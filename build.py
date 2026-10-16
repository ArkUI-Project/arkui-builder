#!/usr/bin/env python3
# Copyright (C) 2026 The ArkUI Project
# SPDX-License-Identifier: Apache-2.0

"""Interactive ArkUI build selection. Python 3.10+, standard library only."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import lzma
import os
from pathlib import Path
import queue
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import xml.etree.ElementTree as ET


BUILD_SHELL = r'''
set -eo pipefail
source build/envsetup.sh
breakfast "${1#lineage_}" "$2"
get_build_vars /PRODUCT_OUT /TARGET_OUT_PRODUCT /TARGET_OUT_SYSTEM_EXT \
    TARGET_PRODUCT TARGET_DEVICE TARGET_ARCH TARGET_RELEASE TARGET_BUILD_VARIANT \
    BUILDING_GSI TARGET_COPY_OUT_PRODUCT TARGET_COPY_OUT_SYSTEM_EXT \
    BOARD_SYSTEMIMAGE_FILE_SYSTEM_TYPE PRODUCT_DEFAULT_DEV_CERTIFICATE > "$5"
if [[ $3 == gsi ]]; then
    [[ $(get_build_var BUILDING_GSI) == true ]] || exit 1
    [[ $(get_build_var TARGET_COPY_OUT_PRODUCT) == system/product ]] || exit 1
    [[ $(get_build_var TARGET_COPY_OUT_SYSTEM_EXT) == system/system_ext ]] || exit 1
    m -j"$4" systemimage
else
    shift 5
    m -j"$ARKUI_BUILDER_JOBS" "$@"
fi
'''


class BuildError(Exception):
    pass


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def relative_path(value, label):
    path = Path(value)
    if not value or path.is_absolute() or ".." in path.parts or "\\" in value:
        raise BuildError(f"{label} 必须是源码内的相对路径: {value}")
    return path


def source_path(source, value):
    path = source / relative_path(value, "配置路径")
    if not path.resolve().is_relative_to(source):
        raise BuildError(f"路径通过符号链接离开源码目录: {value}")
    return path


def load_targets(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema") != 1 or not isinstance(data.get("targets"), list):
        raise BuildError("targets 文件需要 schema=1 和 targets 数组")
    targets = data["targets"]
    ids, outputs = set(), set()
    for target in targets:
        for field in ("id", "name", "product", "kind", "architecture", "flavor", "out_dir"):
            if not isinstance(target.get(field), str) or not target[field]:
                raise BuildError(f"目标缺少字符串字段: {field}")
        if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", target["id"]) or target["id"] in ids:
            raise BuildError(f"目标 id 无效或重复: {target['id']}")
        if not re.fullmatch(r"lineage_[A-Za-z0-9_]+", target["product"]):
            raise BuildError(f"无效的 Lineage 产品名: {target['product']}")
        if target["kind"] not in ("gsi", "device"):
            raise BuildError("kind 仅支持 gsi 或 device")
        for field in ("architecture", "flavor"):
            if not re.fullmatch(r"[A-Za-z0-9_+-]+", target[field]):
                raise BuildError(f"无效的 {field}: {target[field]}")
        output = relative_path(target["out_dir"], "out_dir")
        if len(output.parts) < 2 or output.parts[0] != "out" or " " in str(output):
            raise BuildError("out_dir 必须位于 out/ 下，且不能包含空格")
        if any(output.is_relative_to(Path(known)) or Path(known).is_relative_to(output) for known in outputs):
            raise BuildError(f"目标输出目录不能相同或互相包含: {output}")
        if target["kind"] == "device" and not target.get("goals"):
            raise BuildError("device 目标需要 goals 数组，例如 [\"bacon\"]")
        goals = target.get("goals", [])
        if not isinstance(goals, list) or any(not isinstance(g, str) or not re.fullmatch(r"[A-Za-z0-9_.+-]+", g) for g in goals):
            raise BuildError("goals 必须是有效构建目标名称的数组")
        artifacts = target.get("artifacts", [])
        if not isinstance(artifacts, list) or (target["kind"] == "device" and not artifacts):
            raise BuildError("device 目标需要 artifacts 数组，例如 [\"*.zip\"]")
        for pattern in artifacts:
            relative_path(pattern, "artifacts")
        if not isinstance(target.get("required_paths", []), list) or not isinstance(target.get("dependencies", []), list):
            raise BuildError("required_paths 和 dependencies 必须是数组")
        for required in target.get("required_paths", []):
            relative_path(required, "required_paths")
        for dependency in target.get("dependencies", []):
            dependency_path = relative_path(dependency["path"], "dependency.path")
            if len(dependency_path.parts) < 2 or dependency_path.parts[0] in (".repo", ".git", "out"):
                raise BuildError("依赖必须放在正常的源码子目录中")
            if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", dependency["repository"]):
                raise BuildError("dependency.repository 需要 GitHub owner/repository")
            if not re.fullmatch(r"[A-Za-z0-9_.+/-]+", dependency["revision"]):
                raise BuildError("dependency.revision 无效")
        ids.add(target["id"])
        outputs.add(str(output))
    if not targets:
        raise BuildError("没有配置可选目标")
    return targets


def selection(text, count):
    if text.strip().lower() == "all":
        return list(range(count))
    result = []
    for part in re.split(r"[,，\s]+", text.strip()):
        match = re.fullmatch(r"([0-9]+)(?:-([0-9]+))?", part)
        if not match:
            raise BuildError("请输入编号或范围，例如 1、1,2、1-2、all；不支持数学表达式")
        first, last = int(match[1]), int(match[2] or match[1])
        if not 1 <= first <= last <= count:
            raise BuildError(f"编号范围应在 1 到 {count} 之间")
        for number in range(first - 1, last):
            if number not in result:
                result.append(number)
    return result


def missing_paths(source, target):
    return [p for p in target.get("required_paths", []) if not source_path(source, p).exists()]


def menu(source, targets):
    print("\nArkUI 编译目标（按配置顺序编号）")
    for number, target in enumerate(targets, 1):
        missing = missing_paths(source, target)
        state = "依赖已就绪" if not missing else "缺少依赖"
        print(f"  {number}. {target['name']} [{state}]\n     {target['product']}")
        for path in missing:
            print(f"     缺少: {path}")
    print("编号可多选，例如 1,2 或 1-2；all 全选；q 退出。", flush=True)


def checked(command, **kwargs):
    try:
        return subprocess.run(command, check=True, **kwargs)
    except subprocess.CalledProcessError as error:
        raise BuildError(f"命令失败 ({error.returncode}): {shlex.join(map(str, command))}") from error


def stream_command(command, source, env, log):
    process = subprocess.Popen(command, cwd=source, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, errors="replace",
                               bufsize=1, start_new_session=True)
    messages = queue.Queue()

    def read_output():
        try:
            for line in process.stdout:
                messages.put(line)
        finally:
            messages.put(None)

    reader = threading.Thread(target=read_output, daemon=True)
    reader.start()
    started = time.monotonic()
    try:
        while True:
            try:
                line = messages.get(timeout=30)
            except queue.Empty:
                line = f"[仍在运行，已用时 {int(time.monotonic() - started)} 秒]\n"
            if line is None:
                break
            print(line, end="", flush=True)
            log.write(line)
            log.flush()
        result = process.wait()
        if result:
            raise BuildError(f"编译命令退出码: {result}")
    except BaseException:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        raise
    finally:
        reader.join(timeout=2)
        process.stdout.close()


@contextmanager
def output_lock(path):
    import fcntl
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise BuildError(f"已有构建占用输出目录: {path.parent}") from error
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def repo_command(source):
    executable = shutil.which("repo") or str(source / ".repo/repo/repo")
    if not Path(executable).is_file():
        raise BuildError("找不到 repo 命令")
    return executable


def snapshot(source, destination, log):
    destination.mkdir()
    repo = repo_command(source)
    checked([repo, "manifest", "-r", "-o", str(destination / "source-lock.xml")],
            cwd=source, stdout=log, stderr=log)
    queries = {
        "source-status.txt": 's=$(git status --porcelain=v1 --untracked-files=all) || exit; if [ -n "$s" ]; then printf "project %s\\n%s\\n" "$REPO_PATH" "$s"; fi',
        "source-changes.patch": 'if ! git diff --quiet HEAD --; then printf "project %s\\n" "$REPO_PATH"; git diff --binary HEAD -- || exit; fi',
        "untracked-sha256.txt": 'printf "project %s\\n" "$REPO_PATH"; git ls-files --others --exclude-standard -z | xargs -0 -r sha256sum --',
    }
    for filename, script in queries.items():
        with (destination / filename).open("wb") as stream:
            checked([repo, "forall", "-j1", "-e", "-c", script], cwd=source, stdout=stream, stderr=log)


def prepare_dependencies(source, selected):
    entries = {}
    for target in selected:
        for dep in target.get("dependencies", []):
            if dep["path"] in entries and entries[dep["path"]] != dep:
                raise BuildError(f"依赖配置冲突: {dep['path']}")
            entries[dep["path"]] = dep
    if not entries:
        print("所选目标未声明外部依赖。")
        return
    project_list = source / ".repo/project.list"
    managed = set(project_list.read_text().splitlines()) if project_list.exists() else set()
    missing = []
    for path, dep in sorted(entries.items()):
        if path in managed:
            print(f"保留现有 manifest 管理的依赖: {path}")
            required = [p for target in selected for p in missing_paths(source, target)]
            if any(p.startswith(path + "/") for p in required):
                missing.append(path)
            continue
        if source_path(source, path).exists():
            raise BuildError(f"路径已有文件且不由 repo 管理，拒绝覆盖: {path}")
        root = ET.Element("manifest")
        ET.SubElement(root, "remote", name="arkui_builder_dependencies", fetch="https://github.com/")
        ET.SubElement(root, "project", name=dep["repository"], path=path,
                      remote="arkui_builder_dependencies", revision=dep["revision"])
        ET.indent(root)
        content = ET.tostring(root, encoding="unicode") + "\n"
        fingerprint = hashlib.sha256(path.encode()).hexdigest()[:12]
        manifest = source / f".repo/local_manifests/arkui-builder-{fingerprint}.xml"
        manifest.parent.mkdir(parents=True, exist_ok=True)
        if manifest.exists() and manifest.read_text(encoding="utf-8") != content:
            raise BuildError(f"拒绝覆盖已有 local manifest: {manifest}")
        manifest.write_text(content, encoding="utf-8")
        missing.append(path)
    if not missing:
        print("依赖仓库均已存在；未执行同步。")
        return
    checked([repo_command(source), "sync", "--current-branch", "--no-tags", "-j4", *missing], cwd=source)
    print("依赖已准备；本次未启动编译。")


def read_variables(path):
    values = {}
    for token in shlex.split(path.read_text(encoding="utf-8")):
        name, sep, value = token.partition("=")
        if not sep or not re.fullmatch(r"[A-Z0-9_]+", name):
            raise BuildError("构建变量输出格式无效")
        values[name] = value
    return values


def read_properties(path):
    values = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.lstrip().startswith("#") and "=" in line:
            name, value = line.split("=", 1)
            values[name.strip()] = value.strip()
    return values


def package(source, stage, target, variables, env):
    output = Path(variables["PRODUCT_OUT"]).resolve()
    expected = (source / env["OUT_DIR"]).resolve()
    if not output.is_relative_to(expected):
        raise BuildError("PRODUCT_OUT 离开预期输出目录")
    if variables.get("TARGET_PRODUCT") != target["product"] or variables.get("TARGET_ARCH") != target["architecture"]:
        raise BuildError("实际构建产品或架构与选择不一致")
    if variables.get("TARGET_BUILD_VARIANT") != env["ARKUI_BUILDER_VARIANT"]:
        raise BuildError("实际构建类型与选择不一致")
    properties = stage / "properties"
    properties.mkdir()
    for label, path in {
        "system": output / "system/build.prop",
        "product": Path(variables["TARGET_OUT_PRODUCT"]) / "etc/build.prop",
        "system_ext": Path(variables["TARGET_OUT_SYSTEM_EXT"]) / "etc/build.prop",
    }.items():
        shutil.copy2(path, properties / f"{label}.build.prop")
    props = read_properties(properties / "product.build.prop")
    if props.get("ro.lineage.releasetype") != env["LINEAGE_BUILDTYPE"]:
        raise BuildError("实际发行类型不符合选择")
    version = props.get("ro.lineage.version", "")
    if not re.fullmatch(r"[A-Za-z0-9._-]+", version):
        raise BuildError("镜像缺少有效的 ro.lineage.version")
    artifacts = []
    if target["kind"] == "gsi":
        if variables.get("BUILDING_GSI") != "true" or variables.get("BOARD_SYSTEMIMAGE_FILE_SYSTEM_TYPE") != "ext4":
            raise BuildError("预期 ext4 GSI 配置")
        if props.get("ro.arkui.gsi") != "true" or props.get("ro.arkui.gsi.variant") != target["flavor"]:
            raise BuildError("镜像的 GSI 类型不符合选择")
        installed = {p.stem for p in (output / "system").rglob("*.apk")}
        has_gms = bool(installed & {"GmsCore", "PrebuiltGmsCore"})
        if target["flavor"] == "gms":
            if not has_gms or "Phonesky" not in installed:
                raise BuildError("GMS 镜像缺少 GmsCore 或 Phonesky，拒绝打包")
        elif target["flavor"] == "vanilla" and (has_gms or "Phonesky" in installed):
            raise BuildError("Vanilla 输出目录含 Google 服务，拒绝打包为原生版")
        image = output / "system.img"
        if not image.is_file() or not image.stat().st_size:
            raise BuildError("缺少 system.img")
        name = f"ArkUI-GSI-{target['architecture']}-{target['flavor']}-{version}.img"
        raw_hash = sha256(image)
        with image.open("rb") as source_stream, lzma.open(stage / f"{name}.xz", "wb", preset=6) as compressed:
            shutil.copyfileobj(source_stream, compressed, length=1024 * 1024)
        digest = hashlib.sha256()
        with lzma.open(stage / f"{name}.xz", "rb") as compressed:
            for chunk in iter(lambda: compressed.read(1024 * 1024), b""):
                digest.update(chunk)
        if digest.hexdigest() != raw_hash:
            raise BuildError("压缩镜像校验失败")
        (stage / "IMAGE.sha256").write_text(f"{raw_hash}  {name}\n", encoding="utf-8")
        artifacts.append({"file": f"{name}.xz", "raw_sha256": raw_hash, "raw_bytes": image.stat().st_size})
    else:
        for pattern in target.get("artifacts", []):
            relative_path(pattern, "artifacts")
            matched = sorted(output.glob(pattern))
            if not matched:
                raise BuildError(f"缺少设备产物: {pattern}")
            for file in matched:
                if not file.is_file() or not file.resolve().is_relative_to(output):
                    raise BuildError(f"产物路径无效: {file}")
                destination = stage / "images" / file.relative_to(output)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, destination)
                artifacts.append({"file": destination.relative_to(stage).as_posix()})
        if not artifacts:
            raise BuildError("device 目标必须配置 artifacts 数组，例如 [\"*.zip\"]")
    return version, artifacts


def build_one(source, artifacts_root, target, args, catalog):
    started = utc_now()
    builder_hash = sha256(Path(__file__).resolve())
    catalog_hash = sha256(catalog)
    stage = Path(tempfile.mkdtemp(prefix=f".{target['id']}-partial-", dir=artifacts_root))
    env = os.environ.copy()
    for key in ("OUT_DIR_COMMON_BASE", "OUT_DIR_SUFFIX", "DIST_DIR", "TARGET_PRODUCT", "TARGET_RELEASE",
                "TARGET_BUILD_VARIANT", "TARGET_BUILD_APPS", "LINEAGE_EXTRAVERSION", "TARGET_UNOFFICIAL_BUILD_ID",
                "RELEASE_TYPE", "WITH_ADB_INSECURE", "WITH_GMS"):
        env.pop(key, None)
    output = target["out_dir"] if args.variant == "userdebug" else f"{target['out_dir']}-{args.variant}"
    env.update(OUT_DIR=output, LINEAGE_BUILDTYPE="OFFICIAL" if args.official else "EXPERIMENTAL",
               ARKUI_BUILDER_JOBS=str(args.jobs), ARKUI_BUILDER_VARIANT=args.variant)
    lock = source_path(source, output) / ".arkui-gsi.lock"
    try:
        with output_lock(lock), (stage / "build.log").open("w", encoding="utf-8") as log:
            snapshot(source, stage / "source-before", log)
            dirty = bool((stage / "source-before/source-status.txt").stat().st_size)
            if args.official and dirty:
                raise BuildError("OFFICIAL 构建要求源码工作树干净，详见 source-before/source-status.txt")
            command = ["bash", "-c", BUILD_SHELL, "arkui-build", target["product"], args.variant,
                       target["kind"], str(args.jobs), str(stage / "build-vars.txt"), *target.get("goals", [])]
            stream_command(command, source, env, log)
            snapshot(source, stage / "source-after", log)
            for file in (stage / "source-before").iterdir():
                if sha256(file) != sha256(stage / "source-after" / file.name):
                    raise BuildError(f"构建期间源码变化: {file.name}")
            if sha256(Path(__file__).resolve()) != builder_hash or sha256(catalog) != catalog_hash:
                raise BuildError("构建期间编译工具或目标配置发生变化")
            version, files = package(source, stage, target, read_variables(stage / "build-vars.txt"), env)
            shutil.copy2(source / "vendor/lineage/LICENSE", stage / "LICENSE.vendor-lineage")
            if target["flavor"] == "gms":
                shutil.copy2(source / "vendor/gapps/LICENSE", stage / "LICENSE.gapps")
            write_json(stage / "build.json", {
                "schema": 1, "target": target, "version": version, "build_variant": args.variant,
                "release_type": env["LINEAGE_BUILDTYPE"], "started_at": started, "completed_at": utc_now(),
                "source_state": "dirty" if dirty else "clean", "local_build": True, "build_success": True,
                "boot_verified": False, "source_dir": str(source), "out_dir": output, "artifacts": files,
                "builder_sha256": builder_hash, "catalog_sha256": catalog_hash,
            })
            lines = [f"{sha256(file)}  {file.relative_to(stage).as_posix()}\n"
                     for file in sorted(stage.rglob("*")) if file.is_file() and file.name != "build.log"]
            (stage / "SHA256SUMS").write_text("".join(lines), encoding="utf-8")
        destination = artifacts_root / f"{target['id']}-{datetime.now(timezone.utc):%Y%m%dT%H%M%SZ}-{stage.name.rsplit('-', 1)[-1]}"
        stage.rename(destination)
        print(f"\n编译与打包成功: {destination}\n镜像启动状态：尚未验证。")
        return destination
    except BaseException as error:
        write_json(stage / "failure.json", {"target": target["id"], "failed_at": utc_now(), "error": str(error)})
        print(f"\n失败记录保留在: {stage}", file=sys.stderr)
        raise


def windows_dispatch():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--distro", default="Ubuntu")
    args, _ = parser.parse_known_args()
    def linux_path(path):
        return checked(["wsl.exe", "-d", args.distro, "--exec", "wslpath", "-a", path],
                       capture_output=True, text=True).stdout.strip()
    forwarded = sys.argv[1:]
    for index, value in enumerate(forwarded):
        option, separator, path = value.partition("=")
        if option not in ("--source", "--artifacts-dir", "--targets-file", "--config"):
            continue
        if separator:
            if not path.startswith("/"):
                forwarded[index] = option + "=" + linux_path(path)
        elif index + 1 < len(forwarded):
            if not forwarded[index + 1].startswith("/"):
                forwarded[index + 1] = linux_path(forwarded[index + 1])
    return subprocess.call(["wsl.exe", "-d", args.distro, "--exec", "python3", linux_path(str(Path(__file__).resolve())), *forwarded])


def main():
    if os.name == "nt":
        return windows_dispatch()
    if not sys.platform.startswith("linux"):
        raise BuildError("请在 Linux 或 Windows + WSL Ubuntu 中运行")
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__, epilog="targets.json 可扩展 kind=device、goals、artifacts、required_paths 和独立仓库 dependencies。")
    parser.add_argument("--source", help="完整 Android 源码目录")
    parser.add_argument("--artifacts-dir", help="源码树外的产物目录")
    parser.add_argument("--config", type=Path, default=root.parent / "arkui.config.json")
    parser.add_argument("--targets-file", type=Path, default=root / "targets.json")
    parser.add_argument("--select", help="编号/范围，例如 1,2 或 1-2；all 全选")
    parser.add_argument("--list", action="store_true", help="只显示目标，不编译")
    parser.add_argument("--prepare-dependencies", action="store_true", help="只同步所选目标缺少的独立依赖仓库，不编译")
    parser.add_argument("--jobs", type=int)
    parser.add_argument("--variant", choices=("userdebug", "user", "eng"), default="userdebug")
    parser.add_argument("--official", action="store_true")
    parser.add_argument("--distro", default="Ubuntu", help="Windows 调用时的 WSL 发行版")
    args = parser.parse_args()
    config = json.loads(args.config.read_text(encoding="utf-8")) if args.config.is_file() else {}
    source_value = args.source or config.get("source_dir") or os.environ.get("ARKUI_SOURCE") or str(Path.cwd())
    source = Path(source_value).expanduser().resolve()
    if not (source / ".repo").is_dir() or not (source / "build/envsetup.sh").is_file():
        raise BuildError("不是完整 Android repo 源码目录，请设置 --source")
    args.jobs = args.jobs if args.jobs is not None else int(config.get("build_jobs", 4))
    if args.jobs < 1:
        raise BuildError("--jobs 必须大于 0")
    catalog = args.targets_file.expanduser().resolve()
    targets = load_targets(catalog)
    menu(source, targets)
    if args.list:
        return 0
    choice = args.select
    while choice is None:
        if not sys.stdin.isatty():
            raise BuildError("非交互终端需要 --select")
        try:
            response = input("\n请输入本次目标编号: ").strip()
        except EOFError:
            return 0
        if response.lower() in ("q", "quit", "exit"):
            return 0
        try:
            selection(response, len(targets))
            choice = response
        except BuildError as error:
            print(error)
    selected = [targets[index] for index in selection(choice, len(targets))]
    if args.prepare_dependencies:
        with output_lock(source / "out/.arkui-builder.lock"):
            prepare_dependencies(source, selected)
        return 0
    for target in selected:
        missing = missing_paths(source, target)
        if missing:
            raise BuildError(f"{target['name']} 缺少: {', '.join(missing)}。可用 --prepare-dependencies --select {targets.index(target) + 1} 准备独立依赖仓库。")
    artifacts_root = Path(args.artifacts_dir).expanduser() if args.artifacts_dir else args.config.resolve().parent / "artifacts/builder"
    artifacts_root = artifacts_root.resolve()
    if artifacts_root.is_relative_to(source):
        raise BuildError("产物目录必须在 Android 源码树之外")
    if artifacts_root.is_relative_to(root):
        raise BuildError("产物目录必须在编译工具仓库之外")
    artifacts_root.mkdir(parents=True, exist_ok=True)
    print("\n本次依次编译: " + " → ".join(target["name"] for target in selected))
    with output_lock(source / "out/.arkui-builder.lock"):
        for target in selected:
            build_one(source, artifacts_root, target, args, catalog)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n已取消；保留已有产物和日志。", file=sys.stderr)
        sys.exit(130)
    except (BuildError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"错误: {error}", file=sys.stderr)
        sys.exit(1)
