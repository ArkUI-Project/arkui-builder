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
import unicodedata
from urllib.error import URLError
from urllib.parse import urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener
import uuid
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


RELEASE_TYPES = ("OFFICIAL", "UNOFFICIAL")
RELEASE_CHANNELS = ("stable", "beta", "alpha")
ROM_VERSION_PATTERN = r"[0-9]+(?:\.[0-9]+){1,3}(?:[-+][A-Za-z0-9.-]+)?"
BUILD_NUMBER_PATTERN = r"[A-Za-z0-9][A-Za-z0-9._-]{0,63}"
DEFAULT_BUILD_NUMBER_API = "https://api.ark-ui.org/api/v2/builds/latest"
MAX_CHANNEL_NUMBER = 2147483647


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


def source_version(source):
    text = (source / "vendor/lineage/config/version.mk").read_text(encoding="utf-8")
    match = re.search(r"^ARKUI_VERSION\s*[?:]?=\s*(\S+)\s*$", text, re.MULTILINE)
    if not match:
        raise BuildError("无法从源码读取默认版本: ARKUI_VERSION")
    return match[1]


def valid_build_number(value):
    # AOSP replaces eng.* build numbers with a timestamp in build.prop.
    return re.fullmatch(BUILD_NUMBER_PATTERN, value) and not value.startswith("eng.")


def channel_label(channel, number):
    if channel is None:
        return "None"
    if channel == "stable":
        return "Stable"
    return channel.capitalize() + str(number)


def build_name(args):
    return f"ArkUI-{args.rom_version}-{args.release_type}-{channel_label(args.channel, args.channel_number)}-{args.build_number}"


def validate_release(args):
    if args.release_type not in RELEASE_TYPES:
        raise BuildError("发行类型仅支持 OFFICIAL、UNOFFICIAL")
    if args.release_type == "OFFICIAL":
        if args.channel not in RELEASE_CHANNELS:
            raise BuildError("官方更新渠道仅支持 stable、beta、alpha")
        if args.channel == "stable":
            if args.channel_number is not None:
                raise BuildError("Stable 不使用渠道编号")
        elif type(args.channel_number) is not int or not 1 <= args.channel_number <= MAX_CHANNEL_NUMBER:
            raise BuildError(f"Beta/Alpha 编号应为 1–{MAX_CHANNEL_NUMBER} 的整数")
    elif args.channel is not None or args.channel_number is not None:
        raise BuildError("UNOFFICIAL 构建不能指定渠道或渠道编号")
    if not re.fullmatch(ROM_VERSION_PATTERN, args.rom_version):
        raise BuildError("ArkUI 版本无效，例如 1.0 或 1.0.1")
    if not args.build_number or not valid_build_number(args.build_number):
        raise BuildError("构建号限 1–64 位字母、数字、点、下划线或短横线，不能以 eng. 开头")
    if args.jobs < 1:
        raise BuildError("并行任务必须大于 0")


def refresh_build_number(args):
    latest = fetch_latest_build_number(args.build_number_api)
    suggested = str(int(latest) + 1) if latest is not None else "1"
    if not valid_build_number(suggested):
        raise BuildError("远端构建号递增后超过 64 位，需手动指定")
    args.build_number_lookup = {"latest": latest, "suggested": suggested, "queried_at": utc_now()}
    return suggested


def fetch_latest_build_number(url):
    try:
        parsed = urlsplit(url)
    except ValueError as error:
        raise BuildError("构建号查询接口 URL 无效") from error
    if (parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password
            or parsed.fragment or re.search(r"[\x00-\x20\x7f]", url)):
        raise BuildError("构建号查询接口必须为不含账号密码或片段的 HTTPS URL")

    class NoRedirect(HTTPRedirectHandler):
        def redirect_request(self, request, file, code, message, headers, new_url):
            return None

    request = Request(url, headers={
        "Accept": "application/json", "Cache-Control": "no-cache", "User-Agent": "ArkUI-Builder"
    })
    try:
        with build_opener(NoRedirect()).open(request, timeout=10) as response:
            if response.status != 200:
                raise BuildError(f"构建号接口返回 HTTP {response.status}")
            body = response.read(4097)
        if len(body) > 4096:
            raise BuildError("构建号接口响应过大")
        payload = json.loads(body)
    except (URLError, OSError, ValueError) as error:
        raise BuildError(f"无法读取远端构建号: {error}") from error
    if not isinstance(payload, dict) or set(payload) != {"build_number"}:
        raise BuildError("构建号接口必须返回仅包含 build_number 的 JSON 对象")
    latest = payload["build_number"]
    if latest is not None and (not isinstance(latest, str) or not re.fullmatch(r"0|[1-9][0-9]{0,63}", latest)):
        raise BuildError("远端 build_number 必须为十进制整数字符串或 null")
    return latest


def configure_release(source, selected, args):
    default_version = source_version(source)
    if not args.interactive_configured and not args.yes and not args.preview:
        raise BuildError("编译前需要交互确认；自动化调用请提供完整版本参数和 --yes")
    if not args.interactive_configured:
        if args.yes and not (args.rom_version and args.release_type):
            raise BuildError("--yes 需要显式提供 --release-type 和 --rom-version")
        if args.yes and args.release_type == "OFFICIAL" and not args.channel:
            raise BuildError("OFFICIAL 自动化构建需要显式提供 --channel")
        args.release_type = args.release_type or "OFFICIAL"
        args.rom_version = args.rom_version or default_version
        if args.release_type == "OFFICIAL":
            args.channel = args.channel or "beta"
            if args.channel in ("beta", "alpha"):
                args.channel_number = args.channel_number if args.channel_number is not None else 1
        print("\n正在查询远端最新构建号……", flush=True)
        args.build_number_lookup = None
        try:
            suggested = refresh_build_number(args)
            print(f"  自动构建号: {suggested}")
            args.build_number = args.build_number or suggested
        except BuildError as error:
            if not args.build_number:
                raise BuildError(f"{error}；请重试或通过 --build-number 手动指定") from error
            print(f"  查询失败，采用手动构建号: {error}", file=sys.stderr)
    validate_release(args)
    print("\n编译前确认：")
    print("  目标: " + ", ".join(target["name"] for target in selected))
    print(f"  发行名称: {build_name(args)}")
    print(f"  版本属性 org.arkui.build.version: {args.rom_version}（与本次 ArkUI 版本一致）")
    print(f"  编译类型: {args.variant}\n  并行任务: {args.jobs}")
    if args.preview:
        print("仅预览，未确认或启动编译。")
        return False
    if not args.interactive_configured:
        args.confirmed_at = utc_now()
    return True


class _BuildMenuUI:
    def __init__(self, screen, curses):
        self.screen = screen
        self.curses = curses
        self.usable = True
        self.scroll_limit = 0
        self.styles = {
            "normal": curses.A_NORMAL, "muted": curses.A_DIM,
            "accent": curses.A_BOLD, "heading": curses.A_BOLD,
            "border": curses.A_DIM, "selected": curses.A_REVERSE | curses.A_BOLD,
            "success": curses.A_NORMAL, "warning": curses.A_BOLD,
        }
        if curses.has_colors():
            try:
                curses.start_color()
                background = -1
                try:
                    curses.use_default_colors()
                except curses.error:
                    background = curses.COLOR_BLACK
                for number, foreground, back in (
                    (1, curses.COLOR_CYAN, background),
                    (2, curses.COLOR_WHITE, background),
                    (3, curses.COLOR_BLACK, curses.COLOR_CYAN),
                    (4, curses.COLOR_GREEN, background),
                    (5, curses.COLOR_YELLOW, background),
                ):
                    curses.init_pair(number, foreground, back)
                self.styles.update({
                    "accent": curses.color_pair(1) | curses.A_BOLD,
                    "heading": curses.color_pair(1),
                    "border": curses.color_pair(2) | curses.A_DIM,
                    "selected": curses.color_pair(3) | curses.A_BOLD,
                    "success": curses.color_pair(4),
                    "warning": curses.color_pair(5),
                })
            except curses.error:
                pass

    @staticmethod
    def _width(text):
        return sum(0 if unicodedata.combining(char) else
                   2 if unicodedata.east_asian_width(char) in ("W", "F") else 1
                   for char in text)

    @classmethod
    def _clip(cls, text, width):
        text = str(text).replace("\n", " ").replace("\r", " ").replace("\t", " ")
        if width < 1:
            return ""
        if cls._width(text) <= width:
            return text
        result, used = [], 0
        for char in text:
            size = cls._width(char)
            if used + size > width - 1:
                break
            result.append(char)
            used += size
        return "".join(result) + "…"

    @classmethod
    def _pad(cls, text, width):
        text = cls._clip(text, width)
        return text + " " * max(0, width - cls._width(text))

    def _put(self, y, x, text, width, role="normal"):
        height, columns = self.screen.getmaxyx()
        if not 0 <= y < height or not 0 <= x < columns - 1:
            return
        text = self._clip(text, min(width, columns - x - 1))
        if text:
            try:
                self.screen.addstr(y, x, text, self.styles[role])
            except self.curses.error:
                # A terminal resize can invalidate coordinates between calls.
                pass

    @classmethod
    def _wrap(cls, text, width):
        line, used = "", 0
        for char in str(text):
            size = cls._width(char)
            if char == "\n" or used + size > width:
                yield line
                line, used = "", 0
                if char == "\n":
                    continue
            line += char
            used += size
        if line:
            yield line

    def draw(self, lines, active=0, *, title="构建配置", subtitle="配置目标与发行信息",
             footer="↑↓ 选择  ←→ 调整  Enter 编辑/执行  Esc 退出", status="",
             sections=None, details=None, preview=None, align_values=False, compact=False,
             status_error=False, short_footer="↑↓ 选择  ←→ 调整  Enter 确认  Esc 返回",
             scroll_offset=None):
        self.screen.erase()
        rows, columns = self.screen.getmaxyx()
        self.usable = rows >= 18 and columns >= 60
        if not self.usable:
            self.scroll_limit = 0
            self._put(max(0, rows // 2 - 1), 1, "请将终端调整到至少 60 列 × 18 行", columns - 2, "warning")
            self._put(max(0, rows // 2 + 1), 1, "调整后自动恢复；Esc 返回", columns - 2, "muted")
            self.screen.refresh()
            return

        width = min(columns - 4, 116 if not compact else 86)
        height = min(rows - 2, 32 if not compact else 18)
        top, left = (rows - height) // 2, (columns - width) // 2
        bottom, right = top + height - 1, left + width - 1
        self._put(top, left, "╭" + "─" * (width - 2) + "╮", width, "border")
        self._put(bottom, left, "╰" + "─" * (width - 2) + "╯", width, "border")
        for y in range(top + 1, bottom):
            self._put(y, left, "│", 1, "border")
            self._put(y, right, "│", 1, "border")
        self._put(top + 1, left + 3, "ARKUI", 8, "accent")
        self._put(top + 1, left + 11, "构建工作台", 14, "accent")
        page = title + (f"  {active + 1}/{len(lines)}" if active is not None and lines else "")
        page = self._clip(page, width - 32)
        self._put(top + 1, right - self._width(page) - 2, page, self._width(page), "muted")
        self._put(top + 2, left + 3, subtitle, width - 6, "muted")
        separator = "├" + "─" * (width - 2) + "┤"
        self._put(top + 3, left, separator, width, "border")
        footer_y = bottom - 4
        self._put(footer_y, left, separator, width, "border")

        content_top, content_height = top + 5, footer_y - top - 5
        list_left, list_width = left + 3, width - 6
        show_preview = bool(preview) and width >= 100
        if show_preview:
            list_width = (width - 9) // 2
            divider = list_left + list_width + 1
            for y in range(top + 4, footer_y):
                self._put(y, divider, "│", 1, "border")
            preview_left, preview_width = divider + 3, right - divider - 5
            y = content_top
            for role, text in preview:
                for line in list(self._wrap(text, preview_width)) or [""]:
                    if y >= footer_y:
                        break
                    self._put(y, preview_left, line, preview_width, role)
                    y += 1
                if y >= footer_y:
                    break

        entries, positions = [], {}
        for index, line in enumerate(lines):
            if sections and index in sections:
                if entries:
                    entries.append((None, "", "muted"))
                entries.append((None, sections[index], "heading"))
            positions[index] = len(entries)
            if align_values:
                label, separator, value = line.partition("：")
                line = self._pad(label, 14) + ("  " + value if separator else "")
            entries.append((index, line, "normal"))
            if details:
                entries.append((None, "   " + details[index], "muted"))
        selected_y = positions.get(active, 0)
        start = max(0, selected_y - content_height + 1)
        self.scroll_limit = max(0, len(entries) - content_height)
        if scroll_offset is not None:
            start = max(0, min(scroll_offset, self.scroll_limit))
        for offset, (index, line, role) in enumerate(entries[start:start + content_height]):
            selected = index is not None and index == active
            if index is not None:
                line = ("› " if selected else "  ") + line
            if selected:
                line, role = self._pad(line, list_width), "selected"
            self._put(content_top + offset, list_left, line, list_width, role)

        role = "warning" if status_error else "success"
        message = status or "修改将在开始编译前再次确认。"
        for index, line in enumerate(self._wrap(message, width - 6)):
            if index == 2:
                break
            self._put(footer_y + 1 + index, left + 3, line, width - 6,
                      role if status else "muted")
        if self._width(footer) > width - 6:
            footer = short_footer
        self._put(footer_y + 3, left + 3, footer, width - 6, "muted")
        self.screen.refresh()

    def read_key(self):
        while True:
            key = self.screen.get_wch()
            if self.usable or key in ("\x1b", self.curses.KEY_RESIZE):
                return key


def interactive_configure(source, targets, args):
    try:
        import curses
    except ImportError as error:
        raise BuildError("当前 Python 缺少 curses，请使用 Ubuntu 的系统 Python 运行键盘菜单") from error

    args.release_type = args.release_type or "OFFICIAL"
    args.rom_version = args.rom_version or source_version(source)
    if args.release_type == "OFFICIAL":
        args.channel = args.channel or "beta"
        if args.channel != "stable" and args.channel_number is None:
            args.channel_number = 1
    chosen = set(selection(args.select, len(targets))) if args.select else {0}
    args.build_number_lookup = None

    def run(screen):
        try:
            curses.curs_set(0)
        except curses.error:
            pass
        screen.keypad(True)
        ui = _BuildMenuUI(screen, curses)
        status = ""
        status_error = False

        def preview_name():
            if args.build_number:
                return build_name(args)
            return f"ArkUI-{args.rom_version}-{args.release_type}-{channel_label(args.channel, args.channel_number)}-待填写构建号"

        def preview(hint):
            selected = [targets[i] for i in sorted(chosen)]
            lines = [("heading", "本次发行"), ("normal", preview_name()),
                     ("muted", f"{args.variant} · {args.jobs} 个并行任务"), ("normal", ""),
                     ("heading", f"已选目标  ·  {len(selected)}")]
            if not selected:
                lines.append(("warning", "尚未选择编译目标"))
            for target in selected[:4]:
                lines.append(("normal", "• " + target["name"]))
            if len(selected) > 4:
                lines.append(("muted", f"另有 {len(selected) - 4} 个目标"))
            lines.extend([("normal", ""), ("heading", "当前操作"), ("muted", hint)])
            return lines

        def edit(title, value):
            text = str(value or "")
            while True:
                visible = text
                limit = max(8, min(screen.getmaxyx()[1] - 14, 74))
                while ui._width(visible) > limit:
                    visible = visible[1:]
                if visible != text:
                    visible = "…" + visible
                ui.draw([visible + "▏"], title="编辑" + title, subtitle="输入新的值，保存后返回构建配置。",
                        footer="Enter 保存  Esc 取消  Backspace 删除  Ctrl+U 清空", compact=True,
                        short_footer="Enter 保存  Esc 取消  Ctrl+U 清空")
                key = ui.read_key()
                if key in ("\n", "\r", curses.KEY_ENTER):
                    return text.strip()
                if key == "\x1b":
                    return None
                if key in (curses.KEY_BACKSPACE, "\b", "\x7f"):
                    text = text[:-1]
                elif key == "\x15":
                    text = ""
                elif isinstance(key, str) and key.isprintable():
                    text += key

        def pick_targets():
            index = 0
            while True:
                lines = [f"[{'✓' if i in chosen else ' '}] {i + 1:02d}  {t['name']}"
                         for i, t in enumerate(targets)]
                details = [f"{t['architecture'].upper()} · " +
                           ("缺少依赖" if missing_paths(source, t) else "依赖就绪")
                           for t in targets]
                ui.draw(lines, index, title="选择编译目标", subtitle=f"已选 {len(chosen)} 项 · 按列表顺序依次编译",
                        footer="↑↓ 选择  Space/←→ 勾选  Enter 完成  Esc 返回", details=details,
                        preview=preview(targets[index]["product"] + "；A 全选，N 清空。"),
                        short_footer="↑↓ 移动  空格选择  Enter 完成  Esc 返回")
                key = ui.read_key()
                if key == curses.KEY_UP:
                    index = (index - 1) % len(targets)
                elif key == curses.KEY_DOWN:
                    index = (index + 1) % len(targets)
                elif key in (" ", curses.KEY_LEFT, curses.KEY_RIGHT):
                    chosen.symmetric_difference_update({index})
                elif key in ("a", "A"):
                    chosen.update(range(len(targets)))
                elif key in ("n", "N"):
                    chosen.clear()
                elif key in ("\n", "\r", curses.KEY_ENTER, "\x1b"):
                    return

        def query_number(replace=False):
            nonlocal status, status_error
            status = "正在查询远端最新构建号……"
            status_error = False
            ui.draw([status], active=None, title="查询构建号", subtitle="读取完成后可手动修改建议值。",
                    compact=True)
            try:
                number = refresh_build_number(args)
                if replace or not args.build_number:
                    args.build_number = number
                status = f"远端最新：{args.build_number_lookup['latest']}；自动建议：{number}"
            except BuildError as error:
                status = f"查询失败，请编辑构建号：{error}"
                status_error = True

        query_number()
        active = 0
        hints = {
            "targets": "Enter 打开目标列表，Space 勾选；支持同时编译多个目标。",
            "release_type": "←→ 切换 OFFICIAL / UNOFFICIAL；非官方构建不使用更新渠道。",
            "channel": "←→ 选择 Stable、Beta 或 Alpha。",
            "channel_number": "←→ 调整编号，Enter 输入；例如 Beta1、Beta2。",
            "rom_version": "Enter 编辑 ArkUI 版本；发行名称和镜像版本属性会同步使用这个值。",
            "build_number": "Enter 手动编辑，或选择“刷新构建号”获取远端最新编号加一。",
            "jobs": "←→ 调整并行任务数，Enter 直接输入。",
            "variant": "←→ 选择 userdebug、user 或 eng。",
            "refresh": "Enter 重新查询远端最新构建号，并采用递增后的建议值。",
            "prepare": "Enter 准备所选目标缺少的独立仓库依赖。",
            "start": "Enter 查看最终确认页，确认后开始依次编译所选目标。",
            "cancel": "Enter 退出构建菜单。",
        }
        while True:
            rows = [("targets", f"编译目标：{len(chosen)} 项已选"),
                    ("release_type", f"发行类型：{args.release_type} · " +
                     ("官方构建" if args.release_type == "OFFICIAL" else "非官方构建"))]
            if args.release_type == "OFFICIAL":
                rows.append(("channel", f"更新渠道：{args.channel.capitalize()}"))
                if args.channel != "stable":
                    rows.append(("channel_number", f"阶段编号：{args.channel_number}"))
            rows.extend([("rom_version", f"ArkUI 版本：{args.rom_version}"),
                         ("build_number", f"构建号：{args.build_number or '请手动输入'}"),
                         ("jobs", f"并行任务：{args.jobs}"), ("variant", f"编译类型：{args.variant}"),
                         ("refresh", "刷新构建号：从远端获取建议值"),
                         ("prepare", "准备依赖：同步所选目标的依赖"),
                         ("start", "开始编译：检查并确认 →"), ("cancel", "退出")])
            active = min(active, len(rows) - 1)
            sections = {i: {"targets": "01  编译目标", "release_type": "02  发行信息",
                            "jobs": "03  构建选项", "refresh": "04  操作"}[field]
                        for i, (field, _) in enumerate(rows)
                        if field in ("targets", "release_type", "jobs", "refresh")}
            ui.draw([text for _, text in rows], active, sections=sections, align_values=True,
                    subtitle=preview_name(), status=status, status_error=status_error,
                    preview=preview(hints[rows[active][0]]))
            key = ui.read_key()
            if key in ("q", "\x1b"):
                return None
            if key in (curses.KEY_UP, curses.KEY_DOWN):
                active = (active + (1 if key == curses.KEY_DOWN else -1)) % len(rows)
                continue
            field = rows[active][0]
            enter = key in ("\n", "\r", curses.KEY_ENTER)
            step = -1 if key == curses.KEY_LEFT else 1
            if key not in (curses.KEY_LEFT, curses.KEY_RIGHT, " ") and not enter:
                continue
            if status_error:
                status, status_error = "", False
            if field == "targets":
                pick_targets()
            elif field in ("release_type", "channel", "variant"):
                options = {"release_type": RELEASE_TYPES, "channel": RELEASE_CHANNELS,
                           "variant": ("userdebug", "user", "eng")}[field]
                setattr(args, field, options[(options.index(getattr(args, field)) + step) % len(options)])
                if field == "release_type":
                    args.channel = "beta" if args.release_type == "OFFICIAL" else None
                if field in ("release_type", "channel"):
                    args.channel_number = 1 if args.channel in ("beta", "alpha") else None
            elif field in ("jobs", "channel_number") and not enter:
                setattr(args, field, max(1, min(MAX_CHANNEL_NUMBER, getattr(args, field) + step)))
            elif field in ("rom_version", "build_number", "jobs", "channel_number") and enter:
                value = edit(rows[active][1].split("：")[0], getattr(args, field))
                if value is not None:
                    if field in ("jobs", "channel_number"):
                        if not value.isascii() or not value.isdigit() or not 1 <= int(value) <= MAX_CHANNEL_NUMBER:
                            status = f"请输入 1–{MAX_CHANNEL_NUMBER} 的整数"
                            status_error = True
                            continue
                        value = int(value)
                    setattr(args, field, value)
            elif field == "refresh" and enter:
                query_number(replace=True)
            elif field in ("start", "prepare") and enter:
                if not chosen:
                    status = "请至少选择一个目标"
                    status_error = True
                    continue
                selected = [targets[i] for i in sorted(chosen)]
                if field == "prepare":
                    args.prepare_dependencies = True
                    return selected
                try:
                    validate_release(args)
                    for target in selected:
                        if missing_paths(source, target):
                            raise BuildError("所选目标缺少依赖，请先选择“准备依赖”")
                except BuildError as error:
                    status = str(error)
                    status_error = True
                    continue
                summary = [f"发行类型：{args.release_type}",
                           f"更新渠道：{channel_label(args.channel, args.channel_number)}",
                           f"ArkUI 版本：{args.rom_version}", f"构建号：{args.build_number}",
                           f"编译类型：{args.variant}", f"并行任务：{args.jobs}", "",
                           *[f"{i + 1:02d}  {target['name']}" for i, target in enumerate(selected)]]
                review_offset = 0
                while True:
                    ui.draw(summary, active=None, title="确认开始编译", subtitle=preview_name(),
                            footer="↑↓ 滚动查看  Enter 开始编译  Esc 返回修改",
                            status="确认后将按目标列表顺序编译。",
                            preview=preview("检查发行信息和目标列表。按 Enter 开始，按 Esc 返回修改。"),
                            short_footer="↑↓ 滚动  Enter 开始  Esc 返回", scroll_offset=review_offset)
                    review_offset = min(review_offset, ui.scroll_limit)
                    key = ui.read_key()
                    if key in ("\n", "\r", curses.KEY_ENTER):
                        args.interactive_configured = True
                        args.confirmed_at = utc_now()
                        return selected
                    if key == curses.KEY_UP:
                        review_offset = max(0, review_offset - 1)
                    elif key == curses.KEY_DOWN:
                        review_offset = min(ui.scroll_limit, review_offset + 1)
                    elif key != curses.KEY_RESIZE:
                        break
            elif field == "cancel" and enter:
                return None

    try:
        return curses.wrapper(run)
    except curses.error as error:
        raise BuildError("无法打开键盘菜单，请在支持交互的终端中运行，或使用参数进行自动化调用") from error


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


def package(source, stage, target, variables, env, args):
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
    props = read_properties(properties / "system.build.prop")
    props.update(read_properties(properties / "product.build.prop"))
    if props.get("org.arkui.releasetype") != env["LINEAGE_BUILDTYPE"]:
        raise BuildError("实际发行类型不符合选择")
    if (props.get("org.arkui.channel") or None) != args.channel:
        raise BuildError("实际更新渠道不符合选择")
    if (props.get("org.arkui.channel.number") or None) != (
        str(args.channel_number) if args.channel_number is not None else None
    ):
        raise BuildError("实际渠道编号不符合选择")
    for key, expected_value in {
        "ro.arkui.version": args.rom_version,
        "org.arkui.build.version": args.rom_version,
        "ro.build.version.incremental": args.build_number,
    }.items():
        if props.get(key) != expected_value:
            raise BuildError(f"镜像属性 {key}={props.get(key)!r} 与确认值 {expected_value!r} 不一致")
    version = build_name(args)
    if props.get("ro.lineage.version") != version:
        raise BuildError("系统发行名称与确认的构建配置不一致")
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
        name = f"{version}.img"
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
        copied = set()
        for pattern in target.get("artifacts", []):
            pattern = pattern.replace("{release_name}", version)
            relative_path(pattern, "artifacts")
            matched = sorted(output.glob(pattern))
            if not matched:
                raise BuildError(f"缺少设备产物: {pattern}")
            for file in matched:
                if not file.is_file() or not file.resolve().is_relative_to(output):
                    raise BuildError(f"产物路径无效: {file}")
                identity = (file.stat().st_dev, file.stat().st_ino)
                if identity in copied:
                    continue
                copied.add(identity)
                destination = stage / "images" / file.relative_to(output)
                if file.suffix == ".zip":
                    destination = stage / "images" / f"{version}.zip"
                if destination.exists():
                    raise BuildError("设备产物匹配到多个 ROM ZIP，请收窄 artifacts 配置")
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, destination)
                artifacts.append({"file": destination.relative_to(stage).as_posix()})
        if not artifacts:
            raise BuildError("device 目标必须配置 artifacts 数组，例如 [\"*.zip\"]")
    for artifact in artifacts:
        file = stage / artifact["file"]
        if not re.fullmatch(r"(?:[A-Za-z0-9_-][A-Za-z0-9._+ -]*/)*[A-Za-z0-9_-][A-Za-z0-9._+ -]*", artifact["file"]):
            raise BuildError(f"产物文件名不符合发布格式: {artifact['file']}")
        if not file.stat().st_size or not re.fullmatch(r"[a-z0-9]+", file.suffix.lstrip(".").lower()):
            raise BuildError(f"产物为空或缺少文件格式: {file.name}")
        artifact.update(bytes=file.stat().st_size, sha256=sha256(file),
                        role="system" if target["kind"] == "gsi" else "rom",
                        format=file.suffix.lstrip(".").lower())
    return version, artifacts, props


def release_manifest(target, variables, props, artifacts, source_state, release_id):
    required = ("org.arkui.releasetype", "org.arkui.build.version", "ro.arkui.version",
                "ro.build.version.incremental", "ro.lineage.version", "ro.build.version.release",
                "ro.build.version.sdk", "ro.build.version.security_patch", "ro.build.date.utc",
                "ro.build.fingerprint", "ro.build.tags")
    if any(not props.get(key) for key in required):
        raise BuildError("镜像缺少生成 release.json 所需的版本属性")
    release_type = props["org.arkui.releasetype"]
    channel = props.get("org.arkui.channel") or None
    channel_number = int(props["org.arkui.channel.number"]) if props.get("org.arkui.channel.number") else None
    if release_type not in RELEASE_TYPES or (
        release_type == "OFFICIAL" and channel not in RELEASE_CHANNELS
    ) or (release_type == "UNOFFICIAL" and channel is not None):
        raise BuildError("镜像的发行类型与更新渠道组合无效")
    sdk, timestamp = int(props["ro.build.version.sdk"]), int(props["ro.build.date.utc"])
    if sdk < 1 or timestamp < 1:
        raise BuildError("镜像中的 SDK 或构建时间无效")
    return {
        "format": "arkui.release", "schema_version": 2, "release_id": release_id,
        "created_at": utc_now(),
        "target": {"id": target["id"], "product": target["product"], "kind": target["kind"],
                   "device": props.get("ro.lineage.device") or variables["TARGET_DEVICE"],
                   "board": variables["TARGET_DEVICE"], "architecture": target["architecture"],
                   "flavor": target["flavor"]},
        "name": props["ro.lineage.version"],
        "release_type": release_type, "release_channel": channel,
        "release_channel_number": channel_number,
        "build_variant": variables["TARGET_BUILD_VARIANT"],
        "versions": {"rom": props["ro.arkui.version"], "base": props["org.arkui.build.version"],
                     "build_number": props["ro.build.version.incremental"],
                     "display": props["ro.lineage.version"], "android": props["ro.build.version.release"],
                     "sdk": sdk, "security_patch": props["ro.build.version.security_patch"]},
        "build_timestamp": timestamp, "fingerprint": props["ro.build.fingerprint"],
        "build_tags": props["ro.build.tags"], "source_state": source_state,
        "validation": {"build_success": True, "boot_verified": False},
        "artifacts": artifacts,
    }


def build_one(source, artifacts_root, target, args, catalog):
    started = utc_now()
    builder_hash = sha256(Path(__file__).resolve())
    catalog_hash = sha256(catalog)
    release_id = str(uuid.uuid4())
    destination = artifacts_root / target["id"] / build_name(args)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        raise BuildError(f"相同发行名称的产物已存在，拒绝覆盖: {destination}")
    stage = Path(tempfile.mkdtemp(prefix=".partial-", dir=destination.parent))
    env = os.environ.copy()
    for key in ("OUT_DIR_COMMON_BASE", "OUT_DIR_SUFFIX", "DIST_DIR", "TARGET_PRODUCT", "TARGET_RELEASE",
                "TARGET_BUILD_VARIANT", "TARGET_BUILD_APPS", "LINEAGE_EXTRAVERSION", "TARGET_UNOFFICIAL_BUILD_ID",
                "RELEASE_TYPE", "WITH_ADB_INSECURE", "WITH_GMS", "ARKUI_VERSION", "ARKUI_CHANNEL",
                "ARKUI_CHANNEL_NUMBER", "ARKUI_BUILD_NUMBER", "BUILD_NUMBER"):
        env.pop(key, None)
    output = target["out_dir"] if args.variant == "userdebug" else f"{target['out_dir']}-{args.variant}"
    env.update(OUT_DIR=output, LINEAGE_BUILDTYPE=args.release_type,
               ARKUI_VERSION=args.rom_version, BUILD_NUMBER=args.build_number,
               ARKUI_BUILD_NUMBER=args.build_number,
               ARKUI_BUILDER_JOBS=str(args.jobs), ARKUI_BUILDER_VARIANT=args.variant)
    if args.channel is not None:
        env["ARKUI_CHANNEL"] = args.channel
    if args.channel_number is not None:
        env["ARKUI_CHANNEL_NUMBER"] = str(args.channel_number)
    lock = source_path(source, output) / ".arkui-gsi.lock"
    try:
        with output_lock(lock), (stage / "build.log").open("w", encoding="utf-8") as log:
            snapshot(source, stage / "source-before", log)
            dirty = bool((stage / "source-before/source-status.txt").stat().st_size)
            if args.release_type == "OFFICIAL" and dirty:
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
            variables = read_variables(stage / "build-vars.txt")
            version, files, props = package(source, stage, target, variables, env, args)
            shutil.copy2(source / "vendor/lineage/LICENSE", stage / "LICENSE.vendor-lineage")
            if target["flavor"] == "gms":
                shutil.copy2(source / "vendor/gapps/LICENSE", stage / "LICENSE.gapps")
            write_json(stage / "build.json", {
                "schema": 1, "target": target, "version": version, "build_variant": args.variant,
                "release_type": env["LINEAGE_BUILDTYPE"], "release_channel": args.channel,
                "release_channel_number": args.channel_number,
                "started_at": started, "completed_at": utc_now(),
                "source_state": "dirty" if dirty else "clean", "local_build": True, "build_success": True,
                "boot_verified": False, "source_dir": str(source), "out_dir": output, "artifacts": files,
                "builder_sha256": builder_hash, "catalog_sha256": catalog_hash,
                "release_id": release_id, "confirmed_at": args.confirmed_at,
                "build_number_lookup": args.build_number_lookup,
                "confirmed_settings": {"release_type": args.release_type, "release_channel": args.channel,
                                       "release_channel_number": args.channel_number,
                                       "rom_version": args.rom_version,
                                       "build_number": args.build_number, "base_version": args.rom_version},
            })
            write_json(stage / "release.json", release_manifest(
                target, variables, props, files, "dirty" if dirty else "clean", release_id))
            lines = [f"{sha256(file)}  {file.relative_to(stage).as_posix()}\n"
                     for file in sorted(stage.rglob("*")) if file.is_file() and file.name != "build.log"]
            (stage / "SHA256SUMS").write_text("".join(lines), encoding="utf-8")
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
    parser.add_argument("--release-type", type=str.upper, choices=RELEASE_TYPES, help="发行类型：OFFICIAL、UNOFFICIAL；默认 OFFICIAL")
    parser.add_argument("--channel", type=str.lower, choices=RELEASE_CHANNELS, help="仅用于 OFFICIAL：stable、beta、alpha；交互默认 beta")
    parser.add_argument("--channel-number", type=int, help="Beta/Alpha 编号，例如 1 对应 Beta1；默认 1")
    parser.add_argument("--rom-version", help="本次 ArkUI 版本，例如 1.0.1")
    parser.add_argument("--build-number", help="手动覆盖构建号；默认查询远端最新构建号并加一")
    parser.add_argument("--build-number-api", help="查询最新构建号的 HTTPS 接口，可通过配置 build_number_api 设置")
    parser.add_argument("--yes", action="store_true", help="显式确认命令行提供的完整版本参数")
    parser.add_argument("--preview", action="store_true", help="仅预览编译配置，不初始化构建环境")
    parser.add_argument("--distro", default="Ubuntu", help="Windows 调用时的 WSL 发行版")
    args = parser.parse_args()
    args.interactive_configured = False
    config = json.loads(args.config.read_text(encoding="utf-8")) if args.config.is_file() else {}
    args.build_number_api = args.build_number_api or config.get("build_number_api") or DEFAULT_BUILD_NUMBER_API
    if not isinstance(args.build_number_api, str):
        raise BuildError("build_number_api 必须是 HTTPS URL 字符串")
    source_value = args.source or config.get("source_dir") or os.environ.get("ARKUI_SOURCE") or str(Path.cwd())
    source = Path(source_value).expanduser().resolve()
    if not (source / ".repo").is_dir() or not (source / "build/envsetup.sh").is_file():
        raise BuildError("不是完整 Android repo 源码目录，请设置 --source")
    args.jobs = args.jobs if args.jobs is not None else int(config.get("build_jobs", 4))
    if args.jobs < 1:
        raise BuildError("--jobs 必须大于 0")
    catalog = args.targets_file.expanduser().resolve()
    targets = load_targets(catalog)
    if args.list:
        menu(source, targets)
        return 0
    if sys.stdin.isatty() and sys.stdout.isatty() and not (args.yes or args.preview or args.prepare_dependencies):
        selected = interactive_configure(source, targets, args)
        if selected is None:
            return 0
    else:
        menu(source, targets)
        if not args.select:
            raise BuildError("非交互调用需要 --select；直接运行可打开键盘菜单")
        selected = [targets[index] for index in selection(args.select, len(targets))]
    if args.prepare_dependencies:
        with output_lock(source / "out/.arkui-builder.lock"):
            prepare_dependencies(source, selected)
        return 0
    for target in selected:
        missing = missing_paths(source, target)
        if missing:
            raise BuildError(f"{target['name']} 缺少: {', '.join(missing)}。可用 --prepare-dependencies --select {targets.index(target) + 1} 准备独立依赖仓库。")
    if not configure_release(source, selected, args):
        return 0
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
