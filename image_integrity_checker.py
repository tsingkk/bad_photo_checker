import os
import sys
import json
import csv
import struct
import time
import hashlib
import warnings
import subprocess
import threading
import multiprocessing
from multiprocessing import Process, Queue, Event
import queue
from pathlib import Path
from tkinter import ttk, filedialog, messagebox
import tkinter.font as tkfont
from tkinter import *
import io
from PIL import Image, ImageFile

# 解除 Pillow 默认像素上限（防止高分辨率底片扫描件、全景拼图被误报为 DecompressionBombError）
Image.MAX_IMAGE_PIXELS = None
# 严格禁止容忍截断图像，确保截断文件在 load() 时抛出异常
ImageFile.LOAD_TRUNCATED_IMAGES = False

SUPPORTED_FORMATS = {
    ".jpg": "JPEG",
    ".jpeg": "JPEG",
    ".png": "PNG",
    ".gif": "GIF",
    ".bmp": "BMP",
    ".tiff": "TIFF",
    ".tif": "TIFF",
    ".webp": "WebP",
    ".ico": "ICO",
}

FORMAT_EXTENSIONS = list(SUPPORTED_FORMATS.keys())

# 已知相册/网盘导出失败生成的错误占位图 MD5 签名库
KNOWN_PLACEHOLDER_MD5 = {
    "373666b34d1786fa01ffa53830b394a3": "文件实为‘:( 相片读取失败’的 GIF 错误占位图 (130x86)，原始照片已丢失",
}

# 表格最大展示的“正常”文件行数上限（避免十万级照片撑爆 Tkinter Treeview 内存，异常文件则无上限展示）
MAX_VALID_TREE_ITEMS = 5000


# --- 核心图像检测算法 ---

def detect_file_signature(file_path):
    """
    读取文件头部字节并识别真实图像格式。
    注意：不捕获 PermissionError / OSError，交由上层精确分类为权限问题或磁盘坏道 I/O 错误。
    返回: (real_format: str | None, header_bytes: bytes)
    """
    with open(file_path, "rb") as f:
        header = f.read(32)

    if not header:
        return None, b""

    if header.startswith(b"\xff\xd8\xff"):
        return "JPEG", header
    if header.startswith(b"\x89PNG\r\n\x1a\n"):
        return "PNG", header
    if header.startswith((b"GIF87a", b"GIF89a")):
        return "GIF", header
    if header.startswith(b"BM"):
        return "BMP", header
    # 支持标准 TIFF (42) 与 BigTIFF (43)
    if header.startswith((b"II\x2a\x00", b"MM\x00\x2a", b"II\x2b\x00", b"MM\x00\x2b")):
        return "TIFF", header
    if len(header) >= 12 and header.startswith(b"RIFF") and header[8:12] == b"WEBP":
        return "WebP", header
    # 支持 ICO (1) 与 CUR (2) 容器头
    if header.startswith((b"\x00\x00\x01\x00", b"\x00\x00\x02\x00")):
        return "ICO", header
    # 识别常见现代手机 HEIC/HEIF/AVIF 容器（常被直接改后缀为 .jpg）
    if len(header) >= 12 and header[4:8] == b"ftyp":
        brand = header[8:12].lower()
        if brand in (b"heic", b"heix", b"hevc", b"heim", b"heis", b"hevm", b"hevs", b"mif1", b"msf1"):
            return "HEIF", header
        if brand in (b"avif", b"avis"):
            return "AVIF", header

    return None, header


def get_real_format(file_path):
    """兼容原有接口：返回文件的真实格式字符串，若异常或未知则返回 None"""
    try:
        fmt, _ = detect_file_signature(file_path)
        return fmt
    except Exception:
        return None


def _check_tail_zero_sectors(file_path, file_size, check_bytes=4096, zero_run_threshold=1024):
    """
    检查文件尾部是否存在因磁盘坏道恢复（如 chkdsk）或拷贝中断产生的连续全 0x00 扇区。
    返回 True 表示发现异常的尾部连续全零填充。
    """
    if file_size < check_bytes:
        return False
    with open(file_path, "rb") as f:
        f.seek(max(0, file_size - check_bytes))
        tail = f.read(check_bytes)
    # 若文件最末尾连续 zero_run_threshold 字节全为 0x00
    return tail.endswith(b"\x00" * zero_run_threshold)


def _check_jpeg_bottom_gray_corruption(img):
    """
    检测 JPEG 因数据流提前终止（如坏道清零后巧合遇到 EOI，或中途位翻转产生 0xFFD9）
    导致的画面下半部分变成 libjpeg 默认未初始化中性灰 RGB(128, 128, 128) 的情况。
    """
    try:
        w, h = img.size
        if w < 32 or h < 32:
            return False

        # 检查底部 8 行像素（至少覆盖一个 MCU 行高）
        check_h = min(16, max(4, h // 20))
        if img.mode == "RGB":
            bottom_extrema = img.crop((0, h - check_h, w, h)).getextrema()
            if bottom_extrema == ((128, 128), (128, 128), (128, 128)):
                # 排除整张图片本身就是纯 #808080 灰色色卡的情况
                top_extrema = img.crop((0, 0, w, check_h)).getextrema()
                if top_extrema != ((128, 128), (128, 128), (128, 128)):
                    return True
        elif img.mode == "L":
            bottom_extrema = img.crop((0, h - check_h, w, h)).getextrema()
            if bottom_extrema == (128, 128):
                top_extrema = img.crop((0, 0, w, check_h)).getextrema()
                if top_extrema != (128, 128):
                    return True
    except Exception:
        pass
    return False


def deep_verify(file_path, result, real_format=None):
    """
    深度校验图像像素数据流与多帧结构，同时捕获解码器发出的警告。
    """
    caught_warnings = []
    try:
        with warnings.catch_warnings(record=True) as w_list:
            warnings.simplefilter("always")

            # PngImageFile 实现了专门的 chunk CRC verify()，其他格式调用 verify() 只是关闭文件
            if real_format == "PNG":
                with Image.open(file_path) as img:
                    img.verify()

            with Image.open(file_path) as img:
                n_frames = getattr(img, "n_frames", 1) or 1
                if n_frames <= 1:
                    img.load()
                    if real_format == "JPEG" and _check_jpeg_bottom_gray_corruption(img):
                        result["valid"] = False
                        result["status"] = "corrupted"
                        result["error_type"] = "画面局部损坏"
                        result["error_message"] = "JPEG 数据流疑似提前中断，图像底部出现未解码死灰块"
                        return result
                else:
                    # 多帧图像（GIF / 多页 TIFF / 动态 WebP / MPO）：
                    # 帧数较少时全量逐帧解码；超长动图抽样前10帧、中间帧与最后5帧（截断多发生在尾部）
                    if n_frames <= 40:
                        frames_to_check = range(n_frames)
                    else:
                        mid_step = max(1, (n_frames - 15) // 10)
                        frames_to_check = sorted(set(
                            list(range(10))
                            + list(range(10, n_frames - 5, mid_step))
                            + list(range(n_frames - 5, n_frames))
                        ))
                    for frame_idx in frames_to_check:
                        img.seek(frame_idx)
                        img.load()

            for w in w_list:
                msg = str(w.message)
                caught_warnings.append(msg)

        # 分析捕获到的警告信息
        for msg in caught_warnings:
            lower_msg = msg.lower()
            if any(k in lower_msg for k in ("truncated", "premature end", "damaged", "corruptper")):
                result["valid"] = False
                result["status"] = "corrupted"
                result["error_type"] = "图像数据截断"
                result["error_message"] = f"解码器警告: {msg}"
                return result

        # 若存在非致命警告（如 Corrupt EXIF data），且此前无更高级别状态，则记录为警告但保留 valid=True
        if caught_warnings and result.get("status") == "valid":
            non_benign = [m for m in caught_warnings if "decompressionbomb" not in m.lower()]
            if non_benign:
                result["status"] = "warning"
                result["error_type"] = "元数据警告"
                result["error_message"] = f"像素完好，但存在元数据异常: {non_benign[0]}"

        return result
    except Exception as e:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "解码错误"
        result["error_message"] = str(e)
        return result


def validate_jpeg(file_path, result):
    file_size = result["size"]
    if file_size < 107:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = f"JPEG 文件过小 ({file_size} B)，不足以包含完整图像结构"
        return result

    # 检查是否存在 JPEG 结束标记 EOI (\xff\xd9)，同时兼容末尾附带 MP4 的手机动态照片（Motion Photos）
    tail_read_size = min(file_size, 65536)
    with open(file_path, "rb") as f:
        f.seek(file_size - tail_read_size)
        tail_data = f.read(tail_read_size)

    has_eoi = b"\xff\xd9" in tail_data
    if not has_eoi and file_size > tail_read_size:
        # 若最后 64KB 没有 EOI（例如动态照片附带了数 MB 的视频流），则在全文件中流式搜索 \xff\xd9
        with open(file_path, "rb") as f:
            prev_byte = b""
            while True:
                chunk = f.read(262144)
                if not chunk:
                    break
                if b"\xff\xd9" in (prev_byte + chunk):
                    has_eoi = True
                    break
                prev_byte = chunk[-1:]

    if not has_eoi:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = "JPEG 缺少结束标记 (EOI 0xFFD9)，文件未传输完整或尾部损坏"
        return result

    # 检查尾部是否被磁盘坏道连续清零（1KB 以上纯 0x00 结尾）
    if tail_data.endswith(b"\x00" * 1024):
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "扇区清零损坏"
        result["error_message"] = "文件尾部发现大段连续全零字节 (0x00)，疑似磁盘坏道或复制中断"
        return result

    return deep_verify(file_path, result, real_format="JPEG")


def validate_png(file_path, result):
    file_size = result["size"]
    if file_size < 57:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = f"PNG 文件过小 ({file_size} B)"
        return result

    # 检查尾部是否包含 IEND 块标识
    with open(file_path, "rb") as f:
        f.seek(max(0, file_size - 128))
        tail = f.read(128)
    if b"IEND" not in tail:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = "PNG 尾部缺少 IEND 结束块"
        return result

    return deep_verify(file_path, result, real_format="PNG")


def validate_gif(file_path, result):
    if result["size"] < 35:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = "GIF 文件过小"
        return result
    return deep_verify(file_path, result, real_format="GIF")


def validate_bmp(file_path, result):
    file_size = result["size"]
    if file_size < 54:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "无效文件头"
        result["error_message"] = "BMP 文件小于最小头部长度 (54 B)"
        return result

    with open(file_path, "rb") as f:
        bmp_header = f.read(14)
    declared_size, _, _, pixel_offset = struct.unpack("<IHHI", bmp_header[2:14])
    if declared_size > 0 and file_size < declared_size:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = f"BMP 实际大小 ({file_size} B) 小于文件头声明大小 ({declared_size} B)"
        return result
    if pixel_offset >= file_size:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "无效文件头"
        result["error_message"] = "BMP 像素数据偏移量超出文件末尾"
        return result

    return deep_verify(file_path, result, real_format="BMP")


def validate_tiff(file_path, result):
    file_size = result["size"]
    if file_size < 42:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = "TIFF 文件过小"
        return result

    # 校验 TIFF Strip/Tile 数据偏移量是否超出实际文件大小（解决未压缩 TIFF 截断不报错问题）
    try:
        with Image.open(file_path) as img:
            if hasattr(img, "tag_v2"):
                # 273: StripOffsets, 279: StripByteCounts, 324: TileOffsets, 325: TileByteCounts
                for off_tag, cnt_tag in ((273, 279), (324, 325)):
                    offsets = img.tag_v2.get(off_tag)
                    counts = img.tag_v2.get(cnt_tag)
                    if offsets and counts:
                        if isinstance(offsets, int):
                            offsets = (offsets,)
                        if isinstance(counts, int):
                            counts = (counts,)
                        max_end = max(o + c for o, c in zip(offsets, counts))
                        if max_end > file_size:
                            result["valid"] = False
                            result["status"] = "corrupted"
                            result["error_type"] = "文件截断"
                            result["error_message"] = f"TIFF 数据块超出文件大小 (需 {max_end} B, 实际 {file_size} B)"
                            return result

            # 检测未压缩 TIFF 后半段被磁盘坏道清零（尾部全 0 且画面底部全黑、顶部非全黑）
            compression = img.info.get("compression", "raw")
            if compression == "raw" and file_size > 8192 and _check_tail_zero_sectors(file_path, file_size, 4096, 2048):
                img.load()
                w, h = img.size
                if w >= 16 and h >= 16:
                    check_h = min(16, max(4, h // 10))
                    bottom_ext = img.crop((0, h - check_h, w, h)). convert("RGB").getextrema()
                    top_ext = img.crop((0, 0, w, check_h)).convert("RGB").getextrema()
                    if bottom_ext == ((0, 0), (0, 0), (0, 0)) and top_ext != ((0, 0), (0, 0), (0, 0)):
                        result["valid"] = False
                        result["status"] = "corrupted"
                        result["error_type"] = "扇区清零损坏"
                        result["error_message"] = "未压缩 TIFF 尾部出现大段全零扇区，画面底部缺失变黑"
                        return result
    except Exception as e:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "解码错误"
        result["error_message"] = str(e)
        return result

    return deep_verify(file_path, result, real_format="TIFF")


def validate_webp(file_path, result):
    file_size = result["size"]
    if file_size < 20:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = "WebP 文件过小"
        return result

    with open(file_path, "rb") as f:
        riff_header = f.read(12)
    riff_size = struct.unpack("<I", riff_header[4:8])[0]
    expected_total = riff_size + 8
    if file_size < expected_total:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = f"WebP 实际大小 ({file_size} B) 小于 RIFF 容器声明大小 ({expected_total} B)"
        return result

    return deep_verify(file_path, result, real_format="WebP")


def validate_ico(file_path, result):
    file_size = result["size"]
    if file_size < 22:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件截断"
        result["error_message"] = "ICO 文件小于最小目录头长度 (22 B)"
        return result

    with open(file_path, "rb") as f:
        ico_header = f.read(6)
        _, _, count = struct.unpack("<HHH", ico_header)
        if count == 0 or 6 + count * 16 > file_size:
            result["valid"] = False
            result["status"] = "corrupted"
            result["error_type"] = "无效文件头"
            result["error_message"] = "ICO 目录项数量异常或文件被截断"
            return result
        for _ in range(count):
            entry = f.read(16)
            bytes_in_res, img_offset = struct.unpack("<II", entry[8:16])
            if img_offset + bytes_in_res > file_size:
                result["valid"] = False
                result["status"] = "corrupted"
                result["error_type"] = "文件截断"
                result["error_message"] = f"ICO 图层偏移 ({img_offset + bytes_in_res} B) 超出文件总大小 ({file_size} B)"
                return result

    return deep_verify(file_path, result, real_format="ICO")


def _detect_placeholder_anomaly(file_path, ext, real_format, file_size):
    """
    针对扩展名与实际格式不符的文件，进一步分析是否为云相册/导出工具生成的‘相片读取失败’等错误占位图。
    """
    try:
        # 对小体积异常文件计算 MD5 比对已知错误占位图签名
        if file_size <= 65536:
            with open(file_path, "rb") as f:
                md5_hex = hashlib.md5(f.read()).hexdigest()
            if md5_hex in KNOWN_PLACEHOLDER_MD5:
                return KNOWN_PLACEHOLDER_MD5[md5_hex]

        # 照片后缀（如 .jpg/.png）内部却是单帧小尺寸 GIF，极可能是导出失败占位图
        if real_format == "GIF" and ext in (".jpg", ".jpeg", ".png", ".bmp", ".tiff", ".tif"):
            with Image.open(file_path) as im:
                w, h = im.size
                n_frames = getattr(im, "n_frames", 1) or 1
                if n_frames == 1 and (file_size < 16384 or (w <= 300 and h <= 300)):
                    return f"扩展名 {ext} 与实际内容 GIF ({w}x{h}) 不符，疑似相册导出失败生成的错误占位图"
    except Exception:
        pass
    return None


def validate_image(file_path):
    """
    核心单文件检测入口。
    返回结构：
    {
        "path": str,
        "valid": bool,          # True 表示图像正常，False 表示损坏或格式异常无法正常查看
        "status": str,          # "valid" | "warning" | "corrupted"
        "error_type": str | None,
        "error_message": str | None,
        "size": int,
    }
    """
    result = {
        "path": file_path,
        "valid": True,
        "status": "valid",
        "error_type": None,
        "error_message": None,
        "size": 0,
    }

    try:
        if not os.path.exists(file_path):
            result["valid"] = False
            result["status"] = "corrupted"
            result["error_type"] = "文件未找到"
            result["error_message"] = "扫描过程中文件已不存在或路径无法访问"
            return result

        result["size"] = os.path.getsize(file_path)

        if result["size"] == 0:
            result["valid"] = False
            result["status"] = "corrupted"
            result["error_type"] = "空文件 (0字节)"
            result["error_message"] = "文件大小为 0 字节，内容已完全丢失"
            return result

        real_format, header = detect_file_signature(file_path)
        ext = Path(file_path).suffix.lower()

        if not real_format:
            result["valid"] = False
            result["status"] = "corrupted"
            if header and header == b"\x00" * len(header):
                result["error_type"] = "文件头清零损坏"
                result["error_message"] = f"文件头部全为 0x00 字节，数据已被清零 (后缀: {ext})"
            else:
                result["error_type"] = "未知或损坏的文件头"
                result["error_message"] = f"无法识别图像文件头魔数 (后缀: {ext})"
            return result

        # 检查文件扩展名与实际文件头格式是否一致（如 .\data\photo2test 中 .jpg 实为 GIF 错误占位图）
        expected_format = SUPPORTED_FORMATS.get(ext)
        if expected_format and real_format != expected_format:
            result["valid"] = False
            result["status"] = "corrupted"
            placeholder_msg = _detect_placeholder_anomaly(file_path, ext, real_format, result["size"])
            if placeholder_msg:
                result["error_type"] = "格式不匹配 (错误占位图)"
                result["error_message"] = placeholder_msg
            else:
                result["error_type"] = "格式不匹配"
                result["error_message"] = f"扩展名 {ext} 与实际内容 {real_format} 不符，可能导致无法打开"
            return result

        validators = {
            "JPEG": validate_jpeg,
            "PNG": validate_png,
            "GIF": validate_gif,
            "BMP": validate_bmp,
            "TIFF": validate_tiff,
            "WebP": validate_webp,
            "ICO": validate_ico,
        }

        if real_format not in validators:
            result["valid"] = False
            result["status"] = "corrupted"
            result["error_type"] = "不支持的格式"
            result["error_message"] = f"检测到格式 {real_format}，暂不支持深度校验"
            return result

        return validators[real_format](file_path, result)

    except PermissionError as e:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "权限被拒绝"
        result["error_message"] = f"操作系统拒绝访问该文件: {e}"
    except FileNotFoundError:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "文件未找到"
        result["error_message"] = "扫描过程中文件已消失"
    except OSError as e:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "磁盘读取错误"
        result["error_message"] = f"底层 I/O 读取异常 (可能存在磁盘物理坏道): {e}"
    except Exception as e:
        result["valid"] = False
        result["status"] = "corrupted"
        result["error_type"] = "解码错误"
        result["error_message"] = str(e)

    return result


# --- 多进程扫描引擎 ---

def worker_process(file_queue, result_queue, stop_event):
    """
    工作子进程：从有界队列获取文件路径，保证每个取出的文件必然向 result_queue 返回一条结果，
    彻底消除主进程计数死锁风险。
    """
    try:
        file_queue.cancel_join_thread()
        result_queue.cancel_join_thread()
    except Exception:
        pass

    while not stop_event.is_set():
        try:
            file_path = file_queue.get(block=True, timeout=0.1)
        except queue.Empty:
            continue
        except (EOFError, OSError):
            break

        if file_path is None:
            break

        try:
            res = validate_image(file_path)
        except BaseException as e:
            res = {
                "path": file_path,
                "valid": False,
                "status": "corrupted",
                "error_type": "校验进程异常",
                "error_message": str(e),
                "size": 0,
            }

        if stop_event.is_set():
            break

        try:
            result_queue.put(res, timeout=1.0)
        except Exception:
            break


def scan_directory(directory, extensions, num_processes, progress_callback, result_callback, stop_event, status_callback=None):
    """
    多进程扫描指定目录。
    修复点：
    1. 遍历目录阶段提供状态回调反馈；
    2. 使用后台 Feeder 线程 + 有界队列投喂路径，避免数万文件一次性塞爆 OS 管道；
    3. 主循环同时检查子进程存活状态，防止子进程意外退出导致永久死锁；
    4. 使用 cancel_join_thread() 确保停止扫描时瞬间退出不挂起。
    """
    ext_set = {e.lower() for e in extensions}
    file_list = []

    if status_callback:
        status_callback("正在检索目录文件...")

    last_notify = time.time()
    for root, dirs, files in os.walk(directory):
        if stop_event.is_set():
            break
        for file in files:
            ext = os.path.splitext(file)[1].lower()
            if ext in ext_set:
                file_list.append(os.path.join(root, file))
                if status_callback and len(file_list) % 500 == 0:
                    now = time.time()
                    if now - last_notify >= 0.2:
                        status_callback(f"正在检索目录... 已发现 {len(file_list)} 个图像文件")
                        last_notify = now

    total = len(file_list)
    if total == 0 or stop_event.is_set():
        return 0

    # 使用有界队列防止内存与管道膨胀
    queue_capacity = max(64, num_processes * 16)
    file_queue = multiprocessing.Queue(maxsize=queue_capacity)
    result_queue = multiprocessing.Queue()
    file_queue.cancel_join_thread()
    result_queue.cancel_join_thread()

    def _feed_files():
        try:
            for f_path in file_list:
                while not stop_event.is_set():
                    try:
                        file_queue.put(f_path, timeout=0.1)
                        break
                    except queue.Full:
                        continue
                if stop_event.is_set():
                    return
            for _ in range(num_processes):
                while not stop_event.is_set():
                    try:
                        file_queue.put(None, timeout=0.1)
                        break
                    except queue.Full:
                        continue
        except Exception:
            pass

    feeder_thread = threading.Thread(target=_feed_files, daemon=True)
    feeder_thread.start()

    processes = []
    for _ in range(num_processes):
        p = Process(target=worker_process, args=(file_queue, result_queue, stop_event))
        p.daemon = True
        p.start()
        processes.append(p)

    processed = 0
    while processed < total and not stop_event.is_set():
        try:
            result = result_queue.get(timeout=0.1)
            processed += 1
            progress_callback(processed, total)
            result_callback(result)
        except queue.Empty:
            # 若所有工作进程已退出且结果队列已空，则立即跳出循环，彻底杜绝死锁
            if not any(p.is_alive() for p in processes) and result_queue.empty():
                break
            continue
        except Exception:
            continue

    if stop_event.is_set():
        for p in processes:
            if p.is_alive():
                try:
                    p.terminate()
                except Exception:
                    pass

    for p in processes:
        p.join(timeout=0.2)

    try:
        file_queue.close()
        result_queue.close()
    except Exception:
        pass

    return processed


def format_size(size):
    if size <= 0:
        return "0 B"
    units = ["B", "KB", "MB", "GB"]
    i = 0
    s = float(size)
    while s >= 1024 and i < len(units) - 1:
        s /= 1024
        i += 1
    return f"{s:.2f} {units[i]}"


# --- GUI 界面 ---

class ImageCheckApp:
    def __init__(self, root):
        self.root = root
        self.root.title("图像完整性检测器")

        # 赛博朋克配色方案
        self.BG_DARK = "#0d0221"
        self.BG_LIGHT = "#1a0b38"
        self.CYAN = "#00f3ff"
        self.MAGENTA = "#ff00ff"
        self.PURPLE = "#9d00ff"
        self.ORANGE = "#ffaa00"
        self.TEXT_COLOR = "#e0e0e0"

        # 窗口尺寸
        self.root.geometry("1150x780")
        self.root.minsize(1000, 700)
        self.root.configure(background=self.BG_DARK)

        self.style = ttk.Style()
        self.style.theme_use("clam")

        self.results = []
        self.is_scanning = False
        self.stop_event = multiprocessing.Event()

        # 线程安全的 UI 批量更新队列与状态缓存
        self.ui_queue = queue.Queue()
        self.current_processed = 0
        self.current_total = 0
        self.status_message_override = None

        self.valid_count = 0
        self.warning_count = 0
        self.corrupted_count = 0
        self.displayed_valid_count = 0
        self.start_time = 0
        self._sort_reverse = {}

        self.setup_styles()
        self.create_widgets()

    def setup_styles(self):
        # 框架
        self.style.configure("TFrame", background=self.BG_DARK)
        self.style.configure("TLabelframe", background=self.BG_DARK, foreground=self.CYAN, borderwidth=1)
        self.style.configure("TLabelframe.Label", background=self.BG_DARK, foreground=self.CYAN, font=("Microsoft YaHei", 10, "bold"))

        # 标签
        self.style.configure("TLabel", background=self.BG_DARK, foreground=self.TEXT_COLOR, font=("Microsoft YaHei", 10))
        self.style.configure("Header.TLabel", background=self.BG_DARK, foreground=self.CYAN, font=("Microsoft YaHei", 20, "bold"))
        self.style.configure("Version.TLabel", background=self.BG_DARK, foreground="#a0a0a0", font=("Consolas", 9))

        # 按钮
        self.style.configure("TButton", font=("Microsoft YaHei", 10), borderwidth=0)
        self.style.configure("Primary.TButton", background=self.CYAN, foreground=self.BG_DARK)
        self.style.map("Primary.TButton", background=[("active", self.MAGENTA), ("disabled", "#333333")])

        self.style.configure("Action.TButton", background=self.PURPLE, foreground=self.TEXT_COLOR)
        self.style.map("Action.TButton", background=[("active", self.MAGENTA), ("disabled", "#333333")])

        # 输入框与复选框
        self.style.configure("TEntry", fieldbackground=self.BG_LIGHT, foreground=self.CYAN, insertcolor=self.CYAN)
        self.style.configure("TCheckbutton", background=self.BG_DARK, foreground=self.TEXT_COLOR, indicatorcolor=self.CYAN)
        self.style.map("TCheckbutton", background=[("active", self.BG_DARK)], foreground=[("active", self.CYAN)])

        # 组合框
        self.style.configure("TCombobox", fieldbackground=self.BG_LIGHT, foreground=self.CYAN, arrowcolor=self.CYAN)

        # 进度条
        self.style.configure("TProgressbar", thickness=10, troughcolor=self.BG_LIGHT, background=self.CYAN, bordercolor=self.BG_DARK)

        # 表格
        self.style.configure(
            "Treeview",
            background=self.BG_LIGHT,
            foreground=self.TEXT_COLOR,
            fieldbackground=self.BG_LIGHT,
            rowheight=28,
            font=("Microsoft YaHei", 9),
        )
        self.style.configure(
            "Treeview.Heading",
            background="#2d1b5a",
            foreground=self.CYAN,
            font=("Microsoft YaHei", 10, "bold"),
        )
        self.style.map("Treeview", background=[("selected", self.PURPLE)])

    def create_widgets(self):
        # 顶部栏
        header_frame = ttk.Frame(self.root, padding=(10, 15, 10, 5))
        header_frame.pack(fill=X)

        # 居中标题
        ttk.Label(header_frame, text="Kit 图 像 完 整 性 检 测 器", style="Header.TLabel").pack(expand=True)
        # 右侧版本号
        ttk.Label(header_frame, text="v2.0 by tsingkk@github", style="Version.TLabel").place(relx=1.0, rely=0.7, anchor="se")

        main_frame = ttk.Frame(self.root, padding=20)
        main_frame.pack(fill=BOTH, expand=True)

        self.create_control_panel(main_frame)
        self.create_progress_area(main_frame)
        self.create_results_area(main_frame)
        self.create_status_bar(main_frame)

    def create_control_panel(self, parent):
        control_frame = ttk.LabelFrame(parent, text="", padding=15)
        control_frame.pack(fill=X, pady=(0, 15))

        # 目录选择行
        dir_frame = ttk.Frame(control_frame)
        dir_frame.pack(fill=X, pady=(0, 10))
        ttk.Label(dir_frame, text="扫描目录:").pack(side=LEFT)
        self.dir_entry = ttk.Entry(dir_frame, font=("Microsoft YaHei", 10))
        self.dir_entry.pack(side=LEFT, fill=X, expand=True, padx=10)
        self.browse_btn = ttk.Button(dir_frame, text="浏览...", command=self.browse_directory, width=10, style="Action.TButton")
        self.browse_btn.pack(side=LEFT, padx=2)
        ttk.Button(dir_frame, text="✕", command=self.clear_directory, width=3, style="Action.TButton").pack(side=LEFT, padx=(5, 0))

        # 选项行
        options_line = ttk.Frame(control_frame)
        options_line.pack(fill=X, pady=5)

        # 格式复选框组
        fmt_frame = ttk.Frame(options_line)
        fmt_frame.pack(side=LEFT)
        ttk.Label(fmt_frame, text="格式:").pack(side=LEFT, padx=(0, 5))
        self.format_vars = {}

        unique_formats = {}
        for ext, label in SUPPORTED_FORMATS.items():
            if label not in unique_formats:
                unique_formats[label] = []
            unique_formats[label].append(ext)

        for label, exts in unique_formats.items():
            var = BooleanVar(value=True)
            for ext in exts:
                self.format_vars[ext] = var
            ttk.Checkbutton(fmt_frame, text=label, variable=var).pack(side=LEFT, padx=6)

        ttk.Button(fmt_frame, text="全选", command=lambda: self.toggle_all_formats(True), width=5, style="Action.TButton").pack(side=LEFT, padx=(6, 2))
        ttk.Button(fmt_frame, text="清空", command=lambda: self.toggle_all_formats(False), width=5, style="Action.TButton").pack(side=LEFT, padx=2)

        # 进程数与过滤选择
        proc_frame = ttk.Frame(options_line)
        proc_frame.pack(side=RIGHT)

        self.only_abnormal_var = BooleanVar(value=False)
        ttk.Checkbutton(
            proc_frame,
            text="仅显示异常项",
            variable=self.only_abnormal_var,
            command=self.refresh_tree_filter,
        ).pack(side=LEFT, padx=(0, 15))

        ttk.Label(proc_frame, text="并发进程:").pack(side=LEFT, padx=5)

        cores = os.cpu_count() or 4
        potential_values = [1, 2, 4, 8, 12, 16, 24, 32, 64]
        proc_values = [str(v) for v in potential_values if v <= cores]
        if str(cores) not in proc_values:
            proc_values.append(str(cores))
            proc_values.sort(key=lambda x: int(x))

        self.process_var = StringVar(value=str(min(4, cores)))
        process_combo = ttk.Combobox(proc_frame, textvariable=self.process_var, values=proc_values, width=5, state="readonly")
        process_combo.pack(side=LEFT, padx=5)

        # 按钮行
        btn_line = ttk.Frame(control_frame)
        btn_line.pack(fill=X, pady=(15, 0))
        self.start_btn = ttk.Button(btn_line, text="⚡ 开始扫描", command=self.start_scan, style="Primary.TButton", width=18)
        self.start_btn.pack(side=LEFT, padx=5)
        self.stop_btn = ttk.Button(btn_line, text="■ 停止", command=self.stop_scan, state=DISABLED, style="Action.TButton", width=12)
        self.stop_btn.pack(side=LEFT, padx=5)
        self.export_btn = ttk.Button(btn_line, text="导出报告", command=self.export_dialog, style="Action.TButton", width=15)
        self.export_btn.pack(side=RIGHT, padx=5)
        self.clear_btn = ttk.Button(btn_line, text="清除记录", command=self.clear_results, style="Action.TButton", width=12)
        self.clear_btn.pack(side=RIGHT, padx=5)

    def create_progress_area(self, parent):
        progress_frame = ttk.Frame(parent, padding=(0, 0, 0, 15))
        progress_frame.pack(fill=X)
        self.progress_var = DoubleVar()
        self.progress_bar = ttk.Progressbar(progress_frame, variable=self.progress_var, maximum=100)
        self.progress_bar.pack(fill=X, pady=5)
        info_frame = ttk.Frame(progress_frame)
        info_frame.pack(fill=X)
        self.progress_label = ttk.Label(info_frame, text="系统准备就绪 (双击列表项可在资源管理器中定位文件)", foreground="#a0a0a0")
        self.progress_label.pack(side=LEFT)
        self.file_count_label = ttk.Label(info_frame, text="0 / 0", foreground=self.CYAN)
        self.file_count_label.pack(side=RIGHT)

    def create_results_area(self, parent):
        results_frame = ttk.Frame(parent)
        results_frame.pack(fill=BOTH, expand=True)
        results_frame.rowconfigure(0, weight=1)
        results_frame.columnconfigure(0, weight=1)

        self.STATUS_COL_WIDTH = 76
        self.SIZE_COL_WIDTH = 88
        self.DEFAULT_PATH_WIDTH = 380
        self.DEFAULT_ERROR_WIDTH = 545
        self._tree_font = tkfont.Font(family="Microsoft YaHei", size=9)

        columns = ("status", "path", "size", "error")
        self.tree = ttk.Treeview(results_frame, columns=columns, show="headings", selectmode="browse")
        self.tree.heading("status", text="状态 ⇅", command=lambda: self.sort_tree("status"))
        self.tree.heading("path", text="文件路径 ⇅", command=lambda: self.sort_tree("path"))
        self.tree.heading("size", text="大小 ⇅", command=lambda: self.sort_tree("size"))
        self.tree.heading("error", text="故障原因与详情 ⇅", command=lambda: self.sort_tree("error"))

        # 关键：将 stretch 设为 False，避免 Tkinter 强行将超宽列压缩在可视窗口内导致横向滚动条失效
        self.tree.column("status", width=self.STATUS_COL_WIDTH, minwidth=68, anchor="center", stretch=False)
        self.tree.column("path", width=self.DEFAULT_PATH_WIDTH, minwidth=200, stretch=False)
        self.tree.column("size", width=self.SIZE_COL_WIDTH, minwidth=72, anchor="center", stretch=False)
        self.tree.column("error", width=self.DEFAULT_ERROR_WIDTH, minwidth=360, stretch=False)
        self._reset_column_widths()

        vsb = ttk.Scrollbar(results_frame, orient=VERTICAL, command=self.tree.yview)
        hsb = ttk.Scrollbar(results_frame, orient=HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        self.tree.tag_configure("corrupted", foreground="#ff4d4d", background="#2a0000")
        self.tree.tag_configure("warning", foreground=self.ORANGE, background="#261c00")
        self.tree.tag_configure("valid", foreground="#00ff00")

        # 双击打开文件所在目录并选中
        self.tree.bind("<Double-1>", self.on_tree_double_click)
        # 监听表格尺寸变化：窗口放大时自动铺满，窗口缩小或内容超长时保持真实列宽并启用横向滚动条
        self.tree.bind("<Configure>", self._on_tree_configure)

    def _reset_column_widths(self):
        self._req_path_width = self.DEFAULT_PATH_WIDTH
        self._req_error_width = self.DEFAULT_ERROR_WIDTH
        self._max_path_chars = 0
        self._max_error_chars = 0
        self._apply_column_widths()

    def _apply_column_widths(self, tree_width=None):
        if tree_width is None:
            tree_width = self.tree.winfo_width()
        fixed = self.STATUS_COL_WIDTH + self.SIZE_COL_WIDTH
        total_req = fixed + self._req_path_width + self._req_error_width

        if tree_width > total_req + 4:
            # 窗口宽度充足时，将富余宽度按比例分配给路径列与故障详情列以铺满表格
            extra = tree_width - total_req - 4
            path_w = self._req_path_width + int(extra * 0.45)
            err_w = self._req_error_width + (extra - int(extra * 0.45))
        else:
            # 内容总宽超出窗口可视宽度时，保持实际所需宽度，激活底部横向滚动条
            path_w = self._req_path_width
            err_w = self._req_error_width

        self.tree.column("path", width=path_w)
        self.tree.column("error", width=err_w)

    def _on_tree_configure(self, event):
        if event and event.width > 100:
            self._apply_column_widths(event.width)

    def _adjust_column_widths_for_row(self, values):
        """当文件路径或故障原因超长时，动态扩展列宽以触发横向滚动条，确保内容不被截断"""
        path_str = values[1] or ""
        err_str = values[3] or ""
        updated = False

        if len(path_str) > self._max_path_chars:
            self._max_path_chars = len(path_str)
            px = self._tree_font.measure(path_str) + 32
            if px > self._req_path_width:
                self._req_path_width = px
                updated = True

        if len(err_str) > self._max_error_chars:
            self._max_error_chars = len(err_str)
            px = self._tree_font.measure(err_str) + 32
            if px > self._req_error_width:
                self._req_error_width = px
                updated = True

        if updated:
            self._apply_column_widths()
        return updated

    def create_status_bar(self, parent):
        status_frame = ttk.Frame(parent, padding=(5, 15, 5, 0))
        status_frame.pack(fill=X)

        ttk.Label(status_frame, text="[ 实时统计 ] ", foreground="#a0a0a0").pack(side=LEFT)
        self.total_label = ttk.Label(status_frame, text="总计: 0", font=("Consolas", 11, "bold"), foreground="#ffffff")
        self.total_label.pack(side=LEFT, padx=15)
        self.valid_label = ttk.Label(status_frame, text="正常: 0", font=("Consolas", 11, "bold"), foreground="#00ff00")
        self.valid_label.pack(side=LEFT, padx=15)
        self.warning_label = ttk.Label(status_frame, text="警告: 0", font=("Consolas", 11, "bold"), foreground=self.ORANGE)
        self.warning_label.pack(side=LEFT, padx=15)
        self.corrupted_label = ttk.Label(status_frame, text="损坏: 0", font=("Consolas", 11, "bold"), foreground=self.MAGENTA)
        self.corrupted_label.pack(side=LEFT, padx=15)
        self.time_label = ttk.Label(status_frame, text="耗时: 0s", font=("Consolas", 11, "bold"), foreground=self.CYAN)
        self.time_label.pack(side=LEFT, padx=15)

    # --- 交互与逻辑处理 ---

    def toggle_all_formats(self, state: bool):
        for var in set(self.format_vars.values()):
            var.set(state)

    def browse_directory(self):
        d = filedialog.askdirectory()
        if d:
            self.dir_entry.delete(0, END)
            self.dir_entry.insert(0, d)

    def clear_directory(self):
        self.dir_entry.delete(0, END)

    def on_tree_double_click(self, event):
        selected = self.tree.selection()
        if not selected:
            return
        values = self.tree.item(selected[0], "values")
        if not values or len(values) < 2:
            return
        file_path = values[1]
        if os.path.exists(file_path):
            try:
                if sys.platform.startswith("win"):
                    subprocess.Popen(["explorer", "/select,", os.path.normpath(file_path)])
                elif sys.platform == "darwin":
                    subprocess.Popen(["open", "-R", file_path])
                else:
                    subprocess.Popen(["xdg-open", os.path.dirname(file_path)])
            except Exception:
                pass

    def sort_tree(self, col):
        if self.is_scanning:
            return
        reverse = self._sort_reverse.get(col, False)
        items = [(self.tree.set(k, col), k) for k in self.tree.get_children("")]

        if col == "size":
            unit_map = {"B": 1, "KB": 1024, "MB": 1024**2, "GB": 1024**3}
            def _parse_size(val_str):
                parts = val_str.split()
                if len(parts) == 2:
                    try:
                        return float(parts[0]) * unit_map.get(parts[1], 1)
                    except ValueError:
                        return 0
                return 0
            items.sort(key=lambda t: _parse_size(t[0]), reverse=reverse)
        else:
            items.sort(key=lambda t: t[0], reverse=reverse)

        for index, (_, k) in enumerate(items):
            self.tree.move(k, "", index)
        self._sort_reverse[col] = not reverse

    def _format_row_data(self, r):
        status = r.get("status", "valid" if r["valid"] else "corrupted")
        if not r["valid"] or status == "corrupted":
            tags = ("corrupted",)
            st = "✖ 损坏"
        elif status == "warning":
            tags = ("warning",)
            st = "▲ 警告"
        else:
            tags = ("valid",)
            st = "● 正常"

        err_type = r.get("error_type") or ""
        err_msg = r.get("error_message") or ""
        if err_type and err_msg:
            err_display = f"[{err_type}] {err_msg}"
        else:
            err_display = err_type or err_msg

        return st, (st, r["path"], format_size(r["size"]), err_display), tags, status

    def refresh_tree_filter(self):
        """切换‘仅显示异常项’时动态重绘列表"""
        for i in self.tree.get_children():
            self.tree.delete(i)
        self.displayed_valid_count = 0
        self._reset_column_widths()
        only_abnormal = self.only_abnormal_var.get()

        for r in self.results:
            _, values, tags, status = self._format_row_data(r)
            if status == "valid":
                if only_abnormal or self.displayed_valid_count >= MAX_VALID_TREE_ITEMS:
                    continue
                self.displayed_valid_count += 1
            self._adjust_column_widths_for_row(values)
            self.tree.insert("", END, values=values, tags=tags)

    def start_scan(self):
        if self.is_scanning:
            return
        directory = self.dir_entry.get().strip()
        if not directory or not os.path.isdir(directory):
            messagebox.showwarning("注意", "请选择有效的扫描目录。")
            return
        exts = [e for e, v in self.format_vars.items() if v.get()]
        if not exts:
            messagebox.showwarning("注意", "请至少选择一种图像格式。")
            return
        try:
            num = int(self.process_var.get())
        except Exception:
            num = 4

        # 清空状态与残留队列
        while not self.ui_queue.empty():
            try:
                self.ui_queue.get_nowait()
            except queue.Empty:
                break

        self.results = []
        self.valid_count = 0
        self.warning_count = 0
        self.corrupted_count = 0
        self.displayed_valid_count = 0
        self.current_processed = 0
        self.current_total = 0
        self.status_message_override = "正在检索目录文件..."
        self.start_time = time.time()

        for i in self.tree.get_children():
            self.tree.delete(i)
        self._reset_column_widths()
        self.progress_var.set(0)
        self.file_count_label.config(text="0 / 0")
        self.update_stats()

        self.is_scanning = True
        self.stop_event.clear()
        self.start_btn.config(state=DISABLED)
        self.stop_btn.config(state=NORMAL)

        # 启动 UI 节流轮询定时器（每 80ms 批量刷新一次界面，彻底解决海量图片 UI 假死）
        self.root.after(80, self._poll_ui_queue)
        threading.Thread(target=self.run_scan, args=(directory, exts, num), daemon=True).start()

    def run_scan(self, d, e, n):
        scan_error = None
        try:
            scan_directory(
                d,
                e,
                n,
                self.update_progress,
                self.add_result,
                self.stop_event,
                status_callback=self.update_status_text,
            )
        except Exception as ex:
            scan_error = str(ex)
        self.root.after(0, lambda: self.scan_complete(scan_error))

    def update_status_text(self, text):
        self.status_message_override = text

    def update_progress(self, c, t):
        self.current_processed = c
        self.current_total = t
        self.status_message_override = None

    def add_result(self, r):
        self.ui_queue.put(r)

    def _drain_ui_queue_batch(self, max_batch=500):
        batch = []
        while len(batch) < max_batch:
            try:
                batch.append(self.ui_queue.get_nowait())
            except queue.Empty:
                break

        if batch:
            only_abnormal = self.only_abnormal_var.get()
            last_item_id = None
            for r in batch:
                self.results.append(r)
                _, values, tags, status = self._format_row_data(r)
                if not r["valid"] or status == "corrupted":
                    self.corrupted_count += 1
                    self._adjust_column_widths_for_row(values)
                    # 损坏项优先展示
                    last_item_id = self.tree.insert("", END, values=values, tags=tags)
                elif status == "warning":
                    self.valid_count += 1
                    self.warning_count += 1
                    self._adjust_column_widths_for_row(values)
                    last_item_id = self.tree.insert("", END, values=values, tags=tags)
                else:
                    self.valid_count += 1
                    if not only_abnormal and self.displayed_valid_count < MAX_VALID_TREE_ITEMS:
                        self.displayed_valid_count += 1
                        self._adjust_column_widths_for_row(values)
                        last_item_id = self.tree.insert("", END, values=values, tags=tags)

            if last_item_id is not None:
                self.tree.see(last_item_id)

        # 更新进度条与实时耗时
        if self.current_total > 0:
            c, t = self.current_processed, self.current_total
            self.progress_var.set((c / t) * 100)
            extra_note = ""
            if not self.only_abnormal_var.get() and self.valid_count > MAX_VALID_TREE_ITEMS:
                extra_note = f" (正常项仅在列表展示前 {MAX_VALID_TREE_ITEMS} 条，异常项全部展示)"
            self.progress_label.config(text=f"内核分析中... {c}/{t}{extra_note}")
            self.file_count_label.config(text=f"{c} / {t}")
        elif self.status_message_override:
            self.progress_label.config(text=self.status_message_override)

        self.update_stats()

    def _poll_ui_queue(self):
        if not self.is_scanning:
            return
        self._drain_ui_queue_batch(max_batch=400)
        if self.is_scanning:
            self.root.after(80, self._poll_ui_queue)

    def _add_result(self, r):
        """保留单条插入方法以兼容外部调用"""
        self.ui_queue.put(r)
        self._drain_ui_queue_batch(max_batch=100)

    def update_stats(self):
        t = self.valid_count + self.corrupted_count
        elapsed = int(time.time() - self.start_time) if self.start_time > 0 else 0
        self.total_label.config(text=f"总计: {t}")
        self.valid_label.config(text=f"正常: {self.valid_count}")
        self.warning_label.config(text=f"警告: {self.warning_count}")
        self.corrupted_label.config(text=f"损坏: {self.corrupted_count}")
        self.time_label.config(text=f"耗时: {elapsed}s")

    def scan_complete(self, error_msg=None):
        self.is_scanning = False
        # 排空队列中剩余的所有结果
        while not self.ui_queue.empty():
            self._drain_ui_queue_batch(max_batch=1000)

        self.update_stats()

        if error_msg:
            messagebox.showerror("错误", error_msg)

        if self.stop_event.is_set():
            self.progress_label.config(text="扫描已中止")
        elif self.current_total == 0:
            self.progress_label.config(text="扫描完成：所选目录下未找到匹配的图像文件")
        else:
            self.progress_label.config(text=f"扫描完成 (共检测 {len(self.results)} 个文件，发现 {self.corrupted_count} 个损坏，{self.warning_count} 个警告)")

        self.start_btn.config(state=NORMAL)
        self.stop_btn.config(state=DISABLED)

    def stop_scan(self):
        self.stop_event.set()
        self.stop_btn.config(state=DISABLED)
        self.progress_label.config(text="正在切断进程...")

    def clear_results(self):
        if self.is_scanning:
            return
        while not self.ui_queue.empty():
            try:
                self.ui_queue.get_nowait()
            except queue.Empty:
                break
        self.results = []
        self.valid_count = 0
        self.warning_count = 0
        self.corrupted_count = 0
        self.displayed_valid_count = 0
        self.current_processed = 0
        self.current_total = 0
        self.start_time = 0
        for i in self.tree.get_children():
            self.tree.delete(i)
        self._reset_column_widths()
        self.update_stats()
        self.progress_var.set(0)
        self.file_count_label.config(text="0 / 0")
        self.progress_label.config(text="系统准备就绪")

    def export_dialog(self):
        if not self.results:
            messagebox.showinfo("提示", "当前没有可导出的检测记录。")
            return

        # 格式选择窗口
        choice_win = Toplevel(self.root)
        choice_win.title("导出格式")
        choice_win.geometry("420x160")
        choice_win.configure(background=self.BG_DARK)
        choice_win.resizable(False, False)
        choice_win.transient(self.root)
        choice_win.grab_set()

        # 居中
        self.root.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - 210
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - 80
        choice_win.geometry(f"+{x}+{y}")

        ttk.Label(choice_win, text="请选择导出的文件格式：", font=("Microsoft YaHei", 10), padding=20).pack()

        btn_frame = ttk.Frame(choice_win)
        btn_frame.pack(pady=10)

        def select_fmt(f):
            choice_win.destroy()
            self._save_report(f)

        ttk.Button(btn_frame, text="CSV 表格", style="Action.TButton", width=11, command=lambda: select_fmt("csv")).pack(side=LEFT, padx=8)
        ttk.Button(btn_frame, text="TXT 文本", style="Action.TButton", width=11, command=lambda: select_fmt("txt")).pack(side=LEFT, padx=8)
        ttk.Button(btn_frame, text="JSON 数据", style="Action.TButton", width=11, command=lambda: select_fmt("json")).pack(side=LEFT, padx=8)

    def _save_report(self, fmt):
        type_map = {
            "csv": [("CSV 表格", "*.csv")],
            "txt": [("TXT 文本", "*.txt")],
            "json": [("JSON 数据", "*.json")],
        }
        file_path = filedialog.asksaveasfilename(
            initialfile="图像完整性检测报告",
            defaultextension=f".{fmt}",
            filetypes=type_map.get(fmt, [("所有文件", "*.*")]),
        )

        if file_path:
            try:
                # 排序优先级：损坏(0) -> 警告(1) -> 正常(2)
                def _sort_key(item):
                    st = item.get("status", "valid" if item["valid"] else "corrupted")
                    order = 0 if (not item["valid"] or st == "corrupted") else (1 if st == "warning" else 2)
                    return (order, item["path"])

                sorted_results = sorted(self.results, key=_sort_key)

                if fmt == "csv":
                    with open(file_path, "w", newline="", encoding="utf-8-sig") as f:
                        w = csv.writer(f)
                        w.writerow(["状态", "路径", "大小", "故障原因", "详细说明"])
                        for r in sorted_results:
                            st = r.get("status", "valid" if r["valid"] else "corrupted")
                            st_label = "损坏" if not r["valid"] else ("警告" if st == "warning" else "正常")
                            w.writerow([
                                st_label,
                                r["path"],
                                format_size(r["size"]),
                                r["error_type"] or "",
                                r["error_message"] or "",
                            ])
                elif fmt == "txt":
                    with open(file_path, "w", encoding="utf-8") as f:
                        f.write("=== 图像完整性检测报告 ===\n")
                        f.write(f"生成时间: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                        f.write(f"总计: {len(self.results)} | 正常: {self.valid_count} | 警告: {self.warning_count} | 损坏: {self.corrupted_count}\n")
                        f.write("=" * 40 + "\n\n")

                        f.write("--- 损坏文件列表 ---\n")
                        corrupted = [r for r in sorted_results if not r["valid"]]
                        if not corrupted:
                            f.write("无损坏文件。\n")
                        else:
                            for r in corrupted:
                                f.write(f"[{r['error_type']}] {r['path']} ({format_size(r['size'])})\n")
                                if r["error_message"]:
                                    f.write(f"    详情: {r['error_message']}\n")
                        f.write("\n")

                        warnings_list = [r for r in sorted_results if r["valid"] and r.get("status") == "warning"]
                        if warnings_list:
                            f.write("--- 警告文件列表 (图像像素完好，但扩展名或元数据异常) ---\n")
                            for r in warnings_list:
                                f.write(f"[{r['error_type']}] {r['path']} ({format_size(r['size'])})\n")
                                if r["error_message"]:
                                    f.write(f"    详情: {r['error_message']}\n")
                            f.write("\n")

                        f.write("--- 正常文件列表 ---\n")
                        valid = [r for r in sorted_results if r["valid"] and r.get("status", "valid") == "valid"]
                        if not valid:
                            f.write("无正常文件。\n")
                        else:
                            for r in valid:
                                f.write(f" [正常] {r['path']} ({format_size(r['size'])})\n")
                        f.write("\n")
                elif fmt == "json":
                    report_data = {
                        "generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                        "summary": {
                            "total": len(self.results),
                            "valid": self.valid_count,
                            "warning": self.warning_count,
                            "corrupted": self.corrupted_count,
                        },
                        "results": sorted_results,
                    }
                    with open(file_path, "w", encoding="utf-8") as f:
                        json.dump(report_data, f, ensure_ascii=False, indent=2)

                messagebox.showinfo("成功", f"报告已生成至:\n{file_path}")
            except Exception as e:
                messagebox.showerror("错误", f"导出失败: {str(e)}")


def main():
    multiprocessing.freeze_support()
    root = Tk()
    try:
        root.tk.call("tk", "scaling", 1.25)
    except Exception:
        pass
    app = ImageCheckApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
