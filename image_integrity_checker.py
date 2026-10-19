import os
import sys
import json
import csv
import struct
import time
import threading
import multiprocessing
from multiprocessing import Process, Queue, Event
import queue
from pathlib import Path
from tkinter import ttk, filedialog, messagebox
from tkinter import *
import io
from PIL import Image

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

# --- 核心逻辑 ---

def get_real_format(file_path):
    try:
        with open(file_path, "rb") as f:
            header = f.read(12)
            if not header:
                return None
            if header.startswith(b"\xff\xd8\xff"):
                return "JPEG"
            if header.startswith(b"\x89PNG\r\n\x1a\n"):
                return "PNG"
            if header.startswith(b"GIF87a") or header.startswith(b"GIF89a"):
                return "GIF"
            if header.startswith(b"BM"):
                return "BMP"
            if header.startswith(b"II\x2a\x00") or header.startswith(b"MM\x00\x2a"):
                return "TIFF"
            if header.startswith(b"RIFF") and header[8:12] == b"WEBP":
                return "WebP"
            if header.startswith(b"\x00\x00\x01\x00"):
                return "ICO"
    except:
        pass
    return None

def validate_image(file_path):
    result = {
        "path": file_path,
        "valid": True,
        "error_type": None,
        "error_message": None,
        "size": 0,
    }

    try:
        if not os.path.exists(file_path):
            result["valid"] = False
            result["error_type"] = "文件未找到"
            return result

        result["size"] = os.path.getsize(file_path)

        if result["size"] == 0:
            result["valid"] = False
            result["error_type"] = "无效文件头"
            result["error_message"] = "文件内容为空"
            return result

        real_format = get_real_format(file_path)
        ext = Path(file_path).suffix.lower()

        if not real_format:
            result["valid"] = False
            result["error_type"] = "未知格式"
            result["error_message"] = f"无法识别图像头信息 (后缀: {ext})"
            return result

        expected_format = SUPPORTED_FORMATS.get(ext)
        if expected_format and real_format != expected_format:
            result["valid"] = False
            result["error_type"] = "格式不匹配"
            result["error_message"] = f"扩展名 {ext} 与实际内容 {real_format} 不符"
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

        if real_format in validators:
            return validators[real_format](file_path, result)
        else:
            result["valid"] = False
            result["error_type"] = "不支持的格式"
            return result

    except PermissionError:
        result["valid"] = False
        result["error_type"] = "权限被拒绝"
    except Exception as e:
        result["valid"] = False
        result["error_type"] = "解码错误"
        result["error_message"] = str(e)

    return result

def deep_verify(file_path, result):
    try:
        with Image.open(file_path) as img:
            img.verify()
        with Image.open(file_path) as img:
            img.load()
        return result
    except Exception as e:
        result["valid"] = False
        result["error_type"] = "解码错误"
        result["error_message"] = str(e)
        return result

def validate_jpeg(file_path, result):
    return deep_verify(file_path, result)

def validate_png(file_path, result): return deep_verify(file_path, result)
def validate_gif(file_path, result): return deep_verify(file_path, result)
def validate_bmp(file_path, result): return deep_verify(file_path, result)
def validate_tiff(file_path, result): return deep_verify(file_path, result)
def validate_webp(file_path, result): return deep_verify(file_path, result)
def validate_ico(file_path, result): return deep_verify(file_path, result)

def worker_process(file_queue, result_queue, stop_event):
    while not stop_event.is_set():
        try:
            file_path = file_queue.get(block=True, timeout=0.1)
            if file_path is None: break
            result = validate_image(file_path)
            if stop_event.is_set(): break
            result_queue.put(result)
        except queue.Empty: continue
        except EOFError: break
        except Exception: continue

def scan_directory(directory, extensions, num_processes, progress_callback, result_callback, stop_event):
    file_list = []
    for root, dirs, files in os.walk(directory):
        if stop_event.is_set(): break
        for file in files:
            ext = Path(file).suffix.lower()
            if ext in extensions:
                file_list.append(os.path.join(root, file))
    
    total = len(file_list)
    if total == 0 or stop_event.is_set(): return 0
    
    file_queue = multiprocessing.Queue()
    result_queue = multiprocessing.Queue()
    for f in file_list: file_queue.put(f)
    for _ in range(num_processes): file_queue.put(None)
    
    processes = []
    for _ in range(num_processes):
        p = Process(target=worker_process, args=(file_queue, result_queue, stop_event))
        p.daemon = True
        p.start()
        processes.append(p)
    
    processed = 0
    while processed < total:
        if stop_event.is_set(): break
        try:
            result = result_queue.get(timeout=0.1)
            processed += 1
            progress_callback(processed, total)
            result_callback(result)
        except queue.Empty: continue
        except Exception: continue
        
    if stop_event.is_set():
        for p in processes: p.terminate()
        
    for p in processes: p.join(timeout=0.2)
    return processed

def format_size(size):
    if size == 0: return "0 B"
    units = ["B", "KB", "MB", "GB"]
    i = 0
    while size >= 1024 and i < len(units) - 1:
        size /= 1024
        i += 1
    return f"{size:.2f} {units[i]}"

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
        self.TEXT_COLOR = "#e0e0e0"

        # 增加默认窗口尺寸
        self.root.geometry("1100x780")
        self.root.minsize(1000, 700)
        self.root.configure(background=self.BG_DARK)

        self.style = ttk.Style()
        self.style.theme_use("clam")

        self.results = []
        self.is_scanning = False
        self.stop_event = multiprocessing.Event()

        self.valid_count = 0
        self.corrupted_count = 0
        self.start_time = 0

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
        self.style.map("Action.TButton", background=[("active", self.MAGENTA)])

        # 输入框与复选框
        self.style.configure("TEntry", fieldbackground=self.BG_LIGHT, foreground=self.CYAN, insertcolor=self.CYAN)
        self.style.configure("TCheckbutton", background=self.BG_DARK, foreground=self.TEXT_COLOR, indicatorcolor=self.CYAN)
        self.style.map("TCheckbutton", background=[("active", self.BG_DARK)], foreground=[("active", self.CYAN)])

        # 组合框
        self.style.configure("TCombobox", fieldbackground=self.BG_LIGHT, foreground=self.CYAN, arrowcolor=self.CYAN)

        # 进度条
        self.style.configure("TProgressbar", thickness=10, troughcolor=self.BG_LIGHT, background=self.CYAN, bordercolor=self.BG_DARK)

        # 表格
        self.style.configure("Treeview", 
                           background=self.BG_LIGHT, 
                           foreground=self.TEXT_COLOR, 
                           fieldbackground=self.BG_LIGHT,
                           rowheight=28,
                           font=("Microsoft YaHei", 9))
        self.style.configure("Treeview.Heading", 
                           background="#2d1b5a", 
                           foreground=self.CYAN, 
                           font=("Microsoft YaHei", 10, "bold"))
        self.style.map("Treeview", background=[("selected", self.PURPLE)])

    def create_widgets(self):
        # 顶部栏
        header_frame = ttk.Frame(self.root, padding=(10, 15, 10, 5))
        header_frame.pack(fill=X)
        
        # 居中标题
        ttk.Label(header_frame, text="Kit 图 像 完 整 性 检 测 器", style="Header.TLabel").pack(expand=True)
        # 右侧版本号
        ttk.Label(header_frame, text="v1.0 by tsingkk@github", style="Version.TLabel").place(relx=1.0, rely=0.7, anchor="se")

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
        
        # 从 SUPPORTED_FORMATS 动态生成 (去重显示名)
        unique_formats = {}
        for ext, label in SUPPORTED_FORMATS.items():
            if label not in unique_formats:
                unique_formats[label] = []
            unique_formats[label].append(ext)
            
        for label, exts in unique_formats.items():
            var = BooleanVar(value=True)
            for ext in exts:
                self.format_vars[ext] = var
            ttk.Checkbutton(fmt_frame, text=label, variable=var).pack(side=LEFT, padx=8)

        # 进程数选择
        proc_frame = ttk.Frame(options_line)
        proc_frame.pack(side=RIGHT)
        ttk.Label(proc_frame, text="并发进程:").pack(side=LEFT, padx=5)
        
        # 动态获取核心数，设置合理选项
        cores = os.cpu_count() or 4
        # 预设常用值：2, 4, 8, 16，但不超过核心数
        # 增加 1 核心选项以便于低配或对比
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
        self.progress_label = ttk.Label(info_frame, text="系统准备就绪", foreground="#a0a0a0")
        self.progress_label.pack(side=LEFT)
        self.file_count_label = ttk.Label(info_frame, text="0 / 0", foreground=self.CYAN)
        self.file_count_label.pack(side=RIGHT)

    def create_results_area(self, parent):
        results_frame = ttk.Frame(parent)
        results_frame.pack(fill=BOTH, expand=True)
        columns = ("status", "path", "size", "error")
        self.tree = ttk.Treeview(results_frame, columns=columns, show="headings", selectmode="browse")
        self.tree.heading("status", text="状态")
        self.tree.heading("path", text="文件路径")
        self.tree.heading("size", text="大小")
        self.tree.heading("error", text="故障原因")
        self.tree.column("status", width=100, anchor="center")
        self.tree.column("path", width=550)
        self.tree.column("size", width=120, anchor="center")
        self.tree.column("error", width=250)
        
        sb = ttk.Scrollbar(results_frame, orient=VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side=LEFT, fill=BOTH, expand=True)
        sb.pack(side=RIGHT, fill=Y)

        self.tree.tag_configure("corrupted", foreground="#ff4d4d", background="#2a0000")
        self.tree.tag_configure("valid", foreground="#00ff00")

    def create_status_bar(self, parent):
        status_frame = ttk.Frame(parent, padding=(5, 15, 5, 0))
        status_frame.pack(fill=X)
        
        ttk.Label(status_frame, text="[ 实时统计 ] ", foreground="#a0a0a0").pack(side=LEFT)
        self.total_label = ttk.Label(status_frame, text="总计: 0", font=("Consolas", 11, "bold"), foreground="#ffffff")
        self.total_label.pack(side=LEFT, padx=20)
        self.valid_label = ttk.Label(status_frame, text="正常: 0", font=("Consolas", 11, "bold"), foreground="#00ff00")
        self.valid_label.pack(side=LEFT, padx=20)
        self.corrupted_label = ttk.Label(status_frame, text="损坏: 0", font=("Consolas", 11, "bold"), foreground=self.MAGENTA)
        self.corrupted_label.pack(side=LEFT, padx=20)
        self.time_label = ttk.Label(status_frame, text="耗时: 0s", font=("Consolas", 11, "bold"), foreground=self.CYAN)
        self.time_label.pack(side=LEFT, padx=20)

    # --- 逻辑处理 ---
    def browse_directory(self):
        d = filedialog.askdirectory()
        if d: self.dir_entry.delete(0, END); self.dir_entry.insert(0, d)
    def clear_directory(self): self.dir_entry.delete(0, END)
    def start_scan(self):
        directory = self.dir_entry.get().strip()
        if not directory or not os.path.isdir(directory):
            messagebox.showwarning("注意", "请选择有效的扫描目录。")
            return
        exts = [e for e, v in self.format_vars.items() if v.get()]
        if not exts:
            messagebox.showwarning("注意", "请至少选择一种协议格式。")
            return
        try: num = int(self.process_var.get())
        except: num = 4
        
        self.results = []
        self.valid_count = 0
        self.corrupted_count = 0
        self.start_time = time.time()
        for i in self.tree.get_children(): self.tree.delete(i)
        self.update_stats()
        
        self.is_scanning = True
        self.stop_event.clear()
        self.start_btn.config(state=DISABLED); self.stop_btn.config(state=NORMAL)
        threading.Thread(target=self.run_scan, args=(directory, exts, num), daemon=True).start()

    def run_scan(self, d, e, n):
        try: scan_directory(d, e, n, self.update_progress, self.add_result, self.stop_event)
        except Exception as ex: messagebox.showerror("错误", str(ex))
        self.root.after(0, self.scan_complete)

    def update_progress(self, c, t):
        self.root.after(0, lambda: [
            self.progress_var.set((c/t)*100),
            self.progress_label.config(text=f"内核分析中... {c}/{t}"),
            self.file_count_label.config(text=f"{c} / {t}")
        ])

    def add_result(self, r):
        self.root.after(0, lambda: self._add_result(r))

    def _add_result(self, r):
        self.results.append(r)
        if r["valid"]:
            self.valid_count += 1; tags = ("valid",); st = "● 正常"
        else:
            self.corrupted_count += 1; tags = ("corrupted",); st = "✖ 损坏"
        item_id = self.tree.insert("", END, values=(st, r["path"], format_size(r["size"]), r["error_type"] or ""), tags=tags)
        self.tree.see(item_id); self.update_stats()

    def update_stats(self):
        t = self.valid_count + self.corrupted_count
        elapsed = int(time.time() - self.start_time) if self.start_time > 0 else 0
        self.total_label.config(text=f"总计: {t}")
        self.valid_label.config(text=f"正常: {self.valid_count}")
        self.corrupted_label.config(text=f"损坏: {self.corrupted_count}")
        self.time_label.config(text=f"耗时: {elapsed}s")

    def scan_complete(self):
        self.is_scanning = False
        self.update_stats()
        self.progress_label.config(text="扫描完成" if not self.stop_event.is_set() else "扫描已中止")
        self.start_btn.config(state=NORMAL); self.stop_btn.config(state=DISABLED)

    def stop_scan(self): 
        self.stop_event.set()
        self.stop_btn.config(state=DISABLED)
        self.progress_label.config(text="正在切断进程...")
    def clear_results(self):
        self.results = []; self.valid_count = 0; self.corrupted_count = 0; self.start_time = 0
        for i in self.tree.get_children(): self.tree.delete(i)
        self.update_stats(); self.progress_var.set(0); self.progress_label.config(text="系统准备就绪")

    def export_dialog(self):
        if not self.results: return

        # 格式选择窗口
        choice_win = Toplevel(self.root)
        choice_win.title("导出格式")
        choice_win.geometry("320x160")
        choice_win.configure(background=self.BG_DARK)
        choice_win.resizable(False, False)
        choice_win.transient(self.root)
        choice_win.grab_set()

        # 居中
        self.root.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - 160
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - 80
        choice_win.geometry(f"+{x}+{y}")

        ttk.Label(choice_win, text="请选择导出的文件格式：", font=("Microsoft YaHei", 10), padding=20).pack()

        btn_frame = ttk.Frame(choice_win)
        btn_frame.pack(pady=10)

        def select_fmt(f):
            choice_win.destroy()
            self._save_report(f)

        ttk.Button(btn_frame, text="CSV 表格", style="Action.TButton", width=12, 
                   command=lambda: select_fmt("csv")).pack(side=LEFT, padx=10)
        ttk.Button(btn_frame, text="TXT 文本", style="Action.TButton", width=12, 
                   command=lambda: select_fmt("txt")).pack(side=LEFT, padx=10)

    def _save_report(self, fmt):
        file_types = [("CSV 表格", "*.csv")] if fmt == "csv" else [("TXT 文本", "*.txt")]
        file_path = filedialog.asksaveasfilename(
            initialfile=f"图像完整性检测报告",
            defaultextension=f".{fmt}",
            filetypes=file_types
        )

        if file_path:
            try:
                # 排序：损坏在前
                sorted_results = sorted(self.results, key=lambda x: (x["valid"], x["path"]))

                if fmt == "csv":
                    with open(file_path, "w", newline="", encoding="utf-8-sig") as f:
                        w = csv.writer(f)
                        w.writerow(["状态", "路径", "大小", "故障原因"])
                        for r in sorted_results:
                            w.writerow(["正常" if r["valid"] else "损坏", r["path"], format_size(r["size"]), r["error_type"] or ""])
                elif fmt == "txt":
                    with open(file_path, "w", encoding="utf-8") as f:
                        f.write(f"=== 图像完整性检测报告 ===\n")
                        f.write(f"生成时间: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                        f.write(f"总计: {len(self.results)} | 正常: {self.valid_count} | 损坏: {self.corrupted_count}\n")
                        f.write("="*30 + "\n\n")

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

                        f.write("--- 正常文件列表 ---\n")
                        valid = [r for r in sorted_results if r["valid"]]
                        if not valid:
                            f.write("无正常文件。\n")
                        else:
                            for r in valid:
                                f.write(f" [正常] {r['path']} ({format_size(r['size'])})\n")
                        f.write("\n")

                messagebox.showinfo("成功", f"报告已生成至:\n{file_path}")
            except Exception as e:
                messagebox.showerror("错误", f"导出失败: {str(e)}")
def main():
    root = Tk()
    try: root.tk.call("tk", "scaling", 1.25)
    except: pass
    app = ImageCheckApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()
