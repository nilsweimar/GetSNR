import tkinter as tk
from tkinter import filedialog, messagebox, ttk, simpledialog
import pydicom
import numpy as np
from PIL import Image, ImageTk, ImageDraw, ImageFont
import sys
import os
import csv
import math
import subprocess
import json
import time
from collections import deque
import datetime

PREFS_FILE = os.path.expanduser("~/.getsnr_prefs.json")
DEFAULT_PREFS = {
    "force_dark_mode": False,
    "show_toolbar": True,
    "default_tool": "rect",
    "default_colormap": "Grayscale",
    "screenshot_dest_mode": "default",
    "screenshot_custom_dir": "",
    "csv_dest_mode": "default",
    "csv_custom_dir": "",
    "pdf_include_histograms": True
}

def setup_logging():
    """Redirects all terminal output (stdout/stderr) to a macOS-native log file."""
    log_dir = os.path.expanduser("~/Library/Logs")
    try:
        os.makedirs(log_dir, exist_ok=True)
        log_file_path = os.path.join(log_dir, "GetSNR.log")
        
        # 'w' mode ensures the file is wiped clean on every startup
        log_file = open(log_file_path, "w")
        
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_file.write(f"--- GetSNR Log Session Started: {timestamp} ---\n\n")
        log_file.flush()
        
        # AutoFlush wrapper ensures crash traces are written immediately before app dies
        class AutoFlush:
            def __init__(self, file):
                self.file = file
            def write(self, data):
                self.file.write(data)
                self.file.flush()
            def flush(self):
                self.file.flush()
                
        sys.stdout = AutoFlush(log_file)
        sys.stderr = AutoFlush(log_file)
    except Exception as e:
        # Fallback if logging fails for permissions reasons
        print(f"Warning: Could not initialize macOS logging pipeline: {e}")


class DicomApp:
    def __init__(self, root):
        self.root = root
        self.root.title("GetSNR")
        
        screen_height = self.root.winfo_screenheight()
        screen_width = self.root.winfo_screenwidth()
        
        self.init_h = int(screen_height * (2 / 3))
        self.init_w = self.init_h * 2
        self.root.maxsize(screen_width, screen_height)
        
        # Load Preferences
        self.prefs = DEFAULT_PREFS.copy()
        self.load_prefs()
        
        # Session Overrides
        self.session_screenshot_override = False
        self.session_screenshot_dest_mode = "default"
        self.session_screenshot_custom_dir = ""
        
        self.session_csv_override = False
        self.session_csv_dest_mode = "default"
        self.session_csv_custom_dir = ""
        
        # NIfTI Flags
        self.nifti_mode = False
        self.nifti_volume = None
        self.nifti_spacing = (1.0, 1.0, 1.0)
        
        self.nifti_mode2 = False
        self.nifti_volume2 = None
        
        # Core Image 1 Data
        self.current_file_path = None
        self.dicom_dataset = None
        self.image_data = None
        self.base_pil_image = None
        self.tk_image = None
        self.mask_overlay = None
        
        # Split-Screen Image 2 Data
        self.split_mode = False
        self.current_file_path2 = None
        self.dicom_dataset2 = None
        self.image_data2 = None
        self.base_pil_image2 = None
        self.tk_image2 = None
        self.mask_overlay2 = None
        
        self.current_dir = ""
        self.sorted_dir_files = []
        self.current_dir2 = ""
        self.sorted_dir_files2 = []
        
        self.default_window_center = 0
        self.default_window_width = 1
        self.window_center = 0
        self.window_width = 1
        
        self.default_window_center2 = 0
        self.default_window_width2 = 1
        self.window_center2 = 0
        self.window_width2 = 1
        
        self.last_mouse_x = 0
        self.last_mouse_y = 0
        
        # Synchronized Camera Engine
        self.actual_scale = 1.0
        self.off_x = 0
        self.off_y = 0
        self.orig_w = 0
        self.orig_h = 0
        self.last_cw = 0
        self.last_ch = 0
        
        # 3D Tracking & State
        self.volume_rois = {} 
        self.current_slice_idx = 0
        self.is_navigating = False
        self.start_keyframe_idx = None
        self.end_keyframe_idx = None
        
        self.drag_start = None
        self.drag_current = None
        self.freehand_pts = []
        self.active_move_target = None 
        self.is_pulsating = False
        self.pulse_val = 0.0
        
        self.signal_rois = [] 
        self.noise_roi = None
        self.calipers = []
        self.profiles = []
        self.history_stack = [] 
        self.redo_stack = []
        self.current_results = None 
        
        self.sig_colors = [(255,0,0,255), (0,200,0,255), (255,140,0,255), (255,0,255,255), (0,200,200,255)]
        self.hex_colors = ["#FF0000", "#00C800", "#FF8C00", "#FF00FF", "#00C8C8"]
        self.ext_sig_colors = self.sig_colors + [
            (255,255,0,255), (128,0,128,255), (191,255,0,255), (255,192,203,255), (0,255,255,255),
            (165,42,42,255), (0,0,128,255), (128,0,0,255), (128,128,0,255), (255,127,80,255)
        ]
        self.ext_hex_colors = self.hex_colors + [
            "#FFFF00", "#800080", "#BFFF00", "#FFC0CB", "#00FFFF",
            "#A52A2A", "#000080", "#800000", "#808000", "#FF7F50"
        ]
        self.noise_color = (0,0,255,255)
        self.noise_hex = "#0000FF"
        
        self.show_std_var = tk.BooleanVar(value=True)
        self.show_cnr_var = tk.BooleanVar(value=True)     
        self.keep_rois_var = tk.BooleanVar(value=True) 
        self.colormap_var = tk.StringVar(value=self.prefs["default_colormap"])
        self.show_roi_numbers_var = tk.BooleanVar(value=False)
        self.extended_colors_var = tk.BooleanVar(value=False)
        self.auto_features_triggered = False
        
        self.last_os_theme_dark = False
        is_mac_dark = False
        if self.prefs["force_dark_mode"]: is_mac_dark = True
        else:
            try:
                out = subprocess.check_output('defaults read -g AppleInterfaceStyle', shell=True, stderr=subprocess.DEVNULL)
                if out.strip() == b'Dark': is_mac_dark = True
            except Exception: pass
        self.dark_mode_var = tk.BooleanVar(value=is_mac_dark)
        
        self.current_tool_var = tk.StringVar(value=self.prefs["default_tool"]) 
        self.previous_draw_tool = self.prefs["default_tool"]
        self.last_tool = self.prefs["default_tool"]
        self.current_tool_var.trace_add("write", self.on_tool_changed)
        
        self.target_mode_var = tk.StringVar(value="signal") 
        self.loupe_zoom_var = tk.DoubleVar(value=3.0)
        self.loupe_zoom_var.trace_add("write", self._sync_loupe_combo)
        self.hud_str = ""
        
        self.build_menu()
        self.build_toolbar()
        
        self.left_frame = tk.Frame(self.root, bg="black")
        self.left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.image_container = tk.Frame(self.left_frame, bg="black")
        self.image_container.pack(fill=tk.BOTH, expand=True)

        self.left_img_frame = tk.Frame(self.image_container, bg="black", highlightbackground="gray", highlightthickness=1)
        self.left_img_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.top_label = tk.Label(self.left_img_frame, text="Image 1: No file loaded", font=("Arial", 14, "bold"), bg="white", fg="black")
        self.top_label.pack(fill=tk.X, side=tk.TOP)
        self.canvas = tk.Canvas(self.left_img_frame, bg="#333333", cursor="cross")
        self.canvas.pack(fill=tk.BOTH, expand=True, side=tk.TOP)

        self.right_img_frame = tk.Frame(self.image_container, bg="black", highlightbackground="gray", highlightthickness=1)
        self.top_label2 = tk.Label(self.right_img_frame, text="Image 2: No file loaded", font=("Arial", 14, "bold"), bg="white", fg="black")
        self.top_label2.pack(fill=tk.X, side=tk.TOP)
        self.canvas2 = tk.Canvas(self.right_img_frame, bg="#333333", cursor="cross")
        self.canvas2.pack(fill=tk.BOTH, expand=True, side=tk.TOP)

        self.right_frame = tk.Frame(self.root, bg="white")
        self.right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        self.header_frame = tk.Frame(self.right_frame, bg="#F5F5F5")
        self.header_frame.pack(side=tk.TOP, fill=tk.X)
        self.task_label = tk.Label(self.header_frame, text="Welcome to GetSNR.", font=("Arial", 16, "bold"), bg="#F5F5F5", fg="black", justify="left")
        self.task_label.pack(anchor="nw", padx=20, pady=(20, 15))
        self.header_separator = tk.Frame(self.header_frame, bg="#D3D3D3", height=1)
        self.header_separator.pack(side=tk.BOTTOM, fill=tk.X)

        self.footer_frame = tk.Frame(self.right_frame, bg="#F5F5F5")
        self.footer_frame.pack(side=tk.BOTTOM, fill=tk.X)
        self.footer_separator = tk.Frame(self.footer_frame, bg="#D3D3D3", height=1)
        self.footer_separator.pack(side=tk.TOP, fill=tk.X)
        self.copyright_label = tk.Label(self.footer_frame, text="© 2026 Nils Weimar & Simon Rieger. Released under the MIT License.", font=("Arial", 11), bg="#F5F5F5", fg="#666666")
        self.copyright_label.pack(pady=10)

        self.scroll_container = tk.Frame(self.right_frame, bg="white")
        self.scroll_container.pack(fill=tk.BOTH, expand=True) 
        self.results_canvas = tk.Canvas(self.scroll_container, bg="white", highlightthickness=0)
        self.results_scrollbar = ttk.Scrollbar(self.scroll_container, orient="vertical", command=self.results_canvas.yview)
        self.results_canvas.configure(yscrollcommand=self.results_scrollbar.set)
        self.results_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.results_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.results_inner_frame = tk.Frame(self.results_canvas, bg="white", padx=20, pady=10)
        self.results_canvas_window = self.results_canvas.create_window((0, 0), window=self.results_inner_frame, anchor="nw")
        
        self.results_inner_frame.bind("<Configure>", lambda e: self.results_canvas.configure(scrollregion=self.results_canvas.bbox("all")))
        self.results_canvas.bind("<Configure>", lambda e: self.results_canvas.itemconfig(self.results_canvas_window, width=e.width))
        self.results_canvas.bind("<MouseWheel>", self._on_results_scroll)
        self.results_inner_frame.bind("<MouseWheel>", self._on_results_scroll)
        
        self.update_ui_colors()
        self.start_theme_polling()
        
        self.root.update_idletasks()
        self.top_lbl_h = self.top_label.winfo_reqheight()
        self.root.wm_aspect(2, 1, 2, 1)
        self.root.minsize(1000, 500)

        for c in [self.canvas, self.canvas2]:
            c.bind("<Configure>", self.on_resize)
            c.bind("<Motion>", self.on_mouse_move)
            c.bind("<ButtonPress-1>", self.on_mouse_press)
            c.bind("<B1-Motion>", self.on_mouse_drag)
            c.bind("<ButtonRelease-1>", self.on_mouse_release)
            c.bind("<Shift-ButtonPress-1>", self.on_magic_wand)
            c.bind("<Option-ButtonPress-1>", self.start_pan)
            c.bind("<Option-B1-Motion>", self.do_pan)
            c.bind("<Alt-ButtonPress-1>", self.start_pan)
            c.bind("<Alt-B1-Motion>", self.do_pan)
            c.bind("<MouseWheel>", self.on_zoom)
            c.bind("<Command-MouseWheel>", self.on_slice_scroll)
            c.bind("<Double-Button-1>", lambda e: self.fit_to_screen())

        self.canvas.bind("<ButtonPress-2>", self.start_windowing)
        self.canvas.bind("<B2-Motion>", self.do_windowing)
        self.canvas.bind("<ButtonPress-3>", self.start_windowing)
        self.canvas.bind("<B3-Motion>", self.do_windowing)
        
        self.canvas2.bind("<ButtonPress-2>", self.start_windowing2)
        self.canvas2.bind("<B2-Motion>", self.do_windowing2)
        self.canvas2.bind("<ButtonPress-3>", self.start_windowing2)
        self.canvas2.bind("<B3-Motion>", self.do_windowing2)

        self.root.bind("<Command-o>", lambda e: self.load_dicom_dialog())
        self.root.bind("<Command-Shift-o>", lambda e: self.load_new_data_dialog())
        self.root.bind("<Command-Shift-O>", lambda e: self.load_new_data_dialog())
        self.root.bind("<Command-Shift-r>", lambda e: self.reset_app_keep_data())
        self.root.bind("<Command-Shift-R>", lambda e: self.reset_app_keep_data())
        self.root.bind("<Command-2>", lambda e: self.load_split_screen_dialog())
        self.root.bind("<Command-s>", lambda e: self.save_data())
        self.root.bind("<Command-Shift-s>", lambda e: self.save_data_as())
        self.root.bind("<Command-p>", lambda e: self.export_pdf_report())
        self.root.bind("<Command-r>", lambda e: self.reset_rois())
        self.root.bind("<Command-z>", lambda e: self.undo_last_action())
        self.root.bind("<Command-Shift-z>", lambda e: self.redo_last_action())
        self.root.bind("<Command-Shift-Z>", lambda e: self.redo_last_action())
        self.root.bind("<Escape>", self.on_escape)
        self.root.bind("<Command-l>", lambda e: self.log_to_csv())
        self.root.bind("<Command-w>", lambda e: self.reset_windowing())
        self.root.bind("<Command-i>", lambda e: self.show_metadata())
        self.root.bind("<Command-h>", lambda e: self.show_histogram())
        self.root.bind("<Command-d>", lambda e: self.toggle_dark_mode())
        self.root.bind("<Command-m>", lambda e: self.toggle_loupe())
        self.root.bind("<Command-v>", self.toggle_move)
        self.root.bind("<space>", lambda e: self.toggle_target_mode())
        self.root.bind("<Left>", lambda e: self.navigate_file(-1))
        self.root.bind("<Right>", lambda e: self.navigate_file(1))
        
        self.root.bind("<plus>", self.increase_loupe)
        self.root.bind("<equal>", self.increase_loupe)
        self.root.bind("<KP_Add>", self.increase_loupe)
        self.root.bind("<minus>", self.decrease_loupe)
        self.root.bind("<KP_Subtract>", self.decrease_loupe)

    def load_prefs(self):
        try:
            if os.path.exists(PREFS_FILE):
                with open(PREFS_FILE, 'r') as f:
                    loaded = json.load(f)
                    self.prefs.update(loaded)
        except Exception: pass

    def save_prefs(self):
        try:
            with open(PREFS_FILE, 'w') as f:
                json.dump(self.prefs, f, indent=4)
        except Exception as e:
            print("Error saving prefs:", e)

    def build_toolbar(self):
        self.toolbar_frame = tk.Frame(self.root, bg="#F5F5F5", highlightbackground="#D3D3D3", highlightthickness=1)
        
        self.btn_undo = tk.Button(self.toolbar_frame, text="⟲ Undo", command=self.undo_last_action, state=tk.DISABLED)
        self.btn_undo.pack(side=tk.LEFT, padx=(15, 2), pady=5)
        
        self.btn_redo = tk.Button(self.toolbar_frame, text="⟳ Redo", command=self.redo_last_action, state=tk.DISABLED)
        self.btn_redo.pack(side=tk.LEFT, padx=2, pady=5)
        
        tk.Frame(self.toolbar_frame, width=1, bg="gray").pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=5)
        
        tools_def = [
            ("rect", "⬜ Rectangle"),
            ("ellipse", "◯ Ellipse"),
            ("freehand", "✎ Freehand"),
            ("caliper", "📏 Caliper"),
            ("profile", "📈 Profile Line"),
            ("move", "✥ Move"),
            ("delete", "🗑 Delete")
        ]
        for t_id, label_text in tools_def:
            rb = ttk.Radiobutton(self.toolbar_frame, text=label_text, variable=self.current_tool_var, value=t_id, style="Toolbutton")
            rb.pack(side=tk.LEFT, padx=2, pady=5)
            
        tk.Frame(self.toolbar_frame, width=1, bg="gray").pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=5)
        
        rb_loupe = ttk.Radiobutton(self.toolbar_frame, text="🔍 Loupe", variable=self.current_tool_var, value="loupe", style="Toolbutton")
        rb_loupe.pack(side=tk.LEFT, padx=2, pady=5)
        
        self.loupe_combo = ttk.Combobox(self.toolbar_frame, values=["2.0x", "2.5x", "3.0x", "3.5x", "4.0x", "4.5x", "5.0x"], state="readonly", width=5)
        self.loupe_combo.set(f"{self.loupe_zoom_var.get()}x")
        self.loupe_combo.pack(side=tk.LEFT, padx=(2, 10), pady=5)
        self.loupe_combo.bind("<<ComboboxSelected>>", self._on_loupe_combo_changed)
        
        self.btn_reset = tk.Button(self.toolbar_frame, text="↺ Reset Image Data", command=self.reset_rois, state=tk.DISABLED)
        self.btn_reset.pack(side=tk.RIGHT, padx=15, pady=5)
        
        self.update_toolbar_visibility()

    def update_toolbar_visibility(self):
        if self.prefs.get("show_toolbar", True):
            if hasattr(self, 'left_frame'):
                self.toolbar_frame.pack(side=tk.TOP, fill=tk.X, before=self.left_frame)
            else:
                self.toolbar_frame.pack(side=tk.TOP, fill=tk.X)
        else:
            self.toolbar_frame.pack_forget()

    def _sync_loupe_combo(self, *args):
        if hasattr(self, 'loupe_combo'):
            self.loupe_combo.set(f"{self.loupe_zoom_var.get()}x")

    def _on_loupe_combo_changed(self, event):
        val_str = self.loupe_combo.get()
        try:
            val = float(val_str.replace("x", ""))
            self.loupe_zoom_var.set(val)
        except ValueError: pass
        if self.current_tool_var.get() == "loupe" and hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def start_theme_polling(self):
        is_mac_dark = False
        if self.prefs.get("force_dark_mode", False):
            is_mac_dark = True
        else:
            try:
                out = subprocess.check_output('defaults read -g AppleInterfaceStyle', shell=True, stderr=subprocess.DEVNULL)
                if out.strip() == b'Dark': is_mac_dark = True
            except Exception: pass
            
        if is_mac_dark != self.last_os_theme_dark:
            self.last_os_theme_dark = is_mac_dark
            self.dark_mode_var.set(is_mac_dark)
            self.update_ui_colors()
            
        self.root.after(2000, self.start_theme_polling)

    def build_menu(self):
        self.menubar = tk.Menu(self.root)
        
        self.file_menu = tk.Menu(self.menubar, tearoff=0)
        self.file_menu.add_command(label="Open Data", accelerator="Cmd+O", command=self.load_dicom_dialog)
        self.file_menu.add_command(label="Open New Data (Hard Reset)", accelerator="Cmd+Shift+O", command=self.load_new_data_dialog)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Load Split-Screen Data", accelerator="Cmd+2", command=self.load_split_screen_dialog, state=tk.DISABLED)
        self.file_menu.add_command(label="Close Split-Screen", command=self.close_split_screen, state=tk.DISABLED)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="View DICOM Metadata", accelerator="Cmd+I", command=self.show_metadata, state=tk.DISABLED)
        self.file_menu.add_command(label="Export Data / Anonymize", command=self.anonymize_dicom, state=tk.DISABLED)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Select New ROI", accelerator="Cmd+R", command=self.reset_rois, state=tk.DISABLED)
        self.file_menu.add_command(label="Reset All Overlays (Keep Data)", accelerator="Cmd+Shift+R", command=self.reset_app_keep_data, state=tk.DISABLED)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Save Screenshot", accelerator="Cmd+S", command=self.save_data, state=tk.DISABLED)
        self.file_menu.add_command(label="Save Screenshot As...", accelerator="Cmd+Shift+S", command=self.save_data_as, state=tk.DISABLED)
        self.file_menu.add_command(label="Export Full PDF Report", accelerator="Cmd+P", command=self.export_pdf_report, state=tk.DISABLED)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Log Results to CSV", accelerator="Cmd+L", command=self.log_to_csv, state=tk.DISABLED)
        self.menubar.add_cascade(label="File", menu=self.file_menu)
        
        self.edit_menu = tk.Menu(self.menubar, tearoff=0)
        self.edit_menu.add_command(label="Undo Last Draw", accelerator="Cmd+Z", command=self.undo_last_action, state=tk.DISABLED)
        self.edit_menu.add_command(label="Redo Last Draw", accelerator="Cmd+Shift+Z", command=self.redo_last_action, state=tk.DISABLED)
        self.menubar.add_cascade(label="Edit", menu=self.edit_menu)

        self.view_menu = tk.Menu(self.menubar, tearoff=0)
        self.view_menu.add_command(label="Reset Contrast/Brightness", accelerator="Cmd+W", command=self.reset_windowing)
        cmap_menu = tk.Menu(self.view_menu, tearoff=0)
        for cmap in ["Grayscale", "Heatmap (Rainbow)", "Hot Metal", "Bone", "Jet"]:
            cmap_menu.add_radiobutton(label=cmap, variable=self.colormap_var, value=cmap, command=self.apply_windowing)
        self.view_menu.add_cascade(label="Medical Colormaps (LUT)", menu=cmap_menu)
        self.view_menu.add_separator()
        self.view_menu.add_checkbutton(label="Reading Room Dark Mode", accelerator="Cmd+D", variable=self.dark_mode_var, command=self.toggle_dark_mode)
        self.view_menu.add_separator()
        self.view_menu.add_command(label="Show ROI Histograms", accelerator="Cmd+H", command=self.show_histogram, state=tk.DISABLED)
        self.menubar.add_cascade(label="View", menu=self.view_menu)
        
        self.tools_menu = tk.Menu(self.menubar, tearoff=0)
        self.tools_menu.add_radiobutton(label="Target: Signal", variable=self.target_mode_var, value="signal", command=self.update_task_text)
        self.tools_menu.add_radiobutton(label="Target: Noise (Press Space)", variable=self.target_mode_var, value="noise", command=self.update_task_text)
        self.tools_menu.add_separator()
        self.tools_menu.add_radiobutton(label="Tool: Move ROI/Line", accelerator="Cmd+V", variable=self.current_tool_var, value="move")
        self.tools_menu.add_radiobutton(label="Tool: Delete Target", variable=self.current_tool_var, value="delete")
        self.tools_menu.add_radiobutton(label="Tool: Rectangle", variable=self.current_tool_var, value="rect")
        self.tools_menu.add_radiobutton(label="Tool: Ellipse", variable=self.current_tool_var, value="ellipse")
        self.tools_menu.add_radiobutton(label="Tool: Freehand", variable=self.current_tool_var, value="freehand")
        self.tools_menu.add_radiobutton(label="Tool: Caliper (Measure)", variable=self.current_tool_var, value="caliper")
        self.tools_menu.add_radiobutton(label="Tool: Profile Line (Graph)", variable=self.current_tool_var, value="profile")
        self.tools_menu.add_radiobutton(label="Tool: Magnifying Glass (Loupe)", accelerator="Cmd+M", variable=self.current_tool_var, value="loupe")
        
        mag_menu = tk.Menu(self.tools_menu, tearoff=0)
        for val in [2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0]:
            mag_menu.add_radiobutton(label=f"{val}x", variable=self.loupe_zoom_var, value=val)
        self.tools_menu.add_cascade(label="Loupe Magnification Level", menu=mag_menu)
        
        self.tools_menu.add_separator()
        self.tools_menu.add_command(label="3D: Set Start Slice", command=self.set_start_keyframe, state=tk.DISABLED)
        self.tools_menu.add_command(label="3D: Set End Slice", command=self.set_end_keyframe, state=tk.DISABLED)
        self.tools_menu.add_command(label="3D: Interpolate ROIs", command=self.interpolate_3d_rois, state=tk.DISABLED)
        self.tools_menu.add_separator()
        self.tools_menu.add_command(label="Batch Analyze 3D Volume", command=self.batch_analyze_volume, state=tk.DISABLED)
        self.menubar.add_cascade(label="Tools", menu=self.tools_menu)

        self.settings_menu = tk.Menu(self.menubar, tearoff=0)
        self.settings_menu.add_command(label="Preferences...", command=self.show_preferences)
        self.settings_menu.add_separator()
        self.settings_menu.add_checkbutton(label="Show standard deviation", variable=self.show_std_var, command=self.calculate_and_show_results)
        self.settings_menu.add_checkbutton(label="Show CNR Analysis", variable=self.show_cnr_var, command=self.calculate_and_show_results)
        self.settings_menu.add_separator()
        self.settings_menu.add_checkbutton(label="Show ROI Numbers", variable=self.show_roi_numbers_var, command=self._on_settings_change)
        self.settings_menu.add_checkbutton(label="Extended Color Palette", variable=self.extended_colors_var, command=self._on_settings_change)
        self.settings_menu.add_separator()
        self.settings_menu.add_checkbutton(label="Keep ROIs on Next Image", variable=self.keep_rois_var)
        self.menubar.add_cascade(label="Settings", menu=self.settings_menu)
        
        self.help_menu = tk.Menu(self.menubar, tearoff=0)
        self.help_menu.add_command(label="GetSNR Help (Cheat Sheet)", command=self.show_help)
        self.help_menu.add_command(label="Export Project History PDF", command=self.export_history_pdf)
        self.menubar.add_cascade(label="Help", menu=self.help_menu)
        
        self.root.config(menu=self.menubar)
        self.root.createcommand('tkAboutDialog', self.show_about)
        self.root.createcommand('tk::mac::ShowHelp', self.show_help)

    def show_preferences(self):
        win = tk.Toplevel(self.root)
        win.title("GetSNR Preferences")
        win.geometry("650x700")
        win.minsize(500, 500)
        
        bg_col = "#1E1E1E" if self.dark_mode_var.get() else "white"
        fg_col = "white" if self.dark_mode_var.get() else "black"
        win.configure(bg=bg_col)
        
        # Scrollable structure
        canvas = tk.Canvas(win, bg=bg_col, highlightthickness=0)
        scrollbar = ttk.Scrollbar(win, orient="vertical", command=canvas.yview)
        main_frame = tk.Frame(canvas, bg=bg_col, padx=20, pady=20)
        
        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        canvas_window = canvas.create_window((0, 0), window=main_frame, anchor="nw")
        
        def _on_frame_configure(event):
            canvas.configure(scrollregion=canvas.bbox("all"))
        def _on_canvas_configure(event):
            canvas.itemconfig(canvas_window, width=event.width)
            
        main_frame.bind("<Configure>", _on_frame_configure)
        canvas.bind("<Configure>", _on_canvas_configure)
        
        # Variables
        force_dark_var = tk.BooleanVar(value=self.prefs["force_dark_mode"])
        show_toolbar_var = tk.BooleanVar(value=self.prefs.get("show_toolbar", True))
        pdf_histograms_var = tk.BooleanVar(value=self.prefs.get("pdf_include_histograms", True))
        def_tool_var = tk.StringVar(value=self.prefs["default_tool"])
        def_cmap_var = tk.StringVar(value=self.prefs["default_colormap"])
        
        ss_mode_var = tk.StringVar(value=self.prefs["screenshot_dest_mode"])
        ss_custom_var = tk.StringVar(value=self.prefs["screenshot_custom_dir"])
        ss_sess_over_var = tk.BooleanVar(value=self.session_screenshot_override)
        ss_sess_mode_var = tk.StringVar(value=self.session_screenshot_dest_mode)
        ss_sess_custom_var = tk.StringVar(value=self.session_screenshot_custom_dir)

        csv_mode_var = tk.StringVar(value=self.prefs["csv_dest_mode"])
        csv_custom_var = tk.StringVar(value=self.prefs["csv_custom_dir"])
        csv_sess_over_var = tk.BooleanVar(value=self.session_csv_override)
        csv_sess_mode_var = tk.StringVar(value=self.session_csv_dest_mode)
        csv_sess_custom_var = tk.StringVar(value=self.session_csv_custom_dir)

        def browse_dir(var):
            d = filedialog.askdirectory(title="Select Folder")
            if d: var.set(d)

        def make_section(parent, text):
            lbl = tk.Label(parent, text=text, font=("Arial", 14, "bold"), bg=bg_col, fg=fg_col, anchor="w")
            lbl.pack(fill=tk.X, pady=(15, 5))
            f = tk.Frame(parent, bg=bg_col)
            f.pack(fill=tk.X, padx=10)
            return f

        # --- General Section ---
        gen_f = make_section(main_frame, "General Settings")
        tk.Checkbutton(gen_f, text="Force Dark Mode (Overrides Mac OS setting)", variable=force_dark_var, bg=bg_col, fg=fg_col).pack(anchor="w", pady=2)
        tk.Checkbutton(gen_f, text="Show Quick-Access Toolbar", variable=show_toolbar_var, bg=bg_col, fg=fg_col).pack(anchor="w", pady=2)
        
        t_f = tk.Frame(gen_f, bg=bg_col)
        t_f.pack(fill=tk.X, pady=5)
        tk.Label(t_f, text="Default Tool on Startup:", bg=bg_col, fg=fg_col).pack(side=tk.LEFT)
        tools = {"rect": "Rectangle", "ellipse": "Ellipse", "freehand": "Freehand"}
        tool_menu = ttk.Combobox(t_f, textvariable=def_tool_var, values=list(tools.keys()), state="readonly", width=15)
        tool_menu.pack(side=tk.LEFT, padx=10)
        
        c_f = tk.Frame(gen_f, bg=bg_col)
        c_f.pack(fill=tk.X, pady=5)
        tk.Label(c_f, text="Default Colormap:", bg=bg_col, fg=fg_col).pack(side=tk.LEFT)
        cmap_menu = ttk.Combobox(c_f, textvariable=def_cmap_var, values=["Grayscale", "Heatmap (Rainbow)", "Hot Metal", "Bone", "Jet"], state="readonly", width=15)
        cmap_menu.pack(side=tk.LEFT, padx=10)
        
        # --- Output Section ---
        out_f = make_section(main_frame, "Export Settings")
        tk.Checkbutton(out_f, text="Include Histograms in Exported PDF Report", variable=pdf_histograms_var, bg=bg_col, fg=fg_col).pack(anchor="w", pady=2)

        def build_path_section(parent_frame, title, global_mode_var, global_custom_var, sess_over_var, sess_mode_var, sess_custom_var):
            sf = make_section(parent_frame, title)
            
            tk.Radiobutton(sf, text="Default (Save in same folder as data)", variable=global_mode_var, value="default", bg=bg_col, fg=fg_col).pack(anchor="w")
            g_cust_f = tk.Frame(sf, bg=bg_col)
            g_cust_f.pack(fill=tk.X, anchor="w", pady=2)
            tk.Radiobutton(g_cust_f, text="Custom Folder:", variable=global_mode_var, value="custom", bg=bg_col, fg=fg_col).pack(side=tk.LEFT)
            g_ent = tk.Entry(g_cust_f, textvariable=global_custom_var, width=30)
            g_ent.pack(side=tk.LEFT, padx=5)
            g_btn = tk.Button(g_cust_f, text="Browse", command=lambda: browse_dir(global_custom_var))
            g_btn.pack(side=tk.LEFT)

            sess_f = tk.Frame(sf, bg=bg_col, highlightbackground="gray", highlightthickness=1, padx=10, pady=5)
            sess_f.pack(fill=tk.X, pady=10)
            tk.Checkbutton(sess_f, text="Override For This Session Only (Resets on close)", variable=sess_over_var, bg=bg_col, fg="orange").pack(anchor="w")
            
            s_rad1 = tk.Radiobutton(sess_f, text="Default (Same folder as data)", variable=sess_mode_var, value="default", bg=bg_col, fg=fg_col)
            s_rad1.pack(anchor="w", padx=20)
            s_cust_f = tk.Frame(sess_f, bg=bg_col)
            s_cust_f.pack(fill=tk.X, anchor="w", padx=20, pady=2)
            s_rad2 = tk.Radiobutton(s_cust_f, text="Custom Folder:", variable=sess_mode_var, value="custom", bg=bg_col, fg=fg_col)
            s_rad2.pack(side=tk.LEFT)
            s_ent = tk.Entry(s_cust_f, textvariable=sess_custom_var, width=25)
            s_ent.pack(side=tk.LEFT, padx=5)
            s_btn = tk.Button(s_cust_f, text="Browse", command=lambda: browse_dir(sess_custom_var))
            s_btn.pack(side=tk.LEFT)
            
            def update(*args):
                g_st = tk.NORMAL if global_mode_var.get() == "custom" else tk.DISABLED
                g_ent.config(state=g_st)
                g_btn.config(state=g_st)
                
                over_st = tk.NORMAL if sess_over_var.get() else tk.DISABLED
                s_rad1.config(state=over_st)
                s_rad2.config(state=over_st)
                
                s_st = tk.NORMAL if sess_over_var.get() and sess_mode_var.get() == "custom" else tk.DISABLED
                s_ent.config(state=s_st)
                s_btn.config(state=s_st)
                
            global_mode_var.trace_add("write", update)
            sess_over_var.trace_add("write", update)
            sess_mode_var.trace_add("write", update)
            update()

        build_path_section(main_frame, "Screenshot Output Directory", ss_mode_var, ss_custom_var, ss_sess_over_var, ss_sess_mode_var, ss_sess_custom_var)
        build_path_section(main_frame, "CSV Log Output Directory", csv_mode_var, csv_custom_var, csv_sess_over_var, csv_sess_mode_var, csv_sess_custom_var)

        def apply_settings():
            self.prefs["force_dark_mode"] = force_dark_var.get()
            self.prefs["show_toolbar"] = show_toolbar_var.get()
            self.prefs["pdf_include_histograms"] = pdf_histograms_var.get()
            self.prefs["default_tool"] = def_tool_var.get()
            self.prefs["default_colormap"] = def_cmap_var.get()
            
            self.prefs["screenshot_dest_mode"] = ss_mode_var.get()
            self.prefs["screenshot_custom_dir"] = ss_custom_var.get()
            self.prefs["csv_dest_mode"] = csv_mode_var.get()
            self.prefs["csv_custom_dir"] = csv_custom_var.get()
            
            self.session_screenshot_override = ss_sess_over_var.get()
            self.session_screenshot_dest_mode = ss_sess_mode_var.get()
            self.session_screenshot_custom_dir = ss_sess_custom_var.get()
            
            self.session_csv_override = csv_sess_over_var.get()
            self.session_csv_dest_mode = csv_sess_mode_var.get()
            self.session_csv_custom_dir = csv_sess_custom_var.get()
            
            self.current_tool_var.set(self.prefs["default_tool"])
            self.colormap_var.set(self.prefs["default_colormap"])
            self.apply_windowing()
            self.update_toolbar_visibility()
            self.save_prefs()
            self.start_theme_polling()

        def save_and_close():
            apply_settings()
            win.destroy()
            
        def reset_defaults():
            force_dark_var.set(False)
            show_toolbar_var.set(True)
            pdf_histograms_var.set(True)
            def_tool_var.set("rect")
            def_cmap_var.set("Grayscale")
            ss_mode_var.set("default")
            ss_custom_var.set("")
            ss_sess_over_var.set(False)
            ss_sess_mode_var.set("default")
            ss_sess_custom_var.set("")
            
            csv_mode_var.set("default")
            csv_custom_var.set("")
            csv_sess_over_var.set(False)
            csv_sess_mode_var.set("default")
            csv_sess_custom_var.set("")

        btn_f = tk.Frame(win, bg=bg_col)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM, pady=20, padx=20)
        
        tk.Button(btn_f, text="Reset Defaults", fg="red", command=reset_defaults).pack(side=tk.LEFT)
        tk.Button(btn_f, text="Save & Close", font=("Arial", 12, "bold"), command=save_and_close).pack(side=tk.RIGHT, padx=5)
        tk.Button(btn_f, text="Apply", command=apply_settings).pack(side=tk.RIGHT, padx=5)
        tk.Button(btn_f, text="Cancel", command=win.destroy).pack(side=tk.RIGHT, padx=5)

        # MouseWheel binding specifically for the preferences window
        def _on_prefs_scroll(event):
            scroll_amt = -1 if event.delta > 0 else 1
            canvas.yview_scroll(scroll_amt, "units")

        def _bind_mousewheel(w):
            # Skip Entry and Combobox as they might need their own focus handling
            if not isinstance(w, (tk.Entry, ttk.Combobox, ttk.Scrollbar)):
                w.bind("<MouseWheel>", _on_prefs_scroll)
                w.bind("<Button-4>", lambda e: canvas.yview_scroll(-1, "units")) # Linux scroll up
                w.bind("<Button-5>", lambda e: canvas.yview_scroll(1, "units"))  # Linux scroll down
            for child in w.winfo_children():
                _bind_mousewheel(child)
                
        # Attach the recursively generated events
        _bind_mousewheel(win)

    def _get_target_dir(self, pref_type="screenshot"):
        base_dir = os.path.dirname(self.current_file_path) if self.current_file_path else ""
        override = self.session_screenshot_override if pref_type == "screenshot" else self.session_csv_override
        mode = self.session_screenshot_dest_mode if pref_type == "screenshot" else self.session_csv_dest_mode
        custom_dir = self.session_screenshot_custom_dir if pref_type == "screenshot" else self.session_csv_custom_dir
        
        if not override:
            mode = self.prefs[f"{pref_type}_dest_mode"]
            custom_dir = self.prefs[f"{pref_type}_custom_dir"]
            
        if mode == "custom" and custom_dir and os.path.isdir(custom_dir):
            return custom_dir
        return base_dir

    def update_undo_redo_state(self):
        u_state = tk.NORMAL if self.history_stack else tk.DISABLED
        r_state = tk.NORMAL if self.redo_stack else tk.DISABLED
        
        if hasattr(self, 'edit_menu'):
            self.edit_menu.entryconfig("Undo Last Draw", state=u_state)
            self.edit_menu.entryconfig("Redo Last Draw", state=r_state)
            
        if hasattr(self, 'btn_undo'):
            self.btn_undo.config(state=u_state)
            self.btn_redo.config(state=r_state)

    def _on_settings_change(self, *args):
        if self.image_data is not None:
            self.rebuild_mask_overlay()
            self.calculate_and_show_results()
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def on_tool_changed(self, var, indx, mode):
        new_tool = self.current_tool_var.get()
        
        if new_tool == "delete":
            self.canvas.config(cursor="target")
            self.canvas2.config(cursor="target")
        else:
            self.canvas.config(cursor="cross")
            self.canvas2.config(cursor="cross")
            
        if self.last_tool not in ["loupe", "move", "delete"]:
            self.previous_draw_tool = self.last_tool
        self.last_tool = new_tool
        
        if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def toggle_loupe(self):
        if self.current_tool_var.get() == "loupe": self.current_tool_var.set(self.previous_draw_tool)
        else: self.current_tool_var.set("loupe")

    def toggle_move(self, event=None):
        if self.current_tool_var.get() == "move": self.current_tool_var.set(self.previous_draw_tool)
        else: self.current_tool_var.set("move")

    def increase_loupe(self, event):
        if self.current_tool_var.get() == "loupe":
            v = self.loupe_zoom_var.get()
            if v < 5.0:
                self.loupe_zoom_var.set(round(v + 0.5, 1))
                if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
                    self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def decrease_loupe(self, event):
        if self.current_tool_var.get() == "loupe":
            v = self.loupe_zoom_var.get()
            if v > 2.0:
                self.loupe_zoom_var.set(round(v - 0.5, 1))
                if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
                    self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def _pulse_tick(self):
        if not self.is_pulsating: return
        self.pulse_val += 0.2
        self.rebuild_mask_overlay()
        if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
        self.root.after(50, self._pulse_tick)

    def toggle_dark_mode(self):
        self.dark_mode_var.set(not self.dark_mode_var.get())
        self.update_ui_colors()

    def update_ui_colors(self):
        is_dark = self.dark_mode_var.get()
        
        vp_bg = "#1E1E1E" if is_dark else "white"        
        hf_bg = "#252525" if is_dark else "#F5F5F5"      
        sep_col = "#3C3C3C" if is_dark else "#D3D3D3"    
        fg_col = "white" if is_dark else "black"         
        cpy_col = "#888888" if is_dark else "#666666"    
        
        if hasattr(self, 'toolbar_frame'):
            self.toolbar_frame.config(bg=hf_bg, highlightbackground=sep_col)
            for child in self.toolbar_frame.winfo_children():
                if isinstance(child, tk.Frame):
                    child.config(bg=sep_col)
        
        self.right_frame.config(bg=vp_bg)
        self.scroll_container.config(bg=vp_bg)
        self.results_canvas.config(bg=vp_bg)
        self.results_inner_frame.config(bg=vp_bg)
        
        self.header_frame.config(bg=hf_bg)
        self.task_label.config(bg=hf_bg, fg=fg_col)
        self.header_separator.config(bg=sep_col)
        
        self.footer_frame.config(bg=hf_bg)
        self.copyright_label.config(bg=hf_bg, fg=cpy_col)
        self.footer_separator.config(bg=sep_col)
        
        self.top_label.config(bg=vp_bg, fg=fg_col)
        self.top_label2.config(bg=vp_bg, fg=fg_col)
        self._build_text_output()

    def show_about(self):
        messagebox.showinfo("About GetSNR", "GetSNR\nVersion 1.7.6.7\n\nAuthors: Nils Weimar & Simon Rieger\nContains AI generated code\n\n© 2026 Nils Weimar & Simon Rieger\nReleased under the MIT License")

    def export_help_pdf(self):
        target_path = filedialog.asksaveasfilename(
            initialfile="GetSNR_Cheat_Sheet.pdf",
            title="Save Help Cheat Sheet", defaultextension=".pdf", filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if not target_path: return
        try:
            try: font_title = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 36)
            except: font_title = ImageFont.load_default()
            try: font_head = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 26)
            except: font_head = ImageFont.load_default()
            try: font_body = ImageFont.truetype("/Library/Fonts/Arial.ttf", 22)
            except: font_body = ImageFont.load_default()

            def draw_footer(draw_obj, page_num, total_pages):
                draw_obj.line([100, 1450, 1100, 1450], fill="lightgray", width=2)
                draw_obj.text((100, 1480), f"Page {page_num} of {total_pages}", fill="gray", font=font_body)
                bbox = draw_obj.textbbox((0, 0), "© 2026 Nils Weimar & Simon Rieger. Released under the MIT License.", font=font_body)
                tw = bbox[2] - bbox[0]
                draw_obj.text((1100 - tw, 1480), "© 2026 Nils Weimar & Simon Rieger. Released under the MIT License.", fill="gray", font=font_body)

            # --- Page 1 Rendering ---
            page1 = Image.new("RGB", (1200, 1600), "white")
            draw1 = ImageDraw.Draw(page1)
            draw1.text((100, 100), "GetSNR 1.7.6.7 - Universal Quick Start", fill="black", font=font_title)
            draw1.line([100, 150, 1100, 150], fill="gray", width=2)
            
            p1_text = (
                "GetSNR is designed for maximum speed in analyzing Signal-to-Noise Ratio (SNR)\n"
                "and Contrast-to-Noise Ratio (CNR) in DICOM & NIfTI imagery.\n\n"
                "1. LOADING DATA:\n"
                "   • Cmd + O : Open Data (Loads a primary DICOM or NIfTI file).\n"
                "   • Cmd + 2 : Load Split-Screen Data. Loads a secondary image side-by-side.\n"
                "               Both images instantly synchronize pan, zoom, and ROI coordinates.\n"
                "   • Cmd + Shift + O : Hard Data Reset. Completely flushes existing memory and starts fresh.\n\n"
                "2. MOUSE & CAMERA CONTROLS:\n"
                "   • Scroll Wheel : Zoom In / Out cleanly centered at your mouse cursor.\n"
                "   • Option + Drag : Pan effortlessly around zoomed images.\n"
                "   • Double Click : Snap image perfectly back to screen center.\n"
                "   • Right-Click & Drag : Adjust contrast (Window Width) and brightness (Window Center).\n\n"
                "3. DRAWING REGIONS OF INTEREST (ROI):\n"
                "   • Select a tool from the top Menu/Toolbar (Rectangle, Ellipse, Freehand).\n"
                "   • Click & Drag on the image to draw your shape.\n"
                "   • Spacebar : Quick-switches between drawing Signal ROIs and your singular Noise ROI.\n"
                "   • Shift + Click : 'Magic Wand' tool. Auto-selects connected pixels of similar intensity."
            )
            draw1.text((100, 200), "THE BASICS:", fill="#00008B", font=font_head)
            draw1.text((120, 250), p1_text, fill="black", font=font_body, spacing=10)
            
            p1_short_text = (
                "• Cmd + R : Soft Reset (Clears drawn ROIs but keeps data).\n"
                "• Cmd + Shift + R : Hard Overlays Reset (Clears ROIs, Tools, Tracking, etc. Keeps data).\n"
                "• Cmd + Z : Undo Last Draw.\n"
                "• Cmd + Shift + Z : Redo Last Draw.\n"
                "• Esc : Cancel Active Draw mid-action (or Cancel Move)."
            )
            draw1.text((100, 850), "ESSENTIAL SHORTCUTS:", fill="#00008B", font=font_head)
            draw1.text((120, 900), p1_short_text, fill="black", font=font_body, spacing=10)
            draw_footer(draw1, 1, 3)

            # --- Page 2 Rendering ---
            page2 = Image.new("RGB", (1200, 1600), "white")
            draw2 = ImageDraw.Draw(page2)
            draw2.text((100, 100), "GetSNR 1.7.6.7 - Advanced Measurement Tools", fill="black", font=font_title)
            draw2.line([100, 150, 1100, 150], fill="gray", width=2)
            
            p2_text = (
                "1. MEASUREMENT & PROFILING:\n"
                "   • Caliper Tool : Click and drag to measure physical distance (in mm) directly mapped to\n"
                "                    the DICOM/NIfTI Pixel Spacing tags.\n"
                "   • Profile Line Tool : Draw a line across anatomy. A window instantly pops up showing\n"
                "                         a graph of the pixel intensity distribution exactly along that path.\n"
                "                         (In split-screen, it graphs both images simultaneously!).\n\n"
                "2. MANIPULATION (MOVE MODE):\n"
                "   • Shortcut: Cmd + V (Or via Top Toolbar)\n"
                "   • Allows you to grab existing ROIs, Calipers, or Profile Lines and slide them around\n"
                "     the anatomy. Measurements and SNR calculations auto-update live as you drag.\n"
                "   • While actively dragging, press Esc to snap the ROI back to its original location.\n\n"
                "3. DELETION (TRASH MODE):\n"
                "   • Select 'Delete Target' via Toolbar. Your cursor will change.\n"
                "   • Click any ROI, caliper, or profile line to instantly remove it.\n\n"
                "4. HISTOGRAMS & DATA EXPORT:\n"
                "   • Cmd + H : Generates high-fidelity visual Histograms of every active ROI dataset.\n"
                "   • Cmd + P : Exports a massive, multi-page professional PDF Report (including Histograms).\n"
                "   • Cmd + L : Quietly logs all active math and values into an appendable 'snr_log.csv'."
            )
            draw2.text((100, 200), "ANALYSIS SUITE:", fill="#00008B", font=font_head)
            draw2.text((120, 250), p2_text, fill="black", font=font_body, spacing=10)
            draw_footer(draw2, 2, 3)

            # --- Page 3 Rendering ---
            page3 = Image.new("RGB", (1200, 1600), "white")
            draw3 = ImageDraw.Draw(page3)
            draw3.text((100, 100), "GetSNR 1.7.6.7 - 3D Volume Tracking & Export", fill="black", font=font_title)
            draw3.line([100, 150, 1100, 150], fill="gray", width=2)
            
            p3_text = (
                "GetSNR fundamentally understands standard DICOM folder structures AND native NIfTI volumes,\n"
                "automatically building a cohesive 3D Z-Axis stack.\n\n"
                "1. NAVIGATION:\n"
                "   • Cmd + Scroll Wheel (or Left/Right Arrows) : Scrub through slices seamlessly.\n"
                "   • 'Keep ROIs on Next Image' Setting (Default: ON) actively pins your masks to the screen.\n\n"
                "2. 3D KEYFRAME INTERPOLATION (Morphing ROIs):\n"
                "   This feature allows you to seamlessly morph bounding boxes across a 3D patient volume.\n"
                "     Step A: Scroll to your designated starting slice.\n"
                "     Step B: Draw your Signal/Noise ROIs on the anatomy.\n"
                "     Step C: Go to Tools -> '3D: Set Start Slice'.\n"
                "     Step D: Scroll to your designated ending slice.\n"
                "     Step E: Switch to Move Mode (Cmd + V) and reposition/re-draw ROIs to match anatomy.\n"
                "     Step F: Go to Tools -> '3D: Set End Slice'.\n"
                "     Step G: Click Tools -> '3D: Interpolate ROIs'.\n"
                "             The engine instantly backfills all slices in between, calculating shift AND scaling.\n\n"
                "3. DUAL-3D BATCH ANALYSIS:\n"
                "   Clicking 'Batch Analyze 3D Volume' triggers a scanner across the entire stack.\n"
                "   It pulls exact slice data using your 3D interpolated ROI path, calculating SNR slice-by-slice\n"
                "   and exporting a completely compiled volume log CSV, along with visual trend graphs.\n\n"
                "4. BULK DATA EXPORT (DICOM & NIfTI):\n"
                "   The 'Export Data / Anonymize' tool under the File menu allows you to bulk strip metadata\n"
                "   and natively convert entire directories of slices into fully compliant 3D NIfTI volumes!"
            )
            draw3.text((100, 200), "Z-AXIS WORKFLOWS:", fill="#00008B", font=font_head)
            draw3.text((120, 250), p3_text, fill="black", font=font_body, spacing=10)
            draw_footer(draw3, 3, 3)

            page1.save(target_path, "PDF", resolution=150.0, save_all=True, append_images=[page2, page3])
            messagebox.showinfo("Success", f"Comprehensive Cheat Sheet PDF safely exported to:\n{target_path}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save PDF:\n{e}")

    def export_history_pdf(self):
        target_path = filedialog.asksaveasfilename(
            initialfile="GetSNR_Project_History.pdf",
            title="Save Project History PDF", defaultextension=".pdf", filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if not target_path: return
        try:
            try: font_title = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 36)
            except: font_title = ImageFont.load_default()
            try: font_head = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 26)
            except: font_head = ImageFont.load_default()
            try: font_body = ImageFont.truetype("/Library/Fonts/Arial.ttf", 22)
            except: font_body = ImageFont.load_default()

            page = Image.new("RGB", (1200, 1600), "white")
            draw = ImageDraw.Draw(page)
            draw.text((100, 100), "GetSNR: Project History", fill="black", font=font_title)
            draw.line([100, 150, 1100, 150], fill="gray", width=2)
            
            p_text = (
                "Version 1.7.6.7 - first release edition"
            )
            draw.text((100, 200), "THE EVOLUTION OF AN APP:", fill="#00008B", font=font_head)
            draw.text((120, 250), p_text, fill="black", font=font_body, spacing=10)
            
            draw.line([100, 1450, 1100, 1450], fill="lightgray", width=2)
            bbox = draw.textbbox((0, 0), "© 2026 Nils Weimar & Simon Rieger. Released under the MIT License.", font=font_body)
            tw = bbox[2] - bbox[0]
            draw.text((1100 - tw, 1480), "© 2026 Nils Weimar & Simon Rieger. Released under the MIT License.", fill="gray", font=font_body)

            page.save(target_path, "PDF", resolution=150.0)
            messagebox.showinfo("Success", f"Project History PDF safely exported to:\n{target_path}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save PDF:\n{e}")

    def show_help(self):
        help_win = tk.Toplevel(self.root)
        help_win.title("GetSNR Help")
        help_win.geometry("850x650")
        
        bg_color = "#1E1E1E" if self.dark_mode_var.get() else "white"
        fg_color = "white" if self.dark_mode_var.get() else "black"
        help_win.configure(bg=bg_color)
        
        top_bar = tk.Frame(help_win, bg=bg_color)
        top_bar.pack(fill=tk.X, padx=20, pady=(20, 10))
        
        title_lbl = tk.Label(top_bar, text="GetSNR Version 1.7.6.7 - Advanced Medical Imaging Utility", font=("Arial", 16, "bold"), bg=bg_color, fg=fg_color)
        title_lbl.pack(side=tk.LEFT)
        
        pdf_btn = tk.Button(top_bar, text="Save as PDF Cheat Sheet", command=self.export_help_pdf)
        pdf_btn.pack(side=tk.RIGHT)
        
        help_text = (
            "CONTROLS:\n"
            "• Click & Drag : Draw ROIs, Calipers, Loupe, or Profile Lines\n"
            "• Spacebar : Switch between drawing Signal and drawing Noise\n"
            "• Scroll Wheel : Zoom In/Out (Synchronized across screens)\n"
            "• Cmd + Scroll : Scrub through 3D Volume Slices (Synchronized)\n"
            "• Option + Drag : Pan around image\n"
            "• Double Click : Reset zoom and center image\n"
            "• Right-Click & Drag : Adjust Contrast and Brightness independently\n"
            "• Shift + Click : Magic Wand Auto-Threshold Selection\n\n"
            "SHORTCUTS:\n"
            "• Cmd + V : Toggle Move ROI / Line Tool\n"
            "• Cmd + Z : Undo Last Draw\n"
            "• Cmd + Shift + Z : Redo Last Draw\n"
            "• Cmd + Shift + R : Hard Reset Overlays (Keeps your Data loaded)\n"
            "• Esc : Cancel Active Draw (or Cancel Move Target)\n"
            "• Cmd + O : Open Data\n"
            "• Cmd + 2 : Load Split-Screen Data\n"
            "• Cmd + S / Cmd + P : Save Screenshot / Export Full PDF Report\n"
            "• Cmd + L : Log Results to CSV\n"
            "• Cmd + W : Reset Contrast / Brightness\n"
            "• Cmd + M : Toggle Magnifying Glass (Loupe)\n"
            "• Cmd + D : Toggle Reading Room Dark Mode\n\n"
            "*** For a comprehensive guide and detailed tool instructions, ***\n"
            "*** click 'Save as PDF Cheat Sheet' above! ***\n"
        )
        
        content_lbl = tk.Label(help_win, text=help_text, font=("Arial", 14), justify="left", bg=bg_color, fg=fg_color)
        content_lbl.pack(padx=30, anchor="w")
        
        close_btn = tk.Button(help_win, text="Close", command=help_win.destroy)
        close_btn.pack(pady=20)

    def _on_results_scroll(self, event):
        scroll_amt = -1 if event.delta > 0 else 1
        self.results_canvas.yview_scroll(scroll_amt, "units")

    def on_mouse_move(self, event):
        if self.image_data is None: return
        
        ix = int((event.x - self.off_x) / self.actual_scale)
        iy = int((event.y - self.off_y) / self.actual_scale)
        
        if 0 <= ix < self.orig_w and 0 <= iy < self.orig_h:
            val1 = self.image_data[iy, ix]
            if self.split_mode and self.image_data2 is not None:
                val2 = self.image_data2[iy, ix]
                self.hud_str = f"X: {ix}  Y: {iy}  |  Img1: {val1:.1f}  |  Img2: {val2:.1f}"
            else:
                self.hud_str = f"X: {ix}  Y: {iy}  |  Intensity: {val1:.1f}"
        else:
            self.hud_str = ""
            
        if hasattr(self, 'hud_item') and self.canvas.type(self.hud_item):
            self.canvas.itemconfig(self.hud_item, text=self.hud_str)
        if self.split_mode and hasattr(self, 'hud_item2') and self.canvas2.type(self.hud_item2):
            self.canvas2.itemconfig(self.hud_item2, text=self.hud_str)

    def toggle_target_mode(self):
        if self.image_data is None: return
        new_mode = "noise" if self.target_mode_var.get() == "signal" else "signal"
        self.target_mode_var.set(new_mode)
        self.update_task_text()

    def update_task_text(self):
        if self.image_data is None: return
        t_mode = self.target_mode_var.get()
        if t_mode == "signal":
            self.task_label.config(text=f"TASK: Draw Signal {len(self.signal_rois)+1}.\n(Press 'Space' to switch to Noise)")
        else:
            self.task_label.config(text="TASK: Draw Noise ROI.\n(Press 'Space' to switch to Signal)")

    def _save_current_rois_to_volume(self):
        if not hasattr(self, 'current_slice_idx') or self.current_slice_idx is None: return
        state = {
            'signals': [{'mask': r['mask'].copy()} for r in self.signal_rois],
            'noise': {'mask': self.noise_roi['mask'].copy()} if self.noise_roi else None,
            'calipers': [c.copy() for c in self.calipers],
            'profiles': [p.copy() for p in self.profiles]
        }
        self.volume_rois[self.current_slice_idx] = state

    def _load_current_rois_from_volume(self):
        if self.current_slice_idx in self.volume_rois:
            state = self.volume_rois[self.current_slice_idx]
            self.signal_rois = [{'mask': r['mask'].copy()} for r in state['signals']]
            self.noise_roi = {'mask': state['noise']['mask'].copy()} if state['noise'] else None
            self.calipers = [c.copy() for c in state['calipers']]
            self.profiles = [p.copy() for p in state['profiles']]
        else:
            if not self.keep_rois_var.get():
                self.signal_rois = []
                self.noise_roi = None
                self.calipers = []
                self.profiles = []

        self.redo_stack.clear()
        self.update_undo_redo_state()
        self.rebuild_mask_overlay()
        self.calculate_and_show_results()
        if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def load_dicom_dialog(self):
        filetypes = [("All Supported Files", "*.*"), ("DICOM files", "*.dcm"), ("NIfTI files", "*.nii"), ("Compressed files", "*.gz")]
        file_path = filedialog.askopenfilename(title="Select primary image", filetypes=filetypes)
        if file_path: self.load_dicom_file(file_path)
        
    def load_split_screen_dialog(self):
        if self.image_data is None:
            messagebox.showerror("Error", "Please load a primary image first.")
            return
        filetypes = [("All Supported Files", "*.*"), ("DICOM files", "*.dcm"), ("NIfTI files", "*.nii"), ("Compressed files", "*.gz")]
        file_path = filedialog.askopenfilename(title="Select secondary image for Split-Screen", filetypes=filetypes)
        if file_path: self.load_dicom_file2(file_path)

    def close_split_screen(self):
        self.split_mode = False
        self.right_img_frame.pack_forget()
        self.image_data2 = None
        self.dicom_dataset2 = None
        self.base_pil_image2 = None
        self.tk_image2 = None
        self.current_file_path2 = None
        self.nifti_mode2 = False
        self.nifti_volume2 = None
        self.top_label2.config(text="Image 2: No file loaded")
        self.file_menu.entryconfig("Load Split-Screen Data", state=tk.NORMAL)
        self.file_menu.entryconfig("Close Split-Screen", state=tk.DISABLED)
        self.calculate_and_show_results()
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
        
    def load_new_data_dialog(self):
        filetypes = [("All Supported Files", "*.*"), ("DICOM files", "*.dcm"), ("NIfTI files", "*.nii"), ("Compressed files", "*.gz")]
        file_path = filedialog.askopenfilename(title="Select new image data (Hard Reset)", filetypes=filetypes)
        if file_path:
            self.show_std_var.set(True)
            self.show_cnr_var.set(True)
            self.colormap_var.set(self.prefs["default_colormap"])
            self.keep_rois_var.set(True)
            self.current_tool_var.set(self.prefs["default_tool"])
            self.target_mode_var.set("signal")
            self.loupe_zoom_var.set(3.0)
            
            self.show_roi_numbers_var.set(False)
            self.extended_colors_var.set(False)
            self.auto_features_triggered = False
            
            self.signal_rois = []
            self.noise_roi = None
            self.calipers = []
            self.profiles = []
            self.history_stack = []
            self.redo_stack = []
            self.current_results = None
            self.volume_rois = {}
            self.start_keyframe_idx = None
            self.end_keyframe_idx = None
            
            self.close_split_screen()
            self.load_dicom_file(file_path, force_reset=True)

    def reset_app_keep_data(self, event=None):
        if self.image_data is None: return
        self.signal_rois.clear()
        self.noise_roi = None
        self.calipers.clear()
        self.profiles.clear()
        self.history_stack.clear()
        self.redo_stack.clear()
        self.volume_rois.clear()
        self.start_keyframe_idx = None
        self.end_keyframe_idx = None
        
        self.target_mode_var.set("signal")
        self.current_tool_var.set(self.prefs["default_tool"])
        self.colormap_var.set(self.prefs["default_colormap"])
        
        self.show_std_var.set(True)
        self.show_cnr_var.set(True)
        self.keep_rois_var.set(True)
        self.show_roi_numbers_var.set(False)
        self.extended_colors_var.set(False)
        self.auto_features_triggered = False
        self.loupe_zoom_var.set(3.0)
        
        self.mask_overlay = Image.new("RGBA", (self.orig_w, self.orig_h), (0,0,0,0))
        if self.split_mode: self.mask_overlay2 = Image.new("RGBA", (self.orig_w, self.orig_h), (0,0,0,0))
        for widget in self.results_inner_frame.winfo_children(): widget.destroy()
        self.update_task_text()
        
        self.update_undo_redo_state()
        self.reset_windowing()
        self.rebuild_mask_overlay()
        self.calculate_and_show_results()
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
        messagebox.showinfo("Reset Successful", "All overalys, tools, ROIs, and memory flushed.\nData remains untouched.")

    def build_sorted_dir(self, dir_name):
        files = [f for f in os.listdir(dir_name) if f.lower().endswith('.dcm')]
        def sort_key(f):
            try:
                ds = pydicom.dcmread(os.path.join(dir_name, f), specific_tags=['InstanceNumber'], stop_before_pixels=True)
                return (int(ds.InstanceNumber), f)
            except: return (999999, f)
        files.sort(key=sort_key)
        return dir_name, files

    def navigate_file(self, direction):
        if not self.current_file_path: return
        self._save_current_rois_to_volume()

        if self.nifti_mode:
            new_idx = (self.current_slice_idx + direction) % self.nifti_volume.shape[2]
            self.current_slice_idx = new_idx
            self.image_data = self.nifti_volume[:, :, new_idx].T
            self.top_label.config(text=f"Image 1: {os.path.basename(self.current_file_path)} (Slice {new_idx+1}/{self.nifti_volume.shape[2]})")
            
            if self.split_mode and self.nifti_mode2:
                new_idx2 = (self.current_slice_idx2 + direction) % self.nifti_volume2.shape[2]
                self.current_slice_idx2 = new_idx2
                self.image_data2 = self.nifti_volume2[:, :, new_idx2].T
                self.top_label2.config(text=f"Image 2: {os.path.basename(self.current_file_path2)} (Slice {new_idx2+1}/{self.nifti_volume2.shape[2]})")
            
            self._load_current_rois_from_volume()
            self.apply_windowing()
            return

        dir1 = os.path.dirname(self.current_file_path)
        if dir1 != self.current_dir:
            self.current_dir, self.sorted_dir_files = self.build_sorted_dir(dir1)
            
        try:
            c_idx = self.sorted_dir_files.index(os.path.basename(self.current_file_path))
            n_idx = (c_idx + direction) % len(self.sorted_dir_files)
            n_file = os.path.join(dir1, self.sorted_dir_files[n_idx])
            
            self.is_navigating = True
            self.load_dicom_file(n_file)
            self.is_navigating = False
            
            if self.split_mode and self.current_file_path2 and not self.nifti_mode2:
                dir2 = os.path.dirname(self.current_file_path2)
                if dir2 != self.current_dir2:
                    self.current_dir2, self.sorted_dir_files2 = self.build_sorted_dir(dir2)
                try:
                    c_idx2 = self.sorted_dir_files2.index(os.path.basename(self.current_file_path2))
                    n_idx2 = (c_idx2 + direction) % len(self.sorted_dir_files2)
                    n_file2 = os.path.join(dir2, self.sorted_dir_files2[n_idx2])
                    self.load_dicom_file2(n_file2)
                except ValueError: pass

            self.current_slice_idx = n_idx
            self._load_current_rois_from_volume()

        except ValueError: pass

    def on_slice_scroll(self, event):
        if self.image_data is None: return
        direction = 1 if event.delta < 0 else -1 
        self.navigate_file(direction)

    def load_dicom_file(self, file_path, force_reset=False):
        is_nifti = file_path.lower().endswith('.nii') or file_path.lower().endswith('.nii.gz')
        
        if is_nifti:
            try:
                import nibabel as nib
                nii = nib.load(file_path)
                data = nii.get_fdata()
                if data.ndim == 2:
                    data = np.expand_dims(data, axis=2)
                elif data.ndim > 3:
                    data = data[:, :, :, 0]
                
                self.nifti_mode = True
                self.nifti_volume = data
                try: self.nifti_spacing = nii.header.get_zooms()
                except: self.nifti_spacing = (1.0, 1.0, 1.0)
                
                self.dicom_dataset = None
                self.current_file_path = file_path
                self.current_dir = os.path.dirname(file_path)
                self.sorted_dir_files = [f"Slice {i}" for i in range(data.shape[2])]
                
                if not self.is_navigating and not force_reset:
                    self.current_slice_idx = data.shape[2] // 2
                
                self.image_data = self.nifti_volume[:, :, self.current_slice_idx].T
                self.top_label.config(text=f"Image 1: {os.path.basename(file_path)} (Slice {self.current_slice_idx+1}/{data.shape[2]})")
                
                self.default_window_center = (np.max(self.image_data) + np.min(self.image_data)) / 2
                self.default_window_width = max(1, np.max(self.image_data) - np.min(self.image_data))
                self.window_center = self.default_window_center
                self.window_width = self.default_window_width
                
            except Exception as e:
                messagebox.showerror("Error", f"Could not read NIfTI file:\n{e}\n\nMake sure nibabel is installed (pip install nibabel)")
                return
        else:
            try:
                self.dicom_dataset = pydicom.dcmread(file_path)
                self.image_data = self.dicom_dataset.pixel_array.astype(float)
                self.nifti_mode = False
                self.nifti_volume = None
            except Exception as e:
                messagebox.showerror("Error", f"Could not read DICOM file:\n{e}")
                return

            self.current_file_path = file_path
            self.top_label.config(text=f"Image 1: {os.path.basename(file_path)}")
            
            dir_name = os.path.dirname(file_path)
            if self.current_dir != dir_name:
                self.current_dir, self.sorted_dir_files = self.build_sorted_dir(dir_name)
            try: self.current_slice_idx = self.sorted_dir_files.index(os.path.basename(file_path))
            except: self.current_slice_idx = 0

            try:
                wc, ww = self.dicom_dataset.WindowCenter, self.dicom_dataset.WindowWidth
                self.default_window_center = float(wc[0]) if isinstance(wc, pydicom.multival.MultiValue) else float(wc)
                self.default_window_width = float(ww[0]) if isinstance(ww, pydicom.multival.MultiValue) else float(ww)
            except:
                self.default_window_center = (np.max(self.image_data) + np.min(self.image_data)) / 2
                self.default_window_width = max(1, np.max(self.image_data) - np.min(self.image_data))
                
            self.window_center = self.default_window_center
            self.window_width = self.default_window_width

        new_h, new_w = self.image_data.shape

        self.file_menu.entryconfig("Select New ROI", state=tk.NORMAL)
        self.file_menu.entryconfig("Reset All Overlays (Keep Data)", state=tk.NORMAL)
        self.file_menu.entryconfig("View DICOM Metadata", state=tk.NORMAL)
        self.file_menu.entryconfig("Export Data / Anonymize", state=tk.NORMAL)
        self.file_menu.entryconfig("Load Split-Screen Data", state=tk.NORMAL)
        self.tools_menu.entryconfig("3D: Set Start Slice", state=tk.NORMAL)
        self.tools_menu.entryconfig("3D: Set End Slice", state=tk.NORMAL)
        self.tools_menu.entryconfig("3D: Interpolate ROIs", state=tk.NORMAL)
        self.tools_menu.entryconfig("Batch Analyze 3D Volume", state=tk.NORMAL)
        
        if hasattr(self, 'btn_reset'):
            self.btn_reset.config(state=tk.NORMAL)
        
        size_changed = (self.orig_h != new_h or self.orig_w != new_w)
        self.orig_h, self.orig_w = new_h, new_w 
        
        if force_reset or size_changed or (not self.keep_rois_var.get() and not self.is_navigating):
            self.signal_rois = []
            self.noise_roi = None
            self.calipers = []
            self.profiles = []
            self.history_stack = []
            self.redo_stack = []
            self.current_results = None
            self.volume_rois = {}
            self.start_keyframe_idx = None
            self.end_keyframe_idx = None
            self.target_mode_var.set("signal")
            self.mask_overlay = Image.new("RGBA", (self.orig_w, self.orig_h), (0,0,0,0))
            if self.split_mode: self.mask_overlay2 = Image.new("RGBA", (self.orig_w, self.orig_h), (0,0,0,0))
            
            for widget in self.results_inner_frame.winfo_children(): widget.destroy()
                
            self.update_task_text()
            self.update_undo_redo_state()
            self.view_menu.entryconfig("Show ROI Histograms", state=tk.DISABLED)
            self.file_menu.entryconfig("Save Screenshot", state=tk.DISABLED)
            self.file_menu.entryconfig("Save Screenshot As...", state=tk.DISABLED)
            self.file_menu.entryconfig("Export Full PDF Report", state=tk.DISABLED)
            self.file_menu.entryconfig("Log Results to CSV", state=tk.DISABLED)
            
            cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
            if cw >= 10 and ch >= 10:
                self.actual_scale = min(cw / self.orig_w, ch / self.orig_h)
                self.off_x = (cw - self.orig_w * self.actual_scale) / 2
                self.off_y = (ch - self.orig_h * self.actual_scale) / 2
                self.last_cw = cw
                self.last_ch = ch

        self.apply_windowing()
        if not self.is_navigating and not force_reset and self.keep_rois_var.get() and not size_changed:
            self.rebuild_mask_overlay()
            self.calculate_and_show_results()
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def load_dicom_file2(self, file_path):
        is_nifti = file_path.lower().endswith('.nii') or file_path.lower().endswith('.nii.gz')
        
        if is_nifti:
            try:
                import nibabel as nib
                nii = nib.load(file_path)
                data = nii.get_fdata()
                if data.ndim == 2:
                    data = np.expand_dims(data, axis=2)
                elif data.ndim > 3:
                    data = data[:, :, :, 0]
                
                self.nifti_mode2 = True
                self.nifti_volume2 = data
                self.dicom_dataset2 = None
                self.current_file_path2 = file_path
                self.current_dir2 = os.path.dirname(file_path)
                self.sorted_dir_files2 = [f"Slice {i}" for i in range(data.shape[2])]
                self.current_slice_idx2 = data.shape[2] // 2
                
                img_data2 = self.nifti_volume2[:, :, self.current_slice_idx2].T
                self.top_label2.config(text=f"Image 2: {os.path.basename(file_path)} (Slice {self.current_slice_idx2+1}/{data.shape[2]})")
                
                self.default_window_center2 = (np.max(img_data2) + np.min(img_data2)) / 2
                self.default_window_width2 = max(1, np.max(img_data2) - np.min(img_data2))
                self.window_center2 = self.default_window_center2
                self.window_width2 = self.default_window_width2
                
            except Exception as e:
                messagebox.showerror("Error", f"Could not read NIfTI file:\n{e}")
                return
        else:
            try:
                ds = pydicom.dcmread(file_path)
                img_data2 = ds.pixel_array.astype(float)
                self.nifti_mode2 = False
                self.nifti_volume2 = None
                self.dicom_dataset2 = ds
                self.current_file_path2 = file_path
                self.top_label2.config(text=f"Image 2: {os.path.basename(file_path)}")
                
                dir_name2 = os.path.dirname(file_path)
                if self.current_dir2 != dir_name2:
                    self.current_dir2, self.sorted_dir_files2 = self.build_sorted_dir(dir_name2)
                    
                try:
                    wc, ww = self.dicom_dataset2.WindowCenter, self.dicom_dataset2.WindowWidth
                    self.default_window_center2 = float(wc[0]) if isinstance(wc, pydicom.multival.MultiValue) else float(wc)
                    self.default_window_width2 = float(ww[0]) if isinstance(ww, pydicom.multival.MultiValue) else float(ww)
                except:
                    self.default_window_center2 = (np.max(img_data2) + np.min(img_data2)) / 2
                    self.default_window_width2 = max(1, np.max(img_data2) - np.min(img_data2))
                    
                self.window_center2 = self.default_window_center2
                self.window_width2 = self.default_window_width2
            except Exception as e:
                messagebox.showerror("Error", f"Could not read DICOM file:\n{e}")
                return

        if img_data2.shape != (self.orig_h, self.orig_w):
            messagebox.showerror("Dimension Mismatch", "Image 2 must have the exact same pixel dimensions as Image 1 for accurate Synchronized Split-Screen.")
            return

        self.image_data2 = img_data2
        self.split_mode = True
        self.right_img_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.file_menu.entryconfig("Load Split-Screen Data", state=tk.DISABLED)
        self.file_menu.entryconfig("Close Split-Screen", state=tk.NORMAL)
        
        self.rebuild_mask_overlay()
        self.apply_windowing()
        self.calculate_and_show_results()

    def set_start_keyframe(self):
        self._save_current_rois_to_volume()
        self.start_keyframe_idx = self.current_slice_idx
        messagebox.showinfo("Start Keyframe Set", f"Start slice set to Index {self.current_slice_idx}.")

    def set_end_keyframe(self):
        self._save_current_rois_to_volume()
        self.end_keyframe_idx = self.current_slice_idx
        messagebox.showinfo("End Keyframe Set", f"End slice set to Index {self.current_slice_idx}.")

    def interpolate_3d_rois(self):
        if self.start_keyframe_idx is None or self.end_keyframe_idx is None:
            messagebox.showerror("Error", "Please set both a Start and End slice first using the Tools menu.")
            return

        start_idx = min(self.start_keyframe_idx, self.end_keyframe_idx)
        end_idx = max(self.start_keyframe_idx, self.end_keyframe_idx)

        if end_idx - start_idx <= 1:
            messagebox.showinfo("Error", "Start and End slices must have at least one slice between them to interpolate.")
            return

        if start_idx not in self.volume_rois or end_idx not in self.volume_rois:
            messagebox.showerror("Error", "Keyframes are missing ROI data. Please draw and set them again.")
            return

        state_A = self.volume_rois[start_idx]
        state_B = self.volume_rois[end_idx]

        for step_idx in range(start_idx + 1, end_idx):
            frac = (step_idx - start_idx) / float(end_idx - start_idx)
            new_state = {'signals': [], 'noise': None, 'calipers': [], 'profiles': []}

            if state_A['noise'] and state_B['noise']:
                new_state['noise'] = {'mask': self._interpolate_mask(state_A['noise']['mask'], state_B['noise']['mask'], frac)}

            max_sigs = min(len(state_A['signals']), len(state_B['signals']))
            for sig_idx in range(max_sigs):
                mA = state_A['signals'][sig_idx]['mask']
                mB = state_B['signals'][sig_idx]['mask']
                new_state['signals'].append({'mask': self._interpolate_mask(mA, mB, frac)})
                
            max_cals = min(len(state_A['calipers']), len(state_B['calipers']))
            for j in range(max_cals):
                cA, cB = state_A['calipers'][j], state_B['calipers'][j]
                nC = {}
                for k in ['x1','y1','x2','y2','dist']: nC[k] = cA[k] + (cB[k] - cA[k]) * frac
                new_state['calipers'].append(nC)

            max_profs = min(len(state_A['profiles']), len(state_B['profiles']))
            for j in range(max_profs):
                pA, pB = state_A['profiles'][j], state_B['profiles'][j]
                nP = {}
                for k in ['x1','y1','x2','y2','dist']: nP[k] = pA[k] + (pB[k] - pA[k]) * frac
                nP['intensities'] = []
                new_state['profiles'].append(nP)

            self.volume_rois[step_idx] = new_state

        self._load_current_rois_from_volume()
        messagebox.showinfo("Success", f"3D Z-Axis ROIs successfully tracked and interpolated between slices {start_idx} and {end_idx}!")

    def _shift_mask(self, mask, dx, dy):
        shifted = np.zeros_like(mask)
        h, w = mask.shape
        sx1, sy1 = max(0, -dx), max(0, -dy)
        sx2, sy2 = min(w, w - dx), min(h, h - dy)
        dx1, dy1 = max(0, dx), max(0, dy)
        dx2, dy2 = min(w, w + dx), min(h, h + dy)

        if dx1 < dx2 and dy1 < dy2 and sx1 < sx2 and sy1 < sy2:
            shifted[dy1:dy2, dx1:dx2] = mask[sy1:sy2, sx1:sx2]
        return shifted
        
    def _interpolate_mask(self, maskA, maskB, frac):
        ptsA = np.argwhere(maskA)
        ptsB = np.argwhere(maskB)
        if len(ptsA) == 0: return maskB.copy()
        if len(ptsB) == 0: return maskA.copy()

        yA_min, xA_min = ptsA.min(axis=0)
        yA_max, xA_max = ptsA.max(axis=0)
        yB_min, xB_min = ptsB.min(axis=0)
        yB_max, xB_max = ptsB.max(axis=0)

        y_min = int(round(yA_min + (yB_min - yA_min) * frac))
        x_min = int(round(xA_min + (xB_min - xA_min) * frac))
        y_max = int(round(yA_max + (yB_max - yA_max) * frac))
        x_max = int(round(xA_max + (xB_max - xA_max) * frac))

        new_w = max(1, x_max - x_min + 1)
        new_h = max(1, y_max - y_min + 1)

        cropA = maskA[yA_min:yA_max+1, xA_min:xA_max+1].astype(np.uint8) * 255
        imgA = Image.fromarray(cropA, mode='L')
        img_resA = imgA.resize((new_w, new_h), Image.NEAREST)
        arr_resA = np.array(img_resA) > 127
        
        cropB = maskB[yB_min:yB_max+1, xB_min:xB_max+1].astype(np.uint8) * 255
        imgB = Image.fromarray(cropB, mode='L')
        img_resB = imgB.resize((new_w, new_h), Image.NEAREST)
        arr_resB = np.array(img_resB) > 127
        
        if frac < 0.5:
            arr_res = arr_resA
        else:
            arr_res = arr_resB

        new_mask = np.zeros_like(maskA)
        h, w = new_mask.shape
        start_y = max(0, y_min)
        end_y = min(h, y_min + new_h)
        start_x = max(0, x_min)
        end_x = min(w, x_min + new_w)
        
        src_start_y = start_y - y_min
        src_end_y = src_start_y + (end_y - start_y)
        src_start_x = start_x - x_min
        src_end_x = src_start_x + (end_x - start_x)
        
        if start_y < end_y and start_x < end_x:
            new_mask[start_y:end_y, start_x:end_x] = arr_res[src_start_y:src_end_y, src_start_x:src_end_x]
            
        return new_mask

    def _anonymize_dataset(self, ds):
        anon_ds = ds.copy()
        tags_to_anonymize = ['PatientName', 'PatientID', 'PatientBirthDate', 'PatientSex', 'InstitutionName', 'StudyID', 'AccessionNumber']
        for tag in tags_to_anonymize:
            if tag in anon_ds:
                if tag == 'PatientName': anon_ds.data_element(tag).value = "ANONYMOUS^PATIENT"
                elif tag in ['PatientID', 'StudyID', 'AccessionNumber']: anon_ds.data_element(tag).value = "000000"
                elif tag == 'PatientBirthDate': anon_ds.data_element(tag).value = "19000101"
                else: anon_ds.data_element(tag).value = "ANONYMOUS"
        try: anon_ds.remove_private_tags()
        except: pass
        return anon_ds

    def anonymize_dicom(self):
        if not self.current_file_path: return
        
        top = tk.Toplevel(self.root)
        top.title("Export & Anonymize Data")
        top.geometry("450x380")
        
        bg_col = "#1E1E1E" if self.dark_mode_var.get() else "white"
        fg_col = "white" if self.dark_mode_var.get() else "black"
        top.configure(bg=bg_col)
        
        # Scope Selection
        tk.Label(top, text="1. Select Scope:", bg=bg_col, fg=fg_col, font=("Arial", 14, "bold")).pack(anchor="w", padx=20, pady=(20, 5))
        scope_var = tk.StringVar(value="file")
        tk.Radiobutton(top, text="Current Active File Only", variable=scope_var, value="file", bg=bg_col, fg=fg_col, font=("Arial", 12)).pack(anchor="w", padx=40)
        tk.Radiobutton(top, text="Entire Directory (Bulk / 3D Volume)", variable=scope_var, value="dir", bg=bg_col, fg=fg_col, font=("Arial", 12)).pack(anchor="w", padx=40)
        
        # Format Selection
        tk.Label(top, text="2. Select Data Format:", bg=bg_col, fg=fg_col, font=("Arial", 14, "bold")).pack(anchor="w", padx=20, pady=(20, 5))
        format_var = tk.StringVar(value="dicom" if not self.nifti_mode else "nifti")
        
        r1 = tk.Radiobutton(top, text="DICOM (.dcm) - Anonymized", variable=format_var, value="dicom", bg=bg_col, fg=fg_col, font=("Arial", 12))
        r1.pack(anchor="w", padx=40)
        if self.nifti_mode: r1.config(state=tk.DISABLED)
        
        tk.Radiobutton(top, text="NIfTI (.gz)", variable=format_var, value="nifti", bg=bg_col, fg=fg_col, font=("Arial", 12)).pack(anchor="w", padx=40)
        
        def proceed():
            s = scope_var.get()
            f = format_var.get()
            top.destroy()
            self._process_export(s, f)
            
        btn_frame = tk.Frame(top, bg=bg_col)
        btn_frame.pack(side=tk.BOTTOM, pady=20)
        tk.Button(btn_frame, text="Cancel", command=top.destroy).pack(side=tk.LEFT, padx=10)
        tk.Button(btn_frame, text="Continue", font=("Arial", 12, "bold"), command=proceed).pack(side=tk.LEFT, padx=10)

    def _process_export(self, scope, fmt):
        if fmt == "nifti":
            try:
                import nibabel as nib
            except ImportError:
                messagebox.showerror("Dependency Missing", "The 'nibabel' library is required to create NIfTI files.\n\nPlease open your terminal and run:\npip install nibabel")
                return

        if scope == "file":
            if fmt == "dicom":
                if self.nifti_mode: return
                target_path = filedialog.asksaveasfilename(
                    initialfile=f"anon_{os.path.basename(self.current_file_path)}",
                    title="Export Anonymized DICOM", defaultextension=".dcm", filetypes=[("DICOM files", "*.dcm")]
                )
                if not target_path: return
                try:
                    anon_ds = self._anonymize_dataset(self.dicom_dataset)
                    anon_ds.save_as(target_path)
                    messagebox.showinfo("Success", f"Anonymized DICOM saved safely to:\n{target_path}")
                except Exception as e: messagebox.showerror("Error", f"Failed to save DICOM:\n{e}")
                
            elif fmt == "nifti":
                target_path = filedialog.asksaveasfilename(
                    initialfile=f"export_{os.path.splitext(os.path.basename(self.current_file_path))[0]}.gz",
                    title="Export NIfTI", defaultextension=".gz", filetypes=[("GZipped NIfTI", "*.gz"), ("All files", "*.*")]
                )
                if not target_path: return
                try:
                    import nibabel as nib
                    affine = np.eye(4)
                    
                    if not self.nifti_mode:
                        try: 
                            spacing = self.dicom_dataset.PixelSpacing
                            affine[0,0] = float(spacing[1])
                            affine[1,1] = float(spacing[0])
                        except: pass
                        nii_data = np.transpose(self.image_data)
                    else:
                        affine[0,0] = self.nifti_spacing[0]
                        affine[1,1] = self.nifti_spacing[1]
                        affine[2,2] = self.nifti_spacing[2] if len(self.nifti_spacing) > 2 else 1.0
                        nii_data = self.nifti_volume
                        
                    nii = nib.Nifti1Image(nii_data, affine)
                    nib.save(nii, target_path)
                    messagebox.showinfo("Success", f"NIfTI cleanly generated and saved to:\n{target_path}")
                except Exception as e: messagebox.showerror("Error", f"Failed to generate NIfTI:\n{e}")
                
        elif scope == "dir":
            if self.nifti_mode:
                if fmt == "nifti":
                    target_path = filedialog.asksaveasfilename(
                        initialfile=f"bulk_export_{os.path.basename(self.current_file_path)}.gz",
                        title="Export NIfTI Volume", defaultextension=".gz", filetypes=[("GZipped NIfTI", "*.gz"), ("All files", "*.*")]
                    )
                    if not target_path: return
                    try:
                        import nibabel as nib
                        affine = np.eye(4)
                        affine[0,0] = self.nifti_spacing[0]
                        affine[1,1] = self.nifti_spacing[1]
                        if len(self.nifti_spacing) > 2: affine[2,2] = self.nifti_spacing[2]
                        nib.save(nib.Nifti1Image(self.nifti_volume, affine), target_path)
                        messagebox.showinfo("Success", f"NIfTI Volume exported to:\n{target_path}")
                    except Exception as e: messagebox.showerror("Error", f"Failed to save:\n{e}")
                return

            if not self.sorted_dir_files:
                self.current_dir, self.sorted_dir_files = self.build_sorted_dir(os.path.dirname(self.current_file_path))
                
            if not self.sorted_dir_files: return
            
            parent_dir = filedialog.askdirectory(title="Select Destination Parent Directory")
            if not parent_dir: return
            
            folder_name = simpledialog.askstring("Folder Name", "Please enter a name for the newly created container folder:", initialvalue="Anonymized_Export")
            if not folder_name: return
            
            target_dir = os.path.join(parent_dir, folder_name)
            try: os.makedirs(target_dir, exist_ok=True)
            except Exception as e:
                messagebox.showerror("Error", f"Could not generate secure container directory:\n{e}")
                return

            prog_win = tk.Toplevel(self.root)
            prog_win.title("Exporting...")
            prog_win.geometry("300x120")
            bg_c = "#1E1E1E" if self.dark_mode_var.get() else "white"
            fg_c = "white" if self.dark_mode_var.get() else "black"
            prog_win.configure(bg=bg_c)
            tk.Label(prog_win, text=f"Processing {len(self.sorted_dir_files)} files...\nPlease wait.", font=("Arial", 14), bg=bg_c, fg=fg_c).pack(expand=True)
            prog_win.update()

            try:
                if fmt == "dicom":
                    for file in self.sorted_dir_files:
                        src_path = os.path.join(self.current_dir, file)
                        ds = pydicom.dcmread(src_path)
                        anon_ds = self._anonymize_dataset(ds)
                        anon_ds.save_as(os.path.join(target_dir, file))
                    
                    prog_win.destroy()
                    messagebox.showinfo("Success", f"Bulk Directory correctly anonymized and exported to:\n{target_dir}")
                    
                elif fmt == "nifti":
                    import nibabel as nib
                    vol_stack = []
                    for file in self.sorted_dir_files:
                        src_path = os.path.join(self.current_dir, file)
                        ds = pydicom.dcmread(src_path)
                        vol_stack.append(ds.pixel_array.astype(float))
                        
                    vol_data = np.stack(vol_stack, axis=0) 
                    nii_data = np.transpose(vol_data, (2, 1, 0)) 
                    
                    affine = np.eye(4)
                    try:
                        base_ds = pydicom.dcmread(os.path.join(self.current_dir, self.sorted_dir_files[0]))
                        spacing = base_ds.PixelSpacing
                        affine[0,0] = float(spacing[1])
                        affine[1,1] = float(spacing[0])
                        try: affine[2,2] = float(base_ds.SliceThickness)
                        except: pass
                    except: pass
                    
                    nii = nib.Nifti1Image(nii_data, affine)
                    target_file = os.path.join(target_dir, "volume.nii.gz")
                    nib.save(nii, target_file)
                    
                    prog_win.destroy()
                    messagebox.showinfo("Success", f"3D NIfTI Volume successfully stacked and saved inside:\n{target_dir}")
                    
            except Exception as e:
                prog_win.destroy()
                messagebox.showerror("Batch Error", f"Process failed during bulk export:\n{e}")

    def show_metadata(self):
        if not self.current_file_path: return
        top = tk.Toplevel(self.root)
        top.title("Metadata Viewer")
        top.geometry("600x500")
        
        tree = ttk.Treeview(top, columns=("Tag", "Name", "Value"), show="headings")
        tree.heading("Tag", text="Tag")
        tree.heading("Name", text="Name")
        tree.heading("Value", text="Value")
        tree.column("Tag", width=100, stretch=False)
        tree.column("Name", width=200, stretch=False)
        tree.column("Value", width=300)
        
        scrollbar = ttk.Scrollbar(top, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        tree.pack(fill="both", expand=True)

        if self.nifti_mode:
            try:
                import nibabel as nib
                nii = nib.load(self.current_file_path)
                for k, v in nii.header.items():
                    tree.insert("", "end", values=("NIfTI Header", str(k), str(v)[:200]))
            except: pass
        elif self.dicom_dataset:
            for elem in self.dicom_dataset:
                if elem.tag == (0x7fe0, 0x0010): continue 
                try: tree.insert("", "end", values=(f"{elem.tag}", elem.name, str(elem.value)[:200]))
                except: pass

    def show_histogram(self):
        if not self.current_results or (not self.signal_rois and not self.noise_roi): return
        top = tk.Toplevel(self.root)
        top.title("ROI Histograms & Stats")
        top.geometry("600x600")
        top.configure(bg="#1E1E1E" if self.dark_mode_var.get() else "white")
        
        canvas = tk.Canvas(top, bg="#1E1E1E" if self.dark_mode_var.get() else "white", highlightthickness=0)
        canvas.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        active_sig_colors = self.ext_sig_colors if self.extended_colors_var.get() else self.sig_colors
        datasets = []
        for i, s in enumerate(self.signal_rois):
            pixels = self.image_data[s['mask']]
            if len(pixels) > 0: datasets.append((f"Signal {i+1}" + (" (Img 1)" if self.split_mode else ""), pixels, active_sig_colors[i % len(active_sig_colors)]))
            if self.split_mode and self.image_data2 is not None:
                pixels2 = self.image_data2[s['mask']]
                if len(pixels2) > 0: datasets.append((f"Signal {i+1} (Img 2)", pixels2, active_sig_colors[i % len(active_sig_colors)]))
                
        if self.noise_roi:
            pixels = self.image_data[self.noise_roi['mask']]
            if len(pixels) > 0: datasets.append(("Noise" + (" (Img 1)" if self.split_mode else ""), pixels, self.noise_color))
            if self.split_mode and self.image_data2 is not None:
                pixels2 = self.image_data2[self.noise_roi['mask']]
                if len(pixels2) > 0: datasets.append(("Noise (Img 2)", pixels2, self.noise_color))
            
        if not datasets: return
        
        scroll_frame = tk.Frame(canvas, bg="#1E1E1E" if self.dark_mode_var.get() else "white")
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        
        h_per_graph = 250
        text_color = "white" if self.dark_mode_var.get() else "black"
        
        for idx, (name, data, color) in enumerate(datasets):
            y_offset = idx * h_per_graph
            stat_text = f"{name} | Min: {np.min(data):.1f} | Max: {np.max(data):.1f} | Median: {np.median(data):.1f} | Mean: {np.mean(data):.1f} | Std: {np.std(data):.1f}"
            canvas.create_text(10, y_offset + 10, anchor="nw", text=stat_text, fill=text_color, font=("Arial", 12, "bold"))
            
            counts, bins = np.histogram(data, bins=50)
            max_count = max(1, np.max(counts))
            
            bar_w = 540 / 50
            graph_h = h_per_graph - 40
            hex_color = f"#{color[0]:02x}{color[1]:02x}{color[2]:02x}"
            
            for b_idx, count in enumerate(counts):
                bar_h = (count / max_count) * graph_h
                x1 = 10 + (b_idx * bar_w)
                y1 = y_offset + 30 + graph_h
                x2 = x1 + bar_w - 1
                y2 = y1 - bar_h
                canvas.create_rectangle(x1, y1, x2, y2, fill=hex_color, outline="")
                
            canvas.create_line(10, y_offset + 30 + graph_h, 550, y_offset + 30 + graph_h, fill=text_color)
            
        canvas.configure(scrollregion=canvas.bbox("all"))

    def _generate_histogram_page(self):
        if not self.current_results or (not self.signal_rois and not self.noise_roi): return None
        if not self.prefs.get("pdf_include_histograms", True): return None
        
        active_sig_colors = self.ext_sig_colors if self.extended_colors_var.get() else self.sig_colors
        datasets = []
        for i, s in enumerate(self.signal_rois):
            pixels = self.image_data[s['mask']]
            if len(pixels) > 0: datasets.append((f"Signal {i+1}" + (" (Img 1)" if self.split_mode else ""), pixels, active_sig_colors[i % len(active_sig_colors)]))
            if self.split_mode and self.image_data2 is not None:
                pixels2 = self.image_data2[s['mask']]
                if len(pixels2) > 0: datasets.append((f"Signal {i+1} (Img 2)", pixels2, active_sig_colors[i % len(active_sig_colors)]))
                
        if self.noise_roi:
            pixels = self.image_data[self.noise_roi['mask']]
            if len(pixels) > 0: datasets.append(("Noise" + (" (Img 1)" if self.split_mode else ""), pixels, self.noise_color))
            if self.split_mode and self.image_data2 is not None:
                pixels2 = self.image_data2[self.noise_roi['mask']]
                if len(pixels2) > 0: datasets.append(("Noise (Img 2)", pixels2, self.noise_color))
                
        if not datasets: return None
        
        try: font_title = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 26)
        except: font_title = ImageFont.load_default()
        try: font_stat = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 18)
        except: font_stat = ImageFont.load_default()

        h_per_graph = 300
        page_w = 1200
        page_h = max(1600, 200 + len(datasets) * h_per_graph)
        
        bg_col = "#1E1E1E" if self.dark_mode_var.get() else "white"
        text_col = "white" if self.dark_mode_var.get() else "black"
        
        img = Image.new("RGB", (page_w, page_h), bg_col)
        draw = ImageDraw.Draw(img)
        
        draw.text((100, 100), "ROI Histograms & Comprehensive Statistics", fill=text_col, font=font_title)
        draw.line([100, 150, 1100, 150], fill="gray", width=2)

        for idx, (name, data, color) in enumerate(datasets):
            y_offset = 200 + idx * h_per_graph
            stat_text = f"{name} | Min: {np.min(data):.1f} | Max: {np.max(data):.1f} | Median: {np.median(data):.1f} | Mean: {np.mean(data):.1f} | Std: {np.std(data):.1f}"
            draw.text((100, y_offset), stat_text, fill=text_col, font=font_stat)
            
            counts, bins = np.histogram(data, bins=50)
            max_count = max(1, np.max(counts))
            
            bar_w = 1000 / 50
            graph_h = h_per_graph - 80
            hex_color = f"#{color[0]:02x}{color[1]:02x}{color[2]:02x}"
            
            for b_idx, count in enumerate(counts):
                bar_h = (count / max_count) * graph_h
                x1 = 100 + (b_idx * bar_w)
                y1 = y_offset + 40 + graph_h
                x2 = x1 + bar_w - 2
                y2 = y1 - bar_h
                draw.rectangle([x1, y2, x2, y1], fill=hex_color)
                
            draw.line([100, y_offset + 40 + graph_h, 1100, y_offset + 40 + graph_h], fill=text_col, width=2)
            
        return img

    def batch_analyze_volume(self):
        if not self.current_file_path or not self.signal_rois: return
        
        if self.nifti_mode:
            self.sorted_dir_files = [f"Slice {i}" for i in range(self.nifti_volume.shape[2])]
            if self.split_mode and self.nifti_mode2:
                self.sorted_dir_files2 = [f"Slice {i}" for i in range(self.nifti_volume2.shape[2])]
        else:
            if not self.sorted_dir_files:
                self.current_dir, self.sorted_dir_files = self.build_sorted_dir(os.path.dirname(self.current_file_path))
            if self.split_mode and self.current_file_path2 and not self.nifti_mode2 and not self.sorted_dir_files2:
                self.current_dir2, self.sorted_dir_files2 = self.build_sorted_dir(os.path.dirname(self.current_file_path2))
            
        if not self.sorted_dir_files: return
        
        top = tk.Toplevel(self.root)
        top.title("Batch Processing 3D Volume...")
        top.geometry("400x150")
        top.configure(bg="#1E1E1E" if self.dark_mode_var.get() else "white")
        
        lbl = tk.Label(top, text="Scanning patient volume (3D Tracked ROIs)...", font=("Arial", 14), bg="#1E1E1E" if self.dark_mode_var.get() else "white", fg="white" if self.dark_mode_var.get() else "black")
        lbl.pack(expand=True)
        top.update()
        
        def analyze_dir(files, d_dir, is_nifti_mode, nifti_vol):
            res = []
            for file_idx, file in enumerate(files):
                try:
                    if is_nifti_mode:
                        arr = nifti_vol[:, :, file_idx].T
                        instance_num = file_idx
                    else:
                        ds = pydicom.dcmread(os.path.join(d_dir, file))
                        arr = ds.pixel_array.astype(float)
                        if arr.shape != (self.orig_h, self.orig_w): continue
                        instance_num = getattr(ds, 'InstanceNumber', 0)
                    
                    state = self.volume_rois.get(file_idx)
                    if not state and self.keep_rois_var.get():
                        state = {'signals': [{'mask': s['mask']} for s in self.signal_rois], 'noise': {'mask': self.noise_roi['mask']} if self.noise_roi else None}
                    elif not state:
                        continue 
                    
                    n_mean = np.mean(arr[state['noise']['mask']]) if state['noise'] else None
                    n_std = np.std(arr[state['noise']['mask']]) if state['noise'] else None
                    
                    slice_data = {
                        'File': file, 
                        'Instance': instance_num, 
                        'Noise_Mean': n_mean,
                        'Noise_Std': n_std,
                        'Signals': []
                    }
                    
                    for sig in state['signals']:
                        pixels = arr[sig['mask']]
                        if len(pixels) > 0:
                            s_mean = np.mean(pixels)
                            snr = (s_mean / n_mean) if n_mean and n_mean != 0 else None
                            slice_data['Signals'].append({'mean': s_mean, 'snr': snr})
                        else:
                            slice_data['Signals'].append({'mean': 0, 'snr': None})
                        
                    res.append(slice_data)
                except: pass
            return res

        results1 = analyze_dir(self.sorted_dir_files, self.current_dir, self.nifti_mode, self.nifti_volume)
        results2 = analyze_dir(self.sorted_dir_files2, self.current_dir2, self.nifti_mode2, self.nifti_volume2) if self.split_mode else []
            
        top.destroy()
        
        target_dir = self._get_target_dir("csv")
        csv_path = os.path.join(target_dir, "batch_volume_log.csv")
        try:
            with open(csv_path, 'w', newline='') as f:
                writer = csv.writer(f)
                header = ['Instance', 'Filename', 'Noise Mean', 'Noise Std']
                for i in range(len(self.signal_rois)):
                    header.extend([f'Sig {i+1} Mean', f'Sig {i+1} SNR'])
                
                if self.split_mode:
                    header.extend(['Img 2 Filename', 'Img 2 Noise Mean', 'Img 2 Noise Std'])
                    for i in range(len(self.signal_rois)):
                        header.extend([f'Img 2 Sig {i+1} Mean', f'Img 2 Sig {i+1} SNR'])
                        
                writer.writerow(header)
                
                max_len = max(len(results1), len(results2)) if self.split_mode else len(results1)
                for idx in range(max_len):
                    row = []
                    if idx < len(results1):
                        r1 = results1[idx]
                        row.extend([r1['Instance'], r1['File'], 
                               round(r1['Noise_Mean'], 4) if r1['Noise_Mean'] else 'N/A', 
                               round(r1['Noise_Std'], 4) if r1['Noise_Std'] else 'N/A'])
                        for s in r1['Signals']:
                            row.extend([round(s['mean'], 4), round(s['snr'], 4) if s['snr'] else 'N/A'])
                    else:
                        row.extend(['N/A', 'N/A', 'N/A', 'N/A'])
                        for _ in range(len(self.signal_rois) * 2): row.append('N/A')
                        
                    if self.split_mode:
                        if idx < len(results2):
                            r2 = results2[idx]
                            row.extend([r2['File'], 
                                   round(r2['Noise_Mean'], 4) if r2['Noise_Mean'] else 'N/A', 
                                   round(r2['Noise_Std'], 4) if r2['Noise_Std'] else 'N/A'])
                            for s in r2['Signals']:
                                row.extend([round(s['mean'], 4), round(s['snr'], 4) if s['snr'] else 'N/A'])
                        else:
                            row.extend(['N/A', 'N/A', 'N/A'])
                            for _ in range(len(self.signal_rois) * 2): row.append('N/A')
                    writer.writerow(row)
                    
            messagebox.showinfo("Success", f"3D Volume completely analyzed!\nResults safely exported to:\n{csv_path}")
            
            if results1: self.draw_batch_graph(results1, "Z-Axis Volume Profile (Image 1)" if self.split_mode else "Z-Axis Volume Profile")
            if self.split_mode and results2: self.draw_batch_graph(results2, "Z-Axis Volume Profile (Image 2)")
            
        except Exception as e: messagebox.showerror("Error", f"Failed to batch log:\n{e}")

    def draw_batch_graph(self, results, title):
        top = tk.Toplevel(self.root)
        top.title(title)
        top.geometry("700x500")
        top.configure(bg="#1E1E1E" if self.dark_mode_var.get() else "white")
        
        canvas = tk.Canvas(top, bg="#1E1E1E" if self.dark_mode_var.get() else "white", highlightthickness=0)
        canvas.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        canvas.update_idletasks()
        
        w, h = canvas.winfo_width(), canvas.winfo_height()
        if w < 10: w, h = 660, 460
        pad_x, pad_y, top_y = 50, 40, 40
        graph_w, graph_h = w - pad_x * 2, h - top_y - pad_y
        
        text_col = "white" if self.dark_mode_var.get() else "black"
        canvas.create_text(10, 10, anchor="nw", text=title, fill=text_col, font=("Arial", 14, "bold"))
        
        instances = [r['Instance'] for r in results]
        min_x, max_x = min(instances), max(instances)
        if max_x == min_x: max_x = min_x + 1
        
        all_means = [s['mean'] for r in results for s in r['Signals']]
        if results[0]['Noise_Mean']: all_means.extend([r['Noise_Mean'] for r in results])
        
        min_y, max_y = min(all_means), max(all_means)
        if max_y == min_y: max_y = min_y + 1
        
        active_hex_colors = self.ext_hex_colors if self.extended_colors_var.get() else self.hex_colors
        
        for s_idx in range(len(self.signal_rois)):
            color = active_hex_colors[s_idx % len(active_hex_colors)]
            pts = []
            for r in results:
                px = pad_x + ((r['Instance'] - min_x) / (max_x - min_x)) * graph_w
                py = top_y + graph_h - ((r['Signals'][s_idx]['mean'] - min_y) / (max_y - min_y)) * graph_h
                pts.append((px, py))
            canvas.create_line(pts, fill=color, width=2)
            
        if results[0]['Noise_Mean']:
            pts = []
            for r in results:
                px = pad_x + ((r['Instance'] - min_x) / (max_x - min_x)) * graph_w
                py = top_y + graph_h - ((r['Noise_Mean'] - min_y) / (max_y - min_y)) * graph_h
                pts.append((px, py))
            canvas.create_line(pts, fill=self.noise_hex, width=2, dash=(4,2))
            
        canvas.create_line(pad_x, top_y, pad_x, top_y + graph_h, fill=text_col, width=2)
        canvas.create_line(pad_x, top_y + graph_h, pad_x + graph_w, top_y + graph_h, fill=text_col, width=2)

    def reset_windowing(self):
        self.window_center = self.default_window_center
        self.window_width = self.default_window_width
        self.window_center2 = self.default_window_center2
        self.window_width2 = self.default_window_width2
        self.apply_windowing()

    def _get_lut_image(self, img_data, wc, ww, cmap):
        vmin = wc - (ww / 2.0)
        vmax = wc + (ww / 2.0)
        if vmax == vmin: vmax = vmin + 0.1 
        
        clipped = np.clip(img_data, vmin, vmax)
        display_data = 255.0 * (clipped - vmin) / (vmax - vmin)
        
        if cmap == "Grayscale":
            return Image.fromarray(display_data.astype(np.uint8)).convert("RGB")
            
        x = np.linspace(0, 1, 256)
        if cmap == "Heatmap (Rainbow)":
            r = np.clip(1.5 - np.abs(2 * x - 1.5), 0, 1)
            g = np.clip(1.5 - np.abs(2 * x - 1.0), 0, 1)
            b = np.clip(1.5 - np.abs(2 * x - 0.5), 0, 1)
        elif cmap == "Hot Metal":
            r = np.clip(3 * x, 0, 1)
            g = np.clip(3 * x - 1, 0, 1)
            b = np.clip(3 * x - 2, 0, 1)
        elif cmap == "Bone":
            r = np.clip(x * 0.87, 0, 1)
            g = np.clip(x * 0.87 + x**2 * 0.13, 0, 1)
            b = np.clip(x, 0, 1)
        elif cmap == "Jet":
            r = np.clip(1.5 - np.abs(4 * x - 3.0), 0, 1)
            g = np.clip(1.5 - np.abs(4 * x - 2.0), 0, 1)
            b = np.clip(1.5 - np.abs(4 * x - 1.0), 0, 1)
            
        lut = (np.column_stack((r, g, b)) * 255).astype(np.uint8)
        rgb_data = lut[display_data.astype(np.uint8)]
        return Image.fromarray(rgb_data, "RGB")

    def apply_windowing(self):
        if self.image_data is None: return
        cmap = self.colormap_var.get()
        self.base_pil_image = self._get_lut_image(self.image_data, self.window_center, self.window_width, cmap)
        
        if self.split_mode and self.image_data2 is not None:
            self.base_pil_image2 = self._get_lut_image(self.image_data2, self.window_center2, self.window_width2, cmap)
            
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def fit_to_screen(self):
        if self.image_data is None: return
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        if cw < 10: return
        self.actual_scale = min(cw / self.orig_w, ch / self.orig_h)
        self.off_x = (cw - self.orig_w * self.actual_scale) / 2
        self.off_y = (ch - self.orig_h * self.actual_scale) / 2
        self.last_cw = cw
        self.last_ch = ch
        self.redraw(cw, ch)

    def on_zoom(self, event):
        if self.image_data is None: return
        factor = 1.05 if event.delta > 0 else 0.95
        img_x = (event.x - self.off_x) / self.actual_scale
        img_y = (event.y - self.off_y) / self.actual_scale
        self.actual_scale *= factor
        self.off_x = event.x - (img_x * self.actual_scale)
        self.off_y = event.y - (img_y * self.actual_scale)
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def start_windowing(self, event):
        self.last_mouse_x = event.x
        self.last_mouse_y = event.y
        return "break"

    def do_windowing(self, event):
        if self.image_data is None: return "break"
        dx = event.x - self.last_mouse_x
        dy = event.y - self.last_mouse_y
        self.last_mouse_x, self.last_mouse_y = event.x, event.y
        
        sensitivity = max(1, self.window_width * 0.005)
        self.window_width = max(1, self.window_width + dx * sensitivity)
        self.window_center += dy * sensitivity
        self.apply_windowing()
        return "break"
        
    def start_windowing2(self, event):
        self.last_mouse_x = event.x
        self.last_mouse_y = event.y
        return "break"

    def do_windowing2(self, event):
        if self.image_data2 is None: return "break"
        dx = event.x - self.last_mouse_x
        dy = event.y - self.last_mouse_y
        self.last_mouse_x, self.last_mouse_y = event.x, event.y
        
        sensitivity = max(1, self.window_width2 * 0.005)
        self.window_width2 = max(1, self.window_width2 + dx * sensitivity)
        self.window_center2 += dy * sensitivity
        self.apply_windowing()
        return "break"

    def start_pan(self, event):
        self.last_mouse_x = event.x
        self.last_mouse_y = event.y
        return "break"

    def do_pan(self, event):
        if self.image_data is None: return "break"
        self.off_x += event.x - self.last_mouse_x
        self.off_y += event.y - self.last_mouse_y
        self.last_mouse_x, self.last_mouse_y = event.x, event.y
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
        return "break"

    def undo_last_action(self, event=None):
        if not self.history_stack: 
            self.root.bell()
            return
        action = self.history_stack.pop()
        
        if action == "signal" and self.signal_rois: 
            self.redo_stack.append(('signal', self.signal_rois.pop()))
        elif action == "noise" and self.noise_roi: 
            self.redo_stack.append(('noise', self.noise_roi))
            self.noise_roi = None
        elif action == "caliper" and self.calipers: 
            self.redo_stack.append(('caliper', self.calipers.pop()))
        elif action == "profile" and self.profiles: 
            self.redo_stack.append(('profile', self.profiles.pop()))
            
        self.update_undo_redo_state()
        self.rebuild_mask_overlay()
        self.calculate_and_show_results()
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def redo_last_action(self, event=None):
        if not self.redo_stack: 
            self.root.bell()
            return
        action, data = self.redo_stack.pop()
        
        if action == "signal": self.signal_rois.append(data)
        elif action == "noise": self.noise_roi = data
        elif action == "caliper": self.calipers.append(data)
        elif action == "profile": self.profiles.append(data)
            
        self.history_stack.append(action)
        self.update_undo_redo_state()
        self.rebuild_mask_overlay()
        self.calculate_and_show_results()
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def on_escape(self, event=None):
        if self.current_tool_var.get() == "move" and self.active_move_target is not None:
            tgt = self.active_move_target
            if tgt['type'] == 'signal': self.signal_rois[tgt['idx']]['mask'] = tgt['orig']
            elif tgt['type'] == 'noise': self.noise_roi['mask'] = tgt['orig']
            elif tgt['type'] == 'caliper': self.calipers[tgt['idx']] = tgt['orig']
            elif tgt['type'] == 'profile': 
                self.profiles[tgt['idx']] = tgt['orig']
                self._update_profile_intensities(self.profiles[tgt['idx']])
            
            self.drag_start = None
            self.active_move_target = None
            self.is_pulsating = False
            self.rebuild_mask_overlay()
            self.calculate_and_show_results()
            if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
                self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
            return
            
        if self.drag_start is not None or self.freehand_pts:
            self.drag_start = None
            self.drag_current = None
            self.active_move_target = None
            self.freehand_pts = []
            if hasattr(self, 'canvas') and self.canvas.winfo_width() > 10:
                self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
        else:
            self.root.bell()

    def reset_rois(self):
        if self.image_data is None: return
        self.signal_rois = []
        self.noise_roi = None
        self.calipers = []
        self.profiles = []
        self.history_stack = []
        self.redo_stack = []
        self.current_results = None
        self.start_keyframe_idx = None
        self.end_keyframe_idx = None
        self.target_mode_var.set("signal")
        self.mask_overlay = Image.new("RGBA", (self.orig_w, self.orig_h), (0,0,0,0))
        if self.split_mode: self.mask_overlay2 = Image.new("RGBA", (self.orig_w, self.orig_h), (0,0,0,0))
        
        for widget in self.results_inner_frame.winfo_children(): widget.destroy()
            
        self.update_task_text()
        self.update_undo_redo_state()
        self.view_menu.entryconfig("Show ROI Histograms", state=tk.DISABLED)
        self.file_menu.entryconfig("Save Screenshot", state=tk.DISABLED)
        self.file_menu.entryconfig("Save Screenshot As...", state=tk.DISABLED)
        self.file_menu.entryconfig("Export Full PDF Report", state=tk.DISABLED)
        self.file_menu.entryconfig("Log Results to CSV", state=tk.DISABLED)
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def on_resize(self, event):
        if event.widget == self.canvas:
            cw, ch = event.width, event.height
            if cw < 10 or ch < 10: return

            if self.image_data is not None and self.orig_w > 0 and self.orig_h > 0:
                if self.last_cw > 0 and self.last_ch > 0:
                    old_base_scale = min(self.last_cw / self.orig_w, self.last_ch / self.orig_h)
                    new_base_scale = min(cw / self.orig_w, ch / self.orig_h)
                    
                    if old_base_scale > 0:
                        user_zoom = self.actual_scale / old_base_scale
                        old_actual_scale = self.actual_scale
                        self.actual_scale = new_base_scale * user_zoom
                        
                        img_center_x = (self.last_cw / 2 - self.off_x) / old_actual_scale
                        img_center_y = (self.last_ch / 2 - self.off_y) / old_actual_scale
                        
                        self.off_x = cw / 2 - img_center_x * self.actual_scale
                        self.off_y = ch / 2 - img_center_y * self.actual_scale

            self.last_cw = cw
            self.last_ch = ch
            if self.image_data is not None:
                self.redraw(cw, ch)

    def _draw_loupe(self, cx, cy, canvas_target, base_img_target):
        zoom = self.loupe_zoom_var.get()
        lens_size = 200 
        src_size = lens_size / (self.actual_scale * zoom)
        half_src = src_size / 2.0
        
        left, top = int(round(cx - half_src)), int(round(cy - half_src))
        right, bottom = left + int(round(src_size)), top + int(round(src_size))
        
        crop = base_img_target.crop((left, top, right, bottom))
        if crop.width > 0 and crop.height > 0:
            zoomed = crop.resize((lens_size, lens_size), Image.NEAREST).convert("RGBA")
            mask = Image.new("L", (lens_size, lens_size), 0)
            draw = ImageDraw.Draw(mask)
            draw.ellipse((0, 0, lens_size, lens_size), fill=255)
            zoomed.putalpha(mask)
            
            tk_img = ImageTk.PhotoImage(zoomed)
            if canvas_target == self.canvas: self.loupe_tk_img = tk_img
            else: self.loupe_tk_img2 = tk_img
            
            screen_x, screen_y = self.off_x + cx * self.actual_scale, self.off_y + cy * self.actual_scale
            canvas_target.create_image(screen_x, screen_y, image=tk_img, anchor="center")
            canvas_target.create_oval(screen_x - lens_size/2, screen_y - lens_size/2, screen_x + lens_size/2, screen_y + lens_size/2, outline="white", width=3)

    def _render_canvas(self, canvas, base_pil, overlay, is_second=False):
        canvas.delete("all")
        display_img = base_pil.convert("RGBA")
        if overlay: display_img = Image.alpha_composite(display_img, overlay)
            
        new_w, new_h = int(self.orig_w * self.actual_scale), int(self.orig_h * self.actual_scale)
        scaled_img = display_img.resize((new_w, new_h), Image.NEAREST)
        tk_img = ImageTk.PhotoImage(scaled_img)
        
        if is_second: self.tk_image2 = tk_img
        else: self.tk_image = tk_img
            
        canvas.create_image(self.off_x, self.off_y, anchor="nw", image=tk_img)

        tool = self.current_tool_var.get()
        if self.drag_start and self.drag_current and tool not in ["move", "delete"]:
            x1 = self.off_x + self.drag_start[0] * self.actual_scale
            y1 = self.off_y + self.drag_start[1] * self.actual_scale
            x2 = self.off_x + self.drag_current[0] * self.actual_scale
            y2 = self.off_y + self.drag_current[1] * self.actual_scale
            
            color = "blue" if self.target_mode_var.get() == "noise" else "red"
            if tool == "caliper": color = "yellow"
            if tool == "profile": color = "magenta"
            
            if tool == "rect": canvas.create_rectangle(x1, y1, x2, y2, outline=color, width=1)
            elif tool == "ellipse": canvas.create_oval(x1, y1, x2, y2, outline=color, width=1)
            elif tool in ["caliper", "profile"]: canvas.create_line(x1, y1, x2, y2, fill=color, width=1, dash=(4,2))
            if tool == "loupe": self._draw_loupe(self.drag_current[0], self.drag_current[1], canvas, base_pil)
            
        if self.freehand_pts and len(self.freehand_pts) > 1 and tool == "freehand":
            color = "blue" if self.target_mode_var.get() == "noise" else "red"
            scaled_pts = [(self.off_x + px*self.actual_scale, self.off_y + py*self.actual_scale) for px, py in self.freehand_pts]
            canvas.create_line(scaled_pts, fill=color, width=1)

        if self.show_roi_numbers_var.get():
            active_hex_colors = self.ext_hex_colors if self.extended_colors_var.get() else self.hex_colors
            for i, roi in enumerate(self.signal_rois):
                y_idx, x_idx = np.where(roi['mask'])
                if len(x_idx) > 0:
                    cx, cy = np.mean(x_idx), np.mean(y_idx)
                    screen_x = self.off_x + cx * self.actual_scale
                    screen_y = self.off_y + cy * self.actual_scale
                    col = active_hex_colors[i % len(active_hex_colors)]
                    
                    if self.is_pulsating and self.active_move_target and self.active_move_target['type'] == 'signal' and self.active_move_target['idx'] == i:
                        f = (math.sin(self.pulse_val) + 1) / 2
                        r = int(int(col[1:3], 16) * (1-f) + 255 * f)
                        g = int(int(col[3:5], 16) * (1-f) + 255 * f)
                        b = int(int(col[5:7], 16) * (1-f) + 255 * f)
                        col = f"#{r:02x}{g:02x}{b:02x}"
                        
                    canvas.create_text(screen_x, screen_y, text=str(i + 1), fill=col, font=("Arial", 12, "bold"))

        for i, cal in enumerate(self.calipers):
            cx1, cy1 = self.off_x + cal['x1'] * self.actual_scale, self.off_y + cal['y1'] * self.actual_scale
            cx2, cy2 = self.off_x + cal['x2'] * self.actual_scale, self.off_y + cal['y2'] * self.actual_scale
            c_color = "yellow"
            if self.is_pulsating and self.active_move_target and self.active_move_target['type'] == 'caliper' and self.active_move_target['idx'] == i:
                c_color = "white" if math.sin(self.pulse_val) > 0 else "yellow"
            canvas.create_line(cx1, cy1, cx2, cy2, fill=c_color, width=2 if c_color=="white" else 1)
            canvas.create_text((cx1+cx2)/2, (cy1+cy2)/2, text=f"{cal['dist']:.2f} mm", fill="lightblue" if c_color=="white" else "blue", font=("Arial", 12, "bold"))

        for i, p in enumerate(self.profiles):
            cx1, cy1 = self.off_x + p['x1'] * self.actual_scale, self.off_y + p['y1'] * self.actual_scale
            cx2, cy2 = self.off_x + p['x2'] * self.actual_scale, self.off_y + p['y2'] * self.actual_scale
            p_color = "magenta"
            if self.is_pulsating and self.active_move_target and self.active_move_target['type'] == 'profile' and self.active_move_target['idx'] == i:
                p_color = "white" if math.sin(self.pulse_val) > 0 else "magenta"
            canvas.create_line(cx1, cy1, cx2, cy2, fill=p_color, width=2 if p_color=="white" else 1)

        hud = canvas.create_text(10, 10, text=self.hud_str, fill="yellow", font=("Arial", 14, "bold"), anchor="nw")
        if is_second: self.hud_item2 = hud
        else: self.hud_item = hud
        
        tool_names = {
            "rect": "Rectangle ROI",
            "ellipse": "Ellipse ROI",
            "freehand": "Freehand ROI",
            "caliper": "Caliper Tool",
            "profile": "Profile Line Tool",
            "loupe": f"Loupe Tool ({self.loupe_zoom_var.get():.1f}x)",
            "move": "Move Mode",
            "delete": "Delete Mode"
        }
        canvas.create_text(canvas.winfo_width() - 10, 10, text=tool_names.get(tool, tool.capitalize()), fill="yellow", font=("Arial", 14, "bold"), anchor="ne")

    def redraw(self, cw, ch):
        if cw < 10 or ch < 10 or self.base_pil_image is None: return
        self._render_canvas(self.canvas, self.base_pil_image, self.mask_overlay, False)
        if self.split_mode and self.base_pil_image2:
            self._render_canvas(self.canvas2, self.base_pil_image2, self.mask_overlay2, True)

    def _get_outline_mask(self, mask):
        eroded = mask.copy()
        eroded[1:] &= mask[:-1]
        eroded[:-1] &= mask[1:]
        eroded[:, 1:] &= mask[:, :-1]
        eroded[:, :-1] &= mask[:, 1:]
        return mask ^ eroded

    def rebuild_mask_overlay(self):
        rgba = np.zeros((self.orig_h, self.orig_w, 4), dtype=np.uint8)
        active_colors = self.ext_sig_colors if self.extended_colors_var.get() else self.sig_colors
        
        pulse_f = (math.sin(self.pulse_val) + 1) / 2 if self.is_pulsating else 0
        
        for i, roi in enumerate(self.signal_rois):
            outline = self._get_outline_mask(roi['mask'])
            c = list(active_colors[i % len(active_colors)])
            
            if self.is_pulsating and self.active_move_target and self.active_move_target['type'] == 'signal' and self.active_move_target['idx'] == i:
                c[0] = int(c[0] * (1-pulse_f) + 255 * pulse_f)
                c[1] = int(c[1] * (1-pulse_f) + 255 * pulse_f)
                c[2] = int(c[2] * (1-pulse_f) + 255 * pulse_f)
                
            rgba[outline] = tuple(c)
            
        if self.noise_roi:
            outline = self._get_outline_mask(self.noise_roi['mask'])
            c = list(self.noise_color)
            if self.is_pulsating and self.active_move_target and self.active_move_target['type'] == 'noise':
                c[0] = int(c[0] * (1-pulse_f) + 255 * pulse_f)
                c[1] = int(c[1] * (1-pulse_f) + 255 * pulse_f)
                c[2] = int(c[2] * (1-pulse_f) + 255 * pulse_f)
            rgba[outline] = tuple(c)
            
        self.mask_overlay = Image.fromarray(rgba, "RGBA")
        if self.split_mode: self.mask_overlay2 = Image.fromarray(rgba, "RGBA")

    def get_physical_distance(self, x1, y1, x2, y2):
        if self.nifti_mode:
            dx = (x2 - x1) * float(self.nifti_spacing[0])
            dy = (y2 - y1) * float(self.nifti_spacing[1])
            return math.hypot(dx, dy)
        try:
            spacing = self.dicom_dataset.PixelSpacing
            dx = (x2 - x1) * float(spacing[0])
            dy = (y2 - y1) * float(spacing[1])
            return math.hypot(dx, dy)
        except: return math.hypot(x2-x1, y2-y1) 

    def _point_line_dist(self, px, py, x1, y1, x2, y2):
        l2 = (x2-x1)**2 + (y2-y1)**2
        if l2 == 0: return math.hypot(px-x1, py-y1)
        t = max(0, min(1, ((px-x1)*(x2-x1) + (py-y1)*(y2-y1)) / l2))
        proj_x = x1 + t * (x2-x1)
        proj_y = y1 + t * (y2-y1)
        return math.hypot(px-proj_x, py-proj_y)

    def on_mouse_press(self, event):
        if event.state & 0x0001 or event.state & 0x0010 or event.state & 0x0040: return
        if self.image_data is None: return

        cx, cy = event.x, event.y
        orig_x, orig_y = (cx - self.off_x) / self.actual_scale, (cy - self.off_y) / self.actual_scale
        
        t_var = self.current_tool_var.get()
        
        if t_var == "delete":
            ix, iy = int(orig_x), int(orig_y)
            deleted = False
            for i, cal in enumerate(self.calipers):
                if self._point_line_dist(orig_x, orig_y, cal['x1'], cal['y1'], cal['x2'], cal['y2']) < 5:
                    self.calipers.pop(i)
                    deleted = True
                    break
            if not deleted:
                for i, p in enumerate(self.profiles):
                    if self._point_line_dist(orig_x, orig_y, p['x1'], p['y1'], p['x2'], p['y2']) < 5:
                        self.profiles.pop(i)
                        deleted = True
                        break
            if not deleted and self.noise_roi and 0 <= ix < self.orig_w and 0 <= iy < self.orig_h:
                if self.noise_roi['mask'][iy, ix]:
                    self.noise_roi = None
                    deleted = True
            if not deleted and 0 <= ix < self.orig_w and 0 <= iy < self.orig_h:
                for i, sig in enumerate(self.signal_rois):
                    if sig['mask'][iy, ix]:
                        self.signal_rois.pop(i)
                        deleted = True
                        break
            if deleted:
                self.history_stack.clear()
                self.redo_stack.clear()
                self.update_undo_redo_state()
                self.rebuild_mask_overlay()
                self.calculate_and_show_results()
                self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
            return

        if t_var == "move":
            self.drag_start = (orig_x, orig_y)
            self.active_move_target = None
            ix, iy = int(orig_x), int(orig_y)
            
            if 0 <= ix < self.orig_w and 0 <= iy < self.orig_h:
                for i, cal in enumerate(self.calipers):
                    if self._point_line_dist(orig_x, orig_y, cal['x1'], cal['y1'], cal['x2'], cal['y2']) < 5:
                        self.active_move_target = {'type': 'caliper', 'idx': i, 'orig': cal.copy()}
                        break
                if not self.active_move_target:
                    for i, p in enumerate(self.profiles):
                        if self._point_line_dist(orig_x, orig_y, p['x1'], p['y1'], p['x2'], p['y2']) < 5:
                            self.active_move_target = {'type': 'profile', 'idx': i, 'orig': p.copy()}
                            break
                if not self.active_move_target and self.noise_roi and self.noise_roi['mask'][iy, ix]:
                    self.active_move_target = {'type': 'noise', 'orig': self.noise_roi['mask'].copy()}
                if not self.active_move_target:
                    for i, sig in enumerate(self.signal_rois):
                        if sig['mask'][iy, ix]:
                            self.active_move_target = {'type': 'signal', 'idx': i, 'orig': sig['mask'].copy()}
                            break
                            
            if self.active_move_target:
                self.is_pulsating = True
                self.pulse_val = 0.0
                self._pulse_tick()
            return

        self.drag_start = (orig_x, orig_y)
        if t_var == "freehand":
            self.freehand_pts = [(orig_x, orig_y)]
        else:
            self.drag_current = (orig_x, orig_y)
            
        if t_var == "loupe":
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def _update_profile_intensities(self, prof):
        x1, y1, x2, y2 = prof['x1'], prof['y1'], prof['x2'], prof['y2']
        n = int(math.hypot(x2-x1, y2-y1))
        if n > 2:
            x_c = np.clip(np.linspace(x1, x2, n), 0, self.orig_w - 1).astype(int)
            y_c = np.clip(np.linspace(y1, y2, n), 0, self.orig_h - 1).astype(int)
            prof['intensities'] = self.image_data[y_c, x_c]
            prof['intensities2'] = self.image_data2[y_c, x_c] if self.split_mode and self.image_data2 is not None else []

    def on_mouse_drag(self, event):
        if not self.drag_start: return
        orig_x, orig_y = (event.x - self.off_x) / self.actual_scale, (event.y - self.off_y) / self.actual_scale
        
        if self.current_tool_var.get() == "move" and self.active_move_target:
            dx = orig_x - self.drag_start[0]
            dy = orig_y - self.drag_start[1]
            tgt = self.active_move_target
            
            if tgt['type'] in ['signal', 'noise']:
                new_mask = self._shift_mask(tgt['orig'], int(round(dx)), int(round(dy)))
                if tgt['type'] == 'signal': self.signal_rois[tgt['idx']]['mask'] = new_mask
                else: self.noise_roi['mask'] = new_mask
            elif tgt['type'] == 'caliper':
                self.calipers[tgt['idx']]['x1'] = tgt['orig']['x1'] + dx
                self.calipers[tgt['idx']]['y1'] = tgt['orig']['y1'] + dy
                self.calipers[tgt['idx']]['x2'] = tgt['orig']['x2'] + dx
                self.calipers[tgt['idx']]['y2'] = tgt['orig']['y2'] + dy
            elif tgt['type'] == 'profile':
                p = self.profiles[tgt['idx']]
                p['x1'] = tgt['orig']['x1'] + dx
                p['y1'] = tgt['orig']['y1'] + dy
                p['x2'] = tgt['orig']['x2'] + dx
                p['y2'] = tgt['orig']['y2'] + dy
                self._update_profile_intensities(p)
                
            self.calculate_and_show_results()
            return
            
        if self.current_tool_var.get() == "freehand":
            self.freehand_pts.append((orig_x, orig_y))
        else:
            self.drag_current = (orig_x, orig_y)
            
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def draw_profile_graph(self, prof):
        top = tk.Toplevel(self.root)
        top.title("Intensity Profile")
        top.geometry("600x400")
        
        bg_col = "#1E1E1E" if self.dark_mode_var.get() else "white"
        text_col = "white" if self.dark_mode_var.get() else "black"
        top.configure(bg=bg_col)
        
        canvas = tk.Canvas(top, bg=bg_col, highlightthickness=0)
        canvas.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        data1 = prof['intensities']
        data2 = prof.get('intensities2', [])
        
        if len(data1) < 2: return
        
        min_val, max_val = np.min(data1), np.max(data1)
        if len(data2) > 0:
            min_val = min(min_val, np.min(data2))
            max_val = max(max_val, np.max(data2))
            
        if max_val == min_val: max_val = min_val + 1
        
        canvas.update_idletasks()
        w, h = canvas.winfo_width(), canvas.winfo_height()
        if w < 10: w, h = 560, 360
        
        canvas.create_text(10, 10, anchor="nw", text=f"Profile Line | Length: {prof['dist']:.2f} mm", fill=text_col, font=("Arial", 12, "bold"))
        
        left_pad, right_pad, top_y, bottom_pad = 50, 120, 40, 40
        graph_w = w - left_pad - right_pad
        graph_h = h - top_y - bottom_pad
        
        leg_w, leg_h = 100, 40 if len(data2) == 0 else 60
        leg_x = w - right_pad + 10
        leg_y = top_y
        
        canvas.create_rectangle(leg_x, leg_y, leg_x + leg_w, leg_y + leg_h, fill=bg_col, outline=text_col)
        canvas.create_line(leg_x + 10, leg_y + 20, leg_x + 40, leg_y + 20, fill="magenta", width=2)
        canvas.create_text(leg_x + 45, leg_y + 20, text="Img 1", fill=text_col, anchor="w", font=("Arial", 10))
        
        pts1 = []
        for i, val in enumerate(data1):
            x = left_pad + (i / (len(data1) - 1)) * graph_w
            y = top_y + graph_h - ((val - min_val) / (max_val - min_val)) * graph_h
            pts1.append((x, y))
        canvas.create_line(pts1, fill="magenta", width=2)
        
        if len(data2) > 0:
            canvas.create_line(leg_x + 10, leg_y + 40, leg_x + 40, leg_y + 40, fill="cyan", width=2, dash=(4,2))
            canvas.create_text(leg_x + 45, leg_y + 40, text="Img 2", fill=text_col, anchor="w", font=("Arial", 10))
            
            pts2 = []
            for i, val in enumerate(data2):
                x = left_pad + (i / (len(data2) - 1)) * graph_w
                y = top_y + graph_h - ((val - min_val) / (max_val - min_val)) * graph_h
                pts2.append((x, y))
            canvas.create_line(pts2, fill="cyan", width=2, dash=(4,2))
            
        canvas.create_line(left_pad, top_y, left_pad, top_y + graph_h, fill=text_col, width=2)
        canvas.create_line(left_pad, top_y + graph_h, left_pad + graph_w, top_y + graph_h, fill=text_col, width=2)

    def on_mouse_release(self, event):
        if not self.drag_start: return
        tool = self.current_tool_var.get()
        
        if tool == "move":
            self.drag_start = None
            self.active_move_target = None
            self.is_pulsating = False
            self.rebuild_mask_overlay()
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
            return
            
        if tool == "loupe":
            self.drag_start = None
            self.drag_current = None
            self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
            return
            
        if tool in ["rect", "ellipse"]:
            if not self.drag_current: return
            x1, y1 = self.drag_start
            x2, y2 = self.drag_current
            if abs(x2-x1) > 2 and abs(y2-y1) > 2: 
                x_min, x_max = int(min(x1, x2)), int(max(x1, x2))
                y_min, y_max = int(min(y1, y2)), int(max(y1, y2))
                mask = np.zeros((self.orig_h, self.orig_w), dtype=bool)
                
                if tool == "rect": mask[y_min:y_max, x_min:x_max] = True
                elif tool == "ellipse":
                    cx, cy, a, b = (x1+x2)/2.0, (y1+y2)/2.0, abs(x2-x1)/2.0, abs(y2-y1)/2.0
                    Y, X = np.ogrid[:self.orig_h, :self.orig_w]
                    mask = ((X - cx)/a)**2 + ((Y - cy)/b)**2 <= 1
                self._save_mask(mask)
                
        elif tool == "freehand":
            if len(self.freehand_pts) > 5:
                mask_img = Image.new('L', (self.orig_w, self.orig_h), 0)
                ImageDraw.Draw(mask_img).polygon(self.freehand_pts, outline=1, fill=1)
                self._save_mask(np.array(mask_img, dtype=bool))
                
        elif tool == "caliper":
            if self.drag_current:
                x1, y1 = self.drag_start
                x2, y2 = self.drag_current
                if math.hypot(x2-x1, y2-y1) > 2:
                    dist = self.get_physical_distance(x1, y1, x2, y2)
                    self.calipers.append({'x1': x1, 'y1': y1, 'x2': x2, 'y2': y2, 'dist': dist})
                    self.history_stack.append('caliper')
                    self.redo_stack.clear()

        elif tool == "profile":
            if self.drag_current:
                x1, y1 = self.drag_start
                x2, y2 = self.drag_current
                dist = self.get_physical_distance(x1, y1, x2, y2)
                prof = {'x1': x1, 'y1': y1, 'x2': x2, 'y2': y2, 'dist': dist, 'intensities': [], 'intensities2': []}
                self._update_profile_intensities(prof)
                self.profiles.append(prof)
                self.history_stack.append('profile')
                self.redo_stack.clear()
                self.draw_profile_graph(prof)

        self.drag_start = None
        self.drag_current = None
        self.freehand_pts = []
        
        self.update_undo_redo_state()
        self.rebuild_mask_overlay()
        self.calculate_and_show_results()
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())

    def on_magic_wand(self, event):
        if self.image_data is None: return "break"
        ix, iy = int((event.x - self.off_x) / self.actual_scale), int((event.y - self.off_y) / self.actual_scale)
        if not (0 <= ix < self.orig_w and 0 <= iy < self.orig_h): return "break"
        
        seed_val = self.image_data[iy, ix]
        tol = max(1.0, self.window_width * 0.05) 
        mask = np.zeros((self.orig_h, self.orig_w), dtype=bool)
        q = deque([(iy, ix)])
        mask[iy, ix] = True
        
        img = self.image_data
        h, w = self.orig_h, self.orig_w
        visited_count = 0
        max_pixels = (h * w) // 2 
        
        while q and visited_count < max_pixels:
            y, x = q.popleft()
            visited_count += 1
            if y > 0 and not mask[y-1, x] and abs(img[y-1, x] - seed_val) <= tol: mask[y-1, x] = True; q.append((y-1, x))
            if y < h-1 and not mask[y+1, x] and abs(img[y+1, x] - seed_val) <= tol: mask[y+1, x] = True; q.append((y+1, x))
            if x > 0 and not mask[y, x-1] and abs(img[y, x-1] - seed_val) <= tol: mask[y, x-1] = True; q.append((y, x-1))
            if x < w-1 and not mask[y, x+1] and abs(img[y, x+1] - seed_val) <= tol: mask[y, x+1] = True; q.append((y, x+1))

        self._save_mask(mask)
        self.rebuild_mask_overlay()
        self.calculate_and_show_results()
        self.redraw(self.canvas.winfo_width(), self.canvas.winfo_height())
        return "break"

    def _save_mask(self, mask):
        self.redo_stack.clear()
        if self.target_mode_var.get() == "signal": 
            self.signal_rois.append({'mask': mask})
            self.history_stack.append('signal')
            
            if len(self.signal_rois) > 5 and not self.auto_features_triggered:
                self.show_roi_numbers_var.set(True)
                self.extended_colors_var.set(True)
                self.auto_features_triggered = True
        else: 
            self.noise_roi = {'mask': mask}
            self.history_stack.append('noise')
            self.target_mode_var.set("signal") 
            self.update_task_text()
        self.update_undo_redo_state()

    def get_physical_area_from_mask(self, mask):
        pixel_count = np.sum(mask)
        if self.nifti_mode:
            return pixel_count, pixel_count * float(self.nifti_spacing[0]) * float(self.nifti_spacing[1])
        try:
            spacing = self.dicom_dataset.PixelSpacing
            return pixel_count, pixel_count * float(spacing[0]) * float(spacing[1])
        except: return pixel_count, None

    def calculate_and_show_results(self):
        res = []
        n_mean1, n_std1, n_mean2, n_std2 = None, None, None, None
        
        if self.noise_roi:
            px, mm2 = self.get_physical_area_from_mask(self.noise_roi['mask'])
            pixels1 = self.image_data[self.noise_roi['mask']]
            n_mean1, n_std1 = (np.mean(pixels1), np.std(pixels1)) if len(pixels1) > 0 else (None, None)
            
            if self.split_mode and self.image_data2 is not None:
                pixels2 = self.image_data2[self.noise_roi['mask']]
                n_mean2, n_std2 = (np.mean(pixels2), np.std(pixels2)) if len(pixels2) > 0 else (None, None)
                
            res.append({'type': 'Noise', 'px': px, 'mm2': mm2, 'm1': n_mean1, 's1': n_std1, 'snr1': None, 'm2': n_mean2, 's2': n_std2, 'snr2': None})

        for i, s in enumerate(self.signal_rois):
            px, mm2 = self.get_physical_area_from_mask(s['mask'])
            pixels1 = self.image_data[s['mask']]
            m1, s1 = (np.mean(pixels1), np.std(pixels1)) if len(pixels1) > 0 else (None, None)
            
	    # Rayleigh-corrected SNR calculation using noise standard deviation
            snr1 = (m1 * 0.655 / n_std1) if (m1 is not None and n_std1 and n_std1 != 0) else None            


            m2, s2, snr2 = None, None, None
            if self.split_mode and self.image_data2 is not None:
                pixels2 = self.image_data2[s['mask']]
                m2, s2 = (np.mean(pixels2), np.std(pixels2)) if len(pixels2) > 0 else (None, None)
                snr2 = (m2 * 0.655 / n_std2) if (m2 is not None and n_std2 and n_std2 != 0) else None
                
            res.append({'type': f'Signal {i+1}', 'px': px, 'mm2': mm2, 'm1': m1, 's1': s1, 'snr1': snr1, 'm2': m2, 's2': s2, 'snr2': snr2})

        self.current_results = res
        self.update_task_text()
        
        if res or self.calipers or self.profiles:
            self.file_menu.entryconfig("Save Screenshot", state=tk.NORMAL)
            self.file_menu.entryconfig("Save Screenshot As...", state=tk.NORMAL)
            self.file_menu.entryconfig("Export Full PDF Report", state=tk.NORMAL)
        else:
            self.file_menu.entryconfig("Save Screenshot", state=tk.DISABLED)
            self.file_menu.entryconfig("Save Screenshot As...", state=tk.DISABLED)
            self.file_menu.entryconfig("Export Full PDF Report", state=tk.DISABLED)

        if res:
            self.view_menu.entryconfig("Show ROI Histograms", state=tk.NORMAL)
            self.file_menu.entryconfig("Log Results to CSV", state=tk.NORMAL)
        else:
            self.view_menu.entryconfig("Show ROI Histograms", state=tk.DISABLED)
            self.file_menu.entryconfig("Log Results to CSV", state=tk.DISABLED)

        self._build_text_output()

    def _build_text_output(self):
        for widget in self.results_inner_frame.winfo_children(): widget.destroy()
        if not self.current_results: return

        bg_col = "#1E1E1E" if self.dark_mode_var.get() else "white"
        active_hex_colors = self.ext_hex_colors if self.extended_colors_var.get() else self.hex_colors

        for r in self.current_results:
            color = self.noise_hex if r['type'] == 'Noise' else active_hex_colors[(int(r['type'].split()[1]) - 1) % len(active_hex_colors)]
            area_txt = f"{r['mm2']:.1f} mm² ({r['px']} px)" if r['mm2'] else f"{r['px']} px"
            
            if not self.split_mode:
                snr_txt = f"  |  SNR: {r['snr1']:.2f}" if r['snr1'] else ""
                std_txt = f"  |  Std: {r['s1']:.2f}" if self.show_std_var.get() and r['s1'] else ""
                text = f"▶ {r['type']}:\n    Mean: {r['m1']:.2f}{std_txt}{snr_txt}\n    Area: {area_txt}\n"
            else:
                s1_txt = f"  |  Std: {r['s1']:.2f}" if self.show_std_var.get() and r['s1'] else ""
                snr1_txt = f"  |  SNR: {r['snr1']:.2f}" if r['snr1'] else ""
                s2_txt = f"  |  Std: {r['s2']:.2f}" if self.show_std_var.get() and r['s2'] else ""
                snr2_txt = f"  |  SNR: {r['snr2']:.2f}" if r['snr2'] else ""
                
                m1_safe = r['m1'] if r['m1'] is not None else 0
                m2_safe = r['m2'] if r['m2'] is not None else 0
                
                text = f"▶ {r['type']}:\n    Img 1 Mean: {m1_safe:.2f}{s1_txt}{snr1_txt}\n    Img 2 Mean: {m2_safe:.2f}{s2_txt}{snr2_txt}\n    Area: {area_txt}\n"
                
            lbl = tk.Label(self.results_inner_frame, text=text, font=("Arial", 14, "bold"), bg=bg_col, fg=color, justify="left")
            lbl.pack(anchor="nw", pady=2)
            lbl.bind("<MouseWheel>", self._on_results_scroll)
            
        if self.show_cnr_var.get() and self.noise_roi and len(self.signal_rois) >= 2:
            n_res = next((x for x in self.current_results if x['type'] == 'Noise'), None)
            if n_res and n_res['s1'] and n_res['s1'] > 0:
                cnr_lines = ["\n▶ CNR Analysis (Img 1):"]
                for i in range(len(self.signal_rois)):
                    for j in range(i+1, len(self.signal_rois)):
                        m1 = next((x['m1'] for x in self.current_results if x['type'] == f'Signal {i+1}'), 0)
                        m2 = next((x['m1'] for x in self.current_results if x['type'] == f'Signal {j+1}'), 0)
                        cnr_val = abs(m1 - m2) / n_res['s1']
                        cnr_lines.append(f"    Sig {i+1} vs Sig {j+1}: {cnr_val:.2f}")
                
                if self.split_mode and n_res['s2'] and n_res['s2'] > 0:
                    cnr_lines.append("\n▶ CNR Analysis (Img 2):")
                    for i in range(len(self.signal_rois)):
                        for j in range(i+1, len(self.signal_rois)):
                            m1 = next((x['m2'] for x in self.current_results if x['type'] == f'Signal {i+1}'), 0)
                            m2 = next((x['m2'] for x in self.current_results if x['type'] == f'Signal {j+1}'), 0)
                            cnr_val = abs(m1 - m2) / n_res['s2']
                            cnr_lines.append(f"    Sig {i+1} vs Sig {j+1}: {cnr_val:.2f}")

                cnr_lbl = tk.Label(self.results_inner_frame, text="\n".join(cnr_lines), font=("Arial", 14, "bold"), bg=bg_col, fg="orange", justify="left")
                cnr_lbl.pack(anchor="nw", pady=2)
                cnr_lbl.bind("<MouseWheel>", self._on_results_scroll)

    def log_to_csv(self):
        if not self.current_results or not self.current_file_path: return
        target_dir = self._get_target_dir("csv")
        csv_path = os.path.join(target_dir, "snr_log.csv")
        try:
            file_exists = os.path.isfile(csv_path)
            with open(csv_path, 'a', newline='') as csvfile:
                fieldnames = ['Filename', 'ROI Name', 'Type', 'Area (px)', 'Area (mm2)', 'Mean 1', 'Std 1', 'Noise Base 1', 'SNR 1']
                if self.split_mode:
                    fieldnames.extend(['Filename 2', 'Mean 2', 'Std 2', 'Noise Base 2', 'SNR 2'])
                    
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                if not file_exists: writer.writeheader()
                
                n_m1 = next((r['m1'] for r in self.current_results if r['type'] == 'Noise'), 'N/A')
                n_m2 = next((r['m2'] for r in self.current_results if r['type'] == 'Noise'), 'N/A') if self.split_mode else 'N/A'
                
                for r in self.current_results:
                    row = {
                        'Filename': os.path.basename(self.current_file_path),
                        'ROI Name': r['type'],
                        'Type': 'Signal' if 'Signal' in r['type'] else 'Noise',
                        'Area (px)': r['px'],
                        'Area (mm2)': round(r['mm2'], 2) if r['mm2'] else 'N/A',
                        'Mean 1': round(r['m1'], 4) if r['m1'] else 'N/A',
                        'Std 1': round(r['s1'], 4) if r['s1'] else 'N/A',
                        'Noise Base 1': round(n_m1, 4) if 'Signal' in r['type'] and n_m1 != 'N/A' else 'N/A',
                        'SNR 1': round(r['snr1'], 4) if r['snr1'] else 'N/A'
                    }
                    if self.split_mode:
                        row.update({
                            'Filename 2': os.path.basename(self.current_file_path2) if self.current_file_path2 else 'N/A',
                            'Mean 2': round(r['m2'], 4) if r['m2'] else 'N/A',
                            'Std 2': round(r['s2'], 4) if r['s2'] else 'N/A',
                            'Noise Base 2': round(n_m2, 4) if 'Signal' in r['type'] and n_m2 != 'N/A' else 'N/A',
                            'SNR 2': round(r['snr2'], 4) if r['snr2'] else 'N/A'
                        })
                    writer.writerow(row)
                    
            orig_txt = self.top_label.cget("text")
            self.top_label.config(text="✅ Logged to snr_log.csv!", bg="#d4edda", fg="black")
            self.root.after(2000, lambda: self.top_label.config(text=orig_txt, bg="white", fg="black"))
        except Exception as e: messagebox.showerror("Error", f"Failed to log to CSV:\n{e}")

    def _generate_export_image(self):
        th = self.init_h
        bg_c = "#1E1E1E" if self.dark_mode_var.get() else "white"
        text_c = "white" if self.dark_mode_var.get() else "black"
        active_hex_colors = self.ext_hex_colors if self.extended_colors_var.get() else self.hex_colors
        
        draw_mock = ImageDraw.Draw(Image.new("RGB", (1,1)))
        try: font_top = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 20)
        except: font_top = ImageFont.load_default()
        try: font_res = ImageFont.truetype("/Library/Fonts/Arial Bold.ttf", 18)
        except: font_res = ImageFont.load_default()

        lbl1_text = self.top_label.cget("text")
        bbox1 = draw_mock.textbbox((0,0), lbl1_text, font=font_top)
        lbl1_w = bbox1[2] - bbox1[0]
        
        lbl2_w = 0
        if self.split_mode:
            lbl2_text = self.top_label2.cget("text")
            bbox2 = draw_mock.textbbox((0,0), lbl2_text, font=font_top)
            lbl2_w = bbox2[2] - bbox2[0]

        max_h = th if not self.split_mode else (th / 2.0) - 40
        export_scale = min(max_h / self.orig_w, max_h / self.orig_h)
        new_w, new_h = int(self.orig_w * export_scale), int(self.orig_h * export_scale)
        
        left_panel_w = max(new_w, lbl1_w, lbl2_w) + 40 
        
        text_blocks = []
        for r in self.current_results:
            area_txt = f"{r['mm2']:.1f} mm² ({r['px']} px)" if r['mm2'] else f"{r['px']} px"
            if not self.split_mode:
                snr_txt = f"  |  SNR: {r['snr1']:.2f}" if r['snr1'] else ""
                std_txt = f"  |  Std: {r['s1']:.2f}" if self.show_std_var.get() and r['s1'] else ""
                text = f"{r['type']}:\n    Mean: {r['m1']:.2f}{std_txt}{snr_txt}\n    Area: {area_txt}\n"
            else:
                s1_txt = f"  |  Std: {r['s1']:.2f}" if self.show_std_var.get() and r['s1'] else ""
                snr1_txt = f"  |  SNR: {r['snr1']:.2f}" if r['snr1'] else ""
                s2_txt = f"  |  Std: {r['s2']:.2f}" if self.show_std_var.get() and r['s2'] else ""
                snr2_txt = f"  |  SNR: {r['snr2']:.2f}" if r['snr2'] else ""
                m1_safe = r['m1'] if r['m1'] is not None else 0
                m2_safe = r['m2'] if r['m2'] is not None else 0
                text = f"{r['type']}:\n    Img 1 Mean: {m1_safe:.2f}{s1_txt}{snr1_txt}\n    Img 2 Mean: {m2_safe:.2f}{s2_txt}{snr2_txt}\n    Area: {area_txt}\n"
            
            color = self.noise_hex if r['type'] == 'Noise' else active_hex_colors[(int(r['type'].split()[1]) - 1) % len(active_hex_colors)]
            text_blocks.append({"text": text, "color": color})
            
        if self.show_cnr_var.get() and self.noise_roi and len(self.signal_rois) >= 2:
            n_res = next((x for x in self.current_results if x['type'] == 'Noise'), None)
            if n_res and n_res['s1'] and n_res['s1'] > 0:
                cnr_lines = ["CNR Analysis (Img 1):"]
                for i in range(len(self.signal_rois)):
                    for j in range(i+1, len(self.signal_rois)):
                        m1 = next((x['m1'] for x in self.current_results if x['type'] == f'Signal {i+1}'), 0)
                        m2 = next((x['m1'] for x in self.current_results if x['type'] == f'Signal {j+1}'), 0)
                        cnr_val = abs(m1 - m2) / n_res['s1']
                        cnr_lines.append(f"    Sig {i+1} vs Sig {j+1}: {cnr_val:.2f}")
                text_blocks.append({"text": "\n".join(cnr_lines), "color": "orange"})
                
                if self.split_mode and n_res['s2'] and n_res['s2'] > 0:
                    cnr_lines2 = ["CNR Analysis (Img 2):"]
                    for i in range(len(self.signal_rois)):
                        for j in range(i+1, len(self.signal_rois)):
                            m1 = next((x['m2'] for x in self.current_results if x['type'] == f'Signal {i+1}'), 0)
                            m2 = next((x['m2'] for x in self.current_results if x['type'] == f'Signal {j+1}'), 0)
                            cnr_val = abs(m1 - m2) / n_res['s2']
                            cnr_lines2.append(f"    Sig {i+1} vs Sig {j+1}: {cnr_val:.2f}")
                    text_blocks.append({"text": "\n".join(cnr_lines2), "color": "orange"})

        right_panel_w = 0
        temp_y = 50
        for tb in text_blocks:
            bbox = draw_mock.textbbox((0,0), tb["text"], font=font_res)
            tw = bbox[2] - bbox[0]
            if tw > right_panel_w: right_panel_w = tw
            temp_y += (bbox[3] - bbox[1]) + 20
        
        right_panel_w += 80 
        total_w = int(left_panel_w + right_panel_w)
        
        off_y1 = 50
        off_x1 = int((left_panel_w - new_w) / 2) 
        
        if self.split_mode:
            off_y2 = off_y1 + new_h + 60
            off_x2 = int((left_panel_w - new_w) / 2)
            final_img_h = off_y2 + new_h + 20
        else:
            final_img_h = off_y1 + new_h + 20
            
        final_h = int(max(final_img_h, temp_y + 30))
        export_img = Image.new("RGB", (total_w, final_h), bg_c)
        draw = ImageDraw.Draw(export_img)
        
        draw.text(((left_panel_w - lbl1_w)/2, off_y1 - 30), lbl1_text, fill=text_c, font=font_top)
        if self.split_mode:
            draw.text(((left_panel_w - lbl2_w)/2, off_y2 - 30), lbl2_text, fill=text_c, font=font_top)
        
        img_exp1 = self.base_pil_image.convert("RGBA")
        if self.mask_overlay: img_exp1 = Image.alpha_composite(img_exp1, self.mask_overlay)
        export_img.paste(img_exp1.resize((new_w, new_h), Image.NEAREST).convert("RGB"), (off_x1, off_y1))
        
        if self.split_mode and self.base_pil_image2:
            img_exp2 = self.base_pil_image2.convert("RGBA")
            if self.mask_overlay2: img_exp2 = Image.alpha_composite(img_exp2, self.mask_overlay2)
            export_img.paste(img_exp2.resize((new_w, new_h), Image.NEAREST).convert("RGB"), (off_x2, off_y2))
            
        def draw_overlays(off_x, off_y):
            if self.show_roi_numbers_var.get():
                for i, roi in enumerate(self.signal_rois):
                    y_idx, x_idx = np.where(roi['mask'])
                    if len(x_idx) > 0:
                        cx_exp = off_x + np.mean(x_idx) * export_scale
                        cy_exp = off_y + np.mean(y_idx) * export_scale
                        col = active_hex_colors[i % len(active_hex_colors)]
                        t_bbox = draw.textbbox((0, 0), str(i + 1), font=font_top)
                        draw.text((cx_exp - (t_bbox[2]-t_bbox[0])/2, cy_exp - (t_bbox[3]-t_bbox[1])/2), str(i + 1), fill=col, font=font_top)
            
            for cal in self.calipers:
                cx1, cy1 = off_x + cal['x1'] * export_scale, off_y + cal['y1'] * export_scale
                cx2, cy2 = off_x + cal['x2'] * export_scale, off_y + cal['y2'] * export_scale
                draw.line([cx1, cy1, cx2, cy2], fill="yellow", width=1)
                draw.text(((cx1+cx2)/2, (cy1+cy2)/2), f"{cal['dist']:.2f} mm", fill="lightblue" if self.dark_mode_var.get() else "blue", font=font_top)
                
            for p in self.profiles:
                cx1, cy1 = off_x + p['x1'] * export_scale, off_y + p['y1'] * export_scale
                cx2, cy2 = off_x + p['x2'] * export_scale, off_y + p['y2'] * export_scale
                draw.line([cx1, cy1, cx2, cy2], fill="magenta", width=1)

        draw_overlays(off_x1, off_y1)
        if self.split_mode: draw_overlays(off_x2, off_y2)

        text_start_x = left_panel_w
        draw.line([text_start_x, 0, text_start_x, final_h], fill="#333333" if self.dark_mode_var.get() else "lightgray", width=2)
            
        y_offset = 50
        for tb in text_blocks:
            color = tb["color"]
            text = tb["text"]
            
            if "CNR Analysis" not in text:
                tx, ty, ts = text_start_x + 20, y_offset + 4, 12 
                draw.polygon([(tx, ty), (tx, ty+ts), (tx+ts*0.8, ty+ts/2)], fill=color)
                draw.multiline_text((tx + 20, y_offset), text, fill=color, font=font_res)
            else:
                draw.multiline_text((text_start_x + 20, y_offset), text, fill=color, font=font_res)
                
            bbox = draw.textbbox((0,0), text, font=font_res)
            y_offset += (bbox[3] - bbox[1]) + 20
            
        return export_img

    def export_pdf_report(self):
        if not self.current_file_path or self.image_data is None: return
        base_name = os.path.basename(self.current_file_path)
        target_dir = self._get_target_dir("screenshot")
        
        target_path = filedialog.asksaveasfilename(
            initialdir=target_dir, initialfile=f"Report_{os.path.splitext(base_name)[0]}.pdf",
            title="Export Full PDF Report", defaultextension=".pdf", filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if not target_path: return
        
        try:
            page1 = self._generate_export_image()
            pages = [page1]
            
            hist_page = self._generate_histogram_page()
            if hist_page: pages.append(hist_page)
                
            pages[0].save(target_path, "PDF", resolution=150.0, save_all=True, append_images=pages[1:])
            messagebox.showinfo("Success", f"Full PDF Report successfully generated:\n{target_path}")
        except Exception as e: 
            messagebox.showerror("Error", f"Failed to generate PDF Report:\n{e}")

    def save_data(self):
        if not self.current_file_path or self.image_data is None: return
        base_name = os.path.basename(self.current_file_path)
        target_dir = self._get_target_dir("screenshot")
        target_path = os.path.join(target_dir, f"snr_{os.path.splitext(base_name)[0]}.png")
        try:
            self._generate_export_image().save(target_path, "PNG")
            messagebox.showinfo("Success", f"Screenshot saved to:\n{target_path}")
        except Exception as e: messagebox.showerror("Error", f"Failed to save:\n{e}")

    def save_data_as(self):
        if not self.current_file_path or self.image_data is None: return
        base_name = os.path.basename(self.current_file_path)
        target_dir = self._get_target_dir("screenshot")
        
        target_path = filedialog.asksaveasfilename(
            initialdir=target_dir, initialfile=f"snr_{os.path.splitext(base_name)[0]}.png",
            title="Save Data As", defaultextension=".png", filetypes=[("PNG files", "*.png"), ("All files", "*.*")]
        )
        if target_path:
            try:
                self._generate_export_image().save(target_path, "PNG")
                messagebox.showinfo("Success", f"Screenshot saved to:\n{target_path}")
            except Exception as e: messagebox.showerror("Error", f"Failed to save:\n{e}")

def main():
    setup_logging()
    root = tk.Tk()
    root.withdraw()
    app = DicomApp(root)
    
    window_width = app.init_w
    window_height = app.init_h + app.top_lbl_h
    x = int((root.winfo_screenwidth() / 2) - (window_width / 2))
    y = int((root.winfo_screenheight() / 2) - (window_height / 2))
    
    root.geometry(f"{window_width}x{window_height}+{x}+{y}")
    root.deiconify() 
    root.mainloop()

if __name__ == "__main__": main()