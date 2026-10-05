"""
============================================================================
ERN — EVM Rework Notes
Created and developed by PIA — members: Pogi, LT, Rona
Do not edit the code without informing PIA
PIA site: https://eagleviewcloud.sharepoint.com/sites/QualityTeam/SitePages/PIA.aspx
============================================================================

ERN.py
Pick a folder of .evm files, scan them for "Needs Rework" rejections,
show the results as tables and export either table to CSV.

Tabs
  Rework Notes  - Filename, Tech, Notes, QC   (one row per rework)
  File Summary  - Filename, Reworks, Status   (one row per .evm file)

Rework rules (same as EVMData.py)
  * only "Rejected in QC from TW as Needs Rework" events are listed
  * Tech  = the Tech who opened the file right before the rework
  * Notes = the latest note block written in the rejecting QC's session
  * QC    = the rejection line (QC user + date/time)
"""

import os
import re
import sys
import csv
import queue
import threading
import webbrowser
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

import numpy as np
import scipy.io as sio

# ---------------------------------------------------------------- settings
VERSION = "1.10.5"
PIA_URL = ("https://eagleviewcloud.sharepoint.com/sites/QualityTeam/"
           "SitePages/PIA.aspx")
TECH_TAG = "TCT"                     # user IDs containing this are Techs
REWORK_PHRASE = "Rejected in QC from TW as Needs Rework"
DEFAULT_RECURSIVE = False            # initial state of the subfolder checkbox

REWORK_COLS = ["Filename", "Tech", "Notes", "QC"]
SUMMARY_COLS = ["Filename", "Reworks", "Status"]

# History-log lines containing any of these are events, not note text
EVENT_PHRASES = ["Opened by",
                 "from TW as Checkpoint by",
                 "Saved by",
                 "Checkpoint upon Finish",
                 "Measurement Completed from TW by",
                 "Checkpoint upon Reject",
                 "Rejected in QC from TW as",
                 "Rejected from TW as",
                 "from TW by",
                 "Shipped by awshrcacher",
                 "History_New"]

# "... by <USER> on <DD.MM.YYYY_HH.MM.SS>"
USER_RE = re.compile(
    r"\bby\s+([A-Za-z0-9]+)\s+on\s+"
    r"(\d{2}\.\d{2}\.\d{4}_\d{2}[.:]\d{2}[.:]\d{2})"
)
OPENED_RE = re.compile(r"Opened by\s+(\S+)")


# ------------------------------------------------------- extraction logic
def base_dir():
    """Folder that contains this script (or the .exe if frozen)."""
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def first_elem(arr):
    """First struct element regardless of shape ((1,1), (1,), (N,) ...)."""
    return np.asarray(arr).reshape(-1)[0]


def flat(arr):
    """Flatten any array shape into a 1-D array."""
    return np.asarray(arr).reshape(-1)


def to_str(x):
    """Turn a MATLAB string / nested array of strings into clean text."""
    if isinstance(x, np.ndarray):
        return " ".join(to_str(i) for i in x.reshape(-1)).strip()
    return str(x).strip()


def find_evms(folder, recursive):
    """Return a sorted list of (display_name, full_path) for .evm files."""
    found = []
    if recursive:
        for root, _, files in os.walk(folder):
            for f in files:
                if f.lower().endswith(".evm"):
                    full = os.path.join(root, f)
                    found.append((os.path.relpath(full, folder), full))
    else:
        for f in os.listdir(folder):
            full = os.path.join(folder, f)
            if os.path.isfile(full) and f.lower().endswith(".evm"):
                found.append((f, full))
    return sorted(found, key=lambda t: t[0].lower())


def file_hint(path):
    """File size and header bytes, to help diagnose unreadable files."""
    try:
        size = os.path.getsize(path)
        with open(path, "rb") as fh:
            head = fh.read(128)
        return f" [size={size} bytes, start={head[:16]!r}, ver={head[124:128]!r}]"
    except OSError:
        return ""


def get_reworks(log_lines):
    """
    Find every "Needs Rework" rejection in the history log.

    Returns a list of (tech, notes, qc_line). Notes is the LATEST block of
    note lines in the rejecting QC's session (the log repeats note blocks
    before a checkpoint and again before the reject; only the last is kept).
    """
    reworks = []
    session_user = ""
    current = []                # note lines being collected right now
    last_block = []             # most recent finished block of note lines
    last_tech = ""

    for line in log_lines:
        if not line:
            continue

        m = OPENED_RE.search(line)
        if m:
            user = m.group(1)
            if user != session_user:            # new session -> new notes
                session_user = user
                current, last_block = [], []
            if TECH_TAG.upper() in user.upper():
                last_tech = user

        is_event = (any(p in line for p in EVENT_PHRASES)
                    or USER_RE.search(line))

        if not is_event:                        # note text
            current.append(line)
            continue

        if REWORK_PHRASE in line:
            block = current or last_block
            reworks.append((last_tech, "\n".join(block), line))

        if current:                             # an event ends the block
            last_block, current = current, []

    return reworks


def extract(path):
    """Read one .evm file and return a list of rework dicts."""
    try:
        m = sio.loadmat(path, variable_names=["Comments"])
    except Exception as e:
        raise RuntimeError(
            f"{type(e).__name__}: {e}{file_hint(path)}") from e
    c = first_elem(m["Comments"])
    log_lines = [to_str(x) for x in flat(c["Notes"])]
    return [{"Tech": tech, "Notes": notes, "QC": qc}
            for tech, notes, qc in get_reworks(log_lines)]


# --------------------------------------------------------------------- GUI
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"ERN — EVM Rework Notes  v{VERSION}")
        self.geometry("1200x720")
        self.minsize(900, 500)

        self.q = queue.Queue()
        self.worker = None
        self.cancel = threading.Event()

        self.rework_rows = {}       # tree iid -> dict(Filename, Tech, ...)
        self.summary_rows = {}      # tree iid -> dict(Filename, ...)
        self.sort_state = {}        # (tree, col) -> reverse?
        self.scanned_folder = ""

        self.folder_var = tk.StringVar(value=base_dir())
        self.recursive_var = tk.BooleanVar(value=DEFAULT_RECURSIVE)
        self.status_var = tk.StringVar(value="Choose a folder and click Scan.")

        self._build_ui()
        self.after(100, self._poll)

    # ------------------------------------------------------------- layout
    def _build_ui(self):
        pad = {"padx": 8, "pady": 4}

        top = ttk.Frame(self)
        top.pack(fill="x", **pad)
        ttk.Label(top, text="EVM folder:").pack(side="left")
        entry = ttk.Entry(top, textvariable=self.folder_var)
        entry.pack(side="left", fill="x", expand=True, padx=6)
        entry.bind("<Return>", lambda e: self.start_scan())
        ttk.Button(top, text="Browse...", command=self.browse).pack(side="left")
        ttk.Checkbutton(top, text="Include subfolders",
                        variable=self.recursive_var).pack(side="left", padx=10)
        self.scan_btn = ttk.Button(top, text="Scan", command=self.start_scan)
        self.scan_btn.pack(side="left")
        self.export_btn = ttk.Button(top, text="Export CSV...",
                                     command=self.export_csv,
                                     state="disabled")
        self.export_btn.pack(side="left", padx=(8, 0))

        # tabs with the two tables
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, **pad)

        self.rework_tree = self._make_table(
            self.nb, "Rework Notes", REWORK_COLS,
            {"Filename": 380, "Tech": 120, "Notes": 360, "QC": 420})
        self.summary_tree = self._make_table(
            self.nb, "File Summary", SUMMARY_COLS,
            {"Filename": 520, "Reworks": 90, "Status": 520})

        # full-text detail of the selected rework row
        detail = ttk.LabelFrame(self, text="Selected rework")
        detail.pack(fill="x", padx=8, pady=(0, 4))
        self.detail = tk.Text(detail, height=9, wrap="word",
                              state="disabled", relief="flat")
        self.detail.pack(fill="x", padx=6, pady=4)
        self.rework_tree.bind("<<TreeviewSelect>>", self._show_detail)

        # footer: PIA link on the left, status + progress bar on the right
        bar = ttk.Frame(self)
        bar.pack(fill="x", padx=8, pady=(0, 8))

        pia = tk.Label(bar, text="\u2605 PIA", fg="#0563c1", cursor="hand2",
                       font=("Segoe UI", 9, "bold"))
        pia.pack(side="left")
        pia.bind("<Button-1>", lambda e: webbrowser.open(PIA_URL))

        self.progress = ttk.Progressbar(bar, length=200, mode="determinate")
        self.progress.pack(side="right")
        ttk.Label(bar, textvariable=self.status_var, anchor="e").pack(
            side="right", padx=(0, 10))

    def _make_table(self, nb, title, cols, widths):
        frame = ttk.Frame(nb)
        nb.add(frame, text=title)
        tree = ttk.Treeview(frame, columns=cols, show="headings",
                            selectmode="browse")
        for col in cols:
            tree.heading(col, text=col,
                         command=lambda c=col, t=tree: self._sort(t, c))
            tree.column(col, width=widths.get(col, 150), anchor="w")
        tree.tag_configure("odd", background="#f3f6fa")
        vs = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        hs = ttk.Scrollbar(frame, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
        tree.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        hs.grid(row=1, column=0, sticky="ew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        return tree

    # ------------------------------------------------------------ actions
    def browse(self):
        start = self.folder_var.get()
        folder = filedialog.askdirectory(
            title="Select the folder with the .evm files",
            initialdir=start if os.path.isdir(start) else base_dir())
        if folder:
            self.folder_var.set(os.path.normpath(folder))
            self.start_scan()

    def start_scan(self):
        if self.worker and self.worker.is_alive():
            return
        folder = self.folder_var.get().strip().strip('"')
        if not os.path.isdir(folder):
            messagebox.showerror("Folder not found",
                                 f"This folder does not exist:\n{folder}")
            return

        self._clear_tables()
        self.scanned_folder = folder
        self.scan_btn.config(state="disabled")
        self.export_btn.config(state="disabled")
        self.progress.config(value=0, maximum=1)
        self.status_var.set("Looking for .evm files...")

        self.cancel.clear()
        self.worker = threading.Thread(
            target=self._scan_worker,
            args=(folder, self.recursive_var.get()), daemon=True)
        self.worker.start()

    def _scan_worker(self, folder, recursive):
        """Runs in a thread; talks to the UI only through the queue."""
        try:
            evms = find_evms(folder, recursive)
        except OSError as e:
            self.q.put(("fatal", f"{type(e).__name__}: {e}"))
            return
        self.q.put(("total", len(evms)))
        for i, (name, path) in enumerate(evms, 1):
            if self.cancel.is_set():
                break
            try:
                found = extract(path)
                status = "Rework found" if found else "No rework"
            except Exception as e:
                found, status = [], f"ERROR: {e}"
            self.q.put(("file", i, len(evms), name, found, status))
        self.q.put(("done",))

    def _poll(self):
        """Apply worker results to the tables (runs on the UI thread)."""
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "total":
                    self.progress.config(maximum=max(msg[1], 1), value=0)
                    if msg[1] == 0:
                        self.status_var.set("No .evm files found in that "
                                            "folder.")
                elif kind == "file":
                    _, i, total, name, found, status = msg
                    self._add_file(name, found, status)
                    self.progress.config(value=i)
                    self.status_var.set(f"Scanning {i}/{total}: {name}")
                elif kind == "fatal":
                    messagebox.showerror("Scan failed", msg[1])
                    self._finish_scan()
                elif kind == "done":
                    self._finish_scan()
        except queue.Empty:
            pass
        self.after(100, self._poll)

    def _finish_scan(self):
        self.scan_btn.config(state="normal")
        n_files = len(self.summary_rows)
        n_rework = len(self.rework_rows)
        n_err = sum(1 for r in self.summary_rows.values()
                    if r["Status"].startswith("ERROR"))
        if n_files:
            self.status_var.set(
                f"Done: {n_rework} rework entries from {n_files} file(s)"
                + (f"; {n_err} file(s) failed to read (see File Summary)"
                   if n_err else "") + ".")
        self.export_btn.config(state="normal" if n_files else "disabled")

    def _add_file(self, name, found, status):
        srow = {"Filename": name, "Reworks": len(found), "Status": status}
        iid = self.summary_tree.insert(
            "", "end", values=self._display(SUMMARY_COLS, srow),
            tags=self._stripe(self.summary_tree))
        self.summary_rows[iid] = srow

        for r in found:
            row = {"Filename": name, **r}
            iid = self.rework_tree.insert(
                "", "end", values=self._display(REWORK_COLS, row),
                tags=self._stripe(self.rework_tree))
            self.rework_rows[iid] = row

    @staticmethod
    def _display(cols, row):
        """Single-line cell text for the table (newlines -> ' | ')."""
        return [str(row[c]).replace("\r", "").replace("\n", "  |  ")
                for c in cols]

    @staticmethod
    def _stripe(tree):
        return ("odd",) if len(tree.get_children()) % 2 else ()

    def _clear_tables(self):
        for tree in (self.rework_tree, self.summary_tree):
            tree.delete(*tree.get_children())
        self.rework_rows.clear()
        self.summary_rows.clear()
        self._set_detail("")

    def _sort(self, tree, col):
        key = (str(tree), col)
        reverse = not self.sort_state.get(key, True)
        self.sort_state[key] = reverse

        def sort_val(iid):
            v = tree.set(iid, col)
            return (0, float(v), "") if v.isdigit() else (1, 0, v.lower())

        items = sorted(tree.get_children(""), key=sort_val, reverse=reverse)
        for idx, iid in enumerate(items):
            tree.move(iid, "", idx)
            tree.item(iid, tags=("odd",) if idx % 2 else ())

    # ------------------------------------------------------------- detail
    def _set_detail(self, text):
        self.detail.config(state="normal")
        self.detail.delete("1.0", "end")
        self.detail.insert("1.0", text)
        self.detail.config(state="disabled")

    def _show_detail(self, _event=None):
        sel = self.rework_tree.selection()
        if not sel:
            return
        r = self.rework_rows[sel[0]]
        self._set_detail(f"File: {r['Filename']}\nTech: {r['Tech']}\n"
                         f"QC:   {r['QC']}\n\nNotes:\n{r['Notes']}")

    # ------------------------------------------------------------- export
    def export_csv(self):
        """Export the table on the active tab, in the order shown."""
        on_rework = self.nb.index(self.nb.select()) == 0
        tree, rows, cols, default = (
            (self.rework_tree, self.rework_rows, REWORK_COLS,
             "ReworkNotes.csv") if on_rework else
            (self.summary_tree, self.summary_rows, SUMMARY_COLS,
             "FileSummary.csv"))

        ordered = [rows[i] for i in tree.get_children("")]
        if not ordered:
            messagebox.showinfo("Nothing to export",
                                "This table has no rows.")
            return

        path = filedialog.asksaveasfilename(
            title="Save CSV", defaultextension=".csv",
            initialdir=self.scanned_folder or base_dir(),
            initialfile=default,
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")])
        if not path:
            return
        try:
            # utf-8-sig so Excel opens it correctly; newline="" keeps the
            # line breaks inside the Notes cells
            with open(path, "w", newline="", encoding="utf-8-sig") as fh:
                w = csv.DictWriter(fh, fieldnames=cols,
                                   extrasaction="ignore")
                w.writeheader()
                w.writerows(ordered)
        except PermissionError:
            messagebox.showerror(
                "Cannot save",
                f"{os.path.basename(path)} is locked (open in Excel?).\n"
                "Close it or pick another name.")
            return
        except OSError as e:
            messagebox.showerror("Cannot save", str(e))
            return
        self.status_var.set(f"Saved {len(ordered)} row(s) to {path}")


if __name__ == "__main__":
    App().mainloop()
