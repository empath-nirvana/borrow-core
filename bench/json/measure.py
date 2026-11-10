"""#977's JSON benchmark: our `parse.bc` and `roundtrip.bc` (`include json`) against serde_json.

    python3 -I measure.py build            build both sides into out/
    python3 -I measure.py time [--runs N]  time them; run.sh calls this holding the gate lock

`build`:
- ours: `bcc compile --target native` (Backend2, the default), then the native runtime (the C
  source `runtimeC` in `Target/Native/Runtime.lean`) and the program's LLVM IR compiled together
  by the C compiler and flags `bcc` builds with: `bcc cc --flags` when this `bcc` has it, else
  `bcc cc` and the flags of `clangArgs` in `Pipeline/Driver.lean`;
- serde: `cargo build --release --offline --locked` in `serde/`.
`$BCC` names the `bcc` (default: this checkout's `.lake/build/bin/bcc`); it must know the library
module `json`.

`time`, for each document of data/ and each of parse and roundtrip:
- **CPU time**: user + sys of the process, from `wait4`'s rusage, in µs. One warm-up run per
  binary, then rounds that interleave ours and serde (the order alternating by round), until each
  has `--runs` (default 7) kept runs; the median is reported, and MB/s is the document's bytes
  (10^6 to the MB) over it.
- **A run is discarded** when the 1-minute load (`os.getloadavg`) is 2 or more before or after
  it, or when a lake, lean, clang or bcc process is running before or after it. Each run records
  `uptime` and those processes before and after, in out/results.json.
- **Allocations**: serde's from its counting allocator (`JSON_BENCH_ALLOCS`, the count of
  `alloc`, `alloc_zeroed` and `realloc` calls); ours from `bcc-counts --native` (`$BCC_COUNTS`,
  default next to `bcc`), the count of `bc_alloc` calls of a counting build. `bcc-counts` also runs
  the flat IR's interpreter on the document to compare its counts, which can take long:
  `--no-allocs` skips it, `--allocs-timeout` bounds it (default 1800 s), and a column it cannot
  fill is `—`.
- **Peak RSS**: `/usr/bin/time -l`'s maximum resident set size, one run each.
- **Stripped size**: a copy of each executable after `strip`.
The table, ours over Rust for each column, goes to standard output and out/results.md.
"""

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(HERE, "out")
DATA = os.path.join(HERE, "data")
DOCS = ["canada", "citm_catalog", "twitter"]
MODES = ["parse", "roundtrip"]
BCC = os.environ.get("BCC", os.path.join(ROOT, ".lake", "build", "bin", "bcc"))
BCC_COUNTS = os.environ.get("BCC_COUNTS", os.path.join(os.path.dirname(BCC), "bcc-counts"))
SERDE = os.path.join(HERE, "serde", "target", "release", "json-bench")
# The processes whose presence before or after a run discards it.
BUSY = {"lake", "lean", "leanc", "clang", "clang++", "bcc", "bcc-counts"}
MAX_LOAD = 2.0


def ours_exe(mode):
    return os.path.join(OUT, mode)


def command(side, mode):
    return [ours_exe(mode)] if side == "ours" else [SERDE, mode]


def must(r, what):
    if r.returncode != 0:
        sys.exit(f"measure.py: {what} failed ({r.returncode}):\n{r.stderr.decode()[:3000]}")
    return r


# ### Building

def runtime_c():
    """The native runtime's C source: `runtimeC` in `Target/Native/Runtime.lean`."""
    src = open(os.path.join(ROOT, "Target", "Native", "Runtime.lean")).read()
    start = src.index('r##"', src.index("def runtimeC")) + 4
    return src[start:src.index('"##', start)]


def native_cc():
    """The C compiler command and flags `bcc` builds native code with."""
    r = subprocess.run([BCC, "cc", "--flags"], capture_output=True)
    if r.returncode == 0 and r.stdout.strip():
        return r.stdout.decode().split()
    cc = must(subprocess.run([BCC, "cc"], capture_output=True), "bcc cc").stdout.decode().split()
    src = open(os.path.join(ROOT, "Pipeline", "Driver.lean")).read()
    m = re.search(r"def clangArgs : Array String := #\[([^\]]*)\]", src)
    if not m:
        sys.exit("measure.py: no `clangArgs` in Pipeline/Driver.lean")
    return cc + re.findall(r'"([^"]*)"', m.group(1))


def build():
    os.makedirs(OUT, exist_ok=True)
    if not os.access(BCC, os.X_OK):
        sys.exit(f"measure.py: no bcc at {BCC} (set $BCC)")
    must(subprocess.run(["cargo", "build", "--release", "--offline", "--locked"],
                        cwd=os.path.join(HERE, "serde"), capture_output=True), "cargo build")
    rt = os.path.join(OUT, "runtime.c")
    open(rt, "w").write(runtime_c())
    cc = native_cc()
    info = {"cc": cc, "bcc": BCC}
    for mode in MODES:
        ll = os.path.join(OUT, mode + ".ll")
        t0 = time.monotonic()
        must(subprocess.run([BCC, "compile", "--target", "native",
                             os.path.join(HERE, mode + ".bc"), "-o", ll], capture_output=True),
             f"bcc compile {mode}.bc")
        t1 = time.monotonic()
        must(subprocess.run(cc + [ll, rt, "-o", ours_exe(mode)], capture_output=True),
             f"{' '.join(cc)} {mode}")
        t2 = time.monotonic()
        info[mode] = {"bcc_s": t1 - t0, "cc_s": t2 - t1}
        print(f"built out/{mode}: bcc {t1 - t0:.2f} s, cc {t2 - t1:.2f} s")
    json.dump(info, open(os.path.join(OUT, "build.json"), "w"), indent=1)
    print(f"built {SERDE}")


# ### The machine's state

def busy_processes():
    """The lake, lean, clang and bcc processes running now, as `pid name`."""
    r = subprocess.run(["ps", "-axo", "pid=,comm="], capture_output=True, text=True)
    found = []
    for line in r.stdout.splitlines():
        pid, _, comm = line.strip().partition(" ")
        if os.path.basename(comm.strip()) in BUSY and int(pid) != os.getpid():
            found.append(f"{pid} {os.path.basename(comm.strip())}")
    return found


def machine():
    up = subprocess.run(["uptime"], capture_output=True, text=True).stdout.strip()
    return {"uptime": up, "load1": os.getloadavg()[0], "busy": busy_processes()}


def quiet(state):
    return state["load1"] < MAX_LOAD and not state["busy"]


# ### Running

def run_once(cmd, doc, stdout=subprocess.DEVNULL):
    """Run `cmd` with the document on standard input: (exit status, CPU µs, ru_maxrss)."""
    with open(doc, "rb") as f:
        p = subprocess.Popen(cmd, stdin=f, stdout=stdout, stderr=subprocess.DEVNULL)
        _, status, ru = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
    cpu_us = round((ru.ru_utime + ru.ru_stime) * 1e6)
    return p.returncode, cpu_us, ru.ru_maxrss


def timed_runs(doc, mode, runs, log):
    """Interleaved kept runs of both sides: {side: [µs]}."""
    kept = {"ours": [], "serde": []}
    for side in ("ours", "serde"):  # warm-up
        run_once(command(side, mode), doc)
    rnd = 0
    attempts = 0
    while min(len(v) for v in kept.values()) < runs:
        order = ("ours", "serde") if rnd % 2 == 0 else ("serde", "ours")
        for side in order:
            if len(kept[side]) >= runs:
                continue
            attempts += 1
            if attempts > 6 * runs:
                sys.exit(f"measure.py: {mode} {doc}: too many discarded runs; the machine is "
                         "not quiet (see out/results.json)")
            before = machine()
            status, us, _ = run_once(command(side, mode), doc)
            after = machine()
            keep = status == 0 and quiet(before) and quiet(after)
            log.append({"doc": os.path.basename(doc), "mode": mode, "side": side, "cpu_us": us,
                        "status": status, "kept": keep, "before": before, "after": after})
            if status != 0:
                sys.exit(f"measure.py: {side} {mode} on {doc} exits {status}")
            if keep:
                kept[side].append(us)
            else:
                print(f"  discarded a {side} run: load {before['load1']:.2f}/{after['load1']:.2f}, "
                      f"busy {before['busy'] + after['busy']}", file=sys.stderr)
                time.sleep(5)
        rnd += 1
    return kept


def peak_rss(cmd, doc):
    """`/usr/bin/time -l`'s maximum resident set size, in bytes."""
    with open(doc, "rb") as f:
        r = subprocess.run(["/usr/bin/time", "-l"] + cmd, stdin=f, stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, text=True)
    m = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
    return int(m.group(1)) if m else None


def serde_allocs(mode, doc):
    with open(doc, "rb") as f:
        r = subprocess.run([SERDE, mode], stdin=f, stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, text=True,
                           env=dict(os.environ, JSON_BENCH_ALLOCS="1"))
    m = re.search(r"^allocs (\d+)$", r.stderr, re.M)
    return int(m.group(1)) if m else None


def ours_allocs(mode, doc, timeout):
    """`bc_alloc` calls of `bcc-counts --native`'s counting build, or None."""
    if not os.access(BCC_COUNTS, os.X_OK):
        return None
    try:
        with open(doc, "rb") as f:
            r = subprocess.run([BCC_COUNTS, "--native", os.path.join(HERE, mode + ".bc")],
                               stdin=f, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    m = re.search(r"^allocs (\d+)", r.stdout, re.M)
    return int(m.group(1)) if m and r.returncode == 0 else None


def stripped_size(exe):
    s = os.path.join(OUT, os.path.basename(exe) + ".stripped")
    shutil.copyfile(exe, s)
    subprocess.run(["strip", s], capture_output=True)
    return os.path.getsize(s)


# ### The table

def fmt(x, unit=""):
    return "—" if x is None else f"{x:,}{unit}" if isinstance(x, int) else f"{x:.1f}{unit}"


def ratio(a, b):
    return "—" if a is None or b is None or b == 0 else f"{a / b:.2f}×"


def table(results):
    rows = ["| document | mode | ours MB/s | Rust MB/s | time ours/Rust | allocs ours / Rust (ratio) "
            "| peak RSS MB ours / Rust (ratio) |",
            "|---|---|---|---|---|---|---|"]
    for r in results:
        o, s = r["ours"], r["serde"]
        mb = lambda b: None if b is None else b / 1e6
        rows.append(
            f"| {r['doc']} | {r['mode']} | {o['mbs']:.1f} | {s['mbs']:.1f} "
            f"| **{ratio(o['median_us'], s['median_us'])}** "
            f"| {fmt(o['allocs'])} / {fmt(s['allocs'])} ({ratio(o['allocs'], s['allocs'])}) "
            f"| {fmt(mb(o['rss']))} / {fmt(mb(s['rss']))} ({ratio(o['rss'], s['rss'])}) |")
    return "\n".join(rows)


def time_all(args):
    for exe in [ours_exe(m) for m in MODES] + [SERDE]:
        if not os.access(exe, os.X_OK):
            sys.exit(f"measure.py: {exe} not built (measure.py build)")
    log = []
    results = []
    start = machine()
    print(f"start: {start['uptime']}; busy: {start['busy'] or 'none'}")
    for d in DOCS:
        doc = os.path.join(DATA, d + ".json")
        size = os.path.getsize(doc)
        for mode in MODES:
            kept = timed_runs(doc, mode, args.runs, log)
            res = {"doc": d, "mode": mode, "bytes": size}
            for side in ("ours", "serde"):
                med = statistics.median(kept[side])
                res[side] = {
                    "runs_us": kept[side], "median_us": med, "mbs": size / med,
                    "rss": peak_rss(command(side, mode), doc),
                    "allocs": serde_allocs(mode, doc) if side == "serde"
                    else None if args.no_allocs else ours_allocs(mode, doc, args.allocs_timeout),
                }
            results.append(res)
            print(f"{d} {mode}: ours {res['ours']['median_us']} µs, "
                  f"serde {res['serde']['median_us']} µs")
    end = machine()
    sizes = {"ours": {m: stripped_size(ours_exe(m)) for m in MODES},
             "serde": stripped_size(SERDE)}
    md = [table(results), "",
          "Stripped size: " + ", ".join(
              f"ours {m} {sizes['ours'][m]:,} B ({ratio(sizes['ours'][m], sizes['serde'])})"
              for m in MODES) + f"; Rust (both modes) {sizes['serde']:,} B.",
          "", f"CPU time (user + sys), median of {args.runs} kept runs, interleaved; MB = 10^6 bytes.",
          f"Machine before: `{start['uptime']}`; after: `{end['uptime']}`."]
    text = "\n".join(md)
    print(text)
    open(os.path.join(OUT, "results.md"), "w").write(text + "\n")
    json.dump({"results": results, "sizes": sizes, "start": start, "end": end, "runs": log},
              open(os.path.join(OUT, "results.json"), "w"), indent=1)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("build")
    t = sub.add_parser("time")
    t.add_argument("--runs", type=int, default=7)
    t.add_argument("--no-allocs", action="store_true")
    t.add_argument("--allocs-timeout", type=int, default=1800)
    sub.add_parser("dry", help="check the setup and the machine's state; time nothing")
    a = ap.parse_args()
    if a.cmd == "time" and a.runs < 7:
        sys.exit("measure.py: at least 7 runs")
    if a.cmd == "build":
        build()
    elif a.cmd == "time":
        time_all(a)
    else:
        print(f"bcc: {BCC} ({'present' if os.access(BCC, os.X_OK) else 'missing'})")
        print(f"bcc-counts: {BCC_COUNTS} ({'present' if os.access(BCC_COUNTS, os.X_OK) else 'missing'})")
        print(f"serde: {SERDE} ({'present' if os.access(SERDE, os.X_OK) else 'missing'})")
        for m in MODES:
            print(f"ours {m}: {'present' if os.access(ours_exe(m), os.X_OK) else 'missing'}")
        for d in DOCS:
            p = os.path.join(DATA, d + ".json")
            print(f"data {d}: {os.path.getsize(p) if os.path.exists(p) else 'missing'}")
        print(f"runtime.c: {len(runtime_c()):,} chars from Target/Native/Runtime.lean")
        if os.access(BCC, os.X_OK):
            print(f"cc: {' '.join(native_cc())}")
        st = machine()
        print(f"machine: {st['uptime']}; busy: {st['busy'] or 'none'}; quiet: {quiet(st)}")


if __name__ == "__main__":
    main()
