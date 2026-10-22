#!/usr/bin/env python3
"""Bug injection for the #669 hard cases: each variant is the base term with one textual
replacement. Writes <dir>/bugs/<base>--<tag>.bc and runs `bcc check` on it, printing
KIND tag: REJECTED <first error> | ACCEPTED (then src/lir live counts).

    bugs.py <base.bc> <spec.py>    spec: BUGS = [(kind, tag, old, new, note), ...]; old/new may be lists of edits
"""
import os, subprocess, sys, runpy
root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
bcc = os.path.join(root, ".lake/build/bin/bcc")
base, spec = sys.argv[1], sys.argv[2]
src = open(base).read()
bugs = runpy.run_path(spec)["BUGS"]
d = os.path.join(os.path.dirname(os.path.abspath(base)), "bugs")
os.makedirs(d, exist_ok=True)
for kind, tag, old, new, note in bugs:
    olds, news = (old, new) if isinstance(old, list) else ([old], [new])
    bad = [o for o in olds if src.count(o) != 1]
    if bad:
        print(f"{kind} {tag}: SPEC ERROR: old text occurs {src.count(bad[0])} times"); continue
    out_src = src
    for o, n in zip(olds, news):
        out_src = out_src.replace(o, n)
    f = os.path.join(d, os.path.basename(base)[:-3] + "--" + tag + ".bc")
    open(f, "w").write(f"-- bug {kind} {tag}: {note}\n" + out_src)
    r = subprocess.run([bcc, "check", f], capture_output=True, text=True)
    out = (r.stdout + r.stderr)
    if "assurance:" in out:
        runs = []
        for st in ([], ["--stage", "lir"]):
            p = subprocess.run([bcc, "interp"] + st + [f], capture_output=True, text=True, timeout=120)
            runs.append((p.stdout + p.stderr).strip().replace("\n", " ")[:100])
        a = [l for l in out.splitlines() if l.startswith("assurance:")][0]
        print(f"{kind} {tag}: ACCEPTED ({a}) src: {runs[0]} | lir: {runs[1]}  -- {note}")
    else:
        err = [l for l in out.splitlines() if l.strip() and not l.startswith("loop ")]
        e = err[0] if err else out.strip()
        e = e.replace(f + ":", "")
        print(f"{kind} {tag}: REJECTED {e[:260]}  -- {note}")
