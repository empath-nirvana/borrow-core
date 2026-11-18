#!/usr/bin/env bash
# The per-PR gate's tier: which steps `make gate` runs, chosen from the paths the change touches,
# never from anyone's judgement, so two agents with the same change get the same gate.
#
#     scripts/gate-tier.sh                 the tier statement and the plan, for a reader
#     scripts/gate-tier.sh --plan          the plan, one line per item, for scripts/ci-local.sh
#     scripts/gate-tier.sh --base C        diff against commit C instead of the merge base (also
#                                          `CI_LOCAL_BASE=C`)
#     scripts/gate-tier.sh --paths         read the changed paths from standard input instead of git
#
# The change is every path that differs between the merge base with origin/main (after a fetch)
# and the working tree: committed, staged, unstaged and untracked files. A rename counts as both
# its old and its new path (`--no-renames`), so moving a file never lowers the tier. If origin/main cannot be
# fetched or has no merge base with HEAD, the tier is `full` and the statement says why.
#
# Each path falls in one class; the gate runs the union of what the classes present ask for, and
# the tier is named after the highest class present:
#
#   docs < book < corpus < research < scripts < compiler < full
#
#   docs       docs/, SPEC.md, any *.md outside book/, bench/, experiments/, .github/, Brewfile:
#              read by no step but spec files (docs/changelog, docs/status) and judgment freeze
#              (every tracked .lean, experiments/ included). Runs A. No build.
#   book       book/: A, book doc-tests, book build.
#   corpus     corpus/ (but the files Frontend/Check/CrossCheck.lean reads at elaboration, which are
#              Lean inputs: compiler): A, and every step on the programs the change touches (a
#              program's .bc, a sidecar .in .args .out .err .status .key, its reports/, trusted/ or
#              copies/ file; corpus/reject, pending, fail and sugar files); the steps without a
#              per-program mode whole (clause kinds, handled names, cell classes, sugar pairs,
#              layout rejects); a changed table (`*.expected`) runs its step whole, and
#              `corpus/skips.expected` every step that pins skips; a touched program that
#              compile-native.sh names in its serial tail runs native whole. What is a program is
#              scripts/corpus-set.sh's answer, as for every corpus step.
#   research   research/: A and L.
#   scripts    a step's own script (the map below): A, the steps whose script changed, and the
#              compiler tier's cut. Every result-cache key holds all of scripts/, so every unit
#              misses after any script change; the cut keeps that to the compiler tier's cost.
#              Scripts no gate step runs (falsify, the kernel census, new-worktree, gate-daily): A.
#   compiler   any other .lean, scripts/axioms/*.names, lib/, the CrossCheck corpus files: the
#              whole build, A, L, the cut (C and X on every program), R on every program when a
#              changed path is in the elaborator's or the reference interpreter's import closure
#              (below), and every step on the touched programs.
#   full       lean-toolchain, lake-manifest.json, lakefile.toml; the gate's own machinery
#              (ci-local.sh, par.sh, par_unit.py, slot, slotpool.py, gate_cache.py, gate-tier.sh,
#              source-stage.sh, interp-digest.sh, corpus-set.sh, the Makefile); and every path that
#              matches no rule here: every step on every
#              program (the full gate, cached).
#
# Step groups (ci-local.sh's step names):
#   A  spec files, judgment freeze, assumptions, gate tiers (scripts/check-gate-tier.sh)
#   L  hygiene + axioms, type equality, axiom report, insertion pins, research archive, backend2 fence
#   C  parse corpus, check corpus, corpus (Backend2, final), corpus (old backend, final), result cache
#   X  compile scaling, kernel (old backend), layout rejects, sugar pairs, book doc-tests, book build
#   R  renaming, let mut combos
#   P  corpus (Backend2), corpus (old backend), native facts, native, clause kinds, handled names,
#      cell classes
# What the per-PR gate leaves out is checked by the daily full gate on main (scripts/gate-daily.sh).
#
# R's paths are computed, not listed: the import closure, over the repository's own modules, of
# every Frontend module but Frontend.Main (the parser, the elaborator and the checker, which
# `bcc check`, `bcc erase` and `bcc alpha` run) and of every Reference module (the interpreter
# `bcc interp` runs, which let mut combos uses), plus Frontend/Main.lean itself (the command
# dispatch) and lib/. Today that closure is Frontend, Core, Support, Paper, Reference,
# Pipeline.Driver, Target.Value and Target.Native.Runtime; a backend-only change is outside it.
#
# --plan prints:
#   base <commit> | base none <why>
#   tier <name>
#   build none | build bins | build all
#   run <step>                       the step on every program (or the whole step)
#   run <step> <file>...             the step on those files only
#   line <text>                      the tier statement (printed by ci-local at the top and end)
#   left <text>                      what is left to the daily run
set -uo pipefail
cd "$(dirname "$0")/.."
plan=0 base=${CI_LOCAL_BASE:-} stdin=0
while [ $# -gt 0 ]; do
  case "$1" in
    --plan) plan=1 ;;
    --base) base=${2:?--base needs a commit}; shift ;;
    --paths) stdin=1 ;;
    *) echo "usage: scripts/gate-tier.sh [--plan] [--base <commit>] [--paths]"; exit 2 ;;
  esac
  shift
done
why=""
if [ "$stdin" = 1 ]; then
  files=$(cat); base=${base:-stdin}
else
  if [ -z "$base" ]; then
    if ! git fetch -q origin 2>/dev/null; then why="origin could not be fetched"
    elif ! base=$(git merge-base origin/main HEAD 2>/dev/null); then base=""; why="HEAD has no merge base with origin/main"
    fi
  fi
  files=""
  [ -z "$base" ] || base=$(git rev-parse --verify -q "$base^{commit}") || { why="$base is not a commit"; base=""; }
  [ -z "$base" ] || files=$({ git diff --name-only --no-renames "$base"; git ls-files --others --exclude-standard; } | sort -u)
fi
export GATE_TIER_PLAN=$plan GATE_TIER_BASE=$base GATE_TIER_WHY=$why
printf '%s\n' "$files" | python3 -c "$(sed -n '/^# PYTHON$/,$p' "$0")"
exit
# PYTHON
import os, re, sys, glob

plan = os.environ["GATE_TIER_PLAN"] == "1"
base = os.environ["GATE_TIER_BASE"]
why = os.environ["GATE_TIER_WHY"]
paths = [p for p in sys.stdin.read().split("\n") if p]

A = ["spec files", "judgment freeze", "assumptions", "gate tiers"]
L = ["hygiene + axioms", "type equality", "axiom report", "insertion pins", "research archive", "backend2 fence"]
C = ["parse corpus", "check corpus", "corpus (Backend2, final)", "corpus (old backend, final)", "result cache"]
X = ["compile scaling", "kernel (old backend)", "layout rejects", "sugar pairs", "book doc-tests", "book build"]
R = ["renaming", "let mut combos"]
P = ["corpus (Backend2)", "corpus (old backend)", "native facts", "native", "clause kinds", "handled names", "cell classes"]
FULL = A + L + ["parse corpus", "check corpus"] + X + R + P + ["result cache"]
ORDER = ["docs", "book", "corpus", "research", "scripts", "compiler", "full"]

# The steps each script belongs to (a change to it reruns those steps on every program).
STEP_SCRIPTS = {
    "check-hygiene.sh": ["hygiene + axioms"], "check-crosscheck-trace.sh": ["hygiene + axioms"], "CheckAxioms.lean": ["hygiene + axioms"],
    "gen-pin.py": ["hygiene + axioms"], "pin/": ["hygiene + axioms"],
    "check-spec-files.sh": ["spec files"], "changelog.sh": ["spec files"], "status.sh": ["spec files"],
    "check-judgments.sh": ["judgment freeze"], "judgments.allow": ["judgment freeze"],
    "check-assumptions.sh": ["assumptions"],
    "check-type-eq.sh": ["type equality"], "TypeEq.lean": ["type equality"], "type-eq.allow": ["type equality"],
    "AxiomCheck.lean": ["axiom report", "research archive"],
    "check-pins.sh": ["insertion pins"], "PinSites.lean": ["insertion pins"],
    "check-research.sh": ["research archive"],
    "parse-corpus.sh": ["parse corpus"], "check-corpus.sh": ["check corpus"],
    "check-kinds.sh": ["clause kinds"], "check-handled.sh": ["handled names"], "check-cells.sh": ["cell classes"],
    "compile-backend2.sh": ["corpus (Backend2)", "corpus (Backend2, final)", "result cache"],
    "compile-corpus.sh": ["corpus (old backend)", "corpus (old backend, final)"],
    "merge-rows.awk": ["corpus (Backend2)", "corpus (old backend)"],
    "compile-kernel.sh": ["kernel (old backend)"], "check-backend2.sh": ["backend2 fence"],
    "check-layout-reject.sh": ["layout rejects"], "native-facts.sh": ["native facts"],
    "compile-native.sh": ["native"], "check-sugar.sh": ["sugar pairs"], "mut-combos.py": ["let mut combos"],
    "alpha-check.py": ["renaming"], "book-doctest.sh": ["book doc-tests"],
    "compile-scaling.sh": ["compile scaling"], "check-gate-cache.sh": ["result cache"],
    "check-gate-tier.sh": ["gate tiers"],
    "native-run.sh": ["corpus (Backend2)", "corpus (Backend2, final)", "native", "result cache"],
    "gate-census.sh": ["hygiene + axioms", "type equality", "axiom report", "insertion pins", "research archive"],
    "GateCensus.lean": ["hygiene + axioms", "type equality", "axiom report", "insertion pins", "research archive"],
    "GateCensus/": ["hygiene + axioms", "type equality", "axiom report", "insertion pins", "research archive"],
    "census-neg/": ["type equality", "axiom report", "insertion pins"],
}
MACHINERY = {"ci-local.sh", "par.sh", "gate_cache.py", "gate-tier.sh", "source-stage.sh", "interp-digest.sh",
             "corpus-set.sh", "par_unit.py", "slot", "slotpool.py"}
NO_STEP = {"falsify.sh", "kernel-census.sh", "KernelCensus.lean", "KernelDecls.lean", "new-worktree.sh",
           "gate-daily.sh", "gate-daily.plist"}
TABLES = {"kinds.expected": "clause kinds", "handled.expected": "handled names", "cells.expected": "cell classes",
          "counts.expected": "corpus (old backend)", "counts-backend2.expected": "corpus (Backend2)",
          "erasure-backend2.expected": "corpus (Backend2)", "kernel-counts.expected": "kernel (old backend)"}
# The pinned skips: read by every step that skips a program (`corpus-set.sh --skips`).
SKIPS_STEPS = ["check corpus", "corpus (Backend2)", "corpus (old backend)", "native facts", "native",
               "clause kinds", "handled names", "cell classes"]
LIBS = ["Paper", "Support", "Examples", "Core", "Frontend", "Target", "Pipeline", "Reference", "Backend", "Backend2"]


def crosscheck_files():
    """The corpus files Frontend/Check/CrossCheck.lean embeds at elaboration (`bcc_program% "…"`)."""
    try:
        return set(re.findall(r'bcc_program%\s*"([^"]+)"', open("Frontend/Check/CrossCheck.lean").read()))
    except OSError:
        return set()


def r_closure():
    """The files of the elaborator's and the reference interpreter's import closure (header)."""
    mods = {}
    for lib in LIBS:
        for p in [lib + ".lean"] + sorted(glob.glob(lib + "/**/*.lean", recursive=True)):
            if os.path.exists(p):
                mods[p[:-5].replace("/", ".")] = p
    imports = {}
    for m, p in mods.items():
        ims = []
        for line in open(p, encoding="utf-8"):
            s = line.strip()
            m2 = re.match(r"(?:(?:public|private|meta)\s+)*import\s+(.*)", s)
            if m2:
                ims += [x for x in m2.group(1).split() if x in mods]
        imports[m] = ims
    todo = [m for m in mods if (m.startswith("Frontend.") and m != "Frontend.Main") or m.split(".")[0] == "Reference"]
    seen = set()
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo += imports[m]
    return {mods[m] for m in seen} | {"Frontend/Main.lean"}


def native_tail():
    """The corpus programs compile-native.sh's serial tail runs by name."""
    try:
        s = open("scripts/compile-native.sh").read()
    except OSError:
        return set()
    out = set(re.findall(r"corpus/[A-Za-z0-9_-]+\.bc", s))
    for group in re.findall(r"corpus/\{([^}]*)\}", s):
        out |= {f"corpus/{x}.bc" for x in group.split(",")}
    return out


SIDECARS = (".in", ".args", ".out", ".err", ".status", ".key")


_sets = {}


def corpus_set(cls):
    """The corpus files of a class, as every corpus step takes them (scripts/corpus-set.sh)."""
    if cls not in _sets:
        import subprocess
        r = subprocess.run(["scripts/corpus-set.sh", cls], capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"gate-tier: scripts/corpus-set.sh {cls} failed: {r.stderr.strip()}")
        _sets[cls] = set(r.stdout.split("\n")) - {""}
    return _sets[cls]


def is_program(p):
    return p in corpus_set("programs")


cross = crosscheck_files()
classes = {}          # path -> class
step_all = set()      # steps on every program
touched = set()       # corpus files touched
step_why = []         # scripts changed -> steps
unknown = []
r_paths = []
for p in paths:
    name = p.split("/", 1)[1] if p.startswith("scripts/") else None
    if p in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "Makefile"):
        c = "full"
    elif name is not None:
        if name in MACHINERY:
            c = "full"
        elif name in NO_STEP:
            c = "docs"
        elif name.startswith("axioms/"):
            c = "compiler"
        elif name.startswith("__pycache__/"):
            c = "docs"
        else:
            key = next((d for d in ("pin/", "GateCensus/", "census-neg/") if name.startswith(d)), name)
            if key in STEP_SCRIPTS:
                c = "scripts"
                step_all.update(STEP_SCRIPTS[key])
            else:
                c = "full"
    elif p in cross:
        c = "compiler"; touched.add(p)
    elif p.startswith("corpus/"):
        rest = p[len("corpus/"):]
        if rest in TABLES:
            c = "corpus"; step_all.add(TABLES[rest])
        elif rest == "skips.expected":
            c = "corpus"; step_all.update(SKIPS_STEPS)
        elif p.endswith(".md"):
            c = "docs"
        elif p.endswith(".bc") or p.endswith(SIDECARS) or re.fullmatch(r"corpus/(reports|trusted|copies)/[^/]+\.txt", p):
            c = "corpus"; touched.add(p)
        else:
            c = "full"
    elif p.startswith("lib/"):
        c = "compiler"
    elif p.startswith("book/"):
        c = "book"
    elif p.startswith("research/"):
        c = "research"
    elif p.startswith(("docs/", "bench/", "experiments/", ".github/")) or p in ("SPEC.md", "Brewfile") or p.endswith(".md"):
        c = "docs"
    elif p.endswith(".lean") and p.split("/")[0].removesuffix(".lean") in LIBS:
        c = "compiler"
    else:
        c = "full"
    classes[p] = c
    if c == "full" and not (p in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "Makefile")
                            or (name is not None and name in MACHINERY)):
        unknown.append(p)

present = set(classes.values())
if not base or why:
    tier = "full"
else:
    tier = max(present, key=ORDER.index) if present else "docs"

steps = {}            # step -> None (every program) or set of files


def every(names):
    for s in names:
        steps[s] = None


def on(name, files):
    if not files:
        return
    if name in steps and steps[name] is None:
        return
    steps.setdefault(name, set()).update(files)


every(A)
build = "none"
if tier == "full":
    every(FULL)
    build = "all"
else:
    if "book" in present:
        every(["book doc-tests", "book build"])
        build = "bins"
    if "research" in present:
        every(L)
        build = "all"
    if "compiler" in present or "scripts" in present:
        every(C + X)
        build = "bins"
    if "compiler" in present:
        build = "all"
        if any(classes[p] == "compiler" and p.endswith(".lean") or p.startswith("scripts/axioms/") for p in classes):
            every(L)
        closure = r_closure()
        r_paths = [p for p in paths if p in closure or p.startswith("lib/")
                   or (p in cross and "Frontend/Check/CrossCheck.lean" in closure)]
        if r_paths:
            every(R)
    every(sorted(step_all))
    if step_all & set(L):
        build = "all"
    if touched:
        build = "all" if build == "all" else "bins"
        # A program's report, trust and copy files are checked with it.
        progs = set()
        for t in touched:
            if t.endswith(".bc"):
                progs.add(t)
            elif t.endswith(SIDECARS):
                progs.add(t.rsplit(".", 1)[0] + ".bc")
        for prog in list(progs):
            if re.fullmatch(r"corpus/[^/]+\.bc", prog):
                stem = os.path.basename(prog)[:-3]
                for d in ("reports", "trusted", "copies"):
                    f = f"corpus/{d}/{stem}.txt"
                    if os.path.exists(f):
                        touched.add(f)
        exists = lambda f: os.path.exists(f)
        programs = sorted(f for f in progs if is_program(f) and exists(f))
        checked = sorted(set(programs) | {f for f in touched if exists(f) and (
            f in corpus_set("reject") or f in corpus_set("pending") or f.endswith(".txt"))})
        parsed = sorted(set(programs) | {f for f in touched if exists(f) and f in corpus_set("fail")})
        renamed = sorted({f for f in progs | touched if f.endswith(".bc") and exists(f)})
        on("parse corpus", parsed)
        on("check corpus", checked)
        on("renaming", renamed)
        for s in ("corpus (Backend2)", "corpus (old backend)", "native facts", "native"):
            on(s, programs)
        if set(programs) & native_tail():
            every(["native"])
        every(["clause kinds", "handled names", "cell classes", "sugar pairs", "layout rejects"])

if build == "none" and any(v is not None or k not in A for k, v in steps.items()):
    build = "bins"

# The plan, in ci-local's step order.
order = ["compile scaling"] + FULL + ["corpus (Backend2, final)", "corpus (old backend, final)"]
seen = [s for s in dict.fromkeys(order) if s in steps]
assert set(seen) == set(steps), sorted(set(steps) - set(seen))
cut = ""
if tier in ("compiler", "scripts") or (tier != "full" and ("compiler" in present or "scripts" in present)):
    cut = "cut 2" + (f", +R: {', '.join(sorted({p.split('/')[0] + '/' for p in r_paths}))}" if r_paths else "")
counts = {}
for p in paths:
    top = p.split("/")[0] + ("/" if "/" in p else "")
    counts[top] = counts.get(top, 0) + 1
summary = ", ".join(f"{k} {v}" for k, v in sorted(counts.items()))
progs_n = len(steps.get("corpus (Backend2)") or []) if isinstance(steps.get("corpus (Backend2)"), set) else 0
basetxt = f"vs origin/main {base[:8]}" if base and not why else f"(no base: {why})"
line = f"gate tier: {tier}{' (' + cut + ')' if cut and tier != 'full' else ''} {basetxt}; {len(paths)} path(s)" + \
       (f": {summary}" if summary else "") + (f"; {progs_n} touched program(s)" if progs_n else "")
if unknown:
    line += f"; unrecognised, so full: {', '.join(unknown[:5])}{' …' if len(unknown) > 5 else ''}"
left_steps = [s for s in FULL if s not in steps]
partial = [s for s in FULL if isinstance(steps.get(s), set)]
left = []
if left_steps:
    left.append(", ".join(left_steps))
if partial:
    left.append(", ".join(partial) + " on untouched programs")
lefttxt = "left to the daily run: " + ("; ".join(left) if left else "nothing")

if plan:
    print(f"base {base}" if base and not why else f"base none {why}")
    print(f"tier {tier}")
    print(f"build {build}")
    for s in seen:
        v = steps[s]
        print("run " + s if v is None else "run " + s + "\t" + "\t".join(sorted(v)))
    print(f"line {line}")
    print(f"left {lefttxt}")
else:
    print(line)
    print(f"  build: {build}")
    for s in seen:
        v = steps[s]
        print(f"  {s}: " + ("all" if v is None else ", ".join(sorted(v))))
    print(f"({lefttxt})")
