#!/usr/bin/env bash
# The project's gate, run locally. Needs elan and wasmtime; mdbook is optional (the book build is
# skipped with a notice if absent), and so is a C compiler for the native target
# (scripts/compile-native.sh says so and passes).
#
#     scripts/ci-local.sh             the per-PR gate (`make gate`): the steps the change's tier
#                                     names (scripts/gate-tier.sh), run before opening a PR
#     scripts/ci-local.sh --full      the full gate (`make gate-full`): every step
#     scripts/ci-local.sh --source    the full gate, and the source stage on every program and
#                                     book block, re-verifying every golden
#     scripts/ci-local.sh --changed   for iteration only: the sanity gate's steps the changes since
#                                     origin/main can affect (below) (`make gate-fast`)
#     … --no-cache                    with any of the above: run every unit, neither reading nor
#                                     writing the result cache (`make gate-full-nocache`; also
#                                     `GATE_CACHE=0`)
#     … --plan                        with any of the above: print the tier, the build and each
#                                     step's command, and run nothing (every gate prints the tier
#                                     and the step list before it builds)
#     … --record-cache                with any of the above: run every unit and record its passes,
#                                     reading none (`make gate-full-record`, the daily run on main;
#                                     also `GATE_CACHE=record`)
#
# The result cache (scripts/gate_cache.py). Every unit of work a step has, one program of one
# step (each job of scripts/par.sh) or a whole step that is not per program, has a key: a sha256
# over everything it reads (the binaries `bcc` and `bcc-counts` and the library they read, or the
# Lean sources and Lake's configuration; every file under scripts/ and the Makefile; the tools'
# versions; the `BC_*`, `BCC_*` and `CI_LOCAL_*` variables; the step's mode; and the unit's own
# files: a program with its sidecars, goldens, reports and table rows). A unit whose key has a
# recorded pass in `${GATE_CACHE_DIR:-~/repos/.gate-cache}` (shared by every worktree) is
# replayed, its output and side files as the run gave them, instead of run; a unit that passes is
# recorded. A failure is never recorded, nor a unit that runs the source interpreter or writes a
# key, nor any unit of a writing mode (`--write-goldens`, `--write-counts`, `--write-keys`,
# `--write`) or of `--source`. The steps that always run: compile scaling (it measures time),
# spec files, judgment freeze, assumptions, layout rejects and the book build. The summary line
# counts the units replayed and run. scripts/check-gate-cache.sh shows that a change to each kind
# of input misses.
#
# The per-PR gate (no mode; `make gate`). scripts/gate-tier.sh reads the paths changed since the
# merge base with origin/main (after a fetch; or `CI_LOCAL_BASE`) and names a tier (docs, book,
# corpus, research, scripts, compiler, full) and, for each step, whether it runs on every program,
# on the programs the change touches, or not at all; it prints one line saying so, which the gate
# prints first and again with its verdict, followed by what it left to the daily full gate on main
# (scripts/gate-daily.sh). A `full` tier (the toolchain, the gate's own machinery, a path no rule
# knows, or no merge base) is the full gate. scripts/check-gate-tier.sh (`gate tiers`) tests the
# tiers.
#
# The sanity gate (`gateSteps` below; now the set `--changed` draws from) checks that the library builds; hygiene (no forbidden
# keyword, every declaration's axioms within propext, Classical.choice and Quot.sound) and the
# axioms of the theorems SPEC.md names (listed in `scripts/axioms/*.names`, read by
# `gate-census axiom-report`); the typing-judgment freeze, the hypothesis register (`assumptions`:
# every hypothesis a theorem takes is listed in Core/Assumptions.lean) and the new backend's import
# fence; that the result cache misses on a change to each kind of input (`result cache`,
# scripts/check-gate-cache.sh); that every type comparison goes through the one `[α]` helper (`type equality`); that the
# corpus parses and checks, and elaborates the same under a renaming of its binders (`renaming`);
# and that every corpus program, compiled to WebAssembly
# by each backend, prints its golden output with `live 0`: by Backend2, the default
# (`corpus (Backend2, final)`, `compile-backend2.sh --final`), and by the old backend, checked until
# it is retired in N7 (`corpus (old backend, final)`, `compile-corpus.sh --final`); no
# intermediate-IR interpreter runs and no counts, except to name the first differing stage of a
# program whose WebAssembly run is wrong. The full gate runs every
# step in `steps`, the two corpus runs at every stage with their counts (each against its own
# table: `corpus/counts-backend2.expected`, `corpus/counts.expected`), the kernel programs on the
# old backend, the compile-time guard on Backend2 (`compile scaling`), and the tree archive
# (`research archive`: `research/tree` builds and its registered names' axioms, scripts/check-research.sh).
#
# The source stage. A corpus program's `.out` and a book block's `-- answer:` are goldens: the
# output of `Support`'s interpreter (`bcc interp`), the reference semantics. Every compiled stage
# a step runs is checked against the golden. The interpreter itself is slow (minutes on the largest
# programs), so by default it runs only where a golden is unverified: where no key is recorded
# for it, or the recorded key is not the current one, a key covering the elaborated term the
# interpreter runs, its input and the interpreter's source (scripts/source-stage.sh). Every gate
# follows this rule; with `--source`, it runs on every program and book block,
# and every golden is re-verified. `--changed` never runs the interpreter: it lists the unverified
# programs instead.
#
# A gate builds everything (`lake build`), then (the full gate) runs the compile-time guard alone
# (it measures time), then every other step at once, each one's output printed in order as it
# finishes, with its wall time. The steps are independent: each reads the build and the sources,
# and writes only its own temporary files (and `mdbook` its `book/book`). The scripts skip their
# own `lake build` when this one has built (`CI_LOCAL_BUILT`); when the build fails, they run one
# after another, each trying its own build, as when run alone.
#
# `--changed` compares the working tree (committed, staged, unstaged and untracked files) with
# its merge base with origin/main (or with the commit `CI_LOCAL_BASE` names):
#   * a `.lean` file outside experiments/, the lakefile, the manifest or the toolchain: every
#     step of the sanity gate (the compiler imports the proofs, so every Lean change reaches it);
#   * otherwise no Lean step runs (no `lake build` of the library, no hygiene, no axioms): only
#     `lake build bcc bcc-counts gate-census`, and the sanity gate's steps whose inputs changed:
#     corpus/ or lib/ for the corpus steps, a script for its own step (source-stage.sh for the
#     corpus runs), and ci-local.sh or par.sh for all of them. Documentation alone runs nothing.
set -uo pipefail
cd "$(dirname "$0")/.."
changed=0
full=0
tiered=0
mode=""
usage() { echo "usage: scripts/ci-local.sh [--full | --source | --changed] [--no-cache | --record-cache] [--plan]"; exit 2; }
planOnly=0
for a in "$@"; do
  case "$a" in
    --no-cache) export GATE_CACHE=0 ;;
    --record-cache) export GATE_CACHE=record ;;
    --plan) planOnly=1 ;;
    --changed|--full|--source) [ -z "$mode" ] || usage; mode=$a ;;
    *) usage ;;
  esac
done
case "${GATE_CACHE:-1}" in 1|0|record) ;; *) echo "ci-local: GATE_CACHE=$GATE_CACHE: not one of 1, 0, record"; exit 2 ;; esac
# The tools line is this gate's own (below); one left in the environment is not used.
unset GATE_CACHE_TOOLS_FILE GATE_CACHE_BUILT
case "$mode" in
  "") tiered=1 ;;
  --changed) changed=1; export BCC_SOURCE=0 ;;
  --full) full=1 ;;
  --source) full=1; export BCC_SOURCE=1 ;;
esac
# The per-PR gate: the tier of the change (scripts/gate-tier.sh) names the steps, each on every
# program or on the programs the change touches. A `full` tier is the full gate.
tierLine="" tierLeft="" tierPlan=""
if [ "$tiered" = 1 ]; then
  tierPlan=$(scripts/gate-tier.sh --plan) || { echo "ci-local: scripts/gate-tier.sh failed"; exit 1; }
  tierLine=$(printf '%s\n' "$tierPlan" | sed -n 's/^line //p')
  tierLeft=$(printf '%s\n' "$tierPlan" | sed -n 's/^left //p')
  tierName=$(printf '%s\n' "$tierPlan" | sed -n 's/^tier //p')
  tierBuild=$(printf '%s\n' "$tierPlan" | sed -n 's/^build //p')
  echo "$tierLine"
  [ "$tierName" != full ] || { tiered=0; full=1; }
fi
# The files a tiered step runs on (none: every program), from the plan's `run <step>\t<file>…`.
tierFiles() { printf '%s\n' "$tierPlan" | awk -F'\t' -v s="run $1" '$1 == s { for (i = 2; i <= NF; i++) printf "%s ", $i }'; }
# A change that reaches the reference semantics or the compiler needs the full gate.
reach=""
if [ "$full" = 0 ] && [ "$tiered" = 0 ] && base=${CI_LOCAL_BASE:-$(git merge-base origin/main HEAD 2>/dev/null)}; then
  reach=$({ git diff --name-only "$base"; git ls-files --others --exclude-standard; } | grep -E '^(Paper|Support|Target|Pipeline|Reference|Backend)/' | head -1 || true)
  [ -z "$reach" ] || echo "ci-local: $reach (and perhaps more of Paper/, Support/, Target/, Pipeline/, Reference/, Backend/) changed since $(git rev-parse --short "$base"): \`make gate-full\` is required as well"
fi
scripts/lake-packages.sh check
start=$SECONDS
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
# The result cache's count of units replayed and run (scripts/gate_cache.py).
export GATE_CACHE_STATS=$out/cache-stats
: > "$GATE_CACHE_STATS"
fail=0
step() {
  local name="$1" t=$SECONDS; shift
  printf '==> %s\n' "$name"
  if "$@"; then printf '    ok: %s (%ss)\n' "$name" $((SECONDS - t)); else printf '    FAILED: %s (%ss)\n' "$name" $((SECONDS - t)); fail=1; fi
}

# The full gate's steps after the build, in the order they are reported: name, then command.
steps=(
  "hygiene + axioms" "scripts/check-hygiene.sh"
  "spec files"       "scripts/check-spec-files.sh"
  "judgment freeze"  "scripts/check-judgments.sh"
  "assumptions"      "scripts/check-assumptions.sh"
  "type equality"    "scripts/check-type-eq.sh"
  "axiom report"     "python3 scripts/gate_cache.py step axiom-report lean -- scripts/gate-census.sh axiom-report"
  "insertion pins"   "scripts/check-pins.sh"
  "research archive" "scripts/check-research.sh"
  "parse corpus"     "scripts/parse-corpus.sh"
  "check corpus"     "scripts/check-corpus.sh"
  "clause kinds"     "scripts/check-kinds.sh"
  "handled names"    "scripts/check-handled.sh"
  "cell classes"     "scripts/check-cells.sh"
  "corpus (Backend2)"        "scripts/compile-backend2.sh"
  "corpus (Backend2, final)" "scripts/compile-backend2.sh --final"
  "corpus (old backend)"     "scripts/compile-corpus.sh"
  "corpus (old backend, final)"  "scripts/compile-corpus.sh --final"
  "kernel (old backend)"     "scripts/compile-kernel.sh"
  "backend2 fence"   "scripts/check-backend2.sh"
  "layout rejects"   "scripts/check-layout-reject.sh"
  "native facts"     "scripts/native-facts.sh"
  "native"           "scripts/compile-native.sh"
  "sugar pairs"      "scripts/check-sugar.sh"
  "respell pairs"    "scripts/check-respell.sh"
  "let mut combos"   "scripts/mut-combos.py --gate --count 400"
  "renaming"         "scripts/alpha-check.py"
  "book doc-tests"   "scripts/book-doctest.sh"
  "book build"       "mdbook build book"
  "result cache"     "scripts/check-gate-cache.sh"
  "gate tiers"       "scripts/check-gate-tier.sh"
)
# The sanity gate's steps (`make gate`, `--changed`). The corpus runs named `final` are its own:
# the full gate runs the corpus at every stage instead.
gateSteps=("hygiene + axioms" "spec files" "judgment freeze" "assumptions" "axiom report" "type equality" "parse corpus"
  "check corpus" "respell pairs" "renaming" "corpus (Backend2, final)" "corpus (old backend, final)" "backend2 fence" "result cache" "gate tiers")
if [ "$full" = 1 ]; then
  everyStep=("compile scaling")
  for ((i = 0; i < ${#steps[@]}; i += 2)); do
    case "${steps[i]}" in *"final)") ;; *) everyStep+=("${steps[i]}") ;; esac
  done
elif [ "$tiered" = 1 ]; then
  everyStep=()
  while IFS= read -r l; do everyStep+=("$l"); done < <(printf '%s\n' "$tierPlan" | awk -F'\t' '/^run / { print substr($1, 5) }')
else
  everyStep=("${gateSteps[@]}")
fi
inGate() { local s; for s in "${everyStep[@]}"; do [ "$s" = "$1" ] && return 0; done; return 1; }

# --changed: the steps to run (`|name|name|…|`), from the paths changed.
all=1
run="|"
add() { local s; for s in "$@"; do run="$run$s|"; done; }
if [ "$changed" = 1 ]; then
  base=${CI_LOCAL_BASE:-$(git merge-base origin/main HEAD)} || { echo "ci-local: no merge base with origin/main"; exit 1; }
  files=$({ git diff --name-only "$base"; git ls-files --others --exclude-standard; } | sort -u)
  lean=0
  for f in $files; do
    case "$f" in
      experiments/*) ;;
      *.lean|scripts/axioms/*.names|lakefile.toml|lake-manifest.json|lean-toolchain) lean=1 ;;
    esac
  done
  if [ "$lean" = 0 ]; then
    all=0
    corpus=("parse corpus" "check corpus" "respell pairs" "renaming" "corpus (Backend2, final)" "corpus (old backend, final)")
    for f in $files; do
      case "$f" in
        corpus/*|lib/*|scripts/corpus-set.sh) add "${corpus[@]}" ;;
        scripts/ci-local.sh|scripts/par.sh|scripts/gate_cache.py) add "${everyStep[@]}" ;;
        scripts/parse-corpus.sh) add "parse corpus" ;;
        scripts/check-corpus.sh) add "check corpus" ;;
        scripts/check-respell.sh) add "respell pairs" ;;
        scripts/compile-corpus.sh|scripts/source-stage.sh|scripts/interp-digest.sh) add "corpus (old backend, final)" ;;
        scripts/compile-backend2.sh) add "corpus (Backend2, final)" "result cache" ;;
        scripts/check-backend2.sh) add "backend2 fence" ;;
        scripts/check-gate-cache.sh) add "result cache" ;;
        scripts/gate-tier.sh|scripts/check-gate-tier.sh) add "gate tiers" ;;
        scripts/check-assumptions.sh) add "assumptions" ;;
        scripts/check-type-eq.sh|scripts/type-eq.allow|scripts/gate-census.sh) add "type equality" ;;
        scripts/alpha-check.py) add "renaming" ;;
        SPEC.md|docs/changelog/*|docs/status/*|scripts/changelog.sh|scripts/status.sh|scripts/check-spec-files.sh) add "spec files" ;;
      esac
    done
  fi
  echo "ci-local --changed: $(printf '%s\n' "$files" | grep -c . || true) path(s) changed since $(git rev-parse --short "$base")"
fi
# Hygiene and the axioms read only Lean sources: they run exactly when every step does.
wanted() {
  inGate "$1" || return 1
  [ "$all" = 1 ] && return 0
  case "$1" in "hygiene + axioms"|"axiom report") return 1 ;; esac
  case "$run" in *"|$1|"*) return 0 ;; *) return 1 ;; esac
}

# The plan, before anything is built or run: the build and every step (with its files when it runs
# on some programs only). `--plan` prints each step's command and stops there.
planBuild=${tierBuild:-$([ "$all" = 1 ] && echo all || echo bins)}
planSteps=""
wanted "compile scaling" && planSteps="compile scaling"
for ((i = 0; i < ${#steps[@]}; i += 2)); do
  wanted "${steps[i]}" || continue
  n=0; [ "$tiered" = 0 ] || n=$(tierFiles "${steps[i]}" | wc -w | tr -d ' ')
  planSteps="$planSteps${planSteps:+, }${steps[i]}$([ "$n" = 0 ] || echo " ($n file(s))")"
  if [ "$planOnly" = 1 ]; then
    c=${steps[i + 1]}; [ "$tiered" = 0 ] || c="$c $(tierFiles "${steps[i]}")"
    echo "  ${steps[i]}: $c"
  fi
done
echo "ci-local plan: build $planBuild; steps: ${planSteps:-none}"
[ "$planOnly" = 0 ] || exit 0
# The machine-wide job pool (scripts/slot), shared by every gate on the machine: each `par` job,
# each subprocess of the Python pools and `gate-census` take their slots there; the serial steps
# below take one; the build and the compile-time guard take the whole CPU pool. `SLOT_OFF=1`
# turns it off.
# The pool is on when scripts/slot answers; otherwise SLOT_OFF=1 for every step (scripts/par.sh
# and scripts/slotpool.py decide the same way when run alone).
pool=""
if [ "${SLOT_OFF:-}" = 1 ]; then echo "ci-local: job pool off (SLOT_OFF=1)"
elif size=$(scripts/slot -s 2>&1); then
  read -r poolN poolM <<< "$size"; pool=scripts/slot
  echo "ci-local: job pool on ($poolN CPU slots, $poolM GB, shared by every gate on the machine)"
else
  export SLOT_OFF=1; echo "ci-local: job pool off (scripts/slot -s: ${size:-no answer})"
fi
# slotted CPU MEM CMD…: CMD in the pool, or CMD itself when the pool is off.
slotted() { local c=$1 m=$2; shift 2; if [ -n "$pool" ]; then "$pool" -c "$c" -m "$m" -- "$@"; else "$@"; fi; }
# The build: nothing when Lake finds every target up to date (`--no-build`, exit 3 when one is
# not); otherwise the build itself, holding the whole CPU pool (Lake starts a Lean process per
# core and has no job limit).
build() {
  local rc=0
  [ -n "$pool" ] || { lake build "$@"; return; }
  lake build --no-build "$@" || rc=$?
  [ "$rc" = 3 ] || return "$rc"
  # Its memory tokens bound the physical memory it adds: 16 GB, twice the 7.7 GB rise measured on
  # the largest rebuild (an edit to Core/Judgment.lean: 346 modules, 15 processes, 525 s; the
  # gate30 verification's results.md, T6b: vm_stat anonymous + wired + compressor pages). Its summed
  # RSS (61.5 GB) is not the measure: it counts the mapped .oleans once per Lean process, though
  # they share their pages.
  slotted 999 16 lake build "$@"
}
if [ "$tiered" = 1 ] && [ "$tierBuild" = none ]; then echo "==> build: none (no step of this tier reads the build)"
elif [ "$tiered" = 1 ] && [ "$tierBuild" = bins ]; then step "build (bcc, bcc-counts)" build bcc bcc-counts gate-census
elif [ "$all" = 1 ]; then step "build" build
else step "build (bcc, bcc-counts)" build bcc bcc-counts gate-census; fi
built=$fail
# CI_LOCAL_BUILT says this invocation built the binaries; a tier that builds nothing does not say it.
[ "$built" = 0 ] && { [ "$tiered" = 1 ] && [ "$tierBuild" = none ] || export CI_LOCAL_BUILT=1; }
# When the build fails, the steps run one after another, each trying its own build, with the cache
# off: the binaries left in .lake are not this tree's, and nothing is replayed or recorded.
if [ "$built" != 0 ] && [ "${GATE_CACHE:-1}" != 0 ]; then export GATE_CACHE=0; cachenote=" (the build failed)"; fi
# The tools in every cache key, found once for the whole gate after the build (they do not change
# during it).
if [ "$built" = 0 ] && [ "${GATE_CACHE:-1}" != 0 ]; then
  python3 scripts/gate_cache.py tools > "$out/tools" && export GATE_CACHE_TOOLS_FILE=$out/tools
fi

# The censuses that read the Lean environment: one `gate-census` process for every step that asks
# (scripts/gate-census.sh), started by the first step that runs one. The research archive's runs
# on its own, after that step builds the archive.
# The directory is this gate's: it holds this gate's token, and gate-census.sh reads no other.
unset GATE_CENSUS_DIR GATE_CENSUS_ALL GATE_CENSUS_TOKEN
if [ "$built" = 0 ]; then
  export GATE_CENSUS_DIR="$out/census" GATE_CENSUS_ALL="" GATE_CENSUS_TOKEN="$$.$RANDOM.$SECONDS"
  mkdir -p "$GATE_CENSUS_DIR" && echo "$GATE_CENSUS_TOKEN" > "$GATE_CENSUS_DIR/token"
  wanted "hygiene + axioms" && GATE_CENSUS_ALL+=" axioms axioms+scripts/census-neg/axioms.lean"
  wanted "axiom report" && GATE_CENSUS_ALL+=" axiom-report"
  wanted "type equality" && GATE_CENSUS_ALL+=" type-eq type-eq+scripts/census-neg/type-eq.lean"
  wanted "insertion pins" && GATE_CENSUS_ALL+=" pins pins+scripts/census-neg/pins.lean"
fi

# The compile-time guard measures time: it runs holding the whole CPU pool, alone on the machine.
if wanted "compile scaling"; then step "compile scaling" slotted 999 1 scripts/compile-scaling.sh --guard; fi
# The steps that run their programs one at a time take one slot for the whole step.
serial() { case "$1" in "layout rejects") return 0 ;; *) return 1 ;; esac; }

mdbook=1; command -v mdbook >/dev/null || mdbook=0
names=(); pids=()
for ((i = 0; i < ${#steps[@]}; i += 2)); do
  name=${steps[i]}; cmd=${steps[i + 1]}
  wanted "$name" || continue
  [ "$tiered" = 0 ] || cmd="$cmd $(tierFiles "$name")"
  if [ "$name" = "book build" ] && [ "$mdbook" = 0 ]; then continue; fi
  if [ "$built" = 0 ]; then
    k=${#names[@]}
    pre=(); serial "$name" && pre=(slotted 1 1)
    (t=$SECONDS; ${pre[@]+"${pre[@]}"} $cmd > "$out/$k.log" 2>&1; rc=$?; echo $((SECONDS - t)) > "$out/$k.time"; exit $rc) &
    names+=("$name"); pids+=($!)
  else
    pre=(); serial "$name" && pre=(slotted 1 1)
    step "$name" ${pre[@]+"${pre[@]}"} $cmd
  fi
done
for ((k = 0; k < ${#names[@]}; k++)); do
  printf '==> %s\n' "${names[k]}"
  if wait "${pids[k]}"; then rc=0; else rc=1; fi
  cat "$out/$k.log"
  t=$(cat "$out/$k.time" 2>/dev/null || echo "?")
  if [ "$rc" = 0 ]; then printf '    ok: %s (%ss)\n' "${names[k]}" "$t"; else printf '    FAILED: %s (%ss)\n' "${names[k]}" "$t"; fail=1; fi
done
if [ "$mdbook" = 0 ] && wanted "book build"; then echo "==> book build: skipped (mdbook not installed)"; fi
if [ "$all" = 0 ]; then
  skipped=""
  for s in "${everyStep[@]}"; do wanted "$s" || skipped="$skipped${skipped:+, }$s"; done
  [ -z "$skipped" ] || echo "==> skipped (no change reaches them): $skipped"
fi

echo
tag="ci-local"; [ "$changed" = 1 ] && tag="ci-local --changed"; [ "$full" = 1 ] && tag="ci-local --full"
[ "${BCC_SOURCE:-}" = 1 ] && [ "$full" = 1 ] && tag="ci-local --source"
[ -z "$tierLine" ] || tag="ci-local [tier $tierName$(printf '%s' "$tierLine" | sed -n 's/^gate tier: [a-z]* (\(cut [^)]*\)).*/, \1/p')]"
[ "${GATE_CACHE:-1}" = 0 ] && [ -z "${cachenote:-}" ] && tag="$tag --no-cache"
[ "${GATE_CACHE:-1}" = record ] && tag="$tag --record-cache"
if [ "${GATE_CACHE:-1}" = 0 ]; then cache="cache off${cachenote:-}"
else cache=$(awk '{ r += $1; n += $2; f += $3 } END { printf "cache: %d unit(s) replayed, %d run", r, n; if (f) printf "; WARNING: %d pass(es) could not be recorded (store not writable)", f }' "$GATE_CACHE_STATS"); fi
if [ -n "$pool" ]; then cache="$cache; job pool $poolN/$poolM GB"; else cache="$cache; job pool off"; fi
if [ "$fail" -eq 0 ]; then echo "$tag: ALL PASSED ($((SECONDS - start))s; $cache)"; else echo "$tag: FAILURES (see above) ($((SECONDS - start))s; $cache)"; fi
[ "$changed" = 1 ] && echo "(--changed is for iteration only: the sanity gate, scripts/ci-local.sh, runs before a PR)"
if [ -n "$tierLine" ]; then echo "$tierLine"; echo "($tierLeft)"
elif [ "$full" = 0 ]; then echo "(the sanity gate: \`make gate-full\` runs every check; \`make verify-goldens\` re-verifies every golden)"; fi
[ -z "$reach" ] || echo "($reach changed: \`make gate-full\` is required as well)"
exit "$fail"
