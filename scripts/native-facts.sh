#!/usr/bin/env bash
# The new backend's native facts (SPEC §50), on the corpus. For every corpus program
# (`scripts/corpus-set.sh`) in the new backend's fragment, as scripts/compile-backend2.sh runs them
# (each skip printed, and with no file named pinned in `corpus/skips.expected`; a program with no
# golden fails):
#
#   * the differential run: the program built with its parameters' facts left out
#     (`bcc run --backend new --native --no-facts`) prints the golden standard output and error and
#     ends with the golden status, as the build with them (compile-backend2.sh's native stage) must;
#     both are `clang -O2`;
#   * `alwaysinline`: no call of a function the word IR asks to inline (`Fn.inline`) is left in the
#     `clang -O2` IR of the build with its facts;
#   * local placement: frame slots plus checked register-promoted locals per run are at least the
#     old backend's, in every program where the old backend has a scoped cell (`bcc-counts
#     --sites`' `scoped-cells`): physical frames plus checked locals promoted to registers;
#   * the lend bits (`Fn.lendEncl`): every function with a borrow fact is a source function, the
#     code of a source `λ`, thunk or `&` (`lam`, `thunk`, `with`). The functions are read off the
#     word IR's `Fn.facts` (`bcc trusted`'s `LendEnclosesFn` lines), not the emitted attributes,
#     which the tail-call classes filter. The regression pair (`async-r1-cancel-finaliser-writes`,
#     `async-r1-step-lend`) each has a function the conversion makes that takes a `mut` borrow
#     beside its owner (`cancel 1.0`, `step`), and it has no fact;
#   * the `willreturn` class (`Fn.willreturn`): read off the word IR (`bcc trusted`'s `CallRelated and HostStack`
#     lines), every function in it a source function, and exactly the functions the emitted IR
#     marks `willreturn mustprogress`; each calls no runtime function but `bc_free` and only
#     functions of the class, checked on the emitted IR. `native-willreturn.bc` keeps a function in
#     the class and an allocating and a writing one outside it.
#
#     scripts/native-facts.sh [file.bc…]
set -euo pipefail
cd "$(dirname "$0")/.."
files=("$@")
named=1
[ ${#files[@]} -gt 0 ] || { named=0; list=$(scripts/corpus-set.sh); files=(); while IFS= read -r f; do [ -z "$f" ] || files+=("$f"); done <<< "$list"; }
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
if ! cc=$("$bcc" cc 2>/dev/null); then echo "native-facts: no C compiler: skipped"; exit 0; fi
export cc
. scripts/par.sh
export tmp; tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
: > "$tmp/skips"

argsOf() {
  args=()
  local a=${1%.bc}.args line
  [ -f "$a" ] || return 0
  while IFS= read -r line || [ -n "$line" ]; do args+=("$line"); done < "$a"
}
statusOf() {
  local s=${1%.bc}.status
  if [ -f "$s" ]; then tr -d ' \n' < "$s"; else echo 0; fi
}

program() {
  local f=$1 w=${PAR_TMP:-$tmp} base in err rc fns fn left old new sigs
  if grepq -E '^(--|#) check: parse-only' "$f"; then echo "$f: parse-only, skipped"; echo "parse-only $f" >> "$PAR_SIDE/skips"; return 0; fi
  if ! grepq -E '^(main|fn main\()' "$f"; then echo "$f: no main, skipped"; echo "no-main $f" >> "$PAR_SIDE/skips"; return 0; fi
  base=${f%.bc}
  if [ ! -f "$base.out" ]; then
    echo "$f: no golden $base.out: write it from the source stage with \`scripts/compile-corpus.sh --write-goldens $f\`"
    return 1
  fi
  if ! "$bcc" compile --backend new --target native "$f" -o "$w/on.ll" > "$w/log" 2>&1; then
    if grepq 'outside the pure fragment' "$w/log"; then
      echo "$f: outside the new backend's fragment, skipped"; echo "outside-fragment $f" >> "$PAR_SIDE/skips"; return 0
    fi
    echo "$f: $(head -3 "$w/log")"; return 1
  fi
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  err=/dev/null; [ -f "$base.err" ] && err="$base.err"
  argsOf "$f"
  rc=0
  "$bcc" run --backend new --native --no-facts "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$?
  if [ "$rc" != "$(statusOf "$f")" ] || ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
    echo "$f: without its facts the native build differs from the golden (status $rc)"
    return 1
  fi
  # `alwaysinline`: the functions asked for, and no call of one left after `-O2`.
  fns=$(sed -n 's/^define internal .* @\(f[0-9]*\)(.*) nounwind alwaysinline .*/\1/p' "$w/on.ll")
  if [ -n "$fns" ]; then
    $cc -O2 -S -emit-llvm -w "$w/on.ll" -o "$w/opt.ll" 2>/dev/null || par_nostore
    left=""
    for fn in $fns; do
      grepq "call .*@$fn(" "$w/opt.ll" && left="$left $fn"
    done
    if [ -n "$left" ]; then echo "$f: alwaysinline, but called after -O2:$left"; return 1; fi
  fi
  # Physical frame slots plus checked register-promoted locals must cover the old backend's
  # frame slots. Both counts are dynamic; a promoted local is not an actual frame slot.
  old=""; new=""; registers=0
  # A program the old backend refuses (`-- check: old-backend-refuses`) has no old count to compare.
  # (A failed tool here is never recorded in the cache: `par_nostore`.)
  sites=""
  if ! grepq -E '^(--|#) check: old-backend-refuses' "$f"; then sites=$("$bccCounts" --sites "$f" 2>/dev/null) || par_nostore; fi
  if ! grepq -E '^(--|#) check: old-backend-refuses' "$f" && [ "$(printf '%s\n' "$sites" | sed -n 's/.*scoped-cells framed \([0-9]*\).*/\1/p')" != 0 ]; then
    old=$("$bccCounts" --backend old --frames "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>/dev/null | sed -n 's/^slots //p')
    new=$("$bccCounts" --backend new --frames "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>/dev/null | sed -n 's/^slots //p')
    if [ -z "$old" ] || [ -z "$new" ]; then echo "$f: no frame slot counts (old '$old', new '$new')"; return 1; fi
    if [ "$new" -lt "$old" ]; then
      registers=$("$bccCounts" --backend new --registers "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>/dev/null | sed -n 's/^registers //p')
      if [ -z "$registers" ] || [ "$((new + registers))" -lt "$old" ]; then
        echo "$f: $new frame slots and ${registers:-unknown} register locals per run, the old backend's $old frame slots"
        return 1
      fi
    fi
  fi
  # The lend bits: the functions with a borrow fact, from the word IR (`bcc trusted`).
  "$bcc" trusted "$f" > "$w/trusted" 2>/dev/null || { echo "$f: bcc trusted failed"; return 1; }
  awk '/^backend: LendEnclosesFn/ { on = 1; next } on && /^  / { print; next } { on = 0 }' \
    "$w/trusted" > "$w/facted"
  left=$(sed -n 's/^  f[0-9]* (\(.*\))$/\1/p' "$w/facted" | grep -vxE 'lam|thunk|with' || true)
  if [ -n "$left" ]; then
    echo "$f: a borrow fact at a function the conversion makes: $(echo $left)"; return 1
  fi
  case "$f" in
    corpus/async-r1-cancel-finaliser-writes.bc) pair="cancel 1.0" ;;
    corpus/async-r1-step-lend.bc) pair="step" ;;
    *) pair="" ;;
  esac
  if [ -n "$pair" ]; then
    "$bcc" lir "$f" > "$w/lir" 2>/dev/null || { echo "$f: bcc lir failed"; return 1; }
    sigs=$(grep -E "^f[0-9]+ $pair\(" "$w/lir" || true)
    if ! grep -q "mut i32" <<< "$sigs" || ! grep -q "ref i32" <<< "$sigs"; then
      echo "$f: the regression's \`$pair\` no longer takes a mut borrow beside its owner"; return 1
    fi
    if grepq "($pair)\$" "$w/facted"; then echo "$f: \`$pair\` has a borrow fact"; return 1; fi
  fi
  # The `willreturn` class: read off the word IR (`bcc trusted`'s `CallRelated and HostStack` lines), every one a
  # source function, and exactly the functions the emitted IR marks. Each marked function calls no
  # runtime function but `bc_free` and only marked functions, checked on the emitted IR.
  awk '/^backend \(native\): CallRelated and HostStack/ { on = 1; next } on && /^  / { print; next } { on = 0 }' \
    "$w/trusted" > "$w/wr"
  left=$(sed -n 's/^  f[0-9]* (\(.*\))$/\1/p' "$w/wr" | grep -vxE 'lam|thunk|with' || true)
  if [ -n "$left" ]; then
    echo "$f: willreturn at a function the conversion makes: $(echo $left)"; return 1
  fi
  want=$(sed -n 's/^  f\([0-9]*\) .*/\1/p' "$w/wr" | while read -r i; do echo "f$((i + 1))"; done | sort)
  have=$(sed -n 's/^define internal .* @\(f[0-9]*\)(.*) nounwind.* willreturn mustprogress .*/\1/p' \
    "$w/on.ll" | sort)
  if [ "$want" != "$have" ]; then
    echo "$f: the emitted willreturn functions ($(echo $have)) are not the word IR's class ($(echo $want))"
    return 1
  fi
  bad=$(awk -v set="$(echo $have)" '
    BEGIN { n = split(set, a, " "); for (i = 1; i <= n; i++) wr["@" a[i]] = 1 }
    /^define / { fn = $0; sub(/\(.*/, "", fn); sub(/.*@/, "@", fn); inwr = (fn in wr); next }
    /^}/ { inwr = 0; next }
    inwr && /call / {
      c = $0; sub(/^.*call [^@]*/, "", c); sub(/\(.*/, "", c)
      if (c ~ /^@bc_/ && c != "@bc_free") print fn " calls " c
      else if (c ~ /^@f[0-9]+$/ && !(c in wr)) print fn " calls " c
    }' "$w/on.ll")
  if [ -n "$bad" ]; then echo "$f: a willreturn function leaves the class: $(echo $bad)"; return 1; fi
  if [ "$f" = corpus/native-willreturn.bc ]; then
    # The pair, by function: a source `λ` in the class that adds (`twice`); a source `λ` outside it
    # that calls `bc_alloc` itself (`through`); and a source `λ` outside it that calls a function
    # that calls `bc_putv` (the library's writing closures). Source `λ`s are read off `bcc lir`.
    "$bcc" lir "$f" > "$w/lir" 2>/dev/null || { echo "$f: bcc lir failed"; return 1; }
    lams=$(sed -n 's/^f\([0-9]*\) lam(.*/\1/p' "$w/lir" | while read -r i; do echo "f$((i + 1))"; done)
    out=$(awk -v set="$(echo $have)" -v lams="$(echo $lams)" '
      BEGIN { n = split(set, a, " "); for (i = 1; i <= n; i++) wr["@" a[i]] = 1
              n = split(lams, b, " "); for (i = 1; i <= n; i++) lam["@" b[i]] = 1 }
      /^define / { fn = $0; sub(/\(.*/, "", fn); sub(/.*@/, "@", fn); next }
      /^}/ { fn = ""; next }
      fn != "" && / = add i(32|64) / { adds[fn] = 1 }
      fn != "" && /call .*@bc_alloc\(/ { allocs[fn] = 1 }
      fn != "" && /call .*@bc_putv\(/ { puts[fn] = 1 }
      fn != "" && /call / { c = $0; sub(/^.*call [^@]*/, "", c); sub(/\(.*/, "", c); calls[fn, c] = 1 }
      END {
        for (g in wr) if ((g in lam) && (g in adds)) pos = 1
        for (g in lam) if (!(g in wr) && (g in allocs)) al = 1
        for (k in calls) { split(k, kc, SUBSEP); if ((kc[1] in lam) && !(kc[1] in wr) && (kc[2] in puts)) pu = 1 }
        print (pos ? "in" : "") (al ? " alloc" : "") (pu ? " put" : "") }' "$w/on.ll")
    if [ "$out" != "in alloc put" ]; then
      echo "$f: the willreturn pair is gone (class '$(echo $have)', found '$out')"; return 1
    fi
  fi
  echo "$f: ok${new:+ (frame slots $new, register locals $registers, old $old)}${fns:+ (inlined $(echo $fns | wc -w | tr -d ' '))} (facts at $(wc -l < "$w/facted" | tr -d ' ') functions, willreturn at $(wc -l < "$w/wr" | tr -d ' '))"
}
export -f program argsOf statusOf
# Each program is a unit of the result cache (scripts/par.sh; the C compiler is among its tools).
# Its skip lines are a side file (`skips`), gathered in $tmp.
export PAR_COLLECT=$tmp PAR_CACHE="native-facts cc=$cc" PAR_CACHE_NATIVE=1
par program "${files[@]}"
skipbad=0
if [ "$named" = 0 ]; then
  scripts/corpus-set.sh --skips native-facts parse-only no-main outside-fragment < "$tmp/skips" || skipbad=1
fi
echo "native facts: $par_failed failure(s)."
[ "$par_failed" -eq 0 ] && [ "$skipbad" = 0 ]
