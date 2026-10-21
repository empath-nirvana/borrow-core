#!/usr/bin/env bash
# Compile time against program size (#122). Generates programs whose `main` is k copies of one
# body, for k in 1 2 4 8 16, and compiles each with `bcc compile --timings`, which writes every
# stage's time and output size (Backend/Driver.lean, `compileWatTimed`). Prints the table of
# times per stage and scale, and each stage's fitted growth: the exponent b of time ≈ a·kᵇ, by
# least squares on log time against log k (b = 1 is linear).
#
# The body is corpus-like code, and grows a program as programs grow: more functions, more
# generators and adapters, a longer `main`. Each copy adds a generator, and four functions, each
# a loop: over a pipeline of the adapters of `lib/adapters.bc` (`corpus/gen-adapters.bc`), over
# a pipeline of generators reading an array through an `imm` borrow taken at each step
# (`corpus/axes/scope-loop-lend.bc`), and writing a cell through a `mut` borrow taken at each step. `main` gets a loop over a
# pipeline and a call of the four functions, each a div call in direct style, so `main`'s state
# machine (SPEC §14) grows by five points per copy, and a loop over the input at its end.
#
# **The new backend** (`--backend new`, SPEC §49): the programs are compiled by `bcc compile
# --backend new --timings` (`Backend2/Driver.lean`, `watTimed`), whose stages are the frontend's and
# the new backend's. The body above is stored generators and adapters throughout (a `U (pull …)`
# value, `reify` of a generator that loops: the state machines of N3), which the new backend does
# not compile, so the new backend's body is the same kind of code inside its fragment: per copy a
# `for` over a generator that does not loop and a `while`, a recursion under a handler of
# `Exhausted` and a fold, a `raise` under `to_result`, the array read through an `imm` borrow and
# the cell written through a `mut` borrow at each step of a counted loop, and a handler with state
# around a loop that performs its operation; `main` gets a `while` and a call of each in direct
# style, and the loop over the input at its end. The gate measures the new backend (the decision on
# #646: the old backend is deleted at N6), with the same limit.
#
#     scripts/compile-scaling.sh             the table and the fitted growth
#     scripts/compile-scaling.sh 1 2 4       other scales
#     scripts/compile-scaling.sh --guard     the gate's check: the 8× program compiles in at most
#                                            GUARD (default 16) times the 1× program's time
#     scripts/compile-scaling.sh --backend new [--guard]
#                                            the same, of the new backend's body by the new backend
#     scripts/compile-scaling.sh --keep DIR  leave the generated programs in DIR
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
guard=0; keep=""; backend=old
scales=()
while [ $# -gt 0 ]; do
  case "$1" in
    --guard) guard=1; shift ;;
    --backend) backend="$2"; shift 2 ;;
    --keep) keep="$2"; shift 2 ;;
    *) scales+=("$1"); shift ;;
  esac
done
[ "$guard" = 1 ] && scales=(1 8)
[ ${#scales[@]} -eq 0 ] && scales=(1 2 4 8 16)
if [ -n "$keep" ]; then tmp="$keep"; mkdir -p "$tmp"
else tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT; fi

# The program with k copies of the body: four functions and a generator per copy, and per copy
# a loop and a call of the four in `main`.
gen() {
local k=$1 i
cat <<'H'
include adapters

type List = mu X. 1 + (i32 * X)

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn squares(it: U (pull i32 1 1)) -> 1 with Yield[i32] =
  for x in it { yield(x * x) };
  ()

fn above(n: i32, it: U (pull i32 1 1)) -> 1 with Yield[i32] =
  for x in it { if n < x { yield(x) } else { () } };
  ()

fn tab(i: i32) -> i32 = i + 1

def get : !(all 'a < top. imm 'a (array i32) * i32 => i32) =
  !thunkv Fun 'a < top. return (thunkv fun (p : imm 'a (array i32) * i32) ->
    let (b, i) = p;
    withload['a, 'z, array i32, i32] b (thunkv Fun 'z < dom. return (thunkv fun (xs : array_imm 'z i32) ->
      match array_get['z, i32] (xs, i) { inl e -> let v = *e; boxed['z] v | inr _ -> boxed['z] 0 })))

fn len_alg(r: 1 + i32 * i32) -> i32 = match r { inl _ -> 0 | inr (x, n) -> n + 1 }
def len : !(List => i32) = fold_own[1 + i32 * X, i32] len_alg

type Line = mu X. 1 + (u8 * X)
fn len8_alg(r: 1 + u8 * i32) -> i32 = match r { inl _ -> 0 | inr (x, n) -> n + 1 }
def len8 : !(Line => i32) = fold_own[1 + u8 * X, i32] len8_alg

fn add_up(p: i32 * i32) -> i32 * bool =
  let (s, x) = p;
  if s + x >= 10 { (s + x, true) } else { (s + x, false) }
H
for ((i = 0; i < k; i++)); do
cat <<B

fn evens$i(n: i32) -> 1 with Yield[i32] =
  for x in range(0, n) { if x > $i { yield(x + 1) } else { () } };
  ()

fn pa$i(k: i32) -> i32 =
  let mut a = k;
  for y in take(skip(filter(map(evens$i(20), !{ x -> x * x }), !{ x -> x > 5 }), 2), 3) {
    a = a + y
  };
  a

fn pb$i(k: i32) -> i32 =
  let mut b = k;
  for p in enumerate(chain(scan(range(1, 5), 0, !{ (s, x) -> s + x }),
                           flat_map(range(0, 3), !{ n -> let g : U (pull i32 1 1) = range(0, n); g }))) {
    let (i, x) = p;
    b = b + i * x + $i
  };
  b

fn pc$i(k: i32) -> i32 =
  let mut c = k;
  for p in zip(batch(range(1, 8), 0, add_up),
               map(chunks(take_until(range(0, 100), !{ x -> x * x > 20 }), 2), len)) {
    let (x, y) = p;
    c = c + x * y + $i
  };
  c

fn pd$i(k: i32) -> i32 =
  let t = alloc(array_new[i32] (101, tab));
  let mut acc = k;
  for x in above(20, squares(range(1, 11))) { let v = get(&t, x); acc = acc + v + $i };
  let _ = free(t);
  let c = alloc(acc);
  for x in range(0, 5) { borrow mut c { m -> modify m { v -> v + x } } };
  free(c)
B
done
echo
echo "main -> i32 * i32 ="
echo "  let mut t = 0;"
echo "  let mut m = 0;"
for ((i = 0; i < k; i++)); do
  echo "  for y in take(skip(filter(map(range(0, 20), !{ x -> x * x }), !{ x -> x > 5 }), 1), 2) { t = t + y };"
  echo "  t = pd$i(pc$i(pb$i(pa$i(t))));"
done
echo "  for b in bytes(&mut stdin) { m = m + to_i32(b) };"
echo "  (t, m)"
}

# The new backend's program with k copies of its body (above): per copy a generator, a
# recursion, a raising function and five functions over them, and in `main` a `while` and a call
# of each.
gen2() {
local k=$1 i
cat <<'H'
include fail
include rec
include yield

type List = mu X. 1 + (i32 * X)

fn tab(i: i32) -> i32 = i + 1

def get : !(all 'a < top. imm 'a (array i32) * i32 => i32) =
  !thunkv Fun 'a < top. return (thunkv fun (p : imm 'a (array i32) * i32) ->
    let (b, i) = p;
    withload['a, 'z, array i32, i32] b (thunkv Fun 'z < dom. return (thunkv fun (xs : array_imm 'z i32) ->
      match array_get['z, i32] (xs, i) { inl e -> let v = *e; boxed['z] v | inr _ -> boxed['z] 0 })))

fn len_alg(r: 1 + i32 * i32) -> i32 = match r { inl _ -> 0 | inr (x, n) -> n + 1 }
def len : !(List => i32) = fold_own[1 + i32 * X, i32] len_alg

effect Log { fn log(x: i32) }
handler summing(mut s: i32): Log = { log(x) = { s = s + x; () } }
H
for ((i = 0; i < k; i++)); do
cat <<B

fn three$i(n: i32) -> 1 with Yield[i32] = yield(n); yield(n + $i); yield(n * 2)

fn fib$i(n: i32) -> i32 with Exhausted = if n < 2 { n + $i } else { fib$i(n - 1) + fib$i(n - 2) }

fn checked$i(x: i32) -> i32 with Fail[i32] = if x > 100000 { raise(x) } else { x * 2 + $i }

fn pa$i(k: i32) -> i32 =
  let mut a = k;
  for y in three$i(k) { if y > $i { a = a + y } else { () } };
  let mut j = 0;
  while j < 10 { a = a + j * $i; j = j + 1 };
  a

fn pb$i(k: i32) -> i32 =
  let f = with on_exhausted(!{ u -> 0 }) { fib$i(8) };
  let xs : List = roll inr (k, roll inr (f, roll inl ()));
  k + f + len(xs)

fn pc$i(k: i32) -> i32 =
  match with to_result { checked$i(k) } { inl v -> v | inr e -> e }

fn pd$i(k: i32) -> i32 =
  let t = alloc(array_new[i32] (101, tab));
  let mut acc = k;
  for x in 0..20 { let v = get(&t, x); acc = acc + v + $i };
  let _ = free(t);
  let c = alloc(acc);
  for x in 0..5 { borrow mut c { m -> modify m { v -> v + x } } };
  free(c)

fn pe$i(k: i32) -> i32 with Log =
  let mut e = k;
  for i in 0..8 { log(i + $i); e = e + i };
  e

fn run$i(c: ref i32, k: i32) -> ref i32 * i32 =
  let a = with summing(&mut c) { pe$i(k) };
  (c, a)
B
done
echo
echo "main -> i32 * i32 ="
echo "  let mut t = 0;"
echo "  let mut m = 0;"
for ((i = 0; i < k; i++)); do
  echo "  let mut j$i = 0;"
  echo "  while j$i < 3 { t = t + j$i; j$i = j$i + 1 };"
  echo "  t = pd$i(pc$i(pb$i(pa$i(t))));"
  echo "  let (c$i, a$i) = run$i(alloc(0), t);"
  echo "  t = a$i + free(c$i);"
done
echo "  for b in bytes(&mut stdin) { m = m + to_i32(b) };"
echo "  (t, m)"
}

# Seconds of stage $2 in timings file $1 (the total when $2 is `total`).
stageMs() { awk -F': ' -v s="$2" '$1 == s { split($2, a, " "); print a[1] }' "$1"; }

case "$backend" in
  old)
    stages=("check" "elaborate" "convert" "collapse" "flat" "wasm" "print" "total")
    for k in "${scales[@]}"; do
      gen "$k" > "$tmp/scale$k.bc"
      "$bcc" compile --timings "$tmp/scale$k.bc" -o "$tmp/scale$k.wat" 2> "$tmp/scale$k.times"
    done ;;
  new)
    stages=("parse" "check" "lir" "layout" "flow" "lower" "wasm" "print" "total")
    for k in "${scales[@]}"; do
      gen2 "$k" > "$tmp/scale$k.bc"
      "$bcc" compile --backend new --timings "$tmp/scale$k.bc" -o "$tmp/scale$k.wat" 2> "$tmp/scale$k.times" ||
        { echo "the new backend does not compile the ${k}× program:"; cat "$tmp/scale$k.times"; exit 1; }
    done ;;
  *) echo "usage: scripts/compile-scaling.sh [--backend old|new] [--guard] [--keep DIR] [scale…]"; exit 2 ;;
esac

if [ "$guard" = 1 ]; then
  limit=${GUARD:-16}
  t1=$(stageMs "$tmp/scale1.times" total); t8=$(stageMs "$tmp/scale8.times" total)
  ratio=$(awk -v a="$t1" -v b="$t8" 'BEGIN { printf "%.1f", b / (a > 0 ? a : 1) }')
  echo "compile time ($backend backend): 1× ${t1} ms, 8× ${t8} ms, ratio ${ratio} (limit ${limit}; 8 is linear)"
  awk -v r="$ratio" -v l="$limit" 'BEGIN { exit !(r <= l) }' || { echo "compile time grows too fast"; exit 1; }
  exit 0
fi

printf '%-10s' "stage"; for k in "${scales[@]}"; do printf '%9s' "${k}×"; done; printf '%9s\n' "growth"
for s in "${stages[@]}"; do
  printf '%-10s' "$s"
  xs=""; ys=""
  for k in "${scales[@]}"; do
    ms=$(stageMs "$tmp/scale$k.times" "$s"); printf '%9s' "${ms}ms"
    xs="$xs $k"; ys="$ys $ms"
  done
  # Least squares of log(max(ms, 1)) on log k.
  awk -v xs="$xs" -v ys="$ys" 'BEGIN {
    n = split(xs, x, " "); split(ys, y, " ")
    for (i = 1; i <= n; i++) { lx = log(x[i]); ly = log(y[i] < 1 ? 1 : y[i])
      sx += lx; sy += ly; sxx += lx * lx; sxy += lx * ly }
    d = n * sxx - sx * sx
    if (n < 2 || d == 0) printf "%9s\n", "-"; else printf "%9.2f\n", (n * sxy - sx * sy) / d }'
done
printf '%-10s' "wat bytes"
for k in "${scales[@]}"; do printf '%9s' "$(( $(wc -c < "$tmp/scale$k.wat") / 1000 ))k"; done
echo
