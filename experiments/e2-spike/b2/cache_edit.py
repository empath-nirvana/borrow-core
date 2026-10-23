"""B2.2, UNCHECKED: the cached form of `p1-r3-owned-reborrow.bc`, by a hand edit of its emitted
LLVM IR. The proven form's resume `adv` (the one function whose body computes `value`, i.e.
stores the constant 7919, and whose signature is `St`'s seven words to `i64 + St`'s eight) is
renamed, and a wrapper of the same signature takes its place, calling `cached_step.c`'s
`cached_adv`. Everything else in the module (the build, `spawn0`, the scheduler) is untouched.
The output is linked with `cached_step.c` under LTO, so the step can be inlined as `adv` was.

    python3 experiments/e2-spike/b2/cache_edit.py in.ll out.ll [--hook FN KEY]

With `--hook FN KEY` (for `inv-b-owner-mutated.bc`; `FN` may be `auto`, the one `ref => ref`
function `adv` calls), the wrapper first runs the program's own
compiled `change` (`FN`, of type `ref Tree => ref Tree`, the cell as a word) when the resumed node's
key is `KEY`, as the proven `adv` does, and then the cached step: the optimisation applied to a
program whose machine mutates its owner between yields. With `--move KEY` (for
`inv-c-owner-moved.bc`, whose `change` is inlined), the wrapper calls `cached_adv_moving`, which
does that `change` (the cell freed, a new one allocated with its contents) at `KEY` first; with
`--move-fresh KEY` (for `inv-c2-owner-moved-fresh.bc`), `cached_adv_moving_fresh`, which allocates
the new cell before it frees the old one.
"""
import re, sys

SIG = "{i64, i64, i64, i64, i64, i64, i64, i64} @%s(ptr %%a0, ptr %%a1, i64 %%a2, i64 %%a3, i64 %%a4, i64 %%a5, i64 %%a6)"


def main(src, dst, hook=None):
    ll = open(src).read()
    defs = [(m.start(), m.group(1)) for m in re.finditer(r"^define internal \{i64, i64, i64, i64, i64, i64, i64, i64\} @(f\d+)\(ptr %a0, ptr %a1, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6\)", ll, re.M)]
    hits = []
    for start, name in defs:
        end = ll.index("\n}\n", start)
        if "store i64 7919," in ll[start:end]:
            hits.append(name)
    if len(hits) != 1:
        sys.exit(f"expected one `adv`, found {hits}")
    f = hits[0]
    if hook and hook[0] == "auto":
        start = ll.index("@" + f + "(ptr %a0")
        body = ll[start:ll.index("\n}\n", start)]
        fns = sorted(set(re.findall(r"call i64 @(f\d+)\(ptr [^,)]*\)", body)))
        if len(fns) != 1:
            sys.exit(f"expected one `change` called from `adv`, found {fns}")
        hook = (fns[0], hook[1])
    ll = ll.replace("define internal " + SIG % f, "define internal " + SIG % (f + "_proven"), 1)
    wrapper = """
declare void @cached_adv(ptr, i64, i64, i64, i64, i64, i64, i64)
declare void @cached_adv_moving(ptr, i64, i64, i64, i64, i64, i64, i64, i64)
declare void @cached_adv_moving_fresh(ptr, i64, i64, i64, i64, i64, i64, i64, i64)

; the cached resume (UNCHECKED, b2/cached_step.c) in place of the proven one
define internal %s nounwind {
entry:
  %%o = alloca [8 x i64], align 8
  %%c0 = ptrtoint ptr %%a0 to i64
  %%p = ptrtoint ptr %%a1 to i64
""" % (SIG % f)
    if hook and hook[0] in ("--move", "--move-fresh"):
        fn = "cached_adv_moving" if hook[0] == "--move" else "cached_adv_moving_fresh"
        wrapper += f"  call void @{fn}(ptr %o, i64 %c0, i64 %p, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6, i64 {hook[1]})\n"
    elif hook:
        fn, key = hook
        wrapper += f"""  %at = icmp eq i64 %a4, {key}
  br i1 %at, label %chg, label %go
chg:
  %c1 = call i64 @{fn}(ptr %a0)
  br label %go
go:
  %c = phi i64 [ %c0, %entry ], [ %c1, %chg ]
"""
    if not (hook and hook[0] in ("--move", "--move-fresh")):
        if not hook:
            wrapper += "  %c = add i64 %c0, 0\n"
        wrapper += """  call void @cached_adv(ptr %o, i64 %c, i64 %p, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6)
"""
    acc = "undef"
    for i in range(8):
        wrapper += f"  %g{i} = getelementptr i64, ptr %o, i64 {i}\n  %v{i} = load i64, ptr %g{i}, align 8\n"
        wrapper += f"  %s{i} = insertvalue {{i64, i64, i64, i64, i64, i64, i64, i64}} {acc}, i64 %v{i}, {i}\n"
        acc = f"%s{i}"
    wrapper += f"  ret {{i64, i64, i64, i64, i64, i64, i64, i64}} {acc}\n}}\n"
    open(dst, "w").write(ll + wrapper)
    print(f"adv is @{f}; replaced by the cached step")


a = sys.argv
main(a[1], a[2], (a[4], a[5]) if len(a) > 3 and a[3] == "--hook" else (a[3], a[4]) if len(a) > 3 and a[3] in ("--move", "--move-fresh") else None)
