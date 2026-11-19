#!/usr/bin/env bash
# Respell the book's `bc` blocks (SPEC §82). A book block carries no pragma: book-doctest.sh reads
# every block with `bcc --dialect 82`. Each block (found as book-doctest.sh's `extract` finds it) is
# translated by `bcc respell`, its pragma line dropped, and checked against its text in today's
# spelling:
#
#   * a `bc` or `bc,check` block: `bcc erase` of the two is byte-identical, and `bcc check`'s
#     declarations with their checked types are the same (positions blanked, lines sorted, as
#     check-respell.sh's `sigs`);
#   * a `bc,reject` block: both are refused, with the same message up to the positions it quotes;
#     its `# expect:` line is the new block's refusal, at its new position;
#   * every block: its `answer:`, `output:` and `stdin:` lines have the same text.
#
# A block the translator does not translate whole (a `#?respell:` mark) or that fails the check is
# left as it is and reported. `bc,ignore` blocks are left as they are.
#
#     scripts/respell-book.sh [--write] [file.md…]   every chapter, or the ones named; without
#                                                    --write, nothing is changed
set -euo pipefail
cd "$(dirname "$0")/.."
write=0
[ "${1:-}" = --write ] && { write=1; shift; }
bcc=${BCC:-.lake/build/bin/bcc}
[ -x "$bcc" ] || { echo "no bcc at $bcc: run \`lake build bcc\`, or set BCC"; exit 1; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else find book/src -name '*.md' | sort; fi > "$tmp/chapters"
export LC_ALL=C
python3 -I - "$bcc" "$tmp" "$write" "$tmp/chapters" <<'PY'
import re, subprocess, sys
bcc, tmp, write = sys.argv[1], sys.argv[2], sys.argv[3] == "1"
fence = re.compile(r"^\s*```")
directive = re.compile(r"^(?:--|#) (answer|output|stdin):(.*)$")

def run(args, path):
    p = subprocess.run([bcc] + args + [path], capture_output=True, text=True, timeout=300)
    return p.returncode, p.stdout, p.stderr

def blank(s, new=False):
    s = re.sub(r"\b\d+:\d+\b", "L:C", s)
    return s

def sigs(out):
    return sorted(blank(l) for l in out.splitlines())

def directives(text):
    return [m.groups() for m in map(directive.match, text.splitlines()) if m]

counts = {"same": 0, "left": 0, "ignored": 0}
rows = []
for md in open(sys.argv[4]).read().split():
    lines = open(md, encoding="utf-8").read().split("\n")
    blocks, i = [], 0
    while i < len(lines):
        if fence.match(lines[i]):
            info = re.sub(r"^\s*```\s*", "", lines[i]).rstrip()
            j = i + 1
            while j < len(lines) and not fence.match(lines[j]):
                j += 1
            if info == "bc" or info.startswith("bc,"):
                attrs = info[3:] or "run"
                blocks.append((i, j, attrs))
            i = j + 1
        else:
            i += 1
    out = list(lines)
    for (a, b, attrs) in reversed(blocks):
        at = f"{md}:{a + 1}"
        old = "\n".join(lines[a + 1:b]) + "\n"
        if attrs == "ignore":
            counts["ignored"] += 1; rows.append((at, attrs, "ignored", "")); continue
        of, nf = f"{tmp}/old.bc", f"{tmp}/new.bc"
        open(of, "w", encoding="utf-8").write(old)
        rc, tr, err = run(["respell"], of)
        if rc != 0:
            counts["left"] += 1; rows.append((at, attrs, "respell", " ".join(err.split())[:200])); continue
        new = tr.split("\n", 1)[1]
        open(nf, "w", encoding="utf-8").write(new)
        why = ""
        if directives(old) != directives(new):
            why = "its answer/output/stdin lines differ"
        elif attrs in ("run", "check"):
            ro, eo, xo = run(["erase"], of)
            rn, en, xn = run(["--dialect", "82", "erase"], nf)
            if ro != 0 or rn != 0:
                why = f"erase failed: old {' '.join(xo.split())[:120]} | new {' '.join(xn.split())[:160]}"
            elif eo != en:
                why = "its erasure differs"
            else:
                _, so, _ = run(["check"], of)
                _, sn, _ = run(["--dialect", "82", "check"], nf)
                if sigs(so) != sigs(sn):
                    why = "the checked types of its declarations differ"
        elif attrs == "reject":
            _, _, xo = run(["check"], of)
            rn, _, xn = run(["--dialect", "82", "check"], nf)
            mo = xo.strip().replace(of + ":", "", 1)
            mn = xn.strip().replace(nf + ":", "", 1)
            if rn == 0:
                why = "the new block checks"
            elif blank(mo) != blank(mn):
                why = f"refused differently: old {mo[:120]} | new {mn[:160]}"
            else:
                exp = [k for k, l in enumerate(new.split("\n")) if re.match(r"^(?:--|#) expect: ", l)]
                if not exp:
                    why = "no expect line"
                else:
                    nl = new.split("\n")
                    oldexp = nl[exp[0]]
                    nl[exp[0]] = "# expect: " + mn
                    new = "\n".join(nl)
                    if nl[exp[0]] != oldexp:
                        rows.append((at, attrs, "expect", f"{oldexp} -> {nl[exp[0]]}"))
        else:
            why = f"unknown attributes {attrs}"
        if why:
            counts["left"] += 1; rows.append((at, attrs, "left", why)); continue
        counts["same"] += 1; rows.append((at, attrs, "same", ""))
        out[a + 1:b] = new.rstrip("\n").split("\n")
    if write:
        open(md, "w", encoding="utf-8").write("\n".join(out))
for r in reversed(rows):
    print("\t".join(r))
print(f"{counts['same']} block(s) respelled{' and written' if write else ''}, {counts['left']} left in today's spelling, {counts['ignored']} ignored.")
PY
