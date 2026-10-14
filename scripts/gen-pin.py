#!/usr/bin/env python3
"""Generate `CDerivesP` and its Fundamental Property from Core's (SPEC §28).

`CDerivesP` (`Core/PinDerives.lean`) is `CDerives` with every premise read in `CDerivesP`, plus
the rules written by hand in `scripts/pin/CDerivesP.tmpl.lean`.  `fundamentalC_pin`
(`Core/PinFundamental.lean`) is `fundamentalC`'s induction, case for case, plus those rules' cases
written by hand in `scripts/pin/PinFundamental.tmpl.lean`.  `CDerivesP.ofC` (every `CDerives`
derivation is a `CDerivesP` one) is generated from the constructors' explicit binders.  A rule
added to `CDerives` is picked up by rerunning this script.

    python3 scripts/gen-pin.py           write the two files
    python3 scripts/gen-pin.py --check   fail if either differs from what would be written
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "Core" / "Fundamental.lean"
OUT = ROOT / "Core"
TMPL = ROOT / "scripts" / "pin"
CHECK = "--check" in sys.argv[1:]

text = SRC.read_text().splitlines()


def block(start_pat, stop_pat):
    i = next(k for k, l in enumerate(text) if re.match(start_pat, l))
    j = next(k for k in range(i + 1, len(text)) if re.match(stop_pat, text[k]))
    return text[i:j]


ind = block(r"^inductive CDerives ", r"^/-- `\[then\]` with its finaliser at the pure row")
while ind and ind[-1].strip() == "":
    ind.pop()
fund = block(r"^theorem fundamentalC ", r"^/-! ### Adequacy")
while fund and fund[-1].strip() == "":
    fund.pop()


def rename(lines):
    return [re.sub(r"\bCDerives\b", "CDerivesP", l) for l in lines]


# --- constructors and their explicit binders, for `PDerives.ofC` ---------------------------------
body = "\n".join(ind[1:])
ctors = []
for m in re.finditer(r"^  \| (\S+)(.*?)(?=^  \| |^  /--|\Z)", body, re.S | re.M):
    name, rest = m.group(1), m.group(2)
    explicit = []
    depth = 0
    k = 0
    grp_start = None
    grp_kind = None
    while k < len(rest):
        c = rest[k]
        if c in "({[":
            if depth == 0:
                grp_start, grp_kind = k + 1, c
            depth += 1
        elif c in ")}]":
            depth -= 1
            if depth == 0 and grp_kind == "(":
                grp = rest[grp_start:k]
                d = 0
                colon = None
                for q, ch in enumerate(grp):
                    if ch in "({[":
                        d += 1
                    elif ch in ")}]":
                        d -= 1
                    elif ch == ":" and d == 0 and grp[q:q + 2] != ":=":
                        colon = q
                        break
                names = grp[:colon].split()
                ty = grp[colon + 1:]
                for nm in names:
                    explicit.append((nm, "CDerives" in ty))
        elif c == ":" and depth == 0:
            break
        k += 1
    ctors.append((name, explicit))

ofc = []
for name, explicit in ctors:
    pat, args = [], []
    nih = 0
    for i, (nm, rec) in enumerate(explicit):
        pat.append(f"a{i}")
    ihs = []
    for i, (nm, rec) in enumerate(explicit):
        if rec:
            ihs.append(f"ih{len(ihs)}")
            args.append(ihs[-1])
        else:
            args.append(f"a{i}")
    lhs = " ".join([name] + pat + ihs)
    rhs = " ".join([f"CDerivesP.{name}"] + args)
    ofc.append(f"  | {lhs} => exact {rhs}")

# --- assemble ---------------------------------------------------------------------------------
der = (TMPL / "CDerivesP.tmpl.lean").read_text()
der = der.replace("--@CORE_RULES@", "\n".join(rename(ind[1:])))

fun = (TMPL / "PinFundamental.tmpl.lean").read_text()
fcases = rename(fund)
# drop the signature and `induction` line: the template supplies them
start = next(k for k, l in enumerate(fcases) if l.strip() == "induction h with") + 1
fun = fun.replace("--@CORE_CASES@", "\n".join(fcases[start:]))
fun = fun.replace("--@OFC_CASES@", "\n".join(ofc))

stale = []
for name, txt in (("PinDerives.lean", der), ("PinFundamental.lean", fun)):
    path = OUT / name
    if CHECK:
        if not path.exists() or path.read_text() != txt:
            stale.append(name)
    else:
        path.write_text(txt)
if CHECK:
    if stale:
        print("stale: " + ", ".join(f"Core/{n}" for n in stale) + " (run python3 scripts/gen-pin.py)")
        sys.exit(1)
    print(f"Core/PinDerives.lean, Core/PinFundamental.lean up to date ({len(ctors)} constructors)")
else:
    print(f"{len(ctors)} constructors copied")
