#!/usr/bin/env python3
"""Generate `CDerivesP` and its Fundamental Property from Core's (SPEC §29), and the typed term
with its derivations (SPEC §3).

`CDerivesP` (`Core/PinDerives.lean`) is `CDerives` with every premise read in `CDerivesP`, plus
the rules written by hand in `scripts/pin/CDerivesP.tmpl.lean`.  `fundamentalC_pin`
(`Core/PinFundamental.lean`) is `fundamentalC`'s induction, case for case, plus those rules' cases
written by hand in `scripts/pin/PinFundamental.tmpl.lean`.  `CDerivesP.ofC` (every `CDerives`
derivation is a `CDerivesP` one) is generated from the constructors' explicit binders.

The typed term (`Frontend/Check/TExpr.lean`, from `scripts/pin/TExpr.tmpl.lean`) has one node per
`CDerivesP` rule, holding the rule's arguments and one child per premise; `TExpr.erase` is the
rule's conclusion term.  `TDerivesAt`/`TDerivesP` (`Frontend/Check/TDerives.lean`, from
`scripts/pin/TDerives.tmpl.lean`) are `CDerivesAt` (`Core/Tied.lean`) and `CDerivesP` over the
typed term, with their projections to the erasure, case for case.  A rule added to `CDerives` is
picked up by rerunning this script.

    python3 scripts/gen-pin.py           write the four files
    python3 scripts/gen-pin.py --check   fail if any differs from what would be written
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "Core" / "Fundamental.lean"
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
# fundamentalC's induction: up to the next top-level declaration or section
fund = block(r"^theorem fundamentalC ", r"^(/-! |/-- |theorem |def |lemma )")
# `[then]` at the pure row and `[handle]` at two variables, stated after the inductive
derived = block(r"^/-- `\[then\]` with its finaliser at the pure row", r"^/-! ### The delay, stream")
while derived and derived[-1].strip() == "":
    derived.pop()
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
der = der.replace("--@CORE_DERIVED@", "\n".join(rename(derived)))

fun = (TMPL / "PinFundamental.tmpl.lean").read_text()
fcases = rename(fund)
# drop the signature and `induction` line: the template supplies them
start = next(k for k, l in enumerate(fcases) if l.strip() == "induction h with") + 1
fun = fun.replace("--@CORE_CASES@", "\n".join(fcases[start:]))
fun = fun.replace("--@OFC_CASES@", "\n".join(ofc))


# --- the typed term (docs/compiler.md §2.3, §2.4) ---------------------------------------------
# `TExpr` has one constructor per `CDerivesP` rule: the rule's arguments other than its contexts,
# its proofs and the terms its premises type, with the node's `TInfo` and judgment first and one
# child per premise last. `TDerivesAt`/`TDerivesP` are `CDerivesAt`/`CDerivesP` with each premise
# at a child: a premise's term is the child's erasure (an equation `t.erase = M` when the premise
# types a term built from other arguments, as `thunkV`'s `λN` does), and the conclusion's term is
# the node. The projections `TDerivesAt.erase`, `TDerivesP.erase` are generated case for case.

def strip_comments(t):
    t = re.sub(r"/-.*?-/", "", t, flags=re.S)
    return re.sub(r"--[^\n]*", "", t)


def ctor_texts(src, header):
    """The constructors of the inductive whose declaration line starts with `header`."""
    lines = src.splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith(header))
    j = next(k for k in range(i + 1, len(lines))
             if lines[k] and not lines[k].startswith(" ") and not lines[k].startswith("--"))
    body = strip_comments("\n".join(lines[i + 1:j]))
    return [(m.group(1), m.group(2)) for m in
            re.finditer(r"^  \| (\S+)(.*?)(?=^  \| |\Z)", body, re.S | re.M)]


OPEN, CLOSE = "({[⟨", ")}]⟩"


def top_split(s):
    """`s`'s arguments at bracket depth 0, split at whitespace."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        if ch.isspace() and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def top_split_commas(s):
    """`s`'s items at bracket depth 0, split at commas."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return out


def norm(s):
    return " ".join(s.split())


def binders(rest):
    """A constructor's binder groups `(kind, names, type or None)` and its conclusion."""
    groups, depth, k, start = [], 0, 0, None
    while k < len(rest):
        c = rest[k]
        if c in "({[":
            if depth == 0:
                start = (k + 1, c)
            depth += 1
        elif c in ")}]":
            depth -= 1
            if depth == 0:
                grp = rest[start[0]:k]
                d, colon = 0, None
                for q, ch in enumerate(grp):
                    if ch in OPEN:
                        d += 1
                    elif ch in CLOSE:
                        d -= 1
                    elif ch == ":" and d == 0 and grp[q:q + 2] != ":=":
                        colon = q
                        break
                if colon is None:
                    groups.append((start[1], grp.split(), None))
                else:
                    groups.append((start[1], grp[:colon].split(), norm(grp[colon + 1:])))
        elif c == ":" and depth == 0:
            break
        k += 1
    return groups, norm(rest[k + 1:])


# The types of the implicit binders `CDerives` leaves unannotated, by name. A name a premise or
# the conclusion types as its term is an `Expr`.
NAME_TY = {"A": "VTy", "B": "VTy", "R": "VTy", "S": "VTy", "T": "VTy", "C": "CTy", "D": "CTy",
           "a": "Lifetime.Life", "b": "Lifetime.Life", "x": "LifeVar", "y": "LifeVar",
           "i": "Nat", "j": "Jdg"}
EXPR_NAMES = {"e", "e₁", "e₂", "M", "N", "V", "H", "f", "d", "M₁", "M₂", "K", "s0"}
DATA_TY = {"VTy", "CTy", "Row", "LifeVar", "Lifetime.Life", "IntLit", "HostOp", "FShape", "Expr",
           "Jdg", "OpSig", "UInt32", "Nat", "List (Qual × VTy × VTy)", "Nat → CTy", "Val"}
TOKEN = r"[^\s()\[\]{}⟨⟩,.:]+"
# erasures that are a `λ` whatever the children's (`withPair M N = λs. case s {…}`)
LAM_HEADS = ("(withPair ",)
# erasures whose head is an `Expr` constructor other than `lam`
NOT_LAM_HEADS = ("(.var ", "(.pair ", "(.inj₁ ", "(.inj₂ ", "(.app ", "(.seq ", "(.letpair ",
                 "(.case ", "(.val .unit)", "(.val (.prim ", "(.val ⟨.prim ")


def subst(text, sigma):
    """`text` with each identifier in `sigma` replaced (not after a `.`: a field, a constructor)."""
    def rep(m):
        w = m.group(0)
        if m.start() > 0 and text[m.start() - 1] == ".":
            return w
        return sigma.get(w, w)
    return re.sub(TOKEN, rep, text)


def idents(text):
    return {m.group(0) for m in re.finditer(TOKEN, text)
            if not (m.start() > 0 and text[m.start() - 1] == ".")}


# Fields a node carries that are not its rule's arguments: facts the checker establishes at the
# node, which the typed derivation does not constrain (`Frontend/Check/TFacts.lean`). At
# `[handle]`, each operation's qualifier and its clause's kind (SPEC §19, *Clause kinds*).
EXTRA = {"effHandleV": [("ks", "List ClauseKinds.HKind")],
         "effHandleVB": [("ks", "List ClauseKinds.HKind")]}


def kid_name(h):
    return "t" + h[1:] if h.startswith("h") else "t_" + h


class Rule:
    """One constructor of `CDerivesP` or `CDerivesAt`, read for its typed copy."""

    def __init__(self, name, rest, judg):
        self.name = name
        self.judg = judg  # "CDerivesP" or "CDerivesAt Ξ"
        self.groups, concl = binders(rest)
        cargs = top_split(concl)
        if cargs[0] != judg.split()[0] or len(cargs) != 5 + len(judg.split()) - 1:
            sys.exit(f"gen-pin: {name}: a conclusion not of the form `{judg} Δ Γ e j`: {concl}")
        nctx = len(judg.split()) - 1
        self.cpre = cargs[1:1 + nctx]  # `Ξ`, in `CDerivesAt`
        self.cΔ, self.cΓ, self.cexpr, self.cjdg = cargs[1 + nctx:]
        # premises: explicit binders whose type is a judgment
        # (binder, child, Δ, Γ, term, judgment, whether the term is a binder)
        self.prem = []
        for kind, names, ty in self.groups:
            if ty and ty.startswith(judg.split()[0] + " "):
                pa = top_split(ty)
                if len(pa) != 5 + nctx:
                    sys.exit(f"gen-pin: {name}: a premise not of the form `{judg} Δ Γ e j`: {ty}")
                pΔ, pΓ, pe, pj = pa[1 + nctx:]
                for nm in names:
                    self.prem.append((nm, kid_name(nm), pΔ, pΓ, pe, pj, re.fullmatch(TOKEN, pe) is not None))
            elif ty and judg.split()[0] in ty:
                sys.exit(f"gen-pin: {name}: a premise not of the form `{judg} …`: {ty}")
        bare = {p[4]: p[1] for p in self.prem if p[6]}
        if len(bare) != len([p for p in self.prem if p[6]]):
            sys.exit(f"gen-pin: {name}: a term typed by two premises")
        self.bare = bare
        # each binder with its kind and type
        self.order = []
        for kind, names, ty in self.groups:
            for nm in names:
                if ty is None:
                    if nm == "Δ":
                        t = "LifeCtx"
                    elif nm.startswith("Γ"):
                        t = "Ctx VTy"
                    elif nm in bare or nm in EXPR_NAMES:
                        t = "Expr"
                    elif nm in NAME_TY:
                        t = NAME_TY[nm]
                    else:
                        sys.exit(f"gen-pin: {name}: the type of the binder `{nm}` is not known")
                else:
                    t = ty
                self.order.append((nm, kind, t))
        self.sigma = {x: f"({k}.erase)" for x, k in bare.items()}
        # the erasure; `pass_kid` is the child whose erasure the conclusion's term is, `pass_eq`
        # whether through an equation
        cexpr = norm(self.cexpr)
        self.pass_kid, self.pass_eq = None, False
        if cexpr in bare:
            self.erase = f"{bare[cexpr]}.erase"
            self.pass_kid = bare[cexpr]
        else:
            same = [p for p in self.prem if not p[6] and norm(p[4]) == cexpr]
            if same:
                self.erase = f"{same[0][1]}.erase"
                self.pass_kid, self.pass_eq = same[0][1], True
            else:
                self.erase = subst(self.cexpr, self.sigma)
        used = idents(self.erase)
        self.fields = []
        for nm, kind, t in self.order:
            if t in ("LifeCtx", "Ctx VTy") or nm in bare:
                continue
            if kind == "(" and t not in DATA_TY:
                continue  # a proof or a premise
            if t == "Expr" and nm not in used:
                continue  # determined by an equation; an index of the typed rule only
            self.fields.append((nm, t))
        # at a split, the use mask of its left part: the slots it uses, as the checker found them
        # (`Fam.u`); the split itself is chosen at each liveness, and is not a field
        if any(kind == "(" and ty and ty.startswith("Ctx.SplitP ") for kind, _, ty in self.groups):
            self.fields.append(("u", "List Bool"))
        # facts the checker records on the node that are not arguments of the rule (`EXTRA`)
        self.fields += EXTRA.get(name, [])
        self.kids = [p[1] for p in self.prem]

    def texpr_ctor(self):
        fs = " ".join(f"({n} : {t})" for n, t in self.fields)
        ks = f" ({' '.join(self.kids)} : TExpr)" if self.kids else ""
        return f"  | {self.name} (info : TInfo) (jdg : Jdg){(' ' + fs) if fs else ''}{ks}"

    def lam_case(self):
        """`isLam`'s case, and `isLam_eq`'s: whether the node erases to a `λ`, read off the rule's
        term where its head is a constructor, through the child where the rule keeps its premise's
        term, and computed from the erasure otherwise."""
        pats = ["_"] * self.arity()
        e = self.erase
        if self.pass_kid:
            k = 2 + len(self.fields) + self.kids.index(self.pass_kid)
            pats[k] = "t"
            return f"  | .{self.name} {' '.join(pats)} => t.isLam", \
                f"  | .{self.name} {' '.join(pats)} => isLam_eq t"
        if e.startswith("(.val (.lam") or any(e.startswith(h) for h in LAM_HEADS):
            return f"  | .{self.name} {' '.join(pats)} => true", f"  | .{self.name} {' '.join(pats)} => rfl"
        if any(e.startswith(h) for h in NOT_LAM_HEADS):
            return f"  | .{self.name} {' '.join(pats)} => false", f"  | .{self.name} {' '.join(pats)} => rfl"
        used = idents(e)
        ps = ["_", "_"] + [n if n in used else "_" for n, _ in self.fields] + \
            [k if k in used else "_" for k in self.kids]
        own = {n for n, _ in self.fields} | set(self.kids)
        body = subst(e, {c: f"BoCa.{c}" for c in RULE_NAMES - own})
        return f"  | .{self.name} {' '.join(ps)} => (({body} : Expr) matches .lam _)", \
            f"  | .{self.name} {' '.join(pats)} => rfl"

    def scope(self, pΓ):
        """How a premise's context is formed from the conclusion's: slots pushed onto a part of
        it (a split's part has its length), or a literal context of its own."""
        g = norm(pΓ)
        if g.startswith("(") and g.endswith(")"):
            g = g[1:-1].strip()
        if g.startswith("["):
            inner = g[1:-1].strip()
            return f".fresh {0 if not inner else len(top_split_commas(inner))}"
        if g.startswith("withCtx "):
            return ".push 2"
        n = g.count(" :: ")
        tail = g.split(" :: ")[-1]
        if not re.fullmatch(r"Γ\S*", tail):
            sys.exit(f"gen-pin: {self.name}: a premise context not read: {pΓ}")
        return f".push {n}"

    def children_case(self):
        pats = ["_"] * self.arity()
        for j, k in enumerate(self.kids):
            pats[2 + len(self.fields) + j] = k
        kids = ", ".join(f"({self.scope(p[3])}, {p[1]})" for p in self.prem)
        return f"  | .{self.name} {' '.join(pats)} => [{kids}]"

    def arity(self):
        return 2 + len(self.fields) + len(self.kids)

    def erase_case(self):
        used = idents(self.erase)
        pats = ["_", "_"] + [n if n in used else "_" for n, _ in self.fields] + \
            [k if k in used else "_" for k in self.kids]
        # a Core term named as a node (`copy`, `swap`, …), not the node
        own = {n for n, _ in self.fields} | set(self.kids)
        body = subst(self.erase, {c: f"BoCa.{c}" for c in RULE_NAMES - own})
        return f"  | .{self.name} {' '.join(pats)} => {body}"


def typed_rule(r, fieldsof):
    """`r`'s typed copy: the constructor of `TDerivesP`/`TDerivesAt`, and its projection case."""
    jn = r.judg.split()[0]
    tj = "T" + jn[1:]  # TDerivesP, TDerivesAt
    sig = r.sigma
    out = []
    # implicit and explicit binders, in order
    for kind, names, ty in r.groups:
        if kind == "(" and ty and ty.startswith(jn + " "):
            for nm in names:
                p = next(p for p in r.prem if p[0] == nm)
                pre = " ".join(r.cpre)
                Δ, Γ, pj = subst(p[2], sig), subst(p[3], sig), subst(p[5], sig)
                out.append(f"({nm} : {tj}{(' ' + pre) if pre else ''} {Δ} {Γ} {p[1]} {pj})")
                if not p[6]:
                    out.append(f"(q{p[1][1:]} : {p[1]}.erase = ({subst(p[4], sig)} : Expr))")
            continue
        keep = [n for n in names if n not in r.bare]
        if not keep:
            continue
        o, c = kind, {"(": ")", "{": "}", "[": "]"}[kind]
        tys = f" : {subst(ty, sig)}" if ty else ""
        out.append(f"{o}{' '.join(keep)}{tys}{c}")
    impl = "{info : TInfo}" + (" {u : List Bool}" if ("u", "List Bool") in r.fields else "") + \
        "".join(f" {{{n} : {t}}}" for n, t in EXTRA.get(r.name, [])) + \
        (f" {{{' '.join(r.kids)} : TExpr}}" if r.kids else "")
    J = subst(r.cjdg, sig)
    flds = fieldsof[r.name]
    args = ["(info := info)", f"(jdg := {J})"] + [f"({n} := {n})" for n, _ in flds] + \
        [f"({k} := {k})" for k in r.kids]
    node = f"(TExpr.{r.name} {' '.join(args)})"
    pre = " ".join(r.cpre)
    concl = f"{tj}{(' ' + pre) if pre else ''} {r.cΔ} {r.cΓ} {node} {J}"
    ctor = f"  | {r.name} " + " ".join(out[:1] + [impl] + out[1:]) + f" :\n      {concl}"
    # the projection case: every explicit binder of the typed rule, then one IH per premise
    pat, args, ihs, rws = [], [], [], []
    n = 0
    for kind, names, ty in r.groups:
        if kind != "(":
            continue
        for nm in names:
            v = f"a{n}"
            n += 1
            pat.append(v)
            p = next((p for p in r.prem if p[0] == nm), None) if ty and ty.startswith(jn + " ") else None
            if p is None:
                args.append(v)
            else:
                ih = f"ih{len(ihs)}"
                ihs.append(ih)
                args.append(ih)
                if not p[6]:
                    q = f"a{n}"
                    n += 1
                    pat.append(q)
                    rws.append(f"rw [{q}] at {ih}")
                    if r.pass_eq and p[1] == r.pass_kid:
                        rws.append(f"rw [{q}]")
    lines = [f"  | {' '.join([r.name] + pat + ihs)} =>", "      dsimp only [TExpr.erase]"]
    lines += [f"      {x}" for x in rws]
    lines.append(f"      exact {jn}.{r.name} {' '.join(args)}".rstrip())
    return ctor, "\n".join(lines)


RULE_NAMES = {n for n, _ in ctor_texts(der, "inductive CDerivesP ")}
def typed_explicit(r):
    """The explicit binders of `r`'s typed rule, in order: `(name, whether a premise)`; each
    equation follows its premise."""
    jn = r.judg.split()[0]
    out = []
    for kind, names, ty in r.groups:
        if kind != "(":
            continue
        for nm in names:
            p = next((p for p in r.prem if p[0] == nm), None) if ty and ty.startswith(jn + " ") else None
            out.append((nm, p is not None))
            if p is not None and not p[6]:
                out.append(("q" + p[1][1:], False))
    return out


def to_p_case(ra, rp):
    """`TDerivesAt.toP`'s case at `ra`: the same node in `TDerivesP`, its tie dropped."""
    ea = typed_explicit(ra)
    pat = {nm: f"a{k}" for k, (nm, _) in enumerate(ea)}
    ihs = {nm: f"ih{k}" for k, nm in enumerate([nm for nm, prem in ea if prem])}
    args = [ihs[nm] if prem else pat.get(nm) for nm, prem in typed_explicit(rp)]
    if None in args:
        sys.exit(f"gen-pin: TDerivesP.{rp.name} has a binder that TDerivesAt.{ra.name} lacks")
    lhs = " ".join([ra.name] + [f"a{k}" for k in range(len(ea))] + list(ihs.values()))
    return f"  | {lhs} => exact TDerivesP.{rp.name} {' '.join(args)}".rstrip()


rulesP = [Rule(n, rest, "CDerivesP") for n, rest in ctor_texts(der, "inductive CDerivesP ")]
tied_src = (ROOT / "Core" / "Tied.lean").read_text()
rulesAt = [Rule(n, rest, "CDerivesAt Ξ") for n, rest in ctor_texts(tied_src, "inductive CDerivesAt ")]
fieldsof = {r.name: r.fields for r in rulesP}
for r in rulesAt:
    if r.name not in fieldsof:
        sys.exit(f"gen-pin: CDerivesAt.{r.name} is not a rule of CDerivesP")
    if [n for n, _ in r.fields] != [n for n, _ in fieldsof[r.name]] or r.kids != next(
            q.kids for q in rulesP if q.name == r.name):
        sys.exit(f"gen-pin: CDerivesAt.{r.name} and CDerivesP.{r.name} give different nodes")

tex = (TMPL / "TExpr.tmpl.lean").read_text()
tex = tex.replace("--@TEXPR_CTORS@", "\n".join(r.texpr_ctor() for r in rulesP))
tex = tex.replace("--@ERASE_CASES@", "\n".join(r.erase_case() for r in rulesP))
tex = tex.replace("--@INFO_CASES@", "\n".join(
    f"  | .{r.name} i {' '.join(['_'] * (r.arity() - 1))} => i" for r in rulesP))
tex = tex.replace("--@JDG_CASES@", "\n".join(
    f"  | .{r.name} _ j {' '.join(['_'] * (r.arity() - 2))} => j".replace(" j  =>", " j =>")
    for r in rulesP))

tex = tex.replace("--@CHILDREN_CASES@", "\n".join(r.children_case() for r in rulesP))
lams = [r.lam_case() for r in rulesP]
tex = tex.replace("--@ISLAM_CASES@", "\n".join(a for a, _ in lams))
tex = tex.replace("--@ISLAM_EQ@", "\n".join(b for _, b in lams))

tder = (TMPL / "TDerives.tmpl.lean").read_text()
byP = {r.name: r for r in rulesP}
tder = tder.replace("--@TOP_CASES@", "\n".join(to_p_case(r, byP[r.name]) for r in rulesAt))
for tag, rules in (("AT", rulesAt), ("P", rulesP)):
    pairs = [typed_rule(r, fieldsof) for r in rules]
    tder = tder.replace(f"--@{tag}_RULES@", "\n".join(c for c, _ in pairs))
    tder = tder.replace(f"--@{tag}_ERASE@", "\n".join(p for _, p in pairs))

stale = []
outs = (("Core/PinDerives.lean", der), ("Core/PinFundamental.lean", fun),
        ("Frontend/Check/TExpr.lean", tex), ("Frontend/Check/TDerives.lean", tder))
for name, txt in outs:
    path = ROOT / name
    if CHECK:
        if not path.exists() or path.read_text() != txt:
            stale.append(name)
    else:
        path.write_text(txt)
if CHECK:
    if stale:
        print("stale: " + ", ".join(stale) + " (run python3 scripts/gen-pin.py)")
        sys.exit(1)
    print(", ".join(n for n, _ in outs) + f" up to date ({len(ctors)} constructors, "
          f"{len(rulesP)} typed nodes)")
else:
    print(f"{len(ctors)} constructors copied, {len(rulesP)} typed nodes")
