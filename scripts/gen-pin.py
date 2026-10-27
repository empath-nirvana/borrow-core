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
# node (`Frontend/Check/TFacts.lean`). At `[handle]`, each operation's qualifier and its clause's
# kind (SPEC §19, *Clause kinds*), what the elaboration of effects records of the site (`HSite`),
# and the frames the handled computation holds (`inside`, `Core/HandledNames.lean`).
EXTRA = {"effHandleV": [("ks", "List ClauseKinds.HKind"), ("site", "Option HSite"),
                        ("inside", "ClauseKinds.HIn")],
         "effHandleVB": [("ks", "List ClauseKinds.HKind"), ("site", "Option HSite"),
                         ("inside", "ClauseKinds.HIn")],
         "effHandleT": [("site", "Option HSite"), ("inside", "ClauseKinds.HIn")],
         "effHandleL": [("site", "Option HSite"), ("inside", "ClauseKinds.HIn")]}

# Premises the typed rule adds to its rule's, which pin a field of `EXTRA` to the node's children:
# `inside` is the handled computation's frames. The projection to `CDerives` drops them.
EXTRA_PREM = {r: [("hins", "inside = Expr.hin e")] for r in ("effHandleV", "effHandleVB", "effHandleT",
                                                         "effHandleL")}


# Rule arguments that are terms but are determined by an equation on a child's erasure: the node
# does not hold them, and its erasure reads them off the child's (`Expr.pairL`, `Expr.toVal`, …,
# `scripts/pin/TExpr.tmpl.lean`). No node holds an untyped term (`lint_texpr`).
DERIVED = {
    "effHandleT": {"Hr": "(Expr.pairL (tc.erase))", "Hc": "(Expr.pairR (tc.erase))"},
    "effHandleL": {"Hr": "(Expr.pairL (tc.erase))", "Hw": "(Expr.pairL (Expr.pairR (tc.erase)))",
                   "Hn": "(Expr.pairR (Expr.pairR (tc.erase)))"},
    "reify": {"res": "(Expr.toVal (tres.erase))"},
    "letPoly": {"b": "(Expr.lamBody (tV.erase))", "N": "(Expr.letBody (tN.erase) (tV.erase))"},
}
# The projections of those rules: after each equation is rewritten in its premise and in the goal,
# the read-off arguments are the rule's (`Expr.toVal_val`, `Expr.letBody_shift`, `subst_unfill`).
PROJ_TAIL = {
    "reify": ["rw [Expr.toVal_val]"],
}
PROJ_LETPOLY = """  | letPoly a0 a1 a2 a3 a4 a5 ih0 ih1 =>
      dsimp only [TExpr.erase]
      rw [a3] at ih0
      rw [a5] at ih1
      rw [a3, a5, Expr.letBody_shift, Expr.lamBody_lam]
      exact JN.letPoly a0 a1 ih0 (by rw [subst_unfill a1]; exact ih1)"""


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
        self.erase = subst(self.erase, DERIVED.get(name, {}))
        used = idents(self.erase)
        self.fields = []
        for nm, kind, t in self.order:
            if t in ("LifeCtx", "Ctx VTy") or nm in bare:
                continue
            if kind == "(" and t not in DATA_TY:
                continue  # a proof or a premise
            if (t == "Expr" and nm not in used) or nm in DERIVED.get(name, {}):
                continue  # determined by an equation; an index of the typed rule only
            self.fields.append((nm, t))
        # at a split, the use masks of its two parts: the slots each uses, as the checker found
        # them (`Fam.u`); the split itself is chosen at each liveness, and is not a field, and
        # the typed rule relates the masks to its parts' contexts (`SplitMasks`)
        self.split = next(((names, ty) for kind, names, ty in self.groups
                           if kind == "(" and ty and ty.startswith("Ctx.SplitP ")), None)
        if self.split:
            self.fields.append(("u", "Masks"))
        # facts the checker records on the node that are not arguments of the rule (`EXTRA`)
        self.fields += EXTRA.get(name, [])
        self.kids = [p[1] for p in self.prem]
        # premises of the typed rule only, after the rule's own
        self.groups = self.groups + [("(", [nm], ty) for nm, ty in EXTRA_PREM.get(name, [])]

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
        if ty is None:
            # a term the node does not hold is an index of the typed rule: give it its type
            typed = [n for n in keep if n in DERIVED.get(r.name, {})]
            keep = [n for n in keep if n not in typed]
            out += [f"{o}{n} : {next(t for m, _, t in r.order if m == n)}{c}" for n in typed]
            if not keep:
                continue
        tys = f" : {subst(ty, sig)}" if ty else ""
        out.append(f"{o}{' '.join(keep)}{tys}{c}")
        if r.split and ty == r.split[1] and names == r.split[0]:
            g = top_split(ty)
            out.append(f"(hm : u.Rel {g[2]} {g[3]})")
    impl = "{info : TInfo}" + (" {u : Masks}" if ("u", "Masks") in r.fields else "") + \
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
                if nm not in {q for q, _ in EXTRA_PREM.get(r.name, [])}:
                    args.append(v)
                if r.split and ty == r.split[1]:
                    pat.append(f"a{n}")  # the masks' premise, which the projection drops
                    n += 1
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
    if r.name == "letPoly":
        return ctor, PROJ_LETPOLY.replace("JN", jn)
    if r.name in DERIVED:
        rws += [x.split(" at ")[0] for x in rws if x.startswith("rw [") and " at " in x]
        rws += PROJ_TAIL.get(r.name, [])
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
            if r.split and ty == r.split[1]:
                out.append(("hm", False))
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


def masks_case(r):
    pats = ["_"] * r.arity()
    pats[2 + [n for n, _ in r.fields].index("u")] = "u"
    return f"  | .{r.name} {' '.join(pats)} => some u"


tex = tex.replace("--@MASKS_CASES@", "\n".join(masks_case(r) for r in rulesP if r.split))
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

def lint_texpr(txt):
    """The nodes that hold an untyped term (`Expr`, `Val`, a surface term): none may."""
    lines = txt.splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("inductive TExpr "))
    j = next(k for k in range(i + 1, len(lines)) if lines[k] and not lines[k].startswith(" "))
    body = strip_comments("\n".join(lines[i + 1:j]))
    bad = []
    for m in re.finditer(r"^  \| (\S+)(.*?)(?=^  \| |\Z)", body, re.S | re.M):
        groups, _ = binders(m.group(2) + " :")
        for _, names, ty in groups:
            if ty and re.search(r"(?<![\w.])(BoCa\.)?(Expr|Val|Comp|Frontend\.Val|Frontend\.Comp)(?![\w.])", ty):
                bad.append(f"{m.group(1)} ({' '.join(names)} : {ty})")
    return bad


untyped = lint_texpr(tex)
if untyped:
    print("gen-pin: typed nodes hold an untyped term: " + "; ".join(untyped))
    sys.exit(1)

# --- a typed derivation at a wider lifetime context (`Frontend/Check/TLife.lean`) ----------------
# A rule whose node's type or premises are read at `⊓Δ` (the borrows), or that takes a fresh
# lifetime variable (`Δ.find? x = none`), is kept at its `Δ`: a body that holds one is checked at
# each lifetime context. Every other premise on `Δ` is kept by a larger `Δ` (`LeΔ`), and the
# freshness of a binder from the larger context's bounds is the extension's (`ExtΔ`).
MONO = [
    (r"^Δ\.EntailsLt ", "(LeΔ.entailsLt he.1 {a})"),
    (r"^Δ\.EntailsLe ", "(LeΔ.entailsLe he.1 {a})"),
    (r"^∀ y u, Δ\.find\? y = some u → u\.mentions x = false$",
     "(ExtΔ.avoid he (by simp [TExpr.lifeBinders]) {a})"),
    (r"^CtxOutlives Δ ", "(LeΔ.ctxOutlives he.1 {a})"),
    (r"^Row\.AnsOutlives Δ ", "(LeΔ.ansOutlives he.1 {a})"),
]


def mentions_delta(ty):
    return re.search(r"(?<![\w'])Δ(?![\w'])", ty) is not None


def is_dom(r):
    txt = " ".join(ty or "" for _, _, ty in r.groups) + " " + r.cjdg
    return "meetOfDom" in txt or "find? x = none" in txt or "find? c = none" in txt


def life_cases(r, tag):
    """`TExpr.lifeBinders`, `TExpr.domFree`, `TExpr.reAb` cases at `r`, and its `weakenΔ` case."""
    names = ["ii", "jj"] + [n for n, _ in r.fields] + r.kids
    pat = " ".join(names)
    binders = []
    kidΔ = {}
    for p in r.prem:
        g = norm(p[2])
        kidΔ[p[1]] = g
        m = re.fullmatch(r"\(Δ\.extend (\S+) .*\)", g)
        if m:
            binders.append(f"[{m.group(1)}]")
        elif g != "Δ":
            sys.exit(f"gen-pin: {r.name}: a premise at the lifetime context {g}")
    kids_b = [f"{k}.lifeBinders" for k in r.kids]
    bcase = f"  | .{r.name} {pat} => " + (" ++ ".join(binders + kids_b) if binders or kids_b else "[]")
    dom = is_dom(r)
    dcase = f"  | .{r.name} {pat} => " + ("false" if dom else
        (" && ".join(f"{k}.domFree" for k in r.kids) if r.kids else "true"))
    args = ["ii", "jj"] + [n for n, _ in r.fields] + \
        [f"({k}.reAb {kidΔ[k].replace('Δ', 'Δr')})" for k in r.kids]
    rcase = f"  | .{r.name} {pat} => .{r.name} {' '.join(args)}"
    return bcase, dcase, rcase


def weaken_life_case(r):
    jn = r.judg.split()[0]
    tj = "T" + jn[1:]
    if is_dom(r):
        return f"  | {r.name} => intro _ _ hd; simp [TExpr.domFree] at hd"
    pat, args, ihs = [], [], []
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
                t = norm(ty or "")
                if any(k in idents(subst(t, r.sigma)) for k in r.kids):
                    args.append(f"(by rw [TExpr.reAb_erase]; exact {v})")
                elif mentions_delta(t):
                    m = next((f for rx, f in MONO if re.search(rx, t)), None)
                    if m is None:
                        sys.exit(f"gen-pin: {r.name}: a premise on Δ not kept by a larger one: {t}")
                    args.append(m.format(a=v))
                else:
                    args.append(v)
                if r.split and ty == r.split[1]:
                    pat.append(f"a{n}")
                    args.append(f"a{n}")
                    n += 1
            else:
                ih = f"ih{len(ihs)}"
                ihs.append(ih)
                g = norm(p[2])
                if g == "Δ":
                    dd, ext = "Δ'", "(ExtΔ.sub he (fun z hz => by simp [TExpr.lifeBinders, hz]))"
                else:
                    m = re.fullmatch(r"\(Δ\.extend (\S+) (.*)\)", g)
                    dd = "_"
                    ext = "(ExtΔ.extend he (fun z hz => by simp [TExpr.lifeBinders, hz]))"
                args.append(f"({ih} {dd} {ext} (by simp_all [TExpr.domFree]))")
                if not p[6]:
                    q = f"a{n}"
                    n += 1
                    pat.append(q)
                    args.append(f"(by rw [TExpr.reAb_erase]; exact {q})")
    lines = [f"  | {' '.join([r.name] + pat + ihs)} =>", "      intro Δ' he hd",
             f"      exact {tj}.{r.name} {' '.join(args)}".rstrip()]
    return "\n".join(lines)


tlife = (TMPL / "TLife.tmpl.lean").read_text()
lc = [life_cases(r, "P") for r in rulesP]
tlife = tlife.replace("--@BINDERS@", "\n".join(a for a, _, _ in lc))
tlife = tlife.replace("--@DOMFREE@", "\n".join(b for _, b, _ in lc))
tlife = tlife.replace("--@REAB@", "\n".join(c for _, _, c in lc))
tlife = tlife.replace("--@P_WEAKENL@", "\n".join(weaken_life_case(r) for r in rulesP))
tlife = tlife.replace("--@AT_WEAKENL@", "\n".join(weaken_life_case(r) for r in rulesAt))

stale = []
outs = (("Core/PinDerives.lean", der), ("Core/PinFundamental.lean", fun),
        ("Frontend/Check/TExpr.lean", tex), ("Frontend/Check/TDerives.lean", tder),
        ("Frontend/Check/TLife.lean", tlife))
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
          f"{len(rulesP)} typed nodes, none holding an untyped term)")
else:
    print(f"{len(ctors)} constructors copied, {len(rulesP)} typed nodes")
