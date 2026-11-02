"""Translate printed Lean source (over CellU) to the tree carrier (CellUT K).
usage: port.py OUT HEADER_IMPORTS -- SRC[:a-b] ...  (skip decls via SKIP env, comma sep)"""
import re, sys, os
out = sys.argv[1]; imports = sys.argv[2].split(',')
srcs = sys.argv[4:]
skip = set(x for x in os.environ.get('SKIP','').split(',') if x)
body = []
for spec in srcs:
    if ':' in spec:
        f, rng = spec.split(':'); a, b = map(int, rng.split('-'))
        lines = open(f).read().split('\n')[a-1:b]
    else:
        lines = open(spec).read().split('\n')
    body.append('\n'.join(lines))
s = '\n'.join(body)
# drop import lines / module docstrings at file starts are kept as comments? remove imports
s = re.sub(r'^import .*$\n', '', s, flags=re.M)
s = re.sub(r'^alias .*$\n', '', s, flags=re.M)
s = re.sub(r'^variable \{ℍ : BoCa\.Host\} \[BoCa\.HostIs ℍ\]\n', '', s, flags=re.M)
s = re.sub(r'^noncomputable section\n', '', s, flags=re.M)
s = re.sub(r'^end\s*$', '', s, flags=re.M)
# namespaces
s = re.sub(r'^namespace BoCa\.Fig16\.BoLo\s*$', 'namespace BoCa.Fig16.Tree.BoLo\nopen BoCa.Fig16 BoCa.Fig16.Tree', s, flags=re.M)
s = re.sub(r'^end BoCa\.Fig16\.BoLo\s*$', 'end BoCa.Fig16.Tree.BoLo', s, flags=re.M)
s = re.sub(r'^namespace BoCa\.Fig16\s*$', 'namespace BoCa.Fig16.Tree\nopen BoCa.Fig16', s, flags=re.M)
s = re.sub(r'^end BoCa\.Fig16\s*$', 'end BoCa.Fig16.Tree', s, flags=re.M)
s = re.sub(r'^variable \{Loc Val : Type\}\s*$', 'variable {Loc Val : Type} {K : WCactus}', s, flags=re.M)
# types
s = s.replace('(Loc := Loc) (Val := Val)', '(Loc := Loc) (Val := Val) (K := K)'); s = s.replace('CellU Loc Val', 'CellUT Loc Val K').replace('ResU Loc Val', 'ResUT Loc Val K')
s = s.replace('CellU BoCa.Loc BoCa.Val', 'CellUT BoCa.Loc BoCa.Val K').replace('ResU BoCa.Loc BoCa.Val', 'ResUT BoCa.Loc BoCa.Val K')
s = re.sub(r'\bWRes\b', '(ResUT BoCa.Loc BoCa.Val K)', s)
s = re.sub(r'\bCellU\.', 'CellUT.', s)
s = re.sub(r'\bResU\.', 'ResUT.', s)
s = re.sub(r'\blsOf\b', 'lsOfI', s); s = re.sub(r'\bImmU\b', 'ImmT', s); s = re.sub(r'\bMutU\b', 'MutT', s)
# walks
for _a, _b in (('ExW', 'ExWT'), ('AgW', 'AgWT'), ('ExS', 'ExST'), ('ExR', 'ExRT'), ('BigComp', 'BigCompT')):
    s = re.sub(r'\bBoLo\.' + _a + r'\b', 'BoLo.' + _b, s)
s = re.sub(r'\bExW\.(mk|rec)\b', r'G.ExW.\1', s)
s = re.sub(r'\bExWits\.(nil|cons|rec)\b', r'G.ExWits.\1', s)
s = re.sub(r'\bAgW\.(mk|rec)\b', r'G.AgW.\1', s)
s = re.sub(r'\bAgWitsM\.(nil|cons)\b', r'G.AgWitsM.\1', s)
s = re.sub(r'\bAgWitsI\.(nil|cons)\b', r'G.AgWitsI.\1', s)
s = re.sub(r'\bBigComp\.(nil|cons)\b', r'G.BigComp.\1', s)
s = re.sub(r'(?<![.\w])ExWits\b', 'ExWitsT', s)
s = re.sub(r'(?<![.\w])ExW\b', 'ExWT', s)
s = re.sub(r'(?<![.\w])AgWitsM\b', 'AgWitsMT', s)
s = re.sub(r'(?<![.\w])AgWitsI\b', 'AgWitsIT', s)
s = re.sub(r'(?<![.\w])AgW\b', 'AgWT', s)
s = re.sub(r'(?<![.\w])BigComp\b', 'BigCompT', s)
s = re.sub(r'(?<![.\w])OptComp\b', 'OptCompT', s)
s = re.sub(r'(?<![.\w])ExS\b', 'ExST', s)
s = re.sub(r'(?<![.\w])ExR\b', 'ExRT', s)
# rho|iota in its unfolded form, the form the walk constructors' fields carry
s = re.sub(r"((?:\((?:[^()]|\([^()]*\))*\))|(?<![.\w'])[\w'₀-₉]+)\.restrict ((?:Kind\.\w+)|[\w']+)", r"(G.restrict CellUT.kind \1 \2)", s)
s = re.sub(r"\bResUT\.restrict ((?:\((?:[^()]|\([^()]*\))*\))|[\w'₀-₉]+) ((?:Kind\.\w+)|[\w']+)", r"(G.restrict CellUT.kind \1 \2)", s)
# dot notation on a restriction: PMap has none of ResUT's names
for _ in range(3):
    s = re.sub(r"\(\((G\.restrict CellUT\.kind (?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)\)", r"(\1)", s)
def _dot(m):
    expr, attr = m.group(1), m.group(2)
    if attr in ('get', 'finite', 'map'):
        return m.group(0)
    return 'ResUT.' + attr + ' (ρ := ' + expr + ')'
s = re.sub(r"(\(G\.restrict CellUT\.kind (?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))\.(\w+)", _dot, s)
# K for own cells, which carry no lifetime
s = s.replace('CellUT.ownOf (Loc := Loc)', 'CellUT.ownOf (K := K) (Loc := Loc)')
s = re.sub(r"\(CellUT\.ownOf ([\w']+)\)\.kind", r"(CellUT.ownOf (K := K) \1).kind", s)
# lifetimes and mut cells
s = s.replace('SPropS Loc Val', 'SPropST Loc Val K').replace('SPropS BoCa.Loc BoCa.Val', 'SPropST BoCa.Loc BoCa.Val K')
s = re.sub(r'\bSPropS\.', 'SPropST.', s)
s = s.replace('mutOf_at', 'mutOf_ls')
s = re.sub(r'\bCellUT\.rep\b', "CellUT.rep'", s)
s = re.sub(r'\bLSet\b(?!\.)', 'TSet', s)
s = re.sub(r"InStratum ([\w']+)\.join\b", r'InStratum \1', s)
s = re.sub(r'InStratum \((\w+)\.join\)', r'InStratum \1', s)
s = re.sub(r"\.InStratum ([\w']+)\.join\b", r'.InStratum \1', s)
# rep' mut alternative gains the antichain fact
lines = s.split('\n')
for i, l in enumerate(lines):
    if "rep'" in l or (i > 0 and "rep'" in lines[i-1]):
        lines[i] = re.sub(r"⟨([^,⟨⟩]+), ([^,⟨⟩]+), ([^,⟨⟩]+), ([^,⟨⟩]+), ([^,⟨⟩]+), ([^,⟨⟩]+), rfl⟩", r"⟨\1, _, \2, \3, \4, \5, \6, rfl⟩", l)
s = '\n'.join(lines)
# per-declaration: Life binders -> TSet, with Fact anti for mut lifetimes
chunks = re.split(r'(?m)^(?=(?:theorem|def|lemma|abbrev|noncomputable def) )', s)
outc = []
for c in chunks:
    mutvars = set(re.findall(r'mutOf \(?(\w+)', c))
    def binder(m):
        br_o, names, br_c = m.group(1), m.group(2).split(), m.group(3)
        res = br_o + ' '.join(names) + ' : TSet' + br_c
        for n in names:
            if n in mutvars:
                res += ' [Fact (K.Anti ' + n + ')]'
        return res
    c = re.sub(r'([({])((?:[^\s(){}:]+ )*[^\s(){}:]+) : Life([)}])', binder, c)
    outc.append(c)
s = ''.join(outc)
# skip declarations: remove from 'theorem NAME' to next blank-line-preceded decl
if skip:
    parts = re.split(r'(?m)^(?=(?:/--|theorem |def |abbrev |lemma |@\[|structure |inductive |noncomputable def |open Classical in))', s)
    keep = []
    pending_doc = ''
    for p in parts:
        m = re.search(r'(?:theorem|def|abbrev|lemma|structure|inductive)\s+(\S+)', p)
        nm = m.group(1) if m else None
        if nm and nm.replace('ResU.','ResUT.') in skip or (nm in skip if nm else False):
            continue
        keep.append(p)
    s = ''.join(keep)
root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
def _rel(spec):
    f = os.path.abspath(spec.split(':')[0])
    r = os.path.relpath(f, root)
    return '`' + r + (':' + spec.split(':')[1] if ':' in spec else '') + '`'
banner = ('/-!\n# Generated: the printed source over the tree-stratified carrier\n\n'
          'Generated by `scripts/tree-port/regen.sh` (`port.py`, then the fixes recorded in '
          '`fixups.py`)\nfrom ' + ', '.join(_rel(x) for x in srcs) + ', read at `CellUT K`. '
          'Edit the generator,\nnot this file; `scripts/tree-port/regen.sh --check` verifies '
          'it.\n-/\n\n')
hdr = '\n'.join('import '+i for i in imports) + '\n\n' + banner + 'noncomputable section\n\n'
open(out,'w').write(hdr + s.strip() + '\n\nend\n')
