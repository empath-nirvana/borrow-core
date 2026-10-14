#!/usr/bin/env python3
"""Classify the census of Census.lean by what each declaration needs of the lifetime order.

    lake env lean experiments/PartialLife/scripts/Census.lean > census.txt
    python3 experiments/PartialLife/scripts/classify.py census.txt

Each finding line is `module | declaration | line | kind | head | class | part`. Findings of a
generated declaration (an equation lemma, a `match_`, `below`, `brecOn`) are those of its source.

A declaration is in the strongest class any of its findings is in, in the order (iii), (iv), (ii),
(i):

  (iii) compares two lifetimes no order relation is known between: `le_total`, `lt_trichotomy`,
        `le_of_not_gt`, a chain-only iff lemma in its chain-only direction (`sup_lt_iff.mpr`,
        `lt_inf_iff.mpr`, `Nat.max_lt` at `Life`, `not_le.mp`, ...), `Nat.le_total` at `Life`;
  (iv)  reads that no lifetime lies strictly between `↓a` and `a` (DenseCarrier's class (c));
  (ii)  uses `⊓` or `⊔` of two lifetimes, or a lifetime beneath finitely many (`exists_fresh`):
        a meet-semilattice (`⊓`, `inf_*`, `le_inf`) or a join-semilattice (`⊔`, `sup_*`);
  (i)   uses the order only: `≤`, `<`, `⊤`, preorder and partial-order lemmas, a decidable test of
        `<`, the carrier's construction by well-founded recursion, `δ` carried as `ℕ`.

Findings that do not concern the order (the coercions of `ℕ ≃ ℕᵒᵈ`, `SizeOf`, `BEq` on pairs,
numerals) are dropped; the instance paths a lemma's instance is built through
(`Lattice.toSemilatticeInf`, `LinearOrder.toLattice`, ...) are dropped, the lemma itself is kept.
"""
import collections
import re
import sys

GEN = re.compile(r'\.(eq_\d+|eq_def|match_\d+(_\d+)?|below(\.\w+)?|brecOn|_unary|_mutual)$')

# Chain-only lemmas, in any direction they are used.
CHAIN = {'le_total', 'lt_trichotomy', 'le_of_not_gt', 'lt_of_not_ge', 'lt_or_ge', 'le_or_gt',
         'lt_or_gt_of_ne', 'Ne.lt_or_lt', 'max_lt', 'lt_min', 'max_def', 'min_def',
         'Nat.le_total', 'Nat.lt_or_ge', 'Nat.lt_trichotomy', 'Nat.le_of_not_lt',
         'Nat.lt_of_not_le', 'Nat.max_lt', 'Nat.lt_min'}
# Iff lemmas: the direction that holds in every partial order (resp. semilattice).
IFF_PO = {('not_le', 'iff.mpr'), ('not_lt', 'iff.mpr'), ('sup_lt_iff', 'iff.mp'),
          ('max_lt_iff', 'iff.mp'), ('lt_inf_iff', 'iff.mp'), ('lt_min_iff', 'iff.mp'),
          ('Nat.max_lt', 'iff.mp'), ('Nat.lt_min', 'iff.mp'), ('le_max_iff', 'iff.mpr'),
          ('min_le_iff', 'iff.mpr'), ('lt_max_iff', 'iff.mpr'), ('min_lt_iff', 'iff.mpr'),
          ('Nat.not_le', 'iff.mpr'), ('Nat.not_lt', 'iff.mpr'), ('lt_iff_not_ge', 'iff.mp')}
SEMI_INF_HEADS = {'Min.min', 'inf_le_left', 'inf_le_right', 'le_inf', 'inf_comm', 'inf_assoc',
                  'inf_idem', 'inf_le_inf', 'inf_eq_left', 'inf_eq_right', 'min_le_left',
                  'min_le_right', 'le_min', 'Nat.max_assoc', 'Nat.max_le', 'Nat.le_max_left',
                  'Nat.le_max_right'}
SEMI_SUP_HEADS = {'Max.max', 'sup_le', 'le_sup_left', 'le_sup_right', 'sup_comm', 'sup_assoc',
                  'sup_idem', 'sup_le_sup', 'sup_eq_left', 'sup_eq_right', 'max_le',
                  'le_max_left', 'le_max_right', 'Nat.min_le_left', 'Nat.min_le_right'}
PLUMBING = re.compile(r'^(Lattice|SemilatticeInf|SemilatticeSup|LinearOrder|PartialOrder|Preorder|'
                      r'DistribLattice|OrderDual|instDistribLattice|Order\.)\.?')
NOT_ORDER = {'DFunLike.coe', 'EquivLike.toFunLike', 'SizeOf.sizeOf', 'instBEqProd',
             'Prod.instLawfulBEq', 'OfNat.ofNat', 'One.toOfNat1', 'instOfNatAtLeastTwo',
             'gt_iff_lt._simp_1', 'Lean.Omega'}
# DenseCarrier's class (c): no lifetime strictly between `↓a` and `a`, and its users.
DISCRETE = {'BoCa.Fig16.Life.le_of_down_lt', 'BoCa.Fig16.Life.not_lt_of_down_lt',
            'BoCa.Fig16.CellU.not_at_lt_of_inStratum_down', 'BoCa.Fig16.CellU.wit_inStratum_of_down',
            'BoCa.Fig16.ExW.inStratum_at', 'BoCa.Fig16.AgW.inStratum_at',
            'BoCa.Fig16.ResU.flat_inStratum_at', 'BoCa.Fig16.ResU.updV_outlives_at',
            'BoCa.Fig16.ResU.Sub.inStratum', 'BoCa.Fig16.ResU.six27', 'BoCa.Fig16.ResU.six52_H1',
            'BoCa.Fig16.ResU.six52_sub_inStratum'}
DISCRETE_LINES = {
    ('Support.Model.Outlives', 'BoCa.Fig16.CellU.not_at_lt_of_inStratum_down'): 428,
    ('Support.Model.Outlives', 'BoCa.Fig16.CellU.wit_inStratum_of_down'): 469,
    ('Support.Model.Outlives', 'BoCa.Fig16.ExW.inStratum_at'): 521,
    ('Support.Model.Outlives', 'BoCa.Fig16.AgW.inStratum_at'): 548,
    ('Support.Model.Outlives', 'BoCa.Fig16.ResU.flat_inStratum_at'): 578,
    ('Support.Model.Outlives', 'BoCa.Fig16.ResU.updV_outlives_at'): 606,
    ('Support.Model.Outlives', 'BoCa.Fig16.ResU.Sub.inStratum'): 625}
# A lifetime strictly beneath finitely many, built as `(Σ ofDual) + 1`: a common lower bound.
FRESH = {'BoCa.Fig16.LogRel.Core.exists_fresh', 'BoCa.Fig16.LogRel.Typed.exists_fresh'}
# Statements that are a chain-only fact at the resource level, proved through another (iii) place
# and so carrying no finding of their own beyond `⊔`.
CHAIN_STATEMENTS = {'BoCa.Fig16.ResU.InStratum.sup'}

PREFIXES = ['BoCa.Fig16.LogRel.Core.', 'BoCa.Fig16.LogRel.Typed.', 'BoCa.Fig16.LogRel.',
            'BoCa.Fig16.BoLo.', 'BoCa.Fig16.', 'BoCa.Lifetime.']


def short(n):
    for p in PREFIXES:
        if n.startswith(p):
            return n[len(p):]
    return n


def parent(n):
    while GEN.search(n):
        n = GEN.sub('', n)
    return n


def finding_class(kind, head, cls):
    """The class of one finding, or None when it does not concern the order."""
    if kind == 'timeout':
        return 'timeout'
    if kind == 'omega' or kind == 'nat':
        return None
    if head in NOT_ORDER or cls in ('DFunLike', 'EquivLike', 'SizeOf', 'BEq', 'LawfulBEq',
                                    'OfNat', 'One', 'NatCast'):
        return None
    if kind in ('iff.mp', 'iff.mpr'):
        return 'i' if (head, kind) in IFF_PO else 'iii'
    if kind == 'rw':
        return 'iii'
    if head in CHAIN:
        return 'iii'
    if kind == 'inst' and PLUMBING.match(head) and head not in SEMI_INF_HEADS | SEMI_SUP_HEADS:
        return None
    if head in SEMI_INF_HEADS or cls == 'SemilatticeInf':
        return 'ii-meet'
    if head in SEMI_SUP_HEADS or cls in ('SemilatticeSup',):
        return 'ii-join'
    if cls in ('Lattice',):
        return 'ii-meet'
    if kind == 'inst' and cls == 'LinearOrder':
        return 'iii?'
    return 'i'


RANK = {'iii': 5, 'iii?': 5, 'iv': 4, 'ii-meet': 3, 'ii-join': 2, 'i': 1, 'timeout': 0}


def main(path):
    rows = [l.rstrip('\n').split(' | ') for l in open(path) if l.count(' | ') == 6]
    lines, decls = {}, collections.OrderedDict()
    for m, n, line, *_ in rows:
        if int(line):
            lines[(m.strip(), parent(n.strip()))] = int(line)
    for m, n, _, kind, head, cls, part in rows:
        key = (m.strip(), parent(n.strip()))
        if key in lines:
            decls.setdefault(key, set()).add((kind.strip(), head.strip(), cls.strip()))
    if any(m == 'Support.Model.Outlives' for m, _ in decls):
        for key, line in DISCRETE_LINES.items():
            decls.setdefault(key, set())
            lines[key] = line
    classes = {}
    for (m, n), fs in decls.items():
        cs = {finding_class(*f) for f in fs} - {None}
        if n in DISCRETE:
            cs.add('iv')
        if n in FRESH:
            cs.add('ii-meet')
        if n in CHAIN_STATEMENTS:
            cs.add('iii')
        if not cs:
            continue
        classes[(m, n)] = cs
    strongest = {k: max(cs, key=lambda c: RANK[c]) for k, cs in classes.items()}
    titles = [('iii', '(iii) compares two lifetimes'), ('iii?', '(iii?) a `LinearOrder` lemma, unclassified'),
              ('iv', '(iv) discreteness'), ('ii-meet', '(ii) a meet-semilattice: `⊓`, a common lower bound'),
              ('ii-join', '(ii) a join-semilattice: `⊔`'), ('i', '(i) the order only'),
              ('timeout', 'timeout')]
    print('| class | places | `Paper/` | `Support/` | `Core/` |')
    print('|---|---|---|---|---|')
    tot = collections.Counter()
    for c, title in titles:
        places = {(m, lines[(m, n)]) for (m, n), s in strongest.items() if s == c}
        if not places:
            continue
        cnt = collections.Counter(m.split('.')[0] for m, _ in places)
        tot.update(cnt)
        print(f"| {title} | {len(places)} | {cnt['Paper']} | {cnt['Support']} | {cnt['Core']} |")
    print(f"| all | {sum(tot.values())} | {tot['Paper']} | {tot['Support']} | {tot['Core']} |")
    print()
    print(f'(Places are distinct file and line; a declaration is counted once, in its strongest '
          f'class. {len(classes)} declarations.)')
    print()
    for c, title in titles:
        if c == 'i':
            continue
        sel = sorted((m, lines[(m, n)], short(n)) for (m, n), s in strongest.items() if s == c)
        if not sel:
            continue
        print(f'**{title}: {len({(m, l) for m, l, _ in sel})}**\n')
        by = collections.defaultdict(set)
        for m, l, n in sel:
            by[m].add((l, n))
        for m in sorted(by):
            p = m.replace('.', '/') + '.lean'
            print(f'- `{p}`: ' + ', '.join(f'{l} `{n}`' for l, n in sorted(by[m])))
        print()


if __name__ == '__main__':
    main(sys.argv[1])
