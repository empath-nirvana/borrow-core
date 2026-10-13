#!/usr/bin/env python3
"""Classify the census of Census.lean into the README's classes.

    lake env lean experiments/DenseCarrier/scripts/Census.lean > census.txt
    python3 experiments/DenseCarrier/scripts/classify.py census.txt

Each finding line is `module | declaration | line | kind | head`. Findings of a generated
declaration (an equation lemma, a `match_`, `below`, `brecOn`) are those of its source; one
generated in another module than its source is dropped, the source being listed in its own.

Classes:
  (b) the stratified construction: `Cell`, `Cell_eq` (`WellFounded.fix` on `ℕ`);
  (c) discreteness: the two facts "no lifetime strictly between `↓a` and `a`" and the
      declarations that use them to read `ρ ∈ Res_{↓α}` as "every cell `⊒ α`";
  (a) everything else, by what the `ℕ` is used for: `↓` as a strictly shorter lifetime,
      `ofDual`/`toDual`, an `ℕ` order lemma at `Life`, or `δ`/`@aδ` carried as `ℕ`.
"""
import collections
import re
import sys

GEN = re.compile(r'\.(eq_\d+|eq_def|match_\d+(_\d+)?|below(\.\w+)?|brecOn)$')

DISCRETE = {
    'BoCa.Fig16.Life.le_of_down_lt', 'BoCa.Fig16.Life.not_lt_of_down_lt',
    'BoCa.Fig16.CellU.not_at_lt_of_inStratum_down', 'BoCa.Fig16.CellU.wit_inStratum_of_down',
    'BoCa.Fig16.ExW.inStratum_at', 'BoCa.Fig16.AgW.inStratum_at',
    'BoCa.Fig16.ResU.flat_inStratum_at', 'BoCa.Fig16.ResU.updV_outlives_at',
    'BoCa.Fig16.ResU.Sub.inStratum', 'BoCa.Fig16.ResU.six27', 'BoCa.Fig16.ResU.six52_H1',
    'BoCa.Fig16.ResU.six52_sub_inStratum'}
# The discreteness users that reach the facts through lemmas, so carry no `ℕ` finding of their own.
DISCRETE_LINES = {
    ('Support.Model.Outlives', 'BoCa.Fig16.CellU.not_at_lt_of_inStratum_down'): 428,
    ('Support.Model.Outlives', 'BoCa.Fig16.CellU.wit_inStratum_of_down'): 469,
    ('Support.Model.Outlives', 'BoCa.Fig16.ExW.inStratum_at'): 521,
    ('Support.Model.Outlives', 'BoCa.Fig16.AgW.inStratum_at'): 548,
    ('Support.Model.Outlives', 'BoCa.Fig16.ResU.flat_inStratum_at'): 578,
    ('Support.Model.Outlives', 'BoCa.Fig16.ResU.updV_outlives_at'): 606,
    ('Support.Model.Outlives', 'BoCa.Fig16.ResU.Sub.inStratum'): 625}
CONSTRUCTION = {'BoCa.Fig16.Cell', 'BoCa.Fig16.Cell_eq'}
ORDER = {'BoCa.Fig16.leMaxL', 'BoCa.Fig16.leMaxR', 'BoCa.Fig16.minLeL', 'BoCa.Fig16.minLeR',
         'Max.max', 'LE.le', 'LT.lt'}


PREFIXES = ['BoCa.Fig16.LogRel.Core.', 'BoCa.Fig16.LogRel.Typed.', 'BoCa.Fig16.LogRel.',
            'BoCa.Fig16.BoLo.', 'BoCa.Fig16.']


def short(n):
    for p in PREFIXES:
        if n.startswith(p):
            return n[len(p):]
    return n


def parent(n):
    while GEN.search(n):
        n = GEN.sub('', n)
    return n


def kind_a(findings):
    heads = {h for _, h in findings}
    if any('down' in h or 'succ' in h for h in heads):
        return 'a-down'
    if heads & {'OrderDual.ofDual', 'OrderDual.toDual'}:
        return 'a-dual'
    if all(k == 'L→N' and (h.startswith('Nat.') or h in ORDER) for k, h in findings):
        return 'a-order'
    return 'a-rep'


def main(path):
    rows = [l.rstrip('\n').split(' | ') for l in open(path) if l.count(' | ') == 4]
    lines, decls = {}, collections.OrderedDict()
    for m, n, line, _, _ in rows:
        if int(line):
            lines[(m.strip(), parent(n.strip()))] = int(line)
    for m, n, _, kind, head in rows:
        key = (m.strip(), parent(n.strip()))
        if key in lines:
            decls.setdefault(key, set()).add((kind.strip(), head.strip()))
    for key, line in DISCRETE_LINES.items():
        decls.setdefault(key, set())
        lines[key] = line
    groups = collections.defaultdict(set)
    for (m, n), findings in decls.items():
        cls = 'b' if n in CONSTRUCTION else 'c' if n in DISCRETE else kind_a(findings)
        groups[cls].add((m, lines[(m, n)], short(n)))
    titles = [('b', '(b) the stratified construction'), ('c', '(c) discreteness'),
              ('a-down', '(a) a strictly shorter lifetime, `↓`'),
              ('a-dual', '(a) `ofDual`/`toDual` at `ℕ`'),
              ('a-order', '(a) an `ℕ` order lemma at `Life`'),
              ('a-rep', '(a) `δ` and `@aδ` carried as `ℕ`')]
    for cls, title in titles:
        places = {(m, l) for m, l, _ in groups[cls]}
        print(f'**{title}: {len(places)}**\n')
        by = collections.defaultdict(set)
        for m, l, n in groups[cls]:
            by[m].add((l, n))
        for m in sorted(by):
            path_ = m.replace('.', '/') + '.lean'
            if cls == 'a-rep':
                print(f'- `{path_}`: ' + ', '.join(str(l) for l in sorted({l for l, _ in by[m]})))
            else:
                print(f'- `{path_}`: ' + ', '.join(f'{l} `{n}`' for l, n in sorted(by[m])))
        print()


if __name__ == '__main__':
    main(sys.argv[1])
