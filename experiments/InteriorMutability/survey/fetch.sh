#!/usr/bin/env bash
# Rebuild the two survey corpora: crates.io top-500 by all-time downloads (top/)
# and the top-40 of four app-level categories not already in the top 500 (cat/).
# Crate lists and "default_version" come from the live crates.io API, so a rerun
# on a later date yields later versions; meta/top500.txt and meta/cat.txt record
# the lists used for the reported numbers (reuse them to skip the API steps).
set -euo pipefail
SURVEY="${SURVEY:-$(cd "$(dirname "$0")/.." && pwd)}"
UA="ic-survey-research-script"
cd "$SURVEY"; mkdir -p meta top cat dl

# 1. Crate lists.
if [ ! -s meta/top500.txt ]; then
  for p in 1 2 3 4 5; do
    curl -s -m 30 -A "$UA" "https://crates.io/api/v1/crates?sort=downloads&per_page=100&page=$p" -o meta/top_$p.json; sleep 1
  done
  python3 - <<'PY'
import json
out=[]
for p in range(1,6):
    for c in json.load(open(f'meta/top_{p}.json'))['crates']:
        out.append((c['name'], c['default_version'] or c['max_stable_version']))
open('meta/top500.txt','w').write('\n'.join(f'{a} {b}' for a,b in out)+'\n')
PY
fi
if [ ! -s meta/cat.txt ]; then
  for c in gui game-development wasm compilers; do
    curl -s -m 30 -A "$UA" "https://crates.io/api/v1/crates?category=$c&sort=downloads&per_page=40" -o meta/cat_$c.json; sleep 1
  done
  python3 - <<'PY'
import json
top=set(l.split()[0] for l in open('meta/top500.txt'))
out=[]
for c in ['gui','game-development','wasm','compilers']:
    for x in json.load(open(f'meta/cat_{c}.json'))['crates']:
        if x['name'] not in top and x['name'] not in [o[0] for o in out]:
            out.append((x['name'], x['default_version'] or x['max_stable_version'], c))
open('meta/cat.txt','w').write('\n'.join(' '.join(o) for o in out)+'\n')
PY
fi

# 2. Download and extract.
dl(){ n=$1; v=$2; dest=$3; f=dl/$n-$v.crate
  [ -f "$f" ] || curl -s -L -m 60 -A "$UA" "https://static.crates.io/crates/$n/$n-$v.crate" -o "$f"
  tar xzf "$f" -C "$dest" 2>/dev/null || echo "FAIL $n $v"; }
while read -r n v; do dl "$n" "$v" top; done < meta/top500.txt
while read -r n v c; do dl "$n" "$v" cat; done < meta/cat.txt
echo "top: $(ls top | wc -l) crates; cat: $(ls cat | wc -l) crates"

# 3. Downstream steps (as run for the report):
#   python3 census.py top "crates.io top-500 by downloads" 1 meta/cr_top.json
#   python3 census.py cat "app-category top" 1 meta/cr_cat.json
#   python3 tl.py top cat
#   rg -n --no-heading --type rust -e '\bRefCell\s*<' top cat | grep -vE '^[^:]+:[0-9]+:\s*//' > meta/hits_refcell.txt
#   rg -n --no-heading --type rust -e '(^|[^A-Za-z0-9_])Cell\s*<' top cat | grep -vE '^[^:]+:[0-9]+:\s*//' > meta/hits_cell.txt
#   python3 sample.py > meta/sample.txt        # seed 20260928
#   python3 meta/classify.py                   # writes meta/sample-classified.tsv
