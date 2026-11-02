"""drop.py FILE NAME... : remove declarations (with preceding docstring/attrs) by name."""
import re, sys
f = sys.argv[1]; names = sys.argv[2:]
lines = open(f).read().split('\n')
starts = re.compile(r'^(theorem|def|abbrev|lemma|structure|inductive|noncomputable def|instance)\s+(\S+)')
out = []; i = 0
def is_boundary(l):
    return bool(re.match(r'^(theorem|def|abbrev|lemma|structure|inductive|noncomputable def|instance|/--|/-!|@\[|open |namespace |end |section|variable|set_option|alias|mutual)', l)) or l.strip()=='' and False
while i < len(lines):
    m = starts.match(lines[i])
    if m and m.group(2) in names:
        # remove preceding docstring / attribute lines already in out
        j = len(out)
        while j > 0 and (out[j-1].startswith('@[') or out[j-1].startswith('set_option') or out[j-1].startswith('open Classical in')):
            j -= 1
        # docstring block ending at j-1
        if j > 0 and out[j-1].rstrip().endswith('-/'):
            k = j-1
            while k >= 0 and not out[k].startswith('/--'):
                k -= 1
            if k >= 0: j = k
        out = out[:j]
        i += 1
        while i < len(lines) and not is_boundary(lines[i]):
            i += 1
        continue
    out.append(lines[i]); i += 1
open(f,'w').write('\n'.join(out))
