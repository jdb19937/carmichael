"""T15 freeze check: carmtmw is ( ph -> <frozen carmtm> ) under carmsw's hypotheses, verbatim.

    MM_DB=sorties/t15.mm python3 tools/gen/t15_freeze.py check
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def norm(s):
    return ' '.join(s.split())


def stmt(path, label):
    txt = open(os.path.join(ROOT, path)).read()
    hyps = {int(m.group(1)): norm(m.group(2)) for m in re.finditer(r'\b%s\.(\d+) \$e \|- (.*?) \$\.' % re.escape(label), txt, re.S)}
    m = re.search(r'\b%s \$p \|- (.*?) \$=' % re.escape(label), txt, re.S)
    return [hyps[k] for k in sorted(hyps)], (norm(m.group(1)) if m else None)


def main():
    frozen = open(os.path.join(ROOT, 'scratch', 'carmtm.mmp')).read()
    q = norm(frozen[frozen.index('qed::') + 5:].split('$)')[0])
    assert q.startswith('|- ')
    G = q[3:]
    db = os.environ.get('MM_DB', 'carmichael.mm')
    hyps, concl = stmt(db, 'carmtmw')
    if concl is None:
        print('carmtmw not in %s' % db); sys.exit(1)
    shyps, _ = stmt('carmichael.mm', 'carmsw')
    bad = 0
    if concl != '( ph -> %s )' % G:
        print('carmtmw conclusion differs from ( ph -> frozen carmtm )'); bad += 1
    if hyps != shyps:
        print('carmtmw hypotheses differ from carmsw.1-.%d' % len(shyps)); bad += 1
    print('carmtm frozen text: %d tokens; carmtmw = ( ph -> carmtm ) verbatim: %s; hypotheses = carmsw.1-.%d verbatim: %s'
          % (len(G.split()), 'yes' if concl == '( ph -> %s )' % G else 'NO', len(shyps), 'yes' if hyps == shyps else 'NO'))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
