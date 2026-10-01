"""Sortie DSH: transcribe a Z6 worksheet to the half-line detector by the text substitution dsub
(tools/dshlib.py) plus local patches of the parameter-closure steps.
Run: MM_DB=sorties/dsh.mm python3 tools/gen/dsh_tr.py X [X ...]   (X = suffix of z6X, e.g. anp)"""
import sys, os, re, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from dshlib import dsub, LABMAP, Y151, trstmt, A7SUB, A7TR

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
STEP = re.compile(r'^([^:\s]+):([^:]*):([^\s]*)( \|- (.*))?$')


def parse(path):
    """list of [name, hyps, ref, formula-or-None] and the header/comment lines"""
    head, steps, tail = [], [], []
    for l in open(path).read().split('\n'):
        m = STEP.match(l)
        if m and not l.startswith('$') and not l.startswith('*'):
            steps.append([m.group(1), m.group(2), m.group(3), m.group(5)])
        elif steps:
            tail.append(l)
        else:
            head.append(l)
    return head, steps, tail


def split_imp(f):
    t = f.split()
    if not t or t[0] != '(':
        return None, f
    d = 0
    for i, x in enumerate(t):
        if x == '(':
            d += 1
        elif x == ')':
            d -= 1
        elif x == '->' and d == 1:
            return ' '.join(t[1:i]), ' '.join(t[i + 1:-1])
    return None, f


def transform(x, extra=()):
    src = os.path.join(ROOT, 'worksheets', 'z6%s.mmp' % x)
    head, steps, tail = parse(src)
    subs = list(extra) + ([(dsub(a), b) for a, b in A7SUB] if x in A7TR else [])
    out = []
    byf = {}
    pn = [0]
    dv = set()

    def new(hyps, ref, f):
        pn[0] += 1
        n = 'p%d' % pn[0]
        out.append([n, ','.join(hyps), ref, f])
        return n
    for n, h, r, f in steps:
        r = LABMAP.get(r, r)
        if f is not None:
            f = dsub(f).replace('( 6 / 5 )', Y151)
            for a, b in subs:
                f = f.replace(a, b)
        if f is not None:
            a, c = split_imp(f)
            if f == '%s e. RR+' % Y151:
                h, r = '', 'dsh151rp'
            elif a is not None and c == '1 e. RR+' and r == 'rpcxpcld':
                h, r = new([], '1rp', '1 e. RR+'), 'a1i'
            elif a is not None and c == '1 <_ D' and r == 'a5ge1cxp':
                hs = [byf.get('( %s -> %s )' % (a, g)) for g in ('1 e. RR', 'D e. RR', '1 < D')]
                if None in hs:
                    hs = [byf.get('( %s -> %s )' % (a, 'D e. RR')), byf.get('( %s -> %s )' % (a, '1 < D'))]
                    if None in hs:
                        raise SystemExit('no D facts for step %s' % n)
                    h, r = ','.join(hs), 'ltled' if False else 'ltled'
                    one = new([], '1re', '1 e. RR'); one = new([one], 'a1i', '( %s -> 1 e. RR )' % a)
                    h = ','.join([one] + hs)
                else:
                    h = ','.join(hs)
                r = 'ltled'
            elif a is None and f == '1 e. _V' and r == 'ovex':
                r = '1ex'
            elif a is None and f == 'D e. _V' and r == 'ovex':
                dv.add(n)
            elif a is not None and c == 'D e. _V' and r == 'a1i' and h in dv:
                dr = byf.get('( %s -> D e. RR )' % a)
                if dr is None:
                    raise SystemExit('no D e. RR for step %s' % n)
                h, r = dr, 'elexd'
            byf.setdefault(f, n)
        out.append([n, h, r, f])
    lab = 'dsh' + x
    hd = '\n'.join(head).replace('THEOREM=z6%s ' % x, 'THEOREM=%s ' % lab)
    for k, v in LABMAP.items():
        hd = re.sub(r'~ %s\b' % k, '~ %s' % v, hd)
    lines = [hd] + ['%s:%s:%s%s' % (n, h, r, '' if f is None else ' |- ' + f) for n, h, r, f in out] + tail
    q = [s for s in out if s[0] == 'qed'][0]
    assert q[3] == trstmt(x), 'qed differs from trstmt(%s)\n%s\n%s' % (x, q[3], trstmt(x))
    p = os.path.join(ROOT, 'worksheets', lab + '.mmp')
    open(p, 'w').write('\n'.join(lines))
    return p


if __name__ == '__main__':
    for x in sys.argv[1:]:
        p = transform(x)
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'add', p], capture_output=True, text=True, env=env, cwd=ROOT)
        txt = (r.stdout + r.stderr).strip().split('\n')
        print('\n'.join(txt[-6:]))
