"""Sortie GF1: frozen statements and helpers (GramFunction.lean 1-1074, GammaStrip remnants).

    python3 tools/gf1lib.py print                                   # the frozen table
    MM_DB=sorties/gf1.mm python3 tools/gf1lib.py check [LABEL...]    # grammar check (mmatch)

Objects (macros, no df-):
  PH(C, W)  = if ( W = 0 , C , ( ( exp ( C W ) - 1 ) / W ) )        the difference quotient of
              w |-> exp ( C w ) at 0, extended by its derivative C (entire: gf1ph)
  AVG(A, L, W) = exp ( A W ) . ( PH(L, W) / L )                        Lean avgExp A L W
              (= ( 1 / L ) S. ( A , A + L ) exp ( W t ) dt, gf1avgi)
  KK(A, B, L, W) = AVG(B, L, W) - AVG(A, L, W)                         Lean Kker M0 X L W at
              A = log M0, B = log X
  KQ(A, B, L, W) = ( PH(L, W) / L ) . ( exp ( A W ) . PH(B - A, W) )  Lean dslope ( Kker ) 0 W
  G1(A, B, L, W) = _G ( W + 1 ) . KQ(A, B, L, W)                       Lean G1 M0 X L W
  MH(N, R, C, S), HM(N, R)                                             Lean Mh, Hmass
  C7 = 8337480 = 1608 ( 1 + 5184 )                                     Lean C7 (value kept)
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)

DB = os.environ.get('MM_DB', 'sorties/gf1.mm')
_TXT = {}


def stmt(label):
    """the assertion of LABEL from the sortie file or carmichael.mm, without |-"""
    for fn in ('sorties/gf1.mm', 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if fn not in _TXT or fn.startswith('sorties'):
            _TXT[fn] = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), _TXT[fn], re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects ----------------------------------------------------------------------------------
def PH(C, W):
    return 'if ( %s = 0 , %s , ( ( ( exp ` ( %s x. %s ) ) - 1 ) / %s ) )' % (W, C, C, W, W)


def AVG(A, L, W):
    return '( ( exp ` ( %s x. %s ) ) x. ( %s / %s ) )' % (A, W, PH(L, W), L)


def KK(A, B, L, W):
    return '( %s - %s )' % (AVG(B, L, W), AVG(A, L, W))


def KQ(A, B, L, W):
    return '( ( %s / %s ) x. ( ( exp ` ( %s x. %s ) ) x. %s ) )' % (PH(L, W), L, A, W, PH('( %s - %s )' % (B, A), W))


def G1(A, B, L, W):
    return '( ( _G ` ( %s + 1 ) ) x. %s )' % (W, KQ(A, B, L, W))


def HOL(F, D):
    return '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)


HPM1 = "( `' Re \" ( -u 1 (,) +oo ) )"
C7 = '; ; ; ; ; ; 8 3 3 7 4 8 0'
DIV = lambda K, x='x': '{ %s e. NN | %s || %s }' % (x, x, K)
RS = lambda N, R: '( %s RSet %s )' % (N, R)


def MH(N, R, C, S):
    return ('sum_ r e. %s sum_ t e. %s ( ( 1 / ( r x. t ) ) x. sum_ d e. %s ( ( ( ( r hBV t ) ` d ) x. ( %s ` d ) ) '
            'x. ( d ^c -u %s ) ) )') % (RS(N, R), RS(N, R), DIV('( r x. t )'), C, S)


def HM(N, R):
    return ('sum_ r e. %s sum_ t e. %s ( ( 1 / ( r x. t ) ) x. sum_ d e. %s ( abs ` ( ( r hBV t ) ` d ) ) )') % (
        RS(N, R), RS(N, R), DIV('( r x. t )'))


ZR = lambda N, K: '( ( ZRHom ` ( Z/nZ ` %s ) ) ` %s )' % (N, K)
DB_ = lambda N: '( Base ` ( DChr ` %s ) )' % N
EXPH = lambda Z: '( exp ` ( -u ( abs ` ( Im ` %s ) ) / 2 ) )' % Z

S = {}
# ---- Gamma input and the elementary bound --------------------------------------------------------
S['gf1ga'] = ('( ( Z e. CC /\\ ( -u ( 1 / ; 5 0 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 0 ) ) -> '
              '( abs ` ( _G ` ( Z + 1 ) ) ) <_ ( ; ; ; 4 8 9 6 x. ( exp ` -u ( abs ` ( Im ` Z ) ) ) ) )')
S['gf1em1'] = ('( ( Z e. CC /\\ ( M e. RR /\\ 1 <_ M /\\ ( exp ` ( Re ` Z ) ) <_ M ) ) -> '
               '( abs ` ( ( exp ` Z ) - 1 ) ) <_ ( M x. ( abs ` Z ) ) )')
# ---- PH -------------------------------------------------------------------------------------------
S['gf1ph'] = '( C e. CC -> %s )' % HOL('( w e. CC |-> %s )' % PH('C', 'w'), 'CC')
S['gf1phv'] = ('( ( C e. CC /\\ W e. CC ) -> ( %s e. CC /\\ ( %s x. W ) = ( ( exp ` ( C x. W ) ) - 1 ) /\\ %s = C ) )'
               % (PH('C', 'W'), PH('C', 'W'), PH('C', '0')))
_PHW = PH('C', 'W')
S['gf1phb'] = ('( ( ( C e. RR /\\ 0 <_ C ) /\\ W e. CC ) -> ( ( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ C ) /\\ '
               '( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( C x. ( exp ` C ) ) ) /\\ '
               '( ( ( Re ` W ) <_ 0 /\\ W =/= 0 ) -> ( ( abs ` %s ) x. ( abs ` W ) ) <_ 2 ) ) )') % (_PHW, _PHW, _PHW)
# ---- avgExp, Kker ---------------------------------------------------------------------------------
_AV = AVG('A', 'L', 'W')
S['gf1avgi'] = ('( ( ( A e. RR /\\ L e. RR+ ) /\\ W e. CC ) -> ( ( t e. ( A (,) ( A + L ) ) |-> ( exp ` ( W x. t ) ) ) e. L^1 /\\ '
                '( ( 1 / L ) x. S. ( A (,) ( A + L ) ) ( exp ` ( W x. t ) ) _d t ) = %s ) )') % _AV
S['gf1avgh'] = '( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) -> ( %s /\\ %s ) )' % (
    HOL('( w e. CC |-> %s )' % AVG('A', 'L', 'w'), 'CC'), HOL('( w e. CC |-> %s )' % KK('A', 'B', 'L', 'w'), 'CC'))
S['gf1avgb'] = ('( ( ( A e. RR /\\ 0 <_ A ) /\\ L e. RR+ /\\ W e. CC ) -> ( ( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ '
                '( exp ` ( A x. ( Re ` W ) ) ) ) /\\ ( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( exp ` ( A + L ) ) ) ) )') % (_AV, _AV)
_K = KK('A', 'B', 'L', 'W')
_KQ = KQ('A', 'B', 'L', 'W')
S['gf1kq'] = '( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ /\\ W e. CC ) -> ( %s e. CC /\\ %s = ( W x. %s ) ) )' % (_KQ, _K, _KQ)
S['gf1kb'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) ) /\\ L e. RR+ /\\ W e. CC ) -> '
              '( ( ( Re ` W ) <_ 0 -> ( ( abs ` %s ) <_ ( ( exp ` ( B x. ( Re ` W ) ) ) + ( exp ` ( A x. ( Re ` W ) ) ) ) /\\ '
              '( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. ( L x. ( abs ` W ) ) ) <_ 4 ) ) /\\ '
              '( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( ( exp ` ( B + L ) ) + ( exp ` ( A + L ) ) ) ) ) )') % (_K, _K, _K, _K)
S['gf1kqb'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ A <_ B ) ) /\\ L e. RR+ /\\ ( W e. CC /\\ ( Re ` W ) <_ 0 ) ) -> '
               '( abs ` %s ) <_ ( B - A ) )') % _KQ
# ---- G1 -------------------------------------------------------------------------------------------
S['gf1g1h'] = '( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) -> %s )' % HOL('( w e. %s |-> %s )' % (HPM1, G1('A', 'B', 'L', 'w')), HPM1)
S['gf1g10'] = '( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) -> %s = ( B - A ) )' % G1('A', 'B', 'L', '0')
S['gf1g1v'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) /\\ ( W e. CC /\\ -u 1 < ( Re ` W ) /\\ W =/= 0 ) ) -> '
               '%s = ( ( _G ` W ) x. %s ) )') % (G1('A', 'B', 'L', 'W'), _K)
_GZ = G1('A', 'B', 'L', 'Z')
S['gf1g1b'] = ('( ( ( ( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ A <_ B ) ) /\\ ( L e. RR+ /\\ ( Y e. RR /\\ 1 <_ Y ) /\\ '
               '( ( B + A ) + ( 2 x. L ) ) <_ ( ( 5 / 2 ) x. Y ) ) ) /\\ ( Z e. CC /\\ -u ( 1 / ; 5 0 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 0 ) ) -> '
               '( ( abs ` %s ) <_ ( ( %s x. %s ) x. Y ) /\\ ( ( abs ` ( Im ` Z ) ) x. ( abs ` %s ) ) <_ ( %s x. %s ) /\\ '
               '( ( ( ( Im ` Z ) ^ 2 ) x. L ) x. ( abs ` %s ) ) <_ ( ( 4 x. %s ) x. %s ) ) )') % (
    _GZ, C7, EXPH('Z'), _GZ, C7, EXPH('Z'), _GZ, C7, EXPH('Z'))
# ---- Halasz duality (generic) ---------------------------------------------------------------------
AN = lambda n: 'if ( ( B ` %s ) = 0 , 0 , ( ( ( abs ` ( C ` %s ) ) ^ 2 ) / ( B ` %s ) ) )' % (n, n, n)
XV = lambda j, n: '( ( X ` %s ) ` %s )' % (j, n)
S['gf1hal.1'] = '( ph -> J e. Fin )'
S['gf1hal.2'] = '( ( ph /\\ ( j e. J /\\ n e. NN ) ) -> ( %s e. CC /\\ ( abs ` %s ) <_ 1 ) )' % (XV('j', 'n'), XV('j', 'n'))
S['gf1hal.3'] = '( ( ph /\\ n e. NN ) -> ( ( C ` n ) e. CC /\\ ( ( B ` n ) e. RR /\\ 0 <_ ( B ` n ) ) /\\ ( ( C ` n ) =/= 0 -> 0 < ( B ` n ) ) ) )'
S['gf1hal.4'] = '( ph -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % AN('n')
S['gf1hal.5'] = '( ph -> seq 1 ( + , B ) e. dom ~~> )'
S['gf1hal'] = ('( ph -> ( sum_ j e. J ( abs ` sum_ n e. NN ( ( C ` n ) x. %s ) ) ^ 2 ) <_ ( sum_ n e. NN %s x. '
               'sum_ j e. J sum_ k e. J ( abs ` sum_ n e. NN ( ( ( B ` n ) x. %s ) x. ( * ` %s ) ) ) ) )') % (XV('j', 'n'), AN('n'), XV('j', 'n'), XV('k', 'n'))
_XN = '( X ` %s )' % ZR('N', 'K')
_YN = '( Y ` %s )' % ZR('N', 'K')
S['gf1chb'] = ('( ( ( N e. NN /\\ X e. %s ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ K e. NN ) -> '
               '( ( %s x. ( K ^c -u S ) ) e. CC /\\ ( abs ` ( %s x. ( K ^c -u S ) ) ) <_ 1 ) )') % (DB_('N'), _XN, _XN)
S['gf1chc'] = ('( ( ( N e. NN /\\ ( X e. %s /\\ Y e. %s ) ) /\\ ( S e. CC /\\ T e. CC ) /\\ K e. NN ) -> '
               '( ( %s x. ( K ^c -u S ) ) x. ( * ` ( %s x. ( K ^c -u T ) ) ) ) = '
               '( ( ( X ( +g ` ( DChr ` N ) ) ( ( invg ` ( DChr ` N ) ) ` Y ) ) ` %s ) x. ( K ^c -u ( S + ( * ` T ) ) ) ) )') % (
    DB_('N'), DB_('N'), _XN, _YN, ZR('N', 'K'))
# ---- the Dirichlet polynomial M_h and its mass ------------------------------------------------------
S['gf1hbvs.1'] = '( ph -> ( R e. NN /\\ T e. NN /\\ K e. NN ) )'
S['gf1hbvs.2'] = '( ( ph /\\ d e. NN ) -> G e. CC )'
S['gf1hbvs'] = ('( ph -> sum_ d e. %s ( ( ( R hBV T ) ` d ) x. G ) = sum_ d e. %s if ( d || K , ( ( ( R hBV T ) ` d ) x. G ) , 0 ) )') % (
    DIV('K'), DIV('( R x. T )'))
_MH = MH('N', 'R', 'C', 'S')
_HM = HM('N', 'R')
S['gf1mhh'] = '( ( ( N e. V /\\ R e. W ) /\\ C : NN --> CC ) -> %s )' % HOL('( s e. CC |-> %s )' % MH('N', 'R', 'C', 's'), 'CC')
S['gf1mhb'] = ('( ( ( N e. V /\\ R e. W ) /\\ ( C : NN --> CC /\\ A. k e. NN ( abs ` ( C ` k ) ) <_ 1 ) /\\ '
               '( S e. CC /\\ 0 <_ ( Re ` S ) ) ) -> ( %s e. CC /\\ ( abs ` %s ) <_ %s ) )') % (_MH, _MH, _HM)
S['gf1hm'] = ('( ( N e. V /\\ ( R e. RR /\\ 1 <_ R ) ) -> ( 0 <_ %s /\\ %s <_ ( ( CTau ^ 2 ) x. ( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) ) ) )') % (_HM, _HM)

ORDER = [k for k in S if '.' not in k]


def hyps(label):
    return [(k, S[k]) for k in S if k.startswith(label + '.')]


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'gf1gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'gf1gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=gf1gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::gf1gc%s.1 |- %s\n' % (lab, S[lab]))
            for i, (k, h) in enumerate(hyps(lab)):
                f.write('h%d::gf1gc%s.%d |- %s\n' % (i + 2, lab, i + 2, h))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch', MM_DB=DB)
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in S:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)


# ---- step helpers (the cmlib pattern) -----------------------------------------------------------
from tm import W
import lin
from cl import lift, Closure, split_imp
lin.FASTPATH = True


def D(w, ante, ref, hyps, concl, name=None):
    """deduction step ( ante -> concl )"""
    return w.s(hyps, ref, '( %s -> %s )' % (ante, concl), name=name)


def mk(w, ante):
    return lambda ref, h, c: D(w, ante, ref, h, c)


def a1(w, ante, ref, fact, hyps=()):
    """closed fact lifted to ( ante -> fact )"""
    return w.s([w.s(list(hyps), ref, fact)], 'a1i', '( %s -> %s )' % (ante, fact))


def ehyps(w, label):
    """the $e hypothesis steps h1.. of LABEL"""
    return [w.s([], k, f, name='h%d' % (i + 1)) for i, (k, f) in enumerate(hyps(label))]


def chain(w, ante, terms, steps, rel=None):
    """( ante -> t0 R tn ) from steps[i] : ( ante -> t_i R_i t_(i+1) ); a tuple ('r', st) is reversed"""
    rel = rel or ['='] * len(steps)
    steps = list(steps)
    for i, st in enumerate(steps):
        if isinstance(st, tuple):
            steps[i] = w.s([st[1]], 'eqcomd', '( %s -> %s = %s )' % (ante, terms[i], terms[i + 1]))
    cur, cr = steps[0], rel[0]
    for i in range(1, len(steps)):
        r = rel[i]
        a, c = terms[0], terms[i + 1]
        if cr == '=' and r == '=':
            ref, nr = 'eqtrd', '='
        elif cr == '=':
            ref, nr = 'eqbrtrd', r
        elif r == '=':
            ref, nr = 'breqtrd', cr
        else:
            raise ValueError('chain: two inequalities')
        cur = w.s([cur, steps[i]], ref, '( %s -> %s %s %s )' % (ante, a, nr, c))
        cr = nr
    return cur


_LABELS = None


def known_labels():
    global _LABELS
    if _LABELS is None:
        import mm as _mm
        idx = _mm.INDEX
        if not os.path.exists(idx):
            _mm.build_index()
        _LABELS = set(l.split(' ', 1)[0] for l in open(idx))
        for fn in ('sorties/gf1.mm',):
            _LABELS |= set(re.findall(r'\n\s*([\w.-]+) \$[pe] ', open(os.path.join(HERE, '..', fn)).read()))
    return _LABELS


def run(w, only=()):
    if only and w.label not in only:
        return True
    kl = known_labels()
    bad = set()
    for ln in w.lines:
        parts = ln.split(':', 2)
        if len(parts) == 3:
            ref = parts[2].split(' ', 1)[0]
            if ref and ref not in kl and not ref.startswith(w.label + '.'):
                bad.add(ref)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, ' '.join(sorted(bad))))
    return w.run()


def proj(w, to, part):
    """( to -> part ) for part a conjunct of to (any depth), or a conjunction of such"""
    from cl import ante_path, _conjuncts
    part = ' '.join(part.split())
    if ante_path(part, to) is not None:
        idp = w.s([], 'id', '( %s -> %s )' % (part, part))
        return lift(w, idp, to)
    ps = _conjuncts(part)
    if ps is None:
        raise ValueError('proj: %s not derivable from %s' % (part, to))
    sts = [proj(w, to, x) for x in ps]
    return w.s(sts, 'jca' if len(ps) == 2 else '3jca', '( %s -> %s )' % (to, part))


def tsub(f, m):
    """simultaneous token substitution"""
    return ' '.join(m.get(t, t) for t in f.split())


def norm(f):
    return ' '.join(f.split())


def build(w, ante, formula, facts):
    """( ante -> formula ) for a conjunction whose leaves are keys of facts (steps ( ante -> leaf ))"""
    from cl import _conjuncts
    f = norm(formula)
    if f in facts:
        return facts[f]
    ps = _conjuncts(f)
    if ps is None:
        raise KeyError('build: no fact for %s' % f)
    sts = [build(w, ante, p, facts) for p in ps]
    return w.s(sts, 'jca' if len(ps) == 2 else '3jca', '( %s -> %s )' % (ante, f))


def holeq(w, ante, eqstep, F, G, D):
    """( ante -> ( HOL(F,D) -> HOL(G,D) ) ) from eqstep ( ante -> F = G )"""
    e1 = D_(w, ante, 'eleq1d', [eqstep], '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (F, D, G, D))
    e2 = D_(w, ante, 'oveq2d', [eqstep], '( CC _D %s ) = ( CC _D %s )' % (F, G))
    e3 = D_(w, ante, 'dmeqd', [e2], 'dom ( CC _D %s ) = dom ( CC _D %s )' % (F, G))
    e4 = D_(w, ante, 'sseq2d', [e3], '( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) )' % (D, F, D, G))
    e5 = D_(w, ante, 'anbi12d', [e1, e4], '( %s <-> %s )' % (HOL(F, D), HOL(G, D)))
    return D_(w, ante, 'biimpd', [e5], '( %s -> %s )' % (HOL(F, D), HOL(G, D)))


def D_(w, ante, ref, hyps, concl):
    return w.s(hyps, ref, '( %s -> %s )' % (ante, concl))



def phsub(w, C, a, b):
    """( a = b -> PH(C, a) = PH(C, b) ) for set variables a, b"""
    e1 = w.s([], 'eqeq1', '( %s = %s -> ( %s = 0 <-> %s = 0 ) )' % (a, b, a, b))
    e2 = w.s([], 'oveq2', '( %s = %s -> ( %s x. %s ) = ( %s x. %s ) )' % (a, b, C, a, C, b))
    e3 = w.s([e2], 'fveq2d', '( %s = %s -> ( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. %s ) ) )' % (a, b, C, a, C, b))
    e4 = w.s([e3], 'oveq1d', '( %s = %s -> ( ( exp ` ( %s x. %s ) ) - 1 ) = ( ( exp ` ( %s x. %s ) ) - 1 ) )' % (a, b, C, a, C, b))
    e5 = w.s([], 'id', '( %s = %s -> %s = %s )' % (a, b, a, b))
    e6 = w.s([e4, e5], 'oveq12d', '( %s = %s -> ( ( ( exp ` ( %s x. %s ) ) - 1 ) / %s ) = ( ( ( exp ` ( %s x. %s ) ) - 1 ) / %s ) )' % (a, b, C, a, a, C, b, b))
    return w.s([e1, e6], 'ifbieq2d', '( %s = %s -> %s = %s )' % (a, b, PH(C, a), PH(C, b)))
