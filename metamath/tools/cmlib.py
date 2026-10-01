"""Sortie CM: helpers and the frozen statements (CensusMid.lean: the middle-regime census, MidCensusHyp).

    python3 tools/cmlib.py print                                   # the frozen table
    MM_DB=sorties/cm.mm python3 tools/cmlib.py check [LABEL...]     # grammar check (mmatch)

Letters.  Census: abscissa S, height V, cutoff Z (integer K), W = Z (V + 2), L = log W.  Detection (kd2det):
character N X, eta E, window half-width D, height t (integration), u (the X1..X2 integration), zero z.
Family sums: conductor d, character x.  PWS binds p a; BC binds y o; CNT binds m y o; MCH binds u v w.
Generic lemmas: index set P (binders p q), t-domain A, u-range Y Z.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from tm import W
import lin
from cl import lift, Closure, split_imp
from cen2lib import BC, CNT, C2, C3, THR, MCH, BND, LOGZ, TYP, RNG, F3940, dec, split_all
from kd1lib import NDET, MDET, XONE, XTWO
lin.FASTPATH = True

DB = 'sorties/cm.mm'
_TXT = {}


def stmt(label):
    """the assertion of LABEL from sorties/cm.mm or carmichael.mm, without |-"""
    for fn in (DB, 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if fn == DB or fn not in _TXT:
            _TXT[fn] = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), _TXT[fn], re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects --------------------------------------------------------------------------------
BASE = lambda N: '( Base ` ( DChr ` %s ) )' % N
CHV = lambda n, N='N', X='X': '( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` %s ) )' % (X, N, n)
PSET = lambda Y, U, a='a': '{ %s e. ( 1 ... ( |_ ` %s ) ) | ( %s e. Prime /\\ %s < %s ) }' % (a, U, a, Y, a)
CP = lambda p, T, N='N', X='X': '( ( %s x. ( log ` %s ) ) x. ( %s ^c ( -u 1 - ( %s x. _i ) ) ) )' % (CHV(p, N, X), p, p, T)
PWS = lambda T, Y, U, N='N', X='X', p='p': 'sum_ %s e. %s %s' % (p, PSET(Y, U), CP(p, T, N, X))
ABS2 = lambda E: '( ( abs ` %s ) ^ 2 )' % E
IOO = lambda a, b: '( %s (,) %s )' % (a, b)
II = lambda T, Y, Z, N='N', X='X': 'S. ( %s (,) %s ) ( %s / u ) _d u' % (Y, Z, ABS2(PWS(T, Y, 'u', N, X)))
JJ = lambda H, Y, U, N='N', X='X': 'S. ( -u %s (,) %s ) %s _d t' % (H, H, ABS2(PWS('t', Y, U, N, X)))
LW = '( log ` W )'
R5000 = '( 1 / ; ; ; 5 0 0 0 )'
MW = MDET('E', LW)
X1 = XONE('E', LW)
X2 = XTWO('E', LW)
CDET = '( ( ( E ^ 3 ) x. %s ) x. ( exp ` ( 6 x. %s ) ) )' % (MW, MW)
V1 = '( V + 1 )'
EE2 = '( ( exp ` 1 ) ^ 2 )'
C750 = '( ; ; 7 5 0 x. %s )' % EE2
C3072 = dec('3072000')
AMACH = dec('4' + '0' * 9)          # machine constant a = 4 . 10^9 (Lean 1.2 . 10^8)
BMACH = dec('4' + '0' * 10)         # machine slope b = 4 . 10^10 (Lean 1.2 . 10^9)
LFN = stmt('kd2det').split(' E. p e. CC ( ( ', 1)[1].split(' ` p ) = 0', 1)[0]

S = {}
# ---- generic lemmas -------------------------------------------------------------------------
# |sum_p if(p <_ U, F, 0)|^2 as a double sum (absvalsq, fsumcj, fsum2mul, lswifmul)
S['cmsqx.1'] = '( ph -> P e. Fin )'
S['cmsqx.2'] = '( ( ph /\\ p e. P ) -> F e. CC )'
S['cmsqx.3'] = '( p = q -> F = G )'
S['cmsqx'] = ('( ph -> ( ( abs ` sum_ p e. P if ( p <_ U , F , 0 ) ) ^ 2 ) = '
              'sum_ p e. P sum_ q e. P if ( ( p <_ U /\\ q <_ U ) , ( F x. ( * ` G ) ) , 0 ) )')
# integral of a guarded integrand (the guard free of the integration letter)
S['cmitgif.1'] = '( ph -> ( x e. A |-> B ) e. L^1 )'
S['cmitgif.2'] = '( ( ph /\\ x e. A ) -> B e. CC )'
S['cmitgif'] = ('( ph -> ( ( x e. A |-> if ( ps , B , 0 ) ) e. L^1 /\\ '
                'S. A if ( ps , B , 0 ) _d x = if ( ps , S. A B _d x , 0 ) ) )')
# the u-integral of a double step sum against du/u (kd2ind, kd2log, itgfsum)
MXU = 'if ( p <_ q , q , p )'
S['cmuint.1'] = '( ph -> ( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z ) )'
S['cmuint.2'] = '( ph -> ( P e. Fin /\\ P C_ ( Y (,] Z ) ) )'
S['cmuint.3'] = '( ( ph /\\ ( p e. P /\\ q e. P ) ) -> K e. CC )'
UIF = 'sum_ p e. P sum_ q e. P if ( ( p <_ u /\\ q <_ u ) , ( K / u ) , 0 )'
S['cmuint'] = ('( ph -> ( ( u e. ( Y (,) Z ) |-> %s ) e. L^1 /\\ S. ( Y (,) Z ) %s _d u = '
               'sum_ p e. P sum_ q e. P ( K x. ( ( log ` Z ) - ( log ` %s ) ) ) ) )') % (UIF, UIF, MXU)
# the swap of the t- and u-integrals for a step Dirichlet polynomial (Lean integral_integral_swap)
DSUM = 'sum_ p e. P if ( p <_ u , F , 0 )'
S['cmfub.1'] = S['cmuint.1']
S['cmfub.2'] = S['cmuint.2']
S['cmfub.3'] = '( ph -> A e. dom vol )'
S['cmfub.4'] = '( ( ph /\\ ( p e. P /\\ t e. A ) ) -> F e. CC )'
S['cmfub.5'] = '( p = q -> F = G )'
S['cmfub.6'] = '( ( ph /\\ ( p e. P /\\ q e. P ) ) -> ( t e. A |-> ( F x. ( * ` G ) ) ) e. L^1 )'
_IU = 'S. ( Y (,) Z ) ( %s / u ) _d u' % ABS2(DSUM)
_JT = 'S. A %s _d t' % ABS2(DSUM)
S['cmfub'] = ('( ph -> ( ( t e. A |-> %s ) e. L^1 /\\ ( u e. ( Y (,) Z ) |-> ( %s / u ) ) e. L^1 /\\ '
              'S. A %s _d t = S. ( Y (,) Z ) ( %s / u ) _d u ) )') % (_IU, _JT, _IU, _JT)

# ---- the prime window sum -------------------------------------------------------------------
NX = '( N e. NN /\\ X e. %s )' % BASE('N')
S['cmcnt'] = '( ( %s /\\ P e. NN ) -> ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (NX, CP('P', 't'))
S['cmpwt'] = ('( ( %s /\\ H e. RR /\\ ( Y e. RR /\\ U e. RR ) ) -> ( ( t e. ( -u H (,) H ) |-> %s ) e. L^1 /\\ '
              '%s e. RR /\\ 0 <_ %s ) )') % (NX, ABS2(PWS('t', 'Y', 'U')), JJ('H', 'Y', 'U'), JJ('H', 'Y', 'U'))
S['cmswp'] = ('( ( %s /\\ H e. RR /\\ ( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z ) ) -> ( ( t e. ( -u H (,) H ) |-> %s ) e. L^1 /\\ '
              '( u e. ( Y (,) Z ) |-> ( %s / u ) ) e. L^1 /\\ S. ( -u H (,) H ) %s _d t = S. ( Y (,) Z ) ( %s / u ) _d u ) )') % (
    NX, II('t', 'Y', 'Z'), JJ('H', 'Y', 'u'), II('t', 'Y', 'Z'), JJ('H', 'Y', 'u'))

# ---- one zero per bad character, the detection window -------------------------------------
LFNZ = '( ( %s ` z ) = 0 /\\ ( ( S <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 ) /\\ ( abs ` ( Im ` z ) ) <_ V ) )' % LFN
S['cmzero'] = ('( ( ( ( N e. NN /\\ 2 <_ N ) /\\ X e. %s ) /\\ ( ( S e. RR /\\ 0 < S ) /\\ V e. RR ) ) -> '
               '( ( X e. %s /\\ X =/= ( 0g ` ( DChr ` N ) ) ) /\\ E. z e. CC %s ) )') % (BC('S', 'V', 'N'), BASE('N'), LFNZ)
DETH = ('( ( ( ( N e. NN /\\ 2 <_ N ) /\\ X e. %s ) /\\ ( ( S e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( 0 < S /\\ S <_ 1 ) /\\ '
        '( N <_ W /\\ ( V + 3 ) <_ W ) ) ) /\\ ( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ '
        '( ( D e. RR+ /\\ D <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( D ^ 2 ) ) <_ ( E ^ 2 ) ) ) )') % (BC('S', 'V', 'N'), R5000, LW)
S['cmdet'] = '( %s -> ( 2 x. D ) <_ ( %s x. S. ( -u %s (,) %s ) %s _d t ) )' % (DETH, CDET, V1, V1, II('t', X1, X2))

# ---- the sieve at fixed u -------------------------------------------------------------------
S['cmlsq'] = ('( ( ( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z ) /\\ ( A e. Fin /\\ A C_ Prime /\\ A C_ ( 0 [,] Z ) ) ) -> '
              'sum_ p e. A ( ( ( log ` p ) ^ 2 ) / p ) <_ ( ( ( ; 1 5 / 4 ) x. %s ) x. ( ( log ` Z ) ^ 2 ) ) )') % EE2
FAMJ = lambda U, Y: 'sum_ d e. ( 2 ... K ) sum_ x e. %s %s' % (BC('S', 'V', 'd'), JJ(V1, Y, U, 'd', 'x'))
SVH = ('( ( ( S e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( 1 <_ V /\\ 2 <_ W ) /\\ ( K e. ZZ /\\ K <_ W /\\ ( V + 3 ) <_ W ) ) /\\ '
       '( ( Y e. RR /\\ ( W ^ 5 ) <_ Y ) /\\ ( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z ) /\\ ( U e. RR /\\ Y < U /\\ U <_ Z ) ) )')
AMAP = lambda Y, U: '( b e. %s |-> ( ( log ` b ) / b ) )' % PSET(Y, U)
SIEVE_T = lambda T, Y, U, N='N', X='X': 'sum_ n e. %s ( ( ( %s ` n ) x. %s ) x. ( n ^c ( -u %s x. _i ) ) )' % (PSET(Y, U), AMAP(Y, U), CHV('n', N, X), T)
S['cmsid'] = '( ( %s /\\ ( Y e. RR /\\ U e. RR ) /\\ T e. RR ) -> %s = %s )' % (NX, SIEVE_T('T', 'Y', 'U'), PWS('T', 'Y', 'U'))
SRH = ('( ( ( V e. RR /\\ W e. RR ) /\\ ( 1 <_ V /\\ 2 <_ W /\\ ( V + 3 ) <_ W ) ) /\\ '
       '( ( Y e. RR /\\ ( W ^ 5 ) <_ Y ) /\\ ( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z ) /\\ ( U e. RR /\\ U <_ Z ) ) )')
S['cmsrh'] = ('( %s -> ( ; ; 1 0 0 x. sum_ n e. %s ( ( n + ( ( ( W ^ 2 ) ^ 2 ) x. ( V + 1 ) ) ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) ) ) '
              '<_ ( %s x. ( ( log ` Z ) ^ 2 ) ) )') % (SRH, PSET('Y', 'U'), AMAP('Y', 'U'), '( ; ; 7 5 0 x. ( ( exp ` 1 ) ^ 2 ) )')
S['cmsvu'] = '( %s -> ( %s x. %s ) <_ ( %s x. ( ( log ` Z ) ^ 2 ) ) )' % (SVH, LW, FAMJ('U', 'Y'), C750)

# ---- the family bound -----------------------------------------------------------------------
RCNT = 'sum_ d e. ( 2 ... K ) ( # ` %s )' % BC('S', 'V', 'd')
FAMH = ('( ( ( ( S e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( 0 < S /\\ S <_ 1 ) /\\ ( 1 <_ V /\\ 2 <_ W ) ) /\\ '
        '( K e. ZZ /\\ K <_ W /\\ ( V + 3 ) <_ W ) ) /\\ ( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ '
        '( ( ( D e. RR+ /\\ D <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( D ^ 2 ) ) <_ ( E ^ 2 ) ) /\\ ( W ^ 5 ) <_ %s ) ) )') % (R5000, LW, X1)
S['cmfam'] = ('( %s -> ( ( ( 2 x. D ) x. %s ) x. %s ) <_ ( ( %s x. %s ) x. ( ( ( log ` %s ) ^ 2 ) x. ( ( log ` %s ) - ( log ` %s ) ) ) ) )') % (
    FAMH, RCNT, LW, C750, CDET, X2, X2, X1)

# ---- the machine bound and the discharge ----------------------------------------------------
WIN = '( ( 1 - S ) < ( 2 / %s ) /\\ %s < ( ( 1 - S ) x. %s ) )' % (C3, THR, LOGZ('Z', 'V'))
MEXP = '( exp ` ( %s + ( ( %s x. ( 1 - S ) ) x. %s ) ) )' % (AMACH, BMACH, LOGZ('Z', 'V'))
ETA0 = lambda L='L': '( ( 1 - S ) + ( 1 / ( ; 1 2 x. %s ) ) )' % L
EEX = lambda L='L': '( ( ; 1 1 / ; 1 0 ) x. %s )' % ETA0(L)
DDX = lambda L='L': '( %s / 3 )' % ETA0(L)
def CDX(E, L):
    M = MDET(E, L)
    return '( ( ( %s ^ 3 ) x. %s ) x. ( exp ` ( 6 x. %s ) ) )' % (E, M, M)
def FAMC(L='L', R='R'):
    E = EEX(L)
    x1, x2 = XONE(E, L), XTWO(E, L)
    return ('( ( ( 2 x. %s ) x. %s ) x. %s ) <_ ( ( %s x. %s ) x. ( ( ( log ` %s ) ^ 2 ) x. ( ( log ` %s ) - ( log ` %s ) ) ) )') % (
        DDX(L), R, L, C750, CDX(E, L), x2, x2, x1)
MEXPL = lambda L='L': '( exp ` ( %s + ( ( %s x. ( 1 - S ) ) x. %s ) ) )' % (AMACH, BMACH, L)
S['cmbud'] = ('( ( ( ( S e. RR /\\ S <_ 1 ) /\\ ( L e. RR /\\ ; ; 5 0 0 < L ) /\\ ( R e. RR /\\ 0 <_ R ) ) /\\ %s ) -> ( 1 + R ) <_ %s )') % (FAMC(), MEXPL())
S['cmmach'] = '( ( %s /\\ %s /\\ %s ) -> %s <_ %s )' % (TYP, RNG, WIN, CNT('S', 'V', '( |_ ` Z )'), MEXP)
_MB = MCH.split(' A. w e. RR ', 1)[1]
MBODY = split_imp(' '.join({'u': 'S', 'v': 'V', 'w': 'Z'}.get(x, x) for x in _MB.split()))[0]
S['cmabs'] = '( ( %s /\\ %s ) -> %s <_ %s )' % (TYP, MBODY, CNT('S', 'V', '( |_ ` Z )'), BND('S', 'V', 'Z'))
S['cmmch'] = MCH
S['cmcc'] = '( ( %s /\\ %s ) -> %s <_ %s )' % (TYP, RNG, CNT('S', 'V', '( |_ ` Z )'), BND('S', 'V', 'Z'))
S['cmbad'] = ('( ( ( %s /\\ %s ) /\\ ( D e. Fin /\\ A. m e. D ( ( m e. NN0 /\\ 2 <_ m ) /\\ ( m <_ Z /\\ %s =/= (/) ) ) ) ) -> '
              '( # ` D ) <_ %s )') % (TYP, RNG, BC('S', 'V', 'm'), BND('S', 'V', 'Z'))
ORDER = [k for k in S if '.' not in k]


def hyps(label):
    return [(k, S[k]) for k in S if k.startswith(label + '.')]


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'cmgc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'cmgc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=cmgc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::cmgc%s.1 |- %s\n' % (lab, S[lab]))
            for i, (k, h) in enumerate(hyps(lab)):
                f.write('h%d::cmgc%s.%d |- %s\n' % (i + 2, lab, i + 2, h))
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


# ---- step helpers ----------------------------------------------------------------------------
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


def inst(label, sub):
    """the statement of LABEL with the token map sub, split into (hyp, concl)"""
    from c8lib import tsub
    return split_imp(tsub(stmt(label), sub))


def use(w, A, label, sub, hstep):
    """( A -> C' ) from hstep : ( A -> H' ), LABEL : ( H -> C ) instantiated by sub"""
    h, c = inst(label, sub)
    return w.s([hstep, w.inst(label)], 'syl', '( %s -> %s )' % (A, c))


def run(w, only=()):
    if only and w.label not in only:
        return True
    return w.run()


def ante_of_step(w, step):
    from cl import formula_of
    return split_imp(formula_of(w, step))


def proj(w, to, part):
    """( to -> part ) for part a conjunct of to (any depth), or a conjunction of such (jca / 3jca)"""
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


def rean(w, step, to):
    """re-antecede STEP ( A -> X ) to ( to -> X ) when every leaf conjunct of A is a conjunct of to"""
    a, x = ante_of_step(w, step)
    from cl import ante_path
    if ante_path(a, to) is not None:
        return lift(w, step, to)
    pr = proj(w, to, a)
    return w.s([pr, step], 'syl', '( %s -> %s )' % (to, x))


def ere(w, C):
    """( C -> ( exp ` 1 ) e. RR )"""
    return a1(w, C, 'ax-mp', '( exp ` 1 ) e. RR', [w.s([], '1re', '1 e. RR'), w.inst('reefcl')])


def epos(w, C):
    """( C -> 0 < ( exp ` 1 ) )"""
    return a1(w, C, 'ax-mp', '0 < ( exp ` 1 )', [w.s([], '1re', '1 e. RR'), w.inst('efgt0')])
