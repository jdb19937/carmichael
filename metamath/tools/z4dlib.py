"""Sortie Z4d helpers (Route Z: LargeSieve.lean 1352-1535 and 2001-2506: the Lebesgue block,
the window integrals and presifted_large_sieve).

STATEMENTS / HYPS are the frozen text of Z4d-blueprint.md section 2.
`MM_DB=sorties/z4d.mm python3 tools/z4dlib.py [LABEL...]` grammar-checks them with mmatch.
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mvlib import HK, SX, TRI, ABS2, CCJ, IOO, ITG, DB, LZ

STATEMENTS = {}
HYPS = {}

# lin.py builds a fresh congr.StepGen('p') for every power expansion, so two linarith calls with
# integer powers in one worksheet both emit a step `p1`.  Runtime patch (shared module untouched):
# steps with prefix 'p' draw from one global counter.
import congr as _cg
if not getattr(_cg.StepGen, '_z4d', False):
    class _GSG(_cg.StepGen):
        _z4d = True
        _n = [0]

        def fresh(self):
            if self.prefix != 'p':
                return _cg.StepGen.fresh(self) if False else super().fresh()
            _GSG._n[0] += 1
            return 'pz%d' % _GSG._n[0]
    _cg.StepGen = _GSG


def st(label, text, hyps=()):
    STATEMENTS[label] = text
    HYPS[label] = list(hyps)


# ---- abbreviations -------------------------------------------------------------------------
ICC = lambda a, b: '( %s [,] %s )' % (a, b)
H8 = '( _pi / ( 8 x. T ) )'                    # Lean pi / (8 T): the window half-width
D4 = '( _pi / ( 4 x. T ) )'                    # Lean pi / (4 T) = 2 H8
RHO = '( ( exp ` %s ) - 1 )' % D4               # Lean rho


def WIF(Lv, H, C, u='u'):
    """window indicator summand if ( | L - u | <_ H , C , 0 )"""
    return 'if ( ( abs ` ( %s - %s ) ) <_ %s , %s , 0 )' % (Lv, u, H, C)


def WS(H, i='i', u='u'):
    """Lean sum_{i in s.filter (|lam i - x| <_ H)} c i, as an indicator sum over P"""
    return 'sum_ %s e. P %s' % (i, WIF('( L ` %s )' % i, H, '( C ` %s )' % i, u))


def BIL(D):
    return 'sum_ i e. P sum_ j e. P ( %s x. %s )' % (CCJ('i', 'j'), TRI(D, '( ( L ` i ) - ( L ` j ) )'))


def PC(f):
    return '{ y e. %s | ( %s DChrCond y ) = %s }' % (DB(f), f, f)


Q0S = '( 1 ... ( |_ ` Q ) )'
SIFT = 'A. k e. S A. p e. Prime ( p || k -> Q < p )'
HPS = '( ( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) ) /\\ ( S e. Fin /\\ S C_ NN /\\ A : S --> CC ) /\\ %s )' % SIFT
LOGN = '-u ( log ` n )'
AX = '( ( A ` n ) x. ( x ` ( %s ` n ) ) )' % LZ('f')        # Lean a n * psi n
CPW = '( n ^c ( -u t x. _i ) )'                               # Lean n ^ (-(t) * I)
DIR = 'sum_ n e. S ( %s x. %s )' % (AX, CPW)
WAX = 'sum_ n e. S %s' % WIF(LOGN, H8, AX)                     # the window sum at (f, x)
LOGW = '( log ` ( Q / f ) )'
AN2 = ABS2('( A ` n )')


def GW(n='n'):
    return '( ( ( Q ^ 2 ) + ( ( ( 2 x. _pi ) x. %s ) x. %s ) ) + ( 4 x. _pi ) )' % (RHO, n)


LHSU = 'sum_ f e. %s ( %s x. sum_ x e. %s %s )' % (Q0S, LOGW, PC('f'), ABS2(WAX))
RHSU = 'sum_ n e. S %s' % WIF(LOGN, H8, '( %s x. %s )' % (GW(), AN2))
LHST = 'sum_ f e. %s ( %s x. sum_ x e. %s %s )' % (Q0S, LOGW, PC('f'), ITG(IOO('-u T', 'T'), ABS2(DIR)))
C48 = '( ( ; 4 8 x. ( T ^ 2 ) ) / _pi )'

# ---- A. generic Lebesgue lemmas over RR ------------------------------------------------------
IND = 'if ( u e. %s , K , 0 )' % ICC('U', 'V')
st('lsind', '( ( U e. RR /\\ V e. RR /\\ K e. CC ) -> ( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( K x. if ( U <_ V , ( V - U ) , 0 ) ) ) )'
   % (IND, ITG('RR', IND, 'u')))
PAIR = 'if ( ( ( abs ` ( X - u ) ) <_ H /\\ ( abs ` ( Y - u ) ) <_ H ) , K , 0 )'
PAIRC = '( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( K x. %s ) )' % (PAIR, ITG('RR', PAIR, 'u'), TRI('( 2 x. H )', '( X - Y )'))
st('lswpairlem', '( ( ( X e. RR /\\ Y e. RR /\\ X <_ Y ) /\\ ( H e. RR+ /\\ K e. CC ) ) -> %s )' % PAIRC)
st('lswpair', '( ( ( X e. RR /\\ Y e. RR ) /\\ ( H e. RR+ /\\ K e. CC ) ) -> %s )' % PAIRC)
WI = 'sum_ i e. P %s' % WIF('L', 'H', 'G')
st('lswint', '( ph -> ( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( ( 2 x. H ) x. sum_ i e. P G ) ) )' % (WI, ITG('RR', WI, 'u')),
   [('1', '( ph -> P e. Fin )'), ('2', '( ( ph /\\ i e. P ) -> L e. RR )'),
    ('3', '( ( ph /\\ i e. P ) -> G e. CC )'), ('4', '( ph -> H e. RR+ )')])
st('lswifmul', '( ( B e. CC /\\ C e. CC ) -> ( if ( ph , B , 0 ) x. ( * ` if ( ps , C , 0 ) ) ) = if ( ( ph /\\ ps ) , ( B x. ( * ` C ) ) , 0 ) )')
st('lswsq', '( ( %s /\\ H e. RR+ ) -> ( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( Re ` %s ) ) )'
   % (HK, ABS2(WS('H')), ITG('RR', ABS2(WS('H')), 'u'), BIL('( 2 x. H )')))
st('lstint', '( ( T e. RR+ /\\ %s ) -> %s <_ ( %s x. %s ) )'
   % (HK, ITG(IOO('-u T', 'T'), ABS2(SX('t'))), C48, ITG('RR', ABS2(WS(H8)), 'u')))

# ---- B. numerics -------------------------------------------------------------------------------
st('pile165', '_pi <_ ( ; 1 6 / 5 )')
st('lsexpb', '( ( T e. RR /\\ 1 <_ T ) -> ( ( ( ; 2 4 x. _pi ) x. T ) x. %s ) <_ ; 9 5 )' % RHO)
st('lsnum', '( ( ( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) ) /\\ ( N e. NN /\\ B e. RR /\\ 0 <_ B ) ) -> '
   '( ( ; 1 2 x. T ) x. ( %s x. B ) ) <_ ( ; ; 1 0 0 x. ( ( N + ( ( Q ^ 2 ) x. T ) ) x. B ) ) )' % GW('N'))

# ---- C. the sieve side ---------------------------------------------------------------------------
st('lscopsift', '( ( ( Q e. RR /\\ N e. NN /\\ A. p e. Prime ( p || N -> Q < p ) ) /\\ D e. %s ) -> ( N gcd D ) = 1 )' % Q0S)
st('lspwb', '( ( %s /\\ u e. RR ) -> %s <_ %s )' % (HPS, LHSU, RHSU))

LO = '( exp ` ( -u u - %s ) )' % H8
HI = '( exp ` ( -u u + %s ) )' % H8
EE = '( ( ( %s - %s ) / 2 ) + 1 )' % (HI, LO)
MM = '( |_ ` ( ( %s + %s ) / 2 ) )' % (LO, HI)
st('lspwin', '( ( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ N e. NN ) /\\ ( abs ` ( -u ( log ` N ) - u ) ) <_ %s ) -> ( %s <_ N /\\ N <_ %s ) )' % (H8, LO, HI))
st('lspwe', '( ( ( T e. RR /\\ 1 <_ T ) /\\ ( u e. RR /\\ N e. RR ) /\\ %s <_ N ) -> ( ( 4 x. _pi ) x. %s ) <_ ( ( ( ( 2 x. _pi ) x. %s ) x. N ) + ( 4 x. _pi ) ) )' % (LO, EE, RHO))
st('lspwf', '( ( ( X e. RR /\\ Y e. RR ) /\\ ( N e. RR /\\ X <_ N /\\ N <_ Y ) ) -> ( abs ` ( N - ( |_ ` ( ( X + Y ) / 2 ) ) ) ) <_ ( ( ( Y - X ) / 2 ) + 1 ) )')

# ---- D. assembly ---------------------------------------------------------------------------------
st('lscpow', '( ( N e. NN /\\ t e. RR ) -> ( N ^c ( -u t x. _i ) ) = ( exp ` ( _i x. ( -u ( log ` N ) x. t ) ) ) )')
st('lspsa', '( ( %s /\\ ( f e. NN /\\ x e. %s ) ) -> ( ( u e. RR |-> %s ) e. L^1 /\\ %s e. RR /\\ %s <_ ( %s x. %s ) ) )'
   % (HPS, DB('f'), ABS2(WAX), ITG(IOO('-u T', 'T'), ABS2(DIR)), ITG(IOO('-u T', 'T'), ABS2(DIR)), C48, ITG('RR', ABS2(WAX), 'u')))
st('lspsb', '( %s -> ( ( u e. RR |-> %s ) e. L^1 /\\ %s <_ ( %s x. %s ) ) )' % (HPS, LHSU, LHST, C48, ITG('RR', LHSU, 'u')))
st('lspresift', '( %s -> %s <_ ( ; ; 1 0 0 x. sum_ n e. S ( ( n + ( ( Q ^ 2 ) x. T ) ) x. %s ) ) )' % (HPS, LHST, AN2))


def gramcheck(labels):
    out = {}
    for lab in labels:
        fs = [STATEMENTS[lab]] + [f for _, f in HYPS[lab]]
        ok = True
        for k, f in enumerate(fs):
            path = 'worksheets/z4dgc%s%d.mmp' % (lab, k)
            with open(path, 'w') as fh:
                fh.write('$( <MM> <PROOF_ASST> THEOREM=z4dgc%s%d  LOC_AFTER=?\n\n* gc\n\n'
                         'h1::z4dgc%s%d.1 |- %s\nqed:1:idi |- %s\n$)\n' % (lab, k, lab, k, f, f))
            env = dict(os.environ, MM_ENGINE='mmatch')
            r = subprocess.run(['python3', 'tools/mm.py', 'unify', path], capture_output=True, text=True, env=env)
            if 'UNIFY OK' in r.stdout:
                os.remove(path)
            else:
                ok = False
                print(lab, k, r.stdout[-1200:], r.stderr[-600:])
        out[lab] = ok
    return out


if __name__ == '__main__':
    for lab, ok in gramcheck(sys.argv[1:] or list(STATEMENTS)).items():
        print(('OK   ' if ok else 'BAD  ') + lab)
