"""Sortie C8, section 2: the analytic logarithm (hollogex, hollogdv, hollog)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from congr import mptval

CCPR = 'CC e. { RR , CC }'
EXPG = 'A. z e. E ( exp ` ( g ` z ) ) = ( F ` z )'


def gen_hollogex():
    w = W('hollogex', 'Existence of a holomorphic logarithm of a function holomorphic and zero-free on a rectangle, on any open subset of it.')
    A0 = '( %s /\\ ( %s /\\ %s ) )' % (ABGEO, NZ0, EOPN)
    abgeo = w.s([], 'simpl', '( %s -> %s )' % (A0, ABGEO))
    nzo = w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (A0, NZ0, EOPN))
    nz = w.s([nzo, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, NZ0))
    eop = w.s([nzo, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, EOPN))
    hn = w.s([w.s([abgeo, nz], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, ABGEO, NZ0)), w.inst('hlogn')], 'syl', '( %s -> E. n e. NN %s )' % (A0, SLITP('n')))
    d = abgeoctx(w, A0, abgeo)
    kd = w.s([d['hol'], d['ab'], d['nest'], w.inst('holnss')], 'syl3anc', '( %s -> ( A crect B ) C_ D )' % A0)
    CONC = 'E. g ( %s /\\ %s )' % (HOLE('g'), EXPG)
    A1 = '( ( %s /\\ n e. NN ) /\\ %s )' % (A0, SLITP('n'))
    a0 = w.s([], 'simpll', '( %s -> %s )' % (A1, A0))
    nn = w.s([], 'simplr', '( %s -> n e. NN )' % A1)
    sl = w.s([], 'simpr', '( %s -> %s )' % (A1, SLITP('n')))
    def up(st, f):
        return w.s([a0, st], 'syl', '( %s -> %s )' % (A1, f))
    abg1 = w.s([up(d['hol'], HOL), w.s([up(d['ab'], AB), up(d['geo'], GEO)], 'jca', '( %s -> ( %s /\\ %s ) )' % (A1, AB, GEO))], 'jca', '( %s -> %s )' % (A1, ABG))
    nz1 = up(nz, NZ0)
    eop1 = up(eop, EOPN)
    kd1 = up(kd, '( A crect B ) C_ D')
    LN = LAM('n')
    hh = w.s([w.s([abg1, nz1], 'jca', '( %s -> ( %s /\\ %s ) )' % (A1, ABG, NZ0)), w.s([nn, sl], 'jca', '( %s -> ( n e. NN /\\ %s ) )' % (A1, SLITP('n'))),
              w.s([eop1, kd1], 'jca', '( %s -> ( %s /\\ ( A crect B ) C_ D ) )' % (A1, EOPN)), w.inst('hlogh')], 'syl3anc', '( %s -> %s )' % (A1, HOLE(LN)))
    # exp ( LAM ` z ) = F ` z
    A2 = '( %s /\\ z e. E )' % A1
    zin = w.s([], 'simpr', '( %s -> z e. E )' % A2)
    ek = w.s([w.s([eop1, w.inst('simpr')], 'syl', '( %s -> E C_ ( A crect B ) )' % A1)], 'adantr', '( %s -> E C_ ( A crect B ) )' % A2)
    zk = w.s([ek, zin], 'sseldd', '( %s -> z e. ( A crect B ) )' % A2)
    val, v = mptval(w, A2, 'x', 'E', LAMB('n', 'x'), 'z', zin, mp=LN, gen=StepGen('mv'))
    assert v == LAMB('n', 'z'), v
    ex = w.s([w.s([w.s([abg1, nz1], 'jca', '( %s -> ( %s /\\ %s ) )' % (A1, ABG, NZ0))], 'adantr', '( %s -> ( %s /\\ %s ) )' % (A2, ABG, NZ0)),
              w.s([w.s([w.s([nn, kd1], 'jca', '( %s -> ( n e. NN /\\ ( A crect B ) C_ D ) )' % A1)], 'adantr', '( %s -> ( n e. NN /\\ ( A crect B ) C_ D ) )' % A2)], 'idi',
                  '( %s -> ( n e. NN /\\ ( A crect B ) C_ D ) )' % A2), zk, w.inst('hlogexp')], 'syl3anc', '( %s -> ( exp ` %s ) = ( F ` z ) )' % (A2, LAMB('n', 'z')))
    ez = w.s([w.s([val], 'fveq2d', '( %s -> ( exp ` ( %s ` z ) ) = ( exp ` %s ) )' % (A2, LN, LAMB('n', 'z'))), ex], 'eqtrd', '( %s -> ( exp ` ( %s ` z ) ) = ( F ` z ) )' % (A2, LN))
    ral = w.s([ez], 'ralrimiva', '( %s -> A. z e. E ( exp ` ( %s ` z ) ) = ( F ` z ) )' % (A1, LN))
    both = w.s([hh, ral], 'jca', '( %s -> ( %s /\\ A. z e. E ( exp ` ( %s ` z ) ) = ( F ` z ) ) )' % (A1, HOLE(LN), LN))
    eset = w.s([w.s([w.s([eop1, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A1, TOP)), w.inst('elex')], 'syl', '( %s -> E e. _V )' % A1), w.inst('mptexg')], 'syl',
               '( %s -> %s e. _V )' % (A1, LN))
    idg = w.s([], 'id', '( g = %s -> g = %s )' % (LN, LN))
    cg, new = w.wcongr('( %s /\\ %s )' % (HOLE('g'), EXPG), {'g': LN}, 'g = %s' % LN, {'g': idg})
    assert new == '( %s /\\ A. z e. E ( exp ` ( %s ` z ) ) = ( F ` z ) )' % (HOLE(LN), LN), new
    sp = w.s([eset, both, cg], 'spcedv', '( %s -> %s )' % (A1, CONC))
    e1 = w.s([w.s([sp], 'ex', '( ( %s /\\ n e. NN ) -> ( %s -> %s ) )' % (A0, SLITP('n'), CONC))], 'rexlimdva', '( %s -> ( E. n e. NN %s -> %s ) )' % (A0, SLITP('n'), CONC))
    w.qed([hn, e1], 'mpd', '( %s -> %s )' % (A0, CONC))
    return run8(w)


def gen_hollogdv():
    w = W('hollogdv', 'A holomorphic logarithm ` G ` of ` F ` has the logarithmic derivative of ` F ` as its derivative.')
    HG = HOLE('G')
    ALLV = 'A. v e. E ( exp ` ( G ` v ) ) = ( F ` v )'
    A0 = '( ( %s /\\ ( %s /\\ E C_ D ) ) /\\ %s )' % (HOL, HG, ALLV)
    h = w.s([], 'simpl', '( %s -> ( %s /\\ ( %s /\\ E C_ D ) ) )' % (A0, HOL, HG))
    allv = w.s([], 'simpr', '( %s -> %s )' % (A0, ALLV))
    hol = w.s([h, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    hged = w.s([h, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ E C_ D ) )' % (A0, HG))
    hg = w.s([hged, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HG))
    ed = w.s([hged, w.inst('simpr')], 'syl', '( %s -> E C_ D )' % A0)
    eto = w.s([hg, w.inst('holopn')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    gf = w.s([w.s([hg, w.inst('simpl')], 'syl', '( %s -> G e. ( E -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> G : E --> CC )' % A0)
    dgf = w.s([hg, w.inst('holf')], 'syl', '( %s -> ( CC _D G ) : E --> CC )' % A0)
    ff = w.s([w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    dff = w.s([hol, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % A0)
    cc = w.s([w.s([], 'cnelprrecn', CCPR)], 'a1i', '( %s -> %s )' % (A0, CCPR))
    dg = w.s([hg, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. E |-> ( G ` z ) ) ) = ( z e. E |-> ( ( CC _D G ) ` z ) ) )' % A0)
    # exp as a mapping
    EXM = '( y e. CC |-> ( exp ` y ) )'
    em = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC')], 'a1i', '( %s -> exp : CC --> CC )' % A0)], 'feqmptd', '( %s -> exp = %s )' % (A0, EXM))
    dex = w.s([w.s([w.s([em], 'oveq2d', '( %s -> ( CC _D exp ) = ( CC _D %s ) )' % (A0, EXM))], 'eqcomd', '( %s -> ( CC _D %s ) = ( CC _D exp ) )' % (A0, EXM)),
               w.s([w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'a1i', '( %s -> ( CC _D exp ) = exp )' % A0), em], 'eqtrd', '( %s -> ( CC _D exp ) = %s )' % (A0, EXM))],
              'eqtrd', '( %s -> ( CC _D %s ) = %s )' % (A0, EXM, EXM))
    A1 = '( %s /\\ z e. E )' % A0
    zin = w.s([], 'simpr', '( %s -> z e. E )' % A1)
    gz = w.s([w.s([gf], 'adantr', '( %s -> G : E --> CC )' % A1), zin], 'ffvelcdmd', '( %s -> ( G ` z ) e. CC )' % A1)
    dgz = w.s([w.s([dgf], 'adantr', '( %s -> ( CC _D G ) : E --> CC )' % A1), zin], 'ffvelcdmd', '( %s -> ( ( CC _D G ) ` z ) e. CC )' % A1)
    Ay = '( %s /\\ y e. CC )' % A0
    ey = w.s([w.s([], 'simpr', '( %s -> y e. CC )' % Ay)], 'efcld', '( %s -> ( exp ` y ) e. CC )' % Ay)
    f1 = w.s([], 'fveq2', '( y = ( G ` z ) -> ( exp ` y ) = ( exp ` ( G ` z ) ) )')
    M1 = '( z e. E |-> ( ( exp ` ( G ` z ) ) x. ( ( CC _D G ) ` z ) ) )'
    dco = w.s([cc, cc, gz, dgz, ey, ey, dg, dex, f1, f1], 'dvmptco', '( %s -> ( CC _D ( z e. E |-> ( exp ` ( G ` z ) ) ) ) = %s )' % (A0, M1))
    # exp o G = F on E
    idv = w.s([], 'id', '( v = z -> v = z )')
    cgv, _ = w.wcongr('( exp ` ( G ` v ) ) = ( F ` v )', {'v': 'z'}, 'v = z', {'v': idv})
    egz = w.s([cgv, w.s([allv], 'adantr', '( %s -> %s )' % (A1, ALLV)), zin], 'rspcdva', '( %s -> ( exp ` ( G ` z ) ) = ( F ` z ) )' % A1)
    meq = w.s([egz], 'mpteq2dva', '( %s -> ( z e. E |-> ( exp ` ( G ` z ) ) ) = ( z e. E |-> ( F ` z ) ) )' % A0)
    dF0 = w.s([hol, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. D |-> ( F ` z ) ) ) = ( z e. D |-> ( ( CC _D F ) ` z ) ) )' % A0)
    Az = '( %s /\\ z e. D )' % A0
    zd = w.s([], 'simpr', '( %s -> z e. D )' % Az)
    fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Az), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % Az)
    dfzc = w.s([w.s([dff], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % Az), zd], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` z ) e. CC )' % Az)
    jeq = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    M2 = '( z e. E |-> ( ( CC _D F ) ` z ) )'
    dF = w.s([cc, fzc, dfzc, dF0, ed, jeq, keq, eto], 'dvmptres', '( %s -> ( CC _D ( z e. E |-> ( F ` z ) ) ) = %s )' % (A0, M2))
    m12 = w.s([w.s([w.s([meq], 'oveq2d', '( %s -> ( CC _D ( z e. E |-> ( exp ` ( G ` z ) ) ) ) = ( CC _D ( z e. E |-> ( F ` z ) ) ) )' % A0), dco], 'eqtr3d',
                   '( %s -> ( CC _D ( z e. E |-> ( F ` z ) ) ) = %s )' % (A0, M1)), dF], 'eqtr3d', '( %s -> %s = %s )' % (A0, M1, M2))
    # pointwise
    pz = w.s([w.s([m12], 'adantr', '( %s -> %s = %s )' % (A1, M1, M2))], 'fveq1d', '( %s -> ( %s ` z ) = ( %s ` z ) )' % (A1, M1, M2))
    PROD = '( ( exp ` ( G ` z ) ) x. ( ( CC _D G ) ` z ) )'
    prc = w.s([w.s([gz], 'efcld', '( %s -> ( exp ` ( G ` z ) ) e. CC )' % A1), dgz], 'mulcld', '( %s -> %s e. CC )' % (A1, PROD))
    v1 = w.s([zin, prc, w.s([w.s([], 'eqid', '%s = %s' % (M1, M1))], 'fvmpt2', '( ( z e. E /\\ %s e. CC ) -> ( %s ` z ) = %s )' % (PROD, M1, PROD))], 'syl2anc',
             '( %s -> ( %s ` z ) = %s )' % (A1, M1, PROD))
    ze = w.s([w.s([ed], 'adantr', '( %s -> E C_ D )' % A1), zin], 'sseldd', '( %s -> z e. D )' % A1)
    dfz1 = w.s([w.s([dff], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % A1), ze], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` z ) e. CC )' % A1)
    v2 = w.s([zin, dfz1, w.s([w.s([], 'eqid', '%s = %s' % (M2, M2))], 'fvmpt2', '( ( z e. E /\\ ( ( CC _D F ) ` z ) e. CC ) -> ( %s ` z ) = ( ( CC _D F ) ` z ) )' % M2)],
             'syl2anc', '( %s -> ( %s ` z ) = ( ( CC _D F ) ` z ) )' % (A1, M2))
    p1 = w.s([w.s([v1, pz], 'eqtr3d', '( %s -> %s = ( %s ` z ) )' % (A1, PROD, M2)), v2], 'eqtrd', '( %s -> %s = ( ( CC _D F ) ` z ) )' % (A1, PROD))
    p2 = w.s([w.s([w.s([egz], 'oveq1d', '( %s -> %s = ( ( F ` z ) x. ( ( CC _D G ) ` z ) ) )' % (A1, PROD))], 'eqcomd',
                  '( %s -> ( ( F ` z ) x. ( ( CC _D G ) ` z ) ) = %s )' % (A1, PROD)), p1], 'eqtrd', '( %s -> ( ( F ` z ) x. ( ( CC _D G ) ` z ) ) = ( ( CC _D F ) ` z ) )' % A1)
    fzc1 = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), ze], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
    fz0 = w.s([w.s([w.s([gz], 'efne0d', '( %s -> ( exp ` ( G ` z ) ) =/= 0 )' % A1), egz], 'idi', 'X')], 'idi', 'X') if False else None
    fz0 = w.s([egz, w.s([gz], 'efne0d', '( %s -> ( exp ` ( G ` z ) ) =/= 0 )' % A1)], 'eqnetrrd', '( %s -> ( F ` z ) =/= 0 )' % A1)
    fin = w.s([p2, w.s([dfz1, fzc1, dgz, fz0], 'divmuld', '( %s -> ( ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( ( CC _D G ) ` z ) <-> ( ( F ` z ) x. ( ( CC _D G ) ` z ) ) = ( ( CC _D F ) ` z ) ) )' % A1)],
              'mpbird', '( %s -> ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( ( CC _D G ) ` z ) )' % A1)
    fin2 = w.s([fin], 'eqcomd', '( %s -> ( ( CC _D G ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) ) )' % A1)
    w.qed([fin2], 'ralrimiva', '( %s -> A. z e. E ( ( CC _D G ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) ) )' % A0)
    return run8(w)


def gen_hollog():
    w = W('hollog', 'The analytic logarithm on a rectangle: a function holomorphic on an open set containing a nested rectangle and zero-free on the rectangle has, on every open subset of the rectangle, a holomorphic logarithm whose derivative is its logarithmic derivative ( Lean ` exists_exp_eq_of_forall_ne_zero ` ).')
    A0 = '( %s /\\ ( %s /\\ %s ) )' % (ABGEO, NZ0, EOPN)
    ex = w.s([w.inst('hollogex')], 'idi', 'X') if False else None
    ex = w.s([], 'hollogex', '( %s -> E. g ( %s /\\ %s ) )' % (A0, HOLE('g'), EXPG))
    abgeo = w.s([], 'simpl', '( %s -> %s )' % (A0, ABGEO))
    d = abgeoctx(w, A0, abgeo)
    kd = w.s([d['hol'], d['ab'], d['nest'], w.inst('holnss')], 'syl3anc', '( %s -> ( A crect B ) C_ D )' % A0)
    ek = w.s([w.s([w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (A0, NZ0, EOPN)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, EOPN)), w.inst('simpr')], 'syl',
             '( %s -> E C_ ( A crect B ) )' % A0)
    ed = w.s([ek, kd], 'sstrd', '( %s -> E C_ D )' % A0)
    A1 = '( %s /\\ ( %s /\\ %s ) )' % (A0, HOLE('g'), EXPG)
    hg = w.s([], 'simprl', '( %s -> %s )' % (A1, HOLE('g')))
    eg = w.s([], 'simprr', '( %s -> %s )' % (A1, EXPG))
    ALLV = 'A. v e. E ( exp ` ( g ` v ) ) = ( F ` v )'
    cbz = w.s([w.s([w.s([w.s([], 'fveq2', '( z = v -> ( g ` z ) = ( g ` v ) )')], 'fveq2d', '( z = v -> ( exp ` ( g ` z ) ) = ( exp ` ( g ` v ) ) )'),
                    w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')], 'eqeq12d', '( z = v -> ( ( exp ` ( g ` z ) ) = ( F ` z ) <-> ( exp ` ( g ` v ) ) = ( F ` v ) ) )')],
              'cbvralvw', '( %s <-> %s )' % (EXPG, ALLV))
    ev = w.s([eg, cbz], 'sylib', '( %s -> %s )' % (A1, ALLV))
    DV = 'A. z e. E ( ( CC _D g ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) )'
    dv = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, A0)), d['hol']], 'syl', '( %s -> %s )' % (A1, HOL)),
                   w.s([hg, w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, A0)), ed], 'syl', '( %s -> E C_ D )' % A1)], 'jca', '( %s -> ( %s /\\ E C_ D ) )' % (A1, HOLE('g')))], 'jca',
                  '( %s -> ( %s /\\ ( %s /\\ E C_ D ) ) )' % (A1, HOL, HOLE('g'))), ev, w.inst('hollogdv')], 'syl2anc', '( %s -> %s )' % (A1, DV))
    BOTH = 'A. z e. E ( ( ( CC _D g ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) ) /\\ ( exp ` ( g ` z ) ) = ( F ` z ) )'
    r26 = w.s([w.s([dv, eg], 'jca', '( %s -> ( %s /\\ %s ) )' % (A1, DV, EXPG)), w.s([], 'r19.26', '( %s <-> ( %s /\\ %s ) )' % (BOTH, DV, EXPG))], 'sylibr', '( %s -> %s )' % (A1, BOTH))
    fin = w.s([hg, r26], 'jca', '( %s -> ( %s /\\ %s ) )' % (A1, HOLE('g'), BOTH))
    exi = w.s([w.s([fin], 'ex', '( %s -> ( ( %s /\\ %s ) -> ( %s /\\ %s ) ) )' % (A0, HOLE('g'), EXPG, HOLE('g'), BOTH))], 'eximdv',
              '( %s -> ( E. g ( %s /\\ %s ) -> E. g ( %s /\\ %s ) ) )' % (A0, HOLE('g'), EXPG, HOLE('g'), BOTH))
    w.qed([ex, exi], 'mpd', '( %s -> E. g ( %s /\\ %s ) )' % (A0, HOLE('g'), BOTH))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_hollogex, gen_hollogdv, gen_hollog]:
        g()
