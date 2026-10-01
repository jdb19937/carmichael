"""ZL1 section C: the L-function interface (zl1hcomb, dchrlfval, zl1ehol, zl1e1, zl1dser, zl1lif, zl1dlbz)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl1lib import *
from zl1lib import mptval_ as mptval
from cl import Closure

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    return w.run()


# ---------------------------------------------------------------- zl1hcomb
TM = '( ( C x. ( z + ( F ` z ) ) ) + ( ( z - 1 ) x. ( G ` z ) ) )'
if not only or 'zl1hcomb' in only:
    w = W('zl1hcomb', 'Holomorphy of the combination ` C ( z + F ( z ) ) + ( z - 1 ) G ( z ) ` of two holomorphic '
          'functions on an open set ( ~ holdv , ~ dvmptadd , ~ dvmptmul , ~ dvcn ).')
    A0 = STATEMENTS['zl1hcomb'][2:].split(' -> ( ( z e. D')[0]
    fh = w.s([], 'simp1', '( %s -> %s )' % (A0, HOL('F', 'D')))
    gh = w.s([], 'simp2', '( %s -> %s )' % (A0, HOL('G', 'D')))
    cc = w.s([], 'simp3', '( %s -> C e. CC )' % A0)
    dop = w.s([fh, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ton = w.s([w.s([ek], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (A0, TOP))
    dcc = w.s([ton, dop, w.inst('toponss')], 'syl2anc', '( %s -> D C_ CC )' % A0)
    sc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    Az = '( %s /\\ z e. D )' % A0
    zd = w.s([], 'simpr', '( %s -> z e. D )' % Az)
    zc = w.s([w.s([dcc], 'adantr', '( %s -> D C_ CC )' % Az), zd], 'sseldd', '( %s -> z e. CC )' % Az)
    def fv(Fn, h):
        ff = w.s([w.s([h], 'simpld', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, Fn)), w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (A0, Fn))
        fz = w.s([w.s([ff], 'adantr', '( %s -> %s : D --> CC )' % (Az, Fn)), zd], 'ffvelcdmd', '( %s -> ( %s ` z ) e. CC )' % (Az, Fn))
        ss = w.s([h], 'simprd', '( %s -> D C_ dom ( CC _D %s ) )' % (A0, Fn))
        zdom = w.s([w.s([ss], 'adantr', '( %s -> D C_ dom ( CC _D %s ) )' % (Az, Fn)), zd], 'sseldd', '( %s -> z e. dom ( CC _D %s ) )' % (Az, Fn))
        dfz = w.s([w.s([w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (Fn, Fn))], 'a1i', '( %s -> ( CC _D %s ) : dom ( CC _D %s ) --> CC )' % (Az, Fn, Fn)), zdom], 'ffvelcdmd',
                '( %s -> ( ( CC _D %s ) ` z ) e. CC )' % (Az, Fn))
        dv = w.s([h, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. D |-> ( %s ` z ) ) ) = ( z e. D |-> ( ( CC _D %s ) ` z ) ) )' % (A0, Fn, Fn))
        return fz, dfz, dv
    fz, dfz, dF = fv('F', fh)
    gz, dgz, dG = fv('G', gh)
    rest = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    Ac = '( %s /\\ z e. CC )' % A0
    zcc = w.s([], 'simpr', '( %s -> z e. CC )' % Ac)
    c1 = a1(w, Ac, 'ax-1cn', '1 e. CC'); c0 = a1(w, Ac, '0cn', '0 e. CC')
    di = w.s([sc], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)
    dI = w.s([sc, zcc, c1, di, dcc, rest, ek, dop], 'dvmptres', '( %s -> ( CC _D ( z e. D |-> z ) ) = ( z e. D |-> 1 ) )' % A0)
    d1 = w.s([sc, zcc, c1, di, c1, c0, w.s([sc], 'dvmptc', '( %s -> ( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 ) )' % A0)], 'dvmptsub',
             '( %s -> ( CC _D ( z e. CC |-> ( z - 1 ) ) ) = ( z e. CC |-> ( 1 - 0 ) ) )' % A0)
    dZ1 = w.s([sc, w.s([zcc, c1], 'subcld', '( %s -> ( z - 1 ) e. CC )' % Ac), w.s([c1, c0], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % Ac), d1, dcc, rest, ek, dop], 'dvmptres',
              '( %s -> ( CC _D ( z e. D |-> ( z - 1 ) ) ) = ( z e. D |-> ( 1 - 0 ) ) )' % A0)
    a1z = a1(w, Az, 'ax-1cn', '1 e. CC'); a0z = a1(w, Az, '0cn', '0 e. CC')
    DF = '( ( CC _D F ) ` z )'; DG = '( ( CC _D G ) ` z )'
    dS = w.s([sc, zc, a1z, dI, fz, dfz, dF], 'dvmptadd', '( %s -> ( CC _D ( z e. D |-> ( z + ( F ` z ) ) ) ) = ( z e. D |-> ( 1 + %s ) ) )' % (A0, DF))
    szc = w.s([zc, fz], 'addcld', '( %s -> ( z + ( F ` z ) ) e. CC )' % Az)
    s1c = w.s([a1z, dfz], 'addcld', '( %s -> ( 1 + %s ) e. CC )' % (Az, DF))
    dC = w.s([sc, szc, s1c, dS, cc], 'dvmptcmul', '( %s -> ( CC _D ( z e. D |-> ( C x. ( z + ( F ` z ) ) ) ) ) = ( z e. D |-> ( C x. ( 1 + %s ) ) ) )' % (A0, DF))
    z1c = w.s([zc, a1z], 'subcld', '( %s -> ( z - 1 ) e. CC )' % Az)
    o0c = w.s([a1z, a0z], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % Az)
    DM = '( ( ( 1 - 0 ) x. ( G ` z ) ) + ( %s x. ( z - 1 ) ) )' % DG
    dM = w.s([sc, z1c, o0c, dZ1, gz, dgz, dG], 'dvmptmul', '( %s -> ( CC _D ( z e. D |-> ( ( z - 1 ) x. ( G ` z ) ) ) ) = ( z e. D |-> %s ) )' % (A0, DM))
    ccz = w.s([cc], 'adantr', '( %s -> C e. CC )' % Az)
    DT = '( ( C x. ( 1 + %s ) ) + %s )' % (DF, DM)
    dT = w.s([sc, w.s([ccz, szc], 'mulcld', '( %s -> ( C x. ( z + ( F ` z ) ) ) e. CC )' % Az), w.s([ccz, s1c], 'mulcld', '( %s -> ( C x. ( 1 + %s ) ) e. CC )' % (Az, DF)), dC,
              w.s([z1c, gz], 'mulcld', '( %s -> ( ( z - 1 ) x. ( G ` z ) ) e. CC )' % Az),
              w.s([w.s([o0c, gz], 'mulcld', '( %s -> ( ( 1 - 0 ) x. ( G ` z ) ) e. CC )' % Az), w.s([dgz, z1c], 'mulcld', '( %s -> ( %s x. ( z - 1 ) ) e. CC )' % (Az, DG))], 'addcld',
                  '( %s -> %s e. CC )' % (Az, DM)), dM], 'dvmptadd', '( %s -> ( CC _D ( z e. D |-> %s ) ) = ( z e. D |-> %s ) )' % (A0, TM, DT))
    tmc = w.s([w.s([ccz, szc], 'mulcld', '( %s -> ( C x. ( z + ( F ` z ) ) ) e. CC )' % Az), w.s([z1c, gz], 'mulcld', '( %s -> ( ( z - 1 ) x. ( G ` z ) ) e. CC )' % Az)], 'addcld',
              '( %s -> %s e. CC )' % (Az, TM))
    dtc = w.s([w.s([ccz, s1c], 'mulcld', '( %s -> ( C x. ( 1 + %s ) ) e. CC )' % (Az, DF)),
               w.s([w.s([o0c, gz], 'mulcld', '( %s -> ( ( 1 - 0 ) x. ( G ` z ) ) e. CC )' % Az), w.s([dgz, z1c], 'mulcld', '( %s -> ( %s x. ( z - 1 ) ) e. CC )' % (Az, DG))], 'addcld',
                   '( %s -> %s e. CC )' % (Az, DM))], 'addcld', '( %s -> %s e. CC )' % (Az, DT))
    TMM = '( z e. D |-> %s )' % TM; DTM = '( z e. D |-> %s )' % DT
    tf = w.s([tmc, w.s([], 'eqid', '%s = %s' % (TMM, TMM))], 'fmptd', '( %s -> %s : D --> CC )' % (A0, TMM))
    dtf = w.s([dtc, w.s([], 'eqid', '%s = %s' % (DTM, DTM))], 'fmptd', '( %s -> %s : D --> CC )' % (A0, DTM))
    dm = w.s([w.s([dT], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, TMM, DTM)), w.s([dtf, w.inst('fdm')], 'syl', '( %s -> dom %s = D )' % (A0, DTM))], 'eqtrd',
             '( %s -> dom ( CC _D %s ) = D )' % (A0, TMM))
    cn = w.s([w.s([w.s([a1(w, A0, 'ssid', 'CC C_ CC'), tf, dcc], '3jca', '( %s -> ( CC C_ CC /\\ %s : D --> CC /\\ D C_ CC ) )' % (A0, TMM)), dm], 'jca',
                  '( %s -> ( ( CC C_ CC /\\ %s : D --> CC /\\ D C_ CC ) /\\ dom ( CC _D %s ) = D ) )' % (A0, TMM, TMM)), w.inst('dvcn')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, TMM))
    w.qed([cn, w.s([w.s([dm], 'eqcomd', '( %s -> D = dom ( CC _D %s ) )' % (A0, TMM))], 'eqimssd', '( %s -> D C_ dom ( CC _D %s ) )' % (A0, TMM))], 'jca', '( %s -> %s )' % (A0, HOL(TMM, 'D')))
    go(w)

BODY = sub_(LFM, {'N': 'n', 'X': 'x'})
DF = 'DChrLF = ( n e. NN , x e. _V |-> %s )' % BODY
if not only or 'dchrlfval' in only:
    w = W('dchrlfval', 'The value of ~ df-dchrlf : ` ( N DChrLF X ) ` as a mapping on the open right half-plane.')
    A0 = NX
    i1 = w.s([], 'id', '( n = N -> n = N )')
    h1, G1 = w.congr(BODY, {'n': 'N'}, 'n = N', {'n': i1})
    i2 = w.s([], 'id', '( x = X -> x = X )')
    h2, S2 = w.congr(G1, {'x': 'X'}, 'x = X', {'x': i2})
    assert S2 == LFM, (S2, LFM)
    df = w.s([], 'df-dchrlf', DF)
    ov = w.s([h1, h2, df], 'ovmpog', '( ( N e. NN /\\ X e. _V /\\ %s e. _V ) -> %s = %s )' % (LFM, LF, LFM))
    nn = w.s([], 'simpl', '( %s -> N e. NN )' % A0)
    xv = w.s([w.s([], 'simpr', '( %s -> X e. %s )' % (A0, DC))], 'elexd', '( %s -> X e. _V )' % A0)
    hpv = w.s([w.s([], 'cnex', 'CC e. _V'), w.s([], 'hpss', '%s C_ CC' % HPZ)], 'ssexi', '%s e. _V' % HPZ)
    mx = w.s([w.s([hpv], 'mptex', '%s e. _V' % LFM)], 'a1i', '( %s -> %s e. _V )' % (A0, LFM))
    w.qed([nn, xv, mx, ov], 'syl3anc', '( %s -> %s = %s )' % (A0, LF, LFM))
    go(w)

ZFM = '( z e. %s |-> %s )' % (HPZ, HS('z'))
ABM = ABF()
EVS = '( ( %s x. ( s + ( %s ` s ) ) ) + ( ( s - 1 ) x. ( %s ` s ) ) )' % (QM, ZFM, ABM)


def qmcl(w, ante, nn):
    pc = w.s([w.s([w.s([nn, w.inst('phicl')], 'syl', '( %s -> ( phi ` N ) e. NN )' % ante)], 'nncnd', '( %s -> ( phi ` N ) e. CC )' % ante),
              w.s([nn], 'nncnd', '( %s -> N e. CC )' % ante), w.s([nn], 'nnne0d', '( %s -> N =/= 0 )' % ante)], 'divcld', '( %s -> ( ( phi ` N ) / N ) e. CC )' % ante)
    return w.s([pc, a1(w, ante, '0cn', '0 e. CC')], 'ifcld', '( %s -> %s e. CC )' % (ante, QM))


def hpmem(w, ante, S, sc, s0):
    """( ante -> S e. HPZ ) from sc: S e. CC, s0: 0 < Re S"""
    return w.s([w.s([sc, s0], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (ante, S, S)),
                w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (S, HPZ, S, S))], 'sylibr', '( %s -> %s e. %s )' % (ante, S, HPZ))


def hpel(w, ante, S, sh):
    """( ante -> ( S e. CC /\\ 0 < ( Re ` S ) ) ) from sh: S e. HPZ"""
    return w.s([sh, w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (S, HPZ, S, S))], 'sylib',
               '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (ante, S, S))


if not only or 'zl1ehol' in only:
    w = W('zl1ehol', 'The function ` ( N DChrLF X ) = ( s - 1 ) L ( s , X ) ` is holomorphic on the open right half-plane: '
          'the interface item ` EHOL ` of ~ z6dlbz (Lean ` differentiableAt_LFunction ` , ` LFunctionTrivChar_1 ` ; '
          '~ zl1zhol , ~ zl1ahol , ~ zl1hcomb ).')
    A0 = NX
    zh = a1(w, A0, 'zl1zhol', HOL(ZFM, HPZ))
    ah = w.s([], 'zl1ahol', '( %s -> %s )' % (A0, HOL(ABM, HPZ)))
    nn = w.s([], 'simpl', '( %s -> N e. NN )' % A0)
    qc = qmcl(w, A0, nn)
    EM = '( s e. %s |-> %s )' % (HPZ, EVS)
    hc = w.s([zh, ah, qc, w.inst('zl1hcomb')], 'syl3anc', '( %s -> %s )' % (A0, HOL(EM, HPZ)))
    As = '( %s /\\ s e. %s )' % (A0, HPZ)
    sh = w.s([], 'simpr', '( %s -> s e. %s )' % (As, HPZ))
    se = hpel(w, As, 's', sh)
    zv, _ = mptval(w, As, 'z', HPZ, HS('z'), 's', sh, mp=ZFM, exs=vexd(w, As, HS('s'), 'sum'))
    av, _ = mptval(w, As, 'z', HPZ, AB('z'), 's', sh, mp=ABM, exs=vexd(w, As, AB('s'), 'sum'))
    e1 = E(w, As, 'oveq12d', [E(w, As, 'oveq2d', [E(w, As, 'oveq2d', [zv], '( s + ( %s ` s ) )' % ZFM, ZF('s'))], '( %s x. ( s + ( %s ` s ) ) )' % (QM, ZFM), '( %s x. %s )' % (QM, ZF('s'))),
                                     E(w, As, 'oveq2d', [av], '( ( s - 1 ) x. ( %s ` s ) )' % ABM, '( ( s - 1 ) x. %s )' % AB('s'))], EVS, EV('s'))
    me = w.s([e1], 'mpteq2dva', '( %s -> %s = %s )' % (A0, EM, LFM))
    lv = w.s([w.s([], 'dchrlfval', '( %s -> %s = %s )' % (A0, LF, LFM)), me], 'eqtr4d', '( %s -> %s = %s )' % (A0, LF, EM))
    b1 = w.s([lv], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A0, LF, HPZ, EM, HPZ))
    b2 = w.s([w.s([w.s([lv], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, LF, EM))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, LF, EM))],
             'sseq2d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A0, HPZ, LF, HPZ, EM))
    w.qed([hc, w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A0, HOL(LF, HPZ), HOL(EM, HPZ)))], 'mpbird', '( %s -> %s )' % (A0, HOL(LF, HPZ)))
    go(w)


def lfval(w, ante, S, nx, sh):
    """( ante -> ( LF ` S ) = EV ( S ) ) from sh: S e. HPZ"""
    lv = w.s([nx, w.inst('dchrlfval')], 'syl', '( %s -> %s = %s )' % (ante, LF, LFM))
    if S == 's':
        # the argument is the mapping's binder: fvmpt2d under ( NX /\ s e. HPZ )
        B0 = '( %s /\\ s e. %s )' % (NX, HPZ)
        nx0 = w.s([], 'simpl', '( %s -> %s )' % (B0, NX))
        s0 = w.s([], 'simpr', '( %s -> s e. %s )' % (B0, HPZ))
        se = hpel(w, B0, 's', s0)
        nn0 = w.s([nx0, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % B0)
        zc = w.s([se, w.inst('zl1zcl')], 'syl', '( %s -> %s e. CC )' % (B0, HS('s')))
        ac = w.s([w.s([nx0, se], 'jca', '( %s -> ( %s /\\ ( s e. CC /\\ 0 < ( Re ` s ) ) ) )' % (B0, NX)), w.inst('zl1acl')], 'syl', '( %s -> %s e. CC )' % (B0, AB('s')))
        scc = w.s([se, w.inst('simpl')], 'syl', '( %s -> s e. CC )' % B0)
        evc = w.s([w.s([qmcl(w, B0, nn0), w.s([scc, zc], 'addcld', '( %s -> %s e. CC )' % (B0, ZF('s')))], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (B0, QM, ZF('s'))),
                   w.s([w.s([scc, a1(w, B0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( s - 1 ) e. CC )' % B0), ac], 'mulcld', '( %s -> ( ( s - 1 ) x. %s ) e. CC )' % (B0, AB('s')))],
                  'addcld', '( %s -> %s e. CC )' % (B0, EV('s')))
        v0 = selfv(w, NX, 's', HPZ, EV('s'), LFM, evc)
        v = w.s([w.s([w.s([nx, sh], 'jca', '( %s -> %s )' % (ante, B0)), v0], 'syl', '( %s -> ( %s ` s ) = %s )' % (ante, LFM, EV('s')))], 'idi', '( %s -> ( %s ` s ) = %s )' % (ante, LFM, EV('s')))
    else:
        v, _ = mptval(w, ante, 's', HPZ, EV('s'), S, sh, mp=LFM, exs=w.s([], 'ovexd', '( %s -> %s e. _V )' % (ante, EV(S))))
    return w.s([w.s([lv], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ante, LF, S, LFM, S)), v], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ante, LF, S, EV(S)))


if not only or 'zl1e1' in only:
    w = W('zl1e1', 'The value of ` ( N DChrLF X ) ` at ` 1 ` is the residue ` RESV ` : ` phi ( N ) / N ` for the principal '
          'character, ` 0 ` otherwise (Lean ` LFunctionTrivChar_1 ` at ` 1 ` and ` prod_one_sub_inv_eq_totient_div ` ; '
          '~ zl1z1 , ~ zl1prn ).')
    A0 = NX
    nx = w.s([], 'id', '( %s -> %s )' % (A0, NX))
    nn = w.s([], 'simpl', '( %s -> N e. NN )' % A0)
    c1 = a1(w, A0, 'ax-1cn', '1 e. CC')
    r1 = w.s([w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A0)], 'idi', '( %s -> ( Re ` 1 ) = 1 )' % A0)
    p1 = w.s([a1(w, A0, '0lt1', '0 < 1'), r1], 'breqtrrd', '( %s -> 0 < ( Re ` 1 ) )' % A0)
    oh = hpmem(w, A0, '1', c1, p1)
    v = lfval(w, A0, '1', nx, oh)
    qc = qmcl(w, A0, nn)
    ac = w.s([w.s([nx, w.s([c1, p1], 'jca', '( %s -> ( 1 e. CC /\\ 0 < ( Re ` 1 ) ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( 1 e. CC /\\ 0 < ( Re ` 1 ) ) ) )' % (A0, NX)),
              w.inst('zl1acl')], 'syl', '( %s -> %s e. CC )' % (A0, AB('1')))
    z1 = w.s([w.s([], 'zl1z1', '%s = 0' % HS('1'))], 'a1i', '( %s -> %s = 0 )' % (A0, HS('1')))
    t1 = chain(w, A0, [ZF('1'), '( 1 + 0 )', '1'], [E(w, A0, 'oveq2d', [z1], ZF('1'), '( 1 + 0 )'), E(w, A0, 'addridd', [c1], '( 1 + 0 )', '1')])
    t2 = chain(w, A0, ['( %s x. %s )' % (QM, ZF('1')), '( %s x. 1 )' % QM, QM], [E(w, A0, 'oveq2d', [t1], '( %s x. %s )' % (QM, ZF('1')), '( %s x. 1 )' % QM),
                                                                             E(w, A0, 'mulridd', [qc], '( %s x. 1 )' % QM, QM)])
    t3 = chain(w, A0, ['( ( 1 - 1 ) x. %s )' % AB('1'), '( 0 x. %s )' % AB('1'), '0'],
               [E(w, A0, 'oveq1d', [E(w, A0, 'subidd', [c1], '( 1 - 1 )', '0')], '( ( 1 - 1 ) x. %s )' % AB('1'), '( 0 x. %s )' % AB('1')),
                E(w, A0, 'mul02d', [ac], '( 0 x. %s )' % AB('1'), '0')])
    t4 = chain(w, A0, [EV('1'), '( %s + 0 )' % QM, QM], [E(w, A0, 'oveq12d', [t2, t3], EV('1'), '( %s + 0 )' % QM), E(w, A0, 'addridd', [qc], '( %s + 0 )' % QM, QM)])
    pr = w.s([], 'zl1prn', '( %s -> ( %s = %s <-> X = %s ) )' % (A0, CX, PRN, ONE))
    ib = w.s([w.s([pr], 'bicomd', '( %s -> ( X = %s <-> %s = %s ) )' % (A0, ONE, CX, PRN))], 'ifbid', '( %s -> %s = %s )' % (A0, QM, RESVX))
    chain(w, A0, ['( %s ` 1 )' % LF, EV('1'), QM, RESVX], [v, t4, ib], name='qed')
    go(w)

LSX = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u s ) )' % CX
if not only or 'zl1dser' in only:
    w = W('zl1dser', 'On ` 1 < Re s ` the function ` ( N DChrLF X ) ` is ` ( s - 1 ) ` times the L-series of the character: '
          'the interface item ` DSER ` of ~ z6dlbz (Lean ` LFunction_eq_LSeries ` ; ~ zl1zser , ~ zl1aagr ).')
    A0 = NX
    nx = w.s([], 'id', '( %s -> %s )' % (A0, NX))
    As = '( ( %s /\\ s e. %s ) /\\ 1 < ( Re ` s ) )' % (A0, HPZ)
    nxs = w.s([], 'simpll', '( %s -> %s )' % (As, NX))
    sh = w.s([], 'simplr', '( %s -> s e. %s )' % (As, HPZ))
    s1 = w.s([], 'simpr', '( %s -> 1 < ( Re ` s ) )' % As)
    sc = w.s([hpel(w, As, 's', sh)], 'simpld', '( %s -> s e. CC )' % As)
    nn = w.s([nxs, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % As)
    sp = w.s([sc, s1], 'jca', '( %s -> ( s e. CC /\\ 1 < ( Re ` s ) ) )' % As)
    v = lfval(w, As, 's', nxs, sh)
    zs = w.s([sp, w.inst('zl1zser')], 'syl', '( %s -> %s = ( ( s - 1 ) x. sum_ k e. NN ( k ^c -u s ) ) )' % (As, ZF('s')))
    CHWs = lambda k: CHW(k)
    ag = w.s([w.s([nxs, sp], 'jca', '( %s -> ( %s /\\ ( s e. CC /\\ 1 < ( Re ` s ) ) ) )' % (As, NX)), w.inst('zl1aagr')], 'syl',
             '( %s -> %s = sum_ k e. NN ( %s x. ( k ^c -u s ) ) )' % (As, AB('s'), CHW('k')))
    ZS = 'sum_ k e. NN ( k ^c -u s )'
    WS = 'sum_ k e. NN ( %s x. ( k ^c -u s ) )' % CHW('k')
    VS = 'sum_ k e. NN ( %s x. ( k ^c -u s ) )' % CHV('k')
    qc = qmcl(w, As, nn)
    # VS = WS + QM ZS
    Ak = '( %s /\\ k e. NN )' % As
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([nxs], 'adantr', '( %s -> %s )' % (Ak, NX))
    ck = Closure(w, Ak, {'k': ('NN', kn), 's': ('CC', w.s([sc], 'adantr', '( %s -> s e. CC )' % Ak))})
    cv = w.s([w.s([nxk, kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX)), w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (Ak, CHV('k')))
    qk = w.s([qc], 'adantr', '( %s -> %s e. CC )' % (Ak, QM))
    kt = ck.mem('( k ^c -u s )', 'CC')
    tk = chain(w, Ak, ['( %s x. ( k ^c -u s ) )' % CHV('k'), '( ( %s + %s ) x. ( k ^c -u s ) )' % (CHW('k'), QM),
                       '( ( %s x. ( k ^c -u s ) ) + ( %s x. ( k ^c -u s ) ) )' % (CHW('k'), QM)],
               [('r', E(w, Ak, 'oveq1d', [E(w, Ak, 'npcand', [cv, qk], '( %s + %s )' % (CHW('k'), QM), CHV('k'))], '( ( %s + %s ) x. ( k ^c -u s ) )' % (CHW('k'), QM),
                        '( %s x. ( k ^c -u s ) )' % CHV('k'))),
                E(w, Ak, 'adddird', [w.s([cv, qk], 'subcld', '( %s -> %s e. CC )' % (Ak, CHW('k'))), qk, kt], '( ( %s + %s ) x. ( k ^c -u s ) )' % (CHW('k'), QM),
                  '( ( %s x. ( k ^c -u s ) ) + ( %s x. ( k ^c -u s ) ) )' % (CHW('k'), QM))])
    sumsp = w.s([tk], 'sumeq2dv', '( %s -> %s = sum_ k e. NN ( ( %s x. ( k ^c -u s ) ) + ( %s x. ( k ^c -u s ) ) ) )' % (As, VS, CHW('k'), QM))
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    z1 = a1(w, As, '1z', '1 e. ZZ')
    MW = '( n e. NN |-> ( %s x. ( n ^c -u s ) ) )' % CHW('n')
    MQ = '( n e. NN |-> ( %s x. ( n ^c -u s ) ) )' % QM
    wv, _ = mptval(w, Ak, 'n', 'NN', '( %s x. ( n ^c -u s ) )' % CHW('n'), 'k', kn, mp=MW)
    qv, _ = mptval(w, Ak, 'n', 'NN', '( %s x. ( n ^c -u s ) )' % QM, 'k', kn, mp=MQ)
    # convergence: W series by dsercvg (bounded coefficients), Q series by zsercvgz and isermulc2
    AW = '( q e. NN |-> %s )' % CHW('q')
    CB1 = '( 1 + ( abs ` %s ) )' % QM
    Am = '( %s /\\ m e. NN )' % As
    mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
    nxm = w.s([nxs], 'adantr', '( %s -> %s )' % (Am, NX)); nnm = w.s([nn], 'adantr', '( %s -> N e. NN )' % Am)
    awm, _ = mptval(w, Am, 'q', 'NN', CHW('q'), 'm', mn, mp=AW)
    qcm = qmcl(w, Am, nnm)
    cvm = w.s([w.s([nxm, mn], 'jca', '( %s -> ( %s /\\ m e. NN ) )' % (Am, NX)), w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (Am, CHV('m')))
    t1 = w.s([cvm, qcm, w.inst('abs2dif2')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (Am, CHW('m'), CHV('m'), QM))
    t2 = w.s([w.s([cvm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, CHV('m'))), a1(w, Am, '1re', '1 e. RR'), w.s([qcm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, QM)),
              w.s([w.s([nxm, mn], 'jca', '( %s -> ( %s /\\ m e. NN ) )' % (Am, NX)), w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (Am, CHV('m')))], 'leadd1dd',
             '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ %s )' % (Am, CHV('m'), QM, CB1))
    cbrm = w.s([a1(w, Am, '1re', '1 e. RR'), w.s([qcm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, QM))], 'readdcld', '( %s -> %s e. RR )' % (Am, CB1))
    cwm = w.s([cvm, qcm], 'subcld', '( %s -> %s e. CC )' % (Am, CHW('m')))
    t3 = w.s([w.s([cwm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, CHW('m'))), w.s([w.s([cvm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, CHV('m'))),
                                                                                           w.s([qcm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, QM))], 'readdcld',
                                                                                          '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (Am, CHV('m'), QM)), cbrm, t1, t2],
             'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (Am, CHW('m'), CB1))
    awb = w.s([w.s([awm], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (Am, AW, CHW('m'))), t3], 'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ %s )' % (Am, AW, CB1))
    Aq = '( %s /\\ q e. NN )' % As
    qn = w.s([], 'simpr', '( %s -> q e. NN )' % Aq)
    fq = w.s([w.s([w.s([w.s([nxs], 'adantr', '( %s -> %s )' % (Aq, NX)), qn], 'jca', '( %s -> ( %s /\\ q e. NN ) )' % (Aq, NX)), w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (Aq, CHV('q'))),
              qmcl(w, Aq, w.s([nn], 'adantr', '( %s -> N e. NN )' % Aq))], 'subcld', '( %s -> %s e. CC )' % (Aq, CHW('q')))
    af = w.s([fq, w.s([], 'eqid', '%s = %s' % (AW, AW))], 'fmptd', '( %s -> %s : NN --> CC )' % (As, AW))
    cbr = w.s([a1(w, As, '1re', '1 e. RR'), w.s([qc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (As, QM))], 'readdcld', '( %s -> %s e. RR )' % (As, CB1))
    CFBW = '( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (AW, CB1, AW, CB1)
    cfb = w.s([af, cbr, w.s([awb], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (As, AW, CB1))], '3jca', '( %s -> %s )' % (As, CFBW))
    MWA = '( n e. NN |-> ( ( %s ` n ) x. ( n ^c -u s ) ) )' % AW
    dcv = w.s([w.s([cfb, sp], 'jca', '( %s -> ( %s /\\ ( s e. CC /\\ 1 < ( Re ` s ) ) ) )' % (As, CFBW)), w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (As, MWA))
    Ank = '( %s /\\ n e. NN )' % As
    nnk = w.s([], 'simpr', '( %s -> n e. NN )' % Ank)
    awn, _ = mptval(w, Ank, 'q', 'NN', CHW('q'), 'n', nnk, mp=AW)
    meq = w.s([w.s([awn], 'oveq1d', '( %s -> ( ( %s ` n ) x. ( n ^c -u s ) ) = ( %s x. ( n ^c -u s ) ) )' % (Ank, AW, CHW('n')))], 'mpteq2dva', '( %s -> %s = %s )' % (As, MWA, MW))
    wcv = w.s([dcv, w.s([w.s([meq], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (As, MWA, MW))], 'eleq1d',
                        '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (As, MWA, MW))], 'mpbid', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (As, MW))
    ZT = '( n e. NN |-> ( n ^c -u s ) )'
    qcv = w.s([w.s([sc, s1], 'jca', '( %s -> ( s e. CC /\\ 1 < ( Re ` s ) ) )' % As), w.inst('zsercvgz')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (As, ZT))
    zkv, _ = mptval(w, Ak, 'n', 'NN', '( n ^c -u s )', 'k', kn, mp=ZT)
    iq = w.s([nu, z1, zkv, kt, qcv, qc], 'isummulc2', '( %s -> ( %s x. %s ) = sum_ k e. NN ( %s x. ( k ^c -u s ) ) )' % (As, QM, ZS, QM))
    # the constant series converges (dsercvg at the constant coefficient QM)
    AQ = '( q e. NN |-> %s )' % QM
    aqf = w.s([w.s([qmcl(w, Aq, w.s([nn], 'adantr', '( %s -> N e. NN )' % Aq)), w.s([], 'eqid', '%s = %s' % (AQ, AQ))], 'fmptd', '( %s -> %s : NN --> CC )' % (As, AQ))], 'idi',
              '( %s -> %s : NN --> CC )' % (As, AQ))
    aqm, _ = mptval(w, Am, 'q', 'NN', QM, 'm', mn, mp=AQ, exs=w.s([w.s([qcm], 'elexd', '( %s -> %s e. _V )' % (Am, QM))], 'idi', '( %s -> %s e. _V )' % (Am, QM)))
    aqb = w.s([w.s([aqm], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (Am, AQ, QM)), w.s([w.s([qcm], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Am, QM))], 'leidd',
                                                                                                  '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (Am, QM, QM))], 'eqbrtrd',
              '( %s -> ( abs ` ( %s ` m ) ) <_ ( abs ` %s ) )' % (Am, AQ, QM))
    CFBQ = '( %s : NN --> CC /\\ ( abs ` %s ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( abs ` %s ) )' % (AQ, QM, AQ, QM)
    cfq = w.s([aqf, w.s([qc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (As, QM)), w.s([aqb], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ ( abs ` %s ) )' % (As, AQ, QM))],
              '3jca', '( %s -> %s )' % (As, CFBQ))
    MQA = '( n e. NN |-> ( ( %s ` n ) x. ( n ^c -u s ) ) )' % AQ
    dqv = w.s([w.s([cfq, sp], 'jca', '( %s -> ( %s /\\ ( s e. CC /\\ 1 < ( Re ` s ) ) ) )' % (As, CFBQ)), w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (As, MQA))
    aqn, _ = mptval(w, Ank, 'q', 'NN', QM, 'n', nnk, mp=AQ, exs=w.s([w.s([qmcl(w, Ank, w.s([nn], 'adantr', '( %s -> N e. NN )' % Ank))], 'elexd', '( %s -> %s e. _V )' % (Ank, QM))], 'idi',
                                                                  '( %s -> %s e. _V )' % (Ank, QM)))
    meq2 = w.s([w.s([aqn], 'oveq1d', '( %s -> ( ( %s ` n ) x. ( n ^c -u s ) ) = ( %s x. ( n ^c -u s ) ) )' % (Ank, AQ, QM))], 'mpteq2dva', '( %s -> %s = %s )' % (As, MQA, MQ))
    mqcv = w.s([dqv, w.s([w.s([meq2], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (As, MQA, MQ))], 'eleq1d',
                         '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (As, MQA, MQ))], 'mpbid', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (As, MQ))
    wkc = w.s([w.s([cv, qk], 'subcld', '( %s -> %s e. CC )' % (Ak, CHW('k'))), kt], 'mulcld', '( %s -> ( %s x. ( k ^c -u s ) ) e. CC )' % (Ak, CHW('k')))
    qkc = w.s([qk, kt], 'mulcld', '( %s -> ( %s x. ( k ^c -u s ) ) e. CC )' % (Ak, QM))
    ia = w.s([nu, z1, wv, wkc, qv, qkc, wcv, mqcv], 'isumadd',
             '( %s -> sum_ k e. NN ( ( %s x. ( k ^c -u s ) ) + ( %s x. ( k ^c -u s ) ) ) = ( %s + sum_ k e. NN ( %s x. ( k ^c -u s ) ) ) )' % (As, CHW('k'), QM, WS, QM))
    vs = chain(w, As, [VS, 'sum_ k e. NN ( ( %s x. ( k ^c -u s ) ) + ( %s x. ( k ^c -u s ) ) )' % (CHW('k'), QM), '( %s + sum_ k e. NN ( %s x. ( k ^c -u s ) ) )' % (WS, QM),
                       '( %s + ( %s x. %s ) )' % (WS, QM, ZS)],
               [sumsp, ia, ('r', E(w, As, 'oveq2d', [iq], '( %s + ( %s x. %s ) )' % (WS, QM, ZS), '( %s + sum_ k e. NN ( %s x. ( k ^c -u s ) ) )' % (WS, QM)))])
    # EV ( s ) = ( s - 1 ) VS
    zsc = w.s([nu, z1, zkv, kt, qcv], 'isumcl', '( %s -> %s e. CC )' % (As, ZS))
    wsc = w.s([nu, z1, wv, wkc, wcv], 'isumcl', '( %s -> %s e. CC )' % (As, WS))
    s1c = w.s([sc, a1(w, As, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( s - 1 ) e. CC )' % As)
    QZ = '( %s x. %s )' % (QM, ZS)
    ev = chain(w, As, [EV('s'), '( ( %s x. ( ( s - 1 ) x. %s ) ) + ( ( s - 1 ) x. %s ) )' % (QM, ZS, WS), '( ( ( s - 1 ) x. %s ) + ( ( s - 1 ) x. %s ) )' % (QZ, WS),
                       '( ( s - 1 ) x. ( %s + %s ) )' % (QZ, WS), '( ( s - 1 ) x. ( %s + %s ) )' % (WS, QZ), '( ( s - 1 ) x. %s )' % VS],
               [E(w, As, 'oveq12d', [E(w, As, 'oveq2d', [zs], '( %s x. %s )' % (QM, ZF('s')), '( %s x. ( ( s - 1 ) x. %s ) )' % (QM, ZS)),
                                     E(w, As, 'oveq2d', [ag], '( ( s - 1 ) x. %s )' % AB('s'), '( ( s - 1 ) x. %s )' % WS)], EV('s'),
                  '( ( %s x. ( ( s - 1 ) x. %s ) ) + ( ( s - 1 ) x. %s ) )' % (QM, ZS, WS)),
                E(w, As, 'oveq1d', [E(w, As, 'mul12d', [qc, s1c, zsc], '( %s x. ( ( s - 1 ) x. %s ) )' % (QM, ZS), '( ( s - 1 ) x. %s )' % QZ)],
                  '( ( %s x. ( ( s - 1 ) x. %s ) ) + ( ( s - 1 ) x. %s ) )' % (QM, ZS, WS), '( ( ( s - 1 ) x. %s ) + ( ( s - 1 ) x. %s ) )' % (QZ, WS)),
                ('r', E(w, As, 'adddid', [s1c, w.s([qc, zsc], 'mulcld', '( %s -> %s e. CC )' % (As, QZ)), wsc], '( ( s - 1 ) x. ( %s + %s ) )' % (QZ, WS),
                        '( ( ( s - 1 ) x. %s ) + ( ( s - 1 ) x. %s ) )' % (QZ, WS))),
                E(w, As, 'oveq2d', [E(w, As, 'addcomd', [w.s([qc, zsc], 'mulcld', '( %s -> %s e. CC )' % (As, QZ)), wsc], '( %s + %s )' % (QZ, WS), '( %s + %s )' % (WS, QZ))],
                  '( ( s - 1 ) x. ( %s + %s ) )' % (QZ, WS), '( ( s - 1 ) x. ( %s + %s ) )' % (WS, QZ)),
                ('r', E(w, As, 'oveq2d', [vs], '( ( s - 1 ) x. %s )' % VS, '( ( s - 1 ) x. ( %s + %s ) )' % (WS, QZ)))])
    # VS = LSX (the character read through CX)
    cxk = w.s([w.s([nxk, kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX)), w.inst('zl1cxv')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, CX, CHV('k')))
    lsx = w.s([w.s([cxk], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u s ) ) = ( %s x. ( k ^c -u s ) ) )' % (Ak, CX, CHV('k')))], 'sumeq2dv', '( %s -> %s = %s )' % (As, LSX, VS))
    fin = chain(w, As, ['( %s ` s )' % LF, EV('s'), '( ( s - 1 ) x. %s )' % VS, '( ( s - 1 ) x. %s )' % LSX],
                [v, ev, ('r', E(w, As, 'oveq2d', [lsx], '( ( s - 1 ) x. %s )' % LSX, '( ( s - 1 ) x. %s )' % VS))])
    im = w.s([fin], 'ex', '( ( %s /\\ s e. %s ) -> ( 1 < ( Re ` s ) -> ( %s ` s ) = ( ( s - 1 ) x. %s ) ) )' % (A0, HPZ, LF, LSX))
    w.qed([im], 'ralrimiva', '( %s -> %s )' % (A0, DSERX))
    go(w)

if not only or 'zl1lif' in only:
    w = W('zl1lif', 'The L-function interface of ~ z6dlbz , except the convexity bound ` CVXH ` , at a set.mm Dirichlet '
          'character ` X ` mod ` N ` : the character facts ` CHRB ` of ` a |-> X ( a ) ` and, for ` E = ( N DChrLF X ) ` , '
          '` EHOL ` , ` E ( 1 ) = RESV ` and ` DSER ` (the Mathlib ` LFunction ` facts the Lean consumers use: '
          '` differentiableAt_LFunction ` , ` LFunctionTrivChar_1 ` , ` LFunction_eq_LSeries ` ).')
    A0 = NX
    c = w.s([], 'zl1chrb', '( %s -> %s )' % (A0, CHRBX))
    h = w.s([], 'zl1ehol', '( %s -> %s )' % (A0, EHOLX))
    e = w.s([], 'zl1e1', '( %s -> ( %s ` 1 ) = %s )' % (A0, LF, RESVX))
    d = w.s([], 'zl1dser', '( %s -> %s )' % (A0, DSERX))
    w.qed([c, w.s([w.s([h, e], 'jca', '( %s -> ( %s /\\ ( %s ` 1 ) = %s ) )' % (A0, EHOLX, LF, RESVX)), d], 'jca',
                  '( %s -> ( ( %s /\\ ( %s ` 1 ) = %s ) /\\ %s ) )' % (A0, EHOLX, LF, RESVX, DSERX))], 'jca', '( %s -> %s )' % (A0, STATEMENTS['zl1lif'].split(' -> ', 1)[1][:-2]))
    go(w)

if not only or 'zl1dlbz' in only:
    w = W('zl1dlbz', 'Proposition 4.4 of the blueprint ( ~ z6dlbz , Lean ` detector_lower_bound_of_zero_all ` ) at a set.mm '
          'Dirichlet character ` X ` mod ` N ` with ` E = ( N DChrLF X ) ` : every hypothesis of the L-function interface is '
          'discharged ( ~ zl1lif ) except the convexity bound ` CVXH ` .')
    A0 = STATEMENTS['zl1dlbz'][2:].split(' -> ( ( ( 1 / ; ; 4 0 0 )')[0]
    HZ = Z6.HZD3
    P1 = '( %s /\\ %s )' % (HZ, NX)
    MID = '( ( ( %s /\\ S =/= 1 ) /\\ %s ) /\\ ( %s /\\ ( %s /\\ ( %s ` S ) = 0 ) ) )' % (Z6.SRNG, Z6.HDN, Z6.T1, CVXHX, LF)
    HG = '( %s = %s -> %s <_ ( abs ` ( Im ` S ) ) )' % (CX, PRN, Z6.LAM60)
    TR = '( %s /\\ %s )' % (Z6.TRNG, HG)
    p1 = w.s([], 'simpll', '( %s -> %s )' % (A0, P1))
    hz = w.s([p1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HZ))
    nx = w.s([p1, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NX))
    nn = w.s([nx, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    q = w.s([], 'simplr', '( %s -> %s )' % (A0, MID))
    SH = '( ( %s /\\ S =/= 1 ) /\\ %s )' % (Z6.SRNG, Z6.HDN)
    srh = w.s([q, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, SH))
    rest = w.s([q, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ ( %s /\\ ( %s ` S ) = 0 ) ) )' % (A0, Z6.T1, CVXHX, LF))
    t1 = w.s([rest, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, Z6.T1))
    cz = w.s([rest, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ ( %s ` S ) = 0 ) )' % (A0, CVXHX, LF))
    cvx = w.s([cz, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CVXHX))
    zr = w.s([cz, w.inst('simpr')], 'syl', '( %s -> ( %s ` S ) = 0 )' % (A0, LF))
    tr = w.s([], 'simpr', '( %s -> %s )' % (A0, TR))
    LIFP = '( ( %s /\\ ( %s ` 1 ) = %s ) /\\ %s )' % (EHOLX, LF, RESVX, DSERX)
    lif = w.s([nx, w.inst('zl1lif')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, CHRBX, LIFP))
    chrb = w.s([lif, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CHRBX))
    lp = w.s([lif, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, LIFP))
    eh1 = w.s([lp, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ ( %s ` 1 ) = %s ) )' % (A0, EHOLX, LF, RESVX))
    ds = w.s([lp, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, DSERX))
    LIFX = CI(Z6.LIF)
    lifx = w.s([eh1, w.s([ds, cvx], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, DSERX, CVXHX))], 'jca', '( %s -> %s )' % (A0, LIFX))
    A7X = CI(Z6.A7)
    a7a = w.s([hz, nn], 'jca', '( %s -> ( %s /\\ N e. NN ) )' % (A0, HZ))
    a7b = w.s([chrb, srh], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CHRBX, SH))
    a7c = w.s([t1, w.s([lifx, zr], 'jca', '( %s -> ( %s /\\ ( %s ` S ) = 0 ) )' % (A0, LIFX, LF))], 'jca', '( %s -> ( %s /\\ ( %s /\\ ( %s ` S ) = 0 ) ) )' % (A0, Z6.T1, LIFX, LF))
    a7 = w.s([w.s([a7a, a7b], 'jca', '( %s -> ( ( %s /\\ N e. NN ) /\\ ( %s /\\ %s ) ) )' % (A0, HZ, CHRBX, SH)), a7c], 'jca', '( %s -> %s )' % (A0, A7X))
    ant = w.s([a7, tr], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, A7X, TR))
    CONC = STATEMENTS['zl1dlbz'][len(A0) + 6:-2]
    w.qed([ant, w.inst('z6dlbz')], 'syl', '( %s -> %s )' % (A0, CONC))
    go(w)
