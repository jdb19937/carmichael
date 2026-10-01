"""Sortie v2: the powerset expansion  sum_ t e. ~P T prod_ p e. t B = prod_ p e. T ( 1 + B )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

YZ = '( y u. { z } )'
PWYZ = '~P ( y u. { z } )'
Q2 = '( ~P ( y u. { z } ) \\ ~P y )'
F = '( u e. ~P y |-> ( u u. { z } ) )'
NZ = '-. z e. y'


def pwpdifsn():
    w = W('pwpdifsn', 'Removing a new element from a set with it adjoined.')
    d1 = w.s([], 'difun2', '( %s \\ { z } ) = ( y \\ { z } )' % YZ)
    d1a = w.s([d1], 'a1i', '( %s -> ( %s \\ { z } ) = ( y \\ { z } ) )' % (NZ, YZ))
    d2 = w.s([], 'difsn', '( %s -> ( y \\ { z } ) = y )' % NZ)
    w.qed([d1a, d2], 'eqtrd', '( %s -> ( %s \\ { z } ) = y )' % (NZ, YZ))
    return w


def pwpf1o():
    w = W('pwpf1o', 'Adjoining a new element is a bijection from the powerset onto the new subsets.')
    A = NZ
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    fdef = w.s([], 'eqid', '%s = %s' % (F, F))
    # ( 2 ) the map lands in Q2
    BU = '( %s /\\ u e. ~P y )' % A
    uss = st([w.s([], 'simpr', '( %s -> u e. ~P y )' % BU), w.inst('elpwi')], 'syl',
             'u C_ y', BU)
    usu = st([uss, w.inst('unss1')], 'syl', '( u u. { z } ) C_ %s' % YZ, BU)
    uset = st([w.s([], 'vex', 'u e. _V')], 'a1i', 'u e. _V', BU)
    zset = st([w.s([], 'snex', '{ z } e. _V')], 'a1i', '{ z } e. _V', BU)
    unset = st([uset, zset], 'unexd', '( u u. { z } ) e. _V', BU)
    upw = st([unset, usu], 'elpwd', '( u u. { z } ) e. %s' % PWYZ, BU)
    zin = st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }', BU)
    ssu2 = st([w.s([], 'ssun2', '{ z } C_ ( u u. { z } )')], 'a1i', '{ z } C_ ( u u. { z } )', BU)
    zinu = st([ssu2, zin], 'sseldd', 'z e. ( u u. { z } )', BU)
    nzy = st([], 'simpl', NZ, BU)
    # -. ( u u. { z } ) e. ~P y
    BUP = '( %s /\\ ( u u. { z } ) e. ~P y )' % BU
    inp = w.s([], 'simpr', '( %s -> ( u u. { z } ) e. ~P y )' % BUP)
    ssy = st([inp, w.inst('elpwi')], 'syl', '( u u. { z } ) C_ y', BUP)
    zinu2 = st([zinu], 'adantr', 'z e. ( u u. { z } )', BUP)
    zy = st([ssy, zinu2], 'sseldd', 'z e. y', BUP)
    npw = st([nzy, zy], 'mtand', '-. ( u u. { z } ) e. ~P y', BU)
    h2 = st([upw, npw], 'eldifd', '( u u. { z } ) e. %s' % Q2, BU)
    # ( 3 ) the inverse map lands in ~P y
    BT = '( %s /\\ t e. %s )' % (A, Q2)
    tpw = st([w.s([], 'simpr', '( %s -> t e. %s )' % (BT, Q2)), w.inst('eldifi')], 'syl',
             't e. %s' % PWYZ, BT)
    tss = st([tpw, w.inst('elpwi')], 'syl', 't C_ %s' % YZ, BT)
    tds = st([tss, w.inst('ssdif')], 'syl', '( t \\ { z } ) C_ ( %s \\ { z } )' % YZ, BT)
    ds = st([st([], 'simpl', NZ, BT), w.inst('pwpdifsn')], 'syl', '( %s \\ { z } ) = y' % YZ, BT)
    tssy = st([tds, ds], 'sseqtrd', '( t \\ { z } ) C_ y', BT)
    tset = st([w.s([], 'vex', 't e. _V')], 'a1i', 't e. _V', BT)
    tdset = st([tset], 'difexd', '( t \\ { z } ) e. _V', BT)
    h3 = st([tdset, tssy], 'elpwd', '( t \\ { z } ) e. ~P y', BT)
    # ( 4 ) the two equations agree
    BB = '( %s /\\ ( u e. ~P y /\\ t e. %s ) )' % (A, Q2)
    ut = st([], 'simprl', 'u e. ~P y', BB)
    tt = st([], 'simprr', 't e. %s' % Q2, BB)
    nzy2 = st([], 'simpl', NZ, BB)
    zt = st([tt, w.inst('elpwunsn')], 'syl', 'z e. t', BB)
    ussb = st([ut, w.inst('elpwi')], 'syl', 'u C_ y', BB)
    nzu = st([ussb, nzy2], 'ssneldd', '-. z e. u', BB)
    # forward: u = ( t \ { z } ) -> t = ( u u. { z } )
    CF = '( %s /\\ u = ( t \\ { z } ) )' % BB
    eqf = st([], 'simpr', 'u = ( t \\ { z } )', CF)
    uf = st([eqf], 'uneq1d', '( u u. { z } ) = ( ( t \\ { z } ) u. { z } )', CF)
    dsi = st([st([zt], 'adantr', 'z e. t', CF), w.inst('difsnid')], 'syl',
             '( ( t \\ { z } ) u. { z } ) = t', CF)
    fwd = st([uf, dsi], 'eqtr2d', 't = ( u u. { z } )', CF)
    # backward: t = ( u u. { z } ) -> u = ( t \ { z } )
    CB = '( %s /\\ t = ( u u. { z } ) )' % BB
    eqb = st([], 'simpr', 't = ( u u. { z } )', CB)
    db = st([eqb], 'difeq1d', '( t \\ { z } ) = ( ( u u. { z } ) \\ { z } )', CB)
    db2 = st([st([nzu], 'adantr', '-. z e. u', CB), w.inst('pwpdifsn')], 'syl',
             '( ( u u. { z } ) \\ { z } ) = u', CB)
    bwd = st([db, db2], 'eqtr2d', 'u = ( t \\ { z } )', CB)
    h4 = st([st([fwd], 'ex', '( u = ( t \\ { z } ) -> t = ( u u. { z } ) )', BB),
             st([bwd], 'ex', '( t = ( u u. { z } ) -> u = ( t \\ { z } ) )', BB)], 'impbid',
            '( u = ( t \\ { z } ) <-> t = ( u u. { z } ) )', BB)
    w.qed([fdef, h2, h3, h4], 'f1o2d', '( %s -> %s : ~P y -1-1-onto-> %s )' % (A, F, Q2))
    return w


GP = '( G ` p )'
GZ = '( G ` z )'
SUP = 'G : S --> CC'
A2 = '( ( y e. Fin /\\ %s ) /\\ ( %s /\\ %s C_ S ) )' % (NZ, SUP, YZ)


def pwpsum2():
    w = W('pwpsum2', 'The sum over the new subsets is the sum over the old ones times the new value.')
    A = A2
    SQ2 = 'sum_ t e. %s prod_ p e. t %s' % (Q2, GP)
    SV = 'sum_ v e. ~P y prod_ p e. ( v u. { z } ) %s' % GP
    SU = 'sum_ v e. ~P y prod_ p e. v %s' % GP
    ST = 'sum_ t e. ~P y prod_ p e. t %s' % GP
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    yfin = st([], 'simpll', 'y e. Fin')
    nz = st([], 'simplr', NZ)
    gf = st([], 'simprl', SUP)
    yzs = st([], 'simprr', '%s C_ S' % YZ)
    f1o = st([nz, w.inst('pwpf1o')], 'syl', '%s : ~P y -1-1-onto-> %s' % (F, Q2))
    pwfin = st([yfin, w.inst('pwfi')], 'sylib', '~P y e. Fin')
    yzfin = st([yfin, st([w.s([], 'snfi', '{ z } e. Fin')], 'a1i', '{ z } e. Fin')], 'unfid',
               '%s e. Fin' % YZ)
    # ( F ` v ) = ( v u. { z } ) for v e. ~P y
    BV = '( %s /\\ v e. ~P y )' % A
    fdef = w.s([], 'eqid', '%s = %s' % (F, F))
    sub = w.s([], 'uneq1', '( u = v -> ( u u. { z } ) = ( v u. { z } ) )')
    vin = w.s([], 'simpr', '( %s -> v e. ~P y )' % BV)
    vset = st([w.s([], 'vex', 'v e. _V')], 'a1i', 'v e. _V', BV)
    zsn = st([w.s([], 'snex', '{ z } e. _V')], 'a1i', '{ z } e. _V', BV)
    vuset = st([vset, zsn], 'unexd', '( v u. { z } ) e. _V', BV)
    fvi = w.s([sub, fdef], 'fvmptg',
              '( ( v e. ~P y /\\ ( v u. { z } ) e. _V ) -> ( %s ` v ) = ( v u. { z } ) )' % F)
    fval = st([vin, vuset, fvi], 'syl2anc', '( %s ` v ) = ( v u. { z } )' % F, BV)
    # closure of the product over t e. Q2
    BT2 = '( %s /\\ t e. %s )' % (A, Q2)
    tpw = st([w.s([], 'simpr', '( %s -> t e. %s )' % (BT2, Q2)), w.inst('eldifi')], 'syl',
             't e. %s' % PWYZ, BT2)
    tss = st([tpw, w.inst('elpwi')], 'syl', 't C_ %s' % YZ, BT2)
    tfin = st([st([yzfin], 'adantr', '%s e. Fin' % YZ, BT2), tss], 'ssfid', 't e. Fin', BT2)
    tsS = st([tss, st([yzs], 'adantr', '%s C_ S' % YZ, BT2)], 'sstrd', 't C_ S', BT2)
    BTP = '( %s /\\ p e. t )' % BT2
    pit = st([st([tsS], 'adantr', 't C_ S', BTP), w.s([], 'simpr', '( %s -> p e. t )' % BTP)],
             'sseldd', 'p e. S', BTP)
    bcl = st([st([st([gf], 'adantr', SUP, BT2)], 'adantr', SUP, BTP), pit], 'ffvelcdmd',
             '%s e. CC' % GP, BTP)
    pcl = st([tfin, bcl], 'fprodcl', 'prod_ p e. t %s e. CC' % GP, BT2)
    sub2 = w.s([], 'prodeq1', '( t = ( v u. { z } ) -> prod_ p e. t %s = prod_ p e. ( v u. { z } ) %s )' % (GP, GP))
    e1 = st([sub2, pwfin, f1o, fval, pcl], 'fsumf1o', '%s = %s' % (SQ2, SV))
    # termwise: split off z
    vss = st([vin, w.inst('elpwi')], 'syl', 'v C_ y', BV)
    vfin = st([st([yfin], 'adantr', 'y e. Fin', BV), vss], 'ssfid', 'v e. Fin', BV)
    nzv = st([vss, st([nz], 'adantr', NZ, BV)], 'ssneldd', '-. z e. v', BV)
    nfz = w.s([], 'nfcv', 'F/_ p %s' % GZ)
    zex = st([w.s([], 'vex', 'z e. _V')], 'a1i', 'z e. _V', BV)
    csb = w.s([], 'fveq2', '( p = z -> %s = %s )' % (GP, GZ))
    zyz = st([w.s([], 'ssun2', '{ z } C_ %s' % YZ),
              st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }', BV)],
             'sselid', 'z e. %s' % YZ, BV)
    zS = st([st([yzs], 'adantr', '%s C_ S' % YZ, BV), zyz], 'sseldd', 'z e. S', BV)
    gfv = st([gf], 'adantr', SUP, BV)
    bzcl = st([gfv, zS], 'ffvelcdmd', '%s e. CC' % GZ, BV)
    BVP = '( %s /\\ p e. v )' % BV
    ysyz = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    ysS = st([ysyz, yzs], 'sstrd', 'y C_ S')
    vsy = st([vss, st([ysS], 'adantr', 'y C_ S', BV)], 'sstrd', 'v C_ S', BV)
    piv = st([st([vsy], 'adantr', 'v C_ S', BVP), w.s([], 'simpr', '( %s -> p e. v )' % BVP)],
             'sseldd', 'p e. S', BVP)
    bclv = st([st([gfv], 'adantr', SUP, BVP), piv], 'ffvelcdmd', '%s e. CC' % GP, BVP)
    spl = st([nfz, vfin, zex, nzv, bclv, csb, bzcl], 'fprodsplitsn',
             'prod_ p e. ( v u. { z } ) %s = ( prod_ p e. v %s x. %s )' % (GP, GP, GZ), BV)
    e2 = st([spl], 'sumeq2dv', '%s = sum_ v e. ~P y ( prod_ p e. v %s x. %s )' % (SV, GP, GZ))
    pclv = st([vfin, bclv], 'fprodcl', 'prod_ p e. v %s e. CC' % GP, BV)
    zyz0 = st([w.s([], 'ssun2', '{ z } C_ %s' % YZ),
               st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')],
              'sselid', 'z e. %s' % YZ)
    zS0 = st([yzs, zyz0], 'sseldd', 'z e. S')
    bzcl0 = st([gf, zS0], 'ffvelcdmd', '%s e. CC' % GZ)
    e3 = st([pwfin, bzcl0, pclv], 'fsummulc1',
            '( %s x. %s ) = sum_ v e. ~P y ( prod_ p e. v %s x. %s )' % (SU, GZ, GP, GZ))
    cb = st([w.s([], 'cbvsumv', '%s = %s' % (SU, ST))], 'a1i', '%s = %s' % (SU, ST))
    e4 = st([e1, e2], 'eqtrd', '%s = sum_ v e. ~P y ( prod_ p e. v %s x. %s )' % (SQ2, GP, GZ))
    e5 = st([e4, e3], 'eqtr4d', '%s = ( %s x. %s )' % (SQ2, SU, GZ))
    e6 = st([cb], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (SU, GZ, ST, GZ))
    w.qed([e5, e6], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A, SQ2, ST, GZ))
    return w


def pwpstep1():
    w = W('pwpstep1', 'The induction step of the powerset expansion.')
    A = A2
    SUMy = 'sum_ t e. ~P y prod_ p e. t %s' % GP
    SUMQ = 'sum_ t e. %s prod_ p e. t %s' % (Q2, GP)
    SUMyz = 'sum_ t e. %s prod_ p e. t %s' % (PWYZ, GP)
    PRODy = 'prod_ p e. y ( 1 + %s )' % GP
    PRODyz = 'prod_ p e. %s ( 1 + %s )' % (YZ, GP)
    AI = '( %s /\\ %s = %s )' % (A, SUMy, PRODy)
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    yfin = st([], 'simpll', 'y e. Fin')
    nz = st([], 'simplr', NZ)
    gf = st([], 'simprl', SUP)
    yzs = st([], 'simprr', '%s C_ S' % YZ)
    ysyz = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    ysS = st([ysyz, yzs], 'sstrd', 'y C_ S')
    yzfin = st([yfin, st([w.s([], 'snfi', '{ z } e. Fin')], 'a1i', '{ z } e. Fin')], 'unfid',
               '%s e. Fin' % YZ)
    pwyzfin = st([yzfin, w.inst('pwfi')], 'sylib', '%s e. Fin' % PWYZ)
    # the split of the powerset
    disj = st([w.s([], 'disjdif', '( ~P y i^i %s ) = (/)' % Q2)], 'a1i', '( ~P y i^i %s ) = (/)' % Q2)
    sspw = st([ysyz, w.inst('sspwb')], 'sylib', '~P y C_ %s' % PWYZ)
    und = st([sspw, w.inst('undif')], 'sylib', '( ~P y u. %s ) = %s' % (Q2, PWYZ))
    uni = st([und], 'eqcomd', '%s = ( ~P y u. %s )' % (PWYZ, Q2))
    # closure of the summand on ~P YZ
    BT = '( %s /\\ t e. %s )' % (A, PWYZ)
    tss = st([w.s([], 'simpr', '( %s -> t e. %s )' % (BT, PWYZ)), w.inst('elpwi')], 'syl',
             't C_ %s' % YZ, BT)
    tfin = st([st([yzfin], 'adantr', '%s e. Fin' % YZ, BT), tss], 'ssfid', 't e. Fin', BT)
    tsS = st([tss, st([yzs], 'adantr', '%s C_ S' % YZ, BT)], 'sstrd', 't C_ S', BT)
    BTP = '( %s /\\ p e. t )' % BT
    pit = st([st([tsS], 'adantr', 't C_ S', BTP), w.s([], 'simpr', '( %s -> p e. t )' % BTP)],
             'sseldd', 'p e. S', BTP)
    bcl = st([st([st([gf], 'adantr', SUP, BT)], 'adantr', SUP, BTP), pit], 'ffvelcdmd',
             '%s e. CC' % GP, BTP)
    pcl = st([tfin, bcl], 'fprodcl', 'prod_ p e. t %s e. CC' % GP, BT)
    spl = st([disj, uni, pwyzfin, pcl], 'fsumsplit', '%s = ( %s + %s )' % (SUMyz, SUMy, SUMQ))
    s2 = st([], 'pwpsum2', '%s = ( %s x. %s )' % (SUMQ, SUMy, GZ))
    # the new value and the closures over y
    zyz = st([w.s([], 'ssun2', '{ z } C_ %s' % YZ),
              st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')], 'sselid',
             'z e. %s' % YZ)
    zS = st([yzs, zyz], 'sseldd', 'z e. S')
    gzcl = st([gf, zS], 'ffvelcdmd', '%s e. CC' % GZ)
    BY = '( %s /\\ p e. y )' % A
    piy = st([st([ysS], 'adantr', 'y C_ S', BY), w.s([], 'simpr', '( %s -> p e. y )' % BY)],
             'sseldd', 'p e. S', BY)
    gpcl = st([st([gf], 'adantr', SUP, BY), piy], 'ffvelcdmd', '%s e. CC' % GP, BY)
    oneb = w.s([], '1cnd', '( %s -> 1 e. CC )' % BY)
    bodyc = st([oneb, gpcl], 'addcld', '( 1 + %s ) e. CC' % GP, BY)
    prodyc = st([yfin, bodyc], 'fprodcl', '%s e. CC' % PRODy)
    # PRODyz = ( PRODy x. ( 1 + GZ ) )
    nfd = w.s([], 'nfcv', 'F/_ p ( 1 + %s )' % GZ)
    zex = st([w.s([], 'vex', 'z e. _V')], 'a1i', 'z e. _V')
    subc = w.s([], 'fveq2', '( p = z -> %s = %s )' % (GP, GZ))
    subd = w.s([subc], 'oveq2d', '( p = z -> ( 1 + %s ) = ( 1 + %s ) )' % (GP, GZ))
    onea = w.s([], '1cnd', '( %s -> 1 e. CC )' % A)
    dcl = st([onea, gzcl], 'addcld', '( 1 + %s ) e. CC' % GZ)
    pyz = st([nfd, yfin, zex, nz, bodyc, subd, dcl], 'fprodsplitsn',
             '%s = ( %s x. ( 1 + %s ) )' % (PRODyz, PRODy, GZ))
    # under the induction hypothesis
    ih = w.s([], 'simpr', '( %s -> %s = %s )' % (AI, SUMy, PRODy))
    splI = st([spl], 'adantr', '%s = ( %s + %s )' % (SUMyz, SUMy, SUMQ), AI)
    s2I = st([s2], 'adantr', '%s = ( %s x. %s )' % (SUMQ, SUMy, GZ), AI)
    e1 = st([ih, st([ih], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (SUMy, GZ, PRODy, GZ), AI)],
            'oveq12d', '( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) )' % (SUMy, SUMy, GZ, PRODy, PRODy, GZ), AI)
    e2 = st([s2I], 'oveq2d', '( %s + %s ) = ( %s + ( %s x. %s ) )' % (SUMy, SUMQ, SUMy, SUMy, GZ), AI)
    e3 = st([splI, e2], 'eqtrd', '%s = ( %s + ( %s x. %s ) )' % (SUMyz, SUMy, SUMy, GZ), AI)
    e4 = st([e3, e1], 'eqtrd', '%s = ( %s + ( %s x. %s ) )' % (SUMyz, PRODy, PRODy, GZ), AI)
    prodycI = st([prodyc], 'adantr', '%s e. CC' % PRODy, AI)
    gzclI = st([gzcl], 'adantr', '%s e. CC' % GZ, AI)
    oneI = w.s([], '1cnd', '( %s -> 1 e. CC )' % AI)
    dist = st([prodycI, oneI, gzclI], 'adddid',
              '( %s x. ( 1 + %s ) ) = ( ( %s x. 1 ) + ( %s x. %s ) )' % (PRODy, GZ, PRODy, PRODy, GZ), AI)
    mr = st([prodycI], 'mulridd', '( %s x. 1 ) = %s' % (PRODy, PRODy), AI)
    dist2 = st([dist, st([mr], 'oveq1d',
               '( ( %s x. 1 ) + ( %s x. %s ) ) = ( %s + ( %s x. %s ) )' % (PRODy, PRODy, GZ, PRODy, PRODy, GZ), AI)],
               'eqtrd', '( %s x. ( 1 + %s ) ) = ( %s + ( %s x. %s ) )' % (PRODy, GZ, PRODy, PRODy, GZ), AI)
    pyzI = st([pyz], 'adantr', '%s = ( %s x. ( 1 + %s ) )' % (PRODyz, PRODy, GZ), AI)
    rhs = st([pyzI, dist2], 'eqtrd', '%s = ( %s + ( %s x. %s ) )' % (PRODyz, PRODy, PRODy, GZ), AI)
    fin = st([e4, rhs], 'eqtr4d', '%s = %s' % (SUMyz, PRODyz), AI)
    w.qed([fin], 'ex', '( %s -> ( %s = %s -> %s = %s ) )' % (A, SUMy, PRODy, SUMyz, PRODyz))
    return w


def PHI(X):
    return ('( ( %s e. Fin /\\ ( %s /\\ %s C_ S ) ) -> '
            'sum_ t e. ~P %s prod_ p e. t %s = prod_ p e. %s ( 1 + %s ) )'
            % (X, SUP, X, X, GP, X, GP))


def pwprod():
    w = W('pwprod',
          'The powerset expansion of a product: summing the products of the values of G over the '
          'subsets of T gives the product of 1 + ( G ` p ) over T.')
    def subst(X):
        """( x = X -> ( PHI( x ) <-> PHI( X ) ) )"""
        e = 'x = %s' % X
        a = w.s([], 'eleq1', '( %s -> ( x e. Fin <-> %s e. Fin ) )' % (e, X))
        b = w.s([], 'sseq1', '( %s -> ( x C_ S <-> %s C_ S ) )' % (e, X))
        b2 = w.s([b], 'anbi2d', '( %s -> ( ( %s /\\ x C_ S ) <-> ( %s /\\ %s C_ S ) ) )' % (e, SUP, SUP, X))
        ab = w.s([a, b2], 'anbi12d',
                 '( %s -> ( ( x e. Fin /\\ ( %s /\\ x C_ S ) ) <-> ( %s e. Fin /\\ ( %s /\\ %s C_ S ) ) ) )'
                 % (e, SUP, X, SUP, X))
        pw = w.s([], 'pweq', '( %s -> ~P x = ~P %s )' % (e, X))
        su = w.s([pw], 'sumeq1d',
                 '( %s -> sum_ t e. ~P x prod_ p e. t %s = sum_ t e. ~P %s prod_ p e. t %s )'
                 % (e, GP, X, GP))
        pr = w.s([], 'prodeq1', '( %s -> prod_ p e. x ( 1 + %s ) = prod_ p e. %s ( 1 + %s ) )'
                 % (e, GP, X, GP))
        eq = w.s([su, pr], 'eqeq12d',
                 '( %s -> ( sum_ t e. ~P x prod_ p e. t %s = prod_ p e. x ( 1 + %s ) <-> '
                 'sum_ t e. ~P %s prod_ p e. t %s = prod_ p e. %s ( 1 + %s ) ) )'
                 % (e, GP, GP, X, GP, X, GP))
        return w.s([ab, eq], 'imbi12d', '( %s -> ( %s <-> %s ) )' % (e, PHI('x'), PHI(X)))
    h1 = subst('(/)')
    h2 = subst('y')
    h3 = subst(YZ)
    h4 = subst('T')
    # base case
    pw0 = w.s([], 'pw0', '~P (/) = { (/) }')
    sq = w.s([pw0], 'sumeq1i', 'sum_ t e. ~P (/) prod_ p e. t %s = sum_ t e. { (/) } prod_ p e. t %s' % (GP, GP))
    sub0 = w.s([], 'prodeq1', '( t = (/) -> prod_ p e. t %s = prod_ p e. (/) %s )' % (GP, GP))
    p0 = w.s([], 'prod0', 'prod_ p e. (/) %s = 1' % GP)
    p0c = w.s([], 'ax-1cn', '1 e. CC')
    p0cc = w.s([p0, p0c], 'eqeltri', 'prod_ p e. (/) %s e. CC' % GP)
    zex = w.s([], '0ex', '(/) e. _V')
    sni = w.s([sub0], 'sumsn',
              '( ( (/) e. _V /\\ prod_ p e. (/) %s e. CC ) -> sum_ t e. { (/) } prod_ p e. t %s = prod_ p e. (/) %s )'
              % (GP, GP, GP))
    sn = w.s([zex, p0cc, sni], 'mp2an',
             'sum_ t e. { (/) } prod_ p e. t %s = prod_ p e. (/) %s' % (GP, GP))
    lhs = w.s([sq, sn], 'eqtri', 'sum_ t e. ~P (/) prod_ p e. t %s = prod_ p e. (/) %s' % (GP, GP))
    lhs1 = w.s([lhs, p0], 'eqtri', 'sum_ t e. ~P (/) prod_ p e. t %s = 1' % GP)
    r0 = w.s([], 'prod0', 'prod_ p e. (/) ( 1 + %s ) = 1' % GP)
    base = w.s([lhs1, r0], 'eqtr4i',
               'sum_ t e. ~P (/) prod_ p e. t %s = prod_ p e. (/) ( 1 + %s )' % (GP, GP))
    h5 = w.s([base], 'a1i', PHI('(/)'))
    # the step
    AST = '( y e. Fin /\\ %s )' % NZ
    ANTyz = '( %s e. Fin /\\ ( %s /\\ %s C_ S ) )' % (YZ, SUP, YZ)
    ANTy = '( y e. Fin /\\ ( %s /\\ y C_ S ) )' % SUP
    CS = '( %s /\\ %s )' % (AST, ANTyz)
    def st(hyps, ref, f, ante=CS):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    yfin = st([], 'simpll', 'y e. Fin')
    nzs = st([], 'simplr', NZ)
    gfs = st([], 'simprrl' if False else 'simprr', '( %s /\\ %s C_ S )' % (SUP, YZ))
    gf = st([gfs], 'simpld', SUP)
    yzs = st([gfs], 'simprd', '%s C_ S' % YZ)
    ysyz = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    ysS = st([ysyz, yzs], 'sstrd', 'y C_ S')
    anty = st([yfin, st([gf, ysS], 'jca', '( %s /\\ y C_ S )' % SUP)], 'jca', ANTy)
    a2 = st([st([yfin, nzs], 'jca', AST), gfs], 'jca', A2)
    stp = st([a2, w.inst('pwpstep1')], 'syl',
             '( sum_ t e. ~P y prod_ p e. t %s = prod_ p e. y ( 1 + %s ) -> '
             'sum_ t e. %s prod_ p e. t %s = prod_ p e. %s ( 1 + %s ) )'
             % (GP, GP, PWYZ, GP, YZ, GP))
    mp27 = st([anty, w.inst('pm2.27')], 'syl',
              '( %s -> sum_ t e. ~P y prod_ p e. t %s = prod_ p e. y ( 1 + %s ) )' % (PHI('y'), GP, GP))
    ih = w.s([mp27, stp], 'syld',
             '( %s -> ( %s -> sum_ t e. %s prod_ p e. t %s = prod_ p e. %s ( 1 + %s ) ) )'
             % (CS, PHI('y'), PWYZ, GP, YZ, GP))
    ih2 = w.s([ih], 'com12', '( %s -> ( %s -> sum_ t e. %s prod_ p e. t %s = prod_ p e. %s ( 1 + %s ) ) )'
              % (PHI('y'), CS, PWYZ, GP, YZ, GP))
    ih3 = w.s([ih2], 'expd',
              '( %s -> ( %s -> ( %s -> sum_ t e. %s prod_ p e. t %s = prod_ p e. %s ( 1 + %s ) ) ) )'
              % (PHI('y'), AST, ANTyz, PWYZ, GP, YZ, GP))
    h6 = w.s([ih3], 'com12', '( %s -> ( %s -> %s ) )' % (AST, PHI('y'), PHI(YZ)))
    res = w.s([h1, h2, h3, h4, h5, h6], 'findcard2s', '( T e. Fin -> %s )' % PHI('T'))
    ANT = '( T e. Fin /\\ ( %s /\\ T C_ S ) )' % SUP
    tf = w.s([], 'simpl', '( %s -> T e. Fin )' % ANT)
    d1 = w.s([tf, res], 'syl', '( %s -> %s )' % (ANT, PHI('T')))
    w.qed([d1], 'pm2.43i', '( %s -> sum_ t e. ~P T prod_ p e. t %s = prod_ p e. T ( 1 + %s ) )'
          % (ANT, GP, GP))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['pwpdifsn']:
        globals()[f]().run()


