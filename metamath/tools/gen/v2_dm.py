"""Sortie v2: DivisorMean.lean -- dmkey, divmeanw, divmean."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

def PF(X, v='q'): return '{ %s e. Prime | %s || %s }' % (v, v, X)
def OM(X): return '( # ` %s )' % PF(X)
GM = '( r e. Prime |-> X )'
SD = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || D ) }'
DV = '{ x e. NN | x || D }'
AN = '( ( D e. NN /\\ ( mmu ` D ) =/= 0 ) /\\ X e. CC )'


def dmkey():
    w = W('dmkey',
          'The divisor sum of X to the number of prime factors over a squarefree D.')
    SUMD = 'sum_ d e. %s ( X ^ %s )' % (DV, OM('d'))
    SUMS = 'sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SD, PF('d'), GM)
    SUMS2 = 'sum_ d e. %s ( X ^ %s )' % (SD, OM('d'))
    PRD = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (PF('D'), GM)
    def st(hyps, ref, f, ante=AN):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    d = st([], 'simpll', 'D e. NN')
    sqf = st([], 'simplr', '( mmu ` D ) =/= 0')
    x = st([], 'simpr', 'X e. CC')
    # G : Prime --> CC
    BP = '( %s /\\ r e. Prime )' % AN
    gfh = st([x], 'adantr', 'X e. CC', BP)
    gdef = w.s([], 'eqid', '%s = %s' % (GM, GM))
    gf = st([gfh, gdef], 'fmptd', '%s : Prime --> CC' % GM)
    # the master identity
    key = st([d, gf, w.inst('sqfdvdsum')], 'syl2anc', '%s = %s' % (SUMS, PRD))
    # ( G ` p ) = X on Prime
    xv = st([x], 'elexd', 'X e. _V')
    subfv = w.s([], 'eqidd', '( r = p -> X = X )')
    fvi = w.s([subfv, gdef], 'fvmptg', '( ( p e. Prime /\\ X e. _V ) -> ( %s ` p ) = X )' % GM)
    # rewrite the inner products
    BD = '( %s /\\ d e. %s )' % (AN, SD)
    dsd = w.s([], 'simpr', '( %s -> d e. %s )' % (BD, SD))
    dnn = st([dsd, w.inst('elrabi')], 'syl', 'd e. NN', BD)
    finp = st([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'), BD)
    cbvd = st([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
              '%s = %s' % (PF('d', 'p'), PF('d')), BD)
    find = st([cbvd, finp], 'eqeltrrd', '%s e. Fin' % PF('d'), BD)
    BDP = '( %s /\\ p e. %s )' % (BD, PF('d'))
    pprm = st([w.s([], 'simpr', '( %s -> p e. %s )' % (BDP, PF('d'))), w.inst('elrabi')], 'syl',
              'p e. Prime', BDP)
    xvd = st([st([xv], 'adantr', 'X e. _V', BD)], 'adantr', 'X e. _V', BDP)
    gval = st([pprm, xvd, fvi], 'syl2anc', '( %s ` p ) = X' % GM, BDP)
    pr1 = st([gval], 'prodeq2dv', 'prod_ p e. %s ( %s ` p ) = prod_ p e. %s X' % (PF('d'), GM, PF('d')), BD)
    pc = st([find, st([x], 'adantr', 'X e. CC', BD), w.inst('fprodconst')], 'syl2anc',
            'prod_ p e. %s X = ( X ^ %s )' % (PF('d'), OM('d')), BD)
    pr2 = st([pr1, pc], 'eqtrd', 'prod_ p e. %s ( %s ` p ) = ( X ^ %s )' % (PF('d'), GM, OM('d')), BD)
    e1 = st([pr2], 'sumeq2dv', '%s = %s' % (SUMS, SUMS2))
    # rewrite the outer product
    finDp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbvD = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), PF('D')))], 'a1i',
              '%s = %s' % (PF('D', 'p'), PF('D')))
    finD = st([cbvD, finDp], 'eqeltrrd', '%s e. Fin' % PF('D'))
    BDD = '( %s /\\ p e. %s )' % (AN, PF('D'))
    pprmD = st([w.s([], 'simpr', '( %s -> p e. %s )' % (BDD, PF('D'))), w.inst('elrabi')], 'syl',
               'p e. Prime', BDD)
    xvD = st([xv], 'adantr', 'X e. _V', BDD)
    gvalD = st([pprmD, xvD, fvi], 'syl2anc', '( %s ` p ) = X' % GM, BDD)
    gvalD2 = st([gvalD], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + X )' % GM, BDD)
    pr1D = st([gvalD2], 'prodeq2dv',
              '%s = prod_ p e. %s ( 1 + X )' % (PRD, PF('D')), AN)
    onec = st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')
    x1c = st([onec, x], 'addcld', '( 1 + X ) e. CC')
    pcD = st([finD, x1c, w.inst('fprodconst')], 'syl2anc',
             'prod_ p e. %s ( 1 + X ) = ( ( 1 + X ) ^ %s )' % (PF('D'), OM('D')))
    pr2D = st([pr1D, pcD], 'eqtrd', '%s = ( ( 1 + X ) ^ %s )' % (PRD, OM('D')))
    # the index set: all divisors of a squarefree D are squarefree
    BX = '( %s /\\ x e. NN )' % AN
    xnn = w.s([], 'simpr', '( %s -> x e. NN )' % BX)
    dsqf = st([sqf], 'adantr', '( mmu ` D ) =/= 0', BX)
    dnnb = st([d], 'adantr', 'D e. NN', BX)
    BX2 = '( %s /\\ x || D )' % BX
    dvv = w.s([], 'simpr', '( %s -> x || D )' % BX2)
    imp = st([st([dnnb], 'adantr', 'D e. NN', BX2), st([xnn], 'adantr', 'x e. NN', BX2), dvv,
              w.inst('dvdssqf')], 'syl3anc',
             '( ( mmu ` D ) =/= 0 -> ( mmu ` x ) =/= 0 )', BX2)
    sqx = st([st([dsqf], 'adantr', '( mmu ` D ) =/= 0', BX2), imp], 'mpd',
             '( mmu ` x ) =/= 0', BX2)
    bi = w.s([sqx], 'ex', '( %s -> ( x || D -> ( mmu ` x ) =/= 0 ) )' % BX)
    bi2 = st([bi], 'pm4.71rd', '( x || D <-> ( ( mmu ` x ) =/= 0 /\\ x || D ) )', BX)
    rab = st([bi2], 'rabbidva', '%s = %s' % (DV, SD))
    e0 = st([rab], 'sumeq1d', '%s = %s' % (SUMD, SUMS2))
    e2 = st([e1, key], 'eqtr3d', '%s = %s' % (SUMS2, PRD))
    e3 = st([e0, e2], 'eqtrd', '%s = %s' % (SUMD, PRD))
    e4 = st([e3, pr2D], 'eqtrd', '%s = ( ( 1 + X ) ^ %s )' % (SUMD, OM('D')))
    cm = st([onec, x], 'addcomd', '( 1 + X ) = ( X + 1 )')
    cm2 = st([cm], 'oveq1d', '( ( 1 + X ) ^ %s ) = ( ( X + 1 ) ^ %s )' % (OM('D'), OM('D')))
    w.qed([e4, cm2], 'eqtrd', '( %s -> %s = ( ( X + 1 ) ^ %s ) )' % (AN, SUMD, OM('D')))
    return w


def sqf1():
    w = W('sqf1', 'One is squarefree.')
    n1 = w.s([], '1nn', '1 e. NN')
    bi = w.s([n1, w.inst('issqf')], 'ax-mp',
             '( ( mmu ` 1 ) =/= 0 <-> A. p e. Prime ( p pCnt 1 ) <_ 1 )')
    pc = w.s([], 'pc1', '( p e. Prime -> ( p pCnt 1 ) = 0 )')
    z1 = w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( p e. Prime -> 0 <_ 1 )')
    le = w.s([pc, z1], 'eqbrtrd', '( p e. Prime -> ( p pCnt 1 ) <_ 1 )')
    ral = w.s([le], 'rgen', 'A. p e. Prime ( p pCnt 1 ) <_ 1')
    w.qed([ral, bi], 'mpbir', '( mmu ` 1 ) =/= 0')
    return w


def dmterm():
    w = W('dmterm', 'The divisor expansion of the ( K + 1 ) -st power weight at N.')
    AN2 = '( K e. NN0 /\\ N e. NN )'
    SQ = '( mmu ` N ) =/= 0'
    LHS = 'if ( %s , ( ( ( K + 1 ) ^ %s ) / N ) , 0 )' % (SQ, OM('N'))
    RHS = 'sum_ d e. { x e. NN | x || N } if ( %s , ( ( K ^ %s ) / N ) , 0 )' % (SQ, OM('d'))
    C1 = '( %s /\\ %s )' % (AN2, SQ)
    C2 = '( %s /\\ -. %s )' % (AN2, SQ)
    def st(hyps, ref, f, ante=AN2):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    # case N squarefree
    k1 = st([], 'simpll', 'K e. NN0', C1)
    n1 = st([], 'simplr', 'N e. NN', C1)
    sq1 = st([], 'simpr', SQ, C1)
    kc1 = st([k1], 'nn0cnd', 'K e. CC', C1)
    lhs1 = st([sq1], 'iftrued', '%s = ( ( ( K + 1 ) ^ %s ) / N )' % (LHS, OM('N')), C1)
    BD1 = '( %s /\\ d e. { x e. NN | x || N } )' % C1
    sq1d = st([sq1], 'adantr', SQ, BD1)
    ifd = st([sq1d], 'iftrued', 'if ( %s , ( ( K ^ %s ) / N ) , 0 ) = ( ( K ^ %s ) / N )'
             % (SQ, OM('d'), OM('d')), BD1)
    rhs1 = st([ifd], 'sumeq2dv', '%s = sum_ d e. { x e. NN | x || N } ( ( K ^ %s ) / N )'
              % (RHS, OM('d')), C1)
    # the divisor sum divided by N
    finN = st([n1, w.inst('dvdsfi')], 'syl', '{ x e. NN | x || N } e. Fin', C1)
    nc1 = st([n1], 'nncnd', 'N e. CC', C1)
    nne1 = st([n1], 'nnne0d', 'N =/= 0', C1)
    BD1P = BD1
    dnn = st([w.s([], 'simpr', '( %s -> d e. { x e. NN | x || N } )' % BD1), w.inst('elrabi')],
             'syl', 'd e. NN', BD1)
    omcl = st([st([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'),  BD1),
               st([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                  '%s = %s' % (PF('d', 'p'), PF('d')), BD1)], 'eqeltrrd',
              '%s e. Fin' % PF('d'), BD1)
    hcl = st([omcl, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'), BD1)
    kex = st([st([kc1], 'adantr', 'K e. CC', BD1), hcl], 'expcld', '( K ^ %s ) e. CC' % OM('d'), BD1)
    dvi = st([finN, nc1, kex, nne1], 'fsumdivc',
             '( sum_ d e. { x e. NN | x || N } ( K ^ %s ) / N ) = sum_ d e. { x e. NN | x || N } ( ( K ^ %s ) / N )'
             % (OM('d'), OM('d')), C1)
    key = st([st([n1, sq1], 'jca', '( N e. NN /\\ %s )' % SQ, C1), kc1, w.inst('dmkey')], 'syl2anc',
             'sum_ d e. { x e. NN | x || N } ( K ^ %s ) = ( ( K + 1 ) ^ %s )' % (OM('d'), OM('N')), C1)
    num = st([key], 'oveq1d',
             '( sum_ d e. { x e. NN | x || N } ( K ^ %s ) / N ) = ( ( ( K + 1 ) ^ %s ) / N )'
             % (OM('d'), OM('N')), C1)
    r2 = st([rhs1, dvi], 'eqtr4d', '%s = ( sum_ d e. { x e. NN | x || N } ( K ^ %s ) / N )'
            % (RHS, OM('d')), C1)
    r3 = st([r2, num], 'eqtrd', '%s = ( ( ( K + 1 ) ^ %s ) / N )' % (RHS, OM('N')), C1)
    case1 = st([lhs1, r3], 'eqtr4d', '%s = %s' % (LHS, RHS), C1)
    # case N not squarefree
    nsq = st([], 'simpr', '-. %s' % SQ, C2)
    n2 = st([], 'simplr', 'N e. NN', C2)
    lhs2 = st([nsq], 'iffalsed', '%s = 0' % LHS, C2)
    BD2 = '( %s /\\ d e. { x e. NN | x || N } )' % C2
    nsqd = st([nsq], 'adantr', '-. %s' % SQ, BD2)
    ifd2 = st([nsqd], 'iffalsed', 'if ( %s , ( ( K ^ %s ) / N ) , 0 ) = 0' % (SQ, OM('d')), BD2)
    rhs2 = st([ifd2], 'sumeq2dv', '%s = sum_ d e. { x e. NN | x || N } 0' % RHS, C2)
    finN2 = st([n2, w.inst('dvdsfi')], 'syl', '{ x e. NN | x || N } e. Fin', C2)
    orr = st([finN2], 'olcd',
             '( { x e. NN | x || N } C_ ( ZZ>= ` 1 ) \\/ { x e. NN | x || N } e. Fin )', C2)
    z = st([orr, w.inst('sumz')], 'syl', 'sum_ d e. { x e. NN | x || N } 0 = 0', C2)
    rhs3 = st([rhs2, z], 'eqtrd', '%s = 0' % RHS, C2)
    case2 = st([lhs2, rhs3], 'eqtr4d', '%s = %s' % (LHS, RHS), C2)
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s = %s )' % (AN2, LHS, RHS))
    return w


E = '( K ^ %s )' % OM('D')
FZ = '( 1 ... ( |_ ` ( Y / D ) ) )'
TM = 'if ( ( mmu ` ( D x. m ) ) =/= 0 , ( %s / ( D x. m ) ) , 0 )' % E
IFD = 'if ( ( mmu ` D ) =/= 0 , ( %s / D ) , 0 )' % E
ANI = '( ( K e. NN0 /\\ Y e. NN ) /\\ D e. ( 1 ... Y ) )'


def dminner():
    w = W('dminner', 'The inner sum bound for the divisor mean-value estimate.')
    C1 = '( %s /\\ ( mmu ` D ) =/= 0 )' % ANI
    C2 = '( %s /\\ -. ( mmu ` D ) =/= 0 )' % ANI
    BM = '( %s /\\ m e. %s )' % (C1, FZ)
    BM2 = '( %s /\\ m e. %s )' % (C2, FZ)
    SUM = 'sum_ m e. %s %s' % (FZ, TM)
    PRM = '( ( %s / D ) x. ( 1 / m ) )' % E
    HS = 'sum_ m e. %s ( 1 / m )' % FZ
    LOG = '( 1 + ( log ` Y ) )'
    def mk(ante):
        def f(hyps, ref, g):
            return w.s(hyps, ref, '( %s -> %s )' % (ante, g))
        return f
    st, s1, sm, s2, sm2 = mk(ANI), mk(C1), mk(BM), mk(C2), mk(BM2)
    k = st([], 'simpll', 'K e. NN0')
    y = st([], 'simplr', 'Y e. NN')
    dfz = st([], 'simpr', 'D e. ( 1 ... Y )')
    d = st([dfz, w.inst('elfznn')], 'syl', 'D e. NN')
    dc = st([d], 'nncnd', 'D e. CC')
    dne = st([d], 'nnne0d', 'D =/= 0')
    drp = st([d], 'nnrpd', 'D e. RR+')
    omfin = st([st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p')),
                st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), PF('D')))], 'a1i',
                   '%s = %s' % (PF('D', 'p'), PF('D')))], 'eqeltrrd', '%s e. Fin' % PF('D'))
    hcl = st([omfin, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('D'))
    en0 = st([k, hcl], 'nn0expcld', '%s e. NN0' % E)
    er = st([en0], 'nn0red', '%s e. RR' % E)
    ec = st([en0], 'nn0cnd', '%s e. CC' % E)
    e0 = st([en0], 'nn0ge0d', '0 <_ %s' % E)
    edr = st([er, drp], 'rerpdivcld', '( %s / D ) e. RR' % E)
    ed0 = st([er, drp, e0], 'divge0d', '0 <_ ( %s / D )' % E)
    fin = st([], 'fzfid', '%s e. Fin' % FZ)
    harm = st([y, dfz, w.inst('harmub')], 'syl2anc', '%s <_ %s' % (HS, LOG))
    # ---- case D squarefree
    sq = s1([], 'simpr', '( mmu ` D ) =/= 0')
    ifd1 = s1([sq], 'iftrued', '%s = ( %s / D )' % (IFD, E))
    dc1 = s1([dc], 'adantr', 'D e. CC'); dne1 = s1([dne], 'adantr', 'D =/= 0')
    ec1 = s1([ec], 'adantr', '%s e. CC' % E); er1 = s1([er], 'adantr', '%s e. RR' % E)
    e01 = s1([e0], 'adantr', '0 <_ %s' % E)
    edr1 = s1([edr], 'adantr', '( %s / D ) e. RR' % E)
    ed01 = s1([ed0], 'adantr', '0 <_ ( %s / D )' % E)
    fin1 = s1([fin], 'adantr', '%s e. Fin' % FZ)
    harm1 = s1([harm], 'adantr', '%s <_ %s' % (HS, LOG))
    # under BM
    mfz = sm([], 'simpr', 'm e. %s' % FZ)
    m = sm([mfz, w.inst('elfznn')], 'syl', 'm e. NN')
    mrp = sm([m], 'nnrpd', 'm e. RR+')
    mc = sm([m], 'nncnd', 'm e. CC')
    mne = sm([m], 'nnne0d', 'm =/= 0')
    dcm = sm([dc1], 'adantr', 'D e. CC'); dnem = sm([dne1], 'adantr', 'D =/= 0')
    ecm = sm([ec1], 'adantr', '%s e. CC' % E)
    edrm = sm([edr1], 'adantr', '( %s / D ) e. RR' % E)
    ed0m = sm([ed01], 'adantr', '0 <_ ( %s / D )' % E)
    dd = sm([ecm, dcm, dnem, mc, mne], 'divdiv1d',
            '( ( %s / D ) / m ) = ( %s / ( D x. m ) )' % (E, E))
    edc = sm([ecm, dcm, dnem], 'divcld', '( %s / D ) e. CC' % E)
    dr2 = sm([edc, mc, mne], 'divrecd', '( ( %s / D ) / m ) = %s' % (E, PRM))
    teq = sm([dd, dr2], 'eqtr3d', '( %s / ( D x. m ) ) = %s' % (E, PRM))
    recr = sm([mrp], 'rpreccld', '( 1 / m ) e. RR+')
    rec0 = sm([recr], 'rpge0d', '0 <_ ( 1 / m )')
    recre = sm([recr], 'rpred', '( 1 / m ) e. RR')
    prmre = sm([edrm, recre], 'remulcld', '%s e. RR' % PRM)
    prm0 = sm([edrm, recre, ed0m, rec0], 'mulge0d', '0 <_ %s' % PRM)
    eqle = sm([teq], 'eqled', '( %s / ( D x. m ) ) <_ %s' % (E, PRM))
    b1 = w.s([], 'breq1', '( ( %s / ( D x. m ) ) = %s -> ( ( %s / ( D x. m ) ) <_ %s <-> %s <_ %s ) )'
             % (E, TM, E, PRM, TM, PRM))
    b2 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (TM, PRM, TM, PRM))
    h3 = w.s([eqle], 'adantr', '( ( %s /\\ ( mmu ` ( D x. m ) ) =/= 0 ) -> ( %s / ( D x. m ) ) <_ %s )'
             % (BM, E, PRM))
    h4 = w.s([prm0], 'adantr', '( ( %s /\\ -. ( mmu ` ( D x. m ) ) =/= 0 ) -> 0 <_ %s )' % (BM, PRM))
    tle = sm([b1, b2, h3, h4], 'ifbothda', '%s <_ %s' % (TM, PRM))
    zre = sm([], '0red', '0 e. RR')
    d1nn = s1([d], 'adantr', 'D e. NN')
    dmnn = sm([d1nn], 'adantr', 'D e. NN')
    dmm = sm([dmnn, m], 'nnmulcld', '( D x. m ) e. NN')
    dmrp2 = sm([dmm], 'nnrpd', '( D x. m ) e. RR+')
    erm2 = sm([er1], 'adantr', '%s e. RR' % E)
    edmre = sm([erm2, dmrp2], 'rerpdivcld', '( %s / ( D x. m ) ) e. RR' % E)
    tmre = sm([edmre, zre], 'ifcld', '%s e. RR' % TM)
    sle = s1([fin1, tmre, prmre, tle], 'fsumle', '%s <_ sum_ m e. %s %s' % (SUM, FZ, PRM))
    edcc = s1([ec1, dc1, dne1], 'divcld', '( %s / D ) e. CC' % E)
    reccc = sm([recre], 'recnd', '( 1 / m ) e. CC')
    mul = s1([fin1, edcc, reccc], 'fsummulc2',
             '( ( %s / D ) x. %s ) = sum_ m e. %s %s' % (E, HS, FZ, PRM))
    hsre = s1([fin1, recre], 'fsumrecl', '%s e. RR' % HS)
    yrp = st([y], 'nnrpd', 'Y e. RR+')
    logy = st([yrp], 'relogcld', '( log ` Y ) e. RR')
    oner = st([], '1red', '1 e. RR')
    logr0 = st([oner, logy], 'readdcld', '%s e. RR' % LOG)
    logr = s1([logr0], 'adantr', '%s e. RR' % LOG)
    lem = s1([hsre, logr, edr1, ed01, harm1], 'lemul2ad',
             '( ( %s / D ) x. %s ) <_ ( ( %s / D ) x. %s )' % (E, HS, E, LOG))
    sumre = s1([fin1, tmre], 'fsumrecl', '%s e. RR' % SUM)
    prmsre = s1([fin1, prmre], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (FZ, PRM))
    edlr = s1([edr1, logr], 'remulcld', '( ( %s / D ) x. %s ) e. RR' % (E, LOG))
    mulr = s1([mul], 'eqcomd', 'sum_ m e. %s %s = ( ( %s / D ) x. %s )' % (FZ, PRM, E, HS))
    le2 = s1([mulr, lem], 'eqbrtrd', 'sum_ m e. %s %s <_ ( ( %s / D ) x. %s )' % (FZ, PRM, E, LOG))
    tot1 = s1([sumre, prmsre, edlr, sle, le2], 'letrd', '%s <_ ( ( %s / D ) x. %s )' % (SUM, E, LOG))
    rhs1 = s1([ifd1], 'oveq1d', '( %s x. %s ) = ( ( %s / D ) x. %s )' % (IFD, LOG, E, LOG))
    case1 = s1([tot1, rhs1], 'breqtrrd', '%s <_ ( %s x. %s )' % (SUM, IFD, LOG))
    # ---- case D not squarefree
    nsq = s2([], 'simpr', '-. ( mmu ` D ) =/= 0')
    d2 = s2([d], 'adantr', 'D e. NN')
    fin2 = s2([fin], 'adantr', '%s e. Fin' % FZ)
    logr2 = s2([logr0], 'adantr', '%s e. RR' % LOG)
    ifd2 = s2([nsq], 'iffalsed', '%s = 0' % IFD)
    rhs2 = s2([ifd2], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (IFD, LOG, LOG))
    logc2 = s2([logr2], 'recnd', '%s e. CC' % LOG)
    rhs2b = s2([logc2], 'mul02d', '( 0 x. %s ) = 0' % LOG)
    rhs2c = s2([rhs2, rhs2b], 'eqtrd', '( %s x. %s ) = 0' % (IFD, LOG))
    # each term is zero
    m2 = sm2([sm2([], 'simpr', 'm e. %s' % FZ), w.inst('elfznn')], 'syl', 'm e. NN')
    d2m = sm2([d2], 'adantr', 'D e. NN')
    dm = sm2([d2m, m2], 'nnmulcld', '( D x. m ) e. NN')
    dz = sm2([d2m], 'nnzd', 'D e. ZZ')
    mz = sm2([m2], 'nnzd', 'm e. ZZ')
    dvm = sm2([dz, mz, w.inst('dvdsmul1')], 'syl2anc', 'D || ( D x. m )')
    impl = sm2([dm, d2m, dvm, w.inst('dvdssqf')], 'syl3anc',
               '( ( mmu ` ( D x. m ) ) =/= 0 -> ( mmu ` D ) =/= 0 )')
    nsqm = sm2([nsq], 'adantr', '-. ( mmu ` D ) =/= 0')
    ndm = sm2([nsqm, impl], 'mtod', '-. ( mmu ` ( D x. m ) ) =/= 0')
    tz = sm2([ndm], 'iffalsed', '%s = 0' % TM)
    sz = s2([tz], 'sumeq2dv', '%s = sum_ m e. %s 0' % (SUM, FZ))
    orr = s2([fin2], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (FZ, FZ))
    z0 = s2([orr, w.inst('sumz')], 'syl', 'sum_ m e. %s 0 = 0' % FZ)
    sz2 = s2([sz, z0], 'eqtrd', '%s = 0' % SUM)
    zle = s2([s2([], '0red', '0 e. RR')], 'leidd', '0 <_ 0')
    case2a = s2([sz2, zle], 'eqbrtrd', '%s <_ 0' % SUM)
    case2 = s2([case2a, rhs2c], 'breqtrrd', '%s <_ ( %s x. %s )' % (SUM, IFD, LOG))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s <_ ( %s x. %s ) )' % (ANI, SUM, IFD, LOG))
    return w


def TRM(v, k='K'):
    return 'if ( ( mmu ` %s ) =/= 0 , ( ( %s ^ %s ) / %s ) , 0 )' % (v, k, OM(v), v)


def divmeanw0():
    w = W('divmeanw0', 'The base case of the weighted divisor mean-value estimate.')
    A = 'Y e. NN'
    SUM = 'sum_ d e. ( 1 ... Y ) %s' % TRM('d', '0')
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    y = w.s([], 'id', '( %s -> Y e. NN )' % A)
    yuz = st([st([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', 'NN = ( ZZ>= ` 1 )'), y],
             'eleqtrd', 'Y e. ( ZZ>= ` 1 )')
    one = st([yuz, w.inst('eluzfz1')], 'syl', '1 e. ( 1 ... Y )')
    sns = st([one], 'snssd', '{ 1 } C_ ( 1 ... Y )')
    fin = st([], 'fzfid', '( 1 ... Y ) e. Fin')
    # the summand is in CC on { 1 }
    BS = '( %s /\\ d e. { 1 } )' % A
    dsn = w.s([], 'simpr', '( %s -> d e. { 1 } )' % BS)
    d1 = w.s([dsn, w.inst('elsni')], 'syl', '( %s -> d = 1 )' % BS)
    dnn0 = w.s([d1, w.s([], '1nn', '1 e. NN')], 'eqeltrdi', '( %s -> d e. NN )' % BS)
    def clos(ante, dstep, v='d'):
        """( ante -> TRM( v , 0 ) e. CC ) given ( ante -> v e. NN )"""
        f = lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (ante, g))
        omf = f([f([w.s([], 'cbvrabv', '%s = %s' % (PF(v, 'p'), PF(v)))], 'a1i',
                   '%s = %s' % (PF(v, 'p'), PF(v))),
                 f([dstep, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF(v, 'p'))],
                'eqeltrrd', '%s e. Fin' % PF(v))
        h = f([omf, w.inst('hashcl')], 'syl', '%s e. NN0' % OM(v))
        zc = f([f([], '0red', '0 e. RR')], 'recnd', '0 e. CC')
        ex = f([zc, h], 'expcld', '( 0 ^ %s ) e. CC' % OM(v))
        dc = f([dstep], 'nncnd', '%s e. CC' % v)
        dn = f([dstep], 'nnne0d', '%s =/= 0' % v)
        dv = f([ex, dc, dn], 'divcld', '( ( 0 ^ %s ) / %s ) e. CC' % (OM(v), v))
        z = f([], '0cnd', '0 e. CC')
        return f([dv, z], 'ifcld', '%s e. CC' % TRM(v, '0'))
    cl1 = clos(BS, dnn0)
    # the summand vanishes off { 1 }
    BD = '( %s /\\ d e. ( ( 1 ... Y ) \\ { 1 } ) )' % A
    fd = lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (BD, g))
    ddif = fd([], 'simpr', 'd e. ( ( 1 ... Y ) \\ { 1 } )')
    dfz = fd([ddif, w.inst('eldifi')], 'syl', 'd e. ( 1 ... Y )')
    dnn = fd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    dne = fd([ddif, w.inst('eldifsni')], 'syl', 'd =/= 1')
    duz = fd([fd([dnn, dne], 'jca', '( d e. NN /\\ d =/= 1 )'),
              fd([w.s([], 'eluz2b3', '( d e. ( ZZ>= ` 2 ) <-> ( d e. NN /\\ d =/= 1 ) )')], 'a1i',
                 '( d e. ( ZZ>= ` 2 ) <-> ( d e. NN /\\ d =/= 1 ) )')], 'mpbird',
             'd e. ( ZZ>= ` 2 )')
    ex = fd([duz, w.inst('exprmfct')], 'syl', 'E. p e. Prime p || d')
    rab0 = fd([w.s([], 'rabn0', '( %s =/= (/) <-> E. p e. Prime p || d )' % PF('d', 'p'))], 'a1i',
              '( %s =/= (/) <-> E. p e. Prime p || d )' % PF('d', 'p'))
    ne0p = fd([rab0, ex], 'mpbird', '%s =/= (/)' % PF('d', 'p'))
    cbv = fd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
             '%s = %s' % (PF('d', 'p'), PF('d')))
    cbvr = fd([cbv], 'eqcomd', '%s = %s' % (PF('d'), PF('d', 'p')))
    ne0 = fd([cbvr, ne0p], 'eqnetrd', '%s =/= (/)' % PF('d'))
    omfin = fd([cbv, fd([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
               'eqeltrrd', '%s e. Fin' % PF('d'))
    hne = fd([fd([omfin, w.inst('hashneq0')], 'syl',
                 '( 0 < %s <-> %s =/= (/) )' % (OM('d'), PF('d'))), ne0], 'mpbird',
             '0 < %s' % OM('d'))
    hcl = fd([omfin, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    hnn = fd([fd([hcl, hne], 'jca', '( %s e. NN0 /\\ 0 < %s )' % (OM('d'), OM('d'))),
              fd([w.s([], 'elnnnn0b', '( %s e. NN <-> ( %s e. NN0 /\\ 0 < %s ) )' % (OM('d'), OM('d'), OM('d')))],
                 'a1i', '( %s e. NN <-> ( %s e. NN0 /\\ 0 < %s ) )' % (OM('d'), OM('d'), OM('d')))],
             'mpbird', '%s e. NN' % OM('d'))
    zex = fd([hnn, w.inst('0exp')], 'syl', '( 0 ^ %s ) = 0' % OM('d'))
    dvz = fd([zex], 'oveq1d', '( ( 0 ^ %s ) / d ) = ( 0 / d )' % OM('d'))
    dvz2 = fd([fd([dnn], 'nncnd', 'd e. CC'), fd([dnn], 'nnne0d', 'd =/= 0')], 'div0d',
              '( 0 / d ) = 0')
    dvz3 = fd([dvz, dvz2], 'eqtrd', '( ( 0 ^ %s ) / d ) = 0' % OM('d'))
    ifz = fd([dvz3], 'ifeq1d', '%s = if ( ( mmu ` d ) =/= 0 , 0 , 0 )' % TRM('d', '0'))
    ifz2 = fd([w.s([], 'ifid', 'if ( ( mmu ` d ) =/= 0 , 0 , 0 ) = 0')], 'a1i',
              'if ( ( mmu ` d ) =/= 0 , 0 , 0 ) = 0')
    vanish = fd([ifz, ifz2], 'eqtrd', '%s = 0' % TRM('d', '0'))
    ss = st([sns, cl1, vanish, fin], 'fsumss',
            'sum_ d e. { 1 } %s = %s' % (TRM('d', '0'), SUM))
    # the value at 1
    sub1 = w.s([], 'fveq2', '( d = 1 -> ( mmu ` d ) = ( mmu ` 1 ) )')
    sub2 = w.s([sub1], 'neeq1d', '( d = 1 -> ( ( mmu ` d ) =/= 0 <-> ( mmu ` 1 ) =/= 0 ) )')
    sub3 = w.s([], 'breq2', '( d = 1 -> ( q || d <-> q || 1 ) )')
    sub4 = w.s([sub3], 'rabbidv', '( d = 1 -> %s = %s )' % (PF('d'), PF('1')))
    sub5 = w.s([sub4], 'fveq2d', '( d = 1 -> %s = %s )' % (OM('d'), OM('1')))
    sub6 = w.s([sub5], 'oveq2d', '( d = 1 -> ( 0 ^ %s ) = ( 0 ^ %s ) )' % (OM('d'), OM('1')))
    sub7 = w.s([], 'id', '( d = 1 -> d = 1 )')
    sub8 = w.s([sub6, sub7], 'oveq12d',
               '( d = 1 -> ( ( 0 ^ %s ) / d ) = ( ( 0 ^ %s ) / 1 ) )' % (OM('d'), OM('1')))
    sub = w.s([sub2, sub8], 'ifbieq1d',
              '( d = 1 -> %s = %s )' % (TRM('d', '0'), TRM('1', '0')))
    onev = w.s([], '1ex', '1 e. _V')
    # the value at 1 is in CC
    n1 = w.s([], '1nn', '1 e. NN')
    n1a = st([n1], 'a1i', '1 e. NN')
    cl0 = clos(A, n1a, '1')
    sni = w.s([sub], 'sumsn',
              '( ( 1 e. _V /\\ %s e. CC ) -> sum_ d e. { 1 } %s = %s )'
              % (TRM('1', '0'), TRM('d', '0'), TRM('1', '0')))
    snval = st([st([onev], 'a1i', '1 e. _V'), cl0, sni], 'syl2anc',
               'sum_ d e. { 1 } %s = %s' % (TRM('d', '0'), TRM('1', '0')))
    # evaluate the value at 1
    sq1 = st([w.s([], 'sqf1', '( mmu ` 1 ) =/= 0')], 'a1i', '( mmu ` 1 ) =/= 0')
    ift = st([sq1], 'iftrued', '%s = ( ( 0 ^ %s ) / 1 )' % (TRM('1', '0'), OM('1')))
    rgen = w.s([w.s([], 'nprmdvds1', '( q e. Prime -> -. q || 1 )')], 'rgen',
               'A. q e. Prime -. q || 1')
    rab = w.s([w.s([], 'rabeq0', '( %s = (/) <-> A. q e. Prime -. q || 1 )' % PF('1')), rgen],
              'mpbir', '%s = (/)' % PF('1'))
    h1 = w.s([rab], 'fveq2i', '%s = ( # ` (/) )' % OM('1'))
    h2 = w.s([h1, w.s([], 'hash0', '( # ` (/) ) = 0')], 'eqtri', '%s = 0' % OM('1'))
    e1 = w.s([h2], 'oveq2i', '( 0 ^ %s ) = ( 0 ^ 0 )' % OM('1'))
    e2 = w.s([e1, w.s([], '0exp0e1', '( 0 ^ 0 ) = 1')], 'eqtri', '( 0 ^ %s ) = 1' % OM('1'))
    e3 = w.s([e2], 'oveq1i', '( ( 0 ^ %s ) / 1 ) = ( 1 / 1 )' % OM('1'))
    e4 = w.s([e3, w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'eqtri', '( ( 0 ^ %s ) / 1 ) = 1' % OM('1'))
    val = st([ift, st([e4], 'a1i', '( ( 0 ^ %s ) / 1 ) = 1' % OM('1'))], 'eqtrd',
             '%s = 1' % TRM('1', '0'))
    tot = st([snval, val], 'eqtrd', 'sum_ d e. { 1 } %s = 1' % TRM('d', '0'))
    w.qed([ss, tot], 'eqtr3d', '( %s -> %s = 1 )' % (A, SUM))
    return w


def divmeanw1():
    w = W('divmeanw1', 'The induction step of the weighted divisor mean-value estimate.')
    LOG = '( 1 + ( log ` Y ) )'
    FY = '( 1 ... ( |_ ` Y ) )'
    FZd = '( 1 ... ( |_ ` ( Y / d ) ) )'
    IB = 'if ( ( mmu ` n ) =/= 0 , ( ( K ^ %s ) / n ) , 0 )' % OM('d')
    IC = 'if ( ( mmu ` ( d x. m ) ) =/= 0 , ( ( K ^ %s ) / ( d x. m ) ) , 0 )' % OM('d')
    S0 = 'sum_ n e. ( 1 ... Y ) %s' % TRM('n', '( K + 1 )')
    S1 = 'sum_ n e. ( 1 ... Y ) sum_ d e. { x e. NN | x || n } %s' % IB
    S1F = 'sum_ n e. %s sum_ d e. { x e. NN | x || n } %s' % (FY, IB)
    S2F = 'sum_ d e. %s sum_ m e. %s %s' % (FY, FZd, IC)
    S2 = 'sum_ d e. ( 1 ... Y ) sum_ m e. %s %s' % (FZd, IC)
    S3 = 'sum_ d e. ( 1 ... Y ) ( %s x. %s )' % (TRM('d'), LOG)
    SK = 'sum_ d e. ( 1 ... Y ) %s' % TRM('d')
    IH = '%s <_ ( %s ^ K )' % (SK, LOG)
    AN0 = '( K e. NN0 /\\ Y e. NN )'
    ANT = '( %s /\\ %s )' % (AN0, IH)
    def mk(ante):
        return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (ante, g))
    st = mk(AN0)
    k = st([], 'simpl', 'K e. NN0')
    y = st([], 'simpr', 'Y e. NN')
    yz = st([y], 'nnzd', 'Y e. ZZ')
    yr = st([y], 'nnred', 'Y e. RR')
    yrp = st([y], 'nnrpd', 'Y e. RR+')
    fl = st([yz, w.inst('flid')], 'syl', '( |_ ` Y ) = Y')
    fzeq = st([fl], 'oveq2d', '%s = ( 1 ... Y )' % FY)
    fin = st([], 'fzfid', '( 1 ... Y ) e. Fin')
    logy = st([yrp], 'relogcld', '( log ` Y ) e. RR')
    oner = st([], '1red', '1 e. RR')
    logr = st([oner, logy], 'readdcld', '%s e. RR' % LOG)
    y1 = st([y, w.inst('nnge1')], 'syl', '1 <_ Y')
    log0 = st([yr, y1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` Y )')
    z1 = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    log00 = st([oner, logy, z1, log0], 'addge0d', '0 <_ %s' % LOG)
    # ( 1 ) the termwise divisor expansion
    BN = '( %s /\\ n e. ( 1 ... Y ) )' % AN0
    fn = mk(BN)
    nnn = fn([fn([], 'simpr', 'n e. ( 1 ... Y )'), w.inst('elfznn')], 'syl', 'n e. NN')
    trm = fn([fn([k], 'adantr', 'K e. NN0'), nnn, w.inst('dmterm')], 'syl2anc',
             '%s = sum_ d e. { x e. NN | x || n } %s' % (TRM('n', '( K + 1 )'), IB))
    e1 = st([trm], 'sumeq2dv', '%s = %s' % (S0, S1))
    # ( 2 ) the double-sum swap
    sub1 = w.s([], 'neeq1d' if False else 'fveq2', '( n = ( d x. m ) -> ( mmu ` n ) = ( mmu ` ( d x. m ) ) )')
    sub2 = w.s([sub1], 'neeq1d', '( n = ( d x. m ) -> ( ( mmu ` n ) =/= 0 <-> ( mmu ` ( d x. m ) ) =/= 0 ) )')
    sub3 = w.s([], 'id', '( n = ( d x. m ) -> n = ( d x. m ) )')
    sub4 = w.s([sub3], 'oveq2d',
               '( n = ( d x. m ) -> ( ( K ^ %s ) / n ) = ( ( K ^ %s ) / ( d x. m ) ) )' % (OM('d'), OM('d')))
    sub = w.s([sub2, sub4], 'ifbieq1d', '( n = ( d x. m ) -> %s = %s )' % (IB, IC))
    # closure of IB for n e. FY and d | n
    BND = '( %s /\\ ( n e. %s /\\ d e. { x e. NN | x || n } ) )' % (AN0, FY)
    fnd = mk(BND)
    pr = fnd([], 'simpr', '( n e. %s /\\ d e. { x e. NN | x || n } )' % FY)
    nfz2 = fnd([pr], 'simpld', 'n e. %s' % FY)
    dvs = fnd([pr], 'simprd', 'd e. { x e. NN | x || n }')
    nnn2 = fnd([nfz2, w.inst('elfznn')], 'syl', 'n e. NN')
    dnn2 = fnd([dvs, w.inst('elrabi')], 'syl', 'd e. NN')
    omf2 = fnd([fnd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                    '%s = %s' % (PF('d', 'p'), PF('d'))),
                fnd([dnn2, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
               'eqeltrrd', '%s e. Fin' % PF('d'))
    hcl2 = fnd([omf2, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    kc2 = fnd([fnd([k], 'adantr', 'K e. NN0')], 'nn0cnd', 'K e. CC')
    ex2 = fnd([kc2, hcl2], 'expcld', '( K ^ %s ) e. CC' % OM('d'))
    nc2 = fnd([nnn2], 'nncnd', 'n e. CC')
    nne2 = fnd([nnn2], 'nnne0d', 'n =/= 0')
    dv2 = fnd([ex2, nc2, nne2], 'divcld', '( ( K ^ %s ) / n ) e. CC' % OM('d'))
    z2 = fnd([], '0cnd', '0 e. CC')
    ifcc = fnd([dv2, z2], 'ifcld', '%s e. CC' % IB)
    swap = st([sub, yr, ifcc], 'dvdsflsumcom', '%s = %s' % (S1F, S2F))
    e2a = st([fzeq], 'sumeq1d', '%s = %s' % (S1F, S1))
    e2b = st([fzeq], 'sumeq1d', '%s = %s' % (S2F, S2))
    e2 = st([st([e2a], 'eqcomd', '%s = %s' % (S1, S1F)), st([swap, e2b], 'eqtrd', '%s = %s' % (S1F, S2))],
            'eqtrd', '%s = %s' % (S1, S2))
    e3 = st([e1, e2], 'eqtrd', '%s = %s' % (S0, S2))
    # ( 3 ) the inner bound and the sum
    BD = '( %s /\\ d e. ( 1 ... Y ) )' % AN0
    fd = mk(BD)
    dfz = fd([], 'simpr', 'd e. ( 1 ... Y )')
    dnn = fd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    inner = fd([fd([fd([k], 'adantr', 'K e. NN0'), fd([y], 'adantr', 'Y e. NN')], 'jca', AN0), dfz,
                w.inst('dminner')], 'syl2anc',
               'sum_ m e. %s %s <_ ( %s x. %s )' % (FZd, IC, TRM('d'), LOG))
    # closures for fsumle
    omf3 = fd([fd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                  '%s = %s' % (PF('d', 'p'), PF('d'))),
               fd([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
              'eqeltrrd', '%s e. Fin' % PF('d'))
    hcl3 = fd([omf3, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    kn3 = fd([k], 'adantr', 'K e. NN0')
    en3 = fd([kn3, hcl3], 'nn0expcld', '( K ^ %s ) e. NN0' % OM('d'))
    er3 = fd([en3], 'nn0red', '( K ^ %s ) e. RR' % OM('d'))
    drp3 = fd([dnn], 'nnrpd', 'd e. RR+')
    edr3 = fd([er3, drp3], 'rerpdivcld', '( ( K ^ %s ) / d ) e. RR' % OM('d'))
    zr3 = fd([], '0red', '0 e. RR')
    ifr3 = fd([edr3, zr3], 'ifcld', '%s e. RR' % TRM('d'))
    logr3 = fd([logr], 'adantr', '%s e. RR' % LOG)
    prr3 = fd([ifr3, logr3], 'remulcld', '( %s x. %s ) e. RR' % (TRM('d'), LOG))
    fin3 = fd([], 'fzfid', '%s e. Fin' % FZd)
    BDM = '( %s /\\ m e. %s )' % (BD, FZd)
    fdm = mk(BDM)
    mnn = fdm([fdm([], 'simpr', 'm e. %s' % FZd), w.inst('elfznn')], 'syl', 'm e. NN')
    dnnm = fdm([dnn], 'adantr', 'd e. NN')
    dmm = fdm([dnnm, mnn], 'nnmulcld', '( d x. m ) e. NN')
    dmrp = fdm([dmm], 'nnrpd', '( d x. m ) e. RR+')
    erm3 = fdm([er3], 'adantr', '( K ^ %s ) e. RR' % OM('d'))
    edmr = fdm([erm3, dmrp], 'rerpdivcld', '( ( K ^ %s ) / ( d x. m ) ) e. RR' % OM('d'))
    zrm = fdm([], '0red', '0 e. RR')
    icr = fdm([edmr, zrm], 'ifcld', '%s e. RR' % IC)
    insre = fd([fin3, icr], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (FZd, IC))
    sle = st([fin, insre, prr3, inner], 'fsumle', '%s <_ %s' % (S2, S3))
    # ( 4 ) factor out and use the induction hypothesis
    logc0 = st([logr], 'recnd', '%s e. CC' % LOG)
    ifc3 = fd([ifr3], 'recnd', '%s e. CC' % TRM('d'))
    mulc = st([fin, logc0, ifc3], 'fsummulc1', '( %s x. %s ) = %s' % (SK, LOG, S3))
    skre = st([fin, ifr3], 'fsumrecl', '%s e. RR' % SK)
    kexr = st([logr, k], 'reexpcld', '( %s ^ K ) e. RR' % LOG)
    sk = mk(ANT)
    ihh = sk([], 'simpr', IH)
    skreA = sk([skre], 'adantr', '%s e. RR' % SK)
    kexrA = sk([kexr], 'adantr', '( %s ^ K ) e. RR' % LOG)
    logrA = sk([logr], 'adantr', '%s e. RR' % LOG)
    log00A = sk([log00], 'adantr', '0 <_ %s' % LOG)
    lem = sk([skreA, kexrA, logrA, log00A, ihh], 'lemul1ad',
             '( %s x. %s ) <_ ( ( %s ^ K ) x. %s )' % (SK, LOG, LOG, LOG))
    logc = sk([logrA], 'recnd', '%s e. CC' % LOG)
    kA = sk([k], 'adantr', 'K e. NN0')
    p1 = sk([logc, kA, w.inst('expp1')], 'syl2anc',
            '( %s ^ ( K + 1 ) ) = ( ( %s ^ K ) x. %s )' % (LOG, LOG, LOG))
    mulcA = sk([mulc], 'adantr', '( %s x. %s ) = %s' % (SK, LOG, S3))
    le3 = sk([sk([mulcA], 'eqcomd', '%s = ( %s x. %s )' % (S3, SK, LOG)), lem], 'eqbrtrd',
             '%s <_ ( ( %s ^ K ) x. %s )' % (S3, LOG, LOG))
    le4 = sk([le3, sk([p1], 'eqcomd', '( ( %s ^ K ) x. %s ) = ( %s ^ ( K + 1 ) )' % (LOG, LOG, LOG))],
             'breqtrd', '%s <_ ( %s ^ ( K + 1 ) )' % (S3, LOG))
    s2re = st([fin, insre], 'fsumrecl', '%s e. RR' % S2)
    s3re = st([fin, prr3], 'fsumrecl', '%s e. RR' % S3)
    k1n = st([k, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')
    kexr1 = st([logr, k1n], 'reexpcld', '( %s ^ ( K + 1 ) ) e. RR' % LOG)
    s2reA = sk([s2re], 'adantr', '%s e. RR' % S2)
    s3reA = sk([s3re], 'adantr', '%s e. RR' % S3)
    kexr1A = sk([kexr1], 'adantr', '( %s ^ ( K + 1 ) ) e. RR' % LOG)
    sleA = sk([sle], 'adantr', '%s <_ %s' % (S2, S3))
    e3A = sk([e3], 'adantr', '%s = %s' % (S0, S2))
    tot = sk([s2reA, s3reA, kexr1A, sleA, le4], 'letrd', '%s <_ ( %s ^ ( K + 1 ) )' % (S2, LOG))
    fin2 = sk([e3A, tot], 'eqbrtrd', '%s <_ ( %s ^ ( K + 1 ) )' % (S0, LOG))
    w.qed([fin2], 'ex', '( %s -> ( %s -> %s <_ ( %s ^ ( K + 1 ) ) ) )' % (AN0, IH, S0, LOG))
    return w


def divmeanw():
    w = W('divmeanw',
          'The weighted divisor mean-value estimate: the sum of K to the number of prime factors '
          'divided by d, over the squarefree d up to Y, is at most ( 1 + log Y ) to the K.')
    LOG = '( 1 + ( log ` Y ) )'
    def PHI(X):
        return ('( Y e. NN -> sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ %s ) )'
                % (TRM('d', X), LOG, X))
    def subst(X):
        e = 'k = %s' % X
        a = w.s([], 'oveq1', '( %s -> ( k ^ %s ) = ( %s ^ %s ) )' % (e, OM('d'), X, OM('d')))
        b = w.s([a], 'oveq1d', '( %s -> ( ( k ^ %s ) / d ) = ( ( %s ^ %s ) / d ) )'
                % (e, OM('d'), X, OM('d')))
        c = w.s([b], 'ifeq1d', '( %s -> %s = %s )' % (e, TRM('d', 'k'), TRM('d', X)))
        d_ = w.s([c], 'sumeq2sdv', '( %s -> sum_ d e. ( 1 ... Y ) %s = sum_ d e. ( 1 ... Y ) %s )'
                 % (e, TRM('d', 'k'), TRM('d', X)))
        f = w.s([], 'oveq2', '( %s -> ( %s ^ k ) = ( %s ^ %s ) )' % (e, LOG, LOG, X))
        g = w.s([d_, f], 'breq12d',
                '( %s -> ( sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ k ) <-> sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ %s ) ) )'
                % (e, TRM('d', 'k'), LOG, TRM('d', X), LOG, X))
        return w.s([g], 'imbi2d', '( %s -> ( %s <-> %s ) )' % (e, PHI('k'), PHI(X)))
    h1 = subst('0')
    h2 = subst('j')
    h3 = subst('( j + 1 )')
    h4 = subst('K')
    # base case
    A = 'Y e. NN'
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (A, f))
    yrp = st([w.s([], 'id', '( %s -> Y e. NN )' % A)], 'nnrpd', 'Y e. RR+')
    logy = st([yrp], 'relogcld', '( log ` Y ) e. RR')
    oner = st([], '1red', '1 e. RR')
    logr = st([oner, logy], 'readdcld', '%s e. RR' % LOG)
    logc = st([logr], 'recnd', '%s e. CC' % LOG)
    e0 = st([logc, w.inst('exp0')], 'syl', '( %s ^ 0 ) = 1' % LOG)
    sum0 = st([], 'divmeanw0', 'sum_ d e. ( 1 ... Y ) %s = 1' % TRM('d', '0'))
    oneq = st([oner], 'leidd', '1 <_ 1')
    b1 = st([sum0, oneq], 'eqbrtrd', 'sum_ d e. ( 1 ... Y ) %s <_ 1' % TRM('d', '0'))
    b2 = st([b1, e0], 'breqtrrd', 'sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ 0 )' % (TRM('d', '0'), LOG))
    h5 = w.s([b2], 'idi', PHI('0'))
    # the step
    x1n = w.s([], 'divmeanw1',
              '( ( j e. NN0 /\\ Y e. NN ) -> ( sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ j ) -> '
              'sum_ n e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) ) )'
              % (TRM('d', 'j'), LOG, TRM('n', '( j + 1 )'), LOG))
    ca = w.s([], 'fveq2', '( n = d -> ( mmu ` n ) = ( mmu ` d ) )')
    cb = w.s([ca], 'neeq1d', '( n = d -> ( ( mmu ` n ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )')
    cc = w.s([], 'breq2', '( n = d -> ( q || n <-> q || d ) )')
    cd = w.s([cc], 'rabbidv', '( n = d -> %s = %s )' % (PF('n'), PF('d')))
    ce = w.s([cd], 'fveq2d', '( n = d -> %s = %s )' % (OM('n'), OM('d')))
    cf = w.s([ce], 'oveq2d',
             '( n = d -> ( ( j + 1 ) ^ %s ) = ( ( j + 1 ) ^ %s ) )' % (OM('n'), OM('d')))
    cid = w.s([], 'id', '( n = d -> n = d )')
    cg = w.s([cf, cid], 'oveq12d',
             '( n = d -> ( ( ( j + 1 ) ^ %s ) / n ) = ( ( ( j + 1 ) ^ %s ) / d ) )'
             % (OM('n'), OM('d')))
    ch = w.s([cb, cg], 'ifbieq1d', '( n = d -> %s = %s )'
             % (TRM('n', '( j + 1 )'), TRM('d', '( j + 1 )')))
    cbs = w.s([ch], 'cbvsumv', 'sum_ n e. ( 1 ... Y ) %s = sum_ d e. ( 1 ... Y ) %s'
              % (TRM('n', '( j + 1 )'), TRM('d', '( j + 1 )')))
    cbi = w.s([cbs], 'breq1i',
              '( sum_ n e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) <-> sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) )'
              % (TRM('n', '( j + 1 )'), LOG, TRM('d', '( j + 1 )'), LOG))
    cbia = w.s([cbi], 'a1i',
               '( ( j e. NN0 /\\ Y e. NN ) -> ( sum_ n e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) <-> '
               'sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) ) )'
               % (TRM('n', '( j + 1 )'), LOG, TRM('d', '( j + 1 )'), LOG))
    x1 = w.s([x1n, cbia], 'sylibd',
             '( ( j e. NN0 /\\ Y e. NN ) -> ( sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ j ) -> '
             'sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) ) )'
             % (TRM('d', 'j'), LOG, TRM('d', '( j + 1 )'), LOG))
    x2 = w.s([x1], 'ex',
             '( j e. NN0 -> ( Y e. NN -> ( sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ j ) -> '
             'sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ ( j + 1 ) ) ) ) )'
             % (TRM('d', 'j'), LOG, TRM('d', '( j + 1 )'), LOG))
    h6 = w.s([x2], 'a2d', '( j e. NN0 -> ( %s -> %s ) )' % (PHI('j'), PHI('( j + 1 )')))
    res = w.s([h1, h2, h3, h4, h5, h6], 'nn0ind', '( K e. NN0 -> %s )' % PHI('K'))
    w.qed([res], 'imp',
          '( ( K e. NN0 /\\ Y e. NN ) -> sum_ d e. ( 1 ... Y ) %s <_ ( %s ^ K ) )'
          % (TRM('d', 'K'), LOG))
    return w


def TRU(v, k='K'):
    return 'if ( ( mmu ` %s ) =/= 0 , ( %s ^ %s ) , 0 )' % (v, k, OM(v))


def dmterm2():
    w = W('dmterm2', 'The divisor expansion of the unweighted ( K + 1 ) -st power weight at N.')
    AN2 = '( K e. NN0 /\\ N e. NN )'
    SQ = '( mmu ` N ) =/= 0'
    LHS = TRU('N', '( K + 1 )')
    RHS = 'sum_ d e. { x e. NN | x || N } if ( %s , ( K ^ %s ) , 0 )' % (SQ, OM('d'))
    C1 = '( %s /\\ %s )' % (AN2, SQ)
    C2 = '( %s /\\ -. %s )' % (AN2, SQ)
    def mk(a):
        return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))
    st, s1, s2 = mk(AN2), mk(C1), mk(C2)
    k1 = s1([], 'simpll', 'K e. NN0')
    n1 = s1([], 'simplr', 'N e. NN')
    sq1 = s1([], 'simpr', SQ)
    kc1 = s1([k1], 'nn0cnd', 'K e. CC')
    lhs1 = s1([sq1], 'iftrued', '%s = ( ( K + 1 ) ^ %s )' % (LHS, OM('N')))
    BD1 = '( %s /\\ d e. { x e. NN | x || N } )' % C1
    f1 = mk(BD1)
    ifd = f1([f1([sq1], 'adantr', SQ)], 'iftrued',
             'if ( %s , ( K ^ %s ) , 0 ) = ( K ^ %s )' % (SQ, OM('d'), OM('d')))
    rhs1 = s1([ifd], 'sumeq2dv', '%s = sum_ d e. { x e. NN | x || N } ( K ^ %s )' % (RHS, OM('d')))
    key = s1([s1([n1, sq1], 'jca', '( N e. NN /\\ %s )' % SQ), kc1, w.inst('dmkey')], 'syl2anc',
             'sum_ d e. { x e. NN | x || N } ( K ^ %s ) = ( ( K + 1 ) ^ %s )' % (OM('d'), OM('N')))
    r2 = s1([rhs1, key], 'eqtrd', '%s = ( ( K + 1 ) ^ %s )' % (RHS, OM('N')))
    case1 = s1([lhs1, r2], 'eqtr4d', '%s = %s' % (LHS, RHS))
    nsq = s2([], 'simpr', '-. %s' % SQ)
    n2 = s2([], 'simplr', 'N e. NN')
    lhs2 = s2([nsq], 'iffalsed', '%s = 0' % LHS)
    BD2 = '( %s /\\ d e. { x e. NN | x || N } )' % C2
    f2 = mk(BD2)
    ifd2 = f2([f2([nsq], 'adantr', '-. %s' % SQ)], 'iffalsed',
              'if ( %s , ( K ^ %s ) , 0 ) = 0' % (SQ, OM('d')))
    rhs2 = s2([ifd2], 'sumeq2dv', '%s = sum_ d e. { x e. NN | x || N } 0' % RHS)
    finN2 = s2([n2, w.inst('dvdsfi')], 'syl', '{ x e. NN | x || N } e. Fin')
    orr = s2([finN2], 'olcd',
             '( { x e. NN | x || N } C_ ( ZZ>= ` 1 ) \\/ { x e. NN | x || N } e. Fin )')
    z = s2([orr, w.inst('sumz')], 'syl', 'sum_ d e. { x e. NN | x || N } 0 = 0')
    rhs3 = s2([rhs2, z], 'eqtrd', '%s = 0' % RHS)
    case2 = s2([lhs2, rhs3], 'eqtr4d', '%s = %s' % (LHS, RHS))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s = %s )' % (AN2, LHS, RHS))
    return w


def dminner2():
    w = W('dminner2', 'The inner sum bound for the unweighted divisor mean-value estimate.')
    EE = '( K ^ %s )' % OM('D')
    FZ2 = '( 1 ... ( |_ ` ( Y / D ) ) )'
    TM2 = 'if ( ( mmu ` ( D x. m ) ) =/= 0 , %s , 0 )' % EE
    IFD2 = 'if ( ( mmu ` D ) =/= 0 , ( %s / D ) , 0 )' % EE
    SUM = 'sum_ m e. %s %s' % (FZ2, TM2)
    AN = '( ( K e. NN0 /\\ Y e. NN ) /\\ D e. ( 1 ... Y ) )'
    C1 = '( %s /\\ ( mmu ` D ) =/= 0 )' % AN
    C2 = '( %s /\\ -. ( mmu ` D ) =/= 0 )' % AN
    BM = '( %s /\\ m e. %s )' % (C1, FZ2)
    BM2 = '( %s /\\ m e. %s )' % (C2, FZ2)
    def mk(a):
        return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))
    st, s1, sm, s2, sm2 = mk(AN), mk(C1), mk(BM), mk(C2), mk(BM2)
    k = st([], 'simpll', 'K e. NN0')
    y = st([], 'simplr', 'Y e. NN')
    dfz = st([], 'simpr', 'D e. ( 1 ... Y )')
    d = st([dfz, w.inst('elfznn')], 'syl', 'D e. NN')
    yr = st([y], 'nnred', 'Y e. RR')
    yc = st([y], 'nncnd', 'Y e. CC')
    dle = st([dfz, w.inst('elfzle2')], 'syl', 'D <_ Y')
    omfin = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), PF('D')))], 'a1i',
                   '%s = %s' % (PF('D', 'p'), PF('D'))),
                st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))],
               'eqeltrrd', '%s e. Fin' % PF('D'))
    hcl = st([omfin, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('D'))
    en0 = st([k, hcl], 'nn0expcld', '%s e. NN0' % EE)
    er = st([en0], 'nn0red', '%s e. RR' % EE)
    ec = st([en0], 'nn0cnd', '%s e. CC' % EE)
    e0 = st([en0], 'nn0ge0d', '0 <_ %s' % EE)
    # ---- case D squarefree
    sq = s1([], 'simpr', '( mmu ` D ) =/= 0')
    ifd1 = s1([sq], 'iftrued', '%s = ( %s / D )' % (IFD2, EE))
    d1 = s1([d], 'adantr', 'D e. NN')
    er1 = s1([er], 'adantr', '%s e. RR' % EE)
    ec1 = s1([ec], 'adantr', '%s e. CC' % EE)
    e01 = s1([e0], 'adantr', '0 <_ %s' % EE)
    yr1 = s1([yr], 'adantr', 'Y e. RR')
    yc1 = s1([yc], 'adantr', 'Y e. CC')
    dle1 = s1([dle], 'adantr', 'D <_ Y')
    fl = s1([], 'fzfid', '%s e. Fin' % FZ2)
    # termwise: TM2 <_ EE
    b1 = w.s([], 'breq1', '( %s = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (EE, TM2, EE, EE, TM2, EE))
    b2 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (TM2, EE, TM2, EE))
    erm = sm([er1], 'adantr', '%s e. RR' % EE)
    e0m = sm([e01], 'adantr', '0 <_ %s' % EE)
    h3 = w.s([sm([erm], 'leidd', '%s <_ %s' % (EE, EE))], 'adantr',
             '( ( %s /\\ ( mmu ` ( D x. m ) ) =/= 0 ) -> %s <_ %s )' % (BM, EE, EE))
    h4 = w.s([e0m], 'adantr', '( ( %s /\\ -. ( mmu ` ( D x. m ) ) =/= 0 ) -> 0 <_ %s )' % (BM, EE))
    tle = sm([b1, b2, h3, h4], 'ifbothda', '%s <_ %s' % (TM2, EE))
    zrm = sm([], '0red', '0 e. RR')
    tmre = sm([erm, zrm], 'ifcld', '%s e. RR' % TM2)
    sle = s1([fl, tmre, erm, tle], 'fsumle', '%s <_ sum_ m e. %s %s' % (SUM, FZ2, EE))
    cst = s1([fl, ec1, w.inst('fsumconst')], 'syl2anc',
             'sum_ m e. %s %s = ( ( # ` %s ) x. %s )' % (FZ2, EE, FZ2, EE))
    # ( # ` FZ2 ) = ( |_ ` ( Y / D ) ) <_ ( Y / D )
    drp1 = s1([d1], 'nnrpd', 'D e. RR+')
    ydr = s1([yr1, drp1], 'rerpdivcld', '( Y / D ) e. RR')
    ynn1 = s1([y], 'adantr', 'Y e. NN')
    y01 = s1([ynn1], 'nnge0d' if False else 'nnrpd', 'Y e. RR+')
    yd0b = s1([y01, drp1], 'rpdivcld', '( Y / D ) e. RR+')
    ydge0 = s1([yd0b], 'rpge0d', '0 <_ ( Y / D )')
    flnn0 = s1([ydr, ydge0, w.inst('flge0nn0')], 'syl2anc', '( |_ ` ( Y / D ) ) e. NN0')
    hfz = s1([flnn0, w.inst('hashfz1')], 'syl', '( # ` %s ) = ( |_ ` ( Y / D ) )' % FZ2)
    cst2 = s1([cst, s1([hfz], 'oveq1d',
              '( ( # ` %s ) x. %s ) = ( ( |_ ` ( Y / D ) ) x. %s )' % (FZ2, EE, EE))], 'eqtrd',
              'sum_ m e. %s %s = ( ( |_ ` ( Y / D ) ) x. %s )' % (FZ2, EE, EE))
    flr = s1([flnn0], 'nn0red', '( |_ ` ( Y / D ) ) e. RR')
    flle1 = s1([ydr, w.inst('flle')], 'syl', '( |_ ` ( Y / D ) ) <_ ( Y / D )')
    lem = s1([flr, ydr, er1, e01, flle1], 'lemul1ad',
             '( ( |_ ` ( Y / D ) ) x. %s ) <_ ( ( Y / D ) x. %s )' % (EE, EE))
    dc1 = s1([d1], 'nncnd', 'D e. CC')
    dne1 = s1([d1], 'nnne0d', 'D =/= 0')
    a23 = s1([yc1, ec1, dc1, dne1], 'div23d',
             '( ( Y x. %s ) / D ) = ( ( Y / D ) x. %s )' % (EE, EE))
    aas = s1([yc1, ec1, dc1, dne1], 'divassd',
             '( ( Y x. %s ) / D ) = ( Y x. ( %s / D ) )' % (EE, EE))
    ident = s1([a23, aas], 'eqtr3d', '( ( Y / D ) x. %s ) = ( Y x. ( %s / D ) )' % (EE, EE))
    rhs1 = s1([ifd1], 'oveq2d', '( Y x. %s ) = ( Y x. ( %s / D ) )' % (IFD2, EE))
    sumre = s1([fl, tmre], 'fsumrecl', '%s e. RR' % SUM)
    csre = s1([fl, erm], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (FZ2, EE))
    ydere = s1([ydr, er1], 'remulcld', '( ( Y / D ) x. %s ) e. RR' % EE)
    le1 = s1([cst2, lem], 'eqbrtrd', 'sum_ m e. %s %s <_ ( ( Y / D ) x. %s )' % (FZ2, EE, EE))
    tot = s1([sumre, csre, ydere, sle, le1], 'letrd', '%s <_ ( ( Y / D ) x. %s )' % (SUM, EE))
    tot2 = s1([tot, ident], 'breqtrd', '%s <_ ( Y x. ( %s / D ) )' % (SUM, EE))
    case1 = s1([tot2, rhs1], 'breqtrrd', '%s <_ ( Y x. %s )' % (SUM, IFD2))
    # ---- case D not squarefree
    nsq = s2([], 'simpr', '-. ( mmu ` D ) =/= 0')
    d2 = s2([d], 'adantr', 'D e. NN')
    yc2 = s2([yc], 'adantr', 'Y e. CC')
    fl2 = s2([], 'fzfid', '%s e. Fin' % FZ2)
    ifd2 = s2([nsq], 'iffalsed', '%s = 0' % IFD2)
    rhs2 = s2([ifd2], 'oveq2d', '( Y x. %s ) = ( Y x. 0 )' % IFD2)
    rhs2b = s2([yc2], 'mul01d', '( Y x. 0 ) = 0')
    rhs2c = s2([rhs2, rhs2b], 'eqtrd', '( Y x. %s ) = 0' % IFD2)
    m2 = sm2([sm2([], 'simpr', 'm e. %s' % FZ2), w.inst('elfznn')], 'syl', 'm e. NN')
    d2m = sm2([d2], 'adantr', 'D e. NN')
    dmm = sm2([d2m, m2], 'nnmulcld', '( D x. m ) e. NN')
    dz = sm2([d2m], 'nnzd', 'D e. ZZ')
    mz = sm2([m2], 'nnzd', 'm e. ZZ')
    dvm = sm2([dz, mz, w.inst('dvdsmul1')], 'syl2anc', 'D || ( D x. m )')
    impl = sm2([dmm, d2m, dvm, w.inst('dvdssqf')], 'syl3anc',
               '( ( mmu ` ( D x. m ) ) =/= 0 -> ( mmu ` D ) =/= 0 )')
    nsqm = sm2([nsq], 'adantr', '-. ( mmu ` D ) =/= 0')
    ndm = sm2([nsqm, impl], 'mtod', '-. ( mmu ` ( D x. m ) ) =/= 0')
    tz = sm2([ndm], 'iffalsed', '%s = 0' % TM2)
    sz = s2([tz], 'sumeq2dv', '%s = sum_ m e. %s 0' % (SUM, FZ2))
    orr = s2([fl2], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (FZ2, FZ2))
    z0 = s2([orr, w.inst('sumz')], 'syl', 'sum_ m e. %s 0 = 0' % FZ2)
    sz2 = s2([sz, z0], 'eqtrd', '%s = 0' % SUM)
    zle = s2([s2([], '0red', '0 e. RR')], 'leidd', '0 <_ 0')
    case2a = s2([sz2, zle], 'eqbrtrd', '%s <_ 0' % SUM)
    case2 = s2([case2a, rhs2c], 'breqtrrd', '%s <_ ( Y x. %s )' % (SUM, IFD2))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s <_ ( Y x. %s ) )' % (AN, SUM, IFD2))
    return w


def divmean1():
    w = W('divmean1', 'The unweighted divisor mean-value estimate at exponent K + 1.')
    LOG = '( 1 + ( log ` Y ) )'
    FY = '( 1 ... ( |_ ` Y ) )'
    FZd = '( 1 ... ( |_ ` ( Y / d ) ) )'
    IB = 'if ( ( mmu ` n ) =/= 0 , ( K ^ %s ) , 0 )' % OM('d')
    IC = 'if ( ( mmu ` ( d x. m ) ) =/= 0 , ( K ^ %s ) , 0 )' % OM('d')
    S0 = 'sum_ n e. ( 1 ... Y ) %s' % TRU('n', '( K + 1 )')
    S1 = 'sum_ n e. ( 1 ... Y ) sum_ d e. { x e. NN | x || n } %s' % IB
    S1F = 'sum_ n e. %s sum_ d e. { x e. NN | x || n } %s' % (FY, IB)
    S2F = 'sum_ d e. %s sum_ m e. %s %s' % (FY, FZd, IC)
    S2 = 'sum_ d e. ( 1 ... Y ) sum_ m e. %s %s' % (FZd, IC)
    S3 = 'sum_ d e. ( 1 ... Y ) ( Y x. %s )' % TRM('d')
    SK = 'sum_ d e. ( 1 ... Y ) %s' % TRM('d')
    AN0 = '( K e. NN0 /\\ Y e. NN )'
    def mk(a):
        return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))
    st = mk(AN0)
    k = st([], 'simpl', 'K e. NN0')
    y = st([], 'simpr', 'Y e. NN')
    yz = st([y], 'nnzd', 'Y e. ZZ')
    yr = st([y], 'nnred', 'Y e. RR')
    yc = st([y], 'nncnd', 'Y e. CC')
    y0 = st([st([y], 'nnrpd', 'Y e. RR+')], 'rpge0d', '0 <_ Y')
    fl = st([yz, w.inst('flid')], 'syl', '( |_ ` Y ) = Y')
    fzeq = st([fl], 'oveq2d', '%s = ( 1 ... Y )' % FY)
    fin = st([], 'fzfid', '( 1 ... Y ) e. Fin')
    yrp = st([y], 'nnrpd', 'Y e. RR+')
    logy = st([yrp], 'relogcld', '( log ` Y ) e. RR')
    oner = st([], '1red', '1 e. RR')
    logr = st([oner, logy], 'readdcld', '%s e. RR' % LOG)
    # ( 1 ) termwise
    BN = '( %s /\\ n e. ( 1 ... Y ) )' % AN0
    fn = mk(BN)
    nnn = fn([fn([], 'simpr', 'n e. ( 1 ... Y )'), w.inst('elfznn')], 'syl', 'n e. NN')
    trm = fn([fn([k], 'adantr', 'K e. NN0'), nnn, w.inst('dmterm2')], 'syl2anc',
             '%s = sum_ d e. { x e. NN | x || n } %s' % (TRU('n', '( K + 1 )'), IB))
    e1 = st([trm], 'sumeq2dv', '%s = %s' % (S0, S1))
    # ( 2 ) swap
    sub1 = w.s([], 'fveq2', '( n = ( d x. m ) -> ( mmu ` n ) = ( mmu ` ( d x. m ) ) )')
    sub2 = w.s([sub1], 'neeq1d',
               '( n = ( d x. m ) -> ( ( mmu ` n ) =/= 0 <-> ( mmu ` ( d x. m ) ) =/= 0 ) )')
    sub = w.s([sub2], 'ifbid', '( n = ( d x. m ) -> %s = %s )' % (IB, IC))
    BND = '( %s /\\ ( n e. %s /\\ d e. { x e. NN | x || n } ) )' % (AN0, FY)
    fnd = mk(BND)
    pr = fnd([], 'simpr', '( n e. %s /\\ d e. { x e. NN | x || n } )' % FY)
    dvs = fnd([pr], 'simprd', 'd e. { x e. NN | x || n }')
    dnn2 = fnd([dvs, w.inst('elrabi')], 'syl', 'd e. NN')
    omf2 = fnd([fnd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                    '%s = %s' % (PF('d', 'p'), PF('d'))),
                fnd([dnn2, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
               'eqeltrrd', '%s e. Fin' % PF('d'))
    hcl2 = fnd([omf2, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    kc2 = fnd([fnd([k], 'adantr', 'K e. NN0')], 'nn0cnd', 'K e. CC')
    ex2 = fnd([kc2, hcl2], 'expcld', '( K ^ %s ) e. CC' % OM('d'))
    z2 = fnd([], '0cnd', '0 e. CC')
    ifcc = fnd([ex2, z2], 'ifcld', '%s e. CC' % IB)
    swap = st([sub, yr, ifcc], 'dvdsflsumcom', '%s = %s' % (S1F, S2F))
    e2a = st([fzeq], 'sumeq1d', '%s = %s' % (S1F, S1))
    e2b = st([fzeq], 'sumeq1d', '%s = %s' % (S2F, S2))
    e2 = st([st([e2a], 'eqcomd', '%s = %s' % (S1, S1F)),
             st([swap, e2b], 'eqtrd', '%s = %s' % (S1F, S2))], 'eqtrd', '%s = %s' % (S1, S2))
    e3 = st([e1, e2], 'eqtrd', '%s = %s' % (S0, S2))
    # ( 3 ) the inner bound
    BD = '( %s /\\ d e. ( 1 ... Y ) )' % AN0
    fd = mk(BD)
    dfz = fd([], 'simpr', 'd e. ( 1 ... Y )')
    dnn = fd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    inner = fd([fd([fd([k], 'adantr', 'K e. NN0'), fd([y], 'adantr', 'Y e. NN')], 'jca', AN0), dfz,
                w.inst('dminner2')], 'syl2anc',
               'sum_ m e. %s %s <_ ( Y x. %s )' % (FZd, IC, TRM('d')))
    omf3 = fd([fd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                  '%s = %s' % (PF('d', 'p'), PF('d'))),
               fd([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
              'eqeltrrd', '%s e. Fin' % PF('d'))
    hcl3 = fd([omf3, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    en3 = fd([fd([k], 'adantr', 'K e. NN0'), hcl3], 'nn0expcld', '( K ^ %s ) e. NN0' % OM('d'))
    er3 = fd([en3], 'nn0red', '( K ^ %s ) e. RR' % OM('d'))
    drp3 = fd([dnn], 'nnrpd', 'd e. RR+')
    edr3 = fd([er3, drp3], 'rerpdivcld', '( ( K ^ %s ) / d ) e. RR' % OM('d'))
    zr3 = fd([], '0red', '0 e. RR')
    ifr3 = fd([edr3, zr3], 'ifcld', '%s e. RR' % TRM('d'))
    yr3 = fd([yr], 'adantr', 'Y e. RR')
    prr3 = fd([yr3, ifr3], 'remulcld', '( Y x. %s ) e. RR' % TRM('d'))
    fin3 = fd([], 'fzfid', '%s e. Fin' % FZd)
    BDM = '( %s /\\ m e. %s )' % (BD, FZd)
    fdm = mk(BDM)
    icr = fdm([fdm([er3], 'adantr', '( K ^ %s ) e. RR' % OM('d')),
               fdm([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IC)
    insre = fd([fin3, icr], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (FZd, IC))
    sle = st([fin, insre, prr3, inner], 'fsumle', '%s <_ %s' % (S2, S3))
    # ( 4 ) factor Y out and apply divmeanw
    ifc3 = fd([ifr3], 'recnd', '%s e. CC' % TRM('d'))
    mulc = st([fin, yc, ifc3], 'fsummulc2', '( Y x. %s ) = %s' % (SK, S3))
    skre = st([fin, ifr3], 'fsumrecl', '%s e. RR' % SK)
    kexr = st([logr, k], 'reexpcld', '( %s ^ K ) e. RR' % LOG)
    dmw = st([], 'divmeanw', '%s <_ ( %s ^ K )' % (SK, LOG))
    lem = st([skre, kexr, yr, y0, dmw], 'lemul2ad',
             '( Y x. %s ) <_ ( Y x. ( %s ^ K ) )' % (SK, LOG))
    le3 = st([st([mulc], 'eqcomd', '%s = ( Y x. %s )' % (S3, SK)), lem], 'eqbrtrd',
             '%s <_ ( Y x. ( %s ^ K ) )' % (S3, LOG))
    s2re = st([fin, insre], 'fsumrecl', '%s e. RR' % S2)
    s3re = st([fin, prr3], 'fsumrecl', '%s e. RR' % S3)
    ykre = st([yr, kexr], 'remulcld', '( Y x. ( %s ^ K ) ) e. RR' % LOG)
    tot = st([s2re, s3re, ykre, sle, le3], 'letrd', '%s <_ ( Y x. ( %s ^ K ) )' % (S2, LOG))
    w.qed([e3, tot], 'eqbrtrd', '( %s -> %s <_ ( Y x. ( %s ^ K ) ) )' % (AN0, S0, LOG))
    return w


def divmean():
    w = W('divmean',
          'The unweighted divisor mean-value estimate: the sum of K to the number of prime '
          'factors over the squarefree d up to Y is at most Y x. ( 1 + log Y ) to the K - 1.')
    LOG = '( 1 + ( log ` Y ) )'
    AN = '( K e. NN /\\ Y e. NN )'
    K1 = '( K - 1 )'
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (AN, f))
    k = st([], 'simpl', 'K e. NN')
    y = st([], 'simpr', 'Y e. NN')
    k1n = st([k, w.inst('nnm1nn0')], 'syl', '%s e. NN0' % K1)
    d1 = st([k1n, y, w.inst('divmean1')], 'syl2anc',
            'sum_ n e. ( 1 ... Y ) %s <_ ( Y x. ( %s ^ %s ) )' % (TRU('n', '( %s + 1 )' % K1), LOG, K1))
    kc = st([k], 'nncnd', 'K e. CC')
    onec = st([], '1cnd', '1 e. CC')
    np = st([kc, onec, w.inst('npcan')], 'syl2anc', '( %s + 1 ) = K' % K1)
    ex = st([np], 'oveq1d', '( ( %s + 1 ) ^ %s ) = ( K ^ %s )' % (K1, OM('n'), OM('n')))
    ife = st([ex], 'ifeq1d', '%s = %s' % (TRU('n', '( %s + 1 )' % K1), TRU('n', 'K')))
    se = st([ife], 'sumeq2sdv', 'sum_ n e. ( 1 ... Y ) %s = sum_ n e. ( 1 ... Y ) %s'
            % (TRU('n', '( %s + 1 )' % K1), TRU('n', 'K')))
    d2 = st([st([se], 'eqcomd', 'sum_ n e. ( 1 ... Y ) %s = sum_ n e. ( 1 ... Y ) %s'
                % (TRU('n', 'K'), TRU('n', '( %s + 1 )' % K1))), d1], 'eqbrtrd',
            'sum_ n e. ( 1 ... Y ) %s <_ ( Y x. ( %s ^ %s ) )' % (TRU('n', 'K'), LOG, K1))
    # rename the summation variable
    ca = w.s([], 'fveq2', '( n = d -> ( mmu ` n ) = ( mmu ` d ) )')
    cb = w.s([ca], 'neeq1d', '( n = d -> ( ( mmu ` n ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )')
    cc = w.s([], 'breq2', '( n = d -> ( q || n <-> q || d ) )')
    cd = w.s([cc], 'rabbidv', '( n = d -> %s = %s )' % (PF('n'), PF('d')))
    ce = w.s([cd], 'fveq2d', '( n = d -> %s = %s )' % (OM('n'), OM('d')))
    cf = w.s([ce], 'oveq2d', '( n = d -> ( K ^ %s ) = ( K ^ %s ) )' % (OM('n'), OM('d')))
    ch = w.s([cb, cf], 'ifbieq1d', '( n = d -> %s = %s )' % (TRU('n', 'K'), TRU('d', 'K')))
    cbs = w.s([ch], 'cbvsumv', 'sum_ n e. ( 1 ... Y ) %s = sum_ d e. ( 1 ... Y ) %s'
              % (TRU('n', 'K'), TRU('d', 'K')))
    cbsa = st([cbs], 'a1i', 'sum_ n e. ( 1 ... Y ) %s = sum_ d e. ( 1 ... Y ) %s'
              % (TRU('n', 'K'), TRU('d', 'K')))
    cbsr = st([cbsa], 'eqcomd', 'sum_ d e. ( 1 ... Y ) %s = sum_ n e. ( 1 ... Y ) %s'
              % (TRU('d', 'K'), TRU('n', 'K')))
    w.qed([cbsr, d2], 'eqbrtrd',
          '( %s -> sum_ d e. ( 1 ... Y ) %s <_ ( Y x. ( %s ^ %s ) ) )' % (AN, TRU('d', 'K'), LOG, K1))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['dmkey']:
        globals()[f]().run()
