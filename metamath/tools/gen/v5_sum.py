"""Sortie V5: the sum over the cofactors (smshsum) and the bound of the bad
primes by half of ppi (smshpi).  MM_DB=sorties/v5.mm python3 tools/gen/v5_sum.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from lin import linarith
from cl import lift
import num
import a5lib
import v5lib
from v5lib import mkst, lit, Proj, subst, csubst, HALF, E3

only = sys.argv[1:]
SBX = v5lib.SB('X', 'E')
MX = v5lib.MM('X', 'E')
L = '( log ` X )'
AX = '( X ^c ( 1 - E ) )'
XE = '( X ^c E )'
KX = v5lib.K('C', 'X', L)
TWINCT = v5lib.TWIN('C', 'T')
SQX = '( sqrt ` X )'


def run(w):
    if only and w.label not in only:
        return True
    ok = w.run()
    assert ok, w.label
    return ok


# ------------------------------------------------------------------ smshsum
def smshsum():
    w = W('smshsum', 'Summing the twin-type bounds over the cofactors: the number of bad primes up to X is at most '
                     '16 C X / ( log X ) ^ 2 times e^3 ( 1 + log |_ X ^c E _| ) (Lean: hterm, hbadR of smooth_shifted_weak).')
    A = v5lib.PH5
    st = mkst(w, A); pj = Proj(w, A)
    B0 = '( ( C e. RR /\\ 0 <_ C ) /\\ ( X e. NN /\\ E e. RR ) /\\ 4 <_ %s )' % L
    cre, c0 = pj('C e. RR'), pj('0 <_ C'); xnn, ere = pj('X e. NN'), pj('E e. RR'); l4 = pj('4 <_ %s' % L)
    tnn, twin = pj('T e. NN'), pj(TWINCT); e0, eh = pj('0 < E'), pj('E <_ %s' % HALF); t2s = pj('( T + 2 ) <_ %s' % SQX)
    RNG = '( 1 ... %s )' % MX
    xre = st([xnn], 'nnred', 'X e. RR'); xrp = st([xnn], 'nnrpd', 'X e. RR+'); x1 = st([xnn], 'nnge1d', '1 <_ X')
    x0 = st([xrp], 'rpge0d', '0 <_ X'); xcn = st([xre], 'recnd', 'X e. CC')
    xere = st([xre, x0, ere], 'recxpcld', '%s e. RR' % XE)
    Mz = st([xere], 'flcld', '%s e. ZZ' % MX); Mre = st([Mz], 'zred', '%s e. RR' % MX)
    # M e. NN
    one_xe = st([st([st([xcn], 'cxp0d', '( X ^c 0 ) = 1')], 'eqcomd', '1 = ( X ^c 0 )'),
                 st([xre, x1, st([], '0red', '0 e. RR'), ere, st([st([], '0red', '0 e. RR'), ere, e0], 'ltled', '0 <_ E')], 'cxplead',
                    '( X ^c 0 ) <_ %s' % XE)], 'eqbrtrd', '1 <_ %s' % XE)
    M1 = st([one_xe, st([xere, st([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('flge')], 'syl2anc',
                        '( 1 <_ %s <-> 1 <_ %s )' % (XE, MX))], 'mpbid', '1 <_ %s' % MX)
    Mnn = st([Mz, M1, w.s([], 'elnnz1', '( %s e. NN <-> ( %s e. ZZ /\\ 1 <_ %s ) )' % (MX, MX, MX))], 'sylanbrc', '%s e. NN' % MX)
    # ---- per cofactor j
    AJ = '( %s /\\ j e. %s )' % (A, RNG)
    sj = mkst(w, AJ)
    lj = lambda s: lift(w, s, AJ)
    jnn = sj([sj([], 'simpr', 'j e. %s' % RNG), w.inst('elfznn')], 'syl', 'j e. NN')
    jre = sj([jnn], 'nnred', 'j e. RR'); jrp = sj([jnn], 'nnrpd', 'j e. RR+'); jz = sj([jnn], 'nnzd', 'j e. ZZ')
    jM = sj([sj([], 'simpr', 'j e. %s' % RNG), w.inst('elfzle2')], 'syl', 'j <_ %s' % MX)
    jxe = sj([jre, lj(Mre), lj(xere), jM, sj([lj(xere), w.inst('flle')], 'syl', '%s <_ %s' % (MX, XE))], 'letrd', 'j <_ %s' % XE)
    sqre = sj([lj(xre), lj(x0)], 'resqrtcld', '%s e. RR' % SQX)
    half = lit(w, AJ, HALF, 'RR')
    xeh = sj([lj(xre), lj(x1), lj(ere), half, lj(eh)], 'cxplead', '%s <_ ( X ^c %s )' % (XE, HALF))
    cxs = sj([lj(xcn), w.inst('cxpsqrt')], 'syl', '( X ^c %s ) = %s' % (HALF, SQX))
    xes = sj([xeh, cxs], 'breqtrd', '%s <_ %s' % (XE, SQX))
    jsq = sj([jre, lj(xere), sqre, jxe, xes], 'letrd', 'j <_ %s' % SQX)
    tre = sj([lj(tnn)], 'nnred', 'T e. RR'); t0 = sj([lj(tnn)], 'nnge1d', '1 <_ T')
    tge0 = sj([sj([], '0red', '0 e. RR'), lit(w, AJ, '1', 'RR'), tre, lit(w, AJ, '1', 'ge0'), t0], 'letrd', '0 <_ T')
    t2re = sj([tre, lit(w, AJ, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    tsq = sj([tre, t2re, sqre, sj([tre, sj([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')], 'ltaddrpd', 'T < ( T + 2 )'), lj(t2s)],
             'ltletrd', 'T < %s' % SQX)
    tsq = sj([tre, sqre, tsq], 'ltled', 'T <_ %s' % SQX)
    twosq = sj([lit(w, AJ, '2', 'RR'), t2re, sqre, sj([lit(w, AJ, '2', 'RR'), sj([lj(tnn)], 'nnrpd', 'T e. RR+')], 'ltaddrp2d', '2 < ( T + 2 )'), lj(t2s)],
               'ltletrd', '2 < %s' % SQX)
    twosq = sj([lit(w, AJ, '2', 'RR'), sqre, twosq], 'ltled', '2 <_ %s' % SQX)
    tj = sj([tre, sqre, jre, sqre, tge0, sj([jrp], 'rpge0d', '0 <_ j'), tsq, jsq], 'lemul12ad', '( T x. j ) <_ ( %s x. %s )' % (SQX, SQX))
    sqsq = sj([lj(xre), lj(x0), w.inst('remsqsqrt')], 'syl2anc', '( %s x. %s ) = X' % (SQX, SQX))
    tjx = sj([tj, sqsq], 'breqtrd', '( T x. j ) <_ X')
    XJ = '( X / j )'
    txj = sj([tjx, sj([tre, lj(xre), jrp], 'lemuldivd', '( ( T x. j ) <_ X <-> T <_ %s )' % XJ)], 'mpbid', 'T <_ %s' % XJ)
    xjre = sj([lj(xre), jrp], 'rerpdivcld', '%s e. RR' % XJ)
    Z = v5lib.FL('X', 'j')
    tz = sj([txj, sj([xjre, sj([lj(tnn)], 'nnzd', 'T e. ZZ'), w.inst('flge')], 'syl2anc', '( T <_ %s <-> T <_ %s )' % (XJ, Z))], 'mpbid', 'T <_ %s' % Z)
    zz = sj([xjre], 'flcld', '%s e. ZZ' % Z); zre = sj([zz], 'zred', '%s e. RR' % Z)
    zuz = sj([sj([lj(tnn)], 'nnzd', 'T e. ZZ'), zz, tz, w.s([], 'eluz2', '( %s e. ( ZZ>= ` T ) <-> ( T e. ZZ /\\ %s e. ZZ /\\ T <_ %s ) )' % (Z, Z, Z))],
             'syl3anbrc', '%s e. ( ZZ>= ` T )' % Z)
    z1 = sj([lit(w, AJ, '1', 'RR'), tre, zre, t0, tz], 'letrd', '1 <_ %s' % Z)
    znn = sj([zz, z1, w.s([], 'elnnz1', '( %s e. NN <-> ( %s e. ZZ /\\ 1 <_ %s ) )' % (Z, Z, Z))], 'sylanbrc', '%s e. NN' % Z)
    zrp = sj([znn], 'nnrpd', '%s e. RR+' % Z); z0 = sj([zrp], 'rpge0d', '0 <_ %s' % Z)
    zxj = sj([xjre, w.inst('flle')], 'syl', '%s <_ %s' % (Z, XJ))
    # AX / 2 <_ Z
    ome = sj([lit(w, AJ, '1', 'RR'), lj(ere)], 'resubcld', '( 1 - E ) e. RR')
    axrp = sj([lj(xrp), ome], 'rpcxpcld', '%s e. RR+' % AX); axre = sj([axrp], 'rpred', '%s e. RR' % AX)
    axj = sj([jre, lj(xere), axre, sj([axrp], 'rpge0d', '0 <_ %s' % AX), jxe], 'lemul2ad', '( %s x. j ) <_ ( %s x. %s )' % (AX, AX, XE))
    ecn = sj([lj(ere)], 'recnd', 'E e. CC'); onecn = sj([], '1cnd', '1 e. CC')
    xsp = sj([lj(xcn), sj([lj(xrp)], 'rpne0d', 'X =/= 0'), sj([ome], 'recnd', '( 1 - E ) e. CC'), ecn], 'cxpaddd',
             '( X ^c ( ( 1 - E ) + E ) ) = ( %s x. %s )' % (AX, XE))
    e1 = sj([sj([onecn, ecn], 'npcand', '( ( 1 - E ) + E ) = 1')], 'oveq2d', '( X ^c ( ( 1 - E ) + E ) ) = ( X ^c 1 )')
    xeq = sj([sj([e1, sj([lj(xcn)], 'cxp1d', '( X ^c 1 ) = X')], 'eqtrd', '( X ^c ( ( 1 - E ) + E ) ) = X'), xsp], 'eqtr3d',
             'X = ( %s x. %s )' % (AX, XE))
    axjx = sj([axj, sj([xeq], 'eqcomd', '( %s x. %s ) = X' % (AX, XE))], 'breqtrd', '( %s x. j ) <_ X' % AX)
    axxj = sj([axjx, sj([axre, lj(xre), jrp], 'lemuldivd', '( ( %s x. j ) <_ X <-> %s <_ %s )' % (AX, AX, XJ))], 'mpbid', '%s <_ %s' % (AX, XJ))
    xjz1 = sj([xjre, w.inst('flltp1')], 'syl', '%s < ( %s + 1 )' % (XJ, Z))
    hehe = sj([lj(eh), sj([w.s([], '1mhlfehlf', '( 1 - %s ) = %s' % (HALF, HALF))], 'a1i', '( 1 - %s ) = %s' % (HALF, HALF))], 'breqtrrd',
              'E <_ ( 1 - %s )' % HALF)
    hle = sj([lj(ere), lit(w, AJ, '1', 'RR'), half, hehe], 'lesubd', '%s <_ ( 1 - E )' % HALF)
    sqax = sj([sj([lj(xre), lj(x1), half, ome, hle], 'cxplead', '( X ^c %s ) <_ %s' % (HALF, AX)), cxs], 'eqbrtrrd',
              '%s <_ %s' % (SQX, AX))
    twoax = sj([lit(w, AJ, '2', 'RR'), sqre, axre, twosq, sqax], 'letrd', '2 <_ %s' % AX)
    ax2z = linarith(w, AJ, [axxj, xjz1, twoax], '( %s / 2 ) <_ %s' % (AX, Z), leaves={AX: axre, XJ: xjre, Z: zre})
    # log Z
    LZ = '( log ` %s )' % Z
    lzre = sj([zrp], 'relogcld', '%s e. RR' % LZ)
    lre = sj([lj(xrp)], 'relogcld', '%s e. RR' % L)
    lgz = sj([sj([sj([lj(xrp), lj(l4)], 'jca', '( X e. RR+ /\\ 4 <_ %s )' % L), sj([lj(ere), lj(eh)], 'jca', '( E e. RR /\\ E <_ %s )' % HALF),
                  sj([zre, ax2z], 'jca', '( %s e. RR /\\ ( %s / 2 ) <_ %s )' % (Z, AX, Z))], '3jca',
                 '( ( X e. RR+ /\\ 4 <_ %s ) /\\ ( E e. RR /\\ E <_ %s ) /\\ ( %s e. RR /\\ ( %s / 2 ) <_ %s ) )' % (L, HALF, Z, AX, Z)),
              w.inst('smshlog')], 'syl', '( %s / 4 ) <_ %s' % (L, LZ))
    l0 = sj([sj([], '0red', '0 e. RR'), lit(w, AJ, '4', 'RR'), lre, lit(w, AJ, '4', 'gt0'), lj(l4)], 'ltletrd', '0 < %s' % L)
    # the twin instance
    R = v5lib.RQ('j')
    jphi = sj([jre, sj([jnn, w.inst('phicl')], 'syl', '( phi ` j ) e. NN')], 'nndivred', '( j / ( phi ` j ) ) e. RR')
    rre = sj([jphi], 'resqcld', '%s e. RR' % R); r0 = sj([jphi], 'sqge0d', '0 <_ %s' % R)
    TWJZ = v5lib.TW('j', Z)
    tw, twtext = a5lib.unwind(w, AJ, lj(twin), TWINCT, [('q', 'n', 'NN', 'j', jnn), ('q', 'z', '( ZZ>= ` T )', Z, zuz)])
    MID = '( ( ( C x. %s ) x. %s ) / ( %s ^ 2 ) )' % (R, Z, LZ)
    assert twtext == '( # ` %s ) <_ %s' % (TWJZ, MID), twtext
    dv = sj([sj([sj([sj([sj([lj(cre), lj(c0)], 'jca', '( C e. RR /\\ 0 <_ C )'), sj([rre, r0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (R, R))], 'jca',
                         '( ( C e. RR /\\ 0 <_ C ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (R, R)),
                     sj([sj([jre, sj([jrp], 'rpgt0d', '0 < j')], 'jca', '( j e. RR /\\ 0 < j )'), sj([lj(xre), lj(x0)], 'jca', '( X e. RR /\\ 0 <_ X )')], 'jca',
                        '( ( j e. RR /\\ 0 < j ) /\\ ( X e. RR /\\ 0 <_ X ) )'),
                     sj([sj([lre, l0], 'jca', '( %s e. RR /\\ 0 < %s )' % (L, L)), sj([lzre, lgz], 'jca', '( %s e. RR /\\ ( %s / 4 ) <_ %s )' % (LZ, L, LZ))], 'jca',
                        '( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ ( %s / 4 ) <_ %s ) )' % (L, L, LZ, L, LZ))], '3jca',
                    '( ( ( C e. RR /\\ 0 <_ C ) /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ ( ( j e. RR /\\ 0 < j ) /\\ ( X e. RR /\\ 0 <_ X ) ) /\\ ( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ ( %s / 4 ) <_ %s ) ) )'
                    % (R, R, L, L, LZ, L, LZ)),
                 sj([zre, z0, zxj], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ %s )' % (Z, Z, Z, XJ))], 'jca',
                '( ( ( ( C e. RR /\\ 0 <_ C ) /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ ( ( j e. RR /\\ 0 < j ) /\\ ( X e. RR /\\ 0 <_ X ) ) /\\ ( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ ( %s / 4 ) <_ %s ) ) ) /\\ ( %s e. RR /\\ 0 <_ %s /\\ %s <_ %s ) )'
                % (R, R, L, L, LZ, L, LZ, Z, Z, Z, XJ)), w.inst('smshdiv')], 'syl', '%s <_ ( %s x. ( %s / j ) )' % (MID, KX, R))
    twfin = sj([sj([], 'fzfid', '( 1 ... %s ) e. Fin' % Z), w.inst('rabfi')], 'syl', '%s e. Fin' % TWJZ)
    twre = sj([sj([twfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TWJZ)], 'nn0red', '( # ` %s ) e. RR' % TWJZ)
    lz0 = sj([sj([], '0red', '0 e. RR'), sj([lre, lit(w, AJ, '4', 'RR+')], 'rerpdivcld', '( %s / 4 ) e. RR' % L), lzre,
              sj([sj([sj([lre, l0], 'elrpd', '%s e. RR+' % L), lit(w, AJ, '4', 'RR+')], 'rpdivcld', '( %s / 4 ) e. RR+' % L)], 'rpgt0d', '0 < ( %s / 4 )' % L), lgz], 'ltletrd', '0 < %s' % LZ)
    midre = sj([sj([sj([lj(cre), rre], 'remulcld', '( C x. %s ) e. RR' % R), zre], 'remulcld', '( ( C x. %s ) x. %s ) e. RR' % (R, Z)),
                sj([sj([lzre, lz0], 'elrpd', '%s e. RR+' % LZ), sj([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % LZ)],
               'rerpdivcld', '%s e. RR' % MID)
    # K
    l2rp = st([st([st([xrp], 'relogcld', '%s e. RR' % L), st([st([], '0red', '0 e. RR'), lit(w, A, '4', 'RR'), st([xrp], 'relogcld', '%s e. RR' % L), lit(w, A, '4', 'gt0'), l4], 'ltletrd', '0 < %s' % L)], 'elrpd', '%s e. RR+' % L),
                st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % L)
    num16 = st([lit(w, A, '; 1 6', 'RR'), st([cre, xre], 'remulcld', '( C x. X ) e. RR')], 'remulcld', '( ; 1 6 x. ( C x. X ) ) e. RR')
    kre = st([num16, l2rp], 'rerpdivcld', '%s e. RR' % KX)
    k0 = st([num16, l2rp, st([lit(w, A, '; 1 6', 'RR'), st([cre, xre], 'remulcld', '( C x. X ) e. RR'), lit(w, A, '; 1 6', 'ge0'), st([cre, xre, c0, x0], 'mulge0d', '0 <_ ( C x. X )')], 'mulge0d',
                            '0 <_ ( ; 1 6 x. ( C x. X ) )')], 'divge0d', '0 <_ %s' % KX)
    rjre = sj([rre, jnn], 'nndivred', '( %s / j ) e. RR' % R)
    krj = sj([lj(kre), rjre], 'remulcld', '( %s x. ( %s / j ) ) e. RR' % (KX, R))
    term = sj([twre, midre, krj, tw, dv], 'letrd', '( # ` %s ) <_ ( %s x. ( %s / j ) )' % (TWJZ, KX, R))
    # the sums
    rfin = st([], 'fzfid', '%s e. Fin' % RNG)
    SUM1 = v5lib.SUMTW('X', 'E')
    SUM2 = 'sum_ j e. %s ( %s x. ( %s / j ) )' % (RNG, KX, R)
    SUM3 = 'sum_ j e. %s ( %s / j )' % (RNG, R)
    fle = st([rfin, twre, krj, term], 'fsumle', '%s <_ %s' % (SUM1, SUM2))
    # fsummulc2 under the TWIN-free conjunct B0
    sb = mkst(w, B0); pb = Proj(w, B0)
    BJ = '( %s /\\ j e. %s )' % (B0, RNG)
    sbj = mkst(w, BJ)
    bxnn = pb('X e. NN'); bxrp = sb([bxnn], 'nnrpd', 'X e. RR+'); bxre = sb([bxnn], 'nnred', 'X e. RR')
    blre = sb([bxrp], 'relogcld', '%s e. RR' % L)
    bl0 = sb([sb([], '0red', '0 e. RR'), lit(w, B0, '4', 'RR'), blre, lit(w, B0, '4', 'gt0'), pb('4 <_ %s' % L)], 'ltletrd', '0 < %s' % L)
    bl2 = sb([sb([blre, bl0], 'elrpd', '%s e. RR+' % L), sb([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % L)
    bk = sb([sb([lit(w, B0, '; 1 6', 'RR'), sb([pb('C e. RR'), bxre], 'remulcld', '( C x. X ) e. RR')], 'remulcld', '( ; 1 6 x. ( C x. X ) ) e. RR'), bl2],
            'rerpdivcld', '%s e. RR' % KX)
    bkcn = sb([bk], 'recnd', '%s e. CC' % KX)
    bjnn = sbj([sbj([], 'simpr', 'j e. %s' % RNG), w.inst('elfznn')], 'syl', 'j e. NN')
    bjre = sbj([bjnn], 'nnred', 'j e. RR')
    brj = sbj([sbj([sbj([bjre, sbj([bjnn, w.inst('phicl')], 'syl', '( phi ` j ) e. NN')], 'nndivred', '( j / ( phi ` j ) ) e. RR')], 'resqcld', '%s e. RR' % R), bjnn],
              'nndivred', '( %s / j ) e. RR' % R)
    bmul = sb([sb([], 'fzfid', '%s e. Fin' % RNG), bkcn, sbj([brj], 'recnd', '( %s / j ) e. CC' % R)], 'fsummulc2',
              '( %s x. %s ) = %s' % (KX, SUM3, SUM2))
    mul = lift(w, bmul, A)
    # totsumsq at M, renamed to j
    tsq = st([Mnn, w.inst('totsumsq')], 'syl', 'sum_ m e. %s ( %s / m ) <_ ( %s x. ( 1 + ( log ` %s ) ) )' % (RNG, v5lib.RQ('m'), E3, MX))
    cs, _ = csubst(w, 'm', 'j', '( %s / m )' % v5lib.RQ('m'))
    cbv = w.s([cs], 'cbvsumv', 'sum_ m e. %s ( %s / m ) = %s' % (RNG, v5lib.RQ('m'), SUM3))
    tsq2 = st([st([cbv], 'a1i', 'sum_ m e. %s ( %s / m ) = %s' % (RNG, v5lib.RQ('m'), SUM3)), tsq], 'eqbrtrrd',
              '%s <_ ( %s x. ( 1 + ( log ` %s ) ) )' % (SUM3, E3, MX))
    sum3re = st([rfin, rjre], 'fsumrecl', '%s e. RR' % SUM3)
    bnd = '( %s x. ( 1 + ( log ` %s ) ) )' % (E3, MX)
    bndre = st([st([lit(w, A, '3', 'RR')], 'reefcld', '%s e. RR' % E3), st([lit(w, A, '1', 'RR'), st([st([Mnn], 'nnrpd', '%s e. RR+' % MX)], 'relogcld', '( log ` %s ) e. RR' % MX)], 'readdcld',
                '( 1 + ( log ` %s ) ) e. RR' % MX)], 'remulcld', '%s e. RR' % bnd)
    kmul = st([sum3re, bndre, kre, k0, tsq2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (KX, SUM3, KX, bnd))
    cnt = st([st([xnn, ere], 'jca', '( X e. NN /\\ E e. RR )'), w.inst('smshcnt')], 'syl', '( # ` %s ) <_ %s' % (SBX, SUM1))
    sbre = st([st([st([st([], 'fzfid', '( 0 ... X ) e. Fin'), w.inst('rabfi')], 'syl', '%s e. Fin' % SBX), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SBX)], 'nn0red',
              '( # ` %s ) e. RR' % SBX)
    sum1re = st([rfin, twre], 'fsumrecl', '%s e. RR' % SUM1)
    sum2re = st([rfin, krj], 'fsumrecl', '%s e. RR' % SUM2)
    c1 = st([sbre, sum1re, sum2re, cnt, fle], 'letrd', '( # ` %s ) <_ %s' % (SBX, SUM2))
    c2 = st([c1, st([mul], 'eqcomd', '%s = ( %s x. %s )' % (SUM2, KX, SUM3))], 'breqtrd', '( # ` %s ) <_ ( %s x. %s )' % (SBX, KX, SUM3))
    w.qed([sbre, st([kre, sum3re], 'remulcld', '( %s x. %s ) e. RR' % (KX, SUM3)), st([kre, bndre], 'remulcld', '( %s x. %s ) e. RR' % (KX, bnd)), c2, kmul],
          'letrd', v5lib.STATEMENTS['smshsum'])
    return run(w)



# ------------------------------------------------------------------ smshpi
def smshpi():
    w = W('smshpi', 'The bad primes are at most half of all primes up to X: 1 + log M <_ 2 E log X, Chebyshev '
                    'X / ( 3 log X ) <_ ppi X, and 96 C e^3 E <_ 1 / 2 (Lean: hlogM, hbadR2, hxL, hbadPi of smooth_shifted_weak).')
    A = v5lib.PH6
    st = mkst(w, A); pj = Proj(w, A)
    PI = '( ppi ` X )'
    U = '( X / ( 3 x. %s ) )' % L
    Q = '( X / %s )' % L
    G = '( ( C x. %s ) x. E )' % E3
    LM = '( log ` %s )' % MX
    H = '( %s x. ( 2 x. E ) )' % E3
    N16 = '( ; 1 6 x. ( C x. X ) )'
    cre, c0 = pj('C e. RR'), pj('0 <_ C'); xnn, ere = pj('X e. NN'), pj('E e. RR')
    e0 = pj('0 < E'); h96 = pj(v5lib.H96('C', 'E')); l4e = pj('( 4 + ( 1 / E ) ) <_ %s' % L); cheb = pj('%s <_ %s' % (U, PI))
    b5 = pj(v5lib.BOUND5('C', 'X', 'E'))
    xre = st([xnn], 'nnred', 'X e. RR'); xrp = st([xnn], 'nnrpd', 'X e. RR+'); x1 = st([xnn], 'nnge1d', '1 <_ X')
    x0 = st([xrp], 'rpge0d', '0 <_ X'); xcn = st([xre], 'recnd', 'X e. CC')
    erp = st([ere, e0], 'elrpd', 'E e. RR+'); ecn = st([ere], 'recnd', 'E e. CC'); ege0 = st([erp], 'rpge0d', '0 <_ E')
    lre = st([xrp], 'relogcld', '%s e. RR' % L)
    rerp = st([erp], 'rpreccld', '( 1 / E ) e. RR+'); rere = st([rerp], 'rpred', '( 1 / E ) e. RR')
    four = lit(w, A, '4', 'RR')
    l4 = st([four, st([four, rere], 'readdcld', '( 4 + ( 1 / E ) ) e. RR'), lre, st([four, rerp], 'ltaddrpd', '4 < ( 4 + ( 1 / E ) )'), l4e],
            'ltletrd', '4 < %s' % L)
    l0 = st([st([], '0red', '0 e. RR'), four, lre, lit(w, A, '4', 'gt0'), l4], 'lttrd', '0 < %s' % L)
    lrp = st([lre, l0], 'elrpd', '%s e. RR+' % L); lcn = st([lre], 'recnd', '%s e. CC' % L); lne = st([lrp], 'rpne0d', '%s =/= 0' % L)
    # 1 <_ E L
    rel = st([rere, st([four, rere], 'readdcld', '( 4 + ( 1 / E ) ) e. RR'), lre,
              st([rere, lit(w, A, '4', 'RR+')], 'ltaddrp2d', '( 1 / E ) < ( 4 + ( 1 / E ) )'), l4e], 'ltletrd', '( 1 / E ) < %s' % L)
    rel = st([rere, lre, rel], 'ltled', '( 1 / E ) <_ %s' % L)
    erl = st([rere, lre, ere, ege0, rel], 'lemul2ad', '( E x. ( 1 / E ) ) <_ ( E x. %s )' % L)
    recid = st([ecn, st([erp], 'rpne0d', 'E =/= 0'), w.inst('recid')], 'syl2anc', '( E x. ( 1 / E ) ) = 1')
    el1 = st([recid, erl], 'eqbrtrrd', '1 <_ ( E x. %s )' % L)
    # log M <_ E L
    XE_ = XE
    xere = st([xre, x0, ere], 'recxpcld', '%s e. RR' % XE_)
    xerp = st([xrp, ere], 'rpcxpcld', '%s e. RR+' % XE_)
    Mz = st([xere], 'flcld', '%s e. ZZ' % MX)
    one_xe = st([st([st([xcn], 'cxp0d', '( X ^c 0 ) = 1')], 'eqcomd', '1 = ( X ^c 0 )'),
                 st([xre, x1, st([], '0red', '0 e. RR'), ere, ege0], 'cxplead', '( X ^c 0 ) <_ %s' % XE_)], 'eqbrtrd', '1 <_ %s' % XE_)
    M1 = st([one_xe, st([xere, st([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('flge')], 'syl2anc',
                        '( 1 <_ %s <-> 1 <_ %s )' % (XE_, MX))], 'mpbid', '1 <_ %s' % MX)
    Mnn = st([Mz, M1, w.s([], 'elnnz1', '( %s e. NN <-> ( %s e. ZZ /\\ 1 <_ %s ) )' % (MX, MX, MX))], 'sylanbrc', '%s e. NN' % MX)
    Mrp = st([Mnn], 'nnrpd', '%s e. RR+' % MX)
    mxe = st([xere, w.inst('flle')], 'syl', '%s <_ %s' % (MX, XE_))
    lmle = st([mxe, st([Mrp, xerp], 'logled', '( %s <_ %s <-> %s <_ ( log ` %s ) )' % (MX, XE_, LM, XE_))], 'mpbid', '%s <_ ( log ` %s )' % (LM, XE_))
    lmel = st([lmle, st([xrp, ere], 'logcxpd', '( log ` %s ) = ( E x. %s )' % (XE_, L))], 'breqtrd', '%s <_ ( E x. %s )' % (LM, L))
    lmre = st([Mrp], 'relogcld', '%s e. RR' % LM)
    elre = st([ere, lre], 'remulcld', '( E x. %s ) e. RR' % L)
    twocn = st([], '2cnd', '2 e. CC')
    ass2 = st([twocn, ecn, lcn], 'mulassd', '( ( 2 x. E ) x. %s ) = ( 2 x. ( E x. %s ) )' % (L, L))
    TEL = '( ( 2 x. E ) x. %s )' % L
    telre = st([st([lit(w, A, '2', 'RR'), ere], 'remulcld', '( 2 x. E ) e. RR'), lre], 'remulcld', '%s e. RR' % TEL)
    hlm = linarith(w, A, [lmel, el1, ass2], '( 1 + %s ) <_ %s' % (LM, TEL),
                   leaves={LM: lmre, '( E x. %s )' % L: elre, TEL: telre})
    # B <_ K ( e^3 ( ( 2 E ) L ) )
    e3rp = st([lit(w, A, '3', 'RR')], 'rpefcld', '%s e. RR+' % E3); e3re = st([e3rp], 'rpred', '%s e. RR' % E3)
    e3cn = st([e3rp], 'rpcnd', '%s e. CC' % E3); e3ge = st([e3rp], 'rpge0d', '0 <_ %s' % E3)
    lm1 = st([lit(w, A, '1', 'RR'), lmre], 'readdcld', '( 1 + %s ) e. RR' % LM)
    m1 = st([lm1, telre, e3re, e3ge, hlm], 'lemul2ad', '( %s x. ( 1 + %s ) ) <_ ( %s x. %s )' % (E3, LM, E3, TEL))
    l2rp = st([lrp, st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % L)
    cxre = st([cre, xre], 'remulcld', '( C x. X ) e. RR')
    n16re = st([lit(w, A, '; 1 6', 'RR'), cxre], 'remulcld', '%s e. RR' % N16)
    kre = st([n16re, l2rp], 'rerpdivcld', '%s e. RR' % KX)
    k0 = st([n16re, l2rp, st([lit(w, A, '; 1 6', 'RR'), cxre, lit(w, A, '; 1 6', 'ge0'), st([cre, xre, c0, x0], 'mulge0d', '0 <_ ( C x. X )')], 'mulge0d',
                            '0 <_ %s' % N16)], 'divge0d', '0 <_ %s' % KX)
    B1 = '( %s x. ( 1 + %s ) )' % (E3, LM); B2 = '( %s x. %s )' % (E3, TEL)
    b1re = st([e3re, lm1], 'remulcld', '%s e. RR' % B1); b2re = st([e3re, telre], 'remulcld', '%s e. RR' % B2)
    m2 = st([b1re, b2re, kre, k0, m1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (KX, B1, KX, B2))
    sbre = st([st([st([st([], 'fzfid', '( 0 ... X ) e. Fin'), w.inst('rabfi')], 'syl', '%s e. Fin' % SBX), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SBX)], 'nn0red',
              '( # ` %s ) e. RR' % SBX)
    kb1 = st([kre, b1re], 'remulcld', '( %s x. %s ) e. RR' % (KX, B1)); kb2 = st([kre, b2re], 'remulcld', '( %s x. %s ) e. RR' % (KX, B2))
    ha = st([sbre, kb1, kb2, b5, m2], 'letrd', '( # ` %s ) <_ ( %s x. %s )' % (SBX, KX, B2))
    # the identity K ( e^3 ( ( 2 E ) L ) ) = 32 ( G Q )
    kcn = st([kre], 'recnd', '%s e. CC' % KX); ccn = st([cre], 'recnd', 'C e. CC')
    tecn = st([twocn, ecn], 'mulcld', '( 2 x. E ) e. CC')
    hcn = st([e3cn, tecn], 'mulcld', '%s e. CC' % H)
    a1 = st([st([e3cn, tecn, lcn], 'mulassd', '( %s x. %s ) = ( %s x. %s )' % (H, L, E3, TEL))], 'eqcomd', '( %s x. %s ) = ( %s x. %s )' % (E3, TEL, H, L))
    a2 = st([a1], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (KX, B2, KX, H, L))
    a3 = st([st([kcn, hcn, lcn], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (KX, H, L, KX, H, L))], 'eqcomd',
            '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (KX, H, L, KX, H, L))
    a4 = st([kcn, hcn, lcn], 'mul32d', '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (KX, H, L, KX, L, H))
    n16cn = st([n16re], 'recnd', '%s e. CC' % N16)
    a5b = st([st([lcn], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (L, L, L))], 'oveq2d', '%s = ( %s / ( %s x. %s ) )' % (KX, N16, L, L))
    a5c = st([n16cn, lcn, lcn, lne, lne], 'divdiv1d', '( ( %s / %s ) / %s ) = ( %s / ( %s x. %s ) )' % (N16, L, L, N16, L, L))
    a5d = st([a5b, a5c], 'eqtr4d', '%s = ( ( %s / %s ) / %s )' % (KX, N16, L, L))
    a5e = st([a5d], 'oveq1d', '( %s x. %s ) = ( ( ( %s / %s ) / %s ) x. %s )' % (KX, L, N16, L, L, L))
    n16l = st([n16cn, lcn, lne], 'divcld', '( %s / %s ) e. CC' % (N16, L))
    a5f = st([n16l, lcn, lne], 'divcan1d', '( ( ( %s / %s ) / %s ) x. %s ) = ( %s / %s )' % (N16, L, L, L, N16, L))
    a5 = st([a5e, a5f], 'eqtrd', '( %s x. %s ) = ( %s / %s )' % (KX, L, N16, L))
    c16 = st([num.cc(w, '; 1 6')], 'a1i', '; 1 6 e. CC'); cxcn = st([ccn, xcn], 'mulcld', '( C x. X ) e. CC')
    a6 = st([c16, cxcn, lcn, lne], 'divassd', '( %s / %s ) = ( ; 1 6 x. ( ( C x. X ) / %s ) )' % (N16, L, L))
    a7 = st([st([ccn, xcn, lcn, lne], 'divassd', '( ( C x. X ) / %s ) = ( C x. %s )' % (L, Q))], 'oveq2d',
            '( ; 1 6 x. ( ( C x. X ) / %s ) ) = ( ; 1 6 x. ( C x. %s ) )' % (L, Q))
    a8 = st([a5, st([a6, a7], 'eqtrd', '( %s / %s ) = ( ; 1 6 x. ( C x. %s ) )' % (N16, L, Q))], 'eqtrd', '( %s x. %s ) = ( ; 1 6 x. ( C x. %s ) )' % (KX, L, Q))
    a9 = st([a8], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( ( ; 1 6 x. ( C x. %s ) ) x. %s )' % (KX, L, H, Q, H))
    a10 = st([e3cn, twocn, ecn], 'mul12d', '%s = ( 2 x. ( %s x. E ) )' % (H, E3))
    a11 = st([a10], 'oveq2d', '( ( ; 1 6 x. ( C x. %s ) ) x. %s ) = ( ( ; 1 6 x. ( C x. %s ) ) x. ( 2 x. ( %s x. E ) ) )' % (Q, H, Q, E3))
    qcn = st([xcn, lcn, lne], 'divcld', '%s e. CC' % Q); cqcn = st([ccn, qcn], 'mulcld', '( C x. %s ) e. CC' % Q)
    e3ecn = st([e3cn, ecn], 'mulcld', '( %s x. E ) e. CC' % E3)
    a12 = st([c16, cqcn, twocn, e3ecn], 'mul4d',
             '( ( ; 1 6 x. ( C x. %s ) ) x. ( 2 x. ( %s x. E ) ) ) = ( ( ; 1 6 x. 2 ) x. ( ( C x. %s ) x. ( %s x. E ) ) )' % (Q, E3, Q, E3))
    a13 = st([st([num.mul_nat(w, 16, 2)], 'a1i', '( ; 1 6 x. 2 ) = ; 3 2')], 'oveq1d',
             '( ( ; 1 6 x. 2 ) x. ( ( C x. %s ) x. ( %s x. E ) ) ) = ( ; 3 2 x. ( ( C x. %s ) x. ( %s x. E ) ) )' % (Q, E3, Q, E3))
    a14 = st([ccn, qcn, e3cn, ecn], 'mul4d', '( ( C x. %s ) x. ( %s x. E ) ) = ( ( C x. %s ) x. ( %s x. E ) )' % (Q, E3, E3, Q))
    a15 = st([st([qcn, ecn], 'mulcomd', '( %s x. E ) = ( E x. %s )' % (Q, Q))], 'oveq2d',
             '( ( C x. %s ) x. ( %s x. E ) ) = ( ( C x. %s ) x. ( E x. %s ) )' % (E3, Q, E3, Q))
    ce3cn = st([ccn, e3cn], 'mulcld', '( C x. %s ) e. CC' % E3)
    a16 = st([st([ce3cn, ecn, qcn], 'mulassd', '( %s x. %s ) = ( ( C x. %s ) x. ( E x. %s ) )' % (G, Q, E3, Q))], 'eqcomd',
             '( ( C x. %s ) x. ( E x. %s ) ) = ( %s x. %s )' % (E3, Q, G, Q))
    a17 = st([st([st([a14, a15], 'eqtrd', '( ( C x. %s ) x. ( %s x. E ) ) = ( ( C x. %s ) x. ( E x. %s ) )' % (Q, E3, E3, Q)), a16], 'eqtrd',
                 '( ( C x. %s ) x. ( %s x. E ) ) = ( %s x. %s )' % (Q, E3, G, Q))], 'oveq2d',
             '( ; 3 2 x. ( ( C x. %s ) x. ( %s x. E ) ) ) = ( ; 3 2 x. ( %s x. %s ) )' % (Q, E3, G, Q))
    GQ = '( %s x. %s )' % (G, Q)
    def chain(steps, texts):
        cur, ct = steps[0], texts[0]
        for s_, t_ in zip(steps[1:], texts[2:]):
            cur = st([cur, s_], 'eqtrd', '%s = %s' % (ct, t_))
        return cur
    lhs = chain([a2, a3, a4, a9, a11, a12, a13, a17],
                ['( %s x. %s )' % (KX, B2), '( %s x. ( %s x. %s ) )' % (KX, H, L), '( ( %s x. %s ) x. %s )' % (KX, H, L),
                 '( ( %s x. %s ) x. %s )' % (KX, L, H), '( ( ; 1 6 x. ( C x. %s ) ) x. %s )' % (Q, H),
                 '( ( ; 1 6 x. ( C x. %s ) ) x. ( 2 x. ( %s x. E ) ) )' % (Q, E3),
                 '( ( ; 1 6 x. 2 ) x. ( ( C x. %s ) x. ( %s x. E ) ) )' % (Q, E3),
                 '( ; 3 2 x. ( ( C x. %s ) x. ( %s x. E ) ) )' % (Q, E3), '( ; 3 2 x. %s )' % GQ])
    # 32 ( G Q ) = 96 ( G U )
    threecn = st([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC'); threene = st([w.s([], '3ne0', '3 =/= 0')], 'a1i', '3 =/= 0')
    tlcn = st([threecn, lcn], 'mulcld', '( 3 x. %s ) e. CC' % L)
    tlne = st([st([lit(w, A, '3', 'RR+'), lrp], 'rpmulcld', '( 3 x. %s ) e. RR+' % L)], 'rpne0d', '( 3 x. %s ) =/= 0' % L)
    b1a = st([st([threecn, xcn, tlcn, tlne], 'divassd', '( ( 3 x. X ) / ( 3 x. %s ) ) = ( 3 x. %s )' % (L, U))], 'eqcomd',
             '( 3 x. %s ) = ( ( 3 x. X ) / ( 3 x. %s ) )' % (U, L))
    b1b = st([xcn, lcn, threecn, lne, threene], 'divcan5d', '( ( 3 x. X ) / ( 3 x. %s ) ) = %s' % (L, Q))
    b1 = st([st([b1a, b1b], 'eqtrd', '( 3 x. %s ) = %s' % (U, Q))], 'eqcomd', '%s = ( 3 x. %s )' % (Q, U))
    gcn = st([ce3cn, ecn], 'mulcld', '%s e. CC' % G)
    ucn = st([xcn, tlcn, tlne], 'divcld', '%s e. CC' % U)
    GU = '( %s x. %s )' % (G, U)
    b2 = st([b1], 'oveq2d', '%s = ( %s x. ( 3 x. %s ) )' % (GQ, G, U))
    b3 = st([gcn, threecn, ucn], 'mul12d', '( %s x. ( 3 x. %s ) ) = ( 3 x. %s )' % (G, U, GU))
    b23 = st([st([b2, b3], 'eqtrd', '%s = ( 3 x. %s )' % (GQ, GU))], 'oveq2d', '( ; 3 2 x. %s ) = ( ; 3 2 x. ( 3 x. %s ) )' % (GQ, GU))
    c32 = st([num.cc(w, '; 3 2')], 'a1i', '; 3 2 e. CC'); gucn = st([gcn, ucn], 'mulcld', '%s e. CC' % GU)
    b4 = st([st([c32, threecn, gucn], 'mulassd', '( ( ; 3 2 x. 3 ) x. %s ) = ( ; 3 2 x. ( 3 x. %s ) )' % (GU, GU))], 'eqcomd',
            '( ; 3 2 x. ( 3 x. %s ) ) = ( ( ; 3 2 x. 3 ) x. %s )' % (GU, GU))
    b5_ = st([st([num.mul_nat(w, 32, 3)], 'a1i', '( ; 3 2 x. 3 ) = ; 9 6')], 'oveq1d', '( ( ; 3 2 x. 3 ) x. %s ) = ( ; 9 6 x. %s )' % (GU, GU))
    rhs = chain([b23, b4, b5_], ['( ; 3 2 x. %s )' % GQ, '( ; 3 2 x. ( 3 x. %s ) )' % GU, '( ( ; 3 2 x. 3 ) x. %s )' % GU, '( ; 9 6 x. %s )' % GU])
    ident = st([lhs, rhs], 'eqtrd', '( %s x. %s ) = ( ; 9 6 x. %s )' % (KX, B2, GU))
    # 96 ( G U ) <_ 96 ( G PI ) = ( 96 G ) PI <_ ( 1 / 2 ) PI
    gre = st([st([cre, e3re], 'remulcld', '( C x. %s ) e. RR' % E3), ere], 'remulcld', '%s e. RR' % G)
    g0 = st([st([cre, e3re], 'remulcld', '( C x. %s ) e. RR' % E3), ere, st([cre, e3re, c0, e3ge], 'mulge0d', '0 <_ ( C x. %s )' % E3), ege0], 'mulge0d', '0 <_ %s' % G)
    ure = st([xre, st([lit(w, A, '3', 'RR+'), lrp], 'rpmulcld', '( 3 x. %s ) e. RR+' % L)], 'rerpdivcld', '%s e. RR' % U)
    pire = st([st([xre, w.inst('ppicl')], 'syl', '%s e. NN0' % PI)], 'nn0red', '%s e. RR' % PI)
    pi0 = st([st([xre, w.inst('ppicl')], 'syl', '%s e. NN0' % PI)], 'nn0ge0d', '0 <_ %s' % PI)
    c1 = st([ure, pire, gre, g0, cheb], 'lemul2ad', '%s <_ ( %s x. %s )' % (GU, G, PI))
    gure = st([gre, ure], 'remulcld', '%s e. RR' % GU); gpire = st([gre, pire], 'remulcld', '( %s x. %s ) e. RR' % (G, PI))
    c1b = st([gure, gpire, lit(w, A, '; 9 6', 'RR'), lit(w, A, '; 9 6', 'ge0'), c1], 'lemul2ad', '( ; 9 6 x. %s ) <_ ( ; 9 6 x. ( %s x. %s ) )' % (GU, G, PI))
    c96 = st([num.cc(w, '; 9 6')], 'a1i', '; 9 6 e. CC')
    c2 = st([st([c96, gcn, st([pire], 'recnd', '%s e. CC' % PI)], 'mulassd', '( ( ; 9 6 x. %s ) x. %s ) = ( ; 9 6 x. ( %s x. %s ) )' % (G, PI, G, PI))], 'eqcomd',
            '( ; 9 6 x. ( %s x. %s ) ) = ( ( ; 9 6 x. %s ) x. %s )' % (G, PI, G, PI))
    g96re = st([lit(w, A, '; 9 6', 'RR'), gre], 'remulcld', '( ; 9 6 x. %s ) e. RR' % G)
    c3 = st([g96re, lit(w, A, HALF, 'RR'), pire, pi0, h96], 'lemul1ad', '( ( ; 9 6 x. %s ) x. %s ) <_ ( %s x. %s )' % (G, PI, HALF, PI))
    r96gu = st([lit(w, A, '; 9 6', 'RR'), gure], 'remulcld', '( ; 9 6 x. %s ) e. RR' % GU)
    r96gpi = st([lit(w, A, '; 9 6', 'RR'), gpire], 'remulcld', '( ; 9 6 x. ( %s x. %s ) ) e. RR' % (G, PI))
    hpi = st([lit(w, A, HALF, 'RR'), pire], 'remulcld', '( %s x. %s ) e. RR' % (HALF, PI))
    d1 = st([c1b, c2], 'breqtrd', '( ; 9 6 x. %s ) <_ ( ( ; 9 6 x. %s ) x. %s )' % (GU, G, PI))
    d2 = st([r96gu, st([g96re, pire], 'remulcld', '( ( ; 9 6 x. %s ) x. %s ) e. RR' % (G, PI)), hpi, d1, c3], 'letrd',
            '( ; 9 6 x. %s ) <_ ( %s x. %s )' % (GU, HALF, PI))
    e1 = st([ha, ident], 'breqtrd', '( # ` %s ) <_ ( ; 9 6 x. %s )' % (SBX, GU))
    w.qed([sbre, r96gu, hpi, e1, d2], 'letrd', v5lib.STATEMENTS['smshpi'])
    return run(w)


if __name__ == '__main__':
    smshsum(); smshpi()
