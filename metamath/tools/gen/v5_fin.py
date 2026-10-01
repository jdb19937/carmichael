"""Sortie V5: the pointwise conclusion (smshx), the eventual statement
(smshev) and the headline smshw = Lean's smooth_shifted_weak.
MM_DB=sorties/v5.mm python3 tools/gen/v5_fin.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from lin import linarith
from cl import lift
import num
import a5lib
import v5lib
from v5lib import mkst, lit, Proj, subst, HALF, E3

only = sys.argv[1:]
L = '( log ` X )'
SQX = '( sqrt ` X )'
TWINCT = v5lib.TWIN('C', 'T')


def run(w):
    if only and w.label not in only:
        return True
    ok = w.run()
    assert ok, w.label
    return ok


# ------------------------------------------------------------------ smshx
def smshx():
    w = W('smshx', 'At every x satisfying the pointwise conditions, at least half of the primes up to x are '
                   'smooth-shifted (Lean: the body of `key` in smooth_shifted_weak).')
    A = '( %s /\\ %s )' % (v5lib.PH(), v5lib.XC('X'))
    st = mkst(w, A); pj = Proj(w, A)
    cre, c0 = pj('C e. RR'), pj('0 < C'); tnn, twin = pj('T e. NN'), pj(TWINCT)
    ere, e0, eh = pj('E e. RR'), pj('0 < E'), pj('E <_ %s' % HALF); h96 = pj(v5lib.H96('C', 'E'))
    xnn = pj('X e. NN'); l4e = pj('( 4 + ( 1 / E ) ) <_ %s' % L); t2s = pj('( T + 2 ) <_ %s' % SQX)
    U = '( X / ( 3 x. %s ) )' % L; PI = '( ppi ` X )'
    cheb = pj('%s <_ %s' % (U, PI))
    cge0 = st([cre, c0], 'elrpd', 'C e. RR+'); cge0 = st([cge0], 'rpge0d', '0 <_ C')
    xrp = st([xnn], 'nnrpd', 'X e. RR+'); lre = st([xrp], 'relogcld', '%s e. RR' % L)
    erp = st([ere, e0], 'elrpd', 'E e. RR+'); rerp = st([erp], 'rpreccld', '( 1 / E ) e. RR+'); rere = st([rerp], 'rpred', '( 1 / E ) e. RR')
    four = lit(w, A, '4', 'RR')
    l4 = st([four, st([four, rere], 'readdcld', '( 4 + ( 1 / E ) ) e. RR'), lre, st([four, rerp], 'ltaddrpd', '4 < ( 4 + ( 1 / E ) )'), l4e],
            'ltletrd', '4 < %s' % L)
    l4 = st([four, lre, l4], 'ltled', '4 <_ %s' % L)
    ph5 = st([st([st([cre, cge0], 'jca', '( C e. RR /\\ 0 <_ C )'), st([xnn, ere], 'jca', '( X e. NN /\\ E e. RR )'), l4], '3jca',
                 '( ( C e. RR /\\ 0 <_ C ) /\\ ( X e. NN /\\ E e. RR ) /\\ 4 <_ %s )' % L),
              st([st([tnn, twin], 'jca', '( T e. NN /\\ %s )' % TWINCT),
                  st([st([e0, eh], 'jca', '( 0 < E /\\ E <_ %s )' % HALF), t2s], 'jca', '( ( 0 < E /\\ E <_ %s ) /\\ ( T + 2 ) <_ %s )' % (HALF, SQX))], 'jca',
                 '( ( T e. NN /\\ %s ) /\\ ( ( 0 < E /\\ E <_ %s ) /\\ ( T + 2 ) <_ %s ) )' % (TWINCT, HALF, SQX))], 'jca', v5lib.PH5)
    b5 = st([ph5, w.inst('smshsum')], 'syl', v5lib.BOUND5('C', 'X', 'E'))
    ph6 = st([st([st([cre, cge0], 'jca', '( C e. RR /\\ 0 <_ C )'), st([xnn, ere], 'jca', '( X e. NN /\\ E e. RR )')], 'jca',
                 '( ( C e. RR /\\ 0 <_ C ) /\\ ( X e. NN /\\ E e. RR ) )'),
              st([st([st([e0, h96], 'jca', '( 0 < E /\\ %s )' % v5lib.H96('C', 'E')), st([l4e, cheb], 'jca', '( ( 4 + ( 1 / E ) ) <_ %s /\\ %s <_ %s )' % (L, U, PI))], 'jca',
                     '( ( 0 < E /\\ %s ) /\\ ( ( 4 + ( 1 / E ) ) <_ %s /\\ %s <_ %s ) )' % (v5lib.H96('C', 'E'), L, U, PI)), b5], 'jca',
                 '( ( ( 0 < E /\\ %s ) /\\ ( ( 4 + ( 1 / E ) ) <_ %s /\\ %s <_ %s ) ) /\\ %s )' % (v5lib.H96('C', 'E'), L, U, PI, v5lib.BOUND5('C', 'X', 'E')))],
             'jca', v5lib.PH6)
    SBX, SGX = v5lib.SB('X', 'E'), v5lib.SG('X', 'E')
    hpi = st([ph6, w.inst('smshpi')], 'syl', '( # ` %s ) <_ ( %s x. %s )' % (SBX, HALF, PI))
    spl = st([st([xnn, ere], 'jca', '( X e. NN /\\ E e. RR )'), w.inst('smshsplit')], 'syl', '%s <_ ( ( # ` %s ) + ( # ` %s ) )' % (PI, SGX, SBX))
    fz = st([], 'fzfid', '( 0 ... X ) e. Fin')
    gre = st([st([st([fz, w.inst('rabfi')], 'syl', '%s e. Fin' % SGX), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SGX)], 'nn0red', '( # ` %s ) e. RR' % SGX)
    bre = st([st([st([fz, w.inst('rabfi')], 'syl', '%s e. Fin' % SBX), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SBX)], 'nn0red', '( # ` %s ) e. RR' % SBX)
    pire = st([st([st([xnn], 'nnred', 'X e. RR'), w.inst('ppicl')], 'syl', '%s e. NN0' % PI)], 'nn0red', '%s e. RR' % PI)
    linarith(w, A, [hpi, spl], v5lib.GOAL('X', 'E'), leaves={PI: pire, '( # ` %s )' % SGX: gre, '( # ` %s )' % SBX: bre}, name='qed')
    return run(w)


# ------------------------------------------------------------------ smshev
def smshev():
    w = W('smshev', 'Eventually at least half of the primes up to x are smooth-shifted: the threshold is '
                    '|_ exp ( 4 + 1 / E ) _| + 1 + ( T + 2 ) ^ 2 + the Chebyshev threshold (Lean: `key` of smooth_shifted_weak).')
    PH = v5lib.PH()
    CH = lambda z: '( %s / ( 3 x. ( log ` %s ) ) ) <_ ( ppi ` %s )' % (z, z, z)
    ALLCH = 'A. z e. ( ZZ>= ` m ) %s' % CH('z')
    A1 = '( %s /\\ m e. NN )' % PH
    A2 = '( %s /\\ %s )' % (A1, ALLCH)
    st = mkst(w, A2); pj = Proj(w, A2)
    tnn = pj('T e. NN'); ere, e0 = pj('E e. RR'), pj('0 < E'); mnn = pj('m e. NN'); allch = pj(ALLCH)
    EXP = '( exp ` ( 4 + ( 1 / E ) ) )'
    F1 = '( ( |_ ` %s ) + 1 )' % EXP
    F2 = '( ( T + 2 ) ^ 2 )'
    WW = '( %s + ( %s + m ) )' % (F1, F2)
    erp = st([ere, e0], 'elrpd', 'E e. RR+'); rere = st([st([erp], 'rpreccld', '( 1 / E ) e. RR+')], 'rpred', '( 1 / E ) e. RR')
    arg = st([lit(w, A2, '4', 'RR'), rere], 'readdcld', '( 4 + ( 1 / E ) ) e. RR')
    exrp = st([arg], 'rpefcld', '%s e. RR+' % EXP); exre = st([exrp], 'rpred', '%s e. RR' % EXP)
    fln0 = st([exre, st([exrp], 'rpge0d', '0 <_ %s' % EXP), w.inst('flge0nn0')], 'syl2anc', '( |_ ` %s ) e. NN0' % EXP)
    f1n0 = st([fln0, w.inst('peano2nn0')], 'syl', '%s e. NN0' % F1)
    t2nn = st([tnn, lit(w, A2, '2', 'NN')], 'nnaddcld', '( T + 2 ) e. NN')
    f2nn = st([t2nn, lit(w, A2, '2', 'NN0')], 'nnexpcld', '%s e. NN' % F2)
    f2n0 = st([f2nn], 'nnnn0d', '%s e. NN0' % F2)
    f2m = st([f2n0, st([mnn], 'nnnn0d', 'm e. NN0')], 'nn0addcld', '( %s + m ) e. NN0' % F2)
    wn0 = st([f1n0, f2m], 'nn0addcld', '%s e. NN0' % WW)
    # under x e. ( ZZ>= ` W )
    A3 = '( %s /\\ x e. ( ZZ>= ` %s ) )' % (A2, WW)
    s3 = mkst(w, A3)
    l3 = lambda s: lift(w, s, A3)
    xuz = s3([], 'simpr', 'x e. ( ZZ>= ` %s )' % WW)
    xz = s3([xuz, w.inst('eluzelz')], 'syl', 'x e. ZZ'); xre = s3([xz], 'zred', 'x e. RR')
    wx = s3([xuz, w.inst('eluzle')], 'syl', '%s <_ x' % WW)
    f1re = s3([l3(f1n0)], 'nn0red', '%s e. RR' % F1); f2re = s3([l3(f2n0)], 'nn0red', '%s e. RR' % F2)
    mre = s3([l3(mnn)], 'nnred', 'm e. RR'); f2mre = s3([l3(f2m)], 'nn0red', '( %s + m ) e. RR' % F2)
    wre = s3([l3(wn0)], 'nn0red', '%s e. RR' % WW)
    f1w = s3([s3([l3(f2m)], 'nn0ge0d', '0 <_ ( %s + m )' % F2), s3([f1re, f2mre], 'addge01d', '( 0 <_ ( %s + m ) <-> %s <_ %s )' % (F2, F1, WW))], 'mpbid', '%s <_ %s' % (F1, WW))
    f1x = s3([f1re, wre, xre, f1w, wx], 'letrd', '%s <_ x' % F1)
    f2f2m = s3([s3([s3([l3(mnn)], 'nnnn0d', 'm e. NN0')], 'nn0ge0d', '0 <_ m'),
                s3([f2re, mre], 'addge01d', '( 0 <_ m <-> %s <_ ( %s + m ) )' % (F2, F2))], 'mpbid', '%s <_ ( %s + m )' % (F2, F2))
    f2mw = s3([s3([l3(f1n0)], 'nn0ge0d', '0 <_ %s' % F1), s3([f2mre, f1re], 'addge02d', '( 0 <_ %s <-> ( %s + m ) <_ %s )' % (F1, F2, WW))], 'mpbid',
              '( %s + m ) <_ %s' % (F2, WW))
    f2w = s3([f2re, f2mre, wre, f2f2m, f2mw], 'letrd', '%s <_ %s' % (F2, WW))
    f2x = s3([f2re, wre, xre, f2w, wx], 'letrd', '%s <_ x' % F2)
    mf2m = s3([s3([l3(f2n0)], 'nn0ge0d', '0 <_ %s' % F2), s3([mre, f2re], 'addge02d', '( 0 <_ %s <-> m <_ ( %s + m ) )' % (F2, F2))], 'mpbid', 'm <_ ( %s + m )' % F2)
    mw = s3([mre, f2mre, wre, mf2m, f2mw], 'letrd', 'm <_ %s' % WW)
    mx = s3([mre, wre, xre, mw, wx], 'letrd', 'm <_ x')
    # x e. NN
    x1 = s3([lit(w, A3, '1', 'RR'), f2re, xre, s3([l3(f2nn)], 'nnge1d', '1 <_ %s' % F2), f2x], 'letrd', '1 <_ x')
    xnn = s3([xz, x1, w.s([], 'elnnz1', '( x e. NN <-> ( x e. ZZ /\\ 1 <_ x ) )')], 'sylanbrc', 'x e. NN')
    xrp = s3([xnn], 'nnrpd', 'x e. RR+')
    # log x >= 4 + 1 / E
    exx = s3([l3(exre), f1re, xre, s3([l3(exre), w.inst('flltp1')], 'syl', '%s < %s' % (EXP, F1)), f1x], 'ltletrd', '%s < x' % EXP)
    exx = s3([l3(exre), xre, exx], 'ltled', '%s <_ x' % EXP)
    lgx = s3([exx, s3([l3(exrp), xrp], 'logled', '( %s <_ x <-> ( log ` %s ) <_ ( log ` x ) )' % (EXP, EXP))], 'mpbid', '( log ` %s ) <_ ( log ` x )' % EXP)
    lgx = s3([s3([l3(arg)], 'relogefd', '( log ` %s ) = ( 4 + ( 1 / E ) )' % EXP), lgx], 'eqbrtrrd', '( 4 + ( 1 / E ) ) <_ ( log ` x )')
    # T + 2 <_ sqrt x
    t2re = s3([l3(t2nn)], 'nnred', '( T + 2 ) e. RR'); t2ge0 = s3([s3([l3(t2nn)], 'nnrpd', '( T + 2 ) e. RR+')], 'rpge0d', '0 <_ ( T + 2 )')
    sq = s3([f2x, s3([f2re, s3([l3(f2n0)], 'nn0ge0d', '0 <_ %s' % F2), xre, s3([xrp], 'rpge0d', '0 <_ x')], 'sqrtled',
                     '( %s <_ x <-> ( sqrt ` %s ) <_ ( sqrt ` x ) )' % (F2, F2))], 'mpbid', '( sqrt ` %s ) <_ ( sqrt ` x )' % F2)
    sq = s3([s3([t2re, t2ge0], 'sqrtsqd', '( sqrt ` %s ) = ( T + 2 )' % F2), sq], 'eqbrtrrd', '( T + 2 ) <_ ( sqrt ` x )')
    # Chebyshev at x
    xum = s3([s3([l3(mnn)], 'nnzd', 'm e. ZZ'), xz, mx, w.s([], 'eluz2', '( x e. ( ZZ>= ` m ) <-> ( m e. ZZ /\\ x e. ZZ /\\ m <_ x ) )')], 'syl3anbrc',
             'x e. ( ZZ>= ` m )')
    chx, chtext = a5lib.unwind(w, A3, l3(allch), ALLCH, [('q', 'z', '( ZZ>= ` m )', 'x', xum)])
    assert chtext == CH('x'), chtext
    xc = s3([xnn, s3([lgx, sq], 'jca', '( ( 4 + ( 1 / E ) ) <_ ( log ` x ) /\\ ( T + 2 ) <_ ( sqrt ` x ) )'), chx], '3jca', v5lib.XC('x'))
    gx = s3([s3([l3(st([], 'simpll', PH)), xc], 'jca', '( %s /\\ %s )' % (PH, v5lib.XC('x'))), w.inst('smshx')], 'syl', v5lib.GOAL('x', 'E'))
    allx = st([gx], 'ralrimiva', 'A. x e. ( ZZ>= ` %s ) %s' % (WW, v5lib.GOAL('x', 'E')))
    sl, _ = subst(w, 'w', WW, 'A. x e. ( ZZ>= ` w ) %s' % v5lib.GOAL('x', 'E'))
    GEV = 'E. w e. NN0 A. x e. ( ZZ>= ` w ) %s' % v5lib.GOAL('x', 'E')
    ex = st([wn0, allx, w.s([sl], 'rspcev', '( ( %s e. NN0 /\\ A. x e. ( ZZ>= ` %s ) %s ) -> %s )' % (WW, WW, v5lib.GOAL('x', 'E'), GEV))], 'syl2anc', GEV)
    rl = w.s([w.s([ex], 'ex', '( %s -> ( %s -> %s ) )' % (A1, ALLCH, GEV))], 'rexlimdva', '( %s -> ( E. m e. NN %s -> %s ) )' % (PH, ALLCH, GEV))
    w.qed([w.s([], 'ppilb3', 'E. m e. NN %s' % ALLCH), rl], 'mpi', '( %s -> %s )' % (PH, GEV))
    return run(w)


# ------------------------------------------------------------------ smshw
def smshw():
    w = W('smshw', 'Weak AGP Theorem 3 (Lean: smooth_shifted_weak of SmoothShifted.lean): for some smoothness '
                   'exponent t in ( 0 , 1 / 2 ] and density g > 0, eventually at least g ppi x of the primes p <_ x '
                   'have p - 1 free of prime factors above x ^c ( 1 - t ).  The existential closure of carmsalg.3 to carmsalg.10.')
    TWcm = v5lib.TWIN('c', 'm')
    A1 = '( ( ( c e. RR /\\ 0 < c ) /\\ m e. NN ) /\\ %s )' % TWcm
    st = mkst(w, A1); pj = Proj(w, A1)
    cre, c0, mnn, twin = pj('c e. RR'), pj('0 < c'), pj('m e. NN'), pj(TWcm)
    ET = v5lib.EE('c')
    ef = st([st([cre, c0], 'jca', '( c e. RR /\\ 0 < c )'), w.inst('smshe')], 'syl',
            '( ( %s e. RR /\\ 0 < %s /\\ %s <_ %s ) /\\ %s )' % (ET, ET, ET, HALF, v5lib.H96('c', ET)))
    ph = st([st([st([cre, c0], 'jca', '( c e. RR /\\ 0 < c )'), st([mnn, twin], 'jca', '( m e. NN /\\ %s )' % TWcm)], 'jca',
                '( ( c e. RR /\\ 0 < c ) /\\ ( m e. NN /\\ %s ) )' % TWcm), ef], 'jca', v5lib.PH('c', 'm', ET))
    GOALX = v5lib.GOAL('x', ET)
    GEV = 'E. w e. NN0 A. x e. ( ZZ>= ` w ) %s' % GOALX
    ev = st([ph, w.inst('smshev')], 'syl', GEV)
    # g := 1 / 2
    DG = 'E. w e. NN0 A. x e. ( ZZ>= ` w ) ( g x. ( ppi ` x ) ) <_ ( # ` %s )' % v5lib.SG('x', ET)
    BG = '( 0 < g /\\ %s )' % DG
    slg, bg_half = subst(w, 'g', HALF, BG)
    hg = st([lit(w, A1, HALF, 'gt0'), ev], 'jca', bg_half)
    exg = st([lit(w, A1, HALF, 'RR'), hg, w.s([slg], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. g e. RR %s )' % (HALF, bg_half, BG))], 'syl2anc',
             'E. g e. RR %s' % BG)
    # t := ET
    BT = '( ( 0 < t /\\ t <_ %s ) /\\ E. g e. RR ( 0 < g /\\ E. w e. NN0 %s ) )' % (HALF, v5lib.dens_text('t', 'g', 'w'))
    slt, bt_et = subst(w, 't', ET, BT)
    e3 = st([ef], 'simpld', '( %s e. RR /\\ 0 < %s /\\ %s <_ %s )' % (ET, ET, ET, HALF))
    ht = st([st([st([e3], 'simp2d', '0 < %s' % ET), st([e3], 'simp3d', '%s <_ %s' % (ET, HALF))], 'jca', '( 0 < %s /\\ %s <_ %s )' % (ET, ET, HALF)), exg], 'jca', bt_et)
    GOAL = v5lib.STATEMENTS['smshw']
    assert GOAL == 'E. t e. RR %s' % BT, (GOAL, BT)
    ext = st([st([e3], 'simp1d', '%s e. RR' % ET), ht, w.s([slt], 'rspcev', '( ( %s e. RR /\\ %s ) -> %s )' % (ET, bt_et, GOAL))], 'syl2anc', GOAL)
    A0 = '( c e. RR /\\ 0 < c )'
    r1 = w.s([w.s([ext], 'ex', '( ( %s /\\ m e. NN ) -> ( %s -> %s ) )' % (A0, TWcm, GOAL))], 'rexlimdva', '( %s -> ( E. m e. NN %s -> %s ) )' % (A0, TWcm, GOAL))
    r2 = w.s([w.s([r1], 'ex', '( c e. RR -> ( 0 < c -> ( E. m e. NN %s -> %s ) ) )' % (TWcm, GOAL))], 'impd',
              '( c e. RR -> ( ( 0 < c /\\ E. m e. NN %s ) -> %s ) )' % (TWcm, GOAL))
    r3 = w.s([r2], 'rexlimiv', '( E. c e. RR ( 0 < c /\\ E. m e. NN %s ) -> %s )' % (TWcm, GOAL))
    w.qed([w.s([], 'twinsv', 'E. c e. RR ( 0 < c /\\ E. m e. NN %s )' % TWcm), r3], 'ax-mp', GOAL)
    return run(w)


if __name__ == '__main__':
    smshx(); smshev(); smshw()
