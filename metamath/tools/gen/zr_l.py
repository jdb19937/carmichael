"""Sortie ZR, REP: zrfib (fiberwise split of a character's good zero mass by cell), zrcb (a nonempty cell's mass is a
local count), zrcov (Lean sum_good_le_of_localCount), zrsg (sum_good_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of
from zr_i import scale_facts
from zr_j import box_facts
from zr_k import idx_of


def zf_facts(w, A, nxb, sr, s0, s1, tr, X='X'):
    """( A -> ZFX(X) e. Fin ), ( A -> A. q e. ZFX ( ORD ) e. NN ) from zffin"""
    from zr_e import f2ne0
    c = Ctx(w, A)
    hol = c([nxb, w.inst('zl1ehol')], 'syl', HOLF(EX(X), HP0))
    e2 = c([c([nxb, c([], '0red', '0 e. RR')], 'jca', '( ( N e. NN /\\ %s e. ( Base ` ( DChr ` N ) ) ) /\\ 0 e. RR )' % X), w.inst('ectr')], 'syl', '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % EX(X))
    f2 = f2ne0(w, A, EX(X), None, '( 1 / 2 )', bstep=e2)
    ZA = ante_of(tsub(stmt('zffin'), {'F': EX(X), 'A': 'S'}))
    zf = c([c([c([hol, f2], 'jca', top_and(ZA[0])[0]), c([c([sr, s0, s1], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), tr], 'jca', top_and(ZA[0])[1])], 'jca', ZA[0]), w.inst('zffin')], 'syl', ZA[1])
    return c([zf], 'simpld', '%s e. Fin' % ZFX(X)), c([zf], 'simprd', 'A. q e. %s %s e. NN' % (ZFX(X), ORDX(X, 'q')))


def gen_fib():
    from ef4_g import elrab_unpack
    w = W('zrfib', 'The good zero mass of a character splits over the cells ` 0 ... Qpar ` (the fibres of the cell index; Lean ` sum_fiberwise_of_maps_to ` step of ` sum_good_le_of_localCount ` ; ~ fsumiun , ~ invdisjrab ).')
    A0 = ante_of(S['zrfib'])[0]
    c = Ctx(w, A0)
    nn_, xb, sr, s0, s1, tr, t0 = [c.g(x) for x in ('N e. NN', 'X e. ( Base ` ( DChr ` N ) )', 'S e. RR', '0 < S', 'S <_ 1', 'T e. RR', '0 <_ T')]
    nxb = c([nn_, xb], 'jca', NX)
    zfin, zal = zf_facts(w, A0, nxb, sr, s0, s1, tr)
    GXX = GX('X')
    gss = c.a1(w.s([], 'ssrab2', '%s C_ %s' % (GXX, ZFX('X'))), '%s C_ %s' % (GXX, ZFX('X')))
    gfin = c([zfin, gss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % GXX)
    FB = lambda m: '{ j e. %s | %s = %s }' % (GXX, IDX('j'), m)
    FZ = '( 0 ... %s )' % QP
    dj = c.a1(w.s([], 'invdisjrab', 'Disj_ m e. %s %s' % (FZ, FB('m'))), 'Disj_ m e. %s %s' % (FZ, FB('m')))
    Am = '( %s /\\ m e. %s )' % (A0, FZ)
    cm = Ctx(w, Am)
    fbfin = cm([lift(w, gfin, Am), cm.a1(w.s([], 'ssrab2', '%s C_ %s' % (FB('m'), GXX)), '%s C_ %s' % (FB('m'), GXX)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % FB('m'))
    Amq = '( %s /\\ ( m e. %s /\\ q e. %s ) )' % (A0, FZ, FB('m'))
    cmq = Ctx(w, Amq)
    qfb = cmq.g('q e. %s' % FB('m'))
    qg = cmq([qfb, w.inst('elrabi')], 'syl', 'q e. %s' % GXX)
    qz = cmq([qg, w.inst('elrabi')], 'syl', 'q e. %s' % ZFX('X'))
    Az = '( %s /\\ q e. %s )' % (A0, ZFX('X'))
    on = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Az, ORDX('X', 'q')))
    onq = cmq([cmq([cmq.g(A0), qz], 'jca', Az), on], 'syl', '%s e. NN' % ORDX('X', 'q'))
    oc = cmq([onq], 'nncnd', '%s e. CC' % ORDX('X', 'q'))
    U = 'U_ m e. %s %s' % (FZ, FB('m'))
    fi = c([c([], 'fzfid', '%s e. Fin' % FZ), fbfin, dj, oc], 'fsumiun', 'sum_ q e. %s %s = sum_ m e. %s sum_ q e. %s %s' % (U, ORDX('X', 'q'), FZ, FB('m'), ORDX('X', 'q')))
    # U = GX
    PSI = 'E. m e. %s %s = m' % (FZ, IDX('j'))
    ir = c.a1(w.s([], 'iunrab', '%s = { j e. %s | %s }' % (U, GXX, PSI)), '%s = { j e. %s | %s }' % (U, GXX, PSI))
    Aj = '( %s /\\ j e. %s )' % (A0, GXX)
    cj = Ctx(w, Aj)
    jz = cj([cj([], 'simpr', 'j e. %s' % GXX), w.inst('elrabi')], 'syl', 'j e. %s' % ZFX('X'))
    from ef4_g import elrab_unpack as _eu
    jb, _, _ = _eu(w, Aj, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX('X'), 'j', jz)
    vc, rvr, ivr, f1, f2, f3, f4 = box_facts(w, Aj, lift(w, sr, Aj), lift(w, tr, Aj), jb, 'j')
    ab = cj([cj([f3, f4], 'jca', '( -u T <_ ( Im ` j ) /\\ ( Im ` j ) <_ T )'), cj([ivr, lift(w, tr, Aj)], 'absled', '( ( abs ` ( Im ` j ) ) <_ T <-> ( -u T <_ ( Im ` j ) /\\ ( Im ` j ) <_ T ) )')], 'mpbird', '( abs ` ( Im ` j ) ) <_ T')
    pre = cj([lift(w, nn_, Aj), cj([lift(w, tr, Aj), lift(w, t0, Aj)], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    n0, lq, _, _ = idx_of(w, Aj, pre, 'j', vc, ab)
    d2, lr, lp, dr = scale_facts(w, Aj, lift(w, nn_, Aj), lift(w, tr, Aj), lift(w, t0, Aj))
    Q2 = '( ( 2 x. T ) x. %s )' % LD
    q2r = cj([cj([numst8(w, Aj, '2', 'RR'), lift(w, tr, Aj)], 'remulcld', '( 2 x. T ) e. RR'), lr], 'remulcld', '%s e. RR' % Q2)
    tl0 = cj([cj([numst8(w, Aj, '2', 'RR'), lift(w, tr, Aj)], 'remulcld', '( 2 x. T ) e. RR'), lr,
                  cj([numst8(w, Aj, '2', 'RR'), lift(w, tr, Aj), lin8(w, Aj, [], '0 <_ 2', {}), lift(w, t0, Aj)], 'mulge0d', '0 <_ ( 2 x. T )'),
                  cj([lp], 'ltled', '0 <_ %s' % LD)], 'mulge0d', '0 <_ %s' % Q2)
    qn0 = cj([q2r, tl0, w.inst('flge0nn0')], 'syl2anc', '%s e. NN0' % QP)
    ifz = cj([cj([n0, qn0, lq], '3jca', '( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s )' % (IDX('j'), QP, IDX('j'), QP)), w.s([], 'elfz2nn0', '( %s e. %s <-> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (IDX('j'), FZ, IDX('j'), QP, IDX('j'), QP))],
             'sylibr', '%s e. %s' % (IDX('j'), FZ))
    PSI2 = 'E. m e. %s m = %s' % (FZ, IDX('j'))
    ex_ = cj([ifz, w.s([], 'risset', '( %s e. %s <-> %s )' % (IDX('j'), FZ, PSI2))], 'sylib', PSI2)
    pb = w.s([w.s([], 'eqcom', '( %s = m <-> m = %s )' % (IDX('j'), IDX('j')))], 'rexbii', '( %s <-> %s )' % (PSI, PSI2))
    ps = cj([ex_, pb], 'sylibr', PSI)
    al = c([ps], 'ralrimiva', 'A. j e. %s %s' % (GXX, PSI))
    ge = c([al, w.s([], 'rabid2', '( %s = { j e. %s | %s } <-> A. j e. %s %s )' % (GXX, GXX, PSI, GXX, PSI))], 'sylibr', '%s = { j e. %s | %s }' % (GXX, GXX, PSI))
    ug = c([ir, ge], 'eqtr4d', '%s = %s' % (U, GXX))
    s1 = c([c([ug], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (U, ORDX('X', 'q'), GXX, ORDX('X', 'q')))], 'eqcomd', 'sum_ q e. %s %s = sum_ q e. %s %s' % (GXX, ORDX('X', 'q'), U, ORDX('X', 'q')))
    # fibres are the cells
    from ef3lib import elrab_
    e1_, n1 = elrab_(w, 'j', GXX, '%s = m' % IDX('j'), 'y')
    e2_, n2 = elrab_(w, 'v', ZFX('X'), 'v e. G', 'y')
    e3_, n3 = elrab_(w, 'v', ZFX('X'), '( v e. G /\\ %s = m )' % IDX('v'), 'y')
    b1 = w.s([e1_, w.s([e2_], 'anbi1i', '( ( y e. %s /\\ %s ) <-> ( ( y e. %s /\\ %s ) /\\ %s ) )' % (GXX, n1, ZFX('X'), n2, n1))], 'bitri',
             '( y e. %s <-> ( ( y e. %s /\\ %s ) /\\ %s ) )' % (FB('m'), ZFX('X'), n2, n1))
    b2 = w.s([b1, w.s([], 'anass', '( ( ( y e. %s /\\ %s ) /\\ %s ) <-> ( y e. %s /\\ ( %s /\\ %s ) ) )' % (ZFX('X'), n2, n1, ZFX('X'), n2, n1))], 'bitri',
             '( y e. %s <-> ( y e. %s /\\ ( %s /\\ %s ) ) )' % (FB('m'), ZFX('X'), n2, n1))
    b3 = w.s([b2, e3_], 'bitr4i', '( y e. %s <-> y e. %s )' % (FB('m'), CELL('X', 'm')))
    fcx = w.s([b3], 'eqriv', '%s = %s' % (FB('m'), CELL('X', 'm')))
    fc = cm.a1(fcx, '%s = %s' % (FB('m'), CELL('X', 'm')))
    s3 = c([cm([fc], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (FB('m'), ORDX('X', 'q'), CELL('X', 'm'), ORDX('X', 'q')))], 'sumeq2dv',
           'sum_ m e. %s sum_ q e. %s %s = sum_ m e. %s sum_ q e. %s %s' % (FZ, FB('m'), ORDX('X', 'q'), FZ, CELL('X', 'm'), ORDX('X', 'q')))
    fin = c([c([s1, fi], 'eqtrd', 'sum_ q e. %s %s = sum_ m e. %s sum_ q e. %s %s' % (GXX, ORDX('X', 'q'), FZ, FB('m'), ORDX('X', 'q'))), s3], 'eqtrd', ante_of(S['zrfib'])[1])
    w.qed([fin], 'idi', S['zrfib'])
    return run8(w)


GENS = {'zrfib': gen_fib}


def gen_cb():
    from ef4_g import elrab_pack
    from zr_k import cell_facts
    w = W('zrcb', 'A nonempty cell ` m ` of a character carries at most one local count: its mass is ` <_ B ` when every local count at a height ` abs u <_ T ` is ` <_ B ` (the ` hS_le ` step of Lean ` sum_good_le_of_localCount ` ; ~ zrc1 ).')
    A0 = ante_of(S['zrcb'])[0]
    c = Ctx(w, A0)
    nn_, xb, sr, s0, s1, tr, t0 = [c.g(x) for x in ('N e. NN', 'X e. ( Base ` ( DChr ` N ) )', 'S e. RR', '0 < S', 'S <_ 1', 'T e. RR', '0 <_ T')]
    br = c.g('B e. RR')
    ALU = 'A. u e. RR ( ( abs ` u ) <_ T -> %s <_ B )' % LCX('X', 'u')
    alu = c.g(ALU); mz = c.g('M e. ZZ'); cn = c.g('%s =/= (/)' % CELL('X', 'M'))
    nxb = c([nn_, xb], 'jca', NX)
    zfin, zal = zf_facts(w, A0, nxb, sr, s0, s1, tr)
    CM = CELL('X', 'M')
    ex0 = c([cn, w.s([], 'n0', '( %s =/= (/) <-> E. z z e. %s )' % (CM, CM))], 'sylib', 'E. z z e. %s' % CM)
    GOAL = ante_of(S['zrcb'])[1]
    A0p = '( ( %s /\\ %s ) /\\ ( M e. ZZ /\\ %s =/= (/) ) )' % (NX, BOX01, CM)
    Azf = '( %s /\\ z e. %s )' % (A0, CM)
    Az = '( %s /\\ z e. %s )' % (A0p, CM)
    cp = Ctx(w, A0p)
    nn_, xb, sr, s0, s1, tr, t0 = [cp.g(x) for x in ('N e. NN', 'X e. ( Base ` ( DChr ` N ) )', 'S e. RR', '0 < S', 'S <_ 1', 'T e. RR', '0 <_ T')]
    nxb = cp([nn_, xb], 'jca', NX)
    zfin, zal = zf_facts(w, A0p, nxb, sr, s0, s1, tr)
    cz = Ctx(w, Az)
    Lz = lambda st: lift(w, st, Az)
    fz = cell_facts(w, Az, cz([], 'simpr', 'z e. %s' % CM), 'z', 'X', 'M', Lz(sr), Lz(tr))
    IZ = '( Im ` z )'
    WZ = '{ v e. %s | ( abs ` ( ( Im ` v ) - %s ) ) <_ ( 1 / %s ) }' % (ZFX('X'), IZ, LD)
    # CELL C_ W ( z )
    Ay = '( %s /\\ y e. %s )' % (Az, CM)
    cy = Ctx(w, Ay)
    Ly = lambda st: lift(w, st, Ay)
    fy = cell_facts(w, Ay, cy([], 'simpr', 'y e. %s' % CM), 'y', 'X', 'M', Ly(sr), Ly(tr))
    C1 = ante_of(tsub(S['zrc1'], {'A': 'y', 'B': 'z'}))
    _d2, _lr, _lp, _dr = scale_facts(w, Ay, Ly(nn_), Ly(tr), Ly(t0))
    sfl = (_lr, cy([_lp], 'gt0ne0d', '%s =/= 0' % LD))
    pre = cy([Ly(nn_), cy([Ly(tr), Ly(t0)], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    ie = cy([fy['idx'], cy([Ly(fz['idx'])], 'eqcomd', 'M = %s' % IDX('z'))], 'eqtrd', '%s = %s' % (IDX('y'), IDX('z')))
    c1 = cy([cy([cy([pre, cy([fy['cc'], fy['im']], 'jca', PTB('y')), cy([Ly(fz['cc']), Ly(fz['im'])], 'jca', PTB('z'))], '3jca', top_and(C1[0])[0]), ie], 'jca', C1[0]), w.inst('zrc1')], 'syl', C1[1])
    yw = elrab_pack(w, Ay, 'v', ZFX('X'), '( abs ` ( ( Im ` v ) - %s ) ) <_ ( 1 / %s )' % (IZ, LD), 'y', fy['zf'], cy([cy([cy([fy['imr'], Ly(fz['imr'])], 'resubcld', '( ( Im ` y ) - %s ) e. RR' % IZ)], 'recnd', '( ( Im ` y ) - %s ) e. CC' % IZ)], 'abscld', '( abs ` ( ( Im ` y ) - %s ) ) e. RR' % IZ) and
                  cy([cy([cy([cy([fy['imr'], Ly(fz['imr'])], 'resubcld', '( ( Im ` y ) - %s ) e. RR' % IZ)], 'recnd', '( ( Im ` y ) - %s ) e. CC' % IZ)], 'abscld', '( abs ` ( ( Im ` y ) - %s ) ) e. RR' % IZ),
                      cy([cy([], '1red', '1 e. RR'), sfl[0], sfl[1]], 'redivcld', '( 1 / %s ) e. RR' % LD), c1], 'ltled', '( abs ` ( ( Im ` y ) - %s ) ) <_ ( 1 / %s )' % (IZ, LD)))
    ss = cz([w.s([yw], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (Az, CM, WZ))], 'ssrdv', '%s C_ %s' % (CM, WZ))
    wss = cz.a1(w.s([], 'ssrab2', '%s C_ %s' % (WZ, ZFX('X'))), '%s C_ %s' % (WZ, ZFX('X')))
    wfin = cz([Lz(zfin), wss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % WZ)
    Aq = '( %s /\\ q e. %s )' % (A0p, ZFX('X'))
    on = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Aq, ORDX('X', 'q')))
    Azq = '( %s /\\ q e. %s )' % (Az, WZ)
    czq = Ctx(w, Azq)
    onq = czq([czq([czq.g(A0p), czq([lift(w, wss, Azq), czq([], 'simpr', 'q e. %s' % WZ)], 'sseldd', 'q e. %s' % ZFX('X'))], 'jca', Aq), on], 'syl', '%s e. NN' % ORDX('X', 'q'))
    fl = cz([wfin, czq([onq], 'nnred', '%s e. RR' % ORDX('X', 'q')), czq([czq([onq], 'nnnn0d', '%s e. NN0' % ORDX('X', 'q'))], 'nn0ge0d', '0 <_ %s' % ORDX('X', 'q')), ss], 'fsumless',
            'sum_ q e. %s %s <_ %s' % (CM, ORDX('X', 'q'), LCX('X', IZ)))
    body = '( ( abs ` u ) <_ T -> %s <_ B )' % LCX('X', 'u')
    czf = Ctx(w, Azf)
    brg = czf([czf([czf([czf.g(NX), czf.g(BOX01)], 'jca', '( %s /\\ %s )' % (NX, BOX01)), czf([czf.g('M e. ZZ'), czf.g('%s =/= (/)' % CM)], 'jca', '( M e. ZZ /\\ %s =/= (/) )' % CM)], 'jca', A0p),
               czf([], 'simpr', 'z e. %s' % CM)], 'jca', Az)
    R_ = lambda st: w.s([brg, st], 'syl', '( %s -> %s )' % (Azf, strip_ante(formula_of(w, st), Az)))
    inu, newu = ral_at(w, Azf, lift(w, alu, Azf), 'u', IZ, body, R_(fz['imr']))
    lcb = czf([R_(fz['im']), inu], 'mpd', '%s <_ B' % LCX('X', IZ))
    Acq = '( %s /\\ q e. %s )' % (Az, CM)
    ccq = Ctx(w, Acq)
    onc = ccq([ccq([ccq.g(A0p), ccq([lift(w, wss, Acq), ccq([lift(w, ss, Acq), ccq([], 'simpr', 'q e. %s' % CM)], 'sseldd', 'q e. %s' % WZ)], 'sseldd', 'q e. %s' % ZFX('X'))], 'jca', Aq), on], 'syl', '%s e. NN' % ORDX('X', 'q'))
    cfin = cz([wfin, ss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % CM)
    s1r = cz([cfin, ccq([onc], 'nnred', '%s e. RR' % ORDX('X', 'q'))], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (CM, ORDX('X', 'q')))
    lcr = cz([wfin, czq([onq], 'nnred', '%s e. RR' % ORDX('X', 'q'))], 'fsumrecl', '%s e. RR' % LCX('X', IZ))
    gz = lin8(w, Azf, [R_(fl), lcb], GOAL, {'sum_ q e. %s %s' % (CM, ORDX('X', 'q')): R_(s1r), LCX('X', IZ): R_(lcr), 'B': lift(w, br, Azf)})
    fin = c([ex0, c([w.s([gz], 'ex', '( %s -> ( z e. %s -> %s ) )' % (A0, CM, GOAL))], 'exlimdv', '( E. z z e. %s -> %s )' % (CM, GOAL))], 'mpd', GOAL)
    w.qed([fin], 'idi', S['zrcb'])
    return run8(w)


GENS['zrcb'] = gen_cb


def gen_cov():
    from zr_k import ri_facts
    w = W('zrcov', 'Lean ` sum_good_le_of_localCount ` (blueprint 7.2(a), abstract form): if every local count at a height ` abs u <_ T ` is ` <_ B ` for the characters of ` Y ` , the good zero mass over ` Y ` is ` <_ B ( J_ev + J_od ) ` ( ~ zrfib , ~ zrcb , ~ fsumxp ).')
    A0 = ante_of(S['zrcov'])[0]
    GOAL = ante_of(S['zrcov'])[1]
    c = Ctx(w, A0)
    FZ = '( 0 ... %s )' % QP
    XPY = '( Y X. %s )' % FZ
    SC = lambda P: 'sum_ q e. %s %s' % (CELL('( 1st ` %s )' % P, '( 2nd ` %s )' % P), ORDX('( 1st ` %s )' % P, 'q'))
    SCxm = 'sum_ q e. %s %s' % (CELL('x', 'm'), ORDX('x', 'q'))
    # --- the sum identities, in the context without the local-count hypothesis
    A0p = '( ( %s /\\ %s ) /\\ B e. RR )' % (NY, BOX01)
    cp = Ctx(w, A0p)
    nn_, ys, yf, sr, s0, s1, tr, t0, br = [cp.g(x) for x in ('N e. NN', 'Y C_ ( Base ` ( DChr ` N ) )', 'Y e. Fin', 'S e. RR', '0 < S', 'S <_ 1', 'T e. RR', '0 <_ T', 'B e. RR')]
    box = cp([cp([sr, s0, s1], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), cp([tr, t0], 'jca', TT)], 'jca', BOX01)
    Ax = '( %s /\\ x e. Y )' % A0p
    cx = Ctx(w, Ax)
    xb = cx([lift(w, ys, Ax), cx([], 'simpr', 'x e. Y')], 'sseldd', 'x e. ( Base ` ( DChr ` N ) )')
    FA = ante_of(tsub(S['zrfib'], {'X': 'x'}))
    fb = cx([cx([cx([lift(w, nn_, Ax), xb], 'jca', tsub(NX, {'X': 'x'})), lift(w, box, Ax)], 'jca', FA[0]), w.inst('zrfib')], 'syl', FA[1])
    e1 = cp([fb], 'sumeq2dv', '%s = sum_ x e. Y sum_ m e. %s %s' % (GOODS('Y'), FZ, SCxm))
    # fsumxp
    Apr = 'p = <. x , m >.'
    s1st = w.s([w.s([], 'fveq2', '( %s -> ( 1st ` p ) = ( 1st ` <. x , m >. ) )' % Apr), w.s([w.s([], 'vex', 'x e. _V'), w.s([], 'vex', 'm e. _V')], 'op1st', '( 1st ` <. x , m >. ) = x')], 'eqtrdi', '( %s -> ( 1st ` p ) = x )' % Apr)
    s2nd = w.s([w.s([], 'fveq2', '( %s -> ( 2nd ` p ) = ( 2nd ` <. x , m >. ) )' % Apr), w.s([w.s([], 'vex', 'x e. _V'), w.s([], 'vex', 'm e. _V')], 'op2nd', '( 2nd ` <. x , m >. ) = m')], 'eqtrdi', '( %s -> ( 2nd ` p ) = m )' % Apr)
    eqp, newp = w.congr(SC('p'), {}, Apr, {}, rules={'( 1st ` p )': ('x', s1st), '( 2nd ` p )': ('m', s2nd)})
    assert newp == SCxm, (newp, SCxm)
    Axm = '( %s /\\ ( x e. Y /\\ m e. %s ) )' % (A0p, FZ)
    cxm = Ctx(w, Axm)
    xb2 = cxm([lift(w, ys, Axm), cxm.g('x e. Y')], 'sseldd', 'x e. ( Base ` ( DChr ` N ) )')
    zfin, zal = zf_facts(w, Axm, cxm([lift(w, nn_, Axm), xb2], 'jca', tsub(NX, {'X': 'x'})), lift(w, sr, Axm), lift(w, s0, Axm), lift(w, s1, Axm), lift(w, tr, Axm), 'x')
    cfin = cxm([zfin, cxm.a1(w.s([], 'ssrab2', '%s C_ %s' % (CELL('x', 'm'), ZFX('x'))), '%s C_ %s' % (CELL('x', 'm'), ZFX('x'))), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % CELL('x', 'm'))
    Axmq = '( %s /\\ q e. %s )' % (Axm, CELL('x', 'm'))
    cq = Ctx(w, Axmq)
    Aq = '( %s /\\ q e. %s )' % (Axm, ZFX('x'))
    on = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Aq, ORDX('x', 'q')))
    onq = cq([cq([cq.g(Axm), cq([cq([], 'simpr', 'q e. %s' % CELL('x', 'm')), w.inst('elrabi')], 'syl', 'q e. %s' % ZFX('x'))], 'jca', Aq), on], 'syl', '%s e. NN' % ORDX('x', 'q'))
    scc = cxm([cfin, cq([onq], 'nncnd', '%s e. CC' % ORDX('x', 'q'))], 'fsumcl', '%s e. CC' % SCxm)
    xpf = cp([yf, cp([], 'fzfid', '%s e. Fin' % FZ), w.inst('xpfi')], 'syl2anc', '%s e. Fin' % XPY)
    e2 = cp([eqp, yf, cp([], 'fzfid', '%s e. Fin' % FZ), scc], 'fsumxp', 'sum_ x e. Y sum_ m e. %s %s = sum_ p e. %s %s' % (FZ, SCxm, XPY, SC('p')))
    TP = '{ j e. %s | %s =/= (/) }' % (XPY, CELL('( 1st ` j )', '( 2nd ` j )'))
    TPp = '{ p e. %s | %s =/= (/) }' % (XPY, CELL('( 1st ` p )', '( 2nd ` p )'))
    from ef3lib import elrab_
    elTP, _nb = elrab_(w, 'j', XPY, '%s =/= (/)' % CELL('( 1st ` j )', '( 2nd ` j )'), 'p')
    def sc_facts(Ab, pin_xpy):
        cb = Ctx(w, Ab)
        p1 = cb([pin_xpy, w.inst('xp1st')], 'syl', '( 1st ` p ) e. Y')
        p2 = cb([pin_xpy, w.inst('xp2nd')], 'syl', '( 2nd ` p ) e. %s' % FZ)
        xb_ = cb([lift(w, ys, Ab), p1], 'sseldd', '( 1st ` p ) e. ( Base ` ( DChr ` N ) )')
        nxp = cb([lift(w, nn_, Ab), xb_], 'jca', tsub(NX, {'X': '( 1st ` p )'}))
        zf_, za_ = zf_facts(w, Ab, nxp, lift(w, sr, Ab), lift(w, s0, Ab), lift(w, s1, Ab), lift(w, tr, Ab), '( 1st ` p )')
        CP = CELL('( 1st ` p )', '( 2nd ` p )')
        cf_ = cb([zf_, cb.a1(w.s([], 'ssrab2', '%s C_ %s' % (CP, ZFX('( 1st ` p )'))), '%s C_ %s' % (CP, ZFX('( 1st ` p )'))), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % CP)
        Abq = '( %s /\\ q e. %s )' % (Ab, CP)
        cbq = Ctx(w, Abq)
        Az_ = '( %s /\\ q e. %s )' % (Ab, ZFX('( 1st ` p )'))
        on_ = w.s([za_], 'r19.21bi', '( %s -> %s e. NN )' % (Az_, ORDX('( 1st ` p )', 'q')))
        onq_ = cbq([cbq([cbq.g(Ab), cbq([cbq([], 'simpr', 'q e. %s' % CP), w.inst('elrabi')], 'syl', 'q e. %s' % ZFX('( 1st ` p )'))], 'jca', Az_), on_], 'syl', '%s e. NN' % ORDX('( 1st ` p )', 'q'))
        scr = cb([cf_, cbq([onq_], 'nnred', '%s e. RR' % ORDX('( 1st ` p )', 'q'))], 'fsumrecl', '%s e. RR' % SC('p'))
        return scr, p1, p2, nxp
    Apx = '( %s /\\ p e. %s )' % (A0p, XPY)
    cpx = Ctx(w, Apx)
    scr_x, _, _, _ = sc_facts(Apx, cpx([], 'simpr', 'p e. %s' % XPY))
    Apd = '( %s /\\ p e. ( %s \\ %s ) )' % (A0p, XPY, TP)
    cpd = Ctx(w, Apd)
    pd = cpd([], 'simpr', 'p e. ( %s \\ %s )' % (XPY, TP))
    pdx = cpd([pd], 'eldifad', 'p e. %s' % XPY)
    pnt = cpd([pd], 'eldifbd', '-. p e. %s' % TP)
    CP = CELL('( 1st ` p )', '( 2nd ` p )')
    from ef4_g import elrab_pack
    # CP = (/): otherwise p e. TP
    Apn = '( %s /\\ %s =/= (/) )' % (Apd, CP)
    rb = elTP
    pin = w.s([w.s([lift(w, pdx, Apn), w.s([], 'simpr', '( %s -> %s =/= (/) )' % (Apn, CP))], 'jca', '( %s -> ( p e. %s /\\ %s =/= (/) ) )' % (Apn, XPY, CP)), rb], 'sylibr', '( %s -> p e. %s )' % (Apn, TP))
    nne = cpd([w.s([pin], 'ex', '( %s -> ( %s =/= (/) -> p e. %s ) )' % (Apd, CP, TP)), pnt], 'mtod', '-. %s =/= (/)' % CP)
    cz = cpd([nne, w.s([], 'nne', '( -. %s =/= (/) <-> %s = (/) )' % (CP, CP))], 'sylib', '%s = (/)' % CP)
    s0_ = cpd([cpd([cz], 'sumeq1d', '%s = sum_ q e. (/) %s' % (SC('p'), ORDX('( 1st ` p )', 'q'))), cpd.a1(w.s([], 'sum0', 'sum_ q e. (/) %s = 0' % ORDX('( 1st ` p )', 'q')), 'sum_ q e. (/) %s = 0' % ORDX('( 1st ` p )', 'q'))],
              'eqtrd', '%s = 0' % SC('p'))
    tss = cp.a1(w.s([], 'ssrab2', '%s C_ %s' % (TP, XPY)), '%s C_ %s' % (TP, XPY))
    Apt = '( %s /\\ p e. %s )' % (A0p, TP)
    cpt = Ctx(w, Apt)
    ptx = cpt([lift(w, tss, Apt), cpt([], 'simpr', 'p e. %s' % TP)], 'sseldd', 'p e. %s' % XPY)
    scr_t, p1t, p2t, nxpt = sc_facts(Apt, ptx)
    e3 = cp([tss, cpt([scr_t], 'recnd', '%s e. CC' % SC('p')), s0_, xpf], 'fsumss', 'sum_ p e. %s %s = sum_ p e. %s %s' % (TP, SC('p'), XPY, SC('p')))
    # TP = RI0 u. RI1, disjoint
    PH = '%s =/= (/)' % CP
    P0, P1 = '( ( 2nd ` p ) mod 2 ) = 0', '( ( 2nd ` p ) mod 2 ) = 1'
    un = w.s([], 'unrab', '( %s u. %s ) = { p e. %s | ( ( %s /\\ %s ) \\/ ( %s /\\ %s ) ) }' % (RI('0'), RI('1'), XPY, PH, P0, PH, P1))
    p2z = cpx([cpx([cpx([], 'simpr', 'p e. %s' % XPY), w.inst('xp2nd')], 'syl', '( 2nd ` p ) e. %s' % FZ), w.inst('elfzelz')], 'syl', '( 2nd ` p ) e. ZZ')
    o0 = cpx([p2z, w.inst('mod2eq0even')], 'syl', '( %s <-> 2 || ( 2nd ` p ) )' % P0)
    o1 = cpx([p2z, w.inst('mod2eq1n2dvds')], 'syl', '( %s <-> -. 2 || ( 2nd ` p ) )' % P1)
    ex_ = cpx.a1(w.s([], 'exmid', '( 2 || ( 2nd ` p ) \\/ -. 2 || ( 2nd ` p ) )'), '( 2 || ( 2nd ` p ) \\/ -. 2 || ( 2nd ` p ) )')
    o01 = cpx([ex_, cpx([o0, o1], 'orbi12d', '( ( %s \\/ %s ) <-> ( 2 || ( 2nd ` p ) \\/ -. 2 || ( 2nd ` p ) ) )' % (P0, P1))], 'mpbird', '( %s \\/ %s )' % (P0, P1))
    bi = cpx([cpx([o01, w.inst('iba')], 'syl', '( %s <-> ( %s /\\ ( %s \\/ %s ) ) )' % (PH, PH, P0, P1)), cpx.a1(w.s([], 'andi', '( ( %s /\\ ( %s \\/ %s ) ) <-> ( ( %s /\\ %s ) \\/ ( %s /\\ %s ) ) )' % (PH, P0, P1, PH, P0, PH, P1)),
                                                                                                    '( ( %s /\\ ( %s \\/ %s ) ) <-> ( ( %s /\\ %s ) \\/ ( %s /\\ %s ) ) )' % (PH, P0, P1, PH, P0, PH, P1))],
              'bitrd', '( %s <-> ( ( %s /\\ %s ) \\/ ( %s /\\ %s ) ) )' % (PH, PH, P0, PH, P1))
    rb2 = cp([bi], 'rabbidva', '%s = { p e. %s | ( ( %s /\\ %s ) \\/ ( %s /\\ %s ) ) }' % (TPp, XPY, PH, P0, PH, P1))
    tu = cp([rb2, cp.a1(un, '( %s u. %s ) = { p e. %s | ( ( %s /\\ %s ) \\/ ( %s /\\ %s ) ) }' % (RI('0'), RI('1'), XPY, PH, P0, PH, P1))], 'eqtr4d', '%s = ( %s u. %s )' % (TPp, RI('0'), RI('1')))
    s1j = w.s([w.s([], 'id', '( j = p -> j = p )')], 'fveq2d', '( j = p -> ( 1st ` j ) = ( 1st ` p ) )')
    s2j = w.s([w.s([], 'id', '( j = p -> j = p )')], 'fveq2d', '( j = p -> ( 2nd ` j ) = ( 2nd ` p ) )')
    ceq, cnew = w.congr(CELL('( 1st ` j )', '( 2nd ` j )'), {}, 'j = p', {}, rules={'( 1st ` j )': ('( 1st ` p )', s1j), '( 2nd ` j )': ('( 2nd ` p )', s2j)})
    assert cnew == CP, cnew
    cbj = w.s([w.s([ceq], 'neeq1d', '( j = p -> ( %s =/= (/) <-> %s =/= (/) ) )' % (CELL('( 1st ` j )', '( 2nd ` j )'), CP))], 'cbvrabv', '%s = %s' % (TP, TPp))
    tu = cp([cp.a1(cbj, '%s = %s' % (TP, TPp)), tu], 'eqtrd', '%s = ( %s u. %s )' % (TP, RI('0'), RI('1')))
    inr = w.s([], 'inrab', '( %s i^i %s ) = { p e. %s | ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) }' % (RI('0'), RI('1'), XPY, PH, P0, PH, P1))
    APP = '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (PH, P0, PH, P1)
    Aa = '( %s /\\ %s )' % (Apx, APP)
    ca_ = Ctx(w, Aa)
    zz = ca_([ca_([ca_.g(P0)], 'eqcomd', '0 = ( ( 2nd ` p ) mod 2 )'), ca_.g(P1)], 'eqtrd', '0 = 1')
    ALL = cp([cpx([w.s([zz], 'ex', '( %s -> ( %s -> 0 = 1 ) )' % (Apx, APP)), cpx.a1(w.s([w.s([], '0ne1', '0 =/= 1')], 'neii', '-. 0 = 1'), '-. 0 = 1')], 'mtod', '-. %s' % APP)], 'ralrimiva', 'A. p e. %s -. %s' % (XPY, APP))
    r0 = cp([ALL, w.s([], 'rabeq0', '( { p e. %s | %s } = (/) <-> A. p e. %s -. %s )' % (XPY, APP, XPY, APP))], 'sylibr', '{ p e. %s | %s } = (/)' % (XPY, APP))
    dis = cp([cp.a1(inr, '( %s i^i %s ) = { p e. %s | %s }' % (RI('0'), RI('1'), XPY, APP)), r0], 'eqtrd', '( %s i^i %s ) = (/)' % (RI('0'), RI('1')))
    f0 = cp([xpf, cp.a1(w.s([], 'ssrab2', '%s C_ %s' % (RI('0'), XPY)), '%s C_ %s' % (RI('0'), XPY)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % RI('0'))
    f1 = cp([xpf, cp.a1(w.s([], 'ssrab2', '%s C_ %s' % (RI('1'), XPY)), '%s C_ %s' % (RI('1'), XPY)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % RI('1'))
    hu = cp([f0, f1, dis, w.inst('hashun')], 'syl3anc', '( # ` ( %s u. %s ) ) = ( ( # ` %s ) + ( # ` %s ) )' % (RI('0'), RI('1'), RI('0'), RI('1')))
    ht = cp([cp([tu], 'fveq2d', '( # ` %s ) = ( # ` ( %s u. %s ) )' % (TP, RI('0'), RI('1'))), hu], 'eqtrd', '( # ` %s ) = %s' % (TP, JJ))
    tfin = cp([xpf, tss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % TP)
    cst = cp([tfin, cp([br], 'recnd', 'B e. CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ p e. %s B = ( ( # ` %s ) x. B )' % (TP, TP))
    # --- in the full context
    brg = c([c([c.g(NY), c.g(BOX01)], 'jca', '( %s /\\ %s )' % (NY, BOX01)), c.g('B e. RR')], 'jca', A0p)
    R_ = lambda st: c([brg, st], 'syl', strip_ante(formula_of(w, st), A0p))
    Ap = '( %s /\\ p e. %s )' % (A0, TP)
    cpp = Ctx(w, Ap)
    brgp = cpp([lift(w, brg, Ap), cpp([], 'simpr', 'p e. %s' % TP)], 'jca', Apt)
    Rp = lambda st: cpp([brgp, st], 'syl', strip_ante(formula_of(w, st), Apt))
    HYP = 'A. x e. Y A. u e. RR ( ( abs ` u ) <_ T -> %s <_ B )' % LCX('x', 'u')
    hyp = cpp.g(HYP)
    bodyx = 'A. u e. RR ( ( abs ` u ) <_ T -> %s <_ B )' % LCX('x', 'u')
    alx, newx = ral_at(w, Ap, hyp, 'x', '( 1st ` p )', bodyx, Rp(p1t))
    cne = cpp([cpp([cpp([], 'simpr', 'p e. %s' % TP), elTP], 'sylib', '( p e. %s /\\ %s =/= (/) )' % (XPY, CP))], 'simprd', '%s =/= (/)' % CP)
    CBA = ante_of(tsub(S['zrcb'], {'X': '( 1st ` p )', 'M': '( 2nd ` p )'}))
    Q_ = top_and(CBA[0])
    cb1 = cpp([cpp([Rp(nxpt), cpp([cpp([cpp.g('S e. RR'), cpp.g('0 < S'), cpp.g('S <_ 1')], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), cpp([cpp.g('T e. RR'), cpp.g('0 <_ T')], 'jca', TT)], 'jca', BOX01)], 'jca', Q_[0]),
               cpp([cpp([cpp.g('B e. RR'), alx], 'jca', top_and(Q_[1])[0]), cpp([cpp([Rp(p2t), w.inst('elfzelz')], 'syl', '( 2nd ` p ) e. ZZ'), cne], 'jca', top_and(Q_[1])[1])], 'jca', Q_[1])], 'jca', CBA[0])
    scb = cpp([cb1, w.inst('zrcb')], 'syl', CBA[1])
    fle = c([R_(tfin), Rp(scr_t), lift(w, c.g('B e. RR'), Ap), scb], 'fsumle', 'sum_ p e. %s %s <_ sum_ p e. %s B' % (TP, SC('p'), TP))
    SG = GOODS('Y'); SXP = 'sum_ p e. %s %s' % (XPY, SC('p')); STP = 'sum_ p e. %s %s' % (TP, SC('p'))
    eqa = c([c([R_(e1), R_(e2)], 'eqtrd', '%s = %s' % (SG, SXP)), c([R_(e3)], 'eqcomd', '%s = %s' % (SXP, STP))], 'eqtrd', '%s = %s' % (SG, STP))
    htb = c([R_(ht)], 'oveq1d', '( ( # ` %s ) x. B ) = ( %s x. B )' % (TP, JJ))
    stpr = c([R_(tfin), Rp(scr_t)], 'fsumrecl', '%s e. RR' % STP)
    j0r = c([c([R_(f0), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RI('0'))], 'nn0red', '( # ` %s ) e. RR' % RI('0'))
    j1r = c([c([R_(f1), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RI('1'))], 'nn0red', '( # ` %s ) e. RR' % RI('1'))
    jtr = c([c([R_(tfin), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TP)], 'nn0red', '( # ` %s ) e. RR' % TP)
    sgr = c([eqa, stpr], 'eqeltrd', '%s e. RR' % SG)
    lv = {SG: sgr, STP: stpr, 'sum_ p e. %s B' % TP: c([R_(tfin), cpp.g('B e. RR')], 'fsumrecl', 'sum_ p e. %s B e. RR' % TP),
          '( # ` %s )' % RI('0'): j0r, '( # ` %s )' % RI('1'): j1r, '( # ` %s )' % TP: jtr, 'B': c.g('B e. RR')}
    fin = lin8(w, A0, [eqa, fle, R_(cst), htb], GOAL, lv, products=True)
    w.qed([fin], 'idi', S['zrcov'])
    return run8(w)


GENS['zrcov'] = gen_cov


def gen_sg():
    w = W('zrsg', 'Lean ` sum_good_le ` (blueprint 7.2(a) with Lemma 7.1): the good zero mass over ` Y ` is ` <_ Cloc ( 1 + ( 1 - S ) L ) ( J_ev + J_od ) ` for ` 99 / 100 <_ S <_ 1 ` , ` L >_ 25 ` ( ~ zrcov , ~ zrlc ).')
    A0 = ante_of(S['zrsg'])[0]
    c = Ctx(w, A0)
    nn_, ys, yf, sr, s99, s1, tr, t0, l25 = [c.g(x) for x in ('N e. NN', 'Y C_ ( Base ` ( DChr ` N ) )', 'Y e. Fin', 'S e. RR', '( ; 9 9 / ; ; 1 0 0 ) <_ S', 'S <_ 1', 'T e. RR', '0 <_ T', '; 2 5 <_ %s' % LD)]
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    B = '( %s x. ( 1 + %s ) )' % (CLOC, LAM)
    cl = Closure(w, A0, {LD: ('RR', lr), 'S': ('RR', sr)})
    cl.atom(LD); cl.atom('S')
    bre = cl.mem(B, 'RR')
    Axu = '( ( ( %s /\\ x e. Y ) /\\ u e. RR ) /\\ ( abs ` u ) <_ T )' % A0
    cu = Ctx(w, Axu)
    xb = cu([lift(w, ys, Axu), cu.g('x e. Y')], 'sseldd', 'x e. ( Base ` ( DChr ` N ) )')
    LA = ante_of(tsub(S['zrlc'], {'X': 'x', 'U': 'u'}))
    Q = top_and(LA[0])
    lc = cu([cu([cu([cu.g('N e. NN'), xb], 'jca', Q[0]), cu([cu([cu.g('S e. RR'), cu([cu.g('( ; 9 9 / ; ; 1 0 0 ) <_ S'), cu.g('S <_ 1')], 'jca', '( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 )')], 'jca', SS),
                                                              cu([cu.g('T e. RR'), cu.g('0 <_ T')], 'jca', TT)], 'jca', Q[1]),
                  cu([cu.g('; 2 5 <_ %s' % LD), cu([cu.g('u e. RR'), cu.g('( abs ` u ) <_ T')], 'jca', '( u e. RR /\\ ( abs ` u ) <_ T )')], 'jca', Q[2])], '3jca', LA[0]), w.inst('zrlc')], 'syl', LA[1])
    al = c([w.s([w.s([lc], 'ex', '( ( ( %s /\\ x e. Y ) /\\ u e. RR ) -> ( ( abs ` u ) <_ T -> %s <_ %s ) )' % (A0, LCX('x', 'u'), B))], 'ralrimiva',
                '( ( %s /\\ x e. Y ) -> A. u e. RR ( ( abs ` u ) <_ T -> %s <_ %s ) )' % (A0, LCX('x', 'u'), B))], 'ralrimiva', 'A. x e. Y A. u e. RR ( ( abs ` u ) <_ T -> %s <_ %s )' % (LCX('x', 'u'), B))
    CA = ante_of(tsub(S['zrcov'], {'B': B}))
    P_ = top_and(CA[0])
    s0 = lin8(w, A0, [s99], '0 < S', {'S': sr})
    ca = c([c.g(NY), c([c([sr, s0, s1], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), c([tr, t0], 'jca', TT)], 'jca', BOX01)], 'jca', P_[0])
    fin = c([c([ca, c([bre, al], 'jca', P_[1])], 'jca', CA[0]), w.inst('zrcov')], 'syl', CA[1])
    w.qed([fin], 'idi', S['zrsg'])
    return run8(w)


GENS['zrsg'] = gen_sg


def gen_szc():
    w = W('zrszc', 'Lean ` sum_zeroCountBox_le ` (Theorem M instance, ` good := True ` , here ` G = CC ` ): ` sum_ x N ( S , T , x ) <_ Cloc ( 1 + ( 1 - S ) L ) ( J_ev + J_od ) ` ( ~ zrsg ).')
    A0 = ante_of(S['zrszc'])[0]
    c = Ctx(w, A0)
    sr, tr = c.g('S e. RR'), c.g('T e. RR')
    SGA = ante_of(tsub(S['zrsg'], {'G': 'CC'}))
    sg = c([c([], 'id', A0), w.inst('zrsg')], 'syl', SGA[1])
    Ax = '( %s /\\ x e. Y )' % A0
    cx = Ctx(w, Ax)
    ic = cx.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    CA, CB = '( S + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    cac = cx([cx([lift(w, sr, Ax)], 'recnd', 'S e. CC'), cx([ic, cx([cx([lift(w, tr, Ax)], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = cx([cx([], '1cnd', '1 e. CC'), cx([ic, cx([lift(w, tr, Ax)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CB)
    bss = cx([cac, cbc, w.inst('crectss')], 'syl2anc', '%s C_ CC' % BOXR)
    zss = cx([cx.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZFX('x'), BOXR)), '%s C_ %s' % (ZFX('x'), BOXR)), bss], 'sstrd', '%s C_ CC' % ZFX('x'))
    Av = '( %s /\\ v e. %s )' % (Ax, ZFX('x'))
    vc = w.s([lift(w, zss, Av), w.s([], 'simpr', '( %s -> v e. %s )' % (Av, ZFX('x')))], 'sseldd', '( %s -> v e. CC )' % Av)
    al = cx([vc], 'ralrimiva', 'A. v e. %s v e. CC' % ZFX('x'))
    GCC = '{ v e. %s | v e. CC }' % ZFX('x')
    ge = cx([al, w.s([], 'rabid2', '( %s = %s <-> A. v e. %s v e. CC )' % (ZFX('x'), GCC, ZFX('x')))], 'sylibr', '%s = %s' % (ZFX('x'), GCC))
    se = c([cx([ge], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (ZFX('x'), ORDX('x', 'q'), GCC, ORDX('x', 'q')))], 'sumeq2dv',
           'sum_ x e. Y sum_ q e. %s %s = %s' % (ZFX('x'), ORDX('x', 'q'), tsub(GOODS('Y'), {'G': 'CC'})))
    fin = c([se, sg], 'eqbrtrd', ante_of(S['zrszc'])[1])
    w.qed([fin], 'idi', S['zrszc'])
    return run8(w)


GENS['zrszc'] = gen_szc
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
