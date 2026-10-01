"""Sortie LDEN, part e: the logged local count (Lemma 3.1), the two covering instances of ~ zrcov, Theorem L and the
headline: ldenwin ldenlc1 ldenlc0 ldenlc ldenlow ldenin1 ldenin0 ldene40 ldenlarge ldensmall ldenld ldenledg ldencbv loggeddensity.

    MM_DB=sorties/lden.mm MM_ENGINE=mmatch python3 tools/gen/lden_e.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ldenlib import *
import ldenlib as LL
from zrlib import ZSE, LCX, GX, GOODS, JJ, LT2, HOLF
from ef4_g import elrab_unpack, elrab_pack
from ef3lib import elrab_
from lden_a import sc_facts, num8
from zr_i import scale_facts
from zr_j import box_facts, sq_memU, LFNX
from zr_l import zf_facts
from zr_k import ri_facts, cell_facts
import lin as _lin
_lin.MAXPOW = 20
_lin.MAXDEG = 20

only = sys.argv[1:]
S = STATEMENTS
E0 = EX('X')                                     # ( N DChrLF X )
EZ = EX(ZG)                                      # the principal L-function
IL = '( 1 / %s )' % LD
WIN = lambda X='X': '{ v e. %s | ( abs ` ( ( Im ` v ) - U ) ) <_ %s }' % (ZFX(X), IL)
LNU = '( log ` ( N x. ( ( abs ` U ) + 2 ) ) )'
L800 = '( ; ; 8 0 0 x. %s )' % LD
Y1 = '( %s \\ { %s } )' % (DB(), ZG)
Y0 = '{ %s }' % ZG
LP = lambda k: '( %s ^ %s )' % (LD, k)


def ctx_lc(w, A):
    """the local-count antecedents: N X S T U facts, the scale, the window width"""
    c = Ctx(w, A)
    nn_, xb, sr, s39, s1, tr, t2, ur, ut = [c.g(x) for x in ('N e. NN', 'X e. %s' % DB(), 'S e. RR', '( ; 3 9 / ; 5 0 ) <_ S', 'S <_ 1', 'T e. RR', '2 <_ T', 'U e. RR', '( abs ` U ) <_ T')]
    F = sc_facts(w, A, nn_, tr, t2)
    F.update(dict(nn=nn_, xb=xb, sr=sr, s39=s39, s1=s1, tr=tr, t2=t2, ur=ur, ut=ut))
    F['nxb'] = c([nn_, xb], 'jca', NX)
    F['s0'] = lin8(w, A, [s39], '0 < S', {'S': sr})
    lrp = c([F['lr'], F['lp']], 'elrpd', '%s e. RR+' % LD)
    F['lrp'] = lrp
    F['ilr'] = c([lrp], 'rpreccld', '%s e. RR+' % IL)
    F['ilre'] = c([F['ilr']], 'rpred', '%s e. RR' % IL)
    # 1 / LD <_ 1 from 1 <_ LD
    one = num8(w, A, '1', 'RR+')
    le = c([c([c([num8(w, A, '1'), lin8(w, A, [], '0 < 1', {})], 'jca', '( 1 e. RR /\\ 0 < 1 )'), c([F['lr'], F['lp']], 'jca', '( %s e. RR /\\ 0 < %s )' % (LD, LD))], 'jca', '( ( 1 e. RR /\\ 0 < 1 ) /\\ ( %s e. RR /\\ 0 < %s ) )' % (LD, LD)), w.inst('lerec')], 'syl',
           '( 1 <_ %s <-> ( 1 / %s ) <_ ( 1 / 1 ) )' % (LD, LD))
    il1 = c([lin8(w, A, [F['l1']], '1 <_ %s' % LD, {LD: F['lr']}), le], 'mpbid', '%s <_ ( 1 / 1 )' % IL)
    F['il1'] = c([il1, c.a1(w.s([w.s([], 'ax-1cn', '1 e. CC')], 'div1i', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')], 'breqtrd', '%s <_ 1' % IL)
    F['zfin'], F['zal'] = zf_facts(w, A, F['nxb'], sr, F['s0'], s1, tr)
    # 800 log ( N ( abs U + 2 ) ) <_ 800 LD ;  800 log ( abs U + 2 ) <_ 800 LD
    uc = c([ur], 'recnd', 'U e. CC'); aur = c([uc], 'abscld', '( abs ` U ) e. RR'); au0 = c([uc], 'absge0d', '0 <_ ( abs ` U )')
    U2 = '( ( abs ` U ) + 2 )'
    u2r = c([aur, num8(w, A, '2')], 'readdcld', '%s e. RR' % U2)
    u2p = c([u2r, lin8(w, A, [au0], '0 < %s' % U2, {'( abs ` U )': aur})], 'elrpd', '%s e. RR+' % U2)
    NU = '( N x. %s )' % U2
    nup = c([c([nn_], 'nnrpd', 'N e. RR+'), u2p], 'rpmulcld', '%s e. RR+' % NU)
    hnu = c([F['nr'], c([tr, aur], 'resubcld', '( T - ( abs ` U ) ) e. RR'), lin8(w, A, [F['n1']], '0 <_ N', {'N': F['nr']}), lin8(w, A, [ut], '0 <_ ( T - ( abs ` U ) )', {'( abs ` U )': aur, 'T': tr})], 'mulge0d', '0 <_ ( N x. ( T - ( abs ` U ) ) )')
    nule = lin8(w, A, [hnu], '%s <_ %s' % (NU, DSC), {'N': F['nr'], '( abs ` U )': aur, 'T': tr}, products=True)
    drp = c([F['dr'], lin8(w, A, [F['d4']], '0 < %s' % DSC, {DSC: F['dr']})], 'elrpd', '%s e. RR+' % DSC)
    ll = c([nule, c([nup, drp], 'logled', '( %s <_ %s <-> %s <_ %s )' % (NU, DSC, LNU, LD))], 'mpbid', '%s <_ %s' % (LNU, LD))
    F['lnur'] = c([nup], 'relogcld', '%s e. RR' % LNU)
    F['l800n'] = lin8(w, A, [ll], '( ; ; 8 0 0 x. %s ) <_ %s' % (LNU, L800), {LNU: F['lnur'], LD: F['lr']})
    hu2 = c([c([F['nr'], num8(w, A, '1')], 'resubcld', '( N - 1 ) e. RR'), c([tr, num8(w, A, '2')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A, [F['n1']], '0 <_ ( N - 1 )', {'N': F['nr']}), lin8(w, A, [F['t0']], '0 <_ ( T + 2 )', {'T': tr})], 'mulge0d', '0 <_ ( ( N - 1 ) x. ( T + 2 ) )')
    u2le = lin8(w, A, [hu2, ut], '%s <_ %s' % (U2, DSC), {'N': F['nr'], '( abs ` U )': aur, 'T': tr}, products=True)
    LU2 = LT2('U')
    ll2 = c([u2le, c([u2p, drp], 'logled', '( %s <_ %s <-> %s <_ %s )' % (U2, DSC, LU2, LD))], 'mpbid', '%s <_ %s' % (LU2, LD))
    F['lu2r'] = c([u2p], 'relogcld', '%s e. RR' % LU2)
    F['l800u'] = lin8(w, A, [ll2], '( ; ; 8 0 0 x. %s ) <_ %s' % (LU2, L800), {LU2: F['lu2r'], LD: F['lr']})
    F['drp'] = drp
    return c, F


def win_facts(w, A, F, X='X'):
    """under ( A /\\ q e. WIN ): q e. ZFX, q e. BOXR, q =/= 1, ( E ` q ) = 0, q e. SQ13(U), q e. HP0"""
    Av = '( %s /\\ q e. %s )' % (A, WIN(X))
    cv = Ctx(w, Av)
    qw = cv([], 'simpr', 'q e. %s' % WIN(X))
    qz, qim, _ = elrab_unpack(w, Av, 'v', ZFX(X), '( abs ` ( ( Im ` v ) - U ) ) <_ %s' % IL, 'q', qw)
    qb, qp, _ = elrab_unpack(w, Av, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX(X), 'q', qz)
    qn1 = cv([qp], 'simpld', 'q =/= 1'); qe0 = cv([qp], 'simprd', '( %s ` q ) = 0' % EX(X))
    L_ = lambda st: lift(w, st, Av)
    WA = ante_of(tsub(S['ldenwin'], {'E': IL, 'V': 'q'}))
    wn = cv([cv([cv([cv([L_(F['sr']), L_(F['s39'])], 'jca', '( S e. RR /\\ ( ; 3 9 / ; 5 0 ) <_ S )'), cv([L_(F['tr']), L_(F['ur'])], 'jca', '( T e. RR /\\ U e. RR )')], 'jca', top_and(WA[0])[0]),
                 cv([cv([L_(F['ilre']), L_(F['il1'])], 'jca', '( %s e. RR /\\ %s <_ 1 )' % (IL, IL)), cv([qb, qim], 'jca', '( q e. %s /\\ ( abs ` ( ( Im ` q ) - U ) ) <_ %s )' % (BOXR, IL))], 'jca', top_and(WA[0])[1])], 'jca', WA[0]),
             w.inst('ldenwin')], 'syl', WA[1])
    qsq = cv([wn], 'simpld', 'q e. %s' % SQ13('U')); qh = cv([wn], 'simprd', 'q e. %s' % HP0)
    return dict(Av=Av, cv=cv, qw=qw, qz=qz, qb=qb, qn1=qn1, qe0=qe0, qsq=qsq, qh=qh)


def gen_win():
    w = W('ldenwin', 'Lean ` mem_disk_of_window ` on a square: a point of the box ` [ S , 1 ] x. [ - T , T ] ` with ` S >_ 39 / 50 ` within ` E <_ 1 ` of the height ` U ` lies in the square ` SQ ( 2 + i U , 13 / 8 ) ` and in the right half-plane.')
    A0 = ante('ldenwin'); c = Ctx(w, A0)
    sr, s39, tr, ur, er, e1, vin, vim = [c.g(x) for x in ('S e. RR', '( ; 3 9 / ; 5 0 ) <_ S', 'T e. RR', 'U e. RR', 'E e. RR', 'E <_ 1', 'V e. %s' % BOXR, '( abs ` ( ( Im ` V ) - U ) ) <_ E')]
    vc, rvr, ivr, f1, f2, f3, f4 = box_facts(w, A0, sr, tr, vin)
    RV, IV = '( Re ` V )', '( Im ` V )'
    IU = '( %s - U )' % IV
    iur = c([ivr, ur], 'resubcld', '%s e. RR' % IU)
    ab = c([vim, c([iur, er], 'absled', '( ( abs ` %s ) <_ E <-> ( -u E <_ %s /\\ %s <_ E ) )' % (IU, IU, IU))], 'mpbid', '( -u E <_ %s /\\ %s <_ E )' % (IU, IU))
    a1, a2 = c([ab], 'simpld', '-u E <_ %s' % IU), c([ab], 'simprd', '%s <_ E' % IU)
    lv = {RV: rvr, IV: ivr, 'S': sr, 'U': ur, 'E': er}
    sq0 = sq_memU(w, A0, ur, RV, rvr, IV, ivr, [s39, f1, f2, a1, a2, e1], lv)
    rp = c([vc, w.inst('replim')], 'syl', 'V = ( %s + ( _i x. %s ) )' % (RV, IV))
    sq1 = c([c([rp], 'eleq1d', '( V e. %s <-> ( %s + ( _i x. %s ) ) e. %s )' % (SQ13('U'), RV, IV, SQ13('U'))), sq0], 'mpbird', 'V e. %s' % SQ13('U'))
    hp = c([c([vc, lin8(w, A0, [f1, s39], '0 < %s' % RV, lv)], 'jca', '( V e. CC /\\ 0 < %s )' % RV), c([c([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( V e. %s <-> ( V e. CC /\\ 0 < %s ) )' % (HP0, RV))],
           'mpbird', 'V e. %s' % HP0)
    return fin(w, c([sq1, hp], 'jca', concl('ldenwin')))


def gen_lc1():
    w = W('ldenlc1', 'Lean ` localCount_le_logged ` for ` chi =/= 1 ` : the zeros in the box within ` 1 / L ` of the height ` U ` lie in the square about ` 2 + i U ` , where ~ lchrzc8 counts ` 800 log ( N ( abs U + 2 ) ) <_ 800 L ` ( ~ ldenwin , ~ zc1eord ).')
    A = ante('ldenlc1'); c, F = ctx_lc(w, A)
    x0 = c.g('X =/= %s' % ZG)
    NXX = '( %s /\\ X =/= %s )' % (NX, ZG)
    nxx = c([F['nxb'], x0], 'jca', NXX)
    ZSL = '{ r e. %s | ( %s ` r ) = 0 }' % (SQ13('U'), LFNX)
    lz = c([c([nxx, F['ur']], 'jca', '( %s /\\ U e. RR )' % NXX), w.inst('lchrzc8')], 'syl', ante_of(tsub(stmt('lchrzc8'), {'T': 'U'}))[1])
    zfin = c([lz], 'simp1d', '%s e. Fin' % ZSL)
    zal = c([lz], 'simp2d', 'A. q e. %s ( %s holord q ) e. NN' % (ZSL, LFNX))
    zsum = c([lz], 'simp3d', 'sum_ q e. %s ( %s holord q ) <_ ( ; ; 8 0 0 x. %s )' % (ZSL, LFNX, LNU))
    Wd = win_facts(w, A, F)
    Av, cv = Wd['Av'], Wd['cv']
    EO = ante_of(tsub(stmt('zc1eord'), {'P': 'q'}))
    eo = cv([cv([lift(w, nxx, Av), cv([Wd['qh'], Wd['qn1']], 'jca', '( q e. %s /\\ q =/= 1 )' % HP0)], 'jca', EO[0]), w.inst('zc1eord')], 'syl', EO[1])
    oq = cv([eo], 'simpld', '( %s holord q ) = ( %s holord q )' % (E0, LFNX))
    lq0 = cv([Wd['qe0'], cv([eo], 'simprd', '( ( %s ` q ) = 0 <-> ( %s ` q ) = 0 )' % (E0, LFNX))], 'mpbid', '( %s ` q ) = 0' % LFNX)
    qzl = elrab_pack(w, Av, 'r', SQ13('U'), '( %s ` r ) = 0' % LFNX, 'q', Wd['qsq'], lq0)
    wss = c([w.s([qzl], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A, WIN(), ZSL))], 'ssrdv', '%s C_ %s' % (WIN(), ZSL))
    OL = '( %s holord q )' % LFNX
    se = c([oq], 'sumeq2dv', '%s = sum_ q e. %s %s' % (LCX('X', 'U'), WIN(), OL))
    Az = '( %s /\\ q e. %s )' % (A, ZSL)
    zn = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Az, OL))
    fl = c([zfin, w.s([zn], 'nnred', '( %s -> %s e. RR )' % (Az, OL)), w.s([w.s([zn], 'nnnn0d', '( %s -> %s e. NN0 )' % (Az, OL))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (Az, OL)), wss],
           'fsumless', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (WIN(), OL, ZSL, OL))
    S1 = 'sum_ q e. %s %s' % (WIN(), OL); S2 = 'sum_ q e. %s %s' % (ZSL, OL)
    wfin = c([zfin, wss], 'ssfid', '%s e. Fin' % WIN())
    Aw = '( %s /\\ q e. %s )' % (A, WIN())
    wq = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Aw, A)), w.s([lift(w, wss, Aw), w.s([], 'simpr', '( %s -> q e. %s )' % (Aw, WIN()))], 'sseldd', '( %s -> q e. %s )' % (Aw, ZSL))], 'jca', '( %s -> %s )' % (Aw, Az)), w.s([zn], 'nnred', '( %s -> %s e. RR )' % (Az, OL))], 'syl', '( %s -> %s e. RR )' % (Aw, OL))
    s1r = c([wfin, wq], 'fsumrecl', '%s e. RR' % S1)
    s2r = c([zfin, w.s([zn], 'nnred', '( %s -> %s e. RR )' % (Az, OL))], 'fsumrecl', '%s e. RR' % S2)
    lcr = c([se, s1r], 'eqeltrd', '%s e. RR' % LCX('X', 'U'))
    lv = {LCX('X', 'U'): lcr, S1: s1r, S2: s2r, LNU: F['lnur'], LD: F['lr']}
    return fin(w, lin8(w, A, [se, fl, zsum, F['l800n']], concl('ldenlc1'), lv))


def gen_lc0():
    w = W('ldenlc0', 'Lean ` localCount_le_logged ` for the principal character: its orders are those of ` ( s - 1 ) zeta ` ( ~ zc1tord ), at most those of ` eta ` ( ~ zc1ezt ), and ~ etazc counts the square: ` 800 log ( abs U + 2 ) <_ 800 L ` .')
    A = ante('ldenlc0'); c, F = ctx_lc(w, A)
    x0 = c.g('X = %s' % ZG)
    NXX = '( %s /\\ X = %s )' % (NX, ZG)
    nxx = c([F['nxb'], x0], 'jca', NXX)
    fz = c([F['ur'], w.inst('etazc')], 'syl', tsub(ante_of(stmt('etazc'))[1], {'T': 'U'}))
    ZSU = ZSE('U')
    zfin = c([fz], 'simp1d', '%s e. Fin' % ZSU)
    zal = c([fz], 'simp2d', 'A. q e. %s ( %s holord q ) e. NN' % (ZSU, ETA))
    zsum = c([fz], 'simp3d', 'sum_ q e. %s ( %s holord q ) <_ ( ; ; 8 0 0 x. %s )' % (ZSU, ETA, LT2('U')))
    Wd = win_facts(w, A, F)
    Av, cv = Wd['Av'], Wd['cv']
    TO = ante_of(tsub(stmt('zc1tord'), {'P': 'q'}))
    to = cv([cv([lift(w, nxx, Av), Wd['qh']], 'jca', TO[0]), w.inst('zc1tord')], 'syl', TO[1])
    oq = cv([to], 'simpld', '( %s holord q ) = ( %s holord q )' % (E0, E1))
    e1z = cv([Wd['qe0'], cv([to], 'simprd', '( ( %s ` q ) = 0 <-> ( %s ` q ) = 0 )' % (E0, E1))], 'mpbid', '( %s ` q ) = 0' % E1)
    ZT = ante_of(tsub(stmt('zc1ezt'), {'P': 'q'}))
    zt = cv([cv([Wd['qh'], Wd['qn1']], 'jca', ZT[0]), w.inst('zc1ezt')], 'syl', ZT[1])
    ole = cv([zt], 'simpld', '( %s holord q ) <_ ( %s holord q )' % (E1, ETA))
    etz = cv([e1z, cv([zt], 'simprd', '( ( %s ` q ) = 0 -> ( %s ` q ) = 0 )' % (E1, ETA))], 'mpd', '( %s ` q ) = 0' % ETA)
    qzl = elrab_pack(w, Av, 'r', SQ13('U'), '( %s ` r ) = 0' % ETA, 'q', Wd['qsq'], etz)
    wss = c([w.s([qzl], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A, WIN(), ZSU))], 'ssrdv', '%s C_ %s' % (WIN(), ZSU))
    OE = '( %s holord q )' % E0; OT = '( %s holord q )' % ETA
    ole2 = cv([oq, ole], 'eqbrtrd', '%s <_ %s' % (OE, OT))
    wfin = c([zfin, wss], 'ssfid', '%s e. Fin' % WIN())
    Az = '( %s /\\ q e. %s )' % (A, ZSU)
    zn = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Az, OT))
    Aw = Av
    inz = cv([cv([], 'simpl', A), cv([lift(w, wss, Aw), Wd['qw']], 'sseldd', 'q e. %s' % ZSU)], 'jca', Az)
    otr = w.s([inz, w.s([zn], 'nnred', '( %s -> %s e. RR )' % (Az, OT))], 'syl', '( %s -> %s e. RR )' % (Aw, OT))
    # E holord q e. NN for q e. ZFX ( from zf_facts )
    Azf = '( %s /\\ q e. %s )' % (A, ZFX('X'))
    on = w.s([F['zal']], 'r19.21bi', '( %s -> %s e. NN )' % (Azf, OE))
    oer = w.s([cv([cv([], 'simpl', A), Wd['qz']], 'jca', Azf), w.s([on], 'nnred', '( %s -> %s e. RR )' % (Azf, OE))], 'syl', '( %s -> %s e. RR )' % (Aw, OE))
    fl1 = c([wfin, oer, otr, ole2], 'fsumle', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (WIN(), OE, WIN(), OT))
    fl2 = c([zfin, w.s([zn], 'nnred', '( %s -> %s e. RR )' % (Az, OT)), w.s([w.s([zn], 'nnnn0d', '( %s -> %s e. NN0 )' % (Az, OT))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (Az, OT)), wss],
            'fsumless', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (WIN(), OT, ZSU, OT))
    S0 = LCX('X', 'U'); S1 = 'sum_ q e. %s %s' % (WIN(), OT); S2 = 'sum_ q e. %s %s' % (ZSU, OT)
    assert S0 == 'sum_ q e. %s %s' % (WIN(), OE), S0[:100]
    lv = {S0: c([wfin, oer], 'fsumrecl', '%s e. RR' % S0), S1: c([wfin, otr], 'fsumrecl', '%s e. RR' % S1), S2: c([zfin, w.s([zn], 'nnred', '( %s -> %s e. RR )' % (Az, OT))], 'fsumrecl', '%s e. RR' % S2),
          LT2('U'): F['lu2r'], LD: F['lr']}
    return fin(w, lin8(w, A, [fl1, fl2, zsum, F['l800u']], concl('ldenlc0'), lv))


def gen_lc():
    w = W('ldenlc', '**Lean ` localCount_le_logged ` ** (Lemma 3.1): for every character the zeros of the box within ` 1 / L ` of a height ` U ` , ` abs U <_ T ` , number at most ` 800 L ` , ` L = log ( N ( T + 2 ) ) ` ( ~ ldenlc0 , ~ ldenlc1 ; Lean\'s ` 112 L ` is ZC1\'s square mass ` 800 log ` ).')
    A = ante('ldenlc'); c = Ctx(w, A)
    GOAL = concl('ldenlc')
    outs = []
    for lab, cond in (('ldenlc0', 'X = %s' % ZG), ('ldenlc1', 'X =/= %s' % ZG)):
        Ac = '( %s /\\ %s )' % (A, cond)
        cc = Ctx(w, Ac)
        A1 = ante(lab)
        st = cc([cc([cc([cc.g(NX), cc([], 'simpr', cond)], 'jca', '( %s /\\ %s )' % (NX, cond)), cc.g(top_and(top_and(A1)[0])[1])], 'jca', top_and(A1)[0]), cc.g(top_and(A1)[1])], 'jca', A1)
        outs.append(cc([st, w.inst(lab)], 'syl', GOAL))
    return fin(w, c([outs[0], outs[1]], 'pm2.61dane', GOAL))


def denparts(w, A, P):
    """HDEN / HD0 antecedents: closure (N T S LD DSC PW CTau), the scale facts, the principal character"""
    F = {}
    F['nN'] = P['N e. NN']; F['sr'] = P['S e. RR']; F['s39'] = P['( ; 3 9 / ; 5 0 ) <_ S']; F['s1'] = P['S <_ 1']; F['tr'] = P['T e. RR']; F['t2'] = P['2 <_ T']
    F['hsig'] = P[HSIG]
    if H40 in P:
        F['l40'] = P[H40]
    F.update(sc_facts(w, A, F['nN'], F['tr'], F['t2']))
    c = Closure(w, A, {'N': ('NN', F['nN']), 'T': [('RR', F['tr']), ('ge0', F['t0'])], 'S': ('RR', F['sr']), DSC: [('RR', F['dr'])], LD: [('RR', F['lr'])]})
    c.leaf(DSC, 'RR+', dst(w, A, [F['dr'], linarith(w, A, [F['d4']], '0 < %s' % DSC, closure=c)], 'elrpd', '%s e. RR+' % DSC))
    c.leaf(LD, 'RR', F['lr']); c.have(LD, 'gt0', F['lp']); c.have(LD, 'ge0', linarith(w, A, [F['l1']], '0 <_ %s' % LD, closure=c))
    c.have(LD, 'ge1', linarith(w, A, [F['l1']], '1 <_ %s' % LD, closure=c))
    F['s0'] = linarith(w, A, [F['s39']], '0 < S', closure=c); c.have('S', 'ge0', ltle(w, A, c, F['s0']))
    c.leaf(PW, 'RR+', c.mem(PW, 'RR+'))
    c.leaf('CTau', 'NN', ctau_nn(w, A))
    F['ex0'] = linarith(w, A, [F['s1']], '0 <_ %s' % EXPS, closure=c)
    # 1 <_ PW
    pw1 = ap(w, A, 'cxplea', [J(w, A, c.mem(DSC, 'RR'), linarith(w, A, [F['d4']], '1 <_ %s' % DSC, closure=c)), J(w, A, num8(w, A, '0'), c.mem(EXPS, 'RR')), F['ex0']], '( %s ^c 0 ) <_ %s' % (DSC, PW))
    F['pw1'] = dst(w, A, [eqc(w, A, dst(w, A, [c.mem(DSC, 'CC')], 'cxp0d', '( %s ^c 0 ) = 1' % DSC)), pw1], 'eqbrtrd', '1 <_ %s' % PW)
    c.have(PW, 'ge1', F['pw1'])
    CT2 = '( CTau ^ 2 )'
    F['ct1'] = ap(w, A, 'expge1', [J(w, A, c.mem('CTau', 'RR'), a1(w, A, '2nn0', '2 e. NN0'), dst(w, A, [c.mem('CTau', 'NN')], 'nnge1d', '1 <_ CTau'))], '1 <_ %s' % CT2)
    c.leaf(CT2, 'RR', c.mem(CT2, 'RR')); c.have(CT2, 'ge1', F['ct1']); c.have(CT2, 'ge0', linarith(w, A, [F['ct1']], '0 <_ %s' % CT2, closure=c))
    # the principal character and the finite character set
    g_ = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); b_ = w.s([], 'eqid', '%s = %s' % (DB(), DB()))
    F['dbfin'] = w.s([F['nN'], w.s([g_, b_], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB())], 'syl', '( %s -> %s e. Fin )' % (A, DB()))
    abl = w.s([F['nN'], w.s([g_], 'dchrabl', '( N e. NN -> ( DChr ` N ) e. Abel )')], 'syl', '( %s -> ( DChr ` N ) e. Abel )' % A)
    grp = dst(w, A, [abl], 'ablgrpd', '( DChr ` N ) e. Grp')
    gid = w.s([b_, w.s([], 'eqid', '%s = %s' % (ZG, ZG))], 'grpidcl', '( ( DChr ` N ) e. Grp -> %s e. %s )' % (ZG, DB()))
    F['zg'] = w.s([grp, gid], 'syl', '( %s -> %s e. %s )' % (A, ZG, DB()))
    return c, F


def lc_all(w, A, F, Y, yss):
    """( A -> A. x e. Y A. u e. RR ( abs u <_ T -> LCX(x,u) <_ 800 LD ) ) from ~ ldenlc; yss: ( A -> Y C_ DB )"""
    Axu = '( %s /\\ ( x e. %s /\\ u e. RR ) )' % (A, Y)
    A2 = '( %s /\\ ( abs ` u ) <_ T )' % Axu
    xin = w.s([], 'simprl', '( %s -> x e. %s )' % (Axu, Y)); uin = w.s([], 'simprr', '( %s -> u e. RR )' % Axu)
    xdb = w.s([lift(w, yss, Axu), xin], 'sseldd', '( %s -> x e. %s )' % (Axu, DB()))
    L2 = lambda st: lift(w, st, A2)
    LA = ante_of(tsub(S['ldenlc'], {'X': 'x', 'U': 'u'}))
    hyp = J(w, A2, J(w, A2, J(w, A2, L2(lift(w, F['nN'], Axu)), L2(xdb)), J(w, A2, L2(lift(w, F['hsig'], Axu)), J(w, A2, L2(lift(w, F['tr'], Axu)), L2(lift(w, F['t2'], Axu))))), J(w, A2, L2(uin), w.s([], 'simpr', '( %s -> ( abs ` u ) <_ T )' % A2)))
    assert body(w, hyp, A2) == LA[0], (body(w, hyp, A2)[:300], LA[0][:300])
    lc = ap(w, A2, 'ldenlc', [hyp], LA[1])
    ex_ = w.s([lc], 'ex', '( %s -> ( ( abs ` u ) <_ T -> %s ) )' % (Axu, LA[1]))
    return dst(w, A, [ex_], 'ralrimivva', 'A. x e. %s A. u e. RR ( ( abs ` u ) <_ T -> %s )' % (Y, LA[1]))


def cov_at(w, A, c, F, Y, G, yss, yfin, lcal):
    """~ zrcov at Y, G, B := 800 LD: ( A -> GOODS <_ ( 800 LD ) x. JJ )"""
    SUB = {'Y': Y, 'G': G, 'B': L800}
    CA, CC_ = ante_of(tsub(stmt('zrcov'), SUB))
    hyp = J(w, A, J(w, A, J(w, A, J(w, A, F['nN'], yss), yfin), J(w, A, J(w, A, F['sr'], F['s0'], F['s1']), F['tt'])), J(w, A, c.mem(L800, 'RR'), lcal))
    assert body(w, hyp, A) == CA, (body(w, hyp, A)[:300], CA[:300])
    return ap(w, A, 'zrcov', [hyp], CC_), SUB


def ri_at(w, A, c, F, Y, G, yss, yfin, P_, hgd):
    """~ ldenri at Y, G, P: ( A -> ( # ` RI ) <_ ( 2 LD ) B2 )"""
    SUB = {'Y': Y, 'G': G, 'P': P_}
    RA, RC = ante_of(tsub(S['ldenri'], SUB))
    hyp = J(w, A, J(w, A, J(w, A, J(w, A, F['nN'], yss), yfin), J(w, A, F['hsig'], J(w, A, J(w, A, F['tr'], F['t2']), F['l40']))), hgd)
    assert body(w, hyp, A) == RA, (body(w, hyp, A)[:300], RA[:300])
    return ap(w, A, 'ldenri', [hyp], RC)


def gen_low():
    w = W('ldenlow', 'Lean ` low_zeta_count ` : the ` chi_0 ` zeros of the box below height ` L ` lie in the box of abscissa ` 1 / 2 ` and height ` L ` , whose mass ~ zc1tle bounds by ` 6400 L log ( L + 2 ) <_ 12800 L ^ 2 ` .')
    A = ante('ldenlow'); P = parts(w, A)
    c, F = denparts(w, A, P)
    ZFH = tsub(ZFX(ZG), {'S': '( 1 / 2 )', 'T': LD})           # the box of abscissa 1/2 and height L
    assert ZFH == '{ r e. ( ( ( 1 / 2 ) + ( _i x. -u %s ) ) crect ( 1 + ( _i x. %s ) ) ) | ( r =/= 1 /\\ ( %s ` r ) = 0 ) }' % (LD, LD, EZ), ZFH
    OQ = ORDX(ZG, 'q')
    Aq = '( %s /\\ q e. %s )' % (A, NOTGH)
    cq = Ctx(w, Aq)
    qin = cq([], 'simpr', 'q e. %s' % NOTGH)
    qz, qng, _ = elrab_unpack(w, Aq, 'v', ZFX(ZG), '-. v e. %s' % GH, 'q', qin)
    qb, qp, _ = elrab_unpack(w, Aq, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EZ, 'q', qz)
    vc, rvr, ivr, f1, f2, f3, f4 = box_facts(w, Aq, lift(w, F['sr'], Aq), lift(w, F['tr'], Aq), qb, 'q')
    # -. LD <_ abs Im q
    eg, _ = elrab_(w, 'g', 'CC', '%s <_ ( abs ` ( Im ` g ) )' % LD, 'q')
    ng2 = w.s([qng, w.s([eg], 'a1i', '( %s -> ( q e. %s <-> ( q e. CC /\\ %s <_ ( abs ` ( Im ` q ) ) ) ) )' % (Aq, GH, LD))], 'mtbid', '( %s -> -. ( q e. CC /\\ %s <_ ( abs ` ( Im ` q ) ) ) )' % (Aq, LD))
    # -. ( q e. CC /\ ph ) with q e. CC gives -. ph :  ( ph -> -. ps ) from -. ( ph /\ ps ) is imnan; use pm3.2 route
    imp_ = w.s([ng2, w.s([], 'imnan', '( ( q e. CC -> -. %s <_ ( abs ` ( Im ` q ) ) ) <-> -. ( q e. CC /\\ %s <_ ( abs ` ( Im ` q ) ) ) )' % (LD, LD))], 'sylibr', '( %s -> ( q e. CC -> -. %s <_ ( abs ` ( Im ` q ) ) ) )' % (Aq, LD))
    ng3 = w.s([vc, imp_], 'mpd', '( %s -> -. %s <_ ( abs ` ( Im ` q ) ) )' % (Aq, LD))
    AI = '( abs ` ( Im ` q ) )'
    air = cq([cq([ivr], 'recnd', '( Im ` q ) e. CC')], 'abscld', '%s e. RR' % AI)
    lt = cq([ng3, cq([air, lift(w, F['lr'], Aq)], 'ltnled', '( %s < %s <-> -. %s <_ %s )' % (AI, LD, LD, AI))], 'mpbird', '%s < %s' % (AI, LD))
    le = cq([air, lift(w, F['lr'], Aq), lt], 'ltled', '%s <_ %s' % (AI, LD))
    half = lin8(w, Aq, [f1, lift(w, F['s39'], Aq)], '( 1 / 2 ) <_ ( Re ` q )', {'( Re ` q )': rvr, 'S': lift(w, F['sr'], Aq)})
    # pack into ZFH by t21zfel
    ZA = tsub(stmt('t21zfel'), {'A': '( 1 / 2 )', 'T': LD, 'F': EZ, 'Q': 'q'})
    za, zc_ = ante_of(ZA)
    bic = cq([cq([num8(w, Aq, '( 1 / 2 )'), lift(w, F['lr'], Aq)], 'jca', za), w.inst('t21zfel')], 'syl', zc_)
    qn1 = cq([qp], 'simpld', 'q =/= 1'); qe0 = cq([qp], 'simprd', '( %s ` q ) = 0' % EZ)
    mem = cq([cq([vc, cq([cq([half, f2], 'jca', '( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )'), le], 'jca', '( ( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ %s <_ %s )' % (AI, LD)), cq([qn1, qe0], 'jca', '( q =/= 1 /\\ ( %s ` q ) = 0 )' % EZ)], '3jca',
                 '( q e. CC /\\ ( ( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ %s <_ %s ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (AI, LD, EZ)), bic], 'mpbird', 'q e. %s' % ZFH)
    ss = dst(w, A, [w.s([mem], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A, NOTGH, ZFH))], 'ssrdv', '%s C_ %s' % (NOTGH, ZFH))
    # ZFH finite, orders NN (ezf at A := 1/2, T := LD)
    nx0 = J(w, A, F['nN'], F['zg'])
    EA = ante_of(tsub(stmt('ezf'), {'X': ZG, 'A': '( 1 / 2 )', 'T': LD}))
    ez = ap(w, A, 'ezf', [J(w, A, nx0, J(w, A, J(w, A, num8(w, A, '( 1 / 2 )'), lin8(w, A, [], '0 < ( 1 / 2 )', {}), lin8(w, A, [], '( 1 / 2 ) <_ 1', {})), F['lr']))], EA[1])
    hfin = dst(w, A, [ez], 'simpld', '%s e. Fin' % ZFH); hal = dst(w, A, [ez], 'simprd', 'A. q e. %s %s e. NN' % (ZFH, OQ))
    Ah = '( %s /\\ q e. %s )' % (A, ZFH)
    on = w.s([hal], 'r19.21bi', '( %s -> %s e. NN )' % (Ah, OQ))
    fl = dst(w, A, [hfin, w.s([on], 'nnred', '( %s -> %s e. RR )' % (Ah, OQ)), w.s([w.s([on], 'nnnn0d', '( %s -> %s e. NN0 )' % (Ah, OQ))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (Ah, OQ)), ss], 'fsumless',
            'sum_ q e. %s %s <_ sum_ q e. %s %s' % (NOTGH, OQ, ZFH, OQ))
    # zc1tle at T := LD
    TA = ante_of(tsub(stmt('zc1tle'), {'X': ZG, 'T': LD}))
    tle = ap(w, A, 'zc1tle', [J(w, A, J(w, A, nx0, dst(w, A, [], 'eqidd', '%s = %s' % (ZG, ZG))), J(w, A, F['lr'], c.mem(LD, 'ge1')))], TA[1])
    LL2 = '( log ` ( %s + 2 ) )' % LD
    l2 = ap(w, A, 'loglet', [J(w, A, c.mem('( %s + 2 )' % LD, 'RR'), linarith(w, A, [F['l40']], '1 <_ ( %s + 2 )' % LD, closure=c))], '%s <_ ( %s + 2 )' % (LL2, LD))
    c.leaf(LL2, 'RR', dst(w, A, [c.mem('( %s + 2 )' % LD, 'RR+')], 'relogcld', '%s e. RR' % LL2))
    nfin = dst(w, A, [hfin, ss], 'ssfid', '%s e. Fin' % NOTGH)
    An = '( %s /\\ q e. %s )' % (A, NOTGH)
    onn = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (An, A)), w.s([lift(w, ss, An), w.s([], 'simpr', '( %s -> q e. %s )' % (An, NOTGH))], 'sseldd', '( %s -> q e. %s )' % (An, ZFH))], 'jca', '( %s -> %s )' % (An, Ah)), w.s([on], 'nnred', '( %s -> %s e. RR )' % (Ah, OQ))], 'syl', '( %s -> %s e. RR )' % (An, OQ))
    SN = 'sum_ q e. %s %s' % (NOTGH, OQ); SH = 'sum_ q e. %s %s' % (ZFH, OQ)
    c.leaf(SN, 'RR', dst(w, A, [nfin, onn], 'fsumrecl', '%s e. RR' % SN)); c.leaf(SH, 'RR', dst(w, A, [hfin, w.s([on], 'nnred', '( %s -> %s e. RR )' % (Ah, OQ))], 'fsumrecl', '%s e. RR' % SH))
    return fin(w, nlinarith(w, A, [fl, tle, l2, F['l40']], concl('ldenlow'), closure=c))


def ri_facts2(w, A, qst, Q, SUB, P_):
    """zr_k.ri_facts for an instance of RI(P) with Y, G substituted (SUB): Q e. XPY, cell nonempty, parity, 2nd Q e. ZZ, 1st Q e. Y, 2nd Q e. ( 0 ... QP )"""
    from zr_k import XPY as XPY0, RIB
    c = Ctx(w, A)
    XP = tsub(XPY0, SUB); rib = tsub(RIB(P_), SUB)
    qxp, qb, new = elrab_unpack(w, A, 'p', XP, rib, Q, qst)
    cne = c([qb], 'simpld', top_and(new)[0])
    par = c([qb], 'simprd', top_and(new)[1])
    q2 = c([qxp, w.inst('xp2nd')], 'syl', '( 2nd ` %s ) e. ( 0 ... %s )' % (Q, QP))
    q2z = c([q2, w.inst('elfzelz')], 'syl', '( 2nd ` %s ) e. ZZ' % Q)
    q1 = c([qxp, w.inst('xp1st')], 'syl', '( 1st ` %s ) e. %s' % (Q, SUB['Y']))
    return qxp, cne, par, q2z, q1, q2


def gen_in1():
    w = W('ldenin1', 'Instance 1 of Lean ` logged_density_large ` : the nonprincipal characters with every zero, ~ zrcov at ` X = univ.erase 1 ` , ` good = True ` ( ` G = CC ` ), ` B = 800 L ` , and ~ ldenri for the two parity systems (the height clause holds vacuously).')
    A = ante('ldenin1'); P = parts(w, A)
    c, F = denparts(w, A, P)
    yss = w.s([w.s([], 'difss', '%s C_ %s' % (Y1, DB()))], 'a1i', '( %s -> %s C_ %s )' % (A, Y1, DB()))
    yfin = w.s([F['dbfin'], w.inst('diffi')], 'syl', '( %s -> %s e. Fin )' % (A, Y1))
    lcal = lc_all(w, A, F, Y1, yss)
    cov, SUB = cov_at(w, A, c, F, Y1, 'CC', yss, yfin, lcal)
    # the good filter is the whole zero set (G = CC)
    Ax = '( %s /\\ x e. %s )' % (A, Y1)
    cx = Ctx(w, Ax)
    ic = cx.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    CA_, CB_ = '( S + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    cac = cx([cx([lift(w, F['sr'], Ax)], 'recnd', 'S e. CC'), cx([ic, cx([cx([lift(w, F['tr'], Ax)], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % CA_)
    cbc = cx([cx([], '1cnd', '1 e. CC'), cx([ic, cx([lift(w, F['tr'], Ax)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CB_)
    bss = cx([cac, cbc, w.inst('crectss')], 'syl2anc', '%s C_ CC' % BOXR)
    zss = cx([cx.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZFX('x'), BOXR)), '%s C_ %s' % (ZFX('x'), BOXR)), bss], 'sstrd', '%s C_ CC' % ZFX('x'))
    Av = '( %s /\\ v e. %s )' % (Ax, ZFX('x'))
    vc = w.s([lift(w, zss, Av), w.s([], 'simpr', '( %s -> v e. %s )' % (Av, ZFX('x')))], 'sseldd', '( %s -> v e. CC )' % Av)
    al = cx([vc], 'ralrimiva', 'A. v e. %s v e. CC' % ZFX('x'))
    GCC = tsub(GX('x'), {'G': 'CC'})
    ge = cx([al, w.s([], 'rabid2', '( %s = %s <-> A. v e. %s v e. CC )' % (ZFX('x'), GCC, ZFX('x')))], 'sylibr', '%s = %s' % (ZFX('x'), GCC))
    se = dst(w, A, [cx([ge], 'sumeq1d', '%s = sum_ q e. %s %s' % (ZCB('x'), GCC, ORDX('x', 'q')))], 'sumeq2dv', 'sum_ x e. %s %s = %s' % (Y1, ZCB('x'), tsub(GOODS('Y'), SUB)))
    # the two systems
    RI1 = lambda P_: tsub(RI(P_), SUB)
    def hgd1(P_):
        Ae = '( %s /\\ e e. %s )' % (A, RI1(P_))
        ein = w.s([], 'simpr', '( %s -> e e. %s )' % (Ae, RI1(P_)))
        exp_, cne, par, e2z, e1y, e2 = ri_facts2(w, Ae, ein, 'e', SUB, P_)
        # 1st e e. Y1 -> 1st e =/= ZG -> ( 1st e = ZG -> anything )
        ne = w.s([e1y, w.inst('eldifsni')], 'syl', '( %s -> ( 1st ` e ) =/= %s )' % (Ae, ZG))
        CZ = tsub(CELL('( 1st ` e )', '( 2nd ` e )'), SUB)
        BODY = 'A. z e. %s %s <_ ( abs ` ( Im ` z ) )' % (CZ, LD)
        im = w.s([w.s([], 'eqneqall', '( ( 1st ` e ) = %s -> ( ( 1st ` e ) =/= %s -> %s ) )' % (ZG, ZG, BODY))], 'com12', '( ( 1st ` e ) =/= %s -> ( ( 1st ` e ) = %s -> %s ) )' % (ZG, ZG, BODY))
        st = w.s([ne, im], 'syl', '( %s -> ( ( 1st ` e ) = %s -> %s ) )' % (Ae, ZG, BODY))
        return dst(w, A, [st], 'ralrimiva', tsub(HGD, dict(SUB, P=P_)))
    r0 = ri_at(w, A, c, F, Y1, 'CC', yss, yfin, '0', hgd1('0'))
    r1 = ri_at(w, A, c, F, Y1, 'CC', yss, yfin, '1', hgd1('1'))
    H0_, H1_ = '( # ` %s )' % RI1('0'), '( # ` %s )' % RI1('1')
    xfin = dst(w, A, [yfin, dst(w, A, [], 'fzfid', '( 0 ... %s ) e. Fin' % QP), w.inst('xpfi')], 'syl2anc', '( %s X. ( 0 ... %s ) ) e. Fin' % (Y1, QP))
    for P_, H_ in (('0', H0_), ('1', H1_)):
        rf = dst(w, A, [xfin, w.s([w.s([], 'ssrab2', '%s C_ ( %s X. ( 0 ... %s ) )' % (RI1(P_), Y1, QP))], 'a1i', '( %s -> %s C_ ( %s X. ( 0 ... %s ) ) )' % (A, RI1(P_), Y1, QP))], 'ssfid', '%s e. Fin' % RI1(P_))
        c.leaf(H_, 'NN0', w.s([rf, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, H_)))
    c.leaf(B2, 'RR', c.mem(B2, 'RR')); c.have(B2, 'ge0', c.ge0(B2))
    for a_ in (B2, LD):
        c.atom(a_)
    GS = tsub(GOODS('Y'), SUB)
    # the sum is real: from the bound? use fsumrecl over Y1 of ZCB (orders NN)
    Ax2 = Ax
    xdb = w.s([lift(w, yss, Ax2), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax2, Y1))], 'sseldd', '( %s -> x e. %s )' % (Ax2, DB()))
    zfx, zax = zf_facts(w, Ax2, cx([lift(w, F['nN'], Ax2), xdb], 'jca', tsub(NX, {'X': 'x'})), lift(w, F['sr'], Ax2), lift(w, F['s0'], Ax2), lift(w, F['s1'], Ax2), lift(w, F['tr'], Ax2), 'x')
    Axq = '( %s /\\ q e. %s )' % (Ax2, ZFX('x'))
    onq = w.s([zax], 'r19.21bi', '( %s -> %s e. NN )' % (Axq, ORDX('x', 'q')))
    zcbr = cx([zfx, w.s([onq], 'nnred', '( %s -> %s e. RR )' % (Axq, ORDX('x', 'q')))], 'fsumrecl', '%s e. RR' % ZCB('x'))
    sumr = dst(w, A, [yfin, zcbr], 'fsumrecl', 'sum_ x e. %s %s e. RR' % (Y1, ZCB('x')))
    c.leaf('sum_ x e. %s %s' % (Y1, ZCB('x')), 'RR', sumr)
    c.leaf(GS, 'RR', dst(w, A, [se, sumr], 'eqeltrrd', '%s e. RR' % GS))
    cov2 = dst(w, A, [se, cov], 'eqbrtrd', 'sum_ x e. %s %s <_ ( %s x. ( %s + %s ) )' % (Y1, ZCB('x'), L800, H0_, H1_))
    return fin(w, nlinarith(w, A, [cov2, r0, r1, c.ge0(LD)], concl('ldenin1'), closure=c))


def gen_in0():
    w = W('ldenin0', 'Instance 0 of Lean ` logged_density_large ` : the principal character with the zeros of height at least ` L ` ( ~ zrcov at ` X = { 1 } ` , ` good = goodHigh L ` , ~ ldenri for the two parity systems) and the low zeros ( ~ ldenlow ).')
    A = ante('ldenin0'); P = parts(w, A)
    c, F = denparts(w, A, P)
    yss = dst(w, A, [F['zg']], 'snssd', '%s C_ %s' % (Y0, DB()))
    yfin = a1(w, A, 'snfi', '%s e. Fin' % Y0)
    lcal = lc_all(w, A, F, Y0, yss)
    cov, SUB = cov_at(w, A, c, F, Y0, GH, yss, yfin, lcal)
    GOODZ = tsub(GX('x'), {'G': GH})
    OQ = ORDX(ZG, 'q')
    # sum_ x e. { ZG } ... = the term at ZG
    BODYx = 'sum_ q e. %s %s' % (GOODZ, ORDX('x', 'q'))
    cg, BODYz = w.congr(BODYx, {'x': ZG}, 'x = %s' % ZG, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (ZG, ZG))})
    GOODG = tsub(GOODZ, {'x': ZG})
    assert BODYz == 'sum_ q e. %s %s' % (GOODG, OQ), BODYz[:200]
    nx0 = J(w, A, F['nN'], F['zg'])
    zfin, zal = zf_facts(w, A, nx0, F['sr'], F['s0'], F['s1'], F['tr'], ZG)
    gfin = dst(w, A, [zfin, w.s([w.s([], 'ssrab2', '%s C_ %s' % (GOODG, ZFX(ZG)))], 'a1i', '( %s -> %s C_ %s )' % (A, GOODG, ZFX(ZG)))], 'ssfid', '%s e. Fin' % GOODG)
    nfin = dst(w, A, [zfin, w.s([w.s([], 'ssrab2', '%s C_ %s' % (NOTGH, ZFX(ZG)))], 'a1i', '( %s -> %s C_ %s )' % (A, NOTGH, ZFX(ZG)))], 'ssfid', '%s e. Fin' % NOTGH)
    Az = '( %s /\\ q e. %s )' % (A, ZFX(ZG))
    on = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Az, OQ))
    onc = w.s([on], 'nncnd', '( %s -> %s e. CC )' % (Az, OQ))
    onr = w.s([on], 'nnred', '( %s -> %s e. RR )' % (Az, OQ))
    def sub_terms(SET):
        As = '( %s /\\ q e. %s )' % (A, SET)
        st = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (As, A)), w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (As, SET)), w.inst('elrabi')], 'syl', '( %s -> q e. %s )' % (As, ZFX(ZG)))], 'jca', '( %s -> %s )' % (As, Az)), onr], 'syl', '( %s -> %s e. RR )' % (As, OQ))
        return st
    gr = dst(w, A, [gfin, sub_terms(GOODG)], 'fsumrecl', '%s e. RR' % BODYz)
    sn = w.s([J(w, A, dst(w, A, [], 'x', '') if False else a1(w, A, 'fvex', '%s e. _V' % ZG), dst(w, A, [gr], 'recnd', '%s e. CC' % BODYz)), w.s([cg], 'sumsn', '( ( %s e. _V /\\ %s e. CC ) -> sum_ x e. %s %s = %s )' % (ZG, BODYz, Y0, BODYx, BODYz))], 'syl',
             '( %s -> sum_ x e. %s %s = %s )' % (A, Y0, BODYx, BODYz))
    from z4blib import _lhs_rhs
    RHSC = _lhs_rhs(tsub(concl('zrcov'), SUB))[2]
    cov2 = dst(w, A, [eqc(w, A, sn), cov], 'eqbrtrd', '%s <_ %s' % (BODYz, RHSC))
    # the split ZCB ( ZG ) = good + low
    sp = dst(w, A, [a1(w, A, 'rabnc', '( %s i^i %s ) = (/)' % (GOODG, NOTGH)), a1(w, A, 'rabxm', '%s = ( %s u. %s )' % (ZFX(ZG), GOODG, NOTGH)), zfin, onc], 'fsumsplit', '%s = ( %s + sum_ q e. %s %s )' % (ZCB(ZG), BODYz, NOTGH, OQ))
    low = ap(w, A, 'ldenlow', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ldenlow'))
    # the two systems
    RI0 = lambda P_: tsub(RI(P_), SUB)
    def hgd0(P_):
        Ae = '( %s /\\ e e. %s )' % (A, RI0(P_))
        CZ = tsub(CELL('( 1st ` e )', '( 2nd ` e )'), SUB)
        Aez = '( %s /\\ z e. %s )' % (Ae, CZ)
        zin = w.s([], 'simpr', '( %s -> z e. %s )' % (Aez, CZ))
        zz, zb, _ = elrab_unpack(w, Aez, 'v', tsub(ZFX('( 1st ` e )'), SUB) if False else ZFX('( 1st ` e )'), '( v e. %s /\\ %s = ( 2nd ` e ) )' % (GH, IDX('v')), 'z', zin)
        zg = dst(w, Aez, [zb], 'simpld', 'z e. %s' % GH)
        egz, _ = elrab_(w, 'g', 'CC', '%s <_ ( abs ` ( Im ` g ) )' % LD, 'z')
        ge = w.s([zg, egz], 'sylib', '( %s -> ( z e. CC /\\ %s <_ ( abs ` ( Im ` z ) ) ) )' % (Aez, LD))
        ht = dst(w, Aez, [ge], 'simprd', '%s <_ ( abs ` ( Im ` z ) )' % LD)
        al = dst(w, Ae, [ht], 'ralrimiva', 'A. z e. %s %s <_ ( abs ` ( Im ` z ) )' % (CZ, LD))
        imp_ = w.s([al], 'a1d', '( %s -> ( ( 1st ` e ) = %s -> A. z e. %s %s <_ ( abs ` ( Im ` z ) ) ) )' % (Ae, ZG, CZ, LD))
        return dst(w, A, [imp_], 'ralrimiva', tsub(HGD, dict(SUB, P=P_)))
    r0 = ri_at(w, A, c, F, Y0, GH, yss, yfin, '0', hgd0('0'))
    r1 = ri_at(w, A, c, F, Y0, GH, yss, yfin, '1', hgd0('1'))
    H0_, H1_ = '( # ` %s )' % RI0('0'), '( # ` %s )' % RI0('1')
    xfin = dst(w, A, [yfin, dst(w, A, [], 'fzfid', '( 0 ... %s ) e. Fin' % QP), w.inst('xpfi')], 'syl2anc', '( %s X. ( 0 ... %s ) ) e. Fin' % (Y0, QP))
    for P_, H_ in (('0', H0_), ('1', H1_)):
        rf = dst(w, A, [xfin, w.s([w.s([], 'ssrab2', '%s C_ ( %s X. ( 0 ... %s ) )' % (RI0(P_), Y0, QP))], 'a1i', '( %s -> %s C_ ( %s X. ( 0 ... %s ) ) )' % (A, RI0(P_), Y0, QP))], 'ssfid', '%s e. Fin' % RI0(P_))
        c.leaf(H_, 'NN0', w.s([rf, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, H_)))
    c.leaf(B2, 'RR', c.mem(B2, 'RR')); c.have(B2, 'ge0', c.ge0(B2))
    SNl = 'sum_ q e. %s %s' % (NOTGH, OQ)
    c.leaf(BODYz, 'RR', gr); c.leaf(SNl, 'RR', dst(w, A, [nfin, sub_terms(NOTGH)], 'fsumrecl', '%s e. RR' % SNl))
    c.leaf(ZCB(ZG), 'RR', dst(w, A, [zfin, onr], 'fsumrecl', '%s e. RR' % ZCB(ZG)))
    for a_ in (B2, LD):
        c.atom(a_)
    return fin(w, nlinarith(w, A, [sp, cov2, r0, r1, low, c.ge0(LD)], concl('ldenin0'), closure=c))


def gen_e40():
    w = W('ldene40', 'Lean ` hexp40 ` : ` exp 40 <_ 10 ^ 20 ` ( ` e < 3 ` , ` 3 ^ 40 = 9 ^ 20 <_ 10 ^ 20 ` ).')
    e1 = w.s([w.s([], 'ax-1cn', '1 e. CC'), num.fact(w, '; 4 0', 'ZZ'), w.inst('efexp')], 'mp2an', '( exp ` ( ; 4 0 x. 1 ) ) = ( ( exp ` 1 ) ^ ; 4 0 )')
    e2 = w.s([w.s([num.fact(w, '; 4 0', 'CC')], 'mulridi', '( ; 4 0 x. 1 ) = ; 4 0')], 'fveq2i', '( exp ` ( ; 4 0 x. 1 ) ) = ( exp ` ; 4 0 )')
    e3 = w.s([e2, e1], 'eqtr3i', '( exp ` ; 4 0 ) = ( ( exp ` 1 ) ^ ; 4 0 )')
    ee = w.s([], 'df-e', '_e = ( exp ` 1 )')
    e3b = w.s([e3, w.s([ee], 'oveq1i', '( _e ^ ; 4 0 ) = ( ( exp ` 1 ) ^ ; 4 0 )')], 'eqtr4i', '( exp ` ; 4 0 ) = ( _e ^ ; 4 0 )')
    er = w.s([], 'ere', '_e e. RR')
    e0 = w.s([w.s([], '0re', '0 e. RR'), er, w.s([], 'epos', '0 < _e')], 'ltleii', '0 <_ _e')
    e3l = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    e3le = w.s([er, num.fact(w, '3', 'RR'), e3l], 'ltleii', '_e <_ 3')
    p1 = w.s([w.s([er, num.fact(w, '3', 'RR'), num.fact(w, '; 4 0', 'NN0')], '3pm3.2i', '( _e e. RR /\\ 3 e. RR /\\ ; 4 0 e. NN0 )'), w.s([e0, e3le], 'pm3.2i', '( 0 <_ _e /\\ _e <_ 3 )'), w.inst('leexp1a')], 'mp2an', '( _e ^ ; 4 0 ) <_ ( 3 ^ ; 4 0 )')
    m1 = w.s([num.fact(w, '3', 'CC'), num.fact(w, '2', 'NN0'), num.fact(w, '; 2 0', 'NN0'), w.inst('expmul')], 'mp3an', '( 3 ^ ( 2 x. ; 2 0 ) ) = ( ( 3 ^ 2 ) ^ ; 2 0 )')
    m2 = w.s([w.s([num.mul_nat(w, 2, 20)], 'oveq2i', '( 3 ^ ( 2 x. ; 2 0 ) ) = ( 3 ^ ; 4 0 )'), m1], 'eqtr3i', '( 3 ^ ; 4 0 ) = ( ( 3 ^ 2 ) ^ ; 2 0 )')
    sq9 = w.s([], 'sq3', '( 3 ^ 2 ) = 9')
    m3 = w.s([m2, w.s([sq9], 'oveq1i', '( ( 3 ^ 2 ) ^ ; 2 0 ) = ( 9 ^ ; 2 0 )')], 'eqtri', '( 3 ^ ; 4 0 ) = ( 9 ^ ; 2 0 )')
    p2 = w.s([w.s([num.fact(w, '9', 'RR'), num.fact(w, '; 1 0', 'RR'), num.fact(w, '; 2 0', 'NN0')], '3pm3.2i', '( 9 e. RR /\\ ; 1 0 e. RR /\\ ; 2 0 e. NN0 )'), w.s([num.fact(w, '9', 'ge0'), num.le_nat(w, 9, 10)], 'pm3.2i', '( 0 <_ 9 /\\ 9 <_ ; 1 0 )'), w.inst('leexp1a')], 'mp2an', '( 9 ^ ; 2 0 ) <_ ( ; 1 0 ^ ; 2 0 )')
    p3 = w.s([m3, p2], 'eqbrtri', '( 3 ^ ; 4 0 ) <_ ( ; 1 0 ^ ; 2 0 )')
    E40, E3, P20 = '( _e ^ ; 4 0 )', '( 3 ^ ; 4 0 )', '( ; 1 0 ^ ; 2 0 )'
    er40 = w.s([er, num.fact(w, '; 4 0', 'NN0'), w.inst('reexpcl')], 'mp2an', '%s e. RR' % E40)
    r3 = w.s([num.fact(w, '3', 'RR'), num.fact(w, '; 4 0', 'NN0'), w.inst('reexpcl')], 'mp2an', '%s e. RR' % E3)
    r10 = w.s([num.fact(w, '; 1 0', 'RR'), num.fact(w, '; 2 0', 'NN0'), w.inst('reexpcl')], 'mp2an', '%s e. RR' % P20)
    tr = w.s([w.s([p1, p3], 'pm3.2i', '( %s <_ %s /\\ %s <_ %s )' % (E40, E3, E3, P20)), w.s([er40, r3, r10], 'letri', '( ( %s <_ %s /\\ %s <_ %s ) -> %s <_ %s )' % (E40, E3, E3, P20, E40, P20))], 'ax-mp', '%s <_ %s' % (E40, P20))
    fin_ = w.s([e3b, tr], 'eqbrtri', S['ldene40'])
    w.qed([fin_], 'idi', S['ldene40'])
    return go(w)


def gen_large():
    w = W('ldenlarge', 'Lean ` logged_density_large ` (Theorem L for ` L >_ 40 ` ): the two covering instances ~ ldenin1 , ~ ldenin0 with ~ ldenri \'s bound ` 2 L B2 ` per parity system: ` 6400 L ^ 2 B2 + 12800 L ^ 2 <_ 3 10 ^ 30 CTau ^ 2 D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) L ^ 14 ` .')
    A = ante('ldenlarge'); P = parts(w, A)
    c, F = denparts(w, A, P)
    idA = w.s([], 'id', '( %s -> %s )' % (A, A))
    i1 = ap(w, A, 'ldenin1', [idA], concl('ldenin1'))
    i0 = ap(w, A, 'ldenin0', [idA], concl('ldenin0'))
    # SUMALL = ZCB ( ZG ) + sum over DB \ { ZG }
    Ax = '( %s /\\ x e. %s )' % (A, DB())
    cx = Ctx(w, Ax)
    zfx, zax = zf_facts(w, Ax, cx([lift(w, F['nN'], Ax), cx([], 'simpr', 'x e. %s' % DB())], 'jca', tsub(NX, {'X': 'x'})), lift(w, F['sr'], Ax), lift(w, F['s0'], Ax), lift(w, F['s1'], Ax), lift(w, F['tr'], Ax), 'x')
    Axq = '( %s /\\ q e. %s )' % (Ax, ZFX('x'))
    onq = w.s([zax], 'r19.21bi', '( %s -> %s e. NN )' % (Axq, ORDX('x', 'q')))
    zcbc = cx([zfx, w.s([onq], 'nncnd', '( %s -> %s e. CC )' % (Axq, ORDX('x', 'q')))], 'fsumcl', '%s e. CC' % ZCB('x'))
    un = dst(w, A, [dst(w, A, [F['zg']], 'x', '') if False else w.s([F['zg'], w.inst('difsnid')], 'syl', '( %s -> ( %s u. { %s } ) = %s )' % (A, Y1, ZG, DB()))], 'eqcomd', '%s = ( %s u. { %s } )' % (DB(), Y1, ZG))
    dj = a1(w, A, 'disjdifr', '( %s i^i { %s } ) = (/)' % (Y1, ZG))
    sp = dst(w, A, [dj, un, F['dbfin'], zcbc], 'fsumsplit', '%s = ( sum_ x e. %s %s + sum_ x e. { %s } %s )' % (SUMALL, Y1, ZCB('x'), ZG, ZCB('x')))
    cg, BZ = w.congr(ZCB('x'), {'x': ZG}, 'x = %s' % ZG, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (ZG, ZG))})
    assert BZ == ZCB(ZG), BZ[:100]
    nx0 = J(w, A, F['nN'], F['zg'])
    zfin0, zal0 = zf_facts(w, A, nx0, F['sr'], F['s0'], F['s1'], F['tr'], ZG)
    Az = '( %s /\\ q e. %s )' % (A, ZFX(ZG))
    on0 = w.s([zal0], 'r19.21bi', '( %s -> %s e. NN )' % (Az, ORDX(ZG, 'q')))
    zcb0 = dst(w, A, [zfin0, w.s([on0], 'nncnd', '( %s -> %s e. CC )' % (Az, ORDX(ZG, 'q')))], 'fsumcl', '%s e. CC' % ZCB(ZG))
    sn = w.s([J(w, A, a1(w, A, 'fvex', '%s e. _V' % ZG), zcb0), w.s([cg], 'sumsn', '( ( %s e. _V /\\ %s e. CC ) -> sum_ x e. { %s } %s = %s )' % (ZG, ZCB(ZG), ZG, ZCB('x'), ZCB(ZG)))], 'syl',
             '( %s -> sum_ x e. { %s } %s = %s )' % (A, ZG, ZCB('x'), ZCB(ZG)))
    S1_ = 'sum_ x e. %s %s' % (Y1, ZCB('x'))
    sp2 = dst(w, A, [sp, dst(w, A, [sn], 'oveq2d', '( %s + sum_ x e. { %s } %s ) = ( %s + %s )' % (S1_, ZG, ZCB('x'), S1_, ZCB(ZG)))], 'eqtrd', '%s = ( %s + %s )' % (SUMALL, S1_, ZCB(ZG)))
    # reals
    yfin = w.s([F['dbfin'], w.inst('diffi')], 'syl', '( %s -> %s e. Fin )' % (A, Y1))
    Ay = '( %s /\\ x e. %s )' % (A, Y1)
    zcbr_y = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Ay, A)), w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (Ay, Y1)), w.inst('eldifi')], 'syl', '( %s -> x e. %s )' % (Ay, DB()))], 'jca', '( %s -> %s )' % (Ay, Ax)), cx([zfx, w.s([onq], 'nnred', '( %s -> %s e. RR )' % (Axq, ORDX('x', 'q')))], 'fsumrecl', '%s e. RR' % ZCB('x'))], 'syl', '( %s -> %s e. RR )' % (Ay, ZCB('x')))
    c.leaf(S1_, 'RR', dst(w, A, [yfin, zcbr_y], 'fsumrecl', '%s e. RR' % S1_))
    c.leaf(ZCB(ZG), 'RR', dst(w, A, [zfin0, w.s([on0], 'nnred', '( %s -> %s e. RR )' % (Az, ORDX(ZG, 'q')))], 'fsumrecl', '%s e. RR' % ZCB(ZG)))
    c.leaf(SUMALL, 'RR', dst(w, A, [sp2, c.mem('( %s + %s )' % (S1_, ZCB(ZG)), 'RR')], 'eqeltrd', '%s e. RR' % SUMALL))
    # the numerals: B2 = 2 10^26 CT2 L^12 PW; total <_ 6400 L^2 B2 + 12800 L^2 <_ 3 10^30 CT2 PW L^14
    P26 = LL.P10('; 2 6'); P30 = LL.P10('; 3 0'); P4 = LL.P10('4')
    for p_, k_ in ((P26, '; 2 6'), (P30, '; 3 0'), (P4, '4')):
        c.leaf(p_, 'NN', w.s([w.s([w.s([], '10nn', '; 1 0 e. NN'), num.fact(w, k_, 'NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % p_)], 'a1i', '( %s -> %s e. NN )' % (A, p_)))
    e30 = w.s([w.s([num.fact(w, '; 1 0', 'CC'), num.fact(w, '; 2 6', 'NN0'), num.fact(w, '4', 'NN0'), w.inst('expadd')], 'mp3an', '( ; 1 0 ^ ( ; 2 6 + 4 ) ) = ( %s x. %s )' % (P26, P4)), w.s([num.add_nat(w, 26, 4)], 'oveq2i', '( ; 1 0 ^ ( ; 2 6 + 4 ) ) = %s' % P30)], 'eqtr3i', '( %s x. %s ) = %s' % (P26, P4, P30))
    e30d = w.s([e30], 'a1i', '( %s -> ( %s x. %s ) = %s )' % (A, P26, P4, P30))
    e4 = w.s([w.s([num.fact(w, '; 1 0', 'NN0'), num.fact(w, '2', 'NN0'), w.s([], '2t2e4', '( 2 x. 2 ) = 4'), w.s([num.fact(w, '; 1 0', 'NN0'), num.fact(w, '1', 'NN0'), w.s([], '2t1e2', '( 2 x. 1 ) = 2'), w.s([num.fact(w, '; 1 0', 'CC'), w.inst('exp1')], 'ax-mp', '( ; 1 0 ^ 1 ) = ; 1 0'), num.mul_lits(w, '; 1 0', '; 1 0')], 'numexp2x', '( ; 1 0 ^ 2 ) = ; ; 1 0 0'), num.mul_lits(w, '; ; 1 0 0', '; ; 1 0 0')], 'numexp2x', '%s = ; ; ; ; 1 0 0 0 0' % P4)], 'a1i', '( %s -> %s = ; ; ; ; 1 0 0 0 0 )' % (A, P4))
    CT2 = '( CTau ^ 2 )'
    for a_ in (LD, PW, CT2, P26, P30, P4, SUMALL, S1_, ZCB(ZG)):
        c.atom(a_)
    # M14 = CT2 ( PW L^14 ); 12800 L^2 <_ 12800 L^2 X = 12800 M14 ; the goal's 10^30 = 10^26 x. 10000
    l12 = ap(w, A, 'expge1', [J(w, A, c.mem(LD, 'RR'), w.s([num.fact(w, '; 1 2', 'NN0')], 'a1i', '( %s -> ; 1 2 e. NN0 )' % A), c.mem(LD, 'ge1'))], '1 <_ %s' % LP('; 1 2'))
    X_ = '( %s x. ( %s x. %s ) )' % (CT2, PW, LP('; 1 2'))
    c.have(X_, 'RR', c.mem(X_, 'RR'))
    x1 = nlinarith(w, A, [F['ct1'], F['pw1'], l12], '1 <_ %s' % X_, closure=c)
    L2_ = '( ; ; ; ; 1 2 8 0 0 x. ( %s ^ 2 ) )' % LD
    m1 = dst(w, A, [num8(w, A, '1'), c.mem(X_, 'RR'), c.mem(L2_, 'RR'), c.ge0(L2_), x1], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (L2_, L2_, X_))
    m1b = dst(w, A, [eqc(w, A, dst(w, A, [c.mem(L2_, 'CC')], 'mulridd', '( %s x. 1 ) = %s' % (L2_, L2_))), m1], 'eqbrtrd', '%s <_ ( %s x. %s )' % (L2_, L2_, X_))
    M14 = '( %s x. ( %s x. %s ) )' % (CT2, PW, LP('; 1 4'))
    c.have(M14, 'RR', c.mem(M14, 'RR')); c.have(M14, 'ge0', c.ge0(M14))
    p26ge1 = dst(w, A, [c.mem(P26, 'NN')], 'nnge1d', '1 <_ %s' % P26)
    hm = dst(w, A, [num8(w, A, '1'), c.mem(P26, 'RR'), c.mem(M14, 'RR'), c.ge0(M14), p26ge1], 'lemul1ad', '( 1 x. %s ) <_ ( %s x. %s )' % (M14, P26, M14))
    hm2 = dst(w, A, [eqc(w, A, dst(w, A, [c.mem(M14, 'CC')], 'mullidd', '( 1 x. %s ) = %s' % (M14, M14))), hm], 'eqbrtrd', '%s <_ ( %s x. %s )' % (M14, P26, M14))
    p30eq = dst(w, A, [eqc(w, A, e30d), dst(w, A, [e4], 'oveq2d', '( %s x. %s ) = ( %s x. ; ; ; ; 1 0 0 0 0 )' % (P26, P4, P26))], 'eqtrd', '%s = ( %s x. ; ; ; ; 1 0 0 0 0 )' % (P30, P26))
    req, RHSp = w.congr(RHS1, {}, A, {}, rules={P30: ('( %s x. ; ; ; ; 1 0 0 0 0 )' % P26, p30eq)})
    PM = '( %s x. %s )' % (P26, M14)
    c.have(PM, 'RR', c.mem(PM, 'RR'))
    pm0 = c.ge0(PM)
    fin0 = linarith(w, A, [sp2, i1, i0, m1b, hm2, pm0], '%s <_ %s' % (SUMALL, RHSp), closure=c, cert={sp2: 1, i1: 1, i0: 1, m1b: 1, hm2: 12800, pm0: 4400})
    return fin(w, dst(w, A, [fin0, req], 'breqtrrd', concl('ldenlarge')))


def gen_small():
    w = W('ldensmall', 'Lean ` logged_density_small ` (Theorem L for ` L < 40 ` , audit F5): the count at abscissa ` 1 / 2 ` ( ~ zcmono , ~ zc1sum ) is at most ` 6400 T N L <_ 6400 e ^ 40 40 <_ 256000 10 ^ 20 <_ 3 10 ^ 30 ` ( ~ ldene40 ).')
    A = ante('ldensmall'); P = parts(w, A)
    c, F = denparts(w, A, P)
    l40 = P['%s < ; 4 0' % LD]
    # monotonicity per character
    Ax = '( %s /\\ x e. %s )' % (A, DB())
    cx = Ctx(w, Ax)
    nxb = cx([lift(w, F['nN'], Ax), cx([], 'simpr', 'x e. %s' % DB())], 'jca', tsub(NX, {'X': 'x'}))
    from zr_e import f2ne0
    hol = cx([nxb, w.inst('zl1ehol')], 'syl', HOLF(EX('x'), HP0))
    e2 = cx([cx([nxb, cx([], '0red', '0 e. RR')], 'jca', '( %s /\\ 0 e. RR )' % tsub(NX, {'X': 'x'})), w.inst('ectr')], 'syl', '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % EX('x'))
    f2 = f2ne0(w, Ax, EX('x'), None, '( 1 / 2 )', bstep=e2)
    MA, MC = ante_of(tsub(stmt('zcmono'), {'F': EX('x'), 'A': '( 1 / 2 )', 'B': 'S'}))
    mono = cx([cx([cx([hol, f2], 'jca', top_and(MA)[0]), cx([cx([num8(w, Ax, '( 1 / 2 )'), lin8(w, Ax, [], '0 < ( 1 / 2 )', {}), lin8(w, Ax, [], '( 1 / 2 ) <_ 1', {})], '3jca', '( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 1 )'),
                                                                    cx([lift(w, F['sr'], Ax), lin8(w, Ax, [lift(w, F['s39'], Ax)], '( 1 / 2 ) <_ S', {'S': lift(w, F['sr'], Ax)})], 'jca', '( S e. RR /\\ ( 1 / 2 ) <_ S )'), lift(w, F['tr'], Ax)], '3jca', top_and(MA)[1])], 'jca', MA), w.inst('zcmono')], 'syl', MC)
    ZH = lambda x: tsub(ZCB(x), {'S': '( 1 / 2 )'})
    assert MC == '%s <_ %s' % (ZCB('x'), ZH('x')), MC[-200:]
    zfx, zax = zf_facts(w, Ax, nxb, lift(w, F['sr'], Ax), lift(w, F['s0'], Ax), lift(w, F['s1'], Ax), lift(w, F['tr'], Ax), 'x')
    Axq = '( %s /\\ q e. %s )' % (Ax, ZFX('x'))
    onq = w.s([zax], 'r19.21bi', '( %s -> %s e. NN )' % (Axq, ORDX('x', 'q')))
    zr = cx([zfx, w.s([onq], 'nnred', '( %s -> %s e. RR )' % (Axq, ORDX('x', 'q')))], 'fsumrecl', '%s e. RR' % ZCB('x'))
    zfxh, zaxh = zf_facts(w, Ax, nxb, num8(w, Ax, '( 1 / 2 )'), lin8(w, Ax, [], '0 < ( 1 / 2 )', {}), lin8(w, Ax, [], '( 1 / 2 ) <_ 1', {}), lift(w, F['tr'], Ax), 'x') if False else (None, None)
    # ZH(x) real: from the sum bound at abscissa 1/2 (zffin at A := 1/2)
    ZA = ante_of(tsub(stmt('zffin'), {'F': EX('x'), 'A': '( 1 / 2 )'}))
    zfh = cx([cx([cx([hol, f2], 'jca', top_and(ZA[0])[0]), cx([cx([num8(w, Ax, '( 1 / 2 )'), lin8(w, Ax, [], '0 < ( 1 / 2 )', {}), lin8(w, Ax, [], '( 1 / 2 ) <_ 1', {})], '3jca', '( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 1 )'), lift(w, F['tr'], Ax)], 'jca', top_and(ZA[0])[1])], 'jca', ZA[0]), w.inst('zffin')], 'syl', ZA[1])
    ZFH = tsub(ZFX('x'), {'S': '( 1 / 2 )'})
    hfin = cx([zfh], 'simpld', '%s e. Fin' % ZFH); hal = cx([zfh], 'simprd', 'A. q e. %s %s e. NN' % (ZFH, ORDX('x', 'q')))
    Axh = '( %s /\\ q e. %s )' % (Ax, ZFH)
    onh = w.s([hal], 'r19.21bi', '( %s -> %s e. NN )' % (Axh, ORDX('x', 'q')))
    zhr = cx([hfin, w.s([onh], 'nnred', '( %s -> %s e. RR )' % (Axh, ORDX('x', 'q')))], 'fsumrecl', '%s e. RR' % ZH('x'))
    fl = dst(w, A, [F['dbfin'], zr, zhr, mono], 'fsumle', '%s <_ sum_ x e. %s %s' % (SUMALL, DB(), ZH('x')))
    SH = 'sum_ x e. %s %s' % (DB(), ZH('x'))
    zs = ap(w, A, 'zc1sum', [J(w, A, F['nN'], J(w, A, F['tr'], linarith(w, A, [F['t2']], '1 <_ T', closure=c)))], concl('zc1sum'))
    assert concl('zc1sum').startswith(SH + ' <_ '), concl('zc1sum')[:100]
    c.leaf(SUMALL, 'RR', dst(w, A, [F['dbfin'], zr], 'fsumrecl', '%s e. RR' % SUMALL)); c.leaf(SH, 'RR', dst(w, A, [F['dbfin'], zhr], 'fsumrecl', '%s e. RR' % SH))
    # DSC = exp ( LD ) < exp 40 <_ 10^20
    ef = w.s([c.mem(DSC, 'RR+'), w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = %s )' % (A, LD, DSC))
    lt = dst(w, A, [l40, dst(w, A, [c.mem(LD, 'RR'), num8(w, A, '; 4 0'), w.inst('eflt')], 'syl2anc', '( %s < ; 4 0 <-> ( exp ` %s ) < ( exp ` ; 4 0 ) )' % (LD, LD))], 'mpbid', '( exp ` %s ) < ( exp ` ; 4 0 )' % LD)
    lt2 = dst(w, A, [eqc(w, A, ef) if False else ef, lt], 'eqbrtrrd', '%s < ( exp ` ; 4 0 )' % DSC)
    e40 = a1(w, A, 'ldene40', S['ldene40'])
    P20 = LL.P10('; 2 0'); P30 = LL.P10('; 3 0'); P10 = LL.P10('; 1 0')
    for p_, k_ in ((P20, '; 2 0'), (P30, '; 3 0'), (P10, '; 1 0')):
        c.leaf(p_, 'NN', w.s([w.s([w.s([], '10nn', '; 1 0 e. NN'), num.fact(w, k_, 'NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % p_)], 'a1i', '( %s -> %s e. NN )' % (A, p_)))
    c.leaf('( exp ` ; 4 0 )', 'RR', dst(w, A, [num8(w, A, '; 4 0')], 'reefcld', '( exp ` ; 4 0 ) e. RR'))
    e30 = w.s([w.s([num.fact(w, '; 1 0', 'CC'), num.fact(w, '; 1 0', 'NN0'), num.fact(w, '; 2 0', 'NN0'), w.inst('expadd')], 'mp3an', '( ; 1 0 ^ ( ; 1 0 + ; 2 0 ) ) = ( %s x. %s )' % (P10, P20)), w.s([num.add_nat(w, 10, 20)], 'oveq2i', '( ; 1 0 ^ ( ; 1 0 + ; 2 0 ) ) = %s' % P30)], 'eqtr3i', '( %s x. %s ) = %s' % (P10, P20, P30))
    e30d = w.s([e30], 'a1i', '( %s -> ( %s x. %s ) = %s )' % (A, P10, P20, P30))
    from lden_b import pow10_8
    p8 = pow10_8(w)
    ten = '; 1 0'
    e10 = w.s([num.fact(w, ten, 'CC'), num.fact(w, '8', 'NN0'), num.fact(w, '2', 'NN0'), w.inst('expadd')], 'mp3an', '( %s ^ ( 8 + 2 ) ) = ( ( %s ^ 8 ) x. ( %s ^ 2 ) )' % (ten, ten, ten))
    e82 = w.s([w.s([num.add_nat(w, 8, 2)], 'oveq2i', '( %s ^ ( 8 + 2 ) ) = %s' % (ten, P10))], 'eqcomi', '%s = ( %s ^ ( 8 + 2 ) )' % (P10, ten))
    e2_ = w.s([num.fact(w, ten, 'NN0'), num.fact(w, '1', 'NN0'), w.s([], '2t1e2', '( 2 x. 1 ) = 2'), w.s([num.fact(w, ten, 'CC'), w.inst('exp1')], 'ax-mp', '( %s ^ 1 ) = %s' % (ten, ten)), num.mul_lits(w, ten, ten)], 'numexp2x', '( %s ^ 2 ) = ; ; 1 0 0' % ten)
    e100 = w.s([p8, e2_], 'oveq12i', '( ( %s ^ 8 ) x. ( %s ^ 2 ) ) = ( ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 x. ; ; 1 0 0 )' % (ten, ten))
    TEN10 = '; ; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0 0'
    e10b = w.s([w.s([w.s([e82, e10], 'eqtri', '%s = ( ( %s ^ 8 ) x. ( %s ^ 2 ) )' % (P10, ten, ten)), e100], 'eqtri', '%s = ( ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 x. ; ; 1 0 0 )' % P10), num.mul_lits(w, '; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0', '; ; 1 0 0')], 'eqtri', '%s = %s' % (P10, TEN10))
    e10d = w.s([e10b], 'a1i', '( %s -> %s = %s )' % (A, P10, TEN10))
    CT2 = '( CTau ^ 2 )'
    l14 = ap(w, A, 'expge1', [J(w, A, c.mem(LD, 'RR'), w.s([num.fact(w, '; 1 4', 'NN0')], 'a1i', '( %s -> ; 1 4 e. NN0 )' % A), c.mem(LD, 'ge1'))], '1 <_ %s' % LP('; 1 4'))
    c.have(LP('; 1 4'), 'RR', c.mem(LP('; 1 4'), 'RR'))
    for a_ in (LD, PW, CT2, P20, P30, P10, 'T', 'N', SUMALL, SH, DSC):
        c.atom(a_)
    X_ = '( %s x. ( %s x. %s ) )' % (CT2, PW, LP('; 1 4'))
    c.have(X_, 'RR', c.mem(X_, 'RR'))
    x1 = nlinarith(w, A, [F['ct1'], F['pw1'], l14], '1 <_ %s' % X_, closure=c)
    # ( T N ) LD <_ DSC 40 ; DSC <_ 10^20 ; P20 <_ P20 X ; the goal's 10^30 = 10^10 x. 10^20 = 10000000000 x. 10^20
    TN = '( T x. N )'
    tn = dst(w, A, [dst(w, A, [c.mem('T', 'CC'), c.mem('N', 'CC')], 'mulcomd', '%s = ( N x. T )' % TN), F['nt']], 'eqbrtrd', '%s <_ %s' % (TN, DSC))
    m1 = dst(w, A, [c.mem(TN, 'RR'), c.mem(DSC, 'RR'), c.mem(LD, 'RR'), num8(w, A, '; 4 0'), c.ge0(TN), c.ge0(LD), tn, ltle(w, A, c, l40)], 'lemul12ad', '( %s x. %s ) <_ ( %s x. ; 4 0 )' % (TN, LD, DSC))
    dle = dst(w, A, [c.mem(DSC, 'RR'), c.mem('( exp ` ; 4 0 )', 'RR'), c.mem(P20, 'RR'), lt2, e40], 'ltletrd', '%s < %s' % (DSC, P20))
    hx = dst(w, A, [num8(w, A, '1'), c.mem(X_, 'RR'), c.mem(P20, 'RR'), c.ge0(P20), x1], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (P20, P20, X_))
    hx2 = dst(w, A, [eqc(w, A, dst(w, A, [c.mem(P20, 'CC')], 'mulridd', '( %s x. 1 ) = %s' % (P20, P20))), hx], 'eqbrtrd', '%s <_ ( %s x. %s )' % (P20, P20, X_))
    p30eq = dst(w, A, [eqc(w, A, e30d), dst(w, A, [e10d], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (P10, P20, TEN10, P20))], 'eqtrd', '%s = ( %s x. %s )' % (P30, TEN10, P20))
    req, RHSp = w.congr(RHS1, {}, A, {}, rules={P30: ('( %s x. %s )' % (TEN10, P20), p30eq)})
    PX = '( %s x. %s )' % (P20, X_)
    c.have(PX, 'RR', c.mem(PX, 'RR'))
    px0 = c.ge0(PX)
    fin0 = linarith(w, A, [fl, zs, m1, dle, hx2, px0], '%s <_ %s' % (SUMALL, RHSp), closure=c, cert={fl: 1, zs: 1, m1: 6400, dle: 256000, hx2: 256000, px0: 30000000000 - 256000})
    return fin(w, dst(w, A, [fin0, req], 'breqtrrd', concl('ldensmall')))


def gen_ld():
    w = W('ldenld', '**Lean ` logged_density ` ** (THEOREM L, routez/Z6-logged.md 3.6): for every ` d >_ 1 ` , ` t >_ 2 ` , ` sigma e. [ 39 / 50 , 1 ] ` , ` sum_ chi N ( sigma , t , chi ) <_ 3 10 ^ 30 CTau ^ 2 ( d ( t + 2 ) ) ^ ( ( 151 / 50 ) ( 1 - sigma ) ) log ^ 14 ( d ( t + 2 ) ) ` ( ~ ldenlarge , ~ ldensmall ).')
    A = ante('ldenld'); P = parts(w, A)
    c, F = denparts(w, A, P)
    GOAL = concl('ldenld')
    A1 = '( %s /\\ %s )' % (A, H40); A2 = '( %s /\\ %s < ; 4 0 )' % (A, LD)
    h1 = w.s([J(w, A1, lift(w, F['nN'], A1), J(w, A1, lift(w, F['hsig'], A1), J(w, A1, J(w, A1, lift(w, F['tr'], A1), lift(w, F['t2'], A1)), w.s([], 'simpr', '( %s -> %s )' % (A1, H40))))), w.inst('ldenlarge')], 'syl', '( %s -> %s )' % (A1, GOAL))
    h2 = w.s([J(w, A2, lift(w, F['nN'], A2), J(w, A2, lift(w, F['hsig'], A2), J(w, A2, J(w, A2, lift(w, F['tr'], A2), lift(w, F['t2'], A2)), w.s([], 'simpr', '( %s -> %s < ; 4 0 )' % (A2, LD))))), w.inst('ldensmall')], 'syl', '( %s -> %s )' % (A2, GOAL))
    tri = dst(w, A, [num8(w, A, '; 4 0'), c.mem(LD, 'RR'), w.inst('lelttric')], 'syl2anc', '( %s \\/ %s < ; 4 0 )' % (H40, LD))
    return fin(w, dst(w, A, [tri, dst(w, A, [w.s([h1], 'ex', '( %s -> ( %s -> %s ) )' % (A, H40, GOAL)), w.s([h2], 'ex', '( %s -> ( %s < ; 4 0 -> %s ) )' % (A, LD, GOAL))], 'jaod', '( ( %s \\/ %s < ; 4 0 ) -> %s )' % (H40, LD, GOAL))], 'mpd', GOAL))


def gen_ledg():
    w = W('ldenledg', 'Lean ` logged_density_ledger ` (the Z0a section 7 / Z0b I3\' form, audit F3): ` ( d ( t + 2 ) ) ^ e <_ 2 ( d t ) ^ e ` for ` 0 <_ e <_ 1 ` , so Theorem L holds with ` ( d t ) ` and the constant ` 6 10 ^ 30 CTau ^ 2 ` .')
    A = ante('ldenledg'); P = parts(w, A)
    c, F = denparts(w, A, P)
    ld = ap(w, A, 'ldenld', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ldenld'))
    NT = '( N x. T )'
    c.leaf(NT, 'RR', c.mem(NT, 'RR')); c.have(NT, 'ge0', c.ge0(NT))
    PT = '( %s ^c %s )' % (NT, EXPS)
    c.leaf(PT, 'RR', ap(w, A, 'recxpcl', [J(w, A, c.mem(NT, 'RR'), c.ge0(NT), c.mem(EXPS, 'RR'))], '%s e. RR' % PT)); c.have(PT, 'ge0', ap(w, A, 'cxpge0', [J(w, A, c.mem(NT, 'RR'), c.ge0(NT), c.mem(EXPS, 'RR'))], '0 <_ %s' % PT))
    NT2 = '( 2 x. %s )' % NT
    m1 = ap(w, A, 'cxple2a', [J(w, A, c.mem(DSC, 'RR'), c.mem(NT2, 'RR'), c.mem(EXPS, 'RR')), J(w, A, c.ge0(DSC), F['ex0']), F['d2']], '%s <_ ( %s ^c %s )' % (PW, NT2, EXPS))
    m2 = dst(w, A, [num8(w, A, '2'), lin8(w, A, [], '0 <_ 2', {}), c.mem(NT, 'RR'), c.ge0(NT), c.mem(EXPS, 'CC')], 'mulcxpd', '( %s ^c %s ) = ( ( 2 ^c %s ) x. %s )' % (NT2, EXPS, EXPS, PT))
    ex1 = linarith(w, A, [F['s39']], '%s <_ 1' % EXPS, closure=c)
    m3 = ap(w, A, 'cxplea', [J(w, A, num8(w, A, '2'), lin8(w, A, [], '1 <_ 2', {})), J(w, A, c.mem(EXPS, 'RR'), num8(w, A, '1')), ex1], '( 2 ^c %s ) <_ ( 2 ^c 1 )' % EXPS)
    m3b = dst(w, A, [m3, dst(w, A, [num8(w, A, '2', 'CC')], 'cxp1d', '( 2 ^c 1 ) = 2')], 'breqtrd', '( 2 ^c %s ) <_ 2' % EXPS)
    T2E = '( 2 ^c %s )' % EXPS
    c.leaf(T2E, 'RR', ap(w, A, 'recxpcl', [J(w, A, num8(w, A, '2'), lin8(w, A, [], '0 <_ 2', {}), c.mem(EXPS, 'RR'))], '%s e. RR' % T2E))
    m4 = dst(w, A, [c.mem(T2E, 'RR'), num8(w, A, '2'), c.mem(PT, 'RR'), c.ge0(PT), m3b], 'lemul1ad', '( %s x. %s ) <_ ( 2 x. %s )' % (T2E, PT, PT))
    pw2 = dst(w, A, [c.mem(PW, 'RR'), c.mem('( %s x. %s )' % (T2E, PT), 'RR'), c.mem('( 2 x. %s )' % PT, 'RR'), dst(w, A, [m1, m2], 'breqtrd', '%s <_ ( %s x. %s )' % (PW, T2E, PT)), m4], 'letrd', '%s <_ ( 2 x. %s )' % (PW, PT))
    CT2 = '( CTau ^ 2 )'
    P30 = LL.P10('; 3 0')
    c.leaf(P30, 'NN', w.s([w.s([w.s([], '10nn', '; 1 0 e. NN'), num.fact(w, '; 3 0', 'NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % P30)], 'a1i', '( %s -> %s e. NN )' % (A, P30)))
    c.have(LP('; 1 4'), 'RR', c.mem(LP('; 1 4'), 'RR')); c.have(LP('; 1 4'), 'ge0', c.ge0(LP('; 1 4')))
    for a_ in (LD, PW, PT, CT2, P30, SUMALL):
        c.atom(a_)
    # SUMALL is real: lerelxr on ld? use the sum's real-ness from the antecedent-free route: ld gives SUMALL <_ RHS1 with RHS1 real; SUMALL e. RR from the terms
    Ax = '( %s /\\ x e. %s )' % (A, DB())
    cx = Ctx(w, Ax)
    nxb = cx([lift(w, F['nN'], Ax), cx([], 'simpr', 'x e. %s' % DB())], 'jca', tsub(NX, {'X': 'x'}))
    zfx, zax = zf_facts(w, Ax, nxb, lift(w, F['sr'], Ax), lift(w, F['s0'], Ax), lift(w, F['s1'], Ax), lift(w, F['tr'], Ax), 'x')
    Axq = '( %s /\\ q e. %s )' % (Ax, ZFX('x'))
    onq = w.s([zax], 'r19.21bi', '( %s -> %s e. NN )' % (Axq, ORDX('x', 'q')))
    zr = cx([zfx, w.s([onq], 'nnred', '( %s -> %s e. RR )' % (Axq, ORDX('x', 'q')))], 'fsumrecl', '%s e. RR' % ZCB('x'))
    c.leaf(SUMALL, 'RR', dst(w, A, [F['dbfin'], zr], 'fsumrecl', '%s e. RR' % SUMALL))
    K3 = '( ( 3 x. %s ) x. %s )' % (P30, CT2)
    c.have(K3, 'RR', c.mem(K3, 'RR')); c.have(K3, 'ge0', c.ge0(K3))
    m5 = dst(w, A, [c.mem(PW, 'RR'), c.mem('( 2 x. %s )' % PT, 'RR'), c.mem(K3, 'RR'), c.ge0(K3), pw2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 2 x. %s ) )' % (K3, PW, K3, PT))
    L14 = LP('; 1 4')
    m6 = dst(w, A, [c.mem('( %s x. %s )' % (K3, PW), 'RR'), c.mem('( %s x. ( 2 x. %s ) )' % (K3, PT), 'RR'), c.mem(L14, 'RR'), c.ge0(L14), m5], 'lemul1ad', '( ( %s x. %s ) x. %s ) <_ ( ( %s x. ( 2 x. %s ) ) x. %s )' % (K3, PW, L14, K3, PT, L14))
    assert RHS1 == '( ( %s x. %s ) x. %s )' % (K3, PW, L14), RHS1
    e6 = ringeq(w, A, '( ( %s x. ( 2 x. %s ) ) x. %s )' % (K3, PT, L14), RHSL, c)
    t1 = dst(w, A, [c.mem(SUMALL, 'RR'), c.mem(RHS1, 'RR'), c.mem('( ( %s x. ( 2 x. %s ) ) x. %s )' % (K3, PT, L14), 'RR'), ld, m6], 'letrd', '%s <_ ( ( %s x. ( 2 x. %s ) ) x. %s )' % (SUMALL, K3, PT, L14))
    return fin(w, dst(w, A, [t1, e6], 'breqtrd', concl('ldenledg')))


def gen_cbv():
    w = W('ldencbv', 'The zero-count sum in LOGGED\'s letters: ` x q r -> y p o ` (closed, ~ cbvsumv , ~ cbvrabv ).')
    ZO = lambda x: tsub(ZFX(x), {'r': 'o'})
    # inner: sum_ q e. ZFX(x) ORDX(x,q) = sum_ p e. ZO(x) ORDX(x,p)  (for the class letter x, then y)
    def inner(x):
        cg, _ = w.congr(ORDX(x, 'q'), {'q': 'p'}, 'q = p', {'q': w.s([], 'id', '( q = p -> q = p )')})
        c1 = w.s([cg], 'cbvsumv', 'sum_ q e. %s %s = sum_ p e. %s %s' % (ZFX(x), ORDX(x, 'q'), ZFX(x), ORDX(x, 'p')))
        cg2, _ = w.wcongr('( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX(x), {'r': 'o'}, 'r = o', {'r': w.s([], 'id', '( r = o -> r = o )')})
        c2 = w.s([cg2], 'cbvrabv', '%s = %s' % (ZFX(x), ZO(x)))
        c3 = w.s([c2], 'sumeq1i', 'sum_ p e. %s %s = sum_ p e. %s %s' % (ZFX(x), ORDX(x, 'p'), ZO(x), ORDX(x, 'p')))
        return w.s([c1, c3], 'eqtri', 'sum_ q e. %s %s = sum_ p e. %s %s' % (ZFX(x), ORDX(x, 'q'), ZO(x), ORDX(x, 'p')))
    cgo, BODYy = w.congr(ZCB('x'), {'x': 'y'}, 'x = y', {'x': w.s([], 'id', '( x = y -> x = y )')})
    assert BODYy == ZCB('y')
    o1 = w.s([cgo], 'cbvsumv', '%s = sum_ y e. %s %s' % (SUMALL, DB(), ZCB('y')))
    iy = inner('y')
    o2 = w.s([w.s([iy], 'a1i', '( y e. %s -> sum_ q e. %s %s = sum_ p e. %s %s )' % (DB(), ZFX('y'), ORDX('y', 'q'), ZO('y'), ORDX('y', 'p')))], 'sumeq2i', 'sum_ y e. %s %s = sum_ y e. %s sum_ p e. %s %s' % (DB(), ZCB('y'), DB(), ZO('y'), ORDX('y', 'p')))
    fin_ = w.s([o1, o2], 'eqtri', S['ldencbv'])
    assert 'sum_ y e. %s sum_ p e. %s %s' % (DB(), ZO('y'), ORDX('y', 'p')) == SUMY, (SUMY[:200])
    w.qed([fin_], 'idi', S['ldencbv'])
    return go(w)


def gen_headline():
    w = W('loggeddensity', '**Lean ` loggedDensity ` : THE LOGGED ZERO-DENSITY STATEMENT ` Carmichael.LoggedDensity ` ** (DensityInterface.lean, tools/zdilib.py LOGGED verbatim), with ` h = 6 10 ^ 30 CTau ^ 2 ` , ` w = 151 / 50 ` , ` c = 1 ` , ` k = 14 ` ( ~ ldenledg in the letters ` m u v ` , ~ ldencbv ). The last analytic input of the main theorem.')
    SUBM = {'N': 'm', 'S': 'u', 'T': 'v'}
    LDm = tsub(LD, SUBM); SUMYm = tsub(SUMY, SUBM); EXm = tsub(EXPS, SUBM)
    A = '( ( m e. NN /\\ v e. RR /\\ u e. RR ) /\\ ( 2 <_ v /\\ ( ; 3 9 / ; 5 0 ) <_ u /\\ u <_ 1 ) )'
    c = Ctx(w, A)
    mn, vr, ur, v2, u39, u1 = [c.g(x) for x in ('m e. NN', 'v e. RR', 'u e. RR', '2 <_ v', '( ; 3 9 / ; 5 0 ) <_ u', 'u <_ 1')]
    LA, LC = ante_of(tsub(S['ldenledg'], SUBM))
    hyp = c([mn, c([c([ur, c([u39, u1], 'jca', '( ( ; 3 9 / ; 5 0 ) <_ u /\\ u <_ 1 )')], 'jca', tsub(HSIG, SUBM)), c([vr, v2], 'jca', '( v e. RR /\\ 2 <_ v )')], 'jca', '( %s /\\ ( v e. RR /\\ 2 <_ v ) )' % tsub(HSIG, SUBM))], 'jca', LA)
    ld = c([hyp, w.inst('ldenledg')], 'syl', LC)
    cbv = c.a1(w.s([], 'ldencbv', tsub(S['ldencbv'], SUBM)), tsub(S['ldencbv'], SUBM))
    ld2 = c([cbv, ld], 'eqbrtrrd', LC.replace(tsub(SUMALL, SUBM), SUMYm, 1))
    # ( m x. v ) = ( m x. ( v ^c 1 ) )
    v1 = c([c([vr], 'recnd', 'v e. CC')], 'cxp1d', '( v ^c 1 ) = v')
    mv = c([c([v1], 'oveq2d', '( m x. ( v ^c 1 ) ) = ( m x. v )')], 'eqcomd', '( m x. v ) = ( m x. ( v ^c 1 ) )')
    H0m = H0
    RHSm = tsub(RHSL, SUBM)
    RHSf = RHSm.replace('( m x. v )', '( m x. ( v ^c 1 ) )', 1)
    e1 = c([c([c([mv], 'oveq1d', '( ( m x. v ) ^c %s ) = ( ( m x. ( v ^c 1 ) ) ^c %s )' % (EXm, EXm))], 'oveq2d', '( %s x. ( ( m x. v ) ^c %s ) ) = ( %s x. ( ( m x. ( v ^c 1 ) ) ^c %s ) )' % (H0m, EXm, H0m, EXm))], 'oveq1d', '%s = %s' % (RHSm, RHSf))
    ld3 = c([ld2, e1], 'breqtrd', '%s <_ %s' % (SUMYm, RHSf))
    BODY = '( ( 2 <_ v /\\ ( ; 3 9 / ; 5 0 ) <_ u /\\ u <_ 1 ) -> %s <_ %s )' % (SUMYm, RHSf)
    imp_ = w.s([ld3], 'ex', '( ( m e. NN /\\ v e. RR /\\ u e. RR ) -> %s )' % BODY)
    al = w.s([imp_], 'rgen3', 'A. m e. NN A. v e. RR A. u e. RR %s' % BODY)
    # the constants
    W_ = '( ; ; 1 5 1 / ; 5 0 )'
    p30n = w.s([w.s([], '10nn', '; 1 0 e. NN'), num.fact(w, '; 3 0', 'NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % LL.P10('; 3 0'))
    p30r = w.s([p30n], 'nnrei', '%s e. RR' % LL.P10('; 3 0'))
    ctn = w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'), w.s([w.s([], '2nn', '2 e. NN'), w.s([w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. NN')], 'eqeltri', 'CTau e. NN')
    ctr = w.s([ctn], 'nnrei', 'CTau e. RR')
    ct2r = w.s([ctr, num.fact(w, '2', 'NN0'), w.inst('reexpcl')], 'mp2an', '( CTau ^ 2 ) e. RR')
    ct2ge1 = w.s([w.s([ctr, num.fact(w, '2', 'NN0'), w.s([ctn, w.inst('nnge1')], 'ax-mp', '1 <_ CTau')], '3pm3.2i', '( CTau e. RR /\\ 2 e. NN0 /\\ 1 <_ CTau )'), w.inst('expge1')], 'ax-mp', '1 <_ ( CTau ^ 2 )')
    six = w.s([num.fact(w, '6', 'RR'), p30r], 'remulcli', '( 6 x. %s ) e. RR' % LL.P10('; 3 0'))
    h0r = w.s([six, ct2r], 'remulcli', '%s e. RR' % H0)
    lv = {LL.P10('; 3 0'): p30r, '( CTau ^ 2 )': ct2r}
    A0 = 'T.'
    tru = w.s([], 'tru', 'T.')
    def cl(st, f):
        return w.s([st], 'a1i', '( T. -> %s )' % f)
    p30ge1 = w.s([p30n, w.inst('nnge1')], 'ax-mp', '1 <_ %s' % LL.P10('; 3 0'))
    h1 = linarith(w, A0, [cl(p30ge1, '1 <_ %s' % LL.P10('; 3 0')), cl(ct2ge1, '1 <_ ( CTau ^ 2 )')], '1 <_ %s' % H0, leaves={LL.P10('; 3 0'): cl(p30r, '%s e. RR' % LL.P10('; 3 0')), '( CTau ^ 2 )': cl(ct2r, '( CTau ^ 2 ) e. RR')}, products=True)
    h1c = w.s([tru, h1], 'ax-mp', '1 <_ %s' % H0)
    w0 = num.fact(w, W_, 'ge0'); w72 = num.le_lit(w, W_, '( 7 / 2 )'); c1 = w.s([], '1le1', '1 <_ 1'); c54 = num.le_lit(w, '1', '( 5 / 4 )')
    wr = num.fact(w, W_, 'RR'); onr = num.fact(w, '1', 'RR'); k14 = w.s([num.fact(w, '1', 'NN0'), num.fact(w, '4', 'NN0')], 'deccl', '; 1 4 e. NN0')
    CONS = '( ( ( %s e. RR /\\ %s e. RR /\\ 1 e. RR ) /\\ ; 1 4 e. NN0 ) /\\ ( ( 1 <_ %s /\\ 0 <_ %s /\\ %s <_ ( 7 / 2 ) ) /\\ ( 1 <_ 1 /\\ 1 <_ ( 5 / 4 ) ) ) /\\ A. m e. NN A. v e. RR A. u e. RR %s )' % (H0, W_, H0, W_, W_, BODY)
    full = w.s([w.s([w.s([h0r, wr, onr], '3pm3.2i', '( %s e. RR /\\ %s e. RR /\\ 1 e. RR )' % (H0, W_)), k14], 'pm3.2i', '( ( %s e. RR /\\ %s e. RR /\\ 1 e. RR ) /\\ ; 1 4 e. NN0 )' % (H0, W_)),
                w.s([w.s([h1c, w0, w72], '3pm3.2i', '( 1 <_ %s /\\ 0 <_ %s /\\ %s <_ ( 7 / 2 ) )' % (H0, W_, W_)), w.s([c1, c54], 'pm3.2i', '( 1 <_ 1 /\\ 1 <_ ( 5 / 4 ) )')], 'pm3.2i', '( ( 1 <_ %s /\\ 0 <_ %s /\\ %s <_ ( 7 / 2 ) ) /\\ ( 1 <_ 1 /\\ 1 <_ ( 5 / 4 ) ) )' % (H0, W_, W_)), al], '3pm3.2i', CONS)
    # the four existentials, innermost first: k, c, w, h (~ spcev with the substitution biconditional under the inner prefix)
    BODYW = lambda h, w_, c_, k_: tsub('( ( ( h e. RR /\\ w e. RR /\\ c e. RR ) /\\ k e. NN0 ) /\\ ( ( 1 <_ h /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) ) /\\ ( 1 <_ c /\\ c <_ ( 5 / 4 ) ) ) /\\ A. m e. NN A. v e. RR A. u e. RR ( ( 2 <_ v /\\ ( ; 3 9 / ; 5 0 ) <_ u /\\ u <_ 1 ) -> %s <_ ( ( h x. ( ( m x. ( v ^c c ) ) ^c ( w x. ( 1 - u ) ) ) ) x. ( ( log ` ( m x. ( v + 2 ) ) ) ^ k ) ) ) )' % SUMYm,
                                        {'h': h, 'w': w_, 'c': c_, 'k': k_})
    assert BODYW(H0, W_, '1', '; 1 4') == CONS, (BODYW(H0, W_, '1', '; 1 4')[:300], CONS[:300])
    vals = {'h': H0, 'w': W_, 'c': '1', 'k': '; 1 4'}
    exs = {'k': w.s([k14], 'elexi', '; 1 4 e. _V'), 'c': w.s([], '1ex', '1 e. _V'), 'w': w.s([], 'ovex', '%s e. _V' % W_), 'h': w.s([], 'ovex', '%s e. _V' % H0)}
    order = ['k', 'c', 'w', 'h']
    cur = full; curf = CONS
    for i, var in enumerate(order):
        val = vals[var]
        m = {v_: (v_ if order.index(v_) <= i else vals[v_]) for v_ in vals}
        gen_ = BODYW(m['h'], m['w'], m['c'], m['k'])
        m2 = dict(m); m2[var] = val
        ps_ = BODYW(m2['h'], m2['w'], m2['c'], m2['k'])
        pref = ''.join('E. %s ' % v_ for v_ in reversed(order[:i]))
        ph = pref + gen_; ps = pref + ps_
        assert ps == curf, (ps[:200], curf[:200])
        bi, new = w.wcongr(gen_, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
        assert new == ps_, (new[:200], ps_[:200])
        st = bi; inner_ph, inner_ps = gen_, ps_
        for v_ in order[:i]:
            inner_ph = 'E. %s %s' % (v_, inner_ph); inner_ps = 'E. %s %s' % (v_, inner_ps)
            st = w.s([st], 'exbidv', '( %s = %s -> ( %s <-> %s ) )' % (var, val, inner_ph, inner_ps))
        assert inner_ph == ph and inner_ps == ps
        spc = w.s([exs[var], st], 'spcev', '( %s -> E. %s %s )' % (ps, var, ph))
        cur = w.s([cur, spc], 'ax-mp', 'E. %s %s' % (var, ph)); curf = 'E. %s %s' % (var, ph)
    assert curf == S['loggeddensity'], (curf[:300], S['loggeddensity'][:300])
    w.qed([cur], 'idi', S['loggeddensity'])
    return go(w)


GENS = {'ldenwin': gen_win, 'ldenlc1': gen_lc1, 'ldenlc0': gen_lc0, 'ldenlc': gen_lc, 'ldenlow': gen_low, 'ldenin1': gen_in1, 'ldenin0': gen_in0, 'ldene40': gen_e40,
        'ldenlarge': gen_large, 'ldensmall': gen_small, 'ldenld': gen_ld, 'ldenledg': gen_ledg, 'ldencbv': gen_cbv, 'loggeddensity': gen_headline}
if __name__ == '__main__':
    for lab in (only or list(GENS)):
        GENS[lab]()
