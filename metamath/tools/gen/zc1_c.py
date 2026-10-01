"""Sortie ZC1: centre bounds on Re = 2 (dchrctr, ectr, zc1x1, zetactr, etactr)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
from c8_o import numst
import lin
lin.FASTPATH = True

CX = '( a e. NN |-> ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) ) )'
MUMAP = '( q e. NN |-> ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` q ) ) x. ( mmu ` q ) ) )'


def DSC(Z, C=CX):
    return 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u %s ) )' % (C, Z)


def isyl(w, A0, label, sub, ante_step):
    """( A0 -> concl ) from ante_step : ( A0 -> ante ) of the closed theorem LABEL instantiated by SUB"""
    a, c = ante_of(tsub(stmt(label), sub))
    return w.s([ante_step, w.inst(label)], 'syl', '( %s -> %s )' % (A0, c)), c


S['dchrctr'] = '( ( %s /\\ ( Z e. CC /\\ ( Re ` Z ) = 2 ) ) -> ( 1 / 2 ) <_ ( abs ` %s ) )' % (NX, DSC('Z'))
S['ectr'] = '( ( %s /\\ T e. RR ) -> ( 1 / 2 ) <_ ( abs ` ( %s ` %s ) ) )' % (NX, E, CT('T'))
Y1 = "( ( ZRHom ` ( Z/nZ ` 1 ) ) ` K )"
S['zc1x1'] = '( ( Y e. ( Base ` ( DChr ` 1 ) ) /\\ K e. ZZ ) -> ( Y ` %s ) = 1 )' % Y1
S['zetactr'] = '( ( Z e. CC /\\ ( Re ` Z ) = 2 ) -> ( sum_ k e. NN ( k ^c -u Z ) e. CC /\\ ( 1 / 2 ) <_ ( abs ` sum_ k e. NN ( k ^c -u Z ) ) ) )'
S['etactr'] = '( T e. RR -> ( 1 / 4 ) <_ ( abs ` ( %s ` %s ) ) )' % (ETA, CT('T'))


def gen_dchrctr():
    w = W('dchrctr', 'Centre bound for the Dirichlet series of any character on ` Re Z = 2 ` : the series times the Moebius series is ` 1 ` ( ~ lchrmu ) and the Moebius series is at most ` 2 ` in modulus ( ~ dserbnd ); C10\'s ~ lchrctr without the Abel continuation, principal characters included.')
    A0 = '( %s /\\ ( Z e. CC /\\ ( Re ` Z ) = 2 ) )' % NX
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', NX); zc = s([], 'simprl', 'Z e. CC'); re2 = s([], 'simprr', '( Re ` Z ) = 2')
    rez = s([zc], 'recld', '( Re ` Z ) e. RR')
    z1 = s([zc, lin8(w, A0, [re2], '1 < ( Re ` Z )', {'( Re ` Z )': rez})], 'jca', '( Z e. CC /\\ 1 < ( Re ` Z ) )')
    mu, muc = isyl(w, A0, 'lchrmu', {}, s([nx, z1], 'jca', ante_of(stmt('lchrmu'))[0]))
    MS = muc.split(' x. sum_', 1)[0][2:]
    DSX = muc[len('( %s x. ' % MS):-len(' ) = 1')]
    DS = DSC('Z')
    Ak = '( %s /\\ k e. NN )' % A0
    cv = w.s([w.s([lift(w, nx, Ak), w.s([], 'simpr', '( %s -> k e. NN )' % Ak)], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX)), w.inst('zl1cxv')], 'syl',
             '( %s -> ( %s ` k ) = ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) )' % (Ak, CX))
    cv2 = w.s([cv], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u Z ) ) )' % (Ak, CX))
    dse = s([cv2], 'sumeq2dv', '%s = %s' % (DS, DSX))
    chs, chc = isyl(w, A0, 'zl2chs', {}, s([nx, z1], 'jca', ante_of(stmt('zl2chs'))[0]))
    dsc = s([chs, w.inst('simpl')], 'syl', '%s e. CC' % DS)
    dsxc = s([dse, dsc], 'eqeltrrd', '%s e. CC' % DSX)
    cf = s([nx, w.inst('lchmucfb')], 'syl', '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (MUMAP, MUMAP))
    DB = tsub(stmt('dserbnd'), {'A': MUMAP, 'C': '1'})
    dba, dbc = ante_of(DB)
    db = s([s([cf, z1], 'jca', dba), w.inst('dserbnd')], 'syl', dbc)
    SMA = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) )' % MUMAP
    mv = w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Ak), w.inst('lchmuval')], 'syl', '( %s -> ( %s ` k ) = ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( mmu ` k ) ) )' % (Ak, MUMAP))
    mv2 = w.s([mv], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( mmu ` k ) ) x. ( k ^c -u Z ) ) )' % (Ak, MUMAP))
    se = s([mv2], 'sumeq2dv', '%s = %s' % (SMA, MS))
    RHS = dbc.split(' <_ ', 1)[1]
    r1 = s([re2], 'oveq1d', '( ( Re ` Z ) - 1 ) = ( 2 - 1 )')
    r2 = s([s([r1, s([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')], 'eqtrd', '( ( Re ` Z ) - 1 ) = 1')], 'oveq2d', '( 1 / ( ( Re ` Z ) - 1 ) ) = ( 1 / 1 )')
    r3 = s([r2, s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')], 'eqtrd', '( 1 / ( ( Re ` Z ) - 1 ) ) = 1')
    r4 = s([s([r3], 'oveq2d', '( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) ) = ( 1 + 1 )'), s([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2')], 'eqtrd',
           '( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) ) = 2')
    r5 = s([s([r4], 'oveq2d', '%s = ( 1 x. 2 )' % RHS), s([s([], '2cnd', '2 e. CC')], 'mullidd', '( 1 x. 2 ) = 2')], 'eqtrd', '%s = 2' % RHS)
    mb0 = s([s([se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (SMA, MS)), db], 'eqbrtrrd', '( abs ` %s ) <_ %s' % (MS, RHS))
    mb = s([mb0, r5], 'breqtrd', '( abs ` %s ) <_ 2' % MS)
    msc = s([s([cf, z1], 'jca', dba), w.inst('dsercl')], 'syl', '%s e. CC' % SMA)
    msc = s([s([se], 'eqcomd', '%s = %s' % (MS, SMA)), msc], 'eqeltrd', '%s e. CC' % MS)
    am = s([msc, dsxc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (MS, DSX, MS, DSX))
    a1 = s([s([mu], 'fveq2d', '( abs ` ( %s x. %s ) ) = ( abs ` 1 )' % (MS, DSX)), s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')], 'eqtrd',
           '( abs ` ( %s x. %s ) ) = 1' % (MS, DSX))
    one = s([a1, am], 'eqtr3d', '1 = ( ( abs ` %s ) x. ( abs ` %s ) )' % (MS, DSX))
    ADS = '( abs ` %s )' % DSX
    adr = s([dsxc], 'abscld', '%s e. RR' % ADS)
    le = s([s([msc], 'abscld', '( abs ` %s ) e. RR' % MS), s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), adr, s([dsxc], 'absge0d', '0 <_ %s' % ADS), mb], 'lemul1ad',
           '( ( abs ` %s ) x. %s ) <_ ( 2 x. %s )' % (MS, ADS, ADS))
    le1 = s([one, le], 'eqbrtrd', '1 <_ ( 2 x. %s )' % ADS)
    h = lin8(w, A0, [le1], '( 1 / 2 ) <_ %s' % ADS, {ADS: adr})
    goal = S['dchrctr']
    w.qed([h, s([dse], 'fveq2d', '( abs ` %s ) = %s' % (DS, ADS))], 'breqtrrd', goal)
    return run8(w)


def gen_ectr():
    w = W('ectr', 'Centre bound for ` E = ( s - 1 ) L ( s , X ) ` : ` 1 / 2 <_ abs E ( 2 + i T ) ` for every character ( ~ zl1dser , ~ dchrctr , ` abs ( 1 + i T ) >_ 1 ` ).')
    A0 = '( %s /\\ T e. RR )' % NX
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', NX); tr = s([], 'simpr', 'T e. RR')
    import c9_h
    patch(c9_h)
    from c9_h import c0_facts
    c0, re0, im0 = c0_facts(w, A0, tr)
    ch = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)), ch], 'mpbird', '%s e. %s' % (C0, HP0))
    DSR = ante_of(stmt('zl1dser'))[1]
    ds = s([nx, w.inst('zl1dser')], 'syl', DSR)
    body = DSR[len("A. s e. %s " % HP0):]
    sub = {'s': C0}
    inst = tsub(body, sub)
    # rspcdva on s = C0
    import congr
    eqs = '( s = %s -> ( %s <-> %s ) )' % (C0, body, inst)
    stq, _ = w.wcongr(body, {'s': C0}, 's = %s' % C0, {'s': w.s([], 'id', '( s = %s -> s = %s )' % (C0, C0))})
    v = w.s([stq, ds, c0h], 'rspcdva', '( %s -> %s )' % (A0, inst))
    g1 = s([lin8(w, A0, [], '1 < 2', {}), re0], 'breqtrrd', '1 < ( Re ` %s )' % C0)
    ev = s([g1, v], 'mpd', inst.split(' -> ', 1)[1][:-2])
    EC = '( %s ` %s )' % (E, C0)
    D1 = '( %s - 1 )' % C0
    DS = DSC(C0)
    d1c = s([c0, s([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % D1)
    dct, _ = isyl(w, A0, 'dchrctr', {'Z': C0}, s([nx, s([c0, re0], 'jca', '( %s e. CC /\\ ( Re ` %s ) = 2 )' % (C0, C0))], 'jca', ante_of(tsub(S['dchrctr'], {'Z': C0}))[0]))
    chs, _ = isyl(w, A0, 'zl2chs', {'Z': C0}, s([nx, s([c0, g1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (C0, C0))], 'jca', ante_of(tsub(stmt('zl2chs'), {'Z': C0}))[0]))
    dsc = s([chs, w.inst('simpl')], 'syl', '%s e. CC' % DS)
    am = s([d1c, dsc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (D1, DS, D1, DS))
    rd1 = s([c0, s([], '1cnd', '1 e. CC')], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` 1 ) )' % (D1, C0))
    re1 = s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( Re ` 1 ) = 1')
    ar = s([d1c], 'abs.rele', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (D1, D1)) if False else s([d1c, w.inst('absrele')], 'syl', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (D1, D1))
    rr = s([d1c], 'recld', '( Re ` %s ) e. RR' % D1)
    lvr = {'( Re ` %s )' % D1: rr, '( Re ` %s )' % C0: s([c0], 'recld', '( Re ` %s ) e. RR' % C0), '( Re ` 1 )': s([w.s([], '1re', '1 e. RR')], 'a1i', '( Re ` 1 ) e. RR') if False else None}
    del lvr['( Re ` 1 )']
    rv1 = lin.linarith(w, A0, [rd1, re1, re0], '( Re ` %s ) = 1' % D1, closure=None) if False else None
    rv1 = s([s([rd1, s([re0, re1], 'oveq12d', '( ( Re ` %s ) - ( Re ` 1 ) ) = ( 2 - 1 )' % C0)], 'eqtrd', '( Re ` %s ) = ( 2 - 1 )' % D1),
             s([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')], 'eqtrd', '( Re ` %s ) = 1' % D1)
    ar1 = s([s([rv1], 'fveq2d', '( abs ` ( Re ` %s ) ) = ( abs ` 1 )' % D1), s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')], 'eqtrd', '( abs ` ( Re ` %s ) ) = 1' % D1)
    ge1 = s([ar1, ar], 'eqbrtrrd', '1 <_ ( abs ` %s )' % D1)
    AD1, ADS = '( abs ` %s )' % D1, '( abs ` %s )' % DS
    lv = {AD1: s([d1c], 'abscld', '%s e. RR' % AD1), ADS: s([dsc], 'abscld', '%s e. RR' % ADS)}
    prod = '( %s x. %s )' % (AD1, ADS)
    lv2 = dict(lv)
    lv2[prod] = s([lv[AD1], lv[ADS]], 'remulcld', '%s e. RR' % prod)
    # ( AD1 - 1 ) x. ADS >= 0
    hint = s([s([lv[AD1], s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % AD1), lv[ADS],
              lin8(w, A0, [ge1], '0 <_ ( %s - 1 )' % AD1, {AD1: lv[AD1]}), s([dsc], 'absge0d', '0 <_ %s' % ADS)], 'mulge0d', '0 <_ ( ( %s - 1 ) x. %s )' % (AD1, ADS))
    import cl as _cl
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    fin = lin.linarith(w, A0, [hint, dct], '( 1 / 2 ) <_ %s' % prod, closure=c, products=True)
    ae = s([s([ev], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. %s ) )' % (EC, D1, DS)), am], 'eqtrd', '( abs ` %s ) = %s' % (EC, prod))
    goal = S['ectr']
    w.qed([fin, ae], 'breqtrrd', goal)
    return run8(w)


U1 = '( 0g ` ( DChr ` 1 ) )'
L1 = '( ZRHom ` ( Z/nZ ` 1 ) )'


def gen_zc1x1():
    w = W('zc1x1', 'A character mod ` 1 ` takes the value ` 1 ` at every integer ( ~ dchrzrh1 , ~ zndvds : every integer is ` 1 ` mod ` 1 ` ).')
    A0 = '( Y e. ( Base ` ( DChr ` 1 ) ) /\\ K e. ZZ )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yb = s([], 'simpl', 'Y e. ( Base ` ( DChr ` 1 ) )'); kz = s([], 'simpr', 'K e. ZZ')
    e1 = w.s([], 'eqid', '( Z/nZ ` 1 ) = ( Z/nZ ` 1 )')
    e2 = w.s([], 'eqid', '%s = %s' % (L1, L1))
    zd = w.s([e1, e2], 'zndvds', '( ( 1 e. NN0 /\\ K e. ZZ /\\ 1 e. ZZ ) -> ( ( %s ` K ) = ( %s ` 1 ) <-> 1 || ( K - 1 ) ) )' % (L1, L1))
    n0 = s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0')
    z1 = s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')
    bi = s([n0, kz, z1, zd], 'syl3anc', '( ( %s ` K ) = ( %s ` 1 ) <-> 1 || ( K - 1 ) )' % (L1, L1))
    dv = s([s([kz, z1], 'zsubcld', '( K - 1 ) e. ZZ'), w.inst('1dvds')], 'syl', '1 || ( K - 1 )')
    lk = s([dv, bi], 'mpbird', '( %s ` K ) = ( %s ` 1 )' % (L1, L1))
    g = w.s([], 'eqid', '( DChr ` 1 ) = ( DChr ` 1 )')
    b = w.s([], 'eqid', '( Base ` ( DChr ` 1 ) ) = ( Base ` ( DChr ` 1 ) )')
    one = w.s([g, e1, b, e2, yb], 'dchrzrh1', '( %s -> ( Y ` ( %s ` 1 ) ) = 1 )' % (A0, L1))
    w.qed([s([lk], 'fveq2d', '( Y ` ( %s ` K ) ) = ( Y ` ( %s ` 1 ) )' % (L1, L1)), one], 'eqtrd', S['zc1x1'])
    return run8(w)


def u1base(w, A0):
    """( A0 -> ( 0g ` ( DChr ` 1 ) ) e. ( Base ` ( DChr ` 1 ) ) )"""
    g = w.s([], 'eqid', '( DChr ` 1 ) = ( DChr ` 1 )')
    ab = w.s([g], 'dchrabl', '( 1 e. NN -> ( DChr ` 1 ) e. Abel )')
    ab1 = w.s([w.s([], '1nn', '1 e. NN'), ab], 'ax-mp', '( DChr ` 1 ) e. Abel')
    gr = w.s([ab1, w.inst('ablgrp')], 'ax-mp', '( DChr ` 1 ) e. Grp')
    b = w.s([], 'eqid', '( Base ` ( DChr ` 1 ) ) = ( Base ` ( DChr ` 1 ) )')
    o = w.s([], 'eqid', '%s = %s' % (U1, U1))
    gi = w.s([b, o], 'grpidcl', '( ( DChr ` 1 ) e. Grp -> %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    return w.s([w.s([gr, gi], 'ax-mp', '%s e. ( Base ` ( DChr ` 1 ) )' % U1)], 'a1i', '( %s -> %s e. ( Base ` ( DChr ` 1 ) ) )' % (A0, U1))


CX1 = '( a e. NN |-> ( %s ` ( %s ` a ) ) )' % (U1, L1)


def cx1val(w, A0, ub):
    """( ( A0 /\\ k e. NN ) -> ( CX1 ` k ) = 1 )"""
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nx1 = w.s([w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % Ak), lift(w, ub, Ak)], 'jca', '( %s -> ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) )' % (Ak, U1))
    cv = w.s([w.s([nx1, kn], 'jca', '( %s -> ( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ k e. NN ) )' % (Ak, U1)), w.inst('zl1cxv')], 'syl',
             '( %s -> ( %s ` k ) = ( %s ` ( %s ` k ) ) )' % (Ak, CX1, U1, L1))
    x1 = w.s([w.s([lift(w, ub, Ak), w.s([kn], 'nnzd', '( %s -> k e. ZZ )' % Ak)], 'jca', '( %s -> ( %s e. ( Base ` ( DChr ` 1 ) ) /\\ k e. ZZ ) )' % (Ak, U1)), w.inst('zc1x1')], 'syl',
             '( %s -> ( %s ` ( %s ` k ) ) = 1 )' % (Ak, U1, L1))
    return w.s([cv, x1], 'eqtrd', '( %s -> ( %s ` k ) = 1 )' % (Ak, CX1)), Ak


def gen_zetactr():
    w = W('zetactr', 'Centre bound for the zeta series: ` 1 / 2 <_ abs zeta ( Z ) ` on ` Re Z = 2 ` ( ~ dchrctr at the character mod ` 1 ` , ~ zc1x1 ).')
    A0 = '( Z e. CC /\\ ( Re ` Z ) = 2 )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    D = tsub(S['dchrctr'], {'N': '1', 'X': U1})
    da, dc = ante_of(D)
    dct = s([s([nx1, s([], 'id', '( Z e. CC /\\ ( Re ` Z ) = 2 )')], 'jca', da), w.inst('dchrctr')], 'syl', dc)
    cv, Ak = cx1val(w, A0, ub)
    t1 = w.s([cv], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( 1 x. ( k ^c -u Z ) ) )' % (Ak, CX1))
    kc = w.s([w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Ak)], 'nncnd', '( %s -> k e. CC )' % Ak), w.s([lift(w, s([], 'simpl', 'Z e. CC'), Ak)], 'negcld', '( %s -> -u Z e. CC )' % Ak)], 'cxpcld',
             '( %s -> ( k ^c -u Z ) e. CC )' % Ak)
    t2 = w.s([t1, w.s([kc], 'mullidd', '( %s -> ( 1 x. ( k ^c -u Z ) ) = ( k ^c -u Z ) )' % Ak)], 'eqtrd', '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( k ^c -u Z ) )' % (Ak, CX1))
    se = s([t2], 'sumeq2dv', 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) = sum_ k e. NN ( k ^c -u Z )' % CX1)
    ZZ_ = 'sum_ k e. NN ( k ^c -u Z )'
    CH = tsub(stmt('zl2chs'), {'N': '1', 'X': U1})
    cha, chc = ante_of(CH)
    z1 = s([s([], 'simpl', 'Z e. CC'), lin8(w, A0, [s([], 'simpr', '( Re ` Z ) = 2')], '1 < ( Re ` Z )', {'( Re ` Z )': s([s([], 'simpl', 'Z e. CC')], 'recld', '( Re ` Z ) e. RR')})], 'jca', '( Z e. CC /\\ 1 < ( Re ` Z ) )')
    chs = s([s([nx1, z1], 'jca', cha), w.inst('zl2chs')], 'syl', chc)
    c1 = s([chs, w.inst('simpl')], 'syl', top_and(chc)[0])
    zcc = s([se, c1], 'eqeltrrd', '%s e. CC' % ZZ_)
    lb = s([dct, s([se], 'fveq2d', '( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) ) = ( abs ` %s )' % (CX1, ZZ_))], 'breqtrd', '( 1 / 2 ) <_ ( abs ` %s )' % ZZ_)
    w.qed([zcc, lb], 'jca', S['zetactr'])
    return run8(w)


def gen_etactr():
    w = W('etactr', 'Centre bound for the Abel-summed eta function: ` 1 / 4 <_ abs eta ( 2 + i T ) ` ( ~ etazser , ~ zetactr , ` abs ( 1 - 2 ^ ( 1 - s ) ) >_ 1 / 2 ` on ` Re s = 2 ` ).')
    A0 = 'T e. RR'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'id', 'T e. RR')
    import c9_h
    patch(c9_h)
    from c9_h import c0_facts
    c0, re0, im0 = c0_facts(w, A0, tr)
    ch = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)), ch], 'mpbird', '%s e. %s' % (C0, HP0))
    BODY = 'sum_ k e. NN ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) )'
    VAL = tsub(BODY, {'z': C0})
    vx = s([w.s([], 'sumex', '%s e. _V' % VAL)], 'a1i', '%s e. _V' % VAL)
    fv, val = _cg.mptval(w, A0, 'z', HP0, BODY, C0, c0h, exs=vx, gen=w.g)
    g1 = s([lin8(w, A0, [], '1 < 2', {}), re0], 'breqtrrd', '1 < ( Re ` %s )' % C0)
    z1 = s([c0, g1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (C0, C0))
    ez, ezc = isyl(w, A0, 'etazser', {'Z': C0}, z1)
    G = '( 1 - ( 2 ^c ( 1 - %s ) ) )' % C0
    ZS_ = 'sum_ k e. NN ( k ^c -u %s )' % C0
    zre = s([c0, re0], 'jca', '( %s e. CC /\\ ( Re ` %s ) = 2 )' % (C0, C0))
    zc, _ = isyl(w, A0, 'zetactr', {'Z': C0}, zre)
    # abs ( 2 ^c ( 1 - C0 ) ) = 1 / 2
    D1 = '( %s - 1 )' % C0
    d1c = s([c0, s([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % D1)
    rd1 = s([c0, s([], '1cnd', '1 e. CC')], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` 1 ) )' % (D1, C0))
    re1 = s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( Re ` 1 ) = 1')
    rv1 = s([s([rd1, s([re0, re1], 'oveq12d', '( ( Re ` %s ) - ( Re ` 1 ) ) = ( 2 - 1 )' % C0)], 'eqtrd', '( Re ` %s ) = ( 2 - 1 )' % D1),
             s([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')], 'eqtrd', '( Re ` %s ) = 1' % D1)
    ng = s([c0, s([], '1cnd', '1 e. CC')], 'negsubdi2d', '-u %s = ( 1 - %s )' % (D1, C0))
    rng = s([d1c, w.inst('reneg')], 'syl', '( Re ` -u %s ) = -u ( Re ` %s )' % (D1, D1))
    rr = s([s([s([ng], 'fveq2d', '( Re ` -u %s ) = ( Re ` ( 1 - %s ) )' % (D1, C0)), rng], 'eqtr3d', '( Re ` ( 1 - %s ) ) = -u ( Re ` %s )' % (C0, D1)),
            s([rv1], 'negeqd', '-u ( Re ` %s ) = -u 1' % D1)], 'eqtrd', '( Re ` ( 1 - %s ) ) = -u 1' % C0)
    omc = s([s([], '1cnd', '1 e. CC'), c0], 'subcld', '( 1 - %s ) e. CC' % C0)
    two = numst(w, A0, '2', 'RR+')
    ac = s([s([two, omc], 'jca', '( 2 e. RR+ /\\ ( 1 - %s ) e. CC )' % C0), w.inst('abscxp')], 'syl', '( abs ` ( 2 ^c ( 1 - %s ) ) ) = ( 2 ^c ( Re ` ( 1 - %s ) ) )' % (C0, C0))
    ac2 = s([ac, s([rr], 'oveq2d', '( 2 ^c ( Re ` ( 1 - %s ) ) ) = ( 2 ^c -u 1 )' % C0)], 'eqtrd', '( abs ` ( 2 ^c ( 1 - %s ) ) ) = ( 2 ^c -u 1 )' % C0)
    cn = s([s([s([], '2cnd', '2 e. CC'), s([], '2ne0', '2 =/= 0') if False else s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0'), s([], '1cnd', '1 e. CC')], '3jca', '( 2 e. CC /\\ 2 =/= 0 /\\ 1 e. CC )'),
            w.inst('cxpneg')], 'syl', '( 2 ^c -u 1 ) = ( 1 / ( 2 ^c 1 ) )')
    c1 = s([s([s([], '2cnd', '2 e. CC'), w.inst('cxp1')], 'syl', '( 2 ^c 1 ) = 2')], 'oveq2d', '( 1 / ( 2 ^c 1 ) ) = ( 1 / 2 )')
    half = s([ac2, s([cn, c1], 'eqtrd', '( 2 ^c -u 1 ) = ( 1 / 2 )')], 'eqtrd', '( abs ` ( 2 ^c ( 1 - %s ) ) ) = ( 1 / 2 )' % C0)
    pc = s([s([], '2cnd', '2 e. CC'), omc], 'cxpcld', '( 2 ^c ( 1 - %s ) ) e. CC' % C0)
    ad = s([s([], '1cnd', '1 e. CC'), pc], 'abs2difd', '( ( abs ` 1 ) - ( abs ` ( 2 ^c ( 1 - %s ) ) ) ) <_ ( abs ` %s )' % (C0, G))
    gc = s([s([], '1cnd', '1 e. CC'), pc], 'subcld', '%s e. CC' % G)
    AG, AZ, AP = '( abs ` %s )' % G, '( abs ` %s )' % ZS_, '( abs ` ( 2 ^c ( 1 - %s ) ) )' % C0
    zsc = s([zc, w.inst('simpl')], 'syl', '%s e. CC' % ZS_)
    zlb = s([zc, w.inst('simpr')], 'syl', '( 1 / 2 ) <_ %s' % AZ)
    a1 = s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')
    ad1 = s([s([a1, half], 'oveq12d', '( ( abs ` 1 ) - %s ) = ( 1 - ( 1 / 2 ) )' % AP), ad], 'eqbrtrrd', '( 1 - ( 1 / 2 ) ) <_ %s' % AG)
    agr = s([gc], 'abscld', '%s e. RR' % AG); azr = s([zsc], 'abscld', '%s e. RR' % AZ)
    lvh = {AG: agr, AZ: azr}
    hint = s([s([agr, numst(w, A0, '( 1 / 2 )', 'RR')], 'resubcld', '( %s - ( 1 / 2 ) ) e. RR' % AG), s([azr, numst(w, A0, '( 1 / 2 )', 'RR')], 'resubcld', '( %s - ( 1 / 2 ) ) e. RR' % AZ),
              lin8(w, A0, [ad1], '0 <_ ( %s - ( 1 / 2 ) )' % AG, lvh), lin8(w, A0, [zlb], '0 <_ ( %s - ( 1 / 2 ) )' % AZ, lvh)], 'mulge0d',
             '0 <_ ( ( %s - ( 1 / 2 ) ) x. ( %s - ( 1 / 2 ) ) )' % (AG, AZ))
    import cl as _cl
    c = _cl.Closure(w, A0, lvh)
    for k_ in lvh:
        c.atom(k_)
    PR = '( %s x. %s )' % (AG, AZ)
    fin = lin.linarith(w, A0, [hint, ad1, zlb], '( 1 / 4 ) <_ %s' % PR, closure=c, products=True)
    ae = s([s([s([fv, ez], 'eqtrd', '( %s ` %s ) = ( %s x. %s )' % (ETA, C0, G, ZS_))], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` ( %s x. %s ) )' % (ETA, C0, G, ZS_)),
            s([gc, zsc], 'absmuld', '( abs ` ( %s x. %s ) ) = %s' % (G, ZS_, PR))], 'eqtrd', '( abs ` ( %s ` %s ) ) = %s' % (ETA, C0, PR))
    w.qed([fin, ae], 'breqtrrd', S['etactr'])
    return run8(w)


if __name__ == '__main__':
    gen_dchrctr()
    gen_ectr()
    gen_zc1x1()
    gen_zetactr()
    gen_etactr()
