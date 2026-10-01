"""Sortie EF56: a height at distance from the square zeros is good (ef6gg; inside Lean exists_good_height)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from cl import lift, Closure
import congr as _cg
from c8_o import numst
import lin
lin.FASTPATH = True
from ef2lib import zs_mem, zs_unpack, sq_data


def gen_gg():
    w = W('ef6gg', 'A height ` H e. [ K , K + 1 ] ` with ` abs H <_ T + 1 ` at distance ` >_ 1 / ( 4000 log ( A ( T + 4 ) ) ) ` from the ordinates of the zeros in the two ` 13 / 8 ` squares about ` 2 + i K ` and ` 2 + i ( K + 1 ) ` is good: ` F ( v + i H ) =/= 0 ` and ` abs ( F-prime / F ) ( v + i H ) <_ 21000000 log ^ 2 ( A ( T + 4 ) ) ` on ` v e. [ 1 / 2 , 3 ] ` ( ~ ef2ghc , ~ ef2lnd , ~ ef2ghs ; the second half of Lean ` exists_good_height ` ).')
    A00 = ante_of(S['ef6gg'])[0]
    GAPP = 'A. p e. %s ( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - ( Im ` p ) ) )' % (ZSK, GAP, LT4)
    GAPO = 'A. o e. %s ( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - ( Im ` o ) ) )' % (ZSK, GAP, LT4)
    A0 = A00.replace(GAPP, GAPO)
    c = Ctx(w, A0)
    dd = c.g(DD()); tr = c.g('T e. RR'); t2 = c.g('2 <_ T'); kr = c.g('K e. RR'); hin = c.g('H e. ( K [,] ( K + 1 ) )'); ht = c.g('( abs ` H ) <_ ( T + 1 )')
    GAPH = c.g(GAPO)
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    k1 = c([kr, numst(w, A0, '1', 'RR')], 'readdcld', '( K + 1 ) e. RR')
    e2 = c([kr, k1, w.inst('elicc2')], 'syl2anc', '( H e. ( K [,] ( K + 1 ) ) <-> ( H e. RR /\\ K <_ H /\\ H <_ ( K + 1 ) ) )')
    h3 = c([hin, e2], 'mpbid', '( H e. RR /\\ K <_ H /\\ H <_ ( K + 1 ) )')
    hr = c([h3, w.inst('simp1')], 'syl', 'H e. RR')
    L_ = LT4
    A4 = '( A x. ( T + 4 ) )'
    t4 = c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')
    a4r = c([ar, t4], 'remulcld', '%s e. RR' % A4)
    a4g = c([numst(w, A0, '1', 'RR'), ar, t4, lin8(w, A0, [t2], '0 <_ ( T + 4 )', {'T': tr}), a1], 'lemul1ad', '( 1 x. ( T + 4 ) ) <_ %s' % A4)
    six = lin8(w, A0, [a4g, t2], '6 <_ %s' % A4, {'T': tr, 'A': ar, A4: a4r})
    a4p = c([a4r, lin8(w, A0, [six], '0 < %s' % A4, {A4: a4r})], 'elrpd', '%s e. RR+' % A4)
    ere = c.a1(w.s([], 'epr', '_e e. RR+'), '_e e. RR+')
    e3 = c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')
    er_ = c([ere], 'rpred', '_e e. RR')
    ele = lin8(w, A0, [e3, six], '_e <_ %s' % A4, {'_e': er_, A4: a4r})
    lg1 = c([c.a1(w.s([], 'loge', '( log ` _e ) = 1'), '( log ` _e ) = 1'), c([ele, c([ere, a4p], 'logled', '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (A4, L_))], 'mpbid', '( log ` _e ) <_ %s' % L_)],
             'eqbrtrrd', '1 <_ %s' % L_)
    lr = c([a4p], 'relogcld', '%s e. RR' % L_)
    L4p = c([numst(w, A0, GAP, 'RR+'), c([lr, lin8(w, A0, [lg1], '0 < %s' % L_, {L_: lr})], 'elrpd', '%s e. RR+' % L_)], 'rpmulcld', '( %s x. %s ) e. RR+' % (GAP, L_))
    DL = '( 1 / ( %s x. %s ) )' % (GAP, L_)
    dlp = c([L4p], 'rpreccld', '%s e. RR+' % DL)
    dlr = c([dlp], 'rpred', '%s e. RR' % DL)
    IV = '( ( 1 / 2 ) [,] 3 )'
    SV = PTL('v', 'H')
    Av = '( %s /\\ v e. %s )' % (A0, IV)
    sv = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Av, f_))
    av = lambda st, f_: lift(w, st, Av)
    vi = sv([], 'simpr', 'v e. %s' % IV)
    h2 = numst(w, Av, '( 1 / 2 )', 'RR'); th = numst(w, Av, '3', 'RR')
    v3 = sv([vi, sv([h2, th, w.inst('elicc2')], 'syl2anc', '( v e. %s <-> ( v e. RR /\\ ( 1 / 2 ) <_ v /\\ v <_ 3 ) )' % IV)], 'mpbid', '( v e. RR /\\ ( 1 / 2 ) <_ v /\\ v <_ 3 )')
    vr = sv([v3, w.inst('simp1')], 'syl', 'v e. RR'); v1 = sv([v3, w.inst('simp2')], 'syl', '( 1 / 2 ) <_ v'); v2 = sv([v3, w.inst('simp3')], 'syl', 'v <_ 3')
    urv = av(hr, 'H e. RR')
    iu = sv([sv([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sv([urv], 'recnd', 'H e. CC')], 'mulcld', '( _i x. H ) e. CC')
    scc = sv([sv([vr], 'recnd', 'v e. CC'), iu], 'addcld', '%s e. CC' % SV)
    res = sv([vr, urv], 'crred', '( Re ` %s ) = v' % SV); ims = sv([vr, urv], 'crimd', '( Im ` %s ) = H' % SV)
    ddv = av(dd, DD()); holv = av(hol, HOLF('F', HP0))
    ZUu = ZS('F', 'H')
    Ap = '( %s /\\ p e. %s )' % (Av, ZUu)
    sp = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Ap, f_))
    GH = tsub(stmt('ef2ghc'), {'T': 'K', 'U': 'H', 'Q': 'p'})
    gha, ghc_ = ante_of(GH)
    pw = sp([sp([sp([lift(w, kr, Ap), lift(w, hin, Ap)], 'jca', '( K e. RR /\\ H e. ( K [,] ( K + 1 ) ) )'), sp([], 'simpr', 'p e. %s' % ZUu)], 'jca', gha), w.inst('ef2ghc')], 'syl', ghc_)
    BODY = '%s <_ ( abs ` ( H - ( Im ` p ) ) )' % DL
    gp = sp([lift(w, GAPH, Ap), pw], 'rspcdva' if False else 'x', 'x') if False else None
    gp, _ = ral_at(w, Ap, lift(w, GAPH, Ap), 'o', 'p', '( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - ( Im ` o ) ) )' % (GAP, LT4), pw)
    GZ = 'A. p e. %s %s' % (ZUu, BODY)
    gapz = w.s([gp], 'ralrimiva', '( %s -> %s )' % (Av, GZ))
    dlv = av(dlp, '%s e. RR+' % DL)
    # F ( v + i H ) =/= 0
    Az = '( %s /\\ ( F ` %s ) = 0 )' % (Av, SV)
    sz = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Az, f_))
    az = lambda st, f_: lift(w, st, Az)
    lvz = {'v': az(vr, 'v e. RR'), 'H': az(urv, 'H e. RR')}
    sin = zs_mem(w, Az, 'F', 'H', lvz['H'], SV, az(scc, '%s e. CC' % SV), [az(res, '( Re ` %s ) = v' % SV), az(ims, '( Im ` %s ) = H' % SV), az(v1, '( 1 / 2 ) <_ v'), az(v2, 'v <_ 3')],
                 lvz, sz([], 'simpr', '( F ` %s ) = 0' % SV))
    subp = w.s([w.s([w.s([w.s([], 'fveq2', '( p = %s -> ( Im ` p ) = ( Im ` %s ) )' % (SV, SV))], 'oveq2d', '( p = %s -> ( H - ( Im ` p ) ) = ( H - ( Im ` %s ) ) )' % (SV, SV))],
                      'fveq2d', '( p = %s -> ( abs ` ( H - ( Im ` p ) ) ) = ( abs ` ( H - ( Im ` %s ) ) ) )' % (SV, SV))], 'breq2d',
               '( p = %s -> ( %s <_ ( abs ` ( H - ( Im ` p ) ) ) <-> %s <_ ( abs ` ( H - ( Im ` %s ) ) ) ) )' % (SV, DL, DL, SV))
    gz = sz([subp, az(gapz, GZ), sin], 'rspcdva', '%s <_ ( abs ` ( H - ( Im ` %s ) ) )' % (DL, SV))
    e0 = sz([sz([sz([az(ims, '( Im ` %s ) = H' % SV)], 'oveq2d', '( H - ( Im ` %s ) ) = ( H - H )' % SV), sz([sz([lvz['H']], 'recnd', 'H e. CC')], 'subidd', '( H - H ) = 0')], 'eqtrd',
                 '( H - ( Im ` %s ) ) = 0' % SV)], 'fveq2d', '( abs ` ( H - ( Im ` %s ) ) ) = ( abs ` 0 )' % SV)
    e1 = sz([e0, sz([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` ( H - ( Im ` %s ) ) ) = 0' % SV)
    dz = sz([gz, e1], 'breqtrd', '%s <_ 0' % DL)
    dlz = az(dlr, '%s e. RR' % DL)
    ndz = sz([sz([az(dlp, '%s e. RR+' % DL)], 'rpgt0d', '0 < %s' % DL), sz([numst(w, Az, '0', 'RR'), dlz], 'ltnled', '( 0 < %s <-> -. %s <_ 0 )' % (DL, DL))], 'mpbid', '-. %s <_ 0' % DL)
    fne = sv([sv([dz, ndz], 'pm2.65da', '-. ( F ` %s ) = 0' % SV)], 'neqned', '( F ` %s ) =/= 0' % SV)
    # the Landau expansion at 2 + i H
    pn = sv([sv([vr], 'recnd', 'v e. CC'), numst(w, Av, '2', 'CC'), iu, w.inst('pnpcan2')], 'syl3anc', '( %s - %s ) = ( v - 2 )' % (SV, CT('H')))
    tw = numst(w, Av, '2', 'RR'); th2 = numst(w, Av, '( 3 / 2 )', 'RR')
    ad2 = sv([sv([vr, tw, th2], 'absdifled', '( ( abs ` ( v - 2 ) ) <_ ( 3 / 2 ) <-> ( ( 2 - ( 3 / 2 ) ) <_ v /\\ v <_ ( 2 + ( 3 / 2 ) ) ) )'),
              sv([lin8(w, Av, [v1], '( 2 - ( 3 / 2 ) ) <_ v', {'v': vr}), lin8(w, Av, [v2], 'v <_ ( 2 + ( 3 / 2 ) )', {'v': vr})], 'jca', '( ( 2 - ( 3 / 2 ) ) <_ v /\\ v <_ ( 2 + ( 3 / 2 ) ) )')],
             'mpbird', '( abs ` ( v - 2 ) ) <_ ( 3 / 2 )')
    ad3 = sv([sv([pn], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( v - 2 ) )' % (SV, CT('H'))), ad2], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 3 / 2 )' % (SV, CT('H')))
    ddu = sv([ddv, urv], 'jca', '( %s /\\ H e. RR )' % DD())
    LN = tsub(stmt('ef2lnd'), {'T': 'H', 'S': SV})
    lna, lnc = ante_of(LN)
    lnd = sv([sv([ddu, sv([scc, ad3, fne], '3jca', top_and(lna)[1])], 'jca', lna), w.inst('ef2lnd')], 'syl', lnc)
    GS = tsub(stmt('ef2ghs'), {'U': 'H', 'V': 'v', 'E': DL})
    gsa, gsc = ante_of(GS)
    ghs = sv([sv([ddu, sv([vr, dlv, gapz], '3jca', top_and(gsa)[1])], 'jca', gsa), w.inst('ef2ghs')], 'syl', gsc)
    hpv = sv([sv([numst(w, Av, '0', 'RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (SV, HP0, SV, SV)),
              sv([scc, sv([lin8(w, Av, [v1], '0 < v', {'v': vr}), res], 'breqtrrd', '0 < ( Re ` %s )' % SV)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (SV, SV))], 'mpbird', '%s e. %s' % (SV, HP0))
    fsc = fcc(w, Av, holv, 'F', HP0, SV, hpv)
    dfc = sv([sv([holv, w.inst('holf')], 'syl', '( CC _D F ) : %s --> CC' % HP0), hpv], 'ffvelcdmd', '( ( CC _D F ) ` %s ) e. CC' % SV)
    Q = '( ( ( CC _D F ) ` %s ) / ( F ` %s ) )' % (SV, SV)
    qc = sv([dfc, fsc, fne], 'divcld', '%s e. CC' % Q)
    zc = tsub(ante_of(stmt('ef2zs'))[1], {'T': 'H'})
    zs = sv([ddu, w.inst('ef2zs')], 'syl', zc)
    zfin = sv([zs, w.inst('simp1')], 'syl', top_and(zc)[0]); zall = sv([zs, w.inst('simp2')], 'syl', top_and(zc)[1])
    Aq = '( %s /\\ q e. %s )' % (Av, ZUu)
    sq_ = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Aq, f_))
    aq = lambda st, f_: lift(w, st, Aq)
    d = zs_unpack(w, Aq, 'F', 'H', aq(urv, 'H e. RR'), 'q', sq_([], 'simpr', 'q e. %s' % ZUu))
    ne1 = sq_([aq(fne, '( F ` %s ) =/= 0' % SV), d['fz']], 'neeqtrrd', '( F ` %s ) =/= ( F ` q )' % SV)
    ne2 = sq_([sq_([w.s([], 'fveq2', '( %s = q -> ( F ` %s ) = ( F ` q ) )' % (SV, SV))], 'a1i', '( %s = q -> ( F ` %s ) = ( F ` q ) )' % (SV, SV))], 'necon3d',
              '( ( F ` %s ) =/= ( F ` q ) -> %s =/= q )' % (SV, SV))
    sqn = sq_([ne1, ne2], 'mpd', '%s =/= q' % SV)
    dn = sq_([aq(scc, '%s e. CC' % SV), d['cc'], sqn], 'subne0d', '( %s - q ) =/= 0' % SV)
    mc = sq_([w.s([zall], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)], 'nncnd', '( F holord q ) e. CC')
    tc = sq_([mc, sq_([aq(scc, '%s e. CC' % SV), d['cc']], 'subcld', '( %s - q ) e. CC' % SV), dn], 'divcld', '( ( F holord q ) / ( %s - q ) ) e. CC' % SV)
    P = 'sum_ q e. %s ( ( F holord q ) / ( %s - q ) )' % (ZUu, SV)
    pc = sv([zfin, tc], 'fsumcl', '%s e. CC' % P)
    tri = sv([qc, pc], 'abs2difd', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (Q, P, Q, P))
    # numbers: log XA ( H ) <_ L
    XU_ = XA('H')
    Lu = '( log ` %s )' % XU_
    aur = sv([sv([urv], 'recnd', 'H e. CC')], 'abscld', '( abs ` H ) e. RR')
    inner = '( ( abs ` H ) + 2 )'
    ir = sv([aur, numst(w, Av, '2', 'RR')], 'readdcld', '%s e. RR' % inner)
    arv = av(ar, 'A e. RR'); a1v = av(a1, '1 <_ A'); t4v = av(t4, '( T + 4 ) e. RR')
    a0le = sv([numst(w, Av, '0', 'RR'), numst(w, Av, '1', 'RR'), arv, lin8(w, Av, [], '0 <_ 1', {}), a1v], 'letrd', '0 <_ A')
    xle = sv([ir, t4v, arv, a0le, lin8(w, Av, [av(ht, '( abs ` H ) <_ ( T + 1 )')], '%s <_ ( T + 4 )' % inner, {'T': av(tr, 'T e. RR'), '( abs ` H )': aur})], 'lemul2ad', '%s <_ %s' % (XU_, A4))
    xr = sv([arv, ir], 'remulcld', '%s e. RR' % XU_)
    x2 = sv([ddu, w.inst('ef2x2')], 'syl', '2 <_ %s' % XU_)
    xp = sv([xr, lin8(w, Av, [x2], '0 < %s' % XU_, {XU_: xr})], 'elrpd', '%s e. RR+' % XU_)
    lul = sv([xle, sv([xp, av(a4p, '%s e. RR+' % A4)], 'logled', '( %s <_ %s <-> %s <_ %s )' % (XU_, A4, Lu, L_))], 'mpbid', '%s <_ %s' % (Lu, L_))
    lur = sv([xp], 'relogcld', '%s e. RR' % Lu)
    lu0 = sv([xr, lin8(w, Av, [x2], '1 <_ %s' % XU_, {XU_: xr})], 'logge0d', '0 <_ %s' % Lu)
    lrv = av(lr, '%s e. RR' % L_); lg1v = av(lg1, '1 <_ %s' % L_)
    X8 = '( ; ; 8 0 0 x. %s )' % Lu
    x8r = sv([numst(w, Av, '; ; 8 0 0', 'RR'), lur], 'remulcld', '%s e. RR' % X8)
    DEN = '( %s x. %s )' % (GAP, L_)
    denp = av(L4p, '%s e. RR+' % DEN)
    q1 = sv([sv([x8r], 'recnd', '%s e. CC' % X8), sv([dlv], 'rpcnd', '%s e. CC' % DL), sv([dlv], 'rpne0d', '%s =/= 0' % DL)], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (X8, DL, X8, DL))
    q2 = sv([sv([sv([denp], 'rpcnd', '%s e. CC' % DEN), sv([denp], 'rpne0d', '%s =/= 0' % DEN)], 'recrecd', '( 1 / %s ) = %s' % (DL, DEN))], 'oveq2d', '( %s x. ( 1 / %s ) ) = ( %s x. %s )' % (X8, DL, X8, DEN))
    q3 = sv([q1, q2], 'eqtrd', '( %s / %s ) = ( %s x. %s )' % (X8, DL, X8, DEN))
    L8 = '( ; ; 8 0 0 x. %s )' % L_
    pr = sv([x8r, sv([numst(w, Av, '; ; 8 0 0', 'RR'), lrv], 'remulcld', '%s e. RR' % L8), sv([denp], 'rpred', '%s e. RR' % DEN), sv([denp], 'rpred', '%s e. RR' % DEN),
             lin8(w, Av, [lu0], '0 <_ %s' % X8, {Lu: lur}), sv([denp], 'rpge0d', '0 <_ %s' % DEN), lin8(w, Av, [lul], '%s <_ %s' % (X8, L8), {Lu: lur, L_: lrv}), sv([sv([denp], 'rpred', '%s e. RR' % DEN)], 'leidd', '%s <_ %s' % (DEN, DEN))],
            'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (X8, DEN, L8, DEN))
    l0 = sv([numst(w, Av, '0', 'RR'), numst(w, Av, '1', 'RR'), lrv, lin8(w, Av, [], '0 <_ 1', {}), lg1v], 'letrd', '0 <_ %s' % L_)
    lsq = sv([numst(w, Av, '1', 'RR'), lrv, lrv, l0, lg1v], 'lemul1ad', '( 1 x. %s ) <_ ( %s x. %s )' % (L_, L_, L_))
    sqv = sv([sv([lrv], 'recnd', '%s e. CC' % L_)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (L_, L_, L_))
    AQ, AP, AQP = '( abs ` %s )' % Q, '( abs ` %s )' % P, '( abs ` ( %s - %s ) )' % (Q, P)
    lvf = {AQ: sv([qc], 'abscld', '%s e. RR' % AQ), AP: sv([pc], 'abscld', '%s e. RR' % AP), AQP: sv([sv([qc, pc], 'subcld', '( %s - %s ) e. CC' % (Q, P))], 'abscld', '%s e. RR' % AQP),
           Lu: lur, L_: lrv, '( %s / %s )' % (X8, DL): sv([x8r, dlv], 'rerpdivcld', '( %s / %s ) e. RR' % (X8, DL)),
           '( %s x. %s )' % (X8, DEN): sv([x8r, sv([denp], 'rpred', '%s e. RR' % DEN)], 'remulcld', '( %s x. %s ) e. RR' % (X8, DEN))}
    fin_ = lin8(w, Av, [tri, lnd, ghs, q3, pr, lul, lg1v, lsq, sqv], '%s <_ ( %s x. ( %s ^ 2 ) )' % (AQ, KGH, L_), lvf, products=True)
    body = sv([fne, fin_], 'jca', GOOD(SV))
    fin = w.s([body], 'ralrimiva', '( %s -> A. v e. %s %s )' % (A0, IV, GOOD(SV)))
    cb, _ = cbvral(w, ZSK, 'p', 'o', '( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - ( Im ` p ) ) )' % (GAP, LT4))
    c0 = Ctx(w, A00)
    rb = rebuild(w, c0, A0, {GAPO: c0([c0.g(GAPP), c0.a1(cb, '( %s <-> %s )' % (GAPP, GAPO))], 'mpbid', GAPO)})
    w.qed([rb, fin], 'syl', S['ef6gg'])
    return run8(w)


GENS = {'ef6gg': gen_gg}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
