"""Sortie EF4: band mass (ef4bm: Lean band_mass_le), cuts (ef4cut: exists_cuts)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out, unit_t, const_ibl


def gen_bm():
    w = W('ef4bm', 'Lean ` band_mass_le ` : zeros with ` 1 / 2 <_ Re <_ 3 / 2 ` and ` T < abs Im <_ T + 1 ` lie in the two squares about ` 2 +- i ( T + 1 / 2 ) ` , so their mass is at most ` 1600 log ( A ( T + 4 ) ) ` (Lean ` 224 ` ; ~ ef2zss ).')
    A0, G = ante_of(S['ef4bm'])
    c = Ctx(w, A0)
    dd = c.g(DD()); tr = c.g('T e. RR'); t2 = c.g('2 <_ T'); gcc = c.g('G C_ CC')
    BANDP = BAND
    alp = c.g('A. p e. G %s' % BANDP)
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    CP, CM = '( T + ( 1 / 2 ) )', '( -u T - ( 1 / 2 ) )'
    cpr = c([tr, numst(w, A0, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % CP)
    cmr = c([c([tr], 'renegcld', '-u T e. RR'), numst(w, A0, '( 1 / 2 )', 'RR')], 'resubcld', '%s e. RR' % CM)
    ZP, ZM = ZS('F', CP), ZS('F', CM)
    def zsinfo(t, trs):
        f = tsub(stmt('ef2zs'), {'T': t})
        fa, fc = ante_of(f)
        st = c([c([dd, trs], 'jca', fa), w.inst('ef2zs')], 'syl', fc)
        parts = top_and(fc)
        return [c([st, w.inst(k)], 'syl', parts[i]) for i, k in enumerate(('simp1', 'simp2', 'simp3'))]
    zpf, zpo, _ = zsinfo(CP, cpr)
    zmf, zmo, _ = zsinfo(CM, cmr)
    # G C_ Z+ u. Z-
    Aa = '( %s /\\ a e. G )' % A0
    ca = Ctx(w, Aa)
    L = lambda st: lift(w, st, Aa)
    ag = ca([], 'simpr', 'a e. G')
    bb, BA = ral_at(w, Aa, L(alp), 'p', 'a', BANDP, ag)
    fz = ca([bb, w.inst('simpl')], 'syl', '( F ` a ) = 0')
    rest = ca([bb, w.inst('simpr')], 'syl', top_and(BA)[1])
    reb, imb = conj_split(w, Aa, rest)
    r1, r2 = conj_split(w, Aa, reb)
    i1, i2 = conj_split(w, Aa, imb)
    acc = ca([L(gcc), ag], 'sseldd', 'a e. CC')
    rer = ca([acc], 'recld', '( Re ` a ) e. RR'); imr = ca([acc], 'imcld', '( Im ` a ) e. RR')
    lv = {'( Re ` a )': rer, '( Im ` a )': imr, 'T': L(tr), '( abs ` ( Im ` a ) )': ca([ca([imr], 'recnd', '( Im ` a ) e. CC')], 'abscld', '( abs ` ( Im ` a ) ) e. RR')}
    U = '( %s u. %s )' % (ZP, ZM)
    # branch 0 <_ Im a
    Ap = '( %s /\\ 0 <_ ( Im ` a ) )' % Aa
    cp = Ctx(w, Ap)
    Lp = lambda st: lift(w, st, Ap)
    ap_ = cp([Lp(imr), cp([], 'simpr', '0 <_ ( Im ` a )')], 'absidd', '( abs ` ( Im ` a ) ) = ( Im ` a )')
    lvp = {k: Lp(v) for k, v in lv.items()}
    inp = zs_mem(w, Ap, 'F', CP, Lp(cpr), 'a', Lp(acc), [Lp(r1), Lp(r2), Lp(i1), Lp(i2), ap_, Lp(t2)], lvp, Lp(fz))
    up = cp([inp, w.inst('elun1')], 'syl', 'a e. %s' % U)
    # branch Im a < 0
    Am = '( %s /\\ ( Im ` a ) < 0 )' % Aa
    cm = Ctx(w, Am)
    Lm = lambda st: lift(w, st, Am)
    am_ = cm([Lm(imr), lin8(w, Am, [cm([], 'simpr', '( Im ` a ) < 0')], '( Im ` a ) <_ 0', {'( Im ` a )': Lm(imr)})],
             'absnidd', '( abs ` ( Im ` a ) ) = -u ( Im ` a )')
    lvm = {k: Lm(v) for k, v in lv.items()}
    inm = zs_mem(w, Am, 'F', CM, Lm(cmr), 'a', Lm(acc), [Lm(r1), Lm(r2), Lm(i1), Lm(i2), am_, Lm(t2)], lvm, Lm(fz))
    um = cm([inm, w.inst('elun2')], 'syl', 'a e. %s' % U)
    tri = ca([ca([numst(w, Aa, '0', 'RR'), imr], 'jca', '( 0 e. RR /\\ ( Im ` a ) e. RR )'), w.inst('lelttric')], 'syl', '( 0 <_ ( Im ` a ) \\/ ( Im ` a ) < 0 )')
    au = ca([up, um, tri], 'mpjaodan', 'a e. %s' % U)
    gu = c([w.s([au], 'ex', '( %s -> ( a e. G -> a e. %s ) )' % (A0, U))], 'ssrdv', 'G C_ %s' % U)
    gd = c([gu, c.a1(w.s([], 'ssundif', '( G C_ %s <-> ( G \\ %s ) C_ %s )' % (U, ZP, ZM)), '( G C_ %s <-> ( G \\ %s ) C_ %s )' % (U, ZP, ZM))], 'mpbid', '( G \\ %s ) C_ %s' % (ZP, ZM))
    uf = c([c([zpf, zmf], 'jca', '( %s e. Fin /\\ %s e. Fin )' % (ZP, ZM)), w.inst('unfi')], 'syl', '%s e. Fin' % U)
    gf = c([uf, gu], 'ssfid', 'G e. Fin')
    # orders in NN on G
    Aq = '( %s /\\ q e. G )' % A0
    cq = Ctx(w, Aq)
    qu = cq([lift(w, gu, Aq), cq([], 'simpr', 'q e. G')], 'sseldd', 'q e. %s' % U)
    op_ = cq([lift(w, zpo, Aq), w.inst('rsp')], 'syl', '( q e. %s -> ( F holord q ) e. NN )' % ZP)
    om_ = cq([lift(w, zmo, Aq), w.inst('rsp')], 'syl', '( q e. %s -> ( F holord q ) e. NN )' % ZM)
    qo = cq([cq([op_, om_], 'jaod', '( ( q e. %s \\/ q e. %s ) -> ( F holord q ) e. NN )' % (ZP, ZM)), cq([qu, cq.a1(w.s([], 'elun', '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (U, ZP, ZM)), '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (U, ZP, ZM))], 'mpbid', '( q e. %s \\/ q e. %s )' % (ZP, ZM))],
            'mpd', '( F holord q ) e. NN')
    qcc = cq([qo], 'nncnd', '( F holord q ) e. CC')
    GI, GD = '( G i^i %s )' % ZP, '( G \\ %s )' % ZP
    d0 = c.a1(w.s([], 'inindif', '( %s i^i %s ) = (/)' % (GI, GD)), '( %s i^i %s ) = (/)' % (GI, GD))
    u0 = c.a1(w.s([w.s([], 'inundif', '( %s u. %s ) = G' % (GI, GD))], 'eqcomi', 'G = ( %s u. %s )' % (GI, GD)), 'G = ( %s u. %s )' % (GI, GD))
    sp = c([d0, u0, gf, qcc], 'fsumsplit', '%s = ( %s + %s )' % (MASS('G', 'F'), MASS(GI, 'F'), MASS(GD, 'F')))
    def mass(Gs, t, trs, sub):
        f = tsub(stmt('ef2zss'), {'T': t, 'G': Gs})
        fa, fc = ante_of(f)
        return c([c([c([dd, trs], 'jca', top_and(fa)[0]), sub], 'jca', fa), w.inst('ef2zss')], 'syl', fc)
    mp = mass(GI, CP, cpr, c.a1(w.s([], 'inss2', '%s C_ %s' % (GI, ZP)), '%s C_ %s' % (GI, ZP)))
    mm_ = mass(GD, CM, cmr, gd)
    # log XA(c+-) <_ LT4
    xp = XA(CP); xm = XA(CM)
    ap = c([cpr, lin8(w, A0, [t2], '0 <_ %s' % CP, {'T': tr})], 'absidd', '( abs ` %s ) = %s' % (CP, CP))
    am2 = c([cmr, lin8(w, A0, [t2], '%s <_ 0' % CM, {'T': tr})], 'absnidd', '( abs ` %s ) = -u %s' % (CM, CM))
    T4 = '( A x. ( T + 4 ) )'
    ap0 = lin8(w, A0, [a1], '0 < A', {'A': ar})
    arp = c([ar, ap0], 'elrpd', 'A e. RR+')
    t4p = c([arp, c([c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 4 )', {'T': tr})], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '%s e. RR+' % T4)
    def lg(xx, ab):
        t_ = CP if xx == xp else CM
        AB = '( ( abs ` %s ) + 2 )' % t_
        abr = c([c([c([cpr if t_ == CP else cmr], 'recnd', '%s e. CC' % t_)], 'abscld', '( abs ` %s ) e. RR' % t_), numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % AB)
        abp = c([abr, lin8(w, A0, [ab, t2], '0 < %s' % AB, {'T': tr, '( abs ` %s )' % t_: c([c([cpr if t_ == CP else cmr], 'recnd', '%s e. CC' % t_)], 'abscld', '( abs ` %s ) e. RR' % t_)})], 'elrpd', '%s e. RR+' % AB)
        xxp = c([arp, abp], 'rpmulcld', '%s e. RR+' % xx)
        le = c([abr, c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), ar, lin8(w, A0, [a1], '0 <_ A', {'A': ar}),
                lin8(w, A0, [ab], '%s <_ ( T + 4 )' % AB, {'T': tr, '( abs ` %s )' % t_: c([c([cpr if t_ == CP else cmr], 'recnd', '%s e. CC' % t_)], 'abscld', '( abs ` %s ) e. RR' % t_)})], 'lemul2ad', '%s <_ %s' % (xx, T4))
        return c([le, c([xxp, t4p, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (xx, T4, xx, T4))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (xx, T4))
    lp_ = lg(xp, ap)
    lm_ = lg(xm, am2)
    def mr(Gs, sub):
        fin = c([gf, sub], 'ssfid', '%s e. Fin' % Gs)
        Aq2 = '( %s /\\ q e. %s )' % (A0, Gs)
        q2 = Ctx(w, Aq2)
        qg = q2([q2.a1(w.s([], 'inss1' if 'i^i' in Gs else 'difss', '%s C_ G' % Gs), '%s C_ G' % Gs), q2([], 'simpr', 'q e. %s' % Gs)], 'sseldd', 'q e. G')
        return fsre(w, A0, Gs, fin, sublift(w, A0, Gs, qg, qo))
    mpr = mr(GI, c.a1(w.s([], 'inss1', '%s C_ G' % GI), '%s C_ G' % GI))
    mmr = mr(GD, c.a1(w.s([], 'difss', '%s C_ G' % GD), '%s C_ G' % GD))
    lxp = c([c([arp, c([c([c([c([cpr], 'recnd', '%s e. CC' % CP)], 'abscld', '( abs ` %s ) e. RR' % CP), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % CP), lin8(w, A0, [ap, t2], '0 < ( ( abs ` %s ) + 2 )' % CP, {'T': tr, '( abs ` %s )' % CP: c([c([cpr], 'recnd', '%s e. CC' % CP)], 'abscld', '( abs ` %s ) e. RR' % CP)})], 'elrpd', '( ( abs ` %s ) + 2 ) e. RR+' % CP)], 'rpmulcld', '%s e. RR+' % xp)], 'relogcld', '( log ` %s ) e. RR' % xp)
    lxm = c([c([arp, c([c([c([c([cmr], 'recnd', '%s e. CC' % CM)], 'abscld', '( abs ` %s ) e. RR' % CM), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % CM), lin8(w, A0, [am2, t2], '0 < ( ( abs ` %s ) + 2 )' % CM, {'T': tr, '( abs ` %s )' % CM: c([c([cmr], 'recnd', '%s e. CC' % CM)], 'abscld', '( abs ` %s ) e. RR' % CM)})], 'elrpd', '( ( abs ` %s ) + 2 ) e. RR+' % CM)], 'rpmulcld', '%s e. RR+' % xm)], 'relogcld', '( log ` %s ) e. RR' % xm)
    l4 = c([t4p], 'relogcld', '( log ` %s ) e. RR' % T4)
    fin = lin8(w, A0, [sp, mp, mm_, lp_, lm_], G, {MASS(GI, 'F'): mpr, MASS(GD, 'F'): mmr, MASS('G', 'F'): c([sp, c([mpr, mmr], 'readdcld', '( %s + %s ) e. RR' % (MASS(GI, 'F'), MASS(GD, 'F')))], 'eqeltrd', '%s e. RR' % MASS('G', 'F')),
                                                   '( log ` %s )' % xp: lxp, '( log ` %s )' % xm: lxm, '( log ` %s )' % T4: l4})
    w.qed([fin], 'idi', S['ef4bm'])
    return run8(w)



def gen_cut():
    w = W('ef4cut', 'Lean ` exists_cuts ` : strictly increasing heights from ` P ` to ` Q ` with gaps at most 1 whose interior values avoid a finite set ` B ` ( ` m = ceil ( 2 ( Q - P ) ) ` equal steps ` d ` , interior cuts shifted by one ` u d ` , ` u ` off the fractional parts ` ( b - P ) / d mod 1 ` by ~ gappt ).')
    A0, G = ante_of(S['ef4cut'])
    c = Ctx(w, A0)
    bf = c.g('B e. Fin'); bre = c.g('B C_ RR'); pr = c.g('P e. RR'); qr = c.g('Q e. RR'); l1 = c.g('1 <_ ( Q - P )')
    L_ = '( Q - P )'
    lr = c([qr, pr], 'resubcld', '%s e. RR' % L_)
    TL = '( 2 x. %s )' % L_
    tlr = c([numst(w, A0, '2', 'RR'), lr], 'remulcld', '%s e. RR' % TL)
    M_ = '( |^ ` %s )' % TL
    mz = c([tlr, w.inst('ceilcl')], 'syl', '%s e. ZZ' % M_)
    mr = c([mz], 'zred', '%s e. RR' % M_)
    mge = c([tlr, w.inst('ceilge')], 'syl', '%s <_ %s' % (TL, M_))
    lvm = {'P': pr, 'Q': qr, M_: mr}
    m2 = lin8(w, A0, [mge, l1], '2 <_ %s' % M_, lvm)
    m0 = lin8(w, A0, [m2], '0 < %s' % M_, lvm)
    mn = c([c([mz, m0], 'jca', '( %s e. ZZ /\\ 0 < %s )' % (M_, M_)), c.a1(w.s([], 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (M_, M_, M_)), '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (M_, M_, M_))], 'mpbird', '%s e. NN' % M_)
    mp = c([mr, m0], 'elrpd', '%s e. RR+' % M_)
    D_ = '( %s / %s )' % (L_, M_)
    lp = c([lr, lin8(w, A0, [l1], '0 < %s' % L_, {'P': pr, 'Q': qr})], 'elrpd', '%s e. RR+' % L_)
    dp = c([lp, mp], 'rpdivcld', '%s e. RR+' % D_)
    dr = c([dp], 'rpred', '%s e. RR' % D_)
    md = c([c([lr], 'recnd', '%s e. CC' % L_), c([mr], 'recnd', '%s e. CC' % M_), c([mp], 'rpne0d', '%s =/= 0' % M_)], 'divcan2d', '( %s x. %s ) = %s' % (M_, D_, L_))
    dh = c([lin8(w, A0, [mge], '%s <_ ( %s x. ( 1 / 2 ) )' % (L_, M_), {'P': pr, 'Q': qr, M_: mr}), c([lr, numst(w, A0, '( 1 / 2 )', 'RR'), mp], 'ledivmuld', '( %s <_ ( 1 / 2 ) <-> %s <_ ( %s x. ( 1 / 2 ) ) )' % (D_, L_, M_))], 'mpbird', '%s <_ ( 1 / 2 )' % D_)
    # the finite set of fractional parts
    XB = lambda b: '( ( %s - P ) / %s )' % (b, D_)
    FR = lambda b: '( %s - ( |_ ` %s ) )' % (XB(b), XB(b))
    MPF = '( b e. B |-> %s )' % FR('b')
    E_ = '( ran %s u. { 0 , 1 } )' % MPF
    Ab = '( %s /\\ b e. B )' % A0
    cbb = Ctx(w, Ab)
    brr = cbb([lift(w, bre, Ab), cbb([], 'simpr', 'b e. B')], 'sseldd', 'b e. RR')
    xbr = cbb([cbb([brr, lift(w, pr, Ab)], 'resubcld', '( b - P ) e. RR'), lift(w, dp, Ab)], 'rerpdivcld', '%s e. RR' % XB('b'))
    frr = cbb([xbr, cbb([cbb([xbr, w.inst('flcl')], 'syl', '( |_ ` %s ) e. ZZ' % XB('b'))], 'zred', '( |_ ` %s ) e. RR' % XB('b'))], 'resubcld', '%s e. RR' % FR('b'))
    fm = c([frr, w.s([], 'eqid', '%s = %s' % (MPF, MPF))], 'fmptd', '%s : B --> RR' % MPF)
    ern = c([c([fm], 'frnd', 'ran %s C_ RR' % MPF), c.a1(w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR')], 'pm3.2i', '( 0 e. RR /\\ 1 e. RR )'), w.inst('prssi')], 'ax-mp', '{ 0 , 1 } C_ RR'), '{ 0 , 1 } C_ RR')],
            'unssd', '%s C_ RR' % E_)
    efin = c([c([c([c([bf, w.inst('mptfi')], 'syl', '%s e. Fin' % MPF), w.inst('rnfi')], 'syl', 'ran %s e. Fin' % MPF), c.a1(w.s([], 'prfi', '{ 0 , 1 } e. Fin'), '{ 0 , 1 } e. Fin')], 'jca', '( ran %s e. Fin /\\ { 0 , 1 } e. Fin )' % MPF), w.inst('unfi')], 'syl', '%s e. Fin' % E_)
    GAPE = '( 1 / ( 2 x. ( ( # ` %s ) + 1 ) ) )' % E_
    GP = tsub(stmt('gappt'), {'G': E_, 'T': '0'})
    gpa, gpc = ante_of(GP)
    gp = c([c([c([efin, ern], 'jca', top_and(gpa)[0]), numst(w, A0, '0', 'RR')], 'jca', gpa), w.inst('gappt')], 'syl', gpc)
    GB = '%s <_ ( abs ` ( t - g ) )' % GAPE
    cbg, GBC = cbvral(w, E_, 'g', 'c', GB)
    RX = 'E. t e. ( 0 [,] ( 0 + 1 ) ) A. c e. %s %s' % (E_, GBC)
    rb = w.s([cbg], 'rexbii', '( %s <-> %s )' % (gpc, RX))
    gp2 = c([gp, c.a1(rb, '( %s <-> %s )' % (gpc, RX))], 'mpbid', RX)
    # inside: t and the gap
    A1 = '( ( %s /\\ t e. ( 0 [,] ( 0 + 1 ) ) ) /\\ A. c e. %s %s )' % (A0, E_, GBC)
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tin = c1([w.s([], 'simpr', '( ( %s /\\ t e. ( 0 [,] ( 0 + 1 ) ) ) -> t e. ( 0 [,] ( 0 + 1 ) ) )' % A0)], 'adantr', 't e. ( 0 [,] ( 0 + 1 ) )')
    tr, t0, t1_ = icc_out(c1, 't', '0', '( 0 + 1 )', tin, numst(w, A1, '0', 'RR'), c1([numst(w, A1, '0', 'RR'), numst(w, A1, '1', 'RR')], 'readdcld', '( 0 + 1 ) e. RR'))
    alc = c1([], 'simpr', 'A. c e. %s %s' % (E_, GBC))
    hn = c1([L1(efin), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % E_)
    hr = c1([hn], 'nn0red', '( # ` %s ) e. RR' % E_)
    gpos = c1([c1([numst(w, A1, '1', 'RR+'), c1([numst(w, A1, '2', 'RR+'), c1([c1([hr, numst(w, A1, '1', 'RR')], 'readdcld', '( ( # ` %s ) + 1 ) e. RR' % E_),
                                                                              lin8(w, A1, [c1([hn], 'nn0ge0d', '0 <_ ( # ` %s )' % E_)], '0 < ( ( # ` %s ) + 1 )' % E_, {'( # ` %s )' % E_: hr})], 'elrpd', '( ( # ` %s ) + 1 ) e. RR+' % E_)],
                                             'rpmulcld', '( 2 x. ( ( # ` %s ) + 1 ) ) e. RR+' % E_)], 'rpdivcld', '%s e. RR+' % GAPE)], 'rpgt0d', '0 < %s' % GAPE)

    def tne(e, ein):
        """( A -> t =/= e ) for ein : ( A -> e e. E_ )"""
        A = ante_of([l for l in w.lines if l.startswith(ein + ':')][0].split(' |- ', 1)[1])[0]
        cc = Ctx(w, A)
        gb, _ = ral_at(w, A, lift(w, alc, A), 'c', e, GBC, ein)
        er = cc([lift(w, ern, A), ein], 'sseldd', '%s e. RR' % e)
        trA = lift(w, tr, A)
        tcc, ecc = cc([trA], 'recnd', 't e. CC'), cc([er], 'recnd', '%s e. CC' % e)
        dr_ = cc([tcc, ecc], 'subcld', '( t - %s ) e. CC' % e)
        pos = lin8(w, A, [lift(w, gpos, A), gb], '0 < ( abs ` ( t - %s ) )' % e,
                   {GAPE: lift(w, gap_re(c1, E_, hr, hn), A), '( abs ` ( t - %s ) )' % e: cc([dr_], 'abscld', '( abs ` ( t - %s ) ) e. RR' % e)})
        an0 = cc([pos], 'gt0ne0d', '( abs ` ( t - %s ) ) =/= 0' % e)
        e0 = cc([dr_, w.inst('abs00')], 'syl', '( ( abs ` ( t - %s ) ) = 0 <-> ( t - %s ) = 0 )' % (e, e))
        sn0 = cc([an0, cc([e0], 'necon3bid', '( ( abs ` ( t - %s ) ) =/= 0 <-> ( t - %s ) =/= 0 )' % (e, e))], 'mpbid', '( t - %s ) =/= 0' % e)
        e1 = cc([tcc, ecc, w.inst('subeq0')], 'syl2anc', '( ( t - %s ) = 0 <-> t = %s )' % (e, e))
        return cc([sn0, cc([e1], 'necon3bid', '( ( t - %s ) =/= 0 <-> t =/= %s )' % (e, e))], 'mpbid', 't =/= %s' % e)
    PR01 = '{ 0 , 1 }'
    z_in = c1.a1(w.s([w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }'), w.inst('elun2')], 'ax-mp', '0 e. %s' % E_), '0 e. %s' % E_)
    o_in = c1.a1(w.s([w.s([w.s([], '1ex', '1 e. _V')], 'prid2', '1 e. { 0 , 1 }'), w.inst('elun2')], 'ax-mp', '1 e. %s' % E_), '1 e. %s' % E_)
    tn0 = tne('0', z_in)
    tn1 = tne('1', o_in)
    tp0 = c1([c1([t0, tn0], 'jca', '( 0 <_ t /\\ t =/= 0 )'), c1([numst(w, A1, '0', 'RR'), tr], 'ltlend', '( 0 < t <-> ( 0 <_ t /\\ t =/= 0 ) )')], 'mpbird', '0 < t')
    t1le = lin8(w, A1, [t1_], 't <_ 1', {'t': tr})
    tl1 = c1([c1([t1le, c1([tn1], 'necomd', '1 =/= t')], 'jca', '( t <_ 1 /\\ 1 =/= t )'), c1([tr, numst(w, A1, '1', 'RR')], 'ltlend', '( t < 1 <-> ( t <_ 1 /\\ 1 =/= t ) )')], 'mpbird', 't < 1')
    # the cut function
    H = lambda x: 'if ( %s = 0 , 0 , if ( %s = %s , %s , ( ( %s - 1 ) + t ) ) )' % (x, x, M_, M_, x)
    GBx = lambda x: '( P + ( %s x. %s ) )' % (H(x), D_)
    G_ = '( a e. ( 0 ... %s ) |-> %s )' % (M_, GBx('a'))
    FZ = '( 0 ... %s )' % M_

    def hv(cc, x, case, s1=None, s2=None):
        """H(x) evaluated: case '0' (s1: x = 0), 'M' (s1: x =/= 0, s2: x = M_), 'I' (s1: x =/= 0, s2: x =/= M_)"""
        inner = 'if ( %s = %s , %s , ( ( %s - 1 ) + t ) )' % (x, M_, M_, x)
        if case == '0':
            return cc([s1, w.inst('iftrue')], 'syl', '%s = 0' % H(x)), '0'
        e1 = cc([s1, w.inst('ifnefalse')], 'syl', '%s = %s' % (H(x), inner))
        if case == 'M':
            e2 = cc([s2, w.inst('iftrue')], 'syl', '%s = %s' % (inner, M_))
            return cc([e1, e2], 'eqtrd', '%s = %s' % (H(x), M_)), M_
        e2 = cc([s2, w.inst('ifnefalse')], 'syl', '%s = ( ( %s - 1 ) + t )' % (inner, x))
        return cc([e1, e2], 'eqtrd', '%s = ( ( %s - 1 ) + t )' % (H(x), x)), '( ( %s - 1 ) + t )' % x

    def hre(cc, x, xz):
        """( A -> H(x) e. RR ) from xz : ( A -> x e. ZZ )"""
        A = cc.A
        tA = lift(w, tr, A)
        v = cc([cc([cc([xz], 'zred', '%s e. RR' % x), numst(w, A, '1', 'RR')], 'resubcld', '( %s - 1 ) e. RR' % x), tA], 'readdcld', '( ( %s - 1 ) + t ) e. RR' % x)
        inner = cc([lift(w, mr, A), v], 'ifcld', 'if ( %s = %s , %s , ( ( %s - 1 ) + t ) ) e. RR' % (x, M_, M_, x))
        return cc([numst(w, A, '0', 'RR'), inner], 'ifcld', '%s e. RR' % H(x))

    def gval(cc, x, xin):
        st, val = _cg.mptval(w, cc.A, 'a', FZ, GBx('a'), x, xin, gen=w.g)
        return st
    mn0 = c1([L1(mn)], 'nnnn0d', '%s e. NN0' % M_)
    # (a) G_ : FZ --> RR
    Aa = '( %s /\\ a e. %s )' % (A1, FZ)
    ca = Ctx(w, Aa)
    az = ca([ca([], 'simpr', 'a e. %s' % FZ), w.inst('elfzelz')], 'syl', 'a e. ZZ')
    gbr = ca([lift(w, pr, Aa), ca([hre(ca, 'a', az), lift(w, dr, Aa)], 'remulcld', '( %s x. %s ) e. RR' % (H('a'), D_))], 'readdcld', '%s e. RR' % GBx('a'))
    gf = c1([gbr, w.s([], 'eqid', '%s = %s' % (G_, G_))], 'fmptd', '%s : %s --> RR' % (G_, FZ))
    # (b) G_ ` 0 = P
    z0 = c1([mn0, w.inst('0elfz')], 'syl', '0 e. %s' % FZ)
    h0, _ = hv(c1, '0', '0', c1.a1(w.s([], 'eqid', '0 = 0'), '0 = 0'))
    g0 = c1([gval(c1, '0', z0), c1([c1([c1([h0], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (H('0'), D_, D_)), c1([c1([L1(dr)], 'recnd', '%s e. CC' % D_)], 'mul02d', '( 0 x. %s ) = 0' % D_)], 'eqtrd',
                                             '( %s x. %s ) = 0' % (H('0'), D_))], 'oveq2d', '%s = ( P + 0 )' % GBx('0'))], 'eqtrd', '( %s ` 0 ) = ( P + 0 )' % G_)
    g0 = c1([g0, c1([c1([L1(pr)], 'recnd', 'P e. CC')], 'addridd', '( P + 0 ) = P')], 'eqtrd', '( %s ` 0 ) = P' % G_)
    # (c) G_ ` M_ = Q
    mfz = c1([mn0, c1.a1(w.s([], 'nn0fz0', '( %s e. NN0 <-> %s e. %s )' % (M_, M_, FZ)), '( %s e. NN0 <-> %s e. %s )' % (M_, M_, FZ))], 'mpbid', '%s e. %s' % (M_, FZ))
    mne0 = c1([L1(m0)], 'gt0ne0d', '%s =/= 0' % M_)
    hm, _ = hv(c1, M_, 'M', mne0, c1.a1(w.s([], 'eqid', '%s = %s' % (M_, M_)), '%s = %s' % (M_, M_)))
    gm = c1([gval(c1, M_, mfz), c1([c1([c1([hm], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (H(M_), D_, M_, D_)), L1(md)], 'eqtrd', '( %s x. %s ) = %s' % (H(M_), D_, L_))], 'oveq2d', '%s = ( P + %s )' % (GBx(M_), L_))],
            'eqtrd', '( %s ` %s ) = ( P + %s )' % (G_, M_, L_))
    gm = c1([gm, c1([c1([L1(pr)], 'recnd', 'P e. CC'), c1([L1(qr)], 'recnd', 'Q e. CC')], 'pncan3d', '( P + %s ) = Q' % L_)], 'eqtrd', '( %s ` %s ) = Q' % (G_, M_))
    # (d) steps
    Aj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (A1, M_)
    cj = Ctx(w, Aj)
    jo = cj([], 'simpr', 'j e. ( 0 ..^ %s )' % M_)
    jz = cj([jo, w.inst('elfzoelz')], 'syl', 'j e. ZZ')
    jr = cj([jz], 'zred', 'j e. RR')
    j0 = cj([jo, w.inst('elfzole1')], 'syl', '0 <_ j')
    jm = cj([jo, w.inst('elfzolt2')], 'syl', 'j < %s' % M_)
    jf = cj([jo, w.inst('elfzofz')], 'syl', 'j e. %s' % FZ)
    j1f = cj([jo, w.inst('fzofzp1')], 'syl', '( j + 1 ) e. %s' % FZ)
    J1 = '( j + 1 )'
    j1z = cj([jz], 'peano2zd', '%s e. ZZ' % J1)
    DH = '( %s - %s )' % (H(J1), H('j'))
    KJ = '( 0 < %s /\\ %s <_ 2 )' % (DH, DH)
    hjr, hj1r = hre(cj, 'j', jz), hre(cj, J1, j1z)
    lvj = {'j': jr, 't': lift(w, tr, Aj), M_: lift(w, mr, Aj), H('j'): hjr, H(J1): hj1r}

    def kcase(A, eqs):
        return Ctx(w, A)([lin8(w, A, eqs + [lift(w, tp0, A), lift(w, tl1, A)], '0 < %s' % DH, {k: lift(w, v, A) for k, v in lvj.items()}),
                          lin8(w, A, eqs + [lift(w, tp0, A), lift(w, tl1, A)], '%s <_ 2' % DH, {k: lift(w, v, A) for k, v in lvj.items()})], 'jca', KJ)
    Ja = '( %s /\\ j = 0 )' % Aj
    ja = Ctx(w, Ja)
    jeq = ja([], 'simpr', 'j = 0')
    ha, _ = hv(ja, 'j', '0', jeq)
    j1p = lin8(w, Ja, [jeq], '0 < %s' % J1, {'j': lift(w, jr, Ja)})
    j1lt = lin8(w, Ja, [jeq, lift(w, L1(m2), Ja)], '%s < %s' % (J1, M_), {'j': lift(w, jr, Ja), M_: lift(w, L1(mr), Ja)})
    hb, _ = hv(ja, J1, 'I', ja([j1p], 'gt0ne0d', '%s =/= 0' % J1), ja([ja([lift(w, jz, Ja)], 'peano2zd', '%s e. ZZ' % J1) and ja([ja([lift(w, jz, Ja)], 'peano2zd', '%s e. ZZ' % J1)], 'zred', '%s e. RR' % J1), j1lt], 'ltned', '%s =/= %s' % (J1, M_)))
    ka = kcase(Ja, [ha, hb, jeq])
    Jb = '( %s /\\ j =/= 0 )' % Aj
    jb = Ctx(w, Jb)
    jne = jb([], 'simpr', 'j =/= 0')
    jnm = jb([lift(w, jr, Jb), lift(w, jm, Jb)], 'ltned', 'j =/= %s' % M_)
    hjb, _ = hv(jb, 'j', 'I', jne, jnm)
    j1n0 = jb([lin8(w, Jb, [lift(w, j0, Jb)], '0 < %s' % J1, {'j': lift(w, jr, Jb)})], 'gt0ne0d', '%s =/= 0' % J1)
    Jc = '( %s /\\ %s = %s )' % (Jb, J1, M_)
    jc = Ctx(w, Jc)
    hc, _ = hv(jc, J1, 'M', lift(w, j1n0, Jc), jc([], 'simpr', '%s = %s' % (J1, M_)))
    kc = kcase(Jc, [lift(w, hjb, Jc), hc, jc([], 'simpr', '%s = %s' % (J1, M_))])
    Jd = '( %s /\\ %s =/= %s )' % (Jb, J1, M_)
    jd = Ctx(w, Jd)
    hd, _ = hv(jd, J1, 'I', lift(w, j1n0, Jd), jd([], 'simpr', '%s =/= %s' % (J1, M_)))
    kd = kcase(Jd, [lift(w, hjb, Jd), hd])
    kb = jb([kc, kd, jb.a1(w.s([], 'exmidne', '( %s = %s \\/ %s =/= %s )' % (J1, M_, J1, M_)), '( %s = %s \\/ %s =/= %s )' % (J1, M_, J1, M_))], 'mpjaodan', KJ)
    kk = cj([ka, kb, cj.a1(w.s([], 'exmidne', '( j = 0 \\/ j =/= 0 )'), '( j = 0 \\/ j =/= 0 )')], 'mpjaodan', KJ)
    dh0 = cj([kk, w.inst('simpl')], 'syl', '0 < %s' % DH)
    dh2 = cj([kk, w.inst('simpr')], 'syl', '%s <_ 2' % DH)
    dhr = cj([hj1r, hjr], 'resubcld', '%s e. RR' % DH)
    drj = lift(w, dr, Aj)
    pdp = cj([dhr, drj, dh0, lift(w, c1([L1(dp)], 'rpgt0d', '0 < %s' % D_), Aj)], 'mulgt0d', '0 < ( %s x. %s )' % (DH, D_))
    pd2 = cj([dhr, numst(w, Aj, '2', 'RR'), drj, lift(w, c1([L1(dp)], 'rpge0d', '0 <_ %s' % D_), Aj), dh2], 'lemul1ad', '( %s x. %s ) <_ ( 2 x. %s )' % (DH, D_, D_))
    gj, gj1 = gval(cj, 'j', jf), gval(cj, J1, j1f)
    GJ, GJ1 = '( %s ` j )' % G_, '( %s ` %s )' % (G_, J1)
    gjr = cj([cj([lift(w, gf, Aj), jf], 'ffvelcdmd', '%s e. RR' % GJ)], 'idi', '%s e. RR' % GJ)
    gj1r = cj([lift(w, gf, Aj), j1f], 'ffvelcdmd', '%s e. RR' % GJ1)
    cl = Closure(w, Aj, {'P': ('RR', lift(w, pr, Aj)), D_: ('RR', drj), H('j'): ('RR', hjr), H(J1): ('RR', hj1r)})
    for k in ('P', D_, H('j'), H(J1)):
        cl.atom(k)
    ed = cj([cj([gj1, gj], 'oveq12d', '( %s - %s ) = ( %s - %s )' % (GJ1, GJ, GBx(J1), GBx('j'))), ringeq(w, Aj, '( %s - %s )' % (GBx(J1), GBx('j')), '( %s x. %s )' % (DH, D_), cl)], 'eqtrd',
            '( %s - %s ) = ( %s x. %s )' % (GJ1, GJ, DH, D_))
    PDD = '( %s x. %s )' % (DH, D_)
    lvg = {GJ: gjr, GJ1: gj1r, PDD: cj([dhr, drj], 'remulcld', '%s e. RR' % PDD), D_: drj}
    s1 = lin8(w, Aj, [ed, pdp], '%s < %s' % (GJ, GJ1), lvg)
    s2 = lin8(w, Aj, [ed, pd2, lift(w, dh, Aj)], '( %s - %s ) <_ 1' % (GJ1, GJ), lvg)
    STEP = '( %s < %s /\\ ( %s - %s ) <_ 1 )' % (GJ, GJ1, GJ1, GJ)
    alj = c1([cj([s1, s2], 'jca', STEP)], 'ralrimiva', 'A. j e. ( 0 ..^ %s ) %s' % (M_, STEP))
    # (e) interior cuts avoid B
    Ai = '( %s /\\ j e. ( 1 ..^ %s ) )' % (A1, M_)
    ci = Ctx(w, Ai)
    jo1 = ci([], 'simpr', 'j e. ( 1 ..^ %s )' % M_)
    jzi = ci([jo1, w.inst('elfzoelz')], 'syl', 'j e. ZZ')
    jri = ci([jzi], 'zred', 'j e. RR')
    j1i = ci([jo1, w.inst('elfzole1')], 'syl', '1 <_ j')
    jmi = ci([jo1, w.inst('elfzolt2')], 'syl', 'j < %s' % M_)
    jfi = ci([ci.a1(w.s([], 'fz1ssfz0', '( 1 ... %s ) C_ %s' % (M_, FZ)), '( 1 ... %s ) C_ %s' % (M_, FZ)), ci([jo1, w.inst('elfzofz')], 'syl', 'j e. ( 1 ... %s )' % M_)], 'sseldd', 'j e. %s' % FZ)
    hi, _ = hv(ci, 'j', 'I', ci([lin8(w, Ai, [j1i], '0 < j', {'j': jri})], 'gt0ne0d', 'j =/= 0'), ci([jri, jmi], 'ltned', 'j =/= %s' % M_))
    HI_ = '( ( j - 1 ) + t )'
    gi = ci([gval(ci, 'j', jfi), ci([ci([hi], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (H('j'), D_, HI_, D_))], 'oveq2d', '%s = ( P + ( %s x. %s ) )' % (GBx('j'), HI_, D_))], 'eqtrd', '%s = ( P + ( %s x. %s ) )' % (GJ, HI_, D_))
    hir = ci([ci([jri, numst(w, Ai, '1', 'RR')], 'resubcld', '( j - 1 ) e. RR'), lift(w, tr, Ai)], 'readdcld', '%s e. RR' % HI_)
    gpm = ci([ci([gi], 'oveq1d', '( %s - P ) = ( ( P + ( %s x. %s ) ) - P )' % (GJ, HI_, D_)), ci([ci([lift(w, pr, Ai)], 'recnd', 'P e. CC'), ci([ci([hir, lift(w, dr, Ai)], 'remulcld', '( %s x. %s ) e. RR' % (HI_, D_))], 'recnd', '( %s x. %s ) e. CC' % (HI_, D_))], 'pncan2d', '( ( P + ( %s x. %s ) ) - P ) = ( %s x. %s )' % (HI_, D_, HI_, D_))], 'eqtrd',
             '( %s - P ) = ( %s x. %s )' % (GJ, HI_, D_))
    xq = ci([ci([gpm], 'oveq1d', '%s = ( ( %s x. %s ) / %s )' % (XB(GJ), HI_, D_, D_)), ci([ci([hir], 'recnd', '%s e. CC' % HI_), ci([lift(w, dr, Ai)], 'recnd', '%s e. CC' % D_), ci([lift(w, dp, Ai)], 'rpne0d', '%s =/= 0' % D_)], 'divcan4d', '( ( %s x. %s ) / %s ) = %s' % (HI_, D_, D_, HI_))], 'eqtrd', '%s = %s' % (XB(GJ), HI_))
    jm1z = ci([jzi, ci.a1(w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')], 'zsubcld', '( j - 1 ) e. ZZ')
    xr_ = ci([ci([xq], 'eqcomd', '%s = %s' % (HI_, XB(GJ))), hir], 'eqeltrrd', '%s e. RR' % XB(GJ))
    lvx = {XB(GJ): xr_, 'j': jri, 't': lift(w, tr, Ai)}
    fl1 = lin8(w, Ai, [xq, lift(w, t0, Ai)], '( j - 1 ) <_ %s' % XB(GJ), lvx)
    fl2 = lin8(w, Ai, [xq, lift(w, tl1, Ai)], '%s < ( ( j - 1 ) + 1 )' % XB(GJ), lvx)
    fle = ci([ci([fl1, fl2], 'jca', '( ( j - 1 ) <_ %s /\\ %s < ( ( j - 1 ) + 1 ) )' % (XB(GJ), XB(GJ))), ci([xr_, jm1z, w.inst('flbi')], 'syl2anc', '( ( |_ ` %s ) = ( j - 1 ) <-> ( ( j - 1 ) <_ %s /\\ %s < ( ( j - 1 ) + 1 ) ) )' % (XB(GJ), XB(GJ), XB(GJ)))],
             'mpbird', '( |_ ` %s ) = ( j - 1 )' % XB(GJ))
    lvx2 = dict(lvx, **{'( |_ ` %s )' % XB(GJ): ci([ci([xr_, w.inst('flcl')], 'syl', '( |_ ` %s ) e. ZZ' % XB(GJ))], 'zred', '( |_ ` %s ) e. RR' % XB(GJ))})
    clx = Closure(w, Ai, lvx2)
    for k in lvx2:
        clx.atom(k)
    frt = lin.lineq(w, Ai, FR(GJ), 't', hyps=[xq, fle], closure=clx)
    Ai3 = '( %s /\\ %s e. B )' % (Ai, GJ)
    c3 = Ctx(w, Ai3)
    gb3 = c3([], 'simpr', '%s e. B' % GJ)
    fv3, fvv = _cg.mptval(w, Ai3, 'b', 'B', FR('b'), GJ, gb3, gen=w.g)
    rn3 = c3([c3([lift(w, fm, Ai3), w.inst('ffn')], 'syl', '%s Fn B' % MPF), gb3, w.inst('fnfvelrn')], 'syl2anc', '( %s ` %s ) e. ran %s' % (MPF, GJ, MPF))
    fe3 = c3([c3([fv3, rn3], 'eqeltrrd', '%s e. ran %s' % (fvv, MPF)), w.inst('elun1')], 'syl', '%s e. %s' % (fvv, E_))
    tn3 = tne(fvv, fe3)
    ai = ci([ci([frt], 'eqcomd', 't = %s' % FR(GJ)) and w.s([ci([frt], 'eqcomd', 't = %s' % FR(GJ))], 'adantr', '( %s -> t = %s )' % (Ai3, FR(GJ))), c3([tn3], 'neneqd', '-. t = %s' % FR(GJ))], 'pm2.65da', '-. %s e. B' % GJ)
    ali = c1([ai], 'ralrimiva', 'A. j e. ( 1 ..^ %s ) -. %s e. B' % (M_, GJ))
    # (f) range
    Af = '( %s /\\ j e. %s )' % (A1, FZ)
    cf = Ctx(w, Af)
    jff = cf([], 'simpr', 'j e. %s' % FZ)
    jzf = cf([jff, w.inst('elfzelz')], 'syl', 'j e. ZZ')
    jrf = cf([jzf], 'zred', 'j e. RR')
    j0f = cf([jff, w.inst('elfzle1')], 'syl', '0 <_ j')
    jmf = cf([jff, w.inst('elfzle2')], 'syl', 'j <_ %s' % M_)
    hjf = hre(cf, 'j', jzf)
    RB_ = '( 0 <_ %s /\\ %s <_ %s )' % (H('j'), H('j'), M_)
    lvf = lambda A: {'j': lift(w, jrf, A), 't': lift(w, tr, A), M_: lift(w, L1(mr), A), H('j'): lift(w, hjf, A)}
    Fa = '( %s /\\ j = 0 )' % Af
    fa = Ctx(w, Fa)
    hfa, _ = hv(fa, 'j', '0', fa([], 'simpr', 'j = 0'))
    ra = fa([lin8(w, Fa, [hfa], '0 <_ %s' % H('j'), lvf(Fa)), lin8(w, Fa, [hfa, lift(w, L1(m0), Fa)], '%s <_ %s' % (H('j'), M_), lvf(Fa))], 'jca', RB_)
    Fb = '( %s /\\ j =/= 0 )' % Af
    fb = Ctx(w, Fb)
    Fc = '( %s /\\ j = %s )' % (Fb, M_)
    fc = Ctx(w, Fc)
    hfc, _ = hv(fc, 'j', 'M', lift(w, fb([], 'simpr', 'j =/= 0'), Fc), fc([], 'simpr', 'j = %s' % M_))
    rc = fc([lin8(w, Fc, [hfc, lift(w, L1(m0), Fc)], '0 <_ %s' % H('j'), lvf(Fc)), lin8(w, Fc, [hfc], '%s <_ %s' % (H('j'), M_), lvf(Fc))], 'jca', RB_)
    Fd = '( %s /\\ j =/= %s )' % (Fb, M_)
    fd = Ctx(w, Fd)
    jnz = lift(w, fb([], 'simpr', 'j =/= 0'), Fd)
    hfd, _ = hv(fd, 'j', 'I', jnz, fd([], 'simpr', 'j =/= %s' % M_))
    jpos = fd([fd([lift(w, j0f, Fd), jnz], 'jca', '( 0 <_ j /\\ j =/= 0 )'),
                fd([numst(w, Fd, '0', 'RR'), lift(w, jrf, Fd)], 'ltlend', '( 0 < j <-> ( 0 <_ j /\\ j =/= 0 ) )')], 'mpbird', '0 < j')
    jge1 = fd([jpos, fd([lift(w, jzf, Fd), w.inst('zgt0ge1')], 'syl', '( 0 < j <-> 1 <_ j )')], 'mpbid', '1 <_ j')
    rd = fd([lin8(w, Fd, [hfd, jge1, lift(w, t0, Fd)], '0 <_ %s' % H('j'), lvf(Fd)), lin8(w, Fd, [hfd, lift(w, jmf, Fd), lift(w, tl1, Fd)], '%s <_ %s' % (H('j'), M_), lvf(Fd))], 'jca', RB_)
    rb = fb([rc, rd, fb.a1(w.s([], 'exmidne', '( j = %s \\/ j =/= %s )' % (M_, M_)), '( j = %s \\/ j =/= %s )' % (M_, M_))], 'mpjaodan', RB_)
    rr_ = cf([ra, rb, cf.a1(w.s([], 'exmidne', '( j = 0 \\/ j =/= 0 )'), '( j = 0 \\/ j =/= 0 )')], 'mpjaodan', RB_)
    h0f = cf([rr_, w.inst('simpl')], 'syl', '0 <_ %s' % H('j'))
    hmf = cf([rr_, w.inst('simpr')], 'syl', '%s <_ %s' % (H('j'), M_))
    drf = lift(w, dr, Af)
    p0 = cf([hjf, drf, h0f, lift(w, c1([L1(dp)], 'rpge0d', '0 <_ %s' % D_), Af)], 'mulge0d', '0 <_ ( %s x. %s )' % (H('j'), D_))
    pm_ = cf([hjf, lift(w, L1(mr), Af), drf, lift(w, c1([L1(dp)], 'rpge0d', '0 <_ %s' % D_), Af), hmf], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (H('j'), D_, M_, D_))
    gf_ = gval(cf, 'j', jff)
    GJf = '( %s ` j )' % G_
    PHD = '( %s x. %s )' % (H('j'), D_)
    lvr = {GJf: cf([lift(w, gf, Af), jff], 'ffvelcdmd', '%s e. RR' % GJf), PHD: cf([hjf, drf], 'remulcld', '%s e. RR' % PHD), 'P': lift(w, pr, Af), 'Q': lift(w, qr, Af),
           '( %s x. %s )' % (M_, D_): cf([lift(w, L1(mr), Af), drf], 'remulcld', '( %s x. %s ) e. RR' % (M_, D_))}
    ge_ = lin8(w, Af, [gf_, p0], 'P <_ %s' % GJf, lvr)
    le_ = lin8(w, Af, [gf_, pm_, lift(w, L1(md), Af)], '%s <_ Q' % GJf, lvr)
    alf = c1([cf([ge_, le_], 'jca', '( P <_ %s /\\ %s <_ Q )' % (GJf, GJf))], 'ralrimiva', 'A. j e. %s ( P <_ %s /\\ %s <_ Q )' % (FZ, GJf, GJf))
    # assembly
    BODY = lambda m, g: ('( %s : ( 0 ... %s ) --> RR /\\ ( ( ( %s ` 0 ) = P /\\ ( %s ` %s ) = Q ) /\\ A. j e. ( 0 ..^ %s ) ( ( %s ` j ) < ( %s ` ( j + 1 ) ) /\\ ( ( %s ` ( j + 1 ) ) - ( %s ` j ) ) <_ 1 ) ) /\\ '
                         '( A. j e. ( 1 ..^ %s ) -. ( %s ` j ) e. B /\\ A. j e. ( 0 ... %s ) ( P <_ ( %s ` j ) /\\ ( %s ` j ) <_ Q ) ) )') % (g, m, g, g, m, m, g, g, g, g, m, g, m, g, g)
    bG = c1([gf, c1([c1([g0, gm], 'jca', '( ( %s ` 0 ) = P /\\ ( %s ` %s ) = Q )' % (G_, G_, M_)), alj], 'jca', top_and(BODY(M_, G_))[1]), c1([ali, alf], 'jca', top_and(BODY(M_, G_))[2])], '3jca', BODY(M_, G_))
    gex = c1.a1(w.s([w.s([], 'ovex', '%s e. _V' % FZ)], 'mptex', '%s e. _V' % G_), '%s e. _V' % G_)
    def body_eq(var, val, m0, g0, m1, g1):
        """closed ( var = val -> ( BODY(m0,g0) <-> BODY(m1,g1) ) )"""
        EQ = '%s = %s' % (var, val)
        idv = w.s([], 'id', '( %s -> %s )' % (EQ, EQ))
        b0, b1 = top_and(BODY(m0, g0)), top_and(BODY(m1, g1))
        if var == 'g':
            f1 = w.s([idv], 'feq1d', '( %s -> ( %s <-> %s ) )' % (EQ, b0[0], b1[0]))
        else:
            f1 = w.s([w.s([idv], 'oveq2d', '( %s -> ( 0 ... %s ) = ( 0 ... %s ) )' % (EQ, m0, m1))], 'feq2d', '( %s -> ( %s <-> %s ) )' % (EQ, b0[0], b1[0]))
        f2, _ = w.wcongr(b0[1], {var: val}, EQ, {var: idv})
        f3, _ = w.wcongr(b0[2], {var: val}, EQ, {var: idv})
        return w.s([f1, f2, f3], '3anbi123d', '( %s -> ( %s <-> %s ) )' % (EQ, BODY(m0, g0), BODY(m1, g1)))
    sg = body_eq('g', G_, M_, 'g', M_, G_)
    eg = c1([gex, bG, sg], 'spcedv', 'E. g %s' % BODY(M_, 'g'))
    sm = w.s([body_eq('m', M_, 'm', 'g', M_, 'g')], 'exbidv', '( m = %s -> ( E. g %s <-> E. g %s ) )' % (M_, BODY('m', 'g'), BODY(M_, 'g')))
    em = c1([L1(mn), eg, w.s([sm], 'rspcev', '( ( %s e. NN /\\ E. g %s ) -> %s )' % (M_, BODY(M_, 'g'), G))], 'syl2anc', G)
    r1 = w.s([em], 'ex', '( ( %s /\\ t e. ( 0 [,] ( 0 + 1 ) ) ) -> ( A. c e. %s %s -> %s ) )' % (A0, E_, GBC, G))
    r2 = c([r1], 'rexlimdva', '( %s -> %s )' % (RX, G))
    w.qed([gp2, r2], 'mpd', S['ef4cut'])
    return run8(w)


def gap_re(c1, E_, hr, hn):
    w = c1.w
    s1 = c1([hr, numst(w, c1.A, '1', 'RR')], 'readdcld', '( ( # ` %s ) + 1 ) e. RR' % E_)
    s2 = c1([numst(w, c1.A, '2', 'RR'), s1], 'remulcld', '( 2 x. ( ( # ` %s ) + 1 ) ) e. RR' % E_)
    ne = c1([lin8(w, c1.A, [c1([hn], 'nn0ge0d', '0 <_ ( # ` %s )' % E_)], '0 < ( 2 x. ( ( # ` %s ) + 1 ) )' % E_, {'( # ` %s )' % E_: hr})], 'gt0ne0d', '( 2 x. ( ( # ` %s ) + 1 ) ) =/= 0' % E_)
    return c1([numst(w, c1.A, '1', 'RR'), s2, ne], 'redivcld', '( 1 / ( 2 x. ( ( # ` %s ) + 1 ) ) ) e. RR' % E_)

def sublift(w, A0, Gs, qg, qo):
    """( ( A0 /\\ q e. Gs ) -> ( F holord q ) e. NN ) from qg : ( ( A0 /\\ q e. Gs ) -> q e. G ) and qo : ( ( A0 /\\ q e. G ) -> ... )"""
    Aq2 = '( %s /\\ q e. %s )' % (A0, Gs)
    ex = w.s([qo], 'ex', '( %s -> ( q e. G -> ( F holord q ) e. NN ) )' % A0)
    return w.s([qg, w.s([ex], 'adantr', '( %s -> ( q e. G -> ( F holord q ) e. NN ) )' % Aq2)], 'mpd', '( %s -> ( F holord q ) e. NN )' % Aq2)


def fsre(w, A0, Gs, fin, qn):
    Aq2 = '( %s /\\ q e. %s )' % (A0, Gs)
    qr = w.s([qn], 'nnred', '( %s -> ( F holord q ) e. RR )' % Aq2)
    return w.s([fin, qr], 'fsumrecl', '( %s -> %s e. RR )' % (A0, MASS(Gs, 'F')))


GENS = {'ef4bm': gen_bm, 'ef4cut': gen_cut}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
