"""T2: the mover with a restricted internal-state class --- Lean's
`moveNum_loop'` / `moveNum_runs'` (blueprint 3.5, D3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t2_lib import hstepcp
from t2_c_mov import (constfty, rfun, updn, upd2cl, OPT, RATY, CTY, PTY, DG, GK, GJ, ST,
                      STMT_T, TL, NVF, GA, PU, UPD2)

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

BR = BRANCH('C', PU, 'Q')
STM = POP('K', 'F', BR)
HC = ('A. r e. N A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. N )'
      % (NVF('r', 'z'), NVF('r', 'z'), NVF('r', 'z')))
NSS = 'N C_ %s' % S('T')
LAB = '( A e. %s /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )' % (L('T'), DG, DG)
FTY = '( %s /\\ %s /\\ %s )' % (RATY, CTY, PTY)
WTY = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( R e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
       % (GK, GJ, GK, GJ, STK('T')))
QTY = '( Q e. %s /\\ ( %s /\\ %s ) )' % (STMT_T, NSS, HC)
PH1 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM, LAB, FTY, WTY, QTY))


def CLN(X, Y, lb='A'):
    return '( { ( inl ` %s ) } X. ( N X. { %s } ) )' % (lb, UPD2(X, Y))


def ctx(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH1, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1l', PHM)
    meq = g('simp1r', '( M ` A ) = %s' % STM)
    lab = g('simp2', LAB)
    p3 = g('simp3', '( %s /\\ %s /\\ %s )' % (FTY, WTY, QTY))
    al = w.s([lab, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    kj2 = w.s([lab, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s ) )' % (ph, DG, DG))
    kk = w.s([kj2], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([kj2], 'simprd', '( %s -> J e. %s )' % (ph, DG))
    ne = w.s([lab, w.inst('simp3')], 'syl', '( %s -> K =/= J )' % ph)
    nes = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    ra = w.s([ft, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([ft, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    pp = w.s([ft, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTY))
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ))
    bk = w.s([b2], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    bj = w.s([b2], 'simprd', '( %s -> B C_ %s )' % (ph, GJ))
    r2 = w.s([wt, w.inst('simp2')], 'syl', '( %s -> ( R e. Word %s /\\ H e. Word %s ) )' % (ph, GK, GJ))
    rw = w.s([r2], 'simpld', '( %s -> R e. Word %s )' % (ph, GK))
    hw = w.s([r2], 'simprd', '( %s -> H e. Word %s )' % (ph, GJ))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    qt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, QTY))
    qq = w.s([qt], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    nh = w.s([qt], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HC))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    hc = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HC))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, kk=kk, jj=jj, ne=ne, nes=nes, ra=ra, cc=cc, pp=pp,
                bk=bk, bj=bj, rw=rw, hw=hw, dd=dd, qq=qq, nss=nss, hc=hc, tv=tv)


def stmtty(w, ph, u):
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], jp, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    j = w.s([pu, u['qq']], 'jca', '( %s -> ( %s e. %s /\\ Q e. %s ) )' % (ph, PU, STMT_T, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR, STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STM, STMT_T))
    return dict(fa=fa, ga=ga, pu=pu, br=br, pop=po)


def hcitern(w, av, vv, ZT, zcl, hca):
    """HC at ( r := v , z := ZT ): branch taken, pushed letter is ZT, new state in N"""
    NV = NVF('v', ZT); NZ = NVF('v', 'z'); RZ = NVF('r', 'z')
    def trip(x, rhs):
        return '( ( C ` %s ) = 1o /\\ ( P ` %s ) = %s /\\ %s e. N )' % (x, x, rhs, x)
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (RZ, NZ))
    i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (RZ, NZ))
    i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (RZ, NZ))
    i5 = w.s([i2], 'fveq2d', '( r = v -> ( P ` %s ) = ( P ` %s ) )' % (RZ, NZ))
    i6 = w.s([i5], 'eqeq1d', '( r = v -> ( ( P ` %s ) = z <-> ( P ` %s ) = z ) )' % (RZ, NZ))
    i7 = w.s([i2], 'eleq1d', '( r = v -> ( %s e. N <-> %s e. N ) )' % (RZ, NZ))
    i8 = w.s([i4, i6, i7], '3anbi123d', '( r = v -> ( %s <-> %s ) )' % (trip(RZ, 'z'), trip(NZ, 'z')))
    i9 = w.s([i8], 'ralbidv', '( r = v -> ( A. z e. B %s <-> A. z e. B %s ) )' % (trip(RZ, 'z'), trip(NZ, 'z')))
    h1 = w.s([i9, hca, vv], 'rspcdva', '( %s -> A. z e. B %s )' % (av, trip(NZ, 'z')))
    j1 = w.s([], 'fveq2', '( z = %s -> ( inl ` z ) = ( inl ` %s ) )' % (ZT, ZT))
    j2 = w.s([j1], 'opeq2d', '( z = %s -> <. v , ( inl ` z ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    j3 = w.s([j2], 'fveq2d', '( z = %s -> %s = %s )' % (ZT, NZ, NV))
    j4 = w.s([j3], 'fveq2d', '( z = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NZ, NV))
    j5 = w.s([j4], 'eqeq1d', '( z = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (ZT, NZ, NV))
    jid = w.s([], 'id', '( z = %s -> z = %s )' % (ZT, ZT))
    j6 = w.s([j3], 'fveq2d', '( z = %s -> ( P ` %s ) = ( P ` %s ) )' % (ZT, NZ, NV))
    j7 = w.s([j6, jid], 'eqeq12d', '( z = %s -> ( ( P ` %s ) = z <-> ( P ` %s ) = %s ) )' % (ZT, NZ, NV, ZT))
    j8 = w.s([j3], 'eleq1d', '( z = %s -> ( %s e. N <-> %s e. N ) )' % (ZT, NZ, NV))
    j9 = w.s([j5, j7, j8], '3anbi123d', '( z = %s -> ( %s <-> %s ) )' % (ZT, trip(NZ, 'z'), trip(NV, ZT)))
    h2 = w.s([j9, h1, zcl], 'rspcdva', '( %s -> %s )' % (av, trip(NV, ZT)))
    bc = w.s([h2, w.inst('simp1')], 'syl', '( %s -> ( C ` %s ) = 1o )' % (av, NV))
    pv = w.s([h2, w.inst('simp2')], 'syl', '( %s -> ( P ` %s ) = %s )' % (av, NV, ZT))
    nv = w.s([h2, w.inst('simp3')], 'syl', '( %s -> %s e. N )' % (av, NV))
    return bc, pv, nv


def tm2fmvn1():
    lab = 'tm2fmvn1'
    ph = '( ( %s /\\ ( x e. Word B /\\ s e. Word B ) ) /\\ x =/= (/) )' % PH1
    XR = '( x ++ R )'; SH = '( s ++ H )'
    TXR = '( %s ++ R )' % TL('x'); X0 = '( x ` 0 )'
    ACC = '( ( <" %s "> ++ s ) ++ H )' % X0
    D1 = UPD2(XR, SH); D2 = UPD2(TXR, ACC)
    DK1 = UPD('T', 'D', 'K', XR); D2K = UPD('T', D1, 'K', TXR)
    NV = NVF('v', X0)
    w = W(lab, 'One iteration of the mover with the internal state confined to '
               'a class ` N ` closed under the pop handler: the registers and '
               'flags outside the read interface are untouched.  Lean: '
               '` moveNum_loop\' ` , the ` cons ` case.  Instantiating ` N ` at '
               '` ( 2nd ` T ) ` gives ~ tm2fmov1 ; instantiating it at '
               '` { r e. ( 2nd ` T ) | ( U ` r ) = X } ` says the field ` U ` '
               'survives the loop.')
    u = ctx(w, ph, 'ad2antrr')
    t = stmtty(w, ph, u)
    xw = w.s([], 'simplrl', '( %s -> x e. Word B )' % ph)
    sw = w.s([], 'simplrr', '( %s -> s e. Word B )' % ph)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ph)
    swk = w.s([u['bk'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GK))
    swj = w.s([u['bj'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GJ))
    xwg = w.s([swk, xw], 'sseldd', '( %s -> x e. Word %s )' % (ph, GK))
    swg = w.s([swj, sw], 'sseldd', '( %s -> s e. Word %s )' % (ph, GJ))
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ph, X0))
    x0k = w.s([u['bk'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GK))
    x0j = w.s([u['bj'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GJ))
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ph, TL('x')))
    tlwg = w.s([swk, tlw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, TL('x'), GK))
    xrw = w.s([xwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, XR, GK))
    txrw = w.s([tlwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, TXR, GK))
    shw = w.s([swg, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, SH, GJ))
    s1c = w.s([x0j], 's1cld', '( %s -> <" %s "> e. Word %s )' % (ph, X0, GJ))
    xsw = w.s([s1c, swg, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" %s "> ++ s ) e. Word %s )' % (ph, X0, GJ))
    accw = w.s([xsw, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ACC, GJ))
    xrn = w.s([xwg, xn, u['rw'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, XR))
    k1 = w.s([u['kk'], xrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, XR, GK))
    k2 = w.s([u['kk'], txrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, TXR, GK))
    dk1 = w.s([u['tv'], u['dd'], k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DK1, STK('T')))
    d1cl = upd2cl(w, ph, XR, SH, GK, GJ, u['tv'], u['dd'], u['kk'], u['jj'], xrw, shw)
    d2cl = upd2cl(w, ph, TXR, ACC, GK, GJ, u['tv'], u['dd'], u['kk'], u['jj'], txrw, accw)
    d2kcl = w.s([u['tv'], d1cl, k2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2K, STK('T')))
    rf = rfun(w, ph, u['ra'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = A_(u['nss'], NSS)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG)
        ne = A_(u['ne'], 'K =/= J'); nes = A_(u['nes'], 'J =/= K')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T')); qq = A_(u['qq'], 'Q e. %s' % STMT_T)
        hca = A_(u['hc'], HC); aa = A_(u['al'], 'A e. %s' % L('T'))
        fa = A_(t['fa'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        ga = A_(t['ga'], '%s e. %s' % (GA, STMT_T)); pu = A_(t['pu'], '%s e. %s' % (PU, STMT_T))
        br = A_(t['br'], '%s e. %s' % (BR, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        d2k = A_(d2kcl, '%s e. %s' % (D2K, STK('T'))); dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T')))
        xrwa = A_(xrw, '%s e. Word %s' % (XR, GK)); txrwa = A_(txrw, '%s e. Word %s' % (TXR, GK))
        shwa = A_(shw, '%s e. Word %s' % (SH, GJ)); accwa = A_(accw, '%s e. Word %s' % (ACC, GJ))
        xwga = A_(xwg, 'x e. Word %s' % GK); swga = A_(swg, 's e. Word %s' % GJ)
        rwa = A_(u['rw'], 'R e. Word %s' % GK); hwa = A_(u['hw'], 'H e. Word %s' % GJ)
        xna = A_(xn, 'x =/= (/)'); x0b = A_(x0, '%s e. B' % X0)
        x0ka = A_(x0k, '%s e. %s' % (X0, GK)); s1ca = A_(s1c, '<" %s "> e. Word %s' % (X0, GJ))
        xrna = A_(xrn, '%s =/= (/)' % XR)
        rff = A_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        a1 = updn(w, av, DK1, 'J', SH, 'Word %s' % GJ, 'K', tv, dk1a, jj, shwa, kk, ne)
        xrv = w.s([xrwa], 'elexd', '( %s -> %s e. _V )' % (av, XR))
        a2 = updkval(w, av, 'T', 'D', 'K', XR, tv, dd, kk, xrv)
        rk = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (av, D1, XR))
        b1 = updn(w, av, D1, 'K', TXR, 'Word %s' % GK, 'J', tv, d1, kk, txrwa, jj, nes)
        shv = w.s([shwa], 'elexd', '( %s -> %s e. _V )' % (av, SH))
        b2 = updkval(w, av, 'T', DK1, 'J', SH, tv, dk1a, jj, shv)
        rj = w.s([b1, b2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (av, D2K, SH))
        xnn = w.s([xrna], 'neneqd', '( %s -> -. %s = (/) )' % (av, XR))
        nnx = w.s([xwga, xna, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` x ) e. NN )' % av)
        xpos = w.s([nnx, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` x ) )' % av)
        rfv = w.s([xwga, rwa, xpos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = %s )' % (av, XR, X0))
        rtl = w.s([xwga, xna, rwa, w.inst('wrdtlcc')], 'syl3anc', '( %s -> %s = %s )' % (av, TL(XR), TXR))
        as1 = w.s([s1ca, swga, hwa, w.inst('ccatass')], 'syl3anc',
                  '( %s -> %s = ( <" %s "> ++ %s ) )' % (av, ACC, X0, SH))
        asc = w.s([as1], 'eqcomd', '( %s -> ( <" %s "> ++ %s ) = %s )' % (av, X0, SH, ACC))
        tdj = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T'))), ne],
                  'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (av, STK('T')))
        pk2 = w.s([kk, w.s([xrwa, txrwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                            % (av, XR, GK, TXR, GK))], 'jca',
                  '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (av, DG, XR, GK, TXR, GK))
        pj2 = w.s([jj, w.s([shwa, accwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                            % (av, SH, GJ, ACC, GJ))], 'jca',
                  '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (av, DG, SH, GJ, ACC, GJ))
        up4 = w.s([tdj, pk2, pj2, w.inst('tm2stkup4')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D2K, 'J', ACC), D2))
        bc, pv, nvn = hcitern(w, av, vn, X0, x0b, hca)
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        avv = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2K, STK('T')): d2k,
                 '%s e. %s' % (D2, STK('T')): d2, '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, RATY: ra, CTY: cc, PTY: pp,
                 '%s e. %s' % (BR, STMT_T): br, '%s e. %s' % (PU, STMT_T): pu,
                 '%s e. %s' % (GA, STMT_T): ga, 'Q e. %s' % STMT_T: qq,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): fa}
        rules = {'( %s ` K )' % D1: (XR, rk), '( %s ` J )' % D2K: (SH, rj),
                 '( %s ` 0 )' % XR: (X0, rfv), TL(XR): (TXR, rtl),
                 '( <" %s "> ++ %s )' % (X0, SH): (ACC, asc),
                 '( P ` %s )' % NV: (X0, pv),
                 UPD('T', D2K, 'J', ACC): (D2, up4),
                 '( %s ` %s )' % (CONSTF('T', 'A'), NV): ('A', rga)}
        ifr = {'%s = (/)' % XR: (False, xnn), '( C ` %s ) = 1o' % NV: (True, bc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , %s >.' % D1)
        want_res = '<. ( inl ` A ) , <. %s , %s >. >.' % (NV, D2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), D1, STM, SA('T'), D1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), D1, res))
        return fin, NV, nvn
    hstepcp(w, ph, 'T', 'M', 'A', 'A', 'N', D1, D2, (u['meq'], u['phm']), u['al'], u['al'],
            u['nss'], d1cl, d2cl, body, qed=True)
    return w.run()


JMVN = ('( p e. _V |-> ( { ( inl ` A ) } X. ( N X. { %s } ) ) )'
        % UPD2('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )'))


def clnex(w, ante, X, Y):
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    c = w.s([], 'snex', '{ %s } e. _V' % UPD2(X, Y))
    d = w.s([c], 'xpexg', '( N e. _V -> ( N X. { %s } ) e. _V )' % UPD2(X, Y))
    return a, c, d


def jmvn(w, ante, U, WW, ucl, wcl, nex):
    aq = '( %s /\\ p = <. %s , %s >. )' % (ante, U, WW)
    lp = w.s([], 'simpr', '( %s -> p = <. %s , %s >. )' % (aq, U, WW))
    body = ('( { ( inl ` A ) } X. ( N X. { %s } ) )'
            % UPD2('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )'))
    st, mid = W.congr(w, body, {'p': '<. %s , %s >.' % (U, WW)}, aq, {'p': lp})
    uv = w.s([ucl], 'elexd', '( %s -> %s e. _V )' % (ante, U))
    wv = w.s([wcl], 'elexd', '( %s -> %s e. _V )' % (ante, WW))
    uva = w.s([uv], 'adantr', '( %s -> %s e. _V )' % (aq, U))
    wva = w.s([wv], 'adantr', '( %s -> %s e. _V )' % (aq, WW))
    p1 = w.s([uva, wva, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (aq, U, WW, U))
    p2 = w.s([uva, wva, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (aq, U, WW, WW))
    ev, res = W.congr(w, mid, {}, aq, {},
                      rules={'( 1st ` <. %s , %s >. )' % (U, WW): (U, p1),
                             '( 2nd ` <. %s , %s >. )' % (U, WW): (WW, p2)})
    tgt = CLN('( %s ++ R )' % U, '( %s ++ H )' % WW)
    assert res == tgt, res
    h2 = w.s([st, ev], 'eqtrd', '( %s -> %s = %s )' % (aq, body, tgt))
    eqi = w.s([], 'eqid', '%s = %s' % (JMVN, JMVN))
    opv = w.s([], 'opex', '<. %s , %s >. e. _V' % (U, WW))
    opva = w.s([opv], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (ante, U, WW))
    sn1 = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    sn1a = w.s([sn1], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ante)
    sn2 = w.s([], 'snex', '{ %s } e. _V' % UPD2('( %s ++ R )' % U, '( %s ++ H )' % WW))
    sn2a = w.s([sn2], 'a1i', '( %s -> { %s } e. _V )' % (ante, UPD2('( %s ++ R )' % U, '( %s ++ H )' % WW)))
    xp1 = w.s([nex, sn2a, w.inst('xpexg')], 'syl2anc',
              '( %s -> ( N X. { %s } ) e. _V )' % (ante, UPD2('( %s ++ R )' % U, '( %s ++ H )' % WW)))
    cex = w.s([sn1a, xp1, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ante, tgt))
    return w.s([h2, eqi, opva, cex], 'fvmptd2',
               '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, JMVN, U, WW, tgt))


def tm2fmvnw():
    lab = 'tm2fmvnw'
    ph = '( %s /\\ ( W e. Word B /\\ U e. Word B ) )' % PH1
    phx = '( %s /\\ ( x e. Word B /\\ s e. Word B ) )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    X0 = '( x ` 0 )'
    ACCx = '( <" %s "> ++ s )' % X0
    HRx = HR('( %s ` <. x , s >. )' % JMVN, 'T', 'M',
             '( %s ` <. %s , %s >. )' % (JMVN, TL('x'), ACCx), '1')
    HYPJ = 'A. x e. Word B A. s e. Word B ( x =/= (/) -> %s )' % HRx
    ZCJ = 'A. s e. Word B ( %s ` <. (/) , s >. ) C_ %s' % (JMVN, CFG('T'))
    CLx = CLN('( x ++ R )', '( s ++ H )')
    CLt = CLN('( %s ++ R )' % TL('x'), '( %s ++ H )' % ACCx)
    w = W(lab, 'The scan loop of the mover with the internal state confined to '
               'a class ` N ` : Lean\'s ` moveNum_loop\' ` .  An instantiation '
               'of ~ tm2hwrd2 ; the state class is carried through the '
               'induction by the invariant, not by the rule.')
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ante2, PH1))
    xw1 = w.s([], 'simplrl', '( %s -> x e. Word B )' % ante2)
    sw1 = w.s([], 'simplrr', '( %s -> s e. Word B )' % ante2)
    xn1 = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    one = w.s([], 'tm2fmvn1', '( %s -> %s )' % (ante2, HR(CLx, 'T', 'M', CLt, '1')))
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    x01 = w.s([xw1, xn1, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ante2, X0))
    s1c1 = w.s([x01], 's1cld', '( %s -> <" %s "> e. Word B )' % (ante2, X0))
    acw1 = w.s([s1c1, sw1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ante2, ACCx))
    u2 = ctx(w, ante2, 'ad2antrr')
    sev2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    sev2a = w.s([sev2], 'a1i', '( %s -> %s e. _V )' % (ante2, S('T')))
    nex2 = w.s([u2['nss'], sev2a, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ante2)
    jx = jmvn(w, ante2, 'x', 's', xw1, sw1, nex2)
    jt = jmvn(w, ante2, TL('x'), ACCx, tlw1, acw1, nex2)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` <. %s , %s >. ) , 1 >. = <. %s , 1 >. )'
             % (ante2, JMVN, TL('x'), ACCx, CLt))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JMVN, TL('x'), ACCx), '1'),
                HR(CLx, 'T', 'M', CLt, '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JMVN, TL('x'), ACCx), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JMVN, TL('x'), ACCx), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    ex2 = w.s([ex1], 'anassrs', '( ( ( %s /\\ x e. Word B ) /\\ s e. Word B ) -> ( x =/= (/) -> %s ) )' % (PH1, HRx))
    ex3 = w.s([ex2], 'ralrimiva', '( ( %s /\\ x e. Word B ) -> A. s e. Word B ( x =/= (/) -> %s ) )' % (PH1, HRx))
    hyp = w.s([ex3], 'ralrimiva', '( %s -> %s )' % (PH1, HYPJ))
    hypa = w.s([hyp], 'adantr', '( %s -> %s )' % (ph, HYPJ))
    u = ctx(w, ph, 'adantr')
    ww = w.s([], 'simprl', '( %s -> W e. Word B )' % ph)
    uu = w.s([], 'simprr', '( %s -> U e. Word B )' % ph)
    phs = '( %s /\\ s e. Word B )' % ph
    def B_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (phs, f))
    tvs = B_(u['tv'], 'T e. V'); als = B_(u['al'], 'A e. %s' % L('T'))
    dds = B_(u['dd'], 'D e. %s' % STK('T')); kks = B_(u['kk'], 'K e. %s' % DG)
    jjs = B_(u['jj'], 'J e. %s' % DG); hws = B_(u['hw'], 'H e. Word %s' % GJ)
    rws = B_(u['rw'], 'R e. Word %s' % GK); bjs = B_(u['bj'], 'B C_ %s' % GJ)
    nsss = B_(u['nss'], NSS)
    sws2 = w.s([], 'simpr', '( %s -> s e. Word B )' % phs)
    sevs = w.s([], 'fvex', '%s e. _V' % S('T'))
    sevsa = w.s([sevs], 'a1i', '( %s -> %s e. _V )' % (phs, S('T')))
    nexs = w.s([nsss, sevsa, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % phs)
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0s = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % phs)
    jzs = jmvn(w, phs, '(/)', 's', w0s, sws2, nexs)
    swj = w.s([bjs, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (phs, GJ))
    swg = w.s([swj, sws2], 'sseldd', '( %s -> s e. Word %s )' % (phs, GJ))
    z0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. Word %s )' % (phs, GK))
    zrw = w.s([z0a, rws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( (/) ++ R ) e. Word %s )' % (phs, GK))
    shw = w.s([swg, hws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( s ++ H ) e. Word %s )' % (phs, GJ))
    ups = upd2cl(w, phs, '( (/) ++ R )', '( s ++ H )', GK, GJ, tvs, dds, kks, jjs, zrw, shw)
    UPS = UPD2('( (/) ++ R )', '( s ++ H )')
    sn = w.s([ups], 'snssd', '( %s -> { %s } C_ %s )' % (phs, UPS, STK('T')))
    xs = w.s([nsss, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( N X. { %s } ) C_ %s )' % (phs, UPS, ST))
    cls = w.s([tvs, als, xs, w.inst('tm2hcfgss')], 'syl3anc',
              '( %s -> %s C_ %s )' % (phs, CLN('( (/) ++ R )', '( s ++ H )'), CFG('T')))
    clj = w.s([jzs, cls], 'eqsstrd', '( %s -> ( %s ` <. (/) , s >. ) C_ %s )' % (phs, JMVN, CFG('T')))
    zc = w.s([clj], 'ralrimiva', '( %s -> %s )' % (ph, ZCJ))
    n1 = w.s([], '1nn0', '1 e. NN0')
    n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([n1a, zc], 'jca', '( %s -> ( 1 e. NN0 /\\ %s ) )' % (ph, ZCJ))
    ant = w.s([u['phm'], pj, hypa], '3jca', '( %s -> ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) )' % (ph, PHM, ZCJ, HYPJ))
    xy = w.s([ww, uu], 'jca', '( %s -> ( W e. Word B /\\ U e. Word B ) )' % ph)
    ant2 = w.s([ant, xy], 'jca',
               '( %s -> ( ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) /\\ ( W e. Word B /\\ U e. Word B ) ) )'
               % (ph, PHM, ZCJ, HYPJ))
    RV = '( ( reverse ` W ) ++ U )'
    run = w.s([ant2, w.inst('tm2hwrd2')], 'syl', '( %s -> %s )'
              % (ph, HR('( %s ` <. W , U >. )' % JMVN, 'T', 'M',
                        '( %s ` <. (/) , %s >. )' % (JMVN, RV), '( ( # ` W ) x. 1 )')))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    rvw = w.s([rvc, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, RV))
    w0b = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    sevp = w.s([], 'fvex', '%s e. _V' % S('T'))
    sevpa = w.s([sevp], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    nexp = w.s([u['nss'], sevpa, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ph)
    jw = jmvn(w, ph, 'W', 'U', ww, uu, nexp)
    jz = jmvn(w, ph, '(/)', RV, w0b, rvw, nexp)
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    TGT0 = CLN('( (/) ++ R )', '( %s ++ H )' % RV)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` <. (/) , %s >. ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JMVN, RV, TGT0))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JMVN, 'T', 'M',
                       '( %s ` <. (/) , %s >. )' % (JMVN, RV), '( ( # ` W ) x. 1 )'),
                HR('( %s ` <. W , U >. )' % JMVN, 'T', 'M', TGT0, '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` <. W , U >. )' % JMVN, 'T', 'M', TGT0, '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JMVN, 'T', 'M', TGT0, '( # ` W )'),
                HR(CLN('( W ++ R )', '( U ++ H )'), 'T', 'M', TGT0, '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )'
          % (ph, HR(CLN('( W ++ R )', '( U ++ H )'), 'T', 'M', TGT0, '( # ` W )')))
    return w.run()


GE = GOTO(CONSTF('T', 'E'))
BR0 = BRANCH('C', PU, GE)
STM0 = POP('K', 'F', BR0)
RY = '( <" Y "> ++ X )'
HE = 'A. r e. N ( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NVF('r', 'Y'), NVF('r', 'Y'))
LAB0 = '( ( A e. %s /\\ E e. %s ) /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )' % (L('T'), L('T'), DG, DG)
WTY0 = '( ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) /\\ D e. %s )' % (GK, GK, GJ, STK('T'))
PH0 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ %s ) ) )'
       % (PHM, STM0, LAB0, FTY, WTY0, NSS, HE))


def ctx0(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH0, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1l', PHM)
    meq = g('simp1r', '( M ` A ) = %s' % STM0)
    lab = g('simp2', LAB0)
    p3 = g('simp3', '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (FTY, WTY0, NSS, HE))
    ae = w.s([lab, w.inst('simp1')], 'syl', '( %s -> ( A e. %s /\\ E e. %s ) )' % (ph, L('T'), L('T')))
    al = w.s([ae], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([ae], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    kj2 = w.s([lab, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s ) )' % (ph, DG, DG))
    kk = w.s([kj2], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([kj2], 'simprd', '( %s -> J e. %s )' % (ph, DG))
    ne = w.s([lab, w.inst('simp3')], 'syl', '( %s -> K =/= J )' % ph)
    nes = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    ra = w.s([ft, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([ft, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    pp = w.s([ft, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTY0))
    w3 = w.s([wt], 'simpld', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) )' % (ph, GK, GK, GJ))
    yy = w.s([w3, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([w3, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    hw = w.s([w3, w.inst('simp3')], 'syl', '( %s -> H e. Word %s )' % (ph, GJ))
    dd = w.s([wt], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    nh = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HE))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, el=el, kk=kk, jj=jj, ne=ne, nes=nes, ra=ra, cc=cc, pp=pp,
                yy=yy, xx=xx, hw=hw, dd=dd, nss=nss, he=he, tv=tv)


def stmtty0(w, ph, u):
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], jp, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    j = w.s([pu, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, PU, STMT_T, GE, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR0, STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STM0, STMT_T))
    return dict(fa=fa, fe=fe, ga=ga, ge=ge, pu=pu, br=br, pop=po)


def tm2fmvn0():
    lab = 'tm2fmvn0'
    ph = PH0
    D1 = UPD2(RY, 'H'); D2 = UPD2('X', 'H')
    DK1 = UPD('T', 'D', 'K', RY)
    NV = NVF('v', 'Y')
    w = W(lab, 'The exit step of the mover with the internal state confined to '
               'a class ` N ` : Lean\'s ` moveNum_loop\' ` , the ` nil ` case.')
    u = ctx0(w, ph)
    t = stmtty0(w, ph, u)
    s1c = w.s([u['yy']], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    s1n = w.s([], 's1nz', '<" Y "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    ryw = w.s([s1c, u['xx'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    ryn = w.s([s1c, s1na, u['xx'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, RY))
    d1cl = upd2cl(w, ph, RY, 'H', GK, GJ, u['tv'], u['dd'], u['kk'], u['jj'], ryw, u['hw'])
    d2cl = upd2cl(w, ph, 'X', 'H', GK, GJ, u['tv'], u['dd'], u['kk'], u['jj'], u['xx'], u['hw'])
    k1 = w.s([u['kk'], ryw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, RY, GK))
    dk1 = w.s([u['tv'], u['dd'], k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DK1, STK('T')))
    rf = rfun(w, ph, u['ra'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = A_(u['nss'], NSS)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG)
        ne = A_(u['ne'], 'K =/= J')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T')); hea = A_(u['he'], HE)
        ela = A_(u['el'], 'E e. %s' % L('T'))
        fe = A_(t['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        ga = A_(t['ga'], '%s e. %s' % (GA, STMT_T)); ge = A_(t['ge'], '%s e. %s' % (GE, STMT_T))
        pu = A_(t['pu'], '%s e. %s' % (PU, STMT_T)); br = A_(t['br'], '%s e. %s' % (BR0, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T')))
        rywa = A_(ryw, '%s e. Word %s' % (RY, GK)); ryna = A_(ryn, '%s =/= (/)' % RY)
        xxa = A_(u['xx'], 'X e. Word %s' % GK); hwa = A_(u['hw'], 'H e. Word %s' % GJ)
        yya = A_(u['yy'], 'Y e. %s' % GK)
        rff = A_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        a1 = updn(w, av, DK1, 'J', 'H', 'Word %s' % GJ, 'K', tv, dk1a, jj, hwa, kk, ne)
        ryv = w.s([rywa], 'elexd', '( %s -> %s e. _V )' % (av, RY))
        a2 = updkval(w, av, 'T', 'D', 'K', RY, tv, dd, kk, ryv)
        rk = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (av, D1, RY))
        rnn = w.s([ryna], 'neneqd', '( %s -> -. %s = (/) )' % (av, RY))
        yj = w.s([yya, xxa], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        rfv = w.s([yj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Y )' % (av, RY))
        rtl = w.s([yj, w.inst('wrdtls1')], 'syl', '( %s -> %s = X )' % (av, TL(RY)))
        tdj = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T'))), ne],
                  'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (av, STK('T')))
        pk2 = w.s([kk, w.s([rywa, xxa], 'jca', '( %s -> ( %s e. Word %s /\\ X e. Word %s ) )'
                            % (av, RY, GK, GK))], 'jca',
                  '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ X e. Word %s ) ) )' % (av, DG, RY, GK, GK))
        pj1 = w.s([jj, hwa], 'jca', '( %s -> ( J e. %s /\\ H e. Word %s ) )' % (av, DG, GJ))
        up3 = w.s([tdj, pk2, pj1, w.inst('tm2stkup3')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', 'X'), D2))
        # the exit interface at r := v
        PAIR = '( -. ( C ` %s ) = 1o /\\ %s e. N )'
        i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` Y ) >. = <. v , ( inl ` Y ) >. )')
        i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (NVF('r', 'Y'), NV))
        i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (NVF('r', 'Y'), NV))
        i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (NVF('r', 'Y'), NV))
        i5 = w.s([i4], 'notbid', '( r = v -> ( -. ( C ` %s ) = 1o <-> -. ( C ` %s ) = 1o ) )' % (NVF('r', 'Y'), NV))
        i6 = w.s([i2], 'eleq1d', '( r = v -> ( %s e. N <-> %s e. N ) )' % (NVF('r', 'Y'), NV))
        i7 = w.s([i5, i6], 'anbi12d', '( r = v -> ( %s <-> %s ) )'
                 % (PAIR % (NVF('r', 'Y'), NVF('r', 'Y')), PAIR % (NV, NV)))
        h2 = w.s([i7, hea, vn], 'rspcdva', '( %s -> %s )' % (av, PAIR % (NV, NV)))
        rc = w.s([h2], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        nvn = w.s([h2], 'simprd', '( %s -> %s e. N )' % (av, NV))
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2, STK('T')): d2,
                 '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, RATY: ra, CTY: cc, PTY: pp,
                 '%s e. %s' % (BR0, STMT_T): br, '%s e. %s' % (PU, STMT_T): pu,
                 '%s e. %s' % (GA, STMT_T): ga, '%s e. %s' % (GE, STMT_T): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe}
        rules = {'( %s ` K )' % D1: (RY, rk), '( %s ` 0 )' % RY: ('Y', rfv), TL(RY): ('X', rtl),
                 UPD('T', D1, 'K', 'X'): (D2, up3),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NV): ('E', rge)}
        ifr = {'%s = (/)' % RY: (False, rnn), '( C ` %s ) = 1o' % NV: (False, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM0, '<. v , %s >.' % D1)
        want_res = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV, D2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM0)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), D1, STM0, SA('T'), D1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), D1, res))
        return fin, NV, nvn
    hstepcp(w, ph, 'T', 'M', 'A', 'E', 'N', D1, D2, (u['meq'], u['phm']), u['al'], u['el'],
            u['nss'], d1cl, d2cl, body, qed=True)
    return w.run()


WTYF = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
        % (GK, GJ, GK, GK, GJ, STK('T')))
PHF = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
       % (PHM, STM0, LAB0, FTY, WTYF, NSS, HC, HE))


def CLNE(X, Y):
    return '( { ( inl ` E ) } X. ( N X. { %s } ) )' % UPD2(X, Y)


def tm2fmvn():
    lab = 'tm2fmvn'
    ph = '( %s /\\ W e. Word B )' % PHF
    RVW = '( reverse ` W )'
    RVH = '( %s ++ H )' % RVW
    w = W(lab, 'The mover with the internal state confined to a class ` N ` : '
               'Lean\'s ` moveNum_runs\' ` .  At '
               '` N = { r e. ( 2nd ` T ) | ( U ` r ) = X } ` it says the field '
               '` U ` --- Lean\'s ` flag ` , ` cmp ` , ` carry ` --- has the '
               'same value at the exit as at the entry.')
    phm0 = w.s([], 'simp1l', '( %s -> %s )' % (PHF, PHM))
    meq0 = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHF, STM0))
    lab0 = w.s([], 'simp2', '( %s -> %s )' % (PHF, LAB0))
    p30 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
              % (PHF, FTY, WTYF, NSS, HC, HE))
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm0, PHM); meq = A_(meq0, '( M ` A ) = %s' % STM0)
    lab2 = A_(lab0, LAB0)
    p3 = A_(p30, '( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (FTY, WTYF, NSS, HC, HE))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTYF))
    nh = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (ph, NSS, HC, HE))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    ce = w.s([nh], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, HC, HE))
    hc = w.s([ce], 'simpld', '( %s -> %s )' % (ph, HC))
    he = w.s([ce], 'simprd', '( %s -> %s )' % (ph, HE))
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ))
    bj = w.s([b2], 'simprd', '( %s -> B C_ %s )' % (ph, GJ))
    w3 = w.s([wt, w.inst('simp2')], 'syl',
             '( %s -> ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) )' % (ph, GK, GK, GJ))
    yy = w.s([w3, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([w3, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    hw = w.s([w3, w.inst('simp3')], 'syl', '( %s -> H e. Word %s )' % (ph, GJ))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    ae = w.s([lab2, w.inst('simp1')], 'syl', '( %s -> ( A e. %s /\\ E e. %s ) )' % (ph, L('T'), L('T')))
    al = w.s([ae], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([ae], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    kj2 = w.s([lab2, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s ) )' % (ph, DG, DG))
    ne = w.s([lab2, w.inst('simp3')], 'syl', '( %s -> K =/= J )' % ph)
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    ryw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    labm = w.s([al, kj2, ne], '3jca', '( %s -> %s )' % (ph, LAB))
    WTYi = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( %s e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
            % (GK, GJ, RY, GK, GJ, STK('T')))
    wtym = w.s([b2, w.s([ryw, hw], 'jca', '( %s -> ( %s e. Word %s /\\ H e. Word %s ) )' % (ph, RY, GK, GJ)),
                dd], '3jca', '( %s -> %s )' % (ph, WTYi))
    nhc = w.s([nss, hc], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HC))
    qtym = w.s([ge, nhc], 'jca', '( %s -> ( %s e. %s /\\ ( %s /\\ %s ) ) )' % (ph, GE, STMT_T, NSS, HC))
    pm1 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STM0))
    pm3 = w.s([ft, wtym, qtym], '3jca',
              '( %s -> ( %s /\\ %s /\\ ( %s e. %s /\\ ( %s /\\ %s ) ) ) )'
              % (ph, FTY, WTYi, GE, STMT_T, NSS, HC))
    PH1i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s e. %s /\\ ( %s /\\ %s ) ) ) )'
            % (PHM, STM0, LAB, FTY, WTYi, GE, STMT_T, NSS, HC))
    pmi = w.s([pm1, labm, pm3], '3jca', '( %s -> %s )' % (ph, PH1i))
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    wu = w.s([ww, w0a], 'jca', '( %s -> ( W e. Word B /\\ (/) e. Word B ) )' % ph)
    ant = w.s([pmi, wu], 'jca', '( %s -> ( %s /\\ ( W e. Word B /\\ (/) e. Word B ) ) )' % (ph, PH1i))
    C0 = CLN('( W ++ %s )' % RY, '( (/) ++ H )')
    C1 = CLN('( (/) ++ %s )' % RY, '( ( %s ++ (/) ) ++ H )' % RVW)
    loop = w.s([ant, w.inst('tm2fmvnw')], 'syl', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C1, '( # ` W )')))
    lid1 = w.s([hw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ H ) = H )' % ph)
    c1s, n1 = w.rewrite(C0, {'( (/) ++ H )': ('H', lid1)}, ph)
    assert n1 == CLN('( W ++ %s )' % RY, 'H'), n1
    lid2 = w.s([ryw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, RY, RY))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word B )' % (ph, RVW))
    rid = w.s([rvc, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, RVW, RVW))
    c2s, n2 = w.rewrite(C1, {'( (/) ++ %s )' % RY: (RY, lid2), '( %s ++ (/) )' % RVW: (RVW, rid)}, ph)
    assert n2 == CLN(RY, RVH), n2
    o1 = w.s([c2s], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )' % (ph, C1, CLN(RY, RVH)))
    b1 = w.s([c1s, o1], 'breq12d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(C0, 'T', 'M', C1, '( # ` W )'),
                HR(CLN('( W ++ %s )' % RY, 'H'), 'T', 'M', CLN(RY, RVH), '( # ` W )')))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )'
                % (ph, HR(CLN('( W ++ %s )' % RY, 'H'), 'T', 'M', CLN(RY, RVH), '( # ` W )')))
    swj = w.s([bj, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GJ))
    rvg = w.s([swj, rvc], 'sseldd', '( %s -> %s e. Word %s )' % (ph, RVW, GJ))
    rvh = w.s([rvg, hw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RVH, GJ))
    WTY0i = ('( ( Y e. %s /\\ X e. Word %s /\\ %s e. Word %s ) /\\ D e. %s )'
             % (GK, GK, RVH, GJ, STK('T')))
    wty0 = w.s([w.s([yy, xx, rvh], '3jca', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ %s e. Word %s ) )'
                    % (ph, GK, GK, RVH, GJ)), dd], 'jca', '( %s -> %s )' % (ph, WTY0i))
    nhe = w.s([nss, he], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HE))
    p30i = w.s([ft, wty0, nhe], '3jca', '( %s -> ( %s /\\ %s /\\ ( %s /\\ %s ) ) )' % (ph, FTY, WTY0i, NSS, HE))
    PH0i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ %s ) ) )'
            % (PHM, STM0, LAB0, FTY, WTY0i, NSS, HE))
    p0i = w.s([pm1, lab2, p30i], '3jca', '( %s -> %s )' % (ph, PH0i))
    exit_ = w.s([p0i, w.inst('tm2fmvn0')], 'syl', '( %s -> %s )'
                % (ph, HR(CLN(RY, RVH), 'T', 'M', CLNE('X', RVH), '1')))
    w.qed([phm, loop2, exit_], 'syl3anc', '( %s -> %s )'
          % (ph, HR(CLN('( W ++ %s )' % RY, 'H'), 'T', 'M', CLNE('X', RVH), '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fmvn1'): tm2fmvn1()
    if want('tm2fmvnw'): tm2fmvnw()
    if want('tm2fmvn0'): tm2fmvn0()
    if want('tm2fmvn'): tm2fmvn()
