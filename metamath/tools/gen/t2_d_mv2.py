"""T2: the copier's loop `move2Num` of TM/Prims.lean (blueprint 3.2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t2_c_mov import constfty, rfun, updn, OPT, RATY, CTY, DG, GK, ST, STMT_T, TL, NVF

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GJ = '( %s ` J )' % G('T')
GI = '( %s ` I )' % G('T')
PTY = 'P e. ( %s ^m %s )' % (GJ, S('T'))
OTY = 'O e. ( %s ^m %s )' % (GI, S('T'))
GA = GOTO(CONSTF('T', 'A'))
PUI = PUSH('I', 'O', GA)
PUJ = PUSH('J', 'P', PUI)
BR = BRANCH('C', PUJ, 'Q')
STM = POP('K', 'F', BR)
HC = ('A. r e. %s A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z /\\ ( O ` %s ) = z )'
      % (S('T'), NVF('r', 'z'), NVF('r', 'z'), NVF('r', 'z')))
NE3 = '( K =/= J /\\ K =/= I /\\ J =/= I )'
LAB = '( A e. %s /\\ ( K e. %s /\\ J e. %s /\\ I e. %s ) /\\ %s )' % (L('T'), DG, DG, DG, NE3)
FTY = '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (RATY, CTY, PTY, OTY)
WTY = ('( ( B C_ %s /\\ B C_ %s /\\ B C_ %s ) /\\ ( R e. Word %s /\\ H e. Word %s /\\ N e. Word %s ) /\\ D e. %s )'
       % (GK, GJ, GI, GK, GJ, GI, STK('T')))
QTY = '( Q e. %s /\\ %s )' % (STMT_T, HC)
PH1 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM, LAB, FTY, WTY, QTY))


def UPD3(X, Y, Z):
    return UPD('T', UPD('T', UPD('T', 'D', 'K', X), 'J', Y), 'I', Z)


def CL3(X, Y, Z, lb='A'):
    return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (lb, S('T'), UPD3(X, Y, Z))


def ctx(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH1, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1l', PHM)
    meq = g('simp1r', '( M ` A ) = %s' % STM)
    lab = g('simp2', LAB)
    p3 = g('simp3', '( %s /\\ %s /\\ %s )' % (FTY, WTY, QTY))
    al = w.s([lab, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    kji = w.s([lab, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s /\\ I e. %s ) )' % (ph, DG, DG, DG))
    kk = w.s([kji, w.inst('simp1')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([kji, w.inst('simp2')], 'syl', '( %s -> J e. %s )' % (ph, DG))
    ii = w.s([kji, w.inst('simp3')], 'syl', '( %s -> I e. %s )' % (ph, DG))
    ne = w.s([lab, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, NE3))
    kj = w.s([ne, w.inst('simp1')], 'syl', '( %s -> K =/= J )' % ph)
    ki = w.s([ne, w.inst('simp2')], 'syl', '( %s -> K =/= I )' % ph)
    ji = w.s([ne, w.inst('simp3')], 'syl', '( %s -> J =/= I )' % ph)
    jk = w.s([kj], 'necomd', '( %s -> J =/= K )' % ph)
    ik = w.s([ki], 'necomd', '( %s -> I =/= K )' % ph)
    ij = w.s([ji], 'necomd', '( %s -> I =/= J )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    f1 = w.s([ft], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    f2 = w.s([ft], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, PTY, OTY))
    ra = w.s([f1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f1], 'simprd', '( %s -> %s )' % (ph, CTY))
    pp = w.s([f2], 'simpld', '( %s -> %s )' % (ph, PTY))
    oo = w.s([f2], 'simprd', '( %s -> %s )' % (ph, OTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTY))
    b3 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ, GI))
    bk = w.s([b3, w.inst('simp1')], 'syl', '( %s -> B C_ %s )' % (ph, GK))
    bj = w.s([b3, w.inst('simp2')], 'syl', '( %s -> B C_ %s )' % (ph, GJ))
    bi = w.s([b3, w.inst('simp3')], 'syl', '( %s -> B C_ %s )' % (ph, GI))
    r3 = w.s([wt, w.inst('simp2')], 'syl',
             '( %s -> ( R e. Word %s /\\ H e. Word %s /\\ N e. Word %s ) )' % (ph, GK, GJ, GI))
    rw = w.s([r3, w.inst('simp1')], 'syl', '( %s -> R e. Word %s )' % (ph, GK))
    hw = w.s([r3, w.inst('simp2')], 'syl', '( %s -> H e. Word %s )' % (ph, GJ))
    nw = w.s([r3, w.inst('simp3')], 'syl', '( %s -> N e. Word %s )' % (ph, GI))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    qt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, QTY))
    qq = w.s([qt], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    hc = w.s([qt], 'simprd', '( %s -> %s )' % (ph, HC))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, kk=kk, jj=jj, ii=ii, kj=kj, ki=ki, ji=ji,
                jk=jk, ik=ik, ij=ij, ne=ne, ra=ra, cc=cc, pp=pp, oo=oo,
                bk=bk, bj=bj, bi=bi, rw=rw, hw=hw, nw=nw, dd=dd, qq=qq, hc=hc, tv=tv)


def stmtty(w, ph, u):
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    io = w.s([u['ii'], u['oo']], 'jca', '( %s -> ( I e. %s /\\ %s ) )' % (ph, DG, OTY))
    pui = w.s([u['tv'], io, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUI, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    puj = w.s([u['tv'], jp, pui, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUJ, STMT_T))
    j = w.s([puj, u['qq']], 'jca', '( %s -> ( %s e. %s /\\ Q e. %s ) )' % (ph, PUJ, STMT_T, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR, STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STM, STMT_T))
    return dict(fa=fa, ga=ga, pui=pui, puj=puj, br=br, pop=po)


def hciter3(w, av, vv, ZT, zcl, hca):
    NV = NVF('v', ZT)
    NZ = NVF('v', 'z')
    RZ = NVF('r', 'z')
    def trip(a, b, c, rhs):
        return '( ( C ` %s ) = 1o /\\ ( P ` %s ) = %s /\\ ( O ` %s ) = %s )' % (a, b, rhs, c, rhs)
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (RZ, NZ))
    i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (RZ, NZ))
    i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (RZ, NZ))
    i5 = w.s([i2], 'fveq2d', '( r = v -> ( P ` %s ) = ( P ` %s ) )' % (RZ, NZ))
    i6 = w.s([i5], 'eqeq1d', '( r = v -> ( ( P ` %s ) = z <-> ( P ` %s ) = z ) )' % (RZ, NZ))
    i7 = w.s([i2], 'fveq2d', '( r = v -> ( O ` %s ) = ( O ` %s ) )' % (RZ, NZ))
    i8 = w.s([i7], 'eqeq1d', '( r = v -> ( ( O ` %s ) = z <-> ( O ` %s ) = z ) )' % (RZ, NZ))
    i9 = w.s([i4, i6, i8], '3anbi123d', '( r = v -> ( %s <-> %s ) )'
             % (trip(RZ, RZ, RZ, 'z'), trip(NZ, NZ, NZ, 'z')))
    i10 = w.s([i9], 'ralbidv', '( r = v -> ( A. z e. B %s <-> A. z e. B %s ) )'
              % (trip(RZ, RZ, RZ, 'z'), trip(NZ, NZ, NZ, 'z')))
    h1 = w.s([i10, hca, vv], 'rspcdva', '( %s -> A. z e. B %s )' % (av, trip(NZ, NZ, NZ, 'z')))
    j1 = w.s([], 'fveq2', '( z = %s -> ( inl ` z ) = ( inl ` %s ) )' % (ZT, ZT))
    j2 = w.s([j1], 'opeq2d', '( z = %s -> <. v , ( inl ` z ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    j3 = w.s([j2], 'fveq2d', '( z = %s -> %s = %s )' % (ZT, NZ, NV))
    j4 = w.s([j3], 'fveq2d', '( z = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NZ, NV))
    j5 = w.s([j4], 'eqeq1d', '( z = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (ZT, NZ, NV))
    jid = w.s([], 'id', '( z = %s -> z = %s )' % (ZT, ZT))
    j6 = w.s([j3], 'fveq2d', '( z = %s -> ( P ` %s ) = ( P ` %s ) )' % (ZT, NZ, NV))
    j7 = w.s([j6, jid], 'eqeq12d', '( z = %s -> ( ( P ` %s ) = z <-> ( P ` %s ) = %s ) )' % (ZT, NZ, NV, ZT))
    j8 = w.s([j3], 'fveq2d', '( z = %s -> ( O ` %s ) = ( O ` %s ) )' % (ZT, NZ, NV))
    j9 = w.s([j8, jid], 'eqeq12d', '( z = %s -> ( ( O ` %s ) = z <-> ( O ` %s ) = %s ) )' % (ZT, NZ, NV, ZT))
    j10 = w.s([j5, j7, j9], '3anbi123d', '( z = %s -> ( %s <-> %s ) )'
              % (ZT, trip(NZ, NZ, NZ, 'z'), trip(NV, NV, NV, ZT)))
    h2 = w.s([j10, h1, zcl], 'rspcdva', '( %s -> %s )' % (av, trip(NV, NV, NV, ZT)))
    bc = w.s([h2, w.inst('simp1')], 'syl', '( %s -> ( C ` %s ) = 1o )' % (av, NV))
    pv = w.s([h2, w.inst('simp2')], 'syl', '( %s -> ( P ` %s ) = %s )' % (av, NV, ZT))
    ov = w.s([h2, w.inst('simp3')], 'syl', '( %s -> ( O ` %s ) = %s )' % (av, NV, ZT))
    return bc, pv, ov


def upd3cl(w, ante, X, Y, Z, tv, dd, kk, jj, ii, xw, yw, zw):
    k1 = w.s([kk, xw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ante, DG, X, GK))
    j1 = w.s([jj, yw], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ante, DG, Y, GJ))
    i1 = w.s([ii, zw], 'jca', '( %s -> ( I e. %s /\\ %s e. Word %s ) )' % (ante, DG, Z, GI))
    d1 = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc',
             '( %s -> %s e. %s )' % (ante, UPD('T', 'D', 'K', X), STK('T')))
    d2 = w.s([tv, d1, j1, w.inst('tm2stkupd')], 'syl3anc',
             '( %s -> %s e. %s )' % (ante, UPD('T', UPD('T', 'D', 'K', X), 'J', Y), STK('T')))
    d3 = w.s([tv, d2, i1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ante, UPD3(X, Y, Z), STK('T')))
    return d1, d2, d3


def tm2fmv21():
    lab = 'tm2fmv21'
    ph = '( ( %s /\\ ( x e. Word B /\\ s e. Word B ) ) /\\ x =/= (/) )' % PH1
    XR = '( x ++ R )'; SH = '( s ++ H )'; SN = '( s ++ N )'
    TXR = '( %s ++ R )' % TL('x'); X0 = '( x ` 0 )'
    XS = '( <" %s "> ++ s )' % X0
    ACH = '( %s ++ H )' % XS; ACN = '( %s ++ N )' % XS
    D1 = UPD3(XR, SH, SN)
    D2 = UPD3(TXR, ACH, ACN)
    DK1 = UPD('T', 'D', 'K', XR); D1J = UPD('T', DK1, 'J', SH)
    D2K = UPD('T', D1, 'K', TXR)
    D3 = UPD('T', D2K, 'J', ACH)
    NV = NVF('v', X0)
    w = W(lab, 'One iteration of the copier ` move2Num ` of TM/Prims.lean: the '
               'label pops a letter of the scanned word from stack ` K ` and '
               'pushes it on both ` J ` and ` I ` .  Lean: ` move2Num_loop ` , '
               'the ` cons ` case.  The exit branch ` Q ` is a class variable.')
    u = ctx(w, ph, 'ad2antrr')
    t = stmtty(w, ph, u)
    xw = w.s([], 'simplrl', '( %s -> x e. Word B )' % ph)
    sw = w.s([], 'simplrr', '( %s -> s e. Word B )' % ph)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ph)
    swk = w.s([u['bk'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GK))
    swj = w.s([u['bj'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GJ))
    swi = w.s([u['bi'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GI))
    xwg = w.s([swk, xw], 'sseldd', '( %s -> x e. Word %s )' % (ph, GK))
    swgj = w.s([swj, sw], 'sseldd', '( %s -> s e. Word %s )' % (ph, GJ))
    swgi = w.s([swi, sw], 'sseldd', '( %s -> s e. Word %s )' % (ph, GI))
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ph, X0))
    x0k = w.s([u['bk'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GK))
    x0j = w.s([u['bj'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GJ))
    x0i = w.s([u['bi'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GI))
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ph, TL('x')))
    tlwg = w.s([swk, tlw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, TL('x'), GK))
    xrw = w.s([xwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, XR, GK))
    txrw = w.s([tlwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, TXR, GK))
    shw = w.s([swgj, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, SH, GJ))
    snw = w.s([swgi, u['nw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, SN, GI))
    s1j = w.s([x0j], 's1cld', '( %s -> <" %s "> e. Word %s )' % (ph, X0, GJ))
    s1i = w.s([x0i], 's1cld', '( %s -> <" %s "> e. Word %s )' % (ph, X0, GI))
    xsj = w.s([s1j, swgj, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, XS, GJ))
    xsi = w.s([s1i, swgi, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, XS, GI))
    achw = w.s([xsj, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ACH, GJ))
    acnw = w.s([xsi, u['nw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ACN, GI))
    xrn = w.s([xwg, xn, u['rw'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, XR))
    dk1, d1j, d1cl = upd3cl(w, ph, XR, SH, SN, u['tv'], u['dd'], u['kk'], u['jj'], u['ii'], xrw, shw, snw)
    _, _, d2cl = upd3cl(w, ph, TXR, ACH, ACN, u['tv'], u['dd'], u['kk'], u['jj'], u['ii'], txrw, achw, acnw)
    k2 = w.s([u['kk'], txrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, TXR, GK))
    d2kcl = w.s([u['tv'], d1cl, k2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2K, STK('T')))
    j3 = w.s([u['jj'], achw], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, ACH, GJ))
    d3cl = w.s([u['tv'], d2kcl, j3, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D3, STK('T')))
    rf = rfun(w, ph, u['ra'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG); ii = A_(u['ii'], 'I e. %s' % DG)
        kj = A_(u['kj'], 'K =/= J'); ki = A_(u['ki'], 'K =/= I'); ji = A_(u['ji'], 'J =/= I')
        jk = A_(u['jk'], 'J =/= K'); ik = A_(u['ik'], 'I =/= K'); ij = A_(u['ij'], 'I =/= J')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY); oo = A_(u['oo'], OTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T')); qq = A_(u['qq'], 'Q e. %s' % STMT_T)
        hca = A_(u['hc'], HC); aa = A_(u['al'], 'A e. %s' % L('T'))
        fa = A_(t['fa'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        ga = A_(t['ga'], '%s e. %s' % (GA, STMT_T)); pui = A_(t['pui'], '%s e. %s' % (PUI, STMT_T))
        puj = A_(t['puj'], '%s e. %s' % (PUJ, STMT_T)); br = A_(t['br'], '%s e. %s' % (BR, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        d2k = A_(d2kcl, '%s e. %s' % (D2K, STK('T'))); d3 = A_(d3cl, '%s e. %s' % (D3, STK('T')))
        dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T'))); d1ja = A_(d1j, '%s e. %s' % (D1J, STK('T')))
        xrwa = A_(xrw, '%s e. Word %s' % (XR, GK)); txrwa = A_(txrw, '%s e. Word %s' % (TXR, GK))
        shwa = A_(shw, '%s e. Word %s' % (SH, GJ)); snwa = A_(snw, '%s e. Word %s' % (SN, GI))
        achwa = A_(achw, '%s e. Word %s' % (ACH, GJ)); acnwa = A_(acnw, '%s e. Word %s' % (ACN, GI))
        xwga = A_(xwg, 'x e. Word %s' % GK); rwa = A_(u['rw'], 'R e. Word %s' % GK)
        swja = A_(swgj, 's e. Word %s' % GJ); swia = A_(swgi, 's e. Word %s' % GI)
        hwa = A_(u['hw'], 'H e. Word %s' % GJ); nwa = A_(u['nw'], 'N e. Word %s' % GI)
        xna = A_(xn, 'x =/= (/)'); x0b = A_(x0, '%s e. B' % X0)
        x0ka = A_(x0k, '%s e. %s' % (X0, GK))
        s1ja = A_(s1j, '<" %s "> e. Word %s' % (X0, GJ)); s1ia = A_(s1i, '<" %s "> e. Word %s' % (X0, GI))
        xrna = A_(xrn, '%s =/= (/)' % XR)
        rff = A_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        # ( D1 ` K ) = XR
        a1 = updn(w, av, D1J, 'I', SN, 'Word %s' % GI, 'K', tv, d1ja, ii, snwa, kk, ki)
        a2 = updn(w, av, DK1, 'J', SH, 'Word %s' % GJ, 'K', tv, dk1a, jj, shwa, kk, kj)
        xrv = w.s([xrwa], 'elexd', '( %s -> %s e. _V )' % (av, XR))
        a3 = updkval(w, av, 'T', 'D', 'K', XR, tv, dd, kk, xrv)
        a12 = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (av, D1, DK1))
        rk = w.s([a12, a3], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (av, D1, XR))
        # ( D2K ` J ) = SH
        b1 = updn(w, av, D1, 'K', TXR, 'Word %s' % GK, 'J', tv, d1, kk, txrwa, jj, jk)
        b2 = updn(w, av, D1J, 'I', SN, 'Word %s' % GI, 'J', tv, d1ja, ii, snwa, jj, ji)
        shv = w.s([shwa], 'elexd', '( %s -> %s e. _V )' % (av, SH))
        b3 = updkval(w, av, 'T', DK1, 'J', SH, tv, dk1a, jj, shv)
        b12 = w.s([b1, b2], 'eqtrd', '( %s -> ( %s ` J ) = ( %s ` J ) )' % (av, D2K, D1J))
        rj = w.s([b12, b3], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (av, D2K, SH))
        # ( D3 ` I ) = SN
        c1 = updn(w, av, D2K, 'J', ACH, 'Word %s' % GJ, 'I', tv, d2k, jj, achwa, ii, ij)
        c2 = updn(w, av, D1, 'K', TXR, 'Word %s' % GK, 'I', tv, d1, kk, txrwa, ii, ik)
        snv = w.s([snwa], 'elexd', '( %s -> %s e. _V )' % (av, SN))
        c3 = updkval(w, av, 'T', D1J, 'I', SN, tv, d1ja, ii, snv)
        c12 = w.s([c1, c2], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (av, D3, D1))
        ri = w.s([c12, c3], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (av, D3, SN))
        # the word steps
        xnn = w.s([xrna], 'neneqd', '( %s -> -. %s = (/) )' % (av, XR))
        nnx = w.s([xwga, xna, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` x ) e. NN )' % av)
        xpos = w.s([nnx, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` x ) )' % av)
        rfv = w.s([xwga, rwa, xpos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = %s )' % (av, XR, X0))
        rtl = w.s([xwga, xna, rwa, w.inst('wrdtlcc')], 'syl3anc', '( %s -> %s = %s )' % (av, TL(XR), TXR))
        ash = w.s([s1ja, swja, hwa, w.inst('ccatass')], 'syl3anc',
                  '( %s -> %s = ( <" %s "> ++ %s ) )' % (av, ACH, X0, SH))
        ashc = w.s([ash], 'eqcomd', '( %s -> ( <" %s "> ++ %s ) = %s )' % (av, X0, SH, ACH))
        asn = w.s([s1ia, swia, nwa, w.inst('ccatass')], 'syl3anc',
                  '( %s -> %s = ( <" %s "> ++ %s ) )' % (av, ACN, X0, SN))
        asnc = w.s([asn], 'eqcomd', '( %s -> ( <" %s "> ++ %s ) = %s )' % (av, X0, SN, ACN))
        # the six-update collapse
        ne3 = w.s([kj, ki, ji], '3jca', '( %s -> %s )' % (av, NE3))
        tdn = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T'))), ne3],
                  'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ %s ) )' % (av, STK('T'), NE3))
        qk = w.s([kk, w.s([xrwa, txrwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                           % (av, XR, GK, TXR, GK))], 'jca',
                 '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (av, DG, XR, GK, TXR, GK))
        qj = w.s([jj, w.s([shwa, achwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                           % (av, SH, GJ, ACH, GJ))], 'jca',
                 '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (av, DG, SH, GJ, ACH, GJ))
        qi = w.s([ii, w.s([snwa, acnwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                           % (av, SN, GI, ACN, GI))], 'jca',
                 '( %s -> ( I e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (av, DG, SN, GI, ACN, GI))
        qji = w.s([qj, qi], 'jca', '( %s -> ( ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) /\\ '
                  '( I e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) ) )'
                  % (av, DG, SH, GJ, ACH, GJ, DG, SN, GI, ACN, GI))
        up6 = w.s([tdn, qk, qji, w.inst('tm2stkup6')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D3, 'I', ACN), D2))
        bc, pv, ov = hciter3(w, av, vv, X0, x0b, hca)
        djl = w.s([x0ka, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (av, X0, OPT))
        pr = w.s([vv, djl], 'opelxpd', '( %s -> <. v , ( inl ` %s ) >. e. ( %s X. %s ) )' % (av, X0, S('T'), OPT))
        nvcl = w.s([rff, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        avv = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2K, STK('T')): d2k,
                 '%s e. %s' % (D3, STK('T')): d3, '%s e. %s' % (D2, STK('T')): d2,
                 '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, 'I e. %s' % DG: ii,
                 RATY: ra, CTY: cc, PTY: pp, OTY: oo,
                 '%s e. %s' % (BR, STMT_T): br, '%s e. %s' % (PUJ, STMT_T): puj,
                 '%s e. %s' % (PUI, STMT_T): pui, '%s e. %s' % (GA, STMT_T): ga,
                 'Q e. %s' % STMT_T: qq,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): fa}
        rules = {'( %s ` K )' % D1: (XR, rk), '( %s ` J )' % D2K: (SH, rj), '( %s ` I )' % D3: (SN, ri),
                 '( %s ` 0 )' % XR: (X0, rfv), TL(XR): (TXR, rtl),
                 '( <" %s "> ++ %s )' % (X0, SH): (ACH, ashc),
                 '( <" %s "> ++ %s )' % (X0, SN): (ACN, asnc),
                 '( P ` %s )' % NV: (X0, pv), '( O ` %s )' % NV: (X0, ov),
                 UPD('T', D3, 'I', ACN): (D2, up6),
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
        return fin, NV, nvcl
    hstepc(w, ph, 'T', 'M', 'A', 'A', D1, D2, (u['meq'], u['phm']), u['al'], u['al'],
           d1cl, d2cl, body, qed=True)
    return w.run()


JMV2 = ('( p e. _V |-> ( { ( inl ` A ) } X. ( %s X. { %s } ) ) )'
        % (S('T'), UPD3('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )', '( ( 2nd ` p ) ++ N )')))


def cl3ex(w, ante, X, Y, Z):
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    b = w.s([], 'fvex', '%s e. _V' % S('T'))
    c = w.s([], 'snex', '{ %s } e. _V' % UPD3(X, Y, Z))
    d = w.s([b, c], 'xpex', '( %s X. { %s } ) e. _V' % (S('T'), UPD3(X, Y, Z)))
    e = w.s([a, d], 'xpex', '%s e. _V' % CL3(X, Y, Z))
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, CL3(X, Y, Z)))


def jmv2(w, ante, U, WW, ucl, wcl):
    aq = '( %s /\\ p = <. %s , %s >. )' % (ante, U, WW)
    lp = w.s([], 'simpr', '( %s -> p = <. %s , %s >. )' % (aq, U, WW))
    body = ('( { ( inl ` A ) } X. ( %s X. { %s } ) )'
            % (S('T'), UPD3('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )', '( ( 2nd ` p ) ++ N )')))
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
    tgt = CL3('( %s ++ R )' % U, '( %s ++ H )' % WW, '( %s ++ N )' % WW)
    assert res == tgt, res
    h2 = w.s([st, ev], 'eqtrd', '( %s -> %s = %s )' % (aq, body, tgt))
    eqi = w.s([], 'eqid', '%s = %s' % (JMV2, JMV2))
    opv = w.s([], 'opex', '<. %s , %s >. e. _V' % (U, WW))
    opva = w.s([opv], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (ante, U, WW))
    cex = cl3ex(w, ante, '( %s ++ R )' % U, '( %s ++ H )' % WW, '( %s ++ N )' % WW)
    return w.s([h2, eqi, opva, cex], 'fvmptd2',
               '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, JMV2, U, WW, tgt))


def tm2fmv2w():
    lab = 'tm2fmv2w'
    ph = '( %s /\\ ( W e. Word B /\\ U e. Word B ) )' % PH1
    phx = '( %s /\\ ( x e. Word B /\\ s e. Word B ) )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    X0 = '( x ` 0 )'
    ACCx = '( <" %s "> ++ s )' % X0
    HRx = HR('( %s ` <. x , s >. )' % JMV2, 'T', 'M',
             '( %s ` <. %s , %s >. )' % (JMV2, TL('x'), ACCx), '1')
    HYPJ = 'A. x e. Word B A. s e. Word B ( x =/= (/) -> %s )' % HRx
    ZCJ = 'A. s e. Word B ( %s ` <. (/) , s >. ) C_ %s' % (JMV2, CFG('T'))
    CLx = CL3('( x ++ R )', '( s ++ H )', '( s ++ N )')
    CLt = CL3('( %s ++ R )' % TL('x'), '( %s ++ H )' % ACCx, '( %s ++ N )' % ACCx)
    w = W(lab, 'The scan loop of the copier ` move2Num ` of TM/Prims.lean: the '
               'label moves the whole scanned word from stack ` K ` onto both '
               '` J ` and ` I ` , reversed, one step per letter.  An '
               'instantiation of ~ tm2hwrd2 ; the two destinations accumulate '
               'the same word, so the accumulating word recursion applies '
               'unchanged.')
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ante2, PH1))
    xw1 = w.s([], 'simplrl', '( %s -> x e. Word B )' % ante2)
    sw1 = w.s([], 'simplrr', '( %s -> s e. Word B )' % ante2)
    xn1 = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    one = w.s([], 'tm2fmv21', '( %s -> %s )' % (ante2, HR(CLx, 'T', 'M', CLt, '1')))
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    x01 = w.s([xw1, xn1, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ante2, X0))
    s1c1 = w.s([x01], 's1cld', '( %s -> <" %s "> e. Word B )' % (ante2, X0))
    acw1 = w.s([s1c1, sw1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ante2, ACCx))
    jx = jmv2(w, ante2, 'x', 's', xw1, sw1)
    jt = jmv2(w, ante2, TL('x'), ACCx, tlw1, acw1)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` <. %s , %s >. ) , 1 >. = <. %s , 1 >. )'
             % (ante2, JMV2, TL('x'), ACCx, CLt))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JMV2, TL('x'), ACCx), '1'),
                HR(CLx, 'T', 'M', CLt, '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JMV2, TL('x'), ACCx), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JMV2, TL('x'), ACCx), '1')))
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
    jjs = B_(u['jj'], 'J e. %s' % DG); iis = B_(u['ii'], 'I e. %s' % DG)
    hws = B_(u['hw'], 'H e. Word %s' % GJ); nws = B_(u['nw'], 'N e. Word %s' % GI)
    rws = B_(u['rw'], 'R e. Word %s' % GK)
    bjs = B_(u['bj'], 'B C_ %s' % GJ); bis = B_(u['bi'], 'B C_ %s' % GI)
    sws2 = w.s([], 'simpr', '( %s -> s e. Word B )' % phs)
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0s = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % phs)
    jzs = jmv2(w, phs, '(/)', 's', w0s, sws2)
    swj = w.s([bjs, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (phs, GJ))
    swi = w.s([bis, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (phs, GI))
    sgj = w.s([swj, sws2], 'sseldd', '( %s -> s e. Word %s )' % (phs, GJ))
    sgi = w.s([swi, sws2], 'sseldd', '( %s -> s e. Word %s )' % (phs, GI))
    z0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. Word %s )' % (phs, GK))
    zrw = w.s([z0a, rws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( (/) ++ R ) e. Word %s )' % (phs, GK))
    shw = w.s([sgj, hws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( s ++ H ) e. Word %s )' % (phs, GJ))
    snw = w.s([sgi, nws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( s ++ N ) e. Word %s )' % (phs, GI))
    _, _, ups = upd3cl(w, phs, '( (/) ++ R )', '( s ++ H )', '( s ++ N )', tvs, dds, kks, jjs, iis, zrw, shw, snw)
    C0s = CL3('( (/) ++ R )', '( s ++ H )', '( s ++ N )')
    sn = w.s([ups], 'snssd', '( %s -> { %s } C_ %s )' % (phs, UPD3('( (/) ++ R )', '( s ++ H )', '( s ++ N )'), STK('T')))
    ssr = w.s([], 'ssid', '%s C_ %s' % (S('T'), S('T')))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (phs, S('T'), S('T')))
    xs = w.s([ssra, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ %s )' % (phs, S('T'), UPD3('( (/) ++ R )', '( s ++ H )', '( s ++ N )'), ST))
    cls = w.s([tvs, als, xs, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (phs, C0s, CFG('T')))
    clj = w.s([jzs, cls], 'eqsstrd', '( %s -> ( %s ` <. (/) , s >. ) C_ %s )' % (phs, JMV2, CFG('T')))
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
              % (ph, HR('( %s ` <. W , U >. )' % JMV2, 'T', 'M',
                        '( %s ` <. (/) , %s >. )' % (JMV2, RV), '( ( # ` W ) x. 1 )')))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    rvw = w.s([rvc, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, RV))
    w0b = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    jw = jmv2(w, ph, 'W', 'U', ww, uu)
    jz = jmv2(w, ph, '(/)', RV, w0b, rvw)
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    TGT0 = CL3('( (/) ++ R )', '( %s ++ H )' % RV, '( %s ++ N )' % RV)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` <. (/) , %s >. ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JMV2, RV, TGT0))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JMV2, 'T', 'M',
                       '( %s ` <. (/) , %s >. )' % (JMV2, RV), '( ( # ` W ) x. 1 )'),
                HR('( %s ` <. W , U >. )' % JMV2, 'T', 'M', TGT0, '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` <. W , U >. )' % JMV2, 'T', 'M', TGT0, '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JMV2, 'T', 'M', TGT0, '( # ` W )'),
                HR(CL3('( W ++ R )', '( U ++ H )', '( U ++ N )'), 'T', 'M', TGT0, '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )'
          % (ph, HR(CL3('( W ++ R )', '( U ++ H )', '( U ++ N )'), 'T', 'M', TGT0, '( # ` W )')))
    return w.run()


GE = GOTO(CONSTF('T', 'E'))
STM0 = POP('K', 'F', BRANCH('C', PUJ, GE))
BR0 = BRANCH('C', PUJ, GE)
RY = '( <" Y "> ++ X )'
HE = 'A. r e. %s -. ( C ` %s ) = 1o' % (S('T'), NVF('r', 'Y'))
LAB0 = ('( ( A e. %s /\\ E e. %s ) /\\ ( K e. %s /\\ J e. %s /\\ I e. %s ) /\\ %s )'
        % (L('T'), L('T'), DG, DG, DG, NE3))
WTY0 = ('( ( Y e. %s /\\ X e. Word %s ) /\\ ( H e. Word %s /\\ N e. Word %s ) /\\ D e. %s )'
        % (GK, GK, GJ, GI, STK('T')))
PH0 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM0, LAB0, FTY, WTY0, HE))


def ctx0(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH0, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1l', PHM)
    meq = g('simp1r', '( M ` A ) = %s' % STM0)
    lab = g('simp2', LAB0)
    p3 = g('simp3', '( %s /\\ %s /\\ %s )' % (FTY, WTY0, HE))
    ae = w.s([lab, w.inst('simp1')], 'syl', '( %s -> ( A e. %s /\\ E e. %s ) )' % (ph, L('T'), L('T')))
    al = w.s([ae], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([ae], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    kji = w.s([lab, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s /\\ I e. %s ) )' % (ph, DG, DG, DG))
    kk = w.s([kji, w.inst('simp1')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([kji, w.inst('simp2')], 'syl', '( %s -> J e. %s )' % (ph, DG))
    ii = w.s([kji, w.inst('simp3')], 'syl', '( %s -> I e. %s )' % (ph, DG))
    ne = w.s([lab, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, NE3))
    kj = w.s([ne, w.inst('simp1')], 'syl', '( %s -> K =/= J )' % ph)
    ki = w.s([ne, w.inst('simp2')], 'syl', '( %s -> K =/= I )' % ph)
    ji = w.s([ne, w.inst('simp3')], 'syl', '( %s -> J =/= I )' % ph)
    ik = w.s([ki], 'necomd', '( %s -> I =/= K )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    f1 = w.s([ft], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    f2 = w.s([ft], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, PTY, OTY))
    ra = w.s([f1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f1], 'simprd', '( %s -> %s )' % (ph, CTY))
    pp = w.s([f2], 'simpld', '( %s -> %s )' % (ph, PTY))
    oo = w.s([f2], 'simprd', '( %s -> %s )' % (ph, OTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTY0))
    yx = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (ph, GK, GK))
    yy = w.s([yx], 'simpld', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([yx], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    hn = w.s([wt, w.inst('simp2')], 'syl', '( %s -> ( H e. Word %s /\\ N e. Word %s ) )' % (ph, GJ, GI))
    hw = w.s([hn], 'simpld', '( %s -> H e. Word %s )' % (ph, GJ))
    nw = w.s([hn], 'simprd', '( %s -> N e. Word %s )' % (ph, GI))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    he = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, el=el, kk=kk, jj=jj, ii=ii, kj=kj, ki=ki, ji=ji, ik=ik,
                ne=ne, ra=ra, cc=cc, pp=pp, oo=oo, yy=yy, xx=xx, hw=hw, nw=nw, dd=dd, he=he, tv=tv)


def stmtty0(w, ph, u):
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    io = w.s([u['ii'], u['oo']], 'jca', '( %s -> ( I e. %s /\\ %s ) )' % (ph, DG, OTY))
    pui = w.s([u['tv'], io, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUI, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    puj = w.s([u['tv'], jp, pui, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUJ, STMT_T))
    j = w.s([puj, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, PUJ, STMT_T, GE, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR0, STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STM0, STMT_T))
    return dict(fa=fa, fe=fe, ga=ga, ge=ge, pui=pui, puj=puj, br=br, pop=po)


def tm2fmv20():
    lab = 'tm2fmv20'
    ph = PH0
    D1 = UPD3(RY, 'H', 'N')
    D2 = UPD3('X', 'H', 'N')
    DK1 = UPD('T', 'D', 'K', RY); D1J = UPD('T', DK1, 'J', 'H')
    DX = UPD('T', 'D', 'K', 'X'); DXJ = UPD('T', DX, 'J', 'H')
    NV = NVF('v', 'Y')
    w = W(lab, 'The exit step of the copier ` move2Num ` of TM/Prims.lean: the '
               'label pops the number\'s terminator and the machine jumps to '
               'the exit.  Lean: ` move2Num_loop ` , the ` nil ` case.')
    u = ctx0(w, ph)
    t = stmtty0(w, ph, u)
    s1c = w.s([u['yy']], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    s1n = w.s([], 's1nz', '<" Y "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    ryw = w.s([s1c, u['xx'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    ryn = w.s([s1c, s1na, u['xx'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, RY))
    dk1, d1j, d1cl = upd3cl(w, ph, RY, 'H', 'N', u['tv'], u['dd'], u['kk'], u['jj'], u['ii'],
                            ryw, u['hw'], u['nw'])
    dx, dxj, d2cl = upd3cl(w, ph, 'X', 'H', 'N', u['tv'], u['dd'], u['kk'], u['jj'], u['ii'],
                           u['xx'], u['hw'], u['nw'])
    rf = rfun(w, ph, u['ra'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG); ii = A_(u['ii'], 'I e. %s' % DG)
        kj = A_(u['kj'], 'K =/= J'); ki = A_(u['ki'], 'K =/= I'); ik = A_(u['ik'], 'I =/= K')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY); oo = A_(u['oo'], OTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T')); hea = A_(u['he'], HE)
        ela = A_(u['el'], 'E e. %s' % L('T'))
        fe = A_(t['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        ga = A_(t['ga'], '%s e. %s' % (GA, STMT_T)); ge = A_(t['ge'], '%s e. %s' % (GE, STMT_T))
        pui = A_(t['pui'], '%s e. %s' % (PUI, STMT_T)); puj = A_(t['puj'], '%s e. %s' % (PUJ, STMT_T))
        br = A_(t['br'], '%s e. %s' % (BR0, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T'))); d1ja = A_(d1j, '%s e. %s' % (D1J, STK('T')))
        rywa = A_(ryw, '%s e. Word %s' % (RY, GK)); ryna = A_(ryn, '%s =/= (/)' % RY)
        xxa = A_(u['xx'], 'X e. Word %s' % GK); hwa = A_(u['hw'], 'H e. Word %s' % GJ)
        nwa = A_(u['nw'], 'N e. Word %s' % GI); yya = A_(u['yy'], 'Y e. %s' % GK)
        rff = A_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        a1 = updn(w, av, D1J, 'I', 'N', 'Word %s' % GI, 'K', tv, d1ja, ii, nwa, kk, ki)
        a2 = updn(w, av, DK1, 'J', 'H', 'Word %s' % GJ, 'K', tv, dk1a, jj, hwa, kk, kj)
        ryv = w.s([rywa], 'elexd', '( %s -> %s e. _V )' % (av, RY))
        a3 = updkval(w, av, 'T', 'D', 'K', RY, tv, dd, kk, ryv)
        a12 = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (av, D1, DK1))
        rk = w.s([a12, a3], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (av, D1, RY))
        rnn = w.s([ryna], 'neneqd', '( %s -> -. %s = (/) )' % (av, RY))
        yj = w.s([yya, xxa], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        rfv = w.s([yj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Y )' % (av, RY))
        rtl = w.s([yj, w.inst('wrdtls1')], 'syl', '( %s -> %s = X )' % (av, TL(RY)))
        # UPD( D1 , K , X ) = D2 : commute past I, then tm2stkup3
        tdik = w.s([w.s([tv, d1ja], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (av, D1J, STK('T'))), ik],
                   'jca', '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ I =/= K ) )' % (av, D1J, STK('T')))
        pin = w.s([ii, nwa], 'jca', '( %s -> ( I e. %s /\\ N e. Word %s ) )' % (av, DG, GI))
        pkx = w.s([kk, xxa], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (av, DG, GK))
        sw1 = w.s([tdik, pin, pkx, w.inst('tm2stkupc')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', 'X'), UPD('T', UPD('T', D1J, 'K', 'X'), 'I', 'N')))
        tdkj = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T'))), kj],
                   'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (av, STK('T')))
        pk2 = w.s([kk, w.s([rywa, xxa], 'jca', '( %s -> ( %s e. Word %s /\\ X e. Word %s ) )'
                            % (av, RY, GK, GK))], 'jca',
                  '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ X e. Word %s ) ) )' % (av, DG, RY, GK, GK))
        pjh = w.s([jj, hwa], 'jca', '( %s -> ( J e. %s /\\ H e. Word %s ) )' % (av, DG, GJ))
        u3 = w.s([tdkj, pk2, pjh, w.inst('tm2stkup3')], 'syl3anc',
                 '( %s -> %s = %s )' % (av, UPD('T', D1J, 'K', 'X'), DXJ))
        r1, n1 = w.rewrite(UPD('T', UPD('T', D1J, 'K', 'X'), 'I', 'N'), {UPD('T', D1J, 'K', 'X'): (DXJ, u3)}, av)
        assert n1 == D2, n1
        up = w.s([sw1, r1], 'eqtrd', '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', 'X'), D2))
        i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` Y ) >. = <. v , ( inl ` Y ) >. )')
        i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (NVF('r', 'Y'), NV))
        i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (NVF('r', 'Y'), NV))
        i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (NVF('r', 'Y'), NV))
        i5 = w.s([i4], 'notbid', '( r = v -> ( -. ( C ` %s ) = 1o <-> -. ( C ` %s ) = 1o ) )' % (NVF('r', 'Y'), NV))
        rc = w.s([i5, hea, vv], 'rspcdva', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        djl = w.s([yya, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. %s )' % (av, OPT))
        pr = w.s([vv, djl], 'opelxpd', '( %s -> <. v , ( inl ` Y ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        nvcl = w.s([rff, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2, STK('T')): d2,
                 '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, 'I e. %s' % DG: ii,
                 RATY: ra, CTY: cc, PTY: pp, OTY: oo,
                 '%s e. %s' % (BR0, STMT_T): br, '%s e. %s' % (PUJ, STMT_T): puj,
                 '%s e. %s' % (PUI, STMT_T): pui, '%s e. %s' % (GA, STMT_T): ga,
                 '%s e. %s' % (GE, STMT_T): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe}
        rules = {'( %s ` K )' % D1: (RY, rk), '( %s ` 0 )' % RY: ('Y', rfv), TL(RY): ('X', rtl),
                 UPD('T', D1, 'K', 'X'): (D2, up),
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
        return fin, NV, nvcl
    hstepc(w, ph, 'T', 'M', 'A', 'E', D1, D2, (u['meq'], u['phm']), u['al'], u['el'],
           d1cl, d2cl, body, qed=True)
    return w.run()


WTYF = ('( ( B C_ %s /\\ B C_ %s /\\ B C_ %s ) /\\ ( ( Y e. %s /\\ X e. Word %s ) /\\ '
        '( H e. Word %s /\\ N e. Word %s ) ) /\\ D e. %s )'
        % (GK, GJ, GI, GK, GK, GJ, GI, STK('T')))
PHF = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ %s ) ) )'
       % (PHM, STM0, LAB0, FTY, WTYF, HC, HE))


def tm2fmv2():
    lab = 'tm2fmv2'
    ph = '( %s /\\ W e. Word B )' % PHF
    RVW = '( reverse ` W )'
    RVH = '( %s ++ H )' % RVW
    RVN = '( %s ++ N )' % RVW
    w = W(lab, 'The copier\'s loop ` move2Num ` of TM/Prims.lean: the label '
               'moves the whole number on stack ` K ` onto both ` J ` and '
               '` I ` , reversed, and pops its terminator, in '
               '` ( # ` W ) + 1 ` steps --- Lean\'s ` move2Num_runs ` bound '
               '` l.length + 1 ` .')
    phm0 = w.s([], 'simp1l', '( %s -> %s )' % (PHF, PHM))
    meq0 = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHF, STM0))
    lab0 = w.s([], 'simp2', '( %s -> %s )' % (PHF, LAB0))
    p30 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ ( %s /\\ %s ) ) )' % (PHF, FTY, WTYF, HC, HE))
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm0, PHM); meq = A_(meq0, '( M ` A ) = %s' % STM0)
    lab2 = A_(lab0, LAB0); p3 = A_(p30, '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (FTY, WTYF, HC, HE))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTYF))
    qt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, HC, HE))
    hc = w.s([qt], 'simpld', '( %s -> %s )' % (ph, HC))
    he = w.s([qt], 'simprd', '( %s -> %s )' % (ph, HE))
    b3 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ, GI))
    bj = w.s([b3, w.inst('simp2')], 'syl', '( %s -> B C_ %s )' % (ph, GJ))
    bi = w.s([b3, w.inst('simp3')], 'syl', '( %s -> B C_ %s )' % (ph, GI))
    w2 = w.s([wt, w.inst('simp2')], 'syl',
             '( %s -> ( ( Y e. %s /\\ X e. Word %s ) /\\ ( H e. Word %s /\\ N e. Word %s ) ) )'
             % (ph, GK, GK, GJ, GI))
    yx = w.s([w2], 'simpld', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (ph, GK, GK))
    hn = w.s([w2], 'simprd', '( %s -> ( H e. Word %s /\\ N e. Word %s ) )' % (ph, GJ, GI))
    yy = w.s([yx], 'simpld', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([yx], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    hw = w.s([hn], 'simpld', '( %s -> H e. Word %s )' % (ph, GJ))
    nw = w.s([hn], 'simprd', '( %s -> N e. Word %s )' % (ph, GI))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    ae = w.s([lab2, w.inst('simp1')], 'syl', '( %s -> ( A e. %s /\\ E e. %s ) )' % (ph, L('T'), L('T')))
    al = w.s([ae], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([ae], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    kji = w.s([lab2, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s /\\ I e. %s ) )' % (ph, DG, DG, DG))
    ne = w.s([lab2, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, NE3))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    ryw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    labm = w.s([al, kji, ne], '3jca', '( %s -> %s )' % (ph, LAB))
    WTYi = ('( ( B C_ %s /\\ B C_ %s /\\ B C_ %s ) /\\ ( %s e. Word %s /\\ H e. Word %s /\\ N e. Word %s ) /\\ D e. %s )'
            % (GK, GJ, GI, RY, GK, GJ, GI, STK('T')))
    wtym = w.s([b3, w.s([ryw, hw, nw], '3jca',
                        '( %s -> ( %s e. Word %s /\\ H e. Word %s /\\ N e. Word %s ) )' % (ph, RY, GK, GJ, GI)),
                dd], '3jca', '( %s -> %s )' % (ph, WTYi))
    qtym = w.s([ge, hc], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (ph, GE, STMT_T, HC))
    pm1 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STM0))
    pm3 = w.s([ft, wtym, qtym], '3jca',
              '( %s -> ( %s /\\ %s /\\ ( %s e. %s /\\ %s ) ) )' % (ph, FTY, WTYi, GE, STMT_T, HC))
    PH1i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s e. %s /\\ %s ) ) )'
            % (PHM, STM0, LAB, FTY, WTYi, GE, STMT_T, HC))
    pmi = w.s([pm1, labm, pm3], '3jca', '( %s -> %s )' % (ph, PH1i))
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    wu = w.s([ww, w0a], 'jca', '( %s -> ( W e. Word B /\\ (/) e. Word B ) )' % ph)
    ant = w.s([pmi, wu], 'jca', '( %s -> ( %s /\\ ( W e. Word B /\\ (/) e. Word B ) ) )' % (ph, PH1i))
    C0 = CL3('( W ++ %s )' % RY, '( (/) ++ H )', '( (/) ++ N )')
    C1 = CL3('( (/) ++ %s )' % RY, '( ( %s ++ (/) ) ++ H )' % RVW, '( ( %s ++ (/) ) ++ N )' % RVW)
    loop = w.s([ant, w.inst('tm2fmv2w')], 'syl', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C1, '( # ` W )')))
    lidh = w.s([hw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ H ) = H )' % ph)
    lidn = w.s([nw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ N ) = N )' % ph)
    c1s, n1 = w.rewrite(C0, {'( (/) ++ H )': ('H', lidh), '( (/) ++ N )': ('N', lidn)}, ph)
    assert n1 == CL3('( W ++ %s )' % RY, 'H', 'N'), n1
    lidr = w.s([ryw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, RY, RY))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word B )' % (ph, RVW))
    rid = w.s([rvc, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, RVW, RVW))
    c2s, n2 = w.rewrite(C1, {'( (/) ++ %s )' % RY: (RY, lidr), '( %s ++ (/) )' % RVW: (RVW, rid)}, ph)
    assert n2 == CL3(RY, RVH, RVN), n2
    o1 = w.s([c2s], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )'
             % (ph, C1, CL3(RY, RVH, RVN)))
    b1 = w.s([c1s, o1], 'breq12d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(C0, 'T', 'M', C1, '( # ` W )'),
                HR(CL3('( W ++ %s )' % RY, 'H', 'N'), 'T', 'M', CL3(RY, RVH, RVN), '( # ` W )')))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )'
                % (ph, HR(CL3('( W ++ %s )' % RY, 'H', 'N'), 'T', 'M', CL3(RY, RVH, RVN), '( # ` W )')))
    swj = w.s([bj, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GJ))
    swi = w.s([bi, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GI))
    rvgj = w.s([swj, rvc], 'sseldd', '( %s -> %s e. Word %s )' % (ph, RVW, GJ))
    rvgi = w.s([swi, rvc], 'sseldd', '( %s -> %s e. Word %s )' % (ph, RVW, GI))
    rvh = w.s([rvgj, hw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RVH, GJ))
    rvn = w.s([rvgi, nw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RVN, GI))
    WTY0i = ('( ( Y e. %s /\\ X e. Word %s ) /\\ ( %s e. Word %s /\\ %s e. Word %s ) /\\ D e. %s )'
             % (GK, GK, RVH, GJ, RVN, GI, STK('T')))
    wty0 = w.s([yx, w.s([rvh, rvn], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                        % (ph, RVH, GJ, RVN, GI)), dd], '3jca', '( %s -> %s )' % (ph, WTY0i))
    p30i = w.s([ft, wty0, he], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, FTY, WTY0i, HE))
    PH0i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
            % (PHM, STM0, LAB0, FTY, WTY0i, HE))
    p0i = w.s([pm1, lab2, p30i], '3jca', '( %s -> %s )' % (ph, PH0i))
    exit_ = w.s([p0i, w.inst('tm2fmv20')], 'syl', '( %s -> %s )'
                % (ph, HR(CL3(RY, RVH, RVN), 'T', 'M', CL3('X', RVH, RVN, 'E'), '1')))
    w.qed([phm, loop2, exit_], 'syl3anc', '( %s -> %s )'
          % (ph, HR(CL3('( W ++ %s )' % RY, 'H', 'N'), 'T', 'M', CL3('X', RVH, RVN, 'E'),
                    '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fmv21'): tm2fmv21()
    if want('tm2fmv2w'): tm2fmv2w()
    if want('tm2fmv20'): tm2fmv20()
    if want('tm2fmv2'): tm2fmv2()
