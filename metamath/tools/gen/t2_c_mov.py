"""T2: the mover `moveNum` of TM/Arith.lean as an instantiation of the
fragment calculus (blueprint 3.1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GK = '( %s ` K )' % G('T')
GJ = '( %s ` J )' % G('T')
ST = '( %s X. %s )' % (S('T'), STK('T'))
OPT = '( %s |_| 1o )' % GK
RATY = 'F e. ( %s ^m ( %s X. %s ) )' % (S('T'), S('T'), OPT)
CTY = 'C e. ( 2o ^m %s )' % S('T')
PTY = 'P e. ( %s ^m %s )' % (GJ, S('T'))
GA = GOTO(CONSTF('T', 'A'))
PU = PUSH('J', 'P', GA)
BR = BRANCH('C', PU, 'Q')
STM = POP('K', 'F', BR)
STMT_T = '( TM2Stmt ` T )'
TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)


def NVF(r, z):
    return '( F ` <. %s , ( inl ` %s ) >. )' % (r, z)


HC = ('A. r e. %s A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z )'
      % (S('T'), NVF('r', 'z'), NVF('r', 'z')))
LAB = '( A e. %s /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )' % (L('T'), DG, DG)
FTY = '( %s /\\ %s /\\ %s )' % (RATY, CTY, PTY)
WTY = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( R e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
       % (GK, GJ, GK, GJ, STK('T')))
QTY = '( Q e. %s /\\ %s )' % (STMT_T, HC)
PH1 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM, LAB, FTY, WTY, QTY))


def UPD2(X, Y):
    return UPD('T', UPD('T', 'D', 'K', X), 'J', Y)


def CL2(X, Y):
    return '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (S('T'), UPD2(X, Y))


def CL2E(X, Y):
    return '( { ( inl ` E ) } X. ( %s X. { %s } ) )' % (S('T'), UPD2(X, Y))


def ctx(w, ph, lift=None):
    """the components of PH1 under an antecedent ph reached from PH1 by `lift`"""
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
    hc = w.s([qt], 'simprd', '( %s -> %s )' % (ph, HC))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, kk=kk, jj=jj, ne=ne, nes=nes, ra=ra, cc=cc, pp=pp,
                bk=bk, bj=bj, rw=rw, hw=hw, dd=dd, qq=qq, hc=hc, tv=tv)


def constfty(w, ante, X, COD, xcl):
    f = w.s([xcl, w.inst('fconst6g')], 'syl', '( %s -> %s : %s --> %s )' % (ante, CONSTF('T', X), S('T'), COD))
    c1 = w.s([], 'fvex', '%s e. _V' % COD)
    c1a = w.s([c1], 'a1i', '( %s -> %s e. _V )' % (ante, COD))
    c2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    c2a = w.s([c2], 'a1i', '( %s -> %s e. _V )' % (ante, S('T')))
    bi = w.s([c1a, c2a, w.inst('elmapg')], 'syl2anc',
             '( %s -> ( %s e. ( %s ^m %s ) <-> %s : %s --> %s ) )'
             % (ante, CONSTF('T', X), COD, S('T'), CONSTF('T', X), S('T'), COD))
    return w.s([bi, f], 'mpbird', '( %s -> %s e. ( %s ^m %s ) )' % (ante, CONSTF('T', X), COD, S('T')))


def stmtty(w, ph, u):
    """the statement typings of the mover's code"""
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], jp, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    j = w.s([pu, u['qq']], 'jca', '( %s -> ( %s e. %s /\\ Q e. %s ) )' % (ph, PU, STMT_T, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR, STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STM, STMT_T))
    return dict(fa=fa, ga=ga, pu=pu, br=br, pop=po)


def updn(w, ante, Dc, Kup, Yv, YW, Jq, tv, dcl, kupcl, ywcl, jqcl, nestep):
    """( ante -> ( UPD(Dc,Kup,Yv) ` Jq ) = ( Dc ` Jq ) ), from Jq =/= Kup"""
    p1 = w.s([tv, dcl], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ante, Dc, STK('T')))
    p2 = w.s([kupcl, ywcl], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ante, Kup, DG, Yv, YW))
    p3 = w.s([jqcl, nestep], 'jca', '( %s -> ( %s e. %s /\\ %s =/= %s ) )' % (ante, Jq, DG, Jq, Kup))
    return w.s([p1, p2, p3, w.inst('tm2stkupn')], 'syl3anc',
               '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ante, UPD('T', Dc, Kup, Yv), Jq, Dc, Jq))


def rfun(w, ph, ra):
    """F as a function ( S X. ( GK |_| 1o ) ) --> S"""
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    gev = w.s([], 'fvex', '%s e. _V' % GK)
    o1e = w.s([], '1oex', '1o e. _V')
    oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xev = w.s([sev, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
    xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (ph, S('T'), OPT))
    rbi = w.s([seva, xeva, w.inst('elmapg')], 'syl2anc',
              '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (ph, RATY, S('T'), OPT, S('T')))
    return w.s([rbi, ra], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (ph, S('T'), OPT, S('T')))


def hciter(w, av, vv, ZT, zcl, hca):
    """from HC at ( r := v , z := ZT ): the branch is taken and the pushed
    letter is ZT"""
    NV = NVF('v', ZT)
    NZ = NVF('v', 'z')
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (NVF('r', 'z'), NZ))
    i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (NVF('r', 'z'), NZ))
    i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (NVF('r', 'z'), NZ))
    i5 = w.s([i2], 'fveq2d', '( r = v -> ( P ` %s ) = ( P ` %s ) )' % (NVF('r', 'z'), NZ))
    i6 = w.s([i5], 'eqeq1d', '( r = v -> ( ( P ` %s ) = z <-> ( P ` %s ) = z ) )' % (NVF('r', 'z'), NZ))
    i7 = w.s([i4, i6], 'anbi12d',
             '( r = v -> ( ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z ) <-> ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z ) ) )'
             % (NVF('r', 'z'), NVF('r', 'z'), NZ, NZ))
    i8 = w.s([i7], 'ralbidv',
             '( r = v -> ( A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z ) <-> '
             'A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z ) ) )'
             % (NVF('r', 'z'), NVF('r', 'z'), NZ, NZ))
    h1 = w.s([i8, hca, vv], 'rspcdva',
             '( %s -> A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z ) )' % (av, NZ, NZ))
    j1 = w.s([], 'fveq2', '( z = %s -> ( inl ` z ) = ( inl ` %s ) )' % (ZT, ZT))
    j2 = w.s([j1], 'opeq2d', '( z = %s -> <. v , ( inl ` z ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    j3 = w.s([j2], 'fveq2d', '( z = %s -> %s = %s )' % (ZT, NZ, NV))
    j4 = w.s([j3], 'fveq2d', '( z = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NZ, NV))
    j5 = w.s([j4], 'eqeq1d', '( z = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (ZT, NZ, NV))
    j6 = w.s([j3], 'fveq2d', '( z = %s -> ( P ` %s ) = ( P ` %s ) )' % (ZT, NZ, NV))
    j7 = w.s([], 'id', '( z = %s -> z = %s )' % (ZT, ZT))
    j8 = w.s([j6, j7], 'eqeq12d', '( z = %s -> ( ( P ` %s ) = z <-> ( P ` %s ) = %s ) )' % (ZT, NZ, NV, ZT))
    j9 = w.s([j5, j8], 'anbi12d',
             '( z = %s -> ( ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z ) <-> ( ( C ` %s ) = 1o /\\ ( P ` %s ) = %s ) ) )'
             % (ZT, NZ, NZ, NV, NV, ZT))
    h2 = w.s([j9, h1, zcl], 'rspcdva',
             '( %s -> ( ( C ` %s ) = 1o /\\ ( P ` %s ) = %s ) )' % (av, NV, NV, ZT))
    bc = w.s([h2], 'simpld', '( %s -> ( C ` %s ) = 1o )' % (av, NV))
    pv = w.s([h2], 'simprd', '( %s -> ( P ` %s ) = %s )' % (av, NV, ZT))
    return bc, pv


def tm2fmov1():
    lab = 'tm2fmov1'
    ph = '( ( %s /\\ ( x e. Word B /\\ s e. Word B ) ) /\\ x =/= (/) )' % PH1
    XR = '( x ++ R )'
    SH = '( s ++ H )'
    TXR = '( %s ++ R )' % TL('x')
    X0 = '( x ` 0 )'
    ACC = '( ( <" %s "> ++ s ) ++ H )' % X0
    D1 = UPD2(XR, SH)
    D2 = UPD2(TXR, ACC)
    DK1 = UPD('T', 'D', 'K', XR)
    D2K = UPD('T', D1, 'K', TXR)
    NV = NVF('v', X0)
    w = W(lab, 'One iteration of the mover ` moveNum ` of TM/Arith.lean: the '
               'label pops a letter of the scanned word from stack ` K ` , the '
               'branch on the internal state is true, the letter is pushed on '
               'stack ` J ` and the machine returns to the same label.  Lean: '
               '` moveNum_loop ` , the ` cons ` case.  The exit branch ` Q ` is '
               'a class variable, so a machine that halts where the mover jumps '
               'shares this lemma.')
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
    # the two stack assignments
    k1 = w.s([u['kk'], xrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, XR, GK))
    k2 = w.s([u['kk'], txrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, TXR, GK))
    j1c = w.s([u['jj'], shw], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, SH, GJ))
    j2c = w.s([u['jj'], accw], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, ACC, GJ))
    dk1 = w.s([u['tv'], u['dd'], k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DK1, STK('T')))
    dk2 = w.s([u['tv'], u['dd'], k2, w.inst('tm2stkupd')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', TXR), STK('T')))
    d1cl = w.s([u['tv'], dk1, j1c, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D1, STK('T')))
    d2cl = w.s([u['tv'], dk2, j2c, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))
    d2kcl = w.s([u['tv'], d1cl, k2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2K, STK('T')))
    rf = rfun(w, ph, u['ra'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG)
        ne = A_(u['ne'], 'K =/= J'); nes = A_(u['nes'], 'J =/= K')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T'))
        qq = A_(u['qq'], 'Q e. %s' % STMT_T)
        hca = A_(u['hc'], HC)
        aa = A_(u['al'], 'A e. %s' % L('T'))
        fa = A_(t['fa'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        ga = A_(t['ga'], '%s e. %s' % (GA, STMT_T)); pu = A_(t['pu'], '%s e. %s' % (PU, STMT_T))
        br = A_(t['br'], '%s e. %s' % (BR, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        d2k = A_(d2kcl, '%s e. %s' % (D2K, STK('T')))
        dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T')))
        xrwa = A_(xrw, '%s e. Word %s' % (XR, GK)); txrwa = A_(txrw, '%s e. Word %s' % (TXR, GK))
        shwa = A_(shw, '%s e. Word %s' % (SH, GJ)); accwa = A_(accw, '%s e. Word %s' % (ACC, GJ))
        xwga = A_(xwg, 'x e. Word %s' % GK); swga = A_(swg, 's e. Word %s' % GJ)
        rwa = A_(u['rw'], 'R e. Word %s' % GK); hwa = A_(u['hw'], 'H e. Word %s' % GJ)
        xna = A_(xn, 'x =/= (/)'); x0b = A_(x0, '%s e. B' % X0)
        x0ja = A_(x0j, '%s e. %s' % (X0, GJ))
        s1ca = A_(s1c, '<" %s "> e. Word %s' % (X0, GJ))
        rff = A_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        # ( D1 ` K ) = ( x ++ R )
        a1 = updn(w, av, DK1, 'J', SH, 'Word %s' % GJ, 'K', tv, dk1a, jj, shwa, kk, ne)
        xrv = w.s([xrwa], 'elexd', '( %s -> %s e. _V )' % (av, XR))
        a2 = updkval(w, av, 'T', 'D', 'K', XR, tv, dd, kk, xrv)
        rk = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (av, D1, XR))
        # ( D2K ` J ) = ( s ++ H )
        b1 = updn(w, av, D1, 'K', TXR, 'Word %s' % GK, 'J', tv, d1, kk, txrwa, jj, nes)
        shv = w.s([shwa], 'elexd', '( %s -> %s e. _V )' % (av, SH))
        b2 = updkval(w, av, 'T', DK1, 'J', SH, tv, dk1a, jj, shv)
        rj = w.s([b1, b2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (av, D2K, SH))
        # the word steps
        xrna = A_(xrn, '%s =/= (/)' % XR)
        xnn = w.s([xrna], 'neneqd', '( %s -> -. %s = (/) )' % (av, XR))
        nnx = w.s([xwga, xna, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` x ) e. NN )' % av)
        xpos = w.s([nnx, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` x ) )' % av)
        rfv = w.s([xwga, rwa, xpos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = %s )' % (av, XR, X0))
        rtl = w.s([xwga, xna, rwa, w.inst('wrdtlcc')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, TL(XR), TXR))
        # ccatass on the accumulator
        as1 = w.s([s1ca, swga, hwa, w.inst('ccatass')], 'syl3anc',
                  '( %s -> %s = ( <" %s "> ++ %s ) )' % (av, ACC, X0, SH))
        asc = w.s([as1], 'eqcomd', '( %s -> ( <" %s "> ++ %s ) = %s )' % (av, X0, SH, ACC))
        # the four-update collapse
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
        # the read interface
        bc, pv = hciter(w, av, vv, X0, x0b, hca)
        dj = w.s([x0b, A_(u['bk'], 'B C_ %s' % GK)], 'sseldd',
                 '( %s -> %s e. %s )' % (av, X0, GK))
        djl = w.s([dj, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (av, X0, OPT))
        pr = w.s([vv, djl], 'opelxpd', '( %s -> <. v , ( inl ` %s ) >. e. ( %s X. %s ) )' % (av, X0, S('T'), OPT))
        nvcl = w.s([rff, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        avv = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2K, STK('T')): d2k,
                 '%s e. %s' % (D2, STK('T')): d2,
                 '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, RATY: ra, CTY: cc, PTY: pp,
                 '%s e. %s' % (BR, STMT_T): br, '%s e. %s' % (PU, STMT_T): pu,
                 '%s e. %s' % (GA, STMT_T): ga, 'Q e. %s' % STMT_T: qq,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): fa}
        rules = {'( %s ` K )' % D1: (XR, rk),
                 '( %s ` J )' % D2K: (SH, rj),
                 '( %s ` 0 )' % XR: (X0, rfv),
                 TL(XR): (TXR, rtl),
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
        return fin, NV, nvcl
    hstepc(w, ph, 'T', 'M', 'A', 'A', D1, D2, (u['meq'], u['phm']), u['al'], u['al'],
           d1cl, d2cl, body, qed=True)
    return w.run()


JMOV = ('( p e. _V |-> ( { ( inl ` A ) } X. ( %s X. { %s } ) ) )'
        % (S('T'), UPD2('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )')))


def cl2ex(w, ante, X, Y):
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    b = w.s([], 'fvex', '%s e. _V' % S('T'))
    c = w.s([], 'snex', '{ %s } e. _V' % UPD2(X, Y))
    d = w.s([b, c], 'xpex', '( %s X. { %s } ) e. _V' % (S('T'), UPD2(X, Y)))
    e = w.s([a, d], 'xpex', '%s e. _V' % CL2(X, Y))
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, CL2(X, Y)))


def jmov(w, ante, U, WW, ucl, wcl):
    """( ante -> ( JMOV ` <. U , WW >. ) = CL2( U ++ R , WW ++ H ) )"""
    aq = '( %s /\\ p = <. %s , %s >. )' % (ante, U, WW)
    lp = w.s([], 'simpr', '( %s -> p = <. %s , %s >. )' % (aq, U, WW))
    body = ('( { ( inl ` A ) } X. ( %s X. { %s } ) )'
            % (S('T'), UPD2('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )')))
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
    tgt = CL2('( %s ++ R )' % U, '( %s ++ H )' % WW)
    assert res == tgt, res
    h2 = w.s([st, ev], 'eqtrd', '( %s -> %s = %s )' % (aq, body, tgt))
    eqi = w.s([], 'eqid', '%s = %s' % (JMOV, JMOV))
    opv = w.s([], 'opex', '<. %s , %s >. e. _V' % (U, WW))
    opva = w.s([opv], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (ante, U, WW))
    cex = cl2ex(w, ante, '( %s ++ R )' % U, '( %s ++ H )' % WW)
    return w.s([h2, eqi, opva, cex], 'fvmptd2', '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, JMOV, U, WW, tgt))


def clss(w, ante, X, Y, tv, al, updcl):
    """( ante -> CL2(X,Y) C_ ( TM2Cfg ` T ) )"""
    sn = w.s([updcl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, UPD2(X, Y), STK('T')))
    ssr = w.s([], 'ssid', '%s C_ %s' % (S('T'), S('T')))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (ante, S('T'), S('T')))
    xs = w.s([ssra, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ %s )' % (ante, S('T'), UPD2(X, Y), ST))
    return w.s([tv, al, xs, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ante, CL2(X, Y), CFG('T')))


def upd2cl(w, ante, X, Y, XW, YW, tv, dd, kk, jj, xw, yw):
    """( ante -> UPD2(X,Y) e. ( TM2Stk ` T ) )"""
    k1 = w.s([kk, xw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ante, DG, X, XW))
    j1 = w.s([jj, yw], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ante, DG, Y, YW))
    d1 = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc',
             '( %s -> %s e. %s )' % (ante, UPD('T', 'D', 'K', X), STK('T')))
    return w.s([tv, d1, j1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ante, UPD2(X, Y), STK('T')))


def tm2fmovw():
    lab = 'tm2fmovw'
    ph = '( %s /\\ ( W e. Word B /\\ U e. Word B ) )' % PH1
    phx = '( %s /\\ ( x e. Word B /\\ s e. Word B ) )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    X0 = '( x ` 0 )'
    ACCx = '( <" %s "> ++ s )' % X0
    HRx = HR('( %s ` <. x , s >. )' % JMOV, 'T', 'M',
             '( %s ` <. %s , %s >. )' % (JMOV, TL('x'), ACCx), '1')
    HYPJ = 'A. x e. Word B A. s e. Word B ( x =/= (/) -> %s )' % HRx
    ZCJ = 'A. s e. Word B ( %s ` <. (/) , s >. ) C_ %s' % (JMOV, CFG('T'))
    w = W(lab, 'The scan loop of the mover ` moveNum ` of TM/Arith.lean: the '
               'label moves the whole scanned word from stack ` K ` to stack '
               '` J ` , reversed, one step per letter.  An instantiation of '
               '~ tm2hwrd2 , which does once and for all the induction Lean\'s '
               '` moveNum_loop ` does by hand.')
    # the iteration hypothesis
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ante2, PH1))
    xw1 = w.s([], 'simplrl', '( %s -> x e. Word B )' % ante2)
    sw1 = w.s([], 'simplrr', '( %s -> s e. Word B )' % ante2)
    xn1 = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    one = w.s([], 'tm2fmov1', '( %s -> %s )'
              % (ante2, HR(CL2('( x ++ R )', '( s ++ H )'), 'T', 'M',
                           CL2('( %s ++ R )' % TL('x'), '( %s ++ H )' % ACCx), '1')))
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    x01 = w.s([xw1, xn1, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ante2, X0))
    s1c1 = w.s([x01], 's1cld', '( %s -> <" %s "> e. Word B )' % (ante2, X0))
    acw1 = w.s([s1c1, sw1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ante2, ACCx))
    jx = jmov(w, ante2, 'x', 's', xw1, sw1)
    jt = jmov(w, ante2, TL('x'), ACCx, tlw1, acw1)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` <. %s , %s >. ) , 1 >. = <. %s , 1 >. )'
             % (ante2, JMOV, TL('x'), ACCx, CL2('( %s ++ R )' % TL('x'), '( %s ++ H )' % ACCx)))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CL2('( x ++ R )', '( s ++ H )'), 'T', 'M',
                          '( %s ` <. %s , %s >. )' % (JMOV, TL('x'), ACCx), '1'),
                HR(CL2('( x ++ R )', '( s ++ H )'), 'T', 'M',
                   CL2('( %s ++ R )' % TL('x'), '( %s ++ H )' % ACCx), '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CL2('( x ++ R )', '( s ++ H )'), 'T', 'M',
                          '( %s ` <. %s , %s >. )' % (JMOV, TL('x'), ACCx), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CL2('( x ++ R )', '( s ++ H )'), 'T', 'M',
                               '( %s ` <. %s , %s >. )' % (JMOV, TL('x'), ACCx), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    ex2 = w.s([ex1], 'anassrs', '( ( ( %s /\\ x e. Word B ) /\\ s e. Word B ) -> ( x =/= (/) -> %s ) )' % (PH1, HRx))
    ex3 = w.s([ex2], 'ralrimiva', '( ( %s /\\ x e. Word B ) -> A. s e. Word B ( x =/= (/) -> %s ) )' % (PH1, HRx))
    hyp = w.s([ex3], 'ralrimiva', '( %s -> %s )' % (PH1, HYPJ))
    hypa = w.s([hyp], 'adantr', '( %s -> %s )' % (ph, HYPJ))
    # the empty-word members are classes of configurations
    u = ctx(w, ph, 'adantr')
    ww = w.s([], 'simprl', '( %s -> W e. Word B )' % ph)
    uu = w.s([], 'simprr', '( %s -> U e. Word B )' % ph)
    phs = '( %s /\\ s e. Word B )' % ph
    def B_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (phs, f))
    tvs = B_(u['tv'], 'T e. V'); als = B_(u['al'], 'A e. %s' % L('T'))
    dds = B_(u['dd'], 'D e. %s' % STK('T')); kks = B_(u['kk'], 'K e. %s' % DG)
    jjs = B_(u['jj'], 'J e. %s' % DG); hws = B_(u['hw'], 'H e. Word %s' % GJ)
    rws = B_(u['rw'], 'R e. Word %s' % GK); bjs = B_(u['bj'], 'B C_ %s' % GJ)
    sws2 = w.s([], 'simpr', '( %s -> s e. Word B )' % phs)
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0s = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % phs)
    jzs = jmov(w, phs, '(/)', 's', w0s, sws2)
    swj = w.s([bjs, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (phs, GJ))
    swg = w.s([swj, sws2], 'sseldd', '( %s -> s e. Word %s )' % (phs, GJ))
    z0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. Word %s )' % (phs, GK))
    zrw = w.s([z0a, rws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( (/) ++ R ) e. Word %s )' % (phs, GK))
    shw = w.s([swg, hws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( s ++ H ) e. Word %s )' % (phs, GJ))
    ups = upd2cl(w, phs, '( (/) ++ R )', '( s ++ H )', GK, GJ, tvs, dds, kks, jjs, zrw, shw)
    cls = clss(w, phs, '( (/) ++ R )', '( s ++ H )', tvs, als, ups)
    clj = w.s([jzs, cls], 'eqsstrd', '( %s -> ( %s ` <. (/) , s >. ) C_ %s )' % (phs, JMOV, CFG('T')))
    zc = w.s([clj], 'ralrimiva', '( %s -> %s )' % (ph, ZCJ))
    # tm2hwrd2
    n1 = w.s([], '1nn0', '1 e. NN0')
    n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([n1a, zc], 'jca', '( %s -> ( 1 e. NN0 /\\ %s ) )' % (ph, ZCJ))
    ant = w.s([u['phm'], pj, hypa], '3jca', '( %s -> ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) )'
              % (ph, PHM, ZCJ, HYPJ))
    xy = w.s([ww, uu], 'jca', '( %s -> ( W e. Word B /\\ U e. Word B ) )' % ph)
    ant2 = w.s([ant, xy], 'jca',
               '( %s -> ( ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) /\\ ( W e. Word B /\\ U e. Word B ) ) )'
               % (ph, PHM, ZCJ, HYPJ))
    RV = '( ( reverse ` W ) ++ U )'
    run = w.s([ant2, w.inst('tm2hwrd2')], 'syl', '( %s -> %s )'
              % (ph, HR('( %s ` <. W , U >. )' % JMOV, 'T', 'M',
                        '( %s ` <. (/) , %s >. )' % (JMOV, RV), '( ( # ` W ) x. 1 )')))
    # unfold the family and the bound
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    rvw = w.s([rvc, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, RV))
    w0b = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    jw = jmov(w, ph, 'W', 'U', ww, uu)
    jz = jmov(w, ph, '(/)', RV, w0b, rvw)
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    TGT0 = CL2('( (/) ++ R )', '( %s ++ H )' % RV)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` <. (/) , %s >. ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JMOV, RV, TGT0))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JMOV, 'T', 'M',
                       '( %s ` <. (/) , %s >. )' % (JMOV, RV), '( ( # ` W ) x. 1 )'),
                HR('( %s ` <. W , U >. )' % JMOV, 'T', 'M', TGT0, '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` <. W , U >. )' % JMOV, 'T', 'M', TGT0, '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JMOV, 'T', 'M', TGT0, '( # ` W )'),
                HR(CL2('( W ++ R )', '( U ++ H )'), 'T', 'M', TGT0, '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )'
          % (ph, HR(CL2('( W ++ R )', '( U ++ H )'), 'T', 'M', TGT0, '( # ` W )')))
    return w.run()


GE = GOTO(CONSTF('T', 'E'))
STM0 = POP('K', 'F', BRANCH('C', PU, GE))
RY = '( <" Y "> ++ X )'
HE = 'A. r e. %s -. ( C ` %s ) = 1o' % (S('T'), NVF('r', 'Y'))
LAB0 = '( ( A e. %s /\\ E e. %s ) /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )' % (L('T'), L('T'), DG, DG)
WTY0 = '( ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) /\\ D e. %s )' % (GK, GK, GJ, STK('T'))
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
    he = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, el=el, kk=kk, jj=jj, ne=ne, nes=nes, ra=ra, cc=cc, pp=pp,
                yy=yy, xx=xx, hw=hw, dd=dd, he=he, tv=tv)


def stmtty0(w, ph, u):
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], jp, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    j = w.s([pu, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, PU, STMT_T, GE, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, BRANCH('C', PU, GE), STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STM0, STMT_T))
    return dict(fa=fa, fe=fe, ga=ga, ge=ge, pu=pu, br=br, pop=po)


def tm2fmov0():
    lab = 'tm2fmov0'
    ph = PH0
    D1 = UPD2(RY, 'H')
    D2 = UPD2('X', 'H')
    DK1 = UPD('T', 'D', 'K', RY)
    NV = NVF('v', 'Y')
    w = W(lab, 'The exit step of the mover ` moveNum ` of TM/Arith.lean: the '
               'label pops the number\'s terminator, the branch on the internal '
               'state is false, and the machine jumps to the exit.  Lean: '
               '` moveNum_loop ` , the ` nil ` case.')
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
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG)
        ne = A_(u['ne'], 'K =/= J')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T'))
        hea = A_(u['he'], HE)
        ela = A_(u['el'], 'E e. %s' % L('T'))
        fe = A_(t['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        ga = A_(t['ga'], '%s e. %s' % (GA, STMT_T)); ge = A_(t['ge'], '%s e. %s' % (GE, STMT_T))
        pu = A_(t['pu'], '%s e. %s' % (PU, STMT_T))
        br = A_(t['br'], '%s e. %s' % (BRANCH('C', PU, GE), STMT_T))
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
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, RATY: ra, CTY: cc, PTY: pp,
                 '%s e. %s' % (BRANCH('C', PU, GE), STMT_T): br, '%s e. %s' % (PU, STMT_T): pu,
                 '%s e. %s' % (GA, STMT_T): ga, '%s e. %s' % (GE, STMT_T): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe}
        rules = {'( %s ` K )' % D1: (RY, rk),
                 '( %s ` 0 )' % RY: ('Y', rfv),
                 TL(RY): ('X', rtl),
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
        return fin, NV, nvcl
    hstepc(w, ph, 'T', 'M', 'A', 'E', D1, D2, (u['meq'], u['phm']), u['al'], u['el'],
           d1cl, d2cl, body, qed=True)
    return w.run()


WTYF = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
        % (GK, GJ, GK, GK, GJ, STK('T')))
PHF = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ %s ) ) )'
       % (PHM, STM0, LAB0, FTY, WTYF, HC, HE))


def tm2fmov():
    lab = 'tm2fmov'
    ph = '( %s /\\ W e. Word B )' % PHF
    RVW = '( reverse ` W )'
    RVH = '( %s ++ H )' % RVW
    w = W(lab, 'The mover ` moveNum ` of TM/Arith.lean: the label moves the '
               'whole number on stack ` K ` onto stack ` J ` , reversed, and '
               'pops its terminator, in ` ( # ` W ) + 1 ` steps --- Lean\'s '
               '` moveNum_runs ` bound ` l.length + 1 ` .  Two one-step lemmas, '
               '~ tm2hwrd2 and ~ tm2hseq .')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (PHF, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHF, STM0))
    lab2 = w.s([], 'simp2', '( %s -> %s )' % (PHF, LAB0))
    p3 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ ( %s /\\ %s ) ) )' % (PHF, FTY, WTYF, HC, HE))
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm, PHM); meq = A_(meq, '( M ` A ) = %s' % STM0)
    lab2 = A_(lab2, LAB0); p3 = A_(p3, '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (FTY, WTYF, HC, HE))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTYF))
    qt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, HC, HE))
    hc = w.s([qt], 'simpld', '( %s -> %s )' % (ph, HC))
    he = w.s([qt], 'simprd', '( %s -> %s )' % (ph, HE))
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ))
    bj = w.s([b2], 'simprd', '( %s -> B C_ %s )' % (ph, GJ))
    w3 = w.s([wt, w.inst('simp2')], 'syl', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) )'
             % (ph, GK, GK, GJ))
    yy = w.s([w3, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([w3, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    hw = w.s([w3, w.inst('simp3')], 'syl', '( %s -> H e. Word %s )' % (ph, GJ))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    al2 = w.s([lab2, w.inst('simp1')], 'syl', '( %s -> ( A e. %s /\\ E e. %s ) )' % (ph, L('T'), L('T')))
    al = w.s([al2], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([al2], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    kj2 = w.s([lab2, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s ) )' % (ph, DG, DG))
    ne = w.s([lab2, w.inst('simp3')], 'syl', '( %s -> K =/= J )' % ph)
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    # R := ( <" Y "> ++ X ) is a word
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    ryw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    # the loop, via tm2fmovw at R := ( <" Y "> ++ X ) , U := (/)
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    labm = w.s([al, kj2, ne], '3jca', '( %s -> %s )' % (ph, LAB))
    wtym = w.s([b2, w.s([ryw, hw], 'jca', '( %s -> ( %s e. Word %s /\\ H e. Word %s ) )' % (ph, RY, GK, GJ)), dd],
               '3jca', '( %s -> ( ( B C_ %s /\\ B C_ %s ) /\\ ( %s e. Word %s /\\ H e. Word %s ) /\\ D e. %s ) )'
               % (ph, GK, GJ, RY, GK, GJ, STK('T')))
    qtym = w.s([ge, hc], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (ph, GE, STMT_T, HC))
    pm1 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STM0))
    pm3 = w.s([ft, wtym, qtym], '3jca',
              '( %s -> ( %s /\\ ( ( B C_ %s /\\ B C_ %s ) /\\ ( %s e. Word %s /\\ H e. Word %s ) /\\ D e. %s ) '
              '/\\ ( %s e. %s /\\ %s ) ) )' % (ph, FTY, GK, GJ, RY, GK, GJ, STK('T'), GE, STMT_T, HC))
    PH1i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ ( ( B C_ %s /\\ B C_ %s ) /\\ '
            '( %s e. Word %s /\\ H e. Word %s ) /\\ D e. %s ) /\\ ( %s e. %s /\\ %s ) ) )'
            % (PHM, STM0, LAB, FTY, GK, GJ, RY, GK, GJ, STK('T'), GE, STMT_T, HC))
    pmi = w.s([pm1, labm, pm3], '3jca', '( %s -> %s )' % (ph, PH1i))
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    wu = w.s([ww, w0a], 'jca', '( %s -> ( W e. Word B /\\ (/) e. Word B ) )' % ph)
    ant = w.s([pmi, wu], 'jca', '( %s -> ( %s /\\ ( W e. Word B /\\ (/) e. Word B ) ) )' % (ph, PH1i))
    C0 = CL2('( W ++ %s )' % RY, '( (/) ++ H )')
    C1 = CL2('( (/) ++ %s )' % RY, '( ( %s ++ (/) ) ++ H )' % RVW)
    loop = w.s([ant, w.inst('tm2fmovw')], 'syl', '( %s -> %s )'
               % (ph, HR(C0, 'T', 'M', C1, '( # ` W )')))
    # normalise the two classes
    lid1 = w.s([hw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ H ) = H )' % ph)
    c1s, n1 = w.rewrite(C0, {'( (/) ++ H )': ('H', lid1)}, ph)
    assert n1 == CL2('( W ++ %s )' % RY, 'H'), n1
    lid2 = w.s([ryw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, RY, RY))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word B )' % (ph, RVW))
    rid = w.s([rvc, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, RVW, RVW))
    c2s, n2 = w.rewrite(C1, {'( (/) ++ %s )' % RY: (RY, lid2), '( %s ++ (/) )' % RVW: (RVW, rid)}, ph)
    assert n2 == CL2(RY, RVH), n2
    o1 = w.s([c2s], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )' % (ph, C1, CL2(RY, RVH)))
    b1 = w.s([c1s, o1], 'breq12d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(C0, 'T', 'M', C1, '( # ` W )'),
                HR(CL2('( W ++ %s )' % RY, 'H'), 'T', 'M', CL2(RY, RVH), '( # ` W )')))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )'
                % (ph, HR(CL2('( W ++ %s )' % RY, 'H'), 'T', 'M', CL2(RY, RVH), '( # ` W )')))
    # the exit step, via tm2fmov0 at H := ( ( reverse ` W ) ++ H )
    swj = w.s([bj, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GJ))
    rvg = w.s([swj, rvc], 'sseldd', '( %s -> %s e. Word %s )' % (ph, RVW, GJ))
    rvh = w.s([rvg, hw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RVH, GJ))
    wty0 = w.s([w.s([yy, xx, rvh], '3jca', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ %s e. Word %s ) )'
                     % (ph, GK, GK, RVH, GJ)), dd], 'jca',
               '( %s -> ( ( Y e. %s /\\ X e. Word %s /\\ %s e. Word %s ) /\\ D e. %s ) )'
               % (ph, GK, GK, RVH, GJ, STK('T')))
    p30 = w.s([ft, wty0, he], '3jca',
              '( %s -> ( %s /\\ ( ( Y e. %s /\\ X e. Word %s /\\ %s e. Word %s ) /\\ D e. %s ) /\\ %s ) )'
              % (ph, FTY, GK, GK, RVH, GJ, STK('T'), HE))
    PH0i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ ( ( Y e. %s /\\ X e. Word %s /\\ %s e. Word %s ) '
            '/\\ D e. %s ) /\\ %s ) )' % (PHM, STM0, LAB0, FTY, GK, GK, RVH, GJ, STK('T'), HE))
    p0i = w.s([pm1, lab2, p30], '3jca', '( %s -> %s )' % (ph, PH0i))
    exit_ = w.s([p0i, w.inst('tm2fmov0')], 'syl', '( %s -> %s )'
                % (ph, HR(CL2(RY, RVH), 'T', 'M', CL2E('X', RVH), '1')))
    w.qed([phm, loop2, exit_], 'syl3anc', '( %s -> %s )'
          % (ph, HR(CL2('( W ++ %s )' % RY, 'H'), 'T', 'M', CL2E('X', RVH), '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fmov1'): tm2fmov1()
    if want('tm2fmovw'): tm2fmovw()
    if want('tm2fmov0'): tm2fmov0()
    if want('tm2fmov'): tm2fmov()
