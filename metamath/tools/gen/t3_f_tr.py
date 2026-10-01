"""T3: the transducing mover --- a pop-branch-push scan loop whose pushed
letter is the image of the popped one under a letter map ` G ` .  ~ tm2fmvn is
the instance at ` G ` the identity and the carry chain of `incLoop` and the
borrow chain of `predLoop` (TM/Prims.lean) are the instances at ` G ` a
constant (blueprint 4.6, 4.7)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty, rfun, updn, upd2cl, OPT, RATY, CTY, PTY, DG, GK, GJ, ST, \
    STMT_T, TL, NVF, GA, UPD2

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GE = GOTO(CONSTF('T', 'E'))
PU = PUSH('J', 'P', GA)
BR = BRANCH('C', PU, 'Q')
STM = POP('K', 'F', BR)
GTY = 'G : B --> %s' % GJ
NSS = 'N C_ %s' % S('T')
TRIP = lambda r, z: ("( ( C ` %s ) = 1o /\\ ( P ` %s ) = ( G ` %s ) /\\ %s e. N )"
                     % (NVF(r, z), NVF(r, z), z, NVF(r, z)))
HC = 'A. r e. N A. z e. B %s' % TRIP('r', 'z')
LAB = '( A e. %s /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )' % (L('T'), DG, DG)
FTY = '( %s /\\ %s /\\ %s )' % (RATY, CTY, PTY)
WTY = ('( ( B C_ %s /\\ %s ) /\\ ( R e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
       % (GK, GTY, GK, GJ, STK('T')))
QTY = '( Q e. %s /\\ ( %s /\\ %s ) )' % (STMT_T, NSS, HC)
PH1 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM, LAB, FTY, WTY, QTY))
CO = lambda s: '( G o. %s )' % s


def CLT(X, Y, lb='A'):
    return '( { ( inl ` %s ) } X. ( N X. { %s } ) )' % (lb, UPD2('( %s ++ R )' % X, '( %s ++ H )' % CO(Y)))


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
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ %s ) )' % (ph, GK, GTY))
    bk = w.s([b2], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    gf = w.s([b2], 'simprd', '( %s -> %s )' % (ph, GTY))
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
                bk=bk, gf=gf, rw=rw, hw=hw, dd=dd, qq=qq, nss=nss, hc=hc, tv=tv)


def hcitr(w, av, vn, ZT, zcl, hca):
    """the interface at ( r := v , z := ZT )"""
    NV = NVF('v', ZT); NZ = NVF('v', 'z'); RZ = NVF('r', 'z')
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (RZ, NZ))
    i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (RZ, NZ))
    i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (RZ, NZ))
    i5 = w.s([i2], 'fveq2d', '( r = v -> ( P ` %s ) = ( P ` %s ) )' % (RZ, NZ))
    i6 = w.s([i5], 'eqeq1d', '( r = v -> ( ( P ` %s ) = ( G ` z ) <-> ( P ` %s ) = ( G ` z ) ) )' % (RZ, NZ))
    i7 = w.s([i2], 'eleq1d', '( r = v -> ( %s e. N <-> %s e. N ) )' % (RZ, NZ))
    i8 = w.s([i4, i6, i7], '3anbi123d', '( r = v -> ( %s <-> %s ) )' % (TRIP('r', 'z'), TRIP('v', 'z')))
    i9 = w.s([i8], 'ralbidv', '( r = v -> ( A. z e. B %s <-> A. z e. B %s ) )'
             % (TRIP('r', 'z'), TRIP('v', 'z')))
    h1 = w.s([i9, hca, vn], 'rspcdva', '( %s -> A. z e. B %s )' % (av, TRIP('v', 'z')))
    j1 = w.s([], 'fveq2', '( z = %s -> ( inl ` z ) = ( inl ` %s ) )' % (ZT, ZT))
    j2 = w.s([j1], 'opeq2d', '( z = %s -> <. v , ( inl ` z ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    j3 = w.s([j2], 'fveq2d', '( z = %s -> %s = %s )' % (ZT, NZ, NV))
    j4 = w.s([j3], 'fveq2d', '( z = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NZ, NV))
    j5 = w.s([j4], 'eqeq1d', '( z = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (ZT, NZ, NV))
    j6 = w.s([j3], 'fveq2d', '( z = %s -> ( P ` %s ) = ( P ` %s ) )' % (ZT, NZ, NV))
    jg = w.s([], 'fveq2', '( z = %s -> ( G ` z ) = ( G ` %s ) )' % (ZT, ZT))
    j7 = w.s([j6, jg], 'eqeq12d', '( z = %s -> ( ( P ` %s ) = ( G ` z ) <-> ( P ` %s ) = ( G ` %s ) ) )'
             % (ZT, NZ, NV, ZT))
    j8 = w.s([j3], 'eleq1d', '( z = %s -> ( %s e. N <-> %s e. N ) )' % (ZT, NZ, NV))
    j9 = w.s([j5, j7, j8], '3anbi123d', '( z = %s -> ( %s <-> %s ) )' % (ZT, TRIP('v', 'z'), TRIP('v', ZT)))
    h2 = w.s([j9, h1, zcl], 'rspcdva', '( %s -> %s )' % (av, TRIP('v', ZT)))
    bc = w.s([h2, w.inst('simp1')], 'syl', '( %s -> ( C ` %s ) = 1o )' % (av, NV))
    pv = w.s([h2, w.inst('simp2')], 'syl', '( %s -> ( P ` %s ) = ( G ` %s ) )' % (av, NV, ZT))
    nv = w.s([h2, w.inst('simp3')], 'syl', '( %s -> %s e. N )' % (av, NV))
    return bc, pv, nv


def tm2ftr1():
    lab = 'tm2ftr1'
    ph = '( ( %s /\\ ( x e. Word B /\\ s e. Word B ) ) /\\ x =/= (/) )' % PH1
    XR = '( x ++ R )'; X0 = '( x ` 0 )'
    GS = CO('s'); SH = '( %s ++ H )' % GS
    TXR = '( %s ++ R )' % TL('x')
    SACC = '( <" %s "> ++ s )' % X0
    GACC = CO(SACC)
    ACC = '( %s ++ H )' % GACC
    D1 = UPD2(XR, SH); D2 = UPD2(TXR, ACC)
    DK1 = UPD('T', 'D', 'K', XR); D2K = UPD('T', D1, 'K', TXR)
    NV = NVF('v', X0)
    GX0 = '( G ` %s )' % X0
    w = W(lab, 'One iteration of the transducing mover: the letter popped from '
               'stack ` K ` is pushed on stack ` J ` after the letter map ` G ` .  '
               'The destination therefore holds the image under ` G ` of the '
               'reversed word read so far.  At ` G ` the identity this is '
               '~ tm2fmvn1 ; at ` G ` a constant it is the carry chain of '
               '` incLoop ` and the borrow chain of ` predLoop ` .')
    u = ctx(w, ph, 'ad2antrr')
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], jp, ga, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    j = w.s([pu, u['qq']], 'jca', '( %s -> ( %s e. %s /\\ Q e. %s ) )' % (ph, PU, STMT_T, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR, STMT_T))
    xw = w.s([], 'simplrl', '( %s -> x e. Word B )' % ph)
    sw = w.s([], 'simplrr', '( %s -> s e. Word B )' % ph)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ph)
    swk = w.s([u['bk'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GK))
    xwg = w.s([swk, xw], 'sseldd', '( %s -> x e. Word %s )' % (ph, GK))
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ph, X0))
    x0k = w.s([u['bk'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GK))
    x0j = w.s([u['gf'], x0], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, GX0, GJ))
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ph, TL('x')))
    tlwg = w.s([swk, tlw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, TL('x'), GK))
    xrw = w.s([xwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, XR, GK))
    txrw = w.s([tlwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, TXR, GK))
    gsw = w.s([sw, u['gf'], w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, GS, GJ))
    shw = w.s([gsw, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, SH, GJ))
    s1cb = w.s([x0], 's1cld', '( %s -> <" %s "> e. Word B )' % (ph, X0))
    sacb = w.s([s1cb, sw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, SACC))
    gacw = w.s([sacb, u['gf'], w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, GACC, GJ))
    accw = w.s([gacw, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ACC, GJ))
    s1c = w.s([x0j], 's1cld', '( %s -> <" %s "> e. Word %s )' % (ph, GX0, GJ))
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
        faa = A_(fa, '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        gaa = A_(ga, '%s e. %s' % (GA, STMT_T)); pua = A_(pu, '%s e. %s' % (PU, STMT_T))
        bra = A_(br, '%s e. %s' % (BR, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        d2k = A_(d2kcl, '%s e. %s' % (D2K, STK('T'))); dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T')))
        xrwa = A_(xrw, '%s e. Word %s' % (XR, GK)); txrwa = A_(txrw, '%s e. Word %s' % (TXR, GK))
        shwa = A_(shw, '%s e. Word %s' % (SH, GJ)); accwa = A_(accw, '%s e. Word %s' % (ACC, GJ))
        xwga = A_(xwg, 'x e. Word %s' % GK); gswa = A_(gsw, '%s e. Word %s' % (GS, GJ))
        rwa = A_(u['rw'], 'R e. Word %s' % GK); hwa = A_(u['hw'], 'H e. Word %s' % GJ)
        xna = A_(xn, 'x =/= (/)'); x0b = A_(x0, '%s e. B' % X0)
        s1ca = A_(s1c, '<" %s "> e. Word %s' % (GX0, GJ))
        xrna = A_(xrn, '%s =/= (/)' % XR)
        swa = A_(sw, 's e. Word B'); s1cba = A_(s1cb, '<" %s "> e. Word B' % X0)
        gfa = A_(u['gf'], GTY)
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
        # ( G o. ( <" x0 "> ++ s ) ) = ( <" ( G ` x0 ) "> ++ ( G o. s ) )
        cco = w.s([s1cba, swa, gfa, w.inst('ccatco')], 'syl3anc',
                  '( %s -> %s = ( %s ++ %s ) )' % (av, GACC, CO('<" %s ">' % X0), GS))
        s1c2 = w.s([x0b, gfa, w.inst('s1co')], 'syl2anc',
                   '( %s -> %s = <" %s "> )' % (av, CO('<" %s ">' % X0), GX0))
        cco2 = w.s([s1c2], 'oveq1d', '( %s -> ( %s ++ %s ) = ( <" %s "> ++ %s ) )'
                   % (av, CO('<" %s ">' % X0), GS, GX0, GS))
        gacc = w.s([cco, cco2], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (av, GACC, GX0, GS))
        gacc1 = w.s([gacc], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ %s ) ++ H ) )' % (av, ACC, GX0, GS))
        as1 = w.s([s1ca, gswa, hwa, w.inst('ccatass')], 'syl3anc',
                  '( %s -> ( ( <" %s "> ++ %s ) ++ H ) = ( <" %s "> ++ %s ) )' % (av, GX0, GS, GX0, SH))
        gacc2 = w.s([gacc1, as1], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (av, ACC, GX0, SH))
        asc = w.s([gacc2], 'eqcomd', '( %s -> ( <" %s "> ++ %s ) = %s )' % (av, GX0, SH, ACC))
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
        bc, pv, nvn = hcitr(w, av, vn, X0, x0b, hca)
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        avv = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2K, STK('T')): d2k,
                 '%s e. %s' % (D2, STK('T')): d2, '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, RATY: ra, CTY: cc, PTY: pp,
                 '%s e. %s' % (BR, STMT_T): bra, '%s e. %s' % (PU, STMT_T): pua,
                 '%s e. %s' % (GA, STMT_T): gaa, 'Q e. %s' % STMT_T: qq,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): faa}
        rules = {'( %s ` K )' % D1: (XR, rk), '( %s ` J )' % D2K: (SH, rj),
                 '( %s ` 0 )' % XR: (X0, rfv), TL(XR): (TXR, rtl),
                 '( <" %s "> ++ %s )' % (GX0, SH): (ACC, asc),
                 '( P ` %s )' % NV: (GX0, pv),
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
    hstepc2(w, ph, 'T', 'M', 'A', 'A', 'N', 'N', D1, D2, (u['meq'], u['phm']),
            u['al'], u['al'], u['nss'], u['nss'], d1cl, d2cl, body, qed=True)
    return w.run()



JTR = ('( p e. _V |-> ( { ( inl ` A ) } X. ( N X. { %s } ) ) )'
       % UPD2('( ( 1st ` p ) ++ R )', '( %s ++ H )' % CO('( 2nd ` p )')))


def jtr(w, ante, U, WW, ucl, wcl, nex, gf):
    """( ante -> ( JTR ` <. U , WW >. ) = CLT(U, WW) )"""
    aq = '( %s /\\ p = <. %s , %s >. )' % (ante, U, WW)
    lp = w.s([], 'simpr', '( %s -> p = <. %s , %s >. )' % (aq, U, WW))
    body = ('( { ( inl ` A ) } X. ( N X. { %s } ) )'
            % UPD2('( ( 1st ` p ) ++ R )', '( %s ++ H )' % CO('( 2nd ` p )')))
    st, mid = W.congr(w, body, {'p': '<. %s , %s >.' % (U, WW)}, aq, {'p': lp})
    uv = w.s([ucl], 'elexd', '( %s -> %s e. _V )' % (ante, U))
    wv = w.s([wcl], 'elexd', '( %s -> %s e. _V )' % (ante, WW))
    uva = w.s([uv], 'adantr', '( %s -> %s e. _V )' % (aq, U))
    wva = w.s([wv], 'adantr', '( %s -> %s e. _V )' % (aq, WW))
    p1 = w.s([uva, wva, w.inst('op1stg')], 'syl2anc',
             '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (aq, U, WW, U))
    p2 = w.s([uva, wva, w.inst('op2ndg')], 'syl2anc',
             '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (aq, U, WW, WW))
    ev, res = W.congr(w, mid, {}, aq, {},
                      rules={'( 1st ` <. %s , %s >. )' % (U, WW): (U, p1),
                             '( 2nd ` <. %s , %s >. )' % (U, WW): (WW, p2)})
    tgt = CLT(U, WW)
    assert res == tgt, res
    h2 = w.s([st, ev], 'eqtrd', '( %s -> %s = %s )' % (aq, body, tgt))
    eqi = w.s([], 'eqid', '%s = %s' % (JTR, JTR))
    opv = w.s([], 'opex', '<. %s , %s >. e. _V' % (U, WW))
    opva = w.s([opv], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (ante, U, WW))
    sn1 = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    sn1a = w.s([sn1], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ante)
    UPS = UPD2('( %s ++ R )' % U, '( %s ++ H )' % CO(WW))
    sn2 = w.s([], 'snex', '{ %s } e. _V' % UPS)
    sn2a = w.s([sn2], 'a1i', '( %s -> { %s } e. _V )' % (ante, UPS))
    xp1 = w.s([nex, sn2a, w.inst('xpexg')], 'syl2anc',
              '( %s -> ( N X. { %s } ) e. _V )' % (ante, UPS))
    cex = w.s([sn1a, xp1, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ante, tgt))
    return w.s([h2, eqi, opva, cex], 'fvmptd2',
               '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, JTR, U, WW, tgt))


def tm2ftrw():
    lab = 'tm2ftrw'
    ph = '( %s /\\ ( W e. Word B /\\ U e. Word B ) )' % PH1
    phx = '( %s /\\ ( x e. Word B /\\ s e. Word B ) )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    X0 = '( x ` 0 )'
    ACCx = '( <" %s "> ++ s )' % X0
    HRx = HR('( %s ` <. x , s >. )' % JTR, 'T', 'M',
             '( %s ` <. %s , %s >. )' % (JTR, TL('x'), ACCx), '1')
    HYPJ = 'A. x e. Word B A. s e. Word B ( x =/= (/) -> %s )' % HRx
    ZCJ = 'A. s e. Word B ( %s ` <. (/) , s >. ) C_ %s' % (JTR, CFG('T'))
    CLx = CLT('x', 's')
    CLt = CLT(TL('x'), ACCx)
    w = W(lab, 'The scan loop of the transducing mover: an instantiation of '
               '~ tm2hwrd2 whose invariant carries the image of the accumulated '
               'word under the letter map ` G ` (set.mm writes a word map as a '
               'composition, so ` ( G o. s ) ` is the pushed word and '
               '~ ccatco , ~ s1co , ~ revco are its algebra).')
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ante2, PH1))
    xw1 = w.s([], 'simplrl', '( %s -> x e. Word B )' % ante2)
    sw1 = w.s([], 'simplrr', '( %s -> s e. Word B )' % ante2)
    xn1 = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    one = w.s([], 'tm2ftr1', '( %s -> %s )' % (ante2, HR(CLx, 'T', 'M', CLt, '1')))
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    x01 = w.s([xw1, xn1, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ante2, X0))
    s1c1 = w.s([x01], 's1cld', '( %s -> <" %s "> e. Word B )' % (ante2, X0))
    acw1 = w.s([s1c1, sw1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ante2, ACCx))
    u2 = ctx(w, ante2, 'ad2antrr')
    sev2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    sev2a = w.s([sev2], 'a1i', '( %s -> %s e. _V )' % (ante2, S('T')))
    nex2 = w.s([u2['nss'], sev2a, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ante2)
    jx = jtr(w, ante2, 'x', 's', xw1, sw1, nex2, u2['gf'])
    jt = jtr(w, ante2, TL('x'), ACCx, tlw1, acw1, nex2, u2['gf'])
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` <. %s , %s >. ) , 1 >. = <. %s , 1 >. )'
             % (ante2, JTR, TL('x'), ACCx, CLt))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JTR, TL('x'), ACCx), '1'),
                HR(CLx, 'T', 'M', CLt, '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JTR, TL('x'), ACCx), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JTR, TL('x'), ACCx), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    ex2 = w.s([ex1], 'anassrs',
              '( ( ( %s /\\ x e. Word B ) /\\ s e. Word B ) -> ( x =/= (/) -> %s ) )' % (PH1, HRx))
    ex3 = w.s([ex2], 'ralrimiva',
              '( ( %s /\\ x e. Word B ) -> A. s e. Word B ( x =/= (/) -> %s ) )' % (PH1, HRx))
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
    rws = B_(u['rw'], 'R e. Word %s' % GK); gfs = B_(u['gf'], GTY)
    nsss = B_(u['nss'], NSS)
    sws2 = w.s([], 'simpr', '( %s -> s e. Word B )' % phs)
    sevs = w.s([], 'fvex', '%s e. _V' % S('T'))
    sevsa = w.s([sevs], 'a1i', '( %s -> %s e. _V )' % (phs, S('T')))
    nexs = w.s([nsss, sevsa, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % phs)
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0s = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % phs)
    jzs2 = jtr(w, phs, '(/)', 's', w0s, sws2, nexs, gfs)
    gsws = w.s([sws2, gfs, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (phs, CO('s'), GJ))
    z0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. Word %s )' % (phs, GK))
    zrw = w.s([z0a, rws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( (/) ++ R ) e. Word %s )' % (phs, GK))
    shw = w.s([gsws, hws, w.inst('ccatcl')], 'syl2anc',
              '( %s -> ( %s ++ H ) e. Word %s )' % (phs, CO('s'), GJ))
    ups = upd2cl(w, phs, '( (/) ++ R )', '( %s ++ H )' % CO('s'), GK, GJ, tvs, dds, kks, jjs, zrw, shw)
    UPS = UPD2('( (/) ++ R )', '( %s ++ H )' % CO('s'))
    sn = w.s([ups], 'snssd', '( %s -> { %s } C_ %s )' % (phs, UPS, STK('T')))
    xs = w.s([nsss, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( N X. { %s } ) C_ %s )' % (phs, UPS, ST))
    cls = w.s([tvs, als, xs, w.inst('tm2hcfgss')], 'syl3anc',
              '( %s -> %s C_ %s )' % (phs, CLT('(/)', 's'), CFG('T')))
    clj = w.s([jzs2, cls], 'eqsstrd', '( %s -> ( %s ` <. (/) , s >. ) C_ %s )' % (phs, JTR, CFG('T')))
    zc = w.s([clj], 'ralrimiva', '( %s -> %s )' % (ph, ZCJ))
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
              % (ph, HR('( %s ` <. W , U >. )' % JTR, 'T', 'M',
                        '( %s ` <. (/) , %s >. )' % (JTR, RV), '( ( # ` W ) x. 1 )')))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    rvw = w.s([rvc, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, RV))
    w0b = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    sevp = w.s([], 'fvex', '%s e. _V' % S('T'))
    sevpa = w.s([sevp], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    nexp = w.s([u['nss'], sevpa, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ph)
    jw = jtr(w, ph, 'W', 'U', ww, uu, nexp, u['gf'])
    jz = jtr(w, ph, '(/)', RV, w0b, rvw, nexp, u['gf'])
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    TGT0 = CLT('(/)', RV)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` <. (/) , %s >. ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JTR, RV, TGT0))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JTR, 'T', 'M',
                       '( %s ` <. (/) , %s >. )' % (JTR, RV), '( ( # ` W ) x. 1 )'),
                HR('( %s ` <. W , U >. )' % JTR, 'T', 'M', TGT0, '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` <. W , U >. )' % JTR, 'T', 'M', TGT0, '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JTR, 'T', 'M', TGT0, '( # ` W )'),
                HR(CLT('W', 'U'), 'T', 'M', TGT0, '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )'
          % (ph, HR(CLT('W', 'U'), 'T', 'M', TGT0, '( # ` W )')))
    return w.run()



HE = ('A. m e. N ( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NVF('m', 'Y'), NVF('m', 'Y')))
BR0 = BRANCH('C', PU, GE)
STM0 = POP('K', 'F', BR0)
LAB0 = ('( ( A e. %s /\\ E e. %s ) /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )'
        % (L('T'), L('T'), DG, DG))
WTYF = ('( ( B C_ %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
        % (GK, GTY, GK, GK, GJ, STK('T')))
QTYF = '( %s /\\ ( %s /\\ %s ) )' % (NSS, HC, HE)
PHF = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM0, LAB0, FTY, WTYF, QTYF))


def tm2ftr():
    lab = 'tm2ftr'
    ph = '( %s /\\ W e. Word B )' % PHF
    ZXY = '( <" Y "> ++ X )'
    GW = CO('W')
    RGW = '( reverse ` %s )' % GW
    RGWH = '( %s ++ H )' % RGW
    w = W(lab, 'The transducing mover: the top number of stack ` K ` is moved '
               'onto stack ` J ` reversed and letterwise mapped by ` G ` , and '
               'the terminator ` Y ` is consumed.  At ` G ` the identity this is '
               '~ tm2fmvn (Lean\'s ` moveNum_runs\' ` ); at ` G ` the constant '
               'map it is the carry chain of ` incLoop ` (Lean\'s '
               '` incLoop_loop ` , which turns a run of ones into a run of '
               'zeros) and the borrow chain of ` predLoop ` .')
    phm0 = w.s([], 'simp1l', '( %s -> %s )' % (PHF, PHM))
    meq0 = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHF, STM0))
    lab0 = w.s([], 'simp2', '( %s -> %s )' % (PHF, LAB0))
    p30 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ %s ) )' % (PHF, FTY, WTYF, QTYF))
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm0, PHM); meq = A_(meq0, '( M ` A ) = %s' % STM0)
    lab2 = A_(lab0, LAB0); p3 = A_(p30, '( %s /\\ %s /\\ %s )' % (FTY, WTYF, QTYF))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    ra = w.s([ft, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([ft, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    pp = w.s([ft, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTYF))
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ %s ) )' % (ph, GK, GTY))
    bk = w.s([b2], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    gf = w.s([b2], 'simprd', '( %s -> %s )' % (ph, GTY))
    w3 = w.s([wt, w.inst('simp2')], 'syl',
             '( %s -> ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) )' % (ph, GK, GK, GJ))
    yy = w.s([w3, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([w3, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    hw = w.s([w3, w.inst('simp3')], 'syl', '( %s -> H e. Word %s )' % (ph, GJ))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    qt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, QTYF))
    nss = w.s([qt], 'simpld', '( %s -> %s )' % (ph, NSS))
    ce = w.s([qt], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, HC, HE))
    hc = w.s([ce], 'simpld', '( %s -> %s )' % (ph, HC))
    he = w.s([ce], 'simprd', '( %s -> %s )' % (ph, HE))
    ae = w.s([lab2, w.inst('simp1')], 'syl', '( %s -> ( A e. %s /\\ E e. %s ) )' % (ph, L('T'), L('T')))
    al = w.s([ae], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([ae], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    kj2 = w.s([lab2, w.inst('simp2')], 'syl', '( %s -> ( K e. %s /\\ J e. %s ) )' % (ph, DG, DG))
    kk = w.s([kj2], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([kj2], 'simprd', '( %s -> J e. %s )' % (ph, DG))
    ne = w.s([lab2, w.inst('simp3')], 'syl', '( %s -> K =/= J )' % ph)
    nes = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    zxw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZXY, GK))
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    # ---- the loop at R := ( <" Y "> ++ X ) , Q := goto E , U := (/)
    labm = w.s([al, kj2, ne], '3jca', '( %s -> %s )' % (ph, LAB))
    WTYi = ('( ( B C_ %s /\\ %s ) /\\ ( %s e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
            % (GK, GTY, ZXY, GK, GJ, STK('T')))
    wtym = w.s([b2, w.s([zxw, hw], 'jca', '( %s -> ( %s e. Word %s /\\ H e. Word %s ) )'
                        % (ph, ZXY, GK, GJ)), dd], '3jca', '( %s -> %s )' % (ph, WTYi))
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
    CL0 = ('( { ( inl ` A ) } X. ( N X. { %s } ) )'
           % UPD2('( W ++ %s )' % ZXY, '( %s ++ H )' % CO('(/)')))
    RV0 = '( ( reverse ` W ) ++ (/) )'
    CL1 = ('( { ( inl ` A ) } X. ( N X. { %s } ) )'
           % UPD2('( (/) ++ %s )' % ZXY, '( %s ++ H )' % CO(RV0)))
    loop = w.s([ant, w.inst('tm2ftrw')], 'syl', '( %s -> %s )' % (ph, HR(CL0, 'T', 'M', CL1, '( # ` W )')))
    # ---- the two classes in their reduced form
    co0 = w.s([], 'co02', '%s = (/)' % CO('(/)'))
    co0a = w.s([co0], 'a1i', '( %s -> %s = (/) )' % (ph, CO('(/)')))
    cs1, m1t = w.rewrite(CL0, {CO('(/)'): ('(/)', co0a)}, ph)
    lidh = w.s([hw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ H ) = H )' % ph)
    cs2, m2t = w.rewrite(m1t, {'( (/) ++ H )': ('H', lidh)}, ph)
    PRE = '( { ( inl ` A ) } X. ( N X. { %s } ) )' % UPD2('( W ++ %s )' % ZXY, 'H')
    assert m2t == PRE, m2t
    cs = w.s([cs1, cs2], 'eqtrd', '( %s -> %s = %s )' % (ph, CL0, PRE))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    ridw = w.s([rvc, w.inst('ccatrid')], 'syl', '( %s -> %s = ( reverse ` W ) )' % (ph, RV0))
    d1, t1 = w.rewrite(CL1, {RV0: ('( reverse ` W )', ridw)}, ph)
    rvco = w.s([ww, gf, w.inst('revco')], 'syl2anc',
               '( %s -> %s = %s )' % (ph, CO('( reverse ` W )'), RGW))
    lidz = w.s([zxw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, ZXY, ZXY))
    d2, t2 = w.rewrite(t1, {CO('( reverse ` W )'): (RGW, rvco), '( (/) ++ %s )' % ZXY: (ZXY, lidz)}, ph)
    DST = UPD2(ZXY, RGWH)
    MID = '( { ( inl ` A ) } X. ( N X. { %s } ) )' % DST
    assert t2 == MID, t2
    ds = w.s([d1, d2], 'eqtrd', '( %s -> %s = %s )' % (ph, CL1, MID))
    b1 = w.s([cs, w.s([ds], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )' % (ph, CL1, MID))],
             'breq12d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CL0, 'T', 'M', CL1, '( # ` W )'), HR(PRE, 'T', 'M', MID, '( # ` W )')))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )' % (ph, HR(PRE, 'T', 'M', MID, '( # ` W )')))
    # ---- the exit, by tm2fpb0
    gww = w.s([ww, gf, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, GW, GJ))
    rgw = w.s([gww, w.inst('revcl')], 'syl', '( %s -> %s e. Word %s )' % (ph, RGW, GJ))
    rgwh = w.s([rgw, hw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RGWH, GJ))
    dstcl = upd2cl(w, ph, ZXY, RGWH, GK, GJ, tv, dd, kk, jj, zxw, rgwh)
    DK1 = UPD('T', 'D', 'K', ZXY)
    k1 = w.s([kk, zxw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, ZXY, GK))
    dk1 = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DK1, STK('T')))
    a1 = updn(w, ph, DK1, 'J', RGWH, 'Word %s' % GJ, 'K', tv, dk1, jj, rgwh, kk, ne)
    zxv = w.s([zxw], 'elexd', '( %s -> %s e. _V )' % (ph, ZXY))
    a2 = updkval(w, ph, 'T', 'D', 'K', ZXY, tv, dd, kk, zxv)
    dstk = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, DST, ZXY))
    fa0 = constfty(w, ph, 'A', L('T'), al)
    ga0 = w.s([tv, fa0, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    jp0 = w.s([jj, pp], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu0 = w.s([tv, jp0, ga0, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    lb0 = w.s([al, el, kk], '3jca', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )'
              % (ph, L('T'), L('T'), DG))
    ft0 = w.s([ra, cc, pu0], '3jca', '( %s -> ( %s /\\ %s /\\ %s e. %s ) )' % (ph, RATY, CTY, PU, STMT_T))
    l2 = w.s([lb0, ft0], 'jca',
             '( %s -> ( ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s /\\ %s e. %s ) ) )'
             % (ph, L('T'), L('T'), DG, RATY, CTY, PU, STMT_T))
    yx0 = w.s([yy, xx], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (ph, GK, GK))
    d30 = w.s([dstcl, dstk, yx0], '3jca',
              '( %s -> ( %s e. %s /\\ ( %s ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) )'
              % (ph, DST, STK('T'), DST, ZXY, GK, GK))
    nh0 = w.s([nss, he], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HE))
    s30 = w.s([d30, nh0], 'jca',
              '( %s -> ( ( %s e. %s /\\ ( %s ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) /\\ ( %s /\\ %s ) ) )'
              % (ph, DST, STK('T'), DST, ZXY, GK, GK, NSS, HE))
    ant0 = w.s([pm1, l2, s30], '3jca', '( %s -> ( ( %s /\\ ( M ` A ) = %s ) /\\ '
               '( ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s /\\ %s e. %s ) ) /\\ '
               '( ( %s e. %s /\\ ( %s ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) /\\ ( %s /\\ %s ) ) ) )'
               % (ph, PHM, STM0, L('T'), L('T'), DG, RATY, CTY, PU, STMT_T,
                  DST, STK('T'), DST, ZXY, GK, GK, NSS, HE))
    CLE = '( { ( inl ` E ) } X. ( N X. { %s } ) )' % UPD('T', DST, 'K', 'X')
    exit_ = w.s([ant0, w.inst('tm2fpb0')], 'syl', '( %s -> %s )' % (ph, HR(MID, 'T', 'M', CLE, '1')))
    tdj = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK('T'))), ne],
              'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (ph, STK('T')))
    pk2 = w.s([kk, w.s([zxw, xx], 'jca', '( %s -> ( %s e. Word %s /\\ X e. Word %s ) )'
                       % (ph, ZXY, GK, GK))], 'jca',
              '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ X e. Word %s ) ) )' % (ph, DG, ZXY, GK, GK))
    pj1 = w.s([jj, rgwh], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, RGWH, GJ))
    up3 = w.s([tdj, pk2, pj1, w.inst('tm2stkup3')], 'syl3anc',
              '( %s -> %s = %s )' % (ph, UPD('T', DST, 'K', 'X'), UPD2('X', RGWH)))
    CLE2 = '( { ( inl ` E ) } X. ( N X. { %s } ) )' % UPD2('X', RGWH)
    cs3, n2 = w.rewrite(CLE, {UPD('T', DST, 'K', 'X'): (UPD2('X', RGWH), up3)}, ph)
    assert n2 == CLE2, n2
    o2 = w.s([cs3], 'opeq1d', '( %s -> <. %s , 1 >. = <. %s , 1 >. )' % (ph, CLE, CLE2))
    b2b = w.s([o2], 'breq2d', '( %s -> ( %s <-> %s ) )'
              % (ph, HR(MID, 'T', 'M', CLE, '1'), HR(MID, 'T', 'M', CLE2, '1')))
    exit2 = w.s([b2b, exit_], 'mpbid', '( %s -> %s )' % (ph, HR(MID, 'T', 'M', CLE2, '1')))
    w.qed([phm, loop2, exit2], 'syl3anc', '( %s -> %s )'
          % (ph, HR(PRE, 'T', 'M', CLE2, '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2ftr1'): tm2ftr1()
    if want('tm2ftrw'): tm2ftrw()
    if want('tm2ftr'): tm2ftr()
