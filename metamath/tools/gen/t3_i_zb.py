"""T3: `zeroIfBorrow` of TM/Sub.lean (blueprint 4.5) --- a guarded dropping
scan: if the borrow flag is set the just-written difference is popped back to
its terminator, which is then pushed again with the flag cleared."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty, rfun, OPT, RATY, CTY, DG, GK, STMT_T, NVF, TL

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GA = GOTO(CONSTF('T', 'A'))
GE = GOTO(CONSTF('T', 'E'))
CTY2 = "C' e. ( 2o ^m %s )" % S('T')
PKTY = 'P e. ( %s ^m %s )' % (GK, S('T'))
LTY = "F' e. ( %s ^m %s )" % (S('T'), S('T'))
NSS = 'N C_ %s' % S('T')
YX = '( <" Y "> ++ X )'
YPX = "( <\" Y' \"> ++ X )"

# --- the continue step: the guard passes, a letter is popped and dropped
BRC = BRANCH('C', GA, 'Q')
STM1 = BRANCH("C'", POP('K', 'F', BRC), "Q'")
HC1 = ("A. r e. N A. z e. B ( ( C' ` r ) = 1o /\\ ( C ` %s ) = 1o /\\ %s e. N )"
       % (NVF('r', 'z'), NVF('r', 'z')))
LAB1 = '( A e. %s /\\ K e. %s )' % (L('T'), DG)
FTY1 = '( ( %s /\\ %s /\\ %s ) /\\ ( Q e. %s /\\ Q\' e. %s ) )' % (RATY, CTY, CTY2, STMT_T, STMT_T)
WTY1 = '( ( B C_ %s /\\ R e. Word %s ) /\\ D e. %s )' % (GK, GK, STK('T'))
PH1 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )'
       % (PHM, STM1, LAB1, FTY1, WTY1, NSS, HC1))


def ctx1(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH1, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1l', PHM)
    meq = g('simp1r', '( M ` A ) = %s' % STM1)
    lab = g('simp2l', LAB1)
    ft = g('simp2r', FTY1)
    wt = g('simp3l', WTY1)
    nh = g('simp3r', '( %s /\\ %s )' % (NSS, HC1))
    al = w.s([lab], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
    kk = w.s([lab], 'simprd', '( %s -> K e. %s )' % (ph, DG))
    f3 = w.s([ft], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RATY, CTY, CTY2))
    ra = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, CTY2))
    qs = w.s([ft], 'simprd', "( %s -> ( Q e. %s /\\ Q' e. %s ) )" % (ph, STMT_T, STMT_T))
    qq = w.s([qs], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    q2 = w.s([qs], 'simprd', "( %s -> Q' e. %s )" % (ph, STMT_T))
    b2 = w.s([wt], 'simpld', '( %s -> ( B C_ %s /\\ R e. Word %s ) )' % (ph, GK, GK))
    bk = w.s([b2], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    rw = w.s([b2], 'simprd', '( %s -> R e. Word %s )' % (ph, GK))
    dd = w.s([wt], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    hc = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HC1))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, kk=kk, ra=ra, cc=cc, c2=c2, qq=qq, q2=q2,
                bk=bk, rw=rw, dd=dd, nss=nss, hc=hc, tv=tv)


def hc1at(w, av, vn, ZT, zcl, hca):
    TRIP = lambda r, z: ("( ( C' ` %s ) = 1o /\\ ( C ` %s ) = 1o /\\ %s e. N )"
                         % (r, NVF(r, z), NVF(r, z)))
    NV = NVF('v', ZT); NZ = NVF('v', 'z'); RZ = NVF('r', 'z')
    i0 = w.s([], 'fveq2', "( r = v -> ( C' ` r ) = ( C' ` v ) )")
    i0b = w.s([i0], 'eqeq1d', "( r = v -> ( ( C' ` r ) = 1o <-> ( C' ` v ) = 1o ) )")
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (RZ, NZ))
    i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (RZ, NZ))
    i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (RZ, NZ))
    i7 = w.s([i2], 'eleq1d', '( r = v -> ( %s e. N <-> %s e. N ) )' % (RZ, NZ))
    i8 = w.s([i0b, i4, i7], '3anbi123d', '( r = v -> ( %s <-> %s ) )' % (TRIP('r', 'z'), TRIP('v', 'z')))
    i9 = w.s([i8], 'ralbidv', '( r = v -> ( A. z e. B %s <-> A. z e. B %s ) )'
             % (TRIP('r', 'z'), TRIP('v', 'z')))
    h1 = w.s([i9, hca, vn], 'rspcdva', '( %s -> A. z e. B %s )' % (av, TRIP('v', 'z')))
    j1 = w.s([], 'fveq2', '( z = %s -> ( inl ` z ) = ( inl ` %s ) )' % (ZT, ZT))
    j2 = w.s([j1], 'opeq2d', '( z = %s -> <. v , ( inl ` z ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    j3 = w.s([j2], 'fveq2d', '( z = %s -> %s = %s )' % (ZT, NZ, NV))
    j4 = w.s([j3], 'fveq2d', '( z = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NZ, NV))
    j5 = w.s([j4], 'eqeq1d', '( z = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (ZT, NZ, NV))
    j8 = w.s([j3], 'eleq1d', '( z = %s -> ( %s e. N <-> %s e. N ) )' % (ZT, NZ, NV))
    jid = w.s([], 'biidd', "( z = %s -> ( ( C' ` v ) = 1o <-> ( C' ` v ) = 1o ) )" % ZT)
    j9 = w.s([jid, j5, j8], '3anbi123d', '( z = %s -> ( %s <-> %s ) )' % (ZT, TRIP('v', 'z'), TRIP('v', ZT)))
    h2 = w.s([j9, h1, zcl], 'rspcdva', '( %s -> %s )' % (av, TRIP('v', ZT)))
    gd = w.s([h2, w.inst('simp1')], 'syl', "( %s -> ( C' ` v ) = 1o )" % av)
    bc = w.s([h2, w.inst('simp2')], 'syl', '( %s -> ( C ` %s ) = 1o )' % (av, NV))
    nv = w.s([h2, w.inst('simp3')], 'syl', '( %s -> %s e. N )' % (av, NV))
    return gd, bc, nv


def tm2fzb1():
    lab = 'tm2fzb1'
    ph = '( ( %s /\\ x e. Word B ) /\\ x =/= (/) )' % PH1
    XR = '( x ++ R )'; X0 = '( x ` 0 )'; TXR = '( %s ++ R )' % TL('x')
    D1 = UPD('T', 'D', 'K', XR); D2 = UPD('T', 'D', 'K', TXR)
    NV = NVF('v', X0)
    w = W(lab, 'One iteration of a guarded dropping scan: the guard ` C\' ` holds, '
               'a letter of the continue alphabet is popped from stack ` K ` and '
               'discarded, and the machine loops.  Lean: ` zeroIfBorrow_loop ` , '
               'the ` cons ` case.  The exit branch ` Q ` and the branch ` Q\' ` '
               'taken when the guard fails are class variables.')
    u = ctx1(w, ph, 'ad2antrr')
    xw = w.s([], 'simplr', '( %s -> x e. Word B )' % ph)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ph)
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    gq = w.s([ga, u['qq']], 'jca', '( %s -> ( %s e. %s /\\ Q e. %s ) )' % (ph, GA, STMT_T, STMT_T))
    brc = w.s([u['tv'], u['cc'], gq, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BRC, STMT_T))
    kf = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([u['tv'], kf, brc, w.inst('tm2pop')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, POP('K', 'F', BRC), STMT_T))
    swk = w.s([u['bk'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GK))
    xwg = w.s([swk, xw], 'sseldd', '( %s -> x e. Word %s )' % (ph, GK))
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ph, X0))
    x0k = w.s([u['bk'], x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GK))
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ph, TL('x')))
    tlwg = w.s([swk, tlw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, TL('x'), GK))
    xrw = w.s([xwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, XR, GK))
    txrw = w.s([tlwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, TXR, GK))
    xrn = w.s([xwg, xn, u['rw'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, XR))
    k1 = w.s([u['kk'], xrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, XR, GK))
    k2 = w.s([u['kk'], txrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, TXR, GK))
    d1cl = w.s([u['tv'], u['dd'], k1, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, D1, STK('T')))
    d2cl = w.s([u['tv'], u['dd'], k2, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, D2, STK('T')))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = A_(u['nss'], NSS)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        kka = A_(u['kk'], 'K e. %s' % DG); raa = A_(u['ra'], RATY)
        cca = A_(u['cc'], CTY); c2a = A_(u['c2'], CTY2)
        qqa = A_(u['qq'], 'Q e. %s' % STMT_T); q2a = A_(u['q2'], "Q' e. %s" % STMT_T)
        dda = A_(u['dd'], 'D e. %s' % STK('T')); hca = A_(u['hc'], HC1)
        ala = A_(u['al'], 'A e. %s' % L('T'))
        faa = A_(fa, '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        gaa = A_(ga, '%s e. %s' % (GA, STMT_T)); brca = A_(brc, '%s e. %s' % (BRC, STMT_T))
        poa = A_(po, '%s e. %s' % (POP('K', 'F', BRC), STMT_T))
        d1a = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        xrwa = A_(xrw, '%s e. Word %s' % (XR, GK)); txrwa = A_(txrw, '%s e. Word %s' % (TXR, GK))
        xwga = A_(xwg, 'x e. Word %s' % GK); rwa = A_(u['rw'], 'R e. Word %s' % GK)
        xna = A_(xn, 'x =/= (/)'); x0b = A_(x0, '%s e. B' % X0)
        xrna = A_(xrn, '%s =/= (/)' % XR)
        gd, bc, nvn = hc1at(w, av, vn, X0, x0b, hca)
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        xrv = w.s([xrwa], 'elexd', '( %s -> %s e. _V )' % (av, XR))
        d1k = updkval(w, av, 'T', 'D', 'K', XR, tv, dda, kka, xrv)
        xnn = w.s([xrna], 'neneqd', '( %s -> -. %s = (/) )' % (av, XR))
        nnx = w.s([xwga, xna, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` x ) e. NN )' % av)
        xpos = w.s([nnx, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` x ) )' % av)
        rfv = w.s([xwga, rwa, xpos, w.inst('ccatfv0')], 'syl3anc',
                  '( %s -> ( %s ` 0 ) = %s )' % (av, XR, X0))
        rtl = w.s([xwga, xna, rwa, w.inst('wrdtlcc')], 'syl3anc', '( %s -> %s = %s )' % (av, TL(XR), TXR))
        tdk = w.s([tv, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        k2b = w.s([xrwa, txrwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                  % (av, XR, GK, TXR, GK))
        up2 = w.s([tdk, kka, k2b, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', TXR), D2))
        avv = w.s([ala], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '%s e. %s' % (NV, S('T')): nvcl,
                 '%s e. %s' % (D1, STK('T')): d1a, '%s e. %s' % (D2, STK('T')): d2a,
                 'K e. %s' % DG: kka, RATY: raa, CTY: cca, CTY2: c2a,
                 'Q e. %s' % STMT_T: qqa, "Q' e. %s" % STMT_T: q2a,
                 '%s e. %s' % (BRC, STMT_T): brca, '%s e. %s' % (GA, STMT_T): gaa,
                 '%s e. %s' % (POP('K', 'F', BRC), STMT_T): poa,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): faa}
        rules = {'( %s ` K )' % D1: (XR, d1k), '( %s ` 0 )' % XR: (X0, rfv),
                 TL(XR): (TXR, rtl), UPD('T', D1, 'K', TXR): (D2, up2),
                 '( %s ` %s )' % (CONSTF('T', 'A'), NV): ('A', rga)}
        ifr = {'%s = (/)' % XR: (False, xnn), '( C ` %s ) = 1o' % NV: (True, bc),
               "( C' ` v ) = 1o": (True, gd)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM1, '<. v , %s >.' % D1)
        wr = '<. ( inl ` A ) , <. %s , %s >. >.' % (NV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM1)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), D1, STM1, SA('T'), D1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), D1, res))
        return fin, NV, nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'A', 'N', 'N', D1, D2, (u['meq'], u['phm']),
            u['al'], u['al'], u['nss'], u['nss'], d1cl, d2cl, body, qed=True)
    return w.run()



# --- the exit step: the guard passes, the terminator is popped, pushed back
#     with the guard's field cleared
PUZ = PUSH('K', 'P', LOAD("F'", GE))
BR0 = BRANCH('C', 'Q', PUZ)
STM0 = BRANCH("C'", POP('K', 'F', BR0), "Q'")
HEB = lambda m: ("( ( C' ` %s ) = 1o /\\ -. ( C ` %s ) = 1o /\\ "
                 "( ( P ` %s ) = Y' /\\ ( F' ` %s ) e. N' ) )"
                 % (m, NVF(m, 'Y'), NVF(m, 'Y'), NVF(m, 'Y')))
HE = 'A. m e. N %s' % HEB('m')
LAB0 = '( A e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), DG)
FTY0 = ('( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( Q e. %s /\\ Q\' e. %s ) ) )'
        % (RATY, CTY, CTY2, PKTY, LTY, STMT_T, STMT_T))
STK0 = ("( ( D e. %s /\\ ( D ` K ) = %s ) /\\ ( ( Y e. %s /\\ Y' e. %s ) /\\ X e. Word %s ) )"
        % (STK('T'), YX, GK, GK, GK))
NSS2 = "( %s /\\ N' C_ %s )" % (NSS, S('T'))
PH0 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )'
       % (PHM, STM0, LAB0, FTY0, STK0, NSS2, HE))


def tm2fzb0():
    lab = 'tm2fzb0'
    ph = PH0
    D1 = UPD('T', 'D', 'K', 'X')
    D2 = UPD('T', 'D', 'K', YPX)
    NV = NVF('v', 'Y'); LV = "( F' ` %s )" % NV
    w = W(lab, 'The exit step of a guarded dropping scan: the guard ` C\' ` holds, '
               'the terminator ` Y ` is popped, the letter ` Y\' ` is pushed in '
               'its place and the guard\'s field is cleared by the load ` F\' ` , '
               'so the state class changes from ` N ` to ` N\' ` .  Lean: '
               '` zeroIfBorrow_loop ` , the ` nil ` case --- the terminator comes '
               'back and ` carry ` is reset.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM0))
    lb = w.s([], 'simp2l', '( %s -> %s )' % (ph, LAB0))
    al = w.s([lb, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lb, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([lb, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    ft = w.s([], 'simp2r', '( %s -> %s )' % (ph, FTY0))
    f3 = w.s([ft], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RATY, CTY, CTY2))
    ra = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, CTY2))
    f4 = w.s([ft], 'simprd', "( %s -> ( ( %s /\\ %s ) /\\ ( Q e. %s /\\ Q' e. %s ) ) )"
             % (ph, PKTY, LTY, STMT_T, STMT_T))
    pl = w.s([f4], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, PKTY, LTY))
    pk = w.s([pl], 'simpld', '( %s -> %s )' % (ph, PKTY))
    lt = w.s([pl], 'simprd', '( %s -> %s )' % (ph, LTY))
    qs = w.s([f4], 'simprd', "( %s -> ( Q e. %s /\\ Q' e. %s ) )" % (ph, STMT_T, STMT_T))
    qq = w.s([qs], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    q2 = w.s([qs], 'simprd', "( %s -> Q' e. %s )" % (ph, STMT_T))
    sk = w.s([], 'simp3l', '( %s -> %s )' % (ph, STK0))
    dk = w.s([sk], 'simpld', '( %s -> ( D e. %s /\\ ( D ` K ) = %s ) )' % (ph, STK('T'), YX))
    dd = w.s([dk], 'simpld', '( %s -> D e. %s )' % (ph, STK('T')))
    dke = w.s([dk], 'simprd', '( %s -> ( D ` K ) = %s )' % (ph, YX))
    ly = w.s([sk], 'simprd', "( %s -> ( ( Y e. %s /\\ Y' e. %s ) /\\ X e. Word %s ) )" % (ph, GK, GK, GK))
    y2 = w.s([ly], 'simpld', "( %s -> ( Y e. %s /\\ Y' e. %s ) )" % (ph, GK, GK))
    yy = w.s([y2], 'simpld', '( %s -> Y e. %s )' % (ph, GK))
    yp = w.s([y2], 'simprd', "( %s -> Y' e. %s )" % (ph, GK))
    xx = w.s([ly], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    nh = w.s([], 'simp3r', '( %s -> ( %s /\\ %s ) )' % (ph, NSS2, HE))
    n2 = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS2))
    nss = w.s([n2], 'simpld', '( %s -> %s )' % (ph, NSS))
    n2ss = w.s([n2], 'simprd', "( %s -> N' C_ %s )" % (ph, S('T')))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    ld = w.s([tv, lt, ge, w.inst('tm2load')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, LOAD("F'", GE), STMT_T))
    kp = w.s([kk, pk], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, PKTY))
    puz = w.s([tv, kp, ld, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUZ, STMT_T))
    qp = w.s([qq, puz], 'jca', '( %s -> ( Q e. %s /\\ %s e. %s ) )' % (ph, STMT_T, PUZ, STMT_T))
    br0 = w.s([tv, cc, qp, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR0, STMT_T))
    kf = w.s([kk, ra], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    po = w.s([tv, kf, br0, w.inst('tm2pop')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, POP('K', 'F', BR0), STMT_T))
    s1y = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    s1n = w.s([], 's1nz', '<" Y "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    yxn = w.s([s1y, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, YX))
    s1yp = w.s([yp], 's1cld', "( %s -> <\" Y' \"> e. Word %s )" % (ph, GK))
    ypxw = w.s([s1yp, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, YPX, GK))
    k1 = w.s([kk, xx], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (ph, DG, GK))
    d1cl = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D1, STK('T')))
    k2 = w.s([kk, ypxw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, YPX, GK))
    d2cl = w.s([tv, dd, k2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, 'D e. %s' % STK('T'))
        raa = A_(ra, RATY); cca = A_(cc, CTY); c2a = A_(c2, CTY2)
        pka = A_(pk, PKTY); lta = A_(lt, LTY)
        qqa = A_(qq, 'Q e. %s' % STMT_T); q2a = A_(q2, "Q' e. %s" % STMT_T)
        gea = A_(ge, '%s e. %s' % (GE, STMT_T)); lda = A_(ld, '%s e. %s' % (LOAD("F'", GE), STMT_T))
        puza = A_(puz, '%s e. %s' % (PUZ, STMT_T)); br0a = A_(br0, '%s e. %s' % (BR0, STMT_T))
        poa = A_(po, '%s e. %s' % (POP('K', 'F', BR0), STMT_T))
        kka = A_(kk, 'K e. %s' % DG); ela = A_(el, 'E e. %s' % L('T'))
        fea = A_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        d1a = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        dkea = A_(dke, '( D ` K ) = %s' % YX); yya = A_(yy, 'Y e. %s' % GK)
        xxa = A_(xx, 'X e. Word %s' % GK); ypxa = A_(ypxw, '%s e. Word %s' % (YPX, GK))
        nssa = A_(nss, NSS); n2sa = A_(n2ss, "N' C_ %s" % S('T'))
        hea = A_(he, HE); yxna = A_(yxn, '%s =/= (/)' % YX)
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        cg, new = W.wcongr(w, HEB('m'), {'m': 'v'}, 'm = v',
                           {'m': w.s([], 'id', '( m = v -> m = v )')})
        assert new == HEB('v'), new
        trip = w.s([cg, hea, vn], 'rspcdva', '( %s -> %s )' % (av, HEB('v')))
        gd = w.s([trip, w.inst('simp1')], 'syl', "( %s -> ( C' ` v ) = 1o )" % av)
        cf = w.s([trip, w.inst('simp2')], 'syl', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        t3 = w.s([trip, w.inst('simp3')], 'syl',
                 "( %s -> ( ( P ` %s ) = Y' /\\ %s e. N' ) )" % (av, NV, LV))
        pq = w.s([t3], 'simpld', "( %s -> ( P ` %s ) = Y' )" % (av, NV))
        lvn = w.s([t3], 'simprd', "( %s -> %s e. N' )" % (av, LV))
        lvcl = w.s([n2sa, lvn], 'sseldd', '( %s -> %s e. %s )' % (av, LV, S('T')))
        rf = w.s([], 'fvex', '%s e. _V' % S('T'))
        rfa = w.s([rf], 'a1i', '( %s -> %s e. _V )' % (av, S('T')))
        gev = w.s([], 'fvex', '%s e. _V' % GK)
        o1e = w.s([], '1oex', '1o e. _V')
        oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
        xev = w.s([rf, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
        xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (av, S('T'), OPT))
        rbi = w.s([rfa, xeva, w.inst('elmapg')], 'syl2anc',
                  '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (av, RATY, S('T'), OPT, S('T')))
        rff = w.s([rbi, raa], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (av, S('T'), OPT, S('T')))
        yil = w.s([yya, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. %s )' % (av, OPT))
        op1 = w.s([vv, yil], 'opelxpd',
                  '( %s -> <. v , ( inl ` Y ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        nvcl = w.s([rff, op1], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, lvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), LV))
        yxnn = w.s([yxna], 'neneqd', '( %s -> -. %s = (/) )' % (av, YX))
        yj = w.s([yya, xxa], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        yfv = w.s([yj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Y )' % (av, YX))
        ytl = w.s([yj, w.inst('wrdtls1')], 'syl',
                  '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = X )' % (av, YX, YX))
        xv = w.s([xxa], 'elexd', '( %s -> X e. _V )' % av)
        d1k = updkval(w, av, 'T', 'D', 'K', 'X', tva, dda, kka, xv)
        tdk = w.s([tva, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        kw2 = w.s([xxa, ypxa], 'jca', '( %s -> ( X e. Word %s /\\ %s e. Word %s ) )' % (av, GK, YPX, GK))
        up2 = w.s([tdk, kka, kw2, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', YPX), D2))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, '%s e. %s' % (NV, S('T')): nvcl,
                 '%s e. %s' % (LV, S('T')): lvcl, 'D e. %s' % STK('T'): dda,
                 '%s e. %s' % (D1, STK('T')): d1a, '%s e. %s' % (D2, STK('T')): d2a,
                 'K e. %s' % DG: kka, RATY: raa, CTY: cca, CTY2: c2a, PKTY: pka, LTY: lta,
                 'Q e. %s' % STMT_T: qqa, "Q' e. %s" % STMT_T: q2a,
                 '%s e. %s' % (BR0, STMT_T): br0a, '%s e. %s' % (PUZ, STMT_T): puza,
                 '%s e. %s' % (LOAD("F'", GE), STMT_T): lda, '%s e. %s' % (GE, STMT_T): gea,
                 '%s e. %s' % (POP('K', 'F', BR0), STMT_T): poa,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( D ` K )': (YX, dkea), '( %s ` 0 )' % YX: ('Y', yfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (YX, YX): ('X', ytl),
                 '( %s ` K )' % D1: ('X', d1k), '( P ` %s )' % NV: ("Y'", pq),
                 UPD('T', D1, 'K', YPX): (D2, up2),
                 '( %s ` %s )' % (CONSTF('T', 'E'), LV): ('E', rge)}
        ifr = {'%s = (/)' % YX: (False, yxnn), '( C ` %s ) = 1o' % NV: (False, cf),
               "( C' ` v ) = 1o": (True, gd)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM0, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (LV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, '( M ` A ) = %s' % STM0)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM0, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, LV, lvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', D2, (meq, phm),
            al, el, nss, n2ss, dd, d2cl, body, qed=True)
    return w.run()



def CLZB(X):
    return ('( { ( inl ` A ) } X. ( N X. { %s } ) )' % UPD('T', 'D', 'K', '( %s ++ R )' % X))


JZB = ('( p e. _V |-> ( { ( inl ` A ) } X. ( N X. { %s } ) ) )'
       % UPD('T', 'D', 'K', '( p ++ R )'))


def jzb(w, ante, U, ucl, nex):
    aq = '( %s /\\ p = %s )' % (ante, U)
    lp = w.s([], 'simpr', '( %s -> p = %s )' % (aq, U))
    body = ('( { ( inl ` A ) } X. ( N X. { %s } ) )' % UPD('T', 'D', 'K', '( p ++ R )'))
    st, mid = W.congr(w, body, {'p': U}, aq, {'p': lp})
    tgt = CLZB(U)
    assert mid == tgt, mid
    eqi = w.s([], 'eqid', '%s = %s' % (JZB, JZB))
    uv = w.s([ucl], 'elexd', '( %s -> %s e. _V )' % (ante, U))
    sn1 = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    sn1a = w.s([sn1], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ante)
    UPS = UPD('T', 'D', 'K', '( %s ++ R )' % U)
    sn2 = w.s([], 'snex', '{ %s } e. _V' % UPS)
    sn2a = w.s([sn2], 'a1i', '( %s -> { %s } e. _V )' % (ante, UPS))
    xp1 = w.s([nex, sn2a, w.inst('xpexg')], 'syl2anc',
              '( %s -> ( N X. { %s } ) e. _V )' % (ante, UPS))
    cex = w.s([sn1a, xp1, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ante, tgt))
    return w.s([st, eqi, uv, cex], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ante, JZB, U, tgt))


def tm2fzbw():
    lab = 'tm2fzbw'
    ph = '( %s /\\ W e. Word B )' % PH1
    phx = '( %s /\\ x e. Word B )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    HRx = HR('( %s ` x )' % JZB, 'T', 'M', '( %s ` %s )' % (JZB, TL('x')), '1')
    HYPJ = 'A. x e. Word B ( x =/= (/) -> %s )' % HRx
    ZCJ = '( %s ` (/) ) C_ %s' % (JZB, CFG('T'))
    w = W(lab, 'The loop of a guarded dropping scan: an instantiation of '
               '~ tm2hwrd , whose invariant is indexed by the part of the word '
               'still to be popped --- nothing is accumulated, because nothing '
               'is pushed.  Lean: the induction in ` zeroIfBorrow_loop ` .')
    one = w.s([], 'tm2fzb1', '( %s -> %s )'
              % (ante2, HR(CLZB('x'), 'T', 'M', CLZB(TL('x')), '1')))
    u2 = ctx1(w, ante2, 'ad2antrr')
    xw1 = w.s([], 'simplr', '( %s -> x e. Word B )' % ante2)
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    sev2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    sev2a = w.s([sev2], 'a1i', '( %s -> %s e. _V )' % (ante2, S('T')))
    nex2 = w.s([u2['nss'], sev2a, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ante2)
    jx = jzb(w, ante2, 'x', xw1, nex2)
    jt = jzb(w, ante2, TL('x'), tlw1, nex2)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` %s ) , 1 >. = <. %s , 1 >. )'
             % (ante2, JZB, TL('x'), CLZB(TL('x'))))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CLZB('x'), 'T', 'M', '( %s ` %s )' % (JZB, TL('x')), '1'),
                HR(CLZB('x'), 'T', 'M', CLZB(TL('x')), '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CLZB('x'), 'T', 'M', '( %s ` %s )' % (JZB, TL('x')), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CLZB('x'), 'T', 'M', '( %s ` %s )' % (JZB, TL('x')), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    hyp = w.s([ex1], 'ralrimiva', '( %s -> %s )' % (PH1, HYPJ))
    hypa = w.s([hyp], 'adantr', '( %s -> %s )' % (ph, HYPJ))
    u = ctx1(w, ph, 'adantr')
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    sevp = w.s([], 'fvex', '%s e. _V' % S('T'))
    sevpa = w.s([sevp], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    nexp = w.s([u['nss'], sevpa, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ph)
    w0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word %s )' % (ph, GK))
    w0b = w.s([], 'wrd0', '(/) e. Word B')
    w0ba = w.s([w0b], 'a1i', '( %s -> (/) e. Word B )' % ph)
    jz = jzb(w, ph, '(/)', w0ba, nexp)
    zrw = w.s([w0a, u['rw'], w.inst('ccatcl')], 'syl2anc',
              '( %s -> ( (/) ++ R ) e. Word %s )' % (ph, GK))
    kz = w.s([u['kk'], zrw], 'jca', '( %s -> ( K e. %s /\\ ( (/) ++ R ) e. Word %s ) )' % (ph, DG, GK))
    dzcl = w.s([u['tv'], u['dd'], kz, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), STK('T')))
    sn = w.s([dzcl], 'snssd', '( %s -> { %s } C_ %s )'
             % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), STK('T')))
    xs = w.s([u['nss'], sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( N X. { %s } ) C_ ( %s X. %s ) )'
             % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), S('T'), STK('T')))
    cls = w.s([u['tv'], u['al'], xs, w.inst('tm2hcfgss')], 'syl3anc',
              '( %s -> %s C_ %s )' % (ph, CLZB('(/)'), CFG('T')))
    zc = w.s([jz, cls], 'eqsstrd', '( %s -> %s )' % (ph, ZCJ))
    n1 = w.s([], '1nn0', '1 e. NN0')
    n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([n1a, zc], 'jca', '( %s -> ( 1 e. NN0 /\\ %s ) )' % (ph, ZCJ))
    ant = w.s([u['phm'], pj, hypa], '3jca', '( %s -> ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) )'
              % (ph, PHM, ZCJ, HYPJ))
    ant2 = w.s([ant, ww], 'jca',
               '( %s -> ( ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) /\\ W e. Word B ) )'
               % (ph, PHM, ZCJ, HYPJ))
    run = w.s([ant2, w.inst('tm2hwrd')], 'syl', '( %s -> %s )'
              % (ph, HR('( %s ` W )' % JZB, 'T', 'M', '( %s ` (/) )' % JZB, '( ( # ` W ) x. 1 )')))
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` (/) ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JZB, CLZB('(/)')))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` W )' % JZB, 'T', 'M', '( %s ` (/) )' % JZB, '( ( # ` W ) x. 1 )'),
                HR('( %s ` W )' % JZB, 'T', 'M', CLZB('(/)'), '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` W )' % JZB, 'T', 'M', CLZB('(/)'), '( # ` W )')))
    jw = jzb(w, ph, 'W', ww, nexp)
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` W )' % JZB, 'T', 'M', CLZB('(/)'), '( # ` W )'),
                HR(CLZB('W'), 'T', 'M', CLZB('(/)'), '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )'
          % (ph, HR(CLZB('W'), 'T', 'M', CLZB('(/)'), '( # ` W )')))
    return w.run()



HC1F = ("A. r e. N A. z e. B ( ( C' ` r ) = 1o /\\ ( C ` %s ) = 1o /\\ %s e. N )"
        % (NVF('r', 'z'), NVF('r', 'z')))
STMF = BRANCH("C'", POP('K', 'F', BRANCH('C', GA, PUZ)), GE)
LABF = '( A e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), DG)
FTYF = '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (RATY, CTY, CTY2, PKTY, LTY)
WTYF = ("( ( B C_ %s /\\ ( Y e. %s /\\ Y' e. %s ) ) /\\ ( X e. Word %s /\\ D e. %s ) )"
        % (GK, GK, GK, GK, STK('T')))
PHF = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
       % (PHM, STMF, LABF, FTYF, WTYF, NSS2, HC1F, HE))


def tm2fzb():
    lab = 'tm2fzb'
    ph = '( %s /\\ W e. Word B )' % PHF
    DM = UPD('T', 'D', 'K', YX)
    D2 = UPD('T', 'D', 'K', YPX)
    w = W(lab, 'The guarded dropping scan, assembled: if the guard ` C\' ` holds, '
               'the machine pops the word ` W ` off stack ` K ` , pushes the '
               'letter ` Y\' ` in place of the terminator ` Y ` and clears the '
               'guard\'s field, in ` ( # ` W ) + 1 ` steps.  Lean: '
               '` zeroIfBorrow_runs ` in the branch ` v.carry = true ` --- the '
               'difference just written is replaced by zero.')
    phm0 = w.s([], 'simp1l', '( %s -> %s )' % (PHF, PHM))
    meq0 = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHF, STMF))
    lb0 = w.s([], 'simp2l', '( %s -> %s )' % (PHF, LABF))
    ft0 = w.s([], 'simp2r', '( %s -> %s )' % (PHF, FTYF))
    wt0 = w.s([], 'simp3l', '( %s -> %s )' % (PHF, WTYF))
    nh0 = w.s([], 'simp3r', '( %s -> ( %s /\\ ( %s /\\ %s ) )' % (PHF, NSS2, HC1F, HE) + ' )')
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm0, PHM); meq = A_(meq0, '( M ` A ) = %s' % STMF)
    lb = A_(lb0, LABF); ft = A_(ft0, FTYF); wt = A_(wt0, WTYF)
    nh = A_(nh0, '( %s /\\ ( %s /\\ %s ) )' % (NSS2, HC1F, HE))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    al = w.s([lb, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lb, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([lb, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    f3 = w.s([ft], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RATY, CTY, CTY2))
    ra = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, CTY2))
    pl = w.s([ft], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, PKTY, LTY))
    pk = w.s([pl], 'simpld', '( %s -> %s )' % (ph, PKTY))
    lt = w.s([pl], 'simprd', '( %s -> %s )' % (ph, LTY))
    by = w.s([wt], 'simpld', "( %s -> ( B C_ %s /\\ ( Y e. %s /\\ Y' e. %s ) ) )" % (ph, GK, GK, GK))
    bk = w.s([by], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    y2 = w.s([by], 'simprd', "( %s -> ( Y e. %s /\\ Y' e. %s ) )" % (ph, GK, GK))
    yy = w.s([y2], 'simpld', '( %s -> Y e. %s )' % (ph, GK))
    yp = w.s([y2], 'simprd', "( %s -> Y' e. %s )" % (ph, GK))
    xd = w.s([wt], 'simprd', '( %s -> ( X e. Word %s /\\ D e. %s ) )' % (ph, GK, STK('T')))
    xx = w.s([xd], 'simpld', '( %s -> X e. Word %s )' % (ph, GK))
    dd = w.s([xd], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    n2 = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS2))
    nss = w.s([n2], 'simpld', '( %s -> %s )' % (ph, NSS))
    n2ss = w.s([n2], 'simprd', "( %s -> N' C_ %s )" % (ph, S('T')))
    ch = w.s([nh], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, HC1F, HE))
    hc = w.s([ch], 'simpld', '( %s -> %s )' % (ph, HC1F))
    he = w.s([ch], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fa = constfty(w, ph, 'A', L('T'), al)
    ga = w.s([tv, fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    ld = w.s([tv, lt, ge, w.inst('tm2load')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, LOAD("F'", GE), STMT_T))
    kp = w.s([kk, pk], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, PKTY))
    puz = w.s([tv, kp, ld, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUZ, STMT_T))
    s1y = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    yxw = w.s([s1y, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, YX, GK))
    # ---- the loop, at R := ( <" Y "> ++ X ) , Q := PUZ , Q' := goto E
    lab1i = w.s([al, kk], 'jca', '( %s -> ( A e. %s /\\ K e. %s ) )' % (ph, L('T'), DG))
    fty1i = w.s([f3, w.s([puz, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
                         % (ph, PUZ, STMT_T, GE, STMT_T))], 'jca',
                '( %s -> ( ( %s /\\ %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) )'
                % (ph, RATY, CTY, CTY2, PUZ, STMT_T, GE, STMT_T))
    wty1i = w.s([w.s([bk, yxw], 'jca', '( %s -> ( B C_ %s /\\ %s e. Word %s ) )' % (ph, GK, YX, GK)), dd],
                'jca', '( %s -> ( ( B C_ %s /\\ %s e. Word %s ) /\\ D e. %s ) )'
                % (ph, GK, YX, GK, STK('T')))
    nhc = w.s([nss, hc], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HC1F))
    p3i = w.s([wty1i, nhc], 'jca',
              '( %s -> ( ( ( B C_ %s /\\ %s e. Word %s ) /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
              % (ph, GK, YX, GK, STK('T'), NSS, HC1F))
    pm1 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STMF))
    p2i = w.s([lab1i, fty1i], 'jca',
              '( %s -> ( ( A e. %s /\\ K e. %s ) /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) ) )'
              % (ph, L('T'), DG, RATY, CTY, CTY2, PUZ, STMT_T, GE, STMT_T))
    PH1i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ '
            '( ( A e. %s /\\ K e. %s ) /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) ) /\\ '
            '( ( ( B C_ %s /\\ %s e. Word %s ) /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
            % (PHM, STMF, L('T'), DG, RATY, CTY, CTY2, PUZ, STMT_T, GE, STMT_T,
               GK, YX, GK, STK('T'), NSS, HC1F))
    pmi = w.s([pm1, p2i, p3i], '3jca', '( %s -> %s )' % (ph, PH1i))
    anti = w.s([pmi, ww], 'jca', '( %s -> ( %s /\\ W e. Word B ) )' % (ph, PH1i))
    CL0 = ('( { ( inl ` A ) } X. ( N X. { %s } ) )'
           % UPD('T', 'D', 'K', '( W ++ %s )' % YX))
    CL1 = ('( { ( inl ` A ) } X. ( N X. { %s } ) )'
           % UPD('T', 'D', 'K', '( (/) ++ %s )' % YX))
    loop = w.s([anti, w.inst('tm2fzbw')], 'syl', '( %s -> %s )'
               % (ph, HR(CL0, 'T', 'M', CL1, '( # ` W )')))
    lidy = w.s([yxw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, YX, YX))
    cs, mid = w.rewrite(CL1, {'( (/) ++ %s )' % YX: (YX, lidy)}, ph)
    MID = '( { ( inl ` A ) } X. ( N X. { %s } ) )' % DM
    assert mid == MID, mid
    o1 = w.s([cs], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )' % (ph, CL1, MID))
    b1 = w.s([o1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CL0, 'T', 'M', CL1, '( # ` W )'), HR(CL0, 'T', 'M', MID, '( # ` W )')))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )' % (ph, HR(CL0, 'T', 'M', MID, '( # ` W )')))
    # ---- the exit, at D := DM , Q := goto A , Q' := goto E
    kyx = w.s([kk, yxw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, YX, GK))
    dmcl = w.s([tv, dd, kyx, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DM, STK('T')))
    yxv = w.s([yxw], 'elexd', '( %s -> %s e. _V )' % (ph, YX))
    dmk = updkval(w, ph, 'T', 'D', 'K', YX, tv, dd, kk, yxv)
    lab0i = w.s([al, el, kk], '3jca', '( %s -> %s )' % (ph, LABF))
    fty0i = w.s([f3, w.s([pl, w.s([ga, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
                                  % (ph, GA, STMT_T, GE, STMT_T))], 'jca',
                         '( %s -> ( ( %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) )'
                         % (ph, PKTY, LTY, GA, STMT_T, GE, STMT_T))], 'jca',
                '( %s -> ( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) ) )'
                % (ph, RATY, CTY, CTY2, PKTY, LTY, GA, STMT_T, GE, STMT_T))
    stk0i = w.s([w.s([dmcl, dmk], 'jca', '( %s -> ( %s e. %s /\\ ( %s ` K ) = %s ) )'
                     % (ph, DM, STK('T'), DM, YX)),
                 w.s([y2, xx], 'jca', "( %s -> ( ( Y e. %s /\\ Y' e. %s ) /\\ X e. Word %s ) )"
                     % (ph, GK, GK, GK))], 'jca',
                "( %s -> ( ( %s e. %s /\\ ( %s ` K ) = %s ) /\\ ( ( Y e. %s /\\ Y' e. %s ) /\\ X e. Word %s ) ) )"
                % (ph, DM, STK('T'), DM, YX, GK, GK, GK))
    nhe = w.s([n2, he], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, NSS2, HE))
    p30i = w.s([stk0i, nhe], 'jca',
               "( %s -> ( ( ( %s e. %s /\\ ( %s ` K ) = %s ) /\\ ( ( Y e. %s /\\ Y' e. %s ) /\\ X e. Word %s ) ) "
               '/\\ ( %s /\\ %s ) ) )'
               % (ph, DM, STK('T'), DM, YX, GK, GK, GK, NSS2, HE))
    p20i = w.s([lab0i, fty0i], 'jca',
               '( %s -> ( %s /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) ) ) )'
               % (ph, LABF, RATY, CTY, CTY2, PKTY, LTY, GA, STMT_T, GE, STMT_T))
    PH0i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ '
            '( %s /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) ) ) /\\ '
            "( ( ( %s e. %s /\\ ( %s ` K ) = %s ) /\\ ( ( Y e. %s /\\ Y' e. %s ) /\\ X e. Word %s ) ) "
            '/\\ ( %s /\\ %s ) ) )'
            % (PHM, STMF, LABF, RATY, CTY, CTY2, PKTY, LTY, GA, STMT_T, GE, STMT_T,
               DM, STK('T'), DM, YX, GK, GK, GK, NSS2, HE))
    p0i = w.s([pm1, p20i, p30i], '3jca', '( %s -> %s )' % (ph, PH0i))
    CLE = "( { ( inl ` E ) } X. ( N' X. { %s } ) )" % UPD('T', DM, 'K', YPX)
    exit_ = w.s([p0i, w.inst('tm2fzb0')], 'syl', '( %s -> %s )' % (ph, HR(MID, 'T', 'M', CLE, '1')))
    s1yp = w.s([yp], 's1cld', "( %s -> <\" Y' \"> e. Word %s )" % (ph, GK))
    ypxw = w.s([s1yp, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, YPX, GK))
    tdk = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK('T')))
    kw2 = w.s([yxw, ypxw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, YX, GK, YPX, GK))
    up2 = w.s([tdk, kk, kw2, w.inst('tm2stkup2')], 'syl3anc',
              '( %s -> %s = %s )' % (ph, UPD('T', DM, 'K', YPX), D2))
    CLE2 = "( { ( inl ` E ) } X. ( N' X. { %s } ) )" % D2
    cs3, n3 = w.rewrite(CLE, {UPD('T', DM, 'K', YPX): (D2, up2)}, ph)
    assert n3 == CLE2, n3
    o2 = w.s([cs3], 'opeq1d', '( %s -> <. %s , 1 >. = <. %s , 1 >. )' % (ph, CLE, CLE2))
    b2b = w.s([o2], 'breq2d', '( %s -> ( %s <-> %s ) )'
              % (ph, HR(MID, 'T', 'M', CLE, '1'), HR(MID, 'T', 'M', CLE2, '1')))
    exit2 = w.s([b2b, exit_], 'mpbid', '( %s -> %s )' % (ph, HR(MID, 'T', 'M', CLE2, '1')))
    w.qed([phm, loop2, exit2], 'syl3anc', '( %s -> %s )'
          % (ph, HR(CL0, 'T', 'M', CLE2, '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fzb1'): tm2fzb1()
    if want('tm2fzb0'): tm2fzb0()
    if want('tm2fzbw'): tm2fzbw()
    if want('tm2fzb'): tm2fzb()
