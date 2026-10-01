"""T3: the generic exit step of a pop-branch scan loop, and `zeroScan` --- the
mover with a fold into the internal state (blueprint 4.3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty, rfun, updn, upd2cl, OPT, RATY, CTY, PTY, DG, GK, GJ, ST, \
    STMT_T, TL, NVF, GA, UPD2

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GE = GOTO(CONSTF('T', 'E'))
ZX = '( <" Y "> ++ X )'


def tm2fpb0():
    lab = 'tm2fpb0'
    BR0 = BRANCH('C', 'Q', GE)
    STM0 = POP('K', 'F', BR0)
    D2 = UPD('T', 'D', 'K', 'X')
    HE = 'A. m e. N ( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NVF('m', 'Y'), NVF('m', 'Y'))
    LABTY = ('( ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s /\\ Q e. %s ) )'
             % (L('T'), L('T'), DG, RATY, CTY, STMT_T))
    STKTY = ('( ( D e. %s /\\ ( D ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) /\\ ( N C_ %s /\\ %s ) )'
             % (STK('T'), ZX, GK, GK, S('T'), HE))
    ph = '( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ %s )' % (PHM, STM0, LABTY, STKTY)
    w = W(lab, 'The exit step of a pop-branch scan loop: the terminator ` Y ` '
               'is on top of stack ` K ` , the branch is not taken and the '
               'machine leaves the loop, the internal state staying in the '
               'class ` N ` .  The continue branch ` Q ` and the stacks ` D ` '
               'are class variables, so this one lemma is the exit step of '
               '` dropNum ` , ` moveNum ` , ` move2Num ` , ` zeroScan ` and '
               'every other fragment of the layer whose loop ends with '
               '` goto e ` (Lean: the ` nil ` case of each ` _loop ` ).')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM0))
    lb = w.s([], 'simp2l', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )' % (ph, L('T'), L('T'), DG))
    al = w.s([lb, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lb, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([lb, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    ft = w.s([], 'simp2r', '( %s -> ( %s /\\ %s /\\ Q e. %s ) )' % (ph, RATY, CTY, STMT_T))
    ra = w.s([ft, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([ft, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    qq = w.s([ft, w.inst('simp3')], 'syl', '( %s -> Q e. %s )' % (ph, STMT_T))
    dk = w.s([], 'simp3l', '( %s -> ( D e. %s /\\ ( D ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) )'
             % (ph, STK('T'), ZX, GK, GK))
    dd = w.s([dk, w.inst('simp1')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    dke = w.s([dk, w.inst('simp2')], 'syl', '( %s -> ( D ` K ) = %s )' % (ph, ZX))
    yx = w.s([dk, w.inst('simp3')], 'syl', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (ph, GK, GK))
    yy = w.s([yx], 'simpld', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([yx], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    nh = w.s([], 'simp3r', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), HE))
    nss = w.s([nh], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    qg = w.s([qq, ge], 'jca', '( %s -> ( Q e. %s /\\ %s e. %s ) )' % (ph, STMT_T, GE, STMT_T))
    br = w.s([tv, cc, qg, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR0, STMT_T))
    kx = w.s([kk, xx], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (ph, DG, GK))
    d2cl = w.s([tv, dd, kx, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    s1n = w.s([], 's1nz', '<" Y "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    zxn = w.s([s1c, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, ZX))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, 'D e. %s' % STK('T'))
        raa = A_(ra, RATY); cca = A_(cc, CTY); qqa = A_(qq, 'Q e. %s' % STMT_T)
        gea = A_(ge, '%s e. %s' % (GE, STMT_T)); bra = A_(br, '%s e. %s' % (BR0, STMT_T))
        kka = A_(kk, 'K e. %s' % DG); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        nssa = A_(nss, 'N C_ %s' % S('T')); hea = A_(he, HE); ela = A_(el, 'E e. %s' % L('T'))
        fea = A_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        dkea = A_(dke, '( D ` K ) = %s' % ZX); yya = A_(yy, 'Y e. %s' % GK)
        xxa = A_(xx, 'X e. Word %s' % GK); zxna = A_(zxn, '%s =/= (/)' % ZX)
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        # the exit interface at m := v
        NV = NVF('v', 'Y')
        PAIR = lambda x: '( -. ( C ` %s ) = 1o /\\ %s e. N )' % (x, x)
        cg, new = W.wcongr(w, PAIR(NVF('m', 'Y')), {'m': 'v'}, 'm = v',
                           {'m': w.s([], 'id', '( m = v -> m = v )')})
        assert new == PAIR(NV), new
        h2 = w.s([cg, hea, vn], 'rspcdva', '( %s -> %s )' % (av, PAIR(NV)))
        rc = w.s([h2], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        nvn = w.s([h2], 'simprd', '( %s -> %s e. N )' % (av, NV))
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        zxnn = w.s([zxna], 'neneqd', '( %s -> -. %s = (/) )' % (av, ZX))
        yj = w.s([yya, xxa], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        zfv = w.s([yj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Y )' % (av, ZX))
        ztl = w.s([yj, w.inst('wrdtls1')], 'syl',
                  '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = X )' % (av, ZX, ZX))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, '%s e. %s' % (NV, S('T')): nvcl,
                 'D e. %s' % STK('T'): dda, '%s e. %s' % (D2, STK('T')): d2a,
                 RATY: raa, CTY: cca, 'Q e. %s' % STMT_T: qqa,
                 '%s e. %s' % (BR0, STMT_T): bra, '%s e. %s' % (GE, STMT_T): gea,
                 'K e. %s' % DG: kka,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( D ` K )': (ZX, dkea), '( %s ` 0 )' % ZX: ('Y', zfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (ZX, ZX): ('X', ztl),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NV): ('E', rge)}
        ifr = {'%s = (/)' % ZX: (False, zxnn), '( C ` %s ) = 1o' % NV: (False, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM0, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, '( M ` A ) = %s' % STM0)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM0, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, NV, nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', D2, (meq, phm),
            al, el, nss, nss, dd, d2cl, body, qed=True)
    return w.run()



# --------------------------------------------------- zeroScan: the fold mover

LTY = "F' e. ( %s ^m %s )" % (S('T'), S('T'))
LVF = lambda r, z: "( F' ` %s )" % NVF(r, z)
PU = PUSH('J', 'P', LOAD("F'", GA))
BR = BRANCH('C', PU, 'Q')
STM = POP('K', 'F', BR)
TRIP = lambda m, n, t: ("( ( C ` %s ) = 1o /\\ ( P ` %s ) = %s /\\ ( P' ` %s ) = ( O ` ( <\" %s \"> ++ %s ) ) )"
                        % (NVF(m, n), NVF(m, n), n, LVF(m, n), n, t))
IMP = lambda m, n, t: "( ( P' ` %s ) = ( O ` %s ) -> %s )" % (m, t, TRIP(m, n, t))
HC = 'A. m e. %s A. n e. B A. t e. Word B %s' % (S('T'), IMP('m', 'n', 't'))
NCL = lambda s: "{ q e. %s | ( P' ` q ) = ( O ` %s ) }" % (S('T'), s)
LAB = '( A e. %s /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )' % (L('T'), DG, DG)
FTY = '( %s /\\ %s /\\ %s )' % (RATY, CTY, PTY)
WTY = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( R e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
       % (GK, GJ, GK, GJ, STK('T')))
QTY = '( ( Q e. %s /\\ %s ) /\\ %s )' % (STMT_T, LTY, HC)
PH1 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM, LAB, FTY, WTY, QTY))


def zctx(w, ph, lift=None):
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
    ql = w.s([qt], 'simpld', '( %s -> ( Q e. %s /\\ %s ) )' % (ph, STMT_T, LTY))
    qq = w.s([ql], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    lt = w.s([ql], 'simprd', '( %s -> %s )' % (ph, LTY))
    hc = w.s([qt], 'simprd', '( %s -> %s )' % (ph, HC))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, kk=kk, jj=jj, ne=ne, nes=nes, ra=ra, cc=cc, pp=pp,
                bk=bk, bj=bj, rw=rw, hw=hw, dd=dd, qq=qq, lt=lt, hc=hc, tv=tv)


def hcinst(w, av, ZT, TT, hca, vv, zcl, tcl, pre):
    """the fold interface at m := v , n := ZT , t := TT , given `pre` proving
    ( av -> ( P' ` v ) = ( O ` TT ) )"""
    # m := v
    a1 = w.s([], 'opeq1', '( m = v -> <. m , ( inl ` n ) >. = <. v , ( inl ` n ) >. )')
    a2 = w.s([a1], 'fveq2d', '( m = v -> %s = %s )' % (NVF('m', 'n'), NVF('v', 'n')))
    a3 = w.s([a2], 'fveq2d', '( m = v -> ( C ` %s ) = ( C ` %s ) )' % (NVF('m', 'n'), NVF('v', 'n')))
    a4 = w.s([a3], 'eqeq1d', '( m = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )'
             % (NVF('m', 'n'), NVF('v', 'n')))
    a5 = w.s([a2], 'fveq2d', '( m = v -> ( P ` %s ) = ( P ` %s ) )' % (NVF('m', 'n'), NVF('v', 'n')))
    a6 = w.s([a5], 'eqeq1d', '( m = v -> ( ( P ` %s ) = n <-> ( P ` %s ) = n ) )'
             % (NVF('m', 'n'), NVF('v', 'n')))
    a7 = w.s([a2], 'fveq2d', "( m = v -> %s = %s )" % (LVF('m', 'n'), LVF('v', 'n')))
    a8 = w.s([a7], 'fveq2d', "( m = v -> ( P' ` %s ) = ( P' ` %s ) )" % (LVF('m', 'n'), LVF('v', 'n')))
    a9 = w.s([a8], 'eqeq1d', "( m = v -> ( ( P' ` %s ) = ( O ` ( <\" n \"> ++ t ) ) <-> "
             "( P' ` %s ) = ( O ` ( <\" n \"> ++ t ) ) ) )" % (LVF('m', 'n'), LVF('v', 'n')))
    a10 = w.s([a4, a6, a9], '3anbi123d', '( m = v -> ( %s <-> %s ) )'
              % (TRIP('m', 'n', 't'), TRIP('v', 'n', 't')))
    b1 = w.s([], 'fveq2', "( m = v -> ( P' ` m ) = ( P' ` v ) )")
    b2 = w.s([b1], 'eqeq1d', "( m = v -> ( ( P' ` m ) = ( O ` t ) <-> ( P' ` v ) = ( O ` t ) ) )")
    b3 = w.s([b2, a10], 'imbi12d', '( m = v -> ( %s <-> %s ) )' % (IMP('m', 'n', 't'), IMP('v', 'n', 't')))
    b4 = w.s([b3], 'ralbidv', '( m = v -> ( A. t e. Word B %s <-> A. t e. Word B %s ) )'
             % (IMP('m', 'n', 't'), IMP('v', 'n', 't')))
    b5 = w.s([b4], 'ralbidv', '( m = v -> ( A. n e. B A. t e. Word B %s <-> A. n e. B A. t e. Word B %s ) )'
             % (IMP('m', 'n', 't'), IMP('v', 'n', 't')))
    h1 = w.s([b5, hca, vv], 'rspcdva', '( %s -> A. n e. B A. t e. Word B %s )' % (av, IMP('v', 'n', 't')))
    # n := ZT
    c1 = w.s([], 'fveq2', '( n = %s -> ( inl ` n ) = ( inl ` %s ) )' % (ZT, ZT))
    c2 = w.s([c1], 'opeq2d', '( n = %s -> <. v , ( inl ` n ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    c3 = w.s([c2], 'fveq2d', '( n = %s -> %s = %s )' % (ZT, NVF('v', 'n'), NVF('v', ZT)))
    c4 = w.s([c3], 'fveq2d', '( n = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NVF('v', 'n'), NVF('v', ZT)))
    c5 = w.s([c4], 'eqeq1d', '( n = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )'
             % (ZT, NVF('v', 'n'), NVF('v', ZT)))
    cid = w.s([], 'id', '( n = %s -> n = %s )' % (ZT, ZT))
    c6 = w.s([c3], 'fveq2d', '( n = %s -> ( P ` %s ) = ( P ` %s ) )' % (ZT, NVF('v', 'n'), NVF('v', ZT)))
    c7 = w.s([c6, cid], 'eqeq12d', '( n = %s -> ( ( P ` %s ) = n <-> ( P ` %s ) = %s ) )'
             % (ZT, NVF('v', 'n'), NVF('v', ZT), ZT))
    c8 = w.s([c3], 'fveq2d', "( n = %s -> %s = %s )" % (ZT, LVF('v', 'n'), LVF('v', ZT)))
    c9 = w.s([c8], 'fveq2d', "( n = %s -> ( P' ` %s ) = ( P' ` %s ) )" % (ZT, LVF('v', 'n'), LVF('v', ZT)))
    c10 = w.s([cid], 's1eqd', '( n = %s -> <\" n \"> = <\" %s \"> )' % (ZT, ZT))
    c11 = w.s([c10], 'oveq1d', '( n = %s -> ( <\" n \"> ++ t ) = ( <\" %s \"> ++ t ) )' % (ZT, ZT))
    c12 = w.s([c11], 'fveq2d', '( n = %s -> ( O ` ( <\" n \"> ++ t ) ) = ( O ` ( <\" %s \"> ++ t ) ) )'
              % (ZT, ZT))
    c13 = w.s([c9, c12], 'eqeq12d', "( n = %s -> ( ( P' ` %s ) = ( O ` ( <\" n \"> ++ t ) ) <-> "
              "( P' ` %s ) = ( O ` ( <\" %s \"> ++ t ) ) ) )" % (ZT, LVF('v', 'n'), LVF('v', ZT), ZT))
    c14 = w.s([c5, c7, c13], '3anbi123d', '( n = %s -> ( %s <-> %s ) )'
              % (ZT, TRIP('v', 'n', 't'), TRIP('v', ZT, 't')))
    c15 = w.s([c14], 'imbi2d', '( n = %s -> ( %s <-> %s ) )' % (ZT, IMP('v', 'n', 't'), IMP('v', ZT, 't')))
    c16 = w.s([c15], 'ralbidv', '( n = %s -> ( A. t e. Word B %s <-> A. t e. Word B %s ) )'
              % (ZT, IMP('v', 'n', 't'), IMP('v', ZT, 't')))
    h2 = w.s([c16, h1, zcl], 'rspcdva', '( %s -> A. t e. Word B %s )' % (av, IMP('v', ZT, 't')))
    # t := TT
    d1 = w.s([], 'fveq2', '( t = %s -> ( O ` t ) = ( O ` %s ) )' % (TT, TT))
    d2 = w.s([d1], 'eqeq2d', "( t = %s -> ( ( P' ` v ) = ( O ` t ) <-> ( P' ` v ) = ( O ` %s ) ) )"
             % (TT, TT))
    d3 = w.s([], 'oveq2', '( t = %s -> ( <\" %s \"> ++ t ) = ( <\" %s \"> ++ %s ) )' % (TT, ZT, ZT, TT))
    d4 = w.s([d3], 'fveq2d', '( t = %s -> ( O ` ( <\" %s \"> ++ t ) ) = ( O ` ( <\" %s \"> ++ %s ) ) )'
             % (TT, ZT, ZT, TT))
    d5 = w.s([d4], 'eqeq2d', "( t = %s -> ( ( P' ` %s ) = ( O ` ( <\" %s \"> ++ t ) ) <-> "
             "( P' ` %s ) = ( O ` ( <\" %s \"> ++ %s ) ) ) )" % (TT, LVF('v', ZT), ZT, LVF('v', ZT), ZT, TT))
    d6 = w.s([d5], '3anbi3d', '( t = %s -> ( %s <-> %s ) )' % (TT, TRIP('v', ZT, 't'), TRIP('v', ZT, TT)))
    d7 = w.s([d2, d6], 'imbi12d', '( t = %s -> ( %s <-> %s ) )' % (TT, IMP('v', ZT, 't'), IMP('v', ZT, TT)))
    h3 = w.s([d7, h2, tcl], 'rspcdva', '( %s -> %s )' % (av, IMP('v', ZT, TT)))
    trip = w.s([h3, pre], 'mpd', '( %s -> %s )' % (av, TRIP('v', ZT, TT)))
    bc = w.s([trip, w.inst('simp1')], 'syl', '( %s -> ( C ` %s ) = 1o )' % (av, NVF('v', ZT)))
    pv = w.s([trip, w.inst('simp2')], 'syl', '( %s -> ( P ` %s ) = %s )' % (av, NVF('v', ZT), ZT))
    fl = w.s([trip, w.inst('simp3')], 'syl',
             "( %s -> ( P' ` %s ) = ( O ` ( <\" %s \"> ++ %s ) ) )" % (av, LVF('v', ZT), ZT, TT))
    return bc, pv, fl



def nclss(w, ante, ss):
    st = w.s([], 'ssrab2', '%s C_ %s' % (NCL(ss), S('T')))
    return w.s([st], 'a1i', '( %s -> %s C_ %s )' % (ante, NCL(ss), S('T')))


def inncl(w, ante, X, ss, xcl, val):
    """( ante -> X e. NCL(ss) ) from xcl : X e. S and val : ( P' ` X ) = ( O ` ss )"""
    c1 = w.s([], 'fveq2', "( q = %s -> ( P' ` q ) = ( P' ` %s ) )" % (X, X))
    c2 = w.s([c1], 'eqeq1d', "( q = %s -> ( ( P' ` q ) = ( O ` %s ) <-> ( P' ` %s ) = ( O ` %s ) ) )"
             % (X, ss, X, ss))
    return w.s([c2, xcl, val], 'elrabd', '( %s -> %s e. %s )' % (ante, X, NCL(ss)))


def outncl(w, ante, X, ss, xin):
    """( ante -> ( P' ` X ) = ( O ` ss ) ) from xin : X e. NCL(ss)"""
    c1 = w.s([], 'fveq2', "( q = %s -> ( P' ` q ) = ( P' ` %s ) )" % (X, X))
    c2 = w.s([c1], 'eqeq1d', "( q = %s -> ( ( P' ` q ) = ( O ` %s ) <-> ( P' ` %s ) = ( O ` %s ) ) )"
             % (X, ss, X, ss))
    return w.s([c2, xin], 'elrabrd', "( %s -> ( P' ` %s ) = ( O ` %s ) )" % (ante, X, ss))


def lfun(w, ph, lt):
    """F' as a function S --> S"""
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    bi = w.s([seva, seva, w.inst('elmapg')], 'syl2anc',
             "( %s -> ( %s <-> F' : %s --> %s ) )" % (ph, LTY, S('T'), S('T')))
    return w.s([bi, lt], 'mpbid', "( %s -> F' : %s --> %s )" % (ph, S('T'), S('T')))


def tm2fzs1():
    lab = 'tm2fzs1'
    ph = '( ( %s /\\ ( x e. Word B /\\ s e. Word B ) ) /\\ x =/= (/) )' % PH1
    XR = '( x ++ R )'; SH = '( s ++ H )'
    TXR = '( %s ++ R )' % TL('x'); X0 = '( x ` 0 )'
    ACC = '( ( <" %s "> ++ s ) ++ H )' % X0
    SACC = '( <" %s "> ++ s )' % X0
    D1 = UPD2(XR, SH); D2 = UPD2(TXR, ACC)
    DK1 = UPD('T', 'D', 'K', XR); D2K = UPD('T', D1, 'K', TXR)
    NV = NVF('v', X0); LV = LVF('v', X0)
    w = W(lab, 'One iteration of the fold mover: the popped letter is pushed on '
               'stack ` J ` and folded into the internal state, whose class is '
               'therefore a function of the word accumulated so far --- '
               '` { q e. ( 2nd ` T ) | ( P\' ` q ) = ( O ` s ) } ` with ` O ` '
               'the fold and ` P\' ` the field it acts on.  Lean: '
               '` zeroScan_loop ` , the ` cons ` case (` flag := flag && !bit `).  '
               'At a constant ` O ` this is ~ tm2fmvn1 .')
    u = zctx(w, ph, 'ad2antrr')
    # statement typings
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ld = w.s([u['tv'], u['lt'], ga, w.inst('tm2load')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, LOAD("F'", GA), STMT_T))
    jp = w.s([u['jj'], u['pp']], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], jp, ld, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    j = w.s([pu, u['qq']], 'jca', '( %s -> ( %s e. %s /\\ Q e. %s ) )' % (ph, PU, STMT_T, STMT_T))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR, STMT_T))
    # words
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
    xsw = w.s([s1c, swg, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, SACC, GJ))
    accw = w.s([xsw, u['hw'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ACC, GJ))
    s1cb = w.s([x0], 's1cld', '( %s -> <" %s "> e. Word B )' % (ph, X0))
    sacb = w.s([s1cb, sw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, SACC))
    xrn = w.s([xwg, xn, u['rw'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, XR))
    k1 = w.s([u['kk'], xrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, XR, GK))
    k2 = w.s([u['kk'], txrw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, TXR, GK))
    dk1 = w.s([u['tv'], u['dd'], k1, w.inst('tm2stkupd')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, DK1, STK('T')))
    d1cl = upd2cl(w, ph, XR, SH, GK, GJ, u['tv'], u['dd'], u['kk'], u['jj'], xrw, shw)
    d2cl = upd2cl(w, ph, TXR, ACC, GK, GJ, u['tv'], u['dd'], u['kk'], u['jj'], txrw, accw)
    d2kcl = w.s([u['tv'], d1cl, k2, w.inst('tm2stkupd')], 'syl3anc',
                '( %s -> %s e. %s )' % (ph, D2K, STK('T')))
    rf = rfun(w, ph, u['ra'])
    lf = lfun(w, ph, u['lt'])
    n1ss = nclss(w, ph, 's')
    n2ss = nclss(w, ph, SACC)

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V')
        vn = w.s([], 'simpr', '( %s -> v e. %s )' % (av, NCL('s')))
        vv = w.s([vn, w.inst('elrabi')], 'syl', '( %s -> v e. %s )' % (av, S('T')))
        pre = outncl(w, av, 'v', 's', vn)
        kk = A_(u['kk'], 'K e. %s' % DG); jj = A_(u['jj'], 'J e. %s' % DG)
        ne = A_(u['ne'], 'K =/= J'); nes = A_(u['nes'], 'J =/= K')
        ra = A_(u['ra'], RATY); cc = A_(u['cc'], CTY); pp = A_(u['pp'], PTY)
        lt = A_(u['lt'], LTY)
        dd = A_(u['dd'], 'D e. %s' % STK('T')); qq = A_(u['qq'], 'Q e. %s' % STMT_T)
        hca = A_(u['hc'], HC); aa = A_(u['al'], 'A e. %s' % L('T'))
        faa = A_(fa, '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        gaa = A_(ga, '%s e. %s' % (GA, STMT_T)); lda = A_(ld, '%s e. %s' % (LOAD("F'", GA), STMT_T))
        pua = A_(pu, '%s e. %s' % (PU, STMT_T)); bra = A_(br, '%s e. %s' % (BR, STMT_T))
        d1 = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2 = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        d2k = A_(d2kcl, '%s e. %s' % (D2K, STK('T'))); dk1a = A_(dk1, '%s e. %s' % (DK1, STK('T')))
        xrwa = A_(xrw, '%s e. Word %s' % (XR, GK)); txrwa = A_(txrw, '%s e. Word %s' % (TXR, GK))
        shwa = A_(shw, '%s e. Word %s' % (SH, GJ)); accwa = A_(accw, '%s e. Word %s' % (ACC, GJ))
        xwga = A_(xwg, 'x e. Word %s' % GK); swga = A_(swg, 's e. Word %s' % GJ)
        rwa = A_(u['rw'], 'R e. Word %s' % GK); hwa = A_(u['hw'], 'H e. Word %s' % GJ)
        xna = A_(xn, 'x =/= (/)'); x0b = A_(x0, '%s e. B' % X0)
        swa = A_(sw, 's e. Word B')
        x0ka = A_(x0k, '%s e. %s' % (X0, GK)); s1ca = A_(s1c, '<" %s "> e. Word %s' % (X0, GJ))
        xrna = A_(xrn, '%s =/= (/)' % XR)
        rff = A_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        lff = A_(lf, "F' : %s --> %s" % (S('T'), S('T')))
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
        bc, pv, fl = hcinst(w, av, X0, 's', hca, vv, x0b, swa, pre)
        zil = w.s([x0ka, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (av, X0, OPT))
        op1 = w.s([vv, zil], 'opelxpd',
                  '( %s -> <. v , ( inl ` %s ) >. e. ( %s X. %s ) )' % (av, X0, S('T'), OPT))
        nvcl = w.s([rff, op1], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        lvcl = w.s([lff, nvcl], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, LV, S('T')))
        lvn = inncl(w, av, LV, SACC, lvcl, fl)
        avv = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, lvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), LV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv,
                 '%s e. %s' % (D1, STK('T')): d1, '%s e. %s' % (D2K, STK('T')): d2k,
                 '%s e. %s' % (D2, STK('T')): d2, '%s e. %s' % (NV, S('T')): nvcl,
                 '%s e. %s' % (LV, S('T')): lvcl,
                 'K e. %s' % DG: kk, 'J e. %s' % DG: jj, RATY: ra, CTY: cc, PTY: pp, LTY: lt,
                 '%s e. %s' % (BR, STMT_T): bra, '%s e. %s' % (PU, STMT_T): pua,
                 '%s e. %s' % (LOAD("F'", GA), STMT_T): lda,
                 '%s e. %s' % (GA, STMT_T): gaa, 'Q e. %s' % STMT_T: qq,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): faa}
        rules = {'( %s ` K )' % D1: (XR, rk), '( %s ` J )' % D2K: (SH, rj),
                 '( %s ` 0 )' % XR: (X0, rfv), TL(XR): (TXR, rtl),
                 '( <" %s "> ++ %s )' % (X0, SH): (ACC, asc),
                 '( P ` %s )' % NV: (X0, pv),
                 UPD('T', D2K, 'J', ACC): (D2, up4),
                 '( %s ` %s )' % (CONSTF('T', 'A'), LV): ('A', rga)}
        ifr = {'%s = (/)' % XR: (False, xnn), '( C ` %s ) = 1o' % NV: (True, bc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , %s >.' % D1)
        want_res = '<. ( inl ` A ) , <. %s , %s >. >.' % (LV, D2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), D1, STM, SA('T'), D1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), D1, res))
        return fin, LV, lvn
    hstepc2(w, ph, 'T', 'M', 'A', 'A', NCL('s'), NCL(SACC), D1, D2, (u['meq'], u['phm']),
            u['al'], u['al'], n1ss, n2ss, d1cl, d2cl, body, qed=True)
    return w.run()



def CLZ(X, Y, lb='A'):
    return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (lb, NCL(Y), UPD2('( %s ++ R )' % X, '( %s ++ H )' % Y))


JZS = ('( p e. _V |-> ( { ( inl ` A ) } X. ( %s X. { %s } ) ) )'
       % (NCL('( 2nd ` p )'), UPD2('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )')))


def rabex(w, ante, ss):
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ante, S('T')))
    return w.s([nclss(w, ante, ss), seva, w.inst('ssexg')], 'syl2anc',
               '( %s -> %s e. _V )' % (ante, NCL(ss)))


def jzs(w, ante, U, WW, ucl, wcl):
    """( ante -> ( JZS ` <. U , WW >. ) = CLZ(U, WW) )"""
    aq = '( %s /\\ p = <. %s , %s >. )' % (ante, U, WW)
    lp = w.s([], 'simpr', '( %s -> p = <. %s , %s >. )' % (aq, U, WW))
    body = ('( { ( inl ` A ) } X. ( %s X. { %s } ) )'
            % (NCL('( 2nd ` p )'), UPD2('( ( 1st ` p ) ++ R )', '( ( 2nd ` p ) ++ H )')))
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
    tgt = CLZ(U, WW)
    assert res == tgt, res
    h2 = w.s([st, ev], 'eqtrd', '( %s -> %s = %s )' % (aq, body, tgt))
    eqi = w.s([], 'eqid', '%s = %s' % (JZS, JZS))
    opv = w.s([], 'opex', '<. %s , %s >. e. _V' % (U, WW))
    opva = w.s([opv], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (ante, U, WW))
    sn1 = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    sn1a = w.s([sn1], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ante)
    UPS = UPD2('( %s ++ R )' % U, '( %s ++ H )' % WW)
    sn2 = w.s([], 'snex', '{ %s } e. _V' % UPS)
    sn2a = w.s([sn2], 'a1i', '( %s -> { %s } e. _V )' % (ante, UPS))
    rex = rabex(w, ante, WW)
    xp1 = w.s([rex, sn2a, w.inst('xpexg')], 'syl2anc',
              '( %s -> ( %s X. { %s } ) e. _V )' % (ante, NCL(WW), UPS))
    cex = w.s([sn1a, xp1, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ante, tgt))
    return w.s([h2, eqi, opva, cex], 'fvmptd2',
               '( %s -> ( %s ` <. %s , %s >. ) = %s )' % (ante, JZS, U, WW, tgt))


def tm2fzsw():
    lab = 'tm2fzsw'
    ph = '( %s /\\ ( W e. Word B /\\ U e. Word B ) )' % PH1
    phx = '( %s /\\ ( x e. Word B /\\ s e. Word B ) )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    X0 = '( x ` 0 )'
    ACCx = '( <" %s "> ++ s )' % X0
    HRx = HR('( %s ` <. x , s >. )' % JZS, 'T', 'M',
             '( %s ` <. %s , %s >. )' % (JZS, TL('x'), ACCx), '1')
    HYPJ = 'A. x e. Word B A. s e. Word B ( x =/= (/) -> %s )' % HRx
    ZCJ = 'A. s e. Word B ( %s ` <. (/) , s >. ) C_ %s' % (JZS, CFG('T'))
    CLx = CLZ('x', 's')
    CLt = CLZ(TL('x'), ACCx)
    w = W(lab, 'The scan loop of the fold mover: an instantiation of '
               '~ tm2hwrd2 whose invariant carries the accumulated word in both '
               'the destination stack and the internal state class, so that the '
               'fold ` O ` of the scanned letters is what the state class says '
               'at each step.  Lean: ` zeroScan_loop ` .')
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ante2, PH1))
    xw1 = w.s([], 'simplrl', '( %s -> x e. Word B )' % ante2)
    sw1 = w.s([], 'simplrr', '( %s -> s e. Word B )' % ante2)
    xn1 = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    one = w.s([], 'tm2fzs1', '( %s -> %s )' % (ante2, HR(CLx, 'T', 'M', CLt, '1')))
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    x01 = w.s([xw1, xn1, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B )' % (ante2, X0))
    s1c1 = w.s([x01], 's1cld', '( %s -> <" %s "> e. Word B )' % (ante2, X0))
    acw1 = w.s([s1c1, sw1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ante2, ACCx))
    jx = jzs(w, ante2, 'x', 's', xw1, sw1)
    jt = jzs(w, ante2, TL('x'), ACCx, tlw1, acw1)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` <. %s , %s >. ) , 1 >. = <. %s , 1 >. )'
             % (ante2, JZS, TL('x'), ACCx, CLt))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JZS, TL('x'), ACCx), '1'),
                HR(CLx, 'T', 'M', CLt, '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JZS, TL('x'), ACCx), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CLx, 'T', 'M', '( %s ` <. %s , %s >. )' % (JZS, TL('x'), ACCx), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    ex2 = w.s([ex1], 'anassrs',
              '( ( ( %s /\\ x e. Word B ) /\\ s e. Word B ) -> ( x =/= (/) -> %s ) )' % (PH1, HRx))
    ex3 = w.s([ex2], 'ralrimiva',
              '( ( %s /\\ x e. Word B ) -> A. s e. Word B ( x =/= (/) -> %s ) )' % (PH1, HRx))
    hyp = w.s([ex3], 'ralrimiva', '( %s -> %s )' % (PH1, HYPJ))
    hypa = w.s([hyp], 'adantr', '( %s -> %s )' % (ph, HYPJ))
    u = zctx(w, ph, 'adantr')
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
    jzs2 = jzs(w, phs, '(/)', 's', w0s, sws2)
    swj = w.s([bjs, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (phs, GJ))
    swg = w.s([swj, sws2], 'sseldd', '( %s -> s e. Word %s )' % (phs, GJ))
    z0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. Word %s )' % (phs, GK))
    zrw = w.s([z0a, rws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( (/) ++ R ) e. Word %s )' % (phs, GK))
    shw = w.s([swg, hws, w.inst('ccatcl')], 'syl2anc', '( %s -> ( s ++ H ) e. Word %s )' % (phs, GJ))
    ups = upd2cl(w, phs, '( (/) ++ R )', '( s ++ H )', GK, GJ, tvs, dds, kks, jjs, zrw, shw)
    UPS = UPD2('( (/) ++ R )', '( s ++ H )')
    sn = w.s([ups], 'snssd', '( %s -> { %s } C_ %s )' % (phs, UPS, STK('T')))
    xs = w.s([nclss(w, phs, 's'), sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ %s )' % (phs, NCL('s'), UPS, ST))
    cls = w.s([tvs, als, xs, w.inst('tm2hcfgss')], 'syl3anc',
              '( %s -> %s C_ %s )' % (phs, CLZ('(/)', 's'), CFG('T')))
    clj = w.s([jzs2, cls], 'eqsstrd', '( %s -> ( %s ` <. (/) , s >. ) C_ %s )' % (phs, JZS, CFG('T')))
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
              % (ph, HR('( %s ` <. W , U >. )' % JZS, 'T', 'M',
                        '( %s ` <. (/) , %s >. )' % (JZS, RV), '( ( # ` W ) x. 1 )')))
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    rvw = w.s([rvc, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, RV))
    w0b = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    jw = jzs(w, ph, 'W', 'U', ww, uu)
    jz = jzs(w, ph, '(/)', RV, w0b, rvw)
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    TGT0 = CLZ('(/)', RV)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` <. (/) , %s >. ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JZS, RV, TGT0))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JZS, 'T', 'M',
                       '( %s ` <. (/) , %s >. )' % (JZS, RV), '( ( # ` W ) x. 1 )'),
                HR('( %s ` <. W , U >. )' % JZS, 'T', 'M', TGT0, '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` <. W , U >. )' % JZS, 'T', 'M', TGT0, '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , U >. )' % JZS, 'T', 'M', TGT0, '( # ` W )'),
                HR(CLZ('W', 'U'), 'T', 'M', TGT0, '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )'
          % (ph, HR(CLZ('W', 'U'), 'T', 'M', TGT0, '( # ` W )')))
    return w.run()



HE = ("A. n e. %s ( -. ( C ` %s ) = 1o /\\ ( P' ` %s ) = ( P' ` n ) )"
      % (S('T'), NVF('n', 'Y'), NVF('n', 'Y')))
GEZ = GOTO(CONSTF('T', 'E'))
BR0Z = BRANCH('C', PU, GEZ)
STM0Z = POP('K', 'F', BR0Z)
LAB0 = ('( ( A e. %s /\\ E e. %s ) /\\ ( K e. %s /\\ J e. %s ) /\\ K =/= J )'
        % (L('T'), L('T'), DG, DG))
WTYF = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
        % (GK, GJ, GK, GK, GJ, STK('T')))
QTYF = '( %s /\\ ( %s /\\ %s ) )' % (LTY, HC, HE)
PHF = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )'
       % (PHM, STM0Z, LAB0, FTY, WTYF, QTYF))


def tm2fzs():
    lab = 'tm2fzs'
    ph = '( %s /\\ ( W e. Word B /\\ U e. Word B ) )' % PHF
    ZXY = '( <" Y "> ++ X )'
    RV = '( ( reverse ` W ) ++ U )'
    RVH = '( %s ++ H )' % RV
    w = W(lab, 'The fold mover: the top number of stack ` K ` is moved onto '
               'stack ` J ` reversed, each letter folded into the internal '
               'state by ` O ` , and the terminator ` Y ` is consumed.  At the '
               'exit the state class says the fold of the whole word: Lean\'s '
               '` zeroScan_runs ` , whose ` flag = zeroBits l v.flag ` is this '
               'statement at ` O ` the fold and ` P\' ` the flag.')
    phm0 = w.s([], 'simp1l', '( %s -> %s )' % (PHF, PHM))
    meq0 = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHF, STM0Z))
    lab0 = w.s([], 'simp2', '( %s -> %s )' % (PHF, LAB0))
    p30 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ %s ) )' % (PHF, FTY, WTYF, QTYF))
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm0, PHM); meq = A_(meq0, '( M ` A ) = %s' % STM0Z)
    lab2 = A_(lab0, LAB0); p3 = A_(p30, '( %s /\\ %s /\\ %s )' % (FTY, WTYF, QTYF))
    ww = w.s([], 'simprl', '( %s -> W e. Word B )' % ph)
    uu = w.s([], 'simprr', '( %s -> U e. Word B )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    ra = w.s([ft, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([ft, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    pp = w.s([ft, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTYF))
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ))
    bk = w.s([b2], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    bj = w.s([b2], 'simprd', '( %s -> B C_ %s )' % (ph, GJ))
    w3 = w.s([wt, w.inst('simp2')], 'syl',
             '( %s -> ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) )' % (ph, GK, GK, GJ))
    yy = w.s([w3, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([w3, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    hw = w.s([w3, w.inst('simp3')], 'syl', '( %s -> H e. Word %s )' % (ph, GJ))
    dd = w.s([wt, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    qt = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, QTYF))
    lt = w.s([qt], 'simpld', '( %s -> %s )' % (ph, LTY))
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
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GEZ, STMT_T))
    # ---- the loop, at R := ( <" Y "> ++ X ) and Q := goto E
    labm = w.s([al, kj2, ne], '3jca', '( %s -> %s )' % (ph, LAB))
    WTYi = ('( ( B C_ %s /\\ B C_ %s ) /\\ ( %s e. Word %s /\\ H e. Word %s ) /\\ D e. %s )'
            % (GK, GJ, ZXY, GK, GJ, STK('T')))
    wtym = w.s([b2, w.s([zxw, hw], 'jca', '( %s -> ( %s e. Word %s /\\ H e. Word %s ) )'
                        % (ph, ZXY, GK, GJ)), dd], '3jca', '( %s -> %s )' % (ph, WTYi))
    gl = w.s([ge, lt], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (ph, GEZ, STMT_T, LTY))
    qtym = w.s([gl, hc], 'jca', '( %s -> ( ( %s e. %s /\\ %s ) /\\ %s ) )' % (ph, GEZ, STMT_T, LTY, HC))
    pm1 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STM0Z))
    pm3 = w.s([ft, wtym, qtym], '3jca',
              '( %s -> ( %s /\\ %s /\\ ( ( %s e. %s /\\ %s ) /\\ %s ) ) )'
              % (ph, FTY, WTYi, GEZ, STMT_T, LTY, HC))
    PH1i = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( ( %s e. %s /\\ %s ) /\\ %s ) ) )'
            % (PHM, STM0Z, LAB, FTY, WTYi, GEZ, STMT_T, LTY, HC))
    pmi = w.s([pm1, labm, pm3], '3jca', '( %s -> %s )' % (ph, PH1i))
    wu = w.s([ww, uu], 'jca', '( %s -> ( W e. Word B /\\ U e. Word B ) )' % ph)
    ant = w.s([pmi, wu], 'jca', '( %s -> ( %s /\\ ( W e. Word B /\\ U e. Word B ) ) )' % (ph, PH1i))
    CL0 = ('( { ( inl ` A ) } X. ( %s X. { %s } ) )'
           % (NCL('U'), UPD2('( W ++ %s )' % ZXY, '( U ++ H )')))
    CL1 = ('( { ( inl ` A ) } X. ( %s X. { %s } ) )'
           % (NCL(RV), UPD2('( (/) ++ %s )' % ZXY, '( %s ++ H )' % RV)))
    loop = w.s([ant, w.inst('tm2fzsw')], 'syl', '( %s -> %s )' % (ph, HR(CL0, 'T', 'M', CL1, '( # ` W )')))
    lid = w.s([zxw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, ZXY, ZXY))
    c1s, n1 = w.rewrite(CL1, {'( (/) ++ %s )' % ZXY: (ZXY, lid)}, ph)
    DST = UPD2(ZXY, RVH)
    CL1b = '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (NCL(RV), DST)
    assert n1 == CL1b, n1
    o1 = w.s([c1s], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )' % (ph, CL1, CL1b))
    b1 = w.s([o1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CL0, 'T', 'M', CL1, '( # ` W )'), HR(CL0, 'T', 'M', CL1b, '( # ` W )')))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )' % (ph, HR(CL0, 'T', 'M', CL1b, '( # ` W )')))
    # ---- the exit, by tm2fpb0 at D := DST and N := NCL(RV)
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    rvw = w.s([rvc, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (ph, RV))
    swj = w.s([bj, w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GJ))
    rvg = w.s([swj, rvw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, RV, GJ))
    rvh = w.s([rvg, hw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RVH, GJ))
    dstcl = upd2cl(w, ph, ZXY, RVH, GK, GJ, tv, dd, kk, jj, zxw, rvh)
    DK1 = UPD('T', 'D', 'K', ZXY)
    k1 = w.s([kk, zxw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, ZXY, GK))
    dk1 = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DK1, STK('T')))
    a1 = updn(w, ph, DK1, 'J', RVH, 'Word %s' % GJ, 'K', tv, dk1, jj, rvh, kk, ne)
    zxv = w.s([zxw], 'elexd', '( %s -> %s e. _V )' % (ph, ZXY))
    a2 = updkval(w, ph, 'T', 'D', 'K', ZXY, tv, dd, kk, zxv)
    dstk = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, DST, ZXY))
    # the exit interface on the class NCL(RV)
    an = '( %s /\\ u e. %s )' % (ph, NCL(RV))
    mn = w.s([], 'simpr', '( %s -> u e. %s )' % (an, NCL(RV)))
    ms = w.s([mn, w.inst('elrabi')], 'syl', '( %s -> u e. %s )' % (an, S('T')))
    mval = outncl(w, an, 'u', RV, mn)
    hea = w.s([he], 'adantr', '( %s -> %s )' % (an, HE))
    PAIR = lambda x: "( -. ( C ` %s ) = 1o /\\ ( P' ` %s ) = ( P' ` %s ) )" % (NVF(x, 'Y'), NVF(x, 'Y'), x)
    cg, new = W.wcongr(w, PAIR('n'), {'n': 'u'}, 'n = u',
                       {'n': w.s([], 'id', '( n = u -> n = u )')})
    assert new == PAIR('u'), new
    h2 = w.s([cg, hea, ms], 'rspcdva', '( %s -> %s )' % (an, PAIR('u')))
    rc = w.s([h2], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (an, NVF('u', 'Y')))
    pv = w.s([h2], 'simprd', "( %s -> ( P' ` %s ) = ( P' ` u ) )" % (an, NVF('u', 'Y')))
    pv2 = w.s([pv, mval], 'eqtrd', "( %s -> ( P' ` %s ) = ( O ` %s ) )" % (an, NVF('u', 'Y'), RV))
    rfa = w.s([rfun(w, ph, ra)], 'adantr', '( %s -> F : ( %s X. %s ) --> %s )' % (an, S('T'), OPT, S('T')))
    yya = w.s([yy], 'adantr', '( %s -> Y e. %s )' % (an, GK))
    yil = w.s([yya, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. %s )' % (an, OPT))
    opm = w.s([ms, yil], 'opelxpd', '( %s -> <. u , ( inl ` Y ) >. e. ( %s X. %s ) )' % (an, S('T'), OPT))
    nvs = w.s([rfa, opm], 'ffvelcdmd', '( %s -> %s e. %s )' % (an, NVF('u', 'Y'), S('T')))
    nvn = inncl(w, an, NVF('u', 'Y'), RV, nvs, pv2)
    PRB = lambda x: ('( -. ( C ` %s ) = 1o /\\ %s e. %s )' % (NVF(x, 'Y'), NVF(x, 'Y'), NCL(RV)))
    pr = w.s([rc, nvn], 'jca', '( %s -> %s )' % (an, PRB('u')))
    hexu = w.s([pr], 'ralrimiva', '( %s -> A. u e. %s %s )' % (ph, NCL(RV), PRB('u')))
    cg2, new2 = W.wcongr(w, PRB('u'), {'u': 'm'}, 'u = m',
                         {'u': w.s([], 'id', '( u = m -> u = m )')})
    assert new2 == PRB('m'), new2
    HEX = 'A. m e. %s %s' % (NCL(RV), PRB('m'))
    cb2 = w.s([cg2], 'cbvralvw', '( A. u e. %s %s <-> %s )' % (NCL(RV), PRB('u'), HEX))
    cb2a = w.s([cb2], 'a1i', '( %s -> ( A. u e. %s %s <-> %s ) )' % (ph, NCL(RV), PRB('u'), HEX))
    hex = w.s([cb2a, hexu], 'mpbid', '( %s -> %s )' % (ph, HEX))
    # tm2fpb0's antecedent
    lb0 = w.s([al, el, kk], '3jca', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )'
              % (ph, L('T'), L('T'), DG))
    fa0 = constfty(w, ph, 'A', L('T'), al)
    ga0 = w.s([tv, fa0, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ld0 = w.s([tv, lt, ga0, w.inst('tm2load')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, LOAD("F'", GA), STMT_T))
    jp0 = w.s([jj, pp], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu0 = w.s([tv, jp0, ld0, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    ft0 = w.s([ra, cc, pu0], '3jca', '( %s -> ( %s /\\ %s /\\ %s e. %s ) )' % (ph, RATY, CTY, PU, STMT_T))
    l2 = w.s([lb0, ft0], 'jca', '( %s -> ( ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s /\\ %s e. %s ) ) )'
             % (ph, L('T'), L('T'), DG, RATY, CTY, PU, STMT_T))
    yx0 = w.s([yy, xx], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (ph, GK, GK))
    d30 = w.s([dstcl, dstk, yx0], '3jca',
              '( %s -> ( %s e. %s /\\ ( %s ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) )'
              % (ph, DST, STK('T'), DST, ZXY, GK, GK))
    nh0 = w.s([nclss(w, ph, RV), hex], 'jca', '( %s -> ( %s C_ %s /\\ %s ) )'
              % (ph, NCL(RV), S('T'), HEX))
    s30 = w.s([d30, nh0], 'jca',
              '( %s -> ( ( %s e. %s /\\ ( %s ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) /\\ ( %s C_ %s /\\ %s ) ) )'
              % (ph, DST, STK('T'), DST, ZXY, GK, GK, NCL(RV), S('T'), HEX))
    pm10 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STM0Z))
    ant0 = w.s([pm10, l2, s30], '3jca', '( %s -> ( ( %s /\\ ( M ` A ) = %s ) /\\ '
               '( ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s /\\ %s e. %s ) ) /\\ '
               '( ( %s e. %s /\\ ( %s ` K ) = %s /\\ ( Y e. %s /\\ X e. Word %s ) ) /\\ ( %s C_ %s /\\ %s ) ) ) )'
               % (ph, PHM, STM0Z, L('T'), L('T'), DG, RATY, CTY, PU, STMT_T,
                  DST, STK('T'), DST, ZXY, GK, GK, NCL(RV), S('T'), HEX))
    CLE = '( { ( inl ` E ) } X. ( %s X. { %s } ) )' % (NCL(RV), UPD('T', DST, 'K', 'X'))
    exit_ = w.s([ant0, w.inst('tm2fpb0')], 'syl', '( %s -> %s )' % (ph, HR(CL1b, 'T', 'M', CLE, '1')))
    # the three updates collapse
    tdj = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK('T'))), ne],
              'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (ph, STK('T')))
    pk2 = w.s([kk, w.s([zxw, xx], 'jca', '( %s -> ( %s e. Word %s /\\ X e. Word %s ) )'
                       % (ph, ZXY, GK, GK))], 'jca',
              '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ X e. Word %s ) ) )' % (ph, DG, ZXY, GK, GK))
    pj1 = w.s([jj, rvh], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, RVH, GJ))
    up3 = w.s([tdj, pk2, pj1, w.inst('tm2stkup3')], 'syl3anc',
              '( %s -> %s = %s )' % (ph, UPD('T', DST, 'K', 'X'), UPD2('X', RVH)))
    CLE2 = '( { ( inl ` E ) } X. ( %s X. { %s } ) )' % (NCL(RV), UPD2('X', RVH))
    cs2, n2 = w.rewrite(CLE, {UPD('T', DST, 'K', 'X'): (UPD2('X', RVH), up3)}, ph)
    assert n2 == CLE2, n2
    o2 = w.s([cs2], 'opeq1d', '( %s -> <. %s , 1 >. = <. %s , 1 >. )' % (ph, CLE, CLE2))
    b2b = w.s([o2], 'breq2d', '( %s -> ( %s <-> %s ) )'
              % (ph, HR(CL1b, 'T', 'M', CLE, '1'), HR(CL1b, 'T', 'M', CLE2, '1')))
    exit2 = w.s([b2b, exit_], 'mpbid', '( %s -> %s )' % (ph, HR(CL1b, 'T', 'M', CLE2, '1')))
    w.qed([phm, loop2, exit2], 'syl3anc', '( %s -> %s )'
          % (ph, HR(CL0, 'T', 'M', CLE2, '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fpb0'): tm2fpb0()
    if want('tm2fzs1'): tm2fzs1()
    if want('tm2fzsw'): tm2fzsw()
    if want('tm2fzs'): tm2fzs()
