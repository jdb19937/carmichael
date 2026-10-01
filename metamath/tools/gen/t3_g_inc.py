"""T3: the exit steps of a three-way pop-branch loop --- the two exits of
`incLoop` (TM/Prims.lean, blueprint 4.6): the popped letter is not the one the
carry chain continues on, so the machine pushes on the *source* stack and
leaves."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty, OPT, RATY, CTY, DG, GK, STMT_T, NVF

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GE = GOTO(CONSTF('T', 'E'))
CTY2 = "C' e. ( 2o ^m %s )" % S('T')
PKTY = 'P e. ( %s ^m %s )' % (GK, S('T'))
PKTY2 = "P' e. ( %s ^m %s )" % (GK, S('T'))
NSS = 'N C_ %s' % S('T')
ZX = '( <" Z "> ++ X )'
LABTY = '( A e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), DG)


def prelude(w, ph, STM, FUNTY, STKTY, HE, LETS, zx=None):
    """the shared context; LETS is the letters conjunct of STKTY"""
    zx = zx or ZX
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    lb = w.s([], 'simp2l', '( %s -> %s )' % (ph, LABTY))
    al = w.s([lb, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lb, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([lb, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    ft = w.s([], 'simp2r', '( %s -> %s )' % (ph, FUNTY))
    dk = w.s([], 'simp3l', '( %s -> %s )' % (ph, STKTY))
    dd = w.s([dk, w.inst('simp1')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    dke = w.s([dk, w.inst('simp2')], 'syl', '( %s -> ( D ` K ) = %s )' % (ph, zx))
    lets = w.s([dk, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, LETS))
    nh = w.s([], 'simp3r', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HE))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    return dict(phm=phm, meq=meq, al=al, el=el, kk=kk, ft=ft, dd=dd, dke=dke, lets=lets,
                nss=nss, he=he, tv=tv, fe=fe, ge=ge)


def stkwork(w, ph, u, zz, xx):
    """the nonemptiness of ( <" Z "> ++ X ) and the tail update"""
    s1c = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ph, GK))
    s1n = w.s([], 's1nz', '<" Z "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Z "> =/= (/) )' % ph)
    zxn = w.s([s1c, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, ZX))
    D1 = UPD('T', 'D', 'K', 'X')
    kx = w.s([u['kk'], xx], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (ph, DG, GK))
    d1cl = w.s([u['tv'], u['dd'], kx, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, D1, STK('T')))
    return zxn, D1, d1cl


def updcl(w, ph, u, WD, wdcl):
    kj = w.s([u['kk'], wdcl], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, WD, GK))
    return w.s([u['tv'], u['dd'], kj, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', WD), STK('T')))


def popr(w, av, u, A_, zz, xx, zxn):
    """the head/tail rules at the popped letter Z"""
    zxna = A_(zxn, '%s =/= (/)' % ZX)
    zxnn = w.s([zxna], 'neneqd', '( %s -> -. %s = (/) )' % (av, ZX))
    zj = w.s([A_(zz, 'Z e. %s' % GK), A_(xx, 'X e. Word %s' % GK)], 'jca',
             '( %s -> ( Z e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
    zfv = w.s([zj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Z )' % (av, ZX))
    ztl = w.s([zj, w.inst('wrdtls1')], 'syl',
              '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = X )' % (av, ZX, ZX))
    return zxnn, zfv, ztl


def heat(w, av, u, HEB, A_, HE):
    hea = A_(u['he'], HE)
    vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
    cg, new = W.wcongr(w, HEB('m'), {'m': 'v'}, 'm = v',
                       {'m': w.s([], 'id', '( m = v -> m = v )')})
    assert new == HEB('v'), new
    return vn, w.s([cg, hea, vn], 'rspcdva', '( %s -> %s )' % (av, HEB('v')))


def in0frag(lab, ctrue=True, desc=None):
    PU1 = PUSH('K', 'P', GE)
    BR2 = BRANCH("C'", PU1, 'R') if ctrue else BRANCH("C'", 'R', PU1)
    BR1 = BRANCH('C', 'Q', BR2)
    STM = POP('K', 'F', BR1)
    ZPX = "( <\" Z' \"> ++ X )"
    D2 = UPD('T', 'D', 'K', ZPX)
    NV = NVF('v', 'Z')
    NEG = '' if ctrue else '-. '
    HEB = lambda m: ("( -. ( C ` %s ) = 1o /\\ %s( C' ` %s ) = 1o /\\ ( ( P ` %s ) = Z' /\\ %s e. N ) )"
                     % (NVF(m, 'Z'), NEG, NVF(m, 'Z'), NVF(m, 'Z'), NVF(m, 'Z')))
    HE = 'A. m e. N %s' % HEB('m')
    LETS = "( ( Z e. %s /\\ Z' e. %s ) /\\ X e. Word %s )" % (GK, GK, GK)
    FUNTY = ('( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ ( Q e. %s /\\ R e. %s ) ) )'
             % (RATY, CTY, CTY2, PKTY, STMT_T, STMT_T))
    STKTY = '( D e. %s /\\ ( D ` K ) = %s /\\ %s )' % (STK('T'), ZX, LETS)
    ph = ("( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )"
          % (PHM, STM, LABTY, FUNTY, STKTY, NSS, HE))
    w = W(lab, desc)
    u = prelude(w, ph, STM, FUNTY, STKTY, HE, LETS)
    z2 = w.s([u['lets']], 'simpld', "( %s -> ( Z e. %s /\\ Z' e. %s ) )" % (ph, GK, GK))
    zz = w.s([z2], 'simpld', '( %s -> Z e. %s )' % (ph, GK))
    zp = w.s([z2], 'simprd', "( %s -> Z' e. %s )" % (ph, GK))
    xx = w.s([u['lets']], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    zxn, D1, d1cl = stkwork(w, ph, u, zz, xx)
    s1zp = w.s([zp], 's1cld', "( %s -> <\" Z' \"> e. Word %s )" % (ph, GK))
    zpxw = w.s([s1zp, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZPX, GK))
    d2cl = updcl(w, ph, u, ZPX, zpxw)
    f3 = w.s([u['ft']], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RATY, CTY, CTY2))
    ra = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, CTY2))
    f4 = w.s([u['ft']], 'simprd', '( %s -> ( %s /\\ ( Q e. %s /\\ R e. %s ) ) )'
             % (ph, PKTY, STMT_T, STMT_T))
    pk = w.s([f4], 'simpld', '( %s -> %s )' % (ph, PKTY))
    qr = w.s([f4], 'simprd', '( %s -> ( Q e. %s /\\ R e. %s ) )' % (ph, STMT_T, STMT_T))
    qq = w.s([qr], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    rr = w.s([qr], 'simprd', '( %s -> R e. %s )' % (ph, STMT_T))
    kp = w.s([u['kk'], pk], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, PKTY))
    pu1 = w.s([u['tv'], kp, u['ge'], w.inst('tm2push')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, PU1, STMT_T))
    if ctrue:
        pr = w.s([pu1, rr], 'jca', '( %s -> ( %s e. %s /\\ R e. %s ) )' % (ph, PU1, STMT_T, STMT_T))
    else:
        pr = w.s([rr, pu1], 'jca', '( %s -> ( R e. %s /\\ %s e. %s ) )' % (ph, STMT_T, PU1, STMT_T))
    br2 = w.s([u['tv'], c2, pr, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR2, STMT_T))
    qb = w.s([qq, br2], 'jca', '( %s -> ( Q e. %s /\\ %s e. %s ) )' % (ph, STMT_T, BR2, STMT_T))
    br1 = w.s([u['tv'], cc, qb, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR1, STMT_T))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V'); dd = A_(u['dd'], 'D e. %s' % STK('T'))
        raa = A_(ra, RATY); cca = A_(cc, CTY); c2a = A_(c2, CTY2); pka = A_(pk, PKTY)
        qqa = A_(qq, 'Q e. %s' % STMT_T); rra = A_(rr, 'R e. %s' % STMT_T)
        gea = A_(u['ge'], '%s e. %s' % (GE, STMT_T)); kka = A_(u['kk'], 'K e. %s' % DG)
        br1a = A_(br1, '%s e. %s' % (BR1, STMT_T)); br2a = A_(br2, '%s e. %s' % (BR2, STMT_T))
        pu1a = A_(pu1, '%s e. %s' % (PU1, STMT_T)); ela = A_(u['el'], 'E e. %s' % L('T'))
        fea = A_(u['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        d1a = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        dkea = A_(u['dke'], '( D ` K ) = %s' % ZX)
        xxa = A_(xx, 'X e. Word %s' % GK); nssa = A_(u['nss'], NSS)
        zpxa = A_(zpxw, '%s e. Word %s' % (ZPX, GK))
        zxnn, zfv, ztl = popr(w, av, u, A_, zz, xx, zxn)
        vn, trip = heat(w, av, u, HEB, A_, HE)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        cq = w.s([trip, w.inst('simp1')], 'syl', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        c2q = w.s([trip, w.inst('simp2')], 'syl', "( %s -> %s( C' ` %s ) = 1o )" % (av, NEG, NV))
        pz = w.s([trip, w.inst('simp3')], 'syl',
                 "( %s -> ( ( P ` %s ) = Z' /\\ %s e. N ) )" % (av, NV, NV))
        pq = w.s([pz], 'simpld', "( %s -> ( P ` %s ) = Z' )" % (av, NV))
        nvn = w.s([pz], 'simprd', '( %s -> %s e. N )' % (av, NV))
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        xv = w.s([xxa], 'elexd', '( %s -> X e. _V )' % av)
        d1k = updkval(w, av, 'T', 'D', 'K', 'X', tv, dd, kka, xv)
        tdk = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        kxx = w.s([xxa, zpxa], 'jca',
                   '( %s -> ( X e. Word %s /\\ %s e. Word %s ) )' % (av, GK, ZPX, GK))
        up2 = w.s([tdk, kka, kxx, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', ZPX), D2))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '%s e. %s' % (NV, S('T')): nvcl,
                 'D e. %s' % STK('T'): dd, '%s e. %s' % (D1, STK('T')): d1a,
                 '%s e. %s' % (D2, STK('T')): d2a,
                 RATY: raa, CTY: cca, CTY2: c2a, PKTY: pka,
                 'Q e. %s' % STMT_T: qqa, 'R e. %s' % STMT_T: rra,
                 '%s e. %s' % (BR1, STMT_T): br1a, '%s e. %s' % (BR2, STMT_T): br2a,
                 '%s e. %s' % (PU1, STMT_T): pu1a, '%s e. %s' % (GE, STMT_T): gea,
                 'K e. %s' % DG: kka,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( D ` K )': (ZX, dkea), '( %s ` 0 )' % ZX: ('Z', zfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (ZX, ZX): ('X', ztl),
                 '( %s ` K )' % D1: ('X', d1k), '( P ` %s )' % NV: ("Z'", pq),
                 UPD('T', D1, 'K', ZPX): (D2, up2),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NV): ('E', rge)}
        ifr = {'%s = (/)' % ZX: (False, zxnn), '( C ` %s ) = 1o' % NV: (False, cq),
               "( C' ` %s ) = 1o" % NV: (ctrue, c2q)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, NV, nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', D2, (u['meq'], u['phm']),
            u['al'], u['el'], u['nss'], u['nss'], u['dd'], d2cl, body, qed=True)
    return w.run()



def tm2fin0t():
    lab = 'tm2fin0t'
    PU1 = PUSH('K', 'P', GE)
    PU2 = PUSH('K', "P'", PU1)
    BR2 = BRANCH("C'", 'R', PU2)
    BR1 = BRANCH('C', 'Q', BR2)
    STM = POP('K', 'F', BR1)
    ZZX = "( <\" Z\" \"> ++ X )"
    ZPZX = "( <\" Z' \"> ++ %s )" % ZZX
    DA = UPD('T', 'D', 'K', ZZX)
    D2 = UPD('T', 'D', 'K', ZPZX)
    NV = NVF('v', 'Z')
    HEB = lambda m: ("( ( -. ( C ` %s ) = 1o /\\ -. ( C' ` %s ) = 1o ) /\\ "
                     "( ( ( P ` %s ) = Z' /\\ ( P' ` %s ) = Z\" ) /\\ %s e. N ) )"
                     % (NVF(m, 'Z'), NVF(m, 'Z'), NVF(m, 'Z'), NVF(m, 'Z'), NVF(m, 'Z')))
    HE = 'A. m e. N %s' % HEB('m')
    LETS = "( ( Z e. %s /\\ Z' e. %s /\\ Z\" e. %s ) /\\ X e. Word %s )" % (GK, GK, GK, GK)
    FUNTY = ('( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( Q e. %s /\\ R e. %s ) ) )'
             % (RATY, CTY, CTY2, PKTY, PKTY2, STMT_T, STMT_T))
    STKTY = '( D e. %s /\\ ( D ` K ) = %s /\\ %s )' % (STK('T'), ZX, LETS)
    ph = ("( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )"
          % (PHM, STM, LABTY, FUNTY, STKTY, NSS, HE))
    w = W(lab, 'The second exit of a three-way pop-branch loop: the popped letter '
               '` Z ` fails both tests, so the machine pushes two letters on the '
               'source stack ` K ` and leaves.  Lean: ` incLoop_loop ` case 1 --- '
               'the terminator is pushed back and a one above it, which is the '
               'carry running off the top of the number.  The continue branch '
               '` Q ` and the middle branch ` R ` are class variables.')
    u = prelude(w, ph, STM, FUNTY, STKTY, HE, LETS)
    z3 = w.s([u['lets']], 'simpld', "( %s -> ( Z e. %s /\\ Z' e. %s /\\ Z\" e. %s ) )" % (ph, GK, GK, GK))
    zz = w.s([z3, w.inst('simp1')], 'syl', '( %s -> Z e. %s )' % (ph, GK))
    zp = w.s([z3, w.inst('simp2')], 'syl', "( %s -> Z' e. %s )" % (ph, GK))
    zq = w.s([z3, w.inst('simp3')], 'syl', "( %s -> Z\" e. %s )" % (ph, GK))
    xx = w.s([u['lets']], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    zxn, D1, d1cl = stkwork(w, ph, u, zz, xx)
    s1zq = w.s([zq], 's1cld', "( %s -> <\" Z\" \"> e. Word %s )" % (ph, GK))
    zzxw = w.s([s1zq, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZZX, GK))
    s1zp = w.s([zp], 's1cld', "( %s -> <\" Z' \"> e. Word %s )" % (ph, GK))
    zpzxw = w.s([s1zp, zzxw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZPZX, GK))
    dacl = updcl(w, ph, u, ZZX, zzxw)
    d2cl = updcl(w, ph, u, ZPZX, zpzxw)
    f3 = w.s([u['ft']], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RATY, CTY, CTY2))
    ra = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    cc = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, CTY2))
    f4 = w.s([u['ft']], 'simprd', '( %s -> ( ( %s /\\ %s ) /\\ ( Q e. %s /\\ R e. %s ) ) )'
             % (ph, PKTY, PKTY2, STMT_T, STMT_T))
    p2 = w.s([f4], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, PKTY, PKTY2))
    pk = w.s([p2], 'simpld', '( %s -> %s )' % (ph, PKTY))
    pk2 = w.s([p2], 'simprd', '( %s -> %s )' % (ph, PKTY2))
    qr = w.s([f4], 'simprd', '( %s -> ( Q e. %s /\\ R e. %s ) )' % (ph, STMT_T, STMT_T))
    qq = w.s([qr], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    rr = w.s([qr], 'simprd', '( %s -> R e. %s )' % (ph, STMT_T))
    kp = w.s([u['kk'], pk], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, PKTY))
    pu1 = w.s([u['tv'], kp, u['ge'], w.inst('tm2push')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, PU1, STMT_T))
    kp2 = w.s([u['kk'], pk2], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, PKTY2))
    pu2 = w.s([u['tv'], kp2, pu1, w.inst('tm2push')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, PU2, STMT_T))
    rp = w.s([rr, pu2], 'jca', '( %s -> ( R e. %s /\\ %s e. %s ) )' % (ph, STMT_T, PU2, STMT_T))
    br2 = w.s([u['tv'], c2, rp, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR2, STMT_T))
    qb = w.s([qq, br2], 'jca', '( %s -> ( Q e. %s /\\ %s e. %s ) )' % (ph, STMT_T, BR2, STMT_T))
    br1 = w.s([u['tv'], cc, qb, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR1, STMT_T))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V'); dd = A_(u['dd'], 'D e. %s' % STK('T'))
        raa = A_(ra, RATY); cca = A_(cc, CTY); c2a = A_(c2, CTY2)
        pka = A_(pk, PKTY); pk2a = A_(pk2, PKTY2)
        qqa = A_(qq, 'Q e. %s' % STMT_T); rra = A_(rr, 'R e. %s' % STMT_T)
        gea = A_(u['ge'], '%s e. %s' % (GE, STMT_T)); kka = A_(u['kk'], 'K e. %s' % DG)
        br1a = A_(br1, '%s e. %s' % (BR1, STMT_T)); br2a = A_(br2, '%s e. %s' % (BR2, STMT_T))
        pu1a = A_(pu1, '%s e. %s' % (PU1, STMT_T)); pu2a = A_(pu2, '%s e. %s' % (PU2, STMT_T))
        ela = A_(u['el'], 'E e. %s' % L('T'))
        fea = A_(u['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        d1a = A_(d1cl, '%s e. %s' % (D1, STK('T'))); daa = A_(dacl, '%s e. %s' % (DA, STK('T')))
        d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        dkea = A_(u['dke'], '( D ` K ) = %s' % ZX)
        xxa = A_(xx, 'X e. Word %s' % GK); nssa = A_(u['nss'], NSS)
        zzxa = A_(zzxw, '%s e. Word %s' % (ZZX, GK)); zpzxa = A_(zpzxw, '%s e. Word %s' % (ZPZX, GK))
        zxnn, zfv, ztl = popr(w, av, u, A_, zz, xx, zxn)
        vn, trip = heat(w, av, u, HEB, A_, HE)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        t1 = w.s([trip], 'simpld', "( %s -> ( -. ( C ` %s ) = 1o /\\ -. ( C' ` %s ) = 1o ) )" % (av, NV, NV))
        cq = w.s([t1], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        c2q = w.s([t1], 'simprd', "( %s -> -. ( C' ` %s ) = 1o )" % (av, NV))
        t2 = w.s([trip], 'simprd',
                 "( %s -> ( ( ( P ` %s ) = Z' /\\ ( P' ` %s ) = Z\" ) /\\ %s e. N ) )" % (av, NV, NV, NV))
        t3 = w.s([t2], 'simpld', "( %s -> ( ( P ` %s ) = Z' /\\ ( P' ` %s ) = Z\" ) )" % (av, NV, NV))
        pq = w.s([t3], 'simpld', "( %s -> ( P ` %s ) = Z' )" % (av, NV))
        pq2 = w.s([t3], 'simprd', "( %s -> ( P' ` %s ) = Z\" )" % (av, NV))
        nvn = w.s([t2], 'simprd', '( %s -> %s e. N )' % (av, NV))
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        xv = w.s([xxa], 'elexd', '( %s -> X e. _V )' % av)
        d1k = updkval(w, av, 'T', 'D', 'K', 'X', tv, dd, kka, xv)
        zzxv = w.s([zzxa], 'elexd', '( %s -> %s e. _V )' % (av, ZZX))
        dak = updkval(w, av, 'T', 'D', 'K', ZZX, tv, dd, kka, zzxv)
        tdk = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        k1 = w.s([xxa, zzxa], 'jca', '( %s -> ( X e. Word %s /\\ %s e. Word %s ) )' % (av, GK, ZZX, GK))
        upa = w.s([tdk, kka, k1, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', ZZX), DA))
        k2 = w.s([zzxa, zpzxa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                 % (av, ZZX, GK, ZPZX, GK))
        upb = w.s([tdk, kka, k2, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', DA, 'K', ZPZX), D2))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '%s e. %s' % (NV, S('T')): nvcl,
                 'D e. %s' % STK('T'): dd, '%s e. %s' % (D1, STK('T')): d1a,
                 '%s e. %s' % (DA, STK('T')): daa, '%s e. %s' % (D2, STK('T')): d2a,
                 RATY: raa, CTY: cca, CTY2: c2a, PKTY: pka, PKTY2: pk2a,
                 'Q e. %s' % STMT_T: qqa, 'R e. %s' % STMT_T: rra,
                 '%s e. %s' % (BR1, STMT_T): br1a, '%s e. %s' % (BR2, STMT_T): br2a,
                 '%s e. %s' % (PU1, STMT_T): pu1a, '%s e. %s' % (PU2, STMT_T): pu2a,
                 '%s e. %s' % (GE, STMT_T): gea, 'K e. %s' % DG: kka,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( D ` K )': (ZX, dkea), '( %s ` 0 )' % ZX: ('Z', zfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (ZX, ZX): ('X', ztl),
                 '( %s ` K )' % D1: ('X', d1k), '( %s ` K )' % DA: (ZZX, dak),
                 '( P ` %s )' % NV: ("Z'", pq), "( P' ` %s )" % NV: ('Z"', pq2),
                 UPD('T', D1, 'K', ZZX): (DA, upa), UPD('T', DA, 'K', ZPZX): (D2, upb),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NV): ('E', rge)}
        ifr = {'%s = (/)' % ZX: (False, zxnn), '( C ` %s ) = 1o' % NV: (False, cq),
               "( C' ` %s ) = 1o" % NV: (False, c2q)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, NV, nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', D2, (u['meq'], u['phm']),
            u['al'], u['el'], u['nss'], u['nss'], u['dd'], d2cl, body, qed=True)
    return w.run()


D_IN0 = ('The first exit of a three-way pop-branch loop: the popped letter '
         '` Z ` fails the first test and passes the second, so the machine '
         "pushes ` Z' ` on the source stack ` K ` in its place and leaves.  "
         'Lean: ` incLoop_loop ` case 2 --- a zero bit becomes a one and the '
         'carry chain ends.  The continue branch ` Q ` and the third branch '
         '` R ` are class variables.')
D_PR0C = ('The last exit of a three-way pop-branch loop: the popped letter '
          '` Z ` fails both tests, so the machine pushes one letter ` Z\' ` on '
          'the source stack ` K ` in its place and leaves.  Lean: '
          '` predLoop_loop ` case 1 --- the terminator is pushed back, which is '
          'the truncated decrement of zero.  The other two branches ` Q ` and '
          '` R ` are class variables.')

if __name__ == '__main__':
    if want('tm2fin0'): in0frag('tm2fin0', True, D_IN0)
    if want('tm2fin0t'): tm2fin0t()
    if want('tm2fpr0c'): in0frag('tm2fpr0c', False, D_PR0C)
