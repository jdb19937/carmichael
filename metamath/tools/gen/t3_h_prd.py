"""T3: the exit steps of `predLoop` (TM/Prims.lean, blueprint 4.7) --- the only
`peek` of layer T: the borrow chain drops the first one bit, and whether a zero
is pushed in its place depends on whether that bit was the top of the number."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty, OPT, RATY, CTY, DG, GK, STMT_T, NVF
from t3_g_inc import prelude, stkwork, updcl, popr, heat, GE, CTY2, PKTY, NSS, LABTY

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

RATY2 = "F' e. ( %s ^m ( %s X. ( %s |_| 1o ) ) )" % (S('T'), S('T'), GK)
CTY3 = 'C" e. ( 2o ^m %s )' % S('T')
PVF = lambda m, z, zp: "( F' ` <. %s , ( inl ` %s ) >. )" % (NVF(m, z), zp)
ZPX = "( <\" Z' \"> ++ X )"
ZZPX = "( <\" Z \"> ++ %s )" % ZPX


def prfrag(lab, push):
    """the two peek exits of `predLoop`; `push` says whether the peeked letter is
    a bit (so a zero is pushed back) or the terminator (so nothing is)"""
    PU = PUSH('K', 'P', GE)
    BR3 = BRANCH('C"', GE, PU)
    PK = PEEK('K', "F'", BR3)
    BR2 = BRANCH("C'", PK, 'R')
    BR1 = BRANCH('C', 'Q', BR2)
    STM = POP('K', 'F', BR1)
    NV = NVF('v', 'Z'); PV = PVF('v', 'Z', "Z'")
    ZQZPX = "( <\" Z\" \"> ++ %s )" % ZPX
    D1 = UPD('T', 'D', 'K', ZPX)
    D2 = UPD('T', 'D', 'K', ZQZPX) if push else D1
    if push:
        HEB = lambda m: ('( ( -. ( C ` %s ) = 1o /\\ ( C\' ` %s ) = 1o ) /\\ '
                         '( -. ( C" ` %s ) = 1o /\\ ( ( P ` %s ) = Z" /\\ %s e. N ) ) )'
                         % (NVF(m, 'Z'), NVF(m, 'Z'), PVF(m, 'Z', "Z'"),
                            PVF(m, 'Z', "Z'"), PVF(m, 'Z', "Z'")))
        LETS = "( ( Z e. %s /\\ Z' e. %s /\\ Z\" e. %s ) /\\ X e. Word %s )" % (GK, GK, GK, GK)
        FUNTY = ('( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( Q e. %s /\\ R e. %s ) ) )'
                 % (RATY, RATY2, CTY, CTY2, CTY3, PKTY, STMT_T, STMT_T))
    else:
        HEB = lambda m: ('( ( -. ( C ` %s ) = 1o /\\ ( C\' ` %s ) = 1o ) /\\ '
                         '( ( C" ` %s ) = 1o /\\ %s e. N ) )'
                         % (NVF(m, 'Z'), NVF(m, 'Z'), PVF(m, 'Z', "Z'"), PVF(m, 'Z', "Z'")))
        LETS = "( ( Z e. %s /\\ Z' e. %s ) /\\ X e. Word %s )" % (GK, GK, GK)
        FUNTY = ('( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( Q e. %s /\\ R e. %s ) ) )'
                 % (RATY, RATY2, CTY, CTY2, CTY3, PKTY, STMT_T, STMT_T))
    HE = 'A. m e. N %s' % HEB('m')
    STKTY = '( D e. %s /\\ ( D ` K ) = %s /\\ %s )' % (STK('T'), ZZPX, LETS)
    ph = ("( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )"
          % (PHM, STM, LABTY, FUNTY, STKTY, NSS, HE))
    desc = ('The %s exit of the borrow chain: the popped letter ` Z ` passes the '
            'second test, the machine peeks at the letter ` Z\' ` below it and '
            '%s.  Lean: ` predLoop_loop ` case %s --- the first one bit of the '
            'number is dropped, and a zero replaces it unless it was the top '
            'bit.  This is the only ` peek ` of layer T.'
            % (('second', 'pushes ` Z" ` in the popped letter\'s place', '4')
               if push else ('first', 'leaves the stack as the pop left it', '3')))
    w = W(lab, desc)
    u = prelude(w, ph, STM, FUNTY, STKTY, HE, LETS, zx=ZZPX)
    if push:
        z3 = w.s([u['lets']], 'simpld', "( %s -> ( Z e. %s /\\ Z' e. %s /\\ Z\" e. %s ) )"
                 % (ph, GK, GK, GK))
        zz = w.s([z3, w.inst('simp1')], 'syl', '( %s -> Z e. %s )' % (ph, GK))
        zp = w.s([z3, w.inst('simp2')], 'syl', "( %s -> Z' e. %s )" % (ph, GK))
        zq = w.s([z3, w.inst('simp3')], 'syl', "( %s -> Z\" e. %s )" % (ph, GK))
    else:
        z2 = w.s([u['lets']], 'simpld', "( %s -> ( Z e. %s /\\ Z' e. %s ) )" % (ph, GK, GK))
        zz = w.s([z2], 'simpld', '( %s -> Z e. %s )' % (ph, GK))
        zp = w.s([z2], 'simprd', "( %s -> Z' e. %s )" % (ph, GK))
    xx = w.s([u['lets']], 'simprd', '( %s -> X e. Word %s )' % (ph, GK))
    s1zp = w.s([zp], 's1cld', "( %s -> <\" Z' \"> e. Word %s )" % (ph, GK))
    zpxw = w.s([s1zp, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZPX, GK))
    s1z = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ph, GK))
    zzpxw = w.s([s1z, zpxw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZZPX, GK))
    s1n = w.s([], 's1nz', '<" Z "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Z "> =/= (/) )' % ph)
    zxn = w.s([s1z, s1na, zpxw, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, ZZPX))
    d1cl = updcl(w, ph, u, ZPX, zpxw)
    if push:
        s1zq = w.s([zq], 's1cld', "( %s -> <\" Z\" \"> e. Word %s )" % (ph, GK))
        zqw = w.s([s1zq, zpxw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZQZPX, GK))
        d2cl = updcl(w, ph, u, ZQZPX, zqw)
    else:
        d2cl = d1cl
    f3 = w.s([u['ft']], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RATY, RATY2, CTY))
    ra = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    ra2 = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, RATY2))
    cc = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, CTY))
    f4 = w.s([u['ft']], 'simprd', '( %s -> ( ( %s /\\ %s /\\ %s ) /\\ ( Q e. %s /\\ R e. %s ) ) )'
             % (ph, CTY2, CTY3, PKTY, STMT_T, STMT_T))
    c3 = w.s([f4], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, CTY2, CTY3, PKTY))
    c2 = w.s([c3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, CTY2))
    cq = w.s([c3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY3))
    pk = w.s([c3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PKTY))
    qr = w.s([f4], 'simprd', '( %s -> ( Q e. %s /\\ R e. %s ) )' % (ph, STMT_T, STMT_T))
    qq = w.s([qr], 'simpld', '( %s -> Q e. %s )' % (ph, STMT_T))
    rr = w.s([qr], 'simprd', '( %s -> R e. %s )' % (ph, STMT_T))
    kp = w.s([u['kk'], pk], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, PKTY))
    puc = w.s([u['tv'], kp, u['ge'], w.inst('tm2push')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    gp = w.s([u['ge'], puc], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
             % (ph, GE, STMT_T, PU, STMT_T))
    br3 = w.s([u['tv'], cq, gp, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR3, STMT_T))
    kf2 = w.s([u['kk'], ra2], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY2))
    pkc = w.s([u['tv'], kf2, br3, w.inst('tm2peek')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PK, STMT_T))
    pr = w.s([pkc, rr], 'jca', '( %s -> ( %s e. %s /\\ R e. %s ) )' % (ph, PK, STMT_T, STMT_T))
    br2 = w.s([u['tv'], c2, pr, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR2, STMT_T))
    qb = w.s([qq, br2], 'jca', '( %s -> ( Q e. %s /\\ %s e. %s ) )' % (ph, STMT_T, BR2, STMT_T))
    br1 = w.s([u['tv'], cc, qb, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR1, STMT_T))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V'); dd = A_(u['dd'], 'D e. %s' % STK('T'))
        raa = A_(ra, RATY); ra2a = A_(ra2, RATY2); cca = A_(cc, CTY)
        c2a = A_(c2, CTY2); cqa = A_(cq, CTY3); pka = A_(pk, PKTY)
        qqa = A_(qq, 'Q e. %s' % STMT_T); rra = A_(rr, 'R e. %s' % STMT_T)
        gea = A_(u['ge'], '%s e. %s' % (GE, STMT_T)); kka = A_(u['kk'], 'K e. %s' % DG)
        br1a = A_(br1, '%s e. %s' % (BR1, STMT_T)); br2a = A_(br2, '%s e. %s' % (BR2, STMT_T))
        br3a = A_(br3, '%s e. %s' % (BR3, STMT_T)); pkca = A_(pkc, '%s e. %s' % (PK, STMT_T))
        puca = A_(puc, '%s e. %s' % (PU, STMT_T)); ela = A_(u['el'], 'E e. %s' % L('T'))
        fea = A_(u['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        d1a = A_(d1cl, '%s e. %s' % (D1, STK('T'))); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        dkea = A_(u['dke'], '( D ` K ) = %s' % ZZPX)
        xxa = A_(xx, 'X e. Word %s' % GK); nssa = A_(u['nss'], NSS)
        zpa = A_(zp, "Z' e. %s" % GK); zza = A_(zz, 'Z e. %s' % GK)
        zpxa = A_(zpxw, '%s e. Word %s' % (ZPX, GK))
        # the pop: the head and the tail of ( <" Z "> ++ ( <" Z' "> ++ X ) )
        zxna = A_(zxn, '%s =/= (/)' % ZZPX)
        zxnn = w.s([zxna], 'neneqd', '( %s -> -. %s = (/) )' % (av, ZZPX))
        zj = w.s([zza, zpxa], 'jca', '( %s -> ( Z e. %s /\\ %s e. Word %s ) )' % (av, GK, ZPX, GK))
        zfv = w.s([zj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Z )' % (av, ZZPX))
        ztl = w.s([zj, w.inst('wrdtls1')], 'syl',
                  '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = %s )' % (av, ZZPX, ZZPX, ZPX))
        vn, trip = heat(w, av, u, HEB, A_, HE)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        t1 = w.s([trip], 'simpld', "( %s -> ( -. ( C ` %s ) = 1o /\\ ( C' ` %s ) = 1o ) )" % (av, NV, NV))
        cf = w.s([t1], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        ct = w.s([t1], 'simprd', "( %s -> ( C' ` %s ) = 1o )" % (av, NV))
        t2 = w.s([trip], 'simprd', '( %s -> %s )'
                 % (av, ('( -. ( C" ` %s ) = 1o /\\ ( ( P ` %s ) = Z" /\\ %s e. N ) )'
                         % (PV, PV, PV)) if push else
                    ('( ( C" ` %s ) = 1o /\\ %s e. N )' % (PV, PV))))
        if push:
            cqf = w.s([t2], 'simpld', '( %s -> -. ( C" ` %s ) = 1o )' % (av, PV))
            t3 = w.s([t2], 'simprd', "( %s -> ( ( P ` %s ) = Z\" /\\ %s e. N ) )" % (av, PV, PV))
            pqv = w.s([t3], 'simpld', "( %s -> ( P ` %s ) = Z\" )" % (av, PV))
            pvn = w.s([t3], 'simprd', '( %s -> %s e. N )' % (av, PV))
        else:
            cqf = w.s([t2], 'simpld', '( %s -> ( C" ` %s ) = 1o )' % (av, PV))
            pvn = w.s([t2], 'simprd', '( %s -> %s e. N )' % (av, PV))
        pvcl = w.s([nssa, pvn], 'sseldd', '( %s -> %s e. %s )' % (av, PV, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, pvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), PV))
        zpxv = w.s([zpxa], 'elexd', '( %s -> %s e. _V )' % (av, ZPX))
        d1k = updkval(w, av, 'T', 'D', 'K', ZPX, tv, dd, kka, zpxv)
        # the peek's head: ( D1 ` K ) = ( <" Z' "> ++ X ) , its 0th letter is Z'
        zj2 = w.s([zpa, xxa], 'jca', "( %s -> ( Z' e. %s /\\ X e. Word %s ) )" % (av, GK, GK))
        zfv2 = w.s([zj2, w.inst('ccats1fv0')], 'syl', "( %s -> ( %s ` 0 ) = Z' )" % (av, ZPX))
        s1n2 = w.s([], 's1nz', "<\" Z' \"> =/= (/)")
        s1n2a = w.s([s1n2], 'a1i', "( %s -> <\" Z' \"> =/= (/) )" % av)
        s1zpa = A_(s1zp, "<\" Z' \"> e. Word %s" % GK)
        zpn = w.s([s1zpa, s1n2a, xxa, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (av, ZPX))
        zpnn = w.s([zpn], 'neneqd', '( %s -> -. %s = (/) )' % (av, ZPX))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '%s e. %s' % (NV, S('T')): None,
                 'D e. %s' % STK('T'): dd, '%s e. %s' % (D1, STK('T')): d1a,
                 RATY: raa, RATY2: ra2a, CTY: cca, CTY2: c2a, CTY3: cqa, PKTY: pka,
                 'Q e. %s' % STMT_T: qqa, 'R e. %s' % STMT_T: rra,
                 '%s e. %s' % (BR1, STMT_T): br1a, '%s e. %s' % (BR2, STMT_T): br2a,
                 '%s e. %s' % (BR3, STMT_T): br3a, '%s e. %s' % (PK, STMT_T): pkca,
                 '%s e. %s' % (PU, STMT_T): puca, '%s e. %s' % (GE, STMT_T): gea,
                 'K e. %s' % DG: kka,
                 '%s e. %s' % (PV, S('T')): pvcl,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        # the state after the pop must be a state, for the peek clause
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
        zil = w.s([zza, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Z ) e. %s )' % (av, OPT))
        op1 = w.s([vv, zil], 'opelxpd',
                  '( %s -> <. v , ( inl ` Z ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        nvcl = w.s([rff, op1], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        facts['%s e. %s' % (NV, S('T'))] = nvcl
        rules = {'( D ` K )': (ZZPX, dkea), '( %s ` 0 )' % ZZPX: ('Z', zfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (ZZPX, ZZPX): (ZPX, ztl),
                 '( %s ` K )' % D1: (ZPX, d1k), '( %s ` 0 )' % ZPX: ("Z'", zfv2),
                 '( %s ` %s )' % (CONSTF('T', 'E'), PV): ('E', rge)}
        ifr = {'%s = (/)' % ZZPX: (False, zxnn), '%s = (/)' % ZPX: (False, zpnn),
               '( C ` %s ) = 1o' % NV: (False, cf), "( C' ` %s ) = 1o" % NV: (True, ct),
               '( C" ` %s ) = 1o' % PV: (bool(not push), cqf)}
        if push:
            zqa = A_(zq, "Z\" e. %s" % GK)
            rules['( P ` %s )' % PV] = ('Z"', pqv)
            s1zqa = A_(s1zq, "<\" Z\" \"> e. Word %s" % GK)
            zqwa = A_(zqw, '%s e. Word %s' % (ZQZPX, GK))
            tdk = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
            k2 = w.s([zpxa, zqwa], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )'
                     % (av, ZPX, GK, ZQZPX, GK))
            up2 = w.s([tdk, kka, k2, w.inst('tm2stkup2')], 'syl3anc',
                      '( %s -> %s = %s )' % (av, UPD('T', D1, 'K', ZQZPX), D2))
            rules[UPD('T', D1, 'K', ZQZPX)] = (D2, up2)
            facts['%s e. %s' % (D2, STK('T'))] = d2a
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (PV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, PV, pvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', D2, (u['meq'], u['phm']),
            u['al'], u['el'], u['nss'], u['nss'], u['dd'], d2cl, body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fpr0a'): prfrag('tm2fpr0a', False)
    if want('tm2fpr0b'): prfrag('tm2fpr0b', True)
