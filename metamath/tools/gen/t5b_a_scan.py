"""T5b: the two one-step lemmas of `blScan` (TM/Prims.lean) --- a bit is popped,
pushed on the destination and folded into the state (~ tm2fbls1 ), or the
terminator is popped and the state is loaded (~ tm2fbls0 ); blueprint D1.
The branch not executed is a class variable ` Q ` (T3, principle 3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t3_lib import hstepc2
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

OPTK = '( %s |_| 1o )' % GK
GE = GT('E')
CE = CONST('E')
CETY = '%s e. ( %s ^m %s )' % (CE, LL, SS)


def fmap(w, ph, st, F, DOM, COD):
    """( ph -> F : DOM --> COD ) from st : ( ph -> F e. ( COD ^m DOM ) )"""
    return w.s([st, w.inst('elmapi')], 'syl', '( %s -> %s : %s --> %s )' % (ph, F, DOM, COD))


def popfacts(w, av, A_, zz, xx, zxn, Zl, ZXl):
    """the pop rules at the popped letter Zl on top of ( <" Zl "> ++ X )"""
    zxnn = w.s([A_(zxn, '%s =/= (/)' % ZXl)], 'neneqd', '( %s -> -. %s = (/) )' % (av, ZXl))
    zj = w.s([A_(zz, '%s e. %s' % (Zl, GK)), A_(xx, WRD('X', GK))], 'jca',
             '( %s -> ( %s e. %s /\\ X e. Word %s ) )' % (av, Zl, GK, GK))
    zfv = w.s([zj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = %s )' % (av, ZXl, Zl))
    ztl = w.s([zj, w.inst('wrdtls1')], 'syl',
              '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = X )' % (av, ZXl, ZXl))
    return zxnn, zfv, ztl


def nonempty(w, ph, zz, xx, Zl, ZXl):
    s1c = w.s([zz], 's1cld', '( %s -> <" %s "> e. Word %s )' % (ph, Zl, GK))
    s1n = w.s([], 's1nz', '<" %s "> =/= (/)' % Zl)
    s1na = w.s([s1n], 'a1i', '( %s -> <" %s "> =/= (/) )' % (ph, Zl))
    return w.s([s1c, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, ZXl))


def tm2fbls1():
    lab = 'tm2fbls1'
    tree, ph = TREE_BLS1, cj(TREE_BLS1)
    STM = STM_BLS1
    LD = LOAD('L', GE); PU = PUSH('J', 'P', LD); BR = BRANCH('C', 'Q', PU)
    ZPDJ = CC(S1("Z'"), '( D ` J )')
    D1 = UP('D', 'K', 'X'); D2 = UP(D1, 'J', ZPDJ)
    assert D2 == D2_BLS1
    w = W(lab, 'The step ` blScan ` of TM/Prims.lean on a bit: the letter ` Z ` is popped '
               'from stack ` K ` , the branch (the terminator test ` C ` ) fails, the '
               'letter ` Z\' ` (T7: the same bit) is pushed on stack ` J ` , the state is '
               'loaded by ` L ` (T7: ` flag := flag || bit ` ) from the class ` N ` into '
               '` N\' ` and the machine leaves for ` E ` .  Lean: ` blScan_runs_bit ` .  '
               'The terminator branch ` Q ` is a class variable.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]; meq = c[MEQ('A', STM)]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, el = c[LAB('A')], c[LAB('E')]
    kk, jj, ne = c['K e. %s' % DG], c['J e. %s' % DG], c['K =/= J']
    nej = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    ff, cc, pp, ll, qq = c[RTY('F', 'K')], c[CTY('C')], c[PTY('P', 'J')], c[LTY('L')], c[STMT('Q')]
    dd, dke = c[STKD('D')], c['( D ` K ) = %s' % ZX]
    zz, zp, xx = c['Z e. %s' % GK], c["Z' e. %s" % GJ], c[WRD('X', GK)]
    nss, n2s = c[SSS('N')], c[SSS("N'")]
    hs = c[HSCAN('N', 'Z', "Z'", "N'")]
    # statement typings
    fe = constfty(w, ph, 'E', LL, el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    ld = loadcl(w, ph, tv, 'L', GE, ll, ge)
    pu = pushcl(w, ph, tv, 'J', 'P', LD, jj, pp, ld)
    br = brcl(w, ph, tv, 'C', 'Q', PU, cc, qq, pu)
    # stacks
    zxn = nonempty(w, ph, zz, xx, 'Z', ZX)
    d1cl = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    zps = s1w(w, ph, zp, "Z'", GJ)
    zpdjw = ccatw(w, ph, zps, djw, S1("Z'"), '( D ` J )', GJ)
    d2cl = updcl(w, ph, D1, 'J', ZPDJ, tv, d1cl, jj, zpdjw)
    rff = fmap(w, ph, ff, 'F', '( %s X. %s )' % (SS, OPTK), SS)
    lff = fmap(w, ph, ll, 'L', SS, SS)

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, STKD('D'))
        d1a = A_(d1cl, STKD(D1)); d2a = A_(d2cl, STKD(D2))
        kka = A_(kk, 'K e. %s' % DG); jja = A_(jj, 'J e. %s' % DG)
        ffa, cca, ppa, lla, qqa = A_(ff, RTY('F', 'K')), A_(cc, CTY('C')), A_(pp, PTY('P', 'J')), A_(ll, LTY('L')), A_(qq, STMT('Q'))
        gea, lda, pua, bra = A_(ge, STMT(GE)), A_(ld, STMT(LD)), A_(pu, STMT(PU)), A_(br, STMT(BR))
        fea = A_(fe, CETY); ela = A_(el, LAB('E'))
        dkea = A_(dke, '( D ` K ) = %s' % ZX); xxa = A_(xx, WRD('X', GK))
        nssa, n2sa = A_(nss, SSS('N')), A_(n2s, SSS("N'"))
        rffa = A_(rff, 'F : ( %s X. %s ) --> %s' % (SS, OPTK, SS))
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, SS))
        NVv = NV('F', 'v', 'Z'); LV = '( L ` %s )' % NVv
        BODY = lambda m: ('( -. ( C ` %s ) = 1o /\\ ( P ` %s ) = Z\' /\\ ( L ` %s ) e. N\' )'
                          % (NV('F', m, 'Z'), NV('F', m, 'Z'), NV('F', m, 'Z')))
        cg, new = W.wcongr(w, BODY('m'), {'m': 'v'}, 'm = v', {'m': w.s([], 'id', '( m = v -> m = v )')})
        assert new == BODY('v'), new
        h = w.s([cg, A_(hs, HSCAN('N', 'Z', "Z'", "N'")), vn], 'rspcdva', '( %s -> %s )' % (av, BODY('v')))
        cq = w.s([h, w.inst('simp1')], 'syl', '( %s -> -. ( C ` %s ) = 1o )' % (av, NVv))
        pq = w.s([h, w.inst('simp2')], 'syl', "( %s -> ( P ` %s ) = Z' )" % (av, NVv))
        lvn = w.s([h, w.inst('simp3')], 'syl', "( %s -> %s e. N' )" % (av, LV))
        zil = w.s([A_(zz, 'Z e. %s' % GK), w.inst('djulcl')], 'syl', '( %s -> ( inl ` Z ) e. %s )' % (av, OPTK))
        op1 = w.s([vv, zil], 'opelxpd', '( %s -> <. v , ( inl ` Z ) >. e. ( %s X. %s ) )' % (av, SS, OPTK))
        nvcl = w.s([rffa, op1], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NVv, SS))
        lvcl = w.s([n2sa, lvn], 'sseldd', '( %s -> %s e. %s )' % (av, LV, SS))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, lvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CE, LV))
        zxnn, zfv, ztl = popfacts(w, av, A_, zz, xx, zxn, 'Z', ZX)
        xv = w.s([xxa], 'elexd', '( %s -> X e. _V )' % av)
        d1j = updnv(w, av, 'D', 'K', 'X', 'J', tva, dda, kka, xv, jja, A_(nej, 'J =/= K'))
        facts = {'T e. V': tva, 'v e. %s' % SS: vv, '%s e. %s' % (NVv, SS): nvcl, '%s e. %s' % (LV, SS): lvcl,
                 STKD('D'): dda, STKD(D1): d1a, STKD(D2): d2a,
                 'K e. %s' % DG: kka, 'J e. %s' % DG: jja,
                 RTY('F', 'K'): ffa, CTY('C'): cca, PTY('P', 'J'): ppa, LTY('L'): lla, STMT('Q'): qqa,
                 STMT(GE): gea, STMT(LD): lda, STMT(PU): pua, STMT(BR): bra, CETY: fea}
        rules = {'( D ` K )': (ZX, dkea), '( %s ` 0 )' % ZX: ('Z', zfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (ZX, ZX): ('X', ztl),
                 '( P ` %s )' % NVv: ("Z'", pq), '( %s ` J )' % D1: ('( D ` J )', d1j),
                 '( %s ` %s )' % (CE, LV): ('E', rge)}
        ifr = {'%s = (/)' % ZX: (False, zxnn), '( C ` %s ) = 1o' % NVv: (False, cq)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (LV, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, MEQ('A', STM))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )' % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, LV, lvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', D2, (meq, phm), al, el, nss, n2s, dd, d2cl, body, qed=True)
    return w.run()


def tm2fbls0():
    lab = 'tm2fbls0'
    tree, ph = TREE_BLS0, cj(TREE_BLS0)
    STM = STM_BLS0
    LD = LOAD('L', GE); BR = BRANCH('C', LD, 'Q')
    D1 = UP('D', 'K', 'X')
    w = W(lab, 'The step ` blScan ` of TM/Prims.lean on the terminator: the letter ` Y ` '
               'is popped from stack ` K ` , the branch (the terminator test ` C ` ) is '
               'taken, the state is loaded by ` L ` (T7: ` carry := true ` ) from the '
               'class ` N ` into ` N\' ` and the machine leaves for ` E ` .  Lean: '
               '` blScan_runs_end ` .  The bit branch ` Q ` is a class variable.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]; meq = c[MEQ('A', STM)]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, el, kk = c[LAB('A')], c[LAB('E')], c['K e. %s' % DG]
    ff, cc, ll, qq = c[RTY('F', 'K')], c[CTY('C')], c[LTY('L')], c[STMT('Q')]
    dd, dke = c[STKD('D')], c['( D ` K ) = %s' % YX]
    yy, xx = c['Y e. %s' % GK], c[WRD('X', GK)]
    nss, n2s = c[SSS('N')], c[SSS("N'")]
    he = c[HEND('N', 'Y', "N'")]
    fe = constfty(w, ph, 'E', LL, el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    ld = loadcl(w, ph, tv, 'L', GE, ll, ge)
    br = brcl(w, ph, tv, 'C', LD, 'Q', cc, ld, qq)
    yxn = nonempty(w, ph, yy, xx, 'Y', YX)
    d1cl = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)
    rff = fmap(w, ph, ff, 'F', '( %s X. %s )' % (SS, OPTK), SS)

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, STKD('D')); d1a = A_(d1cl, STKD(D1))
        kka = A_(kk, 'K e. %s' % DG)
        ffa, cca, lla, qqa = A_(ff, RTY('F', 'K')), A_(cc, CTY('C')), A_(ll, LTY('L')), A_(qq, STMT('Q'))
        gea, lda, bra = A_(ge, STMT(GE)), A_(ld, STMT(LD)), A_(br, STMT(BR))
        fea = A_(fe, CETY); ela = A_(el, LAB('E'))
        dkea = A_(dke, '( D ` K ) = %s' % YX)
        nssa, n2sa = A_(nss, SSS('N')), A_(n2s, SSS("N'"))
        rffa = A_(rff, 'F : ( %s X. %s ) --> %s' % (SS, OPTK, SS))
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, SS))
        NVv = NV('F', 'v', 'Y'); LV = '( L ` %s )' % NVv
        BODY = lambda m: "( ( C ` %s ) = 1o /\\ ( L ` %s ) e. N' )" % (NV('F', m, 'Y'), NV('F', m, 'Y'))
        cg, new = W.wcongr(w, BODY('m'), {'m': 'v'}, 'm = v', {'m': w.s([], 'id', '( m = v -> m = v )')})
        assert new == BODY('v'), new
        h = w.s([cg, A_(he, HEND('N', 'Y', "N'")), vn], 'rspcdva', '( %s -> %s )' % (av, BODY('v')))
        cq = w.s([h], 'simpld', '( %s -> ( C ` %s ) = 1o )' % (av, NVv))
        lvn = w.s([h], 'simprd', "( %s -> %s e. N' )" % (av, LV))
        yil = w.s([A_(yy, 'Y e. %s' % GK), w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. %s )' % (av, OPTK))
        op1 = w.s([vv, yil], 'opelxpd', '( %s -> <. v , ( inl ` Y ) >. e. ( %s X. %s ) )' % (av, SS, OPTK))
        nvcl = w.s([rffa, op1], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NVv, SS))
        lvcl = w.s([n2sa, lvn], 'sseldd', '( %s -> %s e. %s )' % (av, LV, SS))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, lvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CE, LV))
        yxnn, yfv, ytl = popfacts(w, av, A_, yy, xx, yxn, 'Y', YX)
        facts = {'T e. V': tva, 'v e. %s' % SS: vv, '%s e. %s' % (NVv, SS): nvcl, '%s e. %s' % (LV, SS): lvcl,
                 STKD('D'): dda, STKD(D1): d1a, 'K e. %s' % DG: kka,
                 RTY('F', 'K'): ffa, CTY('C'): cca, LTY('L'): lla, STMT('Q'): qqa,
                 STMT(GE): gea, STMT(LD): lda, STMT(BR): bra, CETY: fea}
        rules = {'( D ` K )': (YX, dkea), '( %s ` 0 )' % YX: ('Y', yfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (YX, YX): ('X', ytl),
                 '( %s ` %s )' % (CE, LV): ('E', rge)}
        ifr = {'%s = (/)' % YX: (False, yxnn), '( C ` %s ) = 1o' % NVv: (True, cq)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (LV, D1)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, MEQ('A', STM))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )' % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, LV, lvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', D1, (meq, phm), al, el, nss, n2s, dd, d1cl, body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fbls1'): tm2fbls1()
    if want('tm2fbls0'): tm2fbls0()
