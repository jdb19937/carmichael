"""T5: the two-operand loops, part 2 --- the iteration cores ~ tm2fadi (adder
and subtractor: push the output bit, update the carry) and ~ tm2fcmi
(comparator: fold the verdict), as ~ tm2hitr over ~ tm2fad1 / ~ tm2fcm1
with the family of blueprint D4."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ, GI = GX('K'), GX('J'), GX('I')
LOADG = LOAD('G', GT('A'))
REST_AD = BRANCH('C"', 'Q', PUSH('I', 'P', LOADG))
REST_CM = BRANCH('C"', 'Q', LOADG)
XF = lambda j: '( X ` %s )' % j
YF = lambda j: '( Y ` %s )' % j
NF = lambda j: '( N ` %s )' % j
OFC = lambda j: '( O ` %s )' % j
DI = '( D ` I )'
OUT = lambda j: '( ( reverse ` ( Z prefix %s ) ) ++ %s )' % (j, DI)
SAT = SA('T')


def DPRE(j, cmp):
    base = 'D' if cmp else UP('D', 'I', OUT(j))
    return UP(UP(base, 'K', XF(j)), 'J', YF(j))


def D5(j, cmp):
    j1 = '( %s + 1 )' % j
    return UP(UP(DPRE(j, cmp), 'K', XF(j1)), 'J', YF(j1))


def RESTQ(cmp, Q):
    return BRANCH('C"', Q, LOADG) if cmp else BRANCH('C"', Q, PUSH('I', 'P', LOADG))


def H1(j, cmp, Q='Q'):
    return ('A. r e. %s E. p e. %s ( ( M ` A ) %s <. r , %s >. ) = ( %s %s <. p , %s >. )'
            % (NF(j), OFC(j), SAT, DPRE(j, cmp), RESTQ(cmp, Q), SAT, D5(j, cmp)))


def BI(j, cmp):
    j1 = '( %s + 1 )' % j
    if cmp:
        return 'A. p e. %s ( -. ( C" ` p ) = 1o /\\ ( G ` p ) e. %s )' % (OFC(j), NF(j1))
    return 'A. p e. %s ( -. ( C" ` p ) = 1o /\\ ( P ` p ) = ( Z ` %s ) /\\ ( G ` p ) e. %s )' % (OFC(j), j, NF(j1))


def N0(cmp):
    return 'B' if cmp else '( # ` Z )'


def FAMN(cmp):
    return 'A. k e. ( 0 ... %s ) ( %s C_ %s /\\ %s C_ %s )' % (N0(cmp), NF('k'), SS, OFC('k'), SS)


def FAMXY(cmp):
    return 'A. k e. ( 0 ... ( %s + 1 ) ) ( %s e. Word %s /\\ %s e. Word %s )' % (N0(cmp), XF('k'), GK, YF('k'), GJ)


def HYPS(cmp, Q='Q'):
    return 'A. k e. ( 0 ..^ %s ) ( %s /\\ %s )' % (N0(cmp), H1('k', cmp, Q), BI('k', cmp))


def IFAM(cmp):
    return '( j e. NN0 |-> %s )' % CLN('A', NF('j'), DPRE('j', cmp))


def TREE(cmp):
    if cmp:
        head = ((PHM, ('A e. %s' % LL, ('K e. %s' % DG, 'J e. %s' % DG, 'K =/= J'))),
                (('C" e. ( 2o ^m %s )' % SS, 'G e. ( %s ^m %s )' % (SS, SS)),
                 ('Q e. %s' % STMT_T, 'B e. NN0', 'D e. %s' % STK_T)))
    else:
        head = ((PHM, ('A e. %s' % LL, ('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I', 'J =/= I'))),
                (('C" e. ( 2o ^m %s )' % SS, 'P e. ( %s ^m %s )' % (GI, SS), 'G e. ( %s ^m %s )' % (SS, SS)),
                 ('Q e. %s' % STMT_T, 'Z e. Word %s' % GI, 'D e. %s' % STK_T)))
    return (head, ((FAMN(cmp), FAMXY(cmp)), HYPS(cmp)))


def inst_k(w, ph, st, body_k, X, xcl, name=None):
    """( ph -> body(X) ) from st : ( ph -> A. k e. A body(k) ) and xcl : ( ph -> X e. A )"""
    cg, new = W.wcongr(w, body_k, {'k': X}, 'k = %s' % X, {'k': w.s([], 'id', '( k = %s -> k = %s )' % (X, X))})
    return w.s([cg, st, xcl], 'rspcdva', '( %s -> %s )' % (ph, new)), new


def ifval(w, ph, cmp, X, xcl, nss, dcl, tv, al):
    """( ph -> ( IF ` X ) = CLN( A , ( N ` X ) , DPRE( X ) ) )"""
    IF = IFAM(cmp)
    aq = '( %s /\\ j = %s )' % (ph, X)
    lj = w.s([], 'simpr', '( %s -> j = %s )' % (aq, X))
    body = CLN('A', NF('j'), DPRE('j', cmp))
    st, res = W.congr(w, body, {'j': X}, aq, {'j': lj})
    CL = CLN('A', NF(X), DPRE(X, cmp))
    assert res == CL, (res, CL)
    eqi = w.s([], 'eqid', '%s = %s' % (IF, IF))
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    b = w.s([], 'fvex', '%s e. _V' % NF(X))
    c = w.s([], 'snex', '{ %s } e. _V' % DPRE(X, cmp))
    d = w.s([b, c], 'xpex', '( %s X. { %s } ) e. _V' % (NF(X), DPRE(X, cmp)))
    e = w.s([a, d], 'xpex', '%s e. _V' % CL)
    ea = w.s([e], 'a1i', '( %s -> %s e. _V )' % (ph, CL))
    return w.s([st, eqi, xcl, ea], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ph, IF, X, CL)), CL


def core(lab, cmp):
    tree = TREE(cmp)
    ph = cj(tree)
    n0 = N0(cmp)
    IF = IFAM(cmp)
    desc = ('The iteration core of the comparator loop ` cmpFrag ` (TM/Arith.lean): '
            '~ tm2hitr over ` ( 0 ..^ B ) ` with the family of state classes ` N ` , '
            'post-read classes ` O ` and operand stacks ` X ` , ` Y ` ; each iteration is '
            '~ tm2fcm1 under the read-phase hypothesis ` H1 ` of ~ tm2fadrd and the body '
            'interface (the verdict fold ` G ` lands in the next class).  Lean: the '
            'induction of ` cmpFrag_loop ` .' if cmp else
            'The iteration core of the adder and subtractor loops ` addLoop ` , ` subLoop ` '
            '(TM/Arith.lean, TM/Sub.lean): ~ tm2hitr over ` ( 0 ..^ ( # ` Z ) ) ` with the '
            'family of state classes ` N ` , post-read classes ` O ` , operand stacks ` X ` , '
            '` Y ` and the output word ` Z ` pushed one letter per iteration (reversed on '
            'stack ` I ` ); each iteration is ~ tm2fad1 under the read-phase hypothesis '
            '` H1 ` of ~ tm2fadrd and the body interface (the push function gives the '
            '` i ` -th output bit, the load lands in the next class).  Lean: the induction '
            'of ` addLoop_loop ` and ` subLoop_loop ` .')
    w = W(lab, desc)
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al = c['A e. %s' % LL]
    kk, jj, nkj = c['K e. %s' % DG], c['J e. %s' % DG], c['K =/= J']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    dd = c['D e. %s' % STK_T]; qq = c['Q e. %s' % STMT_T]
    c3, gg = c['C" e. ( 2o ^m %s )' % SS], c['G e. ( %s ^m %s )' % (SS, SS)]
    famn, famxy, hyps = c[FAMN(cmp)], c[FAMXY(cmp)], c[HYPS(cmp)]
    if cmp:
        n0cl = c['B e. NN0']
    else:
        ii = c['I e. %s' % DG]; nki, nji = c['K =/= I'], c['J =/= I']
        nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
        nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
        pp = c['P e. ( %s ^m %s )' % (GI, SS)]; zw = c['Z e. Word %s' % GI]
        n0cl = w.s([zw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, n0))
        diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)

    def outw(ph2, X, zw2, diw2):
        """( ph2 -> OUT(X) e. Word GI )"""
        p = w.s([zw2, w.inst('pfxcl')], 'syl', '( %s -> ( Z prefix %s ) e. Word %s )' % (ph2, X, GI))
        r = revw(w, ph2, p, '( Z prefix %s )' % X, GI)
        return ccatw(w, ph2, r, diw2, '( reverse ` ( Z prefix %s ) )' % X, DI, GI)

    def dprecl(ph2, X, tv2, dd2, kk2, jj2, xw, yw, ii2=None, ow=None):
        base = dd2 if cmp else updcl(w, ph2, 'D', 'I', OUT(X), tv2, dd2, ii2, ow)
        bt = 'D' if cmp else UP('D', 'I', OUT(X))
        a = updcl(w, ph2, bt, 'K', XF(X), tv2, base, kk2, xw)
        return updcl(w, ph2, UP(bt, 'K', XF(X)), 'J', YF(X), tv2, a, jj2, yw), base

    def fam_at(ph2, X, xcl, xcl1, famn2, famxy2):
        """the family facts at X (X e. ( 0 ... n0 )) and X e. ( 0 ... ( n0 + 1 ) )"""
        fn, _ = inst_k(w, ph2, famn2, '( %s C_ %s /\\ %s C_ %s )' % (NF('k'), SS, OFC('k'), SS), X, xcl)
        fx, _ = inst_k(w, ph2, famxy2, '( %s e. Word %s /\\ %s e. Word %s )' % (XF('k'), GK, YF('k'), GJ), X, xcl1)
        nss = w.s([fn], 'simpld', '( %s -> %s C_ %s )' % (ph2, NF(X), SS))
        oss = w.s([fn], 'simprd', '( %s -> %s C_ %s )' % (ph2, OFC(X), SS))
        xw = w.s([fx], 'simpld', '( %s -> %s e. Word %s )' % (ph2, XF(X), GK))
        yw = w.s([fx], 'simprd', '( %s -> %s e. Word %s )' % (ph2, YF(X), GJ))
        return nss, oss, xw, yw

    # ---------------- the iteration hypothesis
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, n0)
    L = Lifter(w, pi)
    ii_ = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, n0))
    inn = w.s([ii_, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    ifz = w.s([ii_, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (pi, n0))
    i1fz = w.s([ii_, w.inst('fzofzp1')], 'syl', '( %s -> ( i + 1 ) e. ( 0 ... %s ) )' % (pi, n0))
    ss1 = w.s([], 'fzssp1', '( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) )' % (n0, n0))
    ss1a = w.s([ss1], 'a1i', '( %s -> ( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) ) )' % (pi, n0, n0))
    ifz1 = w.s([ss1a, ifz], 'sseldd', '( %s -> i e. ( 0 ... ( %s + 1 ) ) )' % (pi, n0))
    i1fz1 = w.s([ss1a, i1fz], 'sseldd', '( %s -> ( i + 1 ) e. ( 0 ... ( %s + 1 ) ) )' % (pi, n0))
    tvi, ddi, kki, jji = L(tv, 'T e. V'), L(dd, 'D e. %s' % STK_T), L(kk, 'K e. %s' % DG), L(jj, 'J e. %s' % DG)
    phmi = L(phm, PHM); ali = L(al, 'A e. %s' % LL); qqi = L(qq, 'Q e. %s' % STMT_T)
    c3i, ggi = L(c3, 'C" e. ( 2o ^m %s )' % SS), L(gg, 'G e. ( %s ^m %s )' % (SS, SS))
    famni, famxyi = L(famn, FAMN(cmp)), L(famxy, FAMXY(cmp))
    nis, ois, xiw, yiw = fam_at(pi, 'i', ifz, ifz1, famni, famxyi)
    ni1s, _, xi1w, yi1w = fam_at(pi, '( i + 1 )', i1fz, i1fz1, famni, famxyi)
    hy, _ = inst_k(w, pi, L(hyps, HYPS(cmp)), '( %s /\\ %s )' % (H1('k', cmp), BI('k', cmp)), 'i', ii_)
    h1 = w.s([hy], 'simpld', '( %s -> %s )' % (pi, H1('i', cmp)))
    bi = w.s([hy], 'simprd', '( %s -> %s )' % (pi, BI('i', cmp)))
    if cmp:
        dpi, _ = dprecl(pi, 'i', tvi, ddi, kki, jji, xiw, yiw)
        dpi1, _ = dprecl(pi, '( i + 1 )', tvi, ddi, kki, jji, xi1w, yi1w)
    else:
        iii = L(ii, 'I e. %s' % DG); zwi = L(zw, 'Z e. Word %s' % GI); diwi = L(diw, '%s e. Word %s' % (DI, GI))
        ppi = L(pp, 'P e. ( %s ^m %s )' % (GI, SS))
        owi = outw(pi, 'i', zwi, diwi); owi1 = outw(pi, '( i + 1 )', zwi, diwi)
        dpi, basei = dprecl(pi, 'i', tvi, ddi, kki, jji, xiw, yiw, iii, owi)
        dpi1, _ = dprecl(pi, '( i + 1 )', tvi, ddi, kki, jji, xi1w, yi1w, iii, owi1)
        zi = w.s([zwi, ii_, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( Z ` i ) e. %s )' % (pi, GI))
    d5k = updcl(w, pi, DPRE('i', cmp), 'K', XF('( i + 1 )'), tvi, dpi, kki, xi1w)
    d5 = updcl(w, pi, UP(DPRE('i', cmp), 'K', XF('( i + 1 )')), 'J', YF('( i + 1 )'), tvi, d5k, jji, yi1w)
    D5i = D5('i', cmp)
    if cmp:
        post = CLN('A', NF('( i + 1 )'), D5i)
        tri = applylem(w, pi, 'tm2fcm1',
                       ((phmi, (ali, (dpi, d5))), ((c3i, ggi), qqi), ((nis, ois, ni1s), h1, bi)),
                       HR(CLN('A', NF('i'), DPRE('i', cmp)), 'T', 'M', post, '1'))
        col = up4(w, pi, 'D', 'K', XF('i'), 'J', YF('i'), XF('( i + 1 )'), YF('( i + 1 )'),
                  tvi, ddi, L(nkj, 'K =/= J'), kki, xiw, xi1w, jji, yiw, yi1w)
        deq = clneq(w, pi, 'A', NF('( i + 1 )'), col, D5i, DPRE('( i + 1 )', cmp))
        tri2, _, _, _ = hrrw(w, pi, tri, CLN('A', NF('i'), DPRE('i', cmp)), post, '1', deq=deq)
    else:
        POST = UP(D5i, 'I', '( <" ( Z ` i ) "> ++ ( %s ` I ) )' % D5i)
        post = CLN('A', NF('( i + 1 )'), POST)
        tri = applylem(w, pi, 'tm2fad1',
                       ((phmi, (ali, (iii, zi), (dpi, d5))), ((c3i, ppi, ggi), qqi), ((nis, ois, ni1s), h1, bi)),
                       HR(CLN('A', NF('i'), DPRE('i', cmp)), 'T', 'M', post, '1'))
        # ( D5 ` I ) = OUT( i )
        nij_i, nik_i = L(nij, 'I =/= J'), L(nik, 'I =/= K')
        yi1v, xi1v, yiv, xiv, oiv = [elv(w, pi, s, t) for s, t in
                                     ((yi1w, YF('( i + 1 )')), (xi1w, XF('( i + 1 )')), (yiw, YF('i')), (xiw, XF('i')), (owi, OUT('i')))]
        BASE = UP('D', 'I', OUT('i'))
        D4 = UP(DPRE('i', cmp), 'K', XF('( i + 1 )'))
        e1 = updnv(w, pi, DPRE('i', cmp), 'K', XF('( i + 1 )'), 'I', tvi, dpi, kki, xi1v, iii, nik_i)
        e0 = updnv(w, pi, D4, 'J', YF('( i + 1 )'), 'I', tvi, d5k, jji, yi1v, iii, nij_i)
        bk = updcl(w, pi, BASE, 'K', XF('i'), tvi, basei, kki, xiw)
        e2 = updnv(w, pi, UP(BASE, 'K', XF('i')), 'J', YF('i'), 'I', tvi, bk, jji, yiv, iii, nij_i)
        e3 = updnv(w, pi, BASE, 'K', XF('i'), 'I', tvi, basei, kki, xiv, iii, nik_i)
        e4 = updkv(w, pi, 'D', 'I', OUT('i'), tvi, ddi, iii, oiv)
        d5i = e0
        for st, rhs in ((e1, '( %s ` I )' % DPRE('i', cmp)), (e2, '( %s ` I )' % UP(BASE, 'K', XF('i'))),
                        (e3, '( %s ` I )' % BASE), (e4, OUT('i'))):
            d5i = w.s([d5i, st], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (pi, D5i, rhs))
        # ( <" ( Z ` i ) "> ++ OUT( i ) ) = OUT( i + 1 )
        ir = w.s([inn, w.inst('nn0red')], 'syl', '( %s -> i e. RR )' % pi)
        ilp = w.s([ir, w.inst('lep1')], 'syl', '( %s -> i <_ ( i + 1 ) )' % pi)
        ifz1b = w.s([w.s([inn, i1n, ilp], '3jca', '( %s -> ( i e. NN0 /\\ ( i + 1 ) e. NN0 /\\ i <_ ( i + 1 ) ) )' % pi),
                     w.inst('elfz2nn0')], 'sylibr', '( %s -> i e. ( 0 ... ( i + 1 ) ) )' % pi)
        cp = w.s([zwi, ifz1b, i1fz, w.inst('ccatpfx')], 'syl3anc',
                 '( %s -> ( ( Z prefix i ) ++ ( Z substr <. i , ( i + 1 ) >. ) ) = ( Z prefix ( i + 1 ) ) )' % pi)
        sw = w.s([zwi, ii_, w.inst('swrds1')], 'syl2anc', '( %s -> ( Z substr <. i , ( i + 1 ) >. ) = <" ( Z ` i ) "> )' % pi)
        cp2, _ = w.rewrite('( ( Z prefix i ) ++ ( Z substr <. i , ( i + 1 ) >. ) )',
                           {'( Z substr <. i , ( i + 1 ) >. )': ('<" ( Z ` i ) ">', sw)}, pi)
        cpx = w.s([cp2, cp], 'eqtr3d', '( %s -> ( ( Z prefix i ) ++ <" ( Z ` i ) "> ) = ( Z prefix ( i + 1 ) ) )' % pi)
        pfi = w.s([zwi, w.inst('pfxcl')], 'syl', '( %s -> ( Z prefix i ) e. Word %s )' % (pi, GI))
        s1i = s1w(w, pi, zi, '( Z ` i )', GI)
        rv = w.s([pfi, s1i, w.inst('revccat')], 'syl2anc',
                 '( %s -> ( reverse ` ( ( Z prefix i ) ++ <" ( Z ` i ) "> ) ) = ( ( reverse ` <" ( Z ` i ) "> ) ++ ( reverse ` ( Z prefix i ) ) ) )' % pi)
        rs1 = w.s([], 'revs1', '( reverse ` <" ( Z ` i ) "> ) = <" ( Z ` i ) ">')
        rs1a = w.s([rs1], 'a1i', '( %s -> ( reverse ` <" ( Z ` i ) "> ) = <" ( Z ` i ) "> )' % pi)
        rv2, _ = w.rewrite('( ( reverse ` <" ( Z ` i ) "> ) ++ ( reverse ` ( Z prefix i ) ) )',
                           {'( reverse ` <" ( Z ` i ) "> )': ('<" ( Z ` i ) ">', rs1a)}, pi)
        rv3 = w.s([rv, rv2], 'eqtrd', '( %s -> ( reverse ` ( ( Z prefix i ) ++ <" ( Z ` i ) "> ) ) = ( <" ( Z ` i ) "> ++ ( reverse ` ( Z prefix i ) ) ) )' % pi)
        rvi = w.s([cpx], 'fveq2d', '( %s -> ( reverse ` ( ( Z prefix i ) ++ <" ( Z ` i ) "> ) ) = ( reverse ` ( Z prefix ( i + 1 ) ) ) )' % pi)
        rvfin = w.s([rvi, rv3], 'eqtr3d', '( %s -> ( reverse ` ( Z prefix ( i + 1 ) ) ) = ( <" ( Z ` i ) "> ++ ( reverse ` ( Z prefix i ) ) ) )' % pi)
        rvpi = revw(w, pi, pfi, '( Z prefix i )', GI)
        asso = w.s([s1i, rvpi, diwi, w.inst('ccatass')], 'syl3anc',
                   '( %s -> ( ( <" ( Z ` i ) "> ++ ( reverse ` ( Z prefix i ) ) ) ++ %s ) = ( <" ( Z ` i ) "> ++ %s ) )' % (pi, DI, OUT('i')))
        pre1 = w.s([rvfin], 'oveq1d', '( %s -> %s = ( ( <" ( Z ` i ) "> ++ ( reverse ` ( Z prefix i ) ) ) ++ %s ) )' % (pi, OUT('( i + 1 )'), DI))
        pre2 = w.s([pre1, asso], 'eqtrd', '( %s -> %s = ( <" ( Z ` i ) "> ++ %s ) )' % (pi, OUT('( i + 1 )'), OUT('i')))
        pre2c = w.s([pre2], 'eqcomd', '( %s -> ( <" ( Z ` i ) "> ++ %s ) = %s )' % (pi, OUT('i'), OUT('( i + 1 )')))
        # collapse
        col4 = up4(w, pi, BASE, 'K', XF('i'), 'J', YF('i'), XF('( i + 1 )'), YF('( i + 1 )'),
                   tvi, basei, L(nkj, 'K =/= J'), kki, xiw, xi1w, jji, yiw, yi1w)
        D5c = UP(UP(BASE, 'K', XF('( i + 1 )')), 'J', YF('( i + 1 )'))
        c3c = applylem(w, pi, 'tm2stkup3c',
                       (((tvi, ddi), (L(nkj, 'K =/= J'), L(nki, 'K =/= I'), L(nji, 'J =/= I'))),
                        (iii, (owi, owi1)), ((kki, xi1w), (jji, yi1w))),
                       '%s = %s' % (UP(D5c, 'I', OUT('( i + 1 )')), DPRE('( i + 1 )', cmp)))
        tbl = {'( %s ` I )' % D5i: (OUT('i'), d5i),
               '( <" ( Z ` i ) "> ++ %s )' % OUT('i'): (OUT('( i + 1 )'), pre2c),
               D5i: (D5c, col4),
               UP(D5c, 'I', OUT('( i + 1 )')): (DPRE('( i + 1 )', cmp), c3c)}
        ps, postn = evaluate(w, pi, POST, {}, extra_rules=(lambda n: tbl.get(n.text())))
        assert postn == DPRE('( i + 1 )', cmp), postn
        deq = clneq(w, pi, 'A', NF('( i + 1 )'), ps, POST, DPRE('( i + 1 )', cmp))
        tri2, _, _, _ = hrrw(w, pi, tri, CLN('A', NF('i'), DPRE('i', cmp)), post, '1', deq=deq)
    # transport into the family
    jvi, CLi = ifval(w, pi, cmp, 'i', inn, nis, dpi, tvi, ali)
    jvi1, CLi1 = ifval(w, pi, cmp, '( i + 1 )', i1n, ni1s, dpi1, tvi, ali)
    t1, _, _, _ = hrrw(w, pi, tri2, CLi, CLi1, '1',
                       ceq=w.s([jvi], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (pi, CLi, IF)),
                       deq=w.s([jvi1], 'eqcomd', '( %s -> %s = ( %s ` ( i + 1 ) ) )' % (pi, CLi1, IF)))
    HYP = 'A. i e. ( 0 ..^ %s ) %s' % (n0, HR('( %s ` i )' % IF, 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '1'))
    hyp = w.s([t1], 'ralrimiva', '( %s -> %s )' % (ph, HYP))
    # ---------------- ( IF ` 0 ) C_ Cfg and the endpoints
    z0 = w.s([], '0nn0', '0 e. NN0')
    z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    n0r = w.s([n0cl, w.inst('nn0red')], 'syl', '( %s -> %s e. RR )' % (ph, n0))
    ge0 = w.s([n0cl, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ph, n0))
    z0fz = w.s([w.s([z0a, n0cl, ge0], '3jca', '( %s -> ( 0 e. NN0 /\\ %s e. NN0 /\\ 0 <_ %s ) )' % (ph, n0, n0)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, n0))
    n0fz = w.s([w.s([n0cl, n0cl, w.s([n0r, w.inst('leidd')], 'syl', '( %s -> %s <_ %s )' % (ph, n0, n0))], '3jca',
                    '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, n0, n0, n0, n0)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, n0, n0))
    ss1b = w.s([], 'fzssp1', '( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) )' % (n0, n0))
    ss1c = w.s([ss1b], 'a1i', '( %s -> ( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    z0fz1 = w.s([ss1c, z0fz], 'sseldd', '( %s -> 0 e. ( 0 ... ( %s + 1 ) ) )' % (ph, n0))
    n0fz1 = w.s([ss1c, n0fz], 'sseldd', '( %s -> %s e. ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    n0s, _, x0w, y0w = fam_at(ph, '0', z0fz, z0fz1, famn, famxy)
    nns, _, xnw, ynw = fam_at(ph, n0, n0fz, n0fz1, famn, famxy)
    if cmp:
        dp0, _ = dprecl(ph, '0', tv, dd, kk, jj, x0w, y0w)
        dpn, _ = dprecl(ph, n0, tv, dd, kk, jj, xnw, ynw)
    else:
        ow0 = outw(ph, '0', zw, diw); own = outw(ph, n0, zw, diw)
        dp0, _ = dprecl(ph, '0', tv, dd, kk, jj, x0w, y0w, ii, ow0)
        dpn, _ = dprecl(ph, n0, tv, dd, kk, jj, xnw, ynw, ii, own)
    ss0 = cfgcl(w, ph, 'A', NF('0'), DPRE('0', cmp), tv, al, n0s, dp0)
    jv0, CL0 = ifval(w, ph, cmp, '0', z0a, n0s, dp0, tv, al)
    jvn, CLn = ifval(w, ph, cmp, n0, n0cl, nns, dpn, tv, al)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IF, CFG_T))
    n1a = w.s([], '1nn0', '1 e. NN0')
    n1b = w.s([n1a], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([ss0j, n1b], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ 1 e. NN0 ) )' % (ph, IF, CFG_T))
    ant = w.s([phm, pj, hyp], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ 1 e. NN0 ) /\\ %s ) )' % (ph, PHM, IF, CFG_T, HYP))
    RUN = HR('( %s ` 0 )' % IF, 'T', 'M', '( %s ` %s )' % (IF, n0), '( %s x. 1 )' % n0)
    itr0 = w.s([n0cl, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ 1 e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IF, CFG_T, HYP, RUN))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )' % (ph, RUN))
    hc = w.s([n0cl], 'nn0cnd', '( %s -> %s e. CC )' % (ph, n0))
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( %s x. 1 ) = %s )' % (ph, n0, n0))
    hrrw(w, ph, run, '( %s ` 0 )' % IF, '( %s ` %s )' % (IF, n0), '( %s x. 1 )' % n0, ceq=jv0, deq=jvn, neq=m1, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fadi'): core('tm2fadi', False)
    if want('tm2fcmi'): core('tm2fcmi', True)
