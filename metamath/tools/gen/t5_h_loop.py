"""T5: the two-operand loops, part 3 --- the assembled loops with their exits:
~ tm2fadl (adder, carry flush by disjunction), ~ tm2fsbl (subtractor),
~ tm2fcml (comparator); each derives the read-phase hypothesis at every
iteration by ~ tm2fadrd , runs the core ~ tm2fadi / ~ tm2fcmi and appends the
exit iteration (blueprint D4)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *
from t5_f_rd import BODY, STEPX, STEPY, HA, TREE_RDX, CONCLX, DP2, HDL
from t5_g_core import (DPRE, D5, H1, BI, N0, FAMN, FAMXY, HYPS, OUT, RESTQ, LOADG, XF, YF, NF, OFC, DI, TREE as CORETREE)

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ, GI = GX('K'), GX('J'), GX('I')
GE = GT('E')


def inst_v(w, ph, st, body_v, v, X, xcl):
    """( ph -> body(X) ) from st : ( ph -> A. v e. A body(v) ), xcl : ( ph -> X e. A )"""
    cg, new = W.wcongr(w, body_v, {v: X}, '%s = %s' % (v, X), {v: w.s([], 'id', '( %s = %s -> %s = %s )' % (v, X, v, X))})
    return w.s([cg, st, xcl], 'rspcdva', '( %s -> %s )' % (ph, new)), new


def rename_ral(w, ph, st, body_i, dom, v2):
    """( ph -> A. v2 e. dom body(v2) ) from st : ( ph -> A. i e. dom body(i) ) by cbvralvw"""
    cg, new = W.wcongr(w, body_i, {'i': v2}, 'i = %s' % v2, {'i': w.s([], 'id', '( i = %s -> i = %s )' % (v2, v2))})
    bi = w.s([cg], 'cbvralvw', '( A. i e. %s %s <-> A. %s e. %s %s )' % (dom, body_i, v2, dom, new))
    return w.s([st, bi], 'sylib', '( %s -> A. %s e. %s %s )' % (ph, v2, dom, new))


def loopasm(lab, kind):
    cmp = kind == 'cmp'
    add = kind == 'add'
    n0 = N0(cmp)
    Q = BRANCH('C0', PUSH('I', "P'", GE), GE) if add else GE
    REST = RESTQ(cmp, Q)
    CONT = LOADG if cmp else PUSH('I', 'P', LOADG)
    BODYQ = BODY(REST)
    famn_i = 'A. i e. ( 0 ... %s ) ( %s C_ %s /\\ %s C_ %s )' % (n0, NF('i'), SS, OFC('i'), SS)
    famxy_i = 'A. i e. ( 0 ... ( %s + 1 ) ) ( %s e. Word %s /\\ %s e. Word %s )' % (n0, XF('i'), GK, YF('i'), GJ)
    steps_i = 'A. i e. ( 0 ... %s ) ( %s /\\ %s )' % (n0, STEPX('i'), STEPY('i'))
    has_i = 'A. i e. ( 0 ... %s ) %s' % (n0, HA('i'))
    bis_i = 'A. i e. ( 0 ..^ %s ) %s' % (n0, BI('i', cmp))
    ON = OFC(n0)
    if add:
        IFC = ("A. p e. %s ( ( ( C\" ` p ) = 1o /\\ ( C0 ` p ) = 1o ) /\\ ( ( P' ` p ) = Z' /\\ p e. N' ) )" % ON)
        IFN = "A. p e. %s ( ( C\" ` p ) = 1o /\\ -. ( C0 ` p ) = 1o /\\ p e. N' )" % ON
        EXIT = "( ( %s /\\ W = ( Z ++ <\" Z' \"> ) ) \\/ ( %s /\\ W = Z ) )" % (IFC, IFN)
    else:
        EXIT = "A. p e. %s ( ( C\" ` p ) = 1o /\\ p e. N' )" % ON
    IDXT = ('K e. %s' % DG, 'J e. %s' % DG) if cmp else ('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG)
    DIST = 'K =/= J' if cmp else ('K =/= J', 'K =/= I', 'J =/= I')
    CC, CP, CD, C0 = ['%s e. ( 2o ^m %s )' % (x, SS) for x in ('C', "C'", 'C"', 'C0')]
    CONDS = ((CC, CP), (CD, C0)) if add else (CC, CP, CD)
    FT, FPT = 'F e. %s' % HDL('K'), "F' e. %s" % HDL('J')
    PT, PPT, GTY = 'P e. ( %s ^m %s )' % (GI, SS), "P' e. ( %s ^m %s )" % (GI, SS), 'G e. ( %s ^m %s )' % (SS, SS)
    FUNS = ((FT, FPT), (PT, PPT, GTY)) if add else (((FT, FPT), (PT, GTY)) if kind == 'sub' else ((FT, FPT), GTY))
    WORDS = ('Z e. Word %s' % GI, "Z' e. %s" % GI) if add else ('Z e. Word %s' % GI if kind == 'sub' else 'B e. NN0')
    X0, Y0 = '( X ` 0 ) = ( D ` K )', '( Y ` 0 ) = ( D ` J )'
    tree = (((PHM, '( M ` A ) = %s' % BODYQ),
             (('A e. %s' % LL, 'E e. %s' % LL), IDXT, DIST),
             (CONDS, FUNS, (WORDS, ('D e. %s' % STK_T, "N' C_ %s" % SS)))),
            (((famn_i, famxy_i), (X0, Y0)), ((steps_i, has_i), (bis_i, EXIT))))
    ph = cj(tree)
    desc = {
        'add': 'The assembled adder loop ` addLoop ` (TM/Arith.lean): from label ` A ` with the '
               'operands on ` K ` , ` J ` and the state in ` ( N ` 0 ) ` , the machine reaches ` E ` in '
               '` ( # ` Z ) + 1 ` steps with the operands consumed, the sum word ` W ` (the output '
               'bits ` Z ` , plus the carry bit ` Z\' ` when the final carry is set, by the exit '
               'disjunction) reversed on ` I ` and the state in ` N\' ` .  The read phase of every '
               'iteration is ~ tm2fadrd , the iterations are ~ tm2fadi , the exit is ~ tm2fad0c or '
               '~ tm2fad0n .  Lean: ` addLoop_loop ` ; the families ` N ` , ` O ` , ` X ` , ` Y ` and the '
               'sets ` R ` , ` R\' ` are the N-level content (T5-blueprint section 4).',
        'sub': 'The assembled subtractor loop ` subLoop ` (TM/Sub.lean): as ~ tm2fadl with the '
               'exit ` goto E ` (~ tm2fcm0 ): the difference bits ` Z ` reversed on ` I ` , the final '
               'borrow in the exit class ` N\' ` .  Lean: ` subLoop_loop ` ; with ` R\' = (/) ` the '
               'phantom operand of ` decLoop_runs ` .',
        'cmp': 'The assembled comparator loop ` cmpFrag ` (TM/Arith.lean): ` B ` iterations of '
               '~ tm2fcmi fold the verdict into the state class and the exit ~ tm2fcm0 leaves for '
               '` E ` with the operands consumed.  Lean: ` cmpFrag_loop ` .'}[kind]
    w = W(lab, desc)
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, el = c['A e. %s' % LL], c['E e. %s' % LL]
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    nkj = c['K =/= J']; njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    dd, npss = c['D e. %s' % STK_T], c["N' C_ %s" % SS]
    cc, cp, cd = c[CC], c[CP], c[CD]
    ff, fp, gg = c[FT], c[FPT], c[GTY]
    meq = c['( M ` A ) = %s' % BODYQ]
    famn, famxy, x0, y0 = c[famn_i], c[famxy_i], c[X0], c[Y0]
    steps, has, bis, exit_ = c[steps_i], c[has_i], c[bis_i], c[EXIT]
    if cmp:
        n0cl = c['B e. NN0']
    else:
        ii = c['I e. %s' % DG]; nki, nji = c['K =/= I'], c['J =/= I']
        nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph); nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
        pp, zw = c[PT], c['Z e. Word %s' % GI]
        n0cl = w.s([zw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, n0))
        diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    if add:
        c0, ppp, zp = c[C0], c[PPT], c["Z' e. %s" % GI]
    # statement typings
    ge = gotocl(w, ph, tv, 'E', el)
    ga = gotocl(w, ph, tv, 'A', al)
    ld = loadcl(w, ph, tv, 'G', GT('A'), gg, ga)
    cont = ld if cmp else pushcl(w, ph, tv, 'I', 'P', LOADG, ii, pp, ld)
    if add:
        pe = pushcl(w, ph, tv, 'I', "P'", GE, ii, ppp, ge)
        qcl = brcl(w, ph, tv, 'C0', PUSH('I', "P'", GE), GE, c0, pe, ge)
    else:
        qcl = ge
    rest = brcl(w, ph, tv, 'C"', Q, CONT, cd, qcl, cont)

    def outw(ph2, X, zw2, diw2):
        p = w.s([zw2, w.inst('pfxcl')], 'syl', '( %s -> ( Z prefix %s ) e. Word %s )' % (ph2, X, GI))
        r = revw(w, ph2, p, '( Z prefix %s )' % X, GI)
        return ccatw(w, ph2, r, diw2, '( reverse ` ( Z prefix %s ) )' % X, DI, GI)

    def dprecl(ph2, X, tv2, dd2, kk2, jj2, xw, yw, ii2=None, ow=None):
        """DPRE(X) e. Stk, its K and J values, the base"""
        base = dd2 if cmp else updcl(w, ph2, 'D', 'I', OUT(X), tv2, dd2, ii2, ow)
        bt = 'D' if cmp else UP('D', 'I', OUT(X))
        a = updcl(w, ph2, bt, 'K', XF(X), tv2, base, kk2, xw)
        dp = updcl(w, ph2, UP(bt, 'K', XF(X)), 'J', YF(X), tv2, a, jj2, yw)
        vk1 = updnv(w, ph2, UP(bt, 'K', XF(X)), 'J', YF(X), 'K', tv2, a, jj2, elv(w, ph2, yw, YF(X)), kk2, L2(ph2, nkj, 'K =/= J'))
        vk2 = updkv(w, ph2, bt, 'K', XF(X), tv2, base, kk2, elv(w, ph2, xw, XF(X)))
        vk = w.s([vk1, vk2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph2, DPRE(X, cmp), XF(X)))
        vj = updkv(w, ph2, UP(bt, 'K', XF(X)), 'J', YF(X), tv2, a, jj2, elv(w, ph2, yw, YF(X)))
        return dp, base, a, vk, vj

    def L2(ph2, st, f):
        return st if ph2 == ph else w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))

    def at(ph2, X, xfz, xfz1, x1fz1, Lf):
        """the family facts, steps and interface at X"""
        fn, _ = inst_v(w, ph2, Lf(famn, famn_i), '( %s C_ %s /\\ %s C_ %s )' % (NF('i'), SS, OFC('i'), SS), 'i', X, xfz)
        fx, _ = inst_v(w, ph2, Lf(famxy, famxy_i), '( %s e. Word %s /\\ %s e. Word %s )' % (XF('i'), GK, YF('i'), GJ), 'i', X, xfz1)
        fx1, _ = inst_v(w, ph2, Lf(famxy, famxy_i), '( %s e. Word %s /\\ %s e. Word %s )' % (XF('i'), GK, YF('i'), GJ), 'i', '( %s + 1 )' % X, x1fz1)
        st, _ = inst_v(w, ph2, Lf(steps, steps_i), '( %s /\\ %s )' % (STEPX('i'), STEPY('i')), 'i', X, xfz)
        ha, _ = inst_v(w, ph2, Lf(has, has_i), HA('i'), 'i', X, xfz)
        return dict(nss=w.s([fn], 'simpld', '( %s -> %s C_ %s )' % (ph2, NF(X), SS)),
                    oss=w.s([fn], 'simprd', '( %s -> %s C_ %s )' % (ph2, OFC(X), SS)),
                    xw=w.s([fx], 'simpld', '( %s -> %s e. Word %s )' % (ph2, XF(X), GK)),
                    yw=w.s([fx], 'simprd', '( %s -> %s e. Word %s )' % (ph2, YF(X), GJ)),
                    x1w=w.s([fx1], 'simpld', '( %s -> %s e. Word %s )' % (ph2, XF('( %s + 1 )' % X), GK)),
                    y1w=w.s([fx1], 'simprd', '( %s -> %s e. Word %s )' % (ph2, YF('( %s + 1 )' % X), GJ)),
                    stx=w.s([st], 'simpld', '( %s -> %s )' % (ph2, STEPX(X))),
                    sty=w.s([st], 'simprd', '( %s -> %s )' % (ph2, STEPY(X))),
                    ha=ha)

    def h1at(ph2, X, f, Lf):
        """H1 at X by tm2fadrd; returns (step, dpcl, d5cl, base)"""
        tv2, dd2, kk2, jj2 = Lf(tv, 'T e. V'), Lf(dd, 'D e. %s' % STK_T), Lf(kk, 'K e. %s' % DG), Lf(jj, 'J e. %s' % DG)
        if cmp:
            dp, base, a, vk, vj = dprecl(ph2, X, tv2, dd2, kk2, jj2, f['xw'], f['yw'])
        else:
            ow = outw(ph2, X, Lf(zw, 'Z e. Word %s' % GI), Lf(diw, '%s e. Word %s' % (DI, GI)))
            dp, base, a, vk, vj = dprecl(ph2, X, tv2, dd2, kk2, jj2, f['xw'], f['yw'], Lf(ii, 'I e. %s' % DG), ow)
        DPX = DPRE(X, cmp)
        d5k = updcl(w, ph2, DPX, 'K', XF('( %s + 1 )' % X), tv2, dp, kk2, f['x1w'])
        d5 = updcl(w, ph2, UP(DPX, 'K', XF('( %s + 1 )' % X)), 'J', YF('( %s + 1 )' % X), tv2, d5k, jj2, f['y1w'])
        leaves = ((tv2, (Lf(cc, CC), Lf(cp, CP)), (Lf(ff, FT), Lf(fp, FPT))),
                  ((kk2, jj2, Lf(nkj, 'K =/= J')), (Lf(rest, '%s e. %s' % (REST, STMT_T)), dp), Lf(meq, '( M ` A ) = %s' % BODYQ)),
                  ((vk, vj), (f['stx'], f['sty']), (f['nss'], f['ha'])))
        assert cj(TREE_RDX(X, DPX, REST)) == cj(tuple_text(leaves)), 'shape'
        h1 = applylem(w, ph2, 'tm2fadrd', leaves, CONCLX(X, DP2(X, DPX), DPX, REST))
        assert CONCLX(X, DP2(X, DPX), DPX, REST) == H1(X, cmp, Q)
        return h1, dp, d5, base

    def tuple_text(t):
        if isinstance(t, str):
            return concl(w, cur_ph[0], t)
        return tuple(tuple_text(x) for x in t)
    cur_ph = [ph]

    # ---------------- HYPS for the core (binder k)
    pk = '( %s /\\ k e. ( 0 ..^ %s ) )' % (ph, n0)
    cur_ph[0] = pk
    Lk = Lifter(w, pk)
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ %s ) )' % (pk, n0))
    kfz = w.s([kin, w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... %s ) )' % (pk, n0))
    k1fz = w.s([kin, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. ( 0 ... %s ) )' % (pk, n0))
    ssp = w.s([], 'fzssp1', '( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) )' % (n0, n0))
    sspk = w.s([ssp], 'a1i', '( %s -> ( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) ) )' % (pk, n0, n0))
    kfz1 = w.s([sspk, kfz], 'sseldd', '( %s -> k e. ( 0 ... ( %s + 1 ) ) )' % (pk, n0))
    k1fz1 = w.s([sspk, k1fz], 'sseldd', '( %s -> ( k + 1 ) e. ( 0 ... ( %s + 1 ) ) )' % (pk, n0))
    fk = at(pk, 'k', kfz, kfz1, k1fz1, Lk)
    h1k, _, _, _ = h1at(pk, 'k', fk, Lk)
    bik, _ = inst_v(w, pk, Lk(bis, bis_i), BI('i', cmp), 'i', 'k', kin)
    hb = w.s([h1k, bik], 'jca', '( %s -> ( %s /\\ %s ) )' % (pk, H1('k', cmp, Q), BI('k', cmp)))
    hyps = w.s([hb], 'ralrimiva', '( %s -> %s )' % (ph, HYPS(cmp, Q)))
    cur_ph[0] = ph
    famnk = rename_ral(w, ph, famn, '( %s C_ %s /\\ %s C_ %s )' % (NF('i'), SS, OFC('i'), SS), '( 0 ... %s )' % n0, 'k')
    famxyk = rename_ral(w, ph, famxy, '( %s e. Word %s /\\ %s e. Word %s )' % (XF('i'), GK, YF('i'), GJ), '( 0 ... ( %s + 1 ) )' % n0, 'k')
    # ---------------- the core
    if cmp:
        coretree = ((phm, (al, (kk, jj, nkj))), ((cd, gg), (qcl, n0cl, dd)))
    else:
        coretree = ((phm, (al, (kk, jj, ii), (nkj, nki, nji))), ((cd, pp, gg), (qcl, zw, dd)))
    core = applylem(w, ph, 'tm2fcmi' if cmp else 'tm2fadi', (coretree, ((famnk, famxyk), hyps)),
                    HR(CLN('A', NF('0'), DPRE('0', cmp)), 'T', 'M', CLN('A', NF(n0), DPRE(n0, cmp)), n0))
    # DPRE(0) = D
    tbl0 = {}
    if not cmp:
        p00 = w.s([], 'pfx00', '( Z prefix 0 ) = (/)'); p00a = w.s([p00], 'a1i', '( %s -> ( Z prefix 0 ) = (/) )' % ph)
        r0 = w.s([], 'rev0', '( reverse ` (/) ) = (/)'); r0a = w.s([r0], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % ph)
        lid = w.s([diw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, DI, DI))
        ui = upid(w, ph, 'D', 'I', tv, dd, ii)
        tbl0.update({'( Z prefix 0 )': ('(/)', p00a), '( reverse ` (/) )': ('(/)', r0a), '( (/) ++ %s )' % DI: (DI, lid), UP('D', 'I', DI): ('D', ui)})
    uk = upid(w, ph, 'D', 'K', tv, dd, kk); uj = upid(w, ph, 'D', 'J', tv, dd, jj)
    tbl0.update({XF('0'): ('( D ` K )', x0), UP('D', 'K', '( D ` K )'): ('D', uk), YF('0'): ('( D ` J )', y0), UP('D', 'J', '( D ` J )'): ('D', uj)})
    e0, d0n = evaluate(w, ph, DPRE('0', cmp), {}, extra_rules=(lambda n: tbl0.get(n.text())))
    assert d0n == 'D', d0n
    core2, _, _, _ = hrrw(w, ph, core, CLN('A', NF('0'), DPRE('0', cmp)), CLN('A', NF(n0), DPRE(n0, cmp)), n0,
                          ceq=clneq(w, ph, 'A', NF('0'), e0, DPRE('0', cmp), 'D'))
    # ---------------- the exit at n0
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    n0r = w.s([n0cl, w.inst('nn0red')], 'syl', '( %s -> %s e. RR )' % (ph, n0))
    n0fz = w.s([w.s([n0cl, n0cl, w.s([n0r, w.inst('leidd')], 'syl', '( %s -> %s <_ %s )' % (ph, n0, n0))], '3jca',
                    '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, n0, n0, n0, n0)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, n0, n0))
    ssp2 = w.s([ssp], 'a1i', '( %s -> ( 0 ... %s ) C_ ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    n0fz1 = w.s([ssp2, n0fz], 'sseldd', '( %s -> %s e. ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    n1n = w.s([n0cl, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, n0))
    n1r = w.s([n1n, w.inst('nn0red')], 'syl', '( %s -> ( %s + 1 ) e. RR )' % (ph, n0))
    n1fz1 = w.s([w.s([n1n, n1n, w.s([n1r, w.inst('leidd')], 'syl', '( %s -> ( %s + 1 ) <_ ( %s + 1 ) )' % (ph, n0, n0))], '3jca',
                     '( %s -> ( ( %s + 1 ) e. NN0 /\\ ( %s + 1 ) e. NN0 /\\ ( %s + 1 ) <_ ( %s + 1 ) ) )' % (ph, n0, n0, n0, n0)),
                 w.inst('elfz2nn0')], 'sylibr', '( %s -> ( %s + 1 ) e. ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    Lid = lambda st, f: st
    fn = at(ph, n0, n0fz, n0fz1, n1fz1, Lid)
    h1n, dpn, d5n, basen = h1at(ph, n0, fn, Lid)
    DPN, D5N = DPRE(n0, cmp), D5(n0, cmp)
    X1, Y1 = XF('( %s + 1 )' % n0), YF('( %s + 1 )' % n0)
    PREN = CLN('A', NF(n0), DPN)
    col4 = up4(w, ph, 'D' if cmp else UP('D', 'I', OUT(n0)), 'K', XF(n0), 'J', YF(n0), X1, Y1,
               tv, basen, nkj, kk, fn['xw'], fn['x1w'], jj, fn['yw'], fn['y1w'])
    D5c = UP(UP('D' if cmp else UP('D', 'I', OUT(n0)), 'K', X1), 'J', Y1)
    if not cmp:
        RZ = '( reverse ` Z )'
        pid = w.s([zw, w.inst('pfxid')], 'syl', '( %s -> ( Z prefix %s ) = Z )' % (ph, n0))
        rzw = revw(w, ph, zw, 'Z', GI)
        rzdi = ccatw(w, ph, rzw, diw, RZ, DI, GI)
    if add:
        # the flush cases
        pha = '( %s /\\ ( %s /\\ W = ( Z ++ <" Z\' "> ) ) )' % (ph, IFC)
        phb = '( %s /\\ ( %s /\\ W = Z ) )' % (ph, IFN)
        FIN = UP(UP(UP('D', 'I', '( ( reverse ` W ) ++ %s )' % DI), 'K', X1), 'J', Y1)
        POSTE = CLN('E', "N'", FIN)
        EXT = HR(PREN, 'T', 'M', POSTE, '1')
        # case c
        La = Lifter(w, pha)
        ifc = w.s([], 'simprl', '( %s -> %s )' % (pha, IFC)); weq = w.s([], 'simprr', '( %s -> W = ( Z ++ <" Z\' "> ) )' % pha)
        tc = applylem(w, pha, 'tm2fad0c',
                      ((La(phm, PHM), ((La(al, 'A e. %s' % LL), La(el, 'E e. %s' % LL)), (La(ii, 'I e. %s' % DG), La(zp, "Z' e. %s" % GI)), (La(dpn, '%s e. %s' % (DPN, STK_T)), La(d5n, '%s e. %s' % (D5N, STK_T))))),
                       ((La(cd, CD), La(c0, C0), La(ppp, PPT)), La(cont, '%s e. %s' % (CONT, STMT_T))),
                       ((La(fn['nss'], '%s C_ %s' % (NF(n0), SS)), La(fn['oss'], '%s C_ %s' % (OFC(n0), SS)), La(npss, "N' C_ %s" % SS)), La(h1n, H1(n0, cmp, Q)), ifc)),
                      HR(PREN, 'T', 'M', CLN('E', "N'", UP(D5N, 'I', '( <" Z\' "> ++ ( %s ` I ) )' % D5N)), '1'))
        POSTC = UP(D5N, 'I', '( <" Z\' "> ++ ( %s ` I ) )' % D5N)
        # ( D5N ` I ) = ( RZ ++ DI )
        tva, dda, iia, kka, jja = La(tv, 'T e. V'), La(dd, 'D e. %s' % STK_T), La(ii, 'I e. %s' % DG), La(kk, 'K e. %s' % DG), La(jj, 'J e. %s' % DG)
        BASE = UP('D', 'I', OUT(n0))
        bk = updcl(w, pha, BASE, 'K', XF(n0), tva, La(basen, '%s e. %s' % (BASE, STK_T)), kka, La(fn['xw'], '%s e. Word %s' % (XF(n0), GK)))
        d5ka = updcl(w, pha, DPN, 'K', X1, tva, La(dpn, '%s e. %s' % (DPN, STK_T)), kka, La(fn['x1w'], '%s e. Word %s' % (X1, GK)))
        e0 = updnv(w, pha, UP(DPN, 'K', X1), 'J', Y1, 'I', tva, d5ka, jja, elv(w, pha, La(fn['y1w'], '%s e. Word %s' % (Y1, GJ)), Y1), iia, La(nij, 'I =/= J'))
        e1 = updnv(w, pha, DPN, 'K', X1, 'I', tva, La(dpn, '%s e. %s' % (DPN, STK_T)), kka, elv(w, pha, La(fn['x1w'], '%s e. Word %s' % (X1, GK)), X1), iia, La(nik, 'I =/= K'))
        e2 = updnv(w, pha, UP(BASE, 'K', XF(n0)), 'J', YF(n0), 'I', tva, bk, jja, elv(w, pha, La(fn['yw'], '%s e. Word %s' % (YF(n0), GJ)), YF(n0)), iia, La(nij, 'I =/= J'))
        e3 = updnv(w, pha, BASE, 'K', XF(n0), 'I', tva, La(basen, '%s e. %s' % (BASE, STK_T)), kka, elv(w, pha, La(fn['xw'], '%s e. Word %s' % (XF(n0), GK)), XF(n0)), iia, La(nik, 'I =/= K'))
        own = outw(pha, n0, La(zw, 'Z e. Word %s' % GI), La(diw, '%s e. Word %s' % (DI, GI)))
        e4 = updkv(w, pha, 'D', 'I', OUT(n0), tva, dda, iia, elv(w, pha, own, OUT(n0)))
        d5i = e0
        for st, rhs in ((e1, '( %s ` I )' % DPN), (e2, '( %s ` I )' % UP(BASE, 'K', XF(n0))), (e3, '( %s ` I )' % BASE), (e4, OUT(n0))):
            d5i = w.s([d5i, st], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (pha, D5N, rhs))
        pida = La(pid, '( Z prefix %s ) = Z' % n0)
        o1 = w.s([pida], 'fveq2d', '( %s -> ( reverse ` ( Z prefix %s ) ) = %s )' % (pha, n0, RZ))
        o2 = w.s([o1], 'oveq1d', '( %s -> %s = ( %s ++ %s ) )' % (pha, OUT(n0), RZ, DI))
        d5i2 = w.s([d5i, o2], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ++ %s ) )' % (pha, D5N, RZ, DI))
        # ( <" Z' "> ++ ( RZ ++ DI ) ) = ( ( reverse ` W ) ++ DI )
        zps = s1w(w, pha, La(zp, "Z' e. %s" % GI), "Z'", GI)
        rw1 = w.s([weq], 'fveq2d', '( %s -> ( reverse ` W ) = ( reverse ` ( Z ++ <" Z\' "> ) ) )' % pha)
        rw2 = w.s([La(zw, 'Z e. Word %s' % GI), zps, w.inst('revccat')], 'syl2anc',
                  '( %s -> ( reverse ` ( Z ++ <" Z\' "> ) ) = ( ( reverse ` <" Z\' "> ) ++ %s ) )' % (pha, RZ))
        rs1 = w.s([], 'revs1', '( reverse ` <" Z\' "> ) = <" Z\' ">'); rs1a = w.s([rs1], 'a1i', '( %s -> ( reverse ` <" Z\' "> ) = <" Z\' "> )' % pha)
        rw3, _ = w.rewrite('( ( reverse ` <" Z\' "> ) ++ %s )' % RZ, {'( reverse ` <" Z\' "> )': ('<" Z\' ">', rs1a)}, pha)
        rw4 = w.s([rw1, w.s([rw2, rw3], 'eqtrd', '( %s -> ( reverse ` ( Z ++ <" Z\' "> ) ) = ( <" Z\' "> ++ %s ) )' % (pha, RZ))], 'eqtrd',
                  '( %s -> ( reverse ` W ) = ( <" Z\' "> ++ %s ) )' % (pha, RZ))
        rw5 = w.s([rw4], 'oveq1d', '( %s -> ( ( reverse ` W ) ++ %s ) = ( ( <" Z\' "> ++ %s ) ++ %s ) )' % (pha, DI, RZ, DI))
        asso = w.s([zps, La(rzw, '%s e. Word %s' % (RZ, GI)), La(diw, '%s e. Word %s' % (DI, GI)), w.inst('ccatass')], 'syl3anc',
                   '( %s -> ( ( <" Z\' "> ++ %s ) ++ %s ) = ( <" Z\' "> ++ ( %s ++ %s ) ) )' % (pha, RZ, DI, RZ, DI))
        rw6 = w.s([rw5, asso], 'eqtrd', '( %s -> ( ( reverse ` W ) ++ %s ) = ( <" Z\' "> ++ ( %s ++ %s ) ) )' % (pha, DI, RZ, DI))
        rw6c = w.s([rw6], 'eqcomd', '( %s -> ( <" Z\' "> ++ ( %s ++ %s ) ) = ( ( reverse ` W ) ++ %s ) )' % (pha, RZ, DI, DI))
        RWDI = '( ( reverse ` W ) ++ %s )' % DI
        rwdiw = w.s([rw6c, w.s([zps, La(rzdi, '( %s ++ %s ) e. Word %s' % (RZ, DI, GI)), w.inst('ccatcl')], 'syl2anc',
                                '( %s -> ( <" Z\' "> ++ ( %s ++ %s ) ) e. Word %s )' % (pha, RZ, DI, GI))], 'eqeltrrd',
                    '( %s -> %s e. Word %s )' % (pha, RWDI, GI))
        c3c = applylem(w, pha, 'tm2stkup3c',
                       (((tva, dda), (La(nkj, 'K =/= J'), La(nki, 'K =/= I'), La(nji, 'J =/= I'))),
                        (iia, (own, rwdiw)), ((kka, La(fn['x1w'], '%s e. Word %s' % (X1, GK))), (jja, La(fn['y1w'], '%s e. Word %s' % (Y1, GJ))))),
                       '%s = %s' % (UP(D5c, 'I', RWDI), FIN))
        tblc = {'( %s ` I )' % D5N: ('( %s ++ %s )' % (RZ, DI), d5i2),
                '( <" Z\' "> ++ ( %s ++ %s ) )' % (RZ, DI): (RWDI, rw6c),
                D5N: (D5c, La(col4, '%s = %s' % (D5N, D5c))),
                UP(D5c, 'I', RWDI): (FIN, c3c)}
        pc, pcn = evaluate(w, pha, POSTC, {}, extra_rules=(lambda n: tblc.get(n.text())))
        assert pcn == FIN, pcn
        tc2, _, _, _ = hrrw(w, pha, tc, PREN, CLN('E', "N'", POSTC), '1', deq=clneq(w, pha, 'E', "N'", pc, POSTC, FIN))
        # case n
        Lb = Lifter(w, phb)
        ifn = w.s([], 'simprl', '( %s -> %s )' % (phb, IFN)); weqb = w.s([], 'simprr', '( %s -> W = Z )' % phb)
        tn = applylem(w, phb, 'tm2fad0n',
                      ((Lb(phm, PHM), ((Lb(al, 'A e. %s' % LL), Lb(el, 'E e. %s' % LL)), (Lb(ii, 'I e. %s' % DG), Lb(zp, "Z' e. %s" % GI)), (Lb(dpn, '%s e. %s' % (DPN, STK_T)), Lb(d5n, '%s e. %s' % (D5N, STK_T))))),
                       ((Lb(cd, CD), Lb(c0, C0), Lb(ppp, PPT)), Lb(cont, '%s e. %s' % (CONT, STMT_T))),
                       ((Lb(fn['nss'], '%s C_ %s' % (NF(n0), SS)), Lb(fn['oss'], '%s C_ %s' % (OFC(n0), SS)), Lb(npss, "N' C_ %s" % SS)), Lb(h1n, H1(n0, cmp, Q)), ifn)),
                      HR(PREN, 'T', 'M', CLN('E', "N'", D5N), '1'))
        pidb = Lb(pid, '( Z prefix %s ) = Z' % n0)
        o1b = w.s([pidb], 'fveq2d', '( %s -> ( reverse ` ( Z prefix %s ) ) = %s )' % (phb, n0, RZ))
        wz = w.s([weqb], 'eqcomd', '( %s -> Z = W )' % phb)
        rzw_ = w.s([wz], 'fveq2d', '( %s -> %s = ( reverse ` W ) )' % (phb, RZ))
        tbln = {D5N: (D5c, Lb(col4, '%s = %s' % (D5N, D5c))), '( reverse ` ( Z prefix %s ) )' % n0: (RZ, o1b), RZ: ('( reverse ` W )', rzw_)}
        pn, pnn = evaluate(w, phb, D5N, {}, extra_rules=(lambda n: tbln.get(n.text())))
        assert pnn == FIN, (pnn, FIN)
        tn2, _, _, _ = hrrw(w, phb, tn, PREN, CLN('E', "N'", D5N), '1', deq=clneq(w, phb, 'E', "N'", pn, D5N, FIN))
        both = w.s([tc2, tn2], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, EXIT, EXT))
        ext = w.s([exit_, both], 'mpdan', '( %s -> %s )' % (ph, EXT))
    else:
        FIN = UP(UP('D' if cmp else UP('D', 'I', '( ( reverse ` Z ) ++ %s )' % DI), 'K', X1), 'J', Y1)
        POSTE = CLN('E', "N'", FIN)
        EXT = HR(PREN, 'T', 'M', POSTE, '1')
        te = applylem(w, ph, 'tm2fcm0',
                      ((phm, ((al, el), (dpn, d5n))), (cd, cont),
                       ((fn['nss'], fn['oss'], npss), h1n, exit_)),
                      HR(PREN, 'T', 'M', CLN('E', "N'", D5N), '1'))
        tbln = {D5N: (D5c, col4)}
        if not cmp:
            o1b = w.s([pid], 'fveq2d', '( %s -> ( reverse ` ( Z prefix %s ) ) = %s )' % (ph, n0, RZ))
            tbln['( reverse ` ( Z prefix %s ) )' % n0] = (RZ, o1b)
        pn, pnn = evaluate(w, ph, D5N, {}, extra_rules=(lambda n: tbln.get(n.text())))
        assert pnn == FIN, (pnn, FIN)
        ext, _, _, _ = hrrw(w, ph, te, PREN, CLN('E', "N'", D5N), '1', deq=clneq(w, ph, 'E', "N'", pn, D5N, FIN))
    w.qed([phm, core2, ext], 'syl3anc', '( %s -> %s )' % (ph, HR(CLN('A', NF('0'), 'D'), 'T', 'M', POSTE, '( %s + 1 )' % n0)))
    return w.run()


if __name__ == '__main__':
    if want('tm2fadl'): loopasm('tm2fadl', 'add')
    if want('tm2fsbl'): loopasm('tm2fsbl', 'sub')
    if want('tm2fcml'): loopasm('tm2fcml', 'cmp')
