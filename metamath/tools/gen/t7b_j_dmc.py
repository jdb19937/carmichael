"""T7b: ` divmodCore ` at the machine ( tmidmcr ): ~ tm2fdmcv instantiated at the
families of blueprint section 3, its blocks from ~ tmidmuq , ~ tmidmd1 - ~ tmidmd4 ,
~ tmidmdt , the prologue ( ~ tmidm3 ) and the ` isZero ` before the down loop
( ~ tmiizs ).

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_j_dmc.py tmidmcr
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith, lineq
from t7_e_cmp import machine, togk as togk7, letgk, bitsgk, lamty, cis_ty, ral_S
from t7b_g_dmu import STMT_DDC, NCM, MXLL, BND_DDC
from t7b_h_dmq import T_GDM, fv, rab_elim, STMT_UQ, DATA_U, ifmax_le
from lin import nlinarith
from t7lib import ST_DRI
from t7b_i_dmd import DATA_D, PH_D, dblocks, DMAP

SEL = sys.argv[1:]
K6 = ['K', 'J', 'I', "I'", 'I"', 'I0']
ENF, ENGG = '( encNatGam ` F )', '( encNatGam ` G )'
DATA_M = ((('F e. NN0', 'G e. NN', 'R e. NN0'), ('R <_ %s' % NF, 'F < ( ( 2 ^ R ) x. G )',
                                                  'A. y e. ( 0 ..^ R ) ( ( 2 ^ y ) x. G ) <_ F')),
          ((WRD('X', GAM), WRD('Y', GAM), STKD('D')),
           ('( D ` K ) = %s' % CC(ENF, YXt('X')), '( D ` J ) = %s' % CC(ENGG, YXt('Y')), "P' = %s" % PDF)))
UPP = tsub_text(BND_DDC, {'L': '( encodeNat ` F )', "L'": '( encodeNat ` G )'})
U0B = '( ( 2 x. ( # ` ( encodeNat ` R ) ) ) + 5 )'
WQ0 = '( encNatGam ` ( R - R ) )'


def GMAP():
    lc = FRAGS['dmc'].lmap('P', 'E')
    lu = FRAGS['dmu'].lmap(PL('P', 7), PL('P', 1))
    ld = FRAGS['dmd'].lmap(PL('P', 9), PL('P', 3))
    m = {'P0': lc['P0'], 'P1': lc['P1'], 'A': lc['A'], 'B0': lc['B0'], "B'": lu["B'"], 'E': lc['E'], 'E1': lc['E1'],
         "A'": lc["A'"], 'A"': lc['A"'], 'A0': ld['A0'], 'B"': ld['B"'], 'D0': ld['D0'], 'E0': ld['E0'], 'B1_': ld['B1_'],
         'E"': ld['E"'], 'G0': ld['G0'], "E'": lc["E'"], "G'": 'E',
         'Y': '4', 'Z0': Z0B, 'C0': CNGT, 'C"': CNFL, 'C': CNGT, "L'": LID, 'F': 'TMrdBit', "F'": 'TMrdA', "C'": CIS, 'B': BITS,
         "Y'": YUF, "Q'": QUF, "N'": NUF, 'R': 'R', 'X': XDF, 'Y"': YDF, 'H': HDF, 'Q': QDF, 'P': "P'", 'N': NDF, 'N1': NSF,
         'N"': NSF, 'N0': N0F, "R'": 'R', 'O': '( 2nd ` T )', "U'": UPB, 'U"': UPP, 'U0': U0B, 'T1': T1B, 'T"': TQB,
         'T0': T0B, "T'": TPB, 'W': WQ0, 'X"': "( D ` I' )", 'D': 'D'}
    return m


def STMT_M():
    tree = ((T_PHM7, FRAGS['dmc'].pred()), (idx_tree(K6), dist_tree(K6)), DATA_M)
    return tree, tsub_text(_GC_, GMAP())


_GA_, _GC_ = split_imp(stmt('tm2fdmcv'))


def tmidmcr():
    lab = 'tmidmcr'
    T, C = STMT_M()
    ph = cj(T)
    w = W(lab, 'Lean\'s ` divmodCore x y q j s t ` at the machine, wherever it is installed ( ` divmodCore_runs ` ): '
               'with the dividend ` F ` on ` x ` , the divisor ` G ` on ` y ` and ` R ` the number of doublings '
               '(Lean ` divSteps ` ), the machine runs the shift-up loop ` R ` times and the shift-down loop ` R ` '
               'times and leaves the stacks of the down loop\'s family at ` R ` with the counter dropped; ~ tm2fdmcv '
               'at the families of ~ tmidmuq and ~ tmidmd1 .')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K6)
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    GM = GMAP()
    kk = mk['k']
    # ---------------- unfoldings
    un = unfold_all(w, ph, c[FRAGS['dmc'].pred()], 'dmc', K6, 'P', 'E', rec=False)
    lc = FRAGS['dmc'].lmap('P', 'E')
    def unf(fname, ks, P_, E_):
        pr = FRAGS[fname].pred(ks, 'T', 'M', P_, E_)
        st = un[pr] if pr in un else None
        assert st is not None, pr
        un.update(unfold_all(w, ph, st, fname, ks, P_, E_, rec=False))
    unf('dmu', ['K', 'J', "I'", 'I"', 'I0'], PL('P', 7), PL('P', 1))
    unf('dmd', K6, PL('P', 9), PL('P', 3))
    unf('dup', ['J', 'I0', 'I"'], PL('P', 4), PL(PL('P', 5), 0))
    unf('inc', ["I'", 'I"'], PL(PL('P', 7), 1), PL(PL(PL('P', 7), 2), 0))
    unf('iz', ["I'", 'I"'], PL('P', 8), PL('P', 3))
    unf('prd', ["I'", 'I"'], PL(PL('P', 9), 4), PL(PL('P', 9), 0))
    unf('dup', ['J', 'I0', 'I"'], PL(PL('P', 9), 5), PL(PL(PL('P', 9), 6), 0))
    unf('dup', ['J', 'I0', 'I"'], PL(PL('P', 9), 8), PL(PL(PL('P', 9), 9), 0))
    unf('iz', ["I'", 'I"'], PL(PL('P', 9), 11), PL('P', 3))
    unf('drop', ["I'"], PL('P', 10), 'E')
    base = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    ex = dict(base); ex.update(un)
    for s_ in K6:
        ex['%s e. %s' % (s_, DG)] = kk[s_]['kd']
    for a_, b_ in [(a, b) for i_, a in enumerate(K6) for b in K6[i_ + 1:]]:
        ex['%s =/= %s' % (a_, b_)] = ne(a_, b_)
        ex['%s =/= %s' % (b_, a_)] = ne(b_, a_)
    bld = lambda extra: Bld(w, ph, c, extra)
    # ---------------- the up block
    up_m = {'P': PL('P', 7), 'E': PL('P', 1)}
    upst, upcc = inst(w, ph, 'tmidmuq', up_m, bld(ex))
    ex.update(parts(w, ph, upst, parse_conj(upcc)))
    # the per-iteration up block is one leaf of the generic antecedent (the A. i text)
    # ---------------- the down blocks
    dm = {'P': PL('P', 9), 'E': PL('P', 3)}
    dtst, dtc = inst(w, ph, 'tmidmdt', dm, bld(ex))
    ex.update(parts(w, ph, dtst, parse_conj(dtc)))
    PHD = tsub_text(cj(PH_D()), dm)
    phd = bld(ex)(tsub(PH_D(), dm))
    ps = '( %s /\\ i e. ( 0 ..^ R ) )' % ph
    j = w.s([w.s([phd], 'adantr', '( %s -> %s )' % (ps, PHD)), w.s([], 'simpr', '( %s -> i e. ( 0 ..^ R ) )' % ps)], 'jca',
            '( %s -> ( %s /\\ i e. ( 0 ..^ R ) ) )' % (ps, PHD))
    typ, body, exd = dblocks()
    body_m = tsub(body, dm)
    def piece(label, concl_text):
        return w.s([j, w.inst(label)], 'syl', '( %s -> %s )' % (ps, concl_text))
    p1 = piece('tmidmd1', '( %s /\\ %s )' % (cj(body_m[0]), cj(body_m[1])))
    p2 = piece('tmidmd2', '( %s /\\ %s )' % (body_m[2][0][0], body_m[2][0][1]))
    p3 = piece('tmidmd3', body_m[2][1])
    p4 = piece('tmidmd4', body_m[2][2])
    b0 = w.s([p1], 'simpld', '( %s -> %s )' % (ps, cj(body_m[0])))
    b1 = w.s([p1], 'simprd', '( %s -> %s )' % (ps, cj(body_m[1])))
    b2 = w.s([p2, p3, p4], '3jca', '( %s -> %s )' % (ps, cj(body_m[2])))
    bb = w.s([b0, b1, b2], '3jca', '( %s -> %s )' % (ps, cj(body_m)))
    per_d = w.s([bb], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ R ) %s )' % (ph, cj(body_m)))
    ex['A. i e. ( 0 ..^ R ) %s' % cj(body_m)] = per_d
    # ---------------- the machine's typings
    b01 = lambda X_of: w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    two = w.s([], '2oex', '2o e. _V')
    XG = lambda t: 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t
    XF_ = lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t
    ex[CTY(CNGT)] = lamty(w, ph, mk, CNGT, XG, '2o', two, b01(XG))
    ex[CTY(CNFL)] = lamty(w, ph, mk, CNFL, XF_, '2o', two, b01(XF_))
    ex[CTY(CIS)] = cis_ty(w, ph, mk)
    f1 = w.s([], 'f1oi', '( _I |` TMSt ) : TMSt -1-1-onto-> TMSt')
    ff = w.s([w.s([f1, w.inst('f1of')], 'ax-mp', '( _I |` TMSt ) : TMSt --> TMSt')], 'a1i', '( %s -> ( _I |` TMSt ) : TMSt --> TMSt )' % ph)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    em = w.s([w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), w.inst('elmapg')], 'syl2anc',
             '( %s -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )' % ph)
    li = w.s([em, ff], 'mpbird', '( %s -> ( _I |` TMSt ) e. ( TMSt ^m TMSt ) )' % ph)
    sq = w.s([seq], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    mq = w.s([sq, sq], 'oveq12d', '( %s -> ( TMSt ^m TMSt ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    ex[LTY(LID)] = w.s([li, mq], 'eleqtrd', '( %s -> %s )' % (ph, LTY(LID)))
    ex[RTY('TMrdBit', 'J')] = kk['J']['hdl']['TMrdBit']
    ex[RTY('TMrdA', "I'")] = kk["I'"]['hdl']['TMrdA']
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    g0 = w.s([closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, Z0B))
    for s_ in ['J', 'I']:
        ex['%s e. %s' % (Z0B, GX(s_))] = letgk(w, ph, mk, Z0B, s_, g0)
    for s_ in ["I'", 'I']:
        ex['4 e. %s' % GX(s_)] = letgk(w, ph, mk, '4', s_, g4)
    ex['%s C_ %s' % (BITS, GX("I'"))] = bitsgk(w, ph, mk, "I'")
    ex['( 2nd ` T ) C_ ( 2nd ` T )'] = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    # ---------------- the numbers
    fn, gn, rn = c['F e. NN0'], c['G e. NN'], c['R e. NN0']
    gn0 = w.s([gn, w.inst('nnnn0')], 'syl', '( %s -> G e. NN0 )' % ph)
    ef = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    eg = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    er = w.s([rn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` R ) e. Word 2o )' % ph)
    cl = Closure(w, ph, {'R': ('NN0', rn), 'F': ('NN0', fn), 'G': ('NN', gn)})
    for a_, st_ in [(NF, ef), (NG, eg), ('( # ` ( encodeNat ` R ) )', er)]:
        cl.leaf(a_, 'NN0', w.s([st_, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, a_)))
    MXFG = 'if ( %s <_ %s , %s , %s )' % (NG, NF, NF, NG)
    cl.leaf(MXFG, 'NN0', w.s([cl.mem(NF, 'NN0'), cl.mem(NG, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXFG)))
    for e_ in [UPB, UPP, U0B, T1B, TQB, T0B, TPB]:
        ex['%s e. NN0' % e_] = cl.mem(e_, 'NN0')
    ex['1 <_ %s' % T0B] = linarith(w, ph, [cl.ge0(NF)], '1 <_ %s' % T0B, closure=cl)
    # ---------------- the families at 0 and R (from tmidmdt's typing)
    TYP = tsub_text(typ, dm)
    tyst = ex[TYP] if TYP in ex else None
    assert tyst is not None
    tbody = TYP[len('A. i e. ( 0 ... R ) '):]
    def typ_at(t, tfz):
        idi = w.s([], 'id', '( i = %s -> i = %s )' % (t, t))
        cg, new = w.wcongr(tbody, {'i': t}, 'i = %s' % t, {'i': idi})
        at = w.s([cg, tyst, tfz], 'rspcdva', '( %s -> %s )' % (ph, new))
        return parts(w, ph, at, parse_conj(new))
    z0fz = w.s([rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... R ) )' % ph)
    rfz = w.s([rn, w.inst('nn0fz0')], 'sylib', '( %s -> R e. ( 0 ... R ) )' % ph)
    t0 = typ_at('0', z0fz); tR = typ_at('R', rfz)
    ex.update(t0)
    # ( ( P ` R ) ` I' ) = ( W ++ ( <" 4 "> ++ ( D ` I' ) ) )
    PR_ = FAPP("P'", 'R')
    PEQ = c["P' = %s" % PDF]
    gam = lambda s_, X, st: w.s([st, kk[s_]['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, X))
    SR = Stacks(w, ph, mk, 'D', c[STKD('D')], ne, {})
    SR = SR.upd("I'", FAPP(QDF, 'R'), gam("I'", FAPP(QDF, 'R'), tR[WRD(FAPP(QDF, 'R'), GX("I'"))])) \
           .upd('J', FAPP(YDF, 'R'), gam('J', FAPP(YDF, 'R'), tR[WRD(FAPP(YDF, 'R'), GX('J'))])) \
           .upd('I', FAPP(HDF, 'R'), gam('I', FAPP(HDF, 'R'), tR[WRD(FAPP(HDF, 'R'), GX('I'))])) \
           .upd('K', FAPP(XDF, 'R'), gam('K', FAPP(XDF, 'R'), tR[WRD(FAPP(XDF, 'R'), GX('K'))]))
    assert SR.D == PDB('R')
    pvR0 = mval(w, ph, 'j', 'NN0', PDB, 'R', rn, w.s([SR.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PDB('R'))))
    pvR = w.s([w.s([PEQ], 'fveq1d', "( %s -> ( P' ` R ) = ( %s ` R ) )" % (ph, PDF)), pvR0], 'eqtrd', "( %s -> ( P' ` R ) = %s )" % (ph, PDB('R')))
    rr0 = lineq(w, ph, '( R - R )', '0', closure=cl) if False else None
    dip = w.s([stkfv(w, ph, 'D', "I'", tv, c[STKD('D')], kk["I'"]['kd']), kk["I'"]['wge']], 'eleqtrd', "( %s -> ( D ` I' ) e. Word Gamma' )" % ph)
    rrn = w.s([rn, rn, w.s([w.s([rn], 'nn0red', '( %s -> R e. RR )' % ph)], 'leidd', '( %s -> R <_ R )' % ph), w.inst('nn0sub2')], 'syl3anc',
              '( %s -> ( R - R ) e. NN0 )' % ph)
    qRw = wgcat(w, ph, WQ0, YXt("( D ` I' )"), w.s([rrn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, WQ0)), wg4(w, ph, "( D ` I' )", dip))
    qRv = fv(w, ph, QDF, QDB, 'R', rn, w.s([qRw], 'elexd', '( %s -> %s e. _V )' % (ph, QDB('R'))))
    pRi = w.s([w.s([w.s([pvR], 'fveq1d', "( %s -> ( %s ` I' ) = ( %s ` I' ) )" % (ph, PR_, PDB('R'))), SR.val("I'")[1]], 'eqtrd',
                   "( %s -> ( %s ` I' ) = %s )" % (ph, PR_, FAPP(QDF, 'R'))), qRv], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ph, PR_, QDB('R')))
    ex["( %s ` I' ) = %s" % (PR_, CC(WQ0, YXt("( D ` I' )")))] = pRi
    egw = w.s([rrn, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. ( encodeNat ` ( R - R ) ) ) )' % (ph, WQ0))
    ibw = w.s([w.s([rrn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` ( R - R ) ) e. Word 2o )' % ph), w.inst('tmcibw')], 'syl',
              '( %s -> ( inclBool o. ( encodeNat ` ( R - R ) ) ) e. Word %s )' % (ph, BITS))
    ex[WRD(WQ0, BITS)] = w.s([egw, ibw], 'eqeltrd', '( %s -> %s e. Word %s )' % (ph, WQ0, BITS))
    ex[WRD("( D ` I' )", GX("I'"))] = stkfv(w, ph, 'D', "I'", tv, c[STKD('D')], kk["I'"]['kd'])
    # dropNum's interface
    dri = w.s([], 'tmcdri', ST_DRI)
    ex['A. r e. ( 2nd ` T ) A. z e. %s ( %s ` %s ) = 1o' % (BITS, CIS, NVA('r', 'z'))] = ral_S(
        w, ph, mk, w.s([dri], 'simpli', ST_DRI[2:].split(' /\\ A. r e. TMSt ')[0]), '( %s ` %s ) = 1o' % (CIS, NVA('r', 'z')), 2)
    ex['A. r e. ( 2nd ` T ) -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4'))] = ral_S(
        w, ph, mk, w.s([dri], 'simpri', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4'))), '-. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')), 1)
    # ---------------- the prologue: dup y t s ; dup x s t ; cmpFrag t s from P1
    DK = c['( D ` K ) = %s' % CC(ENF, YXt('X'))]
    DJ = c['( D ` J ) = %s' % CC(ENGG, YXt('Y'))]
    D4I = CC('<" 4 ">', "( D ` I' )")
    d4w = wg4(w, ph, "( D ` I' )", dip)
    S1 = Stacks(w, ph, mk, 'D', c[STKD('D')], ne, {'K': (CC(ENF, YXt('X')), DK, None), 'J': (CC(ENGG, YXt('Y')), DJ, None)}).upd("I'", D4I, d4w)
    D1 = S1.D
    egf = w.s([fn, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. ( encodeNat ` F ) ) )' % (ph, ENF))
    egg = w.s([gn0, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. %s ) )' % (ph, ENGG, EG))
    WXF = CC('( inclBool o. ( encodeNat ` F ) )', YXt('X'))
    WYG = CC('( inclBool o. %s )' % EG, YXt('Y'))
    d1k = w.s([S1.val('K')[1], w.s([egf], 'oveq1d', '( %s -> %s = %s )' % (ph, CC(ENF, YXt('X')), WXF))], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, WXF))
    d1j = w.s([S1.val('J')[1], w.s([egg], 'oveq1d', '( %s -> %s = %s )' % (ph, CC(ENGG, YXt('Y')), WYG))], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1, WYG))
    mp = {'P': PL('P', 4), "P'": PL('P', 5), 'P"': PL('P', 6), 'E': PL('P', 1), 'L': '( encodeNat ` F )', "L'": EG, 'X': 'X', 'Y': 'Y', 'D': D1}
    exp_ = dict(ex)
    exp_.update({WRD('( encodeNat ` F )', '2o'): ef, WRD(EG, '2o'): eg, STKD(D1): S1.memb, '( %s ` K ) = %s' % (D1, WXF): d1k, '( %s ` J ) = %s' % (D1, WYG): d1j})
    tp, cp = inst(w, ph, 'tmidm3', mp, bld(exp_))
    Cp, Dp, npr = triple_parts(cp)
    NCMP = tsub_text(NCM, mp)
    tgg = w.s([gn0, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ph, EG))
    tff = w.s([fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)
    p0g = w.s([w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ph)], 'exp0d', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)], 'oveq1d', '( %s -> ( ( 2 ^ 0 ) x. G ) = ( 1 x. G ) )' % ph)
    p0g2 = w.s([p0g, w.s([cl.mem('G', 'CC')], 'mullidd', '( %s -> ( 1 x. G ) = G )' % ph)], 'eqtrd', '( %s -> ( ( 2 ^ 0 ) x. G ) = G )' % ph)
    tgg2 = w.s([tgg, p0g2], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( ( 2 ^ 0 ) x. G ) )' % (ph, EG))
    vv = w.s([tgg2, tff], 'oveq12d', '( %s -> ( ( toNat ` %s ) Ncmp ( toNat ` ( encodeNat ` F ) ) ) = ( ( ( 2 ^ 0 ) x. G ) Ncmp F ) )' % (ph, EG))
    ce = w.s([vv], 'eqeq2d', '( %s -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` ( encodeNat ` F ) ) ) <-> ( TMcmp ` h ) = ( ( ( 2 ^ 0 ) x. G ) Ncmp F ) ) )' % (ph, EG))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` ( encodeNat ` F ) ) ) <-> ( TMcmp ` h ) = ( ( ( 2 ^ 0 ) x. G ) Ncmp F ) ) )' % (ph, EG))],
             'rabbidva', '( %s -> %s = %s )' % (ph, NCMP, NUB('0')))
    z0n = closed(w, ph, '0nn0', '0 e. NN0')
    nu0 = fv(w, ph, NUF, NUB, '0', z0n, rabV(w, ph, NUB('0')))
    ncl0 = w.s([rb, w.s([nu0], 'eqcomd', '( %s -> %s = %s )' % (ph, NUB('0'), FAPP(NUF, '0')))], 'eqtrd', '( %s -> %s = %s )' % (ph, NCMP, FAPP(NUF, '0')))
    # stacks: D1 = UPD( UPD( D , J , ( Y' ` 0 ) ) , I' , ( Q' ` 0 ) )
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    r0 = w.s([b0, w.inst('repsw0')], 'syl', '( %s -> ( (/) repeatS 0 ) = (/) )' % ph)
    sh0 = w.s([w.s([r0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ph, SHG('0'), EG)), w.s([eg, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, EG, EG))],
              'eqtrd', '( %s -> %s = %s )' % (ph, SHG('0'), EG))
    yb0 = w.s([w.s([sh0], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. %s ) )' % (ph, SHG('0'), EG))], 'oveq1d', '( %s -> %s = %s )' % (ph, YUB('0'), WYG))
    rw0 = w.s([b0, z0n, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS 0 ) e. Word 2o )' % ph)
    sh0w = w.s([rw0, eg, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, SHG('0')))
    y0w = wgcat(w, ph, '( inclBool o. %s )' % SHG('0'), YXt('Y'), wib(w, ph, SHG('0'), sh0w), wg4(w, ph, 'Y', c[WRD('Y', GAM)]))
    yv0 = fv(w, ph, YUF, YUB, '0', z0n, w.s([y0w], 'elexd', '( %s -> %s e. _V )' % (ph, YUB('0'))))
    dj0 = w.s([DJ, w.s([egg], 'oveq1d', '( %s -> %s = %s )' % (ph, CC(ENGG, YXt('Y')), WYG))], 'eqtrd', '( %s -> ( D ` J ) = %s )' % (ph, WYG))
    y0e = w.s([w.s([yv0, yb0], 'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(YUF, '0'), WYG)), dj0], 'eqtr4d', '( %s -> %s = ( D ` J ) )' % (ph, FAPP(YUF, '0')))
    eng0 = w.s([w.s([w.s([z0n, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ph),
                     w.s([closed(w, ph, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ph)], 'eqtrd',
                    '( %s -> ( encNatGam ` 0 ) = ( inclBool o. (/) ) )' % ph), closed(w, ph, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd', '( %s -> ( encNatGam ` 0 ) = (/) )' % ph)
    q0w = wgcat(w, ph, '( encNatGam ` 0 )', YXt("( D ` I' )"), w.s([z0n, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` 0 ) e. Word Gamma' )" % ph), d4w)
    qv0 = fv(w, ph, QUF, QUB, '0', z0n, w.s([q0w], 'elexd', '( %s -> %s e. _V )' % (ph, QUB('0'))))
    q0e = w.s([qv0, w.s([w.s([eng0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ph, QUB('0'), D4I)), w.s([d4w, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, D4I, D4I))],
                                 'eqtrd', '( %s -> %s = %s )' % (ph, QUB('0'), D4I))], 'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(QUF, '0'), D4I))
    TGT = UP(UP('D', 'J', FAPP(YUF, '0')), "I'", FAPP(QUF, '0'))
    r1_, n1_ = w.rewrite(TGT, {FAPP(YUF, '0'): ('( D ` J )', y0e), FAPP(QUF, '0'): (D4I, q0e)}, ph)
    assert n1_ == UP(UP('D', 'J', '( D ` J )'), "I'", D4I), n1_
    uid = upid(w, ph, 'D', 'J', tv, c[STKD('D')], kk['J']['kd'])
    r2_, n2_ = w.rewrite(n1_, {UP('D', 'J', '( D ` J )'): ('D', uid)}, ph)
    assert n2_ == D1
    deqp = w.s([r1_, r2_], 'eqtrd', '( %s -> %s = %s )' % (ph, TGT, D1))
    assert Dp == CLN(PL('P', 1), NCMP, D1), Dp
    dpq = w.s([clnneq(w, ph, PL('P', 1), ncl0, NCMP, FAPP(NUF, '0'), D1),
               clneq(w, ph, PL('P', 1), FAPP(NUF, '0'), w.s([deqp], 'eqcomd', '( %s -> %s = %s )' % (ph, D1, TGT)), D1, TGT)], 'eqtrd',
              '( %s -> %s = %s )' % (ph, Dp, CLN(PL('P', 1), FAPP(NUF, '0'), TGT)))
    tp2, Cp2, Dp2, np2 = hrrw(w, ph, tp, Cp, Dp, npr, deq=dpq)
    ex[TRI(Cp2, Dp2, np2)] = tp2
    # ---------------- isZero j s before the down loop, from E1
    rnn = rn
    H4 = CC('<" 4 ">', '( D ` I )')
    dsI = w.s([stkfv(w, ph, 'D', 'I', tv, c[STKD('D')], kk['I']['kd']), kk['I']['wge']], 'eleqtrd', "( %s -> ( D ` I ) e. Word Gamma' )" % ph)
    h4w = wg4(w, ph, '( D ` I )', dsI)
    # the families at R of the up loop
    rwR = w.s([b0, rn, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS R ) e. Word 2o )' % ph)
    shR = w.s([rwR, eg, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, SHG('R')))
    yRw = wgcat(w, ph, '( inclBool o. %s )' % SHG('R'), YXt('Y'), wib(w, ph, SHG('R'), shR), wg4(w, ph, 'Y', c[WRD('Y', GAM)]))
    yvR = fv(w, ph, YUF, YUB, 'R', rn, w.s([yRw], 'elexd', '( %s -> %s e. _V )' % (ph, YUB('R'))))
    qRw2 = wgcat(w, ph, '( encNatGam ` R )', YXt("( D ` I' )"), w.s([rn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` R ) e. Word Gamma' )" % ph), d4w)
    qvR = fv(w, ph, QUF, QUB, 'R', rn, w.s([qRw2], 'elexd', '( %s -> %s e. _V )' % (ph, QUB('R'))))
    YUR, QUR = FAPP(YUF, 'R'), FAPP(QUF, 'R')
    yURg = w.s([yvR, yRw], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, YUR))
    qURg = w.s([qvR, qRw2], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, QUR))
    SE_ = Stacks(w, ph, mk, 'D', c[STKD('D')], ne, {}).upd('J', YUR, yURg).upd("I'", QUR, qURg).upd('I', H4, h4w)
    SE = SE_.D
    ENR = '( encodeNat ` R )'
    egR = w.s([rn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` R ) = ( inclBool o. %s ) )' % (ph, ENR))
    WQR = CC('( inclBool o. %s )' % ENR, YXt("( D ` I' )"))
    sei = w.s([w.s([SE_.val("I'")[1], qvR], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ph, SE, QUB('R'))),
               w.s([egR], 'oveq1d', '( %s -> %s = %s )' % (ph, QUB('R'), WQR))], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ph, SE, WQR))
    mz = {'K': "I'", 'I': 'I"', 'P': PL('P', 8), 'E': PL('P', 3), 'L': ENR, 'X': "( D ` I' )", 'D': SE}
    exz = dict(ex)
    exz.update({WRD(ENR, '2o'): er, WRD("( D ` I' )", GAM): dip, STKD(SE): SE_.memb, "( %s ` I' ) = %s" % (SE, WQR): sei})
    tz, cz_ = inst(w, ph, 'tmiizs', mz, bld(exz))
    Cz, Dz, nz = triple_parts(cz_)
    # pre class ( N' ` R ) C_ S
    nuR = fv(w, ph, NUF, NUB, 'R', rn, rabV(w, ph, NUB('R')))
    nuss = w.s([nuR, w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NUB('R'))], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NUB('R'))), seq], 'sseqtrrd',
                          '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NUB('R')))], 'eqsstrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, FAPP(NUF, 'R')))
    E1_ = PL(PL('P', 8), 0)
    tz2 = hrssc(w, ph, phm, tz, Cz, Dz, nz, CLN(E1_, FAPP(NUF, 'R'), SE), clnss(w, ph, E1_, FAPP(NUF, 'R'), SS, SE, nuss))
    # post class
    IF0 = 'if ( ( toNat ` %s ) = 0 , 1o , (/) )' % ENR
    IFD = 'if ( 0 = R , 1o , (/) )'
    trr = w.s([rn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = R )' % (ph, ENR))
    e0 = w.s([trr], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> R = 0 ) )' % (ph, ENR))
    e1_ = w.s([e0, w.s([w.s([], 'eqcom', '( R = 0 <-> 0 = R )')], 'a1i', '( %s -> ( R = 0 <-> 0 = R ) )' % ph)], 'bitrd',
              '( %s -> ( ( toNat ` %s ) = 0 <-> 0 = R ) )' % (ph, ENR))
    ib = w.s([e1_], 'ifbid', '( %s -> %s = %s )' % (ph, IF0, IFD))
    ce = w.s([ib], 'eqeq2d', '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ph, IF0, IFD))
    NFL0 = '{ h e. TMSt | ( TMfl ` h ) = %s }' % IF0
    rbz = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ph, IF0, IFD))], 'rabbidva',
              '( %s -> %s = %s )' % (ph, NFL0, NDB('0')))
    nd0 = fv(w, ph, NDF, NDB, '0', z0n, rabV(w, ph, NDB('0')))
    ncz = w.s([rbz, w.s([nd0], 'eqcomd', '( %s -> %s = %s )' % (ph, NDB('0'), FAPP(NDF, '0')))], 'eqtrd', '( %s -> %s = %s )' % (ph, NFL0, FAPP(NDF, '0')))
    # post stacks: SE = ( P ` 0 )
    S0_ = Stacks(w, ph, mk, 'D', c[STKD('D')], ne, {'K': (CC(ENF, YXt('X')), DK, None)})
    S0_ = S0_.upd("I'", FAPP(QDF, '0'), gam("I'", FAPP(QDF, '0'), t0[WRD(FAPP(QDF, '0'), GX("I'"))])) \
             .upd('J', FAPP(YDF, '0'), gam('J', FAPP(YDF, '0'), t0[WRD(FAPP(YDF, '0'), GX('J'))])) \
             .upd('I', FAPP(HDF, '0'), gam('I', FAPP(HDF, '0'), t0[WRD(FAPP(HDF, '0'), GX('I'))]))
    X3 = S0_.D
    S0b = S0_.upd('K', FAPP(XDF, '0'), gam('K', FAPP(XDF, '0'), t0[WRD(FAPP(XDF, '0'), GX('K'))]))
    assert S0b.D == PDB('0')
    pv00 = mval(w, ph, 'j', 'NN0', PDB, '0', z0n, w.s([S0b.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PDB('0'))))
    pv0 = w.s([w.s([PEQ], 'fveq1d', "( %s -> ( P' ` 0 ) = ( %s ` 0 ) )" % (ph, PDF)), pv00], 'eqtrd', "( %s -> ( P' ` 0 ) = %s )" % (ph, PDB('0')))
    r0_ = w.s([cl.mem('R', 'CC')], 'subid1d', '( %s -> ( R - 0 ) = R )' % ph)
    # Q
    q0v = fv(w, ph, QDF, QDB, '0', z0n, w.s([w.s([w.s([w.s([r0_], 'fveq2d', '( %s -> ( encNatGam ` ( R - 0 ) ) = ( encNatGam ` R ) )' % ph)], 'oveq1d',
                                                          '( %s -> %s = %s )' % (ph, QDB('0'), QUB('R'))), qRw2], 'eqeltrd' if False else 'eqeltrd',
                                                   "( %s -> %s e. Word Gamma' )" % (ph, QDB('0')))], 'elexd', '( %s -> %s e. _V )' % (ph, QDB('0'))))
    qq = w.s([w.s([q0v, w.s([w.s([r0_], 'fveq2d', '( %s -> ( encNatGam ` ( R - 0 ) ) = ( encNatGam ` R ) )' % ph)], 'oveq1d', '( %s -> %s = %s )' % (ph, QDB('0'), QUB('R')))],
                  'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(QDF, '0'), QUB('R'))), qvR], 'eqtr4d', '( %s -> %s = %s )' % (ph, FAPP(QDF, '0'), QUR))
    # Y
    ysh = w.s([w.s([w.s([r0_], 'oveq2d', '( %s -> ( (/) repeatS ( R - 0 ) ) = ( (/) repeatS R ) )' % ph)], 'oveq1d', '( %s -> %s = %s )' % (ph, SHG('( R - 0 )'), SHG('R')))],
              'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. %s ) )' % (ph, SHG('( R - 0 )'), SHG('R')))
    ydr = w.s([ysh], 'oveq1d', '( %s -> %s = %s )' % (ph, YDB('0'), YUB('R')))
    y0v = fv(w, ph, YDF, YDB, '0', z0n, w.s([w.s([ydr, yRw], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, YDB('0')))], 'elexd', '( %s -> %s e. _V )' % (ph, YDB('0'))))
    yy = w.s([w.s([y0v, ydr], 'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(YDF, '0'), YUB('R'))), yvR], 'eqtr4d', '( %s -> %s = %s )' % (ph, FAPP(YDF, '0'), YUR))
    # H
    D0_ = DV('0')
    fq0 = '( |_ ` ( F / %s ) )' % D0_
    cl.have('( R - 0 )', 'NN0', w.s([r0_, rn], 'eqeltrd', '( %s -> ( R - 0 ) e. NN0 )' % ph))
    bw0 = w.s([cl.mem(fq0, 'ZZ'), w.inst('bwrd0')], 'syl', '( %s -> ( %s bwrd 0 ) = (/) )' % (ph, fq0))
    hib = w.s([w.s([bw0], 'coeq2d', '( %s -> ( inclBool o. ( %s bwrd 0 ) ) = ( inclBool o. (/) ) )' % (ph, fq0)), closed(w, ph, 'co02', '( inclBool o. (/) ) = (/)')],
              'eqtrd', '( %s -> ( inclBool o. ( %s bwrd 0 ) ) = (/) )' % (ph, fq0))
    hd0 = w.s([w.s([hib], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ph, HDB('0'), H4)), w.s([h4w, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, H4, H4))],
              'eqtrd', '( %s -> %s = %s )' % (ph, HDB('0'), H4))
    h0v = fv(w, ph, HDF, HDB, '0', z0n, w.s([w.s([hd0, h4w], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, HDB('0')))], 'elexd', '( %s -> %s e. _V )' % (ph, HDB('0'))))
    hh = w.s([h0v, hd0], 'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(HDF, '0'), H4))
    # X
    d0e = w.s([w.s([r0_], 'oveq2d', '( %s -> ( 2 ^ ( R - 0 ) ) = ( 2 ^ R ) )' % ph)], 'oveq1d', '( %s -> %s = ( ( 2 ^ R ) x. G ) )' % (ph, D0_))
    flt0 = w.s([c['F < ( ( 2 ^ R ) x. G )'], w.s([d0e], 'eqcomd', '( %s -> ( ( 2 ^ R ) x. G ) = %s )' % (ph, D0_))], 'breqtrd', '( %s -> F < %s )' % (ph, D0_))
    mid = w.s([w.s([cl.mem('F', 'RR'), w.s([cl.mem(D0_, 'NN')], 'nnrpd', '( %s -> %s e. RR+ )' % (ph, D0_))], 'jca', '( %s -> ( F e. RR /\\ %s e. RR+ ) )' % (ph, D0_)),
               w.s([cl.ge0('F'), flt0], 'jca', '( %s -> ( 0 <_ F /\\ F < %s ) )' % (ph, D0_)), w.inst('modid')], 'syl2anc', '( %s -> ( F mod %s ) = F )' % (ph, D0_))
    ebl = w.s([fn, w.inst('encnatbwrd')], 'syl', '( %s -> ( encodeNat ` F ) = ( F bwrd ( bl ` F ) ) )' % ph)
    elb = w.s([fn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` F ) )' % (ph, NF))
    fbw = w.s([w.s([elb], 'oveq2d', '( %s -> ( F bwrd %s ) = ( F bwrd ( bl ` F ) ) )' % (ph, NF)), ebl], 'eqtr4d', '( %s -> ( F bwrd %s ) = ( encodeNat ` F ) )' % (ph, NF))
    xw1 = w.s([w.s([mid], 'oveq1d', '( %s -> ( ( F mod %s ) bwrd %s ) = ( F bwrd %s ) )' % (ph, D0_, NF, NF)), fbw], 'eqtrd',
              '( %s -> ( ( F mod %s ) bwrd %s ) = ( encodeNat ` F ) )' % (ph, D0_, NF))
    xw2 = w.s([w.s([xw1], 'coeq2d', '( %s -> ( inclBool o. ( ( F mod %s ) bwrd %s ) ) = ( inclBool o. ( encodeNat ` F ) ) )' % (ph, D0_, NF)), egf], 'eqtr4d',
              '( %s -> ( inclBool o. ( ( F mod %s ) bwrd %s ) ) = %s )' % (ph, D0_, NF, ENF))
    xd0 = w.s([w.s([xw2], 'oveq1d', '( %s -> %s = %s )' % (ph, XDB('0'), CC(ENF, YXt('X')))), DK], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (ph, XDB('0')))
    x0v = fv(w, ph, XDF, XDB, '0', z0n, w.s([w.s([xd0, w.s([stkfv(w, ph, 'D', 'K', tv, c[STKD('D')], kk['K']['kd']), kk['K']['wge']], 'eleqtrd', "( %s -> ( D ` K ) e. Word Gamma' )" % ph)],
                                               'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, XDB('0')))], 'elexd', '( %s -> %s e. _V )' % (ph, XDB('0'))))
    xx = w.s([x0v, xd0], 'eqtrd', '( %s -> %s = ( D ` K ) )' % (ph, FAPP(XDF, '0')))
    # PDB( 0 ) = UPD( X3 , K , ( D ` K ) ) = X3
    ukx = upeq(w, ph, X3, 'K', xx, FAPP(XDF, '0'), '( D ` K )')
    x3k = S0_.val('K')[1]
    uid3 = upidv(w, ph, X3, 'K', '( D ` K )', w.s([x3k], 'id', '( %s -> ( %s ` K ) = %s )' % (ph, X3, CC(ENF, YXt('X')))) if False else
                 w.s([x3k, DK], 'eqtr4d', '( %s -> ( %s ` K ) = ( D ` K ) )' % (ph, X3)), tv, S0_.memb, kk['K']['kd'])
    p0x3 = w.s([w.s([pv0, ukx], 'eqtrd', '( %s -> ( P\' ` 0 ) = %s )' % (ph, UP(X3, 'K', '( D ` K )'))), uid3], 'eqtrd', '( %s -> ( P\' ` 0 ) = %s )' % (ph, X3))
    # X3 = UPD3( D ; I' , QUR ; J , YUR ; I , H4 )
    rx, nx = w.rewrite(X3, {FAPP(QDF, '0'): (QUR, qq), FAPP(YDF, '0'): (YUR, yy), FAPP(HDF, '0'): (H4, hh)}, ph)
    assert nx == UP(UP(UP('D', "I'", QUR), 'J', YUR), 'I', H4), nx
    togk_ = lambda X, s_, g: w.s([g, kk[s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    ucm = upc(w, ph, 'D', "I'", QUR, 'J', YUR, tv, c[STKD('D')], ne("I'", 'J'), kk["I'"]['kd'], togk_(QUR, "I'", qURg), kk['J']['kd'], togk_(YUR, 'J', yURg))
    ry, ny = w.rewrite(nx, {UP(UP('D', "I'", QUR), 'J', YUR): (UP(UP('D', 'J', YUR), "I'", QUR), ucm)}, ph)
    assert ny == SE, ny
    pse = w.s([w.s([p0x3, rx], 'eqtrd', '( %s -> ( P\' ` 0 ) = %s )' % (ph, nx)), ry], 'eqtrd', '( %s -> ( P\' ` 0 ) = %s )' % (ph, SE))
    assert Dz == CLN(PL('P', 3), NFL0, SE), Dz
    dzq = w.s([clnneq(w, ph, PL('P', 3), ncz, NFL0, FAPP(NDF, '0'), SE),
               clneq(w, ph, PL('P', 3), FAPP(NDF, '0'), w.s([pse], 'eqcomd', '( %s -> %s = ( P\' ` 0 ) )' % (ph, SE)), SE, FAPP("P'", '0'))], 'eqtrd',
              '( %s -> %s = %s )' % (ph, Dz, CLN(PL('P', 3), FAPP(NDF, '0'), FAPP("P'", '0'))))
    tz3, Cz3, Dz3, nz3 = hrrw(w, ph, tz2, CLN(E1_, FAPP(NUF, 'R'), SE), Dz, nz, deq=dzq)
    ex[TRI(Cz3, Dz3, nz3)] = tz3
    # ---------------- apply tm2fdmcv
    fin, cf = inst(w, ph, 'tm2fdmcv', GM, bld(ex))
    assert cf == C, (cf[:300], C[:300])
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()



XR_ = '( ( inclBool o. ( ( F mod G ) bwrd %s ) ) ++ ( <" 4 "> ++ X ) )' % NF
HR_ = '( ( inclBool o. ( ( |_ ` ( F / G ) ) bwrd R ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )'
FINAL_DM = UP(UP(UP('D', 'K', XR_), 'I', HR_), 'J', 'Y')
BDM = ('( ( %s x. ( ( ( ; 2 3 x. %s ) + ( 6 x. %s ) ) + ; 5 4 ) ) + ( ( ( 5 x. %s ) + ( 4 x. %s ) ) + ; 2 3 ) )'
       % (NF, NF, NG, NF, NG))


def STMT_DMR():
    tree = ((T_PHM7, FRAGS['dm'].pred()), (idx_tree(K6), dist_tree(K6)), DATA_M)
    return tree, TRI(CLN(FRAGS['dm'].entry(), SS, 'D'), CLN('E', SS, FINAL_DM), BDM)


def tmidmr():
    lab = 'tmidmr'
    T, C = STMT_DMR()
    ph = cj(T)
    w = W(lab, 'Lean\'s ` divmod x y q j s t ` (= ` divmodCore ; dropNum y ` ) at the machine, wherever it is '
               'installed ( ` divmod_runs ` ): ` x ` gets the ` n ` -bit word of ` F mod G ` , ` q ` the ` R ` -bit word '
               'of ` |_ ( F / G ) ` , the divisor is consumed and ` j ` , ` s ` , ` t ` are restored, within '
               '` n ( 23 n + 6 g + 54 ) + 5 n + 4 g + 23 ` steps ( ` n ` , ` g ` the bit lengths of ` F ` , ` G ` ).')
    from t7b_i_dmd import Dn
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K6)
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    kk = mk['k']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    un = unfold_all(w, ph, c[FRAGS['dm'].pred()], 'dm', K6, 'P', 'E', rec=False)
    base = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    ex = dict(base); ex.update(un)
    for s_ in K6:
        ex['%s e. %s' % (s_, DG)] = kk[s_]['kd']
    for a_, b_ in [(a, b) for i_, a in enumerate(K6) for b in K6[i_ + 1:]]:
        ex['%s =/= %s' % (a_, b_)] = ne(a_, b_)
        ex['%s =/= %s' % (b_, a_)] = ne(b_, a_)
    t1, c1 = inst(w, ph, 'tmidmcr', {'P': PL('P', 0), 'E': PL(PL('P', 1), 0)}, Bld(w, ph, c, ex))
    Ca, Da, n1 = triple_parts(c1)
    # ---- the family at R
    rn = c['R e. NN0']
    rle = w.s([w.s([rn], 'nn0red', '( %s -> R e. RR )' % ph)], 'leidd', '( %s -> R <_ R )' % ph)
    dn = Dn(w, ph, c, mk, ne, closed_range='none')
    aR = dn.at('R', rn, rle)
    cl = dn.cl
    PV_ = "P'"
    pv = aR['pv']       # ( P' ` R ) = PDB( R )
    SRm = aR['S']
    # DV( R ) = G
    rr = w.s([cl.mem('R', 'CC')], 'subidd', '( %s -> ( R - R ) = 0 )' % ph)
    e2 = w.s([w.s([rr], 'oveq2d', '( %s -> ( 2 ^ ( R - R ) ) = ( 2 ^ 0 ) )' % ph), w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ph)], 'exp0d', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)],
             'eqtrd', '( %s -> ( 2 ^ ( R - R ) ) = 1 )' % ph)
    dvr = w.s([w.s([e2], 'oveq1d', '( %s -> %s = ( 1 x. G ) )' % (ph, DV('R'))), w.s([cl.mem('G', 'CC')], 'mullidd', '( %s -> ( 1 x. G ) = G )' % ph)], 'eqtrd',
              '( %s -> %s = G )' % (ph, DV('R')))
    xrv = w.s([aR['xv'], w.s([w.s([w.s([w.s([dvr], 'oveq2d', '( %s -> ( F mod %s ) = ( F mod G ) )' % (ph, DV('R')))], 'oveq1d',
                                           '( %s -> ( ( F mod %s ) bwrd %s ) = ( ( F mod G ) bwrd %s ) )' % (ph, DV('R'), NF, NF))], 'coeq2d',
                                    '( %s -> ( inclBool o. ( ( F mod %s ) bwrd %s ) ) = ( inclBool o. ( ( F mod G ) bwrd %s ) ) )' % (ph, DV('R'), NF, NF))], 'oveq1d',
                             '( %s -> %s = %s )' % (ph, XDB('R'), XR_))], 'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(XDF, 'R'), XR_))
    hrv = w.s([aR['hv'], w.s([w.s([w.s([w.s([w.s([dvr], 'oveq2d', '( %s -> ( F / %s ) = ( F / G ) )' % (ph, DV('R')))], 'fveq2d',
                                                  '( %s -> ( |_ ` ( F / %s ) ) = ( |_ ` ( F / G ) ) )' % (ph, DV('R')))], 'oveq1d',
                                           '( %s -> ( ( |_ ` ( F / %s ) ) bwrd R ) = ( ( |_ ` ( F / G ) ) bwrd R ) )' % (ph, DV('R')))], 'coeq2d',
                                    '( %s -> ( inclBool o. ( ( |_ ` ( F / %s ) ) bwrd R ) ) = ( inclBool o. ( ( |_ ` ( F / G ) ) bwrd R ) ) )' % (ph, DV('R')))], 'oveq1d',
                             '( %s -> %s = %s )' % (ph, HDB('R'), HR_))], 'eqtrd', '( %s -> %s = %s )' % (ph, FAPP(HDF, 'R'), HR_))
    YW = YDB('R')
    yrv = aR['yv']
    # ---- the stack algebra: UPD( ( P' ` R ) , I' , ( D ` I' ) ) = UPD( D2 , J , YW )
    qq, yy, hh, xx = FAPP(QDF, 'R'), FAPP(YDF, 'R'), FAPP(HDF, 'R'), FAPP(XDF, 'R')
    dd = c[STKD('D')]
    togk = lambda X, s_, g: w.s([g, kk[s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    gq, gy, gh, gx = togk(qq, "I'", aR['qg']), togk(yy, 'J', aR['yg']), togk(hh, 'I', aR['hg']), togk(xx, 'K', aR['xg'])
    dI = "( D ` I' )"
    gd = stkfv(w, ph, 'D', "I'", tv, dd, kk["I'"]['kd'])
    S_ = lambda: Stacks(w, ph, mk, 'D', dd, ne, {})
    A1 = S_().upd("I'", qq, aR['qg'])
    A2 = A1.upd('J', yy, aR['yg'])
    A3 = A2.upd('I', hh, aR['hg'])
    ST0 = UP(UP(A3.D, 'K', xx), "I'", dI)
    e_a = upc(w, ph, A3.D, 'K', xx, "I'", dI, tv, A3.memb, ne('K', "I'"), kk['K']['kd'], gx, kk["I'"]['kd'], gd)
    e_b = upc(w, ph, A2.D, 'I', hh, "I'", dI, tv, A2.memb, ne('I', "I'"), kk['I']['kd'], gh, kk["I'"]['kd'], gd)
    e_c = upc(w, ph, A1.D, 'J', yy, "I'", dI, tv, A1.memb, ne('J', "I'"), kk['J']['kd'], gy, kk["I'"]['kd'], gd)
    e_d = up2(w, ph, 'D', "I'", qq, dI, tv, dd, kk["I'"]['kd'], gq, gd)
    e_e = upid(w, ph, 'D', "I'", tv, dd, kk["I'"]['kd'])
    t_ = ST0
    r1, t1_ = w.rewrite(t_, {}, ph) if False else (None, None)
    # chain of rewrites
    cur = ST0
    steps = []
    def rw_(cur, sub, new, st):
        r, n = w.rewrite(cur, {sub: (new, st)}, ph)
        steps.append(r)
        return n
    n1 = UP(UP(A3.D, "I'", dI), 'K', xx)
    n2 = rw_(n1, UP(A3.D, "I'", dI), UP(UP(A2.D, "I'", dI), 'I', hh), e_b)
    n3 = rw_(n2, UP(A2.D, "I'", dI), UP(UP(A1.D, "I'", dI), 'J', yy), e_c)
    n4 = rw_(n3, UP(A1.D, "I'", dI), UP('D', "I'", dI), e_d)
    n5 = rw_(n4, UP('D', "I'", dI), 'D', e_e)
    assert n5 == UP(UP(UP('D', 'J', yy), 'I', hh), 'K', xx), n5
    # reorder: UPD( UPD( UPD( D , J , yy ) , I , hh ) , K , xx ) = UPD( UPD( UPD( D , K , xx ) , I , hh ) , J , yy )
    B1 = S_().upd('J', yy, aR['yg'])
    e_f = upc(w, ph, 'D', 'J', yy, 'I', hh, tv, dd, ne('J', 'I'), kk['J']['kd'], gy, kk['I']['kd'], gh)
    n6 = rw_(n5, UP(UP('D', 'J', yy), 'I', hh), UP(UP('D', 'I', hh), 'J', yy), e_f)
    B2 = S_().upd('I', hh, aR['hg'])
    e_g = upc(w, ph, B2.D, 'J', yy, 'K', xx, tv, B2.memb, ne('J', 'K'), kk['J']['kd'], gy, kk['K']['kd'], gx)
    n7 = rw_(n6, n6, UP(UP(B2.D, 'K', xx), 'J', yy), e_g) if False else None
    steps.append(e_g)
    n7 = UP(UP(B2.D, 'K', xx), 'J', yy)
    e_h = upc(w, ph, 'D', 'I', hh, 'K', xx, tv, dd, ne('I', 'K'), kk['I']['kd'], gh, kk['K']['kd'], gx)
    n8 = rw_(n7, UP(UP('D', 'I', hh), 'K', xx), UP(UP('D', 'K', xx), 'I', hh), e_h)
    # values
    n9 = rw_(n8, xx, XR_, xrv)
    n10 = rw_(n9, hh, HR_, hrv)
    n11 = rw_(n10, yy, YW, yrv)
    D2 = UP(UP('D', 'K', XR_), 'I', HR_)
    assert n11 == UP(D2, 'J', YW), n11
    # the full chain ST0 = ... = UPD( D2 , J , YW )
    allst = [e_a] + steps
    txt = [ST0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11]
    cur = allst[0]
    for k_ in range(1, len(allst)):
        cur = w.s([cur, allst[k_]], 'eqtrd', '( %s -> %s = %s )' % (ph, ST0, txt[k_ + 1]))
    # ( P' ` R ) = PDB( R ) inside ST0's text
    STP = UP(FAPP(PV_, 'R'), "I'", dI)
    rp, np_ = w.rewrite(STP, {FAPP(PV_, 'R'): (PDB('R'), pv)}, ph)
    assert np_ == ST0, np_
    seq_all = w.s([rp, cur], 'eqtrd', '( %s -> %s = %s )' % (ph, STP, n11))
    assert Da == CLN(PL(PL('P', 1), 0), SS, STP), Da
    deq = clneq(w, ph, PL(PL('P', 1), 0), SS, seq_all, STP, n11)
    t1b, Cb, Db, nb = hrrw(w, ph, t1, Ca, Da, n1 if False else triple_parts(c1)[2], deq=deq)
    n1b = triple_parts(c1)[2]
    # ---- dropNum y
    Wy = '( inclBool o. %s )' % SHG('( R - R )')
    wyb = w.s([aR['sh'], w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, Wy, BITS))
    SD2 = S_().upd('K', XR_, w.s([xrv, aR['xg']], 'eqeltrrd' if False else 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ph, XR_))) if False else None
    xrg = w.s([w.s([xrv], 'eqcomd', '( %s -> %s = %s )' % (ph, XR_, xx)), aR['xg']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, XR_))
    hrg = w.s([w.s([hrv], 'eqcomd', '( %s -> %s = %s )' % (ph, HR_, hh)), aR['hg']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ph, HR_))
    SD2 = S_().upd('K', XR_, xrg).upd('I', HR_, hrg)
    assert SD2.D == D2
    md = {'K': 'J', 'P': PL('P', 1), 'E': 'E', 'W': Wy, 'X': 'Y', 'D': D2}
    exd = dict(ex)
    exd.update({WRD(Wy, BITS): wyb, STKD(D2): SD2.memb})
    t2, c2 = inst(w, ph, 'tmidrop', md, Bld(w, ph, c, exd))
    C2_, D2_, n2 = triple_parts(c2)
    assert C2_ == Db, (C2_, Db)
    t12 = hrseq(w, ph, phm, t1b, t2, Cb, Db, D2_, n1b, n2)
    NT = '( %s + %s )' % (n1b, n2)
    # ---- the bound
    ef = w.s([c['F e. NN0'], w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    gn0 = w.s([c['G e. NN'], w.inst('nnnn0')], 'syl', '( %s -> G e. NN0 )' % ph)
    eg = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    er = w.s([rn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` R ) e. Word 2o )' % ph)
    cb = Closure(w, ph, {'R': ('NN0', rn)})
    ENR = '( # ` ( encodeNat ` R ) )'
    LW = '( # ` %s )' % Wy
    LWQ = '( # ` %s )' % WQ0
    LSH = '( # ` %s )' % SHG('( R - R )')
    wq0w = w.s([w.s([w.s([w.s([rn, rn, rle, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( R - R ) e. NN0 )' % ph), w.inst('encnatcl')], 'syl',
                          '( %s -> ( encodeNat ` ( R - R ) ) e. Word 2o )' % ph), w.inst('tmcibw')], 'syl',
                    '( %s -> ( inclBool o. ( encodeNat ` ( R - R ) ) ) e. Word %s )' % (ph, BITS))], 'id', '') if False else None
    for a_, st_ in [(NF, w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NF))), (NG, w.s([eg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NG))),
                    (ENR, w.s([er, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, ENR))),
                    (LW, w.s([wyb, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))]:
        cb.leaf(a_, 'NN0', st_)
    # # W = g : bwmaplen , ccatlen , repswlen , R - R = 0
    lw1 = w.s([aR['sh'], w.inst('bwmaplen')], 'syl', '( %s -> %s = %s )' % (ph, LW, LSH))
    lw2 = w.s([aR['rw'], eg, w.inst('ccatlen')], 'syl2anc', '( %s -> %s = ( ( # ` ( (/) repeatS ( R - R ) ) ) + %s ) )' % (ph, LSH, NG))
    lw3 = w.s([closed(w, ph, '0el2o', '(/) e. 2o'), aR['rt'], w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS ( R - R ) ) ) = ( R - R ) )' % ph)
    cb.leaf(LSH, 'NN0', w.s([aR['sh'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LSH)))
    cb.leaf('( # ` ( (/) repeatS ( R - R ) ) )', 'NN0', w.s([aR['rw'], w.inst('lencl')], 'syl', '( %s -> ( # ` ( (/) repeatS ( R - R ) ) ) e. NN0 )' % ph))
    # # WQ0 = 0
    eg0 = w.s([w.s([w.s([rr], 'fveq2d', '( %s -> ( encNatGam ` ( R - R ) ) = ( encNatGam ` 0 ) )' % ph),
                    w.s([w.s([closed(w, ph, '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ph),
                         w.s([closed(w, ph, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ph)],
                        'eqtrd', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. (/) ) )' % ph)], 'eqtrd', '( %s -> %s = ( inclBool o. (/) ) )' % (ph, WQ0)),
               closed(w, ph, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd', '( %s -> %s = (/) )' % (ph, WQ0))
    lwq = w.s([w.s([eg0], 'fveq2d', '( %s -> %s = ( # ` (/) ) )' % (ph, LWQ)), closed(w, ph, 'hash0', '( # ` (/) ) = 0')], 'eqtrd', '( %s -> %s = 0 )' % (ph, LWQ))
    cb.leaf(LWQ, 'NN0', w.s([lwq, closed(w, ph, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, LWQ)))
    # |enc R| <_ n
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    rp2 = w.s([w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph), rn, w.inst('bernneq3')], 'syl2anc', '( %s -> R < ( 2 ^ R ) )' % ph)
    blr = w.s([rn, rn, rp2, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` R ) <_ R )' % ph)
    enr = w.s([w.s([rn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` R ) )' % (ph, ENR)), blr], 'eqbrtrd', '( %s -> %s <_ R )' % (ph, ENR))
    MXFG = 'if ( %s <_ %s , %s , %s )' % (NG, NF, NF, NG)
    mxl = ifmax_le(w, ph, NG, NF, '( %s + %s )' % (NF, NG), cb.mem(NG, 'RR'), cb.mem(NF, 'RR'), cb.mem('( %s + %s )' % (NF, NG), 'RR'),
                   linarith(w, ph, [cb.ge0(NF)], '%s <_ ( %s + %s )' % (NG, NF, NG), closure=cb),
                   linarith(w, ph, [cb.ge0(NG)], '%s <_ ( %s + %s )' % (NF, NF, NG), closure=cb))
    cb.leaf(MXFG, 'NN0', w.s([cb.mem(NF, 'NN0'), cb.mem(NG, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXFG)))
    rr0 = w.s([rr], 'id', '') if False else rr
    le = nlinarith(w, ph, [c['R <_ %s' % NF], enr, mxl, lwq, lw1, lw2, lw3, rr0, cb.ge0(NF), cb.ge0(NG)], '%s <_ %s' % (NT, BDM), closure=cb,
                   atoms=[NF, NG, ENR, LW, LWQ, LSH, MXFG, '( # ` ( (/) repeatS ( R - R ) ) )'])
    hrle(w, ph, phm, t12, Cb, D2_, NT, BDM, cb.mem(BDM, 'NN0'), le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
