"""T5: the composites `incr` and `predNum` of TM/Prims.lean: `push comma s ;
incLoop y s ; moveNum s y` (resp. `predLoop`), as ~ tm2hseq chains over
~ tm2fpshn , ~ tm2fincl / ~ tm2fprdl and ~ tm2fmvn ; the exit disjunction
of the loop passes through unchanged (blueprint D3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *
from t5_d_scl import (PK, GK, GJ, HDL, CTY, CTY2, CTY3, PTY, PKTY, GTY, NV, NV2, NVZ, HC,
                      IFA, IFB, ZA, ZB, DISJ_INC, IFPA, IFPB, IFPC, PA, PB, PC, XPX, DISJ_PRD,
                      PEEKST, RATY, RATY2, ZX, CO)

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DJ = '( D ` J )'
YDJ = '( <" Y "> ++ %s )' % DJ
RGW = '( reverse ` %s )' % CO('W')
GA1 = GT("A'"); GA2 = GT('A"'); GE = GT('E')
WZX = '( W ++ %s )' % ZX
UP2 = lambda x, y: UP(UP('D', 'K', x), 'J', y)
NVM = lambda r, z: NVF('F"', r, z)
HCmv = ('A. r e. N A. z e. B\' ( ( C0 ` %s ) = 1o /\\ ( O ` %s ) = z /\\ %s e. N )'
        % (NVM('r', 'z'), NVM('r', 'z'), NVM('r', 'z')))
HEmv = 'A. r e. N ( -. ( C0 ` %s ) = 1o /\\ %s e. N )' % (NVM('r', 'Y'), NVM('r', 'Y'))
RATY3 = 'F" e. %s' % HDL('J')
CTY0 = 'C0 e. ( 2o ^m %s )' % SS
OTY = 'O e. ( %s ^m %s )' % (GK, SS)

ST1 = PUSH('J', CONSTF('T', 'Y'), GA1)
STMOV = POP('J', 'F"', BRANCH('C0', PUSH('K', 'O', GA2), GE))
QINC = BRANCH("C'", PK("P'", GA2), PK('P"', PK("P'", GA2)))
STINC = POP('K', 'F', BRANCH('C', PUSH('J', 'P', GA1), QINC))
PEEKST2 = PEEK('K', "F'", BRANCH('C"', GA2, PK("P'", GA2)))
QPRD = BRANCH("C'", PEEKST2, PK('P"', GA2))
STPRD = POP('K', 'F', BRANCH('C', PUSH('J', 'P', GA1), QPRD))


def tree(pred):
    fun = (((RATY, RATY2, RATY3), (CTY, CTY2, CTY3), CTY0) if pred
           else ((RATY, RATY3), (CTY, CTY2), CTY0))
    lets = ((('Z e. %s' % GK, "Z' e. %s" % GK), ('Z" e. %s' % GK, 'Y e. %s' % GK)) if pred
            else ('Z e. %s' % GK, "Z' e. %s" % GK, 'Z" e. %s' % GK))
    words = (('W e. Word B', ('X e. Word %s' % GK, "X' e. Word %s" % GK)) if pred
             else ('W e. Word B', 'X e. Word %s' % GK))
    return (((PHM, '( M ` A ) = %s' % ST1, "( M ` A' ) = %s" % (STPRD if pred else STINC)),
             '( M ` A" ) = %s' % STMOV),
            ((('A e. %s' % LL, "A' e. %s" % LL), ('A" e. %s' % LL, 'E e. %s' % LL)),
             ('K e. %s' % DG, 'J e. %s' % DG, 'K =/= J'),
             (fun, ((PTY, OTY), (PKTY("P'"), PKTY('P"'))))),
            ((('B C_ %s' % GK, "B' C_ %s" % GK, "B' C_ %s" % GJ), ("G : B --> B'", 'Y e. %s' % GJ),
              (lets, words, 'D e. %s' % STK_T)),
             ('( D ` K ) = %s' % WZX, ('N C_ %s' % SS, HC), (HCmv, HEmv)),
             DISJ_PRD if pred else DISJ_INC))


def composite(lab, pred):
    TREE = tree(pred)
    ph = cj(TREE)
    desc = ('The composite ` predNum ` of TM/Prims.lean: ` push comma s ; predLoop x s ; '
            'moveNum s x ` decrements the top number of stack ` K ` in place, restoring the '
            'scratch stack ` J ` : the run ` W ` of zeros becomes ones ( ` G o. W ` ), and '
            'what follows is settled by the three-way disjunction of ~ tm2fprdl .  Lean: '
            '` predNum_runs ` , whose ` predBits_eq ` is this decomposition.'
            if pred else
            'The composite ` incr ` of TM/Prims.lean: ` push comma s ; incLoop y s ; '
            'moveNum s y ` increments the top number of stack ` K ` in place, restoring the '
            'scratch stack ` J ` : the run ` W ` of ones becomes zeros ( ` G o. W ` ), and '
            'what follows is settled by the two-way disjunction of ~ tm2fincl .  Lean: '
            '` incr_runs ` , whose ` incBits_eq ` is this decomposition.')
    w = W(lab, desc)
    c = Ctx(w, ph, TREE)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ne = c['K e. %s' % DG], c['J e. %s' % DG], c['K =/= J']
    nej = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    dd = c['D e. %s' % STK_T]; ww = c['W e. Word B']; xx = c['X e. Word %s' % GK]
    yj = c['Y e. %s' % GJ]; bk, bpk, bpj = c['B C_ %s' % GK], c["B' C_ %s" % GK], c["B' C_ %s" % GJ]
    gf = c["G : B --> B'"]
    gfj = w.s([gf, bpj, w.inst('fss')], 'syl2anc', '( %s -> %s )' % (ph, GTY))
    dke = c['( D ` K ) = %s' % WZX]; nss = c['N C_ %s' % SS]
    disj = c[DISJ_PRD if pred else DISJ_INC]
    zz = c['Z e. %s' % GK]
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    ys = s1w(w, ph, yj, 'Y', GJ)
    ydjw = ccatw(w, ph, ys, djw, '<" Y ">', DJ, GJ)
    zs = s1w(w, ph, zz, 'Z', GK)
    zxw = ccatw(w, ph, zs, xx, '<" Z ">', 'X', GK)
    gwb = w.s([ww, gf, w.inst('wrdco')], 'syl2anc', "( %s -> %s e. Word B' )" % (ph, CO('W')))
    rgwb = revw(w, ph, gwb, CO('W'), "B'")
    gwj = sswordd(w, ph, gwb, CO('W'), "B'", GJ, bpj)
    rgwj = revw(w, ph, gwj, CO('W'), GJ)
    rgwh = ccatw(w, ph, rgwj, ydjw, RGW, YDJ, GJ)
    # Z0 e. Word GK by cases on the disjunction
    def z0word():
        cases = []
        if pred:
            zp, zpp, yk, xpw = c["Z' e. %s" % GK], c['Z" e. %s' % GK], c['Y e. %s' % GK], c["X' e. Word %s" % GK]
            zps = s1w(w, ph, zp, "Z'", GK); zpps = s1w(w, ph, zpp, 'Z"', GK); yks = s1w(w, ph, yk, 'Y', GK)
            xpxw = ccatw(w, ph, zps, xpw, '<" Z\' ">', "X'", GK)
            pbw = ccatw(w, ph, zpps, xpxw, '<" Z" ">', XPX, GK)
            pcw = ccatw(w, ph, yks, xx, '<" Y ">', 'X', GK)
            specs = [('( X = %s /\\ %s /\\ Z0 = %s )' % (XPX, IFPA, PA), PA, xpxw, 'simp3'),
                     ('( X = %s /\\ %s /\\ Z0 = %s )' % (XPX, IFPB, PB), PB, pbw, 'simp3'),
                     ('( %s /\\ Z0 = %s )' % (IFPC, PC), PC, pcw, 'simprd')]
        else:
            zp, zpp = c["Z' e. %s" % GK], c['Z" e. %s' % GK]
            zps = s1w(w, ph, zp, "Z'", GK); zpps = s1w(w, ph, zpp, 'Z"', GK)
            zaw = ccatw(w, ph, zps, xx, '<" Z\' ">', 'X', GK)
            zppx = ccatw(w, ph, zpps, xx, '<" Z" ">', 'X', GK)
            zbw = ccatw(w, ph, zps, zppx, '<" Z\' ">', '( <" Z" "> ++ X )', GK)
            specs = [('( %s /\\ Z0 = %s )' % (IFA, ZA), ZA, zaw, 'simprd'),
                     ('( %s /\\ Z0 = %s )' % (IFB, ZB), ZB, zbw, 'simprd')]
        for casef, zeq, zw, ref in specs:
            pha = '( %s /\\ %s )' % (ph, casef)
            cs = w.s([], 'simpr', '( %s -> %s )' % (pha, casef))
            if ref == 'simprd':
                czq = w.s([cs], 'simprd', '( %s -> Z0 = %s )' % (pha, zeq))
            else:
                czq = w.s([cs, w.inst(ref)], 'syl', '( %s -> Z0 = %s )' % (pha, zeq))
            zwa = lift(w, zw, pha, '%s e. Word %s' % (zeq, GK))
            cases.append(w.s([czq, zwa], 'eqeltrd', '( %s -> Z0 e. Word %s )' % (pha, GK)))
        dj = DISJ_PRD if pred else DISJ_INC
        allc = w.s(cases, '3jaodan' if pred else 'jaodan', '( ( %s /\\ %s ) -> Z0 e. Word %s )' % (ph, dj, GK))
        return w.s([disj, allc], 'mpdan', '( %s -> Z0 e. Word %s )' % (ph, GK))
    z0w = z0word()
    # ---- stage 1: push Y on J
    D1 = UP('D', 'J', YDJ)
    d1cl = updcl(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjw)
    t1 = applylem(w, ph, 'tm2fpshn',
                  ((phm, c['( M ` A ) = %s' % ST1]),
                   (c['A e. %s' % LL], c["A' e. %s" % LL], (jj, yj)), (dd, nss)),
                  HR(CLN('A', 'N', 'D'), 'T', 'M', CLN("A'", 'N', D1), '1'))
    # ---- stage 2: the loop at D := D1 , H := YDJ , A := A' , E := A"
    UPD1 = lambda x, y: UP(UP(D1, 'K', x), 'J', y)
    PRE2 = UPD1(WZX, YDJ)
    RGWH = '( %s ++ %s )' % (RGW, YDJ)
    D2 = UPD1('Z0', RGWH)
    meq2 = c["( M ` A' ) = %s" % (STPRD if pred else STINC)]
    if pred:
        fun = (((c[RATY], c[RATY2]), (c[CTY], c[CTY2], c[CTY3])), (c[PTY], c[PKTY("P'")], c[PKTY('P"')]))
        lets = (((c['Z e. %s' % GK], c["Z' e. %s" % GK]), (c['Z" e. %s' % GK], c['Y e. %s' % GK])),
                (xx, c["X' e. Word %s" % GK]), ydjw)
    else:
        fun = ((c[RATY], c[CTY], c[CTY2]), (c[PTY], c[PKTY("P'")], c[PKTY('P"')]))
        lets = ((c['Z e. %s' % GK], c["Z' e. %s" % GK], c['Z" e. %s' % GK]), xx, ydjw)
    t2 = applylem(w, ph, 'tm2fprdl' if pred else 'tm2fincl',
                  ((((phm, meq2),
                     ((c["A' e. %s" % LL], c['A" e. %s' % LL]), (kk, jj), ne),
                     (fun, ((bk, gfj), lets, d1cl), ((nss, c[HC]), disj)))),
                   ww),
                  HR(CLN("A'", 'N', PRE2), 'T', 'M', CLN('A"', 'N', D2), '( ( # ` W ) + 1 )'))
    ydjv = elv(w, ph, ydjw, YDJ)
    d1k = updnv(w, ph, 'D', 'J', YDJ, 'K', tv, dd, jj, ydjv, kk, ne)
    d1k2 = w.s([d1k, dke], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, WZX))
    e1 = upidv(w, ph, D1, 'K', WZX, d1k2, tv, d1cl, kk)
    d1j = updkv(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjv)
    e2 = upidv(w, ph, D1, 'J', YDJ, d1j, tv, d1cl, jj)
    tbl = {UP(D1, 'K', WZX): (D1, e1), UP(D1, 'J', YDJ): (D1, e2)}
    g, pre2n = evaluate(w, ph, PRE2, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert pre2n == D1, pre2n
    gc = w.s([g], 'eqcomd', '( %s -> %s = %s )' % (ph, D1, PRE2))
    t2r, _, _, _ = hrrw(w, ph, t2, CLN("A'", 'N', PRE2), CLN('A"', 'N', D2), '( ( # ` W ) + 1 )',
                        ceq=w.s([clneq(w, ph, "A'", 'N', gc, D1, PRE2)], 'eqcomd',
                                '( %s -> %s = %s )' % (ph, CLN("A'", 'N', PRE2), CLN("A'", 'N', D1))))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN('A', 'N', 'D'), CLN("A'", 'N', D1), CLN('A"', 'N', D2), '1', '( ( # ` W ) + 1 )')
    N12 = '( 1 + ( ( # ` W ) + 1 ) )'
    # ---- stage 3: moveNum J -> K at K := J , J := K , W := RGW , X := DJ , H := Z0 , D := D2
    d1kcl = updcl(w, ph, D1, 'K', 'Z0', tv, d1cl, kk, z0w)
    d2cl = updcl(w, ph, UP(D1, 'K', 'Z0'), 'J', RGWH, tv, d1kcl, jj, rgwh)
    RGWYDJ = '( %s ++ ( <" Y "> ++ %s ) )' % (RGW, DJ)
    assert RGWYDJ == RGWH
    PRE3 = UP(UP(D2, 'J', RGWYDJ), 'K', 'Z0')
    RRGW = '( reverse ` %s )' % RGW
    POST3 = UP(UP(D2, 'J', DJ), 'K', '( %s ++ Z0 )' % RRGW)
    N3 = '( ( # ` %s ) + 1 )' % RGW
    t3 = applylem(w, ph, 'tm2fmvn',
                  ((((phm, c['( M ` A" ) = %s' % STMOV]),
                     ((c['A" e. %s' % LL], c['E e. %s' % LL]), (jj, kk), nej),
                     ((c[RATY3], c[CTY0], c[OTY]),
                      ((bpj, bpk), (yj, djw, z0w), d2cl),
                      (nss, (c[HCmv], c[HEmv])))),
                    rgwb)),
                  HR(CLN('A"', 'N', PRE3), 'T', 'M', CLN('E', 'N', POST3), N3))
    rgwhv = elv(w, ph, rgwh, RGWH)
    d2j = updkv(w, ph, UP(D1, 'K', 'Z0'), 'J', RGWH, tv, d1kcl, jj, rgwhv)
    f1 = upidv(w, ph, D2, 'J', RGWH, d2j, tv, d2cl, jj)
    d2k1 = updnv(w, ph, UP(D1, 'K', 'Z0'), 'J', RGWH, 'K', tv, d1kcl, jj, rgwhv, kk, ne)
    d2k2 = updkv(w, ph, D1, 'K', 'Z0', tv, d1cl, kk, elv(w, ph, z0w, 'Z0'))
    d2k = w.s([d2k1, d2k2], 'eqtrd', '( %s -> ( %s ` K ) = Z0 )' % (ph, D2))
    f2 = upidv(w, ph, D2, 'K', 'Z0', d2k, tv, d2cl, kk)
    tbl3 = {UP(D2, 'J', RGWH): (D2, f1), UP(D2, 'K', 'Z0'): (D2, f2)}
    g3, pre3n = evaluate(w, ph, PRE3, {}, extra_rules=(lambda n: tbl3.get(n.text())))
    assert pre3n == D2, pre3n
    g3c = w.s([g3], 'eqcomd', '( %s -> %s = %s )' % (ph, D2, PRE3))
    ceq3 = w.s([clneq(w, ph, 'A"', 'N', g3c, D2, PRE3)], 'eqcomd', '( %s -> %s = %s )' % (ph, CLN('A"', 'N', PRE3), CLN('A"', 'N', D2)))
    # POST3 collapses to UP( D , K , ( ( G o. W ) ++ Z0 ) )
    rr = w.s([gwb, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, RRGW, CO('W')))
    GWZ = '( %s ++ Z0 )' % CO('W')
    gwk = sswordd(w, ph, gwb, CO('W'), "B'", GK, bpk)
    gwzw = ccatw(w, ph, gwk, z0w, CO('W'), 'Z0', GK)
    D2c = UP(UP('D', 'J', RGWH), 'K', 'Z0')
    col1 = up3(w, ph, 'D', 'J', YDJ, 'K', 'Z0', RGWH, tv, dd, nej, jj, ydjw, rgwh, kk, z0w)
    col2 = up4(w, ph, 'D', 'J', RGWH, 'K', 'Z0', DJ, GWZ, tv, dd, nej, jj, rgwh, djw, kk, z0w, gwzw)
    uj = upid(w, ph, 'D', 'J', tv, dd, jj)
    tbl4 = {RRGW: (CO('W'), rr), D2: (D2c, col1),
            UP(UP(D2c, 'J', DJ), 'K', GWZ): (UP(UP('D', 'J', DJ), 'K', GWZ), col2),
            UP('D', 'J', DJ): ('D', uj)}
    g4, postn = evaluate(w, ph, POST3, {}, extra_rules=(lambda n: tbl4.get(n.text())))
    FIN = UP('D', 'K', GWZ)
    assert postn == FIN, postn
    deq3 = clneq(w, ph, 'E', 'N', g4, POST3, FIN)
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', 'N', PRE3), CLN('E', 'N', POST3), N3, ceq=ceq3, deq=deq3)
    tall = hrseq(w, ph, phm, t12, t3r, CLN('A', 'N', 'D'), CLN('A"', 'N', D2), CLN('E', 'N', FIN), N12, N3)
    NALL = '( %s + %s )' % (N12, N3)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    l1 = w.s([gwb, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RGW, CO('W')))
    l2 = w.s([ww, gf, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, CO('W')))
    l3 = w.s([l1, l2], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RGW))
    nrgw = w.s([rgwb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, RGW))
    bound(w, ph, phm, tall, CLN('A', 'N', 'D'), CLN('E', 'N', FIN), NALL, '( ( 2 x. ( # ` W ) ) + 3 )',
          {'( # ` W )': nw, '( # ` %s )' % RGW: nrgw}, hyps=[l3], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fincr'): composite('tm2fincr', False)
    if want('tm2fprdn'): composite('tm2fprdn', True)
