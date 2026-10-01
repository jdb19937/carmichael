"""T5: the subtraction composites: ~ tm2fsbt (` subTail_runs ` : zeroIfBorrow by
disjunction, a push, ~ tm2fmov ), ~ tm2fsub (` sub_runs ` ) and ~ tm2fdec
(` dec_runs ` , the loop with the phantom operand on the output stack)."""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *
from t5_f_rd import BODY, STEPX, STEPY, HA, HDL
from t5_g_core import BI, N0, XF, YF, NF, OFC, DI, RESTQ, LOADG
from t5_h_loop import inst_v
from t5_i_add import hyps_i, CC, CP, CD, C0, FT, FPT, GTY, LTY

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ, GI, GH = GX('K'), GX('J'), GX('I'), GX('H')
QX = '( <" Q "> ++ X )'
QDH = '( <" Q "> ++ ( D ` H ) )'


def sbt_parts(lab_a, lab_a1, lab_a2, lab_e, F, C, Cc, Fl, P, Pm, N, Np):
    """the programs and interfaces of subTail at the given letters"""
    NV = lambda r, z: NVF(F, r, z)
    ZB = BRANCH(Cc, POP('I', F, BRANCH(C, GT(lab_a), PUSH('I', P, LOAD(Fl, GT(lab_a1))))), GT(lab_a1))
    POPST = POP('I', F, BRANCH(C, GT(lab_a), PUSH('I', P, LOAD(Fl, GT(lab_a1)))))
    PUSHH = PUSH('H', CONSTF('T', 'Q'), GT(lab_a2))
    MOV = POP('I', F, BRANCH(C, PUSH('H', Pm, GT(lab_a2)), GT(lab_e)))
    HC = ('A. r e. %s A. z e. B ( ( %s ` r ) = 1o /\\ ( %s ` %s ) = 1o /\\ %s e. %s )'
          % (N, Cc, C, NV('r', 'z'), NV('r', 'z'), N))
    HE = ('A. m e. %s ( ( %s ` m ) = 1o /\\ -. ( %s ` %s ) = 1o /\\ ( ( %s ` %s ) = Q /\\ ( %s ` %s ) e. %s ) )'
          % (N, Cc, C, NV('m', 'Q'), P, NV('m', 'Q'), Fl, NV('m', 'Q'), Np))
    BR = 'A. m e. %s -. ( %s ` m ) = 1o' % (N, Cc)
    MOVH = ('( A. r e. %s A. z e. B ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z ) /\\ A. r e. %s -. ( %s ` %s ) = 1o )'
            % (SS, C, NV('r', 'z'), Pm, NV('r', 'z'), SS, C, NV('r', 'Q')))
    return dict(ZB=ZB, POPST=POPST, PUSHH=PUSHH, MOV=MOV, HC=HC, HE=HE, BR=BR, MOVH=MOVH)


def tm2fsbt():
    lab = 'tm2fsbt'
    p = sbt_parts('A', "A'", 'A"', 'E', 'F', 'C', "C'", "F'", 'P', 'P"', 'N', "N'")
    WQX = '( W ++ %s )' % QX
    DISJ = '( ( ( %s /\\ %s ) /\\ Z0 = (/) ) \\/ ( %s /\\ Z0 = W ) )' % (p['HC'], p['HE'], p['BR'])
    FTY = 'F e. %s' % HDL('I')
    tree = (((PHM, '( M ` A ) = %s' % p['ZB'], "( M ` A' ) = %s" % p['PUSHH']), '( M ` A" ) = %s' % p['MOV']),
            ((('A e. %s' % LL, "A' e. %s" % LL), ('A" e. %s' % LL, 'E e. %s' % LL)),
             ('I e. %s' % DG, 'H e. %s' % DG, 'I =/= H'),
             ((FTY, CC, CP), ('P e. ( %s ^m %s )' % (GI, SS), 'P" e. ( %s ^m %s )' % (GH, SS), "F' e. ( %s ^m %s )" % (SS, SS)))),
            ((('B C_ %s' % GI, 'B C_ %s' % GH), ('Q e. %s' % GI, 'Q e. %s' % GH), ('W e. Word B', 'X e. Word %s' % GI, 'D e. %s' % STK_T)),
             ('( D ` I ) = %s' % WQX, ('N C_ %s' % SS, "N' C_ %s" % SS), p['MOVH']),
             DISJ))
    ph = cj(tree)
    w = W(lab, 'The tail ` zeroIfBorrow z ; push comma w ; moveNum z w ` shared by ` sub ` and '
               '` dec ` (TM/Sub.lean): the reversed difference ` W ` on ` I ` is zeroed if the '
               'guard ` C\' ` is set on the state class ` N ` (~ tm2fzb ) and kept otherwise '
               '(~ tm2fbrg ), so the word ` Z0 ` moved onto ` H ` is ` (/) ` or ` W ` by the '
               'disjunction; ` I ` is left with the rest ` X ` .  Lean: ` subTail_runs ` , whose '
               '` if v.carry then [] else l ` is the disjunction.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    ii, hh, nih = c['I e. %s' % DG], c['H e. %s' % DG], c['I =/= H']
    nhi = w.s([nih], 'necomd', '( %s -> H =/= I )' % ph)
    dd, ww, xx = c['D e. %s' % STK_T], c['W e. Word B'], c['X e. Word %s' % GI]
    bi, bh, qi, qh = c['B C_ %s' % GI], c['B C_ %s' % GH], c['Q e. %s' % GI], c['Q e. %s' % GH]
    nss, npss = c['N C_ %s' % SS], c["N' C_ %s" % SS]
    die = c['( D ` I ) = %s' % WQX]; disj = c[DISJ]
    al, a1l, a2l, el = c['A e. %s' % LL], c["A' e. %s" % LL], c['A" e. %s' % LL], c['E e. %s' % LL]
    ff, cc, cp = c[FTY], c[CC], c[CP]
    pp, pm, fl = c['P e. ( %s ^m %s )' % (GI, SS)], c['P" e. ( %s ^m %s )' % (GH, SS)], c["F' e. ( %s ^m %s )" % (SS, SS)]
    qsi = s1w(w, ph, qi, 'Q', GI); qsh = s1w(w, ph, qh, 'Q', GH)
    qxw = ccatw(w, ph, qsi, xx, '<" Q ">', 'X', GI)
    dhw = stkfv(w, ph, 'D', 'H', tv, dd, hh)
    qdhw = ccatw(w, ph, qsh, dhw, '<" Q ">', '( D ` H )', GH)
    wi = sswordd(w, ph, ww, 'W', 'B', GI, bi)
    wqxw = ccatw(w, ph, wi, qxw, 'W', QX, GI)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    # the pop statement of zeroBody, for tm2fbrg
    ga = gotocl(w, ph, tv, 'A', al); ga1 = gotocl(w, ph, tv, "A'", a1l)
    ldc = loadcl(w, ph, tv, "F'", GT("A'"), fl, ga1)
    puc = pushcl(w, ph, tv, 'I', 'P', LOAD("F'", GT("A'")), ii, pp, ldc)
    brc = brcl(w, ph, tv, 'C', GT('A'), PUSH('I', 'P', LOAD("F'", GT("A'"))), cc, ga, puc)
    popc = popcl(w, ph, tv, 'I', 'F', BRANCH('C', GT('A'), PUSH('I', 'P', LOAD("F'", GT("A'")))), ii, ff, brc)
    Z0QX = '( Z0 ++ %s )' % QX
    DM = UP('D', 'I', Z0QX)
    T1 = HR(CLN('A', 'N', 'D'), 'T', 'M', CLN("A'", SS, DM), '( ( # ` W ) + 1 )')
    GOAL1 = '( %s /\\ ( Z0 e. Word B /\\ ( # ` Z0 ) <_ ( # ` W ) ) )' % T1

    def finish(pha, tri, PRE, POST, n, Ncl, z0eq, zw, lenle, Lf):
        """from tri : PRE ~~> POST in n (POST at class Ncl) reach GOAL1"""
        # POST's stacks = DM, class Ncl C_ S
        d0 = clneq(w, pha, "A'", Ncl, z0eq, concl(w, pha, z0eq).split(' = ')[0] if False else None, None) if False else None
        return None

    # ---- case c : the guard is set, tm2fzb zeroes the number
    pha = '( %s /\\ ( ( %s /\\ %s ) /\\ Z0 = (/) ) )' % (ph, p['HC'], p['HE'])
    La = Lifter(w, pha)
    hce = w.s([], 'simprl', '( %s -> ( %s /\\ %s ) )' % (pha, p['HC'], p['HE']))
    hc = w.s([hce], 'simpld', '( %s -> %s )' % (pha, p['HC'])); he = w.s([hce], 'simprd', '( %s -> %s )' % (pha, p['HE']))
    z0e = w.s([], 'simprr', '( %s -> Z0 = (/) )' % pha)
    PREa = UP('D', 'I', WQX)
    ta = applylem(w, pha, 'tm2fzb',
                  ((((La(phm, PHM), La(c['( M ` A ) = %s' % p['ZB']], '( M ` A ) = %s' % p['ZB'])),
                     ((La(al, 'A e. %s' % LL), La(a1l, "A' e. %s" % LL), La(ii, 'I e. %s' % DG)),
                      ((La(ff, FTY), La(cc, CC), La(cp, CP)), (La(pp, 'P e. ( %s ^m %s )' % (GI, SS)), La(fl, "F' e. ( %s ^m %s )" % (SS, SS))))),
                     (((La(bi, 'B C_ %s' % GI), (La(qi, 'Q e. %s' % GI), La(qi, 'Q e. %s' % GI))), (La(xx, 'X e. Word %s' % GI), La(dd, 'D e. %s' % STK_T))),
                      ((La(nss, 'N C_ %s' % SS), La(npss, "N' C_ %s" % SS)), (hc, he)))),
                    La(ww, 'W e. Word B'))),
                  HR(CLN('A', 'N', PREa), 'T', 'M', CLN("A'", "N'", UP('D', 'I', QX)), '( ( # ` W ) + 1 )'))
    ua = upidv(w, pha, 'D', 'I', WQX, La(die, '( D ` I ) = %s' % WQX), La(tv, 'T e. V'), La(dd, 'D e. %s' % STK_T), La(ii, 'I e. %s' % DG))
    lid = w.s([La(qxw, '%s e. Word %s' % (QX, GI)), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (pha, QX, QX))
    z1 = w.s([z0e], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (pha, Z0QX, QX))
    z2 = w.s([z1, lid], 'eqtrd', '( %s -> %s = %s )' % (pha, Z0QX, QX))
    dme = upeq(w, pha, 'D', 'I', w.s([z2], 'eqcomd', '( %s -> %s = %s )' % (pha, QX, Z0QX)), QX, Z0QX)
    ta2, _, _, _ = hrrw(w, pha, ta, CLN('A', 'N', PREa), CLN("A'", "N'", UP('D', 'I', QX)), '( ( # ` W ) + 1 )',
                        ceq=w.s([clneq(w, pha, 'A', 'N', w.s([ua], 'eqcomd', '( %s -> D = %s )' % (pha, PREa)), 'D', PREa)], 'eqcomd',
                                '( %s -> %s = %s )' % (pha, CLN('A', 'N', PREa), CLN('A', 'N', 'D'))),
                        deq=clneq(w, pha, "A'", "N'", dme, UP('D', 'I', QX), DM))
    z0w_a = w.s([z0e, w.s([w.s([], 'wrd0', '(/) e. Word B')], 'a1i', '( %s -> (/) e. Word B )' % pha)], 'eqeltrd', '( %s -> Z0 e. Word B )' % pha)
    dmcl_a = updcl(w, pha, 'D', 'I', Z0QX, La(tv, 'T e. V'), La(dd, 'D e. %s' % STK_T), La(ii, 'I e. %s' % DG),
                   ccatw(w, pha, sswordd(w, pha, z0w_a, 'Z0', 'B', GI, La(bi, 'B C_ %s' % GI)), La(qxw, '%s e. Word %s' % (QX, GI)), 'Z0', QX, GI))
    cfa = cfgcl(w, pha, "A'", SS, DM, La(tv, 'T e. V'), La(a1l, "A' e. %s" % LL), w.s([w.s([], 'ssid', '%s C_ %s' % (SS, SS))], 'a1i', '( %s -> %s C_ %s )' % (pha, SS, SS)), dmcl_a)
    ta3 = hrssd(w, pha, La(phm, PHM), ta2, CLN('A', 'N', 'D'), CLN("A'", "N'", DM), '( ( # ` W ) + 1 )', CLN("A'", SS, DM),
                clnss(w, pha, "A'", "N'", SS, DM, La(npss, "N' C_ %s" % SS)), cfa)
    h0 = w.s([], 'hash0', '( # ` (/) ) = 0')
    l1 = w.s([w.s([z0e], 'fveq2d', '( %s -> ( # ` Z0 ) = ( # ` (/) ) )' % pha), w.s([h0], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % pha)], 'eqtrd', '( %s -> ( # ` Z0 ) = 0 )' % pha)
    l2 = w.s([La(nw, '( # ` W ) e. NN0'), w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ ( # ` W ) )' % pha)
    l3 = w.s([l1, l2], 'eqbrtrd', '( %s -> ( # ` Z0 ) <_ ( # ` W ) )' % pha)
    ca = w.s([ta3, w.s([z0w_a, l3], 'jca', '( %s -> ( Z0 e. Word B /\\ ( # ` Z0 ) <_ ( # ` W ) ) )' % pha)], 'jca', '( %s -> %s )' % (pha, GOAL1))
    # ---- case n : the guard is clear, tm2fbrg leaves at once
    phb = '( %s /\\ ( %s /\\ Z0 = W ) )' % (ph, p['BR'])
    Lb = Lifter(w, phb)
    br = w.s([], 'simprl', '( %s -> %s )' % (phb, p['BR'])); z0w = w.s([], 'simprr', '( %s -> Z0 = W )' % phb)
    tb = applylem(w, phb, 'tm2fbrg',
                  ((Lb(phm, PHM), Lb(c['( M ` A ) = %s' % p['ZB']], '( M ` A ) = %s' % p['ZB'])),
                   (Lb(al, 'A e. %s' % LL), Lb(a1l, "A' e. %s" % LL), Lb(dd, 'D e. %s' % STK_T)),
                   ((Lb(cp, CP), Lb(popc, '%s e. %s' % (p['POPST'], STMT_T))), (Lb(nss, 'N C_ %s' % SS), br))),
                  HR(CLN('A', 'N', 'D'), 'T', 'M', CLN("A'", 'N', 'D'), '1'))
    zb1 = w.s([z0w], 'oveq1d', '( %s -> %s = %s )' % (phb, Z0QX, WQX))
    zb2 = w.s([zb1, Lb(die, '( D ` I ) = %s' % WQX)], 'eqtr4d', '( %s -> %s = ( D ` I ) )' % (phb, Z0QX))
    ub = upidv(w, phb, 'D', 'I', Z0QX, w.s([zb2], 'eqcomd', '( %s -> ( D ` I ) = %s )' % (phb, Z0QX)), Lb(tv, 'T e. V'), Lb(dd, 'D e. %s' % STK_T), Lb(ii, 'I e. %s' % DG))
    tb2, _, _, _ = hrrw(w, phb, tb, CLN('A', 'N', 'D'), CLN("A'", 'N', 'D'), '1',
                        deq=clneq(w, phb, "A'", 'N', w.s([ub], 'eqcomd', '( %s -> D = %s )' % (phb, DM)), 'D', DM))
    z0w_b = w.s([z0w, Lb(ww, 'W e. Word B')], 'eqeltrd', '( %s -> Z0 e. Word B )' % phb)
    dmcl_b = updcl(w, phb, 'D', 'I', Z0QX, Lb(tv, 'T e. V'), Lb(dd, 'D e. %s' % STK_T), Lb(ii, 'I e. %s' % DG),
                   ccatw(w, phb, sswordd(w, phb, z0w_b, 'Z0', 'B', GI, Lb(bi, 'B C_ %s' % GI)), Lb(qxw, '%s e. Word %s' % (QX, GI)), 'Z0', QX, GI))
    cfb = cfgcl(w, phb, "A'", SS, DM, Lb(tv, 'T e. V'), Lb(a1l, "A' e. %s" % LL), w.s([w.s([], 'ssid', '%s C_ %s' % (SS, SS))], 'a1i', '( %s -> %s C_ %s )' % (phb, SS, SS)), dmcl_b)
    tb3 = hrssd(w, phb, Lb(phm, PHM), tb2, CLN('A', 'N', 'D'), CLN("A'", 'N', DM), '1', CLN("A'", SS, DM),
                clnss(w, phb, "A'", 'N', SS, DM, Lb(nss, 'N C_ %s' % SS)), cfb)
    nwb = Lb(nw, '( # ` W ) e. NN0')
    cl = Closure(w, phb, leaves={'( # ` W )': nwb})
    mcl = cl.mem('( ( # ` W ) + 1 )', 'NN0')
    ge0b = w.s([nwb, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ ( # ` W ) )' % phb)
    le1 = linarith(w, phb, [ge0b], '1 <_ ( ( # ` W ) + 1 )', closure=cl)
    tb4 = hrle(w, phb, Lb(phm, PHM), tb3, CLN('A', 'N', 'D'), CLN("A'", SS, DM), '1', '( ( # ` W ) + 1 )', mcl, le1)
    lb1 = w.s([z0w], 'fveq2d', '( %s -> ( # ` Z0 ) = ( # ` W ) )' % phb)
    lb2 = w.s([lb1, w.s([w.s([nwb, w.inst('nn0red')], 'syl', '( %s -> ( # ` W ) e. RR )' % phb), w.inst('leidd')], 'syl', '( %s -> ( # ` W ) <_ ( # ` W ) )' % phb)],
              'eqbrtrd', '( %s -> ( # ` Z0 ) <_ ( # ` W ) )' % phb)
    cb = w.s([tb4, w.s([z0w_b, lb2], 'jca', '( %s -> ( Z0 e. Word B /\\ ( # ` Z0 ) <_ ( # ` W ) ) )' % phb)], 'jca', '( %s -> %s )' % (phb, GOAL1))
    both = w.s([ca, cb], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ, GOAL1))
    g1 = w.s([disj, both], 'mpdan', '( %s -> %s )' % (ph, GOAL1))
    t1 = w.s([g1], 'simpld', '( %s -> %s )' % (ph, T1))
    zl = w.s([g1], 'simprd', '( %s -> ( Z0 e. Word B /\\ ( # ` Z0 ) <_ ( # ` W ) ) )' % ph)
    z0wd = w.s([zl], 'simpld', '( %s -> Z0 e. Word B )' % ph); z0le = w.s([zl], 'simprd', '( %s -> ( # ` Z0 ) <_ ( # ` W ) )' % ph)
    z0i = sswordd(w, ph, z0wd, 'Z0', 'B', GI, bi)
    z0qxw = ccatw(w, ph, z0i, qxw, 'Z0', QX, GI)
    dmcl = updcl(w, ph, 'D', 'I', Z0QX, tv, dd, ii, z0qxw)
    # ---- stage 2: push Q on H
    D3 = UP(DM, 'H', '( <" Q "> ++ ( %s ` H ) )' % DM)
    t2 = applylem(w, ph, 'tm2fpush',
                  ((phm, c["( M ` A' ) = %s" % p['PUSHH']]), (a1l, a2l, (hh, qh)), dmcl),
                  HR(CLN("A'", SS, DM), 'T', 'M', CLN('A"', SS, D3), '1'))
    dmh = updnv(w, ph, 'D', 'I', Z0QX, 'H', tv, dd, ii, elv(w, ph, z0qxw, Z0QX), hh, nhi)
    e3, D3p = w.rewrite(D3, {'( %s ` H )' % DM: ('( D ` H )', dmh)}, ph)
    assert D3p == UP(DM, 'H', QDH), D3p
    t2r, _, _, _ = hrrw(w, ph, t2, CLN("A'", SS, DM), CLN('A"', SS, D3), '1', deq=clneq(w, ph, 'A"', SS, e3, D3, D3p))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN('A', 'N', 'D'), CLN("A'", SS, DM), CLN('A"', SS, D3p), '( ( # ` W ) + 1 )', '1')
    # ---- stage 3: moveNum I -> H with W := Z0
    d3cl = updcl(w, ph, DM, 'H', QDH, tv, dmcl, hh, qdhw)
    PRE3 = UP(UP(D3p, 'I', Z0QX), 'H', QDH)
    RZ0 = '( reverse ` Z0 )'
    POST3 = UP(UP(D3p, 'I', 'X'), 'H', '( %s ++ %s )' % (RZ0, QDH))
    N3 = '( ( # ` Z0 ) + 1 )'
    mh = c[p['MOVH']]
    mh1 = w.s([mh], 'simpld', '( %s -> %s )' % (ph, p['MOVH'].split(' /\\ A. r e.')[0][2:]))
    mh2 = w.s([mh], 'simprd', '( %s -> A. r e. %s -. ( C ` %s ) = 1o )' % (ph, SS, NVF('F', 'r', 'Q')))
    t3 = applylem(w, ph, 'tm2fmov',
                  ((((phm, c['( M ` A" ) = %s' % p['MOV']]),
                     ((a2l, el), (ii, hh), nih),
                     ((ff, cc, pm), ((bi, bh), (qi, xx, qdhw), d3cl), (mh1, mh2))),
                    z0wd)),
                  HR(CLN('A"', SS, PRE3), 'T', 'M', CLN('E', SS, POST3), N3))
    d3i = w.s([updnv(w, ph, DM, 'H', QDH, 'I', tv, dmcl, hh, elv(w, ph, qdhw, QDH), ii, nih),
               updkv(w, ph, 'D', 'I', Z0QX, tv, dd, ii, elv(w, ph, z0qxw, Z0QX))], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, D3p, Z0QX))
    f1 = upidv(w, ph, D3p, 'I', Z0QX, d3i, tv, d3cl, ii)
    f2 = upidv(w, ph, D3p, 'H', QDH, updkv(w, ph, DM, 'H', QDH, tv, dmcl, hh, elv(w, ph, qdhw, QDH)), tv, d3cl, hh)
    tbl3 = {UP(D3p, 'I', Z0QX): (D3p, f1), UP(D3p, 'H', QDH): (D3p, f2)}
    g3, pre3n = evaluate(w, ph, PRE3, {}, extra_rules=(lambda n: tbl3.get(n.text())))
    assert pre3n == D3p, pre3n
    ceq3 = w.s([clneq(w, ph, 'A"', SS, w.s([g3], 'eqcomd', '( %s -> %s = %s )' % (ph, D3p, PRE3)), D3p, PRE3)], 'eqcomd',
               '( %s -> %s = %s )' % (ph, CLN('A"', SS, PRE3), CLN('A"', SS, D3p)))
    RZ0QDH = '( %s ++ %s )' % (RZ0, QDH)
    rz0h = sswordd(w, ph, revw(w, ph, z0wd, 'Z0', 'B'), RZ0, 'B', GH, bh)
    rz0qdhw = ccatw(w, ph, rz0h, qdhw, RZ0, QDH, GH)
    col = up4(w, ph, 'D', 'I', Z0QX, 'H', QDH, 'X', RZ0QDH, tv, dd, nih, ii, z0qxw, xx, hh, qdhw, rz0qdhw)
    FIN = UP(UP('D', 'I', 'X'), 'H', RZ0QDH)
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', SS, PRE3), CLN('E', SS, POST3), N3, ceq=ceq3, deq=clneq(w, ph, 'E', SS, col, POST3, FIN))
    tall = hrseq(w, ph, phm, t12, t3r, CLN('A', 'N', 'D'), CLN('A"', SS, D3p), CLN('E', SS, FIN), '( ( ( # ` W ) + 1 ) + 1 )', N3)
    nz0 = w.s([z0wd, w.inst('lencl')], 'syl', '( %s -> ( # ` Z0 ) e. NN0 )' % ph)
    bound(w, ph, phm, tall, CLN('A', 'N', 'D'), CLN('E', SS, FIN), '( ( ( ( # ` W ) + 1 ) + 1 ) + %s )' % N3,
          '( ( 2 x. ( # ` W ) ) + 3 )', {'( # ` W )': nw, '( # ` Z0 )': nz0}, hyps=[z0le], qed=True)
    return w.run()


def subJ(t, dec):
    return re.sub(r'(?<![A-Za-z"\'])J(?![A-Za-z"\'0-9_])', 'H', t) if dec else t


def subasm(lab, dec):
    """tm2fsub (dec = False) and tm2fdec (dec = True): init ; the subtractor loop ; subTail"""
    cmp = False
    n0 = N0(cmp)
    Jv = 'H' if dec else 'J'
    GJv = GX(Jv)
    Q = GT('E"') if False else None
    # the loop: label A, exit A" (the zeroBody label)
    QEX = GT('A"')
    REST = RESTQ(cmp, QEX)
    BODYQ = subJ(BODY(REST), dec)
    INIT = LOAD('L', PUSH('I', CONSTF('T', 'Q'), GT('A')))
    h = {k: subJ(v, dec) for k, v in hyps_i(cmp).items()}
    ON = OFC(n0)
    EXIT = subJ("A. p e. %s ( ( C\" ` p ) = 1o /\\ p e. N' )" % ON, dec)
    INITH = 'A. r e. N0 ( L ` r ) e. %s' % NF('0')
    p = sbt_parts('A"', "E'", 'E"', 'E', 'F"', 'C1_', 'C0', "L'", "P'", 'P"', "N'", 'N"')
    DISJ = '( ( ( %s /\\ %s ) /\\ Z" = (/) ) \\/ ( %s /\\ Z" = Z ) )' % (p['HC'], p['HE'], p['BR'])
    X0, Y0 = '( X ` 0 ) = ( D ` K )', subJ('( Y ` 0 ) = ( D ` J )', dec)
    FPTv = subJ(FPT, dec)
    PT, PPT, PMT = 'P e. ( %s ^m %s )' % (GI, SS), "P' e. ( %s ^m %s )" % (GI, SS), 'P" e. ( %s ^m %s )' % (GH, SS)
    FMT = 'F" e. %s' % HDL('I')
    LPT = "L' e. ( %s ^m %s )" % (SS, SS)
    C1 = 'C1_ e. ( 2o ^m %s )' % SS
    idx = ('K e. %s' % DG, 'I e. %s' % DG, 'H e. %s' % DG) if dec else (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, 'H e. %s' % DG))
    dist = ('K =/= H', 'K =/= I', 'H =/= I') if dec else (('K =/= J', 'K =/= I', 'J =/= I'), ('H =/= K', 'H =/= J', 'H =/= I'))
    tree = ((((PHM, "( M ` A' ) = %s" % INIT, '( M ` A ) = %s' % BODYQ), ('( M ` A" ) = %s' % p['ZB'], "( M ` E' ) = %s" % p['PUSHH'], '( M ` E" ) = %s' % p['MOV'])),
             ((("A' e. %s" % LL, 'A e. %s' % LL, 'A" e. %s' % LL), ("E' e. %s" % LL, 'E" e. %s' % LL, 'E e. %s' % LL)), idx, dist),
             ((((CC, CP, CD), (C0, C1)), ((FT, FPTv, FMT), (PT, PPT, PMT), (GTY, LTY, LPT))),
              ((('Z e. Word %s' % GI, 'Z e. Word B'), ('B C_ %s' % GI, 'B C_ %s' % GH), ('Q e. %s' % GI, 'Q e. %s' % GH)),
               ('D e. %s' % STK_T, ('N0 C_ %s' % SS, "N' C_ %s" % SS, 'N" C_ %s' % SS))),
              ((INITH, p['MOVH']), DISJ))),
            (((h['famn'], h['famxy']), (X0, Y0)), ((h['steps'], h['has']), (h['bis'], EXIT))))
    ph = cj(tree)
    desc = ('The decrement ` dec ` of TM/Sub.lean: ` subLoop x w z true true ; zeroIfBorrow z ; push comma w ; '
            'moveNum z w ` --- the subtractor loop with the phantom operand on the output stack ` H ` '
            '(never read: the consumer takes ` R\' = (/) ` and ` Y ` constant), then the tail '
            '~ tm2fsbt .  Lean: ` decLoop_runs ` and ` dec_runs ` .' if dec else
            'The subtractor ` sub ` of TM/Sub.lean: ` subLoop x y z false false ; zeroIfBorrow z ; '
            'push comma w ; moveNum z w ` .  The initialising load-and-push (~ tm2flpg ), the loop '
            '~ tm2fsbl leaving the difference bits ` Z ` reversed on ` I ` and the borrow in ` N\' ` , '
            'then the tail ~ tm2fsbt , whose disjunction decides whether ` H ` receives ` Z ` or ` (/) ` '
            '(` Z" ` ).  Lean: ` subLoop_runs ` and ` sub_runs ` .')
    w = W(lab, desc)
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, ii, hh = c['K e. %s' % DG], c['I e. %s' % DG], c['H e. %s' % DG]
    jj = hh if dec else c['J e. %s' % DG]
    if dec:
        nkj, nki, nji = c['K =/= H'], c['K =/= I'], c['H =/= I']
        nhk, nhi = w.s([nkj], 'necomd', '( %s -> H =/= K )' % ph), c['H =/= I']
    else:
        nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
        nhk, nhj, nhi = c['H =/= K'], c['H =/= J'], c['H =/= I']
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph); nij = w.s([nji], 'necomd', '( %s -> I =/= %s )' % (ph, Jv))
    nih = w.s([nhi], 'necomd', '( %s -> I =/= H )' % ph)
    dd, zw, zb = c['D e. %s' % STK_T], c['Z e. Word %s' % GI], c['Z e. Word B']
    bi, bh, qi, qh = c['B C_ %s' % GI], c['B C_ %s' % GH], c['Q e. %s' % GI], c['Q e. %s' % GH]
    n0s0, npss, nqss = c['N0 C_ %s' % SS], c["N' C_ %s" % SS], c['N" C_ %s' % SS]
    disj = c[DISJ]
    n0cl = w.s([zw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, n0))
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    qsi = s1w(w, ph, qi, 'Q', GI)
    QDI = '( <" Q "> ++ %s )' % DI
    qdiw = ccatw(w, ph, qsi, diw, '<" Q ">', DI, GI)
    RZ = '( reverse ` Z )'
    rzb = revw(w, ph, zb, 'Z', 'B'); rzi = sswordd(w, ph, rzb, RZ, 'B', GI, bi)
    RZQDI = '( %s ++ %s )' % (RZ, QDI)
    rzqdiw = ccatw(w, ph, rzi, qdiw, RZ, QDI, GI)
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([n0cl, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ph, n0))
    z0fz = w.s([w.s([z0a, n0cl, ge0], '3jca', '( %s -> ( 0 e. NN0 /\\ %s e. NN0 /\\ 0 <_ %s ) )' % (ph, n0, n0)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, n0))
    fn0, _ = inst_v(w, ph, c[h['famn']], subJ('( %s C_ %s /\\ %s C_ %s )' % (NF('i'), SS, OFC('i'), SS), dec), 'i', '0', z0fz)
    n0s = w.s([fn0], 'simpld', '( %s -> %s C_ %s )' % (ph, NF('0'), SS))
    n1n = w.s([n0cl, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, n0))
    n1r = w.s([n1n, w.inst('nn0red')], 'syl', '( %s -> ( %s + 1 ) e. RR )' % (ph, n0))
    n1fz1 = w.s([w.s([n1n, n1n, w.s([n1r, w.inst('leidd')], 'syl', '( %s -> ( %s + 1 ) <_ ( %s + 1 ) )' % (ph, n0, n0))], '3jca',
                     '( %s -> ( ( %s + 1 ) e. NN0 /\\ ( %s + 1 ) e. NN0 /\\ ( %s + 1 ) <_ ( %s + 1 ) ) )' % (ph, n0, n0, n0, n0)),
                 w.inst('elfz2nn0')], 'sylibr', '( %s -> ( %s + 1 ) e. ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    fx1, _ = inst_v(w, ph, c[h['famxy']], subJ('( %s e. Word %s /\\ %s e. Word %s )' % (XF('i'), GK, YF('i'), GJ), dec), 'i', '( %s + 1 )' % n0, n1fz1)
    X1, Y1 = XF('( %s + 1 )' % n0), YF('( %s + 1 )' % n0)
    x1w = w.s([fx1], 'simpld', '( %s -> %s e. Word %s )' % (ph, X1, GK)); y1w = w.s([fx1], 'simprd', '( %s -> %s e. Word %s )' % (ph, Y1, GJv))
    # ---- stage 1: init
    D1 = UP('D', 'I', QDI)
    d1cl = updcl(w, ph, 'D', 'I', QDI, tv, dd, ii, qdiw)
    t1 = applylem(w, ph, 'tm2flpg',
                  ((phm, c["( M ` A' ) = %s" % INIT]), ((c["A' e. %s" % LL], c['A e. %s' % LL], dd), (ii, qi)),
                   (c[LTY], (n0s0, n0s), c[INITH])),
                  HR(CLN("A'", 'N0', 'D'), 'T', 'M', CLN('A', NF('0'), D1), '1'))
    # ---- stage 2: the loop at D := D1 (J := H when dec)
    qdiv = elv(w, ph, qdiw, QDI)
    d1k = updnv(w, ph, 'D', 'I', QDI, 'K', tv, dd, ii, qdiv, kk, nki)
    d1j = updnv(w, ph, 'D', 'I', QDI, Jv, tv, dd, ii, qdiv, jj, nji)
    x01 = w.s([c[X0], d1k], 'eqtr4d', '( %s -> ( X ` 0 ) = ( %s ` K ) )' % (ph, D1))
    y01 = w.s([c[Y0], d1j], 'eqtr4d', '( %s -> ( Y ` 0 ) = ( %s ` %s ) )' % (ph, D1, Jv))
    POST2 = UP(UP(UP(D1, 'I', '( %s ++ ( %s ` I ) )' % (RZ, D1)), 'K', X1), Jv, Y1)
    t2 = applylem(w, ph, 'tm2fsbl',
                  (((phm, c['( M ` A ) = %s' % BODYQ]),
                    ((c['A e. %s' % LL], c['A" e. %s' % LL]), (kk, jj, ii), (nkj, nki, nji)),
                    ((c[CC], c[CP], c[CD]), ((c[FT], c[FPTv]), (c[PT], c[GTY])), (zw, (d1cl, npss)))),
                   (((c[h['famn']], c[h['famxy']]), (x01, y01)), ((c[h['steps']], c[h['has']]), (c[h['bis']], c[EXIT])))),
                  HR(CLN('A', NF('0'), D1), 'T', 'M', CLN('A"', "N'", POST2), '( %s + 1 )' % n0))
    d1i = updkv(w, ph, 'D', 'I', QDI, tv, dd, ii, qdiv)
    u2 = up2(w, ph, 'D', 'I', QDI, RZQDI, tv, dd, ii, qdiw, rzqdiw)
    tbl2 = {'( %s ` I )' % D1: (QDI, d1i), UP(D1, 'I', RZQDI): (UP('D', 'I', RZQDI), u2)}
    e2, D2 = evaluate(w, ph, POST2, {}, extra_rules=(lambda n: tbl2.get(n.text())))
    BI_ = UP('D', 'I', RZQDI)
    assert D2 == UP(UP(BI_, 'K', X1), Jv, Y1), D2
    t2r, _, _, _ = hrrw(w, ph, t2, CLN('A', NF('0'), D1), CLN('A"', "N'", POST2), '( %s + 1 )' % n0, deq=clneq(w, ph, 'A"', "N'", e2, POST2, D2))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN("A'", 'N0', 'D'), CLN('A', NF('0'), D1), CLN('A"', "N'", D2), '1', '( %s + 1 )' % n0)
    N12 = '( 1 + ( %s + 1 ) )' % n0
    # ---- stage 3: the tail at W := RZ , X := DI , D := D2 , N := N' , N' := N" , Z0 := ( reverse ` Z" )
    bicl = updcl(w, ph, 'D', 'I', RZQDI, tv, dd, ii, rzqdiw)
    bkcl = updcl(w, ph, BI_, 'K', X1, tv, bicl, kk, x1w)
    d2cl = updcl(w, ph, UP(BI_, 'K', X1), Jv, Y1, tv, bkcl, jj, y1w)
    i2 = updnv(w, ph, UP(BI_, 'K', X1), Jv, Y1, 'I', tv, bkcl, jj, elv(w, ph, y1w, Y1), ii, nij)
    i3 = updnv(w, ph, BI_, 'K', X1, 'I', tv, bicl, kk, elv(w, ph, x1w, X1), ii, nik)
    i4 = updkv(w, ph, 'D', 'I', RZQDI, tv, dd, ii, elv(w, ph, rzqdiw, RZQDI))
    d2i = w.s([i2, w.s([i3, i4], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, UP(BI_, 'K', X1), RZQDI))], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, D2, RZQDI))
    RZP = '( reverse ` Z" )'
    # the tail's disjunction at Z0 := RZP from ours
    pt = sbt_parts('A"', "E'", 'E"', 'E', 'F"', 'C1_', 'C0', "L'", "P'", 'P"', "N'", 'N"')
    DISJT = '( ( ( %s /\\ %s ) /\\ %s = (/) ) \\/ ( %s /\\ %s = %s ) )' % (pt['HC'], pt['HE'], RZP, pt['BR'], RZP, RZ)
    pha = '( %s /\\ ( ( %s /\\ %s ) /\\ Z" = (/) ) )' % (ph, pt['HC'], pt['HE'])
    hce = w.s([], 'simprl', '( %s -> ( %s /\\ %s ) )' % (pha, pt['HC'], pt['HE']))
    zpe = w.s([], 'simprr', '( %s -> Z" = (/) )' % pha)
    r0 = w.s([], 'rev0', '( reverse ` (/) ) = (/)')
    zr = w.s([w.s([zpe], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (pha, RZP)), w.s([r0], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % pha)], 'eqtrd', '( %s -> %s = (/) )' % (pha, RZP))
    da = w.s([w.s([hce, zr], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ %s = (/) ) )' % (pha, pt['HC'], pt['HE'], RZP))], 'orcd', '( %s -> %s )' % (pha, DISJT))
    phb = '( %s /\\ ( %s /\\ Z" = Z ) )' % (ph, pt['BR'])
    brs = w.s([], 'simprl', '( %s -> %s )' % (phb, pt['BR'])); zze = w.s([], 'simprr', '( %s -> Z" = Z )' % phb)
    zr2 = w.s([zze], 'fveq2d', '( %s -> %s = %s )' % (phb, RZP, RZ))
    db = w.s([w.s([brs, zr2], 'jca', '( %s -> ( %s /\\ %s = %s ) )' % (phb, pt['BR'], RZP, RZ))], 'olcd', '( %s -> %s )' % (phb, DISJT))
    dj = w.s([disj, w.s([da, db], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ, DISJT))], 'mpdan', '( %s -> %s )' % (ph, DISJT))
    QDH = '( <" Q "> ++ ( D2 ` H ) )'.replace('D2', D2)
    RZPQDH = '( ( reverse ` %s ) ++ %s )' % (RZP, QDH)
    POST3 = UP(UP(D2, 'I', DI), 'H', RZPQDH)
    mh = c[pt['MOVH']]
    t3 = applylem(w, ph, 'tm2fsbt',
                  ((((phm, c['( M ` A" ) = %s' % pt['ZB']], c["( M ` E' ) = %s" % pt['PUSHH']]), c['( M ` E" ) = %s' % pt['MOV']]),
                    (((c['A" e. %s' % LL], c["E' e. %s" % LL]), (c['E" e. %s' % LL], c['E e. %s' % LL])), (ii, hh, nih),
                     ((c[FMT], c[C1], c[C0]), (c[PPT], c[PMT], c[LPT]))),
                    (((bi, bh), (qi, qh), (rzb, diw, d2cl)), (d2i, (npss, nqss), mh), dj))),
                  HR(CLN('A"', "N'", D2), 'T', 'M', CLN('E', SS, POST3), '( ( 2 x. ( # ` %s ) ) + 3 )' % RZ))
    # POST3 collapses; ( D2 ` H ) and ( reverse ` ( reverse ` Z" ) )
    zpw = w.s([disj, w.s([w.s([zpe, w.s([w.s([], 'wrd0', '(/) e. Word B')], 'a1i', '( %s -> (/) e. Word B )' % pha)], 'eqeltrd', '( %s -> Z" e. Word B )' % pha),
                          w.s([zze, lift(w, zb, phb, 'Z e. Word B')], 'eqeltrd', '( %s -> Z" e. Word B )' % phb)], 'jaodan',
                         '( ( %s /\\ %s ) -> Z" e. Word B )' % (ph, DISJ))], 'mpdan', '( %s -> Z" e. Word B )' % ph)
    rr = w.s([zpw, w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = Z" )' % (ph, RZP))
    c3c = applylem(w, ph, 'tm2stkup3c',
                   (((tv, dd), (nkj, nki, nji)), (ii, (rzqdiw, diw)), ((kk, x1w), (jj, y1w))),
                   '%s = %s' % (UP(D2, 'I', DI), UP(UP(UP('D', 'I', DI), 'K', X1), Jv, Y1)))
    ui = upid(w, ph, 'D', 'I', tv, dd, ii)
    tbl = {RZP and '( reverse ` %s )' % RZP: ('Z"', rr), UP(D2, 'I', DI): (UP(UP(UP('D', 'I', DI), 'K', X1), Jv, Y1), c3c), UP('D', 'I', DI): ('D', ui)}
    if dec:
        h1 = updkv(w, ph, UP(BI_, 'K', X1), 'H', Y1, tv, bkcl, hh, elv(w, ph, y1w, Y1))
        tbl['( %s ` H )' % D2] = (Y1, h1)
        zpq = '( Z" ++ ( <" Q "> ++ %s ) )' % Y1
        zph = sswordd(w, ph, zpw, 'Z"', 'B', GH, bh)
        qsh = s1w(w, ph, qh, 'Q', GH)
        zpqw = ccatw(w, ph, zph, ccatw(w, ph, qsh, y1w, '<" Q ">', Y1, GH), 'Z"', '( <" Q "> ++ %s )' % Y1, GH)
        dkcl = updcl(w, ph, 'D', 'K', X1, tv, dd, kk, x1w)
        cm2 = up2(w, ph, UP('D', 'K', X1), 'H', Y1, zpq, tv, dkcl, hh, y1w, zpqw)
        tbl[UP(UP(UP('D', 'K', X1), 'H', Y1), 'H', zpq)] = (UP(UP('D', 'K', X1), 'H', zpq), cm2)
        FIN = UP(UP('D', 'K', X1), 'H', zpq)
    else:
        h1 = updnv(w, ph, UP(BI_, 'K', X1), 'J', Y1, 'H', tv, bkcl, jj, elv(w, ph, y1w, Y1), hh, nhj)
        h2 = updnv(w, ph, BI_, 'K', X1, 'H', tv, bicl, kk, elv(w, ph, x1w, X1), hh, nhk)
        h3 = updnv(w, ph, 'D', 'I', RZQDI, 'H', tv, dd, ii, elv(w, ph, rzqdiw, RZQDI), hh, nhi)
        d2h = w.s([h1, w.s([h2, h3], 'eqtrd', '( %s -> ( %s ` H ) = ( D ` H ) )' % (ph, UP(BI_, 'K', X1)))], 'eqtrd', '( %s -> ( %s ` H ) = ( D ` H ) )' % (ph, D2))
        tbl['( %s ` H )' % D2] = ('( D ` H )', d2h)
        FIN = UP(UP(UP('D', 'K', X1), 'J', Y1), 'H', '( Z" ++ ( <" Q "> ++ ( D ` H ) ) )')
    g, postn = evaluate(w, ph, POST3, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert postn == FIN, (postn, FIN)
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', "N'", D2), CLN('E', SS, POST3), '( ( 2 x. ( # ` %s ) ) + 3 )' % RZ, deq=clneq(w, ph, 'E', SS, g, POST3, FIN))
    tall = hrseq(w, ph, phm, t12, t3r, CLN("A'", 'N0', 'D'), CLN('A"', "N'", D2), CLN('E', SS, FIN), N12, '( ( 2 x. ( # ` %s ) ) + 3 )' % RZ)
    rl = w.s([zb, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` Z ) )' % (ph, RZ))
    nrz = w.s([rzb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, RZ))
    bound(w, ph, phm, tall, CLN("A'", 'N0', 'D'), CLN('E', SS, FIN), '( %s + ( ( 2 x. ( # ` %s ) ) + 3 ) )' % (N12, RZ),
          '( ( 3 x. ( # ` Z ) ) + 5 )', {n0: n0cl, '( # ` %s )' % RZ: nrz}, hyps=[rl], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fsbt'): tm2fsbt()
    if want('tm2fsub'): subasm('tm2fsub', False)
    if want('tm2fdec'): subasm('tm2fdec', True)
