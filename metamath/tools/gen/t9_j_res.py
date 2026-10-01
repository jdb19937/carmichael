"""T9: the extraction loop's state sequence against Algorithm.lean's ` extractGo ` (Lean ` extractGo_some ` ,
` extractGo_none ` , and the iteration count against the cost).

  exgo1   one pool element: ` extractGo ` on ` p :: V ` is the hit pair (when the step hits) or ` extractGo ` on ` V ` from
          the next state, and costs at least one unit more
  exres   ` ( 1st ` extractGo ) ` is ` inl <. m , used >. ` of the state at the stop index when that step hit, ` inr (/) `
          otherwise, and the stop index is at most the cost

    MM_DB=sorties/t9.mm python3 tools/gen/t9_j_res.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
from t9_h_seq import (PH_S, SQW, ST_S0, ST_SP1, ST_SCL, ST_OPV, ST_OPCL, ST_IP, RW_, HI)

SEL = sys.argv[1:]
T_G = (('L e. NN', 'G e. NN0'), ('Z e. %s' % STY, 'F e. NN0', 'V e. Word NN0'))
PH_G = cj(T_G)
ZPG = '( Z ( L ExStOp G ) F )'
EGV = lambda z: EGO('L', 'G', 'V', ZM(z), ZU(z), ZA(z))
EG1 = EGO('L', 'G', '( <" F "> ++ V )', ZM('Z'), ZU('Z'), ZA('Z'))
IFH = lambda z, a, b: 'if ( %s = 1o , %s , %s )' % (ZH(z), a, b)
ST_G1 = ('( %s -> ( ( 1st ` %s ) = %s /\\ ( %s + 1 ) <_ ( 2nd ` %s ) ) )'
         % (PH_G, EG1, IFH(ZPG, '( inl ` <. %s , %s >. )' % (ZM(ZPG), ZU(ZPG)), '( 1st ` %s )' % EGV(ZPG)), IFH(ZPG, '0', '( 2nd ` %s )' % EGV(ZPG)), EG1))


def exgo1():
    lab = 'exgo1'
    ph = PH_G
    w = W(lab, 'One pool element of Lean\'s ` extractGo ` against ~ df-exstop : on ` p :: V ` from the state ` Z ` the result '
               'is the hit pair ` ( m\' , S ++ used ) ` when the step hits and ` extractGo ` on ` V ` from the next state otherwise, '
               'and the cost grows by at least one (~ extractgocsn , ~ extractgocss ).')
    s = w.s
    c = Ctx(w, ph, T_G)
    ln, gn, zs, fn, vw = c['L e. NN'], c['G e. NN0'], c['Z e. %s' % STY], c['F e. NN0'], c['V e. Word NN0']
    T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
    mz = s([zs, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, ZM('Z')))
    z2 = s([zs, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` Z ) e. %s )' % (ph, T23))
    uz = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ZU('Z')))
    z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` Z ) ) e. ( Tbl X. 2o ) )' % ph)
    az = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, ZA('Z')))
    AZ = ZA('Z')
    A1 = DP1('L', 'F', AZ)
    SL = SLF('L', 'F', AZ)
    dp = s([s([s([ln, fn], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % ph), az], 'jca', '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ %s e. Tbl ) )' % (ph, AZ)),
            w.inst('dpstepcl')], 'syl', '( %s -> %s e. ( Tbl X. NN0 ) )' % (ph, DPS_('L', 'F', AZ)))
    a1 = s([dp, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, A1))
    DPC = '( 2nd ` %s )' % DPS_('L', 'F', AZ)
    dpc = s([dp, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, DPC))
    opv = s([s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), s([zs, fn], 'jca', '( %s -> ( Z e. %s /\\ F e. NN0 ) )' % (ph, STY))],
               'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ ( Z e. %s /\\ F e. NN0 ) ) )' % (ph, STY)), w.inst('exstopv')], 'syl',
            '( %s -> %s = %s )' % (ph, ZPG, STOPB('L', 'G', 'Z', 'F')))
    ex_leaves = {'N e. NN0': gn, 'M e. NN0': mz}
    def ego_inst(pc, lab_, cond, cst):
        """( pc -> EG1 = ... ) by extractgocsn / extractgocss"""
        Lp = lambda st: Lft(w, pc, ph, st)
        ante, concl_ = split_imp(stmt(lab_))
        mp = {'N': 'G', 'M': ZM('Z'), 'U': ZU('Z'), 'T': AZ, 'P': 'F', 'W': 'V'}
        tree = tsub(parse_conj(ante), mp)
        ex = {'L e. NN': Lp(ln), 'G e. NN0': Lp(gn), '%s e. NN0' % ZM('Z'): Lp(mz), '%s e. Word NN0' % ZU('Z'): Lp(uz), '%s e. Tbl' % AZ: Lp(az),
              'F e. NN0': Lp(fn), 'V e. Word NN0': Lp(vw), cond: cst}
        class _NoCtx:
            def __getitem__(self, k):
                raise KeyError(k)
        bld = Builder(w, pc, _NoCtx(), ex)
        st_ = bld(tree)
        return s([st_, w.inst(lab_)], 'syl', '( %s -> %s )' % (pc, tsub_text(concl_, mp)))
    CON = ST_G1[len(ph) + 6:-2]
    IF1 = IFH(ZPG, '( inl ` <. %s , %s >. )' % (ZM(ZPG), ZU(ZPG)), '( 1st ` %s )' % EGV(ZPG))
    IF2 = IFH(ZPG, '0', '( 2nd ` %s )' % EGV(ZPG))

    def egn(pc, V_, m_, u_, a_, ms, us, as_):
        """( pc -> ( 2nd ` EGO ) e. NN0 )"""
        E = EGO('L', 'G', V_, m_, u_, a_)
        t = s([s([s([s([s([Lft(w, pc, ph, ln), Lft(w, pc, ph, gn)], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % pc),
                        Lft(w, pc, ph, vw) if V_ == 'V' else None], 'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, V_)),
                      ms], 'jca', '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) )' % (pc, V_, m_)),
                    us], 'jca', '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, V_, m_, u_)),
                  as_], 'jca', '( %s -> ( ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )'
                  % (pc, V_, m_, u_, a_))
        ec = s([t, w.inst('extractgocl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (pc, E))
        return s([ec, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, E))

    def pr12(pc, eg, PAIR, X, Y):
        """from eg : ( pc -> EG1 = <. X , Y >. ): ( 1st EG1 ) = X , ( 2nd EG1 ) = Y"""
        xv, yv = vex_(w, pc, X) if not X.startswith('( inl') else s([s([], 'fvex', '%s e. _V' % X)], 'a1i', '( %s -> %s e. _V )' % (pc, X)), vex_(w, pc, Y)
        f1 = s([s([eg], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (pc, EG1, PAIR)), s([xv, yv, w.inst('op1stg')], 'syl2anc',
               '( %s -> ( 1st ` %s ) = %s )' % (pc, PAIR, X))], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (pc, EG1, X))
        f2 = s([s([eg], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pc, EG1, PAIR)), s([xv, yv, w.inst('op2ndg')], 'syl2anc',
               '( %s -> ( 2nd ` %s ) = %s )' % (pc, PAIR, Y))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pc, EG1, Y))
        return f1, f2

    def fin(pc, zp_h_true, i1, i2, f1, f2, E2, X1, Y2, cl_leaves, hyps):
        """assemble CON under pc: i1 : IF1 = X1-form, f1 : 1st EG1 = X1; i2 : IF2 = Z2, f2 : 2nd EG1 = Y2"""
        c1 = s([f1, i1], 'eqtr4d', '( %s -> ( 1st ` %s ) = %s )' % (pc, EG1, IF1))
        cl = Closure(w, pc, cl_leaves)
        ge = [cl.ge0(k) for k in cl_leaves]
        z2 = concl(w, pc, i2).split(' = ', 1)[1] if concl(w, pc, i2).startswith(IF2 + ' = ') else None
        z2 = concl(w, pc, i2)[len(IF2) + 3:]
        cl.leaf(IF2, 'NN0', s([i2, cl.mem(z2, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (pc, IF2)))
        cl.leaf('( 2nd ` %s )' % EG1, 'NN0', s([f2, cl.mem(Y2, 'NN0')], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, EG1)))
        le = linarith(w, pc, [i2, f2] + hyps + ge, '( %s + 1 ) <_ ( 2nd ` %s )' % (IF2, EG1), closure=cl, atoms=list(cl_leaves.keys()) + [IF2, '( 2nd ` %s )' % EG1])
        return s([c1, le], 'jca', '( %s -> %s )' % (pc, CON))

    # ---------------- none
    pn = '( %s /\\ %s = ( inr ` (/) ) )' % (ph, SL)
    Ln = lambda st: Lft(w, pn, ph, st)
    sn = s([], 'simpr', '( %s -> %s = ( inr ` (/) ) )' % (pn, SL))
    T1 = ZT(ZM('Z'), ZU('Z'), A1, '(/)')
    zeq = s([Ln(opv), s([sn], 'iftrued', '( %s -> %s = %s )' % (pn, STOPB('L', 'G', 'Z', 'F'), T1))], 'eqtrd', '( %s -> %s = %s )' % (pn, ZPG, T1))
    zp = tup_comps(w, pn, ZPG, zeq, ZM('Z'), ZU('Z'), A1, '(/)',
                   {'m': vex_(w, pn, ZM('Z')), 'u': vex_(w, pn, ZU('Z')), 'a': vex_(w, pn, A1), 'h': vex_(w, pn, '(/)')})
    E0 = EGO('L', 'G', 'V', ZM('Z'), ZU('Z'), A1)
    eg = ego_inst(pn, 'extractgocsn', '%s = ( inr ` (/) )' % SL, sn)
    Y0 = '( ( ( 2nd ` %s ) + %s ) + 1 )' % (E0, DPC)
    PAIR = '<. ( 1st ` %s ) , %s >.' % (E0, Y0)
    assert concl(w, pn, eg) == '%s = %s' % (EG1, PAIR), concl(w, pn, eg)
    f1, f2 = pr12(pn, eg, PAIR, '( 1st ` %s )' % E0, Y0)
    ev, ev2 = w.rewrite(EGV(ZPG), {ZM(ZPG): (ZM('Z'), zp['m']), ZU(ZPG): (ZU('Z'), zp['u']), ZA(ZPG): (A1, zp['a'])}, pn)
    assert ev2 == E0, ev2
    nh = s([s([zp['h']], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (pn, ZH(ZPG))),
            s([s([s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')], 'a1i', '( %s -> -. (/) = 1o )' % pn)], 'mtbird', '( %s -> -. %s = 1o )' % (pn, ZH(ZPG)))
    i1 = s([s([nh], 'iffalsed', '( %s -> %s = ( 1st ` %s ) )' % (pn, IF1, EGV(ZPG))), s([ev], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (pn, EGV(ZPG), E0))],
           'eqtrd', '( %s -> %s = ( 1st ` %s ) )' % (pn, IF1, E0))
    i2 = s([s([nh], 'iffalsed', '( %s -> %s = ( 2nd ` %s ) )' % (pn, IF2, EGV(ZPG))), s([ev], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pn, EGV(ZPG), E0))],
           'eqtrd', '( %s -> %s = ( 2nd ` %s ) )' % (pn, IF2, E0))
    e0n = egn(pn, 'V', ZM('Z'), ZU('Z'), A1, Ln(mz), Ln(uz), Ln(a1))
    cn_ = fin(pn, None, i1, i2, f1, f2, E0, None, Y0, {DPC: ('NN0', Ln(dpc)), '( 2nd ` %s )' % E0: ('NN0', e0n)}, [])
    # ---------------- some
    ps_ = '( %s /\\ %s =/= ( inr ` (/) ) )' % (ph, SL)
    Ls = lambda st: Lft(w, ps_, ph, st)
    ss_ = s([], 'simpr', '( %s -> %s =/= ( inr ` (/) ) )' % (ps_, SL))
    WV = '( 2nd ` %s )' % SL
    MM = '( %s x. %s )' % (ZM('Z'), PRL(WV))
    WU = '( %s ++ %s )' % (WV, ZU('Z'))
    HT = 'if ( G < %s , 1o , (/) )' % MM
    T2 = ZT(MM, WU, 'EmptyTbl', HT)
    ML = '( 1 mod L )'
    mln = s([closed(w, ps_, '1z', '1 e. ZZ'), Ls(ln), w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps_, ML))
    slt = s([Ls(a1), mln, w.inst('tblfv')], 'syl2anc', '( %s -> %s e. ( Word NN0 |_| 1o ) )' % (ps_, SL))
    wvw = s([slt, w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (ps_, WV))
    prn = s([s([wvw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ps_, WV)), w.inst('xp1st')], 'syl',
            '( %s -> %s e. NN0 )' % (ps_, PRL(WV)))
    PRC = '( 2nd ` ( ProdL ` %s ) )' % WV
    prc = s([s([wvw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ps_, WV)), w.inst('xp2nd')], 'syl',
            '( %s -> %s e. NN0 )' % (ps_, PRC))
    mmn = s([Ls(mz), prn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ps_, MM))
    wuw = s([wvw, Ls(uz), w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ps_, WU))
    zeq2 = s([Ls(opv), s([s([ss_], 'neneqd', '( %s -> -. %s = ( inr ` (/) ) )' % (ps_, SL))], 'iffalsed', '( %s -> %s = %s )' % (ps_, STOPB('L', 'G', 'Z', 'F'), T2))],
             'eqtrd', '( %s -> %s = %s )' % (ps_, ZPG, T2))
    hv = s([s([s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V')], 'ifex', '%s e. _V' % HT)], 'a1i', '( %s -> %s e. _V )' % (ps_, HT))
    zp2 = tup_comps(w, ps_, ZPG, zeq2, MM, WU, 'EmptyTbl', HT, {'m': vex_(w, ps_, MM), 'u': vex_(w, ps_, WU), 'a': vex_(w, ps_, 'EmptyTbl'), 'h': hv})
    eg2 = ego_inst(ps_, 'extractgocss', '%s =/= ( inr ` (/) )' % SL, ss_)
    E2 = EGO('L', 'G', 'V', MM, WU, 'EmptyTbl')
    HITP = '<. ( inl ` <. %s , %s >. ) , ( ( %s + %s ) + 1 ) >.' % (MM, WU, DPC, PRC)
    Y2 = '( ( ( ( 2nd ` %s ) + %s ) + %s ) + 1 )' % (E2, DPC, PRC)
    NOHP = '<. ( 1st ` %s ) , %s >.' % (E2, Y2)
    RHS2 = 'if ( G < %s , %s , %s )' % (MM, HITP, NOHP)
    assert concl(w, ps_, eg2) == '%s = %s' % (EG1, RHS2), concl(w, ps_, eg2)
    e2n = egn(ps_, 'V', MM, WU, 'EmptyTbl', mmn, wuw, closed(w, ps_, 'emptytblcl', 'EmptyTbl e. Tbl'))
    outs2 = []
    for hit in (True, False):
        cnd = ('G < %s' % MM) if hit else ('-. G < %s' % MM)
        pc = '( %s /\\ %s )' % (ps_, cnd)
        Lc = lambda st: Lft(w, pc, ps_, st)
        hc = s([], 'simpr', '( %s -> %s )' % (pc, cnd))
        if hit:
            egc = s([Lc(eg2), s([hc], 'iftrued', '( %s -> %s = %s )' % (pc, RHS2, HITP))], 'eqtrd', '( %s -> %s = %s )' % (pc, EG1, HITP))
            X = '( inl ` <. %s , %s >. )' % (MM, WU)
            Yh = '( ( %s + %s ) + 1 )' % (DPC, PRC)
            f1, f2 = pr12(pc, egc, HITP, X, Yh)
            h1 = s([Lc(zp2['h']), s([hc], 'iftrued', '( %s -> %s = 1o )' % (pc, HT))], 'eqtrd', '( %s -> %s = 1o )' % (pc, ZH(ZPG)))
            r1, x1 = w.rewrite('( inl ` <. %s , %s >. )' % (ZM(ZPG), ZU(ZPG)), {ZM(ZPG): (MM, Lc(zp2['m'])), ZU(ZPG): (WU, Lc(zp2['u']))}, pc)
            i1 = s([s([h1], 'iftrued', '( %s -> %s = ( inl ` <. %s , %s >. ) )' % (pc, IF1, ZM(ZPG), ZU(ZPG))), r1], 'eqtrd', '( %s -> %s = %s )' % (pc, IF1, X))
            i2 = s([h1], 'iftrued', '( %s -> %s = 0 )' % (pc, IF2))
            outs2.append(fin(pc, None, i1, i2, f1, f2, E2, X, Yh, {DPC: ('NN0', Lc(Ls(dpc))), PRC: ('NN0', Lc(prc))}, []))
        else:
            egc = s([Lc(eg2), s([hc], 'iffalsed', '( %s -> %s = %s )' % (pc, RHS2, NOHP))], 'eqtrd', '( %s -> %s = %s )' % (pc, EG1, NOHP))
            f1, f2 = pr12(pc, egc, NOHP, '( 1st ` %s )' % E2, Y2)
            h0 = s([Lc(zp2['h']), s([hc], 'iffalsed', '( %s -> %s = (/) )' % (pc, HT))], 'eqtrd', '( %s -> %s = (/) )' % (pc, ZH(ZPG)))
            nh = s([s([h0], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (pc, ZH(ZPG))),
                    s([s([s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')], 'a1i', '( %s -> -. (/) = 1o )' % pc)], 'mtbird', '( %s -> -. %s = 1o )' % (pc, ZH(ZPG)))
            ev, evn = w.rewrite(EGV(ZPG), {ZM(ZPG): (MM, Lc(zp2['m'])), ZU(ZPG): (WU, Lc(zp2['u'])), ZA(ZPG): ('EmptyTbl', Lc(zp2['a']))}, pc)
            assert evn == E2, evn
            i1 = s([s([nh], 'iffalsed', '( %s -> %s = ( 1st ` %s ) )' % (pc, IF1, EGV(ZPG))), s([ev], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (pc, EGV(ZPG), E2))],
                   'eqtrd', '( %s -> %s = ( 1st ` %s ) )' % (pc, IF1, E2))
            i2 = s([s([nh], 'iffalsed', '( %s -> %s = ( 2nd ` %s ) )' % (pc, IF2, EGV(ZPG))), s([ev], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pc, EGV(ZPG), E2))],
                   'eqtrd', '( %s -> %s = ( 2nd ` %s ) )' % (pc, IF2, E2))
            outs2.append(fin(pc, None, i1, i2, f1, f2, E2, None, Y2, {DPC: ('NN0', Lc(Ls(dpc))), PRC: ('NN0', Lc(prc)),
                                                                      '( 2nd ` %s )' % E2: ('NN0', Lc(e2n))}, []))
    cs_ = s(outs2, 'pm2.61dan', '( %s -> %s )' % (ps_, CON))
    w.qed([s([cn_], 'ex', '( %s -> ( %s = ( inr ` (/) ) -> %s ) )' % (ph, SL, CON)), s([cs_], 'ex', '( %s -> ( %s =/= ( inr ` (/) ) -> %s ) )' % (ph, SL, CON))],
          'pm2.61dne', ST_G1)
    return w.run()



Si = lambda t: '( %s ` %s )' % (SQW, t)
NW = '( # ` W )'
DRP = lambda t: '( W substr <. %s , %s >. )' % (t, NW)
GI = lambda t: EGO('L', 'G', DRP(t), ZM(Si(t)), ZU(Si(t)), ZA(Si(t)))
ST_GS = ('( ( %s /\\ J e. ( 0 ..^ %s ) ) -> ( ( 1st ` %s ) = if ( %s = 1o , ( inl ` <. %s , %s >. ) , ( 1st ` %s ) ) /\\ '
         '( if ( %s = 1o , 0 , ( 2nd ` %s ) ) + 1 ) <_ ( 2nd ` %s ) ) )'
         % (PH_S, NW, GI('J'), ZH(Si('( J + 1 )')), ZM(Si('( J + 1 )')), ZU(Si('( J + 1 )')), GI('( J + 1 )'),
            ZH(Si('( J + 1 )')), GI('( J + 1 )'), GI('J')))


def exgostep():
    lab = 'exgostep'
    ph = '( %s /\\ J e. ( 0 ..^ %s ) )' % (PH_S, NW)
    w = W(lab, 'One pool element of the extraction loop against ` extractGo ` along the state sequence (~ exgo1 at the state '
               '` i ` , ~ tm2ldrop , ~ exstp1 ).')
    s = w.s
    c = Ctx(w, ph, ((('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)), 'J e. ( 0 ..^ %s )' % NW))
    ln, gn, ww, zs, mo = c['L e. NN'], c['G e. NN0'], c['W e. Word NN0'], c['Z e. %s' % STY], c['J e. ( 0 ..^ %s )' % NW]
    ps0 = s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), s([ww, zs], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph, STY))],
            'jca', '( %s -> %s )' % (ph, PH_S))
    mz = s([mo, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... %s ) )' % (ph, NW))
    mn = s([mo, w.inst('elfzonn0')], 'syl', '( %s -> J e. NN0 )' % ph)
    sm = s([s([ps0, mz], 'jca', '( %s -> ( %s /\\ J e. ( 0 ... %s ) ) )' % (ph, PH_S, NW)), w.inst('exstcl')], 'syl', '( %s -> %s e. %s )' % (ph, Si('J'), STY))
    pm = s([ww, mo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` J ) e. NN0 )' % ph)
    V1 = DRP('( J + 1 )')
    v1 = s([ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, V1))
    g1in = s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph), s([sm, pm, v1], '3jca', '( %s -> ( %s e. %s /\\ ( W ` J ) e. NN0 /\\ %s e. Word NN0 ) )'
              % (ph, Si('J'), STY, V1))], 'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ ( %s e. %s /\\ ( W ` J ) e. NN0 /\\ %s e. Word NN0 ) ) )'
             % (ph, Si('J'), STY, V1))
    mp = {'Z': Si('J'), 'F': '( W ` J )', 'V': V1}
    G1 = tsub_text(ST_G1.split(' -> ', 1)[1][:-2], mp)
    g1 = s([g1in, w.inst('exgo1')], 'syl', '( %s -> %s )' % (ph, G1))
    # rewrite: <" ( W ` J ) "> ++ V1 = drop m ; ( Si m OP W ` m ) = Si ( m + 1 )
    dr = s([ww, mo, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( <" ( W ` J ) "> ++ %s ) )' % (ph, DRP('J'), V1))
    sp = s([s([ps0, mn], 'jca', '( %s -> ( %s /\\ J e. NN0 ) )' % (ph, PH_S)), w.inst('exstp1')], 'syl',
           '( %s -> %s = ( %s ( L ExStOp G ) ( W ` J ) ) )' % (ph, Si('( J + 1 )'), Si('J')))
    ZPm = '( %s ( L ExStOp G ) ( W ` J ) )' % Si('J')
    r, new = w.wcongr(G1, {}, ph, {}, rules={'( <" ( W ` J ) "> ++ %s )' % V1: (DRP('J'), s([dr], 'eqcomd', '( %s -> ( <" ( W ` J ) "> ++ %s ) = %s )' % (ph, V1, DRP('J')))),
                                             ZPm: (Si('( J + 1 )'), s([sp], 'eqcomd', '( %s -> %s = %s )' % (ph, ZPm, Si('( J + 1 )'))))})
    CON = ST_GS.split(' -> ', 1)[1][:-2]
    assert new == CON, (new, CON)
    w.qed([g1, r], 'mpbid', ST_GS)
    return w.run()



T_R = ((('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)), '%s = (/)' % ZH('Z'))
PH_R = cj(T_R)
RR_ = RW_
FIN = Si(RR_)
HR = ZH(FIN)
RP = 'if ( %s = 1o , ( %s - 1 ) , %s )' % (HR, RR_, RR_)
G0 = GI('0')
CC_ = lambda t: '( ( 1st ` %s ) = ( 1st ` %s ) /\\ ( %s + ( 2nd ` %s ) ) <_ ( 2nd ` %s ) )' % (G0, GI(t), t, GI(t), G0)
ST_RI = '( ( %s /\\ I e. NN0 ) -> ( I <_ %s -> %s ) )' % (PH_R, RP, CC_('I'))
ST_RES = ('( %s -> ( ( 1st ` %s ) = if ( %s = 1o , ( inl ` <. %s , %s >. ) , ( inr ` (/) ) ) /\\ %s <_ ( 2nd ` %s ) ) )'
          % (PH_R, G0, HR, ZM(FIN), ZU(FIN), RR_, G0))


def gnn(w, pc, ps0, t, tz):
    """( pc -> ( 2nd ` GI( t ) ) e. NN0 ) from tz : t e. ( 0 ... # W )"""
    s = w.s
    st = s([s([ps0, tz], 'jca', '( %s -> ( %s /\\ %s e. ( 0 ... %s ) ) )' % (pc, PH_S, t, NW)), w.inst('exstcl')], 'syl', '( %s -> %s e. %s )' % (pc, Si(t), STY))
    T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
    mz = s([st, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (pc, ZM(Si(t))))
    z2 = s([st, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. %s )' % (pc, Si(t), T23))
    uz = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, ZU(Si(t))))
    z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` %s ) ) e. ( Tbl X. 2o ) )' % (pc, Si(t)))
    az = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (pc, ZA(Si(t))))
    return st, mz, uz, az


def exresi():
    lab = 'exresi'
    ph0 = PH_R
    w = W(lab, 'The extraction loop against ` extractGo ` up to the step before the stop index: every non-hitting step keeps '
               '` ( 1st ` extractGo ) ` and costs at least one unit (~ exgostep , ~ exitp ).')
    s = w.s
    c = Ctx(w, ph0, T_R)
    ln, gn, ww, zs = c['L e. NN'], c['G e. NN0'], c['W e. Word NN0'], c['Z e. %s' % STY]
    ps0 = s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph0), s([ww, zs], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph0, STY))],
            'jca', '( %s -> %s )' % (ph0, PH_S))
    ep = s([ps0, w.inst('exitp')], 'syl', '( %s -> %s )' % (ph0, ST_IP.split(' -> ', 1)[1][:-2]))
    parts3 = ST_IP.split(' -> ', 1)[1][:-2]
    IPT = parse_conj(parts3)
    rfz = s([ep], 'simp1d', '( %s -> %s )' % (ph0, IPT[0]))
    ral = s([ep], 'simp3d', '( %s -> %s )' % (ph0, IPT[2]))
    rn = s([rfz, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph0, RR_))
    PS = lambda t: '( %s <_ %s -> %s )' % (t, RP, CC_(t))
    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    # base
    z0 = closed(w, ph0, '0nn0', '0 e. NN0')
    lw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph0, NW))
    z0z = s([lw, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph0, NW))
    _, m0, u0, a0 = gnn(w, ph0, ps0, '0', z0z)
    e0 = s([s([s([s([s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph0), s([ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph0, DRP('0')))],
                         'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) )' % (ph0, DRP('0'))), m0], 'jca',
                      '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) )' % (ph0, DRP('0'), ZM(Si('0')))), u0], 'jca',
                   '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (ph0, DRP('0'), ZM(Si('0')), ZU(Si('0')))),
                 a0], 'jca', '( %s -> ( ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )'
                 % (ph0, DRP('0'), ZM(Si('0')), ZU(Si('0')), ZA(Si('0')))), w.inst('extractgocl')], 'syl',
           '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph0, G0))
    g0n = s([e0, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (ph0, G0))
    cl0 = Closure(w, ph0, {'( 2nd ` %s )' % G0: ('NN0', g0n)})
    b0 = s([s([], 'eqidd', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph0, G0, G0)),
            linarith(w, ph0, [], '( 0 + ( 2nd ` %s ) ) <_ ( 2nd ` %s )' % (G0, G0), closure=cl0)], 'jca', '( %s -> %s )' % (ph0, CC_('0')))
    base = s([b0], 'a1d', '( %s -> %s )' % (ph0, PS('0')))
    # step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph0, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ %s )' % (a, RP)
    La = lambda st: s([s([s([st], 'adantr', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph0, concl(w, ph0, st)))], 'adantr', '( %s -> %s )' % (a, concl(w, ph0, st)))],
                      'adantr', '( %s -> %s )' % (a2, concl(w, ph0, st)))
    mn = s([s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ %s )' % (a2, RP))
    GOAL = '( m e. ( 0 ..^ %s ) /\\ -. %s = 1o )' % (NW, HI('( m + 1 )'))
    RAL_ = IPT[2]
    BODYI = lambda t: '( %s e. ( 0 ..^ %s ) /\\ -. %s = 1o )' % (t, NW, HI(t))
    def at(pc, t, tfz):
        e = s([], 'id', '( i = %s -> i = %s )' % (t, t))
        cg, new = w.wcongr(BODYI('i'), {'i': t}, 'i = %s' % t, {'i': e})
        assert new == BODYI(t), new
        return s([cg, Lft(w, pc, a2, La(ral)) if pc != a2 else La(ral), tfz], 'rspcdva', '( %s -> %s )' % (pc, BODYI(t)))
    def fzo(pc, t, tn, tlt, rpos):
        rnn = s([s([Lft(w, pc, a2, La(rn)) if pc != a2 else La(rn), rpos], 'jca', '( %s -> ( %s e. NN0 /\\ 0 < %s ) )' % (pc, RR_, RR_)), w.inst('elnnnn0b')],
                'sylibr', '( %s -> %s e. NN )' % (pc, RR_))
        return s([s([tn, rnn, tlt], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN /\\ %s < %s ) )' % (pc, t, RR_, t, RR_)), w.inst('elfzo0')], 'sylibr',
                 '( %s -> %s e. ( 0 ..^ %s ) )' % (pc, t, RR_))
    outs = []
    for hit in (True, False):
        cnd = ('%s = 1o' % HR) if hit else ('-. %s = 1o' % HR)
        pc = '( %s /\\ %s )' % (a2, cnd)
        Lc = lambda st: Lft(w, pc, a2, st)
        hc = s([], 'simpr', '( %s -> %s )' % (pc, cnd))
        cl = Closure(w, pc, {'m': ('NN0', Lc(mn)), RR_: ('NN0', Lc(La(rn)))})
        if hit:
            rpe = s([hc], 'iftrued', '( %s -> %s = ( %s - 1 ) )' % (pc, RP, RR_))
            le1 = s([Lc(m1l), rpe], 'breqtrd', '( %s -> ( m + 1 ) <_ ( %s - 1 ) )' % (pc, RR_))
            m1lt = linarith(w, pc, [le1], '( m + 1 ) < %s' % RR_, closure=cl)
            mlt = linarith(w, pc, [le1], 'm < %s' % RR_, closure=cl)
            rpos = linarith(w, pc, [le1, cl.ge0('m')], '0 < %s' % RR_, closure=cl)
            m1n = s([Lc(mn), w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % pc)
            b1 = at(pc, '( m + 1 )', fzo(pc, '( m + 1 )', m1n, m1lt, rpos))
            b0_ = at(pc, 'm', fzo(pc, 'm', Lc(mn), mlt, rpos))
            outs.append(s([s([b0_], 'simpld', '( %s -> m e. ( 0 ..^ %s ) )' % (pc, NW)), s([b1], 'simprd', '( %s -> -. %s = 1o )' % (pc, HI('( m + 1 )')))],
                          'jca', '( %s -> %s )' % (pc, GOAL)))
        else:
            rpe = s([hc], 'iffalsed', '( %s -> %s = %s )' % (pc, RP, RR_))
            le1 = s([Lc(m1l), rpe], 'breqtrd', '( %s -> ( m + 1 ) <_ %s )' % (pc, RR_))
            mlt = linarith(w, pc, [le1], 'm < %s' % RR_, closure=cl)
            rpos = linarith(w, pc, [le1, cl.ge0('m')], '0 < %s' % RR_, closure=cl)
            b0_ = at(pc, 'm', fzo(pc, 'm', Lc(mn), mlt, rpos))
            sub = []
            for lt in (True, False):
                c2 = ('( m + 1 ) < %s' % RR_) if lt else ('-. ( m + 1 ) < %s' % RR_)
                pd = '( %s /\\ %s )' % (pc, c2)
                Ld = lambda st: Lft(w, pd, pc, st)
                h2c = s([], 'simpr', '( %s -> %s )' % (pd, c2))
                if lt:
                    cld = Closure(w, pd, {'m': ('NN0', Ld(Lc(mn))), RR_: ('NN0', Ld(Lc(La(rn))))})
                    m1n = s([Ld(Lc(mn)), w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % pd)
                    rpos2 = Ld(rpos)
                    fz1 = s([s([m1n, s([s([Ld(Lc(La(rn))), rpos2], 'jca', '( %s -> ( %s e. NN0 /\\ 0 < %s ) )' % (pd, RR_, RR_)), w.inst('elnnnn0b')], 'sylibr',
                                        '( %s -> %s e. NN )' % (pd, RR_)), h2c], '3jca', '( %s -> ( ( m + 1 ) e. NN0 /\\ %s e. NN /\\ ( m + 1 ) < %s ) )' % (pd, RR_, RR_)),
                                w.inst('elfzo0')], 'sylibr', '( %s -> ( m + 1 ) e. ( 0 ..^ %s ) )' % (pd, RR_))
                    e = s([], 'id', '( i = ( m + 1 ) -> i = ( m + 1 ) )')
                    cg, new = w.wcongr(BODYI('i'), {'i': '( m + 1 )'}, 'i = ( m + 1 )', {'i': e})
                    b1 = s([cg, Ld(Lc(La(ral))), fz1], 'rspcdva', '( %s -> %s )' % (pd, BODYI('( m + 1 )')))
                    sub.append(s([b1], 'simprd', '( %s -> -. %s = 1o )' % (pd, HI('( m + 1 )'))))
                else:
                    cld = Closure(w, pd, {'m': ('NN0', Ld(Lc(mn))), RR_: ('NN0', Ld(Lc(La(rn))))})
                    ge_ = s([s([cld.mem(RR_, 'RR'), cld.mem('( m + 1 )', 'RR')], 'lenltd', '( %s -> ( %s <_ ( m + 1 ) <-> -. ( m + 1 ) < %s ) )' % (pd, RR_, RR_)), h2c],
                            'mpbird', '( %s -> %s <_ ( m + 1 ) )' % (pd, RR_))
                    eq_ = s([s([cld.mem('( m + 1 )', 'RR'), cld.mem(RR_, 'RR')], 'letri3d', '( %s -> ( ( m + 1 ) = %s <-> ( ( m + 1 ) <_ %s /\\ %s <_ ( m + 1 ) ) ) )'
                               % (pd, RR_, RR_, RR_)), s([Ld(le1), ge_], 'jca', '( %s -> ( ( m + 1 ) <_ %s /\\ %s <_ ( m + 1 ) ) )' % (pd, RR_, RR_))],
                            'mpbird', '( %s -> ( m + 1 ) = %s )' % (pd, RR_))
                    r_, new = w.rewrite(HI('( m + 1 )'), {'( m + 1 )': (RR_, eq_)}, pd)
                    assert new == HR, new
                    sub.append(s([s([r_], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (pd, HI('( m + 1 )'), HR)), Ld(hc)], 'mtbird',
                                 '( %s -> -. %s = 1o )' % (pd, HI('( m + 1 )'))))
            nh = s(sub, 'pm2.61dan', '( %s -> -. %s = 1o )' % (pc, HI('( m + 1 )')))
            outs.append(s([s([b0_], 'simpld', '( %s -> m e. ( 0 ..^ %s ) )' % (pc, NW)), nh], 'jca', '( %s -> %s )' % (pc, GOAL)))
    gl = s(outs, 'pm2.61dan', '( %s -> %s )' % (a2, GOAL))
    mw = s([gl], 'simpld', '( %s -> m e. ( 0 ..^ %s ) )' % (a2, NW))
    nh = s([gl], 'simprd', '( %s -> -. %s = 1o )' % (a2, HI('( m + 1 )')))
    GSM = tsub_text(ST_GS.split(' -> ', 1)[1][:-2], {'J': 'm'})
    gs = s([s([La(ps0), mw], 'jca', '( %s -> ( %s /\\ m e. ( 0 ..^ %s ) ) )' % (a2, PH_S, NW)), w.inst('exgostep')], 'syl',
           '( %s -> %s )' % (a2, GSM))
    GS = parse_conj(GSM)
    g1 = s([gs], 'simpld', '( %s -> %s )' % (a2, GS[0]))
    g2 = s([gs], 'simprd', '( %s -> %s )' % (a2, GS[1]))
    i1 = s([nh], 'iffalsed', '( %s -> if ( %s = 1o , ( inl ` <. %s , %s >. ) , ( 1st ` %s ) ) = ( 1st ` %s ) )'
           % (a2, HI('( m + 1 )'), ZM(Si('( m + 1 )')), ZU(Si('( m + 1 )')), GI('( m + 1 )'), GI('( m + 1 )')))
    e1 = s([g1, i1], 'eqtrd', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (a2, GI('m'), GI('( m + 1 )')))
    i2 = s([nh], 'iffalsed', '( %s -> if ( %s = 1o , 0 , ( 2nd ` %s ) ) = ( 2nd ` %s ) )' % (a2, HI('( m + 1 )'), GI('( m + 1 )'), GI('( m + 1 )')))
    # IH at m
    rpre = s([s([s([La(rn)], 'nn0red', '( %s -> %s e. RR )' % (a2, RR_)), closed(w, a2, '1re', '1 e. RR')], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (a2, RR_)),
              s([La(rn)], 'nn0red', '( %s -> %s e. RR )' % (a2, RR_))], 'ifcld', '( %s -> %s e. RR )' % (a2, RP))
    cla = Closure(w, a2, {'m': ('NN0', mn)})
    cla.leaf(RP, 'RR', rpre)
    mle = linarith(w, a2, [m1l], 'm <_ %s' % RP, closure=cla)
    ih = s([mle, ih0], 'mpd', '( %s -> %s )' % (a2, CC_('m')))
    ih1 = s([ih], 'simpld', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (a2, G0, GI('m')))
    ih2 = s([ih], 'simprd', '( %s -> ( m + ( 2nd ` %s ) ) <_ ( 2nd ` %s ) )' % (a2, GI('m'), G0))
    c1 = s([ih1, e1], 'eqtrd', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (a2, G0, GI('( m + 1 )')))
    # the costs
    m1z = s([mw, w.inst('fzofzp1')], 'syl', '( %s -> ( m + 1 ) e. ( 0 ... %s ) )' % (a2, NW))
    mz = s([mw, w.inst('elfzofz')], 'syl', '( %s -> m e. ( 0 ... %s ) )' % (a2, NW))
    def gn2(t, tz):
        st, mm_, uu, aa = gnn(w, a2, La(ps0), t, tz)
        E = GI(t)
        dw = s([La(ww), w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (a2, DRP(t)))
        tt = s([s([s([s([s([La(ln), La(gn)], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % a2), dw], 'jca',
                        '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) )' % (a2, DRP(t))), mm_], 'jca',
                     '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) )' % (a2, DRP(t), ZM(Si(t)))), uu], 'jca',
                  '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (a2, DRP(t), ZM(Si(t)), ZU(Si(t)))),
                aa], 'jca', '( %s -> ( ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )'
                % (a2, DRP(t), ZM(Si(t)), ZU(Si(t)), ZA(Si(t))))
        ec = s([tt, w.inst('extractgocl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (a2, E))
        return s([ec, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (a2, E))
    cla.leaf('( 2nd ` %s )' % GI('m'), 'NN0', gn2('m', mz))
    cla.leaf('( 2nd ` %s )' % GI('( m + 1 )'), 'NN0', gn2('( m + 1 )', m1z))
    cla.leaf('( 2nd ` %s )' % G0, 'NN0', La(g0n))
    IF2 = 'if ( %s = 1o , 0 , ( 2nd ` %s ) )' % (HI('( m + 1 )'), GI('( m + 1 )'))
    cla.leaf(IF2, 'NN0', s([i2, cla.mem('( 2nd ` %s )' % GI('( m + 1 )'), 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (a2, IF2)))
    c2 = linarith(w, a2, [i2, g2, ih2], '( ( m + 1 ) + ( 2nd ` %s ) ) <_ ( 2nd ` %s )' % (GI('( m + 1 )'), G0), closure=cla,
                  atoms=['( 2nd ` %s )' % GI('m'), '( 2nd ` %s )' % GI('( m + 1 )'), '( 2nd ` %s )' % G0, IF2])
    q1 = s([c1, c2], 'jca', '( %s -> %s )' % (a2, CC_('( m + 1 )')))
    st = s([q1], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', ST_RI)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()



def exres():
    lab = 'exres'
    ph0 = PH_R
    w = W(lab, 'The extraction loop against Lean\'s ` extractGo ` (` extractGo_some ` , ` extractGo_none ` and the iteration count): '
               'from a state that has not hit, ` ( 1st ` extractGo ) ` is ` inl <. m , used >. ` of the state at the stop index when that '
               'step hit and ` inr (/) ` otherwise, and the stop index is at most the cost (~ exresi , ~ exgostep , ~ exitp ).')
    s = w.s
    c = Ctx(w, ph0, T_R)
    ln, gn, ww, zs = c['L e. NN'], c['G e. NN0'], c['W e. Word NN0'], c['Z e. %s' % STY]
    ps0 = s([s([ln, gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph0), s([ww, zs], 'jca', '( %s -> ( W e. Word NN0 /\\ Z e. %s ) )' % (ph0, STY))],
            'jca', '( %s -> %s )' % (ph0, PH_S))
    IPT = parse_conj(ST_IP.split(' -> ', 1)[1][:-2])
    ep = s([ps0, w.inst('exitp')], 'syl', '( %s -> %s )' % (ph0, cj(IPT)))
    rfz = s([ep], 'simp1d', '( %s -> %s )' % (ph0, IPT[0]))
    rco = s([ep], 'simp2d', '( %s -> %s )' % (ph0, IPT[1]))
    ral = s([ep], 'simp3d', '( %s -> %s )' % (ph0, IPT[2]))
    rn = s([rfz, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph0, RR_))
    CON = ST_RES.split(' -> ', 1)[1][:-2]
    INL = '( inl ` <. %s , %s >. )' % (ZM(FIN), ZU(FIN))
    IFR = 'if ( %s = 1o , %s , ( inr ` (/) ) )' % (HR, INL)
    g0n = None
    outs = []
    for hit in (True, False):
        cnd = ('%s = 1o' % HR) if hit else ('-. %s = 1o' % HR)
        pc = '( %s /\\ %s )' % (ph0, cnd)
        Lc = lambda st: Lft(w, pc, ph0, st)
        hc = s([], 'simpr', '( %s -> %s )' % (pc, cnd))
        if not hit:
            rpe = s([hc], 'iffalsed', '( %s -> %s = %s )' % (pc, RP, RR_))
            rle = s([s([s([Lc(rn)], 'nn0red', '( %s -> %s e. RR )' % (pc, RR_))], 'leidd', '( %s -> %s <_ %s )' % (pc, RR_, RR_)), rpe], 'breqtrrd',
                    '( %s -> %s <_ %s )' % (pc, RR_, RP))
            ri = s([s([s([], 'simpl', '( %s -> %s )' % (pc, ph0)), Lc(rn)], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (pc, ph0, RR_)), w.inst('exresi')], 'syl',
                   '( %s -> ( %s <_ %s -> %s ) )' % (pc, RR_, RP, CC_(RR_)))
            cc_ = s([rle, ri], 'mpd', '( %s -> %s )' % (pc, CC_(RR_)))
            rw = s([hc, Lc(rco), w.inst('orel2')], 'sylc', '( %s -> %s = %s )' % (pc, RR_, NW))
            d0 = s([s([rw], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (pc, RR_, NW, NW, NW))], 'oveq2d',
                   '( %s -> %s = ( W substr <. %s , %s >. ) )' % (pc, DRP(RR_), NW, NW))
            d1 = s([d0, closed(w, pc, 'swrd00', '( W substr <. %s , %s >. ) = (/)' % (NW, NW))], 'eqtrd', '( %s -> %s = (/) )' % (pc, DRP(RR_)))
            st, mz, uz, az = gnn(w, pc, Lc(ps0), RR_, Lc(rfz))
            EGR0 = EGO('L', 'G', '(/)', ZM(FIN), ZU(FIN), ZA(FIN))
            g0 = s([s([s([s([s([Lc(ln), Lc(gn)], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % pc), mz], 'jca',
                           '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. NN0 ) )' % (pc, ZM(FIN))), uz], 'jca',
                        '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, ZM(FIN), ZU(FIN))), az], 'jca',
                      '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )' % (pc, ZM(FIN), ZU(FIN), ZA(FIN))),
                    w.inst('extractgo0')], 'syl', '( %s -> %s = <. ( inr ` (/) ) , 0 >. )' % (pc, EGR0))
            r1, x1 = w.rewrite(GI(RR_), {DRP(RR_): ('(/)', d1)}, pc)
            assert x1 == EGR0, x1
            gv = s([r1, g0], 'eqtrd', '( %s -> %s = <. ( inr ` (/) ) , 0 >. )' % (pc, GI(RR_)))
            inr_v = s([s([], 'fvex', '( inr ` (/) ) e. _V')], 'a1i', '( %s -> ( inr ` (/) ) e. _V )' % pc)
            zv = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % pc)
            f1 = s([s([gv], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. ( inr ` (/) ) , 0 >. ) )' % (pc, GI(RR_))),
                    s([inr_v, zv, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. ( inr ` (/) ) , 0 >. ) = ( inr ` (/) ) )' % pc)], 'eqtrd',
                   '( %s -> ( 1st ` %s ) = ( inr ` (/) ) )' % (pc, GI(RR_)))
            f2 = s([s([gv], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. ( inr ` (/) ) , 0 >. ) )' % (pc, GI(RR_))),
                    s([inr_v, zv, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. ( inr ` (/) ) , 0 >. ) = 0 )' % pc)], 'eqtrd',
                   '( %s -> ( 2nd ` %s ) = 0 )' % (pc, GI(RR_)))
            c1 = s([s([s([cc_], 'simpld', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (pc, G0, GI(RR_))), f1], 'eqtrd',
                      '( %s -> ( 1st ` %s ) = ( inr ` (/) ) )' % (pc, G0)), s([hc], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (pc, IFR))], 'eqtr4d',
                   '( %s -> ( 1st ` %s ) = %s )' % (pc, G0, IFR))
            c2i = s([cc_], 'simprd', '( %s -> ( %s + ( 2nd ` %s ) ) <_ ( 2nd ` %s ) )' % (pc, RR_, GI(RR_), G0))
            cl = Closure(w, pc, {RR_: ('NN0', Lc(rn))})
            cl.leaf('( 2nd ` %s )' % GI(RR_), 'NN0', s([f2, closed(w, pc, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, GI(RR_))))
            z0z = s([s([Lc(ww), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pc, NW)), w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (pc, NW))
            _, m0, u0, a0 = gnn(w, pc, Lc(ps0), '0', z0z)
            e0 = s([s([s([s([s([s([Lc(ln), Lc(gn)], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % pc), s([Lc(ww), w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, DRP('0')))],
                                 'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, DRP('0'))), m0], 'jca',
                              '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) )' % (pc, DRP('0'), ZM(Si('0')))), u0], 'jca',
                           '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, DRP('0'), ZM(Si('0')), ZU(Si('0')))),
                         a0], 'jca', '( %s -> ( ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )'
                         % (pc, DRP('0'), ZM(Si('0')), ZU(Si('0')), ZA(Si('0')))), w.inst('extractgocl')], 'syl',
                   '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (pc, G0))
            cl.leaf('( 2nd ` %s )' % G0, 'NN0', s([e0, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, G0)))
            c2 = linarith(w, pc, [c2i, f2], '%s <_ ( 2nd ` %s )' % (RR_, G0), closure=cl)
            outs.append(s([c1, c2], 'jca', '( %s -> %s )' % (pc, CON)))
        else:
            # R =/= 0
            p0 = '( %s /\\ %s = 0 )' % (pc, RR_)
            L0 = lambda st: Lft(w, p0, pc, st)
            r0 = s([], 'simpr', '( %s -> %s = 0 )' % (p0, RR_))
            h0 = s([s([s([s([s([r0], 'fveq2d', '( %s -> %s = ( %s ` 0 ) )' % (p0, FIN, SQW))], 'id', '') if False else
                         s([r0], 'fveq2d', '( %s -> %s = ( %s ` 0 ) )' % (p0, FIN, SQW)), L0(Lc(s([ps0, w.inst('exst0')], 'syl', '( %s -> ( %s ` 0 ) = Z )' % (ph0, SQW))))],
                        'eqtrd', '( %s -> %s = Z )' % (p0, FIN))], 'id', '') if False else None], 'id', '') if False else None
            fz = s([s([r0], 'fveq2d', '( %s -> %s = ( %s ` 0 ) )' % (p0, FIN, SQW)), L0(Lc(s([ps0, w.inst('exst0')], 'syl', '( %s -> ( %s ` 0 ) = Z )' % (ph0, SQW))))],
                   'eqtrd', '( %s -> %s = Z )' % (p0, FIN))
            r_, x_ = w.rewrite(HR, {FIN: ('Z', fz)}, p0)
            assert x_ == ZH('Z'), x_
            hz = s([r_, L0(Lc(c['%s = (/)' % ZH('Z')]))], 'eqtrd', '( %s -> %s = (/) )' % (p0, HR))
            n1 = s([s([s([hz], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (p0, HR)),
                       s([s([s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')], 'a1i', '( %s -> -. (/) = 1o )' % p0)], 'mtbird', '( %s -> -. %s = 1o )' % (p0, HR)),
                    L0(hc)], 'pm2.65da' if False else 'id', '') if False else None
            nh0 = s([s([hz], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (p0, HR)),
                     s([s([s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')], 'a1i', '( %s -> -. (/) = 1o )' % p0)], 'mtbird', '( %s -> -. %s = 1o )' % (p0, HR))
            rn0 = s([L0(hc), nh0], 'pm2.65da', '( %s -> -. %s = 0 )' % (pc, RR_))
            rnn = s([s([Lc(rn), s([rn0], 'neqned', '( %s -> %s =/= 0 )' % (pc, RR_))], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (pc, RR_, RR_)),
                     w.inst('elnnne0')], 'sylibr', '( %s -> %s e. NN )' % (pc, RR_))
            R1 = '( %s - 1 )' % RR_
            r1n = s([rnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (pc, R1))
            rpe = s([hc], 'iftrued', '( %s -> %s = %s )' % (pc, RP, R1))
            rle = s([s([s([r1n], 'nn0red', '( %s -> %s e. RR )' % (pc, R1))], 'leidd', '( %s -> %s <_ %s )' % (pc, R1, R1)), rpe], 'breqtrrd',
                    '( %s -> %s <_ %s )' % (pc, R1, RP))
            ri = s([s([s([], 'simpl', '( %s -> %s )' % (pc, ph0)), r1n], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (pc, ph0, R1)), w.inst('exresi')], 'syl',
                   '( %s -> ( %s <_ %s -> %s ) )' % (pc, R1, RP, CC_(R1)))
            cc_ = s([rle, ri], 'mpd', '( %s -> %s )' % (pc, CC_(R1)))
            rlt = s([s([rnn], 'nnred', '( %s -> %s e. RR )' % (pc, RR_))], 'ltm1d', '( %s -> %s < %s )' % (pc, R1, RR_))
            mfz = s([s([r1n, rnn, rlt], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN /\\ %s < %s ) )' % (pc, R1, RR_, R1, RR_)), w.inst('elfzo0')], 'sylibr',
                    '( %s -> %s e. ( 0 ..^ %s ) )' % (pc, R1, RR_))
            BODYI = lambda t: '( %s e. ( 0 ..^ %s ) /\\ -. %s = 1o )' % (t, NW, HI(t))
            e_ = s([], 'id', '( i = %s -> i = %s )' % (R1, R1))
            cg, new = w.wcongr(BODYI('i'), {'i': R1}, 'i = %s' % R1, {'i': e_})
            b1 = s([cg, Lc(ral), mfz], 'rspcdva', '( %s -> %s )' % (pc, BODYI(R1)))
            mw = s([b1], 'simpld', '( %s -> %s e. ( 0 ..^ %s ) )' % (pc, R1, NW))
            GSm = tsub_text(ST_GS.split(' -> ', 1)[1][:-2], {'J': R1})
            gs = s([s([Lc(ps0), mw], 'jca', '( %s -> ( %s /\\ %s e. ( 0 ..^ %s ) ) )' % (pc, PH_S, R1, NW)), w.inst('exgostep')], 'syl',
                   '( %s -> %s )' % (pc, GSm))
            np_ = s([s([rnn], 'nncnd', '( %s -> %s e. CC )' % (pc, RR_)), closed(w, pc, 'ax-1cn', '1 e. CC')], 'npcand', '( %s -> ( %s + 1 ) = %s )' % (pc, R1, RR_))
            r2, GS2 = w.wcongr(GSm, {}, pc, {}, rules={'( %s + 1 )' % R1: (RR_, np_)})
            gs2 = s([gs, r2], 'mpbid', '( %s -> %s )' % (pc, GS2))
            GP = parse_conj(GS2)
            g1 = s([gs2], 'simpld', '( %s -> %s )' % (pc, GP[0]))
            g2 = s([gs2], 'simprd', '( %s -> %s )' % (pc, GP[1]))
            i1 = s([hc], 'iftrued', '( %s -> if ( %s = 1o , %s , ( 1st ` %s ) ) = %s )' % (pc, HR, INL, GI(RR_), INL))
            f1 = s([g1, i1], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (pc, GI(R1), INL))
            i2 = s([hc], 'iftrued', '( %s -> if ( %s = 1o , 0 , ( 2nd ` %s ) ) = 0 )' % (pc, HR, GI(RR_)))
            c1 = s([s([s([cc_], 'simpld', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (pc, G0, GI(R1))), f1], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (pc, G0, INL)),
                    s([hc], 'iftrued', '( %s -> %s = %s )' % (pc, IFR, INL))], 'eqtr4d', '( %s -> ( 1st ` %s ) = %s )' % (pc, G0, IFR))
            c2i = s([cc_], 'simprd', '( %s -> ( %s + ( 2nd ` %s ) ) <_ ( 2nd ` %s ) )' % (pc, R1, GI(R1), G0))
            cl = Closure(w, pc, {RR_: ('NN0', Lc(rn))})
            r1z = s([mw, w.inst('elfzofz')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (pc, R1, NW))
            _, mm1, uu1, aa1 = gnn(w, pc, Lc(ps0), R1, r1z)
            et = s([s([s([s([s([s([Lc(ln), Lc(gn)], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % pc), s([Lc(ww), w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, DRP(R1)))],
                                 'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, DRP(R1))), mm1], 'jca',
                              '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) )' % (pc, DRP(R1), ZM(Si(R1)))), uu1], 'jca',
                           '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, DRP(R1), ZM(Si(R1)), ZU(Si(R1)))),
                         aa1], 'jca', '( %s -> ( ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )'
                         % (pc, DRP(R1), ZM(Si(R1)), ZU(Si(R1)), ZA(Si(R1)))), w.inst('extractgocl')], 'syl',
                   '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (pc, GI(R1)))
            cl.leaf('( 2nd ` %s )' % GI(R1), 'NN0', s([et, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, GI(R1))))
            z0z = s([s([Lc(ww), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pc, NW)), w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (pc, NW))
            _, m0, u0, a0 = gnn(w, pc, Lc(ps0), '0', z0z)
            e0 = s([s([s([s([s([s([Lc(ln), Lc(gn)], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % pc), s([Lc(ww), w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, DRP('0')))],
                                 'jca', '( %s -> ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, DRP('0'))), m0], 'jca',
                              '( %s -> ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) )' % (pc, DRP('0'), ZM(Si('0')))), u0], 'jca',
                           '( %s -> ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) )' % (pc, DRP('0'), ZM(Si('0')), ZU(Si('0')))),
                         a0], 'jca', '( %s -> ( ( ( ( ( L e. NN /\\ G e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. NN0 ) /\\ %s e. Word NN0 ) /\\ %s e. Tbl ) )'
                         % (pc, DRP('0'), ZM(Si('0')), ZU(Si('0')), ZA(Si('0')))), w.inst('extractgocl')], 'syl',
                   '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (pc, G0))
            cl.leaf('( 2nd ` %s )' % G0, 'NN0', s([e0, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, G0)))
            IF2 = 'if ( %s = 1o , 0 , ( 2nd ` %s ) )' % (HR, GI(RR_))
            cl.leaf(IF2, 'NN0', s([i2, closed(w, pc, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (pc, IF2)))
            c2 = linarith(w, pc, [c2i, g2, i2], '%s <_ ( 2nd ` %s )' % (RR_, G0), closure=cl,
                          atoms=['( 2nd ` %s )' % GI(R1), '( 2nd ` %s )' % G0, IF2, RR_])
            outs.append(s([c1, c2], 'jca', '( %s -> %s )' % (pc, CON)))
    w.qed(outs, 'pm2.61dan', ST_RES)
    return w.run()


STMTS = {'exgo1': ST_G1, 'exgostep': ST_GS, 'exresi': ST_RI, 'exres': ST_RES}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
