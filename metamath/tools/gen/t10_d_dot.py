"""T10: divOutTest at the machine (Lean ` divOutTest_le_B ` ) at ` xd xr xf s t u = 4 6 7 1 2 3 ` .

  tmidota   the prefix ` dup xr s t ; dup xd t s ; divmodC s t u xd xf xr ; isZero s t ; dropNum s ` :
            the quotient on ` u ` , flag ` r mod d = 0 ` , in ` 5 B b `
  tmidotb   divOutTest_le_B: the prefix, then ` ite flag ( isZero xf s ; load' ( flag := !flag ) ) skip ` by cases

    MM_DB=sorties/t10.mm python3 tools/gen/t10_d_dot.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7_h_iz import lset_val, lset_ty
from cl import Closure
import num

SEL = sys.argv[1:]
LM = FRAGS['dot'].lmap()


class DotB(Base):
    """the facts of a divOutTest theorem: d = G on 4, r = F on 6, fuel = H on 7"""
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        gnn, fn, hn = c0['G e. NN'], c0['F e. NN0'], c0['H e. NN0']
        gn = w.s([gnn], 'nnnn0d', '( %s -> G e. NN0 )' % ph)
        xw, x2w, yw = c0[WG('X')], c0[WG("X'")], c0[WG('Y')]
        eqs = {'4': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xw)), '6': (EWg('F', "X'"), ewg_(w, ph, 'F', fn, "X'", x2w)),
               '7': (EWg('H', 'Y'), ewg_(w, ph, 'H', hn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, 'dot', eqs)
        self.gnn, self.gn, self.fn, self.hn, self.bn = gnn, gn, fn, hn, self.c['B e. NN0']
        s = w.s
        self.fmn = s([s([fn], 'nn0zd', '( %s -> F e. ZZ )' % ph), gnn, w.inst('zmodcl')], 'syl2anc',
                     '( %s -> %s e. NN0 )' % (ph, FM_))
        self.fqn = s([fn, gnn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FQ_))
        self.cl = Closure(w, ph, {'F': ('NN0', fn), 'G': ('NN', gnn), 'H': ('NN0', hn), 'B': ('NN0', self.bn)})
        self.tbn = s([s([self.bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d',
                     '( %s -> ( TMB ` B ) e. NN0 )' % ph)
        self.cl.leaf('( TMB ` B )', 'NN0', self.tbn)


def modle(w, ph, B):
    """( ph -> ( F mod G ) <_ F )"""
    s = w.s
    cl = B.cl
    fr = s([B.fn], 'nn0red', '( %s -> F e. RR )' % ph)
    mv = s([fr, s([B.gnn], 'nnrpd', '( %s -> G e. RR+ )' % ph), w.inst('modvalr')], 'syl2anc',
           '( %s -> %s = ( F - ( %s x. G ) ) )' % (ph, FM_, FQ_))
    cl.leaf(FQ_, 'NN0', B.fqn)
    return nlinarith(w, ph, [mv, cl.ge0(FQ_), cl.ge0('G')], '%s <_ F' % FM_, closure=cl, atoms=[FQ_, FM_])


def tmidota():
    lab = 'tmidota'
    T = numtree(TREE_DOT)
    ph = cj(T)
    w = W(lab, 'The prefix of Lean\'s ` divOutTest ` at the machine ( ` xd xr xf s t u = 4 6 7 1 2 3 ` ): ` dup xr s t ; '
               'dup xd t s ; divmodC s t u xd xf xr ; isZero s t ; dropNum s ` pushes ` r / d ` on ` u ` , sets the flag to '
               '` r mod d = 0 ` and restores every other stack, within ` 5 B b ` steps.')
    s = w.s
    B = DotB(w, ph, T)
    R = B.run()
    DV = DK
    g = lambda k: R.S.vals[k][2]
    # 1. dup 6 1 2
    B.call(R, 'tmidupb', {'K': '6', 'J': '1', 'I': '2', 'F': 'F', 'N': 'B', 'X': "X'", 'P': PL('P', 3), 'E': LM['Y2']},
           {}, [('1', EWg('F', DV(1)), B.g(EWg('F', DV(1)), ewg_(w, ph, 'F', B.fn, DV(1), g('1'))))])
    # 2. dup 4 2 1
    B.call(R, 'tmidupb', {'K': '4', 'J': '2', 'I': '1', 'F': 'G', 'N': 'B', 'X': 'X', 'P': PL('P', 4), 'E': LM['Y3']},
           {'G e. NN0': B.gn}, [('2', EWg('G', DV(2)), B.g(EWg('G', DV(2)), ewg_(w, ph, 'G', B.gn, DV(2), B.gam[DV(2)])))])
    # 3. divmodC 1 2 3 4 7 6
    EM, EQ = EWg(FM_, DV(1)), EWg(FQ_, DV(3))
    B.call(R, 'tmidivmodcb', {'K': '1', 'J': '2', 'I': '3', "I'": '4', 'I"': '7', 'I0': '6', 'F': 'F', 'G': 'G', 'N': 'B',
                              'X': DV(1), 'Y': DV(2), 'P': PL('P', 5), 'E': LM['Y4']},
           {}, [('1', EM, B.g(EM, ewg_(w, ph, FM_, B.fmn, DV(1), B.gam[DV(1)]))),
                ('3', EQ, B.g(EQ, ewg_(w, ph, FQ_, B.fqn, DV(3), B.gam[DV(3)]))), ('2', DV(2), B.gam[DV(2)])])
    # 4. isZero 1 2
    p2 = '( 2 ^ B )'
    ml = modle(w, ph, B)
    B.cl.leaf(FM_, 'NN0', B.fmn)
    mlt = s([B.cl.mem(FM_, 'RR'), B.cl.mem('F', 'RR'), B.cl.mem(p2, 'RR'), ml, B.c['F < ( 2 ^ B )']], 'lelttrd',
            '( %s -> %s < %s )' % (ph, FM_, p2))
    xm = {'%s e. NN0' % FM_: B.fmn, '%s < %s' % (FM_, p2): mlt}
    B.call(R, 'tmiizbs', {'K': '1', 'I': '2', 'F': FM_, 'N': 'B', 'X': DV(1), 'P': PL('P', 6), 'E': LM['Y5']}, xm, [])
    # 5. dropNum 1 at the class
    cur, out = R.normalize(['0', '2', '3', '4', '5', '6', '7', '1'])
    assert out == [('3', EQ), ('1', EM)], out
    S3 = R.at([('3', EQ)])
    B.call(R, 'tmidropnb', {'K': '1', 'F': FM_, 'N': 'B', 'X': DV(1), 'O': IFM_, 'P': PL('P', 7), 'E': LM['Z1']}, xm,
           [('1', DV(1), B.gam[DV(1)])], on=(S3, [('3', EQ)]))
    cur, out = R.normalize(N8)
    assert out == [('3', EQ)], out
    assert cur == CLN(LM['Z1'], NFL(IFM_), D3Q), cur
    TB = '( TMB ` B )'
    B5 = '( 5 x. %s )' % TB
    le = linarith(w, ph, [B.cl.ge0(TB)], '%s <_ %s' % (R.n, B5), closure=B.cl)
    st = hrle(w, ph, B.mk['phm'], R.tri, R.C0, R.cur, R.n, B5, B.cl.mem(B5, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def cls_to(w, pc, t, V1, V2, eq):
    """rewrite the post class NFL( V1 ) of the triple t (C, D, n) to NFL( V2 ) by eq : ( pc -> V1 = V2 )"""
    tri, C, D, n = t
    lab = D.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
    Dst = triple_D(D)
    ceq = clnneq(w, pc, lab, nfl_eq(w, pc, V1, V2, eq), NFL(V1), NFL(V2), Dst)
    return hrrw(w, pc, tri, C, D, n, deq=ceq)


def load_nfl(w, pc, mk, lam, kw, Vin, Vout, fleq):
    """( pc -> A. r e. NFL( Vin ) ( lam ` r ) e. NFL( Vout ) ) ; kw(t) the set fields, fleq(pr, f) : given
    f : ( pr -> ( TMfl ` r ) = Vin ) , a step ( pr -> FL( r ) = Vout ) for FL( r ) = kw( r )['fl']"""
    s = w.s
    pr = '( %s /\\ r e. %s )' % (pc, NFL(Vin))
    rr, f = A8.nfl_unpack(w, pr, Vin, 'r', s([], 'simpr', '( %s -> r e. %s )' % (pr, NFL(Vin))))
    nv = lset_val(w, pr, kw, 'r', rr)
    NR = '( %s ` r )' % lam
    fl = s([nv['fields']['fl'], fleq(pr, f)], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pr, NR, Vout))
    inm = A8.nfl_pack(w, pr, Vout, NR, nv['mem'], fl)
    return s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (pc, NFL(Vin), lam, NFL(Vout)))


def notfl(Vin, Vout):
    """fleq for ` flag := !flag ` : ` if ( Vin = 1o , (/) , 1o ) = Vout ` """
    def f(pr, fst, w=None):
        pass
    return f


def skip_ty(w, ph, mk):
    s = w.s
    f1_ = s([], 'f1oi', '( _I |` TMSt ) : TMSt -1-1-onto-> TMSt')
    ff = s([s([f1_, w.inst('f1of')], 'ax-mp', '( _I |` TMSt ) : TMSt --> TMSt')], 'a1i', '( %s -> ( _I |` TMSt ) : TMSt --> TMSt )' % ph)
    sv = s([s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    em = s([s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), w.inst('elmapg')], 'syl2anc',
           '( %s -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )' % ph)
    li = s([em, ff], 'mpbird', '( %s -> ( _I |` TMSt ) e. ( TMSt ^m TMSt ) )' % ph)
    sq = s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    mq = s([sq, sq], 'oveq12d', '( %s -> ( TMSt ^m TMSt ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    return s([li, mq], 'eleqtrd', '( %s -> %s )' % (ph, LTY(LID)))


def skip_in(w, ph, NV):
    """( ph -> A. r e. NV ( ( _I |` TMSt ) ` r ) e. NV ) for NV = { h e. TMSt | ... }"""
    s = w.s
    pr = '( %s /\\ r e. %s )' % (ph, NV)
    rin = s([], 'simpr', '( %s -> r e. %s )' % (pr, NV))
    rt = s([rin, w.inst('elrabi')], 'syl', '( %s -> r e. TMSt )' % pr)
    fv = s([rt, w.inst('fvresi')], 'syl', '( %s -> ( ( _I |` TMSt ) ` r ) = r )' % pr)
    return s([s([fv, rin], 'eqeltrd', '( %s -> ( ( _I |` TMSt ) ` r ) e. %s )' % (pr, NV))], 'ralrimiva',
             '( %s -> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (ph, NV, NV))


def lit_if(w, pc, cond_step, truth, a, b, cond):
    """( pc -> if ( cond , a , b ) = a ) or ( ... = b )"""
    return w.s([cond_step], 'iftrued' if truth else 'iffalsed',
               '( %s -> if ( %s , %s , %s ) = %s )' % (pc, cond, a, b, a if truth else b))


def tmidotb():
    lab = 'tmidotb'
    T0 = numtree(TREE_DOT)
    ph = cj(T0)
    w = W(lab, 'Lean\'s ` divOutTest_le_B ` at the machine ( ` xd xr xf s t u = 4 6 7 1 2 3 ` ): the prefix (~ tmidota ), '
               'then ` ite flag ( isZero xf s ; load\' ( flag := !flag ) ) skip ` : the flag ends up '
               '` r mod d = 0 /\\ fuel =/= 0 ` , the quotient ` r / d ` on ` u ` , every other stack restored, within '
               '` 6 B b + 2 ` steps (by cases on the two tests).')
    s = w.s
    pre0 = s([], 'tmidota', STMTS10['tmidota'])
    pre = s([s([], 't10stk', ST_NUMS), pre0], 'mpan2', '( %s -> %s )' % (cj(TREE_DOT), CONCL_DOTA)) if False else None
    # the prefix under ph (with the numeral facts): from the frozen form by adantr
    pre = s([pre0], 'adantr', '( %s -> %s )' % (ph, CONCL_DOTA))
    Q1, Q2, Q3 = PL('P', 0), PL('P', 1), PL('P', 2)
    FZ = '%s = 0' % FM_
    outs_outer = []
    for mz in (True, False):
        c1 = FZ if mz else '-. %s' % FZ
        inner = []
        for hz in ((True, False) if mz else (None,)):
            conds = [c1] + ([] if hz is None else ['H = 0' if hz else '-. H = 0'])
            T = T0
            for cc in conds:
                T = (T, cc)
            pc = cj(T)
            B = DotB(w, pc, T)
            c, mk = B.c, B.mk
            L = lambda st: lift(w, pc, ph, st, conds)
            cst = c[c1]
            tp = L(pre)
            C0_, D0_, n0_ = triple_parts(concl(w, pc, tp))
            V0 = '1o' if mz else '(/)'
            e0 = lit_if(w, pc, cst, mz, '1o', '(/)', FZ)
            tri = cls_to(w, pc, (tp, C0_, D0_, n0_), IFM_, V0, e0)
            t0, C0_, D0_, n0_ = tri
            S3 = B.S0.upd('3', EWg(FQ_, DK(3)), ewg_(w, pc, FQ_, B.fqn, DK(3), B.gam[DK(3)]))
            R = B.run(S3)
            N0 = NFL(V0)
            ex = {SSS(N0): B.ss(N0)}
            if mz:
                ex[STMT(GT(Q3))] = gotocl(w, pc, mk['tv'], Q3, B.ex[LAB(Q3)])
                ex['A. m e. %s ( TMfl ` m ) = 1o' % N0] = A8.ht_nfl(w, pc, '1o')
                B.call(R, 'tm2lbrt', {'A': Q1, 'C': 'TMfl', 'E': LM['Y6'], 'Q': GT(Q3), 'N': N0}, ex, [])
                # isZero 7 1 at N0
                ex2 = {'( %s ` 7 ) = %s' % (R.S.D, EWg('H', 'Y')): R.S.vals['7'][1]}
                V1 = '1o' if hz else '(/)'
                hc = c['H = 0' if hz else '-. H = 0']
                e1 = lit_if(w, pc, hc, hz, '1o', '(/)', 'H = 0')
                B.call(R, 'tmiizbs', {'K': '7', 'I': '1', 'F': 'H', 'N': 'B', 'X': 'Y', 'P': PL('P', 8), 'E': Q2}, ex2, [],
                       pre=(N0, B.ss(N0)), cls_rw=(nfl_eq(w, pc, 'if ( H = 0 , 1o , (/) )', V1, e1), NFL(V1)))
                # load ( flag := !flag )
                V2 = '(/)' if hz else '1o'
                kw = lambda t: dict(fl='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t)

                def fleq(pr, f, V1=V1, V2=V2):
                    x = s([f], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (pr, V1))
                    i1 = s([x], 'ifbid', '( %s -> if ( ( TMfl ` r ) = 1o , (/) , 1o ) = if ( %s = 1o , (/) , 1o ) )' % (pr, V1))
                    if V1 == '1o':
                        i2 = s([s([], 'eqid', '1o = 1o')], 'iftruei', 'if ( 1o = 1o , (/) , 1o ) = (/)')
                    else:
                        i2 = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), w.inst('neneqd') if False else
                                s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
                        i2 = s([i2], 'iffalsei', 'if ( (/) = 1o , (/) , 1o ) = 1o')
                    return s([i1, s([i2], 'a1i', '( %s -> if ( %s = 1o , (/) , 1o ) = %s )' % (pr, V1, V2))], 'eqtrd',
                             '( %s -> if ( ( TMfl ` r ) = 1o , (/) , 1o ) = %s )' % (pr, V2))
                ex3 = {LTY(L_NOTF): lset_ty(w, pc, mk, L_NOTF, kw), SSS(NFL(V1)): B.ss(NFL(V1)), SSS(NFL(V2)): B.ss(NFL(V2)),
                       'A. r e. %s ( %s ` r ) e. %s' % (NFL(V1), L_NOTF, NFL(V2)): load_nfl(w, pc, mk, L_NOTF, kw, V1, V2, fleq)}
                B.call(R, 'tm2flg', {'A': Q2, 'E': 'E', 'F': L_NOTF, 'N': NFL(V1), "N'": NFL(V2)}, ex3, [])
                VF = V2
                # FINV = VF
                cj2 = '( %s /\\ H =/= 0 )' % FZ
                if hz:
                    nh = s([s([hc], 'nne', '( %s -> -. H =/= 0 )' % pc) if False else
                            s([hc, s([], 'nne', '( -. H =/= 0 <-> H = 0 )')], 'sylibr', '( %s -> -. H =/= 0 )' % pc)],
                           'intnand', '( %s -> -. %s )' % (pc, cj2))
                    ef = s([nh], 'iffalsed', '( %s -> %s = (/) )' % (pc, FINV_DOT))
                else:
                    hn0 = s([hc], 'neqned', '( %s -> H =/= 0 )' % pc)
                    ef = s([s([cst, hn0], 'jca', '( %s -> %s )' % (pc, cj2))], 'iftrued', '( %s -> %s = 1o )' % (pc, FINV_DOT))
                nb = '( ( 1 + ( TMB ` B ) ) + 1 )'
            else:
                ex[STMT(GT(LM['Y6']))] = gotocl(w, pc, mk['tv'], LM['Y6'], B.ex[LAB(LM['Y6'])])
                ex['A. m e. %s -. ( TMfl ` m ) = 1o' % N0] = A8.ht_nfl(w, pc, '(/)')
                B.call(R, 'tm2fbrg', {'A': Q1, 'C': 'TMfl', 'E': Q3, 'Q': GT(LM['Y6']), 'N': N0}, ex, [])
                B.call(R, 'tm2flg', {'A': Q3, 'E': 'E', 'F': LID, 'N': N0, "N'": N0},
                       {LTY(LID): skip_ty(w, pc, mk), SSS(N0): B.ss(N0), 'A. r e. %s ( %s ` r ) e. %s' % (N0, LID, N0): skip_in(w, pc, N0)}, [])
                VF = '(/)'
                ef = s([s([cst], 'intnanrd', '( %s -> -. ( %s /\\ H =/= 0 ) )' % (pc, FZ))], 'iffalsed',
                       '( %s -> %s = (/) )' % (pc, FINV_DOT))
                nb = '( 1 + 1 )'
            # the case run from the prefix
            t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
            assert C1 == D0_, (C1, D0_)
            t2 = hrseq(w, pc, mk['phm'], t0, t1, C0_, D0_, D1, n0_, n1)
            n2 = '( %s + %s )' % (n0_, n1)
            t2, C2, D2, n2 = cls_to(w, pc, (t2, C0_, D1, n2), VF, FINV_DOT, s([ef], 'eqcomd', '( %s -> %s = %s )' % (pc, VF, FINV_DOT)))
            BND = '( ( 6 x. ( TMB ` B ) ) + 2 )'
            TB = '( TMB ` B )'
            le = linarith(w, pc, [B.cl.ge0(TB)], '%s <_ %s' % (n2, BND), closure=B.cl)
            inner.append(hrle(w, pc, mk['phm'], t2, C2, D2, n2, BND, B.cl.mem(BND, 'NN0'), le))
        if mz:
            outs_outer.append(s(inner, 'pm2.61dan', '( ( %s /\\ %s ) -> %s )' % (ph, c1, CONCL_DOTB)))
        else:
            outs_outer.append(inner[0])
    st = s(outs_outer, 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_DOTB))
    finish(w, st, lab)
    return w.run()


def lift(w, pc, ph, st, conds):
    """from st : ( ph -> X ) to ( pc -> X ), pc = ph with the case conditions conjoined in turn"""
    cur = ph
    for cc in conds:
        nxt = '( %s /\\ %s )' % (cur, cc)
        st = w.s([st], 'adantr', '( %s -> %s )' % (nxt, concl(w, cur, st)))
        cur = nxt
    return st


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
