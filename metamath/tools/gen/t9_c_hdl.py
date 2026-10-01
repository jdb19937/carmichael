"""T9: the pop handler ` readEmpty ` (TM/Prims.lean) of ` clear ` .

  tmcrdempf   the handler is a function on states and popped symbols
  tmcrdempv   its value
  tmcrdempi   the interface of T4's ~ tm2fclr at the test ` !da ` : a popped letter gives ` !da = true ` ,
              an empty stack ` !da = false `

    MM_DB=sorties/t9.mm python3 tools/gen/t9_c_hdl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from t7lib import lamval, ifex_closed, not1o, _transport

SEL = sys.argv[1:]
ST_EF = '%s e. %s' % (RDE, HDLC)
ST_EV = '( ( V e. TMSt /\\ O e. %s ) -> ( %s ` <. V , O >. ) = %s )' % (OPT, RDE, EVAL('V', 'O'))
XDA = lambda t: 'if ( ( TMda ` %s ) = 1o , (/) , 1o )' % t
EI_TY = ('%s e. %s' % (RDE, HDLS), '%s e. ( 2o ^m %s )' % (CNDA, S))
EI_Z = "A. r e. %s A. z e. Gamma' ( %s ` ( %s ` <. r , ( inl ` z ) >. ) ) = 1o" % (S, CNDA, RDE)
EI_N = 'A. r e. %s -. ( %s ` ( %s ` <. r , ( inr ` (/) ) >. ) ) = 1o' % (S, CNDA, RDE)
EI_TREE = (EI_TY, EI_Z, EI_N)
ST_EI = '( %s -> %s )' % (SEQ, cj(EI_TREE))


def tmcrdempf():
    lab = 'tmcrdempf'
    w = W(lab, 'The handler ` readEmpty ` is a function on the states and the popped symbols (Lean: its type '
               '` St -> Option Gamma\' -> St ` ).')
    ph = '( v e. TMSt /\\ o e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> v e. TMSt )' % ph)
    cl = st_comps(w, ph, 'v', vv)
    ifc = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFE)
    comps = [FLD(f, 'v') for f in ORDER[:3]] + [IFE] + [FLD(f, 'v') for f in ORDER[4:]]
    cls = [cl[f] for f in ORDER[:3]] + [w.s([ifc], 'a1i', '( %s -> %s e. 2o )' % (ph, IFE))] + [cl[f] for f in ORDER[4:]]
    mem, _ = tuple_facts(w, ph, comps, cls)
    B = EVAL('v', 'o')
    ral = w.s([mem], 'rgen2', 'A. v e. TMSt A. o e. %s %s e. TMSt' % (OPT, B))
    d = w.s([], 'df-tmrdemp', DF_RDE)
    fm = w.s([d], 'fmpo', '( A. v e. TMSt A. o e. %s %s e. TMSt <-> %s : ( TMSt X. %s ) --> TMSt )' % (OPT, B, RDE, OPT))
    ff = w.s([ral, fm], 'mpbi', '%s : ( TMSt X. %s ) --> TMSt' % (RDE, OPT))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ov = w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.s([], '1oex', '1o e. _V'), w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xv = w.s([sv, ov, w.inst('xpexg')], 'mp2an', '( TMSt X. %s ) e. _V' % OPT)
    em = w.s([sv, xv, w.inst('elmapg')], 'mp2an', '( %s e. %s <-> %s : ( TMSt X. %s ) --> TMSt )' % (RDE, HDLC, RDE, OPT))
    w.qed([ff, em], 'mpbir', ST_EF)
    return w.run()


def tmcrdempv():
    lab = 'tmcrdempv'
    w = W(lab, 'Value of ` readEmpty ` : ` da ` records whether the pop found the stack empty (Lean ` readEmpty ` , '
               '` da := o.isNone ` ).')
    ph = '( V e. TMSt /\\ O e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    oo = w.s([], 'simpr', '( %s -> O e. %s )' % (ph, OPT))
    B = EVAL('v', 'o'); BV = EVAL('V', 'O')
    ante = '( v = V /\\ o = O )'
    ev = w.s([], 'simpl', '( %s -> v = V )' % ante)
    eo = w.s([], 'simpr', '( %s -> o = O )' % ante)
    cg, nb = w.congr(B, {'v': 'V', 'o': 'O'}, ante, {'v': ev, 'o': eo})
    assert nb == BV, nb
    d = w.s([], 'df-tmrdemp', DF_RDE)
    bx = w.s([], 'opex', '%s e. _V' % BV)
    bxa = w.s([bx], 'a1i', '( %s -> %s e. _V )' % (ph, BV))
    j = w.s([vv, oo, bxa], '3jca', '( %s -> ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) )' % (ph, OPT, BV))
    ovi = w.s([cg, d], 'ovmpoga', '( ( V e. TMSt /\\ O e. %s /\\ %s e. _V ) -> ( V %s O ) = %s )' % (OPT, BV, RDE, BV))
    ov = w.s([j, ovi], 'syl', '( %s -> ( V %s O ) = %s )' % (ph, RDE, BV))
    dov = w.s([], 'df-ov', '( V %s O ) = ( %s ` <. V , O >. )' % (RDE, RDE))
    dova = w.s([dov], 'a1i', '( %s -> ( V %s O ) = ( %s ` <. V , O >. ) )' % (ph, RDE, RDE))
    w.qed([dova, ov], 'eqtr3d', ST_EV)
    return w.run()


def emp_at(w, a, r, rr, O, oo):
    """the value of readEmpty at ( r , O ): dict val/mem/fields"""
    N = '( %s ` <. %s , %s >. )' % (RDE, r, O)
    IFB = 'if ( %s = ( inr ` (/) ) , 1o , (/) )' % O
    comps = [FLD(f, r) for f in ORDER[:3]] + [IFB] + [FLD(f, r) for f in ORDER[4:]]
    val = w.s([rr, oo, w.inst('tmcrdempv')], 'syl2anc', '( %s -> %s = %s )' % (a, N, MK(*comps)))
    cl = st_comps(w, a, r, rr)
    ifc = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFB)
    cls = [cl[f] for f in ORDER[:3]] + [w.s([ifc], 'a1i', '( %s -> %s e. 2o )' % (a, IFB))] + [cl[f] for f in ORDER[4:]]
    mem, vals = tuple_facts(w, a, comps, cls)
    return _transport(w, a, N, val, mem, vals, comps)


def tmcrdempi():
    lab = 'tmcrdempi'
    ph = SEQ
    w = W(lab, 'The interface of ~ tm2fclr at the handler ` readEmpty ` and the test ` !da ` : both typed at the '
               'generic alphabet; after popping a letter ` !da ` holds, after popping from the empty stack it fails '
               '(Lean ` clear_loop ` ).')
    sq = w.s([], 'id', '( %s -> %s )' % (ph, SEQ))
    seqr = w.s([sq], 'eqcomd', '( %s -> TMSt = %s )' % (ph, S))
    x1 = w.s([seqr], 'xpeq1d', "( %s -> ( TMSt X. ( Gamma' |_| 1o ) ) = ( %s X. ( Gamma' |_| 1o ) ) )" % (ph, S))
    e3 = w.s([seqr, x1], 'oveq12d', '( %s -> %s = %s )' % (ph, HDLC, HDLS))
    f = w.s([], 'tmcrdempf', ST_EF)
    t1 = w.s([w.s([f], 'a1i', '( %s -> %s )' % (ph, ST_EF)), e3], 'eleqtrd', '( %s -> %s e. %s )' % (ph, RDE, HDLS))
    # the test's typing
    mkf = {'seq': sq}
    b01 = w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % XDA('u'))
    from t7_e_cmp import lamty
    t2 = lamty(w, ph, mkf, CNDA, XDA, '2o', w.s([], '2oex', '2o e. _V'), b01)
    ty = w.s([t1, t2], 'jca', '( %s -> %s )' % (ph, cj(EI_TY)))
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    # a letter
    a1 = '( ( %s /\\ r e. %s ) /\\ z e. Gamma\' )' % (ph, S)
    r1 = w.s([w.s([], 'simplr', '( %s -> r e. %s )' % (a1, S)), w.s([], 'simpll', '( %s -> %s )' % (a1, SEQ))], 'eleqtrd',
             '( %s -> r e. TMSt )' % a1)
    zz = w.s([], 'simpr', "( %s -> z e. Gamma' )" % a1)
    oz = w.s([zz, w.inst('djulcl')], 'syl', '( %s -> ( inl ` z ) e. %s )' % (a1, OPT))
    nv = emp_at(w, a1, 'r', r1, '( inl ` z )', oz)
    N = '( %s ` <. r , ( inl ` z ) >. )' % RDE
    ne = w.s([w.s([], 'vex', 'z e. _V'), w.inst('tmcinlne')], 'ax-mp', '-. ( inl ` z ) = ( inr ` (/) )')
    da0 = w.s([nv['fields']['da'], w.s([w.s([ne], 'a1i', '( %s -> -. ( inl ` z ) = ( inr ` (/) ) )' % a1)], 'iffalsed',
                                          '( %s -> if ( ( inl ` z ) = ( inr ` (/) ) , 1o , (/) ) = (/) )' % a1)],
              'eqtrd', '( %s -> ( TMda ` %s ) = (/) )' % (a1, N))
    xex = ifex_closed(w, a1, '( TMda ` %s ) = 1o' % N, '(/)', '1o', z0, o1)
    cv = lamval(w, a1, XDA, N, nv['mem'], xex)
    c1 = w.s([cv, w.s([not1o(w, a1, da0, 'TMda', N)], 'iffalsed', '( %s -> %s = 1o )' % (a1, XDA(N)))], 'eqtrd',
             '( %s -> ( %s ` %s ) = 1o )' % (a1, CNDA, N))
    rz = w.s([w.s([c1], 'ralrimiva', "( ( %s /\\ r e. %s ) -> A. z e. Gamma' ( %s ` %s ) = 1o )" % (ph, S, CNDA, N))],
             'ralrimiva', '( %s -> %s )' % (ph, EI_Z))
    # the empty stack
    a2 = '( %s /\\ r e. %s )' % (ph, S)
    r2 = w.s([w.s([], 'simpr', '( %s -> r e. %s )' % (a2, S)), w.s([], 'simpl', '( %s -> %s )' % (a2, SEQ))], 'eleqtrd',
             '( %s -> r e. TMSt )' % a2)
    z1 = w.s([], '0lt1o', '(/) e. 1o')
    on = w.s([z1, w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. %s' % OPT)
    nv2 = emp_at(w, a2, 'r', r2, '( inr ` (/) )', w.s([on], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (a2, OPT)))
    N2 = '( %s ` <. r , ( inr ` (/) ) >. )' % RDE
    eqi = w.s([], 'eqid', '( inr ` (/) ) = ( inr ` (/) )')
    da1 = w.s([nv2['fields']['da'], w.s([w.s([eqi], 'a1i', '( %s -> ( inr ` (/) ) = ( inr ` (/) ) )' % a2)], 'iftrued',
                                           '( %s -> if ( ( inr ` (/) ) = ( inr ` (/) ) , 1o , (/) ) = 1o )' % a2)],
              'eqtrd', '( %s -> ( TMda ` %s ) = 1o )' % (a2, N2))
    xex2 = ifex_closed(w, a2, '( TMda ` %s ) = 1o' % N2, '(/)', '1o', z0, o1)
    cv2 = lamval(w, a2, XDA, N2, nv2['mem'], xex2)
    c2 = w.s([cv2, w.s([da1], 'iftrued', '( %s -> %s = (/) )' % (a2, XDA(N2)))], 'eqtrd', '( %s -> ( %s ` %s ) = (/) )' % (a2, CNDA, N2))
    rn = w.s([not1o(w, a2, c2, CNDA, N2)], 'ralrimiva', '( %s -> %s )' % (ph, EI_N))
    w.qed([ty, rz, rn], '3jca', ST_EI)
    return w.run()


STMTS = {'tmcrdempf': ST_EF, 'tmcrdempv': ST_EV, 'tmcrdempi': ST_EI}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
