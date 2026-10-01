"""T7: isZero at the machine (blueprint section 8, delivered): the fold of
the zero test on the machine word, its two N-level lemmas, the inverse of
inclBool, and ~ tm2fiz instantiated with the pair summary <. flag , cmp >."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7lib import _transport
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

IFZ = lambda t: 'if ( ( ( TMfl ` %s ) = 1o /\\ -. ( bitOf ` ( TMra ` %s ) ) = 1o ) , 1o , (/) )' % (t, t)
IFT = lambda t: 'if ( ( toNat ` ( %s o. %s ) ) = 0 , 1o , (/) )' % (P2, t)
SPX = lambda t: '<. ( TMfl ` %s ) , ( TMcmp ` %s ) >.' % (t, t)
OZX = lambda t: '<. %s , Q >.' % IFT(t)
IBL = '( inclBool o. L )'


def tmcif1():
    w = W('tmcif1', 'A decided proposition as a bit: ` if ( ph , 1o , (/) ) = 1o ` exactly when ` ph ` .')
    a1 = w.s([], 'iftrue', '( ph -> if ( ph , 1o , (/) ) = 1o )')
    a2 = w.s([], 'iffalse', '( -. ph -> if ( ph , 1o , (/) ) = (/) )')
    a3 = w.s([a2], 'eqeq1d', '( -. ph -> ( if ( ph , 1o , (/) ) = 1o <-> (/) = 1o ) )')
    n0 = w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
    a4 = w.s([a3, n0], 'mtbiri', '( -. ph -> -. if ( ph , 1o , (/) ) = 1o )')
    a5 = w.s([a4], 'con4i', '( if ( ph , 1o , (/) ) = 1o -> ph )')
    w.qed([a5, a1], 'impbii', '( if ( ph , 1o , (/) ) = 1o <-> ph )')
    return w.run()


def tmctn0c():
    ph = '( B e. 2o /\\ L e. Word 2o )'
    w = W('tmctn0c', 'The value of a bit word is zero exactly when its first bit is zero and the rest is zero '
                     '(the step of the zero-scan fold, Lean ` zeroBits ` on a cons).')
    bb = w.s([], 'simpl', '( %s -> B e. 2o )' % ph); ll = w.s([], 'simpr', '( %s -> L e. Word 2o )' % ph)
    C = '( <" B "> ++ L )'
    t1 = w.s([bb, ll, w.inst('tonatcons')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( bToNat ` B ) + ( 2 x. ( toNat ` L ) ) ) )' % (ph, C))
    e1 = w.s([t1], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( ( bToNat ` B ) + ( 2 x. ( toNat ` L ) ) ) = 0 ) )' % (ph, C))
    bn = w.s([bb, w.inst('bwbncl')], 'syl', '( %s -> ( bToNat ` B ) e. NN0 )' % ph)
    bnr = w.s([bn], 'nn0red', '( %s -> ( bToNat ` B ) e. RR )' % ph)
    bn0 = w.s([bn], 'nn0ge0d', '( %s -> 0 <_ ( bToNat ` B ) )' % ph)
    tn = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` L ) e. NN0 )' % ph)
    two = closed(w, ph, '2nn0', '2 e. NN0')
    t2 = w.s([two, tn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 2 x. ( toNat ` L ) ) e. NN0 )' % ph)
    t2r = w.s([t2], 'nn0red', '( %s -> ( 2 x. ( toNat ` L ) ) e. RR )' % ph)
    t20 = w.s([t2], 'nn0ge0d', '( %s -> 0 <_ ( 2 x. ( toNat ` L ) ) )' % ph)
    j1 = w.s([bnr, bn0], 'jca', '( %s -> ( ( bToNat ` B ) e. RR /\\ 0 <_ ( bToNat ` B ) ) )' % ph)
    j2 = w.s([t2r, t20], 'jca', '( %s -> ( ( 2 x. ( toNat ` L ) ) e. RR /\\ 0 <_ ( 2 x. ( toNat ` L ) ) ) )' % ph)
    a20 = w.s([j1, j2, w.inst('add20')], 'syl2anc', '( %s -> ( ( ( bToNat ` B ) + ( 2 x. ( toNat ` L ) ) ) = 0 <-> ( ( bToNat ` B ) = 0 /\\ ( 2 x. ( toNat ` L ) ) = 0 ) ) )' % ph)
    twoc = closed(w, ph, '2cn', '2 e. CC')
    tnc = w.s([tn], 'nn0cnd', '( %s -> ( toNat ` L ) e. CC )' % ph)
    m0 = w.s([twoc, tnc, w.inst('mul0or')], 'syl2anc', '( %s -> ( ( 2 x. ( toNat ` L ) ) = 0 <-> ( 2 = 0 \\/ ( toNat ` L ) = 0 ) ) )' % ph)
    n2 = w.s([w.s([], '2ne0', '2 =/= 0')], 'neneqi' if False else 'necon2bi', None) if False else None
    n2 = w.s([w.s([], '2ne0', '2 =/= 0'), w.s([], 'df-ne', '( 2 =/= 0 <-> -. 2 = 0 )')], 'mpbi', '-. 2 = 0')
    bo = w.s([n2], 'biorfi', '( ( toNat ` L ) = 0 <-> ( 2 = 0 \\/ ( toNat ` L ) = 0 ) )')
    boa = w.s([bo], 'a1i', '( %s -> ( ( toNat ` L ) = 0 <-> ( 2 = 0 \\/ ( toNat ` L ) = 0 ) ) )' % ph)
    m1 = w.s([m0, boa], 'bitr4d', '( %s -> ( ( 2 x. ( toNat ` L ) ) = 0 <-> ( toNat ` L ) = 0 ) )' % ph)
    b0 = w.s([bb, w.inst('bwbneq0')], 'syl', '( %s -> ( ( bToNat ` B ) = 0 <-> B = (/) ) )' % ph)
    an = w.s([b0, m1], 'anbi12d', '( %s -> ( ( ( bToNat ` B ) = 0 /\\ ( 2 x. ( toNat ` L ) ) = 0 ) <-> ( B = (/) /\\ ( toNat ` L ) = 0 ) ) )' % ph)
    c1 = w.s([e1, a20], 'bitrd', '( %s -> ( ( toNat ` %s ) = 0 <-> ( ( bToNat ` B ) = 0 /\\ ( 2 x. ( toNat ` L ) ) = 0 ) ) )' % (ph, C))
    w.qed([c1, an], 'bitrd', '( %s -> ( ( toNat ` %s ) = 0 <-> ( B = (/) /\\ ( toNat ` L ) = 0 ) ) )' % (ph, C))
    return w.run()


def tmcibinv():
    ph = 'L e. Word 2o'
    U = '( %s o. %s )' % (P2, IBL)
    w = W('tmcibinv', 'The payloads of the machine word of a bit word are the bit word (` inclBool ` is inverted by '
                      'the second projection on the bit letters).')
    ll = w.s([], 'id', '( %s -> L e. Word 2o )' % ph)
    f2 = closed(w, ph, 'f2ndres', '%s : %s --> 2o' % (P2, BITS))
    ibl = w.s([ll, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IBL, BITS))
    uw = w.s([ibl, f2, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, U))
    lu = w.s([ibl, f2, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, U, IBL))
    li = w.s([ll, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` L ) )' % (ph, IBL))
    lul = w.s([lu, li], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` L ) )' % (ph, U))
    ph2 = '( %s /\\ i e. ( 0 ..^ ( # ` %s ) ) )' % (ph, U)
    A_ = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ ( # ` %s ) ) )' % (ph2, U))
    o1 = w.s([A_(lu, '( # ` %s ) = ( # ` %s )' % (U, IBL))], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ ( # ` %s ) ) )' % (ph2, U, IBL))
    fi = w.s([ii, o1], 'eleqtrd', '( %s -> i e. ( 0 ..^ ( # ` %s ) ) )' % (ph2, IBL))
    o2 = w.s([A_(lul, '( # ` %s ) = ( # ` L )' % U)], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ ( # ` L ) ) )' % (ph2, U))
    fi2 = w.s([ii, o2], 'eleqtrd', '( %s -> i e. ( 0 ..^ ( # ` L ) ) )' % ph2)
    ibla = A_(ibl, '%s e. Word %s' % (IBL, BITS)); lla = A_(ll, 'L e. Word 2o')
    iblf = w.s([ibla, w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> %s )' % (ph2, IBL, IBL, BITS))
    v1 = w.s([iblf, fi, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` i ) = ( %s ` ( %s ` i ) ) )' % (ph2, U, P2, IBL))
    s1 = w.s([ibla, fi, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( %s ` i ) e. %s )' % (ph2, IBL, BITS))
    v2 = w.s([s1, w.inst('fvres')], 'syl', '( %s -> ( %s ` ( %s ` i ) ) = ( 2nd ` ( %s ` i ) ) )' % (ph2, P2, IBL, IBL))
    lf = w.s([lla, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ ( # ` L ) ) --> 2o )' % ph2)
    v3 = w.s([lf, fi2, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` i ) = ( inclBool ` ( L ` i ) ) )' % (ph2, IBL))
    s2 = w.s([lla, fi2, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` i ) e. 2o )' % ph2)
    v4 = w.s([s2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` ( L ` i ) ) = <. 1 , ( L ` i ) >. )' % ph2)
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'elexi', '1 e. _V')
    onea = w.s([one], 'a1i', '( %s -> 1 e. _V )' % ph2)
    liv = w.s([s2], 'elexd', '( %s -> ( L ` i ) e. _V )' % ph2)
    v5 = w.s([onea, liv, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. 1 , ( L ` i ) >. ) = ( L ` i ) )' % ph2)
    v34 = w.s([v3, v4], 'eqtrd', '( %s -> ( %s ` i ) = <. 1 , ( L ` i ) >. )' % (ph2, IBL))
    v34b = w.s([v34], 'fveq2d', '( %s -> ( 2nd ` ( %s ` i ) ) = ( 2nd ` <. 1 , ( L ` i ) >. ) )' % (ph2, IBL))
    ch = w.s([w.s([w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` i ) = ( 2nd ` ( %s ` i ) ) )' % (ph2, U, IBL)), v34b], 'eqtrd',
                  '( %s -> ( %s ` i ) = ( 2nd ` <. 1 , ( L ` i ) >. ) )' % (ph2, U)), v5], 'eqtrd', '( %s -> ( %s ` i ) = ( L ` i ) )' % (ph2, U))
    ral = w.s([ch], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i ) = ( L ` i ) )' % (ph, U, U))
    eq = w.s([uw, ll, w.inst('eqwrd')], 'syl2anc', '( %s -> ( %s = L <-> ( ( # ` %s ) = ( # ` L ) /\\ A. i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i ) = ( L ` i ) ) ) )' % (ph, U, U, U, U))
    j = w.s([lul, ral], 'jca', '( %s -> ( ( # ` %s ) = ( # ` L ) /\\ A. i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i ) = ( L ` i ) ) )' % (ph, U, U, U))
    w.qed([eq, j], 'mpbird', '( %s -> %s = L )' % (ph, U))
    return w.run()


def lamvalw(w, ph, X_of, A, amem, xex):
    """( ph -> ( ( u e. Word BITS |-> X(u) ) ` A ) = X(A) )"""
    F = '( u e. %s |-> %s )' % (WB, X_of('u'))
    da = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, F, F))
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (A, A))
    cg, newX = w.congr(X_of('u'), {'u': A}, 'u = %s' % A, {'u': idu})
    assert newX == X_of(A), (newX, X_of(A))
    if ' u ' in ' %s ' % ph:
        return fvg(w, ph, F, WB, X_of, A, cg, amem, xex)
    cga = w.s([cg], 'adantl', '( ( %s /\\ u = %s ) -> %s = %s )' % (ph, A, X_of('u'), X_of(A)))
    return w.s([da, cga, amem, xex], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ph, F, A, X_of(A)))


def spair(w, ph, A, amem):
    """( ph -> ( SPAIR ` A ) = <. ( TMfl ` A ) , ( TMcmp ` A ) >. )"""
    return lamval(w, ph, SPX, A, amem, closed(w, ph, 'opex', '%s e. _V' % SPX(A)))


def spair_nv(w, ph, nv, N):
    """( ph -> ( SPAIR ` N ) = <. fl , cmp >. ) through the tuple of nv (N may carry the binder u)"""
    tup = MK(*nv['comps'])
    e1 = w.s([nv['val']], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, SPAIR, N, SPAIR, tup))
    e2 = spair(w, ph, tup, nv['tmem'])
    fl, cm = nv['comps'][6], nv['comps'][5]
    e3 = w.s([nv['tvals']['fl'], nv['tvals']['cmp']], 'opeq12d', '( %s -> %s = <. %s , %s >. )' % (ph, SPX(tup), fl, cm))
    return w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, SPAIR, N, SPX(tup))), e3], 'eqtrd',
               '( %s -> ( %s ` %s ) = <. %s , %s >. )' % (ph, SPAIR, N, fl, cm))


def ozval(w, ph, A, aw):
    """( ph -> ( OZ ` A ) = <. IFT( A ) , Q >. ) from aw : A e. Word BITS"""
    return lamvalw(w, ph, OZX, A, aw, closed(w, ph, 'opex', '%s e. _V' % OZX(A)))


def lset_val(w, ph, kw_of, A, nv_or_mem):
    """the load ` ( u e. TMSt |-> SETF( u , f := x(u) ) ) ` at A: value, membership, fields.
    kw_of(t) is the dict of set fields at t; nv_or_mem : ( ph -> A e. TMSt )"""
    X_of = lambda t: SETF(t, **kw_of(t))
    val = lamval(w, ph, X_of, A, nv_or_mem, closed(w, ph, 'opex', '%s e. _V' % X_of(A)))
    kw = kw_of(A)
    cl = st_comps(w, ph, A, nv_or_mem)
    comps = [kw.get(f, FLD(f, A)) for f in ORDER]
    cls = []
    for f, comp in zip(ORDER, comps):
        if f in kw:
            if comp == '1o':
                cls.append(closed(w, ph, '1oel2o', '1o e. 2o'))
            else:   # the zero-scan flag: an if of bits
                e = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % comp)
                cls.append(w.s([e], 'a1i', '( %s -> %s e. 2o )' % (ph, comp)))
        else:
            cls.append(cl[f])
    mem, vals = tuple_facts(w, ph, comps, cls)
    N = '( %s ` %s )' % ('( u e. TMSt |-> %s )' % X_of('u'), A)
    return _transport(w, ph, N, val, mem, vals, comps)


def lset_ty(w, ph, mk, lam, kw_of):
    """( ph -> lam e. ( S ^m S ) ) for a load lambda"""
    X_of = lambda t: SETF(t, **kw_of(t))
    assert lam == '( u e. TMSt |-> %s )' % X_of('u')
    phu = 'u e. TMSt'
    uu = w.s([], 'id', '( %s -> u e. TMSt )' % phu)
    cl = st_comps(w, phu, 'u', uu)
    kw = kw_of('u')
    comps = [kw.get(f, FLD(f, 'u')) for f in ORDER]
    cls = []
    for f, comp in zip(ORDER, comps):
        if f in kw:
            if comp == '1o':
                cls.append(closed(w, phu, '1oel2o', '1o e. 2o'))
            else:
                e = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % comp)
                cls.append(w.s([e], 'a1i', '( %s -> %s e. 2o )' % (phu, comp)))
        else:
            cls.append(cl[f])
    mem, _ = tuple_facts(w, phu, comps, cls)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    t = lamty(w, ph, mk, lam, X_of, 'TMSt', sv, mem)
    e = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    e2 = w.s([e], 'oveq1d', '( %s -> ( TMSt ^m ( 2nd ` T ) ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    return w.s([t, e2], 'eleqtrd', '( %s -> %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % (ph, lam))


def rab_in2(w, ph, binder, dom, cond_fn, A, amem, cond_step):
    """( ph -> A e. { binder e. dom | cond_fn( binder ) } )"""
    cls = '{ %s e. %s | %s }' % (binder, dom, cond_fn(binder))
    idh = w.s([], 'id', '( %s = %s -> %s = %s )' % (binder, A, binder, A))
    cg, new = w.wcongr(cond_fn(binder), {binder: A}, '%s = %s' % (binder, A), {binder: idh})
    assert new == cond_fn(A), (new, cond_fn(A))
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (A, cls, A, dom, cond_fn(A)))
    both = w.s([amem, cond_step], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (ph, A, dom, cond_fn(A)))
    return w.s([both, el], 'sylibr', '( %s -> %s e. %s )' % (ph, A, cls))


def tmciz():
    lab = 'tmciz'
    ph = cj(TREE_IZ)
    w = W(lab, '` isZero x s ` at the machine: ~ tm2fiz with ` readA ` , the mover\'s handlers, the loads '
               '` flag := true ` and ` flag := flag && !bitOf ra ` , the summary ` <. flag , cmp >. ` and the '
               'fold ` <. [ toNat ( payloads ) = 0 ] , cmp >. ` on the scanned word; the exit class says '
               '` flag = decide ( toNat l = 0 ) ` and ` cmp ` unchanged (Lean ` isZero_runs ` ).')
    c = Ctx(w, ph, TREE_IZ)
    mk = machine(w, ph, c, ['K', 'I'])
    ll, xg, dd = c[WRD('L', '2o')], c[WRD('X', GAM)], c[STKD('D')]
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    ibl = w.s([ll, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IBL, BITS))
    f2 = w.s([], 'f2ndres', '%s : %s --> 2o' % (P2, BITS))
    lfl_kw = lambda t: dict(fl='1o')
    lzs_kw = lambda t: dict(fl=IFZ(t))
    assert LFL1 == '( u e. TMSt |-> %s )' % SETF('u', **lfl_kw('u')) and LZS == '( u e. TMSt |-> %s )' % SETF('u', **lzs_kw('u'))
    # ---- HLD
    ph1 = '( %s /\\ r e. %s )' % (ph, NPC)
    rin = w.s([], 'simpr', '( %s -> r e. %s )' % (ph1, NPC))
    rr, fl, cm, ca = np_out(w, ph1, 'r', rin)
    lv = lset_val(w, ph1, lfl_kw, 'r', rr)
    LR = '( %s ` r )' % LFL1
    sp = spair_nv(w, ph1, lv, LR)
    sp2 = w.s([cm], 'opeq2d', '( %s -> <. 1o , ( TMcmp ` r ) >. = <. 1o , Q >. )' % ph1)
    sp3 = w.s([sp, sp2], 'eqtrd', '( %s -> ( %s ` %s ) = <. 1o , Q >. )' % (ph1, SPAIR, LR))
    oz0 = ozval(w, ph1, '(/)', closed(w, ph1, 'wrd0', '(/) e. %s' % WB))
    c0 = closed(w, ph1, 'co02', '( %s o. (/) ) = (/)' % P2)
    c0b = w.s([c0], 'fveq2d', '( %s -> ( toNat ` ( %s o. (/) ) ) = ( toNat ` (/) ) )' % (ph1, P2))
    c0c = w.s([c0b, closed(w, ph1, 'tonat0', '( toNat ` (/) ) = 0')], 'eqtrd', '( %s -> ( toNat ` ( %s o. (/) ) ) = 0 )' % (ph1, P2))
    it0 = w.s([c0c], 'iftrued', '( %s -> %s = 1o )' % (ph1, IFT('(/)')))
    it0b = w.s([it0], 'opeq1d', '( %s -> %s = <. 1o , Q >. )' % (ph1, OZX('(/)')))
    oz0b = w.s([oz0, it0b], 'eqtrd', '( %s -> ( %s ` (/) ) = <. 1o , Q >. )' % (ph1, OZ))
    speq = w.s([sp3, oz0b], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` (/) ) )' % (ph1, SPAIR, LR, OZ))
    lrs = w.s([lv['mem'], mk['seq']], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (ph1, LR)) if False else None
    seqr1 = w.s([mk['seq']], 'adantr', '( %s -> %s )' % (ph1, SEQ))
    lrs = w.s([lv['mem'], seqr1], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (ph1, LR))
    hld1 = rab_in2(w, ph1, 's', '( 2nd ` T )', lambda t: '( %s ` %s ) = ( %s ` (/) )' % (SPAIR, t, OZ), LR, lrs, speq)
    HLD = w.s([hld1], 'ralrimiva', '( %s -> A. r e. %s %s e. { s e. ( 2nd ` T ) | ( %s ` s ) = ( %s ` (/) ) } )' % (ph, NPC, LR, SPAIR, OZ))
    # ---- HCzs
    HYP = '( %s ` m ) = ( %s ` t )' % (SPAIR, OZ)
    ph2a = '( %s /\\ ( m e. ( 2nd ` T ) /\\ n e. %s /\\ t e. %s ) )' % (ph, BITS, WB)
    ph2 = '( %s /\\ %s )' % (ph2a, HYP)
    A2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    tr = w.s([], 'simpr', '( %s -> ( m e. ( 2nd ` T ) /\\ n e. %s /\\ t e. %s ) )' % (ph2a, BITS, WB))
    ms = A2(w.s([tr], 'simp1d', '( %s -> m e. ( 2nd ` T ) )' % ph2a), 'm e. ( 2nd ` T )')
    nn = A2(w.s([tr], 'simp2d', '( %s -> n e. %s )' % (ph2a, BITS)), 'n e. %s' % BITS)
    tt = A2(w.s([tr], 'simp3d', '( %s -> t e. %s )' % (ph2a, WB)), 't e. %s' % WB)
    seq2 = A2(w.s([mk['seq']], 'adantr', '( %s -> %s )' % (ph2a, SEQ)), SEQ)
    mm = w.s([ms, seq2], 'eleqtrd', '( %s -> m e. TMSt )' % ph2)
    hyp = w.s([], 'simpr', '( %s -> %s )' % (ph2, HYP))
    N = NVA('m', 'n')
    nv = rd_bit(w, ph2, 'A', 'm', 'n', mm, nn)
    c1, _ = cis_val(w, ph2, nv, N)
    p1 = pbr_val(w, ph2, nv, N, 'n', nn)
    lz = lset_val(w, ph2, lzs_kw, N, nv['mem'])
    LZ = '( %s ` %s )' % (LZS, N)
    spz = spair_nv(w, ph2, lz, LZ)
    # the fields of the loaded state
    # the hypothesis: ( TMfl ` m ) = IFT( t ) and ( TMcmp ` m ) = Q
    spm = spair(w, ph2, 'm', mm)
    ozt = ozval(w, ph2, 't', tt)
    e1 = w.s([spm, ozt], 'eqeq12d', '( %s -> ( %s <-> %s = %s ) )' % (ph2, HYP, SPX('m'), OZX('t')))
    e2 = w.s([e1, hyp], 'mpbid', '( %s -> %s = %s )' % (ph2, SPX('m'), OZX('t')))
    fv1 = w.s([], 'fvexd', '( %s -> ( TMfl ` m ) e. _V )' % ph2); fv2 = w.s([], 'fvexd', '( %s -> ( TMcmp ` m ) e. _V )' % ph2)
    o = w.s([fv1, fv2, w.inst('opthg')], 'syl2anc', '( %s -> ( %s = %s <-> ( ( TMfl ` m ) = %s /\\ ( TMcmp ` m ) = Q ) ) )' % (ph2, SPX('m'), OZX('t'), IFT('t')))
    e3 = w.s([o, e2], 'mpbid', '( %s -> ( ( TMfl ` m ) = %s /\\ ( TMcmp ` m ) = Q ) )' % (ph2, IFT('t')))
    flm = w.s([e3], 'simpld', '( %s -> ( TMfl ` m ) = %s )' % (ph2, IFT('t')))
    cmq = w.s([e3], 'simprd', '( %s -> ( TMcmp ` m ) = Q )' % ph2)
    # IFZ( N ) = IFT( <" n "> ++ t )
    fln = w.s([nv['fields']['fl'], flm], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (ph2, N, IFT('t')))
    bn = w.s([nv['fields']['ra']], 'fveq2d', '( %s -> ( bitOf ` ( TMra ` %s ) ) = ( bitOf ` ( inl ` ( 2nd ` n ) ) ) )' % (ph2, N))
    n2 = w.s([nn, w.inst('tmcbit2')], 'syl', '( %s -> ( 2nd ` n ) e. 2o )' % ph2)
    bs = w.s([n2, w.inst('bitofsome')], 'syl', '( %s -> ( bitOf ` ( inl ` ( 2nd ` n ) ) ) = ( 2nd ` n ) )' % ph2)
    bn2 = w.s([bn, bs], 'eqtrd', '( %s -> ( bitOf ` ( TMra ` %s ) ) = ( 2nd ` n ) )' % (ph2, N))
    q1 = w.s([fln], 'eqeq1d', '( %s -> ( ( TMfl ` %s ) = 1o <-> %s = 1o ) )' % (ph2, N, IFT('t')))
    if1 = w.s([], 'tmcif1', '( %s = 1o <-> ( toNat ` ( %s o. t ) ) = 0 )' % (IFT('t'), P2))
    if1a = w.s([if1], 'a1i', '( %s -> ( %s = 1o <-> ( toNat ` ( %s o. t ) ) = 0 ) )' % (ph2, IFT('t'), P2))
    q1b = w.s([q1, if1a], 'bitrd', '( %s -> ( ( TMfl ` %s ) = 1o <-> ( toNat ` ( %s o. t ) ) = 0 ) )' % (ph2, N, P2))
    q2 = w.s([bn2], 'eqeq1d', '( %s -> ( ( bitOf ` ( TMra ` %s ) ) = 1o <-> ( 2nd ` n ) = 1o ) )' % (ph2, N))
    q2b = w.s([q2], 'notbid', '( %s -> ( -. ( bitOf ` ( TMra ` %s ) ) = 1o <-> -. ( 2nd ` n ) = 1o ) )' % (ph2, N))
    b2n = w.s([n2, w.inst('bwel2on')], 'syl', '( %s -> ( -. ( 2nd ` n ) = 1o <-> ( 2nd ` n ) = (/) ) )' % ph2)
    q2c = w.s([q2b, b2n], 'bitrd', '( %s -> ( -. ( bitOf ` ( TMra ` %s ) ) = 1o <-> ( 2nd ` n ) = (/) ) )' % (ph2, N))
    q3 = w.s([q1b, q2c], 'anbi12d', '( %s -> ( ( ( TMfl ` %s ) = 1o /\\ -. ( bitOf ` ( TMra ` %s ) ) = 1o ) <-> ( ( toNat ` ( %s o. t ) ) = 0 /\\ ( 2nd ` n ) = (/) ) ) )' % (ph2, N, N, P2))
    ac = w.s([], 'ancom', '( ( ( toNat ` ( %s o. t ) ) = 0 /\\ ( 2nd ` n ) = (/) ) <-> ( ( 2nd ` n ) = (/) /\\ ( toNat ` ( %s o. t ) ) = 0 ) )' % (P2, P2))
    aca = w.s([ac], 'a1i', '( %s -> %s )' % (ph2, formula(w, ac)))
    tw = w.s([tt, w.s([f2], 'a1i', '( %s -> %s : %s --> 2o )' % (ph2, P2, BITS)), w.inst('wrdco')], 'syl2anc', '( %s -> ( %s o. t ) e. Word 2o )' % (ph2, P2))
    tn0 = w.s([n2, tw, w.inst('tmctn0c')], 'syl2anc', '( %s -> ( ( toNat ` ( <" ( 2nd ` n ) "> ++ ( %s o. t ) ) ) = 0 <-> ( ( 2nd ` n ) = (/) /\\ ( toNat ` ( %s o. t ) ) = 0 ) ) )' % (ph2, P2, P2))
    q4 = w.s([w.s([q3, aca], 'bitrd', '( %s -> ( ( ( TMfl ` %s ) = 1o /\\ -. ( bitOf ` ( TMra ` %s ) ) = 1o ) <-> ( ( 2nd ` n ) = (/) /\\ ( toNat ` ( %s o. t ) ) = 0 ) ) )' % (ph2, N, N, P2)), tn0], 'bitr4d',
             '( %s -> ( ( ( TMfl ` %s ) = 1o /\\ -. ( bitOf ` ( TMra ` %s ) ) = 1o ) <-> ( toNat ` ( <" ( 2nd ` n ) "> ++ ( %s o. t ) ) ) = 0 ) )' % (ph2, N, N, P2))
    # ( P2 o. ( <" n "> ++ t ) ) = ( <" ( 2nd ` n ) "> ++ ( P2 o. t ) )
    f2a = w.s([f2], 'a1i', '( %s -> %s : %s --> 2o )' % (ph2, P2, BITS))
    s1n = w.s([nn], 's1cld', '( %s -> <" n "> e. %s )' % (ph2, WB))
    cc = w.s([s1n, tt, f2a, w.inst('ccatco')], 'syl3anc', '( %s -> ( %s o. ( <" n "> ++ t ) ) = ( ( %s o. <" n "> ) ++ ( %s o. t ) ) )' % (ph2, P2, P2, P2))
    s1c = w.s([nn, f2a, w.inst('s1co')], 'syl2anc', '( %s -> ( %s o. <" n "> ) = <" ( %s ` n ) "> )' % (ph2, P2, P2))
    fr = w.s([nn, w.inst('fvres')], 'syl', '( %s -> ( %s ` n ) = ( 2nd ` n ) )' % (ph2, P2))
    s1c2 = w.s([s1c, w.s([fr], 's1eqd', '( %s -> <" ( %s ` n ) "> = <" ( 2nd ` n ) "> )' % (ph2, P2))], 'eqtrd', '( %s -> ( %s o. <" n "> ) = <" ( 2nd ` n ) "> )' % (ph2, P2))
    cc2 = w.s([cc, w.s([s1c2], 'oveq1d', '( %s -> ( ( %s o. <" n "> ) ++ ( %s o. t ) ) = ( <" ( 2nd ` n ) "> ++ ( %s o. t ) ) )' % (ph2, P2, P2, P2))], 'eqtrd',
              '( %s -> ( %s o. ( <" n "> ++ t ) ) = ( <" ( 2nd ` n ) "> ++ ( %s o. t ) ) )' % (ph2, P2, P2))
    cc3 = w.s([w.s([cc2], 'fveq2d', '( %s -> ( toNat ` ( %s o. ( <" n "> ++ t ) ) ) = ( toNat ` ( <" ( 2nd ` n ) "> ++ ( %s o. t ) ) ) )' % (ph2, P2, P2))], 'eqeq1d',
              '( %s -> ( ( toNat ` ( %s o. ( <" n "> ++ t ) ) ) = 0 <-> ( toNat ` ( <" ( 2nd ` n ) "> ++ ( %s o. t ) ) ) = 0 ) )' % (ph2, P2, P2))
    q5 = w.s([q4, cc3], 'bitr4d', '( %s -> ( ( ( TMfl ` %s ) = 1o /\\ -. ( bitOf ` ( TMra ` %s ) ) = 1o ) <-> ( toNat ` ( %s o. ( <" n "> ++ t ) ) ) = 0 ) )' % (ph2, N, N, P2))
    ifz = w.s([q5], 'ifbid', '( %s -> %s = %s )' % (ph2, IFZ(N), IFT('( <" n "> ++ t )')))
    cmN = w.s([nv['fields']['cmp'], cmq], 'eqtrd', '( %s -> ( TMcmp ` %s ) = Q )' % (ph2, N))
    spz2 = w.s([spz, w.s([ifz, cmN], 'opeq12d', '( %s -> <. %s , ( TMcmp ` %s ) >. = %s )' % (ph2, IFZ(N), N, OZX('( <" n "> ++ t )')))], 'eqtrd',
               '( %s -> ( %s ` %s ) = %s )' % (ph2, SPAIR, LZ, OZX('( <" n "> ++ t )')))
    ntw = w.s([s1n, tt, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" n "> ++ t ) e. %s )' % (ph2, WB))
    oznt = ozval(w, ph2, '( <" n "> ++ t )', ntw)
    spz3 = w.s([spz2, oznt], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` ( <" n "> ++ t ) ) )' % (ph2, SPAIR, LZ, OZ))
    body = '( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = n /\\ ( %s ` %s ) = ( %s ` ( <" n "> ++ t ) ) )' % (CIS, N, PBR, N, SPAIR, LZ, OZ)
    j = w.s([c1, p1, spz3], '3jca', '( %s -> %s )' % (ph2, body))
    jx = w.s([j], 'ex', '( %s -> ( %s -> %s ) )' % (ph2a, HYP, body))
    HCZ = w.s([jx], 'ralrimivvva', '( %s -> A. m e. ( 2nd ` T ) A. n e. %s A. t e. %s ( %s -> %s ) )' % (ph, BITS, WB, HYP, body))
    # ---- HEzs
    ph3 = '( %s /\\ n e. ( 2nd ` T ) )'  % ph
    ns = w.s([], 'simpr', '( %s -> n e. ( 2nd ` T ) )' % ph3)
    seq3 = w.s([mk['seq']], 'adantr', '( %s -> %s )' % (ph3, SEQ))
    nn3 = w.s([ns, seq3], 'eleqtrd', '( %s -> n e. TMSt )' % ph3)
    N3 = NVA('n', '4')
    nv3 = rd_comma(w, ph3, 'A', 'n', nn3)
    c3, _ = cis_val(w, ph3, nv3, N3)
    c3n = not1o(w, ph3, c3, CIS, N3)
    spn = spair(w, ph3, N3, nv3['mem'])
    spn2 = w.s([spn, w.s([nv3['fields']['fl'], nv3['fields']['cmp']], 'opeq12d', '( %s -> %s = %s )' % (ph3, SPX(N3), SPX('n')))], 'eqtrd',
               '( %s -> ( %s ` %s ) = %s )' % (ph3, SPAIR, N3, SPX('n')))
    spnn = spair(w, ph3, 'n', nn3)
    spn3 = w.s([spn2, spnn], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` n ) )' % (ph3, SPAIR, N3, SPAIR))
    body3 = '( -. ( %s ` %s ) = 1o /\\ ( %s ` %s ) = ( %s ` n ) )' % (CIS, N3, SPAIR, N3, SPAIR)
    HEZ = w.s([w.s([c3n, spn3], 'jca', '( %s -> %s )' % (ph3, body3))], 'ralrimiva', '( %s -> A. n e. ( 2nd ` T ) %s )' % (ph, body3))
    # ---- the mover's interface and the class
    mvin = w.s([], 'tmcmvin', ST_MVIN)
    hc = w.s([mvin], 'simpli', ST_MVIN.split(' /\\ A. r e. ')[0][2:])
    he = w.s([mvin], 'simpri', 'A. r e. ' + ST_MVIN.split(' /\\ A. r e. ')[1][:-2])
    hca = w.s([hc], 'a1i', '( %s -> %s )' % (ph, formula(w, hc))); hea = w.s([he], 'a1i', '( %s -> %s )' % (ph, formula(w, he)))
    nss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPC))
    nss2 = w.s([nss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPC))
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], CTY(CIS): cis_ty(w, ph, mk),
             LTY(LFL1): lset_ty(w, ph, mk, LFL1, lfl_kw), LTY(LZS): lset_ty(w, ph, mk, LZS, lzs_kw),
             leaf(hca): hca, leaf(hea): hea, leaf(nss2): nss2, leaf(HLD): HLD, leaf(HCZ): HCZ, leaf(HEZ): HEZ,
             WRD(IBL, BITS): ibl}
    for k in ['K', 'I']:
        K = mk['k'][k]
        extra['%s e. %s' % (k, DG)] = K['kd']
        extra[RTY('TMrdA', k)] = K['hdl']['TMrdA']
        extra[PTY(PBR, k)] = pbr_ty(w, ph, mk, k)
        extra['%s C_ %s' % (BITS, GX(k))] = bitsgk(w, ph, mk, k)
        extra['4 e. %s' % GX(k)] = letgk(w, ph, mk, '4', k, g4)
    extra[WRD('X', GK)] = togk(w, ph, mk, 'X', 'K', xg)
    bld = Builder(w, ph, c, extra)
    m = {'F': 'TMrdA', "F'": 'TMrdA', 'C': CIS, 'P': PBR, "P'": PBR, 'L': LFL1, "L'": LZS, 'B': BITS, 'Y': '4',
         "S'": SPAIR, 'O': OZ, 'W': IBL, 'N': NPC}
    ante, concl = split_imp(stmt('tm2fiz'))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl, m)
    tri = w.s([st, w.inst('tm2fiz')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1, n1 = triple_parts(c2)
    # ---- the exit class: { q e. ( 2nd ` T ) | ( SPAIR ` q ) = ( OZ ` IBL ) } = NZC
    EX = '{ q e. ( 2nd ` T ) | ( %s ` q ) = ( %s ` %s ) }' % (SPAIR, OZ, IBL)
    assert EX in D1, (EX, D1)
    r1 = w.s([mk['seq']], 'rabeqdv', '( %s -> %s = { q e. TMSt | ( %s ` q ) = ( %s ` %s ) } )' % (ph, EX, SPAIR, OZ, IBL))
    phq = '( %s /\\ q e. TMSt )' % ph
    qq = w.s([], 'simpr', '( %s -> q e. TMSt )' % phq)
    spq = spair(w, phq, 'q', qq)
    ozi = ozval(w, phq, IBL, w.s([ibl], 'adantr', '( %s -> %s e. Word %s )' % (phq, IBL, BITS)))
    inv = w.s([w.s([ll], 'adantr', '( %s -> L e. Word 2o )' % phq), w.inst('tmcibinv')], 'syl', '( %s -> ( %s o. %s ) = L )' % (phq, P2, IBL))
    inv2 = w.s([w.s([w.s([inv], 'fveq2d', '( %s -> ( toNat ` ( %s o. %s ) ) = ( toNat ` L ) )' % (phq, P2, IBL))], 'eqeq1d',
                    '( %s -> ( ( toNat ` ( %s o. %s ) ) = 0 <-> ( toNat ` L ) = 0 ) )' % (phq, P2, IBL))], 'ifbid',
               '( %s -> %s = %s )' % (phq, IFT(IBL), IFL))
    ozi2 = w.s([ozi, w.s([inv2], 'opeq1d', '( %s -> %s = <. %s , Q >. )' % (phq, OZX(IBL), IFL))], 'eqtrd', '( %s -> ( %s ` %s ) = <. %s , Q >. )' % (phq, OZ, IBL, IFL))
    eq = w.s([spq, ozi2], 'eqeq12d', '( %s -> ( ( %s ` q ) = ( %s ` %s ) <-> %s = <. %s , Q >. ) )' % (phq, SPAIR, OZ, IBL, SPX('q'), IFL))
    fq1 = w.s([], 'fvexd', '( %s -> ( TMfl ` q ) e. _V )' % phq); fq2 = w.s([], 'fvexd', '( %s -> ( TMcmp ` q ) e. _V )' % phq)
    oq = w.s([fq1, fq2, w.inst('opthg')], 'syl2anc', '( %s -> ( %s = <. %s , Q >. <-> ( ( TMfl ` q ) = %s /\\ ( TMcmp ` q ) = Q ) ) )' % (phq, SPX('q'), IFL, IFL))
    eq2 = w.s([eq, oq], 'bitrd', '( %s -> ( ( %s ` q ) = ( %s ` %s ) <-> ( ( TMfl ` q ) = %s /\\ ( TMcmp ` q ) = Q ) ) )' % (phq, SPAIR, OZ, IBL, IFL))
    condq = lambda t: '( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = Q )' % (t, IFL, t)
    r2 = w.s([eq2], 'rabbidva', '( %s -> { q e. TMSt | ( %s ` q ) = ( %s ` %s ) } = { q e. TMSt | %s } )' % (ph, SPAIR, OZ, IBL, condq('q')))
    idq = w.s([], 'id', '( q = h -> q = h )')
    cgq, newq = w.wcongr(condq('q'), {'q': 'h'}, 'q = h', {'q': idq})
    assert newq == condq('h')
    r3 = w.s([cgq], 'cbvrabv', '{ q e. TMSt | %s } = %s' % (condq('q'), NZC))
    r3a = w.s([r3], 'a1i', '( %s -> { q e. TMSt | %s } = %s )' % (ph, condq('q'), NZC))
    req = w.s([w.s([r1, r2], 'eqtrd', '( %s -> %s = { q e. TMSt | %s } )' % (ph, EX, condq('q'))), r3a], 'eqtrd', '( %s -> %s = %s )' % (ph, EX, NZC))
    deq = clnneq(w, ph, 'E', req, EX, NZC, 'D')
    ln = w.s([ll, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` L ) )' % (ph, IBL))
    ln3 = w.s([w.s([ln], 'oveq2d', '( %s -> ( 2 x. ( # ` %s ) ) = ( 2 x. ( # ` L ) ) )' % (ph, IBL))], 'oveq1d',
              '( %s -> ( ( 2 x. ( # ` %s ) ) + 5 ) = ( ( 2 x. ( # ` L ) ) + 5 ) )' % (ph, IBL))
    _, C2, D2, n2 = hrrw(w, ph, tri, C1, D1, n1, deq=deq, neq=ln3, qed=True)
    assert TRI(C2, D2, n2) == CONCL_IZ, (TRI(C2, D2, n2), CONCL_IZ)
    return w.run()


if __name__ == '__main__':
    if want('tmcif1'): tmcif1()
    if want('tmctn0c'): tmctn0c()
    if want('tmcibinv'): tmcibinv()
    if want('tmciz'): tmciz()
