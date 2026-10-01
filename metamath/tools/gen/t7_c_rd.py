"""T7: the four named handlers (blueprint D2): their types, their values on a
bit letter and on a non-bit letter, the identity pop handler's type, and the
five typings at the generic alphabet of the type triple (tmchdl)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

TEST = lambda o: '( ( 1st ` %s ) = (/) /\\ ( 2nd ` %s ) e. ( { 1 } X. 2o ) )' % (o, o)
OPTB = '( 2o |_| 1o )'
LEANDEF = dict(A='readA', B='readB', Bit='readBit', End='readEnd')


def body(h, v, o):
    """the value of the reader h at ( v , o ), as df-tmrd* writes it"""
    bit = dict(RDBIT[h])
    for k in bit:
        bit[k] = bit[k].replace('( 2nd ` Z )', '( 2nd ` ( 2nd ` %s ) )' % o)
    return 'if ( %s , %s , %s )' % (TEST(o), SETF(v, **bit), SETF(v, **RDNONE[h]))


def compcl(w, ph, comp, f, vv, extra):
    """( ph -> comp e. CODOM[f] ) for a component of a SETF tuple: an accessor of v
    (closure lemma from vv : v e. TMSt) or one of the special values; `extra`
    maps a special value to its step"""
    if comp in extra:
        return extra[comp]
    if comp == '1o':
        return w.s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % ph)
    if comp == '(/)':
        return w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % ph)
    if comp == NONE:
        z1 = w.s([], '0lt1o', '(/) e. 1o')
        m = w.s([z1, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, OPTB))
        return w.s([m], 'a1i', '( %s -> %s e. %s )' % (ph, NONE, OPTB))
    # an accessor of the state
    for g in ORDER:
        if comp == FLD(g, 'v') or comp == FLD(g, 'V'):
            return w.s([vv, w.inst('tmc%scl' % g)], 'syl', '( %s -> %s e. %s )' % (ph, comp, CODOM[g]))
    raise KeyError(comp)


def tuple_in(w, ph, tup_kw, v, vv, extra):
    """( ph -> SETF( v , **tup_kw ) e. TMSt ) by tmcstmk"""
    comps = [tup_kw.get(f, FLD(f, v)) for f in ORDER]
    steps = [compcl(w, ph, c, f, vv, extra) for c, f in zip(comps, ORDER)]
    t1 = w.s(steps[0:3], '3jca', '( %s -> ( %s e. 2o /\\ %s e. %s /\\ %s e. %s ) )' % (ph, comps[0], comps[1], OPTB, comps[2], OPTB))
    t2 = w.s(steps[3:5], 'jca', '( %s -> ( %s e. 2o /\\ %s e. 2o ) )' % (ph, comps[3], comps[4]))
    t3 = w.s(steps[5:7], 'jca', '( %s -> ( %s e. 3o /\\ %s e. 2o ) )' % (ph, comps[5], comps[6]))
    ty = w.s([t1, t2, t3], '3jca', '( %s -> %s )' % (ph, cj(tsub(TY7, dict(zip('ABCDEFG', comps))))))
    return w.s([ty, w.inst('tmcstmk')], 'syl', '( %s -> %s e. TMSt )' % (ph, MK(*comps)))


def tmcrdf(h):
    name = READERS[h]
    lab = 'tmcrd%sf' % h.lower()
    w = W(lab, 'The handler ` %s ` is a function on the states and the popped symbols (Lean: its type '
               '` St -> Option Gamma\' -> St ` ), the shape ~ df-tm2stmt \'s pop and peek take.' % LEANDEF[h])
    ph = '( v e. TMSt /\\ o e. %s )' % OPT
    vv = w.s([], 'simpl', '( %s -> v e. TMSt )' % ph)
    B = body(h, 'v', 'o')
    # the bit branch
    pht = '( %s /\\ %s )' % (ph, TEST('o'))
    vvt = w.s([vv], 'adantr', '( %s -> v e. TMSt )' % pht)
    tt = w.s([], 'simpr', '( %s -> %s )' % (pht, TEST('o')))
    t2 = w.s([tt], 'simprd', '( %s -> ( 2nd ` o ) e. ( { 1 } X. 2o ) )' % pht)
    t3 = w.s([t2, w.inst('tmcbit2')], 'syl', '( %s -> ( 2nd ` ( 2nd ` o ) ) e. 2o )' % pht)
    t4 = w.s([t3, w.inst('djulcl')], 'syl', '( %s -> ( inl ` ( 2nd ` ( 2nd ` o ) ) ) e. %s )' % (pht, OPTB))
    bit = {k: val.replace('( 2nd ` Z )', '( 2nd ` ( 2nd ` o ) )') for k, val in RDBIT[h].items()}
    m1 = tuple_in(w, pht, bit, 'v', vvt, {'( inl ` ( 2nd ` ( 2nd ` o ) ) )': t4})
    # the other branch
    phf = '( %s /\\ -. %s )' % (ph, TEST('o'))
    vvf = w.s([vv], 'adantr', '( %s -> v e. TMSt )' % phf)
    m2 = tuple_in(w, phf, RDNONE[h], 'v', vvf, {})
    m = w.s([m1, m2], 'ifclda', '( %s -> %s e. TMSt )' % (ph, B))
    ral = w.s([m], 'rgen2', 'A. v e. TMSt A. o e. %s %s e. TMSt' % (OPT, B))
    d = w.s([], 'df-tmrd%s' % h.lower(), '%s = ( v e. TMSt , o e. %s |-> %s )' % (name, OPT, B))
    fm = w.s([d], 'fmpo', '( A. v e. TMSt A. o e. %s %s e. TMSt <-> %s : ( TMSt X. %s ) --> TMSt )' % (OPT, B, name, OPT))
    ff = w.s([ral, fm], 'mpbi', '%s : ( TMSt X. %s ) --> TMSt' % (name, OPT))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ov = w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.s([], '1oex', '1o e. _V'), w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xv = w.s([sv, ov, w.inst('xpexg')], 'mp2an', '( TMSt X. %s ) e. _V' % OPT)
    em = w.s([sv, xv, w.inst('elmapg')], 'mp2an', '( %s e. %s <-> %s : ( TMSt X. %s ) --> TMSt )' % (name, HDLC, name, OPT))
    w.qed([ff, em], 'mpbir', '%s e. %s' % (name, HDLC))
    return w.run()


def rdval(h, bitcase):
    name = READERS[h]
    lab = 'tmcrd%s%s' % (h.lower(), 'b' if bitcase else 'n')
    if bitcase:
        ph = '( V e. TMSt /\\ Z e. ( { 1 } X. 2o ) )'
        desc = ('Value of ` %s ` on a bit letter (Lean ` %s_bit ` ): the register is loaded with the bit.'
                % (LEANDEF[h], LEANDEF[h]))
    else:
        ph = "( V e. TMSt /\\ Z e. Gamma' /\\ -. Z e. ( { 1 } X. 2o ) )"
        desc = ('Value of ` %s ` on a letter that is not a bit, the terminator in every use (Lean ` %s_comma ` ).'
                % (LEANDEF[h], LEANDEF[h]))
    w = W(lab, desc)
    OZ = '( inl ` Z )'
    B = body(h, 'v', 'o')
    BV = body(h, 'V', OZ)
    vv = w.s([], 'simpl' if bitcase else 'simp1', '( %s -> V e. TMSt )' % ph)
    zz = w.s([], 'simpr' if bitcase else 'simp2', '( %s -> Z e. %s )' % (ph, BITS if bitcase else GAM))
    zg = zz
    if bitcase:
        bs = w.s([], 'tm2lbits', "( { 1 } X. 2o ) C_ Gamma'")
        bsa = w.s([bs], 'a1i', "( %s -> ( { 1 } X. 2o ) C_ Gamma' )" % ph)
        zg = w.s([bsa, zz], 'sseldd', "( %s -> Z e. Gamma' )" % ph)
    zv = w.s([zg], 'elexd', '( %s -> Z e. _V )' % ph)
    oz = w.s([zg, w.inst('djulcl')], 'syl', '( %s -> %s e. %s )' % (ph, OZ, OPT))
    # the substitution instance for ovmpoga
    ante = '( v = V /\\ o = %s )' % OZ
    ev = w.s([], 'simpl', '( %s -> v = V )' % ante)
    eo = w.s([], 'simpr', '( %s -> o = %s )' % (ante, OZ))
    cg, newB = w.congr(B, {'v': 'V', 'o': OZ}, ante, {'v': ev, 'o': eo})
    assert newB == BV, (newB, BV)
    d = w.s([], 'df-tmrd%s' % h.lower(), '%s = ( v e. TMSt , o e. %s |-> %s )' % (name, OPT, B))
    # BV e. _V : both branches are ordered pairs
    # build BV e. _V from opex of the two tuples
    tb = SETF('V', **{k: val.replace('( 2nd ` Z )', '( 2nd ` ( 2nd ` %s ) )' % OZ) for k, val in RDBIT[h].items()})
    tn = SETF('V', **RDNONE[h])
    e1 = w.s([], 'opex', '%s e. _V' % tb)
    e2 = w.s([], 'opex', '%s e. _V' % tn)
    e3 = w.s([e1, e2], 'ifcli', '%s e. _V' % BV)
    e3a = w.s([e3], 'a1i', '( %s -> %s e. _V )' % (ph, BV))
    j = w.s([vv, oz, e3a], '3jca', '( %s -> ( V e. TMSt /\\ %s e. %s /\\ %s e. _V ) )' % (ph, OZ, OPT, BV))
    ovi = w.s([cg, d], 'ovmpoga', '( ( V e. TMSt /\\ %s e. %s /\\ %s e. _V ) -> ( V %s %s ) = %s )' % (OZ, OPT, BV, name, OZ, BV))
    ov = w.s([j, ovi], 'syl', '( %s -> ( V %s %s ) = %s )' % (ph, name, OZ, BV))
    dov = w.s([], 'df-ov', '( V %s %s ) = ( %s ` <. V , %s >. )' % (name, OZ, name, OZ))
    dova = w.s([dov], 'a1i', '( %s -> ( V %s %s ) = ( %s ` <. V , %s >. ) )' % (ph, name, OZ, name, OZ))
    fv = w.s([dova, ov], 'eqtr3d', '( %s -> ( %s ` <. V , %s >. ) = %s )' % (ph, name, OZ, BV))
    # evaluate the test: ( inl ` Z ) = <. (/) , Z >.
    iv = w.s([zv, w.inst('inlval')], 'syl', '( %s -> %s = <. (/) , Z >. )' % (ph, OZ))
    z0 = w.s([], '0ex', '(/) e. _V')
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % ph)
    f1 = w.s([iv], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. (/) , Z >. ) )' % (ph, OZ))
    f1b = w.s([z0a, zv, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. (/) , Z >. ) = (/) )' % ph)
    f1c = w.s([f1, f1b], 'eqtrd', '( %s -> ( 1st ` %s ) = (/) )' % (ph, OZ))
    f2 = w.s([iv], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. (/) , Z >. ) )' % (ph, OZ))
    f2b = w.s([z0a, zv, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. (/) , Z >. ) = Z )' % ph)
    f2c = w.s([f2, f2b], 'eqtrd', '( %s -> ( 2nd ` %s ) = Z )' % (ph, OZ))
    if bitcase:
        m2 = w.s([f2c, zz], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. ( { 1 } X. 2o ) )' % (ph, OZ))
        tst = w.s([f1c, m2], 'jca', '( %s -> %s )' % (ph, TEST(OZ)))
        it = w.s([tst], 'iftrued', '( %s -> %s = %s )' % (ph, BV, tb))
        # ( 2nd ` ( 2nd ` ( inl ` Z ) ) ) = ( 2nd ` Z ) inside the tuple
        f3 = w.s([f2c], 'fveq2d', '( %s -> ( 2nd ` ( 2nd ` %s ) ) = ( 2nd ` Z ) )' % (ph, OZ))
        if '( 2nd ` ( 2nd ` %s ) )' % OZ in tb:
            rw, tb2 = w.rewrite(tb, {'( 2nd ` ( 2nd ` %s ) )' % OZ: ('( 2nd ` Z )', f3)}, ph)
            assert tb2 == SETF('V', **RDBIT[h]), (tb2, SETF('V', **RDBIT[h]))
            val = w.s([it, rw], 'eqtrd', '( %s -> %s = %s )' % (ph, BV, tb2))
        else:
            tb2 = tb; val = it
        w.qed([fv, val], 'eqtrd', '( %s -> ( %s ` <. V , %s >. ) = %s )' % (ph, name, OZ, tb2))
    else:
        nz = w.s([], 'simp3', '( %s -> -. Z e. ( { 1 } X. 2o ) )' % ph)
        m2 = w.s([f2c], 'eleq1d', '( %s -> ( ( 2nd ` %s ) e. ( { 1 } X. 2o ) <-> Z e. ( { 1 } X. 2o ) ) )' % (ph, OZ))
        m3 = w.s([m2, nz], 'mtbird', '( %s -> -. ( 2nd ` %s ) e. ( { 1 } X. 2o ) )' % (ph, OZ))
        m4 = w.s([m3], 'intnand', '( %s -> -. %s )' % (ph, TEST(OZ)))
        it = w.s([m4], 'iffalsed', '( %s -> %s = %s )' % (ph, BV, tn))
        w.qed([fv, it], 'eqtrd', '( %s -> ( %s ` <. V , %s >. ) = %s )' % (ph, name, OZ, tn))
    return w.run()


def tmcpidf():
    lab = 'tmcpidf'
    w = W(lab, 'The identity pop handler ` fun v _ => v ` of the strip loop (TM/Canon.lean) as a function on '
               'the states and the popped symbols.')
    f = w.s([], 'f1stres', '%s : ( TMSt X. %s ) --> TMSt' % (PID, OPT))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ov = w.s([w.s([], 'gammaex', "Gamma' e. _V"), w.s([], '1oex', '1o e. _V'), w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xv = w.s([sv, ov, w.inst('xpexg')], 'mp2an', '( TMSt X. %s ) e. _V' % OPT)
    em = w.s([sv, xv, w.inst('elmapg')], 'mp2an', '( %s e. %s <-> %s : ( TMSt X. %s ) --> TMSt )' % (PID, HDLC, PID, OPT))
    w.qed([f, em], 'mpbir', '%s e. %s' % (PID, HDLC))
    return w.run()


def tmchdl():
    lab = 'tmchdl'
    ph = '( ( %s /\\ %s ) /\\ K e. ( 0 ..^ 8 ) )' % (GEQ, SEQ)
    w = W(lab, 'The five concrete pop/peek handlers typed at the alphabet of stack ` K ` of the type triple, '
               'as the generic fragment lemmas want them (blueprint D1).')
    geq = w.s([w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (ph, GEQ, SEQ))], 'simpld', '( %s -> %s )' % (ph, GEQ))
    seq = w.s([w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (ph, GEQ, SEQ))], 'simprd', '( %s -> %s )' % (ph, SEQ))
    kk = w.s([], 'simpr', '( %s -> K e. ( 0 ..^ 8 ) )' % ph)
    gk = w.s([geq, kk], 'jca', '( %s -> ( %s /\\ K e. ( 0 ..^ 8 ) ) )' % (ph, GEQ))
    gk2 = w.s([gk, w.inst('tmcgk')], 'syl', "( %s -> ( K e. dom ( 1st ` ( 1st ` T ) ) /\\ ( ( 1st ` ( 1st ` T ) ) ` K ) = Gamma' ) )" % ph)
    ge = w.s([gk2], 'simprd', "( %s -> ( ( 1st ` ( 1st ` T ) ) ` K ) = Gamma' )" % ph)
    # ( TMSt ^m ( TMSt X. ( Gamma' |_| 1o ) ) ) = HDL( K )
    seqr = w.s([seq], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    ger = w.s([ge], 'eqcomd', "( %s -> Gamma' = ( ( 1st ` ( 1st ` T ) ) ` K ) )" % ph)
    e1 = w.s([ger, w.inst('djueq1')], 'syl', "( %s -> ( Gamma' |_| 1o ) = ( ( ( 1st ` ( 1st ` T ) ) ` K ) |_| 1o ) )" % ph)
    e2 = w.s([seqr, e1], 'xpeq12d', "( %s -> ( TMSt X. ( Gamma' |_| 1o ) ) = ( ( 2nd ` T ) X. ( ( ( 1st ` ( 1st ` T ) ) ` K ) |_| 1o ) ) )" % ph)
    e3 = w.s([seqr, e2], 'oveq12d', '( %s -> %s = %s )' % (ph, HDLC, HDL('K')))
    def ty(name, lem):
        c = w.s([], lem, '%s e. %s' % (name, HDLC))
        ca = w.s([c], 'a1i', '( %s -> %s e. %s )' % (ph, name, HDLC))
        return w.s([ca, e3], 'eleqtrd', '( %s -> %s e. %s )' % (ph, name, HDL('K')))
    ta, tb = ty('TMrdA', 'tmcrdaf'), ty('TMrdB', 'tmcrdbf')
    tc, td = ty('TMrdBit', 'tmcrdbitf'), ty('TMrdEnd', 'tmcrdendf')
    te = ty(PID, 'tmcpidf')
    j1 = w.s([ta, tb], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, RTY('TMrdA', 'K'), RTY('TMrdB', 'K')))
    j2 = w.s([tc, td], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, RTY('TMrdBit', 'K'), RTY('TMrdEnd', 'K')))
    w.qed([j1, j2, te], '3jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) )'
          % (ph, RTY('TMrdA', 'K'), RTY('TMrdB', 'K'), RTY('TMrdBit', 'K'), RTY('TMrdEnd', 'K'), RTY(PID, 'K')))
    return w.run()


if __name__ == '__main__':
    for h in ['A', 'B', 'Bit', 'End']:
        if want('tmcrd%sf' % h.lower()): tmcrdf(h)
    for h in ['A', 'B', 'Bit', 'End']:
        if want('tmcrd%sb' % h.lower()): rdval(h, True)
        if want('tmcrd%sn' % h.lower()): rdval(h, False)
    if want('tmcpidf'): tmcpidf()
    if want('tmchdl'): tmchdl()
