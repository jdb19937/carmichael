"""T7: the state record ` TMSt ` --- the closures of the seven accessors, the
membership of a typed seven-tuple, and the accessors' values on a tuple
(blueprint D2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

# the product structure of df-tmst, innermost last: TMSt = 2o X. ( OPTB X. ( OPTB X. ( 2o X. ( 2o X. ( 3o X. 2o ) ) ) ) )
OPTB = '( 2o |_| 1o )'
COMPS = [CODOM[f] for f in ORDER]          # 2o OPTB OPTB 2o 2o 3o 2o


def prodfrom(i):
    """the product of the components i..6"""
    out = COMPS[6]
    for c in reversed(COMPS[i:6]):
        out = '( %s X. %s )' % (c, out)
    return out


PROD0 = prodfrom(0)
DFST = 'df-tmst'


def tmst_unfold(w, ph, vv):
    """( ph -> V e. PROD0 ) from vv : ( ph -> V e. TMSt )"""
    d = w.s([], DFST, 'TMSt = %s' % PROD0)
    return w.s([vv, d], 'eleqtrdi', '( %s -> V e. %s )' % (ph, PROD0))


def proj(i, v):
    """the projection of field i applied to v, as the accessor definitions write it"""
    t = v
    for _ in range(i):
        t = '( 2nd ` %s )' % t
    return t if i == 6 else '( 1st ` %s )' % t


def accval(w, ph, f, V, vv):
    """( ph -> ( TMxx ` V ) = proj ) by fvmptd from vv : ( ph -> V e. TMSt )"""
    i = ORDER.index(f)
    body = proj(i, 'v')
    d = w.s([], 'df-tm%s' % f, '%s = ( v e. TMSt |-> %s )' % (ACC[f], body))
    da = w.s([d], 'a1i', '( %s -> %s = ( v e. TMSt |-> %s ) )' % (ph, ACC[f], body))
    # ( v = V -> proj(v) = proj(V) )
    f1 = '1st' if i == 0 else '2nd'
    e = w.s([], 'fveq2', '( v = %s -> ( %s ` v ) = ( %s ` %s ) )' % (V, f1, f1, V))
    cur_v, cur_V = ('( %s ` v )' % f1), ('( %s ` %s )' % (f1, V))
    for k in range(1, i):
        e = w.s([e], 'fveq2d', '( v = %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (V, cur_v, cur_V))
        cur_v, cur_V = '( 2nd ` %s )' % cur_v, '( 2nd ` %s )' % cur_V
    if 0 < i < 6:
        e = w.s([e], 'fveq2d', '( v = %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (V, cur_v, cur_V))
    pv = proj(i, V)
    ea = w.s([e], 'adantl', '( ( %s /\\ v = %s ) -> %s = %s )' % (ph, V, body, pv))
    ex = w.s([], 'fvexd', '( %s -> %s e. _V )' % (ph, pv))
    return w.s([da, ea, vv, ex], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ph, ACC[f], V, pv)), pv


def tmc_cl(f):
    lab = 'tmc%scl' % f
    i = ORDER.index(f)
    ph = 'V e. TMSt'
    w = W(lab, 'Closure of the ` %s ` field of a machine state (Lean: the type of ` St.%s ` ).' % (f, f))
    vv = w.s([], 'id', '( %s -> V e. TMSt )' % ph)
    val, pv = accval(w, ph, f, 'V', vv)
    # membership chain: V e. PROD0, ( 2nd ` V ) e. prodfrom(1), ...
    cur = tmst_unfold(w, ph, vv)
    t = 'V'
    for k in range(i):
        t2 = '( 2nd ` %s )' % t
        cur = w.s([cur, w.inst('xp2nd')], 'syl', '( %s -> %s e. %s )' % (ph, t2, prodfrom(k + 1)))
        t = t2
    if i < 6:
        cur = w.s([cur, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` %s ) e. %s )' % (ph, t, COMPS[i]))
    w.qed([val, cur], 'eqeltrd', '( %s -> ( %s ` V ) e. %s )' % (ph, ACC[f], CODOM[f]))
    return w.run()


LETS = 'ABCDEFG'


def tuple_tail(i):
    """MK's suffix tuple from component i"""
    return MK(*LETS)[0:0] or _tail(i)


def _tail(i):
    out = LETS[6]
    for x in reversed(LETS[i:6]):
        out = '<. %s , %s >.' % (x, out)
    return out


def tails_mem(w, ph, c):
    """steps: ( ph -> _tail(i) e. prodfrom(i) ) for i = 6 .. 0"""
    mem = {6: c['G e. 2o']}
    for i in range(5, -1, -1):
        ci = c['%s e. %s' % (LETS[i], COMPS[i])]
        mem[i] = w.s([ci, mem[i + 1]], 'opelxpd', '( %s -> %s e. %s )' % (ph, _tail(i), prodfrom(i)))
    return mem


def tmcstmk():
    lab = 'tmcstmk'
    ph = cj(TY7)
    w = W(lab, 'A record literal with typed fields is a machine state (Lean: ` St.mk ` , through ~ df-tmst ).')
    c = Ctx(w, ph, TY7)
    mem = tails_mem(w, ph, c)
    d = w.s([], DFST, 'TMSt = %s' % PROD0)
    w.qed([mem[0], d], 'eleqtrrdi', '( %s -> %s e. TMSt )' % (ph, MK7))
    return w.run()


def tmc_mk(f):
    lab = 'tmc%smk' % f
    i = ORDER.index(f)
    ph = cj(TY7)
    w = W(lab, 'The ` %s ` field of a record literal (Lean: the projection of ` St.equivProd ` on ` St.mk ` ).' % f)
    c = Ctx(w, ph, TY7)
    mem = tails_mem(w, ph, c)
    d = w.s([], DFST, 'TMSt = %s' % PROD0)
    vv = w.s([mem[0], d], 'eleqtrrdi', '( %s -> %s e. TMSt )' % (ph, MK7))
    val, pv = accval(w, ph, f, MK7, vv)
    # the projection chain on the explicit tuple: ( 2nd ` _tail(k) ) = _tail(k+1), ( 1st ` _tail(i) ) = LETS[i]
    chain = None
    cur_t = MK7
    for k in range(i):
        ak = c['%s e. %s' % (LETS[k], COMPS[k])]
        tk = mem[k + 1]
        st = w.s([ak, tk], 'op2ndd' if False else 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, LETS[k], COMPS[k], _tail(k + 1), prodfrom(k + 1)))
        st2 = w.s([st, w.inst('op2ndg')], 'syl', '( %s -> ( 2nd ` %s ) = %s )' % (ph, _tail(k), _tail(k + 1)))
        if chain is None:
            chain = st2
        else:
            # chain : proj_k(MK7) = _tail(k) ; lift through 2nd
            chain = w.s([chain], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, cur_t, _tail(k)))
            chain = w.s([chain, st2], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (ph, cur_t, _tail(k + 1)))
        cur_t = '( 2nd ` %s )' % cur_t
    if i < 6:
        ai = c['%s e. %s' % (LETS[i], COMPS[i])]
        ti = mem[i + 1]
        st = w.s([ai, ti], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, LETS[i], COMPS[i], _tail(i + 1), prodfrom(i + 1)))
        st1 = w.s([st, w.inst('op1stg')], 'syl', '( %s -> ( 1st ` %s ) = %s )' % (ph, _tail(i), LETS[i]))
        if chain is None:
            fin = st1
        else:
            ch2 = w.s([chain], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, cur_t, _tail(i)))
            fin = w.s([ch2, st1], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ph, cur_t, LETS[i]))
    else:
        fin = chain      # ( 2nd ` ... ) = G
    w.qed([val, fin], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, ACC[f], MK7, LETS[i]))
    return w.run()


if __name__ == '__main__':
    for f in ORDER:
        if want('tmc%scl' % f): tmc_cl(f)
    if want('tmcstmk'): tmcstmk()
    for f in ORDER:
        if want('tmc%smk' % f): tmc_mk(f)
