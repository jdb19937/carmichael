"""T12: failAll at the machine (Lean ` failAll_runs ` ): eight clears (~ tm2fclr ) and ` pushSym 1 comma ` leave
` Frag.initStacks 1 [comma] ` .

    MM_DB=sorties/t12.mm python3 tools/gen/t12_d_fal.py tmifal
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t9_f_exs import clear_extra
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]


def num_ne(w, ph, a, b):
    """( ph -> -. a = b ) for distinct numerals 0 ... 9"""
    s = w.s
    lo, hi = min(int(a), int(b)), max(int(a), int(b))
    lt = s([], '%dlt%d' % (lo, hi) if lo > 0 else ('0lt1' if hi == 1 else '%dpos' % hi), '%d < %d' % (lo, hi))
    ne = s([s([], '%dre' % lo, '%d e. RR' % lo), lt], 'ltneii', '%d =/= %d' % (lo, hi))
    if int(a) == lo:
        n0 = s([ne], 'neii', '-. %s = %s' % (a, b))
    else:
        n0 = s([s([ne], 'necomi', '%s =/= %s' % (a, b))], 'neii', '-. %s = %s' % (a, b))
    return s([n0], 'a1i', '( %s -> -. %s = %s )' % (ph, a, b))


def init_vals(w, ph, mk, k0, W_, wv, ks=N8):
    """( ph -> ( INIT( k0 , W ) ` k ) = W or (/) ) for every k, from wv : ( ph -> W e. _V )"""
    s = w.s
    IN = INIT(k0, W_)
    out = {}
    for k in ks:
        kin = mk['k'][k]['kk']
        v = s([s([mk['geq'], s([kin, wv], 'jca', '( %s -> ( %s e. ( 0 ..^ 8 ) /\\ %s e. _V ) )' % (ph, k, W_))], 'jca',
                 '( %s -> ( ( 1st ` ( 1st ` T ) ) = TMGam /\\ ( %s e. ( 0 ..^ 8 ) /\\ %s e. _V ) ) )' % (ph, k, W_)),
               w.inst('t12ini')], 'syl', '( %s -> ( %s ` %s ) = if ( %s = %s , %s , (/) ) )' % (ph, IN, k, k, k0, W_))
        IFK = 'if ( %s = %s , %s , (/) )' % (k, k0, W_)
        if k == k0:
            e = s([s([s([], 'eqid', '%s = %s' % (k, k))], 'a1i', '( %s -> %s = %s )' % (ph, k, k))], 'iftrued', '( %s -> %s = %s )' % (ph, IFK, W_))
            out[k] = s([v, e], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, IN, k, W_))
        else:
            e = s([num_ne(w, ph, k, k0)], 'iffalsed', '( %s -> %s = (/) )' % (ph, IFK))
            out[k] = s([v, e], 'eqtrd', '( %s -> ( %s ` %s ) = (/) )' % (ph, IN, k))
    return out


_IDX = {}


def idx8(w, ph, k):
    """( ph -> k e. ( 0 ..^ 8 ) ) for a numeral k"""
    s = w.s
    key = (ph, k)
    if key in _IDX:
        return _IDX[key]
    n = int(k)
    kn = s([], '%snn0' % k if n else '0nn0', '%s e. NN0' % k)
    lt = s([], '%dlt8' % n if n else '8pos', '%s < 8' % k)
    e = s([kn, s([], '8nn', '8 e. NN'), lt], 'elfzo0z' if False else '3pm3.2i', '( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 )' % (k, k))
    st = s([e, s([], 'elfzo0', '( %s e. ( 0 ..^ 8 ) <-> ( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 ) )' % (k, k, k))], 'mpbir', '%s e. ( 0 ..^ 8 )' % k)
    _IDX[key] = s([st], 'a1i', '( %s -> %s e. ( 0 ..^ 8 ) )' % (ph, k))
    return _IDX[key]


def to_init(w, ph, B, R, k0, W_, wv, wg, chain_vals, Dc):
    """( ph -> Dc = INIT( k0 , W ) ) from the chain's values chain_vals[k] : ( ph -> ( Dc ` k ) = v_k ) with v_k = W at k0
    and (/) elsewhere (by ~ t12stkeq )"""
    s = w.s
    mk = B.mk
    IN = INIT(k0, W_)
    iv = init_vals(w, ph, mk, k0, W_, wv)
    facts = {}
    for k in N8:
        v = W_ if k == k0 else '(/)'
        facts[k] = s([chain_vals[k], s([iv[k]], 'eqcomd', '( %s -> %s = ( %s ` %s ) )' % (ph, v, IN, k))], 'eqtrd',
                     '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, Dc, k, IN, k))
    # INIT e. ( TM2Stk ` T )
    kd = mk['k'][k0]['kd']
    wgk = s([wg, mk['k'][k0]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, W_, GX(k0)))
    ini = s([mk['tv'], kd, wgk, w.inst('tm2initstk')], 'syl3anc', '( %s -> %s e. ( TM2Stk ` T ) )' % (ph, IN))
    T8 = EQ8_(Dc, IN)
    byt = {'( %s ` %s ) = ( %s ` %s )' % (Dc, k, IN, k): k for k in N8}
    def tree_step(t):
        if isinstance(t, str):
            return facts[byt[t]]
        parts = [tree_step(x) for x in t]
        return s(parts, 'jca' if len(parts) == 2 else '3jca', '( %s -> %s )' % (ph, cj(t)))
    eqs = tree_step(T8)
    a = s([mk['tv'], mk['geq']], 'jca', '( %s -> ( T e. V /\\ ( 1st ` ( 1st ` T ) ) = TMGam ) )' % ph)
    b = s([R.S.memb, ini], 'jca', '( %s -> ( %s e. ( TM2Stk ` T ) /\\ %s e. ( TM2Stk ` T ) ) )' % (ph, Dc, IN))
    ab = s([a, b], 'jca', '( %s -> ( ( T e. V /\\ ( 1st ` ( 1st ` T ) ) = TMGam ) /\\ ( %s e. ( TM2Stk ` T ) /\\ %s e. ( TM2Stk ` T ) ) ) )'
           % (ph, Dc, IN))
    full = s([ab, eqs], 'jca', '( %s -> ( ( ( T e. V /\\ ( 1st ` ( 1st ` T ) ) = TMGam ) /\\ ( %s e. ( TM2Stk ` T ) /\\ %s e. ( TM2Stk ` T ) ) ) /\\ %s ) )'
             % (ph, Dc, IN, cj(T8)))
    return s([full, w.inst('t12stkeq')], 'syl', '( %s -> %s = %s )' % (ph, Dc, IN))


def EQ8_(A, B):
    return ((('( %s ` 0 ) = ( %s ` 0 )' % (A, B), '( %s ` 1 ) = ( %s ` 1 )' % (A, B)),
             ('( %s ` 2 ) = ( %s ` 2 )' % (A, B), '( %s ` 3 ) = ( %s ` 3 )' % (A, B))),
            (('( %s ` 4 ) = ( %s ` 4 )' % (A, B), '( %s ` 5 ) = ( %s ` 5 )' % (A, B)),
             ('( %s ` 6 ) = ( %s ` 6 )' % (A, B), '( %s ` 7 ) = ( %s ` 7 )' % (A, B))))


def tmifal():
    lab = 'tmifal'
    T = numtree(TREE_FAL)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` failAll_runs ` at the machine: wherever ` failAll ` is installed, the eight clears (~ tm2fclr ) '
               'empty every stack and ` pushSym 1 comma ` leaves ` Frag.initStacks 1 [ comma ] ` , within the sum of the '
               'stack lengths plus 9 steps.')
    s = w.s
    B = Base(w, ph, T, N8, 'fal', {})
    c, mk = B.c, B.mk
    LM = FRAGS['fal'].lmap()
    R = B.run()
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    leq = []
    for i, k in enumerate(N8):
        Dcur = R.S.D
        if Dcur != 'D':
            txt, st0, g0 = R.S.vals[k]
            assert txt == DK(k), txt
            leq.append(('( # ` ( %s ` %s ) )' % (Dcur, k), s([st0], 'fveq2d', '( %s -> ( # ` ( %s ` %s ) ) = %s )' % (ph, Dcur, k, LEN(DK(k)))), k))
        ex = clear_extra(w, ph, mk, k)
        B.call(R, 'tm2fclr', {'A': LM['Z%d' % (i + 1)], 'E': LM['Z%d' % (i + 2)], 'K': k, 'F': RDE, 'C': CNDA}, ex,
               [(k, '(/)', wrd0)])
    K2 = '( <" 4 "> ++ (/) )'
    g2 = B.g(K2, wg4(w, ph, '(/)', wrd0))
    B.call(R, 'tm2fpshn', {'A': LM['Z9'], 'E': 'E', 'K': '1', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('1'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['1']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('1')))},
           [('1', K2, g2)])
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    Dc = triple_D(D)
    W1 = COMMA1
    s1 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> %s e. Word Gamma' )" % (ph, W1))
    cr = s([s1, w.inst('ccatrid')], 'syl', '( %s -> %s = %s )' % (ph, K2, W1))
    vals = {}
    for k in N8:
        txt, st, g = R.S.vals[k]
        if k == '1':
            assert txt == K2, txt
            vals[k] = s([st, cr], 'eqtrd', '( %s -> ( %s ` 1 ) = %s )' % (ph, Dc, W1))
        else:
            assert txt == '(/)', (k, txt)
            vals[k] = st
    wv = s([s1], 'elexd', '( %s -> %s e. _V )' % (ph, W1))
    deq = to_init(w, ph, B, R, '1', W1, wv, s1, vals, Dc)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, deq, Dc, INIT('1', W1)))
    cl = Closure(w, ph, {})
    for k in N8:
        cl.leaf(LEN(DK(k)), 'NN0', s([B.S0.vals[k][2], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN(DK(k)))))
    hyps = []
    for atom, eqst, k in leq:
        cl.leaf(atom, 'NN0', s([eqst, cl.mem(LEN(DK(k)), 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, atom)))
        hyps.append(eqst)
    le = linarith(w, ph, hyps, '%s <_ %s' % (n, FALC), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, FALC, cl.mem(FALC, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
