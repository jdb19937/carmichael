"""T15 (d): support lemmas for the kind theorems."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
import lin
lin.FASTPATH = True
from lin import linarith

D30 = '; 3 0'
HL = 'A. v e. Word A ( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. L )'
HM = 'A. v e. Word A ( ( ( # ` v ) <_ ; 3 0 /\\ ( R TMWalk v ) e. S ) -> ( M ` ( TMLab ` v ) ) = ( R TMWalk v ) )'


def d30(w, ante):
    a = w.s([w.s([], '3nn0', '3 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 3 0 e. NN0')
    b = w.s([a], 'nn0rei', '; 3 0 e. RR')
    return a1(w, ante, b, '; 3 0 e. RR')


def t15ap():
    w = W('t15ap', 'One application of an address label: value, address typing, remaining depth.')
    ph = '( ( X e. Word A /\\ ( ( # ` X ) + S ) <_ ; 3 0 ) /\\ ( ( N e. NN0 /\\ ( N + 1 ) = S ) /\\ ( I e. A /\\ A C_ NN0 ) ) )'
    xw = w.s([], 'simpll', '( %s -> X e. Word A )' % ph)
    le = w.s([], 'simplr', '( %s -> ( ( # ` X ) + S ) <_ ; 3 0 )' % ph)
    nn = w.s([], 'simprll', '( %s -> N e. NN0 )' % ph)
    eq = w.s([], 'simprlr', '( %s -> ( N + 1 ) = S )' % ph)
    ia = w.s([], 'simprrl', '( %s -> I e. A )' % ph)
    ss = w.s([], 'simprrr', '( %s -> A C_ NN0 )' % ph)
    sw = w.s([ss, w.inst('sswrd')], 'syl', '( %s -> Word A C_ Word NN0 )' % ph)
    xw0 = w.s([sw, xw], 'sseldd', '( %s -> X e. Word NN0 )' % ph)
    i0 = w.s([ss, ia], 'sseldd', '( %s -> I e. NN0 )' % ph)
    xn = w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` X ) e. NN0 )' % ph)
    xr = w.s([xn], 'nn0red', '( %s -> ( # ` X ) e. RR )' % ph)
    nr = w.s([nn], 'nn0red', '( %s -> N e. RR )' % ph)
    n0 = w.s([nn], 'nn0ge0d', '( %s -> 0 <_ N )' % ph)
    one = a1(w, ph, w.s([], '1re', '1 e. RR'), '1 e. RR')
    sr0 = w.s([nr, one], 'readdcld', '( %s -> ( N + 1 ) e. RR )' % ph)
    sr = w.s([eq, sr0], 'eqeltrrd', '( %s -> S e. RR )' % ph)
    lt = linarith(w, ph, [le, eq, n0], '( # ` X ) < ; 3 0', leaves={'( # ` X )': xr, 'N': nr, 'S': sr})
    c1 = w.s([xw0, lt, i0, w.inst('tmlabap')], 'syl3anc', '( %s -> ( ( TMLab ` X ) ` I ) = ( TMLab ` ( X ++ <" I "> ) ) )' % ph)
    c2 = w.s([xw, ia, w.inst('ccatws1cl')], 'syl2anc', '( %s -> ( X ++ <" I "> ) e. Word A )' % ph)
    ln = w.s([xw, w.inst('ccatws1len')], 'syl', '( %s -> ( # ` ( X ++ <" I "> ) ) = ( ( # ` X ) + 1 ) )' % ph)
    ln2 = w.s([ln], 'oveq1d', '( %s -> ( ( # ` ( X ++ <" I "> ) ) + N ) = ( ( ( # ` X ) + 1 ) + N ) )' % ph)
    l3 = linarith(w, ph, [le, eq], '( ( ( # ` X ) + 1 ) + N ) <_ ; 3 0', leaves={'( # ` X )': xr, 'N': nr, 'S': sr})
    c3 = w.s([ln2, l3], 'eqbrtrd', '( %s -> ( ( # ` ( X ++ <" I "> ) ) + N ) <_ ; 3 0 )' % ph)
    w.qed([c1, c2, c3], '3jca', '( %s -> ( ( ( TMLab ` X ) ` I ) = ( TMLab ` ( X ++ <" I "> ) ) /\\ ( X ++ <" I "> ) e. Word A /\\ ( ( # ` ( X ++ <" I "> ) ) + N ) <_ ; 3 0 ) )' % ph)
    return w


def inst_all(w, ante, allstep, body, T, mem):
    """from ( ante -> A. v e. Word A body ) and ( ante -> T e. Word A ) get ( ante -> body[v:=T] )"""
    eq = 'v = %s' % T
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, new = w.wcongr(body, {'v': T}, eq, {'v': idx})
    r = w.s([st], 'rspcv', '( %s e. Word A -> ( A. v e. Word A %s -> %s ) )' % (T, body, new))
    return w.s([mem, allstep, r], 'sylc', '( %s -> %s )' % (ante, new)), new


def t15own():
    w = W('t15own', 'An installed own label: its statement and its membership in the label set.')
    ph = '( ( %s /\\ %s ) /\\ ( X e. Word A /\\ ( ( # ` X ) + N ) <_ ; 3 0 /\\ N e. NN0 ) /\\ ( ( R TMWalk X ) = Y /\\ Y e. S ) )' % (HL, HM)
    hl = w.s([], 'simp1l', '( %s -> %s )' % (ph, HL))
    hm = w.s([], 'simp1r', '( %s -> %s )' % (ph, HM))
    xw = w.s([], 'simp21', '( %s -> X e. Word A )' % ph)
    le = w.s([], 'simp22', '( %s -> ( ( # ` X ) + N ) <_ ; 3 0 )' % ph)
    nn = w.s([], 'simp23', '( %s -> N e. NN0 )' % ph)
    wy = w.s([], 'simp3l', '( %s -> ( R TMWalk X ) = Y )' % ph)
    ys = w.s([], 'simp3r', '( %s -> Y e. S )' % ph)
    xn = w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` X ) e. NN0 )' % ph)
    xr = w.s([xn], 'nn0red', '( %s -> ( # ` X ) e. RR )' % ph)
    nr = w.s([nn], 'nn0red', '( %s -> N e. RR )' % ph)
    n0 = w.s([nn], 'nn0ge0d', '( %s -> 0 <_ N )' % ph)
    l30 = linarith(w, ph, [le, n0], '( # ` X ) <_ ; 3 0', leaves={'( # ` X )': xr, 'N': nr})
    ws = w.s([wy, ys], 'eqeltrd', '( %s -> ( R TMWalk X ) e. S )' % ph)
    m1, f1 = inst_all(w, ph, hm, '( ( ( # ` v ) <_ ; 3 0 /\\ ( R TMWalk v ) e. S ) -> ( M ` ( TMLab ` v ) ) = ( R TMWalk v ) )', 'X', xw)
    j = w.s([l30, ws], 'jca', '( %s -> ( ( # ` X ) <_ ; 3 0 /\\ ( R TMWalk X ) e. S ) )' % ph)
    m2 = w.s([j, m1], 'mpd', '( %s -> ( M ` ( TMLab ` X ) ) = ( R TMWalk X ) )' % ph)
    m3 = w.s([m2, wy], 'eqtrd', '( %s -> ( M ` ( TMLab ` X ) ) = Y )' % ph)
    l1, f2 = inst_all(w, ph, hl, '( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. L )', 'X', xw)
    l2 = w.s([l30, l1], 'mpd', '( %s -> ( TMLab ` X ) e. L )' % ph)
    w.qed([m3, l2], 'jca', '( %s -> ( ( M ` ( TMLab ` X ) ) = Y /\\ ( TMLab ` X ) e. L ) )' % ph)
    return w


def t15lab():
    w = W('t15lab', 'An address label within the depth bound is in the label set.')
    ph = '( %s /\\ ( X e. Word A /\\ ( ( # ` X ) + N ) <_ ; 3 0 /\\ N e. NN0 ) )' % HL
    hl = w.s([], 'simpl', '( %s -> %s )' % (ph, HL))
    xw = w.s([], 'simpr1', '( %s -> X e. Word A )' % ph)
    le = w.s([], 'simpr2', '( %s -> ( ( # ` X ) + N ) <_ ; 3 0 )' % ph)
    nn = w.s([], 'simpr3', '( %s -> N e. NN0 )' % ph)
    xn = w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` X ) e. NN0 )' % ph)
    xr = w.s([xn], 'nn0red', '( %s -> ( # ` X ) e. RR )' % ph)
    nr = w.s([nn], 'nn0red', '( %s -> N e. RR )' % ph)
    n0 = w.s([nn], 'nn0ge0d', '( %s -> 0 <_ N )' % ph)
    l30 = linarith(w, ph, [le, n0], '( # ` X ) <_ ; 3 0', leaves={'( # ` X )': xr, 'N': nr})
    l1, f2 = inst_all(w, ph, hl, '( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. L )', 'X', xw)
    w.qed([l30, l1], 'mpd', '( %s -> ( TMLab ` X ) e. L )' % ph)
    return w


def t15wk():
    w = W('t15wk', 'Weaken a remaining-depth bound.')
    ph = '( ( X e. Word A /\\ ( ( # ` X ) + S ) <_ ; 3 0 ) /\\ ( N e. RR /\\ S e. RR /\\ N <_ S ) )'
    xw = w.s([], 'simpll', '( %s -> X e. Word A )' % ph)
    le = w.s([], 'simplr', '( %s -> ( ( # ` X ) + S ) <_ ; 3 0 )' % ph)
    nr = w.s([], 'simpr1', '( %s -> N e. RR )' % ph)
    sr = w.s([], 'simpr2', '( %s -> S e. RR )' % ph)
    ns = w.s([], 'simpr3', '( %s -> N <_ S )' % ph)
    xn = w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` X ) e. NN0 )' % ph)
    xr = w.s([xn], 'nn0red', '( %s -> ( # ` X ) e. RR )' % ph)
    linarith(w, ph, [le, ns], '( ( # ` X ) + N ) <_ ; 3 0', leaves={'( # ` X )': xr, 'N': nr, 'S': sr}, name='qed')
    return w


G1 = '( 1st ` ( 1st ` T ) )'


def t15kdom():
    w = W('t15kdom', 'A stack index of the eight-stack machine.')
    ph = '( %s = TMGam /\\ K e. ( 0 ..^ 8 ) )' % G1
    g = w.s([], 'simpl', '( %s -> %s = TMGam )' % (ph, G1))
    k = w.s([], 'simpr', '( %s -> K e. ( 0 ..^ 8 ) )' % ph)
    fn = w.s([], 'tmgamfn', 'TMGam Fn ( 0 ..^ 8 )')
    dm = w.s([fn, w.inst('fndm')], 'ax-mp', 'dom TMGam = ( 0 ..^ 8 )')
    d1 = w.s([g], 'dmeqd', '( %s -> dom %s = dom TMGam )' % (ph, G1))
    d2 = w.s([d1, dm], 'eqtrdi', '( %s -> dom %s = ( 0 ..^ 8 ) )' % (ph, G1))
    a = w.s([k, d2], 'eleqtrrd', '( %s -> K e. dom %s )' % (ph, G1))
    b1 = w.s([g], 'fveq1d', '( %s -> ( %s ` K ) = ( TMGam ` K ) )' % (ph, G1))
    b2 = w.s([k, w.inst('tmgamfv')], 'syl', '( %s -> ( TMGam ` K ) = Gamma\' )' % ph)
    b = w.s([b1, b2], 'eqtrd', '( %s -> ( %s ` K ) = Gamma\' )' % (ph, G1))
    w.qed([a, b], 'jca', '( %s -> ( K e. dom %s /\\ ( %s ` K ) = Gamma\' ) )' % (ph, G1, G1))
    return w


def t15cst():
    w = W('t15cst', 'A constant function on the states of T.')
    ph = '( B e. V /\\ Z e. B )'
    bv = w.s([], 'simpl', '( %s -> B e. V )' % ph)
    z = w.s([], 'simpr', '( %s -> Z e. B )' % ph)
    f = w.s([z, w.inst('fconst6g')], 'syl', '( %s -> ( ( 2nd ` T ) X. { Z } ) : ( 2nd ` T ) --> B )' % ph)
    sv = a1(w, ph, w.s([], 'fvex', '( 2nd ` T ) e. _V'), '( 2nd ` T ) e. _V')
    e = w.s([bv, sv, w.inst('elmapg')], 'syl2anc', '( %s -> ( ( ( 2nd ` T ) X. { Z } ) e. ( B ^m ( 2nd ` T ) ) <-> ( ( 2nd ` T ) X. { Z } ) : ( 2nd ` T ) --> B ) )' % ph)
    w.qed([f, e], 'mpbird', '( %s -> ( ( 2nd ` T ) X. { Z } ) e. ( B ^m ( 2nd ` T ) ) )' % ph)
    return w


def t15rd():
    w = W('t15rd', 'A read handler of the concrete machine has the type pop and peek require.')
    ph = '( ( ( 2nd ` T ) = TMSt /\\ ( %s ` K ) = Gamma\' ) /\\ F e. ( TMSt ^m ( TMSt X. ( Gamma\' |_| 1o ) ) ) )' % G1
    s = w.s([], 'simpll', '( %s -> ( 2nd ` T ) = TMSt )' % ph)
    g = w.s([], 'simplr', '( %s -> ( %s ` K ) = Gamma\' )' % (ph, G1))
    f = w.s([], 'simpr', '( %s -> F e. ( TMSt ^m ( TMSt X. ( Gamma\' |_| 1o ) ) ) )' % ph)
    g2 = w.s([g, w.inst('djueq1')], 'syl', '( %s -> ( ( %s ` K ) |_| 1o ) = ( Gamma\' |_| 1o ) )' % (ph, G1))
    x = w.s([s, g2], 'xpeq12d', '( %s -> ( ( 2nd ` T ) X. ( ( %s ` K ) |_| 1o ) ) = ( TMSt X. ( Gamma\' |_| 1o ) ) )' % (ph, G1))
    m = w.s([s, x], 'oveq12d', '( %s -> ( ( 2nd ` T ) ^m ( ( 2nd ` T ) X. ( ( %s ` K ) |_| 1o ) ) ) = ( TMSt ^m ( TMSt X. ( Gamma\' |_| 1o ) ) ) )' % (ph, G1))
    w.qed([f, m], 'eleqtrrd', '( %s -> F e. ( ( 2nd ` T ) ^m ( ( 2nd ` T ) X. ( ( %s ` K ) |_| 1o ) ) ) )' % (ph, G1))
    return w


GENS = {'t15ap': t15ap, 't15own': t15own, 't15lab': t15lab, 't15wk': t15wk, 't15kdom': t15kdom,
        't15cst': t15cst, 't15rd': t15rd}

if __name__ == '__main__':
    for lab in sys.argv[1:] or list(GENS):
        GENS[lab]().run()
