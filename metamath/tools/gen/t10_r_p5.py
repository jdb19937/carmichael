"""T10: pow5F at the machine (Lean ` pow5F_le_B ` ): four ` mulC ` s on copies of ` L ` (stack 3) leave ` L ^ 5 ` on 6.

    MM_DB=sorties/t10.mm python3 tools/gen/t10_r_p5.py tmip5b
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq, powexp
from cl import Closure
from t10_e_doa import ex_, lift_from
from t10_n_rgf import tmbn

SEL = sys.argv[1:]
LM = FRAGS['p5'].lmap()


def mul_lt(w, ph, a, b, n, m, an, bn, nn, mn, alt, blt):
    """( ph -> ( a x. b ) < ( 2 ^ ( n + m ) ) ) from a < 2 ^ n , b < 2 ^ m"""
    s = w.s
    r = lambda x, xn: s([xn], 'nn0red', '( %s -> %s e. RR )' % (ph, x))
    pn = s([closed(w, ph, '2nn0', '2 e. NN0'), nn, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, n))
    pm = s([closed(w, ph, '2nn0', '2 e. NN0'), mn, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, m))
    j1 = s([s([r(a, an), r('( 2 ^ %s )' % n, pn)], 'jca', '( %s -> ( %s e. RR /\\ ( 2 ^ %s ) e. RR ) )' % (ph, a, n)),
            s([s([an], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, a)), alt], 'jca', '( %s -> ( 0 <_ %s /\\ %s < ( 2 ^ %s ) ) )' % (ph, a, a, n))], 'jca',
           '( %s -> ( ( %s e. RR /\\ ( 2 ^ %s ) e. RR ) /\\ ( 0 <_ %s /\\ %s < ( 2 ^ %s ) ) ) )' % (ph, a, n, a, a, n))
    j2 = s([s([r(b, bn), r('( 2 ^ %s )' % m, pm)], 'jca', '( %s -> ( %s e. RR /\\ ( 2 ^ %s ) e. RR ) )' % (ph, b, m)),
            s([s([bn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, b)), blt], 'jca', '( %s -> ( 0 <_ %s /\\ %s < ( 2 ^ %s ) ) )' % (ph, b, b, m))], 'jca',
           '( %s -> ( ( %s e. RR /\\ ( 2 ^ %s ) e. RR ) /\\ ( 0 <_ %s /\\ %s < ( 2 ^ %s ) ) ) )' % (ph, b, m, b, b, m))
    lt = s([j1, j2, w.inst('ltmul12a')], 'syl2anc', '( %s -> ( %s x. %s ) < ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (ph, a, b, n, m))
    ea = s([closed(w, ph, '2cn', '2 e. CC'), nn, mn, w.inst('expadd')], 'syl3anc', '( %s -> ( 2 ^ ( %s + %s ) ) = ( ( 2 ^ %s ) x. ( 2 ^ %s ) ) )' % (ph, n, m, n, m))
    return s([lt, ea], 'breqtrrd', '( %s -> ( %s x. %s ) < ( 2 ^ ( %s + %s ) ) )' % (ph, a, b, n, m))


def tmip5b():
    lab = 'tmip5b'
    T = numtree(TREE_P5)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` pow5F_le_B ` at the machine: ` dup ; dup ; mulC ; dup ; mulC ; dup ; mulC ; dup ; mulC ` on copies of '
               '` L ` (stack 3) push ` L ^ 5 ` on stack 6 (~ tmimulb ), every other stack restored, within ` 9 B ( 4 m ) ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    ln, nn = c0['L e. NN0'], c0['N e. NN0']
    eqs = {'3': (EWg('L', 'X'), ewg_(w, ph, 'L', ln, 'X', c0[WG('X')]))}
    B = Base(w, ph, T, N8, 'p5', eqs)
    c, mk = B.c, B.mk
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    llt = c['L < ( 2 ^ N )']
    L2, L3, L4 = '( L x. L )', '( ( L x. L ) x. L )', '( ( ( L x. L ) x. L ) x. L )'
    L5 = '( %s x. L )' % L4
    N2, N3, N4 = '( N + N )', '( ( N + N ) + N )', '( ( ( N + N ) + N ) + N )'
    nsum = lambda x, xn: s([xn, nn, w.inst('nn0addcl')], 'syl2anc', '( %s -> ( %s + N ) e. NN0 )' % (ph, x))
    n2n = nsum('N', nn)
    n3n = nsum(N2, n2n)
    n4n = nsum(N3, n3n)
    mul = lambda a, an: s([an, ln, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( %s x. L ) e. NN0 )' % (ph, a))
    l2n = mul('L', ln)
    l3n = mul(L2, l2n)
    l4n = mul(L3, l3n)
    l5n = mul(L4, l4n)
    l2lt = mul_lt(w, ph, 'L', 'L', 'N', 'N', ln, ln, nn, nn, llt, llt)
    l3lt = mul_lt(w, ph, L2, 'L', N2, 'N', l2n, ln, n2n, nn, l2lt, llt)
    l4lt = mul_lt(w, ph, L3, 'L', N3, 'N', l3n, ln, n3n, nn, l3lt, llt)
    cl = Closure(w, ph, {'N': ('NN0', nn), 'L': ('NN0', ln)})
    def lt_up(x, xn, xlt, n_, nnn):
        """x < 2 ^ n_ from x < 2 ^ N"""
        le = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'),
                s([s([s([nn], 'nn0zd', '( %s -> N e. ZZ )' % ph), s([nnn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, n_)),
                      linarith(w, ph, [cl.ge0('N')], 'N <_ %s' % n_, closure=cl)], '3jca', '( %s -> ( N e. ZZ /\\ %s e. ZZ /\\ N <_ %s ) )' % (ph, n_, n_)),
                   s([], 'eluz2', '( %s e. ( ZZ>= ` N ) <-> ( N e. ZZ /\\ %s e. ZZ /\\ N <_ %s ) )' % (n_, n_, n_))], 'sylibr', '( %s -> %s e. ( ZZ>= ` N ) )' % (ph, n_)),
                w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ N ) <_ ( 2 ^ %s ) )' % (ph, n_))
        pr = lambda e_, en_: s([s([closed(w, ph, '2nn0', '2 e. NN0'), en_, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, e_))], 'nn0red',
                               '( %s -> ( 2 ^ %s ) e. RR )' % (ph, e_))
        return s([s([xn], 'nn0red', '( %s -> %s e. RR )' % (ph, x)), pr('N', nn), pr(n_, nnn), xlt, le], 'ltletrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, x, n_))
    E5 = EWg('L', DK(5))
    def dup3(j, P, Ex, tgt):
        et = EWg('L', DK(tgt))
        B.call(R, 'tmidupb', {'K': '3', 'J': str(tgt), 'I': str(j), 'F': 'L', 'N': 'N', 'X': 'X', 'P': P, 'E': Ex}, {},
               [(str(tgt), et, B.g(et, ewg_(w, ph, 'L', ln, DK(tgt), g(str(tgt)))))])
    dup3(6, PL('P', 0), LM['Y2'], 5)
    dup3(5, PL('P', 1), LM['Y3'], 6)
    # mulC 5 6 7 2 4
    def mulc(x, y, wv, F, G, Fn, Gn, Nb, Nbn, Flt, Glt, P, Ex):
        prod = '( %s x. %s )' % (F, G)
        pn_ = s([Fn, Gn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, prod))
        ew = EWg(prod, DK(wv))
        B.call(R, 'tmimulb', {'K': str(x), 'J': str(y), 'I': str(wv), "I'": '2', 'I"': '4', 'F': F, 'G': G, 'N': Nb, 'X': DK(x), 'Y': DK(y), 'P': P, 'E': Ex},
               {'%s e. NN0' % F: Fn, '%s e. NN0' % G: Gn, '%s e. NN0' % Nb: Nbn, '%s < ( 2 ^ %s )' % (F, Nb): Flt, '%s < ( 2 ^ %s )' % (G, Nb): Glt},
               [(str(wv), ew, B.g(ew, ewg_(w, ph, prod, pn_, DK(wv), g(str(wv))))), (str(x), DK(x), g(str(x))), (str(y), DK(y), g(str(y)))])
    mulc(5, 6, 7, 'L', 'L', ln, ln, 'N', nn, llt, llt, PL('P', 2), LM['Y4'])
    dup3(6, PL('P', 3), LM['Y5'], 5)
    mulc(7, 5, 6, L2, 'L', l2n, ln, N2, n2n, l2lt, lt_up('L', ln, llt, N2, n2n), PL('P', 4), LM['Y6'])
    dup3(7, PL('P', 5), LM['Y7'], 5)
    mulc(6, 5, 7, L3, 'L', l3n, ln, N3, n3n, l3lt, lt_up('L', ln, llt, N3, n3n), PL('P', 6), LM['Y8'])
    dup3(6, PL('P', 7), LM['Y9'], 5)
    mulc(7, 5, 6, L4, 'L', l4n, ln, N4, n4n, l4lt, lt_up('L', ln, llt, N4, n4n), PL('P', 8), 'E')
    cur, out = R.normalize(N8)
    assert out == [('6', EWg(L5, DK(6)))], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    pe, prod = powexp(w, ph, 'L', 5, cl)
    assert prod == L5, prod
    le5 = s([pe], 'eqcomd', '( %s -> %s = ( L ^ 5 ) )' % (ph, L5))
    Dc = triple_D(D)
    rf, xf = w.rewrite(Dc, {L5: ('( L ^ 5 )', le5)}, ph)
    assert xf == UP('D', '6', EWg('( L ^ 5 )', DK(6))), xf
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, rf, Dc, xf))
    # the bound
    N4B = '( 4 x. N )'
    n4b = s([closed(w, ph, '4nn0', '4 e. NN0'), nn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, N4B))
    TB4 = '( TMB ` %s )' % N4B
    hs = []
    for x_, xn_ in (('N', nn), (N2, n2n), (N3, n3n), (N4, n4n)):
        tb = tmbn(w, ph, x_, xn_)
        cl.leaf('( TMB ` %s )' % x_, 'NN0', tb)
        hs.append(s([xn_, n4b, linarith(w, ph, [cl.ge0('N')], '%s <_ %s' % (x_, N4B), closure=cl), w.inst('tmbmono')], 'syl3anc',
                    '( %s -> ( TMB ` %s ) <_ %s )' % (ph, x_, TB4)))
    cl.leaf(TB4, 'NN0', tmbn(w, ph, N4B, n4b))
    BND = '( 9 x. %s )' % TB4
    le = linarith(w, ph, hs, '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
