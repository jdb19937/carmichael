"""Sortie T21a: numerals of the grid (t21e272: e <_ 68/25; t21e9: exp(-9/200) <_ 200/209)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
import num
import lin
import cl as _cl
lin.FASTPATH = True
from tm import W
from t21alib import ap as ap_


def gen_e272():
    w = W('t21e272', 'Euler\'s number is at most ` 68 / 25 ` : ` exp 1 = 1 + 1 + 1 / 2 + 1 / 6 + ` tail, the tail at most ` 5 / 96 ` ( ~ ef4p , ~ eftlub ; Lean ` Real.exp_one_lt_d9 ` in ` grid_geom ` ).')
    st = lambda h, r, f: w.s(h, r, '( T. -> %s )' % f)
    F = '( n e. NN0 |-> ( ( 1 ^ n ) / ( ! ` n ) ) )'
    G = '( n e. NN0 |-> ( ( ( abs ` 1 ) ^ n ) / ( ! ` n ) ) )'
    H = '( n e. NN0 |-> ( ( ( ( abs ` 1 ) ^ 4 ) / ( ! ` 4 ) ) x. ( ( 1 / ( 4 + 1 ) ) ^ n ) ) )'
    TL = 'sum_ k e. ( ZZ>= ` 4 ) ( %s ` k )' % F
    P = '( ( ( 1 + 1 ) + ( ( 1 ^ 2 ) / 2 ) ) + ( ( 1 ^ 3 ) / 6 ) )'
    PL = '( ( ( 1 + 1 ) + ( 1 / 2 ) ) + ( 1 / 6 ) )'
    eF = w.s([], 'eqid', '%s = %s' % (F, F))
    eG = w.s([], 'eqid', '%s = %s' % (G, G))
    eH = w.s([], 'eqid', '%s = %s' % (H, H))
    c1 = w.s([], 'ax-1cn', '1 e. CC')
    ef = w.s([c1, w.s([eF], 'ef4p', '( 1 e. CC -> ( exp ` 1 ) = ( %s + %s ) )' % (P, TL))], 'ax-mp', '( exp ` 1 ) = ( %s + %s )' % (P, TL))
    s2 = w.s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'oveq1i', '( ( 1 ^ 2 ) / 2 ) = ( 1 / 2 )')
    one3 = w.s([w.s([], '3z', '3 e. ZZ'), w.s([], '1exp', '( 3 e. ZZ -> ( 1 ^ 3 ) = 1 )')], 'ax-mp', '( 1 ^ 3 ) = 1')
    s3 = w.s([one3], 'oveq1i', '( ( 1 ^ 3 ) / 6 ) = ( 1 / 6 )')
    pe = w.s([w.s([s2], 'oveq2i', '( ( 1 + 1 ) + ( ( 1 ^ 2 ) / 2 ) ) = ( ( 1 + 1 ) + ( 1 / 2 ) )'), s3], 'oveq12i', '%s = %s' % (P, PL))
    ef2 = w.s([ef, w.s([pe], 'oveq1i', '( %s + %s ) = ( %s + %s )' % (P, TL, PL, TL))], 'eqtri', '( exp ` 1 ) = ( %s + %s )' % (PL, TL))
    ef3 = st([ef2], 'a1i', '( exp ` 1 ) = ( %s + %s )' % (PL, TL))
    tlr = st([w.s([w.s([], '1re', '1 e. RR'), w.s([], '4nn0', '4 e. NN0'), w.s([eF], 'reeftlcl', '( ( 1 e. RR /\\ 4 e. NN0 ) -> %s e. RR )' % TL)], 'mp2an', '%s e. RR' % TL)], 'a1i', '%s e. RR' % TL)
    m4 = st([w.s([], '4nn', '4 e. NN')], 'a1i', '4 e. NN')
    c1t = st([c1], 'a1i', '1 e. CC')
    a1 = st([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1'), w.s([], '1le1', '1 <_ 1')], 'eqbrtri', '( abs ` 1 ) <_ 1')], 'a1i', '( abs ` 1 ) <_ 1')
    B = '( ( ( abs ` 1 ) ^ 4 ) x. ( ( 4 + 1 ) / ( ( ! ` 4 ) x. 4 ) ) )'
    ub = w.s([eF, eG, eH, m4, c1t, a1], 'eftlub', '( T. -> ( abs ` %s ) <_ %s )' % (TL, B))
    e1 = w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'oveq1i', '( ( abs ` 1 ) ^ 4 ) = ( 1 ^ 4 )')
    e2 = w.s([w.s([], '4z', '4 e. ZZ'), w.s([], '1exp', '( 4 e. ZZ -> ( 1 ^ 4 ) = 1 )')], 'ax-mp', '( 1 ^ 4 ) = 1')
    e3 = w.s([e1, e2], 'eqtri', '( ( abs ` 1 ) ^ 4 ) = 1')
    f1 = w.s([w.s([], 'fac4', '( ! ` 4 ) = ; 2 4')], 'oveq1i', '( ( ! ` 4 ) x. 4 ) = ( ; 2 4 x. 4 )')
    f3 = w.s([f1, num.mul_nat(w, 24, 4)], 'eqtri', '( ( ! ` 4 ) x. 4 ) = ; 9 6')
    f4 = w.s([w.s([], '4p1e5', '( 4 + 1 ) = 5'), f3], 'oveq12i', '( ( 4 + 1 ) / ( ( ! ` 4 ) x. 4 ) ) = ( 5 / ; 9 6 )')
    f5 = w.s([e3, f4], 'oveq12i', '%s = ( 1 x. ( 5 / ; 9 6 ) )' % B)
    f6 = w.s([f5, w.s([num.cc(w, '( 5 / ; 9 6 )')], 'mullidi', '( 1 x. ( 5 / ; 9 6 ) ) = ( 5 / ; 9 6 )')], 'eqtri', '%s = ( 5 / ; 9 6 )' % B)
    ub2 = st([ub, st([f6], 'a1i', '%s = ( 5 / ; 9 6 )' % B)], 'breqtrd', '( abs ` %s ) <_ ( 5 / ; 9 6 )' % TL)
    le = st([tlr], 'leabsd', '%s <_ ( abs ` %s )' % (TL, TL))
    ab = st([st([tlr], 'recnd', '%s e. CC' % TL)], 'abscld', '( abs ` %s ) e. RR' % TL)
    er = st([st([], '1red', '1 e. RR')], 'reefcld', '( exp ` 1 ) e. RR')
    c = _cl.Closure(w, 'T.', {})
    c.leaf(TL, 'RR', tlr); c.leaf('( abs ` %s )' % TL, 'RR', ab); c.leaf('( exp ` 1 )', 'RR', er)
    fin = lin.linarith(w, 'T.', [ef3, ub2, le], '( exp ` 1 ) <_ ( ; 6 8 / ; 2 5 )', closure=c)
    w.qed([fin], 'mptru', S['t21e272'])
    return w.run()


def gen_e9():
    w = W('t21e9', '` exp ( - 9 / 200 ) <_ 200 / 209 ` ( ~ efgt1p ; Lean ` one_div_one_sub_exp_le ` ).')
    st = lambda h, r, f: w.s(h, r, '( T. -> %s )' % f)
    A = F9200
    ap = st([num.rp(w, A)], 'a1i', '%s e. RR+' % A)
    gt = ap_(w, 'T.', [ap], 'efgt1p', '( 1 + %s ) < ( exp ` %s )' % (A, A))
    ar = st([ap], 'rpred', '%s e. RR' % A)
    ex = st([ar], 'reefcld', '( exp ` %s ) e. RR' % A)
    exp_ = st([ar], 'rpefcld', '( exp ` %s ) e. RR+' % A)
    q = '( ; ; 2 0 9 / ; ; 2 0 0 )'
    c = _cl.Closure(w, 'T.', {})
    c.leaf('( exp ` %s )' % A, 'RR', ex)
    le = lin.linarith(w, 'T.', [gt], '%s <_ ( exp ` %s )' % (q, A), closure=c)
    qp = st([num.rp(w, q)], 'a1i', '%s e. RR+' % q)
    rec = st([qp, exp_], 'lerecd',
             '( %s <_ ( exp ` %s ) <-> ( 1 / ( exp ` %s ) ) <_ ( 1 / %s ) )' % (q, A, A, q))
    r2 = st([le, rec], 'mpbid', '( 1 / ( exp ` %s ) ) <_ ( 1 / %s )' % (A, q))
    en = st([st([ar], 'recnd', '%s e. CC' % A), w.inst('efneg')], 'syl', '( exp ` -u %s ) = ( 1 / ( exp ` %s ) )' % (A, A))
    rq = st([num.cc(w, '; ; 2 0 9') and st([num.cc(w, '; ; 2 0 9')], 'a1i', '; ; 2 0 9 e. CC'), st([num.cc(w, '; ; 2 0 0')], 'a1i', '; ; 2 0 0 e. CC'),
             st([num.ne0_nat(w, 209)], 'a1i', '; ; 2 0 9 =/= 0'), st([num.ne0_nat(w, 200)], 'a1i', '; ; 2 0 0 =/= 0')], 'recdivd', '( 1 / %s ) = ( ; ; 2 0 0 / ; ; 2 0 9 )' % q)
    fin = st([st([en, r2], 'eqbrtrd', '( exp ` -u %s ) <_ ( 1 / %s )' % (A, q)), rq], 'breqtrd', '( exp ` -u %s ) <_ ( ; ; 2 0 0 / ; ; 2 0 9 )' % A)
    w.qed([fin], 'mptru', S['t21e9'])
    return w.run()


if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21e272', gen_e272), ('t21e9', gen_e9)]:
        if not only or lab in only:
            f()
