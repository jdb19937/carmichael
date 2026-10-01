"""Sortie KD1: the annulus comparison (kddist)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_dist():
    w = W('kddist', 'Lean ` KDerivDetect.dist_one_le_norm_sub ` : for ` Re Q <_ 1 ` and ` 0 <_ E ` , ` abs ( Q - ( 1 + i T ) ) <_ abs ( ( ( 1 + E ) + i T ) - Q ) ` .')
    A0 = S['kddist'].split(' -> ( abs')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    g1 = s([], 'simpl', '( E e. RR /\\ 0 <_ E /\\ T e. RR )'); g2 = s([], 'simpr', '( Q e. CC /\\ ( Re ` Q ) <_ 1 )')
    er = s([g1], 'simp1d', 'E e. RR'); e0 = s([g1], 'simp2d', '0 <_ E'); tr = s([g1], 'simp3d', 'T e. RR')
    qc = s([g2], 'simpld', 'Q e. CC'); rq = s([g2], 'simprd', '( Re ` Q ) <_ 1')
    ONEt = ONE('T'); SS = S0()
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
    onec = s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % ONEt)
    oe = s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), er], 'readdcld', '( 1 + E ) e. RR')
    s0c = s([s([oe], 'recnd', '( 1 + E ) e. CC'), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SS)
    r1 = s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % ONEt)
    i1 = s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % ONEt)
    r2 = s([oe, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + E )' % SS)
    i2 = s([oe, tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % SS)
    W1 = '( Q - %s )' % ONEt; W2 = '( %s - Q )' % SS
    w1c = s([qc, onec], 'subcld', '%s e. CC' % W1); w2c = s([s0c, qc], 'subcld', '%s e. CC' % W2)
    rw1 = s([qc, onec], 'resubd', '( Re ` %s ) = ( ( Re ` Q ) - ( Re ` %s ) )' % (W1, ONEt))
    iw1 = s([qc, onec], 'imsubd', '( Im ` %s ) = ( ( Im ` Q ) - ( Im ` %s ) )' % (W1, ONEt))
    rw2 = s([s0c, qc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` Q ) )' % (W2, SS))
    iw2 = s([s0c, qc], 'imsubd', '( Im ` %s ) = ( ( Im ` %s ) - ( Im ` Q ) )' % (W2, SS))
    X = '( Re ` Q )'; Y = '( Im ` Q )'
    rw1b = s([rw1, s([r1], 'oveq2d', '( %s - ( Re ` %s ) ) = ( %s - 1 )' % (X, ONEt, X))], 'eqtrd', '( Re ` %s ) = ( %s - 1 )' % (W1, X))
    iw1b = s([iw1, s([i1], 'oveq2d', '( %s - ( Im ` %s ) ) = ( %s - T )' % (Y, ONEt, Y))], 'eqtrd', '( Im ` %s ) = ( %s - T )' % (W1, Y))
    rw2b = s([rw2, s([r2], 'oveq1d', '( ( Re ` %s ) - %s ) = ( ( 1 + E ) - %s )' % (SS, X, X))], 'eqtrd', '( Re ` %s ) = ( ( 1 + E ) - %s )' % (W2, X))
    iw2b = s([iw2, s([i2], 'oveq1d', '( ( Im ` %s ) - %s ) = ( T - %s )' % (SS, Y, Y))], 'eqtrd', '( Im ` %s ) = ( T - %s )' % (W2, Y))
    a1 = s([w1c, w.inst('absvalsq2')], 'syl', '( ( abs ` %s ) ^ 2 ) = ( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (W1, W1, W1))
    a2 = s([w2c, w.inst('absvalsq2')], 'syl', '( ( abs ` %s ) ^ 2 ) = ( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (W2, W2, W2))
    a1b = s([a1, s([s([rw1b], 'oveq1d', '( ( Re ` %s ) ^ 2 ) = ( ( %s - 1 ) ^ 2 )' % (W1, X)), s([iw1b], 'oveq1d', '( ( Im ` %s ) ^ 2 ) = ( ( %s - T ) ^ 2 )' % (W1, Y))], 'oveq12d',
                  '( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) ) = ( ( ( %s - 1 ) ^ 2 ) + ( ( %s - T ) ^ 2 ) )' % (W1, W1, X, Y))], 'eqtrd',
            '( ( abs ` %s ) ^ 2 ) = ( ( ( %s - 1 ) ^ 2 ) + ( ( %s - T ) ^ 2 ) )' % (W1, X, Y))
    a2b = s([a2, s([s([rw2b], 'oveq1d', '( ( Re ` %s ) ^ 2 ) = ( ( ( 1 + E ) - %s ) ^ 2 )' % (W2, X)), s([iw2b], 'oveq1d', '( ( Im ` %s ) ^ 2 ) = ( ( T - %s ) ^ 2 )' % (W2, Y))], 'oveq12d',
                  '( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) ) = ( ( ( ( 1 + E ) - %s ) ^ 2 ) + ( ( T - %s ) ^ 2 ) )' % (W2, W2, X, Y))], 'eqtrd',
            '( ( abs ` %s ) ^ 2 ) = ( ( ( ( 1 + E ) - %s ) ^ 2 ) + ( ( T - %s ) ^ 2 ) )' % (W2, X, Y))
    c = Closure(w, A0, {'E': ('RR', er), 'T': ('RR', tr), X: ('RR', s([qc], 'recld', '%s e. RR' % X)), Y: ('RR', s([qc], 'imcld', '%s e. RR' % Y)),
                        '( ( abs ` %s ) ^ 2 )' % W1: ('RR', s([s([w1c], 'abscld', '( abs ` %s ) e. RR' % W1)], 'resqcld', '( ( abs ` %s ) ^ 2 ) e. RR' % W1)),
                        '( ( abs ` %s ) ^ 2 )' % W2: ('RR', s([s([w2c], 'abscld', '( abs ` %s ) e. RR' % W2)], 'resqcld', '( ( abs ` %s ) ^ 2 ) e. RR' % W2))})
    for e_ in (X, Y, '( ( abs ` %s ) ^ 2 )' % W1, '( ( abs ` %s ) ^ 2 )' % W2):
        c.atom(e_)
    sq = nlinarith(w, A0, [a1b, a2b, e0, rq], '( ( abs ` %s ) ^ 2 ) <_ ( ( abs ` %s ) ^ 2 )' % (W1, W2), closure=c)
    le = s([s([w1c], 'abscld', '( abs ` %s ) e. RR' % W1), s([w2c], 'abscld', '( abs ` %s ) e. RR' % W2), s([w1c], 'absge0d', '0 <_ ( abs ` %s )' % W1), s([w2c], 'absge0d', '0 <_ ( abs ` %s )' % W2)],
           'le2sqd', '( ( abs ` %s ) <_ ( abs ` %s ) <-> ( ( abs ` %s ) ^ 2 ) <_ ( ( abs ` %s ) ^ 2 ) )' % (W1, W2, W1, W2))
    fin = s([sq, le], 'mpbird', '( abs ` %s ) <_ ( abs ` %s )' % (W1, W2))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kddist']))
    return run(w)


if __name__ == '__main__':
    gen_dist()
