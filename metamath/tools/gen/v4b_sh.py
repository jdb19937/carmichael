"""Sortie v4b block 3: the sieve hypothesis of the progression sieve.

progsh  ( PH -> SH )
progsel ( PH -> SF <_ ( ( X / SS ) + ERR ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import A, P, PH, V, WF, X, Y, SH, SS, SF, ERR, T, mkst

MUL = ('A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> ( %s ` ( a x. b ) ) = '
       '( ( %s ` a ) x. ( %s ` b ) ) )' % (V, V, V))
PRM = ('A. s e. Prime ( s || %s -> ( 0 < ( %s ` s ) /\\ ( %s ` s ) < 1 ) )' % (P, V, V))


def progsh():
    w = W('progsh', 'The progression sieve satisfies the hypothesis of the fundamental '
                    'theorem of the Selberg sieve.')
    st = mkst(w, PH)
    muz = st([], 'simp1', 'M e. ( ZZ>= ` 2 )')
    mnn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    znn = st([], 'simp2', 'Z e. NN')
    nn0 = st([], 'simp3', 'N e. NN0')
    # A e. Fin, A C_ NN
    fzf = st([], 'fzfid', '( 1 ... N ) e. Fin')
    ass = st([w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % A)], 'a1i', '%s C_ ( 1 ... N )' % A)
    afin = st([fzf, ass], 'ssfid', '%s e. Fin' % A)
    fss = st([w.s([], 'fz1ssnn', '( 1 ... N ) C_ NN')], 'a1i', '( 1 ... N ) C_ NN')
    ann = st([ass, fss], 'sstrd', '%s C_ NN' % A)
    # W : NN --> RR
    ac = '( %s /\\ c e. NN )' % PH
    wf = st([w.s([], '1red', '( %s -> 1 e. RR )' % ac),
             w.s([], 'eqid', '%s = %s' % (WF, WF))], 'fmptd', '%s : NN --> RR' % WF)
    g1 = st([afin, ann, wf], '3jca',
            '( %s e. Fin /\\ %s C_ NN /\\ %s : NN --> RR )' % (A, A, WF))
    # A. k e. NN 0 <_ ( W ` k )
    wv0 = w.s([w.s([], 'eqidd', '( c = k -> 1 = 1 )'),
               w.s([], 'eqid', '%s = %s' % (WF, WF))], 'fvmptg',
              '( ( k e. NN /\\ 1 e. _V ) -> ( %s ` k ) = 1 )' % WF)
    oex = w.s([], '1ex', '1 e. _V')
    wv = w.s([w.s([], 'id', '( k e. NN -> k e. NN )'),
              w.s([oex], 'a1i', '( k e. NN -> 1 e. _V )'), wv0],
             'syl2anc', '( k e. NN -> ( %s ` k ) = 1 )' % WF)
    zle1 = w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( k e. NN -> 0 <_ 1 )')
    wge = w.s([zle1, wv], 'breqtrrd', '( k e. NN -> 0 <_ ( %s ` k ) )' % WF)
    wrg = st([w.s([wge], 'rgen', 'A. k e. NN 0 <_ ( %s ` k )' % WF)], 'a1i',
             'A. k e. NN 0 <_ ( %s ` k )' % WF)
    # X e. RR
    nre = st([nn0], 'nn0red', 'N e. RR')
    mre = st([mnn], 'nnred', 'M e. RR')
    mne = st([mnn], 'nnne0d', 'M =/= 0')
    xre = st([nre, mre, mne], 'redivcld', '%s e. RR' % X)
    # Y e. RR /\ 1 <_ Y
    zre = st([znn], 'nnred', 'Z e. RR')
    two = st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    yre = st([zre, two], 'reexpcld', '%s e. RR' % Y)
    zge1 = st([znn], 'nnge1d', '1 <_ Z')
    y1 = st([zre, two, zge1, w.inst('expge1')], 'syl3anc', '1 <_ %s' % Y)
    g2 = st([wrg, xre, st([yre, y1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (Y, Y))], '3jca',
            '( A. k e. NN 0 <_ ( %s ` k ) /\\ %s e. RR /\\ ( %s e. RR /\\ 1 <_ %s ) )'
            % (WF, X, Y, Y))
    # P
    pn = st([], 'progpnn',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )'
            % (P, P, P, T))
    g3 = st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))
    # V
    vcl = st([], 'progvcl', '%s : NN --> RR' % V)
    v1 = st([], 'progv1', '( %s ` 1 ) = 1' % V)
    vm = st([], 'progvmul', MUL)
    vp = st([], 'progvprm', PRM)
    g4 = st([vcl, v1, st([vm, vp], 'jca', '( %s /\\ %s )' % (MUL, PRM))], '3jca',
            '( %s : NN --> RR /\\ ( %s ` 1 ) = 1 /\\ ( %s /\\ %s ) )' % (V, V, MUL, PRM))
    w.qed([st([g1, g2], 'jca', '( ( %s e. Fin /\\ %s C_ NN /\\ %s : NN --> RR ) /\\ '
               '( A. k e. NN 0 <_ ( %s ` k ) /\\ %s e. RR /\\ ( %s e. RR /\\ 1 <_ %s ) ) )'
               % (A, A, WF, WF, X, Y, Y)),
           st([g3, g4], 'jca', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ '
              '( %s : NN --> RR /\\ ( %s ` 1 ) = 1 /\\ ( %s /\\ %s ) ) )'
              % (P, P, V, V, MUL, PRM))], 'jca', '( %s -> %s )' % (PH, SH))
    return w


def progsel():
    w = W('progsel', 'The fundamental theorem of the Selberg sieve at the progression '
                     'sieve.')
    st = mkst(w, PH)
    sh = st([], 'progsh', SH)
    w.qed([sh, w.inst('selbsieve')], 'syl',
          '( %s -> %s <_ ( ( %s / %s ) + %s ) )' % (PH, SF, X, SS, ERR))
    return w


def main(names=None):
    fns = {'progsh': progsh, 'progsel': progsel}
    order = ['progsh', 'progsel']
    ok = True
    for nm in (names or order):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
