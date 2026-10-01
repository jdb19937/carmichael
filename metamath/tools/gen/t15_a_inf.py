"""T15 (a): address objects TMFam / TMLab and the trie walk TMWalk."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *

WN = 'Word NN0'


def wordex(w):
    a = w.s([], 'nn0ex', 'NN0 e. _V')
    i = w.inst('wrdexg')
    return w.s([a, i], 'ax-mp', 'Word NN0 e. _V')


def tmfam0():
    w = W('tmfam0', 'The address objects of depth 0 carry only their address.')
    d = w.s([], 'df-tmfam', 'TMFam = %s' % SEQF)
    a = w.s([d], 'fveq1i', '( TMFam ` 0 ) = ( %s ` 0 )' % SEQF)
    z = w.s([], '0z', '0 e. ZZ')
    b = w.s([z, w.inst('seq1')], 'ax-mp', '( %s ` 0 ) = ( ( NN0 X. { %s } ) ` 0 )' % (SEQF, F0))
    we = wordex(w)
    fx = w.s([we], 'mptex', '%s e. _V' % F0)
    n0 = w.s([], '0nn0', '0 e. NN0')
    c = w.s([fx, n0, w.inst('fvconst2g')], 'mp2an', '( ( NN0 X. { %s } ) ` 0 ) = %s' % (F0, F0))
    w.qed([a, b, c], '3eqtri', '( TMFam ` 0 ) = %s' % F0)
    return w


def tmfamsuc():
    w = W('tmfamsuc', 'The address objects of depth N + 1.')
    ph = 'N e. NN0'
    d = w.s([], 'df-tmfam', 'TMFam = %s' % SEQF)
    t3 = w.s([d], 'fveq1i', '( TMFam ` ( N + 1 ) ) = ( %s ` ( N + 1 ) )' % SEQF)
    idn = w.s([], 'id', '( N e. NN0 -> N e. NN0 )')
    uz = w.s([idn, w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '( N e. NN0 -> N e. ( ZZ>= ` 0 ) )')
    B = '( ( NN0 X. { %s } ) ` ( N + 1 ) )' % F0
    t1 = w.s([uz, w.inst('seqp1')], 'syl', '( N e. NN0 -> ( %s ` ( N + 1 ) ) = ( ( %s ` N ) %s %s ) )' % (SEQF, SEQF, OPF, B))
    s8 = w.s([d], 'fveq1i', '( TMFam ` N ) = ( %s ` N )' % SEQF)
    s8r = w.s([s8], 'eqcomi', '( %s ` N ) = ( TMFam ` N )' % SEQF)
    o1 = w.s([s8r], 'oveq1i', '( ( %s ` N ) %s %s ) = ( ( TMFam ` N ) %s %s )' % (SEQF, OPF, B, OPF, B))
    # ovmpog closed
    body = '( w e. Word NN0 |-> ( ( i e. NN0 |-> ( g ` ( w ++ <" i "> ) ) ) u. { <. -u 1 , w >. } ) )'
    h1, v1 = subhyp(w, 'g', '( TMFam ` N )', body)
    h2 = w.s([], 'eqidd', '( y = %s -> %s = %s )' % (B, v1, v1))
    h3 = w.s([], 'eqid', '%s = %s' % (OPF, OPF))
    om = w.s([h1, h2, h3], 'ovmpog', '( ( ( TMFam ` N ) e. _V /\\ %s e. _V /\\ %s e. _V ) -> ( ( TMFam ` N ) %s %s ) = %s )' % (B, v1, OPF, B, v1))
    e1 = w.s([], 'fvex', '( TMFam ` N ) e. _V')
    e2 = w.s([], 'fvex', '%s e. _V' % B)
    e3 = w.s([wordex(w)], 'mptex', '%s e. _V' % v1)
    o2 = w.s([e1, e2, e3, om], 'mp3an', '( ( TMFam ` N ) %s %s ) = %s' % (OPF, B, v1))
    t2 = w.s([o1, o2], 'eqtri', '( ( %s ` N ) %s %s ) = %s' % (SEQF, OPF, B, v1))
    u = w.s([t3, t1], 'eqtrid', '( N e. NN0 -> ( TMFam ` ( N + 1 ) ) = ( ( %s ` N ) %s %s ) )' % (SEQF, OPF, B))
    w.qed([u, t2], 'eqtrdi', '( N e. NN0 -> ( TMFam ` ( N + 1 ) ) = %s )' % GF('N'))
    return w


def neg1nn0(w):
    """-. -u 1 e. NN0"""
    a = w.s([], 'neg1lt0', '-u 1 < 0')
    b = w.s([], 'nn0nlt0', '( -u 1 e. NN0 -> -. -u 1 < 0 )')
    return w.s([a, b], 'mt2', '-. -u 1 e. NN0')


def union_parts(w, ante, N, Wd, wset):
    """( ante -> F Fn NN0 ), ( ante -> G Fn { -u 1 } ), ( ante -> ( NN0 i^i { -u 1 } ) = (/) )"""
    F = '( i e. NN0 |-> ( ( TMFam ` %s ) ` ( %s ++ <" i "> ) ) )' % (N, Wd)
    fx = w.s([], 'fvex', '( ( TMFam ` %s ) ` ( %s ++ <" i "> ) ) e. _V' % (N, Wd))
    fe = w.s([], 'eqid', '%s = %s' % (F, F))
    fn = w.s([fx, fe], 'fnmpti', '%s Fn NN0' % F)
    fnd = a1(w, ante, fn, '%s Fn NN0' % F)
    ng = w.s([], 'negex', '-u 1 e. _V')
    ngd = a1(w, ante, ng, '-u 1 e. _V')
    gn = w.s([ngd, wset, w.inst('fnsng')], 'syl2anc', '( %s -> { <. -u 1 , %s >. } Fn { -u 1 } )' % (ante, Wd))
    dj = w.s([neg1nn0(w), w.s([], 'disjsn', '( ( NN0 i^i { -u 1 } ) = (/) <-> -. -u 1 e. NN0 )')], 'mpbir',
             '( NN0 i^i { -u 1 } ) = (/)')
    djd = a1(w, ante, dj, '( NN0 i^i { -u 1 } ) = (/)')
    return F, fnd, gn, djd


def uex(w, ante, N, Wd):
    F = '( i e. NN0 |-> ( ( TMFam ` %s ) ` ( %s ++ <" i "> ) ) )' % (N, Wd)
    a = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % F)
    b = w.s([], 'snex', '{ <. -u 1 , %s >. } e. _V' % Wd)
    c = w.s([a, b], 'unex', '%s e. _V' % UF(N, Wd))
    return a1(w, ante, c, '%s e. _V' % UF(N, Wd))


def tmfamap():
    w = W('tmfamap', 'Applying an address object of depth N + 1 to an index extends its address.')
    ph = '( N e. NN0 /\\ W e. Word NN0 /\\ I e. NN0 )'
    n = w.s([], 'simp1', '( %s -> N e. NN0 )' % ph)
    wm = w.s([], 'simp2', '( %s -> W e. Word NN0 )' % ph)
    im = w.s([], 'simp3', '( %s -> I e. NN0 )' % ph)
    a2 = w.s([n, w.inst('tmfamsuc')], 'syl', '( %s -> ( TMFam ` ( N + 1 ) ) = %s )' % (ph, GF('N')))
    a3 = w.s([a2], 'fveq1d', '( %s -> ( ( TMFam ` ( N + 1 ) ) ` W ) = ( %s ` W ) )' % (ph, GF('N')))
    body = UF('N', 'w')
    a4, v = fvm(w, ph, GF('N'), None, 'w', WN, body, 'W', wm, uex(w, ph, 'N', 'W'))
    a5 = w.s([a3, a4], 'eqtrd', '( %s -> ( ( TMFam ` ( N + 1 ) ) ` W ) = %s )' % (ph, v))
    a6 = w.s([a5], 'fveq1d', '( %s -> ( ( ( TMFam ` ( N + 1 ) ) ` W ) ` I ) = ( %s ` I ) )' % (ph, v))
    wset = w.s([wm], 'elexd', '( %s -> W e. _V )' % ph)
    F, fnd, gn, djd = union_parts(w, ph, 'N', 'W', wset)
    j = w.s([djd, im], 'jca', '( %s -> ( ( NN0 i^i { -u 1 } ) = (/) /\\ I e. NN0 ) )' % ph)
    u1 = w.s([fnd, gn, j, w.inst('fvun1')], 'syl3anc', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (ph, v, F))
    ex = w.s([], 'fvexd', '( %s -> ( ( TMFam ` N ) ` ( W ++ <" I "> ) ) e. _V )' % ph)
    u2, v2 = fvm(w, ph, F, None, 'i', 'NN0', '( ( TMFam ` N ) ` ( W ++ <" i "> ) )', 'I', im, ex)
    w.qed([a6, u1, u2], '3eqtrd', '( %s -> ( ( ( TMFam ` ( N + 1 ) ) ` W ) ` I ) = ( ( TMFam ` N ) ` ( W ++ <" I "> ) ) )' % ph)
    return w


def tmfamadr():
    w = W('tmfamadr', 'An address object returns its address at -u 1.')
    ph = '( N e. NN0 /\\ W e. Word NN0 )'
    wm = w.s([], 'simpr', '( %s -> W e. Word NN0 )' % ph)
    wset = w.s([wm], 'elexd', '( %s -> W e. _V )' % ph)
    ng = w.s([], 'negex', '-u 1 e. _V')
    goal = '( ( ( TMFam ` N ) ` W ) ` -u 1 ) = W'
    # case N = 0
    p0 = '( %s /\\ N = 0 )' % ph
    c0a = w.s([], 'simpr', '( %s -> N = 0 )' % p0)
    c0b = w.s([c0a], 'fveq2d', '( %s -> ( TMFam ` N ) = ( TMFam ` 0 ) )' % p0)
    c0c = a1(w, p0, w.s([], 'tmfam0', '( TMFam ` 0 ) = %s' % F0), '( TMFam ` 0 ) = %s' % F0)
    c0d = w.s([c0b, c0c], 'eqtrd', '( %s -> ( TMFam ` N ) = %s )' % (p0, F0))
    c0e = w.s([c0d], 'fveq1d', '( %s -> ( ( TMFam ` N ) ` W ) = ( %s ` W ) )' % (p0, F0))
    wm0 = w.s([wm], 'adantr', '( %s -> W e. Word NN0 )' % p0)
    sx = a1(w, p0, w.s([], 'snex', '{ <. -u 1 , W >. } e. _V'), '{ <. -u 1 , W >. } e. _V')
    c0f, v0 = fvm(w, p0, F0, None, 'w', WN, '{ <. -u 1 , w >. }', 'W', wm0, sx)
    c0g = w.s([c0e, c0f], 'eqtrd', '( %s -> ( ( TMFam ` N ) ` W ) = { <. -u 1 , W >. } )' % p0)
    c0h = w.s([c0g], 'fveq1d', '( %s -> ( ( ( TMFam ` N ) ` W ) ` -u 1 ) = ( { <. -u 1 , W >. } ` -u 1 ) )' % p0)
    ngd0 = a1(w, p0, ng, '-u 1 e. _V')
    ws0 = w.s([wset], 'adantr', '( %s -> W e. _V )' % p0)
    c0i = w.s([ngd0, ws0, w.inst('fvsng')], 'syl2anc', '( %s -> ( { <. -u 1 , W >. } ` -u 1 ) = W )' % p0)
    case0 = w.s([c0h, c0i], 'eqtrd', '( %s -> %s )' % (p0, goal))
    # case N e. NN
    p1 = '( %s /\\ N e. NN )' % ph
    nn = w.s([], 'simpr', '( %s -> N e. NN )' % p1)
    m0 = w.s([nn, w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % p1)
    ncc = w.s([nn], 'nncnd', '( %s -> N e. CC )' % p1)
    np = w.s([ncc], 'npcand1', '( %s -> ( ( N - 1 ) + 1 ) = N )' % p1) if False else None
    np = w.s([ncc, w.inst('npcan1')], 'syl', '( %s -> ( ( N - 1 ) + 1 ) = N )' % p1)
    f1 = w.s([np], 'fveq2d', '( %s -> ( TMFam ` ( ( N - 1 ) + 1 ) ) = ( TMFam ` N ) )' % p1)
    f2 = w.s([m0, w.inst('tmfamsuc')], 'syl', '( %s -> ( TMFam ` ( ( N - 1 ) + 1 ) ) = %s )' % (p1, GF('( N - 1 )')))
    f3 = w.s([f1, f2], 'eqtr3d', '( %s -> ( TMFam ` N ) = %s )' % (p1, GF('( N - 1 )')))
    f4 = w.s([f3], 'fveq1d', '( %s -> ( ( TMFam ` N ) ` W ) = ( %s ` W ) )' % (p1, GF('( N - 1 )')))
    wm1 = w.s([wm], 'adantr', '( %s -> W e. Word NN0 )' % p1)
    f5, v1 = fvm(w, p1, GF('( N - 1 )'), None, 'w', WN, UF('( N - 1 )', 'w'), 'W', wm1, uex(w, p1, '( N - 1 )', 'W'))
    f6 = w.s([f4, f5], 'eqtrd', '( %s -> ( ( TMFam ` N ) ` W ) = %s )' % (p1, v1))
    f7 = w.s([f6], 'fveq1d', '( %s -> ( ( ( TMFam ` N ) ` W ) ` -u 1 ) = ( %s ` -u 1 ) )' % (p1, v1))
    ws1 = w.s([wset], 'adantr', '( %s -> W e. _V )' % p1)
    F, fnd, gn, djd = union_parts(w, p1, '( N - 1 )', 'W', ws1)
    sn = w.s([ng], 'snid', '-u 1 e. { -u 1 }')
    snd = a1(w, p1, sn, '-u 1 e. { -u 1 }')
    j = w.s([djd, snd], 'jca', '( %s -> ( ( NN0 i^i { -u 1 } ) = (/) /\\ -u 1 e. { -u 1 } ) )' % p1)
    f8 = w.s([fnd, gn, j, w.inst('fvun2')], 'syl3anc', '( %s -> ( %s ` -u 1 ) = ( { <. -u 1 , W >. } ` -u 1 ) )' % (p1, v1))
    ngd1 = a1(w, p1, ng, '-u 1 e. _V')
    f9 = w.s([ngd1, ws1, w.inst('fvsng')], 'syl2anc', '( %s -> ( { <. -u 1 , W >. } ` -u 1 ) = W )' % p1)
    case1 = w.s([f7, f8, f9], '3eqtrd', '( %s -> %s )' % (p1, goal))
    nm = w.s([], 'simpl', '( %s -> N e. NN0 )' % ph)
    el = w.s([nm, w.s([], 'elnn0', '( N e. NN0 <-> ( N e. NN \\/ N = 0 ) )')], 'sylib', '( %s -> ( N e. NN \\/ N = 0 ) )' % ph)
    w.qed([case1, case0, el], 'mpjaodan', '( %s -> %s )' % (ph, goal))
    return w


GENS = {'tmfam0': tmfam0, 'tmfamsuc': tmfamsuc, 'tmfamap': tmfamap, 'tmfamadr': tmfamadr}

if __name__ == '__main__':
    for lab in sys.argv[1:] or list(GENS):
        GENS[lab]().run()
