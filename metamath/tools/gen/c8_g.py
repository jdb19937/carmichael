"""Sortie C8, section 2: the telescoping exponential (eftel)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *

CZ = '( CC \\ { 0 } )'


def LG(K):
    return '( log ` ( ( V ` ( %s + 1 ) ) / ( V ` %s ) ) )' % (K, K)


def S_(I):
    return 'sum_ k e. ( 0 ..^ %s ) %s' % (I, LG('k'))


def PS(I):
    return '( exp ` %s ) = ( ( V ` %s ) / ( V ` 0 ) )' % (S_(I), I)


def gen_eftel():
    w = W('eftel', 'The exponential of a telescoping sum of principal logarithms of consecutive quotients is the quotient of the end values.')
    A0 = '( N e. NN0 /\\ V : ( 0 ... N ) --> %s )' % CZ
    nn0 = w.s([], 'simpl', '( %s -> N e. NN0 )' % A0)
    vf = w.s([], 'simpr', '( %s -> V : ( 0 ... N ) --> %s )' % (A0, CZ))

    def vval(ante, vf_, mem, K):
        """( ante -> ( V ` K ) e. CC ) and ( ante -> ( V ` K ) =/= 0 )"""
        v = w.s([vf_, mem], 'ffvelcdmd', '( %s -> ( V ` %s ) e. %s )' % (ante, K, CZ))
        return (w.s([v, w.inst('eldifi')], 'syl', '( %s -> ( V ` %s ) e. CC )' % (ante, K)),
                w.s([v, w.inst('eldifsni')], 'syl', '( %s -> ( V ` %s ) =/= 0 )' % (ante, K)))

    def closk(ante, vf_, kfzo, K):
        """from ( ante -> K e. ( 0 ..^ N ) ): the values at K, K + 1 and LG(K) e. CC"""
        kfz = w.s([kfzo, w.inst('elfzofz')], 'syl', '( %s -> %s e. ( 0 ... N ) )' % (ante, K))
        k1fz = w.s([kfzo, w.inst('fzofzp1')], 'syl', '( %s -> ( %s + 1 ) e. ( 0 ... N ) )' % (ante, K))
        vk, vk0 = vval(ante, vf_, kfz, K)
        vk1, vk10 = vval(ante, vf_, k1fz, '( %s + 1 )' % K)
        q = w.s([vk1, vk, vk0], 'divcld', '( %s -> ( ( V ` ( %s + 1 ) ) / ( V ` %s ) ) e. CC )' % (ante, K, K))
        q0 = w.s([vk1, vk, vk10, vk0], 'divne0d', '( %s -> ( ( V ` ( %s + 1 ) ) / ( V ` %s ) ) =/= 0 )' % (ante, K, K))
        lc = w.s([q, q0], 'logcld', '( %s -> %s e. CC )' % (ante, LG(K)))
        return dict(vk=vk, vk0=vk0, vk1=vk1, vk10=vk10, q=q, q0=q0, lc=lc)

    # ---- the step
    YH = '( h e. ZZ /\\ 0 <_ h /\\ h < N )'
    PH = '( %s /\\ %s )' % (A0, YH)
    ST = '( %s /\\ %s /\\ %s )' % (A0, YH, PS('h'))
    yh = w.s([], 'simpr', '( %s -> %s )' % (PH, YH))
    a0p = w.s([], 'simpl', '( %s -> %s )' % (PH, A0))
    hz = w.s([yh, w.inst('simp1')], 'syl', '( %s -> h e. ZZ )' % PH)
    h0 = w.s([yh, w.inst('simp2')], 'syl', '( %s -> 0 <_ h )' % PH)
    hn = w.s([yh, w.inst('simp3')], 'syl', '( %s -> h < N )' % PH)
    hn0 = w.s([w.s([hz, h0], 'jca', '( %s -> ( h e. ZZ /\\ 0 <_ h ) )' % PH), w.s([], 'elnn0z', '( h e. NN0 <-> ( h e. ZZ /\\ 0 <_ h ) )')], 'sylibr', '( %s -> h e. NN0 )' % PH)
    huz = w.s([hn0, w.s([], 'elnn0uz', '( h e. NN0 <-> h e. ( ZZ>= ` 0 ) )')], 'sylib', '( %s -> h e. ( ZZ>= ` 0 ) )' % PH)
    nn0p = w.s([a0p, nn0], 'syl', '( %s -> N e. NN0 )' % PH)
    hr = w.s([hn0], 'nn0red', '( %s -> h e. RR )' % PH)
    nr = w.s([nn0p], 'nn0red', '( %s -> N e. RR )' % PH)
    npos = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % PH), hr, nr, h0, hn], 'lelttrd', '( %s -> 0 < N )' % PH)
    nnn = w.s([w.s([nn0p, npos], 'jca', '( %s -> ( N e. NN0 /\\ 0 < N ) )' % PH), w.s([], 'elnnnn0b', '( N e. NN <-> ( N e. NN0 /\\ 0 < N ) )')], 'sylibr', '( %s -> N e. NN )' % PH)
    vfp = w.s([a0p, vf], 'syl', '( %s -> V : ( 0 ... N ) --> %s )' % (PH, CZ))
    # closure over k e. ( 0 ... h )
    PK = '( %s /\\ k e. ( 0 ... h ) )' % PH
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ... h ) )' % PK)
    k3 = w.s([kin, w.s([], 'elfz2nn0', '( k e. ( 0 ... h ) <-> ( k e. NN0 /\\ h e. NN0 /\\ k <_ h ) )')], 'sylib', '( %s -> ( k e. NN0 /\\ h e. NN0 /\\ k <_ h ) )' % PK)
    kn0 = w.s([k3, w.inst('simp1')], 'syl', '( %s -> k e. NN0 )' % PK)
    klh = w.s([k3, w.inst('simp3')], 'syl', '( %s -> k <_ h )' % PK)
    kltn = w.s([w.s([kn0], 'nn0red', '( %s -> k e. RR )' % PK), w.s([hr], 'adantr', '( %s -> h e. RR )' % PK), w.s([nr], 'adantr', '( %s -> N e. RR )' % PK),
                klh, w.s([hn], 'adantr', '( %s -> h < N )' % PK)], 'lelttrd', '( %s -> k < N )' % PK)
    kfzo = w.s([w.s([kn0, w.s([nnn], 'adantr', '( %s -> N e. NN )' % PK), kltn], '3jca', '( %s -> ( k e. NN0 /\\ N e. NN /\\ k < N ) )' % PK),
                w.s([], 'elfzo0', '( k e. ( 0 ..^ N ) <-> ( k e. NN0 /\\ N e. NN /\\ k < N ) )')], 'sylibr', '( %s -> k e. ( 0 ..^ N ) )' % PK)
    ck = closk(PK, w.s([vfp], 'adantr', '( %s -> V : ( 0 ... N ) --> %s )' % (PK, CZ)), kfzo, 'k')
    # the closure at h and the split
    hfzo = w.s([w.s([hn0, nnn, hn], '3jca', '( %s -> ( h e. NN0 /\\ N e. NN /\\ h < N ) )' % PH),
                w.s([], 'elfzo0', '( h e. ( 0 ..^ N ) <-> ( h e. NN0 /\\ N e. NN /\\ h < N ) )')], 'sylibr', '( %s -> h e. ( 0 ..^ N ) )' % PH)
    chh = closk(PH, vfp, hfzo, 'h')
    subh = w.s([w.s([w.s([w.s([], 'oveq1', '( k = h -> ( k + 1 ) = ( h + 1 ) )')], 'fveq2d', '( k = h -> ( V ` ( k + 1 ) ) = ( V ` ( h + 1 ) ) )'),
                     w.s([], 'fveq2', '( k = h -> ( V ` k ) = ( V ` h ) )')], 'oveq12d', '( k = h -> ( ( V ` ( k + 1 ) ) / ( V ` k ) ) = ( ( V ` ( h + 1 ) ) / ( V ` h ) ) )')],
               'fveq2d', '( k = h -> %s = %s )' % (LG('k'), LG('h')))
    split = w.s([huz, ck['lc'], subh], 'fzosump1', '( %s -> %s = ( %s + %s ) )' % (PH, S_('( h + 1 )'), S_('h'), LG('h')))
    # S ( h ) e. CC
    PK2 = '( %s /\\ k e. ( 0 ..^ h ) )' % PH
    kk = w.s([w.s([], 'simpr', '( %s -> k e. ( 0 ..^ h ) )' % PK2), w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... h ) )' % PK2)
    # reuse the closure through the implication ( PK -> LG k e. CC )
    lcimp = w.s([ck['lc']], 'ex', '( %s -> ( k e. ( 0 ... h ) -> %s e. CC ) )' % (PH, LG('k')))
    lck2 = w.s([kk, w.s([lcimp], 'adantr', '( %s -> ( k e. ( 0 ... h ) -> %s e. CC ) )' % (PK2, LG('k')))], 'mpd', '( %s -> %s e. CC )' % (PK2, LG('k')))
    sc = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ h ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ h ) e. Fin )' % PH), lck2], 'fsumcl', '( %s -> %s e. CC )' % (PH, S_('h')))
    ex1 = w.s([w.s([split], 'fveq2d', '( %s -> ( exp ` %s ) = ( exp ` ( %s + %s ) ) )' % (PH, S_('( h + 1 )'), S_('h'), LG('h'))),
               w.s([sc, chh['lc'], w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (PH, S_('h'), LG('h'), S_('h'), LG('h')))],
              'eqtrd', '( %s -> ( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (PH, S_('( h + 1 )'), S_('h'), LG('h')))
    elq = w.s([chh['q'], chh['q0'], w.inst('eflog')], 'syl2anc', '( %s -> ( exp ` %s ) = ( ( V ` ( h + 1 ) ) / ( V ` h ) ) )' % (PH, LG('h')))
    # combine under ST
    ph_ = w.s([], '3simpa', '( %s -> %s )' % (ST, PH))
    th = w.s([], 'simp3', '( %s -> %s )' % (ST, PS('h')))
    def L(st, f):
        return w.s([ph_, st], 'syl', '( %s -> %s )' % (ST, f))
    e1 = L(ex1, '( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (S_('( h + 1 )'), S_('h'), LG('h')))
    e2 = w.s([th, L(elq, '( exp ` %s ) = ( ( V ` ( h + 1 ) ) / ( V ` h ) )' % LG('h'))], 'oveq12d',
             '( %s -> ( ( exp ` %s ) x. ( exp ` %s ) ) = ( ( ( V ` h ) / ( V ` 0 ) ) x. ( ( V ` ( h + 1 ) ) / ( V ` h ) ) ) )' % (ST, S_('h'), LG('h')))
    # V ` 0
    z0 = w.s([w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % A0), nn0, w.s([nn0], 'nn0ge0d', '( %s -> 0 <_ N )' % A0)], '3jca',
             '( %s -> ( 0 e. NN0 /\\ N e. NN0 /\\ 0 <_ N ) )' % A0)
    z0in = w.s([z0, w.s([], 'elfz2nn0', '( 0 e. ( 0 ... N ) <-> ( 0 e. NN0 /\\ N e. NN0 /\\ 0 <_ N ) )')], 'sylibr', '( %s -> 0 e. ( 0 ... N ) )' % A0)
    v0, v00 = vval(A0, vf, z0in, '0')
    e3 = w.s([L(chh['vk1'], '( V ` ( h + 1 ) ) e. CC'), L(chh['vk'], '( V ` h ) e. CC'), w.s([ph_, a0p], 'syl', '( %s -> %s )' % (ST, A0)) if False else
              w.s([w.s([ph_, a0p], 'syl', '( %s -> %s )' % (ST, A0)), v0], 'syl', '( %s -> ( V ` 0 ) e. CC )' % ST),
              L(chh['vk0'], '( V ` h ) =/= 0'), w.s([w.s([ph_, a0p], 'syl', '( %s -> %s )' % (ST, A0)), v00], 'syl', '( %s -> ( V ` 0 ) =/= 0 )' % ST)], 'dmdcand',
             '( %s -> ( ( ( V ` h ) / ( V ` 0 ) ) x. ( ( V ` ( h + 1 ) ) / ( V ` h ) ) ) = ( ( V ` ( h + 1 ) ) / ( V ` 0 ) ) )' % ST)
    step = w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( exp ` %s ) = ( ( ( V ` h ) / ( V ` 0 ) ) x. ( ( V ` ( h + 1 ) ) / ( V ` h ) ) ) )' % (ST, S_('( h + 1 )'))), e3],
               'eqtrd', '( %s -> %s )' % (ST, PS('( h + 1 )')))
    # ---- the base
    b1 = w.s([w.s([w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)'), w.inst('sumeq1')], 'ax-mp', '%s = sum_ k e. (/) %s' % (S_('0'), LG('k'))),
              w.s([], 'sum0', 'sum_ k e. (/) %s = 0' % LG('k'))], 'eqtri', '%s = 0' % S_('0'))
    b2 = w.s([w.s([b1], 'fveq2i', '( exp ` %s ) = ( exp ` 0 )' % S_('0')), w.s([], 'ef0', '( exp ` 0 ) = 1')], 'eqtri', '( exp ` %s ) = 1' % S_('0'))
    b3 = w.s([w.s([b2], 'a1i', '( %s -> ( exp ` %s ) = 1 )' % (A0, S_('0'))), w.s([w.s([v0, v00], 'dividd', '( %s -> ( ( V ` 0 ) / ( V ` 0 ) ) = 1 )' % A0)], 'eqcomd',
                                                                              '( %s -> 1 = ( ( V ` 0 ) / ( V ` 0 ) ) )' % A0)], 'eqtrd', '( %s -> %s )' % (A0, PS('0')))
    # ---- the induction
    def sb(t):
        idx = w.s([], 'id', '( i = %s -> i = %s )' % (t, t))
        cg, new = w.wcongr(PS('i'), {'i': t}, 'i = %s' % t, {'i': idx})
        assert new == PS(t), new
        return cg
    s1 = sb('0'); s2 = sb('h'); s3 = sb('( h + 1 )'); s4 = sb('N')
    nz = w.s([nn0], 'nn0zd', '( %s -> N e. ZZ )' % A0)
    ind = w.s([s1, s2, s3, s4, b3, step, w.s([], '0zd', '( %s -> 0 e. ZZ )' % A0), nz, w.s([nn0], 'nn0ge0d', '( %s -> 0 <_ N )' % A0)], 'fzindd',
              '( ( %s /\\ ( N e. ZZ /\\ 0 <_ N /\\ N <_ N ) ) -> %s )' % (A0, PS('N')))
    nn = w.s([nz, w.s([nn0], 'nn0ge0d', '( %s -> 0 <_ N )' % A0), w.s([w.s([nn0], 'nn0red', '( %s -> N e. RR )' % A0)], 'leidd', '( %s -> N <_ N )' % A0)], '3jca',
             '( %s -> ( N e. ZZ /\\ 0 <_ N /\\ N <_ N ) )' % A0)
    w.qed([nn, ind], 'mpdan', '( %s -> %s )' % (A0, PS('N')))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_eftel]:
        g()
