"""Sortie v2c: multiplicativity of the density along lcm and gcd.

vlcm   ( V ` ( E lcm F ) ) = ( ( V ` E ) ( V ` F ) ) / ( V ` ( E gcd F ) )
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2c_lib import *
from cl import lift

G = '( E gcd F )'
Q = '( F / ( E gcd F ) )'
LCM = '( E lcm F )'
EQ = '( E x. %s )' % Q


def vlcm():
    w = W('vlcm', 'The density at the least common multiple of two divisors of the sifting '
                  'product.')
    A = '( %s /\\ ( E e. NN /\\ E || P ) /\\ ( F e. NN /\\ F || P ) )' % SH
    d = shsteps(w, A, ((SH, 'simp1d'),))
    st = d['st']
    enn = st([], 'simp2l', 'E e. NN')
    edp = st([], 'simp2r', 'E || P')
    fnn = st([], 'simp3l', 'F e. NN')
    fdp = st([], 'simp3r', 'F || P')
    ez = st([enn], 'nnzd', 'E e. ZZ')
    fz = st([fnn], 'nnzd', 'F e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    ec = st([enn], 'nncnd', 'E e. CC')
    fc = st([fnn], 'nncnd', 'F e. CC')
    # ---- the gcd
    gnn = st([st([enn, fnn], 'jca', '( E e. NN /\\ F e. NN )'), w.inst('gcdnncl')], 'syl',
             '%s e. NN' % G)
    gz = st([gnn], 'nnzd', '%s e. ZZ' % G)
    gc = st([gnn], 'nncnd', '%s e. CC' % G)
    gne = st([gnn], 'nnne0d', '%s =/= 0' % G)
    gdv = st([st([ez, fz], 'jca', '( E e. ZZ /\\ F e. ZZ )'), w.inst('gcddvds')], 'syl',
             '( %s || E /\\ %s || F )' % (G, G))
    gdE = st([gdv], 'simpld', '%s || E' % G)
    gdF = st([gdv], 'simprd', '%s || F' % G)
    gdP = st([st([st([gz, ez, pz], '3jca', '( %s e. ZZ /\\ E e. ZZ /\\ P e. ZZ )' % G),
                  w.inst('dvdstr')], 'syl', '( ( %s || E /\\ E || P ) -> %s || P )' % (G, G)),
              st([gdE, edp], 'jca', '( %s || E /\\ E || P )' % G)], 'mpd', '%s || P' % G)
    # ---- the cofactor
    qnn = st([st([st([fnn, gnn], 'jca', '( F e. NN /\\ %s e. NN )' % G), w.inst('nndivdvds')],
                 'syl', '( %s || F <-> %s e. NN )' % (G, Q)), gdF], 'mpbid', '%s e. NN' % Q)
    qc = st([qnn], 'nncnd', '%s e. CC' % Q)
    fq = st([fc, gc, gne], 'divcan2d', '( %s x. %s ) = F' % (G, Q))
    # ---- ( E lcm F ) = ( E x. Q )
    lz = st([st([st([ez, fz], 'jca', '( E e. ZZ /\\ F e. ZZ )'), w.inst('lcmcl')], 'syl',
                '%s e. NN0' % LCM)], 'nn0cnd', '%s e. CC' % LCM)
    eqc = st([ec, qc], 'mulcld', '%s e. CC' % EQ)
    lg = st([st([enn, fnn], 'jca', '( E e. NN /\\ F e. NN )'), w.inst('lcmgcdnn')], 'syl',
            '( %s x. %s ) = ( E x. F )' % (LCM, G))
    ef = st([st([st([fq], 'eqcomd', 'F = ( %s x. %s )' % (G, Q))], 'oveq2d',
                '( E x. F ) = ( E x. ( %s x. %s ) )' % (G, Q)),
             st([st([ec, gc, qc], 'mulassd',
                    '( ( E x. %s ) x. %s ) = ( E x. ( %s x. %s ) )' % (G, Q, G, Q))], 'eqcomd',
                '( E x. ( %s x. %s ) ) = ( ( E x. %s ) x. %s )' % (G, Q, G, Q))], 'eqtrd',
            '( E x. F ) = ( ( E x. %s ) x. %s )' % (G, Q))
    swap = st([ec, gc, qc], 'mul32d',
              '( ( E x. %s ) x. %s ) = ( %s x. %s )' % (G, Q, EQ, G))
    lgeq = st([lg, st([ef, swap], 'eqtrd', '( E x. F ) = ( %s x. %s )' % (EQ, G))], 'eqtrd',
              '( %s x. %s ) = ( %s x. %s )' % (LCM, G, EQ, G))
    lcmeq = st([st([lz, eqc, gc, gne], 'mulcan2d',
                   '( ( %s x. %s ) = ( %s x. %s ) <-> %s = %s )' % (LCM, G, EQ, G, LCM, EQ)),
                lgeq], 'mpbid', '%s = %s' % (LCM, EQ))
    # ---- squarefreeness and the two coprimality facts
    lcmdP = st([st([st([pz, ez, fz], '3jca', '( P e. ZZ /\\ E e. ZZ /\\ F e. ZZ )'),
                    w.inst('lcmdvds')], 'syl',
                   '( ( E || P /\\ F || P ) -> %s || P )' % LCM),
                st([edp, fdp], 'jca', '( E || P /\\ F || P )')], 'mpd', '%s || P' % LCM)
    eqdP = st([st([lcmeq], 'eqcomd', '%s = %s' % (EQ, LCM)), lcmdP], 'eqbrtrd', '%s || P' % EQ)
    eqnn = st([enn, qnn], 'nnmulcld', '%s e. NN' % EQ)
    eqsqf = st([st([st([d['pnn'], eqnn, eqdP], '3jca',
                       '( P e. NN /\\ %s e. NN /\\ %s || P )' % (EQ, EQ)), w.inst('dvdssqf')],
                   'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` %s ) =/= 0 )' % EQ),
                d['psqf']], 'mpd', '( mmu ` %s ) =/= 0' % EQ)
    cop1 = st([st([enn, qnn, eqsqf], '3jca',
                  '( E e. NN /\\ %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (Q, EQ)),
               w.inst('sqfcop')], 'syl', '( E gcd %s ) = 1' % Q)
    gqsqf = st([st([st([d['pnn'], fnn, fdp], '3jca', '( P e. NN /\\ F e. NN /\\ F || P )'),
                    w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` F ) =/= 0 )'),
                d['psqf']], 'mpd', '( mmu ` F ) =/= 0')
    gqsqf2 = st([st([fq], 'fveq2d', '( mmu ` ( %s x. %s ) ) = ( mmu ` F )' % (G, Q)),
                 gqsqf], 'eqnetrd', '( mmu ` ( %s x. %s ) ) =/= 0' % (G, Q))
    cop2 = st([st([gnn, qnn, gqsqf2], '3jca',
                  '( %s e. NN /\\ %s e. NN /\\ ( mmu ` ( %s x. %s ) ) =/= 0 )' % (G, Q, G, Q)),
               w.inst('sqfcop')], 'syl', '( %s gcd %s ) = 1' % (G, Q))
    # ---- the two multiplicativity instances
    vlc = st([d['vmul'], st([enn, qnn, cop1], '3jca',
                            '( E e. NN /\\ %s e. NN /\\ ( E gcd %s ) = 1 )' % (Q, Q)),
              w.inst('vmulc')], 'syl2anc',
             '( V ` %s ) = ( ( V ` E ) x. ( V ` %s ) )' % (EQ, Q))
    vfq = st([d['vmul'], st([gnn, qnn, cop2], '3jca',
                            '( %s e. NN /\\ %s e. NN /\\ ( %s gcd %s ) = 1 )' % (G, Q, G, Q)),
              w.inst('vmulc')], 'syl2anc',
             '( V ` ( %s x. %s ) ) = ( ( V ` %s ) x. ( V ` %s ) )' % (G, Q, G, Q))
    vf2 = st([st([st([fq], 'fveq2d', '( V ` ( %s x. %s ) ) = ( V ` F )' % (G, Q))], 'eqcomd',
                 '( V ` F ) = ( V ` ( %s x. %s ) )' % (G, Q)), vfq], 'eqtrd',
             '( V ` F ) = ( ( V ` %s ) x. ( V ` %s ) )' % (G, Q))
    # ---- ( V ` Q ) = ( V ` F ) / ( V ` G )
    grp = st([d['sh'], st([gnn, gdP], 'jca', '( %s e. NN /\\ %s || P )' % (G, G)),
              w.inst('vdrp')], 'syl2anc', '( V ` %s ) e. RR+' % G)
    gvc = st([grp], 'rpcnd', '( V ` %s ) e. CC' % G)
    gvne = st([grp], 'rpne0d', '( V ` %s ) =/= 0' % G)
    qvc = st([st([d['vf'], qnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` %s ) e. RR' % Q)], 'recnd',
             '( V ` %s ) e. CC' % Q)
    evc = st([st([d['vf'], enn, w.inst('ffvelcdm')], 'syl2anc', '( V ` E ) e. RR')], 'recnd',
             '( V ` E ) e. CC')
    fvc = st([st([d['vf'], fnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` F ) e. RR')], 'recnd',
             '( V ` F ) e. CC')
    vqval = st([st([qvc, gvc, fvc, gvne], 'divmuld' if False else 'eqdivd',
                   '( ( V ` F ) / ( V ` %s ) ) = ( V ` %s )' % (G, Q)) if False else
               st([st([vf2], 'oveq1d',
                      '( ( V ` F ) / ( V ` %s ) ) = ( ( ( V ` %s ) x. ( V ` %s ) ) / ( V ` %s ) )'
                      % (G, G, Q, G)),
                   st([qvc, gvc, gvne], 'divcan3d',
                      '( ( ( V ` %s ) x. ( V ` %s ) ) / ( V ` %s ) ) = ( V ` %s )'
                      % (G, Q, G, Q))], 'eqtrd',
                  '( ( V ` F ) / ( V ` %s ) ) = ( V ` %s )' % (G, Q))], 'eqcomd',
               '( V ` %s ) = ( ( V ` F ) / ( V ` %s ) )' % (Q, G))
    # ---- assemble
    lhs = st([st([lcmeq], 'fveq2d', '( V ` %s ) = ( V ` %s )' % (LCM, EQ)), vlc], 'eqtrd',
             '( V ` %s ) = ( ( V ` E ) x. ( V ` %s ) )' % (LCM, Q))
    alg = st([st([vqval], 'oveq2d',
                 '( ( V ` E ) x. ( V ` %s ) ) = ( ( V ` E ) x. ( ( V ` F ) / ( V ` %s ) ) )'
                 % (Q, G)),
              st([st([evc, fvc, gvc, gvne], 'divassd',
                     '( ( ( V ` E ) x. ( V ` F ) ) / ( V ` %s ) ) = '
                     '( ( V ` E ) x. ( ( V ` F ) / ( V ` %s ) ) )' % (G, G))], 'eqcomd',
                 '( ( V ` E ) x. ( ( V ` F ) / ( V ` %s ) ) ) = '
                 '( ( ( V ` E ) x. ( V ` F ) ) / ( V ` %s ) )' % (G, G))], 'eqtrd',
             '( ( V ` E ) x. ( V ` %s ) ) = ( ( ( V ` E ) x. ( V ` F ) ) / ( V ` %s ) )' % (Q, G))
    w.qed([lhs, alg], 'eqtrd',
          '( %s -> ( V ` %s ) = ( ( ( V ` E ) x. ( V ` F ) ) / ( V ` %s ) ) )' % (A, LCM, G))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['vlcm']:
        globals()[f]().run()
