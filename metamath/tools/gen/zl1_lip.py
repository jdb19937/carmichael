"""ZL1: the mean-value bound on [ K , K + 1 ] for a function on RR+ with a given
derivative (zl1lip), set.mm's dvlip through a restriction (C3's cxpmvt route)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl1lib import *

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    return w.run()


ICC = '( K [,] ( K + 1 ) )'
IOO = '( K (,) ( K + 1 ) )'
JR = '( %s |`t RR )' % TOP
RETOP = '( topGen ` ran (,) )'
H = '( F |` %s )' % ICC

if not only or 'zl1lip' in only:
    w = W('zl1lip', 'The mean-value bound between ` K ` and ` K + 1 ` for a complex function on the positive '
          'reals whose derivative is bounded by ` M ` on ` ( K (,) ( K + 1 ) ) ` ( ~ dvlip on the restriction '
          'to ` ( K [,] ( K + 1 ) ) ` ).')
    A0 = STATEMENTS['zl1lip'].split(' -> ( abs ` ( ( F ` ( K + 1 ) )')[0][2:]
    ff = w.s([], 'simpl1', '( %s -> F : RR+ --> CC )' % A0)
    gf = w.s([], 'simpl2', '( %s -> G : RR+ --> CC )' % A0)
    dfg = w.s([], 'simpl3', '( %s -> ( RR _D F ) = G )' % A0)
    krp = w.s([], 'simpr1', '( %s -> K e. RR+ )' % A0)
    mr = w.s([], 'simpr2', '( %s -> M e. RR )' % A0)
    bnd = w.s([], 'simpr3', '( %s -> A. t e. %s ( abs ` ( G ` t ) ) <_ M )' % (A0, IOO))
    kr = w.s([krp], 'rpred', '( %s -> K e. RR )' % A0)
    r1 = a1(w, A0, '1re', '1 e. RR')
    k1r = w.s([kr, r1], 'readdcld', '( %s -> ( K + 1 ) e. RR )' % A0)
    kpos = w.s([krp], 'rpgt0d', '( %s -> 0 < K )' % A0)
    dmg = w.s([gf, w.inst('fdm')], 'syl', '( %s -> dom G = RR+ )' % A0)
    dmd = w.s([w.s([dfg], 'dmeqd', '( %s -> dom ( RR _D F ) = dom G )' % A0), dmg], 'eqtrd', '( %s -> dom ( RR _D F ) = RR+ )' % A0)
    rrcc = a1(w, A0, 'ax-resscn', 'RR C_ CC')
    rpre = a1(w, A0, 'rpssre', 'RR+ C_ RR')
    fcn = w.s([w.s([w.s([rrcc, ff, rpre], '3jca', '( %s -> ( RR C_ CC /\\ F : RR+ --> CC /\\ RR+ C_ RR ) )' % A0), dmd], 'jca',
                   '( %s -> ( ( RR C_ CC /\\ F : RR+ --> CC /\\ RR+ C_ RR ) /\\ dom ( RR _D F ) = RR+ ) )' % A0), w.inst('dvcn')], 'syl',
              '( %s -> F e. ( RR+ -cn-> CC ) )' % A0)
    # ( K [,] ( K + 1 ) ) C_ RR+
    Aic = '( %s /\\ b e. %s )' % (A0, ICC)
    bic = w.s([], 'simpr', '( %s -> b e. %s )' % (Aic, ICC))
    icre = w.s([kr, k1r, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, ICC))
    bre = w.s([w.s([icre], 'adantr', '( %s -> %s C_ RR )' % (Aic, ICC)), bic], 'sseldd', '( %s -> b e. RR )' % Aic)
    icbi = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( b e. %s <-> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) ) )' % (A0, ICC))
    icp = w.s([bic, w.s([icbi], 'adantr', '( %s -> ( b e. %s <-> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) ) )' % (Aic, ICC))], 'mpbid',
              '( %s -> ( b e. RR /\\ K <_ b /\\ b <_ ( K + 1 ) ) )' % Aic)
    kleb = w.s([icp, w.inst('simp2')], 'syl', '( %s -> K <_ b )' % Aic)
    bpos = w.s([a1(w, Aic, '0re', '0 e. RR'), w.s([kr], 'adantr', '( %s -> K e. RR )' % Aic), bre, w.s([kpos], 'adantr', '( %s -> 0 < K )' % Aic), kleb],
               'ltletrd', '( %s -> 0 < b )' % Aic)
    icrp = w.s([bre, bpos], 'elrpd', '( %s -> b e. RR+ )' % Aic)
    icss = w.s([w.s([icrp], 'ex', '( %s -> ( b e. %s -> b e. RR+ ) )' % (A0, ICC))], 'ssrdv', '( %s -> %s C_ RR+ )' % (A0, ICC))
    # the restriction is continuous
    hc = w.s([fcn, w.s([icss, w.inst('rescncf')], 'syl', '( %s -> ( F e. ( RR+ -cn-> CC ) -> %s e. ( %s -cn-> CC ) ) )' % (A0, H, ICC))], 'mpd',
             '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, H, ICC))
    # its derivative is G on the open interval
    ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ejr = w.s([], 'eqid', '%s = %s' % (JR, JR))
    icsr = w.s([icss, rpre], 'sstrd', '( %s -> %s C_ RR )' % (A0, ICC))
    dvr = w.s([w.s([w.s([rrcc, ff], 'jca', '( %s -> ( RR C_ CC /\\ F : RR+ --> CC ) )' % A0), w.s([rpre, icsr], 'jca', '( %s -> ( RR+ C_ RR /\\ %s C_ RR ) )' % (A0, ICC))],
                   'jca', '( %s -> ( ( RR C_ CC /\\ F : RR+ --> CC ) /\\ ( RR+ C_ RR /\\ %s C_ RR ) ) )' % (A0, ICC)),
               w.s([ek, ejr], 'dvres', '( ( ( RR C_ CC /\\ F : RR+ --> CC ) /\\ ( RR+ C_ RR /\\ %s C_ RR ) ) -> ( RR _D %s ) = ( ( RR _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (ICC, H, JR, ICC))],
              'syl', '( %s -> ( RR _D %s ) = ( ( RR _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (A0, H, JR, ICC))
    tg = w.s([], 'tgioo4', '%s = %s' % (RETOP, JR))
    ntr0 = w.s([kr, k1r, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, RETOP, ICC, IOO))
    jeq = w.s([w.s([tg], 'eqcomi', '%s = %s' % (JR, RETOP))], 'a1i', '( %s -> %s = %s )' % (A0, JR, RETOP))
    ntr = w.s([w.s([w.s([jeq], 'fveq2d', '( %s -> ( int ` %s ) = ( int ` %s ) )' % (A0, JR, RETOP))], 'fveq1d',
                   '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` %s ) ` %s ) )' % (A0, JR, ICC, RETOP, ICC)), ntr0], 'eqtrd',
              '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, JR, ICC, IOO))
    dvr2 = w.s([dvr, w.s([dfg, ntr], 'reseq12d', '( %s -> ( ( RR _D F ) |` ( ( int ` %s ) ` %s ) ) = ( G |` %s ) )' % (A0, JR, ICC, IOO))], 'eqtrd',
               '( %s -> ( RR _D %s ) = ( G |` %s ) )' % (A0, H, IOO))
    iossic = a1(w, A0, 'ioossicc', '%s C_ %s' % (IOO, ICC))
    iossrp = w.s([iossic, icss], 'sstrd', '( %s -> %s C_ RR+ )' % (A0, IOO))
    gres = w.s([gf, iossrp, w.inst('fssres')], 'syl2anc', '( %s -> ( G |` %s ) : %s --> CC )' % (A0, IOO, IOO))
    hD = w.s([w.s([dvr2], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom ( G |` %s ) )' % (A0, H, IOO)), w.s([gres, w.inst('fdm')], 'syl', '( %s -> dom ( G |` %s ) = %s )' % (A0, IOO, IOO))],
             'eqtrd', '( %s -> dom ( RR _D %s ) = %s )' % (A0, H, IOO))
    # the bound
    Ax = '( %s /\\ x e. %s )' % (A0, IOO)
    xio = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, IOO))
    dvx = w.s([w.s([w.s([dvr2], 'adantr', '( %s -> ( RR _D %s ) = ( G |` %s ) )' % (Ax, H, IOO))], 'fveq1d',
                   '( %s -> ( ( RR _D %s ) ` x ) = ( ( G |` %s ) ` x ) )' % (Ax, H, IOO)),
               w.s([xio, w.inst('fvres')], 'syl', '( %s -> ( ( G |` %s ) ` x ) = ( G ` x ) )' % (Ax, IOO))], 'eqtrd',
              '( %s -> ( ( RR _D %s ) ` x ) = ( G ` x ) )' % (Ax, H))
    rsp = w.s([w.s([w.s([], 'fveq2', '( t = x -> ( G ` t ) = ( G ` x ) )')], 'fveq2d', '( t = x -> ( abs ` ( G ` t ) ) = ( abs ` ( G ` x ) ) )')], 'breq1d',
              '( t = x -> ( ( abs ` ( G ` t ) ) <_ M <-> ( abs ` ( G ` x ) ) <_ M ) )')
    rs2 = w.s([rsp], 'rspcv', '( x e. %s -> ( A. t e. %s ( abs ` ( G ` t ) ) <_ M -> ( abs ` ( G ` x ) ) <_ M ) )' % (IOO, IOO))
    bx = w.s([xio, w.s([bnd], 'adantr', '( %s -> A. t e. %s ( abs ` ( G ` t ) ) <_ M )' % (Ax, IOO)), rs2], 'sylc', '( %s -> ( abs ` ( G ` x ) ) <_ M )' % Ax)
    hL = w.s([w.s([dvx], 'fveq2d', '( %s -> ( abs ` ( ( RR _D %s ) ` x ) ) = ( abs ` ( G ` x ) ) )' % (Ax, H)), bx], 'eqbrtrd',
             '( %s -> ( abs ` ( ( RR _D %s ) ` x ) ) <_ M )' % (Ax, H))
    # the endpoints
    kle1 = w.s([kr, k1r, w.s([kr], 'ltp1d', '( %s -> K < ( K + 1 ) )' % A0)], 'ltled', '( %s -> K <_ ( K + 1 ) )' % A0)
    kic = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc', '( %s -> ( K e. %s <-> ( K e. RR /\\ K <_ K /\\ K <_ ( K + 1 ) ) ) )' % (A0, ICC))
    kmem = w.s([w.s([kr, w.s([kr], 'leidd', '( %s -> K <_ K )' % A0), kle1], '3jca', '( %s -> ( K e. RR /\\ K <_ K /\\ K <_ ( K + 1 ) ) )' % A0), kic],
               'mpbird', '( %s -> K e. %s )' % (A0, ICC))
    k1ic = w.s([kr, k1r, w.inst('elicc2')], 'syl2anc',
               '( %s -> ( ( K + 1 ) e. %s <-> ( ( K + 1 ) e. RR /\\ K <_ ( K + 1 ) /\\ ( K + 1 ) <_ ( K + 1 ) ) ) )' % (A0, ICC))
    k1mem = w.s([w.s([k1r, kle1, w.s([k1r], 'leidd', '( %s -> ( K + 1 ) <_ ( K + 1 ) )' % A0)], '3jca',
                     '( %s -> ( ( K + 1 ) e. RR /\\ K <_ ( K + 1 ) /\\ ( K + 1 ) <_ ( K + 1 ) ) )' % A0), k1ic], 'mpbird', '( %s -> ( K + 1 ) e. %s )' % (A0, ICC))
    lip = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.s([k1mem, kmem], 'jca', '( %s -> ( ( K + 1 ) e. %s /\\ K e. %s ) )' % (A0, ICC, ICC))], 'jca',
              '( %s -> ( %s /\\ ( ( K + 1 ) e. %s /\\ K e. %s ) ) )' % (A0, A0, ICC, ICC))
    dvl = w.s([kr, k1r, hc, hD, mr, hL], 'dvlip',
              '( ( %s /\\ ( ( K + 1 ) e. %s /\\ K e. %s ) ) -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ ( M x. ( abs ` ( ( K + 1 ) - K ) ) ) )' % (A0, ICC, ICC, H, H))
    dvl2 = w.s([lip, dvl], 'syl', '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ ( M x. ( abs ` ( ( K + 1 ) - K ) ) ) )' % (A0, H, H))
    kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
    onec = a1(w, A0, 'ax-1cn', '1 e. CC')
    gap = w.s([w.s([w.s([kc, onec], 'pncan2d', '( %s -> ( ( K + 1 ) - K ) = 1 )' % A0)], 'fveq2d', '( %s -> ( abs ` ( ( K + 1 ) - K ) ) = ( abs ` 1 ) )' % A0),
               a1(w, A0, 'abs1', '( abs ` 1 ) = 1')], 'eqtrd', '( %s -> ( abs ` ( ( K + 1 ) - K ) ) = 1 )' % A0)
    rhs = w.s([w.s([gap], 'oveq2d', '( %s -> ( M x. ( abs ` ( ( K + 1 ) - K ) ) ) = ( M x. 1 ) )' % A0),
               w.s([w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)], 'mulridd', '( %s -> ( M x. 1 ) = M )' % A0)], 'eqtrd',
              '( %s -> ( M x. ( abs ` ( ( K + 1 ) - K ) ) ) = M )' % A0)
    v1 = w.s([k1mem, w.inst('fvres')], 'syl', '( %s -> ( %s ` ( K + 1 ) ) = ( F ` ( K + 1 ) ) )' % (A0, H))
    v0 = w.s([kmem, w.inst('fvres')], 'syl', '( %s -> ( %s ` K ) = ( F ` K ) )' % (A0, H))
    lhs = w.s([w.s([v1, v0], 'oveq12d', '( %s -> ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) = ( ( F ` ( K + 1 ) ) - ( F ` K ) ) )' % (A0, H, H))], 'fveq2d',
              '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) = ( abs ` ( ( F ` ( K + 1 ) ) - ( F ` K ) ) ) )' % (A0, H, H))
    st = w.s([dvl2, rhs], 'breqtrd', '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ M )' % (A0, H, H))
    w.qed([lhs, st], 'eqbrtrrd', '( %s -> ( abs ` ( ( F ` ( K + 1 ) ) - ( F ` K ) ) ) <_ M )' % A0)
    go(w)
