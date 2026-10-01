"""Sortie KD1: iterated derivatives of the Dirichlet-series-minus-poles function (kdpsidn)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from lin import linarith
from cl import lift

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_psidn():
    w = W('kdpsidn', 'The ` K ` -th derivative of ` -u sum A ( k ) k ^ -u z - sum_ q e. Z M / ( z - q ) ` on ` ( Re > T ) \\ Z ` : the termwise derivatives of ` kddsdn ` and ` kdpoledn ` .')
    HT = HP('T'); V = VSET()
    DSa = DS('A', 'T')
    ph = '( ( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) ) /\\ %s )' % (AGR, ZH)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    at = s([], 'simpl', '( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) )' % AGR)
    ag = s([at], 'simpld', AGR); tc = s([at], 'simprd', '( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T )')
    tr = s([tc], 'simpld', 'T e. RR'); lt = s([tc], 'simprd', '( 1 + ( 2 x. B ) ) < T')
    zh = s([], 'simpr', ZH)
    zf = s([zh], 'simp1d', 'Z e. Fin'); zcc = s([zh], 'simp2d', 'Z C_ CC'); mcc = s([zh], 'simp3d', 'W : Z --> CC')
    bp = s([s([ag], 'simp3d', '( B e. RR+ /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) )')], 'simpld', 'B e. RR+')
    br = s([bp], 'rpred', 'B e. RR')
    c = Closure(w, ph, {'T': ('RR', tr), 'B': ('RR', br)})
    lt1 = linarith(w, ph, [lt, s([bp], 'rpgt0d', '0 < B')], '( 1 + B ) < T', closure=c)
    dv0 = s([ag, s([tr, lt1], 'jca', '( T e. RR /\\ ( 1 + B ) < T )'), w.inst('kddsdv')], 'syl2anc',
            '( %s /\\ ( CC _D %s ) = ( z e. %s |-> sum_ k e. NN -u ( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u z ) ) ) )' % (HOLF(DSa, HT), DSa, HT))
    hol = s([dv0], 'simpld', HOLF(DSa, HT))
    pmD, _ = pmcc(w, ph, hol, DSa, HT)
    # V open, inside HT and CC
    je = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    fre = w.s([w.s([je], 'cnfldhaus', '%s e. Haus' % TOP), w.inst('haust1')], 'ax-mp', '%s e. Fre' % TOP)
    un = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    zcl = s([w.s([fre], 'a1i', '( %s -> %s e. Fre )' % (ph, TOP)), zcc, zf,
             w.s([un], 't1ficld', '( ( %s e. Fre /\\ Z C_ CC /\\ Z e. Fin ) -> Z e. ( Clsd ` %s ) )' % (TOP, TOP))], 'syl3anc', 'Z e. ( Clsd ` %s )' % TOP)
    vop = s([w.s([w.s([], 'hpopn', '%s e. %s' % (HT, TOP))], 'a1i', '( %s -> %s e. %s )' % (ph, HT, TOP)), zcl, w.s([un], 'difopn', '( ( %s e. %s /\\ Z e. ( Clsd ` %s ) ) -> %s e. %s )' % (HT, TOP, TOP, V, TOP))],
            'syl2anc', '%s e. %s' % (V, TOP))
    vht = w.s([w.s([], 'difss', '%s C_ %s' % (V, HT))], 'a1i', '( %s -> %s C_ %s )' % (ph, V, HT))
    htcc = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (DSa, HT)), w.inst('cncfrss')], 'syl', '%s C_ CC' % HT)
    vcc = s([vht, htcc], 'sstrd', '%s C_ CC' % V)
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    cpr = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % ph)
    A1n = '( %s /\\ n e. NN0 )' % ph
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1n, f))
    L = lambda st, ante=None: lift(w, st, ante or A1n)
    nn = t([], 'simpr', 'n e. NN0')
    n1 = t([nn, w.inst('peano2nn0')], 'syl', '( n + 1 ) e. NN0')
    MAPD = lambda x: '( z e. %s |-> %s )' % (HT, S1(x, 'z'))
    KDN = lambda x, nst: t([L(ag), L(tc), nst, w.inst('kddsdn')], 'syl3anc', '( ( CC Dn %s ) ` %s ) = %s' % (DSa, x, MAPD(x)))
    kn = KDN('n', nn); kn1 = KDN('( n + 1 )', n1)
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A1n)
    dnp = t([ccs, L(pmD), nn, w.inst('dvnp1')], 'syl3anc', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D ( ( CC Dn %s ) ` n ) )' % (DSa, DSa))
    ddht = t([kn1, dnp, t([kn], 'oveq2d', '( CC _D ( ( CC Dn %s ) ` n ) ) = ( CC _D %s )' % (DSa, MAPD('n')))], '3eqtr3rd' if False else 'T.', 'T.') if False else \
        t([t([kn1], 'eqcomd', '%s = ( ( CC Dn %s ) ` ( n + 1 ) )' % (MAPD('( n + 1 )'), DSa)), dnp, t([kn], 'oveq2d', '( CC _D ( ( CC Dn %s ) ` n ) ) = ( CC _D %s )' % (DSa, MAPD('n')))],
          '3eqtrrd' if False else '3eqtrd', '%s = ( CC _D %s )' % (MAPD('( n + 1 )'), MAPD('n')))
    ddht = t([ddht], 'eqcomd', '( CC _D %s ) = %s' % (MAPD('n'), MAPD('( n + 1 )')))
    # values of S1 on HT
    def s1c(ante, x, xst, zin):
        """( ante -> S1(x, z) e. CC ) from zin : ( ante -> z e. HT )"""
        a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        hk = a([L(hol, ante), xst, w.inst('kdholdn')], 'syl2anc', HOLF('( ( CC Dn %s ) ` %s )' % (DSa, x), HT))
        kx = a([L(ag, ante), L(tc, ante), xst, w.inst('kddsdn')], 'syl3anc', '( ( CC Dn %s ) ` %s ) = %s' % (DSa, x, MAPD(x)))
        fm = a([a([hk, w.inst('simpl')], 'syl', '( ( CC Dn %s ) ` %s ) e. ( %s -cn-> CC )' % (DSa, x, HT)), w.inst('cncff')], 'syl', '( ( CC Dn %s ) ` %s ) : %s --> CC' % (DSa, x, HT))
        fm2 = a([kx, fm], 'feq1d' if False else 'T.', 'T.') if False else a([fm, a([kx], 'feq1d', '( ( ( CC Dn %s ) ` %s ) : %s --> CC <-> %s : %s --> CC )' % (DSa, x, HT, MAPD(x), HT))], 'mpbid', '%s : %s --> CC' % (MAPD(x), HT))
        vv = a([fm2, zin], 'ffvelcdmd', '( %s ` z ) e. CC' % MAPD(x))
        ev = w.s([w.s([], 'eqid', '%s = %s' % (MAPD(x), MAPD(x)))], 'fvmpt2', '( ( z e. %s /\\ %s e. _V ) -> ( %s ` z ) = %s )' % (HT, S1(x, 'z'), MAPD(x), S1(x, 'z')))
        e2 = a([zin, w.s([w.s([], 'sumex', '%s e. _V' % S1(x, 'z'))], 'a1i', '( %s -> %s e. _V )' % (ante, S1(x, 'z'))), ev], 'syl2anc', '( %s ` z ) = %s' % (MAPD(x), S1(x, 'z')))
        return a([e2, vv], 'eqeltrrd', '%s e. CC' % S1(x, 'z'))
    Ah = '( %s /\\ z e. %s )' % (A1n, HT)
    s1h = s1c(Ah, 'n', L(nn, Ah), w.s([], 'simpr', '( %s -> z e. %s )' % (Ah, HT)))
    Av = '( %s /\\ z e. %s )' % (A1n, V)
    zv = w.s([], 'simpr', '( %s -> z e. %s )' % (Av, V))
    zvh = w.s([L(vht, Av), zv], 'sseldd', '( %s -> z e. %s )' % (Av, HT))
    s1v = s1c(Av, 'n', L(nn, Av), zvh)
    s1v1 = s1c(Av, '( n + 1 )', L(n1, Av), zvh)
    s1x = lambda ante, x: w.s([w.s([], 'sumex', '%s e. _V' % S1(x, 'z'))], 'a1i', '( %s -> %s e. _V )' % (ante, S1(x, 'z')))
    ddv = t([L(cpr), s1h, s1x(Ah, '( n + 1 )'), ddht, L(vht), jr, je, L(vop)], 'dvmptres', '( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s )' % (V, S1('n', 'z'), V, S1('( n + 1 )', 'z')))
    dnv = t([L(cpr), s1v, s1x(Av, '( n + 1 )'), ddv], 'dvmptneg', '( CC _D ( z e. %s |-> -u %s ) ) = ( z e. %s |-> -u %s )' % (V, S1('n', 'z'), V, S1('( n + 1 )', 'z')))
    # ---- poles
    PHQ = '( z e. ( CC \\ { q } ) |-> ( 1 / ( z - q ) ) )'
    MAPP = lambda x: '( z e. ( CC \\ { q } ) |-> %s )' % PQ(x, 'z')
    Aq = '( %s /\\ q e. Z )' % A1n
    u = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    qz = u([], 'simpr', 'q e. Z')
    qc = u([L(zcc, Aq), qz], 'sseldd', 'q e. CC')
    mq = u([L(mcc, Aq), qz], 'ffvelcdmd', '( W ` q ) e. CC')
    nq = L(nn, Aq); n1q = L(n1, Aq)
    kp = u([qc, nq, w.inst('kdpoledn')], 'syl2anc', '( ( CC Dn %s ) ` n ) = %s' % (PHQ, MAPP('n')))
    kp1 = u([qc, n1q, w.inst('kdpoledn')], 'syl2anc', '( ( CC Dn %s ) ` ( n + 1 ) ) = %s' % (PHQ, MAPP('( n + 1 )')))
    # phi_q e. ( CC ^pm CC )
    Aqz = '( %s /\\ z e. ( CC \\ { q } ) )' % Aq
    zq = w.s([], 'simpr', '( %s -> z e. ( CC \\ { q } ) )' % Aqz)
    zqc = w.s([zq, w.inst('eldifi')], 'syl', '( %s -> z e. CC )' % Aqz)
    zqn = w.s([zq, w.inst('eldifsni')], 'syl', '( %s -> z =/= q )' % Aqz)
    wq = w.s([zqc, L(qc, Aqz)], 'subcld', '( %s -> ( z - q ) e. CC )' % Aqz)
    wqn = w.s([zqc, L(qc, Aqz), zqn], 'subne0d', '( %s -> ( z - q ) =/= 0 )' % Aqz)
    phf = u([w.s([wq, wqn], 'reccld', '( %s -> ( 1 / ( z - q ) ) e. CC )' % Aqz)], 'fmptd', '%s : ( CC \\ { q } ) --> CC' % PHQ)
    cx = w.s([], 'cnex', 'CC e. _V')
    pmq = u([w.s([w.s([cx, cx], 'pm3.2i', '( CC e. _V /\\ CC e. _V )')], 'a1i', '( %s -> ( CC e. _V /\\ CC e. _V ) )' % Aq),
             u([phf, w.s([w.s([], 'difss', '( CC \\ { q } ) C_ CC')], 'a1i', '( %s -> ( CC \\ { q } ) C_ CC )' % Aq)], 'jca', '( %s : ( CC \\ { q } ) --> CC /\\ ( CC \\ { q } ) C_ CC )' % PHQ),
             w.inst('elpm2r')], 'syl2anc', '%s e. ( CC ^pm CC )' % PHQ)
    ccq = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % Aq)
    dnq = u([ccq, pmq, nq, w.inst('dvnp1')], 'syl3anc', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D ( ( CC Dn %s ) ` n ) )' % (PHQ, PHQ))
    ddq = u([u([kp1], 'eqcomd', '%s = ( ( CC Dn %s ) ` ( n + 1 ) )' % (MAPP('( n + 1 )'), PHQ)), dnq, u([kp], 'oveq2d', '( CC _D ( ( CC Dn %s ) ` n ) ) = ( CC _D %s )' % (PHQ, MAPP('n')))],
            '3eqtrd', '%s = ( CC _D %s )' % (MAPP('( n + 1 )'), MAPP('n')))
    ddq = u([ddq], 'eqcomd', '( CC _D %s ) = %s' % (MAPP('n'), MAPP('( n + 1 )')))
    def pqc(ante, x, xst, zc_, qc_, zn_):
        a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        wc_ = a([zc_, qc_], 'subcld', '( z - q ) e. CC'); wn_ = a([zc_, qc_, zn_], 'subne0d', '( z - q ) =/= 0')
        x1 = a([xst, w.inst('peano2nn0')], 'syl', '( %s + 1 ) e. NN0' % x)
        num = a([a([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % ante), xst], 'expcld', '( -u 1 ^ %s ) e. CC' % x),
                 a([a([xst], 'faccld', '( ! ` %s ) e. NN' % x)], 'nncnd', '( ! ` %s ) e. CC' % x)], 'mulcld', '( ( -u 1 ^ %s ) x. ( ! ` %s ) ) e. CC' % (x, x))
        return a([num, a([wc_, x1], 'expcld', '( ( z - q ) ^ ( %s + 1 ) ) e. CC' % x), a([wc_, wn_, a([x1], 'nn0zd', '( %s + 1 ) e. ZZ' % x)], 'expne0d', '( ( z - q ) ^ ( %s + 1 ) ) =/= 0' % x)],
                 'divcld', '%s e. CC' % PQ(x, 'z'))
    pqn = pqc(Aqz, 'n', L(nq, Aqz), zqc, L(qc, Aqz), zqn)
    pqx = w.s([w.s([], 'ovex', '%s e. _V' % PQ('( n + 1 )', 'z'))], 'a1i', '( %s -> %s e. _V )' % (Aqz, PQ('( n + 1 )', 'z')))
    # V C_ ( CC \ { q } )
    Aqv = '( %s /\\ z e. %s )' % (Aq, V)
    zvq = w.s([], 'simpr', '( %s -> z e. %s )' % (Aqv, V))
    zvc = w.s([L(vcc, Aqv), zvq], 'sseldd', '( %s -> z e. CC )' % Aqv)
    znz = w.s([zvq, w.inst('eldifn')], 'syl', '( %s -> -. z e. Z )' % Aqv)
    qnz = w.s([w.s([L(qz, Aqv), znz], 'jca', '( %s -> ( q e. Z /\\ -. z e. Z ) )' % Aqv), w.inst('nelne2')], 'syl', '( %s -> q =/= z )' % Aqv)
    zneq = w.s([qnz], 'necomd', '( %s -> z =/= q )' % Aqv)
    zinq = w.s([w.s([zvc, zneq], 'jca', '( %s -> ( z e. CC /\\ z =/= q ) )' % Aqv), w.s([], 'eldifsn', '( z e. ( CC \\ { q } ) <-> ( z e. CC /\\ z =/= q ) )')], 'sylibr', '( %s -> z e. ( CC \\ { q } ) )' % Aqv)
    vq = u([w.s([zinq], 'ex', '( %s -> ( z e. %s -> z e. ( CC \\ { q } ) ) )' % (Aq, V))], 'ssrdv', '%s C_ ( CC \\ { q } )' % V)
    ddqv = u([L(cpr, Aq), pqn, pqx, ddq, vq, jr, je, L(vop, Aq)], 'dvmptres', '( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s )' % (V, PQ('n', 'z'), V, PQ('( n + 1 )', 'z')))
    pqnv = pqc(Aqv, 'n', L(nq, Aqv), zvc, L(qc, Aqv), zneq)
    pqxv = w.s([w.s([], 'ovex', '%s e. _V' % PQ('( n + 1 )', 'z'))], 'a1i', '( %s -> %s e. _V )' % (Aqv, PQ('( n + 1 )', 'z')))
    dmq = u([L(cpr, Aq), pqnv, pqxv, ddqv, mq], 'dvmptcmul', '( CC _D ( z e. %s |-> ( ( W ` q ) x. %s ) ) ) = ( z e. %s |-> ( ( W ` q ) x. %s ) )' % (V, PQ('n', 'z'), V, PQ('( n + 1 )', 'z')))
    # ---- the finite sum over the poles
    A3 = '( %s /\\ q e. Z /\\ z e. %s )' % (A1n, V)
    a3 = w.s([], 'df-3an', '( %s <-> %s )' % (A3, Aqv))
    MPn = '( ( W ` q ) x. %s )' % PQ('n', 'z'); MPn1 = '( ( W ` q ) x. %s )' % PQ('( n + 1 )', 'z')
    mpn_q = w.s([L(mq, Aqv), pqnv], 'mulcld', '( %s -> %s e. CC )' % (Aqv, MPn))
    pqnv1 = pqc(Aqv, '( n + 1 )', L(n1q, Aqv), zvc, L(qc, Aqv), zneq)
    mpn1_q = w.s([L(mq, Aqv), pqnv1], 'mulcld', '( %s -> %s e. CC )' % (Aqv, MPn1))
    fa = w.s([a3, mpn_q], 'sylbi', '( %s -> %s e. CC )' % (A3, MPn))
    fb = w.s([a3, mpn1_q], 'sylbi', '( %s -> %s e. CC )' % (A3, MPn1))
    SUM = t([jr, je, L(cpr), L(vop), L(zf), fa, fb, dmq], 'dvmptfsum' if False else 'T.', 'T.') if False else \
        w.s([jr, je, L(cpr), L(vop), L(zf), fa, fb, dmq], 'dvmptfsum', '( %s -> ( CC _D ( z e. %s |-> sum_ q e. Z %s ) ) = ( z e. %s |-> sum_ q e. Z %s ) )' % (A1n, V, MPn, V, MPn1))
    # ---- combine
    Avq = '( %s /\\ q e. Z )' % Av
    an = w.s([], 'an32', '( %s <-> %s )' % (Avq, Aqv))
    sm = w.s([L(zf, Av), w.s([an, mpn_q], 'sylbi', '( %s -> %s e. CC )' % (Avq, MPn))], 'fsumcl', '( %s -> sum_ q e. Z %s e. CC )' % (Av, MPn))
    smx = w.s([w.s([], 'sumex', 'sum_ q e. Z %s e. _V' % MPn1)], 'a1i', '( %s -> sum_ q e. Z %s e. _V )' % (Av, MPn1))
    nx1 = w.s([w.s([], 'negex', '-u %s e. _V' % S1('( n + 1 )', 'z'))], 'a1i', '( %s -> -u %s e. _V )' % (Av, S1('( n + 1 )', 'z')))
    MAPS = lambda x: '( z e. %s |-> %s )' % (V, PSIK(x, 'z'))
    comb = t([L(cpr), w.s([s1v], 'negcld', '( %s -> -u %s e. CC )' % (Av, S1('n', 'z'))), nx1, dnv, sm, smx, SUM], 'dvmptsub', '( CC _D %s ) = %s' % (MAPS('n'), MAPS('( n + 1 )')))
    # ---- Psi e. ( CC ^pm CC )
    Ap = '( %s /\\ z e. %s )' % (ph, V)
    zv0 = w.s([], 'simpr', '( %s -> z e. %s )' % (Ap, V))
    zh0 = w.s([L(vht, Ap), zv0], 'sseldd', '( %s -> z e. %s )' % (Ap, HT))
    z0 = w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % Ap)
    s10 = s1c(Ap, '0', z0, zh0)
    Apq = '( %s /\\ q e. Z )' % Ap
    zc0 = w.s([L(vcc, Apq), w.s([zv0], 'adantr', '( %s -> z e. %s )' % (Apq, V))], 'sseldd', '( %s -> z e. CC )' % Apq)
    qz0 = w.s([], 'simpr', '( %s -> q e. Z )' % Apq)
    qc0 = w.s([L(zcc, Apq), qz0], 'sseldd', '( %s -> q e. CC )' % Apq)
    zn0 = w.s([w.s([w.s([qz0, w.s([w.s([zv0], 'adantr', '( %s -> z e. %s )' % (Apq, V)), w.inst('eldifn')], 'syl', '( %s -> -. z e. Z )' % Apq)], 'jca', '( %s -> ( q e. Z /\\ -. z e. Z ) )' % Apq),
                     w.inst('nelne2')], 'syl', '( %s -> q =/= z )' % Apq)], 'necomd', '( %s -> z =/= q )' % Apq)
    pq0 = pqc(Apq, '0', w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % Apq), zc0, qc0, zn0)
    m0 = w.s([L(mcc, Apq), qz0], 'ffvelcdmd', '( %s -> ( W ` q ) e. CC )' % Apq)
    ps0 = w.s([w.s([s10], 'negcld', '( %s -> -u %s e. CC )' % (Ap, S1('0', 'z'))), w.s([L(zf, Ap), w.s([m0, pq0], 'mulcld', '( %s -> ( ( W ` q ) x. %s ) e. CC )' % (Apq, PQ('0', 'z')))], 'fsumcl',
                                                                                            '( %s -> sum_ q e. Z ( ( W ` q ) x. %s ) e. CC )' % (Ap, PQ('0', 'z')))], 'subcld', '( %s -> %s e. CC )' % (Ap, PSIK('0', 'z')))
    psf = s([ps0], 'fmptd', '%s : %s --> CC' % (PSI(), V))
    cx = w.s([], 'cnex', 'CC e. _V')
    pmP = s([w.s([w.s([cx, cx], 'pm3.2i', '( CC e. _V /\\ CC e. _V )')], 'a1i', '( %s -> ( CC e. _V /\\ CC e. _V ) )' % ph), s([psf, vcc], 'jca', '( %s : %s --> CC /\\ %s C_ CC )' % (PSI(), V, V)),
              w.inst('elpm2r')], 'syl2anc', '%s e. ( CC ^pm CC )' % PSI())
    # ---- induction
    PSx = lambda x: '( ( CC Dn %s ) ` %s ) = %s' % (PSI(), x, MAPS(x))
    subs = {}
    for nm, tt in (('0', '0'), ('n', 'n'), ('n1', '( n + 1 )'), ('K', 'K')):
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (tt, tt))
        st, new = w.wcongr(PSx('x'), {'x': tt}, 'x = %s' % tt, {'x': idx})
        assert new == PSx(tt), new
        subs[nm] = st
    ccs0 = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % ph)
    base = s([ccs0, pmP, w.inst('dvn0')], 'syl2anc', PSx('0'))
    A1 = '( %s /\\ %s )' % (A1n, PSx('n'))
    v = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    ih = v([], 'simpr', PSx('n'))
    d1 = v([L(ccs0, A1), L(pmP, A1), L(nn, A1), w.inst('dvnp1')], 'syl3anc', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D ( ( CC Dn %s ) ` n ) )' % (PSI(), PSI()))
    d2 = v([ih], 'oveq2d', '( CC _D ( ( CC Dn %s ) ` n ) ) = ( CC _D %s )' % (PSI(), MAPS('n')))
    step = v([d1, d2, L(comb, A1)], '3eqtrd', PSx('( n + 1 )'))
    idx1 = w.s([], 'id', '( x = 1 -> x = 1 )')
    st1, new1 = w.wcongr(PSx('x'), {'x': '1'}, 'x = 1', {'x': idx1})
    indK = w.s([subs['0'], subs['n'], subs['n1'], subs['K'], base, step], 'nn0indd', '( ( %s /\\ K e. NN0 ) -> %s )' % (ph, PSx('K')))
    ind1 = w.s([subs['0'], subs['n'], subs['n1'], st1, base, step], 'nn0indd', '( ( %s /\\ 1 e. NN0 ) -> %s )' % (ph, PSx('1')))
    p1 = s([w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % ph), w.s([ind1], 'ex', '( %s -> ( 1 e. NN0 -> %s ) )' % (ph, PSx('1')))], 'mpd', PSx('1'))
    dv1 = s([ccs0, pmP, w.inst('dvn1')], 'syl2anc', '( ( CC Dn %s ) ` 1 ) = ( CC _D %s )' % (PSI(), PSI()))
    dvm = s([dv1, p1], 'eqtr3d', '( CC _D %s ) = %s' % (PSI(), MAPS('1')))
    Ap1 = '( %s /\\ z e. %s )' % (ph, V)
    vx1 = w.s([w.s([], 'ovex', '%s e. _V' % PSIK('1', 'z'))], 'a1i', '( %s -> %s e. _V )' % (Ap1, PSIK('1', 'z')))
    dmm = s([s([vx1], 'ralrimiva', 'A. z e. %s %s e. _V' % (V, PSIK('1', 'z'))), w.inst('dmmptg')], 'syl', 'dom %s = %s' % (MAPS('1'), V))
    dm2 = s([s([dvm], 'dmeqd', 'dom ( CC _D %s ) = dom %s' % (PSI(), MAPS('1'))), dmm], 'eqtrd', 'dom ( CC _D %s ) = %s' % (PSI(), V))
    cnt = s([s([ccs0, psf, vcc], '3jca', '( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC )' % (PSI(), V, V)), dm2, w.inst('dvcn')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (PSI(), V))
    hpsi = s([cnt, s([dm2, w.inst('eqimss2')], 'syl', '%s C_ dom ( CC _D %s )' % (V, PSI()))], 'jca', HOLF(PSI(), V))
    A0 = '( %s /\\ K e. NN0 )' % ph
    w.qed([w.s([hpsi], 'adantr', '( %s -> %s )' % (A0, HOLF(PSI(), V))), indK], 'jca', S['kdpsidn'])
    return run(w)





if __name__ == '__main__':
    gen_psidn()
