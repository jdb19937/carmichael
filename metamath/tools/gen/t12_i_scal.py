"""T12: scalesF at the machine (Lean ` scalesF_runs ` ) and its arithmetic.

  t12nlogbl   ` Nat.log 2 a <_ bl a `
  t12pow3     ` 1 + 7 b <_ 2 ^ ( 3 b ) ` (Bernoulli, for Lean's ` ninetynine_lt ` )
  t12mullt    ` a < 2 ^ m ` , ` c < 2 ^ n ` give ` a c < 2 ^ ( m + n ) `
  t12fldivle  ` a <_ k x ` gives ` a / k <_ x ` for the floor of the quotient
  sctmval     the value of ~ df-sctm
  tmiscal     Lean's ` scalesF_runs `

    MM_DB=sorties/t12.mm python3 tools/gen/t12_i_scal.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq, nlinarith
from cl import Closure
from t10_n_rgf import tmbn
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
ST_NLOGBL = '( A e. NN0 -> ( 2 Nlog A ) <_ ( bl ` A ) )'
ST_POW3 = '( B e. NN0 -> ( 1 + ( 7 x. B ) ) <_ ( 2 ^ ( 3 x. B ) ) )'
ST_MULLT = ('( ( ( ( A e. NN0 /\\ C e. NN0 ) /\\ ( M e. NN0 /\\ N e. NN0 ) ) /\\ ( A < ( 2 ^ M ) /\\ C < ( 2 ^ N ) ) ) -> '
            '( A x. C ) < ( 2 ^ ( M + N ) ) )')
ST_FLDIVLE = '( ( ( A e. NN0 /\\ K e. NN ) /\\ ( X e. RR /\\ A <_ ( K x. X ) ) ) -> ( |_ ` ( A / K ) ) <_ X )'
ST_SCTMVAL = '( ( C e. NN0 /\\ K e. NN /\\ N e. NN0 ) -> %s = %s )' % (SC_, SCTUP_('C', 'K', 'N'))


def t12nlogbl():
    lab = 't12nlogbl'
    w = W(lab, 'Lean\'s ` Nat.log 2 a <_ bl a ` (~ df-bwbl : ` bl a = Nat.log 2 a + 1 ` for ` a =/= 0 ` , both ` 0 ` at ` 0 ` ).')
    s = w.s
    ph = 'A e. NN'
    an = s([], 'id', '( A e. NN -> A e. NN )')
    bl1 = s([an, w.inst('blnlog')], 'syl', '( A e. NN -> ( 2 Nlog A ) = ( ( bl ` A ) - 1 ) )')
    blc = s([s([an], 'nnnn0d', '( A e. NN -> A e. NN0 )'), w.inst('blcl')], 'syl', '( A e. NN -> ( bl ` A ) e. NN0 )')
    cl = Closure(w, ph, {})
    cl.leaf('( bl ` A )', 'NN0', blc)
    nlc = s([closed(w, ph, '2nn0', '2 e. NN0'), s([an], 'nnnn0d', '( A e. NN -> A e. NN0 )'), w.inst('nlogcl')], 'syl2anc',
            '( A e. NN -> ( 2 Nlog A ) e. NN0 )')
    cl.leaf('( 2 Nlog A )', 'NN0', nlc)
    a1 = linarith(w, ph, [bl1], '( 2 Nlog A ) <_ ( bl ` A )', closure=cl)
    z = 'A = 0'
    n0 = s([s([s([], 'id', '( A = 0 -> A = 0 )')], 'oveq2d', '( A = 0 -> ( 2 Nlog A ) = ( 2 Nlog 0 ) )'), nlog0(w, z)], 'eqtrd',
           '( A = 0 -> ( 2 Nlog A ) = 0 )')
    b0 = s([s([s([], 'id', '( A = 0 -> A = 0 )')], 'fveq2d', '( A = 0 -> ( bl ` A ) = ( bl ` 0 ) )'), closed(w, z, 'bl0', '( bl ` 0 ) = 0')],
           'eqtrd', '( A = 0 -> ( bl ` A ) = 0 )')
    e = s([n0, s([b0], 'eqcomd', '( A = 0 -> 0 = ( bl ` A ) )')], 'eqtrd', '( A = 0 -> ( 2 Nlog A ) = ( bl ` A ) )')
    r = s([s([n0, closed(w, z, '0re', '0 e. RR')], 'eqeltrd', '( A = 0 -> ( 2 Nlog A ) e. RR )')], 'leidd',
          '( A = 0 -> ( 2 Nlog A ) <_ ( 2 Nlog A ) )')
    a2 = s([r, e], 'breqtrd', '( A = 0 -> ( 2 Nlog A ) <_ ( bl ` A ) )')
    j2 = s([a1, a2], 'jaoi', '( ( A e. NN \\/ A = 0 ) -> ( 2 Nlog A ) <_ ( bl ` A ) )')
    w.qed([s([], 'elnn0', '( A e. NN0 <-> ( A e. NN \\/ A = 0 ) )'), j2], 'sylbi', ST_NLOGBL)
    return w.run()


def nlog0(w, ph):
    from t12_g_sc0 import nlog0 as n0
    return n0(w, ph)


def t12pow3():
    lab = 't12pow3'
    ph = 'B e. NN0'
    w = W(lab, 'Bernoulli at ` 8 = 2 ^ 3 ` : ` 1 + 7 b <_ 2 ^ ( 3 b ) ` (~ bernneq ; for Lean\'s ` ninetynine_lt ` ).')
    s = w.s
    bn = s([], 'id', '( B e. NN0 -> B e. NN0 )')
    le7 = linarith(w, ph, [], '-u 1 <_ 7', closure=Closure(w, ph, {}))
    bb = s([closed(w, ph, '7re', '7 e. RR'), bn, le7, w.inst('bernneq')], 'syl3anc',
           '( %s -> ( 1 + ( 7 x. B ) ) <_ ( ( 1 + 7 ) ^ B ) )' % ph)
    e8 = s([s([], '7p1e8', '( 7 + 1 ) = 8')], 'addcomli', '( 1 + 7 ) = 8')
    p8 = s([s([e8], 'oveq1i', '( ( 1 + 7 ) ^ B ) = ( 8 ^ B )')], 'a1i', '( %s -> ( ( 1 + 7 ) ^ B ) = ( 8 ^ B ) )' % ph)
    em = s([closed(w, ph, '2cn', '2 e. CC'), closed(w, ph, '3nn0', '3 e. NN0'), bn, w.inst('expmul')], 'syl3anc',
           '( %s -> ( 2 ^ ( 3 x. B ) ) = ( ( 2 ^ 3 ) ^ B ) )' % ph)
    c8 = s([s([s([], 'cu2', '( 2 ^ 3 ) = 8')], 'oveq1i', '( ( 2 ^ 3 ) ^ B ) = ( 8 ^ B )')], 'a1i', '( %s -> ( ( 2 ^ 3 ) ^ B ) = ( 8 ^ B ) )' % ph)
    e2 = s([em, c8], 'eqtrd', '( %s -> ( 2 ^ ( 3 x. B ) ) = ( 8 ^ B ) )' % ph)
    r = s([bb, s([p8, s([e2], 'eqcomd', '( %s -> ( 8 ^ B ) = ( 2 ^ ( 3 x. B ) ) )' % ph)], 'eqtrd',
                 '( %s -> ( ( 1 + 7 ) ^ B ) = ( 2 ^ ( 3 x. B ) ) )' % ph)], 'breqtrd', '( %s -> ( 1 + ( 7 x. B ) ) <_ ( 2 ^ ( 3 x. B ) ) )' % ph)
    w.qed([r, w.inst('biid')], 'mpbi', ST_POW3)
    return w.run()


def t12mullt():
    lab = 't12mullt'
    T = ((('A e. NN0', 'C e. NN0'), ('M e. NN0', 'N e. NN0')), ('A < ( 2 ^ M )', 'C < ( 2 ^ N )'))
    ph = cj(T)
    w = W(lab, 'The product of numbers below ` 2 ^ m ` and ` 2 ^ n ` is below ` 2 ^ ( m + n ) ` (~ ltmul12a , ~ expadd ).')
    s = w.s
    c = Ctx(w, ph, T)
    an, cn, mn, nn = c['A e. NN0'], c['C e. NN0'], c['M e. NN0'], c['N e. NN0']
    rr = lambda x, st: s([st], 'nn0red', '( %s -> %s e. RR )' % (ph, x))
    pm = s([closed(w, ph, '2re', '2 e. RR'), mn], 'reexpcld', '( %s -> ( 2 ^ M ) e. RR )' % ph)
    pn = s([closed(w, ph, '2re', '2 e. RR'), nn], 'reexpcld', '( %s -> ( 2 ^ N ) e. RR )' % ph)
    j1 = s([s([rr('A', an), pm], 'jca', '( %s -> ( A e. RR /\\ ( 2 ^ M ) e. RR ) )' % ph),
            s([s([an], 'nn0ge0d', '( %s -> 0 <_ A )' % ph), c['A < ( 2 ^ M )']], 'jca', '( %s -> ( 0 <_ A /\\ A < ( 2 ^ M ) ) )' % ph)], 'jca',
           '( %s -> ( ( A e. RR /\\ ( 2 ^ M ) e. RR ) /\\ ( 0 <_ A /\\ A < ( 2 ^ M ) ) ) )' % ph)
    j2 = s([s([rr('C', cn), pn], 'jca', '( %s -> ( C e. RR /\\ ( 2 ^ N ) e. RR ) )' % ph),
            s([s([cn], 'nn0ge0d', '( %s -> 0 <_ C )' % ph), c['C < ( 2 ^ N )']], 'jca', '( %s -> ( 0 <_ C /\\ C < ( 2 ^ N ) ) )' % ph)], 'jca',
           '( %s -> ( ( C e. RR /\\ ( 2 ^ N ) e. RR ) /\\ ( 0 <_ C /\\ C < ( 2 ^ N ) ) ) )' % ph)
    lt = s([j1, j2, w.inst('ltmul12a')], 'syl2anc', '( %s -> ( A x. C ) < ( ( 2 ^ M ) x. ( 2 ^ N ) ) )' % ph)
    ea = s([closed(w, ph, '2cn', '2 e. CC'), mn, nn, w.inst('expadd')], 'syl3anc', '( %s -> ( 2 ^ ( M + N ) ) = ( ( 2 ^ M ) x. ( 2 ^ N ) ) )' % ph)
    w.qed([lt, ea], 'breqtrrd', ST_MULLT)
    return w.run()


def t12fldivle():
    lab = 't12fldivle'
    T = (('A e. NN0', 'K e. NN'), ('X e. RR', 'A <_ ( K x. X )'))
    ph = cj(T)
    w = W(lab, 'The floor of ` a / k ` is at most ` x ` when ` a <_ k x ` (Lean\'s ` Nat.div_le_of_le_mul ` ; ~ fldivle , ~ ledivmul ).')
    s = w.s
    c = Ctx(w, ph, T)
    an, knn, xr = c['A e. NN0'], c['K e. NN'], c['X e. RR']
    ar = s([an], 'nn0red', '( %s -> A e. RR )' % ph)
    kr = s([knn], 'nnred', '( %s -> K e. RR )' % ph)
    kp = s([knn], 'nngt0d', '( %s -> 0 < K )' % ph)
    kpr = s([knn, w.inst('nnrp')], 'syl', '( %s -> K e. RR+ )' % ph)
    f1 = s([ar, kpr, w.inst('fldivle')], 'syl2anc', '( %s -> ( |_ ` ( A / K ) ) <_ ( A / K ) )' % ph)
    d = s([ar, xr, s([kr, kp], 'jca', '( %s -> ( K e. RR /\\ 0 < K ) )' % ph), w.inst('ledivmul')], 'syl3anc',
          '( %s -> ( ( A / K ) <_ X <-> A <_ ( K x. X ) ) )' % ph)
    d2 = s([c['A <_ ( K x. X )'], d], 'mpbird', '( %s -> ( A / K ) <_ X )' % ph)
    fr = s([s([ar, kr, s([knn], 'nnne0d', '( %s -> K =/= 0 )' % ph)], 'redivcld', '( %s -> ( A / K ) e. RR )' % ph)], 'flcld',
           '( %s -> ( |_ ` ( A / K ) ) e. ZZ )' % ph)
    frr = s([fr], 'zred', '( %s -> ( |_ ` ( A / K ) ) e. RR )' % ph)
    qr = s([ar, kr, s([knn], 'nnne0d', '( %s -> K =/= 0 )' % ph)], 'redivcld', '( %s -> ( A / K ) e. RR )' % ph)
    w.qed([frr, qr, xr, f1, d2], 'letrd', ST_FLDIVLE)
    return w.run()


def sctmval():
    lab = 'sctmval'
    ph = '( C e. NN0 /\\ K e. NN /\\ N e. NN0 )'
    w = W(lab, 'The value of ~ df-sctm : Lean\'s ` scalesTM C1 K n ` .')
    s = w.s
    cn = s([], 'simp1', '( %s -> C e. NN0 )' % ph)
    kn = s([], 'simp2', '( %s -> K e. NN )' % ph)
    nn = s([], 'simp3', '( %s -> N e. NN0 )' % ph)
    NM = '( n e. NN0 |-> %s )' % SCTUP_('c', 'k', 'n')
    NMC = '( n e. NN0 |-> %s )' % SCTUP_('C', 'K', 'n')
    ante = '( c = C /\\ k = K )'
    ec = s([], 'simpl', '( %s -> c = C )' % ante)
    ek = s([], 'simpr', '( %s -> k = K )' % ante)
    cg, nb = w.congr(NM, {'c': 'C', 'k': 'K'}, ante, {'c': ec, 'k': ek})
    assert nb == NMC, nb
    d = s([], 'df-sctm', DF_SCTM)
    mx = s([s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % NMC)
    ovi = s([cg, d], 'ovmpoga', '( ( C e. NN0 /\\ K e. NN /\\ %s e. _V ) -> ( C ScTM K ) = %s )' % (NMC, NMC))
    ov = s([cn, kn, s([mx], 'a1i', '( %s -> %s e. _V )' % (ph, NMC)), ovi], 'syl3anc', '( %s -> ( C ScTM K ) = %s )' % (ph, NMC))
    fv0 = s([ov], 'fveq1d', '( %s -> %s = ( %s ` N ) )' % (ph, SC_, NMC))
    en = s([], 'id', '( n = N -> n = N )')
    cg2, nb2 = w.congr(SCTUP_('C', 'K', 'n'), {'n': 'N'}, 'n = N', {'n': en})
    assert nb2 == SCTUP_('C', 'K', 'N'), nb2
    fvm = s([cg2, s([], 'eqid', '%s = %s' % (NMC, NMC))], 'fvmptg', '( ( N e. NN0 /\\ %s e. _V ) -> ( %s ` N ) = %s )'
            % (SCTUP_('C', 'K', 'N'), NMC, SCTUP_('C', 'K', 'N')))
    fv = s([nn, s([s([], 'opex', '%s e. _V' % SCTUP_('C', 'K', 'N'))], 'a1i', '( %s -> %s e. _V )' % (ph, SCTUP_('C', 'K', 'N'))), fvm],
           'syl2anc', '( %s -> ( %s ` N ) = %s )' % (ph, NMC, SCTUP_('C', 'K', 'N')))
    w.qed([fv0, fv], 'eqtrd', ST_SCTMVAL)
    return w.run()



import t12_h_sc as HS

P2 = lambda e: '( 2 ^ %s )' % e
NLOG = lambda a: '( 2 Nlog %s )' % a


def proj_eq(w, ph, proj_txt, tup_eq, tup):
    """( ph -> proj( SC_ ) = component ) from tup_eq : ( ph -> SC_ = tup )"""
    import tm
    s = w.s
    r1, x1 = w.rewrite(proj_txt, {SC_: (tup, tup_eq)}, ph)
    st, val = tm.evaluate(w, ph, x1, {})
    return s([r1, st], 'eqtrd', '( %s -> %s = %s )' % (ph, proj_txt, val)), val


def tmiscal():
    lab = 'tmiscal'
    T = numtree(TREE_SCAL)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scalesF_runs ` at the machine: ` scLogs ` , ` scTheta ` , ` scT ` , ` scZ C1 ` , ` scBz ` , ` scY K ` , '
               '` scZ99 ` (~ tmisclg ... ~ tmisc99 ) at the bit bound ` m = 3 b + 8 ` push the five scales of '
               '` scalesTM C1 K n ` (~ sctmval ) on 0, top first ` z , z99 , y , T , theta ` , within ` 50 B ( 3 b + 8 ) ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    cn, knn, nn, bn, xg = c0['C e. NN0'], c0['K e. NN'], c0['N e. NN0'], c0['B e. NN0'], c0[WG('X')]
    kn = s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % ph)
    B = Base(w, ph, T, N8, 'scal', {'7': (EWg('N', 'X'), ewg_(w, ph, 'N', nn, 'X', xg))})
    c, mk = B.c, B.mk
    F_ = FRAGS['scal']
    LM = F_.lmap()
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    MB = '( ( 3 x. B ) + 8 )'
    cl = Closure(w, ph, {'C': ('NN0', cn), 'K': ('NN', knn), 'N': ('NN0', nn), 'B': ('NN0', bn)})
    mbn = cl.mem(MB, 'NN0')
    BB, BBB = '( B + B )', '( ( B + B ) + B )'
    B28 = '( ( 2 x. B ) + 8 )'
    for e in ('B', MB, BB, BBB, B28, '( 3 x. B )'):
        cl.atom(P2(e))

    def pw_le(e):
        """( ph -> 2 ^ e <_ 2 ^ MB ) for e <_ MB"""
        en = cl.mem(e, 'NN0')
        le = linarith(w, ph, [cl.ge0('B')], '%s <_ %s' % (e, MB), closure=cl)
        u = s([s([s([en], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e)), s([mbn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, MB)), le], '3jca',
                 '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (ph, e, MB, e, MB)), w.inst('eluz2')], 'sylibr',
              '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, MB, e))
        return s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u, w.inst('leexp2a')], 'syl3anc',
                 '( %s -> %s <_ %s )' % (ph, P2(e), P2(MB)))

    def lin_at(e):
        """( ph -> ( ( 8 x. e ) + 100 ) < 2 ^ e ) for 8 <_ e"""
        en = cl.mem(e, 'NN0')
        e8 = linarith(w, ph, [cl.ge0('B')], '8 <_ %s' % e, closure=cl)
        return s([s([en, e8], 'jca', '( %s -> ( %s e. NN0 /\\ 8 <_ %s ) )' % (ph, e, e)), w.inst('t12lin')], 'syl',
                 '( %s -> ( ( 8 x. %s ) + ; ; 1 0 0 ) < %s )' % (ph, e, P2(e)))
    lin8 = lin_at(MB)
    u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    bpb = s([u2, bn, w.inst('bernneq3')], 'syl2anc', '( %s -> B < %s )' % (ph, P2('B')))
    nlt, clt, klt = c[LT2('N')], c[LT2('C')], c[LT2('K')]
    M, A = NLOG('N'), NLOG(NLOG('N'))
    Bb = NLOG(A)
    Z = '( ( C x. %s ) x. %s )' % (A, Bb)
    BZ = '( ( 2 Nlog %s ) + 1 )' % Z

    def nlog(x, xn):
        nx = s([closed(w, ph, '2nn0', '2 e. NN0'), xn, w.inst('nlogcl')], 'syl2anc', '( %s -> ( 2 Nlog %s ) e. NN0 )' % (ph, x))
        cl.leaf('( 2 Nlog %s )' % x, 'NN0', nx)
        return nx, s([xn, w.inst('t12nlogle')], 'syl', '( %s -> ( 2 Nlog %s ) <_ %s )' % (ph, x, x))
    mn, mle = nlog('N', nn)
    an, ale = nlog(M, mn)
    bbn, ble = nlog(A, an)
    blN = s([nn, w.inst('blcl')], 'syl', '( %s -> ( bl ` N ) e. NN0 )' % ph)
    cl.leaf('( bl ` N )', 'NN0', blN)
    mb = linarith(w, ph, [s([nn, w.inst('t12nlogbl')], 'syl', '( %s -> %s <_ ( bl ` N ) )' % (ph, M)),
                          s([nn, bn, nlt, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` N ) <_ B )' % ph)], '%s <_ B' % M, closure=cl)
    hyB = [mb, ale, ble, bpb, pw_le('B'), lin8, nlt, clt, klt, cl.ge0('B')]
    ltB = lambda x: linarith(w, ph, hyB, '%s < %s' % (x, P2('B')), closure=cl)

    def mullt(a_, an_, b_, bn_, ea, eb, alt, blt):
        return s([s([s([an_, bn_], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, a_, b_)),
                     s([cl.mem(ea, 'NN0'), cl.mem(eb, 'NN0')], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, ea, eb))], 'jca',
                    '( %s -> ( ( %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) )' % (ph, a_, b_, ea, eb)),
                  s([alt, blt], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (ph, a_, P2(ea), b_, P2(eb))), w.inst('t12mullt')], 'syl2anc',
                 '( %s -> ( %s x. %s ) < %s )' % (ph, a_, b_, P2('( %s + %s )' % (ea, eb))))
    ca = '( C x. %s )' % A
    cal = mullt('C', cn, A, an, 'B', 'B', clt, ltB(A))
    can = cl.mem(ca, 'NN0')
    zl = mullt(ca, can, Bb, bbn, BB, 'B', cal, ltB(Bb))
    zn = cl.mem(Z, 'NN0')
    hyB += [cal, zl, pw_le(BB), pw_le(BBB)]
    zbn = s([zn, w.inst('blcl')], 'syl', '( %s -> ( bl ` %s ) e. NN0 )' % (ph, Z))
    cl.leaf('( bl ` %s )' % Z, 'NN0', zbn)
    nzn, nzle = nlog(Z, zn)
    bzle = linarith(w, ph, [s([zn, w.inst('t12nlogbl')], 'syl', '( %s -> ( 2 Nlog %s ) <_ ( bl ` %s ) )' % (ph, Z, Z)),
                            s([zn, cl.mem(BBB, 'NN0'), zl, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` %s ) <_ %s )' % (ph, Z, BBB))],
                    '%s <_ ( ( 3 x. B ) + 1 )' % BZ, closure=cl)
    bzn = cl.mem(BZ, 'NN0')
    hyB.append(bzle)
    ltM = lambda x, more=(): linarith(w, ph, hyB + list(more), '%s < %s' % (x, P2(MB)), closure=cl)
    le8M = linarith(w, ph, [cl.ge0('B')], '8 <_ %s' % MB, closure=cl)

    def cp(j):
        fn_, cks, en, exn = F_.children[j]
        return PL('P', F_.slot(j)), LM[exn]
    TY = {'%s e. NN0' % x: st_ for x, st_ in ((M, mn), (A, an), (Bb, bbn), (Z, zn), (BZ, bzn), ('C', cn), ('K', kn), ('N', nn))}
    TY['K e. NN'] = knn
    _call = B.call

    def call(R_, lab_, m_, ex_, ups_):
        e2 = dict(TY); e2.update(ex_)
        return _call(R_, lab_, m_, e2, ups_)

    def ew(t_, X, xg_):
        v = EWg(t_, X)
        return v, B.g(v, ewg_(w, ph, t_, cl.mem(t_, 'NN0'), X, xg_))
    # 1. scLogs
    P, E = cp(0)
    ups = []
    for k, v_ in (('1', M), ('2', A), ('3', Bb)):
        ups.append((k,) + ew(v_, DK(k), g(k)))
    call(R, 'tmisclg', {'N': 'N', 'B': MB, 'X': 'X', 'P': P, 'E': E}, {'%s e. NN0' % MB: mbn, LT2('N', MB): ltM('N')}, ups)
    # 2. scTheta at M
    P, E = cp(1)
    M1 = '( %s + 1 )' % M
    LTH = '( ( 2 Nlog %s ) + 1 )' % M1
    EXPTH = '( |_ ` ( ( ( 6 x. %s ) + 4 ) / 5 ) )' % LTH
    TH = P2(EXPTH)
    m1n = cl.mem(M1, 'NN0')
    nm1n, nm1le = nlog(M1, m1n)
    numth = '( ( 6 x. %s ) + 4 )' % LTH
    fl = s([s([s([cl.mem(numth, 'NN0'), closed(w, ph, '5nn', '5 e. NN')], 'jca', '( %s -> ( %s e. NN0 /\\ 5 e. NN ) )' % (ph, numth)),
               s([cl.mem('( ( 2 x. B ) + 4 )', 'RR'), linarith(w, ph, [nm1le, mb, cl.ge0('B')], '%s <_ ( 5 x. ( ( 2 x. B ) + 4 ) )' % numth, closure=cl)], 'jca',
                 '( %s -> ( ( ( 2 x. B ) + 4 ) e. RR /\\ %s <_ ( 5 x. ( ( 2 x. B ) + 4 ) ) ) )' % (ph, numth))], 'jca',
              '( %s -> ( ( %s e. NN0 /\\ 5 e. NN ) /\\ ( ( ( 2 x. B ) + 4 ) e. RR /\\ %s <_ ( 5 x. ( ( 2 x. B ) + 4 ) ) ) ) )' % (ph, numth, numth)),
            w.inst('t12fldivle')], 'syl', '( %s -> %s <_ ( ( 2 x. B ) + 4 ) )' % (ph, EXPTH))
    exn = s([cl.mem(numth, 'NN0'), closed(w, ph, '5nn', '5 e. NN'), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXPTH))
    cl.leaf(EXPTH, 'NN0', exn)
    thn = s([closed(w, ph, '2nn0', '2 e. NN0'), exn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, TH))
    cl.leaf(TH, 'NN0', thn)
    v0, g0 = ew(TH, DK(0), g('0'))
    call(R, 'tmiscth', {'G': M, 'B': MB, 'X': DK(1), 'P': P, 'E': E},
           {'%s e. NN0' % MB: mbn, '8 <_ %s' % MB: le8M, LT2(M1, MB): ltM(M1),
            '%s < %s' % (EXPTH, MB): linarith(w, ph, [fl, cl.ge0('B')], '%s < %s' % (EXPTH, MB), closure=cl)}, [('0', v0, g0)])
    # 3. scT at a
    P, E = cp(2)
    A3 = '( 3 x. %s )' % A
    v0, g0 = ew(A3, v0, g0)
    call(R, 'tmisctt', {'G': A, 'B': MB, 'X': DK(2), 'P': P, 'E': E},
           {'%s e. NN0' % MB: mbn, '8 <_ %s' % MB: le8M, LT2(A, MB): ltM(A), LT2(A3, MB): ltM(A3)}, [('0', v0, g0)])
    # 4. scZ C1
    P, E = cp(3)
    v5, g5 = ew(Z, DK(5), g('5'))
    call(R, 'tmisczz', {'C': 'C', 'F': M, 'G': A, 'H': Bb, 'B': MB, 'X': DK(1), "X'": DK(2), 'Y': DK(3), 'P': P, 'E': E},
           {'%s e. NN0' % MB: mbn, '8 <_ %s' % MB: le8M, LT2('C', MB): ltM('C'), LT2(M, MB): ltM(M), LT2(A, MB): ltM(A), LT2(Bb, MB): ltM(Bb),
            LT2(ca, MB): ltM(ca)},
           [('1', DK(1), g('1')), ('2', DK(2), g('2')), ('3', DK(3), g('3')), ('5', v5, g5)])
    # 5. scBz
    P, E = cp(4)
    v4, g4 = ew(BZ, DK(4), g('4'))
    call(R, 'tmiscbz', {'Z': Z, 'B': MB, 'X': DK(5), 'P': P, 'E': E},
           {'%s e. NN0' % MB: mbn, '8 <_ %s' % MB: le8M, LT2(Z, MB): ltM(Z)}, [('4', v4, g4)])
    # 6. scY K at bz: ( K - 1 ) ( bz + 1 ) < 2 ^ ( B + ( 2 B + 8 ) ) = 2 ^ MB
    P, E = cp(5)
    K1 = '( K - 1 )'
    k1n = s([knn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, K1))
    cl.leaf(K1, 'NN0', k1n)
    k1e = s([cl.mem('K', 'CC'), closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('npcan')], 'syl2anc', '( %s -> ( %s + 1 ) = K )' % (ph, K1))
    BZ1 = '( %s + 1 )' % BZ
    l28 = lin_at(B28)
    bz1lt = linarith(w, ph, [bzle, l28, cl.ge0('B')], '%s < %s' % (BZ1, P2(B28)), closure=cl)
    k1lt = linarith(w, ph, [k1e, klt], '%s < %s' % (K1, P2('B')), closure=cl)
    kg = mullt(K1, k1n, BZ1, cl.mem(BZ1, 'NN0'), 'B', B28, k1lt, bz1lt)
    KG = '( %s x. %s )' % (K1, BZ1)
    eMB = lineq(w, ph, '( B + %s )' % B28, MB, closure=cl)
    kgl = s([kg, s([eMB], 'oveq2d', '( %s -> %s = %s )' % (ph, P2('( B + %s )' % B28), P2(MB)))], 'breqtrd', '( %s -> %s < %s )' % (ph, KG, P2(MB)))
    NUMY = '( ( ( %s x. %s ) + K ) - 1 )' % (K1, BZ)
    EXPY = '( |_ ` ( %s / K ) )' % NUMY
    Y = P2(EXPY)
    cl2 = Closure(w, ph, {'K': ('NN', knn)})
    cl2.leaf(K1, 'NN0', k1n)
    cl2.leaf(BZ, 'NN0', bzn)
    KBZ = '( %s x. %s )' % (K1, BZ)
    kbzk = s([cl.mem(KBZ, 'NN0'), knn, w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> ( %s + K ) e. NN )' % (ph, KBZ))
    numyn = s([kbzk, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, NUMY))
    cl.leaf(NUMY, 'NN0', numyn)
    kbz1 = s([cl2.mem(K1, 'CC'), cl2.mem(BZ, 'CC'), w.inst('adddirp1d')], 'syl2anc', '( %s -> ( ( %s + 1 ) x. %s ) = ( %s + %s ) )' % (ph, K1, BZ, KBZ, BZ))
    kbz2 = s([k1e], 'oveq1d', '( %s -> ( ( %s + 1 ) x. %s ) = ( K x. %s ) )' % (ph, K1, BZ, BZ))
    kbz = s([kbz2, kbz1], 'eqtr3d', '( %s -> ( K x. %s ) = ( %s + %s ) )' % (ph, BZ, KBZ, BZ))
    numyle = linarith(w, ph, [kbz, cl2.ge0(BZ)], '%s <_ ( K x. %s )' % (NUMY, BZ1), closure=cl2, products=True)
    flY = s([s([s([cl.mem(NUMY, 'NN0'), knn], 'jca', '( %s -> ( %s e. NN0 /\\ K e. NN ) )' % (ph, NUMY)),
                s([cl.mem(BZ1, 'RR'), numyle], 'jca', '( %s -> ( %s e. RR /\\ %s <_ ( K x. %s ) ) )' % (ph, BZ1, NUMY, BZ1))], 'jca',
               '( %s -> ( ( %s e. NN0 /\\ K e. NN ) /\\ ( %s e. RR /\\ %s <_ ( K x. %s ) ) ) )' % (ph, NUMY, BZ1, NUMY, BZ1)),
             w.inst('t12fldivle')], 'syl', '( %s -> %s <_ %s )' % (ph, EXPY, BZ1))
    eyn = s([cl.mem(NUMY, 'NN0'), knn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXPY))
    cl.leaf(EXPY, 'NN0', eyn)
    cl.leaf(Y, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), eyn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Y)))
    v0, g0 = ew(Y, v0, g0)
    call(R, 'tmiscyy', {'K': 'K', 'G': BZ, 'B': MB, 'X': DK(4), 'P': P, 'E': E},
           {'%s e. NN0' % MB: mbn, '8 <_ %s' % MB: le8M, LT2(BZ1, MB): ltM(BZ1), LT2('K', MB): ltM('K'), LT2(KG, MB): kgl,
            '%s < %s' % (EXPY, MB): linarith(w, ph, [flY, bzle, cl.ge0('B')], '%s < %s' % (EXPY, MB), closure=cl)}, [('0', v0, g0)])
    # 7. scZ99 at z , bz: 99 ( bz + 1 ) <_ 99 ( 3 B + 2 ) < 256 ( 1 + 7 B ) <_ 2 ^ MB
    P, E = cp(6)
    N99 = '( ; 9 9 x. %s )' % BZ1
    p3 = s([bn, w.inst('t12pow3')], 'syl', '( %s -> ( 1 + ( 7 x. B ) ) <_ %s )' % (ph, P2('( 3 x. B )')))
    ea = s([closed(w, ph, '2cn', '2 e. CC'), cl.mem('( 3 x. B )', 'NN0'), closed(w, ph, '8nn0', '8 e. NN0'), w.inst('expadd')], 'syl3anc',
           '( %s -> %s = ( %s x. ( 2 ^ 8 ) ) )' % (ph, P2(MB), P2('( 3 x. B )')))
    e256 = s([s([s([], '2exp8', '( 2 ^ 8 ) = ; ; 2 5 6')], 'a1i', '( %s -> ( 2 ^ 8 ) = ; ; 2 5 6 )' % ph)], 'oveq2d',
             '( %s -> ( %s x. ( 2 ^ 8 ) ) = ( %s x. ; ; 2 5 6 ) )' % (ph, P2('( 3 x. B )'), P2('( 3 x. B )')))
    n99lt = linarith(w, ph, [bzle, p3, ea, e256, cl.ge0('B')], '%s < %s' % (N99, P2(MB)), closure=cl)
    NUM99 = '( ( ; 9 9 x. %s ) + ; 9 9 )' % BZ
    EXP99 = '( |_ ` ( %s / ; ; 1 0 0 ) )' % NUM99
    Z99 = P2(EXP99)
    n100 = s([num.nn(w, 100)], 'a1i', '( %s -> ; ; 1 0 0 e. NN )' % ph)
    fl99 = s([s([s([cl.mem(NUM99, 'NN0'), n100], 'jca', '( %s -> ( %s e. NN0 /\\ ; ; 1 0 0 e. NN ) )' % (ph, NUM99)),
                 s([cl.mem(BZ1, 'RR'), linarith(w, ph, [cl.ge0(BZ)], '%s <_ ( ; ; 1 0 0 x. %s )' % (NUM99, BZ1), closure=cl)], 'jca',
                   '( %s -> ( %s e. RR /\\ %s <_ ( ; ; 1 0 0 x. %s ) ) )' % (ph, BZ1, NUM99, BZ1))], 'jca',
                '( %s -> ( ( %s e. NN0 /\\ ; ; 1 0 0 e. NN ) /\\ ( %s e. RR /\\ %s <_ ( ; ; 1 0 0 x. %s ) ) ) )' % (ph, NUM99, BZ1, NUM99, BZ1)),
              w.inst('t12fldivle')], 'syl', '( %s -> %s <_ %s )' % (ph, EXP99, BZ1))
    e99n = s([cl.mem(NUM99, 'NN0'), n100, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXP99))
    cl.leaf(EXP99, 'NN0', e99n)
    cl.leaf(Z99, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), e99n, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Z99)))
    vz99, gz99 = ew(Z99, v0, g0)
    v0, g0 = ew(Z, vz99, gz99)
    call(R, 'tmisc99', {'Z': Z, 'G': BZ, 'B': MB, 'X': DK(4), 'Y': DK(5), 'P': P, 'E': E},
           {'%s e. NN0' % MB: mbn, '8 <_ %s' % MB: le8M, LT2(Z, MB): ltM(Z), LT2(BZ1, MB): ltM(BZ1), LT2(N99, MB): n99lt,
            '%s < %s' % (EXP99, MB): linarith(w, ph, [fl99, bzle, cl.ge0('B')], '%s < %s' % (EXP99, MB), closure=cl)},
           [('0', v0, g0), ('4', DK(4), g('4')), ('5', DK(5), g('5'))])
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    Dc = triple_D(D)
    assert Dc == UP('D', '0', v0), Dc
    # the stack 0 value as the projections of ScTM
    TUP = SCTUP_('C', 'K', 'N')
    tv = s([s([cn, knn, nn], '3jca', '( %s -> ( C e. NN0 /\\ K e. NN /\\ N e. NN0 ) )' % ph), w.inst('sctmval')], 'syl', '( %s -> %s = %s )' % (ph, SC_, TUP))
    rules = {}
    for pj in (PZ, PZ99, PY, PT, PTH):
        st_, val = proj_eq(w, ph, pj(SC_), tv, TUP)
        rules[pj(SC_)] = (val, st_)
    target = SCALD.split('<. 0 , ', 1)[1].rsplit(' >. } )', 1)[0]
    rt, xt = w.rewrite(target, rules, ph)
    assert xt == v0, '\n%s\n%s' % (xt, v0)
    eq0 = s([rt], 'eqcomd', '( %s -> %s = %s )' % (ph, v0, target))
    deq = upeq(w, ph, 'D', '0', eq0, v0, target)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, deq, Dc, SCALD))
    TMB_ = '( TMB ` %s )' % MB
    cl.leaf(TMB_, 'NN0', tmbn(w, ph, MB, mbn))
    BND = '( ; 5 0 x. %s )' % TMB_
    le = linarith(w, ph, [], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
