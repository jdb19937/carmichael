"""Sortie KD1: iterated derivatives of a Dirichlet series with coefficients O(m^B) (kddsdn)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from mvlib import ringeq
from lin import linarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def MAP(x):
    return '( z e. %s |-> sum_ k e. NN ( ( -u ( log ` k ) ^ %s ) x. ( ( A ` k ) x. ( k ^c -u z ) ) ) )' % (HP('T'), x)


def gen_dsdn():
    w = W('kddsdn', 'The ` K ` -th iterated derivative of a Dirichlet series with coefficients ` O ( m ^ B ) ` on ` Re > 1 + 2 B ` has coefficients ` ( -u log k ) ^ K A ( k ) ` (Lean ` LSeries_iteratedDeriv ` , via ` kddsdv ` ).')
    DSa = DS('A', 'T'); HT = HP('T')
    ph = '( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) )' % AGR
    PSx = lambda x: '( ( CC Dn %s ) ` %s ) = %s' % (DSa, x, MAP(x))
    subs = {}
    for nm, t in (('0', '0'), ('n', 'n'), ('n1', '( n + 1 )'), ('K', 'K')):
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (t, t))
        st, new = w.wcongr(PSx('x'), {'x': t}, 'x = %s' % t, {'x': idx})
        assert new == PSx(t), new
        subs[nm] = st
    # common facts under ph
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    ag = s([], 'simpl', AGR)
    af = s([ag], 'simp1d', 'A : NN --> CC'); cr = s([ag], 'simp2d', 'C e. RR')
    bg = s([ag], 'simp3d', '( B e. RR+ /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) )')
    bp = s([bg], 'simpld', 'B e. RR+'); gr = s([bg], 'simprd', 'A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) )')
    tr = s([], 'simprl', 'T e. RR'); lt = s([], 'simprr', '( 1 + ( 2 x. B ) ) < T')
    br = s([bp], 'rpred', 'B e. RR')
    c = Closure(w, ph, {'T': ('RR', tr), 'B': ('RR', br)})
    b0_ = s([bp], 'rpgt0d', '0 < B')
    lt1 = linarith(w, ph, [lt, b0_], '( 1 + B ) < T', closure=c)
    dv0 = s([ag, s([tr, lt1], 'jca', '( T e. RR /\\ ( 1 + B ) < T )'), w.inst('kddsdv')], 'syl2anc',
            '( %s /\\ ( CC _D %s ) = ( z e. %s |-> sum_ k e. NN -u ( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u z ) ) ) )' % (HOLF(DSa, HT), DSa, HT))
    hol = s([dv0], 'simpld', HOLF(DSa, HT))
    pm, _ = pmcc(w, ph, hol, DSa, HT)
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % ph)
    # base
    b0 = s([ccs, pm, w.inst('dvn0')], 'syl2anc', '( ( CC Dn %s ) ` 0 ) = %s' % (DSa, DSa))
    Azk = '( ( %s /\\ z e. %s ) /\\ k e. NN )' % (ph, HT)
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Azk)
    lkc = w.s([w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Azk)], 'relogcld', '( %s -> ( log ` k ) e. RR )' % Azk)], 'recnd', '( %s -> ( log ` k ) e. CC )' % Azk)
    nl = w.s([lkc], 'negcld', '( %s -> -u ( log ` k ) e. CC )' % Azk)
    e0 = w.s([nl], 'exp0d', '( %s -> ( -u ( log ` k ) ^ 0 ) = 1 )' % Azk)
    zz = w.s([], 'simplr', '( %s -> z e. %s )' % (Azk, HT))
    zc = w.s([zz, w.s([w.s([tr], 'adantr', '( ( %s /\\ z e. %s ) -> T e. RR )' % (ph, HT))], 'adantr', '( %s -> T e. RR )' % Azk) and
              w.s([w.s([w.s([tr], 'adantr', '( ( %s /\\ z e. %s ) -> T e. RR )' % (ph, HT))], 'adantr', '( %s -> T e. RR )' % Azk), w.inst('elhp2')], 'syl',
                  '( %s -> ( z e. %s <-> ( z e. CC /\\ T < ( Re ` z ) ) ) )' % (Azk, HT))], 'mpbid', '( %s -> ( z e. CC /\\ T < ( Re ` z ) ) )' % Azk)
    zc = w.s([zc], 'simpld', '( %s -> z e. CC )' % Azk)
    akc = w.s([w.s([w.s([af], 'adantr', '( ( %s /\\ z e. %s ) -> A : NN --> CC )' % (ph, HT))], 'adantr', '( %s -> A : NN --> CC )' % Azk), kn], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % Azk)
    kzc = w.s([w.s([kn], 'nncnd', '( %s -> k e. CC )' % Azk), w.s([zc], 'negcld', '( %s -> -u z e. CC )' % Azk)], 'cxpcld', '( %s -> ( k ^c -u z ) e. CC )' % Azk)
    TM = '( ( A ` k ) x. ( k ^c -u z ) )'
    tmc = w.s([akc, kzc], 'mulcld', '( %s -> %s e. CC )' % (Azk, TM))
    t0 = w.s([w.s([e0], 'oveq1d', '( %s -> ( ( -u ( log ` k ) ^ 0 ) x. %s ) = ( 1 x. %s ) )' % (Azk, TM, TM)), w.s([tmc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (Azk, TM, TM))],
             'eqtrd', '( %s -> ( ( -u ( log ` k ) ^ 0 ) x. %s ) = %s )' % (Azk, TM, TM))
    sm0 = w.s([t0], 'sumeq2dv', '( ( %s /\\ z e. %s ) -> sum_ k e. NN ( ( -u ( log ` k ) ^ 0 ) x. %s ) = sum_ k e. NN %s )' % (ph, HT, TM, TM))
    m0 = s([sm0], 'mpteq2dva', '%s = %s' % (MAP('0'), DSa))
    base = s([b0, m0], 'eqtr4d', PSx('0'))
    # ---- step
    A1 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (ph, PSx('n'))
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    ad1 = lambda st: w.s([st], 'adantr', '( ( %s /\\ n e. NN0 ) -> %s )' % (ph, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    lift1 = lambda st: w.s([ad1(st)], 'adantr', '( %s -> %s )' % (A1, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    nn = t([], 'simplr', 'n e. NN0'); ih = t([], 'simpr', PSx('n'))
    An = '( j e. NN |-> ( ( -u ( log ` j ) ^ n ) x. ( A ` j ) ) )'
    Cp = '( C x. ( ( ! ` n ) / ( B ^ n ) ) )'; Bp = '( 2 x. B )'
    DSn = DS(An, 'T')
    # growth of An, under ( A1 /\ i e. NN )
    Ai = '( %s /\\ i e. NN )' % A1
    v = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    adi = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Ai, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    ii = v([], 'simpr', 'i e. NN')
    ir = v([ii], 'nnrpd', 'i e. RR+')
    L = '( log ` i )'
    lr = v([ir], 'relogcld', '%s e. RR' % L); lc = v([lr], 'recnd', '%s e. CC' % L)
    l0 = v([v([ii], 'nnred', 'i e. RR'), v([ii], 'nnge1d', '1 <_ i'), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L)
    nni = adi(nn)
    aic = v([adi(lift1(af)), ii], 'ffvelcdmd', '( A ` i ) e. CC')
    P = '( -u %s ^ n )' % L
    pc = v([v([lc], 'negcld', '-u %s e. CC' % L), nni], 'expcld', '%s e. CC' % P)
    VAL = '( %s x. ( A ` i ) )' % P
    e1 = w.s([w.s([w.s([w.s([], 'fveq2', '( j = i -> ( log ` j ) = %s )' % L)], 'negeqd', '( j = i -> -u ( log ` j ) = -u %s )' % L)], 'oveq1d', '( j = i -> ( -u ( log ` j ) ^ n ) = %s )' % P),
              w.s([], 'fveq2', '( j = i -> ( A ` j ) = ( A ` i ) )')], 'oveq12d', '( j = i -> ( ( -u ( log ` j ) ^ n ) x. ( A ` j ) ) = %s )' % VAL)
    ai = fvmd(w, Ai, An, 'i', VAL, ii, v([pc, aic], 'mulcld', '%s e. CC' % VAL), e1, var='j')
    g1 = v([ai], 'fveq2d', '( abs ` ( %s ` i ) ) = ( abs ` %s )' % (An, VAL))
    g2 = v([pc, aic], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( A ` i ) ) )' % (VAL, P))
    g3 = v([v([lc], 'negcld', '-u %s e. CC' % L), nni], 'absexpd', '( abs ` %s ) = ( ( abs ` -u %s ) ^ n )' % (P, L))
    g4 = v([lc], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (L, L))
    g5 = v([lr, l0], 'absidd', '( abs ` %s ) = %s' % (L, L))
    g6 = v([v([g4, g5], 'eqtrd', '( abs ` -u %s ) = %s' % (L, L))], 'oveq1d', '( ( abs ` -u %s ) ^ n ) = ( %s ^ n )' % (L, L))
    g7 = v([g3, g6], 'eqtrd', '( abs ` %s ) = ( %s ^ n )' % (P, L))
    g8 = v([g7], 'oveq1d', '( ( abs ` %s ) x. ( abs ` ( A ` i ) ) ) = ( ( %s ^ n ) x. ( abs ` ( A ` i ) ) )' % (P, L))
    gA = v([g1, g2, g8], '3eqtrd', '( abs ` ( %s ` i ) ) = ( ( %s ^ n ) x. ( abs ` ( A ` i ) ) )' % (An, L))
    bpi = adi(lift1(bp)); bri = adi(lift1(br)); cri = adi(lift1(cr))
    lp = v([bpi, nni, ii, w.inst('kdlogpow')], 'syl3anc', '( %s ^ n ) <_ ( ( ( ! ` n ) x. ( i ^c B ) ) / ( B ^ n ) )' % L)
    cg = w.s([w.s([w.s([], 'fveq2', '( m = i -> ( A ` m ) = ( A ` i ) )')], 'fveq2d', '( m = i -> ( abs ` ( A ` m ) ) = ( abs ` ( A ` i ) ) )'),
              w.s([w.s([], 'oveq1', '( m = i -> ( m ^c B ) = ( i ^c B ) )')], 'oveq2d', '( m = i -> ( C x. ( m ^c B ) ) = ( C x. ( i ^c B ) ) )')],
             'breq12d', '( m = i -> ( ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) <-> ( abs ` ( A ` i ) ) <_ ( C x. ( i ^c B ) ) ) )')
    ga = v([ii, adi(lift1(gr)), w.s([cg], 'rspcv', '( i e. NN -> ( A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) -> ( abs ` ( A ` i ) ) <_ ( C x. ( i ^c B ) ) ) )')],
           'sylc', '( abs ` ( A ` i ) ) <_ ( C x. ( i ^c B ) )')
    IB = '( i ^c B )'
    ibr = v([ir, bri], 'rpcxpcld', '%s e. RR+' % IB)
    fn = v([nni], 'faccld', '( ! ` n ) e. NN')
    bn = v([bpi, v([nni], 'nn0zd', 'n e. ZZ')], 'rpexpcld', '( B ^ n ) e. RR+')
    Q = '( ( ! ` n ) / ( B ^ n ) )'
    qr = v([v([fn], 'nnred', '( ! ` n ) e. RR'), bn], 'rerpdivcld', '%s e. RR' % Q)
    X1 = '( ( ( ! ` n ) x. %s ) / ( B ^ n ) )' % IB
    x1r = v([v([v([fn], 'nnred', '( ! ` n ) e. RR'), v([ibr], 'rpred', '%s e. RR' % IB)], 'remulcld', '( ( ! ` n ) x. %s ) e. RR' % IB), bn], 'rerpdivcld', '%s e. RR' % X1)
    lm = v([v([lr, nni], 'reexpcld', '( %s ^ n ) e. RR' % L), x1r, v([aic], 'abscld', '( abs ` ( A ` i ) ) e. RR'), v([cri, v([ibr], 'rpred', '%s e. RR' % IB)], 'remulcld', '( C x. %s ) e. RR' % IB),
            v([lr, nni, l0], 'expge0d', '0 <_ ( %s ^ n )' % L), v([aic], 'absge0d', '0 <_ ( abs ` ( A ` i ) )'), lp, ga], 'lemul12ad',
           '( ( %s ^ n ) x. ( abs ` ( A ` i ) ) ) <_ ( %s x. ( C x. %s ) )' % (L, X1, IB))
    d23 = v([v([fn], 'nncnd', '( ! ` n ) e. CC'), v([ibr], 'rpcnd', '%s e. CC' % IB), v([bn], 'rpcnd', '( B ^ n ) e. CC'), v([bn], 'rpne0d', '( B ^ n ) =/= 0')], 'div23d',
            '%s = ( %s x. %s )' % (X1, Q, IB))
    ci = Closure(w, Ai, {Q: ('CC', v([qr], 'recnd', '%s e. CC' % Q)), IB: ('CC', v([ibr], 'rpcnd', '%s e. CC' % IB)), 'C': ('CC', v([cri], 'recnd', 'C e. CC'))})
    ci.atom(Q); ci.atom(IB)
    r1 = v([d23], 'oveq1d', '( %s x. ( C x. %s ) ) = ( ( %s x. %s ) x. ( C x. %s ) )' % (X1, IB, Q, IB, IB))
    r2 = ringeq(w, Ai, '( ( %s x. %s ) x. ( C x. %s ) )' % (Q, IB, IB), '( ( C x. %s ) x. ( %s x. %s ) )' % (Q, IB, IB), ci)
    icn = v([ir], 'rpcnd', 'i e. CC'); ine = v([ir], 'rpne0d', 'i =/= 0'); bci = v([bri], 'recnd', 'B e. CC')
    r3 = v([icn, ine, bci, bci], 'cxpaddd', '( i ^c ( B + B ) ) = ( %s x. %s )' % (IB, IB))
    r4 = v([v([bci], '2timesd', '( 2 x. B ) = ( B + B )')], 'oveq2d', '( i ^c ( 2 x. B ) ) = ( i ^c ( B + B ) )')
    r5 = v([r4, r3], 'eqtrd', '( i ^c ( 2 x. B ) ) = ( %s x. %s )' % (IB, IB))
    r6 = v([r5], 'oveq2d', '( %s x. ( i ^c ( 2 x. B ) ) ) = ( %s x. ( %s x. %s ) )' % (Cp, Cp, IB, IB))
    r7 = v([r1, r2, r6], '3eqtr4d', '( %s x. ( C x. %s ) ) = ( %s x. ( i ^c ( 2 x. B ) ) )' % (X1, IB, Cp))
    gi = v([gA, lm, r7], '3brtr4d' if False else 'T.', 'T.') if False else v([v([gA, lm], 'eqbrtrd', '( abs ` ( %s ` i ) ) <_ ( %s x. ( C x. %s ) )' % (An, X1, IB)), r7], 'breqtrd',
                                                                           '( abs ` ( %s ` i ) ) <_ ( %s x. ( i ^c ( 2 x. B ) ) )' % (An, Cp))
    gall = w.s([gi], 'ralrimiva', '( %s -> A. i e. NN ( abs ` ( %s ` i ) ) <_ ( %s x. ( i ^c ( 2 x. B ) ) ) )' % (A1, An, Cp))
    idmi = w.s([], 'id', '( m = i -> m = i )')
    cmi, nmi = w.wcongr('( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c ( 2 x. B ) ) )' % (An, Cp), {'m': 'i'}, 'm = i', {'m': idmi})
    gm = t([gall, w.s([cmi], 'cbvralvw', '( A. m e. NN ( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c ( 2 x. B ) ) ) <-> A. i e. NN ( abs ` ( %s ` i ) ) <_ ( %s x. ( i ^c ( 2 x. B ) ) ) )' % (An, Cp, An, Cp))],
           'sylibr', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c ( 2 x. B ) ) )' % (An, Cp))
    # An : NN --> CC
    Aj = '( %s /\\ j e. NN )' % A1
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    adj = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Aj, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    ljc = w.s([w.s([w.s([jn], 'nnrpd', '( %s -> j e. RR+ )' % Aj)], 'relogcld', '( %s -> ( log ` j ) e. RR )' % Aj)], 'recnd', '( %s -> ( log ` j ) e. CC )' % Aj)
    pjc = w.s([w.s([ljc], 'negcld', '( %s -> -u ( log ` j ) e. CC )' % Aj), adj(nn)], 'expcld', '( %s -> ( -u ( log ` j ) ^ n ) e. CC )' % Aj)
    ajc = w.s([adj(lift1(af)), jn], 'ffvelcdmd', '( %s -> ( A ` j ) e. CC )' % Aj)
    anf = t([w.s([pjc, ajc], 'mulcld', '( %s -> ( ( -u ( log ` j ) ^ n ) x. ( A ` j ) ) e. CC )' % Aj)], 'fmptd', '%s : NN --> CC' % An)
    fnt = t([nn], 'faccld', '( ! ` n ) e. NN')
    bnt = t([lift1(bp), t([nn], 'nn0zd', 'n e. ZZ')], 'rpexpcld', '( B ^ n ) e. RR+')
    cpr = t([lift1(cr), t([t([fnt], 'nnred', '( ! ` n ) e. RR'), bnt], 'rerpdivcld', '%s e. RR' % Q)], 'remulcld', '%s e. RR' % Cp)
    bpp = t([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A1), lift1(bp)], 'rpmulcld', '%s e. RR+' % Bp)
    agr2 = t([anf, cpr, t([bpp, gm], 'jca', '( %s e. RR+ /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c ( 2 x. B ) ) ) )' % (Bp, An, Cp))], '3jca',
             '( %s : NN --> CC /\\ %s e. RR /\\ ( %s e. RR+ /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c ( 2 x. B ) ) ) ) )' % (An, Cp, Bp, An, Cp))
    tc = t([lift1(tr), lift1(lt)], 'jca', '( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T )')
    DVn = '( z e. %s |-> sum_ k e. NN -u ( ( ( %s ` k ) x. ( log ` k ) ) x. ( k ^c -u z ) ) )' % (HT, An)
    kdv = t([agr2, tc, w.inst('kddsdv')], 'syl2anc', '( %s /\\ ( CC _D %s ) = %s )' % (HOLF(DSn, HT), DSn, DVn))
    kdv2 = t([kdv], 'simprd', '( CC _D %s ) = %s' % (DSn, DVn))
    nn1 = w.s([], 'simpr', '( ( %s /\\ n e. NN0 ) -> n e. NN0 )' % ph)
    # MAP(n) = DS(An) and the derivative terms, under ( ( A1 /\ z e. HT ) /\ k e. NN )
    A1n = '( %s /\\ n e. NN0 )' % ph
    Bk = '( ( %s /\\ z e. %s ) /\\ k e. NN )' % (A1n, HT)
    q = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Bk, f))
    adk = lambda st: w.s([w.s([st], 'adantr', '( ( %s /\\ z e. %s ) -> %s )' % (A1n, HT, formula_of(w, st).split(' -> ', 1)[1][:-2]))], 'adantr',
                         '( %s -> %s )' % (Bk, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    kk = q([], 'simpr', 'k e. NN')
    zz = q([], 'simplr', 'z e. %s' % HT)
    zc = q([q([zz, q([adk(ad1(tr)), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ T < ( Re ` z ) ) )' % HT)], 'mpbid', '( z e. CC /\\ T < ( Re ` z ) )')], 'simpld', 'z e. CC')
    Lk = '( log ` k )'
    lkc = q([q([q([kk], 'nnrpd', 'k e. RR+')], 'relogcld', '%s e. RR' % Lk)], 'recnd', '%s e. CC' % Lk)
    nkc = q([lkc], 'negcld', '-u %s e. CC' % Lk)
    Pk = '( -u %s ^ n )' % Lk
    pkc = q([nkc, adk(nn1)], 'expcld', '%s e. CC' % Pk)
    akc = q([adk(ad1(af)), kk], 'ffvelcdmd', '( A ` k ) e. CC')
    Ek = '( k ^c -u z )'
    ekc = q([q([kk], 'nncnd', 'k e. CC'), q([zc], 'negcld', '-u z e. CC')], 'cxpcld', '%s e. CC' % Ek)
    AV = '( %s x. ( A ` k ) )' % Pk
    ek1 = w.s([w.s([w.s([w.s([], 'fveq2', '( j = k -> ( log ` j ) = %s )' % Lk)], 'negeqd', '( j = k -> -u ( log ` j ) = -u %s )' % Lk)], 'oveq1d', '( j = k -> ( -u ( log ` j ) ^ n ) = %s )' % Pk),
               w.s([], 'fveq2', '( j = k -> ( A ` j ) = ( A ` k ) )')], 'oveq12d', '( j = k -> ( ( -u ( log ` j ) ^ n ) x. ( A ` j ) ) = %s )' % AV)
    ank = fvmd(w, Bk, An, 'k', AV, kk, q([pkc, akc], 'mulcld', '%s e. CC' % AV), ek1, var='j')
    ck = Closure(w, Bk, {Pk: ('CC', pkc), '( A ` k )': ('CC', akc), Lk: ('CC', lkc), Ek: ('CC', ekc)})
    for a_ in (Pk, '( A ` k )', Lk, Ek):
        ck.atom(a_)
    # map body
    mb1 = q([ank], 'oveq1d', '( ( %s ` k ) x. %s ) = ( %s x. %s )' % (An, Ek, AV, Ek))
    mb2 = ringeq(w, Bk, '( %s x. %s )' % (AV, Ek), '( %s x. ( ( A ` k ) x. %s ) )' % (Pk, Ek), ck)
    mb = q([mb1, mb2], 'eqtrd', '( ( %s ` k ) x. %s ) = ( %s x. ( ( A ` k ) x. %s ) )' % (An, Ek, Pk, Ek))
    msum = w.s([mb], 'sumeq2dv', '( ( %s /\\ z e. %s ) -> sum_ k e. NN ( ( %s ` k ) x. %s ) = sum_ k e. NN ( %s x. ( ( A ` k ) x. %s ) ) )' % (A1n, HT, An, Ek, Pk, Ek))
    meq = t([w.s([msum], 'mpteq2dva', '( %s -> %s = %s )' % (A1n, DSn, MAP('n')))], 'adantr', '%s = %s' % (DSn, MAP('n')))
    # derivative body
    P1 = '( -u %s ^ ( n + 1 ) )' % Lk
    p1e = q([nkc, adk(nn1)], 'expp1d', '%s = ( %s x. -u %s )' % (P1, Pk, Lk))
    db1 = q([q([q([ank], 'oveq1d', '( ( %s ` k ) x. %s ) = ( %s x. %s )' % (An, Lk, AV, Lk))], 'oveq1d',
               '( ( ( %s ` k ) x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (An, Lk, Ek, AV, Lk, Ek))], 'negeqd',
            '-u ( ( ( %s ` k ) x. %s ) x. %s ) = -u ( ( %s x. %s ) x. %s )' % (An, Lk, Ek, AV, Lk, Ek))
    db2 = ringeq(w, Bk, '-u ( ( %s x. %s ) x. %s )' % (AV, Lk, Ek), '( ( %s x. -u %s ) x. ( ( A ` k ) x. %s ) )' % (Pk, Lk, Ek), ck)
    db3 = q([p1e], 'oveq1d', '( %s x. ( ( A ` k ) x. %s ) ) = ( ( %s x. -u %s ) x. ( ( A ` k ) x. %s ) )' % (P1, Ek, Pk, Lk, Ek))
    db = q([q([db1, db2], 'eqtrd', '-u ( ( ( %s ` k ) x. %s ) x. %s ) = ( ( %s x. -u %s ) x. ( ( A ` k ) x. %s ) )' % (An, Lk, Ek, Pk, Lk, Ek)), db3], 'eqtr4d',
           '-u ( ( ( %s ` k ) x. %s ) x. %s ) = ( %s x. ( ( A ` k ) x. %s ) )' % (An, Lk, Ek, P1, Ek))
    dsum = w.s([db], 'sumeq2dv', '( ( %s /\\ z e. %s ) -> sum_ k e. NN -u ( ( ( %s ` k ) x. %s ) x. %s ) = sum_ k e. NN ( %s x. ( ( A ` k ) x. %s ) ) )' % (A1n, HT, An, Lk, Ek, P1, Ek))
    deq = t([w.s([dsum], 'mpteq2dva', '( %s -> %s = %s )' % (A1n, DVn, MAP('( n + 1 )')))], 'adantr', '%s = %s' % (DVn, MAP('( n + 1 )')))
    # chain
    pmt = lift1(pm)
    ccst = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A1)
    c1 = t([ccst, pmt, nn, w.inst('dvnp1')], 'syl3anc', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D ( ( CC Dn %s ) ` n ) )' % (DSa, DSa))
    c2 = t([ih], 'oveq2d', '( CC _D ( ( CC Dn %s ) ` n ) ) = ( CC _D %s )' % (DSa, MAP('n')))
    c3 = t([meq], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (DSn, MAP('n')))
    c4 = t([c1, c2], 'eqtrd', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D %s )' % (DSa, MAP('n')))
    c5 = t([c4, c3], 'eqtr4d', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D %s )' % (DSa, DSn))
    step = t([c5, kdv2, deq], '3eqtrd', PSx('( n + 1 )'))
    ind = w.s([subs['0'], subs['n'], subs['n1'], subs['K'], base, step], 'nn0indd', '( ( %s /\\ K e. NN0 ) -> %s )' % (ph, PSx('K')))
    A0 = S['kddsdn'].split(' -> ( ( CC Dn')[0][2:]
    f = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (A0, fm))
    w.qed([f([f([f([], 'simp1', AGR), f([], 'simp2', '( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T )')], 'jca', ph), f([], 'simp3', 'K e. NN0')], 'jca', '( %s /\\ K e. NN0 )' % ph), ind],
          'syl', S['kddsdn'])
    return run(w)




if __name__ == '__main__':
    gen_dsdn()
