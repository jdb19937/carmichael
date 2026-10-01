"""Sortie KD1: termwise derivative of a Dirichlet series with coefficients O(m^B) on Re > 1 + B (kddsdv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from mvlib import ringeq
from lin import linarith

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_dsdv():
    w = W('kddsdv', 'A Dirichlet series whose coefficients grow at most like ` C m ^ B ` is holomorphic on ` Re > 1 + B ` and is differentiated termwise (C3 ` dserdv ` after the shift ` z -> z - B ` ).')
    A0 = S['kddsdv'].split(' -> ( ( ')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ag = s([], 'simpl', AGR)
    af = s([ag], 'simp1d', 'A : NN --> CC'); cr = s([ag], 'simp2d', 'C e. RR')
    bg = s([ag], 'simp3d', '( B e. RR+ /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) )')
    bp = s([bg], 'simpld', 'B e. RR+'); gr = s([bg], 'simprd', 'A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) )')
    tr = s([], 'simprl', 'T e. RR'); lt = s([], 'simprr', '( 1 + B ) < T')
    br = s([bp], 'rpred', 'B e. RR'); bc = s([br], 'recnd', 'B e. CC')
    Ap = '( j e. NN |-> ( ( A ` j ) x. ( j ^c -u B ) ) )'
    Tp = '( T - B )'
    DSp = DS(Ap, Tp); DSa = DS('A', 'T')
    HT, HTp = HP('T'), HP(Tp)
    # Ap maps into CC, value
    def apval(n, An):
        t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (An, f))
        nn = t([], 'simpr', '%s e. NN' % n)
        nr = t([nn], 'nnrpd', '%s e. RR+' % n)
        anc = t([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % An), nn], 'ffvelcdmd', '( A ` %s ) e. CC' % n)
        nb = t([nr, t([w.s([br], 'adantr', '( %s -> B e. RR )' % An)], 'renegcld', '-u B e. RR')], 'rpcxpcld', '( %s ^c -u B ) e. RR+' % n)
        val = '( ( A ` %s ) x. ( %s ^c -u B ) )' % (n, n)
        vc = t([anc, t([nb], 'rpcnd', '( %s ^c -u B ) e. CC' % n)], 'mulcld', '%s e. CC' % val)
        e1 = None if n == 'j' else w.s([w.s([], 'fveq2', '( j = %s -> ( A ` j ) = ( A ` %s ) )' % (n, n)), w.s([], 'oveq1', '( j = %s -> ( j ^c -u B ) = ( %s ^c -u B ) )' % (n, n))],
                 'oveq12d', '( j = %s -> ( ( A ` j ) x. ( j ^c -u B ) ) = %s )' % (n, val))
        v = fvmd(w, An, Ap, n, val, nn, vc, e1, var='j') if n != 'j' else None
        return dict(nn=nn, nr=nr, anc=anc, nb=nb, val=val, vc=vc, v=v)
    Aj = '( %s /\\ j e. NN )' % A0
    pj = apval('j', Aj)
    apf = s([pj['vc']], 'fmptd', '%s : NN --> CC' % Ap)
    # bound
    An = '( %s /\\ n e. NN )' % A0
    pn = apval('n', An)
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (An, f))
    cg = w.s([w.s([w.s([], 'fveq2', '( m = n -> ( A ` m ) = ( A ` n ) )')], 'fveq2d', '( m = n -> ( abs ` ( A ` m ) ) = ( abs ` ( A ` n ) ) )'),
              w.s([w.s([], 'oveq1', '( m = n -> ( m ^c B ) = ( n ^c B ) )')], 'oveq2d', '( m = n -> ( C x. ( m ^c B ) ) = ( C x. ( n ^c B ) ) )')],
             'breq12d', '( m = n -> ( ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) <-> ( abs ` ( A ` n ) ) <_ ( C x. ( n ^c B ) ) ) )')
    gn = t([pn['nn'], w.s([gr], 'adantr', '( %s -> A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) )' % An),
            w.s([cg], 'rspcv', '( n e. NN -> ( A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) -> ( abs ` ( A ` n ) ) <_ ( C x. ( n ^c B ) ) ) )')],
           'sylc', '( abs ` ( A ` n ) ) <_ ( C x. ( n ^c B ) )')
    NB = '( n ^c -u B )'
    nbr = t([pn['nb']], 'rpred', '%s e. RR' % NB); nbc = t([pn['nb']], 'rpcnd', '%s e. CC' % NB)
    ab1 = t([pn['v']], 'fveq2d', '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (Ap, pn['val']))
    ab2 = t([pn['anc'], nbc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( A ` n ) ) x. ( abs ` %s ) )' % (pn['val'], NB))
    ab3 = t([nbr, t([pn['nb']], 'rpge0d', '0 <_ %s' % NB)], 'absidd', '( abs ` %s ) = %s' % (NB, NB))
    ab4 = t([ab3], 'oveq2d', '( ( abs ` ( A ` n ) ) x. ( abs ` %s ) ) = ( ( abs ` ( A ` n ) ) x. %s )' % (NB, NB))
    ab5 = t([ab1, ab2, ab4], '3eqtrd', '( abs ` ( %s ` n ) ) = ( ( abs ` ( A ` n ) ) x. %s )' % (Ap, NB))
    NBp = '( n ^c B )'
    npb = t([pn['nr'], w.s([br], 'adantr', '( %s -> B e. RR )' % An)], 'rpcxpcld', '%s e. RR+' % NBp)
    crn = w.s([cr], 'adantr', '( %s -> C e. RR )' % An)
    cnb = t([crn, t([npb], 'rpred', '%s e. RR' % NBp)], 'remulcld', '( C x. %s ) e. RR' % NBp)
    l1 = t([t([pn['anc']], 'abscld', '( abs ` ( A ` n ) ) e. RR'), cnb, nbr, t([pn['nb']], 'rpge0d', '0 <_ %s' % NB), gn], 'lemul1ad',
           '( ( abs ` ( A ` n ) ) x. %s ) <_ ( ( C x. %s ) x. %s )' % (NB, NBp, NB))
    ncn = t([pn['nr']], 'rpcnd', 'n e. CC'); nne = t([pn['nr']], 'rpne0d', 'n =/= 0')
    bcn = w.s([bc], 'adantr', '( %s -> B e. CC )' % An)
    x1 = t([ncn, nne, bcn, t([bcn], 'negcld', '-u B e. CC')], 'cxpaddd', '( n ^c ( B + -u B ) ) = ( %s x. %s )' % (NBp, NB))
    x2 = t([t([bcn], 'negidd', '( B + -u B ) = 0')], 'oveq2d', '( n ^c ( B + -u B ) ) = ( n ^c 0 )')
    x3 = t([ncn], 'cxp0d', '( n ^c 0 ) = 1')
    x4 = t([x1, x2, x3], '3eqtr3d', '( %s x. %s ) = 1' % (NBp, NB))
    cc_ = t([crn], 'recnd', 'C e. CC')
    x5 = t([cc_, t([npb], 'rpcnd', '%s e. CC' % NBp), nbc], 'mulassd', '( ( C x. %s ) x. %s ) = ( C x. ( %s x. %s ) )' % (NBp, NB, NBp, NB))
    x6 = t([x5, t([x4], 'oveq2d', '( C x. ( %s x. %s ) ) = ( C x. 1 )' % (NBp, NB)), t([cc_], 'mulridd', '( C x. 1 ) = C')], '3eqtrd', '( ( C x. %s ) x. %s ) = C' % (NBp, NB))
    bnd_n = t([ab5, l1, x6], '3brtr4d' if False else 'T.', 'T.') if False else t([t([ab5, l1], 'eqbrtrd', '( abs ` ( %s ` n ) ) <_ ( ( C x. %s ) x. %s )' % (Ap, NBp, NB)), x6], 'breqtrd', '( abs ` ( %s ` n ) ) <_ C' % Ap)
    bndn = w.s([bnd_n], 'ralrimiva', '( %s -> A. n e. NN ( abs ` ( %s ` n ) ) <_ C )' % (A0, Ap))
    cbn = w.s([w.s([w.s([], 'fveq2', '( m = n -> ( %s ` m ) = ( %s ` n ) )' % (Ap, Ap))], 'fveq2d', '( m = n -> ( abs ` ( %s ` m ) ) = ( abs ` ( %s ` n ) ) )' % (Ap, Ap))],
              'breq1d', '( m = n -> ( ( abs ` ( %s ` m ) ) <_ C <-> ( abs ` ( %s ` n ) ) <_ C ) )' % (Ap, Ap))
    bndm = s([bndn, w.s([cbn], 'cbvralvw', '( A. m e. NN ( abs ` ( %s ` m ) ) <_ C <-> A. n e. NN ( abs ` ( %s ` n ) ) <_ C )' % (Ap, Ap))], 'sylibr',
             'A. m e. NN ( abs ` ( %s ` m ) ) <_ C' % Ap)
    c = Closure(w, A0, {'T': ('RR', tr), 'B': ('RR', br)})
    tpr = c.mem(Tp, 'RR')
    t1 = linarith(w, A0, [lt], '1 < %s' % Tp, closure=c)
    H1 = s([apf, cr, bndm], '3jca', '( %s : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ C )' % (Ap, Ap))
    H2 = s([tpr, t1], 'jca', '( %s e. RR /\\ 1 < %s )' % (Tp, Tp))
    dh = s([H1, H2, w.inst('dserhol')], 'syl2anc', HOLF(DSp, HTp))
    DVB = 'sum_ k e. NN -u ( ( ( %s ` k ) x. ( log ` k ) ) x. ( k ^c -u %s ) )'
    dv = s([H1, H2, w.inst('dserdv')], 'syl2anc', '( CC _D %s ) = ( z e. %s |-> %s )' % (DSp, HTp, DVB % (Ap, 'z')))
    DSz = DSp
    DSv = '( v e. %s |-> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) ) )' % (HTp, Ap)
    idzv = w.s([], 'id', '( z = v -> z = v )')
    czv, nzv = w.congr('sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u z ) )' % Ap, {'z': 'v'}, 'z = v', {'z': idzv})
    ezv = w.s([czv], 'cbvmptv', '%s = %s' % (DSz, DSv))
    ezva = w.s([ezv], 'a1i', '( %s -> %s = %s )' % (A0, DSz, DSv))
    dh = s([dh, holeq(w, A0, ezva, DSz, DSv, HTp)], 'mpbid', HOLF(DSv, HTp))
    dv = s([s([ezva], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (DSz, DSv)), dv], 'eqtr3d', '( CC _D %s ) = ( z e. %s |-> %s )' % (DSv, HTp, DVB % (Ap, 'z')))
    DSp = DSv
    # ---- the shift: z e. HP(T) gives z - B e. HP(T')
    Az = '( %s /\\ z e. %s )' % (A0, HT)
    u = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    adz = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Az, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    zin = u([], 'simpr', 'z e. %s' % HT)
    ez = u([zin, u([adz(tr), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ T < ( Re ` z ) ) )' % HT)], 'mpbid', '( z e. CC /\\ T < ( Re ` z ) )')
    zc = u([ez], 'simpld', 'z e. CC'); zlt = u([ez], 'simprd', 'T < ( Re ` z )')
    ZB = '( z - B )'
    zbc = u([zc, adz(bc)], 'subcld', '%s e. CC' % ZB)
    rz = u([zc, adz(bc)], 'resubd', '( Re ` %s ) = ( ( Re ` z ) - ( Re ` B ) )' % ZB)
    rb = u([adz(br), w.inst('rere')], 'syl', '( Re ` B ) = B')
    rz2 = u([rz, u([rb], 'oveq2d', '( ( Re ` z ) - ( Re ` B ) ) = ( ( Re ` z ) - B )')], 'eqtrd', '( Re ` %s ) = ( ( Re ` z ) - B )' % ZB)
    cz = Closure(w, Az, {'T': ('RR', adz(tr)), 'B': ('RR', adz(br)), '( Re ` z )': ('RR', u([zc], 'recld', '( Re ` z ) e. RR'))})
    cz.atom('( Re ` z )')
    zl2 = linarith(w, Az, [zlt], '%s < ( ( Re ` z ) - B )' % Tp, closure=cz)
    zl3 = u([zl2, rz2], 'breqtrrd', '%s < ( Re ` %s )' % (Tp, ZB))
    zbin = u([u([zbc, zl3], 'jca', '( %s e. CC /\\ %s < ( Re ` %s ) )' % (ZB, Tp, ZB)), u([adz(tpr), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ %s < ( Re ` %s ) ) )' % (ZB, HTp, ZB, Tp, ZB))],
             'mpbird', '%s e. %s' % (ZB, HTp))
    # per-k identities under ( Az /\ k e. NN )
    Ak = '( %s /\\ k e. NN )' % Az
    v = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    adk = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Ak, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    kn = v([], 'simpr', 'k e. NN')
    kr = v([kn], 'nnrpd', 'k e. RR+'); kc = v([kr], 'rpcnd', 'k e. CC'); kne = v([kr], 'rpne0d', 'k =/= 0')
    akc = v([adk(adz(af)), kn], 'ffvelcdmd', '( A ` k ) e. CC')
    KB = '( k ^c -u B )'; KZ = '( k ^c -u z )'; KZB = '( k ^c -u %s )' % ZB
    bck = adk(adz(bc)); zck = adk(zc)
    kbc = v([kc, v([bck], 'negcld', '-u B e. CC')], 'cxpcld', '%s e. CC' % KB)
    kzbc = v([kc, v([adk(zbc)], 'negcld', '-u %s e. CC' % ZB)], 'cxpcld', '%s e. CC' % KZB)
    kzc = v([kc, v([zck], 'negcld', '-u z e. CC')], 'cxpcld', '%s e. CC' % KZ)
    e1 = w.s([w.s([], 'fveq2', '( j = k -> ( A ` j ) = ( A ` k ) )'), w.s([], 'oveq1', '( j = k -> ( j ^c -u B ) = %s )' % KB)],
             'oveq12d', '( j = k -> ( ( A ` j ) x. ( j ^c -u B ) ) = ( ( A ` k ) x. %s ) )' % KB)
    apk = fvmd(w, Ak, Ap, 'k', '( ( A ` k ) x. %s )' % KB, kn, v([akc, kbc], 'mulcld', '( ( A ` k ) x. %s ) e. CC' % KB), e1, var='j')
    # k^-B k^-(z-B) = k^-z
    ex = v([kc, kne, v([bck], 'negcld', '-u B e. CC'), v([adk(zbc)], 'negcld', '-u %s e. CC' % ZB)], 'cxpaddd', '( k ^c ( -u B + -u %s ) ) = ( %s x. %s )' % (ZB, KB, KZB))
    ck = Closure(w, Ak, {'B': ('CC', bck), 'z': ('CC', zck)})
    exn = ringeq(w, Ak, '( -u B + -u %s )' % ZB, '-u z', ck)
    ex2 = v([v([exn], 'oveq2d', '( k ^c ( -u B + -u %s ) ) = %s' % (ZB, KZ)), ex], 'eqtr3d', '%s = ( %s x. %s )' % (KZ, KB, KZB))
    ck.leaf('( A ` k )', 'CC', akc); ck.leaf(KB, 'CC', kbc); ck.leaf(KZB, 'CC', kzbc)
    lk = v([kr], 'relogcld', '( log ` k ) e. RR'); lkc = v([lk], 'recnd', '( log ` k ) e. CC')
    ck.leaf('( log ` k )', 'CC', lkc)
    for a_ in ('( A ` k )', KB, KZB, '( log ` k )'):
        ck.atom(a_)
    # term of the series: ( Ap ` k ) x. k^-(z-B) = ( A ` k ) x. k^-z
    tt1 = v([apk], 'oveq1d', '( ( %s ` k ) x. %s ) = ( ( ( A ` k ) x. %s ) x. %s )' % (Ap, KZB, KB, KZB))
    tt2 = ringeq(w, Ak, '( ( ( A ` k ) x. %s ) x. %s )' % (KB, KZB), '( ( A ` k ) x. ( %s x. %s ) )' % (KB, KZB), ck)
    tt3 = v([ex2], 'oveq2d', '( ( A ` k ) x. %s ) = ( ( A ` k ) x. ( %s x. %s ) )' % (KZ, KB, KZB))
    term = v([tt1, tt2, tt3], '3eqtr4d', '( ( %s ` k ) x. %s ) = ( ( A ` k ) x. %s )' % (Ap, KZB, KZ))
    # derivative term
    dt1 = v([apk], 'oveq1d', '( ( %s ` k ) x. ( log ` k ) ) = ( ( ( A ` k ) x. %s ) x. ( log ` k ) )' % (Ap, KB))
    dt1b = v([dt1], 'oveq1d', '( ( ( %s ` k ) x. ( log ` k ) ) x. %s ) = ( ( ( ( A ` k ) x. %s ) x. ( log ` k ) ) x. %s )' % (Ap, KZB, KB, KZB))
    dt2 = ringeq(w, Ak, '( ( ( ( A ` k ) x. %s ) x. ( log ` k ) ) x. %s )' % (KB, KZB), '( ( ( A ` k ) x. ( log ` k ) ) x. ( %s x. %s ) )' % (KB, KZB), ck)
    dt3 = v([ex2], 'oveq2d', '( ( ( A ` k ) x. ( log ` k ) ) x. %s ) = ( ( ( A ` k ) x. ( log ` k ) ) x. ( %s x. %s ) )' % (KZ, KB, KZB))
    dterm0 = v([v([dt1b, dt2], 'eqtrd', '( ( ( %s ` k ) x. ( log ` k ) ) x. %s ) = ( ( ( A ` k ) x. ( log ` k ) ) x. ( %s x. %s ) )' % (Ap, KZB, KB, KZB)), dt3],
               'eqtr4d', '( ( ( %s ` k ) x. ( log ` k ) ) x. %s ) = ( ( ( A ` k ) x. ( log ` k ) ) x. %s )' % (Ap, KZB, KZ))
    dterm = v([dterm0], 'negeqd', '-u ( ( ( %s ` k ) x. ( log ` k ) ) x. %s ) = -u ( ( ( A ` k ) x. ( log ` k ) ) x. %s )' % (Ap, KZB, KZ))
    SUMp = 'sum_ k e. NN ( ( %s ` k ) x. %s )' % (Ap, KZB)
    SUMa = 'sum_ k e. NN ( ( A ` k ) x. %s )' % KZ
    sm = u([term], 'sumeq2dv', '%s = %s' % (SUMp, SUMa))
    idvz = w.s([], 'id', '( v = %s -> v = %s )' % (ZB, ZB))
    cvz2, nvz2 = w.congr('sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % Ap, {'v': ZB}, 'v = %s' % ZB, {'v': idvz})
    assert nvz2 == SUMp, nvz2
    fvv = w.s([cvz2, w.s([], 'eqid', '%s = %s' % (DSv, DSv))], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (ZB, HTp, SUMp, DSv, ZB, SUMp))
    dvl = u([zbin, w.s([w.s([], 'sumex', '%s e. _V' % SUMp)], 'a1i', '( %s -> %s e. _V )' % (Az, SUMp)), fvv], 'syl2anc', '( %s ` %s ) = %s' % (DSp, ZB, SUMp))
    vz = u([dvl, sm], 'eqtrd', '( %s ` %s ) = %s' % (DSp, ZB, SUMa))
    MPc = '( z e. %s |-> ( %s ` %s ) )' % (HT, DSp, ZB)
    meq = s([vz], 'mpteq2dva', '%s = %s' % (MPc, DSa))
    # ---- value of the derivative of the shifted series at z - B
    idzw = w.s([], 'id', '( z = w -> z = w )')
    cvz, nvz = w.congr(DVB % (Ap, 'z'), {'z': 'w'}, 'z = w', {'z': idzw})
    DVw = '( w e. %s |-> %s )' % (HTp, DVB % (Ap, 'w'))
    cbd = w.s([cvz], 'cbvmptv', '( z e. %s |-> %s ) = %s' % (HTp, DVB % (Ap, 'z'), DVw))
    dvw = s([dv, w.s([cbd], 'a1i', '( %s -> ( z e. %s |-> %s ) = %s )' % (A0, HTp, DVB % (Ap, 'z'), DVw))], 'eqtrd', '( CC _D %s ) = %s' % (DSp, DVw))
    idwz = w.s([], 'id', '( w = %s -> w = %s )' % (ZB, ZB))
    cwz, VAL = w.congr(DVB % (Ap, 'w'), {'w': ZB}, 'w = %s' % ZB, {'w': idwz})
    fvg = w.s([cwz, w.s([], 'eqid', '%s = %s' % (DVw, DVw))], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (ZB, HTp, VAL, DVw, ZB, VAL))
    vx = w.s([w.s([], 'sumex', '%s e. _V' % VAL)], 'a1i', '( %s -> %s e. _V )' % (Az, VAL))
    dz1 = u([zbin, vx, fvg], 'syl2anc', '( %s ` %s ) = %s' % (DVw, ZB, VAL))
    dz2 = u([u([adz(dvw)], 'fveq1d', '( ( CC _D %s ) ` %s ) = ( %s ` %s )' % (DSp, ZB, DVw, ZB)), dz1], 'eqtrd', '( ( CC _D %s ) ` %s ) = %s' % (DSp, ZB, VAL))
    TARG = 'sum_ k e. NN -u ( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u z ) )'
    assert VAL == DVB % (Ap, ZB), VAL
    dz3 = u([dterm], 'sumeq2dv', '%s = %s' % (VAL, TARG))
    dz4 = u([dz2, dz3], 'eqtrd', '( ( CC _D %s ) ` %s ) = %s' % (DSp, ZB, TARG))
    # ---- chain rule
    cpr = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
    b10 = w.s([w.s([], 'ovex', '( 1 - 0 ) e. _V')], 'a1i', '( %s -> ( 1 - 0 ) e. _V )' % Az)
    Ay = '( %s /\\ y e. %s )' % (A0, HTp)
    dcn = s([dh, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (DSp, HTp))
    dff = s([dcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (DSp, HTp))
    cy = w.s([w.s([dff], 'adantr', '( %s -> %s : %s --> CC )' % (Ay, DSp, HTp)), w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, HTp))], 'ffvelcdmd', '( %s -> ( %s ` y ) e. CC )' % (Ay, DSp))
    dyx = w.s([w.s([], 'fvex', '( ( CC _D %s ) ` y ) e. _V' % DSp)], 'a1i', '( %s -> ( ( CC _D %s ) ` y ) e. _V )' % (Ay, DSp))
    # da: derivative of z - B on HP(T)
    Ac = '( %s /\\ z e. CC )' % A0
    zcc = w.s([], 'simpr', '( %s -> z e. CC )' % Ac)
    one_ = w.s([w.s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % Ac)
    bcc = w.s([bc], 'adantr', '( %s -> B e. CC )' % Ac)
    zer = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % Ac)
    did = s([cpr], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    dcs = s([cpr, bc], 'dvmptc', '( CC _D ( z e. CC |-> B ) ) = ( z e. CC |-> 0 )')
    dsub = s([cpr, zcc, one_, did, bcc, zer, dcs], 'dvmptsub', '( CC _D ( z e. CC |-> ( z - B ) ) ) = ( z e. CC |-> ( 1 - 0 ) )')
    zbcc = w.s([zcc, bcc], 'subcld', '( %s -> ( z - B ) e. CC )' % Ac)
    b10c = w.s([w.s([], 'ovex', '( 1 - 0 ) e. _V')], 'a1i', '( %s -> ( 1 - 0 ) e. _V )' % Ac)
    Azz = Az
    hss0 = w.s([zc], 'ex', '( %s -> ( z e. %s -> z e. CC ) )' % (A0, HT))
    hss = s([hss0], 'ssrdv', '%s C_ CC' % HT)
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    hop = w.s([w.s([], 'hpopn', '%s e. %s' % (HT, TOP))], 'a1i', '( %s -> %s e. %s )' % (A0, HT, TOP))
    da = s([cpr, zbcc, b10c, dsub, hss, jr, ej, hop], 'dvmptres', '( CC _D ( z e. %s |-> ( z - B ) ) ) = ( z e. %s |-> ( 1 - 0 ) )' % (HT, HT))
    # dc
    fn1 = s([dff, w.inst('ffn')], 'syl', '%s Fn %s' % (DSp, HTp))
    ea = s([fn1, w.s([], 'dffn5', '( %s Fn %s <-> %s = ( y e. %s |-> ( %s ` y ) ) )' % (DSp, HTp, DSp, HTp, DSp))], 'sylib', '%s = ( y e. %s |-> ( %s ` y ) )' % (DSp, HTp, DSp))
    fn2 = s([s([dh, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (DSp, HTp)), w.inst('ffn')], 'syl', '( CC _D %s ) Fn %s' % (DSp, HTp))
    eb = s([fn2, w.s([], 'dffn5', '( ( CC _D %s ) Fn %s <-> ( CC _D %s ) = ( y e. %s |-> ( ( CC _D %s ) ` y ) ) )' % (DSp, HTp, DSp, HTp, DSp))], 'sylib',
           '( CC _D %s ) = ( y e. %s |-> ( ( CC _D %s ) ` y ) )' % (DSp, HTp, DSp))
    dc = s([s([ea], 'oveq2d', '( CC _D %s ) = ( CC _D ( y e. %s |-> ( %s ` y ) ) )' % (DSp, HTp, DSp)), eb], 'eqtr3d',
           '( CC _D ( y e. %s |-> ( %s ` y ) ) ) = ( y e. %s |-> ( ( CC _D %s ) ` y ) )' % (HTp, DSp, HTp, DSp))
    ce = w.s([], 'fveq2', '( y = %s -> ( %s ` y ) = ( %s ` %s ) )' % (ZB, DSp, DSp, ZB))
    cf = w.s([], 'fveq2', '( y = %s -> ( ( CC _D %s ) ` y ) = ( ( CC _D %s ) ` %s ) )' % (ZB, DSp, DSp, ZB))
    CO = '( z e. %s |-> ( ( ( CC _D %s ) ` %s ) x. ( 1 - 0 ) ) )' % (HT, DSp, ZB)
    chain = s([cpr, cpr, zbin, b10, cy, dyx, da, dc, ce, cf], 'dvmptco', '( CC _D %s ) = %s' % (MPc, CO))
    # final derivative
    d1 = s([meq], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (MPc, DSa))
    fz1 = u([u([w.s([w.s([], '1m0e1', '( 1 - 0 ) = 1')], 'a1i', '( %s -> ( 1 - 0 ) = 1 )' % Az)], 'oveq2d',
                '( ( ( CC _D %s ) ` %s ) x. ( 1 - 0 ) ) = ( ( ( CC _D %s ) ` %s ) x. 1 )' % (DSp, ZB, DSp, ZB)),
             u([u([adz(s([dh, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (DSp, HTp))), zbin], 'ffvelcdmd', '( ( CC _D %s ) ` %s ) e. CC' % (DSp, ZB))],
               'mulridd', '( ( ( CC _D %s ) ` %s ) x. 1 ) = ( ( CC _D %s ) ` %s )' % (DSp, ZB, DSp, ZB)), dz4],
            '3eqtrd', '( ( ( CC _D %s ) ` %s ) x. ( 1 - 0 ) ) = %s' % (DSp, ZB, TARG))
    d2 = s([fz1], 'mpteq2dva', '%s = ( z e. %s |-> %s )' % (CO, HT, TARG))
    DER = s([d1, chain, d2], '3eqtr3d', '( CC _D %s ) = ( z e. %s |-> %s )' % (DSa, HT, TARG))
    # holomorphy
    sac = u([vz, u([adz(dff), zbin], 'ffvelcdmd', '( %s ` %s ) e. CC' % (DSp, ZB))], 'eqeltrrd', '%s e. CC' % SUMa)
    daf = s([sac], 'fmptd', '%s : %s --> CC' % (DSa, HT))
    tex = w.s([w.s([], 'sumex', '%s e. _V' % TARG)], 'a1i', '( %s -> %s e. _V )' % (Az, TARG))
    dmm = s([s([tex], 'ralrimiva', 'A. z e. %s %s e. _V' % (HT, TARG)), w.inst('dmmptg')], 'syl', 'dom ( z e. %s |-> %s ) = %s' % (HT, TARG, HT))
    dm2 = s([s([DER], 'dmeqd', 'dom ( CC _D %s ) = dom ( z e. %s |-> %s )' % (DSa, HT, TARG)), dmm], 'eqtrd', 'dom ( CC _D %s ) = %s' % (DSa, HT))
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    cnt = s([s([ccs, daf, hss], '3jca', '( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC )' % (DSa, HT, HT)), dm2, w.inst('dvcn')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (DSa, HT))
    sd = s([dm2, w.inst('eqimss2')], 'syl', '%s C_ dom ( CC _D %s )' % (HT, DSa))
    hol = s([cnt, sd], 'jca', HOLF(DSa, HT))
    w.qed([hol, DER], 'jca', S['kddsdv'])
    return run(w)




if __name__ == '__main__':
    gen_dsdv()
