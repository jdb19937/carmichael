"""ZL3b E6: sums over ZZ (zl3pzm, zl3grc) and the Gaussian transformation (zl3thg0, zl3c1, zl3thg).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_e6.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of
from zl3b_d2 import cst
from zl3b_e3 import fvm, HOLt
from zl3b_e4 import p_nn0
from zl3b_e5 import Q, Prod
import lin, congr

only = sys.argv[1:]
S = STATEMENTS


def spec(w, A_, allst, var, body, val, valmem, g):
    """( A_ -> body[val] ) from allst: ( A_ -> A. var e. X body ); body a function of the variable"""
    E = '%s = %s' % (var, val)
    ie = w.s([], 'id', '( %s -> %s )' % (E, E))
    st, nt = congr.wff_congruence(body(var), {var: val}, E, {var: ie}, g)
    w.lines.extend(g.lines); g.lines = []
    return w.s([st, allst, valmem], 'rspcdva', '( %s -> %s )' % (A_, body(val)))


# ---------------------------------------------------------------- zl3pzm
if __name__ == '__main__' and (not only or 'zl3pzm' in only):
    w = W('zl3pzm', 'A constant factor comes out of a sum over ` ZZ ` of the form ` PZ `.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3pzm'])
    cc = w.s([], 'simpl1', '( %s -> C e. CC )' % ph)
    AL = 'A. m e. ZZ ( ( H ` m ) e. CC /\\ ( G ` m ) = ( C x. ( H ` m ) ) )'
    al = w.s([], 'simprl', '( %s -> %s )' % (ph, AL))
    SQ = 'seq 1 ( + , ( m e. NN |-> ( ( H ` m ) + ( H ` -u m ) ) ) )'
    cv = w.s([], 'simprr', '( %s -> %s e. dom ~~> )' % (ph, SQ))
    B = lambda v: '( ( H ` %s ) e. CC /\\ ( G ` %s ) = ( C x. ( H ` %s ) ) )' % (v, v, v)
    b0 = spec(w, ph, al, 'm', B, '0', cst(w, ph, '0z', '0 e. ZZ'), g)
    An = '( %s /\\ n e. NN )' % ph
    nz = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'nnzd', '( %s -> n e. ZZ )' % An)
    aln = w.s([al], 'adantr', '( %s -> %s )' % (An, AL))
    bn = spec(w, An, aln, 'm', B, 'n', nz, g)
    bm = spec(w, An, aln, 'm', B, '-u n', D(w, An, 'znegcld', [nz], '-u n e. ZZ'), g)
    h0 = w.s([b0], 'simpld', '( %s -> ( H ` 0 ) e. CC )' % ph); g0 = w.s([b0], 'simprd', '( %s -> ( G ` 0 ) = ( C x. ( H ` 0 ) ) )' % ph)
    hn = w.s([bn], 'simpld', '( %s -> ( H ` n ) e. CC )' % An); gn = w.s([bn], 'simprd', '( %s -> ( G ` n ) = ( C x. ( H ` n ) ) )' % An)
    hm = w.s([bm], 'simpld', '( %s -> ( H ` -u n ) e. CC )' % An); gm = w.s([bm], 'simprd', '( %s -> ( G ` -u n ) = ( C x. ( H ` -u n ) ) )' % An)
    HN = '( ( H ` n ) + ( H ` -u n ) )'
    cn = w.s([cc], 'adantr', '( %s -> C e. CC )' % An)
    pt = D(w, An, 'eqtr4d', [D(w, An, 'oveq12d', [gn, gm], '( ( G ` n ) + ( G ` -u n ) ) = ( ( C x. ( H ` n ) ) + ( C x. ( H ` -u n ) ) )'),
                             D(w, An, 'adddid', [cn, hn, hm], '( C x. %s ) = ( ( C x. ( H ` n ) ) + ( C x. ( H ` -u n ) ) )' % HN)], '( ( G ` n ) + ( G ` -u n ) ) = ( C x. %s )' % HN)
    se = w.s([pt], 'sumeq2dv', '( %s -> sum_ n e. NN ( ( G ` n ) + ( G ` -u n ) ) = sum_ n e. NN ( C x. %s ) )' % (ph, HN))
    FM = '( m e. NN |-> ( ( H ` m ) + ( H ` -u m ) ) )'
    fv, _ = fvm(w, An, 'm', '( ( H ` m ) + ( H ` -u m ) )', 'n', w.s([], 'simpr', '( %s -> n e. NN )' % An), g) if False else (None, None)
    Em = 'm = n'
    ie = w.s([], 'id', '( %s -> %s )' % (Em, Em))
    stm = D(w, Em, 'oveq12d', [D(w, Em, 'fveq2d', [ie], '( H ` m ) = ( H ` n )'), D(w, Em, 'fveq2d', [D(w, Em, 'negeqd', [ie], '-u m = -u n')], '( H ` -u m ) = ( H ` -u n )')], '( ( H ` m ) + ( H ` -u m ) ) = %s' % HN)
    fv = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An), w.s([stm, w.s([], 'eqid', '%s = %s' % (FM, FM)), w.s([], 'ovex', '%s e. _V' % HN)], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (FM, HN))], 'syl', '( %s -> ( %s ` n ) = %s )' % (An, FM, HN))
    hnc = D(w, An, 'addcld', [hn, hm], '%s e. CC' % HN)
    im = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), fv, hnc, cv, cc], 'isummulc2', '( %s -> ( C x. sum_ n e. NN %s ) = sum_ n e. NN ( C x. %s ) )' % (ph, HN, HN))
    SH = 'sum_ n e. NN %s' % HN
    shc = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), fv, hnc, cv], 'isumcl', '( %s -> %s e. CC )' % (ph, SH))
    SG = 'sum_ n e. NN ( ( G ` n ) + ( G ` -u n ) )'
    sg = D(w, ph, 'eqtr4d', [se, im], '%s = ( C x. %s )' % (SG, SH))
    fin = D(w, ph, 'eqtr4d', [D(w, ph, 'oveq12d', [g0, sg], '( ( G ` 0 ) + %s ) = ( ( C x. ( H ` 0 ) ) + ( C x. %s ) )' % (SG, SH)),
                              D(w, ph, 'adddid', [cc, h0, shc], '( C x. ( ( H ` 0 ) + %s ) ) = ( ( C x. ( H ` 0 ) ) + ( C x. %s ) )' % (SH, SH))],
            '( ( G ` 0 ) + %s ) = ( C x. ( ( H ` 0 ) + %s ) )' % (SG, SH))
    w.qed([fin], 'idi', S['zl3pzm'])
    go(w, only)


def both(w, A_, st, lhs, rhs):
    return [D(w, A_, 'eqled', [st], '%s <_ %s' % (lhs, rhs)), D(w, A_, 'eqled', [D(w, A_, 'eqcomd', [st], '%s = %s' % (rhs, lhs))], '%s <_ %s' % (rhs, lhs))]


GRB = lambda k: '( ( %s ^ P ) x. ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. A ) ) ) ) )' % (k, k, k)


def gr_val(w, A_, Z, zz):
    """( A_ -> ( GR ` Z ) = GRB(Z) ) for zz: ( A_ -> Z e. ZZ )"""
    assert GAR == '( k e. ZZ |-> %s )' % GRB('k')
    E = 'k = %s' % Z
    ie = w.s([], 'id', '( %s -> %s )' % (E, E))
    st = D(w, E, 'oveq12d', [D(w, E, 'oveq1d', [ie], '( k ^ P ) = ( %s ^ P )' % Z),
                             D(w, E, 'oveq12d', [D(w, E, 'fveq2d', [D(w, E, 'negeqd', [D(w, E, 'oveq2d', [D(w, E, 'oveq1d', [D(w, E, 'oveq1d', [ie], '( k ^ 2 ) = ( %s ^ 2 )' % Z)], '( ( k ^ 2 ) / T ) = ( ( %s ^ 2 ) / T )' % Z)],
                                                                                              '( _pi x. ( ( k ^ 2 ) / T ) ) = ( _pi x. ( ( %s ^ 2 ) / T ) )' % Z)], '-u ( _pi x. ( ( k ^ 2 ) / T ) ) = -u ( _pi x. ( ( %s ^ 2 ) / T ) )' % Z)],
                                                   '( exp ` -u ( _pi x. ( ( k ^ 2 ) / T ) ) ) = ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) )' % Z),
                                                 D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [D(w, E, 'oveq1d', [ie], '( k x. A ) = ( %s x. A )' % Z)], '( ( 2 x. ( _i x. _pi ) ) x. ( k x. A ) ) = ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. A ) )' % Z)],
                                                   '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( k x. A ) ) ) = ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. A ) ) )' % Z)],
                               '( ( exp ` -u ( _pi x. ( ( k ^ 2 ) / T ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( k x. A ) ) ) ) = ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. A ) ) ) )' % (Z, Z))],
            '%s = %s' % (GRB('k'), GRB(Z)))
    return w.s([zz, w.s([st, w.s([], 'eqid', '%s = %s' % (GAR, GAR)), w.s([], 'ovex', '%s e. _V' % GRB(Z))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (Z, GAR, Z, GRB(Z)))],
               'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, GAR, Z, GRB(Z)))


def abs_gr(w, A_, Z, zz, q, absZ, absZeq, sq_eq):
    """( A_ -> ( abs ` ( GR ` Z ) ) = ( ( absZ ^ P ) x. ( exp ` -u ( _pi x. ( ( absZ ^ 2 ) / T ) ) ) ) ); absZeq: ( abs ` Z ) = absZ ; sq_eq: ( Z ^ 2 ) = ( absZ ^ 2 )"""
    v = gr_val(w, A_, Z, zz)
    E1 = '( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) )' % Z; E2 = '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. A ) ) )' % Z
    ZP = '( %s ^ P )' % Z
    a1 = q.d('absmuld', [q.c(ZP), q.c('( %s x. %s )' % (E1, E2))], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (GRB(Z), ZP, E1, E2))
    a2 = q.d('absmuld', [q.c(E1), q.c(E2)], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (E1, E2, E1, E2))
    x1 = '-u ( _pi x. ( ( %s ^ 2 ) / T ) )' % Z
    x1r = q.cl.mem(x1, 'RR')
    e1 = q.d('absidd', [q.d('reefcld', [x1r], '%s e. RR' % E1), q.d('rpge0d', [q.d('rpefcld', [x1r], '%s e. RR+' % E1)], '0 <_ %s' % E1)], '( abs ` %s ) = %s' % (E1, E1))
    TIP = '( 2 x. ( _i x. _pi ) )'; ZA = '( %s x. A )' % Z
    r1 = q.chain('( %s x. %s )' % (TIP, ZA), [(q.d('oveq1d', [q.eq('mul12d', ['2', '_i', '_pi'], TIP, '( _i x. ( 2 x. _pi ) )')], '( %s x. %s ) = ( ( _i x. ( 2 x. _pi ) ) x. %s )' % (TIP, ZA, ZA)), '( ( _i x. ( 2 x. _pi ) ) x. %s )' % ZA),
                                              (q.eq('mulassd', ['_i', '( 2 x. _pi )', ZA], '( ( _i x. ( 2 x. _pi ) ) x. %s )' % ZA, '( _i x. ( ( 2 x. _pi ) x. %s ) )' % ZA), '( _i x. ( ( 2 x. _pi ) x. %s ) )' % ZA)])
    RB = '( ( 2 x. _pi ) x. %s )' % ZA
    e2 = q.d('eqtrd', [q.d('fveq2d', [q.d('fveq2d', [r1], '%s = ( exp ` ( _i x. %s ) )' % (E2, RB))], '( abs ` %s ) = ( abs ` ( exp ` ( _i x. %s ) ) )' % (E2, RB)),
                       w.s([q.cl.mem(RB, 'RR'), w.inst('absefi')], 'syl', '( %s -> ( abs ` ( exp ` ( _i x. %s ) ) ) = 1 )' % (A_, RB))], '( abs ` %s ) = 1' % E2)
    pn = q.cl.leaves['P'] if False else None
    zp = q.d('eqtrd', [q.d('absexpd', [q.c(Z), q.cl.mem('P', 'NN0')], '( abs ` %s ) = ( ( abs ` %s ) ^ P )' % (ZP, Z)), q.d('oveq1d', [absZeq], '( ( abs ` %s ) ^ P ) = ( %s ^ P )' % (Z, absZ))],
                   '( abs ` %s ) = ( %s ^ P )' % (ZP, absZ))
    ex1 = q.d('fveq2d', [q.d('negeqd', [q.d('oveq2d', [q.d('oveq1d', [sq_eq], '( ( %s ^ 2 ) / T ) = ( ( %s ^ 2 ) / T )' % (Z, absZ))], '( _pi x. ( ( %s ^ 2 ) / T ) ) = ( _pi x. ( ( %s ^ 2 ) / T ) )' % (Z, absZ))],
                                       '-u ( _pi x. ( ( %s ^ 2 ) / T ) ) = -u ( _pi x. ( ( %s ^ 2 ) / T ) )' % (Z, absZ))], '%s = ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) )' % (E1, absZ))
    EA = '( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) )' % absZ
    m = q.d('eqtrd', [q.d('oveq12d', [e1, e2], '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. 1 )' % (E1, E2, E1)), q.d('eqtrd', [q.d('mulridd', [q.c(E1)], '( %s x. 1 ) = %s' % (E1, E1)), ex1], '( %s x. 1 ) = %s' % (E1, EA))],
            '( ( abs ` %s ) x. ( abs ` %s ) ) = %s' % (E1, E2, EA))
    tot = q.chain('( abs ` ( %s ` %s ) )' % (GAR, Z), [(q.d('fveq2d', [v], '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (GAR, Z, GRB(Z))), '( abs ` %s )' % GRB(Z)),
                                                         (a1, '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (ZP, E1, E2)),
                                                         (q.d('oveq12d', [zp, q.d('eqtrd', [a2, m], '( abs ` ( %s x. %s ) ) = %s' % (E1, E2, EA))], '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) ) = ( ( %s ^ P ) x. %s )' % (ZP, E1, E2, absZ, EA)),
                                                          '( ( %s ^ P ) x. %s )' % (absZ, EA))])
    return tot


# ---------------------------------------------------------------- zl3grc
if __name__ == '__main__' and (not only or 'zl3grc' in only):
    w = W('zl3grc', 'The sum over ` ZZ ` of ` GR ` converges.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3grc'])
    tp = w.s([], 'simp1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simp2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simp3', '( %s -> P e. { 0 , 1 } )' % ph)
    pn = p_nn0(w, ph, pp)
    C = '( _pi / T )'
    cp = D(w, ph, 'rpdivcld', [cst(w, ph, 'pirp', '_pi e. RR+'), tp], '%s e. RR+' % C)
    cr = D(w, ph, 'rpred', [cp], '%s e. RR' % C)
    H = '-u ( %s / 2 )' % C
    hr = D(w, ph, 'renegcld', [D(w, ph, 'rehalfcld', [cr], '( %s / 2 ) e. RR' % C)], '%s e. RR' % H)
    R = '( exp ` %s )' % H
    rr = D(w, ph, 'reefcld', [hr], '%s e. RR' % R); r0 = D(w, ph, 'rpge0d', [D(w, ph, 'rpefcld', [hr], '%s e. RR+' % R)], '0 <_ %s' % R)
    hneg = D(w, ph, 'lt0neg2d', [D(w, ph, 'rehalfcld', [cr], '( %s / 2 ) e. RR' % C)], '( 0 < ( %s / 2 ) <-> %s < 0 )' % (C, H)) if False else None
    h0 = D(w, ph, 'mpbid', [D(w, ph, 'rpgt0d', [D(w, ph, 'rphalfcld', [cp], '( %s / 2 ) e. RR+' % C)], '0 < ( %s / 2 )' % C), D(w, ph, 'lt0neg2d', [D(w, ph, 'rehalfcld', [cr], '( %s / 2 ) e. RR' % C)], '( 0 < ( %s / 2 ) <-> %s < 0 )' % (C, H))],
           '%s < 0' % H)
    r1 = D(w, ph, 'eqbrtrd', [D(w, ph, 'eqidd', [], '%s = %s' % (R, R)), D(w, ph, 'breqtrd', [D(w, ph, 'mpbid', [h0, D(w, ph, 'syl2anc', [hr, cst(w, ph, '0re', '0 e. RR'), w.inst('eflt')], '( %s < 0 <-> %s < ( exp ` 0 ) )' % (H, R))], '%s < ( exp ` 0 )' % R),
                                                                                                cst(w, ph, 'ef0', '( exp ` 0 ) = 1')], '%s < 1' % R)], '%s < 1' % R)
    D2 = '( 2 / %s )' % C
    B = '( 2 x. %s )' % D2
    d2r = D(w, ph, 'rerpdivcld', [cst(w, ph, '2re', '2 e. RR'), cp], '%s e. RR' % D2)
    br = D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), d2r], '%s e. RR' % B)
    FM = '( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) )' % (GAR, GAR)
    Ak = '( %s /\\ n e. NN )' % ph
    kn = w.s([], 'simpr', '( %s -> n e. NN )' % Ak)
    kz = D(w, Ak, 'nnzd', [kn], 'n e. ZZ'); kr = D(w, Ak, 'nnred', [kn], 'n e. RR'); k1 = D(w, Ak, 'nnge1d', [kn], '1 <_ n')
    La = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Ak, f))
    q = Q(w, Ak, {'T': La(tp, 'T e. RR+'), 'A': La(ar, 'A e. RR'), 'P': La(pn, 'P e. NN0'), 'n': kz, '_i': cst(w, Ak, 'ax-icn', '_i e. CC'), '_pi': cst(w, Ak, 'pirp', '_pi e. RR+')})
    Em = 'm = n'
    ie = w.s([], 'id', '( %s -> %s )' % (Em, Em))
    stm = D(w, Em, 'oveq12d', [D(w, Em, 'fveq2d', [ie], '( %s ` m ) = ( %s ` n )' % (GAR, GAR)), D(w, Em, 'fveq2d', [D(w, Em, 'negeqd', [ie], '-u m = -u n')], '( %s ` -u m ) = ( %s ` -u n )' % (GAR, GAR))],
            '( ( %s ` m ) + ( %s ` -u m ) ) = ( ( %s ` n ) + ( %s ` -u n ) )' % (GAR, GAR, GAR, GAR))
    FK = '( ( %s ` n ) + ( %s ` -u n ) )' % (GAR, GAR)
    fv = w.s([kn, w.s([stm, w.s([], 'eqid', '%s = %s' % (FM, FM)), w.s([], 'ovex', '%s e. _V' % FK)], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (FM, FK))], 'syl', '( %s -> ( %s ` n ) = %s )' % (Ak, FM, FK))
    nkz = D(w, Ak, 'znegcld', [kz], '-u n e. ZZ')
    g1 = D(w, Ak, 'eqeltrd', [gr_val(w, Ak, 'n', kz), q.c(GRB('n'))], '( %s ` n ) e. CC' % GAR)
    g2 = D(w, Ak, 'eqeltrd', [gr_val(w, Ak, '-u n', nkz), q.c(GRB('-u n'))], '( %s ` -u n ) e. CC' % GAR)
    fkc = D(w, Ak, 'eqeltrd', [fv, D(w, Ak, 'addcld', [g1, g2], '%s e. CC' % FK)], '( %s ` n ) e. CC' % FM)
    kc = q.c('n')
    ak = D(w, Ak, 'absidd', [kr, D(w, Ak, 'nnnn0d', [kn], 'n e. NN0') if False else D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), kr, D(w, Ak, 'nngt0d', [kn], '0 < n')], '0 <_ n')], '( abs ` n ) = n')
    ag1 = abs_gr(w, Ak, 'n', kz, q, 'n', ak, D(w, Ak, 'eqidd', [], '( n ^ 2 ) = ( n ^ 2 )'))
    ag2 = abs_gr(w, Ak, '-u n', nkz, q, 'n', D(w, Ak, 'eqtrd', [D(w, Ak, 'absnegd', [kc], '( abs ` -u n ) = ( abs ` n )'), ak], '( abs ` -u n ) = n'), D(w, Ak, 'sqnegd', [kc], '( -u n ^ 2 ) = ( n ^ 2 )'))
    VK = '( ( n ^ P ) x. ( exp ` -u ( _pi x. ( ( n ^ 2 ) / T ) ) ) )'
    # V_k <_ D2 x. E1 with E1 = R ^ k
    E1 = '( %s ^ n )' % R
    Y = '( n x. ( %s / 2 ) )' % C
    cr1 = La(cr, '%s e. RR' % C); c01 = D(w, Ak, 'rpge0d', [La(cp, '%s e. RR+' % C)], '0 <_ %s' % C)
    yr = D(w, Ak, 'remulcld', [kr, D(w, Ak, 'rehalfcld', [cr1], '( %s / 2 ) e. RR' % C)], '%s e. RR' % Y)
    y0 = D(w, Ak, 'mulge0d', [kr, D(w, Ak, 'rehalfcld', [cr1], '( %s / 2 ) e. RR' % C), D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), kr, D(w, Ak, 'nngt0d', [kn], '0 < n')], '0 <_ n'),
                               D(w, Ak, 'rpge0d', [D(w, Ak, 'rphalfcld', [La(cp, '%s e. RR+' % C)], '( %s / 2 ) e. RR+' % C)], '0 <_ ( %s / 2 )' % C)], '0 <_ %s' % Y)
    KH = '( n x. %s )' % H
    e1e = D(w, Ak, 'eqcomd', [w.s([q.c(H), kz, w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` %s ) = %s )' % (Ak, KH, E1))], '%s = ( exp ` %s )' % (E1, KH))
    kh = q.eq('mulneg2d', ['n', '( %s / 2 )' % C], KH, '-u %s' % Y)
    e1y = D(w, Ak, 'eqtrd', [e1e, D(w, Ak, 'fveq2d', [kh], '( exp ` %s ) = ( exp ` -u %s )' % (KH, Y))], '%s = ( exp ` -u %s )' % (E1, Y))
    ey = '( exp ` %s )' % Y; eny = '( exp ` -u %s )' % Y
    e1r = D(w, Ak, 'reefcld', [D(w, Ak, 'renegcld', [yr], '-u %s e. RR' % Y)], '%s e. RR' % eny); e10 = D(w, Ak, 'rpge0d', [D(w, Ak, 'rpefcld', [D(w, Ak, 'renegcld', [yr], '-u %s e. RR' % Y)], '%s e. RR+' % eny)], '0 <_ %s' % eny)
    eyr = D(w, Ak, 'reefcld', [yr], '%s e. RR' % ey)
    bv = D(w, Ak, 'syl2anc', [yr, y0, w.inst('bvefge1p')], '( 1 + %s ) <_ %s' % (Y, ey))
    f1 = D(w, Ak, 'lemul1ad', [D(w, Ak, 'readdcld', [cst(w, Ak, '1re', '1 e. RR'), yr], '( 1 + %s ) e. RR' % Y), eyr, e1r, e10, bv], '( ( 1 + %s ) x. %s ) <_ ( %s x. %s )' % (Y, eny, ey, eny))
    one = D(w, Ak, 'eqtrd', [D(w, Ak, 'eqcomd', [D(w, Ak, 'syl2anc', [q.c(Y), q.c('-u %s' % Y), w.inst('efadd')], '( exp ` ( %s + -u %s ) ) = ( %s x. %s )' % (Y, Y, ey, eny))], '( %s x. %s ) = ( exp ` ( %s + -u %s ) )' % (ey, eny, Y, Y)),
                             D(w, Ak, 'eqtrd', [D(w, Ak, 'fveq2d', [q.eq('negidd', [Y], '( %s + -u %s )' % (Y, Y), '0')], '( exp ` ( %s + -u %s ) ) = ( exp ` 0 )' % (Y, Y)), cst(w, Ak, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( %s + -u %s ) ) = 1' % (Y, Y))],
              '( %s x. %s ) = 1' % (ey, eny))
    ye = lin.linarith(w, Ak, [f1, e10] + both(w, Ak, one, '( %s x. %s )' % (ey, eny), '1'), '( %s x. %s ) <_ 1' % (Y, eny), leaves={Y: yr, eny: e1r, ey: eyr}, atoms=[Y, eny, ey], products=True)
    d2r1 = La(d2r, '%s e. RR' % D2)
    d2e = D(w, Ak, 'remulcld', [d2r1, e1r], '( %s x. %s ) e. RR' % (D2, eny))
    d2e0 = D(w, Ak, 'mulge0d', [d2r1, e1r, D(w, Ak, 'rpge0d', [D(w, Ak, 'rpdivcld', [cst(w, Ak, '2rp', '2 e. RR+'), La(cp, '%s e. RR+' % C)], '%s e. RR+' % D2)], '0 <_ %s' % D2), e10], '0 <_ ( %s x. %s )' % (D2, eny))
    f2 = D(w, Ak, 'lemul2ad', [D(w, Ak, 'remulcld', [yr, e1r], '( %s x. %s ) e. RR' % (Y, eny)), cst(w, Ak, '1re', '1 e. RR'), d2e, d2e0, ye], '( ( %s x. %s ) x. ( %s x. %s ) ) <_ ( ( %s x. %s ) x. 1 )' % (D2, eny, Y, eny, D2, eny))
    # k = D2 x. Y
    cc1 = q.c(C) if False else D(w, Ak, 'rpcnd', [La(cp, '%s e. RR+' % C)], '%s e. CC' % C); cn0 = D(w, Ak, 'rpne0d', [La(cp, '%s e. RR+' % C)], '%s =/= 0' % C)
    kd = q.chain('( %s x. %s )' % (D2, Y), [(D(w, Ak, 'mul12d', [D(w, Ak, 'divcld', [cst(w, Ak, '2cn', '2 e. CC'), cc1, cn0], '%s e. CC' % D2), kc, D(w, Ak, 'halfcld', [cc1], '( %s / 2 ) e. CC' % C)],
                                               '( %s x. %s ) = ( n x. ( %s x. ( %s / 2 ) ) )' % (D2, Y, D2, C)), '( n x. ( %s x. ( %s / 2 ) ) )' % (D2, C)),
                                             (D(w, Ak, 'oveq2d', [D(w, Ak, 'divcan6d', [cst(w, Ak, '2cn', '2 e. CC'), cst(w, Ak, '2ne0', '2 =/= 0'), cc1, cn0], '( %s x. ( %s / 2 ) ) = 1' % (D2, C))], '( n x. ( %s x. ( %s / 2 ) ) ) = ( n x. 1 )' % (D2, C)), '( n x. 1 )'),
                                             (D(w, Ak, 'mulridd', [kc], '( n x. 1 ) = n'), 'n')])
    f3 = D(w, Ak, 'oveq1d', [kd], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( n x. ( %s x. %s ) )' % (D2, Y, eny, eny, eny, eny))
    kee = lin.linarith(w, Ak, [f2] + both(w, Ak, f3, '( ( %s x. %s ) x. ( %s x. %s ) )' % (D2, Y, eny, eny), '( n x. ( %s x. %s ) )' % (eny, eny)), '( n x. ( %s x. %s ) ) <_ ( %s x. %s )' % (eny, eny, D2, eny),
                       leaves={Y: yr, eny: e1r, D2: d2r1, 'n': kr}, atoms=[Y, eny, D2], products=True)
    # exp ( -u ( _pi x. ( ( k ^ 2 ) / T ) ) ) <_ eny x. eny
    K2 = '( n ^ 2 )'
    PK = '( _pi x. ( %s / T ) )' % K2
    pk = q.chain(PK, [(q.sym(q.d('divassd', [q.c('_pi'), q.c(K2), q.c('T'), D(w, Ak, 'rpne0d', [La(tp, 'T e. RR+')], 'T =/= 0')], '( ( _pi x. %s ) / T ) = %s' % (K2, PK)), '( ( _pi x. %s ) / T )' % K2, PK), '( ( _pi x. %s ) / T )' % K2),
                      (q.d('div23d', [q.c('_pi'), q.c(K2), q.c('T'), D(w, Ak, 'rpne0d', [La(tp, 'T e. RR+')], 'T =/= 0')], '( ( _pi x. %s ) / T ) = ( %s x. %s )' % (K2, C, K2)), '( %s x. %s )' % (C, K2))])
    kk = D(w, Ak, 'lemul2ad', [cst(w, Ak, '1re', '1 e. RR'), kr, kr, D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), kr, D(w, Ak, 'nngt0d', [kn], '0 < n')], '0 <_ n'), k1], '( n x. 1 ) <_ ( n x. n )')
    ck = D(w, Ak, 'lemul2ad', [D(w, Ak, 'remulcld', [kr, cst(w, Ak, '1re', '1 e. RR')], '( n x. 1 ) e. RR'), D(w, Ak, 'remulcld', [kr, kr], '( n x. n ) e. RR'), cr1, c01, kk], '( %s x. ( n x. 1 ) ) <_ ( %s x. ( n x. n ) )' % (C, C))
    ksq = both(w, Ak, D(w, Ak, 'oveq2d', [D(w, Ak, 'sqvald', [kc], '%s = ( n x. n )' % K2)], '( %s x. %s ) = ( %s x. ( n x. n ) )' % (C, K2, C)), '( %s x. %s )' % (C, K2), '( %s x. ( n x. n ) )' % C)
    pkb = both(w, Ak, pk, PK, '( %s x. %s )' % (C, K2))
    ex_ = lin.linarith(w, Ak, [ck] + ksq + pkb, '-u %s <_ ( -u %s + -u %s )' % (PK, Y, Y), leaves={'n': kr, C: cr1, PK: q.cl.mem(PK, 'RR'), '( %s x. %s )' % (C, K2): D(w, Ak, 'remulcld', [cr1, D(w, Ak, 'resqcld', [kr], '%s e. RR' % K2)], '( %s x. %s ) e. RR' % (C, K2))},
                       atoms=[C, PK, '( %s x. %s )' % (C, K2)], products=True)
    EPK = '( exp ` -u %s )' % PK
    epk = D(w, Ak, 'breqtrd', [D(w, Ak, 'mpbid', [ex_, D(w, Ak, 'syl2anc', [q.cl.mem('-u %s' % PK, 'RR'), D(w, Ak, 'readdcld', [D(w, Ak, 'renegcld', [yr], '-u %s e. RR' % Y), D(w, Ak, 'renegcld', [yr], '-u %s e. RR' % Y)], '( -u %s + -u %s ) e. RR' % (Y, Y)), w.inst('efle')],
                                                                                '( -u %s <_ ( -u %s + -u %s ) <-> %s <_ ( exp ` ( -u %s + -u %s ) ) )' % (PK, Y, Y, EPK, Y, Y))], '%s <_ ( exp ` ( -u %s + -u %s ) )' % (EPK, Y, Y)),
                               D(w, Ak, 'syl2anc', [q.c('-u %s' % Y), q.c('-u %s' % Y), w.inst('efadd')], '( exp ` ( -u %s + -u %s ) ) = ( %s x. %s )' % (Y, Y, eny, eny))], '%s <_ ( %s x. %s )' % (EPK, eny, eny))
    # k ^ P <_ k
    A0 = '( %s /\\ P = 0 )' % Ak; A1 = '( %s /\\ P = 1 )' % Ak
    kp0 = D(w, A0, 'breqtrrd', [w.s([k1], 'adantr', '( %s -> 1 <_ n )' % A0), D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [w.s([], 'simpr', '( %s -> P = 0 )' % A0)], '( n ^ P ) = ( n ^ 0 )'), D(w, A0, 'exp0d', [w.s([kc], 'adantr', '( %s -> n e. CC )' % A0)], '( n ^ 0 ) = 1')], '( n ^ P ) = 1')],
            '1 <_ n') if False else D(w, A0, 'eqbrtrd', [D(w, A0, 'eqtrd', [D(w, A0, 'oveq2d', [w.s([], 'simpr', '( %s -> P = 0 )' % A0)], '( n ^ P ) = ( n ^ 0 )'), D(w, A0, 'exp0d', [w.s([kc], 'adantr', '( %s -> n e. CC )' % A0)], '( n ^ 0 ) = 1')], '( n ^ P ) = 1'),
                                                           w.s([k1], 'adantr', '( %s -> 1 <_ n )' % A0)], '( n ^ P ) <_ n')
    kp1 = D(w, A1, 'eqbrtrd', [D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [w.s([], 'simpr', '( %s -> P = 1 )' % A1)], '( n ^ P ) = ( n ^ 1 )'), D(w, A1, 'exp1d', [w.s([kc], 'adantr', '( %s -> n e. CC )' % A1)], '( n ^ 1 ) = n')], '( n ^ P ) = n'),
                               D(w, A1, 'leidd', [w.s([kr], 'adantr', '( %s -> n e. RR )' % A1)], 'n <_ n')], '( n ^ P ) <_ n')
    kpk = w.s([kp0, kp1, w.s([La(pp, 'P e. { 0 , 1 }'), w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % Ak)], 'mpjaodan', '( %s -> ( n ^ P ) <_ n )' % Ak)
    kpr = D(w, Ak, 'reexpcld', [kr, La(pn, 'P e. NN0')], '( n ^ P ) e. RR')
    kp0_ = D(w, Ak, 'expge0d', [kr, La(pn, 'P e. NN0'), D(w, Ak, 'ltled', [cst(w, Ak, '0re', '0 e. RR'), kr, D(w, Ak, 'nngt0d', [kn], '0 < n')], '0 <_ n')], '0 <_ ( n ^ P )')
    epkr = q.cl.mem(EPK, 'RR')
    vk1 = D(w, Ak, 'lemul12ad', [kpr, kr, epkr, D(w, Ak, 'remulcld', [e1r, e1r], '( %s x. %s ) e. RR' % (eny, eny)), kp0_, D(w, Ak, 'rpge0d', [q.cl.mem(EPK, 'RR+')], '0 <_ %s' % EPK), kpk, epk],
            '%s <_ ( n x. ( %s x. %s ) )' % (VK, eny, eny))
    vk = D(w, Ak, 'letrd', [D(w, Ak, 'remulcld', [kpr, epkr], '%s e. RR' % VK), D(w, Ak, 'remulcld', [kr, D(w, Ak, 'remulcld', [e1r, e1r], '( %s x. %s ) e. RR' % (eny, eny))], '( n x. ( %s x. %s ) ) e. RR' % (eny, eny)), d2e, vk1, kee],
           '%s <_ ( %s x. %s )' % (VK, D2, eny))
    # | F ` k | <_ B x. ( R ^ k )
    t1 = D(w, Ak, 'eqbrtrd', [D(w, Ak, 'fveq2d', [fv], '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (FM, FK)), D(w, Ak, 'abstrid', [g1, g2], '( abs ` %s ) <_ ( ( abs ` ( %s ` n ) ) + ( abs ` ( %s ` -u n ) ) )' % (FK, GAR, GAR))],
            '( abs ` ( %s ` n ) ) <_ ( ( abs ` ( %s ` n ) ) + ( abs ` ( %s ` -u n ) ) )' % (FM, GAR, GAR))
    AG1, AG2 = '( abs ` ( %s ` n ) )' % GAR, '( abs ` ( %s ` -u n ) )' % GAR
    fin = lin.linarith(w, Ak, [t1, vk] + both(w, Ak, ag1, AG1, VK) + both(w, Ak, ag2, AG2, VK) + both(w, Ak, D(w, Ak, 'oveq2d', [e1y], '( %s x. %s ) = ( %s x. %s )' % (D2, E1, D2, eny)), '( %s x. %s )' % (D2, E1), '( %s x. %s )' % (D2, eny)), '( abs ` ( %s ` n ) ) <_ ( %s x. %s )' % (FM, B, E1),
                       leaves={'( abs ` ( %s ` n ) )' % FM: D(w, Ak, 'abscld', [fkc], '( abs ` ( %s ` n ) ) e. RR' % FM), AG1: D(w, Ak, 'abscld', [g1], '%s e. RR' % AG1), AG2: D(w, Ak, 'abscld', [g2], '%s e. RR' % AG2),
                               VK: D(w, Ak, 'remulcld', [kpr, epkr], '%s e. RR' % VK), D2: d2r1, eny: e1r, E1: D(w, Ak, 'reexpcld', [La(rr, '%s e. RR' % R), D(w, Ak, 'nnnn0d', [kn], 'n e. NN0')], '%s e. RR' % E1)},
                       atoms=['( abs ` ( %s ` n ) )' % FM, AG1, AG2, VK, D2, eny, E1], products=True)
    ms = w.s([br, rr, r0, r1, fkc, fin], 'zl3mser', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ n e. NN ( %s ` n ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) ) ) )' % (ph, FM, FM, B, R, R))
    w.qed([ms], 'simpld', S['zl3grc'])
    go(w, only)


# ---------------------------------------------------------------- zl3thg0
if __name__ == '__main__' and (not only or 'zl3thg0' in only):
    w = W('zl3thg0', 'The Gaussian transformation with the constant ` -i C0 ` still undetermined.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3thg0'])
    tp = w.s([], 'simp1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simp2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simp3', '( %s -> P e. { 0 , 1 } )' % ph)
    pn = p_nn0(w, ph, pp)
    tpar = w.s([tp, ar, pp], '3jca', '( %s -> %s )' % (ph, TPAR))
    q = Q(w, ph, {'T': tp, 'A': ar, 'P': pn, '_i': cst(w, ph, 'ax-icn', '_i e. CC'), '_pi': cst(w, ph, 'pirp', '_pi e. RR+')})
    hol = D(w, ph, 'syl', [w.s([w.s([q.c('T'), pn], 'jca', '( %s -> ( T e. CC /\\ P e. NN0 ) )' % ph), w.s([q.c('A'), q.c('A')], 'jca', '( %s -> ( A e. CC /\\ A e. CC ) )' % ph)], 'jca',
                               '( %s -> ( ( T e. CC /\\ P e. NN0 ) /\\ ( A e. CC /\\ A e. CC ) ) )' % ph), w.inst('zl3hol')], HOLt(FF))
    fb = D(w, ph, 'syl', [tpar, w.inst('zl3fb')], '( %s e. RR+ /\\ A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) ) )' % (KF, FF, KF))
    pois = D(w, ph, 'syl', [w.s([hol, fb], 'jca', '( %s -> ( %s /\\ ( %s e. RR+ /\\ A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) ) ) ) )' % (ph, HOLt(FF), KF, FF, KF)),
                          w.inst('zl3pois')], '%s = %s' % (PZ(FF), PZ(FTF)))
    # PZ ( GAL ) = PZ ( FF )
    GLB = lambda v: '( ( ( %s + A ) ^ P ) x. ( exp ` -u ( ( _pi x. T ) x. ( ( %s + A ) ^ 2 ) ) ) )' % (v, v)
    assert GAL == '( x e. ZZ |-> %s )' % GLB('x')
    def gal_ff(A_, Z, zz, zc):
        E = 'x = %s' % Z
        ie = w.s([], 'id', '( %s -> %s )' % (E, E))
        st, nt = congr.congruence(GLB('x'), {'x': Z}, E, {'x': ie}, g); w.lines.extend(g.lines); g.lines = []
        v1 = w.s([zz, w.s([st, w.s([], 'eqid', '%s = %s' % (GAL, GAL)), w.s([], 'ovex', '%s e. _V' % GLB(Z))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (Z, GAL, Z, GLB(Z)))], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, GAL, Z, GLB(Z)))
        v2, val = fvm(w, A_, 'y', GLB('y'), Z, zc, g)
        return D(w, A_, 'eqtr4d', [v1, v2], '( %s ` %s ) = ( %s ` %s )' % (GAL, Z, FF, Z))
    e0 = gal_ff(ph, '0', cst(w, ph, '0z', '0 e. ZZ'), cst(w, ph, '0cn', '0 e. CC'))
    An = '( %s /\\ n e. NN )' % ph
    nz = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'nnzd', '( %s -> n e. ZZ )' % An)
    en = gal_ff(An, 'n', nz, D(w, An, 'zcnd', [nz], 'n e. CC'))
    nnz = D(w, An, 'znegcld', [nz], '-u n e. ZZ')
    em = gal_ff(An, '-u n', nnz, D(w, An, 'zcnd', [nnz], '-u n e. CC'))
    se = w.s([D(w, An, 'oveq12d', [en, em], '( ( %s ` n ) + ( %s ` -u n ) ) = ( ( %s ` n ) + ( %s ` -u n ) )' % (GAL, GAL, FF, FF))], 'sumeq2dv',
             '( %s -> sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) )' % (ph, GAL, GAL, FF, FF))
    pzl = D(w, ph, 'oveq12d', [e0, se], '%s = %s' % (PZ(GAL), PZ(FF)))
    # PZ ( FTF ) = CT x. PZ ( GAR )
    CT = '( %s x. ( -u _i x. %s ) )' % (CTP, C0)
    ftw = D(w, ph, 'syl3anc', [tp, pp, cst(w, ph, '0re', '0 e. RR'), w.inst('zl3ftw')], '( ( t e. RR+ |-> %s ) ~~>r ( ( 0 ^ P ) x. ( %s / ( sqrt ` T ) ) ) /\\ %s e. CC )' % (LT(GF('-u T', '0', '0', 'P', 'w'), '0', 't'), C0, C0))
    c0c = w.s([ftw], 'simprd', '( %s -> %s e. CC )' % (ph, C0))
    ctc = D(w, ph, 'mulcld', [q.c(CTP), D(w, ph, 'mulcld', [q.c('-u _i'), c0c], '( -u _i x. %s ) e. CC' % C0)], '%s e. CC' % CT)
    Am = '( %s /\\ m e. ZZ )' % ph
    mz = w.s([], 'simpr', '( %s -> m e. ZZ )' % Am)
    qm = Q(w, Am, {'T': w.s([tp], 'adantr', '( %s -> T e. RR+ )' % Am), 'A': w.s([ar], 'adantr', '( %s -> A e. RR )' % Am), 'P': w.s([pn], 'adantr', '( %s -> P e. NN0 )' % Am), 'm': mz,
                   '_i': cst(w, Am, 'ax-icn', '_i e. CC'), '_pi': cst(w, Am, 'pirp', '_pi e. RR+')})
    grm = D(w, Am, 'eqeltrd', [gr_val(w, Am, 'm', mz), qm.c(GRB('m'))], '( %s ` m ) e. CC' % GAR)
    ftm = D(w, Am, 'syl', [w.s([w.s([tpar], 'adantr', '( %s -> %s )' % (Am, TPAR)), mz], 'jca', '( %s -> ( %s /\\ m e. ZZ ) )' % (Am, TPAR)), w.inst('zl3ft')], '( %s ` m ) = ( %s x. ( %s ` m ) )' % (FTF, CT, GAR))
    al = w.s([w.s([grm, ftm], 'jca', '( %s -> ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) ) )' % (Am, GAR, FTF, CT, GAR))], 'ralrimiva',
             '( %s -> A. m e. ZZ ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) ) )' % (ph, GAR, FTF, CT, GAR))
    grc = D(w, ph, 'syl', [tpar, w.inst('zl3grc')], 'seq 1 ( + , ( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) ) ) e. dom ~~>' % (GAR, GAR))
    pzm = D(w, ph, 'syl', [w.s([w.s([ctc, cst(w, ph, 'mptex', '%s e. _V' % FTF), cst(w, ph, 'mptex', '%s e. _V' % GAR)], '3jca', '( %s -> ( %s e. CC /\\ %s e. _V /\\ %s e. _V ) )' % (ph, CT, FTF, GAR)),
                                w.s([al, grc], 'jca', '( %s -> ( A. m e. ZZ ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) ) /\\ seq 1 ( + , ( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) ) ) e. dom ~~> ) )'
                                    % (ph, GAR, FTF, CT, GAR, GAR, GAR))], 'jca',
                               '( %s -> ( ( %s e. CC /\\ %s e. _V /\\ %s e. _V ) /\\ ( A. m e. ZZ ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) ) /\\ seq 1 ( + , ( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) ) ) e. dom ~~> ) ) )'
                               % (ph, CT, FTF, GAR, GAR, FTF, CT, GAR, GAR, GAR)), w.inst('zl3pzm')], '%s = ( %s x. %s )' % (PZ(FTF), CT, PZ(GAR)))
    w.qed([D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [pzl, pois], '%s = %s' % (PZ(GAL), PZ(FTF))), pzm], '%s = ( %s x. %s )' % (PZ(GAL), CT, PZ(GAR)))], 'idi', S['zl3thg0'])
    go(w, only)


def sub3(text):
    """T := 1 , A := 0 , P := 0 (token-wise)"""
    m = {'T': '1', 'A': '0', 'P': '0'}
    return ' '.join(m.get(t, t) for t in text.split())


# ---------------------------------------------------------------- zl3c1
if __name__ == '__main__' and (not only or 'zl3c1' in only):
    w = W('zl3c1', 'The constant: ` -i C0 = 1 `, from the transformation at ` T = 1 ` where both sides coincide.')
    g = congr.StepGen('m')
    ph = '( 1 e. RR+ /\\ 0 e. RR /\\ 0 e. { 0 , 1 } )'
    assert sub3(TPAR) == ph
    GL1, GR1 = sub3(GAL), sub3(GAR)
    C1 = sub3(CTP)
    t0 = D(w, ph, 'syl', [w.s([], 'id', '( %s -> %s )' % (ph, ph)), w.inst('zl3thg0')], '%s = ( ( %s x. ( -u _i x. %s ) ) x. %s )' % (sub3(PZ(GAL)), C1, C0, sub3(PZ(GAR))))
    En = lambda v: '( exp ` -u ( _pi x. ( %s ^ 2 ) ) )' % v
    GLv = lambda v: '( ( ( %s + 0 ) ^ 0 ) x. ( exp ` -u ( ( _pi x. 1 ) x. ( ( %s + 0 ) ^ 2 ) ) ) )' % (v, v)
    GRv = lambda v: '( ( %s ^ 0 ) x. ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / 1 ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. 0 ) ) ) ) )' % (v, v, v)
    assert GL1 == '( x e. ZZ |-> %s )' % GLv('x') and GR1 == '( k e. ZZ |-> %s )' % GRv('k'), (GL1, GR1)
    def vals(A_, Z, zz):
        zc = D(w, A_, 'zcnd', [zz], '%s e. CC' % Z)
        qz = Q(w, A_, {Z: zz, '_i': cst(w, A_, 'ax-icn', '_i e. CC'), '_pi': cst(w, A_, 'pirp', '_pi e. RR+')}) if len(Z.split()) == 1 else None
        E = 'x = %s' % Z
        ie = w.s([], 'id', '( %s -> %s )' % (E, E))
        st, nt = congr.congruence(GLv('x'), {'x': Z}, E, {'x': ie}, g); w.lines.extend(g.lines); g.lines = []
        v1 = w.s([zz, w.s([st, w.s([], 'eqid', '%s = %s' % (GL1, GL1)), w.s([], 'ovex', '%s e. _V' % GLv(Z))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (Z, GL1, Z, GLv(Z)))], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, GL1, Z, GLv(Z)))
        E2 = 'k = %s' % Z
        ie2 = w.s([], 'id', '( %s -> %s )' % (E2, E2))
        st2, nt2 = congr.congruence(GRv('k'), {'k': Z}, E2, {'k': ie2}, g); w.lines.extend(g.lines); g.lines = []
        v2 = w.s([zz, w.s([st2, w.s([], 'eqid', '%s = %s' % (GR1, GR1)), w.s([], 'ovex', '%s e. _V' % GRv(Z))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (Z, GR1, Z, GRv(Z)))], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, GR1, Z, GRv(Z)))
        z0 = D(w, A_, 'addridd', [zc], '( %s + 0 ) = %s' % (Z, Z))
        pic = cst(w, A_, 'picn', '_pi e. CC'); z2 = D(w, A_, 'sqcld', [zc], '( %s ^ 2 ) e. CC' % Z)
        enc = D(w, A_, 'efcld', [D(w, A_, 'negcld', [D(w, A_, 'mulcld', [pic, z2], '( _pi x. ( %s ^ 2 ) ) e. CC' % Z)], '-u ( _pi x. ( %s ^ 2 ) ) e. CC' % Z)], '%s e. CC' % En(Z))
        gl = D(w, A_, 'eqtrd', [D(w, A_, 'oveq12d', [D(w, A_, 'exp0d', [D(w, A_, 'addcld', [zc, cst(w, A_, '0cn', '0 e. CC')], '( %s + 0 ) e. CC' % Z)], '( ( %s + 0 ) ^ 0 ) = 1' % Z),
                                                     D(w, A_, 'fveq2d', [D(w, A_, 'negeqd', [D(w, A_, 'oveq12d', [D(w, A_, 'mulridd', [pic], '( _pi x. 1 ) = _pi'), D(w, A_, 'oveq1d', [z0], '( ( %s + 0 ) ^ 2 ) = ( %s ^ 2 )' % (Z, Z))],
                                                                                                 '( ( _pi x. 1 ) x. ( ( %s + 0 ) ^ 2 ) ) = ( _pi x. ( %s ^ 2 ) )' % (Z, Z))], '-u ( ( _pi x. 1 ) x. ( ( %s + 0 ) ^ 2 ) ) = -u ( _pi x. ( %s ^ 2 ) )' % (Z, Z))],
                                                       '( exp ` -u ( ( _pi x. 1 ) x. ( ( %s + 0 ) ^ 2 ) ) ) = %s' % (Z, En(Z)))], '%s = ( 1 x. %s )' % (GLv(Z), En(Z))), D(w, A_, 'mullidd', [enc], '( 1 x. %s ) = %s' % (En(Z), En(Z)))],
                '%s = %s' % (GLv(Z), En(Z)))
        TIP = '( 2 x. ( _i x. _pi ) )'
        ez = D(w, A_, 'eqtrd', [D(w, A_, 'fveq2d', [D(w, A_, 'eqtrd', [D(w, A_, 'oveq2d', [D(w, A_, 'mul01d', [zc], '( %s x. 0 ) = 0' % Z)], '( %s x. ( %s x. 0 ) ) = ( %s x. 0 )' % (TIP, Z, TIP)),
                                                                        D(w, A_, 'mul01d', [D(w, A_, 'mulcld', [cst(w, A_, '2cn', '2 e. CC'), D(w, A_, 'mulcld', [cst(w, A_, 'ax-icn', '_i e. CC'), pic], '( _i x. _pi ) e. CC')], '%s e. CC' % TIP)], '( %s x. 0 ) = 0' % TIP)],
                                                          '( %s x. ( %s x. 0 ) ) = 0' % (TIP, Z))], '( exp ` ( %s x. ( %s x. 0 ) ) ) = ( exp ` 0 )' % (TIP, Z)), cst(w, A_, 'ef0', '( exp ` 0 ) = 1')],
                '( exp ` ( %s x. ( %s x. 0 ) ) ) = 1' % (TIP, Z))
        e1 = D(w, A_, 'fveq2d', [D(w, A_, 'negeqd', [D(w, A_, 'oveq2d', [D(w, A_, 'div1d', [z2], '( ( %s ^ 2 ) / 1 ) = ( %s ^ 2 )' % (Z, Z))], '( _pi x. ( ( %s ^ 2 ) / 1 ) ) = ( _pi x. ( %s ^ 2 ) )' % (Z, Z))],
                                                 '-u ( _pi x. ( ( %s ^ 2 ) / 1 ) ) = -u ( _pi x. ( %s ^ 2 ) )' % (Z, Z))], '( exp ` -u ( _pi x. ( ( %s ^ 2 ) / 1 ) ) ) = %s' % (Z, En(Z)))
        inner = D(w, A_, 'eqtrd', [D(w, A_, 'oveq12d', [e1, ez], '( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / 1 ) ) ) x. ( exp ` ( %s x. ( %s x. 0 ) ) ) ) = ( %s x. 1 )' % (Z, TIP, Z, En(Z))), D(w, A_, 'mulridd', [enc], '( %s x. 1 ) = %s' % (En(Z), En(Z)))],
                   '( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / 1 ) ) ) x. ( exp ` ( %s x. ( %s x. 0 ) ) ) ) = %s' % (Z, TIP, Z, En(Z)))
        gr = D(w, A_, 'eqtrd', [D(w, A_, 'oveq12d', [D(w, A_, 'exp0d', [zc], '( %s ^ 0 ) = 1' % Z), inner], '%s = ( 1 x. %s )' % (GRv(Z), En(Z))), D(w, A_, 'mullidd', [enc], '( 1 x. %s ) = %s' % (En(Z), En(Z)))],
                '%s = %s' % (GRv(Z), En(Z)))
        a = D(w, A_, 'eqtrd', [v1, gl], '( %s ` %s ) = %s' % (GL1, Z, En(Z))); b = D(w, A_, 'eqtrd', [v2, gr], '( %s ` %s ) = %s' % (GR1, Z, En(Z)))
        enr = D(w, A_, 'reefcld', [D(w, A_, 'renegcld', [D(w, A_, 'remulcld', [cst(w, A_, 'pire', '_pi e. RR'), D(w, A_, 'resqcld', [D(w, A_, 'zred', [zz], '%s e. RR' % Z)], '( %s ^ 2 ) e. RR' % Z)], '( _pi x. ( %s ^ 2 ) ) e. RR' % Z)],
                                                   '-u ( _pi x. ( %s ^ 2 ) ) e. RR' % Z)], '%s e. RR' % En(Z))
        en0 = D(w, A_, 'rpge0d', [D(w, A_, 'rpefcld', [D(w, A_, 'renegcld', [D(w, A_, 'remulcld', [cst(w, A_, 'pire', '_pi e. RR'), D(w, A_, 'resqcld', [D(w, A_, 'zred', [zz], '%s e. RR' % Z)], '( %s ^ 2 ) e. RR' % Z)], '( _pi x. ( %s ^ 2 ) ) e. RR' % Z)],
                                                                   '-u ( _pi x. ( %s ^ 2 ) ) e. RR' % Z)], '%s e. RR+' % En(Z))], '0 <_ %s' % En(Z))
        return a, b, enr, en0
    a0, b0, _, _ = vals(ph, '0', cst(w, ph, '0z', '0 e. ZZ'))
    An = '( %s /\\ n e. NN )' % ph
    nz = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'nnzd', '( %s -> n e. ZZ )' % An)
    nnz = D(w, An, 'znegcld', [nz], '-u n e. ZZ')
    an, bn, rn, pn_ = vals(An, 'n', nz)
    am, bm, rm, pm = vals(An, '-u n', nnz)
    TN = '( ( %s ` n ) + ( %s ` -u n ) )' % (GR1, GR1)
    se = w.s([D(w, An, 'eqtr4d', [D(w, An, 'oveq12d', [an, am], '( ( %s ` n ) + ( %s ` -u n ) ) = ( %s + %s )' % (GL1, GL1, En('n'), En('-u n'))), D(w, An, 'oveq12d', [bn, bm], '%s = ( %s + %s )' % (TN, En('n'), En('-u n')))],
                  '( ( %s ` n ) + ( %s ` -u n ) ) = %s' % (GL1, GL1, TN))], 'sumeq2dv', '( %s -> sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = sum_ n e. NN %s )' % (ph, GL1, GL1, TN))
    pz = D(w, ph, 'oveq12d', [D(w, ph, 'eqtr4d', [a0, b0], '( %s ` 0 ) = ( %s ` 0 )' % (GL1, GR1)), se], '%s = %s' % (sub3(PZ(GAL)), sub3(PZ(GAR))))
    X = sub3(PZ(GAR))
    # X >_ 1
    FM = '( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) )' % (GR1, GR1)
    grc = D(w, ph, 'syl', [w.s([], 'id', '( %s -> %s )' % (ph, ph)), w.inst('zl3grc')], 'seq 1 ( + , %s ) e. dom ~~>' % FM)
    Em = 'm = n'
    ie = w.s([], 'id', '( %s -> %s )' % (Em, Em))
    stm = D(w, Em, 'oveq12d', [D(w, Em, 'fveq2d', [ie], '( %s ` m ) = ( %s ` n )' % (GR1, GR1)), D(w, Em, 'fveq2d', [D(w, Em, 'negeqd', [ie], '-u m = -u n')], '( %s ` -u m ) = ( %s ` -u n )' % (GR1, GR1))],
            '( ( %s ` m ) + ( %s ` -u m ) ) = %s' % (GR1, GR1, TN))
    fv = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An), w.s([stm, w.s([], 'eqid', '%s = %s' % (FM, FM)), w.s([], 'ovex', '%s e. _V' % TN)], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (FM, TN))], 'syl', '( %s -> ( %s ` n ) = %s )' % (An, FM, TN))
    tnv = D(w, An, 'oveq12d', [bn, bm], '%s = ( %s + %s )' % (TN, En('n'), En('-u n')))
    tnr = D(w, An, 'eqeltrrd', [D(w, An, 'eqcomd', [tnv], '( %s + %s ) = %s' % (En('n'), En('-u n'), TN)), D(w, An, 'readdcld', [rn, rm], '( %s + %s ) e. RR' % (En('n'), En('-u n')))], '%s e. RR' % TN) if False else \
        D(w, An, 'eqeltrd', [tnv, D(w, An, 'readdcld', [rn, rm], '( %s + %s ) e. RR' % (En('n'), En('-u n')))], '%s e. RR' % TN)
    tn0 = D(w, An, 'breqtrrd', [D(w, An, 'addge0d', [rn, rm, pn_, pm], '0 <_ ( %s + %s )' % (En('n'), En('-u n'))), tnv], '0 <_ %s' % TN)
    SUM = 'sum_ n e. NN %s' % TN
    sr = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), fv, tnr, grc], 'isumrecl', '( %s -> %s e. RR )' % (ph, SUM))
    s0 = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), fv, tnr, grc, tn0], 'isumge0', '( %s -> 0 <_ %s )' % (ph, SUM))
    g0 = D(w, ph, 'eqtrd', [b0, D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [D(w, ph, 'eqtrd', [D(w, ph, 'negeqd', [D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [cst(w, ph, 'sq0', '( 0 ^ 2 ) = 0')], '( _pi x. ( 0 ^ 2 ) ) = ( _pi x. 0 )'),
                                                                                                                           D(w, ph, 'mul01d', [cst(w, ph, 'picn', '_pi e. CC')], '( _pi x. 0 ) = 0')], '( _pi x. ( 0 ^ 2 ) ) = 0')], '-u ( _pi x. ( 0 ^ 2 ) ) = -u 0'),
                                                                                     cst(w, ph, 'neg0', '-u 0 = 0')], '-u ( _pi x. ( 0 ^ 2 ) ) = 0')], '%s = ( exp ` 0 )' % En('0')), cst(w, ph, 'ef0', '( exp ` 0 ) = 1')], '%s = 1' % En('0'))],
           '( %s ` 0 ) = 1' % GR1)
    xe = D(w, ph, 'oveq1d', [g0], '%s = ( 1 + %s )' % (X, SUM))
    xr = D(w, ph, 'eqeltrd', [xe, D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), sr], '( 1 + %s ) e. RR' % SUM)], '%s e. RR' % X)
    x1 = D(w, ph, 'breqtrrd', [lin.linarith(w, ph, [s0], '0 < ( 1 + %s )' % SUM, leaves={SUM: sr}), xe], '0 < %s' % X)
    xn0 = D(w, ph, 'gt0ne0d', [x1], '%s =/= 0' % X)
    # ( -u _i x. C0 ) x. X = 1 x. X
    ftw = D(w, ph, 'syl3anc', [w.s([], 'simp1', '( %s -> 1 e. RR+ )' % ph), w.s([], 'simp3', '( %s -> 0 e. { 0 , 1 } )' % ph), cst(w, ph, '0re', '0 e. RR'), w.inst('zl3ftw')],
            '( ( t e. RR+ |-> %s ) ~~>r ( ( 0 ^ 0 ) x. ( %s / ( sqrt ` 1 ) ) ) /\\ %s e. CC )' % (LT(GF('-u 1', '0', '0', '0', 'w'), '0', 't'), C0, C0))
    c0c = w.s([ftw], 'simprd', '( %s -> %s e. CC )' % (ph, C0))
    NC = '( -u _i x. %s )' % C0
    ncc = D(w, ph, 'mulcld', [D(w, ph, 'negcld', [cst(w, ph, 'ax-icn', '_i e. CC')], '-u _i e. CC'), c0c], '%s e. CC' % NC)
    c1v = D(w, ph, 'eqtrd', [D(w, ph, 'oveq12d', [D(w, ph, 'exp0d', [D(w, ph, 'negcld', [cst(w, ph, 'ax-icn', '_i e. CC')], '-u _i e. CC')], '( -u _i ^ 0 ) = 1'),
                                                  D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [D(w, ph, 'eqtrd', [D(w, ph, 'negeqd', [D(w, ph, 'addridd', [cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC')], '( ( 1 / 2 ) + 0 ) = ( 1 / 2 )')], '-u ( ( 1 / 2 ) + 0 ) = -u ( 1 / 2 )'),
                                                                                                            D(w, ph, 'eqidd', [], '-u ( 1 / 2 ) = -u ( 1 / 2 )')], '-u ( ( 1 / 2 ) + 0 ) = -u ( 1 / 2 )')], '( 1 ^c -u ( ( 1 / 2 ) + 0 ) ) = ( 1 ^c -u ( 1 / 2 ) )'),
                                                                     w.s([D(w, ph, 'negcld', [cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC')], '-u ( 1 / 2 ) e. CC'), w.inst('1cxp')], 'syl', '( %s -> ( 1 ^c -u ( 1 / 2 ) ) = 1 )' % ph)],
                                                    '( 1 ^c -u ( ( 1 / 2 ) + 0 ) ) = 1')], '%s = ( 1 x. 1 )' % C1), D(w, ph, 'mulridd', [cst(w, ph, 'ax-1cn', '1 e. CC')], '( 1 x. 1 ) = 1')], '%s = 1' % C1)
    cc1 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq1d', [c1v], '( %s x. %s ) = ( 1 x. %s )' % (C1, NC, NC)), D(w, ph, 'mullidd', [ncc], '( 1 x. %s ) = %s' % (NC, NC))], '( %s x. %s ) = %s' % (C1, NC, NC))
    xx = D(w, ph, 'eqtr3d', [D(w, ph, 'eqtr3d', [pz, t0], '%s = ( ( %s x. %s ) x. %s )' % (X, C1, NC, X)), D(w, ph, 'eqidd', [], '%s = %s' % (X, X))], 'x') if False else None
    x2 = D(w, ph, 'eqtr3d', [pz, t0], '%s = ( ( %s x. %s ) x. %s )' % (X, C1, NC, X))
    x3 = D(w, ph, 'eqtrd', [x2, D(w, ph, 'oveq1d', [cc1], '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (C1, NC, X, NC, X))], '%s = ( %s x. %s )' % (X, NC, X))
    xc = D(w, ph, 'recnd', [xr], '%s e. CC' % X)
    x4 = D(w, ph, 'eqtr4d', [D(w, ph, 'eqcomd', [x3], '( %s x. %s ) = %s' % (NC, X, X)), D(w, ph, 'mullidd', [xc], '( 1 x. %s ) = %s' % (X, X))], '( %s x. %s ) = ( 1 x. %s )' % (NC, X, X))
    res = D(w, ph, 'mpbid', [x4, D(w, ph, 'mulcan2d', [ncc, cst(w, ph, 'ax-1cn', '1 e. CC'), xc, xn0], '( ( %s x. %s ) = ( 1 x. %s ) <-> %s = 1 )' % (NC, X, X, NC))], '%s = 1' % NC)
    a0_ = w.s([cst(w, 'x', '1rp', '1 e. RR+') if False else w.s([], '1rp', '1 e. RR+'), w.s([], '0re', '0 e. RR'), w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }')], '3pm3.2i', ph)
    w.qed([a0_, res], 'mpcom' if False else 'mpd' if False else 'ax-mp', S['zl3c1']) if False else w.qed([a0_, res], 'mpcom', S['zl3c1']) if False else None
    w.qed([a0_, res], 'mpcom', S['zl3c1']) if False else w.qed([a0_, w.s([res], 'idi', '( %s -> %s )' % (ph, S['zl3c1']))], 'ax-mp', S['zl3c1'])
    go(w, only)


# ---------------------------------------------------------------- zl3thg
if __name__ == '__main__' and (not only or 'zl3thg' in only):
    w = W('zl3thg', 'The theta transformation of the Gaussian with characteristic ` A ` and parity ` P `.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3thg'])
    tp = w.s([], 'simp1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simp2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simp3', '( %s -> P e. { 0 , 1 } )' % ph)
    pn = p_nn0(w, ph, pp)
    q = Q(w, ph, {'T': tp, 'A': ar, 'P': pn, '_i': cst(w, ph, 'ax-icn', '_i e. CC'), '_pi': cst(w, ph, 'pirp', '_pi e. RR+')})
    t0 = D(w, ph, 'syl', [w.s([], 'id', '( %s -> %s )' % (ph, ph)), w.inst('zl3thg0')], '%s = ( ( %s x. ( -u _i x. %s ) ) x. %s )' % (PZ(GAL), CTP, C0, PZ(GAR)))
    c1 = cst(w, ph, 'zl3c1', '( -u _i x. %s ) = 1' % C0)
    # PZ ( GAR ) e. CC
    FM = '( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) )' % (GAR, GAR)
    grc = D(w, ph, 'syl', [w.s([], 'id', '( %s -> %s )' % (ph, ph)), w.inst('zl3grc')], 'seq 1 ( + , %s ) e. dom ~~>' % FM)
    An = '( %s /\\ n e. NN )' % ph
    nz = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'nnzd', '( %s -> n e. ZZ )' % An)
    TN_ = '( ( %s ` n ) + ( %s ` -u n ) )' % (GAR, GAR)
    Em = 'm = n'
    ie = w.s([], 'id', '( %s -> %s )' % (Em, Em))
    stm = D(w, Em, 'oveq12d', [D(w, Em, 'fveq2d', [ie], '( %s ` m ) = ( %s ` n )' % (GAR, GAR)), D(w, Em, 'fveq2d', [D(w, Em, 'negeqd', [ie], '-u m = -u n')], '( %s ` -u m ) = ( %s ` -u n )' % (GAR, GAR))],
            '( ( %s ` m ) + ( %s ` -u m ) ) = %s' % (GAR, GAR, TN_))
    fv = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An), w.s([stm, w.s([], 'eqid', '%s = %s' % (FM, FM)), w.s([], 'ovex', '%s e. _V' % TN_)], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (FM, TN_))], 'syl', '( %s -> ( %s ` n ) = %s )' % (An, FM, TN_))
    qn = Q(w, An, {'T': w.s([tp], 'adantr', '( %s -> T e. RR+ )' % An), 'A': w.s([ar], 'adantr', '( %s -> A e. RR )' % An), 'P': w.s([pn], 'adantr', '( %s -> P e. NN0 )' % An), 'n': nz,
                   '_i': cst(w, An, 'ax-icn', '_i e. CC'), '_pi': cst(w, An, 'pirp', '_pi e. RR+')})
    nnz = D(w, An, 'znegcld', [nz], '-u n e. ZZ')
    g1 = D(w, An, 'eqeltrd', [gr_val(w, An, 'n', nz), qn.c(GRB('n'))], '( %s ` n ) e. CC' % GAR)
    g2 = D(w, An, 'eqeltrd', [gr_val(w, An, '-u n', nnz), qn.c(GRB('-u n'))], '( %s ` -u n ) e. CC' % GAR)
    tnc = D(w, An, 'addcld', [g1, g2], '%s e. CC' % TN_)
    sc = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), fv, tnc, grc], 'isumcl', '( %s -> sum_ n e. NN %s e. CC )' % (ph, TN_))
    g0 = D(w, ph, 'eqeltrd', [gr_val(w, ph, '0', cst(w, ph, '0z', '0 e. ZZ')), q.c(GRB('0'))], '( %s ` 0 ) e. CC' % GAR)
    pzc = D(w, ph, 'addcld', [g0, sc], '%s e. CC' % PZ(GAR))
    NIP = '( -u _i ^ P )'; TN = '( T ^c -u ( ( 1 / 2 ) + P ) )'
    tnc_ = D(w, ph, 'cxpcld', [q.c('T'), D(w, ph, 'negcld', [D(w, ph, 'addcld', [cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC'), D(w, ph, 'nn0cnd', [pn], 'P e. CC')], '( ( 1 / 2 ) + P ) e. CC')], '-u ( ( 1 / 2 ) + P ) e. CC')], '%s e. CC' % TN)
    r1 = D(w, ph, 'oveq1d', [D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [c1], '( %s x. ( -u _i x. %s ) ) = ( %s x. 1 )' % (CTP, C0, CTP)), D(w, ph, 'mulridd', [q.c(CTP)], '( %s x. 1 ) = %s' % (CTP, CTP))],
                                                '( %s x. ( -u _i x. %s ) ) = %s' % (CTP, C0, CTP))], '( ( %s x. ( -u _i x. %s ) ) x. %s ) = ( %s x. %s )' % (CTP, C0, PZ(GAR), CTP, PZ(GAR)))
    r2 = D(w, ph, 'mulassd', [q.c(NIP), tnc_, pzc], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (CTP, PZ(GAR), NIP, TN, PZ(GAR)))
    w.qed([D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [t0, r1], '%s = ( %s x. %s )' % (PZ(GAL), CTP, PZ(GAR))), r2], '%s = ( %s x. ( %s x. %s ) )' % (PZ(GAL), NIP, TN, PZ(GAR)))], 'idi', S['zl3thg'])
    go(w, only)
