"""C7b section 6, second part: the logarithmic derivative of holzfac's factorisation
F = prod_ q e. ZS ( z - q ) ^ ( o ` q ) x. h on ( A crect B ) \\ ZS
(fprodhdv, fprodlogdvh, holzlogdvlem, holzlogdv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
lin.FASTPATH = True

TOPO = '( TopOpen ` CCfld )'
CS = '( CC \\ S )'
X = '( D \\ S )'
H0 = '( S e. Fin /\\ S C_ CC /\\ O : S --> NN )'
HOLH = '( H e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D H ) )'


def PR(T, z='z', q='q', O='O'):
    return 'prod_ %s e. %s ( ( %s - %s ) ^ ( %s ` %s ) )' % (q, T, z, q, O, q)


def SM(T, z='z', q='q', O='O'):
    return 'sum_ %s e. %s ( ( %s ` %s ) / ( %s - %s ) )' % (q, T, O, q, z, q)


def closed(w, ante, ref, f):
    return w.s([w.s([], ref, f)], 'a1i', '( %s -> %s )' % (ante, f))


P = PR('S'); L = SM('S')
RMX = '( z e. %s |-> ( ( ( %s x. %s ) x. ( H ` z ) ) + ( ( ( CC _D H ) ` z ) x. %s ) ) )' % (X, P, L, P)
MX = '( z e. %s |-> ( %s x. ( H ` z ) ) )' % (X, P)
FHDV = '( CC _D %s ) = %s' % (MX, RMX)


def common(w, A0, h0, hol):
    """facts under an antecedent A0 that yields H0 (h0) and HOLH (hol)"""
    r = {}
    r['sfin'] = w.s([h0, w.inst('simp1')], 'syl', '( %s -> S e. Fin )' % A0)
    r['scc'] = w.s([h0, w.inst('simp2')], 'syl', '( %s -> S C_ CC )' % A0)
    r['dop'] = w.s([hol, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOPO))
    r['hcn'] = w.s([hol, w.inst('simpl')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
    r['dcc'] = w.s([r['hcn'], w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    ej = w.s([], 'eqid', '%s = %s' % (TOPO, TOPO))
    un = w.s([], 'unicntop', 'CC = U. %s' % TOPO)
    fre = w.s([w.s([ej], 'cnfldhaus', '%s e. Haus' % TOPO), w.inst('haust1')], 'ax-mp', '%s e. Fre' % TOPO)
    fre = w.s([fre], 'a1i', '( %s -> %s e. Fre )' % (A0, TOPO))
    r['scld'] = w.s([fre, r['scc'], r['sfin'], w.s([un], 't1ficld', '( ( %s e. Fre /\\ S C_ CC /\\ S e. Fin ) -> S e. ( Clsd ` %s ) )' % (TOPO, TOPO))], 'syl3anc',
                    '( %s -> S e. ( Clsd ` %s ) )' % (A0, TOPO))
    r['xop'] = w.s([r['dop'], r['scld'], w.s([un], 'difopn', '( ( D e. %s /\\ S e. ( Clsd ` %s ) ) -> %s e. %s )' % (TOPO, TOPO, X, TOPO))], 'syl2anc',
                   '( %s -> %s e. %s )' % (A0, X, TOPO))
    r['jr'] = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOPO, TOPO))], 'eqcomi', '%s = ( %s |`t CC )' % (TOPO, TOPO))
    r['ej'] = ej
    r['xopr'] = w.s([r['xop'], r['jr']], 'eleqtrdi', '( %s -> %s e. ( %s |`t CC ) )' % (A0, X, TOPO))
    r['xcs'] = w.s([r['dcc']], 'ssdifd', '( %s -> %s C_ %s )' % (A0, X, CS))
    r['xd'] = w.s([], 'difssd', '( %s -> %s C_ D )' % (A0, X))
    r['hf'] = w.s([r['hcn'], w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % A0)
    r['hdf'] = w.s([hol, w.inst('holf')], 'syl', '( %s -> ( CC _D H ) : D --> CC )' % A0)
    return r


if __name__ == '__main__' and (not only or 'fprodhdv' in only):
    w = W('fprodhdv', 'The derivative of ` prod_ q e. S ( z - q ) ^ ( O ` q ) x. ( H ` z ) ` on ` D \\ S ` for ` H ` holomorphic on the open set ` D ` .')
    A0 = '( %s /\\ %s )' % (H0, HOLH)
    h0 = w.s([], 'simpl', '( %s -> %s )' % (A0, H0))
    hol = w.s([], 'simpr', '( %s -> %s )' % (A0, HOLH))
    r = common(w, A0, h0, hol)
    cnpr = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    jeq = w.s([], 'eqid', '( %s |`t CC ) = ( %s |`t CC )' % (TOPO, TOPO))
    PHI = '( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> ( %s x. %s ) )' % (CS, P, CS, P, L)
    ffp = w.s([h0, w.inst('fprodlogdvf')], 'syl', '( %s -> %s )' % (A0, PHI))
    Ac = '( %s /\\ z e. %s )' % (A0, CS)
    lcl = w.s([w.s([w.s([h0], 'adantr', '( %s -> %s )' % (Ac, H0)), w.s([], 'simpr', '( %s -> z e. %s )' % (Ac, CS))], 'jca', '( %s -> ( %s /\\ z e. %s ) )' % (Ac, H0, CS)),
               w.inst('fprodlcl')], 'syl', '( %s -> ( %s e. CC /\\ %s =/= 0 /\\ %s e. CC ) )' % (Ac, P, P, L))
    pc = w.s([lcl], 'simp1d', '( %s -> %s e. CC )' % (Ac, P))
    lc = w.s([lcl], 'simp3d', '( %s -> %s e. CC )' % (Ac, L))
    plc = w.s([pc, lc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Ac, P, L))
    dp = w.s([cnpr, pc, plc, ffp, r['xcs'], jeq, r['ej'], r['xopr']], 'dvmptres',
             '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> ( %s x. %s ) ) )' % (A0, X, P, X, P, L))
    Ad = '( %s /\\ z e. D )' % A0
    zd_ = w.s([], 'simpr', '( %s -> z e. D )' % Ad)
    hz = w.s([w.s([r['hf']], 'adantr', '( %s -> H : D --> CC )' % Ad), zd_], 'ffvelcdmd', '( %s -> ( H ` z ) e. CC )' % Ad)
    hdz = w.s([w.s([r['hdf']], 'adantr', '( %s -> ( CC _D H ) : D --> CC )' % Ad), zd_], 'ffvelcdmd', '( %s -> ( ( CC _D H ) ` z ) e. CC )' % Ad)
    hdv = w.s([hol, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. D |-> ( H ` z ) ) ) = ( z e. D |-> ( ( CC _D H ) ` z ) ) )' % A0)
    dh = w.s([cnpr, hz, hdz, hdv, r['xd'], jeq, r['ej'], r['xopr']], 'dvmptres',
             '( %s -> ( CC _D ( z e. %s |-> ( H ` z ) ) ) = ( z e. %s |-> ( ( CC _D H ) ` z ) ) )' % (A0, X, X))
    Ax = '( %s /\\ z e. %s )' % (A0, X)
    zx = w.s([], 'simpr', '( %s -> z e. %s )' % (Ax, X))
    zcs = w.s([w.s([r['xcs']], 'adantr', '( %s -> %s C_ %s )' % (Ax, X, CS)), zx], 'sseldd', '( %s -> z e. %s )' % (Ax, CS))
    zdx = w.s([w.s([r['xd']], 'adantr', '( %s -> %s C_ D )' % (Ax, X)), zx], 'sseldd', '( %s -> z e. D )' % Ax)
    pcx = w.s([zcs, pc], 'syldan', '( %s -> %s e. CC )' % (Ax, P))
    plcx = w.s([zcs, plc], 'syldan', '( %s -> ( %s x. %s ) e. CC )' % (Ax, P, L))
    hzx = w.s([zdx, hz], 'syldan', '( %s -> ( H ` z ) e. CC )' % Ax)
    hdzx = w.s([zdx, hdz], 'syldan', '( %s -> ( ( CC _D H ) ` z ) e. CC )' % Ax)
    w.qed([cnpr, pcx, plcx, dp, hzx, hdzx, dh], 'dvmptmul', '( %s -> %s )' % (A0, FHDV))
    run7b(w)


G = '( z e. D |-> ( %s x. ( H ` z ) ) )' % P
PZ = PR('S', 'Z'); LZ = SM('S', 'Z')
B0 = '( ( %s /\\ %s ) /\\ ( Z e. %s /\\ ( H ` Z ) =/= 0 ) )' % (H0, HOLH, X)
LDH = '( ( ( CC _D %s ) ` Z ) / ( %s x. ( H ` Z ) ) ) = ( %s + ( ( ( CC _D H ) ` Z ) / ( H ` Z ) ) )' % (G, PZ, LZ)

if __name__ == '__main__' and (not only or 'fprodlogdvh' in only):
    w = W('fprodlogdvh', 'The logarithmic derivative of ` prod_ q e. S ( z - q ) ^ ( O ` q ) x. ( H ` z ) ` at a point of ` D \\ S ` where ` H ` does not vanish.')
    A0 = '( %s /\\ %s )' % (H0, HOLH)
    a0 = w.s([], 'simpl', '( %s -> %s )' % (B0, A0))
    h0 = w.s([a0, w.inst('simpl')], 'syl', '( %s -> %s )' % (B0, H0))
    hol = w.s([a0, w.inst('simpr')], 'syl', '( %s -> %s )' % (B0, HOLH))
    r = common(w, B0, h0, hol)
    zx = w.s([], 'simprl', '( %s -> Z e. %s )' % (B0, X))
    hn0 = w.s([], 'simprr', '( %s -> ( H ` Z ) =/= 0 )' % B0)
    zcs = w.s([r['xcs'], zx], 'sseldd', '( %s -> Z e. %s )' % (B0, CS))
    zd = w.s([r['xd'], zx], 'sseldd', '( %s -> Z e. D )' % B0)
    xcc = w.s([r['xd'], r['dcc']], 'sstrd', '( %s -> %s C_ CC )' % (B0, X))
    # G : D --> CC
    Bz = '( %s /\\ z e. D )' % B0
    zc = w.s([w.s([r['dcc']], 'adantr', '( %s -> D C_ CC )' % Bz), w.s([], 'simpr', '( %s -> z e. D )' % Bz)], 'sseldd', '( %s -> z e. CC )' % Bz)
    Bzq = '( %s /\\ q e. S )' % Bz
    qS = w.s([], 'simpr', '( %s -> q e. S )' % Bzq)
    qc = w.s([w.s([w.s([r['scc']], 'adantr', '( %s -> S C_ CC )' % Bz)], 'adantr', '( %s -> S C_ CC )' % Bzq), qS], 'sseldd', '( %s -> q e. CC )' % Bzq)
    of = w.s([h0, w.inst('simp3')], 'syl', '( %s -> O : S --> NN )' % B0)
    oq = w.s([w.s([w.s([of], 'adantr', '( %s -> O : S --> NN )' % Bz)], 'adantr', '( %s -> O : S --> NN )' % Bzq), qS], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN )' % Bzq)
    t1 = w.s([w.s([w.s([zc], 'adantr', '( %s -> z e. CC )' % Bzq), qc], 'subcld', '( %s -> ( z - q ) e. CC )' % Bzq), w.s([oq], 'nnnn0d', '( %s -> ( O ` q ) e. NN0 )' % Bzq)],
             'expcld', '( %s -> ( ( z - q ) ^ ( O ` q ) ) e. CC )' % Bzq)
    pzc = w.s([w.s([r['sfin']], 'adantr', '( %s -> S e. Fin )' % Bz), t1], 'fprodcl', '( %s -> %s e. CC )' % (Bz, P))
    hzc = w.s([w.s([r['hf']], 'adantr', '( %s -> H : D --> CC )' % Bz), w.s([], 'simpr', '( %s -> z e. D )' % Bz)], 'ffvelcdmd', '( %s -> ( H ` z ) e. CC )' % Bz)
    gz = w.s([pzc, hzc], 'mulcld', '( %s -> ( %s x. ( H ` z ) ) e. CC )' % (Bz, P))
    gf = w.s([gz], 'fmptd', '( %s -> %s : D --> CC )' % (B0, G))
    # restriction
    ante = '( ( CC C_ CC /\\ %s : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) )' % (G, X)
    an = w.s([w.s([closed(w, B0, 'ssid', 'CC C_ CC'), gf], 'jca', '( %s -> ( CC C_ CC /\\ %s : D --> CC ) )' % (B0, G)),
              w.s([r['dcc'], xcc], 'jca', '( %s -> ( D C_ CC /\\ %s C_ CC ) )' % (B0, X))], 'jca', '( %s -> %s )' % (B0, ante))
    INT = '( ( int ` %s ) ` %s )' % (TOPO, X)
    dvr = w.s([an, w.s([r['ej'], r['jr']], 'dvres', '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (ante, G, X, G, INT))], 'syl',
              '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (B0, G, X, G, INT))
    top = closed(w, B0, 'cnfldtop', '%s e. Top' % TOPO)
    intx = w.s([top, r['xop'], w.inst('isopn3i')], 'syl2anc', '( %s -> %s = %s )' % (B0, INT, X))
    e1 = w.s([dvr, w.s([intx], 'reseq2d', '( %s -> ( ( CC _D %s ) |` %s ) = ( ( CC _D %s ) |` %s ) )' % (B0, G, INT, G, X))], 'eqtrd',
             '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s ) )' % (B0, G, X, G, X))
    rsm = w.s([r['xd'], w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (B0, G, X, MX))
    e2 = w.s([rsm], 'oveq2d', '( %s -> ( CC _D ( %s |` %s ) ) = ( CC _D %s ) )' % (B0, G, X, MX))
    fh = w.s([a0, w.inst('fprodhdv')], 'syl', '( %s -> %s )' % (B0, FHDV))
    e3 = w.s([e1, w.s([e2, fh], 'eqtrd', '( %s -> ( CC _D ( %s |` %s ) ) = %s )' % (B0, G, X, RMX))], 'eqtr3d', '( %s -> ( ( CC _D %s ) |` %s ) = %s )' % (B0, G, X, RMX))
    fv = w.s([e3], 'fveq1d', '( %s -> ( ( ( CC _D %s ) |` %s ) ` Z ) = ( %s ` Z ) )' % (B0, G, X, RMX))
    fr = w.s([zx, w.inst('fvres')], 'syl', '( %s -> ( ( ( CC _D %s ) |` %s ) ` Z ) = ( ( CC _D %s ) ` Z ) )' % (B0, G, X, G))
    BODY = '( ( ( %s x. %s ) x. ( H ` z ) ) + ( ( ( CC _D H ) ` z ) x. %s ) )' % (P, L, P)
    st, v = _cg.mptval(w, B0, 'z', X, BODY, 'Z', zx, gen=w.g)
    HZ = '( H ` Z )'; HD = '( ( CC _D H ) ` Z )'
    V1 = '( ( %s x. %s ) x. %s )' % (PZ, LZ, HZ); V2 = '( %s x. %s )' % (HD, PZ)
    assert v == '( %s + %s )' % (V1, V2), v
    dgz = w.s([w.s([fr, fv], 'eqtr3d', '( %s -> ( ( CC _D %s ) ` Z ) = ( %s ` Z ) )' % (B0, G, RMX)), st], 'eqtrd', '( %s -> ( ( CC _D %s ) ` Z ) = %s )' % (B0, G, v))
    # algebra
    lcl = w.s([w.s([h0, zcs], 'jca', '( %s -> ( %s /\\ Z e. %s ) )' % (B0, H0, CS)), w.inst('fprodlcl')], 'syl',
              '( %s -> ( %s e. CC /\\ %s =/= 0 /\\ %s e. CC ) )' % (B0, PZ, PZ, LZ))
    pc = w.s([lcl], 'simp1d', '( %s -> %s e. CC )' % (B0, PZ))
    p0 = w.s([lcl], 'simp2d', '( %s -> %s =/= 0 )' % (B0, PZ))
    lc = w.s([lcl], 'simp3d', '( %s -> %s e. CC )' % (B0, LZ))
    hc = w.s([r['hf'], zd], 'ffvelcdmd', '( %s -> %s e. CC )' % (B0, HZ))
    hdc = w.s([r['hdf'], zd], 'ffvelcdmd', '( %s -> %s e. CC )' % (B0, HD))
    PH = '( %s x. %s )' % (PZ, HZ)
    phc = w.s([pc, hc], 'mulcld', '( %s -> %s e. CC )' % (B0, PH))
    ph0 = w.s([pc, hc, p0, hn0], 'mulne0d', '( %s -> %s =/= 0 )' % (B0, PH))
    v1c = w.s([w.s([pc, lc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (B0, PZ, LZ)), hc], 'mulcld', '( %s -> %s e. CC )' % (B0, V1))
    v2c = w.s([hdc, pc], 'mulcld', '( %s -> %s e. CC )' % (B0, V2))
    dd = w.s([v1c, v2c, phc, ph0], 'divdird', '( %s -> ( %s / %s ) = ( ( %s / %s ) + ( %s / %s ) ) )' % (B0, v, PH, V1, PH, V2, PH))
    r1 = w.s([w.s([pc, lc, hc], 'mul32d', '( %s -> %s = ( %s x. %s ) )' % (B0, V1, PH, LZ)), w.s([phc, lc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (B0, PH, LZ, LZ, PH))],
             'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (B0, V1, LZ, PH))
    q1 = w.s([w.s([r1], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s x. %s ) / %s ) )' % (B0, V1, PH, LZ, PH, PH)),
              w.s([lc, phc, ph0], 'divcan4d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (B0, LZ, PH, PH, LZ))], 'eqtrd', '( %s -> ( %s / %s ) = %s )' % (B0, V1, PH, LZ))
    r2 = w.s([hdc, pc], 'mulcomd', '( %s -> %s = ( %s x. %s ) )' % (B0, V2, PZ, HD))
    q2 = w.s([w.s([r2], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s x. %s ) / %s ) )' % (B0, V2, PH, PZ, HD, PH)),
              w.s([hdc, hc, pc, hn0, p0], 'divcan5d', '( %s -> ( ( %s x. %s ) / %s ) = ( %s / %s ) )' % (B0, PZ, HD, PH, HD, HZ))], 'eqtrd',
             '( %s -> ( %s / %s ) = ( %s / %s ) )' % (B0, V2, PH, HD, HZ))
    alg = w.s([dd, w.s([q1, q2], 'oveq12d', '( %s -> ( ( %s / %s ) + ( %s / %s ) ) = ( %s + ( %s / %s ) ) )' % (B0, V1, PH, V2, PH, LZ, HD, HZ))], 'eqtrd',
              '( %s -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (B0, v, PH, LZ, HD, HZ))
    w.qed([w.s([dgz], 'oveq1d', '( %s -> ( ( ( CC _D %s ) ` Z ) / %s ) = ( %s / %s ) )' % (B0, G, PH, v, PH)), alg], 'eqtrd', '( %s -> %s )' % (B0, LDH))
    run7b(w)


# ---- holzfac's factorisation --------------------------------------------------
HOLF = '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) )'
ABRE = '( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) )'
RRD = '( R e. RR+ /\\ ( ( A - ( R + ( _i x. R ) ) ) crect ( B + ( R + ( _i x. R ) ) ) ) C_ D )'
HAN3 = '( %s /\\ %s /\\ %s )' % (HOLF, ABRE, RRD)
HAN = '( %s /\\ E. w e. ( A crect B ) ( F ` w ) =/= 0 )' % HAN3
RECT = '( A crect B )'
ZS = '{ r e. ( A crect B ) | ( F ` r ) = 0 }'
HOLh = '( h e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D h ) )'
PRZ = lambda x: PR(ZS, x, 'q', 'o')
SMZ = lambda x: SM(ZS, x, 'q', 'o')
FALL = 'A. z e. D ( F ` z ) = ( %s x. ( h ` z ) )' % PRZ('z')
HALL = 'A. z e. ( A crect B ) ( h ` z ) =/= 0'
FAC = '( o : %s --> NN /\\ %s /\\ ( %s /\\ %s ) )' % (ZS, HOLh, FALL, HALL)
LD = lambda x: '( ( ( CC _D F ) ` %s ) / ( F ` %s ) ) = ( %s + ( ( ( CC _D h ) ` %s ) / ( h ` %s ) ) )' % (x, x, SMZ(x), x, x)
RZ = '( %s \\ %s )' % (RECT, ZS)
ALL = 'A. z e. %s %s' % (RZ, LD('z'))

if __name__ == '__main__' and (not only or 'holzlogdvlem' in only):
    w = W('holzlogdvlem', 'The logarithmic derivative of a function factored as in ~ holzfac , off its zeros in the rectangle.')
    C1 = '( %s /\\ %s )' % (HAN, FAC)
    han = w.s([], 'simpl', '( %s -> %s )' % (C1, HAN))
    fac = w.s([], 'simpr', '( %s -> %s )' % (C1, FAC))
    of = w.s([fac, w.inst('simp1')], 'syl', '( %s -> o : %s --> NN )' % (C1, ZS))
    holh = w.s([fac, w.inst('simp2')], 'syl', '( %s -> %s )' % (C1, HOLh))
    fz = w.s([fac, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (C1, FALL, HALL))
    fall = w.s([fz], 'simpld', '( %s -> %s )' % (C1, FALL))
    hall = w.s([fz], 'simprd', '( %s -> %s )' % (C1, HALL))
    zsfin = w.s([han, w.inst('holzfi')], 'syl', '( %s -> %s e. Fin )' % (C1, ZS))
    h3 = w.s([han], 'simpld', '( %s -> %s )' % (C1, HAN3))
    holf = w.s([h3], 'simp1d', '( %s -> %s )' % (C1, HOLF))
    abre = w.s([h3], 'simp2d', '( %s -> %s )' % (C1, ABRE))
    rrd = w.s([h3], 'simp3d', '( %s -> %s )' % (C1, RRD))
    ab = w.s([abre], 'simpld', '( %s -> ( A e. CC /\\ B e. CC ) )' % C1)
    rss = w.s([w.s([holf, ab, rrd], '3jca', '( %s -> ( %s /\\ ( A e. CC /\\ B e. CC ) /\\ %s ) )' % (C1, HOLF, RRD)), w.inst('holnss')], 'syl',
              '( %s -> %s C_ D )' % (C1, RECT))
    fcn = w.s([holf], 'simpld', '( %s -> F e. ( D -cn-> CC ) )' % C1)
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % C1)
    zsr = closed(w, C1, 'ssrab2', '%s C_ %s' % (ZS, RECT))
    zscc = w.s([zsr, w.s([rss, dcc], 'sstrd', '( %s -> %s C_ CC )' % (C1, RECT))], 'sstrd', '( %s -> %s C_ CC )' % (C1, ZS))
    H0I = '( %s e. Fin /\\ %s C_ CC /\\ o : %s --> NN )' % (ZS, ZS, ZS)
    h0i = w.s([zsfin, zscc, of], '3jca', '( %s -> %s )' % (C1, H0I))
    # F as a mapping
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % C1)
    ffn = w.s([ff], 'ffnd', '( %s -> F Fn D )' % C1)
    MF = '( z e. D |-> ( F ` z ) )'
    GH = '( z e. D |-> ( %s x. ( h ` z ) ) )' % PRZ('z')
    f5 = w.s([ffn, w.s([], 'dffn5', '( F Fn D <-> F = %s )' % MF)], 'sylib', '( %s -> F = %s )' % (C1, MF))
    m12 = w.s([w.s([w.s([], 'eqidd', '( %s -> D = D )' % C1), fall], 'jca', '( %s -> ( D = D /\\ %s ) )' % (C1, FALL)), w.inst('mpteq12')], 'syl',
              '( %s -> %s = %s )' % (C1, MF, GH))
    fg = w.s([f5, m12], 'eqtrd', '( %s -> F = %s )' % (C1, GH))
    # at a point v
    C2 = '( %s /\\ v e. %s )' % (C1, RZ)
    vz = w.s([], 'simpr', '( %s -> v e. %s )' % (C2, RZ))
    vr = w.s([vz, w.inst('eldifi')], 'syl', '( %s -> v e. %s )' % (C2, RECT))
    vn = w.s([vz, w.inst('eldifn')], 'syl', '( %s -> -. v e. %s )' % (C2, ZS))
    vd = w.s([w.s([rss], 'adantr', '( %s -> %s C_ D )' % (C2, RECT)), vr], 'sseldd', '( %s -> v e. D )' % C2)
    vdz = w.s([vd, vn], 'eldifd', '( %s -> v e. ( D \\ %s ) )' % (C2, ZS))
    idv = w.s([], 'id', '( z = v -> z = v )')
    ch, newh = w.wcongr('( h ` z ) =/= 0', {'z': 'v'}, 'z = v', {'z': idv})
    hv0 = w.s([ch, w.s([hall], 'adantr', '( %s -> %s )' % (C2, HALL)), vr], 'rspcdva', '( %s -> ( h ` v ) =/= 0 )' % C2)
    cf, newf = w.wcongr('( F ` z ) = ( %s x. ( h ` z ) )' % PRZ('z'), {'z': 'v'}, 'z = v', {'z': idv})
    assert newf == '( F ` v ) = ( %s x. ( h ` v ) )' % PRZ('v'), newf
    fv = w.s([cf, w.s([fall], 'adantr', '( %s -> %s )' % (C2, FALL)), vd], 'rspcdva', '( %s -> %s )' % (C2, newf))
    B0I = '( ( %s /\\ %s ) /\\ ( v e. ( D \\ %s ) /\\ ( h ` v ) =/= 0 ) )' % (H0I, HOLh, ZS)
    b0 = w.s([w.s([w.s([h0i], 'adantr', '( %s -> %s )' % (C2, H0I)), w.s([holh], 'adantr', '( %s -> %s )' % (C2, HOLh))], 'jca', '( %s -> ( %s /\\ %s ) )' % (C2, H0I, HOLh)),
              w.s([vdz, hv0], 'jca', '( %s -> ( v e. ( D \\ %s ) /\\ ( h ` v ) =/= 0 ) )' % (C2, ZS))], 'jca', '( %s -> %s )' % (C2, B0I))
    PHV = '( %s x. ( h ` v ) )' % PRZ('v')
    RH = '( %s + ( ( ( CC _D h ) ` v ) / ( h ` v ) ) )' % SMZ('v')
    fl = w.s([b0, w.inst('fprodlogdvh')], 'syl', '( %s -> ( ( ( CC _D %s ) ` v ) / %s ) = %s )' % (C2, GH, PHV, RH))
    dfg = w.s([w.s([w.s([fg], 'adantr', '( %s -> F = %s )' % (C2, GH))], 'oveq2d', '( %s -> ( CC _D F ) = ( CC _D %s ) )' % (C2, GH))], 'fveq1d',
              '( %s -> ( ( CC _D F ) ` v ) = ( ( CC _D %s ) ` v ) )' % (C2, GH))
    lhs = w.s([dfg, fv], 'oveq12d', '( %s -> ( ( ( CC _D F ) ` v ) / ( F ` v ) ) = ( ( ( CC _D %s ) ` v ) / %s ) )' % (C2, GH, PHV))
    ldv = w.s([lhs, fl], 'eqtrd', '( %s -> %s )' % (C2, LD('v')))
    rv = w.s([ldv], 'ralrimiva', '( %s -> A. v e. %s %s )' % (C1, RZ, LD('v')))
    idz = w.s([], 'id', '( v = z -> v = z )')
    cl_, newl = w.wcongr(LD('v'), {'v': 'z'}, 'v = z', {'v': idz})
    assert newl == LD('z'), newl
    cb = w.s([cl_], 'cbvralvw', '( A. v e. %s %s <-> %s )' % (RZ, LD('v'), ALL))
    w.qed([rv, cb], 'sylib', '( %s -> %s )' % (C1, ALL))
    run7b(w)

if __name__ == '__main__' and (not only or 'holzlogdv' in only):
    w = W('holzlogdv', 'The factorisation of ~ holzfac with the logarithmic derivative on the rectangle off the zeros: '
          '` F \' / F = sum_ q e. ZS ( o ` q ) / ( z - q ) + h \' / h ` .')
    lem = w.s([], 'holzlogdvlem', '( ( %s /\\ %s ) -> %s )' % (HAN, FAC, ALL))
    e = w.s([lem], 'ex', '( %s -> ( %s -> %s ) )' % (HAN, FAC, ALL))
    a = w.s([e], 'ancld', '( %s -> ( %s -> ( %s /\\ %s ) ) )' % (HAN, FAC, FAC, ALL))
    ee = w.s([a], '2eximdv', '( %s -> ( E. o E. h %s -> E. o E. h ( %s /\\ %s ) ) )' % (HAN, FAC, FAC, ALL))
    hz = w.s([], 'holzfac', '( %s -> E. o E. h %s )' % (HAN, FAC))
    w.qed([hz, ee], 'mpd', '( %s -> E. o E. h ( %s /\\ %s ) )' % (HAN, FAC, ALL))
    run7b(w)
