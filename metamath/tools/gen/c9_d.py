"""Sortie C9: holzord (the multiplicity of a factorisation over a finite set is
the order F holord P)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from cl import lift
import congr as _cg
from c9_freeze import S as FS

TOPO = '( TopOpen ` CCfld )'
SP = '( Z \\ { P } )'
X = '( D \\ %s )' % SP
OP = '( O |` %s )' % SP
HOLH = HOLG('H', 'D')


def PRq(T, z, O):
    return 'prod_ q e. %s ( ( %s - q ) ^ ( %s ` q ) )' % (T, z, O)


def gen_holzord():
    w = W('holzord', 'In a factorisation ` F = prod ( z - k ) ^ ( O ` k ) x. H ` over a finite set ` Z ` with ` H ` holomorphic and nonzero on ` Z ` , the exponent at ` P e. Z ` is the order ` ( F holord P ) ` ( ~ holordeq , ~ fprodhdv ).')
    FAC = 'A. v e. D ( F ` v ) = ( prod_ k e. Z ( ( v - k ) ^ ( O ` k ) ) x. ( H ` v ) )'
    X1 = '( %s /\\ ( Z e. Fin /\\ Z C_ D ) )' % HOL
    X2 = '( ( O : Z --> NN /\\ %s ) /\\ ( %s /\\ A. v e. Z ( H ` v ) =/= 0 ) )' % (HOLH, FAC)
    A0 = '( %s /\\ %s /\\ P e. Z )' % (X1, X2)
    x1 = w.s([], 'simp1', '( %s -> %s )' % (A0, X1)); x2 = w.s([], 'simp2', '( %s -> %s )' % (A0, X2))
    pz = w.s([], 'simp3', '( %s -> P e. Z )' % A0)
    hol = w.s([x1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    zfin = w.s([x1, w.inst('simprl')], 'syl', '( %s -> Z e. Fin )' % A0)
    zd = w.s([x1, w.inst('simprr')], 'syl', '( %s -> Z C_ D )' % A0)
    of = w.s([x2, w.inst('simpll')], 'syl', '( %s -> O : Z --> NN )' % A0)
    holh = w.s([x2, w.inst('simplr')], 'syl', '( %s -> %s )' % (A0, HOLH))
    fac = w.s([x2, w.inst('simprl')], 'syl', '( %s -> %s )' % (A0, FAC))
    hnz = w.s([x2, w.inst('simprr')], 'syl', '( %s -> A. v e. Z ( H ` v ) =/= 0 )' % A0)
    fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    hcn = w.s([holh, w.inst('simpl')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
    dcc = w.s([hcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    dop = w.s([holh, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOPO))
    hf = w.s([hcn, w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % A0)
    hdf = w.s([holh, w.inst('holf')], 'syl', '( %s -> ( CC _D H ) : D --> CC )' % A0)
    spz = w.s([], 'difssd', '( %s -> %s C_ Z )' % (A0, SP))
    spfin = w.s([zfin, w.inst('diffi')], 'syl', '( %s -> %s e. Fin )' % (A0, SP))
    spcc = w.s([w.s([spz, zd], 'sstrd', '( %s -> %s C_ D )' % (A0, SP)), dcc], 'sstrd', '( %s -> %s C_ CC )' % (A0, SP))
    opf = w.s([of, spz, w.inst('fssres')], 'syl2anc', '( %s -> %s : %s --> NN )' % (A0, OP, SP))
    H0 = '( %s e. Fin /\\ %s C_ CC /\\ %s : %s --> NN )' % (SP, SP, OP, SP)
    h0 = w.s([spfin, spcc, opf], '3jca', '( %s -> %s )' % (A0, H0))
    # X open
    ej = w.s([], 'eqid', '%s = %s' % (TOPO, TOPO))
    un = w.s([], 'unicntop', 'CC = U. %s' % TOPO)
    fre = w.s([w.s([w.s([ej], 'cnfldhaus', '%s e. Haus' % TOPO), w.inst('haust1')], 'ax-mp', '%s e. Fre' % TOPO)], 'a1i', '( %s -> %s e. Fre )' % (A0, TOPO))
    scld = w.s([fre, spcc, spfin, w.s([un], 't1ficld', '( ( %s e. Fre /\\ %s C_ CC /\\ %s e. Fin ) -> %s e. ( Clsd ` %s ) )' % (TOPO, SP, SP, SP, TOPO))], 'syl3anc',
               '( %s -> %s e. ( Clsd ` %s ) )' % (A0, SP, TOPO))
    xop = w.s([dop, scld, w.s([un], 'difopn', '( ( D e. %s /\\ %s e. ( Clsd ` %s ) ) -> %s e. %s )' % (TOPO, SP, TOPO, X, TOPO))], 'syl2anc', '( %s -> %s e. %s )' % (A0, X, TOPO))
    xcs = w.s([dcc], 'ssdifd', '( %s -> %s C_ ( CC \\ %s ) )' % (A0, X, SP))
    xd = w.s([], 'difssd', '( %s -> %s C_ D )' % (A0, X))
    xcc = w.s([xd, dcc], 'sstrd', '( %s -> %s C_ CC )' % (A0, X))
    # G and its derivative
    PZ = PRq(SP, 'z', OP)
    GB = '( %s x. ( H ` z ) )' % PZ
    G = '( z e. %s |-> %s )' % (X, GB)
    FH = tsub(stmt('fprodhdv'), {'S': SP, 'O': OP})
    fa, fc = ante_of(FH)
    assert fa == '( %s /\\ %s )' % (H0, HOLH), fa
    dveq = w.s([w.s([h0, holh], 'jca', '( %s -> %s )' % (A0, fa)), w.inst('fprodhdv')], 'syl', '( %s -> %s )' % (A0, fc))
    RHS = fc.split(' = ( z e. %s |-> ' % X, 1)[1][:-2]
    Az = '( %s /\\ z e. %s )' % (A0, X)
    L = lambda st: lift(w, st, Az)
    zx = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, X))
    zcs = w.s([L(xcs), zx], 'sseldd', '( %s -> z e. ( CC \\ %s ) )' % (Az, SP))
    zdd = w.s([L(xd), zx], 'sseldd', '( %s -> z e. D )' % Az)
    SMZ = 'sum_ q e. %s ( ( %s ` q ) / ( z - q ) )' % (SP, OP)
    lcl = w.s([w.s([L(h0), zcs], 'jca', '( %s -> ( %s /\\ z e. ( CC \\ %s ) ) )' % (Az, H0, SP)), w.inst('fprodlcl')], 'syl', '( %s -> ( %s e. CC /\\ %s =/= 0 /\\ %s e. CC ) )' % (Az, PZ, PZ, SMZ))
    pc = w.s([lcl], 'simp1d', '( %s -> %s e. CC )' % (Az, PZ))
    sc = w.s([lcl], 'simp3d', '( %s -> %s e. CC )' % (Az, SMZ))
    hz = w.s([L(hf), zdd], 'ffvelcdmd', '( %s -> ( H ` z ) e. CC )' % Az)
    hdz = w.s([L(hdf), zdd], 'ffvelcdmd', '( %s -> ( ( CC _D H ) ` z ) e. CC )' % Az)
    gbc = w.s([pc, hz], 'mulcld', '( %s -> %s e. CC )' % (Az, GB))
    rc = w.s([w.s([w.s([pc, sc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Az, PZ, SMZ)), hz], 'mulcld', '( %s -> ( ( %s x. %s ) x. ( H ` z ) ) e. CC )' % (Az, PZ, SMZ)),
              w.s([hdz, pc], 'mulcld', '( %s -> ( ( ( CC _D H ) ` z ) x. %s ) e. CC )' % (Az, PZ))], 'addcld', '( %s -> %s e. CC )' % (Az, RHS))
    MR = '( z e. %s |-> %s )' % (X, RHS)
    eqm = w.s([], 'eqid', '%s = %s' % (MR, MR))
    dmr = w.s([w.s([rc, eqm], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, MR, X)), w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A0, MR, X))
    dmg = w.s([w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, G, MR)), dmr], 'eqtrd', '( %s -> dom ( CC _D %s ) = %s )' % (A0, G, X))
    eqg = w.s([], 'eqid', '%s = %s' % (G, G))
    gf = w.s([gbc, eqg], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, G, X))
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    gcn = w.s([w.s([ccs, gf, xcc], '3jca', '( %s -> ( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC ) )' % (A0, G, X, X)), dmg, w.inst('dvcn')], 'syl2anc',
              '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, G, X))
    gdm = w.s([w.s([dmg], 'eqcomd', '( %s -> %s = dom ( CC _D %s ) )' % (A0, X, G))], 'eqimssd', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, X, G))
    # P in X, G ( P ) =/= 0
    pd = w.s([zd, pz], 'sseldd', '( %s -> P e. D )' % A0)
    px = w.s([pd, w.s([], 'neldifsnd', '( %s -> -. P e. %s )' % (A0, SP))], 'eldifd', '( %s -> P e. %s )' % (A0, X))
    gp, gpv = _cg.mptval(w, A0, 'z', X, GB, 'P', px, gen=w.g)
    PP = PRq(SP, 'P', OP)
    assert gpv == '( %s x. ( H ` P ) )' % PP, gpv
    pcs = w.s([xcs, px], 'sseldd', '( %s -> P e. ( CC \\ %s ) )' % (A0, SP))
    SMP = 'sum_ q e. %s ( ( %s ` q ) / ( P - q ) )' % (SP, OP)
    lp = w.s([w.s([h0, pcs], 'jca', '( %s -> ( %s /\\ P e. ( CC \\ %s ) ) )' % (A0, H0, SP)), w.inst('fprodlcl')], 'syl', '( %s -> ( %s e. CC /\\ %s =/= 0 /\\ %s e. CC ) )' % (A0, PP, PP, SMP))
    subp = w.s([w.s([], 'fveq2', '( v = P -> ( H ` v ) = ( H ` P ) )')], 'neeq1d', '( v = P -> ( ( H ` v ) =/= 0 <-> ( H ` P ) =/= 0 ) )')
    hp0 = w.s([subp, hnz, pz], 'rspcdva', '( %s -> ( H ` P ) =/= 0 )' % A0)
    hpc = w.s([hf, pd], 'ffvelcdmd', '( %s -> ( H ` P ) e. CC )' % A0)
    gp0 = w.s([gp, w.s([w.s([lp], 'simp1d', '( %s -> %s e. CC )' % (A0, PP)), hpc, w.s([lp], 'simp2d', '( %s -> %s =/= 0 )' % (A0, PP)), hp0], 'mulne0d',
                       '( %s -> %s =/= 0 )' % (A0, gpv))], 'eqnetrd', '( %s -> ( %s ` P ) =/= 0 )' % (A0, G))
    opn = w.s([w.s([of, pz], 'ffvelcdmd', '( %s -> ( O ` P ) e. NN )' % A0)], 'nnnn0d', '( %s -> ( O ` P ) e. NN0 )' % A0)
    # the factorisation on X
    T = '( ( z - P ) ^ ( O ` P ) )'
    PQZ = 'prod_ q e. Z ( ( z - q ) ^ ( O ` q ) )'
    PKV = 'prod_ k e. Z ( ( v - k ) ^ ( O ` k ) )'
    PK = 'prod_ k e. Z ( ( z - k ) ^ ( O ` k ) )'
    subz = w.s([w.s([], 'fveq2', '( v = z -> ( F ` v ) = ( F ` z ) )'),
                w.s([w.s([w.s([w.s([], 'oveq1', '( v = z -> ( v - k ) = ( z - k ) )')], 'oveq1d', '( v = z -> ( ( v - k ) ^ ( O ` k ) ) = ( ( z - k ) ^ ( O ` k ) ) )')], 'prodeq2sdv',
                          '( v = z -> %s = %s )' % (PKV, PK)), w.s([], 'fveq2', '( v = z -> ( H ` v ) = ( H ` z ) )')], 'oveq12d',
                    '( v = z -> ( %s x. ( H ` v ) ) = ( %s x. ( H ` z ) ) )' % (PKV, PK))], 'eqeq12d',
               '( v = z -> ( ( F ` v ) = ( %s x. ( H ` v ) ) <-> ( F ` z ) = ( %s x. ( H ` z ) ) ) )' % (PKV, PK))
    fzd = w.s([subz, L(fac), zdd], 'rspcdva', '( %s -> ( F ` z ) = ( %s x. ( H ` z ) ) )' % (Az, PK))
    cbv = w.s([w.s([w.s([], 'oveq2', '( k = q -> ( z - k ) = ( z - q ) )'), w.s([], 'fveq2', '( k = q -> ( O ` k ) = ( O ` q ) )')], 'oveq12d',
                    '( k = q -> ( ( z - k ) ^ ( O ` k ) ) = ( ( z - q ) ^ ( O ` q ) ) )')], 'cbvprodv', '%s = %s' % (PK, PQZ))
    PQS = PRq(SP, 'z', 'O')
    ud = w.s([pz, w.inst('difsnid')], 'syl', '( %s -> ( %s u. { P } ) = Z )' % (A0, SP))
    PU = 'prod_ q e. ( %s u. { P } ) ( ( z - q ) ^ ( O ` q ) )' % SP
    pu = w.s([w.s([L(ud)], 'prodeq1d', '( %s -> %s = %s )' % (Az, PU, PQZ))], 'eqcomd', '( %s -> %s = %s )' % (Az, PQZ, PU))
    Azq = '( %s /\\ q e. %s )' % (Az, SP)
    qc = w.s([lift(w, spcc, Azq), w.s([], 'simpr', '( %s -> q e. %s )' % (Azq, SP))], 'sseldd', '( %s -> q e. CC )' % Azq)
    zc = w.s([lift(w, xcc, Azq), lift(w, zx, Azq)], 'sseldd', '( %s -> z e. CC )' % Azq)
    oqn = w.s([lift(w, of, Azq), w.s([lift(w, spz, Azq), w.s([], 'simpr', '( %s -> q e. %s )' % (Azq, SP))], 'sseldd', '( %s -> q e. Z )' % Azq)], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN )' % Azq)
    tq = w.s([w.s([zc, qc], 'subcld', '( %s -> ( z - q ) e. CC )' % Azq), w.s([oqn], 'nnnn0d', '( %s -> ( O ` q ) e. NN0 )' % Azq)], 'expcld', '( %s -> ( ( z - q ) ^ ( O ` q ) ) e. CC )' % Azq)
    zc1 = w.s([L(xcc), zx], 'sseldd', '( %s -> z e. CC )' % Az)
    pcc = w.s([L(dcc), L(pd)], 'sseldd', '( %s -> P e. CC )' % Az)
    tc = w.s([w.s([zc1, pcc], 'subcld', '( %s -> ( z - P ) e. CC )' % Az), L(opn)], 'expcld', '( %s -> %s e. CC )' % (Az, T))
    subT = w.s([w.s([], 'oveq2', '( q = P -> ( z - q ) = ( z - P ) )'), w.s([], 'fveq2', '( q = P -> ( O ` q ) = ( O ` P ) )')], 'oveq12d', '( q = P -> ( ( z - q ) ^ ( O ` q ) ) = %s )' % T)
    spl = w.s([w.s([], 'nfv', 'F/ q %s' % Az), w.s([], 'nfcv', 'F/_ q %s' % T), L(spfin), L(pz),
               w.s([], 'neldifsnd', '( %s -> -. P e. %s )' % (Az, SP)), tq, subT, tc], 'fprodsplitsn', '( %s -> %s = ( %s x. %s ) )' % (Az, PU, PQS, T))
    res = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Azq, SP)), w.inst('fvres')], 'syl', '( %s -> ( %s ` q ) = ( O ` q ) )' % (Azq, OP))], 'oveq2d',
                   '( %s -> ( ( z - q ) ^ ( %s ` q ) ) = ( ( z - q ) ^ ( O ` q ) ) )' % (Azq, OP))], 'prodeq2dv', '( %s -> %s = %s )' % (Az, PZ, PQS))
    # F z = T x. G z
    gz = w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, G, G)), gbc], 'fvmpt2d', '( %s -> ( %s ` z ) = %s )' % (Az, G, GB))
    e1 = w.s([w.s([w.s([cbv], 'a1i', '( %s -> %s = %s )' % (Az, PK, PQZ)), pu], 'eqtrd', '( %s -> %s = %s )' % (Az, PK, PU)), spl], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (Az, PK, PQS, T))
    e2 = w.s([fzd, w.s([e1], 'oveq1d', '( %s -> ( %s x. ( H ` z ) ) = ( ( %s x. %s ) x. ( H ` z ) ) )' % (Az, PK, PQS, T))], 'eqtrd', '( %s -> ( F ` z ) = ( ( %s x. %s ) x. ( H ` z ) ) )' % (Az, PQS, T))
    pqs = w.s([res, pc], 'eqeltrrd', '( %s -> %s e. CC )' % (Az, PQS))
    e3 = w.s([pqs, tc, hz], 'mul32d', '( %s -> ( ( %s x. %s ) x. ( H ` z ) ) = ( ( %s x. ( H ` z ) ) x. %s ) )' % (Az, PQS, T, PQS, T))
    e4 = w.s([w.s([pqs, hz], 'mulcld', '( %s -> ( %s x. ( H ` z ) ) e. CC )' % (Az, PQS)), tc], 'mulcomd', '( %s -> ( ( %s x. ( H ` z ) ) x. %s ) = ( %s x. ( %s x. ( H ` z ) ) ) )' % (Az, PQS, T, T, PQS))
    e5 = w.s([w.s([gz, w.s([res], 'oveq1d', '( %s -> ( %s x. ( H ` z ) ) = ( %s x. ( H ` z ) ) )' % (Az, PZ, PQS))], 'eqtrd', '( %s -> ( %s ` z ) = ( %s x. ( H ` z ) ) )' % (Az, G, PQS))], 'oveq2d',
             '( %s -> ( %s x. ( %s ` z ) ) = ( %s x. ( %s x. ( H ` z ) ) ) )' % (Az, T, G, T, PQS))
    fx = w.s([w.s([w.s([e2, e3], 'eqtrd', '( %s -> ( F ` z ) = ( ( %s x. ( H ` z ) ) x. %s ) )' % (Az, PQS, T)), e4], 'eqtrd', '( %s -> ( F ` z ) = ( %s x. ( %s x. ( H ` z ) ) ) )' % (Az, T, PQS)), e5],
             'eqtr4d', '( %s -> ( F ` z ) = ( %s x. ( %s ` z ) ) )' % (Az, T, G))
    GBX = '( %s x. ( H ` x ) )' % PRq(SP, 'x', OP)
    GX = '( x e. %s |-> %s )' % (X, GBX)
    PX = PRq(SP, 'x', OP)
    e_in = w.s([w.s([], 'oveq1', '( z = x -> ( z - q ) = ( x - q ) )')], 'oveq1d', '( z = x -> ( ( z - q ) ^ ( %s ` q ) ) = ( ( x - q ) ^ ( %s ` q ) ) )' % (OP, OP))
    e_pr = w.s([e_in], 'prodeq2sdv', '( z = x -> %s = %s )' % (PZ, PX))
    e_b = w.s([e_pr, w.s([], 'fveq2', '( z = x -> ( H ` z ) = ( H ` x ) )')], 'oveq12d', '( z = x -> %s = %s )' % (GB, GBX))
    ceq = w.s([e_b], 'cbvmptv', '%s = %s' % (G, GX))
    ceqd = w.s([ceq], 'a1i', '( %s -> %s = %s )' % (A0, G, GX))
    gcnx = w.s([ceqd, gcn], 'eqeltrrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GX, X))
    gdmx = w.s([gdm, w.s([w.s([ceqd], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, G, GX))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, G, GX))],
               'sseqtrd', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, X, GX))
    gp0x = w.s([w.s([ceqd], 'fveq1d', '( %s -> ( %s ` P ) = ( %s ` P ) )' % (A0, G, GX)), gp0], 'eqnetrrd', '( %s -> ( %s ` P ) =/= 0 )' % (A0, GX))
    fxx = w.s([fx, w.s([w.s([L(ceqd)], 'fveq1d', '( %s -> ( %s ` z ) = ( %s ` z ) )' % (Az, G, GX))], 'oveq2d', '( %s -> ( %s x. ( %s ` z ) ) = ( %s x. ( %s ` z ) ) )' % (Az, T, G, T, GX))],
              'eqtrd', '( %s -> ( F ` z ) = ( %s x. ( %s ` z ) ) )' % (Az, T, GX))
    FX = 'A. z e. %s ( F ` z ) = ( %s x. ( %s ` z ) )' % (X, T, GX)
    fxa = w.s([fxx], 'ralrimiva', '( %s -> %s )' % (A0, FX))
    G = GX
    gcn, gdm, gp0 = gcnx, gdmx, gp0x
    HE = tsub(stmt('holordeq'), {'V': '( D -cn-> CC )', 'E': X, 'G': G, 'N': '( O ` P )'})
    ha, hc = ante_of(HE)
    q1 = '( F e. ( D -cn-> CC ) /\\ ( %s e. %s /\\ P e. %s ) )' % (X, TOPO, X)
    q2 = '( ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) /\\ ( %s ` P ) =/= 0 )' % (G, X, X, G, G)
    q3 = '( ( O ` P ) e. NN0 /\\ %s )' % FX
    assert ha == '( %s /\\ %s /\\ %s )' % (q1, q2, q3), ha
    ho = w.s([w.s([w.s([fcn, w.s([xop, px], 'jca', '( %s -> ( %s e. %s /\\ P e. %s ) )' % (A0, X, TOPO, X))], 'jca', '( %s -> %s )' % (A0, q1)),
                   w.s([w.s([gcn, gdm], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, G, X, X, G)), gp0], 'jca', '( %s -> %s )' % (A0, q2)),
                   w.s([opn, fxa], 'jca', '( %s -> %s )' % (A0, q3))], '3jca', '( %s -> %s )' % (A0, ha)), w.inst('holordeq')], 'syl', '( %s -> %s )' % (A0, hc))
    goal = '( %s -> ( O ` P ) = ( F holord P ) )' % A0
    assert goal == FS['holzord'], (goal, FS['holzord'])
    w.qed([ho], 'eqcomd', goal)
    return run8(w)


if __name__ == '__main__':
    gen_holzord()
