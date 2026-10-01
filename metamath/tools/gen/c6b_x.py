"""Sortie C6b, part 1: $d-clean re-proofs of C6's holfaclem, holfac, holid1,
holid2 (whose merged forms carry `$d C y` / `$d C j` and cannot be cited
with the explicit coefficient family), the split-off `holallz`, and the
$e-free forms holid1c, holid2c, holfacc.  Adapted from tools/gen/c6_b4.py
and tools/gen/c6_c.py."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *

QV = '( v e. D |-> %s )' % QB('v')
HOLGg = HOLG('g')


def gsub(w, GEXP, NEXP):
    """( g = GEXP -> ( PHI(NEXP, g) <-> PHI(NEXP, GEXP) ) )"""
    e1 = w.s([], 'eleq1', '( g = %s -> ( g e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) ) )' % (GEXP, GEXP))
    e2 = w.s([w.s([w.s([], 'oveq2', '( g = %s -> ( CC _D g ) = ( CC _D %s ) )' % (GEXP, GEXP))], 'dmeqd', '( g = %s -> dom ( CC _D g ) = dom ( CC _D %s ) )' % (GEXP, GEXP))], 'sseq2d',
             '( g = %s -> ( D C_ dom ( CC _D g ) <-> D C_ dom ( CC _D %s ) ) )' % (GEXP, GEXP))
    e12 = w.s([e1, e2], 'anbi12d', '( g = %s -> ( ( g e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D g ) ) <-> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) ) )' % (GEXP, GEXP, GEXP))
    e3 = w.s([w.s([], 'fveq1', '( g = %s -> ( g ` P ) = ( %s ` P ) )' % (GEXP, GEXP))], 'neeq1d', '( g = %s -> ( ( g ` P ) =/= 0 <-> ( %s ` P ) =/= 0 ) )' % (GEXP, GEXP))
    e4 = w.s([w.s([w.s([w.s([], 'fveq1', '( g = %s -> ( g ` z ) = ( %s ` z ) )' % (GEXP, GEXP))], 'oveq2d', '( g = %s -> ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) = ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) )' % (GEXP, NEXP, NEXP, GEXP))], 'eqeq2d',
                  '( g = %s -> ( ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) <-> ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) ) )' % (GEXP, NEXP, NEXP, GEXP))], 'ralbidv',
             '( g = %s -> ( A. z e. D ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) <-> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) ) )' % (GEXP, NEXP, NEXP, GEXP))
    return w.s([e12, e3, e4], '3anbi123d', '( g = %s -> ( %s <-> %s ) )' % (GEXP, PHI('P', NEXP), PHI('P', NEXP, GEXP)))


def ZERN(n):
    return 'A. i e. ( 0 ..^ %s ) ( C ` i ) = 0' % n


def CTXN(n):
    return '( %s /\\ ( %s e. NN /\\ %s ) )' % (HRM, n, ZERN(n))


NAL = '-. A. k e. NN0 ( C ` k ) = 0'
ALLZ = 'A. k e. NN0 ( C ` k ) = 0'
A0F = '( %s /\\ %s )' % (HRM, NAL)


def TAY(n):
    """the Taylor characterisation of the exponent n"""
    return '( %s /\\ ( C ` %s ) =/= 0 )' % (ZERN(n), n)


def FACX(n):
    return '( %s /\\ E. g %s )' % (TAY(n), PHI('P', n))


if __name__ == '__main__':
    # ---- holfaclemx ---------------------------------------------------------------
    w = W('holfaclemx', 'The local factorisation when the N-th Taylor coefficient is the first nonzero one: F is ( z - P ) ^ N times a function holomorphic on D and nonzero at P.  Re-proof of ~ holfaclem without the distinct-variable condition between C and y, so that the coefficient family can be instantiated.')
    hyp(w, '1', 'holfaclemx.c', CDEF)
    A0 = '( %s /\\ ( C ` N ) =/= 0 )' % CTX
    ctx = w.s([], 'simpl', '( %s -> %s )' % (A0, CTX))
    cne = w.s([], 'simpr', '( %s -> ( C ` N ) =/= 0 )' % A0)
    hrm = w.s([ctx, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    nz = w.s([ctx, w.inst('simpr')], 'syl', '( %s -> ( N e. NN /\\ %s ) )' % (A0, ZER))
    d['nn'] = nn = w.s([nz, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    d['hn'] = hn = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    s1 = w.s([], 'eqeq1', '( v = z -> ( v = P <-> z = P ) )')
    s2 = w.s([w.s([], 'fveq2', '( v = z -> ( F ` v ) = ( F ` z ) )'), w.s([w.s([], 'oveq1', '( v = z -> ( v - P ) = ( z - P ) )')], 'oveq1d', '( v = z -> ( ( v - P ) ^ N ) = ( ( z - P ) ^ N ) )')], 'oveq12d',
             '( v = z -> ( ( F ` v ) / ( ( v - P ) ^ N ) ) = ( ( F ` z ) / ( ( z - P ) ^ N ) ) )')
    s3 = w.s([s1, w.s([], 'eqidd', '( v = z -> %s = %s )' % (QP, QP)), s2], 'ifbieq12d', '( v = z -> %s = %s )' % (QB('v'), QB('z')))
    qd = w.s([s3], 'cbvmptv', '%s = ( z e. D |-> %s )' % (QV, QB('z')))
    qv = w.s([], 'eqid', '%s = %s' % (QV, QV))
    hol = w.s([ctx, w.s(['1', qd], 'holqhol', '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (CTX, QV, QV))], 'syl',
              '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (A0, QV, QV))
    qp = w.s([ctx, w.s(['1', qd], 'holqvp', '( %s -> ( %s ` P ) = %s )' % (CTX, QV, QP))], 'syl', '( %s -> ( %s ` P ) = %s )' % (A0, QV, QP))
    cn = ccl(w, A0, 'N', hn, d['abih'], '1')
    tpic, tne = tpisteps(w, A0)
    qpne = w.s([cn, tpic, cne, tne], 'divne0d', '( %s -> %s =/= 0 )' % (A0, QP))
    ne = w.s([qp, qpne], 'eqnetrd', '( %s -> ( %s ` P ) =/= 0 )' % (A0, QV))
    A1 = '( %s /\\ z e. D )' % A0
    # holqfac at X := z with the quotient map's own binder v (no rename)
    fac = w.s([w.s([ad(w, ctx, A1, CTX), w.s([], 'simpr', '( %s -> z e. D )' % A1)], 'jca', '( %s -> ( %s /\\ z e. D ) )' % (A1, CTX)),
               w.s(['1', qv], 'holqfac', '( ( %s /\\ z e. D ) -> ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( %s ` z ) ) )' % (CTX, QV))], 'syl',
              '( %s -> ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( %s ` z ) ) )' % (A1, QV))
    ral = w.s([fac], 'ralrimiva', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( %s ` z ) ) )' % (A0, QV))
    body = w.s([hol, ne, ral], '3jca', '( %s -> %s )' % (A0, PHI('P', 'N', QV)))
    dex = w.s([d['dss'], closed(w, A0, 'cnex', 'CC e. _V'), w.inst('ssexg')], 'syl2anc', '( %s -> D e. _V )' % A0)
    ex = w.s([dex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, QV))
    sub = gsub(w, QV, 'N')
    w.qed([ex, body, w.s([sub], 'spcegv', '( %s e. _V -> ( %s -> E. g %s ) )' % (QV, PHI('P', 'N', QV), PHI('P', 'N')))], 'sylc', '( %s -> E. g %s )' % (A0, PHI('P', 'N')))
    run1(w)

    # ---- holfacx ------------------------------------------------------------------
    w = W('holfacx', 'The local factorisation of a holomorphic function at a point where not all Taylor coefficients vanish: for the least index n with a nonzero coefficient, F is ( z - P ) ^ n times a function holomorphic on D and nonzero at P.  Re-proof of ~ holfac keeping the Taylor characterisation of n and without a distinct-variable condition between C and j or y.')
    hyp(w, '1', 'holfacx.c', CDEF)
    A0 = A0F
    S = '{ k e. NN0 | ( C ` k ) =/= 0 }'
    SM = '{ m e. NN0 | ( C ` m ) =/= 0 }'
    IN = 'inf ( %s , RR , < )' % S
    hrm = w.s([], 'simpl', '( %s -> %s )' % (A0, HRM))
    nal = w.s([], 'simpr', '( %s -> %s )' % (A0, NAL))
    d = hrmctx(w, A0, hrm)
    ssz = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN0' % S), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'sseqtri', '%s C_ ( ZZ>= ` 0 )' % S)], 'a1i', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (A0, S))
    rex = w.s([nal, w.inst('rexnal')], 'sylibr', '( %s -> E. k e. NN0 -. ( C ` k ) = 0 )' % A0)
    rex2 = w.s([rex, w.s([w.s([], 'df-ne', '( ( C ` k ) =/= 0 <-> -. ( C ` k ) = 0 )')], 'rexbii', '( E. k e. NN0 ( C ` k ) =/= 0 <-> E. k e. NN0 -. ( C ` k ) = 0 )')], 'sylibr',
               '( %s -> E. k e. NN0 ( C ` k ) =/= 0 )' % A0)
    sne = w.s([rex2, w.inst('rabn0')], 'sylibr', '( %s -> %s =/= (/) )' % (A0, S))
    ins = w.s([ssz, sne, w.inst('infssuzcl')], 'syl2anc', '( %s -> %s e. %s )' % (A0, IN, S))
    cbr = w.s([w.s([w.s([], 'fveq2', '( k = m -> ( C ` k ) = ( C ` m ) )')], 'neeq1d', '( k = m -> ( ( C ` k ) =/= 0 <-> ( C ` m ) =/= 0 ) )')], 'cbvrabv', '%s = %s' % (S, SM))
    insm = w.s([ins, w.s([cbr], 'eleq2i', '( %s e. %s <-> %s e. %s )' % (IN, S, IN, SM))], 'sylib', '( %s -> %s e. %s )' % (A0, IN, SM))
    subi = w.s([w.s([], 'fveq2', '( m = %s -> ( C ` m ) = ( C ` %s ) )' % (IN, IN))], 'neeq1d', '( m = %s -> ( ( C ` m ) =/= 0 <-> ( C ` %s ) =/= 0 ) )' % (IN, IN))
    inr = w.s([insm, w.s([subi], 'elrab', '( %s e. %s <-> ( %s e. NN0 /\\ ( C ` %s ) =/= 0 ) )' % (IN, SM, IN, IN))], 'sylib', '( %s -> ( %s e. NN0 /\\ ( C ` %s ) =/= 0 ) )' % (A0, IN, IN))
    inn0 = w.s([inr, w.inst('simpl')], 'syl', '( %s -> %s e. NN0 )' % (A0, IN))
    cne = w.s([inr, w.inst('simpr')], 'syl', '( %s -> ( C ` %s ) =/= 0 )' % (A0, IN))
    # the coefficients below the infimum vanish
    A1 = '( %s /\\ i e. ( 0 ..^ %s ) )' % (A0, IN)
    A2 = '( %s /\\ ( C ` i ) =/= 0 )' % A1
    ifz = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (A1, IN))
    inn = w.s([closed(w, A1, 'fzo0ssnn0', '( 0 ..^ %s ) C_ NN0' % IN), ifz], 'sseldd', '( %s -> i e. NN0 )' % A1)
    ilt = w.s([ifz, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (A1, IN))
    inS = w.s([w.s([ad(w, inn, A2, 'i e. NN0'), w.s([], 'simpr', '( %s -> ( C ` i ) =/= 0 )' % A2)], 'jca', '( %s -> ( i e. NN0 /\\ ( C ` i ) =/= 0 ) )' % A2), w.s([w.s([w.s([], 'fveq2', '( k = i -> ( C ` k ) = ( C ` i ) )')], 'neeq1d', '( k = i -> ( ( C ` k ) =/= 0 <-> ( C ` i ) =/= 0 ) )')], 'elrab', '( i e. %s <-> ( i e. NN0 /\\ ( C ` i ) =/= 0 ) )' % S)], 'sylibr',
              '( %s -> i e. %s )' % (A2, S))
    lei = w.s([w.s([ssz], 'ad2antrr', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (A2, S)), inS, w.inst('infssuzle')], 'syl2anc', '( %s -> %s <_ i )' % (A2, IN))
    ir = w.s([inn], 'nn0red', '( %s -> i e. RR )' % A1)
    inre = w.s([w.s([inn0], 'nn0red', '( %s -> %s e. RR )' % (A0, IN))], 'adantr', '( %s -> %s e. RR )' % (A1, IN))
    nle = w.s([ilt, w.s([ir, inre, w.inst('ltnle')], 'syl2anc', '( %s -> ( i < %s <-> -. %s <_ i ) )' % (A1, IN, IN))], 'mpbid', '( %s -> -. %s <_ i )' % (A1, IN))
    nne_ = w.s([lei, nle], 'mtand', '( %s -> -. ( C ` i ) =/= 0 )' % A1)
    ci0 = w.s([nne_, w.inst('nne')], 'sylib', '( %s -> ( C ` i ) = 0 )' % A1)
    zer = w.s([ci0], 'ralrimiva', '( %s -> %s )' % (A0, ZERN(IN)))
    tayin = w.s([zer, cne], 'jca', '( %s -> %s )' % (A0, TAY(IN)))
    # E. n e. NN0 TAY(n) with n := IN
    tsub = w.s([w.s([w.s([], 'oveq2', '( n = %s -> ( 0 ..^ n ) = ( 0 ..^ %s ) )' % (IN, IN))], 'raleqdv', '( n = %s -> ( %s <-> %s ) )' % (IN, ZERN('n'), ZERN(IN))),
                w.s([w.s([], 'fveq2', '( n = %s -> ( C ` n ) = ( C ` %s ) )' % (IN, IN))], 'neeq1d', '( n = %s -> ( ( C ` n ) =/= 0 <-> ( C ` %s ) =/= 0 ) )' % (IN, IN))], 'anbi12d',
               '( n = %s -> ( %s <-> %s ) )' % (IN, TAY('n'), TAY(IN)))
    extay = w.s([inn0, tayin, w.s([tsub], 'rspcev', '( ( %s e. NN0 /\\ %s ) -> E. n e. NN0 %s )' % (IN, TAY(IN), TAY('n')))], 'syl2anc', '( %s -> E. n e. NN0 %s )' % (A0, TAY('n')))
    # under n e. NN0 and TAY(n): the factorisation
    B0 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (A0, TAY('n'))
    nn0 = w.s([w.s([], 'simpr', '( ( %s /\\ n e. NN0 ) -> n e. NN0 )' % A0)], 'adantr', '( %s -> n e. NN0 )' % B0)
    tay = w.s([], 'simpr', '( %s -> %s )' % (B0, TAY('n')))
    zern = w.s([tay, w.inst('simpl')], 'syl', '( %s -> %s )' % (B0, ZERN('n')))
    cnen = w.s([tay, w.inst('simpr')], 'syl', '( %s -> ( C ` n ) =/= 0 )' % B0)
    a0b = w.s([], 'simpll', '( %s -> %s )' % (B0, A0))
    hrmb = w.s([a0b, hrm], 'syl', '( %s -> %s )' % (B0, HRM))
    # case n e. NN
    AN = '( %s /\\ n e. NN )' % B0
    ctxn = w.s([ad(w, hrmb, AN, HRM), w.s([w.s([], 'simpr', '( %s -> n e. NN )' % AN), ad(w, zern, AN, ZERN('n'))], 'jca', '( %s -> ( n e. NN /\\ %s ) )' % (AN, ZERN('n')))], 'jca',
               '( %s -> %s )' % (AN, CTXN('n')))
    fl = w.s(['1'], 'holfaclemx', '( ( %s /\\ ( C ` n ) =/= 0 ) -> E. g %s )' % (CTXN('n'), PHI('P', 'n')))
    case1 = w.s([w.s([ctxn, ad(w, cnen, AN, '( C ` n ) =/= 0')], 'jca', '( %s -> ( %s /\\ ( C ` n ) =/= 0 ) )' % (AN, CTXN('n'))), fl], 'syl', '( %s -> E. g %s )' % (AN, PHI('P', 'n')))
    # case n = 0
    AZ = '( %s /\\ n = 0 )' % B0
    in0 = w.s([], 'simpr', '( %s -> n = 0 )' % AZ)
    c0ne = w.s([w.s([in0], 'fveq2d', '( %s -> ( C ` n ) = ( C ` 0 ) )' % AZ), ad(w, cnen, AZ, '( C ` n ) =/= 0')], 'eqnetrrd', '( %s -> ( C ` 0 ) =/= 0 )' % AZ)
    abihz = w.s([w.s([a0b, d['abih']], 'syl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (B0, AB, INTP, HOLO))], 'adantr', '( %s -> ( %s /\\ %s /\\ %s ) )' % (AZ, AB, INTP, HOLO))
    hc0 = w.s([abihz, w.s(['1'], 'holc0', '( ( %s /\\ %s /\\ %s ) -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AB, INTP, HOLO, TPI))], 'syl',
              '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AZ, TPI))
    tfne = w.s([hc0, c0ne], 'eqnetrrd', '( %s -> ( %s x. ( F ` P ) ) =/= 0 )' % (AZ, TPI))
    tpic, tne = tpisteps(w, AZ)
    ffz = w.s([w.s([a0b, d['ff']], 'syl', '( %s -> F : D --> CC )' % B0)], 'adantr', '( %s -> F : D --> CC )' % AZ)
    pdz = w.s([w.s([a0b, d['pd']], 'syl', '( %s -> P e. D )' % B0)], 'adantr', '( %s -> P e. D )' % AZ)
    fp = w.s([ffz, pdz], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % AZ)
    fpne = w.s([w.s([tfne, w.s([tpic, fp, w.inst('mulne0b')], 'syl2anc', '( %s -> ( ( %s =/= 0 /\\ ( F ` P ) =/= 0 ) <-> ( %s x. ( F ` P ) ) =/= 0 ) )' % (AZ, TPI, TPI))], 'mpbird',
                 '( %s -> ( %s =/= 0 /\\ ( F ` P ) =/= 0 ) )' % (AZ, TPI)), w.inst('simpr')], 'syl', '( %s -> ( F ` P ) =/= 0 )' % AZ)
    A3 = '( %s /\\ z e. D )' % AZ
    dssz = w.s([w.s([a0b, d['dss']], 'syl', '( %s -> D C_ CC )' % B0)], 'adantr', '( %s -> D C_ CC )' % AZ)
    zc = w.s([w.s([dssz], 'adantr', '( %s -> D C_ CC )' % A3), w.s([], 'simpr', '( %s -> z e. D )' % A3)], 'sseldd', '( %s -> z e. CC )' % A3)
    fz = w.s([w.s([ffz], 'adantr', '( %s -> F : D --> CC )' % A3), w.s([], 'simpr', '( %s -> z e. D )' % A3)], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A3)
    pcz = w.s([w.s([w.s([a0b, d['pc']], 'syl', '( %s -> P e. CC )' % B0)], 'adantr', '( %s -> P e. CC )' % AZ)], 'adantr', '( %s -> P e. CC )' % A3)
    zp = w.s([zc, pcz], 'subcld', '( %s -> ( z - P ) e. CC )' % A3)
    e0 = w.s([w.s([w.s([ad(w, in0, A3, 'n = 0')], 'oveq2d', '( %s -> ( ( z - P ) ^ n ) = ( ( z - P ) ^ 0 ) )' % A3), w.s([zp], 'exp0d', '( %s -> ( ( z - P ) ^ 0 ) = 1 )' % A3)], 'eqtrd',
                  '( %s -> ( ( z - P ) ^ n ) = 1 )' % A3)], 'oveq1d', '( %s -> ( ( ( z - P ) ^ n ) x. ( F ` z ) ) = ( 1 x. ( F ` z ) ) )' % A3)
    fe = w.s([w.s([e0, w.s([fz], 'mullidd', '( %s -> ( 1 x. ( F ` z ) ) = ( F ` z ) )' % A3)], 'eqtrd', '( %s -> ( ( ( z - P ) ^ n ) x. ( F ` z ) ) = ( F ` z ) )' % A3)], 'eqcomd',
              '( %s -> ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( F ` z ) ) )' % A3)
    ralf = w.s([fe], 'ralrimiva', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( F ` z ) ) )' % AZ)
    holz = w.s([w.s([a0b, d['hol']], 'syl', '( %s -> %s )' % (B0, HOL))], 'adantr', '( %s -> %s )' % (AZ, HOL))
    bodyf = w.s([holz, fpne, ralf], '3jca', '( %s -> %s )' % (AZ, PHI('P', 'n', 'F')))
    subf = gsub(w, 'F', 'n')
    exf = w.s([w.s([holz, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % AZ)], 'elexd', '( %s -> F e. _V )' % AZ)
    case2 = w.s([exf, bodyf, w.s([subf], 'spcegv', '( F e. _V -> ( %s -> E. g %s ) )' % (PHI('P', 'n', 'F'), PHI('P', 'n')))], 'sylc', '( %s -> E. g %s )' % (AZ, PHI('P', 'n')))
    orx = w.s([nn0, w.inst('elnn0')], 'sylib', '( %s -> ( n e. NN \\/ n = 0 ) )' % B0)
    both = w.s([case1, case2, orx], 'mpjaodan', '( %s -> E. g %s )' % (B0, PHI('P', 'n')))
    facx = w.s([tay, both], 'jca', '( %s -> %s )' % (B0, FACX('n')))
    imp_ = w.s([facx], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (A0, TAY('n'), FACX('n')))
    rim = w.s([imp_], 'reximdva', '( %s -> ( E. n e. NN0 %s -> E. n e. NN0 %s ) )' % (A0, TAY('n'), FACX('n')))
    w.qed([extay, rim], 'mpd', '( %s -> E. n e. NN0 %s )' % (A0, FACX('n')))
    run1(w)

    # ---- holallz: all Taylor coefficients zero -> F vanishes on the half disc ----------
    w = W('holallz', 'When every Taylor coefficient at P vanishes, a holomorphic function vanishes on the disc of radius R / 2 about P (the first case of the dichotomy ~ holid1x ).')
    hyp(w, '1', 'holallz.c', CDEF)
    A0 = HRM
    d = hrmctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    AZ = '( %s /\\ %s )' % (A0, ALLZ)
    AW = '( %s /\\ w e. CC )' % AZ
    AL = '( %s /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) )' % AW
    allz = w.s([], 'simpr', '( %s -> %s )' % (AZ, ALLZ))
    z0 = closed(w, AZ, '0nn0', '0 e. NN0')
    c0 = w.s([w.s([w.s([], 'fveq2', '( k = 0 -> ( C ` k ) = ( C ` 0 ) )')], 'eqeq1d', '( k = 0 -> ( ( C ` k ) = 0 <-> ( C ` 0 ) = 0 ) )'), allz, z0], 'rspcdva', '( %s -> ( C ` 0 ) = 0 )' % AZ)
    hc0 = w.s([ad(w, d['abih'], AZ, '( %s /\\ %s /\\ %s )' % (AB, INTP, HOLO)), w.s(['1'], 'holc0', '( ( %s /\\ %s /\\ %s ) -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AB, INTP, HOLO, TPI))], 'syl',
              '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AZ, TPI))
    tf0 = w.s([hc0, c0], 'eqtr3d', '( %s -> ( %s x. ( F ` P ) ) = 0 )' % (AZ, TPI))
    tpic, tne = tpisteps(w, AZ)
    fp = w.s([ad(w, d['ff'], AZ, 'F : D --> CC'), ad(w, d['pd'], AZ, 'P e. D')], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % AZ)
    orx = w.s([w.s([tpic, fp, w.inst('mul0or')], 'syl2anc', '( %s -> ( ( %s x. ( F ` P ) ) = 0 <-> ( %s = 0 \\/ ( F ` P ) = 0 ) ) )' % (AZ, TPI, TPI)), tf0], 'mpbid', '( %s -> ( %s = 0 \\/ ( F ` P ) = 0 ) )' % (AZ, TPI))
    fp0 = w.s([w.s([w.s([tne], 'neneqd', '( %s -> -. %s = 0 )' % (AZ, TPI)), w.inst('orel1')], 'syl', '( %s -> ( ( %s = 0 \\/ ( F ` P ) = 0 ) -> ( F ` P ) = 0 ) )' % (AZ, TPI)), orx], 'mpd', '( %s -> ( F ` P ) = 0 )' % AZ)
    AE = '( %s /\\ w = P )' % AL
    ce = w.s([w.s([w.s([], 'simpr', '( %s -> w = P )' % AE)], 'fveq2d', '( %s -> ( F ` w ) = ( F ` P ) )' % AE), w.s([fp0], 'ad3antrrr', '( %s -> ( F ` P ) = 0 )' % AE)], 'eqtrd', '( %s -> ( F ` w ) = 0 )' % AE)
    AN = '( %s /\\ w =/= P )' % AL
    wc = w.s([w.s([], 'simpr', '( %s -> w e. CC )' % AW)], 'ad2antrr', '( %s -> w e. CC )' % AN)
    wle = w.s([w.s([], 'simpr', '( %s -> ( abs ` ( w - P ) ) <_ ( R / 2 ) )' % AL)], 'adantr', '( %s -> ( abs ` ( w - P ) ) <_ ( R / 2 ) )' % AN)
    wne = w.s([], 'simpr', '( %s -> w =/= P )' % AN)
    def a4(st, f):
        return w.s([st], 'ad4antr', '( %s -> %s )' % (AN, f))
    aw = w.s([w.s([wc, a4(d['pc'], 'P e. CC')], 'subcld', '( %s -> ( w - P ) e. CC )' % AN)], 'abscld', '( %s -> ( abs ` ( w - P ) ) e. RR )' % AN)
    hr = w.s([a4(d['Rrp'], 'R e. RR+')], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % AN)
    ltr = w.s([aw, w.s([hr], 'rpred', '( %s -> ( R / 2 ) e. RR )' % AN), a4(d['rr'], 'R e. RR'), wle, w.s([a4(d['Rrp'], 'R e. RR+'), w.inst('rphalflt')], 'syl', '( %s -> ( R / 2 ) < R )' % AN)], 'lelttrd',
              '( %s -> ( abs ` ( w - P ) ) < R )' % AN)
    intw = w.s([w.s([a4(d['ab'], AB), a4(d['it'], INTP), a4(d['rbd'], RBDP)], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (AN, AB, INTP, RBDP)), w.s([wc, ltr], 'jca', '( %s -> ( w e. CC /\\ ( abs ` ( w - P ) ) < R ) )' % AN), w.inst('holdisint')], 'syl2anc',
               '( %s -> %s )' % (AN, INTV('w')))
    basew = w.s([a4(d['ab'], AB), w.s([a4(d['it'], INTP), intw, w.s([wne], 'necomd', '( %s -> P =/= w )' % AN)], '3jca', '( %s -> ( %s /\\ %s /\\ P =/= w ) )' % (AN, INTP, INTV('w'))), a4(d['holo'], HOLO)], '3jca',
               '( %s -> %s )' % (AN, BASEV('w')))
    ctxw = w.s([basew, w.s([w.s([a4(d['rbd'], RBDP), a4(d['rpos'], '0 < R')], 'jca', '( %s -> ( %s /\\ 0 < R ) )' % (AN, RBDP)), wle], 'jca', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) )' % (AN, RBDP)),
                w.s([a4(d['mr'], 'M e. RR'), a4(d['alf'], ALF)], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (AN, ALF))], '3jca',
               '( %s -> ( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) )' % (AN, BASEV('w'), RBDP, ALF))
    gG0, gH = famsteps(w, 'w')
    GM = '( m e. NN0 |-> %s )' % RINT(RMV(E2V('w'), 'm', 'w'), 'A', 'B')
    XYW = '( ( w - P ) / ( y - P ) )'
    gsb = w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( m = n -> ( %s ^ m ) = ( %s ^ n ) )' % (XYW, XYW))], 'oveq2d', '( m = n -> ( ( F ` y ) x. ( %s ^ m ) ) = ( ( F ` y ) x. ( %s ^ n ) ) )' % (XYW, XYW))], 'oveq1d',
                       '( m = n -> ( ( ( F ` y ) x. ( %s ^ m ) ) / ( y - w ) ) = ( ( ( F ` y ) x. ( %s ^ n ) ) / ( y - w ) ) )' % (XYW, XYW))], 'mpteq2dv',
                  '( m = n -> %s = %s )' % (RMV(E2V('w'), 'm', 'w'), RMV(E2V('w'), 'n', 'w')))], 'oveq1d',
             '( m = n -> %s = %s )' % (RINT(RMV(E2V('w'), 'm', 'w'), 'A', 'B'), RINT(RMV(E2V('w'), 'n', 'w'), 'A', 'B')))
    gG = w.s([gsb], 'cbvmptv', '%s = %s' % (GM, GMAP('w')))
    AI = '( %s /\\ i e. NN0 )' % AN
    inn = w.s([], 'simpr', '( %s -> i e. NN0 )' % AI)
    ci0 = w.s([w.s([w.s([], 'fveq2', '( k = i -> ( C ` k ) = ( C ` i ) )')], 'eqeq1d', '( k = i -> ( ( C ` k ) = 0 <-> ( C ` i ) = 0 ) )'), w.s([w.s([allz], 'ad3antrrr', '( %s -> %s )' % (AN, ALLZ))], 'adantr', '( %s -> %s )' % (AI, ALLZ)), inn], 'rspcdva',
              '( %s -> ( C ` i ) = 0 )' % AI)
    hv0 = w.s([gH, '1'], 'holcfval', '( i e. NN0 -> ( %s ` i ) = ( ( ( w - P ) ^ i ) x. ( C ` i ) ) )' % HMAP('w'))
    hv = w.s([inn, hv0], 'syl', '( %s -> ( %s ` i ) = ( ( ( w - P ) ^ i ) x. ( C ` i ) ) )' % (AI, HMAP('w')))
    wpi = w.s([w.s([ad(w, wc, AI, 'w e. CC'), w.s([d['pc']], 'ad5antr', '( %s -> P e. CC )' % AI)], 'subcld', '( %s -> ( w - P ) e. CC )' % AI), inn], 'expcld', '( %s -> ( ( w - P ) ^ i ) e. CC )' % AI)
    hi0 = w.s([hv, w.s([w.s([ci0], 'oveq2d', '( %s -> ( ( ( w - P ) ^ i ) x. ( C ` i ) ) = ( ( ( w - P ) ^ i ) x. 0 ) )' % AI), w.s([wpi], 'mul01d', '( %s -> ( ( ( w - P ) ^ i ) x. 0 ) = 0 )' % AI)], 'eqtrd',
                        '( %s -> ( ( ( w - P ) ^ i ) x. ( C ` i ) ) = 0 )' % AI)], 'eqtrd', '( %s -> ( %s ` i ) = 0 )' % (AI, HMAP('w')))
    allh = w.s([hi0], 'ralrimiva', '( %s -> A. i e. NN0 ( %s ` i ) = 0 )' % (AN, HMAP('w')))
    rid0 = w.s([gG, gH], 'rectintid', '( ( ( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) /\\ A. i e. NN0 ( %s ` i ) = 0 ) -> ( F ` w ) = 0 )' % (BASEV('w'), RBDP, ALF, HMAP('w')))
    cn = w.s([w.s([ctxw, allh], 'jca', '( %s -> ( ( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) /\\ A. i e. NN0 ( %s ` i ) = 0 ) )' % (AN, BASEV('w'), RBDP, ALF, HMAP('w'))), rid0], 'syl',
             '( %s -> ( F ` w ) = 0 )' % AN)
    both = w.s([ce, cn], 'pm2.61dane', '( %s -> ( F ` w ) = 0 )' % AL)
    w.qed([w.s([both], 'ex', '( %s -> ( ( abs ` ( w - P ) ) <_ ( R / 2 ) -> ( F ` w ) = 0 ) )' % AW)], 'ralrimiva', '( %s -> %s )' % (AZ, HALFZ('P')))
    run1(w)

    # ---- holid1x: the dichotomy -----------------------------------------------------------
    w = W('holid1x', 'The dichotomy at a point: either a holomorphic function vanishes on the disc of radius R / 2 about P, or P is not a limit of zeros.  Re-proof of ~ holid1 from ~ holallz and ~ holfacx , without a distinct-variable condition between C and j or y.')
    hyp(w, '1', 'holid1x.c', CDEF)
    A0 = HRM
    d = hrmctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    AZ = '( %s /\\ %s )' % (A0, ALLZ)
    halfz = w.s([w.s(['1'], 'holallz', '( %s -> %s )' % (AZ, HALFZ('P')))], 'orcd', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (AZ, HALFZ('P'), ISO('P', 'r')))
    ANZ = A0F
    fac = w.s(['1'], 'holfacx', '( %s -> E. n e. NN0 %s )' % (ANZ, FACX('n')))
    AN1 = '( %s /\\ n e. NN0 )' % ANZ
    AN2 = '( %s /\\ %s )' % (AN1, PHI('P', 'n'))
    ph2 = w.s([], 'simpr', '( %s -> %s )' % (AN2, PHI('P', 'n')))
    gh = w.s([ph2, w.inst('simp1')], 'syl', '( %s -> ( g e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D g ) ) )' % AN2)
    gpn = w.s([w.s([gh, w.inst('simpl')], 'syl', '( %s -> g e. ( D -cn-> CC ) )' % AN2), w.s([d['pd']], 'ad3antrrr', '( %s -> P e. D )' % AN2), w.s([ph2, w.inst('simp2')], 'syl', '( %s -> ( g ` P ) =/= 0 )' % AN2)], '3jca',
              '( %s -> ( g e. ( D -cn-> CC ) /\\ P e. D /\\ ( g ` P ) =/= 0 ) )' % AN2)
    nn0 = w.s([w.s([], 'simpr', '( %s -> n e. NN0 )' % AN1)], 'adantr', '( %s -> n e. NN0 )' % AN2)
    nfac = w.s([nn0, w.s([ph2, w.inst('simp3')], 'syl', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) )' % AN2)], 'jca', '( %s -> ( n e. NN0 /\\ A. z e. D ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) ) )' % AN2)
    iso = w.s([gpn, nfac, w.inst('holzisol')], 'syl2anc', '( %s -> E. r e. RR+ %s )' % (AN2, ISO('P', 'r')))
    ex1 = w.s([w.s([iso], 'ex', '( %s -> ( %s -> E. r e. RR+ %s ) )' % (AN1, PHI('P', 'n'), ISO('P', 'r')))], 'exlimdv', '( %s -> ( E. g %s -> E. r e. RR+ %s ) )' % (AN1, PHI('P', 'n'), ISO('P', 'r')))
    ex1b = w.s([w.s([], 'simpr', '( %s -> E. g %s )' % (FACX('n'), PHI('P', 'n'))), ex1], 'syl5', '( %s -> ( %s -> E. r e. RR+ %s ) )' % (AN1, FACX('n'), ISO('P', 'r')))
    ex2 = w.s([fac, w.s([ex1b], 'rexlimdva', '( %s -> ( E. n e. NN0 %s -> E. r e. RR+ %s ) )' % (ANZ, FACX('n'), ISO('P', 'r')))], 'mpd', '( %s -> E. r e. RR+ %s )' % (ANZ, ISO('P', 'r')))
    isoz = w.s([ex2], 'olcd', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (ANZ, HALFZ('P'), ISO('P', 'r')))
    w.qed([halfz, isoz], 'pm2.61dan', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (A0, HALFZ('P'), ISO('P', 'r')))
    run1(w)

    # ---- holid2x: the local identity theorem, propagated to the half-disc --------------
    w = W('holid2x', 'The local identity theorem: a holomorphic function vanishing on some disc about P vanishes on the disc of radius R / 2 about P, R the distance from P to the boundary frame.  Re-proof of ~ holid2 from ~ holid1x .')
    hyp(w, '1', 'holid2x.c', CDEF)
    VANS = 'E. s e. RR+ %s' % VAN('P', 's')
    A0 = HRM
    hrm = w.s([], 'id', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    dich = w.s([hrm, w.s(['1'], 'holid1x', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (HRM, HALFZ('P'), ISO('P', 'r')))], 'syl', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (A0, HALFZ('P'), ISO('P', 'r')))
    A1 = '( %s /\\ ( s e. RR+ /\\ %s ) )' % (A0, VAN('P', 's'))
    A2 = '( %s /\\ ( r e. RR+ /\\ %s ) )' % (A1, ISO('P', 'r'))
    srp = w.s([w.s([w.s([], 'simpr', '( %s -> ( s e. RR+ /\\ %s ) )' % (A1, VAN('P', 's'))), w.inst('simpl')], 'syl', '( %s -> s e. RR+ )' % A1)], 'adantr', '( %s -> s e. RR+ )' % A2)
    vans = w.s([w.s([w.s([], 'simpr', '( %s -> ( s e. RR+ /\\ %s ) )' % (A1, VAN('P', 's'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, VAN('P', 's')))], 'adantr', '( %s -> %s )' % (A2, VAN('P', 's')))
    rrp = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (A2, ISO('P', 'r'))), w.inst('simpl')], 'syl', '( %s -> r e. RR+ )' % A2)
    isor = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (A2, ISO('P', 'r'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (A2, ISO('P', 'r')))
    Rrp2 = w.s([d['Rrp']], 'ad2antrr', '( %s -> R e. RR+ )' % A2)
    SM1 = '( ( r x. s ) / ( r + s ) )'
    SM2 = '( ( %s x. R ) / ( %s + R ) )' % (SM1, SM1)
    T = '( %s / 2 )' % SM2
    sm1 = w.s([rrp, srp, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ r /\\ %s <_ s ) ) )' % (A2, SM1, SM1, SM1))
    sm1rp = w.s([sm1, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A2, SM1))
    sm2 = w.s([sm1rp, Rrp2, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ R ) ) )' % (A2, SM2, SM2, SM1, SM2))
    sm2rp = w.s([sm2, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A2, SM2))
    trp = w.s([sm2rp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A2, T))
    tr = w.s([trp], 'rpred', '( %s -> %s e. RR )' % (A2, T))
    tc = w.s([tr], 'recnd', '( %s -> %s e. CC )' % (A2, T))
    tlt = w.s([sm2rp, w.inst('rphalflt')], 'syl', '( %s -> %s < %s )' % (A2, T, SM2))
    sm2r = w.s([sm2rp], 'rpred', '( %s -> %s e. RR )' % (A2, SM2))
    sm1r = w.s([sm1rp], 'rpred', '( %s -> %s e. RR )' % (A2, SM1))
    rr2 = w.s([Rrp2], 'rpred', '( %s -> R e. RR )' % A2)
    ltR = w.s([tr, sm2r, rr2, tlt, w.s([w.s([sm2, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ R ) )' % (A2, SM2, SM1, SM2)), w.inst('simpr')], 'syl', '( %s -> %s <_ R )' % (A2, SM2))], 'ltletrd', '( %s -> %s < R )' % (A2, T))
    lt1 = w.s([tr, sm2r, sm1r, tlt, w.s([w.s([sm2, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ R ) )' % (A2, SM2, SM1, SM2)), w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A2, SM2, SM1))], 'ltletrd', '( %s -> %s < %s )' % (A2, T, SM1))
    ltr = w.s([tr, sm1r, w.s([rrp], 'rpred', '( %s -> r e. RR )' % A2), lt1, w.s([w.s([sm1, w.inst('simpr')], 'syl', '( %s -> ( %s <_ r /\\ %s <_ s ) )' % (A2, SM1, SM1)), w.inst('simpl')], 'syl', '( %s -> %s <_ r )' % (A2, SM1))], 'ltletrd', '( %s -> %s < r )' % (A2, T))
    lts = w.s([tr, sm1r, w.s([srp], 'rpred', '( %s -> s e. RR )' % A2), lt1, w.s([w.s([sm1, w.inst('simpr')], 'syl', '( %s -> ( %s <_ r /\\ %s <_ s ) )' % (A2, SM1, SM1)), w.inst('simpr')], 'syl', '( %s -> %s <_ s )' % (A2, SM1))], 'ltletrd', '( %s -> %s < s )' % (A2, T))
    Z = '( P + %s )' % T
    pc2 = w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % A2)
    zc = w.s([pc2, tc], 'addcld', '( %s -> %s e. CC )' % (A2, Z))
    zmp = w.s([pc2, tc], 'pncan2d', '( %s -> ( %s - P ) = %s )' % (A2, Z, T))
    azp = w.s([w.s([zmp], 'fveq2d', '( %s -> ( abs ` ( %s - P ) ) = ( abs ` %s ) )' % (A2, Z, T)), w.s([tr, w.s([trp], 'rpge0d', '( %s -> 0 <_ %s )' % (A2, T))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A2, T, T))], 'eqtrd',
              '( %s -> ( abs ` ( %s - P ) ) = %s )' % (A2, Z, T))
    zpne = w.s([zmp, w.s([trp], 'rpne0d', '( %s -> %s =/= 0 )' % (A2, T))], 'eqnetrd', '( %s -> ( %s - P ) =/= 0 )' % (A2, Z))
    zne = w.s([zpne, w.s([w.s([zc, pc2, w.inst('subeq0')], 'syl2anc', '( %s -> ( ( %s - P ) = 0 <-> %s = P ) )' % (A2, Z, Z))], 'necon3bid', '( %s -> ( ( %s - P ) =/= 0 <-> %s =/= P ) )' % (A2, Z, Z))], 'mpbid', '( %s -> %s =/= P )' % (A2, Z))
    ltR2 = w.s([azp, ltR], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < R )' % (A2, Z))
    intz = w.s([w.s([w.s([d['ab']], 'ad2antrr', '( %s -> %s )' % (A2, AB)), w.s([d['it']], 'ad2antrr', '( %s -> %s )' % (A2, INTP)), w.s([d['rbd']], 'ad2antrr', '( %s -> %s )' % (A2, RBDP))], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A2, AB, INTP, RBDP)),
                w.s([zc, ltR2], 'jca', '( %s -> ( %s e. CC /\\ ( abs ` ( %s - P ) ) < R ) )' % (A2, Z, Z)), w.inst('holdisint')], 'syl2anc', '( %s -> %s )' % (A2, INTV(Z)))
    zd = w.s([w.s([d['rd']], 'ad2antrr', '( %s -> ( A crect B ) C_ D )' % A2), w.s([w.s([d['ab']], 'ad2antrr', '( %s -> %s )' % (A2, AB)), intz, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. ( A crect B ) )' % (A2, Z))], 'sseldd', '( %s -> %s e. D )' % (A2, Z))
    subv = w.s([w.s([w.s([w.s([], 'oveq1', '( w = %s -> ( w - P ) = ( %s - P ) )' % (Z, Z))], 'fveq2d', '( w = %s -> ( abs ` ( w - P ) ) = ( abs ` ( %s - P ) ) )' % (Z, Z))], 'breq1d', '( w = %s -> ( ( abs ` ( w - P ) ) < s <-> ( abs ` ( %s - P ) ) < s ) )' % (Z, Z)),
               w.s([w.s([], 'fveq2', '( w = %s -> ( F ` w ) = ( F ` %s ) )' % (Z, Z))], 'eqeq1d', '( w = %s -> ( ( F ` w ) = 0 <-> ( F ` %s ) = 0 ) )' % (Z, Z))], 'imbi12d',
              '( w = %s -> ( ( ( abs ` ( w - P ) ) < s -> ( F ` w ) = 0 ) <-> ( ( abs ` ( %s - P ) ) < s -> ( F ` %s ) = 0 ) ) )' % (Z, Z, Z))
    fz0 = w.s([w.s([azp, lts], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < s )' % (A2, Z)), w.s([subv, vans, zd], 'rspcdva', '( %s -> ( ( abs ` ( %s - P ) ) < s -> ( F ` %s ) = 0 ) )' % (A2, Z, Z))], 'mpd', '( %s -> ( F ` %s ) = 0 )' % (A2, Z))
    subi = w.s([w.s([w.s([], 'neeq1', '( z = %s -> ( z =/= P <-> %s =/= P ) )' % (Z, Z)), w.s([w.s([w.s([], 'oveq1', '( z = %s -> ( z - P ) = ( %s - P ) )' % (Z, Z))], 'fveq2d', '( z = %s -> ( abs ` ( z - P ) ) = ( abs ` ( %s - P ) ) )' % (Z, Z))], 'breq1d',
                                                                                           '( z = %s -> ( ( abs ` ( z - P ) ) < r <-> ( abs ` ( %s - P ) ) < r ) )' % (Z, Z))], 'anbi12d',
                    '( z = %s -> ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) <-> ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) ) )' % (Z, Z, Z)),
               w.s([w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (Z, Z))], 'neeq1d', '( z = %s -> ( ( F ` z ) =/= 0 <-> ( F ` %s ) =/= 0 ) )' % (Z, Z))], 'imbi12d',
              '( z = %s -> ( ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) -> ( F ` z ) =/= 0 ) <-> ( ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) -> ( F ` %s ) =/= 0 ) ) )' % (Z, Z, Z, Z))
    fzne = w.s([w.s([zne, w.s([azp, ltr], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < r )' % (A2, Z))], 'jca', '( %s -> ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) )' % (A2, Z, Z)), w.s([subi, isor, zd], 'rspcdva',
                                                                                                                                                                      '( %s -> ( ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) -> ( F ` %s ) =/= 0 ) )' % (A2, Z, Z, Z))], 'mpd',
               '( %s -> ( F ` %s ) =/= 0 )' % (A2, Z))
    fals = w.s([fzne, fz0], 'pm2.21ddne', '( %s -> F. )' % A2)
    nex3 = w.s([w.s([w.s([fals], 'ex', '( %s -> ( ( r e. RR+ /\\ %s ) -> F. ) )' % (A1, ISO('P', 'r')))], 'expd', '( %s -> ( r e. RR+ -> ( %s -> F. ) ) )' % (A1, ISO('P', 'r')))], 'rexlimdv',
               '( %s -> ( E. r e. RR+ %s -> F. ) )' % (A1, ISO('P', 'r')))
    nis = w.s([w.s([nex3], 'imp', '( ( %s /\\ E. r e. RR+ %s ) -> F. )' % (A1, ISO('P', 'r')))], 'inegd', '( %s -> -. E. r e. RR+ %s )' % (A1, ISO('P', 'r')))
    dich1 = w.s([dich], 'adantr', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (A1, HALFZ('P'), ISO('P', 'r')))
    hz = w.s([w.s([nis, w.inst('orel2')], 'syl', '( %s -> ( ( %s \\/ E. r e. RR+ %s ) -> %s ) )' % (A1, HALFZ('P'), ISO('P', 'r'), HALFZ('P'))), dich1], 'mpd', '( %s -> %s )' % (A1, HALFZ('P')))
    e32 = w.s([hz], 'exp32', '( %s -> ( s e. RR+ -> ( %s -> %s ) ) )' % (HRM, VAN('P', 's'), HALFZ('P')))
    rl = w.s([e32], 'rexlimdv', '( %s -> ( %s -> %s ) )' % (HRM, VANS, HALFZ('P')))
    w.qed([rl], 'imp', '( ( %s /\\ %s ) -> %s )' % (HRM, VANS, HALFZ('P')))
    run1(w)

    # ---- the $e-free forms --------------------------------------------------------------
    CM = CMAP('A', 'B', 'P')
    w = W('holid1c', 'The dichotomy ~ holid1x with the coefficient family written out: no hypothesis, so that it can be applied at any centre.')
    ce = w.s([], 'eqid', '%s = %s' % (CM, CM))
    w.qed([ce], 'holid1x', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (HRM, HALFZ('P'), ISO('P', 'r')))
    run1(w)

    w = W('holid2c', 'The local identity theorem ~ holid2x with the coefficient family written out: no hypothesis, so that it can be applied at any centre.')
    ce = w.s([], 'eqid', '%s = %s' % (CM, CM))
    w.qed([ce], 'holid2x', '( ( %s /\\ E. s e. RR+ %s ) -> %s )' % (HRM, VAN('P', 's'), HALFZ('P')))
    run1(w)

    w = W('holfacc', 'The local factorisation at a point about which F does not vanish identically: F is ( z - P ) ^ n times a function holomorphic on D and nonzero at P, for some n.  ~ holfacx with the coefficient family written out and its hypothesis replaced by the vanishing statement it is equivalent to ( ~ holallz ).')
    ce = w.s([], 'eqid', '%s = %s' % (CM, CM))
    ALLZC = ALLZ.replace('( C ` k )', '( %s ` k )' % CM)
    FACXC = FACX('n').replace('( C ` i )', '( %s ` i )' % CM).replace('( C ` n )', '( %s ` n )' % CM)
    A0 = '( %s /\\ -. %s )' % (HRM, HALFZ('P'))
    hrm = w.s([], 'simpl', '( %s -> %s )' % (A0, HRM))
    nh = w.s([], 'simpr', '( %s -> -. %s )' % (A0, HALFZ('P')))
    az = w.s([ce], 'holallz', '( ( %s /\\ %s ) -> %s )' % (HRM, ALLZC, HALFZ('P')))
    AA = '( %s /\\ %s )' % (A0, ALLZC)
    aza = w.s([w.s([hrm], 'adantr', '( %s -> %s )' % (AA, HRM)), w.s([], 'simpr', '( %s -> %s )' % (AA, ALLZC)), az], 'syl2anc', '( %s -> %s )' % (AA, HALFZ('P')))
    nal = w.s([aza, nh], 'mtand', '( %s -> -. %s )' % (A0, ALLZC))
    fx = w.s([ce], 'holfacx', '( ( %s /\\ -. %s ) -> E. n e. NN0 %s )' % (HRM, ALLZC, FACXC))
    ex = w.s([hrm, nal, fx], 'syl2anc', '( %s -> E. n e. NN0 %s )' % (A0, FACXC))
    strip = w.s([w.s([], 'simpr', '( %s -> E. g %s )' % (FACXC, PHI('P', 'n')))], 'reximi', '( E. n e. NN0 %s -> E. n e. NN0 E. g %s )' % (FACXC, PHI('P', 'n')))
    w.qed([ex, strip], 'syl', '( %s -> E. n e. NN0 E. g %s )' % (A0, PHI('P', 'n')))
    run1(w)
