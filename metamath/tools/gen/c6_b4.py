"""Sortie C6 section B, part 4: the local factorisation (holfaclem, holfac)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

QV = '( v e. D |-> %s )' % QB('v')
HOLG = HOLG('g')


def PHI(NEXP, G='g'):
    return '( ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) /\\ ( %s ` P ) =/= 0 /\\ A. z e. D ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) )' % (G, G, G, NEXP, G)


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
    return w.s([e12, e3, e4], '3anbi123d', '( g = %s -> ( %s <-> %s ) )' % (GEXP, PHI(NEXP), PHI(NEXP, GEXP)))


def nsub(w, var, term):
    """( var = term -> ( E. g PHI(var) <-> E. g PHI(term) ) )"""
    s = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( ( z - P ) ^ %s ) = ( ( z - P ) ^ %s ) )' % (var, term, var, term))], 'oveq1d',
                       '( %s = %s -> ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) )' % (var, term, var, term))], 'eqeq2d',
                  '( %s = %s -> ( ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) <-> ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) ) )' % (var, term, var, term))], 'ralbidv',
             '( %s = %s -> ( A. z e. D ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) <-> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) ) )' % (var, term, var, term))
    t = w.s([s], '3anbi3d', '( %s = %s -> ( %s <-> %s ) )' % (var, term, PHI(var), PHI(term)))
    return w.s([t], 'exbidv', '( %s = %s -> ( E. g %s <-> E. g %s ) )' % (var, term, PHI(var), PHI(term)))


if __name__ == '__main__':
    # ---- holfaclem --------------------------------------------------------------
    w = W('holfaclem', 'The local factorisation when the N-th Taylor coefficient is the first nonzero one: F is ( z - P ) ^ N times a function holomorphic on D and nonzero at P.')
    hyp(w, '1', 'holfaclem.c', CDEF)
    A0 = '( %s /\\ ( C ` N ) =/= 0 )' % CTX
    ctx = w.s([], 'simpl', '( %s -> %s )' % (A0, CTX))
    cne = w.s([], 'simpr', '( %s -> ( C ` N ) =/= 0 )' % A0)
    hrm = w.s([ctx, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    nz = w.s([ctx, w.inst('simpr')], 'syl', '( %s -> ( N e. NN /\\ %s ) )' % (A0, ZER))
    d['nn'] = nn = w.s([nz, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    d['hn'] = hn = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    def qvhyp(x):
        s1 = w.s([], 'eqeq1', '( v = %s -> ( v = P <-> %s = P ) )' % (x, x))
        s2 = w.s([w.s([], 'fveq2', '( v = %s -> ( F ` v ) = ( F ` %s ) )' % (x, x)), w.s([w.s([], 'oveq1', '( v = %s -> ( v - P ) = ( %s - P ) )' % (x, x))], 'oveq1d', '( v = %s -> ( ( v - P ) ^ N ) = ( ( %s - P ) ^ N ) )' % (x, x))], 'oveq12d',
                 '( v = %s -> ( ( F ` v ) / ( ( v - P ) ^ N ) ) = ( ( F ` %s ) / ( ( %s - P ) ^ N ) ) )' % (x, x, x))
        s3 = w.s([s1, w.s([], 'eqidd', '( v = %s -> %s = %s )' % (x, QP, QP)), s2], 'ifbieq12d', '( v = %s -> %s = %s )' % (x, QB('v'), QB(x)))
        return w.s([s3], 'cbvmptv', '%s = ( %s e. D |-> %s )' % (QV, x, QB(x)))
    qd = qvhyp('z')
    qdy = qvhyp('y')
    hol = w.s([ctx, w.s(['1', qd], 'holqhol', '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (CTX, QV, QV))], 'syl',
              '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (A0, QV, QV))
    qp = w.s([ctx, w.s(['1', qd], 'holqvp', '( %s -> ( %s ` P ) = %s )' % (CTX, QV, QP))], 'syl', '( %s -> ( %s ` P ) = %s )' % (A0, QV, QP))
    cn = ccl(w, A0, 'N', hn, d['abih'], '1')
    tpic, tne = tpisteps(w, A0)
    qpne = w.s([cn, tpic, cne, tne], 'divne0d', '( %s -> %s =/= 0 )' % (A0, QP))
    ne = w.s([qp, qpne], 'eqnetrd', '( %s -> ( %s ` P ) =/= 0 )' % (A0, QV))
    A1 = '( %s /\\ z e. D )' % A0
    fac = w.s([w.s([ad(w, ctx, A1, CTX), w.s([], 'simpr', '( %s -> z e. D )' % A1)], 'jca', '( %s -> ( %s /\\ z e. D ) )' % (A1, CTX)),
               w.s(['1', qdy], 'holqfac', '( ( %s /\\ z e. D ) -> ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( %s ` z ) ) )' % (CTX, QV))], 'syl',
              '( %s -> ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( %s ` z ) ) )' % (A1, QV))
    ral = w.s([fac], 'ralrimiva', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( %s ` z ) ) )' % (A0, QV))
    body = w.s([hol, ne, ral], '3jca', '( %s -> %s )' % (A0, PHI('N', QV)))
    dex = w.s([d['dss'], closed(w, A0, 'cnex', 'CC e. _V'), w.inst('ssexg')], 'syl2anc', '( %s -> D e. _V )' % A0)
    ex = w.s([dex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, QV))
    sub = gsub(w, QV, 'N')
    w.qed([ex, body, w.s([sub], 'spcegv', '( %s e. _V -> ( %s -> E. g %s ) )' % (QV, PHI('N', QV), PHI('N')))], 'sylc', '( %s -> E. g %s )' % (A0, PHI('N')))
    run1(w, h=True)

    # ---- holfac ------------------------------------------------------------------
    w = W('holfac', 'The local factorisation of a holomorphic function at a point where not all Taylor coefficients vanish: F is ( z - P ) ^ n times a function holomorphic on D and nonzero at P, for some n.')
    hyp(w, '1', 'holfac.c', CDEF)
    NAL = '-. A. k e. NN0 ( C ` k ) = 0'
    A0 = '( %s /\\ %s )' % (HRM, NAL)
    S = '{ k e. NN0 | ( C ` k ) =/= 0 }'
    SM = '{ m e. NN0 | ( C ` m ) =/= 0 }'
    IN = 'inf ( %s , RR , < )' % S
    hrm = w.s([], 'simpl', '( %s -> %s )' % (A0, HRM))
    nal = w.s([], 'simpr', '( %s -> %s )' % (A0, NAL))
    d = hrmctx(w, A0, hrm)
    # S is a nonempty subset of ( ZZ>= ` 0 )
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
    zer = w.s([ci0], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ %s ) ( C ` i ) = 0 )' % (A0, IN))
    # case IN e. NN
    AN = '( %s /\\ %s e. NN )' % (A0, IN)
    ctxn = w.s([ad(w, hrm, AN, HRM), w.s([w.s([], 'simpr', '( %s -> %s e. NN )' % (AN, IN)), ad(w, zer, AN, 'A. i e. ( 0 ..^ %s ) ( C ` i ) = 0' % IN)], 'jca',
                                          '( %s -> ( %s e. NN /\\ A. i e. ( 0 ..^ %s ) ( C ` i ) = 0 ) )' % (AN, IN, IN))], 'jca',
               '( %s -> ( %s /\\ ( %s e. NN /\\ A. i e. ( 0 ..^ %s ) ( C ` i ) = 0 ) ) )' % (AN, HRM, IN, IN))
    CTXN = CTX.replace('N e. NN', '%s e. NN' % IN).replace('( 0 ..^ N )', '( 0 ..^ %s )' % IN)
    fl = w.s(['1'], 'holfaclem', '( ( %s /\\ ( C ` %s ) =/= 0 ) -> E. g %s )' % (CTXN, IN, PHI(IN)))
    case1 = w.s([w.s([ctxn, ad(w, cne, AN, '( C ` %s ) =/= 0' % IN)], 'jca', '( %s -> ( %s /\\ ( C ` %s ) =/= 0 ) )' % (AN, CTXN, IN)), fl], 'syl', '( %s -> E. g %s )' % (AN, PHI(IN)))
    # case IN = 0
    AZ = '( %s /\\ %s = 0 )' % (A0, IN)
    in0 = w.s([], 'simpr', '( %s -> %s = 0 )' % (AZ, IN))
    c0ne = w.s([w.s([in0], 'fveq2d', '( %s -> ( C ` %s ) = ( C ` 0 ) )' % (AZ, IN)), ad(w, cne, AZ, '( C ` %s ) =/= 0' % IN)], 'eqnetrrd', '( %s -> ( C ` 0 ) =/= 0 )' % AZ)
    hc0 = w.s([ad(w, d['abih'], AZ, '( %s /\\ %s /\\ %s )' % (AB, INTP, HOLO)), w.s(['1'], 'holc0', '( ( %s /\\ %s /\\ %s ) -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AB, INTP, HOLO, TPI))], 'syl',
              '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AZ, TPI))
    tfne = w.s([hc0, c0ne], 'eqnetrrd', '( %s -> ( %s x. ( F ` P ) ) =/= 0 )' % (AZ, TPI))
    tpic, tne = tpisteps(w, AZ)
    fp = w.s([ad(w, d['ff'], AZ, 'F : D --> CC'), ad(w, d['pd'], AZ, 'P e. D')], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % AZ)
    fpne = w.s([w.s([tfne, w.s([tpic, fp, w.inst('mulne0b')], 'syl2anc', '( %s -> ( ( %s =/= 0 /\\ ( F ` P ) =/= 0 ) <-> ( %s x. ( F ` P ) ) =/= 0 ) )' % (AZ, TPI, TPI))], 'mpbird',
                 '( %s -> ( %s =/= 0 /\\ ( F ` P ) =/= 0 ) )' % (AZ, TPI)), w.inst('simpr')], 'syl', '( %s -> ( F ` P ) =/= 0 )' % AZ)
    A3 = '( %s /\\ z e. D )' % AZ
    zc = w.s([w.s([d['dss']], 'ad2antrr', '( %s -> D C_ CC )' % A3), w.s([], 'simpr', '( %s -> z e. D )' % A3)], 'sseldd', '( %s -> z e. CC )' % A3)
    fz = w.s([w.s([d['ff']], 'ad2antrr', '( %s -> F : D --> CC )' % A3), w.s([], 'simpr', '( %s -> z e. D )' % A3)], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A3)
    zp = w.s([zc, w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % A3)], 'subcld', '( %s -> ( z - P ) e. CC )' % A3)
    e0 = w.s([w.s([w.s([ad(w, in0, A3, '%s = 0' % IN)], 'oveq2d', '( %s -> ( ( z - P ) ^ %s ) = ( ( z - P ) ^ 0 ) )' % (A3, IN)), w.s([zp], 'exp0d', '( %s -> ( ( z - P ) ^ 0 ) = 1 )' % A3)], 'eqtrd',
                  '( %s -> ( ( z - P ) ^ %s ) = 1 )' % (A3, IN))], 'oveq1d', '( %s -> ( ( ( z - P ) ^ %s ) x. ( F ` z ) ) = ( 1 x. ( F ` z ) ) )' % (A3, IN))
    fe = w.s([w.s([e0, w.s([fz], 'mullidd', '( %s -> ( 1 x. ( F ` z ) ) = ( F ` z ) )' % A3)], 'eqtrd', '( %s -> ( ( ( z - P ) ^ %s ) x. ( F ` z ) ) = ( F ` z ) )' % (A3, IN))], 'eqcomd',
              '( %s -> ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( F ` z ) ) )' % (A3, IN))
    ralf = w.s([fe], 'ralrimiva', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( F ` z ) ) )' % (AZ, IN))
    bodyf = w.s([ad(w, d['hol'], AZ, HOL), fpne, ralf], '3jca', '( %s -> %s )' % (AZ, PHI(IN, 'F')))
    subf = gsub(w, 'F', IN)
    exf = w.s([ad(w, d['fcn'], AZ, 'F e. ( D -cn-> CC )')], 'elexd', '( %s -> F e. _V )' % AZ)
    case2 = w.s([exf, bodyf, w.s([subf], 'spcegv', '( F e. _V -> ( %s -> E. g %s ) )' % (PHI(IN, 'F'), PHI(IN)))], 'sylc', '( %s -> E. g %s )' % (AZ, PHI(IN)))
    # combine
    orx = w.s([inn0, w.inst('elnn0')], 'sylib', '( %s -> ( %s e. NN \\/ %s = 0 ) )' % (A0, IN, IN))
    both = w.s([case1, case2, orx], 'mpjaodan', '( %s -> E. g %s )' % (A0, PHI(IN)))
    sub = nsub(w, 'n', IN)
    w.qed([inn0, both, w.s([sub], 'rspcev', '( ( %s e. NN0 /\\ E. g %s ) -> E. n e. NN0 E. g %s )' % (IN, PHI(IN), PHI('n')))], 'syl2anc', '( %s -> E. n e. NN0 E. g %s )' % (A0, PHI('n')))
    run1(w, h=True)
