"""Sortie C6b, part 6: the finite product factorisation (holnss, holzfaclem,
holzfac)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *

RECT = '( A crect B )'


def PR(S, o, z, q='q'):
    return 'prod_ %s e. %s ( ( %s - %s ) ^ ( %s ` %s ) )' % (q, S, z, q, o, q)


def FACT(S, o, h, T=None):
    if T is None:
        T = S
    return '( %s : %s --> NN /\\ %s /\\ ( A. z e. D ( F ` z ) = ( %s x. ( %s ` z ) ) /\\ A. z e. %s ( %s ` z ) =/= 0 ) )' % (o, S, HOLG(h), PR(S, o, 'z'), h, T, h)


def PS(S, T=None):
    return 'E. o E. h %s' % FACT(S, 'o', 'h', T)


def holsub(w, ante, he, h1, h2):
    """( ante -> ( HOLG(h1) <-> HOLG(h2) ) ) from he: ( ante -> h1 = h2 )"""
    e1 = w.s([he], 'eleq1d', '( %s -> ( %s e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) ) )' % (ante, h1, h2))
    e2 = w.s([w.s([w.s([he], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (ante, h1, h2))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (ante, h1, h2))], 'sseq2d',
             '( %s -> ( D C_ dom ( CC _D %s ) <-> D C_ dom ( CC _D %s ) ) )' % (ante, h1, h2))
    return w.s([e1, e2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ante, HOLG(h1), HOLG(h2)))


def facsub(w, S, o1, h1, o2, h2, T=None):
    """closed: ( ( o1 = o2 /\\ h1 = h2 ) -> ( FACT(S,o1,h1,T) <-> FACT(S,o2,h2,T) ) )"""
    if T is None:
        T = S
    AE = '( %s = %s /\\ %s = %s )' % (o1, o2, h1, h2)
    oe = w.s([], 'simpl', '( %s -> %s = %s )' % (AE, o1, o2))
    he = w.s([], 'simpr', '( %s -> %s = %s )' % (AE, h1, h2))
    e1 = w.s([oe, w.inst('feq1')], 'syl', '( %s -> ( %s : %s --> NN <-> %s : %s --> NN ) )' % (AE, o1, S, o2, S))
    e2 = holsub(w, AE, he, h1, h2)
    hz = w.s([he], 'fveq1d', '( %s -> ( %s ` z ) = ( %s ` z ) )' % (AE, h1, h2))
    pq = w.s([w.s([oe], 'fveq1d', '( %s -> ( %s ` q ) = ( %s ` q ) )' % (AE, o1, o2))], 'oveq2d', '( %s -> ( ( z - q ) ^ ( %s ` q ) ) = ( ( z - q ) ^ ( %s ` q ) ) )' % (AE, o1, o2))
    pr = w.s([pq], 'prodeq2sdv', '( %s -> %s = %s )' % (AE, PR(S, o1, 'z'), PR(S, o2, 'z')))
    e3 = w.s([w.s([w.s([pr, hz], 'oveq12d', '( %s -> ( %s x. ( %s ` z ) ) = ( %s x. ( %s ` z ) ) )' % (AE, PR(S, o1, 'z'), h1, PR(S, o2, 'z'), h2))], 'eqeq2d',
                  '( %s -> ( ( F ` z ) = ( %s x. ( %s ` z ) ) <-> ( F ` z ) = ( %s x. ( %s ` z ) ) ) )' % (AE, PR(S, o1, 'z'), h1, PR(S, o2, 'z'), h2))], 'ralbidv',
             '( %s -> ( A. z e. D ( F ` z ) = ( %s x. ( %s ` z ) ) <-> A. z e. D ( F ` z ) = ( %s x. ( %s ` z ) ) ) )' % (AE, PR(S, o1, 'z'), h1, PR(S, o2, 'z'), h2))
    e4 = w.s([w.s([hz], 'neeq1d', '( %s -> ( ( %s ` z ) =/= 0 <-> ( %s ` z ) =/= 0 ) )' % (AE, h1, h2))], 'ralbidv', '( %s -> ( A. z e. %s ( %s ` z ) =/= 0 <-> A. z e. %s ( %s ` z ) =/= 0 ) )' % (AE, T, h1, T, h2))
    e34 = w.s([e3, e4], 'anbi12d', '( %s -> ( ( A. z e. D ( F ` z ) = ( %s x. ( %s ` z ) ) /\\ A. z e. %s ( %s ` z ) =/= 0 ) <-> ( A. z e. D ( F ` z ) = ( %s x. ( %s ` z ) ) /\\ A. z e. %s ( %s ` z ) =/= 0 ) ) )' % (
        AE, PR(S, o1, 'z'), h1, T, h1, PR(S, o2, 'z'), h2, T, h2))
    return w.s([e1, e2, e34], '3anbi123d', '( %s -> ( %s <-> %s ) )' % (AE, FACT(S, o1, h1, T), FACT(S, o2, h2, T)))


def facsubset(w, S1, S2):
    """closed: ( S1 = S2 -> ( PS(S1) <-> PS(S2) ) )"""
    AE = '%s = %s' % (S1, S2)
    e1 = w.s([], 'feq2', '( %s -> ( o : %s --> NN <-> o : %s --> NN ) )' % (AE, S1, S2))
    e2 = w.s([], 'biidd', '( %s -> ( %s <-> %s ) )' % (AE, HOLG('h'), HOLG('h')))
    pr = w.s([], 'prodeq1', '( %s -> %s = %s )' % (AE, PR(S1, 'o', 'z'), PR(S2, 'o', 'z')))
    e3 = w.s([w.s([w.s([pr], 'oveq1d', '( %s -> ( %s x. ( h ` z ) ) = ( %s x. ( h ` z ) ) )' % (AE, PR(S1, 'o', 'z'), PR(S2, 'o', 'z')))], 'eqeq2d',
                  '( %s -> ( ( F ` z ) = ( %s x. ( h ` z ) ) <-> ( F ` z ) = ( %s x. ( h ` z ) ) ) )' % (AE, PR(S1, 'o', 'z'), PR(S2, 'o', 'z')))], 'ralbidv',
             '( %s -> ( A. z e. D ( F ` z ) = ( %s x. ( h ` z ) ) <-> A. z e. D ( F ` z ) = ( %s x. ( h ` z ) ) ) )' % (AE, PR(S1, 'o', 'z'), PR(S2, 'o', 'z')))
    e4 = w.s([], 'raleq', '( %s -> ( A. z e. %s ( h ` z ) =/= 0 <-> A. z e. %s ( h ` z ) =/= 0 ) )' % (AE, S1, S2))
    e34 = w.s([e3, e4], 'anbi12d', '( %s -> ( ( A. z e. D ( F ` z ) = ( %s x. ( h ` z ) ) /\\ A. z e. %s ( h ` z ) =/= 0 ) <-> ( A. z e. D ( F ` z ) = ( %s x. ( h ` z ) ) /\\ A. z e. %s ( h ` z ) =/= 0 ) ) )' % (
        AE, PR(S1, 'o', 'z'), S1, PR(S2, 'o', 'z'), S2))
    f = w.s([e1, e2, e34], '3anbi123d', '( %s -> ( %s <-> %s ) )' % (AE, FACT(S1, 'o', 'h'), FACT(S2, 'o', 'h')))
    return w.s([f], '2exbidv', '( %s -> ( %s <-> %s ) )' % (AE, PS(S1), PS(S2)))


def pridat(w, S, o, h, v):
    """closed: ( z = v -> ( ( F ` z ) = ( PR(S,o,z) x. ( h ` z ) ) <-> ( F ` v ) = ( PR(S,o,v) x. ( h ` v ) ) ) )"""
    A = 'z = %s' % v
    fz = w.s([], 'fveq2', '( %s -> ( F ` z ) = ( F ` %s ) )' % (A, v))
    pq = w.s([w.s([], 'oveq1', '( %s -> ( z - q ) = ( %s - q ) )' % (A, v))], 'oveq1d', '( %s -> ( ( z - q ) ^ ( %s ` q ) ) = ( ( %s - q ) ^ ( %s ` q ) ) )' % (A, o, v, o))
    pr = w.s([pq], 'prodeq2sdv', '( %s -> %s = %s )' % (A, PR(S, o, 'z'), PR(S, o, v)))
    hz = w.s([], 'fveq2', '( %s -> ( %s ` z ) = ( %s ` %s ) )' % (A, h, h, v))
    rhs = w.s([pr, hz], 'oveq12d', '( %s -> ( %s x. ( %s ` z ) ) = ( %s x. ( %s ` %s ) ) )' % (A, PR(S, o, 'z'), h, PR(S, o, v), h, v))
    return w.s([fz, rhs], 'eqeq12d', '( %s -> ( ( F ` z ) = ( %s x. ( %s ` z ) ) <-> ( F ` %s ) = ( %s x. ( %s ` %s ) ) ) )' % (A, PR(S, o, 'z'), h, v, PR(S, o, v), h, v))


def prcq(w, S, o, v, q1='q', q2='c'):
    """closed: PR(S,o,v,q1) = PR(S,o,v,q2)"""
    s = w.s([w.s([], 'oveq2', '( %s = %s -> ( %s - %s ) = ( %s - %s ) )' % (q1, q2, v, q1, v, q2)), w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (q1, q2, o, q1, o, q2))], 'oveq12d',
             '( %s = %s -> ( ( %s - %s ) ^ ( %s ` %s ) ) = ( ( %s - %s ) ^ ( %s ` %s ) ) )' % (q1, q2, v, q1, o, q1, v, q2, o, q2))
    return w.s([s], 'cbvprodv', '%s = %s' % (PR(S, o, v, q1), PR(S, o, v, q2)))


def prodcl(w, ante, S, o, v, sfi, scc, of, vc):
    """( ante -> PR(S,o,v,'c') e. CC ) from sfi: S e. Fin, scc: S C_ CC, of: o : S --> NN, vc: v e. CC"""
    A1 = '( %s /\\ c e. S )' % ante if S == 'S' else '( %s /\\ c e. %s )' % (ante, S)
    cs = w.s([], 'simpr', '( %s -> c e. %s )' % (A1, S))
    cc = w.s([w.s([scc], 'adantr', '( %s -> %s C_ CC )' % (A1, S)), cs], 'sseldd', '( %s -> c e. CC )' % A1)
    oc = w.s([w.s([w.s([of], 'adantr', '( %s -> %s : %s --> NN )' % (A1, o, S)), cs], 'ffvelcdmd', '( %s -> ( %s ` c ) e. NN )' % (A1, o))], 'nnnn0d', '( %s -> ( %s ` c ) e. NN0 )' % (A1, o))
    tc = w.s([w.s([w.s([vc], 'adantr', '( %s -> %s e. CC )' % (A1, v)), cc], 'subcld', '( %s -> ( %s - c ) e. CC )' % (A1, v)), oc], 'expcld', '( %s -> ( ( %s - c ) ^ ( %s ` c ) ) e. CC )' % (A1, v, o))
    return w.s([sfi, tc], 'fprodcl', '( %s -> %s e. CC )' % (ante, PR(S, o, v, 'c'))), tc, cc, oc


if __name__ == '__main__':
    # ---- holnss ---------------------------------------------------------------------
    w = W('holnss', 'A rectangle nested at distance R inside an open set lies inside it.')
    A0 = HAN
    d = hanctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    A1 = '( %s /\\ x e. %s )' % (A0, RECT)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (A1, RECT))
    nst = w.s([w.s([w.s([w.s([d['ab'], d['Rrp']], 'jca', '( %s -> ( %s /\\ R e. RR+ ) )' % (A0, AB))], 'adantr', '( %s -> ( %s /\\ R e. RR+ ) )' % (A1, AB)), xin], 'jca', '( %s -> ( ( %s /\\ R e. RR+ ) /\\ x e. %s ) )' % (A1, AB, RECT)), w.inst('holnest')], 'syl',
              '( %s -> ( %s /\\ %s ) )' % (A1, INTG(AR, BR, 'x'), RBDG(AR, BR, 'x')))
    xout = w.s([w.s([d['abr']], 'adantr', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A1, AR, BR)), w.s([nst, w.inst('simpl')], 'syl', '( %s -> %s )' % (A1, INTG(AR, BR, 'x'))), w.inst('crectinp')], 'syl2anc', '( %s -> x e. ( %s crect %s ) )' % (A1, AR, BR))
    xd = w.s([w.s([d['nss']], 'adantr', '( %s -> ( %s crect %s ) C_ D )' % (A1, AR, BR)), xout], 'sseldd', '( %s -> x e. D )' % A1)
    w.qed([w.s([xd], 'ralrimiva', '( %s -> A. x e. %s x e. D )' % (A0, RECT)), w.s([], 'dfss3', '( %s C_ D <-> A. x e. %s x e. D )' % (RECT, RECT))], 'sylibr', '( %s -> %s C_ D )' % (A0, RECT))
    run1(w)

    # ---- holzfaclem -----------------------------------------------------------------
    w = W('holzfaclem', 'The induction step of the factorisation over the zeros of a holomorphic function on a rectangle: a factorisation over a subset S of the zero set extends to one over S with one more zero Q adjoined, the multiplicity of Q coming from the local factorisation ~ holnfac2 of the cofactor.')
    SQ = '( S C_ %s /\\ Q e. ( %s \\ S ) )' % (ZS, ZS)
    A0 = '( %s /\\ %s /\\ %s )' % (ABNZ, SQ, PS('S'))
    SU = '( S u. { Q } )'
    abnz = w.s([], 'simp1', '( %s -> %s )' % (A0, ABNZ))
    sq = w.s([], 'simp2', '( %s -> %s )' % (A0, SQ))
    ps = w.s([], 'simp3', '( %s -> %s )' % (A0, PS('S')))
    abg = w.s([abnz, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ABGEO))
    nz = w.s([abnz, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NZ))
    d = abgeoctx(w, A0, abg)
    ssz = w.s([sq, w.inst('simpl')], 'syl', '( %s -> S C_ %s )' % (A0, ZS))
    qdf = w.s([w.s([sq, w.inst('simpr')], 'syl', '( %s -> Q e. ( %s \\ S ) )' % (A0, ZS)), w.s([], 'eldif', '( Q e. ( %s \\ S ) <-> ( Q e. %s /\\ -. Q e. S ) )' % (ZS, ZS))], 'sylib', '( %s -> ( Q e. %s /\\ -. Q e. S ) )' % (A0, ZS))
    qzs = w.s([qdf, w.inst('simpl')], 'syl', '( %s -> Q e. %s )' % (A0, ZS))
    qns = w.s([qdf, w.inst('simpr')], 'syl', '( %s -> -. Q e. S )' % A0)
    qr = w.s([qzs, w.s([w.s([w.s([], 'fveq2', '( r = Q -> ( F ` r ) = ( F ` Q ) )')], 'eqeq1d', '( r = Q -> ( ( F ` r ) = 0 <-> ( F ` Q ) = 0 ) )')], 'elrab', '( Q e. %s <-> ( Q e. %s /\\ ( F ` Q ) = 0 ) )' % (ZS, RECT))], 'sylib',
             '( %s -> ( Q e. %s /\\ ( F ` Q ) = 0 ) )' % (A0, RECT))
    qin = w.s([qr, w.inst('simpl')], 'syl', '( %s -> Q e. %s )' % (A0, RECT))
    fq0 = w.s([qr, w.inst('simpr')], 'syl', '( %s -> ( F ` Q ) = 0 )' % A0)
    qex = w.s([qin], 'elexd', '( %s -> Q e. _V )' % A0)
    zsfi = w.s([abnz, w.inst('holzfi')], 'syl', '( %s -> %s e. Fin )' % (A0, ZS))
    sfi = w.s([zsfi, ssz], 'ssfid', '( %s -> S e. Fin )' % A0)
    zsr = closed(w, A0, 'ssrab2', '%s C_ %s' % (ZS, RECT))
    sr = w.s([ssz, zsr], 'sstrd', '( %s -> S C_ %s )' % (A0, RECT))
    rd = w.s([d['han'], w.inst('holnss')], 'syl', '( %s -> %s C_ D )' % (A0, RECT))
    sD = w.s([sr, rd], 'sstrd', '( %s -> S C_ D )' % A0)
    scc = w.s([sr, d['crss']], 'sstrd', '( %s -> S C_ CC )' % A0)
    qD = w.s([rd, qin], 'sseldd', '( %s -> Q e. D )' % A0)
    qc = w.s([d['crss'], qin], 'sseldd', '( %s -> Q e. CC )' % A0)
    # rename the existentials to a, b
    FS = FACT('S', 'o', 'h'); FSab = FACT('S', 'a', 'b')
    nfs = [w.s([], 'nfv', 'F/ a %s' % FS), w.s([], 'nfv', 'F/ b %s' % FS), w.s([], 'nfv', 'F/ o %s' % FSab), w.s([], 'nfv', 'F/ h %s' % FSab)]
    cbv = w.s(nfs + [facsub(w, 'S', 'o', 'h', 'a', 'b')], 'cbvex2v', '( %s <-> E. a E. b %s )' % (PS('S'), FSab))
    psab = w.s([ps, cbv], 'sylib', '( %s -> E. a E. b %s )' % (A0, FSab))
    # under the unpacked factorisation
    B0 = '( %s /\\ %s )' % (A0, FSab)
    fac = w.s([], 'simpr', '( %s -> %s )' % (B0, FSab))
    a0b = w.s([], 'simpl', '( %s -> %s )' % (B0, A0))
    def L(st, f):
        return w.s([a0b, st], 'syl', '( %s -> %s )' % (B0, f))
    af = w.s([fac, w.inst('simp1')], 'syl', '( %s -> a : S --> NN )' % B0)
    hb = w.s([fac, w.inst('simp2')], 'syl', '( %s -> %s )' % (B0, HOLG('b')))
    pr2 = w.s([fac, w.inst('simp3')], 'syl', '( %s -> ( A. z e. D ( F ` z ) = ( %s x. ( b ` z ) ) /\\ A. z e. S ( b ` z ) =/= 0 ) )' % (B0, PR('S', 'a', 'z')))
    PRID = 'A. z e. D ( F ` z ) = ( %s x. ( b ` z ) )' % PR('S', 'a', 'z')
    BNE = 'A. z e. S ( b ` z ) =/= 0'
    prid = w.s([pr2, w.inst('simpl')], 'syl', '( %s -> %s )' % (B0, PRID))
    bne = w.s([pr2, w.inst('simpr')], 'syl', '( %s -> %s )' % (B0, BNE))
    bcn = w.s([hb, w.inst('simpl')], 'syl', '( %s -> b e. ( D -cn-> CC ) )' % B0)
    bf = w.s([bcn, w.inst('cncff')], 'syl', '( %s -> b : D --> CC )' % B0)
    sfib = L(sfi, 'S e. Fin'); sccb = L(scc, 'S C_ CC'); qcb = L(qc, 'Q e. CC'); qDb = L(qD, 'Q e. D'); ffb = L(d['ff'], 'F : D --> CC'); dssb = L(d['dss'], 'D C_ CC')
    qnsb = L(qns, '-. Q e. S'); qexb = L(qex, 'Q e. _V'); sDb = L(sD, 'S C_ D'); rdb = L(rd, '%s C_ D' % RECT); qinb = L(qin, 'Q e. %s' % RECT)
    # b Q = 0
    fQ = w.s([pridat(w, 'S', 'a', 'b', 'Q'), prid, qDb], 'rspcdva', '( %s -> ( F ` Q ) = ( %s x. ( b ` Q ) ) )' % (B0, PR('S', 'a', 'Q')))
    prc, tcq, ccq, ocq = prodcl(w, B0, 'S', 'a', 'Q', sfib, sccb, af, qcb)
    A1c = '( %s /\\ c e. S )' % B0
    cne = w.s([w.s([w.s([], 'simpr', '( %s -> c e. S )' % A1c), w.s([qnsb], 'adantr', '( %s -> -. Q e. S )' % A1c), w.inst('nelne2')], 'syl2anc', '( %s -> c =/= Q )' % A1c)], 'necomd', '( %s -> Q =/= c )' % A1c)
    tne = w.s([w.s([w.s([qcb], 'adantr', '( %s -> Q e. CC )' % A1c), ccq], 'subcld', '( %s -> ( Q - c ) e. CC )' % A1c), w.s([w.s([qcb], 'adantr', '( %s -> Q e. CC )' % A1c), ccq, cne], 'subne0d', '( %s -> ( Q - c ) =/= 0 )' % A1c), w.s([ocq], 'nn0zd', '( %s -> ( a ` c ) e. ZZ )' % A1c), w.inst('expne0i')], 'syl3anc',
              '( %s -> ( ( Q - c ) ^ ( a ` c ) ) =/= 0 )' % A1c)
    prne = w.s([sfib, tcq, tne], 'fprodn0', '( %s -> %s =/= 0 )' % (B0, PR('S', 'a', 'Q', 'c')))
    prcq_ = w.s([prcq(w, 'S', 'a', 'Q')], 'a1i', '( %s -> %s = %s )' % (B0, PR('S', 'a', 'Q'), PR('S', 'a', 'Q', 'c')))
    bQ = w.s([bf, qDb], 'ffvelcdmd', '( %s -> ( b ` Q ) e. CC )' % B0)
    prcc = w.s([prcq_, prc], 'eqeltrd', '( %s -> %s e. CC )' % (B0, PR('S', 'a', 'Q')))
    prneq = w.s([prcq_, prne], 'eqnetrd', '( %s -> %s =/= 0 )' % (B0, PR('S', 'a', 'Q')))
    p0 = w.s([w.s([fQ], 'eqcomd', '( %s -> ( %s x. ( b ` Q ) ) = ( F ` Q ) )' % (B0, PR('S', 'a', 'Q'))), L(fq0, '( F ` Q ) = 0')], 'eqtrd', '( %s -> ( %s x. ( b ` Q ) ) = 0 )' % (B0, PR('S', 'a', 'Q')))
    orx = w.s([w.s([prcc, bQ, w.inst('mul0or')], 'syl2anc', '( %s -> ( ( %s x. ( b ` Q ) ) = 0 <-> ( %s = 0 \\/ ( b ` Q ) = 0 ) ) )' % (B0, PR('S', 'a', 'Q'), PR('S', 'a', 'Q'))), p0], 'mpbid', '( %s -> ( %s = 0 \\/ ( b ` Q ) = 0 ) )' % (B0, PR('S', 'a', 'Q')))
    bq0 = w.s([w.s([w.s([prneq], 'neneqd', '( %s -> -. %s = 0 )' % (B0, PR('S', 'a', 'Q'))), w.inst('orel1')], 'syl', '( %s -> ( ( %s = 0 \\/ ( b ` Q ) = 0 ) -> ( b ` Q ) = 0 ) )' % (B0, PR('S', 'a', 'Q'))), orx], 'mpd', '( %s -> ( b ` Q ) = 0 )' % B0)
    # b is not identically zero on the rectangle
    NZV = 'E. v e. %s ( F ` v ) =/= 0' % RECT
    NZB = 'E. v e. %s ( b ` v ) =/= 0' % RECT
    nzv = w.s([L(nz, NZ), w.s([w.s([w.s([], 'fveq2', '( w = v -> ( F ` w ) = ( F ` v ) )')], 'neeq1d', '( w = v -> ( ( F ` w ) =/= 0 <-> ( F ` v ) =/= 0 ) )')], 'cbvrexvw', '( %s <-> %s )' % (NZ, NZV))], 'sylib', '( %s -> %s )' % (B0, NZV))
    C1 = '( %s /\\ v e. %s )' % (B0, RECT)
    C2 = '( %s /\\ ( F ` v ) =/= 0 )' % C1
    vD = w.s([w.s([rdb], 'adantr', '( %s -> %s C_ D )' % (C1, RECT)), w.s([], 'simpr', '( %s -> v e. %s )' % (C1, RECT))], 'sseldd', '( %s -> v e. D )' % C1)
    vc = w.s([w.s([dssb], 'adantr', '( %s -> D C_ CC )' % C1), vD], 'sseldd', '( %s -> v e. CC )' % C1)
    fv = w.s([pridat(w, 'S', 'a', 'b', 'v'), w.s([prid], 'adantr', '( %s -> %s )' % (C1, PRID)), vD], 'rspcdva', '( %s -> ( F ` v ) = ( %s x. ( b ` v ) ) )' % (C1, PR('S', 'a', 'v')))
    prcv, _, _, _ = prodcl(w, C1, 'S', 'a', 'v', w.s([sfib], 'adantr', '( %s -> S e. Fin )' % C1), w.s([sccb], 'adantr', '( %s -> S C_ CC )' % C1), w.s([af], 'adantr', '( %s -> a : S --> NN )' % C1), vc)
    prcvq = w.s([w.s([prcq(w, 'S', 'a', 'v')], 'a1i', '( %s -> %s = %s )' % (C1, PR('S', 'a', 'v'), PR('S', 'a', 'v', 'c'))), prcv], 'eqeltrd', '( %s -> %s e. CC )' % (C1, PR('S', 'a', 'v')))
    bv = w.s([w.s([bf], 'adantr', '( %s -> b : D --> CC )' % C1), vD], 'ffvelcdmd', '( %s -> ( b ` v ) e. CC )' % C1)
    bvne = w.s([w.s([prcvq], 'adantr', '( %s -> %s e. CC )' % (C2, PR('S', 'a', 'v'))), w.s([bv], 'adantr', '( %s -> ( b ` v ) e. CC )' % C2),
                w.s([w.s([fv], 'adantr', '( %s -> ( F ` v ) = ( %s x. ( b ` v ) ) )' % (C2, PR('S', 'a', 'v'))), w.s([], 'simpr', '( %s -> ( F ` v ) =/= 0 )' % C2)], 'eqnetrrd', '( %s -> ( %s x. ( b ` v ) ) =/= 0 )' % (C2, PR('S', 'a', 'v')))], 'mulne0bbd',
               '( %s -> ( b ` v ) =/= 0 )' % C2)
    nzb = w.s([nzv, w.s([w.s([bvne], 'ex', '( %s -> ( ( F ` v ) =/= 0 -> ( b ` v ) =/= 0 ) )' % C1)], 'reximdva', '( %s -> ( %s -> %s ) )' % (B0, NZV, NZB))], 'mpd', '( %s -> %s )' % (B0, NZB))
    # the local factorisation of b at Q
    ABGB = '( %s /\\ ( %s /\\ %s ) /\\ %s )' % (HOLG('b'), AB, GEO, NEST)
    abgb = w.s([hb, L(w.s([d['ab'], d['geo']], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO)), '( %s /\\ %s )' % (AB, GEO)), L(d['nest'], NEST)], '3jca', '( %s -> %s )' % (B0, ABGB))
    PHIB = PHI('Q', 'n', 'g', 'b')
    EXB = 'E. n e. NN0 E. g %s' % PHIB
    exb = w.s([w.s([abgb, nzb], 'jca', '( %s -> ( %s /\\ %s ) )' % (B0, ABGB, NZB)), qinb, w.inst('holnfac2')], 'syl2anc', '( %s -> %s )' % (B0, EXB))
    C0 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (B0, PHIB)
    phi = w.s([], 'simpr', '( %s -> %s )' % (C0, PHIB))
    b0c = w.s([], 'simpll', '( %s -> %s )' % (C0, B0))
    nn0 = w.s([], 'simplr', '( %s -> n e. NN0 )' % C0)
    def M(st, f):
        return w.s([b0c, st], 'syl', '( %s -> %s )' % (C0, f))
    hg = w.s([phi, w.inst('simp1')], 'syl', '( %s -> %s )' % (C0, HOLG('g')))
    gqne = w.s([phi, w.inst('simp2')], 'syl', '( %s -> ( g ` Q ) =/= 0 )' % C0)
    BFAC = 'A. z e. D ( b ` z ) = ( ( ( z - Q ) ^ n ) x. ( g ` z ) )'
    bfac = w.s([phi, w.inst('simp3')], 'syl', '( %s -> %s )' % (C0, BFAC))
    gf = w.s([w.s([hg, w.inst('simpl')], 'syl', '( %s -> g e. ( D -cn-> CC ) )' % C0), w.inst('cncff')], 'syl', '( %s -> g : D --> CC )' % C0)
    def bfacat(v):
        A = 'z = %s' % v
        return w.s([w.s([], 'fveq2', '( %s -> ( b ` z ) = ( b ` %s ) )' % (A, v)), w.s([w.s([w.s([], 'oveq1', '( %s -> ( z - Q ) = ( %s - Q ) )' % (A, v))], 'oveq1d', '( %s -> ( ( z - Q ) ^ n ) = ( ( %s - Q ) ^ n ) )' % (A, v)), w.s([], 'fveq2', '( %s -> ( g ` z ) = ( g ` %s ) )' % (A, v))], 'oveq12d',
                                                                                   '( %s -> ( ( ( z - Q ) ^ n ) x. ( g ` z ) ) = ( ( ( %s - Q ) ^ n ) x. ( g ` %s ) ) )' % (A, v, v))], 'eqeq12d',
                   '( %s -> ( ( b ` z ) = ( ( ( z - Q ) ^ n ) x. ( g ` z ) ) <-> ( b ` %s ) = ( ( ( %s - Q ) ^ n ) x. ( g ` %s ) ) ) )' % (A, v, v, v))
    bQf = w.s([bfacat('Q'), bfac, M(qDb, 'Q e. D')], 'rspcdva', '( %s -> ( b ` Q ) = ( ( ( Q - Q ) ^ n ) x. ( g ` Q ) ) )' % C0)
    # n =/= 0
    D0 = '( %s /\\ n = 0 )' % C0
    gQc = w.s([gf, M(qDb, 'Q e. D')], 'ffvelcdmd', '( %s -> ( g ` Q ) e. CC )' % C0)
    e0 = w.s([w.s([w.s([w.s([M(qcb, 'Q e. CC')], 'subidd', '( %s -> ( Q - Q ) = 0 )' % C0)], 'adantr', '( %s -> ( Q - Q ) = 0 )' % D0), w.s([], 'simpr', '( %s -> n = 0 )' % D0)], 'oveq12d', '( %s -> ( ( Q - Q ) ^ n ) = ( 0 ^ 0 ) )' % D0),
              closed(w, D0, '0exp0e1', '( 0 ^ 0 ) = 1')], 'eqtrd', '( %s -> ( ( Q - Q ) ^ n ) = 1 )' % D0)
    bq1 = w.s([w.s([bQf], 'adantr', '( %s -> ( b ` Q ) = ( ( ( Q - Q ) ^ n ) x. ( g ` Q ) ) )' % D0), w.s([w.s([e0], 'oveq1d', '( %s -> ( ( ( Q - Q ) ^ n ) x. ( g ` Q ) ) = ( 1 x. ( g ` Q ) ) )' % D0), w.s([w.s([gQc], 'adantr', '( %s -> ( g ` Q ) e. CC )' % D0)], 'mullidd', '( %s -> ( 1 x. ( g ` Q ) ) = ( g ` Q ) )' % D0)], 'eqtrd',
                                                                                                                '( %s -> ( ( ( Q - Q ) ^ n ) x. ( g ` Q ) ) = ( g ` Q ) )' % D0)], 'eqtrd', '( %s -> ( b ` Q ) = ( g ` Q ) )' % D0)
    bqne = w.s([bq1, w.s([gqne], 'adantr', '( %s -> ( g ` Q ) =/= 0 )' % D0)], 'eqnetrd', '( %s -> ( b ` Q ) =/= 0 )' % D0)
    fals = w.s([bqne, w.s([M(bq0, '( b ` Q ) = 0')], 'adantr', '( %s -> ( b ` Q ) = 0 )' % D0)], 'pm2.21ddne', '( %s -> F. )' % D0)
    nne0 = w.s([w.s([fals], 'inegd', '( %s -> -. n = 0 )' % C0)], 'neqned', '( %s -> n =/= 0 )' % C0)
    nnn = w.s([nn0, nne0, w.s([], 'elnnne0', '( n e. NN <-> ( n e. NN0 /\\ n =/= 0 ) )')], 'sylanbrc', '( %s -> n e. NN )' % C0)
    # the new exponent function
    OP = '( a u. { <. Q , n >. } )'
    f1 = w.s([M(af, 'a : S --> NN'), w.s([M(qexb, 'Q e. _V'), M(qnsb, '-. Q e. S')], 'jca', '( %s -> ( Q e. _V /\\ -. Q e. S ) )' % C0), nnn, w.inst('fsnunf')], 'syl3anc', '( %s -> %s : %s --> NN )' % (C0, OP, SU))
    dma = w.s([M(af, 'a : S --> NN'), w.inst('fdm')], 'syl', '( %s -> dom a = S )' % C0)
    qnd = w.s([w.s([dma], 'eleq2d', '( %s -> ( Q e. dom a <-> Q e. S ) )' % C0), M(qnsb, '-. Q e. S')], 'mtbird', '( %s -> -. Q e. dom a )' % C0)
    opq = w.s([M(qexb, 'Q e. _V'), nnn, qnd, w.inst('fsnunfv')], 'syl3anc', '( %s -> ( %s ` Q ) = n )' % (C0, OP))
    # the factorisation over S u. { Q } at a point v of D
    E0 = '( %s /\\ v e. D )' % C0
    def N(st, f):
        return w.s([st], 'adantr', '( %s -> %s )' % (E0, f))
    vD = w.s([], 'simpr', '( %s -> v e. D )' % E0)
    vc = w.s([N(M(dssb, 'D C_ CC'), 'D C_ CC'), vD], 'sseldd', '( %s -> v e. CC )' % E0)
    fv = w.s([pridat(w, 'S', 'a', 'b', 'v'), N(M(prid, PRID), PRID), vD], 'rspcdva', '( %s -> ( F ` v ) = ( %s x. ( b ` v ) ) )' % (E0, PR('S', 'a', 'v')))
    bvf = w.s([bfacat('v'), N(bfac, BFAC), vD], 'rspcdva', '( %s -> ( b ` v ) = ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) )' % E0)
    sfie = N(M(sfib, 'S e. Fin'), 'S e. Fin'); scce = N(M(sccb, 'S C_ CC'), 'S C_ CC'); afe = N(M(af, 'a : S --> NN'), 'a : S --> NN')
    prcv, tcv, ccv, ocv = prodcl(w, E0, 'S', 'a', 'v', sfie, scce, afe, vc)
    prq = w.s([prcq(w, 'S', 'a', 'v')], 'a1i', '( %s -> %s = %s )' % (E0, PR('S', 'a', 'v'), PR('S', 'a', 'v', 'c')))
    PRSO = PR('S', OP, 'v', 'c')
    PRSA = PR('S', 'a', 'v', 'c')
    PRU = PR(SU, OP, 'v', 'c')
    E1 = '( %s /\\ c e. S )' % E0
    qnse = N(M(qnsb, '-. Q e. S'), '-. Q e. S')
    qnc = w.s([w.s([w.s([], 'simpr', '( %s -> c e. S )' % E1), w.s([qnse], 'adantr', '( %s -> -. Q e. S )' % E1), w.inst('nelne2')], 'syl2anc', '( %s -> c =/= Q )' % E1)], 'necomd', '( %s -> Q =/= c )' % E1)
    opc = w.s([qnc, w.inst('fvunsn')], 'syl', '( %s -> ( %s ` c ) = ( a ` c ) )' % (E1, OP))
    pso = w.s([w.s([opc], 'oveq2d', '( %s -> ( ( v - c ) ^ ( %s ` c ) ) = ( ( v - c ) ^ ( a ` c ) ) )' % (E1, OP))], 'prodeq2dv', '( %s -> %s = %s )' % (E0, PRSO, PRSA))
    tco = w.s([w.s([opc], 'oveq2d', '( %s -> ( ( v - c ) ^ ( %s ` c ) ) = ( ( v - c ) ^ ( a ` c ) ) )' % (E1, OP)), tcv], 'eqeltrd', '( %s -> ( ( v - c ) ^ ( %s ` c ) ) e. CC )' % (E1, OP))
    vq = w.s([vc, N(M(qcb, 'Q e. CC'), 'Q e. CC')], 'subcld', '( %s -> ( v - Q ) e. CC )' % E0)
    DQ = '( ( v - Q ) ^ ( %s ` Q ) )' % OP
    dqn = w.s([N(opq, '( %s ` Q ) = n' % OP)], 'oveq2d', '( %s -> %s = ( ( v - Q ) ^ n ) )' % (E0, DQ))
    vqn = w.s([vq, N(nn0, 'n e. NN0')], 'expcld', '( %s -> ( ( v - Q ) ^ n ) e. CC )' % E0)
    dqc = w.s([dqn, vqn], 'eqeltrd', '( %s -> %s e. CC )' % (E0, DQ))
    csub = w.s([w.s([], 'oveq2', '( c = Q -> ( v - c ) = ( v - Q ) )'), w.s([], 'fveq2', '( c = Q -> ( %s ` c ) = ( %s ` Q ) )' % (OP, OP))], 'oveq12d', '( c = Q -> ( ( v - c ) ^ ( %s ` c ) ) = %s )' % (OP, DQ))
    spl = w.s([w.s([], 'nfv', 'F/ c %s' % E0), w.s([], 'nfcv', 'F/_ c %s' % DQ), sfie, N(M(qexb, 'Q e. _V'), 'Q e. _V'), N(M(qnsb, '-. Q e. S'), '-. Q e. S'), tco, csub, dqc], 'fprodsplitsn',
              '( %s -> %s = ( %s x. %s ) )' % (E0, PRU, PRSO, DQ))
    spl2 = w.s([spl, w.s([pso, dqn], 'oveq12d', '( %s -> ( %s x. %s ) = ( %s x. ( ( v - Q ) ^ n ) ) )' % (E0, PRSO, DQ, PRSA))], 'eqtrd', '( %s -> %s = ( %s x. ( ( v - Q ) ^ n ) ) )' % (E0, PRU, PRSA))
    gv = w.s([N(gf, 'g : D --> CC'), vD], 'ffvelcdmd', '( %s -> ( g ` v ) e. CC )' % E0)
    fv2 = w.s([fv, w.s([prq, bvf], 'oveq12d', '( %s -> ( %s x. ( b ` v ) ) = ( %s x. ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) ) )' % (E0, PR('S', 'a', 'v'), PRSA))], 'eqtrd',
              '( %s -> ( F ` v ) = ( %s x. ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) ) )' % (E0, PRSA))
    asc = w.s([w.s([prcv, vqn, gv], 'mulassd', '( %s -> ( ( %s x. ( ( v - Q ) ^ n ) ) x. ( g ` v ) ) = ( %s x. ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) ) )' % (E0, PRSA, PRSA))], 'eqcomd',
              '( %s -> ( %s x. ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) ) = ( ( %s x. ( ( v - Q ) ^ n ) ) x. ( g ` v ) ) )' % (E0, PRSA, PRSA))
    fv3 = w.s([w.s([fv2, asc], 'eqtrd', '( %s -> ( F ` v ) = ( ( %s x. ( ( v - Q ) ^ n ) ) x. ( g ` v ) ) )' % (E0, PRSA)), w.s([w.s([spl2], 'eqcomd', '( %s -> ( %s x. ( ( v - Q ) ^ n ) ) = %s )' % (E0, PRSA, PRU))], 'oveq1d',
                                                                                                                                       '( %s -> ( ( %s x. ( ( v - Q ) ^ n ) ) x. ( g ` v ) ) = ( %s x. ( g ` v ) ) )' % (E0, PRSA, PRU))], 'eqtrd',
              '( %s -> ( F ` v ) = ( %s x. ( g ` v ) ) )' % (E0, PRU))
    back = w.s([prcq(w, SU, OP, 'v', 'c', 'q')], 'a1i', '( %s -> %s = %s )' % (E0, PRU, PR(SU, OP, 'v')))
    fv4 = w.s([fv3, w.s([back], 'oveq1d', '( %s -> ( %s x. ( g ` v ) ) = ( %s x. ( g ` v ) ) )' % (E0, PRU, PR(SU, OP, 'v')))], 'eqtrd', '( %s -> ( F ` v ) = ( %s x. ( g ` v ) ) )' % (E0, PR(SU, OP, 'v')))
    RALV = 'A. v e. D ( F ` v ) = ( %s x. ( g ` v ) )' % PR(SU, OP, 'v')
    RALZ = 'A. z e. D ( F ` z ) = ( %s x. ( g ` z ) )' % PR(SU, OP, 'z')
    ralv = w.s([fv4], 'ralrimiva', '( %s -> %s )' % (C0, RALV))
    vzs = w.s([w.s([], 'fveq2', '( v = z -> ( F ` v ) = ( F ` z ) )'), w.s([w.s([w.s([w.s([], 'oveq1', '( v = z -> ( v - q ) = ( z - q ) )')], 'oveq1d', '( v = z -> ( ( v - q ) ^ ( %s ` q ) ) = ( ( z - q ) ^ ( %s ` q ) ) )' % (OP, OP))], 'prodeq2sdv', '( v = z -> %s = %s )' % (PR(SU, OP, 'v'), PR(SU, OP, 'z'))), w.s([], 'fveq2', '( v = z -> ( g ` v ) = ( g ` z ) )')], 'oveq12d', '( v = z -> ( %s x. ( g ` v ) ) = ( %s x. ( g ` z ) ) )' % (PR(SU, OP, 'v'), PR(SU, OP, 'z')))], 'eqeq12d',
              '( v = z -> ( ( F ` v ) = ( %s x. ( g ` v ) ) <-> ( F ` z ) = ( %s x. ( g ` z ) ) ) )' % (PR(SU, OP, 'v'), PR(SU, OP, 'z')))
    f3 = w.s([ralv, w.s([vzs], 'cbvralvw', '( %s <-> %s )' % (RALV, RALZ))], 'sylib', '( %s -> %s )' % (C0, RALZ))
    # g nonzero on S u. { Q }
    G0 = '( %s /\\ v e. %s )' % (C0, SU)
    vu = w.s([w.s([], 'simpr', '( %s -> v e. %s )' % (G0, SU)), w.s([], 'elun', '( v e. %s <-> ( v e. S \\/ v e. { Q } ) )' % SU)], 'sylib', '( %s -> ( v e. S \\/ v e. { Q } ) )' % G0)
    G1 = '( %s /\\ v e. S )' % C0
    vS = w.s([], 'simpr', '( %s -> v e. S )' % G1)
    vD1 = w.s([w.s([M(sDb, 'S C_ D')], 'adantr', '( %s -> S C_ D )' % G1), vS], 'sseldd', '( %s -> v e. D )' % G1)
    bvne1 = w.s([w.s([w.s([], 'fveq2', '( z = v -> ( b ` z ) = ( b ` v ) )')], 'neeq1d', '( z = v -> ( ( b ` z ) =/= 0 <-> ( b ` v ) =/= 0 ) )'), w.s([M(bne, BNE)], 'adantr', '( %s -> %s )' % (G1, BNE)), vS], 'rspcdva', '( %s -> ( b ` v ) =/= 0 )' % G1)
    bvf1 = w.s([bfacat('v'), w.s([bfac], 'adantr', '( %s -> %s )' % (G1, BFAC)), vD1], 'rspcdva', '( %s -> ( b ` v ) = ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) )' % G1)
    vc1 = w.s([w.s([M(dssb, 'D C_ CC')], 'adantr', '( %s -> D C_ CC )' % G1), vD1], 'sseldd', '( %s -> v e. CC )' % G1)
    vqn1 = w.s([w.s([vc1, w.s([M(qcb, 'Q e. CC')], 'adantr', '( %s -> Q e. CC )' % G1)], 'subcld', '( %s -> ( v - Q ) e. CC )' % G1), w.s([nn0], 'adantr', '( %s -> n e. NN0 )' % G1)], 'expcld', '( %s -> ( ( v - Q ) ^ n ) e. CC )' % G1)
    gv1 = w.s([w.s([gf], 'adantr', '( %s -> g : D --> CC )' % G1), vD1], 'ffvelcdmd', '( %s -> ( g ` v ) e. CC )' % G1)
    gvne1 = w.s([vqn1, gv1, w.s([bvf1, bvne1], 'eqnetrrd', '( %s -> ( ( ( v - Q ) ^ n ) x. ( g ` v ) ) =/= 0 )' % G1)], 'mulne0bbd', '( %s -> ( g ` v ) =/= 0 )' % G1)
    G2 = '( %s /\\ v e. { Q } )' % C0
    veq = w.s([w.s([], 'simpr', '( %s -> v e. { Q } )' % G2), w.s([w.s([], 'vex', 'v e. _V')], 'elsn', '( v e. { Q } <-> v = Q )')], 'sylib', '( %s -> v = Q )' % G2)
    gvne2 = w.s([w.s([veq], 'fveq2d', '( %s -> ( g ` v ) = ( g ` Q ) )' % G2), w.s([gqne], 'adantr', '( %s -> ( g ` Q ) =/= 0 )' % G2)], 'eqnetrd', '( %s -> ( g ` v ) =/= 0 )' % G2)
    gvne = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (G0, C0)), vu], 'jca', '( %s -> ( %s /\\ ( v e. S \\/ v e. { Q } ) ) )' % (G0, C0)), w.s([gvne1, gvne2], 'jaodan', '( ( %s /\\ ( v e. S \\/ v e. { Q } ) ) -> ( g ` v ) =/= 0 )' % C0)], 'syl', '( %s -> ( g ` v ) =/= 0 )' % G0)
    GNV = 'A. v e. %s ( g ` v ) =/= 0' % SU
    GNZ = 'A. z e. %s ( g ` z ) =/= 0' % SU
    f4 = w.s([w.s([gvne], 'ralrimiva', '( %s -> %s )' % (C0, GNV)), w.s([w.s([w.s([], 'fveq2', '( v = z -> ( g ` v ) = ( g ` z ) )')], 'neeq1d', '( v = z -> ( ( g ` v ) =/= 0 <-> ( g ` z ) =/= 0 ) )')], 'cbvralvw', '( %s <-> %s )' % (GNV, GNZ))], 'sylib', '( %s -> %s )' % (C0, GNZ))
    FNEW = FACT(SU, OP, 'g')
    fnew = w.s([f1, hg, w.s([f3, f4], 'jca', '( %s -> ( %s /\\ %s ) )' % (C0, RALZ, GNZ))], '3jca', '( %s -> %s )' % (C0, FNEW))
    opex = w.s([w.s([], 'vex', 'a e. _V'), w.s([], 'snex', '{ <. Q , n >. } e. _V'), w.inst('unexg')], 'mp2an', '%s e. _V' % OP)
    gex = w.s([], 'vex', 'g e. _V')
    spc = w.s([opex, gex, w.s([facsub(w, SU, 'o', 'h', OP, 'g')], 'spc2egv', '( ( %s e. _V /\\ g e. _V ) -> ( %s -> %s ) )' % (OP, FNEW, PS(SU)))], 'mp2an', '( %s -> %s )' % (FNEW, PS(SU)))
    psu = w.s([fnew, spc], 'syl', '( %s -> %s )' % (C0, PS(SU)))
    e1 = w.s([w.s([psu], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (B0, PHIB, PS(SU)))], 'exlimdv', '( ( %s /\\ n e. NN0 ) -> ( E. g %s -> %s ) )' % (B0, PHIB, PS(SU)))
    e2 = w.s([exb, w.s([e1], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (B0, EXB, PS(SU)))], 'mpd', '( %s -> %s )' % (B0, PS(SU)))
    e3 = w.s([w.s([e2], 'ex', '( %s -> ( %s -> %s ) )' % (A0, FSab, PS(SU)))], 'exlimdvv', '( %s -> ( E. a E. b %s -> %s ) )' % (A0, FSab, PS(SU)))
    w.qed([psab, e3], 'mpd', '( %s -> %s )' % (A0, PS(SU)))
    run1(w)

    # ---- holzfac --------------------------------------------------------------------
    w = W('holzfac', 'The factorisation of a holomorphic function over the zeros of a rectangle: F is the product of ( z - r ) ^ ( o ` r ) over the zeros r of the rectangle, with positive integer multiplicities o , times a function holomorphic on the open set and nonzero on the rectangle.')
    A0 = ABNZ
    abg = w.s([], 'simpl', '( %s -> %s )' % (A0, ABGEO))
    d = abgeoctx(w, A0, abg)
    h1 = facsubset(w, 'x', '(/)')
    h2 = facsubset(w, 'x', 's')
    h3 = facsubset(w, 'x', '( s u. { t } )')
    h4 = facsubset(w, 'x', ZS)
    # base: the empty factorisation
    z1 = closed(w, A0, 'f0', '(/) : (/) --> NN')
    A1 = '( %s /\\ z e. D )' % A0
    fz = w.s([w.s([d['ff']], 'adantr', '( %s -> F : D --> CC )' % A1), w.s([], 'simpr', '( %s -> z e. D )' % A1)], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
    p0 = w.s([w.s([w.s([closed(w, A1, 'prod0', '%s = 1' % PR('(/)', '(/)', 'z'))], 'oveq1d', '( %s -> ( %s x. ( F ` z ) ) = ( 1 x. ( F ` z ) ) )' % (A1, PR('(/)', '(/)', 'z'))), w.s([fz], 'mullidd', '( %s -> ( 1 x. ( F ` z ) ) = ( F ` z ) )' % A1)], 'eqtrd',
                  '( %s -> ( %s x. ( F ` z ) ) = ( F ` z ) )' % (A1, PR('(/)', '(/)', 'z')))], 'eqcomd', '( %s -> ( F ` z ) = ( %s x. ( F ` z ) ) )' % (A1, PR('(/)', '(/)', 'z')))
    z3 = w.s([p0], 'ralrimiva', '( %s -> A. z e. D ( F ` z ) = ( %s x. ( F ` z ) ) )' % (A0, PR('(/)', '(/)', 'z')))
    z4 = closed(w, A0, 'ral0', 'A. z e. (/) ( F ` z ) =/= 0')
    F0 = FACT('(/)', '(/)', 'F')
    f0 = w.s([z1, d['hol'], w.s([z3, z4], 'jca', '( %s -> ( A. z e. D ( F ` z ) = ( %s x. ( F ` z ) ) /\\ A. z e. (/) ( F ` z ) =/= 0 ) )' % (A0, PR('(/)', '(/)', 'z')))], '3jca', '( %s -> %s )' % (A0, F0))
    fex = w.s([d['fcn']], 'elexd', '( %s -> F e. _V )' % A0)
    spc0 = w.s([w.s([closed(w, A0, '0ex', '(/) e. _V'), fex], 'jca', '( %s -> ( (/) e. _V /\\ F e. _V ) )' % A0), w.s([facsub(w, '(/)', 'o', 'h', '(/)', 'F')], 'spc2egv', '( ( (/) e. _V /\\ F e. _V ) -> ( %s -> %s ) )' % (F0, PS('(/)')))], 'syl',
               '( %s -> ( %s -> %s ) )' % (A0, F0, PS('(/)')))
    h5 = w.s([f0, spc0], 'mpd', '( %s -> %s )' % (A0, PS('(/)')))
    # step
    SQ = '( s C_ %s /\\ t e. ( %s \\ s ) )' % (ZS, ZS)
    h6 = w.s([w.s([], 'holzfaclem', '( ( %s /\\ %s /\\ %s ) -> %s )' % (ABNZ, SQ, PS('s'), PS('( s u. { t } )')))], '3expia', '( ( %s /\\ %s ) -> ( %s -> %s ) )' % (A0, SQ, PS('s'), PS('( s u. { t } )')))
    h7 = w.s([], 'holzfi', '( %s -> %s e. Fin )' % (A0, ZS))
    pzs = w.s([h1, h2, h3, h4, h5, h6, h7], 'findcard2d', '( %s -> %s )' % (A0, PS(ZS)))
    # nonvanishing on the whole rectangle
    FZ = FACT(ZS, 'o', 'h'); FZab = FACT(ZS, 'a', 'b')
    nfs = [w.s([], 'nfv', 'F/ a %s' % FZ), w.s([], 'nfv', 'F/ b %s' % FZ), w.s([], 'nfv', 'F/ o %s' % FZab), w.s([], 'nfv', 'F/ h %s' % FZab)]
    cbv = w.s(nfs + [facsub(w, ZS, 'o', 'h', 'a', 'b')], 'cbvex2v', '( %s <-> E. a E. b %s )' % (PS(ZS), FZab))
    psab = w.s([pzs, cbv], 'sylib', '( %s -> E. a E. b %s )' % (A0, FZab))
    B0 = '( %s /\\ %s )' % (A0, FZab)
    fac = w.s([], 'simpr', '( %s -> %s )' % (B0, FZab))
    a0b = w.s([], 'simpl', '( %s -> %s )' % (B0, A0))
    def L(st, f):
        return w.s([a0b, st], 'syl', '( %s -> %s )' % (B0, f))
    af = w.s([fac, w.inst('simp1')], 'syl', '( %s -> a : %s --> NN )' % (B0, ZS))
    hb = w.s([fac, w.inst('simp2')], 'syl', '( %s -> %s )' % (B0, HOLG('b')))
    PRID = 'A. z e. D ( F ` z ) = ( %s x. ( b ` z ) )' % PR(ZS, 'a', 'z')
    BNE = 'A. z e. %s ( b ` z ) =/= 0' % ZS
    pr2 = w.s([fac, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (B0, PRID, BNE))
    prid = w.s([pr2, w.inst('simpl')], 'syl', '( %s -> %s )' % (B0, PRID))
    bne = w.s([pr2, w.inst('simpr')], 'syl', '( %s -> %s )' % (B0, BNE))
    bf = w.s([w.s([hb, w.inst('simpl')], 'syl', '( %s -> b e. ( D -cn-> CC ) )' % B0), w.inst('cncff')], 'syl', '( %s -> b : D --> CC )' % B0)
    rd = L(w.s([d['han'], w.inst('holnss')], 'syl', '( %s -> %s C_ D )' % (A0, RECT)), '%s C_ D' % RECT)
    zsfi = L(h7, '%s e. Fin' % ZS)
    zscc = L(w.s([closed(w, A0, 'ssrab2', '%s C_ %s' % (ZS, RECT)), d['crss']], 'sstrd', '( %s -> %s C_ CC )' % (A0, ZS)), '%s C_ CC' % ZS)
    C1 = '( %s /\\ v e. %s )' % (B0, RECT)
    vin = w.s([], 'simpr', '( %s -> v e. %s )' % (C1, RECT))
    vD = w.s([w.s([rd], 'adantr', '( %s -> %s C_ D )' % (C1, RECT)), vin], 'sseldd', '( %s -> v e. D )' % C1)
    vc = w.s([w.s([L(d['dss'], 'D C_ CC')], 'adantr', '( %s -> D C_ CC )' % C1), vD], 'sseldd', '( %s -> v e. CC )' % C1)
    C2 = '( %s /\\ v e. %s )' % (C1, ZS)
    bne2 = w.s([w.s([w.s([], 'fveq2', '( z = v -> ( b ` z ) = ( b ` v ) )')], 'neeq1d', '( z = v -> ( ( b ` z ) =/= 0 <-> ( b ` v ) =/= 0 ) )'), w.s([bne], 'ad2antrr', '( %s -> %s )' % (C2, BNE)), w.s([], 'simpr', '( %s -> v e. %s )' % (C2, ZS))], 'rspcdva', '( %s -> ( b ` v ) =/= 0 )' % C2)
    C3 = '( %s /\\ -. v e. %s )' % (C1, ZS)
    elz = w.s([w.s([w.s([w.s([], 'fveq2', '( r = v -> ( F ` r ) = ( F ` v ) )')], 'eqeq1d', '( r = v -> ( ( F ` r ) = 0 <-> ( F ` v ) = 0 ) )')], 'elrab', '( v e. %s <-> ( v e. %s /\\ ( F ` v ) = 0 ) )' % (ZS, RECT))], 'a1i', '( %s -> ( v e. %s <-> ( v e. %s /\\ ( F ` v ) = 0 ) ) )' % (C1, ZS, RECT))
    elz2 = w.s([elz, w.s([vin, w.inst('ibar')], 'syl', '( %s -> ( ( F ` v ) = 0 <-> ( v e. %s /\\ ( F ` v ) = 0 ) ) )' % (C1, RECT))], 'bitr4d', '( %s -> ( v e. %s <-> ( F ` v ) = 0 ) )' % (C1, ZS))
    fvne = w.s([w.s([w.s([], 'simpr', '( %s -> -. v e. %s )' % (C3, ZS)), w.s([w.s([elz2], 'notbid', '( %s -> ( -. v e. %s <-> -. ( F ` v ) = 0 ) )' % (C1, ZS))], 'adantr', '( %s -> ( -. v e. %s <-> -. ( F ` v ) = 0 ) )' % (C3, ZS))], 'mpbid', '( %s -> -. ( F ` v ) = 0 )' % C3)], 'neqned', '( %s -> ( F ` v ) =/= 0 )' % C3)
    fv = w.s([pridat(w, ZS, 'a', 'b', 'v'), w.s([prid], 'adantr', '( %s -> %s )' % (C1, PRID)), vD], 'rspcdva', '( %s -> ( F ` v ) = ( %s x. ( b ` v ) ) )' % (C1, PR(ZS, 'a', 'v')))
    prcv, _, _, _ = prodcl(w, C1, ZS, 'a', 'v', w.s([zsfi], 'adantr', '( %s -> %s e. Fin )' % (C1, ZS)), w.s([zscc], 'adantr', '( %s -> %s C_ CC )' % (C1, ZS)), w.s([af], 'adantr', '( %s -> a : %s --> NN )' % (C1, ZS)), vc)
    prcvq = w.s([w.s([prcq(w, ZS, 'a', 'v')], 'a1i', '( %s -> %s = %s )' % (C1, PR(ZS, 'a', 'v'), PR(ZS, 'a', 'v', 'c'))), prcv], 'eqeltrd', '( %s -> %s e. CC )' % (C1, PR(ZS, 'a', 'v')))
    bv = w.s([w.s([bf], 'adantr', '( %s -> b : D --> CC )' % C1), vD], 'ffvelcdmd', '( %s -> ( b ` v ) e. CC )' % C1)
    bne3 = w.s([w.s([prcvq], 'adantr', '( %s -> %s e. CC )' % (C3, PR(ZS, 'a', 'v'))), w.s([bv], 'adantr', '( %s -> ( b ` v ) e. CC )' % C3), w.s([w.s([fv], 'adantr', '( %s -> ( F ` v ) = ( %s x. ( b ` v ) ) )' % (C3, PR(ZS, 'a', 'v'))), fvne], 'eqnetrrd', '( %s -> ( %s x. ( b ` v ) ) =/= 0 )' % (C3, PR(ZS, 'a', 'v')))], 'mulne0bbd',
               '( %s -> ( b ` v ) =/= 0 )' % C3)
    bvne = w.s([bne2, bne3], 'pm2.61dan', '( %s -> ( b ` v ) =/= 0 )' % C1)
    BNV = 'A. v e. %s ( b ` v ) =/= 0' % RECT
    BNR = 'A. z e. %s ( b ` z ) =/= 0' % RECT
    bnr = w.s([w.s([bvne], 'ralrimiva', '( %s -> %s )' % (B0, BNV)), w.s([w.s([w.s([], 'fveq2', '( v = z -> ( b ` v ) = ( b ` z ) )')], 'neeq1d', '( v = z -> ( ( b ` v ) =/= 0 <-> ( b ` z ) =/= 0 ) )')], 'cbvralvw', '( %s <-> %s )' % (BNV, BNR))], 'sylib', '( %s -> %s )' % (B0, BNR))
    FR_ = FACT(ZS, 'a', 'b', RECT)
    fr = w.s([af, hb, w.s([prid, bnr], 'jca', '( %s -> ( %s /\\ %s ) )' % (B0, PRID, BNR))], '3jca', '( %s -> %s )' % (B0, FR_))
    spc = w.s([w.s([], 'vex', 'a e. _V'), w.s([], 'vex', 'b e. _V'), w.s([facsub(w, ZS, 'o', 'h', 'a', 'b', RECT)], 'spc2egv', '( ( a e. _V /\\ b e. _V ) -> ( %s -> %s ) )' % (FR_, PS(ZS, RECT)))], 'mp2an', '( %s -> %s )' % (FR_, PS(ZS, RECT)))
    e2 = w.s([fr, spc], 'syl', '( %s -> %s )' % (B0, PS(ZS, RECT)))
    e3 = w.s([w.s([e2], 'ex', '( %s -> ( %s -> %s ) )' % (A0, FZab, PS(ZS, RECT)))], 'exlimdvv', '( %s -> ( E. a E. b %s -> %s ) )' % (A0, FZab, PS(ZS, RECT)))
    w.qed([psab, e3], 'mpd', '( %s -> %s )' % (A0, PS(ZS, RECT)))
    run1(w)
