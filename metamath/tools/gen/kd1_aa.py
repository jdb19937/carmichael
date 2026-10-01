"""Sortie KD1: the far-zero tail of the order-( J + 2 ) pole sum (kdfar)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_far():
    w = W('kdfar', 'Lean ` KDerivDetect.norm_sum_far_le ` : zeros at distance more than ` R ` from ` S ` contribute at most ` A / R ^ J ` to the order- ` ( J + 2 ) ` pole sum, ` A ` any bound for the ` l2 ` sum (the far set any ` Y C_ ZD ` ).')
    A0 = S['kdfar'].split(' -> ( abs ` sum_')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L = lambda st, a: lift(w, st, a)
    top = top_and(A0)
    g1 = s([], 'simpl', top[0]); g2 = s([], 'simpr', top[1])
    p1 = top_and(top[0])
    ctr = s([g1], 'simp1d', p1[0]); spos = s([g1], 'simp2d', p1[1]); yrf = s([g1], 'simp3d', p1[2])
    chi = s([ctr], 'simpld', CHI); tr = s([ctr], 'simprd', 'T e. RR')
    sc = s([spos], 'simpld', 'S e. CC'); POS = top_and(p1[1])[1]; pos = s([spos], 'simprd', POS)
    ysub = s([yrf], 'simp1d', 'Y C_ %s' % ZD()); rp = s([yrf], 'simp2d', 'R e. RR+'); FAR = top_and(p1[2])[2]; far = s([yrf], 'simp3d', FAR)
    p2 = top_and(top[1])
    jj = s([g2], 'simp1d', 'J e. NN0'); ar = s([g2], 'simp2d', 'A e. RR'); hA = s([g2], 'simp3d', p2[2])
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0]); zord = s([lz], 'simp2d', top_and(lzc)[1])
    yfin = s([zfin, ysub], 'ssfid', 'Y e. Fin')
    M_ = MU('q'); D_ = '( abs ` ( S - q ) )'; DQ = '( S - q )'
    def zfacts(ante, qz):
        a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        mn = a([qz, a([L(zord, ante), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (ZD(), M_))], 'mpd', '%s e. NN' % M_)
        cp = w.s([w.s([w.s([w.s([], 'oveq2', '( p = q -> ( S - p ) = ( S - q ) )')], 'fveq2d', '( p = q -> ( abs ` ( S - p ) ) = %s )' % D_)], 'breq2d', '( p = q -> ( 0 < ( abs ` ( S - p ) ) <-> 0 < %s ) )' % D_)], 'rspcv',
                 '( q e. %s -> ( %s -> 0 < %s ) )' % (ZD(), POS, D_))
        dpos = a([qz, L(pos, ante), cp], 'sylc', '0 < %s' % D_)
        SQ13 = SQ(CT('T'), R138)
        RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
        cq = Closure(w, ante, {'T': ('RR', L(tr, ante))})
        cct = a([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % ante), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante), a([L(tr, ante)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
                'addcld', '%s e. CC' % CT('T'))
        ric = a([a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante), a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
                'addcld', '%s e. CC' % RI_)
        sqcc = a([a([a([cct, ric], 'subcld', '%s e. CC' % A13), a([cct, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
        qc = a([sqcc, a([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (ante, ZD(), SQ13)), qz], 'sseldd', 'q e. %s' % SQ13)], 'sseldd', 'q e. CC')
        dq = a([L(sc, ante), qc], 'subcld', '%s e. CC' % DQ)
        dne = a([a([a([dpos], 'gt0ne0d', '%s =/= 0' % D_), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % ante)], 'neeqtrrd', '%s =/= ( abs ` 0 )' % D_),
                 w.s([w.s([], 'fveq2', '( %s = 0 -> %s = ( abs ` 0 ) )' % (DQ, D_))], 'necon3i', '( %s =/= ( abs ` 0 ) -> %s =/= 0 )' % (D_, DQ))], 'syl', '%s =/= 0' % DQ)
        return dict(mn=mn, dpos=dpos, qc=qc, dq=dq, dne=dne)
    # Z-terms
    Az = '( %s /\\ q e. %s )' % (A0, ZD())
    az = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    fz = zfacts(Az, az([], 'simpr', 'q e. %s' % ZD()))
    D2 = '( %s ^ 2 )' % D_
    d2p = az([az([fz['dq'], fz['dne']], 'absrpcld', '%s e. RR+' % D_), w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % Az)], 'rpexpcld', '%s e. RR+' % D2)
    tZ = '( %s / %s )' % (M_, D2)
    tzr = az([az([fz['mn']], 'nnred', '%s e. RR' % M_), d2p], 'rerpdivcld', '%s e. RR' % tZ)
    tz0 = az([az([fz['mn']], 'nnred', '%s e. RR' % M_), d2p, az([az([fz['mn']], 'nnrpd', '%s e. RR+' % M_)], 'rpge0d', '0 <_ %s' % M_)], 'T.', 'T.') if False else \
        az([az([az([fz['mn']], 'nnrpd', '%s e. RR+' % M_), d2p], 'rpdivcld', '%s e. RR+' % tZ)], 'rpge0d', '0 <_ %s' % tZ)
    # Y-terms
    Ay = '( %s /\\ q e. Y )' % A0
    ay = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ay, f))
    qy = ay([], 'simpr', 'q e. Y')
    qzy = ay([L(ysub, Ay), qy], 'sseldd', 'q e. %s' % ZD())
    fy = zfacts(Ay, qzy)
    cf = w.s([w.s([w.s([w.s([], 'oveq2', '( p = q -> ( S - p ) = ( S - q ) )')], 'fveq2d', '( p = q -> ( abs ` ( S - p ) ) = %s )' % D_)], 'breq2d', '( p = q -> ( R < ( abs ` ( S - p ) ) <-> R < %s ) )' % D_)], 'rspcv',
             '( q e. Y -> ( %s -> R < %s ) )' % (FAR, D_))
    rlt = ay([qy, L(far, Ay), cf], 'sylc', 'R < %s' % D_)
    TT = '( %s / ( %s ^ ( J + 2 ) ) )' % (M_, DQ)
    j2 = ay([L(jj, Ay), w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % Ay)], 'nn0addcld', '( J + 2 ) e. NN0')
    ttc = ay([ay([fy['mn']], 'nncnd', '%s e. CC' % M_), ay([fy['dq'], j2], 'expcld', '( %s ^ ( J + 2 ) ) e. CC' % DQ), ay([fy['dq'], fy['dne'], ay([j2], 'nn0zd', '( J + 2 ) e. ZZ')], 'expne0d', '( %s ^ ( J + 2 ) ) =/= 0' % DQ)],
             'divcld', '%s e. CC' % TT)
    at1 = ay([ay([fy['mn']], 'nncnd', '%s e. CC' % M_), ay([fy['dq'], j2], 'expcld', '( %s ^ ( J + 2 ) ) e. CC' % DQ), ay([fy['dq'], fy['dne'], ay([j2], 'nn0zd', '( J + 2 ) e. ZZ')], 'expne0d', '( %s ^ ( J + 2 ) ) =/= 0' % DQ)],
             'absdivd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` ( %s ^ ( J + 2 ) ) ) )' % (TT, M_, DQ))
    at2 = ay([ay([ay([fy['mn']], 'nnred', '%s e. RR' % M_), ay([ay([fy['mn']], 'nnrpd', '%s e. RR+' % M_)], 'rpge0d', '0 <_ %s' % M_)], 'absidd', '( abs ` %s ) = %s' % (M_, M_)),
              ay([fy['dq'], j2], 'absexpd', '( abs ` ( %s ^ ( J + 2 ) ) ) = ( %s ^ ( J + 2 ) )' % (DQ, D_))], 'oveq12d', '( ( abs ` %s ) / ( abs ` ( %s ^ ( J + 2 ) ) ) ) = ( %s / ( %s ^ ( J + 2 ) ) )' % (M_, DQ, M_, D_))
    dc_ = ay([fy['dq']], 'abscld', '%s e. RR' % D_); dcc = ay([dc_], 'recnd', '%s e. CC' % D_)
    ex = ay([dcc, L(jj, Ay), w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % Ay)], 'expaddd', '( %s ^ ( J + 2 ) ) = ( ( %s ^ J ) x. %s )' % (D_, D_, D2))
    at3 = ay([ex], 'oveq2d', '( %s / ( %s ^ ( J + 2 ) ) ) = ( %s / ( ( %s ^ J ) x. %s ) )' % (M_, D_, M_, D_, D2))
    dp_ = ay([fy['dq'], fy['dne']], 'absrpcld', '%s e. RR+' % D_)
    djp = ay([dp_, ay([L(jj, Ay)], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( %s ^ J ) e. RR+' % D_)
    d2py = ay([dp_, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % Ay)], 'rpexpcld', '%s e. RR+' % D2)
    mcc = ay([fy['mn']], 'nncnd', '%s e. CC' % M_)
    at4 = ay([mcc, ay([d2py], 'rpcnd', '%s e. CC' % D2), ay([djp], 'rpcnd', '( %s ^ J ) e. CC' % D_), ay([d2py], 'rpne0d', '%s =/= 0' % D2), ay([djp], 'rpne0d', '( %s ^ J ) =/= 0' % D_)], 'divdiv1d',
             '( ( %s / %s ) / ( %s ^ J ) ) = ( %s / ( %s x. ( %s ^ J ) ) )' % (M_, D2, D_, M_, D2, D_))
    mc_ = ay([ay([d2py], 'rpcnd', '%s e. CC' % D2), ay([djp], 'rpcnd', '( %s ^ J ) e. CC' % D_)], 'mulcomd', '( %s x. ( %s ^ J ) ) = ( ( %s ^ J ) x. %s )' % (D2, D_, D_, D2))
    at5 = ay([at4, ay([mc_], 'oveq2d', '( %s / ( %s x. ( %s ^ J ) ) ) = ( %s / ( ( %s ^ J ) x. %s ) )' % (M_, D2, D_, M_, D_, D2))], 'eqtrd',
             '( ( %s / %s ) / ( %s ^ J ) ) = ( %s / ( ( %s ^ J ) x. %s ) )' % (M_, D2, D_, M_, D_, D2))
    at = ay([at1, at2, at3], '3eqtrd', '( abs ` %s ) = ( %s / ( ( %s ^ J ) x. %s ) )' % (TT, M_, D_, D2))
    at6 = ay([at, at5], 'eqtr4d', '( abs ` %s ) = ( ( %s / %s ) / ( %s ^ J ) )' % (TT, M_, D2, D_))
    rr = L(s([rp], 'rpred', 'R e. RR'), Ay); r0 = L(s([rp], 'rpge0d', '0 <_ R'), Ay)
    rjp = ay([L(rp, Ay), ay([L(jj, Ay)], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( R ^ J ) e. RR+')
    le1 = ay([rr, dc_, L(jj, Ay), r0, ay([rr, dc_, rlt], 'ltled', 'R <_ %s' % D_)], 'leexp1ad', '( R ^ J ) <_ ( %s ^ J )' % D_)
    tzy = ay([ay([fy['mn']], 'nnred', '%s e. RR' % M_), d2py], 'rerpdivcld', '%s e. RR' % tZ)
    tzy0 = ay([ay([ay([fy['mn']], 'nnrpd', '%s e. RR+' % M_), d2py], 'rpdivcld', '%s e. RR+' % tZ)], 'rpge0d', '0 <_ %s' % tZ)
    le2 = ay([rjp, djp, tzy, tzy0, le1], 'lediv2ad', '( %s / ( %s ^ J ) ) <_ ( %s / ( R ^ J ) )' % (tZ, D_, tZ))
    IR = '( 1 / ( R ^ J ) )'
    dr = ay([ay([tzy], 'recnd', '%s e. CC' % tZ), ay([rjp], 'rpcnd', '( R ^ J ) e. CC'), ay([rjp], 'rpne0d', '( R ^ J ) =/= 0')], 'divrec2d', '( %s / ( R ^ J ) ) = ( %s x. %s )' % (tZ, IR, tZ))
    tb = ay([ay([at6, le2], 'eqbrtrd', '( abs ` %s ) <_ ( %s / ( R ^ J ) )' % (TT, tZ)), dr], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (TT, IR, tZ))
    # sums
    irr = s([s([rp, s([jj], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( R ^ J ) e. RR+')], 'rpreccld', '%s e. RR+' % IR)
    iyz = ay([L(s([irr], 'rpred', '%s e. RR' % IR), Ay), tzy], 'remulcld', '( %s x. %s ) e. RR' % (IR, tZ))
    SY = 'sum_ q e. Y %s' % TT
    s1 = s([yfin, ttc], 'fsumabs', '( abs ` %s ) <_ sum_ q e. Y ( abs ` %s )' % (SY, TT))
    s2 = s([yfin, ay([ttc], 'abscld', '( abs ` %s ) e. RR' % TT), iyz, tb], 'fsumle', 'sum_ q e. Y ( abs ` %s ) <_ sum_ q e. Y ( %s x. %s )' % (TT, IR, tZ))
    s3 = s([yfin, s([irr], 'rpcnd', '%s e. CC' % IR), ay([tzy], 'recnd', '%s e. CC' % tZ)], 'fsummulc2', '( %s x. sum_ q e. Y %s ) = sum_ q e. Y ( %s x. %s )' % (IR, tZ, IR, tZ))
    s4 = s([zfin, tzr, tz0, ysub], 'fsumless', 'sum_ q e. Y %s <_ sum_ q e. %s %s' % (tZ, ZD(), tZ))
    syr = s([yfin, tzy], 'fsumrecl', 'sum_ q e. Y %s e. RR' % tZ)
    szr = s([zfin, tzr], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (ZD(), tZ))
    idqp = w.s([], 'id', '( q = p -> q = p )')
    cqp, nqp = w.congr(tZ, {'q': 'p'}, 'q = p', {'q': idqp})
    cbz = w.s([cqp], 'cbvsumv', 'sum_ q e. %s %s = sum_ p e. %s %s' % (ZD(), tZ, ZD(), nqp))
    hA = s([w.s([cbz], 'a1i', '( %s -> sum_ q e. %s %s = sum_ p e. %s %s )' % (A0, ZD(), tZ, ZD(), nqp)), hA], 'eqbrtrd', 'sum_ q e. %s %s <_ A' % (ZD(), tZ))
    s5 = s([syr, ar, s([s4, hA], 'T.', 'T.') if False else s([syr, szr, ar, s4, hA], 'letrd', 'sum_ q e. Y %s <_ A' % tZ), s([irr], 'rpred', '%s e. RR' % IR), s([irr], 'rpge0d', '0 <_ %s' % IR)][0:2] +
           [s([irr], 'rpred', '%s e. RR' % IR), s([irr], 'rpge0d', '0 <_ %s' % IR), s([syr, szr, ar, s4, hA], 'letrd', 'sum_ q e. Y %s <_ A' % tZ)], 'lemul2ad', '( %s x. sum_ q e. Y %s ) <_ ( %s x. A )' % (IR, tZ, IR))
    s6 = s([ar, s([rp, s([jj], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( R ^ J ) e. RR+')] and [s([ar], 'recnd', 'A e. CC'), s([s([rp, s([jj], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( R ^ J ) e. RR+')], 'rpcnd', '( R ^ J ) e. CC'),
                                                                                    s([s([rp, s([jj], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( R ^ J ) e. RR+')], 'rpne0d', '( R ^ J ) =/= 0')], 'divrec2d', '( A / ( R ^ J ) ) = ( %s x. A )' % IR)
    aSY = s([s([yfin, ttc], 'fsumcl', '%s e. CC' % SY)], 'abscld', '( abs ` %s ) e. RR' % SY)
    sab = s([yfin, ay([ttc], 'abscld', '( abs ` %s ) e. RR' % TT)], 'fsumrecl', 'sum_ q e. Y ( abs ` %s ) e. RR' % TT)
    siz = s([yfin, iyz], 'fsumrecl', 'sum_ q e. Y ( %s x. %s ) e. RR' % (IR, tZ))
    c1 = s([aSY, sab, siz, s1, s2], 'letrd', '( abs ` %s ) <_ sum_ q e. Y ( %s x. %s )' % (SY, IR, tZ))
    c2 = s([c1, s([s3, s5], 'eqbrtrrd', 'sum_ q e. Y ( %s x. %s ) <_ ( %s x. A )' % (IR, tZ, IR))], 'T.', 'T.') if False else None
    c2 = s([aSY, siz, s([s([irr], 'rpred', '%s e. RR' % IR), ar], 'remulcld', '( %s x. A ) e. RR' % IR), c1, s([s3, s5], 'eqbrtrrd', 'sum_ q e. Y ( %s x. %s ) <_ ( %s x. A )' % (IR, tZ, IR))], 'letrd',
           '( abs ` %s ) <_ ( %s x. A )' % (SY, IR))
    fin = s([c2, s6], 'breqtrrd', '( abs ` %s ) <_ ( A / ( R ^ J ) )' % SY)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdfar']))
    return run(w)




if __name__ == '__main__':
    gen_far()
