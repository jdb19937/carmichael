"""Sortie ZBV2, section 1 part B: the partial sums C ( x , m ) = sum_ n <= m ( mmu n / n ) log ( x / n ).

bvcshift  ( ( ( X e. RR+ /\\ Z e. RR+ ) /\\ K e. NN ) -> CS(X,K) = ( CS(Z,K) + ( log ( X / Z ) x. AS(K) ) ) )
bvcp1     ( K e. NN -> CS(K+1,K+1) = ( CS(K,K) + ( ELL(K) x. AS(K) ) ) )
bvc1      CS(1,1) = 0
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *


def bvcshift():
    w = W('bvcshift', 'Shifting the argument of C ( x , m ) = sum_ n <= m ( mmu n / n ) log ( x / n ): '
                      'C ( X , K ) = C ( Z , K ) + log ( X / Z ) sum_ n <= K ( mmu n / n ).')
    A = '( ( X e. RR+ /\\ Z e. RR+ ) /\\ K e. NN )'
    st = mkst(w, A)
    xrp = st([st([], 'simpl', '( X e. RR+ /\\ Z e. RR+ )')], 'simpld', 'X e. RR+'); zrp = st([st([], 'simpl', '( X e. RR+ /\\ Z e. RR+ )')], 'simprd', 'Z e. RR+')
    AN = '( %s /\\ n e. ( 1 ... K ) )' % A
    sn = mkst(w, AN)
    nnn = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... K )'), 'elfznn', 'n e. NN')
    mf = mqfacts(w, AN, nnn, 'n')
    nrp = sn([nnn], 'nnrpd', 'n e. RR+')
    xn = lift(w, xrp, AN); zn = lift(w, zrp, AN)
    LX, LZ, LN = '( log ` X )', '( log ` Z )', '( log ` n )'
    lxr = sn([xn], 'relogcld', '%s e. RR' % LX); lzr = sn([zn], 'relogcld', '%s e. RR' % LZ); lnr = sn([nrp], 'relogcld', '%s e. RR' % LN)
    d1 = sy2(w, AN, xn, nrp, 'relogdiv', '( log ` ( X / n ) ) = ( %s - %s )' % (LX, LN))
    d2 = sy2(w, AN, zn, nrp, 'relogdiv', '( log ` ( Z / n ) ) = ( %s - %s )' % (LZ, LN))
    d3 = sy2(w, AN, xn, zn, 'relogdiv', '( log ` ( X / Z ) ) = ( %s - %s )' % (LX, LZ))
    T1 = '( %s x. ( log ` ( X / n ) ) )' % MQ('n'); T2 = '( %s x. ( log ` ( Z / n ) ) )' % MQ('n'); T3 = '( ( log ` ( X / Z ) ) x. %s )' % MQ('n')
    r1, t1 = w.rewrite(T1, {'( log ` ( X / n ) )': ('( %s - %s )' % (LX, LN), d1)}, AN)
    r2, t2 = w.rewrite(T2, {'( log ` ( Z / n ) )': ('( %s - %s )' % (LZ, LN), d2)}, AN)
    r3, t3 = w.rewrite(T3, {'( log ` ( X / Z ) )': ('( %s - %s )' % (LX, LZ), d3)}, AN)
    idn = lineq(w, AN, t1, '( %s + %s )' % (t2, t3), leaves={MQ('n'): mf['mqr'], LX: lxr, LZ: lzr, LN: lnr}, products=True)
    term = sn([sn([r1, idn], 'eqtrd', '%s = ( %s + %s )' % (T1, t2, t3)), sn([r2, r3], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (t2, t3, T2, T3))], 'eqtr4d' if False else 'eqtrd',
              '%s = ( %s + %s )' % (T1, T2, T3)) if False else None
    # T1 = t1 = t2 + t3 = T2 + T3
    e23 = sn([sn([r2], 'eqcomd', '%s = %s' % (t2, T2)), sn([r3], 'eqcomd', '%s = %s' % (t3, T3))], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (t2, t3, T2, T3))
    term = sn([sn([r1, idn], 'eqtrd', '%s = ( %s + %s )' % (T1, t2, t3)), e23], 'eqtrd', '%s = ( %s + %s )' % (T1, T2, T3))
    fin = st([], 'fzfid', '( 1 ... K ) e. Fin')
    lzn = sn([sn([zn, nrp], 'rpdivcld', '( Z / n ) e. RR+')], 'relogcld', '( log ` ( Z / n ) ) e. RR')
    t2c = sn([sn([mf['mqr'], lzn], 'remulcld', '%s e. RR' % T2)], 'recnd', '%s e. CC' % T2)
    lxzr = st([st([xrp, zrp], 'rpdivcld', '( X / Z ) e. RR+')], 'relogcld', '( log ` ( X / Z ) ) e. RR'); lxzc = st([lxzr], 'recnd', '( log ` ( X / Z ) ) e. CC')
    t3c = sn([sn([lift(w, lxzr, AN), mf['mqr']], 'remulcld', '%s e. RR' % T3)], 'recnd', '%s e. CC' % T3)
    s1 = st([term], 'sumeq2dv', '%s = sum_ n e. ( 1 ... K ) ( %s + %s )' % (CS('X', 'K'), T2, T3))
    s2 = st([fin, t2c, t3c], 'fsumadd', 'sum_ n e. ( 1 ... K ) ( %s + %s ) = ( %s + sum_ n e. ( 1 ... K ) %s )' % (T2, T3, CS('Z', 'K'), T3))
    s3 = st([fin, lxzc, mf['mqc']], 'fsummulc2', '( ( log ` ( X / Z ) ) x. %s ) = sum_ n e. ( 1 ... K ) %s' % (AS('K'), T3))
    s4 = st([st([s3], 'eqcomd', 'sum_ n e. ( 1 ... K ) %s = ( ( log ` ( X / Z ) ) x. %s )' % (T3, AS('K')))], 'oveq2d',
            '( %s + sum_ n e. ( 1 ... K ) %s ) = ( %s + ( ( log ` ( X / Z ) ) x. %s ) )' % (CS('Z', 'K'), T3, CS('Z', 'K'), AS('K')))
    w.qed([st([s1, s2], 'eqtrd', '%s = ( %s + sum_ n e. ( 1 ... K ) %s )' % (CS('X', 'K'), CS('Z', 'K'), T3)), s4], 'eqtrd',
          '( %s -> %s = ( %s + ( ( log ` ( X / Z ) ) x. %s ) ) )' % (A, CS('X', 'K'), CS('Z', 'K'), AS('K')))
    return w


def bvcp1():
    w = W('bvcp1', 'The recursion of C ( K , K ): C ( K + 1 , K + 1 ) = C ( K , K ) + log ( ( K + 1 ) / K ) sum_ n <= K ( mmu n / n ) '
                   '(the term n = K + 1 vanishes; then bvcshift).')
    A = 'K e. NN'
    st = mkst(w, A)
    kf = kfacts(w, A, st([], 'id', A), 'K')
    K1 = P1('K')
    uz = st([kf['p1nn'], st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', '%s e. ( ZZ>= ` 1 )' % K1)
    AN = '( %s /\\ n e. ( 1 ... %s ) )' % (A, K1)
    sn = mkst(w, AN)
    nnn = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... %s )' % K1), 'elfznn', 'n e. NN')
    mf = mqfacts(w, AN, nnn, 'n')
    nrp = sn([nnn], 'nnrpd', 'n e. RR+')
    BODY = '( %s x. ( log ` ( %s / n ) ) )' % (MQ('n'), K1)
    lr = sn([sn([lift(w, kf['p1rp'], AN), nrp], 'rpdivcld', '( %s / n ) e. RR+' % K1)], 'relogcld', '( log ` ( %s / n ) ) e. RR' % K1)
    bc = sn([sn([mf['mqr'], lr], 'remulcld', '%s e. RR' % BODY)], 'recnd', '%s e. CC' % BODY)
    idn = w.s([], 'id', '( n = %s -> n = %s )' % (K1, K1))
    sub, B = w.congr(BODY, {'n': K1}, 'n = %s' % K1, {'n': idn})
    m1 = st([uz, bc, sub], 'fsumm1', '%s = ( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + %s )' % (CS(K1, K1), K1, BODY, B))
    pc = st([kf['cc'], st([], '1cnd', '1 e. CC')], 'pncand', '( %s - 1 ) = K' % K1)
    rng = st([st([st([pc], 'oveq2d', '( 1 ... ( %s - 1 ) ) = ( 1 ... K )' % K1)], 'sumeq1d', 'sum_ n e. ( 1 ... ( %s - 1 ) ) %s = %s' % (K1, BODY, CS(K1, 'K')))], 'id',
             'sum_ n e. ( 1 ... ( %s - 1 ) ) %s = %s' % (K1, BODY, CS(K1, 'K'))) if False else st([st([pc], 'oveq2d', '( 1 ... ( %s - 1 ) ) = ( 1 ... K )' % K1)], 'sumeq1d', 'sum_ n e. ( 1 ... ( %s - 1 ) ) %s = %s' % (K1, BODY, CS(K1, 'K')))
    # B = MQ(K+1) x. log ( ( K + 1 ) / ( K + 1 ) ) = 0
    dv = st([kf['p1cc'], st([kf['p1rp']], 'rpne0d', '%s =/= 0' % K1)], 'dividd', '( %s / %s ) = 1' % (K1, K1))
    l0 = st([st([dv], 'fveq2d', '( log ` ( %s / %s ) ) = ( log ` 1 )' % (K1, K1)), st([clo(w, 'log1', '( log ` 1 ) = 0')], 'a1i', '( log ` 1 ) = 0')], 'eqtrd', '( log ` ( %s / %s ) ) = 0' % (K1, K1))
    mf1 = mqfacts(w, A, kf['p1nn'], K1)
    b0 = st([st([l0], 'oveq2d', '%s = ( %s x. 0 )' % (B, MQ(K1))), st([mf1['mqc']], 'mul01d', '( %s x. 0 ) = 0' % MQ(K1))], 'eqtrd', '%s = 0' % B)
    csr = st([st([], 'fzfid', '( 1 ... K ) e. Fin'), None], 'x', 'y') if False else None
    ANK = '( %s /\\ n e. ( 1 ... K ) )' % A
    sk = mkst(w, ANK)
    nnk = sy(w, ANK, sk([], 'simpr', 'n e. ( 1 ... K )'), 'elfznn', 'n e. NN')
    mfk = mqfacts(w, ANK, nnk, 'n')
    lrk = sk([sk([lift(w, kf['p1rp'], ANK), sk([nnk], 'nnrpd', 'n e. RR+')], 'rpdivcld', '( %s / n ) e. RR+' % K1)], 'relogcld', '( log ` ( %s / n ) ) e. RR' % K1)
    csc = st([st([], 'fzfid', '( 1 ... K ) e. Fin'), sk([sk([mfk['mqr'], lrk], 'remulcld', '%s e. RR' % BODY)], 'recnd', '%s e. CC' % BODY)], 'fsumcl', '%s e. CC' % CS(K1, 'K'))
    m2 = st([st([rng, b0], 'oveq12d', '( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + %s ) = ( %s + 0 )' % (K1, BODY, B, CS(K1, 'K'))), st([csc], 'addridd', '( %s + 0 ) = %s' % (CS(K1, 'K'), CS(K1, 'K')))], 'eqtrd',
            '( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + %s ) = %s' % (K1, BODY, B, CS(K1, 'K')))
    sh = st([bind(w, A, bind(w, A, kf['p1rp'], kf['rp'], '%s e. RR+' % K1, 'K e. RR+'), st([], 'id', A), '( %s e. RR+ /\\ K e. RR+ )' % K1, A), w.inst('bvcshift')], 'syl',
            '%s = ( %s + ( %s x. %s ) )' % (CS(K1, 'K'), CS('K', 'K'), ELL('K'), AS('K')))
    w.qed([st([m1, m2], 'eqtrd', '%s = %s' % (CS(K1, K1), CS(K1, 'K'))), sh], 'eqtrd', '( %s -> %s = ( %s + ( %s x. %s ) ) )' % (A, CS(K1, K1), CS('K', 'K'), ELL('K'), AS('K')))
    return w


def bvc1():
    w = W('bvc1', 'C ( 1 , 1 ) = 0: the single term is ( mmu 1 / 1 ) log 1.')
    BODY = '( %s x. ( log ` ( 1 / n ) ) )' % MQ('n')
    idn = w.s([], 'id', '( n = 1 -> n = 1 )')
    sub, B = w.congr(BODY, {'n': '1'}, 'n = 1', {'n': idn})
    l0 = w.s([w.s([clo(w, '1div1e1', '( 1 / 1 ) = 1')], 'fveq2i', '( log ` ( 1 / 1 ) ) = ( log ` 1 )'), clo(w, 'log1', '( log ` 1 ) = 0')], 'eqtri', '( log ` ( 1 / 1 ) ) = 0')
    mu1 = w.s([w.s([clo(w, 'muone', '( mmu ` 1 ) = 1')], 'oveq1i', '( ( mmu ` 1 ) / 1 ) = ( 1 / 1 )'), clo(w, '1div1e1', '( 1 / 1 ) = 1')], 'eqtri', '%s = 1' % MQ('1'))
    b1 = w.s([mu1, l0], 'oveq12i', '%s = ( 1 x. 0 )' % B)
    b0 = w.s([b1, w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('mul01')], 'ax-mp', '( 1 x. 0 ) = 0')], 'eqtri', '%s = 0' % B)
    bc = w.s([b0, w.s([], '0cn', '0 e. CC')], 'eqeltri', '%s e. CC' % B)
    f1 = w.s([sub], 'fsum1', '( ( 1 e. ZZ /\\ %s e. CC ) -> %s = %s )' % (B, CS('1', '1'), B))
    v = w.s([w.s([], '1z', '1 e. ZZ'), bc, f1], 'mp2an', '%s = %s' % (CS('1', '1'), B))
    w.qed([v, b0], 'eqtri', '%s = 0' % CS('1', '1'))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvcshift', 'bvcp1', 'bvc1']:
        globals()[f]().run()
