"""Sortie KD1: the Dirichlet-minus-poles function at order 0 for L (kdps0)."""
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


def gen_ps0():
    w = W('kdps0', 'At order ` 0 ` the function of ` kdpsidn ` built from ` chi Lam ` and the zeros of ` L ` in the ` 13 / 8 ` square is ` -u sum chi ( k ) Lam ( k ) k ^ -u z - sum m / ( z - q ) ` .')
    A0 = S['kdps0'].split(' -> ')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ctr = s([], 'simpll', '( %s /\\ T e. RR )' % CHI)
    chi = s([ctr], 'simpld', CHI); tr = s([ctr], 'simprd', 'T e. RR')
    zc = s([], 'simplr', 'z e. CC'); nz = s([], 'simpr', '-. z e. %s' % ZD())
    nx = s([chi], 'simpld', NXH)
    # part 1 under ( NXH /\ z e. CC )
    B1 = '( %s /\\ z e. CC )' % NXH
    Bk = '( %s /\\ k e. NN )' % B1
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Bk, f))
    kn = b([], 'simpr', 'k e. NN')
    nxk = w.s([w.s([], 'simpl', '( %s -> %s )' % (B1, NXH))], 'adantr', '( %s -> %s )' % (Bk, NXH))
    zck = w.s([w.s([], 'simpr', '( %s -> z e. CC )' % B1)], 'adantr', '( %s -> z e. CC )' % Bk)
    chk = b([b([nxk, kn], 'jca', '( %s /\\ k e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CHV('k'))
    lam = b([b([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    cv = b([chk, lam], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHV('k'))
    ek = b([b([kn], 'nncnd', 'k e. CC'), b([zck], 'negcld', '-u z e. CC')], 'cxpcld', '( k ^c -u z ) e. CC')
    idn = w.s([], 'id', '( n = k -> n = k )')
    cn, vn = w.congr('( %s x. ( Lam ` n ) )' % CHV('n'), {'n': 'k'}, 'n = k', {'n': idn})
    cvk = fvmd(w, Bk, CVM, 'k', vn, kn, cv, cn, var='n')
    lk = b([b([b([kn], 'nnrpd', 'k e. RR+')], 'relogcld', '( log ` k ) e. RR')], 'recnd', '( log ` k ) e. CC')
    e0 = b([b([lk], 'negcld', '-u ( log ` k ) e. CC')], 'exp0d', '( -u ( log ` k ) ^ 0 ) = 1')
    TM = '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u z ) )' % CHV('k')
    t1 = b([e0, b([cvk], 'oveq1d', '( ( %s ` k ) x. ( k ^c -u z ) ) = %s' % (CVM, TM))], 'oveq12d', '( ( -u ( log ` k ) ^ 0 ) x. ( ( %s ` k ) x. ( k ^c -u z ) ) ) = ( 1 x. %s )' % (CVM, TM))
    t2 = b([b([cv, ek], 'mulcld', '%s e. CC' % TM)], 'mullidd', '( 1 x. %s ) = %s' % (TM, TM))
    tt = b([t1, t2], 'eqtrd', '( ( -u ( log ` k ) ^ 0 ) x. ( ( %s ` k ) x. ( k ^c -u z ) ) ) = %s' % (CVM, TM))
    p1 = w.s([tt], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (B1, S1I('0', 'z'), TM))
    p1a = s([s([nx, zc], 'jca', B1), p1], 'syl', '%s = sum_ k e. NN %s' % (S1I('0', 'z'), TM))
    # part 2 under ( A0 /\ q e. ZD )
    Aq = '( %s /\\ q e. %s )' % (A0, ZD())
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    L = lambda st: lift(w, st, Aq)
    qq = a([], 'simpr', 'q e. %s' % ZD())
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = a([a([L(chi), L(tr)], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    lzp = top_and(lzc)
    cmp = w.s([w.s([], 'oveq2', '( r = q -> %s = %s )' % (MU('r'), MU('q')))], 'eleq1d', '( r = q -> ( %s e. NN <-> %s e. NN ) )' % (MU('r'), MU('q')))
    ordq_all = a([lz], 'simp2d', lzp[1])
    assert lzp[1].startswith('A. q e. ')
    MUq = MU('q')
    mqn = a([qq, a([ordq_all, w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (ZD(), MUq))], 'mpd', '%s e. NN' % MUq)
    mqc = a([mqn], 'nncnd', '%s e. CC' % MUq)
    SQ13 = SQ(CT('T'), R138)
    qsq = a([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Aq, ZD(), SQ13)), qq], 'sseldd', 'q e. %s' % SQ13)
    from kd1_q import corners
    cc_ = a([a([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % Aq), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([L(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CT('T'))], 'id', 'T.') if False else \
        a([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % Aq), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([L(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CT('T'))
    ri = Closure(w, Aq, {'T': ('RR', L(tr))})
    rr_ = ri.mem(R138, 'RR')
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    ric = a([a([rr_], 'recnd', '%s e. CC' % R138), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([rr_], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)], 'addcld', '%s e. CC' % RI_)
    sqcc = a([a([a([cc_, ric], 'subcld', '%s e. CC' % A13), a([cc_, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    qc = a([sqcc, qsq], 'sseldd', 'q e. CC')
    zne = a([a([a([qq, L(nz)], 'jca', '( q e. %s /\\ -. z e. %s )' % (ZD(), ZD())), w.inst('nelne2')], 'syl', 'q =/= z')], 'necomd', 'z =/= q')
    zq = a([L(zc), qc], 'subcld', '( z - q ) e. CC'); zqn = a([L(zc), qc, zne], 'subne0d', '( z - q ) =/= 0')
    wv = fvmd(w, Aq, WMM, 'q', MUq, qq, w.s([w.s([], 'ovex', '%s e. _V' % MUq)], 'a1i', '( %s -> %s e. _V )' % (Aq, MUq)),
              w.s([], 'oveq2', '( p = q -> %s = %s )' % (MU('p'), MUq)), var='p')
    m1c = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % Aq)
    one = '( ( -u 1 ^ 0 ) x. ( ! ` 0 ) )'
    o1 = a([a([m1c], 'exp0d', '( -u 1 ^ 0 ) = 1'), w.s([w.s([], 'fac0', '( ! ` 0 ) = 1')], 'a1i', '( %s -> ( ! ` 0 ) = 1 )' % Aq)], 'oveq12d', '%s = ( 1 x. 1 )' % one)
    o2 = a([o1, w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % Aq)], 'eqtrd', '%s = 1' % one)
    o3 = a([a([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % Aq)], 'oveq2d', '( ( z - q ) ^ ( 0 + 1 ) ) = ( ( z - q ) ^ 1 )'), a([zq], 'exp1d', '( ( z - q ) ^ 1 ) = ( z - q )')],
           'eqtrd', '( ( z - q ) ^ ( 0 + 1 ) ) = ( z - q )')
    pq = a([o2, o3], 'oveq12d', '%s = ( 1 / ( z - q ) )' % PQ('0', 'z'))
    tq = a([wv, pq], 'oveq12d', '( ( %s ` q ) x. %s ) = ( %s x. ( 1 / ( z - q ) ) )' % (WMM, PQ('0', 'z'), MUq))
    dr = a([mqc, zq, zqn], 'divrecd', '( %s / ( z - q ) ) = ( %s x. ( 1 / ( z - q ) ) )' % (MUq, MUq))
    tq2 = a([tq, dr], 'eqtr4d', '( ( %s ` q ) x. %s ) = ( %s / ( z - q ) )' % (WMM, PQ('0', 'z'), MUq))
    p2 = s([tq2], 'sumeq2dv', 'sum_ q e. %s ( ( %s ` q ) x. %s ) = sum_ q e. %s ( %s / ( z - q ) )' % (ZD(), WMM, PQ('0', 'z'), ZD(), MUq))
    fin = s([s([p1a], 'negeqd', '-u %s = -u sum_ k e. NN %s' % (S1I('0', 'z'), TM)), p2], 'oveq12d',
            '( -u %s - sum_ q e. %s ( ( %s ` q ) x. %s ) ) = ( -u sum_ k e. NN %s - sum_ q e. %s ( %s / ( z - q ) ) )' % (S1I('0', 'z'), ZD(), WMM, PQ('0', 'z'), TM, ZD(), MUq))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdps0']))
    return run(w)


if __name__ == '__main__':
    gen_ps0()
