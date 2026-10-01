"""Sortie CEN2: the pointwise identities at 1 + 3 D (cen2t1, cen2t3; Lean Census hg1, hg4)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure
from c9lib import top_and

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


Q = '( 1 + ( 3 x. D ) )'


def cxsplit(w, s, kc, kne, cQ, cI, I):
    """k ^c -u ( Q + I ) = ( k ^c -u Q ) x. ( k ^c -u I )"""
    a = s([cQ, cI], 'negdid', '-u ( %s + %s ) = ( -u %s + -u %s )' % (Q, I, Q, I))
    b = s([a], 'oveq2d', '( k ^c -u ( %s + %s ) ) = ( k ^c ( -u %s + -u %s ) )' % (Q, I, Q, I))
    c = s([kc, kne, s([cQ], 'negcld', '-u %s e. CC' % Q), s([cI], 'negcld', '-u %s e. CC' % I)], 'cxpaddd',
          '( k ^c ( -u %s + -u %s ) ) = ( ( k ^c -u %s ) x. ( k ^c -u %s ) )' % (Q, I, Q, I))
    return s([b, c], 'eqtrd', '( k ^c -u ( %s + %s ) ) = ( ( k ^c -u %s ) x. ( k ^c -u %s ) )' % (Q, I, Q, I))


def gen_t1():
    w = W('cen2t1', 'The twisted weight at ` 1 + 3 D ` : ` Lam ( k ) k ^ - ( 1 + 3 D ) x. E k ^ - i T = E Lam ( k ) k ^ - ( 1 + 3 D + i T ) ` (Lean Census ` hg1 ` inside ` no_thirteen_bad ` ).')
    A0, C0 = split_imp(S['cen2t1'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    kn = s([], 'simpll', 'k e. NN'); dr = s([], 'simplr', 'D e. RR')
    ec = s([], 'simprl', 'E e. CC'); tr = s([], 'simprr', 'T e. RR')
    lr = s([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')
    c = Closure(w, A0, {'k': ('NN', kn), 'D': ('RR', dr), 'E': ('CC', ec), 'T': ('RR', tr),  '( Lam ` k )': ('RR', lr), '_i': ('CC', s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'))})
    I = '( _i x. T )'
    kc = c.mem('k', 'CC'); kne = s([kn], 'nnne0d', 'k =/= 0')
    sp = cxsplit(w, s, kc, kne, c.mem(Q, 'CC'), c.mem(I, 'CC'), I)
    L = '( Lam ` k )'; a = '( k ^c -u %s )' % Q; b = '( k ^c -u %s )' % I
    s5 = s([sp], 'oveq2d', '( ( E x. %s ) x. ( k ^c -u ( %s + %s ) ) ) = ( ( E x. %s ) x. ( %s x. %s ) )' % (L, Q, I, L, a, b))
    s6 = s([c.mem(L, 'CC'), c.mem(a, 'CC'), ec, c.mem(b, 'CC')], 'mul4d', '( ( %s x. %s ) x. ( E x. %s ) ) = ( ( %s x. E ) x. ( %s x. %s ) )' % (L, a, b, L, a, b))
    s7 = s([c.mem(L, 'CC'), ec], 'mulcomd', '( %s x. E ) = ( E x. %s )' % (L, L))
    s8 = s([s7], 'oveq1d', '( ( %s x. E ) x. ( %s x. %s ) ) = ( ( E x. %s ) x. ( %s x. %s ) )' % (L, a, b, L, a, b))
    s9 = s([s6, s8], 'eqtrd', '( ( %s x. %s ) x. ( E x. %s ) ) = ( ( E x. %s ) x. ( %s x. %s ) )' % (L, a, b, L, a, b))
    w.qed([s9, s5], 'eqtr4d', S['cen2t1'])
    return run(w)


def gen_t3():
    w = W('cen2t3', 'The cross weight at ` 1 + 3 D ` : ` Lam ( k ) k ^ - ( 1 + 3 D ) x. E k ^ - i T x. * ( F k ^ - i U ) = E * F Lam ( k ) k ^ - ( 1 + 3 D + i ( T - U ) ) ` (Lean Census ` hg4 ` inside ` no_thirteen_bad ` ).')
    A0, C0 = split_imp(S['cen2t3'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    kn = s([], 'simpll', 'k e. NN'); dr = s([], 'simplr', 'D e. RR')
    H2 = top_and(A0)[1]
    h2 = s([], 'simpr', H2)
    ef = s([h2], 'simpld', '( E e. CC /\\ F e. CC )'); tu = s([h2], 'simprd', '( T e. RR /\\ U e. RR )')
    ec = s([ef], 'simpld', 'E e. CC'); fc = s([ef], 'simprd', 'F e. CC')
    tr = s([tu], 'simpld', 'T e. RR'); ur = s([tu], 'simprd', 'U e. RR')
    lr = s([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')
    c = Closure(w, A0, {'k': ('NN', kn), 'D': ('RR', dr), 'E': ('CC', ec), 'F': ('CC', fc), 'T': ('RR', tr), 'U': ('RR', ur), '( Lam ` k )': ('RR', lr), '_i': ('CC', s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'))})
    kc = c.mem('k', 'CC'); kne = s([kn], 'nnne0d', 'k =/= 0'); krp = c.mem('k', 'RR+')
    c.have('( * ` F )', 'CC', s([fc], 'cjcld', '( * ` F ) e. CC'))
    L = '( Lam ` k )'; a = '( k ^c -u %s )' % Q
    IT = '( _i x. T )'; IU = '( _i x. U )'
    bT = '( k ^c -u %s )' % IT; bU = '( k ^c -u %s )' % IU
    # conj ( F x. bU ) = ( * F ) x. ( k ^c ( * -u IU ) ) = ( * F ) x. ( k ^c IU )
    cU = c.mem(bU, 'CC')
    j1 = s([fc, cU], 'cjmuld', '( * ` ( F x. %s ) ) = ( ( * ` F ) x. ( * ` %s ) )' % (bU, bU))
    niu = c.mem('-u %s' % IU, 'CC')
    j2 = s([kn, niu, w.inst('cencjcx')], 'syl2anc', '( * ` %s ) = ( k ^c ( * ` -u %s ) )' % (bU, IU))
    # * -u ( _i x. U ) = ( _i x. U ) : cjneg, cjmul, cji, cjre
    iuc = c.mem(IU, 'CC')
    j3 = s([iuc], 'cjnegd', '( * ` -u %s ) = -u ( * ` %s )' % (IU, IU))
    j4 = s([c.mem('_i', 'CC'), c.mem('U', 'CC')], 'cjmuld', '( * ` %s ) = ( ( * ` _i ) x. ( * ` U ) )' % IU)
    j5 = s([w.s([], 'cji', '( * ` _i ) = -u _i')], 'a1i', '( * ` _i ) = -u _i')
    j6 = s([ur], 'cjred', '( * ` U ) = U')
    j7 = s([j5, j6], 'oveq12d', '( ( * ` _i ) x. ( * ` U ) ) = ( -u _i x. U )')
    j8 = s([c.mem('_i', 'CC'), c.mem('U', 'CC')], 'mulneg1d', '( -u _i x. U ) = -u %s' % IU)
    j9 = s([j4, j7, j8], 'eqtr3d', 'x') if False else s([s([j4, j7], 'eqtrd', '( * ` %s ) = ( -u _i x. U )' % IU), j8], 'eqtrd', '( * ` %s ) = -u %s' % (IU, IU))
    j10 = s([j9], 'negeqd', '-u ( * ` %s ) = -u -u %s' % (IU, IU))
    j11 = s([iuc], 'negnegd', '-u -u %s = %s' % (IU, IU))
    j12 = s([s([j3, j10], 'eqtrd', '( * ` -u %s ) = -u -u %s' % (IU, IU)), j11], 'eqtrd', '( * ` -u %s ) = %s' % (IU, IU))
    j13 = s([j2, s([j12], 'oveq2d', '( k ^c ( * ` -u %s ) ) = ( k ^c %s )' % (IU, IU))], 'eqtrd', '( * ` %s ) = ( k ^c %s )' % (bU, IU))
    cF = '( * ` F )'; bI = '( k ^c %s )' % IU
    j14 = s([j1, s([j13], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. %s )' % (cF, bU, cF, bI))], 'eqtrd', '( * ` ( F x. %s ) ) = ( %s x. %s )' % (bU, cF, bI))
    # the exponent: -u ( Q + i ( T - U ) ) = ( -u Q + ( -u IT + IU ) )
    ITU = '( _i x. ( T - U ) )'
    e1 = s([c.mem('_i', 'CC'), c.mem('T', 'CC'), c.mem('U', 'CC')], 'subdid', '%s = ( %s - %s )' % (ITU, IT, IU))
    e2 = s([s([e1], 'negeqd', '-u %s = -u ( %s - %s )' % (ITU, IT, IU)), s([c.mem(IT, 'CC'), iuc], 'negsubdid', '-u ( %s - %s ) = ( -u %s + %s )' % (IT, IU, IT, IU))],
           'eqtrd', '-u %s = ( -u %s + %s )' % (ITU, IT, IU))
    sp = cxsplit(w, s, kc, kne, c.mem(Q, 'CC'), c.mem(ITU, 'CC'), ITU)
    e3 = s([s([e2], 'oveq2d', '( k ^c -u %s ) = ( k ^c ( -u %s + %s ) )' % (ITU, IT, IU)),
            s([kc, kne, c.mem('-u %s' % IT, 'CC'), iuc], 'cxpaddd', '( k ^c ( -u %s + %s ) ) = ( %s x. %s )' % (IT, IU, bT, bI))],
           'eqtrd', '( k ^c -u %s ) = ( %s x. %s )' % (ITU, bT, bI))
    POW = '( k ^c -u ( %s + %s ) )' % (Q, ITU)
    e4 = s([sp, s([e3], 'oveq2d', '( %s x. ( k ^c -u %s ) ) = ( %s x. ( %s x. %s ) )' % (a, ITU, a, bT, bI))], 'eqtrd',
           '%s = ( %s x. ( %s x. %s ) )' % (POW, a, bT, bI))
    # LHS = ( L x. a ) x. ( ( E x. bT ) x. ( cF x. bI ) ); RHS = ( ( E x. cF ) x. L ) x. ( a x. ( bT x. bI ) )
    LHS0 = '( ( %s x. %s ) x. ( ( E x. %s ) x. ( * ` ( F x. %s ) ) ) )' % (L, a, bT, bU)
    LHS1 = '( ( %s x. %s ) x. ( ( E x. %s ) x. ( %s x. %s ) ) )' % (L, a, bT, cF, bI)
    l1 = s([s([j14], 'oveq2d', '( ( E x. %s ) x. ( * ` ( F x. %s ) ) ) = ( ( E x. %s ) x. ( %s x. %s ) )' % (bT, bU, bT, cF, bI))], 'oveq2d', '%s = %s' % (LHS0, LHS1))
    RHS0 = '( ( ( E x. %s ) x. %s ) x. %s )' % (cF, L, POW)
    RHS1 = '( ( ( E x. %s ) x. %s ) x. ( %s x. ( %s x. %s ) ) )' % (cF, L, a, bT, bI)
    r1 = s([e4], 'oveq2d', '%s = %s' % (RHS0, RHS1))
    # ring: LHS1 = RHS1
    vals = {'L': L, 'a': a, 'E': 'E', 'bT': bT, 'cF': cF, 'bI': bI}
    m1 = s([c.mem('E', 'CC'), c.mem(bT, 'CC'), c.mem(cF, 'CC'), c.mem(bI, 'CC')], 'mul4d',
           '( ( E x. %s ) x. ( %s x. %s ) ) = ( ( E x. %s ) x. ( %s x. %s ) )' % (bT, cF, bI, cF, bT, bI))
    m2 = s([m1], 'oveq2d', '%s = ( ( %s x. %s ) x. ( ( E x. %s ) x. ( %s x. %s ) ) )' % (LHS1, L, a, cF, bT, bI))
    EC = '( E x. %s )' % cF; BB = '( %s x. %s )' % (bT, bI)
    m3 = s([c.mem(L, 'CC'), c.mem(a, 'CC'), c.mem(EC, 'CC'), c.mem(BB, 'CC')], 'mul4d',
           '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (L, a, EC, BB, L, EC, a, BB))
    m4 = s([c.mem(L, 'CC'), c.mem(EC, 'CC')], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (L, EC, EC, L))
    m5 = s([m4], 'oveq1d', '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (L, EC, a, BB, EC, L, a, BB))
    m6 = s([s([m2, m3], 'eqtrd', '%s = ( ( %s x. %s ) x. ( %s x. %s ) )' % (LHS1, L, EC, a, BB)), m5], 'eqtrd', '%s = %s' % (LHS1, RHS1))
    w.qed([s([l1, m6], 'eqtrd', '%s = %s' % (LHS0, RHS1)), r1], 'eqtr4d', S['cen2t3'])
    return run(w)


if __name__ == '__main__':
    gen_t1()
    gen_t3()
