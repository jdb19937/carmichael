"""Sortie T14 (a): the ExpB kit of Overhead.lean over a real M.
MM_DB=sorties/t14.mm python3 tools/gen/t14_a_xb.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *


def start(label, desc):
    """worksheet with the $e hypotheses of LABEL; returns (w, [None, '1', '2', ...], hyps)"""
    w = W(label, desc)
    hyps, concl = STMTS14[label]
    H = [None]
    for i, h in enumerate(hyps, 1):
        w.s([], '%s.%d' % (label, i), h, name='h%d' % i)
        H.append(str(i))
    return w, H, concl


def st(w, hyps, ref, goal):
    return w.s(hyps, ref, ph(goal))


def efge(w, x, xre, x0):
    """( ph -> ( 1 + x ) <_ ( exp ` x ) ) from x real and nonnegative"""
    return w.s([xre, x0, w.inst('bvefge1p')], 'syl2anc', ph('( 1 + %s ) <_ ( exp ` %s )' % (x, x)))


# ------------------------------------------------------------------ xbcon
def xbcon():
    w, H, concl = start('xbcon', 'A constant bound: A <_ K with 0 <_ K gives A <_ exp ( K x. M ) once 1 <_ M '
                        '(Lean: ExpB.const_le).')
    cl = Closure(w, 'ph', {'M': ('RR', H[1]), 'K': [('RR', H[3]), ('ge0', H[4])], 'A': ('RR', H[5])})
    m0 = linarith(w, 'ph', [H[2]], '0 <_ M', closure=cl)
    cl.have('M', 'ge0', m0)
    km = '( K x. M )'
    kmre = cl.mem(km, 'RR'); km0 = cl.ge0(km)
    bv = efge(w, km, kmre, km0)
    cl.have(EXP('K', 'M'), 'RR', cl.mem(EXP('K', 'M'), 'RR'))
    nlinarith(w, 'ph', [H[6], H[4], H[2], bv], XB('A', 'K'), closure=cl, name='qed')
    return run(w)




def kitcl(w, H, spec):
    """closure over ph with the leaves given as {expr: [(kind, hypnumber), ...]}"""
    leaves = {}
    for e, lst in spec.items():
        leaves[e] = [(k, H[i]) for k, i in lst]
    return Closure(w, 'ph', leaves)


def efle_(w, cl, x, y, le):
    """( ph -> ( exp ` x ) <_ ( exp ` y ) ) from ( ph -> x <_ y )"""
    bi = w.s([cl.mem(x, 'RR'), cl.mem(y, 'RR'), w.inst('efle')], 'syl2anc',
             ph('( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (x, y, x, y)))
    return w.s([le, bi], 'mpbid', ph('( exp ` %s ) <_ ( exp ` %s )' % (x, y)))


def efadd_(w, cl, x, y):
    """( ph -> ( exp ` ( x + y ) ) = ( ( exp ` x ) x. ( exp ` y ) ) )"""
    return w.s([cl.mem(x, 'CC'), cl.mem(y, 'CC'), w.inst('efadd')], 'syl2anc',
               ph('( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (x, y, x, y)))


# ------------------------------------------------------------------ xbmul
def xbmul():
    w, H, concl = start('xbmul', 'Products: exponent constants add (Lean: ExpB.mul, ExpB.mul_nat), with the target '
                        'constant F >= C + D.')
    cl = kitcl(w, H, {'M': [('RR', 1), ('ge0', 2)], 'C': [('RR', 3)], 'D': [('RR', 4)], 'F': [('RR', 5)],
                      'A': [('RR', 7), ('ge0', 8)], 'B': [('RR', 9), ('ge0', 10)]})
    cm, dm, fm = '( C x. M )', '( D x. M )', '( F x. M )'
    ec, ed = EXP('C', 'M'), EXP('D', 'M')
    p1 = w.s([cl.mem('A', 'RR'), cl.mem(ec, 'RR'), cl.mem('B', 'RR'), cl.mem(ed, 'RR'), H[8], H[10], H[11], H[12]],
             'lemul12ad', ph('( A x. B ) <_ ( %s x. %s )' % (ec, ed)))
    e1 = efadd_(w, cl, cm, dm)
    e2 = w.s([cl.mem('C', 'CC'), cl.mem('D', 'CC'), cl.mem('M', 'CC')], 'adddird',
             ph('( ( C + D ) x. M ) = ( %s + %s )' % (cm, dm)))
    e3 = w.s([e2], 'fveq2d', ph('( exp ` ( ( C + D ) x. M ) ) = ( exp ` ( %s + %s ) )' % (cm, dm)))
    e4 = w.s([e3, e1], 'eqtrd', ph('( exp ` ( ( C + D ) x. M ) ) = ( %s x. %s )' % (ec, ed)))
    le = w.s([cl.mem('( C + D )', 'RR'), cl.mem('F', 'RR'), cl.mem('M', 'RR'), cl.ge0('M'), H[6]], 'lemul1ad',
             ph('( ( C + D ) x. M ) <_ %s' % fm))
    m1 = efle_(w, cl, '( ( C + D ) x. M )', fm, le)
    m2 = w.s([e4, m1], 'eqbrtrrd', ph('( %s x. %s ) <_ %s' % (ec, ed, EXP('F', 'M'))))
    w.qed([cl.mem('( A x. B )', 'RR'), cl.mem('( %s x. %s )' % (ec, ed), 'RR'), cl.mem(EXP('F', 'M'), 'RR'), p1, m2],
          'letrd', ph(XB('( A x. B )', 'F')))
    return run(w)


# ------------------------------------------------------------------ xbadd
def xbadd():
    w, H, concl = start('xbadd', 'Sums: a + b <_ 2 exp ( G M ) <_ exp ( ( G + 1 ) M ) for C , D <_ G and 1 <_ M '
                        '(Lean: ExpB.add with max c1 c2 <_ G, ExpB.add_same, ExpB.add_nat).')
    cl = kitcl(w, H, {'M': [('RR', 1)], 'C': [('RR', 3)], 'D': [('RR', 4)], 'G': [('RR', 5)], 'F': [('RR', 6)],
                      'A': [('RR', 10)], 'B': [('RR', 11)]})
    m0 = linarith(w, 'ph', [H[2]], '0 <_ M', closure=cl); cl.have('M', 'ge0', m0)
    gm = '( G x. M )'; eg = EXP('G', 'M'); em = '( exp ` M )'
    lc = w.s([cl.mem('C', 'RR'), cl.mem('G', 'RR'), cl.mem('M', 'RR'), m0, H[7]], 'lemul1ad', ph('( C x. M ) <_ %s' % gm))
    ld = w.s([cl.mem('D', 'RR'), cl.mem('G', 'RR'), cl.mem('M', 'RR'), m0, H[8]], 'lemul1ad', ph('( D x. M ) <_ %s' % gm))
    ac = efle_(w, cl, '( C x. M )', gm, lc); ad = efle_(w, cl, '( D x. M )', gm, ld)
    bv = w.s([cl.mem('M', 'RR'), m0, w.inst('bvefge1p')], 'syl2anc', ph('( 1 + M ) <_ %s' % em))
    two = linarith(w, 'ph', [bv, H[2]], '2 <_ %s' % em, closure=cl)
    egp = w.s([cl.mem(gm, 'RR'), w.inst('efgt0')], 'syl', ph('0 < %s' % eg))
    eg0 = w.s([w.s([], '0red', ph('0 e. RR')), cl.mem(eg, 'RR'), egp], 'ltled', ph('0 <_ %s' % eg))
    pr = w.s([cl.mem('2', 'RR'), cl.mem(em, 'RR'), cl.mem(eg, 'RR'), eg0, two], 'lemul1ad',
             ph('( 2 x. %s ) <_ ( %s x. %s )' % (eg, em, eg)))
    e1 = efadd_(w, cl, 'M', gm)
    e2 = w.s([cl.mem('G', 'CC'), cl.mem('1', 'CC'), cl.mem('M', 'CC')], 'adddird',
             ph('( ( G + 1 ) x. M ) = ( %s + ( 1 x. M ) )' % gm))
    e3 = w.s([cl.mem('M', 'CC')], 'mullidd', ph('( 1 x. M ) = M'))
    e4 = w.s([e3], 'oveq2d', ph('( %s + ( 1 x. M ) ) = ( %s + M )' % (gm, gm)))
    e5 = w.s([cl.mem(gm, 'CC'), cl.mem('M', 'CC')], 'addcomd', ph('( %s + M ) = ( M + %s )' % (gm, gm)))
    e6 = w.s([w.s([e2, e4], 'eqtrd', ph('( ( G + 1 ) x. M ) = ( %s + M )' % gm)), e5], 'eqtrd',
             ph('( ( G + 1 ) x. M ) = ( M + %s )' % gm))
    e7 = w.s([e6], 'fveq2d', ph('( exp ` ( ( G + 1 ) x. M ) ) = ( exp ` ( M + %s ) )' % gm))
    e8 = w.s([e7, e1], 'eqtrd', ph('( exp ` ( ( G + 1 ) x. M ) ) = ( %s x. %s )' % (em, eg)))
    le = w.s([cl.mem('( G + 1 )', 'RR'), cl.mem('F', 'RR'), cl.mem('M', 'RR'), m0, H[9]], 'lemul1ad',
             ph('( ( G + 1 ) x. M ) <_ ( F x. M )'))
    m1 = efle_(w, cl, '( ( G + 1 ) x. M )', '( F x. M )', le)
    cl.atom('( %s x. %s )' % (em, eg))
    linarith(w, 'ph', [H[12], H[13], ac, ad, pr, e8, m1], XB('( A + B )', 'F'), closure=cl, name='qed')
    return run(w)


# ------------------------------------------------------------------ xblin
def xblin():
    w, H, concl = start('xblin', 'A linear bound is an exponential one: A <_ C M with 0 <_ C M gives '
                        'A <_ exp ( C M ) (x <_ 1 + x <_ exp x).')
    cl = kitcl(w, H, {'M': [('RR', 1)], 'C': [('RR', 2)], 'A': [('RR', 3)]})
    cm = '( C x. M )'
    bv = w.s([cl.mem(cm, 'RR'), H[4], w.inst('bvefge1p')], 'syl2anc', ph('( 1 + %s ) <_ %s' % (cm, EXP('C', 'M'))))
    cl.atom(cm)
    linarith(w, 'ph', [H[5], bv], XB('A', 'C'), closure=cl, name='qed')
    return run(w)


# ------------------------------------------------------------------ xblin2
def xblin2():
    w, H, concl = start('xblin2', 'A bound K M with K <_ M is at most exp ( 2 M ): K M <_ M ^ 2 <_ 2 exp M <_ '
                        '( exp M ) ^ 2 (Lean: window_base_real, exp M >= M ^ 2 / 2).')
    cl = kitcl(w, H, {'M': [('RR', 1)], 'K': [('RR', 3), ('ge0', 4)], 'A': [('RR', 6)]})
    m0 = linarith(w, 'ph', [H[2]], '0 <_ M', closure=cl); cl.have('M', 'ge0', m0)
    em = '( exp ` M )'
    km = w.s([cl.mem('K', 'RR'), cl.mem('M', 'RR'), cl.mem('M', 'RR'), m0, H[5]], 'lemul1ad', ph('( K x. M ) <_ ( M x. M )'))
    q = w.s([cl.mem('M', 'RR'), m0, w.inst('efge1p2')], 'syl2anc', ph('( ( 1 + M ) + ( ( M ^ 2 ) / 2 ) ) <_ %s' % em))
    sq = w.s([cl.mem('M', 'CC')], 'sqvald', ph('( M ^ 2 ) = ( M x. M )'))
    bv = w.s([cl.mem('M', 'RR'), m0, w.inst('bvefge1p')], 'syl2anc', ph('( 1 + M ) <_ %s' % em))
    two = linarith(w, 'ph', [bv, H[2]], '2 <_ %s' % em, closure=cl)
    emp = w.s([cl.mem('M', 'RR'), w.inst('efgt0')], 'syl', ph('0 < %s' % em))
    em0 = w.s([w.s([], '0red', ph('0 e. RR')), cl.mem(em, 'RR'), emp], 'ltled', ph('0 <_ %s' % em))
    pr = w.s([cl.mem('2', 'RR'), cl.mem(em, 'RR'), cl.mem(em, 'RR'), em0, two], 'lemul1ad',
             ph('( 2 x. %s ) <_ ( %s x. %s )' % (em, em, em)))
    w.s([], '2z', '2 e. ZZ')   # an unused step: the stored worksheet of xblin2 contains it
    e1 = w.s([cl.mem('M', 'CC'), w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', ph('2 e. ZZ')),
              w.inst('efexp')], 'syl2anc', ph('( exp ` ( 2 x. M ) ) = ( %s ^ 2 )' % em))
    e2 = w.s([cl.mem(em, 'CC')], 'sqvald', ph('( %s ^ 2 ) = ( %s x. %s )' % (em, em, em)))
    e3 = w.s([e1, e2], 'eqtrd', ph('( exp ` ( 2 x. M ) ) = ( %s x. %s )' % (em, em)))
    cl.atom('( M x. M )'); cl.atom('( %s x. %s )' % (em, em)); cl.atom('( M ^ 2 )'); cl.atom('( K x. M )')
    linarith(w, 'ph', [H[7], km, q, sq, pr, e3, m0], XB('A', '2'), closure=cl, name='qed')
    return run(w)



def eexp(w, cl, x, n):
    """( ph -> ( exp ` ( n x. x ) ) = ( ( exp ` x ) ^ n ) ) for n e. ZZ"""
    return w.s([cl.mem(x, 'CC'), cl.mem(n, 'ZZ'), w.inst('efexp')], 'syl2anc',
               ph('( exp ` ( %s x. %s ) ) = ( ( exp ` %s ) ^ %s )' % (n, x, x, n)))


# ------------------------------------------------------------------ xbpow
def xbpow():
    w, H, concl = start('xbpow', 'Powers: exponent constants multiply (Lean: ExpB.pow, ExpB.pow_nat), with the '
                        'target constant F >= N C.')
    cl = kitcl(w, H, {'M': [('RR', 1), ('ge0', 2)], 'C': [('RR', 3)], 'F': [('RR', 4)], 'N': [('NN0', 5)],
                      'A': [('RR', 7), ('ge0', 8)]})
    cm = '( C x. M )'; ec = EXP('C', 'M')
    p1 = w.s([cl.mem('A', 'RR'), cl.mem(ec, 'RR'), cl.mem('N', 'NN0'), H[8], H[9]], 'leexp1ad',
             ph('( A ^ N ) <_ ( %s ^ N )' % ec))
    e1 = eexp(w, cl, cm, 'N')
    e2 = w.s([cl.mem('N', 'CC'), cl.mem('C', 'CC'), cl.mem('M', 'CC')], 'mulassd',
             ph('( ( N x. C ) x. M ) = ( N x. %s )' % cm))
    e3 = w.s([e2], 'fveq2d', ph('( exp ` ( ( N x. C ) x. M ) ) = ( exp ` ( N x. %s ) )' % cm))
    e4 = w.s([e3, e1], 'eqtrd', ph('( exp ` ( ( N x. C ) x. M ) ) = ( %s ^ N )' % ec))
    le = w.s([cl.mem('( N x. C )', 'RR'), cl.mem('F', 'RR'), cl.mem('M', 'RR'), H[2], H[6]], 'lemul1ad',
             ph('( ( N x. C ) x. M ) <_ ( F x. M )'))
    m1 = efle_(w, cl, '( ( N x. C ) x. M )', '( F x. M )', le)
    m2 = w.s([e4, m1], 'eqbrtrrd', ph('( %s ^ N ) <_ %s' % (ec, EXP('F', 'M'))))
    w.qed([cl.mem('( A ^ N )', 'RR'), cl.mem('( %s ^ N )' % ec, 'RR'), cl.mem(EXP('F', 'M'), 'RR'), p1, m2],
          'letrd', ph(XB('( A ^ N )', 'F')))
    return run(w)


# ------------------------------------------------------------------ xb2pow
def xb2pow():
    w, H, concl = start('xb2pow', 'Powers of two: T <_ C M gives 2 ^ T <_ exp ( C M ) (2 <_ e; Lean: ExpB.two_pow, '
                        'ExpB.two_pow_nat).')
    cl = kitcl(w, H, {'M': [('RR', 1)], 'C': [('RR', 2)], 'T': [('NN0', 3)]})
    e = '_e'
    ere = w.s([w.s([], 'ere', '_e e. RR')], 'a1i', ph('_e e. RR'))
    cl.have(e, 'RR', ere)
    lt2 = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e')
    le2 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], 'ere', '_e e. RR'), lt2], 'ltleii', '2 <_ _e')], 'a1i', ph('2 <_ _e'))
    p1 = w.s([cl.mem('2', 'RR'), ere, cl.mem('T', 'NN0'), cl.ge0('2'), le2], 'leexp1ad', ph('( 2 ^ T ) <_ ( _e ^ T )'))
    d = w.s([w.s([], 'df-e', '_e = ( exp ` 1 )')], 'a1i', ph('_e = ( exp ` 1 )'))
    e1 = w.s([d], 'oveq1d', ph('( _e ^ T ) = ( ( exp ` 1 ) ^ T )'))
    e2 = eexp(w, cl, '1', 'T')
    e3 = w.s([cl.mem('T', 'CC')], 'mulridd', ph('( T x. 1 ) = T'))
    e4 = w.s([e3], 'fveq2d', ph('( exp ` ( T x. 1 ) ) = ( exp ` T )'))
    e5 = w.s([e4, e2], 'eqtr3d', ph('( exp ` T ) = ( ( exp ` 1 ) ^ T )'))
    e6 = w.s([e1, e5], 'eqtr4d', ph('( _e ^ T ) = ( exp ` T )'))
    m1 = efle_(w, cl, 'T', '( C x. M )', H[4])
    m2 = w.s([e6, m1], 'eqbrtrd', ph('( _e ^ T ) <_ %s' % EXP('C', 'M')))
    w.qed([cl.mem('( 2 ^ T )', 'RR'), cl.mem('( _e ^ T )', 'RR'), cl.mem(EXP('C', 'M'), 'RR'), p1, m2],
          'letrd', ph(XB('( 2 ^ T )', 'C')))
    return run(w)


# ------------------------------------------------------------------ xbtmb
def xbtmb():
    w, H, concl = start('xbtmb', 'The machine budget: TMB B = 64 ( B + 2 ) ^ 3 <_ 1728 exp ( 3 C M ) <_ '
                        'exp ( ( 3 C + 11 ) M ) (Lean: ExpB.B, with 2 ^ 11 for exp 8).')
    cl = kitcl(w, H, {'M': [('RR', 1)], 'C': [('RR', 3), ('ge0', 4)], 'F': [('RR', 5)], 'B': [('NN0', 7)]})
    m0 = linarith(w, 'ph', [H[2]], '0 <_ M', closure=cl); cl.have('M', 'ge0', m0)
    cm = '( C x. M )'; X = EXP('C', 'M')
    bv = w.s([cl.mem(cm, 'RR'), cl.ge0(cm), w.inst('bvefge1p')], 'syl2anc', ph('( 1 + %s ) <_ %s' % (cm, X)))
    x1 = linarith(w, 'ph', [bv, cl.ge0(cm)], '1 <_ %s' % X, closure=cl)
    b2 = linarith(w, 'ph', [H[8], x1], '( B + 2 ) <_ ( 3 x. %s )' % X, closure=cl)
    p1 = w.s([cl.mem('( B + 2 )', 'RR'), cl.mem('( 3 x. %s )' % X, 'RR'), cl.mem('3', 'NN0'), cl.ge0('( B + 2 )'), b2],
             'leexp1ad', ph('( ( B + 2 ) ^ 3 ) <_ ( ( 3 x. %s ) ^ 3 )' % X))
    e1 = w.s([cl.mem('3', 'CC'), cl.mem(X, 'CC'), cl.mem('3', 'NN0')], 'mulexpd',
             ph('( ( 3 x. %s ) ^ 3 ) = ( ( 3 ^ 3 ) x. ( %s ^ 3 ) )' % (X, X)))
    e2 = eexp(w, cl, cm, '3')
    X3 = '( exp ` ( 3 x. %s ) )' % cm
    e3 = w.s([cl.mem('3', 'CC'), cl.mem('C', 'CC'), cl.mem('M', 'CC')], 'mulassd',
             ph('( ( 3 x. C ) x. M ) = ( 3 x. %s )' % cm))
    tv = w.s([cl.mem('B', 'NN0'), w.inst('tmbval')], 'syl', ph('( TMB ` B ) = ( ; 6 4 x. ( ( B + 2 ) ^ 3 ) )'))
    # 2 ^ 11 <_ exp ( 11 M )
    t11 = linarith(w, 'ph', [H[2]], '; 1 1 <_ ( ; 1 1 x. M )', closure=cl)
    p11 = w.s([cl.mem('M', 'RR'), cl.mem('; 1 1', 'RR'), cl.mem('; 1 1', 'NN0'), t11], 'xb2pow',
              ph('( 2 ^ ; 1 1 ) <_ %s' % EXP('; 1 1', 'M')))
    v11 = w.s([w.s([], '2exp11', '( 2 ^ ; 1 1 ) = ; ; ; 2 0 4 8')], 'a1i', ph('( 2 ^ ; 1 1 ) = ; ; ; 2 0 4 8'))
    E11 = EXP('; 1 1', 'M')
    ef = efadd_(w, cl, '( ; 1 1 x. M )', '( ( 3 x. C ) x. M )')
    e4 = w.s([cl.mem('; 1 1', 'CC'), cl.mem('( 3 x. C )', 'CC'), cl.mem('M', 'CC')], 'adddird',
             ph('( ( ; 1 1 + ( 3 x. C ) ) x. M ) = ( ( ; 1 1 x. M ) + ( ( 3 x. C ) x. M ) )'))
    e5 = w.s([e4], 'fveq2d', ph('( exp ` ( ( ; 1 1 + ( 3 x. C ) ) x. M ) ) = ( exp ` ( ( ; 1 1 x. M ) + ( ( 3 x. C ) x. M ) ) )'))
    e6 = w.s([e3], 'fveq2d', ph('( exp ` ( ( 3 x. C ) x. M ) ) = %s' % X3))
    # the product 1728 X ^ 3 <_ exp ( 11 M ) X ^ 3
    X3p = w.s([cl.mem(X, 'RR'), cl.mem('3', 'NN0')], 'reexpcld', ph('( %s ^ 3 ) e. RR' % X))
    xg0 = w.s([cl.mem(X, 'RR'), cl.mem('3', 'NN0'), w.s([w.s([], '0red', ph('0 e. RR')), cl.mem(X, 'RR'),
              w.s([cl.mem(cm, 'RR'), w.inst('efgt0')], 'syl', ph('0 < %s' % X))], 'ltled', ph('0 <_ %s' % X))],
              'expge0d', ph('0 <_ ( %s ^ 3 )' % X))
    l1 = linarith(w, 'ph', [p11, v11], '; ; ; 1 7 2 8 <_ %s' % E11, closure=cl)
    pr = w.s([cl.mem('; ; ; 1 7 2 8', 'RR'), cl.mem(E11, 'RR'), X3p, xg0, l1], 'lemul1ad',
             ph('( ; ; ; 1 7 2 8 x. ( %s ^ 3 ) ) <_ ( %s x. ( %s ^ 3 ) )' % (X, E11, X)))
    le = w.s([cl.mem('( ; 1 1 + ( 3 x. C ) )', 'RR'), cl.mem('F', 'RR'), cl.mem('M', 'RR'), m0,
              linarith(w, 'ph', [H[6]], '( ; 1 1 + ( 3 x. C ) ) <_ F', closure=cl)], 'lemul1ad',
             ph('( ( ; 1 1 + ( 3 x. C ) ) x. M ) <_ ( F x. M )'))
    m1 = efle_(w, cl, '( ( ; 1 1 + ( 3 x. C ) ) x. M )', '( F x. M )', le)
    cube = cube3(w)
    cl.atom('( %s ^ 3 )' % X); cl.atom('( ( B + 2 ) ^ 3 )'); cl.atom('( ( 3 x. %s ) ^ 3 )' % X)
    cl.atom('( %s x. ( %s ^ 3 ) )' % (E11, X)); cl.atom(X3)
    cl.atom('( exp ` ( ( ; 1 1 x. M ) + ( ( 3 x. C ) x. M ) ) )'); cl.atom('( exp ` ( ( 3 x. C ) x. M ) )')
    cl.atom('( exp ` ( ( ; 1 1 + ( 3 x. C ) ) x. M ) )')
    e7 = w.s([ef, w.s([e6], 'oveq2d', ph('( %s x. ( exp ` ( ( 3 x. C ) x. M ) ) ) = ( %s x. %s )' % (E11, E11, X3)))],
             'eqtrd', ph('( exp ` ( ( ; 1 1 x. M ) + ( ( 3 x. C ) x. M ) ) ) = ( %s x. %s )' % (E11, X3)))
    e8 = w.s([e5, e7], 'eqtrd', ph('( exp ` ( ( ; 1 1 + ( 3 x. C ) ) x. M ) ) = ( %s x. %s )' % (E11, X3)))
    e9 = w.s([e8, w.s([e2], 'oveq2d', ph('( %s x. %s ) = ( %s x. ( %s ^ 3 ) )' % (E11, X3, E11, X)))], 'eqtrd',
             ph('( exp ` ( ( ; 1 1 + ( 3 x. C ) ) x. M ) ) = ( %s x. ( %s ^ 3 ) )' % (E11, X)))
    e1b = w.s([e1, w.s([cube], 'oveq1d', ph('( ( 3 ^ 3 ) x. ( %s ^ 3 ) ) = ( ; 2 7 x. ( %s ^ 3 ) )' % (X, X)))], 'eqtrd',
              ph('( ( 3 x. %s ) ^ 3 ) = ( ; 2 7 x. ( %s ^ 3 ) )' % (X, X)))
    cl.have('( TMB ` B )', 'RR', w.s([tv, cl.mem('( ; 6 4 x. ( ( B + 2 ) ^ 3 ) )', 'RR')], 'eqeltrd', ph('( TMB ` B ) e. RR')))
    cl.atom('( TMB ` B )')
    linarith(w, 'ph', [tv, p1, e1b, pr, e9, m1], XB('( TMB ` B )', 'F'), closure=cl, name='qed')
    return run(w)


def cube3(w):
    """( ph -> ( 3 ^ 3 ) = ; 2 7 )"""
    return w.s([w.s([], '3exp3', '( 3 ^ 3 ) = ; 2 7')], 'a1i', ph('( 3 ^ 3 ) = ; 2 7'))


if __name__ == '__main__':
    for f in (xbcon, xbmul, xbadd, xblin, xblin2, xbpow, xb2pow, xbtmb):
        if want(f.__name__):
            f()
