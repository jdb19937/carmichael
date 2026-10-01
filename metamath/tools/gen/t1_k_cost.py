"""T1: the machine layer's cost function (TM/Cost.lean) and the fixed machine
shape (the state record and the eight-stack alphabet function of TM/Frag.lean)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from lin import linarith, nlinarith

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

BV = lambda b: '( ; 6 4 x. ( ( %s + 2 ) ^ 3 ) )' % b


def tmbval():
    lab = 'tmbval'
    ph = 'B e. NN0'
    w = W(lab, 'The value of the per-tick step budget of the machine layer.  '
               'Lean (TM/Cost.lean): ` def B (b : Nat) : Nat := 64 * (b + 2) ^ 3 ` .')
    bb = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    sb = w.s([], 'oveq1', '( b = B -> ( b + 2 ) = ( B + 2 ) )')
    sb2 = w.s([sb], 'oveq1d', '( b = B -> ( ( b + 2 ) ^ 3 ) = ( ( B + 2 ) ^ 3 ) )')
    sb3 = w.s([sb2], 'oveq2d', '( b = B -> %s = %s )' % (BV('b'), BV('B')))
    df = w.s([], 'df-tmb', 'TMB = ( b e. NN0 |-> %s )' % BV('b'))
    ve = w.s([], 'ovex', '%s e. _V' % BV('B'))
    vea = w.s([ve], 'a1i', '( %s -> %s e. _V )' % (ph, BV('B')))
    st = w.s([sb3, df], 'fvmptg', '( ( B e. NN0 /\\ %s e. _V ) -> ( TMB ` B ) = %s )' % (BV('B'), BV('B')))
    w.qed([bb, vea, st], 'syl2anc', '( %s -> ( TMB ` B ) = %s )' % (ph, BV('B')))
    return w.run()


def b2nn(w, ph, bb):
    """( ph -> ( B + 2 ) e. NN ) from bb : B e. NN0"""
    t2 = w.s([], '2nn', '2 e. NN')
    t2a = w.s([t2], 'a1i', '( %s -> 2 e. NN )' % ph)
    return w.s([bb, t2a, w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> ( B + 2 ) e. NN )' % ph)


def c64(w, ph):
    """( ph -> ; 6 4 e. NN )"""
    n6 = w.s([], '6nn0', '6 e. NN0')
    n4 = w.s([], '4nn', '4 e. NN')
    d = w.s([n6, n4], 'decnncl', '; 6 4 e. NN')
    return w.s([d], 'a1i', '( %s -> ; 6 4 e. NN )' % ph)


def tmbcl():
    lab = 'tmbcl'
    ph = 'B e. NN0'
    w = W(lab, 'The per-tick step budget of the machine layer is a positive '
               'integer.  Lean: ` one_le_B ` .')
    bb = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    val = w.s([bb, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` B ) = %s )' % (ph, BV('B')))
    bn = b2nn(w, ph, bb)
    n3 = w.s([], '3nn0', '3 e. NN0')
    n3a = w.s([n3], 'a1i', '( %s -> 3 e. NN0 )' % ph)
    ex = w.s([bn, n3a, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( ( B + 2 ) ^ 3 ) e. NN )' % ph)
    c = c64(w, ph)
    mu = w.s([c, ex, w.inst('nnmulcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, BV('B')))
    w.qed([val, mu], 'eqeltrd', '( %s -> ( TMB ` B ) e. NN )' % ph)
    return w.run()


def tmb1():
    lab = 'tmb1'
    ph = 'B e. NN0'
    w = W(lab, 'One step is within the per-tick budget of the machine layer.  '
               'Lean: ` one_le_B ` .')
    bb = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    cl = w.s([bb, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)
    w.qed([cl], 'nnge1d', '( %s -> 1 <_ ( TMB ` B ) )' % ph)
    return w.run()


def tmbmono():
    lab = 'tmbmono'
    ph = '( B e. NN0 /\\ C e. NN0 /\\ B <_ C )'
    w = W(lab, 'The per-tick step budget of the machine layer is monotone in the '
               'operand bit length.  Lean: ` B_mono ` .')
    bb = w.s([], 'simp1', '( %s -> B e. NN0 )' % ph)
    cc = w.s([], 'simp2', '( %s -> C e. NN0 )' % ph)
    le = w.s([], 'simp3', '( %s -> B <_ C )' % ph)
    vb = w.s([bb, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` B ) = %s )' % (ph, BV('B')))
    vc = w.s([cc, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` C ) = %s )' % (ph, BV('C')))
    br = w.s([bb], 'nn0red', '( %s -> B e. RR )' % ph)
    cr = w.s([cc], 'nn0red', '( %s -> C e. RR )' % ph)
    t2r = w.s([], '2re', '2 e. RR')
    t2ra = w.s([t2r], 'a1i', '( %s -> 2 e. RR )' % ph)
    b0 = w.s([bb], 'nn0ge0d', '( %s -> 0 <_ B )' % ph)
    b2r = w.s([br, t2ra], 'readdcld', '( %s -> ( B + 2 ) e. RR )' % ph)
    c2r = w.s([cr, t2ra], 'readdcld', '( %s -> ( C + 2 ) e. RR )' % ph)
    b2p = linarith(w, ph, [b0], '0 <_ ( B + 2 )', leaves={'B': br, '2': t2ra})
    lea = linarith(w, ph, [le], '( B + 2 ) <_ ( C + 2 )', leaves={'B': br, 'C': cr, '2': t2ra})
    n3 = w.s([], '3nn0', '3 e. NN0')
    n3a = w.s([n3], 'a1i', '( %s -> 3 e. NN0 )' % ph)
    t1 = w.s([b2r, c2r, n3a], '3jca', '( %s -> ( ( B + 2 ) e. RR /\\ ( C + 2 ) e. RR /\\ 3 e. NN0 ) )' % ph)
    t2 = w.s([b2p, lea], 'jca', '( %s -> ( 0 <_ ( B + 2 ) /\\ ( B + 2 ) <_ ( C + 2 ) ) )' % ph)
    ex = w.s([t1, t2, w.inst('leexp1a')], 'syl2anc', '( %s -> ( ( B + 2 ) ^ 3 ) <_ ( ( C + 2 ) ^ 3 ) )' % ph)
    c = c64(w, ph)
    crr = w.s([c], 'nnred', '( %s -> ; 6 4 e. RR )' % ph)
    c0 = w.s([c], 'nnnn0d', '( %s -> ; 6 4 e. NN0 )' % ph)
    c0g = w.s([c0], 'nn0ge0d', '( %s -> 0 <_ ; 6 4 )' % ph)
    eb = w.s([b2r, n3a], 'reexpcld', '( %s -> ( ( B + 2 ) ^ 3 ) e. RR )' % ph)
    ec = w.s([c2r, n3a], 'reexpcld', '( %s -> ( ( C + 2 ) ^ 3 ) e. RR )' % ph)
    mul = w.s([eb, ec, crr, c0g, ex], 'lemul2ad', '( %s -> %s <_ %s )' % (ph, BV('B'), BV('C')))
    m2 = w.s([vb, mul], 'eqbrtrd', '( %s -> ( TMB ` B ) <_ %s )' % (ph, BV('C')))
    w.qed([m2, vc], 'breqtrrd', '( %s -> ( TMB ` B ) <_ ( TMB ` C ) )' % ph)
    return w.run()


def tmblin():
    lab = 'tmblin'
    ph = '( B e. NN0 /\\ C e. NN0 /\\ C <_ ; 6 4 )'
    U = '( B + 2 )'
    Q = '( ( B + 2 ) ^ 2 )'
    E3 = '( ( B + 2 ) ^ 3 )'
    w = W(lab, 'A bound linear in the operand bit length with a coefficient at '
               'most 64 is within the per-tick budget of the machine layer.  '
               'Lean: ` linear_le_B ` .')
    bb = w.s([], 'simp1', '( %s -> B e. NN0 )' % ph)
    cc = w.s([], 'simp2', '( %s -> C e. NN0 )' % ph)
    le = w.s([], 'simp3', '( %s -> C <_ ; 6 4 )' % ph)
    val = w.s([bb, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` B ) = %s )' % (ph, BV('B')))
    br = w.s([bb], 'nn0red', '( %s -> B e. RR )' % ph)
    cr = w.s([cc], 'nn0red', '( %s -> C e. RR )' % ph)
    t2r = w.s([], '2re', '2 e. RR')
    t2ra = w.s([t2r], 'a1i', '( %s -> 2 e. RR )' % ph)
    ur = w.s([br, t2ra], 'readdcld', '( %s -> %s e. RR )' % (ph, U))
    n2 = w.s([], '2nn0', '2 e. NN0')
    n2a = w.s([n2], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    n3 = w.s([], '3nn0', '3 e. NN0')
    n3a = w.s([n3], 'a1i', '( %s -> 3 e. NN0 )' % ph)
    qr = w.s([ur, n2a], 'reexpcld', '( %s -> %s e. RR )' % (ph, Q))
    er = w.s([ur, n3a], 'reexpcld', '( %s -> %s e. RR )' % (ph, E3))
    b0 = w.s([bb], 'nn0ge0d', '( %s -> 0 <_ B )' % ph)
    u0 = linarith(w, ph, [b0], '0 <_ %s' % U, leaves={'B': br, '2': t2ra})
    un = b2nn(w, ph, bb)
    u1 = w.s([un], 'nnge1d', '( %s -> 1 <_ %s )' % (ph, U))
    q1 = w.s([ur, n2a, u1], 'expge1d', '( %s -> 1 <_ %s )' % (ph, Q))
    # ( B + 2 ) ^ 3 = ( ( B + 2 ) x. ( ( B + 2 ) ^ 2 ) )
    uc = w.s([ur], 'recnd', '( %s -> %s e. CC )' % (ph, U))
    e3 = w.s([uc, n2a], 'expp1d', '( %s -> ( %s ^ ( 2 + 1 ) ) = ( %s x. %s ) )' % (ph, U, Q, U))
    p21 = w.s([], '2p1e3', '( 2 + 1 ) = 3')
    p21a = w.s([p21], 'a1i', '( %s -> ( 2 + 1 ) = 3 )' % ph)
    e3b = w.s([p21a], 'oveq2d', '( %s -> ( %s ^ ( 2 + 1 ) ) = %s )' % (ph, U, E3))
    e3c = w.s([e3b, e3], 'eqtr3d', '( %s -> %s = ( %s x. %s ) )' % (ph, E3, Q, U))
    c64s = c64(w, ph)
    c64r = w.s([c64s], 'nnred', '( %s -> ; 6 4 e. RR )' % ph)
    c0 = w.s([c64s], 'nnnn0d', '( %s -> ; 6 4 e. NN0 )' % ph)
    c0g = w.s([c0], 'nn0ge0d', '( %s -> 0 <_ ; 6 4 )' % ph)
    s1 = w.s([cr, c64r, ur, u0, le], 'lemul1ad', '( %s -> ( C x. %s ) <_ ( ; 6 4 x. %s ) )' % (ph, U, U))
    one = w.s([], '1re', '1 e. RR')
    onea = w.s([one], 'a1i', '( %s -> 1 e. RR )' % ph)
    t1 = w.s([onea, qr, ur, u0, q1], 'lemul1ad', '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, U, Q, U))
    m1 = w.s([uc, w.inst('mullid')], 'syl', '( %s -> ( 1 x. %s ) = %s )' % (ph, U, U))
    m1c = w.s([m1], 'eqcomd', '( %s -> %s = ( 1 x. %s ) )' % (ph, U, U))
    t2 = w.s([m1c, t1], 'eqbrtrd', '( %s -> %s <_ ( %s x. %s ) )' % (ph, U, Q, U))
    qur = w.s([qr, ur], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (ph, Q, U))
    s2 = w.s([ur, qur, c64r, c0g, t2], 'lemul2ad',
             '( %s -> ( ; 6 4 x. %s ) <_ ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, U, Q, U))
    cur = w.s([cr, ur], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (ph, U))
    c6u = w.s([c64r, ur], 'remulcld', '( %s -> ( ; 6 4 x. %s ) e. RR )' % (ph, U))
    c6qu = w.s([c64r, qur], 'remulcld', '( %s -> ( ; 6 4 x. ( %s x. %s ) ) e. RR )' % (ph, Q, U))
    goal = w.s([cur, c6u, c6qu, s1, s2], 'letrd',
               '( %s -> ( C x. %s ) <_ ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, U, Q, U))
    o1 = w.s([e3c], 'oveq2d', '( %s -> %s = ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, BV('B'), Q, U))
    g2 = w.s([goal, o1], 'breqtrrd', '( %s -> ( C x. %s ) <_ %s )' % (ph, U, BV('B')))
    w.qed([g2, val], 'breqtrrd', '( %s -> ( C x. %s ) <_ ( TMB ` B ) )' % (ph, U))
    return w.run()


def tmbquad():
    lab = 'tmbquad'
    ph = '( B e. NN0 /\\ C e. NN0 /\\ C <_ ; 6 4 )'
    U = '( B + 2 )'
    Q = '( ( B + 2 ) ^ 2 )'
    E3 = '( ( B + 2 ) ^ 3 )'
    w = W(lab, 'A bound quadratic in the operand bit length with a coefficient '
               'at most 64 is within the per-tick budget of the machine layer.  '
               'Lean: ` quad_le_B ` .')
    bb = w.s([], 'simp1', '( %s -> B e. NN0 )' % ph)
    cc = w.s([], 'simp2', '( %s -> C e. NN0 )' % ph)
    le = w.s([], 'simp3', '( %s -> C <_ ; 6 4 )' % ph)
    val = w.s([bb, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` B ) = %s )' % (ph, BV('B')))
    br = w.s([bb], 'nn0red', '( %s -> B e. RR )' % ph)
    cr = w.s([cc], 'nn0red', '( %s -> C e. RR )' % ph)
    t2r = w.s([], '2re', '2 e. RR')
    t2ra = w.s([t2r], 'a1i', '( %s -> 2 e. RR )' % ph)
    ur = w.s([br, t2ra], 'readdcld', '( %s -> %s e. RR )' % (ph, U))
    uc = w.s([ur], 'recnd', '( %s -> %s e. CC )' % (ph, U))
    n2a = w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    n3a = w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ph)
    qr = w.s([ur, n2a], 'reexpcld', '( %s -> %s e. RR )' % (ph, Q))
    qc = w.s([qr], 'recnd', '( %s -> %s e. CC )' % (ph, Q))
    un = b2nn(w, ph, bb)
    u1 = w.s([un], 'nnge1d', '( %s -> 1 <_ %s )' % (ph, U))
    q1 = w.s([ur, n2a, u1], 'expge1d', '( %s -> 1 <_ %s )' % (ph, Q))
    b0 = w.s([bb], 'nn0ge0d', '( %s -> 0 <_ B )' % ph)
    q0 = linarith(w, ph, [q1], '0 <_ %s' % Q, leaves={Q: qr})
    e3 = w.s([uc, n2a], 'expp1d', '( %s -> ( %s ^ ( 2 + 1 ) ) = ( %s x. %s ) )' % (ph, U, Q, U))
    p21a = w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'a1i', '( %s -> ( 2 + 1 ) = 3 )' % ph)
    e3b = w.s([p21a], 'oveq2d', '( %s -> ( %s ^ ( 2 + 1 ) ) = %s )' % (ph, U, E3))
    e3c = w.s([e3b, e3], 'eqtr3d', '( %s -> %s = ( %s x. %s ) )' % (ph, E3, Q, U))
    c64s = c64(w, ph)
    c64r = w.s([c64s], 'nnred', '( %s -> ; 6 4 e. RR )' % ph)
    c0g = w.s([w.s([c64s], 'nnnn0d', '( %s -> ; 6 4 e. NN0 )' % ph)], 'nn0ge0d', '( %s -> 0 <_ ; 6 4 )' % ph)
    s1 = w.s([cr, c64r, qr, q0, le], 'lemul1ad', '( %s -> ( C x. %s ) <_ ( ; 6 4 x. %s ) )' % (ph, Q, Q))
    onea = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % ph)
    t1 = w.s([onea, ur, qr, q0, u1], 'lemul2ad', '( %s -> ( %s x. 1 ) <_ ( %s x. %s ) )' % (ph, Q, Q, U))
    m1 = w.s([qr], 'recnd', '( %s -> %s e. CC )' % (ph, Q))
    m1b = w.s([m1, w.inst('mulrid')], 'syl', '( %s -> ( %s x. 1 ) = %s )' % (ph, Q, Q))
    m1c = w.s([m1b], 'eqcomd', '( %s -> %s = ( %s x. 1 ) )' % (ph, Q, Q))
    t2 = w.s([m1c, t1], 'eqbrtrd', '( %s -> %s <_ ( %s x. %s ) )' % (ph, Q, Q, U))
    qur = w.s([qr, ur], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (ph, Q, U))
    s2 = w.s([qr, qur, c64r, c0g, t2], 'lemul2ad',
             '( %s -> ( ; 6 4 x. %s ) <_ ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, Q, Q, U))
    cqr = w.s([cr, qr], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (ph, Q))
    c6q = w.s([c64r, qr], 'remulcld', '( %s -> ( ; 6 4 x. %s ) e. RR )' % (ph, Q))
    c6qu = w.s([c64r, qur], 'remulcld', '( %s -> ( ; 6 4 x. ( %s x. %s ) ) e. RR )' % (ph, Q, U))
    goal = w.s([cqr, c6q, c6qu, s1, s2], 'letrd',
               '( %s -> ( C x. %s ) <_ ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, Q, Q, U))
    o1 = w.s([e3c], 'oveq2d', '( %s -> %s = ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, BV('B'), Q, U))
    g2 = w.s([goal, o1], 'breqtrrd', '( %s -> ( C x. %s ) <_ %s )' % (ph, Q, BV('B')))
    w.qed([g2, val], 'breqtrrd', '( %s -> ( C x. %s ) <_ ( TMB ` B ) )' % (ph, Q))
    return w.run()


ST7 = '( 2o X. ( ( 2o |_| 1o ) X. ( ( 2o |_| 1o ) X. ( 2o X. ( 2o X. ( 3o X. 2o ) ) ) ) ) )'


def djufin(w, ph, A, B, acl, bcl):
    """( ph -> ( A |_| B ) e. Fin ) from finiteness of A and B"""
    a1 = w.s([acl, w.inst('isfinite')], 'sylib', '( %s -> %s ~< _om )' % (ph, A))
    b1 = w.s([bcl, w.inst('isfinite')], 'sylib', '( %s -> %s ~< _om )' % (ph, B))
    d = w.s([a1, b1, w.inst('djufi')], 'syl2anc', '( %s -> ( %s |_| %s ) ~< _om )' % (ph, A, B))
    return w.s([d, w.inst('isfinite2')], 'syl', '( %s -> ( %s |_| %s ) e. Fin )' % (ph, A, B))


def tmstfi():
    lab = 'tmstfi'
    ph = 'T.'
    w = W(lab, 'The internal state record of the machine layer is a finite set.  '
               'Lean: ` instance : Fintype St ` , through ` St.equivProd ` .')
    f2 = w.s([w.s([], '2onn', '2o e. _om')], 'nnfi' if False else 'a1i', '( %s -> 2o e. _om )' % ph)
    f2b = w.s([f2, w.inst('nnfi')], 'syl', '( %s -> 2o e. Fin )' % ph)
    f3 = w.s([w.s([], '3onn', '3o e. _om')], 'a1i', '( %s -> 3o e. _om )' % ph)
    f3b = w.s([f3, w.inst('nnfi')], 'syl', '( %s -> 3o e. Fin )' % ph)
    f1 = w.s([w.s([], '1onn', '1o e. _om')], 'a1i', '( %s -> 1o e. _om )' % ph)
    f1b = w.s([f1, w.inst('nnfi')], 'syl', '( %s -> 1o e. Fin )' % ph)
    o = djufin(w, ph, '2o', '1o', f2b, f1b)
    x1 = w.s([f3b, f2b, w.inst('xpfi')], 'syl2anc', '( %s -> ( 3o X. 2o ) e. Fin )' % ph)
    x2 = w.s([f2b, x1, w.inst('xpfi')], 'syl2anc', '( %s -> ( 2o X. ( 3o X. 2o ) ) e. Fin )' % ph)
    x3 = w.s([f2b, x2, w.inst('xpfi')], 'syl2anc', '( %s -> ( 2o X. ( 2o X. ( 3o X. 2o ) ) ) e. Fin )' % ph)
    x4 = w.s([o, x3, w.inst('xpfi')], 'syl2anc',
             '( %s -> ( ( 2o |_| 1o ) X. ( 2o X. ( 2o X. ( 3o X. 2o ) ) ) ) e. Fin )' % ph)
    x5 = w.s([o, x4, w.inst('xpfi')], 'syl2anc',
             '( %s -> ( ( 2o |_| 1o ) X. ( ( 2o |_| 1o ) X. ( 2o X. ( 2o X. ( 3o X. 2o ) ) ) ) ) e. Fin )' % ph)
    x6 = w.s([f2b, x5, w.inst('xpfi')], 'syl2anc', '( %s -> %s e. Fin )' % (ph, ST7))
    df = w.s([], 'df-tmst', 'TMSt = %s' % ST7)
    dfa = w.s([df], 'a1i', '( %s -> TMSt = %s )' % (ph, ST7))
    fin = w.s([dfa, x6], 'eqeltrd', '( %s -> TMSt e. Fin )' % ph)
    w.qed([fin], 'mptru', 'TMSt e. Fin')
    return w.run()


def tmgamfn():
    lab = 'tmgamfn'
    w = W(lab, 'The stack-alphabet function of the machine layer is a function '
               'on the eight stack indices.  Lean (TM/Frag.lean): '
               '` abbrev K := Fin 8 ` , ` abbrev Gamma : K -> Type := fun _ => Gamma\' ` .')
    ge = w.s([], 'gammaex', "Gamma' e. _V")
    fn = w.s([ge, w.inst('fnconstg')], 'ax-mp', "( ( 0 ..^ 8 ) X. { Gamma' } ) Fn ( 0 ..^ 8 )")
    df = w.s([], 'df-tmgam', "TMGam = ( ( 0 ..^ 8 ) X. { Gamma' } )")
    bi = w.s([df], 'fneq1i', "( TMGam Fn ( 0 ..^ 8 ) <-> ( ( 0 ..^ 8 ) X. { Gamma' } ) Fn ( 0 ..^ 8 ) )")
    w.qed([bi, fn], 'mpbir', 'TMGam Fn ( 0 ..^ 8 )')
    return w.run()


def tmgamfv():
    lab = 'tmgamfv'
    ph = 'K e. ( 0 ..^ 8 )'
    w = W(lab, 'Every stack of the machine layer carries the alphabet '
               "` Gamma' ` .")
    kk = w.s([], 'id', '( %s -> K e. ( 0 ..^ 8 ) )' % ph)
    ge = w.s([], 'gammaex', "Gamma' e. _V")
    gea = w.s([ge], 'a1i', "( %s -> Gamma' e. _V )" % ph)
    fv = w.s([gea, kk, w.inst('fvconst2g')], 'syl2anc',
             "( %s -> ( ( ( 0 ..^ 8 ) X. { Gamma' } ) ` K ) = Gamma' )" % ph)
    df = w.s([], 'df-tmgam', "TMGam = ( ( 0 ..^ 8 ) X. { Gamma' } )")
    dfa = w.s([df], 'a1i', "( %s -> TMGam = ( ( 0 ..^ 8 ) X. { Gamma' } ) )" % ph)
    fe = w.s([dfa], 'fveq1d', "( %s -> ( TMGam ` K ) = ( ( ( 0 ..^ 8 ) X. { Gamma' } ) ` K ) )" % ph)
    w.qed([fe, fv], 'eqtrd', "( %s -> ( TMGam ` K ) = Gamma' )" % ph)
    return w.run()


def tmgamdm():
    lab = 'tmgamdm'
    w = W(lab, 'The eight stack indices of the machine layer.')
    fn = w.s([], 'tmgamfn', 'TMGam Fn ( 0 ..^ 8 )')
    dm = w.s([fn, w.inst('fndm')], 'ax-mp', 'dom TMGam = ( 0 ..^ 8 )')
    fz = w.s([], 'fzofi', '( 0 ..^ 8 ) e. Fin')
    w.qed([dm, fz], 'eqeltri', 'dom TMGam e. Fin')
    return w.run()


if __name__ == '__main__':
    if want('tmbval'): tmbval()
    if want('tmbcl'): tmbcl()
    if want('tmb1'): tmb1()
    if want('tmbmono'): tmbmono()
    if want('tmblin'): tmblin()
    if want('tmbquad'): tmbquad()
    if want('tmstfi'): tmstfi()
    if want('tmgamfn'): tmgamfn()
    if want('tmgamfv'): tmgamfv()
    if want('tmgamdm'): tmgamdm()
