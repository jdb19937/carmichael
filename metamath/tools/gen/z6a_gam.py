"""Sortie Z6a, block A: Gamma on the real segment, the explicit strip constant,
the line moments (z6gamle1, z6gamre, z6gam1632, z6gmom, z6gmoml)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z6alib import *
from cl import Closure, lift, split_imp, formula_of
import lin
from lin import linarith, lineq, nlinarith
import num

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def cn(w, step):
    return split_imp(formula_of(w, step))[1]


def ind(w, ante, E, er, egt):
    """( ante -> E e. ( CC \\ ( ZZ \\ NN ) ) ) for a real E > 0"""
    st = mkst(w, ante)
    ec = st([er], 'recnd', '%s e. CC' % E)
    re = st([er], 'rered', '( Re ` %s ) = %s' % (E, E))
    rgt = st([egt, re], 'breqtrrd', '0 < ( Re ` %s )' % E)
    return sy2(w, ante, ec, rgt, 'zrenn', '%s e. %s' % (E, DG)), ec


# ---------------------------------------------------------------- z6gamle1
def z6gamle1():
    w = W('z6gamle1', 'On ` ( 0 , 1 ] ` , ` _G ( Y ) Y <_ 1 ` : the ` M = 0 ` case of ~ z5dgzp (the empty '
          'Euler product), with ` _G ( Y ) > 0 ` ( ~ gamrrp ).')
    A = STATEMENTS['z6gamle1'].split(' -> ')[0][2:]
    st = mkst(w, A)
    yr = st([], 'simp1', 'Y e. RR'); ygt = st([], 'simp2', '0 < Y'); yle = st([], 'simp3', 'Y <_ 1')
    ydg, yc = ind(w, A, 'Y', yr, ygt)
    re = st([yr], 'rered', '( Re ` Y ) = Y')
    rege = st([st([st([], '0red', '0 e. RR'), yr, ygt], 'ltled', '0 <_ Y'), re], 'breqtrrd', '0 <_ ( Re ` Y )')
    rele = st([re, yle], 'eqbrtrd', '( Re ` Y ) <_ 1')
    h = st([ydg, st([rege, rele], 'jca', '( 0 <_ ( Re ` Y ) /\\ ( Re ` Y ) <_ 1 )')], 'jca',
           '( Y e. %s /\\ ( 0 <_ ( Re ` Y ) /\\ ( Re ` Y ) <_ 1 ) )' % DG)
    n0 = a1c(w, A, '0nn0', '0 e. NN0')
    PR = 'prod_ k e. ( 1 ... 0 ) ( ( k + ( Re ` Y ) ) / ( abs ` ( Y + k ) ) )'
    P = '( ( _G ` Y ) x. Y )'
    gz = sy2(w, A, h, n0, 'z5dgzp', '( abs ` %s ) <_ %s' % (P, PR))
    pe = w.s([w.s([w.s([], 'fz10', '( 1 ... 0 ) = (/)'), w.inst('prodeq1')], 'ax-mp',
                  '%s = prod_ k e. (/) ( ( k + ( Re ` Y ) ) / ( abs ` ( Y + k ) ) )' % PR),
              w.s([], 'prod0', 'prod_ k e. (/) ( ( k + ( Re ` Y ) ) / ( abs ` ( Y + k ) ) ) = 1')], 'eqtri', '%s = 1' % PR)
    gz1 = st([gz, w.s([pe], 'a1i', '( %s -> %s = 1 )' % (A, PR))], 'breqtrd', '( abs ` %s ) <_ 1' % P)
    grp = sy2(w, A, yr, ygt, 'gamrrp', '( _G ` Y ) e. RR+')
    yrp = st([yr, ygt], 'elrpd', 'Y e. RR+')
    prp = st([grp, yrp], 'rpmulcld', '%s e. RR+' % P)
    ab = st([st([prp], 'rpred', '%s e. RR' % P), st([prp], 'rpge0d', '0 <_ %s' % P)], 'absidd', '( abs ` %s ) = %s' % (P, P))
    w.qed([ab, gz1], 'eqbrtrrd', '( %s -> %s <_ 1 )' % (A, P))
    return w


# ---------------------------------------------------------------- z6gamre
def z6gamre():
    w = W('z6gamre', 'Gamma on ` ( 0 , 3 ] ` : ` _G ( X ) <_ 1 / X + 2 ` .  On ` ( 0 , 1 ] ` from ~ z6gamle1 , '
          'on ` ( 1 , 3 ] ` by the functional equation ~ gamp1 once or twice.  Turns ~ gamvb into '
          'the explicit strip constant ~ z6gam1632 .')
    A = '( X e. RR /\\ 0 < X /\\ X <_ 3 )'
    GOAL = '( _G ` X ) <_ ( ( 1 / X ) + 2 )'
    st = mkst(w, A)
    xr = st([], 'simp1', 'X e. RR'); xgt = st([], 'simp2', '0 < X'); xle = st([], 'simp3', 'X <_ 3')
    xrp = st([xr, xgt], 'elrpd', 'X e. RR+')
    ixr = st([st([xrp], 'rpreccld', '( 1 / X ) e. RR+')], 'rpred', '( 1 / X ) e. RR')
    ixgt = st([st([xrp], 'rpreccld', '( 1 / X ) e. RR+')], 'rpgt0d', '0 < ( 1 / X )')
    gxr = st([sy2(w, A, xr, xgt, 'gamrrp', '( _G ` X ) e. RR+')], 'rpred', '( _G ` X ) e. RR')

    def cl(a):
        c = Closure(w, a, {'X': ('RR', lift(w, xr, a))})
        c.leaf('( 1 / X )', 'RR', lift(w, ixr, a))
        c.leaf('( _G ` X )', 'RR', lift(w, gxr, a))
        return c

    def le1(a, Y, yr, ygt, yle):
        """( a -> ( ( _G ` Y ) x. Y ) <_ 1 )"""
        s = mkst(w, a)
        return s([s([yr, ygt, yle], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (Y, Y, Y)), w.inst('z6gamle1')], 'syl',
                 '( ( _G ` %s ) x. %s ) <_ 1' % (Y, Y))

    def fe(a, Y, yr, ygt, Z, zeq):
        """( a -> ( _G ` Z ) = ( ( _G ` Y ) x. Y ) ) from zeq: ( a -> ( Y + 1 ) = Z )"""
        s = mkst(w, a)
        ydg, yc = ind(w, a, Y, yr, ygt)
        g = sy(w, a, ydg, 'gamp1', '( _G ` ( %s + 1 ) ) = ( ( _G ` %s ) x. %s )' % (Y, Y, Y))
        return s([s([zeq], 'fveq2d', '( _G ` ( %s + 1 ) ) = ( _G ` %s )' % (Y, Z)), g], 'eqtr3d', '( _G ` %s ) = ( ( _G ` %s ) x. %s )' % (Z, Y, Y))

    # case X <_ 1
    a1_ = '( %s /\\ X <_ 1 )' % A
    s1 = mkst(w, a1_)
    l1 = le1(a1_, 'X', lift(w, xr, a1_), lift(w, xgt, a1_), s1([], 'simpr', 'X <_ 1'))
    dv = s1([lift(w, gxr, a1_), s1([], '1red', '1 e. RR'), lift(w, xrp, a1_)], 'lemuldivd',
            '( ( ( _G ` X ) x. X ) <_ 1 <-> ( _G ` X ) <_ ( 1 / X ) )')
    g1 = s1([l1, dv], 'mpbid', '( _G ` X ) <_ ( 1 / X )')
    c1 = linarith(w, a1_, [g1, lift(w, ixgt, a1_)], GOAL, closure=cl(a1_))
    # case 1 < X
    a2 = '( %s /\\ 1 < X )' % A
    s2 = mkst(w, a2)
    X1 = '( X - 1 )'
    x1r = s2([lift(w, xr, a2), s2([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % X1)
    x1eq = s2([s2([lift(w, xr, a2)], 'recnd', 'X e. CC'), s2([], '1cnd', '1 e. CC')], 'npcand', '( %s + 1 ) = X' % X1)
    # case 1 < X <_ 2
    a3 = '( %s /\\ X <_ 2 )' % a2
    s3 = mkst(w, a3)
    cl3 = cl(a3)
    x1r3 = lift(w, x1r, a3)
    x1gt = linarith(w, a3, [lift(w, s2([], 'simpr', '1 < X'), a3)], '0 < %s' % X1, closure=cl3)
    x1le = linarith(w, a3, [s3([], 'simpr', 'X <_ 2')], '%s <_ 1' % X1, closure=cl3)
    l3 = le1(a3, X1, x1r3, x1gt, x1le)
    e3 = fe(a3, X1, x1r3, x1gt, 'X', lift(w, x1eq, a3))
    cl3.leaf('( ( _G ` %s ) x. %s )' % (X1, X1), 'RR', s3([s3([sy2(w, a3, x1r3, x1gt, 'gamrrp', '( _G ` %s ) e. RR+' % X1), s3([x1r3, x1gt], 'elrpd', '%s e. RR+' % X1)], 'rpmulcld',
                                                               '( ( _G ` %s ) x. %s ) e. RR+' % (X1, X1))], 'rpred', '( ( _G ` %s ) x. %s ) e. RR' % (X1, X1)))
    c3 = linarith(w, a3, [e3, l3, lift(w, ixgt, a3)], GOAL, closure=cl3)
    # case 2 < X <_ 3
    a4 = '( %s /\\ 2 < X )' % a2
    s4 = mkst(w, a4)
    cl4 = cl(a4)
    X2 = '( X - 2 )'
    x1r4 = lift(w, x1r, a4)
    x2r = s4([lift(w, xr, a4), a1c(w, a4, '2re', '2 e. RR')], 'resubcld', '%s e. RR' % X2)
    x2gt = linarith(w, a4, [s4([], 'simpr', '2 < X')], '0 < %s' % X2, closure=cl4)
    x2le = linarith(w, a4, [lift(w, xle, a4)], '%s <_ 1' % X2, closure=cl4)
    x1gt4 = linarith(w, a4, [s4([], 'simpr', '2 < X')], '0 < %s' % X1, closure=cl4)
    x2eq = lineq(w, a4, '( %s + 1 )' % X2, X1, closure=Closure(w, a4, {'X': ('RR', lift(w, xr, a4))}))
    l4 = le1(a4, X2, x2r, x2gt, x2le)
    e4a = fe(a4, X2, x2r, x2gt, X1, x2eq)
    G1 = '( _G ` %s )' % X1
    g1r = s4([sy2(w, a4, x1r4, x1gt4, 'gamrrp', '%s e. RR+' % G1)], 'rpred', '%s e. RR' % G1)
    g1le = s4([e4a, l4], 'eqbrtrd', '%s <_ 1' % G1)
    m4 = s4([g1r, s4([], '1red', '1 e. RR'), x1r4, s4([s4([], '0red', '0 e. RR'), x1r4, x1gt4], 'ltled', '0 <_ %s' % X1), g1le], 'lemul1ad',
            '( %s x. %s ) <_ ( 1 x. %s )' % (G1, X1, X1))
    e4 = fe(a4, X1, x1r4, x1gt4, 'X', lift(w, x1eq, a4))
    cl4.leaf('( %s x. %s )' % (G1, X1), 'RR', s4([g1r, x1r4], 'remulcld', '( %s x. %s ) e. RR' % (G1, X1)))
    c4 = linarith(w, a4, [e4, m4, lift(w, xle, a4), lift(w, ixgt, a4)], GOAL, closure=cl4)
    c34 = s2([c3, c4, s2([lift(w, xr, a2), a1c(w, a2, '2re', '2 e. RR'), w.inst('lelttric')], 'syl2anc', '( X <_ 2 \\/ 2 < X )')], 'mpjaodan', GOAL)
    w.qed([c1, c34, st([xr, st([], '1red', '1 e. RR'), w.inst('lelttric')], 'syl2anc', '( X <_ 1 \\/ 1 < X )')], 'mpjaodan', '( %s -> %s )' % (A, GOAL))
    return w


# ---------------------------------------------------------------- z6gam1632
HUND = '( 1 / ; ; 1 0 0 )'
TOP = '( TopOpen ` CCfld )'


def z6gam1632():
    w = W('z6gam1632', 'The Gamma strip bound with an explicit constant: ` | _G ( d ) | <_ 1632 2 ^ ( - | Im d | / 2 ) ` '
          'on ` 1 / 100 <_ Re d <_ 3 ` ( ~ gamvb with ~ z6gamre : ` 16 ( 100 + 2 ) = 1632 ` ).  The hypothesis '
          '` gamlmom.h ` at ` H = 1632 ` .')
    Q = '( d e. CC /\\ ( %s <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 ) )' % HUND
    R = '( Re ` d )'
    st = mkst(w, Q)
    dc = st([], 'simpl', 'd e. CC'); lo = st([], 'simprl', '%s <_ %s' % (HUND, R)); hi = st([], 'simprr', '%s <_ 3' % R)
    rr = st([dc], 'recld', '%s e. RR' % R)
    cl = Closure(w, Q, {})
    cl.leaf(R, 'RR', rr)
    rgt = linarith(w, Q, [lo], '0 < %s' % R, closure=cl)
    rrp = st([rr, rgt], 'elrpd', '%s e. RR+' % R)
    GR_ = '( _G ` %s )' % R
    gre = st([st([rr, rgt, hi], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 3 )' % (R, R, R)), w.inst('z6gamre')], 'syl', '%s <_ ( ( 1 / %s ) + 2 )' % (GR_, R))
    lr = st([st([cl.mem(HUND, 'RR'), cl.gt0(HUND)], 'jca', '( %s e. RR /\\ 0 < %s )' % (HUND, HUND)), st([rr, rgt], 'jca', '( %s e. RR /\\ 0 < %s )' % (R, R)), w.inst('lerec')], 'syl2anc',
            '( %s <_ %s <-> ( 1 / %s ) <_ ( 1 / %s ) )' % (HUND, R, R, HUND))
    r1 = st([lo, lr], 'mpbid', '( 1 / %s ) <_ ( 1 / %s )' % (R, HUND))
    rr1 = st([cl.mem('; ; 1 0 0', 'CC'), cl.ne0('; ; 1 0 0'), w.inst('recrec')], 'syl2anc', '( 1 / %s ) = ; ; 1 0 0' % HUND)
    r2 = st([r1, rr1], 'breqtrd', '( 1 / %s ) <_ ; ; 1 0 0' % R)
    cl.leaf(GR_, 'RR', st([sy2(w, Q, rr, rgt, 'gamrrp', '%s e. RR+' % GR_)], 'rpred', '%s e. RR' % GR_))
    cl.leaf('( 1 / %s )' % R, 'RR', st([st([rrp], 'rpreccld', '( 1 / %s ) e. RR+' % R)], 'rpred', '( 1 / %s ) e. RR' % R))
    A16 = '( ; 1 6 x. %s )' % GR_
    b16 = linarith(w, Q, [gre, r2], '%s <_ ; ; ; 1 6 3 2' % A16, closure=cl)
    AI = '( abs ` ( Im ` d ) )'
    cl.leaf(AI, 'RR', st([st([dc], 'imcld', '( Im ` d ) e. RR')], 'recnd', '( Im ` d ) e. CC') and
            st([st([st([dc], 'imcld', '( Im ` d ) e. RR')], 'recnd', '( Im ` d ) e. CC')], 'abscld', '%s e. RR' % AI))
    E = '( 2 ^c -u ( %s / 2 ) )' % AI
    erp = st([cl.mem('2', 'RR+'), cl.mem('-u ( %s / 2 )' % AI, 'RR')], 'rpcxpcld', '%s e. RR+' % E)
    er = st([erp], 'rpred', '%s e. RR' % E); ege = st([erp], 'rpge0d', '0 <_ %s' % E)
    ddg = sy2(w, Q, dc, rgt, 'zrenn', 'd e. %s' % DG)
    gdr = st([st([ddg, w.inst('gamcl')], 'syl', '( _G ` d ) e. CC')], 'abscld', '( abs ` ( _G ` d ) ) e. RR')
    gv = st([st([dc, rgt, hi], '3jca', '( d e. CC /\\ 0 < %s /\\ %s <_ 3 )' % (R, R)), w.inst('gamvb')], 'syl',
             '( abs ` ( _G ` d ) ) <_ ( %s x. %s )' % (A16, E))
    a16r = cl.mem(A16, 'RR')
    m = st([a16r, cl.mem('; ; ; 1 6 3 2', 'RR'), er, ege, b16], 'lemul1ad', '( %s x. %s ) <_ ( ; ; ; 1 6 3 2 x. %s )' % (A16, E, E))
    t = st([gdr, st([a16r, er], 'remulcld', '( %s x. %s ) e. RR' % (A16, E)), st([cl.mem('; ; ; 1 6 3 2', 'RR'), er], 'remulcld', '( ; ; ; 1 6 3 2 x. %s ) e. RR' % E), gv, m], 'letrd',
           '( abs ` ( _G ` d ) ) <_ ( ; ; ; 1 6 3 2 x. %s )' % E)
    COND = '( %s <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 )' % HUND
    ex = w.s([t], 'ex', '( d e. CC -> ( %s -> ( abs ` ( _G ` d ) ) <_ ( ; ; ; 1 6 3 2 x. %s ) ) )' % (COND, E))
    w.qed([ex], 'rgen', STATEMENTS['z6gam1632'])
    return w


# ---------------------------------------------------------------- z6gmom
def z6gmom():
    w = W('z6gmom', 'The weighted Gamma line moment on ` 1 / 100 <_ C <_ 3 ` with the explicit constant '
          '` 1024 x. 1632 / log 2 ` : ~ gamlmom at ` H = 1632 ` ( ~ z6gam1632 ), integrability by ~ gamlibl .')
    A0 = '( ( C e. RR /\\ %s <_ C /\\ C <_ 3 ) /\\ T e. RR+ )' % HUND
    st = mkst(w, A0)
    x = st([], 'simpl', '( C e. RR /\\ %s <_ C /\\ C <_ 3 )' % HUND)
    t = st([], 'simpr', 'T e. RR+')
    cr = st([x], 'simp1d', 'C e. RR'); clo = st([x], 'simp2d', '%s <_ C' % HUND)
    cl = Closure(w, A0, {'C': ('RR', cr)})
    cgt = linarith(w, A0, [clo], '0 < C', closure=cl)
    h = st([cl.mem('; ; ; 1 6 3 2', 'RR+'), w.s([w.s([], 'z6gam1632', GAMH1632)], 'a1i', '( %s -> %s )' % (A0, GAMH1632))], 'jca',
           '( ; ; ; 1 6 3 2 e. RR+ /\\ %s )' % GAMH1632)
    i = st([st([st([cr, cgt], 'jca', '( C e. RR /\\ 0 < C )'), t], 'jca', '( ( C e. RR /\\ 0 < C ) /\\ T e. RR+ )'), w.inst('gamlibl')], 'syl', '%s e. L^1' % MOMF('C'))
    mom = st([x, t, h, i], 'gamlmom', '%s <_ %s' % (MOM('C'), KG))
    w.qed([i, mom], 'jca', '( %s -> ( %s e. L^1 /\\ %s <_ %s ) )' % (A0, MOMF('C'), MOM('C'), KG))
    return w


# ---------------------------------------------------------------- z6gaml1
N98 = '-u ( ; 9 8 / ; ; 1 0 0 )'
N99 = '-u ( ; 9 9 / ; ; 1 0 0 )'
K5049 = '( ; 5 0 / ; 4 9 )'


def n98eq(w):
    """closed: -u ( 98 / 100 ) = -u ( 49 / 50 )"""
    r = num._reduce_frac(w, 98, 100)
    return w.s([r], 'negeqi', '%s = -u ( ; 4 9 / ; 5 0 )' % N98)


def z6gaml1():
    w = W('z6gaml1', 'The functional equation on the left line ` -1 < Re w <_ -98/100 ` : ` w = C + i U ` lies in the '
          'domain of ` _G ` (its real part is not an integer, ~ btwnnz ), ` w =/= 0 ` , ` _G ( w ) = _G ( w + 1 ) / w ` '
          '( ~ gamp1 ) and ` | _G ( w ) | <_ ( 50 / 49 ) | _G ( w + 1 ) | ` ( ` | w | >_ | C | >_ 98 / 100 ` ).')
    A = '( ( C e. RR /\\ -u 1 < C /\\ C <_ %s ) /\\ U e. RR )' % N98
    WL = '( C + ( _i x. U ) )'
    WL1 = '( ( C + 1 ) + ( _i x. U ) )'
    st = mkst(w, A)
    cr = st([st([], 'simpl', '( C e. RR /\\ -u 1 < C /\\ C <_ %s )' % N98)], 'simp1d', 'C e. RR')
    clo = st([st([], 'simpl', '( C e. RR /\\ -u 1 < C /\\ C <_ %s )' % N98)], 'simp2d', '-u 1 < C')
    chi = st([st([], 'simpl', '( C e. RR /\\ -u 1 < C /\\ C <_ %s )' % N98)], 'simp3d', 'C <_ %s' % N98)
    ur = st([], 'simpr', 'U e. RR')
    cc = st([cr], 'recnd', 'C e. CC'); uc = st([ur], 'recnd', 'U e. CC')
    iu = st([st([], 'ax-icnd' if False else 'ax-icn', '_i e. CC') if False else a1c(w, A, 'ax-icn', '_i e. CC'), uc], 'mulcld', '( _i x. U ) e. CC')
    wc = st([cc, iu], 'addcld', '%s e. CC' % WL)
    rew = sy2(w, A, cr, ur, 'crre', '( Re ` %s ) = C' % WL)
    cl = Closure(w, A, {'C': ('RR', cr)})
    chi = st([chi, a1(w, A, n98eq(w), '%s = -u ( ; 4 9 / ; 5 0 )' % N98)], 'breqtrd', 'C <_ -u ( ; 4 9 / ; 5 0 )')
    # not an integer
    nz = st([st([a1c(w, A, 'neg1z', '-u 1 e. ZZ'), clo, linarith(w, A, [chi], 'C < ( -u 1 + 1 )', closure=cl)], '3jca', '( -u 1 e. ZZ /\\ -u 1 < C /\\ C < ( -u 1 + 1 ) )'),
             w.inst('btwnnz')], 'syl', '-. C e. ZZ')
    Az = '( %s /\\ %s e. ZZ )' % (A, WL)
    sz = mkst(w, Az)
    wz = sz([], 'simpr', '%s e. ZZ' % WL)
    wre = sz([sz([wz], 'zred', '%s e. RR' % WL)], 'rered', '( Re ` %s ) = %s' % (WL, WL))
    ceq = sz([lift(w, rew, Az), wre], 'eqtr3d', 'C = %s' % WL)
    cz = sz([ceq, wz], 'eqeltrd', 'C e. ZZ')
    nwz = st([nz, cz], 'mtand', '-. %s e. ZZ' % WL)
    nwzn = w.s([nwz, w.inst('eldifi')], 'nsyl', '( %s -> -. %s e. ( ZZ \\ NN ) )' % (A, WL))
    wdg = st([wc, nwzn], 'eldifd', '%s e. %s' % (WL, DG))
    # | w | >_ 98 / 100
    cle0 = linarith(w, A, [chi], 'C <_ 0', closure=cl)
    absc = st([cr, cle0], 'absnidd' if False else 'absnidd', '( abs ` C ) = -u C') if False else sy2(w, A, cr, cle0, 'absnid', '( abs ` C ) = -u C')
    rle = sy(w, A, wc, 'absrele', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (WL, WL))
    rle2 = st([st([st([rew], 'fveq2d', '( abs ` ( Re ` %s ) ) = ( abs ` C )' % WL), absc], 'eqtrd', '( abs ` ( Re ` %s ) ) = -u C' % WL), rle], 'eqbrtrrd', '-u C <_ ( abs ` %s )' % WL)
    AW = '( abs ` %s )' % WL
    cl.leaf(AW, 'RR', st([wc], 'abscld', '%s e. RR' % AW))
    wge = linarith(w, A, [rle2, chi], '( ; 4 9 / ; 5 0 ) <_ %s' % AW, closure=cl)
    wgt = linarith(w, A, [wge], '0 < %s' % AW, closure=cl)
    wne = st([wgt, sy(w, A, wc, 'absgt0', '( %s =/= 0 <-> 0 < %s )' % (WL, AW))], 'mpbird', '%s =/= 0' % WL)
    # the functional equation
    g = sy(w, A, wdg, 'gamp1', '( _G ` ( %s + 1 ) ) = ( ( _G ` %s ) x. %s )' % (WL, WL, WL))
    a32 = st([cc, iu, st([], '1cnd', '1 e. CC')], 'add32d', '( %s + 1 ) = %s' % (WL, WL1))
    g1 = st([st([a32], 'fveq2d', '( _G ` ( %s + 1 ) ) = ( _G ` %s )' % (WL, WL1)), g], 'eqtr3d', '( _G ` %s ) = ( ( _G ` %s ) x. %s )' % (WL1, WL, WL))
    gwc = sy(w, A, wdg, 'gamcl', '( _G ` %s ) e. CC' % WL)
    pc = st([gwc, wc], 'mulcld', '( ( _G ` %s ) x. %s ) e. CC' % (WL, WL))
    g1c = st([g1, pc], 'eqeltrd', '( _G ` %s ) e. CC' % WL1)
    dq = st([g1, st([g1c, gwc, wc, wne], 'divmul3d', '( ( ( _G ` %s ) / %s ) = ( _G ` %s ) <-> ( _G ` %s ) = ( ( _G ` %s ) x. %s ) )' % (WL1, WL, WL, WL1, WL, WL))], 'mpbird',
            '( ( _G ` %s ) / %s ) = ( _G ` %s )' % (WL1, WL, WL))
    dq2 = st([dq], 'eqcomd', '( _G ` %s ) = ( ( _G ` %s ) / %s )' % (WL, WL1, WL))
    # the bound
    AG = '( abs ` ( _G ` %s ) )' % WL
    AG1 = '( abs ` ( _G ` %s ) )' % WL1
    am = st([st([g1], 'fveq2d', '%s = ( abs ` ( ( _G ` %s ) x. %s ) )' % (AG1, WL, WL)), sy2(w, A, gwc, wc, 'absmul', '( abs ` ( ( _G ` %s ) x. %s ) ) = ( %s x. %s )' % (WL, WL, AG, AW))], 'eqtrd',
            '%s = ( %s x. %s )' % (AG1, AG, AW))
    agr = st([gwc], 'abscld', '%s e. RR' % AG)
    age = st([gwc], 'absge0d', '0 <_ %s' % AG)
    m = st([cl.mem('( ; 4 9 / ; 5 0 )', 'RR'), st([wc], 'abscld', '%s e. RR' % AW), agr, age, wge], 'lemul2ad', '( %s x. ( ; 4 9 / ; 5 0 ) ) <_ ( %s x. %s )' % (AG, AG, AW))
    cl.leaf(AG, 'RR', agr)
    cl.leaf(AG1, 'RR', st([g1c], 'abscld', '%s e. RR' % AG1))
    cl.leaf('( %s x. %s )' % (AG, AW), 'RR', st([agr, st([wc], 'abscld', '%s e. RR' % AW)], 'remulcld', '( %s x. %s ) e. RR' % (AG, AW)))
    b = linarith(w, A, [m, am], '%s <_ ( %s x. %s )' % (AG, K5049, AG1), closure=cl)
    w.qed([st([wdg, wne], 'jca', '( %s e. %s /\\ %s =/= 0 )' % (WL, DG, WL)), st([dq2, b], 'jca', '( ( _G ` %s ) = ( ( _G ` %s ) / %s ) /\\ %s <_ ( %s x. %s ) )' % (WL, WL1, WL, AG, K5049, AG1))],
          'jca', STATEMENTS['z6gaml1'])
    return w


# ---------------------------------------------------------------- z6gmoml
def z6gmoml():
    w = W('z6gmoml', 'The weighted Gamma line moment on the left line ` -99/100 <_ C <_ -98/100 ` : '
          '` | _G ( C + i u ) | <_ ( 50 / 49 ) | _G ( C + 1 + i u ) | ` ( ~ z6gaml1 , the functional equation '
          'only) and ~ z6gmom at ` C + 1 ` ; integrability from the continuity of ` _G ( C + 1 + i u ) / ( C + i u ) ` '
          'on the closed segment ( ~ gamcnl , ~ divcncf , ~ cniccibl ).')
    A0 = '( ( C e. RR /\\ %s <_ C /\\ C <_ %s ) /\\ T e. RR+ )' % (N99, N98)
    st = mkst(w, A0)
    x3 = st([], 'simpl', '( C e. RR /\\ %s <_ C /\\ C <_ %s )' % (N99, N98))
    cr = st([x3], 'simp1d', 'C e. RR'); clo = st([x3], 'simp2d', '%s <_ C' % N99); chi = st([x3], 'simp3d', 'C <_ %s' % N98)
    trp = st([], 'simpr', 'T e. RR+')
    chi2 = st([chi, a1(w, A0, n98eq(w), '%s = -u ( ; 4 9 / ; 5 0 )' % N98)], 'breqtrd', 'C <_ -u ( ; 4 9 / ; 5 0 )')
    C1 = '( C + 1 )'
    cl = Closure(w, A0, {'C': ('RR', cr), 'T': ('RR+', trp)})
    c1r = cl.mem(C1, 'RR')
    c1lo = linarith(w, A0, [clo], '%s <_ %s' % (HUND, C1), closure=cl)
    c1hi = linarith(w, A0, [chi2], '%s <_ 3' % C1, closure=cl)
    c1gt = linarith(w, A0, [clo], '0 < %s' % C1, closure=cl)
    cgt1 = linarith(w, A0, [clo], '-u 1 < C', closure=cl)
    g = st([st([st([c1r, c1lo, c1hi], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ 3 )' % (C1, HUND, C1, C1)), trp], 'jca',
               '( ( %s e. RR /\\ %s <_ %s /\\ %s <_ 3 ) /\\ T e. RR+ )' % (C1, HUND, C1, C1)), w.inst('z6gmom')], 'syl',
           '( %s e. L^1 /\\ %s <_ %s )' % (MOMF(C1), MOM(C1), KG))
    gi = st([g], 'simpld', '%s e. L^1' % MOMF(C1)); gm = st([g], 'simprd', '%s <_ %s' % (MOM(C1), KG))
    XC = '( -u T [,] T )'; XO = '( -u T (,) T )'
    WU = '( C + ( _i x. u ) )'; W1U = '( %s + ( _i x. u ) )' % C1
    HC = cns('z6gaml1').replace('U', 'u')

    def pt(a, ur):
        """the helper at u under a"""
        s = mkst(w, a)
        h = s([s([s([lift(w, cr, a), lift(w, cgt1, a), lift(w, chi, a)], '3jca', '( C e. RR /\\ -u 1 < C /\\ C <_ %s )' % N98), ur], 'jca',
                 '( ( C e. RR /\\ -u 1 < C /\\ C <_ %s ) /\\ u e. RR )' % N98), w.inst('z6gaml1')], 'syl', HC)
        d = {}
        d['a'] = s([h], 'simpld', '( %s e. %s /\\ %s =/= 0 )' % (WU, DG, WU))
        d['dg'] = s([d['a']], 'simpld', '%s e. %s' % (WU, DG))
        d['ne'] = s([d['a']], 'simprd', '%s =/= 0' % WU)
        d['b'] = s([h], 'simprd', '( ( _G ` %s ) = ( ( _G ` %s ) / %s ) /\\ ( abs ` ( _G ` %s ) ) <_ ( %s x. ( abs ` ( _G ` %s ) ) ) )' % (WU, W1U, WU, WU, K5049, W1U))
        d['eq'] = s([d['b']], 'simpld', '( _G ` %s ) = ( ( _G ` %s ) / %s )' % (WU, W1U, WU))
        d['le'] = s([d['b']], 'simprd', '( abs ` ( _G ` %s ) ) <_ ( %s x. ( abs ` ( _G ` %s ) ) )' % (WU, K5049, W1U))
        d['wc'] = s([d['dg'], w.inst('eldifi')], 'syl', '%s e. CC' % WU)
        d['gc'] = s([d['dg'], w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % WU)
        c1a = lift(w, c1r, a)
        w1c = s([s([c1a], 'recnd', '%s e. CC' % C1), s([a1c(w, a, 'ax-icn', '_i e. CC'), s([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % W1U)
        rew1 = sy2(w, a, c1a, ur, 'crre', '( Re ` %s ) = %s' % (W1U, C1))
        w1dg = sy2(w, a, w1c, s([lift(w, c1gt, a), rew1], 'breqtrrd', '0 < ( Re ` %s )' % W1U), 'zrenn', '%s e. %s' % (W1U, DG))
        d['g1c'] = s([w1dg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % W1U)
        return d
    # continuity on the closed segment
    tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
    ussr = st([ntr, tr, w.inst('iccssre')], 'syl2anc', '%s C_ RR' % XC)
    usscn = st([ussr, a1c(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '%s C_ CC' % XC)
    sscc = a1c(w, A0, 'ssid', 'CC C_ CC')
    keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    gcn1 = st([st([st([c1r, c1gt], 'jca', '( %s e. RR /\\ 0 < %s )' % (C1, C1)), trp], 'jca', '( ( %s e. RR /\\ 0 < %s ) /\\ T e. RR+ )' % (C1, C1)), w.inst('gamcnl')], 'syl',
              '( u e. %s |-> ( _G ` %s ) ) e. ( %s -cn-> CC )' % (XC, W1U, XC))
    idc = st([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( u e. %s |-> u ) e. ( %s -cn-> CC )' % (XC, XC))
    xcst = st([st([cr], 'recnd', 'C e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( u e. %s |-> C ) e. ( %s -cn-> CC )' % (XC, XC))
    icst = st([a1c(w, A0, 'ax-icn', '_i e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( u e. %s |-> _i ) e. ( %s -cn-> CC )' % (XC, XC))
    iu = st([icst, idc], 'mulcncf', '( u e. %s |-> ( _i x. u ) ) e. ( %s -cn-> CC )' % (XC, XC))
    adc = w.s([w.s([keq], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
    MI = '( u e. %s |-> %s )' % (XC, WU)
    micn = st([keq, adc, xcst, iu], 'cncfmpt2f', '%s e. ( %s -cn-> CC )' % (MI, XC))
    Au = '( %s /\\ u e. %s )' % (A0, XC)
    su = mkst(w, Au)
    uru = su([lift(w, ussr, Au), su([], 'simpr', 'u e. %s' % XC)], 'sseldd', 'u e. RR')
    du = pt(Au, uru)
    CC0 = '( CC \\ { 0 } )'
    inn = su([su([du['wc'], du['ne']], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (WU, WU)), w.inst('eldifsn')], 'sylibr', '%s e. %s' % (WU, CC0))
    mif = st([inn, w.s([], 'eqid', '%s = %s' % (MI, MI))], 'fmptd', '%s : %s --> %s' % (MI, XC, CC0))
    mis = st([mif, st([a1c(w, A0, 'difss', '%s C_ CC' % CC0), micn, w.inst('cncfcdm')], 'syl2anc', '( %s e. ( %s -cn-> %s ) <-> %s : %s --> %s )' % (MI, XC, CC0, MI, XC, CC0))], 'mpbird',
             '%s e. ( %s -cn-> %s )' % (MI, XC, CC0))
    QT = '( ( _G ` %s ) / %s )' % (W1U, WU)
    dvc = st([gcn1, mis], 'divcncf', '( u e. %s |-> %s ) e. ( %s -cn-> CC )' % (XC, QT, XC))
    GMAP = '( u e. %s |-> ( _G ` %s ) )' % (XC, WU)
    gcn = st([st([su([du['eq']], 'eqcomd', '%s = ( _G ` %s )' % (QT, WU))], 'mpteq2dva', '( u e. %s |-> %s ) = %s' % (XC, QT, GMAP)), dvc], 'eqeltrrd',
             '%s e. ( %s -cn-> CC )' % (GMAP, XC))
    # the moment integrand on the closed segment (as gamlibl)
    GA = '( abs ` ( _G ` %s ) )' % WU
    QU = '( ( 1 + ( abs ` u ) ) ^ 2 )'
    GMLC = '( %s x. %s )' % (GA, QU)
    abss = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
    absf = w.s([w.s([abss, w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'sselii', 'abs e. ( CC -cn-> CC )')], 'a1i', '( %s -> abs e. ( CC -cn-> CC ) )' % A0)
    gabs = st([absf, gcn], 'cncfmpt1f', '( u e. %s |-> %s ) e. ( %s -cn-> CC )' % (XC, GA, XC))
    absm = st([absf, idc], 'cncfmpt1f', '( u e. %s |-> ( abs ` u ) ) e. ( %s -cn-> CC )' % (XC, XC))
    one = st([a1c(w, A0, 'ax-1cn', '1 e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( u e. %s |-> 1 ) e. ( %s -cn-> CC )' % (XC, XC))
    pl = st([keq, adc, one, absm], 'cncfmpt2f', '( u e. %s |-> ( 1 + ( abs ` u ) ) ) e. ( %s -cn-> CC )' % (XC, XC))
    sq = st([pl, pl], 'mulcncf', '( u e. %s |-> ( ( 1 + ( abs ` u ) ) x. ( 1 + ( abs ` u ) ) ) ) e. ( %s -cn-> CC )' % (XC, XC))
    uc = su([uru], 'recnd', 'u e. CC')
    opr = su([su([], '1red', '1 e. RR'), su([uc], 'abscld', '( abs ` u ) e. RR')], 'readdcld', '( 1 + ( abs ` u ) ) e. RR')
    opc = su([opr], 'recnd', '( 1 + ( abs ` u ) ) e. CC')
    sqv = su([opc], 'sqvald', '%s = ( ( 1 + ( abs ` u ) ) x. ( 1 + ( abs ` u ) ) )' % QU)
    sqm = st([st([sqv], 'mpteq2dva', '( u e. %s |-> %s ) = ( u e. %s |-> ( ( 1 + ( abs ` u ) ) x. ( 1 + ( abs ` u ) ) ) )' % (XC, QU, XC)), sq], 'eqeltrd',
             '( u e. %s |-> %s ) e. ( %s -cn-> CC )' % (XC, QU, XC))
    gml = st([gabs, sqm], 'mulcncf', '( u e. %s |-> %s ) e. ( %s -cn-> CC )' % (XC, GMLC, XC))
    ibl = st([ntr, tr, gml, w.inst('cniccibl')], 'syl3anc', '( u e. %s |-> %s ) e. L^1' % (XC, GMLC))
    gmlc = su([su([su([du['gc']], 'abscld', '%s e. RR' % GA)], 'recnd', '%s e. CC' % GA), su([opc], 'sqcld', '%s e. CC' % QU)], 'mulcld', '%s e. CC' % GMLC)
    fibl = st([a1c(w, A0, 'ioossicc', '%s C_ %s' % (XO, XC)), a1c(w, A0, 'ioombl', '%s e. dom vol' % XO), gmlc, ibl], 'iblss', '%s e. L^1' % MOMF('C'))
    # the bound
    Ao = '( %s /\\ u e. %s )' % (A0, XO)
    so = mkst(w, Ao)
    uro = so([so([], 'simpr', 'u e. %s' % XO), w.inst('elioore')], 'syl', 'u e. RR')
    do = pt(Ao, uro)
    uco = so([uro], 'recnd', 'u e. CC')
    opro = so([so([], '1red', '1 e. RR'), so([uco], 'abscld', '( abs ` u ) e. RR')], 'readdcld', '( 1 + ( abs ` u ) ) e. RR')
    qr = so([opro], 'resqcld', '%s e. RR' % QU); qge = so([opro], 'sqge0d', '0 <_ %s' % QU)
    GA1 = '( abs ` ( _G ` %s ) )' % W1U
    gar = so([do['gc']], 'abscld', '%s e. RR' % GA); ga1r = so([do['g1c']], 'abscld', '%s e. RR' % GA1)
    kr = lift(w, cl.mem(K5049, 'RR'), Ao)
    kgar = so([kr, ga1r], 'remulcld', '( %s x. %s ) e. RR' % (K5049, GA1))
    lm = so([gar, kgar, qr, qge, do['le']], 'lemul1ad', '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (GA, QU, K5049, GA1, QU))
    G1Q = '( %s x. %s )' % (GA1, QU)
    ma = so([so([kr], 'recnd', '%s e. CC' % K5049), so([ga1r], 'recnd', '%s e. CC' % GA1), so([qr], 'recnd', '%s e. CC' % QU)], 'mulassd',
            '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (K5049, GA1, QU, K5049, G1Q))
    lm2 = so([lm, ma], 'breqtrd', '%s <_ ( %s x. %s )' % (GMLC, K5049, G1Q))
    fr = so([gar, qr], 'remulcld', '%s e. RR' % GMLC)
    g1qr = so([ga1r, qr], 'remulcld', '%s e. RR' % G1Q)
    kgr = so([kr, g1qr], 'remulcld', '( %s x. %s ) e. RR' % (K5049, G1Q))
    kc = st([cl.mem(K5049, 'RR')], 'recnd', '%s e. CC' % K5049)
    g1qc = so([g1qr], 'recnd', '%s e. CC' % G1Q)
    kgibl = st([kc, g1qc, gi], 'iblmulc2', '( u e. %s |-> ( %s x. %s ) ) e. L^1' % (XO, K5049, G1Q))
    ITK = 'S. %s ( %s x. %s ) _d u' % (XO, K5049, G1Q)
    i1 = st([fibl, kgibl, fr, kgr, lm2], 'itgle', '%s <_ %s' % (MOM('C'), ITK))
    i2 = st([kc, g1qc, gi], 'itgmulc2', '( %s x. %s ) = %s' % (K5049, MOM(C1), ITK))
    m1r = st([g1qr, gi], 'itgrecl', '%s e. RR' % MOM(C1))
    cl.leaf('( log ` 2 )', 'RR+', st([a1c(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( log ` 2 ) e. RR') and
            st([st([a1c(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( log ` 2 ) e. RR'),
                linarith(w, A0, [a1c(w, A0, 'log2ge', '( 1 / 2 ) <_ ( log ` 2 )')], '0 < ( log ` 2 )',
                         closure=Closure(w, A0, {'( log ` 2 )': ('RR', st([a1c(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( log ` 2 ) e. RR'))}))],
               'elrpd', '( log ` 2 ) e. RR+'))
    kgr0 = cl.mem(KG, 'RR')
    i3 = st([m1r, kgr0, cl.mem(K5049, 'RR'), cl.ge0(K5049), gm], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (K5049, MOM(C1), K5049, KG))
    mr = st([fr, fibl], 'itgrecl', '%s e. RR' % MOM('C'))
    i4 = st([i1, i2], 'breqtrrd', '%s <_ ( %s x. %s )' % (MOM('C'), K5049, MOM(C1)))
    fin = st([mr, st([cl.mem(K5049, 'RR'), m1r], 'remulcld', '( %s x. %s ) e. RR' % (K5049, MOM(C1))), cl.mem(KGL, 'RR'), i4, i3], 'letrd', '%s <_ %s' % (MOM('C'), KGL))
    w.qed([fibl, fin], 'jca', '( %s -> ( %s e. L^1 /\\ %s <_ %s ) )' % (A0, MOMF('C'), MOM('C'), KGL))
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6gamle1, z6gamre, z6gam1632, z6gmom, z6gaml1, z6gmoml]:
        if want(f.__name__):
            run(f())
