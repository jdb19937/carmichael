"""Sortie v4b block 2: the density V of the progression sieve.

V = ( t e. NN |-> prod_ f e. { g e. Prime | g || t } ( 1 / f ) )

progvval  ( L e. NN -> ( V ` L ) = prod_ f e. { g e. Prime | g || L } ( 1 / f ) )
progvcl   ( PH -> V : NN --> RR )
progv1    ( PH -> ( V ` 1 ) = 1 )
progvsqf  ( ( L e. NN /\\ ( mmu ` L ) =/= 0 ) -> ( V ` L ) = ( 1 / L ) )
progvmul  ( PH -> A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> ( V ` ( a x. b ) ) =
            ( ( V ` a ) x. ( V ` b ) ) ) )
progvprm  ( PH -> A. s e. Prime ( s || P -> ( 0 < ( V ` s ) /\\ ( V ` s ) < 1 ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import P, PH, V, mkst

PFG = lambda E: '{ g e. Prime | g || %s }' % E
PFQ = lambda E: '{ q e. Prime | q || %s }' % E
VV = lambda E: 'prod_ f e. %s ( 1 / f )' % PFG(E)
GM = '( g e. Prime |-> ( 1 / g ) )'


def pfgfin(w, st, enn, E):
    """( ante -> { g e. Prime | g || E } e. Fin ) from ( ante -> E e. NN )"""
    q = st([enn, w.inst('pffinq')], 'syl', '%s e. Fin' % PFQ(E))
    cb = w.s([w.s([], 'breq1', '( q = g -> ( q || %s <-> g || %s ) )' % (E, E))], 'cbvrabv',
             '%s = %s' % (PFQ(E), PFG(E)))
    cbd = st([cb], 'a1i', '%s = %s' % (PFQ(E), PFG(E)))
    return st([cbd, q], 'eqeltrrd', '%s e. Fin' % PFG(E))


def recrp(w, ante, var, S):
    """( ( ante /\\ var e. S ) -> ( 1 / var ) e. RR+ ), S a subset of Prime written
    as a rab over Prime"""
    a2 = '( %s /\\ %s e. %s )' % (ante, var, S)
    s2 = mkst(w, a2)
    fel = s2([], 'simpr', '%s e. %s' % (var, S))
    fpr = s2([fel, w.inst('elrabi')], 'syl', '%s e. Prime' % var)
    fnn = s2([fpr, w.inst('prmnn')], 'syl', '%s e. NN' % var)
    frp = s2([fnn, w.inst('nnrp')], 'syl', '%s e. RR+' % var)
    return s2([frp], 'rpreccld', '( 1 / %s ) e. RR+' % var), a2, s2


def progvval():
    w = W('progvval', 'The density of the progression sieve at a positive integer is the '
                      'product of the reciprocals of its prime divisors.')
    ANT = 'L e. NN'
    st = mkst(w, ANT)
    lnn = st([], 'id', 'L e. NN')
    fin = pfgfin(w, st, lnn, 'L')
    rec, a2, s2 = recrp(w, ANT, 'f', PFG('L'))
    recc = s2([rec], 'rpcnd', '( 1 / f ) e. CC')
    cl = st([fin, recc], 'fprodcl', '%s e. CC' % VV('L'))
    ex = st([cl], 'elexd', '%s e. _V' % VV('L'))
    h1 = w.s([], 'breq2', '( t = L -> ( g || t <-> g || L ) )')
    h2 = w.s([h1], 'rabbidv', '( t = L -> %s = %s )' % (PFG('t'), PFG('L')))
    h3 = w.s([h2], 'prodeq1d', '( t = L -> %s = %s )' % (VV('t'), VV('L')))
    mp = w.s([], 'eqid', '%s = %s' % (V, V))
    fv = w.s([h3, mp], 'fvmptg',
             '( ( L e. NN /\\ %s e. _V ) -> ( %s ` L ) = %s )' % (VV('L'), V, VV('L')))
    w.qed([lnn, ex, fv], 'syl2anc', '( %s -> ( %s ` L ) = %s )' % (ANT, V, VV('L')))
    return w


def progvcl():
    w = W('progvcl', 'The density of the progression sieve is a real-valued function on '
                     'the positive integers.')
    st = mkst(w, PH)
    a2 = '( %s /\\ t e. NN )' % PH
    s2 = mkst(w, a2)
    tnn = s2([], 'simpr', 't e. NN')
    fin = pfgfin(w, s2, tnn, 't')
    rec, a3, s3 = recrp(w, a2, 'f', PFG('t'))
    recr = s3([rec], 'rpred', '( 1 / f ) e. RR')
    cl = s2([fin, recr], 'fprodrecl', '%s e. RR' % VV('t'))
    mp = w.s([], 'eqid', '%s = %s' % (V, V))
    w.qed([cl, mp], 'fmptd', '( %s -> %s : NN --> RR )' % (PH, V))
    return w


def progv1():
    w = W('progv1', 'The density of the progression sieve is 1 at 1.')
    st = mkst(w, PH)
    val = st([st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'),
              w.inst('progvval')], 'syl', '( %s ` 1 ) = %s' % (V, VV('1')))
    rg = w.s([w.s([], 'nprmdvds1', '( g e. Prime -> -. g || 1 )')], 'rgen',
             'A. g e. Prime -. g || 1')
    e0 = w.s([], 'rabeq0', '( %s = (/) <-> A. g e. Prime -. g || 1 )' % PFG('1'))
    em = w.s([e0, rg], 'mpbir', '%s = (/)' % PFG('1'))
    emd = st([em], 'a1i', '%s = (/)' % PFG('1'))
    pe = st([emd], 'prodeq1d', '%s = prod_ f e. (/) ( 1 / f )' % VV('1'))
    p0 = st([w.s([], 'prod0', 'prod_ f e. (/) ( 1 / f ) = 1')], 'a1i',
            'prod_ f e. (/) ( 1 / f ) = 1')
    w.qed([val, st([pe, p0], 'eqtrd', '%s = 1' % VV('1'))], 'eqtrd',
          '( %s -> ( %s ` 1 ) = 1 )' % (PH, V))
    return w


def progvsqf():
    w = W('progvsqf', 'The density of the progression sieve at a squarefree positive '
                      'integer is the reciprocal of that integer.')
    ANT = '( L e. NN /\\ ( mmu ` L ) =/= 0 )'
    st = mkst(w, ANT)
    lnn = st([], 'simpl', 'L e. NN')
    val = st([lnn, w.inst('progvval')], 'syl', '( %s ` L ) = %s' % (V, VV('L')))
    fin = pfgfin(w, st, lnn, 'L')
    rec, a2, s2 = recrp(w, ANT, 'f', PFG('L'))
    s2b = mkst(w, a2)
    fel = s2b([], 'simpr', 'f e. %s' % PFG('L'))
    fpr = s2b([fel, w.inst('elrabi')], 'syl', 'f e. Prime')
    fnn = s2b([fpr, w.inst('prmnn')], 'syl', 'f e. NN')
    fcc = s2b([fnn], 'nncnd', 'f e. CC')
    fne = s2b([fnn], 'nnne0d', 'f =/= 0')
    one = s2b([], '1cnd', '1 e. CC')
    div = st([fin, one, fcc, fne], 'fproddiv',
             '%s = ( prod_ f e. %s 1 / prod_ f e. %s f )' % (VV('L'), PFG('L'), PFG('L')))
    dsj = st([fin], 'olcd',
             '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (PFG('L'), PFG('L')))
    num = st([dsj, w.inst('prod1')], 'syl', 'prod_ f e. %s 1 = 1' % PFG('L'))
    sq = st([], 'id', ANT)
    den0 = st([sq, w.inst('sqfprodid')], 'syl', 'prod_ p e. %s p = L' % PFQ('L'))
    cbp = w.s([w.s([], 'id', '( p = f -> p = f )')], 'cbvprodv',
              'prod_ p e. %s p = prod_ f e. %s f' % (PFQ('L'), PFQ('L')))
    cbpd = st([cbp], 'a1i', 'prod_ p e. %s p = prod_ f e. %s f' % (PFQ('L'), PFQ('L')))
    cbr = w.s([w.s([], 'breq1', '( q = g -> ( q || L <-> g || L ) )')], 'cbvrabv',
              '%s = %s' % (PFQ('L'), PFG('L')))
    cbrd = st([cbr], 'a1i', '%s = %s' % (PFQ('L'), PFG('L')))
    cbe = st([cbrd], 'prodeq1d', 'prod_ f e. %s f = prod_ f e. %s f' % (PFQ('L'), PFG('L')))
    den = st([st([cbpd, cbe], 'eqtrd',
                 'prod_ p e. %s p = prod_ f e. %s f' % (PFQ('L'), PFG('L'))),
              den0], 'eqtr3d', 'prod_ f e. %s f = L' % PFG('L'))
    e1 = st([num, den], 'oveq12d',
            '( prod_ f e. %s 1 / prod_ f e. %s f ) = ( 1 / L )' % (PFG('L'), PFG('L')))
    w.qed([val, st([div, e1], 'eqtrd', '%s = ( 1 / L )' % VV('L'))], 'eqtrd',
          '( %s -> ( %s ` L ) = ( 1 / L ) )' % (ANT, V))
    return w


def gmprod(w, st, ante, E):
    """( ante -> prod_ p e. PFQ( E ) ( GM ` p ) = VV( E ) ), given ( ante -> E e. NN )"""
    a2 = '( %s /\\ p e. %s )' % (ante, PFQ(E))
    s2 = mkst(w, a2)
    pel = s2([], 'simpr', 'p e. %s' % PFQ(E))
    ppr = s2([pel, w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = s2([ppr, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = s2([pnn, w.inst('nnrp')], 'syl', 'p e. RR+')
    prc = s2([s2([prp], 'rpreccld', '( 1 / p ) e. RR+')], 'rpcnd', '( 1 / p ) e. CC')
    pex = s2([prc], 'elexd', '( 1 / p ) e. _V')
    gv0 = w.s([w.s([], 'oveq2', '( g = p -> ( 1 / g ) = ( 1 / p ) )'),
               w.s([], 'eqid', '%s = %s' % (GM, GM))], 'fvmptg',
              '( ( p e. Prime /\\ ( 1 / p ) e. _V ) -> ( %s ` p ) = ( 1 / p ) )' % GM)
    gv = s2([ppr, pex, w.s([gv0], 'a1i',
             '( %s -> ( ( p e. Prime /\\ ( 1 / p ) e. _V ) -> ( %s ` p ) = ( 1 / p ) ) )'
             % (a2, GM))], 'mp2and', '( %s ` p ) = ( 1 / p )' % GM)
    e1 = st([gv], 'prodeq2dv',
            'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 / p )' % (PFQ(E), GM, PFQ(E)))
    cb = w.s([w.s([], 'oveq2', '( p = f -> ( 1 / p ) = ( 1 / f ) )')], 'cbvprodv',
             'prod_ p e. %s ( 1 / p ) = prod_ f e. %s ( 1 / f )' % (PFQ(E), PFQ(E)))
    cbd = st([cb], 'a1i',
             'prod_ p e. %s ( 1 / p ) = prod_ f e. %s ( 1 / f )' % (PFQ(E), PFQ(E)))
    cbr = w.s([w.s([], 'breq1', '( q = g -> ( q || %s <-> g || %s ) )' % (E, E))], 'cbvrabv',
              '%s = %s' % (PFQ(E), PFG(E)))
    cbe = st([st([cbr], 'a1i', '%s = %s' % (PFQ(E), PFG(E)))], 'prodeq1d',
             'prod_ f e. %s ( 1 / f ) = %s' % (PFQ(E), VV(E)))
    return st([e1, st([cbd, cbe], 'eqtrd',
                      'prod_ p e. %s ( 1 / p ) = %s' % (PFQ(E), VV(E)))], 'eqtrd',
              'prod_ p e. %s ( %s ` p ) = %s' % (PFQ(E), GM, VV(E)))


def progvmul():
    w = W('progvmul', 'The density of the progression sieve is multiplicative.')
    ANT = '( a e. NN /\\ b e. NN /\\ ( a gcd b ) = 1 )'
    st = mkst(w, ANT)
    ann = st([], 'simp1', 'a e. NN')
    bnn = st([], 'simp2', 'b e. NN')
    abn = st([ann, bnn], 'nnmulcld', '( a x. b ) e. NN')
    # G : Prime --> CC
    ag = '( %s /\\ g e. Prime )' % ANT
    sg = mkst(w, ag)
    gpr = sg([], 'simpr', 'g e. Prime')
    gnn = sg([gpr, w.inst('prmnn')], 'syl', 'g e. NN')
    grp = sg([gnn, w.inst('nnrp')], 'syl', 'g e. RR+')
    grc = sg([sg([grp], 'rpreccld', '( 1 / g ) e. RR+')], 'rpcnd', '( 1 / g ) e. CC')
    gf = st([grc, w.s([], 'eqid', '%s = %s' % (GM, GM))], 'fmptd', '%s : Prime --> CC' % GM)
    hyp = st([], 'id', ANT)
    pm = st([hyp, gf, w.inst('pfprodmul')], 'syl2anc',
            'prod_ p e. %s ( %s ` p ) = ( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) )'
            % (PFQ('( a x. b )'), GM, PFQ('a'), GM, PFQ('b'), GM))
    gab = gmprod(w, st, ANT, '( a x. b )')
    ga = gmprod(w, st, ANT, 'a')
    gb = gmprod(w, st, ANT, 'b')
    vab = st([abn, w.inst('progvval')], 'syl', '( %s ` ( a x. b ) ) = %s' % (V, VV('( a x. b )')))
    va = st([ann, w.inst('progvval')], 'syl', '( %s ` a ) = %s' % (V, VV('a')))
    vb = st([bnn, w.inst('progvval')], 'syl', '( %s ` b ) = %s' % (V, VV('b')))
    rhs = st([st([ga, va], 'eqtr4d',
                 'prod_ p e. %s ( %s ` p ) = ( %s ` a )' % (PFQ('a'), GM, V)),
              st([gb, vb], 'eqtr4d',
                 'prod_ p e. %s ( %s ` p ) = ( %s ` b )' % (PFQ('b'), GM, V))], 'oveq12d',
             '( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) ) = ( ( %s ` a ) x. ( %s ` b ) )'
             % (PFQ('a'), GM, PFQ('b'), GM, V, V))
    lhs = st([gab, vab], 'eqtr4d',
             'prod_ p e. %s ( %s ` p ) = ( %s ` ( a x. b ) )' % (PFQ('( a x. b )'), GM, V))
    core = st([st([lhs, pm], 'eqtr3d',
                  '( %s ` ( a x. b ) ) = ( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) )'
                  % (V, PFQ('a'), GM, PFQ('b'), GM)), rhs], 'eqtrd',
               '( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) )' % (V, V, V))
    ex = w.s([core], '3expia',
             '( ( a e. NN /\\ b e. NN ) -> ( ( a gcd b ) = 1 -> ( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) ) )'
             % (V, V, V))
    rg = w.s([ex], 'rgen2',
             'A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> ( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) )'
             % (V, V, V))
    w.qed([rg], 'a1i',
          '( %s -> A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> ( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) ) )'
          % (PH, V, V, V))
    return w


def progvprm():
    w = W('progvprm', 'The density of the progression sieve is strictly between 0 and 1 '
                      'at a prime.')
    ANT = 's e. Prime'
    st = mkst(w, ANT)
    spr = st([], 'id', 's e. Prime')
    snn = st([spr, w.inst('prmnn')], 'syl', 's e. NN')
    ssq = st([spr, w.inst('sqfprm')], 'syl', '( mmu ` s ) =/= 0')
    val = st([snn, ssq, w.inst('progvsqf')], 'syl2anc', '( %s ` s ) = ( 1 / s )' % V)
    srp = st([snn, w.inst('nnrp')], 'syl', 's e. RR+')
    rrp = st([srp], 'rpreccld', '( 1 / s ) e. RR+')
    pos = st([rrp, w.inst('rpgt0')], 'syl', '0 < ( 1 / s )')
    sre = st([srp], 'rpred', 's e. RR')
    sgt = st([srp, w.inst('rpgt0')], 'syl', '0 < s')
    gt1 = st([spr, w.inst('prmgt1')], 'syl', '1 < s')
    rg = st([sre, sgt, w.inst('recgt1')], 'syl2anc', '( 1 < s <-> ( 1 / s ) < 1 )')
    lt1 = st([rg, gt1], 'mpbid', '( 1 / s ) < 1')
    p2 = st([pos, val], 'breqtrrd', '0 < ( %s ` s )' % V)
    l2 = st([val, lt1], 'eqbrtrd', '( %s ` s ) < 1' % V)
    j = st([p2, l2], 'jca', '( 0 < ( %s ` s ) /\\ ( %s ` s ) < 1 )' % (V, V))
    ad = w.s([j], 'a1d',
             '( s e. Prime -> ( s || %s -> ( 0 < ( %s ` s ) /\\ ( %s ` s ) < 1 ) ) )' % (P, V, V))
    rgn = w.s([ad], 'rgen',
              'A. s e. Prime ( s || %s -> ( 0 < ( %s ` s ) /\\ ( %s ` s ) < 1 ) )' % (P, V, V))
    w.qed([rgn], 'a1i',
          '( %s -> A. s e. Prime ( s || %s -> ( 0 < ( %s ` s ) /\\ ( %s ` s ) < 1 ) ) )'
          % (PH, P, V, V))
    return w


def main(names=None):
    fns = {'progvval': progvval, 'progvcl': progvcl, 'progv1': progv1,
           'progvsqf': progvsqf, 'progvmul': progvmul, 'progvprm': progvprm}
    order = ['progvval', 'progvcl', 'progv1', 'progvsqf', 'progvmul', 'progvprm']
    ok = True
    for nm in (names or order):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
