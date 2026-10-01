"""Sortie A4c, batch 11: the divisor enumeration is exactly the divisor set
(Lean: AlgScan.divisorsOf_spec)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

def DIVS(x): return '{ m e. ( 1 ... %s ) | m || %s }' % (x, x)
def FM(S, q='Q'): return '( d e. %s |-> ( d x. %s ) )' % (S, q)

# ------------------------------------------------------------------ divseteqi
if not only or 'divseteqi' in only:
    w = W('divseteqi', 'The divisor set depends only on the number.')
    A = 'A = B'
    e1 = w.s([], 'oveq2', '( %s -> ( 1 ... A ) = ( 1 ... B ) )' % A)
    e2 = w.s([], 'breq2', '( %s -> ( m || A <-> m || B ) )' % A)
    w.qed([e1, e2], 'rabeqbidv', '( %s -> %s = %s )' % (A, DIVS('A'), DIVS('B')))
    run(w)

# ------------------------------------------------------------------ divset1
if not only or 'divset1' in only:
    w = W('divset1', 'The divisors of one.')
    fz = w.s([w.s([], '1z', '1 e. ZZ'), w.inst('fzsn')], 'ax-mp', '( 1 ... 1 ) = { 1 }')
    r1 = w.s([fz, w.inst('rabeq')], 'ax-mp', '%s = { m e. { 1 } | m || 1 }' % DIVS('1'))
    d11 = w.s([w.s([], '1z', '1 e. ZZ'), w.inst('iddvds')], 'ax-mp', '1 || 1')
    rs = w.s([w.s([], 'breq1', '( m = 1 -> ( m || 1 <-> 1 || 1 ) )')], 'ralsng',
             '( 1 e. _V -> ( A. m e. { 1 } m || 1 <-> 1 || 1 ) )')
    rs2 = w.s([w.s([], '1ex', '1 e. _V'), rs], 'ax-mp', '( A. m e. { 1 } m || 1 <-> 1 || 1 )')
    ralv = w.s([d11, rs2], 'mpbir', 'A. m e. { 1 } m || 1')
    eq = w.s([ralv, w.inst('rabid2')], 'mpbir', '{ 1 } = { m e. { 1 } | m || 1 }')
    w.qed([r1, w.s([eq], 'eqcomi', '{ m e. { 1 } | m || 1 } = { 1 }')], 'eqtri', '%s = { 1 }' % DIVS('1'))
    run(w)

# ------------------------------------------------------------------ wrdprmnn
if not only or 'wrdprmnn' in only:
    w = W('wrdprmnn', 'The product of a word of primes is a positive integer.')
    A = '( W e. Word NN0 /\\ A. q e. ran W q e. Prime )'
    ww = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % A)
    pr = w.s([], 'simpr', '( %s -> A. q e. ran W q e. Prime )' % A)
    one = w.s([w.s([], 'prmnn', '( q e. Prime -> q e. NN )'), w.inst('nnge1')], 'syl', '( q e. Prime -> 1 <_ q )')
    gen = w.s([w.s([one], 'a1i', '( q e. ran W -> ( q e. Prime -> 1 <_ q ) )')], 'rgen',
              'A. q e. ran W ( q e. Prime -> 1 <_ q )')
    imp = w.s([gen, w.inst('ralim')], 'ax-mp', '( A. q e. ran W q e. Prime -> A. q e. ran W 1 <_ q )')
    g2 = w.s([pr, w.s([imp], 'a1i', '( %s -> ( A. q e. ran W q e. Prime -> A. q e. ran W 1 <_ q ) )' % A)], 'mpd',
             '( %s -> A. q e. ran W 1 <_ q )' % A)
    w.qed([ww, g2, w.inst('algprodnn')], 'syl2anc', '( %s -> %s e. NN )' % (A, PRD('W')))
    run(w)

# ------------------------------------------------------------------ wrdprmnd
if not only or 'wrdprmnd' in only:
    w = W('wrdprmnd', 'A prime outside a word of primes divides none of its entries.')
    A = '( W e. Word NN0 /\\ P e. Prime /\\ -. P e. ran W )'
    B = '( %s /\\ q e. ran W )' % A
    qw = w.s([], 'simpr', '( %s -> q e. ran W )' % B)
    pne = w.s([], 'simpl3', '( %s -> -. P e. ran W )' % B)
    pp = w.s([], 'simpl2', '( %s -> P e. Prime )' % B)
    qne = w.s([qw, pne, w.inst('nelne2')], 'syl2anc', '( %s -> q =/= P )' % B)
    C = '( %s /\\ q e. Prime )' % B
    q2 = w.s([w.s([], 'simpr', '( %s -> q e. Prime )' % C), w.inst('prmuz2')], 'syl', '( %s -> q e. ( ZZ>= ` 2 ) )' % C)
    bi = w.s([q2, w.s([pp], 'adantr', '( %s -> P e. Prime )' % C), w.inst('dvdsprm')], 'syl2anc',
             '( %s -> ( q || P <-> q = P ) )' % C)
    nd = w.s([bi, w.s([w.s([qne], 'adantr', '( %s -> q =/= P )' % C), w.inst('neneqd')], 'syl',
                      '( %s -> -. q = P )' % C)], 'mtbird', '( %s -> -. q || P )' % C)
    w.qed([w.s([nd], 'ex', '( %s -> ( q e. Prime -> -. q || P ) )' % B)], 'ralimdva',
          '( %s -> ( A. q e. ran W q e. Prime -> A. q e. ran W -. q || P ) )' % A)
    run(w)

# ------------------------------------------------------------------ mulallrn
if not only or 'mulallrn' in only:
    w = W('mulallrn', 'The range of the multiplied word is the image of the range (Lean: List.map).')
    A = '( Q e. NN0 /\\ W e. Word NN0 )'
    MA = '( 1st ` ( Q MulAll W ) )'
    qq = w.s([], 'simpl', '( %s -> Q e. NN0 )' % A)
    ww = w.s([], 'simpr', '( %s -> W e. Word NN0 )' % A)
    mcl = w.s([w.s([qq, ww, w.inst('mulallcl')], 'syl2anc', '( %s -> ( Q MulAll W ) e. ( Word NN0 X. NN0 ) )' % A),
               w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (A, MA))
    # ran MA C_ ran FM
    B = '( %s /\\ x e. ran %s )' % (A, MA)
    b = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (B, f))
    xn = w.s([b(mcl, '%s e. Word NN0' % MA), w.s([], 'simpr', '( %s -> x e. ran %s )' % (B, MA))], 'jca',
             '( %s -> ( %s e. Word NN0 /\\ x e. ran %s ) )' % (B, MA, MA))
    xn0 = w.s([xn, w.inst('algwrdrn')], 'syl', '( %s -> x e. NN0 )' % B)
    mel = w.s([w.s([w.s([b(qq, 'Q e. NN0'), xn0], 'jca', '( %s -> ( Q e. NN0 /\\ x e. NN0 ) )' % B),
                    b(ww, 'W e. Word NN0')], 'jca', '( %s -> ( ( Q e. NN0 /\\ x e. NN0 ) /\\ W e. Word NN0 ) )' % B),
               w.inst('mulallel')], 'syl', '( %s -> ( x e. ran %s <-> E. d e. ran W x = ( d x. Q ) ) )' % (B, MA))
    rex = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (B, MA)), mel], 'mpbid',
              '( %s -> E. d e. ran W x = ( d x. Q ) )' % B)
    inf = w.s([rex, w.s([w.s([xn0], 'elexd', '( %s -> x e. _V )' % B), w.inst('mulimel')], 'syl',
                        '( %s -> ( x e. ran %s <-> E. d e. ran W x = ( d x. Q ) ) )' % (B, FM('ran W')))], 'mpbird',
              '( %s -> x e. ran %s )' % (B, FM('ran W')))
    ss1 = w.s([w.s([inf], 'ex', '( %s -> ( x e. ran %s -> x e. ran %s ) )' % (A, MA, FM('ran W')))], 'ssrdv',
              '( %s -> ran %s C_ ran %s )' % (A, MA, FM('ran W')))
    # ran FM C_ ran MA
    D = '( %s /\\ x e. ran %s )' % (A, FM('ran W'))
    d = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D, f))
    xex = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (D, FM('ran W')))], 'elexd', '( %s -> x e. _V )' % D)
    rex2 = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (D, FM('ran W'))),
                w.s([xex, w.inst('mulimel')], 'syl',
                    '( %s -> ( x e. ran %s <-> E. d e. ran W x = ( d x. Q ) ) )' % (D, FM('ran W')))], 'mpbid',
               '( %s -> E. d e. ran W x = ( d x. Q ) )' % D)
    cbv = w.s([w.s([w.s([], 'oveq1', '( d = y -> ( d x. Q ) = ( y x. Q ) )')], 'eqeq2d',
                   '( d = y -> ( x = ( d x. Q ) <-> x = ( y x. Q ) ) )')], 'cbvrexv',
              '( E. d e. ran W x = ( d x. Q ) <-> E. y e. ran W x = ( y x. Q ) )')
    rex3 = w.s([rex2, w.s([cbv], 'a1i', '( %s -> ( E. d e. ran W x = ( d x. Q ) <-> E. y e. ran W x = ( y x. Q ) ) )' % D)],
               'mpbid', '( %s -> E. y e. ran W x = ( y x. Q ) )' % D)
    E = '( %s /\\ y e. ran W )' % D
    e = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E, f))
    yn = w.s([w.s([e(d(ww, 'W e. Word NN0'), 'W e. Word NN0'), w.s([], 'simpr', '( %s -> y e. ran W )' % E)], 'jca',
                  '( %s -> ( W e. Word NN0 /\\ y e. ran W ) )' % E), w.inst('algwrdrn')], 'syl',
             '( %s -> y e. NN0 )' % E)
    F = '( %s /\\ x = ( y x. Q ) )' % E
    f = lambda st, f_: w.s([st], 'adantr', '( %s -> %s )' % (F, f_))
    xyq = w.s([], 'simpr', '( %s -> x = ( y x. Q ) )' % F)
    xn2 = w.s([xyq, w.s([f(yn, 'y e. NN0'), f(e(d(qq, 'Q e. NN0'), 'Q e. NN0'), 'Q e. NN0')], 'nn0mulcld',
                        '( %s -> ( y x. Q ) e. NN0 )' % F)], 'eqeltrd', '( %s -> x e. NN0 )' % F)
    mel2 = w.s([w.s([w.s([f(e(d(qq, 'Q e. NN0'), 'Q e. NN0'), 'Q e. NN0'), xn2], 'jca',
                         '( %s -> ( Q e. NN0 /\\ x e. NN0 ) )' % F),
                     f(e(d(ww, 'W e. Word NN0'), 'W e. Word NN0'), 'W e. Word NN0')], 'jca',
                    '( %s -> ( ( Q e. NN0 /\\ x e. NN0 ) /\\ W e. Word NN0 ) )' % F), w.inst('mulallel')], 'syl',
               '( %s -> ( x e. ran %s <-> E. d e. ran W x = ( d x. Q ) ) )' % (F, MA))
    rsp = w.s([w.s([w.s([], 'simpr', '( %s -> y e. ran W )' % E)], 'adantr', '( %s -> y e. ran W )' % F), xyq], 'jca',
              '( %s -> ( y e. ran W /\\ x = ( y x. Q ) ) )' % F)
    rspv = w.s([rsp, w.s([w.s([w.s([], 'oveq1', '( d = y -> ( d x. Q ) = ( y x. Q ) )')], 'eqeq2d',
                              '( d = y -> ( x = ( d x. Q ) <-> x = ( y x. Q ) ) )')], 'rspcev',
                         '( ( y e. ran W /\\ x = ( y x. Q ) ) -> E. d e. ran W x = ( d x. Q ) )')], 'syl',
               '( %s -> E. d e. ran W x = ( d x. Q ) )' % F)
    inm = w.s([rspv, mel2], 'mpbird', '( %s -> x e. ran %s )' % (F, MA))
    ss2 = w.s([w.s([w.s([rex3, w.s([w.s([inm], 'ex', '( %s -> ( x = ( y x. Q ) -> x e. ran %s ) )' % (E, MA))], 'rexlimdva',
                                   '( %s -> ( E. y e. ran W x = ( y x. Q ) -> x e. ran %s ) )' % (D, MA))], 'mpd',
                        '( %s -> x e. ran %s )' % (D, MA))], 'ex',
                   '( %s -> ( x e. ran %s -> x e. ran %s ) )' % (A, FM('ran W'), MA))], 'ssrdv',
              '( %s -> ran %s C_ ran %s )' % (A, FM('ran W'), MA))
    w.qed([ss1, ss2], 'eqssd', '( %s -> ran %s = ran %s )' % (A, MA, FM('ran W')))
    run(w)

# ================================================================= divisorsofspec
CSV = '( <" P "> ++ V )'
def DV(x): return '( 1st ` ( DivisorsOf ` %s ) )' % x
MA = '( 1st ` ( P MulAll %s ) )' % DV('V')
CAT = '( %s ++ %s )' % (DV('V'), MA)
HYP = lambda x: "( Fun `' %s /\\ A. q e. ran %s q e. Prime )" % (x, x)
CONC = lambda x: "( Fun `' %s /\\ ran %s = %s )" % (DV(x), DV(x), DIVS(PRD(x)))
PHI = '( %s -> %s )' % (HYP('s'), CONC('s'))

def _b(w, goal):
    v = w.s([], 'divisorsof0', '( DivisorsOf ` (/) ) = <. <" 1 "> , 0 >.')
    s1e = w.s([w.s([w.s([], 's1cli', '<" 1 "> e. Word _V')], 'elexi', '<" 1 "> e. _V')], 'id', '<" 1 "> e. _V')
    w.lines.pop()
    s1e = w.s([w.s([], 's1cli', '<" 1 "> e. Word _V')], 'elexi', '<" 1 "> e. _V')
    o = w.s([s1e, w.s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. <" 1 "> , 0 >. ) = <" 1 ">')
    dv = w.s([w.s([v], 'fveq2i', '%s = ( 1st ` <. <" 1 "> , 0 >. )' % DV('(/)')), o], 'eqtri', '%s = <" 1 ">' % DV('(/)'))
    n1 = w.s([], '1nn0', '1 e. NN0')
    fu1 = w.s([n1, w.inst('algndps1')], 'ax-mp', "Fun `' <\" 1 \">")
    fu = w.s([w.s([dv], 'cnveqi', "`' %s = `' <\" 1 \">" % DV('(/)')), fu1], 'eqeltrri', None)
    w.lines.pop()
    fueq = w.s([dv], 'cnveqi', "`' %s = `' <\" 1 \">" % DV('(/)'))
    fubi = w.s([fueq], 'funeqi', "( Fun `' %s <-> Fun `' <\" 1 \"> )" % DV('(/)'))
    fu = w.s([fu1, fubi], 'mpbir', "Fun `' %s" % DV('(/)'))
    rn = w.s([w.s([dv], 'rneqi', 'ran %s = ran <" 1 ">' % DV('(/)')),
              w.s([w.s([], '1ex', '1 e. _V'), w.inst('s1rn')], 'ax-mp', 'ran <" 1 "> = { 1 }')], 'eqtri',
             'ran %s = { 1 }' % DV('(/)'))
    p0 = w.s([], 'algprod0', '%s = 1' % PRD('(/)'))
    de = w.s([p0, w.inst('divseteqi')], 'ax-mp', '%s = %s' % (DIVS(PRD('(/)')), DIVS('1')))
    d1 = w.s([], 'divset1', '%s = { 1 }' % DIVS('1'))
    rr = w.s([rn, w.s([w.s([de, d1], 'eqtri', '%s = { 1 }' % DIVS(PRD('(/)')))], 'eqcomi',
                      '{ 1 } = %s' % DIVS(PRD('(/)')))], 'eqtri', 'ran %s = %s' % (DV('(/)'), DIVS(PRD('(/)'))))
    w.qed([w.s([w.s([fu, rr], 'pm3.2i', CONC('(/)'))], 'a1i', '( %s -> %s )' % (HYP('(/)'), CONC('(/)')))], 'id', None)
    w.lines.pop()
    w.qed([w.s([fu, rr], 'pm3.2i', CONC('(/)'))], 'a1i', goal)

def _s(w, A, ih, co):
    U = '( %s /\\ %s )' % (A, HYP(CSV))
    up = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    vv = up(w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A), 'V e. Word NN0')
    pp = up(w.s([], 'simp2', '( %s -> P e. NN0 )' % A), 'P e. NN0')
    ihs = up(w.s([], 'simp3', '( %s -> %s )' % (A, ih)), ih)
    hyp = w.s([], 'simpr', '( %s -> %s )' % (U, HYP(CSV)))
    pex = w.s([pp], 'elexd', '( %s -> P e. _V )' % U)
    rcs = w.s([pp, vv, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (U, CSV))
    rc, _ = ralcons(w, U, 'q', 'q e. Prime', 'P e. Prime', 'V', rcs, pex,
                    w.s([], 'eleq1', '( q = P -> ( q e. Prime <-> P e. Prime ) )'))
    prs = w.s([w.s([hyp], 'simprd', '( %s -> A. q e. ran %s q e. Prime )' % (U, CSV)), rc], 'mpbid',
              '( %s -> ( P e. Prime /\\ A. q e. ran V q e. Prime ) )' % U)
    pp2 = w.s([prs], 'simpld', '( %s -> P e. Prime )' % U)
    vpr = w.s([prs], 'simprd', '( %s -> A. q e. ran V q e. Prime )' % U)
    ndc = w.s([pp, vv, w.inst('algndpcs')], 'syl2anc',
              "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (U, CSV))
    nds = w.s([w.s([hyp], 'simpld', "( %s -> Fun `' %s )" % (U, CSV)), ndc], 'mpbid',
              "( %s -> ( -. P e. ran V /\\ Fun `' V ) )" % U)
    pnv = w.s([nds], 'simpld', '( %s -> -. P e. ran V )' % U)
    fuv = w.s([nds], 'simprd', "( %s -> Fun `' V )" % U)
    got = w.s([ihs, w.s([fuv, vpr], 'jca', '( %s -> %s )' % (U, HYP('V')))], 'mpd', '( %s -> %s )' % (U, CONC('V')))
    fudv = w.s([got], 'simpld', "( %s -> Fun `' %s )" % (U, DV('V')))
    rndv = w.s([got], 'simprd', '( %s -> ran %s = %s )' % (U, DV('V'), DIVS(PRD('V'))))
    pn = w.s([pp2, w.inst('prmnn')], 'syl', '( %s -> P e. NN )' % U)
    pz = w.s([pn], 'nnzd', '( %s -> P e. ZZ )' % U)
    prdn = w.s([w.s([vv, vpr], 'jca', '( %s -> ( V e. Word NN0 /\\ A. q e. ran V q e. Prime ) )' % U),
                w.inst('wrdprmnn')], 'syl', '( %s -> %s e. NN )' % (U, PRD('V')))
    prdz = w.s([prdn], 'nnzd', '( %s -> %s e. ZZ )' % (U, PRD('V')))
    # P does not divide the product
    nda = w.s([w.s([w.s([vv, pp2, pnv], '3jca', '( %s -> ( V e. Word NN0 /\\ P e. Prime /\\ -. P e. ran V ) )' % U),
                    w.inst('wrdprmnd')], 'syl',
                   '( %s -> ( A. q e. ran V q e. Prime -> A. q e. ran V -. q || P ) )' % U), vpr], 'mpd',
              '( %s -> A. q e. ran V -. q || P )' % U)
    cop = w.s([nda, w.s([w.s([w.s([vv, pn], 'jca', '( %s -> ( V e. Word NN0 /\\ P e. NN ) )' % U), vpr], 'jca',
                              '( %s -> ( ( V e. Word NN0 /\\ P e. NN ) /\\ A. q e. ran V q e. Prime ) )' % U),
                         w.inst('coprimetodvd')], 'syl',
                        '( %s -> ( A. q e. ran V -. q || P <-> ( P gcd %s ) = 1 ) )' % (U, PRD('V')))], 'mpbid',
              '( %s -> ( P gcd %s ) = 1 )' % (U, PRD('V')))
    pndvd = w.s([cop, w.s([w.s([pp2, prdz], 'jca', '( %s -> ( P e. Prime /\\ %s e. ZZ ) )' % (U, PRD('V'))),
                           w.inst('coprm')], 'syl',
                          '( %s -> ( -. P || %s <-> ( P gcd %s ) = 1 ) )' % (U, PRD('V'), PRD('V')))], 'mpbird',
                '( %s -> -. P || %s )' % (U, PRD('V')))
    # the shape of the divisor enumeration at a cons
    dcl = w.s([vv, w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` V ) e. ( Word NN0 X. NN0 ) )' % U)
    dv1 = w.s([dcl, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (U, DV('V')))
    dv2 = w.s([dcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( DivisorsOf ` V ) ) e. NN0 )' % U)
    mcl = w.s([pp, dv1, w.inst('mulallcl')], 'syl2anc', '( %s -> ( P MulAll %s ) e. ( Word NN0 X. NN0 ) )' % (U, DV('V')))
    ma1 = w.s([mcl, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (U, MA))
    ma2 = w.s([mcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( P MulAll %s ) ) e. NN0 )' % (U, DV('V')))
    SUM = '( ( 2nd ` ( DivisorsOf ` V ) ) + ( 2nd ` ( P MulAll %s ) ) )' % DV('V')
    cs = w.s([pp, vv, w.inst('divisorsofcs')], 'syl2anc',
             '( %s -> ( DivisorsOf ` %s ) = <. %s , %s >. )' % (U, CSV, CAT, SUM))
    catw = w.s([dv1, ma1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (U, CAT))
    sumn = w.s([dv2, ma2], 'nn0addcld', '( %s -> %s e. NN0 )' % (U, SUM))
    dvcs = projeq(w, U, '( DivisorsOf ` %s )' % CSV, cs, CAT, SUM,
                  w.s([catw], 'elexd', '( %s -> %s e. _V )' % (U, CAT)),
                  w.s([sumn], 'elexd', '( %s -> %s e. _V )' % (U, SUM)), 1)
    # the range
    rnc = w.s([dv1, ma1, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran %s u. ran %s ) )' % (U, CAT, DV('V'), MA))
    rnm = w.s([pp, dv1, w.inst('mulallrn')], 'syl2anc',
              '( %s -> ran %s = ran %s )' % (U, MA, FM('ran %s' % DV('V'), 'P')))
    rnm2 = w.s([rnm, w.s([w.s([rndv], 'mpteq1d', '( %s -> %s = %s )' % (U, FM('ran %s' % DV('V'), 'P'), FM(DIVS(PRD('V')), 'P')))],
                         'rneqd', '( %s -> ran %s = ran %s )' % (U, FM('ran %s' % DV('V'), 'P'), FM(DIVS(PRD('V')), 'P')))],
               'eqtrd', '( %s -> ran %s = ran %s )' % (U, MA, FM(DIVS(PRD('V')), 'P')))
    dpm = w.s([w.s([pp2, prdn], 'jca', '( %s -> ( P e. Prime /\\ %s e. NN ) )' % (U, PRD('V'))), w.inst('divprmmul')], 'syl',
              '( %s -> %s = ( %s u. ran %s ) )' % (U, DIVS('( P x. %s )' % PRD('V')), DIVS(PRD('V')), FM(DIVS(PRD('V')), 'P')))
    pcs = w.s([pp, vv, w.inst('algprodcs')], 'syl2anc', '( %s -> %s = ( P x. %s ) )' % (U, PRD(CSV), PRD('V')))
    dseq = w.s([pcs, w.inst('divseteqi')], 'syl', '( %s -> %s = %s )' % (U, DIVS(PRD(CSV)), DIVS('( P x. %s )' % PRD('V'))))
    un = w.s([rndv, rnm2], 'uneq12d', '( %s -> ( ran %s u. ran %s ) = ( %s u. ran %s ) )'
             % (U, DV('V'), MA, DIVS(PRD('V')), FM(DIVS(PRD('V')), 'P')))
    rnall = w.s([w.s([w.s([dvcs], 'rneqd', '( %s -> ran %s = ran %s )' % (U, DV(CSV), CAT)), rnc], 'eqtrd',
                     '( %s -> ran %s = ( ran %s u. ran %s ) )' % (U, DV(CSV), DV('V'), MA)),
                 w.s([un, w.s([dpm], 'eqcomd',
                              '( %s -> ( %s u. ran %s ) = %s )' % (U, DIVS(PRD('V')), FM(DIVS(PRD('V')), 'P'), DIVS('( P x. %s )' % PRD('V'))))],
                     'eqtrd', '( %s -> ( ran %s u. ran %s ) = %s )' % (U, DV('V'), MA, DIVS('( P x. %s )' % PRD('V'))))], 'eqtrd',
                '( %s -> ran %s = %s )' % (U, DV(CSV), DIVS('( P x. %s )' % PRD('V'))))
    rnfin = w.s([rnall, w.s([dseq], 'eqcomd', '( %s -> %s = %s )' % (U, DIVS('( P x. %s )' % PRD('V')), DIVS(PRD(CSV))))],
                'eqtrd', '( %s -> ran %s = %s )' % (U, DV(CSV), DIVS(PRD(CSV))))
    # duplicate-freeness
    fuma = w.s([w.s([w.s([pn, dv1], 'jca', '( %s -> ( P e. NN /\\ %s e. Word NN0 ) )' % (U, DV('V'))), fudv], 'jca',
                    "( %s -> ( ( P e. NN /\\ %s e. Word NN0 ) /\\ Fun `' %s ) )" % (U, DV('V'), DV('V'))),
                w.inst('mulallndp')], 'syl', "( %s -> Fun `' %s )" % (U, MA))
    #   disjointness
    X1 = '( %s /\\ x e. ran %s )' % (U, MA)
    x1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (X1, f))
    xfm = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (X1, MA)),
               x1(rnm, 'ran %s = ran %s' % (MA, FM('ran %s' % DV('V'), 'P')))], 'eleqtrd',
              '( %s -> x e. ran %s )' % (X1, FM('ran %s' % DV('V'), 'P')))
    xex = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (X1, MA))], 'elexd', '( %s -> x e. _V )' % X1)
    rx = w.s([xfm, w.s([xex, w.inst('mulimel')], 'syl',
                       '( %s -> ( x e. ran %s <-> E. d e. ran %s x = ( d x. P ) ) )' % (X1, FM('ran %s' % DV('V'), 'P'), DV('V')))],
             'mpbid', '( %s -> E. d e. ran %s x = ( d x. P ) )' % (X1, DV('V')))
    cbv = w.s([w.s([w.s([], 'oveq1', '( d = y -> ( d x. P ) = ( y x. P ) )')], 'eqeq2d',
                   '( d = y -> ( x = ( d x. P ) <-> x = ( y x. P ) ) )')], 'cbvrexv',
              '( E. d e. ran %s x = ( d x. P ) <-> E. y e. ran %s x = ( y x. P ) )' % (DV('V'), DV('V')))
    rx2 = w.s([rx, w.s([cbv], 'a1i',
                       '( %s -> ( E. d e. ran %s x = ( d x. P ) <-> E. y e. ran %s x = ( y x. P ) ) )' % (X1, DV('V'), DV('V')))],
              'mpbid', '( %s -> E. y e. ran %s x = ( y x. P ) )' % (X1, DV('V')))
    Y1 = '( %s /\\ y e. ran %s )' % (X1, DV('V'))
    y1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Y1, f))
    yn = w.s([w.s([y1(x1(dv1, '%s e. Word NN0' % DV('V')), '%s e. Word NN0' % DV('V')),
                   w.s([], 'simpr', '( %s -> y e. ran %s )' % (Y1, DV('V')))], 'jca',
                  '( %s -> ( %s e. Word NN0 /\\ y e. ran %s ) )' % (Y1, DV('V'), DV('V'))), w.inst('algwrdrn')], 'syl',
             '( %s -> y e. NN0 )' % Y1)
    Z1 = '( %s /\\ x = ( y x. P ) )' % Y1
    z1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Z1, f))
    xyp = w.s([], 'simpr', '( %s -> x = ( y x. P ) )' % Z1)
    pdx = w.s([w.s([w.s([w.s([yn], 'nn0zd', '( %s -> y e. ZZ )' % Y1)], 'adantr', '( %s -> y e. ZZ )' % Z1),
                    z1(y1(x1(pz, 'P e. ZZ'), 'P e. ZZ'), 'P e. ZZ')], 'jca',
                   '( %s -> ( y e. ZZ /\\ P e. ZZ ) )' % Z1), w.inst('dvdsmul2')], 'syl',
              '( %s -> P || ( y x. P ) )' % Z1)
    pdx2 = w.s([pdx, w.s([xyp], 'eqcomd', '( %s -> ( y x. P ) = x )' % Z1)], 'breqtrd', '( %s -> P || x )' % Z1)
    W1 = '( %s /\\ x e. ran %s )' % (Z1, DV('V'))
    w1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (W1, f))
    xdv = w.s([w.s([], 'simpr', '( %s -> x e. ran %s )' % (W1, DV('V'))),
               w1(z1(y1(x1(rndv, 'ran %s = %s' % (DV('V'), DIVS(PRD('V')))), 'ran %s = %s' % (DV('V'), DIVS(PRD('V')))),
                     'ran %s = %s' % (DV('V'), DIVS(PRD('V')))), 'ran %s = %s' % (DV('V'), DIVS(PRD('V'))))], 'eleqtrd',
              '( %s -> x e. %s )' % (W1, DIVS(PRD('V'))))
    sbx = w.s([], 'breq1', '( m = x -> ( m || %s <-> x || %s ) )' % (PRD('V'), PRD('V')))
    erx = w.s([w.s([sbx], 'elrab', '( x e. %s <-> ( x e. ( 1 ... %s ) /\\ x || %s ) )' % (DIVS(PRD('V')), PRD('V'), PRD('V')))],
              'a1i', '( %s -> ( x e. %s <-> ( x e. ( 1 ... %s ) /\\ x || %s ) ) )' % (W1, DIVS(PRD('V')), PRD('V'), PRD('V')))
    xspl = w.s([xdv, erx], 'mpbid', '( %s -> ( x e. ( 1 ... %s ) /\\ x || %s ) )' % (W1, PRD('V'), PRD('V')))
    xzw = w.s([w.s([xspl], 'simpld', '( %s -> x e. ( 1 ... %s ) )' % (W1, PRD('V'))), w.inst('elfzelz')], 'syl',
              '( %s -> x e. ZZ )' % W1)
    ppW = w1(z1(y1(x1(pz, 'P e. ZZ'), 'P e. ZZ'), 'P e. ZZ'), 'P e. ZZ')
    prdW = w1(z1(y1(x1(prdz, '%s e. ZZ' % PRD('V')), '%s e. ZZ' % PRD('V')), '%s e. ZZ' % PRD('V')), '%s e. ZZ' % PRD('V'))
    trr = w.s([w.s([w.s([ppW, xzw, prdW], '3jca', '( %s -> ( P e. ZZ /\\ x e. ZZ /\\ %s e. ZZ ) )' % (W1, PRD('V'))),
                    w.inst('dvdstr')], 'syl', '( %s -> ( ( P || x /\\ x || %s ) -> P || %s ) )' % (W1, PRD('V'), PRD('V'))),
               w.s([w1(pdx2, 'P || x'), w.s([xspl], 'simprd', '( %s -> x || %s )' % (W1, PRD('V')))], 'jca',
                   '( %s -> ( P || x /\\ x || %s ) )' % (W1, PRD('V')))], 'mpd', '( %s -> P || %s )' % (W1, PRD('V')))
    nel = w.s([trr, w1(z1(y1(x1(pndvd, '-. P || %s' % PRD('V')), '-. P || %s' % PRD('V')), '-. P || %s' % PRD('V')),
                       '-. P || %s' % PRD('V'))], 'pm2.65da', '( %s -> -. x e. ran %s )' % (Z1, DV('V')))
    nel2 = w.s([rx2, w.s([w.s([nel], 'ex', '( %s -> ( x = ( y x. P ) -> -. x e. ran %s ) )' % (Y1, DV('V')))], 'rexlimdva',
                         '( %s -> ( E. y e. ran %s x = ( y x. P ) -> -. x e. ran %s ) )' % (X1, DV('V'), DV('V')))], 'mpd',
               '( %s -> -. x e. ran %s )' % (X1, DV('V')))
    dj = w.s([w.s([nel2], 'ralrimiva', '( %s -> A. x e. ran %s -. x e. ran %s )' % (U, MA, DV('V'))),
              w.s([w.s([], 'disjr', '( ( ran %s i^i ran %s ) = (/) <-> A. x e. ran %s -. x e. ran %s )' % (DV('V'), MA, MA, DV('V')))],
                  'a1i', '( %s -> ( ( ran %s i^i ran %s ) = (/) <-> A. x e. ran %s -. x e. ran %s ) )' % (U, DV('V'), MA, MA, DV('V')))],
             'mpbird', '( %s -> ( ran %s i^i ran %s ) = (/) )' % (U, DV('V'), MA))
    fucat = w.s([w.s([w.s([dv1, ma1], 'jca', '( %s -> ( %s e. Word NN0 /\\ %s e. Word NN0 ) )' % (U, DV('V'), MA)),
                      w.s([w.s([fudv, fuma], 'jca', "( %s -> ( Fun `' %s /\\ Fun `' %s ) )" % (U, DV('V'), MA)), dj], 'jca',
                          "( %s -> ( ( Fun `' %s /\\ Fun `' %s ) /\\ ( ran %s i^i ran %s ) = (/) ) )" % (U, DV('V'), MA, DV('V'), MA))],
                     'jca', "( %s -> ( ( %s e. Word NN0 /\\ %s e. Word NN0 ) /\\ ( ( Fun `' %s /\\ Fun `' %s ) /\\ ( ran %s i^i ran %s ) = (/) ) ) )"
                     % (U, DV('V'), MA, DV('V'), MA, DV('V'), MA)), w.inst('algndpccr')], 'syl',
                "( %s -> Fun `' %s )" % (U, CAT))
    fufin = w.s([w.s([w.s([dvcs], 'cnveqd', "( %s -> `' %s = `' %s )" % (U, DV(CSV), CAT))], 'funeqd',
                     "( %s -> ( Fun `' %s <-> Fun `' %s ) )" % (U, DV(CSV), CAT)), fucat], 'mpbird',
                "( %s -> Fun `' %s )" % (U, DV(CSV)))
    w.qed([w.s([fufin, rnfin], 'jca', '( %s -> %s )' % (U, CONC(CSV)))], 'ex', '( %s -> %s )' % (A, co))

family(run, 'divofsp', PHI, _b, _s, prods=('s',),
       desc='The divisor enumeration is exactly the divisor set, as algwrdi delivers it.', only=only)

if not only or 'divisorsofspec' in only:
    w = W('divisorsofspec', 'The divisor enumeration is duplicate-free and enumerates the divisors (Lean: divisorsOf_spec).')
    A = "( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime )"
    ww = w.s([], 'simp1', '( %s -> W e. Word NN0 )' % A)
    fu = w.s([], 'simp2', "( %s -> Fun `' W )" % A)
    pr = w.s([], 'simp3', '( %s -> A. q e. ran W q e. Prime )' % A)
    w.qed([w.s([ww, w.inst('divofsp')], 'syl', '( %s -> %s )' % (A, '( %s -> %s )' % (HYP('W'), CONC('W')))),
           w.s([fu, pr], 'jca', '( %s -> %s )' % (A, HYP('W')))], 'mpd', '( %s -> %s )' % (A, CONC('W')))
    run(w)
