"""Sortie C1 section 3: shift_lines_residue (the line-shift identity with a
residue), in lint form with the improper integrals given as rlim hypotheses."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

LO = '( A + ( _i x. -u t ) )'
UR = '( B + ( _i x. t ) )'
LR = '( B + ( _i x. -u t ) )'
UL = '( A + ( _i x. t ) )'
C1 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (UR, LO)
C2 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (LO, UR)
BOT = LINT('F', LO, LR); RIG = LINT('F', LR, UR)
TOP = LINT('F', UR, UL); LEF = LINT('F', UL, LO)
RAWC = '( ( %s + %s ) + ( %s + %s ) )' % (LINT('F', LO, C1), LINT('F', C1, UR), LINT('F', UR, C2), LINT('F', C2, LO))
TREE = '( ( %s + %s ) + ( %s + %s ) )' % (BOT, RIG, TOP, LEF)
PH = 'ph'; PS = '( ph /\\ t e. S )'


def corners(w):
    """steps for the corner rewrite; returns the step ( PS -> TREE = K )"""
    ar = w.s(['1'], 'adantr', '( %s -> A e. RR )' % PS)
    br = w.s(['2'], 'adantr', '( %s -> B e. RR )' % PS)
    fv = w.s(['3'], 'adantr', '( %s -> F e. V )' % PS)
    ssr = w.s(['5'], 'adantr', '( %s -> S C_ RR )' % PS)
    tS = w.s([], 'simpr', '( %s -> t e. S )' % PS)
    tr = w.s([ssr, tS], 'sseldd', '( %s -> t e. RR )' % PS)
    ntr = w.s([tr, w.inst('renegcl')], 'syl', '( %s -> -u t e. RR )' % PS)
    ac = w.s([ar], 'recnd', '( %s -> A e. CC )' % PS)
    bc = w.s([br], 'recnd', '( %s -> B e. CC )' % PS)
    tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % PS)
    ntc = w.s([ntr], 'recnd', '( %s -> -u t e. CC )' % PS)
    ic = closed(w, PS, 'ax-icn', '_i e. CC')
    it = w.s([ic, tc], 'mulcld', '( %s -> ( _i x. t ) e. CC )' % PS)
    int_ = w.s([ic, ntc], 'mulcld', '( %s -> ( _i x. -u t ) e. CC )' % PS)
    loc = w.s([ac, int_], 'addcld', '( %s -> %s e. CC )' % (PS, LO))
    urc = w.s([bc, it], 'addcld', '( %s -> %s e. CC )' % (PS, UR))
    reur = w.s([br, tr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = B )' % (PS, UR))
    imlo = w.s([ar, ntr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = -u t )' % (PS, LO))
    relo = w.s([ar, ntr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = A )' % (PS, LO))
    imur = w.s([br, tr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = t )' % (PS, UR))
    c1e = w.s([reur, w.s([imlo], 'oveq2d', '( %s -> ( _i x. ( Im ` %s ) ) = ( _i x. -u t ) )' % (PS, LO))],
              'oveq12d', '( %s -> %s = %s )' % (PS, C1, LR))
    c2e = w.s([relo, w.s([imur], 'oveq2d', '( %s -> ( _i x. ( Im ` %s ) ) = ( _i x. t ) )' % (PS, UR))],
              'oveq12d', '( %s -> %s = %s )' % (PS, C2, UL))
    rv = w.s([fv, loc, urc, w.inst('rectintval')], 'syl3anc',
             '( %s -> %s = %s )' % (PS, RINT('F', LO, UR), RAWC))
    o1 = w.s([c1e], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (PS, LO, C1, LO, LR))
    o2 = w.s([c1e], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (PS, C1, UR, LR, UR))
    o3 = w.s([c2e], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (PS, UR, C2, UR, UL))
    o4 = w.s([c2e], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (PS, C2, LO, UL, LO))
    e1 = w.s([o1], 'oveq2d', '( %s -> %s = %s )' % (PS, LINT('F', LO, C1), BOT))
    e2 = w.s([o2], 'oveq2d', '( %s -> %s = %s )' % (PS, LINT('F', C1, UR), RIG))
    e3 = w.s([o3], 'oveq2d', '( %s -> %s = %s )' % (PS, LINT('F', UR, C2), TOP))
    e4 = w.s([o4], 'oveq2d', '( %s -> %s = %s )' % (PS, LINT('F', C2, LO), LEF))
    p1 = w.s([e1, e2], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (PS, LINT('F', LO, C1), LINT('F', C1, UR), BOT, RIG))
    p2 = w.s([e3, e4], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (PS, LINT('F', UR, C2), LINT('F', C2, LO), TOP, LEF))
    p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (PS, RAWC, TREE))
    eq = w.s([rv, p3], 'eqtrd', '( %s -> %s = %s )' % (PS, RINT('F', LO, UR), TREE))
    return w.s([eq, '7'], 'eqtr3d', '( %s -> %s = K )' % (PS, TREE))



# ---------------------------------------------------------------------------
w = W('rectintshl', 'The line-shift identity with a residue: if the boundary '
      'integral over every rectangle of height t is K and the two horizontal '
      'edge integrals tend to zero, the two vertical edge limits add up to K.  '
      'This is Carmichael.shift_lines_residue of DetectionShift.lean, with the '
      'improper integrals given as limits of the truncated ones.')
hyp(w, '1', 'rectintshl.a', '( ph -> A e. RR )')
hyp(w, '2', 'rectintshl.b', '( ph -> B e. RR )')
hyp(w, '3', 'rectintshl.f', '( ph -> F e. V )')
hyp(w, '4', 'rectintshl.k', '( ph -> K e. CC )')
hyp(w, '5', 'rectintshl.s', '( ph -> S C_ RR )')
hyp(w, '6', 'rectintshl.u', '( ph -> sup ( S , RR* , < ) = +oo )')
hyp(w, '7', 'rectintshl.r', '( %s -> %s = K )' % (PS, RINT('F', LO, UR)))
hyp(w, '8', 'rectintshl.1', '( ph -> %s ~~>r 0 )' % MPT('t', 'S', BOT))
hyp(w, '9', 'rectintshl.2', '( ph -> %s ~~>r X )' % MPT('t', 'S', RIG))
hyp(w, '10', 'rectintshl.3', '( ph -> %s ~~>r 0 )' % MPT('t', 'S', TOP))
hyp(w, '11', 'rectintshl.4', '( ph -> %s ~~>r Y )' % MPT('t', 'S', LEF))
tk = corners(w)
mte = w.s([tk], 'mpteq2dva', '( ph -> %s = %s )' % (MPT('t', 'S', TREE), MPT('t', 'S', 'K')))
vb = ovexd(w, PS, BOT); vr = ovexd(w, PS, RIG)
vt = ovexd(w, PS, TOP); vl = ovexd(w, PS, LEF)
in1 = w.s([vb, vr, '8', '9'], 'rlimadd', '( ph -> %s ~~>r ( 0 + X ) )' % MPT('t', 'S', '( %s + %s )' % (BOT, RIG)))
in2 = w.s([vt, vl, '10', '11'], 'rlimadd', '( ph -> %s ~~>r ( 0 + Y ) )' % MPT('t', 'S', '( %s + %s )' % (TOP, LEF)))
v1 = ovexd(w, PS, '( %s + %s )' % (BOT, RIG)); v2 = ovexd(w, PS, '( %s + %s )' % (TOP, LEF))
out = w.s([v1, v2, in1, in2], 'rlimadd', '( ph -> %s ~~>r ( ( 0 + X ) + ( 0 + Y ) ) )' % MPT('t', 'S', TREE))
kl = w.s([mte, out], 'eqbrtrrd', '( ph -> %s ~~>r ( ( 0 + X ) + ( 0 + Y ) ) )' % MPT('t', 'S', 'K'))
kc = w.s(['4'], 'adantr', '( %s -> K e. CC )' % PS)
kf = w.s([kc], 'fmptd', '( ph -> %s : S --> CC )' % MPT('t', 'S', 'K'))
kco = w.s(['5', '4', w.inst('rlimconst')], 'syl2anc', '( ph -> %s ~~>r K )' % MPT('t', 'S', 'K'))
uni = w.s([kf, '6', kl, kco], 'rlimuni', '( ph -> ( ( 0 + X ) + ( 0 + Y ) ) = K )')
xc = w.s(['9', w.inst('rlimcl')], 'syl', '( ph -> X e. CC )')
yc = w.s(['11', w.inst('rlimcl')], 'syl', '( ph -> Y e. CC )')
ax = w.s([xc, w.inst('addlid')], 'syl', '( ph -> ( 0 + X ) = X )')
ay = w.s([yc, w.inst('addlid')], 'syl', '( ph -> ( 0 + Y ) = Y )')
sm = w.s([ax, ay], 'oveq12d', '( ph -> ( ( 0 + X ) + ( 0 + Y ) ) = ( X + Y ) )')
w.qed([sm, uni], 'eqtr3d', '( ph -> ( X + Y ) = K )')
run1(w, h=True)

# ---------------------------------------------------------------------------
UPL = LINT('F', LO, UL)
w = W('rectintshlr', 'The line-shift identity with a residue, with the left '
      'edge traversed upwards: Carmichael.shift_lines_residue of '
      'DetectionShift.lean.  X is the limit of the right vertical edge '
      'integrals and W that of the left ones, each an _i times the improper '
      'integral along the line.')
hyp(w, '1', 'rectintshlr.a', '( ph -> A e. RR )')
hyp(w, '2', 'rectintshlr.b', '( ph -> B e. RR )')
hyp(w, '3', 'rectintshlr.f', '( ph -> F e. ( D -cn-> CC ) )')
hyp(w, '4', 'rectintshlr.k', '( ph -> K e. CC )')
hyp(w, '5', 'rectintshlr.s', '( ph -> S C_ RR )')
hyp(w, '6', 'rectintshlr.u', '( ph -> sup ( S , RR* , < ) = +oo )')
hyp(w, '7', 'rectintshlr.e', '( %s -> ( %s cseg %s ) C_ D )' % (PS, LO, UL))
hyp(w, '8', 'rectintshlr.r', '( %s -> %s = K )' % (PS, RINT('F', LO, UR)))
hyp(w, '9', 'rectintshlr.1', '( ph -> %s ~~>r 0 )' % MPT('t', 'S', BOT))
hyp(w, '10', 'rectintshlr.2', '( ph -> %s ~~>r X )' % MPT('t', 'S', RIG))
hyp(w, '11', 'rectintshlr.3', '( ph -> %s ~~>r 0 )' % MPT('t', 'S', TOP))
hyp(w, '12', 'rectintshlr.4', '( ph -> %s ~~>r W )' % MPT('t', 'S', UPL))
fex = w.s(['3', w.inst('elex')], 'syl', '( ph -> F e. _V )')
ar = w.s(['1'], 'adantr', '( %s -> A e. RR )' % PS)
ssr = w.s(['5'], 'adantr', '( %s -> S C_ RR )' % PS)
tS = w.s([], 'simpr', '( %s -> t e. S )' % PS)
tr = w.s([ssr, tS], 'sseldd', '( %s -> t e. RR )' % PS)
ntr = w.s([tr, w.inst('renegcl')], 'syl', '( %s -> -u t e. RR )' % PS)
ac = w.s([ar], 'recnd', '( %s -> A e. CC )' % PS)
tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % PS)
ntc = w.s([ntr], 'recnd', '( %s -> -u t e. CC )' % PS)
ic = closed(w, PS, 'ax-icn', '_i e. CC')
loc = w.s([ac, w.s([ic, ntc], 'mulcld', '( %s -> ( _i x. -u t ) e. CC )' % PS)], 'addcld', '( %s -> %s e. CC )' % (PS, LO))
ulc = w.s([ac, w.s([ic, tc], 'mulcld', '( %s -> ( _i x. t ) e. CC )' % PS)], 'addcld', '( %s -> %s e. CC )' % (PS, UL))
fcn = w.s(['3'], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % PS)
phl = w.s([w.s([loc, ulc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (PS, LO, UL)),
           w.s([fcn, '7'], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (PS, LO, UL))],
          'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) ) )' % (PS, LO, UL, LO, UL))
rev = w.s([phl, w.inst('lintrev')], 'syl', '( %s -> %s = -u %s )' % (PS, LEF, UPL))
mte = w.s([rev], 'mpteq2dva', '( ph -> %s = %s )' % (MPT('t', 'S', LEF), MPT('t', 'S', '-u %s' % UPL)))
vu = ovexd(w, PS, UPL)
neg = w.s([vu, '12'], 'rlimneg', '( ph -> %s ~~>r -u W )' % MPT('t', 'S', '-u %s' % UPL))
lft = w.s([mte, neg], 'eqbrtrd', '( ph -> %s ~~>r -u W )' % MPT('t', 'S', LEF))
shl = w.s(['1', '2', fex, '4', '5', '6', '8', '9', '10', '11', lft], 'rectintshl', '( ph -> ( X + -u W ) = K )')
xc = w.s(['10', w.inst('rlimcl')], 'syl', '( ph -> X e. CC )')
wc = w.s(['12', w.inst('rlimcl')], 'syl', '( ph -> W e. CC )')
ns = w.s([xc, wc], 'negsubd', '( ph -> ( X + -u W ) = ( X - W ) )')
w.qed([ns, shl], 'eqtr3d', '( ph -> ( X - W ) = K )')
run1(w, h=True)
