"""Sortie A4c, batch 9: the cost of the extraction loop (Lean: extractGo_cost,
extract_cost)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

R5 = '( ( X e. RR /\\ K e. RR /\\ L e. RR ) /\\ ( A e. RR /\\ B e. RR ) )'
RHS = '( ( X + ( L + 3 ) ) + K )'

def r5(w, A, three=False):
    xx = w.s([w.s([], 'simp1' if three else 'simpll', '( %s -> ( X e. RR /\\ K e. RR /\\ L e. RR ) )' % A)], 'simp1d',
             '( %s -> X e. RR )' % A)
    kk = w.s([w.s([], 'simp1' if three else 'simpll', '( %s -> ( X e. RR /\\ K e. RR /\\ L e. RR ) )' % A)], 'simp2d',
             '( %s -> K e. RR )' % A)
    ll = w.s([w.s([], 'simp1' if three else 'simpll', '( %s -> ( X e. RR /\\ K e. RR /\\ L e. RR ) )' % A)], 'simp3d',
             '( %s -> L e. RR )' % A)
    return xx, kk, ll

# ------------------------------------------------------------------ extgocba
if not only or 'extgocba' in only:
    w = W('extgocba', 'The charge algebra of the extraction loop when the residue is unfilled.')
    A = '( %s /\\ ( A <_ ( X + ( K + 1 ) ) /\\ B = ( L + 1 ) ) )' % R5
    xx, kk, ll = r5(w, A)
    aa = w.s([w.s([], 'simplr', '( %s -> ( A e. RR /\\ B e. RR ) )' % A)], 'simpld', '( %s -> A e. RR )' % A)
    bb = w.s([w.s([], 'simplr', '( %s -> ( A e. RR /\\ B e. RR ) )' % A)], 'simprd', '( %s -> B e. RR )' % A)
    h1 = w.s([], 'simprl', '( %s -> A <_ ( X + ( K + 1 ) ) )' % A)
    h2 = w.s([], 'simprr', '( %s -> B = ( L + 1 ) )' % A)
    li = lin.linarith(w, A, [h1, h2], '( ( A + B ) + 1 ) <_ %s' % RHS,
                      leaves={'X': xx, 'K': kk, 'L': ll, 'A': aa, 'B': bb})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)

# ------------------------------------------------------------------ extgocbb
if not only or 'extgocbb' in only:
    w = W('extgocbb', 'The charge algebra of the extraction loop when it returns.')
    A = '( %s /\\ ( ( A <_ ( K + 1 ) /\\ B = ( L + 1 ) ) /\\ 0 <_ X ) )' % R5
    xx, kk, ll = r5(w, A)
    aa = w.s([w.s([], 'simplr', '( %s -> ( A e. RR /\\ B e. RR ) )' % A)], 'simpld', '( %s -> A e. RR )' % A)
    bb = w.s([w.s([], 'simplr', '( %s -> ( A e. RR /\\ B e. RR ) )' % A)], 'simprd', '( %s -> B e. RR )' % A)
    h1 = w.s([w.s([], 'simprl', '( %s -> ( A <_ ( K + 1 ) /\\ B = ( L + 1 ) ) )' % A)], 'simpld',
             '( %s -> A <_ ( K + 1 ) )' % A)
    h2 = w.s([w.s([], 'simprl', '( %s -> ( A <_ ( K + 1 ) /\\ B = ( L + 1 ) ) )' % A)], 'simprd',
             '( %s -> B = ( L + 1 ) )' % A)
    h3 = w.s([], 'simprr', '( %s -> 0 <_ X )' % A)
    li = lin.linarith(w, A, [h1, h2, h3], '( ( B + A ) + 1 ) <_ %s' % RHS,
                      leaves={'X': xx, 'K': kk, 'L': ll, 'A': aa, 'B': bb})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)

# ------------------------------------------------------------------ extgocbc
if not only or 'extgocbc' in only:
    w = W('extgocbc', 'The charge algebra of the extraction loop across a reset.')
    A = '( ( X e. RR /\\ K e. RR /\\ L e. RR ) /\\ ( A e. RR /\\ B e. RR /\\ C e. RR ) /\\ ( ( A <_ ( X + 0 ) /\\ B = ( L + 1 ) ) /\\ C <_ ( K + 1 ) ) )'
    xx, kk, ll = r5(w, A, True)
    aa = w.s([w.s([], 'simp2', '( %s -> ( A e. RR /\\ B e. RR /\\ C e. RR ) )' % A)], 'simp1d', '( %s -> A e. RR )' % A)
    bb = w.s([w.s([], 'simp2', '( %s -> ( A e. RR /\\ B e. RR /\\ C e. RR ) )' % A)], 'simp2d', '( %s -> B e. RR )' % A)
    ccc = w.s([w.s([], 'simp2', '( %s -> ( A e. RR /\\ B e. RR /\\ C e. RR ) )' % A)], 'simp3d', '( %s -> C e. RR )' % A)
    h1 = w.s([w.s([w.s([], 'simp3', '( %s -> ( ( A <_ ( X + 0 ) /\\ B = ( L + 1 ) ) /\\ C <_ ( K + 1 ) ) )' % A)], 'simpld',
                  '( %s -> ( A <_ ( X + 0 ) /\\ B = ( L + 1 ) ) )' % A)], 'simpld', '( %s -> A <_ ( X + 0 ) )' % A)
    h2 = w.s([w.s([w.s([], 'simp3', '( %s -> ( ( A <_ ( X + 0 ) /\\ B = ( L + 1 ) ) /\\ C <_ ( K + 1 ) ) )' % A)], 'simpld',
                  '( %s -> ( A <_ ( X + 0 ) /\\ B = ( L + 1 ) ) )' % A)], 'simprd', '( %s -> B = ( L + 1 ) )' % A)
    h3 = w.s([w.s([], 'simp3', '( %s -> ( ( A <_ ( X + 0 ) /\\ B = ( L + 1 ) ) /\\ C <_ ( K + 1 ) ) )' % A)], 'simprd',
             '( %s -> C <_ ( K + 1 ) )' % A)
    li = lin.linarith(w, A, [h1, h2, h3], '( ( ( A + B ) + C ) + 1 ) <_ %s' % RHS,
                      leaves={'X': xx, 'K': kk, 'L': ll, 'A': aa, 'B': bb, 'C': ccc})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)

# ================================================================= extgocost
OUT = '( L e. NN /\\ N e. NN0 )'
QU = [('m', 'NN0'), ('u', 'Word NN0'), ('t', 'Tbl'), ('k', 'NN0')]
def EG(s, m, u, t): return '( ( ( ( ( L ExtractGo N ) ` %s ) ` %s ) ` %s ) ` %s )' % (s, m, u, t)
BODY = '( %s -> ( 2nd ` %s ) <_ ( ( ( # ` s ) x. ( L + 3 ) ) + k ) )' % (TB('t', 'k'), EG('s', 'm', 'u', 't'))
CSV = '( <" P "> ++ V )'
DSP = '( ( L DpStep P ) ` t )'
DSP1 = '( 1st ` %s )' % DSP
HIT = '( %s ` ( 1 mod L ) )' % DSP1
SS = '( 2nd ` %s )' % HIT
PL = '( ProdL ` %s )' % SS
PS = '( 1st ` %s )' % PL
MP = '( m x. %s )' % PS
SU = '( %s ++ u )' % SS
XX = '( ( # ` V ) x. ( L + 3 ) )'

def _b(w, ctx, goal):
    A = ctx.A
    ll = w.s([w.s([ctx.out], 'simpld', '( %s -> L e. NN )' % A)], 'nnred', '( %s -> L e. RR )' % A)
    kk = w.s([ctx.v[3]], 'nn0red', '( %s -> k e. RR )' % A)
    k0 = w.s([ctx.v[3]], 'nn0ge0d', '( %s -> 0 <_ k )' % A)
    v = w.s([w.s([w.s([w.s([ctx.out, ctx.v[0]], 'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (A, OUT)), ctx.v[1]], 'jca',
                  '( %s -> ( ( %s /\\ m e. NN0 ) /\\ u e. Word NN0 ) )' % (A, OUT)), ctx.v[2]], 'jca',
                 '( %s -> ( ( ( %s /\\ m e. NN0 ) /\\ u e. Word NN0 ) /\\ t e. Tbl ) )' % (A, OUT)),
             w.inst('extractgo0')], 'syl', '( %s -> %s = <. %s , 0 >. )' % (A, EG('(/)', 'm', 'u', 't'), NONE))
    p2 = prj(w, A, EG('(/)', 'm', 'u', 't'), v, NONE, '0', 2,
             bex=w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A))
    h0 = w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % A)], 'oveq1d',
             '( %s -> ( ( # ` (/) ) x. ( L + 3 ) ) = ( 0 x. ( L + 3 ) ) )' % A)
    three = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % A)
    l3 = w.s([w.s([ll, three], 'readdcld', '( %s -> ( L + 3 ) e. RR )' % A)], 'recnd',
             '( %s -> ( L + 3 ) e. CC )' % A)
    z = w.s([l3], 'mul02d', '( %s -> ( 0 x. ( L + 3 ) ) = 0 )' % A)
    eq = w.s([w.s([h0, z], 'eqtrd', '( %s -> ( ( # ` (/) ) x. ( L + 3 ) ) = 0 )' % A)], 'oveq1d',
             '( %s -> ( ( ( # ` (/) ) x. ( L + 3 ) ) + k ) = ( 0 + k ) )' % A)
    eq2 = w.s([eq, w.s([w.s([ctx.v[3]], 'nn0cnd', '( %s -> k e. CC )' % A)], 'addlidd',
                       '( %s -> ( 0 + k ) = k )' % A)], 'eqtrd',
              '( %s -> ( ( ( # ` (/) ) x. ( L + 3 ) ) + k ) = k )' % A)
    le = w.s([w.s([p2, k0], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ k )' % (A, EG('(/)', 'm', 'u', 't'))),
              w.s([eq2], 'eqcomd', '( %s -> k = ( ( ( # ` (/) ) x. ( L + 3 ) ) + k ) )' % A)], 'breqtrd',
             '( %s -> ( 2nd ` %s ) <_ ( ( ( # ` (/) ) x. ( L + 3 ) ) + k ) )' % (A, EG('(/)', 'm', 'u', 't')))
    return w.s([le], 'a1d', '( %s -> %s )' % (A, goal))

def _s(w, ctx, goal):
    A = ctx.A
    U = '( %s /\\ %s )' % (A, TB('t', 'k'))
    lf = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    out = lf(ctx.out, OUT); ih = lf(ctx.ih, ctx.ihf); vv = lf(ctx.wrd, 'V e. Word NN0'); pp = lf(ctx.let, 'P e. NN0')
    mm = lf(ctx.v[0], 'm e. NN0'); uu = lf(ctx.v[1], 'u e. Word NN0'); ttt = lf(ctx.v[2], 't e. Tbl')
    kk = lf(ctx.v[3], 'k e. NN0')
    tbh = w.s([], 'simpr', '( %s -> %s )' % (U, TB('t', 'k')))
    ll = w.s([out], 'simpld', '( %s -> L e. NN )' % U)
    nn = w.s([out], 'simprd', '( %s -> N e. NN0 )' % U)
    dpo = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % U), ttt], 'jca',
              '( %s -> ( ( L e. NN /\\ P e. NN0 ) /\\ t e. Tbl ) )' % U)
    dpo3 = w.s([ll, pp, ttt], '3jca', '( %s -> ( L e. NN /\\ P e. NN0 /\\ t e. Tbl ) )' % U)
    dscl = w.s([dpo, w.inst('dpstepcl')], 'syl', '( %s -> %s e. ( Tbl X. NN0 ) )' % (U, DSP))
    ds1 = w.s([dscl, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (U, DSP1))
    dsc = w.s([dpo, w.inst('dpstepcost')], 'syl', '( %s -> ( 2nd ` %s ) = ( L + 1 ) )' % (U, DSP))
    tb1 = w.s([w.s([dpo3, w.s([kk, tbh], 'jca', '( %s -> ( k e. NN0 /\\ %s ) )' % (U, TB('t', 'k')))], 'jca',
                   '( %s -> ( ( L e. NN /\\ P e. NN0 /\\ t e. Tbl ) /\\ ( k e. NN0 /\\ %s ) ) )' % (U, TB('t', 'k'))),
               w.inst('tblbnds')], 'syl', '( %s -> %s )' % (U, TB(DSP1, '( k + 1 )')))
    lenV = w.s([vv, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % U)
    lr = w.s([ll], 'nnred', '( %s -> L e. RR )' % U)
    l3r = w.s([lr, w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % U)], 'readdcld',
              '( %s -> ( L + 3 ) e. RR )' % U)
    xxr = w.s([w.s([lenV], 'nn0red', '( %s -> ( # ` V ) e. RR )' % U), l3r], 'remulcld', '( %s -> %s e. RR )' % (U, XX))
    x0 = w.s([w.s([lenV], 'nn0red', '( %s -> ( # ` V ) e. RR )' % U), l3r,
              w.s([lenV], 'nn0ge0d', '( %s -> 0 <_ ( # ` V ) )' % U),
              lin.linarith(w, U, [w.s([ll], 'nnge1d', '( %s -> 1 <_ L )' % U)], '0 <_ ( L + 3 )', leaves={'L': lr})],
             'mulge0d', '( %s -> 0 <_ %s )' % (U, XX))
    krr = w.s([kk], 'nn0red', '( %s -> k e. RR )' % U)
    R5S = '( ( %s e. RR /\\ k e. RR /\\ L e. RR ) /\\ ' % XX
    # the right-hand side rewritten
    lcs = w.s([pp, vv, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (U, CSV))
    ddp = w.s([w.s([lenV], 'nn0cnd', '( %s -> ( # ` V ) e. CC )' % U),
               w.s([l3r], 'recnd', '( %s -> ( L + 3 ) e. CC )' % U)], 'adddirp1d',
              '( %s -> ( ( ( # ` V ) + 1 ) x. ( L + 3 ) ) = ( %s + ( L + 3 ) ) )' % (U, XX))
    rhs = w.s([w.s([w.s([lcs], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( L + 3 ) ) = ( ( ( # ` V ) + 1 ) x. ( L + 3 ) ) )' % (U, CSV)),
                    ddp], 'eqtrd', '( %s -> ( ( # ` %s ) x. ( L + 3 ) ) = ( %s + ( L + 3 ) ) )' % (U, CSV, XX))], 'oveq1d',
              '( %s -> ( ( ( # ` %s ) x. ( L + 3 ) ) + k ) = ( ( %s + ( L + 3 ) ) + k ) )' % (U, CSV, XX))
    RH = '( ( %s + ( L + 3 ) ) + k )' % XX
    TGT = '( 2nd ` %s ) <_ ( ( ( # ` %s ) x. ( L + 3 ) ) + k )' % (EG(CSV, 'm', 'u', 't'), CSV)
    xkl = w.s([xxr, krr, lr], '3jca', '( %s -> ( %s e. RR /\\ k e. RR /\\ L e. RR ) )' % (U, XX))
    # ------------------------------------------------------------ the none branch
    N1 = '( %s /\\ %s = %s )' % (U, HIT, NONE)
    n1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (N1, f))
    ante = '( ( ( ( ( ( %s /\\ m e. NN0 ) /\\ u e. Word NN0 ) /\\ t e. Tbl ) /\\ P e. NN0 ) /\\ V e. Word NN0 ) /\\ %s = %s )' % (OUT, HIT, NONE)
    aj, _f = lnest(w, N1, [(n1(out, OUT), OUT), (n1(mm, 'm e. NN0'), 'm e. NN0'),
                           (n1(uu, 'u e. Word NN0'), 'u e. Word NN0'), (n1(ttt, 't e. Tbl'), 't e. Tbl'),
                           (n1(pp, 'P e. NN0'), 'P e. NN0'), (n1(vv, 'V e. Word NN0'), 'V e. Word NN0')])
    valn = w.s([w.s([aj, w.s([], 'simpr', '( %s -> %s = %s )' % (N1, HIT, NONE))], 'jca', '( %s -> %s )' % (N1, ante)),
                w.inst('extractgocsn')], 'syl',
               '( %s -> %s = <. ( 1st ` %s ) , ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) >. )'
               % (N1, EG(CSV, 'm', 'u', 't'), EG('V', 'm', 'u', DSP1), EG('V', 'm', 'u', DSP1), DSP))
    pn = prj(w, N1, EG(CSV, 'm', 'u', 't'), valn, '( 1st ` %s )' % EG('V', 'm', 'u', DSP1),
             '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (EG('V', 'm', 'u', DSP1), DSP), 2)
    r = ctx.rn
    ihb = subst(subst(subst(subst(subst(BODY, 's', 'V'), 'm', r[0]), 'u', r[1]), 't', r[2]), 'k', r[3])
    k1n = w.s([n1(kk, 'k e. NN0'), w.inst('peano2nn0')], 'syl', '( %s -> ( k + 1 ) e. NN0 )' % N1)
    ihn, _ = instn(w, N1, n1(ih, ctx.ihf), [(r[0], 'NN0'), (r[1], 'Word NN0'), (r[2], 'Tbl'), (r[3], 'NN0')], ihb,
                   ['m', 'u', DSP1, '( k + 1 )'],
                   [n1(mm, 'm e. NN0'), n1(uu, 'u e. Word NN0'), n1(ds1, '%s e. Tbl' % DSP1), k1n])
    ihv = w.s([ihn, n1(tb1, TB(DSP1, '( k + 1 )'))], 'mpd',
              '( %s -> ( 2nd ` %s ) <_ ( %s + ( k + 1 ) ) )' % (N1, EG('V', 'm', 'u', DSP1), XX))
    egj, _f3 = lnest(w, N1, [(n1(out, OUT), OUT), (n1(vv, 'V e. Word NN0'), 'V e. Word NN0'),
                             (n1(mm, 'm e. NN0'), 'm e. NN0'), (n1(uu, 'u e. Word NN0'), 'u e. Word NN0'),
                             (n1(ds1, '%s e. Tbl' % DSP1), '%s e. Tbl' % DSP1)])
    egcl = w.s([egj, w.inst('extractgocl')], 'syl',
               '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (N1, EG('V', 'm', 'u', DSP1)))
    egr = w.s([w.s([egcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (N1, EG('V', 'm', 'u', DSP1)))], 'nn0red',
              '( %s -> ( 2nd ` %s ) e. RR )' % (N1, EG('V', 'm', 'u', DSP1)))
    dsr = w.s([w.s([n1(dscl, '%s e. ( Tbl X. NN0 )' % DSP), w.inst('xp2nd')], 'syl',
                    '( %s -> ( 2nd ` %s ) e. NN0 )' % (N1, DSP))], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (N1, DSP))
    alg = w.s([w.s([n1(xkl, '( %s e. RR /\\ k e. RR /\\ L e. RR )' % XX),
                    w.s([egr, dsr], 'jca', '( %s -> ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) )' % (N1, EG('V', 'm', 'u', DSP1), DSP))], 'jca',
                   '( %s -> ( ( %s e. RR /\\ k e. RR /\\ L e. RR ) /\\ ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) ) )' % (N1, XX, EG('V', 'm', 'u', DSP1), DSP)),
               w.s([ihv, n1(dsc, '( 2nd ` %s ) = ( L + 1 )' % DSP)], 'jca',
                   '( %s -> ( ( 2nd ` %s ) <_ ( %s + ( k + 1 ) ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) )' % (N1, EG('V', 'm', 'u', DSP1), XX, DSP))], 'jca', None)
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> ( ( ( %s e. RR /\\ k e. RR /\\ L e. RR ) /\\ ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) ) /\\ ( ( 2nd ` %s ) <_ ( %s + ( k + 1 ) ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) ) )' % (N1, XX, EG('V', 'm', 'u', DSP1), DSP, EG('V', 'm', 'u', DSP1), XX, DSP)
    cba = w.s([alg, w.inst('extgocba')], 'syl',
              '( %s -> ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) <_ %s )' % (N1, EG('V', 'm', 'u', DSP1), DSP, RH))
    gn = w.s([w.s([pn, cba], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ %s )' % (N1, EG(CSV, 'm', 'u', 't'), RH)),
              w.s([n1(rhs, '( ( ( # ` %s ) x. ( L + 3 ) ) + k ) = %s' % (CSV, RH))], 'eqcomd',
                  '( %s -> %s = ( ( ( # ` %s ) x. ( L + 3 ) ) + k ) )' % (N1, RH, CSV))], 'breqtrd',
             '( %s -> %s )' % (N1, TGT))
    # ------------------------------------------------------------ the some branch
    S1 = '( %s /\\ -. %s = %s )' % (U, HIT, NONE)
    q1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (S1, f))
    hitne = w.s([w.s([], 'simpr', '( %s -> -. %s = %s )' % (S1, HIT, NONE)), w.inst('neqned')], 'syl',
                '( %s -> %s =/= %s )' % (S1, HIT, NONE))
    ante2 = '( ( ( ( ( ( %s /\\ m e. NN0 ) /\\ u e. Word NN0 ) /\\ t e. Tbl ) /\\ P e. NN0 ) /\\ V e. Word NN0 ) /\\ %s =/= %s )' % (OUT, HIT, NONE)
    aj2, _f2 = lnest(w, S1, [(q1(out, OUT), OUT), (q1(mm, 'm e. NN0'), 'm e. NN0'),
                             (q1(uu, 'u e. Word NN0'), 'u e. Word NN0'), (q1(ttt, 't e. Tbl'), 't e. Tbl'),
                             (q1(pp, 'P e. NN0'), 'P e. NN0'), (q1(vv, 'V e. Word NN0'), 'V e. Word NN0')])
    TH2 = '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (DSP, PL)
    TH1 = '( inl ` <. %s , %s >. )' % (MP, SU)
    EGR = EG('V', MP, SU, 'EmptyTbl')
    EL1 = '( 1st ` %s )' % EGR
    EL2 = '( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % (EGR, DSP, PL)
    COND = 'N < %s' % MP
    IFE = 'if ( %s , <. %s , %s >. , <. %s , %s >. )' % (COND, TH1, TH2, EL1, EL2)
    vals = w.s([w.s([aj2, hitne], 'jca', '( %s -> %s )' % (S1, ante2)), w.inst('extractgocss')], 'syl',
               '( %s -> %s = %s )' % (S1, EG(CSV, 'm', 'u', 't'), IFE))
    #  the shared facts
    m1 = w.s([w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % S1), q1(ll, 'L e. NN'), w.inst('zmodcl')], 'syl2anc',
             '( %s -> ( 1 mod L ) e. NN0 )' % S1)
    scl = w.s([w.s([w.s([q1(ds1, '%s e. Tbl' % DSP1), m1], 'jca', '( %s -> ( %s e. Tbl /\\ ( 1 mod L ) e. NN0 ) )' % (S1, DSP1)),
                    hitne], 'jca', '( %s -> ( ( %s e. Tbl /\\ ( 1 mod L ) e. NN0 ) /\\ %s =/= %s ) )' % (S1, DSP1, HIT, NONE)),
               w.inst('tblpay')], 'syl',
              '( %s -> ( %s e. Word NN0 /\\ %s = ( inl ` %s ) ) )' % (S1, SS, HIT, SS))
    sw = w.s([scl], 'simpld', '( %s -> %s e. Word NN0 )' % (S1, SS))
    plc = w.s([sw, w.inst('prodlcost')], 'syl', '( %s -> ( 2nd ` %s ) = ( # ` %s ) )' % (S1, PL, SS))
    tbi, _ = inst1(w, S1, q1(tb1, TB(DSP1, '( k + 1 )')), 'd', 'NN0',
                   '( ( %s ` d ) =/= %s -> ( # ` ( 2nd ` ( %s ` d ) ) ) <_ ( k + 1 ) )' % (DSP1, NONE, DSP1), '( 1 mod L )', m1)
    slen = w.s([tbi, hitne], 'mpd', '( %s -> ( # ` %s ) <_ ( k + 1 ) )' % (S1, SS))
    plle = w.s([plc, slen], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( k + 1 ) )' % (S1, PL))
    plcl = w.s([sw, w.inst('prodlcl')], 'syl', '( %s -> %s e. ( NN0 X. NN0 ) )' % (S1, PL))
    plr = w.s([w.s([plcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (S1, PL))], 'nn0red',
              '( %s -> ( 2nd ` %s ) e. RR )' % (S1, PL))
    dsr2 = w.s([w.s([q1(dscl, '%s e. ( Tbl X. NN0 )' % DSP), w.inst('xp2nd')], 'syl',
                    '( %s -> ( 2nd ` %s ) e. NN0 )' % (S1, DSP))], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (S1, DSP))
    psn = w.s([plcl, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (S1, PS))
    mpn = w.s([q1(mm, 'm e. NN0'), psn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (S1, MP))
    sun = w.s([sw, q1(uu, 'u e. Word NN0'), w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (S1, SU))
    xkl1 = q1(xkl, '( %s e. RR /\\ k e. RR /\\ L e. RR )' % XX)
    ift, iff = ifproj(w, S1, EG(CSV, 'm', 'u', 't'), vals, COND, '<. %s , %s >.' % (TH1, TH2), '<. %s , %s >.' % (EL1, EL2))
    # ---- the return branch
    T1 = '( %s /\\ %s )' % (S1, COND)
    t1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (T1, f))
    pt = prj(w, T1, EG(CSV, 'm', 'u', 't'), ift, TH1, TH2, 2)
    algb = w.s([w.s([t1(xkl1, '( %s e. RR /\\ k e. RR /\\ L e. RR )' % XX),
                     w.s([t1(plr, '( 2nd ` %s ) e. RR' % PL), t1(dsr2, '( 2nd ` %s ) e. RR' % DSP)], 'jca',
                         '( %s -> ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) )' % (T1, PL, DSP))], 'jca',
                    '( %s -> ( ( %s e. RR /\\ k e. RR /\\ L e. RR ) /\\ ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) ) )' % (T1, XX, PL, DSP)),
                w.s([w.s([t1(plle, '( 2nd ` %s ) <_ ( k + 1 )' % PL), t1(q1(dsc, '( 2nd ` %s ) = ( L + 1 )' % DSP), '( 2nd ` %s ) = ( L + 1 )' % DSP)], 'jca',
                         '( %s -> ( ( 2nd ` %s ) <_ ( k + 1 ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) )' % (T1, PL, DSP)),
                     t1(q1(x0, '0 <_ %s' % XX), '0 <_ %s' % XX)], 'jca',
                    '( %s -> ( ( ( 2nd ` %s ) <_ ( k + 1 ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) /\\ 0 <_ %s ) )' % (T1, PL, DSP, XX))],
               'jca', '( %s -> ( ( ( %s e. RR /\\ k e. RR /\\ L e. RR ) /\\ ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) ) /\\ ( ( ( 2nd ` %s ) <_ ( k + 1 ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) /\\ 0 <_ %s ) ) )' % (T1, XX, PL, DSP, PL, DSP, XX))
    cbb = w.s([algb, w.inst('extgocbb')], 'syl', '( %s -> %s <_ %s )' % (T1, TH2, RH))
    gt = w.s([w.s([pt, cbb], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ %s )' % (T1, EG(CSV, 'm', 'u', 't'), RH)),
              w.s([t1(q1(rhs, '( ( ( # ` %s ) x. ( L + 3 ) ) + k ) = %s' % (CSV, RH)), '( ( ( # ` %s ) x. ( L + 3 ) ) + k ) = %s' % (CSV, RH))],
                  'eqcomd', '( %s -> %s = ( ( ( # ` %s ) x. ( L + 3 ) ) + k ) )' % (T1, RH, CSV))], 'breqtrd',
             '( %s -> %s )' % (T1, TGT))
    # ---- the reset branch
    F1 = '( %s /\\ -. %s )' % (S1, COND)
    f1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (F1, f))
    pf = prj(w, F1, EG(CSV, 'm', 'u', 't'), iff, EL1, EL2, 2)
    z0 = w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % F1)
    etc = w.s([w.s([], 'emptytblcl', 'EmptyTbl e. Tbl')], 'a1i', '( %s -> EmptyTbl e. Tbl )' % F1)
    ihf, _ = instn(w, F1, f1(q1(ih, ctx.ihf), ctx.ihf), [(r[0], 'NN0'), (r[1], 'Word NN0'), (r[2], 'Tbl'), (r[3], 'NN0')], ihb,
                   [MP, SU, 'EmptyTbl', '0'],
                   [f1(mpn, '%s e. NN0' % MP), f1(sun, '%s e. Word NN0' % SU), etc, z0])
    tb0 = w.s([z0, w.inst('tblbnd0')], 'syl', '( %s -> %s )' % (F1, TB('EmptyTbl', '0')))
    ihfv = w.s([ihf, tb0], 'mpd', '( %s -> ( 2nd ` %s ) <_ ( %s + 0 ) )' % (F1, EGR, XX))
    egj2, _f4 = lnest(w, F1, [(f1(q1(out, OUT), OUT), OUT),
                              (f1(q1(vv, 'V e. Word NN0'), 'V e. Word NN0'), 'V e. Word NN0'),
                              (f1(mpn, '%s e. NN0' % MP), '%s e. NN0' % MP),
                              (f1(sun, '%s e. Word NN0' % SU), '%s e. Word NN0' % SU),
                              (etc, 'EmptyTbl e. Tbl')])
    egcl2 = w.s([egj2, w.inst('extractgocl')], 'syl',
                '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (F1, EGR))
    egr2 = w.s([w.s([egcl2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (F1, EGR))], 'nn0red',
               '( %s -> ( 2nd ` %s ) e. RR )' % (F1, EGR))
    algc = w.s([f1(xkl1, '( %s e. RR /\\ k e. RR /\\ L e. RR )' % XX),
                w.s([egr2, f1(dsr2, '( 2nd ` %s ) e. RR' % DSP), f1(plr, '( 2nd ` %s ) e. RR' % PL)], '3jca',
                    '( %s -> ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) )' % (F1, EGR, DSP, PL)),
                w.s([w.s([ihfv, f1(q1(dsc, '( 2nd ` %s ) = ( L + 1 )' % DSP), '( 2nd ` %s ) = ( L + 1 )' % DSP)], 'jca',
                         '( %s -> ( ( 2nd ` %s ) <_ ( %s + 0 ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) )' % (F1, EGR, XX, DSP)),
                     f1(plle, '( 2nd ` %s ) <_ ( k + 1 )' % PL)], 'jca',
                    '( %s -> ( ( ( 2nd ` %s ) <_ ( %s + 0 ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) /\\ ( 2nd ` %s ) <_ ( k + 1 ) ) )' % (F1, EGR, XX, DSP, PL))],
               '3jca', '( %s -> ( ( %s e. RR /\\ k e. RR /\\ L e. RR ) /\\ ( ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR /\\ ( 2nd ` %s ) e. RR ) /\\ ( ( ( 2nd ` %s ) <_ ( %s + 0 ) /\\ ( 2nd ` %s ) = ( L + 1 ) ) /\\ ( 2nd ` %s ) <_ ( k + 1 ) ) ) )' % (F1, XX, EGR, DSP, PL, EGR, XX, DSP, PL))
    cbc = w.s([algc, w.inst('extgocbc')], 'syl', '( %s -> %s <_ %s )' % (F1, EL2, RH))
    gf = w.s([w.s([pf, cbc], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ %s )' % (F1, EG(CSV, 'm', 'u', 't'), RH)),
              w.s([f1(q1(rhs, '( ( ( # ` %s ) x. ( L + 3 ) ) + k ) = %s' % (CSV, RH)), '( ( ( # ` %s ) x. ( L + 3 ) ) + k ) = %s' % (CSV, RH))],
                  'eqcomd', '( %s -> %s = ( ( ( # ` %s ) x. ( L + 3 ) ) + k ) )' % (F1, RH, CSV))], 'breqtrd',
             '( %s -> %s )' % (F1, TGT))
    gs = w.s([gt, gf], 'pm2.61dan', '( %s -> %s )' % (S1, TGT))
    fin = w.s([gn, gs], 'pm2.61dan', '( %s -> %s )' % (U, TGT))
    return w.s([fin], 'ex', '( %s -> %s )' % (A, goal))


def _i(w):
    A = '( ( %s /\\ W e. Word NN0 ) /\\ ( M e. NN0 /\\ U e. Word NN0 /\\ T e. Tbl ) /\\ ( K e. NN0 /\\ %s ) )' % (OUT, TB('T', 'K'))
    out = w.s([w.s([], 'simp1', '( %s -> ( %s /\\ W e. Word NN0 ) )' % (A, OUT))], 'simpld', '( %s -> %s )' % (A, OUT))
    ww = w.s([w.s([], 'simp1', '( %s -> ( %s /\\ W e. Word NN0 ) )' % (A, OUT))], 'simprd', '( %s -> W e. Word NN0 )' % A)
    mm = w.s([w.s([], 'simp2', '( %s -> ( M e. NN0 /\\ U e. Word NN0 /\\ T e. Tbl ) )' % A)], 'simp1d', '( %s -> M e. NN0 )' % A)
    uu = w.s([w.s([], 'simp2', '( %s -> ( M e. NN0 /\\ U e. Word NN0 /\\ T e. Tbl ) )' % A)], 'simp2d', '( %s -> U e. Word NN0 )' % A)
    ttt = w.s([w.s([], 'simp2', '( %s -> ( M e. NN0 /\\ U e. Word NN0 /\\ T e. Tbl ) )' % A)], 'simp3d', '( %s -> T e. Tbl )' % A)
    kk = w.s([w.s([], 'simp3', '( %s -> ( K e. NN0 /\\ %s ) )' % (A, TB('T', 'K')))], 'simpld', '( %s -> K e. NN0 )' % A)
    tb = w.s([w.s([], 'simp3', '( %s -> ( K e. NN0 /\\ %s ) )' % (A, TB('T', 'K')))], 'simprd', '( %s -> %s )' % (A, TB('T', 'K')))
    PH = qphi(OUT, QU, subst(BODY, 's', 'W'))
    ral = w.s([w.s([ww, w.inst('extgocost')], 'syl', '( %s -> %s )' % (A, PH)), out], 'mpd',
              '( %s -> %s )' % (A, quantify(QU, ['m', 'u', 't', 'k'], subst(BODY, 's', 'W'))))
    st, bd = instn(w, A, ral, QU, subst(BODY, 's', 'W'), ['M', 'U', 'T', 'K'], [mm, uu, ttt, kk])
    fin = w.s([st, tb], 'mpd', '( %s -> ( 2nd ` %s ) <_ ( ( ( # ` W ) x. ( L + 3 ) ) + K ) )' % (A, EG('W', 'M', 'U', 'T')))
    w.lines[-1] = w.lines[-1].replace('%s:' % fin, 'qed:', 1)


qwrd(run, 'extgocost', OUT, QU, BODY, _b, _s, instfn=_i, only=only,
     desc='The extraction loop charges the modulus per pool element (Lean: extractGo_cost).')

# ================================================================= extcost
if not only or 'extcost' in only:
    w = W('extcost', 'The cost of step 4, the extraction (Lean: extract_cost).')
    A = '( %s /\\ W e. Word NN0 )' % OUT
    EX = '( ( L Extract N ) ` W )'
    EGW = EG('W', '1', '(/)', 'EmptyTbl')
    out = w.s([], 'simpl', '( %s -> %s )' % (A, OUT))
    ww = w.s([], 'simpr', '( %s -> W e. Word NN0 )' % A)
    ll = w.s([out], 'simpld', '( %s -> L e. NN )' % A)
    val = w.s([w.s([out, ww], 'jca', '( %s -> ( %s /\\ W e. Word NN0 ) )' % (A, OUT)), w.inst('extractval')], 'syl',
              '( %s -> %s = %s )' % (A, EX, EGW))
    one = w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % A)
    z0 = w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % A)
    w0 = w.s([w.s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % A)
    etc = w.s([w.s([], 'emptytblcl', 'EmptyTbl e. Tbl')], 'a1i', '( %s -> EmptyTbl e. Tbl )' % A)
    tb0 = w.s([z0, w.inst('tblbnd0')], 'syl', '( %s -> %s )' % (A, TB('EmptyTbl', '0')))
    ci = w.s([w.s([w.s([out, ww], 'jca', '( %s -> ( %s /\\ W e. Word NN0 ) )' % (A, OUT)),
                   w.s([one, w0, etc], '3jca', '( %s -> ( 1 e. NN0 /\\ (/) e. Word NN0 /\\ EmptyTbl e. Tbl ) )' % A),
                   w.s([z0, tb0], 'jca', '( %s -> ( 0 e. NN0 /\\ %s ) )' % (A, TB('EmptyTbl', '0')))], '3jca',
                  '( %s -> ( ( %s /\\ W e. Word NN0 ) /\\ ( 1 e. NN0 /\\ (/) e. Word NN0 /\\ EmptyTbl e. Tbl ) /\\ ( 0 e. NN0 /\\ %s ) ) )'
                  % (A, OUT, TB('EmptyTbl', '0'))), w.inst('extgocosti')], 'syl',
             '( %s -> ( 2nd ` %s ) <_ ( ( ( # ` W ) x. ( L + 3 ) ) + 0 ) )' % (A, EGW))
    XW = '( ( # ` W ) x. ( L + 3 ) )'
    lr = w.s([ll], 'nnred', '( %s -> L e. RR )' % A)
    xr = w.s([w.s([w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % A)], 'nn0red',
                  '( %s -> ( # ` W ) e. RR )' % A),
              w.s([lr, w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % A)], 'readdcld',
                  '( %s -> ( L + 3 ) e. RR )' % A)], 'remulcld', '( %s -> %s e. RR )' % (A, XW))
    egcl = w.s([w.s([w.s([w.s([w.s([out, ww], 'jca', '( %s -> ( %s /\\ W e. Word NN0 ) )' % (A, OUT)), one], 'jca',
                          '( %s -> ( ( %s /\\ W e. Word NN0 ) /\\ 1 e. NN0 ) )' % (A, OUT)), w0], 'jca',
                     '( %s -> ( ( ( %s /\\ W e. Word NN0 ) /\\ 1 e. NN0 ) /\\ (/) e. Word NN0 ) )' % (A, OUT)), etc], 'jca',
                    '( %s -> ( ( ( ( %s /\\ W e. Word NN0 ) /\\ 1 e. NN0 ) /\\ (/) e. Word NN0 ) /\\ EmptyTbl e. Tbl ) )' % (A, OUT)),
               w.inst('extractgocl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (A, EGW))
    egr = w.s([w.s([egcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. NN0 )' % (A, EGW))], 'nn0red',
              '( %s -> ( 2nd ` %s ) e. RR )' % (A, EGW))
    li = lin.linarith(w, A, [ci], '( 2nd ` %s ) <_ ( %s + 1 )' % (EGW, XW),
                      leaves={XW: xr, '( 2nd ` %s )' % EGW: egr})
    eqv, _ = rweq(w, A, '( 2nd ` %s )' % EX, EX, EGW, val)
    w.qed([eqv, li], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( %s + 1 ) )' % (A, EX, XW))
    run(w)
