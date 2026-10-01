"""Sortie A5, batch 15: the search at the paper's exact scales (Lean:
carmichaelSearch_eventually and carmichael_search_alg).
MM_DB=sorties/a5.mm python3 tools/gen/a5_ex.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib, a5lib
from tm import *
from a2lib import WH, EV, evand
from lin import linarith, nlinarith
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

SO = '( ( C ScalesOf E ) ` N )'
ZS = '( C zscale N )'
WS = '( Nfloor ` ( %s ^c ( ; 9 9 / ; ; 1 0 0 ) ) )' % ZS
YS = '( ( C yscaleE N ) ` E )'
TS = '( Tscale ` N )'
PWN = '( ( log ` N ) ^c ( 6 / 5 ) )'
HS = '( Nceil ` %s )' % PWN
IWX = '<. <. C , E >. , N >. InWindow <. <. %s , %s >. , <. %s , %s >. >.' % (ZS, WS, YS, TS)
TUP = '<. <. <. %s , %s >. , <. %s , %s >. >. , %s >.' % (ZS, WS, YS, TS, HS)

# --------------------------------------------------------------- a5ge1cxp
w = WH('a5ge1cxp', 'A real power of a number at least one, with a nonnegative exponent, is at least one.')
p1 = w.h('A e. RR')
p2 = w.h('1 <_ A')
p3 = w.h('B e. RR')
p4 = w.h('0 <_ B')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
o1 = w.s([num.fact(w, '1', 'RR')], 'a1i', '( ph -> 1 e. RR )')
o0 = w.s([num.fact(w, '1', 'ge0')], 'a1i', '( ph -> 0 <_ 1 )')
mono = w.s([o1, o0, p1, p3, p4, p2], 'cxple2ad', '( ph -> ( 1 ^c B ) <_ ( A ^c B ) )')
one = w.s([st([p3], 'recnd', 'B e. CC'), w.inst('1cxp')], 'syl', '( ph -> ( 1 ^c B ) = 1 )')
w.qed([st([one], 'eqcomd', '1 = ( 1 ^c B )'), mono], 'eqbrtrd', '( ph -> 1 <_ ( A ^c B ) )')
run(w)

# --------------------------------------------------------------- a5sc
w = WH('a5sc', 'The scales of the paper at the constants C and E lie in the window, with a threshold in range (Lean: inWindow_exact and the ceiling bounds of carmichaelSearch_eventually).')
h1 = w.h('C e. RR')
h2 = w.h('; ; ; 1 0 0 0 <_ C')
h3 = w.h('E e. RR')
h4 = w.h('0 < E')
h5 = w.h('E <_ ( 1 / 2 )')
h6 = w.h('N e. ( ZZ>= ` 3 )')
h7 = w.h('1 <_ ( ell2 ` N )')
h8 = w.h('1 <_ ( ell3 ` N )')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
lit = lambda t, k: w.s([num.fact(w, t, k)], 'a1i',
                       '( ph -> %s )' % (('%s e. %s' % (t, k)) if k in ('RR', 'NN0', 'NN', 'CC', 'RR+', 'ZZ')
                                         else {'ge0': '0 <_ %s' % t, 'gt0': '0 < %s' % t}[k]))
c1 = linarith(w, 'ph', [h2], '1 <_ C', leaves={'C': ('RR', h1)})
uz2 = st([h6, w.inst('uzuzle23')], 'syl', 'N e. ( ZZ>= ` 2 )')
nnn = st([uz2, w.inst('eluz2nn')], 'syl', 'N e. NN')
nn0 = st([nnn], 'nnnn0d', 'N e. NN0')
are = st([uz2, w.inst('ell2cl')], 'syl', '( ell2 ` N ) e. RR')
bre = st([h6, w.inst('ell3cl')], 'syl', '( ell3 ` N ) e. RR')
iwx = st([st([st([h1, c1], 'jca', '( C e. RR /\\ 1 <_ C )'),
              st([h3, h4, h5], '3jca', '( E e. RR /\\ 0 < E /\\ E <_ ( 1 / 2 ) )'),
              st([h6, h7, h8], '3jca', '( N e. ( ZZ>= ` 3 ) /\\ 1 <_ ( ell2 ` N ) /\\ 1 <_ ( ell3 ` N ) )')],
             '3jca',
             '( ( C e. RR /\\ 1 <_ C ) /\\ ( E e. RR /\\ 0 < E /\\ E <_ ( 1 / 2 ) ) /\\ ( N e. ( ZZ>= ` 3 ) /\\ 1 <_ ( ell2 ` N ) /\\ 1 <_ ( ell3 ` N ) ) )'),
            w.inst('inwinexact')], 'syl', IWX)
# 1 <_ ( C zscale N )
zn0 = st([st([h1, h6], 'jca', '( C e. RR /\\ N e. ( ZZ>= ` 3 ) )'), w.inst('zscalecl')], 'syl', '%s e. NN0' % ZS)
zre = st([zn0], 'nn0red', '%s e. RR' % ZS)
prod1 = nlinarith(w, 'ph', [h2, h7, h8], '1 <_ ( ( C x. ( ell2 ` N ) ) x. ( ell3 ` N ) )',
                  leaves={'C': ('RR', h1), '( ell2 ` N )': ('RR', are), '( ell3 ` N )': ('RR', bre)})
zlo = st([iwx, w.inst('inwinzlo')], 'syl', '( ( C x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) <_ %s' % ZS)
prodre = st([st([h1, are], 'remulcld', '( C x. ( ell2 ` N ) ) e. RR'), bre], 'remulcld',
            '( ( C x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) e. RR')
z1 = st([lit('1', 'RR'), prodre, zre, prod1, zlo], 'letrd', '1 <_ %s' % ZS)
# 1 <_ ( ( C yscaleE N ) ` E )
ome = st([lit('1', 'RR'), h3], 'resubcld', '( 1 - E ) e. RR')
ome0 = linarith(w, 'ph', [h5], '0 <_ ( 1 - E )', leaves={'E': ('RR', h3)})
zc1 = w.s([zre, z1, ome, ome0], 'a5ge1cxp', '( ph -> 1 <_ ( %s ^c ( 1 - E ) ) )' % ZS)
ylo = st([iwx, w.inst('inwinylo')], 'syl', '( %s ^c ( 1 - E ) ) <_ %s' % (ZS, YS))
yn0 = st([st([h1, h6, h3], '3jca', '( C e. RR /\\ N e. ( ZZ>= ` 3 ) /\\ E e. RR )'), w.inst('yscaleecl')], 'syl',
         '%s e. NN0' % YS)
y1 = st([lit('1', 'RR'), st([zre, st([zn0], 'nn0ge0d', '0 <_ %s' % ZS), ome], 'recxpcld',
                            '( %s ^c ( 1 - E ) ) e. RR' % ZS), st([yn0], 'nn0red', '%s e. RR' % YS),
         zc1, ylo], 'letrd', '1 <_ %s' % YS)
scal = st([st([st([st([h1, h3], 'jca', '( C e. RR /\\ E e. RR )'), h6], 'jca',
                  '( ( C e. RR /\\ E e. RR ) /\\ N e. ( ZZ>= ` 3 ) )'), z1], 'jca',
              '( ( ( C e. RR /\\ E e. RR ) /\\ N e. ( ZZ>= ` 3 ) ) /\\ 1 <_ %s )' % ZS), y1], 'jca',
           '( ( ( ( C e. RR /\\ E e. RR ) /\\ N e. ( ZZ>= ` 3 ) ) /\\ 1 <_ %s ) /\\ 1 <_ %s )' % (ZS, YS))
sosc = st([scal, w.inst('scalesofsc')], 'syl', '%s e. Scales' % SO)
# the projections of the tuple
soval = st([st([st([h1, h3], 'jca', '( C e. RR /\\ E e. RR )'), nn0], 'jca',
               '( ( C e. RR /\\ E e. RR ) /\\ N e. NN0 )'), w.inst('scalesofval')], 'syl', '%s = %s' % (SO, TUP))
opv = w.s([w.s([], 'opex', '<. <. %s , %s >. , <. %s , %s >. >. e. _V' % (ZS, WS, YS, TS))], 'a1i',
          '( ph -> <. <. %s , %s >. , <. %s , %s >. >. e. _V )' % (ZS, WS, YS, TS))
hsv = w.s([w.s([], 'fvex', '%s e. _V' % HS)], 'a1i', '( ph -> %s e. _V )' % HS)
so1 = st([w.s([soval], 'fveq2d', '( ph -> ( 1st ` %s ) = ( 1st ` %s ) )' % (SO, TUP)),
          st([opv, hsv, w.inst('op1stg')], 'syl2anc',
             '( 1st ` %s ) = <. <. %s , %s >. , <. %s , %s >. >.' % (TUP, ZS, WS, YS, TS))], 'eqtrd',
         '( 1st ` %s ) = <. <. %s , %s >. , <. %s , %s >. >.' % (SO, ZS, WS, YS, TS))
so2 = st([w.s([soval], 'fveq2d', '( ph -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (SO, TUP)),
          st([opv, hsv, w.inst('op2ndg')], 'syl2anc', '( 2nd ` %s ) = %s' % (TUP, HS))], 'eqtrd',
         '( 2nd ` %s ) = %s' % (SO, HS))
iwso = st([iwx, st([so1], 'eqcomd',
                   '<. <. %s , %s >. , <. %s , %s >. >. = ( 1st ` %s )' % (ZS, WS, YS, TS, SO))], 'breqtrd',
          '<. <. C , E >. , N >. InWindow ( 1st ` %s )' % SO)
# 1 <_ ( ( log ` N ) ^c ( 6 / 5 ) )
n1lt = st([uz2, w.inst('eluz2gt1')], 'syl', '1 < N')
nrp = st([nnn], 'nnrpd', 'N e. RR+')
lnre = st([nrp], 'relogcld', '( log ` N ) e. RR')
ln0 = st([st([nnn], 'nnred', 'N e. RR'), st([n1lt], 'ltled', '1 <_ N'), w.inst('logge0')], 'syl2anc',
         '0 <_ ( log ` N )')
lngt0 = st([st([nrp, w.inst('loggt0b')], 'syl', '( 0 < ( log ` N ) <-> 1 < N )'), n1lt], 'mpbird',
           '0 < ( log ` N )')
lnrp = st([lnre, lngt0], 'elrpd', '( log ` N ) e. RR+')
ell2e = st([nn0, w.inst('ell2val')], 'syl', '( ell2 ` N ) = ( log ` ( log ` N ) )')
lge0 = linarith(w, 'ph', [h7], '0 <_ ( ell2 ` N )', leaves={'( ell2 ` N )': ('RR', are)})
lg0b = st([lge0, ell2e], 'breqtrd', '0 <_ ( log ` ( log ` N ) )')
ln1 = st([lg0b, st([lnrp, w.inst('logge0b')], 'syl', '( 0 <_ ( log ` ( log ` N ) ) <-> 1 <_ ( log ` N ) )')],
         'mpbid', '1 <_ ( log ` N )')
pw1 = w.s([lnre, ln1, lit('( 6 / 5 )', 'RR'), lit('( 6 / 5 )', 'ge0')], 'a5ge1cxp', '( ph -> 1 <_ %s )' % PWN)
pwre = st([lnre, ln0, lit('( 6 / 5 )', 'RR')], 'recxpcld', '%s e. RR' % PWN)
hsn0 = st([pwre, w.inst('nceilcl')], 'syl', '%s e. NN0' % HS)
hsre = st([hsn0], 'nn0red', '%s e. RR' % HS)
lo = st([pwre, w.inst('nceilge')], 'syl', '%s <_ %s' % (PWN, HS))
pw0 = linarith(w, 'ph', [pw1], '0 <_ %s' % PWN, leaves={PWN: ('RR', pwre)})
hilt = st([st([pwre, pw0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (PWN, PWN)), w.inst('nceillt')], 'syl',
          '%s < ( %s + 1 )' % (HS, PWN))
hile = st([hilt], 'ltled', '%s <_ ( %s + 1 )' % (HS, PWN))
p16 = linarith(w, 'ph', [pw1], '( %s + 1 ) <_ ( ; 1 6 x. %s )' % (PWN, PWN), leaves={PWN: ('RR', pwre)})
hi = st([hsre, st([pwre, lit('1', 'RR')], 'readdcld', '( %s + 1 ) e. RR' % PWN),
         st([lit('; 1 6', 'RR'), pwre], 'remulcld', '( ; 1 6 x. %s ) e. RR' % PWN), hile, p16], 'letrd',
        '%s <_ ( ; 1 6 x. %s )' % (HS, PWN))
thlo = st([lo, st([so2], 'eqcomd', '%s = ( 2nd ` %s )' % (HS, SO))], 'breqtrd', '%s <_ ( 2nd ` %s )' % (PWN, SO))
thhi = st([so2, hi], 'eqbrtrd', '( 2nd ` %s ) <_ ( ; 1 6 x. %s )' % (SO, PWN))
w.qed([sosc, iwso, st([thlo, thhi], 'jca',
                      '( %s <_ ( 2nd ` %s ) /\\ ( 2nd ` %s ) <_ ( ; 1 6 x. %s ) )' % (PWN, SO, SO, PWN))], '3jca',
      '( ph -> ( %s e. Scales /\\ <. <. C , E >. , N >. InWindow ( 1st ` %s ) /\\ ( %s <_ ( 2nd ` %s ) /\\ ( 2nd ` %s ) <_ ( ; 1 6 x. %s ) ) ) )'
      % (SO, SO, PWN, SO, SO, PWN))
run(w)

# --------------------------------------------------------------- carmsev
SOn = '( ( C ScalesOf E ) ` n )'
PWn = '( ( log ` n ) ^c ( 6 / 5 ) )'
def CONCL(sr, nn='n', eps='A'):
    mmr = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % sr
    ssr = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % sr
    prd = 'prod_ i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i )' % (ssr, ssr)
    carm = '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (mmr, mmr, mmr, mmr)
    expb = '( exp ` ( ( ; ; 1 0 0 x. ( ell2 ` %s ) ) x. ( ell3 ` %s ) ) )' % (nn, nn)
    return ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
            '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
            '( %s = %s /\\ %s /\\ ( %s < %s /\\ %s <_ ( %s ^c ( 1 + %s ) ) ) ) ) /\\ '
            '( 2nd ` %s ) <_ %s )'
            % (sr, ssr, ssr, ssr, mmr, prd, carm, nn, mmr, mmr, nn, eps, sr, expb))
IWVn = '<. <. C , E >. , n >. InWindow ( 1st ` v )'
THv = '( %s <_ ( 2nd ` v ) /\\ ( 2nd ` v ) <_ ( ; 1 6 x. %s ) )' % (PWn, PWn)
GOALn = 'A. v e. Scales ( ( %s /\\ %s ) -> %s )' % (IWVn, THv, CONCL('( v Search n )'))
IWSO = '<. <. C , E >. , n >. InWindow ( 1st ` %s )' % SOn
THSO = '( %s <_ ( 2nd ` %s ) /\\ ( 2nd ` %s ) <_ ( ; 1 6 x. %s ) )' % (PWn, SOn, SOn, PWn)
SRCH = '( %s Search n )' % SOn
AGP3 = a5lib.dbhyps('step2w')[9]
AGP31 = a5lib.subvars(a5lib.dbhyps('step3w')[8], {'X': 'F'})
AGP3 = AGP3[len('( ph -> '):-2].strip()
AGP31 = AGP31[len('( ph -> '):-2].strip()
HTXT = ['C e. RR', '; ; ; 1 0 0 0 <_ C', 'E e. RR', '0 < E', 'E <_ ( 1 / 2 )', 'G e. RR', '0 < G',
        '; 6 0 <_ ( C x. G )', 'X e. NN0', AGP3, 'D e. RR', 'F e. NN0', AGP31, 'A e. RR', '0 < A']

w = WH('carmsev', 'At the paper\'s exact scales the search outputs a certified Carmichael number in ( n , n ^ ( 1 + A ) ] within the operation budget, for all large n (Lean: carmichaelSearch_eventually of SearchAlg.lean).')
H = [w.h(t) for t in HTXT]
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
sw = w.s(H, 'searchw', '( ph -> %s )' % EV(GOALn))
i1r = w.s([num.fact(w, '1', 'RR')], 'a1i', '( ph -> 1 e. RR )')
e1 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( ph -> %s )' % EV('n e. ( ZZ>= ` 3 )'))
e2 = st([i1r, w.inst('ell2ge')], 'syl', EV('1 <_ ( ell2 ` n )'))
e3 = st([i1r, w.inst('ell3ge')], 'syl', EV('1 <_ ( ell3 ` n )'))
BTX2 = [GOALn, 'n e. ( ZZ>= ` 3 )', '1 <_ ( ell2 ` n )', '1 <_ ( ell3 ` n )']
bun, BUN2 = evand(w, 'ph', [sw, e1, e2, e3], BTX2)
D0 = '( ph /\\ %s )' % BUN2
phs = w.s([], 'simpl', '( %s -> ph )' % D0)
parts = a5lib.unbundle(w, D0, w.s([], 'simpr', '( %s -> %s )' % (D0, BUN2)), BTX2)
rel = lambda i: w.s([phs, H[i]], 'syl', '( %s -> %s )' % (D0, HTXT[i]))
sc = w.s([rel(0), rel(1), rel(2), rel(3), rel(4), parts[1], parts[2], parts[3]], 'a5sc',
         '( %s -> ( %s e. Scales /\\ %s /\\ %s ) )' % (D0, SOn, IWSO, THSO))
scv = w.s([sc], 'simp1d', '( %s -> %s e. Scales )' % (D0, SOn))
imp, IMP = a5lib.unwind(w, D0, parts[0], GOALn, [('q', 'v', 'Scales', SOn, scv)])
ant = w.s([w.s([sc], 'simp2d', '( %s -> %s )' % (D0, IWSO)), w.s([sc], 'simp3d', '( %s -> %s )' % (D0, THSO))],
          'jca', '( %s -> ( %s /\\ %s ) )' % (D0, IWSO, THSO))
pw = w.s([ant, imp], 'mpd', '( %s -> %s )' % (D0, CONCL(SRCH)))
w.qed([bun, pw], 'evimd', '( ph -> %s )' % EV(CONCL(SRCH)))
run(w)

# --------------------------------------------------------------- carmsalg
def OUTC(eps):
    sr, nn = SRCH, 'n'
    mmr = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % sr
    ssr = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % sr
    prd = 'prod_ i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i )' % (ssr, ssr)
    carm = '( 1 < %s /\\ -. %s e. Prime /\\ A. a e. ZZ %s || ( ( a ^ %s ) - a ) )' % (mmr, mmr, mmr, mmr)
    return ('( ( 1st ` %s ) =/= ( inr ` (/) ) /\\ '
            '( ( Fun `\' %s /\\ A. b e. ran %s b e. Prime /\\ 3 <_ ( # ` %s ) ) /\\ '
            '( %s = %s /\\ %s /\\ ( %s < %s /\\ %s <_ ( %s ^c ( 1 + %s ) ) ) ) ) )'
            % (sr, ssr, ssr, ssr, mmr, prd, carm, nn, mmr, mmr, nn, eps))
def CST(c): return '( 2nd ` %s ) <_ ( exp ` ( ( %s x. ( ell2 ` n ) ) x. ( ell3 ` n ) ) )' % (SRCH, c)
def CPART(c): return '( 0 < %s /\\ %s )' % (c, EV(CST(c)))
CEX = 'E. r e. RR %s' % CPART('r')
EPART = 'A. e e. RR ( 0 < e -> %s )' % EV(OUTC('e'))

w = WH('carmsalg', 'Mickey\'s theorem in algorithmic form at the paper\'s exact scales, conditional on AGP Theorem 3 and AGP Theorem 3.1 (Lean: carmichael_search_alg of SearchAlg.lean).')
H2 = [w.h(t) for t in HTXT[:13]]
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)
# the cost half, at eps = 1
i1r = w.s([num.fact(w, '1', 'RR')], 'a1i', '( ph -> 1 e. RR )')
i10 = w.s([num.fact(w, '1', 'gt0')], 'a1i', '( ph -> 0 < 1 )')
ev1 = w.s(H2 + [i1r, i10], 'carmsev', '( ph -> %s )' % EV(CONCL(SRCH, eps='1')))
D1 = '( ph /\\ %s )' % CONCL(SRCH, eps='1')
cst1 = w.s([w.s([], 'simpr', '( %s -> %s )' % (D1, CONCL(SRCH, eps='1')))], 'simp3d',
           '( %s -> %s )' % (D1, CST('; ; 1 0 0')))
evc = w.s([ev1, cst1], 'evimd', '( ph -> %s )' % EV(CST('; ; 1 0 0')))
i100 = w.s([num.fact(w, '; ; 1 0 0', 'RR')], 'a1i', '( ph -> ; ; 1 0 0 e. RR )')
i1000 = w.s([num.fact(w, '; ; 1 0 0', 'gt0')], 'a1i', '( ph -> 0 < ; ; 1 0 0 )')
_idr = w.s([], 'id', '( r = ; ; 1 0 0 -> r = ; ; 1 0 0 )')
_sl, _n = w.wcongr(CPART('r'), {'r': '; ; 1 0 0'}, 'r = ; ; 1 0 0', {'r': _idr})
assert ' '.join(_n.split()) == ' '.join(CPART('; ; 1 0 0').split()), _n
cex = st([st([i100, st([i1000, evc], 'jca', CPART('; ; 1 0 0'))], 'jca',
              '( ; ; 1 0 0 e. RR /\\ %s )' % CPART('; ; 1 0 0')),
          w.s([_sl], 'rspcev', '( ( ; ; 1 0 0 e. RR /\\ %s ) -> %s )' % (CPART('; ; 1 0 0'), CEX))],
         'syl', CEX)
# the existence half, at every positive eps
E1 = '( ph /\\ e e. RR )'
E2 = '( %s /\\ 0 < e )' % E1
rel2 = lambda i: w.s([H2[i]], 'ad2antrr', '( %s -> %s )' % (E2, HTXT[i]))
ere = w.s([], 'simplr', '( %s -> e e. RR )' % E2)
e0 = w.s([], 'simpr', '( %s -> 0 < e )' % E2)
eve = w.s([rel2(i) for i in range(13)] + [ere, e0], 'carmsev', '( %s -> %s )' % (E2, EV(CONCL(SRCH, eps='e'))))
D2 = '( %s /\\ %s )' % (E2, CONCL(SRCH, eps='e'))
cc = w.s([], 'simpr', '( %s -> %s )' % (D2, CONCL(SRCH, eps='e')))
out = w.s([w.s([cc], 'simp1d', '( %s -> ( 1st ` %s ) =/= ( inr ` (/) ) )' % (D2, SRCH)),
           w.s([cc], 'simp2d', '( %s -> %s )' % (D2, OUTC('e').split(' /\\ ', 1)[1][:-2].strip()))], 'jca',
          '( %s -> %s )' % (D2, OUTC('e')))
evo = w.s([eve, out], 'evimd', '( %s -> %s )' % (E2, EV(OUTC('e'))))
impe = w.s([evo], 'ex', '( %s -> ( 0 < e -> %s ) )' % (E1, EV(OUTC('e'))))
alle = w.s([impe], 'ralrimiva', '( ph -> %s )' % EPART)
w.qed([cex, alle], 'jca', '( ph -> ( %s /\\ %s ) )' % (CEX, EPART))
run(w)

# --------------------------------------------------------------- c1algex
CND = '( ; 6 0 / G ) <_ ; ; ; 1 0 0 0'
CQ = 'if ( %s , ; ; ; 1 0 0 0 , ( ; 6 0 / G ) )' % CND
PP = '( G e. RR /\\ 0 < G )'
w = W('c1algex', 'The scale constant of the algorithm exists: some real is at least 1000 and has product at least 60 with the density constant (Lean: C1alg, thousand_le_C1alg and sixty_le_C1alg_mul_gammaWeak of SearchAlg.lean).')
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (PP, f))
gre = st([], 'simpl', 'G e. RR')
g0 = st([], 'simpr', '0 < G')
lit = lambda t, k: w.s([num.fact(w, t, k)], 'a1i', '( %s -> %s )'
                       % (PP, ('%s e. %s' % (t, k)) if k in ('RR', 'NN0', 'NN', 'CC', 'RR+', 'ZZ')
                          else {'ge0': '0 <_ %s' % t, 'gt0': '0 < %s' % t}[k]))
dre = st([lit('; 6 0', 'RR'), gre, st([g0], 'gt0ne0d', 'G =/= 0')], 'redivcld', '( ; 6 0 / G ) e. RR')
cre = st([lit('; ; ; 1 0 0 0', 'RR'), dre], 'ifcld', '%s e. RR' % CQ)
PT = '( %s /\\ %s )' % (PP, CND)
PF = '( %s /\\ -. %s )' % (PP, CND)
tt = w.s([w.s([], 'simpr', '( %s -> %s )' % (PT, CND))], 'iftrued',
         '( %s -> %s = ; ; ; 1 0 0 0 )' % (PT, CQ))
ff = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (PF, CND))], 'iffalsed',
         '( %s -> %s = ( ; 6 0 / G ) )' % (PF, CQ))
# 1000 <_ CQ
k1 = w.s([w.s([st([lit('; ; ; 1 0 0 0', 'RR')], 'leidd', '; ; ; 1 0 0 0 <_ ; ; ; 1 0 0 0')], 'adantr',
              '( %s -> ; ; ; 1 0 0 0 <_ ; ; ; 1 0 0 0 )' % PT),
          w.s([tt], 'eqcomd', '( %s -> ; ; ; 1 0 0 0 = %s )' % (PT, CQ))],
         'breqtrd', '( %s -> ; ; ; 1 0 0 0 <_ %s )' % (PT, CQ))
nlt = w.s([w.s([lit('; ; ; 1 0 0 0', 'RR')], 'adantr', '( %s -> ; ; ; 1 0 0 0 e. RR )' % PF),
           w.s([dre], 'adantr', '( %s -> ( ; 6 0 / G ) e. RR )' % PF), w.inst('ltnled')], 'syl2anc',
          '( %s -> ( ; ; ; 1 0 0 0 < ( ; 6 0 / G ) <-> -. ( ; 6 0 / G ) <_ ; ; ; 1 0 0 0 ) )' % PF)
k2 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> -. %s )' % (PF, CND)), nlt], 'mpbird',
                   '( %s -> ; ; ; 1 0 0 0 < ( ; 6 0 / G ) )' % PF)], 'ltled',
               '( %s -> ; ; ; 1 0 0 0 <_ ( ; 6 0 / G ) )' % PF),
          w.s([ff], 'eqcomd', '( %s -> ( ; 6 0 / G ) = %s )' % (PF, CQ))], 'breqtrd',
         '( %s -> ; ; ; 1 0 0 0 <_ %s )' % (PF, CQ))
kk = w.s([k1, k2], 'pm2.61dan', '( %s -> ; ; ; 1 0 0 0 <_ %s )' % (PP, CQ))
# ( 60 / G ) <_ CQ
m1 = w.s([w.s([], 'simpr', '( %s -> %s )' % (PT, CND)),
          w.s([tt], 'eqcomd', '( %s -> ; ; ; 1 0 0 0 = %s )' % (PT, CQ))], 'breqtrd',
         '( %s -> ( ; 6 0 / G ) <_ %s )' % (PT, CQ))
m2 = w.s([w.s([w.s([dre], 'adantr', '( %s -> ( ; 6 0 / G ) e. RR )' % PF)], 'leidd',
              '( %s -> ( ; 6 0 / G ) <_ ( ; 6 0 / G ) )' % PF),
          w.s([ff], 'eqcomd', '( %s -> ( ; 6 0 / G ) = %s )' % (PF, CQ))], 'breqtrd',
         '( %s -> ( ; 6 0 / G ) <_ %s )' % (PF, CQ))
mm = w.s([m1, m2], 'pm2.61dan', '( %s -> ( ; 6 0 / G ) <_ %s )' % (PP, CQ))
bi = st([lit('; 6 0', 'RR'), cre, st([gre, g0], 'jca', '( G e. RR /\\ 0 < G )'), w.inst('ledivmul')], 'syl3anc',
        '( ( ; 6 0 / G ) <_ %s <-> ; 6 0 <_ ( G x. %s ) )' % (CQ, CQ))
gc = st([mm, bi], 'mpbid', '; 6 0 <_ ( G x. %s )' % CQ)
gc2 = st([gc, st([st([gre], 'recnd', 'G e. CC'), st([cre], 'recnd', '%s e. CC' % CQ)], 'mulcomd', '( G x. %s ) = ( %s x. G )' % (CQ, CQ))], 'breqtrd',
         '; 6 0 <_ ( %s x. G )' % CQ)
BODY = lambda c: '( ; ; ; 1 0 0 0 <_ %s /\\ ; 6 0 <_ ( %s x. G ) )' % (c, c)
_idc = w.s([], 'id', '( c = %s -> c = %s )' % (CQ, CQ))
_slc, _nc = w.wcongr(BODY('c'), {'c': CQ}, 'c = %s' % CQ, {'c': _idc})
assert ' '.join(_nc.split()) == ' '.join(BODY(CQ).split()), _nc
w.qed([st([cre, st([kk, gc2], 'jca', BODY(CQ))], 'jca', '( %s e. RR /\\ %s )' % (CQ, BODY(CQ))),
       w.s([_slc], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. c e. RR %s )' % (CQ, BODY(CQ), BODY('c')))], 'syl',
      '( %s -> E. c e. RR %s )' % (PP, BODY('c')))
run(w)
