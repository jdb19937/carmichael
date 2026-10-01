"""Sortie C2 section 3.3b: the two edge bounds and the numeric bound for Phragmen-Lindelof."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *
from lin import linarith

RV = '( Re ` V )'; IV = '( Im ` V )'
SV = '( ( %s ^ 2 ) - ( %s ^ 2 ) )' % (RV, IV)
SS = '( %s - N )' % SV
GAUV = '( exp ` ( E x. ( ( V ^ 2 ) - N ) ) )'


def base(w, A0):
    vc = w.s([], 'simp11', '( %s -> V e. CC )' % A0)
    erp = w.s([], 'simp12', '( %s -> E e. RR+ )' % A0)
    nr = w.s([], 'simp13', '( %s -> N e. RR )' % A0)
    er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
    rv = w.s([vc], 'recld', '( %s -> %s e. RR )' % (A0, RV))
    iv = w.s([vc], 'imcld', '( %s -> %s e. RR )' % (A0, IV))
    rv2 = w.s([rv], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, RV))
    iv2 = w.s([iv], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, IV))
    iv20 = w.s([iv], 'sqge0d', '( %s -> 0 <_ ( %s ^ 2 ) )' % (A0, IV))
    ssr = w.s([w.s([rv2, iv2], 'resubcld', '( %s -> %s e. RR )' % (A0, SV)), nr], 'resubcld', '( %s -> %s e. RR )' % (A0, SS))
    ag = w.s([vc, er, nr, w.inst('absgau')], 'syl3anc', '( %s -> ( abs ` %s ) = ( exp ` ( E x. %s ) ) )' % (A0, GAUV, SS))
    gc = w.s([w.s([er, ssr], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A0, SS)), w.inst('reefcl')], 'syl',
             '( %s -> ( exp ` ( E x. %s ) ) e. RR )' % (A0, SS))
    gauc = w.s([w.s([w.s([er], 'recnd', '( %s -> E e. CC )' % A0), w.s([w.s([vc], 'sqcld', '( %s -> ( V ^ 2 ) e. CC )' % A0), w.s([nr], 'recnd', '( %s -> N e. CC )' % A0)], 'subcld', '( %s -> ( ( V ^ 2 ) - N ) e. CC )' % A0)], 'mulcld', '( %s -> ( E x. ( ( V ^ 2 ) - N ) ) e. CC )' % A0), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A0, GAUV))
    lv = {'( %s ^ 2 )' % RV: ('RR', rv2), '( %s ^ 2 )' % IV: ('RR', iv2), 'N': ('RR', nr)}
    return dict(vc=vc, erp=erp, nr=nr, er=er, rv=rv, iv=iv, rv2=rv2, iv2=iv2, iv20=iv20, ssr=ssr, ag=ag, gc=gc, gauc=gauc, lv=lv)


# ---- plbndv ----------------------------------------------------------------
w = W('plbndv', 'The Gaussian normaliser does not increase the modulus on a vertical edge of the strip.')
A0 = '( ( V e. CC /\\ E e. RR+ /\\ N e. RR ) /\\ ( ( ( %s ^ 2 ) <_ N /\\ U e. CC ) ) /\\ ( C e. RR /\\ ( abs ` U ) <_ C ) )' % RV
A0 = '( ( V e. CC /\\ E e. RR+ /\\ N e. RR ) /\\ ( ( %s ^ 2 ) <_ N /\\ U e. CC ) /\\ ( C e. RR /\\ ( abs ` U ) <_ C ) )' % RV
d = base(w, A0)
xle = w.s([], 'simp2l', '( %s -> ( %s ^ 2 ) <_ N )' % (A0, RV))
uc = w.s([], 'simp2r', '( %s -> U e. CC )' % A0)
cr = w.s([], 'simp3l', '( %s -> C e. RR )' % A0)
ule = w.s([], 'simp3r', '( %s -> ( abs ` U ) <_ C )' % A0)
au = w.s([uc], 'abscld', '( %s -> ( abs ` U ) e. RR )' % A0)
au0 = w.s([uc], 'absge0d', '( %s -> 0 <_ ( abs ` U ) )' % A0)
sle = linarith(w, A0, [xle, d['iv20']], '%s <_ 0' % SS, leaves=d['lv'])
esle = w.s([sle, w.s([d['ssr'], w.s([], '0red', '( %s -> 0 e. RR )' % A0), d['erp']], 'lemul2d',
                     '( %s -> ( %s <_ 0 <-> ( E x. %s ) <_ ( E x. 0 ) ) )' % (A0, SS, SS))], 'mpbid',
            '( %s -> ( E x. %s ) <_ ( E x. 0 ) )' % (A0, SS))
esle0 = w.s([esle, w.s([w.s([d['er']], 'recnd', '( %s -> E e. CC )' % A0)], 'mul01d', '( %s -> ( E x. 0 ) = 0 )' % A0)], 'breqtrd',
            '( %s -> ( E x. %s ) <_ 0 )' % (A0, SS))
efb = w.s([esle0, w.s([w.s([d['er'], d['ssr']], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A0, SS)), w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.inst('efle')], 'syl2anc',
                      '( %s -> ( ( E x. %s ) <_ 0 <-> ( exp ` ( E x. %s ) ) <_ ( exp ` 0 ) ) )' % (A0, SS, SS))], 'mpbid',
          '( %s -> ( exp ` ( E x. %s ) ) <_ ( exp ` 0 ) )' % (A0, SS))
efb1 = w.s([efb, w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( %s -> ( exp ` 0 ) = 1 )' % A0)], 'breqtrd',
           '( %s -> ( exp ` ( E x. %s ) ) <_ 1 )' % (A0, SS))
gle = w.s([efb1, d['ag']], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ 1 )' % (A0, GAUV)) if False else w.s(
    [w.s([d['ag']], 'idi', '( %s -> ( abs ` %s ) = ( exp ` ( E x. %s ) ) )' % (A0, GAUV, SS)), efb1], 'eqbrtrd',
    '( %s -> ( abs ` %s ) <_ 1 )' % (A0, GAUV))
prod = w.s([w.s([uc, d['gauc']], 'absmuld', '( %s -> ( abs ` ( U x. %s ) ) = ( ( abs ` U ) x. ( abs ` %s ) ) )' % (A0, GAUV, GAUV))], 'idi',
           '( %s -> ( abs ` ( U x. %s ) ) = ( ( abs ` U ) x. ( abs ` %s ) ) )' % (A0, GAUV, GAUV))
agr = w.s([d['gauc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, GAUV))
ag0 = w.s([d['gauc']], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, GAUV))
mul = w.s([au, cr, agr, w.s([], '1red', '( %s -> 1 e. RR )' % A0), au0, ag0, ule, gle], 'lemul12ad',
          '( %s -> ( ( abs ` U ) x. ( abs ` %s ) ) <_ ( C x. 1 ) )' % (A0, GAUV))
w.qed([w.s([prod, mul], 'eqbrtrd', '( %s -> ( abs ` ( U x. %s ) ) <_ ( C x. 1 ) )' % (A0, GAUV)),
       w.s([w.s([cr], 'recnd', '( %s -> C e. CC )' % A0)], 'mulridd', '( %s -> ( C x. 1 ) = C )' % A0)], 'breqtrd',
      '( %s -> ( abs ` ( U x. %s ) ) <_ C )' % (A0, GAUV)); run1(w)

# ---- plbndh ----------------------------------------------------------------
w = W('plbndh', 'The Gaussian normaliser beats the growth bound on a horizontal edge of a tall rectangle.')
A0 = '( ( V e. CC /\\ E e. RR+ /\\ N e. RR ) /\\ ( ( %s ^ 2 ) <_ N /\\ ( %s ^ 2 ) = ( T ^ 2 ) /\\ T e. RR ) /\\ ( U e. CC /\\ G e. RR /\\ ( abs ` U ) <_ G ) )' % (RV, IV)
d = base(w, A0)
xle = w.s([], 'simp21', '( %s -> ( %s ^ 2 ) <_ N )' % (A0, RV))
ieq = w.s([], 'simp2r', '( %s -> ( %s ^ 2 ) = ( T ^ 2 ) )' % (A0, IV)) if False else w.s([], 'simp22', '( %s -> ( %s ^ 2 ) = ( T ^ 2 ) )' % (A0, IV))
trr = w.s([], 'simp23', '( %s -> T e. RR )' % A0)
uc = w.s([], 'simp31', '( %s -> U e. CC )' % A0)
gr = w.s([], 'simp32', '( %s -> G e. RR )' % A0)
ule = w.s([], 'simp33', '( %s -> ( abs ` U ) <_ G )' % A0)
t2r = w.s([trr], 'resqcld', '( %s -> ( T ^ 2 ) e. RR )' % A0)
nt2 = w.s([t2r], 'renegcld', '( %s -> -u ( T ^ 2 ) e. RR )' % A0)
lv = dict(d['lv']); lv['( T ^ 2 )'] = ('RR', t2r)
sle = linarith(w, A0, [xle, ieq], '%s <_ -u ( T ^ 2 )' % SS, leaves=lv)
esle = w.s([sle, w.s([d['ssr'], nt2, d['erp']], 'lemul2d', '( %s -> ( %s <_ -u ( T ^ 2 ) <-> ( E x. %s ) <_ ( E x. -u ( T ^ 2 ) ) ) )' % (A0, SS, SS))],
           'mpbid', '( %s -> ( E x. %s ) <_ ( E x. -u ( T ^ 2 ) ) )' % (A0, SS))
ec_ = w.s([d['er']], 'recnd', '( %s -> E e. CC )' % A0)
t2c = w.s([t2r], 'recnd', '( %s -> ( T ^ 2 ) e. CC )' % A0)
esle2 = w.s([esle, w.s([ec_, t2c], 'mulneg2d', '( %s -> ( E x. -u ( T ^ 2 ) ) = -u ( E x. ( T ^ 2 ) ) )' % A0)], 'breqtrd',
            '( %s -> ( E x. %s ) <_ -u ( E x. ( T ^ 2 ) ) )' % (A0, SS))
et2r = w.s([d['er'], t2r], 'remulcld', '( %s -> ( E x. ( T ^ 2 ) ) e. RR )' % A0)
net2 = w.s([et2r], 'renegcld', '( %s -> -u ( E x. ( T ^ 2 ) ) e. RR )' % A0)
efb = w.s([esle2, w.s([w.s([d['er'], d['ssr']], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A0, SS)), net2, w.inst('efle')], 'syl2anc',
                      '( %s -> ( ( E x. %s ) <_ -u ( E x. ( T ^ 2 ) ) <-> ( exp ` ( E x. %s ) ) <_ ( exp ` -u ( E x. ( T ^ 2 ) ) ) ) )' % (A0, SS, SS))],
          'mpbid', '( %s -> ( exp ` ( E x. %s ) ) <_ ( exp ` -u ( E x. ( T ^ 2 ) ) ) )' % (A0, SS))
gle = w.s([w.s([d['ag']], 'idi', '( %s -> ( abs ` %s ) = ( exp ` ( E x. %s ) ) )' % (A0, GAUV, SS)), efb], 'eqbrtrd',
          '( %s -> ( abs ` %s ) <_ ( exp ` -u ( E x. ( T ^ 2 ) ) ) )' % (A0, GAUV))
au = w.s([uc], 'abscld', '( %s -> ( abs ` U ) e. RR )' % A0)
au0 = w.s([uc], 'absge0d', '( %s -> 0 <_ ( abs ` U ) )' % A0)
agr = w.s([d['gauc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, GAUV))
ag0 = w.s([d['gauc']], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, GAUV))
efr = w.s([net2, w.inst('reefcl')], 'syl', '( %s -> ( exp ` -u ( E x. ( T ^ 2 ) ) ) e. RR )' % A0)
prod = w.s([uc, d['gauc']], 'absmuld', '( %s -> ( abs ` ( U x. %s ) ) = ( ( abs ` U ) x. ( abs ` %s ) ) )' % (A0, GAUV, GAUV))
mul = w.s([au, gr, agr, efr, au0, ag0, ule, gle], 'lemul12ad',
          '( %s -> ( ( abs ` U ) x. ( abs ` %s ) ) <_ ( G x. ( exp ` -u ( E x. ( T ^ 2 ) ) ) ) )' % (A0, GAUV))
w.qed([prod, mul], 'eqbrtrd', '( %s -> ( abs ` ( U x. %s ) ) <_ ( G x. ( exp ` -u ( E x. ( T ^ 2 ) ) ) ) )' % (A0, GAUV)); run1(w)

# ---- plnum -----------------------------------------------------------------
LGX = '( log ` ( C / K ) )'
ABG = '( abs ` %s )' % LGX
ETT = '( E x. ( T ^ 2 ) )'
LTT = '( L x. T )'
w = W('plnum', 'The height choice makes the Gaussian beat the exponential growth on the horizontal edges.')
A0 = ('( ( K e. RR+ /\\ C e. RR+ /\\ E e. RR+ ) /\\ ( L e. RR /\\ 0 <_ L /\\ T e. RR ) '
      '/\\ ( 1 <_ T /\\ ( L + %s ) <_ ( E x. T ) ) )' % ABG)
krp = w.s([], 'simp11', '( %s -> K e. RR+ )' % A0)
crp = w.s([], 'simp12', '( %s -> C e. RR+ )' % A0)
erp = w.s([], 'simp13', '( %s -> E e. RR+ )' % A0)
lr = w.s([], 'simp21', '( %s -> L e. RR )' % A0)
l0 = w.s([], 'simp22', '( %s -> 0 <_ L )' % A0)
tr = w.s([], 'simp23', '( %s -> T e. RR )' % A0)
t1 = w.s([], 'simp3l', '( %s -> 1 <_ T )' % A0)
hyp = w.s([], 'simp3r', '( %s -> ( L + %s ) <_ ( E x. T ) )' % (A0, ABG))
kr = w.s([krp], 'rpred', '( %s -> K e. RR )' % A0)
cr = w.s([crp], 'rpred', '( %s -> C e. RR )' % A0)
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
ckrp = w.s([crp, krp], 'rpdivcld', '( %s -> ( C / K ) e. RR+ )' % A0)
gr = w.s([ckrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, LGX))
nga, pga, agr = absbnds(w, A0, LGX, gr)
ag0 = w.s([w.s([gr], 'recnd', '( %s -> %s e. CC )' % (A0, LGX))], 'absge0d', '( %s -> 0 <_ %s )' % (A0, ABG))
etr = w.s([er, tr], 'remulcld', '( %s -> ( E x. T ) e. RR )' % A0)
ZZ = '( ( E x. T ) - L )'
zr = w.s([etr, lr], 'resubcld', '( %s -> %s e. RR )' % (A0, ZZ))
lv = {'L': ('RR', lr), 'T': ('RR', tr), '( E x. T )': ('RR', etr), ABG: ('RR', agr), LGX: ('RR', gr)}
z0 = linarith(w, A0, [hyp, ag0], '0 <_ %s' % ZZ, leaves=lv)
gz = linarith(w, A0, [hyp], '%s <_ %s' % (ABG, ZZ), leaves=lv)
m1 = w.s([w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr, w.s([zr, z0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, ZZ, ZZ))], '3jca',
               '( %s -> ( 1 e. RR /\\ T e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A0, ZZ, ZZ)), t1, w.inst('lemul1a')], 'syl2anc',
          '( %s -> ( 1 x. %s ) <_ ( T x. %s ) )' % (A0, ZZ, ZZ))
zc = w.s([zr], 'recnd', '( %s -> %s e. CC )' % (A0, ZZ))
m2 = w.s([w.s([w.s([zc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, ZZ, ZZ))], 'eqcomd', '( %s -> %s = ( 1 x. %s ) )' % (A0, ZZ, ZZ)), m1],
         'eqbrtrd', '( %s -> %s <_ ( T x. %s ) )' % (A0, ZZ, ZZ))
tzr = w.s([tr, zr], 'remulcld', '( %s -> ( T x. %s ) e. RR )' % (A0, ZZ))
m3 = w.s([agr, zr, tzr, gz, m2], 'letrd', '( %s -> %s <_ ( T x. %s ) )' % (A0, ABG, ZZ))
tc = w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)
ec_ = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
lc = w.s([lr], 'recnd', '( %s -> L e. CC )' % A0)
etc = w.s([ec_, tc], 'mulcld', '( %s -> ( E x. T ) e. CC )' % A0)
d1 = w.s([tc, etc, lc], 'subdid', '( %s -> ( T x. %s ) = ( ( T x. ( E x. T ) ) - ( T x. L ) ) )' % (A0, ZZ))
d2a = w.s([tc, ec_, tc], 'mul12d', '( %s -> ( T x. ( E x. T ) ) = ( E x. ( T x. T ) ) )' % A0)
d2b = w.s([w.s([w.s([tc], 'sqvald', '( %s -> ( T ^ 2 ) = ( T x. T ) )' % A0)], 'eqcomd', '( %s -> ( T x. T ) = ( T ^ 2 ) )' % A0)], 'oveq2d',
          '( %s -> ( E x. ( T x. T ) ) = %s )' % (A0, ETT))
d2c = w.s([d2a, d2b], 'eqtrd', '( %s -> ( T x. ( E x. T ) ) = %s )' % (A0, ETT))
d3 = w.s([tc, lc], 'mulcomd', '( %s -> ( T x. L ) = %s )' % (A0, LTT))
dfin = w.s([d1, w.s([d2c, d3], 'oveq12d', '( %s -> ( ( T x. ( E x. T ) ) - ( T x. L ) ) = ( %s - %s ) )' % (A0, ETT, LTT))], 'eqtrd',
           '( %s -> ( T x. %s ) = ( %s - %s ) )' % (A0, ZZ, ETT, LTT))
m4 = w.s([m3, dfin], 'breqtrd', '( %s -> %s <_ ( %s - %s ) )' % (A0, ABG, ETT, LTT))
ngr = w.s([gr], 'renegcld', '( %s -> -u %s e. RR )' % (A0, LGX))
nga2 = w.s([w.s([ngr, w.inst('leabs')], 'syl', '( %s -> -u %s <_ ( abs ` -u %s ) )' % (A0, LGX, LGX)),
            w.s([w.s([gr], 'recnd', '( %s -> %s e. CC )' % (A0, LGX))], 'absnegd', '( %s -> ( abs ` -u %s ) = %s )' % (A0, LGX, ABG))],
           'breqtrd', '( %s -> -u %s <_ %s )' % (A0, LGX, ABG))
ettr = w.s([er, w.s([tr], 'resqcld', '( %s -> ( T ^ 2 ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, ETT))
lttr = w.s([lr, tr], 'remulcld', '( %s -> %s e. RR )' % (A0, LTT))
dr = w.s([ettr, lttr], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, ETT, LTT))
m5 = w.s([ngr, agr, dr, nga2, m4], 'letrd', '( %s -> -u %s <_ ( %s - %s ) )' % (A0, LGX, ETT, LTT))
m6 = w.s([gr, dr, m5], 'lenegcon1d', '( %s -> -u ( %s - %s ) <_ %s )' % (A0, ETT, LTT, LGX))
m7 = w.s([w.s([ettr], 'recnd', '( %s -> %s e. CC )' % (A0, ETT)), w.s([lttr], 'recnd', '( %s -> %s e. CC )' % (A0, LTT))], 'negsubdi2d',
         '( %s -> -u ( %s - %s ) = ( %s - %s ) )' % (A0, ETT, LTT, LTT, ETT))
key = w.s([w.s([m7], 'eqcomd', '( %s -> ( %s - %s ) = -u ( %s - %s ) )' % (A0, LTT, ETT, ETT, LTT)), m6], 'eqbrtrd',
          '( %s -> ( %s - %s ) <_ %s )' % (A0, LTT, ETT, LGX))
dif2r = w.s([lttr, ettr], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, LTT, ETT))
ex1 = w.s([key, w.s([dif2r, gr, w.inst('efle')], 'syl2anc', '( %s -> ( ( %s - %s ) <_ %s <-> ( exp ` ( %s - %s ) ) <_ ( exp ` %s ) ) )' % (A0, LTT, ETT, LGX, LTT, ETT, LGX))],
           'mpbid', '( %s -> ( exp ` ( %s - %s ) ) <_ ( exp ` %s ) )' % (A0, LTT, ETT, LGX))
ex2 = w.s([ex1, w.s([ckrp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` %s ) = ( C / K ) )' % (A0, LGX))], 'breqtrd',
          '( %s -> ( exp ` ( %s - %s ) ) <_ ( C / K ) )' % (A0, LTT, ETT))
mk = w.s([ex2, w.s([w.s([dif2r, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( %s - %s ) ) e. RR )' % (A0, LTT, ETT)),
                    w.s([cr, krp], 'rerpdivcld', '( %s -> ( C / K ) e. RR )' % A0), krp], 'lemul2d',
                   '( %s -> ( ( exp ` ( %s - %s ) ) <_ ( C / K ) <-> ( K x. ( exp ` ( %s - %s ) ) ) <_ ( K x. ( C / K ) ) ) )' % (A0, LTT, ETT, LTT, ETT))],
         'mpbid', '( %s -> ( K x. ( exp ` ( %s - %s ) ) ) <_ ( K x. ( C / K ) ) )' % (A0, LTT, ETT))
mk2 = w.s([mk, w.s([w.s([cr], 'recnd', '( %s -> C e. CC )' % A0), w.s([kr], 'recnd', '( %s -> K e. CC )' % A0), w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)],
                   'divcan2d', '( %s -> ( K x. ( C / K ) ) = C )' % A0)], 'breqtrd',
           '( %s -> ( K x. ( exp ` ( %s - %s ) ) ) <_ C )' % (A0, LTT, ETT))
lttc = w.s([lttr], 'recnd', '( %s -> %s e. CC )' % (A0, LTT))
ettc = w.s([ettr], 'recnd', '( %s -> %s e. CC )' % (A0, ETT))
eae = w.s([lttc, w.s([ettc], 'negcld', '( %s -> -u %s e. CC )' % (A0, ETT)), w.inst('efadd')], 'syl2anc',
          '( %s -> ( exp ` ( %s + -u %s ) ) = ( ( exp ` %s ) x. ( exp ` -u %s ) ) )' % (A0, LTT, ETT, LTT, ETT))
nsu = w.s([lttc, ettc], 'negsubd', '( %s -> ( %s + -u %s ) = ( %s - %s ) )' % (A0, LTT, ETT, LTT, ETT))
eq1 = w.s([w.s([w.s([nsu], 'eqcomd', '( %s -> ( %s - %s ) = ( %s + -u %s ) )' % (A0, LTT, ETT, LTT, ETT))], 'fveq2d',
                '( %s -> ( exp ` ( %s - %s ) ) = ( exp ` ( %s + -u %s ) ) )' % (A0, LTT, ETT, LTT, ETT)), eae], 'eqtrd',
          '( %s -> ( exp ` ( %s - %s ) ) = ( ( exp ` %s ) x. ( exp ` -u %s ) ) )' % (A0, LTT, ETT, LTT, ETT))
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
eac = w.s([w.s([lttr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` %s ) e. RR )' % (A0, LTT))], 'recnd', '( %s -> ( exp ` %s ) e. CC )' % (A0, LTT))
ebc = w.s([w.s([w.s([ettr], 'renegcld', '( %s -> -u %s e. RR )' % (A0, ETT)), w.inst('reefcl')], 'syl', '( %s -> ( exp ` -u %s ) e. RR )' % (A0, ETT))], 'recnd',
          '( %s -> ( exp ` -u %s ) e. CC )' % (A0, ETT))
eq2 = w.s([w.s([eq1], 'oveq2d', '( %s -> ( K x. ( exp ` ( %s - %s ) ) ) = ( K x. ( ( exp ` %s ) x. ( exp ` -u %s ) ) ) )' % (A0, LTT, ETT, LTT, ETT)),
           w.s([w.s([kc, eac, ebc], 'mulassd', '( %s -> ( ( K x. ( exp ` %s ) ) x. ( exp ` -u %s ) ) = ( K x. ( ( exp ` %s ) x. ( exp ` -u %s ) ) ) )' % (A0, LTT, ETT, LTT, ETT))], 'eqcomd',
               '( %s -> ( K x. ( ( exp ` %s ) x. ( exp ` -u %s ) ) ) = ( ( K x. ( exp ` %s ) ) x. ( exp ` -u %s ) ) )' % (A0, LTT, ETT, LTT, ETT))], 'eqtrd',
          '( %s -> ( K x. ( exp ` ( %s - %s ) ) ) = ( ( K x. ( exp ` %s ) ) x. ( exp ` -u %s ) ) )' % (A0, LTT, ETT, LTT, ETT))
w.qed([w.s([eq2], 'eqcomd', '( %s -> ( ( K x. ( exp ` %s ) ) x. ( exp ` -u %s ) ) = ( K x. ( exp ` ( %s - %s ) ) ) )' % (A0, LTT, ETT, LTT, ETT)), mk2],
      'eqbrtrd', '( %s -> ( ( K x. ( exp ` %s ) ) x. ( exp ` -u %s ) ) <_ C )' % (A0, LTT, ETT)); run1(w)
