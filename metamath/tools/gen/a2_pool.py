"""Sortie A2, batch 7: the size of the step-3 pool."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

FN0 = '( ~P NN0 i^i Fin )'
LM = '( Lmod ` Q )'
XC = '( xceil ` Q )'
DIV = '{ m e. ( 1 ... %s ) | m || %s }' % (LM, LM)
V = lambda d: '( ( %s x. K ) + 1 )' % d
C3 = lambda d: '( %s <_ %s /\\ %s e. Prime /\\ Z < %s )' % (V(d), XC, V(d), V(d))
C2 = lambda d: '( %s <_ %s /\\ %s e. Prime )' % (V(d), XC, V(d))
R = '{ d e. %s | %s }' % (DIV, C3('d'))
RE = '{ e e. %s | %s }' % (DIV, C3('e'))
R0 = '{ d e. %s | %s }' % (DIV, C2('d'))
POOL = '( ( Q pool Z ) ` K )'
A = '( Q e. %s /\\ Z e. NN0 /\\ K e. NN )' % FN0


def ctx(w):
    qfn = w.s([], 'simp1', '( %s -> Q e. %s )' % (A, FN0))
    zn0 = w.s([], 'simp2', '( %s -> Z e. NN0 )' % A)
    knn = w.s([], 'simp3', '( %s -> K e. NN )' % A)
    return qfn, zn0, knn


def indiv(w, ante, v, st):
    """from ( ante -> v e. DIV ) get ( ante -> v e. NN ) and ( ante -> v e. CC )"""
    idm = w.s([], 'id', '( m = %s -> m = %s )' % (v, v))
    cg, _b = w.wcongr('m || %s' % LM, {'m': v}, 'm = %s' % v, {'m': idm})
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ %s || %s ) )' % (v, DIV, v, LM, v, LM))
    b = w.s([st, w.s([el], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ %s || %s ) ) )' % (ante, v, DIV, v, LM, v, LM))], 'mpbid',
            '( %s -> ( %s e. ( 1 ... %s ) /\\ %s || %s ) )' % (ante, v, LM, v, LM))
    fz = w.s([b], 'simpld', '( %s -> %s e. ( 1 ... %s ) )' % (ante, v, LM))
    nn = w.s([fz, w.inst('elfznn')], 'syl', '( %s -> %s e. NN )' % (ante, v))
    return nn, w.s([nn], 'nncnd', '( %s -> %s e. CC )' % (ante, v))


# ------------------------------------------------------------------ poolcard
w = W('poolcard', 'The pool has as many elements as the set of shifts that generate it (Lean: Finset.card_image_of_injective, Step3W.lean hpool_card).')
qfn, zn0, knn = ctx(w)
kn0 = w.s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % A)
pv = w.s([qfn, zn0, kn0, w.inst('poolval')], 'syl3anc', '( %s -> %s = ran ( d e. %s |-> %s ) )' % (A, POOL, R, V('d')))
# rename the bound variable of the domain so that d does not occur in it
idd = w.s([], 'id', '( d = e -> d = e )')
cgd, _b = w.wcongr(C3('d'), {'d': 'e'}, 'd = e', {'d': idd})
cb = w.s([cgd], 'cbvrabv', '%s = %s' % (R, RE))
nfph = w.s([], 'nfv', 'F/ d %s' % A)
mq = w.s([nfph, w.s([cb], 'a1i', '( %s -> %s = %s )' % (A, R, RE))], 'mpteq1df',
         '( %s -> ( d e. %s |-> %s ) = ( d e. %s |-> %s ) )' % (A, R, V('d'), RE, V('d')))
rn = w.s([mq], 'rneqd', '( %s -> ran ( d e. %s |-> %s ) = ran ( d e. %s |-> %s ) )' % (A, R, V('d'), RE, V('d')))
pv2 = w.s([pv, rn], 'eqtrd', '( %s -> %s = ran ( d e. %s |-> %s ) )' % (A, POOL, RE, V('d')))
# ( d e. RE |-> V(d) ) : RE -1-1-> NN
ide = w.s([], 'id', '( e = d -> e = d )')
cge, _b2 = w.wcongr(C3('e'), {'e': 'd'}, 'e = d', {'e': ide})
elre = w.s([cge], 'elrab', '( d e. %s <-> ( d e. %s /\\ %s ) )' % (RE, DIV, C3('d')))
B1 = '( %s /\\ d e. %s )' % (A, RE)
dre = w.s([], 'simpr', '( %s -> d e. %s )' % (B1, RE))
ddiv = w.s([w.s([dre, w.s([elre], 'a1i', '( %s -> ( d e. %s <-> ( d e. %s /\\ %s ) ) )' % (B1, RE, DIV, C3('d')))], 'mpbid',
               '( %s -> ( d e. %s /\\ %s ) )' % (B1, DIV, C3('d')))], 'simpld', '( %s -> d e. %s )' % (B1, DIV))
dnn, dcn = indiv(w, B1, 'd', ddiv)
knnb = w.s([knn], 'adantr', '( %s -> K e. NN )' % B1)
vnn = w.s([dnn, knnb], 'nnmulcld', '( %s -> ( d x. K ) e. NN )' % B1)
vnn2 = w.s([vnn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (B1, V('d')))
h1 = w.s([vnn2], 'ex', '( %s -> ( d e. %s -> %s e. NN ) )' % (A, RE, V('d')))
# injectivity
B2 = '( %s /\\ ( d e. %s /\\ f e. %s ) )' % (A, RE, RE)
dre2 = w.s([], 'simprl', '( %s -> d e. %s )' % (B2, RE))
fre2 = w.s([], 'simprr', '( %s -> f e. %s )' % (B2, RE))
cgf, _b3 = w.wcongr(C3('e'), {'e': 'f'}, 'e = f', {'e': w.s([], 'id', '( e = f -> e = f )')})
elrf = w.s([cgf], 'elrab', '( f e. %s <-> ( f e. %s /\\ %s ) )' % (RE, DIV, C3('f')))
ddiv2 = w.s([w.s([dre2, w.s([elre], 'a1i', '( %s -> ( d e. %s <-> ( d e. %s /\\ %s ) ) )' % (B2, RE, DIV, C3('d')))], 'mpbid',
                 '( %s -> ( d e. %s /\\ %s ) )' % (B2, DIV, C3('d')))], 'simpld', '( %s -> d e. %s )' % (B2, DIV))
fdiv2 = w.s([w.s([fre2, w.s([elrf], 'a1i', '( %s -> ( f e. %s <-> ( f e. %s /\\ %s ) ) )' % (B2, RE, DIV, C3('f')))], 'mpbid',
                 '( %s -> ( f e. %s /\\ %s ) )' % (B2, DIV, C3('f')))], 'simpld', '( %s -> f e. %s )' % (B2, DIV))
dnn2, dcn2 = indiv(w, B2, 'd', ddiv2)
fnn2, fcn2 = indiv(w, B2, 'f', fdiv2)
knnc = w.s([knn], 'adantr', '( %s -> K e. NN )' % B2)
kcn = w.s([knnc], 'nncnd', '( %s -> K e. CC )' % B2)
kne = w.s([knnc], 'nnne0d', '( %s -> K =/= 0 )' % B2)
dk = w.s([dcn2, kcn], 'mulcld', '( %s -> ( d x. K ) e. CC )' % B2)
fk = w.s([fcn2, kcn], 'mulcld', '( %s -> ( f x. K ) e. CC )' % B2)
one = w.s([], '1cnd', '( %s -> 1 e. CC )' % B2)
ac = w.s([dk, fk, one], 'addcan2d', '( %s -> ( %s = %s <-> ( d x. K ) = ( f x. K ) ) )' % (B2, V('d'), V('f')))
mc = w.s([dcn2, fcn2, kcn, kne], 'mulcan2d', '( %s -> ( ( d x. K ) = ( f x. K ) <-> d = f ) )' % B2)
inj = w.s([ac, mc], 'bitrd', '( %s -> ( %s = %s <-> d = f ) )' % (B2, V('d'), V('f')))
h2 = w.s([inj], 'ex', '( %s -> ( ( d e. %s /\\ f e. %s ) -> ( %s = %s <-> d = f ) ) )' % (A, RE, RE, V('d'), V('f')))
f1 = w.s([h1, h2], 'dom2lem', '( %s -> ( d e. %s |-> %s ) : %s -1-1-> NN )' % (A, RE, V('d'), RE))
mex = w.s([w.s([w.s([], 'fzfi', '( 1 ... %s ) e. Fin' % LM), w.inst('rabfi')], 'ax-mp', '%s e. Fin' % DIV), w.inst('rabfi')], 'ax-mp', '%s e. Fin' % RE)
mexv = w.s([mex], 'elexi', '%s e. _V' % RE)
fex = w.s([mexv], 'mptex', '( d e. %s |-> %s ) e. _V' % (RE, V('d')))
hf = w.s([w.s([fex], 'a1i', '( %s -> ( d e. %s |-> %s ) e. _V )' % (A, RE, V('d'))), f1, w.inst('hashf1dmrn')], 'syl2anc',
         '( %s -> ( # ` %s ) = ( # ` ran ( d e. %s |-> %s ) ) )' % (A, RE, RE, V('d')))
hp = w.s([w.s([pv2], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ran ( d e. %s |-> %s ) ) )' % (A, POOL, RE, V('d')))], 'eqcomd',
         '( %s -> ( # ` ran ( d e. %s |-> %s ) ) = ( # ` %s ) )' % (A, RE, V('d'), POOL))
hr = w.s([w.s([cb], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (R, RE))], 'a1i', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, R, RE))
w.qed([w.s([hr, hf], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` ran ( d e. %s |-> %s ) ) )' % (A, R, RE, V('d'))), hp], 'eqtrd',
      '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, R, POOL))
run(w)

# ----------------------------------------------------------------- poolcard2
w = W('poolcard2', 'Dropping the lower bound z from the pool condition adds at most z + 1 elements (Lean: Step3W.lean hcard_split).')
qfn, zn0, knn = ctx(w)
divfi = w.s([w.s([], 'fzfi', '( 1 ... %s ) e. Fin' % LM), w.inst('rabfi')], 'ax-mp', '%s e. Fin' % DIV)
r0fi = w.s([w.s([divfi, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % R0)], 'a1i', '( %s -> %s e. Fin )' % (A, R0))
rfi = w.s([w.s([divfi, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % R)], 'a1i', '( %s -> %s e. Fin )' % (A, R))
# R C_ R0
B = '( %s /\\ d e. %s )' % (A, DIV)
imp3 = w.s([], 'simp1', '( %s -> %s <_ %s )' % (C3('d'), V('d'), XC))
imp3b = w.s([], 'simp2', '( %s -> %s e. Prime )' % (C3('d'), V('d')))
i2 = w.s([imp3, imp3b], 'jca', '( %s -> %s )' % (C3('d'), C2('d')))
i2d = w.s([i2], 'a1i', '( %s -> ( %s -> %s ) )' % (B, C3('d'), C2('d')))
sub = w.s([i2d], 'ss2rabdv', '( %s -> %s C_ %s )' % (A, R, R0))
# ( R0 \ R ) C_ ( 0 ... Z )
D = '( %s /\\ f e. ( %s \\ %s ) )' % (A, R0, R)
fd = w.s([], 'simpr', '( %s -> f e. ( %s \\ %s ) )' % (D, R0, R))
fr0 = w.s([fd, w.inst('eldifi')], 'syl', '( %s -> f e. %s )' % (D, R0))
fnr = w.s([fd, w.inst('eldifn')], 'syl', '( %s -> -. f e. %s )' % (D, R))
idd = w.s([], 'id', '( d = f -> d = f )')
cg2, _b = w.wcongr(C2('d'), {'d': 'f'}, 'd = f', {'d': idd})
el0 = w.s([cg2], 'elrab', '( f e. %s <-> ( f e. %s /\\ %s ) )' % (R0, DIV, C2('f')))
b0 = w.s([fr0, w.s([el0], 'a1i', '( %s -> ( f e. %s <-> ( f e. %s /\\ %s ) ) )' % (D, R0, DIV, C2('f')))], 'mpbid',
         '( %s -> ( f e. %s /\\ %s ) )' % (D, DIV, C2('f')))
fdiv = w.s([b0], 'simpld', '( %s -> f e. %s )' % (D, DIV))
fc2 = w.s([b0], 'simprd', '( %s -> %s )' % (D, C2('f')))
cg3, _b2 = w.wcongr(C3('d'), {'d': 'f'}, 'd = f', {'d': idd})
el3 = w.s([cg3], 'elrab', '( f e. %s <-> ( f e. %s /\\ %s ) )' % (R, DIV, C3('f')))
E = '( %s /\\ Z < %s )' % (D, V('f'))
c3f = w.s([w.s([w.s([fc2], 'simpld', '( %s -> %s <_ %s )' % (D, V('f'), XC))], 'adantr', '( %s -> %s <_ %s )' % (E, V('f'), XC)),
           w.s([w.s([fc2], 'simprd', '( %s -> %s e. Prime )' % (D, V('f')))], 'adantr', '( %s -> %s e. Prime )' % (E, V('f'))),
           w.s([], 'simpr', '( %s -> Z < %s )' % (E, V('f')))], '3jca', '( %s -> %s )' % (E, C3('f')))
inr = w.s([w.s([w.s([fdiv], 'adantr', '( %s -> f e. %s )' % (E, DIV)), c3f], 'jca', '( %s -> ( f e. %s /\\ %s ) )' % (E, DIV, C3('f'))),
           w.s([el3], 'a1i', '( %s -> ( f e. %s <-> ( f e. %s /\\ %s ) ) )' % (E, R, DIV, C3('f')))], 'mpbird',
          '( %s -> f e. %s )' % (E, R))
nlt = w.s([inr, w.s([fnr], 'adantr', '( %s -> -. f e. %s )' % (E, R))], 'pm2.65da', '( %s -> -. Z < %s )' % (D, V('f')))
fnn, fcn = indiv(w, D, 'f', fdiv)
knnd = w.s([knn], 'adantr', '( %s -> K e. NN )' % D)
zrd = w.s([w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)], 'adantr', '( %s -> Z e. RR )' % D)
fre = w.s([fnn], 'nnred', '( %s -> f e. RR )' % D)
vre = w.s([w.s([fnn, knnd], 'nnmulcld', '( %s -> ( f x. K ) e. NN )' % D)], 'nnred', '( %s -> ( f x. K ) e. RR )' % D)
vre1 = w.s([vre, w.s([], '1red', '( %s -> 1 e. RR )' % D)], 'readdcld', '( %s -> %s e. RR )' % (D, V('f')))
le = w.s([nlt, w.s([vre1, zrd, w.inst('lenlt')], 'syl2anc', '( %s -> ( %s <_ Z <-> -. Z < %s ) )' % (D, V('f'), V('f')))], 'mpbird',
         '( %s -> %s <_ Z )' % (D, V('f')))
k1 = w.s([knnd], 'nnge1d', '( %s -> 1 <_ K )' % D)
kre = w.s([knnd], 'nnred', '( %s -> K e. RR )' % D)
f0 = w.s([w.s([fnn], 'nnnn0d', '( %s -> f e. NN0 )' % D)], 'nn0ge0d', '( %s -> 0 <_ f )' % D)
mg = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % D), kre, fre, f0, k1], 'lemul2ad', '( %s -> ( f x. 1 ) <_ ( f x. K ) )' % D)
mg2 = w.s([w.s([w.s([fcn], 'mulridd', '( %s -> ( f x. 1 ) = f )' % D)], 'eqcomd', '( %s -> f = ( f x. 1 ) )' % D), mg], 'eqbrtrd',
          '( %s -> f <_ ( f x. K ) )' % D)
flez = linarith(w, D, [le, mg2], 'f <_ Z', leaves={'f': fre, '( f x. K )': vre, 'Z': zrd})
fz2 = w.s([w.s([w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % D),
                w.s([w.s([zn0], 'nn0zd', '( %s -> Z e. ZZ )' % A)], 'adantr', '( %s -> Z e. ZZ )' % D),
                w.s([fnn], 'nnzd', '( %s -> f e. ZZ )' % D)], '3jca', '( %s -> ( 0 e. ZZ /\\ Z e. ZZ /\\ f e. ZZ ) )' % D),
           w.s([f0, flez], 'jca', '( %s -> ( 0 <_ f /\\ f <_ Z ) )' % D)], 'jca',
          '( %s -> ( ( 0 e. ZZ /\\ Z e. ZZ /\\ f e. ZZ ) /\\ ( 0 <_ f /\\ f <_ Z ) ) )' % D)
infz = w.s([fz2, w.inst('elfz2')], 'sylibr', '( %s -> f e. ( 0 ... Z ) )' % D)
dsub = w.s([w.s([infz], 'ex', '( %s -> ( f e. ( %s \\ %s ) -> f e. ( 0 ... Z ) ) )' % (A, R0, R))], 'ssrdv',
           '( %s -> ( %s \\ %s ) C_ ( 0 ... Z ) )' % (A, R0, R))
hd = w.s([r0fi, sub, w.inst('hashssdif')], 'syl2anc', '( %s -> ( # ` ( %s \\ %s ) ) = ( ( # ` %s ) - ( # ` %s ) ) )' % (A, R0, R, R0, R))
fzf = w.s([w.s([], 'fzfi', '( 0 ... Z ) e. Fin')], 'a1i', '( %s -> ( 0 ... Z ) e. Fin )' % A)
hs = w.s([fzf, dsub, w.inst('hashss')], 'syl2anc', '( %s -> ( # ` ( %s \\ %s ) ) <_ ( # ` ( 0 ... Z ) ) )' % (A, R0, R))
hf0 = w.s([zn0, w.inst('hashfz0')], 'syl', '( %s -> ( # ` ( 0 ... Z ) ) = ( Z + 1 ) )' % A)
hs2 = w.s([hs, hf0], 'breqtrd', '( %s -> ( # ` ( %s \\ %s ) ) <_ ( Z + 1 ) )' % (A, R0, R))
hs3 = w.s([w.s([hd], 'eqcomd', '( %s -> ( ( # ` %s ) - ( # ` %s ) ) = ( # ` ( %s \\ %s ) ) )' % (A, R0, R, R0, R)), hs2], 'eqbrtrd',
          '( %s -> ( ( # ` %s ) - ( # ` %s ) ) <_ ( Z + 1 ) )' % (A, R0, R))
h0r = w.s([w.s([r0fi, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A, R0))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (A, R0))
hrr = w.s([w.s([rfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A, R))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (A, R))
zre = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
linarith(w, A, [hs3], '( # ` %s ) <_ ( ( # ` %s ) + ( Z + 1 ) )' % (R0, R),
         leaves={'( # ` %s )' % R0: h0r, '( # ` %s )' % R: hrr, 'Z': zre}, name='qed')
run(w)
