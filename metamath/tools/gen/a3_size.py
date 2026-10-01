"""Sortie A3, batch 5: the size bounds of ExtractionW (Nstar, log L, the round
count; Lean: Nstar_leW, lt_NstarW, log_Lmod_geW, log_Lmod_leW, natLog_le_divW)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a3lib
from a3lib import fpp, lmodprod, FPP, FP0
from tm import *
from lin import linarith
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

LM = '( Lmod ` Q )'
LA = '( lambdaL ` Q )'
NS = '( Nstar ` Q )'
XX = '( %s x. ( 1 + ( log ` %s ) ) )' % (LA, LM)


def nstarctx(w, H, q1):
    """closures and the value of Nstar for Q e. FPP"""
    ss, fin, f0 = fpp(w, H, q1)
    lnn = w.s([q1, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (H, LM))
    lann = w.s([q1, w.inst('lambdalcl')], 'syl', '( %s -> %s e. NN )' % (H, LA))
    lgre = w.s([w.s([lnn], 'nnrpd', '( %s -> %s e. RR+ )' % (H, LM))], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (H, LM))
    lg0 = w.s([w.s([lnn], 'nnred', '( %s -> %s e. RR )' % (H, LM)), w.s([lnn], 'nnge1d', '( %s -> 1 <_ %s )' % (H, LM)), w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` %s ) )' % (H, LM))
    onelg = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % H), lgre], 'readdcld', '( %s -> ( 1 + ( log ` %s ) ) e. RR )' % (H, LM))
    xre = w.s([w.s([lann], 'nnred', '( %s -> %s e. RR )' % (H, LA)), onelg], 'remulcld', '( %s -> %s e. RR )' % (H, XX))
    olg0 = linarith(w, H, [lg0], '0 < ( 1 + ( log ` %s ) )' % LM, leaves={'( log ` %s )' % LM: ('RR', lgre)})
    x0 = w.s([w.s([lann], 'nngt0d', '( %s -> 0 < %s )' % (H, LA)), olg0], 'mulgt0d', '( %s -> 0 < %s )' % (H, XX))
    xge0 = linarith(w, H, [x0], '0 <_ %s' % XX, leaves={XX: ('RR', xre)})
    nv = w.s([f0, w.inst('nstarval')], 'syl', '( %s -> %s = ( ( Nceil ` %s ) + 1 ) )' % (H, NS, XX))
    ncl = w.s([xre, w.inst('nceilcl')], 'syl', '( %s -> ( Nceil ` %s ) e. NN0 )' % (H, XX))
    nre = w.s([ncl], 'nn0red', '( %s -> ( Nceil ` %s ) e. RR )' % (H, XX))
    return xre, xge0, nv, nre

# ------------------------------------------------------------ extrwnsle
w = W('extrwnsle', 'Nstar Q <_ lambdaL Q ( 1 + log L ) + 2 (Lean: Nstar_leW).')
H = 'Q e. %s' % FPP
q1 = w.s([], 'id', '( %s -> %s )' % (H, H))
xre, xge0, nv, nre = nstarctx(w, H, q1)
lt = w.s([xre, xge0, w.inst('nceillt')], 'syl2anc', '( %s -> ( Nceil ` %s ) < ( %s + 1 ) )' % (H, XX, XX))
le = linarith(w, H, [lt], '( ( Nceil ` %s ) + 1 ) <_ ( %s + 2 )' % (XX, XX), leaves={XX: ('RR', xre), '( Nceil ` %s )' % XX: ('RR', nre)})
w.qed([nv, le], 'eqbrtrd', '( %s -> %s <_ ( %s + 2 ) )' % (H, NS, XX))
run(w)

# ------------------------------------------------------------ extrwltns
w = W('extrwltns', 'lambdaL Q ( 1 + log L ) < Nstar Q (Lean: lt_NstarW).')
H = 'Q e. %s' % FPP
q1 = w.s([], 'id', '( %s -> %s )' % (H, H))
xre, xge0, nv, nre = nstarctx(w, H, q1)
ge = w.s([xre, w.inst('nceilge')], 'syl', '( %s -> %s <_ ( Nceil ` %s ) )' % (H, XX, XX))
lt = linarith(w, H, [ge], '%s < ( ( Nceil ` %s ) + 1 )' % (XX, XX), leaves={XX: ('RR', xre), '( Nceil ` %s )' % XX: ('RR', nre)})
w.qed([lt, nv], 'breqtrrd', '( %s -> %s < %s )' % (H, XX, NS))
run(w)

# ------------------------------------------------------------ extrwnlogdiv
w = W('extrwnlogdiv', 'The round count: ( ( M + 1 ) Nlog N ) <_ ( log N / G ) whenever 0 < G <_ log ( M + 1 ) (Lean: natLog_le_divW).')
H = '( M e. NN /\\ N e. NN /\\ ( G e. RR /\\ 0 < G /\\ G <_ ( log ` ( M + 1 ) ) ) )'
B = '( M + 1 )'
KL = '( %s Nlog N )' % B
mnn = w.s([], 'simp1', '( %s -> M e. NN )' % H)
nnn = w.s([], 'simp2', '( %s -> N e. NN )' % H)
g3 = w.s([], 'simp3', '( %s -> ( G e. RR /\\ 0 < G /\\ G <_ ( log ` %s ) ) )' % (H, B))
gre = w.s([g3], 'simp1d', '( %s -> G e. RR )' % H)
g0 = w.s([g3], 'simp2d', '( %s -> 0 < G )' % H)
gle = w.s([g3], 'simp3d', '( %s -> G <_ ( log ` %s ) )' % (H, B))
bnn = w.s([mnn, w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % H)], 'nnaddcld', '( %s -> %s e. NN )' % (H, B))
m1 = w.s([mnn], 'nnge1d', '( %s -> 1 <_ M )' % H)
b2 = linarith(w, H, [m1], '2 <_ %s' % B, leaves={'M': ('NN', mnn)})
i2z = w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % H)
bz = w.s([bnn], 'nnzd', '( %s -> %s e. ZZ )' % (H, B))
buz = w.s([w.s([i2z, bz, b2], '3jca', '( %s -> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (H, B, B)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` 2 ) )' % (H, B))
kcl = w.s([w.s([bnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (H, B)), w.s([nnn], 'nnnn0d', '( %s -> N e. NN0 )' % H), w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (H, KL))
kre = w.s([kcl], 'nn0red', '( %s -> %s e. RR )' % (H, KL))
kge0 = w.s([kcl], 'nn0ge0d', '( %s -> 0 <_ %s )' % (H, KL))
ple = w.s([buz, nnn, w.inst('nlogle')], 'syl2anc', '( %s -> ( %s ^ %s ) <_ N )' % (H, B, KL))
brp = w.s([bnn], 'nnrpd', '( %s -> %s e. RR+ )' % (H, B))
nrp = w.s([nnn], 'nnrpd', '( %s -> N e. RR+ )' % H)
bkrp = w.s([brp, w.s([kcl], 'nn0zd', '( %s -> %s e. ZZ )' % (H, KL)), w.inst('rpexpcl')], 'syl2anc', '( %s -> ( %s ^ %s ) e. RR+ )' % (H, B, KL))
lgle = w.s([w.s([bkrp, nrp, w.inst('logleb')], 'syl2anc', '( %s -> ( ( %s ^ %s ) <_ N <-> ( log ` ( %s ^ %s ) ) <_ ( log ` N ) ) )' % (H, B, KL, B, KL)), ple], 'mpbid', '( %s -> ( log ` ( %s ^ %s ) ) <_ ( log ` N ) )' % (H, B, KL))
lgex = w.s([brp, w.s([kcl], 'nn0zd', '( %s -> %s e. ZZ )' % (H, KL)), w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( %s ^ %s ) ) = ( %s x. ( log ` %s ) ) )' % (H, B, KL, KL, B))
klog = w.s([lgex, lgle], 'eqbrtrrd', '( %s -> ( %s x. ( log ` %s ) ) <_ ( log ` N ) )' % (H, KL, B))
lgbre = w.s([brp], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (H, B))
lgnre = w.s([nrp], 'relogcld', '( %s -> ( log ` N ) e. RR )' % H)
kg = w.s([kre, gre, lgbre, kge0, gle], 'lemul2ad', '( %s -> ( %s x. G ) <_ ( %s x. ( log ` %s ) ) )' % (H, KL, KL, B))
chain = w.s([w.s([kre, gre], 'remulcld', '( %s -> ( %s x. G ) e. RR )' % (H, KL)), w.s([kre, lgbre], 'remulcld', '( %s -> ( %s x. ( log ` %s ) ) e. RR )' % (H, KL, B)), lgnre, kg, klog], 'letrd', '( %s -> ( %s x. G ) <_ ( log ` N ) )' % (H, KL))
bi = w.s([kre, lgnre, w.s([gre, g0], 'jca', '( %s -> ( G e. RR /\\ 0 < G ) )' % H), w.inst('lemuldiv')], 'syl3anc', '( %s -> ( ( %s x. G ) <_ ( log ` N ) <-> %s <_ ( ( log ` N ) / G ) ) )' % (H, KL, KL))
w.qed([bi, chain], 'mpbid', '( %s -> %s <_ ( ( log ` N ) / G ) )' % (H, KL))
run(w)

# ------------------------------------------------------------ extrwloglle
w = W('extrwloglle', 'Upper bound on log L: the primes of Q are all at most z (Lean: log_Lmod_leW).')
H = '( Z e. NN /\\ Q e. %s /\\ A. q e. Q q <_ Z )' % FPP
znn = w.s([], 'simp1', '( %s -> Z e. NN )' % H)
q1 = w.s([], 'simp2', '( %s -> Q e. %s )' % (H, FPP))
qle = w.s([], 'simp3', '( %s -> A. q e. Q q <_ Z )' % H)
ss, fin, f0 = fpp(w, H, q1)
lmp = lmodprod(w, H, f0)
lnn = w.s([q1, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (H, LM))
AJ = '( %s /\\ j e. Q )' % H
jnn = w.s([w.s([w.s([ss], 'adantr', '( %s -> Q C_ Prime )' % AJ), w.s([], 'simpr', '( %s -> j e. Q )' % AJ)], 'sseldd', '( %s -> j e. Prime )' % AJ), w.inst('prmnn')], 'syl', '( %s -> j e. NN )' % AJ)
jre = w.s([jnn], 'nnred', '( %s -> j e. RR )' % AJ)
jge0 = w.s([jnn], 'nnge0d' if False else 'nngt0d', '( %s -> 0 < j )' % AJ)
jge = linarith(w, AJ, [jge0], '0 <_ j', leaves={'j': ('RR', jre)})
zreJ = w.s([w.s([znn], 'adantr', '( %s -> Z e. NN )' % AJ)], 'nnred', '( %s -> Z e. RR )' % AJ)
cgj = w.s([w.s([], 'id', '( q = j -> q = j )')], 'breq1d', '( q = j -> ( q <_ Z <-> j <_ Z ) )')
jz = w.s([cgj, w.s([qle], 'adantr', '( %s -> A. q e. Q q <_ Z )' % AJ), w.s([], 'simpr', '( %s -> j e. Q )' % AJ)], 'rspcdva', '( %s -> j <_ Z )' % AJ)
ple = w.s([w.s([], 'nfv', 'F/ j %s' % H), fin, jre, jge, zreJ, jz], 'fprodle', '( %s -> prod_ j e. Q j <_ prod_ j e. Q Z )' % H)
zcn = w.s([znn], 'nncnd', '( %s -> Z e. CC )' % H)
pc = w.s([fin, zcn, w.inst('fprodconst')], 'syl2anc', '( %s -> prod_ j e. Q Z = ( Z ^ ( # ` Q ) ) )' % H)
le1 = w.s([ple, pc], 'breqtrd', '( %s -> prod_ j e. Q j <_ ( Z ^ ( # ` Q ) ) )' % H)
le2 = w.s([lmp, le1], 'eqbrtrd', '( %s -> %s <_ ( Z ^ ( # ` Q ) ) )' % (H, LM))
zrp = w.s([znn], 'nnrpd', '( %s -> Z e. RR+ )' % H)
hz = w.s([w.s([fin, w.inst('hashcl')], 'syl', '( %s -> ( # ` Q ) e. NN0 )' % H)], 'nn0zd', '( %s -> ( # ` Q ) e. ZZ )' % H)
zprp = w.s([zrp, hz, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( Z ^ ( # ` Q ) ) e. RR+ )' % H)
lgm = w.s([w.s([w.s([lnn], 'nnrpd', '( %s -> %s e. RR+ )' % (H, LM)), zprp, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ ( Z ^ ( # ` Q ) ) <-> ( log ` %s ) <_ ( log ` ( Z ^ ( # ` Q ) ) ) ) )' % (H, LM, LM)), le2], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` ( Z ^ ( # ` Q ) ) ) )' % (H, LM))
lex = w.s([zrp, hz, w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( Z ^ ( # ` Q ) ) ) = ( ( # ` Q ) x. ( log ` Z ) ) )' % H)
w.qed([lgm, lex], 'breqtrd', '( %s -> ( log ` %s ) <_ ( ( # ` Q ) x. ( log ` Z ) ) )' % (H, LM))
run(w)

# ------------------------------------------------------------ extrwloglge
w = W('extrwloglge', 'Lower bound on log L: the primes of Q all exceed the square root of z (Lean: log_Lmod_geW).')
H = '( Z e. NN /\\ Q e. %s /\\ A. q e. Q ( sqrt ` Z ) < q )' % FPP
SQ = '( sqrt ` Z )'
znn = w.s([], 'simp1', '( %s -> Z e. NN )' % H)
q1 = w.s([], 'simp2', '( %s -> Q e. %s )' % (H, FPP))
qgt = w.s([], 'simp3', '( %s -> A. q e. Q %s < q )' % (H, SQ))
ss, fin, f0 = fpp(w, H, q1)
lmp = lmodprod(w, H, f0)
lnn = w.s([q1, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (H, LM))
zre = w.s([znn], 'nnred', '( %s -> Z e. RR )' % H)
z0 = w.s([znn], 'nngt0d', '( %s -> 0 < Z )' % H)
sqre = w.s([zre, linarith(w, H, [z0], '0 <_ Z', leaves={'Z': ('RR', zre)}), w.inst('resqrtcl')], 'syl2anc', '( %s -> %s e. RR )' % (H, SQ))
sq0 = w.s([zre, z0, w.inst('sqrtgt0')], 'syl2anc', '( %s -> 0 < %s )' % (H, SQ))
sqrp = w.s([sqre, sq0], 'elrpd', '( %s -> %s e. RR+ )' % (H, SQ))
AJ = '( %s /\\ j e. Q )' % H
jnn = w.s([w.s([w.s([ss], 'adantr', '( %s -> Q C_ Prime )' % AJ), w.s([], 'simpr', '( %s -> j e. Q )' % AJ)], 'sseldd', '( %s -> j e. Prime )' % AJ), w.inst('prmnn')], 'syl', '( %s -> j e. NN )' % AJ)
jre = w.s([jnn], 'nnred', '( %s -> j e. RR )' % AJ)
sqreJ = w.s([sqre], 'adantr', '( %s -> %s e. RR )' % (AJ, SQ))
sqge0 = w.s([sq0], 'adantr', '( %s -> 0 < %s )' % (AJ, SQ))
sqge = linarith(w, AJ, [sqge0], '0 <_ %s' % SQ, leaves={SQ: ('RR', sqreJ)})
cgj = w.s([w.s([], 'id', '( q = j -> q = j )')], 'breq2d', '( q = j -> ( %s < q <-> %s < j ) )' % (SQ, SQ))
jgt = w.s([cgj, w.s([qgt], 'adantr', '( %s -> A. q e. Q %s < q )' % (AJ, SQ)), w.s([], 'simpr', '( %s -> j e. Q )' % AJ)], 'rspcdva', '( %s -> %s < j )' % (AJ, SQ))
jle = w.s([jgt], 'ltled', '( %s -> %s <_ j )' % (AJ, SQ))
ple = w.s([w.s([], 'nfv', 'F/ j %s' % H), fin, sqreJ, sqge, jre, jle], 'fprodle', '( %s -> prod_ j e. Q %s <_ prod_ j e. Q j )' % (H, SQ))
pc = w.s([fin, w.s([sqre], 'recnd', '( %s -> %s e. CC )' % (H, SQ)), w.inst('fprodconst')], 'syl2anc', '( %s -> prod_ j e. Q %s = ( %s ^ ( # ` Q ) ) )' % (H, SQ, SQ))
le1 = w.s([pc, ple], 'eqbrtrrd', '( %s -> ( %s ^ ( # ` Q ) ) <_ prod_ j e. Q j )' % (H, SQ))
le2 = w.s([le1, lmp], 'breqtrrd', '( %s -> ( %s ^ ( # ` Q ) ) <_ %s )' % (H, SQ, LM))
hz = w.s([w.s([fin, w.inst('hashcl')], 'syl', '( %s -> ( # ` Q ) e. NN0 )' % H)], 'nn0zd', '( %s -> ( # ` Q ) e. ZZ )' % H)
sqprp = w.s([sqrp, hz, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( %s ^ ( # ` Q ) ) e. RR+ )' % (H, SQ))
lgm = w.s([w.s([sqprp, w.s([lnn], 'nnrpd', '( %s -> %s e. RR+ )' % (H, LM)), w.inst('logleb')], 'syl2anc', '( %s -> ( ( %s ^ ( # ` Q ) ) <_ %s <-> ( log ` ( %s ^ ( # ` Q ) ) ) <_ ( log ` %s ) ) )' % (H, SQ, LM, SQ, LM)), le2], 'mpbid', '( %s -> ( log ` ( %s ^ ( # ` Q ) ) ) <_ ( log ` %s ) )' % (H, SQ, LM))
lex = w.s([sqrp, hz, w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( %s ^ ( # ` Q ) ) ) = ( ( # ` Q ) x. ( log ` %s ) ) )' % (H, SQ, SQ))
lsq = w.s([w.s([w.s([znn], 'nnrpd', '( %s -> Z e. RR+ )' % H), w.inst('logsqrt')], 'syl', '( %s -> ( log ` %s ) = ( ( log ` Z ) / 2 ) )' % (H, SQ))], 'oveq2d', '( %s -> ( ( # ` Q ) x. ( log ` %s ) ) = ( ( # ` Q ) x. ( ( log ` Z ) / 2 ) ) )' % (H, SQ))
eq = w.s([lex, lsq], 'eqtrd', '( %s -> ( log ` ( %s ^ ( # ` Q ) ) ) = ( ( # ` Q ) x. ( ( log ` Z ) / 2 ) ) )' % (H, SQ))
w.qed([eq, lgm], 'eqbrtrrd', '( %s -> ( ( # ` Q ) x. ( ( log ` Z ) / 2 ) ) <_ ( log ` %s ) )' % (H, LM))
run(w)
