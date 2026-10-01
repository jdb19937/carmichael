"""Sortie A3, batch 4: one extraction round (Lean: round_extractW): any finite
set of naturals coprime to L and larger than E ( 1 + log L ) contains a nonempty
subset whose product is 1 modulo L.  This is vebkz with the finite set turned
into a sequence by fz1f1o."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a3lib
from tm import *
from lin import linarith
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

M = '( # ` V )'
FZ = '( 1 ... %s )' % M
EXP = 'A. a e. ZZ ( ( a gcd L ) = 1 -> L || ( ( a ^ E ) - 1 ) )'
H1 = '( L e. NN /\\ E e. NN /\\ %s )' % EXP
H2 = '( V e. Fin /\\ V C_ NN /\\ A. p e. V ( p gcd L ) = 1 )'
H3 = '( E x. ( 1 + ( log ` L ) ) ) < %s' % M
H = '( %s /\\ %s /\\ %s )' % (H1, H2, H3)
S = '( f " t )'
CONCL = 'E. s e. ~P V ( s =/= (/) /\\ L || ( prod_ j e. s j - 1 ) )'

w = W('extrwrnd', 'One extraction round: a finite set V of naturals coprime to L with E ( 1 + log L ) < ( # ` V ) has a nonempty subset whose product is 1 modulo L (Lean: round_extractW; vebkz in set form).')
h1 = w.s([], 'simp1', '( %s -> %s )' % (H, H1))
h2 = w.s([], 'simp2', '( %s -> %s )' % (H, H2))
h3 = w.s([], 'simp3', '( %s -> %s )' % (H, H3))
lnn = w.s([h1], 'simp1d', '( %s -> L e. NN )' % H)
enn = w.s([h1], 'simp2d', '( %s -> E e. NN )' % H)
vfin = w.s([h2], 'simp1d', '( %s -> V e. Fin )' % H)
vss = w.s([h2], 'simp2d', '( %s -> V C_ NN )' % H)
vcop = w.s([h2], 'simp3d', '( %s -> A. p e. V ( p gcd L ) = 1 )' % H)
hcl = w.s([vfin, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (H, M))
hre = w.s([hcl], 'nn0red', '( %s -> %s e. RR )' % (H, M))
lre = w.s([lnn], 'nnred', '( %s -> L e. RR )' % H)
lge1 = w.s([lnn], 'nnge1d', '( %s -> 1 <_ L )' % H)
lg0 = w.s([lre, lge1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` L ) )' % H)
lgre = w.s([w.s([lnn], 'nnrpd', '( %s -> L e. RR+ )' % H)], 'relogcld', '( %s -> ( log ` L ) e. RR )' % H)
ere = w.s([enn], 'nnred', '( %s -> E e. RR )' % H)
e0 = w.s([enn], 'nngt0d', '( %s -> 0 < E )' % H)
onelg = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % H), lgre], 'readdcld', '( %s -> ( 1 + ( log ` L ) ) e. RR )' % H)
olg0 = linarith(w, H, [lg0], '0 < ( 1 + ( log ` L ) )', leaves={'( log ` L )': ('RR', lgre)})
prod0 = w.s([e0, olg0], 'mulgt0d', '( %s -> 0 < ( E x. ( 1 + ( log ` L ) ) ) )' % H)
mre = w.s([ere, onelg], 'remulcld', '( %s -> ( E x. ( 1 + ( log ` L ) ) ) e. RR )' % H)
h0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % H), mre, hre, prod0, h3], 'lttrd', '( %s -> 0 < %s )' % (H, M))
hne = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % H), h0], 'gtned', '( %s -> %s =/= 0 )' % (H, M))
vne = w.s([w.s([w.s([vfin, w.inst('hasheq0')], 'syl', '( %s -> ( %s = 0 <-> V = (/) ) )' % (H, M))], 'necon3bid', '( %s -> ( %s =/= 0 <-> V =/= (/) ) )' % (H, M)), hne], 'mpbid', '( %s -> V =/= (/) )' % H)
vn0 = w.s([vne], 'neneqd', '( %s -> -. V = (/) )' % H)
f1o = w.s([vfin, w.inst('fz1f1o')], 'syl', '( %s -> ( V = (/) \\/ ( %s e. NN /\\ E. f f : %s -1-1-onto-> V ) ) )' % (H, M, FZ))
orr = w.s([f1o, w.s([vn0, w.s([], 'orel1', '( -. V = (/) -> ( ( V = (/) \\/ ( %s e. NN /\\ E. f f : %s -1-1-onto-> V ) ) -> ( %s e. NN /\\ E. f f : %s -1-1-onto-> V ) ) )' % (M, FZ, M, FZ))], 'syl', '( %s -> ( ( V = (/) \\/ ( %s e. NN /\\ E. f f : %s -1-1-onto-> V ) ) -> ( %s e. NN /\\ E. f f : %s -1-1-onto-> V ) ) )' % (H, M, FZ, M, FZ))], 'mpd', '( %s -> ( %s e. NN /\\ E. f f : %s -1-1-onto-> V ) )' % (H, M, FZ))
exf = w.s([orr], 'simprd', '( %s -> E. f f : %s -1-1-onto-> V )' % (H, FZ))

# ---- under a bijection f : ( 1 ... ( # ` V ) ) -1-1-onto-> V
HF = '( %s /\\ f : %s -1-1-onto-> V )' % (H, FZ)
fb = w.s([], 'simpr', '( %s -> f : %s -1-1-onto-> V )' % (HF, FZ))
ff = w.s([fb, w.inst('f1of')], 'syl', '( %s -> f : %s --> V )' % (HF, FZ))
vssf = w.s([vss], 'adantr', '( %s -> V C_ NN )' % HF)
vz = w.s([vssf, w.s([w.s([], 'nnssz', 'NN C_ ZZ')], 'a1i', '( %s -> NN C_ ZZ )' % HF)], 'sstrd', '( %s -> V C_ ZZ )' % HF)
fz = w.s([ff, vz, w.inst('fss')], 'syl2anc', '( %s -> f : %s --> ZZ )' % (HF, FZ))
AK = '( %s /\\ k e. %s )' % (HF, FZ)
fkv = w.s([w.s([ff], 'adantr', '( %s -> f : %s --> V )' % (AK, FZ)), w.s([], 'simpr', '( %s -> k e. %s )' % (AK, FZ)), w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( f ` k ) e. V )' % AK)
cgk = w.s([w.s([w.s([], 'id', '( p = ( f ` k ) -> p = ( f ` k ) )')], 'oveq1d', '( p = ( f ` k ) -> ( p gcd L ) = ( ( f ` k ) gcd L ) )')], 'eqeq1d', '( p = ( f ` k ) -> ( ( p gcd L ) = 1 <-> ( ( f ` k ) gcd L ) = 1 ) )')
vcopk = w.s([w.s([vcop], 'adantr', '( %s -> A. p e. V ( p gcd L ) = 1 )' % HF)], 'adantr', '( %s -> A. p e. V ( p gcd L ) = 1 )' % AK)
copk = w.s([cgk, vcopk, fkv], 'rspcdva', '( %s -> ( ( f ` k ) gcd L ) = 1 )' % AK)
copall = w.s([copk], 'ralrimiva', '( %s -> A. k e. %s ( ( f ` k ) gcd L ) = 1 )' % (HF, FZ))
VEB = '( ( %s /\\ ( %s e. NN0 /\\ f : %s --> ZZ /\\ A. k e. %s ( ( f ` k ) gcd L ) = 1 ) /\\ ( E x. ( 1 + ( log ` L ) ) ) < %s ) -> E. t e. ~P %s ( t =/= (/) /\\ L || ( prod_ k e. t ( f ` k ) - 1 ) ) )' % (H1, M, FZ, FZ, M, FZ)
veb = w.s([w.s([w.s([h1], 'adantr', '( %s -> %s )' % (HF, H1)), w.s([w.s([hcl], 'adantr', '( %s -> %s e. NN0 )' % (HF, M)), fz, copall], '3jca', '( %s -> ( %s e. NN0 /\\ f : %s --> ZZ /\\ A. k e. %s ( ( f ` k ) gcd L ) = 1 ) )' % (HF, M, FZ, FZ)), w.s([h3], 'adantr', '( %s -> %s )' % (HF, H3))], '3jca', '( %s -> ( %s /\\ ( %s e. NN0 /\\ f : %s --> ZZ /\\ A. k e. %s ( ( f ` k ) gcd L ) = 1 ) /\\ ( E x. ( 1 + ( log ` L ) ) ) < %s ) )' % (HF, H1, M, FZ, FZ, M)), w.s([], 'vebkz', VEB)], 'syl', '( %s -> E. t e. ~P %s ( t =/= (/) /\\ L || ( prod_ k e. t ( f ` k ) - 1 ) ) )' % (HF, FZ))
# ---- under a witness t
HT0 = '( %s /\\ t e. ~P %s )' % (HF, FZ)
HT = '( %s /\\ ( t =/= (/) /\\ L || ( prod_ k e. t ( f ` k ) - 1 ) ) )' % HT0
tss = w.s([w.s([], 'simpr', '( %s -> t e. ~P %s )' % (HT0, FZ)), w.s([], 'elpwi', '( t e. ~P %s -> t C_ %s )' % (FZ, FZ))], 'syl', '( %s -> t C_ %s )' % (HT0, FZ))
# the image is nonempty (derived without the k-binding conjunct in the antecedent)
HT1 = '( %s /\\ t =/= (/) )' % HT0
ext = w.s([w.s([], 'simpr', '( %s -> t =/= (/) )' % HT1), w.s([], 'n0', '( t =/= (/) <-> E. k k e. t )')], 'sylib', '( %s -> E. k k e. t )' % HT1)
HK = '( %s /\\ k e. t )' % HT1
tss1 = w.s([tss], 'adantr', '( %s -> t C_ %s )' % (HT1, FZ))
kfz = w.s([w.s([tss1], 'adantr', '( %s -> t C_ %s )' % (HK, FZ)), w.s([], 'simpr', '( %s -> k e. t )' % HK)], 'sseldd', '( %s -> k e. %s )' % (HK, FZ))
fb1 = w.s([w.s([fb], 'adantr', '( %s -> f : %s -1-1-onto-> V )' % (HT0, FZ))], 'adantr', '( %s -> f : %s -1-1-onto-> V )' % (HT1, FZ))
ffn = w.s([w.s([fb1], 'adantr', '( %s -> f : %s -1-1-onto-> V )' % (HK, FZ)), w.inst('f1ofn')], 'syl', '( %s -> f Fn %s )' % (HK, FZ))
fkim = w.s([ffn, w.s([tss1], 'adantr', '( %s -> t C_ %s )' % (HK, FZ)), w.s([], 'simpr', '( %s -> k e. t )' % HK), w.inst('fnfvima')], 'syl3anc', '( %s -> ( f ` k ) e. %s )' % (HK, S))
sne0 = w.s([fkim, w.s([], 'ne0i', '( ( f ` k ) e. %s -> %s =/= (/) )' % (S, S))], 'syl', '( %s -> %s =/= (/) )' % (HK, S))
sne1 = w.s([w.s([w.s([sne0], 'ex', '( %s -> ( k e. t -> %s =/= (/) ) )' % (HT1, S))], 'exlimdv', '( %s -> ( E. k k e. t -> %s =/= (/) ) )' % (HT1, S)), ext], 'mpd', '( %s -> %s =/= (/) )' % (HT1, S))
sneim = w.s([sne1], 'ex', '( %s -> ( t =/= (/) -> %s =/= (/) ) )' % (HT0, S))
tne = w.s([], 'simprl', '( %s -> t =/= (/) )' % HT)
sne = w.s([w.s([sneim], 'adantr', '( %s -> ( t =/= (/) -> %s =/= (/) ) )' % (HT, S)), tne], 'mpd', '( %s -> %s =/= (/) )' % (HT, S))
# the two products agree (again without the k-binding conjunct)
AJ = '( %s /\\ j e. %s )' % (HT0, S)
tss0 = tss
tfin0 = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (HT0, FZ)), tss0, w.inst('ssfi')], 'syl2anc', '( %s -> t e. Fin )' % HT0)
fb0 = w.s([fb], 'adantr', '( %s -> f : %s -1-1-onto-> V )' % (HT0, FZ))
f110 = w.s([fb0, w.inst('f1of1')], 'syl', '( %s -> f : %s -1-1-> V )' % (HT0, FZ))
fres0 = w.s([f110, tss0, w.inst('f1ores')], 'syl2anc', '( %s -> ( f |` t ) : t -1-1-onto-> %s )' % (HT0, S))
ff0 = w.s([ff], 'adantr', '( %s -> f : %s --> V )' % (HT0, FZ))
sss0 = w.s([w.s([w.s([], 'imassrn', '%s C_ ran f' % S)], 'a1i', '( %s -> %s C_ ran f )' % (HT0, S)), w.s([ff0, w.inst('frn')], 'syl', '( %s -> ran f C_ V )' % HT0)], 'sstrd', '( %s -> %s C_ V )' % (HT0, S))
vss0 = w.s([w.s([vss], 'adantr', '( %s -> V C_ NN )' % HF)], 'adantr', '( %s -> V C_ NN )' % HT0)
jv = w.s([w.s([sss0], 'adantr', '( %s -> %s C_ V )' % (AJ, S)), w.s([], 'simpr', '( %s -> j e. %s )' % (AJ, S))], 'sseldd', '( %s -> j e. V )' % AJ)
jnn = w.s([w.s([vss0], 'adantr', '( %s -> V C_ NN )' % AJ), jv], 'sseldd', '( %s -> j e. NN )' % AJ)
jcc = w.s([jnn], 'nncnd', '( %s -> j e. CC )' % AJ)
AKT = '( %s /\\ k e. t )' % HT0
resfv = w.s([w.s([], 'simpr', '( %s -> k e. t )' % AKT), w.s([], 'fvres', '( k e. t -> ( ( f |` t ) ` k ) = ( f ` k ) )')], 'syl', '( %s -> ( ( f |` t ) ` k ) = ( f ` k ) )' % AKT)
peq0 = w.s([w.s([], 'id', '( j = ( f ` k ) -> j = ( f ` k ) )'), tfin0, fres0, resfv, jcc], 'fprodf1o', '( %s -> prod_ j e. %s j = prod_ k e. t ( f ` k ) )' % (HT0, S))
peq = w.s([peq0], 'adantr', '( %s -> prod_ j e. %s j = prod_ k e. t ( f ` k ) )' % (HT, S))
sss = w.s([sss0], 'adantr', '( %s -> %s C_ V )' % (HT, S))
sex = w.s([w.s([w.s([], 'vex', 'f e. _V')], 'a1i', '( %s -> f e. _V )' % HT), w.inst('imaexg')], 'syl', '( %s -> %s e. _V )' % (HT, S))
spw = w.s([w.s([sex, w.inst('elpwg')], 'syl', '( %s -> ( %s e. ~P V <-> %s C_ V ) )' % (HT, S, S)), sss], 'mpbird', '( %s -> %s e. ~P V )' % (HT, S))
dvt = w.s([], 'simprr', '( %s -> L || ( prod_ k e. t ( f ` k ) - 1 ) )' % HT)
dvs = w.s([dvt, w.s([peq], 'oveq1d', '( %s -> ( prod_ j e. %s j - 1 ) = ( prod_ k e. t ( f ` k ) - 1 ) )' % (HT, S))], 'breqtrrd', '( %s -> L || ( prod_ j e. %s j - 1 ) )' % (HT, S))
conj = w.s([sne, dvs], 'jca', '( %s -> ( %s =/= (/) /\\ L || ( prod_ j e. %s j - 1 ) ) )' % (HT, S, S))
# the existential over subsets of V
SB = '( %s /\\ s = %s )' % (HT, S)
idst = w.s([], 'simpr', '( %s -> s = %s )' % (SB, S))
cgs, newf = w.wcongr('( s =/= (/) /\\ L || ( prod_ j e. s j - 1 ) )', {'s': S}, SB, {'s': idst})
assert newf == '( %s =/= (/) /\\ L || ( prod_ j e. %s j - 1 ) )' % (S, S), newf
exs = w.s([spw, cgs, conj], 'rspcedvd', '( %s -> %s )' % (HT, CONCL))
limt = w.s([w.s([exs], 'ex', '( %s -> ( ( t =/= (/) /\\ L || ( prod_ k e. t ( f ` k ) - 1 ) ) -> %s ) )' % (HT0, CONCL))], 'rexlimdva', '( %s -> ( E. t e. ~P %s ( t =/= (/) /\\ L || ( prod_ k e. t ( f ` k ) - 1 ) ) -> %s ) )' % (HF, FZ, CONCL))
resf = w.s([limt, veb], 'mpd', '( %s -> %s )' % (HF, CONCL))
limf = w.s([w.s([resf], 'ex', '( %s -> ( f : %s -1-1-onto-> V -> %s ) )' % (H, FZ, CONCL))], 'exlimdv', '( %s -> ( E. f f : %s -1-1-onto-> V -> %s ) )' % (H, FZ, CONCL))
w.qed([limf, exf], 'mpd', '( %s -> %s )' % (H, CONCL))
run(w)
