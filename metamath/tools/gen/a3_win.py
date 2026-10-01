"""Sortie A3, batch 9: the window bridge lemmas (the hQfacts and hlogL_ge
blocks of extraction_inputsW): reservoir elements exceed the square root of z,
hence 1.5 T log z is below log L."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a3lib
from a3lib import fpp, lmodprod, FPP, FP0
from tm import *
from lin import linarith
import num
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

LM = '( Lmod ` Q )'
GW = '( ( Z goodPrimesW W ) ` Y )'
E99 = '( ; 9 9 / ; ; 1 0 0 )'


def lift(w, step, tail, antes):
    cur = step
    for a in antes:
        cur = w.s([cur], 'adantr', '( %s -> %s )' % (a, tail))
    return cur


# ------------------------------------------------------------ extrwsqrt
w = W('extrwsqrt', 'A reservoir prime exceeds the square root of z: the window floor z ^c ( 99 / 100 ) is at most w + 1 (Lean: the hQfacts block of extraction_inputsW).')
H = '( ( Z e. NN /\\ 1 < Z /\\ W e. NN0 ) /\\ ( ( Z ^c %s ) <_ ( W + 1 ) /\\ P e. NN /\\ W < P ) )' % E99
znn = w.s([], 'simpl1', '( %s -> Z e. NN )' % H)
z1 = w.s([], 'simpl2', '( %s -> 1 < Z )' % H)
wn0 = w.s([], 'simpl3', '( %s -> W e. NN0 )' % H)
zle = w.s([], 'simpr1', '( %s -> ( Z ^c %s ) <_ ( W + 1 ) )' % (H, E99))
pnn = w.s([], 'simpr2', '( %s -> P e. NN )' % H)
wlt = w.s([], 'simpr3', '( %s -> W < P )' % H)
zre = w.s([znn], 'nnred', '( %s -> Z e. RR )' % H)
zcn = w.s([znn], 'nncnd', '( %s -> Z e. CC )' % H)
sq = w.s([zcn, w.inst('cxpsqrt')], 'syl', '( %s -> ( Z ^c ( 1 / 2 ) ) = ( sqrt ` Z ) )' % H)
half = w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % H)
e99 = num.real(w, E99)
e99d = w.s([e99], 'a1i', '( %s -> %s e. RR )' % (H, E99))
ltex = linarith(w, H, [], '( 1 / 2 ) < %s' % E99, leaves={})
cl = w.s([w.s([w.s([zre, z1], 'jca', '( %s -> ( Z e. RR /\\ 1 < Z ) )' % H), w.s([half, e99d], 'jca', '( %s -> ( ( 1 / 2 ) e. RR /\\ %s e. RR ) )' % (H, E99))], 'jca', '( %s -> ( ( Z e. RR /\\ 1 < Z ) /\\ ( ( 1 / 2 ) e. RR /\\ %s e. RR ) ) )' % (H, E99)), w.inst('cxplt')], 'syl', '( %s -> ( ( 1 / 2 ) < %s <-> ( Z ^c ( 1 / 2 ) ) < ( Z ^c %s ) ) )' % (H, E99, E99))
lt1 = w.s([cl, ltex], 'mpbid', '( %s -> ( Z ^c ( 1 / 2 ) ) < ( Z ^c %s ) )' % (H, E99))
lt2 = w.s([sq, lt1], 'eqbrtrrd', '( %s -> ( sqrt ` Z ) < ( Z ^c %s ) )' % (H, E99))
wz = w.s([wn0], 'nn0zd', '( %s -> W e. ZZ )' % H)
pz = w.s([pnn], 'nnzd', '( %s -> P e. ZZ )' % H)
wbi = w.s([wz, pz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( W < P <-> ( W + 1 ) <_ P ) )' % H)
w1le = w.s([wbi, wlt], 'mpbid', '( %s -> ( W + 1 ) <_ P )' % H)
zrp = w.s([znn], 'nnrpd', '( %s -> Z e. RR+ )' % H)
zere = w.s([w.s([zrp, e99d, w.inst('rpcxpcl')], 'syl2anc', '( %s -> ( Z ^c %s ) e. RR+ )' % (H, E99))], 'rpred', '( %s -> ( Z ^c %s ) e. RR )' % (H, E99))
sqre = w.s([zre, linarith(w, H, [z1], '0 <_ Z', leaves={'Z': ('RR', zre)}), w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` Z ) e. RR )' % H)
w1re = w.s([w.s([wn0], 'nn0red', '( %s -> W e. RR )' % H), w.s([], '1red', '( %s -> 1 e. RR )' % H)], 'readdcld', '( %s -> ( W + 1 ) e. RR )' % H)
pre = w.s([pnn], 'nnred', '( %s -> P e. RR )' % H)
c1 = w.s([sqre, zere, w1re, lt2, zle], 'ltletrd', '( %s -> ( sqrt ` Z ) < ( W + 1 ) )' % H)
w.qed([sqre, w1re, pre, c1, w1le], 'ltletrd', '( %s -> ( sqrt ` Z ) < P )' % H)
run(w)

# ------------------------------------------------------------ extrwloglgw
w = W('extrwloglgw', 'The lower bound on log L at windowed scales: every reservoir prime exceeds the square root of z, so ( # ` Q ) ( log z / 2 ) <_ log L (Lean: the hlogL_ge block of extraction_inputsW).')
H = '( ( ( Z e. NN /\\ 1 < Z ) /\\ ( W e. NN0 /\\ Y e. NN0 ) ) /\\ ( ( Z ^c %s ) <_ ( W + 1 ) /\\ Q e. ~P %s ) )' % (E99, GW)
zw = w.s([], 'simpll', '( %s -> ( Z e. NN /\\ 1 < Z ) )' % H)
wy = w.s([], 'simplr', '( %s -> ( W e. NN0 /\\ Y e. NN0 ) )' % H)
znn = w.s([zw], 'simpld', '( %s -> Z e. NN )' % H)
z1 = w.s([zw], 'simprd', '( %s -> 1 < Z )' % H)
wn0 = w.s([wy], 'simpld', '( %s -> W e. NN0 )' % H)
yn0 = w.s([wy], 'simprd', '( %s -> Y e. NN0 )' % H)
zle = w.s([], 'simprl', '( %s -> ( Z ^c %s ) <_ ( W + 1 ) )' % (H, E99))
qpw = w.s([], 'simprr', '( %s -> Q e. ~P %s )' % (H, GW))
zn0 = w.s([znn], 'nnnn0d', '( %s -> Z e. NN0 )' % H)
gwfi = w.s([zn0, wn0, yn0, w.inst('goodprimeswfi')], 'syl3anc', '( %s -> %s e. %s )' % (H, GW, FPP))
gwb = w.s([gwfi, w.inst('elfpw')], 'sylib', '( %s -> ( %s C_ Prime /\\ %s e. Fin ) )' % (H, GW, GW))
qss = w.s([qpw, w.s([], 'elpwi', '( Q e. ~P %s -> Q C_ %s )' % (GW, GW))], 'syl', '( %s -> Q C_ %s )' % (H, GW))
qprm = w.s([qss, w.s([gwb], 'simpld', '( %s -> %s C_ Prime )' % (H, GW))], 'sstrd', '( %s -> Q C_ Prime )' % H)
qfin = w.s([w.s([gwb], 'simprd', '( %s -> %s e. Fin )' % (H, GW)), qss, w.inst('ssfi')], 'syl2anc', '( %s -> Q e. Fin )' % H)
qfpp = w.s([w.s([qprm, qfin], 'jca', '( %s -> ( Q C_ Prime /\\ Q e. Fin ) )' % H), w.inst('elfpw')], 'sylibr', '( %s -> Q e. %s )' % (H, FPP))
HQ = '( %s /\\ q e. Q )' % H
qel = w.s([], 'simpr', '( %s -> q e. Q )' % HQ)
qgw = w.s([w.s([qss], 'adantr', '( %s -> Q C_ %s )' % (HQ, GW)), qel], 'sseldd', '( %s -> q e. %s )' % (HQ, GW))
cgd, newf = w.wcongr('( Q e. ( 0 ... Z ) /\\ ( Q e. Prime /\\ W < Q /\\ A. p e. Prime ( p || ( Q - 1 ) -> p <_ Y ) ) )', {'Q': 'q'}, 'Q = q', {'Q': w.s([], 'id', '( Q = q -> Q = q )')})
elgh = w.s([lift(w, zn0, 'Z e. NN0', [HQ]), lift(w, wn0, 'W e. NN0', [HQ]), lift(w, yn0, 'Y e. NN0', [HQ])], '3jca', '( %s -> ( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 ) )' % HQ)
elg = w.s([w.s([elgh, w.inst('elgoodprimesw')], 'syl', '( %s -> ( q e. %s <-> %s ) )' % (HQ, GW, newf)), qgw], 'mpbid', '( %s -> %s )' % (HQ, newf))
qtrip = w.s([elg], 'simprd', '( %s -> ( q e. Prime /\\ W < q /\\ A. p e. Prime ( p || ( q - 1 ) -> p <_ Y ) ) )' % HQ)
qp = w.s([qtrip], 'simp1d', '( %s -> q e. Prime )' % HQ)
qw = w.s([qtrip], 'simp2d', '( %s -> W < q )' % HQ)
qnn = w.s([qp, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % HQ)
sq1 = w.s([lift(w, znn, 'Z e. NN', [HQ]), lift(w, z1, '1 < Z', [HQ]), lift(w, wn0, 'W e. NN0', [HQ])], '3jca', '( %s -> ( Z e. NN /\\ 1 < Z /\\ W e. NN0 ) )' % HQ)
sq2 = w.s([lift(w, zle, '( Z ^c %s ) <_ ( W + 1 )' % E99, [HQ]), qnn, qw], '3jca', '( %s -> ( ( Z ^c %s ) <_ ( W + 1 ) /\\ q e. NN /\\ W < q ) )' % (HQ, E99))
sqlt = w.s([w.s([sq1, sq2], 'jca', '( %s -> ( ( Z e. NN /\\ 1 < Z /\\ W e. NN0 ) /\\ ( ( Z ^c %s ) <_ ( W + 1 ) /\\ q e. NN /\\ W < q ) ) )' % (HQ, E99)), w.inst('extrwsqrt')], 'syl', '( %s -> ( sqrt ` Z ) < q )' % HQ)
ral = w.s([sqlt], 'ralrimiva', '( %s -> A. q e. Q ( sqrt ` Z ) < q )' % H)
w.qed([w.s([znn, qfpp, ral], '3jca', '( %s -> ( Z e. NN /\\ Q e. %s /\\ A. q e. Q ( sqrt ` Z ) < q ) )' % (H, FPP)), w.inst('extrwloglge')], 'syl', '( %s -> ( ( # ` Q ) x. ( ( log ` Z ) / 2 ) ) <_ ( log ` %s ) )' % (H, LM))
run(w)
