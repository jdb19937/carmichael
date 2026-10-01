"""Sortie A3b, batch 4: the output certificate at windowed scales, pointwise
(A3b-blueprint.md section 2.4)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
import a3blib as LIB, a3lib
from a3blib import HC, HN, NS, N5, IW, P2, GW, PL, A, B
from a3blib import L as LM
from tm import *
from lin import linarith
from a3lib import lineq
import num
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

a, b = A(), B()
n = NS()
ANT = '( %s /\\ %s /\\ %s )' % (HC, HN(), IW())
ZB = '( 1 < Z /\\ %s <_ ( log ` Z ) /\\ ( log ` Z ) <_ ( 3 x. %s ) )' % (b, b)
N9 = '( ; ; 1 5 0 x. ( %s ^ 2 ) ) <_ ( exp ` %s )' % (a, a)
N10 = '( ( ; 7 5 / D ) x. ( %s ^ 2 ) ) <_ ( exp ` ( ( 9 / ; 1 0 ) x. %s ) )' % (a, a)
DD = '( D e. RR /\\ 0 < D )'
ANTO = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (ANT, DD, N9, N10)
ZT = '( Z ^ ( ; 1 0 x. T ) ) <_ N'
OV = '( %s x. ( ( 5 x. T ) x. ( log ` Z ) ) ) <_ ( D x. ( log ` N ) )' % P2


def common(w, X):
    """every fact the two output lemmas share, from the antecedent X = ANTO"""
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (X, f))
    anl = st([], 'simp1', ANT)
    d = LIB.relay(w, X, anl)
    d['anl'] = anl
    d['dre'] = st([st([], 'simp2', DD)], 'simpld', 'D e. RR')
    d['d0'] = st([st([], 'simp2', DD)], 'simprd', '0 < D')
    nn = st([], 'simp3', '( %s /\\ %s )' % (N9, N10))
    d['n9'] = st([nn], 'simpld', N9)
    d['n10'] = st([nn], 'simprd', N10)
    zb = st([anl, w.inst('extrwzcw')], 'syl', ZB)
    d.update(LIB.zfacts(w, X, d, zb))
    # N in RR+, log N in RR+, exp ( ell2 N ) = log N
    d['nnn'] = st([d['uz2'], w.inst('eluz2nn')], 'syl', 'N e. NN')
    d['nre'] = st([d['nnn']], 'nnred', 'N e. RR')
    d['nrp'] = st([d['nnn']], 'nnrpd', 'N e. RR+')
    d['n1lt'] = st([d['uz2'], w.inst('eluz2gt1')], 'syl', '1 < N')
    d['lnrp'] = st([d['nre'], d['n1lt'], w.inst('rplogcl')], 'syl2anc', '( log ` N ) e. RR+')
    d['lnre'] = st([d['lnrp']], 'rpred', '( log ` N ) e. RR')
    e2v = st([d['nn0'], w.inst('ell2val')], 'syl', '%s = ( log ` ( log ` N ) )' % a)
    d['efeq'] = st([st([e2v], 'fveq2d', '( exp ` %s ) = ( exp ` ( log ` ( log ` N ) ) )' % a),
                    st([d['lnrp'], w.inst('reeflog')], 'syl', '( exp ` ( log ` ( log ` N ) ) ) = ( log ` N )')],
                   'eqtrd', '( exp ` %s ) = ( log ` N )' % a)
    # ell3 N <_ ell2 N  and  ( ell2 N x. ell3 N ) <_ ( ell2 N ^ 2 )
    LV = {a: ('RR', d['are']), b: ('RR', d['bre']), 'T': ('RR', d['tre']), '( log ` Z )': ('RR', d['lzre'])}
    d['lv'] = LV
    d['a1'] = linarith(w, X, [d['n2']], '1 <_ %s' % a, leaves=LV)
    d['ag0'] = linarith(w, X, [d['n2']], '0 <_ %s' % a, leaves=LV)
    lgle = st([d['are'], d['a1'], w.inst('loglet')], 'syl2anc', '( log ` %s ) <_ %s' % (a, a))
    d['bla'] = st([d['beq'], lgle], 'eqbrtrd', '%s <_ %s' % (b, a))
    m = st([d['bre'], d['are'], d['are'], d['ag0'], d['bla']], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (a, b, a, a))
    sq = st([st([d['are']], 'recnd', '%s e. CC' % a)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (a, a, a))
    d['absq'] = st([m, sq], 'breqtrrd', '( %s x. %s ) <_ ( %s ^ 2 )' % (a, b, a))
    d['abre'] = st([d['are'], d['bre']], 'remulcld', '( %s x. %s ) e. RR' % (a, b))
    d['asqre'] = st([d['are'], st([num.fact(w, '2', 'NN0')], 'a1i', '2 e. NN0')], 'reexpcld', '( %s ^ 2 ) e. RR' % a)
    d['tg0'] = st([d['tn0']], 'nn0ge0d', '0 <_ T')
    return d

# ------------------------------------------------------------------ outwztw
w = W('outwztw', 'At windowed scales z ^ ( 10 T ) <_ n (Lean: the first conclusion of eventually_uW of OutputW.lean).')
def st(hyps, ref, f):
    return w.s(hyps, ref, '( %s -> %s )' % (ANTO, f))
d = common(w, ANTO)
LV = d['lv']
i10n0 = st([num.fact(w, '; 1 0', 'NN0')], 'a1i', '; 1 0 e. NN0')
tn = st([i10n0, d['tn0']], 'nn0mulcld', '( ; 1 0 x. T ) e. NN0')
tz = st([tn], 'nn0zd', '( ; 1 0 x. T ) e. ZZ')
lex = st([d['zrp'], tz, w.inst('relogexp')], 'syl2anc', '( log ` ( Z ^ ( ; 1 0 x. T ) ) ) = ( ( ; 1 0 x. T ) x. ( log ` Z ) )')
t10 = linarith(w, ANTO, [d['thi']], '( ; 1 0 x. T ) <_ ( ; 5 0 x. %s )' % a, leaves=LV)
t10r = st([st([num.fact(w, '; 1 0', 'RR')], 'a1i', '; 1 0 e. RR'), d['tre']], 'remulcld', '( ; 1 0 x. T ) e. RR')
f50 = st([st([num.fact(w, '; 5 0', 'RR')], 'a1i', '; 5 0 e. RR'), d['are']], 'remulcld', '( ; 5 0 x. %s ) e. RR' % a)
f3b = st([st([num.fact(w, '3', 'RR')], 'a1i', '3 e. RR'), d['bre']], 'remulcld', '( 3 x. %s ) e. RR' % b)
t10g0 = linarith(w, ANTO, [d['tg0']], '0 <_ ( ; 1 0 x. T )', leaves=LV)
m1 = st([t10r, f50, d['lzre'], f3b, t10g0, d['lz0'], t10, d['lzub']], 'lemul12ad',
        '( ( ; 1 0 x. T ) x. ( log ` Z ) ) <_ ( ( ; 5 0 x. %s ) x. ( 3 x. %s ) )' % (a, b))
i50cn = st([num.cc(w, '; 5 0')], 'a1i', '; 5 0 e. CC')
i3cn = st([num.cc(w, '3')], 'a1i', '3 e. CC')
acn = st([d['are']], 'recnd', '%s e. CC' % a)
bcn = st([d['bre']], 'recnd', '%s e. CC' % b)
m4 = st([i50cn, acn, i3cn, bcn], 'mul4d', '( ( ; 5 0 x. %s ) x. ( 3 x. %s ) ) = ( ( ; 5 0 x. 3 ) x. ( %s x. %s ) )' % (a, b, a, b))
n150 = st([num.mul_nat(w, 50, 3)], 'a1i', '( ; 5 0 x. 3 ) = ; ; 1 5 0')
m4b = st([m4, st([n150], 'oveq1d', '( ( ; 5 0 x. 3 ) x. ( %s x. %s ) ) = ( ; ; 1 5 0 x. ( %s x. %s ) )' % (a, b, a, b))], 'eqtrd',
         '( ( ; 5 0 x. %s ) x. ( 3 x. %s ) ) = ( ; ; 1 5 0 x. ( %s x. %s ) )' % (a, b, a, b))
i150r = st([num.fact(w, '; ; 1 5 0', 'RR')], 'a1i', '; ; 1 5 0 e. RR')
i150g0 = st([num.fact(w, '; ; 1 5 0', 'ge0')], 'a1i', '0 <_ ; ; 1 5 0')
m2 = st([d['abre'], d['asqre'], i150r, i150g0, d['absq']], 'lemul2ad',
        '( ; ; 1 5 0 x. ( %s x. %s ) ) <_ ( ; ; 1 5 0 x. ( %s ^ 2 ) )' % (a, b, a))
efre = st([st([d['are'], w.inst('rpefcl')], 'syl', '( exp ` %s ) e. RR+' % a)], 'rpred', '( exp ` %s ) e. RR' % a)
S1 = '( ( ; 1 0 x. T ) x. ( log ` Z ) )'
S3 = '( ; ; 1 5 0 x. ( %s x. %s ) )' % (a, b)
S4 = '( ; ; 1 5 0 x. ( %s ^ 2 ) )' % a
s1re = st([t10r, d['lzre']], 'remulcld', '%s e. RR' % S1)
s3re = st([i150r, d['abre']], 'remulcld', '%s e. RR' % S3)
s4re = st([i150r, d['asqre']], 'remulcld', '%s e. RR' % S4)
c0 = st([m1, m4b], 'breqtrd', '%s <_ %s' % (S1, S3))
c1 = st([s1re, s3re, s4re, c0, m2], 'letrd', '%s <_ %s' % (S1, S4))
c2 = st([s1re, s4re, efre, c1, d['n9']], 'letrd', '%s <_ ( exp ` %s )' % (S1, a))
c3 = st([c2, d['efeq']], 'breqtrd', '%s <_ ( log ` N )' % S1)
c4 = st([lex, c3], 'eqbrtrd', '( log ` ( Z ^ ( ; 1 0 x. T ) ) ) <_ ( log ` N )')
ztrp = st([d['zrp'], tz], 'rpexpcld', '( Z ^ ( ; 1 0 x. T ) ) e. RR+')
bi = st([ztrp, d['nrp'], w.inst('logleb')], 'syl2anc',
        '( ( Z ^ ( ; 1 0 x. T ) ) <_ N <-> ( log ` ( Z ^ ( ; 1 0 x. T ) ) ) <_ ( log ` N ) )')
w.qed([bi, c4], 'mpbird', '( %s -> %s )' % (ANTO, ZT))
assert run(w)

# ------------------------------------------------------------------ outwovw
w = W('outwovw', 'The overshoot comparison at windowed scales (Lean: the second conclusion of eventually_uW of OutputW.lean, by way of A3 extrwp2).')
def st(hyps, ref, f):
    return w.s(hyps, ref, '( %s -> %s )' % (ANTO, f))
d = common(w, ANTO)
LV = d['lv']
R = '( ( 5 x. T ) x. ( log ` Z ) )'
X1 = '( exp ` ( ( 1 / ; 1 0 ) x. %s ) )' % a
X9 = '( exp ` ( ( 9 / ; 1 0 ) x. %s ) )' % a
QT = '( ( ; 7 5 / D ) x. ( %s ^ 2 ) )' % a
i5r = st([num.fact(w, '5', 'RR')], 'a1i', '5 e. RR')
i25r = st([num.fact(w, '; 2 5', 'RR')], 'a1i', '; 2 5 e. RR')
i3r = st([num.fact(w, '3', 'RR')], 'a1i', '3 e. RR')
t5r = st([i5r, d['tre']], 'remulcld', '( 5 x. T ) e. RR')
f25 = st([i25r, d['are']], 'remulcld', '( ; 2 5 x. %s ) e. RR' % a)
f3b = st([i3r, d['bre']], 'remulcld', '( 3 x. %s ) e. RR' % b)
t5le = linarith(w, ANTO, [d['thi']], '( 5 x. T ) <_ ( ; 2 5 x. %s )' % a, leaves=LV)
t5g0 = linarith(w, ANTO, [d['tg0']], '0 <_ ( 5 x. T )', leaves=LV)
m1 = st([t5r, f25, d['lzre'], f3b, t5g0, d['lz0'], t5le, d['lzub']], 'lemul12ad',
        '%s <_ ( ( ; 2 5 x. %s ) x. ( 3 x. %s ) )' % (R, a, b))
i25cn = st([num.cc(w, '; 2 5')], 'a1i', '; 2 5 e. CC')
i3cn = st([num.cc(w, '3')], 'a1i', '3 e. CC')
acn = st([d['are']], 'recnd', '%s e. CC' % a)
bcn = st([d['bre']], 'recnd', '%s e. CC' % b)
m4 = st([i25cn, acn, i3cn, bcn], 'mul4d', '( ( ; 2 5 x. %s ) x. ( 3 x. %s ) ) = ( ( ; 2 5 x. 3 ) x. ( %s x. %s ) )' % (a, b, a, b))
n75 = st([num.mul_nat(w, 25, 3)], 'a1i', '( ; 2 5 x. 3 ) = ; 7 5')
S3 = '( ; 7 5 x. ( %s x. %s ) )' % (a, b)
S4 = '( ; 7 5 x. ( %s ^ 2 ) )' % a
m4b = st([m4, st([n75], 'oveq1d', '( ( ; 2 5 x. 3 ) x. ( %s x. %s ) ) = %s' % (a, b, S3))], 'eqtrd',
         '( ( ; 2 5 x. %s ) x. ( 3 x. %s ) ) = %s' % (a, b, S3))
i75r = st([num.fact(w, '; 7 5', 'RR')], 'a1i', '; 7 5 e. RR')
i75g0 = st([num.fact(w, '; 7 5', 'ge0')], 'a1i', '0 <_ ; 7 5')
m2 = st([d['abre'], d['asqre'], i75r, i75g0, d['absq']], 'lemul2ad', '%s <_ %s' % (S3, S4))
# ( 75 x. ( ell2 N ^ 2 ) ) = ( D x. ( ( 75 / D ) x. ( ell2 N ^ 2 ) ) )
dcn = st([d['dre']], 'recnd', 'D e. CC')
dne = st([d['d0']], 'gt0ne0d', 'D =/= 0')
i75cn = st([num.cc(w, '; 7 5')], 'a1i', '; 7 5 e. CC')
asqcn = st([d['asqre']], 'recnd', '( %s ^ 2 ) e. CC' % a)
dq = st([i75cn, dcn, dne], 'divcan2d', '( D x. ( ; 7 5 / D ) ) = ; 7 5')
dqcn = st([i75cn, dcn, dne], 'divcld', '( ; 7 5 / D ) e. CC')
as1 = st([dcn, dqcn, asqcn], 'mulassd', '( ( D x. ( ; 7 5 / D ) ) x. ( %s ^ 2 ) ) = ( D x. %s )' % (a, QT))
as2 = st([st([dq], 'oveq1d', '( ( D x. ( ; 7 5 / D ) ) x. ( %s ^ 2 ) ) = %s' % (a, S4)), as1], 'eqtr3d',
         '%s = ( D x. %s )' % (S4, QT))
d0le = st([d['d0']], 'ltled', '0 <_ D')
qtre = st([st([i75r, d['dre'], dne], 'redivcld', '( ; 7 5 / D ) e. RR'), d['asqre']], 'remulcld', '%s e. RR' % QT)
x9re = st([st([st([st([num.fact(w, '( 9 / ; 1 0 )', 'RR')], 'a1i', '( 9 / ; 1 0 ) e. RR'), d['are']], 'remulcld', '( ( 9 / ; 1 0 ) x. %s ) e. RR' % a), w.inst('rpefcl')], 'syl', '%s e. RR+' % X9)], 'rpred', '%s e. RR' % X9)
m3 = st([qtre, x9re, d['dre'], d0le, d['n10']], 'lemul2ad', '( D x. %s ) <_ ( D x. %s )' % (QT, X9))
# chain to R <_ ( D x. X9 )
rre = st([t5r, d['lzre']], 'remulcld', '%s e. RR' % R)
s3re = st([i75r, d['abre']], 'remulcld', '%s e. RR' % S3)
s4re = st([i75r, d['asqre']], 'remulcld', '%s e. RR' % S4)
dx9re = st([d['dre'], x9re], 'remulcld', '( D x. %s ) e. RR' % X9)
dqtre = st([d['dre'], qtre], 'remulcld', '( D x. %s ) e. RR' % QT)
c0 = st([m1, m4b], 'breqtrd', '%s <_ %s' % (R, S3))
c1 = st([rre, s3re, s4re, c0, m2], 'letrd', '%s <_ %s' % (R, S4))
c2 = st([c1, as2], 'breqtrd', '%s <_ ( D x. %s )' % (R, QT))
c3 = st([rre, dqtre, dx9re, c2, m3], 'letrd', '%s <_ ( D x. %s )' % (R, X9))
rg0 = st([t5r, d['lzre'], t5g0, d['lz0']], 'mulge0d', '0 <_ %s' % R)
# P2 typing and the extrwp2w bound
y1n0 = st([d['yn0'], st([num.fact(w, '1', 'NN0')], 'a1i', '1 e. NN0')], 'nn0addcld', '( Y + 1 ) e. NN0')
zg0 = st([d['zn0']], 'nn0ge0d', '0 <_ Z')
zyre = st([d['zre'], y1n0], 'reexpcld', '( Z ^ ( Y + 1 ) ) e. RR')
zyg0 = st([d['zre'], y1n0, zg0], 'expge0d', '0 <_ ( Z ^ ( Y + 1 ) )')
tlzre = st([d['tre'], d['lzre']], 'remulcld', '( T x. ( log ` Z ) ) e. RR')
tlzg0 = st([d['tre'], d['lzre'], d['tg0'], d['lz0']], 'mulge0d', '0 <_ ( T x. ( log ` Z ) )')
f2re = st([st([num.fact(w, '1', 'RR')], 'a1i', '1 e. RR'), tlzre], 'readdcld', '( 1 + ( T x. ( log ` Z ) ) ) e. RR')
f2g0 = linarith(w, ANTO, [tlzg0], '0 <_ ( 1 + ( T x. ( log ` Z ) ) )', leaves={'( T x. ( log ` Z ) )': ('RR', tlzre)})
prre = st([zyre, f2re], 'remulcld', '( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) ) e. RR')
prg0 = st([zyre, f2re, zyg0, f2g0], 'mulge0d', '0 <_ ( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) )')
p2re = st([prre, st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % P2)
p2g0 = linarith(w, ANTO, [prg0], '0 <_ %s' % P2, leaves={'( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) )': ('RR', prre)})
p2le = st([d['anl'], w.inst('extrwp2w')], 'syl', '%s <_ %s' % (P2, X1))
x1re = st([st([st([st([num.fact(w, '( 1 / ; 1 0 )', 'RR')], 'a1i', '( 1 / ; 1 0 ) e. RR'), d['are']], 'remulcld', '( ( 1 / ; 1 0 ) x. %s ) e. RR' % a), w.inst('rpefcl')], 'syl', '%s e. RR+' % X1)], 'rpred', '%s e. RR' % X1)
mm = st([p2re, x1re, rre, dx9re, p2g0, rg0, p2le, c3], 'lemul12ad', '( %s x. %s ) <_ ( %s x. ( D x. %s ) )' % (P2, R, X1, X9))
# ( X1 x. ( D x. X9 ) ) = ( D x. ( log ` N ) )
x1cn = st([x1re], 'recnd', '%s e. CC' % X1)
x9cn = st([x9re], 'recnd', '%s e. CC' % X9)
m12 = st([x1cn, dcn, x9cn], 'mul12d', '( %s x. ( D x. %s ) ) = ( D x. ( %s x. %s ) )' % (X1, X9, X1, X9))
i1t = st([num.fact(w, '( 1 / ; 1 0 )', 'RR')], 'a1i', '( 1 / ; 1 0 ) e. RR')
i9t = st([num.fact(w, '( 9 / ; 1 0 )', 'RR')], 'a1i', '( 9 / ; 1 0 ) e. RR')
u1re = st([i1t, d['are']], 'remulcld', '( ( 1 / ; 1 0 ) x. %s ) e. RR' % a)
u9re = st([i9t, d['are']], 'remulcld', '( ( 9 / ; 1 0 ) x. %s ) e. RR' % a)
sumre = st([u1re, u9re], 'readdcld', '( ( ( 1 / ; 1 0 ) x. %s ) + ( ( 9 / ; 1 0 ) x. %s ) ) e. RR' % (a, a))
seq = lineq(w, ANTO, [], '( ( ( 1 / ; 1 0 ) x. %s ) + ( ( 9 / ; 1 0 ) x. %s ) )' % (a, a), a,
            {a: ('RR', d['are'])}, sumre, d['are'], linarith)
ef1 = st([st([u1re], 'recnd', '( ( 1 / ; 1 0 ) x. %s ) e. CC' % a), st([u9re], 'recnd', '( ( 9 / ; 1 0 ) x. %s ) e. CC' % a), w.inst('efadd')], 'syl2anc',
         '( exp ` ( ( ( 1 / ; 1 0 ) x. %s ) + ( ( 9 / ; 1 0 ) x. %s ) ) ) = ( %s x. %s )' % (a, a, X1, X9))
ef2 = st([st([seq], 'fveq2d', '( exp ` ( ( ( 1 / ; 1 0 ) x. %s ) + ( ( 9 / ; 1 0 ) x. %s ) ) ) = ( exp ` %s )' % (a, a, a)), ef1], 'eqtr3d',
         '( %s x. %s ) = ( exp ` %s )' % (X1, X9, a))
ef3 = st([ef2, d['efeq']], 'eqtrd', '( %s x. %s ) = ( log ` N )' % (X1, X9))
rhs = st([m12, st([ef3], 'oveq2d', '( D x. ( %s x. %s ) ) = ( D x. ( log ` N ) )' % (X1, X9))], 'eqtrd',
         '( %s x. ( D x. %s ) ) = ( D x. ( log ` N ) )' % (X1, X9))
w.qed([mm, rhs], 'breqtrd', '( %s -> %s )' % (ANTO, OV))
assert run(w)

# ------------------------------------------------------------------ outwcw
CONCL5 = LIB.dbconcl('outwins')
QP = '( Q e. ~P %s /\\ ( # ` Q ) = T )' % GW
KC = '( K e. NN /\\ ( K gcd %s ) = 1 )' % LM
PRD = 'prod_ j e. S j'
SH = ('( S e. ~P %s /\\ ( S =/= (/) /\\ %s || ( %s - 1 ) ) /\\ ( N < %s /\\ %s <_ ( N x. ( ( xceil ` Q ) ^ ( Nstar ` Q ) ) ) ) )'
      % (PL, LM, PRD, PRD, PRD))
HS = '( %s /\\ %s /\\ %s )' % (QP, KC, SH)
ANTW = '( %s /\\ %s )' % (ANTO, HS)
w = W('outwcw', 'The output certificate at windowed scales, pointwise (Lean: the body of output_carmichaelW of OutputW.lean).')
def st(hyps, ref, f):
    return w.s(hyps, ref, '( %s -> %s )' % (ANTW, f))
anl = st([], 'simpl', ANTO)
ant = st([anl], 'simp1d', ANT)
d = LIB.relay(w, ANTW, ant)
dre = st([st([anl], 'simp2d', DD)], 'simpld', 'D e. RR')
zb = st([ant, w.inst('extrwzcw')], 'syl', ZB)
z = LIB.zfacts(w, ANTW, d, zb)
zt = st([anl, w.inst('outwztw')], 'syl', ZT)
ov = st([anl, w.inst('outwovw')], 'syl', OV)
hs = st([], 'simpr', HS)
qp = st([hs], 'simp1d', QP)
kc = st([hs], 'simp2d', KC)
sh = st([hs], 'simp3d', SH)
spw = st([sh], 'simp1d', 'S e. ~P %s' % PL)
smod = st([st([sh], 'simp2d', '( S =/= (/) /\\ %s || ( %s - 1 ) )' % (LM, PRD))], 'simprd', '%s || ( %s - 1 )' % (LM, PRD))
sbnd = st([sh], 'simp3d', '( N < %s /\\ %s <_ ( N x. ( ( xceil ` Q ) ^ ( Nstar ` Q ) ) ) )' % (PRD, PRD))
x1 = st([st([z['znn'], d['wn0']], 'jca', '( Z e. NN /\\ W e. NN0 )'),
         st([d['yn0'], d['tn0']], 'jca', '( Y e. NN0 /\\ T e. NN0 )')], 'jca',
        '( ( Z e. NN /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) )')
x2 = st([x1, st([qp, kc], 'jca', '( %s /\\ %s )' % (QP, KC))], 'jca',
        '( ( ( Z e. NN /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) ) /\\ ( %s /\\ %s ) )' % (QP, KC))
X = st([x2, spw], 'jca',
       '( ( ( ( Z e. NN /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) ) /\\ ( %s /\\ %s ) ) /\\ S e. ~P %s )' % (QP, KC, PL))
y1 = st([st([d['uz2'], dre], 'jca', '( N e. ( ZZ>= ` 2 ) /\\ D e. RR )'),
         st([zt, ov], 'jca', '( %s /\\ %s )' % (ZT, OV))], 'jca',
        '( ( N e. ( ZZ>= ` 2 ) /\\ D e. RR ) /\\ ( %s /\\ %s ) )' % (ZT, OV))
tri = st([smod, st([sbnd], 'simpld', 'N < %s' % PRD), st([sbnd], 'simprd', '%s <_ ( N x. ( ( xceil ` Q ) ^ ( Nstar ` Q ) ) )' % PRD)], '3jca',
         '( %s || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( ( xceil ` Q ) ^ ( Nstar ` Q ) ) ) )' % (LM, PRD, PRD, PRD))
Y = st([y1, tri], 'jca',
       '( ( ( N e. ( ZZ>= ` 2 ) /\\ D e. RR ) /\\ ( %s /\\ %s ) ) /\\ ( %s || ( %s - 1 ) /\\ N < %s /\\ %s <_ ( N x. ( ( xceil ` Q ) ^ ( Nstar ` Q ) ) ) ) )' % (ZT, OV, LM, PRD, PRD, PRD))
w.qed([X, Y, w.inst('outwins')], 'syl2anc', '( %s -> %s )' % (ANTW, CONCL5))
assert run(w)
