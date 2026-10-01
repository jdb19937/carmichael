"""Sortie C0c batch 1: the slit plane and the logarithm jump across the cut."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from lin import linarith

# ---- elslitim: a nonreal number is in the slit plane
w = W('elslitim', 'A complex number with nonzero imaginary part lies in the slit plane, the domain of the principal logarithm.')
A0 = '( W e. CC /\\ ( Im ` W ) =/= 0 )'
wc = w.s([], 'simpl', '( %s -> W e. CC )' % A0)
wi = w.s([], 'simpr', '( %s -> ( Im ` W ) =/= 0 )' % A0)
rb = w.s([wc, w.inst('reim0b')], 'syl', '( %s -> ( W e. RR <-> ( Im ` W ) = 0 ) )' % A0)
nn = w.s([wi], 'neneqd', '( %s -> -. ( Im ` W ) = 0 )' % A0)
nr = w.s([nn, rb], 'mtbird', '( %s -> -. W e. RR )' % A0)
im = w.s([nr], 'pm2.21d', '( %s -> ( W e. RR -> W e. RR+ ) )' % A0)
jc = w.s([wc, im], 'jca', '( %s -> ( W e. CC /\\ ( W e. RR -> W e. RR+ ) ) )' % A0)
e1 = w.s([], 'eqid', '%s = %s' % (DD, DD))
el = w.s([e1], 'ellogdm', '( W e. %s <-> ( W e. CC /\\ ( W e. RR -> W e. RR+ ) ) )' % DD)
eld = w.s([el], 'a1i', '( %s -> ( W e. %s <-> ( W e. CC /\\ ( W e. RR -> W e. RR+ ) ) ) )' % (A0, DD))
w.qed([jc, eld], 'mpbird', '( %s -> W e. %s )' % (A0, DD)); run(w)

# ---- elslitre: positive real part puts a number in the slit plane
w = W('elslitre', 'A complex number with positive real part lies in the slit plane, the domain of the principal logarithm.')
A0 = '( W e. CC /\\ 0 < ( Re ` W ) )'
A1 = '( %s /\\ W e. RR )' % A0
wc = w.s([], 'simpl', '( %s -> W e. CC )' % A0)
wr0 = w.s([], 'simpr', '( %s -> 0 < ( Re ` W ) )' % A0)
wr = w.s([], 'simpr', '( %s -> W e. RR )' % A1)
wc2 = w.s([wc], 'adantr', '( %s -> W e. CC )' % A1)
rb = w.s([wc2, w.inst('rereb')], 'syl', '( %s -> ( W e. RR <-> ( Re ` W ) = W ) )' % A1)
eq = w.s([wr, rb], 'mpbid', '( %s -> ( Re ` W ) = W )' % A1)
lt = w.s([w.s([wr0], 'adantr', '( %s -> 0 < ( Re ` W ) )' % A1), eq], 'breqtrd', '( %s -> 0 < W )' % A1)
rp = w.s([wr, lt], 'elrpd', '( %s -> W e. RR+ )' % A1)
im = w.s([rp], 'ex', '( %s -> ( W e. RR -> W e. RR+ ) )' % A0)
jc = w.s([wc, im], 'jca', '( %s -> ( W e. CC /\\ ( W e. RR -> W e. RR+ ) ) )' % A0)
e1 = w.s([], 'eqid', '%s = %s' % (DD, DD))
el = w.s([e1], 'ellogdm', '( W e. %s <-> ( W e. CC /\\ ( W e. RR -> W e. RR+ ) ) )' % DD)
eld = w.s([el], 'a1i', '( %s -> ( W e. %s <-> ( W e. CC /\\ ( W e. RR -> W e. RR+ ) ) ) )' % (A0, DD))
w.qed([jc, eld], 'mpbird', '( %s -> W e. %s )' % (A0, DD)); run(w)

# ---- clogneg: the logarithm of the negative, below the real axis
w = W('clogneg', 'Below the real axis the principal logarithm of the negative is the logarithm plus _i x. _pi.')
A0 = '( V e. CC /\\ ( Im ` V ) < 0 )'
L = LOG('V'); B = '( %s + %s )' % (L, IPI)
vc = w.s([], 'simpl', '( %s -> V e. CC )' % A0)
vlt = w.s([], 'simpr', '( %s -> ( Im ` V ) < 0 )' % A0)
imr = w.s([vc, w.inst('imcl')], 'syl', '( %s -> ( Im ` V ) e. RR )' % A0)
ine = w.s([imr, vlt], 'ltned', '( %s -> ( Im ` V ) =/= 0 )' % A0)
# V =/= 0
i0 = w.s([], 'im0', '( Im ` 0 ) = 0')
fq = w.s([], 'fveq2', '( V = 0 -> ( Im ` V ) = ( Im ` 0 ) )')
gq = w.s([fq, i0], 'eqtrdi', '( V = 0 -> ( Im ` V ) = 0 )')
gqd = w.s([gq], 'a1i', '( %s -> ( V = 0 -> ( Im ` V ) = 0 ) )' % A0)
nne = w.s([ine], 'neneqd', '( %s -> -. ( Im ` V ) = 0 )' % A0)
nv0 = w.s([nne, gqd], 'mtod', '( %s -> -. V = 0 )' % A0)
vne = w.s([nv0], 'neqned', '( %s -> V =/= 0 )' % A0)
nvc = w.s([vc], 'negcld', '( %s -> -u V e. CC )' % A0)
nvne = w.s([vc, vne], 'negne0d', '( %s -> -u V =/= 0 )' % A0)
# closures
lc = w.s([vc, vne], 'logcld', '( %s -> %s e. CC )' % (A0, L))
ic = closed(w, A0, 'ax-icn', '_i e. CC')
pic = closed(w, A0, 'picn', '_pi e. CC')
pir = closed(w, A0, 'pire', '_pi e. RR')
pipos = closed(w, A0, 'pipos', '0 < _pi')
ipc = w.s([ic, pic], 'mulcld', '( %s -> %s e. CC )' % (A0, IPI))
bc = w.s([lc, ipc], 'addcld', '( %s -> %s e. CC )' % (A0, B))
# exp ` B = -u V
e1 = w.s([lc, ipc, w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (A0, B, L, IPI))
e2 = w.s([vc, vne, w.inst('eflog')], 'syl2anc', '( %s -> ( exp ` %s ) = V )' % (A0, L))
e3 = closed(w, A0, 'efipi', '( exp ` %s ) = -u 1' % IPI)
e4 = w.s([e2, e3], 'oveq12d', '( %s -> ( ( exp ` %s ) x. ( exp ` %s ) ) = ( V x. -u 1 ) )' % (A0, L, IPI))
n1c = closed(w, A0, 'neg1cn', '-u 1 e. CC')
e5 = w.s([vc, n1c], 'mulcomd', '( %s -> ( V x. -u 1 ) = ( -u 1 x. V ) )' % A0)
e6 = w.s([vc, w.inst('mulm1')], 'syl', '( %s -> ( -u 1 x. V ) = -u V )' % A0)
ex = w.s([w.s([w.s([e1, e4], 'eqtrd', '( %s -> ( exp ` %s ) = ( V x. -u 1 ) )' % (A0, B)), e5], 'eqtrd',
              '( %s -> ( exp ` %s ) = ( -u 1 x. V ) )' % (A0, B)), e6], 'eqtrd', '( %s -> ( exp ` %s ) = -u V )' % (A0, B))
# B e. ran log
al = w.s([vc, vlt, w.inst('argimlt0')], 'syl2anc', '( %s -> ( Im ` %s ) e. ( -u _pi (,) 0 )' % (A0, L) + ' )')
ord_ = w.s([al, w.inst('eliooord')], 'syl', '( %s -> ( -u _pi < ( Im ` %s ) /\\ ( Im ` %s ) < 0 ) )' % (A0, L, L))
lo = w.s([ord_, w.inst('simpl')], 'syl', '( %s -> -u _pi < ( Im ` %s ) )' % (A0, L))
hi = w.s([ord_, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) < 0 )' % (A0, L))
imlr = w.s([lc, w.inst('imcl')], 'syl', '( %s -> ( Im ` %s ) e. RR )' % (A0, L))
# ( Im ` B ) = ( ( Im ` L ) + _pi )
ri = w.s([pic, w.inst('reim')], 'syl', '( %s -> ( Re ` _pi ) = ( Im ` %s ) )' % (A0, IPI))
rr = w.s([pir, w.inst('rere')], 'syl', '( %s -> ( Re ` _pi ) = _pi )' % A0)
imip = w.s([ri, rr], 'eqtr3d', '( %s -> ( Im ` %s ) = _pi )' % (A0, IPI))
ia = w.s([lc, ipc, w.inst('imadd')], 'syl2anc', '( %s -> ( Im ` %s ) = ( ( Im ` %s ) + ( Im ` %s ) ) )' % (A0, B, L, IPI))
imb = w.s([ia, w.s([imip], 'oveq2d', '( %s -> ( ( Im ` %s ) + ( Im ` %s ) ) = ( ( Im ` %s ) + _pi ) )' % (A0, L, IPI, L))],
          'eqtrd', '( %s -> ( Im ` %s ) = ( ( Im ` %s ) + _pi ) )' % (A0, B, L))
leaves = {'( Im ` %s )' % L: imlr, '_pi': pir}
g1 = linarith(w, A0, [lo, hi, pipos], '-u _pi < ( ( Im ` %s ) + _pi )' % L, leaves=leaves)
g2 = linarith(w, A0, [lo, hi, pipos], '( ( Im ` %s ) + _pi ) <_ _pi' % L, leaves=leaves)
b1 = w.s([g1, imb], 'breqtrrd', '( %s -> -u _pi < ( Im ` %s ) )' % (A0, B))
b2 = w.s([imb, g2], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ _pi )' % (A0, B))
erl = w.s([], 'ellogrn', '( %s e. ran log <-> ( %s e. CC /\\ -u _pi < ( Im ` %s ) /\\ ( Im ` %s ) <_ _pi ) )' % (B, B, B, B))
erld = w.s([erl], 'a1i', '( %s -> ( %s e. ran log <-> ( %s e. CC /\\ -u _pi < ( Im ` %s ) /\\ ( Im ` %s ) <_ _pi ) ) )' % (A0, B, B, B, B))
brl = w.s([bc, b1, b2, erld], 'mpbir3and', '( %s -> %s e. ran log )' % (A0, B))
tb = w.s([nvc, nvne, brl, w.inst('logeftb')], 'syl3anc', '( %s -> ( ( log ` -u V ) = %s <-> ( exp ` %s ) = -u V ) )' % (A0, B, B))
w.qed([ex, tb], 'mpbird', '( %s -> ( log ` -u V ) = %s )' % (A0, B)); run(w)

# ---- clogdif2: the jump below the real axis
w = W('clogdif2', 'Below the real axis the principal logarithm of the negative exceeds the logarithm by _i x. _pi.')
A0 = '( V e. CC /\\ ( Im ` V ) < 0 )'
L = LOG('V'); B = '( %s + %s )' % (L, IPI)
vc = w.s([], 'simpl', '( %s -> V e. CC )' % A0)
vlt = w.s([], 'simpr', '( %s -> ( Im ` V ) < 0 )' % A0)
imr = w.s([vc, w.inst('imcl')], 'syl', '( %s -> ( Im ` V ) e. RR )' % A0)
ine = w.s([imr, vlt], 'ltned', '( %s -> ( Im ` V ) =/= 0 )' % A0)
i0 = w.s([], 'im0', '( Im ` 0 ) = 0')
fq = w.s([], 'fveq2', '( V = 0 -> ( Im ` V ) = ( Im ` 0 ) )')
gq = w.s([fq, i0], 'eqtrdi', '( V = 0 -> ( Im ` V ) = 0 )')
gqd = w.s([gq], 'a1i', '( %s -> ( V = 0 -> ( Im ` V ) = 0 ) )' % A0)
nne = w.s([ine], 'neneqd', '( %s -> -. ( Im ` V ) = 0 )' % A0)
vne = w.s([w.s([nne, gqd], 'mtod', '( %s -> -. V = 0 )' % A0)], 'neqned', '( %s -> V =/= 0 )' % A0)
lc = w.s([vc, vne], 'logcld', '( %s -> %s e. CC )' % (A0, L))
ic = closed(w, A0, 'ax-icn', '_i e. CC'); pic = closed(w, A0, 'picn', '_pi e. CC')
ipc = w.s([ic, pic], 'mulcld', '( %s -> %s e. CC )' % (A0, IPI))
cn = w.s([vc, vlt, w.inst('clogneg')], 'syl2anc', '( %s -> ( log ` -u V ) = %s )' % (A0, B))
o1 = w.s([cn], 'oveq1d', '( %s -> ( ( log ` -u V ) - %s ) = ( %s - %s ) )' % (A0, L, B, L))
pc = w.s([lc, ipc, w.inst('pncan2')], 'syl2anc', '( %s -> ( %s - %s ) = %s )' % (A0, B, L, IPI))
w.qed([o1, pc], 'eqtrd', '( %s -> ( ( log ` -u V ) - %s ) = %s )' % (A0, L, IPI)); run(w)

# ---- clogdif1: the jump above the real axis
w = W('clogdif1', 'Above the real axis the principal logarithm exceeds the logarithm of the negative by _i x. _pi.')
A0 = '( V e. CC /\\ 0 < ( Im ` V ) )'
LN = LOG('-u V'); B = '( %s + %s )' % (LN, IPI)
vc = w.s([], 'simpl', '( %s -> V e. CC )' % A0)
vgt = w.s([], 'simpr', '( %s -> 0 < ( Im ` V ) )' % A0)
imr = w.s([vc, w.inst('imcl')], 'syl', '( %s -> ( Im ` V ) e. RR )' % A0)
nvc = w.s([vc], 'negcld', '( %s -> -u V e. CC )' % A0)
lneg = w.s([imr], 'lt0neg2d', '( %s -> ( 0 < ( Im ` V ) <-> -u ( Im ` V ) < 0 ) )' % A0)
nlt = w.s([vgt, lneg], 'mpbid', '( %s -> -u ( Im ` V ) < 0 )' % A0)
imn = w.s([vc, w.inst('imneg')], 'syl', '( %s -> ( Im ` -u V ) = -u ( Im ` V ) )' % A0)
nlt2 = w.s([imn, nlt], 'eqbrtrd', '( %s -> ( Im ` -u V ) < 0 )' % A0)
cn = w.s([nvc, nlt2, w.inst('clogneg')], 'syl2anc', '( %s -> ( log ` -u -u V ) = %s )' % (A0, B))
nn = w.s([vc, w.inst('negneg')], 'syl', '( %s -> -u -u V = V )' % A0)
lv = w.s([w.s([nn], 'fveq2d', '( %s -> ( log ` -u -u V ) = ( log ` V ) )' % A0), cn], 'eqtr3d', '( %s -> ( log ` V ) = %s )' % (A0, B))
# closures for pncan2
nvne = w.s([nvc, w.s([nlt2, w.s([nvc, w.inst('imcl')], 'syl', '( %s -> ( Im ` -u V ) e. RR )' % A0)], 'jca',
           '( %s -> ( ( Im ` -u V ) < 0 /\\ ( Im ` -u V ) e. RR ) )' % A0)], 'jca',
           '( %s -> ( -u V e. CC /\\ ( ( Im ` -u V ) < 0 /\\ ( Im ` -u V ) e. RR ) ) )' % A0)
imnr = w.s([nvc, w.inst('imcl')], 'syl', '( %s -> ( Im ` -u V ) e. RR )' % A0)
nne0 = w.s([imnr, nlt2], 'ltned', '( %s -> ( Im ` -u V ) =/= 0 )' % A0)
i0 = w.s([], 'im0', '( Im ` 0 ) = 0')
fq = w.s([], 'fveq2', '( -u V = 0 -> ( Im ` -u V ) = ( Im ` 0 ) )')
gq = w.s([fq, i0], 'eqtrdi', '( -u V = 0 -> ( Im ` -u V ) = 0 )')
gqd = w.s([gq], 'a1i', '( %s -> ( -u V = 0 -> ( Im ` -u V ) = 0 ) )' % A0)
nvne2 = w.s([w.s([w.s([nne0], 'neneqd', '( %s -> -. ( Im ` -u V ) = 0 )' % A0), gqd], 'mtod',
            '( %s -> -. -u V = 0 )' % A0)], 'neqned', '( %s -> -u V =/= 0 )' % A0)
lnc = w.s([nvc, nvne2], 'logcld', '( %s -> %s e. CC )' % (A0, LN))
ic = closed(w, A0, 'ax-icn', '_i e. CC'); pic = closed(w, A0, 'picn', '_pi e. CC')
ipc = w.s([ic, pic], 'mulcld', '( %s -> %s e. CC )' % (A0, IPI))
o1 = w.s([lv], 'oveq1d', '( %s -> ( ( log ` V ) - %s ) = ( %s - %s ) )' % (A0, LN, B, LN))
pc = w.s([lnc, ipc, w.inst('pncan2')], 'syl2anc', '( %s -> ( %s - %s ) = %s )' % (A0, B, LN, IPI))
w.qed([o1, pc], 'eqtrd', '( %s -> ( ( log ` V ) - %s ) = %s )' % (A0, LN, IPI)); run(w)
