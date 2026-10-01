"""Sortie C2 section 3.3c: Phragmen-Lindelof at a fixed Gaussian parameter."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *
from lin import linarith

STR = '( `\' Re " ( X [,] Y ) )'
NQ = '( ( ( abs ` X ) + ( abs ` Y ) ) ^ 2 )'
LGK = '( log ` ( C / K ) )'
GT = '( ( L + ( abs ` %s ) ) / E )' % LGK
T1 = '( 1 + %s )' % GT
IW = '( Im ` W )'; RW = '( Re ` W )'
TT = '( %s + ( abs ` %s ) )' % (T1, IW)
LL = '( X + ( _i x. -u %s ) )' % TT
UR = '( Y + ( _i x. %s ) )' % TT


def GAU(Z):
    return '( exp ` ( E x. ( ( %s ^ 2 ) - %s ) ) )' % (Z, NQ)


GG = MP('z', 'D', '( ( F ` z ) x. %s )' % GAU('z'))
GAUM = MP('z', 'D', GAU('z'))
VV = '( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - %s )' % (RW, IW, NQ)
EDG1 = 'A. y e. %s ( ( Re ` y ) = X -> ( abs ` ( F ` y ) ) <_ C )' % STR
EDG2 = 'A. y e. %s ( ( Re ` y ) = Y -> ( abs ` ( F ` y ) ) <_ C )' % STR
GRW = 'A. y e. %s ( abs ` ( F ` y ) ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` y ) ) ) ) )' % STR
H1 = '( X e. RR /\\ Y e. RR )'
H2 = '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D )' % STR
H3 = '( C e. RR+ /\\ %s /\\ %s )' % (EDG1, EDG2)
H4 = '( ( K e. RR+ /\\ L e. RR /\\ 0 <_ L ) /\\ %s )' % GRW
H5 = '( W e. CC /\\ X < %s /\\ %s < Y )' % (RW, RW)
H6 = 'E e. RR+'
A0 = '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) )' % (H1, H2, H3, H4, H5, H6)

# frame of the auxiliary rectangle
FRT = FR.replace('A', '@A@').replace('B', '@B@').replace('@A@', LL).replace('@B@', UR)
# (the replace above would corrupt letters inside LL/UR; build it directly instead)
RLL = '( Re ` %s )' % LL; ILL = '( Im ` %s )' % LL
RUR = '( Re ` %s )' % UR; IUR = '( Im ` %s )' % UR
B1T = '( %s + ( _i x. %s ) )' % (RUR, ILL)
A1T = '( %s + ( _i x. %s ) )' % (RLL, IUR)
SEGT = ['( %s cseg %s )' % (LL, B1T), '( %s cseg %s )' % (B1T, UR),
        '( %s cseg %s )' % (UR, A1T), '( %s cseg %s )' % (A1T, LL)]
FRT = '( ( %s u. %s ) u. ( %s u. %s ) )' % tuple(SEGT)

w = W('rectintpl1', 'Phragmen-Lindelof on a vertical strip at a fixed Gaussian parameter: the modulus at an interior point is at most the edge bound times a Gaussian correction.')
h123 = w.s([], 'simpl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, H1, H2, H3))
h456 = w.s([], 'simpr', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, H4, H5, H6))
h1 = w.s([h123, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, H1))
h2 = w.s([h123, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, H2))
h3 = w.s([h123, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, H3))
h4 = w.s([h456, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, H4))
h5 = w.s([h456, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, H5))
erp = w.s([h456, w.inst('simp3')], 'syl', '( %s -> E e. RR+ )' % A0)
xr = w.s([h1, w.inst('simpl')], 'syl', '( %s -> X e. RR )' % A0)
yr = w.s([h1, w.inst('simpr')], 'syl', '( %s -> Y e. RR )' % A0)
fcn = w.s([h2, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dd = w.s([h2, w.inst('simp2')], 'syl', '( %s -> D C_ dom ( CC _D F ) )' % A0)
sd = w.s([h2, w.inst('simp3')], 'syl', '( %s -> %s C_ D )' % (A0, STR))
crp = w.s([h3, w.inst('simp1')], 'syl', '( %s -> C e. RR+ )' % A0)
ed1 = w.s([h3, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, EDG1))
ed2 = w.s([h3, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, EDG2))
klx = w.s([h4, w.inst('simpl')], 'syl', '( %s -> ( K e. RR+ /\\ L e. RR /\\ 0 <_ L ) )' % A0)
grw = w.s([h4, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, GRW))
krp = w.s([klx, w.inst('simp1')], 'syl', '( %s -> K e. RR+ )' % A0)
lr = w.s([klx, w.inst('simp2')], 'syl', '( %s -> L e. RR )' % A0)
l0 = w.s([klx, w.inst('simp3')], 'syl', '( %s -> 0 <_ L )' % A0)
wc = w.s([h5, w.inst('simp1')], 'syl', '( %s -> W e. CC )' % A0)
xw = w.s([h5, w.inst('simp2')], 'syl', '( %s -> X < %s )' % (A0, RW))
wy = w.s([h5, w.inst('simp3')], 'syl', '( %s -> %s < Y )' % (A0, RW))
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
cr = w.s([crp], 'rpred', '( %s -> C e. RR )' % A0)
kr = w.s([krp], 'rpred', '( %s -> K e. RR )' % A0)
rwr = w.s([wc], 'recld', '( %s -> %s e. RR )' % (A0, RW))
iwr = w.s([wc], 'imcld', '( %s -> %s e. RR )' % (A0, IW))
aiw = w.s([w.s([iwr], 'recnd', '( %s -> %s e. CC )' % (A0, IW))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, IW))
aiw0 = w.s([w.s([iwr], 'recnd', '( %s -> %s e. CC )' % (A0, IW))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, IW))
axr = w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % A0)], 'abscld', '( %s -> ( abs ` X ) e. RR )' % A0)
ayr = w.s([w.s([yr], 'recnd', '( %s -> Y e. CC )' % A0)], 'abscld', '( %s -> ( abs ` Y ) e. RR )' % A0)
nqr = w.s([w.s([axr, ayr], 'readdcld', '( %s -> ( ( abs ` X ) + ( abs ` Y ) ) e. RR )' % A0)], 'resqcld', '( %s -> %s e. RR )' % (A0, NQ))
nqc = w.s([nqr], 'recnd', '( %s -> %s e. CC )' % (A0, NQ))
ec_ = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
ckrp = w.s([crp, krp], 'rpdivcld', '( %s -> ( C / K ) e. RR+ )' % A0)
gkr = w.s([ckrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, LGK))
agk = w.s([w.s([gkr], 'recnd', '( %s -> %s e. CC )' % (A0, LGK))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, LGK))
agk0 = w.s([w.s([gkr], 'recnd', '( %s -> %s e. CC )' % (A0, LGK))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, LGK))
numr = w.s([lr, agk], 'readdcld', '( %s -> ( L + ( abs ` %s ) ) e. RR )' % (A0, LGK))
gtr = w.s([numr, erp], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, GT))
num0 = w.s([lr, agk, l0, agk0], 'addge0d', '( %s -> 0 <_ ( L + ( abs ` %s ) ) )' % (A0, LGK))
gt0 = w.s([w.s([numr, num0], 'jca',
                '( %s -> ( ( L + ( abs ` %s ) ) e. RR /\\ 0 <_ ( L + ( abs ` %s ) ) ) )' % (A0, LGK, LGK)),
            w.s([er, w.s([erp], 'rpgt0d', '( %s -> 0 < E )' % A0)], 'jca', '( %s -> ( E e. RR /\\ 0 < E ) )' % A0), w.inst('divge0')], 'syl2anc',
           '( %s -> 0 <_ %s )' % (A0, GT))
t1r = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), gtr], 'readdcld', '( %s -> %s e. RR )' % (A0, T1))
ttr = w.s([t1r, aiw], 'readdcld', '( %s -> %s e. RR )' % (A0, TT))
one_r = w.s([], '1red', '( %s -> 1 e. RR )' % A0)
le11 = w.s([gt0, w.s([one_r, gtr, w.inst('addge01')], 'syl2anc', '( %s -> ( 0 <_ %s <-> 1 <_ %s ) )' % (A0, GT, T1))], 'mpbid', '( %s -> 1 <_ %s )' % (A0, T1))
le12 = w.s([aiw0, w.s([t1r, aiw, w.inst('addge01')], 'syl2anc', '( %s -> ( 0 <_ ( abs ` %s ) <-> %s <_ %s ) )' % (A0, IW, T1, TT))], 'mpbid', '( %s -> %s <_ %s )' % (A0, T1, TT))
t1le = w.s([one_r, t1r, ttr, le11, le12], 'letrd', '( %s -> 1 <_ %s )' % (A0, TT))
gt1 = w.s([w.s([], '0le1', '0 <_ 1'), w.s([gtr, one_r, w.inst('addge02')], 'syl2anc', '( %s -> ( 0 <_ 1 <-> %s <_ %s ) )' % (A0, GT, T1))], 'mpbii',
          '( %s -> %s <_ %s )' % (A0, GT, T1)) if False else w.s(
    [w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A0),
     w.s([gtr, one_r, w.inst('addge02')], 'syl2anc', '( %s -> ( 0 <_ 1 <-> %s <_ %s ) )' % (A0, GT, T1))], 'mpbid', '( %s -> %s <_ %s )' % (A0, GT, T1))
tgt = w.s([gtr, t1r, ttr, gt1, le12], 'letrd', '( %s -> %s <_ %s )' % (A0, GT, TT))
aiw1r = w.s([aiw, one_r], 'readdcld', '( %s -> ( ( abs ` %s ) + 1 ) e. RR )' % (A0, IW))
lt1 = w.s([aiw], 'ltp1d', '( %s -> ( abs ` %s ) < ( ( abs ` %s ) + 1 ) )' % (A0, IW, IW))
lt2 = w.s([le11, w.s([one_r, t1r, aiw], 'leadd2d', '( %s -> ( 1 <_ %s <-> ( ( abs ` %s ) + 1 ) <_ ( ( abs ` %s ) + %s ) ) )' % (A0, T1, IW, IW, T1))], 'mpbid',
          '( %s -> ( ( abs ` %s ) + 1 ) <_ ( ( abs ` %s ) + %s ) )' % (A0, IW, IW, T1))
lt3 = w.s([lt2, w.s([w.s([aiw], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (A0, IW)), w.s([t1r], 'recnd', '( %s -> %s e. CC )' % (A0, T1))], 'addcomd',
                    '( %s -> ( ( abs ` %s ) + %s ) = %s )' % (A0, IW, T1, TT))], 'breqtrd', '( %s -> ( ( abs ` %s ) + 1 ) <_ %s )' % (A0, IW, TT))
awlt = w.s([aiw, aiw1r, ttr, lt1, lt3], 'ltletrd', '( %s -> ( abs ` %s ) < %s )' % (A0, IW, TT))
t0A0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), one_r, ttr, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A0), t1le], 'letrd',
           '( %s -> 0 <_ %s )' % (A0, TT))
sumle = w.s([tgt, w.s([numr, ttr, w.s([er, w.s([erp], 'rpgt0d', '( %s -> 0 < E )' % A0)], 'jca', '( %s -> ( E e. RR /\\ 0 < E ) )' % A0), w.inst('ledivmul')], 'syl3anc',
                      '( %s -> ( %s <_ %s <-> ( L + ( abs ` %s ) ) <_ ( E x. %s ) ) )' % (A0, GT, TT, LGK, TT))], 'mpbid',
            '( %s -> ( L + ( abs ` %s ) ) <_ ( E x. %s ) )' % (A0, LGK, TT))
imb = w.s([awlt, w.s([iwr, ttr, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` %s ) < %s <-> ( -u %s < %s /\\ %s < %s ) ) )' % (A0, IW, TT, TT, IW, IW, TT))],
          'mpbid', '( %s -> ( -u %s < %s /\\ %s < %s ) )' % (A0, TT, IW, IW, TT))
imlo = w.s([imb, w.inst('simpl')], 'syl', '( %s -> -u %s < %s )' % (A0, TT, IW))
imhi = w.s([imb, w.inst('simpr')], 'syl', '( %s -> %s < %s )' % (A0, IW, TT))
# rectangle corners
nttr = w.s([ttr], 'renegcld', '( %s -> -u %s e. RR )' % (A0, TT))
ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
llc = w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % A0), w.s([ic, w.s([nttr], 'recnd', '( %s -> -u %s e. CC )' % (A0, TT))], 'mulcld', '( %s -> ( _i x. -u %s ) e. CC )' % (A0, TT))], 'addcld', '( %s -> %s e. CC )' % (A0, LL))
urc = w.s([w.s([yr], 'recnd', '( %s -> Y e. CC )' % A0), w.s([ic, w.s([ttr], 'recnd', '( %s -> %s e. CC )' % (A0, TT))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, TT))], 'addcld', '( %s -> %s e. CC )' % (A0, UR))
rll = w.s([xr, nttr, w.inst('crre')], 'syl2anc', '( %s -> %s = X )' % (A0, RLL))
ill = w.s([xr, nttr, w.inst('crim')], 'syl2anc', '( %s -> %s = -u %s )' % (A0, ILL, TT))
rur = w.s([yr, ttr, w.inst('crre')], 'syl2anc', '( %s -> %s = Y )' % (A0, RUR))
iur = w.s([yr, ttr, w.inst('crim')], 'syl2anc', '( %s -> %s = %s )' % (A0, IUR, TT))
abt = w.s([llc, urc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, LL, UR))
xy = w.s([xr, rwr, yr, xw, wy], 'lttrd', '( %s -> X < Y )' % A0)
geo1 = w.s([w.s([w.s([rll], 'eqcomd', '( %s -> X = %s )' % (A0, RLL)), w.s([rur], 'eqcomd', '( %s -> Y = %s )' % (A0, RUR))], 'breq12d',
                '( %s -> ( X <_ Y <-> %s <_ %s ) )' % (A0, RLL, RUR))], 'mpbid', '( %s -> %s <_ %s )' % (A0, RLL, RUR)) if False else None
xyle = w.s([xy], 'ltled', '( %s -> X <_ Y )' % A0)
g1 = w.s([xyle, w.s([rll, rur], 'breq12d', '( %s -> ( %s <_ %s <-> X <_ Y ) )' % (A0, RLL, RUR))], 'mpbird', '( %s -> %s <_ %s )' % (A0, RLL, RUR))
neg0d = w.s([w.s([], 'neg0', '-u 0 = 0')], 'a1i', '( %s -> -u 0 = 0 )' % A0)
nlt = w.s([t0A0, w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), ttr], 'lenegd', '( %s -> ( 0 <_ %s <-> -u %s <_ -u 0 ) )' % (A0, TT, TT))], 'mpbid',
          '( %s -> -u %s <_ -u 0 )' % (A0, TT))
nlt2 = w.s([nlt, neg0d], 'breqtrd', '( %s -> -u %s <_ 0 )' % (A0, TT))
nttle = w.s([nttr, w.s([], '0red', '( %s -> 0 e. RR )' % A0), ttr, nlt2, t0A0], 'letrd', '( %s -> -u %s <_ %s )' % (A0, TT, TT))
g2 = w.s([nttle, w.s([ill, iur], 'breq12d', '( %s -> ( %s <_ %s <-> -u %s <_ %s ) )' % (A0, ILL, IUR, TT, TT))], 'mpbird', '( %s -> %s <_ %s )' % (A0, ILL, IUR))
geot = w.s([g1, g2], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A0, RLL, RUR, ILL, IUR))
# W is strictly interior
i1 = w.s([xw, w.s([rll], 'breq1d', '( %s -> ( %s < %s <-> X < %s ) )' % (A0, RLL, RW, RW))], 'mpbird', '( %s -> %s < %s )' % (A0, RLL, RW))
i2 = w.s([wy, w.s([rur], 'breq2d', '( %s -> ( %s < %s <-> %s < Y ) )' % (A0, RW, RUR, RW))], 'mpbird', '( %s -> %s < %s )' % (A0, RW, RUR))
i3 = w.s([imlo, w.s([ill], 'breq1d', '( %s -> ( %s < %s <-> -u %s < %s ) )' % (A0, ILL, IW, TT, IW))], 'mpbird', '( %s -> %s < %s )' % (A0, ILL, IW))
i4 = w.s([imhi, w.s([iur], 'breq2d', '( %s -> ( %s < %s <-> %s < %s ) )' % (A0, IW, IUR, IW, TT))], 'mpbird', '( %s -> %s < %s )' % (A0, IW, IUR))
intw = w.s([wc, w.s([w.s([i1, i2], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (A0, RLL, RW, RW, RUR)),
                     w.s([i3, i4], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (A0, ILL, IW, IW, IUR))], 'jca',
                    '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RLL, RW, RW, RUR, ILL, IW, IW, IUR))], 'jca',
           '( %s -> ( W e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) ) )' % (A0, RLL, RW, RW, RUR, ILL, IW, IW, IUR))
# the rectangle lies in the strip, hence in D
rst = w.s([xr, yr, ttr, w.inst('crectstr')], 'syl3anc', '( %s -> ( %s crect %s ) C_ %s )' % (A0, LL, UR, STR))
rdd = w.s([rst, sd], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A0, LL, UR))
# holomorphy of the normalised function
hl = w.s([fcn, dd], 'jca', '( %s -> %s )' % (A0, HOL))
dop = w.s([hl, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
hg = w.s([dop, dcc, w.s([ec_, nqc], 'jca', '( %s -> ( E e. CC /\\ %s e. CC ) )' % (A0, NQ)), w.inst('holgau')], 'syl3anc',
         '( %s -> %s )' % (A0, HOLG(GAUM)))
AZ = '( %s /\\ z e. D )' % A0
ff0 = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fmpt = w.s([ff0], 'feqmptd', '( %s -> F = %s )' % (A0, MP('z', 'D', '( F ` z )')))
fmp = w.s([fmpt, fcn], 'eqeltrrd', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MP('z', 'D', '( F ` z )')))
gcn = w.s([ec_, nqc, dcc, w.inst('gaucn')], 'syl3anc', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GAUM))
ej2 = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn = w.s([w.s([ej2], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
ggcn = w.s([ej2, mcn, fmp, gcn], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GG))
cnel2 = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
zdz = w.s([], 'simpr', '( %s -> z e. D )' % AZ)
fzc = w.s([w.s([ff0], 'adantr', '( %s -> F : D --> CC )' % AZ), zdz], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % AZ)
dvfd = w.s([hl, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % A0)
dfzc = w.s([w.s([dvfd], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % AZ), zdz], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` z ) e. CC )' % AZ)
hdv = w.s([hl, w.inst('holdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, MP('z', 'D', '( F ` z )'), MP('z', 'D', '( ( CC _D F ) ` z )')))
zcz = w.s([w.s([dcc], 'adantr', '( %s -> D C_ CC )' % AZ), zdz], 'sseldd', '( %s -> z e. CC )' % AZ)
argz = w.s([w.s([ec_], 'adantr', '( %s -> E e. CC )' % AZ),
            w.s([w.s([zcz], 'sqcld', '( %s -> ( z ^ 2 ) e. CC )' % AZ), w.s([nqc], 'adantr', '( %s -> %s e. CC )' % (AZ, NQ))], 'subcld',
                '( %s -> ( ( z ^ 2 ) - %s ) e. CC )' % (AZ, NQ))], 'mulcld', '( %s -> ( E x. ( ( z ^ 2 ) - %s ) ) e. CC )' % (AZ, NQ))
gauzc = w.s([argz, w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (AZ, GAU('z')))
DRHS = '( %s x. ( E x. ( 2 x. z ) ) )' % GAU('z')
drhsc = w.s([gauzc, w.s([w.s([ec_], 'adantr', '( %s -> E e. CC )' % AZ),
                         w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % AZ), zcz], 'mulcld', '( %s -> ( 2 x. z ) e. CC )' % AZ)], 'mulcld',
                        '( %s -> ( E x. ( 2 x. z ) ) e. CC )' % AZ)], 'mulcld', '( %s -> %s e. CC )' % (AZ, DRHS))
dgau = w.s([dop, dcc, w.s([ec_, nqc], 'jca', '( %s -> ( E e. CC /\\ %s e. CC ) )' % (A0, NQ)), w.inst('dvgaud')], 'syl3anc',
           '( %s -> ( CC _D %s ) = %s )' % (A0, GAUM, MP('z', 'D', DRHS)))
MRHS = '( ( ( ( CC _D F ) ` z ) x. %s ) + ( %s x. ( F ` z ) ) )' % (GAU('z'), DRHS)
dvgg = w.s([cnel2, fzc, dfzc, hdv, gauzc, drhsc, dgau], 'dvmptmul', '( %s -> ( CC _D %s ) = %s )' % (A0, GG, MP('z', 'D', MRHS)))
mrhsc = w.s([w.s([dfzc, gauzc], 'mulcld', '( %s -> ( ( ( CC _D F ) ` z ) x. %s ) e. CC )' % (AZ, GAU('z'))),
             w.s([drhsc, fzc], 'mulcld', '( %s -> ( %s x. ( F ` z ) ) e. CC )' % (AZ, DRHS))], 'addcld', '( %s -> %s e. CC )' % (AZ, MRHS))
ggd = dvdom(w, A0, GG, 'z', 'D', MRHS, dvgg, mrhsc)
hgm = w.s([ggcn, ggd], 'jca', '( %s -> %s )' % (A0, HOLG(GG)))
hoG = w.s([hgm, rdd, w.inst('holcrect')], 'syl2anc', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ dom ( CC _D %s ) ) )' % (A0, GG, LL, UR, GG))
# ---- the frame bound -------------------------------------------------------
A1 = '( %s /\\ v e. %s )' % (A0, FRT)


def lf(st, form):
    return w.s([st], 'adantr', '( %s -> %s )' % (A1, form))


vf = w.s([], 'simpr', '( %s -> v e. %s )' % (A1, FRT))
fru = w.s([abt, geot, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( %s crect %s ) )' % (A0, FRT, LL, UR))
vr_ = w.s([lf(fru, '%s C_ ( %s crect %s )' % (FRT, LL, UR)), vf], 'sseldd', '( %s -> v e. ( %s crect %s ) )' % (A1, LL, UR))
vst = w.s([lf(rst, '( %s crect %s ) C_ %s' % (LL, UR, STR)), vr_], 'sseldd', '( %s -> v e. %s )' % (A1, STR))
vd = w.s([lf(rdd, '( %s crect %s ) C_ D' % (LL, UR)), vr_], 'sseldd', '( %s -> v e. D )' % A1)
vel = w.s([vst, w.s([w.s([], 'elstr', '( v e. %s <-> ( v e. CC /\\ ( Re ` v ) e. ( X [,] Y ) ) )' % STR)], 'a1i',
                    '( %s -> ( v e. %s <-> ( v e. CC /\\ ( Re ` v ) e. ( X [,] Y ) ) ) )' % (A1, STR))], 'mpbid',
          '( %s -> ( v e. CC /\\ ( Re ` v ) e. ( X [,] Y ) ) )' % A1)
vc = w.s([vel, w.inst('simpl')], 'syl', '( %s -> v e. CC )' % A1)
vxy = w.s([vel, w.inst('simpr')], 'syl', '( %s -> ( Re ` v ) e. ( X [,] Y ) )' % A1)
vic = w.s([vxy, w.s([lf(xr, 'X e. RR'), lf(yr, 'Y e. RR'), w.inst('elicc2')], 'syl2anc',
                    '( %s -> ( ( Re ` v ) e. ( X [,] Y ) <-> ( ( Re ` v ) e. RR /\\ X <_ ( Re ` v ) /\\ ( Re ` v ) <_ Y ) ) )' % A1)], 'mpbid',
          '( %s -> ( ( Re ` v ) e. RR /\\ X <_ ( Re ` v ) /\\ ( Re ` v ) <_ Y ) )' % A1)
vrr = w.s([vic, w.inst('simp1')], 'syl', '( %s -> ( Re ` v ) e. RR )' % A1)
vlo = w.s([vic, w.inst('simp2')], 'syl', '( %s -> X <_ ( Re ` v ) )' % A1)
vhi = w.s([vic, w.inst('simp3')], 'syl', '( %s -> ( Re ` v ) <_ Y )' % A1)
sqle = w.s([w.s([lf(xr, 'X e. RR'), lf(yr, 'Y e. RR'), vrr], '3jca', '( %s -> ( X e. RR /\\ Y e. RR /\\ ( Re ` v ) e. RR ) )' % A1),
            w.s([vlo, vhi], 'jca', '( %s -> ( X <_ ( Re ` v ) /\\ ( Re ` v ) <_ Y ) )' % A1), w.inst('sqleabs2')], 'syl2anc',
           '( %s -> ( ( Re ` v ) ^ 2 ) <_ %s )' % (A1, NQ))
subv = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )'),
            w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z ^ 2 ) = ( v ^ 2 ) )')], 'oveq1d', '( z = v -> ( ( z ^ 2 ) - %s ) = ( ( v ^ 2 ) - %s ) )' % (NQ, NQ))], 'oveq2d',
                '( z = v -> ( E x. ( ( z ^ 2 ) - %s ) ) = ( E x. ( ( v ^ 2 ) - %s ) ) )' % (NQ, NQ))], 'idi', 'dummy') if False else None
sv1 = w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')
sv2 = w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z ^ 2 ) = ( v ^ 2 ) )')], 'oveq1d', '( z = v -> ( ( z ^ 2 ) - %s ) = ( ( v ^ 2 ) - %s ) )' % (NQ, NQ))], 'oveq2d',
           '( z = v -> ( E x. ( ( z ^ 2 ) - %s ) ) = ( E x. ( ( v ^ 2 ) - %s ) ) )' % (NQ, NQ))
sv3 = w.s([sv2], 'fveq2d', '( z = v -> %s = %s )' % (GAU('z'), GAU('v')))
subv = w.s([sv1, sv3], 'oveq12d', '( z = v -> ( ( F ` z ) x. %s ) = ( ( F ` v ) x. %s ) )' % (GAU('z'), GAU('v')))
gvv = mptval(w, A1, 'z', 'D', GG, 'v', '( ( F ` v ) x. %s )' % GAU('v'), subv, vd)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fvc = w.s([lf(ff, 'F : D --> CC'), vd], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A1)
# the coordinate disjunction on the frame
DISJT = '( ( ( Re ` v ) = %s \\/ ( Re ` v ) = %s ) \\/ ( ( Im ` v ) = %s \\/ ( Im ` v ) = %s ) )' % (RLL, RUR, ILL, IUR)
DISJ2 = '( ( ( Re ` v ) = X \\/ ( Re ` v ) = Y ) \\/ ( ( Im ` v ) = -u %s \\/ ( Im ` v ) = %s ) )' % (TT, TT)
fre = w.s([abt, geot, w.inst('crectfre')], 'syl2anc', '( %s -> A. u e. %s %s )' % (A0, FRT, DISJT.replace('( Re ` v )', '( Re ` u )').replace('( Im ` v )', '( Im ` u )')))
cbvs = w.s([w.s([w.s([w.s([], 'fveq2', '( u = v -> ( Re ` u ) = ( Re ` v ) )')], 'eqeq1d', '( u = v -> ( ( Re ` u ) = %s <-> ( Re ` v ) = %s ) )' % (RLL, RLL)),
                 w.s([w.s([], 'fveq2', '( u = v -> ( Re ` u ) = ( Re ` v ) )')], 'eqeq1d', '( u = v -> ( ( Re ` u ) = %s <-> ( Re ` v ) = %s ) )' % (RUR, RUR))], 'orbi12d',
                '( u = v -> ( ( ( Re ` u ) = %s \\/ ( Re ` u ) = %s ) <-> ( ( Re ` v ) = %s \\/ ( Re ` v ) = %s ) ) )' % (RLL, RUR, RLL, RUR)),
            w.s([w.s([w.s([], 'fveq2', '( u = v -> ( Im ` u ) = ( Im ` v ) )')], 'eqeq1d', '( u = v -> ( ( Im ` u ) = %s <-> ( Im ` v ) = %s ) )' % (ILL, ILL)),
                 w.s([w.s([], 'fveq2', '( u = v -> ( Im ` u ) = ( Im ` v ) )')], 'eqeq1d', '( u = v -> ( ( Im ` u ) = %s <-> ( Im ` v ) = %s ) )' % (IUR, IUR))], 'orbi12d',
                '( u = v -> ( ( ( Im ` u ) = %s \\/ ( Im ` u ) = %s ) <-> ( ( Im ` v ) = %s \\/ ( Im ` v ) = %s ) ) )' % (ILL, IUR, ILL, IUR))], 'orbi12d',
           '( u = v -> ( %s <-> %s ) )' % (DISJT.replace('( Re ` v )', '( Re ` u )').replace('( Im ` v )', '( Im ` u )'), DISJT))
dsj = w.s([cbvs, lf(fre, 'A. u e. %s %s' % (FRT, DISJT.replace('( Re ` v )', '( Re ` u )').replace('( Im ` v )', '( Im ` u )'))), vf], 'rspcdva',
          '( %s -> %s )' % (A1, DISJT))
dsj2 = w.s([dsj, w.s([w.s([w.s([lf(rll, '%s = X' % RLL)], 'eqeq2d', '( %s -> ( ( Re ` v ) = %s <-> ( Re ` v ) = X ) )' % (A1, RLL)),
                           w.s([lf(rur, '%s = Y' % RUR)], 'eqeq2d', '( %s -> ( ( Re ` v ) = %s <-> ( Re ` v ) = Y ) )' % (A1, RUR))], 'orbi12d',
                          '( %s -> ( ( ( Re ` v ) = %s \\/ ( Re ` v ) = %s ) <-> ( ( Re ` v ) = X \\/ ( Re ` v ) = Y ) ) )' % (A1, RLL, RUR)),
                      w.s([w.s([lf(ill, '%s = -u %s' % (ILL, TT))], 'eqeq2d', '( %s -> ( ( Im ` v ) = %s <-> ( Im ` v ) = -u %s ) )' % (A1, ILL, TT)),
                           w.s([lf(iur, '%s = %s' % (IUR, TT))], 'eqeq2d', '( %s -> ( ( Im ` v ) = %s <-> ( Im ` v ) = %s ) )' % (A1, IUR, TT))], 'orbi12d',
                          '( %s -> ( ( ( Im ` v ) = %s \\/ ( Im ` v ) = %s ) <-> ( ( Im ` v ) = -u %s \\/ ( Im ` v ) = %s ) ) )' % (A1, ILL, IUR, TT, TT))], 'orbi12d',
                     '( %s -> ( %s <-> %s ) )' % (A1, DISJT, DISJ2))], 'mpbid', '( %s -> %s )' % (A1, DISJ2))

# ---- the four cases --------------------------------------------------------
GAV = GAU('v')
FV = '( F ` v )'
TGT = '( abs ` ( %s x. %s ) ) <_ C' % (FV, GAV)
base3 = w.s([vc, lf(erp, 'E e. RR+'), lf(nqr, '%s e. RR' % NQ)], '3jca', '( %s -> ( v e. CC /\\ E e. RR+ /\\ %s e. RR ) )' % (A1, NQ))
t0 = lf(t0A0, '0 <_ %s' % TT)
ttrA = lf(ttr, '%s e. RR' % TT)


def edgecase(eqstep, ante, edg, edgf, val):
    sub = w.s([w.s([w.s([], 'fveq2', '( y = v -> ( Re ` y ) = ( Re ` v ) )')], 'eqeq1d', '( y = v -> ( ( Re ` y ) = %s <-> ( Re ` v ) = %s ) )' % (val, val)),
               w.s([w.s([w.s([], 'fveq2', '( y = v -> ( F ` y ) = %s )' % FV)], 'fveq2d', '( y = v -> ( abs ` ( F ` y ) ) = ( abs ` %s ) )' % FV)], 'breq1d',
                   '( y = v -> ( ( abs ` ( F ` y ) ) <_ C <-> ( abs ` %s ) <_ C ) )' % FV)], 'imbi12d',
              '( y = v -> ( ( ( Re ` y ) = %s -> ( abs ` ( F ` y ) ) <_ C ) <-> ( ( Re ` v ) = %s -> ( abs ` %s ) <_ C ) ) )' % (val, val, FV))
    ins = w.s([sub, w.s([lf(edg, edgf)], 'adantr', '( %s -> %s )' % (ante, edgf)),
               w.s([vst], 'adantr', '( %s -> v e. %s )' % (ante, STR))], 'rspcdva',
              '( %s -> ( ( Re ` v ) = %s -> ( abs ` %s ) <_ C ) )' % (ante, val, FV))
    bnd = w.s([ins, eqstep], 'mpd', '( %s -> ( abs ` %s ) <_ C )' % (ante, FV))
    p1 = w.s([base3], 'adantr', '( %s -> ( v e. CC /\\ E e. RR+ /\\ %s e. RR ) )' % (ante, NQ))
    p2 = w.s([w.s([sqle], 'adantr', '( %s -> ( ( Re ` v ) ^ 2 ) <_ %s )' % (ante, NQ)),
              w.s([fvc], 'adantr', '( %s -> %s e. CC )' % (ante, FV))], 'jca',
             '( %s -> ( ( ( Re ` v ) ^ 2 ) <_ %s /\\ %s e. CC ) )' % (ante, NQ, FV))
    p3 = w.s([w.s([w.s([cr], 'adantr', '( %s -> C e. RR )' % A1)], 'adantr', '( %s -> C e. RR )' % ante), bnd], 'jca',
             '( %s -> ( C e. RR /\\ ( abs ` %s ) <_ C ) )' % (ante, FV))
    return w.s([p1, p2, p3, w.inst('plbndv')], 'syl3anc', '( %s -> %s )' % (ante, TGT))


CV1 = '( %s /\\ ( Re ` v ) = X )' % A1
CV2 = '( %s /\\ ( Re ` v ) = Y )' % A1
cv1 = edgecase(w.s([], 'simpr', '( %s -> ( Re ` v ) = X )' % CV1), CV1, ed1, EDG1, 'X')
cv2 = edgecase(w.s([], 'simpr', '( %s -> ( Re ` v ) = Y )' % CV2), CV2, ed2, EDG2, 'Y')
GH = '( K x. ( exp ` ( L x. %s ) ) )' % TT


def horiz(ante, sqeq, abseq):
    subg = w.s([w.s([w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = %s )' % FV)], 'fveq2d', '( z = v -> ( abs ` ( F ` z ) ) = ( abs ` %s ) )' % FV)], 'breq1d',
                    '( z = v -> ( ( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` z ) ) ) ) ) <-> ( abs ` %s ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` z ) ) ) ) ) ) )' % FV),
                w.s([w.s([w.s([w.s([], 'fveq2', '( z = v -> ( Im ` z ) = ( Im ` v ) )')], 'fveq2d', '( z = v -> ( abs ` ( Im ` z ) ) = ( abs ` ( Im ` v ) ) )')], 'oveq2d',
                         '( z = v -> ( L x. ( abs ` ( Im ` z ) ) ) = ( L x. ( abs ` ( Im ` v ) ) ) )')], 'idi', 'd')], 'idi', 'dd') if False else None
    s1 = w.s([w.s([], 'fveq2', '( y = v -> ( F ` y ) = %s )' % FV)], 'fveq2d', '( y = v -> ( abs ` ( F ` y ) ) = ( abs ` %s ) )' % FV)
    s2 = w.s([w.s([w.s([], 'fveq2', '( y = v -> ( Im ` y ) = ( Im ` v ) )')], 'fveq2d', '( y = v -> ( abs ` ( Im ` y ) ) = ( abs ` ( Im ` v ) ) )')], 'oveq2d',
              '( y = v -> ( L x. ( abs ` ( Im ` y ) ) ) = ( L x. ( abs ` ( Im ` v ) ) ) )')
    s3 = w.s([w.s([s2], 'fveq2d', '( y = v -> ( exp ` ( L x. ( abs ` ( Im ` y ) ) ) ) = ( exp ` ( L x. ( abs ` ( Im ` v ) ) ) ) )')], 'oveq2d',
              '( y = v -> ( K x. ( exp ` ( L x. ( abs ` ( Im ` y ) ) ) ) ) = ( K x. ( exp ` ( L x. ( abs ` ( Im ` v ) ) ) ) ) )')
    sub = w.s([s1, s3], 'breq12d',
              '( y = v -> ( ( abs ` ( F ` y ) ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` y ) ) ) ) ) <-> ( abs ` %s ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` v ) ) ) ) ) ) )' % FV)
    ins = w.s([sub, w.s([lf(grw, GRW)], 'adantr', '( %s -> %s )' % (ante, GRW)), w.s([vst], 'adantr', '( %s -> v e. %s )' % (ante, STR))], 'rspcdva',
              '( %s -> ( abs ` %s ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` v ) ) ) ) ) )' % (ante, FV))
    gbnd = w.s([ins, w.s([w.s([w.s([abseq], 'oveq2d', '( %s -> ( L x. ( abs ` ( Im ` v ) ) ) = ( L x. %s ) )' % (ante, TT))], 'fveq2d',
                              '( %s -> ( exp ` ( L x. ( abs ` ( Im ` v ) ) ) ) = ( exp ` ( L x. %s ) ) )' % (ante, TT))], 'oveq2d',
                         '( %s -> ( K x. ( exp ` ( L x. ( abs ` ( Im ` v ) ) ) ) ) = %s )' % (ante, GH))], 'breqtrd',
               '( %s -> ( abs ` %s ) <_ %s )' % (ante, FV, GH))
    ghr = w.s([w.s([w.s([kr], 'adantr', '( %s -> K e. RR )' % A1)], 'adantr', '( %s -> K e. RR )' % ante),
               w.s([w.s([w.s([w.s([lr], 'adantr', '( %s -> L e. RR )' % A1)], 'adantr', '( %s -> L e. RR )' % ante),
                         w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (ante, TT))], 'remulcld', '( %s -> ( L x. %s ) e. RR )' % (ante, TT)),
                    w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( L x. %s ) ) e. RR )' % (ante, TT))], 'remulcld', '( %s -> %s e. RR )' % (ante, GH))
    p1 = w.s([base3], 'adantr', '( %s -> ( v e. CC /\\ E e. RR+ /\\ %s e. RR ) )' % (ante, NQ))
    p2 = w.s([w.s([sqle], 'adantr', '( %s -> ( ( Re ` v ) ^ 2 ) <_ %s )' % (ante, NQ)), sqeq,
              w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (ante, TT))], '3jca',
             '( %s -> ( ( ( Re ` v ) ^ 2 ) <_ %s /\\ ( ( Im ` v ) ^ 2 ) = ( %s ^ 2 ) /\\ %s e. RR ) )' % (ante, NQ, TT, TT))
    p3 = w.s([w.s([fvc], 'adantr', '( %s -> %s e. CC )' % (ante, FV)), ghr, gbnd], '3jca',
             '( %s -> ( %s e. CC /\\ %s e. RR /\\ ( abs ` %s ) <_ %s ) )' % (ante, FV, GH, FV, GH))
    hb = w.s([p1, p2, p3, w.inst('plbndh')], 'syl3anc', '( %s -> ( abs ` ( %s x. %s ) ) <_ ( %s x. ( exp ` -u ( E x. ( %s ^ 2 ) ) ) ) )' % (ante, FV, GAV, GH, TT))
    pn = w.s([w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % A1)], 'adantr', '( %s -> K e. RR+ )' % ante),
                   w.s([w.s([crp], 'adantr', '( %s -> C e. RR+ )' % A1)], 'adantr', '( %s -> C e. RR+ )' % ante),
                   w.s([w.s([erp], 'adantr', '( %s -> E e. RR+ )' % A1)], 'adantr', '( %s -> E e. RR+ )' % ante)], '3jca',
                  '( %s -> ( K e. RR+ /\\ C e. RR+ /\\ E e. RR+ ) )' % ante),
              w.s([w.s([w.s([w.s([lr], 'adantr', '( %s -> L e. RR )' % A1)], 'adantr', '( %s -> L e. RR )' % ante),
                        w.s([w.s([l0], 'adantr', '( %s -> 0 <_ L )' % A1)], 'adantr', '( %s -> 0 <_ L )' % ante),
                        w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (ante, TT))], '3jca',
                       '( %s -> ( L e. RR /\\ 0 <_ L /\\ %s e. RR ) )' % (ante, TT))], 'idi', '( %s -> ( L e. RR /\\ 0 <_ L /\\ %s e. RR ) )' % (ante, TT)),
              w.s([w.s([w.s([w.s([t1le], 'adantr', '( %s -> 1 <_ %s )' % (A1, TT))], 'adantr', '( %s -> 1 <_ %s )' % (ante, TT)),
                        w.s([w.s([sumle], 'adantr', '( %s -> ( L + ( abs ` %s ) ) <_ ( E x. %s ) )' % (A1, LGK, TT))], 'adantr',
                            '( %s -> ( L + ( abs ` %s ) ) <_ ( E x. %s ) )' % (ante, LGK, TT))], 'jca',
                       '( %s -> ( 1 <_ %s /\\ ( L + ( abs ` %s ) ) <_ ( E x. %s ) ) )' % (ante, TT, LGK, TT))], 'idi',
                  '( %s -> ( 1 <_ %s /\\ ( L + ( abs ` %s ) ) <_ ( E x. %s ) ) )' % (ante, TT, LGK, TT)),
              w.inst('plnum')], 'syl3anc', '( %s -> ( %s x. ( exp ` -u ( E x. ( %s ^ 2 ) ) ) ) <_ C )' % (ante, GH, TT))
    eac = w.s([w.s([w.s([w.s([ec_], 'adantr', '( %s -> E e. CC )' % A1)], 'adantr', '( %s -> E e. CC )' % ante),
                    w.s([w.s([w.s([w.s([vc], 'adantr', '( %s -> v e. CC )' % ante)], 'sqcld', '( %s -> ( v ^ 2 ) e. CC )' % ante),
                             w.s([w.s([nqc], 'adantr', '( %s -> %s e. CC )' % (A1, NQ))], 'adantr', '( %s -> %s e. CC )' % (ante, NQ))], 'subcld',
                             '( %s -> ( ( v ^ 2 ) - %s ) e. CC )' % (ante, NQ))], 'idi', '( %s -> ( ( v ^ 2 ) - %s ) e. CC )' % (ante, NQ))], 'mulcld',
                   '( %s -> ( E x. ( ( v ^ 2 ) - %s ) ) e. CC )' % (ante, NQ)), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (ante, GAV))
    prd = w.s([w.s([w.s([fvc], 'adantr', '( %s -> %s e. CC )' % (ante, FV)), eac], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (ante, FV, GAV))], 'abscld',
              '( %s -> ( abs ` ( %s x. %s ) ) e. RR )' % (ante, FV, GAV))
    et2 = w.s([w.s([w.s([w.s([er], 'adantr', '( %s -> E e. RR )' % A1)], 'adantr', '( %s -> E e. RR )' % ante),
                    w.s([w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (ante, TT))], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (ante, TT))], 'remulcld',
                   '( %s -> ( E x. ( %s ^ 2 ) ) e. RR )' % (ante, TT))], 'renegcld', '( %s -> -u ( E x. ( %s ^ 2 ) ) e. RR )' % (ante, TT))
    mid = w.s([ghr, w.s([et2, w.inst('reefcl')], 'syl', '( %s -> ( exp ` -u ( E x. ( %s ^ 2 ) ) ) e. RR )' % (ante, TT))], 'remulcld',
              '( %s -> ( %s x. ( exp ` -u ( E x. ( %s ^ 2 ) ) ) ) e. RR )' % (ante, GH, TT))
    return w.s([prd, mid, w.s([w.s([w.s([cr], 'adantr', '( %s -> C e. RR )' % A1)], 'adantr', '( %s -> C e. RR )' % ante)], 'idi', '( %s -> C e. RR )' % ante), hb, pn],
               'letrd', '( %s -> %s )' % (ante, TGT))


CH1 = '( %s /\\ ( Im ` v ) = -u %s )' % (A1, TT)
CH2 = '( %s /\\ ( Im ` v ) = %s )' % (A1, TT)
e1 = w.s([], 'simpr', '( %s -> ( Im ` v ) = -u %s )' % (CH1, TT))
sq1 = w.s([w.s([e1], 'oveq1d', '( %s -> ( ( Im ` v ) ^ 2 ) = ( -u %s ^ 2 ) )' % (CH1, TT)),
           w.s([w.s([w.s([w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (CH1, TT))], 'recnd', '( %s -> %s e. CC )' % (CH1, TT)), w.inst('sqneg')], 'syl',
                    '( %s -> ( -u %s ^ 2 ) = ( %s ^ 2 ) )' % (CH1, TT, TT))], 'idi', '( %s -> ( -u %s ^ 2 ) = ( %s ^ 2 ) )' % (CH1, TT, TT))], 'eqtrd',
          '( %s -> ( ( Im ` v ) ^ 2 ) = ( %s ^ 2 ) )' % (CH1, TT))
ab1 = w.s([w.s([w.s([e1], 'fveq2d', '( %s -> ( abs ` ( Im ` v ) ) = ( abs ` -u %s ) )' % (CH1, TT)),
                w.s([w.s([w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (CH1, TT))], 'recnd', '( %s -> %s e. CC )' % (CH1, TT))], 'absnegd',
                    '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (CH1, TT, TT))], 'eqtrd', '( %s -> ( abs ` ( Im ` v ) ) = ( abs ` %s ) )' % (CH1, TT)),
           w.s([w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (CH1, TT)), w.s([w.s([t0], 'adantr', '( %s -> 0 <_ %s )' % (CH1, TT))], 'idi', '( %s -> 0 <_ %s )' % (CH1, TT)), w.inst('absid')],
               'syl2anc', '( %s -> ( abs ` %s ) = %s )' % (CH1, TT, TT))], 'eqtrd', '( %s -> ( abs ` ( Im ` v ) ) = %s )' % (CH1, TT))
ch1 = horiz(CH1, sq1, ab1)
e2 = w.s([], 'simpr', '( %s -> ( Im ` v ) = %s )' % (CH2, TT))
sq2 = w.s([e2], 'oveq1d', '( %s -> ( ( Im ` v ) ^ 2 ) = ( %s ^ 2 ) )' % (CH2, TT))
ab2 = w.s([w.s([e2], 'fveq2d', '( %s -> ( abs ` ( Im ` v ) ) = ( abs ` %s ) )' % (CH2, TT)),
           w.s([w.s([ttrA], 'adantr', '( %s -> %s e. RR )' % (CH2, TT)), w.s([w.s([t0], 'adantr', '( %s -> 0 <_ %s )' % (CH2, TT))], 'idi', '( %s -> 0 <_ %s )' % (CH2, TT)), w.inst('absid')],
               'syl2anc', '( %s -> ( abs ` %s ) = %s )' % (CH2, TT, TT))], 'eqtrd', '( %s -> ( abs ` ( Im ` v ) ) = %s )' % (CH2, TT))
ch2 = horiz(CH2, sq2, ab2)
DV = '( ( Re ` v ) = X \\/ ( Re ` v ) = Y )'
DH = '( ( Im ` v ) = -u %s \\/ ( Im ` v ) = %s )' % (TT, TT)
cv = w.s([cv1, cv2], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (A1, DV, TGT))
ch = w.s([ch1, ch2], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (A1, DH, TGT))
allc = w.s([cv, ch], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (A1, DISJ2, TGT))
bndv = w.s([dsj2, allc], 'mpdan', '( %s -> %s )' % (A1, TGT))
gbv = w.s([w.s([gvv], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s x. %s ) ) )' % (A1, GG, FV, GAV)), bndv], 'eqbrtrd',
          '( %s -> ( abs ` ( %s ` v ) ) <_ C )' % (A1, GG))
allv = w.s([gbv], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ C )' % (A0, FRT, GG))
cbvu = w.s([w.s([w.s([w.s([], 'fveq2', '( v = u -> ( %s ` v ) = ( %s ` u ) )' % (GG, GG))], 'fveq2d',
                      '( v = u -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s ` u ) ) )' % (GG, GG))], 'breq1d',
                '( v = u -> ( ( abs ` ( %s ` v ) ) <_ C <-> ( abs ` ( %s ` u ) ) <_ C ) )' % (GG, GG))], 'cbvralvw',
           '( A. v e. %s ( abs ` ( %s ` v ) ) <_ C <-> A. u e. %s ( abs ` ( %s ` u ) ) <_ C )' % (FRT, GG, FRT, GG))
allu = w.s([allv, cbvu], 'sylib', '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ C )' % (A0, FRT, GG))
# maximum modulus
mm_ = w.s([abt, intw, w.s([hgm, rdd], 'jca', '( %s -> ( %s /\\ ( %s crect %s ) C_ D ) )' % (A0, HOLG(GG), LL, UR)),
           w.s([cr, allu], 'jca', '( %s -> ( C e. RR /\\ A. u e. %s ( abs ` ( %s ` u ) ) <_ C ) )' % (A0, FRT, GG)), w.inst('rectintmm')], 'syl31anc',
          '( %s -> ( abs ` ( %s ` W ) ) <_ C )' % (A0, GG))
# unwind at W
welst = w.s([w.s([wc, w.s([w.s([rwr, w.s([xw], 'ltled', '( %s -> X <_ %s )' % (A0, RW)), w.s([wy], 'ltled', '( %s -> %s <_ Y )' % (A0, RW))], '3jca',
                           '( %s -> ( %s e. RR /\\ X <_ %s /\\ %s <_ Y ) )' % (A0, RW, RW, RW)),
                    w.s([xr, yr, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( X [,] Y ) <-> ( %s e. RR /\\ X <_ %s /\\ %s <_ Y ) ) )' % (A0, RW, RW, RW, RW))],
                   'mpbird', '( %s -> %s e. ( X [,] Y ) )' % (A0, RW))], 'jca', '( %s -> ( W e. CC /\\ %s e. ( X [,] Y ) ) )' % (A0, RW)),
             w.s([w.s([], 'elstr', '( W e. %s <-> ( W e. CC /\\ %s e. ( X [,] Y ) ) )' % (STR, RW))], 'a1i',
                 '( %s -> ( W e. %s <-> ( W e. CC /\\ %s e. ( X [,] Y ) ) ) )' % (A0, STR, RW))], 'mpbird', '( %s -> W e. %s )' % (A0, STR))
wdd = w.s([sd, welst], 'sseldd', '( %s -> W e. D )' % A0)
sw1 = w.s([], 'fveq2', '( z = W -> ( F ` z ) = ( F ` W ) )')
sw2 = w.s([w.s([w.s([], 'oveq1', '( z = W -> ( z ^ 2 ) = ( W ^ 2 ) )')], 'oveq1d', '( z = W -> ( ( z ^ 2 ) - %s ) = ( ( W ^ 2 ) - %s ) )' % (NQ, NQ))], 'oveq2d',
           '( z = W -> ( E x. ( ( z ^ 2 ) - %s ) ) = ( E x. ( ( W ^ 2 ) - %s ) ) )' % (NQ, NQ))
sw3 = w.s([sw2], 'fveq2d', '( z = W -> %s = %s )' % (GAU('z'), GAU('W')))
subw = w.s([sw1, sw3], 'oveq12d', '( z = W -> ( ( F ` z ) x. %s ) = ( ( F ` W ) x. %s ) )' % (GAU('z'), GAU('W')))
gvw = mptval(w, A0, 'z', 'D', GG, 'W', '( ( F ` W ) x. %s )' % GAU('W'), subw, wdd)
fwc = w.s([ff, wdd], 'ffvelcdmd', '( %s -> ( F ` W ) e. CC )' % A0)
gwc = w.s([w.s([ec_, w.s([w.s([wc], 'sqcld', '( %s -> ( W ^ 2 ) e. CC )' % A0), nqc], 'subcld', '( %s -> ( ( W ^ 2 ) - %s ) e. CC )' % (A0, NQ))], 'mulcld',
               '( %s -> ( E x. ( ( W ^ 2 ) - %s ) ) e. CC )' % (A0, NQ)), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A0, GAU('W')))
amul = w.s([fwc, gwc], 'absmuld', '( %s -> ( abs ` ( ( F ` W ) x. %s ) ) = ( ( abs ` ( F ` W ) ) x. ( abs ` %s ) ) )' % (A0, GAU('W'), GAU('W')))
agw = w.s([wc, er, nqr, w.inst('absgau')], 'syl3anc', '( %s -> ( abs ` %s ) = ( exp ` ( E x. %s ) ) )' % (A0, GAU('W'), VV))
chain = w.s([w.s([w.s([gvw], 'fveq2d', '( %s -> ( abs ` ( %s ` W ) ) = ( abs ` ( ( F ` W ) x. %s ) ) )' % (A0, GG, GAU('W'))), amul], 'eqtrd',
                 '( %s -> ( abs ` ( %s ` W ) ) = ( ( abs ` ( F ` W ) ) x. ( abs ` %s ) ) )' % (A0, GG, GAU('W'))),
             w.s([agw], 'oveq2d', '( %s -> ( ( abs ` ( F ` W ) ) x. ( abs ` %s ) ) = ( ( abs ` ( F ` W ) ) x. ( exp ` ( E x. %s ) ) ) )' % (A0, GAU('W'), VV))],
            'eqtrd', '( %s -> ( abs ` ( %s ` W ) ) = ( ( abs ` ( F ` W ) ) x. ( exp ` ( E x. %s ) ) ) )' % (A0, GG, VV))
key = w.s([w.s([chain], 'eqcomd', '( %s -> ( ( abs ` ( F ` W ) ) x. ( exp ` ( E x. %s ) ) ) = ( abs ` ( %s ` W ) ) )' % (A0, VV, GG)), mm_], 'eqbrtrd',
          '( %s -> ( ( abs ` ( F ` W ) ) x. ( exp ` ( E x. %s ) ) ) <_ C )' % (A0, VV))
vvr = w.s([w.s([w.s([rwr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, RW)), w.s([iwr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (A0, IW))], 'resubcld',
               '( %s -> ( ( %s ^ 2 ) - ( %s ^ 2 ) ) e. RR )' % (A0, RW, IW)), nqr], 'resubcld', '( %s -> %s e. RR )' % (A0, VV))
evr = w.s([er, vvr], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A0, VV))
efvr = w.s([evr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( E x. %s ) ) e. RR )' % (A0, VV))
efvp = w.s([evr, w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` ( E x. %s ) ) )' % (A0, VV))
efvrp = w.s([efvr, efvp], 'elrpd', '( %s -> ( exp ` ( E x. %s ) ) e. RR+ )' % (A0, VV))
afw = w.s([fwc], 'abscld', '( %s -> ( abs ` ( F ` W ) ) e. RR )' % A0)
div = w.s([key, w.s([afw, cr, w.s([efvr, efvp], 'jca', '( %s -> ( ( exp ` ( E x. %s ) ) e. RR /\\ 0 < ( exp ` ( E x. %s ) ) ) )' % (A0, VV, VV)), w.inst('lemuldiv')], 'syl3anc',
                    '( %s -> ( ( ( abs ` ( F ` W ) ) x. ( exp ` ( E x. %s ) ) ) <_ C <-> ( abs ` ( F ` W ) ) <_ ( C / ( exp ` ( E x. %s ) ) ) ) )' % (A0, VV, VV))],
          'mpbid', '( %s -> ( abs ` ( F ` W ) ) <_ ( C / ( exp ` ( E x. %s ) ) ) )' % (A0, VV))
rec = w.s([w.s([cr], 'recnd', '( %s -> C e. CC )' % A0), w.s([efvr], 'recnd', '( %s -> ( exp ` ( E x. %s ) ) e. CC )' % (A0, VV)),
           w.s([efvrp], 'rpne0d', '( %s -> ( exp ` ( E x. %s ) ) =/= 0 )' % (A0, VV))], 'divrecd',
          '( %s -> ( C / ( exp ` ( E x. %s ) ) ) = ( C x. ( 1 / ( exp ` ( E x. %s ) ) ) ) )' % (A0, VV, VV))
nege = w.s([w.s([evr], 'recnd', '( %s -> ( E x. %s ) e. CC )' % (A0, VV)), w.inst('efneg')], 'syl',
           '( %s -> ( exp ` -u ( E x. %s ) ) = ( 1 / ( exp ` ( E x. %s ) ) ) )' % (A0, VV, VV))
mneg = w.s([ec_, w.s([vvr], 'recnd', '( %s -> %s e. CC )' % (A0, VV))], 'mulneg2d', '( %s -> ( E x. -u %s ) = -u ( E x. %s ) )' % (A0, VV, VV))
tgt = w.s([w.s([w.s([mneg], 'fveq2d', '( %s -> ( exp ` ( E x. -u %s ) ) = ( exp ` -u ( E x. %s ) ) )' % (A0, VV, VV)), nege], 'eqtrd',
                '( %s -> ( exp ` ( E x. -u %s ) ) = ( 1 / ( exp ` ( E x. %s ) ) ) )' % (A0, VV, VV))], 'oveq2d',
           '( %s -> ( C x. ( exp ` ( E x. -u %s ) ) ) = ( C x. ( 1 / ( exp ` ( E x. %s ) ) ) ) )' % (A0, VV, VV))
w.qed([div, w.s([w.s([rec, w.s([tgt], 'eqcomd', '( %s -> ( C x. ( 1 / ( exp ` ( E x. %s ) ) ) ) = ( C x. ( exp ` ( E x. -u %s ) ) ) )' % (A0, VV, VV))], 'eqtrd',
                      '( %s -> ( C / ( exp ` ( E x. %s ) ) ) = ( C x. ( exp ` ( E x. -u %s ) ) ) )' % (A0, VV, VV))], 'idi',
                 '( %s -> ( C / ( exp ` ( E x. %s ) ) ) = ( C x. ( exp ` ( E x. -u %s ) ) ) )' % (A0, VV, VV))], 'breqtrd',
      '( %s -> ( abs ` ( F ` W ) ) <_ ( C x. ( exp ` ( E x. -u %s ) ) ) )' % (A0, VV)); run1(w)
