"""Sortie C2 section 3.3d: Phragmen-Lindelof on a vertical strip."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *
from lin import linarith

STR = '( `\' Re " ( X [,] Y ) )'
NQ = '( ( ( abs ` X ) + ( abs ` Y ) ) ^ 2 )'
IW = '( Im ` W )'; RW = '( Re ` W )'
VV = '( ( ( %s ^ 2 ) - ( %s ^ 2 ) ) - %s )' % (RW, IW, NQ)
EDG1 = 'A. y e. %s ( ( Re ` y ) = X -> ( abs ` ( F ` y ) ) <_ C )' % STR
EDG2 = 'A. y e. %s ( ( Re ` y ) = Y -> ( abs ` ( F ` y ) ) <_ C )' % STR
GRW = 'A. y e. %s ( abs ` ( F ` y ) ) <_ ( K x. ( exp ` ( L x. ( abs ` ( Im ` y ) ) ) ) )' % STR
H1 = '( X e. RR /\\ Y e. RR )'
H2 = '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D )' % STR
H3 = '( C e. RR+ /\\ %s /\\ %s )' % (EDG1, EDG2)
H4 = '( ( K e. RR+ /\\ L e. RR /\\ 0 <_ L ) /\\ %s )' % GRW
A0 = '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ W e. %s ) )' % (H1, H2, H3, H4, STR)
AFW = '( abs ` ( F ` W ) )'

w = W('rectintpl', 'Phragmen-Lindelof on a vertical strip: a function holomorphic on an open set containing the strip, bounded by C on the two edges and of at most single-exponential growth in the imaginary direction, is bounded by C on the whole strip.')
h123 = w.s([], 'simpl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, H1, H2, H3))
h4w = w.s([], 'simpr', '( %s -> ( %s /\\ W e. %s ) )' % (A0, H4, STR))
h1 = w.s([h123, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, H1))
h2 = w.s([h123, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, H2))
h3 = w.s([h123, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, H3))
h4 = w.s([h4w, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, H4))
wst = w.s([h4w, w.inst('simpr')], 'syl', '( %s -> W e. %s )' % (A0, STR))
xr = w.s([h1, w.inst('simpl')], 'syl', '( %s -> X e. RR )' % A0)
yr = w.s([h1, w.inst('simpr')], 'syl', '( %s -> Y e. RR )' % A0)
fcn = w.s([h2, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
sd = w.s([h2, w.inst('simp3')], 'syl', '( %s -> %s C_ D )' % (A0, STR))
crp = w.s([h3, w.inst('simp1')], 'syl', '( %s -> C e. RR+ )' % A0)
ed1 = w.s([h3, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, EDG1))
ed2 = w.s([h3, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, EDG2))
cr = w.s([crp], 'rpred', '( %s -> C e. RR )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
wd = w.s([sd, wst], 'sseldd', '( %s -> W e. D )' % A0)
fwc = w.s([ff, wd], 'ffvelcdmd', '( %s -> ( F ` W ) e. CC )' % A0)
afw = w.s([fwc], 'abscld', '( %s -> %s e. RR )' % (A0, AFW))
wel = w.s([wst, w.s([w.s([], 'elstr', '( W e. %s <-> ( W e. CC /\\ %s e. ( X [,] Y ) ) )' % (STR, RW))], 'a1i',
                    '( %s -> ( W e. %s <-> ( W e. CC /\\ %s e. ( X [,] Y ) ) ) )' % (A0, STR, RW))], 'mpbid',
          '( %s -> ( W e. CC /\\ %s e. ( X [,] Y ) ) )' % (A0, RW))
wc = w.s([wel, w.inst('simpl')], 'syl', '( %s -> W e. CC )' % A0)
wxy = w.s([wel, w.inst('simpr')], 'syl', '( %s -> %s e. ( X [,] Y ) )' % (A0, RW))
wic = w.s([wxy, w.s([xr, yr, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( X [,] Y ) <-> ( %s e. RR /\\ X <_ %s /\\ %s <_ Y ) ) )' % (A0, RW, RW, RW, RW))],
          'mpbid', '( %s -> ( %s e. RR /\\ X <_ %s /\\ %s <_ Y ) )' % (A0, RW, RW, RW))
rwr = w.s([wic, w.inst('simp1')], 'syl', '( %s -> %s e. RR )' % (A0, RW))
wlo = w.s([wic, w.inst('simp2')], 'syl', '( %s -> X <_ %s )' % (A0, RW))
whi = w.s([wic, w.inst('simp3')], 'syl', '( %s -> %s <_ Y )' % (A0, RW))


def edgeat(ante, edg, edgf, val, eqstep, wstep):
    sub = w.s([w.s([w.s([], 'fveq2', '( y = W -> ( Re ` y ) = %s )' % RW)], 'eqeq1d', '( y = W -> ( ( Re ` y ) = %s <-> %s = %s ) )' % (val, RW, val)),
               w.s([w.s([w.s([], 'fveq2', '( y = W -> ( F ` y ) = ( F ` W ) )')], 'fveq2d', '( y = W -> ( abs ` ( F ` y ) ) = %s )' % AFW)], 'breq1d',
                   '( y = W -> ( ( abs ` ( F ` y ) ) <_ C <-> %s <_ C ) )' % AFW)], 'imbi12d',
              '( y = W -> ( ( ( Re ` y ) = %s -> ( abs ` ( F ` y ) ) <_ C ) <-> ( %s = %s -> %s <_ C ) ) )' % (val, RW, val, AFW))
    ins = w.s([sub, w.s([edg], 'adantr', '( %s -> %s )' % (ante, edgf)), wstep], 'rspcdva',
              '( %s -> ( %s = %s -> %s <_ C ) )' % (ante, RW, val, AFW))
    return w.s([ins, eqstep], 'mpd', '( %s -> %s <_ C )' % (ante, AFW))


# case Re W = X
CX = '( %s /\\ X = %s )' % (A0, RW)
cx = edgeat(CX, ed1, EDG1, 'X', w.s([w.s([], 'simpr', '( %s -> X = %s )' % (CX, RW))], 'eqcomd', '( %s -> %s = X )' % (CX, RW)),
            w.s([wst], 'adantr', '( %s -> W e. %s )' % (CX, STR)))
# case X < Re W, Re W = Y
PX = '( %s /\\ X < %s )' % (A0, RW)
CY = '( %s /\\ %s = Y )' % (PX, RW)
cy = edgeat(CY, w.s([ed2], 'adantr', '( %s -> %s )' % (PX, EDG2)), EDG2, 'Y',
            w.s([], 'simpr', '( %s -> %s = Y )' % (CY, RW)),
            w.s([w.s([wst], 'adantr', '( %s -> W e. %s )' % (PX, STR))], 'adantr', '( %s -> W e. %s )' % (CY, STR)))
# case X < Re W < Y
P3 = '( %s /\\ %s < Y )' % (PX, RW)
Q3 = '( %s /\\ e e. RR+ )' % P3


def l3(st, form):
    return w.s([w.s([st], 'adantr', '( %s -> %s )' % (PX, form))], 'adantr', '( %s -> %s )' % (P3, form))


xw3 = w.s([w.s([], 'simpr', '( %s -> X < %s )' % (PX, RW))], 'adantr', '( %s -> X < %s )' % (P3, RW))
wy3 = w.s([], 'simpr', '( %s -> %s < Y )' % (P3, RW))
h13 = l3(h1, H1); h23 = l3(h2, H2); h33 = l3(h3, H3); h43 = l3(h4, H4)
wc3 = l3(wc, 'W e. CC'); cr3 = l3(cr, 'C e. RR'); crp3 = l3(crp, 'C e. RR+')
afw3 = l3(afw, '%s e. RR' % AFW); rwr3 = l3(rwr, '%s e. RR' % RW)
xr3 = l3(xr, 'X e. RR'); yr3 = l3(yr, 'Y e. RR')
h53 = w.s([wc3, xw3, wy3], '3jca', '( %s -> ( W e. CC /\\ X < %s /\\ %s < Y ) )' % (P3, RW, RW))
erp = w.s([], 'simpr', '( %s -> e e. RR+ )' % Q3)
pl1 = w.s([w.s([w.s([h13], 'adantr', '( %s -> %s )' % (Q3, H1)), w.s([h23], 'adantr', '( %s -> %s )' % (Q3, H2)),
                w.s([h33], 'adantr', '( %s -> %s )' % (Q3, H3))], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (Q3, H1, H2, H3)),
           w.s([w.s([h43], 'adantr', '( %s -> %s )' % (Q3, H4)), w.s([h53], 'adantr', '( %s -> ( W e. CC /\\ X < %s /\\ %s < Y ) )' % (Q3, RW, RW)),
                erp], '3jca', '( %s -> ( %s /\\ ( W e. CC /\\ X < %s /\\ %s < Y ) /\\ e e. RR+ ) )' % (Q3, H4, RW, RW)),
           w.inst('rectintpl1')], 'syl2anc', '( %s -> %s <_ ( C x. ( exp ` ( e x. -u %s ) ) ) )' % (Q3, AFW, VV))
alle = w.s([pl1], 'ralrimiva', '( %s -> A. e e. RR+ %s <_ ( C x. ( exp ` ( e x. -u %s ) ) ) )' % (P3, AFW, VV))
# 0 <_ -u VV
iwr3 = w.s([wc3], 'imcld', '( %s -> %s e. RR )' % (P3, IW))
rw2 = w.s([rwr3], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (P3, RW))
iw2 = w.s([iwr3], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (P3, IW))
iw20 = w.s([iwr3], 'sqge0d', '( %s -> 0 <_ ( %s ^ 2 ) )' % (P3, IW))
axr = w.s([w.s([xr3], 'recnd', '( %s -> X e. CC )' % P3)], 'abscld', '( %s -> ( abs ` X ) e. RR )' % P3)
ayr = w.s([w.s([yr3], 'recnd', '( %s -> Y e. CC )' % P3)], 'abscld', '( %s -> ( abs ` Y ) e. RR )' % P3)
nqr = w.s([w.s([axr, ayr], 'readdcld', '( %s -> ( ( abs ` X ) + ( abs ` Y ) ) e. RR )' % P3)], 'resqcld', '( %s -> %s e. RR )' % (P3, NQ))
sqle = w.s([w.s([xr3, yr3, rwr3], '3jca', '( %s -> ( X e. RR /\\ Y e. RR /\\ %s e. RR ) )' % (P3, RW)),
            w.s([w.s([xw3], 'ltled', '( %s -> X <_ %s )' % (P3, RW)), w.s([wy3], 'ltled', '( %s -> %s <_ Y )' % (P3, RW))], 'jca',
                '( %s -> ( X <_ %s /\\ %s <_ Y ) )' % (P3, RW, RW)), w.inst('sqleabs2')], 'syl2anc',
           '( %s -> ( %s ^ 2 ) <_ %s )' % (P3, RW, NQ))
vvr = w.s([w.s([rw2, iw2], 'resubcld', '( %s -> ( ( %s ^ 2 ) - ( %s ^ 2 ) ) e. RR )' % (P3, RW, IW)), nqr], 'resubcld', '( %s -> %s e. RR )' % (P3, VV))
lv = {'( %s ^ 2 )' % RW: ('RR', rw2), '( %s ^ 2 )' % IW: ('RR', iw2), NQ: ('RR', nqr)}
vle = linarith(w, P3, [sqle, iw20], '%s <_ 0' % VV, leaves=lv)
nv0 = w.s([vle, w.s([vvr], 'le0neg1d', '( %s -> ( %s <_ 0 <-> 0 <_ -u %s ) )' % (P3, VV, VV))], 'mpbid', '( %s -> 0 <_ -u %s )' % (P3, VV))
nvr = w.s([vvr], 'renegcld', '( %s -> -u %s e. RR )' % (P3, VV))
c3 = w.s([afw3, crp3, w.s([w.s([nvr, nv0], 'jca', '( %s -> ( -u %s e. RR /\\ 0 <_ -u %s ) )' % (P3, VV, VV)), alle], 'jca',
                          '( %s -> ( ( -u %s e. RR /\\ 0 <_ -u %s ) /\\ A. e e. RR+ %s <_ ( C x. ( exp ` ( e x. -u %s ) ) ) ) )' % (P3, VV, VV, AFW, VV)),
          w.inst('explimle')], 'syl3anc', '( %s -> %s <_ C )' % (P3, AFW))
# combine
dy = w.s([w.s([w.s([rwr], 'adantr', '( %s -> %s e. RR )' % (PX, RW)), w.s([yr], 'adantr', '( %s -> Y e. RR )' % PX)], 'leloed',
               '( %s -> ( %s <_ Y <-> ( %s < Y \\/ %s = Y ) ) )' % (PX, RW, RW, RW))], 'idi',
         '( %s -> ( %s <_ Y <-> ( %s < Y \\/ %s = Y ) ) )' % (PX, RW, RW, RW))
dyy = w.s([w.s([whi], 'adantr', '( %s -> %s <_ Y )' % (PX, RW)), dy], 'mpbid', '( %s -> ( %s < Y \\/ %s = Y ) )' % (PX, RW, RW))
cpx = w.s([w.s([c3, cy], 'jaodan', '( ( %s /\\ ( %s < Y \\/ %s = Y ) ) -> %s <_ C )' % (PX, RW, RW, AFW)), dyy], 'mpdan', '( %s -> %s <_ C )' % (PX, AFW))
dx = w.s([wlo, w.s([xr, rwr], 'leloed', '( %s -> ( X <_ %s <-> ( X < %s \\/ X = %s ) ) )' % (A0, RW, RW, RW))], 'mpbid',
         '( %s -> ( X < %s \\/ X = %s ) )' % (A0, RW, RW))
w.qed([w.s([cpx, cx], 'jaodan', '( ( %s /\\ ( X < %s \\/ X = %s ) ) -> %s <_ C )' % (A0, RW, RW, AFW)), dx], 'mpdan', '( %s -> %s <_ C )' % (A0, AFW)); run1(w)
