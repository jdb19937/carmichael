"""C7, Gamma block 4: the vertical segment inside lgamgulm's disc, the
continuity of Gamma on a vertical segment, the integrability of the line-moment
integrand, and the T-free line moment (segu, gamcnl, gamlibl, gamlmomx)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq, nlinarith

XC = '( -u T [,] T )'
XO = '( -u T (,) T )'
W_ = CPT('X', 'u')
MI = '( u e. %s |-> %s )' % (XC, W_)
SEG = 'ran %s' % MI
A0 = '( ( X e. RR /\\ 0 < X ) /\\ T e. RR+ )'
ARCH = '( ( 1 / X ) + ( X + T ) )'
AR = '( %s /\\ ( r e. NN /\\ %s < r ) )' % (A0, ARCH)


def ctx(w, A):
    d = {}
    d['xr'] = w.s([], 'simpll', '( %s -> X e. RR )' % A)
    d['xgt'] = w.s([], 'simplr', '( %s -> 0 < X )' % A)
    d['trp'] = w.s([], 'simpr', '( %s -> T e. RR+ )' % A)
    return d


# ---------------------------------------------------------------- segu
w = W('segu', 'The vertical segment ` X + i [ -u T , T ] `, ` 0 < X `, lies in lgamgulm\'s disc of '
      'every natural radius ` r > 1 / X + X + T ` and in the open right half-plane.')
d = ctx(w, A0)
xr = w.s([d['xr']], 'adantr', '( %s -> X e. RR )' % AR)
xgt = w.s([d['xgt']], 'adantr', '( %s -> 0 < X )' % AR)
trp = w.s([d['trp']], 'adantr', '( %s -> T e. RR+ )' % AR)
rn = w.s([], 'simprl', '( %s -> r e. NN )' % AR)
lt = w.s([], 'simprr', '( %s -> %s < r )' % (AR, ARCH))
xrp = w.s([xr, xgt], 'elrpd', '( %s -> X e. RR+ )' % AR)
ixrp = w.s([xrp], 'rpreccld', '( %s -> ( 1 / X ) e. RR+ )' % AR)
cl = Closure(w, AR, {'X': ('RR+', xrp), 'T': ('RR+', trp), 'r': ('NN', rn)})
cl.leaf('( 1 / X )', 'RR+', ixrp)
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR'); rr = cl.mem('r', 'RR')
ixle = linarith(w, AR, [lt, cl.gt0('X'), cl.gt0('T')], '( 1 / X ) <_ r', closure=cl)
lr = w.s([w.s([cl.mem('( 1 / X )', 'RR'), cl.gt0('( 1 / X )')], 'jca', '( %s -> ( ( 1 / X ) e. RR /\\ 0 < ( 1 / X ) ) )' % AR), w.s([rr, cl.gt0('r')], 'jca', '( %s -> ( r e. RR /\\ 0 < r ) )' % AR), w.inst('lerec')], 'syl2anc',
         '( %s -> ( ( 1 / X ) <_ r <-> ( 1 / r ) <_ ( 1 / ( 1 / X ) ) ) )' % AR)
irx = w.s([w.s([ixle, lr], 'mpbid', '( %s -> ( 1 / r ) <_ ( 1 / ( 1 / X ) ) )' % AR), w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % AR), w.s([xrp], 'rpne0d', '( %s -> X =/= 0 )' % AR), w.inst('recrec')], 'syl2anc', '( %s -> ( 1 / ( 1 / X ) ) = X )' % AR)], 'breqtrd',
          '( %s -> ( 1 / r ) <_ X )' % AR)
# the point W = X + i u
Au = '( %s /\\ u e. %s )' % (AR, XC)
uin = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, XC))
ussr = w.s([ntr, tr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (AR, XC))
ur = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (Au, XC)), uin], 'sseldd', '( %s -> u e. RR )' % Au)
bnds = w.s([uin, w.s([w.s([ntr], 'adantr', '( %s -> -u T e. RR )' % Au), w.s([tr], 'adantr', '( %s -> T e. RR )' % Au), w.inst('elicc2')], 'syl2anc', '( %s -> ( u e. %s <-> ( u e. RR /\\ -u T <_ u /\\ u <_ T ) ) )' % (Au, XC))], 'mpbid',
           '( %s -> ( u e. RR /\\ -u T <_ u /\\ u <_ T ) )' % Au)
ulo = w.s([bnds, w.inst('simp2')], 'syl', '( %s -> -u T <_ u )' % Au)
uhi = w.s([bnds, w.inst('simp3')], 'syl', '( %s -> u <_ T )' % Au)
xru = w.s([xr], 'adantr', '( %s -> X e. RR )' % Au)
wc = cptcl(w, Au, 'X', 'u', xru, ur)
uc = w.s([ur], 'recnd', '( %s -> u e. CC )' % Au)
iuc = w.s([a1(w, Au, 'ax-icn', '_i e. CC'), uc], 'mulcld', '( %s -> ( _i x. u ) e. CC )' % Au)
xc = w.s([xru], 'recnd', '( %s -> X e. CC )' % Au)
tri = w.s([xc, iuc], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` X ) + ( abs ` ( _i x. u ) ) ) )' % (Au, W_))
xge = w.s([w.s([xrp], 'adantr', '( %s -> X e. RR+ )' % Au)], 'rpge0d', '( %s -> 0 <_ X )' % Au)
absx = w.s([xru, xge], 'absidd', '( %s -> ( abs ` X ) = X )' % Au)
absiu = absi_(w, Au, 'u', uc)
tri2 = w.s([tri, w.s([absx, absiu], 'oveq12d', '( %s -> ( ( abs ` X ) + ( abs ` ( _i x. u ) ) ) = ( X + ( abs ` u ) ) )' % Au)], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( X + ( abs ` u ) ) )' % (Au, W_))
clu = Closure(w, Au, {'X': ('RR+', w.s([xrp], 'adantr', '( %s -> X e. RR+ )' % Au)), 'T': ('RR+', w.s([trp], 'adantr', '( %s -> T e. RR+ )' % Au)), 'u': ('RR', ur), 'r': ('NN', w.s([rn], 'adantr', '( %s -> r e. NN )' % Au))})
clu.leaf('( 1 / X )', 'RR+', w.s([ixrp], 'adantr', '( %s -> ( 1 / X ) e. RR+ )' % Au))
clu.leaf('( abs ` u )', 'RR', w.s([uc], 'abscld', '( %s -> ( abs ` u ) e. RR )' % Au))
clu.leaf('( abs ` %s )' % W_, 'RR', w.s([wc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Au, W_)))
absu = w.s([w.s([ulo, uhi], 'jca', '( %s -> ( -u T <_ u /\\ u <_ T ) )' % Au), w.s([ur, w.s([tr], 'adantr', '( %s -> T e. RR )' % Au)], 'absled', '( %s -> ( ( abs ` u ) <_ T <-> ( -u T <_ u /\\ u <_ T ) ) )' % Au)], 'mpbird', '( %s -> ( abs ` u ) <_ T )' % Au)
wle = linarith(w, Au, [tri2, absu, w.s([lt], 'adantr', '( %s -> %s < r )' % (Au, ARCH)), clu.gt0('( 1 / X )')], '( abs ` %s ) <_ r' % W_, closure=clu)
# the distance from the poles
Al = '( %s /\\ l e. NN0 )' % Au
ln0 = w.s([], 'simpr', '( %s -> l e. NN0 )' % Al)
lr_ = w.s([ln0], 'nn0red', '( %s -> l e. RR )' % Al); lc_ = w.s([lr_], 'recnd', '( %s -> l e. CC )' % Al)
wcl = w.s([wc], 'adantr', '( %s -> %s e. CC )' % (Al, W_))
WL = '( %s + l )' % W_
wlc = w.s([wcl, lc_], 'addcld', '( %s -> %s e. CC )' % (Al, WL))
rew = w.s([w.s([xru], 'adantr', '( %s -> X e. RR )' % Al), w.s([ur], 'adantr', '( %s -> u e. RR )' % Al), w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = X )' % (Al, W_))
rel = w.s([w.s([wcl, lc_, w.inst('readd')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` %s ) + ( Re ` l ) ) )' % (Al, WL, W_)), w.s([rew, w.s([lr_, w.inst('rere')], 'syl', '( %s -> ( Re ` l ) = l )' % Al)], 'oveq12d', '( %s -> ( ( Re ` %s ) + ( Re ` l ) ) = ( X + l ) )' % (Al, W_))], 'eqtrd',
          '( %s -> ( Re ` %s ) = ( X + l ) )' % (Al, WL))
rle = w.s([w.s([rel], 'eqcomd', '( %s -> ( X + l ) = ( Re ` %s ) )' % (Al, WL)), w.s([wlc, w.inst('releabs')], 'syl', '( %s -> ( Re ` %s ) <_ ( abs ` %s ) )' % (Al, WL, WL))], 'eqbrtrd', '( %s -> ( X + l ) <_ ( abs ` %s ) )' % (Al, WL))
cll = Closure(w, Al, {'X': ('RR', w.s([xru], 'adantr', '( %s -> X e. RR )' % Al)), 'l': ('NN0', ln0), 'r': ('NN', w.s([rn], 'ad2antrr', '( %s -> r e. NN )' % Al))})
cll.leaf('( abs ` %s )' % WL, 'RR', w.s([wlc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Al, WL)))
rrp = w.s([w.s([rn], 'ad2antrr', '( %s -> r e. NN )' % Al)], 'nnrpd', '( %s -> r e. RR+ )' % Al)
cll.leaf('( 1 / r )', 'RR', w.s([w.s([rrp], 'rpreccld', '( %s -> ( 1 / r ) e. RR+ )' % Al)], 'rpred', '( %s -> ( 1 / r ) e. RR )' % Al))
dle = linarith(w, Al, [rle, w.s([irx], 'ad2antrr', '( %s -> ( 1 / r ) <_ X )' % Al), cll.ge0('l')], '( 1 / r ) <_ ( abs ` %s )' % WL, closure=cll)
rall = w.s([dle], 'ralrimiva', '( %s -> A. l e. NN0 ( 1 / r ) <_ ( abs ` %s ) )' % (Au, WL))
# membership in the disc
COND = '( ( abs ` b ) <_ r /\\ A. l e. NN0 ( 1 / r ) <_ ( abs ` ( b + l ) ) )'
CONDW = '( ( abs ` %s ) <_ r /\\ A. l e. NN0 ( 1 / r ) <_ ( abs ` %s ) )' % (W_, WL)
s1 = w.s([w.s([], 'fveq2', '( b = %s -> ( abs ` b ) = ( abs ` %s ) )' % (W_, W_))], 'breq1d', '( b = %s -> ( ( abs ` b ) <_ r <-> ( abs ` %s ) <_ r ) )' % (W_, W_))
s2 = w.s([w.s([w.s([w.s([], 'oveq1', '( b = %s -> ( b + l ) = %s )' % (W_, WL))], 'fveq2d', '( b = %s -> ( abs ` ( b + l ) ) = ( abs ` %s ) )' % (W_, WL))], 'breq2d', '( b = %s -> ( ( 1 / r ) <_ ( abs ` ( b + l ) ) <-> ( 1 / r ) <_ ( abs ` %s ) ) )' % (W_, WL))], 'ralbidv',
          '( b = %s -> ( A. l e. NN0 ( 1 / r ) <_ ( abs ` ( b + l ) ) <-> A. l e. NN0 ( 1 / r ) <_ ( abs ` %s ) ) )' % (W_, WL))
sb = w.s([s1, s2], 'anbi12d', '( b = %s -> ( %s <-> %s ) )' % (W_, COND, CONDW))
elr = w.s([sb], 'elrab', '( %s e. %s <-> ( %s e. CC /\\ %s ) )' % (W_, UR('r'), W_, CONDW))
inu = w.s([wc, w.s([wle, rall], 'jca', '( %s -> %s )' % (Au, CONDW)), elr], 'sylanbrc', '( %s -> %s e. %s )' % (Au, W_, UR('r')))
ssu = w.s([w.s([inu], 'ralrimiva', '( %s -> A. u e. %s %s e. %s )' % (AR, XC, W_, UR('r'))), w.s([w.s([], 'eqid', '%s = %s' % (MI, MI))], 'rnmptss', '( A. u e. %s %s e. %s -> %s C_ %s )' % (XC, W_, UR('r'), SEG, UR('r')))], 'syl',
          '( %s -> %s C_ %s )' % (AR, SEG, UR('r')))
# membership in the half-plane
rew0 = w.s([xru, ur, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = X )' % (Au, W_))
gt = w.s([w.s([xgt], 'adantr', '( %s -> 0 < X )' % Au), rew0], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (Au, W_))
bi = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (W_, HP0, W_, W_))], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (Au, W_, HP0, W_, W_))
inh = w.s([w.s([wc, gt], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (Au, W_, W_)), bi], 'mpbird', '( %s -> %s e. %s )' % (Au, W_, HP0))
ssh = w.s([w.s([inh], 'ralrimiva', '( %s -> A. u e. %s %s e. %s )' % (AR, XC, W_, HP0)), w.s([w.s([], 'eqid', '%s = %s' % (MI, MI))], 'rnmptss', '( A. u e. %s %s e. %s -> %s C_ %s )' % (XC, W_, HP0, SEG, HP0))], 'syl',
          '( %s -> %s C_ %s )' % (AR, SEG, HP0))
w.qed([ssu, ssh], 'jca', '( %s -> ( %s C_ %s /\\ %s C_ %s ) )' % (AR, SEG, UR('r'), SEG, HP0))
run7(w)

# ---------------------------------------------------------------- gamcnl
GMAP = '( u e. %s |-> ( _G ` %s ) )' % (XC, W_)
MIO = '( o e. %s |-> %s )' % (XC, CPT('X', 'o'))
SEGO = 'ran %s' % MIO
GM = '( z e. %s |-> ( _G ` z ) )' % SEGO
w = W('gamcnl', 'The Gamma function is continuous along a vertical segment ` X + i [ -u T , T ] ` '
      'in the open right half-plane ( ~ gamcns on the segment, ~ segu ).  The continuity that '
      'set.mm lacks for ` _G `, in the form the line moment needs.')
d = ctx(w, A0)
xr = w.s([d['xr']], 'adantr', '( %s -> X e. RR )' % AR)
xgt = w.s([d['xgt']], 'adantr', '( %s -> 0 < X )' % AR)
trp = w.s([d['trp']], 'adantr', '( %s -> T e. RR+ )' % AR)
rn = w.s([], 'simprl', '( %s -> r e. NN )' % AR)
both = w.s([w.s([], 'id', '( %s -> %s )' % (AR, AR)), w.inst('segu')], 'syl', '( %s -> ( %s C_ %s /\\ %s C_ %s ) )' % (AR, SEG, UR('r'), SEG, HP0))
segeq = w.s([w.s([w.s([w.s([], 'oveq2', '( u = o -> ( _i x. u ) = ( _i x. o ) )')], 'oveq2d', '( u = o -> %s = %s )' % (W_, CPT('X', 'o')))], 'cbvmptv', '%s = %s' % (MI, MIO))], 'rneqi', '%s = %s' % (SEG, SEGO))
segeqd = w.s([segeq], 'a1i', '( %s -> %s = %s )' % (AR, SEG, SEGO))
ssu = w.s([w.s([both, w.inst('simpl')], 'syl', '( %s -> %s C_ %s )' % (AR, SEG, UR('r'))), segeqd], 'eqsstrrd', '( %s -> %s C_ %s )' % (AR, SEGO, UR('r')))
ssh = w.s([w.s([both, w.inst('simpr')], 'syl', '( %s -> %s C_ %s )' % (AR, SEG, HP0)), segeqd], 'eqsstrrd', '( %s -> %s C_ %s )' % (AR, SEGO, HP0))
gcn = w.s([rn, w.s([], 'eqid', '%s = %s' % (UR('r'), UR('r'))), ssu, ssh], 'gamcns', '( %s -> %s e. ( %s -cn-> CC ) )' % (AR, GM, SEGO))
# the parametrisation is continuous into the segment
cl = Closure(w, AR, {'T': ('RR+', trp)})
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
ussr = w.s([ntr, tr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (AR, XC))
usscn = w.s([ussr, a1(w, AR, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (AR, XC))
sscc = a1(w, AR, 'ssid', 'CC C_ CC')
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( u e. %s |-> u ) e. ( %s -cn-> CC ) )' % (AR, XC, XC))
xcst = w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % AR), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( u e. %s |-> X ) e. ( %s -cn-> CC ) )' % (AR, XC, XC))
icst = w.s([a1(w, AR, 'ax-icn', '_i e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( u e. %s |-> _i ) e. ( %s -cn-> CC ) )' % (AR, XC, XC))
iu = w.s([icst, idc], 'mulcncf', '( %s -> ( u e. %s |-> ( _i x. u ) ) e. ( %s -cn-> CC ) )' % (AR, XC, XC))
adc = w.s([w.s([keq], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (AR, TOP, TOP, TOP))
micn = w.s([keq, adc, xcst, iu], 'cncfmpt2f', '( %s -> %s e. ( %s -cn-> CC ) )' % (AR, MI, XC))
Au = '( %s /\\ u e. %s )' % (AR, XC)
el1 = w.s([w.s([], 'eqid', '%s = %s' % (MI, MI))], 'elrnmpt1', '( ( u e. %s /\\ %s e. _V ) -> %s e. %s )' % (XC, W_, W_, SEG))
inrn0 = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au, XC)), w.s([w.s([], 'ovex', '%s e. _V' % W_)], 'a1i', '( %s -> %s e. _V )' % (Au, W_)), el1], 'syl2anc', '( %s -> %s e. %s )' % (Au, W_, SEG))
inrn = w.s([inrn0, w.s([segeq], 'a1i', '( %s -> %s = %s )' % (Au, SEG, SEGO))], 'eleqtrd', '( %s -> %s e. %s )' % (Au, W_, SEGO))
mif = w.s([inrn, w.s([], 'eqid', '%s = %s' % (MI, MI))], 'fmptd', '( %s -> %s : %s --> %s )' % (AR, MI, XC, SEGO))
segc = w.s([ssh, hp0cc(w, AR)], 'sstrd', '( %s -> %s C_ CC )' % (AR, SEGO))
mis = w.s([mif, w.s([segc, micn, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( %s e. ( %s -cn-> %s ) <-> %s : %s --> %s ) )' % (AR, MI, XC, SEGO, MI, XC, SEGO))], 'mpbird', '( %s -> %s e. ( %s -cn-> %s ) )' % (AR, MI, XC, SEGO))
co = w.s([mis, gcn], 'cncfco', '( %s -> ( %s o. %s ) e. ( %s -cn-> CC ) )' % (AR, GM, MI, XC))
gmf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (AR, GM, SEGO))
cof = w.s([gmf, inrn], 'cofmpt', '( %s -> ( %s o. %s ) = ( u e. %s |-> ( %s ` %s ) ) )' % (AR, GM, MI, XC, GM, W_))
gv = mpv(w, Au, GM, W_, '( _G ` %s )' % W_, w.s([], 'fveq2', '( z = %s -> ( _G ` z ) = ( _G ` %s ) )' % (W_, W_)), inrn, w.s([w.s([], 'fvex', '( _G ` %s ) e. _V' % W_)], 'a1i', '( %s -> ( _G ` %s ) e. _V )' % (Au, W_)), dom=SEGO)
eq = w.s([cof, w.s([gv], 'mpteq2dva', '( %s -> ( u e. %s |-> ( %s ` %s ) ) = %s )' % (AR, XC, GM, W_, GMAP))], 'eqtrd', '( %s -> ( %s o. %s ) = %s )' % (AR, GM, MI, GMAP))
res = w.s([eq, co], 'eqeltrrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (AR, GMAP, XC))
# eliminate the radius
d0 = ctx(w, A0)
xrp0 = w.s([d0['xr'], d0['xgt']], 'elrpd', '( %s -> X e. RR+ )' % A0)
ar = w.s([w.s([w.s([xrp0], 'rpreccld', '( %s -> ( 1 / X ) e. RR+ )' % A0)], 'rpred', '( %s -> ( 1 / X ) e. RR )' % A0), w.s([d0['xr'], w.s([d0['trp']], 'rpred', '( %s -> T e. RR )' % A0)], 'readdcld', '( %s -> ( X + T ) e. RR )' % A0)], 'readdcld',
         '( %s -> %s e. RR )' % (A0, ARCH))
ex = w.s([ar, w.inst('arch')], 'syl', '( %s -> E. r e. NN %s < r )' % (A0, ARCH))
w.qed([ex, w.s([res], 'rexlimdvaa', '( %s -> ( E. r e. NN %s < r -> %s e. ( %s -cn-> CC ) ) )' % (A0, ARCH, GMAP, XC))], 'mpd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GMAP, XC))
run7(w)

# ---------------------------------------------------------------- gamlibl
GA = '( abs ` ( _G ` %s ) )' % W_
QU = '( ( 1 + ( abs ` u ) ) ^ 2 )'
w = W('gamlibl', 'The line-moment integrand ` |Gamma ( X + i u )| ( 1 + |u| ) ^ 2 ` is integrable on '
      '` ( -u T , T ) ` for ` 0 < X ` ( ~ gamcnl , ~ cniccibl ).  Discharges the integrability '
      'hypothesis of ~ gamlmom .')
d = ctx(w, A0)
xr, xgt, trp = d['xr'], d['xgt'], d['trp']
cl = Closure(w, A0, {'T': ('RR+', trp)})
tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
ussr = w.s([ntr, tr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, XC))
usscn = w.s([ussr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XC))
sscc = a1(w, A0, 'ssid', 'CC C_ CC')
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
gcn = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('gamcnl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GMAP, XC))
abss = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
absf = w.s([w.s([abss, w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'sselii', 'abs e. ( CC -cn-> CC )')], 'a1i', '( %s -> abs e. ( CC -cn-> CC ) )' % A0)
gabs = w.s([absf, gcn], 'cncfmpt1f', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, GA, XC))
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( u e. %s |-> u ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
absm = w.s([absf, idc], 'cncfmpt1f', '( %s -> ( u e. %s |-> ( abs ` u ) ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
one = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( u e. %s |-> 1 ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
adc = w.s([w.s([keq], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
pl = w.s([keq, adc, one, absm], 'cncfmpt2f', '( %s -> ( u e. %s |-> ( 1 + ( abs ` u ) ) ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
sq = w.s([pl, pl], 'mulcncf', '( %s -> ( u e. %s |-> ( ( 1 + ( abs ` u ) ) x. ( 1 + ( abs ` u ) ) ) ) e. ( %s -cn-> CC ) )' % (A0, XC, XC))
Au = '( %s /\\ u e. %s )' % (A0, XC)
ur = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (Au, XC)), w.s([], 'simpr', '( %s -> u e. %s )' % (Au, XC))], 'sseldd', '( %s -> u e. RR )' % Au)
uc = w.s([ur], 'recnd', '( %s -> u e. CC )' % Au)
opr = w.s([a1(w, Au, '1re', '1 e. RR'), w.s([uc], 'abscld', '( %s -> ( abs ` u ) e. RR )' % Au)], 'readdcld', '( %s -> ( 1 + ( abs ` u ) ) e. RR )' % Au)
opc = w.s([opr], 'recnd', '( %s -> ( 1 + ( abs ` u ) ) e. CC )' % Au)
sqv = w.s([opc], 'sqvald', '( %s -> %s = ( ( 1 + ( abs ` u ) ) x. ( 1 + ( abs ` u ) ) ) )' % (Au, QU))
sqm = w.s([w.s([sqv], 'mpteq2dva', '( %s -> ( u e. %s |-> %s ) = ( u e. %s |-> ( ( 1 + ( abs ` u ) ) x. ( 1 + ( abs ` u ) ) ) ) )' % (A0, XC, QU, XC)), sq], 'eqeltrd', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, QU, XC))
gml = w.s([gabs, sqm], 'mulcncf', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XC, GML, XC))
ibl = w.s([ntr, tr, gml, w.inst('cniccibl')], 'syl3anc', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XC, GML))
# GML is a complex number on the closed interval
xru = w.s([xr], 'adantr', '( %s -> X e. RR )' % Au)
wc = cptcl(w, Au, 'X', 'u', xru, ur)
rew = w.s([xru, ur, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = X )' % (Au, W_))
gt = w.s([w.s([xgt], 'adantr', '( %s -> 0 < X )' % Au), rew], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (Au, W_))
gc = w.s([w.s([wc, gt, w.inst('zrenn')], 'syl2anc', '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (Au, W_)), w.inst('gamcl')], 'syl', '( %s -> ( _G ` %s ) e. CC )' % (Au, W_))
gmlc = w.s([w.s([w.s([gc], 'abscld', '( %s -> %s e. RR )' % (Au, GA))], 'recnd', '( %s -> %s e. CC )' % (Au, GA)), w.s([opc], 'sqcld', '( %s -> %s e. CC )' % (Au, QU))], 'mulcld', '( %s -> %s e. CC )' % (Au, GML))
w.qed([a1(w, A0, 'ioossicc', '%s C_ %s' % (XO, XC)), a1(w, A0, 'ioombl', '%s e. dom vol' % XO), gmlc, ibl], 'iblss', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A0, XO, GML))
run7(w)

# ---------------------------------------------------------------- gamlmomx
GSBG = GSB.replace('( H x. ', '( g x. ')
PH = '( g e. RR+ /\\ %s )' % GSBG
GMLC = GML.replace('( X + ( _i x. u ) )', '( c + ( _i x. u ) )')
ANT = '( %s <_ c /\\ c <_ 3 )' % HUND
ITG = 'S. ( -u b (,) b ) %s _d u' % GMLC
KK = '( ( ; ; ; 1 0 2 4 x. g ) / ( log ` 2 ) )'
BODY = lambda h: 'A. c e. RR A. b e. RR+ ( %s -> %s <_ %s )' % (ANT, ITG, h)
w = W('gamlmomx', 'The weighted Gamma line moment is bounded uniformly in the truncation height '
      'and in the abscissa over the strip ` 1 / 100 <_ c <_ 3 `: there is an absolute constant '
      '` h ` with ` S. ( -u b (,) b ) |Gamma ( c + i u )| ( 1 + |u| ) ^ 2 _d u <_ h ` for every '
      '` b `.  Lean\'s ` integral_norm_Gamma_line_le ` in truncated form with the strip constant '
      'of ~ gamstrb and the integrability of ~ gamlibl discharged.')
Q0 = '( %s /\\ ( c e. RR /\\ b e. RR+ ) )' % PH
Q = '( %s /\\ %s )' % (Q0, ANT)
cr = w.s([], 'simplrl', '( %s -> c e. RR )' % Q)
brp = w.s([], 'simplrr', '( %s -> b e. RR+ )' % Q)
ph_ = w.s([], 'simpll', '( %s -> %s )' % (Q, PH))
ant = w.s([], 'simpr', '( %s -> %s )' % (Q, ANT))
clo = w.s([ant, w.inst('simpl')], 'syl', '( %s -> %s <_ c )' % (Q, HUND))
chi = w.s([ant, w.inst('simpr')], 'syl', '( %s -> c <_ 3 )' % Q)
h1 = w.s([cr, clo, chi], '3jca', '( %s -> ( c e. RR /\\ %s <_ c /\\ c <_ 3 ) )' % (Q, HUND))
cl = Closure(w, Q, {'c': ('RR', cr)})
cgt = linarith(w, Q, [clo], '0 < c', closure=cl)
h4 = w.s([w.s([w.s([cr, cgt], 'jca', '( %s -> ( c e. RR /\\ 0 < c ) )' % Q), brp], 'jca', '( %s -> ( ( c e. RR /\\ 0 < c ) /\\ b e. RR+ ) )' % Q), w.inst('gamlibl')], 'syl', '( %s -> ( u e. ( -u b (,) b ) |-> %s ) e. L^1 )' % (Q, GMLC))
mom = w.s([h1, brp, ph_, h4], 'gamlmom', '( %s -> %s <_ %s )' % (Q, ITG, KK))
ral = w.s([w.s([mom], 'ex', '( %s -> ( %s -> %s <_ %s ) )' % (Q0, ANT, ITG, KK))], 'ralrimivva', '( %s -> %s )' % (PH, BODY(KK)))
grp = w.s([], 'simpl', '( %s -> g e. RR+ )' % PH)
l2r = w.s([a1(w, PH, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( %s -> ( log ` 2 ) e. RR )' % PH)
cl2 = Closure(w, PH, {}); cl2.leaf('( log ` 2 )', 'RR', l2r)
l2gt = linarith(w, PH, [a1(w, PH, 'log2ge', '( 1 / 2 ) <_ ( log ` 2 )')], '0 < ( log ` 2 )', closure=cl2)
l2rp = w.s([l2r, l2gt], 'elrpd', '( %s -> ( log ` 2 ) e. RR+ )' % PH)
n102 = w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; ; 1 0 2 e. NN0')
n1024 = w.s([n102, w.s([], '4nn', '4 e. NN')], 'decnncl', '; ; ; 1 0 2 4 e. NN')
kk = w.s([w.s([w.s([w.s([n1024], 'a1i', '( %s -> ; ; ; 1 0 2 4 e. NN )' % PH)], 'nnrpd', '( %s -> ; ; ; 1 0 2 4 e. RR+ )' % PH), grp], 'rpmulcld', '( %s -> ( ; ; ; 1 0 2 4 x. g ) e. RR+ )' % PH), l2rp], 'rpdivcld', '( %s -> %s e. RR+ )' % (PH, KK))
sub = w.s([w.s([w.s([w.s([], 'breq2', '( h = %s -> ( %s <_ h <-> %s <_ %s ) )' % (KK, ITG, ITG, KK))], 'imbi2d', '( h = %s -> ( ( %s -> %s <_ h ) <-> ( %s -> %s <_ %s ) ) )' % (KK, ANT, ITG, ANT, ITG, KK))], 'ralbidv',
                '( h = %s -> ( A. b e. RR+ ( %s -> %s <_ h ) <-> A. b e. RR+ ( %s -> %s <_ %s ) ) )' % (KK, ANT, ITG, ANT, ITG, KK))], 'ralbidv', '( h = %s -> ( %s <-> %s ) )' % (KK, BODY('h'), BODY(KK)))
ex = w.s([kk, ral, w.s([sub], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. h e. RR+ %s )' % (KK, BODY(KK), BODY('h')))], 'syl2anc', '( %s -> E. h e. RR+ %s )' % (PH, BODY('h')))
lim = w.s([ex], 'rexlimiva', '( E. g e. RR+ %s -> E. h e. RR+ %s )' % (GSBG, BODY('h')))
w.qed([w.s([], 'gamstrb', 'E. g e. RR+ %s' % GSBG), lim], 'ax-mp', 'E. h e. RR+ %s' % BODY('h'))
run7(w)
