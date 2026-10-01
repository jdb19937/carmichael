"""Sortie A4a, batch 2: the product over a word (closure, append)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# --------------------------------------------------------------- algprodcl
w = W('algprodcl', 'The product over a word of nonnegative integers is a nonnegative integer.')
P = 'W e. Word NN0'
ws = w.s([], 'id', '( %s -> W e. Word NN0 )' % P)
fi = w.s([w.s([], 'fzofi', '( 0 ..^ ( # ` W ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( # ` W ) ) e. Fin )' % P)
Q = '( %s /\\ i e. ( 0 ..^ ( # ` W ) ) )' % P
cl = w.s([w.s([ws], 'adantr', '( %s -> W e. Word NN0 )' % Q), w.s([], 'simpr', '( %s -> i e. ( 0 ..^ ( # ` W ) ) )' % Q), w.inst('wrdsymbcl')],
         'syl2anc', '( %s -> ( W ` i ) e. NN0 )' % Q)
w.qed([fi, cl], 'fprodnn0cl', '( %s -> %s e. NN0 )' % (P, PRD('W')))
run(w)

VW = '( V ++ W )'
PVW = PRD(VW)
CSV = '( <" P "> ++ V )'
PHI = '( W e. Word NN0 -> %s = ( %s x. %s ) )' % (PRD('( s ++ W )'), PRD('s'), PRD('W'))

# --------------------------------------------------------------- algprodccb
w = W('algprodccb', 'Base of the induction for the product over a concatenation.')
BODY = subst(PHI, 's', '(/)')
P = 'W e. Word NN0'
ws = w.s([], 'id', '( %s -> W e. Word NN0 )' % P)
lid = w.s([ws, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ W ) = W )' % P)
lhs = prdeq(w, P, '( (/) ++ W )', 'W', lid)
pc = w.s([ws, w.inst('algprodcl')], 'syl', '( %s -> %s e. NN0 )' % (P, PRD('W')))
pcc = w.s([pc], 'nn0cnd', '( %s -> %s e. CC )' % (P, PRD('W')))
z = w.s([w.s([], 'algprod0', '%s = 1' % PRD('(/)'))], 'a1i', '( %s -> %s = 1 )' % (P, PRD('(/)')))
r1 = w.s([z], 'oveq1d', '( %s -> ( %s x. %s ) = ( 1 x. %s ) )' % (P, PRD('(/)'), PRD('W'), PRD('W')))
r2 = w.s([pcc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (P, PRD('W'), PRD('W')))
rhs = w.s([r1, r2], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (P, PRD('(/)'), PRD('W'), PRD('W')))
w.qed([lhs, rhs], 'eqtr4d', BODY)
assert BODY == '( %s -> %s = ( %s x. %s ) )' % (P, PRD('( (/) ++ W )'), PRD('(/)'), PRD('W')), BODY
run(w)

# --------------------------------------------------------------- algprodccs
w = W('algprodccs', 'Step of the induction for the product over a concatenation.')
IH = subst(PHI, 's', 'V')
CO = subst(PHI, 's', CSV)
A = '( V e. %s /\\ P e. NN0 /\\ %s )' % (W0, IH)
P2 = '( %s /\\ W e. %s )' % (A, W0)
vs = w.s([], 'simpl1', '( %s -> V e. %s )' % (P2, W0))
pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % P2)
ih = w.s([], 'simpl3', '( %s -> %s )' % (P2, IH))
wsx = w.s([], 'simpr', '( %s -> W e. %s )' % (P2, W0))
ihx = w.s([ih, wsx], 'mpd', '( %s -> %s = ( %s x. %s ) )' % (P2, PVW, PRD('V'), PRD('W')))
s1 = w.s([pn, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. %s )' % (P2, W0))
vw = w.s([vs, wsx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. %s )' % (P2, VW, W0))
ass = w.s([s1, vs, wsx, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ W ) = ( <" P "> ++ %s ) )' % (P2, CSV, VW))
lhs = prdeq(w, P2, '( %s ++ W )' % CSV, '( <" P "> ++ %s )' % VW, ass)
cs1 = w.s([pn, vw, w.inst('algprodcs')], 'syl2anc', '( %s -> %s = ( P x. %s ) )' % (P2, PRD('( <" P "> ++ %s )' % VW), PVW))
cs2 = w.s([pn, vs, w.inst('algprodcs')], 'syl2anc', '( %s -> %s = ( P x. %s ) )' % (P2, PRD(CSV), PRD('V')))
pcc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % P2)
pv = w.s([w.s([vs, w.inst('algprodcl')], 'syl', '( %s -> %s e. NN0 )' % (P2, PRD('V')))], 'nn0cnd', '( %s -> %s e. CC )' % (P2, PRD('V')))
pw = w.s([w.s([wsx, w.inst('algprodcl')], 'syl', '( %s -> %s e. NN0 )' % (P2, PRD('W')))], 'nn0cnd', '( %s -> %s e. CC )' % (P2, PRD('W')))
mas = w.s([pcc, pv, pw], 'mulassd', '( %s -> ( ( P x. %s ) x. %s ) = ( P x. ( %s x. %s ) ) )' % (P2, PRD('V'), PRD('W'), PRD('V'), PRD('W')))
ch = w.s([cs1, w.s([ihx], 'oveq2d', '( %s -> ( P x. %s ) = ( P x. ( %s x. %s ) ) )' % (P2, PVW, PRD('V'), PRD('W')))], 'eqtrd',
         '( %s -> %s = ( P x. ( %s x. %s ) ) )' % (P2, PRD('( <" P "> ++ %s )' % VW), PRD('V'), PRD('W')))
rhs = w.s([w.s([cs2], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( P x. %s ) x. %s ) )' % (P2, PRD(CSV), PRD('W'), PRD('V'), PRD('W'))), mas], 'eqtrd',
          '( %s -> ( %s x. %s ) = ( P x. ( %s x. %s ) ) )' % (P2, PRD(CSV), PRD('W'), PRD('V'), PRD('W')))
fin = w.s([w.s([lhs, ch], 'eqtrd', '( %s -> %s = ( P x. ( %s x. %s ) ) )' % (P2, PRD('( %s ++ W )' % CSV), PRD('V'), PRD('W'))), rhs], 'eqtr4d',
          '( %s -> %s = ( %s x. %s ) )' % (P2, PRD('( %s ++ W )' % CSV), PRD(CSV), PRD('W')))
w.qed([fin], 'ex', '( %s -> %s )' % (A, CO))
run(w)

# --------------------------------------------------------------- algprodcc
w = W('algprodcc', 'The product over a concatenation (Lean: List.prod_append).')
st, phit = wrdind(w, PHI, 'V', 'algprodccb', 'algprodccs', prods=['( s ++ W )', 's', 'W'])
P = '( V e. %s /\\ W e. %s )' % (W0, W0)
w.qed([w.s([w.s([], 'simpl', '( %s -> V e. %s )' % (P, W0)), w.s([st], 'a1i', '( %s -> ( V e. %s -> %s ) )' % (P, W0, phit))], 'mpd',
           '( %s -> %s )' % (P, phit)), w.s([], 'simpr', '( %s -> W e. %s )' % (P, W0))], 'mpd',
      '( %s -> %s = ( %s x. %s ) )' % (P, PVW, PRD('V'), PRD('W')))
run(w)

# --------------------------------------------------------------- algranfv
w = W('algranfv', 'An indexed letter is an entry of the word.')
P = '( W e. Word S /\\ I e. ( 0 ..^ ( # ` W ) ) )'
ws = w.s([], 'simpl', '( %s -> W e. Word S )' % P)
ii = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ ( # ` W ) ) )' % P)
fn = w.s([ws, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ ( # ` W ) ) )' % P)
w.qed([fn, ii, w.inst('fnfvelrn')], 'syl2anc', '( %s -> ( W ` I ) e. ran W )' % P)
run(w)

# --------------------------------------------------------------- algprodnn
w = W('algprodnn', 'The product over a word of positive letters is positive (Lean: List.prod_pos).')
P = '( W e. Word NN0 /\\ A. q e. ran W 1 <_ q )'
ws = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % P)
al = w.s([], 'simpr', '( %s -> A. q e. ran W 1 <_ q )' % P)
fi = w.s([w.s([], 'fzofi', '( 0 ..^ ( # ` W ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( # ` W ) ) e. Fin )' % P)
Q = '( %s /\\ i e. ( 0 ..^ ( # ` W ) ) )' % P
wq = w.s([ws], 'adantr', '( %s -> W e. Word NN0 )' % Q)
iq = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ ( # ` W ) ) )' % Q)
cl = w.s([wq, iq, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` i ) e. NN0 )' % Q)
rn = w.s([wq, iq, w.inst('algranfv')], 'syl2anc', '( %s -> ( W ` i ) e. ran W )' % Q)
ge = w.s([w.s([al], 'adantr', '( %s -> A. q e. ran W 1 <_ q )' % Q), rn], 'rspcdva', '( %s -> 1 <_ ( W ` i ) )' % Q)
nn = w.s([cl, ge, w.inst('elnnnn0c')], 'sylanbrc', '( %s -> ( W ` i ) e. NN )' % Q)
w.qed([fi, nn], 'fprodnncl', '( %s -> %s e. NN )' % (P, PRD('W')))
run(w)

# --------------------------------------------------------------- algprodle
w = W('algprodle', 'The product over a word is at most the bound to the power of the length (Lean: List.prod_le_pow_card).')
P = '( ( W e. Word NN0 /\\ X e. NN0 ) /\\ A. q e. ran W q <_ X )'
ws = w.s([], 'simpll', '( %s -> W e. Word NN0 )' % P)
xn = w.s([], 'simplr', '( %s -> X e. NN0 )' % P)
al = w.s([], 'simpr', '( %s -> A. q e. ran W q <_ X )' % P)
nf = w.s([], 'nfv', 'F/ i %s' % P)
fi = w.s([w.s([], 'fzofi', '( 0 ..^ ( # ` W ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( # ` W ) ) e. Fin )' % P)
Q = '( %s /\\ i e. ( 0 ..^ ( # ` W ) ) )' % P
wq = w.s([ws], 'adantr', '( %s -> W e. Word NN0 )' % Q)
xq = w.s([xn], 'adantr', '( %s -> X e. NN0 )' % Q)
iq = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ ( # ` W ) ) )' % Q)
cl = w.s([wq, iq, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` i ) e. NN0 )' % Q)
br = w.s([cl], 'nn0red', '( %s -> ( W ` i ) e. RR )' % Q)
b0 = w.s([cl], 'nn0ge0d', '( %s -> 0 <_ ( W ` i ) )' % Q)
cr = w.s([xq], 'nn0red', '( %s -> X e. RR )' % Q)
rn = w.s([wq, iq, w.inst('algranfv')], 'syl2anc', '( %s -> ( W ` i ) e. ran W )' % Q)
le = w.s([w.s([al], 'adantr', '( %s -> A. q e. ran W q <_ X )' % Q), rn], 'rspcdva', '( %s -> ( W ` i ) <_ X )' % Q)
fl = w.s([nf, fi, br, b0, cr, le], 'fprodle', '( %s -> %s <_ prod_ i e. ( 0 ..^ ( # ` W ) ) X )' % (P, PRD('W')))
co = w.s([w.s([], 'fzofi', '( 0 ..^ ( # ` W ) ) e. Fin'), w.s([xn], 'nn0cnd', '( %s -> X e. CC )' % P), w.inst('fprodconst')], 'sylancr',
         '( %s -> prod_ i e. ( 0 ..^ ( # ` W ) ) X = ( X ^ ( # ` ( 0 ..^ ( # ` W ) ) ) ) )' % P)
hz = w.s([w.s([ws, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % P), w.inst('hashfzo0')], 'syl',
         '( %s -> ( # ` ( 0 ..^ ( # ` W ) ) ) = ( # ` W ) )' % P)
co2 = w.s([co, w.s([hz], 'oveq2d', '( %s -> ( X ^ ( # ` ( 0 ..^ ( # ` W ) ) ) ) = ( X ^ ( # ` W ) ) )' % P)], 'eqtrd',
          '( %s -> prod_ i e. ( 0 ..^ ( # ` W ) ) X = ( X ^ ( # ` W ) ) )' % P)
w.qed([fl, co2], 'breqtrd', '( %s -> %s <_ ( X ^ ( # ` W ) ) )' % (P, PRD('W')))
run(w)

# --------------------------------------------------------------- algprodrn
w = W('algprodrn', 'The product over a duplicate-free word is the product over its entries (Lean: List.prod_toFinset).')
P = "( W e. Word NN0 /\\ Fun `' W )"
FZW = '( 0 ..^ ( # ` W ) )'
ws = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % P)
fu = w.s([], 'simpr', "( %s -> Fun `' W )" % P)
fn = w.s([ws, w.inst('wrdfn')], 'syl', '( %s -> W Fn %s )' % (P, FZW))
fo = w.s([fn, w.inst('dffn4')], 'sylib', '( %s -> W : %s -onto-> ran W )' % (P, FZW))
ff = w.s([ws, w.inst('wrdf')], 'syl', '( %s -> W : %s --> NN0 )' % (P, FZW))
f1 = w.s([w.s([ff, fu], 'jca', "( %s -> ( W : %s --> NN0 /\\ Fun `' W ) )" % (P, FZW)), w.inst('df-f1')], 'sylibr',
         '( %s -> W : %s -1-1-> NN0 )' % (P, FZW))
f1r = w.s([w.s([f1, w.inst('f1f1orn')], 'syl', '( %s -> W : %s -1-1-onto-> ran W )' % (P, FZW))], 'id',
          '( %s -> W : %s -1-1-onto-> ran W )' % (P, FZW)) if False else w.s([f1, w.inst('f1f1orn')], 'syl', '( %s -> W : %s -1-1-onto-> ran W )' % (P, FZW))
h1 = w.s([], 'id', '( q = ( W ` i ) -> q = ( W ` i ) )')
h2 = w.s([w.s([], 'fzofi', '%s e. Fin' % FZW)], 'a1i', '( %s -> %s e. Fin )' % (P, FZW))
h4 = w.s([], 'eqidd', '( ( %s /\\ i e. %s ) -> ( W ` i ) = ( W ` i ) )' % (P, FZW))
R = '( %s /\\ q e. ran W )' % P
h5 = w.s([w.s([w.s([w.s([ws], 'adantr', '( %s -> W e. Word NN0 )' % R), w.s([], 'simpr', '( %s -> q e. ran W )' % R)], 'jca',
                   '( %s -> ( W e. Word NN0 /\\ q e. ran W ) )' % R), w.inst('algwrdrn')], 'syl', '( %s -> q e. NN0 )' % R)], 'nn0cnd',
         '( %s -> q e. CC )' % R)
f = w.s([h1, h2, f1r, h4, h5], 'fprodf1o', '( %s -> prod_ q e. ran W q = %s )' % (P, PRD('W')))
w.qed([f], 'eqcomd', '( %s -> %s = prod_ q e. ran W q )' % (P, PRD('W')))
run(w)

# --------------------------------------------------------------- algdvdprod
w = W('algdvdprod', 'Every entry of a word divides its product (Lean: List.dvd_prod).')
P = '( W e. Word NN0 /\\ Q e. ran W )'
FZW = '( 0 ..^ ( # ` W ) )'
ws = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % P)
qq = w.s([], 'simpr', '( %s -> Q e. ran W )' % P)
fn = w.s([ws, w.inst('wrdfn')], 'syl', '( %s -> W Fn %s )' % (P, FZW))
ex = w.s([w.s([fn, w.inst('fvelrnb')], 'syl', '( %s -> ( Q e. ran W <-> E. j e. %s ( W ` j ) = Q ) )' % (P, FZW)), qq], 'mpbid',
         '( %s -> E. j e. %s ( W ` j ) = Q )' % (P, FZW))
R = '( %s /\\ ( j e. %s /\\ ( W ` j ) = Q ) )' % (P, FZW)
wr = w.s([ws], 'adantr', '( %s -> W e. Word NN0 )' % R)
jf = w.s([], 'simprl', '( %s -> j e. %s )' % (R, FZW))
jq = w.s([], 'simprr', '( %s -> ( W ` j ) = Q )' % R)
fi = w.s([w.s([], 'fzofi', '%s e. Fin' % FZW)], 'a1i', '( %s -> %s e. Fin )' % (R, FZW))
S = '( %s /\\ i e. %s )' % (R, FZW)
bcc = w.s([w.s([w.s([wr], 'adantr', '( %s -> W e. Word NN0 )' % S), w.s([], 'simpr', '( %s -> i e. %s )' % (S, FZW)), w.inst('wrdsymbcl')],
              'syl2anc', '( %s -> ( W ` i ) e. NN0 )' % S)], 'nn0cnd', '( %s -> ( W ` i ) e. CC )' % S)
sub = w.s([w.s([], 'simpr', '( ( %s /\\ i = j ) -> i = j )' % R)], 'fveq2d', '( ( %s /\\ i = j ) -> ( W ` i ) = ( W ` j ) )' % R)
sp = w.s([fi, bcc, jf, sub], 'fprodsplit1', '( %s -> %s = ( ( W ` j ) x. prod_ i e. ( %s \\ { j } ) ( W ` i ) ) )' % (R, PRD('W'), FZW))
sp2 = w.s([sp, w.s([jq], 'oveq1d', '( %s -> ( ( W ` j ) x. prod_ i e. ( %s \\ { j } ) ( W ` i ) ) = ( Q x. prod_ i e. ( %s \\ { j } ) ( W ` i ) ) )' % (R, FZW, FZW))], 'eqtrd',
          '( %s -> %s = ( Q x. prod_ i e. ( %s \\ { j } ) ( W ` i ) ) )' % (R, PRD('W'), FZW))
# the remaining product is an integer
dfi = w.s([w.s([], 'fzofi', '%s e. Fin' % FZW), w.inst('diffi')], 'ax-mp', '( %s \\ { j } ) e. Fin' % FZW)
dfia = w.s([dfi], 'a1i', '( %s -> ( %s \\ { j } ) e. Fin )' % (R, FZW))
T = '( %s /\\ i e. ( %s \\ { j } ) )' % (R, FZW)
idif = w.s([w.s([], 'simpr', '( %s -> i e. ( %s \\ { j } ) )' % (T, FZW)), w.inst('eldifi')], 'syl', '( %s -> i e. %s )' % (T, FZW))
bnn = w.s([w.s([wr], 'adantr', '( %s -> W e. Word NN0 )' % T), idif, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` i ) e. NN0 )' % T)
rest = w.s([dfia, bnn], 'fprodnn0cl', '( %s -> prod_ i e. ( %s \\ { j } ) ( W ` i ) e. NN0 )' % (R, FZW))
restz = w.s([rest], 'nn0zd', '( %s -> prod_ i e. ( %s \\ { j } ) ( W ` i ) e. ZZ )' % (R, FZW))
qz = w.s([w.s([w.s([wr, w.s([qq], 'adantr', '( %s -> Q e. ran W )' % R)], 'jca', '( %s -> ( W e. Word NN0 /\\ Q e. ran W ) )' % R),
               w.inst('algwrdrn')], 'syl', '( %s -> Q e. NN0 )' % R)], 'nn0zd', '( %s -> Q e. ZZ )' % R)
dv = w.s([qz, restz, w.inst('dvdsmul1')], 'syl2anc', '( %s -> Q || ( Q x. prod_ i e. ( %s \\ { j } ) ( W ` i ) ) )' % (R, FZW))
dv2 = w.s([sp2, dv], 'breqtrrd', '( %s -> Q || %s )' % (R, PRD('W')))
w.qed([w.s([dv2], 'rexlimdvaa', '( %s -> ( E. j e. %s ( W ` j ) = Q -> Q || %s ) )' % (P, FZW, PRD('W'))), ex], 'mpd', '( %s -> Q || %s )' % (P, PRD('W')))
run(w)
