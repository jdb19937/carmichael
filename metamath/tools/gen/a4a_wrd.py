"""Sortie A4a, batch 1: the word library (Mathlib's List lemmas under the
Word NN0 encoding).  MM_DB=sorties/a4a.mm python3 tools/gen/a4a_wrd.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1lib
from tm import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CS = '( <" P "> ++ W )'
def PRD(x, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, x, x, i)

# --------------------------------------------------------------- algwrdrn
w = W('algwrdrn', 'An element of a word lies in the alphabet (Lean: typing of a List membership).')
P = '( W e. Word S /\\ Q e. ran W )'
ww = w.s([], 'simpl', '( %s -> W e. Word S )' % P)
qq = w.s([], 'simpr', '( %s -> Q e. ran W )' % P)
f = w.s([ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> S )' % P)
ss = w.s([f, w.inst('frn')], 'syl', '( %s -> ran W C_ S )' % P)
w.qed([ss, qq], 'sseldd', '( %s -> Q e. S )' % P)
run(w)

# --------------------------------------------------------------- algwrdfi
w = W('algwrdfi', 'The set of entries of a word is finite (Lean: List.toFinset).')
P = 'W e. Word S'
i = w.s([], 'id', '( %s -> W e. Word S )' % P)
fn = w.s([i, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ ( # ` W ) ) )' % P)
fi = w.s([], 'fzofi', '( 0 ..^ ( # ` W ) ) e. Fin')
fia = w.s([fi], 'a1i', '( %s -> ( 0 ..^ ( # ` W ) ) e. Fin )' % P)
wf = w.s([fn, fia, w.inst('fnfi')], 'syl2anc', '( %s -> W e. Fin )' % P)
w.qed([wf, w.inst('rnfi')], 'syl', '( %s -> ran W e. Fin )' % P)
run(w)

# --------------------------------------------------------------- algrncs
w = W('algrncs', 'The entries of a cons (Lean: List.mem_cons, as a range).')
P = '( P e. V /\\ W e. Word V )'
pp = w.s([], 'simpl', '( %s -> P e. V )' % P)
ww = w.s([], 'simpr', '( %s -> W e. Word V )' % P)
s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word V )' % P)
rc = w.s([s1, ww, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran <" P "> u. ran W ) )' % (P, CS))
sr = w.s([pp, w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % P)
un = w.s([sr], 'uneq1d', '( %s -> ( ran <" P "> u. ran W ) = ( { P } u. ran W ) )' % P)
w.qed([rc, un], 'eqtrd', '( %s -> ran %s = ( { P } u. ran W ) )' % (P, CS))
run(w)

# --------------------------------------------------------------- algelcs
w = W('algelcs', 'Membership in a cons (Lean: List.mem_cons).')
P = '( ( P e. NN0 /\\ W e. Word NN0 ) /\\ Q e. NN0 )'
pw = w.s([], 'simpl', '( %s -> ( P e. NN0 /\\ W e. Word NN0 ) )' % P)
qq = w.s([], 'simpr', '( %s -> Q e. NN0 )' % P)
rc = w.s([pw, w.inst('algrncs')], 'syl', '( %s -> ran %s = ( { P } u. ran W ) )' % (P, CS))
b1 = w.s([rc], 'eleq2d', '( %s -> ( Q e. ran %s <-> Q e. ( { P } u. ran W ) ) )' % (P, CS))
b2 = w.s([], 'elun', '( Q e. ( { P } u. ran W ) <-> ( Q e. { P } \\/ Q e. ran W ) )')
b2a = w.s([b2], 'a1i', '( %s -> ( Q e. ( { P } u. ran W ) <-> ( Q e. { P } \\/ Q e. ran W ) ) )' % P)
b3 = w.s([qq, w.inst('elsng')], 'syl', '( %s -> ( Q e. { P } <-> Q = P ) )' % P)
b4 = w.s([b3], 'orbi1d', '( %s -> ( ( Q e. { P } \\/ Q e. ran W ) <-> ( Q = P \\/ Q e. ran W ) ) )' % P)
w.qed([b1, b2a, b4], '3bitrd', '( %s -> ( Q e. ran %s <-> ( Q = P \\/ Q e. ran W ) ) )' % (P, CS))
run(w)

# --------------------------------------------------------------- alglencs
w = W('alglencs', 'The length of a cons (Lean: List.length_cons).')
P = '( P e. V /\\ W e. Word V )'
pp = w.s([], 'simpl', '( %s -> P e. V )' % P)
ww = w.s([], 'simpr', '( %s -> W e. Word V )' % P)
s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word V )' % P)
cl = w.s([s1, ww, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" P "> ) + ( # ` W ) ) )' % (P, CS))
sl = w.s([w.s([], 's1len', '( # ` <" P "> ) = 1')], 'a1i', '( %s -> ( # ` <" P "> ) = 1 )' % P)
e1 = w.s([sl], 'oveq1d', '( %s -> ( ( # ` <" P "> ) + ( # ` W ) ) = ( 1 + ( # ` W ) )  )' % P)
lc = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % P)
lcc = w.s([lc], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % P)
o1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % P)
cm = w.s([o1, lcc], 'addcomd', '( %s -> ( 1 + ( # ` W ) ) = ( ( # ` W ) + 1 ) )' % P)
w.qed([cl, e1, cm], '3eqtrd', '( %s -> ( # ` %s ) = ( ( # ` W ) + 1 ) )' % (P, CS))
run(w)

# --------------------------------------------------------------- algndp0
w = W('algndp0', 'The empty word has no repeats (Lean: List.nodup_nil).')
c = w.s([], 'cnv0', "`' (/) = (/)")
f = w.s([], 'fun0', 'Fun (/)')
b = w.s([c], 'funeqi', "( Fun `' (/) <-> Fun (/) )")
w.qed([b, f], 'mpbir', "Fun `' (/)")
run(w)

FZ = '( 0 ..^ ( # ` W ) )'

def wbasics(w, ante, ws, alpha='S', var='W'):
    """from ws: ( ante -> W e. Word S ): fn, fo, dom-finite, ran-finite, ( # ` ( 0 ..^ ( # ` W ) ) ) = ( # ` W )"""
    fz = '( 0 ..^ ( # ` %s ) )' % var
    fn = w.s([ws, w.inst('wrdfn')], 'syl', '( %s -> %s Fn %s )' % (ante, var, fz))
    fo = w.s([fn, w.inst('dffn4')], 'sylib', '( %s -> %s : %s -onto-> ran %s )' % (ante, var, fz, var))
    dfi = w.s([w.s([], 'fzofi', '%s e. Fin' % fz)], 'a1i', '( %s -> %s e. Fin )' % (ante, fz))
    rfi = w.s([ws, w.inst('algwrdfi')], 'syl', '( %s -> ran %s e. Fin )' % (ante, var))
    lc = w.s([ws, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ante, var))
    hz = w.s([lc, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ante, fz, var))
    return fn, fo, dfi, rfi, lc, hz

# --------------------------------------------------------------- algndpcard
w = W('algndpcard', 'A word has no repeats exactly when its entries are as many as its letters (Lean: List.toFinset_card_of_nodup, both directions).')
P = 'W e. Word S'
ws = w.s([], 'id', '( %s -> W e. Word S )' % P)
fn, fo, dfi, rfi, lc, hz = wbasics(w, P, ws)
wex = w.s([w.s([], 'wrdfin', '( W e. Word S -> W e. Fin )')], 'imp' if False else 'syl', '( %s -> W e. Fin )' % P)
# forward
Q = '( %s /\\ Fun `' + "' W )"
Q = Q % P
wsq = w.s([ws], 'adantr', '( %s -> W e. Word S )' % Q)
fq = w.s([], 'simpr', "( %s -> Fun `' W )" % Q)
ffq = w.s([wsq, w.inst('wrdf')], 'syl', '( %s -> W : %s --> S )' % (Q, FZ))
f1q = w.s([w.s([ffq, fq], 'jca', "( %s -> ( W : %s --> S /\\ Fun `' W ) )" % (Q, FZ)), w.inst('df-f1')], 'sylibr',
          '( %s -> W : %s -1-1-> S )' % (Q, FZ))
wfq = w.s([wex], 'adantr', '( %s -> W e. Fin )' % Q)
hq = w.s([wfq, f1q, w.inst('hashf1dmrn')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` ran W ) )' % (Q, FZ))
hzq = w.s([hz], 'adantr', '( %s -> ( # ` %s ) = ( # ` W ) )' % (Q, FZ))
fwd = w.s([hq, hzq], 'eqtr3d', '( %s -> ( # ` ran W ) = ( # ` W ) )' % Q)
fwd2 = w.s([fwd], 'ex', "( %s -> ( Fun `' W -> ( # ` ran W ) = ( # ` W ) ) )" % P)
# backward
R = '( %s /\\ ( # ` ran W ) = ( # ` W ) )' % P
hr = w.s([], 'simpr', '( %s -> ( # ` ran W ) = ( # ` W ) )' % R)
hzr = w.s([hz], 'adantr', '( %s -> ( # ` %s ) = ( # ` W ) )' % (R, FZ))
eqr = w.s([hzr, hr], 'eqtr4d', '( %s -> ( # ` %s ) = ( # ` ran W ) )' % (R, FZ))
dfir = w.s([dfi], 'adantr', '( %s -> %s e. Fin )' % (R, FZ))
rfir = w.s([rfi], 'adantr', '( %s -> ran W e. Fin )' % R)
enr = w.s([w.s([dfir, rfir, w.inst('hashen')], 'syl2anc', '( %s -> ( ( # ` %s ) = ( # ` ran W ) <-> %s ~~ ran W ) )' % (R, FZ, FZ)), eqr], 'mpbid',
          '( %s -> %s ~~ ran W )' % (R, FZ))
for_ = w.s([fo], 'adantr', '( %s -> W : %s -onto-> ran W )' % (R, FZ))
f1o = w.s([for_, enr, rfir, w.inst('fofinf1o')], 'syl3anc', '( %s -> W : %s -1-1-onto-> ran W )' % (R, FZ))
f1r = w.s([f1o, w.inst('f1of1')], 'syl', '( %s -> W : %s -1-1-> ran W )' % (R, FZ))
funr = w.s([w.s([f1r, w.inst('df-f1')], 'sylib', "( %s -> ( W : %s --> ran W /\\ Fun `' W ) )" % (R, FZ))], 'simprd', "( %s -> Fun `' W )" % R)
bwd = w.s([funr], 'ex', "( %s -> ( ( # ` ran W ) = ( # ` W ) -> Fun `' W ) )" % P)
w.qed([fwd2, bwd], 'impbid', "( %s -> ( Fun `' W <-> ( # ` ran W ) = ( # ` W ) ) )" % P)
run(w)

# --------------------------------------------------------------- algwrdcard
w = W('algwrdcard', 'A duplicate-free word has as many entries as letters (Lean: List.toFinset_card_of_nodup).')
P = "( W e. Word S /\\ Fun `' W )"
ws = w.s([], 'simpl', '( %s -> W e. Word S )' % P)
fq = w.s([], 'simpr', "( %s -> Fun `' W )" % P)
b = w.s([ws, w.inst('algndpcard')], 'syl', "( %s -> ( Fun `' W <-> ( # ` ran W ) = ( # ` W ) ) )" % P)
w.qed([b, fq], 'mpbid', '( %s -> ( # ` ran W ) = ( # ` W ) )' % P)
run(w)

# --------------------------------------------------------------- algrnle
w = W('algrnle', 'A word has at most as many entries as letters.')
P = 'W e. Word S'
ws = w.s([], 'id', '( %s -> W e. Word S )' % P)
fn, fo, dfi, rfi, lc, hz = wbasics(w, P, ws)
dom = w.s([dfi, fo, w.inst('fodomfi')], 'syl2anc', '( %s -> ran W ~<_ %s )' % (P, FZ))
h = w.s([dom, w.inst('hashdomi')], 'syl', '( %s -> ( # ` ran W ) <_ ( # ` %s ) )' % (P, FZ))
w.qed([h, hz], 'breqtrd', '( %s -> ( # ` ran W ) <_ ( # ` W ) )' % P)
run(w)

# --------------------------------------------------------------- algwrdss
w = W('algwrdss', 'A duplicate-free word whose entries lie in another word is no longer (Lean: List.Subperm.length_le of List.subperm_of_subset).')
P = "( ( V e. Word S /\\ W e. Word S ) /\\ ( Fun `' V /\\ ran V C_ ran W ) )"
vs = w.s([], 'simpll', '( %s -> V e. Word S )' % P)
wsx = w.s([], 'simplr', '( %s -> W e. Word S )' % P)
fv = w.s([], 'simprl', "( %s -> Fun `' V )" % P)
sub = w.s([], 'simprr', '( %s -> ran V C_ ran W )' % P)
c1 = w.s([vs, fv, w.inst('algwrdcard')], 'syl2anc', '( %s -> ( # ` ran V ) = ( # ` V ) )' % P)
rfi = w.s([wsx, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % P)
c2 = w.s([rfi, sub, w.inst('hashss')], 'syl2anc', '( %s -> ( # ` ran V ) <_ ( # ` ran W ) )' % P)
c3 = w.s([wsx, w.inst('algrnle')], 'syl', '( %s -> ( # ` ran W ) <_ ( # ` W ) )' % P)
lv = w.s([w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % P)], 'nn0red', '( %s -> ( # ` V ) e. RR )' % P)
lrw = w.s([w.s([w.s([wsx, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % P), w.inst('hashcl')], 'syl', '( %s -> ( # ` ran W ) e. NN0 )' % P)], 'nn0red', '( %s -> ( # ` ran W ) e. RR )' % P)
lw = w.s([w.s([wsx, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % P)], 'nn0red', '( %s -> ( # ` W ) e. RR )' % P)
c2b = w.s([c1, c2], 'eqbrtrrd', '( %s -> ( # ` V ) <_ ( # ` ran W ) )' % P)
w.qed([lv, lrw, lw, c2b, c3], 'letrd', '( %s -> ( # ` V ) <_ ( # ` W ) )' % P)
run(w)

# --------------------------------------------------------------- algndpcs
w = W('algndpcs', 'A cons has no repeats exactly when the head is new and the tail has none (Lean: List.nodup_cons).')
P = '( P e. NN0 /\\ W e. Word NN0 )'
pp = w.s([], 'simpl', '( %s -> P e. NN0 )' % P)
ww = w.s([], 'simpr', '( %s -> W e. Word NN0 )' % P)
s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % P)
cc = w.s([s1, ww, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (P, CS))
bc = w.s([cc, w.inst('algndpcard')], 'syl', "( %s -> ( Fun `' %s <-> ( # ` ran %s ) = ( # ` %s ) ) )" % (P, CS, CS, CS))
rc = w.s([], 'algrncs', '( %s -> ran %s = ( { P } u. ran W ) )' % (P, CS))
lcs = w.s([], 'alglencs', '( %s -> ( # ` %s ) = ( ( # ` W ) + 1 ) )' % (P, CS))
b2 = w.s([rc], 'fveq2d', '( %s -> ( # ` ran %s ) = ( # ` ( { P } u. ran W ) ) )' % (P, CS))
b3 = w.s([b2, lcs], 'eqeq12d', '( %s -> ( ( # ` ran %s ) = ( # ` %s ) <-> ( # ` ( { P } u. ran W ) ) = ( ( # ` W ) + 1 ) ) )' % (P, CS, CS))
bmain = w.s([bc, b3], 'bitrd', "( %s -> ( Fun `' %s <-> ( # ` ( { P } u. ran W ) ) = ( ( # ` W ) + 1 ) ) )" % (P, CS))
lc = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % P)
rfi = w.s([ww, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % P)
rcl = w.s([rfi, w.inst('hashcl')], 'syl', '( %s -> ( # ` ran W ) e. NN0 )' % P)
# ---- case -. P e. ran W
A = '( %s /\\ -. P e. ran W )' % P
bma = w.s([bmain], 'adantr', "( %s -> ( Fun `' %s <-> ( # ` ( { P } u. ran W ) ) = ( ( # ` W ) + 1 ) ) )" % (A, CS))
uc = w.s([w.s([], 'uncom', '( { P } u. ran W ) = ( ran W u. { P } )')], 'a1i', '( %s -> ( { P } u. ran W ) = ( ran W u. { P } ) )' % A)
hu = w.s([w.s([w.s([pp], 'adantr', '( %s -> P e. NN0 )' % A), w.inst('hashunsng')], 'syl',
             '( %s -> ( ( ran W e. Fin /\\ -. P e. ran W ) -> ( # ` ( ran W u. { P } ) ) = ( ( # ` ran W ) + 1 ) ) )' % A),
           w.s([w.s([rfi], 'adantr', '( %s -> ran W e. Fin )' % A), w.s([], 'simpr', '( %s -> -. P e. ran W )' % A)], 'jca',
               '( %s -> ( ran W e. Fin /\\ -. P e. ran W ) )' % A)], 'mpd',
          '( %s -> ( # ` ( ran W u. { P } ) ) = ( ( # ` ran W ) + 1 ) )' % A)
uc2 = w.s([uc], 'fveq2d', '( %s -> ( # ` ( { P } u. ran W ) ) = ( # ` ( ran W u. { P } ) ) )' % A)
hu2 = w.s([uc2, hu], 'eqtrd', '( %s -> ( # ` ( { P } u. ran W ) ) = ( ( # ` ran W ) + 1 ) )' % A)
ba = w.s([hu2], 'eqeq1d', '( %s -> ( ( # ` ( { P } u. ran W ) ) = ( ( # ` W ) + 1 ) <-> ( ( # ` ran W ) + 1 ) = ( ( # ` W ) + 1 ) ) )' % A)
rcla = w.s([w.s([rcl], 'adantr', '( %s -> ( # ` ran W ) e. NN0 )' % A)], 'nn0cnd', '( %s -> ( # ` ran W ) e. CC )' % A)
lca = w.s([w.s([lc], 'adantr', '( %s -> ( # ` W ) e. NN0 )' % A)], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % A)
one = w.s([], '1cnd', '( %s -> 1 e. CC )' % A)
bb = w.s([rcla, lca, one], 'addcan2ad' if False else 'addcan2d', '( %s -> ( ( ( # ` ran W ) + 1 ) = ( ( # ` W ) + 1 ) <-> ( # ` ran W ) = ( # ` W ) ) )' % A)
bcard = w.s([w.s([ww], 'adantr', '( %s -> W e. Word NN0 )' % A), w.inst('algndpcard')], 'syl',
            "( %s -> ( Fun `' W <-> ( # ` ran W ) = ( # ` W ) ) )" % A)
lhs = w.s([bma, ba, bb], '3bitrd', "( %s -> ( Fun `' %s <-> ( # ` ran W ) = ( # ` W ) ) )" % (A, CS))
lhs2 = w.s([lhs, bcard], 'bitr4d', "( %s -> ( Fun `' %s <-> Fun `' W ) )" % (A, CS))
rhs = w.s([w.s([], 'simpr', '( %s -> -. P e. ran W )' % A)], 'biantrurd', "( %s -> ( Fun `' W <-> ( -. P e. ran W /\\ Fun `' W ) ) )" % A)
casea = w.s([lhs2, rhs], 'bitrd', "( %s -> ( Fun `' %s <-> ( -. P e. ran W /\\ Fun `' W ) ) )" % (A, CS))
# ---- case P e. ran W
B = '( %s /\\ P e. ran W )' % P
bmb = w.s([bmain], 'adantr', "( %s -> ( Fun `' %s <-> ( # ` ( { P } u. ran W ) ) = ( ( # ` W ) + 1 ) ) )" % (B, CS))
pin = w.s([], 'simpr', '( %s -> P e. ran W )' % B)
sn = w.s([w.s([w.s([pp], 'adantr', '( %s -> P e. NN0 )' % B), pin], 'jca', '( %s -> ( P e. NN0 /\\ P e. ran W ) )' % B),
          w.inst('snssd' if False else 'snssi')], 'syl' if False else 'syl', '( %s -> { P } C_ ran W )' % B) if False else \
     w.s([pin], 'snssd', '( %s -> { P } C_ ran W )' % B)
ueq = w.s([w.s([sn, w.inst('ssequn1')], 'sylib', '( %s -> ( { P } u. ran W ) = ran W )' % B)], 'fveq2d',
          '( %s -> ( # ` ( { P } u. ran W ) ) = ( # ` ran W ) )' % B)
rleb = w.s([w.s([ww], 'adantr', '( %s -> W e. Word NN0 )' % B), w.inst('algrnle')], 'syl', '( %s -> ( # ` ran W ) <_ ( # ` W ) )' % B)
rclb = w.s([w.s([rcl], 'adantr', '( %s -> ( # ` ran W ) e. NN0 )' % B)], 'nn0red', '( %s -> ( # ` ran W ) e. RR )' % B)
lcb = w.s([w.s([lc], 'adantr', '( %s -> ( # ` W ) e. NN0 )' % B)], 'nn0red', '( %s -> ( # ` W ) e. RR )' % B)
lt1 = w.s([lcb], 'ltp1d', '( %s -> ( # ` W ) < ( ( # ` W ) + 1 ) )' % B)
lcb1 = w.s([lcb, w.s([], '1red', '( %s -> 1 e. RR )' % B)], 'readdcld', '( %s -> ( ( # ` W ) + 1 ) e. RR )' % B)
ltb = w.s([rclb, lcb, lcb1, rleb, lt1], 'lelttrd', '( %s -> ( # ` ran W ) < ( ( # ` W ) + 1 ) )' % B)
neb = w.s([ltb], 'ltned', '( %s -> ( # ` ran W ) =/= ( ( # ` W ) + 1 ) )' % B)
nfb = w.s([ueq, neb], 'eqnetrd', '( %s -> ( # ` ( { P } u. ran W ) ) =/= ( ( # ` W ) + 1 ) )' % B)
nfb2 = w.s([nfb], 'neneqd', '( %s -> -. ( # ` ( { P } u. ran W ) ) = ( ( # ` W ) + 1 ) )' % B)
nlhs = w.s([bmb, nfb2], 'mtbird', "( %s -> -. Fun `' %s )" % (B, CS))
nrhs = w.s([w.s([pin], 'notnotd' if False else 'pm2.24d', '')] if False else [], '', '') if False else \
       w.s([w.s([w.s([], 'simpr', '( %s -> P e. ran W )' % B)], 'notnotd', '( %s -> -. -. P e. ran W )' % B)], 'intnanrd',
           "( %s -> -. ( -. P e. ran W /\\ Fun `' W ) )" % B)
caseb = w.s([nlhs, nrhs], '2falsed', "( %s -> ( Fun `' %s <-> ( -. P e. ran W /\\ Fun `' W ) ) )" % (B, CS))
w.qed([caseb, casea], 'pm2.61dan', "( %s -> ( Fun `' %s <-> ( -. P e. ran W /\\ Fun `' W ) ) )" % (P, CS))
run(w)

# --------------------------------------------------------------- algndpccr
w = W('algndpccr', 'The concatenation of two duplicate-free words with disjoint entries has no repeats (Lean: List.nodup_append).')
CC2 = '( V ++ W )'
P = "( ( V e. Word NN0 /\\ W e. Word NN0 ) /\\ ( ( Fun `' V /\\ Fun `' W ) /\\ ( ran V i^i ran W ) = (/) ) )"
vs = w.s([], 'simpll', '( %s -> V e. Word NN0 )' % P)
wsx = w.s([], 'simplr', '( %s -> W e. Word NN0 )' % P)
fv = w.s([], 'simprll', "( %s -> Fun `' V )" % P)
fw = w.s([], 'simprlr', "( %s -> Fun `' W )" % P)
dj = w.s([], 'simprr', '( %s -> ( ran V i^i ran W ) = (/) )' % P)
cc = w.s([vs, wsx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (P, CC2))
rc = w.s([vs, wsx, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran V u. ran W ) )' % (P, CC2))
vfi = w.s([vs, w.inst('algwrdfi')], 'syl', '( %s -> ran V e. Fin )' % P)
wfi = w.s([wsx, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % P)
hu = w.s([vfi, wfi, dj, w.inst('hashun')], 'syl3anc', '( %s -> ( # ` ( ran V u. ran W ) ) = ( ( # ` ran V ) + ( # ` ran W ) ) )' % P)
cv = w.s([vs, fv, w.inst('algwrdcard')], 'syl2anc', '( %s -> ( # ` ran V ) = ( # ` V ) )' % P)
cw = w.s([wsx, fw, w.inst('algwrdcard')], 'syl2anc', '( %s -> ( # ` ran W ) = ( # ` W ) )' % P)
sum_ = w.s([cv, cw], 'oveq12d', '( %s -> ( ( # ` ran V ) + ( # ` ran W ) ) = ( ( # ` V ) + ( # ` W ) ) )' % P)
cl = w.s([vs, wsx, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + ( # ` W ) ) )' % (P, CC2))
h1 = w.s([w.s([rc], 'fveq2d', '( %s -> ( # ` ran %s ) = ( # ` ( ran V u. ran W ) ) )' % (P, CC2)), hu, sum_], '3eqtrd',
         '( %s -> ( # ` ran %s ) = ( ( # ` V ) + ( # ` W ) ) )' % (P, CC2))
h2 = w.s([h1, cl], 'eqtr4d', '( %s -> ( # ` ran %s ) = ( # ` %s ) )' % (P, CC2, CC2))
w.qed([w.s([cc, w.inst('algndpcard')], 'syl', "( %s -> ( Fun `' %s <-> ( # ` ran %s ) = ( # ` %s ) ) )" % (P, CC2, CC2, CC2)), h2], 'mpbird',
      "( %s -> Fun `' %s )" % (P, CC2))
run(w)

Z = CS
def PR(x, i='i'): return 'prod_ %s e. ( 0 ..^ ( # ` %s ) ) ( %s ` %s )' % (i, x, x, i)

# --------------------------------------------------------------- algcsfv0
w = W('algcsfv0', 'The head of a cons (Lean: List.head).')
P = '( P e. V /\\ W e. Word V )'
pp = w.s([], 'simpl', '( %s -> P e. V )' % P)
ww = w.s([], 'simpr', '( %s -> W e. Word V )' % P)
s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word V )' % P)
sl = w.s([w.s([], 's1len', '( # ` <" P "> ) = 1')], 'a1i', '( %s -> ( # ` <" P "> ) = 1 )' % P)
z1 = w.s([w.s([w.s([], 'fzo01', '( 0 ..^ 1 ) = { 0 }')], 'eqcomi', '{ 0 } = ( 0 ..^ 1 )'),
          w.s([], '0ex', '0 e. _V')], 'eleqtrri' if False else 'jctil', '') if False else None
zin = w.s([w.s([], 'c0ex', '0 e. _V')], 'snid' if False else 'elexi', '') if False else None
i0 = w.s([w.s([], 'fzo01', '( 0 ..^ 1 ) = { 0 }')], 'eqcomd' if False else 'a1i', '( %s -> ( 0 ..^ 1 ) = { 0 } )' % P)
mem = w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % P)
i0b = w.s([sl], 'oveq2d', '( %s -> ( 0 ..^ ( # ` <" P "> ) ) = ( 0 ..^ 1 ) )' % P)
i0c = w.s([i0b, i0], 'eqtrd', '( %s -> ( 0 ..^ ( # ` <" P "> ) ) = { 0 } )' % P)
sn0 = w.s([w.s([], 'c0ex', '0 e. _V'), ], 'snid', '0 e. { 0 }')
sn0a = w.s([sn0], 'a1i', '( %s -> 0 e. { 0 } )' % P)
inm = w.s([sn0a, i0c], 'eleqtrrd', '( %s -> 0 e. ( 0 ..^ ( # ` <" P "> ) ) )' % P)
cv = w.s([s1, ww, inm, w.inst('ccatval1')], 'syl3anc', '( %s -> ( %s ` 0 ) = ( <" P "> ` 0 ) )' % (P, Z))
sf = w.s([pp, w.inst('s1fv')], 'syl', '( %s -> ( <" P "> ` 0 ) = P )' % P)
w.qed([cv, sf], 'eqtrd', '( %s -> ( %s ` 0 ) = P )' % (P, Z))
run(w)

# --------------------------------------------------------------- algcsfvp1
w = W('algcsfvp1', 'The entries of a cons past the head (Lean: List.get of a cons).')
P = '( ( P e. V /\\ W e. Word V ) /\\ J e. ( 0 ..^ ( # ` W ) ) )'
pp = w.s([], 'simpll', '( %s -> P e. V )' % P)
ww = w.s([], 'simplr', '( %s -> W e. Word V )' % P)
jj = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` W ) ) )' % P)
s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word V )' % P)
sl = w.s([w.s([], 's1len', '( # ` <" P "> ) = 1')], 'a1i', '( %s -> ( # ` <" P "> ) = 1 )' % P)
# ( J + 1 ) e. ( 1 ..^ ( 1 + ( # ` W ) ) )
j1 = w.s([jj, w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % P), w.inst('fzoaddel')], 'syl2anc',
         '( %s -> ( J + 1 ) e. ( ( 0 + 1 ) ..^ ( ( # ` W ) + 1 ) ) )' % P)
e01 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % P)
lc = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % P)
lcc = w.s([lc], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % P)
o1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % P)
cm = w.s([lcc, o1], 'addcomd', '( %s -> ( ( # ` W ) + 1 ) = ( 1 + ( # ` W ) ) )' % P)
ie = w.s([e01, cm], 'oveq12d', '( %s -> ( ( 0 + 1 ) ..^ ( ( # ` W ) + 1 ) ) = ( 1 ..^ ( 1 + ( # ` W ) ) ) )' % P)
j1b = w.s([j1, ie], 'eleqtrd', '( %s -> ( J + 1 ) e. ( 1 ..^ ( 1 + ( # ` W ) ) ) )' % P)
slp = w.s([sl], 'oveq1d', '( %s -> ( ( # ` <" P "> ) + ( # ` W ) ) = ( 1 + ( # ` W ) ) )' % P)
sle = w.s([sl, slp], 'oveq12d', '( %s -> ( ( # ` <" P "> ) ..^ ( ( # ` <" P "> ) + ( # ` W ) ) ) = ( 1 ..^ ( 1 + ( # ` W ) ) ) )' % P)
j1c = w.s([j1b, sle], 'eleqtrrd', '( %s -> ( J + 1 ) e. ( ( # ` <" P "> ) ..^ ( ( # ` <" P "> ) + ( # ` W ) ) ) )' % P)
cv = w.s([s1, ww, j1c, w.inst('ccatval2')], 'syl3anc', '( %s -> ( %s ` ( J + 1 ) ) = ( W ` ( ( J + 1 ) - ( # ` <" P "> ) ) ) )' % (P, Z))
jz = w.s([w.s([jj, w.inst('elfzoelz')], 'syl', '( %s -> J e. ZZ )' % P)], 'zcnd', '( %s -> J e. CC )' % P)
pn = w.s([jz, o1], 'pncand', '( %s -> ( ( J + 1 ) - 1 ) = J )' % P)
sub = w.s([sl], 'oveq2d', '( %s -> ( ( J + 1 ) - ( # ` <" P "> ) ) = ( ( J + 1 ) - 1 ) )' % P)
sub2 = w.s([sub, pn], 'eqtrd', '( %s -> ( ( J + 1 ) - ( # ` <" P "> ) ) = J )' % P)
w.qed([cv, w.s([sub2], 'fveq2d', '( %s -> ( W ` ( ( J + 1 ) - ( # ` <" P "> ) ) ) = ( W ` J ) )' % P)], 'eqtrd',
      '( %s -> ( %s ` ( J + 1 ) ) = ( W ` J ) )' % (P, Z))
run(w)

# --------------------------------------------------------------- algprod0
w = W('algprod0', 'The product over the empty word is 1 (Lean: List.prod_nil).')
e1 = w.s([], 'hash0', '( # ` (/) ) = 0')
e2 = w.s([e1], 'oveq2i', '( 0 ..^ ( # ` (/) ) ) = ( 0 ..^ 0 )')
e3 = w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')
e4 = w.s([e2, e3], 'eqtri', '( 0 ..^ ( # ` (/) ) ) = (/)')
e5 = w.s([e4], 'prodeq1i', 'prod_ i e. ( 0 ..^ ( # ` (/) ) ) ( (/) ` i ) = prod_ i e. (/) ( (/) ` i )')
e6 = w.s([], 'prod0', 'prod_ i e. (/) ( (/) ` i ) = 1')
w.qed([e5, e6], 'eqtri', '%s = 1' % PR('(/)'))
run(w)

# --------------------------------------------------------------- algprodsh
w = W('algprodsh', 'The product over a word, indexed from one.')
P = 'W e. Word NN0'
LW = '( # ` W )'
ws = w.s([], 'id', '( %s -> W e. Word NN0 )' % P)
lc = w.s([ws, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (P, LW))
lz = w.s([lc], 'nn0zd', '( %s -> %s e. ZZ )' % (P, LW))
lcc = w.s([lc], 'nn0cnd', '( %s -> %s e. CC )' % (P, LW))
fzc = w.s([lz, w.inst('fzoval')], 'syl', '( %s -> ( 0 ..^ %s ) = ( 0 ... ( %s - 1 ) ) )' % (P, LW, LW))
h1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % P)
h2 = w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % P)
h3 = w.s([lz, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % P)], 'zsubcld', '( %s -> ( %s - 1 ) e. ZZ )' % (P, LW))
Q = '( %s /\\ j e. ( 0 ... ( %s - 1 ) ) )' % (P, LW)
jfz = w.s([], 'simpr', '( %s -> j e. ( 0 ... ( %s - 1 ) ) )' % (Q, LW))
fzcq = w.s([fzc], 'adantr', '( %s -> ( 0 ..^ %s ) = ( 0 ... ( %s - 1 ) ) )' % (Q, LW, LW))
jfzo = w.s([jfz, fzcq], 'eleqtrrd', '( %s -> j e. ( 0 ..^ %s ) )' % (Q, LW))
h4 = w.s([w.s([w.s([ws], 'adantr', '( %s -> W e. Word NN0 )' % Q), jfzo, w.inst('wrdsymbcl')], 'syl2anc',
             '( %s -> ( W ` j ) e. NN0 )' % Q)], 'nn0cnd', '( %s -> ( W ` j ) e. CC )' % Q)
h5 = w.s([w.s([], 'id', '( j = ( i - 1 ) -> j = ( i - 1 ) )')], 'fveq2d', '( j = ( i - 1 ) -> ( W ` j ) = ( W ` ( i - 1 ) ) )')
sh = w.s([h1, h2, h3, h4, h5], 'fprodshft',
         '( %s -> prod_ j e. ( 0 ... ( %s - 1 ) ) ( W ` j ) = prod_ i e. ( ( 0 + 1 ) ... ( ( %s - 1 ) + 1 ) ) ( W ` ( i - 1 ) ) )' % (P, LW, LW))
e01 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % P)
np = w.s([lcc, w.s([], '1cnd', '( %s -> 1 e. CC )' % P)], 'npcand', '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (P, LW, LW))
ir = w.s([e01, np], 'oveq12d', '( %s -> ( ( 0 + 1 ) ... ( ( %s - 1 ) + 1 ) ) = ( 1 ... %s ) )' % (P, LW, LW))
rhs = w.s([ir], 'prodeq1d', '( %s -> prod_ i e. ( ( 0 + 1 ) ... ( ( %s - 1 ) + 1 ) ) ( W ` ( i - 1 ) ) = prod_ i e. ( 1 ... %s ) ( W ` ( i - 1 ) ) )' % (P, LW, LW))
lhs = w.s([fzc], 'prodeq1d', '( %s -> prod_ j e. ( 0 ..^ %s ) ( W ` j ) = prod_ j e. ( 0 ... ( %s - 1 ) ) ( W ` j ) )' % (P, LW, LW))
w.qed([w.s([lhs, sh, rhs], '3eqtrd', '( %s -> prod_ j e. ( 0 ..^ %s ) ( W ` j ) = prod_ i e. ( 1 ... %s ) ( W ` ( i - 1 ) ) )' % (P, LW, LW))],
      'eqcomd', '( %s -> prod_ i e. ( 1 ... %s ) ( W ` ( i - 1 ) ) = prod_ j e. ( 0 ..^ %s ) ( W ` j ) )' % (P, LW, LW))
run(w)

# --------------------------------------------------------------- algprodcs
w = W('algprodcs', 'The product over a cons (Lean: List.prod_cons).')
P = '( P e. NN0 /\\ W e. Word NN0 )'
LW = '( # ` W )'
pp = w.s([], 'simpl', '( %s -> P e. NN0 )' % P)
ww = w.s([], 'simpr', '( %s -> W e. Word NN0 )' % P)
s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % P)
zw = w.s([s1, ww, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (P, Z))
lz = w.s([], 'alglencs', '( %s -> ( # ` %s ) = ( %s + 1 ) )' % (P, Z, LW))
lc = w.s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (P, LW))
lcc = w.s([lc], 'nn0cnd', '( %s -> %s e. CC )' % (P, LW))
lzz = w.s([w.s([zw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (P, Z))], 'nn0zd', '( %s -> ( # ` %s ) e. ZZ )' % (P, Z))
fzv = w.s([lzz, w.inst('fzoval')], 'syl', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ... ( ( # ` %s ) - 1 ) ) )' % (P, Z, Z))
sub = w.s([w.s([lz], 'oveq1d', '( %s -> ( ( # ` %s ) - 1 ) = ( ( %s + 1 ) - 1 ) )' % (P, Z, LW)),
           w.s([lcc, w.s([], '1cnd', '( %s -> 1 e. CC )' % P)], 'pncand', '( %s -> ( ( %s + 1 ) - 1 ) = %s )' % (P, LW, LW))], 'eqtrd',
          '( %s -> ( ( # ` %s ) - 1 ) = %s )' % (P, Z, LW))
fzZ = w.s([fzv, w.s([sub], 'oveq2d', '( %s -> ( 0 ... ( ( # ` %s ) - 1 ) ) = ( 0 ... %s ) )' % (P, Z, LW))], 'eqtrd',
          '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ... %s ) )' % (P, Z, LW))
st1 = w.s([fzZ], 'prodeq1d', '( %s -> %s = prod_ i e. ( 0 ... %s ) ( %s ` i ) )' % (P, PR(Z), LW, Z))
# fprod1p
uz = w.s([lc, w.s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % P)], 'eleqtrd',
         '( %s -> %s e. ( ZZ>= ` 0 ) )' % (P, LW))
Q = '( %s /\\ i e. ( 0 ... %s ) )' % (P, LW)
ifz = w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (Q, LW))
fzZq = w.s([fzZ], 'adantr', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ... %s ) )' % (Q, Z, LW))
ifzo = w.s([ifz, fzZq], 'eleqtrrd', '( %s -> i e. ( 0 ..^ ( # ` %s ) ) )' % (Q, Z))
zcc = w.s([w.s([w.s([zw], 'adantr', '( %s -> %s e. Word NN0 )' % (Q, Z)), ifzo, w.inst('wrdsymbcl')], 'syl2anc',
              '( %s -> ( %s ` i ) e. NN0 )' % (Q, Z))], 'nn0cnd', '( %s -> ( %s ` i ) e. CC )' % (Q, Z))
sb = w.s([w.s([], 'id', '( i = 0 -> i = 0 )')], 'fveq2d', '( i = 0 -> ( %s ` i ) = ( %s ` 0 ) )' % (Z, Z))
fp = w.s([uz, zcc, sb], 'fprod1p',
         '( %s -> prod_ i e. ( 0 ... %s ) ( %s ` i ) = ( ( %s ` 0 ) x. prod_ i e. ( ( 0 + 1 ) ... %s ) ( %s ` i ) ) )' % (P, LW, Z, Z, LW, Z))
e01 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % P)
ir = w.s([e01], 'oveq1d', '( %s -> ( ( 0 + 1 ) ... %s ) = ( 1 ... %s ) )' % (P, LW, LW))
ir2 = w.s([ir], 'prodeq1d', '( %s -> prod_ i e. ( ( 0 + 1 ) ... %s ) ( %s ` i ) = prod_ i e. ( 1 ... %s ) ( %s ` i ) )' % (P, LW, Z, LW, Z))
hd = w.s([], 'algcsfv0', '( %s -> ( %s ` 0 ) = P )' % (P, Z))
fp2 = w.s([fp, w.s([hd, ir2], 'oveq12d',
                   '( %s -> ( ( %s ` 0 ) x. prod_ i e. ( ( 0 + 1 ) ... %s ) ( %s ` i ) ) = ( P x. prod_ i e. ( 1 ... %s ) ( %s ` i ) ) )' % (P, Z, LW, Z, LW, Z))], 'eqtrd',
          '( %s -> prod_ i e. ( 0 ... %s ) ( %s ` i ) = ( P x. prod_ i e. ( 1 ... %s ) ( %s ` i ) ) )' % (P, LW, Z, LW, Z))
# body rewrite: ( Z ` i ) = ( W ` ( i - 1 ) ) on ( 1 ... LW )
R = '( %s /\\ i e. ( 1 ... %s ) )' % (P, LW)
ifz1 = w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (R, LW))
iz = w.s([ifz1, w.inst('elfzelz')], 'syl', '( %s -> i e. ZZ )' % R)
icc = w.s([iz], 'zcnd', '( %s -> i e. CC )' % R)
i1 = w.s([ifz1, w.inst('elfzle1')], 'syl', '( %s -> 1 <_ i )' % R)
i2 = w.s([ifz1, w.inst('elfzle2')], 'syl', '( %s -> i <_ %s )' % (R, LW))
im1z = w.s([iz, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % R)], 'zsubcld', '( %s -> ( i - 1 ) e. ZZ )' % R)
ir_ = w.s([iz], 'zred', '( %s -> i e. RR )' % R)
lwr = w.s([w.s([lc], 'adantr', '( %s -> %s e. NN0 )' % (R, LW))], 'nn0red', '( %s -> %s e. RR )' % (R, LW))
o1r = w.s([], '1red', '( %s -> 1 e. RR )' % R)
ge0 = w.s([ir_, o1r], 'subge0d', '( %s -> ( 0 <_ ( i - 1 ) <-> 1 <_ i ) )' % R)
ge0b = w.s([ge0, i1], 'mpbird', '( %s -> 0 <_ ( i - 1 ) )' % R)
im1n = w.s([im1z, ge0b, w.inst('elnn0z')], 'sylanbrc', '( %s -> ( i - 1 ) e. NN0 )' % R)
lwn = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % R), ir_, lwr, i1, i2], 'letrd', '( %s -> 1 <_ %s )' % (R, LW))
lwnn = w.s([w.s([lc], 'adantr', '( %s -> %s e. NN0 )' % (R, LW)), lwn, w.inst('elnnnn0c')], 'sylanbrc', '( %s -> %s e. NN )' % (R, LW))
im1r = w.s([im1z], 'zred', '( %s -> ( i - 1 ) e. RR )' % R)
ltw = w.s([im1r, ir_, lwr, w.s([ir_], 'ltm1d', '( %s -> ( i - 1 ) < i )' % R), i2], 'ltletrd',
          '( %s -> ( i - 1 ) < %s )' % (R, LW))
im1fzo = w.s([w.s([im1n, lwnn, ltw], '3jca', '( %s -> ( ( i - 1 ) e. NN0 /\\ %s e. NN /\\ ( i - 1 ) < %s ) )' % (R, LW, LW)),
              w.inst('elfzo0')], 'sylibr', '( %s -> ( i - 1 ) e. ( 0 ..^ %s ) )' % (R, LW))
cv = w.s([w.s([w.s([pp], 'adantr', '( %s -> P e. NN0 )' % R), w.s([ww], 'adantr', '( %s -> W e. Word NN0 )' % R)], 'jca',
             '( %s -> ( P e. NN0 /\\ W e. Word NN0 ) )' % R), im1fzo, w.inst('algcsfvp1')], 'syl2anc',
         '( %s -> ( %s ` ( ( i - 1 ) + 1 ) ) = ( W ` ( i - 1 ) ) )' % (R, Z))
npc = w.s([icc, w.s([], '1cnd', '( %s -> 1 e. CC )' % R)], 'npcand', '( %s -> ( ( i - 1 ) + 1 ) = i )' % R)
cv2 = w.s([w.s([npc], 'fveq2d', '( %s -> ( %s ` ( ( i - 1 ) + 1 ) ) = ( %s ` i ) )' % (R, Z, Z)), cv], 'eqtr3d',
          '( %s -> ( %s ` i ) = ( W ` ( i - 1 ) ) )' % (R, Z))
body = w.s([cv2], 'prodeq2dv', '( %s -> prod_ i e. ( 1 ... %s ) ( %s ` i ) = prod_ i e. ( 1 ... %s ) ( W ` ( i - 1 ) ) )' % (P, LW, Z, LW))
sh = w.s([ww, w.inst('algprodsh')], 'syl', '( %s -> prod_ i e. ( 1 ... %s ) ( W ` ( i - 1 ) ) = prod_ j e. ( 0 ..^ %s ) ( W ` j ) )' % (P, LW, LW))
cb = w.s([w.s([w.s([], 'id', '( j = i -> j = i )')], 'fveq2d', '( j = i -> ( W ` j ) = ( W ` i ) )')], 'cbvprodv',
         'prod_ j e. ( 0 ..^ %s ) ( W ` j ) = %s' % (LW, PR('W')))
cba = w.s([cb], 'a1i', '( %s -> prod_ j e. ( 0 ..^ %s ) ( W ` j ) = %s )' % (P, LW, PR('W')))
tail = w.s([body, sh, cba], '3eqtrd', '( %s -> prod_ i e. ( 1 ... %s ) ( %s ` i ) = %s )' % (P, LW, Z, PR('W')))
w.qed([st1, fp2, w.s([tail], 'oveq2d', '( %s -> ( P x. prod_ i e. ( 1 ... %s ) ( %s ` i ) ) = ( P x. %s ) )' % (P, LW, Z, PR('W')))], '3eqtrd',
      '( %s -> %s = ( P x. %s ) )' % (P, PR(Z), PR('W')))
run(w)
