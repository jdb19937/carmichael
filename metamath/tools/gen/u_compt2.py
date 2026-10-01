"""Sortie S, batch 6: TM2CompT for explicit tuples (the introduction form for the final assembly)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

body = defbody('df-tm2compt')
wff = body[len('{ <. h , e >. |'):-1].strip()
WFF = lambda H, E: sub(wff, {'h': H, 'e': E})
H = '<. M , <. <. I , J >. , T >. >.'
E = '<. <. <. D , A >. , <. G , B >. >. , F >.'
XP = '( _V X. ( ( _V X. _V ) X. _V ) )'
A = '( ( M e. P /\\ I e. Q /\\ J e. R ) /\\ T e. U /\\ ( ( D e. V /\\ A e. W ) /\\ ( G e. X /\\ B e. Y ) /\\ F e. Z ) )'

w = W('tm2comptel', "TM2CompT for explicit tuples: the machine M with the alphabet bijections I, J and the time function T witnesses that F is computed with input encoding D (alphabet A) and output encoding G (alphabet B) if and only if M is a bundled finite machine, the bijections and the time function have the right types, and on every input a the machine outputs the encoded value of F within time of the input length.")
g1 = w.s([], 'simp1', '( %s -> ( M e. P /\\ I e. Q /\\ J e. R ) )' % A); g2 = w.s([], 'simp2', '( %s -> T e. U )' % A); g3 = w.s([], 'simp3', '( %s -> ( ( D e. V /\\ A e. W ) /\\ ( G e. X /\\ B e. Y ) /\\ F e. Z ) )' % A)
m = w.s([g1], 'simp1d', '( %s -> M e. P )' % A); ia = w.s([g1], 'simp2d', '( %s -> I e. Q )' % A); oa = w.s([g1], 'simp3d', '( %s -> J e. R )' % A)
e1 = w.s([g3], 'simp1d', '( %s -> ( D e. V /\\ A e. W ) )' % A); e2 = w.s([g3], 'simp2d', '( %s -> ( G e. X /\\ B e. Y ) )' % A); f = w.s([g3], 'simp3d', '( %s -> F e. Z )' % A)
ea = w.s([e1], 'simpld', '( %s -> D e. V )' % A); a0 = w.s([e1], 'simprd', '( %s -> A e. W )' % A); eb = w.s([e2], 'simpld', '( %s -> G e. X )' % A); a1 = w.s([e2], 'simprd', '( %s -> B e. Y )' % A)
setmap = {}
for name, st in [('M', m), ('I', ia), ('J', oa), ('T', g2), ('D', ea), ('A', a0), ('G', eb), ('B', a1), ('F', f)]:
    setmap[name] = w.s([st], 'elexd', '( %s -> %s e. _V )' % (A, name))
hx = w.s([], 'opex', '%s e. _V' % H); hxd = w.s([hx], 'a1i', '( %s -> %s e. _V )' % (A, H))
ex = w.s([], 'opex', '%s e. _V' % E); exd = w.s([ex], 'a1i', '( %s -> %s e. _V )' % (A, E))
br = w.s([hxd, exd, w.inst('tm2comptbr')], 'syl2anc', '( %s -> ( %s TM2CompT %s <-> %s ) )' % (A, H, E, WFF(H, E)))
st, res = evaluate(w, A, WFF(H, E), setmap, wff=True)
br2 = w.s([br, st], 'bitrd', '( %s -> ( %s TM2CompT %s <-> %s ) )' % (A, H, E, res))
node = parse_wff(res); assert node.kind == '3an'
P, Q, R = [k.text() for k in node.kids]; Pn = parse_wff(P); P1, P2 = [k.text() for k in Pn.kids]
assert P1 == '%s e. %s' % (H, XP), P1
o1 = w.s([setmap['I'], setmap['J'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. I , J >. e. ( _V X. _V ) )' % A)
o2 = w.s([o1, setmap['T'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. <. I , J >. , T >. e. ( ( _V X. _V ) X. _V ) )' % A)
o3 = w.s([setmap['M'], o2, w.inst('opelxpi')], 'syl2anc', '( %s -> %s )' % (A, P1))
bt = w.s([o3], 'biantrurd', '( %s -> ( %s <-> %s ) )' % (A, P2, P))
bt2 = w.s([bt], '3anbi1d', '( %s -> ( ( %s /\\ %s /\\ %s ) <-> ( %s /\\ %s /\\ %s ) ) )' % (A, P2, Q, R, P, Q, R))
w.qed([br2, bt2], 'bitr4d', '( %s -> ( %s TM2CompT %s <-> ( %s /\\ %s /\\ %s ) ) )' % (A, H, E, P2, Q, R)); run(w)
