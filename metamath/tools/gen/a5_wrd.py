"""Sortie A5, batch 1: the drop of a word (Lean: List.drop (l.length - T) l).
MM_DB=sorties/a5.mm python3 tools/gen/a5_wrd.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1lib
from tm import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

LV = '( # ` V )'
SUB = '( V substr <. ( %s - T ) , %s >. )' % (LV, LV)
P = '( V e. Word S /\\ T e. ( 0 ... %s ) )' % LV

# --------------------------------------------------------------- subcl
w = W('drpcl', 'The tail of a word from a given position is a word (Lean: List.drop).')
wrd = w.s([], 'simpl', '( %s -> V e. Word S )' % P)
w.qed([wrd, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word S )' % (P, SUB))
run(w)

# --------------------------------------------------------------- subfz
w = W('drpfz', 'The starting position of the T-element tail of a word lies in the index range.')
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (P, f))
wrd = st([], 'simpl', 'V e. Word S')
tt = st([], 'simpr', 'T e. ( 0 ... %s )' % LV)
ln = st([wrd, w.inst('lencl')], 'syl', '%s e. NN0' % LV)
tri = st([tt, w.inst('elfz2nn0')], 'sylib', '( T e. NN0 /\\ %s e. NN0 /\\ T <_ %s )' % (LV, LV))
tn0 = st([tri], 'simp1d', 'T e. NN0')
tle = st([tri], 'simp3d', 'T <_ %s' % LV)
sub = st([tn0, ln, w.inst('nn0sub')], 'syl2anc', '( T <_ %s <-> ( %s - T ) e. NN0 )' % (LV, LV))
subn = st([tle, sub], 'mpbid', '( %s - T ) e. NN0' % LV)
lre = st([ln], 'nn0red', '%s e. RR' % LV)
tre = st([tn0], 'nn0red', 'T e. RR')
t0 = st([tn0], 'nn0ge0d', '0 <_ T')
sle = st([lre, tre, w.inst('subge02')], 'syl2anc', '( 0 <_ T <-> ( %s - T ) <_ %s )' % (LV, LV))
sle2 = st([t0, sle], 'mpbid', '( %s - T ) <_ %s' % (LV, LV))
tri3 = st([subn, ln, sle2], '3jca', '( ( %s - T ) e. NN0 /\\ %s e. NN0 /\\ ( %s - T ) <_ %s )' % (LV, LV, LV, LV))
w.qed([tri3, w.inst('elfz2nn0')], 'sylibr',
      '( %s -> ( %s - T ) e. ( 0 ... %s ) )' % (P, LV, LV))
run(w)

# --------------------------------------------------------------- sublen
w = W('drplen', 'The T-element tail of a word has T elements (Lean: List.length_drop).')
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (P, f))
wrd = st([], 'simpl', 'V e. Word S')
tt = st([], 'simpr', 'T e. ( 0 ... %s )' % LV)
fz = st([], 'drpfz', '( %s - T ) e. ( 0 ... %s )' % (LV, LV))
ln = st([wrd, fz, w.inst('swrdrlen')], 'syl2anc',
        '( # ` %s ) = ( %s - ( %s - T ) )' % (SUB, LV, LV))
lcl = st([wrd, w.inst('lencl')], 'syl', '%s e. NN0' % LV)
lcc = st([lcl], 'nn0cnd', '%s e. CC' % LV)
tcl = st([tt, w.inst('elfznn0')], 'syl', 'T e. NN0')
tcc = st([tcl], 'nn0cnd', 'T e. CC')
nc = w.s([lcc, tcc], 'nncand', '( %s -> ( %s - ( %s - T ) ) = T )' % (P, LV, LV))
w.qed([ln, nc], 'eqtrd', '( %s -> ( # ` %s ) = T )' % (P, SUB))
run(w)

# --------------------------------------------------------------- subrn
w = W('drprn', 'Every element of the tail of a word is an element of the word (Lean: List.mem_of_mem_drop).')
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (P, f))
wrd = st([], 'simpl', 'V e. Word S')
fz = st([], 'drpfz', '( %s - T ) e. ( 0 ... %s )' % (LV, LV))
lcl = st([wrd, w.inst('lencl')], 'syl', '%s e. NN0' % LV)
lfz = st([lcl, w.inst('nn0fz0')], 'sylib', '%s e. ( 0 ... %s )' % (LV, LV))
rn = st([wrd, fz, lfz, w.inst('swrdrn3')], 'syl3anc',
        'ran %s = ( V " ( ( %s - T ) ..^ %s ) )' % (SUB, LV, LV))
ss = w.s([], 'imassrn', '( V " ( ( %s - T ) ..^ %s ) ) C_ ran V' % (LV, LV))
ssa = st([ss], 'a1i', '( V " ( ( %s - T ) ..^ %s ) ) C_ ran V' % (LV, LV))
w.qed([rn, ssa], 'eqsstrd', '( %s -> ran %s C_ ran V )' % (P, SUB))
run(w)

# --------------------------------------------------------------- wrdf1x
w = W('wrdf1x', 'A duplicate-free word is injective on its domain (Lean: List.Nodup as injectivity of the index map).')
PF = '( V e. Word S /\\ Fun `\' V )'
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (PF, f))
wrd = st([], 'simpl', 'V e. Word S')
fun = st([], 'simpr', 'Fun `\' V')
wf = st([wrd, w.inst('wrdf')], 'syl', 'V : ( 0 ..^ %s ) --> S' % LV)
f1 = st([st([wf, fun], 'jca', '( V : ( 0 ..^ %s ) --> S /\\ Fun `\' V )' % LV),
         st([w.s([], 'df-f1', '( V : ( 0 ..^ %s ) -1-1-> S <-> ( V : ( 0 ..^ %s ) --> S /\\ Fun `\' V ) )' % (LV, LV))],
            'a1i', '( V : ( 0 ..^ %s ) -1-1-> S <-> ( V : ( 0 ..^ %s ) --> S /\\ Fun `\' V ) )' % (LV, LV))],
        'mpbird', 'V : ( 0 ..^ %s ) -1-1-> S' % LV)
dm = st([wrd, w.inst('wrddm')], 'syl', 'dom V = ( 0 ..^ %s )' % LV)
bi = st([dm, w.inst('f1eq2')], 'syl', '( V : dom V -1-1-> S <-> V : ( 0 ..^ %s ) -1-1-> S )' % LV)
w.qed([f1, bi], 'mpbird', '( %s -> V : dom V -1-1-> S )' % PF)
run(w)

# --------------------------------------------------------------- subndp
w = W('drpndp', 'The tail of a duplicate-free word is duplicate-free (Lean: List.Nodup.sublist).')
PN = '( ( V e. Word S /\\ Fun `\' V ) /\\ T e. ( 0 ... %s ) )' % LV
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (PN, f))
pair = st([], 'simpl', '( V e. Word S /\\ Fun `\' V )')
wrd = st([pair], 'simpld', 'V e. Word S')
fun = st([pair], 'simprd', 'Fun `\' V')
tt = st([], 'simpr', 'T e. ( 0 ... %s )' % LV)
fz = st([st([wrd, tt], 'jca', P), w.inst('drpfz')], 'syl',
        '( %s - T ) e. ( 0 ... %s )' % (LV, LV))
lcl = st([wrd, w.inst('lencl')], 'syl', '%s e. NN0' % LV)
lfz = st([lcl, w.inst('nn0fz0')], 'sylib', '%s e. ( 0 ... %s )' % (LV, LV))
f1 = w.s([st([wrd, fun], 'jca', '( V e. Word S /\\ Fun `\' V )'), w.inst('wrdf1x')], 'syl',
         '( %s -> V : dom V -1-1-> S )' % PN)
sf1 = w.s([wrd, fz, lfz, f1], 'swrdf1',
          '( %s -> %s : dom %s -1-1-> S )' % (PN, SUB, SUB))
bi = w.s([], 'df-f1', '( %s : dom %s -1-1-> S <-> ( %s : dom %s --> S /\\ Fun `\' %s ) )'
         % (SUB, SUB, SUB, SUB, SUB))
bia = st([bi], 'a1i', '( %s : dom %s -1-1-> S <-> ( %s : dom %s --> S /\\ Fun `\' %s ) )'
         % (SUB, SUB, SUB, SUB, SUB))
cj = st([sf1, bia], 'mpbid', '( %s : dom %s --> S /\\ Fun `\' %s )' % (SUB, SUB, SUB))
w.qed([cj], 'simprd', '( %s -> Fun `\' %s )' % (PN, SUB))
run(w)
