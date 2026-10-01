"""Sortie A4c, batch 1: typing of a Tbl entry, the Option payload, and
the divisor-set membership bridge."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DJ = '( Word NN0 |_| 1o )'

# ------------------------------------------------------------------ tblfv
if not only or 'tblfv' in only:
    w = W('tblfv', 'An entry of a DP table is an optional word (Lean: t : Tbl is total).')
    T = '( T e. Tbl /\\ C e. NN0 )'
    tt = w.s([], 'simpl', '( %s -> T e. Tbl )' % T)
    cc = w.s([], 'simpr', '( %s -> C e. NN0 )' % T)
    d = w.s([], 'df-tbl', 'Tbl = ( %s ^m NN0 )' % DJ)
    eq = w.s([d], 'eleq2i', '( T e. Tbl <-> T e. ( %s ^m NN0 ) )' % DJ)
    m = w.s([tt, w.s([eq], 'a1i', '( %s -> ( T e. Tbl <-> T e. ( %s ^m NN0 ) ) )' % (T, DJ))], 'mpbid',
            '( %s -> T e. ( %s ^m NN0 ) )' % (T, DJ))
    f = w.s([m, w.inst('elmapi')], 'syl', '( %s -> T : NN0 --> %s )' % (T, DJ))
    w.qed([f, cc, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( T ` C ) e. %s )' % (T, DJ))
    run(w)

# ------------------------------------------------------------------ alginl2
if not only or 'alginl2' in only:
    w = W('alginl2', 'The payload of a left injection (Lean: Option.some.inj).')
    T = 'S e. V'
    ex = w.s([], 'elex', '( S e. V -> S e. _V )')
    v = w.s([], 'inlval', '( S e. V -> ( inl ` S ) = <. (/) , S >. )')
    e1 = w.s([v], 'fveq2d', '( %s -> ( 2nd ` ( inl ` S ) ) = ( 2nd ` <. (/) , S >. ) )' % T)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % T)
    e2 = w.s([z, ex, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. (/) , S >. ) = S )' % T)
    w.qed([e1, e2], 'eqtrd', '( %s -> ( 2nd ` ( inl ` S ) ) = S )' % T)
    run(w)

# ------------------------------------------------------------------ algnne
if not only or 'algnne' in only:
    w = W('algnne', 'A left injection is not the none of an Option (Lean: Option.some_ne_none).')
    T = '( S e. V /\\ X = ( inl ` S ) )'
    ss = w.s([], 'simpl', '( %s -> S e. V )' % T)
    xe = w.s([], 'simpr', '( %s -> X = ( inl ` S ) )' % T)
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % T)
    ne = w.s([ss, z, w.inst('inlneinr')], 'syl2anc', '( %s -> ( inl ` S ) =/= ( inr ` (/) ) )' % T)
    w.qed([xe, ne], 'eqnetrd', '( %s -> X =/= ( inr ` (/) ) )' % T)
    run(w)

# ------------------------------------------------------------------ tblpay
if not only or 'tblpay' in only:
    w = W('tblpay', 'The witness list stored at a nonempty entry of a DP table (Lean: Option.ne_none_iff_exists).')
    T = '( ( T e. Tbl /\\ C e. NN0 ) /\\ ( T ` C ) =/= ( inr ` (/) ) )'
    fv = w.s([w.s([], 'simpl', '( %s -> ( T e. Tbl /\\ C e. NN0 ) )' % T), w.inst('tblfv')], 'syl',
             '( %s -> ( T ` C ) e. %s )' % (T, DJ))
    nn = w.s([], 'simpr', '( %s -> ( T ` C ) =/= ( inr ` (/) ) )' % T)
    w.qed([fv, nn, w.inst('algdjun')], 'syl2anc',
          "( %s -> ( ( 2nd ` ( T ` C ) ) e. Word NN0 /\\ ( T ` C ) = ( inl ` ( 2nd ` ( T ` C ) ) ) ) )" % T)
    run(w)

# ------------------------------------------------------------------ algndps1
if not only or 'algndps1' in only:
    w = W('algndps1', 'A one-letter word is duplicate-free (Lean: List.nodup_singleton).')
    T = 'P e. NN0'
    ex = w.s([], 'elex', '( P e. NN0 -> P e. _V )')
    v = w.s([ex, w.inst('s1val')], 'syl', '( %s -> <" P "> = { <. 0 , P >. } )' % T)
    c1 = w.s([v], 'cnveqd', "( %s -> `' <\" P \"> = `' { <. 0 , P >. } )" % T)
    z = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % T)
    c2 = w.s([z, ex, w.inst('cnvsng')], 'syl2anc', "( %s -> `' { <. 0 , P >. } = { <. P , 0 >. } )" % T)
    c3 = w.s([c1, c2], 'eqtrd', "( %s -> `' <\" P \"> = { <. P , 0 >. } )" % T)
    fu = w.s([ex, z, w.inst('funsng')], 'syl2anc', '( %s -> Fun { <. P , 0 >. } )' % T)
    bi = w.s([c3], 'funeqd', "( %s -> ( Fun `' <\" P \"> <-> Fun { <. P , 0 >. } ) )" % T)
    w.qed([fu, bi], 'mpbird', "( %s -> Fun `' <\" P \"> )" % T)
    run(w)

# ------------------------------------------------------------------ tblf
if not only or 'tblf' in only:
    w = W('tblf', 'A DP table is a total function on the residues (Lean: Tbl is a function type).')
    d = w.s([], 'df-tbl', 'Tbl = ( %s ^m NN0 )' % DJ)
    eq = w.s([d], 'eleq2i', '( T e. Tbl <-> T e. ( %s ^m NN0 ) )' % DJ)
    m = w.s([w.s([], 'id', '( T e. Tbl -> T e. Tbl )'),
             w.s([eq], 'a1i', '( T e. Tbl -> ( T e. Tbl <-> T e. ( %s ^m NN0 ) ) )' % DJ)], 'mpbid',
            '( T e. Tbl -> T e. ( %s ^m NN0 ) )' % DJ)
    w.qed([m, w.inst('elmapi')], 'syl', '( T e. Tbl -> T : NN0 --> %s )' % DJ)
    run(w)
