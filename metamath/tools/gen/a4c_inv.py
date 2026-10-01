"""Sortie A4c, batch 5: the three table invariants at the empty table and
across one DP step (Lean: AlgExtract.tbl*_empty, tbl*_dpStep)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

PRODS = 'prod_ q e. S q'

# ------------------------------------------------------------------ tcsfin
if not only or 'tcsfin' in only:
    w = W('tcsfin', 'A subset of the entries of a word is a finite set of residues.')
    A = '( E e. Word NN0 /\\ S e. ~P ran E )'
    ee = w.s([], 'simpl', '( %s -> E e. Word NN0 )' % A)
    sp = w.s([], 'simpr', '( %s -> S e. ~P ran E )' % A)
    ss = w.s([sp, w.inst('elpwi')], 'syl', '( %s -> S C_ ran E )' % A)
    fi = w.s([ee, w.inst('algwrdfi')], 'syl', '( %s -> ran E e. Fin )' % A)
    sf = w.s([fi, ss, w.inst('ssfi')], 'syl2anc', '( %s -> S e. Fin )' % A)
    rs = w.s([w.s([ee, w.inst('wrdf')], 'syl', '( %s -> E : ( 0 ..^ ( # ` E ) ) --> NN0 )' % A), w.inst('frn')], 'syl',
             '( %s -> ran E C_ NN0 )' % A)
    w.qed([sf, w.s([ss, rs], 'sstrd', '( %s -> S C_ NN0 )' % A)], 'jca', '( %s -> ( S e. Fin /\\ S C_ NN0 ) )' % A)
    run(w)

# ------------------------------------------------------------------ tcsprod
if not only or 'tcsprod' in only:
    w = W('tcsprod', 'The product of a subset of the entries of a word is a nonnegative integer.')
    A = '( E e. Word NN0 /\\ S e. ~P ran E )'
    fs = w.s([], 'tcsfin', '( %s -> ( S e. Fin /\\ S C_ NN0 ) )' % A)
    sf = w.s([fs], 'simpld', '( %s -> S e. Fin )' % A)
    sn = w.s([fs], 'simprd', '( %s -> S C_ NN0 )' % A)
    el = w.s([w.s([sn], 'adantr', '( ( %s /\\ q e. S ) -> S C_ NN0 )' % A),
              w.s([], 'simpr', '( ( %s /\\ q e. S ) -> q e. S )' % A)], 'sseldd',
             '( ( %s /\\ q e. S ) -> q e. NN0 )' % A)
    w.qed([sf, el], 'fprodnn0cl', '( %s -> %s e. NN0 )' % (A, PRODS))
    run(w)

# ------------------------------------------------------------------ tcsmod
if not only or 'tcsmod' in only:
    w = W('tcsmod', 'The residue of the product of a subset of the entries of a word.')
    A = '( ( L e. NN /\\ E e. Word NN0 ) /\\ S e. ~P ran E )'
    ll = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ E e. Word NN0 ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    ee = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ E e. Word NN0 ) )' % A)], 'simprd', '( %s -> E e. Word NN0 )' % A)
    sp = w.s([], 'simpr', '( %s -> S e. ~P ran E )' % A)
    pn = w.s([w.s([ee, sp], 'jca', '( %s -> ( E e. Word NN0 /\\ S e. ~P ran E ) )' % A), w.inst('tcsprod')], 'syl',
             '( %s -> %s e. NN0 )' % (A, PRODS))
    cl = w.s([w.s([pn], 'nn0zd', '( %s -> %s e. ZZ )' % (A, PRODS)), ll, w.inst('zmodcl')], 'syl2anc',
             '( %s -> ( %s mod L ) e. NN0 )' % (A, PRODS))
    lt = w.s([w.s([pn], 'nn0red', '( %s -> %s e. RR )' % (A, PRODS)),
              w.s([ll, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % A), w.inst('modlt')], 'syl2anc',
             '( %s -> ( %s mod L ) < L )' % (A, PRODS))
    w.qed([cl, lt], 'jca', '( %s -> ( ( %s mod L ) e. NN0 /\\ ( %s mod L ) < L ) )' % (A, PRODS, PRODS))
    run(w)

# ------------------------------------------------------------------ tblsnd0
if not only or 'tblsnd0' in only:
    w = W('tblsnd0', 'The empty table is sound (Lean: tblSound_empty).')
    A = '( L e. NN /\\ E e. Word NN0 )'
    B = '( %s /\\ d e. NN0 )' % A
    ev = w.s([w.s([], 'simpr', '( %s -> d e. NN0 )' % B), w.inst('emptytblval')], 'syl',
             '( %s -> ( EmptyTbl ` d ) = %s )' % (B, NONE))
    ne = w.s([w.s([ev], 'a1d', '( %s -> ( T. -> ( EmptyTbl ` d ) = %s ) )' % (B, NONE))], 'id', None)
    w.lines.pop()
    nn = w.s([w.s([], 'nne', '( -. ( EmptyTbl ` d ) =/= %s <-> ( EmptyTbl ` d ) = %s )' % (NONE, NONE))], 'biimpri',
             '( ( EmptyTbl ` d ) = %s -> -. ( EmptyTbl ` d ) =/= %s )' % (NONE, NONE))
    imp = w.s([w.s([ev, w.s([nn], 'a1i', '( %s -> ( ( EmptyTbl ` d ) = %s -> -. ( EmptyTbl ` d ) =/= %s ) )' % (B, NONE, NONE))],
                   'mpd', '( %s -> -. ( EmptyTbl ` d ) =/= %s )' % (B, NONE))], 'pm2.21d', None)
    body = TS('L', 'EmptyTbl', 'E')
    inner = body[body.index('( ('):]
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> %s )' % (B, inner)
    w.qed([imp], 'ralrimiva', '( %s -> %s )' % (A, body))
    run(w)

# ------------------------------------------------------------------ tblbnd0
if not only or 'tblbnd0' in only:
    w = W('tblbnd0', 'The empty table is length-bounded (Lean: tblBounded_empty).')
    A = 'K e. NN0'
    B = '( %s /\\ d e. NN0 )' % A
    ev = w.s([w.s([], 'simpr', '( %s -> d e. NN0 )' % B), w.inst('emptytblval')], 'syl',
             '( %s -> ( EmptyTbl ` d ) = %s )' % (B, NONE))
    nn = w.s([w.s([], 'nne', '( -. ( EmptyTbl ` d ) =/= %s <-> ( EmptyTbl ` d ) = %s )' % (NONE, NONE))], 'biimpri',
             '( ( EmptyTbl ` d ) = %s -> -. ( EmptyTbl ` d ) =/= %s )' % (NONE, NONE))
    imp = w.s([w.s([ev, w.s([nn], 'a1i', '( %s -> ( ( EmptyTbl ` d ) = %s -> -. ( EmptyTbl ` d ) =/= %s ) )' % (B, NONE, NONE))],
                   'mpd', '( %s -> -. ( EmptyTbl ` d ) =/= %s )' % (B, NONE))], 'pm2.21d', None)
    body = TB('EmptyTbl', 'K')
    inner = body[body.index('( ('):]
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> %s )' % (B, inner)
    w.qed([imp], 'ralrimiva', '( %s -> %s )' % (A, body))
    run(w)

# ------------------------------------------------------------------ tblcmp0
if not only or 'tblcmp0' in only:
    w = W('tblcmp0', 'The empty table is complete for the empty list (Lean: tblComplete_empty).')
    A = 'L e. NN'
    B = '( %s /\\ s e. ~P ran (/) )' % A
    sp = w.s([], 'simpr', '( %s -> s e. ~P ran (/) )' % B)
    e1 = w.s([w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'pweqi', '~P ran (/) = ~P (/)'),
              w.s([], 'pw0', '~P (/) = { (/) }')], 'eqtri', '~P ran (/) = { (/) }')
    s1 = w.s([sp, w.s([e1], 'a1i', '( %s -> ~P ran (/) = { (/) } )' % B)], 'eleqtrd', '( %s -> s e. { (/) } )' % B)
    s2 = w.s([s1, w.inst('elsni')], 'syl', '( %s -> s = (/) )' % B)
    nn = w.s([w.s([], 'nne', '( -. s =/= (/) <-> s = (/) )')], 'biimpri', '( s = (/) -> -. s =/= (/) )')
    imp = w.s([w.s([s2, w.s([nn], 'a1i', '( %s -> ( s = (/) -> -. s =/= (/) ) )' % B)], 'mpd',
                   '( %s -> -. s =/= (/) )' % B)], 'pm2.21d', None)
    body = TC('L', 'EmptyTbl', '(/)')
    inner = body[body.index('( s =/='):]
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> %s )' % (B, inner)
    w.qed([imp], 'ralrimiva', '( %s -> %s )' % (A, body))
    run(w)
