"""Sortie A4c, batch 6: small word and modular-arithmetic helpers."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ------------------------------------------------------------------ algcsnz
if not only or 'algcsnz' in only:
    w = W('algcsnz', 'A word with a letter prepended is nonempty (Lean: List.cons_ne_nil).')
    A = '( P e. NN0 /\\ W e. Word NN0 )'
    s1 = w.s([w.s([], 'simpl', '( %s -> P e. NN0 )' % A), w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A)
    ww = w.s([], 'simpr', '( %s -> W e. Word NN0 )' % A)
    bi = w.s([s1, ww, w.inst('ccat0')], 'syl2anc',
             '( %s -> ( ( <" P "> ++ W ) = (/) <-> ( <" P "> = (/) /\\ W = (/) ) ) )' % A)
    nz = w.s([w.s([w.s([], 's1nz', '<" P "> =/= (/)'), w.inst('neneq')], 'ax-mp', '-. <" P "> = (/)')], 'a1i',
             '( %s -> -. <" P "> = (/) )' % A)
    w.qed([w.s([bi, w.s([nz], 'intnanrd', '( %s -> -. ( <" P "> = (/) /\\ W = (/) ) )' % A)], 'mtbird',
               '( %s -> -. ( <" P "> ++ W ) = (/) )' % A)], 'neqned', '( %s -> ( <" P "> ++ W ) =/= (/) )' % A)
    run(w)

# ------------------------------------------------------------------ algprods1
if not only or 'algprods1' in only:
    w = W('algprods1', 'The product of a one-letter word (Lean: List.prod_singleton).')
    A = 'P e. NN0'
    s1 = w.s([w.inst('s1cl')], 'id', None)
    w.lines.pop()
    s1 = w.s([], 's1cl', '( P e. NN0 -> <" P "> e. Word NN0 )')
    rid = w.s([s1, w.inst('ccatrid')], 'syl', '( %s -> ( <" P "> ++ (/) ) = <" P "> )' % A)
    pr = prdeq(w, A, '( <" P "> ++ (/) )', '<" P ">', rid)
    cs = w.s([w.s([], 'id', '( P e. NN0 -> P e. NN0 )'), w.s([w.s([], 'wrd0', '(/) e. Word NN0')], 'a1i',
                                                             '( %s -> (/) e. Word NN0 )' % A), w.inst('algprodcs')], 'syl2anc',
             '( %s -> %s = ( P x. %s ) )' % (A, PRD('( <" P "> ++ (/) )'), PRD('(/)')))
    p0 = w.s([w.s([], 'algprod0', '%s = 1' % PRD('(/)'))], 'a1i', '( %s -> %s = 1 )' % (A, PRD('(/)')))
    e1 = w.s([cs, w.s([p0], 'oveq2d', '( %s -> ( P x. %s ) = ( P x. 1 ) )' % (A, PRD('(/)')))], 'eqtrd',
             '( %s -> %s = ( P x. 1 ) )' % (A, PRD('( <" P "> ++ (/) )')))
    e2 = w.s([e1, w.s([w.s([w.s([], 'id', '( P e. NN0 -> P e. NN0 )')], 'nn0cnd', '( %s -> P e. CC )' % A)], 'mulridd',
                      '( %s -> ( P x. 1 ) = P )' % A)], 'eqtrd', '( %s -> %s = P )' % (A, PRD('( <" P "> ++ (/) )')))
    w.qed([w.s([pr], 'eqcomd', '( %s -> %s = %s )' % (A, PRD('<" P ">'), PRD('( <" P "> ++ (/) )'))), e2], 'eqtrd',
          '( %s -> %s = P )' % (A, PRD('<" P ">')))
    run(w)

# ------------------------------------------------------------------ modmulr
if not only or 'modmulr' in only:
    w = W('modmulr', 'A factor may be reduced modulo the modulus before multiplying.')
    A = '( A e. NN0 /\\ B e. NN0 /\\ L e. NN )'
    aa = w.s([], 'simp1', '( %s -> A e. NN0 )' % A)
    bb = w.s([], 'simp2', '( %s -> B e. NN0 )' % A)
    ll = w.s([], 'simp3', '( %s -> L e. NN )' % A)
    ar = w.s([aa], 'nn0red', '( %s -> A e. RR )' % A)
    bz = w.s([bb], 'nn0zd', '( %s -> B e. ZZ )' % A)
    lp = w.s([ll, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % A)
    mr = w.s([w.s([w.s([aa], 'nn0zd', '( %s -> A e. ZZ )' % A), ll, w.inst('zmodcl')], 'syl2anc',
                  '( %s -> ( A mod L ) e. NN0 )' % A)], 'nn0red', '( %s -> ( A mod L ) e. RR )' % A)
    ab = w.s([ar, lp, w.inst('modabs2')], 'syl2anc', '( %s -> ( ( A mod L ) mod L ) = ( A mod L ) )' % A)
    w.qed([w.s([mr, ar], 'jca', '( %s -> ( ( A mod L ) e. RR /\\ A e. RR ) )' % A),
           w.s([bz, lp], 'jca', '( %s -> ( B e. ZZ /\\ L e. RR+ ) )' % A), ab, w.inst('modmul1')], 'syl3anc',
          '( %s -> ( ( ( A mod L ) x. B ) mod L ) = ( ( A x. B ) mod L ) )' % A)
    run(w)

# ------------------------------------------------------------------ unsndif
if not only or 'unsndif' in only:
    w = W('unsndif', 'Removing the singleton again from a set it was added to.')
    e1 = w.s([], 'difundir', '( ( { P } u. B ) \\ { P } ) = ( ( { P } \\ { P } ) u. ( B \\ { P } ) )')
    e2 = w.s([w.s([], 'difid', '( { P } \\ { P } ) = (/)')], 'uneq1i',
             '( ( { P } \\ { P } ) u. ( B \\ { P } ) ) = ( (/) u. ( B \\ { P } ) )')
    e3 = w.s([w.s([], 'uncom', '( (/) u. ( B \\ { P } ) ) = ( ( B \\ { P } ) u. (/) )'),
              w.s([], 'un0', '( ( B \\ { P } ) u. (/) ) = ( B \\ { P } )')], 'eqtri',
             '( (/) u. ( B \\ { P } ) ) = ( B \\ { P } )')
    eq = w.s([e1, w.s([e2, e3], 'eqtri', '( ( { P } \\ { P } ) u. ( B \\ { P } ) ) = ( B \\ { P } )')], 'eqtri',
             '( ( { P } u. B ) \\ { P } ) = ( B \\ { P } )')
    w.qed([eq, w.s([], 'difss', '( B \\ { P } ) C_ B')], 'eqsstri', '( ( { P } u. B ) \\ { P } ) C_ B')
    run(w)

# ------------------------------------------------------------------ prodsplitp
if not only or 'prodsplitp' in only:
    w = W('prodsplitp', 'Splitting one element out of a finite product (Lean: Finset.mul_prod_erase).')
    A = '( S e. Fin /\\ S C_ NN0 /\\ P e. S )'
    fi = w.s([], 'simp1', '( %s -> S e. Fin )' % A)
    sn = w.s([], 'simp2', '( %s -> S C_ NN0 )' % A)
    ps = w.s([], 'simp3', '( %s -> P e. S )' % A)
    bd = w.s([w.s([w.s([sn], 'adantr', '( ( %s /\\ q e. S ) -> S C_ NN0 )' % A),
                   w.s([], 'simpr', '( ( %s /\\ q e. S ) -> q e. S )' % A)], 'sseldd',
                  '( ( %s /\\ q e. S ) -> q e. NN0 )' % A)], 'nn0cnd', '( ( %s /\\ q e. S ) -> q e. CC )' % A)
    dd = w.s([], 'simpr', '( ( %s /\\ q = P ) -> q = P )' % A)
    w.qed([fi, bd, ps, dd], 'fprodsplit1', '( %s -> prod_ q e. S q = ( P x. prod_ q e. ( S \\ { P } ) q ) )' % A)
    run(w)
