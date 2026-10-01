"""Sortie A4c, batch 15: the remaining pieces of the round argument."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ------------------------------------------------------------------ extgox
if not only or 'extgox' in only:
    w = W('extgox', 'A nonempty sublist of the pool forces the ceiling to be at least one.')
    A = '( ( S e. Word NN0 /\\ S =/= (/) ) /\\ ( A. q e. ran S 2 <_ q /\\ A. q e. ran S q <_ X /\\ X e. NN0 ) )'
    ss = w.s([w.s([], 'simpl', '( %s -> ( S e. Word NN0 /\\ S =/= (/) ) )' % A)], 'simpld', '( %s -> S e. Word NN0 )' % A)
    snz = w.s([w.s([], 'simpl', '( %s -> ( S e. Word NN0 /\\ S =/= (/) ) )' % A)], 'simprd', '( %s -> S =/= (/) )' % A)
    q2 = w.s([w.s([], 'simpr', '( %s -> ( A. q e. ran S 2 <_ q /\\ A. q e. ran S q <_ X /\\ X e. NN0 ) )' % A)], 'simp1d',
             '( %s -> A. q e. ran S 2 <_ q )' % A)
    qx = w.s([w.s([], 'simpr', '( %s -> ( A. q e. ran S 2 <_ q /\\ A. q e. ran S q <_ X /\\ X e. NN0 ) )' % A)], 'simp2d',
             '( %s -> A. q e. ran S q <_ X )' % A)
    xx = w.s([w.s([], 'simpr', '( %s -> ( A. q e. ran S 2 <_ q /\\ A. q e. ran S q <_ X /\\ X e. NN0 ) )' % A)], 'simp3d',
             '( %s -> X e. NN0 )' % A)
    lnn = w.s([ss, snz, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` S ) e. NN )' % A)
    zfz = w.s([lnn, w.s([w.s([], 'lbfzo0', '( 0 e. ( 0 ..^ ( # ` S ) ) <-> ( # ` S ) e. NN )')], 'a1i',
                        '( %s -> ( 0 e. ( 0 ..^ ( # ` S ) ) <-> ( # ` S ) e. NN ) )' % A)], 'mpbird',
              '( %s -> 0 e. ( 0 ..^ ( # ` S ) ) )' % A)
    s0r = w.s([w.s([ss, w.inst('wrdfn')], 'syl', '( %s -> S Fn ( 0 ..^ ( # ` S ) ) )' % A), zfz, w.inst('fnfvelrn')], 'syl2anc',
              '( %s -> ( S ` 0 ) e. ran S )' % A)
    g2 = w.s([w.s([], 'breq2', '( q = ( S ` 0 ) -> ( 2 <_ q <-> 2 <_ ( S ` 0 ) ) )'), q2, s0r], 'rspcdva',
             '( %s -> 2 <_ ( S ` 0 ) )' % A)
    gx = w.s([w.s([], 'breq1', '( q = ( S ` 0 ) -> ( q <_ X <-> ( S ` 0 ) <_ X ) )'), qx, s0r], 'rspcdva',
             '( %s -> ( S ` 0 ) <_ X )' % A)
    s0n = w.s([w.s([ss, s0r], 'jca', '( %s -> ( S e. Word NN0 /\\ ( S ` 0 ) e. ran S ) )' % A), w.inst('algwrdrn')], 'syl',
              '( %s -> ( S ` 0 ) e. NN0 )' % A)
    li = lin.linarith(w, A, [g2, gx], '1 <_ X',
                      leaves={'( S ` 0 )': w.s([s0n], 'nn0red', '( %s -> ( S ` 0 ) e. RR )' % A),
                              'X': w.s([xx], 'nn0red', '( %s -> X e. RR )' % A)})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)

# ------------------------------------------------------------------ extgol6
if not only or 'extgol6' in only:
    w = W('extgol6', 'A product of two numbers congruent to one is congruent to one.')
    A = '( ( L e. NN /\\ M e. NN0 /\\ S e. NN0 ) /\\ ( L || ( M - 1 ) /\\ L || ( S - 1 ) ) )'
    ll = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ M e. NN0 /\\ S e. NN0 ) )' % A)], 'simp1d', '( %s -> L e. NN )' % A)
    mm = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ M e. NN0 /\\ S e. NN0 ) )' % A)], 'simp2d', '( %s -> M e. NN0 )' % A)
    sss = w.s([w.s([], 'simpl', '( %s -> ( L e. NN /\\ M e. NN0 /\\ S e. NN0 ) )' % A)], 'simp3d', '( %s -> S e. NN0 )' % A)
    d1 = w.s([], 'simprl', '( %s -> L || ( M - 1 ) )' % A)
    d2 = w.s([], 'simprr', '( %s -> L || ( S - 1 ) )' % A)
    lz = w.s([ll], 'nnzd', '( %s -> L e. ZZ )' % A)
    mz = w.s([mm], 'nn0zd', '( %s -> M e. ZZ )' % A)
    sz = w.s([sss], 'nn0zd', '( %s -> S e. ZZ )' % A)
    m1z = w.s([mz, w.inst('peano2zm')], 'syl', '( %s -> ( M - 1 ) e. ZZ )' % A)
    s1z = w.s([sz, w.inst('peano2zm')], 'syl', '( %s -> ( S - 1 ) e. ZZ )' % A)
    dmul = w.s([w.s([w.s([lz, m1z, sz], '3jca', '( %s -> ( L e. ZZ /\\ ( M - 1 ) e. ZZ /\\ S e. ZZ ) )' % A),
                     w.inst('dvdsmultr1')], 'syl', '( %s -> ( L || ( M - 1 ) -> L || ( ( M - 1 ) x. S ) ) )' % A), d1], 'mpd',
               '( %s -> L || ( ( M - 1 ) x. S ) )' % A)
    add = w.s([w.s([w.s([lz, w.s([m1z, sz], 'zmulcld', '( %s -> ( ( M - 1 ) x. S ) e. ZZ )' % A), s1z], '3jca',
                        '( %s -> ( L e. ZZ /\\ ( ( M - 1 ) x. S ) e. ZZ /\\ ( S - 1 ) e. ZZ ) )' % A),
                    w.inst('dvds2add')], 'syl',
                   '( %s -> ( ( L || ( ( M - 1 ) x. S ) /\\ L || ( S - 1 ) ) -> L || ( ( ( M - 1 ) x. S ) + ( S - 1 ) ) ) )' % A),
               w.s([dmul, d2], 'jca', '( %s -> ( L || ( ( M - 1 ) x. S ) /\\ L || ( S - 1 ) ) )' % A)], 'mpd',
              '( %s -> L || ( ( ( M - 1 ) x. S ) + ( S - 1 ) ) )' % A)
    mc = w.s([mm], 'nn0cnd', '( %s -> M e. CC )' % A)
    sc = w.s([sss], 'nn0cnd', '( %s -> S e. CC )' % A)
    e1 = w.s([mc, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A), sc], 'subdird',
             '( %s -> ( ( M - 1 ) x. S ) = ( ( M x. S ) - ( 1 x. S ) ) )' % A)
    e2 = w.s([e1, w.s([w.s([sc], 'mullidd', '( %s -> ( 1 x. S ) = S )' % A)], 'oveq2d',
                      '( %s -> ( ( M x. S ) - ( 1 x. S ) ) = ( ( M x. S ) - S ) )' % A)], 'eqtrd',
             '( %s -> ( ( M - 1 ) x. S ) = ( ( M x. S ) - S ) )' % A)
    msr = w.s([w.s([mm, sss], 'nn0mulcld', '( %s -> ( M x. S ) e. NN0 )' % A)], 'nn0red', '( %s -> ( M x. S ) e. RR )' % A)
    sr = w.s([sss], 'nn0red', '( %s -> S e. RR )' % A)
    w.qed([add, w.s([w.s([e2], 'oveq1d',
                         '( %s -> ( ( ( M - 1 ) x. S ) + ( S - 1 ) ) = ( ( ( M x. S ) - S ) + ( S - 1 ) ) )' % A),
                     w.s([w.s([msr], 'recnd', '( %s -> ( M x. S ) e. CC )' % A), sc,
                          w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A)], 'npncand',
                         '( %s -> ( ( ( M x. S ) - S ) + ( S - 1 ) ) = ( ( M x. S ) - 1 ) )' % A)],
                    'eqtrd', '( %s -> ( ( ( M - 1 ) x. S ) + ( S - 1 ) ) = ( ( M x. S ) - 1 ) )' % A)], 'breqtrd',
          '( %s -> L || ( ( M x. S ) - 1 ) )' % A)
    run(w)

# ------------------------------------------------------------------ extgocbe / extgocbf
if not only or 'extgocbe' in only:
    w = W('extgocbe', 'The supply inequality across one element processed without a hit.')
    A = '( ( A e. RR /\\ C e. RR /\\ D e. RR ) /\\ ( E e. RR /\\ A <_ ( ( ( C + 1 ) + D ) + E ) ) )'
    aa = w.s([w.s([], 'simpl', '( %s -> ( A e. RR /\\ C e. RR /\\ D e. RR ) )' % A)], 'simp1d', '( %s -> A e. RR )' % A)
    cc = w.s([w.s([], 'simpl', '( %s -> ( A e. RR /\\ C e. RR /\\ D e. RR ) )' % A)], 'simp2d', '( %s -> C e. RR )' % A)
    dd = w.s([w.s([], 'simpl', '( %s -> ( A e. RR /\\ C e. RR /\\ D e. RR ) )' % A)], 'simp3d', '( %s -> D e. RR )' % A)
    ee = w.s([], 'simprl', '( %s -> E e. RR )' % A)
    h1 = w.s([], 'simprr', '( %s -> A <_ ( ( ( C + 1 ) + D ) + E ) )' % A)
    li = lin.linarith(w, A, [h1], 'A <_ ( ( C + D ) + ( E + 1 ) )', leaves={'A': aa, 'C': cc, 'D': dd, 'E': ee})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)

if not only or 'extgocbf' in only:
    w = W('extgocbf', 'The supply inequality across a hit and a reset.')
    A = ('( ( A e. RR /\\ C e. RR /\\ D e. RR ) /\\ ( E e. RR /\\ B e. RR ) /\\ '
         '( A <_ ( ( ( C + 1 ) + D ) + E ) /\\ ( E + 1 ) <_ B ) )')
    aa = w.s([w.s([], 'simp1', '( %s -> ( A e. RR /\\ C e. RR /\\ D e. RR ) )' % A)], 'simp1d', '( %s -> A e. RR )' % A)
    cc = w.s([w.s([], 'simp1', '( %s -> ( A e. RR /\\ C e. RR /\\ D e. RR ) )' % A)], 'simp2d', '( %s -> C e. RR )' % A)
    dd = w.s([w.s([], 'simp1', '( %s -> ( A e. RR /\\ C e. RR /\\ D e. RR ) )' % A)], 'simp3d', '( %s -> D e. RR )' % A)
    ee = w.s([w.s([], 'simp2', '( %s -> ( E e. RR /\\ B e. RR ) )' % A)], 'simpld', '( %s -> E e. RR )' % A)
    bb = w.s([w.s([], 'simp2', '( %s -> ( E e. RR /\\ B e. RR ) )' % A)], 'simprd', '( %s -> B e. RR )' % A)
    h1 = w.s([w.s([], 'simp3', '( %s -> ( A <_ ( ( ( C + 1 ) + D ) + E ) /\\ ( E + 1 ) <_ B ) )' % A)], 'simpld',
             '( %s -> A <_ ( ( ( C + 1 ) + D ) + E ) )' % A)
    h2 = w.s([w.s([], 'simp3', '( %s -> ( A <_ ( ( ( C + 1 ) + D ) + E ) /\\ ( E + 1 ) <_ B ) )' % A)], 'simprd',
             '( %s -> ( E + 1 ) <_ B )' % A)
    li = lin.linarith(w, A, [h1, h2], 'A <_ ( ( C + ( D + B ) ) + 0 )',
                      leaves={'A': aa, 'C': cc, 'D': dd, 'E': ee, 'B': bb})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)
