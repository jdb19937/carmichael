"""Sortie DSH, section D: dshnum (Lean pole_threshold_numeric), dshepb (Lean norm_Epole_le_of_height).
Run: MM_DB=sorties/dsh.mm MM_ENGINE=mmatch LIN_FAST=1 python3 tools/gen/dsh_e.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dshlib import *
from tm import W
from z6a_e3 import unpack, c_
from cl import lift
import lin
from lin import linarith
import num

only = sys.argv[1:]
want = lambda l: not only or l in only
mk = lambda w, a: (lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g)))
C3339 = '( ; ; ; 3 3 3 9 / ; ; ; 5 0 0 0 )'
N65 = '; ; ; ; 6 5 5 3 6'
N16 = '; 1 6'

if want('dshnum'):
    w = W('dshnum', 'The pole threshold (Lean ` pole_threshold_numeric ` with the constant of ~ z5dgamh ): ` 960 x <_ e ^ ( ( 3339 / 5000 ) x ) ` for ` x >_ 40 ` , '
          'from ` e ^ ( x / 6 ) >_ 1 + x / 6 ` (~ bvefge1p ) and ` e ^ 16 >_ 2 ^ 16 = 65536 ` (~ egt2lt3 , ~ 2exp16 ).')
    a = '( X e. RR /\\ ; 4 0 <_ X )'; t = mk(w, a)
    xr = t([], 'simpl', 'X e. RR'); x40 = t([], 'simpr', '; 4 0 <_ X')
    L = {'X': xr}
    six = c_(w, a, num.real(w, '6'), '6 e. RR'); s6c = c_(w, a, num.cc(w, '6'), '6 e. CC')
    Y = '( X / 6 )'
    yr = t([xr, six, c_(w, a, w.s([w.s([], '6pos', '0 < 6')], 'gt0ne0ii' if False else 'x', 'x'), 'x') if False else
            c_(w, a, w.s([w.s([], '6re', '6 e. RR'), w.s([], '6pos', '0 < 6')], 'gt0ne0ii', '6 =/= 0'), '6 =/= 0')], 'redivcld', '%s e. RR' % Y)
    L[Y] = yr
    y0 = linarith(w, a, [x40], '0 <_ %s' % Y, leaves={'X': xr})
    e1 = t([t([yr, y0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (Y, Y)), w.inst('bvefge1p')], 'syl', '( 1 + %s ) <_ ( exp ` %s )' % (Y, Y))
    # e ^ 16 >_ 65536 (closed)
    z16 = num.fact(w, N16, 'zz') if False else None
    n16z = w.s([w.s([], 'x', 'x')], 'x', 'x') if False else None
    i16 = num.z_nat(w, 16)
    ex = w.s([w.s([], 'ax-1cn', '1 e. CC'), i16, w.inst('efexp')], 'mp2an', '( exp ` ( %s x. 1 ) ) = ( ( exp ` 1 ) ^ %s )' % (N16, N16))
    m1 = w.s([num.cc(w, '; 1 6')], 'mulridi', '( %s x. 1 ) = %s' % (N16, N16))
    ex2 = w.s([w.s([m1], 'fveq2i', '( exp ` ( %s x. 1 ) ) = ( exp ` %s )' % (N16, N16)), ex], 'eqtr3i', '( exp ` %s ) = ( ( exp ` 1 ) ^ %s )' % (N16, N16))
    de = w.s([w.s([], 'df-e', '_e = ( exp ` 1 )')], 'oveq1i', '( _e ^ %s ) = ( ( exp ` 1 ) ^ %s )' % (N16, N16))
    ex3 = w.s([ex2, de], 'eqtr4i', '( exp ` %s ) = ( _e ^ %s )' % (N16, N16))
    e2 = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e')
    rer = w.s([], 'ere', '_e e. RR')
    le2 = w.s([w.s([], '2re', '2 e. RR'), rer, e2], 'ltleii', '2 <_ _e')
    pw = w.s([w.s([w.s([w.s([], '2re', '2 e. RR'), rer, num.nn0(w, 16)], '3pm3.2i', '( 2 e. RR /\\ _e e. RR /\\ %s e. NN0 )' % N16),
                   w.s([w.s([], '0le2', '0 <_ 2'), le2], 'pm3.2i', '( 0 <_ 2 /\\ 2 <_ _e )')], 'pm3.2i',
                  '( ( 2 e. RR /\\ _e e. RR /\\ %s e. NN0 ) /\\ ( 0 <_ 2 /\\ 2 <_ _e ) )' % N16), w.inst('leexp1a')], 'ax-mp', '( 2 ^ %s ) <_ ( _e ^ %s )' % (N16, N16))
    pw2 = w.s([w.s([], '2exp16', '( 2 ^ %s ) = %s' % (N16, N65)), pw], 'eqbrtrri', '%s <_ ( _e ^ %s )' % (N65, N16))
    e16 = c_(w, a, w.s([pw2, ex3], 'breqtrri', '%s <_ ( exp ` %s )' % (N65, N16)), '%s <_ ( exp ` %s )' % (N65, N16))
    # the product
    r16 = c_(w, a, num.real(w, N16), '%s e. RR' % N16)
    ey = t([yr], 'reefcld', '( exp ` %s ) e. RR' % Y); e16r = t([r16], 'reefcld', '( exp ` %s ) e. RR' % N16)
    one = c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')
    y1 = t([one, yr], 'readdcld', '( 1 + %s ) e. RR' % Y)
    r65 = c_(w, a, num.real(w, N65), '%s e. RR' % N65)
    y10 = linarith(w, a, [x40], '0 <_ ( 1 + %s )' % Y, leaves=L)
    g65 = c_(w, a, num.fact(w, N65, 'ge0'), '0 <_ %s' % N65)
    pr = t([y1, ey, r65, e16r, y10, g65, e1, e16], 'lemul12ad', '( ( 1 + %s ) x. %s ) <_ ( ( exp ` %s ) x. ( exp ` %s ) )' % (Y, N65, Y, N16))
    ea = t([t([yr], 'recnd', '%s e. CC' % Y), t([r16], 'recnd', '%s e. CC' % N16), w.inst('efadd')], 'syl2anc',
           '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (Y, N16, Y, N16))
    pr2 = t([pr, ea], 'breqtrrd', '( ( 1 + %s ) x. %s ) <_ ( exp ` ( %s + %s ) )' % (Y, N65, Y, N16))
    CX = '( %s x. X )' % C3339
    cxr = t([c_(w, a, num.real(w, C3339), '%s e. RR' % C3339), xr], 'remulcld', '%s e. RR' % CX)
    le = linarith(w, a, [x40], '( %s + %s ) <_ %s' % (Y, N16, CX), leaves=L)
    ef = t([le, t([t([yr, r16], 'readdcld', '( %s + %s ) e. RR' % (Y, N16)), cxr, w.inst('efle')], 'syl2anc',
                  '( ( %s + %s ) <_ %s <-> ( exp ` ( %s + %s ) ) <_ ( exp ` %s ) )' % (Y, N16, CX, Y, N16, CX))], 'mpbid',
           '( exp ` ( %s + %s ) ) <_ ( exp ` %s )' % (Y, N16, CX))
    lo = linarith(w, a, [x40], '( ; ; 9 6 0 x. X ) <_ ( ( 1 + %s ) x. %s )' % (Y, N65), leaves=L)
    s1 = t([lo, pr2], 'letrd' if False else 'x', 'x') if False else None
    q1 = t([t([num.real(w, '; ; 9 6 0') and c_(w, a, num.real(w, '; ; 9 6 0'), '; ; 9 6 0 e. RR'), xr], 'remulcld', '( ; ; 9 6 0 x. X ) e. RR'),
            t([y1, r65], 'remulcld', '( ( 1 + %s ) x. %s ) e. RR' % (Y, N65)), t([t([yr, r16], 'readdcld', '( %s + %s ) e. RR' % (Y, N16))], 'reefcld',
                                                                                  '( exp ` ( %s + %s ) ) e. RR' % (Y, N16)), lo, pr2], 'letrd',
           '( ; ; 9 6 0 x. X ) <_ ( exp ` ( %s + %s ) )' % (Y, N16))
    q2 = t([t([c_(w, a, num.real(w, '; ; 9 6 0'), '; ; 9 6 0 e. RR'), xr], 'remulcld', '( ; ; 9 6 0 x. X ) e. RR'),
            t([t([yr, r16], 'readdcld', '( %s + %s ) e. RR' % (Y, N16))], 'reefcld', '( exp ` ( %s + %s ) ) e. RR' % (Y, N16)),
            t([cxr], 'reefcld', '( exp ` %s ) e. RR' % CX), q1, ef], 'letrd', '( ; ; 9 6 0 x. X ) <_ ( exp ` %s )' % CX)
    toqed(w, q2, 'dshnum'); w.run()

from z5clib import HAB0
if want('dshepb'):
    w = W('dshepb', '**Lean ` norm_Epole_le_of_height ` ** (L1.b): the principal pole term of the half-line detector is at most ` 1 / 8 ` once '
          '` log D <_ | Im S | ` , ` log D >_ 40 ` , ` 39 / 50 <_ Re S <_ 1 ` : ` | Gamma ( 1 - S ) | <_ 60 e ^ -| Im S | ` (~ z5dgamh ), '
          '` | Y ^ ( 1 - S ) | <_ Y ^ ( 11 / 50 ) = D ^ ( 1661 / 5000 ) ` (~ z5xabs ), ` phi ( N ) / N <_ 1 ` , ` | M_1 ( 1 ) | <_ 1 + log 2 D ` (~ z5mr1 ), and ~ dshnum .')
    a = split_imp_ = STATEMENTS['dshepb']
    from cl import split_imp
    a = split_imp(STATEMENTS['dshepb'])[0]; t = mk(w, a); f = unpack(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']; l40 = f['; 4 0 <_ ( log ` D )']; nn = f['N e. NN']; sc = f['S e. CC']
    lo = f['( ; 3 9 / ; 5 0 ) <_ ( Re ` S )']; hi = f['( Re ` S ) <_ 1']; lim = f['( log ` D ) <_ ( abs ` ( Im ` S ) )']
    I = '( abs ` ( Im ` S ) )'; Lg = '( log ` D )'
    zz = t([t([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('dshzz')], 'syl', '( D e. RR+ /\\ ( 2 x. D ) e. RR+ /\\ D < ( 2 x. D ) )')
    drp = t([zz], 'simp1d', 'D e. RR+'); d2rp = t([zz], 'simp2d', '( 2 x. D ) e. RR+'); dlt = t([zz], 'simp3d', 'D < ( 2 x. D )')
    HAB = '( ( D e. RR /\\ 0 < D ) /\\ ( ( 2 x. D ) e. RR /\\ D < ( 2 x. D ) ) )'
    hab = t([t([dr, t([drp], 'rpgt0d', '0 < D')], 'jca', '( D e. RR /\\ 0 < D )'), t([t([d2rp], 'rpred', '( 2 x. D ) e. RR'), dlt], 'jca',
                                                                                        '( ( 2 x. D ) e. RR /\\ D < ( 2 x. D ) )')], 'jca', HAB)
    yy = t([t([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('dshyp')], 'syl', '( %s e. RR+ /\\ 1 < %s )' % (YP, YP))
    yrp = t([yy], 'simpld', '%s e. RR+' % YP)
    prx = c_(w, a, w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % PRN), '%s e. _V' % PRN)
    M1 = '( ( <. D , ( 2 x. D ) >. Mr <. %s , 1 >. ) ` 1 )' % PRN
    G = '( _G ` ( 1 - S ) )'; XP = '( %s ^c ( 1 - S ) )' % YP; Q = '( ( phi ` N ) / N )'
    GXQ = '( ( %s x. %s ) x. %s )' % (G, XP, Q)
    V = '( %s x. %s )' % (GXQ, M1)
    ep = t([t([t([t([hab, yrp], 'jca', '( %s /\\ %s e. RR+ )' % (HAB, YP)), t([prx, nn], 'jca', '( %s e. _V /\\ N e. NN )' % PRN)], 'jca',
                 '( ( %s /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ N e. NN ) )' % (HAB, YP, PRN)), sc], 'jca',
              '( ( ( %s /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ N e. NN ) ) /\\ S e. CC )' % (HAB, YP, PRN)), w.inst('dshep1')], 'syl',
           '%s = if ( %s = %s , %s , 0 )' % (EPH(PRN), PRN, PRN, V))
    it = c_(w, a, w.s([w.s([], 'eqid', '%s = %s' % (PRN, PRN)), w.s([], 'iftrue', '( %s = %s -> if ( %s = %s , %s , 0 ) = %s )' % (PRN, PRN, PRN, PRN, V, V))],
                      'ax-mp', 'if ( %s = %s , %s , 0 ) = %s' % (PRN, PRN, V, V)), 'if ( %s = %s , %s , 0 ) = %s' % (PRN, PRN, V, V))
    ev = t([ep, it], 'eqtrd', '%s = %s' % (EPH(PRN), V))
    # S =/= 1 and closures
    rs = t([sc], 'recld', '( Re ` S )  e. RR'.replace('  ', ' ')); ims = t([sc], 'imcld', '( Im ` S ) e. RR')
    imc = t([ims], 'recnd', '( Im ` S ) e. CC'); ir = t([imc], 'abscld', '%s e. RR' % I)
    lr = t([dr, t([drp], 'rpne0d' if False else 'rpgt0d', '0 < D')], 'x', 'x') if False else t([drp], 'relogcld', '%s e. RR' % Lg)
    L = {'( Re ` S )': rs, I: ir, Lg: lr}
    ig0 = linarith(w, a, [l40, lim], '0 < %s' % I, leaves=L)
    imn0 = t([ig0, t([imc, w.inst('absgt0')], 'syl', '( ( Im ` S ) =/= 0 <-> 0 < %s )' % I)], 'mpbird', '( Im ` S ) =/= 0')
    imn1 = t([imn0, c_(w, a, w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')], 'neeqtrrd', '( Im ` S ) =/= ( Im ` 1 )')
    sn1 = t([imn1, w.s([w.s([], 'fveq2', '( S = 1 -> ( Im ` S ) = ( Im ` 1 ) )')], 'necon3i', '( ( Im ` S ) =/= ( Im ` 1 ) -> S =/= 1 )')], 'syl', 'S =/= 1')
    pdg = t([t([t([sc, t([lo, hi], 'jca', '( ( ; 3 9 / ; 5 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )')], 'jca', SRNGH), sn1], 'jca', '( %s /\\ S =/= 1 )' % SRNGH),
             w.inst('dshpdg')], 'syl', '( 1 - S ) e. %s' % DG)
    gc = t([pdg, w.inst('gamcl')], 'syl', '%s e. CC' % G)
    one_c = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    omc = t([one_c, sc], 'subcld', '( 1 - S ) e. CC')
    xc = t([t([yrp], 'rpcnd', '%s e. CC' % YP), omc], 'cxpcld', '%s e. CC' % XP)
    phr = t([t([nn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nnred', '( phi ` N ) e. RR')
    nr = t([nn], 'nnred', 'N e. RR'); nrp = t([nn], 'nnrpd', 'N e. RR+')
    qr = t([phr, nrp], 'rerpdivcld', '%s e. RR' % Q)
    q0 = t([t([t([nn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nnrpd', '( phi ` N ) e. RR+'), nrp], 'rpdivcld', '%s e. RR+' % Q)
    q0 = t([q0], 'rpge0d', '0 <_ %s' % Q)
    q1 = t([t([nn, w.inst('z5phile')], 'syl', '( phi ` N ) <_ N'), t([phr, nrp, w.inst('divle1le')], 'syl2anc', '( %s <_ 1 <-> ( phi ` N ) <_ N )' % Q)], 'mpbird', '%s <_ 1' % Q)
    pr = t([nn, w.inst('z5prin')], 'syl', split_imp(__import__('dshlib').z6stmt('z5prin'))[1].replace('N e. NN', 'N e. NN'))
    PRF = '( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 )' % (PRN, PRN)
    prf = t([pr], 'simpld', PRF)
    pff = t([prf], 'simpld', '%s : NN --> CC' % PRN)
    one_n = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    m1c = t([t([t([hab, one_n], 'jca', '( %s /\\ 1 e. NN )' % HAB), t([pff, one_c], 'jca', '( %s : NN --> CC /\\ 1 e. CC )' % PRN)], 'jca',
               '( ( %s /\\ 1 e. NN ) /\\ ( %s : NN --> CC /\\ 1 e. CC ) )' % (HAB, PRN)), w.inst('z5mrcl')], 'syl', '%s e. CC' % M1)
    # |V| = ( ( |G| |XP| ) Q ) |M1|
    aG = '( abs ` %s )' % G; aX = '( abs ` %s )' % XP; aM = '( abs ` %s )' % M1
    gx = t([gc, xc], 'mulcld', '( %s x. %s ) e. CC' % (G, XP)); gxq = t([gx, t([qr], 'recnd', '%s e. CC' % Q)], 'mulcld', '%s e. CC' % GXQ)
    b1 = t([gxq, m1c], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (V, GXQ, aM))
    b2 = t([gx, t([qr], 'recnd', '%s e. CC' % Q)], 'absmuld', '( abs ` %s ) = ( ( abs ` ( %s x. %s ) ) x. ( abs ` %s ) )' % (GXQ, G, XP, Q))
    b3 = t([gc, xc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (G, XP, aG, aX))
    b4 = t([qr, q0], 'absidd', '( abs ` %s ) = %s' % (Q, Q))
    b23 = t([b2, t([b3, b4], 'oveq12d', '( ( abs ` ( %s x. %s ) ) x. ( abs ` %s ) ) = ( ( %s x. %s ) x. %s )' % (G, XP, Q, aG, aX, Q))], 'eqtrd',
            '( abs ` %s ) = ( ( %s x. %s ) x. %s )' % (GXQ, aG, aX, Q))
    PV = '( ( ( %s x. %s ) x. %s ) x. %s )' % (aG, aX, Q, aM)
    bv = t([b1, t([b23], 'oveq1d', '( ( abs ` %s ) x. %s ) = %s' % (GXQ, aM, PV))], 'eqtrd', '( abs ` %s ) = %s' % (V, PV))
    # the four bounds
    c60 = '; 6 0'; EI = '( exp ` -u %s )' % I
    gh = c_(w, a, w.s([], 'z5dgamh', __import__('dshlib').z6stmt('z5dgamh')), __import__('dshlib').z6stmt('z5dgamh'))
    rs0 = linarith(w, a, [lo], '0 <_ ( Re ` S )', leaves=L); ih = linarith(w, a, [l40, lim], '( 1 / 2 ) <_ %s' % I, leaves=L)
    bG = t([t([t([c_(w, a, num.real(w, c60), '%s e. RR' % c60), gh], 'jca', '( %s e. RR /\\ %s )' % (c60, __import__('dshlib').z6stmt('z5dgamh'))),
                  t([sc, t([t([rs0, hi], 'jca', '( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )'), ih], 'jca', '( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) /\\ ( 1 / 2 ) <_ %s )' % I)], 'jca',
                    '( S e. CC /\\ ( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) /\\ ( 1 / 2 ) <_ %s ) )' % I)], 'jca',
               '( ( %s e. RR /\\ %s ) /\\ ( S e. CC /\\ ( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) /\\ ( 1 / 2 ) <_ %s ) ) )' % (c60, __import__('dshlib').z6stmt('z5dgamh'), I)),
            w.inst('z5gam1')], 'syl', '%s <_ ( %s x. %s )' % (aG, c60, EI))
    T39 = '( ; 3 9 / ; 5 0 )'; YPT = '( %s ^c ( 1 - %s ) )' % (YP, T39)
    yr = t([yrp], 'rpred', '%s e. RR' % YP); y1 = t([t([yy], 'simprd', '1 < %s' % YP)], 'x', 'x') if False else None
    y1 = t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), yr, t([yy], 'simprd', '1 < %s' % YP)], 'ltled', '1 <_ %s' % YP)
    t39 = c_(w, a, num.real(w, T39), '%s e. RR' % T39)
    bX = t([t([t([yr, y1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (YP, YP)), t([t39, t([sc, lo], 'jca', '( S e. CC /\\ %s <_ ( Re ` S ) )' % T39)], 'jca',
                                                                            '( %s e. RR /\\ ( S e. CC /\\ %s <_ ( Re ` S ) ) )' % (T39, T39))], 'jca',
               '( ( %s e. RR /\\ 1 <_ %s ) /\\ ( %s e. RR /\\ ( S e. CC /\\ %s <_ ( Re ` S ) ) ) )' % (YP, YP, T39, T39)), w.inst('z5xabs')], 'syl', '%s <_ %s' % (aX, YPT))
    # | M_1 ( 1 ) | <_ 1 + log ( 2 D )
    d2r = t([d2rp], 'rpred', '( 2 x. D ) e. RR')
    d21 = linarith(w, a, [d1], '1 <_ ( 2 x. D )', leaves={'D': dr})
    mu1 = c_(w, a, w.s([w.s([], 'muone', '( mmu ` 1 ) = 1'), w.s([], 'ax-1ne0', '1 =/= 0')], 'eqnetri', '( mmu ` 1 ) =/= 0'), '( mmu ` 1 ) =/= 0')
    VAC = 'A. c e. Prime ( c || 1 -> ( %s ` c ) = 1 )' % PRN
    vac = c_(w, a, w.s([w.s([w.s([], 'nprmdvds1', '( c e. Prime -> -. c || 1 )')], 'pm2.21d', '( c e. Prime -> ( c || 1 -> ( %s ` c ) = 1 ) )' % PRN)], 'rgen', VAC), VAC)
    MB = '( ( ( phi ` 1 ) / 1 ) x. ( 1 + ( log ` ( 2 x. D ) ) ) )'
    bM0 = t([t([t([hab, d21], 'jca', '( %s /\\ 1 <_ ( 2 x. D ) )' % HAB), t([t([one_n, mu1], 'jca', '( 1 e. NN /\\ ( mmu ` 1 ) =/= 0 )'), t([prf, vac], 'jca', '( %s /\\ %s )' % (PRF, VAC))],
                                                                               'jca', '( ( 1 e. NN /\\ ( mmu ` 1 ) =/= 0 ) /\\ ( %s /\\ %s ) )' % (PRF, VAC))], 'jca',
                '( ( %s /\\ 1 <_ ( 2 x. D ) ) /\\ ( ( 1 e. NN /\\ ( mmu ` 1 ) =/= 0 ) /\\ ( %s /\\ %s ) ) )' % (HAB, PRF, VAC)), w.inst('z5mr1')], 'syl', '%s <_ %s' % (aM, MB))
    D1 = '( 1 + ( log ` ( 2 x. D ) ) )'
    p1 = c_(w, a, w.s([], 'phi1', '( phi ` 1 ) = 1'), '( phi ` 1 ) = 1')
    pe = t([t([t([p1], 'oveq1d', '( ( phi ` 1 ) / 1 ) = ( 1 / 1 )'), c_(w, a, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')], 'eqtrd', '( ( phi ` 1 ) / 1 ) = 1')],
           'oveq1d', '%s = ( 1 x. %s )' % (MB, D1))
    lg2 = t([d2rp], 'relogcld', '( log ` ( 2 x. D ) ) e. RR')
    d1r = t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), lg2], 'readdcld', '%s e. RR' % D1)
    pe2 = t([pe, t([t([d1r], 'recnd', '%s e. CC' % D1)], 'mullidd', '( 1 x. %s ) = %s' % (D1, D1))], 'eqtrd', '%s = %s' % (MB, D1))
    bM = t([bM0, pe2], 'breqtrd', '%s <_ %s' % (aM, D1))
    # product of the bounds
    aGr = t([gc], 'abscld', '%s e. RR' % aG); aXr = t([xc], 'abscld', '%s e. RR' % aX); aMr = t([m1c], 'abscld', '%s e. RR' % aM)
    aG0 = t([gc], 'absge0d', '0 <_ %s' % aG); aX0 = t([xc], 'absge0d', '0 <_ %s' % aX); aM0 = t([m1c], 'absge0d', '0 <_ %s' % aM)
    eir = t([t([ir], 'renegcld', '-u %s e. RR' % I)], 'reefcld', '%s e. RR' % EI)
    A1 = '( %s x. %s )' % (c60, EI)
    a1r = t([c_(w, a, num.real(w, c60), '%s e. RR' % c60), eir], 'remulcld', '%s e. RR' % A1)
    ypr = t([yrp, t([t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), t39], 'resubcld', '( 1 - %s ) e. RR' % T39)], 'x', 'x') if False else
             t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), t39], 'resubcld', '( 1 - %s ) e. RR' % T39)], 'rpcxpcld', '%s e. RR+' % YPT)
    ypr_ = t([ypr], 'rpred', '%s e. RR' % YPT)
    s1 = t([aGr, a1r, aXr, ypr_, aG0, aX0, bG, bX], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (aG, aX, A1, YPT))
    gxr = t([aGr, aXr], 'remulcld', '( %s x. %s ) e. RR' % (aG, aX))
    s2 = t([gxr, t([a1r, ypr_], 'remulcld', '( %s x. %s ) e. RR' % (A1, YPT)), qr, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'),
            t([aGr, aXr, aG0, aX0], 'mulge0d', '0 <_ ( %s x. %s )' % (aG, aX)), q0, s1, q1], 'lemul12ad',
           '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. 1 )' % (aG, aX, Q, A1, YPT))
    gxqr = t([gxr, qr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (aG, aX, Q))
    R2 = '( ( %s x. %s ) x. 1 )' % (A1, YPT)
    r2r = t([t([a1r, ypr_], 'remulcld', '( %s x. %s ) e. RR' % (A1, YPT)), c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'remulcld', '%s e. RR' % R2)
    s3 = t([gxqr, r2r, aMr, d1r, t([gxr, qr, t([aGr, aXr, aG0, aX0], 'mulge0d', '0 <_ ( %s x. %s )' % (aG, aX)), q0], 'mulge0d', '0 <_ ( ( %s x. %s ) x. %s )' % (aG, aX, Q)),
            aM0, s2, bM], 'lemul12ad', '%s <_ ( %s x. %s )' % (PV, R2, D1))
    # the exponential bookkeeping: e ^ -| Im S | Y ^ ( 11 / 50 ) <_ e ^ -( 3339 / 5000 ) log D = 1 / QQ
    K = '( %s x. ( 1 - %s ) )' % (Y151, T39)
    kr = t([c_(w, a, num.real(w, Y151), '%s e. RR' % Y151), t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), t39], 'resubcld', '( 1 - %s ) e. RR' % T39)], 'remulcld', '%s e. RR' % K)
    cm = t([drp, c_(w, a, num.real(w, Y151), '%s e. RR' % Y151), t([t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), t39], 'resubcld', '( 1 - %s ) e. RR' % T39)], 'recnd',
                                                                                         '( 1 - %s ) e. CC' % T39)], 'cxpmuld' if False else 'x', 'x') if False else None
    cm = t([t([drp, c_(w, a, num.real(w, Y151), '%s e. RR' % Y151), t([t([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), t39], 'resubcld', '( 1 - %s ) e. RR' % T39)], 'recnd',
                                                                                                '( 1 - %s ) e. CC' % T39)], '3jca',
               '( D e. RR+ /\\ %s e. RR /\\ ( 1 - %s ) e. CC )' % (Y151, T39)), w.inst('cxpmul')], 'syl', '( D ^c %s ) = %s' % (K, YPT))
    KL = '( %s x. %s )' % (K, Lg); EK = '( exp ` %s )' % KL
    ce = t([t([t([drp], 'rpcnd', 'D e. CC'), t([drp], 'rpne0d', 'D =/= 0'), t([kr], 'recnd', '%s e. CC' % K)], '3jca', '( D e. CC /\\ D =/= 0 /\\ %s e. CC )' % K),
            w.inst('cxpef')], 'syl', '( D ^c %s ) = %s' % (K, EK))
    ye0 = t([cm, ce], 'eqtr3d', '%s = %s' % (YPT, EK))
    C1661 = '( ; ; ; 1 6 6 1 / ; ; ; 5 0 0 0 )'
    ek_ = lin.lineq(w, a, K, C1661, leaves={})
    KL = '( %s x. %s )' % (C1661, Lg)
    ye = t([ye0, t([t([ek_], 'oveq1d', '( %s x. %s ) = %s' % (K, Lg, KL))], 'fveq2d', '%s = ( exp ` %s )' % (EK, KL))], 'eqtrd', '%s = ( exp ` %s )' % (YPT, KL))
    EK = '( exp ` %s )' % KL
    klr = t([c_(w, a, num.real(w, C1661), '%s e. RR' % C1661), lr], 'remulcld', '%s e. RR' % KL)
    ea = t([t([t([ir], 'renegcld', '-u %s e. RR' % I)], 'recnd', '-u %s e. CC' % I), t([klr], 'recnd', '%s e. CC' % KL), w.inst('efadd')], 'syl2anc',
           '( exp ` ( -u %s + %s ) ) = ( %s x. %s )' % (I, KL, EI, EK))
    CL_ = '( %s x. %s )' % (C3339, Lg)
    clr = t([c_(w, a, num.real(w, C3339), '%s e. RR' % C3339), lr], 'remulcld', '%s e. RR' % CL_)
    Lx = dict(L); Lx[KL] = klr
    lex = linarith(w, a, [lim], '( -u %s + %s ) <_ -u %s' % (I, KL, CL_), leaves=L)
    efl = t([lex, t([t([t([ir], 'renegcld', '-u %s e. RR' % I), klr], 'readdcld', '( -u %s + %s ) e. RR' % (I, KL)), t([clr], 'renegcld', '-u %s e. RR' % CL_), w.inst('efle')],
                    'syl2anc', '( ( -u %s + %s ) <_ -u %s <-> ( exp ` ( -u %s + %s ) ) <_ ( exp ` -u %s ) )' % (I, KL, CL_, I, KL, CL_))], 'mpbid',
            '( exp ` ( -u %s + %s ) ) <_ ( exp ` -u %s )' % (I, KL, CL_))
    QQ = '( exp ` %s )' % CL_
    en = t([t([clr], 'recnd', '%s e. CC' % CL_), w.inst('efneg')], 'syl', '( exp ` -u %s ) = ( 1 / %s )' % (CL_, QQ))
    ek = t([t([ea], 'eqcomd', '( %s x. %s ) = ( exp ` ( -u %s + %s ) )' % (EI, EK, I, KL)), t([efl, en], 'breqtrd', '( exp ` ( -u %s + %s ) ) <_ ( 1 / %s )' % (I, KL, QQ))],
           'eqbrtrd', '( %s x. %s ) <_ ( 1 / %s )' % (EI, EK, QQ))
    ek2 = t([ek, t([ye], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (EI, YPT, EI, EK))], 'breqtrrd' if False else 'x', 'x') if False else None
    ek2 = t([t([ye], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (EI, YPT, EI, EK)), ek], 'eqbrtrd', '( %s x. %s ) <_ ( 1 / %s )' % (EI, YPT, QQ))
    # R2 = 60 ( EI YPT ) <_ 60 / QQ
    qq = t([clr], 'rpefcld' if False else 'reefcld', '%s e. RR' % QQ)
    qqp = t([clr], 'efgt0d' if False else 'x', 'x') if False else None
    qqrp = t([t([clr], 'rpefcld', '%s e. RR+' % QQ)], 'x', 'x') if False else t([clr], 'rpefcld', '%s e. RR+' % QQ)
    iq = t([qqrp], 'rprecred', '( 1 / %s ) e. RR' % QQ)
    eyr = t([eir, ypr_], 'remulcld', '( %s x. %s ) e. RR' % (EI, YPT))
    c60r = c_(w, a, num.real(w, c60), '%s e. RR' % c60)
    r60 = t([eyr, iq, c60r, c_(w, a, num.fact(w, c60, 'ge0'), '0 <_ %s' % c60), ek2], 'lemul2ad', '( %s x. ( %s x. %s ) ) <_ ( %s x. ( 1 / %s ) )' % (c60, EI, YPT, c60, QQ))
    ma = t([t([c60r], 'recnd', '%s e. CC' % c60), t([eir], 'recnd', '%s e. CC' % EI), t([ypr_], 'recnd', '%s e. CC' % YPT)], 'mulassd',
           '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (A1, YPT, c60, EI, YPT))
    m1r = t([t([t([a1r, ypr_], 'remulcld', '( %s x. %s ) e. RR' % (A1, YPT))], 'recnd', '( %s x. %s ) e. CC' % (A1, YPT))], 'mulridd', '%s = ( %s x. %s )' % (R2, A1, YPT))
    R3 = '( %s x. ( 1 / %s ) )' % (c60, QQ)
    r2b = t([t([m1r, ma], 'eqtrd', '%s = ( %s x. ( %s x. %s ) )' % (R2, c60, EI, YPT)), r60], 'eqbrtrd', '%s <_ %s' % (R2, R3))
    # D1 <_ 2 + log D
    rlm = t([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), drp, w.inst('relogmul')], 'syl2anc', '( log ` ( 2 x. D ) ) = ( ( log ` 2 ) + %s )' % Lg)
    l2 = c_(w, a, w.s([], 'log2le1', '( log ` 2 ) < 1'), '( log ` 2 ) < 1')
    l2r = c_(w, a, w.s([w.s([], '2rp', '2 e. RR+')], 'relogcli' if False else 'x', 'x'), 'x') if False else t([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')], 'relogcld', '( log ` 2 ) e. RR')
    Ly = dict(L); Ly['( log ` 2 )'] = l2r; Ly['( log ` ( 2 x. D ) )'] = lg2
    Z = '( 2 + %s )' % Lg
    dz = linarith(w, a, [rlm, l2], '%s <_ %s' % (D1, Z), leaves=Ly)
    zr = t([c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), lr], 'readdcld', '%s e. RR' % Z)
    r3r = t([c60r, iq], 'remulcld', '%s e. RR' % R3)
    r2ge = t([t([a1r, ypr_, t([c60r, eir, c_(w, a, num.fact(w, c60, 'ge0'), '0 <_ %s' % c60), t([t([ir], 'renegcld', '-u %s e. RR' % I)], 'efge0d' if False else 'x', 'x') if False else
                                  t([t([t([ir], 'renegcld', '-u %s e. RR' % I)], 'rpefcld', '%s e. RR+' % EI)], 'rpge0d', '0 <_ %s' % EI)], 'mulge0d', '0 <_ %s' % A1),
              t([ypr], 'rpge0d', '0 <_ %s' % YPT)], 'mulge0d', '0 <_ ( %s x. %s )' % (A1, YPT))], 'x', 'x') if False else None
    ge_a1 = t([c60r, eir, c_(w, a, num.fact(w, c60, 'ge0'), '0 <_ %s' % c60), t([t([t([ir], 'renegcld', '-u %s e. RR' % I)], 'rpefcld', '%s e. RR+' % EI)], 'rpge0d', '0 <_ %s' % EI)],
              'mulge0d', '0 <_ %s' % A1)
    ge_r2 = t([t([a1r, ypr_], 'remulcld', '( %s x. %s ) e. RR' % (A1, YPT)), c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'),
               t([a1r, ypr_, ge_a1, t([ypr], 'rpge0d', '0 <_ %s' % YPT)], 'mulge0d', '0 <_ ( %s x. %s )' % (A1, YPT)), c_(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1')],
              'mulge0d', '0 <_ %s' % R2)
    d10 = linarith(w, a, [rlm, l40], '0 <_ %s' % D1, leaves=dict(Ly, **{'( log ` ( 2 x. D ) )': lg2})) if False else None
    d10 = t([aM0, bM], 'x', 'x') if False else t([aMr, d1r, aM0, bM], 'letrd' if False else 'x', 'x') if False else None
    d10 = t([t([aMr, d1r, aM0, bM], 'x', 'x')], 'x', 'x') if False else None
    d10 = t([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), aMr, d1r, aM0, bM], 'letrd', '0 <_ %s' % D1)
    s4 = t([r2r, r3r, d1r, zr, ge_r2, d10, r2b, dz], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (R2, D1, R3, Z))
    # 60 ( 1 / QQ ) ( 2 + L ) <_ 1 / 8 from 960 L <_ QQ (dshnum)
    nm = t([t([lr, l40], 'jca', '( %s e. RR /\\ ; 4 0 <_ %s )' % (Lg, Lg)), w.inst('dshnum')], 'syl', '( ; ; 9 6 0 x. %s ) <_ %s' % (Lg, QQ))
    Lq = dict(L); Lq[QQ] = qq; Lq[Z] = zr
    h480 = linarith(w, a, [nm, l40], '( ; 6 0 x. %s ) <_ ( %s x. ( 1 / 8 ) )' % (Z, QQ), leaves={Lg: lr, QQ: qq})
    E8 = '( 1 / 8 )'
    e8r = c_(w, a, num.real(w, E8), '%s e. RR' % E8)
    c60z = '( %s x. %s )' % (c60, Z)
    dm = t([t([t([c60r, zr], 'remulcld', '%s e. RR' % c60z), e8r, t([qq, t([qqrp], 'rpgt0d', '0 < %s' % QQ)], 'jca', '( %s e. RR /\\ 0 < %s )' % (QQ, QQ))], '3jca',
              '( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 < %s ) )' % (c60z, E8, QQ, QQ)), w.inst('ledivmul')], 'syl',
           '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (c60z, QQ, E8, c60z, QQ, E8))
    fin0 = t([h480, dm], 'mpbird', '( %s / %s ) <_ %s' % (c60z, QQ, E8))
    # ( 60 x. ( 1 / QQ ) ) x. Z = ( 60 x. Z ) / QQ
    c60c = t([c60r], 'recnd', '%s e. CC' % c60); zc = t([zr], 'recnd', '%s e. CC' % Z); qqc = t([qq], 'recnd', '%s e. CC' % QQ); qq0 = t([qqrp], 'rpne0d', '%s =/= 0' % QQ)
    f1 = t([c60c, t([qqc, qq0], 'reccld', '( 1 / %s ) e. CC' % QQ), zc], 'mul32d', '( %s x. %s ) = ( ( %s x. %s ) x. ( 1 / %s ) )' % (R3, Z, c60, Z, QQ))
    f2 = t([t([c60c, zc], 'mulcld', '%s e. CC' % c60z), qqc, qq0], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (c60z, QQ, c60z, QQ))
    f3 = t([f1, f2], 'eqtr4d', '( %s x. %s ) = ( %s / %s )' % (R3, Z, c60z, QQ))
    fin = t([f3, fin0], 'eqbrtrd', '( %s x. %s ) <_ %s' % (R3, Z, E8))
    # assemble
    x1 = t([s3, s4], 'x', 'x') if False else None
    pvr = t([gxqr, aMr], 'remulcld', '%s e. RR' % PV)
    r2d1 = t([r2r, d1r], 'remulcld', '( %s x. %s ) e. RR' % (R2, D1))
    r3z = t([r3r, zr], 'remulcld', '( %s x. %s ) e. RR' % (R3, Z))
    y1_ = t([pvr, r2d1, r3z, s3, s4], 'letrd', '%s <_ ( %s x. %s )' % (PV, R3, Z))
    y2 = t([pvr, r3z, e8r, y1_, fin], 'letrd', '%s <_ %s' % (PV, E8))
    y3 = t([bv, y2], 'eqbrtrd', '( abs ` %s ) <_ %s' % (V, E8))
    y4 = t([t([ev], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (EPH(PRN), V)), y3], 'eqbrtrd', '( abs ` %s ) <_ %s' % (EPH(PRN), E8))
    toqed(w, y4, 'dshepb'); w.run()
