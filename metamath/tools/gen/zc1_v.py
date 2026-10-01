"""Sortie ZC1: the zero-spacing pigeonhole (gappt, Lean exists_gap_point)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
import cl as _cl
from c8_o import numst
import lin
lin.FASTPATH = True

NG = '( # ` G )'
K = '( %s + 1 )' % NG
D = '( 1 / ( 2 x. %s ) )' % K
J = '( T [,] ( T + 1 ) )'
GOAL = 'E. t e. %s A. g e. G %s <_ ( abs ` ( t - g ) )' % (J, D)
S['gappt'] = '( ( ( G e. Fin /\\ G C_ RR ) /\\ T e. RR ) -> %s )' % GOAL
Y = lambda g: '( ( ( %s - T ) x. %s ) + ( 1 / 2 ) )' % (g, K)
M = '( a e. G |-> ( |_ ` %s ) )' % Y('a')
I = '( 0 ... %s )' % NG


def gen_gappt():
    w = W('gappt', 'Zero-spacing pigeonhole (Lean ` exists_gap_point ` ): for a finite set ` G ` of reals there is ` t e. [ T , T + 1 ] ` at distance at least ` 1 / ( 2 ( # G + 1 ) ) ` from every member: the ` # G + 1 ` points ` T + i / ( # G + 1 ) ` cannot all be hit by the rounding map ` g |-> floor ( ( g - T ) ( # G + 1 ) + 1 / 2 ) ` .')
    A0 = ante_of(S['gappt'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    gf = s([], 'simpll', 'G e. Fin'); gr = s([], 'simplr', 'G C_ RR'); tr = s([], 'simpr', 'T e. RR')
    n0 = s([gf, w.inst('hashcl')], 'syl', '%s e. NN0' % NG)
    kn = s([n0, w.inst('nn0p1nn')], 'syl', '%s e. NN' % K)
    kr = s([kn], 'nnred', '%s e. RR' % K); kp = s([kn], 'nnrpd', '%s e. RR+' % K); kc = s([kn], 'nncnd', '%s e. CC' % K); kne = s([kn], 'nnne0d', '%s =/= 0' % K)
    nr = s([n0], 'nn0red', '%s e. RR' % NG)
    # M Fn G, ran M finite, # ran M <_ # G
    Aa = '( %s /\\ a e. G )' % A0
    ar_ = w.s([lift(w, gr, Aa), w.s([], 'simpr', '( %s -> a e. G )' % Aa)], 'sseldd', '( %s -> a e. RR )' % Aa)
    fl_ex = w.s([w.s([], 'fvex', '( |_ ` %s ) e. _V' % Y('a'))], 'a1i', '( %s -> ( |_ ` %s ) e. _V )' % (Aa, Y('a')))
    alv = s([fl_ex], 'ralrimiva', 'A. a e. G ( |_ ` %s ) e. _V' % Y('a'))
    mfn = s([alv, w.s([w.s([], 'eqid', '%s = %s' % (M, M))], 'fnmpt', '( A. a e. G ( |_ ` %s ) e. _V -> %s Fn G )' % (Y('a'), M))], 'syl', '%s Fn G' % M)
    mfo = s([mfn, w.s([], 'dffn4', '( %s Fn G <-> %s : G -onto-> ran %s )' % (M, M, M))], 'sylib', '%s : G -onto-> ran %s' % (M, M))
    dom = s([gf, mfo], 'fodomfi' if False else 'x', 'x') if False else s([s([gf, mfo], 'jca', '( G e. Fin /\\ %s : G -onto-> ran %s )' % (M, M)), w.inst('fodomfi')], 'syl', 'ran %s ~<_ G' % M)
    rfin = s([s([gf, dom], 'jca', '( G e. Fin /\\ ran %s ~<_ G )' % M), w.inst('domfi')], 'syl', 'ran %s e. Fin' % M)
    HR = '( # ` ran %s )' % M
    hle = s([dom, s([s([rfin, gf], 'jca', '( ran %s e. Fin /\\ G e. Fin )' % M), w.inst('hashdom')], 'syl', '( %s <_ %s <-> ran %s ~<_ G )' % (HR, NG, M))], 'mpbird', '%s <_ %s' % (HR, NG))
    # I is not inside ran M
    hi = s([n0, w.inst('hashfz0')], 'syl', '( # ` %s ) = %s' % (I, K))
    Ass = '( %s /\\ %s C_ ran %s )' % (A0, I, M)
    hs = w.s([w.s([lift(w, rfin, Ass), w.s([], 'simpr', '( %s -> %s C_ ran %s )' % (Ass, I, M))], 'jca', '( %s -> ( ran %s e. Fin /\\ %s C_ ran %s ) )' % (Ass, M, I, M)), w.inst('hashss')], 'syl',
             '( %s -> ( # ` %s ) <_ %s )' % (Ass, I, HR))
    hrr = s([s([rfin, w.inst('hashcl')], 'syl', '%s e. NN0' % HR)], 'nn0red', '%s e. RR' % HR)
    hir = s([s([s([], 'fzfid', '%s e. Fin' % I), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % I)], 'nn0red', '( # ` %s ) e. RR' % I)
    lvh = {HR: lift(w, hrr, Ass), '( # ` %s )' % I: lift(w, hir, Ass), NG: lift(w, nr, Ass)}
    cont = lin8(w, Ass, [hs, lift(w, hle, Ass), lift(w, hi, Ass)], '%s < %s' % (NG, NG), lvh)
    ncont = w.s([lift(w, nr, Ass), w.inst('ltnrd') if False else None], 'x', 'x') if False else w.s([lift(w, nr, Ass)], 'ltnrd', '( %s -> -. %s < %s )' % (Ass, NG, NG))
    nss_ = w.s([cont, ncont], 'pm2.65da', '( %s -> -. %s C_ ran %s )' % (A0, I, M))
    exi = s([nss_, w.s([], 'nss', '( -. %s C_ ran %s <-> E. i ( i e. %s /\\ -. i e. ran %s ) )' % (I, M, I, M))], 'sylib', 'E. i ( i e. %s /\\ -. i e. ran %s )' % (I, M))
    # given such an i
    IN = '( i e. %s /\\ -. i e. ran %s )' % (I, M)
    Ai = '( %s /\\ %s )' % (A0, IN)
    si = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    Li = lambda st: lift(w, st, Ai)
    ii = si([], 'simprl', 'i e. %s' % I); nir = si([], 'simprr', '-. i e. ran %s' % M)
    iz = si([ii, w.inst('elfzelz')], 'syl', 'i e. ZZ'); ir = si([iz], 'zred', 'i e. RR')
    i0 = si([ii, w.inst('elfzle1')], 'syl', '0 <_ i'); iln = si([ii, w.inst('elfzle2')], 'syl', 'i <_ %s' % NG)
    IK = '( i / %s )' % K
    ikr = si([ir, Li(kp)], 'rerpdivcld', '%s e. RR' % IK)
    T0 = '( T + %s )' % IK
    t0r = si([Li(tr), ikr], 'readdcld', '%s e. RR' % T0)
    ik0 = si([ir, Li(kp), i0], 'divge0d', '0 <_ %s' % IK)
    ik1 = si([si([lin8(w, Ai, [iln], 'i <_ ( %s x. 1 )' % K, {'i': ir, NG: Li(nr)}), si([ir, si([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), Li(kp)], 'ledivmuld',
                                                                                          '( %s <_ 1 <-> i <_ ( %s x. 1 ) )' % (IK, K))], 'mpbird', '%s <_ 1' % IK)], 'x', 'x') if False else \
        si([lin8(w, Ai, [iln], 'i <_ ( %s x. 1 )' % K, {'i': ir, NG: Li(nr)}), si([ir, si([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), Li(kp)], 'ledivmuld', '( %s <_ 1 <-> i <_ ( %s x. 1 ) )' % (IK, K))],
           'mpbird', '%s <_ 1' % IK)
    lvt = {'T': Li(tr), IK: ikr}
    tj = si([si([Li(tr), si([Li(tr), si([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'readdcld', '( T + 1 ) e. RR'), w.inst('elicc2')], 'syl2anc',
                '( %s e. %s <-> ( %s e. RR /\\ T <_ %s /\\ %s <_ ( T + 1 ) ) )' % (T0, J, T0, T0, T0)),
             ], 'x', 'x') if False else None
    ej = si([Li(tr), si([Li(tr), si([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'readdcld', '( T + 1 ) e. RR'), w.inst('elicc2')], 'syl2anc',
            '( %s e. %s <-> ( %s e. RR /\\ T <_ %s /\\ %s <_ ( T + 1 ) ) )' % (T0, J, T0, T0, T0))
    tj = si([si([t0r, lin8(w, Ai, [ik0], 'T <_ %s' % T0, lvt), lin8(w, Ai, [ik1], '%s <_ ( T + 1 )' % T0, lvt)], '3jca', '( %s e. RR /\\ T <_ %s /\\ %s <_ ( T + 1 ) )' % (T0, T0, T0)), ej],
            'mpbird', '%s e. %s' % (T0, J))
    # for g e. G
    Ag = '( %s /\\ g e. G )' % Ai
    sg = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ag, f))
    Lg = lambda st: lift(w, st, Ag)
    gG = sg([], 'simpr', 'g e. G')
    grr = sg([Lg(Li(gr)), gG], 'sseldd', 'g e. RR')
    YG = Y('g')
    YM = '( ( g - T ) x. %s )' % K
    ymr = sg([sg([grr, Lg(Li(tr))], 'resubcld', '( g - T ) e. RR'), Lg(Li(kr))], 'remulcld', '%s e. RR' % YM)
    ygr = sg([ymr, numst(w, Ag, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % YG)
    mv, _ = _cg.mptval(w, Ag, 'a', 'G', '( |_ ` %s )' % Y('a'), 'g', gG, exs=sg([w.s([], 'fvex', '( |_ ` %s ) e. _V' % YG)], 'a1i', '( |_ ` %s ) e. _V' % YG), gen=w.g)
    mr = sg([Lg(Li(mfn)), gG], 'fnfvelrn' if False else 'x', 'x') if False else sg([sg([Lg(Li(mfn)), gG], 'jca', '( %s Fn G /\\ g e. G )' % M), w.inst('fnfvelrn')], 'syl', '( %s ` g ) e. ran %s' % (M, M))
    # floor ( YG ) =/= i
    Aeq = '( %s /\\ ( |_ ` %s ) = i )' % (Ag, YG)
    inr = w.s([w.s([w.s([lift(w, mv, Aeq), w.s([], 'simpr', '( %s -> ( |_ ` %s ) = i )' % (Aeq, YG))], 'eqtrd', '( %s -> ( %s ` g ) = i )' % (Aeq, M)), lift(w, mr, Aeq)], 'x', 'x') if False else
               w.s([w.s([lift(w, mv, Aeq), w.s([], 'simpr', '( %s -> ( |_ ` %s ) = i )' % (Aeq, YG))], 'eqtrd', '( %s -> ( %s ` g ) = i )' % (Aeq, M)), lift(w, mr, Aeq)], 'eqeltrrd', '( %s -> i e. ran %s )' % (Aeq, M))],
              'x', 'x') if False else w.s([w.s([lift(w, mv, Aeq), w.s([], 'simpr', '( %s -> ( |_ ` %s ) = i )' % (Aeq, YG))], 'eqtrd', '( %s -> ( %s ` g ) = i )' % (Aeq, M)), lift(w, mr, Aeq)], 'eqeltrrd',
                                         '( %s -> i e. ran %s )' % (Aeq, M))
    nfl = w.s([inr, lift(w, Lg(nir), Aeq)], 'pm2.65da', '( %s -> -. ( |_ ` %s ) = i )' % (Ag, YG))
    fb = sg([sg([ygr, Lg(iz)], 'jca', '( %s e. RR /\\ i e. ZZ )' % YG), w.inst('flbi')], 'syl', '( ( |_ ` %s ) = i <-> ( i <_ %s /\\ %s < ( i + 1 ) ) )' % (YG, YG, YG))
    nboth = sg([nfl, fb], 'mtbid' if False else 'x', 'x') if False else sg([nfl, fb], 'mtbid', '-. ( i <_ %s /\\ %s < ( i + 1 ) )' % (YG, YG))
    # 1 / 2 <_ abs ( i - YM )
    DI = '( i - %s )' % YM
    dir_ = sg([Lg(Li(ir)), ymr], 'resubcld', '%s e. RR' % DI)
    adi = sg([sg([dir_], 'recnd', '%s e. CC' % DI)], 'abscld', '( abs ` %s ) e. RR' % DI)
    lvd = {'i': Lg(Li(ir)), YM: ymr, '( abs ` %s )' % DI: adi}
    Ac1 = '( %s /\\ i <_ %s )' % (Ag, YG)
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ac1, f))
    ny = w.s([w.s([w.s([], 'simpr', '( %s -> i <_ %s )' % (Ac1, YG)), lift(w, nboth, Ac1)], 'x', 'x') if False else None], 'x', 'x') if False else None
    nlt = s1([s1([], 'simpr', 'i <_ %s' % YG), lift(w, nboth, Ac1)], 'x', 'x') if False else None
    # -. ( i <_ YG /\ YG < i + 1 ) with i <_ YG gives -. YG < i + 1
    imp = sg([nboth], 'x', 'x') if False else None
    ab = sg([nboth, w.s([], 'imnan', '( ( i <_ %s -> -. %s < ( i + 1 ) ) <-> -. ( i <_ %s /\\ %s < ( i + 1 ) ) )' % (YG, YG, YG, YG))], 'sylibr', '( i <_ %s -> -. %s < ( i + 1 ) )' % (YG, YG))
    ng1 = s1([s1([], 'simpr', 'i <_ %s' % YG), lift(w, ab, Ac1)], 'mpd', '-. %s < ( i + 1 )' % YG)
    i1r = s1([lift(w, Lg(Li(ir)), Ac1), s1([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'readdcld', '( i + 1 ) e. RR')
    ge1 = s1([ng1, s1([i1r, lift(w, ygr, Ac1)], 'lenltd', '( ( i + 1 ) <_ %s <-> -. %s < ( i + 1 ) )' % (YG, YG))], 'mpbird', '( i + 1 ) <_ %s' % YG)
    lvd1 = {k_: lift(w, v_, Ac1) for k_, v_ in lvd.items()}
    c1 = s1([lin8(w, Ac1, [ge1], '( 1 / 2 ) <_ -u %s' % DI, lvd1), s1([s1([lift(w, dir_, Ac1)], 'renegcld', '-u %s e. RR' % DI)], 'leabsd', '-u %s <_ ( abs ` -u %s )' % (DI, DI)),
              s1([s1([lift(w, dir_, Ac1)], 'recnd', '%s e. CC' % DI)], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (DI, DI))], 'x', 'x') if False else None
    nd = s1([s1([lift(w, dir_, Ac1)], 'renegcld', '-u %s e. RR' % DI)], 'leabsd', '-u %s <_ ( abs ` -u %s )' % (DI, DI))
    an = s1([s1([lift(w, dir_, Ac1)], 'recnd', '%s e. CC' % DI)], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (DI, DI))
    ndl = s1([nd, an], 'breqtrd', '-u %s <_ ( abs ` %s )' % (DI, DI))
    lvd1['-u %s' % DI] = s1([lift(w, dir_, Ac1)], 'renegcld', '-u %s e. RR' % DI)
    case1 = lin8(w, Ac1, [ge1, ndl], '( 1 / 2 ) <_ ( abs ` %s )' % DI, {'i': lift(w, Lg(Li(ir)), Ac1), YM: lift(w, ymr, Ac1), '( abs ` %s )' % DI: lift(w, adi, Ac1)})
    Ac2 = '( %s /\\ -. i <_ %s )' % (Ag, YG)
    s2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ac2, f))
    lt2 = s2([s2([], 'simpr', '-. i <_ %s' % YG), s2([lift(w, ygr, Ac2), lift(w, Lg(Li(ir)), Ac2)], 'ltnled', '( %s < i <-> -. i <_ %s )' % (YG, YG))], 'mpbird', '%s < i' % YG)
    dl = s2([lift(w, dir_, Ac2)], 'leabsd', '%s <_ ( abs ` %s )' % (DI, DI))
    case2 = lin8(w, Ac2, [lt2, dl], '( 1 / 2 ) <_ ( abs ` %s )' % DI, {'i': lift(w, Lg(Li(ir)), Ac2), YM: lift(w, ymr, Ac2), '( abs ` %s )' % DI: lift(w, adi, Ac2)})
    half = sg([case1, case2, sg([Lg(Li(ir)), ygr], 'x', 'x') if False else sg([w.s([], 'exmid', '( i <_ %s \\/ -. i <_ %s )' % (YG, YG))], 'a1i', '( i <_ %s \\/ -. i <_ %s )' % (YG, YG))], 'mpjaodan',
              '( 1 / 2 ) <_ ( abs ` %s )' % DI)
    # abs ( T0 - g ) = abs ( DI ) / K
    TG = '( %s - g )' % T0
    gc = sg([grr], 'recnd', 'g e. CC'); tc = sg([Lg(Li(tr))], 'recnd', 'T e. CC')
    dk = sg([sg([Lg(Li(ir)), w.s([], 'x', 'x') if False else None], 'x', 'x') if False else sg([Lg(Li(ir))], 'recnd', 'i e. CC'), sg([ymr], 'recnd', '%s e. CC' % YM), Lg(Li(kc)), Lg(Li(kne))], 'divsubdird',
            '( %s / %s ) = ( ( i / %s ) - ( %s / %s ) )' % (DI, K, K, YM, K))
    yk = sg([sg([gc, tc], 'subcld', '( g - T ) e. CC'), Lg(Li(kc)), Lg(Li(kne))], 'divcan4d', '( %s / %s ) = ( g - T )' % (YM, K))
    DK = '( %s / %s )' % (DI, K)
    dkr = sg([dir_, Lg(Li(kp))], 'rerpdivcld', '%s e. RR' % DK)
    lvt2 = {'T': Lg(Li(tr)), 'g': grr, IK: Lg(ikr), DK: dkr, '( %s / %s )' % (YM, K): sg([ymr, Lg(Li(kp))], 'rerpdivcld', '( %s / %s ) e. RR' % (YM, K))}
    tgk = lin.lineq(w, Ag, TG, DK, closure=None) if False else None
    c_ = _cl.Closure(w, Ag, lvt2)
    for k_ in lvt2:
        c_.atom(k_)
    e1 = lin.linarith(w, Ag, [dk, yk], '%s <_ %s' % (TG, DK), closure=c_)
    e2 = lin.linarith(w, Ag, [dk, yk], '%s <_ %s' % (DK, TG), closure=c_)
    tgr = c_.mem(TG, 'RR')
    teq = sg([tgr, dkr, e1, e2], 'letri3d' if False else 'x', 'x') if False else sg([sg([tgr, dkr], 'letri3d', '( %s = %s <-> ( %s <_ %s /\\ %s <_ %s ) )' % (TG, DK, TG, DK, DK, TG)), sg([e1, e2], 'jca', '( %s <_ %s /\\ %s <_ %s )' % (TG, DK, DK, TG))],
                                                                                 'mpbird', '%s = %s' % (TG, DK))
    ak = sg([sg([dir_], 'recnd', '%s e. CC' % DI), Lg(Li(kc)), Lg(Li(kne))], 'absdivd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (DK, DI, K))
    akk = sg([Lg(Li(kr)), sg([Lg(Li(kp))], 'rpge0d', '0 <_ %s' % K)], 'absidd', '( abs ` %s ) = %s' % (K, K))
    atg = sg([sg([sg([teq], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (TG, DK)), ak], 'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (TG, DI, K)),
              sg([akk], 'oveq2d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / %s )' % (DI, K, DI, K))], 'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) / %s )' % (TG, DI, K))
    hl = sg([half, sg([numst(w, Ag, '( 1 / 2 )', 'RR'), adi, Lg(Li(kp))], 'lediv1d', '( ( 1 / 2 ) <_ ( abs ` %s ) <-> ( ( 1 / 2 ) / %s ) <_ ( ( abs ` %s ) / %s ) )' % (DI, K, DI, K))],
            'mpbid', '( ( 1 / 2 ) / %s ) <_ ( ( abs ` %s ) / %s )' % (K, DI, K))
    dd = sg([sg([], '1cnd', '1 e. CC'), sg([sg([], '2cnd', '2 e. CC'), sg([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')], 'jca', '( 2 e. CC /\\ 2 =/= 0 )'),
             sg([Lg(Li(kc)), Lg(Li(kne))], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (K, K))], 'x', 'x') if False else None
    dd = sg([sg([sg([], '1cnd', '1 e. CC'), sg([sg([], '2cnd', '2 e. CC'), sg([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')], 'jca', '( 2 e. CC /\\ 2 =/= 0 )'),
                 sg([Lg(Li(kc)), Lg(Li(kne))], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (K, K))], '3jca', '( 1 e. CC /\\ ( 2 e. CC /\\ 2 =/= 0 ) /\\ ( %s e. CC /\\ %s =/= 0 ) )' % (K, K)), w.inst('divdiv1')],
            'syl', '( ( 1 / 2 ) / %s ) = %s' % (K, D))
    fin_g = sg([sg([dd], 'eqcomd', '%s = ( ( 1 / 2 ) / %s )' % (D, K)), sg([hl, sg([atg], 'eqcomd', '( ( abs ` %s ) / %s ) = ( abs ` %s )' % (DI, K, TG))], 'breqtrd', '( ( 1 / 2 ) / %s ) <_ ( abs ` %s )' % (K, TG))],
               'eqbrtrd', '%s <_ ( abs ` %s )' % (D, TG))
    alg = si([fin_g], 'ralrimiva', 'A. g e. G %s <_ ( abs ` %s )' % (D, TG))
    BT = 'A. g e. G %s <_ ( abs ` ( t - g ) )' % D
    eqt = w.s([w.s([w.s([w.s([], 'oveq1', '( t = %s -> ( t - g ) = %s )' % (T0, TG))], 'fveq2d', '( t = %s -> ( abs ` ( t - g ) ) = ( abs ` %s ) )' % (T0, TG))], 'breq2d',
                    '( t = %s -> ( %s <_ ( abs ` ( t - g ) ) <-> %s <_ ( abs ` %s ) ) )' % (T0, D, D, TG))], 'ralbidv', '( t = %s -> ( %s <-> A. g e. G %s <_ ( abs ` %s ) ) )' % (T0, BT, D, TG))
    goal_i = si([tj, alg, w.s([eqt], 'rspcev', '( ( %s e. %s /\\ A. g e. G %s <_ ( abs ` %s ) ) -> %s )' % (T0, J, D, TG, GOAL))], 'syl2anc', GOAL)
    el = s([w.s([goal_i], 'ex', '( %s -> ( %s -> %s ) )' % (A0, IN, GOAL))], 'exlimdv', '( E. i %s -> %s )' % (IN, GOAL))
    w.qed([exi, el], 'mpd', S['gappt'])
    return run8(w)


if __name__ == '__main__':
    gen_gappt()
