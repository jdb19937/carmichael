"""Sortie Z5a, section B: the pseudocharacter sum P (Detector.lean 281-392)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5alib import *
from cl import Closure, lift
import lin

HNR = '( N e. V /\\ R e. W )'


def z5phile():
    w = W('z5phile', "Euler's totient is at most its argument: ( phi ` N ) <_ N (the step phi ( g ) <_ g of Lean abs_psi_le, Nat.totient_le).")
    ante = 'N e. NN'
    st = mkst(w, ante)
    S = '{ x e. ( 1 ... N ) | ( x gcd N ) = 1 }'
    pv = sy(w, ante, st([], 'id', 'N e. NN'), 'phival', '( phi ` N ) = ( # ` %s )' % S)
    ss = a1(w, ante, w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % S), '%s C_ ( 1 ... N )' % S)
    hs = sy2(w, ante, st([], 'fzfid', '( 1 ... N ) e. Fin'), ss, 'hashssle', '( # ` %s ) <_ ( # ` ( 1 ... N ) )' % S)
    hf = sy(w, ante, st([st([], 'id', 'N e. NN')], 'nnnn0d', 'N e. NN0'), 'hashfz1', '( # ` ( 1 ... N ) ) = N')
    w.qed([pv, st([hs, hf], 'breqtrd', '( # ` %s ) <_ N' % S)], 'eqbrtrd', STATEMENTS['z5phile'])
    return w


def z5rsetval():
    w = W('z5rsetval', "Value of the pseudocharacter index set: ( N RSet R ) is the set of squarefree k in ( 1 ... ( |_ ` R ) ) "
                       "coprime to N (Lean Rset, Detector.lean 357).")
    ante = HNR
    e1 = cg(w, RSB('m', 'y'), 'm', 'N')
    e2 = cg(w, RSB('N', 'y'), 'y', 'R')
    df = w.s([], 'df-rset', 'RSet = ( m e. _V , y e. _V |-> %s )' % RSB('m', 'y'))
    ex = w.s([w.s([], 'ovex', '( 1 ... ( |_ ` R ) ) e. _V')], 'rabex', '%s e. _V' % RSB('N', 'R'))
    ov = w.s([e1, e2, df, ex], 'ovmpo', '( ( N e. _V /\\ R e. _V ) -> ( N RSet R ) = %s )' % RSB('N', 'R'))
    both = w.s([w.s([], 'elex', '( N e. V -> N e. _V )'), w.s([], 'elex', '( R e. W -> R e. _V )')], 'anim12i', '( %s -> ( N e. _V /\\ R e. _V ) )' % ante)
    w.qed([both, ov], 'syl', '( %s -> ( N RSet R ) = %s )' % (ante, RSB('N', 'R')))
    return w


def z5elrset():
    w = W('z5elrset', "Lean mem_Rset: r e. ( N RSet R ) iff r e. ( 1 ... ( |_ ` R ) ), r is squarefree and coprime to N.")
    ante = HNR
    st = mkst(w, ante)
    rv = st([st([], 'id', HNR), w.inst('z5rsetval')], 'syl', '( N RSet R ) = %s' % RSB('N', 'R'))
    e1 = st([rv], 'eleq2d', '( K e. ( N RSet R ) <-> K e. %s )' % RSB('N', 'R'))
    PH = '( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 )'
    idk = w.s([], 'id', '( k = K -> k = K )')
    c, new = w.wcongr(PH, {'k': 'K'}, 'k = K', {'k': idk})
    er = w.s([c], 'elrab', '( K e. %s <-> ( K e. ( 1 ... ( |_ ` R ) ) /\\ %s ) )' % (RSB('N', 'R'), new))
    w.qed([e1, a1(w, ante, er, '( K e. %s <-> ( K e. ( 1 ... ( |_ ` R ) ) /\\ %s ) )' % (RSB('N', 'R'), new))], 'bitrd', STATEMENTS['z5elrset'])
    return w


def z5rsetfi():
    w = W('z5rsetfi', "The pseudocharacter index set is a finite subset of ( 1 ... ( |_ ` R ) ) (Lean Rset is a Finset).")
    ante = HNR
    st = mkst(w, ante)
    rv = st([st([], 'id', HNR), w.inst('z5rsetval')], 'syl', '( N RSet R ) = %s' % RSB('N', 'R'))
    ss = st([rv, a1(w, ante, w.s([], 'ssrab2', '%s C_ ( 1 ... ( |_ ` R ) )' % RSB('N', 'R')), '%s C_ ( 1 ... ( |_ ` R ) )' % RSB('N', 'R'))], 'eqsstrd',
            '( N RSet R ) C_ ( 1 ... ( |_ ` R ) )')
    fi = sy2(w, ante, st([], 'fzfid', '( 1 ... ( |_ ` R ) ) e. Fin'), ss, 'ssfi', '( N RSet R ) e. Fin')
    w.qed([ss, fi], 'jca', STATEMENTS['z5rsetfi'])
    return w


def z5rsetcard():
    w = W('z5rsetcard', "Lean card_Rset_le: the pseudocharacter index set has at most |_ R elements (0 <_ R).")
    ante = '( N e. V /\\ ( R e. RR /\\ 0 <_ R ) )'
    st = mkst(w, ante)
    nv = st([], 'simpl', 'N e. V'); rr = st([], 'simprl', 'R e. RR'); r0 = st([], 'simprr', '0 <_ R')
    fs = st([nv, rr, w.inst('z5rsetfi')], 'syl2anc', '( ( N RSet R ) C_ ( 1 ... ( |_ ` R ) ) /\\ ( N RSet R ) e. Fin )')
    ss = st([fs], 'simpld', '( N RSet R ) C_ ( 1 ... ( |_ ` R ) )')
    hs = sy2(w, ante, st([], 'fzfid', '( 1 ... ( |_ ` R ) ) e. Fin'), ss, 'hashssle', '( # ` ( N RSet R ) ) <_ ( # ` ( 1 ... ( |_ ` R ) ) )')
    fl = sy2(w, ante, rr, r0, 'flge0nn0', '( |_ ` R ) e. NN0')
    hf = sy(w, ante, fl, 'hashfz1', '( # ` ( 1 ... ( |_ ` R ) ) ) = ( |_ ` R )')
    w.qed([hs, hf], 'breqtrd', STATEMENTS['z5rsetcard'])
    return w


PFB = lambda m, y: '( n e. NN |-> sum_ r e. ( %s RSet %s ) ( %s / r ) )' % (m, y, PSI('r', 'n'))


def z5pfunval():
    w = W('z5pfunval', "Value of the pseudocharacter sum (Lean Pfun, Detector.lean 361): ( ( N PFun R ) ` K ) = sum_ r e. ( N RSet R ) psi_r ( K ) / r "
                       "with psi_r ( K ) = mmu ( ( r , K ) ) phi ( ( r , K ) ).")
    ante = '( %s /\\ K e. NN )' % HNR
    st = mkst(w, ante)
    e1 = cg(w, PFB('m', 'y'), 'm', 'N')
    e2 = cg(w, PFB('N', 'y'), 'y', 'R')
    df = w.s([], 'df-pfun', 'PFun = ( m e. _V , y e. _V |-> %s )' % PFB('m', 'y'))
    ex = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % PFB('N', 'R'))
    ov = w.s([e1, e2, df, ex], 'ovmpo', '( ( N e. _V /\\ R e. _V ) -> ( N PFun R ) = %s )' % PFB('N', 'R'))
    both = st([st([st([], 'simpll', 'N e. V')], 'elexd', 'N e. _V'), st([st([], 'simplr', 'R e. W')], 'elexd', 'R e. _V')], 'jca', '( N e. _V /\\ R e. _V )')
    pv = st([both, ov], 'syl', '( N PFun R ) = %s' % PFB('N', 'R'))
    body = 'sum_ r e. ( N RSet R ) ( %s / r )' % PSI('r', 'n')
    val, v = mpv(w, ante, 'n', 'NN', body, 'K', st([], 'simpr', 'K e. NN'),
                 exs=a1(w, ante, w.s([], 'sumex', '%s e. _V' % PFV('N', 'R', 'K')), '%s e. _V' % PFV('N', 'R', 'K')))
    w.qed([st([pv], 'fveq1d', '( ( N PFun R ) ` K ) = ( %s ` K )' % PFB('N', 'R')), val], 'eqtrd', STATEMENTS['z5pfunval'])
    return w


def psifacts(w, a, rnn, knn, r, K):
    st = mkst(w, a)
    g = '( %s gcd %s )' % (r, K)
    gnn = sy2(w, a, rnn, knn, 'gcdnncl', '%s e. NN' % g)
    muz = sy(w, a, gnn, 'mucl', '( mmu ` %s ) e. ZZ' % g)
    phn = sy(w, a, gnn, 'phicl', '( phi ` %s ) e. NN' % g)
    psr = st([st([muz], 'zred', '( mmu ` %s ) e. RR' % g), st([phn], 'nnred', '( phi ` %s ) e. RR' % g)], 'remulcld', '%s e. RR' % PSI(r, K))
    return dict(g=g, gnn=gnn, muz=muz, phn=phn, psr=psr)


def z5psiabs():
    w = W('z5psiabs', "Lean abs_psi_le: | psi_R ( K ) | <_ R, psi_R ( K ) = mmu ( ( R , K ) ) phi ( ( R , K ) ) (| mmu | <_ 1, phi ( g ) <_ g <_ R).")
    ante = '( R e. NN /\\ K e. NN )'
    st = mkst(w, ante)
    rnn = st([], 'simpl', 'R e. NN'); knn = st([], 'simpr', 'K e. NN')
    f = psifacts(w, ante, rnn, knn, 'R', 'K'); g = f['g']
    MU = '( mmu ` %s )' % g; PH = '( phi ` %s )' % g; AM = '( abs ` %s )' % MU
    muc = st([f['muz']], 'zcnd', '%s e. CC' % MU); phr = st([f['phn']], 'nnred', '%s e. RR' % PH)
    ph0 = st([phr, st([st([f['phn']], 'nngt0d', '0 < %s' % PH)], 'ltled', '0 <_ %s' % PH)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (PH, PH))
    ph0 = st([ph0], 'simprd', '0 <_ %s' % PH)
    ab = st([muc, st([phr], 'recnd', '%s e. CC' % PH)], 'absmuld', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (PSI('R', 'K'), AM, PH))
    ab2 = st([ab, st([st([phr, ph0], 'absidd', '( abs ` %s ) = %s' % (PH, PH))], 'oveq2d', '( %s x. ( abs ` %s ) ) = ( %s x. %s )' % (AM, PH, AM, PH))], 'eqtrd',
             '( abs ` %s ) = ( %s x. %s )' % (PSI('R', 'K'), AM, PH))
    am1 = sy(w, ante, f['gnn'], 'mule1', '%s <_ 1' % AM)
    am0 = st([muc], 'absge0d', '0 <_ %s' % AM)
    phg = sy(w, ante, f['gnn'], 'z5phile', '%s <_ %s' % (PH, g))
    gd = st([st([rnn], 'nnzd', 'R e. ZZ'), st([knn], 'nnzd', 'K e. ZZ'), w.inst('gcddvds')], 'syl2anc', '( %s || R /\\ %s || K )' % (g, g))
    gle = st([st([gd], 'simpld', '%s || R' % g), st([st([f['gnn']], 'nnzd', '%s e. ZZ' % g), rnn, w.inst('dvdsle')], 'syl2anc', '( %s || R -> %s <_ R )' % (g, g))], 'mpd',
             '%s <_ R' % g)
    lv = {AM: st([muc], 'abscld', '%s e. RR' % AM), PH: phr, g: st([f['gnn']], 'nnred', '%s e. RR' % g), 'R': st([rnn], 'nnred', 'R e. RR')}
    le = lin.nlinarith(w, ante, [am1, am0, ph0, phg, gle], '( %s x. %s ) <_ R' % (AM, PH), leaves=lv)
    w.qed([ab2, le], 'eqbrtrd', STATEMENTS['z5psiabs'])
    return w


def rmem(w, a, nv, rw, S='( N RSet R )'):
    """under a = ( ... /\\ r e. ( N RSet R ) ): r e. NN (nv: ( a -> N e. V ), rw: ( a -> R e. W ))"""
    st = mkst(w, a)
    el = st([nv, rw, w.inst('z5elrset')], 'syl2anc', '( r e. %s <-> ( r e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) ) )' % S)
    m = st([st([], 'simpr', 'r e. %s' % S), el], 'mpbid', '( r e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) )')
    return sy(w, a, st([m], 'simpld', 'r e. ( 1 ... ( |_ ` R ) )'), 'elfznn', 'r e. NN')


def z5pfunre():
    w = W('z5pfunre', "The pseudocharacter sum is real (Lean Pfun : RR).")
    ante = '( %s /\\ K e. NN )' % HNR
    st = mkst(w, ante)
    nv = st([], 'simpll', 'N e. V'); rw = st([], 'simplr', 'R e. W'); knn = st([], 'simpr', 'K e. NN')
    pv = st([nv, rw, knn, w.inst('z5pfunval')], 'syl21anc', '( ( N PFun R ) ` K ) = %s' % PFV('N', 'R', 'K'))
    fin = st([st([nv, rw, w.inst('z5rsetfi')], 'syl2anc', '( ( N RSet R ) C_ ( 1 ... ( |_ ` R ) ) /\\ ( N RSet R ) e. Fin )')], 'simprd', '( N RSet R ) e. Fin')
    a = '( %s /\\ r e. ( N RSet R ) )' % ante
    sa = mkst(w, a)
    rnn = rmem(w, a, lift(w, nv, a), lift(w, rw, a))
    f = psifacts(w, a, rnn, lift(w, knn, a), 'r', 'K')
    tr = sa([f['psr'], sa([rnn], 'nnrpd', 'r e. RR+')], 'rerpdivcld', '( %s / r ) e. RR' % PSI('r', 'K'))
    w.qed([pv, st([fin, tr], 'fsumrecl', '%s e. RR' % PFV('N', 'R', 'K'))], 'eqeltrd', STATEMENTS['z5pfunre'])
    return w


def z5pfunabs():
    w = W('z5pfunabs', "Lean abs_Pfun_le: | P ( K ) | <_ |_ R for 0 <_ R (each term | psi_r ( K ) / r | <_ 1, at most |_ R terms).")
    ante = '( ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) /\\ K e. NN )'
    st = mkst(w, ante)
    nv = st([], 'simpll', 'N e. V'); rr = st([], 'simplr', '( R e. RR /\\ 0 <_ R )')
    r0 = st([rr], 'simprd', '0 <_ R'); rr = st([rr], 'simpld', 'R e. RR'); knn = st([], 'simpr', 'K e. NN')
    pv = st([nv, rr, knn, w.inst('z5pfunval')], 'syl21anc', '( ( N PFun R ) ` K ) = %s' % PFV('N', 'R', 'K'))
    fin = st([st([nv, rr, w.inst('z5rsetfi')], 'syl2anc', '( ( N RSet R ) C_ ( 1 ... ( |_ ` R ) ) /\\ ( N RSet R ) e. Fin )')], 'simprd', '( N RSet R ) e. Fin')
    a = '( %s /\\ r e. ( N RSet R ) )' % ante
    sa = mkst(w, a)
    rnn = rmem(w, a, lift(w, nv, a), lift(w, rr, a))
    f = psifacts(w, a, rnn, lift(w, knn, a), 'r', 'K')
    T = '( %s / r )' % PSI('r', 'K')
    rrp = sa([rnn], 'nnrpd', 'r e. RR+')
    tr = sa([f['psr'], rrp], 'rerpdivcld', '%s e. RR' % T)
    tc = sa([tr], 'recnd', '%s e. CC' % T)
    AP = '( abs ` %s )' % PSI('r', 'K')
    t1 = sa([sa([f['psr']], 'recnd', '%s e. CC' % PSI('r', 'K')), sa([rrp], 'rpcnd', 'r e. CC'), sa([rrp], 'rpne0d', 'r =/= 0')], 'absdivd',
            '( abs ` %s ) = ( %s / ( abs ` r ) )' % (T, AP))
    t2 = sa([t1, sa([sa([sa([rrp], 'rpred', 'r e. RR'), sa([rrp], 'rpge0d', '0 <_ r')], 'absidd', '( abs ` r ) = r')], 'oveq2d', '( %s / ( abs ` r ) ) = ( %s / r )' % (AP, AP))],
            'eqtrd', '( abs ` %s ) = ( %s / r )' % (T, AP))
    pa = sa([rnn, lift(w, knn, a), w.inst('z5psiabs')], 'syl2anc', '%s <_ r' % AP)
    apr = sa([sa([f['psr']], 'recnd', '%s e. CC' % PSI('r', 'K'))], 'abscld', '%s e. RR' % AP)
    q = sa([sa([pa, sa([sa([sa([rrp], 'rpcnd', 'r e. CC')], 'mulridd', '( r x. 1 ) = r')], 'eqcomd', 'r = ( r x. 1 )')], 'breqtrd', '%s <_ ( r x. 1 )' % AP),
            sa([apr, sa([], '1red', '1 e. RR'), rrp], 'ledivmuld', '( ( %s / r ) <_ 1 <-> %s <_ ( r x. 1 ) )' % (AP, AP))], 'mpbird', '( %s / r ) <_ 1' % AP)
    tle = sa([t2, q], 'eqbrtrd', '( abs ` %s ) <_ 1' % T)
    S1 = 'sum_ r e. ( N RSet R ) ( abs ` %s )' % T; S2 = 'sum_ r e. ( N RSet R ) 1'
    s1 = st([fin, tc], 'fsumabs', '( abs ` %s ) <_ %s' % (PFV('N', 'R', 'K'), S1))
    atr = sa([tc], 'abscld', '( abs ` %s ) e. RR' % T)
    s2 = st([fin, atr, sa([], '1red', '1 e. RR'), tle], 'fsumle', '%s <_ %s' % (S1, S2))
    HS = '( # ` ( N RSet R ) )'
    s3 = sy2(w, ante, fin, st([], '1cnd', '1 e. CC'), 'fsumconst', '%s = ( %s x. 1 )' % (S2, HS))
    hr = st([sy(w, ante, fin, 'hashcl', '%s e. NN0' % HS)], 'nn0red', '%s e. RR' % HS)
    s4 = st([s3, st([st([hr], 'recnd', '%s e. CC' % HS)], 'mulridd', '( %s x. 1 ) = %s' % (HS, HS))], 'eqtrd', '%s = %s' % (S2, HS))
    s5 = st([nv, rr, r0, w.inst('z5rsetcard')], 'syl12anc', '%s <_ ( |_ ` R )' % HS)
    A1 = '( abs ` %s )' % PFV('N', 'R', 'K')
    a1r = st([st([fin, tc], 'fsumcl', '%s e. CC' % PFV('N', 'R', 'K'))], 'abscld', '%s e. RR' % A1)
    s1r = st([fin, atr], 'fsumrecl', '%s e. RR' % S1)
    s2r = st([fin, sa([], '1red', '1 e. RR')], 'fsumrecl', '%s e. RR' % S2)
    c1 = st([a1r, s1r, s2r, s1, s2], 'letrd', '%s <_ %s' % (A1, S2))
    flr = st([st([rr], 'flcld', '( |_ ` R ) e. ZZ')], 'zred', '( |_ ` R ) e. RR')
    c2 = st([a1r, hr, flr, st([c1, s4], 'breqtrd', '%s <_ %s' % (A1, HS)), s5], 'letrd', '%s <_ ( |_ ` R )' % A1)
    w.qed([st([pv], 'fveq2d', '( abs ` ( ( N PFun R ) ` K ) ) = %s' % A1), c2], 'eqbrtrd', STATEMENTS['z5pfunabs'])
    return w


def z5pfun1():
    w = W('z5pfun1', "Lean Pfun_one: ( ( N PFun R ) ` 1 ) = sum_ r e. ( N RSet R ) 1 / r (Lean P1 N R), since psi_r ( 1 ) = mmu ( 1 ) phi ( 1 ) = 1.")
    ante = HNR
    st = mkst(w, ante)
    nv = st([], 'simpl', 'N e. V'); rw = st([], 'simpr', 'R e. W')
    pv = st([nv, rw, a1c(w, ante, '1nn', '1 e. NN'), w.inst('z5pfunval')], 'syl21anc', '( ( N PFun R ) ` 1 ) = %s' % PFV('N', 'R', '1'))
    a = '( %s /\\ r e. ( N RSet R ) )' % ante
    sa = mkst(w, a)
    rnn = rmem(w, a, lift(w, nv, a), lift(w, rw, a))
    g1 = sy(w, a, sa([rnn], 'nnzd', 'r e. ZZ'), 'gcd1', '( r gcd 1 ) = 1')
    rw1, new = w.rewrite(PSI('r', '1'), {'( r gcd 1 )': ('1', g1)}, a)
    v1 = sa([a1c(w, a, 'muone', '( mmu ` 1 ) = 1'), a1c(w, a, 'phi1', '( phi ` 1 ) = 1')], 'oveq12d', '( ( mmu ` 1 ) x. ( phi ` 1 ) ) = ( 1 x. 1 )')
    v2 = sa([v1, a1c(w, a, '1t1e1', '( 1 x. 1 ) = 1')], 'eqtrd', '( ( mmu ` 1 ) x. ( phi ` 1 ) ) = 1')
    p1 = sa([rw1, v2], 'eqtrd', '%s = 1' % PSI('r', '1'))
    t = sa([p1], 'oveq1d', '( %s / r ) = ( 1 / r )' % PSI('r', '1'))
    s = st([t], 'sumeq2dv', '%s = sum_ r e. ( N RSet R ) ( 1 / r )' % PFV('N', 'R', '1'))
    w.qed([pv, s], 'eqtrd', STATEMENTS['z5pfun1'])
    return w


def z5p1ge0():
    w = W('z5p1ge0', "Lean P1_nonneg: 0 <_ sum_ r e. ( N RSet R ) 1 / r.")
    ante = HNR
    st = mkst(w, ante)
    nv = st([], 'simpl', 'N e. V'); rw = st([], 'simpr', 'R e. W')
    fin = st([st([nv, rw, w.inst('z5rsetfi')], 'syl2anc', '( ( N RSet R ) C_ ( 1 ... ( |_ ` R ) ) /\\ ( N RSet R ) e. Fin )')], 'simprd', '( N RSet R ) e. Fin')
    a = '( %s /\\ r e. ( N RSet R ) )' % ante
    sa = mkst(w, a)
    rnn = rmem(w, a, lift(w, nv, a), lift(w, rw, a))
    rp = sa([sa([rnn], 'nnrpd', 'r e. RR+')], 'rpreccld', '( 1 / r ) e. RR+')
    w.qed([fin, sa([rp], 'rpred', '( 1 / r ) e. RR'), sa([rp], 'rpge0d', '0 <_ ( 1 / r )')], 'fsumge0', STATEMENTS['z5p1ge0'])
    return w


if __name__ == '__main__':
    import z5alib
    for f in sys.argv[1:]:
        z5alib.run(globals()[f]())
