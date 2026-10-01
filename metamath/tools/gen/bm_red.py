"""Sortie BM: the reduced modulus (Lean exists_reduced_modulus, AGP (4.1)): bmhalf, bmred0,
bmredlem, bmred."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from bm_base import *


def gen_half():
    w = W('bmhalf', 'Removing one prime factor ` P ` of a squarefree ` W ` at most halves the number of divisors up to ` y ` (AGP (4.1) for one prime): the divisors of ` W ` lie in the divisors of ` W / P ` together with their ` P ` -multiples (~ coprmdvds , ~ dvdscmulr , ~ bmhashim ).')
    A0 = '( ( W e. NN /\\ ( mmu ` W ) =/= 0 ) /\\ ( P e. Prime /\\ P || W ) )'
    A = '( %s /\\ y e. RR )' % A0
    s = S_(w, A)
    u = unpack(w, A)
    wn, wsf, pp, pdw, yr = u['W e. NN'], u['( mmu ` W ) =/= 0'], u['P e. Prime'], u['P || W'], u['y e. RR']
    pn = s([pp, w.inst('prmnn')], 'syl', 'P e. NN'); pz = s([pn], 'nnzd', 'P e. ZZ'); pc = s([pn], 'nncnd', 'P e. CC'); pn0 = s([pn], 'nnne0d', 'P =/= 0')
    wz = s([wn], 'nnzd', 'W e. ZZ'); wc = s([wn], 'nncnd', 'W e. CC')
    WP = '( W / P )'
    wpn = s([pdw, s([wn, pn, w.inst('nndivdvds')], 'syl2anc', '( P || W <-> %s e. NN )' % WP)], 'mpbid', '%s e. NN' % WP)
    wpz = s([wpn], 'nnzd', '%s e. ZZ' % WP); wpc = s([wpn], 'nncnd', '%s e. CC' % WP)
    eqW = s([wc, pc, pn0], 'divcan2d', '( P x. %s ) = W' % WP)
    AS = CNTS('W', 'y'); BS = CNTS(WP, 'y')
    M = '( h e. NN |-> ( P x. h ) )'; IM = '( %s " %s )' % (M, BS)
    # M Fn NN (closed)
    m1 = w.s([w.s([], 'ovex', '( P x. h ) e. _V')], 'a1i', '( h e. NN -> ( P x. h ) e. _V )')
    m2 = w.s([m1], 'rgen', 'A. h e. NN ( P x. h ) e. _V')
    m3i = w.s([w.s([], 'eqid', '%s = %s' % (M, M))], 'fnmpt', '( A. h e. NN ( P x. h ) e. _V -> %s Fn NN )' % M)
    m3 = w.s([m2, m3i], 'ax-mp', '%s Fn NN' % M)
    mfn = s([m3], 'a1i', '%s Fn NN' % M)
    mfun = s([mfn], 'fnfund', 'Fun %s' % M)
    # BS C_ NN, finite
    bs1 = w.s([], 'ssrab2', '%s C_ %s' % (BS, DIV(WP)))
    bs2 = w.s([], 'ssrab2', '%s C_ ( 1 ... %s )' % (DIV(WP), WP))
    bs3 = w.s([], 'fz1ssnn', '( 1 ... %s ) C_ NN' % WP)
    bs4 = w.s([bs2, bs3], 'sstri', '%s C_ NN' % DIV(WP))
    bs5 = w.s([bs1, bs4], 'sstri', '%s C_ NN' % BS)
    bsnn = s([bs5], 'a1i', '%s C_ NN' % BS)
    bsfin = s([finrab(w, BS)], 'a1i', '%s e. Fin' % BS)
    imfin = s([mfun, bsfin, w.inst('imafi')], 'syl2anc', '%s e. Fin' % IM)
    # AS C_ ( BS u. IM )
    A2 = '( %s /\\ e e. %s )' % (A, AS)
    s2 = S_(w, A2)
    L2 = lambda x_: lift(w, x_, A2)
    ein = s2([], 'simpr', 'e e. %s' % AS)
    cg = w.s([], 'breq1', '( d = e -> ( d <_ y <-> e <_ y ) )')
    el = w.s([cg], 'elrab', '( e e. %s <-> ( e e. %s /\\ e <_ y ) )' % (AS, DIV('W')))
    ed = s2([ein, el], 'sylib', '( e e. %s /\\ e <_ y )' % DIV('W'))
    ediv = s2([ed], 'simpld', 'e e. %s' % DIV('W')); ely = s2([ed], 'simprd', 'e <_ y')
    edb = s2([L2(wn), w.inst('bmeldiv')], 'syl', '( e e. %s <-> ( e e. NN /\\ e || W ) )' % DIV('W'))
    ed2 = s2([ediv, edb], 'mpbid', '( e e. NN /\\ e || W )')
    en = s2([ed2], 'simpld', 'e e. NN'); edw = s2([ed2], 'simprd', 'e || W')
    ez = s2([en], 'nnzd', 'e e. ZZ'); ec = s2([en], 'nncnd', 'e e. CC'); er = s2([en], 'nnred', 'e e. RR')
    elun_ = w.s([], 'elun', '( e e. ( %s u. %s ) <-> ( e e. %s \\/ e e. %s ) )' % (BS, IM, BS, IM))
    # case -. P || e
    A3 = '( %s /\\ -. P || e )' % A2
    s3 = S_(w, A3)
    L3 = lambda x_: lift(w, x_, A3)
    npe = s3([], 'simpr', '-. P || e')
    cp1 = s3([npe, s3([L3(pp), L3(ez), w.inst('coprm')], 'syl2anc', '( -. P || e <-> ( P gcd e ) = 1 )')], 'mpbid', '( P gcd e ) = 1')
    cp2 = s3([L3(pz), L3(ez)], 'gcdcomd', '( P gcd e ) = ( e gcd P )')
    cp3 = s3([cp2, cp1], 'eqtr3d', '( e gcd P ) = 1')
    dv1 = s3([L3(edw), L3(eqW)], 'breqtrrd', 'e || ( P x. %s )' % WP)
    dv2 = s3([s3([dv1, cp3], 'jca', '( e || ( P x. %s ) /\\ ( e gcd P ) = 1 )' % WP), s3([L3(ez), L3(pz), L3(wpz), w.inst('coprmdvds')], 'syl3anc', '( ( e || ( P x. %s ) /\\ ( e gcd P ) = 1 ) -> e || %s )' % (WP, WP))], 'mpd', 'e || %s' % WP)
    eb = s3([s3([L3(en), dv2], 'jca', '( e e. NN /\\ e || %s )' % WP), s3([L3(wpn), w.inst('bmeldiv')], 'syl', '( e e. %s <-> ( e e. NN /\\ e || %s ) )' % (DIV(WP), WP))], 'mpbird', 'e e. %s' % DIV(WP))
    elb = w.s([cg], 'elrab', '( e e. %s <-> ( e e. %s /\\ e <_ y ) )' % (BS, DIV(WP)))
    ebs = s3([s3([eb, L3(ely)], 'jca', '( e e. %s /\\ e <_ y )' % DIV(WP)), elb], 'sylibr', 'e e. %s' % BS)
    c1 = s3([s3([ebs], 'orcd', '( e e. %s \\/ e e. %s )' % (BS, IM)), elun_], 'sylibr', 'e e. ( %s u. %s )' % (BS, IM))
    # case P || e
    A4 = '( %s /\\ P || e )' % A2
    s4 = S_(w, A4)
    L4 = lambda x_: lift(w, x_, A4)
    pe = s4([], 'simpr', 'P || e')
    F = '( e / P )'
    fn = s4([pe, s4([L4(en), L4(pn), w.inst('nndivdvds')], 'syl2anc', '( P || e <-> %s e. NN )' % F)], 'mpbid', '%s e. NN' % F)
    fz = s4([fn], 'nnzd', '%s e. ZZ' % F); fr = s4([fn], 'nnred', '%s e. RR' % F)
    eqE = s4([L4(ec), L4(pc), L4(pn0)], 'divcan2d', '( P x. %s ) = e' % F)
    b1 = s4([eqE, L4(eqW)], 'breq12d', '( ( P x. %s ) || ( P x. %s ) <-> e || W )' % (F, WP))
    b2 = s4([fz, L4(wpz), s4([L4(pz), L4(pn0)], 'jca', '( P e. ZZ /\\ P =/= 0 )'), w.inst('dvdscmulr')], 'syl3anc', '( ( P x. %s ) || ( P x. %s ) <-> %s || %s )' % (F, WP, F, WP))
    b3 = s4([b1, b2], 'bitr3d', '( e || W <-> %s || %s )' % (F, WP))
    fdv = s4([L4(edw), b3], 'mpbid', '%s || %s' % (F, WP))
    fle1 = s4([fr, L4(s([pn], 'nnred', 'P e. RR')), s4([s4([fn], 'nnnn0d', '%s e. NN0' % F)], 'nn0ge0d', '0 <_ %s' % F), L4(s([pn], 'nnge1d', '1 <_ P'))], 'lemulge12d', '%s <_ ( P x. %s )' % (F, F))
    fle2 = s4([fle1, eqE], 'breqtrd', '%s <_ e' % F)
    fley = s4([fr, L4(er), L4(yr), fle2, L4(ely)], 'letrd', '%s <_ y' % F)
    fb = s4([s4([fn, fdv], 'jca', '( %s e. NN /\\ %s || %s )' % (F, F, WP)), s4([L4(wpn), w.inst('bmeldiv')], 'syl', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (F, DIV(WP), F, F, WP))], 'mpbird', '%s e. %s' % (F, DIV(WP)))
    cgf = w.s([], 'breq1', '( d = %s -> ( d <_ y <-> %s <_ y ) )' % (F, F))
    elf = w.s([cgf], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s <_ y ) )' % (F, BS, F, DIV(WP), F))
    fbs = s4([s4([fb, fley], 'jca', '( %s e. %s /\\ %s <_ y )' % (F, DIV(WP), F)), elf], 'sylibr', '%s e. %s' % (F, BS))
    fim = s4([L4(mfn), L4(bsnn), fbs, w.inst('fnfvima')], 'syl3anc', '( %s ` %s ) e. %s' % (M, F, IM))
    mv, val = congr.mptval(w, A4, 'h', 'NN', '( P x. h )', F, fn)
    assert val == '( P x. %s )' % F, val
    mv2 = s4([mv, eqE], 'eqtrd', '( %s ` %s ) = e' % (M, F))
    eim = s4([mv2, fim], 'eqeltrrd', 'e e. %s' % IM)
    c2 = s4([s4([eim], 'olcd', '( e e. %s \\/ e e. %s )' % (BS, IM)), elun_], 'sylibr', 'e e. ( %s u. %s )' % (BS, IM))
    both = w.s([c2, c1], 'pm2.61dan', '( %s -> e e. ( %s u. %s ) )' % (A2, BS, IM))
    ss = s([w.s([both], 'ex', '( %s -> ( e e. %s -> e e. ( %s u. %s ) ) )' % (A, AS, BS, IM))], 'ssrdv', '%s C_ ( %s u. %s )' % (AS, BS, IM))
    # counting
    ufin = s([bsfin, imfin, w.inst('unfi')], 'syl2anc', '( %s u. %s ) e. Fin' % (BS, IM))
    h1 = s([ufin, ss, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` ( %s u. %s ) )' % (AS, BS, IM))
    h2 = s([bsfin, imfin, w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (BS, IM, BS, IM))
    h3 = s([mfn, bsfin, bsnn, w.inst('bmhashim')], 'syl3anc', '( # ` %s ) <_ ( # ` %s )' % (IM, BS))
    asfin = s([finrab(w, AS)], 'a1i', '%s e. Fin' % AS)
    har = s([s([asfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % AS)], 'nn0red', '( # ` %s ) e. RR' % AS)
    hur = s([s([ufin, w.inst('hashcl')], 'syl', '( # ` ( %s u. %s ) ) e. NN0' % (BS, IM))], 'nn0red', '( # ` ( %s u. %s ) ) e. RR' % (BS, IM))
    hbr = s([s([bsfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % BS)], 'nn0red', '( # ` %s ) e. RR' % BS)
    hir = s([s([imfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % IM)], 'nn0red', '( # ` %s ) e. RR' % IM)
    g = lin.linarith(w, A, [h1, h2, h3], '( # ` %s ) <_ ( 2 x. ( # ` %s ) )' % (AS, BS),
                     leaves={'( # ` %s )' % AS: har, '( # ` ( %s u. %s ) )' % (BS, IM): hur, '( # ` %s )' % BS: hbr, '( # ` %s )' % IM: hir}, fast=False)
    w.qed([g], 'ralrimiva', S['bmhalf'])
    return go(w)


ALL = {'bmhalf': gen_half}


def cnt_real(w, ante, n, y='y'):
    """( ante -> CNT(n,y) e. RR ) and ( ante -> 0 <_ CNT(n,y) ) (closed: a rab of a finite interval)"""
    f = finrab(w, CNTS(n, y))
    c = mpi(w, f, 'hashcl', '%s e. NN0' % CNT(n, y))
    r = w.s([mpi(w, c, 'nn0re', '%s e. RR' % CNT(n, y))], 'a1i', '( %s -> %s e. RR )' % (ante, CNT(n, y)))
    g = w.s([mpi(w, c, 'nn0ge0', '0 <_ %s' % CNT(n, y))], 'a1i', '( %s -> 0 <_ %s )' % (ante, CNT(n, y)))
    return r, g


def gen_red0():
    w = W('bmred0', 'The induction base of ~ bmred : with no exceptional modulus the reduced modulus is ` n ` itself (~ iddvds , ~ ral0 , ~ hash0 ).')
    HYP = '( ( mmu ` n ) =/= 0 /\\ A. i e. (/) 2 <_ i )'
    B = '( n e. NN /\\ %s )' % HYP
    s = S_(w, B)
    nn = s([], 'simpl', 'n e. NN')
    d1 = s([s([nn], 'nnzd', 'n e. ZZ'), w.inst('iddvds')], 'syl', 'n || n')
    d2 = s([w.s([], 'ral0', 'A. i e. (/) -. i || n')], 'a1i', 'A. i e. (/) -. i || n')
    BY = '( %s /\\ y e. RR )' % B
    cr, cg = cnt_real(w, BY, 'n')
    e1 = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'oveq2i', '( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 )')
    e2 = w.s([w.s([], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')
    e3 = w.s([e1, e2], 'eqtri', '( 2 ^ ( # ` (/) ) ) = 1')
    e4 = w.s([e3], 'a1i', '( %s -> ( 2 ^ ( # ` (/) ) ) = 1 )' % BY)
    e5 = w.s([e4], 'oveq1d', '( %s -> ( ( 2 ^ ( # ` (/) ) ) x. %s ) = ( 1 x. %s ) )' % (BY, CNT('n', 'y'), CNT('n', 'y')))
    e6 = w.s([w.s([cr], 'recnd', '( %s -> %s e. CC )' % (BY, CNT('n', 'y')))], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (BY, CNT('n', 'y'), CNT('n', 'y')))
    e7 = w.s([e5, e6], 'eqtrd', '( %s -> ( ( 2 ^ ( # ` (/) ) ) x. %s ) = %s )' % (BY, CNT('n', 'y'), CNT('n', 'y')))
    e8 = w.s([w.s([cr], 'leidd', '( %s -> %s <_ %s )' % (BY, CNT('n', 'y'), CNT('n', 'y'))), e7], 'breqtrrd', '( %s -> %s <_ ( ( 2 ^ ( # ` (/) ) ) x. %s ) )' % (BY, CNT('n', 'y'), CNT('n', 'y')))
    d3 = s([e8], 'ralrimiva', 'A. y e. RR %s <_ ( ( 2 ^ ( # ` (/) ) ) x. %s )' % (CNT('n', 'y'), CNT('n', 'y')))
    BODY = lambda ww: '( %s || n /\\ A. i e. (/) -. i || %s /\\ A. y e. RR %s <_ ( ( 2 ^ ( # ` (/) ) ) x. %s ) )' % (ww, ww, CNT('n', 'y'), CNT(ww, 'y'))
    b3 = s([d1, d2, d3], '3jca', BODY('n'))
    cg_, new = wc(w, BODY('w'), 'w', 'n')
    assert new == BODY('n'), new
    ex = s([nn, b3, w.s([cg_], 'rspcev', '( ( n e. NN /\\ %s ) -> E. w e. NN %s )' % (BODY('n'), BODY('w')))], 'syl2anc', 'E. w e. NN %s' % BODY('w'))
    im = w.s([ex], 'ex', '( n e. NN -> ( %s -> E. w e. NN %s ) )' % (HYP, BODY('w')))
    w.qed([im], 'rgen', S['bmred0'])
    return go(w)


def gen_redlem():
    w = W('bmredlem', 'The induction step of ~ bmred : a further exceptional modulus ` u ` costs at most one prime factor of the reduced modulus (~ exprmfct ) and a factor 2 in the divisor counts (~ bmhalf ); ` u ` no longer divides the quotient because the modulus is squarefree (~ sqfpc , ~ pcmul , ~ pceq0 ).')
    T1 = '( t u. { u } )'
    Y0 = '( t e. Fin /\\ -. u e. t )'
    P = '( 2 ^ ( # ` t ) )'; P1 = '( 2 ^ ( # ` %s ) )' % T1
    HYP = lambda ss: '( ( mmu ` n ) =/= 0 /\\ A. i e. %s 2 <_ i )' % ss
    BODY = lambda ss, ww: '( %s || n /\\ A. i e. %s -. i || %s /\\ A. y e. RR %s <_ ( ( 2 ^ ( # ` %s ) ) x. %s ) )' % (ww, ss, ww, CNT('n', 'y'), ss, CNT(ww, 'y'))
    INST = lambda ss: '( %s -> E. w e. NN %s )' % (HYP(ss), BODY(ss, 'w'))
    assert PRED('t') == 'A. n e. NN %s' % INST('t')
    # ---- 2 ^ # T1 = P x. 2 under Y0
    sy = S_(w, Y0)
    hu = w.s([w.s([], 'vex', 'u e. _V'), w.inst('hashunsng')], 'ax-mp', '( %s -> ( # ` %s ) = ( ( # ` t ) + 1 ) )' % (Y0, T1))
    hu = w.s([hu], 'id', '( %s -> ( # ` %s ) = ( ( # ` t ) + 1 ) )' % (Y0, T1)) if False else hu
    tn0 = sy([sy([], 'simpl', 't e. Fin'), w.inst('hashcl')], 'syl', '( # ` t ) e. NN0')
    two = sy([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')
    pe1 = sy([hu], 'oveq2d', '%s = ( 2 ^ ( ( # ` t ) + 1 ) )' % P1)
    pe2 = sy([two, tn0, w.inst('expp1')], 'syl2anc', '( 2 ^ ( ( # ` t ) + 1 ) ) = ( %s x. 2 )' % P)
    peq = sy([pe1, pe2], 'eqtrd', '%s = ( %s x. 2 )' % (P1, P))
    pnn = sy([sy([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), tn0, w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % P)
    # ---- count transfer, case A (w := v) and case B (w := ( v / p )), under YY = ( Y0 /\ y e. RR )
    YY = '( %s /\\ y e. RR )' % Y0
    syy = S_(w, YY)
    Cn = CNT('n', 'y'); Cv = CNT('v', 'y'); VP = '( v / p )'; Cw = CNT(VP, 'y')
    cnr, cng = cnt_real(w, YY, 'n'); cvr, cvg = cnt_real(w, YY, 'v'); cwr, cwg = cnt_real(w, YY, VP)
    pr = syy([lift(w, pnn, YY)], 'nnred', '%s e. RR' % P); pc = syy([pr], 'recnd', '%s e. CC' % P)
    pg = syy([syy([lift(w, pnn, YY)], 'nnnn0d', '%s e. NN0' % P)], 'nn0ge0d', '0 <_ %s' % P)
    peqy = lift(w, peq, YY)
    twoy = syy([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')
    M = '( %s x. %s )' % (P, Cv)
    mr = syy([pr, cvr], 'remulcld', '%s e. RR' % M); mg = syy([pr, cvr, pg, cvg], 'mulge0d', '0 <_ %s' % M)
    # case A: ( CNT(n) <_ M -> CNT(n) <_ ( P1 x. Cv ) )
    ea1 = syy([peqy], 'oveq1d', '( %s x. %s ) = ( ( %s x. 2 ) x. %s )' % (P1, Cv, P, Cv))
    ea2 = syy([pc, twoy, syy([cvr], 'recnd', '%s e. CC' % Cv)], 'mul32d', '( ( %s x. 2 ) x. %s ) = ( %s x. 2 )' % (P, Cv, M))
    ea3 = syy([syy([mr], 'recnd', '%s e. CC' % M), twoy], 'mulcomd', '( %s x. 2 ) = ( 2 x. %s )' % (M, M))
    ea4 = syy([syy([ea1, ea2], 'eqtrd', '( %s x. %s ) = ( %s x. 2 )' % (P1, Cv, M)), ea3], 'eqtrd', '( %s x. %s ) = ( 2 x. %s )' % (P1, Cv, M))
    YA = '( %s /\\ %s <_ %s )' % (YY, Cn, M)
    ha = w.s([], 'simpr', '( %s -> %s <_ %s )' % (YA, Cn, M))
    ga = lin.linarith(w, YA, [ha, lift(w, mg, YA)], '%s <_ ( 2 x. %s )' % (Cn, M), leaves={Cn: lift(w, cnr, YA), M: lift(w, mr, YA)}, atoms=[M, Cn], fast=False)
    ga2 = w.s([ga, lift(w, ea4, YA)], 'breqtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (YA, Cn, P1, Cv))
    tA = w.s([ga2], 'ex', '( %s -> ( %s <_ %s -> %s <_ ( %s x. %s ) ) )' % (YY, Cn, M, Cn, P1, Cv))
    # case B: ( ( CNT(n) <_ M /\ Cv <_ 2 Cw ) -> CNT(n) <_ ( P1 x. Cw ) )
    YB = '( %s /\\ ( %s <_ %s /\\ %s <_ ( 2 x. %s ) ) )' % (YY, Cn, M, Cv, Cw)
    sb = S_(w, YB)
    hb1 = sb([], 'simprl', '%s <_ %s' % (Cn, M)); hb2 = sb([], 'simprr', '%s <_ ( 2 x. %s )' % (Cv, Cw))
    Cw2 = '( 2 x. %s )' % Cw
    cw2r = sb([sb([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), lift(w, cwr, YB)], 'remulcld', '%s e. RR' % Cw2)
    eb1 = sb([lift(w, cvr, YB), cw2r, lift(w, pr, YB), lift(w, pg, YB), hb2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (P, Cv, P, Cw2))
    eb2 = sb([lift(w, cnr, YB), lift(w, mr, YB), sb([lift(w, pr, YB), cw2r], 'remulcld', '( %s x. %s ) e. RR' % (P, Cw2)), hb1, eb1], 'letrd', '%s <_ ( %s x. %s )' % (Cn, P, Cw2))
    eb3 = sb([lift(w, peqy, YB)], 'oveq1d', '( %s x. %s ) = ( ( %s x. 2 ) x. %s )' % (P1, Cw, P, Cw))
    eb4 = sb([lift(w, pc, YB), sb([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC'), sb([lift(w, cwr, YB)], 'recnd', '%s e. CC' % Cw)], 'mulassd', '( ( %s x. 2 ) x. %s ) = ( %s x. %s )' % (P, Cw, P, Cw2))
    eb5 = sb([eb3, eb4], 'eqtrd', '( %s x. %s ) = ( %s x. %s )' % (P1, Cw, P, Cw2))
    gb = sb([eb2, eb5], 'breqtrrd', '%s <_ ( %s x. %s )' % (Cn, P1, Cw))
    tB = w.s([gb], 'ex', '( %s -> ( ( %s <_ %s /\\ %s <_ ( 2 x. %s ) ) -> %s <_ ( %s x. %s ) ) )' % (YY, Cn, M, Cv, Cw, Cn, P1, Cw))
    # the quantified forms
    RA0 = 'A. y e. RR %s <_ %s' % (Cn, M); RA1 = 'A. y e. RR %s <_ ( %s x. %s )' % (Cn, P1, Cv)
    RB0 = 'A. y e. RR %s <_ ( 2 x. %s )' % (Cv, Cw); RB1 = 'A. y e. RR %s <_ ( %s x. %s )' % (Cn, P1, Cw)
    qA = w.s([tA], 'ralimdva', '( %s -> ( %s -> %s ) )' % (Y0, RA0, RA1))
    qB0 = w.s([tB], 'ralimdva', '( %s -> ( A. y e. RR ( %s <_ %s /\\ %s <_ ( 2 x. %s ) ) -> %s ) )' % (Y0, Cn, M, Cv, Cw, RB1))
    r26 = w.s([], 'r19.26', '( A. y e. RR ( %s <_ %s /\\ %s <_ ( 2 x. %s ) ) <-> ( %s /\\ %s ) )' % (Cn, M, Cv, Cw, RA0, RB0))
    qB = w.s([r26, qB0], 'syl5bir' if False else 'x', 'x') if False else None
    qB = w.s([qB0, w.s([r26], 'biimpri', '( ( %s /\\ %s ) -> A. y e. RR ( %s <_ %s /\\ %s <_ ( 2 x. %s ) ) )' % (RA0, RB0, Cn, M, Cv, Cw))], 'syl5' if False else 'x', 'x') if False else None
    bi = w.s([r26], 'biimpri', '( ( %s /\\ %s ) -> A. y e. RR ( %s <_ %s /\\ %s <_ ( 2 x. %s ) ) )' % (RA0, RB0, Cn, M, Cv, Cw))
    qB = w.s([bi, qB0], 'syl5', '( %s -> ( ( %s /\\ %s ) -> %s ) )' % (Y0, RA0, RB0, RB1))
    # ---- the i-transfer: ( X -> ( A. i e. t -. i || v -> A. i e. t -. i || ( v / p ) ) ), X i-free
    X = '( v e. NN /\\ %s e. NN /\\ %s || v )' % (VP, VP)
    XI = '( ( %s /\\ i e. t ) /\\ i || %s )' % (X, VP)
    sxi = S_(w, XI)
    iz = sxi([sxi([sxi([], 'simpr', 'i || %s' % VP), w.inst('dvdszrcl')], 'syl', '( i e. ZZ /\\ %s e. ZZ )' % VP)], 'simpld', 'i e. ZZ')
    vpz = sxi([sxi([lift(w, w.s([], 'simp2', '( %s -> %s e. NN )' % (X, VP)), XI)], 'nnzd', '%s e. ZZ' % VP)], 'id', '%s e. ZZ' % VP) if False else sxi([lift(w, w.s([], 'simp2', '( %s -> %s e. NN )' % (X, VP)), XI)], 'nnzd', '%s e. ZZ' % VP)
    vz = sxi([lift(w, w.s([], 'simp1', '( %s -> v e. NN )' % X), XI)], 'nnzd', 'v e. ZZ')
    dt = sxi([sxi([sxi([], 'simpr', 'i || %s' % VP), lift(w, w.s([], 'simp3', '( %s -> %s || v )' % (X, VP)), XI)], 'jca', '( i || %s /\\ %s || v )' % (VP, VP)), sxi([iz, vpz, vz, w.inst('dvdstr')], 'syl3anc', '( ( i || %s /\\ %s || v ) -> i || v )' % (VP, VP))], 'mpd', 'i || v')
    dt2 = w.s([w.s([dt], 'ex', '( ( %s /\\ i e. t ) -> ( i || %s -> i || v ) )' % (X, VP))], 'con3d', '( ( %s /\\ i e. t ) -> ( -. i || v -> -. i || %s ) )' % (X, VP))
    itr = w.s([dt2], 'ralimdva', '( %s -> ( A. i e. t -. i || v -> A. i e. t -. i || %s ) )' % (X, VP))
    # ---- the main context
    C1 = '( ( %s /\\ n e. NN ) /\\ %s )' % (Y0, INST('t'))
    C2 = '( %s /\\ %s )' % (C1, HYP(T1))
    s2 = S_(w, C2)
    L2 = lambda x_: lift(w, x_, C2)
    y0 = s2([], 'simp-4l' if False else 'x', 'x') if False else None
    y0 = w.s([], 'simpl', '( ( %s /\\ n e. NN ) -> %s )' % (Y0, Y0)); y0 = lift(w, y0, C2)
    nn = w.s([], 'simplr', '( ( %s /\\ n e. NN ) -> n e. NN )' % Y0) if False else w.s([], 'simpr', '( ( %s /\\ n e. NN ) -> n e. NN )' % Y0); nn = lift(w, nn, C2)
    inst = w.s([], 'simpr', '( %s -> %s )' % (C1, INST('t'))); inst = lift(w, inst, C2)
    hyp1 = s2([], 'simpr', HYP(T1))
    msf = s2([hyp1], 'simpld', '( mmu ` n ) =/= 0'); ge2 = s2([hyp1], 'simprd', 'A. i e. %s 2 <_ i' % T1)
    cgu = w.s([], 'breq2', '( i = u -> ( 2 <_ i <-> 2 <_ u ) )')
    rus = w.s([w.s([], 'vex', 'u e. _V'), w.s([cgu], 'ralunsn', '( u e. _V -> ( A. i e. %s 2 <_ i <-> ( A. i e. t 2 <_ i /\\ 2 <_ u ) ) )' % T1)], 'ax-mp', '( A. i e. %s 2 <_ i <-> ( A. i e. t 2 <_ i /\\ 2 <_ u ) )' % T1)
    ge2b = s2([ge2, rus], 'sylib', '( A. i e. t 2 <_ i /\\ 2 <_ u )')
    ge2t = s2([ge2b], 'simpld', 'A. i e. t 2 <_ i'); u2 = s2([ge2b], 'simprd', '2 <_ u')
    exw = s2([s2([msf, ge2t], 'jca', HYP('t')), inst], 'mpd', 'E. w e. NN %s' % BODY('t', 'w'))
    cgv, bv = wc(w, BODY('t', 'w'), 'w', 'v')
    assert bv == BODY('t', 'v'), bv
    exv = s2([exw, w.s([cgv], 'cbvrexvw', '( E. w e. NN %s <-> E. v e. NN %s )' % (BODY('t', 'w'), BODY('t', 'v')))], 'sylib', 'E. v e. NN %s' % BODY('t', 'v'))
    GOAL = 'E. w e. NN %s' % BODY(T1, 'w')
    # ---- under C3: a fixed v
    C3 = '( %s /\\ ( v e. NN /\\ %s ) )' % (C2, BODY('t', 'v'))
    s3 = S_(w, C3)
    L3 = lambda x_: lift(w, x_, C3)
    vn = s3([], 'simprl', 'v e. NN'); vb = s3([], 'simprr', BODY('t', 'v'))
    vdn = s3([vb], 'simp1d', 'v || n'); vbad = s3([vb], 'simp2d', 'A. i e. t -. i || v'); vcnt = s3([vb], 'simp3d', RA0)
    vz3 = s3([vn], 'nnzd', 'v e. ZZ')
    cgw = w.s([], 'breq1', '( i = u -> ( i || w <-> u || w ) )')
    cgwn = w.s([cgw], 'notbid', '( i = u -> ( -. i || w <-> -. u || w ) )')
    # case A: -. u || v
    C4A = '( %s /\\ -. u || v )' % C3
    s4a = S_(w, C4A)
    L4a = lambda x_: lift(w, x_, C4A)
    nuv = s4a([], 'simpr', '-. u || v')
    cgvn, _ = wc(w, '-. i || v', 'i', 'u')
    rusv = w.s([w.s([], 'vex', 'u e. _V'), w.s([cgvn], 'ralunsn', '( u e. _V -> ( A. i e. %s -. i || v <-> ( A. i e. t -. i || v /\\ -. u || v ) ) )' % T1)], 'ax-mp', '( A. i e. %s -. i || v <-> ( A. i e. t -. i || v /\\ -. u || v ) )' % T1)
    badA = s4a([s4a([L4a(vbad), nuv], 'jca', '( A. i e. t -. i || v /\\ -. u || v )'), rusv], 'sylibr', 'A. i e. %s -. i || v' % T1)
    cntA = s4a([L4a(vcnt), s4a([L4a(y0), qA], 'syl', '( %s -> %s )' % (RA0, RA1))], 'mpd', RA1)
    bodyA = s4a([L4a(vdn), badA, cntA], '3jca', BODY(T1, 'v'))
    cgA, bA = wc(w, BODY(T1, 'w'), 'w', 'v')
    assert bA == BODY(T1, 'v'), bA
    exA = s4a([L4a(vn), bodyA, w.s([cgA], 'rspcev', '( ( v e. NN /\\ %s ) -> %s )' % (BODY(T1, 'v'), GOAL))], 'syl2anc', GOAL)
    # case B: u || v
    C4B = '( %s /\\ u || v )' % C3
    s4b = S_(w, C4B)
    L4b = lambda x_: lift(w, x_, C4B)
    uv = s4b([], 'simpr', 'u || v')
    uz = s4b([s4b([uv, w.inst('dvdszrcl')], 'syl', '( u e. ZZ /\\ v e. ZZ )')], 'simpld', 'u e. ZZ')
    uuz = s4b([s4b([s4b([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), uz, L4b(u2)], '3jca', '( 2 e. ZZ /\\ u e. ZZ /\\ 2 <_ u )'), w.s([], 'eluz2', '( u e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ u e. ZZ /\\ 2 <_ u ) )')], 'sylibr', 'u e. ( ZZ>= ` 2 )')
    exp_ = s4b([uuz, w.inst('exprmfct')], 'syl', 'E. p e. Prime p || u')
    C5 = '( %s /\\ ( p e. Prime /\\ p || u ) )' % C4B
    s5 = S_(w, C5)
    L5 = lambda x_: lift(w, x_, C5)
    pp = s5([], 'simprl', 'p e. Prime'); pu = s5([], 'simprr', 'p || u')
    pn = s5([pp, w.inst('prmnn')], 'syl', 'p e. NN'); pz = s5([pn], 'nnzd', 'p e. ZZ'); pn0 = s5([pn], 'nnne0d', 'p =/= 0'); pc5 = s5([pn], 'nncnd', 'p e. CC')
    vn5 = L5(vn); vz5 = L5(vz3); vc5 = s5([vn5], 'nncnd', 'v e. CC')
    pv = s5([s5([pu, L5(uv)], 'jca', '( p || u /\\ u || v )'), s5([pz, L5(uz), vz5, w.inst('dvdstr')], 'syl3anc', '( ( p || u /\\ u || v ) -> p || v )')], 'mpd', 'p || v')
    vpn = s5([pv, s5([vn5, pn, w.inst('nndivdvds')], 'syl2anc', '( p || v <-> %s e. NN )' % VP)], 'mpbid', '%s e. NN' % VP)
    vpz = s5([vpn], 'nnzd', '%s e. ZZ' % VP); vpc = s5([vpn], 'nncnd', '%s e. CC' % VP); vpn0 = s5([vpn], 'nnne0d', '%s =/= 0' % VP)
    vpdv = s5([s5([pv, pn0], 'jca', '( p || v /\\ p =/= 0 )'), w.inst('divconjdvds')], 'syl', '%s || v' % VP)
    vpdn = s5([s5([vpdv, L5(vdn)], 'jca', '( %s || v /\\ v || n )' % VP), s5([vpz, vz5, s5([L5(nn)], 'nnzd', 'n e. ZZ'), w.inst('dvdstr')], 'syl3anc', '( ( %s || v /\\ v || n ) -> %s || n )' % (VP, VP))], 'mpd', '%s || n' % VP)
    vsf = s5([L5(msf), s5([L5(nn), vn5, L5(vdn), w.inst('dvdssqf')], 'syl3anc', '( ( mmu ` n ) =/= 0 -> ( mmu ` v ) =/= 0 )')], 'mpd', '( mmu ` v ) =/= 0')
    half = ap(w, C5, [vn5, vsf, pp, pv], 'bmhalf', RB0)
    # -. p || ( v / p )
    eqv = s5([vc5, pc5, pn0], 'divcan2d', '( p x. %s ) = v' % VP)
    pc1 = s5([pp, s5([pz, pn0], 'jca', '( p e. ZZ /\\ p =/= 0 )'), s5([vpz, vpn0], 'jca', '( %s e. ZZ /\\ %s =/= 0 )' % (VP, VP)), w.inst('pcmul')], 'syl3anc', '( p pCnt ( p x. %s ) ) = ( ( p pCnt p ) + ( p pCnt %s ) )' % (VP, VP))
    pc2 = s5([eqv], 'oveq2d', '( p pCnt ( p x. %s ) ) = ( p pCnt v )' % VP)
    pc3 = s5([pc2, pc1], 'eqtr3d', '( p pCnt v ) = ( ( p pCnt p ) + ( p pCnt %s ) )' % VP)
    pid = s5([s5([pp, s5([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0'), w.inst('pcidlem')], 'syl2anc', '( p pCnt ( p ^ 1 ) ) = 1')], 'id', '( p pCnt ( p ^ 1 ) ) = 1') if False else s5([pp, s5([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0'), w.inst('pcidlem')], 'syl2anc', '( p pCnt ( p ^ 1 ) ) = 1')
    pe1_ = s5([s5([pc5], 'exp1d', '( p ^ 1 ) = p')], 'oveq2d', '( p pCnt ( p ^ 1 ) ) = ( p pCnt p )')
    ppc = s5([pe1_, pid], 'eqtr3d', '( p pCnt p ) = 1')
    pc4 = s5([ppc], 'oveq1d', '( ( p pCnt p ) + ( p pCnt %s ) ) = ( 1 + ( p pCnt %s ) )' % (VP, VP))
    pc5_ = s5([pc3, pc4], 'eqtrd', '( p pCnt v ) = ( 1 + ( p pCnt %s ) )' % VP)
    sq = s5([vn5, vsf, pp, w.inst('sqfpc')], 'syl3anc', '( p pCnt v ) <_ 1')
    kn0 = s5([pp, vpn, w.inst('pccl')], 'syl2anc', '( p pCnt %s ) e. NN0' % VP)
    kr = s5([kn0], 'nn0red', '( p pCnt %s ) e. RR' % VP)
    kle = lin.linarith(w, C5, [pc5_, sq], '( p pCnt %s ) <_ 0' % VP, leaves={'( p pCnt v )': s5([s5([pp, vn5, w.inst('pccl')], 'syl2anc', '( p pCnt v ) e. NN0'), ], 'nn0red', '( p pCnt v ) e. RR'), '( p pCnt %s )' % VP: kr}, fast=False)
    keq = s5([kle, s5([kn0, w.inst('nn0le0eq0')], 'syl', '( ( p pCnt %s ) <_ 0 <-> ( p pCnt %s ) = 0 )' % (VP, VP))], 'mpbid', '( p pCnt %s ) = 0' % VP)
    npvp = s5([keq, s5([pp, vpn, w.inst('pceq0')], 'syl2anc', '( ( p pCnt %s ) = 0 <-> -. p || %s )' % (VP, VP))], 'mpbid', '-. p || %s' % VP)
    # -. u || ( v / p )
    imp = s5([pz, L5(uz), vpz, w.inst('dvdstr')], 'syl3anc', '( ( p || u /\\ u || %s ) -> p || %s )' % (VP, VP))
    imp2 = s5([pu, imp], 'mpand', '( u || %s -> p || %s )' % (VP, VP))
    nuvp = s5([npvp, imp2], 'mtod', '-. u || %s' % VP)
    # A. i e. T1 -. i || ( v / p )
    xst = s5([vn5, vpn, vpdv], '3jca', X)
    badt = s5([L5(vbad), s5([xst, itr], 'syl', '( A. i e. t -. i || v -> A. i e. t -. i || %s )' % VP)], 'mpd', 'A. i e. t -. i || %s' % VP)
    cgvpn, _ = wc(w, '-. i || %s' % VP, 'i', 'u')
    rusvp = w.s([w.s([], 'vex', 'u e. _V'), w.s([cgvpn], 'ralunsn', '( u e. _V -> ( A. i e. %s -. i || %s <-> ( A. i e. t -. i || %s /\\ -. u || %s ) ) )' % (T1, VP, VP, VP))], 'ax-mp', '( A. i e. %s -. i || %s <-> ( A. i e. t -. i || %s /\\ -. u || %s ) )' % (T1, VP, VP, VP))
    badB = s5([s5([badt, nuvp], 'jca', '( A. i e. t -. i || %s /\\ -. u || %s )' % (VP, VP)), rusvp], 'sylibr', 'A. i e. %s -. i || %s' % (T1, VP))
    cntB = s5([s5([L5(vcnt), half], 'jca', '( %s /\\ %s )' % (RA0, RB0)), s5([L5(y0), qB], 'syl', '( ( %s /\\ %s ) -> %s )' % (RA0, RB0, RB1))], 'mpd', RB1)
    bodyB = s5([vpdn, badB, cntB], '3jca', BODY(T1, VP))
    cgB, bB = w.wcongr(BODY(T1, 'w'), {'w': VP}, 'w = %s' % VP, {'w': id_eq(w, 'w', VP)})
    assert bB == BODY(T1, VP), bB
    exB = s5([vpn, bodyB, w.s([cgB], 'rspcev', '( ( %s e. NN /\\ %s ) -> %s )' % (VP, BODY(T1, VP), GOAL))], 'syl2anc', GOAL)
    exB2 = w.s([exp_, exB], 'rexlimddv', '( %s -> %s )' % (C4B, GOAL))
    both = w.s([exB2, exA], 'pm2.61dan', '( %s -> %s )' % (C3, GOAL))
    fin = w.s([exv, both], 'rexlimddv', '( %s -> %s )' % (C2, GOAL))
    i1 = w.s([fin], 'ex', '( %s -> %s )' % (C1, INST(T1)))
    i2 = w.s([i1], 'ex', '( ( %s /\\ n e. NN ) -> ( %s -> %s ) )' % (Y0, INST('t'), INST(T1)))
    w.qed([i2], 'ralimdva', S['bmredlem'])
    return go(w)


def gen_red():
    w = W('bmred', 'AGP (4.1), Lean ` exists_reduced_modulus ` : a squarefree ` L ` has a divisor ` w ` that no member of the finite exceptional set ` G ` (of moduli ` >_ 2 ` , at most ` J ` of them) divides, and whose divisor counts up to any ` y ` are within a factor ` 2 ^ J ` of those of ` L ` ; by induction on ` G ` (~ findcard2s , ~ bmred0 , ~ bmredlem ).')
    A = '( ( L e. NN /\\ ( mmu ` L ) =/= 0 ) /\\ ( G e. Fin /\\ A. i e. G 2 <_ i ) /\\ ( J e. NN0 /\\ ( # ` G ) <_ J ) )'
    s = S_(w, A)
    u = unpack(w, A)
    ln, lsf, gfin, ge2, jn0, hle = u['L e. NN'], u['( mmu ` L ) =/= 0'], u['G e. Fin'], u['A. i e. G 2 <_ i'], u['J e. NN0'], u['( # ` G ) <_ J']
    c1, _ = wc(w, PRED('s'), 's', '(/)')
    c2, _ = wc(w, PRED('s'), 's', 't')
    c3, _ = wc(w, PRED('s'), 's', '( t u. { u } )')
    c4, _ = wc(w, PRED('s'), 's', 'G')
    b = w.s([], 'bmred0', S['bmred0'])
    st = w.s([], 'bmredlem', S['bmredlem'])
    ind = w.s([c1, c2, c3, c4, b, st], 'findcard2s', '( G e. Fin -> %s )' % PRED('G'))
    pg = s([gfin, ind], 'syl', PRED('G'))
    HYP = '( ( mmu ` L ) =/= 0 /\\ A. i e. G 2 <_ i )'
    BODYG = lambda ww: '( %s || L /\\ A. i e. G -. i || %s /\\ A. y e. RR %s <_ ( ( 2 ^ ( # ` G ) ) x. %s ) )' % (ww, ww, CNT('L', 'y'), CNT(ww, 'y'))
    BODYJ = lambda ww: '( %s || L /\\ A. i e. G -. i || %s /\\ A. y e. RR %s <_ ( ( 2 ^ J ) x. %s ) )' % (ww, ww, CNT('L', 'y'), CNT(ww, 'y'))
    body_n = PRED('G')[len('A. n e. NN '):]
    inst, new = rspc(w, A, pg, 'n', 'L', body_n, ln)
    assert new == '( %s -> E. w e. NN %s )' % (HYP, BODYG('w')), new[:200]
    ex = s([s([lsf, ge2], 'jca', HYP), inst], 'mpd', 'E. w e. NN %s' % BODYG('w'))
    # ( ( A /\ w e. NN ) -> ( BODYG(w) -> BODYJ(w) ) )
    AW = '( %s /\\ w e. NN )' % A
    sw = S_(w, AW)
    AWY = '( %s /\\ y e. RR )' % AW
    swy = S_(w, AWY)
    cwr, cwg = cnt_real(w, AWY, 'w'); clr, clg = cnt_real(w, AWY, 'L')
    hg = swy([lift(w, gfin, AWY), w.inst('hashcl')], 'syl', '( # ` G ) e. NN0')
    uz = swy([swy([swy([hg], 'nn0zd', '( # ` G ) e. ZZ'), swy([lift(w, jn0, AWY)], 'nn0zd', 'J e. ZZ'), lift(w, hle, AWY)], '3jca', '( ( # ` G ) e. ZZ /\\ J e. ZZ /\\ ( # ` G ) <_ J )'), w.s([], 'eluz2', '( J e. ( ZZ>= ` ( # ` G ) ) <-> ( ( # ` G ) e. ZZ /\\ J e. ZZ /\\ ( # ` G ) <_ J ) )')], 'sylibr', 'J e. ( ZZ>= ` ( # ` G ) )')
    le2 = swy([swy([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), swy([w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2'), uz, w.inst('leexp2a')], 'syl3anc', '( 2 ^ ( # ` G ) ) <_ ( 2 ^ J )')
    PG = '( 2 ^ ( # ` G ) )'; PJ = '( 2 ^ J )'
    pgr = swy([swy([swy([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), hg, w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % PG)], 'nnred', '%s e. RR' % PG)
    pjr = swy([swy([swy([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), lift(w, jn0, AWY), w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % PJ)], 'nnred', '%s e. RR' % PJ)
    lm = swy([pgr, pjr, cwr, cwg, le2], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (PG, CNT('w', 'y'), PJ, CNT('w', 'y')))
    AWY2 = '( %s /\\ %s <_ ( %s x. %s ) )' % (AWY, CNT('L', 'y'), PG, CNT('w', 'y'))
    h = w.s([], 'simpr', '( %s -> %s <_ ( %s x. %s ) )' % (AWY2, CNT('L', 'y'), PG, CNT('w', 'y')))
    tr = w.s([lift(w, clr, AWY2), lift(w, swy([pgr, cwr], 'remulcld', '( %s x. %s ) e. RR' % (PG, CNT('w', 'y'))), AWY2), lift(w, swy([pjr, cwr], 'remulcld', '( %s x. %s ) e. RR' % (PJ, CNT('w', 'y'))), AWY2), h, lift(w, lm, AWY2)], 'letrd', '( %s -> %s <_ ( %s x. %s ) )' % (AWY2, CNT('L', 'y'), PJ, CNT('w', 'y')))
    tr2 = w.s([tr], 'ex', '( %s -> ( %s <_ ( %s x. %s ) -> %s <_ ( %s x. %s ) ) )' % (AWY, CNT('L', 'y'), PG, CNT('w', 'y'), CNT('L', 'y'), PJ, CNT('w', 'y')))
    R3 = w.s([tr2], 'ralimdva', '( %s -> ( A. y e. RR %s <_ ( %s x. %s ) -> A. y e. RR %s <_ ( %s x. %s ) ) )' % (AW, CNT('L', 'y'), PG, CNT('w', 'y'), CNT('L', 'y'), PJ, CNT('w', 'y')))
    i1 = sw([], 'idd', '( w || L -> w || L )'); i2 = sw([], 'idd', '( A. i e. G -. i || w -> A. i e. G -. i || w )')
    an = w.s([i1, i2, R3], '3anim123d', '( %s -> ( %s -> %s ) )' % (AW, BODYG('w'), BODYJ('w')))
    rx = w.s([an], 'reximdva', '( %s -> ( E. w e. NN %s -> E. w e. NN %s ) )' % (A, BODYG('w'), BODYJ('w')))
    w.qed([ex, rx], 'mpd', S['bmred'])
    return go(w)


ALL.update({'bmred0': gen_red0, 'bmredlem': gen_redlem, 'bmred': gen_red})

if __name__ == '__main__':
    for n in (only or list(ALL)):
        ALL[n]()
