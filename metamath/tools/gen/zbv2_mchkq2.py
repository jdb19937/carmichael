"""Sortie ZBV2, section 2 part B: the two inductions behind abs_mCheckQ_le
(ZBV2-blueprint.md section 3.1).

bvmchkqindlem  one step of the inner induction (the x / P case through the recursion)
bvmchkqindn    the inner induction (nn0indd on N with ( |_ ` y ) <_ N)
bvmchkqind     the bound for R = P Q from the bound for Q
bvmchkq1b      the bound for Q = 1 (bvmchks)
bvmchkqstep    the strong-induction step in Q (a prime factor P of Q, Q / P smaller)
bvmchkqall     nnsinds;  bvmchkq  the headline (Lean abs_mCheckQ_le)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *
from zbv2lib import ALLXU
from zbv2_mchkq import hsfacts, hpqfacts, bqfacts, dfacts_p, PS

PH = 'ph'


def rspcv_at(w, ante, body_var, body, T, memT, allst, rng='RR'):
    """from allst: ( ante -> A. var e. rng body ) and memT: ( ante -> T e. rng ):
    ( ante -> body[T/var] ) through the closed rspcv (no $d on ante); returns (step, new)"""
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (body_var, T, body_var, T))
    sub, new = w.wcongr(body, {body_var: T}, '%s = %s' % (body_var, T), {body_var: idk})
    rs = w.s([sub], 'rspcv', '( %s e. %s -> ( A. %s e. %s %s -> %s ) )' % (T, rng, body_var, rng, body, new))
    imp = w.s([rs], 'imp', '( ( %s e. %s /\\ A. %s e. %s %s ) -> %s )' % (T, rng, body_var, rng, body, new))
    return w.s([memT, allst, imp], 'syl2anc', '( %s -> %s )' % (ante, new)), new


ALLBODY = lambda q, v: '( 1 <_ %s -> ( abs ` %s ) <_ %s )' % (v, MCQ(q, v), BQ(q, v))
PSIBODY = lambda q, m, v: '( ( 1 <_ %s /\\ ( |_ ` %s ) <_ %s ) -> ( abs ` %s ) <_ %s )' % (v, v, m, MCQ(q, v), BQ(q, v))


def bvmchkqindlem():
    w = W('bvmchkqindlem', 'One step of the inner induction of abs_mCheckQ_le: from the bound for Q at X and for '
                           'R = P Q at every x with |_ x <= N, the bound for R at X with |_ X <= N + 1, through the '
                           'recursion bvmchkqrec, P ^c -u S <= 1 / P and the totient ratio.')
    h1, h2, h3, h4, h5, h6, h7 = hyps_of(w, 'bvmchkqindlem')
    st = mkst(w, PH)
    h = hsfacts(w, PH, h1); f = hpqfacts(w, PH, h2)
    xr = st([h7], 'simp1d', 'X e. RR'); x1 = st([h7], 'simp2d', '1 <_ X'); xfl = st([h7], 'simp3d', '( |_ ` X ) <_ ( N + 1 )')
    x0 = linarith(w, PH, [x1], '0 <_ X', leaves={'X': xr})
    xrp = st([xr, linarith(w, PH, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+'); xc = st([xr], 'recnd', 'X e. CC')
    XP = '( X / P )'
    xpr = st([xr, f['pre'], f['pne']], 'redivcld', '%s e. RR' % XP); xprp = st([xrp, f['prp']], 'rpdivcld', '%s e. RR+' % XP)
    rnn = st([h3, f['pqnn']], 'eqeltrd', 'R e. NN')
    nre = st([h5], 'nn0red', 'N e. RR'); nz = st([h5], 'nn0zd', 'N e. ZZ')
    n1nn = sy(w, PH, h5, 'nn0p1nn', '( N + 1 ) e. NN'); n1re = st([n1nn], 'nnred', '( N + 1 ) e. RR'); n1rp = st([n1nn], 'nnrpd', '( N + 1 ) e. RR+')
    # the recursion, in R
    rec = st([bind(w, PH, bind(w, PH, h['sr'], xr, 'S e. RR', 'X e. RR'), h2, '( S e. RR /\\ X e. RR )', HPQ), w.inst('bvmchkqrec')], 'syl',
             '%s = ( %s - ( %s x. %s ) )' % (MCQ('Q', 'X'), MCQ(PQ, 'X'), PS, MCQ(PQ, XP)))
    a, b, c, bp, cp = MCQ('Q', 'X'), MCQ('R', 'X'), MCQ('R', XP), MCQ(PQ, 'X'), MCQ(PQ, XP)
    mrx = st([h3], 'oveq1d', '%s = %s' % (b, bp)); mrxp = st([h3], 'oveq1d', '%s = %s' % (c, cp))
    ar = st([h['sr'], f['qnn'], xr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % a)
    br = st([mrx, st([h['sr'], f['pqnn'], xr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % bp)], 'eqeltrd', '%s e. RR' % b)
    cr = st([mrxp, st([h['sr'], f['pqnn'], xpr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % cp)], 'eqeltrd', '%s e. RR' % c)
    psrp = st([f['prp'], h['nsr']], 'rpcxpcld', '%s e. RR+' % PS); psr = st([psrp], 'rpred', '%s e. RR' % PS); ps0 = st([psrp], 'rpge0d', '0 <_ %s' % PS); psc = st([psr], 'recnd', '%s e. CC' % PS)
    PSC = '( %s x. %s )' % (PS, c)
    rec2 = st([rec, st([st([mrx], 'eqcomd', '%s = %s' % (bp, b)), st([st([mrxp], 'eqcomd', '%s = %s' % (cp, c))], 'oveq2d', '( %s x. %s ) = %s' % (PS, cp, PSC))], 'oveq12d',
                        '( %s - ( %s x. %s ) ) = ( %s - %s )' % (bp, PS, cp, b, PSC))], 'eqtrd', '%s = ( %s - %s )' % (a, b, PSC))
    pscr = st([psr, cr], 'remulcld', '%s e. RR' % PSC)
    beq = lineq(w, PH, b, '( %s + %s )' % (a, PSC), hyps=[rec2], leaves={a: ar, b: br, PSC: pscr})
    # |a| <= BQ(Q,X)
    b1i, _ = rspcv_at(w, PH, 'u', ALLBODY('Q', 'u'), 'X', xr, h4)
    b1 = st([x1, b1i], 'mpd', '( abs ` %s ) <_ %s' % (a, BQ('Q', 'X')))
    # |c| <= BQ(R,X)
    BQRX = BQ('R', 'X')
    bq0 = st([bind(w, PH, h1, bind(w, PH, rnn, bind(w, PH, xr, x1, 'X e. RR', '1 <_ X'), 'R e. NN', '( X e. RR /\\ 1 <_ X )'), HS, '( R e. NN /\\ ( X e. RR /\\ 1 <_ X ) )'), w.inst('bvmchkqbq0')], 'syl', '0 <_ %s' % BQRX)
    A1 = '( ph /\\ %s < 1 )' % XP
    s1 = mkst(w, A1)
    c0 = w.s([bind3(w, A1, lift(w, h['sr'], A1), lift(w, rnn, A1), bind(w, A1, lift(w, xpr, A1), s1([], 'simpr', '%s < 1' % XP), '%s e. RR' % XP, '%s < 1' % XP), 'S e. RR', 'R e. NN', '( %s e. RR /\\ %s < 1 )' % (XP, XP)), w.inst('bvmchkq0')], 'syl',
            '( %s -> %s = 0 )' % (A1, c))
    ca1 = s1([s1([s1([c0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % c), s1([clo(w, 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % c), lift(w, bq0, A1)], 'eqbrtrd', '( abs ` %s ) <_ %s' % (c, BQRX))
    A2 = '( ph /\\ 1 <_ %s )' % XP
    s2 = mkst(w, A2)
    xp1 = s2([], 'simpr', '1 <_ %s' % XP)
    fld = st([st([xr, f['pnn'], w.inst('fldiv')], 'syl2anc', '( |_ ` ( ( |_ ` X ) / P ) ) = ( |_ ` %s )' % XP)], 'eqcomd', '( |_ ` %s ) = ( |_ ` ( ( |_ ` X ) / P ) )' % XP)
    flx0 = sy2(w, PH, xr, x0, 'flge0nn0', '( |_ ` X ) e. NN0'); flxr = st([flx0], 'nn0red', '( |_ ` X ) e. RR')
    fle = st([fld, sy2(w, PH, flx0, f['pnn'], 'fldivnn0le', '( |_ ` ( ( |_ ` X ) / P ) ) <_ ( ( |_ ` X ) / P )')], 'eqbrtrd', '( |_ ` %s ) <_ ( ( |_ ` X ) / P )' % XP)
    d1 = st([flxr, n1re, f['prp'], xfl], 'lediv1dd', '( ( |_ ` X ) / P ) <_ ( ( N + 1 ) / P )')
    d2 = st([f['p2'], st([st([clo(w, '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), f['prp'], n1rp], 'lediv2d', '( 2 <_ P <-> ( ( N + 1 ) / P ) <_ ( ( N + 1 ) / 2 ) )')], 'mpbid', '( ( N + 1 ) / P ) <_ ( ( N + 1 ) / 2 )')
    flxpr = sy(w, PH, xpr, 'reflcl', '( |_ ` %s ) e. RR' % XP)
    n0 = st([h5], 'nn0ge0d', '0 <_ N')
    ltn1 = linarith(w, PH, [fle, d1, d2, n0], '( |_ ` %s ) < ( N + 1 )' % XP,
                    leaves={'( |_ ` %s )' % XP: flxpr, '( ( |_ ` X ) / P )': st([flxr, f['prp']], 'rerpdivcld', '( ( |_ ` X ) / P ) e. RR'), '( ( N + 1 ) / P )': st([n1re, f['prp']], 'rerpdivcld', '( ( N + 1 ) / P ) e. RR'), 'N': nre})
    fln = st([ltn1, sy2(w, PH, sy(w, PH, xpr, 'flcl', '( |_ ` %s ) e. ZZ' % XP), nz, 'zleltp1', '( ( |_ ` %s ) <_ N <-> ( |_ ` %s ) < ( N + 1 ) )' % (XP, XP))], 'mpbird', '( |_ ` %s ) <_ N' % XP)
    psi_i, _ = rspcv_at(w, PH, 'v', PSIBODY('R', 'N', 'v'), XP, xpr, h6)
    c_le = s2([bind(w, A2, xp1, lift(w, fln, A2), '1 <_ %s' % XP, '( |_ ` %s ) <_ N' % XP), lift(w, psi_i, A2)], 'mpd', '( abs ` %s ) <_ %s' % (c, BQ('R', XP)))
    one = st([], '1red', '1 e. RR')
    xpxm = st([st([st([xc], 'mullidd', '( 1 x. X ) = X')], 'eqcomd', 'X = ( 1 x. X )'),
               st([one, f['pre'], xr, x0, st([one, f['pre'], f['p1']], 'ltled', '1 <_ P')], 'lemul1ad', '( 1 x. X ) <_ ( P x. X )')], 'eqbrtrd', 'X <_ ( P x. X )')
    xpx = st([xpxm, st([xr, xr, f['prp']], 'ledivmuld', '( %s <_ X <-> X <_ ( P x. X ) )' % XP)], 'mpbird', '%s <_ X' % XP)
    HXZ = '( ( X e. RR /\\ 1 <_ X ) /\\ ( %s e. RR /\\ 1 <_ %s /\\ %s <_ X ) )' % (XP, XP, XP)
    mono = w.s([bind(w, A2, lift(w, h1, A2), bind(w, A2, lift(w, rnn, A2), bind(w, A2, bind(w, A2, lift(w, xr, A2), lift(w, x1, A2), 'X e. RR', '1 <_ X'),
                                                                                     bind3(w, A2, lift(w, xpr, A2), xp1, lift(w, xpx, A2), '%s e. RR' % XP, '1 <_ %s' % XP, '%s <_ X' % XP),
                                                                                     '( X e. RR /\\ 1 <_ X )', '( %s e. RR /\\ 1 <_ %s /\\ %s <_ X )' % (XP, XP, XP)),
                                                     'R e. NN', HXZ), HS, '( R e. NN /\\ %s )' % HXZ), w.inst('bvmchkqbqle')], 'syl', '( %s -> %s <_ %s )' % (A2, BQ('R', XP), BQRX))
    # closures of BQ(R,X), BQ(R,XP), BQ(Q,X)
    rateq = st([st([h3, st([h3], 'fveq2d', '( phi ` R ) = ( phi ` %s )' % PQ)], 'oveq12d', '%s = %s' % (RAT('R'), RAT(PQ))), sy(w, PH, h2, 'bvmchkqrat', '%s = ( ( P / ( P - 1 ) ) x. %s )' % (RAT(PQ), RAT('Q')))], 'eqtrd',
                '%s = ( ( P / ( P - 1 ) ) x. %s )' % (RAT('R'), RAT('Q')))
    bQ = bqfacts(w, PH, h1, f['qnn'], xr, x1)
    Z0 = BQ('Q', 'X'); L = bQ['L']; r = RAT('Q'); C0 = '( P / ( P - 1 ) )'
    d = dfacts_p(w, PH, f)
    c0r = st([f['pre'], d['rp']], 'rerpdivcld', '%s e. RR' % C0); c0c = st([c0r], 'recnd', '%s e. CC' % C0)
    z0r = st([bQ['rmre'], bQ['lre']], 'remulcld', '%s e. RR' % Z0); z0c = st([z0r], 'recnd', '%s e. CC' % Z0)
    rc = st([bQ['ratre']], 'recnd', '%s e. CC' % r); mc = st([Closure(w, PH).mem(M113, 'RR')], 'recnd', '%s e. CC' % M113); lc = st([bQ['lre']], 'recnd', '%s e. CC' % L)
    RM = '( %s x. %s )' % (r, M113)
    bqeq = eqtr(w, PH, [st([st([rateq], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (RAT('R'), M113, C0, r, M113))], 'oveq1d', '%s = ( ( ( %s x. %s ) x. %s ) x. %s )' % (BQRX, C0, r, M113, L)),
                        st([st([c0c, rc, mc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (C0, r, M113, C0, RM))], 'oveq1d', '( ( ( %s x. %s ) x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (C0, r, M113, L, C0, RM, L)),
                        st([c0c, st([rc, mc], 'mulcld', '%s e. CC' % RM), lc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (C0, RM, L, C0, Z0))], None)
    bqrxr = st([bqeq, st([c0r, z0r], 'remulcld', '( %s x. %s ) e. RR' % (C0, Z0))], 'eqeltrd', '%s e. RR' % BQRX)
    U = '( 1 / P )'
    ur = st([f['prp']], 'rprecred', '%s e. RR' % U); uc = st([ur], 'recnd', '%s e. CC' % U)
    UB = '( %s x. %s )' % (U, BQRX)
    ubeq = eqtr(w, PH, [st([bqeq], 'oveq2d', '%s = ( %s x. ( %s x. %s ) )' % (UB, U, C0, Z0)), st([st([uc, c0c, z0c], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (U, C0, Z0, U, C0, Z0))], 'eqcomd', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (U, C0, Z0, U, C0, Z0))], None)
    ucc = st([uc, c0c], 'mulcld', '( %s x. %s ) e. CC' % (U, C0))
    ratlem = sy2(w, PH, f['pre'], f['p1'], 'bvmchkqratlem', '( 1 + ( %s x. %s ) ) = %s' % (U, C0, C0))
    sumeq = eqtr(w, PH, [st([ubeq], 'oveq2d', '( %s + %s ) = ( %s + ( ( %s x. %s ) x. %s ) )' % (Z0, UB, Z0, U, C0, Z0)),
                         st([st([st([z0c], 'mullidd', '( 1 x. %s ) = %s' % (Z0, Z0))], 'eqcomd', '%s = ( 1 x. %s )' % (Z0, Z0))], 'oveq1d', '( %s + ( ( %s x. %s ) x. %s ) ) = ( ( 1 x. %s ) + ( ( %s x. %s ) x. %s ) )' % (Z0, U, C0, Z0, Z0, U, C0, Z0)),
                         st([st([st([], '1cnd', '1 e. CC'), ucc, z0c], 'adddird', '( ( 1 + ( %s x. %s ) ) x. %s ) = ( ( 1 x. %s ) + ( ( %s x. %s ) x. %s ) )' % (U, C0, Z0, Z0, U, C0, Z0))], 'eqcomd', '( ( 1 x. %s ) + ( ( %s x. %s ) x. %s ) ) = ( ( 1 + ( %s x. %s ) ) x. %s )' % (Z0, U, C0, Z0, U, C0, Z0)),
                         st([ratlem], 'oveq1d', '( ( 1 + ( %s x. %s ) ) x. %s ) = ( %s x. %s )' % (U, C0, Z0, C0, Z0)), st([bqeq], 'eqcomd', '( %s x. %s ) = %s' % (C0, Z0, BQRX))], None)
    # the case split for |c|
    disj = sy2(w, PH, one, xpr, 'lelttric', '( 1 <_ %s \\/ %s < 1 )' % (XP, XP))
    # BQ(R,XP) real: from bvmchkqbq0-style closures: use bqeq-like route through bqfacts at X := XP under A2
    bXP = bqfacts(w, A2, lift(w, h1, A2), lift(w, rnn, A2), lift(w, xpr, A2), xp1, q='R', x=XP)
    ca2 = s2([s2([s2([lift(w, cr, A2)], 'recnd', '%s e. CC' % c)], 'abscld', '( abs ` %s ) e. RR' % c), bXP['bqre'], lift(w, bqrxr, A2), c_le, mono], 'letrd', '( abs ` %s ) <_ %s' % (c, BQRX))
    b2 = st([ca2, ca1, disj], 'mpjaodan', '( abs ` %s ) <_ %s' % (c, BQRX))
    # P ^c -u S <= 1 / P
    ns1 = st([h['s1'], st([one, h['sr']], 'lenegd', '( 1 <_ S <-> -u S <_ -u 1 )')], 'mpbid', '-u S <_ -u 1')
    m1r = st([one], 'renegcld', '-u 1 e. RR')
    cxle = st([f['pre'], st([one, f['pre'], f['p1']], 'ltled', '1 <_ P'), h['nsr'], m1r, ns1], 'cxplead', '%s <_ ( P ^c -u 1 )' % PS)
    p1eq = st([st([f['pcc'], f['pne'], st([], '1cnd', '1 e. CC')], 'cxpnegd', '( P ^c -u 1 ) = ( 1 / ( P ^c 1 ) )'), st([st([f['pcc']], 'cxp1d', '( P ^c 1 ) = P')], 'oveq2d', '( 1 / ( P ^c 1 ) ) = %s' % U)], 'eqtrd', '( P ^c -u 1 ) = %s' % U)
    psle = st([cxle, p1eq], 'breqtrd', '%s <_ %s' % (PS, U))
    # the triangle
    ac = st([ar], 'recnd', '%s e. CC' % a); cc = st([cr], 'recnd', '%s e. CC' % c); pscc = st([psc, cc], 'mulcld', '%s e. CC' % PSC)
    tri = st([st([beq], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s + %s ) )' % (b, a, PSC)), sy2(w, PH, ac, pscc, 'abstri', '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (a, PSC, a, PSC))], 'eqbrtrd',
             '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (b, a, PSC))
    apc = st([st([psc, cc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PSC, PS, c)), st([st([psr, ps0], 'absidd', '( abs ` %s ) = %s' % (PS, PS))], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (PS, c, PS, c))], 'eqtrd',
             '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (PSC, PS, c))
    acr = st([cc], 'abscld', '( abs ` %s ) e. RR' % c)
    m = st([psr, ur, acr, bqrxr, ps0, st([cc], 'absge0d', '0 <_ ( abs ` %s )' % c), psle, b2], 'lemul12ad', '( %s x. ( abs ` %s ) ) <_ %s' % (PS, c, UB))
    m2 = st([apc, m], 'eqbrtrd', '( abs ` %s ) <_ %s' % (PSC, UB))
    aar = st([ac], 'abscld', '( abs ` %s ) e. RR' % a); apscr = st([pscc], 'abscld', '( abs ` %s ) e. RR' % PSC); ubr = st([ur, bqrxr], 'remulcld', '%s e. RR' % UB)
    s_a = st([aar, apscr, z0r, ubr, b1, m2], 'le2addd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + %s )' % (a, PSC, Z0, UB))
    abr = st([st([br], 'recnd', '%s e. CC' % b)], 'abscld', '( abs ` %s ) e. RR' % b)
    fin = st([abr, st([aar, apscr], 'readdcld', '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (a, PSC)), st([z0r, ubr], 'readdcld', '( %s + %s ) e. RR' % (Z0, UB)), tri, s_a], 'letrd',
             '( abs ` %s ) <_ ( %s + %s )' % (b, Z0, UB))
    w.qed([fin, sumeq], 'breqtrd', STATEMENTS['bvmchkqindlem'])
    return w


def bvmchkqindn():
    w = W('bvmchkqindn', 'The inner induction of abs_mCheckQ_le: for every N e. NN0 the bound for R = P Q holds at all '
                         'y >= 1 with |_ y <= N (nn0indd on bvmchkqindlem).')
    h1, h2, h3, h4 = hyps_of(w, 'bvmchkqindn')
    st = mkst(w, PH)
    PSIK = PSI('R', 'k')
    idk = w.s([], 'id', '( k = 0 -> k = 0 )'); n1, p0 = w.wcongr(PSIK, {'k': '0'}, 'k = 0', {'k': idk})
    idj = w.s([], 'id', '( k = j -> k = j )'); n2, pj = w.wcongr(PSIK, {'k': 'j'}, 'k = j', {'k': idj})
    idj1 = w.s([], 'id', '( k = ( j + 1 ) -> k = ( j + 1 ) )'); n3, pj1 = w.wcongr(PSIK, {'k': '( j + 1 )'}, 'k = ( j + 1 )', {'k': idj1})
    idN = w.s([], 'id', '( k = N -> k = N )'); n4, pN = w.wcongr(PSIK, {'k': 'N'}, 'k = N', {'k': idN})
    assert p0 == PSI('R', '0') and pj == PSI('R', 'j') and pj1 == PSI('R', '( j + 1 )') and pN == PSI('R', 'N')
    # base: PSI(R,0) vacuously
    B1 = '( ph /\\ v e. RR )'; B2 = '( %s /\\ ( 1 <_ v /\\ ( |_ ` v ) <_ 0 ) )' % B1
    sb = mkst(w, B2)
    yr = sb([], 'simplr', 'v e. RR'); y1 = sb([], 'simprl', '1 <_ v'); fl0 = sb([], 'simprr', '( |_ ` v ) <_ 0')
    fl1 = sb([y1, sy2(w, B2, yr, sb([clo(w, '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), 'flge', '( 1 <_ v <-> 1 <_ ( |_ ` v ) )')], 'mpbid', '1 <_ ( |_ ` v )')
    le10 = sb([sb([], '1red', '1 e. RR'), sy(w, B2, yr, 'reflcl', '( |_ ` v ) e. RR'), sb([], '0red', '0 e. RR'), fl1, fl0], 'letrd', '1 <_ 0')
    nle = sb([w.s([w.s([], '0lt1', '0 < 1'), w.s([w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR'), w.inst('ltnle')], 'mp2an', '( 0 < 1 <-> -. 1 <_ 0 )')], 'mpbi', '-. 1 <_ 0')], 'a1i', '-. 1 <_ 0')
    bnd0 = sb([le10, nle], 'pm2.21dd', '( abs ` %s ) <_ %s' % (MCQ('R', 'v'), BQ('R', 'v')))
    base = w.s([w.s([bnd0], 'ex', '( %s -> %s )' % (B1, PSIBODY('R', '0', 'v')))], 'ralrimiva', '( ph -> %s )' % p0)
    # step
    B0 = '( ( ph /\\ j e. NN0 ) /\\ %s )' % pj
    BZ = '( %s /\\ t e. RR )' % B0; BZ2 = '( %s /\\ ( 1 <_ t /\\ ( |_ ` t ) <_ ( j + 1 ) ) )' % BZ
    sz = mkst(w, BZ2)
    zr = sz([], 'simplr', 't e. RR'); z1 = sz([], 'simprl', '1 <_ t'); zfl = sz([], 'simprr', '( |_ ` t ) <_ ( j + 1 )')
    jnn0 = lift(w, w.s([], 'simpr', '( ( ph /\\ j e. NN0 ) -> j e. NN0 )'), BZ2)
    ih = lift(w, w.s([], 'simpr', '( %s -> %s )' % (B0, pj)), BZ2)
    hx = sz([zr, z1, zfl], '3jca', '( t e. RR /\\ 1 <_ t /\\ ( |_ ` t ) <_ ( j + 1 ) )')
    lem = w.s([lift(w, h1, BZ2), lift(w, h2, BZ2), lift(w, h3, BZ2), lift(w, h4, BZ2), jnn0, ih, hx], 'bvmchkqindlem', '( %s -> ( abs ` %s ) <_ %s )' % (BZ2, MCQ('R', 't'), BQ('R', 't')))
    allz = w.s([w.s([lem], 'ex', '( %s -> %s )' % (BZ, PSIBODY('R', '( j + 1 )', 't')))], 'ralrimiva', '( %s -> A. t e. RR %s )' % (B0, PSIBODY('R', '( j + 1 )', 't')))
    idz = w.s([], 'id', '( t = v -> t = v )'); cb, body_y = w.wcongr(PSIBODY('R', '( j + 1 )', 't'), {'t': 'v'}, 't = v', {'t': idz})
    assert body_y == PSIBODY('R', '( j + 1 )', 'v')
    cbv = w.s([cb], 'cbvralvw', '( A. t e. RR %s <-> %s )' % (PSIBODY('R', '( j + 1 )', 't'), pj1))
    step = w.s([allz, cbv], 'sylib', '( %s -> %s )' % (B0, pj1))
    w.qed([n1, n2, n3, n4, base, step], 'nn0indd', STATEMENTS['bvmchkqindn'])
    return w


def bvmchkqind():
    w = W('bvmchkqind', 'The bound for R = P Q from the bound for Q (bvmchkqindn at N = |_ u).')
    h1, h2, h3, h4 = hyps_of(w, 'bvmchkqind')
    st = mkst(w, PH)
    PX = '( ph /\\ u e. RR )'; PX1 = '( %s /\\ 1 <_ u )' % PX
    sx = mkst(w, PX1)
    xr = sx([], 'simplr', 'u e. RR'); x1 = sx([], 'simpr', '1 <_ u')
    fl0 = sy2(w, PX1, xr, linarith(w, PX1, [x1], '0 <_ u', leaves={'u': xr}), 'flge0nn0', '( |_ ` u ) e. NN0')
    indn = w.s([h1, h2, h3, h4], 'bvmchkqindn', '( ( ph /\\ ( |_ ` u ) e. NN0 ) -> %s )' % PSI('R', '( |_ ` u )'))
    psi = sx([bind(w, PX1, sx([], 'simpll', 'ph'), fl0, 'ph', '( |_ ` u ) e. NN0'), indn], 'syl', PSI('R', '( |_ ` u )'))
    inst, body = rspcv_at(w, PX1, 'v', PSIBODY('R', '( |_ ` u )', 'v'), 'u', xr, psi)
    assert body == PSIBODY('R', '( |_ ` u )', 'u'), body
    fle = sx([sy(w, PX1, xr, 'reflcl', '( |_ ` u ) e. RR')], 'leidd', '( |_ ` u ) <_ ( |_ ` u )')
    bnd = sx([bind(w, PX1, x1, fle, '1 <_ u', '( |_ ` u ) <_ ( |_ ` u )'), inst], 'mpd', '( abs ` %s ) <_ %s' % (MCQ('R', 'u'), BQ('R', 'u')))
    w.qed([w.s([bnd], 'ex', '( %s -> %s )' % (PX, ALLBODY('R', 'u')))], 'ralrimiva', STATEMENTS['bvmchkqind'])
    return w


def bvmchkq1b():
    w = W('bvmchkq1b', 'The bound of abs_mCheckQ_le at Q = 1 is bvmchks (phi 1 = 1).')
    A = '( %s /\\ x e. RR )' % HS; A1 = '( %s /\\ 1 <_ x )' % A
    s1 = mkst(w, A1)
    hs = s1([], 'simpll', HS); xr = s1([], 'simplr', 'x e. RR'); x1 = s1([], 'simpr', '1 <_ x')
    h = hsfacts(w, A1, hs)
    v = s1([bind(w, A1, h['sr'], xr, 'S e. RR', 'x e. RR'), w.inst('bvmchkq1')], 'syl', '%s = sum_ n e. ( 1 ... ( |_ ` x ) ) %s' % (MCQ('1', 'x'), TERMX('n', 'x')))
    SUMX = 'sum_ n e. ( 1 ... ( |_ ` x ) ) %s' % TERMX('n', 'x')
    L = '( 1 + ( %s x. ( log ` x ) ) )' % E
    chk = s1([bind(w, A1, bind(w, A1, xr, x1, 'x e. RR', '1 <_ x'), hs, '( x e. RR /\\ 1 <_ x )', HS), w.inst('bvmchks')], 'syl', '( abs ` %s ) <_ ( %s x. %s )' % (SUMX, M113, L))
    bq = eqtr(w, A1, [s1([s1([s1([s1([clo(w, 'phi1', '( phi ` 1 ) = 1')], 'a1i', '( phi ` 1 ) = 1')], 'oveq2d', '( 1 / ( phi ` 1 ) ) = ( 1 / 1 )'), s1([clo(w, '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')], 'eqtrd', '%s = 1' % RAT('1'))], 'oveq1d', '( %s x. %s ) = ( 1 x. %s )' % (RAT('1'), M113, M113)),
                      s1([s1([Closure(w, A1).mem(M113, 'RR')], 'recnd', '%s e. CC' % M113)], 'mullidd', '( 1 x. %s ) = %s' % (M113, M113))], None)
    bq2 = s1([bq], 'oveq1d', '%s = ( %s x. %s )' % (BQ('1', 'x'), M113, L))
    bnd = s1([s1([s1([v], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (MCQ('1', 'x'), SUMX)), chk], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (MCQ('1', 'x'), M113, L)), bq2], 'breqtrrd', '( abs ` %s ) <_ %s' % (MCQ('1', 'x'), BQ('1', 'x')))
    w.qed([w.s([bnd], 'ex', '( %s -> %s )' % (A, ALLBODY('1', 'x')))], 'ralrimiva', STATEMENTS['bvmchkq1b'])
    return w


def bvmchkqstep():
    w = W('bvmchkqstep', 'The strong-induction step of abs_mCheckQ_le in Q: Q = 1 is bvmchkq1b; for Q >= 2 a prime '
                         'P || Q (exprmfct) gives Q = P ( Q / P ) with ( P gcd ( Q / P ) ) = 1 (Q squarefree), the '
                         'hypothesis at Q / P < Q, and bvmchkqind.')
    A0 = '( ( %s /\\ Q e. NN ) /\\ A. y e. ( 1 ... ( Q - 1 ) ) %s )' % (HS, PHIQ('y'))
    A1 = '( %s /\\ ( mmu ` Q ) =/= 0 )' % A0
    s = mkst(w, A1)
    hs = s([], 'simplll', HS); qnn = s([], 'simpllr', 'Q e. NN'); ih = s([], 'simplr', 'A. y e. ( 1 ... ( Q - 1 ) ) %s' % PHIQ('y')); mu = s([], 'simpr', '( mmu ` Q ) =/= 0')
    qz = s([qnn], 'nnzd', 'Q e. ZZ'); qre = s([qnn], 'nnred', 'Q e. RR'); qcc = s([qnn], 'nncnd', 'Q e. CC')
    # case Q = 1
    C1 = '( %s /\\ Q = 1 )' % A1
    c1s = mkst(w, C1)
    q1 = c1s([], 'simpr', 'Q = 1')
    all1 = sy(w, C1, lift(w, hs, C1), 'bvmchkq1b', ALLX('1'))
    idq = w.s([], 'id', '( Q = 1 -> Q = 1 )'); cg, allq1 = w.wcongr(ALLX('Q'), {'Q': '1'}, 'Q = 1', {'Q': idq})
    assert allq1 == ALLX('1'), allq1
    c1 = c1s([all1, c1s([q1, cg], 'syl', '( %s <-> %s )' % (ALLX('Q'), ALLX('1')))], 'mpbird', ALLX('Q'))
    # case Q >= 2
    C2 = '( %s /\\ Q e. ( ZZ>= ` 2 ) )' % A1
    c2s = mkst(w, C2)
    qu = c2s([], 'simpr', 'Q e. ( ZZ>= ` 2 )')
    ex = sy(w, C2, qu, 'exprmfct', 'E. p e. Prime p || Q')
    C3 = '( ( %s /\\ p e. Prime ) /\\ p || Q )' % C2
    c3 = mkst(w, C3)
    pp = c3([], 'simplr', 'p e. Prime'); pdq = c3([], 'simpr', 'p || Q')
    pnn = sy(w, C3, pp, 'prmnn', 'p e. NN'); pz = c3([pnn], 'nnzd', 'p e. ZZ'); pcc = c3([pnn], 'nncnd', 'p e. CC'); pre = c3([pnn], 'nnred', 'p e. RR')
    pne = c3([c3([pnn], 'nnrpd', 'p e. RR+')], 'rpne0d', 'p =/= 0'); p2 = sy(w, C3, sy(w, C3, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), 'eluzle', '2 <_ p')
    puz = sy(w, C3, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )')
    qnn3 = lift(w, qnn, C3); qz3 = lift(w, qz, C3); qre3 = lift(w, qre, C3); qcc3 = lift(w, qcc, C3); mu3 = lift(w, mu, C3); hs3 = lift(w, hs, C3)
    QP = '( Q / p )'
    qpnn = c3([pdq, sy2(w, C3, qnn3, pnn, 'nndivdvds', '( p || Q <-> %s e. NN )' % QP)], 'mpbid', '%s e. NN' % QP)
    qpz = c3([qpnn], 'nnzd', '%s e. ZZ' % QP); qpre = c3([qpnn], 'nnred', '%s e. RR' % QP)
    qeq = c3([c3([qcc3, pcc, pne], 'divcan2d', '( p x. %s ) = Q' % QP)], 'eqcomd', 'Q = ( p x. %s )' % QP)
    # -. p || ( Q / p )
    cm = w.s([bind3(w, C3, pz, qpz, pz, 'p e. ZZ', '%s e. ZZ' % QP, 'p e. ZZ'), w.inst('dvdscmul')], 'syl', '( %s -> ( p || %s -> ( p x. p ) || ( p x. %s ) ) )' % (C3, QP, QP))
    sq = c3([pcc], 'sqvald', '( p ^ 2 ) = ( p x. p )')
    b12 = c3([sq, qeq], 'breq12d', '( ( p ^ 2 ) || Q <-> ( p x. p ) || ( p x. %s ) )' % QP)
    im1 = w.s([cm, b12], 'sylibrd', '( %s -> ( p || %s -> ( p ^ 2 ) || Q ) )' % (C3, QP))
    mv = w.s([w.inst('muval1')], '3expia', '( ( Q e. NN /\\ p e. ( ZZ>= ` 2 ) ) -> ( ( p ^ 2 ) || Q -> ( mmu ` Q ) = 0 ) )')
    mvd = c3([c3([qnn3, puz], 'jca', '( Q e. NN /\\ p e. ( ZZ>= ` 2 ) )'), mv], 'syl', '( ( p ^ 2 ) || Q -> ( mmu ` Q ) = 0 )')
    im2 = w.s([im1, mvd], 'syld', '( %s -> ( p || %s -> ( mmu ` Q ) = 0 ) )' % (C3, QP))
    npq = c3([c3([mu3], 'neneqd', '-. ( mmu ` Q ) = 0'), im2], 'mtod', '-. p || %s' % QP)
    gcd = c3([npq, sy2(w, C3, pp, qpz, 'coprm', '( -. p || %s <-> ( p gcd %s ) = 1 )' % (QP, QP))], 'mpbid', '( p gcd %s ) = 1' % QP)
    # mmu ( Q / p ) =/= 0
    dq = c3([sy2(w, C3, pz, qpz, 'dvdsmul2', '%s || ( p x. %s )' % (QP, QP)), c3([qeq], 'eqcomd', '( p x. %s ) = Q' % QP)], 'breqtrd', '%s || Q' % QP)
    muq = c3([mu3, w.s([bind3(w, C3, qnn3, qpnn, dq, 'Q e. NN', '%s e. NN' % QP, '%s || Q' % QP), w.inst('dvdssqf')], 'syl', '( %s -> ( ( mmu ` Q ) =/= 0 -> ( mmu ` %s ) =/= 0 ) )' % (C3, QP))], 'mpd', '( mmu ` %s ) =/= 0' % QP)
    # ( Q / p ) e. ( 1 ... ( Q - 1 ) )
    two = c3([c3([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), pre, qpre, c3([c3([qpnn], 'nnrpd', '%s e. RR+' % QP)], 'rpge0d', '0 <_ %s' % QP), p2], 'lemul1ad', '( 2 x. %s ) <_ ( p x. %s )' % (QP, QP))
    two2 = c3([two, c3([qeq], 'eqcomd', '( p x. %s ) = Q' % QP)], 'breqtrd', '( 2 x. %s ) <_ Q' % QP)
    qp1 = sy(w, C3, qpnn, 'nnge1', '1 <_ %s' % QP)
    lt = linarith(w, C3, [two2, qp1], '%s < Q' % QP, leaves={QP: qpre, 'Q': qre3})
    le = c3([lt, sy2(w, C3, qpz, qz3, 'zltp1le', '( %s < Q <-> ( %s + 1 ) <_ Q )' % (QP, QP))], 'mpbid', '( %s + 1 ) <_ Q' % QP)
    le2 = linarith(w, C3, [le], '%s <_ ( Q - 1 )' % QP, leaves={QP: qpre, 'Q': qre3})
    qm1z = sy(w, C3, qz3, 'peano2zm', '( Q - 1 ) e. ZZ')
    mem = c3([bind(w, C3, qp1, le2, '1 <_ %s' % QP, '%s <_ ( Q - 1 )' % QP), st3 := w.s([bind3(w, C3, qpz, c3([clo(w, '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), qm1z, '%s e. ZZ' % QP, '1 e. ZZ', '( Q - 1 ) e. ZZ'), w.inst('elfz')], 'syl', '( %s -> ( %s e. ( 1 ... ( Q - 1 ) ) <-> ( 1 <_ %s /\\ %s <_ ( Q - 1 ) ) ) )' % (C3, QP, QP, QP))], 'mpbird', '%s e. ( 1 ... ( Q - 1 ) )' % QP)
    # the hypothesis at Q / p
    ihq, phq = rspcv_at(w, C3, 'y', PHIQ('y'), QP, mem, lift(w, ih, C3), rng='( 1 ... ( Q - 1 ) )')
    assert phq == PHIQ(QP), phq
    allq = c3([muq, ihq], 'mpd', ALLX(QP))
    idxu = w.s([], 'id', '( x = u -> x = u )'); cbu, bu = w.wcongr(ALLBODY(QP, 'x'), {'x': 'u'}, 'x = u', {'x': idxu})
    assert bu == ALLBODY(QP, 'u')
    allqu = c3([allq, w.s([cbu], 'cbvralvw', '( %s <-> %s )' % (ALLX(QP), ALLXU(QP)))], 'sylib', ALLXU(QP))
    # bvmchkqind with P := p, Q := Q / p, R := Q (its quantifier letter u is free of the context)
    indu = w.s([hs3, bind3(w, C3, pp, qpnn, gcd, 'p e. Prime', '%s e. NN' % QP, '( p gcd %s ) = 1' % QP), qeq, allqu], 'bvmchkqind', '( %s -> %s )' % (C3, ALLXU('Q')))
    idux = w.s([], 'id', '( u = x -> u = x )'); cbx, bx = w.wcongr(ALLBODY('Q', 'u'), {'u': 'x'}, 'u = x', {'u': idux})
    assert bx == ALLBODY('Q', 'x')
    ind = c3([indu, w.s([cbx], 'cbvralvw', '( %s <-> %s )' % (ALLXU('Q'), ALLX('Q')))], 'sylib', ALLX('Q'))
    c2 = c2s([ex, w.s([w.s([ind], 'ex', '( ( %s /\\ p e. Prime ) -> ( p || Q -> %s ) )' % (C2, ALLX('Q')))], 'rexlimdva', '( %s -> ( E. p e. Prime p || Q -> %s ) )' % (C2, ALLX('Q')))], 'mpd', ALLX('Q'))
    bi = s([clo(w, 'elnn1uz2', '( Q e. NN <-> ( Q = 1 \\/ Q e. ( ZZ>= ` 2 ) ) )')], 'a1i', '( Q e. NN <-> ( Q = 1 \\/ Q e. ( ZZ>= ` 2 ) ) )')
    allQ = s([c1, c2, s([qnn, bi], 'mpbid', '( Q = 1 \\/ Q e. ( ZZ>= ` 2 ) )')], 'mpjaodan', ALLX('Q'))
    e1 = w.s([allQ], 'ex', '( %s -> %s )' % (A0, PHIQ('Q')))
    w.qed([e1], 'ex', STATEMENTS['bvmchkqstep'])
    return w


def bvmchkqall():
    w = W('bvmchkqall', 'abs_mCheckQ_le for every Q e. NN by strong induction (nnsinds on bvmchkqstep).')
    PHq = lambda q: '( %s -> %s )' % (HS, PHIQ(q))
    idy = w.s([], 'id', '( q = y -> q = y )'); n1, py = w.wcongr(PHq('q'), {'q': 'y'}, 'q = y', {'q': idy})
    idQ = w.s([], 'id', '( q = Q -> q = Q )'); n2, pQ = w.wcongr(PHq('q'), {'q': 'Q'}, 'q = Q', {'q': idQ})
    assert py == PHq('y') and pQ == PHq('Q')
    IHY = 'A. y e. ( 1 ... ( q - 1 ) ) %s' % PHq('y')
    A = '( ( q e. NN /\\ %s ) /\\ %s )' % (IHY, HS)
    st = mkst(w, A)
    qnn = st([], 'simpll', 'q e. NN'); ihy = st([], 'simplr', IHY); hs = st([], 'simpr', HS)
    r = w.s([], 'r19.21v', '( %s <-> ( %s -> A. y e. ( 1 ... ( q - 1 ) ) %s ) )' % (IHY, HS, PHIQ('y')))
    ihimp = st([ihy, st([r], 'a1i', '( %s <-> ( %s -> A. y e. ( 1 ... ( q - 1 ) ) %s ) )' % (IHY, HS, PHIQ('y')))], 'mpbid', '( %s -> A. y e. ( 1 ... ( q - 1 ) ) %s )' % (HS, PHIQ('y')))
    ih = st([hs, ihimp], 'mpd', 'A. y e. ( 1 ... ( q - 1 ) ) %s' % PHIQ('y'))
    stp = st([bind(w, A, hs, qnn, HS, 'q e. NN'), w.inst('bvmchkqstep')], 'syl', '( A. y e. ( 1 ... ( q - 1 ) ) %s -> %s )' % (PHIQ('y'), PHIQ('q')))
    ph_q = st([ih, stp], 'mpd', PHIQ('q'))
    n3 = w.s([w.s([ph_q], 'ex', '( ( q e. NN /\\ %s ) -> %s )' % (IHY, PHq('q')))], 'ex', '( q e. NN -> ( %s -> %s ) )' % (IHY, PHq('q')))
    ind = w.s([n1, n2, n3], 'nnsinds', '( Q e. NN -> %s )' % PHq('Q'))
    w.qed([ind], 'impcom', STATEMENTS['bvmchkqall'])
    return w


def bvmchkq():
    w = W('bvmchkq', 'RZA Lemma 3.1 for squarefree Q with constant 11/3 (Lean abs_mCheckQ_le): '
                     '| ( Q ( mChkQ ` S ) X ) | <= ( Q / phi Q ) ( 11 / 3 ) ( 1 + ( S - 1 ) log X ) for X >= 1, S >= 1.')
    A = '( ( ( X e. RR /\\ 1 <_ X ) /\\ %s ) /\\ ( Q e. NN /\\ ( mmu ` Q ) =/= 0 ) )' % HS
    st = mkst(w, A)
    hx = st([], 'simpll', '( X e. RR /\\ 1 <_ X )'); hs = st([], 'simplr', HS); qnn = st([], 'simprl', 'Q e. NN'); mu = st([], 'simprr', '( mmu ` Q ) =/= 0')
    xr = st([hx], 'simpld', 'X e. RR'); x1 = st([hx], 'simprd', '1 <_ X')
    allq = st([mu, st([bind(w, A, hs, qnn, HS, 'Q e. NN'), w.inst('bvmchkqall')], 'syl', PHIQ('Q'))], 'mpd', ALLX('Q'))
    inst, body = rspcv_at(w, A, 'x', ALLBODY('Q', 'x'), 'X', xr, allq)
    w.qed([x1, inst], 'mpd', STATEMENTS['bvmchkq'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmchkqindlem', 'bvmchkqindn', 'bvmchkqind', 'bvmchkq1b', 'bvmchkqstep', 'bvmchkqall', 'bvmchkq']:
        runh(globals()[f]()) if f in ('bvmchkqindlem', 'bvmchkqindn', 'bvmchkqind') else globals()[f]().run()
