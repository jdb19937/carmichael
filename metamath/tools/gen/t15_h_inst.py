"""T15 (h): the concrete machine: projections, the installation, FinTM2."""
import os, sys, json, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
import num
import lin
lin.FASTPATH = True
from lin import linarith

TY = '( TMTy C K )'
LB = '( TMLbl C K )'
RT = '( TMRoot C K )'
PG = '( TMProg C K )'
AL = '( 0 ... ( ( C + K ) + ; ; 1 0 1 ) )'
WS = '{ w e. Word %s | ( # ` w ) <_ ; 3 0 }' % AL
FR = '( TMFroot (/) C K )'
S0 = '<. (/) , <. ( inr ` (/) ) , <. ( inr ` (/) ) , <. (/) , <. (/) , <. (/) , (/) >. >. >. >. >. >.'
MACH = '( TMMach C K )'
MAIN = '( TMLab ` ( ( (/) ++ <" 0 "> ) ++ <" 0 "> ) )'


def sets(w):
    """closed: TMGam e. _V, TMLbl e. _V, TMSt e. _V, <. TMGam , TMLbl >. e. _V"""
    g1 = w.s([w.s([], 'df-tmgam', "TMGam = ( ( 0 ..^ 8 ) X. { Gamma' } )"),
              w.s([w.s([], 'ovex', '( 0 ..^ 8 ) e. _V'), w.s([], 'snex', "{ Gamma' } e. _V")], 'xpex', "( ( 0 ..^ 8 ) X. { Gamma' } ) e. _V")],
             'eqeltri', 'TMGam e. _V')
    lab = w.s([w.s([], 'df-tmlab', 'TMLab = ( w e. Word NN0 |-> ( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w ) )'),
               w.s([w.s([w.s([], 'nn0ex', 'NN0 e. _V'), w.inst('wrdexg')], 'ax-mp', 'Word NN0 e. _V')], 'mptex',
                   '( w e. Word NN0 |-> ( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w ) ) e. _V')], 'eqeltri', 'TMLab e. _V')
    l1 = w.s([w.s([], 'df-tmlbl', '%s = ( TMLab " %s )' % (LB, WS)), w.s([lab], 'imaex', '( TMLab " %s ) e. _V' % WS)], 'eqeltri', '%s e. _V' % LB)
    st = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    gl = w.s([], 'opex', '<. TMGam , %s >. e. _V' % LB)
    return g1, l1, st, gl


def t15typ():
    w = W('t15typ', 'The projections of the type triple of the concrete machine.')
    g1, l1, st, gl = sets(w)
    df = w.s([], 'df-tmty', '%s = <. <. TMGam , %s >. , TMSt >.' % (TY, LB))
    a1_ = w.s([df], 'fveq2i', '( 1st ` %s ) = ( 1st ` <. <. TMGam , %s >. , TMSt >. )' % (TY, LB))
    a2 = w.s([gl, st, w.inst('op1stg')], 'mp2an', '( 1st ` <. <. TMGam , %s >. , TMSt >. ) = <. TMGam , %s >.' % (LB, LB))
    a = w.s([a1_, a2], 'eqtri', '( 1st ` %s ) = <. TMGam , %s >.' % (TY, LB))
    b1 = w.s([a], 'fveq2i', '( 1st ` ( 1st ` %s ) ) = ( 1st ` <. TMGam , %s >. )' % (TY, LB))
    b2 = w.s([g1, l1, w.inst('op1stg')], 'mp2an', '( 1st ` <. TMGam , %s >. ) = TMGam' % LB)
    b = w.s([b1, b2], 'eqtri', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)
    c1 = w.s([a], 'fveq2i', '( 2nd ` ( 1st ` %s ) ) = ( 2nd ` <. TMGam , %s >. )' % (TY, LB))
    c2 = w.s([g1, l1, w.inst('op2ndg')], 'mp2an', '( 2nd ` <. TMGam , %s >. ) = %s' % (LB, LB))
    c = w.s([c1, c2], 'eqtri', '( 2nd ` ( 1st ` %s ) ) = %s' % (TY, LB))
    d1 = w.s([df], 'fveq2i', '( 2nd ` %s ) = ( 2nd ` <. <. TMGam , %s >. , TMSt >. )' % (TY, LB))
    d2 = w.s([gl, st, w.inst('op2ndg')], 'mp2an', '( 2nd ` <. <. TMGam , %s >. , TMSt >. ) = TMSt' % LB)
    d = w.s([d1, d2], 'eqtri', '( 2nd ` %s ) = TMSt' % TY)
    w.qed([b, c, d], '3pm3.2i', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    return w


def fzsub(w, ph, lo_text, lo_le, zst, B, bz):
    """( ph -> ( 0 ... lo ) C_ ( 0 ... B ) ) from ( ph -> lo <_ B ), lo e. ZZ (zst), B e. ZZ (bz)"""
    ez = w.s([zst, bz, w.inst('eluz')], 'syl2anc', '( %s -> ( %s e. ( ZZ>= ` %s ) <-> %s <_ %s ) )' % (ph, B, lo_text, lo_text, B))
    eu = w.s([lo_le, ez], 'mpbird', '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, B, lo_text))
    return w.s([eu, w.inst('fzss2')], 'syl', '( %s -> ( 0 ... %s ) C_ ( 0 ... %s ) )' % (ph, lo_text, B))


def t15inst():
    w = W('t15inst', 'The concrete program installs the whole program (prefix, search, exit).')
    ph = '( C e. NN0 /\\ K e. NN )'
    cn = w.s([], 'simpl', '( %s -> C e. NN0 )' % ph)
    kn = w.s([], 'simpr', '( %s -> K e. NN )' % ph)
    g1, l1, st, gl = sets(w)
    ty = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    tg = w.s([ty], 'simp1i', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)
    tl = w.s([ty], 'simp2i', '( 2nd ` ( 1st ` %s ) ) = %s' % (TY, LB))
    ts = w.s([ty], 'simp3i', '( 2nd ` %s ) = TMSt' % TY)
    tv = w.s([w.s([], 'df-tmty', '%s = <. <. TMGam , %s >. , TMSt >.' % (TY, LB)), w.s([], 'opex', '<. <. TMGam , %s >. , TMSt >. e. _V' % LB)], 'eqeltri', '%s e. _V' % TY)
    TN = '( TMnroot C K %s %s ( TMLab ` (/) ) )' % (TY, FR)
    cb, items = content_body('TMIroot', dict(load_preds(), TMIroot=(['C', 'K', 'T', 'M', 'P', 'E'], ROOT_RHS.split(), 'df-tmiroot')))
    cbi = subst_text(cb, {'T': TY, 'P': FR, 'E': '( TMLab ` (/) )'})
    rdf = w.s([], 'df-tmroot', '%s = %s' % (RT, TN))
    ndf = w.s([], 'df-tmnroot', '%s = %s' % (TN, cbi))
    rx = w.s([rdf, w.s([ndf, w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % cbi)], 'eqeltri', '%s e. _V' % TN)], 'eqeltri', '%s e. _V' % RT)
    L = {}
    L['( ( %s e. _V /\\ %s e. _V ) /\\ ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` %s ) = TMSt )' % (TY, RT, TY, TY)] = a1(
        w, ph, w.s([w.s([tv, rx], 'pm3.2i', '( %s e. _V /\\ %s e. _V )' % (TY, RT)), tg, ts], '3pm3.2i',
                   '( ( %s e. _V /\\ %s e. _V ) /\\ ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` %s ) = TMSt )' % (TY, RT, TY, TY)),
        '( ( %s e. _V /\\ %s e. _V ) /\\ ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` %s ) = TMSt )' % (TY, RT, TY, TY))
    # the alphabet
    cr = w.s([cn], 'nn0red', '( %s -> C e. RR )' % ph)
    kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % ph)
    c0 = w.s([cn], 'nn0ge0d', '( %s -> 0 <_ C )' % ph)
    k0 = w.s([kn], 'nnnn0d', '( %s -> K e. NN0 )' % ph)
    k0g = w.s([k0], 'nn0ge0d', '( %s -> 0 <_ K )' % ph)
    Bt = '( ( C + K ) + ; ; 1 0 1 )'
    bn = w.s([w.s([cn, k0], 'nn0addcld', '( %s -> ( C + K ) e. NN0 )' % ph), a1(w, ph, num.nn0(w, 101), '; ; 1 0 1 e. NN0')], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, Bt))
    bz = w.s([bn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, Bt))
    lvs = {'C': cr, 'K': kr}
    l30 = linarith(w, ph, [c0, k0g], '; 3 0 <_ %s' % Bt, leaves=lvs)
    s30 = fzsub(w, ph, '; 3 0', l30, a1(w, ph, w.s([num.nn0(w, 30)], 'nn0zi', '; 3 0 e. ZZ'), '; 3 0 e. ZZ'), Bt, bz)
    san = a1(w, ph, w.s([], 'fz0ssnn0', '%s C_ NN0' % AL), '%s C_ NN0' % AL)
    L['( ( 0 ... ; 3 0 ) C_ %s /\\ %s C_ NN0 )' % (AL, AL)] = w.s([s30, san], 'jca', '( %s -> ( ( 0 ... ; 3 0 ) C_ %s /\\ %s C_ NN0 ) )' % (ph, AL, AL))
    lc = linarith(w, ph, [k0g], '( C + 1 ) <_ %s' % Bt, leaves=lvs)
    cz = w.s([w.s([cn], 'nn0zd', '( %s -> C e. ZZ )' % ph)], 'peano2zd', '( %s -> ( C + 1 ) e. ZZ )' % ph)
    L['( 0 ... ( C + 1 ) ) C_ %s' % AL] = fzsub(w, ph, '( C + 1 )', lc, cz, Bt, bz)
    lk = linarith(w, ph, [c0], '( K + 1 ) <_ %s' % Bt, leaves=lvs)
    kz = w.s([w.s([kn], 'nnzd', '( %s -> K e. ZZ )' % ph)], 'peano2zd', '( %s -> ( K + 1 ) e. ZZ )' % ph)
    L['( 0 ... ( K + 1 ) ) C_ %s' % AL] = fzsub(w, ph, '( K + 1 )', lk, kz, Bt, bz)
    l101 = linarith(w, ph, [c0, k0g], '; ; 1 0 1 <_ %s' % Bt, leaves=lvs)
    L['( 0 ... ; ; 1 0 1 ) C_ %s' % AL] = fzsub(w, ph, '; ; 1 0 1', l101, a1(w, ph, w.s([num.nn0(w, 101)], 'nn0zi', '; ; 1 0 1 e. ZZ'), '; ; 1 0 1 e. ZZ'), Bt, bz)
    L['C e. NN0'] = cn
    L['K e. NN'] = kn
    # HL
    pv = '( ( %s /\\ v e. Word %s ) /\\ ( # ` v ) <_ ; 3 0 )' % (ph, AL)
    vw = w.s([], 'simplr', '( %s -> v e. Word %s )' % (pv, AL))
    vl = w.s([], 'simpr', '( %s -> ( # ` v ) <_ ; 3 0 )' % pv)
    cbq = w.s([w.s([], 'fveq2', '( w = v -> ( # ` w ) = ( # ` v ) )')], 'breq1d', '( w = v -> ( ( # ` w ) <_ ; 3 0 <-> ( # ` v ) <_ ; 3 0 ) )')
    er = w.s([cbq], 'elrab', '( v e. %s <-> ( v e. Word %s /\\ ( # ` v ) <_ ; 3 0 ) )' % (WS, AL))
    vws = w.s([w.s([vw, vl], 'jca', '( %s -> ( v e. Word %s /\\ ( # ` v ) <_ ; 3 0 ) )' % (pv, AL)), er], 'sylibr', '( %s -> v e. %s )' % (pv, WS))
    ldf = w.s([], 'df-tmlab', 'TMLab = ( w e. Word NN0 |-> ( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w ) )')
    fn = w.s([w.s([], 'fvex', '( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w ) e. _V'), ldf], 'fnmpti', 'TMLab Fn Word NN0')
    ssw = w.s([w.s([w.s([], 'fz0ssnn0', '%s C_ NN0' % AL), w.inst('sswrd')], 'ax-mp', 'Word %s C_ Word NN0' % AL)], 'a1i', '') if False else None
    sw1 = w.s([w.s([], 'fz0ssnn0', '%s C_ NN0' % AL), w.inst('sswrd')], 'ax-mp', 'Word %s C_ Word NN0' % AL)
    sw2 = w.s([w.s([], 'ssrab2', '%s C_ Word %s' % (WS, AL)), sw1], 'sstri', '%s C_ Word NN0' % WS)
    fvi = w.s([a1(w, pv, fn, 'TMLab Fn Word NN0'), a1(w, pv, sw2, '%s C_ Word NN0' % WS), vws, w.inst('fnfvima')], 'syl3anc',
              '( %s -> ( TMLab ` v ) e. ( TMLab " %s ) )' % (pv, WS))
    lbd = w.s([], 'df-tmlbl', '%s = ( TMLab " %s )' % (LB, WS))
    Lq = w.s([tl, lbd], 'eqtri', '( 2nd ` ( 1st ` %s ) ) = ( TMLab " %s )' % (TY, WS))
    fvl = w.s([fvi, a1(w, pv, Lq, '( 2nd ` ( 1st ` %s ) ) = ( TMLab " %s )' % (TY, WS))], 'eleqtrrd', '( %s -> ( TMLab ` v ) e. ( 2nd ` ( 1st ` %s ) ) )' % (pv, TY))
    hl1 = w.s([fvl], 'ex', '( ( %s /\\ v e. Word %s ) -> ( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. ( 2nd ` ( 1st ` %s ) ) ) )' % (ph, AL, TY))
    HLt = 'A. v e. Word %s ( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. ( 2nd ` ( 1st ` %s ) ) )' % (AL, TY)
    L[HLt] = w.s([hl1], 'ralrimiva', '( %s -> %s )' % (ph, HLt))
    # HM
    pm = '( ( %s /\\ v e. Word %s ) /\\ ( ( # ` v ) <_ ; 3 0 /\\ ( %s TMWalk v ) e. ( TM2Stmt ` %s ) ) )' % (ph, AL, RT, TY)
    mw = w.s([], 'simplr', '( %s -> v e. Word %s )' % (pm, AL))
    ml = w.s([], 'simprl', '( %s -> ( # ` v ) <_ ; 3 0 )' % pm)
    ms = w.s([], 'simprr', '( %s -> ( %s TMWalk v ) e. ( TM2Stmt ` %s ) )' % (pm, RT, TY))
    mws = w.s([w.s([mw, ml], 'jca', '( %s -> ( v e. Word %s /\\ ( # ` v ) <_ ; 3 0 ) )' % (pm, AL)), er], 'sylibr', '( %s -> v e. %s )' % (pm, WS))
    mfi = w.s([a1(w, pm, fn, 'TMLab Fn Word NN0'), a1(w, pm, sw2, '%s C_ Word NN0' % WS), mws, w.inst('fnfvima')], 'syl3anc',
              '( %s -> ( TMLab ` v ) e. ( TMLab " %s ) )' % (pm, WS))
    mlb = w.s([mfi, a1(w, pm, lbd, '%s = ( TMLab " %s )' % (LB, WS))], 'eleqtrrd', '( %s -> ( TMLab ` v ) e. %s )' % (pm, LB))
    body = 'if ( ( %s TMWalk ( x ` -u 1 ) ) e. ( TM2Stmt ` %s ) , ( %s TMWalk ( x ` -u 1 ) ) , <. 6 , (/) >. )' % (RT, TY, RT)
    pdf = w.s([], 'df-tmprog', '%s = ( x e. %s |-> %s )' % (PG, LB, body))
    ifx = w.s([], 'ifexd', '') if False else None
    val = body.replace('( x ` -u 1 )', '( ( TMLab ` v ) ` -u 1 )')
    ie = w.s([w.s([], 'ifex', '%s e. _V' % val)], 'a1i', '( %s -> %s e. _V )' % (pm, val))
    m1, v1 = fvm(w, pm, PG, pdf, 'x', LB, body, '( TMLab ` v )', mlb, ie)
    sw3 = w.s([w.s([], 'fz0ssnn0', '%s C_ NN0' % AL), w.inst('sswrd')], 'ax-mp', 'Word %s C_ Word NN0' % AL)
    mw0 = w.s([a1(w, pm, sw3, 'Word %s C_ Word NN0' % AL), mw], 'sseldd', '( %s -> v e. Word NN0 )' % pm)
    ad = w.s([mw0, ml, w.inst('tmlabadr')], 'syl2anc', '( %s -> ( ( TMLab ` v ) ` -u 1 ) = v )' % pm)
    wq = w.s([ad], 'oveq2d', '( %s -> ( %s TMWalk ( ( TMLab ` v ) ` -u 1 ) ) = ( %s TMWalk v ) )' % (pm, RT, RT))
    iq = w.s([w.s([wq], 'eleq1d', '( %s -> ( ( %s TMWalk ( ( TMLab ` v ) ` -u 1 ) ) e. ( TM2Stmt ` %s ) <-> ( %s TMWalk v ) e. ( TM2Stmt ` %s ) ) )' % (pm, RT, TY, RT, TY)), wq,
              w.s([], 'eqidd', '( %s -> <. 6 , (/) >. = <. 6 , (/) >. )' % pm)], 'ifbieq12d',
             '( %s -> %s = if ( ( %s TMWalk v ) e. ( TM2Stmt ` %s ) , ( %s TMWalk v ) , <. 6 , (/) >. ) )' % (pm, val, RT, TY, RT))
    it = w.s([ms], 'iftrued', '( %s -> if ( ( %s TMWalk v ) e. ( TM2Stmt ` %s ) , ( %s TMWalk v ) , <. 6 , (/) >. ) = ( %s TMWalk v ) )' % (pm, RT, TY, RT, RT))
    mv = w.s([m1, iq, it], '3eqtrd', '( %s -> ( %s ` ( TMLab ` v ) ) = ( %s TMWalk v ) )' % (pm, PG, RT))
    hm1 = w.s([mv], 'ex', '( ( %s /\\ v e. Word %s ) -> ( ( ( # ` v ) <_ ; 3 0 /\\ ( %s TMWalk v ) e. ( TM2Stmt ` %s ) ) -> ( %s ` ( TMLab ` v ) ) = ( %s TMWalk v ) ) )' % (ph, AL, RT, TY, PG, RT))
    HMt = 'A. v e. Word %s ( ( ( # ` v ) <_ ; 3 0 /\\ ( %s TMWalk v ) e. ( TM2Stmt ` %s ) ) -> ( %s ` ( TMLab ` v ) ) = ( %s TMWalk v ) )' % (AL, RT, TY, PG, RT)
    L[HMt] = w.s([hm1], 'ralrimiva', '( %s -> %s )' % (ph, HMt))
    # the root address
    L['(/) e. Word %s' % AL] = a1(w, ph, w.s([], 'wrd0', '(/) e. Word %s' % AL), '(/) e. Word %s' % AL)
    h0 = w.s([], 'hash0', '( # ` (/) ) = 0')
    e1 = w.s([h0], 'oveq1i', '( ( # ` (/) ) + ; 2 0 ) = ( 0 + ; 2 0 )')
    e2 = num.add_nat(w, 0, 20)
    e3 = w.s([e1, e2], 'eqtri', '( ( # ` (/) ) + ; 2 0 ) = ; 2 0')
    le = num.le_nat(w, 20, 30)
    L['( ( # ` (/) ) + ; 2 0 ) <_ ; 3 0'] = a1(w, ph, w.s([e3, le], 'eqbrtri', '( ( # ` (/) ) + ; 2 0 ) <_ ; 3 0'), '( ( # ` (/) ) + ; 2 0 ) <_ ; 3 0')
    L['%s = ( TMFroot (/) C K )' % FR] = a1(w, ph, w.s([], 'eqid', '%s = %s' % (FR, FR)), '%s = %s' % (FR, FR))
    # E = ( TMLab ` (/) ) in L
    z0 = w.s([], 'wrd0', '(/) e. Word %s' % AL)
    hle = w.s([e3.replace('', '') if False else h0, a1(w, ph, num.le_nat(w, 0, 30), '0 <_ ; 3 0')], 'eqbrtrd', '') if False else None
    h0l = w.s([h0, num.le_nat(w, 0, 30)], 'eqbrtri', '( # ` (/) ) <_ ; 3 0')
    rs = w.s([z0, w.inst('rspcv')], 'ax-mp', '') if False else None
    cq = w.s([w.s([w.s([], 'fveq2', '( v = (/) -> ( # ` v ) = ( # ` (/) ) )')], 'breq1d', '( v = (/) -> ( ( # ` v ) <_ ; 3 0 <-> ( # ` (/) ) <_ ; 3 0 ) )'),
              w.s([w.s([], 'fveq2', '( v = (/) -> ( TMLab ` v ) = ( TMLab ` (/) ) )')], 'eleq1d', '( v = (/) -> ( ( TMLab ` v ) e. ( 2nd ` ( 1st ` %s ) ) <-> ( TMLab ` (/) ) e. ( 2nd ` ( 1st ` %s ) ) ) )' % (TY, TY))], 'imbi12d',
             '( v = (/) -> ( ( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. ( 2nd ` ( 1st ` %s ) ) ) <-> ( ( # ` (/) ) <_ ; 3 0 -> ( TMLab ` (/) ) e. ( 2nd ` ( 1st ` %s ) ) ) ) )' % (TY, TY))
    rsp = w.s([cq], 'rspcv', '( (/) e. Word %s -> ( %s -> ( ( # ` (/) ) <_ ; 3 0 -> ( TMLab ` (/) ) e. ( 2nd ` ( 1st ` %s ) ) ) ) )' % (AL, HLt, TY))
    e_ = w.s([a1(w, ph, z0, '(/) e. Word %s' % AL), L[HLt], rsp], 'sylc', '( %s -> ( ( # ` (/) ) <_ ; 3 0 -> ( TMLab ` (/) ) e. ( 2nd ` ( 1st ` %s ) ) ) )' % (ph, TY))
    L['( TMLab ` (/) ) e. ( 2nd ` ( 1st ` %s ) )' % TY] = w.s([a1(w, ph, h0l, '( # ` (/) ) <_ ; 3 0'), e_], 'mpd', '( %s -> ( TMLab ` (/) ) e. ( 2nd ` ( 1st ` %s ) ) )' % (ph, TY))
    wk = w.s([a1(w, ph, rx, '%s e. _V' % RT), w.inst('tmwalk0')], 'syl', '( %s -> ( %s TMWalk (/) ) = %s )' % (ph, RT, RT))
    L['( %s TMWalk (/) ) = %s' % (RT, TN)] = w.s([wk, a1(w, ph, rdf, '%s = %s' % (RT, TN))], 'eqtrd', '( %s -> ( %s TMWalk (/) ) = %s )' % (ph, RT, TN))
    # instantiate t15kroot (its hypotheses in order)
    hyps = []
    for f in kroot_hyps():
        f2 = subst_text(f, {'T': TY, 'M': PG, 'R': RT, 'A': AL, 'W': '(/)', 'P': FR, 'E': '( TMLab ` (/) )'})
        hyps.append(L[f2])
    w.qed(hyps, 't15kroot', '( %s -> TMIroot C K %s %s %s ( TMLab ` (/) ) )' % (ph, TY, PG, FR))
    return w


def kroot_hyps():
    """the $e formulas of t15kroot (without ph ->)"""
    txt = open(os.path.join(ROOT, 'sorties', 't15.mm')).read()
    out = []
    for m in re.finditer(r't15kroot\.(\d+) \$e \|- \( ph -> (.*?) \) \$\.', txt, re.S):
        out.append((int(m.group(1)), ' '.join(m.group(2).split())))
    return [f for _, f in sorted(out)]


GENS = {'t15typ': t15typ, 't15inst': t15inst}



def t15prog():
    w = W('t15prog', 'The program of the concrete machine is a function from its labels to statements.')
    ph = '( C e. NN0 /\\ K e. NN )'
    body = 'if ( ( %s TMWalk ( x ` -u 1 ) ) e. ( TM2Stmt ` %s ) , ( %s TMWalk ( x ` -u 1 ) ) , <. 6 , (/) >. )' % (RT, TY, RT)
    pdf = w.s([], 'df-tmprog', '%s = ( x e. %s |-> %s )' % (PG, LB, body))
    px = '( %s /\\ x e. %s )' % (ph, LB)
    c = '( %s TMWalk ( x ` -u 1 ) ) e. ( TM2Stmt ` %s )' % (RT, TY)
    a = w.s([], 'simpr', '( ( %s /\\ %s ) -> %s )' % (px, c, c))
    tv = w.s([w.s([], 'df-tmty', '%s = <. <. TMGam , %s >. , TMSt >.' % (TY, LB)), w.s([], 'opex', '<. <. TMGam , %s >. , TMSt >. e. _V' % LB)], 'eqeltri', '%s e. _V' % TY)
    hl = w.s([tv, w.inst('tm2halt')], 'ax-mp', '<. 6 , (/) >. e. ( TM2Stmt ` %s )' % TY)
    b = w.s([hl], 'a1i', '( ( %s /\\ -. %s ) -> <. 6 , (/) >. e. ( TM2Stmt ` %s ) )' % (px, c, TY))
    ic = w.s([a, b], 'ifclda', '( %s -> %s e. ( TM2Stmt ` %s ) )' % (px, body, TY))
    f1 = w.s([ic], 'fmpt3d' if False else 'fmptd', '( %s -> ( x e. %s |-> %s ) : %s --> ( TM2Stmt ` %s ) )' % (ph, LB, body, LB, TY))
    fq = w.s([a1(w, ph, pdf, '%s = ( x e. %s |-> %s )' % (PG, LB, body))], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stmt ` %s ) <-> ( x e. %s |-> %s ) : %s --> ( TM2Stmt ` %s ) ) )' % (ph, PG, LB, TY, LB, body, LB, TY))
    f2 = w.s([f1, fq], 'mpbird', '( %s -> %s : %s --> ( TM2Stmt ` %s ) )' % (ph, PG, LB, TY))
    ty = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    tl = a1(w, ph, w.s([ty], 'simp2i', '( 2nd ` ( 1st ` %s ) ) = %s' % (TY, LB)), '( 2nd ` ( 1st ` %s ) ) = %s' % (TY, LB))
    fq2 = w.s([tl], 'feq2d', '( %s -> ( %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) <-> %s : %s --> ( TM2Stmt ` %s ) ) )' % (ph, PG, TY, TY, PG, LB, TY))
    w.qed([f2, fq2], 'mpbird', '( %s -> %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) )' % (ph, PG, TY, TY))
    return w


def t15lblfi():
    w = W('t15lblfi', 'The label set of the concrete machine is finite and contains the entry label.')
    ph = '( C e. NN0 /\\ K e. NN )'
    afi = w.s([], 'fzfi', '%s e. Fin' % AL)
    U = 'U_ n e. ( 0 ... ; 3 0 ) { w e. Word %s | ( # ` w ) = n }' % AL
    wn = w.s([afi, w.inst('wrdnfi')], 'ax-mp', '{ w e. Word %s | ( # ` w ) = n } e. Fin' % AL)
    wr = w.s([w.s([wn], 'a1i', '( n e. ( 0 ... ; 3 0 ) -> { w e. Word %s | ( # ` w ) = n } e. Fin )' % AL)], 'rgen', 'A. n e. ( 0 ... ; 3 0 ) { w e. Word %s | ( # ` w ) = n } e. Fin' % AL)
    ufi = w.s([w.s([], 'fzfi', '( 0 ... ; 3 0 ) e. Fin'), wr, w.inst('iunfi')], 'mp2an', '%s e. Fin' % U)
    # WS C_ U
    pv = 'v e. %s' % WS
    cbq = w.s([w.s([], 'fveq2', '( w = v -> ( # ` w ) = ( # ` v ) )')], 'breq1d', '( w = v -> ( ( # ` w ) <_ ; 3 0 <-> ( # ` v ) <_ ; 3 0 ) )')
    er = w.s([cbq], 'elrab', '( v e. %s <-> ( v e. Word %s /\\ ( # ` v ) <_ ; 3 0 ) )' % (WS, AL))
    e1 = w.s([er], 'biimpi', '( %s -> ( v e. Word %s /\\ ( # ` v ) <_ ; 3 0 ) )' % (pv, AL))
    vw = w.s([e1], 'simpld', '( %s -> v e. Word %s )' % (pv, AL))
    vl = w.s([e1], 'simprd', '( %s -> ( # ` v ) <_ ; 3 0 )' % pv)
    vn = w.s([vw, w.inst('lencl')], 'syl', '( %s -> ( # ` v ) e. NN0 )' % pv)
    d30 = w.s([w.s([num.nn0(w, 30)], 'a1i', '( %s -> ; 3 0 e. NN0 )' % pv)], 'id', '') if False else None
    d30 = w.s([num.nn0(w, 30)], 'a1i', '( %s -> ; 3 0 e. NN0 )' % pv)
    fz = w.s([w.s([vn, d30, vl], '3jca', '( %s -> ( ( # ` v ) e. NN0 /\\ ; 3 0 e. NN0 /\\ ( # ` v ) <_ ; 3 0 ) )' % pv),
              w.s([], 'elfz2nn0', '( ( # ` v ) e. ( 0 ... ; 3 0 ) <-> ( ( # ` v ) e. NN0 /\\ ; 3 0 e. NN0 /\\ ( # ` v ) <_ ; 3 0 ) )')], 'sylibr',
             '( %s -> ( # ` v ) e. ( 0 ... ; 3 0 ) )' % pv)
    cq2 = w.s([w.s([], 'fveq2', '( w = v -> ( # ` w ) = ( # ` v ) )')], 'eqeq1d', '( w = v -> ( ( # ` w ) = ( # ` v ) <-> ( # ` v ) = ( # ` v ) ) )')
    er2 = w.s([cq2], 'elrab', '( v e. { w e. Word %s | ( # ` w ) = ( # ` v ) } <-> ( v e. Word %s /\\ ( # ` v ) = ( # ` v ) ) )' % (AL, AL))
    ein = w.s([w.s([vw, w.s([], 'eqidd', '( %s -> ( # ` v ) = ( # ` v ) )' % pv)], 'jca', '( %s -> ( v e. Word %s /\\ ( # ` v ) = ( # ` v ) ) )' % (pv, AL)), er2], 'sylibr',
              '( %s -> v e. { w e. Word %s | ( # ` w ) = ( # ` v ) } )' % (pv, AL))
    cq3 = w.s([w.s([w.s([], 'eqeq2', '( n = ( # ` v ) -> ( ( # ` w ) = n <-> ( # ` w ) = ( # ` v ) ) )')], 'rabbidv',
                   '( n = ( # ` v ) -> { w e. Word %s | ( # ` w ) = n } = { w e. Word %s | ( # ` w ) = ( # ` v ) } )' % (AL, AL))], 'eleq2d',
              '( n = ( # ` v ) -> ( v e. { w e. Word %s | ( # ` w ) = n } <-> v e. { w e. Word %s | ( # ` w ) = ( # ` v ) } ) )' % (AL, AL))
    rx = w.s([cq3], 'rspcev', '( ( ( # ` v ) e. ( 0 ... ; 3 0 ) /\\ v e. { w e. Word %s | ( # ` w ) = ( # ` v ) } ) -> E. n e. ( 0 ... ; 3 0 ) v e. { w e. Word %s | ( # ` w ) = n } )' % (AL, AL))
    ex = w.s([fz, ein, rx], 'syl2anc', '( %s -> E. n e. ( 0 ... ; 3 0 ) v e. { w e. Word %s | ( # ` w ) = n } )' % (pv, AL))
    eu = w.s([ex, w.s([], 'eliun', '( v e. %s <-> E. n e. ( 0 ... ; 3 0 ) v e. { w e. Word %s | ( # ` w ) = n } )' % (U, AL))], 'sylibr', '( %s -> v e. %s )' % (pv, U))
    ss = w.s([eu], 'ssriv', '%s C_ %s' % (WS, U))
    wfi = w.s([ufi, ss, w.inst('ssfi')], 'mp2an', '%s e. Fin' % WS)
    ldf = w.s([], 'df-tmlab', 'TMLab = ( w e. Word NN0 |-> ( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w ) )')
    fn = w.s([w.s([], 'fvex', '( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w ) e. _V'), ldf], 'fnmpti', 'TMLab Fn Word NN0')
    ifi = w.s([w.s([fn], 'fnfuni' if False else 'ax-mp', '') if False else w.s([fn, w.inst('fnfun')], 'ax-mp', 'Fun TMLab'), wfi, w.inst('imafi')], 'mp2an', '( TMLab " %s ) e. Fin' % WS)
    lbd = w.s([], 'df-tmlbl', '%s = ( TMLab " %s )' % (LB, WS))
    lfi = w.s([lbd, ifi], 'eqeltri', '%s e. Fin' % LB)
    # the entry label
    z = w.s([], 'wrd0', '(/) e. Word %s' % AL)
    c0 = w.s([w.s([w.s([w.s([], '0nn0', '0 e. NN0'), num.nn0(w, 101)], 'pm3.2i', '') if False else w.s([], '0nn0', '0 e. NN0'), w.inst('0elfz')], 'ax-mp', '0 e. %s' % AL)], 'id', '') if False else None
    zel = w.s([], 'fvexd', '') if False else None
    # 0 e. AL via 0elfz needs ( ( C + K ) + 101 ) e. NN0: under ph
    cn = w.s([], 'simpl', '( %s -> C e. NN0 )' % ph)
    kn = w.s([w.s([], 'simpr', '( %s -> K e. NN )' % ph)], 'nnnn0d', '( %s -> K e. NN0 )' % ph)
    bn = w.s([w.s([cn, kn], 'nn0addcld', '( %s -> ( C + K ) e. NN0 )' % ph), a1(w, ph, num.nn0(w, 101), '; ; 1 0 1 e. NN0')], 'nn0addcld', '( %s -> ( ( C + K ) + ; ; 1 0 1 ) e. NN0 )' % ph)
    z0 = w.s([bn, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, AL))
    w1 = w.s([a1(w, ph, z, '(/) e. Word %s' % AL), z0, w.inst('ccatws1cl')], 'syl2anc', '( %s -> ( (/) ++ <" 0 "> ) e. Word %s )' % (ph, AL))
    w2 = w.s([w1, z0, w.inst('ccatws1cl')], 'syl2anc', '( %s -> ( ( (/) ++ <" 0 "> ) ++ <" 0 "> ) e. Word %s )' % (ph, AL))
    l1 = w.s([w1, w.inst('ccatws1len')], 'syl', '( %s -> ( # ` ( ( (/) ++ <" 0 "> ) ++ <" 0 "> ) ) = ( ( # ` ( (/) ++ <" 0 "> ) ) + 1 ) )' % ph)
    l2 = w.s([a1(w, ph, z, '(/) e. Word %s' % AL), w.inst('ccatws1len')], 'syl', '( %s -> ( # ` ( (/) ++ <" 0 "> ) ) = ( ( # ` (/) ) + 1 ) )' % ph)
    h0 = a1(w, ph, w.s([], 'hash0', '( # ` (/) ) = 0'), '( # ` (/) ) = 0')
    l3 = w.s([h0], 'oveq1d', '( %s -> ( ( # ` (/) ) + 1 ) = ( 0 + 1 ) )' % ph)
    l4 = w.s([l2, l3, a1(w, ph, w.s([], '0p1e1', '( 0 + 1 ) = 1'), '( 0 + 1 ) = 1')], '3eqtrd', '( %s -> ( # ` ( (/) ++ <" 0 "> ) ) = 1 )' % ph)
    l5 = w.s([l4], 'oveq1d', '( %s -> ( ( # ` ( (/) ++ <" 0 "> ) ) + 1 ) = ( 1 + 1 ) )' % ph)
    l6 = w.s([l1, l5, a1(w, ph, w.s([], '1p1e2', '( 1 + 1 ) = 2'), '( 1 + 1 ) = 2')], '3eqtrd', '( %s -> ( # ` ( ( (/) ++ <" 0 "> ) ++ <" 0 "> ) ) = 2 )' % ph)
    l7 = w.s([l6, a1(w, ph, num.le_nat(w, 2, 30), '2 <_ ; 3 0')], 'eqbrtrd', '( %s -> ( # ` ( ( (/) ++ <" 0 "> ) ++ <" 0 "> ) ) <_ ; 3 0 )' % ph)
    W2 = '( ( (/) ++ <" 0 "> ) ++ <" 0 "> )'
    cq = w.s([w.s([], 'fveq2', '( w = %s -> ( # ` w ) = ( # ` %s ) )' % (W2, W2))], 'breq1d', '( w = %s -> ( ( # ` w ) <_ ; 3 0 <-> ( # ` %s ) <_ ; 3 0 ) )' % (W2, W2))
    ew = w.s([cq], 'elrab', '( %s e. %s <-> ( %s e. Word %s /\\ ( # ` %s ) <_ ; 3 0 ) )' % (W2, WS, W2, AL, W2))
    w3 = w.s([w.s([w2, l7], 'jca', '( %s -> ( %s e. Word %s /\\ ( # ` %s ) <_ ; 3 0 ) )' % (ph, W2, AL, W2)), ew], 'sylibr', '( %s -> %s e. %s )' % (ph, W2, WS))
    sw1 = w.s([w.s([], 'fz0ssnn0', '%s C_ NN0' % AL), w.inst('sswrd')], 'ax-mp', 'Word %s C_ Word NN0' % AL)
    sw2 = w.s([w.s([], 'ssrab2', '%s C_ Word %s' % (WS, AL)), sw1], 'sstri', '%s C_ Word NN0' % WS)
    fv = w.s([a1(w, ph, fn, 'TMLab Fn Word NN0'), a1(w, ph, sw2, '%s C_ Word NN0' % WS), w3, w.inst('fnfvima')], 'syl3anc', '( %s -> %s e. ( TMLab " %s ) )' % (ph, MAIN, WS))
    ml = w.s([fv, a1(w, ph, lbd, '%s = ( TMLab " %s )' % (LB, WS))], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, MAIN, LB))
    w.qed([a1(w, ph, lfi, '%s e. Fin' % LB), ml], 'jca', '( %s -> ( %s e. Fin /\\ %s e. %s ) )' % (ph, LB, MAIN, LB))
    return w


GENS['t15prog'] = t15prog
GENS['t15lblfi'] = t15lblfi

if __name__ == '__main__':
    for lab in sys.argv[1:]:
        GENS[lab]().run()
