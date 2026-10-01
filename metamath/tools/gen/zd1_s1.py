"""Sortie ZD1: ZeroDensity.lean section 1 (Lemma 8.1): the block decomposition, the block weights,
the geometric sum, the frozen parameters."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import Closure


def cc4(w, ante):
    return w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % ante)


def zdje4():
    w = W('zdje4', "A e ^ ( - A / 4 ) <_ 4 for A >_ 0 (the step hje of Lean block_weight_le): 1 + A / 4 <_ e ^ ( A / 4 ).")
    ante = '( A e. RR /\\ 0 <_ A )'
    st = mkst(w, ante)
    ar = st([], 'simpl', 'A e. RR'); a0 = st([], 'simpr', '0 <_ A')
    c = Closure(w, ante, {'A': ('RR', ar)})
    a4 = c.mem('( A / 4 )', 'RR')
    a40 = linarith(w, ante, [a0], '0 <_ ( A / 4 )', leaves={'A': ar})
    E = '( exp ` ( A / 4 ) )'; Ep = '( exp ` -u ( A / 4 ) )'
    ef = st([a4, a40, w.inst('bvefge1p')], 'syl2anc', '( 1 + ( A / 4 ) ) <_ %s' % E)
    er = c.mem(E, 'RR'); epr = c.mem(Ep, 'RR'); ep0 = c.gt0(Ep)
    m = st([ef, st([st([], '1red', '1 e. RR'), a4], 'readdcld', '( 1 + ( A / 4 ) ) e. RR'), er, epr, st([ep0], 'ltled', '0 <_ %s' % Ep)],
           'lemul1ad', '( ( 1 + ( A / 4 ) ) x. %s ) <_ ( %s x. %s )' % (Ep, E, Ep))
    can = st([st([a4], 'recnd', '( A / 4 ) e. CC'), w.inst('efcan')], 'syl', '( %s x. %s ) = 1' % (E, Ep))
    g = linarith(w, ante, [m, can, ep0], '( A x. %s ) <_ 4' % Ep, leaves={'A': ar, Ep: epr, E: er}, products=True)
    # exp ( -u ( A / 4 ) ) = exp ( ( -u A / 4 ) )
    dn = st([st([ar], 'recnd', 'A e. CC'), w.s([w.s([], '4cn', '4 e. CC')], 'a1i', '( %s -> 4 e. CC )' % ante), w.s([w.s([], '4ne0', '4 =/= 0')], 'a1i', '( %s -> 4 =/= 0 )' % ante)], 'divnegd', '-u ( A / 4 ) = ( -u A / 4 )')
    e1 = st([dn], 'fveq2d', '%s = ( exp ` ( -u A / 4 ) )' % Ep)
    e2 = st([e1], 'oveq2d', '( A x. %s ) = ( A x. ( exp ` ( -u A / 4 ) ) )' % Ep)
    w.qed([e2, g], 'eqbrtrrd', STATEMENTS['zdje4'])
    return w



def a1c(w, ante, ref, f):
    """a closed fact lifted to ante"""
    return w.s([w.s([], ref, f)], 'a1i', '( %s -> %s )' % (ante, f))


def efexp_quarter(w, ante, c, r4):
    """facts about r = ( exp ` -u ( 1 / 4 ) ): RR, 0 <_ r, r <_ ( 4 / 5 )"""
    st = mkst(w, ante)
    R = '( exp ` -u ( 1 / 4 ) )'; E = '( exp ` ( 1 / 4 ) )'
    q = w.s([num.real(w, '( 1 / 4 )')], 'a1i', '( %s -> ( 1 / 4 ) e. RR )' % ante)
    q0 = w.s([num.le_lit(w, '0', '( 1 / 4 )')], 'a1i', '( %s -> 0 <_ ( 1 / 4 ) )' % ante)
    ef = st([q, q0, w.inst('bvefge1p')], 'syl2anc', '( 1 + ( 1 / 4 ) ) <_ %s' % E)
    er = st([q], 'reefcld', '%s e. RR' % E)
    rr = st([st([q], 'renegcld', '-u ( 1 / 4 ) e. RR')], 'reefcld', '%s e. RR' % R)
    r0 = st([st([st([q], 'renegcld', '-u ( 1 / 4 ) e. RR')], 'rpefcld', '%s e. RR+' % R)], 'rpgt0d', '0 < %s' % R)
    m = st([er, st([st([], '1red', '1 e. RR'), q], 'readdcld', '( 1 + ( 1 / 4 ) ) e. RR'), rr, st([r0], 'ltled', '0 <_ %s' % R), ef],
           'lemul2ad', '( %s x. ( 1 + ( 1 / 4 ) ) ) <_ ( %s x. %s )' % (R, R, E))
    can = st([st([q], 'recnd', '( 1 / 4 ) e. CC'), w.inst('efcan')], 'syl', '( %s x. %s ) = 1' % (E, R))
    le = linarith(w, ante, [m, can], '%s <_ ( 4 / 5 )' % R, leaves={R: rr, E: er}, products=True)
    return dict(rr=rr, r0=r0, le=le, R=R)


def zdgeo4():
    w = W('zdgeo4', "sum_ j <_ J e ^ ( - j / 4 ) <_ 5 (Lean sum_exp_neg_quarter_le): a geometric sum of ratio e ^ ( - 1 / 4 ) <_ 4 / 5.")
    ante = 'J e. NN0'
    st = mkst(w, ante)
    jn = w.s([], 'id', '( J e. NN0 -> J e. NN0 )')
    c = Closure(w, ante, {'J': ('NN0', jn)})
    f = efexp_quarter(w, ante, c, None)
    R = f['R']; rr = f['rr']
    AF = '( %s /\\ j e. ( 0 ... J ) )' % ante; sf = mkst(w, AF)
    jnn0 = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... J ) )' % AF), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % AF)
    jz = sf([jnn0], 'nn0zd', 'j e. ZZ'); jr = sf([jnn0], 'nn0red', 'j e. RR')
    e1 = lineq(w, AF, '( -u j / 4 )', '( j x. -u ( 1 / 4 ) )', leaves={'j': jr})
    e2 = sf([e1], 'fveq2d', '( exp ` ( -u j / 4 ) ) = ( exp ` ( j x. -u ( 1 / 4 ) ) )')
    qc = w.s([num.cc(w, '-u ( 1 / 4 )') if False else w.s([w.s([num.real(w, '( 1 / 4 )')], 'renegcli', '-u ( 1 / 4 ) e. RR')], 'recni', '-u ( 1 / 4 ) e. CC')], 'a1i',
             '( %s -> -u ( 1 / 4 ) e. CC )' % AF)
    e3 = sf([qc, jz, w.inst('efexp')], 'syl2anc', '( exp ` ( j x. -u ( 1 / 4 ) ) ) = ( %s ^ j )' % R)
    e4 = sf([e2, e3], 'eqtrd', '( exp ` ( -u j / 4 ) ) = ( %s ^ j )' % R)
    S1 = 'sum_ j e. ( 0 ... J ) ( exp ` ( -u j / 4 ) )'
    S2 = 'sum_ j e. ( 0 ... J ) ( %s ^ j )' % R
    es = st([e4], 'sumeq2dv', '%s = %s' % (S1, S2))
    rne1 = st([st([f['le'], linarith(w, ante, [f['le']], '%s < 1' % R, leaves={R: rr})][1:], 'ltned', '%s =/= 1' % R)], 'id', '%s =/= 1' % R) if False else \
        st([linarith(w, ante, [f['le']], '%s < 1' % R, leaves={R: rr})], 'ltned', '%s =/= 1' % R)
    j1 = sy(w, ante, jn, 'peano2nn0', '( J + 1 ) e. NN0')
    g = st([st([rr], 'recnd', '%s e. CC' % R), rne1, j1], 'geoser',
           'sum_ j e. ( 0 ... ( ( J + 1 ) - 1 ) ) ( %s ^ j ) = ( ( 1 - ( %s ^ ( J + 1 ) ) ) / ( 1 - %s ) )' % (R, R, R))
    pn = st([c.mem('J', 'CC'), st([], '1cnd', '1 e. CC')], 'pncand', '( ( J + 1 ) - 1 ) = J')
    rg = st([pn], 'oveq2d', '( 0 ... ( ( J + 1 ) - 1 ) ) = ( 0 ... J )')
    sg = st([rg], 'sumeq1d', 'sum_ j e. ( 0 ... ( ( J + 1 ) - 1 ) ) ( %s ^ j ) = %s' % (R, S2))
    Q = '( ( 1 - ( %s ^ ( J + 1 ) ) ) / ( 1 - %s ) )' % (R, R)
    e5 = st([sg, g], 'eqtr3d', '%s = %s' % (S2, Q))
    pw = '( %s ^ ( J + 1 ) )' % R
    pwr = st([rr, j1], 'reexpcld', '%s e. RR' % pw)
    pw0 = st([rr, j1, st([f['r0']], 'ltled', '0 <_ %s' % R)], 'expge0d', '0 <_ %s' % pw)
    num_ = st([st([], '1red', '1 e. RR'), pwr], 'resubcld', '( 1 - %s ) e. RR' % pw)
    den = '( 1 - %s )' % R
    denr = st([st([], '1red', '1 e. RR'), rr], 'resubcld', '%s e. RR' % den)
    den0 = linarith(w, ante, [f['le']], '0 < %s' % den, leaves={R: rr})
    denp = st([denr, den0], 'elrpd', '%s e. RR+' % den)
    core = linarith(w, ante, [f['le'], pw0], '( 1 - %s ) <_ ( %s x. 5 )' % (pw, den), leaves={R: rr, pw: pwr})
    five = w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % ante)
    bi = st([num_, five, denp], 'ledivmul2d', '( %s <_ 5 <-> ( 1 - %s ) <_ ( 5 x. %s ) )' % (Q, pw, den))
    core2 = st([core, st([st([denr], 'recnd', '%s e. CC' % den), a1c(w, ante, '5cn', '5 e. CC')], 'mulcomd', '( %s x. 5 ) = ( 5 x. %s )' % (den, den))],
               'breqtrd', '( 1 - %s ) <_ ( 5 x. %s )' % (pw, den))
    q5 = st([core2, bi], 'mpbird', '%s <_ 5' % Q)
    w.qed([st([es, e5], 'eqtrd', '%s = %s' % (S1, Q)), q5], 'eqbrtrd', STATEMENTS['zdgeo4'])
    return w



def zdparams():
    w = W('zdparams', "Parameter sanity at log D >_ 200 (Lean frozen_params_large): 100 <_ z1 = D ^c ( 31 / 50 ) <_ X = D ^c ( 6 / 5 ) and 1 <_ X.")
    ante = HZD
    st = mkst(w, ante)
    df = dfacts(w, ante, w.s([], 'id', '( %s -> %s )' % (ante, ante)))
    z = cxpD(w, ante, df, C31)
    L = '( log ` D )'
    a = '( %s x. %s )' % (C31, L)
    ar = st([z['qr'], df['lr']], 'remulcld', '%s e. RR' % a)
    a0 = linarith(w, ante, [df['l200']], '0 <_ %s' % a, leaves={L: df['lr']})
    ef = st([ar, a0, w.inst('bvefge1p')], 'syl2anc', '( 1 + %s ) <_ ( exp ` %s )' % (a, a))
    efr = st([ar], 'reefcld', '( exp ` %s ) e. RR' % a)
    h100 = linarith(w, ante, [ef, df['l200']], '; ; 1 0 0 <_ ( exp ` %s )' % a, leaves={L: df['lr'], '( exp ` %s )' % a: efr})
    z100 = st([h100, z['eq']], 'breqtrrd', '; ; 1 0 0 <_ %s' % Z1)
    x = cxpD(w, ante, df, '( 6 / 5 )')
    zx = st([df['dr'], st([df['d1']], 'ltled', '1 <_ D'), z['qr'], x['qr'], litle(w, ante, C31, '( 6 / 5 )')], 'cxplead', '%s <_ %s' % (Z1, XP))
    x1 = linarith(w, ante, [z100, zx], '1 <_ %s' % XP, leaves={Z1: z['re'], XP: x['re']})
    w.qed([z100, zx, x1], '3jca', STATEMENTS['zdparams'])
    return w



def zdblkw():
    w = W('zdblkw', "The per-block weight (Lean block_weight_le, with wgt j <_ e ^ -j absorbed): for 1 <_ X, 0 <_ B <_ 1 / 50, J e. NN0, "
                    "e ^ -J ( 2 ^ J X ) ^c B log ( 2 ^ J X ) <_ e ^ ( - J / 4 ) X ^c B ( log X + 3 ).")
    ante = '( ( X e. RR /\\ 1 <_ X ) /\\ ( B e. RR /\\ ( 0 <_ B /\\ B <_ ( 1 / ; 5 0 ) ) ) /\\ J e. NN0 )'
    st = mkst(w, ante)
    hx = st([], 'simp1', '( X e. RR /\\ 1 <_ X )'); hb = st([], 'simp2', '( B e. RR /\\ ( 0 <_ B /\\ B <_ ( 1 / ; 5 0 ) ) )')
    jn = st([], 'simp3', 'J e. NN0')
    xr = st([hx], 'simpld', 'X e. RR'); x1 = st([hx], 'simprd', '1 <_ X')
    br = st([hb], 'simpld', 'B e. RR'); b0 = st([st([hb], 'simprd', '( 0 <_ B /\\ B <_ ( 1 / ; 5 0 ) )')], 'simpld', '0 <_ B')
    b50 = st([st([hb], 'simprd', '( 0 <_ B /\\ B <_ ( 1 / ; 5 0 ) )')], 'simprd', 'B <_ ( 1 / ; 5 0 )')
    jr = st([jn], 'nn0red', 'J e. RR'); jz = st([jn], 'nn0zd', 'J e. ZZ'); j0 = st([jn], 'nn0ge0d', '0 <_ J')
    xrp = st([xr, linarith(w, ante, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    P = '( 2 ^ J )'
    prp = st([a1c(w, ante, '2rp', '2 e. RR+'), jz], 'rpexpcld', '%s e. RR+' % P)
    pr = st([prp], 'rpred', '%s e. RR' % P)
    l2 = '( log ` 2 )'
    l2r = st([a1c(w, ante, '2rp', '2 e. RR+')], 'relogcld', '%s e. RR' % l2)
    l2g = a1c(w, ante, 'log2ge', '( 1 / 2 ) <_ %s' % l2)
    l2u = a1c(w, ante, 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % l2)
    LX = '( log ` X )'
    lxr = st([xrp], 'relogcld', '%s e. RR' % LX)
    lx0 = sy2(w, ante, xr, x1, 'logge0', '0 <_ %s' % LX)
    XB = '( X ^c B )'
    xbrp = st([xrp, br], 'rpcxpcld', '%s e. RR+' % XB); xbr = st([xbrp], 'rpred', '%s e. RR' % XB)
    PB = '( %s ^c B )' % P
    # log ( 2 ^ J ) = J log 2
    lp = st([a1c(w, ante, '2rp', '2 e. RR+'), jz, w.inst('relogexp')], 'syl2anc', '( log ` %s ) = ( J x. %s )' % (P, l2))
    # ( 2 ^ J ) ^c B = exp ( B ( J log 2 ) )
    pb1 = st([st([prp], 'rpcnd', '%s e. CC' % P), st([prp], 'rpne0d', '%s =/= 0' % P), st([br], 'recnd', 'B e. CC')], 'cxpefd',
             '%s = ( exp ` ( B x. ( log ` %s ) ) )' % (PB, P))
    pb2 = st([st([lp], 'oveq2d', '( B x. ( log ` %s ) ) = ( B x. ( J x. %s ) )' % (P, l2))], 'fveq2d',
             '( exp ` ( B x. ( log ` %s ) ) ) = ( exp ` ( B x. ( J x. %s ) ) )' % (P, l2))
    pb = st([pb1, pb2], 'eqtrd', '%s = ( exp ` ( B x. ( J x. %s ) ) )' % (PB, l2))
    EJ = '( exp ` -u J )'
    U = '( B x. ( J x. %s ) )' % l2
    ur = st([br, st([jr, l2r], 'remulcld', '( J x. %s ) e. RR' % l2)], 'remulcld', '%s e. RR' % U)
    nj = st([jr], 'renegcld', '-u J e. RR')
    WW = '( exp ` ( -u J + %s ) )' % U
    wadd = st([st([nj], 'recnd', '-u J e. CC'), st([ur], 'recnd', '%s e. CC' % U), w.inst('efadd')], 'syl2anc',
              '%s = ( %s x. ( exp ` %s ) )' % (WW, EJ, U))
    # exp(-J) P^cB = W
    ew = st([st([pb], 'oveq2d', '( %s x. %s ) = ( %s x. ( exp ` %s ) )' % (EJ, PB, EJ, U)), wadd], 'eqtr4d', '( %s x. %s ) = %s' % (EJ, PB, WW))
    # LHS rewriting
    PX = '( %s x. X )' % P
    mc = st([pr, st([prp], 'rpge0d', '0 <_ %s' % P), xr, st([xrp], 'rpge0d', '0 <_ X'), st([br], 'recnd', 'B e. CC')], 'mulcxpd',
            '( %s ^c B ) = ( %s x. %s )' % (PX, PB, XB))
    SS = '( ( J x. %s ) + %s )' % (l2, LX)
    lm = st([prp, xrp], 'relogmuld', '( log ` %s ) = ( ( log ` %s ) + %s )' % (PX, P, LX))
    lm2 = st([lm, st([lp], 'oveq1d', '( ( log ` %s ) + %s ) = %s' % (P, LX, SS))], 'eqtrd', '( log ` %s ) = %s' % (PX, SS))
    LHS = '( ( %s x. ( %s ^c B ) ) x. ( log ` %s ) )' % (EJ, PX, PX)
    L1 = '( ( %s x. ( %s x. %s ) ) x. %s )' % (EJ, PB, XB, SS)
    r1 = st([st([mc], 'oveq2d', '( %s x. ( %s ^c B ) ) = ( %s x. ( %s x. %s ) )' % (EJ, PX, EJ, PB, XB)), lm2], 'oveq12d', '%s = %s' % (LHS, L1))
    ejr = st([nj], 'reefcld', '%s e. RR' % EJ)
    pbr = st([st([prp, br], 'rpcxpcld', '%s e. RR+' % PB)], 'rpred', '%s e. RR' % PB)
    L2 = '( ( ( %s x. %s ) x. %s ) x. %s )' % (EJ, PB, XB, SS)
    r2 = st([st([st([st([ejr], 'recnd', '%s e. CC' % EJ), st([pbr], 'recnd', '%s e. CC' % PB), st([xbr], 'recnd', '%s e. CC' % XB)], 'mulassd',
                    '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (EJ, PB, XB, EJ, PB, XB))], 'oveq1d', '%s = %s' % (L2, L1))], 'eqcomd', '%s = %s' % (L1, L2))
    L3 = '( ( %s x. %s ) x. %s )' % (WW, XB, SS)
    r3 = st([st([ew], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (EJ, PB, XB, WW, XB))], 'oveq1d', '%s = %s' % (L2, L3))
    ssr = st([st([jr, l2r], 'remulcld', '( J x. %s ) e. RR' % l2), lxr], 'readdcld', '%s e. RR' % SS)
    wwr = st([st([nj, ur], 'readdcld', '( -u J + %s ) e. RR' % U)], 'reefcld', '%s e. RR' % WW)
    L4 = '( ( %s x. %s ) x. %s )' % (WW, SS, XB)
    r4 = st([st([wwr], 'recnd', '%s e. CC' % WW), st([xbr], 'recnd', '%s e. CC' % XB), st([ssr], 'recnd', '%s e. CC' % SS)], 'mul32d', '%s = %s' % (L3, L4))
    lhs = eqtr(w, ante, [r1, r2, r3, r4], None)
    # W <_ e e
    E4 = '( exp ` ( -u J / 4 ) )'
    q4 = '( -u J / 4 )'
    q4r = st([nj, a1c(w, ante, '4re', '4 e. RR'), a1c(w, ante, '4ne0', '4 =/= 0')], 'redivcld', '%s e. RR' % q4)
    e4r = st([q4r], 'reefcld', '%s e. RR' % E4)
    e40 = st([st([q4r], 'rpefcld', '%s e. RR+' % E4)], 'rpge0d', '0 <_ %s' % E4)
    l21 = linarith(w, ante, [l2u], '%s <_ 1' % l2, leaves={l2: l2r})
    jl = st([jr, l2r, st([], '1red', '1 e. RR'), j0, l21], 'lemul2ad', '( J x. %s ) <_ ( J x. 1 )' % l2)
    jl0 = st([jr, l2r], 'remulcld', '( J x. %s ) e. RR' % l2)
    jl00 = st([jr, l2r, j0, linarith(w, ante, [l2g], '0 <_ %s' % l2, leaves={l2: l2r})], 'mulge0d', '0 <_ ( J x. %s )' % l2)
    ub = st([br, litr(w, ante, '( 1 / ; 5 0 )'), jl0, st([jr, st([], '1red', '1 e. RR')], 'remulcld', '( J x. 1 ) e. RR'), b0, jl00, b50, jl], 'lemul12ad',
            '%s <_ ( ( 1 / ; 5 0 ) x. ( J x. 1 ) )' % U)
    ex = linarith(w, ante, [ub, j0], '( -u J + %s ) <_ ( %s + %s )' % (U, q4, q4), leaves={'J': jr, U: ur})
    efl = st([st([nj, ur], 'readdcld', '( -u J + %s ) e. RR' % U), st([q4r, q4r], 'readdcld', '( %s + %s ) e. RR' % (q4, q4)), w.inst('efle')], 'syl2anc',
             '( ( -u J + %s ) <_ ( %s + %s ) <-> %s <_ ( exp ` ( %s + %s ) ) )' % (U, q4, q4, WW, q4, q4))
    wle = st([ex, efl], 'mpbid', '%s <_ ( exp ` ( %s + %s ) )' % (WW, q4, q4))
    ee = st([st([q4r], 'recnd', '%s e. CC' % q4), st([q4r], 'recnd', '%s e. CC' % q4), w.inst('efadd')], 'syl2anc',
            '( exp ` ( %s + %s ) ) = ( %s x. %s )' % (q4, q4, E4, E4))
    wle2 = st([wle, ee], 'breqtrd', '%s <_ ( %s x. %s )' % (WW, E4, E4))
    ss0 = linarith(w, ante, [jl00, lx0], '0 <_ %s' % SS, leaves={'( J x. %s )' % l2: jl0, LX: lxr})
    hc = st([wwr, st([e4r, e4r], 'remulcld', '( %s x. %s ) e. RR' % (E4, E4)), ssr, ss0, wle2], 'lemul1ad',
            '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (WW, SS, E4, E4, SS))
    # e J <_ 4 (zdje4), e <_ 1
    je = st([jr, j0, w.inst('zdje4')], 'syl2anc', '( J x. %s ) <_ 4' % E4)
    e1l = st([q4r, st([], '0red', '0 e. RR'), w.inst('efle')], 'syl2anc', '( %s <_ 0 <-> %s <_ ( exp ` 0 ) )' % (q4, E4))
    e1 = st([st([linarith(w, ante, [j0], '%s <_ 0' % q4, leaves={'J': jr}), e1l], 'mpbid', '%s <_ ( exp ` 0 )' % E4), a1c(w, ante, 'ef0', '( exp ` 0 ) = 1')],
            'breqtrd', '%s <_ 1' % E4)
    jer = st([jr, e4r], 'remulcld', '( J x. %s ) e. RR' % E4)
    f1 = st([jer, litr(w, ante, '4'), l2r, linarith(w, ante, [l2g], '0 <_ %s' % l2, leaves={l2: l2r}), je], 'lemul1ad',
            '( ( J x. %s ) x. %s ) <_ ( 4 x. %s )' % (E4, l2, l2))
    f2 = st([e4r, st([], '1red', '1 e. RR'), lxr, lx0, e1], 'lemul1ad', '( %s x. %s ) <_ ( 1 x. %s )' % (E4, LX, LX))
    T3 = '( 3 + %s )' % LX
    g = linarith(w, ante, [f1, f2, l2u], '( ( %s x. %s ) + ( %s x. %s ) ) <_ %s' % (E4, '( J x. %s )' % l2, E4, LX, T3),
                 leaves={E4: e4r, 'J': jr, l2: l2r, LX: lxr}, products=True)
    Tin = '( ( %s x. %s ) + ( %s x. %s ) )' % (E4, '( J x. %s )' % l2, E4, LX)
    tinr = st([st([e4r, jl0], 'remulcld', '( %s x. ( J x. %s ) ) e. RR' % (E4, l2)), st([e4r, lxr], 'remulcld', '( %s x. %s ) e. RR' % (E4, LX))],
              'readdcld', '%s e. RR' % Tin)
    t3r = st([litr(w, ante, '3'), lxr], 'readdcld', '%s e. RR' % T3)
    gm = st([tinr, t3r, e4r, e40, g], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (E4, Tin, E4, T3))
    eqs = lineq(w, ante, '( ( %s x. %s ) x. %s )' % (E4, E4, SS), '( %s x. %s )' % (E4, Tin), products=True,
                leaves={E4: e4r, 'J': jr, l2: l2r, LX: lxr})
    core = st([hc, st([eqs, gm], 'eqbrtrd', '( ( %s x. %s ) x. %s ) <_ ( %s x. %s )' % (E4, E4, SS, E4, T3))], 'letrd',
              '( %s x. %s ) <_ ( %s x. %s )' % (WW, SS, E4, T3))
    fin = st([st([wwr, ssr], 'remulcld', '( %s x. %s ) e. RR' % (WW, SS)), st([e4r, t3r], 'remulcld', '( %s x. %s ) e. RR' % (E4, T3)), xbr,
              st([xbrp], 'rpge0d', '0 <_ %s' % XB), core], 'lemul1ad', '%s <_ ( ( %s x. %s ) x. %s )' % (L4, E4, T3, XB))
    RHS = '( ( %s x. %s ) x. ( %s + 3 ) )' % (E4, XB, LX)
    rr = lineq(w, ante, '( ( %s x. %s ) x. %s )' % (E4, T3, XB), RHS, products=True, leaves={E4: e4r, XB: xbr, LX: lxr})
    w.qed([lhs, st([fin, rr], 'breqtrd', '%s <_ %s' % (L4, RHS))], 'eqbrtrd', STATEMENTS['zdblkw'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
