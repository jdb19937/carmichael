"""Sortie V5: the set-theoretic side of SmoothShifted.lean: the bad primes
inject into the tagged union of the twin sets (smshbad), the count (smshcnt),
and the good/bad split of ppi (smshsplit).
MM_DB=sorties/v5.mm python3 tools/gen/v5_sets.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from cl import lift
import num
import v5lib
from v5lib import mkst, lit, Proj, subst, HALF

only = sys.argv[1:]
A0 = '( X e. NN /\\ E e. RR )'
SBX, SGX = v5lib.SB('X', 'E'), v5lib.SG('X', 'E')
UUX, FFX = v5lib.UU('X', 'E'), v5lib.FF('X', 'E')
MX = v5lib.MM('X', 'E')
AX = '( X ^c ( 1 - E ) )'
INN = v5lib.INNER('X', 'E')


def run(w):
    if only and w.label not in only:
        return True
    ok = w.run()
    assert ok, w.label
    return ok


def a0facts(w, st):
    xnn = st([], 'simpl', 'X e. NN'); ere = st([], 'simpr', 'E e. RR')
    return xnn, ere


# ------------------------------------------------------------------ smshbad
def smshbad():
    w = W('smshbad', 'Every bad prime p <_ X, one with a prime factor q of p - 1 above X ^c ( 1 - E ), is '
                     'm q + 1 for a cofactor m <_ |_ X ^c E _| and a prime q <_ |_ X / m _| with m q + 1 prime: '
                     'the bad primes lie in the range of the map ( m , q ) |-> m q + 1 on the tagged union of '
                     'the twin sets (Lean: hbad_sub of smooth_shifted_weak).')
    A1 = '( %s /\\ p e. %s )' % (A0, SBX)
    st1 = mkst(w, A1)
    # unpack p e. SB
    sl, bodyp = subst(w, 'a', 'p', '( a e. Prime /\\ -. %s )' % INN)
    INNP = v5lib.INNER('X', 'E', a='p')
    el = w.s([sl], 'elrab', '( p e. %s <-> ( p e. ( 0 ... X ) /\\ %s ) )' % (SBX, bodyp))
    unp = st1([st1([], 'simpr', 'p e. %s' % SBX), el], 'sylib', '( p e. ( 0 ... X ) /\\ %s )' % bodyp)
    pfz = st1([unp], 'simpld', 'p e. ( 0 ... X )')
    ppr = st1([st1([unp], 'simprd', bodyp)], 'simpld', 'p e. Prime')
    nal = st1([st1([unp], 'simprd', bodyp)], 'simprd', '-. %s' % INNP)
    NEG = '-. ( q || ( p - 1 ) -> q <_ %s )' % AX
    rex = st1([nal, w.s([], 'rexnal', '( E. q e. Prime %s <-> -. %s )' % (NEG, INNP))], 'sylibr',
              'E. q e. Prime %s' % NEG)
    # the q-free antecedent
    A2 = '( %s /\\ ( p e. ( 0 ... X ) /\\ p e. Prime ) )' % A0
    A3 = '( %s /\\ q e. Prime )' % A2
    A4 = '( %s /\\ %s )' % (A3, NEG)
    st = mkst(w, A4); pj = Proj(w, A4)
    xnn = pj('X e. NN'); ere = pj('E e. RR'); pfz4 = pj('p e. ( 0 ... X )'); ppr4 = pj('p e. Prime')
    qpr = pj('q e. Prime'); neg = pj(NEG)
    dv = st([neg, w.s([], 'annim', '( ( q || ( p - 1 ) /\\ -. q <_ %s ) <-> %s )' % (AX, NEG))], 'sylibr',
            '( q || ( p - 1 ) /\\ -. q <_ %s )' % AX)
    qdv = st([dv], 'simpld', 'q || ( p - 1 )'); nle = st([dv], 'simprd', '-. q <_ %s' % AX)
    pnn = st([ppr4, w.inst('prmnn')], 'syl', 'p e. NN'); qnn = st([qpr, w.inst('prmnn')], 'syl', 'q e. NN')
    pm1 = st([st([ppr4, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'), w.inst('uz2m1nn')], 'syl', '( p - 1 ) e. NN')
    TM = '( ( p - 1 ) / q )'
    mnn = st([qdv, st([pm1, qnn, w.inst('nndivdvds')], 'syl2anc', '( q || ( p - 1 ) <-> %s e. NN )' % TM)], 'mpbid',
             '%s e. NN' % TM)
    pcn = st([pnn], 'nncnd', 'p e. CC'); qcn = st([qnn], 'nncnd', 'q e. CC'); qne = st([qnn], 'nnne0d', 'q =/= 0')
    pm1cn = st([pm1], 'nncnd', '( p - 1 ) e. CC')
    mq = st([pm1cn, qcn, qne], 'divcan1d', '( %s x. q ) = ( p - 1 )' % TM)
    # reals
    xre = st([xnn], 'nnred', 'X e. RR'); xrp = st([xnn], 'nnrpd', 'X e. RR+')
    ome = st([st([], '1red', '1 e. RR'), ere], 'resubcld', '( 1 - E ) e. RR')
    axrp = st([xrp, ome], 'rpcxpcld', '%s e. RR+' % AX); axre = st([axrp], 'rpred', '%s e. RR' % AX)
    XE = '( X ^c E )'
    xerp = st([xrp, ere], 'rpcxpcld', '%s e. RR+' % XE); xere = st([xerp], 'rpred', '%s e. RR' % XE)
    qre = st([qnn], 'nnred', 'q e. RR'); pre = st([pnn], 'nnred', 'p e. RR')
    mre = st([mnn], 'nnred', '%s e. RR' % TM); mrp = st([mnn], 'nnrpd', '%s e. RR+' % TM)
    pm1re = st([pm1], 'nnred', '( p - 1 ) e. RR')
    axq = st([nle, st([axre, qre], 'ltnled', '( %s < q <-> -. q <_ %s )' % (AX, AX))], 'mpbird', '%s < q' % AX)
    px = st([pfz4, w.inst('elfzle2')], 'syl', 'p <_ X')
    # X = X^E X^(1-E)
    ecn = st([ere], 'recnd', 'E e. CC'); onecn = st([], '1cnd', '1 e. CC')
    xcn = st([xre], 'recnd', 'X e. CC'); xne = st([xrp], 'rpne0d', 'X =/= 0')
    xsp = st([xcn, xne, ecn, st([ome], 'recnd', '( 1 - E ) e. CC')], 'cxpaddd',
             '( X ^c ( E + ( 1 - E ) ) ) = ( %s x. %s )' % (XE, AX))
    e1 = st([st([ecn, onecn], 'pncan3d', '( E + ( 1 - E ) ) = 1')], 'oveq2d', '( X ^c ( E + ( 1 - E ) ) ) = ( X ^c 1 )')
    xeq = st([st([e1, st([xcn], 'cxp1d', '( X ^c 1 ) = X')], 'eqtrd', '( X ^c ( E + ( 1 - E ) ) ) = X'), xsp],
             'eqtr3d', 'X = ( %s x. %s )' % (XE, AX))
    # m AX < m q = p - 1 < p <_ X = XE AX
    t0 = st([axq, st([axre, qre, mrp], 'ltmul2d', '( %s < q <-> ( %s x. %s ) < ( %s x. q ) )' % (AX, TM, AX, TM))],
            'mpbid', '( %s x. %s ) < ( %s x. q )' % (TM, AX, TM))
    t1 = st([t0, mq], 'breqtrd', '( %s x. %s ) < ( p - 1 )' % (TM, AX))
    max_ = st([mre, axre], 'remulcld', '( %s x. %s ) e. RR' % (TM, AX))
    t2 = st([max_, pm1re, pre, t1, st([pre], 'ltm1d', '( p - 1 ) < p')], 'lttrd', '( %s x. %s ) < p' % (TM, AX))
    t3 = st([max_, pre, xre, t2, px], 'ltletrd', '( %s x. %s ) < X' % (TM, AX))
    t4 = st([t3, xeq], 'breqtrd', '( %s x. %s ) < ( %s x. %s )' % (TM, AX, XE, AX))
    mlt = st([t4, st([mre, xere, axrp], 'ltmul1d', '( %s < %s <-> ( %s x. %s ) < ( %s x. %s ) )' % (TM, XE, TM, AX, XE, AX))],
             'mpbird', '%s < %s' % (TM, XE))
    mle = st([mre, xere, mlt], 'ltled', '%s <_ %s' % (TM, XE))
    mz = st([mnn], 'nnzd', '%s e. ZZ' % TM)
    mM = st([mle, st([xere, mz, w.inst('flge')], 'syl2anc', '( %s <_ %s <-> %s <_ %s )' % (TM, XE, TM, MX))], 'mpbid',
            '%s <_ %s' % (TM, MX))
    Mz = st([xere], 'flcld', '%s e. ZZ' % MX)
    M1 = st([lit(w, A4, '1', 'RR'), mre, st([Mz], 'zred', '%s e. RR' % MX), st([mnn], 'nnge1d', '1 <_ %s' % TM), mM],
            'letrd', '1 <_ %s' % MX)
    Mnn = st([Mz, M1, w.s([], 'elnnz1', '( %s e. NN <-> ( %s e. ZZ /\\ 1 <_ %s ) )' % (MX, MX, MX))], 'sylanbrc',
             '%s e. NN' % MX)
    mfz = st([mnn, Mnn, mM, w.s([], 'elfz1b', '( %s e. ( 1 ... %s ) <-> ( %s e. NN /\\ %s e. NN /\\ %s <_ %s ) )'
                               % (TM, MX, TM, MX, TM, MX))], 'syl3anbrc', '%s e. ( 1 ... %s )' % (TM, MX))
    # q <_ |_ X / m _|
    FLM = v5lib.FL('X', TM)
    qm = st([st([qcn, st([mnn], 'nncnd', '%s e. CC' % TM)], 'mulcomd', '( q x. %s ) = ( %s x. q )' % (TM, TM)), mq],
            'eqtrd', '( q x. %s ) = ( p - 1 )' % TM)
    pm1x = st([pm1re, pre, xre, st([pre], 'ltm1d', '( p - 1 ) < p'), px], 'ltletrd', '( p - 1 ) < X')
    qmx = st([qm, st([pm1re, xre, pm1x], 'ltled', '( p - 1 ) <_ X')], 'eqbrtrd', '( q x. %s ) <_ X' % TM)
    qxm = st([qmx, st([qre, xre, mrp], 'lemuldivd', '( ( q x. %s ) <_ X <-> q <_ ( X / %s ) )' % (TM, TM))], 'mpbid',
             'q <_ ( X / %s )' % TM)
    xmre = st([xre, mrp], 'rerpdivcld', '( X / %s ) e. RR' % TM)
    qfl = st([qxm, st([xmre, st([qnn], 'nnzd', 'q e. ZZ'), w.inst('flge')], 'syl2anc',
                      '( q <_ ( X / %s ) <-> q <_ %s )' % (TM, FLM))], 'mpbid', 'q <_ %s' % FLM)
    fln0 = st([st([xnn], 'nnnn0d', 'X e. NN0'), mnn, w.inst('fldivnn0')], 'syl2anc', '%s e. NN0' % FLM)
    fl1 = st([lit(w, A4, '1', 'RR'), qre, st([fln0], 'nn0red', '%s e. RR' % FLM), st([qnn], 'nnge1d', '1 <_ q'), qfl],
             'letrd', '1 <_ %s' % FLM)
    flnn = st([fln0, fl1, w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (FLM, FLM, FLM))], 'sylanbrc',
              '%s e. NN' % FLM)
    qfz = st([qnn, flnn, qfl, w.s([], 'elfz1b', '( q e. ( 1 ... %s ) <-> ( q e. NN /\\ %s e. NN /\\ q <_ %s ) )'
                                % (FLM, FLM, FLM))], 'syl3anbrc', 'q e. ( 1 ... %s )' % FLM)
    # m q + 1 = p is prime
    mq1 = st([st([mq], 'oveq1d', '( ( %s x. q ) + 1 ) = ( ( p - 1 ) + 1 )' % TM), st([pcn, onecn], 'npcand', '( ( p - 1 ) + 1 ) = p')],
             'eqtrd', '( ( %s x. q ) + 1 ) = p' % TM)
    mq1pr = st([mq1, ppr4], 'eqeltrd', '( ( %s x. q ) + 1 ) e. Prime' % TM)
    TWM = v5lib.TW(TM, FLM)
    sl2, tbody = subst(w, 'v', 'q', '( v e. Prime /\\ ( ( %s x. v ) + 1 ) e. Prime )' % TM)
    el2 = w.s([sl2], 'elrab', '( q e. %s <-> ( q e. ( 1 ... %s ) /\\ %s ) )' % (TWM, FLM, tbody))
    qtw = st([qfz, st([qpr, mq1pr], 'jca', tbody), el2], 'sylanbrc', 'q e. %s' % TWM)
    mv = st([], 'ovexd', '%s e. _V' % TM)
    msn = st([mv, w.inst('snidg')], 'syl', '%s e. { %s }' % (TM, TM))
    PAIR = '<. %s , q >.' % TM
    pel = st([msn, qtw], 'opelxpd', '%s e. ( { %s } X. %s )' % (PAIR, TM, TWM))
    TWJ = v5lib.TW('j', v5lib.FL('X', 'j'))
    sl3, _ = subst(w, 'j', TM, '%s e. ( { j } X. %s )' % (PAIR, TWJ))
    rex3 = st([mfz, pel, w.s([sl3], 'rspcev', '( ( %s e. ( 1 ... %s ) /\\ %s e. ( { %s } X. %s ) ) -> E. j e. ( 1 ... %s ) %s e. ( { j } X. %s ) )'
                                               % (TM, MX, PAIR, TM, TWM, MX, PAIR, TWJ))], 'syl2anc',
               'E. j e. ( 1 ... %s ) %s e. ( { j } X. %s )' % (MX, PAIR, TWJ))
    puu = st([rex3, w.s([], 'eliun', '( %s e. %s <-> E. j e. ( 1 ... %s ) %s e. ( { j } X. %s ) )' % (PAIR, UUX, MX, PAIR, TWJ))],
             'sylibr', '%s e. %s' % (PAIR, UUX))
    # p = ( 1st u ) ( 2nd u ) + 1 at u = the pair
    A5 = '( %s /\\ u = %s )' % (A4, PAIR)
    ov = w.s([], 'ovex', '%s e. _V' % TM); qv = w.s([], 'vex', 'q e. _V')
    o1 = w.s([ov, qv], 'op1std', '( u = %s -> ( 1st ` u ) = %s )' % (PAIR, TM))
    o2 = w.s([ov, qv], 'op2ndd', '( u = %s -> ( 2nd ` u ) = q )' % PAIR)
    ueq = w.s([], 'simpr', '( %s -> u = %s )' % (A5, PAIR))
    o12 = w.s([w.s([ueq, o1], 'syl', '( %s -> ( 1st ` u ) = %s )' % (A5, TM)), w.s([ueq, o2], 'syl', '( %s -> ( 2nd ` u ) = q )' % A5)],
              'oveq12d', '( %s -> ( ( 1st ` u ) x. ( 2nd ` u ) ) = ( %s x. q ) )' % (A5, TM))
    o13 = w.s([o12], 'oveq1d', '( %s -> ( ( ( 1st ` u ) x. ( 2nd ` u ) ) + 1 ) = ( ( %s x. q ) + 1 ) )' % (A5, TM))
    peq = w.s([w.s([o13, w.s([mq1], 'adantr', '( %s -> ( ( %s x. q ) + 1 ) = p )' % (A5, TM))], 'eqtrd',
                   '( %s -> ( ( ( 1st ` u ) x. ( 2nd ` u ) ) + 1 ) = p )' % A5)], 'eqcomd',
              '( %s -> p = ( ( ( 1st ` u ) x. ( 2nd ` u ) ) + 1 ) )' % A5)
    prn = st([w.s([], 'eqid', '%s = %s' % (FFX, FFX)), puu, st([w.s([], 'vex', 'p e. _V')], 'a1i', 'p e. _V'), peq], 'elrnmptdv', 'p e. ran %s' % FFX)
    # eliminate q and close
    imp = w.s([prn], 'ex', '( %s -> ( %s -> p e. ran %s ) )' % (A3, NEG, FFX))
    rl = w.s([imp], 'rexlimdva', '( %s -> ( E. q e. Prime %s -> p e. ran %s ) )' % (A2, NEG, FFX))
    a2 = st1([st1([], 'simpl', A0), st1([pfz, ppr], 'jca', '( p e. ( 0 ... X ) /\\ p e. Prime )')], 'jca', A2)
    fin = st1([rex, st1([a2, rl], 'syl', '( E. q e. Prime %s -> p e. ran %s )' % (NEG, FFX))], 'mpd', 'p e. ran %s' % FFX)
    w.qed([w.s([fin], 'ex', '( %s -> ( p e. %s -> p e. ran %s ) )' % (A0, SBX, FFX))], 'ssrdv', v5lib.STATEMENTS['smshbad'])
    return run(w)


# ------------------------------------------------------------------ smshcnt
def smshcnt():
    w = W('smshcnt', 'The number of bad primes up to X is at most the sum over the cofactors m <_ |_ X ^c E _| of the '
                     'twin counts # { q <_ |_ X / m _| prime with m q + 1 prime } (Lean: hbad_card of smooth_shifted_weak).')
    st = mkst(w, A0)
    xnn, ere = a0facts(w, st)
    TWJ = v5lib.TW('j', v5lib.FL('X', 'j'))
    XJ = '( { j } X. %s )' % TWJ
    RNG = '( 1 ... %s )' % MX
    rfin = st([], 'fzfid', '%s e. Fin' % RNG)
    AJ = '( %s /\\ j e. %s )' % (A0, RNG)
    stj = mkst(w, AJ)
    twfin = stj([stj([], 'fzfid', '( 1 ... %s ) e. Fin' % v5lib.FL('X', 'j')), w.inst('rabfi')], 'syl', '%s e. Fin' % TWJ)
    snf = stj([w.s([], 'snfi', '{ j } e. Fin')], 'a1i', '{ j } e. Fin')
    xjfin = stj([snf, twfin, w.inst('xpfi')], 'syl2anc', '%s e. Fin' % XJ)
    allfin = st([xjfin], 'ralrimiva', 'A. j e. %s %s e. Fin' % (RNG, XJ))
    uufin = st([rfin, allfin, w.inst('iunfi')], 'syl2anc', '%s e. Fin' % UUX)
    # the map onto its range
    feq = w.s([], 'eqid', '%s = %s' % (FFX, FFX))
    BU = '( ( ( 1st ` u ) x. ( 2nd ` u ) ) + 1 )'
    allv = w.s([w.s([], 'ovex', '%s e. _V' % BU)], 'rgenw', 'A. u e. %s %s e. _V' % (UUX, BU))
    ffn = w.s([allv, w.s([feq], 'fnmpt', '( A. u e. %s %s e. _V -> %s Fn %s )' % (UUX, BU, FFX, UUX))], 'ax-mp',
              '%s Fn %s' % (FFX, UUX))
    ffo = w.s([ffn, w.s([], 'dffn4', '( %s Fn %s <-> %s : %s -onto-> ran %s )' % (FFX, UUX, FFX, UUX, FFX))], 'mpbi',
              '%s : %s -onto-> ran %s' % (FFX, UUX, FFX))
    dom = st([uufin, st([ffo], 'a1i', '%s : %s -onto-> ran %s' % (FFX, UUX, FFX)), w.inst('fodomfi')], 'syl2anc',
             'ran %s ~<_ %s' % (FFX, UUX))
    h2 = st([dom, w.inst('hashdomi')], 'syl', '( # ` ran %s ) <_ ( # ` %s )' % (FFX, UUX))
    rnfin = st([st([uufin, w.inst('mptfi')], 'syl', '%s e. Fin' % FFX), w.inst('rnfi')], 'syl', 'ran %s e. Fin' % FFX)
    sbss = st([], 'smshbad', '%s C_ ran %s' % (SBX, FFX))
    h1 = st([rnfin, sbss, w.inst('hashssle')], 'syl2anc', '( # ` %s ) <_ ( # ` ran %s )' % (SBX, FFX))
    # hashiun
    AJU = '( %s /\\ u e. %s )' % (AJ, XJ)
    fst = w.s([w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (AJU, XJ)), w.inst('xp1st')], 'syl', '( %s -> ( 1st ` u ) e. { j } )' % AJU),
               w.inst('elsni')], 'syl', '( %s -> ( 1st ` u ) = j )' % AJU)
    alu = stj([fst], 'ralrimiva', 'A. u e. %s ( 1st ` u ) = j' % XJ)
    alju = st([alu], 'ralrimiva', 'A. j e. %s A. u e. %s ( 1st ` u ) = j' % (RNG, XJ))
    dsj = st([alju, w.inst('invdisj')], 'syl', 'Disj_ j e. %s %s' % (RNG, XJ))
    hiun = st([rfin, xjfin, dsj], 'hashiun', '( # ` %s ) = sum_ j e. %s ( # ` %s )' % (UUX, RNG, XJ))
    hxp = stj([snf, twfin, w.inst('hashxp')], 'syl2anc', '( # ` %s ) = ( ( # ` { j } ) x. ( # ` %s ) )' % (XJ, TWJ))
    hsn = w.s([w.s([], 'vex', 'j e. _V'), w.inst('hashsng')], 'ax-mp', '( # ` { j } ) = 1')
    hsn2 = stj([stj([hsn], 'a1i', '( # ` { j } ) = 1')], 'oveq1d', '( ( # ` { j } ) x. ( # ` %s ) ) = ( 1 x. ( # ` %s ) )' % (TWJ, TWJ))
    twcn = stj([stj([twfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TWJ)], 'nn0cnd', '( # ` %s ) e. CC' % TWJ)
    body = stj([stj([hxp, hsn2], 'eqtrd', '( # ` %s ) = ( 1 x. ( # ` %s ) )' % (XJ, TWJ)), stj([twcn], 'mullidd', '( 1 x. ( # ` %s ) ) = ( # ` %s )' % (TWJ, TWJ))],
                'eqtrd', '( # ` %s ) = ( # ` %s )' % (XJ, TWJ))
    seq = st([body], 'sumeq2dv', 'sum_ j e. %s ( # ` %s ) = %s' % (RNG, XJ, v5lib.SUMTW('X', 'E')))
    heq = st([hiun, seq], 'eqtrd', '( # ` %s ) = %s' % (UUX, v5lib.SUMTW('X', 'E')))
    sbfin = st([st([], 'fzfid', '( 0 ... X ) e. Fin'), w.inst('rabfi')], 'syl', '%s e. Fin' % SBX)
    r1 = st([st([sbfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SBX)], 'nn0red', '( # ` %s ) e. RR' % SBX)
    r2 = st([st([rnfin, w.inst('hashcl')], 'syl', '( # ` ran %s ) e. NN0' % FFX)], 'nn0red', '( # ` ran %s ) e. RR' % FFX)
    r3 = st([st([uufin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % UUX)], 'nn0red', '( # ` %s ) e. RR' % UUX)
    h12 = st([r1, r2, r3, h1, h2], 'letrd', '( # ` %s ) <_ ( # ` %s )' % (SBX, UUX))
    w.qed([h12, heq], 'breqtrd', v5lib.STATEMENTS['smshcnt'])
    return run(w)


# ------------------------------------------------------------------ smshsplit
def smshsplit():
    w = W('smshsplit', 'The primes up to X are the good ones and the bad ones: ppi X <_ # good + # bad '
                       '(Lean: hsub, hsplit of smooth_shifted_weak).')
    st = mkst(w, A0)
    xnn, ere = a0facts(w, st)
    PS = '( ( 2 ... X ) i^i Prime )'
    ppi = st([st([xnn], 'nnzd', 'X e. ZZ'), w.inst('ppival2')], 'syl', '( ppi ` X ) = ( # ` %s )' % PS)
    A1 = '( %s /\\ p e. %s )' % (A0, PS)
    st1 = mkst(w, A1)
    pin = st1([st1([], 'simpr', 'p e. %s' % PS), w.s([], 'elin', '( p e. %s <-> ( p e. ( 2 ... X ) /\\ p e. Prime ) )' % PS)],
              'sylib', '( p e. ( 2 ... X ) /\\ p e. Prime )')
    p2x = st1([pin], 'simpld', 'p e. ( 2 ... X )'); ppr = st1([pin], 'simprd', 'p e. Prime')
    ss = w.s([w.s([], '2eluzge0', '2 e. ( ZZ>= ` 0 )'), w.inst('fzss1')], 'ax-mp', '( 2 ... X ) C_ ( 0 ... X )')
    p0x = st1([st1([ss], 'a1i', '( 2 ... X ) C_ ( 0 ... X )'), p2x], 'sseldd', 'p e. ( 0 ... X )')
    INNP = v5lib.INNER('X', 'E', a='p')
    slg, gbody = subst(w, 'a', 'p', '( a e. Prime /\\ %s )' % INN)
    slb, bbody = subst(w, 'a', 'p', '( a e. Prime /\\ -. %s )' % INN)
    elg = w.s([slg], 'elrab', '( p e. %s <-> ( p e. ( 0 ... X ) /\\ %s ) )' % (SGX, gbody))
    elb = w.s([slb], 'elrab', '( p e. %s <-> ( p e. ( 0 ... X ) /\\ %s ) )' % (SBX, bbody))
    AG = '( %s /\\ %s )' % (A1, INNP); AB = '( %s /\\ -. %s )' % (A1, INNP)
    ing = w.s([w.s([p0x], 'adantr', '( %s -> p e. ( 0 ... X ) )' % AG),
               w.s([w.s([ppr], 'adantr', '( %s -> p e. Prime )' % AG), w.s([], 'simpr', '( %s -> %s )' % (AG, INNP))], 'jca',
                   '( %s -> %s )' % (AG, gbody)), elg], 'sylanbrc', '( %s -> p e. %s )' % (AG, SGX))
    inb = w.s([w.s([p0x], 'adantr', '( %s -> p e. ( 0 ... X ) )' % AB),
               w.s([w.s([ppr], 'adantr', '( %s -> p e. Prime )' % AB), w.s([], 'simpr', '( %s -> -. %s )' % (AB, INNP))], 'jca',
                   '( %s -> %s )' % (AB, bbody)), elb], 'sylanbrc', '( %s -> p e. %s )' % (AB, SBX))
    orim = st1([w.s([ing], 'ex', '( %s -> ( %s -> p e. %s ) )' % (A1, INNP, SGX)),
                w.s([inb], 'ex', '( %s -> ( -. %s -> p e. %s ) )' % (A1, INNP, SBX))], 'orim12d',
               '( ( %s \\/ -. %s ) -> ( p e. %s \\/ p e. %s ) )' % (INNP, INNP, SGX, SBX))
    por = st1([w.s([], 'exmid', '( %s \\/ -. %s )' % (INNP, INNP)), orim], 'mpi', '( p e. %s \\/ p e. %s )' % (SGX, SBX))
    pun = st1([por, w.s([], 'elun', '( p e. ( %s u. %s ) <-> ( p e. %s \\/ p e. %s ) )' % (SGX, SBX, SGX, SBX))], 'sylibr',
              'p e. ( %s u. %s )' % (SGX, SBX))
    sub = st([w.s([pun], 'ex', '( %s -> ( p e. %s -> p e. ( %s u. %s ) ) )' % (A0, PS, SGX, SBX))], 'ssrdv',
             '%s C_ ( %s u. %s )' % (PS, SGX, SBX))
    fz = st([], 'fzfid', '( 0 ... X ) e. Fin')
    gfin = st([fz, w.inst('rabfi')], 'syl', '%s e. Fin' % SGX); bfin = st([fz, w.inst('rabfi')], 'syl', '%s e. Fin' % SBX)
    ufin = st([gfin, bfin, w.inst('unfi')], 'syl2anc', '( %s u. %s ) e. Fin' % (SGX, SBX))
    h1 = st([ufin, sub, w.inst('hashssle')], 'syl2anc', '( # ` %s ) <_ ( # ` ( %s u. %s ) )' % (PS, SGX, SBX))
    h2 = st([gfin, bfin, w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (SGX, SBX, SGX, SBX))
    psfin = st([st([], 'fzfid', '( 2 ... X ) e. Fin'), w.inst('infi')], 'syl', '%s e. Fin' % PS)
    r1 = st([st([psfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % PS)], 'nn0red', '( # ` %s ) e. RR' % PS)
    r2 = st([st([ufin, w.inst('hashcl')], 'syl', '( # ` ( %s u. %s ) ) e. NN0' % (SGX, SBX))], 'nn0red', '( # ` ( %s u. %s ) ) e. RR' % (SGX, SBX))
    r3 = st([st([st([gfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SGX)], 'nn0red', '( # ` %s ) e. RR' % SGX),
             st([st([bfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SBX)], 'nn0red', '( # ` %s ) e. RR' % SBX)], 'readdcld',
            '( ( # ` %s ) + ( # ` %s ) ) e. RR' % (SGX, SBX))
    h12 = st([r1, r2, r3, h1, h2], 'letrd', '( # ` %s ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (PS, SGX, SBX))
    w.qed([ppi, h12], 'eqbrtrd', v5lib.STATEMENTS['smshsplit'])
    return run(w)


if __name__ == '__main__':
    smshbad(); smshcnt(); smshsplit()
