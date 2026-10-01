"""Sortie GF1, section B: the entire difference quotient PH (gf1edvc, gf1ph, gf1phv).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_b.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *

only = sys.argv[1:]
ES = '( exp ` ( W x. s ) )'
S['gf1edvc'] = '( W e. CC -> ( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> ( %s x. W ) ) )' % (ES, ES)


def gen_edvc():
    w = W('gf1edvc', 'The complex derivative of ` s |-> exp ( W s ) ` is ` exp ( W s ) W ` ( ~ dvmptco , ~ dvef ).')
    A = 'W e. CC'
    d = mk(w, A)
    As = '( W e. CC /\\ s e. CC )'
    ds = mk(w, As)
    idw = w.s([], 'id', '( W e. CC -> W e. CC )')
    cc = a1(w, A, 'cnelprrecn', 'CC e. { RR , CC }')
    did = d('dvmptid', [cc], '( CC _D ( s e. CC |-> s ) ) = ( s e. CC |-> 1 )')
    sc = w.s([], 'simpr', '( %s -> s e. CC )' % As)
    one = ds('1cnd', [], '1 e. CC')
    dml = d('dvmptcmul', [cc, sc, one, did, idw], '( CC _D ( s e. CC |-> ( W x. s ) ) ) = ( s e. CC |-> ( W x. 1 ) )')
    wc = lift(w, idw, As)
    ws_ = ds('mulcld', [wc, sc], '( W x. s ) e. CC')
    w1 = ds('mulcld', [wc, one], '( W x. 1 ) e. CC')
    Ay = '( W e. CC /\\ y e. CC )'
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % Ay)
    ey = D(w, Ay, 'efcld', [yc], '( exp ` y ) e. CC')
    ef = a1(w, A, 'eff', 'exp : CC --> CC')
    feq = d('feqmptd', [ef], 'exp = ( y e. CC |-> ( exp ` y ) )')
    dve = a1(w, A, 'dvef', '( CC _D exp ) = exp')
    feq2 = d('eqcomd', [feq], '( y e. CC |-> ( exp ` y ) ) = exp')
    o2 = d('oveq2d', [feq2], '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( CC _D exp )')
    e1 = d('eqtrd', [o2, dve], '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = exp')
    e2 = d('eqtrd', [e1, feq], '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( y e. CC |-> ( exp ` y ) )')
    fv = w.s([], 'fveq2', '( y = ( W x. s ) -> ( exp ` y ) = %s )' % ES)
    co = d('dvmptco', [cc, cc, ws_, w1, ey, ey, dml, e2, fv, fv],
           '( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> ( %s x. ( W x. 1 ) ) )' % (ES, ES))
    mr = ds('mulridd', [wc], '( W x. 1 ) = W')
    o3 = ds('oveq2d', [mr], '( %s x. ( W x. 1 ) ) = ( %s x. W )' % (ES, ES))
    mp = d('mpteq2dva', [o3], '( s e. CC |-> ( %s x. ( W x. 1 ) ) ) = ( s e. CC |-> ( %s x. W ) )' % (ES, ES))
    fin = d('eqtrd', [co, mp], split_imp(S['gf1edvc'])[1])
    w.qed([fin], 'idi', S['gf1edvc'])
    return run(w, only)


EC = '( s e. CC |-> ( ( exp ` ( C x. s ) ) - 1 ) )'
AA = '( -u 1 + ( _i x. -u 1 ) )'
BB = '( 1 + ( _i x. 1 ) )'


def gen_ph():
    w = W('gf1ph', 'The difference quotient ` PH ( C , w ) ` of ` w |-> exp ( C w ) ` at ` 0 ` , extended by its derivative ` C ` , is entire ( ~ zl3qvp on ` exp ( C w ) - 1 ` ).')
    A = 'C e. CC'
    d = mk(w, A)
    As = '( C e. CC /\\ s e. CC )'
    ds = mk(w, As)
    idc = w.s([], 'id', '( C e. CC -> C e. CC )')
    cc = a1(w, A, 'cnelprrecn', 'CC e. { RR , CC }')
    sc = w.s([], 'simpr', '( %s -> s e. CC )' % As)
    cs = lift(w, idc, As)
    csm = ds('mulcld', [cs, sc], '( C x. s ) e. CC')
    ecs = ds('efcld', [csm], '( exp ` ( C x. s ) ) e. CC')
    ecc = ds('mulcld', [ecs, cs], '( ( exp ` ( C x. s ) ) x. C ) e. CC')
    one = ds('1cnd', [], '1 e. CC')
    zero = ds('0cnd', [], '0 e. CC')
    dex = w.s([idc, w.inst('gf1edvc')], 'syl', '( C e. CC -> ( CC _D ( s e. CC |-> ( exp ` ( C x. s ) ) ) ) = ( s e. CC |-> ( ( exp ` ( C x. s ) ) x. C ) ) )')
    dc1 = d('dvmptc', [cc, d('1cnd', [], '1 e. CC')], '( CC _D ( s e. CC |-> 1 ) ) = ( s e. CC |-> 0 )')
    DER = '( s e. CC |-> ( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) )'
    dE = d('dvmptsub', [cc, ecs, ecc, one, zero, dex, dc1], '( CC _D %s ) = %s' % (EC, DER))
    body = '( ( exp ` ( C x. s ) ) - 1 )'
    bcc = ds('subcld', [ecs, one], '%s e. CC' % body)
    dcc = ds('subcld', [ecc, zero], '( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) e. CC')
    ra = d('ralrimiva', [bcc], 'A. s e. CC %s e. CC' % body)
    rb = d('ralrimiva', [dcc], 'A. s e. CC ( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) e. CC')
    j = d('jca', [dE, rb], '( ( CC _D %s ) = %s /\\ A. s e. CC ( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) e. CC )' % (EC, DER))
    j2 = d('jca', [ra, j], '( A. s e. CC %s e. CC /\\ ( ( CC _D %s ) = %s /\\ A. s e. CC ( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) e. CC ) )' % (body, EC, DER))
    hE = w.s([j2, w.inst('z6ehdv')], 'syl', '( C e. CC -> %s )' % HOL(EC, 'CC'))
    # E ` 0 = 0 and ( CC _D E ) ` 0 = C
    z0 = a1(w, A, '0cn', '0 e. CC')
    c0 = d('mul01d', [idc], '( C x. 0 ) = 0')
    ec0 = d('fveq2d', [c0], '( exp ` ( C x. 0 ) ) = ( exp ` 0 )')
    ec1 = d('eqtrd', [ec0, a1(w, A, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( C x. 0 ) ) = 1')
    sv = w.s([], 'oveq2', '( s = 0 -> ( C x. s ) = ( C x. 0 ) )')
    sv2 = w.s([sv], 'fveq2d', '( s = 0 -> ( exp ` ( C x. s ) ) = ( exp ` ( C x. 0 ) ) )')
    sv3 = w.s([sv2], 'oveq1d', '( s = 0 -> ( ( exp ` ( C x. s ) ) - 1 ) = ( ( exp ` ( C x. 0 ) ) - 1 ) )')
    ecm = d('subcld', [d('efcld', [d('mulcld', [idc, z0], '( C x. 0 ) e. CC')], '( exp ` ( C x. 0 ) ) e. CC'), a1(w, A, 'ax-1cn', '1 e. CC')], '( ( exp ` ( C x. 0 ) ) - 1 ) e. CC')
    fE0 = d('fvmptd', [w.s([], 'eqidd', '( C e. CC -> %s = %s )' % (EC, EC)), w.s([sv3], 'adantl', '( ( C e. CC /\\ s = 0 ) -> ( ( exp ` ( C x. s ) ) - 1 ) = ( ( exp ` ( C x. 0 ) ) - 1 ) )'), z0, ecm],
            '( %s ` 0 ) = ( ( exp ` ( C x. 0 ) ) - 1 )' % EC)
    m1 = d('oveq1d', [ec1], '( ( exp ` ( C x. 0 ) ) - 1 ) = ( 1 - 1 )')
    E0 = chain(w, A, ['( %s ` 0 )' % EC, '( ( exp ` ( C x. 0 ) ) - 1 )', '( 1 - 1 )', '0'], [fE0, m1, a1(w, A, '1m1e0', '( 1 - 1 ) = 0')])
    dv0a = d('fveq1d', [dE], '( ( CC _D %s ) ` 0 ) = ( %s ` 0 )' % (EC, DER))
    sd3 = w.s([sv2], 'oveq1d', '( s = 0 -> ( ( exp ` ( C x. s ) ) x. C ) = ( ( exp ` ( C x. 0 ) ) x. C ) )')
    sd4 = w.s([sd3], 'oveq1d', '( s = 0 -> ( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) = ( ( ( exp ` ( C x. 0 ) ) x. C ) - 0 ) )')
    e0c = d('efcld', [d('mulcld', [idc, z0], '( C x. 0 ) e. CC')], '( exp ` ( C x. 0 ) ) e. CC')
    dcm = d('subcld', [d('mulcld', [e0c, idc], '( ( exp ` ( C x. 0 ) ) x. C ) e. CC'), z0], '( ( ( exp ` ( C x. 0 ) ) x. C ) - 0 ) e. CC')
    dv0b = d('fvmptd', [w.s([], 'eqidd', '( C e. CC -> %s = %s )' % (DER, DER)), w.s([sd4], 'adantl', '( ( C e. CC /\\ s = 0 ) -> ( ( ( exp ` ( C x. s ) ) x. C ) - 0 ) = ( ( ( exp ` ( C x. 0 ) ) x. C ) - 0 ) )'), z0, dcm],
             '( %s ` 0 ) = ( ( ( exp ` ( C x. 0 ) ) x. C ) - 0 )' % DER)
    dv0c = d('subid1d', [d('mulcld', [e0c, idc], '( ( exp ` ( C x. 0 ) ) x. C ) e. CC')], '( ( ( exp ` ( C x. 0 ) ) x. C ) - 0 ) = ( ( exp ` ( C x. 0 ) ) x. C )')
    dv0d = d('oveq1d', [ec1], '( ( exp ` ( C x. 0 ) ) x. C ) = ( 1 x. C )')
    dv0e = d('mullidd', [idc], '( 1 x. C ) = C')
    DV0 = chain(w, A, ['( ( CC _D %s ) ` 0 )' % EC, '( %s ` 0 )' % DER, '( ( ( exp ` ( C x. 0 ) ) x. C ) - 0 )', '( ( exp ` ( C x. 0 ) ) x. C )', '( 1 x. C )', 'C'],
                [dv0a, dv0b, dv0c, dv0d, dv0e])
    # the zl3qvp instance
    CM = '( j e. NN0 |-> ( ( y e. ( ( %s crect %s ) \\ { 0 } ) |-> ( ( %s ` y ) / ( ( y - 0 ) ^ ( j + 1 ) ) ) ) rectint <. %s , %s >. ) )' % (AA, BB, EC, AA, BB)
    Q = '( w e. CC |-> if ( w = 0 , ( ( %s ` 1 ) / ( 2 x. ( _i x. _pi ) ) ) , ( ( %s ` w ) / ( ( w - 0 ) ^ 1 ) ) ) )' % (CM, EC)
    sub = {'F': EC, 'D': 'CC', 'A': AA, 'B': BB, 'P': '0', 'R': '1', 'M': 'm', 'C': CM, 'Q': Q, 'z': 'v'}
    zst = tsub(stmt('zl3qvp'), sub)
    zante, zconc = split_imp(zst)
    Am = '( ( C e. CC /\\ m e. RR ) /\\ A. u e. %s ( abs ` ( %s ` u ) ) <_ m )' % ('FRX', EC)
    FR = zante.split(' A. u e. ', 1)[1].split(' ( abs ` ', 1)[0]
    Am = Am.replace('FRX', FR)
    dm = mk(w, Am)
    lf = lambda st: lift(w, st, Am)
    facts = {}
    facts[HOL(EC, 'CC')] = lf(hE)
    # closed facts about the rectangle, lifted to Am
    def cl_(ref, f, hyps=()):
        return a1(w, Am, ref, f, hyps)
    n1c = w.s([], 'neg1cn', '-u 1 e. CC'); n1r = w.s([], 'neg1rr', '-u 1 e. RR')
    ic = w.s([], 'ax-icn', '_i e. CC'); c1 = w.s([], 'ax-1cn', '1 e. CC'); r1 = w.s([], '1re', '1 e. RR')
    aac = cl_('addcli', '%s e. CC' % AA, [n1c, w.s([ic, n1c], 'mulcli', '( _i x. -u 1 ) e. CC')])
    bbc = cl_('addcli', '%s e. CC' % BB, [c1, w.s([ic, c1], 'mulcli', '( _i x. 1 ) e. CC')])
    rea = cl_('ax-mp', '( Re ` %s ) = -u 1' % AA, [w.s([n1r, n1r], 'pm3.2i', '( -u 1 e. RR /\\ -u 1 e. RR )'), w.inst('crre')])
    ima = cl_('ax-mp', '( Im ` %s ) = -u 1' % AA, [w.s([n1r, n1r], 'pm3.2i', '( -u 1 e. RR /\\ -u 1 e. RR )'), w.inst('crim')])
    reb = cl_('ax-mp', '( Re ` %s ) = 1' % BB, [w.s([r1, r1], 'pm3.2i', '( 1 e. RR /\\ 1 e. RR )'), w.inst('crre')])
    imb = cl_('ax-mp', '( Im ` %s ) = 1' % BB, [w.s([r1, r1], 'pm3.2i', '( 1 e. RR /\\ 1 e. RR )'), w.inst('crim')])
    re0 = cl_('re0', '( Re ` 0 ) = 0'); im0 = cl_('im0', '( Im ` 0 ) = 0')
    atoms = ['( Re ` %s )' % AA, '( Im ` %s )' % AA, '( Re ` %s )' % BB, '( Im ` %s )' % BB, '( Re ` 0 )', '( Im ` 0 )']
    eqs = [rea, ima, reb, imb, re0, im0]
    # closure facts for the Re/Im atoms
    cl_re = Closure(w, Am)
    for a_, arg, st in [(atoms[0], AA, aac), (atoms[1], AA, aac), (atoms[2], BB, bbc), (atoms[3], BB, bbc), (atoms[4], '0', None), (atoms[5], '0', None)]:
        ref = 'recld' if a_.startswith('( Re') else 'imcld'
        argst = st if st is not None else cl_('0cn', '0 e. CC')
        cl_re.leaf(a_, 'RR', D(w, Am, ref, [argst], '%s e. RR' % a_))
    for g in ['( Re ` %s ) < ( Re ` 0 )' % AA, '( Re ` 0 ) < ( Re ` %s )' % BB, '( Im ` %s ) < ( Im ` 0 )' % AA, '( Im ` 0 ) < ( Im ` %s )' % BB,
              '1 <_ ( ( Re ` 0 ) - ( Re ` %s ) )' % AA, '1 <_ ( ( Re ` %s ) - ( Re ` 0 ) )' % BB,
              '1 <_ ( ( Im ` 0 ) - ( Im ` %s ) )' % AA, '1 <_ ( ( Im ` %s ) - ( Im ` 0 ) )' % BB]:
        facts[g] = lin.linarith(w, Am, eqs, g, closure=cl_re)
    facts['%s e. CC' % AA] = aac
    facts['%s e. CC' % BB] = bbc
    facts['0 e. CC'] = cl_('0cn', '0 e. CC')
    facts['1 e. RR'] = cl_('1re', '1 e. RR')
    facts['0 < 1'] = cl_('0lt1', '0 < 1')
    facts['( %s crect %s ) C_ CC' % (AA, BB)] = D(w, Am, 'syl2anc', [aac, bbc, w.inst('crectss')], '( %s crect %s ) C_ CC' % (AA, BB))
    facts['m e. RR'] = D(w, Am, 'simplr', [], 'm e. RR') if False else proj(w, Am, 'm e. RR')
    facts['A. u e. %s ( abs ` ( %s ` u ) ) <_ m' % (FR, EC)] = w.s([], 'simpr', '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ m )' % (Am, FR, EC))
    facts['( %s ` 0 ) = 0' % EC] = lf(E0)
    zan = build(w, Am, zante, facts)
    hc = w.s([], 'eqid', '%s = %s' % (CM, CM))
    IFV = lambda x: 'if ( %s = 0 , %s , ( ( %s ` %s ) / ( ( %s - 0 ) ^ 1 ) ) )' % (x, '( ( %s ` 1 ) / ( 2 x. ( _i x. _pi ) ) )' % CM, EC, x, x)
    q1 = w.s([], 'eqeq1', '( w = v -> ( w = 0 <-> v = 0 ) )')
    q2 = w.s([], 'fveq2', '( w = v -> ( %s ` w ) = ( %s ` v ) )' % (EC, EC))
    q3 = w.s([], 'oveq1', '( w = v -> ( w - 0 ) = ( v - 0 ) )')
    q4 = w.s([q3], 'oveq1d', '( w = v -> ( ( w - 0 ) ^ 1 ) = ( ( v - 0 ) ^ 1 ) )')
    q5 = w.s([q2, q4], 'oveq12d', '( w = v -> ( ( %s ` w ) / ( ( w - 0 ) ^ 1 ) ) = ( ( %s ` v ) / ( ( v - 0 ) ^ 1 ) ) )' % (EC, EC))
    q6 = w.s([q1, q5], 'ifbieq2d', '( w = v -> %s = %s )' % (IFV('w'), IFV('v')))
    hq = w.s([q6], 'cbvmptv', '%s = ( v e. CC |-> %s )' % (Q, IFV('v')))
    zq = w.s([hc, hq], 'zl3qvp', zst)
    zr = w.s([zan, zq], 'syl', '( %s -> %s )' % (Am, zconc))
    qhol = dm('simpld', [zr], HOL(Q, 'CC'))
    q0 = dm('simprd', [zr], '( %s ` 0 ) = ( ( CC _D %s ) ` 0 )' % (Q, EC))
    q0c = dm('eqtrd', [q0, lf(DV0)], '( %s ` 0 ) = C' % Q)
    K1 = '( ( %s ` 1 ) / ( 2 x. ( _i x. _pi ) ) )' % CM
    IFQ = lambda x: 'if ( %s = 0 , %s , ( ( %s ` %s ) / ( ( %s - 0 ) ^ 1 ) ) )' % (x, K1, EC, x, x)
    # value of Q at 0 is K1
    # use fvmpt at 0: Q ` 0 = IFQ(0), and IFQ(0) = K1 by iftrue
    # simpler: for w = 0 the whole if collapses to K1 (iftrue)
    it0 = w.s([], 'iftrue', '( w = 0 -> %s = %s )' % (IFQ('w'), K1))
    # K1 e. CC: from q0c, Q ` 0 = C and fvmpt: prove via fvmptd with the value K1 needs K1 e. V; use the 2pi i division closure
    CMc = '( %s ` 1 )' % CM
    q0v = dm('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Am, Q, Q)), w.s([it0], 'adantl', '( ( %s /\\ w = 0 ) -> %s = %s )' % (Am, IFQ('w'), K1)), facts['0 e. CC'],
                        a1(w, Am, 'ovex', '%s e. _V' % K1)],
              '( %s ` 0 ) = %s' % (Q, K1))
    k1 = dm('eqtr3d', [q0v, q0c], '%s = C' % K1)
    # pointwise identity on CC
    Aw = '( %s /\\ w e. CC )' % Am
    dw = mk(w, Aw)
    wc = w.s([], 'simpr', '( %s -> w e. CC )' % Aw)
    sw = w.s([], 'oveq2', '( s = w -> ( C x. s ) = ( C x. w ) )')
    sw2 = w.s([sw], 'fveq2d', '( s = w -> ( exp ` ( C x. s ) ) = ( exp ` ( C x. w ) ) )')
    sw3 = w.s([sw2], 'oveq1d', '( s = w -> ( ( exp ` ( C x. s ) ) - 1 ) = ( ( exp ` ( C x. w ) ) - 1 ) )')
    A0 = '( C e. CC /\\ w e. CC )'
    d0 = mk(w, A0)
    w0c = w.s([], 'simpr', '( %s -> w e. CC )' % A0)
    cwc = d0('mulcld', [w.s([], 'simpl', '( %s -> C e. CC )' % A0), w0c], '( C x. w ) e. CC')
    ewm = d0('subcld', [d0('efcld', [cwc], '( exp ` ( C x. w ) ) e. CC'), d0('1cnd', [], '1 e. CC')], '( ( exp ` ( C x. w ) ) - 1 ) e. CC')
    few0 = d0('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, EC, EC)), w.s([sw3], 'adantl', '( ( %s /\\ s = w ) -> ( ( exp ` ( C x. s ) ) - 1 ) = ( ( exp ` ( C x. w ) ) - 1 ) )' % A0), w0c, ewm],
             '( %s ` w ) = ( ( exp ` ( C x. w ) ) - 1 )' % EC)
    few = w.s([proj(w, Aw, A0), few0], 'syl', '( %s -> ( %s ` w ) = ( ( exp ` ( C x. w ) ) - 1 ) )' % (Aw, EC))
    w0 = dw('subid1d', [wc], '( w - 0 ) = w')
    w1 = dw('oveq1d', [w0], '( ( w - 0 ) ^ 1 ) = ( w ^ 1 )')
    w2 = dw('eqtrd', [w1, dw('exp1d', [wc], '( w ^ 1 ) = w')], '( ( w - 0 ) ^ 1 ) = w')
    dq = dw('oveq12d', [few, w2], '( ( %s ` w ) / ( ( w - 0 ) ^ 1 ) ) = ( ( ( exp ` ( C x. w ) ) - 1 ) / w )' % EC)
    ife = dw('ifeq12d', [lift(w, k1, Aw), dq], '%s = %s' % (IFQ('w'), PH('C', 'w')))
    PHM = '( w e. CC |-> %s )' % PH('C', 'w')
    qeq = dm('mpteq2dva', [ife], '%s = %s' % (Q, PHM))
    he = holeq(w, Am, qeq, Q, PHM, 'CC')
    fin0 = dm('mpd', [qhol, he], HOL(PHM, 'CC'))
    A2 = '( C e. CC /\\ m e. RR )'
    ex = w.s([fin0], 'ex', '( %s -> ( A. u e. %s ( abs ` ( %s ` u ) ) <_ m -> %s ) )' % (A2, FR, EC, HOL(PHM, 'CC')))
    rl = w.s([ex], 'rexlimdva', '( C e. CC -> ( E. m e. RR A. u e. %s ( abs ` ( %s ` u ) ) <_ m -> %s ) )' % (FR, EC, HOL(PHM, 'CC')))
    # the bound m from holfrmbd
    ac = a1(w, A, 'addcli', '%s e. CC' % AA, [n1c, w.s([ic, n1c], 'mulcli', '( _i x. -u 1 ) e. CC')])
    bc = a1(w, A, 'addcli', '%s e. CC' % BB, [c1, w.s([ic, c1], 'mulcli', '( _i x. 1 ) e. CC')])
    cla = Closure(w, A)
    reqs = [a1(w, A, 'ax-mp', '( Re ` %s ) = -u 1' % AA, [w.s([n1r, n1r], 'pm3.2i', '( -u 1 e. RR /\\ -u 1 e. RR )'), w.inst('crre')]),
            a1(w, A, 'ax-mp', '( Im ` %s ) = -u 1' % AA, [w.s([n1r, n1r], 'pm3.2i', '( -u 1 e. RR /\\ -u 1 e. RR )'), w.inst('crim')]),
            a1(w, A, 'ax-mp', '( Re ` %s ) = 1' % BB, [w.s([r1, r1], 'pm3.2i', '( 1 e. RR /\\ 1 e. RR )'), w.inst('crre')]),
            a1(w, A, 'ax-mp', '( Im ` %s ) = 1' % BB, [w.s([r1, r1], 'pm3.2i', '( 1 e. RR /\\ 1 e. RR )'), w.inst('crim')])]
    for a_, st in [(atoms[0], ac), (atoms[1], ac), (atoms[2], bc), (atoms[3], bc)]:
        ref = 'recld' if a_.startswith('( Re') else 'imcld'
        cla.leaf(a_, 'RR', D(w, A, ref, [st], '%s e. RR' % a_))
    f2 = {'%s e. CC' % AA: ac, '%s e. CC' % BB: bc}
    f2['( Re ` %s ) <_ ( Re ` %s )' % (AA, BB)] = lin.linarith(w, A, reqs, '( Re ` %s ) <_ ( Re ` %s )' % (AA, BB), closure=cla)
    f2['( Im ` %s ) <_ ( Im ` %s )' % (AA, BB)] = lin.linarith(w, A, reqs, '( Im ` %s ) <_ ( Im ` %s )' % (AA, BB), closure=cla)
    f2['%s e. ( CC -cn-> CC )' % EC] = d('simpld', [hE], '%s e. ( CC -cn-> CC )' % EC)
    j0 = d('jca', [ac, bc], '( %s e. CC /\\ %s e. CC )' % (AA, BB))
    j1 = d('jca', [f2['( Re ` %s ) <_ ( Re ` %s )' % (AA, BB)], f2['( Im ` %s ) <_ ( Im ` %s )' % (AA, BB)]], '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (AA, BB, AA, BB))
    j01 = d('jca', [j0, j1], '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (AA, BB, AA, BB, AA, BB))
    fru = w.s([j01, w.inst('crectfru')], 'syl', '( C e. CC -> %s C_ ( %s crect %s ) )' % (FR, AA, BB))
    frc = d('sstrd', [fru, d('syl2anc', [ac, bc, w.inst('crectss')], '( %s crect %s ) C_ CC' % (AA, BB))], '%s C_ CC' % FR)
    j2 = d('jca', [f2['%s e. ( CC -cn-> CC )' % EC], frc], '( %s e. ( CC -cn-> CC ) /\\ %s C_ CC )' % (EC, FR))
    j3 = d('3jca', [j0, j1, j2], '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( %s e. ( CC -cn-> CC ) /\\ %s C_ CC ) )' % (AA, BB, AA, BB, AA, BB, EC, FR))
    bnd = w.s([j3, w.inst('holfrmbd')], 'syl', '( C e. CC -> E. m e. RR A. u e. %s ( abs ` ( %s ` u ) ) <_ m )' % (FR, EC))
    fin = d('mpd', [bnd, rl], HOL(PHM, 'CC'))
    w.qed([fin], 'idi', S['gf1ph'])
    return run(w, only)


def gen_phv():
    w = W('gf1phv', 'Values of ` PH ` : ` PH ( C , W ) W = exp ( C W ) - 1 ` for every ` W ` , and ` PH ( C , 0 ) = C ` .')
    A, Cc = split_imp(S['gf1phv'])
    d = mk(w, A)
    P = PH('C', 'W')
    cc_ = proj(w, A, 'C e. CC'); wc_ = proj(w, A, 'W e. CC')
    num = '( ( exp ` ( C x. W ) ) - 1 )'
    # branch W = 0
    A1 = '( %s /\\ W = 0 )' % A
    d1 = mk(w, A1)
    w0 = w.s([], 'simpr', '( %s -> W = 0 )' % A1)
    it = d1('iftrued', [w0], '%s = C' % P)
    pc1 = d1('eqeltrd', [it, lift(w, cc_, A1)], '%s e. CC' % P)
    m1 = d1('oveq12d', [it, w0], '( %s x. W ) = ( C x. 0 )' % P)
    m2 = d1('eqtrd', [m1, d1('mul01d', [lift(w, cc_, A1)], '( C x. 0 ) = 0')], '( %s x. W ) = 0' % P)
    e1 = d1('oveq2d', [w0], '( C x. W ) = ( C x. 0 )')
    e2 = d1('eqtrd', [e1, d1('mul01d', [lift(w, cc_, A1)], '( C x. 0 ) = 0')], '( C x. W ) = 0')
    e3 = d1('fveq2d', [e2], '( exp ` ( C x. W ) ) = ( exp ` 0 )')
    e4 = d1('eqtrd', [e3, a1(w, A1, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( C x. W ) ) = 1')
    e5 = d1('oveq1d', [e4], '%s = ( 1 - 1 )' % num)
    e6 = d1('eqtrd', [e5, a1(w, A1, '1m1e0', '( 1 - 1 ) = 0')], '%s = 0' % num)
    mm1 = d1('eqtr4d', [m2, e6], '( %s x. W ) = %s' % (P, num))
    b1 = d1('jca', [pc1, mm1], '( %s e. CC /\\ ( %s x. W ) = %s )' % (P, P, num))
    # branch W =/= 0
    A2 = '( %s /\\ W =/= 0 )' % A
    d2 = mk(w, A2)
    wn = w.s([], 'simpr', '( %s -> W =/= 0 )' % A2)
    iff = d2('ifnefalse', [wn] if False else [], '') if False else w.s([wn, w.inst('ifnefalse')], 'syl', '( %s -> %s = ( %s / W ) )' % (A2, P, num))
    nc = d2('subcld', [d2('efcld', [d2('mulcld', [lift(w, cc_, A2), lift(w, wc_, A2)], '( C x. W ) e. CC')], '( exp ` ( C x. W ) ) e. CC'), d2('1cnd', [], '1 e. CC')], '%s e. CC' % num)
    dv = d2('divcld', [nc, lift(w, wc_, A2), wn], '( %s / W ) e. CC' % num)
    pc2 = d2('eqeltrd', [iff, dv], '%s e. CC' % P)
    mq = d2('oveq1d', [iff], '( %s x. W ) = ( ( %s / W ) x. W )' % (P, num))
    dc = d2('divcan1d', [nc, lift(w, wc_, A2), wn], '( ( %s / W ) x. W ) = %s' % (num, num))
    mm2 = d2('eqtrd', [mq, dc], '( %s x. W ) = %s' % (P, num))
    b2 = d2('jca', [pc2, mm2], '( %s e. CC /\\ ( %s x. W ) = %s )' % (P, P, num))
    ex = a1(w, A, 'exmidne', '( W = 0 \\/ W =/= 0 )')
    both = d('mpjaodan', [b1, b2, ex], '( %s e. CC /\\ ( %s x. W ) = %s )' % (P, P, num))
    p0 = a1(w, A, 'ax-mp', '%s = C' % PH('C', '0'), [w.s([], 'eqid', '0 = 0'), w.inst('iftrue')])
    fin = d('3jca', [d('simpld', [both], '%s e. CC' % P), d('simprd', [both], '( %s x. W ) = %s' % (P, num)), p0], Cc)
    w.qed([fin], 'idi', S['gf1phv'])
    return run(w, only)


def gen_phb():
    w = W('gf1phb', 'Bounds on ` PH ( C , W ) ` for real ` C >_ 0 ` : ` abs PH <_ C ` on ` Re W <_ 0 ` , ` <_ C exp ( C ) ` on ` Re W <_ 1 ` , and ` abs PH abs W <_ 2 ` on ` Re W <_ 0 ` ( ~ gf1em1 ; Lean ` norm_avgExp_le_of_re_nonpos ` , ` norm_avgExp_le_of_re_le_one ` , ` norm_avgExp_le_div ` ).')
    A, Cc = split_imp(S['gf1phb'])
    P = PH('C', 'W')
    num = '( ( exp ` ( C x. W ) ) - 1 )'
    def base(X):
        """common facts under antecedent X (which contains A as a conjunct)"""
        dd = mk(w, X)
        cr = proj(w, X, 'C e. RR'); c0 = proj(w, X, '0 <_ C'); wc = proj(w, X, 'W e. CC')
        cc = dd('recnd', [cr], 'C e. CC')
        pv = dd('syl2anc', [cc, wc, w.inst('gf1phv')], split_imp(S['gf1phv'])[1].replace('C', 'C'))
        pc = dd('simp1d', [pv], '%s e. CC' % P)
        pm = dd('simp2d', [pv], '( %s x. W ) = %s' % (P, num))
        ab = dd('absmuld', [pc, wc], '( abs ` ( %s x. W ) ) = ( ( abs ` %s ) x. ( abs ` W ) )' % (P, P))
        ab2 = dd('fveq2d', [pm], '( abs ` ( %s x. W ) ) = ( abs ` %s )' % (P, num))
        key = dd('eqtr3d', [ab, ab2], '( ( abs ` %s ) x. ( abs ` W ) ) = ( abs ` %s )' % (P, num))
        cw = dd('mulcld', [cc, wc], '( C x. W ) e. CC')
        rcw = dd('syl2anc', [cr, wc, w.inst('remul2')], '( Re ` ( C x. W ) ) = ( C x. ( Re ` W ) )')
        return dict(dd=dd, cr=cr, c0=c0, wc=wc, cc=cc, pc=pc, key=key, cw=cw, rcw=rcw)
    def bound(X, K, kr, Mx, mr, m1, em):
        """( X -> ( abs ` P ) <_ K ) given K = C x. Mx: kr ( X -> K e. RR ), steps for Mx e. RR, 1 <_ Mx, exp ( Re ( C W ) ) <_ Mx; K is literally ( C x. Mx ) or C"""
        b = base(X)
        dd = b['dd']
        Xz = '( %s /\\ W = 0 )' % X
        Xn = '( %s /\\ W =/= 0 )' % X
        # W = 0
        dz = mk(w, Xz)
        it = dz('iftrued', [w.s([], 'simpr', '( %s -> W = 0 )' % Xz)], '%s = C' % P)
        ac = dz('fveq2d', [it], '( abs ` %s ) = ( abs ` C )' % P)
        ac2 = dz('absidd', [lift(w, b['cr'], Xz), lift(w, b['c0'], Xz)], '( abs ` C ) = C')
        cz = Closure(w, Xz)
        clz = dz('eqtrd', [ac, ac2], '( abs ` %s ) = C' % P)
        # C <_ K
        kz = lin.nlinarith(w, Xz, [lift(w, m1, Xz), lift(w, b['c0'], Xz)], 'C <_ %s' % K,
                           closure=Closure(w, Xz, {'C': lift(w, b['cr'], Xz), Mx: lift(w, mr, Xz)} if Mx else {'C': lift(w, b['cr'], Xz)})) if K != 'C' else dz('leidd', [lift(w, b['cr'], Xz)], 'C <_ C')
        bz = dz('eqbrtrd', [clz, kz], '( abs ` %s ) <_ %s' % (P, K))
        # W =/= 0
        dn = mk(w, Xn)
        wn = w.s([], 'simpr', '( %s -> W =/= 0 )' % Xn)
        E1 = dn('syl', [dn('jca', [lift(w, b['cw'], Xn), dn('3jca', [lift(w, mr, Xn), lift(w, m1, Xn), lift(w, em, Xn)], '( %s e. RR /\\ 1 <_ %s /\\ ( exp ` ( Re ` ( C x. W ) ) ) <_ %s )' % (Mx, Mx, Mx))],
                                '( ( C x. W ) e. CC /\\ ( %s e. RR /\\ 1 <_ %s /\\ ( exp ` ( Re ` ( C x. W ) ) ) <_ %s ) )' % (Mx, Mx, Mx)), w.inst('gf1em1')],
                '( abs ` ( ( exp ` ( C x. W ) ) - 1 ) ) <_ ( %s x. ( abs ` ( C x. W ) ) )' % Mx)
        acw = dn('absmuld', [lift(w, b['cc'], Xn), lift(w, b['wc'], Xn)], '( abs ` ( C x. W ) ) = ( ( abs ` C ) x. ( abs ` W ) )')
        acC = dn('absidd', [lift(w, b['cr'], Xn), lift(w, b['c0'], Xn)], '( abs ` C ) = C')
        acw2 = dn('eqtrd', [acw, dn('oveq1d', [acC], '( ( abs ` C ) x. ( abs ` W ) ) = ( C x. ( abs ` W ) )')], '( abs ` ( C x. W ) ) = ( C x. ( abs ` W ) )')
        r1 = dn('oveq2d', [acw2], '( %s x. ( abs ` ( C x. W ) ) ) = ( %s x. ( C x. ( abs ` W ) ) )' % (Mx, Mx))
        aw = dn('abscld', [lift(w, b['wc'], Xn)], '( abs ` W ) e. RR')
        awp = dn('absgt0d', [lift(w, b['wc'], Xn), wn] if False else [lift(w, b['wc'], Xn), wn], '0 < ( abs ` W )') if False else w.s([lift(w, b['wc'], Xn), wn, w.inst('absrpcl')], 'syl2anc', '( %s -> ( abs ` W ) e. RR+ )' % Xn)
        mrn = lift(w, mr, Xn)
        r2 = dn('mulassd' if False else 'eqtrd', [], '') if False else None
        # ( Mx x. ( C x. |W| ) ) = ( K x. |W| ) with K = ( C x. Mx )
        Kt = K
        eqk = lin.lineq(w, Xn, '( %s x. ( C x. ( abs ` W ) ) )' % Mx, '( %s x. ( abs ` W ) )' % Kt, [],
                        closure=Closure(w, Xn, {'C': lift(w, b['cr'], Xn), Mx: mrn, '( abs ` W )': aw}), products=True)
        chainb = chain(w, Xn, ['( ( abs ` %s ) x. ( abs ` W ) )' % P, '( abs ` %s )' % num, '( %s x. ( abs ` ( C x. W ) ) )' % Mx,
                               '( %s x. ( C x. ( abs ` W ) ) )' % Mx, '( %s x. ( abs ` W ) )' % Kt],
                       [lift(w, b['key'], Xn), E1, r1, eqk], ['=', '<_', '=', '='])
        apr = dn('abscld', [lift(w, b['pc'], Xn)], '( abs ` %s ) e. RR' % P)
        lm = dn('lemul1d', [apr, lift(w, kr, Xn), awp], '( ( abs ` %s ) <_ %s <-> ( ( abs ` %s ) x. ( abs ` W ) ) <_ ( %s x. ( abs ` W ) ) )' % (P, Kt, P, Kt))
        bn = dn('mpbird', [chainb, lm], '( abs ` %s ) <_ %s' % (P, Kt))
        ex = a1(w, X, 'exmidne', '( W = 0 \\/ W =/= 0 )')
        return w.s([bz, bn, ex], 'mpjaodan', '( %s -> ( abs ` %s ) <_ %s )' % (X, P, K))
    # (i) Re W <_ 0, M = 1, K = ( C x. 1 )
    X1 = '( %s /\\ ( Re ` W ) <_ 0 )' % A
    d1 = mk(w, X1)
    b1 = base(X1)
    one = a1(w, X1, '1re', '1 e. RR')
    le11 = d1('leidd', [one], '1 <_ 1')
    rw = d1('recld', [b1['wc']], '( Re ` W ) e. RR')
    cre = lin.nlinarith(w, X1, [b1['c0'], w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 0 )' % X1)], '( C x. ( Re ` W ) ) <_ 0',
                        closure=Closure(w, X1, {'C': b1['cr'], '( Re ` W )': rw}))
    rcw0 = d1('eqbrtrd', [b1['rcw'], cre], '( Re ` ( C x. W ) ) <_ 0')
    rcr = d1('recld', [b1['cw']], '( Re ` ( C x. W ) ) e. RR')
    ef1 = d1('mpbid', [rcw0, d1('syl2anc', [rcr, a1(w, X1, '0re', '0 e. RR'), w.inst('efle')], '( ( Re ` ( C x. W ) ) <_ 0 <-> ( exp ` ( Re ` ( C x. W ) ) ) <_ ( exp ` 0 ) )')],
              '( exp ` ( Re ` ( C x. W ) ) ) <_ ( exp ` 0 )')
    ef2 = d1('breqtrd', [ef1, a1(w, X1, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( Re ` ( C x. W ) ) ) <_ 1')
    K1 = '( C x. 1 )'
    k1r = d1('remulcld', [b1['cr'], one], '%s e. RR' % K1)
    bi = bound(X1, K1, k1r, '1', one, le11, ef2)
    bi2 = d1('breqtrd', [bi, d1('mulridd', [b1['cc']], '( C x. 1 ) = C')], '( abs ` %s ) <_ C' % P)
    # (ii) Re W <_ 1, M = exp C
    X2 = '( %s /\\ ( Re ` W ) <_ 1 )' % A
    d2 = mk(w, X2)
    b2 = base(X2)
    eC = '( exp ` C )'
    ecr = d2('reefcld', [b2['cr']], '%s e. RR' % eC)
    g1 = d2('syl2anc', [b2['cr'], b2['c0'], w.inst('g3t4')] if False else [d2('jca', [b2['cr'], b2['c0']], '( C e. RR /\\ 0 <_ C )'), w.inst('g3t4')], '1 <_ %s' % eC)
    g1 = w.s([d2('jca', [b2['cr'], b2['c0']], '( C e. RR /\\ 0 <_ C )'), w.inst('g3t4')], 'syl', '( %s -> 1 <_ %s )' % (X2, eC))
    rw2 = d2('recld', [b2['wc']], '( Re ` W ) e. RR')
    cre2 = lin.nlinarith(w, X2, [b2['c0'], w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 1 )' % X2)], '( C x. ( Re ` W ) ) <_ C',
                         closure=Closure(w, X2, {'C': b2['cr'], '( Re ` W )': rw2}))
    rcwC = d2('eqbrtrd', [b2['rcw'], cre2], '( Re ` ( C x. W ) ) <_ C')
    rcr2 = d2('recld', [b2['cw']], '( Re ` ( C x. W ) ) e. RR')
    efC = d2('mpbid', [rcwC, d2('syl2anc', [rcr2, b2['cr'], w.inst('efle')], '( ( Re ` ( C x. W ) ) <_ C <-> ( exp ` ( Re ` ( C x. W ) ) ) <_ %s )' % eC)],
              '( exp ` ( Re ` ( C x. W ) ) ) <_ %s' % eC)
    K2 = '( C x. %s )' % eC
    k2r = d2('remulcld', [b2['cr'], ecr], '%s e. RR' % K2)
    bii = bound(X2, K2, k2r, eC, ecr, g1, efC)
    # (iii) Re W <_ 0, W =/= 0: |P| |W| = |exp(CW) - 1| <_ exp(Re(CW)) + 1 <_ 2
    X3 = '( %s /\\ ( ( Re ` W ) <_ 0 /\\ W =/= 0 ) )' % A
    d3 = mk(w, X3)
    b3 = base(X3)
    ecw = d3('efcld', [b3['cw']], '( exp ` ( C x. W ) ) e. CC')
    tri = d3('syl2anc', [ecw, d3('1cnd', [], '1 e. CC'), w.inst('abs2dif2')], '( abs ` %s ) <_ ( ( abs ` ( exp ` ( C x. W ) ) ) + ( abs ` 1 ) )' % num)
    ae = d3('syl', [b3['cw'], w.inst('absef')], '( abs ` ( exp ` ( C x. W ) ) ) = ( exp ` ( Re ` ( C x. W ) ) )')
    rw3 = d3('recld', [b3['wc']], '( Re ` W ) e. RR')
    cre3 = lin.nlinarith(w, X3, [b3['c0'], d3('simprld' if False else 'simprl', [], '( Re ` W ) <_ 0') if False else proj(w, X3, '( Re ` W ) <_ 0')], '( C x. ( Re ` W ) ) <_ 0',
                         closure=Closure(w, X3, {'C': b3['cr'], '( Re ` W )': rw3}))
    rcw3 = d3('eqbrtrd', [b3['rcw'], cre3], '( Re ` ( C x. W ) ) <_ 0')
    rcr3 = d3('recld', [b3['cw']], '( Re ` ( C x. W ) ) e. RR')
    ef3 = d3('mpbid', [rcw3, d3('syl2anc', [rcr3, a1(w, X3, '0re', '0 e. RR'), w.inst('efle')], '( ( Re ` ( C x. W ) ) <_ 0 <-> ( exp ` ( Re ` ( C x. W ) ) ) <_ ( exp ` 0 ) )')],
              '( exp ` ( Re ` ( C x. W ) ) ) <_ ( exp ` 0 )')
    ef4 = d3('breqtrd', [ef3, a1(w, X3, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( Re ` ( C x. W ) ) ) <_ 1')
    ab1 = a1(w, X3, 'abs1', '( abs ` 1 ) = 1')
    cl3 = Closure(w, X3)
    cl3.leaf('( exp ` ( Re ` ( C x. W ) ) )', 'RR', d3('reefcld', [rcr3], '( exp ` ( Re ` ( C x. W ) ) ) e. RR'))
    cl3.leaf('( abs ` ( exp ` ( C x. W ) ) )', 'RR', d3('abscld', [ecw], '( abs ` ( exp ` ( C x. W ) ) ) e. RR'))
    cl3.leaf('( abs ` 1 )', 'RR', d3('abscld', [d3('1cnd', [], '1 e. CC')], '( abs ` 1 ) e. RR'))
    cl3.leaf('( abs ` %s )' % num, 'RR', d3('abscld', [d3('subcld', [ecw, d3('1cnd', [], '1 e. CC')], '%s e. CC' % num)], '( abs ` %s ) e. RR' % num))
    le2 = lin.linarith(w, X3, [tri, ae, ef4, ab1], '( abs ` %s ) <_ 2' % num, closure=cl3)
    biii = d3('eqbrtrd', [b3['key'], le2], '( ( abs ` %s ) x. ( abs ` W ) ) <_ 2' % P)
    e1 = w.s([bi2], 'ex', '( %s -> ( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ C ) )' % (A, P))
    e2 = w.s([bii], 'ex', '( %s -> ( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ %s ) )' % (A, P, K2))
    e3 = w.s([biii], 'ex', '( %s -> ( ( ( Re ` W ) <_ 0 /\\ W =/= 0 ) -> ( ( abs ` %s ) x. ( abs ` W ) ) <_ 2 ) )' % (A, P))
    fin = w.s([e1, e2, e3], '3jca', S['gf1phb'])
    w.qed([fin], 'idi', S['gf1phb'])
    return run(w, only)


if __name__ == '__main__':
    gen_edvc()
    gen_ph()
    gen_phv()
    gen_phb()
