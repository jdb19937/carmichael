"""T8b: dpBodyF at the machine (Lean ` dpBodyF_runs ` ) on its installation predicate TMIdpb.

  ttrwd     resStep's word: typing, value ( a - q or L - ( q - a ) ) and below L
  ttrwdl    resStep's word has length at most M when a , q and encodeNat L do
  tmidpb    dpBodyF_runs: ~ tm2fdpb once per case of the snapshot slot (none: pop the ket;
            some: ` dup ; dup ; setIfNoneF ` by ~ tmidup and ~ tmisint ), the prefix ~ tmirst

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_k_dpb.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, nlinarith
from t8b_e_sin import L_, lift_mk, LazyBld
from t8a_e_slot import disj_leaf
from t7_v_leb import enc_facts, enc_bits

SEL = sys.argv[1:]
NONE_ = '( inr ` (/) )'
EL = '( encodeNat ` L )'
tG, tQ = '( toNat ` G )', '( toNat ` Q )'
C3 = '( ( G subTrunc Q ) ` (/) )'
C1 = '( ( Q subTrunc G ) ` (/) )'
C2 = '( ( %s subTrunc %s ) ` (/) )' % (EL, C1)
RWC = '%s <_ %s' % (tQ, tG)
assert RWD == 'if ( %s , %s , %s )' % (RWC, C3, C2), RWD
RV = 'if ( %s , ( %s - %s ) , ( L - ( %s - %s ) ) )' % (RWC, tG, tQ, tQ, tG)
PH_RW = '( ( G e. Word 2o /\\ Q e. Word 2o /\\ L e. NN ) /\\ ( %s < L /\\ %s < L ) )' % (tG, tQ)
ST_RW = '( %s -> ( %s e. Word 2o /\\ ( toNat ` %s ) = %s /\\ ( toNat ` %s ) < L ) )' % (PH_RW, RWD, RWD, RV, RWD)
MX = lambda a, b: 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (a, b, b, a)
PH_RWL = ('( ( G e. Word 2o /\\ Q e. Word 2o /\\ L e. NN0 ) /\\ ( M e. NN0 /\\ ( ( # ` G ) <_ M /\\ ( # ` Q ) <_ M /\\ ( # ` %s ) <_ M ) ) )'
          % EL)
ST_RWL = '( %s -> ( # ` %s ) <_ M )' % (PH_RWL, RWD)


def ttrwd():
    ph = PH_RW
    w = W('ttrwd', 'The word ` resStep ` leaves on ` nL ` : a bit word of value ` a - q ` if ` q <_ a ` , else '
                   '` L - ( q - a ) ` , below ` L ` (Lean ` resStep_runs ` \'s ` rl\' ` , ` toNat_subTrunc ` ).')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    gw, qw, ln = c['G e. Word 2o'], c['Q e. Word 2o'], c['L e. NN']
    gl, ql = c['%s < L' % tG], c['%s < L' % tQ]
    z2 = closed(w, ph, '0el2o', '(/) e. 2o')
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    elw = s([l0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EL))
    c3w = s([gw, qw, z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, C3))
    c1w = s([qw, gw, z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, C1))
    c2w = s([elw, c1w, z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, C2))
    rww = s([c3w, c2w], 'ifcld', '( %s -> %s e. Word 2o )' % (ph, RWD))
    tgn = s([gw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, tG))
    tqn = s([qw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, tQ))
    b0 = closed(w, ph, 'bwbn0', '( bToNat ` (/) ) = 0')
    def tst(X, Y, xw, yw, tY):
        """( ph -> ( toNat ` ( ( X subTrunc Y ) ` (/) ) ) = if ( ( toNat ` X ) < tY , 0 , ( ( toNat ` X ) - tY ) ) )"""
        tX = '( toNat ` %s )' % X
        v = s([xw, yw, z2, w.inst('tonatsubtrunc')], 'syl3anc', '( %s -> ( toNat ` ( ( %s subTrunc %s ) ` (/) ) ) = if ( %s < ( %s + ( bToNat ` (/) ) ) , 0 , ( %s - ( %s + ( bToNat ` (/) ) ) ) ) )'
              % (ph, X, Y, tX, '( toNat ` %s )' % Y, tX, '( toNat ` %s )' % Y))
        yc = s([s([s([yw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, Y))], 'nn0cnd', '( %s -> ( toNat ` %s ) e. CC )' % (ph, Y))], 'addridd',
               '( %s -> ( ( toNat ` %s ) + 0 ) = ( toNat ` %s ) )' % (ph, Y, Y))
        a0 = s([s([b0], 'oveq2d', '( %s -> ( ( toNat ` %s ) + ( bToNat ` (/) ) ) = ( ( toNat ` %s ) + 0 ) )' % (ph, Y, Y)), yc], 'eqtrd',
               '( %s -> ( ( toNat ` %s ) + ( bToNat ` (/) ) ) = ( toNat ` %s ) )' % (ph, Y, Y))
        r, new = w.rewrite(concl(w, ph, v).split(' = ', 1)[1], {'( ( toNat ` %s ) + ( bToNat ` (/) ) )' % Y: ('( toNat ` %s )' % Y, a0)}, ph)
        return s([v, r], 'eqtrd', '( %s -> ( toNat ` ( ( %s subTrunc %s ) ` (/) ) ) = %s )' % (ph, X, Y, new)), new
    v3, n3 = tst('G', 'Q', gw, qw, tQ)
    v1, n1 = tst('Q', 'G', qw, gw, tG)
    v2, n2 = tst(EL, C1, elw, c1w, None)
    tel = s([l0, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = L )' % (ph, EL))
    r2, n2b = w.rewrite(n2, {'( toNat ` %s )' % EL: ('L', tel)}, ph)
    v2 = s([v2, r2], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (ph, C2, n2b))
    RVT = lambda p: '( %s -> ( toNat ` %s ) = %s )' % (p, RWD, RV)
    cl0 = lambda p, Lf: Closure(w, p, {'tG': ('NN0', Lf(tgn)), 'tQ': ('NN0', Lf(tqn)), 'L': ('NN', Lf(ln))})
    # case q <_ a
    p1 = '( %s /\\ %s )' % (ph, RWC)
    L1 = lambda st: L_(w, p1, ph, st)
    cc = s([], 'simpr', '( %s -> %s )' % (p1, RWC))
    e1 = s([cc], 'iftrued', '( %s -> %s = %s )' % (p1, RWD, C3))
    cl = Closure(w, p1, {})
    cl.leaf(tG, 'NN0', L1(tgn)); cl.leaf(tQ, 'NN0', L1(tqn)); cl.leaf('L', 'NN', L1(ln))
    ng = s([s([cl.mem(tG, 'RR'), cl.mem(tQ, 'RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( %s <-> -. %s < %s ) )' % (p1, RWC, tG, tQ)), cc], 'mpbid',
           '( %s -> -. %s < %s )' % (p1, tG, tQ))
    t3 = s([L1(v3), s([ng], 'iffalsed', '( %s -> %s = ( %s - %s ) )' % (p1, n3, tG, tQ))], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s - %s ) )' % (p1, C3, tG, tQ))
    ta = s([s([e1], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (p1, RWD, C3)), t3], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s - %s ) )' % (p1, RWD, tG, tQ))
    rv1 = s([cc], 'iftrued', '( %s -> %s = ( %s - %s ) )' % (p1, RV, tG, tQ))
    o1 = s([ta, rv1], 'eqtr4d', RVT(p1))
    lt1 = linarith(w, p1, [L1(gl), cl.ge0(tQ)], '( %s - %s ) < L' % (tG, tQ), closure=cl)
    k1 = s([ta, lt1], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (p1, RWD))
    # case a < q
    p2 = '( %s /\\ -. %s )' % (ph, RWC)
    L2 = lambda st: L_(w, p2, ph, st)
    nc = s([], 'simpr', '( %s -> -. %s )' % (p2, RWC))
    e2 = s([nc], 'iffalsed', '( %s -> %s = %s )' % (p2, RWD, C2))
    cl2 = Closure(w, p2, {})
    cl2.leaf(tG, 'NN0', L2(tgn)); cl2.leaf(tQ, 'NN0', L2(tqn)); cl2.leaf('L', 'NN', L2(ln))
    ltq = s([s([cl2.mem(tQ, 'RR'), cl2.mem(tG, 'RR'), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s ) )' % (p2, tG, tQ, RWC)), nc], 'mpbird',
            '( %s -> %s < %s )' % (p2, tG, tQ)) if False else \
        s([s([cl2.mem(tG, 'RR'), cl2.mem(tQ, 'RR'), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s ) )' % (p2, tG, tQ, RWC)), nc], 'mpbird',
          '( %s -> %s < %s )' % (p2, tG, tQ))
    nq = linarith(w, p2, [ltq], '%s <_ %s' % (tG, tQ), closure=cl2)
    nql = s([s([cl2.mem(tG, 'RR'), cl2.mem(tQ, 'RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( %s <_ %s <-> -. %s < %s ) )' % (p2, tG, tQ, tQ, tG)), nq],
            'mpbid', '( %s -> -. %s < %s )' % (p2, tQ, tG))
    t1v = s([L2(v1), s([nql], 'iffalsed', '( %s -> %s = ( %s - %s ) )' % (p2, n1, tQ, tG))], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s - %s ) )' % (p2, C1, tQ, tG))
    r2b, n2c = w.rewrite(n2b, {'( toNat ` %s )' % C1: ('( %s - %s )' % (tQ, tG), t1v)}, p2)
    v2b = s([L2(v2), r2b], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (p2, C2, n2c))
    nl = linarith(w, p2, [L2(ql)], '-. L < ( %s - %s )' % (tQ, tG), closure=cl2) if False else None
    le2 = linarith(w, p2, [L2(ql), cl2.ge0(tG)], '( %s - %s ) <_ L' % (tQ, tG), closure=cl2)
    nl = s([s([cl2.mem('( %s - %s )' % (tQ, tG), 'RR'), cl2.mem('L', 'RR'), w.inst('lenlt')], 'syl2anc',
              '( %s -> ( ( %s - %s ) <_ L <-> -. L < ( %s - %s ) ) )' % (p2, tQ, tG, tQ, tG)), le2], 'mpbid', '( %s -> -. L < ( %s - %s ) )' % (p2, tQ, tG))
    t2 = s([v2b, s([nl], 'iffalsed', '( %s -> %s = ( L - ( %s - %s ) ) )' % (p2, n2c, tQ, tG))], 'eqtrd', '( %s -> ( toNat ` %s ) = ( L - ( %s - %s ) ) )' % (p2, C2, tQ, tG))
    tb = s([s([e2], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (p2, RWD, C2)), t2], 'eqtrd', '( %s -> ( toNat ` %s ) = ( L - ( %s - %s ) ) )' % (p2, RWD, tQ, tG))
    rv2 = s([nc], 'iffalsed', '( %s -> %s = ( L - ( %s - %s ) ) )' % (p2, RV, tQ, tG))
    o2 = s([tb, rv2], 'eqtr4d', RVT(p2))
    lt2 = linarith(w, p2, [ltq, cl2.ge0(tG)], '( L - ( %s - %s ) ) < L' % (tQ, tG), closure=cl2)
    k2 = s([tb, lt2], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (p2, RWD))
    vv = s([o1, o2], 'pm2.61dan', RVT(ph))
    kk = s([k1, k2], 'pm2.61dan', '( %s -> ( toNat ` %s ) < L )' % (ph, RWD))
    w.qed([rww, vv, kk], '3jca', ST_RW)
    return w.run()


def ttrwdl():
    ph = PH_RWL
    w = W('ttrwdl', 'The word ` resStep ` leaves on ` nL ` is no longer than ` M ` when ` a ` , ` q ` and ` encodeNat L ` '
                    'are not (Lean ` subTrunc_length ` ).')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    gw, qw, l0, mn = c['G e. Word 2o'], c['Q e. Word 2o'], c['L e. NN0'], c['M e. NN0']
    z2 = closed(w, ph, '0el2o', '(/) e. 2o')
    elw = s([l0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EL))
    g2 = {'G': gw, 'Q': qw, EL: elw}
    g2[C3] = s([gw, qw, z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, C3))
    g2[C1] = s([qw, gw, z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, C1))
    g2[C2] = s([elw, g2[C1], z2, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, C2))
    le = {'G': c['( # ` G ) <_ M'], 'Q': c['( # ` Q ) <_ M'], EL: c['( # ` %s ) <_ M' % EL]}
    cl = Closure(w, ph, {'M': ('NN0', mn)})
    for x in g2:
        cl.leaf('( # ` %s )' % x, 'NN0', s([g2[x], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, x)))
    mr = cl.mem('M', 'RR')
    def mxle(a, b):
        m = MX(a, b)
        cl.leaf(m, 'NN0', s([cl.mem('( # ` %s )' % b, 'NN0'), cl.mem('( # ` %s )' % a, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ph, m)))
        j = s([cl.mem('( # ` %s )' % a, 'RR'), cl.mem('( # ` %s )' % b, 'RR'), mr], '3jca', '( %s -> ( ( # ` %s ) e. RR /\\ ( # ` %s ) e. RR /\\ M e. RR ) )' % (ph, a, b))
        e = s([j, w.inst('maxle')], 'syl', '( %s -> ( %s <_ M <-> ( ( # ` %s ) <_ M /\\ ( # ` %s ) <_ M ) ) )' % (ph, m, a, b))
        return s([s([le[a], le[b]], 'jca', '( %s -> ( ( # ` %s ) <_ M /\\ ( # ` %s ) <_ M ) )' % (ph, a, b)), e], 'mpbird', '( %s -> %s <_ M )' % (ph, m))
    def stle(x, a, b):
        m = mxle(a, b)
        sl = s([g2[a], g2[b], z2, w.inst('subtrunclen')], 'syl3anc', '( %s -> ( # ` %s ) <_ %s )' % (ph, x, MX(a, b)))
        le[x] = s([cl.mem('( # ` %s )' % x, 'RR'), cl.mem(MX(a, b), 'RR'), mr, sl, m], 'letrd', '( %s -> ( # ` %s ) <_ M )' % (ph, x))
    stle(C3, 'G', 'Q')
    stle(C1, 'Q', 'G')
    stle(C2, EL, C1)
    f3 = s([s([cl.mem('( # ` %s )' % C3, 'NN0'), mn, le[C3]], '3jca', '( %s -> ( ( # ` %s ) e. NN0 /\\ M e. NN0 /\\ ( # ` %s ) <_ M ) )' % (ph, C3, C3)),
            w.inst('elfz2nn0')], 'sylibr', '( %s -> ( # ` %s ) e. ( 0 ... M ) )' % (ph, C3))
    f2 = s([s([cl.mem('( # ` %s )' % C2, 'NN0'), mn, le[C2]], '3jca', '( %s -> ( ( # ` %s ) e. NN0 /\\ M e. NN0 /\\ ( # ` %s ) <_ M ) )' % (ph, C2, C2)),
            w.inst('elfz2nn0')], 'sylibr', '( %s -> ( # ` %s ) e. ( 0 ... M ) )' % (ph, C2))
    fvi = s([s([], 'fvif', '( # ` %s ) = if ( %s , ( # ` %s ) , ( # ` %s ) )' % (RWD, RWC, C3, C2))], 'a1i',
            '( %s -> ( # ` %s ) = if ( %s , ( # ` %s ) , ( # ` %s ) ) )' % (ph, RWD, RWC, C3, C2))
    ifz = s([f3, f2], 'ifcld', '( %s -> if ( %s , ( # ` %s ) , ( # ` %s ) ) e. ( 0 ... M ) )' % (ph, RWC, C3, C2))
    rfz = s([fvi, ifz], 'eqeltrd', '( %s -> ( # ` %s ) e. ( 0 ... M ) )' % (ph, RWD))
    w.qed([rfz, w.inst('elfzle2')], 'syl', ST_RWL)
    return w.run()


UB = '( ( ; 2 5 x. ( 2 x. B ) ) + ; 5 3 )'
T1D = '( %s + ( ( 6 x. B ) + ; 1 0 ) )' % SETCL
NLW = BW(RWD, BW('Q', EWg('L', 'Y')))
VO = CC(ESL('O'), 'Z')
W2O = '( 2nd ` O )'
WW = '( <" F "> ++ %s )' % W2O
ENF = '( encNatGam ` F )'
ACCW = '( ( L encTblAsc %s ) ++ U )' % ACCP


def tmidpb():
    lab = 'tmidpb'
    ph = cj(TREE_DPB)
    w = W(lab, 'Lean\'s ` dpBodyF_runs ` at the machine with the invariant\'s words explicit: wherever '
               '` dpBodyF np nL snap acc s t ` is installed, the residue ` G ` above ` Q ` above ` L ` on ` nL ` is '
               'updated by ` resStep ` (~ tmirst ), the top slot ` O ` of the snapshot is popped, and if it is a witness '
               '` W ` the list ` p :: W ` is written into the accumulator ` C ` at the new residue (~ tmisint ), within '
               '` dpBodyC L N b ` steps (~ tm2fdpb ).')
    c, mk, ne, ex = hsetup(w, ph, TREE_DPB, K6, 'dpb')
    s = w.s
    dd = c[STKD('D')]
    fn, ln, bn, nn = c['F e. NN0'], c['L e. NN'], c['B e. NN0'], c['N e. NN0']
    gw, qw, ol = c['G e. Word 2o'], c['Q e. Word 2o'], c['O e. %s' % SLOT]
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    elw = s([l0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EL))
    egv = s([l0, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` L ) = ( inclBool o. %s ) )' % (ph, EL))
    cl = Closure(w, ph, {'B': ('NN0', bn), 'N': ('NN0', nn), 'L': ('NN', ln)})
    lel = s([l0, bn, c['L < ( 2 ^ B )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` %s ) <_ B )' % (ph, EL))
    cl.leaf('( # ` %s )' % EL, 'NN0', s([elw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, EL)))
    lel2 = linarith(w, ph, [lel, cl.ge0('B')], '( # ` %s ) <_ ( 2 x. B )' % EL, closure=cl)
    B2 = '( 2 x. B )'
    # the resStep triple
    EY = EWg('L', 'Y')
    BEY = BW(EL, 'Y')
    r1, x1 = w.rewrite(EY, {'( encNatGam ` L )': ('( inclBool o. %s )' % EL, egv)}, ph)
    assert x1 == BEY, x1
    dj = c['( D ` J ) = %s' % BW('G', BW('Q', EY))]
    djr, djt = w.rewrite(BW('G', BW('Q', EY)), {EY: (BEY, r1)}, ph)
    dj2 = s([dj, djr], 'eqtrd', '( %s -> ( D ` J ) = %s )' % (ph, djt))
    exr = dict(ex)
    exr.update({'( D ` J ) = %s' % djt: dj2, '%s e. Word 2o' % EL: elw, '%s e. NN0' % B2: cl.mem(B2, 'NN0'),
                '( # ` %s ) <_ %s' % (EL, B2): lel2})
    t1, cc1 = inst(w, ph, 'tmirst', {'K': 'J', 'J': 'K', 'I': 'I"', "I'": 'I0', 'P': PL('P', 3), 'E': PL('P', 0), 'L': 'G', "L'": 'Q',
                                      'L"': EL, 'X': 'Y', 'H': B2}, Bld(w, ph, c, exr))
    C1_, D1_, n1_ = triple_parts(cc1)
    assert n1_ == UB, n1_
    NLW0 = BW(RWD, BW('Q', BEY))
    assert D1_ == CLN(PL('P', 0), S, UP('D', 'J', NLW0)), D1_
    er = s([r1], 'eqcomd', '( %s -> %s = %s )' % (ph, BEY, EY))
    rn, xn = w.rewrite(UP('D', 'J', NLW0), {BEY: (EY, er)}, ph)
    assert xn == UP('D', 'J', NLW), xn
    t1, C1_, D1_, n1_ = hrrw(w, ph, t1, C1_, D1_, n1_, deq=clneq(w, ph, PL('P', 0), S, rn, UP('D', 'J', NLW0), UP('D', 'J', NLW)))
    # the stacks after resStep
    vals = {k: selfval(w, ph, mk, 'D', dd, k) for k in K6}
    S0 = Stacks(w, ph, mk, 'D', dd, ne, vals)
    rwf = s([s([s([gw, qw, ln], '3jca', '( %s -> ( G e. Word 2o /\\ Q e. Word 2o /\\ L e. NN ) )' % ph),
                s([c['( toNat ` G ) < L'], c['( toNat ` Q ) < L']], 'jca', '( %s -> ( ( toNat ` G ) < L /\\ ( toNat ` Q ) < L ) )' % ph)], 'jca',
               '( %s -> %s )' % (ph, PH_RW)), w.inst('ttrwd')], 'syl', '( %s -> %s )' % (ph, ST_RW.split(' -> ', 1)[1][:-2]))
    rww = s([rwf], 'simp1d', '( %s -> %s e. Word 2o )' % (ph, RWD))
    rwl = s([rwf], 'simp3d', '( %s -> ( toNat ` %s ) < L )' % (ph, RWD))
    rll = s([s([s([gw, qw, l0], '3jca', '( %s -> ( G e. Word 2o /\\ Q e. Word 2o /\\ L e. NN0 ) )' % ph),
                s([cl.mem(B2, 'NN0'), s([c['( # ` G ) <_ %s' % B2], c['( # ` Q ) <_ %s' % B2], lel2], '3jca',
                                        '( %s -> ( ( # ` G ) <_ %s /\\ ( # ` Q ) <_ %s /\\ ( # ` %s ) <_ %s ) )' % (ph, B2, B2, EL, B2))], 'jca',
                  '( %s -> ( %s e. NN0 /\\ ( ( # ` G ) <_ %s /\\ ( # ` Q ) <_ %s /\\ ( # ` %s ) <_ %s ) ) )' % (ph, B2, B2, B2, EL, B2))], 'jca',
               '( %s -> %s )' % (ph, tsub_text(PH_RWL, {'M': B2}))), w.inst('ttrwdl')], 'syl', '( %s -> ( # ` %s ) <_ %s )' % (ph, RWD, B2))
    ibr = s([rww, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, RWD))
    qey = wgcat(w, ph, '( inclBool o. Q )', '( <" 4 "> ++ %s )' % EY, s([qw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. Q ) e. Word Gamma' )" % ph),
                wg4(w, ph, EY, ewg(w, ph, 'L', l0, 'Y', c[WRD('Y', GAM)])))
    nlw = wgcat(w, ph, '( inclBool o. %s )' % RWD, '( <" 4 "> ++ %s )' % BW('Q', EY), ibr, wg4(w, ph, BW('Q', EY), qey))
    SD = S0.upd('J', NLW, nlw)
    DP_ = SD.D
    ex0 = {TRI(C1_, D1_, n1_): t1, STKD(DP_): SD.memb, '%s e. NN0' % UB: cl.mem(UB, 'NN0')}
    # T1
    cl.leaf(SETCL, 'NN0', cl.mem(SETCL, 'NN0'))
    ex0['%s e. NN0' % T1D] = cl.mem(T1D, 'NN0')
    ex0['1 <_ %s' % T1D] = linarith(w, ph, [cl.ge0(SETCL), cl.ge0('B')], '1 <_ %s' % T1D, closure=cl, atoms=[SETCL])
    ex0[SSS(NFL('1o'))] = nfl_ss(w, ph, mk, '1o')
    ex0[SSS(NFL('(/)'))] = nfl_ss(w, ph, mk, '(/)')
    m0 = dict(FRAGS['dpb'].lmap())
    m0.update({'K': 'I', 'F': RDK, 'C': 'TMfl', "F'": PID, "D'": DP_, 'U': UB, 'T1': T1D, 'N1': S, "N'": S, 'N': S, 'D': 'D'})
    esl = s([ol, s([s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi', "( O e. %s -> %s e. Word Gamma' )" % (SLOT, ESL('O')))],
            'syl', "( %s -> %s e. Word Gamma' )" % (ph, ESL('O')))
    zw, uw = c[WRD('Z', GAM)], c[WRD('U', GAM)]
    vow = s([esl, zw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, VO))
    dI = s([SD.vals['I'][1], c['( D ` I ) = %s' % VO]], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, DP_, VO))
    sv = s([ol, w.inst('ttabslotv')], 'syl', '( %s -> %s = if ( O = %s , <" 3 "> , ( encList ` %s ) ) )' % (ph, ESL('O'), NONE_, W2O))
    outs = []
    for cond in ('O = %s' % NONE_, 'O =/= %s' % NONE_):
        pc = '( %s /\\ %s )' % (ph, cond)
        cpc = Ctx(w, pc, (TREE_DPB, cond))
        mkp = lift_mk(w, pc, ph, mk)
        Lp = lambda st: L_(w, pc, ph, st)
        m = dict(m0)
        exc = {}
        if cond.startswith('O = '):
            cs = s([], 'simpr', '( %s -> %s )' % (pc, cond))
            it = s([cs], 'iftrued', '( %s -> if ( O = %s , <" 3 "> , ( encList ` %s ) ) = <" 3 "> )' % (pc, NONE_, W2O))
            e3 = s([Lp(sv), it], 'eqtrd', '( %s -> %s = <" 3 "> )' % (pc, ESL('O')))
            dk = s([Lp(dI), s([e3], 'oveq1d', '( %s -> %s = ( <" 3 "> ++ Z ) )' % (pc, VO))], 'eqtrd', '( %s -> ( %s ` I ) = ( <" 3 "> ++ Z ) )' % (pc, DP_))
            DN = UP(DP_, 'I', 'Z')
            m.update({'Z': '3', 'X': 'Z', 'N"': NFL('1o'), 'D"': DN})
            exc['( %s ` I ) = ( <" 3 "> ++ Z )' % DP_] = dk
            g3 = Lp(ex["3 e. Gamma'"])
            ifq = s([s([], 'eqidd', '( %s -> 3 = 3 )' % pc)], 'iftrued', '( %s -> if ( 3 = 3 , 1o , (/) ) = 1o )' % pc)
            exc['A. r e. %s ( %s ` <. r , ( inl ` 3 ) >. ) e. %s' % (S, RDK, NFL('1o'))] = peek_iface(w, pc, mkp, RDK, '3', g3, ifq, '1o')
            ht = ht_nfl(w, pc, '1o')
            pop = pop_iface(w, pc, mkp, NFL('1o'), Lp(ex0[SSS(NFL('1o'))]), '3', g3)
            d, d1, d2 = disj_leaf('tm2fdpb', m)
            dj1 = s([ht, pop, s([], 'eqidd', '( %s -> %s = %s )' % (pc, DN, DN))], '3jca', '( %s -> %s )' % (pc, d1))
            exc[d] = s([dj1], 'orcd', '( %s -> %s )' % (pc, d))
            exc[STKD(DN)] = updcl(w, pc, DP_, 'I', 'Z', mkp['tv'], Lp(SD.memb), mkp['k']['I']['kd'],
                                  s([Lp(zw), mkp['k']['I']['wge']], 'eleqtrrd', '( %s -> Z e. Word %s )' % (pc, GX('I'))))
            # the post DN = DFIN_DPB
            ap = s([cs], 'iftrued', '( %s -> %s = C )' % (pc, ACCP))
            ra, xa = w.rewrite(ACCW, {ACCP: ('C', ap)}, pc)
            ai = s([ra, s([Lp(c["( D ` I' ) = ( ( L encTblAsc C ) ++ U )"])], 'eqcomd', "( %s -> ( ( L encTblAsc C ) ++ U ) = ( D ` I' ) )" % pc)],
                   'eqtrd', "( %s -> %s = ( D ` I' ) )" % (pc, ACCW))
            rf, xf = w.rewrite(DFIN_DPB, {ACCW: ("( D ` I' )", ai)}, pc)
            gam = {NLW: Lp(nlw), 'Z': Lp(zw), "( D ` I' )": Lp(vals["I'"][2])}
            nst, out = stk_normalize(w, pc, mkp, 'D', Lp(dd), lambda a, b: Lp(ne(a, b)), [('J', NLW), ('I', 'Z'), ("I'", "( D ` I' )")], gam, K6)
            assert chain_text('D', out) == DN, chain_text('D', out)
            fe = s([rf, nst], 'eqtrd', '( %s -> %s = %s )' % (pc, DFIN_DPB, DN))
            post_eq = s([fe], 'eqcomd', '( %s -> %s = %s )' % (pc, DN, DFIN_DPB))
            DNt = DN
        else:
            en = s([Lp(ol), w.inst('ttslotn0')], 'syl', '( %s -> %s =/= (/) )' % (pc, ESL('O')))
            c0 = s([Lp(esl), Lp(zw), w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( %s = (/) /\\ Z = (/) ) ) )' % (pc, VO, ESL('O')))
            n1 = s([s([en], 'neneqd', '( %s -> -. %s = (/) )' % (pc, ESL('O')))], 'intnanrd', '( %s -> -. ( %s = (/) /\\ Z = (/) ) )' % (pc, ESL('O')))
            vn0 = s([s([c0, n1], 'mtbird', '( %s -> -. %s = (/) )' % (pc, VO))], 'neqned', '( %s -> %s =/= (/) )' % (pc, VO))
            eqV, hg, tg = word_split(w, pc, VO, Lp(vow), vn0)
            Zh, Xr = HD0(VO), TL1(VO)
            dk = s([Lp(dI), eqV], 'eqtrd', '( %s -> ( %s ` I ) = ( <" %s "> ++ %s ) )' % (pc, DP_, Zh, Xr))
            sk = s([Lp(ol), Lp(zw), w.inst('ttabslotk')], 'syl2anc', '( %s -> ( %s = 3 <-> O = %s ) )' % (pc, Zh, NONE_))
            cs = s([], 'simpr', '( %s -> O =/= %s )' % (pc, NONE_))
            nn_ = s([cs], 'neneqd', '( %s -> -. O = %s )' % (pc, NONE_))
            nz = s([sk, nn_], 'mtbird', '( %s -> -. %s = 3 )' % (pc, Zh))
            ifq = s([nz], 'iffalsed', '( %s -> if ( %s = 3 , 1o , (/) ) = (/) )' % (pc, Zh))
            m.update({'Z': Zh, 'X': Xr, 'N"': NFL('(/)'), 'D"': DFIN_DPB})
            exc['( %s ` I ) = ( <" %s "> ++ %s )' % (DP_, Zh, Xr)] = dk
            exc["%s e. Gamma'" % Zh] = hg
            exc[WRD(Xr, GAM)] = tg
            exc['A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDK, Zh, NFL('(/)'))] = peek_iface(w, pc, mkp, RDK, Zh, hg, ifq, '(/)')
            itf = s([nn_], 'iffalsed', '( %s -> if ( O = %s , <" 3 "> , ( encList ` %s ) ) = ( encList ` %s ) )' % (pc, NONE_, W2O, W2O))
            enc = s([Lp(sv), itf], 'eqtrd', '( %s -> %s = ( encList ` %s ) )' % (pc, ESL('O'), W2O))
            # slot bound of O
            both = s([cs, Lp(c[SB('O')])], 'mpd', '( %s -> ( ( # ` %s ) <_ N /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (pc, W2O, W2O))
            w2le = s([both], 'simpld', '( %s -> ( # ` %s ) <_ N )' % (pc, W2O))
            w2r = s([both], 'simprd', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (pc, W2O))
            w2w = s([Lp(ol), w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, W2O))
            # the run
            vp = {k: (v[0], Lp(v[1]), Lp(v[2])) for k, v in vals.items()}
            vp['I'] = (VO, Lp(c['( D ` I ) = %s' % VO]), Lp(vow))
            vp['K'] = (EWg('F', 'X'), Lp(c['( D ` K ) = %s' % EWg('F', 'X')]), ewg(w, pc, 'F', Lp(fn), 'X', Lp(c[WRD('X', GAM)])))
            vp["I'"] = ('( ( L encTblAsc C ) ++ U )', Lp(c["( D ` I' ) = ( ( L encTblAsc C ) ++ U )"]), Lp(vals["I'"][2]))
            S0p = Stacks(w, pc, mkp, 'D', Lp(dd), lambda a, b: Lp(ne(a, b)), vp)
            SDp = S0p.upd('J', NLW, Lp(nlw))
            base = dict(ex); base.update(ex0)
            basep = {k: Lp(v) for k, v in base.items()} if False else {}
            R = Run(w, pc, mkp, SDp, {}, cpc)
            R.base = LiftDict(w, pc, ph, base)
            EFt = '( encodeNat ` F )'
            e = {'EF': EFt, 'fn0': Lp(fn), 'ef': s([Lp(fn), w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (pc, EFt)),
                 'gv': s([Lp(fn), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = ( inclBool o. %s ) )' % (pc, EFt))}
            e['le'] = s([Lp(fn), Lp(bn), Lp(c['F < ( 2 ^ B )']), w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` F ) ) <_ B )' % pc)
            wb = enc_bits(w, pc, e)
            gamv = R.gam
            E1 = CC(ENF, '( <" 4 "> ++ %s )' % VO)
            e1g = wgcat(w, pc, ENF, '( <" 4 "> ++ %s )' % VO, ewg(w, pc, 'F', Lp(fn), None, None) if False else
                        s([Lp(fn), w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (pc, ENF)), wg4(w, pc, VO, Lp(vow)))
            R.call('tmidup', {'K': 'K', 'J': 'I', 'I': 'I"', 'P': PL('P', 4), 'E': PL(PL('P', 5), 0), 'W': ENF, 'X': 'X'},
                   {WRD(ENF, BITS): wb, '( %s ` K ) = ( %s ++ ( <" 4 "> ++ X ) )' % (DP_, ENF): SDp.vals['K'][1]},
                   [('I', E1, e1g)], pre=(NFL('(/)'), Lp(ex0[SSS(NFL('(/)'))])))
            S1_ = R.S
            FX = EWg('F', 'X')
            E2 = BW(RWD, FX)
            e2g = wgcat(w, pc, '( inclBool o. %s )' % RWD, '( <" 4 "> ++ %s )' % FX, Lp(ibr), wg4(w, pc, FX, ewg(w, pc, 'F', Lp(fn), 'X', Lp(c[WRD('X', GAM)]))))
            R.call('tmidup', {'K': 'J', 'J': 'K', 'I': 'I"', 'P': PL('P', 5), 'E': PL(PL(PL('P', 6), 3), 0), 'W': '( inclBool o. %s )' % RWD,
                              'X': BW('Q', EY)},
                   {WRD('( inclBool o. %s )' % RWD, BITS): s([Lp(rww), w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (pc, RWD, BITS)),
                    WRD(BW('Q', EY), GAM): Lp(qey), '( %s ` J ) = %s' % (S1_.D, NLW): S1_.vals['J'][1]},
                   [('K', E2, e2g)])
            S2_ = R.S
            # ( S2 ` I ) = ( encList ` WW ) ++ Z
            fcons = s([Lp(fn), w2w, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` %s ) = ( %s ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (pc, WW, ENF, W2O))
            elw2 = s([w2w, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, W2O))
            s4 = s([s([], 'gamma4', "4 e. Gamma'")], 's1cld' if False else 'id', '') if False else None
            g4 = closed(w, pc, 'gamma4', "4 e. Gamma'")
            s4 = s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % pc)
            eng = s([Lp(fn), w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (pc, ENF))
            fz = s([fcons], 'oveq1d', '( %s -> ( ( encList ` %s ) ++ Z ) = ( ( %s ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ Z ) )' % (pc, WW, ENF, W2O))
            a1 = s([eng, s([s4, elw2, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ ( encList ` %s ) ) e. Word Gamma' )" % (pc, W2O)), Lp(zw), w.inst('ccatass')],
                   'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ Z ) = ( %s ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ Z ) ) )'
                   % (pc, ENF, W2O, ENF, W2O))
            a2 = s([s4, elw2, Lp(zw), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ ( encList ` %s ) ) ++ Z ) = ( <" 4 "> ++ ( ( encList ` %s ) ++ Z ) ) )'
                   % (pc, W2O, W2O))
            a3 = s([s([s([enc], 'oveq1d', '( %s -> %s = ( ( encList ` %s ) ++ Z ) )' % (pc, VO, W2O))], 'oveq2d',
                      '( %s -> ( <" 4 "> ++ %s ) = ( <" 4 "> ++ ( ( encList ` %s ) ++ Z ) ) )' % (pc, VO, W2O))], 'oveq2d',
                   '( %s -> %s = ( %s ++ ( <" 4 "> ++ ( ( encList ` %s ) ++ Z ) ) ) )' % (pc, E1, ENF, W2O))
            a2b = s([a2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ Z ) ) = ( %s ++ ( <" 4 "> ++ ( ( encList ` %s ) ++ Z ) ) ) )'
                    % (pc, ENF, W2O, ENF, W2O))
            a4 = s([s([fz, a1], 'eqtrd', '( %s -> ( ( encList ` %s ) ++ Z ) = ( %s ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ Z ) ) )' % (pc, WW, ENF, W2O)), a2b],
                   'eqtrd', '( %s -> ( ( encList ` %s ) ++ Z ) = ( %s ++ ( <" 4 "> ++ ( ( encList ` %s ) ++ Z ) ) ) )' % (pc, WW, ENF, W2O))
            a5 = s([a3, a4], 'eqtr4d', '( %s -> %s = ( ( encList ` %s ) ++ Z ) )' % (pc, E1, WW))
            di2 = s([S2_.vals['I'][1], a5], 'eqtrd', '( %s -> ( %s ` I ) = ( ( encList ` %s ) ++ Z ) )' % (pc, S2_.D, WW))
            # W typing and bounds
            s1f = s([Lp(fn)], 's1cld', '( %s -> <" F "> e. Word NN0 )' % pc)
            www = s([s1f, w2w, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (pc, WW))
            wl = s([s1f, w2w, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" F "> ) + ( # ` %s ) ) )' % (pc, WW, W2O))
            wl2 = s([wl, s([s([], 's1len', '( # ` <" F "> ) = 1')], 'a1i' if False else 'oveq1i', '( ( # ` <" F "> ) + ( # ` %s ) ) = ( 1 + ( # ` %s ) )' % (W2O, W2O))],
                    'eqtrdi' if False else 'id', '') if False else None
            s1l = s([s([], 's1len', '( # ` <" F "> ) = 1')], 'a1i', '( %s -> ( # ` <" F "> ) = 1 )' % pc)
            clp = Closure(w, pc, {'N': ('NN0', Lp(nn)), 'B': ('NN0', Lp(bn))})
            clp.leaf('( # ` %s )' % W2O, 'NN0', s([w2w, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, W2O)))
            clp.leaf('( # ` <" F "> )', 'NN0', s([s1f, w.inst('lencl')], 'syl', '( %s -> ( # ` <" F "> ) e. NN0 )' % pc))
            clp.leaf('( # ` %s )' % WW, 'NN0', s([www, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, WW)))
            wle = linarith(w, pc, [wl, s1l, w2le], '( # ` %s ) <_ ( N + 1 )' % WW, closure=clp)
            fv_ = s([Lp(fn)], 'elexd', '( %s -> F e. _V )' % pc)
            cr = s([s1f, w2w, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran <" F "> u. ran %s ) )' % (pc, WW, W2O))
            sr = s([fv_, w.inst('s1rn')], 'syl', '( %s -> ran <" F "> = { F } )' % pc)
            cr2 = s([cr, s([sr], 'uneq1d', '( %s -> ( ran <" F "> u. ran %s ) = ( { F } u. ran %s ) )' % (pc, W2O, W2O))], 'eqtrd',
                    '( %s -> ran %s = ( { F } u. ran %s ) )' % (pc, WW, W2O))
            rs = s([s([s([], 'breq1', '( a = F -> ( a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')], 'ralsng', '( F e. _V -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )'),
                    ], 'id', '') if False else None
            rsg = s([fv_, s([s([], 'breq1', '( a = F -> ( a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')], 'ralsng',
                             '( F e. _V -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')], 'syl',
                    '( %s -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )' % pc)
            rf1 = s([Lp(c['F < ( 2 ^ B )']), rsg], 'mpbird', '( %s -> A. a e. { F } a < ( 2 ^ B ) )' % pc)
            run_ = s([s([rf1, w2r], 'jca', '( %s -> ( A. a e. { F } a < ( 2 ^ B ) /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (pc, W2O)),
                      s([], 'ralunb', '( A. a e. ( { F } u. ran %s ) a < ( 2 ^ B ) <-> ( A. a e. { F } a < ( 2 ^ B ) /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (W2O, W2O))],
                     'sylibr', '( %s -> A. a e. ( { F } u. ran %s ) a < ( 2 ^ B ) )' % (pc, W2O))
            rw_ = s([s([cr2], 'raleqdv' if False else 'id', '') if False else s([cr2, w.inst('raleq')], 'syl',
                    '( %s -> ( A. a e. ran %s a < ( 2 ^ B ) <-> A. a e. ( { F } u. ran %s ) a < ( 2 ^ B ) ) )' % (pc, WW, W2O)), run_], 'mpbird',
                    '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (pc, WW))
            exs = {'( %s ` I\' ) = ( ( L encTblAsc C ) ++ U )' % S2_.D: S2_.vals["I'"][1],
                   '( %s ` K ) = %s' % (S2_.D, E2): S2_.vals['K'][1], '( %s ` I ) = ( ( encList ` %s ) ++ Z )' % (S2_.D, WW): di2,
                   '%s e. Word 2o' % RWD: Lp(rww), '%s e. Word NN0' % WW: www, 'L e. NN0': Lp(l0), WRD(FX, GAM): ewg(w, pc, 'F', Lp(fn), 'X', Lp(c[WRD('X', GAM)])),
                   '( N + 1 ) e. NN0': clp.mem('( N + 1 )', 'NN0'), '%s e. NN0' % B2: clp.mem(B2, 'NN0'), '( # ` %s ) <_ %s' % (RWD, B2): Lp(rll),
                   '( toNat ` %s ) < L' % RWD: Lp(rwl), '( # ` %s ) <_ ( N + 1 )' % WW: wle, 'A. a e. ran %s a < ( 2 ^ B )' % WW: rw_}
            ACC2 = '( ( L encTblAsc ( ( C SetIfNone ( toNat ` %s ) ) ` %s ) ) ++ U )' % (RWD, WW)
            a2g = s([s([s([s([Lp(ct := c['C e. Tbl']), s([Lp(rww), w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (pc, RWD))], 'jca',
                           '( %s -> ( C e. Tbl /\\ ( toNat ` %s ) e. NN0 ) )' % (pc, RWD)), www, w.inst('setifnonecl')], 'syl2anc',
                         '( %s -> ( ( C SetIfNone ( toNat ` %s ) ) ` %s ) e. Tbl )' % (pc, RWD, WW)), Lp(l0)], 'jca' if False else 'id', '') if False else None],
                    'id', '') if False else None
            R.call('tmisint', {'K': "I'", 'J': 'K', 'I': 'I', "I'": 'I"', 'I"': 'I0', 'P': PL('P', 6), 'E': 'E', 'A': 'C', 'G': RWD, 'W': WW,
                               'X': 'U', 'Y': FX, 'R': 'Z', 'N': '( N + 1 )', 'H': B2}, exs,
                   [("I'", ACC2, acc_typ(w, pc, c, Lp, rww, www, l0, uw)), ('K', FX, ewg(w, pc, 'F', Lp(fn), 'X', Lp(c[WRD('X', GAM)]))), ('I', 'Z', Lp(zw))])
            # normalize over D with the value FX -> ( D ` K )
            cur, out = R.normalize(K6)
            chi = [('J', NLW)] + out
            dkr = s([Lp(c['( D ` K ) = %s' % EWg('F', 'X')])], 'eqcomd', '( %s -> %s = ( D ` K ) )' % (pc, FX))
            ch2 = [(k, '( D ` K )' if v == FX else v) for k, v in chi]
            rq, xq = w.rewrite(chain_text('D', chi), {FX: ('( D ` K )', dkr)}, pc) if FX in chain_text('D', chi) else (None, chain_text('D', chi))
            gam = dict(R.gam); gam['( D ` K )'] = Lp(vals['K'][2]); gam[NLW] = Lp(nlw)
            nst, out2 = stk_normalize(w, pc, mkp, 'D', Lp(dd), lambda a, b: Lp(ne(a, b)), ch2, gam, K6)
            assert out2 == [('J', NLW), ('I', 'Z'), ("I'", ACC2)], out2
            apq = s([nn_], 'iffalsed', '( %s -> %s = ( ( C SetIfNone ( toNat ` %s ) ) ` %s ) )' % (pc, ACCP, RWD, WW))
            ra2, xa2 = w.rewrite(chain_text('D', out2), {ACC2: (ACCW, s([s([apq], 'eqcomd', '( %s -> ( ( C SetIfNone ( toNat ` %s ) ) ` %s ) = %s )' % (pc, RWD, WW, ACCP))] +
                                                                           [], 'id', '') if False else acc_eq(w, pc, apq, ACC2))}, pc)
            assert xa2 == DFIN_DPB, xa2
            eqs = [x for x in (rq, nst, ra2) if x is not None]
            fe = eqs[0]
            curt = chain_text('D', chi)
            nxt = [xq, chain_text('D', out2), xa2]
            txts = []
            if rq is not None:
                txts.append(xq)
            if nst is not None:
                txts.append(chain_text('D', out2))
            txts.append(xa2)
            for st_, tx in zip(eqs[1:], txts[1:]):
                fe = s([fe, st_], 'eqtrd', '( %s -> %s = %s )' % (pc, curt, tx))
            tr, Cr, Dr, nr = R.tri, R.C0, R.cur, R.n
            tr, Cr, Dr, nr = hrrw(w, pc, tr, Cr, Dr, nr, deq=clneq(w, pc, 'E', S, fe, curt, DFIN_DPB))
            # the bound
            sm = s([s([s([s([Lp(rww), w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (pc, RWD)), Lp(l0),
                          s([Lp(rwl)], 'id', '') if False else s([s([Lp(rww), w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (pc, RWD))], 'id', '') if False else
                          ltle(w, pc, Lp(rwl), '( toNat ` %s )' % RWD, 'L', Lp(rww), Lp(l0))], '3jca',
                         '( %s -> ( ( toNat ` %s ) e. NN0 /\\ L e. NN0 /\\ ( toNat ` %s ) <_ L ) )' % (pc, RWD, RWD)),
                       s([clp.mem('( N + 1 )', 'NN0'), Lp(bn), clp.mem(B2, 'NN0')], '3jca', '( %s -> ( ( N + 1 ) e. NN0 /\\ B e. NN0 /\\ %s e. NN0 ) )' % (pc, B2))],
                      'jca', '( %s -> ( ( ( toNat ` %s ) e. NN0 /\\ L e. NN0 /\\ ( toNat ` %s ) <_ L ) /\\ ( ( N + 1 ) e. NN0 /\\ B e. NN0 /\\ %s e. NN0 ) ) )' % (pc, RWD, RWD, B2)),
                    w.inst('ttabsetm')], 'syl', '( %s -> %s <_ %s )' % (pc, SETC('( toNat ` %s )' % RWD, '( N + 1 )', B2), SETCL))
            SJ = SETC('( toNat ` %s )' % RWD, '( N + 1 )', B2)
            clp.leaf(SJ, 'NN0', clp.mem(SJ, 'NN0') if False else s([sj_nn0(w, pc, clp, rww, RWD)], 'id', '') if False else sj_nn0(w, pc, clp, Lp(rww), RWD, SJ))
            clp.leaf(SETCL, 'NN0', s([Lp(cl.mem(SETCL, 'NN0'))], 'id', '') if False else Lp(cl.mem(SETCL, 'NN0')))
            lf = enc_len(w, pc, e, ENF)
            clp.leaf('( # ` %s )' % ENF, 'NN0', lf[0])
            bl = s([Lp(rww), w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (pc, RWD, RWD))
            clp.leaf('( # ` ( inclBool o. %s ) )' % RWD, 'NN0', s([Lp(ibr), w.inst('lencl')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) e. NN0 )' % (pc, RWD)))
            clp.leaf('( # ` %s )' % RWD, 'NN0', s([Lp(rww), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, RWD)))
            le = linarith(w, pc, [sm, lf[1], bl, Lp(rll)], '%s <_ %s' % (nr, T1D), closure=clp, atoms=[SJ, SETCL])
            tr = hrle(w, pc, mkp['phm'], tr, Cr, Dr, nr, T1D, clp.mem(T1D, 'NN0') if False else Lp(ex0['%s e. NN0' % T1D]), le)
            d, d1, d2 = disj_leaf('tm2fdpb', m)
            dj2 = s([ht_nfl(w, pc, '(/)'), tr], 'jca', '( %s -> %s )' % (pc, d2))
            exc[d] = s([dj2], 'olcd', '( %s -> %s )' % (pc, d))
            post_eq = None
            DNt = DFIN_DPB
        bld = LazyBld(w, pc, ph, cpc, dict(ex, **ex0), exc)
        t, cc = inst(w, pc, 'tm2fdpb', m, bld)
        Cg, Dg, ng = triple_parts(cc)
        if post_eq is not None:
            t, Cg, Dg, ng = hrrw(w, pc, t, Cg, Dg, ng, deq=clneq(w, pc, 'E', S, post_eq, DNt, DFIN_DPB))
        cc = TRI(Cg, Dg, ng)
        outs.append((s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, cc)), cc))
    assert outs[0][1] == outs[1][1]
    t = s([outs[0][0], outs[1][0]], 'pm2.61dne', '( %s -> %s )' % (ph, outs[0][1]))
    C, D, n = triple_parts(outs[0][1])
    le = s([s([bn, cl.mem(SETCL, 'NN0')], 'jca', '( %s -> ( B e. NN0 /\\ %s e. NN0 ) )' % (ph, SETCL)), w.inst('ttdpbcx')], 'syl',
           '( %s -> %s <_ %s )' % (ph, n, DPBC))
    hrle(w, ph, mk['phm'], t, C, D, n, DPBC, cl.mem(DPBC, 'NN0'), le, qed=True)
    return w.run()


class LiftDict(dict):
    """a dict of steps under ph, lifted to pc on access"""
    def __init__(self, w, pc, ph, d):
        dict.__init__(self)
        self.w, self.pc, self.ph, self.d, self.memo = w, pc, ph, d, {}
    def __contains__(self, k):
        return k in self.d
    def __getitem__(self, k):
        if k not in self.memo:
            self.memo[k] = L_(self.w, self.pc, self.ph, self.d[k])
        return self.memo[k]
    def items(self):
        return [(k, self[k]) for k in self.d]
    def keys(self):
        return self.d.keys()
    def __iter__(self):
        return iter(self.d)
    def get(self, k, default=None):
        return self[k] if k in self.d else default
    def copy(self):
        return self


def ltle(w, p, lt, a, b, aw, b0):
    ar = w.s([w.s([aw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (p, a))], 'nn0red', '( %s -> %s e. RR )' % (p, a))
    br = w.s([b0], 'nn0red', '( %s -> %s e. RR )' % (p, b))
    return w.s([ar, br, lt], 'ltled', '( %s -> %s <_ %s )' % (p, a, b))


def sj_nn0(w, p, clp, rww, RWD_, SJ):
    tn = w.s([rww if False else rww, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (p, RWD_))
    clp.leaf('( toNat ` %s )' % RWD_, 'NN0', tn)
    return clp.mem(SJ, 'NN0')


def enc_len(w, p, e, ENF_):
    """( # ` ENF ) e. NN0 and ( # ` ENF ) <_ B"""
    s = w.s
    ln = s([s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (p, ENF_, e['EF'])),
            s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (p, e['EF'], e['EF']))], 'eqtrd',
           '( %s -> ( # ` %s ) = ( # ` %s ) )' % (p, ENF_, e['EF']))
    le = s([ln, e['le']], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (p, ENF_))
    n0 = s([s([s([e['fn0'], w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (p, ENF_))], 'id', '') if False else
            s([e['fn0'], w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (p, ENF_)), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (p, ENF_))
    return n0, le


def acc_typ(w, pc, c, Lp, rww, www, l0, uw):
    s = w.s
    RW_ = RWD
    ACC2 = '( ( L encTblAsc ( ( C SetIfNone ( toNat ` %s ) ) ` %s ) ) ++ U )' % (RW_, WW)
    tn = s([Lp(rww), w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (pc, RW_))
    at = s([s([Lp(c['C e. Tbl']), tn], 'jca', '( %s -> ( C e. Tbl /\\ ( toNat ` %s ) e. NN0 ) )' % (pc, RW_)), www, w.inst('setifnonecl')], 'syl2anc',
           '( %s -> ( ( C SetIfNone ( toNat ` %s ) ) ` %s ) e. Tbl )' % (pc, RW_, WW))
    TT = '( ( C SetIfNone ( toNat ` %s ) ) ` %s )' % (RW_, WW)
    te = s([s([at, Lp(l0)], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (pc, TT)), w.inst('tttbles')], 'syl',
           '( %s -> ( ( L encTblAsc %s ) = %s /\\ ( L encTblDesc %s ) = %s ) )' % (pc, TT, ES('( %s |` ( 0 ..^ L ) )' % TT), TT, ES(REV('( %s |` ( 0 ..^ L ) )' % TT))))
    tw = s([s([at, Lp(l0)], 'jca', '( %s -> ( %s e. Tbl /\\ L e. NN0 ) )' % (pc, TT)), w.inst('tttblw')], 'syl',
           '( %s -> ( ( %s |` ( 0 ..^ L ) ) e. %s /\\ ( # ` ( %s |` ( 0 ..^ L ) ) ) = L ) )' % (pc, TT, WSLOT, TT))
    esw = s([s([tw], 'simpld', '( %s -> ( %s |` ( 0 ..^ L ) ) e. %s )' % (pc, TT, WSLOT)), w.inst('ttsescl')], 'syl',
            "( %s -> %s e. Word Gamma' )" % (pc, ES('( %s |` ( 0 ..^ L ) )' % TT)))
    ea = s([te], 'simpld', '( %s -> ( L encTblAsc %s ) = %s )' % (pc, TT, ES('( %s |` ( 0 ..^ L ) )' % TT)))
    eaw = s([ea, esw], 'eqeltrd', "( %s -> ( L encTblAsc %s ) e. Word Gamma' )" % (pc, TT))
    return s([eaw, Lp(uw), w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (pc, ACC2))


def acc_eq(w, pc, apq, ACC2):
    s = w.s
    TT = '( ( C SetIfNone ( toNat ` %s ) ) ` %s )' % (RWD, WW)
    e = s([apq], 'eqcomd', '( %s -> %s = %s )' % (pc, TT, ACCP))
    return s([s([e], 'oveq2d', '( %s -> ( L encTblAsc %s ) = ( L encTblAsc %s ) )' % (pc, TT, ACCP))], 'oveq1d', '( %s -> %s = %s )' % (pc, ACC2, ACCW))


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
