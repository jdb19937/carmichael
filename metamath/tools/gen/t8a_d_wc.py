"""T8a: the counter of walkDown and the empty table's word.

  ttwc0   the counter word at step 0 is the input word
  ttwcp   the counter word at step I <_ F : a bit word of value F - I, no longer than the input
  ttwcs   predBits takes the counter word at step I to that at step I + 1 (I < F)
  ttreps  the free-monoid sum of L copies of the word <" Z "> is Z repeated L times
  ttetb0  Lean ` encTblAsc_emptyTbl `

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_d_wc.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
from lin import linarith, lineq

SEL = sys.argv[1:]
F = FG
LEN = '( # ` G )'
BLF = '( bl ` %s )' % F
CA = '%s = %s' % (LEN, BLF)          # the canonical case


def gfacts(w, ph, gw):
    """F e. NN0, # G e. NN0, bl F e. NN0, F < 2 ^ # G, bl F <_ # G"""
    fn = w.s([gw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, F))
    ln = w.s([gw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN))
    bn = w.s([fn, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, BLF))
    fl = w.s([gw, w.inst('tonatlt')], 'syl', '( %s -> %s < ( 2 ^ %s ) )' % (ph, F, LEN))
    bl = w.s([fn, ln, fl, w.inst('blle')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, BLF, LEN))
    return dict(fn=fn, ln=ln, bn=bn, fl=fl, bl=bl)


def ttwc0():
    w = W('ttwc0', 'The counter word of ` walkDown ` at step 0 is the input bit word (~ bweqwrd ).')
    ph = 'G e. Word 2o'
    gw = w.s([], 'id', '( %s -> %s )' % (ph, ph))
    g = gfacts(w, ph, gw)
    f0 = w.s([w.s([g['fn']], 'nn0cnd', '( %s -> %s e. CC )' % (ph, F))], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (ph, F, F))
    # if ( CA , ( bl ` ( F - 0 ) ) , # G ) = # G
    a1 = '( %s /\\ %s )' % (ph, CA)
    b1 = w.s([w.s([f0], 'adantr', '( %s -> ( %s - 0 ) = %s )' % (a1, F, F))], 'fveq2d', '( %s -> ( bl ` ( %s - 0 ) ) = %s )' % (a1, F, BLF))
    b2 = w.s([w.s([], 'simpr', '( %s -> %s )' % (a1, CA))], 'eqcomd', '( %s -> %s = %s )' % (a1, BLF, LEN))
    t1 = w.s([b1, b2], 'eqtrd', '( %s -> ( bl ` ( %s - 0 ) ) = %s )' % (a1, F, LEN))
    t2 = w.s([], 'eqidd', '( ( %s /\\ -. %s ) -> %s = %s )' % (ph, CA, LEN, LEN))
    ie = w.s([t1, t2], 'ifeqda', '( %s -> %s = %s )' % (ph, LNC('0'), LEN))
    e = w.s([f0, ie], 'oveq12d', '( %s -> %s = ( %s bwrd %s ) )' % (ph, CW('0'), F, LEN))
    bw = w.s([gw, w.inst('bweqwrd')], 'syl', '( %s -> G = ( %s bwrd %s ) )' % (ph, F, LEN))
    w.qed([e, bw], 'eqtr4d', ST_WC0)
    return w.run()


def core(w, ph, gw, inn, ile):
    """facts on the counter word at step I (I <_ F): V = F - I e. NN0, LN e. NN0, V < 2 ^ LN, # CW = LN, LN <_ # G"""
    g = gfacts(w, ph, gw)
    V = '( %s - I )' % F
    vn = w.s([inn, g['fn'], ile, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, V))
    bv = w.s([vn, w.inst('blcl')], 'syl', '( %s -> ( bl ` %s ) e. NN0 )' % (ph, V))
    LN = LNC('I')
    lnn = w.s([bv, g['ln']], 'ifcld', '( %s -> %s e. NN0 )' % (ph, LN))
    # V < 2 ^ LN by cases
    e1 = w.s([w.s([], 'oveq2', '( ( bl ` %s ) = %s -> ( 2 ^ ( bl ` %s ) ) = ( 2 ^ %s ) )' % (V, LN, V, LN))], 'breq2d',
             '( ( bl ` %s ) = %s -> ( %s < ( 2 ^ ( bl ` %s ) ) <-> %s < ( 2 ^ %s ) ) )' % (V, LN, V, V, V, LN))
    e2 = w.s([w.s([], 'oveq2', '( %s = %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (LEN, LN, LEN, LN))], 'breq2d',
             '( %s = %s -> ( %s < ( 2 ^ %s ) <-> %s < ( 2 ^ %s ) ) )' % (LEN, LN, V, LEN, V, LN))
    c1 = w.s([w.s([vn], 'adantr', '( ( %s /\\ %s ) -> %s e. NN0 )' % (ph, CA, V)), w.inst('blpow2')], 'syl',
             '( ( %s /\\ %s ) -> %s < ( 2 ^ ( bl ` %s ) ) )' % (ph, CA, V, V))
    a2 = '( %s /\\ -. %s )' % (ph, CA)
    L2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (a2, f))
    cl = Closure(w, a2, {F: ('NN0', L2(g['fn'], '%s e. NN0' % F)), 'I': ('NN0', L2(inn, 'I e. NN0'))})
    cl.atom('( 2 ^ %s )' % LEN)
    p2 = w.s([closed(w, a2, '2nn0', '2 e. NN0'), L2(g['ln'], '%s e. NN0' % LEN), w.inst('nn0expcl')], 'syl2anc',
             '( %s -> ( 2 ^ %s ) e. NN0 )' % (a2, LEN))
    cl.leaf('( 2 ^ %s )' % LEN, 'NN0', p2)
    c2 = linarith(w, a2, [L2(g['fl'], '%s < ( 2 ^ %s )' % (F, LEN)), cl.ge0('I')], '%s < ( 2 ^ %s )' % (V, LEN), closure=cl)
    vlt = w.s([e1, e2, c1, c2], 'ifbothda', '( %s -> %s < ( 2 ^ %s ) )' % (ph, V, LN))
    # LN <_ # G by cases
    f1 = w.s([], 'breq1', '( ( bl ` %s ) = %s -> ( ( bl ` %s ) <_ %s <-> %s <_ %s ) )' % (V, LN, V, LEN, LN, LEN))
    f2 = w.s([], 'breq1', '( %s = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (LEN, LN, LEN, LEN, LN, LEN))
    a1 = '( %s /\\ %s )' % (ph, CA)
    L1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (a1, f))
    cl1 = Closure(w, a1, {F: ('NN0', L1(g['fn'], '%s e. NN0' % F)), 'I': ('NN0', L1(inn, 'I e. NN0'))})
    p1 = w.s([closed(w, a1, '2nn0', '2 e. NN0'), L1(g['bn'], '%s e. NN0' % BLF), w.inst('nn0expcl')], 'syl2anc',
             '( %s -> ( 2 ^ %s ) e. NN0 )' % (a1, BLF))
    cl1.leaf('( 2 ^ %s )' % BLF, 'NN0', p1)
    fb = w.s([L1(g['fn'], '%s e. NN0' % F), w.inst('blpow2')], 'syl', '( %s -> %s < ( 2 ^ %s ) )' % (a1, F, BLF))
    vb = linarith(w, a1, [fb, cl1.ge0('I')], '%s < ( 2 ^ %s )' % (V, BLF), closure=cl1)
    d1 = w.s([L1(vn, '%s e. NN0' % V), L1(g['bn'], '%s e. NN0' % BLF), vb, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` %s ) <_ %s )' % (a1, V, BLF))
    d2 = w.s([d1, w.s([], 'simpr', '( %s -> %s )' % (a1, CA))], 'breqtrrd', '( %s -> ( bl ` %s ) <_ %s )' % (a1, V, LEN))
    d3 = w.s([w.s([L2(g['ln'], '%s e. NN0' % LEN)], 'nn0red', '( %s -> %s e. RR )' % (a2, LEN))], 'leidd', '( %s -> %s <_ %s )' % (a2, LEN, LEN))
    lle = w.s([f1, f2, d2, d3], 'ifbothda', '( %s -> %s <_ %s )' % (ph, LN, LEN))
    vz = w.s([vn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, V))
    cw = w.s([vz, lnn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, CW('I')))
    cl_ = w.s([vz, lnn, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, CW('I'), LN))
    tn = w.s([vn, lnn, vlt, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ph, CW('I'), V))
    return dict(g=g, V=V, vn=vn, bv=bv, LN=LN, lnn=lnn, vlt=vlt, lle=lle, cw=cw, len=cl_, tn=tn, vz=vz)


def ttwcp():
    w = W('ttwcp', 'The counter word of ` walkDown ` at step ` I <_ F ` : a bit word with the value ` F - I ` , '
                   'no longer than the input word (Lean ` WalkInv ` \'s ` toNat l = jn - i ` , ` l.length <_ m ` ).')
    ph = '( G e. Word 2o /\\ I e. NN0 /\\ I <_ %s )' % F
    gw = w.s([], 'simp1', '( %s -> G e. Word 2o )' % ph)
    inn = w.s([], 'simp2', '( %s -> I e. NN0 )' % ph)
    ile = w.s([], 'simp3', '( %s -> I <_ %s )' % (ph, F))
    x = core(w, ph, gw, inn, ile)
    le = w.s([x['len'], x['lle']], 'eqbrtrd', '( %s -> ( # ` %s ) <_ %s )' % (ph, CW('I'), LEN))
    w.qed([x['cw'], x['tn'], le], '3jca', ST_WCP)
    return w.run()


def ttwcs():
    w = W('ttwcs', 'One step of the counter of ` walkDown ` : ` predBits ` takes the counter word at step ` I ` '
                   'to that at step ` I + 1 ` (a padded word keeps its length, a canonical one stays canonical; '
                   'Lean ` walkBody_runs ` \'s ` predBits l ` ).')
    ph = '( G e. Word 2o /\\ I e. NN0 /\\ I < %s )' % F
    gw = w.s([], 'simp1', '( %s -> G e. Word 2o )' % ph)
    inn = w.s([], 'simp2', '( %s -> I e. NN0 )' % ph)
    ilt = w.s([], 'simp3', '( %s -> I < %s )' % (ph, F))
    fnn = w.s([gw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, F))
    ile = w.s([w.s([inn], 'nn0red', '( %s -> I e. RR )' % ph), w.s([fnn], 'nn0red', '( %s -> %s e. RR )' % (ph, F)), ilt],
              'ltled', '( %s -> I <_ %s )' % (ph, F))
    x = core(w, ph, gw, inn, ile)
    g = x['g']
    V = x['V']
    I1 = '( I + 1 )'
    V1 = '( %s - %s )' % (F, I1)
    iz = w.s([inn], 'nn0zd', '( %s -> I e. ZZ )' % ph)
    fz = w.s([g['fn']], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, F))
    vnn = w.s([ilt, w.s([iz, fz, w.inst('znnsub')], 'syl2anc', '( %s -> ( I < %s <-> %s e. NN ) )' % (ph, F, V))], 'mpbid',
              '( %s -> %s e. NN )' % (ph, V))
    cl = Closure(w, ph, {F: ('NN0', g['fn']), 'I': ('NN0', inn)})
    ve = lineq(w, ph, '( %s - 1 )' % V, V1, closure=cl)
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, I1))
    # case canonical
    a1 = '( %s /\\ %s )' % (ph, CA)
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (a1, concl(w, ph, st)))
    ca = w.s([], 'simpr', '( %s -> %s )' % (a1, CA))
    it0 = w.s([ca], 'iftrued', '( %s -> %s = ( bl ` %s ) )' % (a1, LNC('I'), V))
    it1 = w.s([ca], 'iftrued', '( %s -> %s = ( bl ` %s ) )' % (a1, LNC(I1), V1))
    c0 = w.s([it0], 'oveq2d', '( %s -> %s = ( %s bwrd ( bl ` %s ) ) )' % (a1, CW('I'), V, V))
    en = w.s([L1(x['vn']), w.inst('encnatbwrd')], 'syl', '( %s -> ( encodeNat ` %s ) = ( %s bwrd ( bl ` %s ) ) )' % (a1, V, V, V))
    c0e = w.s([c0, en], 'eqtr4d', '( %s -> %s = ( encodeNat ` %s ) )' % (a1, CW('I'), V))
    pb = w.s([c0e], 'fveq2d', '( %s -> ( predBits ` %s ) = ( predBits ` ( encodeNat ` %s ) ) )' % (a1, CW('I'), V))
    pe = w.s([L1(vnn), w.inst('tmcpredenc')], 'syl', '( %s -> ( predBits ` ( encodeNat ` %s ) ) = ( encodeNat ` ( %s - 1 ) ) )' % (a1, V, V))
    pe2 = w.s([w.s([L1(ve)], 'fveq2d', '( %s -> ( encodeNat ` ( %s - 1 ) ) = ( encodeNat ` %s ) )' % (a1, V, V1))], 'id', '') if False else \
        w.s([L1(ve)], 'fveq2d', '( %s -> ( encodeNat ` ( %s - 1 ) ) = ( encodeNat ` %s ) )' % (a1, V, V1))
    v1n = w.s([i1n, g['fn'], w.s([ilt, w.s([iz, fz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( I < %s <-> %s <_ %s ) )' % (ph, F, I1, F))], 'mpbid',
                                  '( %s -> %s <_ %s )' % (ph, I1, F)), w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, V1))
    en1 = w.s([L1(v1n), w.inst('encnatbwrd')], 'syl', '( %s -> ( encodeNat ` %s ) = ( %s bwrd ( bl ` %s ) ) )' % (a1, V1, V1, V1))
    c1 = w.s([it1], 'oveq2d', '( %s -> %s = ( %s bwrd ( bl ` %s ) ) )' % (a1, CW(I1), V1, V1))
    r1 = w.s([w.s([w.s([pb, pe], 'eqtrd', '( %s -> ( predBits ` %s ) = ( encodeNat ` ( %s - 1 ) ) )' % (a1, CW('I'), V)), pe2], 'eqtrd',
                  '( %s -> ( predBits ` %s ) = ( encodeNat ` %s ) )' % (a1, CW('I'), V1)), en1], 'eqtrd',
             '( %s -> ( predBits ` %s ) = ( %s bwrd ( bl ` %s ) ) )' % (a1, CW('I'), V1, V1))
    b1 = w.s([r1, c1], 'eqtr4d', '( %s -> ( predBits ` %s ) = %s )' % (a1, CW('I'), CW(I1)))
    # case padded
    a2 = '( %s /\\ -. %s )' % (ph, CA)
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (a2, concl(w, ph, st)))
    nc = w.s([], 'simpr', '( %s -> -. %s )' % (a2, CA))
    if0 = w.s([nc], 'iffalsed', '( %s -> %s = %s )' % (a2, LNC('I'), LEN))
    if1 = w.s([nc], 'iffalsed', '( %s -> %s = %s )' % (a2, LNC(I1), LEN))
    pv = w.s([L2(x['cw']), w.inst('predbitsval')], 'syl', '( %s -> ( predBits ` %s ) = ( ( ( toNat ` %s ) - 1 ) bwrd if ( ( 2 x. ( toNat ` %s ) ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) - 1 ) , ( # ` %s ) ) ) )'
             % (a2, CW('I'), CW('I'), CW('I'), CW('I'), CW('I'), CW('I')))
    tn2 = L2(x['tn'])
    ln2 = w.s([L2(x['len']), if0], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (a2, CW('I'), LEN))
    # 2 V =/= 2 ^ # G
    bl = L2(g['bl'])
    ne = w.s([bl, w.s([nc], 'necon3ai' if False else 'id', '') if False else nc], 'id', '') if False else None
    blne = w.s([nc], 'neqned', '( %s -> %s =/= %s )' % (a2, LEN, BLF))
    bllt = w.s([w.s([L2(g['bn'])], 'nn0red', '( %s -> %s e. RR )' % (a2, BLF)), w.s([L2(g['ln'])], 'nn0red', '( %s -> %s e. RR )' % (a2, LEN)), bl, blne],
               'leneltd', '( %s -> %s < %s )' % (a2, BLF, LEN))
    b1le = w.s([w.s([w.s([L2(g['bn'])], 'nn0zd', '( %s -> %s e. ZZ )' % (a2, BLF)), w.s([L2(g['ln'])], 'nn0zd', '( %s -> %s e. ZZ )' % (a2, LEN)),
                     w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> ( %s + 1 ) <_ %s ) )' % (a2, BLF, LEN, BLF, LEN)), bllt], 'mpbird' if False else 'mpbid' if False else 'bitrd' if False else 'mpbid', '') if False else \
        w.s([bllt, w.s([w.s([L2(g['bn'])], 'nn0zd', '( %s -> %s e. ZZ )' % (a2, BLF)), w.s([L2(g['ln'])], 'nn0zd', '( %s -> %s e. ZZ )' % (a2, LEN)),
                        w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> ( %s + 1 ) <_ %s ) )' % (a2, BLF, LEN, BLF, LEN))], 'mpbid',
            '( %s -> ( %s + 1 ) <_ %s )' % (a2, BLF, LEN))
    uz = w.s([w.s([w.s([L2(g['bn']), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (a2, BLF))], 'nn0zd', '( %s -> ( %s + 1 ) e. ZZ )' % (a2, BLF)),
              w.s([L2(g['ln'])], 'nn0zd', '( %s -> %s e. ZZ )' % (a2, LEN)), b1le, w.inst('eluz2')], 'syl3anbrc',
             '( %s -> %s e. ( ZZ>= ` ( %s + 1 ) ) )' % (a2, LEN, BLF))
    le2 = w.s([closed(w, a2, '2re', '2 e. RR'), closed(w, a2, '1le2', '1 <_ 2'), uz, w.inst('leexp2a')], 'syl3anc',
              '( %s -> ( 2 ^ ( %s + 1 ) ) <_ ( 2 ^ %s ) )' % (a2, BLF, LEN))
    ep = w.s([closed(w, a2, '2cn', '2 e. CC'), L2(g['bn']), w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( ( 2 ^ %s ) x. 2 ) )' % (a2, BLF, BLF))
    le3 = w.s([ep, le2], 'eqbrtrrd', '( %s -> ( ( 2 ^ %s ) x. 2 ) <_ ( 2 ^ %s ) )' % (a2, BLF, LEN))
    fb = w.s([L2(g['fn']), w.inst('blpow2')], 'syl', '( %s -> %s < ( 2 ^ %s ) )' % (a2, F, BLF))
    cl2 = Closure(w, a2, {F: ('NN0', L2(g['fn'])), 'I': ('NN0', L2(inn))})
    for e_, st_ in [('( 2 ^ %s )' % BLF, w.s([closed(w, a2, '2nn0', '2 e. NN0'), L2(g['bn']), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (a2, BLF))),
                    ('( 2 ^ %s )' % LEN, w.s([closed(w, a2, '2nn0', '2 e. NN0'), L2(g['ln']), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (a2, LEN)))]:
        cl2.leaf(e_, 'NN0', st_)
    lt = linarith(w, a2, [fb, le3, cl2.ge0('I')], '( 2 x. %s ) < ( 2 ^ %s )' % (V, LEN), closure=cl2)
    ne2 = w.s([cl2.mem('( 2 x. %s )' % V, 'RR'), lt], 'ltned', '( %s -> ( 2 x. %s ) =/= ( 2 ^ %s ) )' % (a2, V, LEN))
    ne3 = w.s([ne2], 'neneqd', '( %s -> -. ( 2 x. %s ) = ( 2 ^ %s ) )' % (a2, V, LEN))
    COND = '( 2 x. ( toNat ` %s ) ) = ( 2 ^ ( # ` %s ) )' % (CW('I'), CW('I'))
    ceq = w.s([w.s([tn2], 'oveq2d', '( %s -> ( 2 x. ( toNat ` %s ) ) = ( 2 x. %s ) )' % (a2, CW('I'), V)),
               w.s([ln2], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = ( 2 ^ %s ) )' % (a2, CW('I'), LEN))], 'eqeq12d',
              '( %s -> ( %s <-> ( 2 x. %s ) = ( 2 ^ %s ) ) )' % (a2, COND, V, LEN))
    nc2 = w.s([ceq, ne3], 'mtbird', '( %s -> -. %s )' % (a2, COND))
    itf = w.s([nc2], 'iffalsed', '( %s -> if ( %s , ( ( # ` %s ) - 1 ) , ( # ` %s ) ) = ( # ` %s ) )' % (a2, COND, CW('I'), CW('I'), CW('I')))
    ife = w.s([itf, ln2], 'eqtrd', '( %s -> if ( %s , ( ( # ` %s ) - 1 ) , ( # ` %s ) ) = %s )' % (a2, COND, CW('I'), CW('I'), LEN))
    t1 = w.s([w.s([tn2], 'oveq1d', '( %s -> ( ( toNat ` %s ) - 1 ) = ( %s - 1 ) )' % (a2, CW('I'), V)), L2(ve)], 'eqtrd',
             '( %s -> ( ( toNat ` %s ) - 1 ) = %s )' % (a2, CW('I'), V1))
    r2 = w.s([t1, ife], 'oveq12d', '( %s -> ( ( ( toNat ` %s ) - 1 ) bwrd if ( %s , ( ( # ` %s ) - 1 ) , ( # ` %s ) ) ) = ( %s bwrd %s ) )'
             % (a2, CW('I'), COND, CW('I'), CW('I'), V1, LEN))
    c2 = w.s([if1], 'oveq2d', '( %s -> %s = ( %s bwrd %s ) )' % (a2, CW(I1), V1, LEN))
    b2 = w.s([w.s([pv, r2], 'eqtrd', '( %s -> ( predBits ` %s ) = ( %s bwrd %s ) )' % (a2, CW('I'), V1, LEN)), c2], 'eqtr4d',
             '( %s -> ( predBits ` %s ) = %s )' % (a2, CW('I'), CW(I1)))
    w.qed([b1, b2], 'pm2.61dan', ST_WCS)
    return w.run()


GS = lambda x: "( ( freeMnd ` Gamma' ) gsum %s )" % x
ST_REPS = "( ( Z e. Gamma' /\\ L e. NN0 ) -> %s = ( Z repeatS L ) )" % GS('( <" Z "> repeatS L )')


def ttreps():
    w = W('ttreps', 'The free-monoid sum of ` L ` copies of the one-letter word ` <" Z "> ` is ` Z ` repeated '
                    '` L ` times.')
    ph = "Z e. Gamma'"
    PS = lambda t: '%s = ( Z repeatS %s )' % (GS('( <" Z "> repeatS %s )' % t), t)
    def sb(a, b):
        e = w.s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('n', '0'), sb('n', 'k'), sb('n', '( k + 1 )'), sb('n', 'L')
    zg = w.s([], 'id', '( %s -> %s )' % (ph, ph))
    s1g = w.s([zg], 's1cld', "( %s -> <\" Z \"> e. Word Gamma' )" % ph)
    r0 = w.s([s1g, w.inst('repsw0')], 'syl', '( %s -> ( <" Z "> repeatS 0 ) = (/) )' % ph)
    g0 = w.s([w.s([r0], 'oveq2d', '( %s -> %s = %s )' % (ph, GS('( <" Z "> repeatS 0 )'), GS('(/)'))), closed(w, ph, 'gsumgam0', '%s = (/)' % GS('(/)'))],
             'eqtrd', '( %s -> %s = (/) )' % (ph, GS('( <" Z "> repeatS 0 )')))
    z0 = w.s([zg, w.inst('repsw0')], 'syl', '( %s -> ( Z repeatS 0 ) = (/) )' % ph)
    base = w.s([g0, z0], 'eqtr4d', '( %s -> %s )' % (ph, PS('0')))
    a = '( ( %s /\\ k e. NN0 ) /\\ %s )' % (ph, PS('k'))
    za = w.s([], 'simpll', '( %s -> %s )' % (a, ph))
    kn = w.s([], 'simplr', '( %s -> k e. NN0 )' % a)
    ih = w.s([], 'simpr', '( %s -> %s )' % (a, PS('k')))
    s1a = w.s([za], 's1cld', "( %s -> <\" Z \"> e. Word Gamma' )" % a)
    one = closed(w, a, '1nn0', '1 e. NN0')
    rc = w.s([s1a, kn, one, w.inst('repswccat')], 'syl3anc', '( %s -> ( ( <" Z "> repeatS k ) ++ ( <" Z "> repeatS 1 ) ) = ( <" Z "> repeatS ( k + 1 ) ) )' % a)
    r1 = w.s([s1a, w.inst('repsw1')], 'syl', '( %s -> ( <" Z "> repeatS 1 ) = <" <" Z "> "> )' % a)
    RK = '( <" Z "> repeatS k )'
    e1 = w.s([w.s([r1], 'oveq2d', '( %s -> ( %s ++ ( <" Z "> repeatS 1 ) ) = ( %s ++ <" <" Z "> "> ) )' % (a, RK, RK)), rc], 'eqtr3d',
             '( %s -> ( %s ++ <" <" Z "> "> ) = ( <" Z "> repeatS ( k + 1 ) ) )' % (a, RK))
    g1 = w.s([e1], 'oveq2d', '( %s -> %s = %s )' % (a, GS('( %s ++ <" <" Z "> "> )' % RK), GS('( <" Z "> repeatS ( k + 1 ) )')))
    rkw = w.s([s1a, kn, w.inst('repsw')], 'syl2anc', "( %s -> %s e. Word Word Gamma' )" % (a, RK))
    ssw = w.s([s1a], 's1cld', "( %s -> <\" <\" Z \"> \"> e. Word Word Gamma' )" % a)
    gc = w.s([rkw, ssw, w.inst('gsumgamccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (a, GS('( %s ++ <" <" Z "> "> )' % RK), GS(RK), GS('<" <" Z "> ">')))
    gs1 = w.s([s1a, w.inst('gsumgams1')], 'syl', '( %s -> %s = <" Z "> )' % (a, GS('<" <" Z "> ">')))
    rz = w.s([ih, gs1], 'oveq12d', '( %s -> ( %s ++ %s ) = ( ( Z repeatS k ) ++ <" Z "> ) )' % (a, GS(RK), GS('<" <" Z "> ">')))
    zr1 = w.s([za, w.inst('repsw1')], 'syl', '( %s -> ( Z repeatS 1 ) = <" Z "> )' % a)
    zc = w.s([za, kn, one, w.inst('repswccat')], 'syl3anc', '( %s -> ( ( Z repeatS k ) ++ ( Z repeatS 1 ) ) = ( Z repeatS ( k + 1 ) ) )' % a)
    zc2 = w.s([w.s([zr1], 'oveq2d', '( %s -> ( ( Z repeatS k ) ++ ( Z repeatS 1 ) ) = ( ( Z repeatS k ) ++ <" Z "> ) )' % a), zc], 'eqtr3d',
              '( %s -> ( ( Z repeatS k ) ++ <" Z "> ) = ( Z repeatS ( k + 1 ) ) )' % a)
    st = w.s([w.s([w.s([w.s([g1], 'eqcomd', '( %s -> %s = %s )' % (a, GS('( <" Z "> repeatS ( k + 1 ) )'), GS('( %s ++ <" <" Z "> "> )' % RK))), gc], 'eqtrd',
                        '( %s -> %s = ( %s ++ %s ) )' % (a, GS('( <" Z "> repeatS ( k + 1 ) )'), GS(RK), GS('<" <" Z "> ">'))), rz], 'eqtrd',
                  '( %s -> %s = ( ( Z repeatS k ) ++ <" Z "> ) )' % (a, GS('( <" Z "> repeatS ( k + 1 ) )'))), zc2], 'eqtrd', '( %s -> %s )' % (a, PS('( k + 1 )')))
    w.qed([h1, h2, h3, h4, base, st], 'nn0indd', ST_REPS)
    return w.run()


def ttetb0():
    w = W('ttetb0', 'The empty table on ` [ 0 , L ) ` is ` L ` kets (Lean ` encTblAsc_emptyTbl ` ).')
    ph = 'L e. NN0'
    NN = '( inr ` (/) )'
    ln = w.s([], 'id', '( %s -> %s )' % (ph, ph))
    tb = closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl')
    v = w.s([ln, tb, w.inst('ttabtbav')], 'syl2anc', '( %s -> ( L encTblAsc EmptyTbl ) = %s )' % (ph, GS('( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) )')))
    d = w.s([], 'df-emptytbl', 'EmptyTbl = ( r e. NN0 |-> %s )' % NN)
    fc = w.s([], 'fconstmpt', '( NN0 X. { %s } ) = ( r e. NN0 |-> %s )' % (NN, NN))
    ec = w.s([d, fc], 'eqtr4i', 'EmptyTbl = ( NN0 X. { %s } )' % NN)
    r1 = w.s([ec], 'reseq1i', '( EmptyTbl |` ( 0 ..^ L ) ) = ( ( NN0 X. { %s } ) |` ( 0 ..^ L ) )' % NN)
    r2 = w.s([w.s([], 'fzo0ssnn0', '( 0 ..^ L ) C_ NN0'), w.inst('xpssres')], 'ax-mp', '( ( NN0 X. { %s } ) |` ( 0 ..^ L ) ) = ( ( 0 ..^ L ) X. { %s } )' % (NN, NN))
    r3 = w.s([r1, r2], 'eqtri', '( EmptyTbl |` ( 0 ..^ L ) ) = ( ( 0 ..^ L ) X. { %s } )' % NN)
    c1 = w.s([r3], 'coeq2i', '( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) ) = ( encSlot o. ( ( 0 ..^ L ) X. { %s } ) )' % NN)
    fnn = w.s([w.s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT), w.inst('ffn')], 'ax-mp', 'encSlot Fn %s' % SLOT)
    nsl = w.s([w.s([], '0lt1o', '(/) e. 1o'), w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NN, SLOT))
    c2 = w.s([fnn, nsl, w.inst('fcoconst')], 'mp2an', '( encSlot o. ( ( 0 ..^ L ) X. { %s } ) ) = ( ( 0 ..^ L ) X. { %s } )' % (NN, ESL(NN)))
    sv = w.s([nsl, w.inst('ttabslotv')], 'ax-mp', '%s = if ( %s = %s , <" 3 "> , ( encList ` ( 2nd ` %s ) ) )' % (ESL(NN), NN, NN, NN))
    it = w.s([w.s([], 'eqid', '%s = %s' % (NN, NN))], 'iftruei', 'if ( %s = %s , <" 3 "> , ( encList ` ( 2nd ` %s ) ) ) = <" 3 ">' % (NN, NN, NN))
    s3 = w.s([sv, it], 'eqtri', '%s = <" 3 ">' % ESL(NN))
    c3 = w.s([w.s([s3], 'sneqi', '{ %s } = { <" 3 "> }' % ESL(NN))], 'xpeq2i', '( ( 0 ..^ L ) X. { %s } ) = ( ( 0 ..^ L ) X. { <" 3 "> } )' % ESL(NN))
    cc = w.s([w.s([c1, c2], 'eqtri', '( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) ) = ( ( 0 ..^ L ) X. { %s } )' % ESL(NN)), c3], 'eqtri',
             '( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) ) = ( ( 0 ..^ L ) X. { <" 3 "> } )')
    s3w = closed(w, ph, 's1cl' if False else 'eqid', '') if False else None
    g3 = w.s([w.s([], 'gamma3', "3 e. Gamma'"), w.inst('s1cl')], 'ax-mp', "<\" 3 \"> e. Word Gamma'")
    rc = w.s([w.s([g3], 'a1i', "( %s -> <\" 3 \"> e. Word Gamma' )" % ph), ln, w.inst('repsconst')], 'syl2anc',
             '( %s -> ( <" 3 "> repeatS L ) = ( ( 0 ..^ L ) X. { <" 3 "> } ) )' % ph)
    cc2 = w.s([w.s([cc], 'a1i', '( %s -> ( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) ) = ( ( 0 ..^ L ) X. { <" 3 "> } ) )' % ph), rc], 'eqtr4d',
              '( %s -> ( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) ) = ( <" 3 "> repeatS L ) )' % ph)
    g = w.s([cc2], 'oveq2d', '( %s -> %s = %s )' % (ph, GS('( encSlot o. ( EmptyTbl |` ( 0 ..^ L ) ) )'), GS('( <" 3 "> repeatS L )')))
    tr = w.s([closed(w, ph, 'gamma3', "3 e. Gamma'"), ln, w.inst('ttreps')], 'syl2anc', '( %s -> %s = ( 3 repeatS L ) )' % (ph, GS('( <" 3 "> repeatS L )')))
    w.qed([w.s([v, g], 'eqtrd', '( %s -> ( L encTblAsc EmptyTbl ) = %s )' % (ph, GS('( <" 3 "> repeatS L )'))), tr], 'eqtrd', ST_ETB0)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
