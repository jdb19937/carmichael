"""T7c: Lean's ` bitlen x y s s' ` (Prims.lean) at the machine, on the installation
predicate TMIbitlen.

  defs       append the syntax and df- of TMIbitlen
  tmiblu     the unfolding theorem
  tmibltop   the top bits: floor ( F / 2 ^ M ) = 2 floor ( F / 2 ^ ( M + 1 ) ) + bit M
  tmiblst    Lean ` bl_step ` : bl ( 2 A + B ) = bl A + 1 for a nonzero 2 A + B , B a bit
  tmiblw1    the scan word: the reversed low bits lose their top bit
  tmiblw2    the rebuilt word: the high bits gain the next bit

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_g_bl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *
from cl import Closure
import lin
from lin import linarith, lineq, nlinarith

lin.FASTPATH = True
SEL = sys.argv[1:]

BLF = FRAGS['bl']


def defs():
    import t7b_a_defs as AD
    AD.main(['bl'])


def tmiblu():
    import t7b_b_unf as UF
    return UF.unf('bl')


BITM = 'if ( M e. ( bits ` F ) , 1 , 0 )'
BITO = 'if ( M e. ( bits ` F ) , 1o , (/) )'
Q0 = '( |_ ` ( F / ( 2 ^ M ) ) )'
Q1 = '( |_ ` ( F / ( 2 ^ ( M + 1 ) ) ) )'
ST_TOP = '( ( F e. NN0 /\\ M e. NN0 ) -> %s = ( ( 2 x. %s ) + %s ) )' % (Q0, Q1, BITM)


def q_facts(w, ph, fn, mn):
    """q = floor ( F / 2 ^ M ) e. NN0, floor ( q / 2 ) = Q1, M e. bits F <-> -. 2 || q"""
    p = '( 2 ^ M )'
    pnn = w.s([closed(w, ph, '2nn', '2 e. NN'), mn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, p))
    qn = w.s([fn, pnn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Q0))
    fr = w.s([fn], 'nn0red', '( %s -> F e. RR )' % ph)
    f2 = w.s([fr, pnn, closed(w, ph, '2nn', '2 e. NN'), w.inst('fldiv2')], 'syl3anc',
             '( %s -> ( |_ ` ( %s / 2 ) ) = ( |_ ` ( F / ( %s x. 2 ) ) ) )' % (ph, Q0, p))
    ep = w.s([closed(w, ph, '2cn', '2 e. CC'), mn, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( M + 1 ) ) = ( %s x. 2 ) )' % (ph, p))
    f3 = w.s([f2, w.s([w.s([w.s([ep], 'eqcomd', '( %s -> ( %s x. 2 ) = ( 2 ^ ( M + 1 ) ) )' % (ph, p))], 'oveq2d',
                           '( %s -> ( F / ( %s x. 2 ) ) = ( F / ( 2 ^ ( M + 1 ) ) ) )' % (ph, p))], 'fveq2d',
                     '( %s -> ( |_ ` ( F / ( %s x. 2 ) ) ) = %s )' % (ph, p, Q1))], 'eqtrd', '( %s -> ( |_ ` ( %s / 2 ) ) = %s )' % (ph, Q0, Q1))
    fz = w.s([fn], 'nn0zd', '( %s -> F e. ZZ )' % ph)
    bv = w.s([fz, mn, w.inst('bitsval2')], 'syl2anc', '( %s -> ( M e. ( bits ` F ) <-> -. 2 || %s ) )' % (ph, Q0))
    return qn, f3, bv


def tmibltop():
    lab = 'tmibltop'
    ph = '( F e. NN0 /\\ M e. NN0 )'
    w = W(lab, 'The number on ` x ` after one more bit of ` bitlen ` \'s scan: ` floor ( F / 2 ^ M ) ` is twice '
               '` floor ( F / 2 ^ ( M + 1 ) ) ` plus the bit ` M ` of ` F ` .')
    fn = w.s([], 'simpl', '( %s -> F e. NN0 )' % ph)
    mn = w.s([], 'simpr', '( %s -> M e. NN0 )' % ph)
    qn, f3, bv = q_facts(w, ph, fn, mn)
    qr = w.s([qn], 'nn0red', '( %s -> %s e. RR )' % (ph, Q0))
    two = closed(w, ph, '2rp', '2 e. RR+')
    fm = w.s([qr, two, w.inst('flpmodeq')], 'syl2anc', '( %s -> ( ( ( |_ ` ( %s / 2 ) ) x. 2 ) + ( %s mod 2 ) ) = %s )' % (ph, Q0, Q0, Q0))
    qz = w.s([qn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, Q0))
    # q mod 2 = BITM
    A1 = '( %s /\\ M e. ( bits ` F ) )' % ph
    A2 = '( %s /\\ -. M e. ( bits ` F ) )' % ph
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A1, concl(w, ph, st)))
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ph, st)))
    nd = w.s([w.s([], 'simpr', '( %s -> M e. ( bits ` F ) )' % A1), L1(bv)], 'mpbid', '( %s -> -. 2 || %s )' % (A1, Q0))
    m1 = w.s([nd, w.s([L1(qz), w.inst('mod2eq1n2dvds')], 'syl', '( %s -> ( ( %s mod 2 ) = 1 <-> -. 2 || %s ) )' % (A1, Q0, Q0))], 'mpbird',
             '( %s -> ( %s mod 2 ) = 1 )' % (A1, Q0))
    b1 = w.s([m1, w.s([w.s([], 'simpr', '( %s -> M e. ( bits ` F ) )' % A1)], 'iftrued', '( %s -> %s = 1 )' % (A1, BITM))], 'eqtr4d',
             '( %s -> ( %s mod 2 ) = %s )' % (A1, Q0, BITM))
    dv = w.s([w.s([], 'simpr', '( %s -> -. M e. ( bits ` F ) )' % A2), L2(bv)], 'mtbid', '( %s -> -. -. 2 || %s )' % (A2, Q0))
    dv2 = w.s([dv], 'notnotrd', '( %s -> 2 || %s )' % (A2, Q0))
    m0 = w.s([dv2, w.s([L2(qz), w.inst('mod2eq0even')], 'syl', '( %s -> ( ( %s mod 2 ) = 0 <-> 2 || %s ) )' % (A2, Q0, Q0))], 'mpbird',
             '( %s -> ( %s mod 2 ) = 0 )' % (A2, Q0))
    b0 = w.s([m0, w.s([w.s([], 'simpr', '( %s -> -. M e. ( bits ` F ) )' % A2)], 'iffalsed', '( %s -> %s = 0 )' % (A2, BITM))], 'eqtr4d',
             '( %s -> ( %s mod 2 ) = %s )' % (A2, Q0, BITM))
    mb = w.s([b1, b0], 'pm2.61dan', '( %s -> ( %s mod 2 ) = %s )' % (ph, Q0, BITM))
    q1n = w.s([w.s([fn, w.s([closed(w, ph, '2nn', '2 e. NN'), w.s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( M + 1 ) e. NN0 )' % ph), w.inst('nnexpcl')],
                                'syl2anc', '( %s -> ( 2 ^ ( M + 1 ) ) e. NN )' % ph), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Q1))],
              'nn0cnd', '( %s -> %s e. CC )' % (ph, Q1))
    e1 = w.s([w.s([w.s([f3], 'oveq1d', '( %s -> ( ( |_ ` ( %s / 2 ) ) x. 2 ) = ( %s x. 2 ) )' % (ph, Q0, Q1)), mb], 'oveq12d',
                  '( %s -> ( ( ( |_ ` ( %s / 2 ) ) x. 2 ) + ( %s mod 2 ) ) = ( ( %s x. 2 ) + %s ) )' % (ph, Q0, Q0, Q1, BITM)), fm], 'eqtr3d',
             '( %s -> %s = ( ( %s x. 2 ) + %s ) )' % (ph, Q0, Q1, BITM))
    cm = w.s([q1n, closed(w, ph, '2cn', '2 e. CC'), w.inst('mulcom')], 'syl2anc', '( %s -> ( %s x. 2 ) = ( 2 x. %s ) )' % (ph, Q1, Q1))
    w.qed([e1, w.s([cm], 'oveq1d', '( %s -> ( ( %s x. 2 ) + %s ) = ( ( 2 x. %s ) + %s ) )' % (ph, Q1, BITM, Q1, BITM))], 'eqtrd', ST_TOP)
    return w.run()


XAB = '( ( 2 x. A ) + B )'
ST_BLST = '( ( A e. NN0 /\\ ( B = 0 \\/ B = 1 ) /\\ %s =/= 0 ) -> ( bl ` %s ) = ( ( bl ` A ) + 1 ) )' % (XAB, XAB)


def tmiblst():
    lab = 'tmiblst'
    ph = '( A e. NN0 /\\ ( B = 0 \\/ B = 1 ) /\\ %s =/= 0 )' % XAB
    w = W(lab, 'The bit length grows by one when a bit is appended below a number and the result is nonzero '
               '(Lean ` bl_step ` , the case ` 2 a + b =/= 0 ` ).')
    an = w.s([], 'simp1', '( %s -> A e. NN0 )' % ph)
    bo = w.s([], 'simp2', '( %s -> ( B = 0 \\/ B = 1 ) )' % ph)
    xn0 = w.s([], 'simp3', '( %s -> %s =/= 0 )' % (ph, XAB))
    # B e. NN0 , 0 <_ B <_ 1
    bn = w.s([bo, w.s([w.s([], 'id', '( B = 0 -> B = 0 )'), w.s([], '0nn0', '0 e. NN0')], 'eqeltrdi' if False else 'syl6eqel' if False else 'eqeltrrid' if False else 'eqeltrdi', '( B = 0 -> B e. NN0 )'),
              w.s([w.s([], 'id', '( B = 1 -> B = 1 )'), w.s([], '1nn0', '1 e. NN0')], 'eqeltrdi', '( B = 1 -> B e. NN0 )'), w.inst('jaoi') if False else w.inst('jaoi')],
             '', '') if False else None
    b0 = w.s([w.s([], '0nn0', '0 e. NN0')], 'eqeltrdi' if False else 'a1i', '') if False else None
    bnn0_0 = w.s([w.s([], 'id', '( B = 0 -> B = 0 )'), w.s([], '0nn0', '0 e. NN0')], 'eqeltrdi', '( B = 0 -> B e. NN0 )')
    bnn0_1 = w.s([w.s([], 'id', '( B = 1 -> B = 1 )'), w.s([], '1nn0', '1 e. NN0')], 'eqeltrdi', '( B = 1 -> B e. NN0 )')
    bnn0 = w.s([bnn0_0, bnn0_1], 'jaoi', '( ( B = 0 \\/ B = 1 ) -> B e. NN0 )')
    bn = w.s([bo, bnn0], 'syl', '( %s -> B e. NN0 )' % ph)
    ble_0 = w.s([w.s([], 'id', '( B = 0 -> B = 0 )'), w.s([], '0le1', '0 <_ 1')], 'eqbrtrdi', '( B = 0 -> B <_ 1 )')
    ble_1 = w.s([w.s([], 'id', '( B = 1 -> B = 1 )'), w.s([w.s([], '1re', '1 e. RR')], 'leidi', '1 <_ 1')], 'eqbrtrdi', '( B = 1 -> B <_ 1 )')
    ble = w.s([bo, w.s([ble_0, ble_1], 'jaoi', '( ( B = 0 \\/ B = 1 ) -> B <_ 1 )')], 'syl', '( %s -> B <_ 1 )' % ph)
    cl = Closure(w, ph, {'A': ('NN0', an), 'B': ('NN0', bn)})
    xn = cl.mem(XAB, 'NN0')
    # case A = 0
    A1 = '( %s /\\ A = 0 )' % ph
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A1, concl(w, ph, st)))
    a0 = w.s([], 'simpr', '( %s -> A = 0 )' % A1)
    cl1 = Closure(w, A1, {'A': ('NN0', L1(an)), 'B': ('NN0', L1(bn))})
    # B =/= 0 : else X = 0
    xb = lineq(w, A1, XAB, 'B', hyps=[a0], closure=cl1)
    bne = w.s([w.s([L1(xn0), xb], 'eqnetrrd' if False else 'eqnetrrd', '( %s -> B =/= 0 )' % A1)], 'neneqd', '( %s -> -. B = 0 )' % A1)
    b1 = w.s([L1(bo), bne], 'ecased' if False else 'orcanai' if False else 'ord', '') if False else None
    b1 = w.s([w.s([L1(bo)], 'ord', '( %s -> ( -. B = 0 -> B = 1 ) )' % A1), bne], 'mpd', '( %s -> B = 1 )' % A1)
    x1 = w.s([xb, b1], 'eqtrd', '( %s -> %s = 1 )' % (A1, XAB))
    one = closed(w, A1, '1nn', '1 e. NN')
    two0 = w.s([closed(w, A1, '1m1e0', '( 1 - 1 ) = 0')], 'oveq2d', '( %s -> ( 2 ^ ( 1 - 1 ) ) = ( 2 ^ 0 ) )' % A1)
    e20 = w.s([two0, closed(w, A1, 'exp0' if False else '2cn', '')], '', '') if False else None
    p0 = w.s([w.s([two0, w.s([closed(w, A1, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % A1)], 'eqtrd',
                  '( %s -> ( 2 ^ ( 1 - 1 ) ) = 1 )' % A1), w.s([w.s([closed(w, A1, '1re', '1 e. RR')], 'leidd', '( %s -> 1 <_ 1 )' % A1)], 'id', '') if False else
              w.s([closed(w, A1, '1re', '1 e. RR')], 'leidd', '( %s -> 1 <_ 1 )' % A1)], 'eqbrtrd', '( %s -> ( 2 ^ ( 1 - 1 ) ) <_ 1 )' % A1)
    p1 = w.s([closed(w, A1, '1lt2', '1 < 2'), w.s([closed(w, A1, '2cn', '2 e. CC'), w.inst('exp1')], 'syl', '( %s -> ( 2 ^ 1 ) = 2 )' % A1)], 'breqtrrd',
             '( %s -> 1 < ( 2 ^ 1 ) )' % A1)
    bc = w.s([w.s([one, one], 'jca', '( %s -> ( 1 e. NN /\\ 1 e. NN ) )' % A1), w.s([p0, p1], 'jca', '( %s -> ( ( 2 ^ ( 1 - 1 ) ) <_ 1 /\\ 1 < ( 2 ^ 1 ) ) )' % A1),
              w.inst('blchar')], 'syl2anc', '( %s -> ( bl ` 1 ) = 1 )' % A1)
    lhs1 = w.s([w.s([x1], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` 1 ) )' % (A1, XAB)), bc], 'eqtrd', '( %s -> ( bl ` %s ) = 1 )' % (A1, XAB))
    ba0 = w.s([w.s([a0], 'fveq2d', '( %s -> ( bl ` A ) = ( bl ` 0 ) )' % A1), closed(w, A1, 'bl0', '( bl ` 0 ) = 0')], 'eqtrd', '( %s -> ( bl ` A ) = 0 )' % A1)
    r1 = w.s([w.s([ba0], 'oveq1d', '( %s -> ( ( bl ` A ) + 1 ) = ( 0 + 1 ) )' % A1), closed(w, A1, '0p1e1', '( 0 + 1 ) = 1')], 'eqtrd',
             '( %s -> ( ( bl ` A ) + 1 ) = 1 )' % A1)
    c1 = w.s([lhs1, r1], 'eqtr4d', '( %s -> ( bl ` %s ) = ( ( bl ` A ) + 1 ) )' % (A1, XAB))
    # case A =/= 0
    A2 = '( %s /\\ -. A = 0 )' % ph
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ph, st)))
    ann = w.s([L2(an), w.s([w.s([], 'simpr', '( %s -> -. A = 0 )' % A2)], 'neqned', '( %s -> A =/= 0 )' % A2), w.inst('elnnne0')], 'sylanbrc', '( %s -> A e. NN )' % A2)
    C_ = '( bl ` A )'
    cn0 = w.s([L2(an), w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (A2, C_))
    cpos = w.s([ann, w.inst('blpos')], 'syl', '( %s -> %s = ( ( 2 Nlog A ) + 1 ) )' % (A2, C_))
    nl = w.s([ann, w.inst('blnlog')], 'syl', '( %s -> ( 2 Nlog A ) = ( %s - 1 ) )' % (A2, C_))
    cl2 = Closure(w, A2, {'A': ('NN', ann), 'B': ('NN0', L2(bn)), C_: ('NN0', cn0)})
    cl2.atom(C_)
    # C_ e. NN : C_ = ( C_ - 1 ) + 1 with ( C_ - 1 ) = Nlog A >= 0
    nlr = w.s([w.s([closed(w, A2, '2z', '2 e. ZZ'), w.inst('uzid')], 'syl', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % A2), ann, w.inst('nlogcl')], 'syl2anc',
              '( %s -> ( 2 Nlog A ) e. NN0 )' % A2) if False else None
    cge = w.s([ann, w.inst('blle2')], 'syl', '( %s -> ( 2 ^ ( %s - 1 ) ) <_ A )' % (A2, C_))
    clt = w.s([L2(an), w.inst('blpow2')], 'syl', '( %s -> A < ( 2 ^ %s ) )' % (A2, C_))
    # C_ e. NN : from 2 ^ ( C_ - 1 ) <_ A and A < 2 ^ C_ we get 0 < C_ (else A < 1)
    cz = w.s([cn0], 'nn0zd', '( %s -> %s e. ZZ )' % (A2, C_))
    B1_ = '( 2 ^ ( %s - 1 ) )'
    # C_ =/= 0 : if C_ = 0 then A < 2 ^ 0 = 1 , A e. NN contradiction
    Z1 = '( %s /\\ %s = 0 )' % (A2, C_)
    LZ = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Z1, concl(w, A2, st)))
    c0 = w.s([], 'simpr', '( %s -> %s = 0 )' % (Z1, C_))
    pz = w.s([w.s([c0], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ 0 ) )' % (Z1, C_)), w.s([closed(w, Z1, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % Z1)],
             'eqtrd', '( %s -> ( 2 ^ %s ) = 1 )' % (Z1, C_))
    al1 = w.s([LZ(clt), pz], 'breqtrd', '( %s -> A < 1 )' % Z1)
    ag1 = w.s([LZ(ann), w.inst('nnge1')], 'syl', '( %s -> 1 <_ A )' % Z1)
    fz = w.s([w.s([closed(w, Z1, '1re', '1 e. RR'), w.s([LZ(ann)], 'nnred', '( %s -> A e. RR )' % Z1)], 'lenltd', '( %s -> ( 1 <_ A <-> -. A < 1 ) )' % Z1), ag1],
             'mpbid', '( %s -> -. A < 1 )' % Z1)
    cne = w.s([w.s([al1, fz], 'pm2.65da' if False else 'pm2.21dd', '( %s -> -. %s = 0 )' % (Z1, C_))], 'id', '') if False else None
    cne = w.s([al1, fz], 'pm2.65da', '( %s -> -. %s = 0 )' % (A2, C_))
    cnnn = w.s([cn0, w.s([cne], 'neqned', '( %s -> %s =/= 0 )' % (A2, C_)), w.inst('elnnne0')], 'sylanbrc', '( %s -> %s e. NN )' % (A2, C_))
    Mx = '( %s + 1 )' % C_
    mnn = w.s([cnnn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (A2, Mx))
    # 2 ^ C_ = 2 ^ ( C_ - 1 ) x. 2 , 2 ^ ( C_ + 1 ) = 2 ^ C_ x. 2
    e1 = w.s([closed(w, A2, '2cn', '2 e. CC'), cnnn, w.inst('expm1t')], 'syl2anc', '( %s -> ( 2 ^ %s ) = ( ( 2 ^ ( %s - 1 ) ) x. 2 ) )' % (A2, C_, C_))
    e2 = w.s([closed(w, A2, '2cn', '2 e. CC'), cn0, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ %s ) = ( ( 2 ^ %s ) x. 2 ) )' % (A2, Mx, C_))
    mm1 = w.s([w.s([cn0], 'nn0cnd', '( %s -> %s e. CC )' % (A2, C_)), closed(w, A2, 'ax-1cn', '1 e. CC'), w.inst('pncan')], 'syl2anc',
              '( %s -> ( %s - 1 ) = %s )' % (A2, Mx, C_))
    e3 = w.s([mm1], 'oveq2d', '( %s -> ( 2 ^ ( %s - 1 ) ) = ( 2 ^ %s ) )' % (A2, Mx, C_))
    P0_, P1_, P2_ = '( 2 ^ ( %s - 1 ) )' % C_, '( 2 ^ %s )' % C_, '( 2 ^ %s )' % Mx
    for a_ in [P0_, P1_, P2_]:
        cl2.atom(a_)
    az = w.s([w.s([ann], 'nnzd', '( %s -> A e. ZZ )' % A2), w.s([w.s([closed(w, A2, '2nn0', '2 e. NN0'), cn0, w.inst('nn0expcl')], 'syl2anc',
                                                                   '( %s -> %s e. NN0 )' % (A2, P1_))], 'nn0zd', '( %s -> %s e. ZZ )' % (A2, P1_)),
              w.inst('zltp1le')], 'syl2anc', '( %s -> ( A < %s <-> ( A + 1 ) <_ %s ) )' % (A2, P1_, P1_))
    a1le = w.s([clt, az], 'mpbid', '( %s -> ( A + 1 ) <_ %s )' % (A2, P1_))
    lo = linarith(w, A2, [e3, e1, cge, cl2.ge0('B')], '( 2 ^ ( %s - 1 ) ) <_ %s' % (Mx, XAB), closure=cl2, atoms=[P0_, P1_, '( 2 ^ ( %s - 1 ) )' % Mx])
    hi = linarith(w, A2, [e2, a1le, L2(ble)], '%s < %s' % (XAB, P2_), closure=cl2, atoms=[P1_, P2_])
    xnn = w.s([L2(xn), L2(xn0), w.inst('elnnne0')], 'sylanbrc', '( %s -> %s e. NN )' % (A2, XAB))
    bc2 = w.s([w.s([xnn, mnn], 'jca', '( %s -> ( %s e. NN /\\ %s e. NN ) )' % (A2, XAB, Mx)), w.s([lo, hi], 'jca', '( %s -> ( ( 2 ^ ( %s - 1 ) ) <_ %s /\\ %s < %s ) )'
                                                                                            % (A2, Mx, XAB, XAB, P2_)), w.inst('blchar')],
              'syl2anc', '( %s -> ( bl ` %s ) = %s )' % (A2, XAB, Mx))
    w.qed([c1, bc2], 'pm2.61dan', ST_BLST)
    return w.run()


LOWM1 = '( ( F mod ( 2 ^ ( M + 1 ) ) ) bwrd ( M + 1 ) )'
LOWM = '( ( F mod ( 2 ^ M ) ) bwrd M )'
ST_W1 = '( ( F e. NN0 /\\ M e. NN0 ) -> ( reverse ` %s ) = ( <" %s "> ++ ( reverse ` %s ) ) )' % (LOWM1, BITO, LOWM)
ST_W2 = '( ( F e. NN0 /\\ M e. NN0 /\\ I e. NN0 ) -> ( %s bwrd ( I + 1 ) ) = ( <" %s "> ++ ( %s bwrd I ) ) )' % (Q0, BITO, Q1)


def tmiblw1():
    lab = 'tmiblw1'
    ph = '( F e. NN0 /\\ M e. NN0 )'
    w = W(lab, 'The word ` bitlen ` scans: the reversed ` M + 1 ` low bits of ` F ` start with the bit ` M ` , '
               'followed by the reversed ` M ` low bits.')
    fn = w.s([], 'simpl', '( %s -> F e. NN0 )' % ph)
    mn = w.s([], 'simpr', '( %s -> M e. NN0 )' % ph)
    fz = w.s([fn], 'nn0zd', '( %s -> F e. ZZ )' % ph)
    m1 = w.s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( M + 1 ) e. NN0 )' % ph)
    u1 = w.s([w.s([m1], 'nn0zd', '( %s -> ( M + 1 ) e. ZZ )' % ph), w.inst('uzid')], 'syl', '( %s -> ( M + 1 ) e. ( ZZ>= ` ( M + 1 ) ) )' % ph)
    u0 = w.s([w.s([mn], 'nn0zd', '( %s -> M e. ZZ )' % ph), w.inst('uzid')], 'syl', '( %s -> M e. ( ZZ>= ` M ) )' % ph)
    a = w.s([fz, m1, u1, w.inst('bwrdmod')], 'syl3anc', '( %s -> %s = ( F bwrd ( M + 1 ) ) )' % (ph, LOWM1))
    b = w.s([fz, mn, w.inst('bwrdp1')], 'syl2anc', '( %s -> ( F bwrd ( M + 1 ) ) = ( ( F bwrd M ) ++ <" %s "> ) )' % (ph, BITO))
    c = w.s([fz, mn, u0, w.inst('bwrdmod')], 'syl3anc', '( %s -> %s = ( F bwrd M ) )' % (ph, LOWM))
    fw = w.s([fz, mn, w.inst('bwrdcl')], 'syl2anc', '( %s -> ( F bwrd M ) e. Word 2o )' % ph)
    bo = w.s([closed(w, ph, '1oel2o', '1o e. 2o'), closed(w, ph, '0el2o', '(/) e. 2o')], 'ifcld', '( %s -> %s e. 2o )' % (ph, BITO))
    sw = w.s([bo], 's1cld', '( %s -> <" %s "> e. Word 2o )' % (ph, BITO))
    rc = w.s([fw, sw, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( ( F bwrd M ) ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) )'
             % (ph, BITO, BITO))
    rs = w.s([bo, w.inst('revs1') if False else w.inst('revs1')], 'a1i', '') if False else None
    rs = closed(w, ph, 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (BITO, BITO))
    ab = w.s([a, b], 'eqtrd', '( %s -> %s = ( ( F bwrd M ) ++ <" %s "> ) )' % (ph, LOWM1, BITO))
    r1 = w.s([ab], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( ( F bwrd M ) ++ <" %s "> ) ) )' % (ph, LOWM1, BITO))
    r2 = w.s([rs, w.s([c], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( F bwrd M ) ) )' % (ph, LOWM))], 'oveq12d',
             '( %s -> ( ( reverse ` <" %s "> ) ++ ( reverse ` %s ) ) = ( <" %s "> ++ ( reverse ` ( F bwrd M ) ) ) )' % (ph, BITO, LOWM, BITO))
    e = w.s([w.s([r1, rc], 'eqtrd', '( %s -> ( reverse ` %s ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) )' % (ph, LOWM1, BITO)),
             w.s([rs], 'oveq1d' if False else 'a1i', '') if False else None], 'id', '') if False else None
    e1 = w.s([r1, rc], 'eqtrd', '( %s -> ( reverse ` %s ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) )' % (ph, LOWM1, BITO))
    e2 = w.s([w.s([rs], 'oveq1d', '( %s -> ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) = ( <" %s "> ++ ( reverse ` ( F bwrd M ) ) ) )'
                  % (ph, BITO, BITO)), r2], 'eqtr4d',
             '( %s -> ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` %s ) ) )' % (ph, BITO, BITO, LOWM)) if False else None
    rr = w.s([w.s([rs], 'oveq1d', '( %s -> ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) = ( <" %s "> ++ ( reverse ` ( F bwrd M ) ) ) )'
                  % (ph, BITO, BITO))], 'id', '') if False else \
        w.s([rs], 'oveq1d',
            '( %s -> ( ( reverse ` <" %s "> ) ++ ( reverse ` ( F bwrd M ) ) ) = ( <" %s "> ++ ( reverse ` ( F bwrd M ) ) ) )' % (ph, BITO, BITO))
    rc2 = w.s([w.s([c], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( F bwrd M ) ) )' % (ph, LOWM))], 'oveq2d',
              '( %s -> ( <" %s "> ++ ( reverse ` %s ) ) = ( <" %s "> ++ ( reverse ` ( F bwrd M ) ) ) )' % (ph, BITO, LOWM, BITO))
    w.qed([w.s([e1, rr], 'eqtrd', '( %s -> ( reverse ` %s ) = ( <" %s "> ++ ( reverse ` ( F bwrd M ) ) ) )' % (ph, LOWM1, BITO)), rc2], 'eqtr4d', ST_W1)
    return w.run()


def tmiblw2():
    lab = 'tmiblw2'
    ph = '( F e. NN0 /\\ M e. NN0 /\\ I e. NN0 )'
    w = W(lab, 'The word ` bitlen ` rebuilds on ` x ` : the ` I + 1 ` low bits of ` floor ( F / 2 ^ M ) ` are the bit '
               '` M ` of ` F ` followed by the ` I ` low bits of ` floor ( F / 2 ^ ( M + 1 ) ) ` .')
    fn = w.s([], 'simp1', '( %s -> F e. NN0 )' % ph)
    mn = w.s([], 'simp2', '( %s -> M e. NN0 )' % ph)
    inn = w.s([], 'simp3', '( %s -> I e. NN0 )' % ph)
    qn, f3, bv = q_facts(w, ph, fn, mn)
    qz = w.s([qn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, Q0))
    BQ = 'if ( 0 e. ( bits ` %s ) , 1o , (/) )' % Q0
    bc = w.s([qz, inn, w.inst('bwrdcons')], 'syl2anc', '( %s -> ( %s bwrd ( I + 1 ) ) = ( <" %s "> ++ ( ( |_ ` ( %s / 2 ) ) bwrd I ) ) )' % (ph, Q0, BQ, Q0))
    b0 = w.s([qz, closed(w, ph, '0nn0', '0 e. NN0'), w.inst('bitsval2')], 'syl2anc',
             '( %s -> ( 0 e. ( bits ` %s ) <-> -. 2 || ( |_ ` ( %s / ( 2 ^ 0 ) ) ) ) )' % (ph, Q0, Q0))
    e0 = w.s([closed(w, ph, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)
    qc = w.s([qn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, Q0))
    d1 = w.s([w.s([e0], 'oveq2d', '( %s -> ( %s / ( 2 ^ 0 ) ) = ( %s / 1 ) )' % (ph, Q0, Q0)), w.s([qc, w.inst('div1')], 'syl', '( %s -> ( %s / 1 ) = %s )' % (ph, Q0, Q0))],
             'eqtrd', '( %s -> ( %s / ( 2 ^ 0 ) ) = %s )' % (ph, Q0, Q0))
    fl = w.s([w.s([d1], 'fveq2d', '( %s -> ( |_ ` ( %s / ( 2 ^ 0 ) ) ) = ( |_ ` %s ) )' % (ph, Q0, Q0)), w.s([qz, w.inst('flid')], 'syl', '( %s -> ( |_ ` %s ) = %s )' % (ph, Q0, Q0))],
             'eqtrd', '( %s -> ( |_ ` ( %s / ( 2 ^ 0 ) ) ) = %s )' % (ph, Q0, Q0))
    b0b = w.s([b0, w.s([w.s([fl], 'breq2d', '( %s -> ( 2 || ( |_ ` ( %s / ( 2 ^ 0 ) ) ) <-> 2 || %s ) )' % (ph, Q0, Q0))], 'notbid',
                       '( %s -> ( -. 2 || ( |_ ` ( %s / ( 2 ^ 0 ) ) ) <-> -. 2 || %s ) )' % (ph, Q0, Q0))], 'bitrd',
              '( %s -> ( 0 e. ( bits ` %s ) <-> -. 2 || %s ) )' % (ph, Q0, Q0))
    bb = w.s([b0b, bv], 'bitr4d', '( %s -> ( 0 e. ( bits ` %s ) <-> M e. ( bits ` F ) ) )' % (ph, Q0))
    ib = w.s([bb], 'ifbid', '( %s -> %s = %s )' % (ph, BQ, BITO))
    r = w.s([w.s([ib], 's1eqd', '( %s -> <" %s "> = <" %s "> )' % (ph, BQ, BITO)), w.s([f3], 'oveq1d', '( %s -> ( ( |_ ` ( %s / 2 ) ) bwrd I ) = ( %s bwrd I ) )' % (ph, Q0, Q1))],
            'oveq12d', '( %s -> ( <" %s "> ++ ( ( |_ ` ( %s / 2 ) ) bwrd I ) ) = ( <" %s "> ++ ( %s bwrd I ) ) )' % (ph, BQ, Q0, BITO, Q1))
    w.qed([bc, r], 'eqtrd', ST_W2)
    return w.run()


# ------------------------------------------------------------ the machine: families of BlInv
K4 = ['K', 'J', 'I', "I'"]
LMB = BLF.lmap()
NF = '( # ` ( encodeNat ` F ) )'
ENCF = '( encodeNat ` F )'
CT = lambda t: 'if ( %s <_ %s , %s , %s )' % (t, NF, t, NF)
TOPX = lambda c: '( |_ ` ( F / ( 2 ^ ( %s - %s ) ) ) )' % (NF, c)
FLV = lambda t: 'if ( %s = 0 , (/) , 1o )' % TOPX(CT(t))
CRV = lambda t: 'if ( %s < %s , 1o , (/) )' % (NF, t)
def NBC(h, t):
    return '( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = %s )' % (h, FLV(t), h, h, CRV(t))
FAMF = lambda cond: '( j e. NN0 |-> { h e. TMSt | %s } )' % cond('h', 'j')
RAB = lambda cond, t: '{ h e. TMSt | %s }' % cond('h', t)
NBF = FAMF(NBC)
XWV = lambda t: '( ( inclBool o. ( %s bwrd %s ) ) ++ ( <" 4 "> ++ X ) )' % (TOPX(CT(t)), CT(t))
YWV = lambda t: EW('( bl ` %s )' % TOPX(CT(t)), '( D ` J )')
LOWV = lambda t: '( ( F mod ( 2 ^ ( %s - %s ) ) ) bwrd ( %s - %s ) )' % (NF, t, NF, t)
SWV = lambda t: 'if ( %s <_ %s , ( ( inclBool o. ( reverse ` %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) ) , ( D ` I ) )' % (t, NF, LOWV(t))
def PBL(t):
    return UP(UP(UP('D', 'K', XWV(t)), 'J', YWV(t)), 'I', SWV(t))
PDFB = '( j e. NN0 |-> %s )' % PBL('j')
PV = "P'"
DATA_BL = (('F e. NN0', WRD('X', GAM), STKD('D')), ('( D ` K ) = %s' % EW('F', 'X'), '%s = %s' % (PV, PDFB)))
T_BL = ((T_PHM7, BLF.pred()), (idx_tree(K4), dist_tree(K4)), DATA_BL)
PHB = cj(T_BL)


class Bc:
    """facts under ps (the bitlen antecedent T_BL, or a substituted tree)"""
    def __init__(self, w, ps, tree=None, root=None, lift=None, pv=None):
        self.w, self.ps = w, ps
        self.PV = pv or PV
        tree = tree or T_BL
        if root is None and ps != cj(tree):
            root = w.s([], lift or 'simpl', '( %s -> %s )' % (ps, cj(tree)))
        self.c = c = Ctx(w, ps, tree, root=root)
        self.mk = machine(w, ps, c, K4)
        self.ne = ne_fn(w, ps, c, set(flat(dist_tree(K4))))
        mk = self.mk
        self.base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        self.base.update(unfold_all(w, ps, c[BLF.pred()], 'bl', K4, 'P', 'E', rec=False))
        lmp = BLF.lmap()
        for j_, (fn_, ks_, en_, ex_) in enumerate(BLF.children):
            P_ = PL('P', BLF.slot(j_))
            pr = FRAGS[fn_].pred(ks_, 'T', 'M', P_, lmp[ex_])
            self.base.update(unfold_all(w, ps, self.base[pr], fn_, ks_, P_, lmp[ex_], rec=False))
        for s_ in K4:
            self.base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K4):
            for b in K4[i_ + 1:]:
                self.base['%s =/= %s' % (a, b)] = self.ne(a, b)
                self.base['%s =/= %s' % (b, a)] = self.ne(b, a)
        self.fn = c['F e. NN0']
        self.efw = w.s([self.fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF))
        self.nfn = w.s([self.efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF))
        self.cl = Closure(w, ps, {'F': ('NN0', self.fn), NF: ('NN0', self.nfn)})
        self.cl.atom(NF)
        self.memo = {}

    def dsg(self, s_):
        key = ('dsg', s_)
        if key not in self.memo:
            w, ps = self.w, self.ps
            self.memo[key] = w.s([stkfv(w, ps, 'D', s_, self.mk['tv'], self.c[STKD('D')], self.mk['k'][s_]['kd']), self.mk['k'][s_]['wge']], 'eleqtrd',
                                 "( %s -> ( D ` %s ) e. Word Gamma' )" % (ps, s_))
        return self.memo[key]

    def ct(self, t, tn):
        """( ps -> CT( t ) e. NN0 ) , ( ps -> CT( t ) <_ NF )"""
        w, ps = self.w, self.ps
        c1 = w.s([tn, self.nfn], 'ifcld', '( %s -> %s e. NN0 )' % (ps, CT(t)))
        A1 = '( %s /\\ %s <_ %s )' % (ps, t, NF)
        A2 = '( %s /\\ -. %s <_ %s )' % (ps, t, NF)
        l1 = w.s([w.s([w.s([], 'simpr', '( %s -> %s <_ %s )' % (A1, t, NF))], 'iftrued', '( %s -> %s = %s )' % (A1, CT(t), t)),
                  w.s([], 'simpr', '( %s -> %s <_ %s )' % (A1, t, NF))], 'eqbrtrd', '( %s -> %s <_ %s )' % (A1, CT(t), NF))
        l2 = w.s([w.s([w.s([], 'simpr', '( %s -> -. %s <_ %s )' % (A2, t, NF))], 'iffalsed', '( %s -> %s = %s )' % (A2, CT(t), NF)),
                  w.s([w.s([w.s([self.nfn], 'adantr', '( %s -> %s e. NN0 )' % (A2, NF))], 'nn0red', '( %s -> %s e. RR )' % (A2, NF))], 'leidd',
                      '( %s -> %s <_ %s )' % (A2, NF, NF))], 'eqbrtrd', '( %s -> %s <_ %s )' % (A2, CT(t), NF))
        c2 = w.s([l1, l2], 'pm2.61dan', '( %s -> %s <_ %s )' % (ps, CT(t), NF))
        return c1, c2

    def topn(self, c_, cn, cle):
        """( ps -> TOPX( c ) e. NN0 ) for c e. NN0 , c <_ NF"""
        w, ps = self.w, self.ps
        d = '( %s - %s )' % (NF, c_)
        dn = w.s([cn, self.nfn, cle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ps, d))
        pn = w.s([closed(w, ps, '2nn', '2 e. NN'), dn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ps, d))
        return w.s([self.fn, pn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, TOPX(c_))), dn, pn

    def pv(self, t, tn):
        """( ps -> ( P' ` t ) = PBL( t ) ) and the Stacks of PBL( t )"""
        key = ('pv', t)
        if key in self.memo:
            return self.memo[key]
        w, ps, c = self.w, self.ps, self.c
        cn, cle = self.ct(t, tn)
        tpn, dn, pn = self.topn(CT(t), cn, cle)
        xw = wgcat(w, ps, '( inclBool o. ( %s bwrd %s ) )' % (TOPX(CT(t)), CT(t)), YX('X'),
                   wib(w, ps, '( %s bwrd %s )' % (TOPX(CT(t)), CT(t)), w.s([w.s([tpn], 'nn0zd', '( %s -> %s e. ZZ )' % (ps, TOPX(CT(t)))), cn, w.inst('bwrdcl')],
                                                                         'syl2anc', '( %s -> ( %s bwrd %s ) e. Word 2o )' % (ps, TOPX(CT(t)), CT(t)))),
                   wg4(w, ps, 'X', c[WRD('X', GAM)]))
        bln = w.s([tpn, w.inst('blcl')], 'syl', '( %s -> ( bl ` %s ) e. NN0 )' % (ps, TOPX(CT(t))))
        yw = ewg(w, ps, '( bl ` %s )' % TOPX(CT(t)), bln, '( D ` J )', self.dsg('J'))
        # SW( t ) typed: both branches words
        A1 = '( %s /\\ %s <_ %s )' % (ps, t, NF)
        L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A1, concl(w, ps, st)))
        d1 = '( %s - %s )' % (NF, t)
        d1n = w.s([w.s([tn], 'adantr', '( %s -> %s e. NN0 )' % (A1, t)), L1(self.nfn), w.s([], 'simpr', '( %s -> %s <_ %s )' % (A1, t, NF)), w.inst('nn0sub2')],
                  'syl3anc', '( %s -> %s e. NN0 )' % (A1, d1))
        p1n = w.s([closed(w, A1, '2nn', '2 e. NN'), d1n, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (A1, d1))
        mdz = w.s([w.s([L1(self.fn)], 'nn0zd', '( %s -> F e. ZZ )' % A1), p1n, w.inst('zmodcl')], 'syl2anc', '( %s -> ( F mod ( 2 ^ %s ) ) e. NN0 )' % (A1, d1))
        lw = w.s([w.s([mdz], 'nn0zd', '( %s -> ( F mod ( 2 ^ %s ) ) e. ZZ )' % (A1, d1)), d1n, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (A1, LOWV(t)))
        rw_ = w.s([lw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word 2o )' % (A1, LOWV(t)))
        SI = '( ( inclBool o. ( reverse ` %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % LOWV(t)
        s1g = wgcat(w, A1, '( inclBool o. ( reverse ` %s ) )' % LOWV(t), YX('( D ` I )'), wib(w, A1, '( reverse ` %s )' % LOWV(t), rw_), wg4(w, A1, '( D ` I )', L1(self.dsg('I'))))
        sg = w.s([w.s([w.s([], 'simpr', '( %s -> %s <_ %s )' % (A1, t, NF))], 'iftrued', '( %s -> %s = %s )' % (A1, SWV(t), SI)), s1g], 'eqeltrd',
                 "( %s -> %s e. Word Gamma' )" % (A1, SWV(t)))
        A2 = '( %s /\\ -. %s <_ %s )' % (ps, t, NF)
        sg2 = w.s([w.s([w.s([], 'simpr', '( %s -> -. %s <_ %s )' % (A2, t, NF))], 'iffalsed', '( %s -> %s = ( D ` I ) )' % (A2, SWV(t))),
                   w.s([self.dsg('I')], 'adantr', "( %s -> ( D ` I ) e. Word Gamma' )" % A2)], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (A2, SWV(t)))
        sw = w.s([sg, sg2], 'pm2.61dan', "( %s -> %s e. Word Gamma' )" % (ps, SWV(t)))
        dd = c[STKD('D')]
        vals = {s_: selfval(w, ps, self.mk, 'D', dd, s_) for s_ in K4}
        S = Stacks(w, ps, self.mk, 'D', dd, self.ne, vals)
        S = S.upd('K', XWV(t), xw).upd('J', YWV(t), yw).upd('I', SWV(t), sw)
        assert S.D == PBL(t)
        pv0 = mval(w, ps, 'j', 'NN0', PBL, t, tn, w.s([S.memb], 'elexd', '( %s -> %s e. _V )' % (ps, PBL(t))))
        pe = w.s([c['%s = %s' % (self.PV, PDFB)]], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, self.PV, t, PDFB, t))
        pvs = w.s([pe, pv0], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, self.PV, t, PBL(t)))
        self.memo[key] = (pvs, S)
        return pvs, S

    def pvals(self, t, tn):
        w, ps = self.w, self.ps
        pvs, S = self.pv(t, tn)
        PT = '( %s ` %s )' % (self.PV, t)
        mem = w.s([pvs, S.memb], 'eqeltrd', '( %s -> %s e. %s )' % (ps, PT, STK_T))
        out = {}
        for s_ in K4:
            txt, st, g = S.vals[s_]
            e = w.s([pvs], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, PT, s_, S.D, s_))
            out[s_] = (txt, w.s([e, st], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PT, s_, txt)), g)
        return mem, Stacks(w, ps, self.mk, PT, mem, self.ne, out)

    def famss(self, t, tn):
        w, ps = self.w, self.ps
        fv = famval(w, ps, NBC, t, tn)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % RAB(NBC, t))], 'a1i', '( %s -> %s C_ TMSt )' % (ps, RAB(NBC, t)))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, RAB(NBC, t)))
        return w.s([fv, s2], 'eqsstrd', '( %s -> ( %s ` %s ) C_ ( 2nd ` T ) )' % (ps, NBF, t))


from t7_e_cmp import togk as togk7, letgk, bitsgk, pbr_ty, cis_ty, lamty
from t7c_d_pgl import ldty
from t7b_h_dmq import rab_elim

WF = '( inclBool o. %s )' % ENCF
PB0 = UP(UP(UP('D', 'K', YX('X')), 'J', YX('( D ` J )')), 'I', CC('( inclBool o. ( reverse ` %s ) )' % ENCF, YX('( D ` I )')))


def upbase(w, ph, D1, D0, k, V, e):
    """( ph -> UPD( D1 , k , V ) = UPD( D0 , k , V ) ) from e : ( ph -> D1 = D0 )"""
    a = w.s([e], 'reseq1d', '( %s -> ( %s |` ( dom ( 1st ` ( 1st ` T ) ) \\ { %s } ) ) = ( %s |` ( dom ( 1st ` ( 1st ` T ) ) \\ { %s } ) ) )' % (ph, D1, k, D0, k))
    return w.s([a], 'uneq1d', '( %s -> %s = %s )' % (ph, UP(D1, k, V), UP(D0, k, V)))


def top0(w, ps, bc):
    """( ps -> TOPX( CT( 0 ) ) = 0 ) and ( ps -> CT( 0 ) = 0 ) , ( ps -> ( NF - 0 ) = NF ) , F < 2 ^ NF"""
    cl = bc.cl
    z0le = w.s([bc.nfn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ps, NF))
    c0 = w.s([z0le], 'iftrued', '( %s -> %s = 0 )' % (ps, CT('0')))
    nf0 = w.s([cl.mem(NF, 'CC')], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (ps, NF, NF))
    lb = w.s([bc.fn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` F ) )' % (ps, NF))
    fp = w.s([bc.fn, w.inst('blpow2')], 'syl', '( %s -> F < ( 2 ^ ( bl ` F ) ) )' % ps)
    fp2 = w.s([fp, w.s([w.s([lb], 'eqcomd', '( %s -> ( bl ` F ) = %s )' % (ps, NF))], 'oveq2d', '( %s -> ( 2 ^ ( bl ` F ) ) = ( 2 ^ %s ) )' % (ps, NF))],
              'breqtrd', '( %s -> F < ( 2 ^ %s ) )' % (ps, NF))
    e1 = w.s([w.s([w.s([c0], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - 0 ) )' % (ps, NF, CT('0'), NF)), nf0], 'eqtrd', '( %s -> ( %s - %s ) = %s )' % (ps, NF, CT('0'), NF))],
             'oveq2d', '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ %s ) )' % (ps, NF, CT('0'), NF))
    e2 = w.s([w.s([e1], 'oveq2d', '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ %s ) ) )' % (ps, NF, CT('0'), NF))], 'fveq2d',
             '( %s -> %s = ( |_ ` ( F / ( 2 ^ %s ) ) ) )' % (ps, TOPX(CT('0')), NF))
    pn = w.s([closed(w, ps, '2nn', '2 e. NN'), bc.nfn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ps, NF))
    fl0 = w.s([w.s([w.s([bc.fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ps), fp2], 'jca', '( %s -> ( 0 <_ F /\\ F < ( 2 ^ %s ) ) )' % (ps, NF)),
               w.s([bc.fn], 'nn0red', '( %s -> F e. RR )' % ps), w.s([pn], 'nnrpd', '( %s -> ( 2 ^ %s ) e. RR+ )' % (ps, NF)), w.inst('fldivle') if False else w.inst('fldiv4lem1div2') if False else w.inst('divfl0')],
              'syl3anc' if False else 'syl2anc' if False else 'syl3anc', '') if False else None
    fl0 = w.s([w.s([bc.fn], 'nn0red', '( %s -> F e. RR )' % ps) if False else bc.fn, pn, w.inst('divfl0')], 'syl2anc',
              '( %s -> ( F < ( 2 ^ %s ) <-> ( |_ ` ( F / ( 2 ^ %s ) ) ) = 0 ) )' % (ps, NF, NF))
    t0 = w.s([e2, w.s([fp2, fl0], 'mpbid', '( %s -> ( |_ ` ( F / ( 2 ^ %s ) ) ) = 0 )' % (ps, NF))], 'eqtrd', '( %s -> %s = 0 )' % (ps, TOPX(CT('0'))))
    return t0, c0, nf0, fp2, pn, lb


def tmiblp():
    lab = 'tmiblp'
    PROB = TRI(CLN(LMB['A'], NPC, 'D'), CLN(LMB['L'], '( %s ` 0 )' % NBF, '( %s ` 0 )' % PV), '@')
    w = W(lab, 'The prologue of Lean\'s ` bitlen x y s s\' ` at the machine: ` pushSym s comma ; moveNum x s ; pushSym x '
               'comma ; pushNum y 0 ; load\' ( flag := false , carry := false ) ` moves the bits of ` a ` reversed onto '
               '` s ` and enters the loop invariant ` BlInv ` at 0 ( ` cmp ` kept).')
    ps = PHB
    bc = Bc(w, ps)
    cl, mk, c = bc.cl, bc.mk, bc.c
    dd = c[STKD('D')]
    xg = c[WRD('X', GAM)]
    vals = {s_: selfval(w, ps, mk, 'D', dd, s_) for s_ in K4}
    vals['K'] = (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ps, 'F', bc.fn, 'X', xg))
    S0 = Stacks(w, ps, mk, 'D', dd, bc.ne, vals)
    run = Run(w, ps, mk, S0, bc.base, c)
    nss = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NPC)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, NPC)), mk['seq']], 'sseqtrrd',
              '( %s -> %s C_ ( 2nd ` T ) )' % (ps, NPC))
    g4 = closed(w, ps, 'gamma4', "4 e. Gamma'")
    DV = lambda s_: '( D ` %s )' % s_
    g4k = lambda k: w.s([g4, mk['k'][k]['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ps, GX(k)))
    run.call('tm2fpshn', {'A': LMB['A'], 'E': LMB["A'"], 'K': 'I', 'Z': '4', 'N': NPC},
             {'4 e. %s' % GX('I'): g4k('I'), '%s C_ ( 2nd ` T )' % NPC: nss}, [('I', YX(DV('I')), wg4(w, ps, DV('I'), bc.dsg('I')))])
    # restate the stacks as UPD( UPD( D , K , VK ) , I , .. )
    VK = CC(WF, YX('X'))
    gv = w.s([bc.fn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = %s )' % (ps, WF))
    dk = w.s([c['( D ` K ) = %s' % EW('F', 'X')], w.s([gv], 'oveq1d', '( %s -> %s = %s )' % (ps, EW('F', 'X'), VK))], 'eqtrd', '( %s -> ( D ` K ) = %s )' % (ps, VK))
    u0 = upidv(w, ps, 'D', 'K', VK, dk, mk['tv'], dd, mk['k']['K']['kd'])
    D1 = UP('D', 'K', VK)
    eb = w.s([upbase(w, ps, D1, 'D', 'I', YX(DV('I')), u0)], 'eqcomd', '( %s -> %s = %s )' % (ps, UP('D', 'I', YX(DV('I'))), UP(D1, 'I', YX(DV('I')))))
    head = run.cur[:-len(' X. { %s } ) )' % run.S.D)]
    ncls = head.split(' } X. ( ', 1)[1]
    run.tri, _, run.cur, _ = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=clneq(w, ps, LMB["A'"], ncls, eb, UP('D', 'I', YX(DV('I'))), UP(D1, 'I', YX(DV('I')))))
    wfg = wib(w, ps, ENCF, bc.efw)
    vkg = wgcat(w, ps, WF, YX('X'), wfg, wg4(w, ps, 'X', xg))
    run.gam[VK] = vkg
    run.S = S0.upd('K', VK, vkg).upd('I', YX(DV('I')), wg4(w, ps, DV('I'), bc.dsg('I')))
    run.chain = [('K', VK), ('I', YX(DV('I')))]
    # moveNum x s
    mvin = w.s([], 'tmcmvin', ST_MVIN)
    HCs = ST_MVIN[2:].split(' /\\ A. r e. %s ( -. ' % NPC)[0]
    HEs = 'A. r e. %s ( -. ' % NPC + ST_MVIN[:-2].split(' /\\ A. r e. %s ( -. ' % NPC)[1]
    hc = w.s([w.s([mvin], 'simpli', HCs)], 'a1i', '( %s -> %s )' % (ps, HCs))
    he = w.s([w.s([mvin], 'simpri', HEs)], 'a1i', '( %s -> %s )' % (ps, HEs))
    wb = w.s([bc.efw, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ps, WF, BITS))
    RW = '( ( reverse ` %s ) ++ %s )' % (WF, YX(DV('I')))
    rwg = wgcat(w, ps, '( reverse ` %s )' % WF, YX(DV('I')), w.s([wfg, w.inst('revcl')], 'syl', "( %s -> ( reverse ` %s ) e. Word Gamma' )" % (ps, WF)),
                wg4(w, ps, DV('I'), bc.dsg('I')))
    ex = {HCs: hc, HEs: he, RTY('TMrdA', 'K'): mk['k']['K']['hdl']['TMrdA'], CTY(CIS): cis_ty(w, ps, mk), PTY(PBR, 'I'): pbr_ty(w, ps, mk, 'I'),
          '%s C_ %s' % (BITS, GX('K')): bitsgk(w, ps, mk, 'K'), '%s C_ %s' % (BITS, GX('I')): bitsgk(w, ps, mk, 'I'),
          '4 e. %s' % GX('K'): g4k('K'), WRD('X', GX('K')): togk7(w, ps, mk, 'X', 'K', xg),
          WRD(YX(DV('I')), GX('I')): togk7(w, ps, mk, YX(DV('I')), 'I', wg4(w, ps, DV('I'), bc.dsg('I'))),
          WRD(WF, BITS): wb, '%s C_ ( 2nd ` T )' % NPC: nss}
    run.call('tm2fmvn', {'A': LMB["A'"], 'E': LMB['A"'], 'K': 'K', 'J': 'I', 'F': 'TMrdA', 'C': CIS, 'P': PBR, 'B': BITS, 'Y': '4', 'X': 'X',
                         'H': YX(DV('I')), 'W': WF, 'N': NPC}, ex, [('K', 'X', xg), ('I', RW, rwg)], on=(S0, []))
    run.call('tm2fpshn', {'A': LMB['A"'], 'E': LMB['A0'], 'K': 'K', 'Z': '4', 'N': NPC},
             {'4 e. %s' % GX('K'): g4k('K'), '%s C_ ( 2nd ` T )' % NPC: nss}, [('K', YX('X'), wg4(w, ps, 'X', xg))])
    run.call('tm2fpshn', {'A': LMB['A0'], 'E': LMB['P1'], 'K': 'J', 'Z': '4', 'N': NPC},
             {'4 e. %s' % GX('J'): g4k('J'), '%s C_ ( 2nd ` T )' % NPC: nss}, [('J', YX(DV('J')), wg4(w, ps, DV('J'), bc.dsg('J')))])
    # the load into ( NBF ` 0 )
    t0, c0, nf0, fp2, pn, lb = top0(w, ps, bc)
    pm = '( %s /\\ r e. %s )' % (ps, NPC)
    Lr = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    rr, fl_, cm_, ca_ = np_out(w, pm, 'r', w.s([], 'simpr', '( %s -> r e. %s )' % (pm, NPC)))
    nv = load_val(w, pm, lambda t: dict(car='(/)', fl='(/)'), 'r', rr)
    NVR = '( %s ` r )' % LBL0
    f0 = w.s([nv['fields']['fl'], w.s([Lr(t0)], 'iftrued', '( %s -> %s = (/) )' % (pm, FLV('0')))], 'eqtr4d', '( %s -> ( TMfl ` %s ) = %s )' % (pm, NVR, FLV('0')))
    cmq = w.s([nv['fields']['cmp'], cm_], 'eqtrd', '( %s -> ( TMcmp ` %s ) = Q )' % (pm, NVR))
    nlt0 = w.s([w.s([Lr(w.s([bc.nfn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ps, NF))), w.s([Lr(cl.mem(NF, 'RR')), closed(w, pm, '0re', '0 e. RR')], 'lenltd',
                                                                                        '( %s -> ( 0 <_ %s <-> -. %s < 0 ) )' % (pm, NF, NF))], 'mpbid',
                    '( %s -> -. %s < 0 )' % (pm, NF))], 'iffalsed', '( %s -> %s = (/) )' % (pm, CRV('0')))
    ca0 = w.s([nv['fields']['car'], nlt0], 'eqtr4d', '( %s -> ( TMcar ` %s ) = %s )' % (pm, NVR, CRV('0')))
    co = w.s([f0, cmq, ca0], '3jca', '( %s -> %s )' % (pm, NBC(NVR, '0')))
    z0 = closed(w, pm, '0nn0', '0 e. NN0')
    in0 = fam_pack(w, pm, NBC, '0', z0, NVR, nv['mem'], co)
    hl = w.s([in0], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. ( %s ` 0 ) )' % (ps, NPC, LBL0, NBF))
    z0p = closed(w, ps, '0nn0', '0 e. NN0')
    S = run.S
    exl = {LTY(LBL0): ldty(w, ps, mk, lambda t: dict(car='(/)', fl='(/)')), '%s C_ ( 2nd ` T )' % NPC: nss,
           '( %s ` 0 ) C_ ( 2nd ` T )' % NBF: bc.famss('0', z0p), 'A. r e. %s ( %s ` r ) e. ( %s ` 0 )' % (NPC, LBL0, NBF): hl}
    run.call('tm2flg', {'A': LMB['P1'], 'E': LMB['L'], 'F': LBL0, 'N': NPC, "N'": '( %s ` 0 )' % NBF}, exl, [])
    cur, out = run.normalize(K4)
    RWI = RW
    assert out == [('K', YX('X')), ('J', YX(DV('J'))), ('I', RW)], out
    DQ = chain_text('D', out)
    # reverse ( inclBool o. ENCF ) = ( inclBool o. ( reverse ` ENCF ) )
    rv = w.s([bc.efw, closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'"), w.inst('revco')], 'syl2anc',
             '( %s -> ( inclBool o. ( reverse ` %s ) ) = ( reverse ` %s ) )' % (ps, ENCF, WF))
    r1, x1 = w.rewrite(DQ, {'( reverse ` %s )' % WF: ('( inclBool o. ( reverse ` %s ) )' % ENCF, w.s([rv], 'eqcomd',
                                                                                                   '( %s -> ( reverse ` %s ) = ( inclBool o. ( reverse ` %s ) ) )' % (ps, WF, ENCF)))}, ps)
    assert x1 == PB0, x1
    # PBL( 0 ) = PB0
    ctz = w.s([t0], 'id', '') if False else None
    b0 = w.s([w.s([w.s([w.s([bc.topn(CT('0'), *bc.ct('0', z0p))[0]], 'nn0zd', '( %s -> %s e. ZZ )' % (ps, TOPX(CT('0')))), w.inst('bwrd0')], 'syl',
                        '( %s -> ( %s bwrd 0 ) = (/) )' % (ps, TOPX(CT('0'))))], 'id', '') if False else None], 'id', '') if False else None
    tz = w.s([bc.topn(CT('0'), *bc.ct('0', z0p))[0]], 'nn0zd', '( %s -> %s e. ZZ )' % (ps, TOPX(CT('0'))))
    bw0 = w.s([w.s([c0], 'oveq2d', '( %s -> ( %s bwrd %s ) = ( %s bwrd 0 ) )' % (ps, TOPX(CT('0')), CT('0'), TOPX(CT('0')))),
               w.s([tz, w.inst('bwrd0')], 'syl', '( %s -> ( %s bwrd 0 ) = (/) )' % (ps, TOPX(CT('0'))))], 'eqtrd',
              '( %s -> ( %s bwrd %s ) = (/) )' % (ps, TOPX(CT('0')), CT('0')))
    ib0 = w.s([w.s([bw0], 'coeq2d', '( %s -> ( inclBool o. ( %s bwrd %s ) ) = ( inclBool o. (/) ) )' % (ps, TOPX(CT('0')), CT('0'))),
               closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd', '( %s -> ( inclBool o. ( %s bwrd %s ) ) = (/) )' % (ps, TOPX(CT('0')), CT('0')))
    xx0 = w.s([w.s([ib0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, XWV('0'), YX('X'))), w.s([wg4(w, ps, 'X', xg), w.inst('ccatlid')], 'syl',
                                                                                              '( %s -> ( (/) ++ %s ) = %s )' % (ps, YX('X'), YX('X')))],
              'eqtrd', '( %s -> %s = %s )' % (ps, XWV('0'), YX('X')))
    bl0 = w.s([w.s([t0], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` 0 ) )' % (ps, TOPX(CT('0')))), closed(w, ps, 'bl0', '( bl ` 0 ) = 0')], 'eqtrd',
              '( %s -> ( bl ` %s ) = 0 )' % (ps, TOPX(CT('0'))))
    e0 = w.s([w.s([closed(w, ps, '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ps),
              w.s([w.s([closed(w, ps, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ps),
                   closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')], 'eqtrd', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = (/) )' % ps)], 'eqtrd',
             '( %s -> ( encNatGam ` 0 ) = (/) )' % ps)
    yy0 = w.s([w.s([w.s([w.s([bl0], 'fveq2d', '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( encNatGam ` 0 ) )' % (ps, TOPX(CT('0')))), e0], 'eqtrd',
                        '( %s -> ( encNatGam ` ( bl ` %s ) ) = (/) )' % (ps, TOPX(CT('0'))))], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, YWV('0'), YX(DV('J')))),
               w.s([wg4(w, ps, DV('J'), bc.dsg('J')), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, YX(DV('J')), YX(DV('J'))))], 'eqtrd',
              '( %s -> %s = %s )' % (ps, YWV('0'), YX(DV('J'))))
    z0le = w.s([bc.nfn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ps, NF))
    SI0 = '( ( inclBool o. ( reverse ` %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % LOWV('0')
    s1 = w.s([z0le], 'iftrued', '( %s -> %s = %s )' % (ps, SWV('0'), SI0))
    md = w.s([w.s([w.s([bc.fn], 'nn0red', '( %s -> F e. RR )' % ps), w.s([pn], 'nnrpd', '( %s -> ( 2 ^ %s ) e. RR+ )' % (ps, NF))], 'jca',
                  '( %s -> ( F e. RR /\\ ( 2 ^ %s ) e. RR+ ) )' % (ps, NF)),
              w.s([w.s([bc.fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ps), fp2], 'jca', '( %s -> ( 0 <_ F /\\ F < ( 2 ^ %s ) ) )' % (ps, NF)), w.inst('modid')],
             'syl2anc', '( %s -> ( F mod ( 2 ^ %s ) ) = F )' % (ps, NF))
    lw0 = w.s([w.s([w.s([w.s([nf0], 'oveq2d', '( %s -> ( 2 ^ ( %s - 0 ) ) = ( 2 ^ %s ) )' % (ps, NF, NF))], 'oveq2d',
                        '( %s -> ( F mod ( 2 ^ ( %s - 0 ) ) ) = ( F mod ( 2 ^ %s ) ) )' % (ps, NF, NF)), md], 'eqtrd',
                   '( %s -> ( F mod ( 2 ^ ( %s - 0 ) ) ) = F )' % (ps, NF)), nf0], 'oveq12d', '( %s -> %s = ( F bwrd %s ) )' % (ps, LOWV('0'), NF))
    eb2 = w.s([w.s([bc.fn, w.inst('encnatbwrd')], 'syl', '( %s -> %s = ( F bwrd ( bl ` F ) ) )' % (ps, ENCF)),
               w.s([w.s([lb], 'eqcomd', '( %s -> ( bl ` F ) = %s )' % (ps, NF))], 'oveq2d', '( %s -> ( F bwrd ( bl ` F ) ) = ( F bwrd %s ) )' % (ps, NF))],
              'eqtrd', '( %s -> %s = ( F bwrd %s ) )' % (ps, ENCF, NF))
    lwe = w.s([lw0, eb2], 'eqtr4d', '( %s -> %s = %s )' % (ps, LOWV('0'), ENCF))
    ss0 = w.s([s1, w.s([w.s([w.s([lwe], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` %s ) )' % (ps, LOWV('0'), ENCF))], 'coeq2d',
                            '( %s -> ( inclBool o. ( reverse ` %s ) ) = ( inclBool o. ( reverse ` %s ) ) )' % (ps, LOWV('0'), ENCF))], 'oveq1d',
                       '( %s -> %s = %s )' % (ps, SI0, CC('( inclBool o. ( reverse ` %s ) )' % ENCF, YX(DV('I')))))], 'eqtrd',
              '( %s -> %s = %s )' % (ps, SWV('0'), CC('( inclBool o. ( reverse ` %s ) )' % ENCF, YX(DV('I')))))
    r2, x2 = w.rewrite(PBL('0'), {XWV('0'): (YX('X'), xx0), YWV('0'): (YX(DV('J')), yy0), SWV('0'): (CC('( inclBool o. ( reverse ` %s ) )' % ENCF, YX(DV('I'))), ss0)}, ps)
    assert x2 == PB0, x2
    pv0, _ = bc.pv('0', z0p)
    p0 = w.s([pv0, r2], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ps, PV, PB0))
    deq = w.s([r1, p0], 'eqtr4d', '( %s -> %s = ( %s ` 0 ) )' % (ps, DQ, PV))
    NC0 = '( %s ` 0 )' % NBF
    t2, C2, D2, n2 = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=clneq(w, ps, LMB['L'], NC0, deq, DQ, '( %s ` 0 )' % PV), qed=True)
    return w.run(), n2


T0_ = TOPX('I')
T1_ = TOPX('( I + 1 )')
MI = '( %s - ( I + 1 ) )' % NF
BMI = 'if ( %s e. ( bits ` F ) , 1 , 0 )' % MI
BOI = 'if ( %s e. ( bits ` F ) , 1o , (/) )' % MI
IT_A = '%s = ( ( 2 x. %s ) + %s )' % (T1_, T0_, BMI)
IT_B = '( ( if ( %s = 0 , (/) , 1o ) = 1o \\/ %s = 1o ) <-> -. %s = 0 )' % (T0_, BOI, T1_)
IT_C = '( -. %s = 0 -> ( bl ` %s ) = ( ( bl ` %s ) + 1 ) )' % (T1_, T1_, T0_)
IT_D = '( %s = 0 -> ( bl ` %s ) = ( bl ` %s ) )' % (T1_, T1_, T0_)
ST_IT = '( ( F e. NN0 /\\ I e. NN0 /\\ I < %s ) -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (NF, IT_A, IT_B, IT_C, IT_D)


def tmiblit():
    lab = 'tmiblit'
    ph = '( F e. NN0 /\\ I e. NN0 /\\ I < %s )' % NF
    w = W(lab, 'One iteration of ` bitlen ` \'s scan on numbers (Lean ` BlInv ` , ` blBody_runs ` ): the number on ` x ` '
               'doubles and gains the next bit of ` F ` , the flag ` flag || bit ` is ` [ top =/= 0 ] ` , and the bit '
               'length counts up exactly when the top is nonzero.')
    fn = w.s([], 'simp1', '( %s -> F e. NN0 )' % ph)
    inn = w.s([], 'simp2', '( %s -> I e. NN0 )' % ph)
    ilt = w.s([], 'simp3', '( %s -> I < %s )' % (ph, NF))
    efw = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, ENCF))
    nfn = w.s([efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NF))
    cl = Closure(w, ph, {'F': ('NN0', fn), 'I': ('NN0', inn), NF: ('NN0', nfn)})
    cl.atom(NF)
    i1le = w.s([ilt, w.s([cl.mem('I', 'ZZ'), cl.mem(NF, 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( I < %s <-> ( I + 1 ) <_ %s ) )' % (ph, NF, NF))],
               'mpbid', '( %s -> ( I + 1 ) <_ %s )' % (ph, NF))
    mn = w.s([w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( I + 1 ) e. NN0 )' % ph), nfn, i1le, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, MI))
    top = w.s([fn, mn, w.inst('tmibltop')], 'syl2anc', '( %s -> %s = ( ( 2 x. ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) ) + %s ) )' % (ph, T1_, MI, BMI))
    mm1 = lineq(w, ph, '( %s + 1 )' % MI, '( %s - I )' % NF, closure=cl)
    t0e = w.s([w.s([w.s([mm1], 'oveq2d', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( 2 ^ ( %s - I ) ) )' % (ph, MI, NF))], 'oveq2d',
                   '( %s -> ( F / ( 2 ^ ( %s + 1 ) ) ) = ( F / ( 2 ^ ( %s - I ) ) ) )' % (ph, MI, NF))], 'fveq2d',
              '( %s -> ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) = %s )' % (ph, MI, T0_))
    a = w.s([top, w.s([w.s([t0e], 'oveq2d', '( %s -> ( 2 x. ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) ) = ( 2 x. %s ) )' % (ph, MI, T0_))], 'oveq1d',
                      '( %s -> ( ( 2 x. ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) ) + %s ) = ( ( 2 x. %s ) + %s ) )' % (ph, MI, BMI, T0_, BMI))], 'eqtrd',
            '( %s -> %s )' % (ph, IT_A))
    # T0 e. NN0 , BMI e. { 0 , 1 }
    ilen = w.s([ilt], 'ltled', '( %s -> I <_ %s )' % (ph, NF))
    dn = w.s([inn, nfn, ilen, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( %s - I ) e. NN0 )' % (ph, NF))
    t0n = w.s([fn, w.s([closed(w, ph, '2nn', '2 e. NN'), dn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ ( %s - I ) ) e. NN )' % (ph, NF)), w.inst('fldivnn0')],
              'syl2anc', '( %s -> %s e. NN0 )' % (ph, T0_))
    bmn = w.s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ph, BMI))
    cl.leaf(T0_, 'NN0', t0n); cl.leaf(BMI, 'NN0', bmn)
    t1nn = w.s([fn, w.s([closed(w, ph, '2nn', '2 e. NN'), mn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, MI)), w.inst('fldivnn0')],
               'syl2anc', '( %s -> %s e. NN0 )' % (ph, T1_))
    cl.leaf(T1_, 'NN0', t1nn)
    bm1 = w.s([], 'ifeqor', '( %s = 1 \\/ %s = 0 )' % (BMI, BMI))
    bor = w.s([w.s([bm1, w.inst('pm1.4')], 'ax-mp', '( %s = 0 \\/ %s = 1 )' % (BMI, BMI))], 'a1i', '( %s -> ( %s = 0 \\/ %s = 1 ) )' % (ph, BMI, BMI))
    # case analysis on the bit and on T0
    B1 = '( %s /\\ %s e. ( bits ` F ) )' % (ph, MI)
    B0 = '( %s /\\ -. %s e. ( bits ` F ) )' % (ph, MI)
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (B1, concl(w, ph, st)))
    L0 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (B0, concl(w, ph, st)))
    bm_1 = w.s([w.s([], 'simpr', '( %s -> %s e. ( bits ` F ) )' % (B1, MI))], 'iftrued', '( %s -> %s = 1 )' % (B1, BMI))
    bo_1 = w.s([w.s([], 'simpr', '( %s -> %s e. ( bits ` F ) )' % (B1, MI))], 'iftrued', '( %s -> %s = 1o )' % (B1, BOI))
    bm_0 = w.s([w.s([], 'simpr', '( %s -> -. %s e. ( bits ` F ) )' % (B0, MI))], 'iffalsed', '( %s -> %s = 0 )' % (B0, BMI))
    bo_0 = w.s([w.s([], 'simpr', '( %s -> -. %s e. ( bits ` F ) )' % (B0, MI))], 'iffalsed', '( %s -> %s = (/) )' % (B0, BOI))
    cl1 = Closure(w, B1, {T0_: ('NN0', L1(t0n)), BMI: ('NN0', L1(bmn)), T1_: ('NN0', L1(t1nn))})
    cl0 = Closure(w, B0, {T0_: ('NN0', L0(t0n)), BMI: ('NN0', L0(bmn)), T1_: ('NN0', L0(t1nn))})
    # bit 1 : T1 =/= 0 , the or holds
    t1p = linarith(w, B1, [L1(a), bm_1, cl1.ge0(T0_)], '0 < %s' % T1_, closure=cl1)
    t1n = w.s([w.s([t1p], 'gt0ne0d', '( %s -> %s =/= 0 )' % (B1, T1_))], 'neneqd', '( %s -> -. %s = 0 )' % (B1, T1_))
    or1 = w.s([bo_1], 'olcd', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o \\/ %s = 1o ) )' % (B1, T0_, BOI))
    b1 = w.s([or1, t1n], '2thd', '( %s -> %s )' % (B1, IT_B))
    # bit 0 : T1 = 2 T0 , the or is T0 =/= 0
    t1e = linarith(w, B0, [L0(a), bm_0], '%s <_ ( 2 x. %s )' % (T1_, T0_), closure=cl0) if False else None
    ne1 = w.s([w.s([closed(w, B0, '1n0', '1o =/= (/)')], 'necomd', '( %s -> (/) =/= 1o )' % B0)], 'neneqd', '( %s -> -. (/) = 1o )' % B0)
    bon = w.s([w.s([bo_0], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (B0, BOI)), ne1], 'mtbird', '( %s -> -. %s = 1o )' % (B0, BOI))
    orb = w.s([bon], 'biorfd' if False else 'biorf', '') if False else None
    orb = w.s([bon, w.inst('biorf')], 'syl', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o <-> ( %s = 1o \\/ if ( %s = 0 , (/) , 1o ) = 1o ) ) )' % (B0, T0_, BOI, T0_))
    orc = w.s([orb, w.s([], 'orcom', '( ( %s = 1o \\/ if ( %s = 0 , (/) , 1o ) = 1o ) <-> ( if ( %s = 0 , (/) , 1o ) = 1o \\/ %s = 1o ) )' % (BOI, T0_, T0_, BOI))],
              'bitrdi', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o <-> ( if ( %s = 0 , (/) , 1o ) = 1o \\/ %s = 1o ) ) )' % (B0, T0_, T0_, BOI))
    # if ( T0 = 0 , (/) , 1o ) = 1o <-> -. T0 = 0
    C1 = '( %s /\\ %s = 0 )' % (B0, T0_)
    C2 = '( %s /\\ -. %s = 0 )' % (B0, T0_)
    ifz = w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (C1, T0_))], 'iftrued', '( %s -> if ( %s = 0 , (/) , 1o ) = (/) )' % (C1, T0_))
    lf1 = w.s([w.s([ifz], 'eqeq1d', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o <-> (/) = 1o ) )' % (C1, T0_)),
               w.s([ne1], 'adantr', '( %s -> -. (/) = 1o )' % C1)], 'mtbird', '( %s -> -. if ( %s = 0 , (/) , 1o ) = 1o )' % (C1, T0_))
    cc1 = Closure(w, C1, {T0_: ('NN0', w.s([L0(t0n)], 'adantr', '( %s -> %s e. NN0 )' % (C1, T0_))), T1_: ('NN0', w.s([L0(t1nn)], 'adantr', '( %s -> %s e. NN0 )' % (C1, T1_))), BMI: ('NN0', w.s([L0(bmn)], 'adantr', '( %s -> %s e. NN0 )' % (C1, BMI)))})
    t1z = lineq(w, C1, T1_, '0', hyps=[w.s([L0(a)], 'adantr', '( %s -> %s )' % (C1, IT_A)), w.s([bm_0], 'adantr', '( %s -> %s = 0 )' % (C1, BMI)),
                                        w.s([], 'simpr', '( %s -> %s = 0 )' % (C1, T0_))], closure=cc1, atoms=[T1_, T0_, BMI])
    r1_ = w.s([lf1, w.s([t1z], 'notnotd', '( %s -> -. -. %s = 0 )' % (C1, T1_))], '2falsed', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o <-> -. %s = 0 ) )' % (C1, T0_, T1_))
    ifn = w.s([w.s([], 'simpr', '( %s -> -. %s = 0 )' % (C2, T0_))], 'iffalsed', '( %s -> if ( %s = 0 , (/) , 1o ) = 1o )' % (C2, T0_))
    cc2 = Closure(w, C2, {T0_: ('NN0', w.s([L0(t0n)], 'adantr', '( %s -> %s e. NN0 )' % (C2, T0_))), T1_: ('NN0', w.s([L0(t1nn)], 'adantr', '( %s -> %s e. NN0 )' % (C2, T1_))), BMI: ('NN0', w.s([L0(bmn)], 'adantr', '( %s -> %s e. NN0 )' % (C2, BMI)))})
    t0p = w.s([w.s([cc2.mem(T0_, 'NN0'), w.s([w.s([], 'simpr', '( %s -> -. %s = 0 )' % (C2, T0_))], 'neqned', '( %s -> %s =/= 0 )' % (C2, T0_)), w.inst('elnnne0')],
                   'sylanbrc', '( %s -> %s e. NN )' % (C2, T0_))], 'nngt0d', '( %s -> 0 < %s )' % (C2, T0_))
    t1p2 = linarith(w, C2, [w.s([L0(a)], 'adantr', '( %s -> %s )' % (C2, IT_A)), w.s([bm_0], 'adantr', '( %s -> %s = 0 )' % (C2, BMI)), t0p], '0 < %s' % T1_,
                    closure=cc2, atoms=[T1_, T0_, BMI])
    t1n2 = w.s([w.s([t1p2], 'gt0ne0d', '( %s -> %s =/= 0 )' % (C2, T1_))], 'neneqd', '( %s -> -. %s = 0 )' % (C2, T1_))
    r2_ = w.s([ifn, t1n2], '2thd', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o <-> -. %s = 0 ) )' % (C2, T0_, T1_))
    rr = w.s([r1_, r2_], 'pm2.61dan', '( %s -> ( if ( %s = 0 , (/) , 1o ) = 1o <-> -. %s = 0 ) )' % (B0, T0_, T1_))
    b0_ = w.s([orc, rr], 'bitr3d', '( %s -> %s )' % (B0, IT_B))
    bb = w.s([b1, b0_], 'pm2.61dan', '( %s -> %s )' % (ph, IT_B))
    # (c) the bit length step
    PC = '( %s /\\ -. %s = 0 )' % (ph, T1_)
    LP = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (PC, concl(w, ph, st)))
    xne = w.s([w.s([w.s([], 'simpr', '( %s -> -. %s = 0 )' % (PC, T1_))], 'neqned', '( %s -> %s =/= 0 )' % (PC, T1_)), LP(a)], 'neeq1d' if False else 'eqnetrrd',
              '( %s -> ( ( 2 x. %s ) + %s ) =/= 0 )' % (PC, T0_, BMI))
    st = w.s([w.s([LP(t0n), LP(bor), xne], '3jca', '( %s -> ( %s e. NN0 /\\ ( %s = 0 \\/ %s = 1 ) /\\ ( ( 2 x. %s ) + %s ) =/= 0 ) )' % (PC, T0_, BMI, BMI, T0_, BMI)),
              w.inst('tmiblst')], 'syl', '( %s -> ( bl ` ( ( 2 x. %s ) + %s ) ) = ( ( bl ` %s ) + 1 ) )' % (PC, T0_, BMI, T0_))
    cst = w.s([w.s([LP(a)], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` ( ( 2 x. %s ) + %s ) ) )' % (PC, T1_, T0_, BMI)), st], 'eqtrd',
              '( %s -> ( bl ` %s ) = ( ( bl ` %s ) + 1 ) )' % (PC, T1_, T0_))
    cc = w.s([cst], 'ex', '( %s -> %s )' % (ph, IT_C))
    # (d)
    PD = '( %s /\\ %s = 0 )' % (ph, T1_)
    LD = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (PD, concl(w, ph, st)))
    cd_ = Closure(w, PD, {T0_: ('NN0', LD(t0n)), BMI: ('NN0', LD(bmn)), T1_: ('NN0', LD(t1nn))})
    t0z = lineq(w, PD, T0_, '0', hyps=[LD(a), w.s([], 'simpr', '( %s -> %s = 0 )' % (PD, T1_)), cd_.ge0(T0_), cd_.ge0(BMI)], closure=cd_, atoms=[T1_, T0_, BMI])
    dd_ = w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (PD, T1_)), t0z], 'eqtr4d', '( %s -> %s = %s )' % (PD, T1_, T0_))], 'fveq2d',
              '( %s -> ( bl ` %s ) = ( bl ` %s ) )' % (PD, T1_, T0_))
    d_ = w.s([dd_], 'ex', '( %s -> %s )' % (ph, IT_D))
    w.qed([w.s([a, bb], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, IT_A, IT_B)), w.s([cc, d_], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, IT_C, IT_D))], 'jca', ST_IT)
    return w.run()


def ldty2(w, ph, mk, kw_of):
    """( ph -> LSET e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) ) , if-components with 1o / (/) branches"""
    pu = 'u e. TMSt'
    rr = w.s([], 'id', '( %s -> u e. TMSt )' % pu)
    cl = st_comps(w, pu, 'u', rr)
    kw = kw_of('u')
    comps = [kw.get(f, FLD(f, 'u')) for f in ORDER]
    c1 = lambda v: closed(w, pu, '1oel2o' if v == '1o' else '0el2o', '%s e. 2o' % v)
    cls = []
    for f, comp in zip(ORDER, comps):
        if f not in kw:
            cls.append(cl[f])
        elif comp in ('(/)', '1o'):
            cls.append(c1(comp))
        else:
            tk = comp.split()
            cls.append(w.s([c1(tk[-4]), c1(tk[-2])], 'ifcld', '( %s -> %s e. 2o )' % (pu, comp)))
    mem, vals = tuple_facts(w, pu, comps, cls)
    X_of = lambda t: SETF(t, **kw_of(t))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    lt = lamty(w, ph, mk, LSET(**kw_of('u')), X_of, 'TMSt', sv, mem)
    e = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    e2 = w.s([e], 'oveq1d', '( %s -> ( TMSt ^m ( 2nd ` T ) ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    return w.s([lt, e2], 'eleqtrd', '( %s -> %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % (ph, LSET(**kw_of('u'))))


PSIB = '( %s /\\ i e. ( 0 ..^ ( %s + 1 ) ) )' % (PHB, NF)
PSIL = '( %s /\\ i < %s )' % (PSIB, NF)
PSIE = '( %s /\\ -. i < %s )' % (PSIB, NF)
I1 = '( i + 1 )'
T0i, T1i = TOPX('i'), TOPX(I1)
Mi = '( %s - %s )' % (NF, I1)
BOi = 'if ( %s e. ( bits ` F ) , 1o , (/) )' % Mi
ZL = '<. 1 , %s >.' % BOi
FL1 = 'if ( %s = 0 , (/) , 1o )' % T1i
def OCLC(h):
    return '( ( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = (/) ) /\\ ( TMda ` %s ) = (/) )' % (h, FL1, h, h, h)
OCL = '{ h e. TMSt | %s }' % OCLC('h')
PSX = UP(UP(UP('D', 'K', XWV(I1)), 'J', YWV('i')), 'I', SWV(I1))
SREST = '( ( inclBool o. ( reverse ` %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % LOWV(I1)
XK = '( ( inclBool o. ( %s bwrd i ) ) ++ ( <" 4 "> ++ X ) )' % T0i
CONCL_S = TRI(CLN(LMB['B'], '( %s ` i )' % NBF, '( %s ` i )' % PV), CLN(LMB['Q2'], OCL, PSX), '( 1 + 1 )')
LCQ = LOAD(LCAR1, GT(LMB['Q']))


class It:
    """iteration facts under ps = PSIL-like antecedents (i e. ( 0 ..^ ( NF + 1 ) ) at simplr position)"""
    def __init__(self, w, ps, lift, ii_ref):
        self.w, self.ps = w, ps
        self.bc = bc = Bc(w, ps, lift=lift)
        cl = bc.cl
        ii = w.s([], ii_ref, '( %s -> i e. ( 0 ..^ ( %s + 1 ) ) )' % (ps, NF))
        self.inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
        ilt1 = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < ( %s + 1 ) )' % (ps, NF))
        cl.leaf('i', 'NN0', self.inn)
        self.ile = w.s([ilt1, w.s([cl.mem('i', 'ZZ'), cl.mem(NF, 'ZZ'), w.inst('zleltp1')], 'syl2anc', '( %s -> ( i <_ %s <-> i < ( %s + 1 ) ) )' % (ps, NF, NF))],
                       'mpbird', '( %s -> i <_ %s )' % (ps, NF))
        self.i1n = w.s([self.inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
        self.cti = w.s([self.ile], 'iftrued', '( %s -> %s = i )' % (ps, CT('i')))


def tmibls():
    lab = 'tmibls'
    ps = PSIL
    C = '( %s -> %s )' % (ps, CONCL_S)
    w = W(lab, 'The scan of one bit in Lean\'s ` bitlen ` loop at the machine ( ` blBody_runs ` , the bit case): '
               '` blScan s x ` pops the next bit of ` a ` from ` s ` , pushes it on ` x ` and sets ` flag := flag || bit ` , '
               'and the test ` da ` fails.')
    it = It(w, ps, 'simpll', 'simplr')
    bc = it.bc
    cl, mk, c = bc.cl, bc.mk, bc.c
    inn, ile, i1n = it.inn, it.ile, it.i1n
    ilt = w.s([], 'simpr', '( %s -> i < %s )' % (ps, NF))
    i1le = w.s([ilt, w.s([cl.mem('i', 'ZZ'), cl.mem(NF, 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < %s <-> %s <_ %s ) )' % (ps, NF, I1, NF))],
               'mpbid', '( %s -> %s <_ %s )' % (ps, I1, NF))
    ct1 = w.s([i1le], 'iftrued', '( %s -> %s = %s )' % (ps, CT(I1), I1))
    mn = w.s([i1n, bc.nfn, i1le, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ps, Mi))
    mm1 = lineq(w, ps, '( %s + 1 )' % Mi, '( %s - i )' % NF, closure=cl)
    itf = w.s([w.s([bc.fn, inn, ilt], '3jca', '( %s -> ( F e. NN0 /\\ i e. NN0 /\\ i < %s ) )' % (ps, NF)), w.inst('tmiblit')], 'syl',
              '( %s -> %s )' % (ps, tsub_text(ST_IT, {'I': 'i'}).split(' -> ', 1)[1][:-2]))
    itp = parts(w, ps, itf, parse_conj(tsub_text(ST_IT, {'I': 'i'}).split(' -> ', 1)[1][:-2]))
    IB = tsub_text(IT_B, {'I': 'i'})
    mem, SP = bc.pvals('i', inn)
    PT = "( %s ` i )" % PV
    DV = lambda s_: '( D ` %s )' % s_
    # the scan word : ( PT ` I ) = ( <" ZL "> ++ SREST )
    bo2 = w.s([closed(w, ps, '1oel2o', '1o e. 2o'), closed(w, ps, '0el2o', '(/) e. 2o')], 'ifcld', '( %s -> %s e. 2o )' % (ps, BOi))
    SI_i = '( ( inclBool o. ( reverse ` %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % LOWV('i')
    s1 = w.s([ile], 'iftrued', '( %s -> %s = %s )' % (ps, SWV('i'), SI_i))
    LM1 = '( ( F mod ( 2 ^ ( %s + 1 ) ) ) bwrd ( %s + 1 ) )' % (Mi, Mi)
    lw1 = w.s([w.s([w.s([w.s([mm1], 'eqcomd', '( %s -> ( %s - i ) = ( %s + 1 ) )' % (ps, NF, Mi))], 'oveq2d',
                        '( %s -> ( 2 ^ ( %s - i ) ) = ( 2 ^ ( %s + 1 ) ) )' % (ps, NF, Mi))], 'oveq2d',
                   '( %s -> ( F mod ( 2 ^ ( %s - i ) ) ) = ( F mod ( 2 ^ ( %s + 1 ) ) ) )' % (ps, NF, Mi)),
               w.s([mm1], 'eqcomd', '( %s -> ( %s - i ) = ( %s + 1 ) )' % (ps, NF, Mi))], 'oveq12d', '( %s -> %s = %s )' % (ps, LOWV('i'), LM1))
    w1 = w.s([bc.fn, mn, w.inst('tmiblw1')], 'syl2anc', '( %s -> ( reverse ` %s ) = ( <" %s "> ++ ( reverse ` %s ) ) )' % (ps, LM1, BOi, LOWV(I1)))
    rw1 = w.s([w.s([lw1], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` %s ) )' % (ps, LOWV('i'), LM1)), w1], 'eqtrd',
              '( %s -> ( reverse ` %s ) = ( <" %s "> ++ ( reverse ` %s ) ) )' % (ps, LOWV('i'), BOi, LOWV(I1)))
    RL1 = '( reverse ` %s )' % LOWV(I1)
    p1n = w.s([closed(w, ps, '2nn', '2 e. NN'), mn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ps, Mi))
    mdz = w.s([w.s([bc.fn], 'nn0zd', '( %s -> F e. ZZ )' % ps), p1n, w.inst('zmodcl')], 'syl2anc', '( %s -> ( F mod ( 2 ^ %s ) ) e. NN0 )' % (ps, Mi))
    lw = w.s([w.s([mdz], 'nn0zd', '( %s -> ( F mod ( 2 ^ %s ) ) e. ZZ )' % (ps, Mi)), mn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, LOWV(I1)))
    rlw = w.s([lw, w.inst('revcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, RL1))
    ff = closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'")
    s1w = w.s([bo2], 's1cld', '( %s -> <" %s "> e. Word 2o )' % (ps, BOi))
    cc = w.s([s1w, rlw, ff, w.inst('ccatco')], 'syl3anc', '( %s -> ( inclBool o. ( <" %s "> ++ %s ) ) = ( ( inclBool o. <" %s "> ) ++ ( inclBool o. %s ) ) )'
             % (ps, BOi, RL1, BOi, RL1))
    sc = w.s([w.s([bo2, ff, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" %s "> ) = <" ( inclBool ` %s ) "> )' % (ps, BOi, BOi)),
              w.s([w.s([bo2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` %s ) = %s )' % (ps, BOi, ZL))], 's1eqd',
                  '( %s -> <" ( inclBool ` %s ) "> = <" %s "> )' % (ps, BOi, ZL))], 'eqtrd', '( %s -> ( inclBool o. <" %s "> ) = <" %s "> )' % (ps, BOi, ZL))
    ib1 = w.s([w.s([w.s([rw1], 'coeq2d', '( %s -> ( inclBool o. ( reverse ` %s ) ) = ( inclBool o. ( <" %s "> ++ %s ) ) )' % (ps, LOWV('i'), BOi, RL1)), cc], 'eqtrd',
                   '( %s -> ( inclBool o. ( reverse ` %s ) ) = ( ( inclBool o. <" %s "> ) ++ ( inclBool o. %s ) ) )' % (ps, LOWV('i'), BOi, RL1)),
               w.s([sc], 'oveq1d', '( %s -> ( ( inclBool o. <" %s "> ) ++ ( inclBool o. %s ) ) = ( <" %s "> ++ ( inclBool o. %s ) ) )' % (ps, BOi, RL1, ZL, RL1))],
              'eqtrd', '( %s -> ( inclBool o. ( reverse ` %s ) ) = ( <" %s "> ++ ( inclBool o. %s ) ) )' % (ps, LOWV('i'), ZL, RL1))
    zlg = w.s([w.s([bo2, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, ZL))], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, ZL))
    irl = wib(w, ps, RL1, rlw)
    y4i = wg4(w, ps, DV('I'), bc.dsg('I'))
    ca = w.s([zlg, irl, y4i, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) = ( <" %s "> ++ %s ) )'
             % (ps, ZL, RL1, YX(DV('I')), ZL, SREST))
    sI = w.s([w.s([s1, w.s([ib1], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) )' % (ps, SI_i, ZL, RL1, YX(DV('I'))))], 'eqtrd',
                  '( %s -> %s = ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) )' % (ps, SWV('i'), ZL, RL1, YX(DV('I')))), ca], 'eqtrd',
             '( %s -> %s = ( <" %s "> ++ %s ) )' % (ps, SWV('i'), ZL, SREST))
    srg = wgcat(w, ps, '( inclBool o. %s )' % RL1, YX(DV('I')), irl, y4i)
    # the x word: XWV( i ) = XK
    xk = w.s([w.s([w.s([w.s([it.cti], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - i ) )' % (ps, NF, CT('i'), NF))], 'oveq2d',
                        '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - i ) ) )' % (ps, NF, CT('i'), NF))], 'oveq2d',
                   '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - i ) ) ) )' % (ps, NF, CT('i'), NF))], 'fveq2d',
              '( %s -> %s = %s )' % (ps, TOPX(CT('i')), T0i))
    xk2 = w.s([xk, it.cti], 'oveq12d', '( %s -> ( %s bwrd %s ) = ( %s bwrd i ) )' % (ps, TOPX(CT('i')), CT('i'), T0i))
    xke = w.s([w.s([xk2], 'coeq2d', '( %s -> ( inclBool o. ( %s bwrd %s ) ) = ( inclBool o. ( %s bwrd i ) ) )' % (ps, TOPX(CT('i')), CT('i'), T0i))], 'oveq1d',
              '( %s -> %s = %s )' % (ps, XWV('i'), XK))
    vals = dict(SP.vals)
    vals['I'] = (('<" %s "> ++ %s' % (ZL, SREST)).join(['( ', ' )']), w.s([SP.vals['I'][1], sI], 'eqtrd', '( %s -> ( %s ` I ) = ( <" %s "> ++ %s ) )' % (ps, PT, ZL, SREST)),
                 wgcat(w, ps, '<" %s ">' % ZL, SREST, zlg, srg))
    vals['K'] = (XK, w.s([SP.vals['K'][1], xke], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, PT, XK)),
                 w.s([xke, SP.vals['K'][2]], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ps, XK)))
    SPs = Stacks(w, ps, mk, PT, mem, bc.ne, vals)
    run = Run(w, ps, mk, SPs, bc.base, c)
    # the interface of blScan at ( NBF ` i )
    NI = '( %s ` i )' % NBF
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NBC, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    zb = w.s([w.s([closed(w, pm, '1ex', '1 e. _V'), w.inst('snidg')], 'syl', '( %s -> 1 e. { 1 } )' % pm), Lm(bo2)], 'opelxpd',
             '( %s -> %s e. ( { 1 } X. 2o ) )' % (pm, ZL))
    nv = rd_bit(w, pm, 'Bit', 'm', ZL, mm, zb)
    NVv = NVF('TMrdBit', 'm', ZL)
    da0 = nv['fields']['da']
    dn1 = not1o(w, pm, da0, 'TMda', NVv)
    pbv = pbr_val(w, pm, nv, NVv, ZL, zb)
    ORC = '( ( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o ) )' % (NVv, NVv)
    ifv = 'if ( ( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o ) , 1o , (/) )' % (NVv, NVv)
    lv = load_val(w, pm, lambda t: dict(fl='if ( ( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o ) , 1o , (/) )' % (t, t)), NVv, nv['mem'],
                  clmap={ifv: w.s([closed(w, pm, '1oel2o', '1o e. 2o'), closed(w, pm, '0el2o', '(/) e. 2o')], 'ifcld', '( %s -> %s e. 2o )' % (pm, ifv))})
    NL = '( %s ` %s )' % (LORB, NVv)
    fcond = w.s([mc, w.inst('simp1')], 'syl', '( %s -> ( TMfl ` m ) = %s )' % (pm, FLV('i')))
    ccond = w.s([mc, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` m ) = Q )' % pm)
    kcond = w.s([mc, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = %s )' % (pm, CRV('i')))
    flvi = w.s([w.s([w.s([Lm(xk)], 'eqeq1d', '( %s -> ( %s = 0 <-> %s = 0 ) )' % (pm, TOPX(CT('i')), T0i))], 'ifbid',
                    '( %s -> %s = if ( %s = 0 , (/) , 1o ) )' % (pm, FLV('i'), T0i))], 'id', '') if False else \
        w.s([w.s([Lm(xk)], 'eqeq1d', '( %s -> ( %s = 0 <-> %s = 0 ) )' % (pm, TOPX(CT('i')), T0i))], 'ifbid',
            '( %s -> %s = if ( %s = 0 , (/) , 1o ) )' % (pm, FLV('i'), T0i))
    fnv = w.s([w.s([nv['fields']['fl'], fcond], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pm, NVv, FLV('i'))), flvi], 'eqtrd',
              '( %s -> ( TMfl ` %s ) = if ( %s = 0 , (/) , 1o ) )' % (pm, NVv, T0i))
    bsv = w.s([w.s([nv['fields']['ra']], 'fveq2d', '( %s -> ( bitOf ` ( TMra ` %s ) ) = ( bitOf ` ( inl ` ( 2nd ` %s ) ) ) )' % (pm, NVv, ZL)),
               w.s([w.s([zb, w.inst('tmcbit2')], 'syl', '( %s -> ( 2nd ` %s ) e. 2o )' % (pm, ZL)), w.inst('bitofsome')], 'syl',
                   '( %s -> ( bitOf ` ( inl ` ( 2nd ` %s ) ) ) = ( 2nd ` %s ) )' % (pm, ZL, ZL))], 'eqtrd', '( %s -> ( bitOf ` ( TMra ` %s ) ) = ( 2nd ` %s ) )' % (pm, NVv, ZL))
    o2 = w.s([closed(w, pm, '1ex', '1 e. _V'), w.s([Lm(bo2)], 'elexd', '( %s -> %s e. _V )' % (pm, BOi)), w.inst('op2ndg')], 'syl2anc',
             '( %s -> ( 2nd ` %s ) = %s )' % (pm, ZL, BOi))
    bsv2 = w.s([bsv, o2], 'eqtrd', '( %s -> ( bitOf ` ( TMra ` %s ) ) = %s )' % (pm, NVv, BOi))
    orq = w.s([w.s([fnv], 'eqeq1d', '( %s -> ( ( TMfl ` %s ) = 1o <-> if ( %s = 0 , (/) , 1o ) = 1o ) )' % (pm, NVv, T0i)),
               w.s([bsv2], 'eqeq1d', '( %s -> ( ( bitOf ` ( TMra ` %s ) ) = 1o <-> %s = 1o ) )' % (pm, NVv, BOi))], 'orbi12d',
              '( %s -> ( %s <-> ( if ( %s = 0 , (/) , 1o ) = 1o \\/ %s = 1o ) ) )' % (pm, ORC[2:-2] if False else '( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o )' % (NVv, NVv), T0i, BOi))
    orr = w.s([orq, Lm(itp[IB])], 'bitrd', '( %s -> ( ( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o ) <-> -. %s = 0 ) )' % (pm, NVv, NVv, T1i))
    fe = w.s([w.s([orr], 'ifbid', '( %s -> %s = if ( -. %s = 0 , 1o , (/) ) )' % (pm, ifv, T1i)), closed(w, pm, 'ifnot', 'if ( -. %s = 0 , 1o , (/) ) = %s' % (T1i, FL1))],
             'eqtrd', '( %s -> %s = %s )' % (pm, ifv, FL1))
    flL = w.s([lv['fields']['fl'], fe], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pm, NL, FL1))
    cmL = w.s([w.s([lv['fields']['cmp'], nv['fields']['cmp']], 'eqtrd', '( %s -> ( TMcmp ` %s ) = ( TMcmp ` m ) )' % (pm, NL)), ccond], 'eqtrd',
              '( %s -> ( TMcmp ` %s ) = Q )' % (pm, NL))
    nlt = w.s([w.s([Lm(ilt), w.s([Lm(cl.mem('i', 'RR')), Lm(cl.mem(NF, 'RR'))], 'ltnsymd' if False else 'jca', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
    nlt = w.s([Lm(ilt), w.inst('ltnsym') if False else None], '', '') if False else None
    nlt2 = w.s([Lm(cl.mem('i', 'RR')), Lm(cl.mem(NF, 'RR')), Lm(ilt), w.inst('ltnsymd') if False else w.inst('ltnsym2') if False else None], '', '') if False else None
    nltv = w.s([w.s([Lm(cl.mem('i', 'RR')), Lm(cl.mem(NF, 'RR'))], 'jca', '( %s -> ( i e. RR /\\ %s e. RR ) )' % (pm, NF)), w.inst('ltnsym')], 'syl',
               '( %s -> ( i < %s -> -. %s < i ) )' % (pm, NF, NF))
    nl = w.s([Lm(ilt), nltv], 'mpd', '( %s -> -. %s < i )' % (pm, NF))
    crv0 = w.s([nl], 'iffalsed', '( %s -> %s = (/) )' % (pm, CRV('i')))
    caL = w.s([w.s([w.s([lv['fields']['car'], nv['fields']['car']], 'eqtrd', '( %s -> ( TMcar ` %s ) = ( TMcar ` m ) )' % (pm, NL)), kcond], 'eqtrd',
                   '( %s -> ( TMcar ` %s ) = %s )' % (pm, NL, CRV('i'))), crv0], 'eqtrd', '( %s -> ( TMcar ` %s ) = (/) )' % (pm, NL))
    daL = w.s([lv['fields']['da'], da0], 'eqtrd', '( %s -> ( TMda ` %s ) = (/) )' % (pm, NL))
    oc = w.s([w.s([flL, cmL, caL], '3jca', '( %s -> ( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = (/) ) )' % (pm, NL, FL1, NL, NL)), daL], 'jca',
             '( %s -> %s )' % (pm, OCLC(NL)))
    oin = rab_in(w, pm, OCL, OCLC, NL, lv['mem'], oc)
    ifc = w.s([w.s([dn1, pbv, oin], '3jca', '( %s -> ( -. ( TMda ` %s ) = 1o /\\ ( %s ` %s ) = %s /\\ %s e. %s ) )' % (pm, NVv, PBR, NVv, ZL, NL, OCL))], 'ralrimiva',
              '( %s -> A. m e. %s ( -. ( TMda ` %s ) = 1o /\\ ( %s ` %s ) = %s /\\ %s e. %s ) )' % (ps, NI, NVF('TMrdBit', 'm', ZL), PBR, NVF('TMrdBit', 'm', ZL), ZL, NL.replace('m', 'm'), OCL))
    # typings
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ps, ST_FLTY[len('( %s -> ' % SEQ):-2]))
    flp = parts(w, ps, fl, parse_conj(ST_FLTY[len('( %s -> ' % SEQ):-2]))
    ocs = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % OCL)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, OCL)), mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, OCL))
    tv = mk['tv']
    labs = bc.base
    qcl = loadcl(w, ps, tv, LCAR1, GT(LMB['Q']), ldty2(w, ps, mk, lambda t: dict(car='1o')), gotocl(w, ps, tv, LMB['Q'], labs[LAB(LMB['Q'])] if LAB(LMB['Q']) in labs else labs['%s e. ( 2nd ` ( 1st ` T ) )' % LMB['Q']]))
    zlk = w.s([w.s([bo2, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, ZL)), mk['k']['K']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ps, ZL, GX('K')))
    zli = w.s([w.s([bo2, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, ZL)), mk['k']['I']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ps, ZL, GX('I')))
    ex = {RTY('TMrdBit', 'I'): mk['k']['I']['hdl']['TMrdBit'], CTY('TMda'): flp[CTY('TMda')], PTY(PBR, 'K'): pbr_ty(w, ps, mk, 'K'),
          LTY(LORB): ldty2(w, ps, mk, lambda t: dict(fl='if ( ( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o ) , 1o , (/) )' % (t, t))),
          '%s e. ( TM2Stmt ` T )' % LCQ: qcl, '%s e. %s' % (ZL, GX('I')): zli, '%s e. %s' % (ZL, GX('K')): zlk,
          WRD(SREST, GX('I')): w.s([srg, mk['k']['I']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, SREST, GX('I'))),
          '%s C_ ( 2nd ` T )' % NI: bc.famss('i', inn), '%s C_ ( 2nd ` T )' % OCL: ocs,
          concl(w, ps, ifc): ifc, '( %s ` I ) = ( <" %s "> ++ %s )' % (PT, ZL, SREST): vals['I'][1]}
    ZLXK = '( <" %s "> ++ %s )' % (ZL, XK)
    zlxg = wgcat(w, ps, '<" %s ">' % ZL, XK, zlg, vals['K'][2])
    run.call('tm2fbls1', {'A': LMB['B'], 'E': LMB['Q'], 'K': 'I', 'J': 'K', 'F': 'TMrdBit', 'C': 'TMda', 'Q': LCQ, 'P': PBR, 'L': LORB,
                          'Z': ZL, "Z'": ZL, 'X': SREST, 'N': NI, "N'": OCL}, ex, [('I', SREST, srg), ('K', ZLXK, zlxg)])
    # the test da fails : branch to Q2
    pm2 = '( %s /\\ m e. %s )' % (ps, OCL)
    mm2, mc2 = rab_elim(w, pm2, OCL, OCLC, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm2, OCL)))
    dz = w.s([mc2], 'simprd', '( %s -> ( TMda ` m ) = (/) )' % pm2)
    hf = w.s([not1o(w, pm2, dz, 'TMda', 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( TMda ` m ) = 1o )' % (ps, OCL))
    exb = {CTY('TMda'): flp[CTY('TMda')], '%s e. ( TM2Stmt ` T )' % GT(LMB['Q1']): gotocl(w, ps, tv, LMB['Q1'], labs['%s e. ( 2nd ` ( 1st ` T ) )' % LMB['Q1']]),
           '%s C_ ( 2nd ` T )' % OCL: ocs, 'A. m e. %s -. ( TMda ` m ) = 1o' % OCL: hf}
    run.call('tm2fbrg', {'A': LMB['Q'], 'C': 'TMda', 'Q': GT(LMB['Q1']), 'E': LMB['Q2'], 'N': OCL}, exb, [])
    cur, out = run.normalize(K4)
    assert out == [('K', ZLXK), ('I', SREST)], out
    DQ = chain_text(PT, out)
    pvi, Si = bc.pv('i', inn)
    r1, x1 = w.rewrite(DQ, {PT: (PBL('i'), pvi)}, ps)
    chain = [('K', XWV('i')), ('J', YWV('i')), ('I', SWV('i')), ('K', ZLXK), ('I', SREST)]
    gam = {XWV('i'): Si.vals['K'][2], YWV('i'): Si.vals['J'][2], SWV('i'): Si.vals['I'][2], ZLXK: zlxg, SREST: srg}
    st, out2 = stk_normalize(w, ps, mk, 'D', c[STKD('D')], bc.ne, chain, gam, K4)
    assert out2 == [('K', ZLXK), ('J', YWV('i')), ('I', SREST)], out2
    x2 = chain_text('D', out2)
    e12 = w.s([r1, st], 'eqtrd', '( %s -> %s = %s )' % (ps, DQ, x2))
    # ZLXK = XWV( i + 1 ) , SREST = SWV( i + 1 )
    q1e = w.s([w.s([w.s([mm1], 'oveq2d', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( 2 ^ ( %s - i ) ) )' % (ps, Mi, NF))], 'oveq2d',
                   '( %s -> ( F / ( 2 ^ ( %s + 1 ) ) ) = ( F / ( 2 ^ ( %s - i ) ) ) )' % (ps, Mi, NF))], 'fveq2d',
              '( %s -> ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) = %s )' % (ps, Mi, T0i))
    w2 = w.s([w.s([bc.fn, mn, inn], '3jca', '( %s -> ( F e. NN0 /\\ %s e. NN0 /\\ i e. NN0 ) )' % (ps, Mi)), w.inst('tmiblw2')], 'syl',
             '( %s -> ( %s bwrd ( i + 1 ) ) = ( <" %s "> ++ ( ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) bwrd i ) ) )' % (ps, T1i, BOi, Mi))
    w2b = w.s([w2, w.s([w.s([q1e], 'oveq1d', '( %s -> ( ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) bwrd i ) = ( %s bwrd i ) )' % (ps, Mi, T0i))], 'oveq2d',
                       '( %s -> ( <" %s "> ++ ( ( |_ ` ( F / ( 2 ^ ( %s + 1 ) ) ) ) bwrd i ) ) = ( <" %s "> ++ ( %s bwrd i ) ) )' % (ps, BOi, Mi, BOi, T0i))],
              'eqtrd', '( %s -> ( %s bwrd ( i + 1 ) ) = ( <" %s "> ++ ( %s bwrd i ) ) )' % (ps, T1i, BOi, T0i))
    t0n = w.s([bc.fn, w.s([closed(w, ps, '2nn', '2 e. NN'), w.s([inn, bc.nfn, ile, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( %s - i ) e. NN0 )' % (ps, NF)),
                           w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ ( %s - i ) ) e. NN )' % (ps, NF)), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, T0i))
    t0w = w.s([w.s([t0n], 'nn0zd', '( %s -> %s e. ZZ )' % (ps, T0i)), inn, w.inst('bwrdcl')], 'syl2anc', '( %s -> ( %s bwrd i ) e. Word 2o )' % (ps, T0i))
    cc2 = w.s([s1w, t0w, ff, w.inst('ccatco')], 'syl3anc', '( %s -> ( inclBool o. ( <" %s "> ++ ( %s bwrd i ) ) ) = ( ( inclBool o. <" %s "> ) ++ ( inclBool o. ( %s bwrd i ) ) ) )'
              % (ps, BOi, T0i, BOi, T0i))
    ib2 = w.s([w.s([w.s([w2b], 'coeq2d', '( %s -> ( inclBool o. ( %s bwrd ( i + 1 ) ) ) = ( inclBool o. ( <" %s "> ++ ( %s bwrd i ) ) ) )' % (ps, T1i, BOi, T0i)), cc2], 'eqtrd',
                   '( %s -> ( inclBool o. ( %s bwrd ( i + 1 ) ) ) = ( ( inclBool o. <" %s "> ) ++ ( inclBool o. ( %s bwrd i ) ) ) )' % (ps, T1i, BOi, T0i)),
               w.s([sc], 'oveq1d', '( %s -> ( ( inclBool o. <" %s "> ) ++ ( inclBool o. ( %s bwrd i ) ) ) = ( <" %s "> ++ ( inclBool o. ( %s bwrd i ) ) ) )'
                   % (ps, BOi, T0i, ZL, T0i))], 'eqtrd', '( %s -> ( inclBool o. ( %s bwrd ( i + 1 ) ) ) = ( <" %s "> ++ ( inclBool o. ( %s bwrd i ) ) ) )' % (ps, T1i, ZL, T0i))
    xg = c[WRD('X', GAM)]
    ca2 = w.s([zlg, wib(w, ps, '( %s bwrd i )' % T0i, t0w), wg4(w, ps, 'X', xg), w.inst('ccatass')], 'syl3anc',
              '( %s -> ( ( <" %s "> ++ ( inclBool o. ( %s bwrd i ) ) ) ++ %s ) = %s )' % (ps, ZL, T0i, YX('X'), ZLXK))
    XW1s = '( ( inclBool o. ( %s bwrd ( i + 1 ) ) ) ++ %s )' % (T1i, YX('X'))
    xw1 = w.s([w.s([ib2], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ ( inclBool o. ( %s bwrd i ) ) ) ++ %s ) )' % (ps, XW1s, ZL, T0i, YX('X'))), ca2], 'eqtrd',
              '( %s -> %s = %s )' % (ps, XW1s, ZLXK))
    ctt = w.s([w.s([w.s([w.s([ct1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                        '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - %s ) ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                   '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - %s ) ) ) )' % (ps, NF, CT(I1), NF, I1))], 'fveq2d',
              '( %s -> %s = %s )' % (ps, TOPX(CT(I1)), T1i))
    xw1b = w.s([w.s([w.s([w.s([ctt, ct1], 'oveq12d', '( %s -> ( %s bwrd %s ) = ( %s bwrd %s ) )' % (ps, TOPX(CT(I1)), CT(I1), T1i, I1))], 'coeq2d',
                         '( %s -> ( inclBool o. ( %s bwrd %s ) ) = ( inclBool o. ( %s bwrd %s ) ) )' % (ps, TOPX(CT(I1)), CT(I1), T1i, I1))], 'oveq1d',
                    '( %s -> %s = %s )' % (ps, XWV(I1), XW1s)), xw1], 'eqtrd', '( %s -> %s = %s )' % (ps, XWV(I1), ZLXK))
    sw1 = w.s([i1le], 'iftrued', '( %s -> %s = %s )' % (ps, SWV(I1), SREST))
    r3, x3 = w.rewrite(x2, {ZLXK: (XWV(I1), w.s([xw1b], 'eqcomd', '( %s -> %s = %s )' % (ps, ZLXK, XWV(I1)))),
                            SREST: (SWV(I1), w.s([sw1], 'eqcomd', '( %s -> %s = %s )' % (ps, SREST, SWV(I1))))}, ps)
    assert x3 == PSX, x3
    deq = w.s([e12, r3], 'eqtrd', '( %s -> %s = %s )' % (ps, DQ, PSX))
    t2, C2, D2, n2 = hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=clneq(w, ps, LMB['Q2'], OCL, deq, DQ, PSX), qed=True)
    return w.run()


CI_ = '( bl ` %s )' % TOPX(CT('i'))
NI1 = '( %s ` %s )' % (NBF, I1)
PI1 = '( %s ` %s )' % (PV, I1)
BND1 = '( 1 + ( ( 2 x. ( # ` ( encodeNat ` %s ) ) ) + 3 ) )' % CI_
PSI1 = '( %s /\\ -. %s = 0 )' % (PSIL, T1i)
PSI0 = '( %s /\\ %s = 0 )' % (PSIL, T1i)
CONCL_1 = TRI(CLN(LMB['Q2'], OCL, PSX), CLN(LMB['L'], NI1, PI1), BND1)
CONCL_0 = TRI(CLN(LMB['Q2'], OCL, PSX), CLN(LMB['L'], NI1, PI1), '( 1 + 1 )')


def next_ctx(w, ps, lift):
    """shared facts of tmibl1 / tmibl0"""
    it = It(w, ps, lift, 'simp2' if False else None) if False else None
    return None


def tail(w, ps, which):
    """the flag dispatch at Q2 and the counter, for which = 1 ( T1 =/= 0 , incr ) or 0 ( T1 = 0 , skip )"""
    it = It(w, ps, 'simplll', None) if False else None
    bc = Bc(w, ps, lift='simplll')
    cl, mk, c = bc.cl, bc.mk, bc.c
    ii = w.s([], 'simpllr' if True else '', '( %s -> i e. ( 0 ..^ ( %s + 1 ) ) )' % (ps, NF))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    cl.leaf('i', 'NN0', inn)
    ilt = w.s([], 'simplr', '( %s -> i < %s )' % (ps, NF))
    ile = w.s([ilt], 'ltled', '( %s -> i <_ %s )' % (ps, NF))
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    i1le = w.s([ilt, w.s([cl.mem('i', 'ZZ'), cl.mem(NF, 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < %s <-> %s <_ %s ) )' % (ps, NF, I1, NF))],
               'mpbid', '( %s -> %s <_ %s )' % (ps, I1, NF))
    cti = w.s([ile], 'iftrued', '( %s -> %s = i )' % (ps, CT('i')))
    ct1 = w.s([i1le], 'iftrued', '( %s -> %s = %s )' % (ps, CT(I1), I1))
    t1c = w.s([], 'simpr', '( %s -> %s%s = 0 )' % (ps, '-. ' if which == 1 else '', T1i))
    itf = w.s([w.s([bc.fn, inn, ilt], '3jca', '( %s -> ( F e. NN0 /\\ i e. NN0 /\\ i < %s ) )' % (ps, NF)), w.inst('tmiblit')], 'syl',
              '( %s -> %s )' % (ps, tsub_text(ST_IT, {'I': 'i'}).split(' -> ', 1)[1][:-2]))
    itp = parts(w, ps, itf, parse_conj(tsub_text(ST_IT, {'I': 'i'}).split(' -> ', 1)[1][:-2]))
    tv = mk['tv']
    dd = c[STKD('D')]
    labs = bc.base
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ps, ST_FLTY[len('( %s -> ' % SEQ):-2]))
    flp = parts(w, ps, fl, parse_conj(ST_FLTY[len('( %s -> ' % SEQ):-2]))
    ocs = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % OCL)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, OCL)), mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, OCL))
    # the stacks PSX
    pv0, S0i = bc.pv('i', inn)
    pv1, S1 = bc.pv(I1, i1n)
    vals = {s_: selfval(w, ps, mk, 'D', dd, s_) for s_ in K4}
    Sb = Stacks(w, ps, mk, 'D', dd, bc.ne, vals)
    SX = Sb.upd('K', XWV(I1), S1.vals['K'][2]).upd('J', YWV('i'), S0i.vals['J'][2]).upd('I', SWV(I1), S1.vals['I'][2])
    assert SX.D == PSX
    run = Run(w, ps, mk, Sb, bc.base, c)
    run.S = SX; run.chain = [('K', XWV(I1)), ('J', YWV('i')), ('I', SWV(I1))]
    for v_, g_ in [(XWV(I1), S1.vals['K'][2]), (YWV('i'), S0i.vals['J'][2]), (SWV(I1), S1.vals['I'][2])]:
        run.gam[v_] = g_
    # class facts on OCL
    pm = '( %s /\\ m e. %s )' % (ps, OCL)
    mm, mc = rab_elim(w, pm, OCL, OCLC, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, OCL)))
    fm = w.s([w.s([mc], 'simpld', '( %s -> ( ( TMfl ` m ) = %s /\\ ( TMcmp ` m ) = Q /\\ ( TMcar ` m ) = (/) ) )' % (pm, FL1)), w.inst('simp1')], 'syl',
             '( %s -> ( TMfl ` m ) = %s )' % (pm, FL1))
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    FLVn = FLV(I1)
    fv1 = w.s([w.s([w.s([w.s([w.s([w.s([ct1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                                  '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - %s ) ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                             '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - %s ) ) ) )' % (ps, NF, CT(I1), NF, I1))], 'fveq2d',
                        '( %s -> %s = %s )' % (ps, TOPX(CT(I1)), T1i))], 'eqeq1d', '( %s -> ( %s = 0 <-> %s = 0 ) )' % (ps, TOPX(CT(I1)), T1i))], 'ifbid',
              '( %s -> %s = %s )' % (ps, FLVn, FL1))
    ncr = w.s([w.s([i1le, w.s([cl.mem(I1, 'RR'), cl.mem(NF, 'RR')], 'lenltd', '( %s -> ( %s <_ %s <-> -. %s < %s ) )' % (ps, I1, NF, NF, I1))], 'mpbid',
                   '( %s -> -. %s < %s )' % (ps, NF, I1))], 'iffalsed', '( %s -> %s = (/) )' % (ps, CRV(I1)))
    if which == 1:
        f1 = w.s([t1c], 'iffalsed', '( %s -> %s = 1o )' % (ps, FL1))
        ht = w.s([w.s([fm, Lm(f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ps, OCL))
        exb = {CTY('TMfl'): flp[CTY('TMfl')], '%s e. ( TM2Stmt ` T )' % GT(LMB['Q3']): gotocl(w, ps, tv, LMB['Q3'], labs['%s e. ( 2nd ` ( 1st ` T ) )' % LMB['Q3']]),
               '%s C_ ( 2nd ` T )' % OCL: ocs, 'A. m e. %s ( TMfl ` m ) = 1o' % OCL: ht}
        run.call('tm2lbrt', {'A': LMB['Q2'], 'C': 'TMfl', 'E': LMB['Z0'], 'Q': GT(LMB['Q3']), 'N': OCL}, exb, [])
        # incr y s' at the class NP( 1o , Q , (/) )
        NPX = NP('1o', 'Q', '(/)')
        s1 = w.s([mc], 'simpld', '( %s -> ( ( TMfl ` m ) = %s /\\ ( TMcmp ` m ) = Q /\\ ( TMcar ` m ) = (/) ) )' % (pm, FL1))
        f1m = w.s([fm, Lm(f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
        inp = np_in(w, pm, 'm', mm, f1m, w.s([s1, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` m ) = Q )' % pm),
                    w.s([s1, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = (/) )' % pm)) if False else None
        idh = w.s([], 'id', '( h = m -> h = m )')
        NPCOND1 = lambda t: '( ( TMfl ` %s ) = 1o /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = (/) )' % (t, t, t)
        inp = rab_in(w, pm, NPX, NPCOND1, 'm', mm, w.s([f1m, w.s([s1, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` m ) = Q )' % pm),
                                                        w.s([s1, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = (/) )' % pm)], '3jca', '( %s -> %s )' % (pm, NPCOND1('m'))))
        oss = w.s([inp], 'ssrdv' if False else 'ralrimiva', '( %s -> A. m e. %s m e. %s )' % (ps, OCL, NPX))
        oss2 = w.s([oss], 'dfss3' if False else 'ssrdv' if False else 'id', '') if False else None
        oss2 = w.s([w.s([inp], 'ex', '( %s -> ( m e. %s -> m e. %s ) )' % (ps, OCL, NPX))], 'ssrdv', '( %s -> %s C_ %s )' % (ps, OCL, NPX))
        C_ = CI_
        cn = w.s([w.s([w.s([bc.fn, w.s([closed(w, ps, '2nn', '2 e. NN'), bc.topn(CT('i'), *bc.ct('i', inn))[1], w.inst('nnexpcl')], 'syl2anc',
                                           '( %s -> ( 2 ^ ( %s - %s ) ) e. NN )' % (ps, NF, CT('i'))), w.inst('fldivnn0')], 'syl2anc',
                                '( %s -> %s e. NN0 )' % (ps, TOPX(CT('i'))))], 'id', '') if False else
                  bc.topn(CT('i'), *bc.ct('i', inn))[0], w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ps, C_))
        EC = ENC(C_)
        ecw = w.s([cn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, EC))
        gv = w.s([cn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (ps, C_, EC))
        S = run.S
        jv = w.s([S.vals['J'][1], w.s([gv], 'oveq1d', '( %s -> %s = %s )' % (ps, YWV('i'), CC('( inclBool o. %s )' % EC, YX('( D ` J )'))))], 'eqtrd',
                 '( %s -> ( %s ` J ) = %s )' % (ps, S.D, CC('( inclBool o. %s )' % EC, YX('( D ` J )'))))
        # the post class
        NPOST = NI1
        rcl = w.s([w.s([w.s([fv1, f1], 'eqtrd', '( %s -> %s = 1o )' % (ps, FLVn))], 'eqeq2d', '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = 1o ) )' % (ps, FLVn)),
                   w.s([], 'biidd', '( %s -> ( ( TMcmp ` h ) = Q <-> ( TMcmp ` h ) = Q ) )' % ps),
                   w.s([ncr], 'eqeq2d', '( %s -> ( ( TMcar ` h ) = %s <-> ( TMcar ` h ) = (/) ) )' % (ps, CRV(I1)))], '3anbi123d',
                  '( %s -> ( %s <-> %s ) )' % (ps, NBC('h', I1), NPCOND1('h')))
        rb = w.s([w.s([rcl], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( %s <-> %s ) )' % (ps, NBC('h', I1), NPCOND1('h')))], 'rabbidva',
                 '( %s -> %s = %s )' % (ps, RAB(NBC, I1), NPX))
        fvn = famval(w, ps, NBC, I1, i1n)
        cls = w.s([w.s([fvn, rb], 'eqtrd', '( %s -> %s = %s )' % (ps, NI1, NPX))], 'eqcomd', '( %s -> %s = %s )' % (ps, NPX, NI1))
        IW = CC('( inclBool o. ( incBits ` %s ) )' % EC, YX('( D ` J )'))
        iwg = wgcat(w, ps, '( inclBool o. ( incBits ` %s ) )' % EC, YX('( D ` J )'), wib(w, ps, '( incBits ` %s )' % EC, w.s([ecw, w.inst('incbitscl')], 'syl',
                                                                                                                         '( %s -> ( incBits ` %s ) e. Word 2o )' % (ps, EC))),
                    wg4(w, ps, '( D ` J )', bc.dsg('J')))
        run.call('tmiinc', {'K': 'J', 'J': "I'", 'L': EC, 'X': '( D ` J )', 'O': '1o', 'Q': 'Q', 'R': '(/)', 'P': PL('P', 11), 'E': LMB['L']},
                 {'( %s ` J ) = %s' % (S.D, CC('( inclBool o. %s )' % EC, YX('( D ` J )'))): jv, WRD(EC, '2o'): ecw, WRD('( D ` J )', GAM): bc.dsg('J')},
                 [('J', IW, iwg)], pre=(OCL, oss2), cls_rw=(cls, NI1))
        # the counter: IW = YWV( i + 1 )
        es = w.s([cn, w.inst('encnatsuc')], 'syl', '( %s -> ( encodeNat ` ( %s + 1 ) ) = ( incBits ` %s ) )' % (ps, C_, EC))
        c1n = w.s([cn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ps, C_))
        g1 = w.s([c1n, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` ( %s + 1 ) ) = ( inclBool o. ( encodeNat ` ( %s + 1 ) ) ) )' % (ps, C_, C_))
        g2 = w.s([g1, w.s([es], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` ( %s + 1 ) ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ps, C_, EC))], 'eqtrd',
                 '( %s -> ( encNatGam ` ( %s + 1 ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ps, C_, EC))
        # ( bl ` TOPX( CT( i + 1 ) ) ) = ( C_ + 1 )
        tci = w.s([w.s([w.s([w.s([w.s([cti], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - i ) )' % (ps, NF, CT('i'), NF))], 'oveq2d',
                                  '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - i ) ) )' % (ps, NF, CT('i'), NF))], 'oveq2d',
                             '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - i ) ) ) )' % (ps, NF, CT('i'), NF))], 'fveq2d',
                        '( %s -> %s = %s )' % (ps, TOPX(CT('i')), T0i))], 'fveq2d', '( %s -> %s = ( bl ` %s ) )' % (ps, C_, T0i))
        tc1 = w.s([w.s([w.s([w.s([w.s([ct1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                                  '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - %s ) ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                             '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - %s ) ) ) )' % (ps, NF, CT(I1), NF, I1))], 'fveq2d',
                        '( %s -> %s = %s )' % (ps, TOPX(CT(I1)), T1i))], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` %s ) )' % (ps, TOPX(CT(I1)), T1i))
        ICs = tsub_text(IT_C, {'I': 'i'})
        blst = w.s([t1c, itp[ICs]], 'mpd' if False else 'mpi' if False else 'mpd', '') if False else None
        blst = w.s([t1c, itp[ICs]], 'mpd', '( %s -> ( bl ` %s ) = ( ( bl ` %s ) + 1 ) )' % (ps, T1i, T0i))
        cnew = w.s([w.s([tc1, blst], 'eqtrd', '( %s -> ( bl ` %s ) = ( ( bl ` %s ) + 1 ) )' % (ps, TOPX(CT(I1)), T0i)),
                    w.s([tci], 'oveq1d', '( %s -> ( %s + 1 ) = ( ( bl ` %s ) + 1 ) )' % (ps, C_, T0i))], 'eqtr4d',
                   '( %s -> ( bl ` %s ) = ( %s + 1 ) )' % (ps, TOPX(CT(I1)), C_))
        yw1 = w.s([w.s([w.s([w.s([cnew], 'fveq2d', '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( encNatGam ` ( %s + 1 ) ) )' % (ps, TOPX(CT(I1)), C_)), g2], 'eqtrd',
                            '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ps, TOPX(CT(I1)), EC))], 'oveq1d',
                       '( %s -> %s = %s )' % (ps, YWV(I1), IW))], 'id', '') if False else \
            w.s([w.s([w.s([cnew], 'fveq2d', '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( encNatGam ` ( %s + 1 ) ) )' % (ps, TOPX(CT(I1)), C_)), g2], 'eqtrd',
                     '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ps, TOPX(CT(I1)), EC))], 'oveq1d',
                '( %s -> %s = %s )' % (ps, YWV(I1), IW))
        NEWJ, NEWJs = IW, yw1
    else:
        f0 = w.s([t1c], 'iftrued', '( %s -> %s = (/) )' % (ps, FL1))
        hf = w.s([not1o(w, pm, w.s([fm, Lm(f0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm), 'TMfl', 'm')], 'ralrimiva',
                 '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (ps, OCL))
        exb = {CTY('TMfl'): flp[CTY('TMfl')], '%s e. ( TM2Stmt ` T )' % GT(LMB['Z0']): gotocl(w, ps, tv, LMB['Z0'], labs['%s e. ( 2nd ` ( 1st ` T ) )' % LMB['Z0']]),
               '%s C_ ( 2nd ` T )' % OCL: ocs, 'A. m e. %s -. ( TMfl ` m ) = 1o' % OCL: hf}
        run.call('tm2fbrg', {'A': LMB['Q2'], 'C': 'TMfl', 'Q': GT(LMB['Z0']), 'E': LMB['Q3'], 'N': OCL}, exb, [])
        # skip : load ( _I |` TMSt ) into ( NBF ` ( i + 1 ) )
        rin = w.s([], 'simpr', '( %s -> m e. %s )' % (pm, OCL))
        lid = w.s([mm, w.inst('fvresi')], 'syl', '( %s -> ( ( _I |` TMSt ) ` m ) = m )' % pm)
        s1 = w.s([mc], 'simpld', '( %s -> ( ( TMfl ` m ) = %s /\\ ( TMcmp ` m ) = Q /\\ ( TMcar ` m ) = (/) ) )' % (pm, FL1))
        fl1 = w.s([fm, w.s([Lm(fv1)], 'eqcomd', '( %s -> %s = %s )' % (pm, FL1, FLVn))], 'eqtrd', '( %s -> ( TMfl ` m ) = %s )' % (pm, FLVn))
        ca1 = w.s([w.s([s1, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = (/) )' % pm), w.s([Lm(ncr)], 'eqcomd', '( %s -> (/) = %s )' % (pm, CRV(I1)))],
                  'eqtrd', '( %s -> ( TMcar ` m ) = %s )' % (pm, CRV(I1)))
        cnd = w.s([fl1, w.s([s1, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` m ) = Q )' % pm), ca1], '3jca', '( %s -> %s )' % (pm, NBC('m', I1)))
        inn1 = fam_pack(w, pm, NBC, I1, Lm(i1n), 'm', mm, cnd)
        inn2 = w.s([lid, inn1], 'eqeltrd', '( %s -> ( ( _I |` TMSt ) ` m ) e. %s )' % (pm, NI1))
        hl = w.s([inn2], 'ralrimiva', '( %s -> A. m e. %s ( ( _I |` TMSt ) ` m ) e. %s )' % (ps, OCL, NI1))
        hl2 = w.s([hl], 'id', '') if False else None
        # tm2flg wants the binder r
        hlr = w.s([hl, w.s([], 'cbvralvw' if False else 'id', '') if False else None], '', '') if False else None
        cb = w.s([w.s([], 'fveq2', '( m = r -> ( ( _I |` TMSt ) ` m ) = ( ( _I |` TMSt ) ` r ) )')], 'eleq1d',
                 '( m = r -> ( ( ( _I |` TMSt ) ` m ) e. %s <-> ( ( _I |` TMSt ) ` r ) e. %s ) )' % (NI1, NI1))
        cbv = w.s([cb], 'cbvralvw', '( A. m e. %s ( ( _I |` TMSt ) ` m ) e. %s <-> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (OCL, NI1, OCL, NI1))
        hlr = w.s([hl, cbv], 'sylib', '( %s -> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (ps, OCL, NI1))
        f1_ = w.s([], 'f1oi', '( _I |` TMSt ) : TMSt -1-1-onto-> TMSt')
        ff = w.s([w.s([f1_, w.inst('f1of')], 'ax-mp', '( _I |` TMSt ) : TMSt --> TMSt')], 'a1i', '( %s -> ( _I |` TMSt ) : TMSt --> TMSt )' % ps)
        sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
        em = w.s([w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ps), w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ps), w.inst('elmapg')], 'syl2anc',
                 '( %s -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )' % ps)
        li = w.s([em, ff], 'mpbird', '( %s -> ( _I |` TMSt ) e. ( TMSt ^m TMSt ) )' % ps)
        sq = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ps)
        mq = w.s([sq, sq], 'oveq12d', '( %s -> ( TMSt ^m TMSt ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ps)
        lty = w.s([li, mq], 'eleqtrd', '( %s -> %s )' % (ps, LTY(LID)))
        exl = {LTY(LID): lty, '%s C_ ( 2nd ` T )' % OCL: ocs, '%s C_ ( 2nd ` T )' % NI1: bc.famss(I1, i1n),
               'A. r e. %s ( %s ` r ) e. %s' % (OCL, LID, NI1): hlr}
        run.call('tm2flg', {'A': LMB['Q3'], 'E': LMB['L'], 'F': LID, 'N': OCL, "N'": NI1}, exl, [])
        IDs = tsub_text(IT_D, {'I': 'i'})
        bleq = w.s([t1c, itp[IDs]], 'mpd', '( %s -> ( bl ` %s ) = ( bl ` %s ) )' % (ps, T1i, T0i))
        tci = w.s([w.s([w.s([w.s([w.s([cti], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - i ) )' % (ps, NF, CT('i'), NF))], 'oveq2d',
                                  '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - i ) ) )' % (ps, NF, CT('i'), NF))], 'oveq2d',
                             '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - i ) ) ) )' % (ps, NF, CT('i'), NF))], 'fveq2d',
                        '( %s -> %s = %s )' % (ps, TOPX(CT('i')), T0i))], 'fveq2d', '( %s -> %s = ( bl ` %s ) )' % (ps, CI_, T0i))
        tc1 = w.s([w.s([w.s([w.s([w.s([ct1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                                  '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - %s ) ) )' % (ps, NF, CT(I1), NF, I1))], 'oveq2d',
                             '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - %s ) ) ) )' % (ps, NF, CT(I1), NF, I1))], 'fveq2d',
                        '( %s -> %s = %s )' % (ps, TOPX(CT(I1)), T1i))], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` %s ) )' % (ps, TOPX(CT(I1)), T1i))
        ceq = w.s([w.s([tc1, bleq], 'eqtrd', '( %s -> ( bl ` %s ) = ( bl ` %s ) )' % (ps, TOPX(CT(I1)), T0i)), tci], 'eqtr4d',
                  '( %s -> ( bl ` %s ) = %s )' % (ps, TOPX(CT(I1)), CI_))
        yw1 = w.s([w.s([ceq], 'fveq2d', '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( encNatGam ` %s ) )' % (ps, TOPX(CT(I1)), CI_))], 'oveq1d',
                  '( %s -> %s = %s )' % (ps, YWV(I1), YWV('i')))
        NEWJ, NEWJs = None, yw1
    cur, out = run.normalize(K4)
    DQ = chain_text('D', out)
    if which == 1:
        assert out == [('K', XWV(I1)), ('J', NEWJ), ('I', SWV(I1))], out
        r_, x_ = w.rewrite(DQ, {NEWJ: (YWV(I1), w.s([NEWJs], 'eqcomd', '( %s -> %s = %s )' % (ps, NEWJ, YWV(I1))))}, ps)
    else:
        assert out == [('K', XWV(I1)), ('J', YWV('i')), ('I', SWV(I1))], out
        r_, x_ = w.rewrite(DQ, {YWV('i'): (YWV(I1), w.s([NEWJs], 'eqcomd', '( %s -> %s = %s )' % (ps, YWV('i'), YWV(I1))))}, ps)
    assert x_ == PBL(I1), x_
    deq = w.s([r_, pv1], 'eqtr4d', '( %s -> %s = %s )' % (ps, DQ, PI1))
    hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=clneq(w, ps, LMB['L'], NI1, deq, DQ, PI1), qed=True)
    return run.n


def tmibl1():
    lab = 'tmibl1'
    w = W(lab, 'The counter of Lean\'s ` bitlen ` loop at the machine when the top is nonzero: the test ` flag ` holds '
               'and ` incr y s\' ` adds one to the bit length (Lean ` bl_step ` ), entering ` BlInv ` at ` i + 1 ` .')
    n = tail(w, PSI1, 1)
    assert n == BND1, n
    return w.run()


def tmibl0():
    lab = 'tmibl0'
    w = W(lab, 'The counter of Lean\'s ` bitlen ` loop at the machine while the top is zero: the test ` flag ` fails, '
               '` skip ` , and the bit length stays ( ` BlInv ` at ` i + 1 ` ).')
    n = tail(w, PSI0, 0)
    assert n == '( 1 + 1 )', n
    return w.run()


def OCLEC(h):
    return '( ( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = 1o ) /\\ ( TMda ` %s ) = 1o )' % (h, FLV('i'), h, h, h)
OCLE = '{ h e. TMSt | %s }' % OCLEC('h')
CONCL_E = TRI(CLN(LMB['B'], '( %s ` i )' % NBF, '( %s ` i )' % PV), CLN(LMB['L'], NI1, PI1), '( ( 1 + 1 ) + 1 )')
QPUSH = PUSH('K', PBR, LOAD(LORB, GT(LMB['Q'])))


def topfix(w, ps, ceq, t):
    """( ps -> TOPX( CT( t ) ) = TOPX( NF ) ) from ceq : ( ps -> CT( t ) = NF )"""
    return w.s([w.s([w.s([w.s([ceq], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (ps, NF, CT(t), NF, NF))], 'oveq2d',
                         '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ ( %s - %s ) ) )' % (ps, NF, CT(t), NF, NF))], 'oveq2d',
                    '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / ( 2 ^ ( %s - %s ) ) ) )' % (ps, NF, CT(t), NF, NF))], 'fveq2d',
               '( %s -> %s = %s )' % (ps, TOPX(CT(t)), TOPX(NF)))


def tmiblt():
    lab = 'tmiblt'
    ps = PSIE
    C = '( %s -> %s )' % (ps, CONCL_E)
    w = W(lab, 'The last iteration of Lean\'s ` bitlen ` loop at the machine ( ` blBody_runs ` , the terminator case): '
               '` blScan ` pops the comma from ` s ` and sets ` carry ` , the test ` da ` holds, ` skip ` , and the loop '
               'test ` !carry ` will fail.')
    bc = Bc(w, ps, lift='simpll')
    cl, mk, c = bc.cl, bc.mk, bc.c
    ii = w.s([], 'simplr', '( %s -> i e. ( 0 ..^ ( %s + 1 ) ) )' % (ps, NF))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    cl.leaf('i', 'NN0', inn)
    ilt1 = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < ( %s + 1 ) )' % (ps, NF))
    ile = w.s([ilt1, w.s([cl.mem('i', 'ZZ'), cl.mem(NF, 'ZZ'), w.inst('zleltp1')], 'syl2anc', '( %s -> ( i <_ %s <-> i < ( %s + 1 ) ) )' % (ps, NF, NF))],
              'mpbird', '( %s -> i <_ %s )' % (ps, NF))
    nlt = w.s([], 'simpr', '( %s -> -. i < %s )' % (ps, NF))
    ige = w.s([nlt, w.s([cl.mem(NF, 'RR'), cl.mem('i', 'RR')], 'lenltd', '( %s -> ( %s <_ i <-> -. i < %s ) )' % (ps, NF, NF))], 'mpbird', '( %s -> %s <_ i )' % (ps, NF))
    ieq = lineq(w, ps, 'i', NF, hyps=[ile, ige], closure=cl)
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, I1))
    cti = w.s([ile], 'iftrued', '( %s -> %s = i )' % (ps, CT('i')))
    ctin = w.s([cti, ieq], 'eqtrd', '( %s -> %s = %s )' % (ps, CT('i'), NF))
    ni1 = w.s([w.s([cl.mem(I1, 'RR'), cl.mem(NF, 'RR'), w.s([w.s([ieq], 'oveq1d', '( %s -> %s = ( %s + 1 ) )' % (ps, I1, NF)),
                                                               linarith(w, ps, [], '%s < ( %s + 1 )' % (NF, NF), closure=cl)], 'id', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
    nlt1 = linarith(w, ps, [ieq], '%s < %s' % (NF, I1), closure=cl)
    ni1 = w.s([nlt1, w.s([cl.mem(NF, 'RR'), cl.mem(I1, 'RR')], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (ps, NF, I1, I1, NF))], 'mpbid',
              '( %s -> -. %s <_ %s )' % (ps, I1, NF))
    ct1 = w.s([ni1], 'iffalsed', '( %s -> %s = %s )' % (ps, CT(I1), NF))
    mem, SP = bc.pvals('i', inn)
    PT = "( %s ` i )" % PV
    DV = lambda s_: '( D ` %s )' % s_
    # ( PT ` I ) = ( <" 4 "> ++ ( D ` I ) )
    SI_i = '( ( inclBool o. ( reverse ` %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % LOWV('i')
    s1 = w.s([ile], 'iftrued', '( %s -> %s = %s )' % (ps, SWV('i'), SI_i))
    ni0 = w.s([w.s([ieq], 'oveq2d', '( %s -> ( %s - i ) = ( %s - %s ) )' % (ps, NF, NF, NF)), w.s([cl.mem(NF, 'CC')], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (ps, NF, NF))],
              'eqtrd', '( %s -> ( %s - i ) = 0 )' % (ps, NF))
    L00 = '( ( F mod ( 2 ^ 0 ) ) bwrd 0 )'
    lw0 = w.s([w.s([w.s([w.s([ni0], 'oveq2d', '( %s -> ( 2 ^ ( %s - i ) ) = ( 2 ^ 0 ) )' % (ps, NF))], 'oveq2d',
                        '( %s -> ( F mod ( 2 ^ ( %s - i ) ) ) = ( F mod ( 2 ^ 0 ) ) )' % (ps, NF))], 'id', '') if False else
               w.s([w.s([ni0], 'oveq2d', '( %s -> ( 2 ^ ( %s - i ) ) = ( 2 ^ 0 ) )' % (ps, NF))], 'oveq2d', '( %s -> ( F mod ( 2 ^ ( %s - i ) ) ) = ( F mod ( 2 ^ 0 ) ) )' % (ps, NF)),
               ni0], 'oveq12d', '( %s -> %s = %s )' % (ps, LOWV('i'), L00))
    mz = w.s([w.s([bc.fn], 'nn0zd', '( %s -> F e. ZZ )' % ps), w.s([closed(w, ps, '2nn', '2 e. NN'), closed(w, ps, '0nn0', '0 e. NN0'), w.inst('nnexpcl')], 'syl2anc',
                                                                   '( %s -> ( 2 ^ 0 ) e. NN )' % ps), w.inst('zmodcl')], 'syl2anc', '( %s -> ( F mod ( 2 ^ 0 ) ) e. NN0 )' % ps)
    b0 = w.s([w.s([mz], 'nn0zd', '( %s -> ( F mod ( 2 ^ 0 ) ) e. ZZ )' % ps), w.inst('bwrd0')], 'syl', '( %s -> %s = (/) )' % (ps, L00))
    le0 = w.s([lw0, b0], 'eqtrd', '( %s -> %s = (/) )' % (ps, LOWV('i')))
    rv0 = w.s([w.s([le0], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` (/) ) )' % (ps, LOWV('i'))), closed(w, ps, 'rev0', '( reverse ` (/) ) = (/)')], 'eqtrd',
              '( %s -> ( reverse ` %s ) = (/) )' % (ps, LOWV('i')))
    ic0 = w.s([w.s([rv0], 'coeq2d', '( %s -> ( inclBool o. ( reverse ` %s ) ) = ( inclBool o. (/) ) )' % (ps, LOWV('i'))), closed(w, ps, 'co02', '( inclBool o. (/) ) = (/)')],
              'eqtrd', '( %s -> ( inclBool o. ( reverse ` %s ) ) = (/) )' % (ps, LOWV('i')))
    y4i = wg4(w, ps, DV('I'), bc.dsg('I'))
    si = w.s([w.s([s1, w.s([ic0], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ps, SI_i, YX(DV('I'))))], 'eqtrd', '( %s -> %s = ( (/) ++ %s ) )' % (ps, SWV('i'), YX(DV('I')))),
              w.s([y4i, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ps, YX(DV('I')), YX(DV('I'))))], 'eqtrd', '( %s -> %s = %s )' % (ps, SWV('i'), YX(DV('I'))))
    vals = dict(SP.vals)
    vals['I'] = (YX(DV('I')), w.s([SP.vals['I'][1], si], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ps, PT, YX(DV('I')))), y4i)
    SPs = Stacks(w, ps, mk, PT, mem, bc.ne, vals)
    run = Run(w, ps, mk, SPs, bc.base, c)
    # the interface on the terminator
    NI = '( %s ` i )' % NBF
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NBC, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    nv = rd_comma(w, pm, 'Bit', 'm', mm)
    NVv = NVF('TMrdBit', 'm', '4')
    da1 = nv['fields']['da']
    lv = load_val(w, pm, lambda t: dict(car='1o'), NVv, nv['mem'])
    NL = '( %s ` %s )' % (LCAR1, NVv)
    fl_ = w.s([w.s([lv['fields']['fl'], nv['fields']['fl']], 'eqtrd', '( %s -> ( TMfl ` %s ) = ( TMfl ` m ) )' % (pm, NL)),
               w.s([mc, w.inst('simp1')], 'syl', '( %s -> ( TMfl ` m ) = %s )' % (pm, FLV('i')))], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pm, NL, FLV('i')))
    cm_ = w.s([w.s([lv['fields']['cmp'], nv['fields']['cmp']], 'eqtrd', '( %s -> ( TMcmp ` %s ) = ( TMcmp ` m ) )' % (pm, NL)),
               w.s([mc, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` m ) = Q )' % pm)], 'eqtrd', '( %s -> ( TMcmp ` %s ) = Q )' % (pm, NL))
    da_ = w.s([lv['fields']['da'], da1], 'eqtrd', '( %s -> ( TMda ` %s ) = 1o )' % (pm, NL))
    oc = w.s([w.s([fl_, cm_, lv['fields']['car']], '3jca', '( %s -> ( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = 1o ) )' % (pm, NL, FLV('i'), NL, NL)),
              da_], 'jca', '( %s -> %s )' % (pm, OCLEC(NL)))
    oin = rab_in(w, pm, OCLE, OCLEC, NL, lv['mem'], oc)
    ifc = w.s([w.s([da1, oin], 'jca', '( %s -> ( ( TMda ` %s ) = 1o /\\ %s e. %s ) )' % (pm, NVv, NL, OCLE))], 'ralrimiva',
              '( %s -> A. m e. %s ( ( TMda ` %s ) = 1o /\\ %s e. %s ) )' % (ps, NI, NVv, NL, OCLE))
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ps, ST_FLTY[len('( %s -> ' % SEQ):-2]))
    flp = parts(w, ps, fl, parse_conj(ST_FLTY[len('( %s -> ' % SEQ):-2]))
    tv = mk['tv']
    labs = bc.base
    ocs = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % OCLE)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, OCLE)), mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, OCLE))
    qg = gotocl(w, ps, tv, LMB['Q'], labs['%s e. ( 2nd ` ( 1st ` T ) )' % LMB['Q']])
    lorbty = ldty2(w, ps, mk, lambda t: dict(fl='if ( ( ( TMfl ` %s ) = 1o \\/ ( bitOf ` ( TMra ` %s ) ) = 1o ) , 1o , (/) )' % (t, t)))
    qpcl = pushcl(w, ps, tv, 'K', PBR, LOAD(LORB, GT(LMB['Q'])), mk['k']['K']['kd'], pbr_ty(w, ps, mk, 'K'), loadcl(w, ps, tv, LORB, GT(LMB['Q']), lorbty, qg))
    g4 = closed(w, ps, 'gamma4', "4 e. Gamma'")
    ex = {RTY('TMrdBit', 'I'): mk['k']['I']['hdl']['TMrdBit'], CTY('TMda'): flp[CTY('TMda')], LTY(LCAR1): ldty2(w, ps, mk, lambda t: dict(car='1o')),
          '%s e. ( TM2Stmt ` T )' % QPUSH: qpcl, '4 e. %s' % GX('I'): w.s([g4, mk['k']['I']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ps, GX('I'))),
          WRD(DV('I'), GX('I')): w.s([bc.dsg('I'), mk['k']['I']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, DV('I'), GX('I'))),
          '%s C_ ( 2nd ` T )' % NI: bc.famss('i', inn), '%s C_ ( 2nd ` T )' % OCLE: ocs, concl(w, ps, ifc): ifc,
          '( %s ` I ) = %s' % (PT, YX(DV('I'))): vals['I'][1]}
    run.call('tm2fbls0', {'A': LMB['B'], 'E': LMB['Q'], 'K': 'I', 'F': 'TMrdBit', 'C': 'TMda', 'L': LCAR1, 'Q': QPUSH, 'Y': '4', 'X': DV('I'), 'N': NI, "N'": OCLE},
             ex, [('I', DV('I'), bc.dsg('I'))])
    # the test da holds : to Q1
    pm2 = '( %s /\\ m e. %s )' % (ps, OCLE)
    mm2, mc2 = rab_elim(w, pm2, OCLE, OCLEC, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm2, OCLE)))
    ht = w.s([w.s([mc2], 'simprd', '( %s -> ( TMda ` m ) = 1o )' % pm2)], 'ralrimiva', '( %s -> A. m e. %s ( TMda ` m ) = 1o )' % (ps, OCLE))
    exb = {CTY('TMda'): flp[CTY('TMda')], '%s e. ( TM2Stmt ` T )' % GT(LMB['Q2']): gotocl(w, ps, tv, LMB['Q2'], labs['%s e. ( 2nd ` ( 1st ` T ) )' % LMB['Q2']]),
           '%s C_ ( 2nd ` T )' % OCLE: ocs, 'A. m e. %s ( TMda ` m ) = 1o' % OCLE: ht}
    run.call('tm2lbrt', {'A': LMB['Q'], 'C': 'TMda', 'E': LMB['Q1'], 'Q': GT(LMB['Q2']), 'N': OCLE}, exb, [])
    # skip into ( NBF ` ( i + 1 ) )
    lid = w.s([mm2, w.inst('fvresi')], 'syl', '( %s -> ( ( _I |` TMSt ) ` m ) = m )' % pm2)
    s1_ = w.s([mc2], 'simpld', '( %s -> ( ( TMfl ` m ) = %s /\\ ( TMcmp ` m ) = Q /\\ ( TMcar ` m ) = 1o ) )' % (pm2, FLV('i')))
    Lm2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm2, concl(w, ps, st)))
    tfi = topfix(w, ps, ctin, 'i'); tf1 = topfix(w, ps, ct1, I1)
    ffv = w.s([w.s([w.s([tfi, tf1], 'eqtr4d', '( %s -> %s = %s )' % (ps, TOPX(CT('i')), TOPX(CT(I1))))], 'eqeq1d',
                   '( %s -> ( %s = 0 <-> %s = 0 ) )' % (ps, TOPX(CT('i')), TOPX(CT(I1))))], 'ifbid', '( %s -> %s = %s )' % (ps, FLV('i'), FLV(I1)))
    f1 = w.s([w.s([s1_, w.inst('simp1')], 'syl', '( %s -> ( TMfl ` m ) = %s )' % (pm2, FLV('i'))), Lm2(ffv)], 'eqtrd', '( %s -> ( TMfl ` m ) = %s )' % (pm2, FLV(I1)))
    c1 = w.s([w.s([s1_, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = 1o )' % pm2), w.s([Lm2(w.s([nlt1], 'iftrued', '( %s -> %s = 1o )' % (ps, CRV(I1))))], 'eqcomd',
                                                                                   '( %s -> 1o = %s )' % (pm2, CRV(I1)))], 'eqtrd', '( %s -> ( TMcar ` m ) = %s )' % (pm2, CRV(I1)))
    cnd = w.s([f1, w.s([s1_, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` m ) = Q )' % pm2), c1], '3jca', '( %s -> %s )' % (pm2, NBC('m', I1)))
    inn1 = fam_pack(w, pm2, NBC, I1, Lm2(i1n), 'm', mm2, cnd)
    hl = w.s([w.s([lid, inn1], 'eqeltrd', '( %s -> ( ( _I |` TMSt ) ` m ) e. %s )' % (pm2, NI1))], 'ralrimiva', '( %s -> A. m e. %s ( ( _I |` TMSt ) ` m ) e. %s )' % (ps, OCLE, NI1))
    cb = w.s([w.s([], 'fveq2', '( m = r -> ( ( _I |` TMSt ) ` m ) = ( ( _I |` TMSt ) ` r ) )')], 'eleq1d',
             '( m = r -> ( ( ( _I |` TMSt ) ` m ) e. %s <-> ( ( _I |` TMSt ) ` r ) e. %s ) )' % (NI1, NI1))
    cbv = w.s([cb], 'cbvralvw', '( A. m e. %s ( ( _I |` TMSt ) ` m ) e. %s <-> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (OCLE, NI1, OCLE, NI1))
    hlr = w.s([hl, cbv], 'sylib', '( %s -> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (ps, OCLE, NI1))
    f1_ = w.s([], 'f1oi', '( _I |` TMSt ) : TMSt -1-1-onto-> TMSt')
    ff = w.s([w.s([f1_, w.inst('f1of')], 'ax-mp', '( _I |` TMSt ) : TMSt --> TMSt')], 'a1i', '( %s -> ( _I |` TMSt ) : TMSt --> TMSt )' % ps)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    em = w.s([w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ps), w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ps), w.inst('elmapg')], 'syl2anc',
             '( %s -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )' % ps)
    li = w.s([em, ff], 'mpbird', '( %s -> ( _I |` TMSt ) e. ( TMSt ^m TMSt ) )' % ps)
    sq = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ps)
    mq = w.s([sq, sq], 'oveq12d', '( %s -> ( TMSt ^m TMSt ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ps)
    lty = w.s([li, mq], 'eleqtrd', '( %s -> %s )' % (ps, LTY(LID)))
    exl = {LTY(LID): lty, '%s C_ ( 2nd ` T )' % OCLE: ocs, '%s C_ ( 2nd ` T )' % NI1: bc.famss(I1, i1n), 'A. r e. %s ( %s ` r ) e. %s' % (OCLE, LID, NI1): hlr}
    run.call('tm2flg', {'A': LMB['Q1'], 'E': LMB['L'], 'F': LID, 'N': OCLE, "N'": NI1}, exl, [])
    cur, out = run.normalize(K4)
    assert out == [('I', DV('I'))], out
    DQ = chain_text(PT, out)
    pvi, Si = bc.pv('i', inn)
    r1, x1 = w.rewrite(DQ, {PT: (PBL('i'), pvi)}, ps)
    st, out2 = stk_normalize(w, ps, mk, 'D', c[STKD('D')], bc.ne, [('K', XWV('i')), ('J', YWV('i')), ('I', SWV('i')), ('I', DV('I'))],
                             {XWV('i'): Si.vals['K'][2], YWV('i'): Si.vals['J'][2], SWV('i'): Si.vals['I'][2], DV('I'): bc.dsg('I')}, K4)
    assert out2 == [('K', XWV('i')), ('J', YWV('i'))], out2
    x2 = chain_text('D', out2)
    e12 = w.s([r1, st], 'eqtrd', '( %s -> %s = %s )' % (ps, DQ, x2))
    # P' ` ( i + 1 ) : its K and J equal those at i , its I is ( D ` I )
    pv1, S1 = bc.pv(I1, i1n)
    xw = lambda t, cte, tf: w.s([w.s([w.s([tf, cte], 'oveq12d', '( %s -> ( %s bwrd %s ) = ( %s bwrd %s ) )' % (ps, TOPX(CT(t)), CT(t), TOPX(NF), NF))], 'coeq2d',
                                     '( %s -> ( inclBool o. ( %s bwrd %s ) ) = ( inclBool o. ( %s bwrd %s ) ) )' % (ps, TOPX(CT(t)), CT(t), TOPX(NF), NF))], 'oveq1d',
                                '( %s -> %s = ( ( inclBool o. ( %s bwrd %s ) ) ++ %s ) )' % (ps, XWV(t), TOPX(NF), NF, YX('X')))
    XN = '( ( inclBool o. ( %s bwrd %s ) ) ++ %s )' % (TOPX(NF), NF, YX('X'))
    yw = lambda t, tf: w.s([w.s([w.s([tf], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` %s ) )' % (ps, TOPX(CT(t)), TOPX(NF)))], 'fveq2d',
                                '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( encNatGam ` ( bl ` %s ) ) )' % (ps, TOPX(CT(t)), TOPX(NF)))], 'oveq1d',
                           '( %s -> %s = %s )' % (ps, YWV(t), EW('( bl ` %s )' % TOPX(NF), DV('J'))))
    YN = EW('( bl ` %s )' % TOPX(NF), DV('J'))
    xi, x1_ = xw('i', ctin, tfi), xw(I1, ct1, tf1)
    yi, y1_ = yw('i', tfi), yw(I1, tf1)
    si1 = w.s([ni1], 'iffalsed', '( %s -> %s = %s )' % (ps, SWV(I1), DV('I')))
    ra, xa = w.rewrite(x2, {XWV('i'): (XN, xi), YWV('i'): (YN, yi)}, ps)
    rb, xb = w.rewrite(PBL(I1), {XWV(I1): (XN, x1_), YWV(I1): (YN, y1_), SWV(I1): (DV('I'), si1)}, ps)
    DJK = UP(UP('D', 'K', XN), 'J', YN)
    assert xa == DJK, xa
    assert xb == UP(DJK, 'I', DV('I')), xb
    dkn = updcl(w, ps, 'D', 'K', XN, mk['tv'], c[STKD('D')], mk['k']['K']['kd'], w.s([w.s([xi, Si.vals['K'][2]], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ps, XN)),
                                                                                    mk['k']['K']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, XN, GX('K'))))
    djk = updcl(w, ps, UP('D', 'K', XN), 'J', YN, mk['tv'], dkn, mk['k']['J']['kd'], w.s([w.s([yi, Si.vals['J'][2]], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ps, YN)),
                                                                                           mk['k']['J']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, YN, GX('J'))))
    # ( DJK ` I ) = ( D ` I )
    div = updnv(w, ps, UP('D', 'K', XN), 'J', YN, 'I', mk['tv'], dkn, mk['k']['J']['kd'], w.s([w.s([yi, Si.vals['J'][2]], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ps, YN))],
                                                                                            'elexd', '( %s -> %s e. _V )' % (ps, YN)), mk['k']['I']['kd'], bc.ne('I', 'J'))
    div2 = updnv(w, ps, 'D', 'K', XN, 'I', mk['tv'], c[STKD('D')], mk['k']['K']['kd'], w.s([w.s([xi, Si.vals['K'][2]], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ps, XN))],
                                                                                         'elexd', '( %s -> %s e. _V )' % (ps, XN)), mk['k']['I']['kd'], bc.ne('I', 'K'))
    dI = w.s([div, div2], 'eqtrd', '( %s -> ( %s ` I ) = ( D ` I ) )' % (ps, DJK))
    ui = upidv(w, ps, DJK, 'I', DV('I'), dI, mk['tv'], djk, mk['k']['I']['kd'])
    p1 = w.s([w.s([pv1, rb], 'eqtrd', '( %s -> %s = %s )' % (ps, PI1, UP(DJK, 'I', DV('I')))), ui], 'eqtrd', '( %s -> %s = %s )' % (ps, PI1, DJK))
    deq = w.s([w.s([e12, ra], 'eqtrd', '( %s -> %s = %s )' % (ps, DQ, DJK)), p1], 'eqtr4d', '( %s -> %s = %s )' % (ps, DQ, PI1))
    hrrw(w, ps, run.tri, run.C0, run.cur, run.n, deq=clneq(w, ps, LMB['L'], NI1, deq, DQ, PI1), qed=True)
    return w.run()


TBL = '( ( 2 x. ( # ` ( encodeNat ` %s ) ) ) + 6 )' % NF
GMB = {'A': LMB['L'], 'B0': LMB['B'], 'E': 'E', 'C0': CNCAR, 'R': '( %s + 1 )' % NF, "T'": TBL, 'N': NBF, 'P': PV}
_LA, _LC = split_imp(stmt('tm2floopu'))
LTREEB = tsub(parse_conj(_LA), GMB)
LCONCLB = tsub_text(_LC, GMB)
LTYPB, LPERB, LEXITB = LTREEB[1]
_pre = 'A. i e. ( 0 ..^ ( %s + 1 ) ) ' % NF
assert LPERB.startswith(_pre)
LBODYB = LPERB[len(_pre):]


def enclen_le(w, ps, bc, t, tn, tle):
    """( ps -> ( # ` ( encodeNat ` ( bl ` TOPX( t ) ) ) ) <_ ( # ` ( encodeNat ` NF ) ) ) for t e. NN0 , t <_ NF"""
    cl = bc.cl
    tp, dn, pn = bc.topn(t, tn, tle)
    TP_ = TOPX(t)
    P_ = '( 2 ^ ( %s - %s ) )' % (NF, t)
    X_ = '( F / %s )' % P_
    fr = w.s([bc.fn], 'nn0red', '( %s -> F e. RR )' % ps)
    prp = w.s([pn], 'nnrpd', '( %s -> %s e. RR+ )' % (ps, P_))
    fl = w.s([fr, prp, w.inst('fldivle')], 'syl2anc', '( %s -> %s <_ %s )' % (ps, TP_, X_))
    xr_ = w.s([fr, prp], 'rerpdivcld', '( %s -> %s e. RR )' % (ps, X_))
    pc = w.s([pn], 'nncnd', '( %s -> %s e. CC )' % (ps, P_))
    dc = w.s([w.s([fr], 'recnd', '( %s -> F e. CC )' % ps), pc, w.s([pn], 'nnne0d', '( %s -> %s =/= 0 )' % (ps, P_)), w.inst('divcan1')], 'syl3anc',
             '( %s -> ( %s x. %s ) = F )' % (ps, X_, P_))
    p1 = w.s([pn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ps, P_))
    x0 = w.s([w.s([bc.fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ps), prp], 'divge0d', '( %s -> 0 <_ %s )' % (ps, X_)) if False else \
        w.s([fr, w.s([bc.fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ps), prp], 'divge0d', '( %s -> 0 <_ %s )' % (ps, X_))
    cl2 = Closure(w, ps, {'F': ('NN0', bc.fn), P_: ('NN', pn), NF: ('NN0', bc.nfn)})
    cl2.atom(NF)
    cl2.leaf(X_, 'RR', xr_)
    xf = nlinarith(w, ps, [dc, p1, x0], '%s <_ F' % X_, closure=cl2, atoms=[X_, P_])
    lb = w.s([bc.fn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` F ) )' % (ps, NF))
    fp = w.s([bc.fn, w.inst('blpow2')], 'syl', '( %s -> F < ( 2 ^ ( bl ` F ) ) )' % ps)
    fp2 = w.s([fp, w.s([w.s([lb], 'eqcomd', '( %s -> ( bl ` F ) = %s )' % (ps, NF))], 'oveq2d', '( %s -> ( 2 ^ ( bl ` F ) ) = ( 2 ^ %s ) )' % (ps, NF))],
              'breqtrd', '( %s -> F < ( 2 ^ %s ) )' % (ps, NF))
    tlt = w.s([w.s([fl, xf], 'letrd', '( %s -> %s <_ F )' % (ps, TP_)), fp2], 'lelttrd', '( %s -> %s < ( 2 ^ %s ) )' % (ps, TP_, NF))
    b1 = w.s([tp, bc.nfn, tlt, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` %s ) <_ %s )' % (ps, TP_, NF))
    bn = w.s([tp, w.inst('blcl')], 'syl', '( %s -> ( bl ` %s ) e. NN0 )' % (ps, TP_))
    blnf = w.s([bc.nfn, w.inst('blcl')], 'syl', '( %s -> ( bl ` %s ) e. NN0 )' % (ps, NF))
    np_ = w.s([bc.nfn, w.inst('blpow2')], 'syl', '( %s -> %s < ( 2 ^ ( bl ` %s ) ) )' % (ps, NF, NF))
    b2 = w.s([bn, blnf, w.s([b1, np_], 'lelttrd', '( %s -> ( bl ` %s ) < ( 2 ^ ( bl ` %s ) ) )' % (ps, TP_, NF)), w.inst('blle')], 'syl3anc',
             '( %s -> ( bl ` ( bl ` %s ) ) <_ ( bl ` %s ) )' % (ps, TP_, NF))
    l1 = w.s([bn, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` ( encodeNat ` ( bl ` %s ) ) ) = ( bl ` ( bl ` %s ) ) )' % (ps, TP_, TP_))
    l2 = w.s([bc.nfn, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` ( encodeNat ` %s ) ) = ( bl ` %s ) )' % (ps, NF, NF))
    return w.s([w.s([l1, b2], 'eqbrtrd', '( %s -> ( # ` ( encodeNat ` ( bl ` %s ) ) ) <_ ( bl ` %s ) )' % (ps, TP_, NF)), l2], 'breqtrrd',
               '( %s -> ( # ` ( encodeNat ` ( bl ` %s ) ) ) <_ ( # ` ( encodeNat ` %s ) ) )' % (ps, TP_, NF))


def tmibli():
    lab = 'tmibli'
    ps = PSIB
    C = '( %s -> %s )' % (ps, LBODYB)
    w = W(lab, 'One iteration of Lean\'s ` bitlen ` loop at the machine ( ` blBody_runs ` at ` BlInv ` ): the test '
               '` !carry ` holds and the body goes from the invariant at ` i ` to the invariant at ` i + 1 ` within the '
               'uniform bound ` 2 # ( bl a ) + 6 ` (~ tmibls , ~ tmibl1 , ~ tmibl0 , ~ tmiblt ).')
    bc = Bc(w, ps)
    cl, mk = bc.cl, bc.mk
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ ( %s + 1 ) ) )' % (ps, NF))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    cl.leaf('i', 'NN0', inn)
    ilt1 = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < ( %s + 1 ) )' % (ps, NF))
    ile = w.s([ilt1, w.s([cl.mem('i', 'ZZ'), cl.mem(NF, 'ZZ'), w.inst('zleltp1')], 'syl2anc', '( %s -> ( i <_ %s <-> i < ( %s + 1 ) ) )' % (ps, NF, NF))],
              'mpbird', '( %s -> i <_ %s )' % (ps, NF))
    NI = '( %s ` i )' % NBF
    # HT
    pm = '( %s /\\ m e. %s )' % (ps, NI)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NBC, 'i', Lm(inn), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)))
    ca = w.s([mc, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = %s )' % (pm, CRV('i')))
    nl = w.s([ile, w.s([cl.mem('i', 'RR'), cl.mem(NF, 'RR')], 'lenltd', '( %s -> ( i <_ %s <-> -. %s < i ) )' % (ps, NF, NF))], 'mpbid', '( %s -> -. %s < i )' % (ps, NF))
    c0 = w.s([ca, Lm(w.s([nl], 'iffalsed', '( %s -> %s = (/) )' % (ps, CRV('i'))))], 'eqtrd', '( %s -> ( TMcar ` m ) = (/) )' % pm)
    X_of = lambda t: 'if ( ( TMcar ` %s ) = 1o , (/) , 1o )' % t
    xex = ifex_closed(w, pm, '( TMcar ` m ) = 1o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    htm = w.s([cv, w.s([not1o(w, pm, c0, 'TMcar', 'm')], 'iffalsed', '( %s -> %s = 1o )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CNCAR))
    ht = w.s([htm], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NI, CNCAR))
    TRIP = LBODYB[len('( A. m e. %s ( %s ` m ) = 1o /\\ ' % (NI, CNCAR)):-2]
    Ca, Da, _ = triple_parts(TRIP)
    efn = w.s([w.s([bc.nfn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` %s ) e. Word 2o )' % (ps, NF)), w.inst('lencl')], 'syl',
              '( %s -> ( # ` ( encodeNat ` %s ) ) e. NN0 )' % (ps, NF))
    # the bit case
    A1 = PSIL
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A1, concl(w, ps, st)))
    ts = w.s([], 'tmibls', '( %s -> %s )' % (A1, CONCL_S))
    phm1 = L1(mk['phm'])
    B1 = PSI1; B0 = PSI0
    LB1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (B1, concl(w, A1, st)))
    LB0 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (B0, concl(w, A1, st)))
    t1 = w.s([], 'tmibl1', '( %s -> %s )' % (B1, CONCL_1))
    t0 = w.s([], 'tmibl0', '( %s -> %s )' % (B0, CONCL_0))
    Cs, Ds, ns = triple_parts(CONCL_S)
    C1_, D1_, n1_ = triple_parts(CONCL_1)
    s1 = hrseq(w, B1, LB1(phm1), LB1(ts), t1, Cs, Ds, D1_, ns, n1_)
    s0 = hrseq(w, B0, LB0(phm1), LB0(ts), t0, Cs, Ds, D1_, ns, '( 1 + 1 )')
    # bounds
    cl1 = Closure(w, B1, {'( # ` ( encodeNat ` %s ) )' % NF: ('NN0', LB1(L1(efn)))})
    cti = w.s([L1(ile)], 'iftrued', '( %s -> %s = i )' % (A1, CT('i')))
    ctn, ctle = bc.ct('i', inn)
    el = enclen_le(w, ps, bc, CT('i'), ctn, ctle)
    ecn = w.s([w.s([w.s([bc.topn(CT('i'), ctn, ctle)[0], w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ps, CI_)), w.inst('encnatcl')], 'syl',
                   '( %s -> ( encodeNat ` %s ) e. Word 2o )' % (ps, CI_)), w.inst('lencl')], 'syl', '( %s -> ( # ` ( encodeNat ` %s ) ) e. NN0 )' % (ps, CI_))
    cl1.leaf('( # ` ( encodeNat ` %s ) )' % CI_, 'NN0', LB1(L1(ecn)))
    NS1 = '( %s + %s )' % (ns, n1_)
    le1 = linarith(w, B1, [LB1(L1(el))], '%s <_ %s' % (NS1, TBL), closure=cl1)
    h1 = hrle(w, B1, LB1(phm1), s1, Cs, D1_, NS1, TBL, cl1.mem(TBL, 'NN0'), le1)
    cl0 = Closure(w, B0, {'( # ` ( encodeNat ` %s ) )' % NF: ('NN0', LB0(L1(efn)))})
    NS0 = '( %s + ( 1 + 1 ) )' % ns
    le0 = linarith(w, B0, [cl0.ge0('( # ` ( encodeNat ` %s ) )' % NF)], '%s <_ %s' % (NS0, TBL), closure=cl0)
    h0 = hrle(w, B0, LB0(phm1), s0, Cs, D1_, NS0, TBL, cl0.mem(TBL, 'NN0'), le0)
    hb = w.s([h0, h1], 'pm2.61dan' if False else 'pm2.61dan', '') if False else None
    hb = w.s([w.s([h1], 'id', '') if False else h1, h0], 'pm2.61dan' if False else 'pm2.61dan', '') if False else None
    # pm2.61dan wants ( ( ph /\ ps ) -> ch ) and ( ( ph /\ -. ps ) -> ch ) : ps := T1 = 0
    hb = w.s([h0, h1], 'pm2.61dan', '( %s -> %s )' % (A1, TRIP))
    # the terminator case
    te = w.s([], 'tmiblt', '( %s -> %s )' % (PSIE, CONCL_E))
    LE = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (PSIE, concl(w, ps, st)))
    cle = Closure(w, PSIE, {'( # ` ( encodeNat ` %s ) )' % NF: ('NN0', LE(efn))})
    Ce, De, ne_ = triple_parts(CONCL_E)
    lee = linarith(w, PSIE, [cle.ge0('( # ` ( encodeNat ` %s ) )' % NF)], '%s <_ %s' % (ne_, TBL), closure=cle)
    he = hrle(w, PSIE, LE(mk['phm']), te, Ce, De, ne_, TBL, cle.mem(TBL, 'NN0'), lee)
    tr = w.s([hb, he], 'pm2.61dan', '( %s -> %s )' % (ps, TRIP))
    w.qed([ht, tr], 'jca', C)
    return w.run()


NPRO = '( ( ( ( 1 + ( ( # ` ( inclBool o. ( encodeNat ` F ) ) ) + 1 ) ) + 1 ) + 1 ) + 1 )'
PROB = TRI(CLN(LMB['A'], NPC, 'D'), CLN(LMB['L'], '( %s ` 0 )' % NBF, '( %s ` 0 )' % PV), NPRO)
NLOOP = triple_parts(LCONCLB)[2]
NF1 = '( %s + 1 )' % NF
CONCL_LL = TRI(CLN(LMB['A'], NPC, 'D'), CLN('E', '( %s ` %s )' % (NBF, NF1), '( %s ` %s )' % (PV, NF1)), '( %s + %s )' % (NPRO, NLOOP))


def tmiblg():
    lab = 'tmiblg'
    ps = PHB
    C = '( %s -> ( %s /\\ %s ) )' % (ps, LTYPB, LEXITB)
    w = W(lab, 'The frame of Lean\'s ` bitlen ` loop at the machine: the invariant\'s classes and stacks for '
               '` i <_ # a + 1 ` , and the test ` !carry ` failing after the terminator.')
    bc = Bc(w, ps)
    cl = bc.cl
    pt = '( %s /\\ i e. ( 0 ... %s ) )' % (ps, NF1)
    bt = Bc(w, pt)
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (pt, NF1))
    inn = w.s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    mem, _ = bt.pvals('i', inn)
    typ = w.s([w.s([bt.famss('i', inn), mem], 'jca', '( %s -> %s )' % (pt, LTYPB[len('A. i e. ( 0 ... %s ) ' % NF1):]))], 'ralrimiva', '( %s -> %s )' % (ps, LTYPB))
    NE = '( %s ` %s )' % (NBF, NF1)
    pm = '( %s /\\ m e. %s )' % (ps, NE)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    n1n = w.s([bc.nfn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF1))
    mm, mc = fam_unpack(w, pm, NBC, NF1, Lm(n1n), 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)))
    ca = w.s([mc, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` m ) = %s )' % (pm, CRV(NF1)))
    lt = linarith(w, ps, [], '%s < %s' % (NF, NF1), closure=cl)
    c1 = w.s([ca, Lm(w.s([lt], 'iftrued', '( %s -> %s = 1o )' % (ps, CRV(NF1))))], 'eqtrd', '( %s -> ( TMcar ` m ) = 1o )' % pm)
    X_of = lambda t: 'if ( ( TMcar ` %s ) = 1o , (/) , 1o )' % t
    xex = ifex_closed(w, pm, '( TMcar ` m ) = 1o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    c0 = w.s([cv, w.s([c1], 'iftrued', '( %s -> %s = (/) )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CNCAR))
    ex_ = w.s([not1o(w, pm, c0, CNCAR, 'm')], 'ralrimiva', '( %s -> %s )' % (ps, LEXITB))
    w.qed([typ, ex_], 'jca', C)
    return w.run()


def tmibll():
    lab = 'tmibll'
    ps = PHB
    C = '( %s -> %s )' % (ps, CONCL_LL)
    w = W(lab, 'Lean\'s ` bitlen x y s s\' ` at the machine (the loop form, ` bitlen_runs ` ): the prologue (~ tmiblp ) '
               'and ~ tm2floopu at the families of ` BlInv ` ( ~ tmibli , ~ tmiblg ) over ` # a + 1 ` iterations.')
    bc = Bc(w, ps)
    cl, mk = bc.cl, bc.mk
    ex = dict(bc.base)
    b01 = w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', 'if ( ( TMcar ` u ) = 1o , (/) , 1o ) e. 2o')
    ex[CTY(CNCAR)] = lamty(w, ps, mk, CNCAR, lambda t: 'if ( ( TMcar ` %s ) = 1o , (/) , 1o )' % t, '2o', w.s([], '2oex', '2o e. _V'), b01)
    n1n = w.s([bc.nfn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF1))
    ex['%s e. NN0' % NF1] = n1n
    efn = w.s([w.s([bc.nfn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` %s ) e. Word 2o )' % (ps, NF)), w.inst('lencl')], 'syl',
              '( %s -> ( # ` ( encodeNat ` %s ) ) e. NN0 )' % (ps, NF))
    cl.leaf('( # ` ( encodeNat ` %s ) )' % NF, 'NN0', efn)
    ex['%s e. NN0' % TBL] = cl.mem(TBL, 'NN0')
    tg = w.s([], 'tmiblg', '( %s -> ( %s /\\ %s ) )' % (ps, LTYPB, LEXITB))
    ex[LTYPB] = w.s([tg], 'simpld', '( %s -> %s )' % (ps, LTYPB))
    ex[LEXITB] = w.s([tg], 'simprd', '( %s -> %s )' % (ps, LEXITB))
    ex[LPERB] = w.s([w.s([], 'tmibli', '( %s -> %s )' % (PSIB, LBODYB))], 'ralrimiva', '( %s -> %s )' % (ps, LPERB))
    st = Bld(w, ps, bc.c, ex)(LTREEB)
    lp = w.s([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ps, LCONCLB))
    pro = w.s([], 'tmiblp', '( %s -> %s )' % (ps, PROB))
    w.qed([mk['phm'], pro, lp], 'syl3anc', C)
    return w.run()


T_RB = ((T_PHM7, BLF.pred()), (idx_tree(K4), dist_tree(K4)), (('F e. NN0', WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % EW('F', 'X')))
EWB = EW('( bl ` F )', '( D ` J )')
DFINB = UP('D', 'J', EWB)
NTOT = '( %s + %s )' % (NPRO, NLOOP)
CONCL_RB = TRI(CLN(LMB['A'], NPC, 'D'), CLN('E', SS, DFINB), NTOT)


def tmiblr():
    lab = 'tmiblr'
    ps = cj(T_RB)
    C = '( %s -> %s )' % (ps, CONCL_RB)
    w = W(lab, 'Lean\'s ` bitlen_runs ` at the machine with ` cmp ` pinned: from the states of a pinned register class '
               'the machine reaches the exit with ` bl a ` pushed on ` y ` and every other stack restored (~ tmibll at its '
               'stack family, evaluated after the last iteration).')
    c = Ctx(w, ps, T_RB)
    eq = closed(w, ps, 'eqid', '%s = %s' % (PDFB, PDFB))
    TL2 = tsub(T_BL, {PV: PDFB})
    root = Bld(w, ps, c, {'%s = %s' % (PDFB, PDFB): eq})(TL2)
    bc = Bc(w, ps, tree=TL2, root=root, pv=PDFB)
    cl, mk = bc.cl, bc.mk
    t, cc = inst(w, ps, 'tmibll', {PV: PDFB}, Bld(w, ps, bc.c, {'%s = %s' % (PDFB, PDFB): eq}))
    Ca, Da, n = triple_parts(cc)
    n1n = w.s([bc.nfn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF1))
    pvF, SF = bc.pv(NF1, n1n)
    nlt1 = linarith(w, ps, [], '%s < %s' % (NF, NF1), closure=cl)
    ni1 = w.s([nlt1, w.s([cl.mem(NF, 'RR'), cl.mem(NF1, 'RR')], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (ps, NF, NF1, NF1, NF))], 'mpbid',
              '( %s -> -. %s <_ %s )' % (ps, NF1, NF))
    ct1 = w.s([ni1], 'iffalsed', '( %s -> %s = %s )' % (ps, CT(NF1), NF))
    tf = topfix(w, ps, ct1, NF1)
    nn0_ = w.s([cl.mem(NF, 'CC')], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (ps, NF, NF))
    e0 = w.s([closed(w, ps, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % ps)
    p0 = w.s([w.s([nn0_], 'oveq2d', '( %s -> ( 2 ^ ( %s - %s ) ) = ( 2 ^ 0 ) )' % (ps, NF, NF)), e0], 'eqtrd', '( %s -> ( 2 ^ ( %s - %s ) ) = 1 )' % (ps, NF, NF))
    fc = w.s([bc.fn], 'nn0cnd', '( %s -> F e. CC )' % ps)
    d1 = w.s([w.s([p0], 'oveq2d', '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = ( F / 1 ) )' % (ps, NF, NF)), w.s([fc, w.inst('div1')], 'syl', '( %s -> ( F / 1 ) = F )' % ps)],
             'eqtrd', '( %s -> ( F / ( 2 ^ ( %s - %s ) ) ) = F )' % (ps, NF, NF))
    tfF = w.s([w.s([d1], 'fveq2d', '( %s -> %s = ( |_ ` F ) )' % (ps, TOPX(NF))), w.s([w.s([bc.fn], 'nn0zd', '( %s -> F e. ZZ )' % ps), w.inst('flid')], 'syl',
                                                                                     '( %s -> ( |_ ` F ) = F )' % ps)], 'eqtrd', '( %s -> %s = F )' % (ps, TOPX(NF)))
    tF = w.s([tf, tfF], 'eqtrd', '( %s -> %s = F )' % (ps, TOPX(CT(NF1))))
    lb = w.s([bc.fn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` F ) )' % (ps, NF))
    eb = w.s([w.s([bc.fn, w.inst('encnatbwrd')], 'syl', '( %s -> %s = ( F bwrd ( bl ` F ) ) )' % (ps, ENCF)),
              w.s([w.s([lb], 'eqcomd', '( %s -> ( bl ` F ) = %s )' % (ps, NF))], 'oveq2d', '( %s -> ( F bwrd ( bl ` F ) ) = ( F bwrd %s ) )' % (ps, NF))],
             'eqtrd', '( %s -> %s = ( F bwrd %s ) )' % (ps, ENCF, NF))
    bw = w.s([w.s([tF, ct1], 'oveq12d', '( %s -> ( %s bwrd %s ) = ( F bwrd %s ) )' % (ps, TOPX(CT(NF1)), CT(NF1), NF)), eb], 'eqtr4d',
             '( %s -> ( %s bwrd %s ) = %s )' % (ps, TOPX(CT(NF1)), CT(NF1), ENCF))
    gv = w.s([bc.fn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = ( inclBool o. %s ) )' % (ps, ENCF))
    xw = w.s([w.s([w.s([bw], 'coeq2d', '( %s -> ( inclBool o. ( %s bwrd %s ) ) = ( inclBool o. %s ) )' % (ps, TOPX(CT(NF1)), CT(NF1), ENCF)),
                   w.s([gv], 'eqcomd', '( %s -> ( inclBool o. %s ) = ( encNatGam ` F ) )' % (ps, ENCF))], 'eqtrd',
                  '( %s -> ( inclBool o. ( %s bwrd %s ) ) = ( encNatGam ` F ) )' % (ps, TOPX(CT(NF1)), CT(NF1)))], 'oveq1d', '( %s -> %s = %s )' % (ps, XWV(NF1), EW('F', 'X')))
    yw = w.s([w.s([w.s([tF], 'fveq2d', '( %s -> ( bl ` %s ) = ( bl ` F ) )' % (ps, TOPX(CT(NF1))))], 'fveq2d',
                  '( %s -> ( encNatGam ` ( bl ` %s ) ) = ( encNatGam ` ( bl ` F ) ) )' % (ps, TOPX(CT(NF1))))], 'oveq1d', '( %s -> %s = %s )' % (ps, YWV(NF1), EWB))
    sw = w.s([ni1], 'iffalsed', '( %s -> %s = ( D ` I ) )' % (ps, SWV(NF1)))
    r1, x1 = w.rewrite(PBL(NF1), {XWV(NF1): (EW('F', 'X'), xw), YWV(NF1): (EWB, yw), SWV(NF1): ('( D ` I )', sw)}, ps)
    DK = UP('D', 'K', EW('F', 'X'))
    assert x1 == UP(UP(DK, 'J', EWB), 'I', '( D ` I )'), x1
    dd = bc.c[STKD('D')]
    uk = upidv(w, ps, 'D', 'K', EW('F', 'X'), bc.c['( D ` K ) = %s' % EW('F', 'X')], mk['tv'], dd, mk['k']['K']['kd'])
    r2, x2 = w.rewrite(x1, {DK: ('D', uk)}, ps)
    DJ_ = UP('D', 'J', EWB)
    blfn = w.s([bc.fn, w.inst('blcl')], 'syl', '( %s -> ( bl ` F ) e. NN0 )' % ps)
    ewbg = ewg(w, ps, '( bl ` F )', blfn, '( D ` J )', bc.dsg('J'))
    djc = updcl(w, ps, 'D', 'J', EWB, mk['tv'], dd, mk['k']['J']['kd'], w.s([ewbg, mk['k']['J']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, EWB, GX('J'))))
    di = updnv(w, ps, 'D', 'J', EWB, 'I', mk['tv'], dd, mk['k']['J']['kd'], w.s([ewbg], 'elexd', '( %s -> %s e. _V )' % (ps, EWB)), mk['k']['I']['kd'], bc.ne('I', 'J'))
    ui = upidv(w, ps, DJ_, 'I', '( D ` I )', di, mk['tv'], djc, mk['k']['I']['kd'])
    pF = w.s([w.s([w.s([pvF, r1], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PDFB, NF1, x1)), r2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PDFB, NF1, x2)), ui],
             'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PDFB, NF1, DFINB))
    NE = '( %s ` %s )' % (NBF, NF1)
    d_ = clneq(w, ps, 'E', NE, pF, '( %s ` %s )' % (PDFB, NF1), DFINB)
    t2, C2, D2, n2 = hrrw(w, ps, t, Ca, Da, n, deq=d_)
    ss = clnss(w, ps, 'E', NE, SS, DFINB, bc.famss(NF1, n1n))
    ssS = closed(w, ps, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    cf = cfgcl(w, ps, 'E', SS, DFINB, mk['tv'], bc.base['E e. ( 2nd ` ( 1st ` T ) )'], ssS, djc)
    t3 = hrssd(w, ps, mk['phm'], t2, C2, D2, n2, CLN('E', SS, DFINB), ss, cf)
    w.lines[-1] = w.lines[-1].replace(t3 + ':', 'qed:', 1)
    return w.run()


CONCL_CB = TRI(CLN(LMB['A'], SS, 'D'), CLN('E', SS, DFINB), NTOT)
T_BB = ((T_PHM7, BLF.pred()), (idx_tree(K4), dist_tree(K4)),
        ((('F e. NN0', 'N e. NN0', 'F < ( 2 ^ N )'), (WRD('X', GAM), STKD('D'))), '( D ` K ) = %s' % EW('F', 'X')))
CONCL_BB = TRI(CLN(LMB['A'], SS, 'D'), CLN('E', SS, DFINB), '( TMB ` N )')


def tmiblc():
    lab = 'tmiblc'
    ps = cj(T_RB)
    C = '( %s -> %s )' % (ps, CONCL_CB)
    w = W(lab, 'Lean\'s ` bitlen_correct ` at the machine: wherever ` bitlen x y s s\' ` is installed, from any state with '
               '` a ` on ` x ` the machine pushes ` bl a ` on ` y ` and restores every other stack (~ tmiblr for every pinned '
               'register value, ~ tmchiun ).')
    c = Ctx(w, ps, T_RB)
    mk = machine(w, ps, c, K4)
    XMX = {'O': '( TMfl ` x )', 'Q': '( TMcmp ` x )', 'R': '( TMcar ` x )'}
    t = w.s([], 'tmiblr', '( %s -> %s )' % (ps, tsub_text(CONCL_RB, XMX)))
    fn = c['F e. NN0']
    efw = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF))
    nfn = w.s([efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF))
    cl = Closure(w, ps, {'F': ('NN0', fn), NF: ('NN0', nfn)})
    cl.atom(NF)
    ibw = w.s([efw, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = %s )' % (ps, ENCF, NF))
    cl.leaf('( # ` ( inclBool o. %s ) )' % ENCF, 'NN0', w.s([ibw, nfn], 'eqeltrd', '( %s -> ( # ` ( inclBool o. %s ) ) e. NN0 )' % (ps, ENCF)))
    cl.leaf('( # ` ( encodeNat ` %s ) )' % NF, 'NN0', w.s([w.s([nfn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` %s ) e. Word 2o )' % (ps, NF)), w.inst('lencl')],
                                                        'syl', '( %s -> ( # ` ( encodeNat ` %s ) ) e. NN0 )' % (ps, NF)))
    nn0 = cl.mem(NTOT, 'NN0')
    dd = c[STKD('D')]
    blfn = w.s([fn, w.inst('blcl')], 'syl', '( %s -> ( bl ` F ) e. NN0 )' % ps)
    dj = w.s([stkfv(w, ps, 'D', 'J', mk['tv'], dd, mk['k']['J']['kd']), mk['k']['J']['wge']], 'eleqtrd', "( %s -> ( D ` J ) e. Word Gamma' )" % ps)
    ewbg = ewg(w, ps, '( bl ` F )', blfn, '( D ` J )', dj)
    djc = updcl(w, ps, 'D', 'J', EWB, mk['tv'], dd, mk['k']['J']['kd'], w.s([ewbg, mk['k']['J']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, EWB, GX('J'))))
    un = unfold_all(w, ps, c[BLF.pred()], 'bl', K4, 'P', 'E', rec=False)
    ssS = closed(w, ps, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    cf = cfgcl(w, ps, 'E', SS, DFINB, mk['tv'], un['E e. ( 2nd ` ( 1st ` T ) )'], ssS, djc)
    from t7b_e_froms import union_from_S
    union_from_S(w, ps, c, mk, t, CLN('E', SS, DFINB), NTOT, nn0, cf)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


def tmiblb():
    lab = 'tmiblb'
    ps = cj(T_BB)
    C = '( %s -> %s )' % (ps, CONCL_BB)
    w = W(lab, 'Lean\'s ` bitlen_le_B ` at the machine: ` bitlen x y s s\' ` on ` a < 2 ^ b ` runs within ` B b ` steps '
               '(~ tmiblc ).')
    c = Ctx(w, ps, T_BB)
    phm = c[PHM]
    t, cc = inst(w, ps, 'tmiblc', {}, Bld(w, ps, c, {}))
    Ca, Da, n = triple_parts(cc)
    fn, nn = c['F e. NN0'], c['N e. NN0']
    efw = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ENCF))
    nfn = w.s([efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF))
    L2 = '( # ` ( encodeNat ` %s ) )' % NF
    l2n = w.s([w.s([nfn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` %s ) e. Word 2o )' % (ps, NF)), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, L2))
    cl = Closure(w, ps, {'F': ('NN0', fn), 'N': ('NN0', nn), NF: ('NN0', nfn), L2: ('NN0', l2n)})
    cl.atom(NF); cl.atom(L2)
    WL = '( # ` ( inclBool o. %s ) )' % ENCF
    ibw = w.s([efw, w.inst('bwmaplen')], 'syl', '( %s -> %s = %s )' % (ps, WL, NF))
    cl.leaf(WL, 'NN0', w.s([ibw, nfn], 'eqeltrd', '( %s -> %s e. NN0 )' % (ps, WL)))
    nfN = w.s([fn, nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ps, NF))
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    np_ = w.s([w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ps), nfn, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ps, NF, NF))
    l2l = w.s([nfn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` %s ) )' % (ps, L2, NF))
    bll = w.s([nfn, nfn, np_, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` %s ) <_ %s )' % (ps, NF, NF))
    l2le = w.s([l2l, bll], 'eqbrtrd', '( %s -> %s <_ %s )' % (ps, L2, NF))
    Q_ = '( 4 x. ( ( N + 2 ) ^ 2 ) )'
    le1 = nlinarith(w, ps, [ibw, l2le, nfN, cl.ge0(NF), cl.ge0(L2), cl.ge0('N')], '%s <_ %s' % (n, Q_), closure=cl, atoms=[NF, L2, 'N', WL])
    import num
    l64 = w.s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ps)
    qd = w.s([nn, closed(w, ps, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc', '( %s -> %s <_ ( TMB ` N ) )' % (ps, Q_))
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ps)], 'nnnn0d', '( %s -> ( TMB ` N ) e. NN0 )' % ps)
    le = w.s([le1, qd], 'letrd', '( %s -> %s <_ ( TMB ` N ) )' % (ps, n))
    hrle(w, ps, phm, t, Ca, Da, n, '( TMB ` N )', tbn, le, qed=True)
    return w.run()


STMTS = {'tmibltop': ST_TOP, 'tmiblst': ST_BLST, 'tmiblw1': ST_W1, 'tmiblw2': ST_W2, 'tmiblit': ST_IT}
STMTS['tmiblc'] = '( %s -> %s )' % (cj(T_RB), CONCL_CB)
STMTS['tmiblb'] = '( %s -> %s )' % (cj(T_BB), CONCL_BB)
STMTS['tmiblr'] = '( %s -> %s )' % (cj(T_RB), CONCL_RB)
STMTS['tmiblp'] = '( %s -> %s )' % (PHB, PROB)
STMTS['tmiblg'] = '( %s -> ( %s /\\ %s ) )' % (PHB, LTYPB, LEXITB)
STMTS['tmibll'] = '( %s -> %s )' % (PHB, CONCL_LL)
STMTS['tmibli'] = '( %s -> %s )' % (PSIB, LBODYB)
STMTS['tmiblt'] = '( %s -> %s )' % (PSIE, CONCL_E)
STMTS['tmibls'] = '( %s -> %s )' % (PSIL, CONCL_S)
STMTS['tmibl1'] = '( %s -> %s )' % (PSI1, CONCL_1)
STMTS['tmibl0'] = '( %s -> %s )' % (PSI0, CONCL_0)

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
