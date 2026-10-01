"""T8b: the arithmetic and the sequences of the DP step (Lean ` res_pred ` , ` accSeq ` ,
` dpGo_accSeq ` , ` dpStep_eq_accSeq ` , ` tblBounded_setIfNone ` , ` tblBounded_accSeq ` ).

  ttrespred  ( r p ) mod L from ( ( r + 1 ) p ) mod L by one modular subtraction of p mod L
  tttbbset   the guarded write keeps TblBounded
  ttrrs      the residue words RR_i of dpStepF's loop: typing, value ( ( L - i ) p ) mod L , length <_ B
  ttaccs     the accumulators ACC_i: tables, TblBounded at N + 1 , and 1st ( dpGo ) invariance
  ttaccl     ACC_L is the DP step's table

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_l_seq.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, lineq, nlinarith
from t8b_e_sin import L_

SEL = sys.argv[1:]
NONE_ = '( inr ` (/) )'
R1F = '( ( ( R + 1 ) x. F ) mod L )'
FL = '( F mod L )'
RF = '( ( R x. F ) mod L )'
PH_RP = '( L e. NN /\\ F e. NN0 /\\ R e. NN0 )'
ST_RP = '( %s -> %s = if ( %s <_ %s , ( %s - %s ) , ( L - ( %s - %s ) ) ) )' % (PH_RP, RF, FL, R1F, R1F, FL, FL, R1F)


def ttrespred():
    ph = PH_RP
    w = W('ttrespred', 'The residue recursion of the DP step: ` ( r p ) mod L ` from ` ( ( r + 1 ) p ) mod L ` by one '
                       'modular subtraction of ` p mod L ` (Lean ` res_pred ` ).')
    s = w.s
    ln = s([], 'simp1', '( %s -> L e. NN )' % ph)
    fn = s([], 'simp2', '( %s -> F e. NN0 )' % ph)
    rn = s([], 'simp3', '( %s -> R e. NN0 )' % ph)
    lp = s([ln, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % ph)
    cl = Closure(w, ph, {'L': ('NN', ln), 'F': ('NN0', fn), 'R': ('NN0', rn)})
    rfr = cl.mem('( R x. F )', 'RR')
    fr = cl.mem('F', 'RR')
    a_n = s([cl.mem('( R x. F )', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, RF))
    q_n = s([cl.mem('F', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FL))
    a_l = s([rfr, lp, w.inst('modlt')], 'syl2anc', '( %s -> %s < L )' % (ph, RF))
    q_l = s([fr, lp, w.inst('modlt')], 'syl2anc', '( %s -> %s < L )' % (ph, FL))
    cl.leaf(RF, 'NN0', a_n); cl.leaf(FL, 'NN0', q_n)
    e1 = lineq(w, ph, '( ( R + 1 ) x. F )', '( ( R x. F ) + F )', closure=cl, products=True)
    e2 = s([s([e1], 'oveq1d', '( %s -> %s = ( ( ( R x. F ) + F ) mod L ) )' % (ph, R1F))], 'id', '') if False else \
        s([e1], 'oveq1d', '( %s -> %s = ( ( ( R x. F ) + F ) mod L ) )' % (ph, R1F))
    e3 = s([rfr, fr, lp, w.inst('modaddabs')], 'syl3anc', '( %s -> ( ( %s + %s ) mod L ) = ( ( ( R x. F ) + F ) mod L ) )' % (ph, RF, FL))
    AQ = '( %s + %s )' % (RF, FL)
    e4 = s([e2, e3], 'eqtr4d', '( %s -> %s = ( %s mod L ) )' % (ph, R1F, AQ))
    GOAL = lambda p: '( %s -> %s = if ( %s <_ %s , ( %s - %s ) , ( L - ( %s - %s ) ) ) )' % (p, RF, FL, R1F, R1F, FL, FL, R1F)
    C = '%s < L' % AQ
    # case a + q < L
    p1 = '( %s /\\ %s )' % (ph, C)
    L1 = lambda st: L_(w, p1, ph, st)
    c1 = s([], 'simpr', '( %s -> %s )' % (p1, C))
    cl1 = Closure(w, p1, {'L': ('NN', L1(ln))})
    cl1.leaf(RF, 'NN0', L1(a_n)); cl1.leaf(FL, 'NN0', L1(q_n))
    md = s([s([cl1.mem(AQ, 'RR'), L1(lp)], 'jca', '( %s -> ( %s e. RR /\\ L e. RR+ ) )' % (p1, AQ)),
            s([cl1.ge0(AQ), c1], 'jca', '( %s -> ( 0 <_ %s /\\ %s ) )' % (p1, AQ, C)), w.inst('modid')], 'syl2anc', '( %s -> ( %s mod L ) = %s )' % (p1, AQ, AQ))
    r1 = s([L1(e4), md], 'eqtrd', '( %s -> %s = %s )' % (p1, R1F, AQ))
    cl1.leaf(R1F, 'NN0', L1(s([cl.mem('( ( R + 1 ) x. F )', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, R1F))))
    le1 = linarith(w, p1, [r1, cl1.ge0(RF)], '%s <_ %s' % (FL, R1F), closure=cl1)
    v1 = s([le1], 'iftrued', '( %s -> if ( %s <_ %s , ( %s - %s ) , ( L - ( %s - %s ) ) ) = ( %s - %s ) )' % (p1, FL, R1F, R1F, FL, FL, R1F, R1F, FL))
    v1b = lineq(w, p1, '( %s - %s )' % (R1F, FL), RF, hyps=[r1], closure=cl1)
    o1 = s([s([v1, v1b], 'eqtrd', '( %s -> if ( %s <_ %s , ( %s - %s ) , ( L - ( %s - %s ) ) ) = %s )' % (p1, FL, R1F, R1F, FL, FL, R1F, RF))], 'eqcomd', GOAL(p1))
    # case L <_ a + q
    p2 = '( %s /\\ -. %s )' % (ph, C)
    L2 = lambda st: L_(w, p2, ph, st)
    c2 = s([], 'simpr', '( %s -> -. %s )' % (p2, C))
    cl2 = Closure(w, p2, {'L': ('NN', L2(ln))})
    cl2.leaf(RF, 'NN0', L2(a_n)); cl2.leaf(FL, 'NN0', L2(q_n))
    ge = s([s([cl2.mem('L', 'RR'), cl2.mem(AQ, 'RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( L <_ %s <-> -. %s ) )' % (p2, AQ, C)), c2], 'mpbird',
           '( %s -> L <_ %s )' % (p2, AQ))
    AQL = '( %s - ( L x. 1 ) )' % AQ
    cy = s([cl2.mem(AQ, 'RR'), L2(lp), closed(w, p2, '1z', '1 e. ZZ'), w.inst('modcyc2')], 'syl3anc', '( %s -> ( %s mod L ) = ( %s mod L ) )' % (p2, AQL, AQ))
    q0 = linarith(w, p2, [ge], '0 <_ %s' % AQL, closure=cl2)
    ql = linarith(w, p2, [L2(a_l), L2(q_l)], '%s < L' % AQL, closure=cl2)
    md2 = s([s([cl2.mem(AQL, 'RR'), L2(lp)], 'jca', '( %s -> ( %s e. RR /\\ L e. RR+ ) )' % (p2, AQL)), s([q0, ql], 'jca', '( %s -> ( 0 <_ %s /\\ %s < L ) )' % (p2, AQL, AQL)),
             w.inst('modid')], 'syl2anc', '( %s -> ( %s mod L ) = %s )' % (p2, AQL, AQL))
    r2 = s([s([L2(e4), cy], 'eqtr4d', '( %s -> %s = ( %s mod L ) )' % (p2, R1F, AQL)), md2], 'eqtrd', '( %s -> %s = %s )' % (p2, R1F, AQL))
    cl2.leaf(R1F, 'NN0', L2(s([cl.mem('( ( R + 1 ) x. F )', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, R1F))))
    nle = linarith(w, p2, [r2, L2(a_l)], '%s < %s' % (R1F, FL), closure=cl2)
    nl2 = s([s([cl2.mem(R1F, 'RR'), cl2.mem(FL, 'RR'), w.inst('ltnle')], 'syl2anc', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (p2, R1F, FL, FL, R1F)), nle],
            'mpbid', '( %s -> -. %s <_ %s )' % (p2, FL, R1F))
    v2 = s([nl2], 'iffalsed', '( %s -> if ( %s <_ %s , ( %s - %s ) , ( L - ( %s - %s ) ) ) = ( L - ( %s - %s ) ) )' % (p2, FL, R1F, R1F, FL, FL, R1F, FL, R1F))
    v2b = lineq(w, p2, '( L - ( %s - %s ) )' % (FL, R1F), RF, hyps=[r2], closure=cl2)
    o2 = s([s([v2, v2b], 'eqtrd', '( %s -> if ( %s <_ %s , ( %s - %s ) , ( L - ( %s - %s ) ) ) = %s )' % (p2, FL, R1F, R1F, FL, FL, R1F, RF))], 'eqcomd', GOAL(p2))
    w.qed([o1, o2], 'pm2.61dan', ST_RP)
    return w.run()


PH_RR = '( ( L e. NN /\\ F e. NN0 /\\ B e. NN0 ) /\\ ( F < ( 2 ^ B ) /\\ L < ( 2 ^ B ) ) )'
QR = lambda t: '( %s e. Word 2o /\\ ( toNat ` %s ) = ( ( ( L - %s ) x. F ) mod L ) /\\ ( # ` %s ) <_ B )' % (RRS(t), RRS(t), t, RRS(t))
ST_RR = '( ( %s /\\ I e. ( 0 ... L ) ) -> %s )' % (PH_RR, QR('I'))
NFE_ = '( # ` ( encodeNat ` F ) )'


def seq_step(w, a, OP, G, Xof, t, tn, xv, gv, val):
    """( a -> ( seq ` ( t + 1 ) ) = val ) where OP = ( x e. _V , y e. _V |-> X( x , y ) ): seqp1 and ovmpog"""
    s = w.s
    SQ = lambda u: '( seq 0 ( %s , %s ) ` %s )' % (OP, G, u)
    uz = s([tn, w.inst('elnn0uz')], 'sylib', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (a, t))
    sp = s([uz, w.inst('seqp1')], 'syl', '( %s -> %s = ( %s %s ( %s ` ( %s + 1 ) ) ) )' % (a, SQ('( %s + 1 )' % t), SQ(t), OP, G, t))
    A_, B_ = SQ(t), '( %s ` ( %s + 1 ) )' % (G, t)
    h1, n1 = w.congr(Xof('x', 'y'), {'x': A_}, 'x = %s' % A_, {'x': s([], 'id', '( x = %s -> x = %s )' % (A_, A_))})
    h2, n2 = w.congr(n1, {'y': B_}, 'y = %s' % B_, {'y': s([], 'id', '( y = %s -> y = %s )' % (B_, B_))})
    if h2 is None:
        h2 = s([], 'eqidd', '( y = %s -> %s = %s )' % (B_, n1, n1)); n2 = n1
    if h1 is None:
        h1 = s([], 'eqidd', '( x = %s -> %s = %s )' % (A_, Xof('x', 'y'), Xof('x', 'y')))
    assert n2 == val, (n2, val)
    df = s([], 'eqid', '%s = %s' % (OP, OP))
    ov = s([h1, h2, df], 'ovmpog', '( ( %s e. _V /\\ %s e. _V /\\ %s e. _V ) -> ( %s %s %s ) = %s )' % (A_, B_, val, A_, OP, B_, val))
    o = s([xv, gv, s([], 'id', '') if False else val_ex(w, a, val), ov], 'syl3anc', '( %s -> ( %s %s %s ) = %s )' % (a, A_, OP, B_, val))
    return s([sp, o], 'eqtrd', '( %s -> %s = %s )' % (a, SQ('( %s + 1 )' % t), val))


_VEX = {}


def val_ex(w, a, val):
    return _VEX[(a, val)]


def ttrrs():
    ph = PH_RR
    w = W('ttrrs', 'The residue words of Lean\'s ` dpStepF ` loop: the ` i ` -th iterate of ` resStep ` \'s word from the empty '
                   'word, with ` p mod L ` as ` q ` and ` L ` as ` encodeNat L ` , is a bit word of value '
                   '` ( ( L - i ) p ) mod L ` and length at most ` b ` (Lean ` DpInv ` \'s ` rl ` , ` res_pred ` ).')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    ln, fn, bn = c['L e. NN'], c['F e. NN0'], c['B e. NN0']
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    lp = s([ln, w.inst('nnrp')], 'syl', '( %s -> L e. RR+ )' % ph)
    cl = Closure(w, ph, {'L': ('NN', ln), 'F': ('NN0', fn), 'B': ('NN0', bn)})
    # PLW facts
    FM = '( F mod L )'
    fmn = s([cl.mem('F', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FM))
    cl.leaf(FM, 'NN0', fmn)
    ef = s([fn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    nfe = s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NFE_))
    cl.leaf(NFE_, 'NN0', nfe)
    tl = s([s([ef, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ph, NFE_)),
            s([fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)], 'eqbrtrrd' if False else 'id', '') if False else None
    tfe = s([fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ph)
    tl = s([tfe, s([ef, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ph, NFE_))], 'eqbrtrrd',
           '( %s -> F < ( 2 ^ %s ) )' % (ph, NFE_))
    fml = s([cl.mem('F', 'ZZ'), lp, w.inst('modle' if False else 'id')], 'id', '') if False else None
    fq = '( |_ ` ( F / L ) )'
    fqn = s([fn, ln, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, fq))
    cl.leaf(fq, 'NN0', fqn)
    mv = s([s([fn], 'nn0red', '( %s -> F e. RR )' % ph), lp, w.inst('modvalr')], 'syl2anc', '( %s -> %s = ( F - ( %s x. L ) ) )' % (ph, FM, fq))
    mle = nlinarith(w, ph, [mv, cl.ge0(fq), cl.ge0('L')], '%s <_ F' % FM, closure=cl, atoms=[fq, FM])
    P2 = '( 2 ^ %s )' % NFE_
    p2n = s([closed(w, ph, '2nn0', '2 e. NN0'), nfe, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, P2))
    cl.leaf(P2, 'NN0', p2n)
    fm2 = linarith(w, ph, [mle, tl], '%s < %s' % (FM, P2), closure=cl)
    tpl = s([fmn, nfe, fm2, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ph, PLW, FM))
    plw = s([s([fmn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, FM)), nfe, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, PLW))
    pll = s([s([s([fmn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, FM)), nfe, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, PLW, NFE_)),
             s([fn, bn, c['F < ( 2 ^ B )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ B )' % (ph, NFE_))], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (ph, PLW))
    fml2 = s([s([fn], 'nn0red', '( %s -> F e. RR )' % ph), lp, w.inst('modlt')], 'syl2anc', '( %s -> %s < L )' % (ph, FM))
    tpll = s([tpl, fml2], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (ph, PLW))
    ell = s([l0, bn, c['L < ( 2 ^ B )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` %s ) <_ B )' % (ph, ELW))
    # the induction
    PS = lambda t: '( %s <_ L -> %s )' % (t, QR(t))
    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    # base
    s0 = s([closed(w, ph, '0z', '0 e. ZZ'), w.inst('seq1')], 'syl', '( %s -> %s = ( %s ` 0 ) )' % (ph, RRS('0'), G1R))
    g0 = s([closed(w, ph, '0nn0', '0 e. NN0'), s([], 'eqid', '%s = %s' % (G1R, G1R)) if False else None], 'id', '') if False else None
    X0 = lambda t: 'if ( %s = 0 , (/) , %s )' % (t, t)
    from t7lib import mval
    gv0 = mval(w, ph, 'k', 'NN0', X0, '0', closed(w, ph, '0nn0', '0 e. NN0'),
               s([s([], 'ifex' if False else 'id', '') if False else closed(w, ph, '0ex', '(/) e. _V')], 'id', '') if False else
               ifexv(w, ph, '0 = 0', '(/)', '0'))
    i0 = s([s([], 'eqidd', '( %s -> 0 = 0 )' % ph)], 'iftrued', '( %s -> if ( 0 = 0 , (/) , 0 ) = (/) )' % ph)
    r0 = s([s([s0, gv0], 'eqtrd', '( %s -> %s = if ( 0 = 0 , (/) , 0 ) )' % (ph, RRS('0'))), i0], 'eqtrd', '( %s -> %s = (/) )' % (ph, RRS('0')))
    w0 = s([r0, s([s([], 'wrd0', '(/) e. Word 2o')], 'a1i', '( %s -> (/) e. Word 2o )' % ph)], 'eqeltrd', '( %s -> %s e. Word 2o )' % (ph, RRS('0')))
    t0a = s([s([r0], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` (/) ) )' % (ph, RRS('0'))), closed(w, ph, 'tonat0', '( toNat ` (/) ) = 0')], 'eqtrd',
            '( %s -> ( toNat ` %s ) = 0 )' % (ph, RRS('0')))
    lf = lineq(w, ph, '( ( L - 0 ) x. F )', '( F x. L )', closure=cl, products=True)
    mm0 = s([cl.mem('F', 'ZZ'), lp, w.inst('mulmod0')], 'syl2anc', '( %s -> ( ( F x. L ) mod L ) = 0 )' % ph)
    t0b = s([s([lf], 'oveq1d', '( %s -> ( ( ( L - 0 ) x. F ) mod L ) = ( ( F x. L ) mod L ) )' % ph), mm0], 'eqtrd', '( %s -> ( ( ( L - 0 ) x. F ) mod L ) = 0 )' % ph)
    t0 = s([t0a, t0b], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( ( ( L - 0 ) x. F ) mod L ) )' % (ph, RRS('0')))
    l0_ = s([s([s([r0], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (ph, RRS('0'))), closed(w, ph, 'hash0', '( # ` (/) ) = 0')], 'eqtrd',
               '( %s -> ( # ` %s ) = 0 )' % (ph, RRS('0'))), s([bn], 'nn0ge0d', '( %s -> 0 <_ B )' % ph)], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (ph, RRS('0')))
    base = s([s([w0, t0, l0_], '3jca', '( %s -> %s )' % (ph, QR('0')))], 'a1d', '( %s -> %s )' % (ph, PS('0')))
    # step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ L )' % a
    La = lambda st: s([st], 'adantr', '( %s -> %s )' % (a2, concl(w, ph, st))) if True else None
    La = lambda st: s([s([s([st], 'adantr', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph, concl(w, ph, st)))], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))],
                      'adantr', '( %s -> %s )' % (a2, concl(w, ph, st)))
    mn = s([s([], 'simplr' if False else 'id', '') if False else s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ L )' % a2)
    cla = Closure(w, a2, {'L': ('NN', La(ln)), 'F': ('NN0', La(fn)), 'B': ('NN0', La(bn)), 'm': ('NN0', mn)})
    mle_ = linarith(w, a2, [m1l], 'm <_ L', closure=cla)
    ih = s([mle_, ih0], 'mpd', '( %s -> %s )' % (a2, QR('m')))
    rw_m = s([ih], 'simp1d', '( %s -> %s e. Word 2o )' % (a2, RRS('m')))
    rv_m = s([ih], 'simp2d', '( %s -> ( toNat ` %s ) = ( ( ( L - m ) x. F ) mod L ) )' % (a2, RRS('m')))
    rl_m = s([ih], 'simp3d', '( %s -> ( # ` %s ) <_ B )' % (a2, RRS('m')))
    RM = RRS('m')
    val = RWX(RM)
    # the value exists (a word)
    ttr_in = s([s([rw_m, La(plw), La(ln)], '3jca', '( %s -> ( %s e. Word 2o /\\ %s e. Word 2o /\\ L e. NN ) )' % (a2, RM, PLW)),
                s([s([rv_m, s([s([cla.mem('( ( L - m ) x. F )', 'RR'), La(lp)], 'jca' if False else 'id', '') if False else None], 'id', '') if False else
                      modlt_step(w, a2, cla, '( ( L - m ) x. F )', La(lp))], 'eqbrtrd', '( %s -> ( toNat ` %s ) < L )' % (a2, RM)), La(tpll)], 'jca',
                  '( %s -> ( ( toNat ` %s ) < L /\\ ( toNat ` %s ) < L ) )' % (a2, RM, PLW))], 'jca',
               '( %s -> ( ( %s e. Word 2o /\\ %s e. Word 2o /\\ L e. NN ) /\\ ( ( toNat ` %s ) < L /\\ ( toNat ` %s ) < L ) ) )' % (a2, RM, PLW, RM, PLW))
    from t8b_k_dpb import ST_RW, RV
    ttr = s([ttr_in, w.inst('ttrwd')], 'syl', '( %s -> ( %s e. Word 2o /\\ ( toNat ` %s ) = %s /\\ ( toNat ` %s ) < L ) )'
            % (a2, val, val, tsub_text(RV, {'G': RM, 'Q': PLW}), val))
    vw = s([ttr], 'simp1d', '( %s -> %s e. Word 2o )' % (a2, val))
    _VEX[(a2, val)] = s([vw], 'elexd', '( %s -> %s e. _V )' % (a2, val))
    xv = s([rw_m], 'elexd', '( %s -> %s e. _V )' % (a2, RM))
    gv = s([s([], 'fvex', '( %s ` ( m + 1 ) ) e. _V' % G1R)], 'a1i', '( %s -> ( %s ` ( m + 1 ) ) e. _V )' % (a2, G1R))
    sq = seq_step2(w, a2, OPR, G1R, 'm', mn, 'ttreswv',
                   '( ( %s e. Word 2o /\\ %s e. Word 2o ) /\\ ( %s e. Word 2o /\\ %%s e. NN0 ) )' % (PLW, ELW, RM),
                   [s([La(plw), s([La(l0), w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (a2, ELW))], 'jca',
                      '( %s -> ( %s e. Word 2o /\\ %s e. Word 2o ) )' % (a2, PLW, ELW)), rw_m], val, lambda t: 'if ( %s = 0 , (/) , %s )' % (t, t))
    RM1 = RRS('( m + 1 )')
    w1 = s([sq, vw], 'eqeltrd', '( %s -> %s e. Word 2o )' % (a2, RM1))
    # value
    tv = s([ttr], 'simp2d', '( %s -> ( toNat ` %s ) = %s )' % (a2, val, tsub_text(RV, {'G': RM, 'Q': PLW})))
    RVV = tsub_text(RV, {'G': RM, 'Q': PLW})
    r1, n1 = w.rewrite(RVV, {'( toNat ` %s )' % RM: ('( ( ( L - m ) x. F ) mod L )', rv_m), '( toNat ` %s )' % PLW: (FM, La(tpl))}, a2)
    # ttrespred at R := L - ( m + 1 )
    RR_ = '( L - ( m + 1 ) )'
    rn = s([s([s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % a2), La(l0), m1l], 'id', '') if False else None], 'id', '') if False else None
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % a2)
    rn = s([s([m1n], 'nn0zd', '( %s -> ( m + 1 ) e. ZZ )' % a2), s([La(l0)], 'nn0zd', '( %s -> L e. ZZ )' % a2), m1l], 'id', '') if False else \
        nn0sub_step(w, a2, m1n, La(l0), m1l, RR_)
    rp = s([s([La(ln), La(fn), rn], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ %s e. NN0 ) )' % (a2, RR_)), w.inst('ttrespred')], 'syl',
           '( %s -> %s )' % (a2, tsub_text(ST_RP, {'R': RR_}).split(' -> ', 1)[1][:-2]))

    e1 = lineq(w, a2, '( %s + 1 )' % RR_, '( L - m )', closure=cla)
    re_, rnew = w.rewrite(concl(w, a2, rp).split(' = ', 1)[1], {'( %s + 1 )' % RR_: ('( L - m )', e1)}, a2)
    assert rnew == n1, (rnew, n1)
    v2 = s([s([tv, r1], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (a2, val, n1)), s([rp, re_], 'eqtrd', '( %s -> ( ( %s x. F ) mod L ) = %s )' % (a2, RR_, n1))],
           'eqtr4d', '( %s -> ( toNat ` %s ) = ( ( %s x. F ) mod L ) )' % (a2, val, RR_))
    v3 = s([s([sq], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (a2, RM1, val)), v2], 'eqtrd', '( %s -> ( toNat ` %s ) = ( ( %s x. F ) mod L ) )' % (a2, RM1, RR_))
    # length
    from t8b_k_dpb import PH_RWL
    rl_in = s([s([rw_m, La(plw), La(l0)], '3jca', '( %s -> ( %s e. Word 2o /\\ %s e. Word 2o /\\ L e. NN0 ) )' % (a2, RM, PLW)),
               s([La(bn), s([rl_m, La(pll), La(ell)], '3jca', '( %s -> ( ( # ` %s ) <_ B /\\ ( # ` %s ) <_ B /\\ ( # ` %s ) <_ B ) )' % (a2, RM, PLW, ELW))], 'jca',
                 '( %s -> ( B e. NN0 /\\ ( ( # ` %s ) <_ B /\\ ( # ` %s ) <_ B /\\ ( # ` %s ) <_ B ) ) )' % (a2, RM, PLW, ELW))], 'jca',
              '( %s -> %s )' % (a2, tsub_text(PH_RWL, {'G': RM, 'Q': PLW, 'M': 'B'})))
    ll = s([rl_in, w.inst('ttrwdl')], 'syl', '( %s -> ( # ` %s ) <_ B )' % (a2, val))
    l3 = s([s([sq], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (a2, RM1, val)), ll], 'eqbrtrd', '( %s -> ( # ` %s ) <_ B )' % (a2, RM1))
    q1 = s([w1, v3, l3], '3jca', '( %s -> %s )' % (a2, QR('( m + 1 )')))
    st = s([q1], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    # from I e. ( 0 ... L )
    p = '( %s /\\ I e. ( 0 ... L ) )' % ph
    ifz = s([], 'simpr', '( %s -> I e. ( 0 ... L ) )' % p)
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> I e. NN0 )' % p)
    ile = s([ifz, w.inst('elfzle2')], 'syl', '( %s -> I <_ L )' % p)
    i2 = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), inn], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)), ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    w.qed([ile, i2], 'mpd', ST_RR)
    return w.run()


def ifexv(w, ph, cond, A, B):
    s = w.s
    ea = {'(/)': '0ex', '0': 'c0ex'}
    e = s([s([], ea[A], '%s e. _V' % A), s([], ea[B], '%s e. _V' % B)], 'ifex', 'if ( %s , %s , %s ) e. _V' % (cond, A, B))
    return s([e], 'a1i', '( %s -> if ( %s , %s , %s ) e. _V )' % (ph, cond, A, B))


def modlt_step(w, a, cl, X, lp):
    return w.s([cl.mem(X, 'RR'), lp, w.inst('modlt')], 'syl2anc', '( %s -> ( %s mod L ) < L )' % (a, X))


def nn0sub_step(w, a, m1n, l0, m1l, RR_):
    """( a -> ( L - ( m + 1 ) ) e. NN0 )"""
    s = w.s
    return s([s([m1n, l0], 'jca', '( %s -> ( ( m + 1 ) e. NN0 /\\ L e. NN0 ) )' % a), m1l, w.inst('nn0sub2' if False else 'id')], 'id', '') if False else \
        s([s([m1n], 'nn0zd', '( %s -> ( m + 1 ) e. ZZ )' % a), s([l0], 'nn0zd', '( %s -> L e. ZZ )' % a), m1l], 'znn0subd' if False else 'id', '') if False else \
        s([s([s([m1n], 'nn0zd', '( %s -> ( m + 1 ) e. ZZ )' % a), s([l0], 'nn0zd', '( %s -> L e. ZZ )' % a)], 'jca', '( %s -> ( ( m + 1 ) e. ZZ /\\ L e. ZZ ) )' % a),
           w.inst('znn0sub')], 'syl', '( %s -> ( ( m + 1 ) <_ L <-> %s e. NN0 ) )' % (a, RR_)) if False else _nn0sub(w, a, m1n, l0, m1l, RR_)


def _nn0sub(w, a, m1n, l0, m1l, RR_):
    s = w.s
    eq = s([s([s([m1n], 'nn0zd', '( %s -> ( m + 1 ) e. ZZ )' % a), s([l0], 'nn0zd', '( %s -> L e. ZZ )' % a), w.inst('znn0sub')], 'syl2anc',
              '( %s -> ( ( m + 1 ) <_ L <-> %s e. NN0 ) )' % (a, RR_))], 'id', '') if False else \
        s([s([m1n], 'nn0zd', '( %s -> ( m + 1 ) e. ZZ )' % a), s([l0], 'nn0zd', '( %s -> L e. ZZ )' % a), w.inst('znn0sub')], 'syl2anc',
          '( %s -> ( ( m + 1 ) <_ L <-> %s e. NN0 ) )' % (a, RR_))
    return s([m1l, eq], 'mpbid', '( %s -> %s e. NN0 )' % (a, RR_))


BODYR = lambda q, e, x: ('if ( ( toNat ` %s ) <_ ( toNat ` %s ) , ( ( %s subTrunc %s ) ` (/) ) , ( ( %s subTrunc ( ( %s subTrunc %s ) ` (/) ) ) ` (/) ) )'
                         % (q, x, x, q, e, q, x))
PH_RWV = '( ( Q e. Word 2o /\\ E e. Word 2o ) /\\ ( X e. Word 2o /\\ Y e. NN0 ) )'
ST_RWV = '( %s -> ( X ( Q ResWOp E ) Y ) = %s )' % (PH_RWV, BODYR('Q', 'E', 'X'))
OPAX = lambda t, l, p, X, Y: ('if ( ( %s ` ( %s - %s ) ) = ( inr ` (/) ) , %s , ( ( %s SetIfNone ( ( ( %s - %s ) x. %s ) mod %s ) ) ` ( <" %s "> ++ ( 2nd ` ( %s ` ( %s - %s ) ) ) ) ) )'
                              % (t, l, Y, X, X, l, Y, p, l, p, t, l, Y))
PH_ACV = '( ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) /\\ ( X e. Tbl /\\ Y e. NN0 ) )'
ST_ACV = '( %s -> ( X ( ( L DpAccOp F ) ` A ) Y ) = %s )' % (PH_ACV, OPAX('A', 'L', 'F', 'X', 'Y'))


def _cg(w, expr, var, val):
    h, n = w.congr(expr, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    if h is None:
        h = w.s([], 'eqidd', '( %s = %s -> %s = %s )' % (var, val, expr, expr)); n = expr
    return h, n


def ttreswv():
    ph = PH_RWV
    w = W('ttreswv', 'Value of ~ df-reswop .')
    s = w.s
    IN = lambda q, e: '( x e. Word 2o , y e. NN0 |-> %s )' % BODYR(q, e, 'x')
    h1, n1 = _cg(w, IN('q', 'e'), 'q', 'Q')
    h2, n2 = _cg(w, n1, 'e', 'E')
    assert n2 == IN('Q', 'E'), n2
    df = s([], 'df-reswop', 'ResWOp = ( q e. Word 2o , e e. Word 2o |-> %s )' % IN('q', 'e'))
    ov = s([h1, h2, df], 'ovmpog', '( ( Q e. Word 2o /\\ E e. Word 2o /\\ %s e. _V ) -> ( Q ResWOp E ) = %s )' % (IN('Q', 'E'), IN('Q', 'E')))
    qe = s([], 'simpl', '( %s -> ( Q e. Word 2o /\\ E e. Word 2o ) )' % ph)
    xy = s([], 'simpr', '( %s -> ( X e. Word 2o /\\ Y e. NN0 ) )' % ph)
    wv = s([s([], '2oex', '2o e. _V'), w.inst('wrdexg')], 'ax-mp', 'Word 2o e. _V')
    mex = s([s([wv, s([], 'nn0ex', 'NN0 e. _V')], 'mpoex', '%s e. _V' % IN('Q', 'E'))], 'a1i', '( %s -> %s e. _V )' % (ph, IN('Q', 'E')))
    o1 = s([s([qe], 'simpld', '( %s -> Q e. Word 2o )' % ph), s([qe], 'simprd', '( %s -> E e. Word 2o )' % ph), mex, ov], 'syl3anc',
           '( %s -> ( Q ResWOp E ) = %s )' % (ph, IN('Q', 'E')))
    o2 = s([o1], 'oveqd', '( %s -> ( X ( Q ResWOp E ) Y ) = ( X %s Y ) )' % (ph, IN('Q', 'E')))
    g1, m1 = _cg(w, BODYR('Q', 'E', 'x'), 'x', 'X')
    g2, m2 = _cg(w, m1, 'y', 'Y')
    assert m2 == BODYR('Q', 'E', 'X'), m2
    ov2 = s([g1, g2, s([], 'eqid', '%s = %s' % (IN('Q', 'E'), IN('Q', 'E')))], 'ovmpog',
            '( ( X e. Word 2o /\\ Y e. NN0 /\\ %s e. _V ) -> ( X %s Y ) = %s )' % (BODYR('Q', 'E', 'X'), IN('Q', 'E'), BODYR('Q', 'E', 'X')))
    bex = s([s([s([], 'fvex', '( ( X subTrunc Q ) ` (/) ) e. _V'), s([], 'fvex', '( ( E subTrunc ( ( Q subTrunc X ) ` (/) ) ) ` (/) ) e. _V')], 'ifex',
               '%s e. _V' % BODYR('Q', 'E', 'X'))], 'a1i', '( %s -> %s e. _V )' % (ph, BODYR('Q', 'E', 'X')))
    o3 = s([s([xy], 'simpld', '( %s -> X e. Word 2o )' % ph), s([xy], 'simprd', '( %s -> Y e. NN0 )' % ph), bex, ov2], 'syl3anc',
           '( %s -> ( X %s Y ) = %s )' % (ph, IN('Q', 'E'), BODYR('Q', 'E', 'X')))
    w.qed([o2, o3], 'eqtrd', ST_RWV)
    return w.run()


def ttaccov():
    ph = PH_ACV
    w = W('ttaccov', 'Value of ~ df-dpaccop : Lean\'s ` dpBody L p t ( L - y ) ` .')
    s = w.s
    INN = lambda t, l, p: '( x e. Tbl , y e. NN0 |-> %s )' % OPAX(t, l, p, 'x', 'y')
    MID = lambda l, p: '( t e. Tbl |-> %s )' % INN('t', l, p)
    h1, n1 = _cg(w, MID('l', 'p'), 'l', 'L')
    h2, n2 = _cg(w, n1, 'p', 'F')
    assert n2 == MID('L', 'F'), n2
    df = s([], 'df-dpaccop', 'DpAccOp = ( l e. NN , p e. NN0 |-> %s )' % MID('l', 'p'))
    tex = s([s([], 'ovex', '( ( Word NN0 |_| 1o ) ^m NN0 ) e. _V'), s([], 'df-tbl', 'Tbl = ( ( Word NN0 |_| 1o ) ^m NN0 )')], 'eqeltrri' if False else 'id', '') if False else None
    tex = s([s([], 'df-tbl', 'Tbl = ( ( Word NN0 |_| 1o ) ^m NN0 )'), s([], 'ovex', '( ( Word NN0 |_| 1o ) ^m NN0 ) e. _V')], 'eqeltri', 'Tbl e. _V')
    ov = s([h1, h2, df], 'ovmpog', '( ( L e. NN /\\ F e. NN0 /\\ %s e. _V ) -> ( L DpAccOp F ) = %s )' % (MID('L', 'F'), MID('L', 'F')))
    c3 = s([], 'simpl', '( %s -> ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) )' % ph)
    xy = s([], 'simpr', '( %s -> ( X e. Tbl /\\ Y e. NN0 ) )' % ph)
    mex = s([s([tex], 'mptex' if False else 'id', '') if False else s([tex, w.inst('mptexg')], 'ax-mp', '%s e. _V' % MID('L', 'F'))], 'a1i',
            '( %s -> %s e. _V )' % (ph, MID('L', 'F')))
    o1 = s([s([c3], 'simp1d', '( %s -> L e. NN )' % ph), s([c3], 'simp2d', '( %s -> F e. NN0 )' % ph), mex, ov], 'syl3anc',
           '( %s -> ( L DpAccOp F ) = %s )' % (ph, MID('L', 'F')))
    f1 = s([o1], 'fveq1d', '( %s -> ( ( L DpAccOp F ) ` A ) = ( %s ` A ) )' % (ph, MID('L', 'F')))
    g1, m1 = _cg(w, INN('t', 'L', 'F'), 't', 'A')
    assert m1 == INN('A', 'L', 'F')
    fg = s([g1, s([], 'eqid', '%s = %s' % (MID('L', 'F'), MID('L', 'F')))], 'fvmptg', '( ( A e. Tbl /\\ %s e. _V ) -> ( %s ` A ) = %s )'
           % (INN('A', 'L', 'F'), MID('L', 'F'), INN('A', 'L', 'F')))
    iex = s([s([tex, s([], 'nn0ex', 'NN0 e. _V')], 'mpoex', '%s e. _V' % INN('A', 'L', 'F'))], 'a1i', '( %s -> %s e. _V )' % (ph, INN('A', 'L', 'F')))
    f2 = s([s([c3], 'simp3d', '( %s -> A e. Tbl )' % ph), iex, fg], 'syl2anc', '( %s -> ( %s ` A ) = %s )' % (ph, MID('L', 'F'), INN('A', 'L', 'F')))
    e = s([f1, f2], 'eqtrd', '( %s -> ( ( L DpAccOp F ) ` A ) = %s )' % (ph, INN('A', 'L', 'F')))
    o2 = s([e], 'oveqd', '( %s -> ( X ( ( L DpAccOp F ) ` A ) Y ) = ( X %s Y ) )' % (ph, INN('A', 'L', 'F')))
    B_ = OPAX('A', 'L', 'F', 'x', 'y')
    k1, q1 = _cg(w, B_, 'x', 'X')
    k2, q2 = _cg(w, q1, 'y', 'Y')
    assert q2 == OPAX('A', 'L', 'F', 'X', 'Y'), q2
    ov2 = s([k1, k2, s([], 'eqid', '%s = %s' % (INN('A', 'L', 'F'), INN('A', 'L', 'F')))], 'ovmpog',
            '( ( X e. Tbl /\\ Y e. NN0 /\\ %s e. _V ) -> ( X %s Y ) = %s )' % (q2, INN('A', 'L', 'F'), q2))
    SI = '( ( X SetIfNone ( ( ( L - Y ) x. F ) mod L ) ) ` ( <" F "> ++ ( 2nd ` ( A ` ( L - Y ) ) ) ) )'
    vex_ = s([s([s([], 'vex' if False else 'id', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
    xv = s([s([xy], 'simpld', '( %s -> X e. Tbl )' % ph)], 'elexd', '( %s -> X e. _V )' % ph)
    bx = s([xv, s([s([], 'fvex', '%s e. _V' % SI)], 'a1i', '( %s -> %s e. _V )' % (ph, SI))], 'ifcld', '( %s -> %s e. _V )' % (ph, q2))
    o3 = s([s([xy], 'simpld', '( %s -> X e. Tbl )' % ph), s([xy], 'simprd', '( %s -> Y e. NN0 )' % ph), bx, ov2], 'syl3anc',
           '( %s -> ( X %s Y ) = %s )' % (ph, INN('A', 'L', 'F'), q2))
    w.qed([o2, o3], 'eqtrd', ST_ACV)
    return w.run()



def seq_step2(w, a, OP, G, t, tn, vlem, conj_fmt, parts2, val, Gof):
    """( a -> ( seq 0 ( OP , G ) ` ( t + 1 ) ) = val ) by seqp1, G ` ( t + 1 ) = ( t + 1 ) and the value lemma vlem
    (antecedent conj_fmt % ( G ` ( t + 1 ) ) proved from parts2 = [ first conjunct , ( seq ` t ) typing ])"""
    from t7lib import mval
    s = w.s
    SQ = lambda u: '( seq 0 ( %s , %s ) ` %s )' % (OP, G, u)
    T1 = '( %s + 1 )' % t
    uz = s([tn, w.inst('elnn0uz')], 'sylib', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (a, t))
    sp = s([uz, w.inst('seqp1')], 'syl', '( %s -> %s = ( %s %s ( %s ` %s ) ) )' % (a, SQ(T1), SQ(t), OP, G, T1))
    t1n = s([tn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (a, T1))
    t1e = s([t1n], 'elexd', '( %s -> %s e. _V )' % (a, T1))
    first = Gof(T1)[len('if ( %s = 0 , ' % T1):].rsplit(' , %s )' % T1, 1)[0]
    fex = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % a) if first == '(/)' else \
        s([s([], 'fvex', '%s e. _V' % first)], 'a1i', '( %s -> %s e. _V )' % (a, first))
    gv = mval(w, a, 'k', 'NN0', Gof, T1, t1n, s([fex, t1e], 'ifcld', '( %s -> %s e. _V )' % (a, Gof(T1))))
    ne0 = s([s([tn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (a, T1))], 'nnne0d', '( %s -> %s =/= 0 )' % (a, T1))
    g2 = s([gv, s([s([ne0], 'neneqd', '( %s -> -. %s = 0 )' % (a, T1))], 'iffalsed', '( %s -> %s = %s )' % (a, Gof(T1), T1))], 'eqtrd',
           '( %s -> ( %s ` %s ) = %s )' % (a, G, T1, T1))
    gn = s([g2, t1n], 'eqeltrd', '( %s -> ( %s ` %s ) e. NN0 )' % (a, G, T1))
    GT = '( %s ` %s )' % (G, T1)
    cf = conj_fmt % GT
    inner = cf.split(' /\\ ( ', 1)[1][:-2] if False else None
    c2 = s([parts2[1], gn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (a, concl(w, a, parts2[1]), GT))
    cj_ = s([parts2[0], c2], 'jca', '( %s -> %s )' % (a, cf))
    vraw = val(GT) if callable(val) else val
    vl = s([cj_, w.inst(vlem)], 'syl', '( %s -> ( %s %s %s ) = %s )' % (a, SQ(t), OP, GT, vraw))
    r = s([sp, vl], 'eqtrd', '( %s -> %s = %s )' % (a, SQ(T1), vraw))
    if callable(val) and GT in vraw:
        rr, vn = w.rewrite(vraw, {GT: (T1, g2)}, a)
        assert vn == val(T1), vn
        r = s([r, rr], 'eqtrd', '( %s -> %s = %s )' % (a, SQ(T1), vn))
    return r



SBQ = lambda X, n='N': '( %s =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` %s ) ) <_ %s /\\ A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) ) )' % (X, X, n, X)
APC = '( ( C SetIfNone J ) ` W )'
FILLC = 'if ( ( C ` J ) = ( inr ` (/) ) , ( inl ` W ) , ( C ` J ) )'
PH_TS = '( ( C e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) /\\ ( ( # ` W ) <_ N /\\ A. a e. ran W a < ( 2 ^ B ) ) /\\ %s )' % TBB('C')
ST_TS = '( %s -> %s )' % (PH_TS, TBB(APC))


def eqsb(w, X, V, n='N'):
    """closed ( X = V -> ( SBQ( X ) <-> SBQ( V ) ) )"""
    idn = w.s([], 'id', '( %s = %s -> %s = %s )' % (X, V, X, V))
    st, new = w.wcongr(SBQ(X, n), {}, '%s = %s' % (X, V), {}, rules={X: (V, idn)})
    assert new == SBQ(V, n), new
    return st


def tttbbset():
    ph = PH_TS
    w = W('tttbbset', 'The guarded write keeps ` TblBounded ` when the written list is bounded (Lean '
                      '` tblBounded_setIfNone ` ).')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    ct, jn, ww = c['C e. Tbl'], c['J e. NN0'], c['W e. Word NN0']
    wle, wr, tb = c['( # ` W ) <_ N'], c['A. a e. ran W a < ( 2 ^ B )'], c[TBB('C')]
    pe = '( %s /\\ e e. NN0 )' % ph
    Le = lambda st: s([st], 'adantr', '( %s -> %s )' % (pe, concl(w, ph, st)))
    en = s([], 'simpr', '( %s -> e e. NN0 )' % pe)
    APE = '( %s ` e )' % APC
    fv = s([s([s([Le(ct), Le(jn), Le(ww)], '3jca', '( %s -> ( C e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) )' % pe), en], 'jca',
              '( %s -> ( ( C e. Tbl /\\ J e. NN0 /\\ W e. Word NN0 ) /\\ e e. NN0 ) )' % pe), w.inst('ttsetfv')], 'syl',
           '( %s -> %s = if ( e = J , %s , ( C ` e ) ) )' % (pe, APE, FILLC))
    def inst_tb(p, X, xn, Lp):
        idd = s([], 'id', '( d = %s -> d = %s )' % (X, X))
        cg, new = w.wcongr(SBQ('( C ` d )'), {'d': X}, 'd = %s' % X, {'d': idd})
        assert new == SBQ('( C ` %s )' % X), new
        r = s([cg], 'rspcv', '( %s e. NN0 -> ( %s -> %s ) )' % (X, TBB('C'), SBQ('( C ` %s )' % X)))
        return s([xn, Lp(tb), r], 'sylc', '( %s -> %s )' % (p, SBQ('( C ` %s )' % X)))
    # SBQ( inl W )
    IW = '( inl ` W )'
    wv = s([ww], 'elexd', '( %s -> W e. _V )' % ph)
    i2 = s([wv, w.inst('2ndinl')], 'syl', '( %s -> ( 2nd ` %s ) = W )' % (ph, IW))
    l2 = s([s([i2], 'fveq2d', '( %s -> ( # ` ( 2nd ` %s ) ) = ( # ` W ) )' % (ph, IW)), wle], 'eqbrtrd', '( %s -> ( # ` ( 2nd ` %s ) ) <_ N )' % (ph, IW))
    cq = s([], 'breq1', '( a = q -> ( a < ( 2 ^ B ) <-> q < ( 2 ^ B ) ) )')
    cb = s([cq], 'cbvralvw', '( A. a e. ran W a < ( 2 ^ B ) <-> A. q e. ran W q < ( 2 ^ B ) )')
    wq = s([wr, cb], 'sylib', '( %s -> A. q e. ran W q < ( 2 ^ B ) )' % ph)
    rq = s([s([i2], 'rneqd', '( %s -> ran ( 2nd ` %s ) = ran W )' % (ph, IW)), w.inst('raleq')], 'syl',
           '( %s -> ( A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) <-> A. q e. ran W q < ( 2 ^ B ) ) )' % (ph, IW))
    r2 = s([wq, rq], 'mpbird', '( %s -> A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) )' % (ph, IW))
    sbw = s([s([l2, r2], 'jca', '( %s -> ( ( # ` ( 2nd ` %s ) ) <_ N /\\ A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) ) )' % (ph, IW, IW))], 'a1d',
            '( %s -> %s )' % (ph, SBQ(IW)))
    sbj = inst_tb(ph, 'J', jn, lambda st: st)
    # the value by cases
    GO = lambda p: '( %s -> %s )' % (p, SBQ(APE))
    def fin(p, V, veq, sbv):
        bi = s([veq, eqsb(w, APE, V)], 'syl', '( %s -> ( %s <-> %s ) )' % (p, SBQ(APE), SBQ(V)))
        return s([sbv, bi], 'mpbird', GO(p))
    p1 = '( %s /\\ e = J )' % pe
    L1 = lambda st: s([st], 'adantr', '( %s -> %s )' % (p1, concl(w, pe, st)))
    ej = s([], 'simpr', '( %s -> e = J )' % p1)
    v1 = s([L1(fv), s([ej], 'iftrued', '( %s -> if ( e = J , %s , ( C ` e ) ) = %s )' % (p1, FILLC, FILLC))], 'eqtrd', '( %s -> %s = %s )' % (p1, APE, FILLC))
    p11 = '( %s /\\ ( C ` J ) = ( inr ` (/) ) )' % p1
    L11 = lambda st: s([st], 'adantr', '( %s -> %s )' % (p11, concl(w, p1, st)))
    v11 = s([L11(v1), s([s([], 'simpr', '( %s -> ( C ` J ) = ( inr ` (/) ) )' % p11)], 'iftrued', '( %s -> %s = %s )' % (p11, FILLC, IW))], 'eqtrd',
            '( %s -> %s = %s )' % (p11, APE, IW))
    L_ph11 = lambda st: s([L1(Le(st))], 'adantr', '( %s -> %s )' % (p11, concl(w, ph, st)))
    o11 = fin(p11, IW, v11, L_ph11(sbw))
    p12 = '( %s /\\ -. ( C ` J ) = ( inr ` (/) ) )' % p1
    L12 = lambda st: s([st], 'adantr', '( %s -> %s )' % (p12, concl(w, p1, st)))
    v12 = s([L12(v1), s([s([], 'simpr', '( %s -> -. ( C ` J ) = ( inr ` (/) ) )' % p12)], 'iffalsed', '( %s -> %s = ( C ` J ) )' % (p12, FILLC))], 'eqtrd',
            '( %s -> %s = ( C ` J ) )' % (p12, APE))
    L_ph12 = lambda st: s([L1(Le(st))], 'adantr', '( %s -> %s )' % (p12, concl(w, ph, st)))
    o12 = fin(p12, '( C ` J )', v12, L_ph12(sbj))
    o1 = s([o11, o12], 'pm2.61dan', GO(p1))
    p2 = '( %s /\\ -. e = J )' % pe
    L2 = lambda st: s([st], 'adantr', '( %s -> %s )' % (p2, concl(w, pe, st)))
    v2 = s([L2(fv), s([s([], 'simpr', '( %s -> -. e = J )' % p2)], 'iffalsed', '( %s -> if ( e = J , %s , ( C ` e ) ) = ( C ` e ) )' % (p2, FILLC))], 'eqtrd',
           '( %s -> %s = ( C ` e ) )' % (p2, APE))
    sbe = inst_tb(p2, 'e', L2(en), lambda st: L2(Le(st)))
    o2 = fin(p2, '( C ` e )', v2, sbe)
    oe = s([o1, o2], 'pm2.61dan', GO(pe))
    ra = s([oe], 'ralrimiva', '( %s -> A. e e. NN0 %s )' % (ph, SBQ(APE)))
    ide = s([], 'id', '( e = d -> e = d )')
    cge, newe = w.wcongr(SBQ(APE), {'e': 'd'}, 'e = d', {'e': ide})
    assert newe == SBQ('( %s ` d )' % APC), newe
    cbe = s([cge], 'cbvralvw', '( A. e e. NN0 %s <-> %s )' % (SBQ(APE), TBB(APC)))
    w.qed([ra, cbe], 'sylib', ST_TS)
    return w.run()



DG = lambda f, x: '( 1st ` ( ( ( ( L DpGo F ) ` A ) ` %s ) ` %s ) )' % (f, x)
DG1 = DG('L', ACC0)
PH_AC = '( ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ F < ( 2 ^ B ) ) /\\ %s )' % TBB('A')
QA = lambda t: '( %s e. Tbl /\\ %s /\\ %s = %s )' % (ACCS(t), TBB(ACCS(t), '( N + 1 )'), DG1, DG('( L - %s )' % t, ACCS(t)))
ST_AC = '( ( %s /\\ I e. ( 0 ... L ) ) -> %s )' % (PH_AC, QA('I'))


def eqtbb(w, X, V, n):
    idn = w.s([], 'id', '( %s = %s -> %s = %s )' % (X, V, X, V))
    st, new = w.wcongr(TBB(X, n), {}, '%s = %s' % (X, V), {}, rules={X: (V, idn)})
    assert new == TBB(V, n), new
    return st


def ttaccs():
    ph = PH_AC
    w = W('ttaccs', 'The accumulators of Lean\'s ` dpStep ` ( ` accSeq ` ): tables, bounded by ` TblBounded ` at ` N + 1 ` , '
                    'and the value of ` dpGo ` from ` accSeq 0 ` is the value from ` accSeq i ` with ` L - i ` fuel left '
                    '(Lean ` dpGo_accSeq ` , ` tblBounded_accSeq ` ).')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    ln, fn, at, nn, bn, fl, tb = (c['L e. NN'], c['F e. NN0'], c['A e. Tbl'], c['N e. NN0'], c['B e. NN0'], c['F < ( 2 ^ B )'], c[TBB('A')])
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    cl = Closure(w, ph, {'L': ('NN', ln), 'F': ('NN0', fn), 'N': ('NN0', nn), 'B': ('NN0', bn)})
    N1 = '( N + 1 )'
    n1n = cl.mem(N1, 'NN0')
    tbm = s([s([s([nn, n1n, linarith(w, ph, [], 'N <_ %s' % N1, closure=cl)], '3jca', '( %s -> ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) )' % (ph, N1, N1)), tb], 'jca',
               '( %s -> ( ( N e. NN0 /\\ %s e. NN0 /\\ N <_ %s ) /\\ %s ) )' % (ph, N1, N1, TBB('A'))), w.inst('ttabtbbm')], 'syl',
            '( %s -> %s )' % (ph, TBB('A', N1)))
    fv_ = s([fn], 'elexd', '( %s -> F e. _V )' % ph)
    def s1ran(p, fvp, flp):
        sr = s([fvp, w.inst('s1rn')], 'syl', '( %s -> ran <" F "> = { F } )' % p)
        rsg = s([fvp, s([s([], 'breq1', '( a = F -> ( a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')], 'ralsng', '( F e. _V -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )')],
                'syl', '( %s -> ( A. a e. { F } a < ( 2 ^ B ) <-> F < ( 2 ^ B ) ) )' % p)
        r1 = s([flp, rsg], 'mpbird', '( %s -> A. a e. { F } a < ( 2 ^ B ) )' % p)
        rq = s([sr, w.inst('raleq')], 'syl', '( %s -> ( A. a e. ran <" F "> a < ( 2 ^ B ) <-> A. a e. { F } a < ( 2 ^ B ) ) )' % p)
        return s([r1, rq], 'mpbird', '( %s -> A. a e. ran <" F "> a < ( 2 ^ B ) )' % p), sr
    # base
    PS = lambda t: '( %s <_ L -> %s )' % (t, QA(t))
    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    from t7lib import mval
    s0 = s([closed(w, ph, '0z', '0 e. ZZ'), w.inst('seq1')], 'syl', '( %s -> %s = ( %s ` 0 ) )' % (ph, ACCS('0'), G2A))
    X0 = lambda t: 'if ( %s = 0 , %s , %s )' % (t, ACC0, t)
    ax0 = s([s([s([], 'fvex', '%s e. _V' % ACC0)], 'a1i', '( %s -> %s e. _V )' % (ph, ACC0)), closed(w, ph, 'c0ex', '0 e. _V')], 'ifcld', '( %s -> %s e. _V )' % (ph, X0('0')))
    gv0 = mval(w, ph, 'k', 'NN0', X0, '0', closed(w, ph, '0nn0', '0 e. NN0'), ax0)
    i0 = s([s([], 'eqidd', '( %s -> 0 = 0 )' % ph)], 'iftrued', '( %s -> %s = %s )' % (ph, X0('0'), ACC0))
    r0 = s([s([s0, gv0], 'eqtrd', '( %s -> %s = %s )' % (ph, ACCS('0'), X0('0'))), i0], 'eqtrd', '( %s -> %s = %s )' % (ph, ACCS('0'), ACC0))
    a0t = s([s([s([ln, fn], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % ph), at], 'jca', '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) )' % ph),
             w.inst('dpstepacl')], 'syl', '( %s -> %s e. Tbl )' % (ph, ACC0))
    w0 = s([r0, a0t], 'eqeltrd', '( %s -> %s e. Tbl )' % (ph, ACCS('0')))
    FM = '( F mod L )'
    fmn = s([cl.mem('F', 'ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, FM))
    s1f = s([fn], 's1cld', '( %s -> <" F "> e. Word NN0 )' % ph)
    s1l = s([s([s([], 's1len', '( # ` <" F "> ) = 1')], 'a1i', '( %s -> ( # ` <" F "> ) = 1 )' % ph), linarith(w, ph, [cl.ge0('N')], '1 <_ %s' % N1, closure=cl)],
            'eqbrtrd', '( %s -> ( # ` <" F "> ) <_ %s )' % (ph, N1))
    rf, _ = s1ran(ph, fv_, fl)
    tsi = s([s([s([at, fmn, s1f], '3jca', '( %s -> ( A e. Tbl /\\ %s e. NN0 /\\ <" F "> e. Word NN0 ) )' % (ph, FM)),
                s([s1l, rf], 'jca', '( %s -> ( ( # ` <" F "> ) <_ %s /\\ A. a e. ran <" F "> a < ( 2 ^ B ) ) )' % (ph, N1)), tbm], '3jca',
               '( %s -> %s )' % (ph, tsub_text(PH_TS, {'C': 'A', 'J': FM, 'W': '<" F ">', 'N': N1}))), w.inst('tttbbset')], 'syl',
            '( %s -> %s )' % (ph, TBB(ACC0, N1)))
    b0 = s([tsi, s([r0, eqtbb(w, ACCS('0'), ACC0, N1)], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBB(ACCS('0'), N1), TBB(ACC0, N1)))], 'mpbird',
           '( %s -> %s )' % (ph, TBB(ACCS('0'), N1)))
    lz = s([s([ln], 'nncnd', '( %s -> L e. CC )' % ph)], 'subid1d', '( %s -> ( L - 0 ) = L )' % ph)
    dg0, dgn = w.rewrite(DG('( L - 0 )', ACCS('0')), {'( L - 0 )': ('L', lz), ACCS('0'): (ACC0, r0)}, ph)
    assert dgn == DG1, dgn
    base = s([s([w0, b0, s([dg0], 'eqcomd', '( %s -> %s = %s )' % (ph, DG1, DG('( L - 0 )', ACCS('0'))))], '3jca', '( %s -> %s )' % (ph, QA('0')))], 'a1d',
             '( %s -> %s )' % (ph, PS('0')))
    # step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ L )' % a
    La = lambda st: s([s([s([st], 'adantr', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph, concl(w, ph, st)))], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))],
                      'adantr', '( %s -> %s )' % (a2, concl(w, ph, st)))
    mn = s([s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ L )' % a2)
    cla = Closure(w, a2, {'L': ('NN', La(ln)), 'F': ('NN0', La(fn)), 'N': ('NN0', La(nn)), 'B': ('NN0', La(bn)), 'm': ('NN0', mn)})
    ih = s([linarith(w, a2, [m1l], 'm <_ L', closure=cla), ih0], 'mpd', '( %s -> %s )' % (a2, QA('m')))
    AM = ACCS('m')
    amt = s([ih], 'simp1d', '( %s -> %s e. Tbl )' % (a2, AM))
    amb = s([ih], 'simp2d', '( %s -> %s )' % (a2, TBB(AM, N1)))
    amd = s([ih], 'simp3d', '( %s -> %s = %s )' % (a2, DG1, DG('( L - m )', AM)))
    RR_ = '( L - ( m + 1 ) )'
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % a2)
    rn = _nn0sub(w, a2, m1n, La(l0), m1l, RR_)
    SLT = '( A ` %s )' % RR_
    VAL = OPAX('A', 'L', 'F', AM, '( m + 1 )')
    c3 = s([La(ln), La(fn), La(at)], '3jca', '( %s -> ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) )' % a2)
    sq = seq_step2(w, a2, OPA, G2A, 'm', mn, 'ttaccov', '( ( L e. NN /\\ F e. NN0 /\\ A e. Tbl ) /\\ ( %s e. Tbl /\\ %%s e. NN0 ) )' % AM,
                   [c3, amt], lambda Y: OPAX('A', 'L', 'F', AM, Y), lambda t: 'if ( %s = 0 , %s , %s )' % (t, ACC0, t))
    A1 = ACCS('( m + 1 )')
    vt = s([s([s([s([La(ln), La(fn)], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % a2), La(at)], 'jca', '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) )' % a2),
               s([rn, amt], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. Tbl ) )' % (a2, RR_, AM))], 'jca',
              '( %s -> ( ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) /\\ ( %s e. NN0 /\\ %s e. Tbl ) ) )' % (a2, RR_, AM)), w.inst('dpgoacl')], 'syl',
           '( %s -> %s e. Tbl )' % (a2, VAL))
    w1 = s([sq, vt], 'eqeltrd', '( %s -> %s e. Tbl )' % (a2, A1))
    # TBB of the value by cases
    C0_ = '%s = ( inr ` (/) )' % SLT
    GOAL = lambda p: '( %s -> %s )' % (p, TBB(VAL, N1))
    q1 = '( %s /\\ %s )' % (a2, C0_)
    Lq1 = lambda st: s([st], 'adantr', '( %s -> %s )' % (q1, concl(w, a2, st)))
    v1 = s([s([], 'simpr', '( %s -> %s )' % (q1, C0_))], 'iftrued', '( %s -> %s = %s )' % (q1, VAL, AM))
    o1 = s([Lq1(amb), s([v1, eqtbb(w, VAL, AM, N1)], 'syl', '( %s -> ( %s <-> %s ) )' % (q1, TBB(VAL, N1), TBB(AM, N1)))], 'mpbird', GOAL(q1))
    q2 = '( %s /\\ -. %s )' % (a2, C0_)
    Lq2 = lambda st: s([st], 'adantr', '( %s -> %s )' % (q2, concl(w, a2, st)))
    nc = s([], 'simpr', '( %s -> -. %s )' % (q2, C0_))
    W2 = '( <" F "> ++ ( 2nd ` %s ) )' % SLT
    JX = '( ( %s x. F ) mod L )' % RR_
    SET = '( ( %s SetIfNone %s ) ` %s )' % (AM, JX, W2)
    v2 = s([nc], 'iffalsed', '( %s -> %s = %s )' % (q2, VAL, SET))
    stl = s([Lq2(La(at)), Lq2(rn), w.inst('tblfv')], 'syl2anc', '( %s -> %s e. %s )' % (q2, SLT, SLOT))
    s2w = s([stl, w.inst('ttabopt')], 'syl', '( %s -> ( 2nd ` %s ) e. Word NN0 )' % (q2, SLT))
    s1f2 = s([Lq2(La(fn))], 's1cld', '( %s -> <" F "> e. Word NN0 )' % q2)
    w2w = s([s1f2, s2w, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (q2, W2))
    # the slot's bound from TBB( A )
    idd = s([], 'id', '( d = %s -> d = %s )' % (RR_, RR_))
    cgd, newd = w.wcongr(SBQ('( A ` d )'), {'d': RR_}, 'd = %s' % RR_, {'d': idd})
    rsp = s([cgd], 'rspcv', '( %s e. NN0 -> ( %s -> %s ) )' % (RR_, TBB('A'), SBQ(SLT)))
    sbs = s([Lq2(rn), Lq2(La(tb)), rsp], 'sylc', '( %s -> %s )' % (q2, SBQ(SLT)))
    nne = s([nc], 'neqned', '( %s -> %s =/= ( inr ` (/) ) )' % (q2, SLT))
    bth = s([nne, sbs], 'mpd', '( %s -> ( ( # ` ( 2nd ` %s ) ) <_ N /\\ A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) ) )' % (q2, SLT, SLT))
    sle = s([bth], 'simpld', '( %s -> ( # ` ( 2nd ` %s ) ) <_ N )' % (q2, SLT))
    srq = s([bth], 'simprd', '( %s -> A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) )' % (q2, SLT))
    cqa = s([s([], 'breq1', '( q = a -> ( q < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
            '( A. q e. ran ( 2nd ` %s ) q < ( 2 ^ B ) <-> A. a e. ran ( 2nd ` %s ) a < ( 2 ^ B ) )' % (SLT, SLT))
    sra = s([srq, cqa], 'sylib', '( %s -> A. a e. ran ( 2nd ` %s ) a < ( 2 ^ B ) )' % (q2, SLT))
    clq = Closure(w, q2, {'N': ('NN0', Lq2(La(nn)))})
    clq.leaf('( # ` ( 2nd ` %s ) )' % SLT, 'NN0', s([s2w, w.inst('lencl')], 'syl', '( %s -> ( # ` ( 2nd ` %s ) ) e. NN0 )' % (q2, SLT)))
    clq.leaf('( # ` <" F "> )', 'NN0', s([s1f2, w.inst('lencl')], 'syl', '( %s -> ( # ` <" F "> ) e. NN0 )' % q2))
    clq.leaf('( # ` %s )' % W2, 'NN0', s([w2w, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (q2, W2)))
    wl = s([s1f2, s2w, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" F "> ) + ( # ` ( 2nd ` %s ) ) ) )' % (q2, W2, SLT))
    s1l2 = s([s([], 's1len', '( # ` <" F "> ) = 1')], 'a1i', '( %s -> ( # ` <" F "> ) = 1 )' % q2)
    wle = linarith(w, q2, [wl, s1l2, sle], '( # ` %s ) <_ %s' % (W2, N1), closure=clq)
    fvq = s([Lq2(La(fn))], 'elexd', '( %s -> F e. _V )' % q2)
    rf2, _ = s1ran(q2, fvq, Lq2(La(fl)))
    cr = s([s1f2, s2w, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran <" F "> u. ran ( 2nd ` %s ) ) )' % (q2, W2, SLT))
    run_ = s([s([rf2, sra], 'jca', '( %s -> ( A. a e. ran <" F "> a < ( 2 ^ B ) /\\ A. a e. ran ( 2nd ` %s ) a < ( 2 ^ B ) ) )' % (q2, SLT)),
              s([], 'ralunb', '( A. a e. ( ran <" F "> u. ran ( 2nd ` %s ) ) a < ( 2 ^ B ) <-> ( A. a e. ran <" F "> a < ( 2 ^ B ) /\\ A. a e. ran ( 2nd ` %s ) a < ( 2 ^ B ) ) )'
                % (SLT, SLT))], 'sylibr', '( %s -> A. a e. ( ran <" F "> u. ran ( 2nd ` %s ) ) a < ( 2 ^ B ) )' % (q2, SLT))
    rw2 = s([run_, s([cr, w.inst('raleq')], 'syl', '( %s -> ( A. a e. ran %s a < ( 2 ^ B ) <-> A. a e. ( ran <" F "> u. ran ( 2nd ` %s ) ) a < ( 2 ^ B ) ) )'
                     % (q2, W2, SLT))], 'mpbird', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (q2, W2))
    jxn = s([s([s([Lq2(rn), Lq2(La(fn))], 'nn0mulcld', '( %s -> ( %s x. F ) e. NN0 )' % (q2, RR_))], 'nn0zd', '( %s -> ( %s x. F ) e. ZZ )' % (q2, RR_)),
             Lq2(La(ln)), w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (q2, JX))
    tsi2 = s([s([s([Lq2(amt), jxn, w2w], '3jca', '( %s -> ( %s e. Tbl /\\ %s e. NN0 /\\ %s e. Word NN0 ) )' % (q2, AM, JX, W2)),
                 s([wle, rw2], 'jca', '( %s -> ( ( # ` %s ) <_ %s /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (q2, W2, N1, W2)), Lq2(amb)], '3jca',
                '( %s -> %s )' % (q2, tsub_text(PH_TS, {'C': AM, 'J': JX, 'W': W2, 'N': N1}))), w.inst('tttbbset')], 'syl',
             '( %s -> %s )' % (q2, TBB(SET, N1)))
    o2 = s([tsi2, s([v2, eqtbb(w, VAL, SET, N1)], 'syl', '( %s -> ( %s <-> %s ) )' % (q2, TBB(VAL, N1), TBB(SET, N1)))], 'mpbird', GOAL(q2))
    tbv = s([o1, o2], 'pm2.61dan', GOAL(a2))
    b1 = s([tbv, s([sq, eqtbb(w, A1, VAL, N1)], 'syl', '( %s -> ( %s <-> %s ) )' % (a2, TBB(A1, N1), TBB(VAL, N1)))], 'mpbird', '( %s -> %s )' % (a2, TBB(A1, N1)))
    # dpGo
    e1 = lineq(w, a2, '( L - m )', '( %s + 1 )' % RR_, closure=cla)
    dr, dn = w.rewrite(DG('( L - m )', AM), {'( L - m )': ('( %s + 1 )' % RR_, e1)}, a2)
    dp = s([s([s([s([s([La(ln), La(fn)], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % a2), La(at)], 'jca', '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) )' % a2), rn],
                 'jca', '( %s -> ( ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) /\\ %s e. NN0 ) )' % (a2, RR_)), amt], 'jca',
               '( %s -> ( ( ( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl ) /\\ %s e. NN0 ) /\\ %s e. Tbl ) )' % (a2, RR_, AM)), w.inst('dpgop1')], 'syl',
           '( %s -> ( ( ( ( L DpGo F ) ` A ) ` ( %s + 1 ) ) ` %s ) = <. %s , ( ( 2nd ` ( ( ( ( L DpGo F ) ` A ) ` %s ) ` %s ) ) + 1 ) >. )'
           % (a2, RR_, AM, DG(RR_, VAL), RR_, VAL))
    DGP = '( ( ( ( L DpGo F ) ` A ) ` ( %s + 1 ) ) ` %s )' % (RR_, AM)
    f1 = s([dp], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , ( ( 2nd ` ( ( ( ( L DpGo F ) ` A ) ` %s ) ` %s ) ) + 1 ) >. ) )' % (a2, DGP, DG(RR_, VAL), RR_, VAL))
    o1s = s([s([s([], 'fvex', '%s e. _V' % DG(RR_, VAL))], 'a1i', '( %s -> %s e. _V )' % (a2, DG(RR_, VAL))),
             s([s([], 'ovex', '( ( 2nd ` ( ( ( ( L DpGo F ) ` A ) ` %s ) ` %s ) ) + 1 ) e. _V' % (RR_, VAL))], 'a1i',
               '( %s -> ( ( 2nd ` ( ( ( ( L DpGo F ) ` A ) ` %s ) ` %s ) ) + 1 ) e. _V )' % (a2, RR_, VAL)), w.inst('op1stg')], 'syl2anc',
            '( %s -> ( 1st ` <. %s , ( ( 2nd ` ( ( ( ( L DpGo F ) ` A ) ` %s ) ` %s ) ) + 1 ) >. ) = %s )' % (a2, DG(RR_, VAL), RR_, VAL, DG(RR_, VAL)))
    g1 = s([f1, o1s], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (a2, DGP, DG(RR_, VAL)))
    ar, an = w.rewrite(DG(RR_, VAL), {VAL: (A1, s([sq], 'eqcomd', '( %s -> %s = %s )' % (a2, VAL, A1)))}, a2)
    ch = s([s([s([amd, dr], 'eqtrd', '( %s -> %s = %s )' % (a2, DG1, dn)), g1], 'eqtrd', '( %s -> %s = %s )' % (a2, DG1, DG(RR_, VAL))), ar], 'eqtrd',
           '( %s -> %s = %s )' % (a2, DG1, an))
    assert an == DG(RR_, A1)
    qq = s([w1, b1, ch], '3jca', '( %s -> %s )' % (a2, QA('( m + 1 )')))
    st = s([qq], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( %s /\\ I e. ( 0 ... L ) )' % ph
    ifz = s([], 'simpr', '( %s -> I e. ( 0 ... L ) )' % p)
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> I e. NN0 )' % p)
    ile = s([ifz, w.inst('elfzle2')], 'syl', '( %s -> I <_ L )' % p)
    i2 = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), inn], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)), ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    w.qed([ile, i2], 'mpd', ST_AC)
    return w.run()



ST_ACL = '( %s -> ( 1st ` ( ( L DpStep F ) ` A ) ) = %s )' % (PH_AC, ACCS('L'))


def ttaccl():
    ph = PH_AC
    w = W('ttaccl', 'The table of the DP step is the last accumulator (Lean ` dpStep_eq_accSeq ` ).')
    s = w.s
    c = Ctx(w, ph, parse_conj(ph))
    ln, fn, at = c['L e. NN'], c['F e. NN0'], c['A e. Tbl']
    l0 = s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph)
    lfz = s([l0, w.inst('nn0fz0')], 'sylib', '( %s -> L e. ( 0 ... L ) )' % ph)
    q = s([s([s([], 'id', '( %s -> %s )' % (ph, ph)), lfz], 'jca', '( %s -> ( %s /\\ L e. ( 0 ... L ) ) )' % (ph, ph)), w.inst('ttaccs')], 'syl',
          '( %s -> %s )' % (ph, QA('L')))
    AL = ACCS('L')
    alt = s([q], 'simp1d', '( %s -> %s e. Tbl )' % (ph, AL))
    dq = s([q], 'simp3d', '( %s -> %s = %s )' % (ph, DG1, DG('( L - L )', AL)))
    ll = s([s([ln], 'nncnd', '( %s -> L e. CC )' % ph)], 'subidd', '( %s -> ( L - L ) = 0 )' % ph)
    r1, n1 = w.rewrite(DG('( L - L )', AL), {'( L - L )': ('0', ll)}, ph)
    LFA = '( ( L e. NN /\\ F e. NN0 ) /\\ A e. Tbl )'
    lfa = s([s([ln, fn], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % ph), at], 'jca', '( %s -> %s )' % (ph, LFA))
    g0 = s([s([lfa, alt], 'jca', '( %s -> ( %s /\\ %s e. Tbl ) )' % (ph, LFA, AL)), w.inst('dpgo0')], 'syl',
           '( %s -> ( ( ( ( L DpGo F ) ` A ) ` 0 ) ` %s ) = <. %s , 0 >. )' % (ph, AL, AL))
    f0 = s([g0], 'fveq2d', '( %s -> %s = ( 1st ` <. %s , 0 >. ) )' % (ph, n1, AL))
    o0 = s([alt, closed(w, ph, 'c0ex', '0 e. _V'), w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , 0 >. ) = %s )' % (ph, AL, AL))
    e1 = s([s([s([dq, r1], 'eqtrd', '( %s -> %s = %s )' % (ph, DG1, n1)), f0], 'eqtrd', '( %s -> %s = ( 1st ` <. %s , 0 >. ) )' % (ph, DG1, AL)), o0], 'eqtrd',
           '( %s -> %s = %s )' % (ph, DG1, AL))
    SND = '( ( 2nd ` ( ( ( ( L DpGo F ) ` A ) ` L ) ` %s ) ) + 1 )' % ACC0
    dv = s([lfa, w.inst('dpstepval')], 'syl', '( %s -> ( ( L DpStep F ) ` A ) = <. %s , %s >. )' % (ph, DG1, SND))
    f1 = s([dv], 'fveq2d', '( %s -> ( 1st ` ( ( L DpStep F ) ` A ) ) = ( 1st ` <. %s , %s >. ) )' % (ph, DG1, SND))
    o1 = s([s([s([], 'fvex', '%s e. _V' % DG1)], 'a1i', '( %s -> %s e. _V )' % (ph, DG1)), s([s([], 'ovex', '%s e. _V' % SND)], 'a1i', '( %s -> %s e. _V )' % (ph, SND)),
            w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, DG1, SND, DG1))
    w.qed([s([f1, o1], 'eqtrd', '( %s -> ( 1st ` ( ( L DpStep F ) ` A ) ) = %s )' % (ph, DG1)), e1], 'eqtrd', ST_ACL)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
