"""T12: verifyF at the machine (Step5.lean ` verifyF_le_B ` ; blueprint D4).

  t12prodle  ` ( 1st ( ProdL W ) ) <_ 2 ^ ( # W x. b ) ` for entries below ` 2 ^ b ` (word induction; Lean ` prodL_le_two_pow ` )
  t12ifand   ` if ( ph , if ( ps , 1 , 0 ) , 0 ) = if ( ( ph /\\ ps ) , 1 , 0 ) `
  t12ifand2  ` if ( ph , if ( ps , A , (/) ) , (/) ) = if ( ( ph /\\ ps ) , A , (/) ) `
  t12verfl   the machine's accumulator read as a flag is ` ( 1st ( m Verify S ) ) ` (~ verifyval , ~ t12kofl under allPrime)
  tmivera    the first half: ` pushNum 1 1 ; nodupTDF ; accAnd ; allPrimeTDF ; accAnd ; prodLF ; dup ; cmpFrag ; load ; accAnd `
  tmiverb    ` verifyF_le_B ` : the first half, ` korseltTDF ; accAnd ; listLen ; pushNum 6 3 ; cmpFrag ; load ; accAnd ;
             isZero ; load ; dropNum 1 `

    MM_DB=sorties/t12.mm python3 tools/gen/t12_o_ver.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq, nlinarith
from cl import Closure
from t7_e_cmp import machine, togk, letgk, lamty
from t7lib import mval, not1o, ifex_closed
from t7_h_iz import lset_val, lset_ty
from t10_n_rgf import tmbn
from t10_d_dot import cls_to, load_nfl, skip_ty
from t10_e_doa import lift_from
from t10_u_s2s import expose
from a4alib import projeq, paircl, family, subst
import t8alib as A8
import t7c_h_lst as LST
from t12_j_acc import notif_fleq
from t12_k_ko import ifo_bi, KOFLAG, ANDW as ANDW_KO, KT_I
import t12_k_ko as KO
import t12_l_ap as AP
import t12_n_nd as ND
from t12_h_sc import linarith_eq as HS_lineq
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
only = SEL
TB = lambda x: '( TMB ` %s )' % x
NW = '( # ` W )'
ND1 = '( 1st ` ( NodupTD ` W ) )'
ND2 = '( 2nd ` ( NodupTD ` W ) )'
AP1 = '( 1st ` ( AllPrimeTD ` W ) )'
AP2 = '( 2nd ` ( AllPrimeTD ` W ) )'
PL1 = '( 1st ` ( ProdL ` W ) )'
PL2 = '( 2nd ` ( ProdL ` W ) )'
KO1 = '( 1st ` ( F KorseltTD W ) )'
KO2 = '( 2nd ` ( F KorseltTD W ) )'
KOF = KOFLAG
VER_ = '( F Verify W )'
c1 = '%s = 1o' % ND1
ACC1 = 'if ( %s , 1 , 0 )' % c1
c2 = '%s = 1o' % AP1
ACC2 = 'if ( %s , %s , 0 )' % (c2, ACC1)
V3 = 'if ( %s = F , 1o , (/) )' % PL1
c3 = '%s = 1o' % V3
ACC3 = 'if ( %s , %s , 0 )' % (c3, ACC2)
c4 = '%s = 1o' % KOF
ACC4 = 'if ( %s , %s , 0 )' % (c4, ACC3)
V5 = 'if ( 3 <_ %s , 1o , (/) )' % NW
c5 = '%s = 1o' % V5
ACC5 = 'if ( %s , %s , 0 )' % (c5, ACC4)
VFLAG = 'if ( %s = 0 , (/) , 1o )' % ACC5
VX = VX_
VXT = TB(VX)
B1 = '( B + 1 )'
B37 = '( ( 3 x. B ) + 7 )'
BPL = '( ( ( 2 x. ( %s + 1 ) ) x. B ) + 4 )' % NW
VA = ('( ( ( ( %s + 1 ) x. ( ; 1 6 x. %s ) ) + ( ( %s + 1 ) x. ( 4 x. %s ) ) ) + ( ( ( %s + 1 ) x. %s ) + ( ( 8 x. %s ) + 6 ) ) )'
      % (ND2, TB(B1), AP2, TB(B37), NW, TB(BPL), VXT))
LMV = FRAGS['ver'].lmap()
FV = FRAGS['ver']
KO_ENTRY = LMV['Y9']
CONCL_VERA = TRI(CS('ver'), CLN(KO_ENTRY, S, UP('D', '1', EWg(ACC3, DK(1)))), VA)
add12('tmivera', TREE_VER, CONCL_VERA)
KOC = '( ( %s + 1 ) x. ( ; 1 6 x. %s ) )' % (KO2, TB('N'))
ACAC = '( ( 2 x. %s ) + 1 )' % VXT
E9 = LMV[FV.children[9][3]]
VC = '( %s + ( %s + %s ) )' % (VA, KOC, ACAC)
CONCL_VERC = TRI(CS('ver'), CLN(E9, S, UP('D', '1', EWg(ACC4, DK(1)))), VC)
add12('tmiverc', TREE_VER, CONCL_VERC)

ST_PRODLE = '( W e. Word NN0 -> ( ( B e. NN0 /\\ A. p e. ran W p < ( 2 ^ B ) ) -> %s <_ ( 2 ^ ( %s x. B ) ) ) )' % (PL1, NW)
ST_IFAND = 'if ( ph , if ( ps , 1 , 0 ) , 0 ) = if ( ( ph /\\ ps ) , 1 , 0 )'
ST_IFAND2 = 'if ( ph , if ( ps , A , (/) ) , (/) ) = if ( ( ph /\\ ps ) , A , (/) )'
ST_VERFL = '( ( ( F e. NN0 /\\ W e. Word NN0 ) /\\ A. a e. ran W 1 <_ a ) -> %s = ( 1st ` %s ) )' % (VFLAG, VER_)


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


# ------------------------------------------------------------ the product bound (word induction, ~ algwrdi)
PHI_P = '( ( B e. NN0 /\\ A. p e. ran s p < ( 2 ^ B ) ) -> ( 1st ` ( ProdL ` s ) ) <_ ( 2 ^ ( ( # ` s ) x. B ) ) )'


def _pb(w, goal):
    s = w.s
    ph = '( B e. NN0 /\\ A. p e. ran (/) p < ( 2 ^ B ) )'
    bn = s([], 'simpl', '( %s -> B e. NN0 )' % ph)
    v = s([s([s([], 'prodl0', '( ProdL ` (/) ) = <. 1 , 0 >.')], 'fveq2i', '( 1st ` ( ProdL ` (/) ) ) = ( 1st ` <. 1 , 0 >. )'),
           s([s([], '1ex', '1 e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. 1 , 0 >. ) = 1')], 'eqtri', '( 1st ` ( ProdL ` (/) ) ) = 1')
    h0 = s([s([s([], 'hash0', '( # ` (/) ) = 0')], 'oveq1i', '( ( # ` (/) ) x. B ) = ( 0 x. B )'), s([s([bn], 'nn0cnd', '( %s -> B e. CC )' % ph)], 'mul02d', '( %s -> ( 0 x. B ) = 0 )' % ph)],
            'eqtrid', '( %s -> ( ( # ` (/) ) x. B ) = 0 )' % ph)
    e = s([s([h0], 'oveq2d', '( %s -> ( 2 ^ ( ( # ` (/) ) x. B ) ) = ( 2 ^ 0 ) )' % ph), s([s([s([], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)],
          'eqtrd', '( %s -> ( 2 ^ ( ( # ` (/) ) x. B ) ) = 1 )' % ph)
    l1 = s([closed(w, ph, '1le1', '1 <_ 1'), e], 'breqtrrd', '( %s -> 1 <_ ( 2 ^ ( ( # ` (/) ) x. B ) ) )' % ph)
    w.qed([s([v], 'a1i', '( %s -> ( 1st ` ( ProdL ` (/) ) ) = 1 )' % ph), l1], 'eqbrtrd', goal)


def _ps(w, A, ih, co):
    s = w.s
    CSV = '( <" P "> ++ V )'
    vs = s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = s([], 'simp3', '( %s -> %s )' % (A, ih))
    hy = '( B e. NN0 /\\ A. p e. ran %s p < ( 2 ^ B ) )' % CSV
    pc = '( %s /\\ %s )' % (A, hy)
    L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pc, concl(w, A, st)))
    bn = s([s([], 'simpr', '( %s -> %s )' % (pc, hy))], 'simpld', '( %s -> B e. NN0 )' % pc)
    ral = s([s([], 'simpr', '( %s -> %s )' % (pc, hy))], 'simprd', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (pc, CSV))
    rc = s([L(pn), L(vs), w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (pc, CSV))
    r1 = s([s([rc], 'raleqdv', '( %s -> ( A. p e. ran %s p < ( 2 ^ B ) <-> A. p e. ( { P } u. ran V ) p < ( 2 ^ B ) ) )' % (pc, CSV)), ral], 'mpbid',
           '( %s -> A. p e. ( { P } u. ran V ) p < ( 2 ^ B ) )' % pc)
    r2 = s([r1, s([], 'ralunb', '( A. p e. ( { P } u. ran V ) p < ( 2 ^ B ) <-> ( A. p e. { P } p < ( 2 ^ B ) /\\ A. p e. ran V p < ( 2 ^ B ) ) )')], 'sylib',
           '( %s -> ( A. p e. { P } p < ( 2 ^ B ) /\\ A. p e. ran V p < ( 2 ^ B ) ) )' % pc)
    rsn = s([s([L(pn)], 'elexd', '( %s -> P e. _V )' % pc), s([s([], 'breq1', '( p = P -> ( p < ( 2 ^ B ) <-> P < ( 2 ^ B ) ) )')], 'ralsng',
                                                                 '( P e. _V -> ( A. p e. { P } p < ( 2 ^ B ) <-> P < ( 2 ^ B ) ) )')], 'syl',
            '( %s -> ( A. p e. { P } p < ( 2 ^ B ) <-> P < ( 2 ^ B ) ) )' % pc)
    plt = s([s([r2], 'simpld', '( %s -> A. p e. { P } p < ( 2 ^ B ) )' % pc), rsn], 'mpbid', '( %s -> P < ( 2 ^ B ) )' % pc)
    ihc = s([L(ihs), s([bn, s([r2], 'simprd', '( %s -> A. p e. ran V p < ( 2 ^ B ) )' % pc)], 'jca', '( %s -> ( B e. NN0 /\\ A. p e. ran V p < ( 2 ^ B ) ) )' % pc)], 'mpd',
            '( %s -> ( 1st ` ( ProdL ` V ) ) <_ ( 2 ^ ( ( # ` V ) x. B ) ) )' % pc)
    PV_ = '( 1st ` ( ProdL ` V ) )'
    cs = s([L(pn), L(vs), w.inst('prodlcs')], 'syl2anc', '( %s -> ( ProdL ` %s ) = <. ( P x. %s ) , ( ( 2nd ` ( ProdL ` V ) ) + 1 ) >. )' % (pc, CSV, PV_))
    pcl = s([L(vs), w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` V ) e. ( NN0 X. NN0 ) )' % pc)
    pa, pb_ = paircl(w, pc, '( ProdL ` V )', pcl, 'NN0', 'NN0')
    xa = s([L(pn), pa], 'nn0mulcld', '( %s -> ( P x. %s ) e. NN0 )' % (pc, PV_))
    xb = s([pb_, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( ProdL ` V ) ) + 1 ) e. NN0 )' % pc)
    f1 = projeq(w, pc, '( ProdL ` %s )' % CSV, cs, '( P x. %s )' % PV_, '( ( 2nd ` ( ProdL ` V ) ) + 1 )', xa, xb, 1)
    cl = Closure(w, pc, {'B': ('NN0', bn), 'P': ('NN0', L(pn))})
    cl.leaf(PV_, 'NN0', pa)
    nv = s([L(vs), w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % pc)
    cl.leaf('( # ` V )', 'NN0', nv)
    P2B = '( 2 ^ B )'
    P2V = '( 2 ^ ( ( # ` V ) x. B ) )'
    cl.atom(P2B); cl.atom(P2V)
    p2bn = s([closed(w, pc, '2nn0', '2 e. NN0'), bn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, P2B))
    p2vn = s([closed(w, pc, '2nn0', '2 e. NN0'), cl.mem('( ( # ` V ) x. B )', 'NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, P2V))
    cl.leaf(P2B, 'NN0', p2bn); cl.leaf(P2V, 'NN0', p2vn)
    ple = s([cl.mem('P', 'RR'), cl.mem(P2B, 'RR'), plt], 'ltled', '( %s -> P <_ %s )' % (pc, P2B))
    j1 = s([s([s([cl.mem('P', 'RR'), cl.ge0('P')], 'jca', '( %s -> ( P e. RR /\\ 0 <_ P ) )' % pc), cl.mem(P2B, 'RR')], 'jca', '( %s -> ( ( P e. RR /\\ 0 <_ P ) /\\ %s e. RR ) )' % (pc, P2B)),
            s([s([cl.mem(PV_, 'RR'), cl.ge0(PV_)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (pc, PV_, PV_)), cl.mem(P2V, 'RR')], 'jca',
              '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR ) )' % (pc, PV_, PV_, P2V))], 'jca',
           '( %s -> ( ( ( P e. RR /\\ 0 <_ P ) /\\ %s e. RR ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR ) ) )' % (pc, P2B, PV_, PV_, P2V))
    mle = s([j1, s([ple, ihc], 'jca', '( %s -> ( P <_ %s /\\ %s <_ %s ) )' % (pc, P2B, PV_, P2V)), w.inst('lemul12a')], 'sylc',
            '( %s -> ( P x. %s ) <_ ( %s x. %s ) )' % (pc, PV_, P2B, P2V))
    ea = s([closed(w, pc, '2cn', '2 e. CC'), bn, cl.mem('( ( # ` V ) x. B )', 'NN0'), w.inst('expadd')], 'syl3anc',
           '( %s -> ( 2 ^ ( B + ( ( # ` V ) x. B ) ) ) = ( %s x. %s ) )' % (pc, P2B, P2V))
    lc = s([L(pn), L(vs), w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (pc, CSV))
    ee = s([s([lc], 'oveq1d', '( %s -> ( ( # ` %s ) x. B ) = ( ( ( # ` V ) + 1 ) x. B ) )' % (pc, CSV)),
            HS_lineq(w, pc, '( ( ( # ` V ) + 1 ) x. B )', '( B + ( ( # ` V ) x. B ) )', [], cl, products=True)], 'eqtrd',
           '( %s -> ( ( # ` %s ) x. B ) = ( B + ( ( # ` V ) x. B ) ) )' % (pc, CSV))
    e2 = s([s([ee], 'oveq2d', '( %s -> ( 2 ^ ( ( # ` %s ) x. B ) ) = ( 2 ^ ( B + ( ( # ` V ) x. B ) ) ) )' % (pc, CSV)), ea], 'eqtrd',
           '( %s -> ( 2 ^ ( ( # ` %s ) x. B ) ) = ( %s x. %s ) )' % (pc, CSV, P2B, P2V))
    fin = s([s([f1, mle], 'eqbrtrd', '( %s -> ( 1st ` ( ProdL ` %s ) ) <_ ( %s x. %s ) )' % (pc, CSV, P2B, P2V)), e2], 'breqtrrd',
            '( %s -> ( 1st ` ( ProdL ` %s ) ) <_ ( 2 ^ ( ( # ` %s ) x. B ) ) )' % (pc, CSV, CSV))
    w.qed([fin], 'ex', '( %s -> %s )' % (A, co))


def t12prodle():
    return family(run, 't12prodle', PHI_P, _pb, _ps, target='W',
                  desc='The product of a list of numbers below ` 2 ^ b ` is at most ` 2 ^ ( # l x. b ) ` (Lean ` prodL_le_two_pow ` ; '
                       '~ prodlcs , ~ lemul12a , ~ expadd ).', only=only)


# ------------------------------------------------------------ the if lemmas
def t12ifand():
    lab = 't12ifand'
    w = W(lab, 'A conditional accumulator nests as a conjunction (the machine\'s ` accAnd ` in the accumulator).')
    s = w.s
    L = 'if ( ph , if ( ps , 1 , 0 ) , 0 )'
    R = 'if ( ( ph /\\ ps ) , 1 , 0 )'
    a1 = s([], 'iftrue', '( ph -> %s = if ( ps , 1 , 0 ) )' % L)
    b1 = s([s([], 'ibar', '( ph -> ( ps <-> ( ph /\\ ps ) ) )')], 'ifbid', '( ph -> if ( ps , 1 , 0 ) = %s )' % R)
    t1 = s([a1, b1], 'eqtrd', '( ph -> %s = %s )' % (L, R))
    a2 = s([], 'iffalse', '( -. ph -> %s = 0 )' % L)
    b2 = s([s([s([], 'simpl', '( ( ph /\\ ps ) -> ph )')], 'con3i', '( -. ph -> -. ( ph /\\ ps ) )')], 'iffalsed', '( -. ph -> %s = 0 )' % R)
    t2 = s([a2, b2], 'eqtr4d', '( -. ph -> %s = %s )' % (L, R))
    w.qed([t1, t2], 'pm2.61i', ST_IFAND)
    return w.run()


def t12ifand2():
    lab = 't12ifand2'
    w = W(lab, 'A nested conditional on ` (/) ` as a conjunction (A1b\'s ` verify ` value).')
    s = w.s
    L = 'if ( ph , if ( ps , A , (/) ) , (/) )'
    R = 'if ( ( ph /\\ ps ) , A , (/) )'
    a1 = s([], 'iftrue', '( ph -> %s = if ( ps , A , (/) ) )' % L)
    b1 = s([s([], 'ibar', '( ph -> ( ps <-> ( ph /\\ ps ) ) )')], 'ifbid', '( ph -> if ( ps , A , (/) ) = %s )' % R)
    t1 = s([a1, b1], 'eqtrd', '( ph -> %s = %s )' % (L, R))
    a2 = s([], 'iffalse', '( -. ph -> %s = (/) )' % L)
    b2 = s([s([s([], 'simpl', '( ( ph /\\ ps ) -> ph )')], 'con3i', '( -. ph -> -. ( ph /\\ ps ) )')], 'iffalsed', '( -. ph -> %s = (/) )' % R)
    t2 = s([a2, b2], 'eqtr4d', '( -. ph -> %s = %s )' % (L, R))
    w.qed([t1, t2], 'pm2.61i', ST_IFAND2)
    return w.run()


def ifand_chain(w, ph, conds):
    """( ph -> ACC = if ( C , 1 , 0 ) ) for ACC = if ( c_n , ... if ( c_1 , 1 , 0 ) ... , 0 ) and C = ( c_n /\\ ( ... /\\ c_1 ) );
    conds innermost first; returns (step, ACC text, C text)"""
    s = w.s
    acc = 'if ( %s , 1 , 0 )' % conds[0]
    C = conds[0]
    st = s([], 'eqidd', '( %s -> %s = %s )' % (ph, acc, acc))
    for c in conds[1:]:
        acc2 = 'if ( %s , %s , 0 )' % (c, acc)
        C2 = '( %s /\\ %s )' % (c, C)
        e1 = s([st], 'ifeq1d', '( %s -> %s = if ( %s , if ( %s , 1 , 0 ) , 0 ) )' % (ph, acc2, c, C))
        e2 = s([s([], 't12ifand', 'if ( %s , if ( %s , 1 , 0 ) , 0 ) = if ( %s , 1 , 0 )' % (c, C, C2))], 'a1i',
                '( %s -> if ( %s , if ( %s , 1 , 0 ) , 0 ) = if ( %s , 1 , 0 ) )' % (ph, c, C, C2))
        st = s([e1, e2], 'eqtrd', '( %s -> %s = if ( %s , 1 , 0 ) )' % (ph, acc2, C2))
        acc, C = acc2, C2
    return st, acc, C


def ifz_flag(w, ph, C):
    """( ph -> if ( if ( C , 1 , 0 ) = 0 , (/) , 1o ) = if ( C , 1o , (/) ) )"""
    s = w.s
    ACC = 'if ( %s , 1 , 0 )' % C
    L = 'if ( %s = 0 , (/) , 1o )' % ACC
    R = 'if ( %s , 1o , (/) )' % C
    pt, pn = '( %s /\\ %s )' % (ph, C), '( %s /\\ -. %s )' % (ph, C)
    a1 = s([s([], 'simpr', '( %s -> %s )' % (pt, C))], 'iftrued', '( %s -> %s = 1 )' % (pt, ACC))
    n1 = s([s([a1], 'eqeq1d', '( %s -> ( %s = 0 <-> 1 = 0 ) )' % (pt, ACC)), s([closed(w, pt, 'ax-1ne0', '1 =/= 0')], 'neneqd', '( %s -> -. 1 = 0 )' % pt)], 'mtbird',
           '( %s -> -. %s = 0 )' % (pt, ACC))
    t1 = s([s([n1], 'iffalsed', '( %s -> %s = 1o )' % (pt, L)), s([s([], 'simpr', '( %s -> %s )' % (pt, C))], 'iftrued', '( %s -> %s = 1o )' % (pt, R))], 'eqtr4d',
           '( %s -> %s = %s )' % (pt, L, R))
    a2 = s([s([], 'simpr', '( %s -> -. %s )' % (pn, C))], 'iffalsed', '( %s -> %s = 0 )' % (pn, ACC))
    t2 = s([s([a2], 'iftrued', '( %s -> %s = (/) )' % (pn, L)), s([s([], 'simpr', '( %s -> -. %s )' % (pn, C))], 'iffalsed', '( %s -> %s = (/) )' % (pn, R))], 'eqtr4d',
           '( %s -> %s = %s )' % (pn, L, R))
    return s([t1, t2], 'pm2.61dan', '( %s -> %s = %s )' % (ph, L, R))


def t12verfl():
    lab = 't12verfl'
    T = (('F e. NN0', 'W e. Word NN0'), 'A. a e. ran W 1 <_ a')
    ph = cj(T)
    w = W(lab, 'The machine\'s verify flag: the accumulator of the five tests (nodup, allPrime, the product, korselt, the length), '
               'read as ` acc =/= 0 ` , is A1b\'s ` ( 1st ( m Verify S ) ) ` (~ verifyval ; the korselt test is Lean\'s under '
               'allPrime, ~ t12kofl , ~ prmuz2 ).')
    s = w.s
    c = Ctx(w, ph, T)
    fn, ww, r1 = c['F e. NN0'], c['W e. Word NN0'], c['A. a e. ran W 1 <_ a']
    # the accumulator as one conjunction
    ac, acc, C = ifand_chain(w, ph, [c1, c2, c3, c4, c5])
    assert acc == ACC5, acc
    fl1 = s([s([ac], 'eqeq1d', '( %s -> ( %s = 0 <-> if ( %s , 1 , 0 ) = 0 ) )' % (ph, ACC5, C))], 'ifbid', '( %s -> %s = if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o ) )' % (ph, VFLAG, C))
    fl2 = s([fl1, ifz_flag(w, ph, C)], 'eqtrd', '( %s -> %s = if ( %s , 1o , (/) ) )' % (ph, VFLAG, C))
    # ( 1st Verify ) as one conjunction
    L3 = '3 <_ %s' % NW
    IF3 = 'if ( %s , %s , (/) )' % (c3, KO1)
    IF2 = 'if ( %s , %s , (/) )' % (c2, IF3)
    IF1 = 'if ( %s , %s , (/) )' % (c1, IF2)
    IFV = 'if ( %s , %s , (/) )' % (L3, IF1)
    CST = '( ( ( ( %s + %s ) + %s ) + %s ) + 2 )' % (ND2, AP2, PL2, KO2)
    vv = s([fn, ww, w.inst('verifyval')], 'syl2anc', '( %s -> %s = <. %s , %s >. )' % (ph, VER_, IFV, CST))
    vcl = s([fn, ww, w.inst('verifycl')], 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (ph, VER_))
    va, vb = paircl(w, ph, VER_, vcl, '2o', 'NN0')
    ifx = s([s([], 'ifex', '%s e. _V' % IFV)], 'a1i', '( %s -> %s e. _V )' % (ph, IFV))
    cx = s([s([], 'ovex', '%s e. _V' % CST)], 'a1i', '( %s -> %s e. _V )' % (ph, CST))
    v1 = projeq(w, ph, VER_, vv, IFV, CST, ifx, cx, 1)
    # KO1 = if ( KO1 = 1o , 1o , (/) )
    kcl = s([s([fn, ww, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( F KorseltTD W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (ph, KO1))
    k2 = s([kcl, s([s([], 'df2o3', '2o = { (/) , 1o }')], 'a1i', '( %s -> 2o = { (/) , 1o } )' % ph)], 'eleqtrd', '( %s -> %s e. { (/) , 1o } )' % (ph, KO1))
    ko = s([k2, w.inst('elpri')], 'syl', '( %s -> ( %s = (/) \\/ %s = 1o ) )' % (ph, KO1, KO1))
    KOI = 'if ( %s = 1o , 1o , (/) )' % KO1
    pt = '( %s /\\ %s = 1o )' % (ph, KO1)
    pz = '( %s /\\ %s = (/) )' % (ph, KO1)
    kt = s([s([], 'simpr', '( %s -> %s = 1o )' % (pt, KO1)), s([s([], 'simpr', '( %s -> %s = 1o )' % (pt, KO1))], 'iftrued', '( %s -> %s = 1o )' % (pt, KOI))], 'eqtr4d',
           '( %s -> %s = %s )' % (pt, KO1, KOI))
    n0 = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
    nz = s([s([n0], 'a1i', '( %s -> -. (/) = 1o )' % pz), s([s([], 'simpr', '( %s -> %s = (/) )' % (pz, KO1))], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (pz, KO1))],
           'mtbird', '( %s -> -. %s = 1o )' % (pz, KO1))
    kz = s([s([], 'simpr', '( %s -> %s = (/) )' % (pz, KO1)), s([nz], 'iffalsed', '( %s -> %s = (/) )' % (pz, KOI))], 'eqtr4d', '( %s -> %s = %s )' % (pz, KO1, KOI))
    koi = s([s([kz], 'ex', '( %s -> ( %s = (/) -> %s = %s ) )' % (ph, KO1, KO1, KOI)), s([kt], 'ex', '( %s -> ( %s = 1o -> %s = %s ) )' % (ph, KO1, KO1, KOI)), ko], 'mpjaod',
            '( %s -> %s = %s )' % (ph, KO1, KOI))
    ck = '%s = 1o' % KO1
    # IF3 = if ( c3 , KOI , (/) ) = if ( ( c3 /\\ ck ) , 1o , (/) )
    e3 = s([s([koi], 'ifeq1d', '( %s -> %s = if ( %s , %s , (/) ) )' % (ph, IF3, c3, KOI)),
            s([s([], 't12ifand2', 'if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) )' % (c3, ck, c3, ck))], 'a1i',
              '( %s -> if ( %s , %s , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, c3, KOI, c3, ck))], 'eqtrd',
           '( %s -> %s = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, IF3, c3, ck))
    Cv = '( %s /\\ %s )' % (c3, ck)
    e2 = s([s([e3], 'ifeq1d', '( %s -> %s = if ( %s , if ( %s , 1o , (/) ) , (/) ) )' % (ph, IF2, c2, Cv)),
            s([s([], 't12ifand2', 'if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) )' % (c2, Cv, c2, Cv))], 'a1i',
              '( %s -> if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, c2, Cv, c2, Cv))], 'eqtrd',
           '( %s -> %s = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, IF2, c2, Cv))
    Cv = '( %s /\\ %s )' % (c2, Cv)
    e1 = s([s([e2], 'ifeq1d', '( %s -> %s = if ( %s , if ( %s , 1o , (/) ) , (/) ) )' % (ph, IF1, c1, Cv)),
            s([s([], 't12ifand2', 'if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) )' % (c1, Cv, c1, Cv))], 'a1i',
              '( %s -> if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, c1, Cv, c1, Cv))], 'eqtrd',
           '( %s -> %s = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, IF1, c1, Cv))
    Cv = '( %s /\\ %s )' % (c1, Cv)
    e0 = s([s([e1], 'ifeq1d', '( %s -> %s = if ( %s , if ( %s , 1o , (/) ) , (/) ) )' % (ph, IFV, L3, Cv)),
            s([s([], 't12ifand2', 'if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) )' % (L3, Cv, L3, Cv))], 'a1i',
              '( %s -> if ( %s , if ( %s , 1o , (/) ) , (/) ) = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, L3, Cv, L3, Cv))], 'eqtrd',
           '( %s -> %s = if ( ( %s /\\ %s ) , 1o , (/) ) )' % (ph, IFV, L3, Cv))
    Cv = '( %s /\\ %s )' % (L3, Cv)
    CvT = (L3, (c1, (c2, (c3, ck))))
    assert cj(CvT) == Cv
    CT = (c5, (c4, (c3, (c2, c1))))
    assert cj(CT) == C
    # C <-> Cv : c5 <-> L3 ; under c2 , c4 <-> ck
    b5 = ifo_bi(w, ph, L3)                       # ( ph -> ( c5 <-> L3 ) )
    # under c2 every entry is prime hence at least 2 : t12kofl
    pc2 = '( %s /\\ %s )' % (ph, c2)
    ap = s([s([ww], 'adantr', '( %s -> W e. Word NN0 )' % pc2), w.inst('allprimetdfst')], 'syl', '( %s -> ( %s <-> A. p e. ran W p e. Prime ) )' % (pc2, c2))
    prm = s([s([], 'simpr', '( %s -> %s )' % (pc2, c2)), ap], 'mpbid', '( %s -> A. p e. ran W p e. Prime )' % pc2)
    pp = '( %s /\\ p e. ran W )' % pc2
    pr = s([prm], 'r19.21bi', '( %s -> p e. Prime )' % pp)
    two = s([s([pr, w.inst('prmuz2')], 'syl', '( %s -> p e. ( ZZ>= ` 2 ) )' % pp), w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )' % pp)
    two2 = s([two], 'simp3d', '( %s -> 2 <_ p )' % pp)
    r2 = s([two2], 'ralrimiva', '( %s -> A. p e. ran W 2 <_ p )' % pc2)
    cb = s([s([s([], 'breq2', '( p = a -> ( 2 <_ p <-> 2 <_ a ) )')], 'cbvralvw', '( A. p e. ran W 2 <_ p <-> A. a e. ran W 2 <_ a )')], 'a1i',
           '( %s -> ( A. p e. ran W 2 <_ p <-> A. a e. ran W 2 <_ a ) )' % pc2)
    r2a = s([r2, cb], 'mpbid', '( %s -> A. a e. ran W 2 <_ a )' % pc2)
    kfl = s([s([s([fn], 'adantr', '( %s -> F e. NN0 )' % pc2), s([ww], 'adantr', '( %s -> W e. Word NN0 )' % pc2)], 'jca', '( %s -> ( F e. NN0 /\\ W e. Word NN0 ) )' % pc2),
             r2a, w.inst('t12kofl')], 'syl2anc', '( %s -> %s = %s )' % (pc2, KO1, KOF))
    b4 = s([kfl], 'eqeq1d', '( %s -> ( %s <-> %s ) )' % (pc2, ck, c4))     # ( ( ph /\\ c2 ) -> ( ck <-> c4 ) )
    # C -> Cv
    pC = '( %s /\\ %s )' % (ph, C)
    cC = Ctx(w, pC, (T, CT))
    aC = cC[c2]
    l3 = s([cC[c5], s([b5], 'adantr', '( %s -> ( %s <-> %s ) )' % (pC, c5, L3))], 'mpbid', '( %s -> %s )' % (pC, L3))
    kC = s([cC[c4], s([s([s([], 'simpl', '( %s -> %s )' % (pC, ph)), aC], 'jca', '( %s -> %s )' % (pC, pc2)), b4], 'syl', '( %s -> ( %s <-> %s ) )' % (pC, ck, c4))],
           'mpbird', '( %s -> %s )' % (pC, ck))
    fwd = s([Bld(w, pC, cC, {L3: l3, ck: kC})(CvT)], 'ex', '( %s -> ( %s -> %s ) )' % (ph, C, Cv))
    pV = '( %s /\\ %s )' % (ph, Cv)
    cV = Ctx(w, pV, (T, CvT))
    aV = cV[c2]
    c5v = s([cV[L3], s([b5], 'adantr', '( %s -> ( %s <-> %s ) )' % (pV, c5, L3))], 'mpbird', '( %s -> %s )' % (pV, c5))
    c4v = s([cV[ck], s([s([s([], 'simpl', '( %s -> %s )' % (pV, ph)), aV], 'jca', '( %s -> %s )' % (pV, pc2)), b4], 'syl', '( %s -> ( %s <-> %s ) )' % (pV, ck, c4))],
            'mpbid', '( %s -> %s )' % (pV, c4))
    bwd = s([Bld(w, pV, cV, {c5: c5v, c4: c4v})(CT)], 'ex', '( %s -> ( %s -> %s ) )' % (ph, Cv, C))
    bi = s([fwd, bwd], 'impbid', '( %s -> ( %s <-> %s ) )' % (ph, C, Cv))
    fin = s([fl2, s([bi], 'ifbid', '( %s -> if ( %s , 1o , (/) ) = if ( %s , 1o , (/) ) )' % (ph, C, Cv)), s([v1, e0], 'eqtrd', '( %s -> ( 1st ` %s ) = if ( %s , 1o , (/) ) )' % (ph, VER_, Cv))],
            '3eqtr4d' if False else 'id', '') if False else None
    fin = s([s([fl2, s([bi], 'ifbid', '( %s -> if ( %s , 1o , (/) ) = if ( %s , 1o , (/) ) )' % (ph, C, Cv))], 'eqtrd', '( %s -> %s = if ( %s , 1o , (/) ) )' % (ph, VFLAG, Cv)),
             s([v1, e0], 'eqtrd', '( %s -> ( 1st ` %s ) = if ( %s , 1o , (/) ) )' % (ph, VER_, Cv))], 'eqtr4d', '( %s -> %s = ( 1st ` %s ) )' % (ph, VFLAG, VER_))
    w.qed([fin, w.inst('biid')], 'mpbi', ST_VERFL)
    return w.run()



# ------------------------------------------------------------ the runs
class Ver(Base):
    def __init__(self, w, ph, T, deep=()):
        c0 = Ctx(w, ph, T)
        ww, fn, bn, nn = c0['W e. Word NN0'], c0['F e. NN0'], c0['B e. NN0'], c0['N e. NN0']
        xw, yw = c0[WG('X')], c0[WG('Y')]
        Base.__init__(self, w, ph, T, N8, 'ver', {'4': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), '7': (EWg('F', 'Y'), ewg_(w, ph, 'F', fn, 'Y', yw))})
        for j_ in deep:
            self.deep('ver', j_)          # the callees' own labels (T9's ~ tmiprlb reads its entry label from the antecedent)
        s = w.s
        self.ww, self.fn, self.bn, self.nn, self.xw, self.yw = ww, fn, bn, nn, xw, yw
        c = self.c
        self.ral, self.nwlt, self.flt = c[RALB('W', 'B')], c[LT2('( # ` W )', 'B')], c[LT2('F', 'N')]
        self.ble, self.f1, self.a1 = c['B <_ N'], c['1 <_ F'], c['A. a e. ran W 1 <_ a']
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
        self.cl = Closure(w, ph, {'B': ('NN0', bn), 'N': ('NN0', nn), 'F': ('NN0', fn)})
        self.cl.leaf(NW, 'NN0', self.nw)
        self.vxn = self.cl.mem(VX, 'NN0')
        for x in ('B', 'N', VX, B1, B37, BPL):
            self.cl.atom('( 2 ^ %s )' % x)
            self.cl.leaf(TB(x), 'NN0', tmbn(w, ph, x, self.cl.mem(x, 'NN0')))
        self.d1 = self.S0.vals['1'][2]
        # the bit bounds against VX
        self.vx8 = linarith(w, ph, [self.cl.ge0('B'), self.cl.ge0('N'), self.cl.ge0(NW)], '8 <_ %s' % VX, closure=self.cl, products=True)
        self.p2 = {}
        self.tbm = {}

    def pw_le(self, e, hyps=()):
        """( ph -> 2 ^ e <_ 2 ^ VX ) and ( ph -> TMB e <_ TMB VX )"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        if e in self.p2:
            return self.p2[e], self.tbm[e]
        en = cl.mem(e, 'NN0')
        le = linarith(w, ph, [cl.ge0('B'), cl.ge0('N'), cl.ge0(NW)] + list(hyps), '%s <_ %s' % (e, VX), closure=cl, products=True)
        u = s([s([s([en], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e)), s([self.vxn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, VX)), le], '3jca',
                 '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (ph, e, VX, e, VX)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, VX, e))
        p = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ %s ) <_ ( 2 ^ %s ) )' % (ph, e, VX))
        m = s([en, self.vxn, le, w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB(e), VXT))
        self.p2[e], self.tbm[e] = p, m
        return p, m

    def acc_facts(self, ACC, parts):
        """( ph -> ACC e. NN0 ) , ( ph -> ACC < 2 ^ VX ) for the nested accumulator ACC (parts: the conditions, outermost first)"""
        w, ph, s, cl = self.w, self.ph, self.w.s, self.cl
        # ACC <_ 1 by peeling the ifs: if ( c , X , 0 ) <_ 1 from X <_ 1
        def le1(t, conds):
            if not conds:
                # t = if ( c1 , 1 , 0 )
                pt, pn = '( %s /\\ %s )' % (ph, c1), '( %s /\\ -. %s )' % (ph, c1)
                l1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, c1))], 'iftrued', '( %s -> %s = 1 )' % (pt, t)), closed(w, pt, '1le1', '1 <_ 1')], 'eqbrtrd', '( %s -> %s <_ 1 )' % (pt, t))
                l2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, c1))], 'iffalsed', '( %s -> %s = 0 )' % (pn, t)), closed(w, pn, '0le1', '0 <_ 1')], 'eqbrtrd', '( %s -> %s <_ 1 )' % (pn, t))
                an = s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, t))
                return an, s([l1, l2], 'pm2.61dan', '( %s -> %s <_ 1 )' % (ph, t))
            c = conds[0]
            inner = t[len('if ( %s , ' % c):-len(' , 0 )')]
            inn, inle = le1(inner, conds[1:])
            pt, pn = '( %s /\\ %s )' % (ph, c), '( %s /\\ -. %s )' % (ph, c)
            l1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, c))], 'iftrued', '( %s -> %s = %s )' % (pt, t, inner)), s([inle], 'adantr', '( %s -> %s <_ 1 )' % (pt, inner))], 'eqbrtrd',
                   '( %s -> %s <_ 1 )' % (pt, t))
            l2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, c))], 'iffalsed', '( %s -> %s = 0 )' % (pn, t)), closed(w, pn, '0le1', '0 <_ 1')], 'eqbrtrd', '( %s -> %s <_ 1 )' % (pn, t))
            an = s([inn, closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, t))
            return an, s([l1, l2], 'pm2.61dan', '( %s -> %s <_ 1 )' % (ph, t))
        an, le = le1(ACC, parts)
        cl.leaf(ACC, 'NN0', an)
        u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
        blt = s([u2, self.vxn, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ph, VX, VX))
        lt = linarith(w, ph, [le, blt, self.vx8], '%s < ( 2 ^ %s )' % (ACC, VX), closure=cl, products=True)
        return an, lt

    def cp(self, j):
        fn_, cks, en, exn = FV.children[j]
        return PL('P', FV.slot(j)), LMV[exn]


def cmp_load(w, ph, B, R, A_lab, E_lab, lam, Fa, Ga, fan, gan, FL, fleq_of):
    """the load after a cmpFrag: from CMPC( Fa , Ga ) into NFL( FL ) ; fleq_of(pr, rc) gives ( pr -> ( TMfl ` ( lam ` r ) ) = FL )
    from rc : ( pr -> ( TMcmp ` r ) = ( Fa Ncmp Ga ) ) and the state facts"""
    s = w.s
    CQ = CMPC(Fa, Ga)
    kw = lambda t: dict(fl=lam.split('|-> ', 1)[1][:-2].split(', ')[-1].rsplit(' >.', 6)[0]) if False else None
    pr = '( %s /\\ r e. %s )' % (ph, CQ)
    rin = s([], 'simpr', '( %s -> r e. %s )' % (pr, CQ))
    condc = lambda t: '( TMcmp ` %s ) = ( %s Ncmp %s )' % (t, Fa, Ga)
    cg, new = w.wcongr(condc('h'), {'h': 'r'}, 'h = r', {'h': s([], 'id', '( h = r -> h = r )')})
    both = s([rin, s([cg], 'elrab', '( r e. %s <-> ( r e. TMSt /\\ %s ) )' % (CQ, condc('r')))], 'sylib', '( %s -> ( r e. TMSt /\\ %s ) )' % (pr, condc('r')))
    rr = s([both], 'simpld', '( %s -> r e. TMSt )' % pr)
    rc = s([both], 'simprd', '( %s -> %s )' % (pr, condc('r')))
    flr, kwf = fleq_of(pr, rr, rc)
    NR = '( %s ` r )' % lam
    inm = A8.nfl_pack(w, pr, FL, NR, flr[0], flr[1])
    hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, CQ, lam, NFL(FL)))
    B.call(R, 'tm2flg', {'A': A_lab, 'E': E_lab, 'F': lam, 'N': CQ, "N'": NFL(FL)},
           {LTY(lam): lset_ty(w, ph, B.mk, lam, kwf), SSS(CQ): B.ss(CQ), SSS(NFL(FL)): B.ss(NFL(FL)),
            'A. r e. %s ( %s ` r ) e. %s' % (CQ, lam, NFL(FL)): hl}, [])


def tmivera():
    lab = 'tmivera'
    T = numtree(TREE_VER)
    ph = cj(T)
    w = W(lab, 'The first half of Lean\'s ` verifyF ` at the machine: ` pushNum 1 1 ` , ` nodupTDF ` (~ tmind ), ` accAnd ` (~ tmiaca ), '
               '` allPrimeTDF ` (~ tmiap ), ` accAnd ` , ` prodLF 4 5 6 2 3 ` (~ tmiprlb ), ` dup 7 6 2 ` , ` cmpFrag 5 6 ` , '
               '` load\' ( flag := decide ( cmp = .eq ) ) ` , ` accAnd ` : the accumulator on 1 holds the three tests so far, '
               'every other stack restored.')
    s = w.s
    B = Ver(w, ph, T, deep=(4,))
    c, mk, cl = B.c, B.mk, B.cl
    g = lambda k: B.S0.vals[k][2]
    ssid = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    R = B.run()
    # 1-2. pushNum 1 1
    K4 = '( <" 4 "> ++ ( D ` 1 ) )'
    g4 = B.g(K4, wg4(w, ph, DK(1), B.d1))
    B.call(R, 'tm2fpshn', {'A': LMV['Z1'], 'E': LMV['Z2'], 'K': '1', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('1'): letgk(w, ph, mk, '4', '1', closed(w, ph, 'gamma4', "4 e. Gamma'")), SSS(S): ssid}, [('1', K4, g4)])
    bg1 = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT1_))
    K41 = '( <" %s "> ++ %s )' % (BIT1_, K4)
    g41 = B.g(K41, wgcat(w, ph, '<" %s ">' % BIT1_, K4, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT1_)), g4))
    B.call(R, 'tm2fpshn', {'A': LMV['Z2'], 'E': LMV['Y1'], 'K': '1', 'Z': BIT1_, 'N': S},
           {'%s e. %s' % (BIT1_, GX('1')): s([bg1, mk['k']['1']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, BIT1_, GX('1'))), SSS(S): ssid}, [('1', K41, g41)])
    E1 = EWg('1', DK(1))
    e1 = s([s([B.d1, w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (ph, E1, K41))], 'eqcomd', '( %s -> %s = %s )' % (ph, K41, E1))
    cur, out = R.normalize(N8)
    assert out == [('1', K41)], out
    D0 = triple_D(R.cur)
    rr_, x_ = w.rewrite(D0, {K41: (E1, e1)}, ph)
    R.tri, _, R.cur, _ = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, LMV['Y1'], S, rr_, D0, x_))
    S1 = B.S0.upd('1', E1, B.g(E1, ewg_(w, ph, '1', closed(w, ph, '1nn0', '1 e. NN0'), DK(1), B.d1)))
    R.S = S1; R.chain = [('1', E1)]; R.gam[E1] = B.gam[E1]
    # 3. nodupTDF at the bit bound B + 1
    p2b1, _ = B.pw_le(B1)
    RALP0 = 'A. p e. ran W p < ( 2 ^ B )'
    cbp0 = s([s([s([], 'breq1', '( a = p -> ( a < ( 2 ^ B ) <-> p < ( 2 ^ B ) ) )')], 'cbvralvw', '( %s <-> %s )' % (RALB('W', 'B'), RALP0))], 'a1i',
             '( %s -> ( %s <-> %s ) )' % (ph, RALB('W', 'B'), RALP0))
    ralp0 = s([B.ral, cbp0], 'mpbid', '( %s -> %s )' % (ph, RALP0))
    pa = '( %s /\\ p e. ran W )' % ph
    alt = s([ralp0], 'r19.21bi', '( %s -> p < ( 2 ^ B ) )' % pa)
    u1 = s([s([s([B.bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), s([cl.mem(B1, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, B1)), linarith(w, ph, [], 'B <_ %s' % B1, closure=cl)], '3jca',
              '( %s -> ( B e. ZZ /\\ %s e. ZZ /\\ B <_ %s ) )' % (ph, B1, B1)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` B ) )' % (ph, B1))
    pbb1 = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u1, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ B ) <_ ( 2 ^ %s ) )' % (ph, B1))
    an_ = s([s([s([B.ww], 'adantr', '( %s -> W e. Word NN0 )' % pa), w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ %s ) --> NN0 )' % (pa, NW)), w.inst('frn')], 'syl',
            '( %s -> ran W C_ NN0 )' % pa)
    an = s([an_, s([], 'simpr', '( %s -> p e. ran W )' % pa)], 'sseldd', '( %s -> p e. NN0 )' % pa)
    cla = Closure(w, pa, {'p': ('NN0', an), 'B': ('NN0', s([B.bn], 'adantr', '( %s -> B e. NN0 )' % pa))})
    cla.atom('( 2 ^ B )'); cla.atom('( 2 ^ %s )' % B1)
    alt1 = linarith(w, pa, [alt, s([pbb1], 'adantr', '( %s -> ( 2 ^ B ) <_ ( 2 ^ %s ) )' % (pa, B1))], 'p < ( 2 ^ %s )' % B1, closure=cla)
    ral1p = s([alt1], 'ralrimiva', '( %s -> A. p e. ran W p < ( 2 ^ %s ) )' % (ph, B1))
    cbp1 = s([s([s([], 'breq1', '( p = a -> ( p < ( 2 ^ %s ) <-> a < ( 2 ^ %s ) ) )' % (B1, B1))], 'cbvralvw', '( A. p e. ran W p < ( 2 ^ %s ) <-> %s )' % (B1, RALB('W', B1)))], 'a1i',
             '( %s -> ( A. p e. ran W p < ( 2 ^ %s ) <-> %s ) )' % (ph, B1, RALB('W', B1)))
    ral1 = s([ral1p, cbp1], 'mpbid', '( %s -> %s )' % (ph, RALB('W', B1)))
    P, E = B.cp(0)
    B.call(R, 'tmind', {'W': 'W', 'B': B1, 'X': 'X', 'P': P, 'E': E},
           {'%s e. NN0' % B1: cl.mem(B1, 'NN0'), '1 <_ %s' % B1: linarith(w, ph, [cl.ge0('B')], '1 <_ %s' % B1, closure=cl), RALB('W', B1): ral1}, [])
    # 4. accAnd
    a1n, a1lt = B.acc_facts(ACC1, [])
    P, E = B.cp(1)
    EA1 = EWg(ACC1, DK(1))
    B.call(R, 'tmiaca', {'A': '1', 'B': VX, 'X': DK(1), 'O': ND1, 'P': P, 'E': E},
           {'1 e. NN0': closed(w, ph, '1nn0', '1 e. NN0'), '%s e. NN0' % VX: B.vxn, '1 < ( 2 ^ %s )' % VX: B.acc_facts('if ( 1 = 1 , 1 , 0 )', [])[1] if False else
            linarith(w, ph, [B.vx8, s([s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph), B.vxn, w.inst('bernneq3')], 'syl2anc',
                                       '( %s -> %s < ( 2 ^ %s ) )' % (ph, VX, VX))], '1 < ( 2 ^ %s )' % VX, closure=cl, products=True)},
           [('1', EA1, B.g(EA1, ewg_(w, ph, ACC1, a1n, DK(1), B.d1)))])
    # 5. allPrimeTDF ; 6. accAnd
    P, E = B.cp(2)
    B.call(R, 'tmiap', {'W': 'W', 'B': 'B', 'X': 'X', 'P': P, 'E': E}, {}, [])
    a2n, a2lt = B.acc_facts(ACC2, [c2])
    P, E = B.cp(3)
    EA2 = EWg(ACC2, DK(1))
    B.call(R, 'tmiaca', {'A': ACC1, 'B': VX, 'X': DK(1), 'O': AP1, 'P': P, 'E': E},
           {'%s e. NN0' % ACC1: a1n, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (ACC1, VX): a1lt}, [('1', EA2, B.g(EA2, ewg_(w, ph, ACC2, a2n, DK(1), B.d1)))])
    # 7. prodLF 4 5 6 2 3
    P, E = B.cp(4)
    pln = s([s([B.ww, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` W ) e. ( NN0 X. NN0 ) )' % ph), w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, PL1))
    cl.leaf(PL1, 'NN0', pln)
    V5 = EWg(PL1, DK(5))
    B.call(R, 'tmiprlb', {'K': '4', 'J': '5', 'I': '6', "I'": '2', 'I"': '3', 'L': 'W', 'R': 'X', 'B': 'B', 'P': P, 'E': E},
           {}, [('5', V5, B.g(V5, ewg_(w, ph, PL1, pln, DK(5), g('5'))))])
    # 8. dup 7 6 2 at VX
    p2n, _ = B.pw_le('N')
    fltx = linarith(w, ph, [B.flt, p2n], 'F < ( 2 ^ %s )' % VX, closure=cl)
    P, E = B.cp(5)
    V6 = EWg('F', DK(6))
    B.call(R, 'tmidupb', {'K': '7', 'J': '6', 'I': '2', 'F': 'F', 'N': VX, 'X': 'Y', 'P': P, 'E': E},
           {'%s e. NN0' % VX: B.vxn, 'F < ( 2 ^ %s )' % VX: fltx}, [('6', V6, B.g(V6, ewg_(w, ph, 'F', B.fn, DK(6), g('6'))))])
    # 9. cmpFrag 5 6 : PL1 <_ 2 ^ ( # W x. B ) < 2 ^ VX
    RALP = 'A. p e. ran W p < ( 2 ^ B )'
    cbp = s([s([s([], 'breq1', '( a = p -> ( a < ( 2 ^ B ) <-> p < ( 2 ^ B ) ) )')], 'cbvralvw', '( %s <-> %s )' % (RALB('W', 'B'), RALP))], 'a1i',
            '( %s -> ( %s <-> %s ) )' % (ph, RALB('W', 'B'), RALP))
    ralp = s([B.ral, cbp], 'mpbid', '( %s -> %s )' % (ph, RALP))
    ple = s([B.ww, s([B.bn, ralp], 'jca', '( %s -> ( B e. NN0 /\\ %s ) )' % (ph, RALP)), w.inst('t12prodle')], 'sylc',
            '( %s -> %s <_ ( 2 ^ ( %s x. B ) ) )' % (ph, PL1, NW))
    NB = '( %s x. B )' % NW
    cl.atom('( 2 ^ %s )' % NB)
    nbn = cl.mem(NB, 'NN0')
    lt_ = linarith(w, ph, [cl.ge0('B'), cl.ge0('N'), cl.ge0(NW)], '%s < %s' % (NB, VX), closure=cl, products=True)
    pnb = s([s([closed(w, ph, '2re', '2 e. RR'), s([nbn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, NB)), s([B.vxn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, VX))], '3jca',
              '( %s -> ( 2 e. RR /\\ %s e. ZZ /\\ %s e. ZZ ) )' % (ph, NB, VX)), s([closed(w, ph, '1lt2', '1 < 2'), lt_], 'jca', '( %s -> ( 1 < 2 /\\ %s < %s ) )' % (ph, NB, VX)),
            w.inst('ltexp2a')], 'syl2anc', '( %s -> ( 2 ^ %s ) < ( 2 ^ %s ) )' % (ph, NB, VX))
    pllt = linarith(w, ph, [ple, pnb], '%s < ( 2 ^ %s )' % (PL1, VX), closure=cl)
    P, E = B.cp(6)
    B.call(R, 'tmicmpb', {'K': '5', 'J': '6', 'F': PL1, 'G': 'F', 'N': VX, 'X': DK(5), 'Y': DK(6), 'P': P, 'E': E},
           {'%s e. NN0' % PL1: pln, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (PL1, VX): pllt, 'F < ( 2 ^ %s )' % VX: fltx},
           [('5', DK(5), g('5')), ('6', DK(6), g('6'))])
    # 10. load ( flag := decide ( cmp = .eq ) ) : CMPC( PL1 , F ) -> NFL( V3 )
    def fleq3(pr, rr, rc):
        kw = lambda t: dict(fl='if ( ( TMcmp ` %s ) = 1o , 1o , (/) )' % t)
        nv = lset_val(w, pr, kw, 'r', rr)
        NR = '( %s ` r )' % L_EQ
        ncq = s([lift_from(w, ph, pr, pln), lift_from(w, ph, pr, B.fn), w.inst('ncmpeq')], 'syl2anc', '( %s -> ( ( %s Ncmp F ) = 1o <-> %s = F ) )' % (pr, PL1, PL1))
        cq = s([s([rc], 'eqeq1d', '( %s -> ( ( TMcmp ` r ) = 1o <-> ( %s Ncmp F ) = 1o ) )' % (pr, PL1)), ncq], 'bitrd', '( %s -> ( ( TMcmp ` r ) = 1o <-> %s = F ) )' % (pr, PL1))
        i1 = s([cq], 'ifbid', '( %s -> if ( ( TMcmp ` r ) = 1o , 1o , (/) ) = %s )' % (pr, V3))
        return (nv['mem'], s([nv['fields']['fl'], i1], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pr, NR, V3))), kw
    cmp_load(w, ph, B, R, LMV['Z3'], LMV['Y8'], L_EQ, PL1, 'F', pln, B.fn, V3, fleq3)
    # 11. accAnd
    a3n, a3lt = B.acc_facts(ACC3, [c3, c2])
    P, E = B.cp(7)
    assert E == KO_ENTRY, E
    EA3 = EWg(ACC3, DK(1))
    B.call(R, 'tmiaca', {'A': ACC2, 'B': VX, 'X': DK(1), 'O': V3, 'P': P, 'E': E},
           {'%s e. NN0' % ACC2: a2n, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (ACC2, VX): a2lt}, [('1', EA3, B.g(EA3, ewg_(w, ph, ACC3, a3n, DK(1), B.d1)))])
    cur, out = R.normalize(N8)
    assert out == [('1', EA3)], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    assert D == CLN(KO_ENTRY, S, UP('D', '1', EA3)), D
    # the bound
    nd2 = s([s([B.ww, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, ND2))
    ap2 = s([s([B.ww, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, AP2))
    pl2 = s([s([B.ww, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` W ) e. ( NN0 X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, PL2))
    cl.leaf(ND2, 'NN0', nd2); cl.leaf(AP2, 'NN0', ap2); cl.leaf(PL2, 'NN0', pl2)
    plc = s([B.ww, w.inst('prodlcost')], 'syl', '( %s -> %s = %s )' % (ph, PL2, NW))
    le = linarith(w, ph, [plc, cl.ge0(TB(B1)), cl.ge0(TB(B37)), cl.ge0(TB(BPL)), cl.ge0(VXT), cl.ge0(ND2), cl.ge0(AP2), cl.ge0(NW)],
                  '%s <_ %s' % (n, VA), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, VA, cl.mem(VA, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def tmiverc():
    lab = 'tmiverc'
    T = numtree(TREE_VER)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` verifyF_le_B ` at the machine: after the first half (~ tmivera ), ` korseltTDF ` (~ tmiko ), ` accAnd ` , '
               '` listLen 4 5 2 3 ` (~ tmillenb ), ` pushNum 6 3 ` , ` cmpFrag 6 5 ` , ` load\' ( flag := !decide ( cmp = .gt ) ) ` , '
               '` accAnd ` , ` isZero 1 2 ` , ` load\' ( flag := !flag ) ` , ` dropNum 1 ` : the flag is ` ( 1st ( m Verify S ) ) ` '
               '(~ t12verfl ), every stack restored, within ` ( ( verify m S ).2 + 1 ) B ( 4 X + 6 ) ` steps.')
    s = w.s
    B = Ver(w, ph, T, deep=())
    c, mk, cl = B.c, B.mk, B.cl
    g = lambda k: B.S0.vals[k][2]
    pre0 = s([], 'tmivera', STMTS12['tmivera'])
    pre = s([pre0], 'adantr', '( %s -> %s )' % (ph, CONCL_VERA))
    C0_, D0_, n0_ = triple_parts(CONCL_VERA)
    a3n, a3lt = B.acc_facts(ACC3, [c3, c2])
    EA3 = EWg(ACC3, DK(1))
    S1 = B.S0.upd('1', EA3, B.g(EA3, ewg_(w, ph, ACC3, a3n, DK(1), B.d1)))
    R = B.run()
    R.S = S1; R.chain = [('1', EA3)]; R.gam[EA3] = B.gam[EA3]
    # 12. korseltTDF ; 13. accAnd
    P, E = B.cp(8)
    B.call(R, 'tmiko', {'W': 'W', 'F': 'F', 'B': 'B', 'N': 'N', 'X': 'X', 'Y': 'Y', 'P': P, 'E': E}, {}, [])
    a4n, a4lt = B.acc_facts(ACC4, [c4, c3, c2])
    P, E = B.cp(9)
    EA4 = EWg(ACC4, DK(1))
    B.call(R, 'tmiaca', {'A': ACC3, 'B': VX, 'X': DK(1), 'O': KOF, 'P': P, 'E': E},
           {'%s e. NN0' % ACC3: a3n, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (ACC3, VX): a3lt}, [('1', EA4, B.g(EA4, ewg_(w, ph, ACC4, a4n, DK(1), B.d1)))])
    cur, out = R.normalize(N8)
    assert out == [('1', EA4)], out
    t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
    assert C1 == D0_, (C1, D0_)
    tvc = hrseq(w, ph, mk['phm'], pre, t1, C0_, D0_, D1, n0_, n1)
    assert TRI(C0_, D1, '( %s + %s )' % (n0_, n1)) == CONCL_VERC, '\n%s\n%s' % (TRI(C0_, D1, '( %s + %s )' % (n0_, n1)), CONCL_VERC)
    finish(w, tvc, lab)
    return w.run()


def tmiverb():
    lab = 'tmiverb'
    T = numtree(TREE_VER)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` verifyF_le_B ` at the machine: after ~ tmiverc (the tests up to korselt), ` listLen 4 5 2 3 ` (~ tmillenb ), '
               '` pushNum 6 3 ` , ` cmpFrag 6 5 ` , ` load\' ( flag := !decide ( cmp = .gt ) ) ` , ` accAnd ` , ` isZero 1 2 ` , '
               '` load\' ( flag := !flag ) ` , ` dropNum 1 ` : the flag is ` ( 1st ( m Verify S ) ) ` (~ t12verfl ), every stack restored, '
               'within ` ( ( verify m S ).2 + 1 ) B ( 4 X + 6 ) ` steps.')
    s = w.s
    B = Ver(w, ph, T, deep=(10,))
    c, mk, cl = B.c, B.mk, B.cl
    g = lambda k: B.S0.vals[k][2]
    pre0 = s([], 'tmiverc', STMTS12['tmiverc'])
    pre = s([pre0], 'adantr', '( %s -> %s )' % (ph, CONCL_VERC))
    C0_, D0_, n0_ = triple_parts(CONCL_VERC)
    a4n, a4lt = B.acc_facts(ACC4, [c4, c3, c2])
    EA4 = EWg(ACC4, DK(1))
    S1 = B.S0.upd('1', EA4, B.g(EA4, ewg_(w, ph, ACC4, a4n, DK(1), B.d1)))
    R = B.run()
    R.S = S1; R.chain = [('1', EA4)]; R.gam[EA4] = B.gam[EA4]
    u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    # 14. listLen 4 5 2 3
    P, E = B.cp(10)
    V5w = EWg(NW, DK(5))
    B.call(R, 'tmillenb', {'K': '4', 'J': '5', 'I': '2', "I'": '3', 'L': 'W', 'R': 'X', 'B': 'B', 'P': P, 'E': E},
           {'%s e. NN0' % NW: B.nw}, [('5', V5w, B.g(V5w, ewg_(w, ph, NW, B.nw, DK(5), g('5'))))])
    # 15. pushNum 6 3 at VX
    u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    blt = s([u2, B.vxn, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ph, VX, VX))
    lt3 = linarith(w, ph, [blt, B.vx8], '3 < ( 2 ^ %s )' % VX, closure=cl, products=True)
    P, E = B.cp(11)
    V6 = EWg('3', DK(6))
    B.call(R, 'tmipnvb', {'K': '6', 'N': '3', 'B': VX, 'P': P, 'E': E},
           {'3 e. NN0': closed(w, ph, '3nn0', '3 e. NN0'), '%s e. NN0' % VX: B.vxn, '3 < ( 2 ^ %s )' % VX: lt3},
           [('6', V6, B.g(V6, ewg_(w, ph, '3', closed(w, ph, '3nn0', '3 e. NN0'), DK(6), g('6'))))])
    # 16. cmpFrag 6 5
    p2b, _ = B.pw_le('B')
    nwltx = linarith(w, ph, [B.nwlt, p2b], '%s < ( 2 ^ %s )' % (NW, VX), closure=cl)
    P, E = B.cp(12)
    B.call(R, 'tmicmpb', {'K': '6', 'J': '5', 'F': '3', 'G': NW, 'N': VX, 'X': DK(6), 'Y': DK(5), 'P': P, 'E': E},
           {'3 e. NN0': closed(w, ph, '3nn0', '3 e. NN0'), '%s e. NN0' % VX: B.vxn, '3 < ( 2 ^ %s )' % VX: lt3, '%s < ( 2 ^ %s )' % (NW, VX): nwltx, '%s e. NN0' % NW: B.nw},
           [('6', DK(6), g('6')), ('5', DK(5), g('5'))])
    # 17. load ( flag := !decide ( cmp = .gt ) ) : CMPC( 3 , # W ) -> NFL( V5 )
    def fleq5(pr, rr, rc):
        kw = lambda t: dict(fl='if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t)
        nv = lset_val(w, pr, kw, 'r', rr)
        NR = '( %s ` r )' % L_NGT
        ncg = s([closed(w, pr, '3nn0', '3 e. NN0'), lift_from(w, ph, pr, B.nw), w.inst('ncmpgt')], 'syl2anc', '( %s -> ( ( 3 Ncmp %s ) = 2o <-> %s < 3 ) )' % (pr, NW, NW))
        cq = s([s([rc], 'eqeq1d', '( %s -> ( ( TMcmp ` r ) = 2o <-> ( 3 Ncmp %s ) = 2o ) )' % (pr, NW)), ncg], 'bitrd', '( %s -> ( ( TMcmp ` r ) = 2o <-> %s < 3 ) )' % (pr, NW))
        nlt = s([s([lift_from(w, ph, pr, B.nw)], 'nn0red', '( %s -> %s e. RR )' % (pr, NW)), closed(w, pr, '3re', '3 e. RR'), w.inst('ltnle')], 'syl2anc',
                '( %s -> ( %s < 3 <-> -. 3 <_ %s ) )' % (pr, NW, NW))
        i1 = s([s([cq, nlt], 'bitrd', '( %s -> ( ( TMcmp ` r ) = 2o <-> -. 3 <_ %s ) )' % (pr, NW))], 'ifbid',
                '( %s -> if ( ( TMcmp ` r ) = 2o , (/) , 1o ) = if ( -. 3 <_ %s , (/) , 1o ) )' % (pr, NW))
        i2 = s([s([], 'ifnot', 'if ( -. 3 <_ %s , (/) , 1o ) = %s' % (NW, V5))], 'a1i', '( %s -> if ( -. 3 <_ %s , (/) , 1o ) = %s )' % (pr, NW, V5))
        return (nv['mem'], s([nv['fields']['fl'], i1, i2], '3eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pr, NR, V5))), kw
    cmp_load(w, ph, B, R, LMV['Z4'], LMV['Y14'], L_NGT, '3', NW, closed(w, ph, '3nn0', '3 e. NN0'), B.nw, V5, fleq5)
    # 18. accAnd
    a5n, a5lt = B.acc_facts(ACC5, [c5, c4, c3, c2])
    P, E = B.cp(13)
    EA5 = EWg(ACC5, DK(1))
    B.call(R, 'tmiaca', {'A': ACC4, 'B': VX, 'X': DK(1), 'O': V5, 'P': P, 'E': E},
           {'%s e. NN0' % ACC4: a4n, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (ACC4, VX): a4lt}, [('1', EA5, B.g(EA5, ewg_(w, ph, ACC5, a5n, DK(1), B.d1)))])
    # 19. isZero 1 2 ; 20. flag := !flag ; 21. dropNum 1
    P, E = B.cp(14)
    B.call(R, 'tmiizbs', {'K': '1', 'I': '2', 'F': ACC5, 'N': VX, 'X': DK(1), 'P': P, 'E': E},
           {'%s e. NN0' % ACC5: a5n, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (ACC5, VX): a5lt}, [])
    Vz1 = 'if ( %s = 0 , 1o , (/) )' % ACC5
    kw = lambda t: dict(fl='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t)
    B.call(R, 'tm2flg', {'A': LMV['Z5'], 'E': LMV['Y16'], 'F': L_NOTF, 'N': NFL(Vz1), "N'": NFL(VFLAG)},
           {LTY(L_NOTF): lset_ty2(w, ph, mk, L_NOTF, kw), SSS(NFL(Vz1)): B.ss(NFL(Vz1)), SSS(NFL(VFLAG)): B.ss(NFL(VFLAG)),
            'A. r e. %s ( %s ` r ) e. %s' % (NFL(Vz1), L_NOTF, NFL(VFLAG)): load_nfl(w, ph, mk, L_NOTF, kw, Vz1, VFLAG, notif_fleq(w, '%s = 0' % ACC5))}, [])
    Son, old = expose(w, ph, B, R, '1')
    P, E = B.cp(15)
    assert E == 'E', E
    B.call(R, 'tmidropnb', {'K': '1', 'F': ACC5, 'N': VX, 'X': DK(1), 'O': VFLAG, 'P': P, 'E': E},
           {'%s e. NN0' % ACC5: a5n, '%s e. NN0' % VX: B.vxn, '%s < ( 2 ^ %s )' % (ACC5, VX): a5lt}, [('1', DK(1), B.d1)], on=(Son, old))
    cur, out = R.normalize(N8)
    assert out == [], out
    t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
    assert C1 == D0_, (C1, D0_)
    t2 = hrseq(w, ph, mk['phm'], pre, t1, C0_, D0_, D1, n0_, n1)
    n2 = '( %s + %s )' % (n0_, n1)
    # the flag
    vf = s([s([s([B.fn, B.ww], 'jca', '( %s -> ( F e. NN0 /\\ W e. Word NN0 ) )' % ph), B.a1], 'jca', '( %s -> ( ( F e. NN0 /\\ W e. Word NN0 ) /\\ A. a e. ran W 1 <_ a ) )' % ph),
            w.inst('t12verfl')], 'syl', '( %s -> %s = ( 1st ` %s ) )' % (ph, VFLAG, VER_))
    t2, C2, D2, n2 = cls_to(w, ph, (t2, C0_, D1, n2), VFLAG, '( 1st ` %s )' % VER_, vf)
    # the bound : ( 2nd Verify ) = nd + pr + # W + ko + 2 , TMB ( 4 VX + 6 ) = 64 TMB VX
    nd2 = s([s([B.ww, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, ND2))
    ap2 = s([s([B.ww, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, AP2))
    pl2 = s([s([B.ww, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` W ) e. ( NN0 X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, PL2))
    ko2 = s([s([B.fn, B.ww, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( F KorseltTD W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, KO2))
    for x, st_ in ((ND2, nd2), (AP2, ap2), (PL2, pl2), (KO2, ko2)):
        cl.leaf(x, 'NN0', st_)
    CST = '( ( ( ( %s + %s ) + %s ) + %s ) + 2 )' % (ND2, AP2, PL2, KO2)
    IFV = triple_parts(CONCL_VER)[1]
    vcl = s([B.fn, B.ww, w.inst('verifycl')], 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (ph, VER_))
    va, vb = paircl(w, ph, VER_, vcl, '2o', 'NN0')
    v2 = verify_snd(w, ph, B, CST)
    cl.leaf('( 2nd ` %s )' % VER_, 'NN0', vb)
    plc = s([B.ww, w.inst('prodlcost')], 'syl', '( %s -> %s = %s )' % (ph, PL2, NW))
    koc = s([B.fn, B.ww, w.inst('korselttdcost')], 'syl2anc', '( %s -> %s = %s )' % (ph, KO2, NW))
    sc = s([closed(w, ph, '3nn0', '3 e. NN0'), B.vxn, w.inst('tplbscale')], 'syl2anc',
           '( %s -> ( ( ( 3 + 1 ) ^ 3 ) x. %s ) = ( TMB ` ( ( ( 3 + 1 ) x. %s ) + ( 2 x. 3 ) ) ) )' % (ph, VXT, VX))
    ae = lineq(w, ph, '( ( ( 3 + 1 ) x. %s ) + ( 2 x. 3 ) )' % VX, '( ( 4 x. %s ) + 6 )' % VX, closure=cl, products=True)
    T46 = TB('( ( 4 x. %s ) + 6 )' % VX)
    sc2 = s([sc, s([ae], 'fveq2d', '( %s -> ( TMB ` ( ( ( 3 + 1 ) x. %s ) + ( 2 x. 3 ) ) ) = %s )' % (ph, VX, T46))], 'eqtrd', '( %s -> ( ( ( 3 + 1 ) ^ 3 ) x. %s ) = %s )' % (ph, VXT, T46))
    e64 = s([s([s([], '3p1e4', '( 3 + 1 ) = 4')], 'oveq1i', '( ( 3 + 1 ) ^ 3 ) = ( 4 ^ 3 )'), s([], 'cu4' if False else '4cu' if False else 'cu4', '( 4 ^ 3 ) = ; 6 4')], 'eqtri', '( ( 3 + 1 ) ^ 3 ) = ; 6 4') if False else None
    e64 = cube4(w)
    t64 = s([s([s([e64], 'oveq1i', '( ( ( 3 + 1 ) ^ 3 ) x. %s ) = ( ; 6 4 x. %s )' % (VXT, VXT))], 'a1i', '( %s -> ( ( ( 3 + 1 ) ^ 3 ) x. %s ) = ( ; 6 4 x. %s ) )' % (ph, VXT, VXT)), sc2],
            'eqtr3d', '( %s -> ( ; 6 4 x. %s ) = %s )' % (ph, VXT, T46))
    cl.leaf(T46, 'NN0', tmbn(w, ph, '( ( 4 x. %s ) + 6 )' % VX, cl.mem('( ( 4 x. %s ) + 6 )' % VX, 'NN0')))
    monos = [B.pw_le(x)[1] for x in (B1, B37, BPL, 'N', 'B')]
    # the products ( k + 1 ) TMB x <_ ( k + 1 ) TMB VX (~ lemul2a ), one per piece
    def _mul2(A_, B_, C_, bc):
        j_ = s([s([cl.mem(B_, 'RR'), cl.mem(C_, 'RR'), s([cl.mem(A_, 'RR'), cl.ge0(A_)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, A_, A_))], '3jca',
                 '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (ph, B_, C_, A_, A_)), bc], 'jca',
              '( %s -> ( ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s <_ %s ) )' % (ph, B_, C_, A_, A_, B_, C_))
        return s([j_, w.inst('lemul2a')], 'syl', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A_, B_, A_, C_))
    prods = [_mul2('( %s + 1 )' % ND2, TB(B1), VXT, monos[0]), _mul2('( %s + 1 )' % AP2, TB(B37), VXT, monos[1]),
             _mul2('( %s + 1 )' % NW, TB(BPL), VXT, monos[2]), _mul2('( %s + 1 )' % KO2, TB('N'), VXT, monos[3]),
             _mul2('( %s + 1 )' % NW, TB('B'), VXT, monos[4])]
    BND = triple_parts(CONCL_VER)[2]
    vx1 = s([s([B.vxn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, VXT)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, VXT))
    le = linarith(w, ph, [v2, plc, koc, t64, vx1] + monos + prods + [cl.ge0(VXT), cl.ge0(ND2), cl.ge0(AP2), cl.ge0(KO2), cl.ge0(NW), B.vx8],
                  '%s <_ %s' % (n2, BND), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t2, C2, D2, n2, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def cube4(w):
    """|- ( ( 3 + 1 ) ^ 3 ) = ; 6 4"""
    s = w.s
    e1 = s([s([], '3p1e4', '( 3 + 1 ) = 4')], 'oveq1i', '( ( 3 + 1 ) ^ 3 ) = ( 4 ^ 3 )')
    s2 = s([s([s([], '4cn', '4 e. CC'), w.inst('sqval')], 'ax-mp', '( 4 ^ 2 ) = ( 4 x. 4 )'), s([], '4t4e16', '( 4 x. 4 ) = ; 1 6')], 'eqtri', '( 4 ^ 2 ) = ; 1 6')
    ep = s([s([], '4cn', '4 e. CC'), s([], '2nn0', '2 e. NN0'), w.inst('expp1')], 'mp2an', '( 4 ^ ( 2 + 1 ) ) = ( ( 4 ^ 2 ) x. 4 )')
    e21 = s([s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( 4 ^ ( 2 + 1 ) ) = ( 4 ^ 3 )')
    m = s([s([s2], 'oveq1i', '( ( 4 ^ 2 ) x. 4 ) = ( ; 1 6 x. 4 )'), num.mul_lits(w, '; 1 6', '4')], 'eqtri', '( ( 4 ^ 2 ) x. 4 ) = ; 6 4')
    c4 = s([s([e21, ep], 'eqtr3i', '( 4 ^ 3 ) = ( ( 4 ^ 2 ) x. 4 )'), m], 'eqtri', '( 4 ^ 3 ) = ; 6 4')
    return s([e1, c4], 'eqtri', '( ( 3 + 1 ) ^ 3 ) = ; 6 4')


def verify_snd(w, ph, B, CST):
    """( ph -> ( 2nd ` VER_ ) = CST )"""
    s = w.s
    L3 = '3 <_ %s' % NW
    IF3 = 'if ( %s , %s , (/) )' % (c3, KO1)
    IF2 = 'if ( %s , %s , (/) )' % (c2, IF3)
    IF1 = 'if ( %s , %s , (/) )' % (c1, IF2)
    IFV = 'if ( %s , %s , (/) )' % (L3, IF1)
    vv = s([B.fn, B.ww, w.inst('verifyval')], 'syl2anc', '( %s -> %s = <. %s , %s >. )' % (ph, VER_, IFV, CST))
    ifx = s([s([], 'ifex', '%s e. _V' % IFV)], 'a1i', '( %s -> %s e. _V )' % (ph, IFV))
    cx = s([s([], 'ovex', '%s e. _V' % CST)], 'a1i', '( %s -> %s e. _V )' % (ph, CST))
    return projeq(w, ph, VER_, vv, IFV, CST, ifx, cx, 2)


if __name__ == '__main__':
    for l in SEL:
        if l == 't12prodle' or l in ('t12prodleb', 't12prodles'):
            t12prodle()
        else:
            globals()[l]()
