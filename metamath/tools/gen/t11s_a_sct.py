"""T11 helper (scan): Lean's ` scanTest ` at the machine (Steps23.lean ` scanTest_runs ` ) on TMIsct.

  tmisct   scanTest_runs: ` poolAlgF ` (~ tmipla ), ` listLen 6 3 7 5 ` (~ tmillenb ), ` moveEntry 0 7 5 ` (~ tmime ),
           ` dup 0 5 4 ` (~ tmidupb ), ` moveEntry 7 0 5 ` (~ tmime ), ` cmpFrag 5 3 ` (~ tmicmpb )

    MM_DB=sorties/t11.mm MM_HEAP=8g python3 tools/gen/t11s_a_sct.py tmisct
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t10_e_doa import lift_from
from t10_u_s2s import me_bound_n
from t11p_d_plf import pw2mono, tbn
import t6blib

SEL = sys.argv[1:]
UO = os.environ.get('T11S_UO') == '1'
PA = '( ( ( W PoolAlg F ) ` Z ) ` G )'
PA1 = '( 1st ` %s )' % PA
PA2 = '( 2nd ` %s )' % PA
PLEN = '( # ` %s )' % PA1
DV = '( DivisorsOf ` W )'
DV1 = '( 1st ` %s )' % DV
DV2 = '( 2nd ` %s )' % DV
PG = '( ( ( F PoolGo Z ) ` G ) ` %s )' % DV1
PGD = '( 1st ` %s )' % PG
PG2 = '( 2nd ` %s )' % PG
NW = '( # ` W )'
MS = MS_
TMS = '( TMB ` %s )' % MS
MPA_ = MPA
TPA = '( TMB ` %s )' % MPA_
TB_ = '( TMB ` B )'
FZG = '( ( F e. NN0 /\\ Z e. NN0 ) /\\ G e. NN0 )'
SQ = '( Nfloor ` ( sqrt ` F ) )'


def pool_facts(w, ph, c, fn, zn, gn, ww, bn, cn):
    """the pool at k' = G: ( ph -> A. a e. ran PA1 a < ( 2 ^ MS ) ) , ( ph -> PLEN < ( 2 ^ MS ) ) , ( ph -> PLEN <_ PA2 ) ,
    PA1 e. Word NN0 , PA2 e. NN0"""
    s = w.s
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
    dvc = s([ww, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, DV))
    dv1w = s([dvc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DV1))
    dv2n = s([dvc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, DV2))
    fzg = s([s([fn, zn], 'jca', '( %s -> ( F e. NN0 /\\ Z e. NN0 ) )' % ph), gn], 'jca', '( %s -> %s )' % (ph, FZG))
    fzgd = s([fzg, dv1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (ph, FZG, DV1))
    pgc = s([fzgd, w.inst('poolgocl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, PG))
    pgw = s([pgc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PGD))
    p2n = s([pgc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, PG2))
    pav = s([s([s([s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph), zn], 'jca',
                  '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % ph),
               gn], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ G e. NN0 ) )' % ph), w.inst('poolalgval')], 'syl',
            '( %s -> %s = <. %s , ( %s + %s ) >. )' % (ph, PA, PGD, DV2, PG2))
    SS = '( %s + %s )' % (DV2, PG2)
    ssn = s([dv2n, p2n], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, SS))
    a1 = s([s([pav], 'fveq2d', '( %s -> %s = ( 1st ` <. %s , %s >. ) )' % (ph, PA1, PGD, SS)),
            s([pgw, ssn, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, PGD, SS, PGD))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, PA1, PGD))
    a2 = s([s([pav], 'fveq2d', '( %s -> %s = ( 2nd ` <. %s , %s >. ) )' % (ph, PA2, PGD, SS)),
            s([pgw, ssn, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, PGD, SS, SS))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, PA2, SS))
    paw = s([a1, pgw], 'eqeltrd', '( %s -> %s e. Word NN0 )' % (ph, PA1))
    pa2n = s([a2, ssn], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, PA2))
    mem = s([fzgd, w.inst('tmpgmem')], 'syl', '( %s -> ( A. q e. ran %s ( q <_ F /\\ Z < q ) /\\ ( ( # ` %s ) <_ %s /\\ ( # ` %s ) <_ %s ) ) )'
            % (ph, PGD, PGD, PG2, DV1, PG2))
    ral = s([mem], 'simpld', '( %s -> A. q e. ran %s ( q <_ F /\\ Z < q ) )' % (ph, PGD))
    lpg = s([s([mem], 'simprd', '( %s -> ( ( # ` %s ) <_ %s /\\ ( # ` %s ) <_ %s ) )' % (ph, PGD, PG2, DV1, PG2))], 'simpld',
            '( %s -> ( # ` %s ) <_ %s )' % (ph, PGD, PG2))
    cl = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn), 'F': ('NN0', fn)})
    cl.leaf(NW, 'NN0', nw)
    msn = cl.mem(MS, 'NN0')
    P2B, P2M = '( 2 ^ B )', '( 2 ^ %s )' % MS
    # B <_ MS
    wb = s([nw, bn], 'nn0mulcld', '( %s -> ( %s x. B ) e. NN0 )' % (ph, NW))
    wbg = s([wb], 'nn0ge0d', '( %s -> 0 <_ ( %s x. B ) )' % (ph, NW))
    wc = s([nw, cn], 'nn0mulcld', '( %s -> ( %s x. C ) e. NN0 )' % (ph, NW))
    wcg = s([wc], 'nn0ge0d', '( %s -> 0 <_ ( %s x. C ) )' % (ph, NW))
    bms = linarith(w, ph, [wbg, wcg, cl.ge0('C'), cl.ge0('B'), cl.ge0(NW)], 'B <_ %s' % MS, closure=cl, products=True)
    m2 = pw2mono(w, ph, 'B', bn, MS, msn, bms)
    # entries
    pa_ = '( %s /\\ p e. ran %s )' % (ph, PA1)
    ain = s([s([], 'simpr', '( %s -> p e. ran %s )' % (pa_, PA1)), s([lift_from(w, ph, pa_, a1)], 'rneqd', '( %s -> ran %s = ran %s )' % (pa_, PA1, PGD))],
            'eleqtrd', '( %s -> p e. ran %s )' % (pa_, PGD))
    qa = s([s([], 'breq1', '( q = p -> ( q <_ F <-> p <_ F ) )'), s([], 'breq2', '( q = p -> ( Z < q <-> Z < p ) )')], 'anbi12d',
           '( q = p -> ( ( q <_ F /\\ Z < q ) <-> ( p <_ F /\\ Z < p ) ) )')
    af = s([s([qa, ain, lift_from(w, ph, pa_, ral)], 'rspcdva', '( %s -> ( p <_ F /\\ Z < p ) )' % pa_)], 'simpld', '( %s -> p <_ F )' % pa_)
    arr = s([s([s([s([lift_from(w, ph, pa_, pgw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa_, PGD, PGD)),
                   w.inst('frn')], 'syl', '( %s -> ran %s C_ NN0 )' % (pa_, PGD)), ain], 'sseldd', '( %s -> p e. NN0 )' % pa_)], 'nn0red',
            '( %s -> p e. RR )' % pa_)
    cla = Closure(w, pa_, {'F': ('NN0', lift_from(w, ph, pa_, fn))})
    cla.leaf('p', 'RR', arr)
    cla.leaf(P2B, 'RR', s([s([closed(w, pa_, '2nn', '2 e. NN'), lift_from(w, ph, pa_, bn), w.inst('nnexpcl')], 'syl2anc',
                             '( %s -> %s e. NN )' % (pa_, P2B))], 'nnred', '( %s -> %s e. RR )' % (pa_, P2B)))
    cla.leaf(P2M, 'RR', s([s([closed(w, pa_, '2nn', '2 e. NN'), lift_from(w, ph, pa_, msn), w.inst('nnexpcl')], 'syl2anc',
                             '( %s -> %s e. NN )' % (pa_, P2M))], 'nnred', '( %s -> %s e. RR )' % (pa_, P2M)))
    alt = linarith(w, pa_, [af, lift_from(w, ph, pa_, c[LT2('F')]), lift_from(w, ph, pa_, m2)], 'p < %s' % P2M, closure=cla)
    ralp = s([alt], 'ralrimiva', '( %s -> A. p e. ran %s p < %s )' % (ph, PA1, P2M))
    ralb = s([ralp, s([s([], 'breq1', '( p = a -> ( p < %s <-> a < %s ) )' % (P2M, P2M))], 'cbvralvw',
                      '( A. p e. ran %s p < %s <-> A. a e. ran %s a < %s )' % (PA1, P2M, PA1, P2M))], 'sylib',
             '( %s -> A. a e. ran %s a < %s )' % (ph, PA1, P2M))
    # the length: PLEN <_ PG2 <_ PA2 <_ ( 2 ^ # W ) ( SQ + 3 ) <_ ( 2 ^ # W ) ( 8 ( 2 ^ B ) ) < 2 ^ MS
    lpa = s([s([a1], 'fveq2d', '( %s -> %s = ( # ` %s ) )' % (ph, PLEN, PGD)), lpg], 'eqbrtrd', '( %s -> %s <_ %s )' % (ph, PLEN, PG2))
    pac = s([s([s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph), s([zn, gn], 'jca', '( %s -> ( Z e. NN0 /\\ G e. NN0 ) )' % ph)],
               'jca', '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ ( Z e. NN0 /\\ G e. NN0 ) ) )' % ph), w.inst('poolalgcost')], 'syl',
            '( %s -> %s <_ ( ( 2 ^ %s ) x. ( %s + 3 ) ) )' % (ph, PA2, NW, SQ))
    fr = s([fn], 'nn0red', '( %s -> F e. RR )' % ph)
    f0 = s([fn], 'nn0ge0d', '( %s -> 0 <_ F )' % ph)
    sqr = s([fr, f0], 'resqrtcld', '( %s -> ( sqrt ` F ) e. RR )' % ph)
    sq0 = s([fr, f0], 'sqrtge0d', '( %s -> 0 <_ ( sqrt ` F ) )' % ph)
    sql = s([sqr, sq0, w.inst('nfloorle')], 'syl2anc', '( %s -> %s <_ ( sqrt ` F ) )' % (ph, SQ))
    F1 = '( F + 1 )'
    f1r = s([fr, w.inst('peano2re')], 'syl', '( %s -> %s e. RR )' % (ph, F1))
    f10 = linarith(w, ph, [f0], '0 <_ %s' % F1, closure=cl)
    f11 = linarith(w, ph, [f0], '1 <_ %s' % F1, closure=cl)
    fle = linarith(w, ph, [], 'F <_ %s' % F1, closure=cl)
    sqm = s([s([s([fr, f0], 'jca', '( %s -> ( F e. RR /\\ 0 <_ F ) )' % ph), s([f1r, f10], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, F1, F1))],
               'jca', '( %s -> ( ( F e. RR /\\ 0 <_ F ) /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (ph, F1, F1)), w.inst('sqrtle')], 'syl',
            '( %s -> ( F <_ %s <-> ( sqrt ` F ) <_ ( sqrt ` %s ) ) )' % (ph, F1, F1))
    sqm2 = s([fle, sqm], 'mpbid', '( %s -> ( sqrt ` F ) <_ ( sqrt ` %s ) )' % (ph, F1))
    cbs = s([f1r, f11, w.inst('cbsqle')], 'syl2anc', '( %s -> ( sqrt ` %s ) <_ %s )' % (ph, F1, F1))
    sqn = s([sqr, w.inst('nfloorcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, SQ))
    cl.leaf(SQ, 'NN0', sqn)
    cl.leaf('( sqrt ` F )', 'RR', sqr)
    cl.leaf('( sqrt ` %s )' % F1, 'RR', s([f1r, f10], 'resqrtcld', '( %s -> ( sqrt ` %s ) e. RR )' % (ph, F1)))
    p2bn = s([closed(w, ph, '2nn', '2 e. NN'), bn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2B))
    cl.leaf(P2B, 'NN', p2bn)
    P2W = '( 2 ^ %s )' % NW
    p2wn = s([closed(w, ph, '2nn', '2 e. NN'), nw, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2W))
    cl.leaf(P2W, 'NN', p2wn)
    p2b1 = s([p2bn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, P2B))
    S3 = '( %s + 3 )' % SQ
    E8 = '( 8 x. %s )' % P2B
    s38 = linarith(w, ph, [sql, sqm2, cbs, c[LT2('F')], p2b1], '%s <_ %s' % (S3, E8), closure=cl)
    mw = s([cl.mem(S3, 'RR'), cl.mem(E8, 'RR'), cl.mem(P2W, 'RR'), cl.ge0(P2W), s38], 'lemul2ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, P2W, S3, P2W, E8))
    B4 = '( B + 4 )'
    b4n = cl.mem(B4, 'NN0')
    EX = '( %s + %s )' % (NW, B4)
    exn = cl.mem(EX, 'NN0')
    e1 = s([closed(w, ph, '2cn', '2 e. CC'), nw, b4n], 'expaddd', '( %s -> ( 2 ^ %s ) = ( %s x. ( 2 ^ %s ) ) )' % (ph, EX, P2W, B4))
    e2 = s([closed(w, ph, '2cn', '2 e. CC'), bn, closed(w, ph, '4nn0', '4 e. NN0')], 'expaddd', '( %s -> ( 2 ^ %s ) = ( %s x. ( 2 ^ 4 ) ) )' % (ph, B4, P2B))
    e3 = s([e2, s([s([s([], '2exp4', '( 2 ^ 4 ) = ; 1 6')], 'oveq2i', '( %s x. ( 2 ^ 4 ) ) = ( %s x. ; 1 6 )' % (P2B, P2B))], 'a1i',
              '( %s -> ( %s x. ( 2 ^ 4 ) ) = ( %s x. ; 1 6 ) )' % (ph, P2B, P2B))], 'eqtrd', '( %s -> ( 2 ^ %s ) = ( %s x. ; 1 6 ) )' % (ph, B4, P2B))
    P2E = '( 2 ^ %s )' % EX
    P2B4 = '( 2 ^ %s )' % B4
    cl.leaf(P2B4, 'NN', s([closed(w, ph, '2nn', '2 e. NN'), b4n, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2B4)))
    e13 = s([e1, s([e3], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. ; 1 6 ) ) )' % (ph, P2W, P2B4, P2W, P2B))], 'eqtrd',
            '( %s -> %s = ( %s x. ( %s x. ; 1 6 ) ) )' % (ph, P2E, P2W, P2B))
    cl.leaf(P2E, 'NN', s([closed(w, ph, '2nn', '2 e. NN'), exn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2E)))
    cl.leaf(P2M, 'NN', s([closed(w, ph, '2nn', '2 e. NN'), msn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2M)))
    exm = linarith(w, ph, [wbg, wcg, cl.ge0('C'), cl.ge0('B'), cl.ge0(NW)], '%s <_ %s' % (EX, MS), closure=cl, products=True)
    m3 = pw2mono(w, ph, EX, exn, MS, msn, exm)
    WB = '( %s x. %s )' % (P2W, P2B)
    wbp = s([p2wn, p2bn], 'nnmulcld', '( %s -> %s e. NN )' % (ph, WB))
    wb1 = s([wbp, w.inst('nngt0')], 'syl', '( %s -> 0 < %s )' % (ph, WB))
    cl.leaf(PG2, 'NN0', p2n)
    cl.leaf(DV2, 'NN0', dv2n)
    cl.leaf(PA2, 'NN0', pa2n)
    cl.leaf(PLEN, 'NN0', s([paw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, PLEN)))
    lt = linarith(w, ph, [lpa, a2, pac, mw, e13, m3, wb1, cl.ge0(DV2)],
                  '%s < %s' % (PLEN, P2M), closure=cl, atoms=[P2W, P2B, PA2, PG2, DV2, PLEN, SQ], products=True)
    lpa2 = linarith(w, ph, [lpa, a2, cl.ge0(DV2)], '%s <_ %s' % (PLEN, PA2), closure=cl, atoms=[PA2, PG2, DV2, PLEN])
    return dict(cl=cl, ralb=ralb, lt=lt, lpa2=lpa2, paw=paw, pa2n=pa2n, msn=msn, m2=m2, bms=bms, nw=nw, wbg=wbg, wcg=wcg)


def tmisct():
    lab = 'tmisct'
    T = numtree11(TREE_SCT)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scanTest_runs ` at the machine: ` poolAlgF ` (~ tmipla ) pushes the pool ` P = ( poolAlg Q x z k\' ).1 ` '
               'on 6, ` listLen 6 3 7 5 ` (~ tmillenb ) pushes ` # P ` on 3 (the pool entries are at most ` x ` , ~ tmpgmem , and '
               'there are at most ` ( poolAlg Q x z k\' ).2 ` of them, ~ poolalgcost ), ` x ` is moved aside (~ tmime ), ` theta ` '
               'duplicated (~ tmidupb ), ` x ` moved back, and ` cmpFrag 5 3 ` (~ tmicmpb ) sets ` cmp = compare theta ( # P ) ` ; '
               'every stack but 6 restored, within Lean\'s ` ( c + 1 ) 32 U + ( # P + 1 ) U + 4 U ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    fn, zn, on_, gn = c0['F e. NN0'], c0['Z e. NN0'], c0['O e. NN0'], c0['G e. NN0']
    ww, bn, cn = c0['W e. Word NN0'], c0['B e. NN0'], c0['C e. NN0']
    xw = c0[WG('X')]
    EOX = EWg('O', 'X')
    eox = ewg_(w, ph, 'O', on_, 'X', xw)
    eqs = {'0': (EWg('F', EOX), ewg_(w, ph, 'F', fn, EOX, eox)), '1': (EWg('Z', "X'"), ewg_(w, ph, 'Z', zn, "X'", c0[WG("X'")])),
           '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', c0[WG('Y')])), '4': (ENCL('W', "Y'"), enclg(w, ph, 'W', ww, "Y'", c0[WG("Y'")]))}
    B = Base(w, ph, T, N8, 'sct', eqs)
    B.g(EOX, eox)
    c, mk = B.c, B.mk
    LM = FRAGS['sct'].lmap()
    g = lambda k: B.S0.vals[k][2]
    pf = pool_facts(w, ph, c, fn, zn, gn, ww, bn, cn)
    P2M = '( 2 ^ %s )' % MS
    R = B.run()
    # 1. poolAlgF
    E6 = ENCL(PA1, DK(6))
    B.call(R, 'tmipla', {'X': EOX, 'P': PL('P', 0), 'E': LM['Y2']}, {},
           [('6', E6, B.g(E6, enclg(w, ph, PA1, pf['paw'], DK(6), g('6'))))])
    # 2. listLen 6 3 7 5 at B := MS
    E3 = EWg(PLEN, DK(3))
    pln = s([pf['paw'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, PLEN))
    B.call(R, 'tmillenb', {'K': '6', 'J': '3', 'I': '7', "I'": '5', 'L': PA1, 'R': DK(6), 'B': MS, 'P': PL('P', 1), 'E': LM['Y3']},
           {'%s e. Word NN0' % PA1: pf['paw'], '%s e. NN0' % MS: pf['msn'], RALB(PA1, MS): pf['ralb'], '%s < %s' % (PLEN, P2M): pf['lt']},
           [('3', E3, B.g(E3, ewg_(w, ph, PLEN, pln, DK(3), g('3'))))])
    # 3. moveEntry 0 7 5
    WF = '( encNatGam ` F )'
    E7 = EWg('F', DK(7))
    B.call(R, 'tmime', {'K': '0', 'J': '7', 'I': '5', 'W': WF, 'X': EOX, 'P': PL('P', 2), 'E': LM['Y4']},
           {WRD(WF, BITS): engb(w, ph, 'F', fn)}, [('0', EOX, eox), ('7', E7, B.g(E7, ewg_(w, ph, 'F', fn, DK(7), g('7'))))])
    # 4. dup 0 5 4
    E5 = EWg('O', DK(5))
    B.call(R, 'tmidupb', {'K': '0', 'J': '5', 'I': '4', 'F': 'O', 'N': 'B', 'X': 'X', 'P': PL('P', 3), 'E': LM['Y5']}, {},
           [('5', E5, B.g(E5, ewg_(w, ph, 'O', on_, DK(5), g('5'))))])
    # 5. moveEntry 7 0 5
    B.call(R, 'tmime', {'K': '7', 'J': '0', 'I': '5', 'W': WF, 'X': DK(7), 'P': PL('P', 4), 'E': LM['Y6']},
           {WRD(WF, BITS): engb(w, ph, 'F', fn)}, [('7', DK(7), g('7')), ('0', EWg('F', EOX), g('0'))])
    # 6. cmpFrag 5 3 at N := MS
    pf['cl'].leaf('O', 'NN0', on_)
    olt = linarith(w, ph, [c[LT2('O')], pf['m2']], 'O < %s' % P2M, closure=pf['cl'])
    B.call(R, 'tmicmpb', {'K': '5', 'J': '3', 'F': 'O', 'G': PLEN, 'N': MS, 'X': DK(5), 'Y': DK(3), 'P': PL('P', 5), 'E': 'E'},
           {'%s e. NN0' % PLEN: pln, '%s e. NN0' % MS: pf['msn'], 'O < %s' % P2M: olt, '%s < %s' % (PLEN, P2M): pf['lt']},
           [('5', DK(5), g('5')), ('3', DK(3), g('3'))])
    cur, out = R.normalize(N8)
    assert out == [('0', EWg('F', EOX)), ('6', E6)], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    Dst = triple_D(D)
    u0 = upidv(w, ph, 'D', '0', EWg('F', EOX), B.S0.vals['0'][1], mk['tv'], B.dd, mk['k']['0']['kd'])
    r0, x0 = w.rewrite(Dst, {UP('D', '0', EWg('F', EOX)): ('D', u0)}, ph)
    assert x0 == UP('D', '6', E6), x0
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', CMPC('O', PLEN), r0, Dst, x0))
    # the bound
    BND = triple_parts(STMTS11[lab].rsplit(' -> ', 1)[1][:-2])[2]
    cl = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn), 'O': ('NN0', on_)})
    cl.leaf(NW, 'NN0', pf['nw'])
    cl.leaf(PA2, 'NN0', pf['pa2n'])
    cl.leaf(PLEN, 'NN0', pln)
    msn, mpn = pf['msn'], cl.mem(MPA_, 'NN0')
    cl.leaf(TMS, 'NN0', tbn(w, ph, MS, msn))
    cl.leaf(TPA, 'NN0', tbn(w, ph, MPA_, mpn))
    cl.leaf(TB_, 'NN0', tbn(w, ph, 'B', bn))
    mb = me_bound_n(w, ph, 'F', fn, c[LT2('F')], 'B', bn, cl)
    mpm = linarith(w, ph, [pf['wbg'], pf['wcg'], cl.ge0('C'), cl.ge0('B'), cl.ge0(NW)], '%s <_ %s' % (MPA_, MS), closure=cl, products=True)
    t1 = s([mpn, msn, mpm, w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TPA, TMS))
    t2 = s([bn, msn, pf['bms'], w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TB_, TMS))
    P1 = '( %s + 1 )' % PA2
    f1 = s([cl.mem(TPA, 'RR'), cl.mem(TMS, 'RR'), cl.mem(P1, 'RR'), cl.ge0(P1), t1], 'lemul2ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, P1, TPA, P1, TMS))
    LWF = '( # ` %s )' % WF
    le = linarith(w, ph, [f1, t2, mb], '%s <_ %s' % (n, BND), closure=cl, atoms=[PA2, PLEN, TMS, TPA, TB_, LWF], products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run(unify_only=UO)


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
