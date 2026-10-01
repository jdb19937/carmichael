"""Sortie KD1: a holomorphic function equal to the Dirichlet-minus-poles function on a square has its derivatives (kdtcs)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift
from kd1_c import sqctx

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_tcs():
    w = W('kdtcs', 'If ` G ` is holomorphic on ` D ` containing ` SQ ( P , R ) ` and equals ` -u sum A ( k ) k ^ -u z - sum_ q W ( q ) / ( z - q ) ` there, its ` K ` -th derivative at ` P ` is the termwise one ( ` kdcdn ` twice, ` kdpsidn ` ; the boundary integrals agree on the frame).')
    A0 = S['kdtcs'].split(' -> ( ( ( CC Dn G )')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L = lambda st, ante=None: lift(w, st, ante or A0)
    HT = HP('T'); V = VSET(); SQP = SQ('P', 'R')
    g1 = s([], 'simp1', '( %s /\\ ( P e. CC /\\ R e. RR+ /\\ %s C_ D ) )' % (HOLF('G', 'D'), SQP))
    hg = s([g1], 'simpld', HOLF('G', 'D')); sqh = s([g1], 'simprd', '( P e. CC /\\ R e. RR+ /\\ %s C_ D )' % SQP)
    g2 = s([], 'simp2', '( ( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) ) /\\ %s )' % (AGR, ZH))
    g3 = s([], 'simp3', '( %s C_ %s /\\ A. z e. %s ( G ` z ) = %s /\\ K e. NN0 )' % (SQP, V, SQP, PSIK('0', 'z')))
    sv = s([g3], 'simp1d', '%s C_ %s' % (SQP, V)); eqz = s([g3], 'simp2d', 'A. z e. %s ( G ` z ) = %s' % (SQP, PSIK('0', 'z'))); kk = s([g3], 'simp3d', 'K e. NN0')
    pc = s([sqh], 'simp1d', 'P e. CC'); rp = s([sqh], 'simp2d', 'R e. RR+')
    cg = s([hg, sqh, kk, w.inst('kdcdn')], 'syl3anc', '( ( ( CC Dn G ) ` K ) ` P ) = ( ( ! ` K ) x. %s )' % TC('G', 'P', 'R', 'K'))
    # Psi holomorphic on V
    PS = PSI()
    one = w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % A0)
    MAPS = lambda x: '( z e. %s |-> %s )' % (V, PSIK(x, 'z'))
    KP = lambda x, xst: s([g2, xst, w.inst('kdpsidn')], 'syl2anc', '( %s /\\ ( ( CC Dn %s ) ` %s ) = %s )' % (HOLF(PS, V), PS, x, MAPS(x)))
    kpK = KP('K', kk)
    hps = s([kpK], 'simpld', HOLF(PS, V)); dK = s([kpK], 'simprd', '( ( CC Dn %s ) ` K ) = %s' % (PS, MAPS('K')))
    PSy = '( y e. %s |-> %s )' % (V, PSIK('0', 'y'))
    idzy = w.s([], 'id', '( z = y -> z = y )')
    czy, nzy = w.congr(PSIK('0', 'z'), {'z': 'y'}, 'z = y', {'z': idzy})
    cy = w.s([czy], 'cbvmptv', '%s = %s' % (PS, PSy))
    cya = w.s([cy], 'a1i', '( %s -> %s = %s )' % (A0, PS, PSy))
    hps = s([hps, holeq(w, A0, cya, PS, PSy, V)], 'mpbid', HOLF(PSy, V))
    PS0 = PS
    PS = PSy
    cps = s([hps, s([pc, rp, sv], '3jca', '( P e. CC /\\ R e. RR+ /\\ %s C_ %s )' % (SQP, V)), kk, w.inst('kdcdn')], 'syl3anc', '( ( ( CC Dn %s ) ` K ) ` P ) = ( ( ! ` K ) x. %s )' % (PS, TC(PS, 'P', 'R', 'K')))
    # the value at P
    pS = s([sqctx(w, A0, pc, rp)['inp'], w.inst('crectinp')], 'syl', 'P e. %s' % SQP)
    pV = s([sv, pS], 'sseldd', 'P e. %s' % V)
    idp = w.s([], 'id', '( z = P -> z = P )')
    cp, vp_ = w.congr(PSIK('K', 'z'), {'z': 'P'}, 'z = P', {'z': idp})
    assert vp_ == PSIK('K', 'P'), vp_
    fvp = w.s([cp, w.s([], 'eqid', '%s = %s' % (MAPS('K'), MAPS('K')))], 'fvmptg', '( ( P e. %s /\\ %s e. _V ) -> ( %s ` P ) = %s )' % (V, vp_, MAPS('K'), vp_))
    vpv = s([pV, w.s([w.s([], 'ovex', '%s e. _V' % vp_)], 'a1i', '( %s -> %s e. _V )' % (A0, vp_)), fvp], 'syl2anc', '( %s ` P ) = %s' % (MAPS('K'), vp_))
    dvP = s([s([dK], 'fveq1d', '( ( ( CC Dn %s ) ` K ) ` P ) = ( %s ` P )' % (PS0, MAPS('K'))), vpv], 'eqtrd', '( ( ( CC Dn %s ) ` K ) ` P ) = %s' % (PS0, vp_))
    # the two boundary integrals agree
    q = sqctx(w, A0, pc, rp)
    A_, B_ = q['A'], q['B']
    FR = FRM(A_, B_)
    Au = '( %s /\\ u e. %s )' % (A0, FR)
    uS = w.s([L(q['fr'], Au), w.s([], 'simpr', '( %s -> u e. %s )' % (Au, FR))], 'sseldd', '( %s -> u e. ( %s \\ { P } ) )' % (Au, SQP))
    uSq = w.s([uS, w.inst('eldifi')], 'syl', '( %s -> u e. %s )' % (Au, SQP))
    uV = w.s([L(sv, Au), uSq], 'sseldd', '( %s -> u e. %s )' % (Au, V))
    idu = w.s([], 'id', '( z = u -> z = u )')
    cu0, vu0 = w.congr(PSIK('0', 'z'), {'z': 'u'}, 'z = u', {'z': idu})
    cgz = w.s([w.s([], 'fveq2', '( z = u -> ( G ` z ) = ( G ` u ) )'), cu0], 'eqeq12d', '( z = u -> ( ( G ` z ) = %s <-> ( G ` u ) = %s ) )' % (PSIK('0', 'z'), vu0))
    gu = w.s([uSq, L(eqz, Au), w.s([cgz], 'rspcv', '( u e. %s -> ( A. z e. %s ( G ` z ) = %s -> ( G ` u ) = %s ) )' % (SQP, SQP, PSIK('0', 'z'), vu0))], 'sylc', '( %s -> ( G ` u ) = %s )' % (Au, vu0))
    idyu = w.s([], 'id', '( y = u -> y = u )')
    cyu, vyu = w.congr(PSIK('0', 'y'), {'y': 'u'}, 'y = u', {'y': idyu})
    assert vyu == vu0
    fvu = w.s([cyu, w.s([], 'eqid', '%s = %s' % (PS, PS))], 'fvmptg', '( ( u e. %s /\\ %s e. _V ) -> ( %s ` u ) = %s )' % (V, vu0, PS, vu0))
    psu = w.s([uV, w.s([w.s([], 'ovex', '%s e. _V' % vu0)], 'a1i', '( %s -> %s e. _V )' % (Au, vu0)), fvu], 'syl2anc', '( %s -> ( %s ` u ) = %s )' % (Au, PS, vu0))
    gpu = w.s([gu, psu], 'eqtr4d', '( %s -> ( G ` u ) = ( %s ` u ) )' % (Au, PS))
    IG = TCI('G', 'P', 'R', 'K'); IP = TCI(PS, 'P', 'R', 'K')
    PW = '( ( u - P ) ^ ( K + 1 ) )'
    cig, vig = w.congr('( ( G ` z ) / ( ( z - P ) ^ ( K + 1 ) ) )', {'z': 'u'}, 'z = u', {'z': idu})
    cip, vip = w.congr('( ( %s ` z ) / ( ( z - P ) ^ ( K + 1 ) ) )' % PS, {'z': 'u'}, 'z = u', {'z': idu})
    fig = w.s([cig, w.s([], 'eqid', '%s = %s' % (IG, IG))], 'fvmptg', '( ( u e. ( %s \\ { P } ) /\\ %s e. _V ) -> ( %s ` u ) = %s )' % (SQP, vig, IG, vig))
    fip = w.s([cip, w.s([], 'eqid', '%s = %s' % (IP, IP))], 'fvmptg', '( ( u e. ( %s \\ { P } ) /\\ %s e. _V ) -> ( %s ` u ) = %s )' % (SQP, vip, IP, vip))
    vg = w.s([uS, w.s([w.s([], 'ovex', '%s e. _V' % vig)], 'a1i', '( %s -> %s e. _V )' % (Au, vig)), fig], 'syl2anc', '( %s -> ( %s ` u ) = %s )' % (Au, IG, vig))
    vpp = w.s([uS, w.s([w.s([], 'ovex', '%s e. _V' % vip)], 'a1i', '( %s -> %s e. _V )' % (Au, vip)), fip], 'syl2anc', '( %s -> ( %s ` u ) = %s )' % (Au, IP, vip))
    gq = w.s([gpu], 'oveq1d', '( %s -> %s = %s )' % (Au, vig, vip))
    agree = w.s([vg, gq, vpp], '3eqtr4d', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (Au, IG, IP))
    agall = w.s([agree], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, FR, IG, IP))
    SQD = '( %s \\ { P } )' % SQP
    sqx = w.s([w.s([w.s([], 'ovex', '%s e. _V' % SQP), w.inst('difexg')], 'ax-mp', '%s e. _V' % SQD)], 'a1i', '( %s -> %s e. _V )' % (A0, SQD))
    RI = lambda G_: '( %s rectint <. %s , %s >. )' % (G_, A_, B_)
    eqe = s([s([q['ab'], w.s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '( %s -> %s C_ %s )' % (A0, FR, FR))], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ %s C_ %s )' % (A_, B_, FR, FR)),
             s([w.s([sqx], 'mptexd', '( %s -> %s e. _V )' % (A0, IG)), w.s([sqx], 'mptexd', '( %s -> %s e. _V )' % (A0, IP))], 'jca', '( %s e. _V /\\ %s e. _V )' % (IG, IP)), agall, w.inst('rectinteqe')],
            'syl3anc', '%s = %s' % (RI(IG), RI(IP)))
    tce = s([eqe], 'oveq1d', '%s = %s' % (TC('G', 'P', 'R', 'K'), TC(PS, 'P', 'R', 'K')))
    brg = s([s([s([cya], 'oveq2d', '( CC Dn %s ) = ( CC Dn %s )' % (PS0, PSy))], 'fveq1d', '( ( CC Dn %s ) ` K ) = ( ( CC Dn %s ) ` K )' % (PS0, PSy))], 'fveq1d',
            '( ( ( CC Dn %s ) ` K ) ` P ) = ( ( ( CC Dn %s ) ` K ) ` P )' % (PS0, PSy))
    dvP = s([brg, dvP], 'eqtr3d', '( ( ( CC Dn %s ) ` K ) ` P ) = %s' % (PSy, vp_))
    fin = s([cg, s([tce], 'oveq2d', '( ( ! ` K ) x. %s ) = ( ( ! ` K ) x. %s )' % (TC('G', 'P', 'R', 'K'), TC(PS, 'P', 'R', 'K'))), s([cps], 'eqcomd', '( ( ! ` K ) x. %s ) = ( ( ( CC Dn %s ) ` K ) ` P )' % (TC(PS, 'P', 'R', 'K'), PS))],
            '3eqtrd', '( ( ( CC Dn G ) ` K ) ` P ) = ( ( ( CC Dn %s ) ` K ) ` P )' % PS)
    w.qed([fin, dvP], 'eqtrd', S['kdtcs'])
    return run(w)


if __name__ == '__main__':
    gen_tcs()
