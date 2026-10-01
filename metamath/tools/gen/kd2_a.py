"""Sortie KD2: budget helpers (kd2tc, kd2nmul, kd2stir).
MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_a.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd2lib import *
from cl import formula_of, split_imp
from lin import linarith
import num

only = sys.argv[1:]


def gen_tc():
    w = W('kd2tc', 'The Turan per-zero constant ` 56 e ` is positive and below ` 168 ` (Lean ` KDerivDetect.turan_const_bounds ` : ` 56 e < 153 ` ; set.mm main has ` e < 3 ` ).')
    e1 = w.s([], 'epr', '_e e. RR+')
    de = w.s([], 'df-e', '_e = ( exp ` 1 )')
    er = w.s([de, e1], 'eqeltrri', '( exp ` 1 ) e. RR+')
    n56 = num.rp(w, '; 5 6')
    pr = w.s([w.s([n56, er], 'pm3.2i', '( ; 5 6 e. RR+ /\\ ( exp ` 1 ) e. RR+ )'), w.inst('rpmulcl')], 'ax-mp', '%s e. RR+' % C56E)
    lt3 = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    lt3e = w.s([de, lt3], 'eqbrtrri', '( exp ` 1 ) < 3')
    rr = w.s([er, w.inst('rpre')], 'ax-mp', '( exp ` 1 ) e. RR')
    lt = w.s([w.s([rr], 'a1i', '( T. -> ( exp ` 1 ) e. RR )'),
              w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( T. -> 3 e. RR )'), w.s([n56], 'a1i', '( T. -> ; 5 6 e. RR+ )'), w.s([lt3e], 'a1i', '( T. -> ( exp ` 1 ) < 3 )')],
             'ltmul2dd', '( T. -> ( ; 5 6 x. ( exp ` 1 ) ) < ( ; 5 6 x. 3 ) )')
    m = num.mul_nat(w, 56, 3)
    lt2 = w.s([w.s([lt], 'mptru', '( ; 5 6 x. ( exp ` 1 ) ) < ( ; 5 6 x. 3 )'), m], 'breqtri', '%s < ; ; 1 6 8' % C56E)
    w.s([pr, lt2], 'pm3.2i', S['kd2tc'], name='qed')
    return only_run(w, only)

def e1rp(w, A):
    """( A -> ( exp ` 1 ) e. RR+ )"""
    e1 = w.s([], 'epr', '_e e. RR+'); de = w.s([], 'df-e', '_e = ( exp ` 1 )')
    return w.s([w.s([de, e1], 'eqeltrri', '( exp ` 1 ) e. RR+')], 'a1i', '( %s -> ( exp ` 1 ) e. RR+ )' % A)


def gen_nmul():
    w = W('kd2nmul', 'Lean ` KDerivDetect.nat_mul_pow_le_pow ` : ` N a^N <_ b^N ` for ` 2 a <_ b ` , ` 0 <_ a ` ( ~ bernneq3 ).')
    A0 = S['kd2nmul'].split(' -> ( N x.')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simp1', [], '( A e. RR /\\ 0 <_ A )'); g2 = d('simp2', [], '( B e. RR /\\ ( 2 x. A ) <_ B )')
    ar = d('simpld', [g1], 'A e. RR'); a0 = d('simprd', [g1], '0 <_ A')
    br = d('simpld', [g2], 'B e. RR'); ab = d('simprd', [g2], '( 2 x. A ) <_ B')
    nn = d('simp3', [], 'N e. NN0')
    u2 = w.s([w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % A0)
    lt = d('syl2anc', [u2, nn, w.inst('bernneq3')], 'N < ( 2 ^ N )')
    nr = d('nn0red', [nn], 'N e. RR')
    two = a1(w, A0, '2re', '2 e. RR')
    p2 = d('reexpcld', [two, nn], '( 2 ^ N ) e. RR')
    pa = d('reexpcld', [ar, nn], '( A ^ N ) e. RR')
    le1 = d('ltled', [nr, p2, lt], 'N <_ ( 2 ^ N )')
    le2 = d('lemul1ad', [nr, p2, pa, d('expge0d', [ar, nn, a0], '0 <_ ( A ^ N )'), le1], '( N x. ( A ^ N ) ) <_ ( ( 2 ^ N ) x. ( A ^ N ) )')
    tc = a1(w, A0, '2cn', '2 e. CC')
    ac = d('recnd', [ar], 'A e. CC')
    eq = d('mulexpd', [tc, ac, nn], '( ( 2 x. A ) ^ N ) = ( ( 2 ^ N ) x. ( A ^ N ) )')
    ta = d('remulcld', [two, ar], '( 2 x. A ) e. RR')
    ta0 = d('mulge0d', [two, ar, a1(w, A0, '0le2', '0 <_ 2'), a0], '0 <_ ( 2 x. A )')
    le3 = d('leexp1ad', [ta, br, nn, ta0, ab], '( ( 2 x. A ) ^ N ) <_ ( B ^ N )')
    le4 = d('eqbrtrrd', [eq, le3], '( ( 2 ^ N ) x. ( A ^ N ) ) <_ ( B ^ N )')
    fin = d('letrd', [d('remulcld', [nr, pa], '( N x. ( A ^ N ) ) e. RR'), d('remulcld', [p2, pa], '( ( 2 ^ N ) x. ( A ^ N ) ) e. RR'),
                      d('reexpcld', [br, nn], '( B ^ N ) e. RR'), le2, le4], '( N x. ( A ^ N ) ) <_ ( B ^ N )')
    w.qed([fin], 'idi', S['kd2nmul'])
    return only_run(w, only)


def gen_stir():
    w = W('kd2stir', 'Lean ` KDerivDetect.factorial_ge_div_exp_pow ` and ` hstir ` : ` ( A / e )^K <_ K! ` for ` 0 <_ A <_ K ` ( TP ~ tppowfac at ` X = K ` ).')
    A0 = S['kd2stir'].split(' -> ( ( A /')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simpl', [], '( A e. RR /\\ 0 <_ A )'); g2 = d('simpr', [], '( K e. NN0 /\\ A <_ K )')
    ar = d('simpld', [g1], 'A e. RR'); a0 = d('simprd', [g1], '0 <_ A')
    kn = d('simpld', [g2], 'K e. NN0'); ak = d('simprd', [g2], 'A <_ K')
    kr = d('nn0red', [kn], 'K e. RR'); k0 = d('nn0ge0d', [kn], '0 <_ K')
    er = e1rp(w, A0); err = d('rpred', [er], '( exp ` 1 ) e. RR')
    ae = d('rerpdivcld', [ar, er], '( A / ( exp ` 1 ) ) e. RR')
    ke = d('rerpdivcld', [kr, er], '( K / ( exp ` 1 ) ) e. RR')
    le1 = d('leexp1ad', [ae, ke, kn, d('divge0d', [ar, er, a0], '0 <_ ( A / ( exp ` 1 ) )'), d('lediv1dd', [ar, kr, er, ak], '( A / ( exp ` 1 ) ) <_ ( K / ( exp ` 1 ) )')],
            '( ( A / ( exp ` 1 ) ) ^ K ) <_ ( ( K / ( exp ` 1 ) ) ^ K )')
    kc = d('recnd', [kr], 'K e. CC'); ec = d('rpcnd', [er], '( exp ` 1 ) e. CC'); en = d('rpne0d', [er], '( exp ` 1 ) =/= 0')
    eq1 = d('expdivd', [kc, ec, en, kn], '( ( K / ( exp ` 1 ) ) ^ K ) = ( ( K ^ K ) / ( ( exp ` 1 ) ^ K ) )')
    tp = d('syl3anc', [kr, k0, kn, w.inst('tppowfac')], '( K ^ K ) <_ ( ( ! ` K ) x. ( exp ` K ) )')
    # exp K = ( exp 1 ) ^ K
    kz = d('nn0zd', [kn], 'K e. ZZ')
    ef = d('syl2anc', [a1(w, A0, 'ax-1cn', '1 e. CC'), kz, w.inst('efexp')], '( exp ` ( K x. 1 ) ) = ( ( exp ` 1 ) ^ K )')
    k1 = d('fveq2d', [d('mulridd', [kc], '( K x. 1 ) = K')], '( exp ` ( K x. 1 ) ) = ( exp ` K )')
    ef2 = d('eqtr3d', [k1, ef], '( exp ` K ) = ( ( exp ` 1 ) ^ K )')
    tp2 = d('breqtrd', [tp, d('oveq2d', [ef2], '( ( ! ` K ) x. ( exp ` K ) ) = ( ( ! ` K ) x. ( ( exp ` 1 ) ^ K ) )')],
            '( K ^ K ) <_ ( ( ! ` K ) x. ( ( exp ` 1 ) ^ K ) )')
    ekp = d('rpexpcld', [er, kz], '( ( exp ` 1 ) ^ K ) e. RR+')
    fr = d('nnred', [d('faccld', [kn], '( ! ` K ) e. NN')], '( ! ` K ) e. RR')
    kk = d('reexpcld', [kr, kn], '( K ^ K ) e. RR')
    le2 = d('mpbird', [tp2, d('ledivmul2d', [kk, fr, ekp], '( ( ( K ^ K ) / ( ( exp ` 1 ) ^ K ) ) <_ ( ! ` K ) <-> ( K ^ K ) <_ ( ( ! ` K ) x. ( ( exp ` 1 ) ^ K ) ) )')],
             '( ( K ^ K ) / ( ( exp ` 1 ) ^ K ) ) <_ ( ! ` K )')
    le3 = d('eqbrtrd', [eq1, le2], '( ( K / ( exp ` 1 ) ) ^ K ) <_ ( ! ` K )')
    fin = d('letrd', [d('reexpcld', [ae, kn], '( ( A / ( exp ` 1 ) ) ^ K ) e. RR'), d('reexpcld', [ke, kn], '( ( K / ( exp ` 1 ) ) ^ K ) e. RR'), fr, le1, le3],
            '( ( A / ( exp ` 1 ) ) ^ K ) <_ ( ! ` K )')
    w.qed([fin], 'idi', S['kd2stir'])
    return only_run(w, only)



if __name__ == '__main__':
    gen_tc()
    gen_nmul()
    gen_stir()
