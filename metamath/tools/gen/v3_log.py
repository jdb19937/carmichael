"""Sortie v3: the logarithm bounds of the final assemblies.

logp1le   ( B e. RR+ -> ( log ` ( B + 1 ) ) <_ B )
logp1le2  ( W e. ( ZZ>= ` 2 ) -> ( log ` ( W + 1 ) ) <_ ( 2 x. ( log ` W ) ) )
logpwub   ( ( A e. NN /\\ B e. NN0 /\\ K e. NN0 ) ->
              ( A < ( ( B + 1 ) ^ K ) -> ( log ` A ) <_ ( K x. ( log ` ( B + 1 ) ) ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst
from lin import linarith, nlinarith


def logp1le():
    w = WS('logp1le', 'log ( B + 1 ) is at most B for positive real B.')
    A = 'B e. RR+'
    st = mkst(w, A)
    br = st([], 'rpred', 'B e. RR')
    bc = st([br], 'recnd', 'B e. CC')
    one = st([], '1red', '1 e. RR')
    onec = st([one], 'recnd', '1 e. CC')
    eg = st([], 'efgt1p', '( 1 + B ) < ( exp ` B )')
    onerp = st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')
    sumrp = st([onerp], 'rpaddcld', '( 1 + B ) e. RR+')
    exrp = st([br, w.inst('rpefcl')], 'syl', '( exp ` B ) e. RR+')
    lt = st([sumrp, exrp, w.inst('logltb')], 'syl2anc',
            '( ( 1 + B ) < ( exp ` B ) <-> ( log ` ( 1 + B ) ) < ( log ` ( exp ` B ) ) )')
    lt2 = st([lt, eg], 'mpbid', '( log ` ( 1 + B ) ) < ( log ` ( exp ` B ) )')
    ef = st([br, w.inst('relogef')], 'syl', '( log ` ( exp ` B ) ) = B')
    lt3 = st([lt2, ef], 'breqtrd', '( log ` ( 1 + B ) ) < B')
    ac = st([onec, bc], 'addcomd', '( 1 + B ) = ( B + 1 )')
    lt4 = st([ac], 'fveq2d', '( log ` ( 1 + B ) ) = ( log ` ( B + 1 ) )')
    lt5 = st([lt4, lt3], 'eqbrtrrd', '( log ` ( B + 1 ) ) < B')
    lgr = st([sumrp], 'relogcld', '( log ` ( 1 + B ) ) e. RR')
    lgr2 = st([lt4, lgr], 'eqeltrrd', '( log ` ( B + 1 ) ) e. RR')
    w.qed([lgr2, br, lt5], 'ltled', '( %s -> ( log ` ( B + 1 ) ) <_ B )' % A)
    return w


def logp1le2():
    w = WS('logp1le2', 'log ( W + 1 ) is at most twice log W for an integer W of at least 2.')
    A = 'W e. ( ZZ>= ` 2 )'
    st = mkst(w, A)
    wr = st([], 'eluzelre', 'W e. RR')
    w2 = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    wle = st([], 'eluzle', '2 <_ W')
    wc = st([wr], 'recnd', 'W e. CC')
    one = st([], '1red', '1 e. RR')
    wp1 = st([wr, one], 'readdcld', '( W + 1 ) e. RR')
    wsq = st([wr, wr], 'remulcld', '( W x. W ) e. RR')
    le = nlinarith(w, A, [wle], '( W + 1 ) <_ ( W x. W )', leaves={'W': wr})
    # positivity
    zr = st([], '0red', '0 e. RR')
    wpos = linarith(w, A, [wle], '0 < W', leaves={'W': wr})
    wrp = st([wr, wpos], 'elrpd', 'W e. RR+')
    onerp = st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')
    wp1rp = st([wrp, onerp], 'rpaddcld', '( W + 1 ) e. RR+')
    wsqrp = st([wrp, wrp], 'rpmulcld', '( W x. W ) e. RR+')
    lg = st([wp1rp, wsqrp, w.inst('logleb')], 'syl2anc',
            '( ( W + 1 ) <_ ( W x. W ) <-> ( log ` ( W + 1 ) ) <_ ( log ` ( W x. W ) ) )')
    lg2 = st([lg, le], 'mpbid', '( log ` ( W + 1 ) ) <_ ( log ` ( W x. W ) )')
    lm = st([wrp, wrp, w.inst('relogmul')], 'syl2anc',
            '( log ` ( W x. W ) ) = ( ( log ` W ) + ( log ` W ) )')
    lgw = st([wrp], 'relogcld', '( log ` W ) e. RR')
    lgwc = st([lgw], 'recnd', '( log ` W ) e. CC')
    tw = st([lgwc], '2timesd', '( 2 x. ( log ` W ) ) = ( ( log ` W ) + ( log ` W ) )')
    lm2 = st([lm, tw], 'eqtr4d', '( log ` ( W x. W ) ) = ( 2 x. ( log ` W ) )')
    w.qed([lg2, lm2], 'breqtrd',
          '( %s -> ( log ` ( W + 1 ) ) <_ ( 2 x. ( log ` W ) ) )' % A)
    return w


def logpwub():
    w = WS('logpwub', 'From A < ( B + 1 ) ^ K, log A is at most K times log ( B + 1 ).')
    A = '( ( A e. NN /\\ B e. NN0 /\\ K e. NN0 ) /\\ A < ( ( B + 1 ) ^ K ) )'
    st = mkst(w, A)
    ann = st([], 'simpl1', 'A e. NN')
    bn0 = st([], 'simpl2', 'B e. NN0')
    kn0 = st([], 'simpl3', 'K e. NN0')
    lt = st([], 'simpr', 'A < ( ( B + 1 ) ^ K )')
    arp = st([ann], 'nnrpd', 'A e. RR+')
    ar = st([arp], 'rpred', 'A e. RR')
    bnn = st([bn0, w.inst('nn0p1nn')], 'syl', '( B + 1 ) e. NN')
    brp = st([bnn], 'nnrpd', '( B + 1 ) e. RR+')
    br = st([brp], 'rpred', '( B + 1 ) e. RR')
    kz = st([kn0], 'nn0zd', 'K e. ZZ')
    pwrp = st([brp, kz], 'rpexpcld', '( ( B + 1 ) ^ K ) e. RR+')
    pwr = st([pwrp], 'rpred', '( ( B + 1 ) ^ K ) e. RR')
    le = st([ar, pwr, lt], 'ltled', 'A <_ ( ( B + 1 ) ^ K )')
    lg = st([arp, pwrp, w.inst('logleb')], 'syl2anc',
            '( A <_ ( ( B + 1 ) ^ K ) <-> ( log ` A ) <_ ( log ` ( ( B + 1 ) ^ K ) ) )')
    lg2 = st([lg, le], 'mpbid', '( log ` A ) <_ ( log ` ( ( B + 1 ) ^ K ) )')
    ex = st([brp, kz, w.inst('relogexp')], 'syl2anc',
            '( log ` ( ( B + 1 ) ^ K ) ) = ( K x. ( log ` ( B + 1 ) ) )')
    fin = st([lg2, ex], 'breqtrd', '( log ` A ) <_ ( K x. ( log ` ( B + 1 ) ) )')
    w.qed([fin], 'ex',
          '( ( A e. NN /\\ B e. NN0 /\\ K e. NN0 ) -> ( A < ( ( B + 1 ) ^ K ) -> '
          '( log ` A ) <_ ( K x. ( log ` ( B + 1 ) ) ) ) )')
    return w


ALL = {'logp1le': logp1le, 'logp1le2': logp1le2, 'logpwub': logpwub}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
