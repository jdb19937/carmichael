"""Sortie KD1: ( log M ) ^ K <_ K ! M ^ B / B ^ K (kdlogpow)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_logpow():
    w = W('kdlogpow', 'Lean ` KDerivDetect.log_pow_le_rpow ` : ` ( log M ) ^ K <_ K ! M ^ B / B ^ K ` for ` M e. NN ` , ` B > 0 ` ( ` tppowfac ` at ` B log M ` ).')
    A = '( B e. RR+ /\\ K e. NN0 /\\ M e. NN )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    b = s([], 'simp1', 'B e. RR+'); kk = s([], 'simp2', 'K e. NN0'); m = s([], 'simp3', 'M e. NN')
    br = s([b], 'rpred', 'B e. RR'); bc = s([br], 'recnd', 'B e. CC')
    mr = s([m], 'nnrpd', 'M e. RR+')
    lg = s([mr], 'relogcld', '( log ` M ) e. RR')
    lg0 = s([s([m], 'nnred', 'M e. RR'), s([m], 'nnge1d', '1 <_ M'), w.inst('logge0')], 'syl2anc', '0 <_ ( log ` M )')
    X = '( B x. ( log ` M ) )'
    xr = s([br, lg], 'remulcld', '%s e. RR' % X)
    x0 = s([br, lg, s([b], 'rpge0d', '0 <_ B'), lg0], 'mulge0d', '0 <_ %s' % X)
    pf = s([xr, x0, kk, w.inst('tppowfac')], 'syl3anc', '( %s ^ K ) <_ ( ( ! ` K ) x. ( exp ` %s ) )' % (X, X))
    e1 = s([bc, s([lg], 'recnd', '( log ` M ) e. CC'), kk], 'mulexpd', '( %s ^ K ) = ( ( B ^ K ) x. ( ( log ` M ) ^ K ) )' % X)
    e2 = s([s([mr], 'rpcnd', 'M e. CC'), s([mr], 'rpne0d', 'M =/= 0'), bc], 'cxpefd', '( M ^c B ) = ( exp ` %s )' % X)
    e3 = s([e2], 'oveq2d', '( ( ! ` K ) x. ( M ^c B ) ) = ( ( ! ` K ) x. ( exp ` %s ) )' % X)
    p2 = s([pf, e1, s([e3], 'eqcomd', '( ( ! ` K ) x. ( exp ` %s ) ) = ( ( ! ` K ) x. ( M ^c B ) )' % X)], '3brtr3d', '( ( B ^ K ) x. ( ( log ` M ) ^ K ) ) <_ ( ( ! ` K ) x. ( M ^c B ) )')
    bk = s([b, s([kk], 'nn0zd', 'K e. ZZ')], 'rpexpcld', '( B ^ K ) e. RR+')
    lk = s([lg, kk], 'reexpcld', '( ( log ` M ) ^ K ) e. RR')
    rhs = s([s([s([kk], 'faccld', '( ! ` K ) e. NN')], 'nnred', '( ! ` K ) e. RR'), s([mr, br], 'rpcxpcld', '( M ^c B ) e. RR+') and s([s([mr, br], 'rpcxpcld', '( M ^c B ) e. RR+')], 'rpred', '( M ^c B ) e. RR')],
            'remulcld', '( ( ! ` K ) x. ( M ^c B ) ) e. RR')
    bi = s([lk, rhs, bk], 'lemuldiv2d', '( ( ( B ^ K ) x. ( ( log ` M ) ^ K ) ) <_ ( ( ! ` K ) x. ( M ^c B ) ) <-> ( ( log ` M ) ^ K ) <_ ( ( ( ! ` K ) x. ( M ^c B ) ) / ( B ^ K ) ) )')
    w.qed([p2, bi], 'mpbid', S['kdlogpow'])
    return run(w)


if __name__ == '__main__':
    gen_logpow()
