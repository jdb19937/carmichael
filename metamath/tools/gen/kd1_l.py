"""Sortie KD1: termwise bound of the twisted log-power series (kdterm)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_term():
    w = W('kdterm', 'Lean ` KDerivDetect.norm_term_log_pow_twist_le ` : ` abs ( ( log M ) ^ K chi ( M ) Lam ( M ) M ^ -u S ) <_ Lam ( M ) ( log M ) ^ K M ^ -u Re S ` (C7b ` lchvmtm ` ).')
    A0 = S['kdterm'].split(' -> ( abs')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', NXH)
    sc = s([], 'simpr1', 'S e. CC'); kk = s([], 'simpr2', 'K e. NN0'); mn = s([], 'simpr3', 'M e. NN')
    CH = CHV('M')
    L = '( log ` M )'
    mr = s([mn], 'nnrpd', 'M e. RR+')
    lr = s([mr], 'relogcld', '%s e. RR' % L)
    l0 = s([s([mn], 'nnred', 'M e. RR'), s([mn], 'nnge1d', '1 <_ M'), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L)
    LK = '( %s ^ K )' % L
    lkr = s([lr, kk], 'reexpcld', '%s e. RR' % LK); lk0 = s([lr, kk, l0], 'expge0d', '0 <_ %s' % LK)
    lkc = s([lkr], 'recnd', '%s e. CC' % LK)
    chc = s([s([nx, mn], 'jca', '( %s /\\ M e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CH)
    lam = s([mn, w.inst('vmacl')], 'syl', '( Lam ` M ) e. RR'); lamc = s([lam], 'recnd', '( Lam ` M ) e. CC')
    EM = '( M ^c -u S )'
    emc = s([s([mn], 'nncnd', 'M e. CC'), s([sc], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % EM)
    T0 = '( ( %s x. ( Lam ` M ) ) x. %s )' % (CH, EM)
    tm = s([s([nx, s([mn, sc], 'jca', '( M e. NN /\\ S e. CC )')], 'jca', '( %s /\\ ( M e. NN /\\ S e. CC ) )' % NXH), w.inst('lchvmtm')], 'syl',
           '( abs ` %s ) <_ ( ( Lam ` M ) x. ( M ^c -u ( Re ` S ) ) )' % T0)
    c = Closure(w, A0, {LK: ('CC', lkc), CH: ('CC', chc), '( Lam ` M )': ('CC', lamc), EM: ('CC', emc)})
    for a_ in (LK, CH, '( Lam ` M )', EM):
        c.atom(a_)
    LHS = '( ( %s x. ( %s x. ( Lam ` M ) ) ) x. %s )' % (LK, CH, EM)
    e1 = ringeq(w, A0, LHS, '( %s x. %s )' % (LK, T0), c)
    t0c = s([s([chc, lamc], 'mulcld', '( %s x. ( Lam ` M ) ) e. CC' % CH), emc], 'mulcld', '%s e. CC' % T0)
    a1 = s([s([e1], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. %s ) )' % (LHS, LK, T0)), s([lkc, t0c], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (LK, T0, LK, T0)),
            s([s([lkr, lk0], 'absidd', '( abs ` %s ) = %s' % (LK, LK))], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (LK, T0, LK, T0))],
           '3eqtrd', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (LHS, LK, T0))
    ER = '( M ^c -u ( Re ` S ) )'
    err = s([mr, s([s([sc], 'recld', '( Re ` S ) e. RR')], 'renegcld', '-u ( Re ` S ) e. RR')], 'rpcxpcld', '%s e. RR+' % ER)
    rr = s([lam, s([err], 'rpred', '%s e. RR' % ER)], 'remulcld', '( ( Lam ` M ) x. %s ) e. RR' % ER)
    b1 = s([s([t0c], 'abscld', '( abs ` %s ) e. RR' % T0), rr, lkr, lk0, tm], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. ( ( Lam ` M ) x. %s ) )' % (LK, T0, LK, ER))
    c.leaf(ER, 'CC', s([err], 'rpcnd', '%s e. CC' % ER)); c.atom(ER)
    e2 = ringeq(w, A0, '( %s x. ( ( Lam ` M ) x. %s ) )' % (LK, ER), '( ( ( Lam ` M ) x. %s ) x. %s )' % (LK, ER), c)
    w.qed([a1, b1, e2], '3brtr4d' if False else 'T.', S['kdterm']) if False else None
    fin = s([s([a1, b1], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( ( Lam ` M ) x. %s ) )' % (LHS, LK, ER)), e2], 'breqtrd', '( abs ` %s ) <_ ( ( ( Lam ` M ) x. %s ) x. %s )' % (LHS, LK, ER))
    w.qed([fin], 'id' if False else 'mp1i' if False else 'syl' if False else 'T.', S['kdterm']) if False else w.lines.append('qed:%s:idi |- %s' % (fin, S['kdterm']))
    return run(w)


if __name__ == '__main__':
    gen_term()
