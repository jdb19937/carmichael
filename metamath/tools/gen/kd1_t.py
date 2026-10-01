"""Sortie KD1: the K-th derivative series of chi Lam is ( -1 ) ^ K times LSeries( log^K chi Lam ) (kdlsalg)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_lsalg():
    w = W('kdlsalg', 'Lean ` logMul_iterate ` / ` LSeries_iteratedDeriv ` in the form used: ` sum ( -u log k ) ^ K chi ( k ) Lam ( k ) k ^ -u S = ( -u 1 ) ^ K sum ( log k ) ^ K chi ( k ) Lam ( k ) k ^ -u S ` on ` Re S = 1 + E ` (convergence ` kdlsb ` ).')
    A0 = S['kdlsalg'].split(' -> ')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', NXH)
    ee = s([], 'simprl', '( E e. RR+ /\\ E <_ 1 )')
    sg = s([], 'simprr', '( S e. CC /\\ ( Re ` S ) = ( 1 + E ) /\\ K e. NN0 )')
    sc = s([sg], 'simp1d', 'S e. CC'); kk = s([sg], 'simp3d', 'K e. NN0')
    TB = lambda x: '( ( ( ( log ` %s ) ^ K ) x. ( %s x. ( Lam ` %s ) ) ) x. ( %s ^c -u S ) )' % (x, CHV(x), x, x)
    G = '( n e. NN |-> %s )' % TB('n')
    lsb = s([nx, ee, sg, w.inst('kdlsb')], 'syl3anc', '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` %s ) <_ %s )' % (G, LSK('K', 'S'), DIAG('K', '( 1 + E )')))
    cvg = s([lsb], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % G)
    Ak = '( %s /\\ k e. NN )' % A0
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    L = lambda st: lift(w, st, Ak)
    kn = b([], 'simpr', 'k e. NN')
    chk = b([b([L(nx), kn], 'jca', '( %s /\\ k e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CHV('k'))
    lam = b([b([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    lk = b([b([b([kn], 'nnrpd', 'k e. RR+')], 'relogcld', '( log ` k ) e. RR')], 'recnd', '( log ` k ) e. CC')
    lkK = b([lk, L(kk)], 'expcld', '( ( log ` k ) ^ K ) e. CC')
    ek = b([b([kn], 'nncnd', 'k e. CC'), b([L(sc)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')
    tbc = b([b([lkK, b([chk, lam], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHV('k'))], 'mulcld', '( ( ( log ` k ) ^ K ) x. ( %s x. ( Lam ` k ) ) ) e. CC' % CHV('k')), ek], 'mulcld', '%s e. CC' % TB('k'))
    idn = w.s([], 'id', '( n = k -> n = k )')
    cn, vn = w.congr(TB('n'), {'n': 'k'}, 'n = k', {'n': idn})
    gv = fvmd(w, Ak, G, 'k', vn, kn, tbc, cn, var='n')
    m1c = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % A0)
    m1k = s([m1c, kk], 'expcld', '( -u 1 ^ K ) e. CC')
    mc = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0), gv, tbc, cvg, m1k], 'isummulc2',
             '( %s -> ( ( -u 1 ^ K ) x. sum_ k e. NN %s ) = sum_ k e. NN ( ( -u 1 ^ K ) x. %s ) )' % (A0, TB('k'), TB('k')))
    # per k
    idn2 = w.s([], 'id', '( n = k -> n = k )')
    cn2, vn2 = w.congr('( %s x. ( Lam ` n ) )' % CHV('n'), {'n': 'k'}, 'n = k', {'n': idn2})
    cvk = fvmd(w, Ak, CVM, 'k', vn2, kn, b([chk, lam], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHV('k')), cn2, var='n')
    ng = b([lk], 'mulm1d', '( -u 1 x. ( log ` k ) ) = -u ( log ` k )')
    pe = b([b([ng], 'oveq1d', '( ( -u 1 x. ( log ` k ) ) ^ K ) = ( -u ( log ` k ) ^ K )'), b([L(m1c), lk, L(kk)], 'mulexpd', '( ( -u 1 x. ( log ` k ) ) ^ K ) = ( ( -u 1 ^ K ) x. ( ( log ` k ) ^ K ) )')],
           'eqtr3d', '( -u ( log ` k ) ^ K ) = ( ( -u 1 ^ K ) x. ( ( log ` k ) ^ K ) )')
    LHS = '( ( -u ( log ` k ) ^ K ) x. ( ( %s ` k ) x. ( k ^c -u S ) ) )' % CVM
    MID = '( ( ( -u 1 ^ K ) x. ( ( log ` k ) ^ K ) ) x. ( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) ) )' % CHV('k')
    t1 = b([pe, b([cvk], 'oveq1d', '( ( %s ` k ) x. ( k ^c -u S ) ) = ( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) )' % (CVM, CHV('k')))], 'oveq12d', '%s = %s' % (LHS, MID))
    c = Closure(w, Ak, {'( -u 1 ^ K )': ('CC', L(m1k)), '( ( log ` k ) ^ K )': ('CC', lkK), CHV('k'): ('CC', chk), '( Lam ` k )': ('CC', lam), '( k ^c -u S )': ('CC', ek)})
    for a_ in ('( -u 1 ^ K )', '( ( log ` k ) ^ K )', CHV('k'), '( Lam ` k )', '( k ^c -u S )'):
        c.atom(a_)
    t2 = ringeq(w, Ak, MID, '( ( -u 1 ^ K ) x. %s )' % TB('k'), c)
    tk = b([t1, t2], 'eqtrd', '%s = ( ( -u 1 ^ K ) x. %s )' % (LHS, TB('k')))
    sm = s([tk], 'sumeq2dv', '%s = sum_ k e. NN ( ( -u 1 ^ K ) x. %s )' % (S1I('K', 'S'), TB('k')))
    idk = w.s([], 'id', '( k = n -> k = n )')
    ck, nk = w.congr(TB('k'), {'k': 'n'}, 'k = n', {'k': idk})
    cb = w.s([ck], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (TB('k'), TB('n')))
    assert 'sum_ n e. NN %s' % TB('n') == LSK('K', 'S'), LSK('K', 'S')
    e3 = s([w.s([cb], 'a1i', '( %s -> sum_ k e. NN %s = %s )' % (A0, TB('k'), LSK('K', 'S')))], 'oveq2d', '( ( -u 1 ^ K ) x. sum_ k e. NN %s ) = ( ( -u 1 ^ K ) x. %s )' % (TB('k'), LSK('K', 'S')))
    w.qed([sm, mc, e3], '3eqtr2d' if False else 'T.', S['kdlsalg']) if False else None
    fin = s([sm, s([mc, e3], 'eqtr3d', 'sum_ k e. NN ( ( -u 1 ^ K ) x. %s ) = ( ( -u 1 ^ K ) x. %s )' % (TB('k'), LSK('K', 'S')))], 'eqtrd', '%s = ( ( -u 1 ^ K ) x. %s )' % (S1I('K', 'S'), LSK('K', 'S')))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdlsalg']))
    return run(w)


if __name__ == '__main__':
    gen_lsalg()
