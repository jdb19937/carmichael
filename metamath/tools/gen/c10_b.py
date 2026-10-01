"""Sortie C10: the Blaschke numerator product is entire (blent)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
import congr as _cg
from c10_freeze import S as FS


def gen_blent():
    w = W('blent', 'The finite product of the normalised Blaschke numerators ` R - ( * ( k - C ) / R ) ( s - C ) ` raised to the orders ` O ( k ) ` is an entire function of ` s ` .')
    A0 = '( ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN ) /\\ ( C e. CC /\\ R e. RR+ ) )'
    zf = w.s([], 'simpl1', '( %s -> Z e. Fin )' % A0)
    zc = w.s([], 'simpl2', '( %s -> Z C_ CC )' % A0)
    of = w.s([], 'simpl3', '( %s -> O : Z --> NN )' % A0)
    cs = w.s([], 'simprl', '( %s -> C e. CC )' % A0)
    rp = w.s([], 'simprr', '( %s -> R e. RR+ )' % A0)
    A1 = '( %s /\\ k e. Z )' % A0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L = lambda st: lift(w, st, A1)
    kz = s([], 'simpr', 'k e. Z')
    kc = s([L(zc), kz], 'sseldd', 'k e. CC')
    c1 = L(cs)
    rc = s([s([L(rp)], 'rpred', 'R e. RR')], 'recnd', 'R e. CC'); rne = s([L(rp)], 'rpne0d', 'R =/= 0')
    X = '( k - C )'
    K = '( ( * ` %s ) / R )' % X
    Kc = s([s([s([kc, c1], 'subcld', '%s e. CC' % X)], 'cjcld', '( * ` %s ) e. CC' % X), rc, rne], 'divcld', '%s e. CC' % K)
    nn = s([L(of), kz], 'ffvelcdmd', '( O ` k ) e. NN')
    # derivative of the affine map
    A2 = '( %s /\\ s e. CC )' % A1
    L2 = lambda st: lift(w, st, A2)
    s2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A2, f))
    sc = s2([], 'simpr', 's e. CC')
    ccp = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A1)
    one = s2([], '1cnd', '1 e. CC'); zero = s2([], '0cnd', '0 e. CC')
    d1 = s([ccp], 'dvmptid', '( CC _D ( s e. CC |-> s ) ) = ( s e. CC |-> 1 )')
    d2 = s([ccp, c1], 'dvmptc', '( CC _D ( s e. CC |-> C ) ) = ( s e. CC |-> 0 )')
    sC = '( s - C )'
    d3 = s([ccp, sc, one, d1, L2(c1), zero, d2], 'dvmptsub', '( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> ( 1 - 0 ) )' % sC)
    scc = s2([sc, L2(c1)], 'subcld', '%s e. CC' % sC)
    o0 = s2([one, zero], 'subcld', '( 1 - 0 ) e. CC')
    d4 = s([ccp, scc, o0, d3, Kc], 'dvmptcmul', '( CC _D ( s e. CC |-> ( %s x. %s ) ) ) = ( s e. CC |-> ( %s x. ( 1 - 0 ) ) )' % (K, sC, K))
    d5 = s([ccp, rc], 'dvmptc', '( CC _D ( s e. CC |-> R ) ) = ( s e. CC |-> 0 )')
    BL = BLF('k', 's')
    DB = '( 0 - ( %s x. ( 1 - 0 ) ) )' % K
    ksc = s2([L2(Kc), scc], 'mulcld', '( %s x. %s ) e. CC' % (K, sC))
    ko = s2([L2(Kc), o0], 'mulcld', '( %s x. ( 1 - 0 ) ) e. CC' % K)
    d6 = s([ccp, L2(rc), zero, d5, ksc, ko, d4], 'dvmptsub', '( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> %s )' % (BL, DB))
    blc = s2([L2(rc), ksc], 'subcld', '%s e. CC' % BL)
    dbc = s2([zero, ko], 'subcld', '%s e. CC' % DB)
    r1 = s([blc], 'ralrimiva', 'A. s e. CC %s e. CC' % BL)
    r2 = s([dbc], 'ralrimiva', 'A. s e. CC %s e. CC' % DB)
    MB = '( s e. CC |-> %s )' % BL
    eB = s([r1, s([d6, r2], 'jca', '( ( CC _D %s ) = ( s e. CC |-> %s ) /\\ A. s e. CC %s e. CC )' % (MB, DB, DB))], 'jca',
           '( A. s e. CC %s e. CC /\\ ( ( CC _D %s ) = ( s e. CC |-> %s ) /\\ A. s e. CC %s e. CC ) )' % (BL, MB, DB, DB))
    entB = s([eB, w.inst('z6ehdv')], 'syl', ENT(MB))
    # power: holexp with binder y
    N = '( O ` k )'
    MY = '( v e. CC |-> ( ( %s ` v ) ^ %s ) )' % (MB, N)
    entY = s([s([entB, nn], 'jca', '( %s /\\ %s e. NN )' % (ENT(MB), N)), w.inst('holexp')], 'syl', ENT(MY))
    A3 = '( %s /\\ v e. CC )' % A1
    yc = w.s([], 'simpr', '( %s -> v e. CC )' % A3)
    fv, val = _cg.mptval(w, A3, 's', 'CC', BL, 'v', yc, gen=w.g)
    pw = w.s([fv], 'oveq1d', '( %s -> ( ( %s ` v ) ^ %s ) = ( %s ^ %s ) )' % (A3, MB, N, val, N))
    m1 = s([pw], 'mpteq2dva', '%s = ( v e. CC |-> ( %s ^ %s ) )' % (MY, val, N))
    BN = '( %s ^ %s )' % (BL, N)
    st, new = subst_eq(w, '( %s ^ %s )' % (val, N), 'v', 's')
    assert new == BN, new
    m2 = s([w.s([st], 'cbvmptv', '( v e. CC |-> ( %s ^ %s ) ) = ( s e. CC |-> %s )' % (val, N, BN))], 'a1i', '( v e. CC |-> ( %s ^ %s ) ) = ( s e. CC |-> %s )' % (val, N, BN))
    MN = '( s e. CC |-> %s )' % BN
    m3 = s([m1, m2], 'eqtrd', '%s = %s' % (MY, MN))
    entN = ent_tr(w, A1, m3, entY, MY, MN)
    # the product
    EJ = BN.replace('( k - C )', '( j - C )').replace('( O ` k )', '( O ` j )')
    st2, new2 = subst_eq(w, BN, 'k', 'j')
    assert new2 == EJ, new2
    goal = '( %s -> %s )' % (A0, ENT('( s e. CC |-> prod_ k e. Z %s )' % BN))
    assert goal == FS['blent'], goal
    w.qed([zf, entN, st2], 'z6ehfp', goal)
    return run8(w)


if __name__ == '__main__':
    gen_blent()
