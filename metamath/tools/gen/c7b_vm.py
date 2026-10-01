"""C7b section 2: the real von Mangoldt series (vmtmb, vmsercvg, vmbndlem, vmbnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl, num
import congr as _cg
lin.FASTPATH = True


def val(w, ante, body, k, mem, exs, x='n'):
    return _cg.mptval(w, ante, x, 'NN', body, k, mem, exs=exs, gen=w.g)


if __name__ == '__main__' and (not only or 'vmtmb' in only):
    w = W('vmtmb', 'The von Mangoldt term against a slightly larger exponent: '
          '` Lam K K ^c -u ( 1 + E ) <_ ( 2 / E ) K ^c -u ( 1 + E / 2 ) ` .')
    A0 = '( K e. NN /\\ E e. RR+ )'
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
    krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
    kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0)
    k0 = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)
    er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
    ec = w.s([erp], 'rpcnd', '( %s -> E e. CC )' % A0)
    e0 = w.s([erp], 'rpne0d', '( %s -> E =/= 0 )' % A0)
    E2 = '( E / 2 )'
    e2rp = w.s([erp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, E2))
    U = '( K ^c %s )' % E2
    V = '( K ^c -u ( 1 + E ) )'
    Wt = '( K ^c -u ( 1 + %s ) )' % E2
    lam = '( Lam ` K )'
    l1 = w.s([kn, w.inst('vmalelog')], 'syl', '( %s -> %s <_ ( log ` K ) )' % (A0, lam))
    l2 = w.s([kn, e2rp, w.inst('logcxpbnd')], 'syl2anc', '( %s -> ( log ` K ) <_ ( %s / %s ) )' % (A0, U, E2))
    ur = w.s([w.s([krp, w.s([e2rp], 'rpred', '( %s -> %s e. RR )' % (A0, E2))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, U))], 'rpred', '( %s -> %s e. RR )' % (A0, U))
    uc = w.s([ur], 'recnd', '( %s -> %s e. CC )' % (A0, U))
    two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
    two0 = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % A0)
    d1 = w.s([uc, ec, two, e0, two0], 'divdiv2d', '( %s -> ( %s / %s ) = ( ( %s x. 2 ) / E ) )' % (A0, U, E2, U))
    d2 = w.s([uc, two, ec, e0], 'divassd', '( %s -> ( ( %s x. 2 ) / E ) = ( %s x. ( 2 / E ) ) )' % (A0, U, U))
    q = '( 2 / E )'
    qc = w.s([two, ec, e0], 'divcld', '( %s -> %s e. CC )' % (A0, q))
    d3 = w.s([uc, qc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, U, q, q, U))
    d = w.s([w.s([d1, d2], 'eqtrd', '( %s -> ( %s / %s ) = ( %s x. %s ) )' % (A0, U, E2, U, q)), d3], 'eqtrd', '( %s -> ( %s / %s ) = ( %s x. %s ) )' % (A0, U, E2, q, U))
    lr = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> %s e. RR )' % (A0, lam))
    lgr = w.s([krp], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)
    br = w.s([ur, e2rp], 'rerpdivcld', '( %s -> ( %s / %s ) e. RR )' % (A0, U, E2))
    l12 = w.s([lr, lgr, br, l1, l2], 'letrd', '( %s -> %s <_ ( %s / %s ) )' % (A0, lam, U, E2))
    l3 = w.s([l12, d], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, lam, q, U))
    ope = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), er], 'readdcld', '( %s -> ( 1 + E ) e. RR )' % A0)
    vrp = w.s([krp, w.s([ope], 'renegcld', '( %s -> -u ( 1 + E ) e. RR )' % A0)], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, V))
    qr = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), erp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, q))
    l4 = w.s([lr, w.s([w.s([qr], 'rpred', '( %s -> %s e. RR )' % (A0, q)), ur], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, q, U)),
              w.s([vrp], 'rpred', '( %s -> %s e. RR )' % (A0, V)), w.s([vrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, V)), l3], 'lemul1ad',
             '( %s -> ( %s x. %s ) <_ ( ( %s x. %s ) x. %s ) )' % (A0, lam, V, q, U, V))
    vc = w.s([vrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, V))
    ma = w.s([qc, uc, vc], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (A0, q, U, V, q, U, V))
    e2c = w.s([e2rp], 'rpcnd', '( %s -> %s e. CC )' % (A0, E2))
    ca = w.s([kc, k0, e2c, w.s([w.s([ope], 'recnd', '( %s -> ( 1 + E ) e. CC )' % A0)], 'negcld', '( %s -> -u ( 1 + E ) e. CC )' % A0)], 'cxpaddd',
             '( %s -> ( K ^c ( %s + -u ( 1 + E ) ) ) = ( %s x. %s ) )' % (A0, E2, U, V))
    ex = lin.lineq(w, A0, '( %s + -u ( 1 + E ) )' % E2, '-u ( 1 + %s )' % E2, leaves={'E': er})
    uv = w.s([w.s([ca], 'eqcomd', '( %s -> ( %s x. %s ) = ( K ^c ( %s + -u ( 1 + E ) ) ) )' % (A0, U, V, E2)),
              w.s([ex], 'oveq2d', '( %s -> ( K ^c ( %s + -u ( 1 + E ) ) ) = %s )' % (A0, E2, Wt))], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (A0, U, V, Wt))
    fin = w.s([ma, w.s([uv], 'oveq2d', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (A0, q, U, V, q, Wt))], 'eqtrd',
              '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. %s ) )' % (A0, q, U, V, q, Wt))
    w.qed([l4, fin], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A0, lam, V, q, Wt))
    run7b(w)


def ex_(w, ante, E, cc):
    return w.s([cc], 'elexd', '( %s -> %s e. _V )' % (ante, E))


if __name__ == '__main__' and (not only or 'vmsercvg' in only):
    w = W('vmsercvg', 'The von Mangoldt Dirichlet series converges for real exponent ` T > 1 ` (Lean ` summable_vonMangoldt_rpow ` ).')
    ph = '( T e. RR /\\ 1 < T )'
    tr = w.s([], 'simpl', '( %s -> T e. RR )' % ph)
    t1 = w.s([], 'simpr', '( %s -> 1 < T )' % ph)
    E = '( T - 1 )'
    er = w.s([tr, w.s([], '1red', '( %s -> 1 e. RR )' % ph)], 'resubcld', '( %s -> %s e. RR )' % (ph, E))
    egt = lin.linarith(w, ph, [t1], '0 < %s' % E, leaves={'T': tr})
    erp = w.s([er, egt], 'elrpd', '( %s -> %s e. RR+ )' % (ph, E))
    q = '( 2 / %s )'% E
    qrp = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % ph), erp], 'rpdivcld', '( %s -> %s e. RR+ )' % (ph, q))
    T2 = '( 1 + ( %s / 2 ) )' % E
    t2r = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % ph), w.s([er], 'rehalfcld', '( %s -> ( %s / 2 ) e. RR )' % (ph, E))], 'readdcld', '( %s -> %s e. RR )' % (ph, T2))
    t2g = lin.linarith(w, ph, [t1], '1 < %s' % T2, leaves={'T': tr})
    FB = '( %s x. ( n ^c -u %s ) )' % (q, T2)
    F = '( n e. NN |-> %s )' % FB
    fcv = w.s([w.s([w.s([t2r, t2g], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (ph, T2, T2)), w.s([qrp], 'rpcnd', '( %s -> %s e. CC )' % (ph, q))], 'jca',
                   '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ %s e. CC ) )' % (ph, T2, T2, q)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, F))
    GB = RVT('n')
    G = '( n e. NN |-> %s )' % GB
    Ak = '( %s /\\ k e. NN )' % ph
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    FK = '( %s x. ( k ^c -u %s ) )' % (q, T2)
    fkr = w.s([w.s([w.s([qrp], 'adantr', '( %s -> %s e. RR+ )' % (Ak, q))], 'rpred', '( %s -> %s e. RR )' % (Ak, q)),
               w.s([w.s([krp, w.s([w.s([t2r], 'adantr', '( %s -> %s e. RR )' % (Ak, T2))], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, T2))], 'rpcxpcld',
                        '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, T2))], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, T2))], 'remulcld', '( %s -> %s e. RR )' % (Ak, FK))
    vf, _ = val(w, Ak, FB, 'k', kn, ex_(w, Ak, FK, w.s([fkr], 'recnd', '( %s -> %s e. CC )' % (Ak, FK))))
    GK = RVT('k')
    pkr = w.s([krp, w.s([w.s([tr], 'adantr', '( %s -> T e. RR )' % Ak)], 'renegcld', '( %s -> -u T e. RR )' % Ak)], 'rpcxpcld', '( %s -> ( k ^c -u T ) e. RR+ )' % Ak)
    lk = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % Ak)
    gkr = w.s([lk, w.s([pkr], 'rpred', '( %s -> ( k ^c -u T ) e. RR )' % Ak)], 'remulcld', '( %s -> %s e. RR )' % (Ak, GK))
    vg, _ = val(w, Ak, GB, 'k', kn, ex_(w, Ak, GK, w.s([gkr], 'recnd', '( %s -> %s e. CC )' % (Ak, GK))))
    f3 = w.s([vf, fkr], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, F))
    g4 = w.s([vg, gkr], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, G))
    Bk = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % ph
    kn2 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Bk), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrrdi', '( %s -> k e. NN )' % Bk)
    # transport Ak facts to Bk
    def tb(st, f):
        return w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Bk, ph)), kn2], 'jca', '( %s -> %s )' % (Bk, Ak)), st], 'syl', '( %s -> %s )' % (Bk, f))
    g0 = w.s([lk, w.s([pkr], 'rpred', '( %s -> ( k ^c -u T ) e. RR )' % Ak), w.s([kn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` k ) )' % Ak),
             w.s([pkr], 'rpge0d', '( %s -> 0 <_ ( k ^c -u T ) )' % Ak)], 'mulge0d', '( %s -> 0 <_ %s )' % (Ak, GK))
    g0v = w.s([g0, vg], 'breqtrrd', '( %s -> 0 <_ ( %s ` k ) )' % (Ak, G))
    vt = w.s([w.s([kn, w.s([erp], 'adantr', '( %s -> %s e. RR+ )' % (Ak, E))], 'jca', '( %s -> ( k e. NN /\\ %s e. RR+ ) )' % (Ak, E)), w.inst('vmtmb')], 'syl',
             '( %s -> ( ( Lam ` k ) x. ( k ^c -u ( 1 + %s ) ) ) <_ %s )' % (Ak, E, FK))
    pc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % Ak), w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % ph)], 'adantr', '( %s -> T e. CC )' % Ak), w.inst('pncan3')],
             'syl2anc', '( %s -> ( 1 + %s ) = T )' % (Ak, E))
    rw = w.s([w.s([w.s([pc], 'negeqd', '( %s -> -u ( 1 + %s ) = -u T )' % (Ak, E))], 'oveq2d', '( %s -> ( k ^c -u ( 1 + %s ) ) = ( k ^c -u T ) )' % (Ak, E))],
             'oveq2d', '( %s -> ( ( Lam ` k ) x. ( k ^c -u ( 1 + %s ) ) ) = %s )' % (Ak, E, GK))
    le = w.s([w.s([rw, vt], 'eqbrtrrd', '( %s -> %s <_ %s )' % (Ak, GK, FK)), vf], 'breqtrrd', '( %s -> %s <_ ( %s ` k ) )' % (Ak, GK, F))
    le2 = w.s([vg, le], 'eqbrtrd', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Ak, G, F))
    w.qed([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % ph), f3, g4, fcv,
           tb(g0v, '0 <_ ( %s ` k )' % G), tb(le2, '( %s ` k ) <_ ( %s ` k )' % (G, F))], 'cvgcmp', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, G))
    run7b(w)


if __name__ == '__main__' and (not only or 'vmbndlem' in only):
    w = W('vmbndlem', 'The arithmetic of Lean ` tsum_vonMangoldt_rpow_le ` : ` ( 2 / E ) ( 1 + 2 / E ) <_ 6 / E ^ 2 ` for ` 0 < E <_ 1 ` .')
    A0 = '( E e. RR+ /\\ E <_ 1 )'
    erp = w.s([], 'simpl', '( %s -> E e. RR+ )' % A0)
    e1 = w.s([], 'simpr', '( %s -> E <_ 1 )' % A0)
    ec = w.s([erp], 'rpcnd', '( %s -> E e. CC )' % A0)
    e0 = w.s([erp], 'rpne0d', '( %s -> E =/= 0 )' % A0)
    u = '( 1 / E )'
    urp = w.s([erp], 'rpreccld', '( %s -> %s e. RR+ )' % (A0, u))
    ur = w.s([urp], 'rpred', '( %s -> %s e. RR )' % (A0, u))
    one_rp = w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % A0)
    u1a = w.s([erp, one_rp, w.s([], '1red', '( %s -> 1 e. RR )' % A0), w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A0), e1], 'lediv2ad',
              '( %s -> ( 1 / 1 ) <_ %s )' % (A0, u))
    u1 = w.s([w.s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( %s -> ( 1 / 1 ) = 1 )' % A0), u1a], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (A0, u))
    two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
    two0 = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % A0)
    q1 = w.s([two, ec, e0], 'divrecd', '( %s -> ( 2 / E ) = ( 2 x. %s ) )' % (A0, u))
    q2 = w.s([w.s([ec, two, e0, two0], 'recdivd', '( %s -> ( 1 / ( E / 2 ) ) = ( 2 / E ) )' % A0), q1], 'eqtrd', '( %s -> ( 1 / ( E / 2 ) ) = ( 2 x. %s ) )' % (A0, u))
    e2 = w.s([ec], 'sqcld', '( %s -> ( E ^ 2 ) e. CC )' % A0)
    z2 = w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A0)
    e2n = w.s([ec, e0, z2], 'expne0d', '( %s -> ( E ^ 2 ) =/= 0 )' % A0)
    six = w.s([], '6cn', '6 e. CC')
    six = w.s([six], 'a1i', '( %s -> 6 e. CC )' % A0)
    q3 = w.s([six, e2, e2n], 'divrecd', '( %s -> ( 6 / ( E ^ 2 ) ) = ( 6 x. ( 1 / ( E ^ 2 ) ) ) )' % A0)
    q4 = w.s([ec, e0, z2], 'exprecd', '( %s -> ( %s ^ 2 ) = ( 1 / ( E ^ 2 ) ) )' % (A0, u))
    q34 = w.s([q3, w.s([q4], 'oveq2d', '( %s -> ( 6 x. ( %s ^ 2 ) ) = ( 6 x. ( 1 / ( E ^ 2 ) ) ) )' % (A0, u))], 'eqtr4d',
              '( %s -> ( 6 / ( E ^ 2 ) ) = ( 6 x. ( %s ^ 2 ) ) )' % (A0, u))
    L = '( ( 2 x. %s ) x. ( 1 + ( 2 x. %s ) ) )' % (u, u)
    lhs = w.s([q1, w.s([q2], 'oveq2d', '( %s -> ( 1 + ( 1 / ( E / 2 ) ) ) = ( 1 + ( 2 x. %s ) ) )' % (A0, u))], 'oveq12d',
              '( %s -> ( ( 2 / E ) x. ( 1 + ( 1 / ( E / 2 ) ) ) ) = %s )' % (A0, L))
    g = lin.nlinarith(w, A0, [u1], '%s <_ ( 6 x. ( %s ^ 2 ) )' % (L, u), leaves={u: ur})
    w.qed([w.s([lhs, g], 'eqbrtrd', '( %s -> ( ( 2 / E ) x. ( 1 + ( 1 / ( E / 2 ) ) ) ) <_ ( 6 x. ( %s ^ 2 ) ) )' % (A0, u)), q34], 'breqtrrd',
          '( %s -> ( ( 2 / E ) x. ( 1 + ( 1 / ( E / 2 ) ) ) ) <_ ( 6 / ( E ^ 2 ) ) )' % A0)
    run7b(w)


if __name__ == '__main__' and (not only or 'vmbnd' in only):
    w = W('vmbnd', 'Lean ` tsum_vonMangoldt_rpow_le ` : ` sum_ k Lam k k ^c -u T <_ 6 / ( T - 1 ) ^ 2 ` for ` 1 < T <_ 2 ` .')
    ph = '( T e. RR /\\ 1 < T /\\ T <_ 2 )'
    tr = w.s([], 'simp1', '( %s -> T e. RR )' % ph)
    t1 = w.s([], 'simp2', '( %s -> 1 < T )' % ph)
    t2 = w.s([], 'simp3', '( %s -> T <_ 2 )' % ph)
    E = '( T - 1 )'
    er = w.s([tr, w.s([], '1red', '( %s -> 1 e. RR )' % ph)], 'resubcld', '( %s -> %s e. RR )' % (ph, E))
    egt = lin.linarith(w, ph, [t1], '0 < %s' % E, leaves={'T': tr})
    erp = w.s([er, egt], 'elrpd', '( %s -> %s e. RR+ )' % (ph, E))
    ele = lin.linarith(w, ph, [t2], '%s <_ 1' % E, leaves={'T': tr})
    q = '( 2 / %s )' % E
    qrp = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % ph), erp], 'rpdivcld', '( %s -> %s e. RR+ )' % (ph, q))
    qc = w.s([qrp], 'rpcnd', '( %s -> %s e. CC )' % (ph, q))
    E2 = '( %s / 2 )' % E
    T2 = '( 1 + %s )' % E2
    e2r = w.s([er], 'rehalfcld', '( %s -> %s e. RR )' % (ph, E2))
    t2r = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % ph), e2r], 'readdcld', '( %s -> %s e. RR )' % (ph, T2))
    t2g = lin.linarith(w, ph, [t1], '1 < %s' % T2, leaves={'T': tr})
    t2h = w.s([t2r, t2g], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (ph, T2, T2))
    FB = RVT('n'); GB = '( %s x. ( n ^c -u %s ) )' % (q, T2); HB = '( n ^c -u %s )' % T2
    F = '( n e. NN |-> %s )' % FB; G = '( n e. NN |-> %s )' % GB; H = '( n e. NN |-> %s )' % HB
    fcv = w.s([w.s([tr, t1], 'jca', '( %s -> ( T e. RR /\\ 1 < T ) )' % ph), w.inst('vmsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, F))
    gcv = w.s([w.s([t2h, qc], 'jca', '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ %s e. CC ) )' % (ph, T2, T2, q)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, G))
    hcv = w.s([t2h, w.inst('zsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, H))
    Ak = '( %s /\\ k e. NN )' % ph
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    hk = w.s([krp, w.s([w.s([t2r], 'adantr', '( %s -> %s e. RR )' % (Ak, T2))], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, T2))], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, T2))
    hkr = w.s([hk], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, T2))
    GK = '( %s x. ( k ^c -u %s ) )' % (q, T2)
    gkr = w.s([w.s([w.s([qrp], 'adantr', '( %s -> %s e. RR+ )' % (Ak, q))], 'rpred', '( %s -> %s e. RR )' % (Ak, q)), hkr], 'remulcld', '( %s -> %s e. RR )' % (Ak, GK))
    FK = RVT('k')
    pkr = w.s([krp, w.s([w.s([tr], 'adantr', '( %s -> T e. RR )' % Ak)], 'renegcld', '( %s -> -u T e. RR )' % Ak)], 'rpcxpcld', '( %s -> ( k ^c -u T ) e. RR+ )' % Ak)
    lk = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % Ak)
    fkr = w.s([lk, w.s([pkr], 'rpred', '( %s -> ( k ^c -u T ) e. RR )' % Ak)], 'remulcld', '( %s -> %s e. RR )' % (Ak, FK))
    vf, _ = val(w, Ak, FB, 'k', kn, ex_(w, Ak, FK, w.s([fkr], 'recnd', '( %s -> %s e. CC )' % (Ak, FK))))
    vg, _ = val(w, Ak, GB, 'k', kn, ex_(w, Ak, GK, w.s([gkr], 'recnd', '( %s -> %s e. CC )' % (Ak, GK))))
    vh, _ = val(w, Ak, HB, 'k', kn, ex_(w, Ak, '( k ^c -u %s )' % T2, w.s([hkr], 'recnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Ak, T2))))
    vt = w.s([w.s([kn, w.s([erp], 'adantr', '( %s -> %s e. RR+ )' % (Ak, E))], 'jca', '( %s -> ( k e. NN /\\ %s e. RR+ ) )' % (Ak, E)), w.inst('vmtmb')], 'syl',
             '( %s -> ( ( Lam ` k ) x. ( k ^c -u ( 1 + %s ) ) ) <_ %s )' % (Ak, E, GK))
    pc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % Ak), w.s([w.s([tr], 'recnd', '( %s -> T e. CC )' % ph)], 'adantr', '( %s -> T e. CC )' % Ak), w.inst('pncan3')],
             'syl2anc', '( %s -> ( 1 + %s ) = T )' % (Ak, E))
    rw = w.s([w.s([w.s([pc], 'negeqd', '( %s -> -u ( 1 + %s ) = -u T )' % (Ak, E))], 'oveq2d', '( %s -> ( k ^c -u ( 1 + %s ) ) = ( k ^c -u T ) )' % (Ak, E))],
             'oveq2d', '( %s -> ( ( Lam ` k ) x. ( k ^c -u ( 1 + %s ) ) ) = %s )' % (Ak, E, FK))
    le = w.s([rw, vt], 'eqbrtrrd', '( %s -> %s <_ %s )' % (Ak, FK, GK))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph)
    SF = 'sum_ k e. NN %s' % FK
    SG = 'sum_ k e. NN %s' % GK
    SH = 'sum_ k e. NN ( k ^c -u %s )' % T2
    s1 = w.s([nnuz, one, vf, fkr, vg, gkr, le, fcv, gcv], 'isumle', '( %s -> %s <_ %s )' % (ph, SF, SG))
    s2 = w.s([nnuz, one, vh, w.s([hkr], 'recnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Ak, T2)), hcv, qc], 'isummulc2', '( %s -> ( %s x. %s ) = %s )' % (ph, q, SH, SG))
    zb = w.s([t2h, w.inst('zserbnd')], 'syl', '( %s -> %s <_ ( 1 + ( 1 / ( %s - 1 ) ) ) )' % (ph, SH, T2))
    pn = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ph), w.s([e2r], 'recnd', '( %s -> %s e. CC )' % (ph, E2))], 'pncan2d', '( %s -> ( %s - 1 ) = %s )' % (ph, T2, E2))
    zb2 = w.s([zb, w.s([w.s([pn], 'oveq2d', '( %s -> ( 1 / ( %s - 1 ) ) = ( 1 / %s ) )' % (ph, T2, E2))], 'oveq2d',
                       '( %s -> ( 1 + ( 1 / ( %s - 1 ) ) ) = ( 1 + ( 1 / %s ) ) )' % (ph, T2, E2))], 'breqtrd', '( %s -> %s <_ ( 1 + ( 1 / %s ) ) )' % (ph, SH, E2))
    B = '( 1 + ( 1 / %s ) )' % E2
    e2rp = w.s([erp], 'rphalfcld', '( %s -> %s e. RR+ )' % (ph, E2))
    br = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % ph), w.s([w.s([e2rp], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (ph, E2))], 'rpred', '( %s -> ( 1 / %s ) e. RR )' % (ph, E2))],
             'readdcld', '( %s -> %s e. RR )' % (ph, B))
    shrr = w.s([nnuz, one, vh, hkr, hcv], 'isumrecl', '( %s -> %s e. RR )' % (ph, SH))
    qr = w.s([qrp], 'rpred', '( %s -> %s e. RR )' % (ph, q))
    s3 = w.s([shrr, br, qr, w.s([qrp], 'rpge0d', '( %s -> 0 <_ %s )' % (ph, q)), zb2], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, q, SH, q, B))
    s4 = w.s([w.s([erp, ele], 'jca', '( %s -> ( %s e. RR+ /\\ %s <_ 1 ) )' % (ph, E, E)), w.inst('vmbndlem')], 'syl',
             '( %s -> ( %s x. %s ) <_ ( 6 / ( %s ^ 2 ) ) )' % (ph, q, B, E))
    R = '( 6 / ( %s ^ 2 ) )' % E
    e2p = w.s([erp, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % ph)], 'rpexpcld', '( %s -> ( %s ^ 2 ) e. RR+ )' % (ph, E))
    rr = w.s([w.s([w.s([], '6re', '6 e. RR')], 'a1i', '( %s -> 6 e. RR )' % ph), e2p], 'rerpdivcld', '( %s -> %s e. RR )' % (ph, R))
    sfr = w.s([nnuz, one, vf, fkr, fcv], 'isumrecl', '( %s -> %s e. RR )' % (ph, SF))
    sgr = w.s([nnuz, one, vg, gkr, gcv], 'isumrecl', '( %s -> %s e. RR )' % (ph, SG))
    qbr = w.s([qr, br], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (ph, q, B))
    l1 = w.s([s2, s3], 'eqbrtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (ph, SG, q, B))
    l2 = w.s([sgr, qbr, rr, l1, s4], 'letrd', '( %s -> %s <_ %s )' % (ph, SG, R))
    w.qed([sfr, sgr, rr, s1, l2], 'letrd', '( %s -> %s <_ %s )' % (ph, SF, R))
    run7b(w)
