"""Sortie TP: the roots-of-unity replacement of the Chebyshev equioscillation bound
(tpruq: orthogonality, tprui: the induction over the quadratic factors)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *
import mvlib
import cl as _cl

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


TPI = '( _i x. ( 2 x. _pi ) )'


def UU(L='L'):
    return '( exp ` ( %s / %s ) )' % (TPI, L)


S['tpruq'] = ('( ( L e. NN /\\ T e. NN0 /\\ T < L ) -> sum_ j e. ( 0 ..^ L ) ( ( %s ^ j ) ^ T ) = if ( T = 0 , L , 0 ) )' % UU())


def consts(w, A, c):
    c.have('_i', 'CC', w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A))
    c.have('_pi', 'RR+', w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % A))
    ine = w.s([w.s([], 'ine0', '_i =/= 0')], 'a1i', '( %s -> _i =/= 0 )' % A)
    c.have('_i', 'ne0', ine)
    c.have(TPI, 'ne0', ap(w, A, 'mulne0d', '%s =/= 0' % TPI, c))


def gen_ruq():
    w = W('tpruq', 'Orthogonality of the L-th roots of unity: ` sum_ ( j < L ) ( U ^ j ) ^ T ` is L for ` T = 0 ` and 0 for ` 0 < T < L ` , '
               '` U = exp ( 2 pi i / L ) ` .')
    A = '( L e. NN /\\ T e. NN0 /\\ T < L )'
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    ln = s([], 'simp1', 'L e. NN'); tn = s([], 'simp2', 'T e. NN0'); tl = s([], 'simp3', 'T < L')
    c = Closure(w, A, {'L': ('NN', ln), 'T': ('NN0', tn)})
    consts(w, A, c)
    U = UU(); Q = '( %s / L )' % TPI
    qc = c.mem(Q, 'CC')
    uc = apc(w, A, 'efcl', '%s e. CC' % U, c)
    c.have(U, 'CC', uc)
    une = apc(w, A, 'efne0', '%s =/= 0' % U, c)
    c.have(U, 'ne0', une)
    c.atom(U)
    V = '( %s ^ T )' % U
    # term rewrite
    Aj = '( %s /\\ j e. ( 0 ..^ L ) )' % A
    sj = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aj, f))
    cj = Closure(w, Aj, {'L': ('NN', w.s([ln], 'adantr', '( %s -> L e. NN )' % Aj)),
                         'T': ('NN0', w.s([tn], 'adantr', '( %s -> T e. NN0 )' % Aj)),
                         U: ('CC', w.s([uc], 'adantr', '( %s -> %s e. CC )' % (Aj, U))),
                         'j': ('NN0', w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ L ) )' % Aj), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % Aj))})
    cj.atom(U)
    t1 = ap(w, Aj, 'expmuld', '( %s ^ ( j x. T ) ) = ( ( %s ^ j ) ^ T )' % (U, U), cj)
    t2 = ap(w, Aj, 'expmuld', '( %s ^ ( T x. j ) ) = ( %s ^ j )' % (U, V), cj)
    t3 = sj([ap(w, Aj, 'mulcomd', '( j x. T ) = ( T x. j )', cj)], 'oveq2d', '( %s ^ ( j x. T ) ) = ( %s ^ ( T x. j ) )' % (U, U))
    term = sj([t1, t3, t2], '3eqtr3d', '( ( %s ^ j ) ^ T ) = ( %s ^ j )' % (U, V))
    SUMA = 'sum_ j e. ( 0 ..^ L ) ( ( %s ^ j ) ^ T )' % U
    SUMB = 'sum_ j e. ( 0 ..^ L ) ( %s ^ j )' % V
    se = s([term], 'sumeq2dv', '%s = %s' % (SUMA, SUMB))
    IF = 'if ( T = 0 , L , 0 )'
    # case T = 0
    A0 = '( %s /\\ T = 0 )' % A
    s0 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t0 = w.s([], 'simpr', '( %s -> T = 0 )' % A0)
    c0 = Closure(w, A0, {'L': ('NN', w.s([ln], 'adantr', '( %s -> L e. NN )' % A0)),
                         U: ('CC', w.s([uc], 'adantr', '( %s -> %s e. CC )' % (A0, U)))})
    c0.atom(U)
    v1 = s0([s0([t0], 'oveq2d', '%s = ( %s ^ 0 )' % (V, U)), ap(w, A0, 'exp0d', '( %s ^ 0 ) = 1' % U, c0)], 'eqtrd', '%s = 1' % V)
    A0j = '( %s /\\ j e. ( 0 ..^ L ) )' % A0
    c0j = Closure(w, A0j, {'j': ('NN0', w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ L ) )' % A0j), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % A0j))})
    v1j = w.s([v1], 'adantr', '( %s -> %s = 1 )' % (A0j, V))
    tj = w.s([v1j], 'oveq1d', '( %s -> ( %s ^ j ) = ( 1 ^ j ) )' % (A0j, V))
    tj2 = w.s([c0j.mem('j', 'ZZ'), w.inst('1exp')], 'syl', '( %s -> ( 1 ^ j ) = 1 )' % A0j)
    tj3 = w.s([tj, tj2], 'eqtrd', '( %s -> ( %s ^ j ) = 1 )' % (A0j, V))
    sb = s0([tj3], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ L ) 1' % SUMB)
    fz = w.s([], 'fzofi', '( 0 ..^ L ) e. Fin')
    sc = s0([s0([fz], 'a1i', '( 0 ..^ L ) e. Fin'), s0([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), w.inst('fsumconst')], 'syl2anc',
            'sum_ j e. ( 0 ..^ L ) 1 = ( ( # ` ( 0 ..^ L ) ) x. 1 )')
    hl = s0([c0.mem('L', 'NN0'), w.inst('hashfzo0')], 'syl', '( # ` ( 0 ..^ L ) ) = L')
    sd = s0([hl], 'oveq1d', '( ( # ` ( 0 ..^ L ) ) x. 1 ) = ( L x. 1 )')
    se2 = ap(w, A0, 'mulridd', '( L x. 1 ) = L', c0)
    sum0 = s0([sb, sc, sd], '3eqtrd', '%s = ( L x. 1 )' % SUMB)
    sum0 = s0([sum0, se2], 'eqtrd', '%s = L' % SUMB)
    if0 = s0([t0], 'iftrued', '%s = L' % IF)
    br0 = s0([sum0, if0], 'eqtr4d', '%s = %s' % (SUMB, IF))
    # case T =/= 0
    A1 = '( %s /\\ -. T = 0 )' % A
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    tn0 = w.s([], 'simpr', '( %s -> -. T = 0 )' % A1)
    c1 = Closure(w, A1, {'L': ('NN', w.s([ln], 'adantr', '( %s -> L e. NN )' % A1)),
                         'T': ('NN0', w.s([tn], 'adantr', '( %s -> T e. NN0 )' % A1)),
                         U: ('CC', w.s([uc], 'adantr', '( %s -> %s e. CC )' % (A1, U)))})
    consts(w, A1, c1)
    c1.atom(U)
    tl1 = w.s([tl], 'adantr', '( %s -> T < L )' % A1)
    tnn = s1([s1([c1.mem('T', 'NN0'), s1([tn0], 'neqned', 'T =/= 0')], 'jca', '( T e. NN0 /\\ T =/= 0 )'), w.inst('elnnne0')], 'sylibr', 'T e. NN')
    c1.have('T', 'NN', tnn)
    ev = apc(w, A1, 'efexp', '( exp ` ( T x. %s ) ) = ( %s ^ T )' % (Q, U), c1)
    # V =/= 1
    TQ = '( T x. %s )' % Q
    e1 = apc(w, A1, 'efeq1', '( ( exp ` %s ) = 1 <-> ( %s / %s ) e. ZZ )' % (TQ, TQ, TPI), c1)
    # ( T x. ( TPI / L ) ) / TPI = T / L
    q1 = ap(w, A1, 'div12d', '( T x. ( %s / L ) ) = ( %s x. ( T / L ) )' % (TPI, TPI), c1)
    q2 = s1([q1], 'oveq1d', '( %s / %s ) = ( ( %s x. ( T / L ) ) / %s )' % (TQ, TPI, TPI, TPI))
    q3 = ap(w, A1, 'divcan3d', '( ( %s x. ( T / L ) ) / %s ) = ( T / L )' % (TPI, TPI), c1)
    q4 = s1([q2, q3], 'eqtrd', '( %s / %s ) = ( T / L )' % (TQ, TPI))
    lt1 = c1.gt0('( T / L )')
    ltb = ap(w, A1, 'ltdivmul2d', '( ( T / L ) < 1 <-> T < ( 1 x. L ) )', c1)
    tl2 = lin.linarith(w, A1, [tl1], 'T < ( 1 x. L )', closure=c1)
    ltb = s1([tl2, ltb], 'mpbird', '( T / L ) < 1')
    z0 = s1([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ')
    ltb2 = s1([ltb, s1([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( 0 + 1 ) = 1')], 'breqtrrd', '( T / L ) < ( 0 + 1 )')
    nz = s1([z0, lt1, ltb2, w.inst('btwnnz')], 'syl3anc', '-. ( T / L ) e. ZZ')
    q4r = s1([q4], 'eleq1d', '( ( %s / %s ) e. ZZ <-> ( T / L ) e. ZZ )' % (TQ, TPI))
    nz3 = s1([nz, q4r], 'mtbird', '-. ( %s / %s ) e. ZZ' % (TQ, TPI))
    ne1 = s1([nz3, e1], 'mtbird', '-. ( exp ` %s ) = 1' % TQ)
    ne1 = s1([ne1], 'neqned', '( exp ` %s ) =/= 1' % TQ)
    vne = s1([ev, ne1], 'eqnetrrd', '%s =/= 1' % V)
    c1.have(V, 'CC', c1.mem(V, 'CC'))
    # U ^ L = 1
    LQ = '( L x. %s )' % Q
    el = apc(w, A1, 'efexp', '( exp ` %s ) = ( %s ^ L )' % (LQ, U), c1)
    lq = ap(w, A1, 'divcan2d', '%s = %s' % (LQ, TPI), c1)
    el2 = s1([s1([lq], 'fveq2d', '( exp ` %s ) = ( exp ` %s )' % (LQ, TPI)), s1([w.s([], 'ef2pi', '( exp ` %s ) = 1' % TPI)], 'a1i', '( exp ` %s ) = 1' % TPI)],
             'eqtrd', '( exp ` %s ) = 1' % LQ)
    ul = s1([el, el2], 'eqtr3d', '( %s ^ L ) = 1' % U)
    # V ^ L = 1
    w1 = ap(w, A1, 'expmuld', '( %s ^ ( T x. L ) ) = ( %s ^ L )' % (U, V), c1)
    w2 = ap(w, A1, 'expmuld', '( %s ^ ( L x. T ) ) = ( ( %s ^ L ) ^ T )' % (U, U), c1)
    w3 = s1([ap(w, A1, 'mulcomd', '( T x. L ) = ( L x. T )', c1)], 'oveq2d', '( %s ^ ( T x. L ) ) = ( %s ^ ( L x. T ) )' % (U, U))
    w4 = s1([ul], 'oveq1d', '( ( %s ^ L ) ^ T ) = ( 1 ^ T )' % U)
    w5 = s1([c1.mem('T', 'ZZ'), w.inst('1exp')], 'syl', '( 1 ^ T ) = 1')
    vl = s1([w1, w3, w2], '3eqtr3d', '( %s ^ L ) = ( ( %s ^ L ) ^ T )' % (V, U))
    vl = s1([vl, w4, w5], '3eqtrd', '( %s ^ L ) = 1' % V)
    c1.atom(V)
    lnn0 = c1.mem('L', 'NN0')
    luz = s1([lnn0, w.inst('elnn0uz')], 'sylib', 'L e. ( ZZ>= ` 0 )')
    z00 = s1([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0')
    g1 = ap(w, A1, 'geoserg', '%s = ( ( ( %s ^ 0 ) - ( %s ^ L ) ) / ( 1 - %s ) )' % (SUMB, V, V, V), c1, facts=[vne, z00, luz])
    v0 = ap(w, A1, 'exp0d', '( %s ^ 0 ) = 1' % V, c1)
    nm = s1([v0, vl], 'oveq12d', '( ( %s ^ 0 ) - ( %s ^ L ) ) = ( 1 - 1 )' % (V, V))
    nm2 = s1([nm, s1([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( 1 - 1 ) = 0')], 'eqtrd', '( ( %s ^ 0 ) - ( %s ^ L ) ) = 0' % (V, V))
    g2 = s1([nm2], 'oveq1d', '( ( ( %s ^ 0 ) - ( %s ^ L ) ) / ( 1 - %s ) ) = ( 0 / ( 1 - %s ) )' % (V, V, V, V))
    one_ne = ap(w, A1, 'necomd', '1 =/= %s' % V, c1, facts=[vne])
    c1.have('( 1 - %s )' % V, 'ne0', ap(w, A1, 'subne0d', '( 1 - %s ) =/= 0' % V, c1, facts=[one_ne]))
    g3 = ap(w, A1, 'div0d', '( 0 / ( 1 - %s ) ) = 0' % V, c1)
    sum1 = s1([g1, g2, g3], '3eqtrd', '%s = 0' % SUMB)
    if1 = s1([tn0], 'iffalsed', '%s = 0' % IF)
    br1 = s1([sum1, if1], 'eqtr4d', '%s = %s' % (SUMB, IF))
    br = s([br0, br1], 'pm2.61dan', '%s = %s' % (SUMB, IF))
    w.qed([se, br], 'eqtrd', S['tpruq'])
    return run(w)


WJ = '( %s ^ j )' % UU()


def QT(h, w):
    return '( ( ( %s + 1 ) ^ 2 ) - ( ( E ` %s ) x. %s ) )' % (w, h, w)


def PR(x, w):
    return 'prod_ h e. ( 0 ..^ %s ) %s' % (x, QT('h', w))


def SUMT(x, t):
    return 'sum_ j e. ( 0 ..^ L ) ( ( %s ^ %s ) x. %s )' % (WJ, t, PR(x, WJ))


def IFT(t):
    return 'if ( %s = 0 , L , 0 )' % t


def BODY(x, s):
    return '( ( %s + ( 2 x. %s ) ) < L -> %s = %s )' % (s, x, SUMT(x, s), IFT(s))


def PS(x):
    return '( %s <_ N -> A. s e. NN0 %s )' % (x, BODY(x, 's'))


QA = '( ( A e. CC /\\ B e. CC ) /\\ ( C e. CC /\\ D e. CC ) )'
QL = '( A x. ( B x. ( ( ( C + 1 ) ^ 2 ) - ( D x. C ) ) ) )'
QR = '( ( ( ( A x. ( C ^ 2 ) ) x. B ) + ( ( 2 - D ) x. ( ( A x. C ) x. B ) ) ) + ( A x. B ) )'
S['tpqid'] = '( %s -> %s = %s )' % (QA, QL, QR)


def gen_qid():
    w = W('tpqid', 'Ring identity for one quadratic factor of the roots-of-unity average.')
    c = Closure(w, QA, {'A': ('CC', w.s([], 'simpll', '( %s -> A e. CC )' % QA)), 'B': ('CC', w.s([], 'simplr', '( %s -> B e. CC )' % QA)),
                        'C': ('CC', w.s([], 'simprl', '( %s -> C e. CC )' % QA)), 'D': ('CC', w.s([], 'simprr', '( %s -> D e. CC )' % QA))})
    st = mvlib.ringeqp(w, QA, QL, QR, c)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return run(w)


S['tprui'] = ('( ( ( L e. NN /\\ N e. NN0 /\\ E : ( 0 ..^ N ) --> CC ) /\\ ( 2 x. N ) < L ) -> '
              'sum_ j e. ( 0 ..^ L ) %s = L )' % PR('N', WJ))


def gen_rui():
    w = W('tprui', 'The average of ` Q ( w ) = prod_ ( h < N ) ( ( w + 1 ) ^ 2 - E_h w ) ` over the L-th roots of unity is ` Q ( 0 ) = 1 ` '
               'for ` 2 N < L ` : the sum over the roots is L (induction over the factors, each shifting the moments by 0, 1, 2).')
    A = '( ( L e. NN /\\ N e. NN0 /\\ E : ( 0 ..^ N ) --> CC ) /\\ ( 2 x. N ) < L )'
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    h3 = s([], 'simpl', '( L e. NN /\\ N e. NN0 /\\ E : ( 0 ..^ N ) --> CC )')
    ln = s([h3], 'simp1d', 'L e. NN'); nn = s([h3], 'simp2d', 'N e. NN0'); ef = s([h3], 'simp3d', 'E : ( 0 ..^ N ) --> CC')
    n2l = s([], 'simpr', '( 2 x. N ) < L')
    U = UU()
    # substitution hypotheses of nn0indd
    def sub(val):
        idst = w.s([], 'id', '( x = %s -> x = %s )' % (val, val))
        st, new = w.wcongr(PS('x'), {'x': val}, 'x = %s' % val, {'x': idst})
        assert new == PS(val), (new, PS(val))
        return st
    hx0 = sub('0'); hxy = sub('y'); hxy1 = sub('( y + 1 )'); hxN = sub('N')
    # ---- base
    Ab = '( %s /\\ s e. NN0 )' % A
    Ab2 = '( %s /\\ ( s + ( 2 x. 0 ) ) < L )' % Ab
    sb = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ab2, f))
    cb = Closure(w, Ab2, {'L': ('NN', w.s([ln], 'adantr', '( %s -> L e. NN )' % Ab) and w.s([w.s([ln], 'adantr', '( %s -> L e. NN )' % Ab)], 'adantr', '( %s -> L e. NN )' % Ab2)),
                          's': ('NN0', w.s([w.s([], 'simpr', '( %s -> s e. NN0 )' % Ab)], 'adantr', '( %s -> s e. NN0 )' % Ab2))})
    slt = lin.linarith(w, Ab2, [w.s([], 'simpr', '( %s -> ( s + ( 2 x. 0 ) ) < L )' % Ab2)], 's < L', closure=cb)
    ruq = w.s([cb.mem('L', 'NN'), cb.mem('s', 'NN0'), slt, w.inst('tpruq')], 'syl3anc',
              '( %s -> sum_ j e. ( 0 ..^ L ) ( %s ^ s ) = %s )' % (Ab2, WJ, IFT('s')))
    Abj = '( %s /\\ j e. ( 0 ..^ L ) )' % Ab2
    cbj = Closure(w, Abj, {'j': ('NN0', w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ L ) )' % Abj), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % Abj)),
                           's': ('NN0', w.s([cb.mem('s', 'NN0')], 'adantr', '( %s -> s e. NN0 )' % Abj))})
    consts(w, Abj, cbj)
    cbj.have('L', 'NN', w.s([cb.mem('L', 'NN')], 'adantr', '( %s -> L e. NN )' % Abj))
    uc = apc(w, Abj, 'efcl', '%s e. CC' % U, cbj); cbj.have(U, 'CC', uc); cbj.atom(U)
    p0a = w.s([w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'prodeq1i', '%s = prod_ h e. (/) %s' % (PR('0', WJ), QT('h', WJ)))
    p0 = w.s([p0a, w.s([], 'prod0', 'prod_ h e. (/) %s = 1' % QT('h', WJ))], 'eqtri', '%s = 1' % PR('0', WJ))
    p0 = w.s([p0], 'a1i', '( %s -> %s = 1 )' % (Abj, PR('0', WJ)))
    tb = w.s([p0], 'oveq2d', '( %s -> ( ( %s ^ s ) x. %s ) = ( ( %s ^ s ) x. 1 ) )' % (Abj, WJ, PR('0', WJ), WJ))
    tb2 = ap(w, Abj, 'mulridd', '( ( %s ^ s ) x. 1 ) = ( %s ^ s )' % (WJ, WJ), cbj)
    tb3 = w.s([tb, tb2], 'eqtrd', '( %s -> ( ( %s ^ s ) x. %s ) = ( %s ^ s ) )' % (Abj, WJ, PR('0', WJ), WJ))
    sb1 = sb([tb3], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ L ) ( %s ^ s )' % (SUMT('0', 's'), WJ))
    sb2 = sb([sb1, ruq], 'eqtrd', '%s = %s' % (SUMT('0', 's'), IFT('s')))
    sb3 = w.s([sb2], 'ex', '( %s -> %s )' % (Ab, BODY('0', 's')))
    sb4 = s([sb3], 'ralrimiva', 'A. s e. NN0 %s' % BODY('0', 's'))
    base = s([sb4], 'a1d', PS('0'))
    # ---- step
    G0 = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (A, PS('y'))
    G1 = '( %s /\\ ( y + 1 ) <_ N )' % G0
    G1t = '( %s /\\ t e. NN0 )' % G1
    G2 = '( %s /\\ ( t + ( 2 x. ( y + 1 ) ) ) < L )' % G1t
    g2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (G2, f))
    yn = w.s([w.s([], 'simpr', '( ( %s /\\ y e. NN0 ) -> y e. NN0 )' % A)], 'adantr', '( %s -> y e. NN0 )' % G0)
    c2 = Closure(w, G2, {})
    L2 = lambda st: _cl.lift(w, st, G2)
    c2.have('y', 'NN0', L2(yn))
    c2.have('L', 'NN', L2(ln))
    c2.have('N', 'NN0', L2(nn))
    tn = w.s([w.s([], 'simpr', '( %s -> t e. NN0 )' % G1t)], 'adantr', '( %s -> t e. NN0 )' % G2)
    c2.have('t', 'NN0', tn)
    consts(w, G2, c2)
    y1n = w.s([w.s([], 'simpr', '( %s -> ( y + 1 ) <_ N )' % G1)], 'adantr', '( %s -> ( y + 1 ) <_ N )' % G1t)
    y1n = w.s([y1n], 'adantr', '( %s -> ( y + 1 ) <_ N )' % G2)
    tl = w.s([], 'simpr', '( %s -> ( t + ( 2 x. ( y + 1 ) ) ) < L )' % G2)
    yle = lin.linarith(w, G2, [y1n], 'y <_ N', closure=c2)
    ih0 = L2(w.s([], 'simpr', '( %s -> %s )' % (G0, PS('y'))))
    ih = g2([yle, ih0], 'mpd', 'A. s e. NN0 %s' % BODY('y', 's'))
    def inst(tv, extra_hyps):
        idst = w.s([], 'id', '( s = %s -> s = %s )' % (tv, tv))
        cg, new = w.wcongr(BODY('y', 's'), {'s': tv}, 's = %s' % tv, {'s': idst})
        assert new == BODY('y', tv)
        r = w.s([cg], 'rspcv', '( %s e. NN0 -> ( A. s e. NN0 %s -> %s ) )' % (tv, BODY('y', 's'), new))
        m = g2([c2.mem(tv, 'NN0'), ih, r], 'sylc', new)
        cond = lin.linarith(w, G2, [tl], '( %s + ( 2 x. y ) ) < L' % tv, closure=c2)
        return g2([cond, m], 'mpd', '%s = %s' % (SUMT('y', tv), IFT(tv)))
    i2 = inst('( t + 2 )', []); i1 = inst('( t + 1 )', []); i0 = inst('t', [])
    def zero_if(tv):
        pos = lin.linarith(w, G2, [c2.ge0('t')], '0 < %s' % tv, closure=c2)
        ne = g2([pos], 'gt0ne0d', '%s =/= 0' % tv)
        nq = g2([ne], 'neneqd', '-. %s = 0' % tv)
        return g2([nq], 'iffalsed', '%s = 0' % IFT(tv))
    z2 = g2([i2, zero_if('( t + 2 )')], 'eqtrd', '%s = 0' % SUMT('y', '( t + 2 )'))
    z1 = g2([i1, zero_if('( t + 1 )')], 'eqtrd', '%s = 0' % SUMT('y', '( t + 1 )'))
    # the algebra is done without the induction hypothesis in the antecedent (its bound j h)
    H0 = '( %s /\\ y e. NN0 )' % A
    H1 = '( %s /\\ ( y + 1 ) <_ N )' % H0
    H = '( %s /\\ t e. NN0 )' % H1
    gh = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (H, f))
    ynH = _cl.lift(w, w.s([], 'simpr', '( %s -> y e. NN0 )' % H0), H)
    tnH = w.s([], 'simpr', '( %s -> t e. NN0 )' % H)
    y1nH = _cl.lift(w, w.s([], 'simpr', '( %s -> ( y + 1 ) <_ N )' % H1), H)
    chH = Closure(w, H, {})
    LH = lambda st: _cl.lift(w, st, H)
    for v, k_, st in (('y', 'NN0', ynH), ('L', 'NN', LH(ln)), ('N', 'NN0', LH(nn)), ('t', 'NN0', tnH)):
        chH.have(v, k_, st)
    consts(w, H, chH)
    # pointwise identity
    Gj = '( %s /\\ j e. ( 0 ..^ L ) )' % H
    gj = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Gj, f))
    cj = Closure(w, Gj, {})
    Lj = lambda st: _cl.lift(w, st, Gj)
    for v, k_, st in (('y', 'NN0', ynH), ('L', 'NN', ln), ('N', 'NN0', nn), ('t', 'NN0', tnH)):
        cj.have(v, k_, Lj(st))
    cj.have('j', 'NN0', w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ L ) )' % Gj), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % Gj))
    consts(w, Gj, cj)
    uc = apc(w, Gj, 'efcl', '%s e. CC' % U, cj); cj.have(U, 'CC', uc); cj.atom(U)
    wc = cj.mem(WJ, 'CC'); cj.atom(WJ)
    efj = Lj(ef)
    # y + 1 <_ N gives ( 0 ..^ ( y + 1 ) ) C_ ( 0 ..^ N )
    y1nj = Lj(y1nH)
    nuz = gj([gj([cj.mem('( y + 1 )', 'ZZ'), cj.mem('N', 'ZZ'), y1nj], '3jca', '( ( y + 1 ) e. ZZ /\\ N e. ZZ /\\ ( y + 1 ) <_ N )'), w.inst('eluz2')],
             'sylibr', 'N e. ( ZZ>= ` ( y + 1 ) )')
    sub1 = gj([nuz, w.inst('fzoss2')], 'syl', '( 0 ..^ ( y + 1 ) ) C_ ( 0 ..^ N )')
    yin = gj([cj.mem('y', 'NN0'), w.inst('fzonn0p1')], 'syl', 'y e. ( 0 ..^ ( y + 1 ) )')
    yinN = gj([sub1, yin], 'sseldd', 'y e. ( 0 ..^ N )')
    ey = gj([efj, yinN], 'ffvelcdmd', '( E ` y ) e. CC')
    cj.have('( E ` y )', 'CC', ey); cj.atom('( E ` y )')
    # the factor on ( 0 ..^ y ) is complex
    Gjh = '( %s /\\ h e. ( 0 ..^ y ) )' % Gj
    chh = Closure(w, Gjh, {})
    Lh = lambda st: _cl.lift(w, st, Gjh)
    chh.have(WJ, 'CC', Lh(wc)); chh.atom(WJ)
    ssy = gj([gj([cj.mem('y', 'NN0'), w.inst('fzossfzop1')], 'syl', '( 0 ..^ y ) C_ ( 0 ..^ ( y + 1 ) )'), sub1], 'sstrd', '( 0 ..^ y ) C_ ( 0 ..^ N )')
    hin = w.s([Lh(ssy), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ y ) )' % Gjh)], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % Gjh)
    eh = w.s([Lh(efj), hin], 'ffvelcdmd', '( %s -> ( E ` h ) e. CC )' % Gjh)
    chh.have('( E ` h )', 'CC', eh); chh.atom('( E ` h )')
    qtc = chh.mem(QT('h', WJ), 'CC')
    fin = gj([w.s([], 'fzofi', '( 0 ..^ y ) e. Fin')], 'a1i', '( 0 ..^ y ) e. Fin')
    P = PR('y', WJ)
    pc = gj([fin, qtc], 'fprodcl', '%s e. CC' % P)
    cj.have(P, 'CC', pc); cj.atom(P)
    qy = cj.mem(QT('y', WJ), 'CC')
    spl = gj([gj([cj.mem('y', 'NN0'), w.inst('elnn0uz')], 'sylib', 'y e. ( ZZ>= ` 0 )'), w.inst('fzosplitsn')], 'syl',
             '( 0 ..^ ( y + 1 ) ) = ( ( 0 ..^ y ) u. { y } )')
    pe1 = gj([spl], 'prodeq1d', '%s = prod_ h e. ( ( 0 ..^ y ) u. { y } ) %s' % (PR('( y + 1 )', WJ), QT('h', WJ)))
    hy = w.s([], 'id', '( h = y -> h = y )')
    cgh, newh = w.congr(QT('h', WJ), {'h': 'y'}, 'h = y', {'h': hy})
    assert newh == QT('y', WJ)
    pe2 = gj([w.s([], 'nfv', 'F/ h %s' % Gj), w.s([], 'nfcv', 'F/_ h %s' % QT('y', WJ)), fin, cj.mem('y', 'NN0'),
              gj([w.s([], 'fzonel', '-. y e. ( 0 ..^ y )')], 'a1i', '-. y e. ( 0 ..^ y )'), qtc, cgh, qy],
             'fprodsplitsn', 'prod_ h e. ( ( 0 ..^ y ) u. { y } ) %s = ( %s x. %s )' % (QT('h', WJ), P, QT('y', WJ)))
    pe = gj([pe1, pe2], 'eqtrd', '%s = ( %s x. %s )' % (PR('( y + 1 )', WJ), P, QT('y', WJ)))
    wt = '( %s ^ t )' % WJ
    cj.have(wt, 'CC', cj.mem(wt, 'CC')); cj.atom(wt)
    c_ = '( 2 - ( E ` y ) )'
    Tl = '( %s x. %s )' % (wt, PR('( y + 1 )', WJ))
    t1 = gj([pe], 'oveq2d', '%s = ( %s x. ( %s x. %s ) )' % (Tl, wt, P, QT('y', WJ)))
    R0 = '( ( ( ( %s x. ( %s ^ 2 ) ) x. %s ) + ( %s x. ( ( %s x. %s ) x. %s ) ) ) + ( %s x. %s ) )' % (wt, WJ, P, c_, wt, WJ, P, wt, P)
    import mvlib
    t2 = apc(w, Gj, 'tpqid', '( %s x. ( %s x. %s ) ) = %s' % (wt, P, QT('y', WJ), R0), cj)
    e2 = ap(w, Gj, 'expaddd', '( %s ^ ( t + 2 ) ) = ( %s x. ( %s ^ 2 ) )' % (WJ, wt, WJ), cj)
    e1 = ap(w, Gj, 'expp1d', '( %s ^ ( t + 1 ) ) = ( %s x. %s )' % (WJ, wt, WJ), cj)
    X2 = '( ( %s ^ ( t + 2 ) ) x. %s )' % (WJ, P); X1 = '( ( %s ^ ( t + 1 ) ) x. %s )' % (WJ, P); X0 = '( %s x. %s )' % (wt, P)
    r2 = gj([e2], 'oveq1d', '( ( %s ^ ( t + 2 ) ) x. %s ) = ( ( %s x. ( %s ^ 2 ) ) x. %s )' % (WJ, P, wt, WJ, P))
    r1 = gj([gj([e1], 'oveq1d', '%s = ( ( %s x. %s ) x. %s )' % (X1, wt, WJ, P))], 'oveq2d',
            '( %s x. %s ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (c_, X1, c_, wt, WJ, P))
    R1 = '( ( %s + ( %s x. %s ) ) + %s )' % (X2, c_, X1, X0)
    r3 = gj([gj([r2, r1], 'oveq12d', '( %s + ( %s x. %s ) ) = ( ( ( %s x. ( %s ^ 2 ) ) x. %s ) + ( %s x. ( ( %s x. %s ) x. %s ) ) )'
                % (X2, c_, X1, wt, WJ, P, c_, wt, WJ, P))], 'oveq1d', '%s = %s' % (R1, R0))
    pt = gj([t1, t2, r3], '3eqtr4d', '%s = %s' % (Tl, R1))
    # sums
    ST = gh([pt], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ L ) %s' % (SUMT('( y + 1 )', 't'), R1))
    fz = gh([w.s([], 'fzofi', '( 0 ..^ L ) e. Fin')], 'a1i', '( 0 ..^ L ) e. Fin')
    x2c = cj.mem(X2, 'CC'); x1c = cj.mem(X1, 'CC'); x0c = cj.mem(X0, 'CC'); cx1 = cj.mem('( %s x. %s )' % (c_, X1), 'CC')
    a12 = cj.mem('( %s + ( %s x. %s ) )' % (X2, c_, X1), 'CC')
    s1 = gh([fz, a12, x0c], 'fsumadd', 'sum_ j e. ( 0 ..^ L ) %s = ( sum_ j e. ( 0 ..^ L ) ( %s + ( %s x. %s ) ) + sum_ j e. ( 0 ..^ L ) %s )'
            % (R1, X2, c_, X1, X0))
    s2 = gh([fz, x2c, cx1], 'fsumadd', 'sum_ j e. ( 0 ..^ L ) ( %s + ( %s x. %s ) ) = ( sum_ j e. ( 0 ..^ L ) %s + sum_ j e. ( 0 ..^ L ) ( %s x. %s ) )'
            % (X2, c_, X1, X2, c_, X1))
    # constant factor is complex under G2
    nuz2 = gh([gh([chH.mem('( y + 1 )', 'ZZ'), chH.mem('N', 'ZZ'), y1nH], '3jca', '( ( y + 1 ) e. ZZ /\\ N e. ZZ /\\ ( y + 1 ) <_ N )'), w.inst('eluz2')],
              'sylibr', 'N e. ( ZZ>= ` ( y + 1 ) )')
    yin2 = gh([gh([nuz2, w.inst('fzoss2')], 'syl', '( 0 ..^ ( y + 1 ) ) C_ ( 0 ..^ N )'),
               gh([chH.mem('y', 'NN0'), w.inst('fzonn0p1')], 'syl', 'y e. ( 0 ..^ ( y + 1 ) )')], 'sseldd', 'y e. ( 0 ..^ N )')
    eyHst = gh([LH(ef), yin2], 'ffvelcdmd', '( E ` y ) e. CC')
    chH.have('( E ` y )', 'CC', eyHst)
    chH.atom('( E ` y )')
    s3 = gh([fz, chH.mem(c_, 'CC'), x1c], 'fsummulc2', '( %s x. sum_ j e. ( 0 ..^ L ) %s ) = sum_ j e. ( 0 ..^ L ) ( %s x. %s )' % (c_, X1, c_, X1))
    SX2 = 'sum_ j e. ( 0 ..^ L ) %s' % X2; SX1 = 'sum_ j e. ( 0 ..^ L ) %s' % X1; SX0 = 'sum_ j e. ( 0 ..^ L ) %s' % X0
    assert SX2 == SUMT('y', '( t + 2 )') and SX1 == SUMT('y', '( t + 1 )') and SX0 == SUMT('y', 't')
    s3 = gh([s3], 'oveq2d', '( %s + ( %s x. %s ) ) = ( %s + sum_ j e. ( 0 ..^ L ) ( %s x. %s ) )' % (SX2, c_, SX1, SX2, c_, X1))
    s4 = gh([s2, s3], 'eqtr4d', 'sum_ j e. ( 0 ..^ L ) ( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) )' % (X2, c_, X1, SX2, c_, SX1))
    s5 = gh([s4], 'oveq1d', '( sum_ j e. ( 0 ..^ L ) ( %s + ( %s x. %s ) ) + %s ) = ( ( %s + ( %s x. %s ) ) + %s )' % (X2, c_, X1, SX0, SX2, c_, SX1, SX0))
    h0g = g2([L2(w.s([], 'id', '( %s -> %s )' % (A, A))), L2(yn)], 'jca', H0)
    h1g = g2([h0g, y1n], 'jca', H1)
    hG = g2([h1g, tn], 'jca', H)
    c2.have('( E ` y )', 'CC', w.s([hG, eyHst], 'syl', '( %s -> ( E ` y ) e. CC )' % G2))
    c2.atom('( E ` y )')
    s6 = g2([z2, g2([z1], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (c_, SX1, c_))], 'oveq12d',
            '( %s + ( %s x. %s ) ) = ( 0 + ( %s x. 0 ) )' % (SX2, c_, SX1, c_))
    s7 = g2([s6, i0], 'oveq12d', '( ( %s + ( %s x. %s ) ) + %s ) = ( ( 0 + ( %s x. 0 ) ) + %s )' % (SX2, c_, SX1, SX0, c_, IFT('t')))
    ifc = g2([c2.mem('L', 'CC'), g2([w.s([], '0cn', '0 e. CC')], 'a1i', '0 e. CC')], 'ifcld', '%s e. CC' % IFT('t'))
    c2.have(IFT('t'), 'CC', ifc); c2.atom(IFT('t'))
    m0 = ap(w, G2, 'mul01d', '( %s x. 0 ) = 0' % c_, c2)
    m1 = g2([m0], 'oveq2d', '( 0 + ( %s x. 0 ) ) = ( 0 + 0 )' % c_)
    m2 = g2([m1, g2([w.s([], '00id', '( 0 + 0 ) = 0')], 'a1i', '( 0 + 0 ) = 0')], 'eqtrd', '( 0 + ( %s x. 0 ) ) = 0' % c_)
    m3 = g2([m2], 'oveq1d', '( ( 0 + ( %s x. 0 ) ) + %s ) = ( 0 + %s )' % (c_, IFT('t'), IFT('t')))
    s8 = g2([m3, ap(w, G2, 'addlidd', '( 0 + %s ) = %s' % (IFT('t'), IFT('t')), c2)], 'eqtrd', '( ( 0 + ( %s x. 0 ) ) + %s ) = %s' % (c_, IFT('t'), IFT('t')))
    q1H = gh([ST, s1, s5], '3eqtrd', '%s = ( ( %s + ( %s x. %s ) ) + %s )' % (SUMT('( y + 1 )', 't'), SX2, c_, SX1, SX0))
    q1 = w.s([hG, q1H], 'syl', '( %s -> %s = ( ( %s + ( %s x. %s ) ) + %s ) )' % (G2, SUMT('( y + 1 )', 't'), SX2, c_, SX1, SX0))
    q2 = g2([q1, s7, s8], '3eqtrd', '%s = %s' % (SUMT('( y + 1 )', 't'), IFT('t')))
    q3 = w.s([q2], 'ex', '( %s -> %s )' % (G1t, BODY('( y + 1 )', 't')))
    q4 = w.s([q3], 'ralrimiva', '( %s -> A. t e. NN0 %s )' % (G1, BODY('( y + 1 )', 't')))
    idts = w.s([], 'id', '( t = s -> t = s )')
    cgt, newt = w.wcongr(BODY('( y + 1 )', 't'), {'t': 's'}, 't = s', {'t': idts})
    assert newt == BODY('( y + 1 )', 's')
    cbv = w.s([cgt], 'cbvralvw', '( A. t e. NN0 %s <-> A. s e. NN0 %s )' % (BODY('( y + 1 )', 't'), newt))
    q5 = w.s([q4, cbv], 'sylib', '( %s -> A. s e. NN0 %s )' % (G1, newt))
    step = w.s([q5], 'ex', '( %s -> %s )' % (G0, PS('( y + 1 )')))
    ind = w.s([hx0, hxy, hxy1, hxN, base, step], 'nn0indd', '( ( %s /\\ N e. NN0 ) -> %s )' % (A, PS('N')))
    psn = s([nn, ind], 'mpdan', PS('N'))
    c = Closure(w, A, {'N': ('NN0', nn), 'L': ('NN', ln)})
    consts(w, A, c)
    alln = s([c.mem('N', 'RR') and ap(w, A, 'leidd', 'N <_ N', c), psn], 'mpd', 'A. s e. NN0 %s' % BODY('N', 's'))
    ids0 = w.s([], 'id', '( s = 0 -> s = 0 )')
    cg0, new0 = w.wcongr(BODY('N', 's'), {'s': '0'}, 's = 0', {'s': ids0})
    r0 = w.s([cg0], 'rspcv', '( 0 e. NN0 -> ( A. s e. NN0 %s -> %s ) )' % (BODY('N', 's'), new0))
    b0 = s([s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), alln, r0], 'sylc', new0)
    cond0 = lin.linarith(w, A, [n2l], '( 0 + ( 2 x. N ) ) < L', closure=c)
    e0 = s([cond0, b0], 'mpd', '%s = %s' % (SUMT('N', '0'), IFT('0')))
    if0 = s([s([w.s([], 'eqid', '0 = 0')], 'a1i', '0 = 0')], 'iftrued', '%s = L' % IFT('0'))
    Aj = '( %s /\\ j e. ( 0 ..^ L ) )' % A
    ca = Closure(w, Aj, {'j': ('NN0', w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ L ) )' % Aj), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % Aj)),
                         'L': ('NN', w.s([ln], 'adantr', '( %s -> L e. NN )' % Aj))})
    consts(w, Aj, ca)
    uca = apc(w, Aj, 'efcl', '%s e. CC' % U, ca); ca.have(U, 'CC', uca); ca.atom(U)
    wca = ca.mem(WJ, 'CC'); ca.atom(WJ)
    Pn = PR('N', WJ)
    Ajh = '( %s /\\ h e. ( 0 ..^ N ) )' % Aj
    cah = Closure(w, Ajh, {})
    cah.have(WJ, 'CC', _cl.lift(w, wca, Ajh)); cah.atom(WJ)
    cah.have('( E ` h )', 'CC', w.s([_cl.lift(w, ef, Ajh), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % Ajh)], 'ffvelcdmd', '( %s -> ( E ` h ) e. CC )' % Ajh))
    cah.atom('( E ` h )')
    pnc = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % Aj), cah.mem(QT('h', WJ), 'CC')], 'fprodcl',
              '( %s -> %s e. CC )' % (Aj, Pn))
    ca.have(Pn, 'CC', pnc); ca.atom(Pn)
    x0 = ap(w, Aj, 'exp0d', '( %s ^ 0 ) = 1' % WJ, ca)
    x1 = w.s([x0], 'oveq1d', '( %s -> ( ( %s ^ 0 ) x. %s ) = ( 1 x. %s ) )' % (Aj, WJ, Pn, Pn))
    x2 = ap(w, Aj, 'mullidd', '( 1 x. %s ) = %s' % (Pn, Pn), ca)
    x3 = w.s([x1, x2], 'eqtrd', '( %s -> ( ( %s ^ 0 ) x. %s ) = %s )' % (Aj, WJ, Pn, Pn))
    sm = s([x3], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ L ) %s' % (SUMT('N', '0'), Pn))
    w.qed([sm, e0, if0], '3eqtr3d', S['tprui'])
    return run(w)


if __name__ == '__main__':
    gen_ruq()
    gen_qid()
    gen_rui()
