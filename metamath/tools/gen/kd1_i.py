"""Sortie KD1: iterated derivatives of a simple pole (kdpoledn)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from mvlib import ringeq, ringeqp

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


U = '( CC \\ { Q } )'
def MAPp(x):
    return '( z e. %s |-> ( ( ( -u 1 ^ %s ) x. ( ! ` %s ) ) / ( ( z - Q ) ^ ( %s + 1 ) ) ) )' % (U, x, x, x)


def gen_poledn():
    w = W('kdpoledn', 'Lean ` KDerivDetect.iteratedDeriv_sub_inv ` : the ` K ` -th derivative of ` 1 / ( z - Q ) ` is ` ( -u 1 ) ^ K K ! / ( z - Q ) ^ ( K + 1 ) ` .')
    PL = '( z e. %s |-> ( 1 / ( z - Q ) ) )' % U
    ph = 'Q e. CC'
    PSx = lambda x: '( ( CC Dn %s ) ` %s ) = %s' % (PL, x, MAPp(x))
    subs = {}
    for nm, t in (('0', '0'), ('n', 'n'), ('n1', '( n + 1 )'), ('K', 'K')):
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (t, t))
        st, new = w.wcongr(PSx('x'), {'x': t}, 'x = %s' % t, {'x': idx})
        assert new == PSx(t), new
        subs[nm] = st
    # pointwise facts under ( ph /\ z e. U ), optionally with n
    def zfacts(ante):
        s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        zu = s([], 'simpr', 'z e. %s' % U)
        zc = s([zu, w.inst('eldifi')], 'syl', 'z e. CC')
        zn = s([zu, w.inst('eldifsni')], 'syl', 'z =/= Q')
        return zu, zc, zn
    Az = '( %s /\\ z e. %s )' % (ph, U)
    zu, zc, zn = zfacts(Az)
    qz = w.s([], 'simpl', '( %s -> Q e. CC )' % Az)
    wc = w.s([zc, qz], 'subcld', '( %s -> ( z - Q ) e. CC )' % Az)
    wn = w.s([zc, qz, zn], 'subne0d', '( %s -> ( z - Q ) =/= 0 )' % Az)
    plc = w.s([wc, wn], 'reccld', '( %s -> ( 1 / ( z - Q ) ) e. CC )' % Az)
    plf = w.s([plc], 'fmptd', '( %s -> %s : %s --> CC )' % (ph, PL, U))
    ucc = w.s([w.s([], 'difss', '%s C_ CC' % U)], 'a1i', '( %s -> %s C_ CC )' % (ph, U))
    cx = w.s([], 'cnex', 'CC e. _V')
    pm = w.s([w.s([w.s([cx, cx], 'pm3.2i', '( CC e. _V /\\ CC e. _V )')], 'a1i', '( %s -> ( CC e. _V /\\ CC e. _V ) )' % ph),
              w.s([plf, ucc], 'jca', '( %s -> ( %s : %s --> CC /\\ %s C_ CC ) )' % (ph, PL, U, U)), w.inst('elpm2r')], 'syl2anc', '( %s -> %s e. ( CC ^pm CC ) )' % (ph, PL))
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % ph)
    b0 = w.s([ccs, pm, w.inst('dvn0')], 'syl2anc', '( %s -> ( ( CC Dn %s ) ` 0 ) = %s )' % (ph, PL, PL))
    # MAPp(0) = PL
    one = '( ( -u 1 ^ 0 ) x. ( ! ` 0 ) )'
    o1 = w.s([w.s([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'exp0', '( -u 1 ^ 0 ) = 1') if False else w.s([w.s([], 'neg1cn', '-u 1 e. CC'), w.inst('exp0')], 'ax-mp', '( -u 1 ^ 0 ) = 1'),
                   w.s([], 'fac0', '( ! ` 0 ) = 1')], 'oveq12i', '%s = ( 1 x. 1 )' % one), w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'eqtri', '%s = 1' % one)
    o2 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'oveq2i', '( ( z - Q ) ^ ( 0 + 1 ) ) = ( ( z - Q ) ^ 1 )')
    o3 = w.s([w.s([w.s([o2], 'a1i', '( %s -> ( ( z - Q ) ^ ( 0 + 1 ) ) = ( ( z - Q ) ^ 1 ) )' % Az), w.s([wc], 'exp1d', '( %s -> ( ( z - Q ) ^ 1 ) = ( z - Q ) )' % Az)], 'eqtrd',
                   '( %s -> ( ( z - Q ) ^ ( 0 + 1 ) ) = ( z - Q ) )' % Az),
              w.s([o1], 'a1i', '( %s -> %s = 1 )' % (Az, one))], 'oveq12d' if False else 'T.', 'T.') if False else None
    o3a = w.s([w.s([o2], 'a1i', '( %s -> ( ( z - Q ) ^ ( 0 + 1 ) ) = ( ( z - Q ) ^ 1 ) )' % Az), w.s([wc], 'exp1d', '( %s -> ( ( z - Q ) ^ 1 ) = ( z - Q ) )' % Az)], 'eqtrd',
              '( %s -> ( ( z - Q ) ^ ( 0 + 1 ) ) = ( z - Q ) )' % Az)
    o3 = w.s([w.s([o1], 'a1i', '( %s -> %s = 1 )' % (Az, one)), o3a], 'oveq12d', '( %s -> ( %s / ( ( z - Q ) ^ ( 0 + 1 ) ) ) = ( 1 / ( z - Q ) ) )' % (Az, one))
    m0 = w.s([o3], 'mpteq2dva', '( %s -> %s = %s )' % (ph, MAPp('0'), PL))
    base = w.s([b0, m0], 'eqtr4d', '( %s -> %s )' % (ph, PSx('0')))
    # ---- step
    A1 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (ph, PSx('n'))
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    qc = t([], 'simpll', 'Q e. CC'); nn = t([], 'simplr', 'n e. NN0'); ih = t([], 'simpr', PSx('n'))
    pmt = t([qc, w.s([pm], 'id', '( %s -> %s e. ( CC ^pm CC ) )' % (ph, PL))], 'syl' if False else 'T.', 'T.') if False else w.s([qc, pm], 'syl', '( %s -> %s e. ( CC ^pm CC ) )' % (A1, PL))
    ccst = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A1)
    c1 = t([ccst, pmt, nn, w.inst('dvnp1')], 'syl3anc', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D ( ( CC Dn %s ) ` n ) )' % (PL, PL))
    c2 = t([ih], 'oveq2d', '( CC _D ( ( CC Dn %s ) ` n ) ) = ( CC _D %s )' % (PL, MAPp('n')))
    A1n = '( %s /\\ n e. NN0 )' % ph
    tn = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1n, f))
    qcn = tn([], 'simpl', 'Q e. CC'); nnn = tn([], 'simpr', 'n e. NN0')
    CN = '( ( -u 1 ^ n ) x. ( ! ` n ) )'
    W_ = '( z - Q )'
    C_ = '( %s ^ ( n + 1 ) )' % W_
    D_ = '( ( n + 1 ) x. ( %s ^ ( ( n + 1 ) - 1 ) ) )' % W_
    # dvmptdiv hypotheses under ( A1 /\ z e. U )
    Bz = '( %s /\\ z e. %s )' % (A1n, U)
    v = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Bz, f))
    adz = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Bz, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    zu2, zc2, zn2 = zfacts(Bz)
    wc2 = v([zc2, adz(qcn)], 'subcld', '%s e. CC' % W_)
    wn2 = v([zc2, adz(qcn), zn2], 'subne0d', '%s =/= 0' % W_)
    nnz = adz(nnn)
    n1 = v([nnz, w.inst('peano2nn0')], 'syl', '( n + 1 ) e. NN0')
    cnc = v([v([v([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % Bz), nnz], 'expcld', '( -u 1 ^ n ) e. CC')], 'id', 'T.') if False else
             v([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % Bz), nnz], 'expcld', '( -u 1 ^ n ) e. CC'),
             v([v([nnz], 'faccld', '( ! ` n ) e. NN')], 'nncnd', '( ! ` n ) e. CC')], 'mulcld', '%s e. CC' % CN)
    cc_ = v([wc2, n1], 'expcld', '%s e. CC' % C_)
    cn_ = v([wc2, wn2, v([n1], 'nn0zd', '( n + 1 ) e. ZZ')], 'expne0d', '%s =/= 0' % C_)
    cU0 = w.s([w.s([cc_, cn_], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (Bz, C_, C_)),
               w.s([], 'eldifsn', '( %s e. ( CC \\ { 0 } ) <-> ( %s e. CC /\\ %s =/= 0 ) )' % (C_, C_, C_))], 'sylibr', '( %s -> %s e. ( CC \\ { 0 } ) )' % (Bz, C_))
    km = v([v([nnz], 'nn0cnd', 'n e. CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % Bz)], 'pncand', '( ( n + 1 ) - 1 ) = n')
    dc_ = v([v([n1], 'nn0cnd', '( n + 1 ) e. CC'), v([wc2, v([km, nnz], 'eqeltrd', '( ( n + 1 ) - 1 ) e. NN0')], 'expcld', '( %s ^ ( ( n + 1 ) - 1 ) ) e. CC' % W_)], 'mulcld', '%s e. CC' % D_)
    cpr = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A1n)
    z0x = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % Bz)
    # derivative of the constant on U
    Ac = '( %s /\\ z e. CC )' % A1n
    cnc_c = w.s([w.s([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % Ac), w.s([nnn], 'adantr', '( %s -> n e. NN0 )' % Ac)], 'expcld', '( %s -> ( -u 1 ^ n ) e. CC )' % Ac),
                 w.s([w.s([w.s([nnn], 'adantr', '( %s -> n e. NN0 )' % Ac)], 'faccld', '( %s -> ( ! ` n ) e. NN )' % Ac)], 'nncnd', '( %s -> ( ! ` n ) e. CC )' % Ac)],
                'mulcld', '( %s -> %s e. CC )' % (Ac, CN))
    cncA = tn([tn([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % A1n), nnn], 'expcld', '( -u 1 ^ n ) e. CC'), tn([tn([nnn], 'faccld', '( ! ` n ) e. NN')], 'nncnd', '( ! ` n ) e. CC')],
             'mulcld', '%s e. CC' % CN)
    dcc = tn([cpr, cncA], 'dvmptc', '( CC _D ( z e. CC |-> %s ) ) = ( z e. CC |-> 0 )' % CN)
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    uop = tn([qcn, w.inst('cnopnsn')], 'syl', '%s e. %s' % (U, TOP))
    uccA = w.s([w.s([], 'difss', '%s C_ CC' % U)], 'a1i', '( %s -> %s C_ CC )' % (A1n, U))
    z0c = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % Ac)
    dcu = tn([cpr, cnc_c, z0c, dcc, uccA, jr, ej, uop], 'dvmptres', '( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> 0 )' % (U, CN, U))
    dse = tn([tn([uop, uccA], 'jca', '( %s e. %s /\\ %s C_ CC )' % (U, TOP, U)), tn([qcn, tn([nnn, w.inst('nn0p1nn')], 'syl', '( n + 1 ) e. NN')], 'jca', '( Q e. CC /\\ ( n + 1 ) e. NN )'),
              w.inst('dvsubexp')], 'syl2anc', '( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s )' % (U, C_, U, D_))
    E0 = '( ( ( 0 x. %s ) - ( %s x. %s ) ) / ( %s ^ 2 ) )' % (C_, D_, CN, C_)
    ddiv = tn([cpr, cnc, z0x, dcu, cU0, dc_, dse], 'dvmptdiv', '( CC _D ( z e. %s |-> ( %s / %s ) ) ) = ( z e. %s |-> %s )' % (U, CN, C_, U, E0))
    Pn = '( %s ^ n )' % W_
    pnc = v([wc2, nnz], 'expcld', '%s e. CC' % Pn)
    pnn = v([wc2, wn2, v([nnz], 'nn0zd', 'n e. ZZ')], 'expne0d', '%s =/= 0' % Pn)
    eC = v([wc2, nnz], 'expp1d', '%s = ( %s x. %s )' % (C_, Pn, W_))
    eD = v([v([km], 'oveq2d', '( %s ^ ( ( n + 1 ) - 1 ) ) = %s' % (W_, Pn))], 'oveq2d', '%s = ( ( n + 1 ) x. %s )' % (D_, Pn))
    st, E1 = w.congr(E0, {}, Bz, {}, rules={C_: ('( %s x. %s )' % (Pn, W_), eC), D_: ('( ( n + 1 ) x. %s )' % Pn, eD)})
    cz = Closure(w, Bz, {Pn: ('CC', pnc), W_: ('CC', wc2), CN: ('CC', cnc), 'n': ('CC', v([nnz], 'nn0cnd', 'n e. CC'))})
    for a_ in (Pn, W_, CN):
        cz.atom(a_)
    NUM1 = '( ( 0 x. ( %s x. %s ) ) - ( ( ( n + 1 ) x. %s ) x. %s ) )' % (Pn, W_, Pn, CN)
    X = '-u ( ( n + 1 ) x. %s )' % CN
    Y = '( ( %s x. %s ) x. %s )' % (Pn, W_, W_)
    assert E1 == '( %s / ( ( %s x. %s ) ^ 2 ) )' % (NUM1, Pn, W_), E1
    YY = '( ( ( n + 1 ) x. %s ) x. %s )' % (Pn, CN)
    z1 = v([v([pnc, wc2], 'mulcld', '( %s x. %s ) e. CC' % (Pn, W_))], 'mul02d', '( 0 x. ( %s x. %s ) ) = 0' % (Pn, W_))
    z2 = v([z1], 'oveq1d', '%s = ( 0 - %s )' % (NUM1, YY))
    z3 = w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (YY, YY))], 'a1i', '( %s -> -u %s = ( 0 - %s ) )' % (Bz, YY, YY))
    z4 = v([z2, z3], 'eqtr4d', '%s = -u %s' % (NUM1, YY))
    rn = v([z4, ringeq(w, Bz, '-u %s' % YY, '( %s x. %s )' % (Pn, X), cz)], 'eqtrd', '%s = ( %s x. %s )' % (NUM1, Pn, X))
    rd = ringeqp(w, Bz, '( ( %s x. %s ) ^ 2 )' % (Pn, W_), '( %s x. %s )' % (Pn, Y), cz)
    e2 = v([rn, rd], 'oveq12d', '%s = ( ( %s x. %s ) / ( %s x. %s ) )' % (E1, Pn, X, Pn, Y))
    xc = cz.mem(X, 'CC'); yc = cz.mem(Y, 'CC')
    yn = v([v([pnc, wc2], 'mulcld', '( %s x. %s ) e. CC' % (Pn, W_)), wc2, v([pnc, wc2, pnn, wn2], 'mulne0d', '( %s x. %s ) =/= 0' % (Pn, W_)), wn2], 'mulne0d', '%s =/= 0' % Y)
    e3 = v([xc, yc, pnc, yn, pnn], 'divcan5d', '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (Pn, X, Pn, Y, X, Y))
    NT = '( ( -u 1 ^ ( n + 1 ) ) x. ( ! ` ( n + 1 ) ) )'
    DT = '( %s ^ ( ( n + 1 ) + 1 ) )' % W_
    m1c = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % Bz)
    ex1 = v([m1c, nnz], 'expp1d', '( -u 1 ^ ( n + 1 ) ) = ( ( -u 1 ^ n ) x. -u 1 )')
    fc = v([nnz, w.inst('facp1')], 'syl', '( ! ` ( n + 1 ) ) = ( ( ! ` n ) x. ( n + 1 ) )')
    cz2 = Closure(w, Bz, {'n': ('CC', v([nnz], 'nn0cnd', 'n e. CC'))})
    cz2.leaf('( -u 1 ^ n )', 'CC', v([m1c, nnz], 'expcld', '( -u 1 ^ n ) e. CC')); cz2.atom('( -u 1 ^ n )')
    cz2.leaf('( ! ` n )', 'CC', v([v([nnz], 'faccld', '( ! ` n ) e. NN')], 'nncnd', '( ! ` n ) e. CC')); cz2.atom('( ! ` n )')
    XR = '( ( ( -u 1 ^ n ) x. -u 1 ) x. ( ( ! ` n ) x. ( n + 1 ) ) )'
    X2 = '-u ( ( n + 1 ) x. ( ( -u 1 ^ n ) x. ( ! ` n ) ) )'
    assert X == X2, (X, X2)
    rx = ringeq(w, Bz, X, XR, cz2)
    rx2 = v([ex1, fc], 'oveq12d', '%s = %s' % (NT, XR))
    ex = v([rx, rx2], 'eqtr4d', '%s = %s' % (X, NT))
    ey = v([v([wc2, n1], 'expp1d', '%s = ( %s x. %s )' % (DT, C_, W_)), v([eC], 'oveq1d', '( %s x. %s ) = %s' % (C_, W_, Y))], 'eqtrd', '%s = %s' % (DT, Y))
    e4 = v([ex, ey], 'oveq12d', '( %s / %s ) = ( %s / %s )' % (X, Y, NT, DT)) if False else v([ex, v([ey], 'eqcomd', '%s = %s' % (Y, DT))], 'oveq12d', '( %s / %s ) = ( %s / %s )' % (X, Y, NT, DT))
    pt = v([st, e2, e3, e4], 'eqtrd' if False else 'T.', 'T.') if False else \
        v([v([v([st, e2], 'eqtrd', '%s = ( ( %s x. %s ) / ( %s x. %s ) )' % (E0, Pn, X, Pn, Y)), e3], 'eqtrd', '%s = ( %s / %s )' % (E0, X, Y)), e4], 'eqtrd', '%s = ( %s / %s )' % (E0, NT, DT))
    mq = tn([pt], 'mpteq2dva', '( z e. %s |-> %s ) = %s' % (U, E0, MAPp('( n + 1 )')))
    step = t([t([c1, c2], 'eqtrd', '( ( CC Dn %s ) ` ( n + 1 ) ) = ( CC _D %s )' % (PL, MAPp('n'))), w.s([ddiv], 'adantr', '( %s -> %s )' % (A1, formula_of(w, ddiv).split(' -> ', 1)[1][:-2])), w.s([mq], 'adantr', '( %s -> %s )' % (A1, formula_of(w, mq).split(' -> ', 1)[1][:-2]))], '3eqtrd', PSx('( n + 1 )'))
    w.qed([subs['0'], subs['n'], subs['n1'], subs['K'], base, step], 'nn0indd', S['kdpoledn'])
    return run(w)




if __name__ == '__main__':
    gen_poledn()
