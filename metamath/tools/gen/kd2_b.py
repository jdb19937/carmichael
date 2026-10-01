"""Sortie KD2: the Turan floor and the seven budgets.
MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_b.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd2lib import *
from cl import formula_of, split_imp
from lin import linarith, nlinarith
from mvlib import ringeq
import num

only = sys.argv[1:]
T56 = C56E


def ante(label, sep):
    return S[label].split(' -> ' + sep, 1)[0][2:]


def e1rp(w, A):
    e1 = w.s([], 'epr', '_e e. RR+'); de = w.s([], 'df-e', '_e = ( exp ` 1 )')
    return w.s([w.s([de, e1], 'eqeltrri', '( exp ` 1 ) e. RR+')], 'a1i', '( %s -> ( exp ` 1 ) e. RR+ )' % A)


def tc(w, A):
    """( A -> T56 e. RR+ ), ( A -> T56 < 168 )"""
    t = w.s([], 'kd2tc', S['kd2tc'])
    return (w.s([w.s([t], 'simpli', '%s e. RR+' % T56)], 'a1i', '( %s -> %s e. RR+ )' % (A, T56)),
            w.s([w.s([t], 'simpri', '%s < ; ; 1 6 8' % T56)], 'a1i', '( %s -> %s < ; ; 1 6 8 )' % (A, T56)))


def gen_q8():
    w = W('kd2q8', 'Lean ` KDerivDetect.turan_floor_eq ` : ` X <_ F . Q / 8 ` iff ` X . ( 8 T^N ( 2 eta )^(j+2) ) <_ F ` , ` T = 56 e ` .')
    A0 = ante('kd2q8', '( X <_')
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g1 = d('simpl', [], '( E e. RR+ /\\ N e. NN0 /\\ J e. NN0 )'); g2 = d('simpr', [], '( X e. RR /\\ F e. RR )')
    ep = d('simp1d', [g1], 'E e. RR+'); nn = d('simp2d', [g1], 'N e. NN0'); jn = d('simp3d', [g1], 'J e. NN0')
    xr = d('simpld', [g2], 'X e. RR'); fr = d('simprd', [g2], 'F e. RR')
    tp, _ = tc(w, A0)
    j2 = d('nn0addcld' if False else 'syl2anc', [jn, a1(w, A0, '2nn0', '2 e. NN0'), w.inst('nn0addcl')], '( J + 2 ) e. NN0')
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN0', nn), '( J + 2 )': ('NN0', j2), T56: ('RR+', tp)})
    cl.atom(T56)
    TN = '( %s ^ N )' % T56; E2 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    tnp = cl.mem(TN, 'RR+'); e2p = cl.mem(E2, 'RR+')
    tc_ = d('rpcnd', [tp], '%s e. CC' % T56); tn0 = d('rpne0d', [tp], '%s =/= 0' % T56)
    ec2 = cl.mem('( 2 x. E )', 'CC'); en2 = cl.ne0('( 2 x. E )')
    r1 = d('exprecd', [tc_, tn0, d('nn0zd', [nn], 'N e. ZZ')], '( ( 1 / %s ) ^ N ) = ( 1 / %s )' % (T56, TN))
    r2 = d('exprecd', [ec2, en2, d('nn0zd', [j2], '( J + 2 ) e. ZZ')], '( ( 1 / ( 2 x. E ) ) ^ ( J + 2 ) ) = ( 1 / %s )' % E2)
    q1 = d('oveq12d', [r1, r2], '%s = ( ( 1 / %s ) x. ( 1 / %s ) )' % (QQ(), TN, E2))
    one = a1(w, A0, 'ax-1cn', '1 e. CC')
    tnc = d('rpcnd', [tnp], '%s e. CC' % TN); tnn = d('rpne0d', [tnp], '%s =/= 0' % TN)
    e2c = d('rpcnd', [e2p], '%s e. CC' % E2); e2n = d('rpne0d', [e2p], '%s =/= 0' % E2)
    q2 = d('divmuldivd', [one, tnc, one, e2c, tnn, e2n], '( ( 1 / %s ) x. ( 1 / %s ) ) = ( ( 1 x. 1 ) / ( %s x. %s ) )' % (TN, E2, TN, E2))
    q3 = d('oveq1d', [a1(w, A0, '1t1e1', '( 1 x. 1 ) = 1')], '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / ( %s x. %s ) )' % (TN, E2, TN, E2))
    PR = '( %s x. %s )' % (TN, E2)
    prp = d('rpmulcld', [tnp, e2p], '%s e. RR+' % PR)
    qq = chain(w, A0, [QQ(), '( ( 1 / %s ) x. ( 1 / %s ) )' % (TN, E2), '( ( 1 x. 1 ) / %s )' % PR, '( 1 / %s )' % PR], [q1, q2, q3])
    q8a = d('oveq1d', [qq], '%s = ( ( 1 / %s ) / 8 )' % (Q8(), PR))
    eight = cl.mem('8', 'CC'); e8n = cl.ne0('8')
    q8b = d('divdiv1d', [one, d('rpcnd', [prp], '%s e. CC' % PR), eight, d('rpne0d', [prp], '%s =/= 0' % PR), e8n], '( ( 1 / %s ) / 8 ) = ( 1 / ( %s x. 8 ) )' % (PR, PR))
    cl.leaf(TN, 'RR+', tnp); cl.leaf(E2, 'RR+', e2p)
    rq = ringeq(w, A0, '( %s x. 8 )' % PR, DEN, cl)
    q8c = d('oveq2d', [rq], '( 1 / ( %s x. 8 ) ) = ( 1 / %s )' % (PR, DEN))
    q8 = chain(w, A0, [Q8(), '( ( 1 / %s ) / 8 )' % PR, '( 1 / ( %s x. 8 ) )' % PR, '( 1 / %s )' % DEN], [q8a, q8b, q8c])
    dp = cl.mem(DEN, 'RR+')
    fq = d('oveq2d', [q8], '( F x. %s ) = ( F x. ( 1 / %s ) )' % (Q8(), DEN))
    fd = d('divrecd', [d('recnd', [fr], 'F e. CC'), d('rpcnd', [dp], '%s e. CC' % DEN), d('rpne0d', [dp], '%s =/= 0' % DEN)], '( F / %s ) = ( F x. ( 1 / %s ) )' % (DEN, DEN))
    fq2 = d('eqtr4d', [fq, fd], '( F x. %s ) = ( F / %s )' % (Q8(), DEN))
    b1 = d('breq2d', [fq2], '( X <_ ( F x. %s ) <-> X <_ ( F / %s ) )' % (Q8(), DEN))
    b2 = d('lemuldivd', [xr, fr, dp], '( ( X x. %s ) <_ F <-> X <_ ( F / %s ) )' % (DEN, DEN))
    fin = d('bitr4d', [b1, b2], '( X <_ ( F x. %s ) <-> ( X x. %s ) <_ F )' % (Q8(), DEN))
    w.qed([fin], 'idi', S['kd2q8'])
    return only_run(w, only)

def uz(w, A, M, N, mz, nz, le):
    """( A -> N e. ( ZZ>= ` M ) )"""
    j = D(w, A, '3jca', [mz, nz, le], '( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s )' % (M, N, M, N))
    return D(w, A, 'sylibr', [j, w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (N, M, M, N, M, N))],
             '%s e. ( ZZ>= ` %s )' % (N, M))


def bhparts(w, A, g):
    """g : ( A -> BH ); returns dict"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    g1 = d('simp1d', [g], '( E e. RR+ /\\ E <_ %s )' % R5000); g2 = d('simp2d', [g], '( N e. NN /\\ J e. NN0 )')
    ix = d('simp3d', [g], '( %s + 1 ) <_ ( J + 2 )' % M6)
    ep = d('simpld', [g1], 'E e. RR+'); e5 = d('simprd', [g1], 'E <_ %s' % R5000)
    nn = d('simpld', [g2], 'N e. NN'); jn = d('simprd', [g2], 'J e. NN0')
    return dict(ep=ep, e5=e5, nn=nn, jn=jn, ix=ix)


def q8le(w, A, X, xr, ep, nn0, jn, F='1', fr=None):
    """( A -> ( X <_ ( F x. Q8 ) <-> ( X x. DEN ) <_ F ) )"""
    fr = fr or a1(w, A, '1re', '1 e. RR')
    j1 = D(w, A, '3jca', [ep, nn0, jn], '( E e. RR+ /\\ N e. NN0 /\\ J e. NN0 )')
    j2 = D(w, A, 'jca', [xr, fr], '( %s e. RR /\\ %s e. RR )' % (X, F))
    return D(w, A, 'syl2anc', [j1, j2, w.inst('kd2q8')], '( %s <_ ( %s x. %s ) <-> ( %s x. %s ) <_ %s )' % (X, F, Q8(), X, DEN, F))


def q8one(w, A, X, xr, ep, nn0, jn, le):
    """from le : ( A -> ( X x. DEN ) <_ 1 ) conclude ( A -> X <_ Q8 )"""
    b = q8le(w, A, X, xr, ep, nn0, jn)
    x1 = D(w, A, 'mpbird', [le, b], '%s <_ ( 1 x. %s )' % (X, Q8()))
    cl = Closure(w, A, {'E': ('RR+', ep), 'N': ('NN0', nn0), 'J': ('NN0', jn), T56: ('RR+', tc(w, A)[0])})
    cl.atom(T56)
    m = D(w, A, 'mullidd', [cl.mem(Q8(), 'CC')], '( 1 x. %s ) = %s' % (Q8(), Q8()))
    return D(w, A, 'breqtrd', [x1, m], '%s <_ %s' % (X, Q8()))


def c729(w):
    """closed ( 3 ^ 6 ) = ; ; 7 2 9"""
    t = w.s([], '3t2e6', '( 3 x. 2 ) = 6')
    em = w.s([w.s([w.s([], '3cn', '3 e. CC')], 'a1i', '( T. -> 3 e. CC )'), w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( T. -> 2 e. NN0 )'),
              w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( T. -> 3 e. NN0 )')], 'expmuld', '( T. -> ( 3 ^ ( 3 x. 2 ) ) = ( ( 3 ^ 3 ) ^ 2 ) )')
    em = w.s([em], 'mptru', '( 3 ^ ( 3 x. 2 ) ) = ( ( 3 ^ 3 ) ^ 2 )')
    e6 = w.s([t], 'oveq2i', '( 3 ^ ( 3 x. 2 ) ) = ( 3 ^ 6 )')
    e27 = w.s([w.s([], '3exp3', '( 3 ^ 3 ) = ; 2 7')], 'oveq1i', '( ( 3 ^ 3 ) ^ 2 ) = ( ; 2 7 ^ 2 )')
    c27 = num.cc(w, '; 2 7')
    sq = w.s([c27], 'sqvali', '( ; 2 7 ^ 2 ) = ( ; 2 7 x. ; 2 7 )')
    m = num.mul_nat(w, 27, 27)
    a = w.s([e6, em], 'eqtr3i', '( 3 ^ 6 ) = ( ( 3 ^ 3 ) ^ 2 )')
    b = w.s([a, e27], 'eqtri', '( 3 ^ 6 ) = ( ; 2 7 ^ 2 )')
    c = w.s([b, sq], 'eqtri', '( 3 ^ 6 ) = ( ; 2 7 x. ; 2 7 )')
    return w.s([c, m], 'eqtri', '( 3 ^ 6 ) = ; ; 7 2 9')


def gen_bfar():
    w = W('kd2bfar', 'Lean ` KDerivDetect.budget_far ` at the Metamath constants: ` A / ( 6 eta )^j <_ Q / 8 ` with ` A = ( 1 / eta ) ( ( 5 / 4 ) / eta + 5 + C ) ` ( ~ kdl2 ), ` C <_ 35000000 L ` , Ndet ` >_ 6 + 840000000 eta L ` , ` N >_ 49 ` .')
    A0 = ante('kd2bfar', FAR('C'))
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g = d('simp1', [], BH); bp = bhparts(w, A0, g)
    ep, e5, nn, jn, ix = bp['ep'], bp['e5'], bp['nn'], bp['jn'], bp['ix']
    gl = d('simp2', [], '( %s /\\ ; 4 9 <_ N )' % LH)
    lh = d('simpld', [gl], LH); n49 = d('simprd', [gl], '; 4 9 <_ N')
    l1 = d('simpld', [lh], '( L e. RR /\\ 0 <_ L )'); nd = d('simprd', [lh], '( 6 + ( ( %s x. E ) x. L ) ) <_ N' % C8E8)
    lr = d('simpld', [l1], 'L e. RR'); l0 = d('simprd', [l1], '0 <_ L')
    gc = d('simp3', [], '( C e. RR /\\ C <_ ( %s x. L ) )' % C35)
    cr = d('simpld', [gc], 'C e. RR'); cle = d('simprd', [gc], 'C <_ ( %s x. L )' % C35)
    nn0 = d('nnnn0d', [nn], 'N e. NN0')
    tp, tlt = tc(w, A0)
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), T56: ('RR+', tp), 'L': ('RR', lr), 'C': ('RR', cr)})
    cl.atom(T56)
    er = d('rpred', [ep], 'E e. RR'); e0 = d('rpge0d', [ep], '0 <_ E')
    AP = '( ( ( ( 5 / 4 ) / E ) + 5 ) + C )'
    AA = '( ( 1 / E ) x. %s )' % AP
    X = FAR('C')
    U = '( %s ^ N )' % T56; P = '( ( 2 x. E ) ^ J )'; R = '( 3 ^ J )'
    up = cl.mem(U, 'RR+'); pp = cl.mem(P, 'RR+'); rp_ = cl.mem(R, 'RR+')
    cl.leaf(U, 'RR+', up); cl.leaf(P, 'RR+', pp); cl.leaf(R, 'RR+', rp_)
    WW = '( ( ( 5 / 4 ) + ( 5 x. E ) ) + ( C x. E ) )'
    # ---- 32 W <_ 2 N
    ce = d('lemul1ad', [cr, cl.mem('( %s x. L )' % C35, 'RR'), er, e0, cle], '( C x. E ) <_ ( ( %s x. L ) x. E )' % C35)
    cl2 = Closure(w, A0, {'E': ('RR', er), 'N': ('RR', d('nnred', [nn], 'N e. RR')), 'L': ('RR', lr), 'C': ('RR', cr)})
    w32 = nlinarith(w, A0, [ce, nd, e5, n49], '( ; 3 2 x. %s ) <_ ( 2 x. N )' % WW, closure=cl2)
    # ---- 6 N <_ 4 ^ N
    nr = d('nnred', [nn], 'N e. RR')
    two = a1(w, A0, '2re', '2 e. RR')
    nm = d('syl3anc', [d('jca', [two, a1(w, A0, '0le2', '0 <_ 2')], '( 2 e. RR /\\ 0 <_ 2 )'),
                      d('jca', [a1(w, A0, '4re', '4 e. RR'), d('eqbrtrrd' if False else 'eqled', [a1(w, A0, '2t2e4', '( 2 x. 2 ) = 4')], '( 2 x. 2 ) <_ 4')], '( 4 e. RR /\\ ( 2 x. 2 ) <_ 4 )'),
                      nn0, w.inst('kd2nmul')], '( N x. ( 2 ^ N ) ) <_ ( 4 ^ N )')
    # 8 <_ 2 ^ N from 3 <_ N
    n3 = uz(w, A0, '3', 'N', a1(w, A0, '3z', '3 e. ZZ'), d('nnzd', [nn], 'N e. ZZ'), linarith(w, A0, [n49], '3 <_ N', closure=cl2))
    p23 = d('leexp2ad', [two, a1(w, A0, '1le2', '1 <_ 2'), n3], '( 2 ^ 3 ) <_ ( 2 ^ N )')
    c8 = w.s([], 'cu2', '( 2 ^ 3 ) = 8')
    p8 = d('eqbrtrrd', [a1(w, A0, 'cu2', '( 2 ^ 3 ) = 8'), p23], '8 <_ ( 2 ^ N )')
    p2 = cl.mem('( 2 ^ N )', 'RR')
    n6 = d('lemul1ad', [a1(w, A0, '6re', '6 e. RR'), p2, nr, d('nnge1d' if False else 'nn0ge0d', [nn0], '0 <_ N'),
                        linarith(w, A0, [p8], '6 <_ ( 2 ^ N )', closure=Closure(w, A0, {'( 2 ^ N )': ('RR', p2)}))], '( 6 x. N ) <_ ( ( 2 ^ N ) x. N )')
    cl.leaf('( 2 ^ N )', 'RR', p2)
    e2n = ringeq(w, A0, '( ( 2 ^ N ) x. N )', '( N x. ( 2 ^ N ) )', cl)
    p4 = cl.mem('( 4 ^ N )', 'RR')
    n64 = d('letrd', [cl.mem('( 6 x. N )', 'RR'), cl.mem('( N x. ( 2 ^ N ) )', 'RR'), p4, d('breqtrd', [n6, e2n], '( 6 x. N ) <_ ( N x. ( 2 ^ N ) )'), nm], '( 6 x. N ) <_ ( 4 ^ N )')
    # ---- 6 N U <_ 3^(J+1)
    u0 = d('rpge0d', [up], '0 <_ %s' % U)
    ur = d('rpred', [up], '%s e. RR' % U)
    s1 = d('lemul1ad', [cl.mem('( 6 x. N )', 'RR'), p4, ur, u0, n64], '( ( 6 x. N ) x. %s ) <_ ( ( 4 ^ N ) x. %s )' % (U, U))
    t4 = d('mulexpd', [a1(w, A0, '4cn', '4 e. CC'), cl.mem(T56, 'CC'), nn0], '( ( 4 x. %s ) ^ N ) = ( ( 4 ^ N ) x. %s )' % (T56, U))
    tr_ = d('rpred', [tp], '%s e. RR' % T56)
    c7 = c729(w)
    clt = Closure(w, A0, {T56: ('RR', tr_)}); clt.atom(T56)
    t729 = linarith(w, A0, [tlt], '( 4 x. %s ) <_ ; ; 7 2 9' % T56, closure=clt)
    t36 = d('breqtrrd', [t729, a1(w, A0, None, None) if False else w.s([c7], 'a1i', '( %s -> ( 3 ^ 6 ) = ; ; 7 2 9 )' % A0)], '( 4 x. %s ) <_ ( 3 ^ 6 )' % T56)
    s2 = d('leexp1ad', [cl.mem('( 4 x. %s )' % T56, 'RR'), cl.mem('( 3 ^ 6 )', 'RR'), nn0, cl.ge0('( 4 x. %s )' % T56), t36],
           '( ( 4 x. %s ) ^ N ) <_ ( ( 3 ^ 6 ) ^ N )' % T56)
    em = d('expmuld', [a1(w, A0, '3cn', '3 e. CC'), nn0, a1(w, A0, '6nn0', '6 e. NN0')], '( 3 ^ ( 6 x. N ) ) = ( ( 3 ^ 6 ) ^ N )')
    j1 = d('nn0addcld' if False else 'syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    jr = d('nn0red', [jn], 'J e. RR')
    cl2.leaf('J', 'RR', jr)
    le6 = linarith(w, A0, [ix], '( 6 x. N ) <_ ( J + 1 )', closure=cl2)
    u6 = uz(w, A0, '( 6 x. N )', '( J + 1 )', d('zmulcld' if False else 'nn0zd', [d('nn0mulcld', [a1(w, A0, '6nn0', '6 e. NN0'), nn0], '( 6 x. N ) e. NN0')], '( 6 x. N ) e. ZZ'),
            d('nn0zd', [j1], '( J + 1 ) e. ZZ'), le6)
    s3 = d('leexp2ad', [a1(w, A0, '3re', '3 e. RR'), a1(w, A0, '1le3', '1 <_ 3'), u6], '( 3 ^ ( 6 x. N ) ) <_ ( 3 ^ ( J + 1 ) )')
    s4 = d('expp1d', [a1(w, A0, '3cn', '3 e. CC'), jn], '( 3 ^ ( J + 1 ) ) = ( ( 3 ^ J ) x. 3 )')
    # combine: ( 6 N ) U <_ ( 4^N ) U = ( 4T )^N <_ ( 3^6 )^N = 3^(6N) <_ 3^(J+1) = 3^J . 3
    k1 = d('breqtrrd', [s1, t4], '( ( 6 x. N ) x. %s ) <_ ( ( 4 x. %s ) ^ N )' % (U, T56))
    k2 = d('letrd', [cl.mem('( ( 6 x. N ) x. %s )' % U, 'RR'), cl.mem('( ( 4 x. %s ) ^ N )' % T56, 'RR'), cl.mem('( ( 3 ^ 6 ) ^ N )', 'RR'), k1, s2],
           '( ( 6 x. N ) x. %s ) <_ ( ( 3 ^ 6 ) ^ N )' % U)
    k3 = d('breqtrrd', [k2, em], '( ( 6 x. N ) x. %s ) <_ ( 3 ^ ( 6 x. N ) )' % U)
    k4 = d('letrd', [cl.mem('( ( 6 x. N ) x. %s )' % U, 'RR'), cl.mem('( 3 ^ ( 6 x. N ) )', 'RR'), cl.mem('( 3 ^ ( J + 1 ) )', 'RR'), k3, s3],
           '( ( 6 x. N ) x. %s ) <_ ( 3 ^ ( J + 1 ) )' % U)
    k5 = d('breqtrd', [k4, s4], '( ( 6 x. N ) x. %s ) <_ ( %s x. 3 )' % (U, R))
    # ---- 32 W U <_ 3^J
    wr = cl2.mem(WW, 'RR')
    k6 = d('lemul1ad', [cl2.mem('( ; 3 2 x. %s )' % WW, 'RR'), cl2.mem('( 2 x. N )', 'RR'), ur, u0, w32], '( ( ; 3 2 x. %s ) x. %s ) <_ ( ( 2 x. N ) x. %s )' % (WW, U, U))
    cl3 = Closure(w, A0, {'N': ('RR', nr), U: ('RR', ur), R: ('RR', d('rpred', [rp_], '%s e. RR' % R)), 'E': ('RR', er), 'C': ('RR', cr)})
    cl3.atom(U); cl3.atom(R)
    k7 = nlinarith(w, A0, [k5, k6], '( ( ; 3 2 x. %s ) x. %s ) <_ %s' % (WW, U, R), closure=cl3)
    # ---- X . DEN = ( ( 32 W ) U ) P / ( 6 E )^J with ( 6 E )^J = R P
    ec = d('rpcnd', [ep], 'E e. CC'); en = d('rpne0d', [ep], 'E =/= 0')
    SE = '( ( 6 x. E ) ^ J )'
    se = d('rpcnd', [cl.mem(SE, 'RR+')], '%s e. CC' % SE); sen = d('rpne0d', [cl.mem(SE, 'RR+')], '%s =/= 0' % SE)
    aac = cl.mem(AA, 'CC'); denc = cl.mem(DEN, 'CC')
    x1 = d('div32d' if False else 'div23d', [aac, denc, se, sen], '( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s )' % (AA, DEN, SE, AA, SE, DEN))
    # AA . DEN = ( ( ( 32 U ) P ) ( AP . E ) ) ( E ( 1 / E ) )
    IE = '( 1 / E )'
    cl4 = Closure(w, A0, {'E': ('RR+', ep), IE: ('CC', cl.mem(IE, 'CC')), AP: ('CC', cl.mem(AP, 'CC')), U: ('CC', d('rpcnd', [up], '%s e. CC' % U)),
                          P: ('CC', d('rpcnd', [pp], '%s e. CC' % P))})
    for a in (IE, AP, U, P):
        cl4.atom(a)
    E22 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    ea = d('expaddd', [cl.mem('( 2 x. E )', 'CC'), a1(w, A0, '2nn0', '2 e. NN0'), jn], '%s = ( %s x. ( ( 2 x. E ) ^ 2 ) )' % (E22, P))
    DEN2 = '( ( 8 x. %s ) x. ( %s x. ( ( 2 x. E ) ^ 2 ) ) )' % (U, P)
    dq = d('oveq2d', [ea], '( ( 8 x. %s ) x. %s ) = %s' % (U, E22, DEN2))
    ad = d('oveq2d', [dq], '( %s x. %s ) = ( %s x. %s )' % (AA, DEN, AA, DEN2))
    from mvlib import ringeqp
    MID = '( ( ( ( ; 3 2 x. %s ) x. %s ) x. ( %s x. E ) ) x. ( E x. %s ) )' % (U, P, AP, IE)
    rq = ringeqp(w, A0, '( %s x. %s )' % (AA, DEN2), MID, cl4)
    rc = d('recidd', [ec, en], '( E x. %s ) = 1' % IE)
    m1 = d('oveq2d', [rc], '%s = ( ( ( ( ; 3 2 x. %s ) x. %s ) x. ( %s x. E ) ) x. 1 )' % (MID, U, P, AP))
    Q32 = '( ( ( ; 3 2 x. %s ) x. %s ) x. ( %s x. E ) )' % (U, P, AP)
    m2 = d('mulridd', [cl4.mem(Q32, 'CC')], '( %s x. 1 ) = %s' % (Q32, Q32))
    # AP . E = W
    cl5 = Closure(w, A0, {'E': ('RR+', ep), '( ( 5 / 4 ) / E )': ('CC', cl.mem('( ( 5 / 4 ) / E )', 'CC')), 'C': ('CC', d('recnd', [cr], 'C e. CC'))})
    cl5.atom('( ( 5 / 4 ) / E )')
    ae1 = ringeq(w, A0, '( %s x. E )' % AP, '( ( ( ( 5 / 4 ) / E ) x. E ) + ( ( 5 x. E ) + ( C x. E ) ) )', cl5)
    dc = d('divcan1d', [cl.mem('( 5 / 4 )', 'CC'), ec, en], '( ( ( 5 / 4 ) / E ) x. E ) = ( 5 / 4 )')
    ae2 = d('oveq1d', [dc], '( ( ( ( 5 / 4 ) / E ) x. E ) + ( ( 5 x. E ) + ( C x. E ) ) ) = ( ( 5 / 4 ) + ( ( 5 x. E ) + ( C x. E ) ) )')
    ae3 = ringeq(w, A0, '( ( 5 / 4 ) + ( ( 5 x. E ) + ( C x. E ) ) )', WW, cl5)
    aw = chain(w, A0, ['( %s x. E )' % AP, '( ( ( ( 5 / 4 ) / E ) x. E ) + ( ( 5 x. E ) + ( C x. E ) ) )', '( ( 5 / 4 ) + ( ( 5 x. E ) + ( C x. E ) ) )', WW], [ae1, ae2, ae3])
    m3 = d('oveq2d', [aw], '%s = ( ( ( ; 3 2 x. %s ) x. %s ) x. %s )' % (Q32, U, P, WW))
    cl4.leaf(WW, 'CC', cl2.mem(WW, 'CC') if False else d('recnd', [wr], '%s e. CC' % WW)); cl4.atom(WW)
    FIN = '( %s x. ( ( ; 3 2 x. %s ) x. %s ) )' % (P, WW, U)
    m4 = ringeq(w, A0, '( ( ( ; 3 2 x. %s ) x. %s ) x. %s )' % (U, P, WW), FIN, cl4)
    ad2 = chain(w, A0, ['( %s x. %s )' % (AA, DEN), '( %s x. %s )' % (AA, DEN2), MID, '( %s x. 1 )' % Q32, Q32, '( ( ( ; 3 2 x. %s ) x. %s ) x. %s )' % (U, P, WW), FIN],
                [ad, rq, m1, m2, m3, m4])
    # ( 6 E )^J = P R . 
    s6 = ringeq(w, A0, '( 6 x. E )', '( 3 x. ( 2 x. E ) )', Closure(w, A0, {'E': ('RR+', ep)}))
    s6b = d('oveq1d', [s6], '%s = ( ( 3 x. ( 2 x. E ) ) ^ J )' % SE)
    s6c = d('mulexpd', [a1(w, A0, '3cn', '3 e. CC'), cl.mem('( 2 x. E )', 'CC'), jn], '( ( 3 x. ( 2 x. E ) ) ^ J ) = ( %s x. %s )' % (R, P))
    cl4.leaf(R, 'CC', d('rpcnd', [rp_], '%s e. CC' % R)); cl4.atom(R)
    s6d = ringeq(w, A0, '( %s x. %s )' % (R, P), '( %s x. %s )' % (P, R), cl4)
    sp = chain(w, A0, [SE, '( ( 3 x. ( 2 x. E ) ) ^ J )', '( %s x. %s )' % (R, P), '( %s x. %s )' % (P, R)], [s6b, s6c, s6d])
    # P ( 32 W U ) <_ P R
    k8 = d('lemul2ad', [cl3.mem('( ( ; 3 2 x. %s ) x. %s )' % (WW, U), 'RR'), d('rpred', [rp_], '%s e. RR' % R), d('rpred', [pp], '%s e. RR' % P),
                        d('rpge0d', [pp], '0 <_ %s' % P), k7], '%s <_ ( %s x. %s )' % (FIN, P, R))
    k9 = d('breqtrrd', [d('eqbrtrd', [ad2, k8], '( %s x. %s ) <_ ( %s x. %s )' % (AA, DEN, P, R)), sp], '( %s x. %s ) <_ %s' % (AA, DEN, SE))
    # ( AA DEN ) / SE <_ 1
    sep = cl.mem(SE, 'RR+')
    k10 = d('mpbird', [d('eqbrtrrd', [d('mullidd', [se], '( 1 x. %s ) = %s' % (SE, SE)), k9] if False else [k9, d('mullidd', [se], '( 1 x. %s ) = %s' % (SE, SE))], 'breqtrrd' and '( %s x. %s ) <_ ( 1 x. %s )' % (AA, DEN, SE)) if False else
            d('breqtrrd', [k9, d('mullidd', [se], '( 1 x. %s ) = %s' % (SE, SE))], '( %s x. %s ) <_ ( 1 x. %s )' % (AA, DEN, SE)),
            d('ledivmul2d', [cl.mem('( %s x. %s )' % (AA, DEN), 'RR'), a1(w, A0, '1re', '1 e. RR'), sep], '( ( ( %s x. %s ) / %s ) <_ 1 <-> ( %s x. %s ) <_ ( 1 x. %s ) )' % (AA, DEN, SE, AA, DEN, SE))],
            '( ( %s x. %s ) / %s ) <_ 1' % (AA, DEN, SE))
    k11 = d('eqbrtrrd', [x1, k10], '( %s x. %s ) <_ 1' % (X, DEN))
    fin = q8one(w, A0, X, cl.mem(X, 'RR'), ep, nn0, jn, k11)
    w.qed([fin], 'idi', S['kd2bfar'])
    return only_run(w, only)


def prelude(w, label, sep, extra_leaves=None):
    A0 = ante(label, sep)
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    g = d('simp1' if S[label].startswith('( ( ( ( E e. RR+') else 'simpl', [], BH) if False else None
    return A0


def lhparts(w, A, gl):
    d = lambda ref, h, c: D(w, A, ref, h, c)
    l1 = d('simpld', [gl], '( L e. RR /\\ 0 <_ L )'); nd = d('simprd', [gl], '( 6 + ( ( %s x. E ) x. L ) ) <_ N' % C8E8)
    return d('simpld', [l1], 'L e. RR'), d('simprd', [l1], '0 <_ L'), nd


def pow2(w, A, jn, base_cc, name_base):
    """( A -> ( B ^ ( J + 2 ) ) = ( ( B ^ ( J + 1 ) ) x. B ) )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    e1 = d('expp1d', [base_cc, j1], '( %s ^ ( ( J + 1 ) + 1 ) ) = ( ( %s ^ ( J + 1 ) ) x. %s )' % (name_base, name_base, name_base))
    jc = d('nn0cnd', [jn], 'J e. CC')
    a = d('addassd', [jc, a1(w, A, 'ax-1cn', '1 e. CC'), a1(w, A, 'ax-1cn', '1 e. CC')], '( ( J + 1 ) + 1 ) = ( J + ( 1 + 1 ) )')
    b = d('oveq2d', [a1(w, A, '1p1e2', '( 1 + 1 ) = 2')], '( J + ( 1 + 1 ) ) = ( J + 2 )')
    ab = d('eqtrd', [a, b], '( ( J + 1 ) + 1 ) = ( J + 2 )')
    e0 = d('oveq2d', [ab], '( %s ^ ( ( J + 1 ) + 1 ) ) = ( %s ^ ( J + 2 ) )' % (name_base, name_base))
    return d('eqtr3d', [e0, e1], '( %s ^ ( J + 2 ) ) = ( ( %s ^ ( J + 1 ) ) x. %s )' % (name_base, name_base, name_base)), j1


def gen_bcau():
    w = W('kd2bcau', 'Lean ` KDerivDetect.budget_cauchy ` at the Metamath constants: ` 2 . 3^(j+1) C <_ Q / 8 ` for ` 0 <_ C <_ 35000000 L ` (the remainder of ~ kdrep ; Lean ` C 2^(j+1) ` , ` C <_ 1040000 L ` ): ` 32 C eta ( 6 eta )^(j+1) T^N <_ ( 4 / 3 ) N ( T / 800 )^N <_ 1 ` .')
    A0 = ante('kd2bcau', CAU('C'))
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    bp = bhparts(w, A0, d('simp1', [], BH))
    ep, e5, nn, jn, ix = bp['ep'], bp['e5'], bp['nn'], bp['jn'], bp['ix']
    lr, l0, nd = lhparts(w, A0, d('simp2', [], LH))
    gc = d('simp3', [], '( C e. RR /\\ 0 <_ C /\\ C <_ ( %s x. L ) )' % C35)
    cr = d('simp1d', [gc], 'C e. RR'); c0 = d('simp2d', [gc], '0 <_ C'); cle = d('simp3d', [gc], 'C <_ ( %s x. L )' % C35)
    nn0 = d('nnnn0d', [nn], 'N e. NN0'); nr = d('nnred', [nn], 'N e. RR')
    tp, tlt = tc(w, A0)
    er = d('rpred', [ep], 'E e. RR'); e0 = d('rpge0d', [ep], '0 <_ E')
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), T56: ('RR+', tp), 'L': ('RR', lr), 'C': ('RR', cr)})
    cl.atom(T56)
    X = CAU('C')
    U = '( %s ^ N )' % T56; P1 = '( ( 2 x. E ) ^ ( J + 1 ) )'; R1 = '( 3 ^ ( J + 1 ) )'; V = '( ( 6 x. E ) ^ ( J + 1 ) )'
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    cl.have('( J + 1 )', 'NN0', j1)
    up = cl.mem(U, 'RR+'); ur = d('rpred', [up], '%s e. RR' % U); u0 = d('rpge0d', [up], '0 <_ %s' % U)
    # algebra: X . DEN = ( 32 ( C E ) ) ( U V )
    E22 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    e2, _ = pow2(w, A0, jn, cl.mem('( 2 x. E )', 'CC'), '( 2 x. E )')
    DEN2 = '( ( 8 x. %s ) x. ( %s x. ( 2 x. E ) ) )' % (U, P1)
    dq = d('oveq2d', [e2], '( ( 8 x. %s ) x. %s ) = %s' % (U, E22, DEN2))
    xd = d('oveq2d', [dq], '( %s x. %s ) = ( %s x. %s )' % (X, DEN, X, DEN2))
    cl4 = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), 'C': ('CC', d('recnd', [cr], 'C e. CC')), U: ('CC', d('rpcnd', [up], '%s e. CC' % U)),
                          P1: ('CC', cl.mem(P1, 'CC')), R1: ('CC', cl.mem(R1, 'CC'))})
    for a in (U, P1, R1):
        cl4.atom(a)
    MID = '( ( ; 3 2 x. ( C x. E ) ) x. ( %s x. ( %s x. %s ) ) )' % (U, R1, P1)
    rq = ringeq(w, A0, '( %s x. %s )' % (X, DEN2), MID, cl4)
    s6 = ringeq(w, A0, '( 6 x. E )', '( 3 x. ( 2 x. E ) )', Closure(w, A0, {'E': ('RR+', ep)}))
    v1 = d('oveq1d', [s6], '%s = ( ( 3 x. ( 2 x. E ) ) ^ ( J + 1 ) )' % V)
    v2 = d('mulexpd', [a1(w, A0, '3cn', '3 e. CC'), cl.mem('( 2 x. E )', 'CC'), j1], '( ( 3 x. ( 2 x. E ) ) ^ ( J + 1 ) ) = ( %s x. %s )' % (R1, P1))
    vv = d('eqtrd', [v1, v2], '%s = ( %s x. %s )' % (V, R1, P1))
    fq = '( ( ; 3 2 x. ( C x. E ) ) x. ( %s x. %s ) )' % (U, V)
    rv = d('eqtr4d', [rq, d('oveq2d', [d('oveq2d', [vv], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (U, V, U, R1, P1))],
                                   '%s = %s' % (fq, MID))], '( %s x. %s ) = %s' % (X, DEN2, fq))
    xe = d('eqtrd', [xd, rv], '( %s x. %s ) = %s' % (X, DEN, fq))
    # 32 ( C E ) <_ ( 4 / 3 ) N
    ce = d('lemul1ad', [cr, cl.mem('( %s x. L )' % C35, 'RR'), er, e0, cle], '( C x. E ) <_ ( ( %s x. L ) x. E )' % C35)
    cl2 = Closure(w, A0, {'E': ('RR', er), 'N': ('RR', nr), 'L': ('RR', lr), 'C': ('RR', cr)})
    k1 = nlinarith(w, A0, [ce, nd], '( ; 3 2 x. ( C x. E ) ) <_ ( ( 4 / 3 ) x. N )', closure=cl2)
    # V <_ ( 1 / 800 )^N
    B8 = '( 1 / ; ; 8 0 0 )'
    cl2.have(B8, 'RR', cl.mem(B8, 'RR'))
    se = linarith(w, A0, [e5], '( 6 x. E ) <_ %s' % B8, closure=cl2)
    v3 = d('leexp1ad', [cl.mem('( 6 x. E )', 'RR'), cl.mem(B8, 'RR'), j1, cl.ge0('( 6 x. E )'), se], '%s <_ ( %s ^ ( J + 1 ) )' % (V, B8))
    le6 = nlinarith(w, A0, [ix, d('nn0ge0d', [nn0], '0 <_ N')], 'N <_ ( J + 1 )', closure=Closure(w, A0, {'N': ('RR', nr), 'J': ('RR', d('nn0red', [jn], 'J e. RR'))}))
    un = uz(w, A0, 'N', '( J + 1 )', d('nnzd', [nn], 'N e. ZZ'), d('nn0zd', [j1], '( J + 1 ) e. ZZ'), le6)
    b8r = cl.mem(B8, 'RR')
    b81 = d('ltled', [b8r, a1(w, A0, '1re', '1 e. RR'), w.s([num.le_lit(w, B8, '1', strict=True)], 'a1i', '( %s -> %s < 1 )' % (A0, B8))], '%s <_ 1' % B8)
    v4 = d('leexp2rd', [b8r, nn0, un, cl.ge0(B8), b81], '( %s ^ ( J + 1 ) ) <_ ( %s ^ N )' % (B8, B8))
    ZN = '( %s ^ N )' % B8
    vz = d('letrd', [cl.mem(V, 'RR'), cl.mem('( %s ^ ( J + 1 ) )' % B8, 'RR'), cl.mem(ZN, 'RR'), v3, v4], '%s <_ %s' % (V, ZN))
    # products
    UV = '( %s x. %s )' % (U, V); UZ = '( %s x. %s )' % (U, ZN)
    k2 = d('lemul1ad', [cl2.mem('( ; 3 2 x. ( C x. E ) )', 'RR'), cl2.mem('( ( 4 / 3 ) x. N )', 'RR'), cl.mem(UV, 'RR'), cl.ge0(UV), k1],
           '%s <_ ( ( ( 4 / 3 ) x. N ) x. %s )' % (fq, UV))
    k3 = d('lemul2ad', [cl.mem(V, 'RR'), cl.mem(ZN, 'RR'), ur, u0, vz], '%s <_ %s' % (UV, UZ))
    k4 = d('lemul2ad', [cl.mem(UV, 'RR'), cl.mem(UZ, 'RR'), cl2.mem('( ( 4 / 3 ) x. N )', 'RR'), cl2.ge0('( ( 4 / 3 ) x. N )') if False else
                        d('mulge0d', [cl.mem('( 4 / 3 )', 'RR'), nr, cl.ge0('( 4 / 3 )'), d('nn0ge0d', [nn0], '0 <_ N')], '0 <_ ( ( 4 / 3 ) x. N )'), k3],
           '( ( ( 4 / 3 ) x. N ) x. %s ) <_ ( ( ( 4 / 3 ) x. N ) x. %s )' % (UV, UZ))
    AT = '( %s x. %s )' % (T56, B8)
    me = d('mulexpd', [cl.mem(T56, 'CC'), cl.mem(B8, 'CC'), nn0], '( %s ^ N ) = %s' % (AT, UZ))
    atr = cl.mem(AT, 'RR')
    nmul = d('syl3anc', [d('jca', [atr, cl.ge0(AT)], '( %s e. RR /\\ 0 <_ %s )' % (AT, AT)),
                         d('jca', [cl.mem('( 2 x. %s )' % AT, 'RR'), d('leidd', [cl.mem('( 2 x. %s )' % AT, 'RR')], '( 2 x. %s ) <_ ( 2 x. %s )' % (AT, AT))],
                           '( ( 2 x. %s ) e. RR /\\ ( 2 x. %s ) <_ ( 2 x. %s ) )' % (AT, AT, AT)), nn0, w.inst('kd2nmul')],
             '( N x. ( %s ^ N ) ) <_ ( ( 2 x. %s ) ^ N )' % (AT, AT))
    tr_ = d('rpred', [tp], '%s e. RR' % T56)
    clt = Closure(w, A0, {T56: ('RR', tr_)}); clt.atom(T56)
    a2 = linarith(w, A0, [tlt], '( 2 x. %s ) <_ 1' % AT, closure=clt, fast=False)
    u1 = uz(w, A0, '1', 'N', a1(w, A0, '1z', '1 e. ZZ'), d('nnzd', [nn], 'N e. ZZ'), d('nnge1d', [nn], '1 <_ N'))
    a3 = d('leexp2rd', [cl.mem('( 2 x. %s )' % AT, 'RR'), a1(w, A0, '1nn0', '1 e. NN0'), u1, cl.ge0('( 2 x. %s )' % AT), a2],
           '( ( 2 x. %s ) ^ N ) <_ ( ( 2 x. %s ) ^ 1 )' % (AT, AT))
    a4 = d('breqtrd', [a3, d('exp1d', [cl.mem('( 2 x. %s )' % AT, 'CC')], '( ( 2 x. %s ) ^ 1 ) = ( 2 x. %s )' % (AT, AT))], '( ( 2 x. %s ) ^ N ) <_ ( 2 x. %s )' % (AT, AT))
    a5 = d('letrd', [cl.mem('( N x. ( %s ^ N ) )' % AT, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AT, 'RR'), cl.mem('( 2 x. %s )' % AT, 'RR'), nmul, a4],
           '( N x. ( %s ^ N ) ) <_ ( 2 x. %s )' % (AT, AT))
    a6 = d('breqtrd', [a5, d('oveq2d', [me], '( N x. ( %s ^ N ) ) = ( N x. %s )' % (AT, UZ))], '( N x. %s ) <_ ( 2 x. %s )' % (UZ, AT)) if False else \
        d('eqbrtrrd', [d('oveq2d', [me], '( N x. ( %s ^ N ) ) = ( N x. %s )' % (AT, UZ)), a5], '( N x. %s ) <_ ( 2 x. %s )' % (UZ, AT))
    cl5 = Closure(w, A0, {'N': ('RR', nr), UZ: ('RR', cl.mem(UZ, 'RR')), T56: ('RR', tr_)}); cl5.atom(UZ); cl5.atom(T56)
    k5 = nlinarith(w, A0, [a6, tlt], '( ( ( 4 / 3 ) x. N ) x. %s ) <_ 1' % UZ, closure=cl5)
    k6 = d('letrd', [cl.mem(fq, 'RR'), cl.mem('( ( ( 4 / 3 ) x. N ) x. %s )' % UV, 'RR'), cl.mem('( ( ( 4 / 3 ) x. N ) x. %s )' % UZ, 'RR'), k2, k4],
           '%s <_ ( ( ( 4 / 3 ) x. N ) x. %s )' % (fq, UZ))
    k7 = d('letrd', [cl.mem(fq, 'RR'), cl.mem('( ( ( 4 / 3 ) x. N ) x. %s )' % UZ, 'RR'), a1(w, A0, '1re', '1 e. RR'), k6, k5], '%s <_ 1' % fq)
    k8 = d('eqbrtrd', [xe, k7], '( %s x. %s ) <_ 1' % (X, DEN))
    fin = q8one(w, A0, X, cl.mem(X, 'RR'), ep, nn0, jn, k8)
    w.qed([fin], 'idi', S['kd2bcau'])
    return only_run(w, only)


def gen_bpp():
    w = W('kd2bpp', 'Lean ` KDerivDetect.budget_primepow ` at the Metamath constants: ` 20 . 4^(j+1) <_ Q / 8 ` (nonprime tail constant 20 of ~ kd2npf for Lean ` 150 ` ): ` 320 eta T^N ( 8 eta )^(j+1) <_ 320 eta ( T / 625 )^N <_ 1 ` .')
    A0 = ante('kd2bpp', '( ; 2 0')
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    bp = bhparts(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    ep, e5, nn, jn, ix = bp['ep'], bp['e5'], bp['nn'], bp['jn'], bp['ix']
    nn0 = d('nnnn0d', [nn], 'N e. NN0'); nr = d('nnred', [nn], 'N e. RR')
    tp, tlt = tc(w, A0)
    er = d('rpred', [ep], 'E e. RR'); e0 = d('rpge0d', [ep], '0 <_ E')
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), T56: ('RR+', tp)})
    cl.atom(T56)
    X = '( ; 2 0 x. ( 4 ^ ( J + 1 ) ) )'
    U = '( %s ^ N )' % T56; P1 = '( ( 2 x. E ) ^ ( J + 1 ) )'; R1 = '( 4 ^ ( J + 1 ) )'; V = '( ( 8 x. E ) ^ ( J + 1 ) )'
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    cl.have('( J + 1 )', 'NN0', j1)
    up = cl.mem(U, 'RR+'); ur = d('rpred', [up], '%s e. RR' % U); u0 = d('rpge0d', [up], '0 <_ %s' % U)
    E22 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    e2, _ = pow2(w, A0, jn, cl.mem('( 2 x. E )', 'CC'), '( 2 x. E )')
    DEN2 = '( ( 8 x. %s ) x. ( %s x. ( 2 x. E ) ) )' % (U, P1)
    dq = d('oveq2d', [e2], '( ( 8 x. %s ) x. %s ) = %s' % (U, E22, DEN2))
    xd = d('oveq2d', [dq], '( %s x. %s ) = ( %s x. %s )' % (X, DEN, X, DEN2))
    cl4 = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), U: ('CC', d('rpcnd', [up], '%s e. CC' % U)),
                          P1: ('CC', cl.mem(P1, 'CC')), R1: ('CC', cl.mem(R1, 'CC'))})
    for a in (U, P1, R1):
        cl4.atom(a)
    MID = '( ( ; ; 3 2 0 x. E ) x. ( %s x. ( %s x. %s ) ) )' % (U, R1, P1)
    rq = ringeq(w, A0, '( %s x. %s )' % (X, DEN2), MID, cl4)
    s8 = ringeq(w, A0, '( 8 x. E )', '( 4 x. ( 2 x. E ) )', Closure(w, A0, {'E': ('RR+', ep)}))
    v1 = d('oveq1d', [s8], '%s = ( ( 4 x. ( 2 x. E ) ) ^ ( J + 1 ) )' % V)
    v2 = d('mulexpd', [a1(w, A0, '4cn', '4 e. CC'), cl.mem('( 2 x. E )', 'CC'), j1], '( ( 4 x. ( 2 x. E ) ) ^ ( J + 1 ) ) = ( %s x. %s )' % (R1, P1))
    vv = d('eqtrd', [v1, v2], '%s = ( %s x. %s )' % (V, R1, P1))
    fq = '( ( ; ; 3 2 0 x. E ) x. ( %s x. %s ) )' % (U, V)
    rv = d('eqtr4d', [rq, d('oveq2d', [d('oveq2d', [vv], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (U, V, U, R1, P1))],
                                   '%s = %s' % (fq, MID))], '( %s x. %s ) = %s' % (X, DEN2, fq))
    xe = d('eqtrd', [xd, rv], '( %s x. %s ) = %s' % (X, DEN, fq))
    B6 = '( 1 / ; ; 6 2 5 )'
    cl2 = Closure(w, A0, {'E': ('RR', er), 'N': ('RR', nr)})
    cl2.have(B6, 'RR', cl.mem(B6, 'RR'))
    se = linarith(w, A0, [e5], '( 8 x. E ) <_ %s' % B6, closure=cl2)
    v3 = d('leexp1ad', [cl.mem('( 8 x. E )', 'RR'), cl.mem(B6, 'RR'), j1, cl.ge0('( 8 x. E )'), se], '%s <_ ( %s ^ ( J + 1 ) )' % (V, B6))
    le6 = nlinarith(w, A0, [ix, d('nn0ge0d', [nn0], '0 <_ N')], 'N <_ ( J + 1 )', closure=Closure(w, A0, {'N': ('RR', nr), 'J': ('RR', d('nn0red', [jn], 'J e. RR'))}))
    un = uz(w, A0, 'N', '( J + 1 )', d('nnzd', [nn], 'N e. ZZ'), d('nn0zd', [j1], '( J + 1 ) e. ZZ'), le6)
    b6r = cl.mem(B6, 'RR')
    b61 = d('ltled', [b6r, a1(w, A0, '1re', '1 e. RR'), w.s([num.le_lit(w, B6, '1', strict=True)], 'a1i', '( %s -> %s < 1 )' % (A0, B6))], '%s <_ 1' % B6)
    v4 = d('leexp2rd', [b6r, nn0, un, cl.ge0(B6), b61], '( %s ^ ( J + 1 ) ) <_ ( %s ^ N )' % (B6, B6))
    ZN = '( %s ^ N )' % B6
    vz = d('letrd', [cl.mem(V, 'RR'), cl.mem('( %s ^ ( J + 1 ) )' % B6, 'RR'), cl.mem(ZN, 'RR'), v3, v4], '%s <_ %s' % (V, ZN))
    UV = '( %s x. %s )' % (U, V); UZ = '( %s x. %s )' % (U, ZN)
    k3 = d('lemul2ad', [cl.mem(V, 'RR'), cl.mem(ZN, 'RR'), ur, u0, vz], '%s <_ %s' % (UV, UZ))
    AT = '( %s x. %s )' % (T56, B6)
    me = d('mulexpd', [cl.mem(T56, 'CC'), cl.mem(B6, 'CC'), nn0], '( %s ^ N ) = %s' % (AT, UZ))
    tr_ = d('rpred', [tp], '%s e. RR' % T56)
    clt = Closure(w, A0, {T56: ('RR', tr_)}); clt.atom(T56)
    a2 = linarith(w, A0, [tlt], '%s <_ 1' % AT, closure=clt, fast=False)
    a3 = d('leexp1ad', [cl.mem(AT, 'RR'), a1(w, A0, '1re', '1 e. RR'), nn0, cl.ge0(AT), a2], '( %s ^ N ) <_ ( 1 ^ N )' % AT)
    a4 = d('breqtrd', [a3, d('syl', [d('nnzd', [nn], 'N e. ZZ'), w.inst('1exp')], '( 1 ^ N ) = 1')], '( %s ^ N ) <_ 1' % AT)
    a5 = d('eqbrtrrd', [me, a4], '%s <_ 1' % UZ)
    uv1 = d('letrd', [cl.mem(UV, 'RR'), cl.mem(UZ, 'RR'), a1(w, A0, '1re', '1 e. RR'), k3, a5], '%s <_ 1' % UV)
    k4 = d('lemul2ad', [cl.mem(UV, 'RR'), a1(w, A0, '1re', '1 e. RR'), cl.mem('( ; ; 3 2 0 x. E )', 'RR'), cl.ge0('( ; ; 3 2 0 x. E )'), uv1],
           '%s <_ ( ( ; ; 3 2 0 x. E ) x. 1 )' % fq)
    k4b = d('breqtrd', [k4, d('mulridd', [cl.mem('( ; ; 3 2 0 x. E )', 'CC')], '( ( ; ; 3 2 0 x. E ) x. 1 ) = ( ; ; 3 2 0 x. E )')], '%s <_ ( ; ; 3 2 0 x. E )' % fq)
    k5 = linarith(w, A0, [e5], '( ; ; 3 2 0 x. E ) <_ 1', closure=cl2)
    k6 = d('letrd', [cl.mem(fq, 'RR'), cl.mem('( ; ; 3 2 0 x. E )', 'RR'), a1(w, A0, '1re', '1 e. RR'), k4b, k5], '%s <_ 1' % fq)
    k8 = d('eqbrtrd', [xe, k6], '( %s x. %s ) <_ 1' % (X, DEN))
    fin = q8one(w, A0, X, cl.mem(X, 'RR'), ep, nn0, jn, k8)
    w.qed([fin], 'idi', S['kd2bpp'])
    return only_run(w, only)


def eparts(w, A):
    """( A -> e e. RR+ ), e e. RR, 2 <_ e, e <_ 3"""
    er = e1rp(w, A)
    de = w.s([], 'df-e', '_e = ( exp ` 1 )')
    e23 = w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')
    ere = w.s([], 'ere', '_e e. RR')
    g2 = w.s([w.s([w.s([], '2re', '2 e. RR'), ere, w.s([e23], 'simpli', '2 < _e')], 'ltleii', '2 <_ _e'), de], 'breqtri', '2 <_ ( exp ` 1 )')
    l3 = w.s([de, w.s([ere, w.s([], '3re', '3 e. RR'), w.s([e23], 'simpri', '_e < 3')], 'ltleii', '_e <_ 3')], 'eqbrtrri', '( exp ` 1 ) <_ 3')
    return er, w.s([g2], 'a1i', '( %s -> 2 <_ ( exp ` 1 ) )' % A), w.s([l3], 'a1i', '( %s -> ( exp ` 1 ) <_ 3 )' % A)


def two_t_le(w, A, tp):
    """( A -> ( 2 x. T56 ) <_ ( ( 8 / ( exp ` 1 ) ) ^ 6 ) )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    er, e2, e3 = eparts(w, A)
    E1 = '( exp ` 1 )'
    cl = Closure(w, A, {E1: ('RR+', er)}); cl.atom(E1)
    E6 = '( %s ^ 6 )' % E1; E7 = '( %s ^ 7 )' % E1
    lhs = '( ( 2 x. %s ) x. %s )' % (T56, E6)
    cl.have(E6, 'CC', cl.mem(E6, 'CC')); cl.atom(E6)
    r0 = ringeq(w, A, lhs, '( ; ; 1 1 2 x. ( %s x. %s ) )' % (E6, E1), cl)
    ep1 = d('expp1d', [cl.mem(E1, 'CC'), a1(w, A, '6nn0', '6 e. NN0')], '( %s ^ ( 6 + 1 ) ) = ( %s x. %s )' % (E1, E6, E1))
    e67 = d('eqtr3d', [d('oveq2d', [a1(w, A, '6p1e7', '( 6 + 1 ) = 7')], '( %s ^ ( 6 + 1 ) ) = %s' % (E1, E7)), ep1], '%s = ( %s x. %s )' % (E7, E6, E1))
    r = d('eqtr4d', [r0, d('oveq2d', [e67], '( ; ; 1 1 2 x. %s ) = ( ; ; 1 1 2 x. ( %s x. %s ) )' % (E7, E6, E1))], '%s = ( ; ; 1 1 2 x. %s )' % (lhs, E7))
    e73 = d('leexp1ad', [cl.mem(E1, 'RR'), a1(w, A, '3re', '3 e. RR'), a1(w, A, '7nn0', '7 e. NN0'), d('rpge0d', [er], '0 <_ %s' % E1), e3], '%s <_ ( 3 ^ 7 )' % E7)
    p37 = w.s([numpow(w, 3, 7)], 'a1i', '( %s -> ( 3 ^ 7 ) = ; ; ; 2 1 8 7 )' % A)
    e7b = d('breqtrd', [e73, p37], '%s <_ ; ; ; 2 1 8 7' % E7)
    m = d('lemul2ad', [cl.mem(E7, 'RR'), cl.mem('; ; ; 2 1 8 7', 'RR'), cl.mem('; ; 1 1 2', 'RR'), cl.ge0('; ; 1 1 2'), e7b],
          '( ; ; 1 1 2 x. %s ) <_ ( ; ; 1 1 2 x. ; ; ; 2 1 8 7 )' % E7)
    mm = w.s([num.mul_nat(w, 112, 2187)], 'a1i', '( %s -> ( ; ; 1 1 2 x. ; ; ; 2 1 8 7 ) = ; ; ; ; ; 2 4 4 9 4 4 )' % A)
    p86 = numpow(w, 8, 6)
    lt = w.s([num.le_nat(w, 244944, 262144), p86], 'breqtrri', '; ; ; ; ; 2 4 4 9 4 4 <_ ( 8 ^ 6 )')
    c1 = d('breqtrd', [m, mm], '( ; ; 1 1 2 x. %s ) <_ ; ; ; ; ; 2 4 4 9 4 4' % E7)
    c2 = d('breqtrd' if False else 'letrd', [cl.mem('( ; ; 1 1 2 x. %s )' % E7, 'RR'), cl.mem('; ; ; ; ; 2 4 4 9 4 4', 'RR'), cl.mem('( 8 ^ 6 )', 'RR'), c1, w.s([lt], 'a1i', '( %s -> ; ; ; ; ; 2 4 4 9 4 4 <_ ( 8 ^ 6 ) )' % A)],
           '( ; ; 1 1 2 x. %s ) <_ ( 8 ^ 6 )' % E7)
    c3 = d('eqbrtrd', [r, c2], '%s <_ ( 8 ^ 6 )' % lhs)
    tt = cl.mem('( 2 x. %s )' % T56, 'RR') if False else d('remulcld', [a1(w, A, '2re', '2 e. RR'), d('rpred', [tp], '%s e. RR' % T56)], '( 2 x. %s ) e. RR' % T56)
    e6p = cl.mem(E6, 'RR+')
    c4 = d('mpbid', [c3, d('lemuldivd', [tt, cl.mem('( 8 ^ 6 )', 'RR'), e6p], '( %s <_ ( 8 ^ 6 ) <-> ( 2 x. %s ) <_ ( ( 8 ^ 6 ) / %s ) )' % (lhs, T56, E6))],
           '( 2 x. %s ) <_ ( ( 8 ^ 6 ) / %s )' % (T56, E6))
    ed = d('expdivd', [cl.mem('8', 'CC'), cl.mem(E1, 'CC'), cl.ne0(E1), a1(w, A, '6nn0', '6 e. NN0')], '( ( 8 / %s ) ^ 6 ) = ( ( 8 ^ 6 ) / %s )' % (E1, E6))
    return d('breqtrrd', [c4, ed], '( 2 x. %s ) <_ ( ( 8 / %s ) ^ 6 )' % (T56, E1)), er, e2, e3


def gen_blow():
    w = W('kd2blow', 'Lean ` KDerivDetect.budget_low ` at the Metamath constants: ` ( M / ( 16 eta ) )^(j+1) ( ( 5 / 4 ) / eta + 5 ) <_ (j+1)! Q / 8 ` ( ~ vmsharp ` ( 5 / 4 ) / u + 5 ` for Lean ` 1 / u + 2 ` ; ` 2 eta ( ( 5 / 4 ) / eta + 5 ) <_ 3 ` ).')
    A0 = ante('kd2blow', '( ( ( %s' % M6)
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    bp = bhparts(w, A0, d('simpl', [], BH))
    ep, e5, nn, jn, ix = bp['ep'], bp['e5'], bp['nn'], bp['jn'], bp['ix']
    n5 = d('simpr', [], '5 <_ N')
    nn0 = d('nnnn0d', [nn], 'N e. NN0'); nr = d('nnred', [nn], 'N e. RR')
    tp, tlt = tc(w, A0)
    er = d('rpred', [ep], 'E e. RR'); e0 = d('rpge0d', [ep], '0 <_ E')
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), '( J + 1 )': ('NN0', j1), T56: ('RR+', tp)})
    cl.atom(T56)
    G = '( %s / ( ; 1 6 x. E ) )' % M6; A2 = '( ( ( 5 / 4 ) / E ) + 5 )'
    GJ = '( %s ^ ( J + 1 ) )' % G
    X = '( %s x. %s )' % (GJ, A2)
    F = '( ! ` ( J + 1 ) )'
    fr = d('nnred', [d('faccld', [j1], '%s e. NN' % F)], '%s e. RR' % F)
    U = '( %s ^ N )' % T56; P1 = '( ( 2 x. E ) ^ ( J + 1 ) )'
    up = cl.mem(U, 'RR+'); ur = d('rpred', [up], '%s e. RR' % U); u0 = d('rpge0d', [up], '0 <_ %s' % U)
    E22 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    e2, _ = pow2(w, A0, jn, cl.mem('( 2 x. E )', 'CC'), '( 2 x. E )')
    DEN2 = '( ( 8 x. %s ) x. ( %s x. ( 2 x. E ) ) )' % (U, P1)
    dq = d('oveq2d', [e2], '( ( 8 x. %s ) x. %s ) = %s' % (U, E22, DEN2))
    xd = d('oveq2d', [dq], '( %s x. %s ) = ( %s x. %s )' % (X, DEN, X, DEN2))
    cl4 = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), U: ('CC', d('rpcnd', [up], '%s e. CC' % U)),
                          P1: ('CC', cl.mem(P1, 'CC')), GJ: ('CC', cl.mem(GJ, 'CC')), A2: ('CC', cl.mem(A2, 'CC'))})
    for a in (U, P1, GJ, A2):
        cl4.atom(a)
    MID = '( ( %s x. %s ) x. ( ( ( 2 x. E ) x. %s ) x. ( 8 x. %s ) ) )' % (GJ, P1, A2, U)
    rq = ringeq(w, A0, '( %s x. %s )' % (X, DEN2), MID, cl4)
    # G^(J+1) P1 = ( ( 6 N ) / 8 )^(J+1)
    H = '( %s / 8 )' % M6
    gp = d('mulexpd', [cl.mem(G, 'CC'), cl.mem('( 2 x. E )', 'CC'), j1], '( ( %s x. ( 2 x. E ) ) ^ ( J + 1 ) ) = ( %s x. %s )' % (G, GJ, P1))
    m6c = cl.mem(M6, 'CC'); e16 = cl.mem('( ; 1 6 x. E )', 'CC'); e16n = cl.ne0('( ; 1 6 x. E )')
    g1 = d('div23d', [m6c, cl.mem('( 2 x. E )', 'CC'), e16, e16n], '( ( %s x. ( 2 x. E ) ) / ( ; 1 6 x. E ) ) = ( %s x. ( 2 x. E ) )' % (M6, G))
    cl6 = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), 'N': ('CC', d('nncnd', [nn], 'N e. CC'))})
    g2 = ringeq(w, A0, '( %s x. ( 2 x. E ) )' % M6, '( ( ; 1 2 x. N ) x. E )', cl6)
    g3 = ringeq(w, A0, '( ; 1 6 x. E )', '( ; 1 6 x. E )', cl6) if False else None
    g4 = d('oveq1d', [g2], '( ( %s x. ( 2 x. E ) ) / ( ; 1 6 x. E ) ) = ( ( ( ; 1 2 x. N ) x. E ) / ( ; 1 6 x. E ) )' % M6)
    g5 = d('divcan5rd', [cl.mem('( ; 1 2 x. N )', 'CC'), cl.mem('; 1 6', 'CC'), d('rpcnd', [ep], 'E e. CC'), cl.ne0('; 1 6'), d('rpne0d', [ep], 'E =/= 0')],
           '( ( ( ; 1 2 x. N ) x. E ) / ( ; 1 6 x. E ) ) = ( ( ; 1 2 x. N ) / ; 1 6 )')
    g6 = ringeq(w, A0, '( ( ; 1 2 x. N ) / ; 1 6 )', H, cl6)
    gg = chain(w, A0, ['( %s x. ( 2 x. E ) )' % G, '( ( %s x. ( 2 x. E ) ) / ( ; 1 6 x. E ) )' % M6, '( ( ( ; 1 2 x. N ) x. E ) / ( ; 1 6 x. E ) )',
                       '( ( ; 1 2 x. N ) / ; 1 6 )', H], [('r', g1), g4, g5, g6])
    HJ = '( %s ^ ( J + 1 ) )' % H
    gh = d('eqtr3d', [gp, d('oveq1d', [gg], '( ( %s x. ( 2 x. E ) ) ^ ( J + 1 ) ) = %s' % (G, HJ))], '( %s x. %s ) = %s' % (GJ, P1, HJ))
    # ( 2 E ) A2 = ( 5 / 2 ) + ( ; 1 0 x. E )
    F54 = '( ( 5 / 4 ) / E )'
    cl7 = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), F54: ('CC', cl.mem(F54, 'CC'))}); cl7.atom(F54)
    a1_ = ringeq(w, A0, '( ( 2 x. E ) x. %s )' % A2, '( ( 2 x. ( E x. %s ) ) + ( ; 1 0 x. E ) )' % F54, cl7)
    a2_ = d('oveq1d', [d('oveq2d', [d('divcan2d', [cl.mem('( 5 / 4 )', 'CC'), d('rpcnd', [ep], 'E e. CC'), d('rpne0d', [ep], 'E =/= 0')], '( E x. %s ) = ( 5 / 4 )' % F54)],
                                  '( 2 x. ( E x. %s ) ) = ( 2 x. ( 5 / 4 ) )' % F54)], '( ( 2 x. ( E x. %s ) ) + ( ; 1 0 x. E ) ) = ( ( 2 x. ( 5 / 4 ) ) + ( ; 1 0 x. E ) )' % F54)
    a3_ = ringeq(w, A0, '( ( 2 x. ( 5 / 4 ) ) + ( ; 1 0 x. E ) )', '( ( 5 / 2 ) + ( ; 1 0 x. E ) )', cl7)
    B2 = '( ( 5 / 2 ) + ( ; 1 0 x. E ) )'
    aa = chain(w, A0, ['( ( 2 x. E ) x. %s )' % A2, '( ( 2 x. ( E x. %s ) ) + ( ; 1 0 x. E ) )' % F54, '( ( 2 x. ( 5 / 4 ) ) + ( ; 1 0 x. E ) )', B2], [a1_, a2_, a3_])
    xe1 = d('oveq12d', [gh, d('oveq1d', [aa], '( ( ( 2 x. E ) x. %s ) x. ( 8 x. %s ) ) = ( %s x. ( 8 x. %s ) )' % (A2, U, B2, U))],
            '%s = ( %s x. ( %s x. ( 8 x. %s ) ) )' % (MID, HJ, B2, U))
    XV = '( %s x. ( %s x. ( 8 x. %s ) ) )' % (HJ, B2, U)
    xe = chain(w, A0, ['( %s x. %s )' % (X, DEN), '( %s x. %s )' % (X, DEN2), MID, XV], [xd, rq, xe1])
    # ( B2 ) ( 8 U ) <_ 24 U
    cl2 = Closure(w, A0, {'E': ('RR', er), U: ('RR', ur)}); cl2.atom(U)
    b1 = nlinarith(w, A0, [e5, u0], '( %s x. ( 8 x. %s ) ) <_ ( ; 2 4 x. %s )' % (B2, U, U), closure=cl2)
    hr = cl.mem(HJ, 'RR'); h0 = cl.ge0(HJ)
    b2 = d('lemul2ad', [cl2.mem('( %s x. ( 8 x. %s ) )' % (B2, U), 'RR'), cl2.mem('( ; 2 4 x. %s )' % U, 'RR'), hr, h0, b1], '%s <_ ( %s x. ( ; 2 4 x. %s ) )' % (XV, HJ, U))
    # 24 U <_ ( 8 / e )^(J+1)
    tt, erp, eg2, el3 = two_t_le(w, A0, tp)
    E1 = '( exp ` 1 )'; EB = '( 8 / %s )' % E1
    n5z = uz(w, A0, '5', 'N', w.s([num.z_nat(w, 5)], 'a1i', '( %s -> 5 e. ZZ )' % A0), d('nnzd', [nn], 'N e. ZZ'), n5)
    p25 = d('leexp2ad', [a1(w, A0, '2re', '2 e. RR'), a1(w, A0, '1le2', '1 <_ 2'), n5z], '( 2 ^ 5 ) <_ ( 2 ^ N )')
    p32 = w.s([numpow(w, 2, 5)], 'a1i', '( %s -> ( 2 ^ 5 ) = ; 3 2 )' % A0)
    p2n = d('eqbrtrrd', [p32, p25], '; 3 2 <_ ( 2 ^ N )')
    cl3 = Closure(w, A0, {'( 2 ^ N )': ('RR', cl.mem('( 2 ^ N )', 'RR')), U: ('RR', ur)}); cl3.atom('( 2 ^ N )'); cl3.atom(U)
    c1 = nlinarith(w, A0, [p2n, u0], '( ; 2 4 x. %s ) <_ ( ( 2 ^ N ) x. %s )' % (U, U), closure=cl3)
    c2 = d('mulexpd', [a1(w, A0, '2cn', '2 e. CC'), cl.mem(T56, 'CC'), nn0], '( ( 2 x. %s ) ^ N ) = ( ( 2 ^ N ) x. %s )' % (T56, U))
    cl.leaf(E1, 'RR+', erp)
    ebr = cl.mem(EB, 'RR')
    c3 = d('leexp1ad', [cl.mem('( 2 x. %s )' % T56, 'RR'), cl.mem('( %s ^ 6 )' % EB, 'RR'), nn0, cl.ge0('( 2 x. %s )' % T56), tt],
           '( ( 2 x. %s ) ^ N ) <_ ( ( %s ^ 6 ) ^ N )' % (T56, EB))
    c4 = d('expmuld', [cl.mem(EB, 'CC'), nn0, a1(w, A0, '6nn0', '6 e. NN0')], '( %s ^ ( 6 x. N ) ) = ( ( %s ^ 6 ) ^ N )' % (EB, EB))
    jr = d('nn0red', [jn], 'J e. RR')
    le6 = linarith(w, A0, [ix], '( 6 x. N ) <_ ( J + 1 )', closure=Closure(w, A0, {'N': ('RR', nr), 'J': ('RR', jr)}))
    u6 = uz(w, A0, '( 6 x. N )', '( J + 1 )', d('nn0zd', [d('nn0mulcld', [a1(w, A0, '6nn0', '6 e. NN0'), nn0], '( 6 x. N ) e. NN0')], '( 6 x. N ) e. ZZ'),
            d('nn0zd', [j1], '( J + 1 ) e. ZZ'), le6)
    cle = Closure(w, A0, {E1: ('RR', d('rpred', [erp], '%s e. RR' % E1))}); cle.atom(E1)
    e8 = linarith(w, A0, [el3], '%s <_ 8' % E1, closure=cle)
    eb1 = d('mpbid', [d('breqtrrd', [e8, d('mullidd', [cl.mem(E1, 'CC')], '( 1 x. %s ) = %s' % (E1, E1))], '( 1 x. %s ) <_ 8' % E1) if False else
                       d('eqbrtrd', [d('mullidd', [cl.mem(E1, 'CC')], '( 1 x. %s ) = %s' % (E1, E1)), e8], '( 1 x. %s ) <_ 8' % E1),
                       d('lemuldivd', [a1(w, A0, '1re', '1 e. RR'), cl.mem('8', 'RR'), erp], '( ( 1 x. %s ) <_ 8 <-> 1 <_ ( 8 / %s ) )' % (E1, E1))], '1 <_ %s' % EB)
    c5 = d('leexp2ad', [ebr, eb1, u6], '( %s ^ ( 6 x. N ) ) <_ ( %s ^ ( J + 1 ) )' % (EB, EB))
    EBJ = '( %s ^ ( J + 1 ) )' % EB
    k1 = d('breqtrrd', [c1, c2], '( ; 2 4 x. %s ) <_ ( ( 2 x. %s ) ^ N )' % (U, T56))
    k2 = d('letrd', [cl3.mem('( ; 2 4 x. %s )' % U, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % T56, 'RR'), cl.mem('( ( %s ^ 6 ) ^ N )' % EB, 'RR'), k1, c3],
           '( ; 2 4 x. %s ) <_ ( ( %s ^ 6 ) ^ N )' % (U, EB))
    k3 = d('breqtrrd', [k2, c4], '( ; 2 4 x. %s ) <_ ( %s ^ ( 6 x. N ) )' % (U, EB))
    k4 = d('letrd', [cl3.mem('( ; 2 4 x. %s )' % U, 'RR'), cl.mem('( %s ^ ( 6 x. N ) )' % EB, 'RR'), cl.mem(EBJ, 'RR'), k3, c5], '( ; 2 4 x. %s ) <_ %s' % (U, EBJ))
    b3 = d('lemul2ad', [cl3.mem('( ; 2 4 x. %s )' % U, 'RR'), cl.mem(EBJ, 'RR'), hr, h0, k4], '( %s x. ( ; 2 4 x. %s ) ) <_ ( %s x. %s )' % (HJ, U, HJ, EBJ))
    # H^(J+1) ( 8 / e )^(J+1) = ( ( 6 N ) / e )^(J+1)
    ME = '( %s / %s )' % (M6, E1)
    h1 = d('mulexpd', [cl.mem(H, 'CC'), cl.mem(EB, 'CC'), j1], '( ( %s x. %s ) ^ ( J + 1 ) ) = ( %s x. %s )' % (H, EB, HJ, EBJ))
    h2 = d('divmuldivd', [m6c, cl.mem('8', 'CC'), cl.mem('8', 'CC'), cl.mem(E1, 'CC'), cl.ne0('8'), cl.ne0(E1)], '( %s x. %s ) = ( ( %s x. 8 ) / ( 8 x. %s ) )' % (H, EB, M6, E1))
    h3 = d('oveq2d', [d('mulcomd', [cl.mem('8', 'CC'), cl.mem(E1, 'CC')], '( 8 x. %s ) = ( %s x. 8 )' % (E1, E1))], '( ( %s x. 8 ) / ( 8 x. %s ) ) = ( ( %s x. 8 ) / ( %s x. 8 ) )' % (M6, E1, M6, E1))
    h4 = d('divcan5rd', [m6c, cl.mem(E1, 'CC'), cl.mem('8', 'CC'), cl.ne0(E1), cl.ne0('8')], '( ( %s x. 8 ) / ( %s x. 8 ) ) = %s' % (M6, E1, ME))
    hh = chain(w, A0, ['( %s x. %s )' % (H, EB), '( ( %s x. 8 ) / ( 8 x. %s ) )' % (M6, E1), '( ( %s x. 8 ) / ( %s x. 8 ) )' % (M6, E1), ME], [h2, h3, h4])
    h5 = d('eqtr3d', [h1, d('oveq1d', [hh], '( ( %s x. %s ) ^ ( J + 1 ) ) = ( %s ^ ( J + 1 ) )' % (H, EB, ME))], '( %s x. %s ) = ( %s ^ ( J + 1 ) )' % (HJ, EBJ, ME))
    st = d('syl2anc', [d('jca', [cl.mem(M6, 'RR'), cl.ge0(M6)], '( %s e. RR /\\ 0 <_ %s )' % (M6, M6)), d('jca', [j1, le6], '( ( J + 1 ) e. NN0 /\\ %s <_ ( J + 1 ) )' % M6), w.inst('kd2stir')],
           '( ( %s / %s ) ^ ( J + 1 ) ) <_ %s' % (M6, E1, F))
    k5 = d('eqbrtrd', [h5, st], '( %s x. %s ) <_ %s' % (HJ, EBJ, F))
    k6 = d('letrd', [cl.mem(XV, 'RR'), cl.mem('( %s x. ( ; 2 4 x. %s ) )' % (HJ, U), 'RR'), cl.mem('( %s x. %s )' % (HJ, EBJ), 'RR'), b2, b3], '%s <_ ( %s x. %s )' % (XV, HJ, EBJ))
    k7 = d('letrd', [cl.mem(XV, 'RR'), cl.mem('( %s x. %s )' % (HJ, EBJ), 'RR'), fr, k6, k5], '%s <_ %s' % (XV, F))
    k8 = d('eqbrtrd', [xe, k7], '( %s x. %s ) <_ %s' % (X, DEN, F))
    b = q8le(w, A0, X, cl.mem(X, 'RR'), ep, nn0, jn, F=F, fr=fr)
    fin = d('mpbird', [k8, b], '%s <_ %s' % (X, FQ8()))
    w.qed([fin], 'idi', S['kd2blow'])
    return only_run(w, only)


def efk(w, A, k):
    """( A -> ( exp ` k ) = ( ( exp ` 1 ) ^ k ) ) for a numeral k"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    kz = w.s([num.z_nat(w, int(num.nat_value(k)))], 'a1i', '( %s -> %s e. ZZ )' % (A, k))
    e = d('syl2anc', [a1(w, A, 'ax-1cn', '1 e. CC'), kz, w.inst('efexp')], '( exp ` ( %s x. 1 ) ) = ( ( exp ` 1 ) ^ %s )' % (k, k))
    m = d('fveq2d', [d('mulridd', [w.s([num.cc(w, k)], 'a1i', '( %s -> %s e. CC )' % (A, k))], '( %s x. 1 ) = %s' % (k, k))], '( exp ` ( %s x. 1 ) ) = ( exp ` %s )' % (k, k))
    return d('eqtr3d', [m, e], '( exp ` %s ) = ( ( exp ` 1 ) ^ %s )' % (k, k))


def efkn(w, A, k, nz):
    """( A -> ( exp ` ( k x. N ) ) = ( ( exp ` k ) ^ N ) ), nz : ( A -> N e. ZZ )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    kc = w.s([num.cc(w, k)], 'a1i', '( %s -> %s e. CC )' % (A, k))
    e = d('syl2anc', [kc, nz, w.inst('efexp')], '( exp ` ( N x. %s ) ) = ( ( exp ` %s ) ^ N )' % (k, k))
    m = d('fveq2d', [d('mulcomd', [kc, d('zcnd', [nz], 'N e. CC')], '( %s x. N ) = ( N x. %s )' % (k, k))], '( exp ` ( %s x. N ) ) = ( exp ` ( N x. %s ) )' % (k, k))
    return d('eqtrd', [m, e], '( exp ` ( %s x. N ) ) = ( ( exp ` %s ) ^ N )' % (k, k))


def gen_bhigh():
    w = W('kd2bhigh', 'Lean ` KDerivDetect.budget_high ` at the Metamath constants (factor ` 5 / 4 ` of ~ kddiag2 ): ` e^(-8M) (j+1)! e ( 5 / 4 ) ( j + 3 ) / ( eta / 2 )^(j+2) <_ (j+1)! Q / 8 ` : ` 10 e ( j + 3 ) 4^(j+2) T^N <_ N ( 80 e 16384 T )^N <_ ( e^48 )^N ` .')
    A0 = ante('kd2bhigh', '( ( exp ` -u')
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    ep = d('simp1', [], 'E e. RR+'); g2 = d('simp2', [], '( N e. NN /\\ J e. NN0 )'); j7 = d('simp3', [], '( J + 2 ) <_ ( 7 x. N )')
    nn = d('simpld', [g2], 'N e. NN'); jn = d('simprd', [g2], 'J e. NN0')
    nn0 = d('nnnn0d', [nn], 'N e. NN0'); nr = d('nnred', [nn], 'N e. RR'); nz = d('nnzd', [nn], 'N e. ZZ')
    tp, tlt = tc(w, A0)
    er = d('rpred', [ep], 'E e. RR')
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    j2 = d('nn0addcld', [jn, a1(w, A0, '2nn0', '2 e. NN0')], '( J + 2 ) e. NN0')
    erp, eg2, el3 = eparts(w, A0)
    E1 = '( exp ` 1 )'
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), '( J + 1 )': ('NN0', j1), '( J + 2 )': ('NN0', j2), T56: ('RR+', tp), E1: ('RR+', erp)})
    cl.atom(T56); cl.atom(E1)
    F = '( ! ` ( J + 1 ) )'
    fnn = d('faccld', [j1], '%s e. NN' % F); fr = d('nnred', [fnn], '%s e. RR' % F)
    cl.leaf(F, 'RR+', d('nnrpd', [fnn], '%s e. RR+' % F))
    EXPN = '( exp ` -u ( 8 x. %s ) )' % M6
    cl.leaf(EXPN, 'RR+', d('rpefcld' if False else 'syl', [cl.mem('-u ( 8 x. %s )' % M6, 'RR'), w.inst('rpefcl')], '%s e. RR+' % EXPN))
    K = '( J + 1 )'; U2 = '( E / 2 )'
    NUM = '( ( %s x. %s ) x. ( ( 5 / 4 ) x. ( %s + 2 ) ) )' % (F, E1, K)
    PeK = '( %s ^ ( %s + 1 ) )' % (U2, K); Pe = '( %s ^ ( J + 2 ) )' % U2
    X = '( %s x. %s )' % (EXPN, DG2(K, U2))
    Uc = '( %s ^ N )' % T56; P2 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    # exponent ( J + 1 ) + 1 = J + 2
    jc = d('nn0cnd', [jn], 'J e. CC')
    kk = d('eqtrd', [d('addassd', [jc, a1(w, A0, 'ax-1cn', '1 e. CC'), a1(w, A0, 'ax-1cn', '1 e. CC')], '( ( J + 1 ) + 1 ) = ( J + ( 1 + 1 ) )'),
                     d('oveq2d', [a1(w, A0, '1p1e2', '( 1 + 1 ) = 2')], '( J + ( 1 + 1 ) ) = ( J + 2 )')], '( ( J + 1 ) + 1 ) = ( J + 2 )')
    pk = d('oveq2d', [kk], '%s = %s' % (PeK, Pe))
    xq = d('oveq2d', [d('oveq2d', [pk], '( %s / %s ) = ( %s / %s )' % (NUM, PeK, NUM, Pe))], '%s = ( %s x. ( %s / %s ) )' % (X, EXPN, NUM, Pe))
    X2 = '( %s x. ( %s / %s ) )' % (EXPN, NUM, Pe)
    Q1 = '( %s / %s )' % (NUM, Pe)
    pep = cl.mem(Pe, 'RR+')
    cl4 = Closure(w, A0, {EXPN: ('CC', cl.mem(EXPN, 'CC')), Q1: ('CC', cl.mem(Q1, 'CC')), Uc: ('CC', cl.mem(Uc, 'CC')), P2: ('CC', cl.mem(P2, 'CC'))})
    for a in (EXPN, Q1, Uc, P2):
        cl4.atom(a)
    xd = d('oveq1d', [xq], '( %s x. %s ) = ( %s x. %s )' % (X, DEN, X2, DEN))
    M1 = '( ( ( 8 x. %s ) x. %s ) x. ( %s x. %s ) )' % (EXPN, Uc, Q1, P2)
    r1 = ringeq(w, A0, '( %s x. %s )' % (X2, DEN), M1, cl4)
    ZZ4 = '( %s / %s )' % (P2, Pe)
    r2 = d('div32d', [cl.mem(NUM, 'CC'), cl.mem(Pe, 'CC'), cl.mem(P2, 'CC'), cl.ne0(Pe)], '( %s x. %s ) = ( %s x. %s )' % (Q1, P2, NUM, ZZ4))
    # ZZ4 = 4 ^ ( J + 2 )
    z1 = d('expdivd', [cl.mem('( 2 x. E )', 'CC'), cl.mem(U2, 'CC'), cl.ne0(U2), j2], '( ( ( 2 x. E ) / %s ) ^ ( J + 2 ) ) = %s' % (U2, ZZ4))
    ec = d('rpcnd', [ep], 'E e. CC'); en = d('rpne0d', [ep], 'E =/= 0')
    z2 = d('divdiv2d', [cl.mem('( 2 x. E )', 'CC'), ec, a1(w, A0, '2cn', '2 e. CC'), en, a1(w, A0, '2ne0', '2 =/= 0')], '( ( 2 x. E ) / %s ) = ( ( ( 2 x. E ) x. 2 ) / E )' % U2)
    z3 = d('oveq1d', [ringeq(w, A0, '( ( 2 x. E ) x. 2 )', '( 4 x. E )', Closure(w, A0, {'E': ('CC', ec)}))], '( ( ( 2 x. E ) x. 2 ) / E ) = ( ( 4 x. E ) / E )')
    z4 = d('divcan4d', [a1(w, A0, '4cn', '4 e. CC'), ec, en], '( ( 4 x. E ) / E ) = 4')
    zz = chain(w, A0, ['( ( 2 x. E ) / %s )' % U2, '( ( ( 2 x. E ) x. 2 ) / E )', '( ( 4 x. E ) / E )', '4'], [z2, z3, z4])
    z5 = d('eqtr3d', [z1, d('oveq1d', [zz], '( ( ( 2 x. E ) / %s ) ^ ( J + 2 ) ) = ( 4 ^ ( J + 2 ) )' % U2)], '%s = ( 4 ^ ( J + 2 ) )' % ZZ4)
    P4 = '( 4 ^ ( J + 2 ) )'
    r3 = d('eqtrd', [r2, d('oveq2d', [z5], '( %s x. %s ) = ( %s x. %s )' % (NUM, ZZ4, NUM, P4))], '( %s x. %s ) = ( %s x. %s )' % (Q1, P2, NUM, P4))
    M2 = '( ( ( 8 x. %s ) x. %s ) x. ( %s x. %s ) )' % (EXPN, Uc, NUM, P4)
    r4 = d('oveq2d', [r3], '%s = %s' % (M1, M2))
    Y = '( ( ( ; 1 0 x. %s ) x. ( %s + 2 ) ) x. ( %s x. %s ) )' % (E1, K, Uc, P4)
    cl5 = Closure(w, A0, {EXPN: ('CC', cl.mem(EXPN, 'CC')), F: ('CC', cl.mem(F, 'CC')), E1: ('CC', cl.mem(E1, 'CC')), Uc: ('CC', cl.mem(Uc, 'CC')),
                          P4: ('CC', cl.mem(P4, 'CC')), 'J': ('CC', jc)})
    for a in (EXPN, F, E1, Uc, P4):
        cl5.atom(a)
    FIN = '( %s x. ( %s x. %s ) )' % (F, EXPN, Y)
    r5 = ringeq(w, A0, M2, FIN, cl5)
    xe = chain(w, A0, ['( %s x. %s )' % (X, DEN), '( %s x. %s )' % (X2, DEN), M1, M2, FIN], [xd, r1, r4, r5])
    # Y <_ exp ( 8 . 6 N )
    jr = d('nn0red', [jn], 'J e. RR')
    clr = Closure(w, A0, {'N': ('RR', nr), 'J': ('RR', jr)})
    y1 = linarith(w, A0, [j7, d('nnge1d', [nn], '1 <_ N')], '( %s + 2 ) <_ ( 8 x. N )' % K, closure=clr)
    n7 = d('nn0mulcld', [a1(w, A0, '7nn0', '7 e. NN0'), nn0], '( 7 x. N ) e. NN0')
    u7 = uz(w, A0, '( J + 2 )', '( 7 x. N )', d('nn0zd', [j2], '( J + 2 ) e. ZZ'), d('nn0zd', [n7], '( 7 x. N ) e. ZZ'), j7)
    y2 = d('leexp2ad', [a1(w, A0, '4re', '4 e. RR'), a1(w, A0, '1le4' if False else 'idi', '1 <_ 4') if False else w.s([num.le_nat(w, 1, 4)], 'a1i', '( %s -> 1 <_ 4 )' % A0), u7],
           '%s <_ ( 4 ^ ( 7 x. N ) )' % P4)
    y3 = d('expmuld', [a1(w, A0, '4cn', '4 e. CC'), nn0, a1(w, A0, '7nn0', '7 e. NN0')], '( 4 ^ ( 7 x. N ) ) = ( ( 4 ^ 7 ) ^ N )')
    C16 = '; ; ; ; 1 6 3 8 4'
    y4 = d('oveq1d', [w.s([numpow(w, 4, 7)], 'a1i', '( %s -> ( 4 ^ 7 ) = %s )' % (A0, C16))], '( ( 4 ^ 7 ) ^ N ) = ( %s ^ N )' % C16)
    y5 = d('breqtrd', [d('breqtrd', [y2, y3], '%s <_ ( ( 4 ^ 7 ) ^ N )' % P4), y4], '%s <_ ( %s ^ N )' % (P4, C16))
    ur = cl.mem(Uc, 'RR'); u0 = cl.ge0(Uc)
    y6 = d('lemul2ad', [cl.mem(P4, 'RR'), cl.mem('( %s ^ N )' % C16, 'RR'), ur, u0, y5], '( %s x. %s ) <_ ( %s x. ( %s ^ N ) )' % (Uc, P4, Uc, C16))
    TA = '( %s x. %s )' % (T56, C16)
    y7 = d('mulexpd', [cl.mem(T56, 'CC'), cl.mem(C16, 'CC'), nn0], '( %s ^ N ) = ( %s x. ( %s ^ N ) )' % (TA, Uc, C16))
    y8 = d('breqtrrd', [y6, y7], '( %s x. %s ) <_ ( %s ^ N )' % (Uc, P4, TA))
    E10 = '( ; 1 0 x. %s )' % E1
    y9 = d('lemul2ad', [cl.mem('( %s + 2 )' % K, 'RR'), cl.mem('( 8 x. N )', 'RR'), cl.mem(E10, 'RR'), cl.ge0(E10), y1],
           '( %s x. ( %s + 2 ) ) <_ ( %s x. ( 8 x. N ) )' % (E10, K, E10))
    y10 = d('lemul12ad', [cl.mem('( %s x. ( %s + 2 ) )' % (E10, K), 'RR'), cl.mem('( %s x. ( 8 x. N ) )' % E10, 'RR'), cl.mem('( %s x. %s )' % (Uc, P4), 'RR'),
                          cl.mem('( %s ^ N )' % TA, 'RR'), cl.ge0('( %s x. ( %s + 2 ) )' % (E10, K)), cl.ge0('( %s x. %s )' % (Uc, P4)), y9, y8],
            '%s <_ ( ( %s x. ( 8 x. N ) ) x. ( %s ^ N ) )' % (Y, E10, TA))
    E80 = '( ; 8 0 x. %s )' % E1
    cl6 = Closure(w, A0, {E1: ('CC', cl.mem(E1, 'CC')), 'N': ('CC', d('nncnd', [nn], 'N e. CC')), '( %s ^ N )' % TA: ('CC', cl.mem('( %s ^ N )' % TA, 'CC'))})
    cl6.atom(E1); cl6.atom('( %s ^ N )' % TA)
    y11 = ringeq(w, A0, '( ( %s x. ( 8 x. N ) ) x. ( %s ^ N ) )' % (E10, TA), '( N x. ( %s x. ( %s ^ N ) ) )' % (E80, TA), cl6)
    # 80 e <_ ( 80 e )^N
    e80r = cl.mem(E80, 'RR')
    cle = Closure(w, A0, {E1: ('RR', cl.mem(E1, 'RR'))}); cle.atom(E1)
    e801 = linarith(w, A0, [eg2], '1 <_ %s' % E80, closure=cle)
    u1 = uz(w, A0, '1', 'N', a1(w, A0, '1z', '1 e. ZZ'), nz, d('nnge1d', [nn], '1 <_ N'))
    y12 = d('breqtrrd', [d('leexp2ad', [e80r, e801, u1], '( %s ^ 1 ) <_ ( %s ^ N )' % (E80, E80)), d('exp1d', [cl.mem(E80, 'CC')], '( %s ^ 1 ) = %s' % (E80, E80))],
            '%s <_ ( %s ^ N )' % (E80, E80)) if False else \
        d('eqbrtrrd', [d('exp1d', [cl.mem(E80, 'CC')], '( %s ^ 1 ) = %s' % (E80, E80)), d('leexp2ad', [e80r, e801, u1], '( %s ^ 1 ) <_ ( %s ^ N )' % (E80, E80))],
          '%s <_ ( %s ^ N )' % (E80, E80))
    y13 = d('lemul1ad', [e80r, cl.mem('( %s ^ N )' % E80, 'RR'), cl.mem('( %s ^ N )' % TA, 'RR'), cl.ge0('( %s ^ N )' % TA), y12],
            '( %s x. ( %s ^ N ) ) <_ ( ( %s ^ N ) x. ( %s ^ N ) )' % (E80, TA, E80, TA))
    AA = '( %s x. %s )' % (E80, TA)
    y14 = d('mulexpd', [cl.mem(E80, 'CC'), cl.mem(TA, 'CC'), nn0], '( %s ^ N ) = ( ( %s ^ N ) x. ( %s ^ N ) )' % (AA, E80, TA))
    y15 = d('breqtrrd', [y13, y14], '( %s x. ( %s ^ N ) ) <_ ( %s ^ N )' % (E80, TA, AA))
    y16 = d('lemul2ad', [cl.mem('( %s x. ( %s ^ N ) )' % (E80, TA), 'RR'), cl.mem('( %s ^ N )' % AA, 'RR'), nr, d('nn0ge0d', [nn0], '0 <_ N'), y15],
            '( N x. ( %s x. ( %s ^ N ) ) ) <_ ( N x. ( %s ^ N ) )' % (E80, TA, AA))
    aar = cl.mem(AA, 'RR')
    y17 = d('syl3anc', [d('jca', [aar, cl.ge0(AA)], '( %s e. RR /\\ 0 <_ %s )' % (AA, AA)),
                        d('jca', [cl.mem('( 2 x. %s )' % AA, 'RR'), d('leidd', [cl.mem('( 2 x. %s )' % AA, 'RR')], '( 2 x. %s ) <_ ( 2 x. %s )' % (AA, AA))],
                          '( ( 2 x. %s ) e. RR /\\ ( 2 x. %s ) <_ ( 2 x. %s ) )' % (AA, AA, AA)), nn0, w.inst('kd2nmul')],
          '( N x. ( %s ^ N ) ) <_ ( ( 2 x. %s ) ^ N )' % (AA, AA))
    # 2 AA <_ ( exp 1 )^48
    E2 = '( %s ^ 2 )' % E1
    cl7 = Closure(w, A0, {E1: ('CC', cl.mem(E1, 'CC')), E2: ('CC', cl.mem(E2, 'CC'))}); cl7.atom(E1); cl7.atom(E2)
    sq = d('sqvald', [cl.mem(E1, 'CC')], '%s = ( %s x. %s )' % (E2, E1, E1))
    CBIG = '; ; ; ; ; ; ; ; 1 4 6 8 0 0 6 4 0'
    t1 = ringeq(w, A0, '( 2 x. %s )' % AA, '( %s x. ( %s x. %s ) )' % (CBIG, E1, E1), cl7)
    t2 = d('eqtr4d', [t1, d('oveq2d', [sq], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (CBIG, E2, CBIG, E1, E1))], '( 2 x. %s ) = ( %s x. %s )' % (AA, CBIG, E2))
    e29 = d('breqtrd', [d('leexp1ad', [cl.mem(E1, 'RR'), a1(w, A0, '3re', '3 e. RR'), a1(w, A0, '2nn0', '2 e. NN0'), cl.ge0(E1), el3], '%s <_ ( 3 ^ 2 )' % E2),
                        w.s([w.s([], 'sq3', '( 3 ^ 2 ) = 9')], 'a1i', '( %s -> ( 3 ^ 2 ) = 9 )' % A0)], '%s <_ 9' % E2)
    t3 = d('lemul2ad', [cl.mem(E2, 'RR'), a1(w, A0, '9re', '9 e. RR'), cl.mem(CBIG, 'RR'), cl.ge0(CBIG), e29], '( %s x. %s ) <_ ( %s x. 9 )' % (CBIG, E2, CBIG))
    CB9 = num.nat_text(146800640 * 9)
    t4 = d('breqtrd', [t3, w.s([num.mul_nat(w, 146800640, 9)], 'a1i', '( %s -> ( %s x. 9 ) = %s )' % (A0, CBIG, CB9))], '( %s x. %s ) <_ %s' % (CBIG, E2, CB9))
    P31 = numpow(w, 2, 31)
    C31 = num.nat_text(2 ** 31)
    t5 = w.s([w.s([num.le_nat(w, 146800640 * 9, 2 ** 31), P31], 'breqtrri', '%s <_ ( 2 ^ ; 3 1 )' % CB9)], 'a1i', '( %s -> %s <_ ( 2 ^ ; 3 1 ) )' % (A0, CB9))
    n31 = w.s([num.nn0(w, 31)], 'a1i', '( %s -> ; 3 1 e. NN0 )' % A0)
    t6 = d('leexp1ad', [a1(w, A0, '2re', '2 e. RR'), cl.mem(E1, 'RR'), n31, a1(w, A0, '0le2', '0 <_ 2'), eg2], '( 2 ^ ; 3 1 ) <_ ( %s ^ ; 3 1 )' % E1)
    cle2 = Closure(w, A0, {E1: ('RR', cl.mem(E1, 'RR'))}); cle2.atom(E1)
    e1le = linarith(w, A0, [eg2], '1 <_ %s' % E1, closure=cle2)
    u31 = uz(w, A0, '; 3 1', '; 4 8', w.s([num.z_nat(w, 31)], 'a1i', '( %s -> ; 3 1 e. ZZ )' % A0), w.s([num.z_nat(w, 48)], 'a1i', '( %s -> ; 4 8 e. ZZ )' % A0),
             w.s([num.le_nat(w, 31, 48)], 'a1i', '( %s -> ; 3 1 <_ ; 4 8 )' % A0))
    t7 = d('leexp2ad', [cl.mem(E1, 'RR'), e1le, u31], '( %s ^ ; 3 1 ) <_ ( %s ^ ; 4 8 )' % (E1, E1))
    cl.have('( 2 ^ ; 3 1 )', 'RR', cl.mem('( 2 ^ ; 3 1 )', 'RR'))
    E48 = '( %s ^ ; 4 8 )' % E1
    tA = d('eqbrtrd', [t2, t4], '( 2 x. %s ) <_ %s' % (AA, CB9))
    tB = d('letrd', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem(CB9, 'RR'), cl.mem('( 2 ^ ; 3 1 )', 'RR'), tA, t5], '( 2 x. %s ) <_ ( 2 ^ ; 3 1 )' % AA)
    tC = d('letrd', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem('( 2 ^ ; 3 1 )', 'RR'), cl.mem('( %s ^ ; 3 1 )' % E1, 'RR'), tB, t6], '( 2 x. %s ) <_ ( %s ^ ; 3 1 )' % (AA, E1))
    tD = d('letrd', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem('( %s ^ ; 3 1 )' % E1, 'RR'), cl.mem(E48, 'RR'), tC, t7], '( 2 x. %s ) <_ %s' % (AA, E48))
    y18 = d('leexp1ad', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem(E48, 'RR'), nn0, cl.ge0('( 2 x. %s )' % AA), tD], '( ( 2 x. %s ) ^ N ) <_ ( %s ^ N )' % (AA, E48))
    # ( e^48 )^N = exp ( 8 . 6 N )
    f1 = efkn(w, A0, '; 4 8', nz)
    f2 = d('oveq1d', [efk(w, A0, '; 4 8')], '( ( exp ` ; 4 8 ) ^ N ) = ( %s ^ N )' % E48)
    f3 = ringeq(w, A0, '( 8 x. %s )' % M6, '( ; 4 8 x. N )', Closure(w, A0, {'N': ('CC', d('nncnd', [nn], 'N e. CC'))}))
    EP = '( exp ` ( 8 x. %s ) )' % M6
    f4 = d('fveq2d', [f3], '%s = ( exp ` ( ; 4 8 x. N ) )' % EP)
    ff = chain(w, A0, [EP, '( exp ` ( ; 4 8 x. N ) )', '( ( exp ` ; 4 8 ) ^ N )', '( %s ^ N )' % E48], [f4, f1, f2])
    # Y <_ EP
    YA = '( ( %s x. ( 8 x. N ) ) x. ( %s ^ N ) )' % (E10, TA)
    k1 = d('breqtrd', [y10, y11], '%s <_ ( N x. ( %s x. ( %s ^ N ) ) )' % (Y, E80, TA))
    k2 = d('letrd', [cl.mem(Y, 'RR'), cl.mem('( N x. ( %s x. ( %s ^ N ) ) )' % (E80, TA), 'RR'), cl.mem('( N x. ( %s ^ N ) )' % AA, 'RR'), k1, y16], '%s <_ ( N x. ( %s ^ N ) )' % (Y, AA))
    k3 = d('letrd', [cl.mem(Y, 'RR'), cl.mem('( N x. ( %s ^ N ) )' % AA, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AA, 'RR'), k2, y17], '%s <_ ( ( 2 x. %s ) ^ N )' % (Y, AA))
    k4 = d('letrd', [cl.mem(Y, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AA, 'RR'), cl.mem('( %s ^ N )' % E48, 'RR'), k3, y18], '%s <_ ( %s ^ N )' % (Y, E48))
    k5 = d('breqtrrd', [k4, ff], '%s <_ %s' % (Y, EP))
    # EXPN . Y <_ 1
    k6 = d('lemul2ad', [cl.mem(Y, 'RR'), cl.mem(EP, 'RR'), cl.mem(EXPN, 'RR'), cl.ge0(EXPN), k5], '( %s x. %s ) <_ ( %s x. %s )' % (EXPN, Y, EXPN, EP))
    ea = d('syl2anc', [cl.mem('-u ( 8 x. %s )' % M6, 'CC'), cl.mem('( 8 x. %s )' % M6, 'CC'), w.inst('efadd')],
           '( exp ` ( -u ( 8 x. %s ) + ( 8 x. %s ) ) ) = ( %s x. %s )' % (M6, M6, EXPN, EP))
    z0 = d('fveq2d', [ringeq(w, A0, '( -u ( 8 x. %s ) + ( 8 x. %s ) )' % (M6, M6), '0', Closure(w, A0, {'N': ('CC', d('nncnd', [nn], 'N e. CC'))}))],
           '( exp ` ( -u ( 8 x. %s ) + ( 8 x. %s ) ) ) = ( exp ` 0 )' % (M6, M6))
    e01 = d('eqtr3d', [ea, d('eqtrd', [z0, a1(w, A0, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( -u ( 8 x. %s ) + ( 8 x. %s ) ) ) = 1' % (M6, M6))],
            '( %s x. %s ) = 1' % (EXPN, EP))
    k7 = d('breqtrd', [k6, e01], '( %s x. %s ) <_ 1' % (EXPN, Y))
    k8 = d('lemul2ad', [cl.mem('( %s x. %s )' % (EXPN, Y), 'RR'), a1(w, A0, '1re', '1 e. RR'), fr, d('nnge1d' if False else 'nn0ge0d', [d('nnnn0d', [fnn], '%s e. NN0' % F)], '0 <_ %s' % F), k7],
           '%s <_ ( %s x. 1 )' % (FIN, F))
    k9 = d('breqtrd', [k8, d('mulridd', [cl.mem(F, 'CC')], '( %s x. 1 ) = %s' % (F, F))], '%s <_ %s' % (FIN, F))
    k10 = d('eqbrtrd', [xe, k9], '( %s x. %s ) <_ %s' % (X, DEN, F))
    b = q8le(w, A0, X, cl.mem(X, 'RR'), ep, nn0, jn, F=F, fr=fr)
    fin = d('mpbird', [k10, b], '%s <_ %s' % (X, FQ8()))
    w.qed([fin], 'idi', S['kd2bhigh'])
    return only_run(w, only)


E1_ = '( exp ` 1 )'


def epow(k): return '( %s ^ %s )' % (E1_, k)


def two_le_e(w, A, k, eg2, cl):
    """( A -> ( 2 ^ k ) <_ ( e ^ k ) ), k numeral"""
    kn = w.s([num.nn0(w, int(num.nat_value(k)))], 'a1i', '( %s -> %s e. NN0 )' % (A, k))
    return D(w, A, 'leexp1ad', [a1(w, A, '2re', '2 e. RR'), cl.mem(E1_, 'RR'), kn, a1(w, A, '0le2', '0 <_ 2'), eg2], '( 2 ^ %s ) <_ %s' % (k, epow(k)))


def eadd(w, A, k1, k2, cl):
    """( A -> ( ( e ^ k1 ) x. ( e ^ k2 ) ) = ( e ^ k3 ) )"""
    v1, v2 = int(num.nat_value(k1)), int(num.nat_value(k2)); k3 = num.nat_text(v1 + v2)
    e = D(w, A, 'expaddd', [cl.mem(E1_, 'CC'), w.s([num.nn0(w, v2)], 'a1i', '( %s -> %s e. NN0 )' % (A, k2)), w.s([num.nn0(w, v1)], 'a1i', '( %s -> %s e. NN0 )' % (A, k1))],
          '( %s ^ ( %s + %s ) ) = ( %s x. %s )' % (E1_, k1, k2, epow(k1), epow(k2)))
    s_ = w.s([num.add_nat(w, v1, v2)], 'a1i', '( %s -> ( %s + %s ) = %s )' % (A, k1, k2, k3))
    return D(w, A, 'eqtr3d', [D(w, A, 'oveq2d', [s_], '( %s ^ ( %s + %s ) ) = %s' % (E1_, k1, k2, epow(k3))), e], '( %s x. %s ) = %s' % (epow(k1), epow(k2), epow(k3)))


def ele(w, A, k1, k2, cl, e1le):
    """( A -> ( e ^ k1 ) <_ ( e ^ k2 ) ) for numerals k1 <= k2"""
    v1, v2 = int(num.nat_value(k1)), int(num.nat_value(k2))
    u = uz(w, A, k1, k2, w.s([num.z_nat(w, v1)], 'a1i', '( %s -> %s e. ZZ )' % (A, k1)), w.s([num.z_nat(w, v2)], 'a1i', '( %s -> %s e. ZZ )' % (A, k2)),
           w.s([num.le_nat(w, v1, v2)], 'a1i', '( %s -> %s <_ %s )' % (A, k1, k2)))
    return D(w, A, 'leexp2ad', [cl.mem(E1_, 'RR'), e1le, u], '%s <_ %s' % (epow(k1), epow(k2)))


def gen_bbd():
    w = W('kd2bbd', 'Lean ` KDerivDetect.budget_boundary ` at the Metamath constants (window bound ` e ( ( 5 / 4 ) log X2 + 5 ) ` of ~ kd2wb for Lean ` e ( log X2 + 2 ) ` ): ` 328 M e T^N ( 32 e )^(j+1) <_ N ( 1968 e T ( 32 e )^7 )^N <_ e^(16 M) ` .')
    A0 = ante('kd2bbd', '( ( ( %s' % X2L)
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    bp = bhparts(w, A0, d('simpl', [], BH))
    ep, e5, nn, jn, ix = bp['ep'], bp['e5'], bp['nn'], bp['jn'], bp['ix']
    j7 = d('simpr', [], '( J + 2 ) <_ ( 7 x. N )')
    nn0 = d('nnnn0d', [nn], 'N e. NN0'); nr = d('nnred', [nn], 'N e. RR'); nz = d('nnzd', [nn], 'N e. ZZ')
    tp, tlt = tc(w, A0)
    er = d('rpred', [ep], 'E e. RR')
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    erp, eg2, el3 = eparts(w, A0)
    E1 = E1_
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), '( J + 1 )': ('NN0', j1), T56: ('RR+', tp), E1: ('RR+', erp)})
    cl.atom(T56); cl.atom(E1)
    F = '( ! ` ( J + 1 ) )'
    fnn = d('faccld', [j1], '%s e. NN' % F); fr = d('nnred', [fnn], '%s e. RR' % F)
    EXP16 = '( exp ` -u ( ; 1 6 x. %s ) )' % M6
    cl.leaf(EXP16, 'RR+', d('syl', [cl.mem('-u ( ; 1 6 x. %s )' % M6, 'RR'), w.inst('rpefcl')], '%s e. RR+' % EXP16))
    X2LJ = '( %s ^ ( J + 1 ) )' % X2L
    BX = '( %s x. ( ( ( 5 / 4 ) x. %s ) + 5 ) )' % (E1, X2L)
    X = '( ( %s x. %s ) x. %s )' % (X2LJ, EXP16, BX)
    Uc = '( %s ^ N )' % T56; P1 = '( ( 2 x. E ) ^ ( J + 1 ) )'
    up = cl.mem(Uc, 'RR+')
    E22 = '( ( 2 x. E ) ^ ( J + 2 ) )'
    e2, _ = pow2(w, A0, jn, cl.mem('( 2 x. E )', 'CC'), '( 2 x. E )')
    DEN2 = '( ( 8 x. %s ) x. ( %s x. ( 2 x. E ) ) )' % (Uc, P1)
    xd = d('oveq2d', [d('oveq2d', [e2], '( ( 8 x. %s ) x. %s ) = %s' % (Uc, E22, DEN2))], '( %s x. %s ) = ( %s x. %s )' % (X, DEN, X, DEN2))
    cl4 = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), Uc: ('CC', cl.mem(Uc, 'CC')), P1: ('CC', cl.mem(P1, 'CC')), X2LJ: ('CC', cl.mem(X2LJ, 'CC')),
                          X2L: ('CC', cl.mem(X2L, 'CC')), EXP16: ('CC', cl.mem(EXP16, 'CC')), E1: ('CC', cl.mem(E1, 'CC'))})
    for a in (Uc, P1, X2LJ, X2L, EXP16, E1):
        cl4.atom(a)
    TAIL = '( ( 8 x. %s ) x. ( %s x. %s ) )' % (E1, Uc, EXP16)
    MID = '( ( %s x. %s ) x. ( ( ( 2 x. E ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) ) x. %s ) )' % (X2LJ, P1, X2L, TAIL)
    rq = ringeq(w, A0, '( %s x. %s )' % (X, DEN2), MID, cl4)
    MM_ = M6
    H = '( ; 3 2 x. %s )' % MM_
    gp = d('mulexpd', [cl.mem(X2L, 'CC'), cl.mem('( 2 x. E )', 'CC'), j1], '( ( %s x. ( 2 x. E ) ) ^ ( J + 1 ) ) = ( %s x. %s )' % (X2L, X2LJ, P1))
    ec = d('rpcnd', [ep], 'E e. CC'); en = d('rpne0d', [ep], 'E =/= 0')
    N16 = '( ; 1 6 x. %s )' % MM_
    g1 = d('div23d', [cl.mem(N16, 'CC'), cl.mem('( 2 x. E )', 'CC'), ec, en], '( ( %s x. ( 2 x. E ) ) / E ) = ( %s x. ( 2 x. E ) )' % (N16, X2L))
    cl6 = Closure(w, A0, {'E': ('CC', ec), 'N': ('CC', d('nncnd', [nn], 'N e. CC'))})
    g2 = d('oveq1d', [ringeq(w, A0, '( %s x. ( 2 x. E ) )' % N16, '( %s x. E )' % H, cl6)], '( ( %s x. ( 2 x. E ) ) / E ) = ( ( %s x. E ) / E )' % (N16, H))
    g3 = d('divcan4d', [cl.mem(H, 'CC'), ec, en], '( ( %s x. E ) / E ) = %s' % (H, H))
    gg = chain(w, A0, ['( %s x. ( 2 x. E ) )' % X2L, '( ( %s x. ( 2 x. E ) ) / E )' % N16, '( ( %s x. E ) / E )' % H, H], [('r', g1), g2, g3])
    HJ = '( %s ^ ( J + 1 ) )' % H
    gh = d('eqtr3d', [gp, d('oveq1d', [gg], '( ( %s x. ( 2 x. E ) ) ^ ( J + 1 ) ) = %s' % (X2L, HJ))], '( %s x. %s ) = %s' % (X2LJ, P1, HJ))
    a1_ = ringeq(w, A0, '( ( 2 x. E ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) )' % X2L, '( ( ( 5 / 4 ) x. ( %s x. ( 2 x. E ) ) ) + ( ; 1 0 x. E ) )' % X2L, cl4)
    a2_ = d('oveq1d', [d('oveq2d', [gg], '( ( 5 / 4 ) x. ( %s x. ( 2 x. E ) ) ) = ( ( 5 / 4 ) x. %s )' % (X2L, H))],
            '( ( ( 5 / 4 ) x. ( %s x. ( 2 x. E ) ) ) + ( ; 1 0 x. E ) ) = ( ( ( 5 / 4 ) x. %s ) + ( ; 1 0 x. E ) )' % (X2L, H))
    B2 = '( ( ( 5 / 4 ) x. %s ) + ( ; 1 0 x. E ) )' % H
    aa = d('eqtrd', [a1_, a2_], '( ( 2 x. E ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) ) = %s' % (X2L, B2))
    XV = '( %s x. ( %s x. %s ) )' % (HJ, B2, TAIL)
    xe1 = d('oveq12d', [gh, d('oveq1d', [aa], '( ( ( 2 x. E ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) ) x. %s ) = ( %s x. %s )' % (X2L, TAIL, B2, TAIL))], '%s = %s' % (MID, XV))
    xe = chain(w, A0, ['( %s x. %s )' % (X, DEN), '( %s x. %s )' % (X, DEN2), MID, XV], [xd, rq, xe1])
    # B2 . TAIL <_ V = ( ( ; 4 1 x. MM ) x. TAIL )
    tlr = cl.mem(TAIL, 'RR'); tl0 = cl.ge0(TAIL)
    clb = Closure(w, A0, {'E': ('RR', er), 'N': ('RR', nr)})
    b1 = linarith(w, A0, [e5, d('nnge1d', [nn], '1 <_ N')], '%s <_ ( ; 4 1 x. %s )' % (B2, MM_), closure=clb)
    V = '( ( ; 4 1 x. %s ) x. %s )' % (MM_, TAIL)
    b2 = d('lemul1ad', [clb.mem(B2, 'RR'), clb.mem('( ; 4 1 x. %s )' % MM_, 'RR'), tlr, tl0, b1], '( %s x. %s ) <_ %s' % (B2, TAIL, V))
    hr = cl.mem(HJ, 'RR'); h0 = cl.ge0(HJ)
    b3 = d('lemul2ad', [cl.mem('( %s x. %s )' % (B2, TAIL), 'RR'), cl.mem(V, 'RR'), hr, h0, b2], '%s <_ ( %s x. %s )' % (XV, HJ, V))
    # W6 = 328 MM e Uc ( 32 e )^(J+1) <_ exp ( 16 MM )
    E32 = '( ; 3 2 x. %s )' % E1
    C32J = '( %s ^ ( J + 1 ) )' % E32
    jr = d('nn0red', [jn], 'J e. RR')
    le7 = linarith(w, A0, [j7], '( J + 1 ) <_ ( 7 x. N )', closure=Closure(w, A0, {'N': ('RR', nr), 'J': ('RR', jr)}))
    n7 = d('nn0mulcld', [a1(w, A0, '7nn0', '7 e. NN0'), nn0], '( 7 x. N ) e. NN0')
    u7 = uz(w, A0, '( J + 1 )', '( 7 x. N )', d('nn0zd', [j1], '( J + 1 ) e. ZZ'), d('nn0zd', [n7], '( 7 x. N ) e. ZZ'), le7)
    cle = Closure(w, A0, {E1: ('RR', cl.mem(E1, 'RR'))}); cle.atom(E1)
    e1le = linarith(w, A0, [eg2], '1 <_ %s' % E1, closure=cle)
    e321 = linarith(w, A0, [eg2], '1 <_ %s' % E32, closure=cle)
    w1 = d('leexp2ad', [cl.mem(E32, 'RR'), e321, u7], '%s <_ ( %s ^ ( 7 x. N ) )' % (C32J, E32))
    w2 = d('expmuld', [cl.mem(E32, 'CC'), nn0, a1(w, A0, '7nn0', '7 e. NN0')], '( %s ^ ( 7 x. N ) ) = ( ( %s ^ 7 ) ^ N )' % (E32, E32))
    B7_ = '( %s ^ 7 )' % E32
    w3 = d('breqtrd', [w1, w2], '%s <_ ( %s ^ N )' % (C32J, B7_))
    E1968 = '( ; ; ; 1 9 6 8 x. %s )' % E1
    W6 = '( ( ( ; ; 3 2 8 x. %s ) x. %s ) x. ( %s x. %s ) )' % (MM_, E1, Uc, C32J)
    c0 = cl.mem('( ( ; ; 3 2 8 x. %s ) x. %s )' % (MM_, E1), 'RR')
    w4 = d('lemul2ad', [cl.mem(C32J, 'RR'), cl.mem('( %s ^ N )' % B7_, 'RR'), cl.mem(Uc, 'RR'), cl.ge0(Uc), w3], '( %s x. %s ) <_ ( %s x. ( %s ^ N ) )' % (Uc, C32J, Uc, B7_))
    w5 = d('lemul2ad', [cl.mem('( %s x. %s )' % (Uc, C32J), 'RR'), cl.mem('( %s x. ( %s ^ N ) )' % (Uc, B7_), 'RR'), c0, cl.ge0('( ( ; ; 3 2 8 x. %s ) x. %s )' % (MM_, E1)), w4],
           '%s <_ ( ( ( ; ; 3 2 8 x. %s ) x. %s ) x. ( %s x. ( %s ^ N ) ) )' % (W6, MM_, E1, Uc, B7_))
    cl7 = Closure(w, A0, {E1: ('CC', cl.mem(E1, 'CC')), 'N': ('CC', d('nncnd', [nn], 'N e. CC')), Uc: ('CC', cl.mem(Uc, 'CC')), '( %s ^ N )' % B7_: ('CC', cl.mem('( %s ^ N )' % B7_, 'CC'))})
    for a in (E1, Uc, '( %s ^ N )' % B7_):
        cl7.atom(a)
    W7 = '( N x. ( %s x. ( %s x. ( %s ^ N ) ) ) )' % (E1968, Uc, B7_)
    w6 = ringeq(w, A0, '( ( ( ; ; 3 2 8 x. %s ) x. %s ) x. ( %s x. ( %s ^ N ) ) )' % (MM_, E1, Uc, B7_), W7, cl7)
    e19r = cl.mem(E1968, 'RR')
    e191 = linarith(w, A0, [eg2], '1 <_ %s' % E1968, closure=cle)
    u1 = uz(w, A0, '1', 'N', a1(w, A0, '1z', '1 e. ZZ'), nz, d('nnge1d', [nn], '1 <_ N'))
    w7 = d('eqbrtrrd', [d('exp1d', [cl.mem(E1968, 'CC')], '( %s ^ 1 ) = %s' % (E1968, E1968)), d('leexp2ad', [e19r, e191, u1], '( %s ^ 1 ) <_ ( %s ^ N )' % (E1968, E1968))],
           '%s <_ ( %s ^ N )' % (E1968, E1968))
    RST = '( %s x. ( %s ^ N ) )' % (Uc, B7_)
    w8 = d('lemul1ad', [e19r, cl.mem('( %s ^ N )' % E1968, 'RR'), cl.mem(RST, 'RR'), cl.ge0(RST), w7], '( %s x. %s ) <_ ( ( %s ^ N ) x. %s )' % (E1968, RST, E1968, RST))
    AA = '( ( %s x. %s ) x. %s )' % (E1968, T56, B7_)
    m1 = d('mulexpd', [cl.mem('( %s x. %s )' % (E1968, T56), 'CC'), cl.mem(B7_, 'CC'), nn0], '( %s ^ N ) = ( ( ( %s x. %s ) ^ N ) x. ( %s ^ N ) )' % (AA, E1968, T56, B7_))
    m2 = d('mulexpd', [cl.mem(E1968, 'CC'), cl.mem(T56, 'CC'), nn0], '( ( %s x. %s ) ^ N ) = ( ( %s ^ N ) x. %s )' % (E1968, T56, E1968, Uc))
    cl8 = Closure(w, A0, {'( %s ^ N )' % E1968: ('CC', cl.mem('( %s ^ N )' % E1968, 'CC')), Uc: ('CC', cl.mem(Uc, 'CC')), '( %s ^ N )' % B7_: ('CC', cl.mem('( %s ^ N )' % B7_, 'CC'))})
    for a in ('( %s ^ N )' % E1968, Uc, '( %s ^ N )' % B7_):
        cl8.atom(a)
    m3 = d('eqtrd', [m1, d('oveq1d', [m2], '( ( ( %s x. %s ) ^ N ) x. ( %s ^ N ) ) = ( ( ( %s ^ N ) x. %s ) x. ( %s ^ N ) )' % (E1968, T56, B7_, E1968, Uc, B7_))],
           '( %s ^ N ) = ( ( ( %s ^ N ) x. %s ) x. ( %s ^ N ) )' % (AA, E1968, Uc, B7_))
    m4 = ringeq(w, A0, '( ( ( %s ^ N ) x. %s ) x. ( %s ^ N ) )' % (E1968, Uc, B7_), '( ( %s ^ N ) x. %s )' % (E1968, RST), cl8)
    w9 = d('breqtrrd', [w8, d('eqtrd', [m3, m4], '( %s ^ N ) = ( ( %s ^ N ) x. %s )' % (AA, E1968, RST))], '( %s x. %s ) <_ ( %s ^ N )' % (E1968, RST, AA))
    w10 = d('lemul2ad', [cl.mem('( %s x. %s )' % (E1968, RST), 'RR'), cl.mem('( %s ^ N )' % AA, 'RR'), nr, d('nn0ge0d', [nn0], '0 <_ N'), w9],
            '%s <_ ( N x. ( %s ^ N ) )' % (W7, AA))
    aar = cl.mem(AA, 'RR')
    w11 = d('syl3anc', [d('jca', [aar, cl.ge0(AA)], '( %s e. RR /\\ 0 <_ %s )' % (AA, AA)),
                        d('jca', [cl.mem('( 2 x. %s )' % AA, 'RR'), d('leidd', [cl.mem('( 2 x. %s )' % AA, 'RR')], '( 2 x. %s ) <_ ( 2 x. %s )' % (AA, AA))],
                          '( ( 2 x. %s ) e. RR /\\ ( 2 x. %s ) <_ ( 2 x. %s )' % (AA, AA, AA) + ' )'), nn0, w.inst('kd2nmul')],
          '( N x. ( %s ^ N ) ) <_ ( ( 2 x. %s ) ^ N )' % (AA, AA))
    # 2 AA <_ e^96
    P327 = '( ; 3 2 ^ 7 )'
    q1 = d('mulexpd', [cl.mem('; 3 2', 'CC'), cl.mem(E1, 'CC'), a1(w, A0, '7nn0', '7 e. NN0')], '%s = ( %s x. %s )' % (B7_, P327, epow('7')))
    E2 = epow('2'); E7 = epow('7'); E9 = epow('9')
    cl9 = Closure(w, A0, {E1: ('CC', cl.mem(E1, 'CC')), P327: ('CC', cl.mem(P327, 'CC')), E7: ('CC', cl.mem(E7, 'CC')), E2: ('CC', cl.mem(E2, 'CC'))})
    for a in (E1, P327, E7, E2):
        cl9.atom(a)
    AA2 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (E1968, T56, P327, E7)
    q2 = d('oveq2d', [d('oveq2d', [q1], '( ( %s x. %s ) x. %s ) = %s' % (E1968, T56, B7_, AA2))], '( 2 x. %s ) = ( 2 x. %s )' % (AA, AA2))
    q3 = ringeq(w, A0, '( 2 x. %s )' % AA2, '( ; ; ; ; ; 2 2 0 4 1 6 x. ( %s x. ( ( %s x. %s ) x. %s ) ) )' % (P327, E1, E1, E7), cl9)
    q4 = d('oveq2d', [d('oveq1d', [d('sqvald', [cl.mem(E1, 'CC')], '%s = ( %s x. %s )' % (E2, E1, E1))], '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (E2, E7, E1, E1, E7))],
           '( %s x. ( %s x. %s ) ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (P327, E2, E7, P327, E1, E1, E7))
    q5 = eadd(w, A0, '2', '7', cl)
    C22 = '; ; ; ; ; 2 2 0 4 1 6'
    q6 = d('oveq2d', [d('oveq2d', [q5], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (P327, E2, E7, P327, E9))], '( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. ( %s x. %s ) )' % (C22, P327, E2, E7, C22, P327, E9))
    qq = chain(w, A0, ['( 2 x. %s )' % AA, '( 2 x. %s )' % AA2, '( %s x. ( %s x. ( ( %s x. %s ) x. %s ) ) )' % (C22, P327, E1, E1, E7),
                       '( %s x. ( %s x. ( %s x. %s ) ) )' % (C22, P327, E2, E7), '( %s x. ( %s x. %s ) )' % (C22, P327, E9)],
               [q2, q3, ('r', d('oveq2d', [q4], '( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. ( %s x. ( ( %s x. %s ) x. %s ) ) )' % (C22, P327, E2, E7, C22, P327, E1, E1, E7))), q6])
    # 220416 <_ e^18 ; 32^7 <_ e^35
    E18 = epow('; 1 8'); E35 = epow('; 3 5'); E5 = epow('5')
    r1 = w.s([w.s([num.le_nat(w, 220416, 262144), numpow(w, 2, 18)], 'breqtrri', '%s <_ ( 2 ^ ; 1 8 )' % C22)], 'a1i', '( %s -> %s <_ ( 2 ^ ; 1 8 ) )' % (A0, C22))
    r2 = d('letrd', [cl.mem(C22, 'RR'), cl.mem('( 2 ^ ; 1 8 )', 'RR'), cl.mem(E18, 'RR'), r1, two_le_e(w, A0, '; 1 8', eg2, cl)], '%s <_ %s' % (C22, E18))
    r3 = d('eqbrtrrd', [w.s([numpow(w, 2, 5)], 'a1i', '( %s -> ( 2 ^ 5 ) = ; 3 2 )' % A0), two_le_e(w, A0, '5', eg2, cl)], '; 3 2 <_ %s' % E5)
    r4 = d('leexp1ad', [cl.mem('; 3 2', 'RR'), cl.mem(E5, 'RR'), a1(w, A0, '7nn0', '7 e. NN0'), cl.ge0('; 3 2'), r3], '%s <_ ( %s ^ 7 )' % (P327, E5))
    r5 = d('expmuld', [cl.mem(E1, 'CC'), a1(w, A0, '7nn0', '7 e. NN0'), a1(w, A0, '5nn0', '5 e. NN0')], '( %s ^ ( 5 x. 7 ) ) = ( %s ^ 7 )' % (E1, E5))
    r6 = d('eqtr3d', [r5, d('oveq2d', [w.s([num.mul_nat(w, 5, 7)], 'a1i', '( %s -> ( 5 x. 7 ) = ; 3 5 )' % A0)], '( %s ^ ( 5 x. 7 ) ) = %s' % (E1, E35))],
           '( %s ^ 7 ) = %s' % (E5, E35))
    r7 = d('breqtrd', [r4, r6], '%s <_ %s' % (P327, E35))
    r8 = d('lemul1ad', [cl.mem(P327, 'RR'), cl.mem(E35, 'RR'), cl.mem(E9, 'RR'), cl.ge0(E9), r7], '( %s x. %s ) <_ ( %s x. %s )' % (P327, E9, E35, E9))
    E44 = epow('; 4 4'); E62 = epow('; 6 2'); E96 = epow('; 9 6')
    r9 = d('breqtrd', [r8, eadd(w, A0, '; 3 5', '9', cl)], '( %s x. %s ) <_ %s' % (P327, E9, E44))
    r10 = d('lemul12ad', [cl.mem(C22, 'RR'), cl.mem(E18, 'RR'), cl.mem('( %s x. %s )' % (P327, E9), 'RR'), cl.mem(E44, 'RR'), cl.ge0(C22), cl.ge0('( %s x. %s )' % (P327, E9)), r2, r9],
            '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (C22, P327, E9, E18, E44))
    r11 = d('breqtrd', [r10, eadd(w, A0, '; 1 8', '; 4 4', cl)], '( %s x. ( %s x. %s ) ) <_ %s' % (C22, P327, E9, E62))
    r12 = d('letrd', [cl.mem('( %s x. ( %s x. %s ) )' % (C22, P327, E9), 'RR'), cl.mem(E62, 'RR'), cl.mem(E96, 'RR'), r11, ele(w, A0, '; 6 2', '; 9 6', cl, e1le)],
            '( %s x. ( %s x. %s ) ) <_ %s' % (C22, P327, E9, E96))
    r13 = d('eqbrtrd', [qq, r12], '( 2 x. %s ) <_ %s' % (AA, E96))
    w12 = d('leexp1ad', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem(E96, 'RR'), nn0, cl.ge0('( 2 x. %s )' % AA), r13], '( ( 2 x. %s ) ^ N ) <_ ( %s ^ N )' % (AA, E96))
    EP = '( exp ` ( ; 1 6 x. %s ) )' % MM_
    f1 = efkn(w, A0, '; 9 6', nz)
    f2 = d('oveq1d', [efk(w, A0, '; 9 6')], '( ( exp ` ; 9 6 ) ^ N ) = ( %s ^ N )' % E96)
    f4 = d('fveq2d', [ringeq(w, A0, '( ; 1 6 x. %s )' % MM_, '( ; 9 6 x. N )', cl6)], '%s = ( exp ` ( ; 9 6 x. N ) )' % EP)
    ff = chain(w, A0, [EP, '( exp ` ( ; 9 6 x. N ) )', '( ( exp ` ; 9 6 ) ^ N )', '( %s ^ N )' % E96], [f4, f1, f2])
    k1 = d('breqtrd', [w5, w6], '%s <_ %s' % (W6, W7))
    k2 = d('letrd', [cl.mem(W6, 'RR'), cl.mem(W7, 'RR'), cl.mem('( N x. ( %s ^ N ) )' % AA, 'RR'), k1, w10], '%s <_ ( N x. ( %s ^ N ) )' % (W6, AA))
    k3 = d('letrd', [cl.mem(W6, 'RR'), cl.mem('( N x. ( %s ^ N ) )' % AA, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AA, 'RR'), k2, w11], '%s <_ ( ( 2 x. %s ) ^ N )' % (W6, AA))
    k4 = d('letrd', [cl.mem(W6, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AA, 'RR'), cl.mem('( %s ^ N )' % E96, 'RR'), k3, w12], '%s <_ ( %s ^ N )' % (W6, E96))
    k5 = d('breqtrrd', [k4, ff], '%s <_ %s' % (W6, EP))
    # V ( 32 e )^(J+1) <_ 1
    ea = d('syl2anc', [cl.mem('-u ( ; 1 6 x. %s )' % MM_, 'CC'), cl.mem('( ; 1 6 x. %s )' % MM_, 'CC'), w.inst('efadd')],
           '( exp ` ( -u ( ; 1 6 x. %s ) + ( ; 1 6 x. %s ) ) ) = ( %s x. %s )' % (MM_, MM_, EXP16, EP))
    z0 = d('fveq2d', [ringeq(w, A0, '( -u ( ; 1 6 x. %s ) + ( ; 1 6 x. %s ) )' % (MM_, MM_), '0', cl6)], '( exp ` ( -u ( ; 1 6 x. %s ) + ( ; 1 6 x. %s ) ) ) = ( exp ` 0 )' % (MM_, MM_))
    e01 = d('eqtr3d', [ea, d('eqtrd', [z0, a1(w, A0, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( -u ( ; 1 6 x. %s ) + ( ; 1 6 x. %s ) ) ) = 1' % (MM_, MM_))], '( %s x. %s ) = 1' % (EXP16, EP))
    VJ = '( %s x. %s )' % (V, C32J)
    cla = Closure(w, A0, {'N': ('CC', d('nncnd', [nn], 'N e. CC')), E1: ('CC', cl.mem(E1, 'CC')), Uc: ('CC', cl.mem(Uc, 'CC')), EXP16: ('CC', cl.mem(EXP16, 'CC')),
                          C32J: ('CC', cl.mem(C32J, 'CC'))})
    for a in (E1, Uc, EXP16, C32J):
        cla.atom(a)
    v1 = ringeq(w, A0, VJ, '( %s x. %s )' % (EXP16, W6), cla)
    v2 = d('lemul2ad', [cl.mem(W6, 'RR'), cl.mem(EP, 'RR'), cl.mem(EXP16, 'RR'), cl.ge0(EXP16), k5], '( %s x. %s ) <_ ( %s x. %s )' % (EXP16, W6, EXP16, EP))
    v3 = d('breqtrd', [d('eqbrtrd', [v1, v2], '%s <_ ( %s x. %s )' % (VJ, EXP16, EP)), e01], '%s <_ 1' % VJ)
    c32p = cl.mem(C32J, 'RR+')
    v4 = d('mpbid', [v3, d('lemuldivd', [cl.mem(V, 'RR'), a1(w, A0, '1re', '1 e. RR'), c32p], '( %s <_ 1 <-> %s <_ ( 1 / %s ) )' % (VJ, V, C32J))], '%s <_ ( 1 / %s )' % (V, C32J))
    IV = '( 1 / %s )' % E32
    v5 = d('exprecd', [cl.mem(E32, 'CC'), cl.ne0(E32), d('nn0zd', [j1], '( J + 1 ) e. ZZ')], '( %s ^ ( J + 1 ) ) = ( 1 / %s )' % (IV, C32J))
    v6 = d('breqtrrd', [v4, v5], '%s <_ ( %s ^ ( J + 1 ) )' % (V, IV))
    b4 = d('lemul2ad', [cl.mem(V, 'RR'), cl.mem('( %s ^ ( J + 1 ) )' % IV, 'RR'), hr, h0, v6], '( %s x. %s ) <_ ( %s x. ( %s ^ ( J + 1 ) ) )' % (HJ, V, HJ, IV))
    ME = '( %s / %s )' % (MM_, E1)
    h1 = d('mulexpd', [cl.mem(H, 'CC'), cl.mem(IV, 'CC'), j1], '( ( %s x. %s ) ^ ( J + 1 ) ) = ( %s x. ( %s ^ ( J + 1 ) ) )' % (H, IV, HJ, IV))
    h2 = d('divrecd', [cl.mem(H, 'CC'), cl.mem(E32, 'CC'), cl.ne0(E32)], '( %s / %s ) = ( %s x. %s )' % (H, E32, H, IV))
    h3 = d('divcan5d', [cl.mem(MM_, 'CC'), cl.mem(E1, 'CC'), cl.mem('; 3 2', 'CC'), cl.ne0(E1), cl.ne0('; 3 2')], '( %s / %s ) = %s' % (H, E32, ME))
    hh = d('eqtr3d', [h2, h3], '( %s x. %s ) = %s' % (H, IV, ME))
    h5 = d('eqtr3d', [h1, d('oveq1d', [hh], '( ( %s x. %s ) ^ ( J + 1 ) ) = ( %s ^ ( J + 1 ) )' % (H, IV, ME))], '( %s x. ( %s ^ ( J + 1 ) ) ) = ( %s ^ ( J + 1 ) )' % (HJ, IV, ME))
    le6 = linarith(w, A0, [ix], '%s <_ ( J + 1 )' % MM_, closure=Closure(w, A0, {'N': ('RR', nr), 'J': ('RR', jr)}))
    st = d('syl2anc', [d('jca', [cl.mem(MM_, 'RR'), cl.ge0(MM_)], '( %s e. RR /\\ 0 <_ %s )' % (MM_, MM_)), d('jca', [j1, le6], '( ( J + 1 ) e. NN0 /\\ %s <_ ( J + 1 ) )' % MM_), w.inst('kd2stir')],
           '( %s ^ ( J + 1 ) ) <_ %s' % (ME, F))
    k6 = d('letrd', [cl.mem(XV, 'RR'), cl.mem('( %s x. %s )' % (HJ, V), 'RR'), cl.mem('( %s x. ( %s ^ ( J + 1 ) ) )' % (HJ, IV), 'RR'), b3, b4], '%s <_ ( %s x. ( %s ^ ( J + 1 ) ) )' % (XV, HJ, IV))
    k7 = d('breqtrd', [k6, h5], '%s <_ ( %s ^ ( J + 1 ) )' % (XV, ME))
    k8 = d('letrd', [cl.mem(XV, 'RR'), cl.mem('( %s ^ ( J + 1 ) )' % ME, 'RR'), fr, k7, st], '%s <_ %s' % (XV, F))
    k9 = d('eqbrtrd', [xe, k8], '( %s x. %s ) <_ %s' % (X, DEN, F))
    b = q8le(w, A0, X, cl.mem(X, 'RR'), ep, nn0, jn, F=F, fr=fr)
    fin = d('mpbird', [k9, b], '%s <_ %s' % (X, FQ8()))
    w.qed([fin], 'idi', S['kd2bbd'])
    return only_run(w, only)


def recpow1(w, A, B, bp, nexp, nz_step):
    """( A -> ( ( ( 1 / B ) ^ n ) x. ( B ^ n ) ) = 1 ), bp : ( A -> B e. RR+ ), nz_step : ( A -> n e. NN0 )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    bc = d('rpcnd', [bp], '%s e. CC' % B); bn = d('rpne0d', [bp], '%s =/= 0' % B)
    ib = d('reccld', [bc, bn], '( 1 / %s ) e. CC' % B)
    m = d('mulexpd', [ib, bc, nz_step], '( ( ( 1 / %s ) x. %s ) ^ %s ) = ( ( ( 1 / %s ) ^ %s ) x. ( %s ^ %s ) )' % (B, B, nexp, B, nexp, B, nexp))
    r = d('recid2d', [bc, bn], '( ( 1 / %s ) x. %s ) = 1' % (B, B))
    o = d('oveq1d', [r], '( ( ( 1 / %s ) x. %s ) ^ %s ) = ( 1 ^ %s )' % (B, B, nexp, nexp))
    e1 = d('syl', [d('nn0zd', [nz_step], '%s e. ZZ' % nexp), w.inst('1exp')], '( 1 ^ %s ) = 1' % nexp)
    return d('eqtr3d', [m, d('eqtrd', [o, e1], '( ( ( 1 / %s ) x. %s ) ^ %s ) = 1' % (B, B, nexp))],
             '( ( ( 1 / %s ) ^ %s ) x. ( %s ^ %s ) ) = 1' % (B, nexp, B, nexp))


def gen_bend():
    w = W('kd2bend', 'Lean ` KDerivDetect.budget_endgame ` (constants unchanged): with ` G = Q eta^j / 68 ` , ` 1 <_ eta^3 M e^(6M) ( eta G^2 / ( 16 M ) ) ` ; ` 73984 ( T^N )^2 4^(j+2) <_ N ( 16384 T^2 )^N <_ e^(36 N) ` .')
    A0 = ante('kd2bend', '1 <_')
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    hh = d('simpl', [], HH)
    ep = d('simp1d', [hh], 'E e. RR+'); g2 = d('simp2d', [hh], '( N e. NN /\\ J e. NN0 )'); j7 = d('simp3d', [hh], '( J + 2 ) <_ ( 7 x. N )')
    n73 = d('simpr', [], '; ; ; ; 7 3 9 8 4 <_ N')
    nn = d('simpld', [g2], 'N e. NN'); jn = d('simprd', [g2], 'J e. NN0')
    nn0 = d('nnnn0d', [nn], 'N e. NN0'); nr = d('nnred', [nn], 'N e. RR'); nz = d('nnzd', [nn], 'N e. ZZ')
    tp, tlt = tc(w, A0)
    j2 = d('nn0addcld', [jn, a1(w, A0, '2nn0', '2 e. NN0')], '( J + 2 ) e. NN0')
    erp, eg2, el3 = eparts(w, A0)
    E1 = E1_
    cl = Closure(w, A0, {'E': ('RR+', ep), 'N': ('NN', nn), 'J': ('NN0', jn), '( J + 2 )': ('NN0', j2), T56: ('RR+', tp), E1: ('RR+', erp)})
    cl.atom(T56); cl.atom(E1)
    MM_ = M6
    EXP6 = '( exp ` ( 6 x. %s ) )' % MM_
    cl.leaf(EXP6, 'RR+', d('syl', [cl.mem('( 6 x. %s )' % MM_, 'RR'), w.inst('rpefcl')], '%s e. RR+' % EXP6))
    G = '( ( %s x. ( E ^ J ) ) / ; 6 8 )' % QQ()
    EX = '( ( ( ( E ^ 3 ) x. %s ) x. %s ) x. ( ( E x. ( %s ^ 2 ) ) / ( ; 1 6 x. %s ) ) )' % (MM_, EXP6, G, MM_)
    Ra = '( 1 / ( ; 1 6 x. %s ) )' % MM_
    EXr = '( ( ( ( E ^ 3 ) x. %s ) x. %s ) x. ( ( E x. ( %s ^ 2 ) ) x. %s ) )' % (MM_, EXP6, G, Ra)
    m16 = cl.mem('( ; 1 6 x. %s )' % MM_, 'RR+')
    dv = d('divrecd', [cl.mem('( E x. ( %s ^ 2 ) )' % G, 'CC'), d('rpcnd', [m16], '( ; 1 6 x. %s ) e. CC' % MM_), d('rpne0d', [m16], '( ; 1 6 x. %s ) =/= 0' % MM_)],
           '( ( E x. ( %s ^ 2 ) ) / ( ; 1 6 x. %s ) ) = ( ( E x. ( %s ^ 2 ) ) x. %s )' % (G, MM_, G, Ra))
    ex1 = d('oveq2d', [dv], '%s = %s' % (EX, EXr))
    a_ = '( %s ^ N )' % T56; b_ = '( 2 ^ ( J + 2 ) )'
    DD = '( ( ; ; ; ; 7 3 9 8 4 x. ( %s ^ 2 ) ) x. ( %s ^ 2 ) )' % (a_, b_)
    H = '( ( ; 6 8 x. %s ) x. ( ( E ^ 2 ) x. ( %s x. %s ) ) )' % (G, a_, b_)
    cla = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), 'N': ('CC', d('nncnd', [nn], 'N e. CC')), EXP6: ('CC', cl.mem(EXP6, 'CC')), G: ('CC', cl.mem(G, 'CC')),
                          Ra: ('CC', cl.mem(Ra, 'CC')), a_: ('CC', cl.mem(a_, 'CC')), b_: ('CC', cl.mem(b_, 'CC'))})
    for x in (EXP6, G, Ra, a_, b_):
        cla.atom(x)
    RHS1 = '( ( %s x. ( %s ^ 2 ) ) x. ( ( ; 1 6 x. %s ) x. %s ) )' % (EXP6, H, MM_, Ra)
    from mvlib import ringeqp
    import lin as _L
    _old = _L.MAXDEG; _L.MAXDEG = 16
    r1 = ringeqp(w, A0, '( %s x. %s )' % (EXr, DD), RHS1, cla)
    _L.MAXDEG = _old
    rr = d('recidd', [d('rpcnd', [m16], '( ; 1 6 x. %s ) e. CC' % MM_), d('rpne0d', [m16], '( ; 1 6 x. %s ) =/= 0' % MM_)], '( ( ; 1 6 x. %s ) x. %s ) = 1' % (MM_, Ra))
    # H = 1
    QE = '( %s x. ( E ^ J ) )' % QQ()
    h1 = d('divcan2d', [cl.mem(QE, 'CC'), cl.mem('; 6 8', 'CC'), cl.ne0('; 6 8')], '( ; 6 8 x. %s ) = %s' % (G, QE))
    h2 = d('oveq1d', [h1], '%s = ( %s x. ( ( E ^ 2 ) x. ( %s x. %s ) ) )' % (H, QE, a_, b_))
    IT = '( ( 1 / %s ) ^ N )' % C56E; IE2 = '( ( 1 / ( 2 x. E ) ) ^ ( J + 2 ) )'
    EJ2 = '( E ^ ( J + 2 ) )'
    clb = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), IT: ('CC', cl.mem(IT, 'CC')), IE2: ('CC', cl.mem(IE2, 'CC')), a_: ('CC', cl.mem(a_, 'CC')),
                          b_: ('CC', cl.mem(b_, 'CC')), '( E ^ J )': ('CC', cl.mem('( E ^ J )', 'CC')), '( E ^ 2 )': ('CC', cl.mem('( E ^ 2 )', 'CC'))})
    for x in (IT, IE2, a_, b_, '( E ^ J )', '( E ^ 2 )'):
        clb.atom(x)
    H3 = '( ( %s x. %s ) x. ( %s x. ( %s x. ( ( E ^ J ) x. ( E ^ 2 ) ) ) ) )' % (IT, a_, IE2, b_)
    h3 = ringeq(w, A0, '( %s x. ( ( E ^ 2 ) x. ( %s x. %s ) ) )' % (QE, a_, b_), H3, clb)
    ea = d('expaddd', [d('rpcnd', [ep], 'E e. CC'), a1(w, A0, '2nn0', '2 e. NN0'), jn], '%s = ( ( E ^ J ) x. ( E ^ 2 ) )' % EJ2)
    me = d('mulexpd', [a1(w, A0, '2cn', '2 e. CC'), d('rpcnd', [ep], 'E e. CC'), j2], '( ( 2 x. E ) ^ ( J + 2 ) ) = ( %s x. %s )' % (b_, EJ2))
    bb = d('eqtrd', [me, d('oveq2d', [ea], '( %s x. %s ) = ( %s x. ( ( E ^ J ) x. ( E ^ 2 ) ) )' % (b_, EJ2, b_))], '( ( 2 x. E ) ^ ( J + 2 ) ) = ( %s x. ( ( E ^ J ) x. ( E ^ 2 ) ) )' % b_)
    one1 = recpow1(w, A0, C56E, tp, 'N', nn0)
    one2 = recpow1(w, A0, '( 2 x. E )', cl.mem('( 2 x. E )', 'RR+'), '( J + 2 )', j2)
    o2 = d('eqtr3d', [d('oveq2d', [bb], '( %s x. ( ( 2 x. E ) ^ ( J + 2 ) ) ) = ( %s x. ( %s x. ( ( E ^ J ) x. ( E ^ 2 ) ) ) )' % (IE2, IE2, b_)), one2],
           '( %s x. ( %s x. ( ( E ^ J ) x. ( E ^ 2 ) ) ) ) = 1' % (IE2, b_))
    h4 = d('oveq12d', [one1, o2], '%s = ( 1 x. 1 )' % H3)
    hh1 = chain(w, A0, [H, '( %s x. ( ( E ^ 2 ) x. ( %s x. %s ) ) )' % (QE, a_, b_), H3, '( 1 x. 1 )', '1'], [h2, h3, h4, a1(w, A0, '1t1e1', '( 1 x. 1 ) = 1')])
    # EXr . DD = EXP6
    r2 = d('oveq12d', [d('oveq2d', [d('oveq1d', [hh1], '( %s ^ 2 ) = ( 1 ^ 2 )' % H)], '( %s x. ( %s ^ 2 ) ) = ( %s x. ( 1 ^ 2 ) )' % (EXP6, H, EXP6)), rr],
           '%s = ( ( %s x. ( 1 ^ 2 ) ) x. 1 )' % (RHS1, EXP6))
    r3 = ringeqp(w, A0, '( ( %s x. ( 1 ^ 2 ) ) x. 1 )' % EXP6, EXP6, cla)
    exd = chain(w, A0, ['( %s x. %s )' % (EXr, DD), RHS1, '( ( %s x. ( 1 ^ 2 ) ) x. 1 )' % EXP6, EXP6], [r1, r2, r3])
    # DD <_ EXP6
    b2 = d('expmuld', [a1(w, A0, '2cn', '2 e. CC'), a1(w, A0, '2nn0', '2 e. NN0'), j2], '( 2 ^ ( ( J + 2 ) x. 2 ) ) = ( %s ^ 2 )' % b_)
    b3 = d('expmuld', [a1(w, A0, '2cn', '2 e. CC'), j2, a1(w, A0, '2nn0', '2 e. NN0')], '( 2 ^ ( 2 x. ( J + 2 ) ) ) = ( ( 2 ^ 2 ) ^ ( J + 2 ) )')
    b4 = d('oveq2d', [d('mulcomd', [cl.mem('( J + 2 )', 'CC'), a1(w, A0, '2cn', '2 e. CC')], '( ( J + 2 ) x. 2 ) = ( 2 x. ( J + 2 ) )')], '( 2 ^ ( ( J + 2 ) x. 2 ) ) = ( 2 ^ ( 2 x. ( J + 2 ) ) )')
    b5 = d('oveq1d', [a1(w, A0, 'sq2', '( 2 ^ 2 ) = 4')], '( ( 2 ^ 2 ) ^ ( J + 2 ) ) = ( 4 ^ ( J + 2 ) )')
    P4 = '( 4 ^ ( J + 2 ) )'
    bq = chain(w, A0, ['( %s ^ 2 )' % b_, '( 2 ^ ( ( J + 2 ) x. 2 ) )', '( 2 ^ ( 2 x. ( J + 2 ) ) )', '( ( 2 ^ 2 ) ^ ( J + 2 ) )', P4], [('r', b2), b4, b3, b5])
    a2 = d('expmuld', [cl.mem(T56, 'CC'), nn0, a1(w, A0, '2nn0', '2 e. NN0')], '( %s ^ ( 2 x. N ) ) = ( ( %s ^ 2 ) ^ N )' % (T56, T56))
    a3 = d('expmuld', [cl.mem(T56, 'CC'), a1(w, A0, '2nn0', '2 e. NN0'), nn0], '( %s ^ ( N x. 2 ) ) = ( %s ^ 2 )' % (T56, a_))
    a4 = d('oveq2d', [d('mulcomd', [d('nncnd', [nn], 'N e. CC'), a1(w, A0, '2cn', '2 e. CC')], '( N x. 2 ) = ( 2 x. N )')], '( %s ^ ( N x. 2 ) ) = ( %s ^ ( 2 x. N ) )' % (T56, T56))
    T2 = '( %s ^ 2 )' % T56
    aq = chain(w, A0, ['( %s ^ 2 )' % a_, '( %s ^ ( N x. 2 ) )' % T56, '( %s ^ ( 2 x. N ) )' % T56, '( %s ^ N )' % T2], [('r', a3), a4, a2])
    DD2 = '( ( ; ; ; ; 7 3 9 8 4 x. ( %s ^ N ) ) x. %s )' % (T2, P4)
    dq = d('oveq12d', [d('oveq2d', [aq], '( ; ; ; ; 7 3 9 8 4 x. ( %s ^ 2 ) ) = ( ; ; ; ; 7 3 9 8 4 x. ( %s ^ N ) )' % (a_, T2)), bq], '%s = %s' % (DD, DD2))
    n7 = d('nn0mulcld', [a1(w, A0, '7nn0', '7 e. NN0'), nn0], '( 7 x. N ) e. NN0')
    u7 = uz(w, A0, '( J + 2 )', '( 7 x. N )', d('nn0zd', [j2], '( J + 2 ) e. ZZ'), d('nn0zd', [n7], '( 7 x. N ) e. ZZ'), j7)
    y2 = d('leexp2ad', [a1(w, A0, '4re', '4 e. RR'), w.s([num.le_nat(w, 1, 4)], 'a1i', '( %s -> 1 <_ 4 )' % A0), u7], '%s <_ ( 4 ^ ( 7 x. N ) )' % P4)
    y3 = d('expmuld', [a1(w, A0, '4cn', '4 e. CC'), nn0, a1(w, A0, '7nn0', '7 e. NN0')], '( 4 ^ ( 7 x. N ) ) = ( ( 4 ^ 7 ) ^ N )')
    C16 = '; ; ; ; 1 6 3 8 4'
    y4 = d('oveq1d', [w.s([numpow(w, 4, 7)], 'a1i', '( %s -> ( 4 ^ 7 ) = %s )' % (A0, C16))], '( ( 4 ^ 7 ) ^ N ) = ( %s ^ N )' % C16)
    y5 = d('breqtrd', [d('breqtrd', [y2, y3], '%s <_ ( ( 4 ^ 7 ) ^ N )' % P4), y4], '%s <_ ( %s ^ N )' % (P4, C16))
    T2N = '( %s ^ N )' % T2
    z1 = d('lemul1ad', [cl.mem('; ; ; ; 7 3 9 8 4', 'RR'), nr, cl.mem(T2N, 'RR'), cl.ge0(T2N), n73], '( ; ; ; ; 7 3 9 8 4 x. %s ) <_ ( N x. %s )' % (T2N, T2N))
    z2 = d('lemul12ad', [cl.mem('( ; ; ; ; 7 3 9 8 4 x. %s )' % T2N, 'RR'), cl.mem('( N x. %s )' % T2N, 'RR'), cl.mem(P4, 'RR'), cl.mem('( %s ^ N )' % C16, 'RR'),
                         cl.ge0('( ; ; ; ; 7 3 9 8 4 x. %s )' % T2N), cl.ge0(P4), z1, y5], '%s <_ ( ( N x. %s ) x. ( %s ^ N ) )' % (DD2, T2N, C16))
    AA = '( %s x. %s )' % (T2, C16)
    m1 = d('mulexpd', [cl.mem(T2, 'CC'), cl.mem(C16, 'CC'), nn0], '( %s ^ N ) = ( %s x. ( %s ^ N ) )' % (AA, T2N, C16))
    clc = Closure(w, A0, {'N': ('CC', d('nncnd', [nn], 'N e. CC')), T2N: ('CC', cl.mem(T2N, 'CC')), '( %s ^ N )' % C16: ('CC', cl.mem('( %s ^ N )' % C16, 'CC'))})
    clc.atom(T2N); clc.atom('( %s ^ N )' % C16)
    m2 = ringeq(w, A0, '( ( N x. %s ) x. ( %s ^ N ) )' % (T2N, C16), '( N x. ( %s x. ( %s ^ N ) ) )' % (T2N, C16), clc)
    z3 = d('eqtr4d', [m2, d('oveq2d', [m1], '( N x. ( %s ^ N ) ) = ( N x. ( %s x. ( %s ^ N ) ) )' % (AA, T2N, C16))], '( ( N x. %s ) x. ( %s ^ N ) ) = ( N x. ( %s ^ N ) )' % (T2N, C16, AA))
    aar = cl.mem(AA, 'RR')
    z4 = d('syl3anc', [d('jca', [aar, cl.ge0(AA)], '( %s e. RR /\\ 0 <_ %s )' % (AA, AA)),
                       d('jca', [cl.mem('( 2 x. %s )' % AA, 'RR'), d('leidd', [cl.mem('( 2 x. %s )' % AA, 'RR')], '( 2 x. %s ) <_ ( 2 x. %s )' % (AA, AA))],
                         '( ( 2 x. %s ) e. RR /\\ ( 2 x. %s ) <_ ( 2 x. %s ) )' % (AA, AA, AA)), nn0, w.inst('kd2nmul')],
         '( N x. ( %s ^ N ) ) <_ ( ( 2 x. %s ) ^ N )' % (AA, AA))
    E2 = epow('2'); E30 = epow('; 3 0'); E36 = epow('; 3 6')
    cl9 = Closure(w, A0, {E1: ('CC', cl.mem(E1, 'CC')), E2: ('CC', cl.mem(E2, 'CC'))}); cl9.atom(E1); cl9.atom(E2)
    CB = num.nat_text(2 * 56 * 56 * 16384)
    t0 = d('sqvald', [cl.mem(T56, 'CC')], '%s = ( %s x. %s )' % (T2, T56, T56))
    t1 = ringeq(w, A0, '( 2 x. ( ( %s x. %s ) x. %s ) )' % (T56, T56, C16), '( %s x. ( %s x. %s ) )' % (CB, E1, E1), cl9)
    sq = d('sqvald', [cl.mem(E1, 'CC')], '%s = ( %s x. %s )' % (E2, E1, E1))
    t2 = d('eqtr4d', [d('eqtrd', [d('oveq2d', [d('oveq1d', [t0], '%s = ( ( %s x. %s ) x. %s )' % (AA, T56, T56, C16))], '( 2 x. %s ) = ( 2 x. ( ( %s x. %s ) x. %s ) )' % (AA, T56, T56, C16)), t1],
                                 '( 2 x. %s ) = ( %s x. ( %s x. %s ) )' % (AA, CB, E1, E1)), d('oveq2d', [sq], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (CB, E2, CB, E1, E1))],
           '( 2 x. %s ) = ( %s x. %s )' % (AA, CB, E2))
    e29 = d('breqtrd', [d('leexp1ad', [cl.mem(E1, 'RR'), a1(w, A0, '3re', '3 e. RR'), a1(w, A0, '2nn0', '2 e. NN0'), cl.ge0(E1), el3], '%s <_ ( 3 ^ 2 )' % E2),
                        a1(w, A0, 'sq3', '( 3 ^ 2 ) = 9')], '%s <_ 9' % E2)
    t3 = d('lemul2ad', [cl.mem(E2, 'RR'), a1(w, A0, '9re', '9 e. RR'), cl.mem(CB, 'RR'), cl.ge0(CB), e29], '( %s x. %s ) <_ ( %s x. 9 )' % (CB, E2, CB))
    CB9 = num.nat_text(2 * 56 * 56 * 16384 * 9)
    t4 = d('breqtrd', [t3, w.s([num.mul_nat(w, 2 * 56 * 56 * 16384, 9)], 'a1i', '( %s -> ( %s x. 9 ) = %s )' % (A0, CB, CB9))], '( %s x. %s ) <_ %s' % (CB, E2, CB9))
    t5 = w.s([w.s([num.le_nat(w, 2 * 56 * 56 * 16384 * 9, 2 ** 30), numpow(w, 2, 30)], 'breqtrri', '%s <_ ( 2 ^ ; 3 0 )' % CB9)], 'a1i', '( %s -> %s <_ ( 2 ^ ; 3 0 ) )' % (A0, CB9))
    cle = Closure(w, A0, {E1: ('RR', cl.mem(E1, 'RR'))}); cle.atom(E1)
    e1le = linarith(w, A0, [eg2], '1 <_ %s' % E1, closure=cle)
    cl.have('( 2 ^ ; 3 0 )', 'RR', cl.mem('( 2 ^ ; 3 0 )', 'RR'))
    tA = d('eqbrtrd', [t2, t4], '( 2 x. %s ) <_ %s' % (AA, CB9))
    tB = d('letrd', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem(CB9, 'RR'), cl.mem('( 2 ^ ; 3 0 )', 'RR'), tA, t5], '( 2 x. %s ) <_ ( 2 ^ ; 3 0 )' % AA)
    tC = d('letrd', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem('( 2 ^ ; 3 0 )', 'RR'), cl.mem(E30, 'RR'), tB, two_le_e(w, A0, '; 3 0', eg2, cl)], '( 2 x. %s ) <_ %s' % (AA, E30))
    tD = d('letrd', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem(E30, 'RR'), cl.mem(E36, 'RR'), tC, ele(w, A0, '; 3 0', '; 3 6', cl, e1le)], '( 2 x. %s ) <_ %s' % (AA, E36))
    y18 = d('leexp1ad', [cl.mem('( 2 x. %s )' % AA, 'RR'), cl.mem(E36, 'RR'), nn0, cl.ge0('( 2 x. %s )' % AA), tD], '( ( 2 x. %s ) ^ N ) <_ ( %s ^ N )' % (AA, E36))
    f1 = efkn(w, A0, '; 3 6', nz)
    f2 = d('oveq1d', [efk(w, A0, '; 3 6')], '( ( exp ` ; 3 6 ) ^ N ) = ( %s ^ N )' % E36)
    f4 = d('fveq2d', [ringeq(w, A0, '( 6 x. %s )' % MM_, '( ; 3 6 x. N )', Closure(w, A0, {'N': ('CC', d('nncnd', [nn], 'N e. CC'))}))], '%s = ( exp ` ( ; 3 6 x. N ) )' % EXP6)
    ff = chain(w, A0, [EXP6, '( exp ` ( ; 3 6 x. N ) )', '( ( exp ` ; 3 6 ) ^ N )', '( %s ^ N )' % E36], [f4, f1, f2])
    k1 = d('breqtrd', [z2, z3], '%s <_ ( N x. ( %s ^ N ) )' % (DD2, AA))
    k2 = d('letrd', [cl.mem(DD2, 'RR'), cl.mem('( N x. ( %s ^ N ) )' % AA, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AA, 'RR'), k1, z4], '%s <_ ( ( 2 x. %s ) ^ N )' % (DD2, AA))
    k3 = d('letrd', [cl.mem(DD2, 'RR'), cl.mem('( ( 2 x. %s ) ^ N )' % AA, 'RR'), cl.mem('( %s ^ N )' % E36, 'RR'), k2, y18], '%s <_ ( %s ^ N )' % (DD2, E36))
    k4 = d('eqbrtrd', [dq, d('breqtrrd', [k3, ff], '%s <_ %s' % (DD2, EXP6))], '%s <_ %s' % (DD, EXP6))
    # 1 <_ EX from DD . 1 <_ DD . EX
    ddp = cl.mem(DD, 'RR+')
    exe = d('eqtrd', [d('oveq1d', [ex1], '( %s x. %s ) = ( %s x. %s )' % (EX, DD, EXr, DD)), exd], '( %s x. %s ) = %s' % (EX, DD, EXP6))
    k5 = d('breqtrrd', [k4, exe], '%s <_ ( %s x. %s )' % (DD, EX, DD))
    k6 = d('eqbrtrd', [d('mulridd', [cl.mem(DD, 'CC')], '( %s x. 1 ) = %s' % (DD, DD)), d('breqtrd', [k5, d('mulcomd', [cl.mem(EX, 'CC'), cl.mem(DD, 'CC')], '( %s x. %s ) = ( %s x. %s )' % (EX, DD, DD, EX))],
                                                                                          '%s <_ ( %s x. %s )' % (DD, DD, EX))], '( %s x. 1 ) <_ ( %s x. %s )' % (DD, DD, EX))
    fin = d('mpbird', [k6, d('lemul2d', [a1(w, A0, '1re', '1 e. RR'), cl.mem(EX, 'RR'), ddp], '( 1 <_ %s <-> ( %s x. 1 ) <_ ( %s x. %s ) )' % (EX, DD, DD, EX))], '1 <_ %s' % EX)
    w.qed([fin], 'idi', S['kd2bend'])
    return only_run(w, only)



if __name__ == '__main__':
    gen_q8()
    gen_bfar()
    gen_bcau()
    gen_bpp()
    gen_blow()
    gen_bhigh()
    gen_bbd()
    gen_bend()
