"""Sortie z4d, section D: assembly (lscpow, lspsa, lspsb, lspresift)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
import lin
lin.FASTPATH = True
from lin import linarith, lineq, nlinarith
from z4dlib import STATEMENTS as S, HYPS, Q0S, SIFT, HPS, RHO, D4, H8, GW, WIF, LOGN, AX, PC, LZ, DB, ABS2, CPW, DIR, WAX, C48, IOO, ITG
from z4d_a import mk, a1
from z4d_d import lift, fget


def lscpow():
    from mvlib import ringeq
    from cl import Closure
    w = W('lscpow', 'The Dirichlet-polynomial term n ^ ( - i t ) as an exponential with frequency - log n '
          '(Lean presifted_large_sieve hconv).')
    A0 = '( N e. NN /\\ t e. RR )'
    s = mk(w, A0)
    nnn = s([], 'simpl', 'N e. NN'); tre = s([], 'simpr', 't e. RR')
    B = '( -u t x. _i )'
    LG = '( log ` N )'
    bc = s([s([s([tre], 'recnd', 't e. CC')], 'negcld', '-u t e. CC'), a1(w, A0, 'ax-icn', '_i e. CC')], 'mulcld', '%s e. CC' % B)
    ce = s([s([nnn], 'nncnd', 'N e. CC'), s([nnn], 'nnne0d', 'N =/= 0'), bc, w.inst('cxpef')], 'syl3anc',
           '( N ^c %s ) = ( exp ` ( %s x. %s ) )' % (B, B, LG))
    lg = s([s([nnn], 'nnrpd', 'N e. RR+')], 'relogcld', '%s e. RR' % LG)
    cl = Closure(w, A0, {'t': tre, LG: lg, '_i': ('CC', a1(w, A0, 'ax-icn', '_i e. CC'))})
    rq = ringeq(w, A0, '( %s x. %s )' % (B, LG), '( _i x. ( -u %s x. t ) )' % LG, cl)
    w.qed([ce, s([rq], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` ( _i x. ( -u %s x. t ) ) )' % (B, LG, LG))], 'eqtrd', S['lscpow'])
    return w


def AXv(k):
    return '( ( A ` %s ) x. ( x ` ( %s ` %s ) ) )' % (k, LZ('f'), k)


CF = '( v e. S |-> %s )' % AXv('v')
LF = '( v e. S |-> -u ( log ` v ) )'


def lspsa():
    from z4blib import fvmd
    from z4d_d import chcl
    w = W('lspsa', 'Step A of presifted_large_sieve at one character: the t-integral of the twisted Dirichlet '
          'polynomial is at most 48 T^2 / pi times the window mean square (t_integral_le = lstint).')
    A0 = '( %s /\\ ( f e. NN /\\ x e. %s ) )' % (HPS, DB('f'))
    s = mk(w, A0)
    hps = s([], 'simpl', HPS)
    X1 = '( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) )'
    X2 = '( S e. Fin /\\ S C_ NN /\\ A : S --> CC )'
    x1 = s([hps], 'simp1d', X1); x2 = s([hps], 'simp2d', X2)
    tt = s([x1], 'simprd', '( T e. RR /\\ 1 <_ T )')
    tre = s([tt], 'simpld', 'T e. RR'); t1 = s([tt], 'simprd', '1 <_ T')
    sfin = s([x2], 'simp1d', 'S e. Fin'); ssnn = s([x2], 'simp2d', 'S C_ NN'); af = s([x2], 'simp3d', 'A : S --> CC')
    fnn = s([], 'simprl', 'f e. NN'); xdb = s([], 'simprr', 'x e. %s' % DB('f'))
    tpos = linarith(w, A0, [t1], '0 < T', leaves={'T': tre})
    trp = s([tre, tpos], 'elrpd', 'T e. RR+')
    L = lambda st, frm, to: lift(w, st, frm, to)

    def vals(ctx, v, vS):
        """( ctx -> ( CF ` v ) = AX(v) ), ( ctx -> ( LF ` v ) = -u ( log ` v ) ), AX(v) e. CC, log v e. RR"""
        an = w.s([L(af, A0, ctx), vS], 'ffvelcdmd', '( %s -> ( A ` %s ) e. CC )' % (ctx, v))
        vn = w.s([L(ssnn, A0, ctx), vS], 'sseldd', '( %s -> %s e. NN )' % (ctx, v))
        vz = w.s([vn], 'nnzd', '( %s -> %s e. ZZ )' % (ctx, v))
        axc = w.s([an, chcl(w, ctx, L(xdb, A0, ctx), vz, n=v)], 'mulcld', '( %s -> %s e. CC )' % (ctx, AXv(v)))
        lg = w.s([w.s([vn], 'nnrpd', '( %s -> %s e. RR+ )' % (ctx, v))], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (ctx, v))
        nlg = w.s([lg], 'renegcld', '( %s -> -u ( log ` %s ) e. RR )' % (ctx, v))
        c = fvmd(w, ctx, 'v', 'S', AXv('v'), v, vS, axc)
        l = fvmd(w, ctx, 'v', 'S', '-u ( log ` v )', v, vS, w.s([nlg], 'recnd', '( %s -> -u ( log ` %s ) e. CC )' % (ctx, v)))
        return c, l, axc, nlg, vn
    Ca = '( %s /\\ a e. S )' % A0
    c, l, axc, nlg, _ = vals(Ca, 'a', w.s([], 'simpr', '( %s -> a e. S )' % Ca))
    HKQ = 'A. a e. S ( ( %s ` a ) e. CC /\\ ( %s ` a ) e. RR )' % (CF, LF)
    hk1 = w.s([w.s([c, axc], 'eqeltrd', '( %s -> ( %s ` a ) e. CC )' % (Ca, CF)), w.s([l, nlg], 'eqeltrd', '( %s -> ( %s ` a ) e. RR )' % (Ca, LF))],
              'jca', '( %s -> ( ( %s ` a ) e. CC /\\ ( %s ` a ) e. RR ) )' % (Ca, CF, LF))
    HK = '( S e. Fin /\\ %s )' % HKQ
    hk = s([sfin, s([hk1], 'ralrimiva', HKQ)], 'jca', HK)
    SXC = 'sum_ i e. S ( ( %s ` i ) x. ( exp ` ( _i x. ( ( %s ` i ) x. t ) ) ) )' % (CF, LF)
    WSC = 'sum_ i e. S if ( ( abs ` ( ( %s ` i ) - u ) ) <_ %s , ( %s ` i ) , 0 )' % (LF, H8, CF)
    lt = s([trp, hk, w.inst('lstint')], 'syl2anc', '%s <_ ( %s x. %s )' % (ITG(IOO('-u T', 'T'), ABS2(SXC)), C48, ITG('RR', ABS2(WSC), 'u')))
    r8 = w.s([w.s([w.s([], '8re', '8 e. RR'), w.s([], '8pos', '0 < 8')], 'elrpii', '8 e. RR+')], 'a1i', '( %s -> 8 e. RR+ )' % A0)
    h8 = s([a1(w, A0, 'pirp', '_pi e. RR+'), s([r8, trp], 'rpmulcld', '( 8 x. T ) e. RR+')], 'rpdivcld', '%s e. RR+' % H8)
    from z4dlib import BIL as ZBIL
    sq = s([hk, h8, w.inst('lswsq')], 'syl2anc', '( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( Re ` %s ) )' % (
        ABS2(WSC), ITG('RR', ABS2(WSC), 'u'), ZBIL('( 2 x. %s )' % H8).replace('( C `', '( %s `' % CF).replace('( L `', '( %s `' % LF).replace(' e. P ', ' e. S ')))
    # window rewrite
    Bu = '( %s /\\ u e. RR )' % A0
    Bui = '( %s /\\ i e. S )' % Bu
    ci, li, _, _, _ = vals(Bui, 'i', w.s([], 'simpr', '( %s -> i e. S )' % Bui))
    WI = lambda v: 'if ( ( abs ` ( -u ( log ` %s ) - u ) ) <_ %s , %s , 0 )' % (v, H8, AXv(v))
    cnd = w.s([w.s([w.s([li], 'oveq1d', '( %s -> ( ( %s ` i ) - u ) = ( -u ( log ` i ) - u ) )' % (Bui, LF))], 'fveq2d',
                   '( %s -> ( abs ` ( ( %s ` i ) - u ) ) = ( abs ` ( -u ( log ` i ) - u ) ) )' % (Bui, LF))], 'breq1d',
              '( %s -> ( ( abs ` ( ( %s ` i ) - u ) ) <_ %s <-> ( abs ` ( -u ( log ` i ) - u ) ) <_ %s ) )' % (Bui, LF, H8, H8))
    ie = w.s([cnd, ci, w.s([], 'eqidd', '( %s -> 0 = 0 )' % Bui)], 'ifbieq12d',
             '( %s -> if ( ( abs ` ( ( %s ` i ) - u ) ) <_ %s , ( %s ` i ) , 0 ) = %s )' % (Bui, LF, H8, CF, WI('i')))
    su = w.s([ie], 'sumeq2dv', '( %s -> %s = sum_ i e. S %s )' % (Bu, WSC, WI('i')))
    idn = w.s([], 'id', '( i = n -> i = n )')
    cw, nw = w.congr(WI('i'), {'i': 'n'}, 'i = n', {'i': idn})
    cb = w.s([w.s([cw], 'cbvsumv', 'sum_ i e. S %s = %s' % (WI('i'), WAX))], 'a1i', '( %s -> sum_ i e. S %s = %s )' % (Bu, WI('i'), WAX))
    wq = w.s([su, cb], 'eqtrd', '( %s -> %s = %s )' % (Bu, WSC, WAX))
    wq2 = w.s([w.s([wq], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (Bu, WSC, WAX))], 'oveq1d', '( %s -> %s = %s )' % (Bu, ABS2(WSC), ABS2(WAX)))
    mq = s([wq2], 'mpteq2dva', '( u e. RR |-> %s ) = ( u e. RR |-> %s )' % (ABS2(WSC), ABS2(WAX)))
    iq = s([wq2], 'itgeq2dv', '%s = %s' % (ITG('RR', ABS2(WSC), 'u'), ITG('RR', ABS2(WAX), 'u')))
    ib = s([mq, s([sq], 'simpld', '( u e. RR |-> %s ) e. L^1' % ABS2(WSC))], 'eqeltrrd', '( u e. RR |-> %s ) e. L^1' % ABS2(WAX))
    # Dirichlet polynomial rewrite
    TT = IOO('-u T', 'T')
    Bt = '( %s /\\ t e. %s )' % (A0, TT)
    tr = w.s([w.s([], 'simpr', '( %s -> t e. %s )' % (Bt, TT)), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % Bt)
    Bti = '( %s /\\ i e. S )' % Bt
    ci2, li2, _, _, inn = vals(Bti, 'i', w.s([], 'simpr', '( %s -> i e. S )' % Bti))
    EXC = '( exp ` ( _i x. ( ( %s ` i ) x. t ) ) )' % LF
    EXL = '( exp ` ( _i x. ( -u ( log ` i ) x. t ) ) )'
    CPi = '( i ^c ( -u t x. _i ) )'
    ex1 = w.s([w.s([w.s([li2], 'oveq1d', '( %s -> ( ( %s ` i ) x. t ) = ( -u ( log ` i ) x. t ) )' % (Bti, LF))], 'oveq2d',
                   '( %s -> ( _i x. ( ( %s ` i ) x. t ) ) = ( _i x. ( -u ( log ` i ) x. t ) ) )' % (Bti, LF))], 'fveq2d', '( %s -> %s = %s )' % (Bti, EXC, EXL))
    cp = w.s([inn, L(tr, Bt, Bti), w.inst('lscpow')], 'syl2anc', '( %s -> %s = %s )' % (Bti, CPi, EXL))
    ex2 = w.s([ex1, cp], 'eqtr4d', '( %s -> %s = %s )' % (Bti, EXC, CPi))
    tq = w.s([ci2, ex2], 'oveq12d', '( %s -> ( ( %s ` i ) x. %s ) = ( %s x. %s ) )' % (Bti, CF, EXC, AXv('i'), CPi))
    st_ = w.s([tq], 'sumeq2dv', '( %s -> %s = sum_ i e. S ( %s x. %s ) )' % (Bt, SXC, AXv('i'), CPi))
    cd, nd = w.congr('( %s x. %s )' % (AXv('i'), CPi), {'i': 'n'}, 'i = n', {'i': idn})
    cb2 = w.s([w.s([cd], 'cbvsumv', 'sum_ i e. S ( %s x. %s ) = %s' % (AXv('i'), CPi, DIR))], 'a1i',
              '( %s -> sum_ i e. S ( %s x. %s ) = %s )' % (Bt, AXv('i'), CPi, DIR))
    dq = w.s([st_, cb2], 'eqtrd', '( %s -> %s = %s )' % (Bt, SXC, DIR))
    dq2 = w.s([w.s([dq], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (Bt, SXC, DIR))], 'oveq1d', '( %s -> %s = %s )' % (Bt, ABS2(SXC), ABS2(DIR)))
    iq2 = s([dq2], 'itgeq2dv', '%s = %s' % (ITG(TT, ABS2(SXC)), ITG(TT, ABS2(DIR))))
    rq = s([iq], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (C48, ITG('RR', ABS2(WSC), 'u'), C48, ITG('RR', ABS2(WAX), 'u')))
    le = s([lt, iq2, rq], '3brtr3d', '%s <_ ( %s x. %s )' % (ITG(TT, ABS2(DIR)), C48, ITG('RR', ABS2(WAX), 'u')))
    # realness of the t-integral (lsibl over the continuous SXC)
    from z4blib import cnsq
    from mvlib import SXD
    DV = '( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )'
    sxd = SXD('t').replace('( C `', '( %s `' % CF).replace('( L `', '( %s `' % LF).replace(' e. P ', ' e. S ')
    dv = s([hk, w.inst('mvsxdv')], 'syl', DV % (SXC, sxd, SXC, sxd))
    cn = s([dv], 'simp2d', '( t e. RR |-> %s ) e. ( RR -cn-> CC )' % SXC)
    At = '( %s /\\ t e. RR )' % A0
    Ati = '( %s /\\ i e. S )' % At
    ci3, li3, axc3, nlg3, _ = vals(Ati, 'i', w.s([], 'simpr', '( %s -> i e. S )' % Ati))
    cc3 = w.s([ci3, axc3], 'eqeltrd', '( %s -> ( %s ` i ) e. CC )' % (Ati, CF))
    lr3 = w.s([li3, nlg3], 'eqeltrd', '( %s -> ( %s ` i ) e. RR )' % (Ati, LF))
    tc3 = w.s([w.s([w.s([], 'simpr', '( %s -> t e. RR )' % At)], 'adantr', '( %s -> t e. RR )' % Ati)], 'recnd', '( %s -> t e. CC )' % Ati)
    ex3 = w.s([w.s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Ati),
                    w.s([w.s([lr3], 'recnd', '( %s -> ( %s ` i ) e. CC )' % (Ati, LF)), tc3], 'mulcld', '( %s -> ( ( %s ` i ) x. t ) e. CC )' % (Ati, LF))],
                   'mulcld', '( %s -> ( _i x. ( ( %s ` i ) x. t ) ) e. CC )' % (Ati, LF))], 'efcld', '( %s -> %s e. CC )' % (Ati, EXC))
    sxc = w.s([L(sfin, A0, At), w.s([cc3, ex3], 'mulcld', '( %s -> ( ( %s ` i ) x. %s ) e. CC )' % (Ati, CF, EXC))], 'fsumcl', '( %s -> %s e. CC )' % (At, SXC))
    xcn = cnsq(w, A0, cn, SXC, 't', sxc)
    ibt = s([s([tre], 'renegcld', '-u T e. RR'), tre, xcn], 'lsibl', '( t e. %s |-> %s ) e. L^1' % (TT, ABS2(SXC)))
    Bt2 = '( %s /\\ t e. %s )' % (A0, TT)
    tr2 = w.s([w.s([], 'simpr', '( %s -> t e. %s )' % (Bt2, TT)), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % Bt2)
    xr2 = w.s([w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Bt2, A0)), tr2], 'jca', '( %s -> %s )' % (Bt2, At)), sxc], 'syl',
                        '( %s -> %s e. CC )' % (Bt2, SXC))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Bt2, SXC))], 'resqcld',
              '( %s -> %s e. RR )' % (Bt2, ABS2(SXC)))
    ir = s([xr2, ibt], 'itgrecl', '%s e. RR' % ITG(TT, ABS2(SXC)))
    ir2 = s([iq2, ir], 'eqeltrrd', '%s e. RR' % ITG(TT, ABS2(DIR)))
    w.qed([ib, ir2, le], '3jca', S['lspsa'])
    return w


def lspsb():
    from z4dlib import LHSU, LHST, LOGW
    from z4d_d import chcl
    w = W('lspsb', 'Steps A, B and the swap of presifted_large_sieve: the conductor-weighted t-integrals are at '
          'most 48 T^2 / pi times the x-integral of the conductor-weighted window sums (Lean hB, hswap).')
    A0 = HPS
    s = mk(w, A0)
    X1 = '( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) )'
    X2 = '( S e. Fin /\\ S C_ NN /\\ A : S --> CC )'
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2)
    qq = s([x1], 'simpld', '( Q e. RR /\\ 2 <_ Q )'); tt = s([x1], 'simprd', '( T e. RR /\\ 1 <_ T )')
    qre = s([qq], 'simpld', 'Q e. RR'); q2 = s([qq], 'simprd', '2 <_ Q')
    tre = s([tt], 'simpld', 'T e. RR')
    sfin = s([x2], 'simp1d', 'S e. Fin'); ssnn = s([x2], 'simp2d', 'S C_ NN'); af = s([x2], 'simp3d', 'A : S --> CC')
    L = lambda st, frm, to: lift(w, st, frm, to)
    Af = '( %s /\\ f e. %s )' % (A0, Q0S)
    fa = mk(w, Af)
    ffz = fa([], 'simpr', 'f e. %s' % Q0S)
    fnn = fa([ffz, w.inst('elfznn')], 'syl', 'f e. NN')
    fre = fa([fnn], 'nnred', 'f e. RR')
    qa = L(qre, A0, Af)
    FL = '( |_ ` Q )'
    fq = fa([fre, fa([fa([qa], 'flcld', '%s e. ZZ' % FL)], 'zred', '%s e. RR' % FL), qa, fa([ffz, w.inst('elfzle2')], 'syl', 'f <_ %s' % FL),
             fa([qa, w.inst('flle')], 'syl', '%s <_ Q' % FL)], 'letrd', 'f <_ Q')
    q1 = fa([fa([a1(w, Af, '1re', '1 e. RR'), qa, fa([fre, fa([fnn], 'nngt0d', '0 < f')], 'jca', '( f e. RR /\\ 0 < f )'), w.inst('lemuldiv')],
                'syl3anc', '( ( 1 x. f ) <_ Q <-> 1 <_ ( Q / f ) )'),
             fa([fa([fa([fnn], 'nncnd', 'f e. CC')], 'mullidd', '( 1 x. f ) = f'), fq], 'eqbrtrd', '( 1 x. f ) <_ Q')], 'mpbid', '1 <_ ( Q / f )')
    qf = fa([qa, fre, fa([fnn], 'nnne0d', 'f =/= 0')], 'redivcld', '( Q / f ) e. RR')
    lge = fa([qf, q1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LOGW)
    qpos = linarith(w, Af, [L(q2, A0, Af)], '0 < Q', leaves={'Q': qa})
    lre = fa([fa([fa([qa, qpos], 'elrpd', 'Q e. RR+'), fa([fnn], 'nnrpd', 'f e. RR+')], 'rpdivcld', '( Q / f ) e. RR+')], 'relogcld', '%s e. RR' % LOGW)
    e = lambda t: w.s([], 'eqid', '%s = %s' % (t, t))
    dfin = fa([fnn, w.s([e('( DChr ` f )'), e(DB('f'))], 'dchrfi', '( f e. NN -> %s e. Fin )' % DB('f'))], 'syl', '%s e. Fin' % DB('f'))
    pcfin = fa([dfin, a1(w, Af, 'ssrab2', '%s C_ %s' % (PC('f'), DB('f')))], 'ssfid', '%s e. Fin' % PC('f'))
    Ax = '( %s /\\ x e. %s )' % (Af, PC('f'))
    xa = mk(w, Ax)
    xdb = xa([xa([], 'simpr', 'x e. %s' % PC('f')), w.inst('elrabi')], 'syl', 'x e. %s' % DB('f'))
    TT = IOO('-u T', 'T')
    WX = ABS2(WAX)
    I_ = ITG(TT, ABS2(DIR))
    J_ = ITG('RR', WX, 'u')
    sa = xa([w.s([], 'simpll', '( %s -> %s )' % (Ax, A0)), xa([L(fnn, Af, Ax), xdb], 'jca', '( f e. NN /\\ x e. %s )' % DB('f')), w.inst('lspsa')],
            'syl2anc', '( ( u e. RR |-> %s ) e. L^1 /\\ %s e. RR /\\ %s <_ ( %s x. %s ) )' % (WX, I_, I_, C48, J_))
    ib = xa([sa], 'simp1d', '( u e. RR |-> %s ) e. L^1' % WX)
    ir = xa([sa], 'simp2d', '%s e. RR' % I_)
    ile = xa([sa], 'simp3d', '%s <_ ( %s x. %s )' % (I_, C48, J_))

    def wxc(ctx, xpc):
        """( ctx -> WAX e. CC ) where ctx proves f e. Q0S via lifting fnn, and xpc: ( ctx -> x e. PC(f) )"""
        xd = w.s([xpc, w.inst('elrabi')], 'syl', '( %s -> x e. %s )' % (ctx, DB('f')))
        Cn = '( %s /\\ n e. S )' % ctx
        nS = w.s([], 'simpr', '( %s -> n e. S )' % Cn)
        an = w.s([L(af, A0, Cn), nS], 'ffvelcdmd', '( %s -> ( A ` n ) e. CC )' % Cn)
        nz = w.s([w.s([L(ssnn, A0, Cn), nS], 'sseldd', '( %s -> n e. NN )' % Cn)], 'nnzd', '( %s -> n e. ZZ )' % Cn)
        axc = w.s([an, chcl(w, Cn, w.s([xd], 'adantr', '( %s -> x e. %s )' % (Cn, DB('f'))), nz)], 'mulcld', '( %s -> %s e. CC )' % (Cn, AX))
        ifc = w.s([axc, w.s([], '0cnd', '( %s -> 0 e. CC )' % Cn)], 'ifcld', '( %s -> %s e. CC )' % (Cn, WIF(LOGN, H8, AX)))
        return w.s([L(sfin, A0, ctx), ifc], 'fsumcl', '( %s -> %s e. CC )' % (ctx, WAX))
    Axu = '( %s /\\ u e. RR )' % Ax
    wr = w.s([w.s([wxc(Axu, L(xa([], 'simpr', 'x e. %s' % PC('f')), Ax, Axu))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Axu, WAX))], 'resqcld',
             '( %s -> %s e. RR )' % (Axu, WX))
    jr = xa([wr, ib], 'itgrecl', '%s e. RR' % J_)
    c48 = s([s([s([w.s([w.s([w.s([], '4nn0', '4 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; 4 8 e. NN0')], 'nn0rei', '; 4 8 e. RR')], 'a1i', '; 4 8 e. RR'),
                s([tre], 'resqcld', '( T ^ 2 ) e. RR')], 'remulcld', '( ; 4 8 x. ( T ^ 2 ) ) e. RR'),
             a1(w, A0, 'pire', '_pi e. RR'), a1(w, A0, 'pine0', '_pi =/= 0')], 'redivcld', '%s e. RR' % C48)
    cj = xa([L(c48, A0, Ax), jr], 'remulcld', '( %s x. %s ) e. RR' % (C48, J_))
    SI = 'sum_ x e. %s %s' % (PC('f'), I_)
    SCJ = 'sum_ x e. %s ( %s x. %s )' % (PC('f'), C48, J_)
    fl1 = fa([pcfin, ir, cj, ile], 'fsumle', '%s <_ %s' % (SI, SCJ))
    sir = fa([pcfin, ir], 'fsumrecl', '%s e. RR' % SI)
    scr = fa([pcfin, cj], 'fsumrecl', '%s e. RR' % SCJ)
    fl2 = fa([sir, scr, lre, lge, fl1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (LOGW, SI, LOGW, SCJ))
    RB = 'sum_ f e. %s ( %s x. %s )' % (Q0S, LOGW, SCJ)
    fl3 = s([a1(w, A0, 'fzfi', '%s e. Fin' % Q0S), fa([lre, sir], 'remulcld', '( %s x. %s ) e. RR' % (LOGW, SI)),
             fa([lre, scr], 'remulcld', '( %s x. %s ) e. RR' % (LOGW, SCJ)), fl2], 'fsumle', '%s <_ %s' % (LHST, RB))
    # swap
    SW_ = 'sum_ x e. %s %s' % (PC('f'), WX)
    Afux = '( %s /\\ ( u e. RR /\\ x e. %s ) )' % (Af, PC('f'))
    h3 = w.s([w.s([wxc(Afux, w.s([], 'simprr', '( %s -> x e. %s )' % (Afux, PC('f'))))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Afux, WAX))],
             'resqcld', '( %s -> %s e. RR )' % (Afux, WX))
    h3c = w.s([h3], 'recnd', '( %s -> %s e. CC )' % (Afux, WX))
    rmb = lambda ante: w.s([w.s([], 'rembl', 'RR e. dom vol')], 'a1i', '( %s -> RR e. dom vol )' % ante)
    inner = fa([rmb(Af), pcfin, h3c, ib], 'itgfsum', '( ( u e. RR |-> %s ) e. L^1 /\\ %s = sum_ x e. %s %s )' % (SW_, ITG('RR', SW_, 'u'), PC('f'), J_))
    Afu = '( %s /\\ u e. RR )' % Af
    Afux2 = '( %s /\\ x e. %s )' % (Afu, PC('f'))
    h3b = w.s([w.s([wxc(Afux2, w.s([], 'simpr', '( %s -> x e. %s )' % (Afux2, PC('f'))))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Afux2, WAX))],
              'resqcld', '( %s -> %s e. RR )' % (Afux2, WX))
    swc = w.s([L(pcfin, Af, Afu), w.s([h3b], 'recnd', '( %s -> %s e. CC )' % (Afux2, WX))], 'fsumcl', '( %s -> %s e. CC )' % (Afu, SW_))
    lc = fa([lre], 'recnd', '%s e. CC' % LOGW)
    ibm = fa([lc, swc, fa([inner], 'simpld', '( u e. RR |-> %s ) e. L^1' % SW_)], 'iblmulc2', '( u e. RR |-> ( %s x. %s ) ) e. L^1' % (LOGW, SW_))
    imc = fa([lc, swc, fa([inner], 'simpld', '( u e. RR |-> %s ) e. L^1' % SW_)], 'itgmulc2',
             '( %s x. %s ) = %s' % (LOGW, ITG('RR', SW_, 'u'), ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u')))
    Auf = '( %s /\\ ( u e. RR /\\ f e. %s ) )' % (A0, Q0S)
    # ( Auf -> ( LOGW x. SW_ ) e. CC ): reorder to Afu
    reo = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Auf, A0)), w.s([], 'simprr', '( %s -> f e. %s )' % (Auf, Q0S))], 'jca', '( %s -> %s )' % (Auf, Af)),
               w.s([], 'simprl', '( %s -> u e. RR )' % Auf)], 'jca', '( %s -> %s )' % (Auf, Afu))
    tcl = w.s([reo, w.s([L(lc, Af, Afu), swc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Afu, LOGW, SW_))], 'syl',
              '( %s -> ( %s x. %s ) e. CC )' % (Auf, LOGW, SW_))
    outer = s([rmb(A0), a1(w, A0, 'fzfi', '%s e. Fin' % Q0S), tcl, ibm], 'itgfsum',
              '( ( u e. RR |-> %s ) e. L^1 /\\ %s = sum_ f e. %s %s )' % (LHSU, ITG('RR', LHSU, 'u'), Q0S, ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u')))
    # per f: C48 x. S. ( LOGW x. SW ) = LOGW x. SCJ
    SJ = 'sum_ x e. %s %s' % (PC('f'), J_)
    c48c = L(s([c48], 'recnd', '%s e. CC' % C48), A0, Af)
    sjc = fa([pcfin, xa([jr], 'recnd', '%s e. CC' % J_)], 'fsumcl', '%s e. CC' % SJ)
    p1 = fa([fa([imc, fa([fa([inner], 'simprd', '%s = %s' % (ITG('RR', SW_, 'u'), SJ))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (LOGW, ITG('RR', SW_, 'u'), LOGW, SJ))],
                'eqtr3d', '%s = ( %s x. %s )' % (ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u'), LOGW, SJ))], 'oveq2d',
            '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (C48, ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u'), C48, LOGW, SJ))
    p2 = fa([c48c, lc, sjc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (C48, LOGW, SJ, LOGW, C48, SJ))
    p3 = fa([fa([pcfin, c48c, xa([jr], 'recnd', '%s e. CC' % J_)], 'fsummulc2', '( %s x. %s ) = %s' % (C48, SJ, SCJ))], 'oveq2d',
            '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (LOGW, C48, SJ, LOGW, SCJ))
    pf = fa([fa([p1, p2], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (C48, ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u'), LOGW, C48, SJ)), p3], 'eqtrd',
            '( %s x. %s ) = ( %s x. %s )' % (C48, ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u'), LOGW, SCJ))
    IT = ITG('RR', '( %s x. %s )' % (LOGW, SW_), 'u')
    itc = fa([imc, fa([lc, fa([fa([inner], 'simprd', '%s = %s' % (ITG('RR', SW_, 'u'), SJ)), sjc], 'eqeltrd', '%s e. CC' % ITG('RR', SW_, 'u'))], 'mulcld',
                      '( %s x. %s ) e. CC' % (LOGW, ITG('RR', SW_, 'u')))], 'eqeltrrd', '%s e. CC' % IT)
    fm = s([a1(w, A0, 'fzfi', '%s e. Fin' % Q0S), s([c48], 'recnd', '%s e. CC' % C48), itc], 'fsummulc2',
           '( %s x. sum_ f e. %s %s ) = sum_ f e. %s ( %s x. %s )' % (C48, Q0S, IT, Q0S, C48, IT))
    sm = s([pf], 'sumeq2dv', 'sum_ f e. %s ( %s x. %s ) = %s' % (Q0S, C48, IT, RB))
    rq = s([s([s([outer], 'simprd', '%s = sum_ f e. %s %s' % (ITG('RR', LHSU, 'u'), Q0S, IT))], 'oveq2d',
              '( %s x. %s ) = ( %s x. sum_ f e. %s %s )' % (C48, ITG('RR', LHSU, 'u'), C48, Q0S, IT)), s([fm, sm], 'eqtrd',
              '( %s x. sum_ f e. %s %s ) = %s' % (C48, Q0S, IT, RB))], 'eqtrd', '( %s x. %s ) = %s' % (C48, ITG('RR', LHSU, 'u'), RB))
    fin = s([fl3, rq], 'breqtrrd', '%s <_ ( %s x. %s )' % (LHST, C48, ITG('RR', LHSU, 'u')))
    w.qed([s([outer], 'simpld', '( u e. RR |-> %s ) e. L^1' % LHSU), fin], 'jca', S['lspsb'])
    return w


def lspresift():
    from z4dlib import LHSU, RHSU, LHST, LOGW, AN2
    from z4d_d import chcl, h2d4
    from mvlib import ringeq
    from cl import Closure
    w = W('lspresift', 'The pre-sifted multiplicative large sieve, t-integrated (Gallagher 1970, Theorem 4, lossy '
          'constants; Lean presifted_large_sieve).')
    A0 = HPS
    s = mk(w, A0)
    X1 = '( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) )'
    X2 = '( S e. Fin /\\ S C_ NN /\\ A : S --> CC )'
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2)
    qq = s([x1], 'simpld', '( Q e. RR /\\ 2 <_ Q )'); tt = s([x1], 'simprd', '( T e. RR /\\ 1 <_ T )')
    qre = s([qq], 'simpld', 'Q e. RR'); q2 = s([qq], 'simprd', '2 <_ Q')
    tre = s([tt], 'simpld', 'T e. RR'); t1 = s([tt], 'simprd', '1 <_ T')
    sfin = s([x2], 'simp1d', 'S e. Fin'); ssnn = s([x2], 'simp2d', 'S C_ NN'); af = s([x2], 'simp3d', 'A : S --> CC')
    L = lambda st, frm, to: lift(w, st, frm, to)
    tpos = linarith(w, A0, [t1], '0 < T', leaves={'T': tre})
    trp = s([tre, tpos], 'elrpd', 'T e. RR+')
    e = lambda t: w.s([], 'eqid', '%s = %s' % (t, t))
    TT = IOO('-u T', 'T')
    WX = ABS2(WAX)
    I_ = ITG(TT, ABS2(DIR))

    def fstuff(Af):
        """facts at ( ... /\\ f e. Q0S ): fnn, LOGW real, PC(f) finite"""
        fa = mk(w, Af)
        base = Af[2:].rsplit(' /\\ f e. ', 1)[0]
        ffz = fa([], 'simpr', 'f e. %s' % Q0S)
        fnn = fa([ffz, w.inst('elfznn')], 'syl', 'f e. NN')
        qa = L(qre, A0, Af)
        qpos = linarith(w, Af, [L(q2, A0, Af)], '0 < Q', leaves={'Q': qa})
        lre = fa([fa([fa([qa, qpos], 'elrpd', 'Q e. RR+'), fa([fnn], 'nnrpd', 'f e. RR+')], 'rpdivcld', '( Q / f ) e. RR+')], 'relogcld', '%s e. RR' % LOGW)
        dfin = fa([fnn, w.s([e('( DChr ` f )'), e(DB('f'))], 'dchrfi', '( f e. NN -> %s e. Fin )' % DB('f'))], 'syl', '%s e. Fin' % DB('f'))
        pcfin = fa([dfin, a1(w, Af, 'ssrab2', '%s C_ %s' % (PC('f'), DB('f')))], 'ssfid', '%s e. Fin' % PC('f'))
        return fnn, lre, pcfin

    def wxr(ctx, xpc):
        xd = w.s([xpc, w.inst('elrabi')], 'syl', '( %s -> x e. %s )' % (ctx, DB('f')))
        Cn = '( %s /\\ n e. S )' % ctx
        nS = w.s([], 'simpr', '( %s -> n e. S )' % Cn)
        an = w.s([L(af, A0, Cn), nS], 'ffvelcdmd', '( %s -> ( A ` n ) e. CC )' % Cn)
        nz = w.s([w.s([L(ssnn, A0, Cn), nS], 'sseldd', '( %s -> n e. NN )' % Cn)], 'nnzd', '( %s -> n e. ZZ )' % Cn)
        axc = w.s([an, chcl(w, Cn, w.s([xd], 'adantr', '( %s -> x e. %s )' % (Cn, DB('f'))), nz)], 'mulcld', '( %s -> %s e. CC )' % (Cn, AX))
        ifc = w.s([axc, w.s([], '0cnd', '( %s -> 0 e. CC )' % Cn)], 'ifcld', '( %s -> %s e. CC )' % (Cn, WIF(LOGN, H8, AX)))
        wc = w.s([L(sfin, A0, ctx), ifc], 'fsumcl', '( %s -> %s e. CC )' % (ctx, WAX))
        return w.s([w.s([wc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ctx, WAX))], 'resqcld', '( %s -> %s e. RR )' % (ctx, WX))
    # LHST real
    Af = '( %s /\\ f e. %s )' % (A0, Q0S)
    fnn, lre, pcfin = fstuff(Af)
    Ax = '( %s /\\ x e. %s )' % (Af, PC('f'))
    xa = mk(w, Ax)
    xdb = xa([xa([], 'simpr', 'x e. %s' % PC('f')), w.inst('elrabi')], 'syl', 'x e. %s' % DB('f'))
    J_ = ITG('RR', WX, 'u')
    sa = xa([w.s([], 'simpll', '( %s -> %s )' % (Ax, A0)), xa([L(fnn, Af, Ax), xdb], 'jca', '( f e. NN /\\ x e. %s )' % DB('f')), w.inst('lspsa')],
            'syl2anc', '( ( u e. RR |-> %s ) e. L^1 /\\ %s e. RR /\\ %s <_ ( %s x. %s ) )' % (WX, I_, I_, C48, J_))
    ir = xa([sa], 'simp2d', '%s e. RR' % I_)
    SI = 'sum_ x e. %s %s' % (PC('f'), I_)
    ltr = s([a1(w, A0, 'fzfi', '%s e. Fin' % Q0S), w.s([lre, w.s([pcfin, ir], 'fsumrecl', '( %s -> %s e. RR )' % (Af, SI))], 'remulcld',
            '( %s -> ( %s x. %s ) e. RR )' % (Af, LOGW, SI))], 'fsumrecl', '%s e. RR' % LHST)
    # LHSU real at u
    Au = '( %s /\\ u e. RR )' % A0
    Auf = '( %s /\\ f e. %s )' % (Au, Q0S)
    fnn2, lre2, pcfin2 = fstuff(Auf)
    Aufx = '( %s /\\ x e. %s )' % (Auf, PC('f'))
    wr2 = wxr(Aufx, w.s([], 'simpr', '( %s -> x e. %s )' % (Aufx, PC('f'))))
    SW_ = 'sum_ x e. %s %s' % (PC('f'), WX)
    lur = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Au, Q0S)), w.s([lre2, w.s([pcfin2, wr2], 'fsumrecl', '( %s -> %s e. RR )' % (Auf, SW_))], 'remulcld',
              '( %s -> ( %s x. %s ) e. RR )' % (Auf, LOGW, SW_))], 'fsumrecl', '( %s -> %s e. RR )' % (Au, LHSU))
    # RHSU: the integrand and its integral
    GA = '( %s x. %s )' % (GW(), AN2)
    An = '( %s /\\ n e. S )' % A0
    na = mk(w, An)
    nS = na([], 'simpr', 'n e. S')
    nnn = na([L(ssnn, A0, An), nS], 'sseldd', 'n e. NN')
    nre = na([nnn], 'nnred', 'n e. RR')
    anc = na([L(af, A0, An), nS], 'ffvelcdmd', '( A ` n ) e. CC')
    a2r = na([na([anc], 'abscld', '( abs ` ( A ` n ) ) e. RR')], 'resqcld', '%s e. RR' % AN2)
    a2g = na([na([anc], 'abscld', '( abs ` ( A ` n ) ) e. RR')], 'sqge0d', '0 <_ %s' % AN2)
    pir = a1(w, An, 'pire', '_pi e. RR')
    d4r = L(s([a1(w, A0, 'pirp', '_pi e. RR+'), s([a1(w, A0, '4rp', '4 e. RR+'), trp], 'rpmulcld', '( 4 x. T ) e. RR+')], 'rpdivcld', '%s e. RR+' % D4), A0, An)
    rhr = na([na([na([d4r], 'rpred', '%s e. RR' % D4)], 'reefcld', '( exp ` %s ) e. RR' % D4), a1(w, An, '1re', '1 e. RR')], 'resubcld', '%s e. RR' % RHO)
    TP = '( ( ( 2 x. _pi ) x. %s ) x. n )' % RHO
    tpr = na([na([na([a1(w, An, '2re', '2 e. RR'), pir], 'remulcld', '( 2 x. _pi ) e. RR'), rhr], 'remulcld', '( ( 2 x. _pi ) x. %s ) e. RR' % RHO), nre],
             'remulcld', '%s e. RR' % TP)
    gwr = na([na([na([L(qre, A0, An)], 'resqcld', '( Q ^ 2 ) e. RR'), tpr], 'readdcld', '( ( Q ^ 2 ) + %s ) e. RR' % TP),
              na([a1(w, An, '4re', '4 e. RR'), pir], 'remulcld', '( 4 x. _pi ) e. RR')], 'readdcld', '%s e. RR' % GW())
    gar = na([gwr, a2r], 'remulcld', '%s e. RR' % GA)
    lr = na([nnn], 'nnrpd', 'n e. RR+')
    nlg = na([na([lr], 'relogcld', '( log ` n ) e. RR')], 'renegcld', '-u ( log ` n ) e. RR')
    h8 = s([a1(w, A0, 'pirp', '_pi e. RR+'), s([w.s([w.s([w.s([], '8re', '8 e. RR'), w.s([], '8pos', '0 < 8')], 'elrpii', '8 e. RR+')], 'a1i', '( %s -> 8 e. RR+ )' % A0),
                                                trp], 'rpmulcld', '( 8 x. T ) e. RR+')], 'rpdivcld', '%s e. RR+' % H8)
    SGA = 'sum_ n e. S %s' % GA
    H2 = '( 2 x. %s )' % H8
    wi = w.s([sfin, nlg, na([gar], 'recnd', '%s e. CC' % GA), h8], 'lswint',
             '( %s -> ( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( %s x. %s ) ) )' % (A0, RHSU, ITG('RR', RHSU, 'u'), H2, SGA))
    Aun = '( %s /\\ n e. S )' % Au
    nb = mk(w, Aun)
    rur = w.s([w.s([], 'simpr', '( %s -> u e. RR )' % Au) and L(sfin, A0, Au), w.s([w.s([], 'id', 'x')] if False else
              [w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (Aun, A0)), w.s([], 'simpr', '( %s -> n e. S )' % Aun)], 'jca', '( %s -> %s )' % (Aun, An)), gar], 'syl',
                   '( %s -> %s e. RR )' % (Aun, GA)), w.s([], '0red', '( %s -> 0 e. RR )' % Aun)], 'ifcld', '( %s -> %s e. RR )' % (Aun, WIF(LOGN, H8, GA)))],
             'fsumrecl', '( %s -> %s e. RR )' % (Au, RHSU))
    pw = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (Au, Au))], 'id', '( %s -> %s )' % (Au, Au)) if False else w.inst('lspwb')], 'id', 'x') if False else None
    pwb = w.s([], 'lspwb', '( %s -> %s <_ %s )' % (Au, LHSU, RHSU))
    sb = s([], 'lspsb', '( ( u e. RR |-> %s ) e. L^1 /\\ %s <_ ( %s x. %s ) )' % (LHSU, LHST, C48, ITG('RR', LHSU, 'u')))
    JL = ITG('RR', LHSU, 'u'); JR = ITG('RR', RHSU, 'u')
    il = s([s([sb], 'simpld', '( u e. RR |-> %s ) e. L^1' % LHSU), s([wi], 'simpld', '( u e. RR |-> %s ) e. L^1' % RHSU), lur, rur, pwb], 'itgle', '%s <_ %s' % (JL, JR))
    c48 = s([s([s([w.s([w.s([w.s([], '4nn0', '4 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; 4 8 e. NN0')], 'nn0rei', '; 4 8 e. RR')], 'a1i', '; 4 8 e. RR'),
                s([tre], 'resqcld', '( T ^ 2 ) e. RR')], 'remulcld', '( ; 4 8 x. ( T ^ 2 ) ) e. RR'),
             a1(w, A0, 'pire', '_pi e. RR'), a1(w, A0, 'pine0', '_pi =/= 0')], 'redivcld', '%s e. RR' % C48)
    c48g = s([s([s([w.s([w.s([w.s([], '4nn0', '4 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; 4 8 e. NN0')], 'nn0rei', '; 4 8 e. RR')], 'a1i', '; 4 8 e. RR'),
                 s([tre], 'resqcld', '( T ^ 2 ) e. RR'), linarith(w, A0, [], '0 <_ ; 4 8', leaves={}), s([tre], 'sqge0d', '0 <_ ( T ^ 2 )')], 'mulge0d',
                '0 <_ ( ; 4 8 x. ( T ^ 2 ) )'), a1(w, A0, 'pirp', '_pi e. RR+')], 'divge0d', '0 <_ %s' % C48)
    jlr = s([s([sb], 'simpld', '( u e. RR |-> %s ) e. L^1' % LHSU), lur], 'itgrecl', '%s e. RR' % JL) if False else \
        s([lur, s([sb], 'simpld', '( u e. RR |-> %s ) e. L^1' % LHSU)], 'itgrecl', '%s e. RR' % JL)
    jrr = s([rur, s([wi], 'simpld', '( u e. RR |-> %s ) e. L^1' % RHSU)], 'itgrecl', '%s e. RR' % JR)
    r2 = s([jlr, jrr, c48, c48g, il], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (C48, JL, C48, JR))
    c1 = s([ltr, s([c48, jlr], 'remulcld', '( %s x. %s ) e. RR' % (C48, JL)), s([c48, jrr], 'remulcld', '( %s x. %s ) e. RR' % (C48, JR)),
            s([sb], 'simprd', '%s <_ ( %s x. %s )' % (LHST, C48, JL)), r2], 'letrd', '%s <_ ( %s x. %s )' % (LHST, C48, JR))
    # C48 x. JR = sum ( 12 T x. GA )
    T12 = '( ; 1 2 x. T )'
    sgac = s([sfin, na([gar], 'recnd', '%s e. CC' % GA)], 'fsumcl', '%s e. CC' % SGA)
    c48c = s([c48], 'recnd', '%s e. CC' % C48)
    h2c = s([s([a1(w, A0, '2re', '2 e. RR'), s([h8], 'rpred', '%s e. RR' % H8)], 'remulcld', '%s e. RR' % H2)], 'recnd', '%s e. CC' % H2)
    q1 = s([s([s([wi], 'simprd', '%s = ( %s x. %s )' % (JR, H2, SGA))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (C48, JR, C48, H2, SGA)),
            s([c48c, h2c, sgac], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (C48, H2, SGA, C48, H2, SGA))], 'eqtr4d',
           '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (C48, JR, C48, H2, SGA))
    d4 = h2d4(w, A0, tre, trp)
    N48 = '( ; 4 8 x. ( T ^ 2 ) )'
    F4 = '( 4 x. T )'
    n48c = s([s([s([w.s([w.s([w.s([], '4nn0', '4 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; 4 8 e. NN0')], 'nn0rei', '; 4 8 e. RR')], 'a1i', '; 4 8 e. RR'),
                 s([tre], 'resqcld', '( T ^ 2 ) e. RR')], 'remulcld', '%s e. RR' % N48)], 'recnd', '%s e. CC' % N48)
    f4c = s([s([a1(w, A0, '4re', '4 e. RR'), tre], 'remulcld', '%s e. RR' % F4)], 'recnd', '%s e. CC' % F4)
    f4ne = s([s([a1(w, A0, '4rp', '4 e. RR+'), trp], 'rpmulcld', '%s e. RR+' % F4)], 'rpne0d', '%s =/= 0' % F4)
    k1 = s([n48c, a1(w, A0, 'picn', '_pi e. CC'), f4c, a1(w, A0, 'pine0', '_pi =/= 0'), f4ne], 'dmdcan2d', '( %s x. %s ) = ( %s / %s )' % (C48, D4, N48, F4))
    cl = Closure(w, A0, {'T': tre})
    k2 = ringeqp_(w, A0, N48, '( %s x. %s )' % (T12, F4), cl)
    t12c = s([s([s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '; 1 2 e. RR'), tre], 'remulcld', '%s e. RR' % T12)], 'recnd', '%s e. CC' % T12)
    k3 = s([s([k2], 'oveq1d', '( %s / %s ) = ( ( %s x. %s ) / %s )' % (N48, F4, T12, F4, F4)), s([t12c, f4c, f4ne], 'divcan4d', '( ( %s x. %s ) / %s ) = %s' % (T12, F4, F4, T12))],
           'eqtrd', '( %s / %s ) = %s' % (N48, F4, T12))
    k4 = s([s([d4], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (C48, H2, C48, D4)), s([k1, k3], 'eqtrd', '( %s x. %s ) = %s' % (C48, D4, T12))], 'eqtrd',
           '( %s x. %s ) = %s' % (C48, H2, T12))
    fm = s([sfin, t12c, na([gar], 'recnd', '%s e. CC' % GA)], 'fsummulc2', '( %s x. %s ) = sum_ n e. S ( %s x. %s )' % (T12, SGA, T12, GA))
    q2_ = s([q1, s([s([k4], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (C48, H2, SGA, T12, SGA)), fm], 'eqtrd',
                   '( ( %s x. %s ) x. %s ) = sum_ n e. S ( %s x. %s )' % (C48, H2, SGA, T12, GA))], 'eqtrd', '( %s x. %s ) = sum_ n e. S ( %s x. %s )' % (C48, JR, T12, GA))
    c2 = s([c1, q2_], 'breqtrd', '%s <_ sum_ n e. S ( %s x. %s )' % (LHST, T12, GA))
    NQ = '( ( n + ( ( Q ^ 2 ) x. T ) ) x. %s )' % AN2
    H100 = '; ; 1 0 0'
    ln = na([na([L(x1, A0, An), na([nnn, a2r, a2g], '3jca', '( n e. NN /\\ %s e. RR /\\ 0 <_ %s )' % (AN2, AN2))], 'jca',
                '( %s /\\ ( n e. NN /\\ %s e. RR /\\ 0 <_ %s ) )' % (X1, AN2, AN2)), w.inst('lsnum')], 'syl', '( %s x. %s ) <_ ( %s x. %s )' % (T12, GA, H100, NQ))
    n100 = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '%s e. NN0' % H100)], 'nn0rei', '%s e. RR' % H100)
    h100 = w.s([n100], 'a1i', '( %s -> %s e. RR )' % (An, H100))
    nqr = na([na([nre, na([na([L(qre, A0, An)], 'resqcld', '( Q ^ 2 ) e. RR'), L(tre, A0, An)], 'remulcld', '( ( Q ^ 2 ) x. T ) e. RR')], 'readdcld',
                 '( n + ( ( Q ^ 2 ) x. T ) ) e. RR'), a2r], 'remulcld', '%s e. RR' % NQ)
    fl = s([sfin, na([L(s([s([s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '; 1 2 e. RR'), tre], 'remulcld', '%s e. RR' % T12)], 'id', 'x') if False else
                      s([s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '; 1 2 e. RR'), tre], 'remulcld', '%s e. RR' % T12), A0, An), gar],
                     'remulcld', '( %s x. %s ) e. RR' % (T12, GA)),
            na([h100, nqr], 'remulcld', '( %s x. %s ) e. RR' % (H100, NQ)), ln], 'fsumle',
           'sum_ n e. S ( %s x. %s ) <_ sum_ n e. S ( %s x. %s )' % (T12, GA, H100, NQ))
    s12 = s([sfin, na([L(s([s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '; 1 2 e. RR'), tre], 'remulcld', '%s e. RR' % T12), A0, An), gar],
                      'remulcld', '( %s x. %s ) e. RR' % (T12, GA))], 'fsumrecl', 'sum_ n e. S ( %s x. %s ) e. RR' % (T12, GA))
    s100 = s([sfin, na([h100, nqr], 'remulcld', '( %s x. %s ) e. RR' % (H100, NQ))], 'fsumrecl', 'sum_ n e. S ( %s x. %s ) e. RR' % (H100, NQ))
    c3 = s([ltr, s12, s100, c2, fl], 'letrd', '%s <_ sum_ n e. S ( %s x. %s )' % (LHST, H100, NQ))
    fm2 = s([sfin, w.s([n100], 'a1i', '( %s -> %s e. RR )' % (A0, H100)) and s([w.s([n100], 'a1i', '( %s -> %s e. RR )' % (A0, H100))], 'recnd', '%s e. CC' % H100),
             na([nqr], 'recnd', '%s e. CC' % NQ)], 'fsummulc2', '( %s x. sum_ n e. S %s ) = sum_ n e. S ( %s x. %s )' % (H100, NQ, H100, NQ))
    w.qed([c3, fm2], 'breqtrrd', S['lspresift'])
    return w


def ringeqp_(w, ante, a, b, cl):
    from mvlib import ringeqp
    return ringeqp(w, ante, a, b, cl)


ALL = {'lspresift': lspresift, 'lspsb': lspsb, 'lspsa': lspsa, 'lscpow': lscpow}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
