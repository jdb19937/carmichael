"""Sortie Z6a, block C: vertical line integrals (z6segl, z6segv, z6aff, z6lvert,
z6rlimle, z6vlcvg, z6vleq, z6shift)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z6alib import *
from cl import Closure, lift, split_imp, formula_of
import lin
from lin import linarith, lineq, nlinarith
import num

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'
JR = '( ( TopOpen ` CCfld ) |`t RR )'
SA = '( C + ( _i x. -u T ) )'
SB = '( C + ( _i x. T ) )'
SEG = '( %s cseg %s )' % (SA, SB)
DT = '( T - -u T )'


def want(lab):
    return not only or lab in only


def cn(w, step):
    return split_imp(formula_of(w, step))[1]


def fvm(w, ante, mp, X, T, val, sub, mem, exs):
    """( ante -> ( mp ` T ) = val ) by fvmpt from the closed substitution step sub: ( x = T -> body = val ),
    mem: ( ante -> T e. X ), exs: closed val e. _V"""
    f = w.s([sub, w.s([], 'eqid', '%s = %s' % (mp, mp)), exs], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (T, X, mp, T, val))
    return w.s([mem, f], 'syl', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, T, val))


def ante_of(lab):
    return split_imp(STATEMENTS[lab])[0]


# ---------------------------------------------------------------- z6segl
def z6segl():
    w = W('z6segl', 'The vertical segment from ` C - i T ` to ` C + i T ` in coordinates: its linear '
          'parametrisation at ` X ` is ` C + i ( -u T + X ( T - -u T ) ) ` , and its direction is ` i ( T - -u T ) ` .')
    A = ante_of('z6segl')
    st = mkst(w, A)
    cc = st([], 'simp1', 'C e. CC'); tc = st([], 'simp2', 'T e. CC'); xc = st([], 'simp3', 'X e. CC')
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    ntc = st([tc], 'negcld', '-u T e. CC')
    dc = st([tc, ntc], 'subcld', '%s e. CC' % DT)
    itc = st([ic, tc], 'mulcld', '( _i x. T ) e. CC'); intc = st([ic, ntc], 'mulcld', '( _i x. -u T ) e. CC')
    e2a = st([cc, itc, intc, w.inst('pnpcan')], 'syl3anc', '( %s - %s ) = ( ( _i x. T ) - ( _i x. -u T ) )' % (SB, SA))
    e2b = st([ic, tc, ntc], 'subdid', '( _i x. %s ) = ( ( _i x. T ) - ( _i x. -u T ) )' % DT)
    e2 = st([e2a, e2b], 'eqtr4d', '( %s - %s ) = ( _i x. %s )' % (SB, SA, DT))
    ID = '( _i x. %s )' % DT
    e1a = st([st([e2], 'oveq2d', '( X x. ( %s - %s ) ) = ( X x. %s )' % (SB, SA, ID))], 'oveq2d',
             '( %s + ( X x. ( %s - %s ) ) ) = ( %s + ( X x. %s ) )' % (SA, SB, SA, SA, ID))
    xid = st([xc, ic, dc], 'mulcld', '( X x. %s ) e. CC' % ID) if False else st([xc, st([ic, dc], 'mulcld', '%s e. CC' % ID)], 'mulcld', '( X x. %s ) e. CC' % ID)
    e1b = st([cc, intc, xid], 'addassd', '( %s + ( X x. %s ) ) = ( C + ( ( _i x. -u T ) + ( X x. %s ) ) )' % (SA, ID, ID))
    m12 = st([xc, ic, dc], 'mul12d', '( X x. %s ) = ( _i x. ( X x. %s ) )' % (ID, DT))
    xd = st([xc, dc], 'mulcld', '( X x. %s ) e. CC' % DT)
    ad = st([ic, ntc, xd], 'adddid', '( _i x. ( -u T + ( X x. %s ) ) ) = ( ( _i x. -u T ) + ( _i x. ( X x. %s ) ) )' % (DT, DT))
    e1c = st([st([m12], 'oveq2d', '( ( _i x. -u T ) + ( X x. %s ) ) = ( ( _i x. -u T ) + ( _i x. ( X x. %s ) ) )' % (ID, DT)), ad], 'eqtr4d',
             '( ( _i x. -u T ) + ( X x. %s ) ) = ( _i x. ( -u T + ( X x. %s ) ) )' % (ID, DT))
    e1d = st([e1c], 'oveq2d', '( C + ( ( _i x. -u T ) + ( X x. %s ) ) ) = ( C + ( _i x. ( -u T + ( X x. %s ) ) ) )' % (ID, DT))
    L = '( %s + ( X x. ( %s - %s ) ) )' % (SA, SB, SA)
    e1 = st([st([e1a, e1b], 'eqtrd', '%s = ( C + ( ( _i x. -u T ) + ( X x. %s ) ) )' % (L, ID)), e1d], 'eqtrd',
            '%s = ( C + ( _i x. ( -u T + ( X x. %s ) ) ) )' % (L, DT))
    w.qed([e1, e2], 'jca', STATEMENTS['z6segl'])
    return w


# ---------------------------------------------------------------- z6segv
def z6segv():
    w = W('z6segv', 'The points ` C + i U ` , ` -u T <_ U <_ T ` , lie on the vertical segment from ` C - i T ` '
          'to ` C + i T ` ( ~ cseglin at ` ( U + T ) / 2 T ` , ~ z6segl ).')
    A = ante_of('z6segv')
    st = mkst(w, A)
    cr = st([], 'simpll', 'C e. RR'); trp = st([], 'simplr', 'T e. RR+'); uin = st([], 'simpr', 'U e. ( -u T [,] T )')
    cl = Closure(w, A, {'C': ('RR', cr), 'T': ('RR+', trp)})
    tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
    b = st([uin, st([ntr, tr, w.inst('elicc2')], 'syl2anc', '( U e. ( -u T [,] T ) <-> ( U e. RR /\\ -u T <_ U /\\ U <_ T ) )')], 'mpbid',
           '( U e. RR /\\ -u T <_ U /\\ U <_ T )')
    ur = st([b], 'simp1d', 'U e. RR'); ulo = st([b], 'simp2d', '-u T <_ U'); uhi = st([b], 'simp3d', 'U <_ T')
    cl.leaf('U', 'RR', ur)
    NUM = '( U - -u T )'
    drp = st([cl.mem(DT, 'RR'), linarith(w, A, [cl.gt0('T')], '0 < %s' % DT, closure=cl)], 'elrpd', '%s e. RR+' % DT)
    X = '( %s / %s )' % (NUM, DT)
    numr = cl.mem(NUM, 'RR')
    xr = st([numr, drp], 'rerpdivcld', '%s e. RR' % X)
    x0 = st([numr, drp, linarith(w, A, [ulo], '0 <_ %s' % NUM, closure=cl)], 'divge0d', '0 <_ %s' % X)
    x1 = st([linarith(w, A, [uhi], '%s <_ %s' % (NUM, DT), closure=cl), sy2(w, A, numr, drp, 'divle1le', '( %s <_ 1 <-> %s <_ %s )' % (X, NUM, DT))], 'mpbird', '%s <_ 1' % X)
    x01 = st([st([xr, x0, x1], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 )' % (X, X, X)), w.inst('elicc01')], 'sylibr', '%s e. ( 0 [,] 1 )' % X)
    cc = st([cr], 'recnd', 'C e. CC'); tc = st([tr], 'recnd', 'T e. CC')
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    sac = st([cc, st([ic, st([tc], 'negcld', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % SA)
    sbc = st([cc, st([ic, tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SB)
    L = '( %s + ( %s x. ( %s - %s ) ) )' % (SA, X, SB, SA)
    inseg = st([sac, sbc, x01, w.inst('cseglin')], 'syl3anc', '%s e. %s' % (L, SEG))
    xc = st([xr], 'recnd', '%s e. CC' % X)
    sl = st([st([cc, tc, xc], '3jca', '( C e. CC /\\ T e. CC /\\ %s e. CC )' % X), w.inst('z6segl')], 'syl',
            '( %s = ( C + ( _i x. ( -u T + ( %s x. %s ) ) ) ) /\\ ( %s - %s ) = ( _i x. %s ) )' % (L, X, DT, SB, SA, DT))
    e1 = st([sl], 'simpld', '%s = ( C + ( _i x. ( -u T + ( %s x. %s ) ) ) )' % (L, X, DT))
    dc = st([drp], 'rpcnd', '%s e. CC' % DT); dne = st([drp], 'rpne0d', '%s =/= 0' % DT)
    numc = st([numr], 'recnd', '%s e. CC' % NUM)
    dcan = st([numc, dc, dne], 'divcan1d', '( %s x. %s ) = %s' % (X, DT, NUM))
    pn = st([st([tc], 'negcld', '-u T e. CC'), st([ur], 'recnd', 'U e. CC'), w.inst('pncan3')], 'syl2anc', '( -u T + %s ) = U' % NUM)
    inner = st([st([dcan], 'oveq2d', '( -u T + ( %s x. %s ) ) = ( -u T + %s )' % (X, DT, NUM)), pn], 'eqtrd', '( -u T + ( %s x. %s ) ) = U' % (X, DT))
    e2 = st([st([inner], 'oveq2d', '( _i x. ( -u T + ( %s x. %s ) ) ) = ( _i x. U )' % (X, DT))], 'oveq2d',
            '( C + ( _i x. ( -u T + ( %s x. %s ) ) ) ) = ( C + ( _i x. U ) )' % (X, DT))
    e = st([e1, e2], 'eqtrd', '%s = ( C + ( _i x. U ) )' % L)
    w.qed([e, inseg], 'eqeltrd' if False else 'eqeltrrd', '( %s -> ( C + ( _i x. U ) ) e. %s )' % (A, SEG))
    return w


# ---------------------------------------------------------------- z6aff
def z6aff():
    w = W('z6aff', 'The affine change of variables ` u = A + t ( B - A ) ` for a function continuous on ` [ A , B ] ` : '
          'the indefinite integral ( ~ ftc1cn , ~ ftc1a ) composed with the affine map is differentiated by the '
          'chain rule ( ~ dvmptco ) and integrated back over ` ( 0 , 1 ) ` ( ~ ftc2 ).  C0\'s ~ ditgaff on '
          'a general interval.')
    A = ante_of('z6aff')
    st = mkst(w, A)
    ar = st([], 'simplll', 'A e. RR'); br = st([], 'simpllr', 'B e. RR'); lt = st([], 'simplr', 'A < B')
    hcn = st([], 'simpr', 'H e. ( ( A [,] B ) -cn-> CC )')
    ABo = '( A (,) B )'; ABc = '( A [,] B )'
    ale = st([ar, br, lt], 'ltled', 'A <_ B')
    ac = st([ar], 'recnd', 'A e. CC'); bc = st([br], 'recnd', 'B e. CC')
    hf = st([hcn, w.inst('cncff')], 'syl', 'H : %s --> CC' % ABc)
    ssoc = a1c(w, A, 'ioossicc', '%s C_ %s' % (ABo, ABc))
    F = '( b e. %s |-> ( H ` b ) )' % ABo
    FY = '( y e. %s |-> ( H ` y ) )' % ABo
    fres = st([hf, ssoc], 'feqresmpt', '( H |` %s ) = %s' % (ABo, F))
    rcn = st([ssoc, hcn, w.inst('rescncf')], 'sylc', '( H |` %s ) e. ( %s -cn-> CC )' % (ABo, ABo))
    fcn = st([fres, rcn], 'eqeltrrd' if False else 'eqeltrd', '%s e. ( %s -cn-> CC )' % (F, ABo)) if False else \
        st([st([fres], 'eqcomd', '%s = ( H |` %s )' % (F, ABo)), rcn], 'eqeltrd', '%s e. ( %s -cn-> CC )' % (F, ABo))
    hibl = st([ar, br, hcn, w.inst('cniccibl')], 'syl3anc', 'H e. L^1')
    hm = st([hf], 'feqmptd', 'H = ( b e. %s |-> ( H ` b ) )' % ABc)
    hmibl = st([hm, hibl], 'eqeltrrd', '( b e. %s |-> ( H ` b ) ) e. L^1' % ABc)
    Ay = '( %s /\\ b e. %s )' % (A, ABc)
    hyc = w.s([lift(w, hf, Ay), w.s([], 'simpr', '( %s -> b e. %s )' % (Ay, ABc))], 'ffvelcdmd', '( %s -> ( H ` b ) e. CC )' % Ay)
    fibl = st([ssoc, a1c(w, A, 'ioombl', '%s e. dom vol' % ABo), hyc, hmibl], 'iblss', '%s e. L^1' % F)
    P = '( x e. %s |-> S. ( A (,) x ) ( %s ` s ) _d s )' % (ABc, F)
    eP = w.s([], 'eqid', '%s = %s' % (P, P))
    d1 = st([eP, ar, br, ale, fcn, fibl], 'ftc1cn', '( RR _D %s ) = %s' % (P, F))
    ff = st([fcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (F, ABo))
    pcn = st([eP, ar, br, ale, st([], 'ssidd', '%s C_ %s' % (ABo, ABo)), a1c(w, A, 'ioossre', '%s C_ RR' % ABo), fibl, ff], 'ftc1a',
             '%s e. ( %s -cn-> CC )' % (P, ABc))
    pf = st([pcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (P, ABc))
    # the derivative of P on the open interval
    PY = '( y e. %s |-> ( %s ` y ) )' % (ABo, P)
    r1 = st([pf, ssoc], 'feqresmpt', '( %s |` %s ) = %s' % (P, ABo, PY))
    iccre = st([ar, br, w.inst('iccssre')], 'syl2anc', '%s C_ RR' % ABc)
    tg = w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)
    jtop = w.s([tg, w.s([], 'retop', '( topGen ` ran (,) ) e. Top')], 'eqeltrri', '%s e. Top' % JR)
    iop = w.s([w.s([], 'iooretop', '%s e. ( topGen ` ran (,) )' % ABo), tg], 'eleqtri', '%s e. %s' % (ABo, JR))
    ntr = w.s([jtop, iop, w.inst('isopn3i')], 'mp2an', '( ( int ` %s ) ` %s ) = %s' % (JR, ABo, ABo))
    ioore = a1c(w, A, 'ioossre', '%s C_ RR' % ABo)
    r2a = st([st([a1c(w, A, 'ax-resscn', 'RR C_ CC'), pf], 'jca', '( RR C_ CC /\\ %s : %s --> CC )' % (P, ABc)), st([iccre, ioore], 'jca', '( %s C_ RR /\\ %s C_ RR )' % (ABc, ABo)),
              w.s([w.s([], 'eqid', '%s = %s' % (TOP, TOP)), w.s([], 'eqid', '%s = %s' % (JR, JR))], 'dvres',
                  '( ( ( RR C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ RR /\\ %s C_ RR ) ) -> ( RR _D ( %s |` %s ) ) = ( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (P, ABc, ABc, ABo, P, ABo, P, JR, ABo))],
             'syl2anc', '( RR _D ( %s |` %s ) ) = ( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) )' % (P, ABo, P, JR, ABo))
    r2 = st([r2a, st([a1(w, A, ntr, '( ( int ` %s ) ` %s ) = %s' % (JR, ABo, ABo))], 'reseq2d', '( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( ( RR _D %s ) |` %s )' % (P, JR, ABo, P, ABo))],
            'eqtrd', '( RR _D ( %s |` %s ) ) = ( ( RR _D %s ) |` %s )' % (P, ABo, P, ABo))
    r3 = st([d1], 'reseq1d', '( ( RR _D %s ) |` %s ) = ( %s |` %s )' % (P, ABo, F, ABo))
    r4 = a1(w, A, w.s([w.s([], 'ssid', '%s C_ %s' % (ABo, ABo)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (F, ABo, F)), '( %s |` %s ) = %s' % (F, ABo, F))
    dc0 = st([st([r1], 'oveq2d', '( RR _D ( %s |` %s ) ) = ( RR _D %s )' % (P, ABo, PY)), st([r2, st([r3, r4], 'eqtrd', '( ( RR _D %s ) |` %s ) = %s' % (P, ABo, F))], 'eqtrd',
                                                                                         '( RR _D ( %s |` %s ) ) = %s' % (P, ABo, F))], 'eqtr3d', '( RR _D %s ) = %s' % (PY, F))
    fy = a1(w, A, w.s([w.s([], 'fveq2', '( b = y -> ( H ` b ) = ( H ` y ) )')], 'cbvmptv', '%s = %s' % (F, FY)), '%s = %s' % (F, FY))
    dc0 = st([dc0, fy], 'eqtrd', '( RR _D %s ) = %s' % (PY, FY))
    # the composite Q
    LN = lambda a: '( A + ( %s x. ( B - A ) ) )' % a
    Q = '( a e. ( 0 [,] 1 ) |-> ( %s ` %s ) )' % (P, LN('a'))
    axr = st([ar], 'rexrd', 'A e. RR*'); bxr = st([br], 'rexrd', 'B e. RR*')
    aab = st([axr, bxr, ale, w.inst('lbicc2')], 'syl3anc', 'A e. %s' % ABc)
    bab = st([axr, bxr, ale, w.inst('ubicc2')], 'syl3anc', 'B e. %s' % ABc)
    segss = st([st([ar, br], 'jca', '( A e. RR /\\ B e. RR )'), st([aab, bab], 'jca', '( A e. %s /\\ B e. %s )' % (ABc, ABc)), w.inst('csegicc')], 'syl2anc',
               '( A cseg B ) C_ %s' % ABc)
    abc = st([ac, bc], 'jca', '( A e. CC /\\ B e. CC )')
    qcn = st([abc, st([pcn, segss], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( A cseg B ) C_ %s )' % (P, ABc, ABc)), a1c(w, A, 'ssid', '( 0 [,] 1 ) C_ ( 0 [,] 1 )'), w.inst('cseglincnf')],
             'syl3anc', '%s e. ( ( 0 [,] 1 ) -cn-> CC )' % Q)
    Aa = '( %s /\\ a e. ( 0 [,] 1 ) )' % A
    sa = mkst(w, Aa)
    lnseg = sa([lift(w, ac, Aa), lift(w, bc, Aa), sa([], 'simpr', 'a e. ( 0 [,] 1 )'), w.inst('cseglin')], 'syl3anc', '%s e. ( A cseg B )' % LN('a'))
    lnab = sa([lift(w, segss, Aa), lnseg], 'sseldd', '%s e. %s' % (LN('a'), ABc))
    bodyc = sa([lift(w, pf, Aa), lnab], 'ffvelcdmd', '( %s ` %s ) e. CC' % (P, LN('a')))
    dvq0 = st([a1c(w, A, 'ax-resscn', 'RR C_ CC'), a1c(w, A, 'unitssre', '( 0 [,] 1 ) C_ RR'), bodyc, w.s([], 'eqid', '%s = %s' % (JR, JR)), w.s([], 'eqid', '%s = %s' % (TOP, TOP)),
               a1c(w, A, 'unitntr', '( ( int ` %s ) ` ( 0 [,] 1 ) ) = ( 0 (,) 1 )' % JR)], 'dvmptntr',
              '( RR _D %s ) = ( RR _D ( a e. ( 0 (,) 1 ) |-> ( %s ` %s ) ) )' % (Q, P, LN('a')))
    Ao = '( %s /\\ a e. ( 0 (,) 1 ) )' % A
    so = mkst(w, Ao)
    lnio = so([so([lift(w, ar, Ao), lift(w, br, Ao), lift(w, lt, Ao)], '3jca', '( A e. RR /\\ B e. RR /\\ A < B )'), so([], 'simpr', 'a e. ( 0 (,) 1 )'), w.inst('ioolin')],
              'syl2anc', '%s e. %s' % (LN('a'), ABo))
    bac = so([lift(w, bc, Ao), lift(w, ac, Ao)], 'subcld', '( B - A ) e. CC')
    Ay2 = '( %s /\\ y e. %s )' % (A, ABo)
    sy_ = mkst(w, Ay2)
    yab = sy_([lift(w, ssoc, Ay2), sy_([], 'simpr', 'y e. %s' % ABo)], 'sseldd', 'y e. %s' % ABc)
    pyc = sy_([lift(w, pf, Ay2), yab], 'ffvelcdmd', '( %s ` y ) e. CC' % P)
    hyc2 = sy_([lift(w, hf, Ay2), yab], 'ffvelcdmd', '( H ` y ) e. CC')
    rr = a1c(w, A, 'reelprrecn', 'RR e. { RR , CC }')
    da = st([ac, bc, w.inst('dvcseglin')], 'syl2anc', '( RR _D ( a e. ( 0 (,) 1 ) |-> %s ) ) = ( a e. ( 0 (,) 1 ) |-> ( B - A ) )' % LN('a'))
    se = w.s([], 'fveq2', '( y = %s -> ( %s ` y ) = ( %s ` %s ) )' % (LN('a'), P, P, LN('a')))
    sf = w.s([], 'fveq2', '( y = %s -> ( H ` y ) = ( H ` %s ) )' % (LN('a'), LN('a')))
    KB = lambda a: '( ( H ` %s ) x. ( B - A ) )' % LN(a)
    K = '( a e. ( 0 (,) 1 ) |-> %s )' % KB('a')
    dco = st([rr, rr, lnio, bac, pyc, hyc2, da, dc0, se, sf], 'dvmptco', '( RR _D ( a e. ( 0 (,) 1 ) |-> ( %s ` %s ) ) ) = %s' % (P, LN('a'), K))
    dq = st([dvq0, dco], 'eqtrd', '( RR _D %s ) = %s' % (Q, K))
    hseg = st([hcn, segss], 'jca', '( H e. ( %s -cn-> CC ) /\\ ( A cseg B ) C_ %s )' % (ABc, ABc))
    kcn = st([abc, hseg, a1c(w, A, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )'), w.inst('lintcnlem')], 'syl3anc', '%s e. ( ( 0 (,) 1 ) -cn-> CC )' % K)
    kibl = st([abc, hseg, w.inst('lintibl')], 'syl2anc', '%s e. L^1' % K)
    dcn = st([dq, kcn], 'eqeltrd', '( RR _D %s ) e. ( ( 0 (,) 1 ) -cn-> CC )' % Q)
    dibl = st([dq, kibl], 'eqeltrd', '( RR _D %s ) e. L^1' % Q)
    f2 = st([st([], '0red', '0 e. RR'), st([], '1red', '1 e. RR'), a1c(w, A, '0le1', '0 <_ 1'), dcn, dibl, qcn], 'ftc2',
            'S. ( 0 (,) 1 ) ( ( RR _D %s ) ` t ) _d t = ( ( %s ` 1 ) - ( %s ` 0 ) )' % (Q, Q, Q))
    # the integrand
    At = '( %s /\\ t e. ( 0 (,) 1 ) )' % A
    stt = mkst(w, At)
    kv, kval = mpv(w, At, 'a', '( 0 (,) 1 )', KB('a'), 't', stt([], 'simpr', 't e. ( 0 (,) 1 )'))
    ig = stt([stt([lift(w, dq, At)], 'fveq1d', '( ( RR _D %s ) ` t ) = ( %s ` t )' % (Q, K)), kv], 'eqtrd', '( ( RR _D %s ) ` t ) = %s' % (Q, KB('t')))
    itq = st([ig], 'itgeq2dv', 'S. ( 0 (,) 1 ) ( ( RR _D %s ) ` t ) _d t = S. ( 0 (,) 1 ) %s _d t' % (Q, KB('t')))
    # Q ` 1 and Q ` 0
    def lnsub(T):
        e = w.s([], 'oveq1', '( a = %s -> ( a x. ( B - A ) ) = ( %s x. ( B - A ) ) )' % (T, T))
        e = w.s([e], 'oveq2d', '( a = %s -> %s = %s )' % (T, LN('a'), LN(T)))
        return w.s([e], 'fveq2d', '( a = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (T, P, LN('a'), P, LN(T)))

    def psub(T):
        e = w.s([], 'oveq2', '( x = %s -> ( A (,) x ) = ( A (,) %s ) )' % (T, T))
        return w.s([e, w.inst('itgeq1')], 'syl', '( x = %s -> S. ( A (,) x ) ( %s ` s ) _d s = S. ( A (,) %s ) ( %s ` s ) _d s )' % (T, F, T, F))
    q1 = fvm(w, A, Q, '( 0 [,] 1 )', '1', '( %s ` %s )' % (P, LN('1')), lnsub('1'), a1c(w, A, '1elunit', '1 e. ( 0 [,] 1 )'), w.s([], 'fvex', '( %s ` %s ) e. _V' % (P, LN('1'))))
    bma = st([bc, ac], 'subcld', '( B - A ) e. CC')
    ln1 = st([st([st([bma], 'mullidd', '( 1 x. ( B - A ) ) = ( B - A )')], 'oveq2d', '%s = ( A + ( B - A ) )' % LN('1')), st([ac, bc, w.inst('pncan3')], 'syl2anc', '( A + ( B - A ) ) = B')],
             'eqtrd', '%s = B' % LN('1'))
    PB = 'S. ( A (,) B ) ( %s ` s ) _d s' % F
    pbv = fvm(w, A, P, ABc, 'B', PB, psub('B'), bab, w.s([], 'itgex', '%s e. _V' % PB))
    qv1 = st([st([q1, st([ln1], 'fveq2d', '( %s ` %s ) = ( %s ` B )' % (P, LN('1'), P))], 'eqtrd', '( %s ` 1 ) = ( %s ` B )' % (Q, P)), pbv], 'eqtrd', '( %s ` 1 ) = %s' % (Q, PB))
    q0 = fvm(w, A, Q, '( 0 [,] 1 )', '0', '( %s ` %s )' % (P, LN('0')), lnsub('0'), a1c(w, A, '0elunit', '0 e. ( 0 [,] 1 )'), w.s([], 'fvex', '( %s ` %s ) e. _V' % (P, LN('0'))))
    ln0 = st([st([st([bma], 'mul02d', '( 0 x. ( B - A ) ) = 0')], 'oveq2d', '%s = ( A + 0 )' % LN('0')), st([ac], 'addridd', '( A + 0 ) = A')], 'eqtrd', '%s = A' % LN('0'))
    PA = 'S. ( A (,) A ) ( %s ` s ) _d s' % F
    pav = fvm(w, A, P, ABc, 'A', PA, psub('A'), aab, w.s([], 'itgex', '%s e. _V' % PA))
    i0 = w.s([w.s([], 'iooid', '( A (,) A ) = (/)'), w.inst('itgeq1')], 'ax-mp', '%s = S. (/) ( %s ` s ) _d s' % (PA, F))
    i00 = a1(w, A, w.s([i0, w.s([], 'itg0', 'S. (/) ( %s ` s ) _d s = 0' % F)], 'eqtri', '%s = 0' % PA), '%s = 0' % PA)
    qv0 = st([st([st([q0, st([ln0], 'fveq2d', '( %s ` %s ) = ( %s ` A )' % (P, LN('0'), P))], 'eqtrd', '( %s ` 0 ) = ( %s ` A )' % (Q, P)), pav], 'eqtrd', '( %s ` 0 ) = %s' % (Q, PA)), i00],
             'eqtrd', '( %s ` 0 ) = 0' % Q)
    pbc = st([pf, bab], 'ffvelcdmd', '( %s ` B ) e. CC' % P)
    pbc2 = st([pbv, pbc], 'eqeltrrd', '%s e. CC' % PB)
    dif = st([st([qv1, qv0], 'oveq12d', '( ( %s ` 1 ) - ( %s ` 0 ) ) = ( %s - 0 )' % (Q, Q, PB)), st([pbc2], 'subid1d', '( %s - 0 ) = %s' % (PB, PB))], 'eqtrd',
             '( ( %s ` 1 ) - ( %s ` 0 ) ) = %s' % (Q, Q, PB))
    # S. ( A (,) B ) ( F ` s ) _d s = S. ( A (,) B ) ( H ` u ) _d u
    As = '( %s /\\ s e. %s )' % (A, ABo)
    fsv = fvm(w, As, F, ABo, 's', '( H ` s )', w.s([], 'fveq2', '( b = s -> ( H ` b ) = ( H ` s ) )'), w.s([], 'simpr', '( %s -> s e. %s )' % (As, ABo)), w.s([], 'fvex', '( H ` s ) e. _V'))
    e3 = st([fsv], 'itgeq2dv', '%s = S. %s ( H ` s ) _d s' % (PB, ABo))
    e4 = a1(w, A, w.s([w.s([], 'fveq2', '( s = u -> ( H ` s ) = ( H ` u ) )')], 'cbvitgv', 'S. %s ( H ` s ) _d s = S. %s ( H ` u ) _d u' % (ABo, ABo)),
            'S. %s ( H ` s ) _d s = S. %s ( H ` u ) _d u' % (ABo, ABo))
    ITK = 'S. ( 0 (,) 1 ) %s _d t' % KB('t')
    tot = st([st([itq, f2], 'eqtr3d', '%s = ( ( %s ` 1 ) - ( %s ` 0 ) )' % (ITK, Q, Q)), dif], 'eqtrd', '%s = %s' % (ITK, PB))
    tot2 = st([st([tot, e3], 'eqtrd', '%s = S. %s ( H ` s ) _d s' % (ITK, ABo)), e4], 'eqtrd', '%s = S. %s ( H ` u ) _d u' % (ITK, ABo))
    w.qed([tot2], 'eqcomd', STATEMENTS['z6aff'].replace(A + ' -> ', '( %s -> ' % A, 1) if False else '( %s -> S. %s ( H ` u ) _d u = %s )' % (A, ABo, ITK))
    return w


# ---------------------------------------------------------------- z6lvert
XC = '( -u T [,] T )'
XO = '( -u T (,) T )'
WU = '( C + ( _i x. u ) )'
WV = '( C + ( _i x. v ) )'


def z6lvert():
    w = W('z6lvert', 'A segment integral along the vertical segment from ` C - i T ` to ` C + i T ` in coordinates: '
          '` _i S. ( -u T (,) T ) G ( C + i u ) _d u ` , with the integrand integrable ( ~ lintval , ~ z6segl , '
          'the affine substitution ~ z6aff ).')
    A = ante_of('z6lvert')
    st = mkst(w, A)
    cr = st([], 'simpll', 'C e. RR'); trp = st([], 'simplr', 'T e. RR+')
    gcn = st([], 'simprl', 'G e. ( D -cn-> CC )'); ss = st([], 'simprr', '%s C_ D' % SEG)
    cl = Closure(w, A, {'C': ('RR', cr), 'T': ('RR+', trp)})
    tr = cl.mem('T', 'RR'); ntr = cl.mem('-u T', 'RR')
    cc = st([cr], 'recnd', 'C e. CC'); tc = st([tr], 'recnd', 'T e. CC')
    gf = st([gcn, w.inst('cncff')], 'syl', 'G : D --> CC')
    # continuity of u |-> G ( C + i u ) on the closed interval
    ussr = st([ntr, tr, w.inst('iccssre')], 'syl2anc', '%s C_ RR' % XC)
    usscn = st([ussr, a1c(w, A, 'ax-resscn', 'RR C_ CC')], 'sstrd', '%s C_ CC' % XC)
    sscc = a1c(w, A, 'ssid', 'CC C_ CC')
    keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    idc = st([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> CC )' % (XC, XC))
    xcst = st([cc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( v e. %s |-> C ) e. ( %s -cn-> CC )' % (XC, XC))
    icst = st([a1c(w, A, 'ax-icn', '_i e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( v e. %s |-> _i ) e. ( %s -cn-> CC )' % (XC, XC))
    iu = st([icst, idc], 'mulcncf', '( v e. %s |-> ( _i x. v ) ) e. ( %s -cn-> CC )' % (XC, XC))
    adc = w.s([w.s([keq], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A, TOP, TOP, TOP))
    MI = '( v e. %s |-> %s )' % (XC, WV)
    micn = st([keq, adc, xcst, iu], 'cncfmpt2f', '%s e. ( %s -cn-> CC )' % (MI, XC))
    Av = '( %s /\\ v e. %s )' % (A, XC)
    sv = mkst(w, Av)
    useg = sv([sv([lift(w, cr, Av), lift(w, trp, Av)], 'jca', '( C e. RR /\\ T e. RR+ )'), sv([], 'simpr', 'v e. %s' % XC), w.inst('z6segv')], 'syl2anc', '%s e. %s' % (WV, SEG))
    ud = sv([lift(w, ss, Av), useg], 'sseldd', '%s e. D' % WV)
    mif = st([ud, w.s([], 'eqid', '%s = %s' % (MI, MI))], 'fmptd', '%s : %s --> D' % (MI, XC))
    dcc = st([gcn, w.inst('cncfrss')], 'syl', 'D C_ CC')
    mis = st([mif, st([dcc, micn, w.inst('cncfcdm')], 'syl2anc', '( %s e. ( %s -cn-> D ) <-> %s : %s --> D )' % (MI, XC, MI, XC))], 'mpbird', '%s e. ( %s -cn-> D )' % (MI, XC))
    co = st([mis, gcn], 'cncfco', '( G o. %s ) e. ( %s -cn-> CC )' % (MI, XC))
    H = '( v e. %s |-> ( G ` %s ) )' % (XC, WV)
    cof = st([gf, ud], 'cofmpt', '( G o. %s ) = %s' % (MI, H))
    hcn = st([cof, co], 'eqeltrrd' if False else 'eqeltrd', '%s e. ( %s -cn-> CC )' % (H, XC)) if False else \
        st([st([cof], 'eqcomd', '%s = ( G o. %s )' % (H, MI)), co], 'eqeltrd', '%s e. ( %s -cn-> CC )' % (H, XC))
    HU = '( u e. %s |-> ( G ` %s ) )' % (XC, WU)
    cbh = a1(w, A, w.s([w.s([w.s([w.s([], 'oveq2', '( v = u -> ( _i x. v ) = ( _i x. u ) )')], 'oveq2d', '( v = u -> %s = %s )' % (WV, WU))], 'fveq2d', '( v = u -> ( G ` %s ) = ( G ` %s ) )' % (WV, WU))],
                       'cbvmptv', '%s = %s' % (H, HU)), '%s = %s' % (H, HU))
    hucn = st([cbh, hcn], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (HU, XC))
    hibl = st([ntr, tr, hucn, w.inst('cniccibl')], 'syl3anc', '%s e. L^1' % HU)
    Au = '( %s /\\ u e. %s )' % (A, XC)
    su = mkst(w, Au)
    udu = su([lift(w, ss, Au), su([su([lift(w, cr, Au), lift(w, trp, Au)], 'jca', '( C e. RR /\\ T e. RR+ )'), su([], 'simpr', 'u e. %s' % XC), w.inst('z6segv')], 'syl2anc', '%s e. %s' % (WU, SEG))],
              'sseldd', '%s e. D' % WU)
    gvc = su([lift(w, gf, Au), udu], 'ffvelcdmd', '( G ` %s ) e. CC' % WU)
    MO = '( u e. %s |-> ( G ` %s ) )' % (XO, WU)
    oibl = st([a1c(w, A, 'ioossicc', '%s C_ %s' % (XO, XC)), a1c(w, A, 'ioombl', '%s e. dom vol' % XO), gvc, hibl], 'iblss', '%s e. L^1' % MO)
    # the substitution
    ltT = linarith(w, A, [cl.gt0('T')], '-u T < T', closure=cl)
    aff = st([st([st([ntr, tr], 'jca', '( -u T e. RR /\\ T e. RR )'), ltT], 'jca', '( ( -u T e. RR /\\ T e. RR ) /\\ -u T < T )'), hcn], 'jca',
             '( ( ( -u T e. RR /\\ T e. RR ) /\\ -u T < T ) /\\ %s e. ( ( -u T [,] T ) -cn-> CC ) )' % H)
    LNt = '( -u T + ( t x. %s ) )' % DT
    KB = '( ( %s ` %s ) x. %s )' % (H, LNt, DT)
    IK = 'S. ( 0 (,) 1 ) %s _d t' % KB
    zaff = st([aff, w.inst('z6aff')], 'syl', 'S. %s ( %s ` u ) _d u = %s' % (XO, H, IK))
    Ao = '( %s /\\ u e. %s )' % (A, XO)
    so = mkst(w, Ao)
    uxc = so([lift(w, a1c(w, A, 'ioossicc', '%s C_ %s' % (XO, XC)), Ao), so([], 'simpr', 'u e. %s' % XO)], 'sseldd', 'u e. %s' % XC)
    hv = fvm(w, Ao, H, XC, 'u', '( G ` %s )' % WU, w.s([w.s([w.s([], 'oveq2', '( v = u -> ( _i x. v ) = ( _i x. u ) )')], 'oveq2d', '( v = u -> %s = %s )' % (WV, WU))], 'fveq2d',
                                                          '( v = u -> ( G ` %s ) = ( G ` %s ) )' % (WV, WU)), uxc, w.s([], 'fvex', '( G ` %s ) e. _V' % WU))
    IG = 'S. %s ( G ` %s ) _d u' % (XO, WU)
    ih = st([hv], 'itgeq2dv', 'S. %s ( %s ` u ) _d u = %s' % (XO, H, IG))
    # the segment integral
    L = '( %s + ( t x. ( %s - %s ) ) )' % (SA, SB, SA)
    sac = st([cc, st([a1c(w, A, 'ax-icn', '_i e. CC'), st([tc], 'negcld', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % SA)
    sbc = st([cc, st([a1c(w, A, 'ax-icn', '_i e. CC'), tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SB)
    gv = st([gcn, w.inst('elex')], 'syl', 'G e. _V')
    lv = st([gv, sac, sbc, w.inst('lintval')], 'syl3anc', '%s = S. ( 0 (,) 1 ) ( ( G ` %s ) x. ( %s - %s ) ) _d t' % (LI('G', 'C', 'T'), L, SB, SA))
    At = '( %s /\\ t e. ( 0 (,) 1 ) )' % A
    stt = mkst(w, At)
    tt = stt([], 'simpr', 't e. ( 0 (,) 1 )')
    tcc = stt([stt([tt, w.inst('elioore')], 'syl', 't e. RR')], 'recnd', 't e. CC')
    sl = stt([stt([lift(w, cc, At), lift(w, tc, At), tcc], '3jca', '( C e. CC /\\ T e. CC /\\ t e. CC )'), w.inst('z6segl')], 'syl',
             '( %s = ( C + ( _i x. %s ) ) /\\ ( %s - %s ) = ( _i x. %s ) )' % (L, LNt, SB, SA, DT))
    e1 = stt([sl], 'simpld', '%s = ( C + ( _i x. %s ) )' % (L, LNt)); e2 = stt([sl], 'simprd', '( %s - %s ) = ( _i x. %s )' % (SB, SA, DT))
    GL = '( G ` ( C + ( _i x. %s ) ) )' % LNt
    lio = stt([stt([lift(w, ntr, At), lift(w, tr, At), lift(w, ltT, At)], '3jca', '( -u T e. RR /\\ T e. RR /\\ -u T < T )'), tt, w.inst('ioolin')], 'syl2anc', '%s e. %s' % (LNt, XO))
    lic = stt([lift(w, a1c(w, A, 'ioossicc', '%s C_ %s' % (XO, XC)), At), lio], 'sseldd', '%s e. %s' % (LNt, XC))
    sub = w.s([w.s([w.s([], 'oveq2', '( v = %s -> ( _i x. v ) = ( _i x. %s ) )' % (LNt, LNt))], 'oveq2d', '( v = %s -> %s = ( C + ( _i x. %s ) ) )' % (LNt, WV, LNt))], 'fveq2d',
              '( v = %s -> ( G ` %s ) = %s )' % (LNt, WV, GL))
    hl = fvm(w, At, H, XC, LNt, GL, sub, lic, w.s([], 'fvex', '%s e. _V' % GL))
    gd = stt([stt([e1], 'fveq2d', '( G ` %s ) = %s' % (L, GL)), e2], 'oveq12d', '( ( G ` %s ) x. ( %s - %s ) ) = ( %s x. ( _i x. %s ) )' % (L, SB, SA, GL, DT))
    # G ( C + i LNt ) e. CC
    Tu = mkst(w, At)
    ld = Tu([lift(w, ss, At), Tu([Tu([lift(w, cr, At), lift(w, trp, At)], 'jca', '( C e. RR /\\ T e. RR+ )'), lic, w.inst('z6segv')], 'syl2anc', '( C + ( _i x. %s ) ) e. %s' % (LNt, SEG))], 'sseldd',
            '( C + ( _i x. %s ) ) e. D' % LNt)
    glc = Tu([lift(w, gf, At), ld], 'ffvelcdmd', '%s e. CC' % GL)
    dtc = lift(w, cl.mem(DT, 'CC'), At)
    m12 = stt([glc, stt([], 'ax-icn' if False else 'ax-icn', '_i e. CC') if False else lift(w, a1c(w, A, 'ax-icn', '_i e. CC'), At), dtc], 'mul12d',
              '( %s x. ( _i x. %s ) ) = ( _i x. ( %s x. %s ) )' % (GL, DT, GL, DT))
    hb = stt([stt([hl], 'eqcomd', '%s = ( %s ` %s )' % (GL, H, LNt))], 'oveq1d', '( %s x. %s ) = %s' % (GL, DT, KB))
    pt = stt([stt([gd, m12], 'eqtrd', '( ( G ` %s ) x. ( %s - %s ) ) = ( _i x. ( %s x. %s ) )' % (L, SB, SA, GL, DT)), stt([hb], 'oveq2d', '( _i x. ( %s x. %s ) ) = ( _i x. %s )' % (GL, DT, KB))],
             'eqtrd', '( ( G ` %s ) x. ( %s - %s ) ) = ( _i x. %s )' % (L, SB, SA, KB))
    ie = st([pt], 'itgeq2dv', 'S. ( 0 (,) 1 ) ( ( G ` %s ) x. ( %s - %s ) ) _d t = S. ( 0 (,) 1 ) ( _i x. %s ) _d t' % (L, SB, SA, KB))
    segx = st([st([ntr, tr], 'jca', '( -u T e. RR /\\ T e. RR )'), st([st([st([ntr], 'rexrd', '-u T e. RR*'), st([tr], 'rexrd', 'T e. RR*'), st([ntr, tr, ltT], 'ltled', '-u T <_ T'), w.inst('lbicc2')], 'syl3anc', '-u T e. %s' % XC),
                                                                             st([st([ntr], 'rexrd', '-u T e. RR*'), st([tr], 'rexrd', 'T e. RR*'), st([ntr, tr, ltT], 'ltled', '-u T <_ T'), w.inst('ubicc2')], 'syl3anc', 'T e. %s' % XC)],
                                                                            'jca', '( -u T e. %s /\\ T e. %s )' % (XC, XC)), w.inst('csegicc')], 'syl2anc', '( -u T cseg T ) C_ %s' % XC)
    kibl = st([st([st([ntr], 'recnd', '-u T e. CC'), tc], 'jca', '( -u T e. CC /\\ T e. CC )'), st([hcn, segx], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( -u T cseg T ) C_ %s )' % (H, XC, XC)), w.inst('lintibl')],
              'syl2anc', '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % KB)
    hlc = stt([hl, glc], 'eqeltrd', '( %s ` %s ) e. CC' % (H, LNt))
    kc = stt([hlc, dtc], 'mulcld', '%s e. CC' % KB)
    mc = st([a1c(w, A, 'ax-icn', '_i e. CC'), kc, kibl], 'itgmulc2', '( _i x. %s ) = S. ( 0 (,) 1 ) ( _i x. %s ) _d t' % (IK, KB))
    lv2 = st([st([lv, ie], 'eqtrd', '%s = S. ( 0 (,) 1 ) ( _i x. %s ) _d t' % (LI('G', 'C', 'T'), KB)), mc], 'eqtr4d', '%s = ( _i x. %s )' % (LI('G', 'C', 'T'), IK))
    ik = st([zaff, ih], 'eqtr3d', '%s = %s' % (IK, IG))
    lv3 = st([lv2, st([ik], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (IK, IG))], 'eqtrd', '%s = ( _i x. %s )' % (LI('G', 'C', 'T'), IG))
    w.qed([oibl, lv3], 'jca', STATEMENTS['z6lvert'])
    return w


# ---------------------------------------------------------------- z6absle, z6rlimlem, z6rlimle
def z6absle():
    w = W('z6absle', 'A class whose absolute value is bounded above is a complex number: off ` CC ` the absolute value is '
          '` (/) ` ( ~ ndmfv ), which is not an extended real ( ~ elxr , ~ 0ncn , ~ pwne0 ).')
    RS = 'RR*'
    s1 = w.s([w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')], 'ssbri', '( ( abs ` A ) <_ B -> ( abs ` A ) ( RR* X. RR* ) B )')
    s2 = w.s([s1, w.s([], 'brxp', '( ( abs ` A ) ( RR* X. RR* ) B <-> ( ( abs ` A ) e. RR* /\\ B e. RR* ) )')], 'sylib', '( ( abs ` A ) <_ B -> ( ( abs ` A ) e. RR* /\\ B e. RR* ) )')
    s3 = w.s([s2], 'simpld', '( ( abs ` A ) <_ B -> ( abs ` A ) e. RR* )')
    n1 = w.s([w.s([], '0ncn', '-. (/) e. CC'), w.inst('recn')], 'mto', '-. (/) e. RR')
    pn = w.s([w.s([], 'df-pnf', '+oo = ~P U. CC'), w.s([], 'pwne0', '~P U. CC =/= (/)')], 'eqnetri', '+oo =/= (/)')
    n2 = w.s([w.s([pn], 'necomi', '(/) =/= +oo')], 'neii', '-. (/) = +oo')
    mn = w.s([w.s([], 'df-mnf', '-oo = ~P +oo'), w.s([], 'pwne0', '~P +oo =/= (/)')], 'eqnetri', '-oo =/= (/)')
    n3 = w.s([w.s([mn], 'necomi', '(/) =/= -oo')], 'neii', '-. (/) = -oo')
    n0 = w.s([w.s([n1, n2, n3], '3pm3.2ni', '-. ( (/) e. RR \\/ (/) = +oo \\/ (/) = -oo )'), w.s([], 'elxr', '( (/) e. RR* <-> ( (/) e. RR \\/ (/) = +oo \\/ (/) = -oo ) )')],
             'mtbir', '-. (/) e. RR*')
    e0 = w.s([n0, w.s([], 'eleq1', '( ( abs ` A ) = (/) -> ( ( abs ` A ) e. RR* <-> (/) e. RR* ) )')], 'mtbiri', '( ( abs ` A ) = (/) -> -. ( abs ` A ) e. RR* )')
    e1 = w.s([e0], 'con2i', '( ( abs ` A ) e. RR* -> -. ( abs ` A ) = (/) )')
    da = w.s([w.s([], 'absf', 'abs : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom abs = CC')
    nd = w.s([w.s([w.s([da], 'eleq2i', '( A e. dom abs <-> A e. CC )')], 'notbii', '( -. A e. dom abs <-> -. A e. CC )'), w.s([], 'ndmfv', '( -. A e. dom abs -> ( abs ` A ) = (/) )')],
             'sylbir', '( -. A e. CC -> ( abs ` A ) = (/) )')
    e2 = w.s([nd], 'con1i', '( -. ( abs ` A ) = (/) -> A e. CC )')
    w.qed([s3, w.s([e1, e2], 'syl', '( ( abs ` A ) e. RR* -> A e. CC )')], 'syl', STATEMENTS['z6absle'])
    return w


def z6rlimlem():
    w = W('z6rlimlem', 'A limit of functions bounded in absolute value by ` B ` is bounded by ` B ` ( ~ rlimabs , '
          '~ rlimle ), for a function symbol ` F ` on ` RR+ ` .')
    A = ante_of('z6rlimlem')
    st = mkst(w, A)
    fr = st([], 'simpll', 'F ~~>r W'); ff = st([], 'simplr', 'F : RR+ --> CC')
    br = st([], 'simprl', 'B e. RR'); al = st([], 'simprr', 'A. y e. RR+ ( abs ` ( F ` y ) ) <_ B')
    fe = st([ff], 'feqmptd', 'F = ( z e. RR+ |-> ( F ` z ) )')
    fr2 = st([fe, fr], 'eqbrtrrd', '( z e. RR+ |-> ( F ` z ) ) ~~>r W')
    Az = '( %s /\\ z e. RR+ )' % A
    sz = mkst(w, Az)
    zr = sz([], 'simpr', 'z e. RR+')
    ra = st([sz([], 'fvexd', '( F ` z ) e. _V'), fr2], 'rlimabs', '( z e. RR+ |-> ( abs ` ( F ` z ) ) ) ~~>r ( abs ` W )')
    rc = st([a1c(w, A, 'rpssre', 'RR+ C_ RR'), st([br], 'recnd', 'B e. CC'), w.inst('rlimconst')], 'syl2anc', '( z e. RR+ |-> B ) ~~>r B')
    fz = sz([lift(w, ff, Az), zr], 'ffvelcdmd', '( F ` z ) e. CC')
    azr = sz([fz], 'abscld', '( abs ` ( F ` z ) ) e. RR')
    sb = w.s([w.s([w.s([], 'fveq2', '( y = z -> ( F ` y ) = ( F ` z ) )')], 'fveq2d', '( y = z -> ( abs ` ( F ` y ) ) = ( abs ` ( F ` z ) ) )')], 'breq1d',
             '( y = z -> ( ( abs ` ( F ` y ) ) <_ B <-> ( abs ` ( F ` z ) ) <_ B ) )')
    rs = w.s([sb], 'rspcv', '( z e. RR+ -> ( A. y e. RR+ ( abs ` ( F ` y ) ) <_ B -> ( abs ` ( F ` z ) ) <_ B ) )')
    le = sz([zr, lift(w, al, Az), rs], 'sylc', '( abs ` ( F ` z ) ) <_ B')
    w.qed([a1c(w, A, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo'), ra, rc, azr, lift(w, br, Az), le], 'rlimle', '( %s -> ( abs ` W ) <_ B )' % A)
    return w


def z6rlimle():
    w = W('z6rlimle', 'A limit of a function on ` RR+ ` bounded in absolute value by ` B ` is bounded by ` B ` '
          '( ~ z6rlimlem ; the norm bound of an integral passes to the limit ` t -> +oo ` ).')
    A = ante_of('z6rlimle')
    st = mkst(w, A)
    FM = '( t e. RR+ |-> A )'
    fr = st([], 'simpl', '%s ~~>r W' % FM); br = st([], 'simprl', 'B e. RR'); al = st([], 'simprr', 'A. t e. RR+ ( abs ` A ) <_ B')
    c1 = w.s([w.s([], 'z6absle', '( ( abs ` A ) <_ B -> A e. CC )')], 'ralimi', '( A. t e. RR+ ( abs ` A ) <_ B -> A. t e. RR+ A e. CC )')
    fm = w.s([w.s([], 'eqid', '%s = %s' % (FM, FM))], 'fmpt', '( A. t e. RR+ A e. CC <-> %s : RR+ --> CC )' % FM)
    ff = st([st([al, c1], 'syl', 'A. t e. RR+ A e. CC'), fm], 'sylib', '%s : RR+ --> CC' % FM)
    X = '( t e. RR+ /\\ ( abs ` A ) <_ B )'
    sx = mkst(w, X)
    ac = sx([sx([], 'simpr', '( abs ` A ) <_ B'), w.inst('z6absle')], 'syl', 'A e. CC')
    fv = sx([sx([], 'simpl', 't e. RR+'), ac, w.s([w.s([], 'eqid', '%s = %s' % (FM, FM))], 'fvmpt2', '( ( t e. RR+ /\\ A e. CC ) -> ( %s ` t ) = A )' % FM)], 'syl2anc', '( %s ` t ) = A' % FM)
    le = sx([sx([fv], 'fveq2d', '( abs ` ( %s ` t ) ) = ( abs ` A )' % FM), sx([], 'simpr', '( abs ` A ) <_ B')], 'eqbrtrd', '( abs ` ( %s ` t ) ) <_ B' % FM)
    ex = w.s([le], 'ex', '( t e. RR+ -> ( ( abs ` A ) <_ B -> ( abs ` ( %s ` t ) ) <_ B ) )' % FM)
    c3 = w.s([ex], 'ralimia', '( A. t e. RR+ ( abs ` A ) <_ B -> A. t e. RR+ ( abs ` ( %s ` t ) ) <_ B )' % FM)
    PT = '( abs ` ( %s ` t ) ) <_ B' % FM; PS = '( abs ` ( %s ` s ) ) <_ B' % FM
    nf1 = w.s([], 'nfv', 'F/ s %s' % PT)
    nfm = w.s([w.s([], 'nfmpt1', 'F/_ t %s' % FM), w.s([], 'nfcv', 'F/_ t s')], 'nffv', 'F/_ t ( %s ` s )' % FM)
    nfa = w.s([w.s([], 'nfcv', 'F/_ t abs'), nfm], 'nffv', 'F/_ t ( abs ` ( %s ` s ) )' % FM)
    nf2 = w.s([nfa, w.s([], 'nfcv', 'F/_ t <_'), w.s([], 'nfcv', 'F/_ t B')], 'nfbr', 'F/ t %s' % PS)
    sb = w.s([w.s([w.s([], 'fveq2', '( t = s -> ( %s ` t ) = ( %s ` s ) )' % (FM, FM))], 'fveq2d', '( t = s -> ( abs ` ( %s ` t ) ) = ( abs ` ( %s ` s ) ) )' % (FM, FM))], 'breq1d',
             '( t = s -> ( %s <-> %s ) )' % (PT, PS))
    cb = w.s([nf1, nf2, sb], 'cbvralw', '( A. t e. RR+ %s <-> A. s e. RR+ %s )' % (PT, PS))
    al2 = st([st([al, c3], 'syl', 'A. t e. RR+ %s' % PT), cb], 'sylib', 'A. s e. RR+ %s' % PS)
    h = st([st([fr, ff], 'jca', '( %s ~~>r W /\\ %s : RR+ --> CC )' % (FM, FM)), st([br, al2], 'jca', '( B e. RR /\\ A. s e. RR+ %s )' % PS)], 'jca',
           '( ( %s ~~>r W /\\ %s : RR+ --> CC ) /\\ ( B e. RR /\\ A. s e. RR+ %s ) )' % (FM, FM, PS))
    w.qed([h, w.inst('z6rlimlem')], 'syl', STATEMENTS['z6rlimle'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6segl, z6segv, z6aff, z6lvert, z6absle, z6rlimlem, z6rlimle]:
        if want(f.__name__):
            run(f())
