"""Sortie T6: the list fragments of the machine layer (TM/Lists.lean).

Expression builders for the list encodings and the fixed-alphabet machine
(` ( 1st ` ( 1st ` T ) ) = TMGam ` ), on top of tools/t1lib.py.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t1lib import *
from t3_lib import hstepc2, hstepE

# ---------------------------------------------------------------- expressions

BITS = '( { 1 } X. 2o )'
WB = 'Word ( { 1 } X. 2o )'
WWB = 'Word Word ( { 1 } X. 2o )'
WG = "Word Gamma'"
WWG = "Word Word Gamma'"
FM = "( freeMnd ` Gamma' )"
C4 = '<" 4 ">'
C2 = '<" 2 ">'
B4 = '( ( { 1 } X. 2o ) u. { 4 } )'
PFW = '( w e. %s |-> ( w ++ <" 4 "> ) )' % WB
PFN = '( p e. NN0 |-> ( ( encNatGam ` p ) ++ <" 4 "> ) )'
STMT_T = '( TM2Stmt ` T )'
DG = 'dom ( 1st ` ( 1st ` T ) )'
GAM = "Gamma'"
OPT = "( Gamma' |_| 1o )"
FZ8 = '( 0 ..^ 8 )'
PHM6 = '( %s /\\ ( 1st ` ( 1st ` T ) ) = TMGam )' % PHM
ST = '( ( 2nd ` T ) X. ( TM2Stk ` T ) )'


def ENT(L): return '( entries ` %s )' % L
def ENCB(L): return '( encListB ` %s )' % L
def ENC(L): return '( encList ` %s )' % L
def EG(N): return '( encNatGam ` %s )' % N
def FLATW(L): return '( %s gsum ( %s o. %s ) )' % (FM, PFW, L)
def FLATN(L): return '( %s gsum ( %s o. %s ) )' % (FM, PFN, L)
def DROP(L, J): return '( %s substr <. %s , ( # ` %s ) >. )' % (L, J, L)
def PFX(L, J): return '( %s prefix %s )' % (L, J)
def CL(A, N, D): return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (A, N, D)
def ENTRY(W, X): return '( %s ++ ( <" 4 "> ++ %s ) )' % (W, X)
def LST(L, R): return '( %s ++ %s )' % (ENCB(L), R)
def NV(F, r, z): return '( %s ` <. %s , ( inl ` %s ) >. )' % (F, r, z)
def UPDT(D, K, X): return UPD('T', D, K, X)
def GT(K): return "( ( 1st ` ( 1st ` T ) ) ` %s )" % K
def HLD(K, Y, Q): return PEEK(K, 'F', GOTO(CONSTF('T', Q))) if False else None

def GOTOL(E): return GOTO(CONSTF('T', E))
def PSH(K, Z, E): return PUSH(K, CONSTF('T', Z), GOTOL(E))
def PEEKL(K, F, E): return PEEK(K, F, GOTOL(E))
def POPL(K, F, E): return POP(K, F, GOTOL(E))
def TESTL(C, B, E): return BRANCH(C, GOTOL(B), GOTOL(E))
def MOVE(A, K, J, E):
    """T2's mover statement at label A from stack K to stack J, exit E"""
    return POP(K, 'F', BRANCH('C', PUSH(J, 'P', GOTOL(A)), GOTOL(E)))


# ------------------------------------------------------------ closed facts

def closedw(w, ante, ref, fact):
    c = w.s([], ref, fact)
    return w.s([c], 'a1i', '( %s -> %s )' % (ante, fact))


def bitsss(w, ante):
    """( ante -> ( { 1 } X. 2o ) C_ Gamma' )"""
    return closedw(w, ante, 'tm2lbits', "%s C_ Gamma'" % BITS)


def wbss(w, ante):
    """( ante -> Word ( { 1 } X. 2o ) C_ Word Gamma' )"""
    return closedw(w, ante, 'tm2lwbss', "%s C_ %s" % (WB, WG))


def wbtog(w, ante, X, xin):
    """( ante -> X e. Word Gamma' ) from xin : ( ante -> X e. WB )"""
    return w.s([wbss(w, ante), xin], 'sseldd', '( %s -> %s e. %s )' % (ante, X, WG))


def gamlet(w, ante, n):
    """( ante -> n e. Gamma' ) for n in 0 2 3 4"""
    return closedw(w, ante, 'gamma%s' % n, "%s e. Gamma'" % n)


def s1g(w, ante, n):
    """( ante -> <" n "> e. Word Gamma' )"""
    g = gamlet(w, ante, n)
    return w.s([g], 's1cld', '( %s -> <" %s "> e. %s )' % (ante, n, WG))


def ccatg(w, ante, X, Y, xcl, ycl):
    """( ante -> ( X ++ Y ) e. Word Gamma' )"""
    return w.s([xcl, ycl, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. %s )' % (ante, X, Y, WG))


# ---------------------------------------------- the fixed-alphabet machine

def gamk(w, ante, K, geq, kk):
    """from geq : ( ante -> ( 1st ` ( 1st ` T ) ) = TMGam ) and
    kk : ( ante -> K e. ( 0 ..^ 8 ) ), return (step : K e. dom G,
    step : ( G ` K ) = Gamma')"""
    fn = closedw(w, ante, 'tmgamfn', 'TMGam Fn ( 0 ..^ 8 )')
    dm = w.s([fn, w.inst('fndm')], 'syl', '( %s -> dom TMGam = ( 0 ..^ 8 ) )' % ante)
    dg = w.s([geq], 'dmeqd', '( %s -> %s = dom TMGam )' % (ante, DG))
    dg2 = w.s([dg, dm], 'eqtrd', '( %s -> %s = ( 0 ..^ 8 ) )' % (ante, DG))
    kd = w.s([kk, dg2], 'eleqtrrd', '( %s -> %s e. %s )' % (ante, K, DG))
    gv = w.s([geq], 'fveq1d', '( %s -> %s = ( TMGam ` %s ) )' % (ante, GT(K), K))
    tg = w.s([kk, w.inst('tmgamfv')], 'syl', "( %s -> ( TMGam ` %s ) = Gamma' )" % (ante, K))
    ge = w.s([gv, tg], 'eqtrd', "( %s -> %s = Gamma' )" % (ante, GT(K)))
    return kd, ge


def wgk(w, ante, X, K, ge, xcl):
    """( ante -> X e. Word ( G ` K ) ) from xcl : ( ante -> X e. Word Gamma' )
    and ge : ( ante -> ( G ` K ) = Gamma' )"""
    we = w.s([ge], 'wrdeqd' if False else 'eqcomd', "( %s -> Gamma' = %s )" % (ante, GT(K)))
    we2 = w.s([we, w.inst('wrdeq')], 'syl', '( %s -> %s = Word %s )' % (ante, WG, GT(K)))
    return w.s([xcl, we2], 'eleqtrd', '( %s -> %s e. Word %s )' % (ante, X, GT(K)))


def lgk(w, ante, Z, K, ge, zcl):
    """( ante -> Z e. ( G ` K ) ) from zcl : ( ante -> Z e. Gamma' )"""
    return w.s([zcl, ge], 'eleqtrrd', '( %s -> %s e. %s )' % (ante, Z, GT(K)))


def stkfvg(w, ante, D, K, tv, dd, kd, ge):
    """( ante -> ( D ` K ) e. Word Gamma' )"""
    f = w.s([tv, dd, kd, w.inst('tm2stkfv')], 'syl3anc', '( %s -> ( %s ` %s ) e. Word %s )' % (ante, D, K, GT(K)))
    we = w.s([ge, w.inst('wrdeq')], 'syl', '( %s -> Word %s = %s )' % (ante, GT(K), WG))
    return w.s([f, we], 'eleqtrd', '( %s -> ( %s ` %s ) e. %s )' % (ante, D, K, WG))


def updcl(w, ante, D, K, X, tv, dd, kd, ge, xcl):
    """( ante -> UPD( D , K , X ) e. Stk ) from xcl : X e. Word Gamma'"""
    xk = wgk(w, ante, X, K, ge, xcl)
    p = w.s([kd, xk], 'jca', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ante, K, DG, X, GT(K)))
    return w.s([tv, dd, p, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ante, UPDT(D, K, X), STK('T')))


def updn(w, ante, D, K, Y, J, tv, dd, kd, yv, jd, ne):
    """( ante -> ( UPD( D , K , Y ) ` J ) = ( D ` J ) ) for J =/= K;
    yv : ( ante -> Y e. _V ), ne : ( ante -> J =/= K )"""
    a = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ante, D, STK('T')))
    b = w.s([kd, yv], 'jca', '( %s -> ( %s e. %s /\\ %s e. _V ) )' % (ante, K, DG, Y))
    c = w.s([jd, ne], 'jca', '( %s -> ( %s e. %s /\\ %s =/= %s ) )' % (ante, J, DG, J, K))
    return w.s([a, b, c, w.inst('tm2stkupn')], 'syl3anc', '( %s -> ( %s ` %s ) = ( %s ` %s ) )'
               % (ante, UPDT(D, K, Y), J, D, J))


def updk(w, ante, D, K, Y, tv, dd, kd, yv):
    """( ante -> ( UPD( D , K , Y ) ` K ) = Y )"""
    return updkval(w, ante, 'T', D, K, Y, tv, dd, kd, yv)


def constf(w, ante, X, COD, xcl):
    """( ante -> ( S X. { X } ) e. ( COD ^m S ) ) --- T2's constfty"""
    f = w.s([xcl, w.inst('fconst6g')], 'syl', '( %s -> %s : %s --> %s )' % (ante, CONSTF('T', X), S('T'), COD))
    c1 = w.s([], 'fvex', '%s e. _V' % COD) if COD.startswith('(') and '`' in COD and not COD.startswith('( 2o') else None
    if c1 is None:
        c1a = setex(w, ante, COD, 'gammaex') if COD == GAM else None
        if c1a is None:
            raise ValueError('constf: codomain ' + COD)
    else:
        c1a = w.s([c1], 'a1i', '( %s -> %s e. _V )' % (ante, COD))
    c2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    c2a = w.s([c2], 'a1i', '( %s -> %s e. _V )' % (ante, S('T')))
    bi = w.s([c1a, c2a, w.inst('elmapg')], 'syl2anc',
             '( %s -> ( %s e. ( %s ^m %s ) <-> %s : %s --> %s ) )'
             % (ante, CONSTF('T', X), COD, S('T'), CONSTF('T', X), S('T'), COD))
    return w.s([bi, f], 'mpbird', '( %s -> %s e. ( %s ^m %s ) )' % (ante, CONSTF('T', X), COD, S('T')))


def gotost(w, ante, E, tv, el):
    """( ante -> <. 5 , ( S X. { E } ) >. e. Stmt ) from el : E e. L"""
    fe = constf(w, ante, E, L('T'), el)
    return fe, w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ante, GOTOL(E), STMT_T))


def fmapg(w, ante, F, K, ge, fty):
    """from fty : ( ante -> F e. ( S ^m ( S X. ( Gamma' |_| 1o ) ) ) ) and
    ge : ( G ` K ) = Gamma', the typing at stack K"""
    oe = w.s([ge], 'eqcomd', "( %s -> Gamma' = %s )" % (ante, GT(K)))
    o1 = w.s([oe], 'djueq1d' if False else 'eqcomd', "( %s -> %s = Gamma' )" % (ante, GT(K)))
    # ( ( G ` K ) |_| 1o ) = ( Gamma' |_| 1o )
    d1 = w.s([o1, w.inst('djueq1')], 'syl', "( %s -> ( %s |_| 1o ) = %s )" % (ante, GT(K), OPT))
    x1 = w.s([d1], 'xpeq2d', "( %s -> ( %s X. ( %s |_| 1o ) ) = ( %s X. %s ) )" % (ante, S('T'), GT(K), S('T'), OPT))
    m1 = w.s([x1], 'oveq2d', "( %s -> ( %s ^m ( %s X. ( %s |_| 1o ) ) ) = ( %s ^m ( %s X. %s ) ) )"
             % (ante, S('T'), S('T'), GT(K), S('T'), S('T'), OPT))
    return w.s([fty, m1], 'eleqtrrd', '( %s -> %s e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) )' % (ante, F, S('T'), S('T'), GT(K)))


def pmapg(w, ante, P, K, ge, pty):
    """from pty : ( ante -> P e. ( Gamma' ^m S ) ) the typing P e. ( ( G ` K ) ^m S )"""
    m1 = w.s([ge], 'oveq1d', "( %s -> ( %s ^m %s ) = ( Gamma' ^m %s ) )" % (ante, GT(K), S('T'), S('T')))
    return w.s([pty, m1], 'eleqtrrd', '( %s -> %s e. ( %s ^m %s ) )' % (ante, P, GT(K), S('T')))


def A_(w, ante, st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (ante, f))


def hseq(w, ante, phm, C, D, R, N, P, t1, t2):
    """tm2hseq: from t1 : C ~~> D in N and t2 : D ~~> R in P"""
    return w.s([phm, t1, t2], 'syl3anc', '( %s -> %s )' % (ante, HR(C, 'T', 'M', R, '( %s + %s )' % (N, P))))


def hle(w, ante, phm, C, D, N, P, tri, pcl, le):
    """tm2hle: raise the bound of tri : C ~~> D in N to P, given pcl : P e. NN0, le : N <_ P"""
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, PHM, HR(C, 'T', 'M', D, N)))
    b = w.s([pcl, le], 'jca', '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ante, P, N, P))
    return w.s([a, b, w.inst('tm2hle')], 'syl2anc', '( %s -> %s )' % (ante, HR(C, 'T', 'M', D, P)))


def hssc(w, ante, phm, C, D, N, S_, tri, ss):
    """tm2hssc: shrink the precondition of tri to S_ given ss : S_ C_ C"""
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, PHM, HR(C, 'T', 'M', D, N)))
    return w.s([a, ss, w.inst('tm2hssc')], 'syl2anc', '( %s -> %s )' % (ante, HR(S_, 'T', 'M', D, N)))


def hssd(w, ante, phm, C, D, N, R, tri, ss, rcfg):
    """tm2hssd: grow the postcondition of tri to R given ss : D C_ R, rcfg : R C_ Cfg"""
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, PHM, HR(C, 'T', 'M', D, N)))
    b = w.s([ss, rcfg], 'jca', '( %s -> ( %s C_ %s /\\ %s C_ %s ) )' % (ante, D, R, R, CFG('T')))
    return w.s([a, b, w.inst('tm2hssd')], 'syl2anc', '( %s -> %s )' % (ante, HR(C, 'T', 'M', R, N)))


def hrtransport(w, ante, tri, C, D, N, C2, D2, eqc=None, eqd=None):
    """rewrite the classes of a triple: eqc : ( ante -> C = C2 ), eqd : ( ante -> D = D2 )"""
    cur = tri; curC, curD = C, D
    if eqc is not None:
        b = w.s([eqc], 'breq1d', '( %s -> ( %s <-> %s ) )' % (ante, HR(curC, 'T', 'M', curD, N), HR(C2, 'T', 'M', curD, N)))
        cur = w.s([b, cur], 'mpbid', '( %s -> %s )' % (ante, HR(C2, 'T', 'M', curD, N))); curC = C2
    if eqd is not None:
        o = w.s([eqd], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ante, curD, N, D2, N))
        b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ante, HR(curC, 'T', 'M', curD, N), HR(curC, 'T', 'M', D2, N)))
        cur = w.s([b, cur], 'mpbid', '( %s -> %s )' % (ante, HR(curC, 'T', 'M', D2, N))); curD = D2
    return cur


def cfgcl(w, ante, A, N, D, tv, al, nss, dd):
    """( ante -> C( A , N , D ) C_ Cfg )"""
    sd = w.s([dd], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D, STK('T')))
    x = w.s([nss, sd, w.inst('xpss12')], 'syl2anc', '( %s -> ( %s X. { %s } ) C_ %s )' % (ante, N, D, ST))
    return w.s([tv, al, x, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ante, CL(A, N, D), CFG('T')))


def cleq(w, ante, A, N, D1, D2, eq):
    """( ante -> C( A , N , D1 ) = C( A , N , D2 ) ) from eq : ( ante -> D1 = D2 )"""
    s = w.s([eq], 'sneqd', '( %s -> { %s } = { %s } )' % (ante, D1, D2))
    x = w.s([s], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ante, N, D1, N, D2))
    return w.s([x], 'xpeq2d', '( %s -> %s = %s )' % (ante, CL(A, N, D1), CL(A, N, D2)))
