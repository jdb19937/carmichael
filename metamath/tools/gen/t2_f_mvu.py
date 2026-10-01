"""T2: the mover at a pinned state field --- the instantiation a consumer
uses (blueprint D3): the state class is ` { q e. ( 2nd ` T ) | ( U ` q ) = O } `."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t2_c_mov import (constfty, rfun, OPT, RATY, CTY, PTY, DG, GK, GJ, STMT_T, NVF, GA, PU, UPD2)
from t2_e_mvn import GE, STM0, RY, LAB0, WTYF, FTY

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

NC = '{ q e. %s | ( U ` q ) = O }' % S('T')
UTY = 'U e. ( Z ^m %s )' % S('T')
HCU = ('A. m e. %s A. n e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = n /\\ ( U ` %s ) = ( U ` m ) )'
       % (S('T'), NVF('m', 'n'), NVF('m', 'n'), NVF('m', 'n')))
HEU = ('A. m e. %s ( -. ( C ` %s ) = 1o /\\ ( U ` %s ) = ( U ` m ) )'
       % (S('T'), NVF('m', 'Y'), NVF('m', 'Y')))
PHU = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
       % (PHM, STM0, LAB0, FTY, WTYF, UTY, HCU, HEU))
NSS = '%s C_ %s' % (NC, S('T'))
HCN = ('A. r e. %s A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. %s )'
       % (NC, NVF('r', 'z'), NVF('r', 'z'), NVF('r', 'z'), NC))
HEN = ('A. r e. %s ( -. ( C ` %s ) = 1o /\\ %s e. %s )'
       % (NC, NVF('r', 'Y'), NVF('r', 'Y'), NC))


def CLU(X, Y, lb='A'):
    return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (lb, NC, UPD2(X, Y))


def inNC(w, ante, EXP, expcl, ucl):
    """( ante -> ( EXP e. NC <-> ( U ` EXP ) = O ) ) for a step expcl : EXP e. S"""
    h1 = w.s([], 'fveq2', '( q = %s -> ( U ` q ) = ( U ` %s ) )' % (EXP, EXP))
    h2 = w.s([h1], 'eqeq1d', '( q = %s -> ( ( U ` q ) = O <-> ( U ` %s ) = O ) )' % (EXP, EXP))
    imp = w.s([h2], 'elrab3', '( %s e. %s -> ( %s e. %s <-> ( U ` %s ) = O ) )'
              % (EXP, S('T'), EXP, NC, EXP))
    return w.s([expcl, imp], 'syl', '( %s -> ( %s e. %s <-> ( U ` %s ) = O ) )' % (ante, EXP, NC, EXP))


def tm2fmvu():
    lab = 'tm2fmvu'
    ph = '( %s /\\ W e. Word B )' % PHU
    RVW = '( reverse ` W )'
    RVH = '( %s ++ H )' % RVW
    w = W(lab, 'The mover with one field of the internal state pinned: with '
               '` U ` a state function (Lean\'s ` flag ` , ` cmp ` , ` carry ` '
               'as projections of ` TMSt ` ) which the pop handler preserves, '
               'the mover leaves ` ( U ` v ) ` unchanged.  ~ tm2fmvn at '
               '` N = { q e. ( 2nd ` T ) | ( U ` q ) = O } ` ; the state class '
               'must bind a variable other than ` r ` and ` z ` , which '
               '~ tm2fmvn\'s distinct-variable conditions exclude.')
    phm0 = w.s([], 'simp1l', '( %s -> %s )' % (PHU, PHM))
    meq0 = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (PHU, STM0))
    lab0 = w.s([], 'simp2', '( %s -> %s )' % (PHU, LAB0))
    p30 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
              % (PHU, FTY, WTYF, UTY, HCU, HEU))
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (ph, f))
    phm = A_(phm0, PHM); meq = A_(meq0, '( M ` A ) = %s' % STM0)
    lab2 = A_(lab0, LAB0)
    p3 = A_(p30, '( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (FTY, WTYF, UTY, HCU, HEU))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    ft = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    wt = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, WTYF))
    uh = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (ph, UTY, HCU, HEU))
    uty = w.s([uh], 'simpld', '( %s -> %s )' % (ph, UTY))
    ce = w.s([uh], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, HCU, HEU))
    hcu = w.s([ce], 'simpld', '( %s -> %s )' % (ph, HCU))
    heu = w.s([ce], 'simprd', '( %s -> %s )' % (ph, HEU))
    ra = w.s([ft, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, RATY))
    b2 = w.s([wt, w.inst('simp1')], 'syl', '( %s -> ( B C_ %s /\\ B C_ %s ) )' % (ph, GK, GJ))
    bk = w.s([b2], 'simpld', '( %s -> B C_ %s )' % (ph, GK))
    w3 = w.s([wt, w.inst('simp2')], 'syl',
             '( %s -> ( Y e. %s /\\ X e. Word %s /\\ H e. Word %s ) )' % (ph, GK, GK, GJ))
    yy = w.s([w3, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    rf = rfun(w, ph, ra)
    ssr = w.s([], 'ssrab2', NSS)
    nss = w.s([ssr], 'a1i', '( %s -> %s )' % (ph, NSS))
    # the continue interface at the pinned class
    pr = '( %s /\\ ( r e. %s /\\ z e. B ) )' % (ph, NC)
    def B_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pr, f))
    rnc = w.s([], 'simprl', '( %s -> r e. %s )' % (pr, NC))
    zb = w.s([], 'simprr', '( %s -> z e. B )' % pr)
    nssp = B_(nss, NSS)
    rs = w.s([nssp, rnc], 'sseldd', '( %s -> r e. %s )' % (pr, S('T')))
    hcup = B_(hcu, HCU)
    def TRIP(x, rhs, base):
        return ('( ( C ` %s ) = 1o /\\ ( P ` %s ) = %s /\\ ( U ` %s ) = ( U ` %s ) )'
                % (x, x, rhs, x, base))
    MN = NVF('m', 'n'); RN = NVF('r', 'n'); RZ = NVF('r', 'z')
    innerM = 'A. n e. B %s' % TRIP(MN, 'n', 'm')
    innerR = 'A. n e. B %s' % TRIP(RN, 'n', 'r')
    k1 = w.s([], 'opeq1', '( m = r -> <. m , ( inl ` n ) >. = <. r , ( inl ` n ) >. )')
    k2 = w.s([k1], 'fveq2d', '( m = r -> %s = %s )' % (MN, RN))
    k3 = w.s([k2], 'fveq2d', '( m = r -> ( C ` %s ) = ( C ` %s ) )' % (MN, RN))
    k4 = w.s([k3], 'eqeq1d', '( m = r -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (MN, RN))
    k5 = w.s([k2], 'fveq2d', '( m = r -> ( P ` %s ) = ( P ` %s ) )' % (MN, RN))
    k6 = w.s([k5], 'eqeq1d', '( m = r -> ( ( P ` %s ) = n <-> ( P ` %s ) = n ) )' % (MN, RN))
    k7 = w.s([k2], 'fveq2d', '( m = r -> ( U ` %s ) = ( U ` %s ) )' % (MN, RN))
    k8 = w.s([], 'fveq2', '( m = r -> ( U ` m ) = ( U ` r ) )')
    k9 = w.s([k7, k8], 'eqeq12d', '( m = r -> ( ( U ` %s ) = ( U ` m ) <-> ( U ` %s ) = ( U ` r ) ) )' % (MN, RN))
    k10 = w.s([k4, k6, k9], '3anbi123d', '( m = r -> ( %s <-> %s ) )'
              % (TRIP(MN, 'n', 'm'), TRIP(RN, 'n', 'r')))
    k11 = w.s([k10], 'ralbidv', '( m = r -> ( %s <-> %s ) )' % (innerM, innerR))
    h1 = w.s([k11, hcup, rs], 'rspcdva', '( %s -> %s )' % (pr, innerR))
    l1 = w.s([], 'fveq2', '( n = z -> ( inl ` n ) = ( inl ` z ) )')
    l2 = w.s([l1], 'opeq2d', '( n = z -> <. r , ( inl ` n ) >. = <. r , ( inl ` z ) >. )')
    l3 = w.s([l2], 'fveq2d', '( n = z -> %s = %s )' % (RN, RZ))
    l4 = w.s([l3], 'fveq2d', '( n = z -> ( C ` %s ) = ( C ` %s ) )' % (RN, RZ))
    l5 = w.s([l4], 'eqeq1d', '( n = z -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (RN, RZ))
    lid = w.s([], 'id', '( n = z -> n = z )')
    l6 = w.s([l3], 'fveq2d', '( n = z -> ( P ` %s ) = ( P ` %s ) )' % (RN, RZ))
    l7 = w.s([l6, lid], 'eqeq12d', '( n = z -> ( ( P ` %s ) = n <-> ( P ` %s ) = z ) )' % (RN, RZ))
    l8 = w.s([l3], 'fveq2d', '( n = z -> ( U ` %s ) = ( U ` %s ) )' % (RN, RZ))
    l9 = w.s([l8], 'eqeq1d', '( n = z -> ( ( U ` %s ) = ( U ` r ) <-> ( U ` %s ) = ( U ` r ) ) )' % (RN, RZ))
    l10 = w.s([l5, l7, l9], '3anbi123d', '( n = z -> ( %s <-> %s ) )'
              % (TRIP(RN, 'n', 'r'), TRIP(RZ, 'z', 'r')))
    h2 = w.s([l10, h1, zb], 'rspcdva', '( %s -> %s )' % (pr, TRIP(RZ, 'z', 'r')))
    c1 = w.s([h2, w.inst('simp1')], 'syl', '( %s -> ( C ` %s ) = 1o )' % (pr, RZ))
    c2 = w.s([h2, w.inst('simp2')], 'syl', '( %s -> ( P ` %s ) = z )' % (pr, RZ))
    c3 = w.s([h2, w.inst('simp3')], 'syl', '( %s -> ( U ` %s ) = ( U ` r ) )' % (pr, RZ))
    # ( U ` r ) = O from r e. NC
    bi1 = inNC(w, pr, 'r', rs, uty)
    ur = w.s([bi1, rnc], 'mpbid', '( %s -> ( U ` r ) = O )' % pr)
    uz = w.s([c3, ur], 'eqtrd', '( %s -> ( U ` %s ) = O )' % (pr, NVF('r', 'z')))
    # the new state is a state
    bkp = B_(bk, 'B C_ %s' % GK)
    zk = w.s([bkp, zb], 'sseldd', '( %s -> z e. %s )' % (pr, GK))
    djl = w.s([zk, w.inst('djulcl')], 'syl', '( %s -> ( inl ` z ) e. %s )' % (pr, OPT))
    prp = w.s([rs, djl], 'opelxpd', '( %s -> <. r , ( inl ` z ) >. e. ( %s X. %s ) )' % (pr, S('T'), OPT))
    rfp = B_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
    nvs = w.s([rfp, prp], 'ffvelcdmd', '( %s -> %s e. %s )' % (pr, NVF('r', 'z'), S('T')))
    bi2 = inNC(w, pr, NVF('r', 'z'), nvs, uty)
    nvn = w.s([bi2, uz], 'mpbird', '( %s -> %s e. %s )' % (pr, NVF('r', 'z'), NC))
    tri = w.s([c1, c2, nvn], '3jca', '( %s -> ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. %s ) )'
              % (pr, NVF('r', 'z'), NVF('r', 'z'), NVF('r', 'z'), NC))
    hcn = w.s([tri], 'ralrimivva', '( %s -> %s )' % (ph, HCN))
    # the exit interface at the pinned class
    pe = '( %s /\\ r e. %s )' % (ph, NC)
    def C_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pe, f))
    rnce = w.s([], 'simpr', '( %s -> r e. %s )' % (pe, NC))
    nsse = C_(nss, NSS)
    rse = w.s([nsse, rnce], 'sseldd', '( %s -> r e. %s )' % (pe, S('T')))
    heup = C_(heu, HEU)
    MY = NVF('m', 'Y'); RYv = NVF('r', 'Y')
    def PAIR(x, base):
        return '( -. ( C ` %s ) = 1o /\\ ( U ` %s ) = ( U ` %s ) )' % (x, x, base)
    g1 = w.s([], 'opeq1', '( m = r -> <. m , ( inl ` Y ) >. = <. r , ( inl ` Y ) >. )')
    g2 = w.s([g1], 'fveq2d', '( m = r -> %s = %s )' % (MY, RYv))
    g3 = w.s([g2], 'fveq2d', '( m = r -> ( C ` %s ) = ( C ` %s ) )' % (MY, RYv))
    g4 = w.s([g3], 'eqeq1d', '( m = r -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (MY, RYv))
    g5 = w.s([g4], 'notbid', '( m = r -> ( -. ( C ` %s ) = 1o <-> -. ( C ` %s ) = 1o ) )' % (MY, RYv))
    g6 = w.s([g2], 'fveq2d', '( m = r -> ( U ` %s ) = ( U ` %s ) )' % (MY, RYv))
    g7 = w.s([], 'fveq2', '( m = r -> ( U ` m ) = ( U ` r ) )')
    g8 = w.s([g6, g7], 'eqeq12d', '( m = r -> ( ( U ` %s ) = ( U ` m ) <-> ( U ` %s ) = ( U ` r ) ) )' % (MY, RYv))
    g9 = w.s([g5, g8], 'anbi12d', '( m = r -> ( %s <-> %s ) )' % (PAIR(MY, 'm'), PAIR(RYv, 'r')))
    e1 = w.s([g9, heup, rse], 'rspcdva', '( %s -> %s )' % (pe, PAIR(RYv, 'r')))
    e2 = w.s([e1], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (pe, RYv))
    e3 = w.s([e1], 'simprd', '( %s -> ( U ` %s ) = ( U ` r ) )' % (pe, RYv))
    bi3 = inNC(w, pe, 'r', rse, uty)
    ure = w.s([bi3, rnce], 'mpbid', '( %s -> ( U ` r ) = O )' % pe)
    uye = w.s([e3, ure], 'eqtrd', '( %s -> ( U ` %s ) = O )' % (pe, NVF('r', 'Y')))
    yye = C_(yy, 'Y e. %s' % GK)
    djle = w.s([yye, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. %s )' % (pe, OPT))
    pre = w.s([rse, djle], 'opelxpd', '( %s -> <. r , ( inl ` Y ) >. e. ( %s X. %s ) )' % (pe, S('T'), OPT))
    rfe = C_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
    nvse = w.s([rfe, pre], 'ffvelcdmd', '( %s -> %s e. %s )' % (pe, NVF('r', 'Y'), S('T')))
    bi4 = inNC(w, pe, NVF('r', 'Y'), nvse, uty)
    nvne = w.s([bi4, uye], 'mpbird', '( %s -> %s e. %s )' % (pe, NVF('r', 'Y'), NC))
    pr2 = w.s([e2, nvne], 'jca', '( %s -> ( -. ( C ` %s ) = 1o /\\ %s e. %s ) )'
              % (pe, NVF('r', 'Y'), NVF('r', 'Y'), NC))
    hen = w.s([pr2], 'ralrimiva', '( %s -> %s )' % (ph, HEN))
    # assemble and apply tm2fmvn
    nhc = w.s([hcn, hen], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, HCN, HEN))
    q3 = w.s([nss, nhc], 'jca', '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (ph, NSS, HCN, HEN))
    p3n = w.s([ft, wt, q3], '3jca', '( %s -> ( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
              % (ph, FTY, WTYF, NSS, HCN, HEN))
    pm1 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STM0))
    PHFi = ('( ( %s /\\ ( M ` A ) = %s ) /\\ %s /\\ ( %s /\\ %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )'
            % (PHM, STM0, LAB0, FTY, WTYF, NSS, HCN, HEN))
    pfi = w.s([pm1, lab2, p3n], '3jca', '( %s -> %s )' % (ph, PHFi))
    ant = w.s([pfi, ww], 'jca', '( %s -> ( %s /\\ W e. Word B ) )' % (ph, PHFi))
    w.qed([ant, w.inst('tm2fmvn')], 'syl', '( %s -> %s )'
          % (ph, HR(CLU('( W ++ %s )' % RY, 'H'), 'T', 'M', CLU('X', RVH, 'E'), '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fmvu'): tm2fmvu()
