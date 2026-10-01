"""Sortie v2b: the Selberg weights.

vrecrp   1 / ( 1 - ( V ` Q ) ) is a positive real for a prime divisor Q of P
gtmul    the Selberg term is multiplicative on coprime divisors of P
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *

BODY = '( 1 / ( 1 - ( V ` q ) ) )'


def PR(X):
    return 'prod_ q e. %s %s' % (PF(X), BODY)


def vrecrp():
    w = W('vrecrp', 'The reciprocal of one minus the density at a prime divisor of the sifting '
                    'product is a positive real.')
    A = '( %s /\\ ( Q e. Prime /\\ Q || P ) )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    qprm = st([], 'simprl', 'Q e. Prime')
    qdp = st([], 'simprr', 'Q || P')
    qnn = st([qprm, w.inst('prmnn')], 'syl', 'Q e. NN')
    vqr = st([d['vf'], qnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` Q ) e. RR')
    both = st([d['vprm'], st([qprm, qdp], 'jca', '( Q e. Prime /\\ Q || P )'), w.inst('vprmc')],
              'syl2anc', '( 0 < ( V ` Q ) /\\ ( V ` Q ) < 1 )')
    lt1 = st([both], 'simprd', '( V ` Q ) < 1')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    pos = st([st([vqr, one], 'posdifd', '( ( V ` Q ) < 1 <-> 0 < ( 1 - ( V ` Q ) ) )'), lt1],
             'mpbid', '0 < ( 1 - ( V ` Q ) )')
    subrp = st([st([one, vqr], 'resubcld', '( 1 - ( V ` Q ) ) e. RR'), pos], 'elrpd',
               '( 1 - ( V ` Q ) ) e. RR+')
    w.qed([subrp], 'rpreccld', '( %s -> ( 1 / ( 1 - ( V ` Q ) ) ) e. RR+ )' % A)
    return w


def gtmul():
    w = W('gtmul', 'The Selberg term is multiplicative on coprime divisors of the sifting '
                   'product.')
    TRI = ('( ( E e. NN /\\ E || P ) /\\ ( F e. NN /\\ F || P ) /\\ ( E gcd F ) = 1 )')
    A = '( %s /\\ %s )' % (SH, TRI)
    EF = '( E x. F )'
    PFE = PF('E')
    PFF = PF('F')
    PFEF = PF(EF)
    d = shsteps(w, A, (SH,))
    st = d['st']
    tri = st([], 'simpr', TRI)
    e2 = st([tri], 'simp1d', '( E e. NN /\\ E || P )')
    f2 = st([tri], 'simp2d', '( F e. NN /\\ F || P )')
    cop = st([tri], 'simp3d', '( E gcd F ) = 1')
    enn = st([e2], 'simpld', 'E e. NN')
    edp = st([e2], 'simprd', 'E || P')
    fnn = st([f2], 'simpld', 'F e. NN')
    fdp = st([f2], 'simprd', 'F || P')
    ez = st([enn], 'nnzd', 'E e. ZZ')
    fz = st([fnn], 'nnzd', 'F e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    efnn = st([enn, fnn], 'nnmulcld', '%s e. NN' % EF)
    efz = st([efnn], 'nnzd', '%s e. ZZ' % EF)
    efdp = st([st([st([st([ez, fz, pz], '3jca', '( E e. ZZ /\\ F e. ZZ /\\ P e. ZZ )'), cop],
                   'jca', '( ( E e. ZZ /\\ F e. ZZ /\\ P e. ZZ ) /\\ ( E gcd F ) = 1 )'),
                   w.inst('coprmdvds2')], 'syl',
                  '( ( E || P /\\ F || P ) -> %s || P )' % EF),
               st([edp, fdp], 'jca', '( E || P /\\ F || P )')], 'mpd', '%s || P' % EF)
    vef = st([d['vmul'], st([enn, fnn, cop], '3jca',
                            '( E e. NN /\\ F e. NN /\\ ( E gcd F ) = 1 )'), w.inst('vmulc')],
             'syl2anc', '( V ` %s ) = ( ( V ` E ) x. ( V ` F ) )' % EF)
    # the prime divisor sets
    AR = '( %s /\\ r e. Prime )' % A
    sr = mkst(w, AR)
    rprm = w.s([], 'simpr', '( %s -> r e. Prime )' % AR)
    eucl = sr([sr([rprm, sr([ez], 'adantr', 'E e. ZZ'), sr([fz], 'adantr', 'F e. ZZ')], '3jca',
                  '( r e. Prime /\\ E e. ZZ /\\ F e. ZZ )'), w.inst('euclemma')], 'syl',
              '( r || %s <-> ( r || E \\/ r || F ) )' % EF)
    rab1 = st([eucl], 'rabbidva', '%s = { r e. Prime | ( r || E \\/ r || F ) }' % PFEF)
    unr = st([w.s([], 'unrab',
                  '( %s u. %s ) = { r e. Prime | ( r || E \\/ r || F ) }' % (PFE, PFF))], 'a1i',
             '( %s u. %s ) = { r e. Prime | ( r || E \\/ r || F ) }' % (PFE, PFF))
    pfun = st([rab1, st([unr], 'eqcomd',
                        '{ r e. Prime | ( r || E \\/ r || F ) } = ( %s u. %s )' % (PFE, PFF))],
              'eqtrd', '%s = ( %s u. %s )' % (PFEF, PFE, PFF))
    # disjointness
    ARB = '( %s /\\ ( r || E /\\ r || F ) )' % AR
    srb = mkst(w, ARB)
    rz = srb([srb([srb([rprm], 'adantr', 'r e. Prime'), w.inst('prmz')], 'syl', 'r e. ZZ')],
             'id', 'r e. ZZ') if False else srb([srb([rprm], 'adantr', 'r e. Prime'),
                                                w.inst('prmz')], 'syl', 'r e. ZZ')
    rdg = srb([srb([srb([rz, srb([sr([ez], 'adantr', 'E e. ZZ')], 'adantr', 'E e. ZZ'),
                         srb([sr([fz], 'adantr', 'F e. ZZ')], 'adantr', 'F e. ZZ')], '3jca',
                        '( r e. ZZ /\\ E e. ZZ /\\ F e. ZZ )'), w.inst('dvdsgcdb')], 'syl',
                   '( ( r || E /\\ r || F ) <-> r || ( E gcd F ) )'),
               srb([], 'simpr', '( r || E /\\ r || F )')], 'mpbid', 'r || ( E gcd F )')
    rd1 = srb([srb([srb([sr([cop], 'adantr', '( E gcd F ) = 1')], 'adantr',
                        '( E gcd F ) = 1')], 'eqcomd', '1 = ( E gcd F )'), rdg], 'breqtrrd',
              'r || 1')
    nd1 = sr([rprm, w.inst('nprmdvds1')], 'syl', '-. r || 1')
    nconj = sr([nd1, rd1], 'mtand', '-. ( r || E /\\ r || F )')
    ral = st([nconj], 'ralrimiva', 'A. r e. Prime -. ( r || E /\\ r || F )')
    rab0 = st([st([w.s([], 'rabeq0',
                       '( { r e. Prime | ( r || E /\\ r || F ) } = (/) <-> '
                       'A. r e. Prime -. ( r || E /\\ r || F ) )')], 'a1i',
                  '( { r e. Prime | ( r || E /\\ r || F ) } = (/) <-> '
                  'A. r e. Prime -. ( r || E /\\ r || F ) )'), ral], 'mpbird',
              '{ r e. Prime | ( r || E /\\ r || F ) } = (/)')
    pfdisj = st([st([w.s([], 'inrab',
                         '( %s i^i %s ) = { r e. Prime | ( r || E /\\ r || F ) }'
                         % (PFE, PFF))], 'a1i',
                    '( %s i^i %s ) = { r e. Prime | ( r || E /\\ r || F ) }' % (PFE, PFF)),
                 rab0], 'eqtrd', '( %s i^i %s ) = (/)' % (PFE, PFF))

    # finiteness
    def fin(X, step):
        return st([st([w.s([], 'cbvrabv', '%s = %s' % (PF(X, 'p'), PF(X)))], 'a1i',
                      '%s = %s' % (PF(X, 'p'), PF(X))),
                   st([step, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF(X, 'p'))],
                  'eqeltrrd', '%s e. Fin' % PF(X))

    finE = fin('E', enn)
    finF = fin('F', fnn)
    finEF = fin(EF, efnn)

    # the body is a complex number on each prime divisor set
    def bodycl(X, dstep, xz):
        AQ = '( %s /\\ q e. %s )' % (A, PF(X))
        sq = mkst(w, AQ)
        elq = w.s([w.s([], 'breq1', '( r = q -> ( r || %s <-> q || %s ) )' % (X, X))], 'elrab',
                  '( q e. %s <-> ( q e. Prime /\\ q || %s ) )' % (PF(X), X))
        cj = sq([sq([elq], 'a1i', '( q e. %s <-> ( q e. Prime /\\ q || %s ) )' % (PF(X), X)),
                 sq([], 'simpr', 'q e. %s' % PF(X))], 'mpbid',
                '( q e. Prime /\\ q || %s )' % X)
        qprm = sq([cj], 'simpld', 'q e. Prime')
        qdx = sq([cj], 'simprd', 'q || %s' % X)
        qdp = sq([sq([sq([sq([qprm, w.inst('prmz')], 'syl', 'q e. ZZ'),
                          sq([xz], 'adantr', '%s e. ZZ' % X), sq([pz], 'adantr', 'P e. ZZ')],
                         '3jca', '( q e. ZZ /\\ %s e. ZZ /\\ P e. ZZ )' % X),
                      w.inst('dvdstr')], 'syl',
                     '( ( q || %s /\\ %s || P ) -> q || P )' % (X, X)),
                  sq([qdx, sq([dstep], 'adantr', '%s || P' % X)], 'jca',
                     '( q || %s /\\ %s || P )' % (X, X))], 'mpd', 'q || P')
        rp = sq([sq([d['sh']], 'adantr', SH), sq([qprm, qdp], 'jca',
                                                 '( q e. Prime /\\ q || P )'),
                 w.inst('vrecrp')], 'syl2anc', '%s e. RR+' % BODY)
        return sq([sq([rp], 'rpred', '%s e. RR' % BODY)], 'recnd', '%s e. CC' % BODY)

    bcE = bodycl('E', edp, ez)
    bcF = bodycl('F', fdp, fz)
    bcEF = bodycl(EF, efdp, efz)
    split = st([pfdisj, pfun, finEF, bcEF], 'fprodsplit',
               '%s = ( %s x. %s )' % (PR(EF), PR('E'), PR('F')))
    prE = st([finE, bcE], 'fprodcl', '%s e. CC' % PR('E'))
    prF = st([finF, bcF], 'fprodcl', '%s e. CC' % PR('F'))
    vec = st([st([d['vf'], enn, w.inst('ffvelcdm')], 'syl2anc', '( V ` E ) e. RR')], 'recnd',
             '( V ` E ) e. CC')
    vfc = st([st([d['vf'], fnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` F ) e. RR')], 'recnd',
             '( V ` F ) e. CC')
    m4 = st([vec, vfc, prE, prF], 'mul4d',
            '( ( ( V ` E ) x. ( V ` F ) ) x. ( %s x. %s ) ) = '
            '( ( ( V ` E ) x. %s ) x. ( ( V ` F ) x. %s ) )' % (PR('E'), PR('F'), PR('E'),
                                                                PR('F')))
    w.qed([st([vef, split], 'oveq12d',
              '( ( V ` %s ) x. %s ) = ( ( ( V ` E ) x. ( V ` F ) ) x. ( %s x. %s ) )'
              % (EF, PR(EF), PR('E'), PR('F'))), m4], 'eqtrd',
          '( %s -> %s = ( %s x. %s ) )' % (A, GT(EF), GT('E'), GT('F')))
    return w


def _facre(w, A, d, st, dnn, ddp):
    """( A -> FAC ( D ) e. RR ) given ( A -> D e. NN ) and ( A -> D || P )"""
    vrp = st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'), w.inst('vdrp')],
             'syl2anc', '( V ` D ) e. RR+')
    recv = st([st([vrp], 'rpreccld', '( 1 / ( V ` D ) ) e. RR+')], 'rpred',
              '( 1 / ( V ` D ) ) e. RR')
    gre = st([st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'), w.inst('gtrp')],
                 'syl2anc', '%s e. RR+' % GT('D'))], 'rpred', '%s e. RR' % GT('D'))
    mur = st([st([dnn, w.inst('mucl')], 'syl', '( mmu ` D ) e. ZZ')], 'zred',
             '( mmu ` D ) e. RR')
    ssr = st([st([st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())], 'rpreccld',
                 '( 1 / %s ) e. RR+' % SS())], 'rpred', '( 1 / %s ) e. RR' % SS())
    return st([st([recv, gre], 'remulcld', '( ( 1 / ( V ` D ) ) x. %s ) e. RR' % GT('D')),
               st([mur, ssr], 'remulcld',
                  '( ( mmu ` D ) x. ( 1 / %s ) ) e. RR' % SS())], 'remulcld',
              '%s e. RR' % FAC('D'))


def _innerre(w, A, d, st, dnn):
    """( A -> INNER ( D ) e. RR ) given ( A -> D e. NN )"""
    DVP = DV('P')
    AM = '( %s /\ m e. %s )' % (A, DVP)
    sm = mkst(w, AM)
    elm = w.s([w.s([], 'breq1', '( x = m -> ( x || P <-> m || P ) )')], 'elrab',
              '( m e. %s <-> ( m e. NN /\ m || P ) )' % DVP)
    mc = sm([sm([elm], 'a1i', '( m e. %s <-> ( m e. NN /\ m || P ) )' % DVP),
             sm([], 'simpr', 'm e. %s' % DVP)], 'mpbid', '( m e. NN /\ m || P )')
    gmre = sm([sm([sm([d['sh']], 'adantr', SH), mc, w.inst('gtrp')], 'syl2anc',
                  '%s e. RR+' % GT('m'))], 'rpred', '%s e. RR' % GT('m'))
    tre = sm([gmre, w.s([], '0red', '( %s -> 0 e. RR )' % AM)], 'ifcld',
             '%s e. RR' % INTERM('D'))
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    return st([finP, tre], 'fsumrecl', '%s e. RR' % INNER('D')), mc, sm, finP


def lwre():
    w = W('lwre', 'The Selberg weight of a positive integer is a real number.')
    A = '( %s /\ D e. NN )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simpr', 'D e. NN')
    innerre, _, _, _ = _innerre(w, A, d, st, dnn)
    AD = '( %s /\ D || P )' % A
    sd = mkst(w, AD)
    d2 = shsteps(w, AD, (A, SH))
    facre = _facre(w, AD, d2, sd, sd([dnn], 'adantr', 'D e. NN'),
                   sd([], 'simpr', 'D || P'))
    prodre = sd([facre, sd([innerre], 'adantr', '%s e. RR' % INNER('D'))], 'remulcld',
                '( %s x. %s ) e. RR' % (FAC('D'), INNER('D')))
    case1 = sd([sd([], 'iftrued', '%s = ( %s x. %s )' % (LW('D'), FAC('D'), INNER('D'))),
                prodre], 'eqeltrd', '%s e. RR' % LW('D'))
    ADF = '( %s /\ -. D || P )' % A
    sdf = mkst(w, ADF)
    case2 = sdf([sdf([], 'iffalsed', '%s = 0' % LW('D')),
                 w.s([], '0red', '( %s -> 0 e. RR )' % ADF)], 'eqeltrd', '%s e. RR' % LW('D'))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s e. RR )' % (A, LW('D')))
    return w


def lwzero():
    w = W('lwzero', 'The Selberg weight vanishes above the square root of the level.')
    A = '( %s /\ D e. NN /\ -. ( D ^ 2 ) <_ Y )' % SH
    DVP = DV('P')
    d = shsteps(w, A, ((SH, 'simp1d'),))
    st = d['st']
    dnn = st([], 'simp2', 'D e. NN')
    nosq = st([], 'simp3', '-. ( D ^ 2 ) <_ Y')
    dre = st([dnn], 'nnred', 'D e. RR')
    d0 = st([st([dnn], 'nnrpd', 'D e. RR+')], 'rpge0d', '0 <_ D')
    innerre, mc, sm, finP = _innerre(w, A, d, st, dnn)
    # every summand of the inner sum vanishes
    AM = '( %s /\ m e. %s )' % (A, DVP)
    mnn = sm([mc], 'simpld', 'm e. NN')
    mre = sm([mnn], 'nnred', 'm e. RR')
    m1 = sm([mnn, w.inst('nnge1')], 'syl', '1 <_ m')
    dresm = sm([dre], 'adantr', 'D e. RR')
    d0m = sm([d0], 'adantr', '0 <_ D')
    dmre = sm([dresm, mre], 'remulcld', '( D x. m ) e. RR')
    dmge = sm([sm([sm([sm([dresm], 'recnd', 'D e. CC')], 'mulridd', '( D x. 1 ) = D')],
                  'eqcomd', 'D = ( D x. 1 )'),
               sm([w.s([], '1red', '( %s -> 1 e. RR )' % AM), mre, dresm, d0m, m1],
                  'lemul2ad', '( D x. 1 ) <_ ( D x. m )')], 'eqbrtrd', 'D <_ ( D x. m )')
    sqi = sm([sm([sm([dresm, d0m], 'jca', '( D e. RR /\ 0 <_ D )'),
                  sm([dmre, dmge], 'jca', '( ( D x. m ) e. RR /\ D <_ ( D x. m ) )')], 'jca',
                 '( ( D e. RR /\ 0 <_ D ) /\ ( ( D x. m ) e. RR /\ D <_ ( D x. m ) ) )'),
              w.inst('le2sq2')], 'syl', '( D ^ 2 ) <_ ( ( D x. m ) ^ 2 )')
    AMY = '( %s /\ ( ( D x. m ) ^ 2 ) <_ Y )' % AM
    smy = mkst(w, AMY)
    dsqle = smy([smy([smy([dresm], 'adantr', 'D e. RR')], 'resqcld', '( D ^ 2 ) e. RR'),
                 smy([smy([dmre], 'adantr', '( D x. m ) e. RR')], 'resqcld',
                     '( ( D x. m ) ^ 2 ) e. RR'),
                 smy([sm([d['yr']], 'adantr', 'Y e. RR')], 'adantr', 'Y e. RR'),
                 smy([sqi], 'adantr', '( D ^ 2 ) <_ ( ( D x. m ) ^ 2 )'),
                 smy([], 'simpr', '( ( D x. m ) ^ 2 ) <_ Y')], 'letrd', '( D ^ 2 ) <_ Y')
    noy = sm([sm([nosq], 'adantr', '-. ( D ^ 2 ) <_ Y'), dsqle], 'mtand',
             '-. ( ( D x. m ) ^ 2 ) <_ Y')
    nocond = sm([noy], 'intnanrd', '-. ( ( ( D x. m ) ^ 2 ) <_ Y /\ ( m gcd D ) = 1 )')
    zero = sm([nocond], 'iffalsed', '%s = 0' % INTERM('D'))
    innerz = st([st([zero], 'sumeq2dv',
                    '%s = sum_ m e. %s 0' % (INNER('D'), DVP)),
                 st([st([finP], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \/ %s e. Fin )' % (DVP, DVP)),
                     w.inst('sumz')], 'syl', 'sum_ m e. %s 0 = 0' % DVP)], 'eqtrd',
                '%s = 0' % INNER('D'))
    AD = '( %s /\ D || P )' % A
    sd = mkst(w, AD)
    d2 = shsteps(w, AD, (A, (SH, 'simp1d')))
    facre = _facre(w, AD, d2, sd, sd([dnn], 'adantr', 'D e. NN'), sd([], 'simpr', 'D || P'))
    case1 = sd([sd([], 'iftrued', '%s = ( %s x. %s )' % (LW('D'), FAC('D'), INNER('D'))),
                sd([sd([sd([innerz], 'adantr', '%s = 0' % INNER('D'))], 'oveq2d',
                       '( %s x. %s ) = ( %s x. 0 )' % (FAC('D'), INNER('D'), FAC('D'))),
                    sd([sd([facre], 'recnd', '%s e. CC' % FAC('D'))], 'mul01d',
                       '( %s x. 0 ) = 0' % FAC('D'))], 'eqtrd',
                   '( %s x. %s ) = 0' % (FAC('D'), INNER('D')))], 'eqtrd', '%s = 0' % LW('D'))
    ADF = '( %s /\ -. D || P )' % A
    sdf = mkst(w, ADF)
    case2 = sdf([], 'iffalsed', '%s = 0' % LW('D'))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s = 0 )' % (A, LW('D')))
    return w


def mp0lem():
    w = W('mp0lem', 'The ordered case of the vanishing of the Selberg Lambda squared '
                    'coefficients above the level.')
    A0 = '( %s /\ D e. NN /\ -. D <_ Y )' % SH
    TRI = '( J e. NN /\ K e. NN /\ ( D = ( J lcm K ) /\ J <_ K ) )'
    A = '( %s /\ %s )' % (A0, TRI)
    d = shsteps(w, A, (A0, (SH, 'simp1d')))
    st = d['st']
    dnn = st([st([], 'simpl', A0)], 'simp2d', 'D e. NN')
    noy = st([st([], 'simpl', A0)], 'simp3d', '-. D <_ Y')
    jnn = st([], 'simpr1', 'J e. NN')
    knn = st([], 'simpr2', 'K e. NN')
    lcmeq = st([st([], 'simpr3', '( D = ( J lcm K ) /\ J <_ K )')], 'simpld',
               'D = ( J lcm K )')
    jle = st([st([], 'simpr3', '( D = ( J lcm K ) /\ J <_ K )')], 'simprd', 'J <_ K')
    jz = st([jnn], 'nnzd', 'J e. ZZ')
    kz = st([knn], 'nnzd', 'K e. ZZ')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    dre = st([dnn], 'nnred', 'D e. RR')
    jre = st([jnn], 'nnred', 'J e. RR')
    kre = st([knn], 'nnred', 'K e. RR')
    k0 = st([st([knn], 'nnrpd', 'K e. RR+')], 'rpge0d', '0 <_ K')
    jknn = st([jnn, knn], 'nnmulcld', '( J x. K ) e. NN')
    jkz = st([jknn], 'nnzd', '( J x. K ) e. ZZ')
    jkre = st([jknn], 'nnred', '( J x. K ) e. RR')
    # D <_ ( K ^ 2 )
    dvd = st([st([st([jkz, jz, kz], '3jca',
                     '( ( J x. K ) e. ZZ /\ J e. ZZ /\ K e. ZZ )'), w.inst('lcmdvds')], 'syl',
                 '( ( J || ( J x. K ) /\ K || ( J x. K ) ) -> ( J lcm K ) || ( J x. K ) )'),
              st([st([st([jz, kz], 'jca', '( J e. ZZ /\ K e. ZZ )'), w.inst('dvdsmul1')], 'syl',
                     'J || ( J x. K )'),
                  st([st([jz, kz], 'jca', '( J e. ZZ /\ K e. ZZ )'), w.inst('dvdsmul2')], 'syl',
                     'K || ( J x. K )')], 'jca',
                 '( J || ( J x. K ) /\ K || ( J x. K ) )')], 'mpd',
             '( J lcm K ) || ( J x. K )')
    ddvd = st([lcmeq, dvd], 'eqbrtrd', 'D || ( J x. K )')
    dlejk = st([st([st([dz, jknn], 'jca', '( D e. ZZ /\ ( J x. K ) e. NN )'),
                    w.inst('dvdsle')], 'syl', '( D || ( J x. K ) -> D <_ ( J x. K ) )'), ddvd],
               'mpd', 'D <_ ( J x. K )')
    jksq = st([st([jre, kre, kre, k0, jle], 'lemul1ad', '( J x. K ) <_ ( K x. K )'),
               st([st([st([kre], 'recnd', 'K e. CC')], 'sqvald',
                      '( K ^ 2 ) = ( K x. K )')], 'eqcomd', '( K x. K ) = ( K ^ 2 )')],
              'breqtrd', '( J x. K ) <_ ( K ^ 2 )')
    ksqre = st([kre], 'resqcld', '( K ^ 2 ) e. RR')
    dleksq = st([dre, jkre, ksqre, dlejk, jksq], 'letrd', 'D <_ ( K ^ 2 )')
    # hence the square of K exceeds the level
    AY = '( %s /\ ( K ^ 2 ) <_ Y )' % A
    sy = mkst(w, AY)
    dley = sy([sy([dre], 'adantr', 'D e. RR'), sy([ksqre], 'adantr', '( K ^ 2 ) e. RR'),
               sy([d['yr']], 'adantr', 'Y e. RR'),
               sy([dleksq], 'adantr', 'D <_ ( K ^ 2 )'), sy([], 'simpr', '( K ^ 2 ) <_ Y')],
              'letrd', 'D <_ Y')
    noksq = st([noy, dley], 'mtand', '-. ( K ^ 2 ) <_ Y')
    lwk = st([st([d['sh'], knn, noksq], '3jca',
                 '( %s /\ K e. NN /\ -. ( K ^ 2 ) <_ Y )' % SH), w.inst('lwzero')], 'syl',
             '%s = 0' % LW('K'))
    lwjc = st([st([st([d['sh'], jnn], 'jca', '( %s /\ J e. NN )' % SH), w.inst('lwre')], 'syl',
                  '%s e. RR' % LW('J'))], 'recnd', '%s e. CC' % LW('J'))
    w.qed([st([lwk], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (LW('J'), LW('K'), LW('J'))),
           st([lwjc], 'mul01d', '( %s x. 0 ) = 0' % LW('J'))], 'eqtrd',
          '( %s -> ( %s x. %s ) = 0 )' % (A, LW('J'), LW('K')))
    return w


def mp0():
    w = W('mp0', 'The Selberg Lambda squared coefficients vanish above the level.')
    A = '( %s /\ D e. NN /\ -. D <_ Y )' % SH
    DVD = DV('D')
    IFT = 'if ( D = ( d lcm e ) , ( %s x. %s ) , 0 )' % (LW('d'), LW('e'))
    d = shsteps(w, A, ((SH, 'simp1d'),))
    st = d['st']
    dnn = st([], 'simp2', 'D e. NN')
    noy = st([], 'simp3', '-. D <_ Y')
    finD = st([dnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVD)

    def eld(v):
        return w.s([w.s([], 'breq1', '( x = %s -> ( x || D <-> %s || D ) )' % (v, v))], 'elrab',
                   '( %s e. %s <-> ( %s e. NN /\ %s || D ) )' % (v, DVD, v, v))

    eldd = eld('d')
    elde = eld('e')
    AD = '( %s /\ d e. %s )' % (A, DVD)
    sd = mkst(w, AD)
    ADE = '( %s /\ e e. %s )' % (AD, DVD)
    sde = mkst(w, ADE)
    dnnv = sde([sde([sde([eldd], 'a1i', '( d e. %s <-> ( d e. NN /\ d || D ) )' % DVD),
                     w.s([], 'simplr', '( %s -> d e. %s )' % (ADE, DVD))], 'mpbid',
                    '( d e. NN /\ d || D )')], 'simpld', 'd e. NN')
    ennv = sde([sde([sde([elde], 'a1i', '( e e. %s <-> ( e e. NN /\ e || D ) )' % DVD),
                     w.s([], 'simpr', '( %s -> e e. %s )' % (ADE, DVD))], 'mpbid',
                    '( e e. NN /\ e || D )')], 'simpld', 'e e. NN')
    shde = sde([d['sh']], 'ad2antrr', SH)
    ade = sde([st([], 'id', A)], 'ad2antrr', A)
    lwdc = sde([sde([sde([shde, dnnv], 'jca', '( %s /\ d e. NN )' % SH), w.inst('lwre')], 'syl',
                    '%s e. RR' % LW('d'))], 'recnd', '%s e. CC' % LW('d'))
    lwec = sde([sde([sde([shde, ennv], 'jca', '( %s /\ e e. NN )' % SH), w.inst('lwre')], 'syl',
                    '%s e. RR' % LW('e'))], 'recnd', '%s e. CC' % LW('e'))
    # the lcm case
    ALC = '( %s /\ D = ( d lcm e ) )' % ADE
    slc = mkst(w, ALC)
    ALC1 = '( %s /\ d <_ e )' % ALC
    s1 = mkst(w, ALC1)
    p1 = s1([s1([slc([ade], 'adantr', A)], 'adantr', A),
             s1([s1([slc([dnnv], 'adantr', 'd e. NN')], 'adantr', 'd e. NN'),
                 s1([slc([ennv], 'adantr', 'e e. NN')], 'adantr', 'e e. NN'),
                 s1([s1([slc([], 'simpr', 'D = ( d lcm e )')], 'adantr', 'D = ( d lcm e )'),
                     s1([], 'simpr', 'd <_ e')], 'jca',
                    '( D = ( d lcm e ) /\ d <_ e )')], '3jca',
                '( d e. NN /\ e e. NN /\ ( D = ( d lcm e ) /\ d <_ e ) )'),
             w.inst('mp0lem')], 'syl2anc', '( %s x. %s ) = 0' % (LW('d'), LW('e')))
    ALC2 = '( %s /\ e <_ d )' % ALC
    s2 = mkst(w, ALC2)
    lcmc = s2([s2([s2([s2([slc([dnnv], 'adantr', 'd e. NN')], 'adantr', 'd e. NN')], 'nnzd',
                      'd e. ZZ'),
                   s2([s2([slc([ennv], 'adantr', 'e e. NN')], 'adantr', 'e e. NN')], 'nnzd',
                      'e e. ZZ')], 'jca', '( d e. ZZ /\ e e. ZZ )'), w.inst('lcmcom')], 'syl',
              '( d lcm e ) = ( e lcm d )')
    deq = s2([s2([slc([], 'simpr', 'D = ( d lcm e )')], 'adantr', 'D = ( d lcm e )'),
              lcmc], 'eqtrd', 'D = ( e lcm d )')
    p2a = s2([s2([slc([ade], 'adantr', A)], 'adantr', A),
              s2([s2([slc([ennv], 'adantr', 'e e. NN')], 'adantr', 'e e. NN'),
                  s2([slc([dnnv], 'adantr', 'd e. NN')], 'adantr', 'd e. NN'),
                  s2([deq, s2([], 'simpr', 'e <_ d')], 'jca',
                     '( D = ( e lcm d ) /\ e <_ d )')], '3jca',
                 '( e e. NN /\ d e. NN /\ ( D = ( e lcm d ) /\ e <_ d ) )'),
              w.inst('mp0lem')], 'syl2anc', '( %s x. %s ) = 0' % (LW('e'), LW('d')))
    p2 = s2([s2([s2([slc([lwdc], 'adantr', '%s e. CC' % LW('d'))], 'adantr',
                    '%s e. CC' % LW('d')),
                 s2([slc([lwec], 'adantr', '%s e. CC' % LW('e'))], 'adantr',
                    '%s e. CC' % LW('e'))], 'mulcomd',
                '( %s x. %s ) = ( %s x. %s )' % (LW('d'), LW('e'), LW('e'), LW('d'))),
             p2a], 'eqtrd', '( %s x. %s ) = 0' % (LW('d'), LW('e')))
    tot = slc([slc([slc([slc([dnnv], 'adantr', 'd e. NN')], 'nnred', 'd e. RR'),
                    slc([slc([ennv], 'adantr', 'e e. NN')], 'nnred', 'e e. RR')], 'jca',
                   '( d e. RR /\ e e. RR )'), w.inst('letric')], 'syl',
              '( d <_ e \/ e <_ d )')
    prodz = slc([p1, p2, tot], 'mpjaodan', '( %s x. %s ) = 0' % (LW('d'), LW('e')))
    case1 = slc([slc([], 'iftrued', '%s = ( %s x. %s )' % (IFT, LW('d'), LW('e'))), prodz],
                'eqtrd', '%s = 0' % IFT)
    ANL = '( %s /\ -. D = ( d lcm e ) )' % ADE
    snl = mkst(w, ANL)
    case2 = snl([], 'iffalsed', '%s = 0' % IFT)
    termz = sde([case1, case2], 'pm2.61dan', '%s = 0' % IFT)
    innerz = sd([sd([termz], 'sumeq2dv',
                    'sum_ e e. %s %s = sum_ e e. %s 0' % (DVD, IFT, DVD)),
                 sd([sd([sd([finD], 'adantr', '%s e. Fin' % DVD)], 'olcd',
                        '( %s C_ ( ZZ>= ` 1 ) \/ %s e. Fin )' % (DVD, DVD)),
                     w.inst('sumz')], 'syl', 'sum_ e e. %s 0 = 0' % DVD)], 'eqtrd',
                'sum_ e e. %s %s = 0' % (DVD, IFT))
    w.qed([st([innerz], 'sumeq2dv',
              'sum_ d e. %s sum_ e e. %s %s = sum_ d e. %s 0' % (DVD, DVD, IFT, DVD)),
           st([st([finD], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \/ %s e. Fin )' % (DVD, DVD)),
               w.inst('sumz')], 'syl', 'sum_ d e. %s 0 = 0' % DVD)], 'eqtrd',
          '( %s -> sum_ d e. %s sum_ e e. %s %s = 0 )' % (A, DVD, DVD, IFT))
    return w


def ITERM(D, m='m'):
    return 'if ( ( ( %s x. %s ) ^ 2 ) <_ Y , %s , 0 )' % (D, m, GT(m))


def _qfacts(w, A, d, st, dnn, ddp):
    """Q = ( P / D ) : positive, D x. Q = P , coprime to D , Q || P"""
    Q = '( P / %s )' % 'D'
    pnn, psqf = d['pnn'], d['psqf']
    pcn = st([pnn], 'nncnd', 'P e. CC')
    dcn = st([dnn], 'nncnd', 'D e. CC')
    dne = st([dnn], 'nnne0d', 'D =/= 0')
    qnn = st([st([pnn, dnn, w.inst('nndivdvds')], 'syl2anc', '( D || P <-> %s e. NN )' % Q),
              ddp], 'mpbid', '%s e. NN' % Q)
    dq = st([pcn, dcn, dne], 'divcan2d', '( D x. %s ) = P' % Q)
    musq = st([st([dq], 'fveq2d', '( mmu ` ( D x. %s ) ) = ( mmu ` P )' % Q), psqf], 'eqnetrd',
              '( mmu ` ( D x. %s ) ) =/= 0' % Q)
    cop = st([st([dnn, qnn, musq], '3jca',
                 '( D e. NN /\ %s e. NN /\ ( mmu ` ( D x. %s ) ) =/= 0 )' % (Q, Q)),
              w.inst('sqfcop')], 'syl', '( D gcd %s ) = 1' % Q)
    qdp = st([st([st([st([dnn], 'nnzd', 'D e. ZZ'), st([qnn], 'nnzd', '%s e. ZZ' % Q)], 'jca',
                    '( D e. ZZ /\ %s e. ZZ )' % Q), w.inst('dvdsmul2')], 'syl',
                 '%s || ( D x. %s )' % (Q, Q)), dq], 'breqtrd', '%s || P' % Q)
    return Q, qnn, dq, cop, qdp


def lwinner():
    w = W('lwinner', 'The inner sum of the Selberg weight runs over the divisors of P / D.')
    A = '( %s /\ ( D e. NN /\ D || P ) )' % SH
    DVP = DV('P')
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    Q, qnn, dq, cop, qdp = _qfacts(w, A, d, st, dnn, ddp)
    DVQ = DV(Q)
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    qz = st([qnn], 'nnzd', '%s e. ZZ' % Q)
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    # DV ( Q ) C_ DV ( P )
    AX = '( %s /\ x e. NN )' % A
    sx = mkst(w, AX)
    AXQ = '( %s /\ x || %s )' % (AX, Q)
    sxq = mkst(w, AXQ)
    xdp = sxq([sxq([sxq([sxq([w.s([], 'simplr', '( %s -> x e. NN )' % AXQ)], 'nnzd', 'x e. ZZ'),
                         sxq([sx([qz], 'adantr', '%s e. ZZ' % Q)], 'adantr', '%s e. ZZ' % Q),
                         sxq([sx([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ')], '3jca',
                        '( x e. ZZ /\ %s e. ZZ /\ P e. ZZ )' % Q), w.inst('dvdstr')], 'syl',
                   '( ( x || %s /\ %s || P ) -> x || P )' % (Q, Q)),
               sxq([sxq([], 'simpr', 'x || %s' % Q),
                    sxq([sx([qdp], 'adantr', '%s || P' % Q)], 'adantr', '%s || P' % Q)], 'jca',
                   '( x || %s /\ %s || P )' % (Q, Q))], 'mpd', 'x || P')
    sub = st([sx([xdp], 'ex', '( x || %s -> x || P )' % Q)], 'ss2rabdv', '%s C_ %s' % (DVQ, DVP))

    def elm(S, X):
        return w.s([w.s([], 'breq1', '( x = m -> ( x || %s <-> m || %s ) )' % (X, X))], 'elrab',
                   '( m e. %s <-> ( m e. NN /\ m || %s ) )' % (S, X))

    elmQ = elm(DVQ, Q)
    elmP = elm(DVP, 'P')
    # on DV ( Q ) : the coprimality condition holds
    AQ = '( %s /\ m e. %s )' % (A, DVQ)
    sq = mkst(w, AQ)
    mcQ = sq([sq([elmQ], 'a1i', '( m e. %s <-> ( m e. NN /\ m || %s ) )' % (DVQ, Q)),
              sq([], 'simpr', 'm e. %s' % DVQ)], 'mpbid', '( m e. NN /\ m || %s )' % Q)
    mnnQ = sq([mcQ], 'simpld', 'm e. NN')
    mdQ = sq([mcQ], 'simprd', 'm || %s' % Q)
    mz = sq([mnnQ], 'nnzd', 'm e. ZZ')
    dgm = sq([sq([sq([sq([dz], 'adantr', 'D e. ZZ'), mz, sq([qz], 'adantr', '%s e. ZZ' % Q)],
                     '3jca', '( D e. ZZ /\ m e. ZZ /\ %s e. ZZ )' % Q),
                  sq([sq([cop], 'adantr', '( D gcd %s ) = 1' % Q), mdQ], 'jca',
                     '( ( D gcd %s ) = 1 /\ m || %s )' % (Q, Q))], 'jca',
                 '( ( D e. ZZ /\ m e. ZZ /\ %s e. ZZ ) /\ '
                 '( ( D gcd %s ) = 1 /\ m || %s ) )' % (Q, Q, Q)), w.inst('rpdvds')], 'syl',
             '( D gcd m ) = 1')
    mgd = sq([sq([sq([mz, sq([dz], 'adantr', 'D e. ZZ')], 'jca', '( m e. ZZ /\ D e. ZZ )'),
                  w.inst('gcdcom')], 'syl', '( m gcd D ) = ( D gcd m )'), dgm], 'eqtrd',
             '( m gcd D ) = 1')
    ifQ = sq([sq([mgd], 'biantrud',
                 '( ( ( D x. m ) ^ 2 ) <_ Y <-> '
                 '( ( ( D x. m ) ^ 2 ) <_ Y /\ ( m gcd D ) = 1 ) )')], 'ifbid',
             '%s = %s' % (ITERM('D'), INTERM('D')))
    sumQ = st([ifQ], 'sumeq2dv',
              'sum_ m e. %s %s = sum_ m e. %s %s' % (DVQ, ITERM('D'), DVQ, INTERM('D')))
    # closure of the summand on DV ( Q )
    gmreQ = sq([sq([sq([d['sh']], 'adantr', SH),
                    sq([mnnQ, sq([sq([sq([mz, sq([qz], 'adantr', '%s e. ZZ' % Q),
                                         sq([pz], 'adantr', 'P e. ZZ')], '3jca',
                                        '( m e. ZZ /\ %s e. ZZ /\ P e. ZZ )' % Q),
                                     w.inst('dvdstr')], 'syl',
                                    '( ( m || %s /\ %s || P ) -> m || P )' % (Q, Q)),
                                 sq([mdQ, sq([qdp], 'adantr', '%s || P' % Q)], 'jca',
                                    '( m || %s /\ %s || P )' % (Q, Q))], 'mpd', 'm || P')],
                       'jca', '( m e. NN /\ m || P )'), w.inst('gtrp')], 'syl2anc',
                   '%s e. RR+' % GT('m'))], 'rpred', '%s e. RR' % GT('m'))
    ccQ = sq([sq([gmreQ], 'recnd', '%s e. CC' % GT('m')),
              w.s([], '0cnd', '( %s -> 0 e. CC )' % AQ)], 'ifcld', '%s e. CC' % INTERM('D'))
    # off DV ( Q ) : the coprimality condition fails
    ADF = '( %s /\ m e. ( %s \ %s ) )' % (A, DVP, DVQ)
    sdf = mkst(w, ADF)
    mdif = w.s([], 'simpr', '( %s -> m e. ( %s \ %s ) )' % (ADF, DVP, DVQ))
    minP = sdf([mdif, w.inst('eldifi')], 'syl', 'm e. %s' % DVP)
    mnotQ = sdf([mdif, w.inst('eldifn')], 'syl', '-. m e. %s' % DVQ)
    mcP = sdf([sdf([elmP], 'a1i', '( m e. %s <-> ( m e. NN /\ m || P ) )' % DVP), minP], 'mpbid',
              '( m e. NN /\ m || P )')
    mnnP = sdf([mcP], 'simpld', 'm e. NN')
    mdP = sdf([mcP], 'simprd', 'm || P')
    ADC = '( %s /\ ( m gcd D ) = 1 )' % ADF
    sdc = mkst(w, ADC)
    mdq2 = sdc([sdc([sdc([sdc([sdc([mnnP], 'adantr', 'm e. NN')], 'nnzd', 'm e. ZZ'),
                          sdc([sdf([dz], 'adantr', 'D e. ZZ')], 'adantr', 'D e. ZZ'),
                          sdc([sdf([qz], 'adantr', '%s e. ZZ' % Q)], 'adantr', '%s e. ZZ' % Q)],
                         '3jca', '( m e. ZZ /\ D e. ZZ /\ %s e. ZZ )' % Q),
                     w.inst('coprmdvds')], 'syl',
                    '( ( m || ( D x. %s ) /\ ( m gcd D ) = 1 ) -> m || %s )' % (Q, Q)),
                sdc([sdc([sdc([mdP], 'adantr', 'm || P'),
                          sdc([sdc([sdf([dq], 'adantr', '( D x. %s ) = P' % Q)], 'adantr',
                                   '( D x. %s ) = P' % Q)], 'eqcomd',
                              'P = ( D x. %s )' % Q)], 'breqtrd', 'm || ( D x. %s )' % Q),
                     sdc([], 'simpr', '( m gcd D ) = 1')], 'jca',
                    '( m || ( D x. %s ) /\ ( m gcd D ) = 1 )' % Q)], 'mpd', 'm || %s' % Q)
    inQ = sdc([sdc([elmQ], 'a1i', '( m e. %s <-> ( m e. NN /\ m || %s ) )' % (DVQ, Q)),
               sdc([sdc([mnnP], 'adantr', 'm e. NN'), mdq2], 'jca',
                   '( m e. NN /\ m || %s )' % Q)], 'mpbird', 'm e. %s' % DVQ)
    nocop = sdf([mnotQ, inQ], 'mtand', '-. ( m gcd D ) = 1')
    zero = sdf([sdf([nocop], 'intnand',
                    '-. ( ( ( D x. m ) ^ 2 ) <_ Y /\ ( m gcd D ) = 1 )')], 'iffalsed',
               '%s = 0' % INTERM('D'))
    ext = st([sub, ccQ, zero, finP], 'fsumss',
             'sum_ m e. %s %s = sum_ m e. %s %s' % (DVQ, INTERM('D'), DVP, INTERM('D')))
    w.qed([sumQ, ext], 'eqtrd',
          '( %s -> sum_ m e. %s %s = %s )' % (A, DVQ, ITERM('D'), INNER('D')))
    return w


def lwsum():
    w = W('lwsum', 'The truncated divisor sum of the Selberg terms above D factors as the Selberg '
                   'term of D times the inner sum of the Selberg weight.')
    A = '( %s /\ ( D e. NN /\ D || P ) )' % SH
    DVP = DV('P')
    DVD = DV('D')
    JM = '( j x. m )'
    DM = '( D x. m )'
    LTERM = 'if ( ( D || l /\ ( l ^ 2 ) <_ Y ) , %s , 0 )' % GT('l')
    JTERM = 'if ( ( D || %s /\ ( %s ^ 2 ) <_ Y ) , %s , 0 )' % (JM, JM, GT(JM))
    DTERM = 'if ( ( D || %s /\ ( %s ^ 2 ) <_ Y ) , %s , 0 )' % (DM, DM, GT(DM))
    T2 = 'if ( ( %s ^ 2 ) <_ Y , %s , 0 )' % (DM, GT(DM))
    AJ = 'if ( j = D , 1 , 0 )'
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    Q, qnn, dq, cop, qdp = _qfacts(w, A, d, st, dnn, ddp)
    DVQ = DV(Q)
    DVZ = DV('( D x. %s )' % Q)
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    qz = st([qnn], 'nnzd', '%s e. ZZ' % Q)
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    finD = st([dnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVD)
    finQ = st([qnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVQ)

    def elv(v, S, X):
        return w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (v, X, v, X))],
                   'elrab', '( %s e. %s <-> ( %s e. NN /\ %s || %s ) )' % (v, S, v, v, X))

    eljD = elv('j', DVD, 'D')
    elmQ = elv('m', DVQ, Q)

    def mfacts(ante, memstep, lift):
        """facts about m e. DV ( Q ) under `ante`; lift(step, formula) moves a step at A"""
        sb = mkst(w, ante)
        mc = sb([sb([elmQ], 'a1i', '( m e. %s <-> ( m e. NN /\ m || %s ) )' % (DVQ, Q)),
                 memstep], 'mpbid', '( m e. NN /\ m || %s )' % Q)
        mnn = sb([mc], 'simpld', 'm e. NN')
        mdQ = sb([mc], 'simprd', 'm || %s' % Q)
        mz = sb([mnn], 'nnzd', 'm e. ZZ')
        mdP = sb([sb([sb([mz, lift(qz, '%s e. ZZ' % Q), lift(pz, 'P e. ZZ')], '3jca',
                         '( m e. ZZ /\ %s e. ZZ /\ P e. ZZ )' % Q), w.inst('dvdstr')], 'syl',
                      '( ( m || %s /\ %s || P ) -> m || P )' % (Q, Q)),
                  sb([mdQ, lift(qdp, '%s || P' % Q)], 'jca',
                     '( m || %s /\ %s || P )' % (Q, Q))], 'mpd', 'm || P')
        dgm = sb([sb([sb([lift(dz, 'D e. ZZ'), mz, lift(qz, '%s e. ZZ' % Q)], '3jca',
                         '( D e. ZZ /\ m e. ZZ /\ %s e. ZZ )' % Q),
                      sb([lift(cop, '( D gcd %s ) = 1' % Q), mdQ], 'jca',
                         '( ( D gcd %s ) = 1 /\ m || %s )' % (Q, Q))], 'jca',
                     '( ( D e. ZZ /\ m e. ZZ /\ %s e. ZZ ) /\ ( ( D gcd %s ) = 1 /\ m || %s ) )'
                     % (Q, Q, Q)), w.inst('rpdvds')], 'syl', '( D gcd m ) = 1')
        gtsplit = sb([sb([lift(d['sh'], SH),
                          sb([sb([lift(dnn, 'D e. NN'), lift(ddp, 'D || P')], 'jca',
                                 '( D e. NN /\ D || P )'),
                              sb([mnn, mdP], 'jca', '( m e. NN /\ m || P )'), dgm], '3jca',
                             '( ( D e. NN /\ D || P ) /\ ( m e. NN /\ m || P ) /\ '
                             '( D gcd m ) = 1 )')], 'jca',
                         '( %s /\ ( ( D e. NN /\ D || P ) /\ ( m e. NN /\ m || P ) /\ '
                         '( D gcd m ) = 1 ) )' % SH), w.inst('gtmul')], 'syl',
                     '%s = ( %s x. %s )' % (GT(DM), GT('D'), GT('m')))
        gdc = sb([sb([sb([lift(d['sh'], SH),
                          sb([lift(dnn, 'D e. NN'), lift(ddp, 'D || P')], 'jca',
                             '( D e. NN /\ D || P )'), w.inst('gtrp')], 'syl2anc',
                         '%s e. RR+' % GT('D'))], 'rpred', '%s e. RR' % GT('D'))], 'recnd',
                 '%s e. CC' % GT('D'))
        gmc = sb([sb([sb([lift(d['sh'], SH), sb([mnn, mdP], 'jca', '( m e. NN /\ m || P )'),
                          w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('m'))], 'rpred',
                     '%s e. RR' % GT('m'))], 'recnd', '%s e. CC' % GT('m'))
        gdmc = sb([gtsplit, sb([gdc, gmc], 'mulcld',
                                '( %s x. %s ) e. CC' % (GT('D'), GT('m')))], 'eqeltrd',
                  '%s e. CC' % GT(DM))
        t2c = sb([gdmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % ante)], 'ifcld',
                 '%s e. CC' % T2)
        return sb, mnn, mz, mdP, dgm, gtsplit, gdc, gmc, t2c

    # ---- at ( A /\ m e. DV ( Q ) )
    AM = '( %s /\ m e. %s )' % (A, DVQ)
    sm, mnn, mz, mdP, dgm, gtsplit, gdc, gmc, t2cM = mfacts(
        AM, w.s([], 'simpr', '( %s -> m e. %s )' % (AM, DVQ)),
        lambda step, f: w.s([step], 'adantr', '( %s -> %s )' % (AM, f)))
    AMT = '( %s /\ ( %s ^ 2 ) <_ Y )' % (AM, DM)
    smt = mkst(w, AMT)
    c1 = smt([smt([smt([], 'iftrued', '%s = %s' % (T2, GT(DM))),
                   smt([gtsplit], 'adantr',
                       '%s = ( %s x. %s )' % (GT(DM), GT('D'), GT('m')))], 'eqtrd',
                  '%s = ( %s x. %s )' % (T2, GT('D'), GT('m'))),
              smt([smt([], 'iftrued', '%s = %s' % (ITERM('D'), GT('m')))], 'oveq2d',
                  '( %s x. %s ) = ( %s x. %s )'
                  % (GT('D'), ITERM('D'), GT('D'), GT('m')))], 'eqtr4d',
             '%s = ( %s x. %s )' % (T2, GT('D'), ITERM('D')))
    AMF = '( %s /\ -. ( %s ^ 2 ) <_ Y )' % (AM, DM)
    smf = mkst(w, AMF)
    c2 = smf([smf([], 'iffalsed', '%s = 0' % T2),
              smf([smf([smf([], 'iffalsed', '%s = 0' % ITERM('D'))], 'oveq2d',
                       '( %s x. %s ) = ( %s x. 0 )' % (GT('D'), ITERM('D'), GT('D'))),
                   smf([smf([gdc], 'adantr', '%s e. CC' % GT('D'))], 'mul01d',
                       '( %s x. 0 ) = 0' % GT('D'))], 'eqtrd',
                  '( %s x. %s ) = 0' % (GT('D'), ITERM('D')))], 'eqtr4d',
             '%s = ( %s x. %s )' % (T2, GT('D'), ITERM('D')))
    t2eq = sm([c1, c2], 'pm2.61dan', '%s = ( %s x. %s )' % (T2, GT('D'), ITERM('D')))
    itc = sm([gmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % AM)], 'ifcld', '%s e. CC' % ITERM('D'))
    gdcA = st([st([st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'), w.inst('gtrp')],
                      'syl2anc', '%s e. RR+' % GT('D'))], 'rpred', '%s e. RR' % GT('D'))],
              'recnd', '%s e. CC' % GT('D'))
    sumQ = st([st([t2eq], 'sumeq2dv',
                  'sum_ m e. %s %s = sum_ m e. %s ( %s x. %s )'
                  % (DVQ, T2, DVQ, GT('D'), ITERM('D'))),
               st([st([finQ, gdcA, itc], 'fsummulc2',
                      '( %s x. sum_ m e. %s %s ) = sum_ m e. %s ( %s x. %s )'
                      % (GT('D'), DVQ, ITERM('D'), DVQ, GT('D'), ITERM('D')))], 'eqcomd',
                  'sum_ m e. %s ( %s x. %s ) = ( %s x. sum_ m e. %s %s )'
                  % (DVQ, GT('D'), ITERM('D'), GT('D'), DVQ, ITERM('D')))], 'eqtrd',
              'sum_ m e. %s %s = ( %s x. sum_ m e. %s %s )'
              % (DVQ, T2, GT('D'), DVQ, ITERM('D')))
    sumQ2 = st([sumQ, st([st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'),
                              w.inst('lwinner')], 'syl2anc',
                             'sum_ m e. %s %s = %s' % (DVQ, ITERM('D'), INNER('D')))], 'oveq2d',
                         '( %s x. sum_ m e. %s %s ) = ( %s x. %s )'
                         % (GT('D'), DVQ, ITERM('D'), GT('D'), INNER('D')))], 'eqtrd',
               'sum_ m e. %s %s = ( %s x. %s )' % (DVQ, T2, GT('D'), INNER('D')))
    # ---- the singleton sum over DV ( D )
    ddvd = st([w.s([w.s([], 'breq1', '( x = D -> ( x || D <-> D || D ) )')], 'elrab',
                   '( D e. %s <-> ( D e. NN /\ D || D ) )' % DVD),
               st([dnn, st([dz, w.inst('iddvds')], 'syl', 'D || D')], 'jca',
                  '( D e. NN /\ D || D )')], 'sylibr', 'D e. %s' % DVD)
    snd = st([ddvd], 'snssd', '{ D } C_ %s' % DVD)
    ASN = '( %s /\ j e. { D } )' % A
    ssn = mkst(w, ASN)
    cc1 = ssn([w.s([], '1cnd', '( %s -> 1 e. CC )' % ASN),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % ASN)], 'ifcld', '%s e. CC' % AJ)
    ADF = '( %s /\ j e. ( %s \ { D } ) )' % (A, DVD)
    sdf = mkst(w, ADF)
    zerj = sdf([sdf([sdf([sdf([], 'simpr', 'j e. ( %s \ { D } )' % DVD), w.inst('eldifsni')],
                         'syl', 'j =/= D')], 'neneqd', '-. j = D')], 'iffalsed', '%s = 0' % AJ)
    sss = st([snd, cc1, zerj, finD], 'fsumss',
             'sum_ j e. { D } %s = sum_ j e. %s %s' % (AJ, DVD, AJ))
    instsn = w.s([w.s([w.s([], 'id', '( j = D -> j = D )')], 'iftrued',
                      '( j = D -> %s = 1 )' % AJ)], 'sumsn',
                 '( ( D e. _V /\ 1 e. CC ) -> sum_ j e. { D } %s = 1 )' % AJ)
    snval = st([st([dnn], 'elexd', 'D e. _V'),
                st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), instsn], 'syl2anc',
               'sum_ j e. { D } %s = 1' % AJ)
    sumj = st([st([sss], 'eqcomd', 'sum_ j e. %s %s = sum_ j e. { D } %s' % (DVD, AJ, AJ)),
               snval], 'eqtrd', 'sum_ j e. %s %s = 1' % (DVD, AJ))
    # ---- the fsumdvdsmul hypotheses
    AJD = '( %s /\ j e. %s )' % (A, DVD)
    h4 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % AJD),
              w.s([], '0cnd', '( %s -> 0 e. CC )' % AJD)], 'ifcld', '( %s -> %s e. CC )'
             % (AJD, AJ))
    AJM = '( %s /\ ( j e. %s /\ m e. %s ) )' % (A, DVD, DVQ)
    jmem = w.s([w.s([], 'simpr', '( %s -> ( j e. %s /\ m e. %s ) )' % (AJM, DVD, DVQ))],
               'simpld', '( %s -> j e. %s )' % (AJM, DVD))
    mmem = w.s([w.s([], 'simpr', '( %s -> ( j e. %s /\ m e. %s ) )' % (AJM, DVD, DVQ))],
               'simprd', '( %s -> m e. %s )' % (AJM, DVQ))
    sjm, mnn2, mz2, mdP2, dgm2, gtsplit2, gdc2, gmc2, t2c2 = mfacts(
        AJM, mmem, lambda step, f: w.s([step], 'adantr', '( %s -> %s )' % (AJM, f)))
    jcD = sjm([sjm([eljD], 'a1i', '( j e. %s <-> ( j e. NN /\ j || D ) )' % DVD), jmem], 'mpbid',
              '( j e. NN /\ j || D )')
    jnn2 = sjm([jcD], 'simpld', 'j e. NN')
    jdD2 = sjm([jcD], 'simprd', 'j || D')
    jz2 = sjm([jnn2], 'nnzd', 'j e. ZZ')
    dzj = sjm([dz], 'adantr', 'D e. ZZ')
    # case j = D
    AJE = '( %s /\ j = D )' % AJM
    sje = mkst(w, AJE)
    jmeq = sje([sje([], 'simpr', 'j = D')], 'oveq1d', '%s = %s' % (JM, DM))
    gteq = sje([sje([jmeq], 'fveq2d', '( V ` %s ) = ( V ` %s )' % (JM, DM)),
                sje([sje([sje([jmeq], 'breq2d', '( r || %s <-> r || %s )' % (JM, DM))],
                        'rabbidv', '%s = %s' % (PF(JM), PF(DM)))], 'prodeq1d',
                    '%s = %s' % (PR(JM), PR(DM)))], 'oveq12d', '%s = %s' % (GT(JM), GT(DM)))
    condeq = sje([sje([jmeq], 'breq2d', '( D || %s <-> D || %s )' % (JM, DM)),
                  sje([sje([jmeq], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (JM, DM))], 'breq1d',
                      '( ( %s ^ 2 ) <_ Y <-> ( %s ^ 2 ) <_ Y )' % (JM, DM))], 'anbi12d',
                 '( ( D || %s /\ ( %s ^ 2 ) <_ Y ) <-> ( D || %s /\ ( %s ^ 2 ) <_ Y ) )'
                 % (JM, JM, DM, DM))
    jrhs = sje([condeq, gteq], 'ifbieq1d', '%s = %s' % (JTERM, DTERM))
    ddm = sje([sje([sje([sje([dzj], 'adantr', 'D e. ZZ'),
                         sje([mz2], 'adantr', 'm e. ZZ')], 'jca',
                        '( D e. ZZ /\ m e. ZZ )'), w.inst('dvdsmul1')], 'syl', 'D || %s' % DM)],
              'biantrurd', '( ( %s ^ 2 ) <_ Y <-> ( D || %s /\ ( %s ^ 2 ) <_ Y ) )'
              % (DM, DM, DM))
    drhs = sje([ddm], 'ifbid', '%s = %s' % (T2, DTERM))
    jlhs = sje([sje([sje([], 'iftrued', '%s = 1' % AJ)], 'oveq1d',
                    '( %s x. %s ) = ( 1 x. %s )' % (AJ, T2, T2)),
                sje([sje([t2c2], 'adantr', '%s e. CC' % T2)], 'mullidd',
                    '( 1 x. %s ) = %s' % (T2, T2))], 'eqtrd',
               '( %s x. %s ) = %s' % (AJ, T2, T2))
    case1 = sje([sje([jlhs, drhs], 'eqtrd', '( %s x. %s ) = %s' % (AJ, T2, DTERM)),
                 sje([jrhs], 'eqcomd', '%s = %s' % (DTERM, JTERM))], 'eqtrd',
                '( %s x. %s ) = %s' % (AJ, T2, JTERM))
    # case -. j = D
    AJF = '( %s /\ -. j = D )' % AJM
    sjf = mkst(w, AJF)
    AJFD = '( %s /\ D || %s )' % (AJF, JM)
    sjfd = mkst(w, AJFD)
    dz3 = sjfd([dzj], 'ad2antrr', 'D e. ZZ')
    mz3 = sjfd([mz2], 'ad2antrr', 'm e. ZZ')
    jz3 = sjfd([jz2], 'ad2antrr', 'j e. ZZ')
    imp3 = sjfd([sjfd([dz3, mz3, jz3], '3jca', '( D e. ZZ /\ m e. ZZ /\ j e. ZZ )'),
                 w.inst('coprmdvds')], 'syl',
                '( ( D || ( m x. j ) /\ ( D gcd m ) = 1 ) -> D || j )')
    comm3 = sjfd([sjfd([jz3], 'zcnd', 'j e. CC'), sjfd([mz3], 'zcnd', 'm e. CC')], 'mulcomd',
                 '%s = ( m x. j )' % JM)
    dmj0 = sjfd([sjfd([], 'simpr', 'D || %s' % JM), comm3], 'breqtrd', 'D || ( m x. j )')
    conj3 = sjfd([dmj0, sjfd([dgm2], 'ad2antrr', '( D gcd m ) = 1')], 'jca',
                 '( D || ( m x. j ) /\ ( D gcd m ) = 1 )')
    dmj = sjfd([imp3, conj3], 'mpd', 'D || j')
    jeqD = sjfd([sjfd([sjfd([sjfd([jnn2], 'ad2antrr', 'j e. NN')], 'nnnn0d', 'j e. NN0'),
                       sjfd([sjm([dnn], 'adantr', 'D e. NN')], 'ad2antrr', 'D e. NN0')
                       if False else
                       sjfd([sjfd([sjm([dnn], 'adantr', 'D e. NN')], 'ad2antrr', 'D e. NN')],
                            'nnnn0d', 'D e. NN0')], 'jca', '( j e. NN0 /\ D e. NN0 )'),
                 sjfd([sjfd([jdD2], 'ad2antrr', 'j || D'), dmj], 'jca',
                      '( j || D /\ D || j )'), w.inst('dvdseq')], 'syl2anc', 'j = D')
    nodvd = sjf([sjf([], 'simpr', '-. j = D'), jeqD], 'mtand', '-. D || %s' % JM)
    case2 = sjf([sjf([sjf([sjf([], 'iffalsed', '%s = 0' % AJ)], 'oveq1d',
                          '( %s x. %s ) = ( 0 x. %s )' % (AJ, T2, T2)),
                      sjf([sjf([t2c2], 'adantr', '%s e. CC' % T2)], 'mul02d',
                          '( 0 x. %s ) = 0' % T2)], 'eqtrd', '( %s x. %s ) = 0' % (AJ, T2)),
                 sjf([sjf([sjf([nodvd], 'intnanrd',
                               '-. ( D || %s /\ ( %s ^ 2 ) <_ Y )' % (JM, JM))], 'iffalsed',
                          '%s = 0' % JTERM)], 'eqcomd', '0 = %s' % JTERM)], 'eqtrd',
                '( %s x. %s ) = %s' % (AJ, T2, JTERM))
    h6 = sjm([case1, case2], 'pm2.61dan', '( %s x. %s ) = %s' % (AJ, T2, JTERM))
    h7 = w.s([w.s([w.s([], 'breq2', '( l = %s -> ( D || l <-> D || %s ) )' % (JM, JM)),
                   w.s([w.s([], 'oveq1', '( l = %s -> ( l ^ 2 ) = ( %s ^ 2 ) )' % (JM, JM))],
                       'breq1d', '( l = %s -> ( ( l ^ 2 ) <_ Y <-> ( %s ^ 2 ) <_ Y ) )'
                       % (JM, JM))], 'anbi12d',
                  '( l = %s -> ( ( D || l /\ ( l ^ 2 ) <_ Y ) <-> '
                  '( D || %s /\ ( %s ^ 2 ) <_ Y ) ) )' % (JM, JM, JM)),
              w.s([w.s([], 'fveq2', '( l = %s -> ( V ` l ) = ( V ` %s ) )' % (JM, JM)),
                   w.s([w.s([w.s([], 'breq2', '( l = %s -> ( r || l <-> r || %s ) )' % (JM, JM))],
                            'rabbidv', '( l = %s -> %s = %s )' % (JM, PF('l'), PF(JM)))],
                       'prodeq1d', '( l = %s -> %s = %s )' % (JM, PR('l'), PR(JM)))], 'oveq12d',
                  '( l = %s -> %s = %s )' % (JM, GT('l'), GT(JM)))], 'ifbieq1d',
             '( l = %s -> %s = %s )' % (JM, LTERM, JTERM))
    mul = st([dnn, qnn, cop,
              w.s([], 'eqid', '%s = %s' % (DVD, DVD)),
              w.s([], 'eqid', '%s = %s' % (DVQ, DVQ)),
              w.s([], 'eqid', '%s = %s' % (DVZ, DVZ)), h4, t2cM, h6, h7], 'fsumdvdsmul',
             '( sum_ j e. %s %s x. sum_ m e. %s %s ) = sum_ l e. %s %s'
             % (DVD, AJ, DVQ, T2, DVZ, LTERM))
    zrab = st([st([dq], 'breq2d', '( x || ( D x. %s ) <-> x || P )' % Q)], 'rabbidv',
              '%s = %s' % (DVZ, DVP))
    zsum = st([zrab], 'sumeq1d',
              'sum_ l e. %s %s = sum_ l e. %s %s' % (DVZ, LTERM, DVP, LTERM))
    innc2 = st([st([st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'),
                       w.inst('lwinner')], 'syl2anc',
                      'sum_ m e. %s %s = %s' % (DVQ, ITERM('D'), INNER('D')))], 'eqcomd',
                   '%s = sum_ m e. %s %s' % (INNER('D'), DVQ, ITERM('D'))),
                st([finQ, itc], 'fsumcl', 'sum_ m e. %s %s e. CC' % (DVQ, ITERM('D')))],
               'eqeltrd', '%s e. CC' % INNER('D'))
    prodcc = st([gdcA, innc2], 'mulcld', '( %s x. %s ) e. CC' % (GT('D'), INNER('D')))
    lhs = st([st([sumj, sumQ2], 'oveq12d',
                 '( sum_ j e. %s %s x. sum_ m e. %s %s ) = ( 1 x. ( %s x. %s ) )'
                 % (DVD, AJ, DVQ, T2, GT('D'), INNER('D'))),
              st([prodcc], 'mullidd',
                 '( 1 x. ( %s x. %s ) ) = ( %s x. %s )'
                 % (GT('D'), INNER('D'), GT('D'), INNER('D')))], 'eqtrd',
             '( sum_ j e. %s %s x. sum_ m e. %s %s ) = ( %s x. %s )'
             % (DVD, AJ, DVQ, T2, GT('D'), INNER('D')))
    w.qed([st([st([zsum], 'eqcomd',
                  'sum_ l e. %s %s = sum_ l e. %s %s' % (DVP, LTERM, DVZ, LTERM)),
               st([mul], 'eqcomd',
                  'sum_ l e. %s %s = ( sum_ j e. %s %s x. sum_ m e. %s %s )'
                  % (DVZ, LTERM, DVD, AJ, DVQ, T2))], 'eqtrd',
              'sum_ l e. %s %s = ( sum_ j e. %s %s x. sum_ m e. %s %s )'
              % (DVP, LTERM, DVD, AJ, DVQ, T2)), lhs], 'eqtrd',
          '( %s -> sum_ l e. %s %s = ( %s x. %s ) )' % (A, DVP, LTERM, GT('D'), INNER('D')))
    return w


def lwdvds():
    w = W('lwdvds', 'The key identity of the Selberg weights.')
    A = '( %s /\ D e. NN )' % SH
    DVP = DV('P')
    LTERM = 'if ( ( D || l /\ ( l ^ 2 ) <_ Y ) , %s , 0 )' % GT('l')
    SL = 'sum_ l e. %s %s' % (DVP, LTERM)
    RHS = '( ( ( 1 / %s ) x. ( mmu ` D ) ) x. %s )' % (SS(), SL)
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simpr', 'D e. NN')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    vdc = st([st([d['vf'], dnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` D ) e. RR')], 'recnd',
             '( V ` D ) e. CC')
    muc = st([st([dnn, w.inst('mucl')], 'syl', '( mmu ` D ) e. ZZ')], 'zcnd',
             '( mmu ` D ) e. CC')
    ssc = st([st([st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())], 'rpreccld',
                 '( 1 / %s ) e. RR+' % SS())], 'rpcnd', '( 1 / %s ) e. CC' % SS())
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    ell = w.s([w.s([], 'breq1', '( x = l -> ( x || P <-> l || P ) )')], 'elrab',
              '( l e. %s <-> ( l e. NN /\ l || P ) )' % DVP)
    # ---------- case D || P
    AD = '( %s /\ D || P )' % A
    sd = mkst(w, AD)
    d2 = shsteps(w, AD, (A, SH))
    dnn2 = sd([dnn], 'adantr', 'D e. NN')
    ddp2 = sd([], 'simpr', 'D || P')
    lsum = sd([d2['sh'], sd([dnn2, ddp2], 'jca', '( D e. NN /\ D || P )'), w.inst('lwsum')],
              'syl2anc', '%s = ( %s x. %s )' % (SL, GT('D'), INNER('D')))
    a = '( V ` D )'
    ai = '( 1 / ( V ` D ) )'
    g = GT('D')
    u = '( mmu ` D )'
    sr = '( 1 / %s )' % SS()
    i = INNER('D')
    X = '( ( %s x. %s ) x. ( %s x. %s ) )' % (ai, g, u, sr)
    vrp = sd([d2['sh'], sd([dnn2, ddp2], 'jca', '( D e. NN /\ D || P )'), w.inst('vdrp')],
             'syl2anc', '%s e. RR+' % a)
    ac = sd([vdc], 'adantr', '%s e. CC' % a)
    ane = sd([vrp], 'rpne0d', '%s =/= 0' % a)
    aic = sd([sd([vrp], 'rpreccld', '%s e. RR+' % ai)], 'rpcnd', '%s e. CC' % ai)
    gc = sd([sd([sd([d2['sh'], sd([dnn2, ddp2], 'jca', '( D e. NN /\ D || P )'),
                     w.inst('gtrp')], 'syl2anc', '%s e. RR+' % g)], 'rpred', '%s e. RR' % g)],
            'recnd', '%s e. CC' % g)
    uc = sd([muc], 'adantr', '%s e. CC' % u)
    src = sd([ssc], 'adantr', '%s e. CC' % sr)
    Q, qnn, dq, cop, qdp = _qfacts(w, AD, d2, sd, dnn2, ddp2)
    DVQ = DV(Q)
    finQ = sd([qnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVQ)
    AM = '( %s /\ m e. %s )' % (AD, DVQ)
    sm = mkst(w, AM)
    elmQ = w.s([w.s([], 'breq1', '( x = m -> ( x || %s <-> m || %s ) )' % (Q, Q))], 'elrab',
               '( m e. %s <-> ( m e. NN /\ m || %s ) )' % (DVQ, Q))
    mcQ = sm([sm([elmQ], 'a1i', '( m e. %s <-> ( m e. NN /\ m || %s ) )' % (DVQ, Q)),
              sm([], 'simpr', 'm e. %s' % DVQ)], 'mpbid', '( m e. NN /\ m || %s )' % Q)
    mnn = sm([mcQ], 'simpld', 'm e. NN')
    mz = sm([mnn], 'nnzd', 'm e. ZZ')
    mdP = sm([sm([sm([mz, sm([sd([qnn], 'nnzd', '%s e. ZZ' % Q)], 'adantr', '%s e. ZZ' % Q),
                      sm([sd([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ')], '3jca',
                     '( m e. ZZ /\ %s e. ZZ /\ P e. ZZ )' % Q), w.inst('dvdstr')], 'syl',
                  '( ( m || %s /\ %s || P ) -> m || P )' % (Q, Q)),
              sm([sm([mcQ], 'simprd', 'm || %s' % Q), sm([qdp], 'adantr', '%s || P' % Q)], 'jca',
                 '( m || %s /\ %s || P )' % (Q, Q))], 'mpd', 'm || P')
    gmc = sm([sm([sm([sm([d2['sh']], 'adantr', SH), sm([mnn, mdP], 'jca',
                                                       '( m e. NN /\ m || P )'),
                      w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('m'))], 'rpred',
                 '%s e. RR' % GT('m'))], 'recnd', '%s e. CC' % GT('m'))
    itc = sm([gmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % AM)], 'ifcld', '%s e. CC' % ITERM('D'))
    ic = sd([sd([sd([d2['sh'], sd([dnn2, ddp2], 'jca', '( D e. NN /\ D || P )'),
                     w.inst('lwinner')], 'syl2anc',
                    'sum_ m e. %s %s = %s' % (DVQ, ITERM('D'), i))], 'eqcomd',
                '%s = sum_ m e. %s %s' % (i, DVQ, ITERM('D'))),
             sd([finQ, itc], 'fsumcl', 'sum_ m e. %s %s e. CC' % (DVQ, ITERM('D')))], 'eqeltrd',
            '%s e. CC' % i)
    # the algebra
    recid = sd([sd([ac, ane], 'jca', '( %s e. CC /\ %s =/= 0 )' % (a, a)), w.inst('recid')],
               'syl', '( %s x. %s ) = 1' % (a, ai))
    e1 = sd([sd([sd([ac, aic, gc], 'mulassd',
                    '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (a, ai, g, a, ai, g))],
                'eqcomd', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (a, ai, g, a, ai, g)),
             sd([sd([recid], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (a, ai, g, g)),
                 sd([gc], 'mullidd', '( 1 x. %s ) = %s' % (g, g))], 'eqtrd',
                '( ( %s x. %s ) x. %s ) = %s' % (a, ai, g, g))], 'eqtrd',
            '( %s x. ( %s x. %s ) ) = %s' % (a, ai, g, g))
    usc = sd([uc, src], 'mulcld', '( %s x. %s ) e. CC' % (u, sr))
    aigc = sd([aic, gc], 'mulcld', '( %s x. %s ) e. CC' % (ai, g))
    e3 = sd([sd([sd([ac, aigc, usc], 'mulassd',
                    '( ( %s x. ( %s x. %s ) ) x. ( %s x. %s ) ) = '
                    '( %s x. ( ( %s x. %s ) x. ( %s x. %s ) ) )'
                    % (a, ai, g, u, sr, a, ai, g, u, sr))], 'eqcomd',
                '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) x. ( %s x. %s ) )'
                % (a, X, a, ai, g, u, sr)),
             sd([e1], 'oveq1d',
                '( ( %s x. ( %s x. %s ) ) x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )'
                % (a, ai, g, u, sr, g, u, sr))], 'eqtrd',
            '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (a, X, g, u, sr))
    Xc = sd([aigc, usc], 'mulcld', '%s e. CC' % X)
    e5 = sd([sd([sd([ac, Xc, ic], 'mulassd',
                    '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (a, X, i, a, X, i))],
                'eqcomd', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (a, X, i, a, X, i)),
             sd([e3], 'oveq1d',
                '( ( %s x. %s ) x. %s ) = ( ( %s x. ( %s x. %s ) ) x. %s )'
                % (a, X, i, g, u, sr, i))], 'eqtrd',
            '( %s x. ( %s x. %s ) ) = ( ( %s x. ( %s x. %s ) ) x. %s )' % (a, X, i, g, u, sr, i))
    # the right-hand side
    r1 = sd([sd([src, uc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (sr, u, u, sr))], 'oveq1d',
            '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )'
            % (sr, u, g, i, u, sr, g, i))
    r2 = sd([sd([usc, gc, ic], 'mulassd',
                '( ( ( %s x. %s ) x. %s ) x. %s ) = ( ( %s x. %s ) x. ( %s x. %s ) )'
                % (u, sr, g, i, u, sr, g, i))], 'eqcomd',
            '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( ( %s x. %s ) x. %s ) x. %s )'
            % (u, sr, g, i, u, sr, g, i))
    r3 = sd([sd([usc, gc], 'mulcomd',
                '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (u, sr, g, g, u, sr))],
            'oveq1d', '( ( ( %s x. %s ) x. %s ) x. %s ) = ( ( %s x. ( %s x. %s ) ) x. %s )'
            % (u, sr, g, i, g, u, sr, i))
    rhsv = sd([sd([r1, r2], 'eqtrd',
                  '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( ( %s x. %s ) x. %s ) x. %s )'
                  % (sr, u, g, i, u, sr, g, i)), r3], 'eqtrd',
              '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. ( %s x. %s ) ) x. %s )'
              % (sr, u, g, i, g, u, sr, i))
    lhsv = sd([sd([sd([], 'iftrued', '%s = ( %s x. %s )' % (LW('D'), FAC('D'), i))], 'oveq2d',
                  '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (a, LW('D'), a, X, i)), e5], 'eqtrd',
              '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) x. %s )' % (a, LW('D'), g, u, sr, i))
    rhsv2 = sd([sd([lsum], 'oveq2d',
                   '%s = ( ( %s x. %s ) x. ( %s x. %s ) )' % (RHS, sr, u, g, i)), rhsv], 'eqtrd',
               '%s = ( ( %s x. ( %s x. %s ) ) x. %s )' % (RHS, g, u, sr, i))
    case1 = sd([lhsv, rhsv2], 'eqtr4d', '( %s x. %s ) = %s' % (a, LW('D'), RHS))
    # ---------- case -. D || P
    ADF = '( %s /\ -. D || P )' % A
    sf = mkst(w, ADF)
    lhs0 = sf([sf([sf([], 'iffalsed', '%s = 0' % LW('D'))], 'oveq2d',
                  '( %s x. %s ) = ( %s x. 0 )' % (a, LW('D'), a)),
               sf([sf([vdc], 'adantr', '%s e. CC' % a)], 'mul01d', '( %s x. 0 ) = 0' % a)],
              'eqtrd', '( %s x. %s ) = 0' % (a, LW('D')))
    AL = '( %s /\ l e. %s )' % (ADF, DVP)
    sl = mkst(w, AL)
    lc = sl([sl([ell], 'a1i', '( l e. %s <-> ( l e. NN /\ l || P ) )' % DVP),
             sl([], 'simpr', 'l e. %s' % DVP)], 'mpbid', '( l e. NN /\ l || P )')
    ALD = '( %s /\ D || l )' % AL
    sld = mkst(w, ALD)
    ddp3 = sld([sld([sld([sld([sl([sf([dz], 'adantr', 'D e. ZZ')], 'adantr', 'D e. ZZ')],
                              'adantr', 'D e. ZZ'),
                          sld([sld([sl([lc], 'simpld', 'l e. NN')], 'adantr', 'l e. NN')],
                              'nnzd', 'l e. ZZ'),
                          sld([sl([sf([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ')],
                              'adantr', 'P e. ZZ')], '3jca',
                         '( D e. ZZ /\ l e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                    '( ( D || l /\ l || P ) -> D || P )'),
                sld([sld([], 'simpr', 'D || l'),
                     sld([sl([lc], 'simprd', 'l || P')], 'adantr', 'l || P')], 'jca',
                    '( D || l /\ l || P )')], 'mpd', 'D || P')
    nodl = sl([sl([sf([], 'simpr', '-. D || P')], 'adantr', '-. D || P'), ddp3], 'mtand',
              '-. D || l')
    zerol = sl([sl([nodl], 'intnanrd', '-. ( D || l /\ ( l ^ 2 ) <_ Y )')], 'iffalsed',
               '%s = 0' % LTERM)
    sumz0 = sf([sf([zerol], 'sumeq2dv', '%s = sum_ l e. %s 0' % (SL, DVP)),
                sf([sf([sf([finP], 'adantr', '%s e. Fin' % DVP)], 'olcd',
                       '( %s C_ ( ZZ>= ` 1 ) \/ %s e. Fin )' % (DVP, DVP)),
                    w.inst('sumz')], 'syl', 'sum_ l e. %s 0 = 0' % DVP)], 'eqtrd', '%s = 0' % SL)
    rhs0 = sf([sf([sumz0], 'oveq2d',
                  '%s = ( ( %s x. %s ) x. 0 )' % (RHS, sr, u)),
               sf([sf([sf([ssc], 'adantr', '%s e. CC' % sr),
                       sf([muc], 'adantr', '%s e. CC' % u)], 'mulcld',
                      '( %s x. %s ) e. CC' % (sr, u))], 'mul01d',
                  '( ( %s x. %s ) x. 0 ) = 0' % (sr, u))], 'eqtrd', '%s = 0' % RHS)
    case2 = sf([lhs0, sf([rhs0], 'eqcomd', '0 = %s' % RHS)], 'eqtrd',
               '( %s x. %s ) = %s' % (a, LW('D'), RHS))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> ( %s x. %s ) = %s )' % (A, a, LW('D'), RHS))
    return w


def muinvdvds2():
    w = W('muinvdvds2', 'The truncated Moebius sum over the divisors of the sifting product that '
                        'are multiples of L and divisors of M detects L = M.')
    A = ('( ( P e. NN /\ ( mmu ` P ) =/= 0 ) /\ ( M e. NN /\ M || P ) /\ L e. NN )')
    DVP = DV('P')
    DVM = DV('M')
    TP = 'if ( ( L || d /\ d || M ) , ( mmu ` d ) , 0 )'
    TM = 'if ( L || d , ( mmu ` d ) , 0 )'
    st = mkst(w, A)
    pnn = st([], 'simp1l', 'P e. NN')
    psq = st([], 'simp1r', '( mmu ` P ) =/= 0')
    mnn = st([], 'simp2l', 'M e. NN')
    mdp = st([], 'simp2r', 'M || P')
    lnn = st([], 'simp3', 'L e. NN')
    pz = st([pnn], 'nnzd', 'P e. ZZ')
    mz = st([mnn], 'nnzd', 'M e. ZZ')
    msq = st([st([st([pnn, mnn, mdp], '3jca', '( P e. NN /\ M e. NN /\ M || P )'),
                  w.inst('dvdssqf')], 'syl',
                 '( ( mmu ` P ) =/= 0 -> ( mmu ` M ) =/= 0 )'), psq], 'mpd',
             '( mmu ` M ) =/= 0')
    finP = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    # DV ( M ) C_ DV ( P )
    AX = '( %s /\ x e. NN )' % A
    sx = mkst(w, AX)
    AXM = '( %s /\ x || M )' % AX
    sxm = mkst(w, AXM)
    xdp = sxm([sxm([sxm([sxm([w.s([], 'simplr', '( %s -> x e. NN )' % AXM)], 'nnzd', 'x e. ZZ'),
                         sxm([sx([mz], 'adantr', 'M e. ZZ')], 'adantr', 'M e. ZZ'),
                         sxm([sx([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ')], '3jca',
                        '( x e. ZZ /\ M e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                   '( ( x || M /\ M || P ) -> x || P )'),
               sxm([sxm([], 'simpr', 'x || M'),
                    sxm([sx([mdp], 'adantr', 'M || P')], 'adantr', 'M || P')], 'jca',
                   '( x || M /\ M || P )')], 'mpd', 'x || P')
    sub = st([sx([xdp], 'ex', '( x || M -> x || P )')], 'ss2rabdv', '%s C_ %s' % (DVM, DVP))

    def eld(S, X):
        return w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (X, X))], 'elrab',
                   '( d e. %s <-> ( d e. NN /\ d || %s ) )' % (S, X))

    eldM = eld(DVM, 'M')
    eldP = eld(DVP, 'P')
    # on DV ( M ) the second condition holds
    AM = '( %s /\ d e. %s )' % (A, DVM)
    sm = mkst(w, AM)
    dcM = sm([sm([eldM], 'a1i', '( d e. %s <-> ( d e. NN /\ d || M ) )' % DVM),
              sm([], 'simpr', 'd e. %s' % DVM)], 'mpbid', '( d e. NN /\ d || M )')
    ifM = sm([sm([sm([dcM], 'simprd', 'd || M')], 'biantrud',
                 '( L || d <-> ( L || d /\ d || M ) )')], 'ifbid', '%s = %s' % (TM, TP))
    sumM = st([ifM], 'sumeq2dv',
              'sum_ d e. %s %s = sum_ d e. %s %s' % (DVM, TM, DVM, TP))
    ccM = sm([sm([sm([sm([dcM], 'simpld', 'd e. NN'), w.inst('mucl')], 'syl',
                     '( mmu ` d ) e. ZZ')], 'zcnd', '( mmu ` d ) e. CC'),
              w.s([], '0cnd', '( %s -> 0 e. CC )' % AM)], 'ifcld', '%s e. CC' % TP)
    # off DV ( M ) the second condition fails
    ADF = '( %s /\ d e. ( %s \ %s ) )' % (A, DVP, DVM)
    sdf = mkst(w, ADF)
    ddif = w.s([], 'simpr', '( %s -> d e. ( %s \ %s ) )' % (ADF, DVP, DVM))
    dinP = sdf([ddif, w.inst('eldifi')], 'syl', 'd e. %s' % DVP)
    dnotM = sdf([ddif, w.inst('eldifn')], 'syl', '-. d e. %s' % DVM)
    dnnP = sdf([sdf([sdf([eldP], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP), dinP],
                    'mpbid', '( d e. NN /\ d || P )')], 'simpld', 'd e. NN')
    ADM = '( %s /\ d || M )' % ADF
    sdm = mkst(w, ADM)
    inM = sdm([sdm([eldM], 'a1i', '( d e. %s <-> ( d e. NN /\ d || M ) )' % DVM),
               sdm([sdm([dnnP], 'adantr', 'd e. NN'), sdm([], 'simpr', 'd || M')], 'jca',
                   '( d e. NN /\ d || M )')], 'mpbird', 'd e. %s' % DVM)
    ndM = sdf([dnotM, inM], 'mtand', '-. d || M')
    zero = sdf([sdf([ndM], 'intnand', '-. ( L || d /\ d || M )')], 'iffalsed', '%s = 0' % TP)
    ext = st([sub, ccM, zero, finP], 'fsumss',
             'sum_ d e. %s %s = sum_ d e. %s %s' % (DVM, TP, DVP, TP))
    inv = st([st([mnn, msq, lnn], '3jca',
                 '( M e. NN /\ ( mmu ` M ) =/= 0 /\ L e. NN )'), w.inst('muinvdvds')], 'syl',
             'sum_ d e. %s %s = if ( L = M , ( mmu ` L ) , 0 )' % (DVM, TM))
    w.qed([st([st([ext], 'eqcomd',
                  'sum_ d e. %s %s = sum_ d e. %s %s' % (DVP, TP, DVM, TP)),
               st([sumM], 'eqcomd',
                  'sum_ d e. %s %s = sum_ d e. %s %s' % (DVM, TP, DVM, TM))], 'eqtrd',
              'sum_ d e. %s %s = sum_ d e. %s %s' % (DVP, TP, DVM, TM)), inv], 'eqtrd',
          '( %s -> sum_ d e. %s %s = if ( L = M , ( mmu ` L ) , 0 ) )' % (A, DVP, TP))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['vrecrp']:
        globals()[f]().run()
