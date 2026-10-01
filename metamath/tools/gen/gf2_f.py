"""Sortie GF2, section F: termwise integration of power series along segments, the exponential Fubini
exchange, and the quantitative Mellin representation of the averaged window (Lean
intervalIntegral_integral_swap, avg_window_eq_integral, Wwin_eq_integral).
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_f.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
from mvlib import ringeq, ringeqp

S_ = L.S
EXT = lambda X, m: '( ( %s ^ ( %s - 1 ) ) / ( ! ` ( %s - 1 ) ) )' % (X, m, m)
EXF = lambda X: '( m e. NN |-> %s )' % EXT(X, 'm')
S_['gf2exps'] = '( X e. CC -> seq 1 ( + , %s ) ~~> ( exp ` X ) )' % EXF('X')


def gf2exps():
    w = W('gf2exps', 'The exponential series indexed from 1: ` sum_ ( m >_ 1 ) X ^ ( m - 1 ) / ( m - 1 ) ! = e ^ X ` (~ efcvg , ~ isershft , ~ seqfeq ).')
    a = 'X e. CC'
    st = mkst(w, a)
    E = '( n e. NN0 |-> ( ( X ^ n ) / ( ! ` n ) ) )'
    ef = w.s([w.s([], 'eqid', '%s = %s' % (E, E))], 'efcvg', '( X e. CC -> seq 0 ( + , %s ) ~~> ( exp ` X ) )' % E)
    ev = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % E)
    sh = w.s([ev], 'isershft', '( ( 0 e. ZZ /\\ 1 e. ZZ ) -> ( seq 0 ( + , %s ) ~~> ( exp ` X ) <-> seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) ~~> ( exp ` X ) ) )' % (E, E))
    sh2 = w.s([w.s([], '0z', '0 e. ZZ'), w.s([], '1z', '1 e. ZZ'), sh], 'mp2an',
              '( seq 0 ( + , %s ) ~~> ( exp ` X ) <-> seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) ~~> ( exp ` X ) )' % (E, E))
    c1 = st([ef, a1(w, a, sh2, '( seq 0 ( + , %s ) ~~> ( exp ` X ) <-> seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) ~~> ( exp ` X ) )' % (E, E))], 'mpbid',
            'seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) ~~> ( exp ` X )' % E)
    s01 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1'), w.inst('seqeq1')], 'ax-mp', 'seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) = seq 1 ( + , ( %s shift 1 ) )' % (E, E))
    c2 = st([c1, st([a1(w, a, s01, 'seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) = seq 1 ( + , ( %s shift 1 ) )' % (E, E))], 'breq1d',
                    '( seq ( 0 + 1 ) ( + , ( %s shift 1 ) ) ~~> ( exp ` X ) <-> seq 1 ( + , ( %s shift 1 ) ) ~~> ( exp ` X ) )' % (E, E))], 'mpbid',
            'seq 1 ( + , ( %s shift 1 ) ) ~~> ( exp ` X )' % E)
    ak = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    sk = mkst(w, ak)
    kn = sk([sk([], 'simpr', 'k e. ( ZZ>= ` 1 )'), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr', 'k e. NN')
    kc = sk([kn], 'nncnd', 'k e. CC')
    sv = sk([sk([], '1cnd', '1 e. CC'), kc, w.s([ev], 'shftval', '( ( 1 e. CC /\\ k e. CC ) -> ( ( %s shift 1 ) ` k ) = ( %s ` ( k - 1 ) ) )' % (E, E))], 'syl2anc',
            '( ( %s shift 1 ) ` k ) = ( %s ` ( k - 1 ) )' % (E, E))
    km1 = sk([kn, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0')
    v1, _ = mpv(w, ak, 'n', 'NN0', '( ( X ^ n ) / ( ! ` n ) )', '( k - 1 )', km1)
    v2, _ = mpv(w, ak, 'm', 'NN', EXT('X', 'm'), 'k', kn)
    e = sk([sk([sv, v1], 'eqtrd', '( ( %s shift 1 ) ` k ) = %s' % (E, EXT('X', 'k'))), v2], 'eqtr4d', '( ( %s shift 1 ) ` k ) = ( %s ` k )' % (E, EXF('X')))
    sq = st([a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), e], 'seqfeq', 'seq 1 ( + , ( %s shift 1 ) ) = seq 1 ( + , %s )' % (E, EXF('X')))
    fin = st([c2, st([sq], 'breq1d', '( seq 1 ( + , ( %s shift 1 ) ) ~~> ( exp ` X ) <-> seq 1 ( + , %s ) ~~> ( exp ` X ) )' % (E, EXF('X')))], 'mpbid', S_['gf2exps'].split(' -> ', 1)[1][:-2])
    w.qed([fin], 'idi', S_['gf2exps'])
    return w


def fvd(w, ante, x, D, body, A, mem, exs):
    """( ante -> ( ( x e. D |-> body ) ` A ) = body[A/x] ) by fvmptd (no proof dummy y); the value from the congruence (binder-aware)"""
    mp = '( %s e. %s |-> %s )' % (x, D, body)
    idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, A, x, A))
    cst, val = w.congr(body, {x: A}, '%s = %s' % (x, A), {x: idx})
    if cst is None:
        cst = w.s([], 'eqidd', '( %s = %s -> %s = %s )' % (x, A, body, val))
    sub = w.s([cst], 'adantl', '( ( %s /\\ %s = %s ) -> %s = %s )' % (ante, x, A, body, val))
    return w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, mp, mp)), sub, mem, exs], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, A, val))


from z6a_e3 import unpack
CNU = '( U -cn-> CC )'
TPH = ('( ( ( ( A e. CC /\\ B e. CC ) /\\ ( A cseg B ) C_ U ) /\\ ( G e. %s /\\ ( H e. RR /\\ A. v e. U ( abs ` ( G ` v ) ) <_ H ) ) /\\ '
       '( R e. RR /\\ A. v e. U ( abs ` v ) <_ R ) ) /\\ ( Q : NN --> CC /\\ ( ( K e. RR /\\ 0 <_ K ) /\\ ( C e. RR /\\ 0 <_ C ) ) /\\ '
       'A. i e. NN ( abs ` ( Q ` i ) ) <_ ( K x. %s ) ) )') % (CNU, EXT('C', 'i'))
FTB = lambda m, x: '( ( G ` %s ) x. ( ( Q ` %s ) x. ( %s ^ ( %s - 1 ) ) ) )' % (x, m, x, m)
FT = '( m e. NN |-> ( x e. U |-> %s ) )' % FTB('m', 'x')
SF = '( r e. U |-> sum_ k e. NN ( ( %s ` k ) ` r ) )' % FT
SFZ = '( z e. U |-> sum_ k e. NN ( ( %s ` k ) ` z ) )' % FT
GP = lambda k: '( h e. U |-> ( ( G ` h ) x. ( h ^ ( %s - 1 ) ) ) )' % k
LIG = lambda k: '( %s lint <. A , B >. )' % GP(k)
S_['gf2tps'] = '( %s -> ( %s e. %s /\\ seq 1 ( + , ( k e. NN |-> ( ( Q ` k ) x. %s ) ) ) ~~> ( %s lint <. A , B >. ) ) )' % (TPH, SF, CNU, LIG('k'), SF)


def gf2tps():
    w = W('gf2tps', 'Termwise integration of a power series with a factorial majorant along a segment: for ` | Q ( m ) | <_ K C ^ ( m - 1 ) / ( m - 1 ) ! ` , '
                    '` sum_m Q ( m ) int G ( x ) x ^ ( m - 1 ) ` converges to ` int G ( x ) sum_m Q ( m ) x ^ ( m - 1 ) ` , and the sum is continuous (~ z6lsum , ~ uhlim , ~ ulmcn ).')
    a = TPH
    f = unpack(w, a); st = mkst(w, a)
    ac = f['A e. CC']; bc = f['B e. CC']; sgu = f['( A cseg B ) C_ U']; gcn = f['G e. %s' % CNU]
    hr = f['H e. RR']; gb = f['A. v e. U ( abs ` ( G ` v ) ) <_ H']; rr = f['R e. RR']; rb = f['A. v e. U ( abs ` v ) <_ R']
    qf = f['Q : NN --> CC']; kr = f['K e. RR']; k0 = f['0 <_ K']; cr = f['C e. RR']; c0 = f['0 <_ C']
    qb = f['A. i e. NN ( abs ` ( Q ` i ) ) <_ ( K x. %s )' % EXT('C', 'i')]
    ucc = st([gcn, w.inst('cncfrss')], 'syl', 'U C_ CC')
    gff = st([gcn, w.inst('cncff')], 'syl', 'G : U --> CC')
    geq = st([gff], 'feqmptd', 'G = ( x e. U |-> ( G ` x ) )')
    gm = st([gcn, st([geq], 'eleq1d', '( G e. %s <-> ( x e. U |-> ( G ` x ) ) e. %s )' % (CNU, CNU))], 'mpbid', '( x e. U |-> ( G ` x ) ) e. %s' % CNU)
    idc = st([ucc, a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( x e. U |-> x ) e. %s' % CNU)
    idch = st([ucc, a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( h e. U |-> h ) e. %s' % CNU)
    geqh = st([gff], 'feqmptd', 'G = ( h e. U |-> ( G ` h ) )')
    gmh = st([gcn, st([geqh], 'eleq1d', '( G e. %s <-> ( h e. U |-> ( G ` h ) ) e. %s )' % (CNU, CNU))], 'mpbid', '( h e. U |-> ( G ` h ) ) e. %s' % CNU)
    # ---- the terms
    am = '( %s /\\ m e. NN )' % a
    sm = mkst(w, am)
    mn = sm([], 'simpr', 'm e. NN')
    m1 = sm([mn, w.inst('nnm1nn0')], 'syl', '( m - 1 ) e. NN0')
    pw = sm([lift(w, idc, am), m1, w.inst('cncfexpb')], 'syl2anc', '( x e. U |-> ( x ^ ( m - 1 ) ) ) e. %s' % CNU)
    qc = sm([lift(w, qf, am), mn], 'ffvelcdmd', '( Q ` m ) e. CC')
    qcn = sm([qc, lift(w, ucc, am), a1(w, am, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( x e. U |-> ( Q ` m ) ) e. %s' % CNU)
    qx = sm([qcn, pw], 'mulcncf', '( x e. U |-> ( ( Q ` m ) x. ( x ^ ( m - 1 ) ) ) ) e. %s' % CNU)
    ftm = sm([lift(w, gm, am), qx], 'mulcncf', '( x e. U |-> %s ) e. %s' % (FTB('m', 'x'), CNU))
    ftf = st([ftm], 'fmptd', '%s : NN --> %s' % (FT, CNU))
    # ---- the majorant
    CR = '( C x. R )'
    MSB = lambda m: '( ( H x. K ) x. %s )' % EXT(CR, m)
    MS = '( m e. NN |-> %s )' % MSB('m')
    crr = st([cr, rr], 'remulcld', '%s e. RR' % CR)
    hk = st([hr, kr], 'remulcld', '( H x. K ) e. RR')
    fac = sm([m1, w.inst('faccl')], 'syl', '( ! ` ( m - 1 ) ) e. NN')
    extr = sm([sm([lift(w, crr, am), m1], 'reexpcld', '( %s ^ ( m - 1 ) ) e. RR' % CR), sm([fac], 'nnred', '( ! ` ( m - 1 ) ) e. RR'), sm([fac], 'nnne0d', '( ! ` ( m - 1 ) ) =/= 0')],
              'redivcld', '%s e. RR' % EXT(CR, 'm'))
    msf = st([sm([lift(w, hk, am), extr], 'remulcld', '%s e. RR' % MSB('m'))], 'fmptd', '%s : NN --> RR' % MS)
    ex = st([st([crr], 'recnd', '%s e. CC' % CR), w.inst('gf2exps')], 'syl', 'seq 1 ( + , %s ) ~~> ( exp ` %s )' % (EXF(CR), CR))
    ak = '( %s /\\ k e. NN )' % a
    sk = mkst(w, ak)
    kn = sk([], 'simpr', 'k e. NN')
    ek1, _ = mpv(w, ak, 'm', 'NN', EXT(CR, 'm'), 'k', kn)
    ek2, _ = mpv(w, ak, 'm', 'NN', MSB('m'), 'k', kn)
    kfac = sk([sk([kn, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0'), w.inst('faccl')], 'syl', '( ! ` ( k - 1 ) ) e. NN')
    ekc = sk([sk([sk([lift(w, crr, ak)], 'recnd', '%s e. CC' % CR), sk([kn, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0')], 'expcld', '( %s ^ ( k - 1 ) ) e. CC' % CR),
              sk([kfac], 'nncnd', '( ! ` ( k - 1 ) ) e. CC'), sk([kfac], 'nnne0d', '( ! ` ( k - 1 ) ) =/= 0')], 'divcld', '%s e. CC' % EXT(CR, 'k'))
    ekc2 = sk([ek1, ekc], 'eqeltrd', '( %s ` k ) e. CC' % EXF(CR))
    ekm = sk([ek2, sk([ek1], 'oveq2d', '( ( H x. K ) x. ( %s ` k ) ) = %s' % (EXF(CR), MSB('k')))], 'eqtr4d', '( %s ` k ) = ( ( H x. K ) x. ( %s ` k ) )' % (MS, EXF(CR)))
    msl = st([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), st([hk], 'recnd', '( H x. K ) e. CC'), ex, ekc2, ekm], 'isermulc2',
             'seq 1 ( + , %s ) ~~> ( ( H x. K ) x. ( exp ` %s ) )' % (MS, CR))
    mcv = w.s([w.s([], 'climrel', 'Rel ~~>'), msl, w.inst('releldm')], 'sylancr', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (a, MS))
    # ---- the bound
    ajy = '( %s /\\ ( j e. NN /\\ y e. U ) )' % a
    sj = mkst(w, ajy)
    jn = sj([], 'simprl', 'j e. NN'); yu = sj([], 'simprr', 'y e. U')
    FJ = '( x e. U |-> %s )' % FTB('j', 'x')
    uv = st([a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), ucc], 'ssexd', 'U e. _V')
    fj1, _ = mpv(w, ajy, 'm', 'NN', '( x e. U |-> %s )' % FTB('m', 'x'), 'j', jn, exs=sj([lift(w, uv, ajy)], 'mptexd', '%s e. _V' % FJ))
    fj2 = fvd(w, ajy, 'x', 'U', FTB('j', 'x'), 'y', yu, sj([], 'ovexd', '%s e. _V' % FTB('j', 'y')))
    fjv = sj([sj([fj1], 'fveq1d', '( ( %s ` j ) ` y ) = ( %s ` y )' % (FT, FJ)), fj2], 'eqtrd', '( ( %s ` j ) ` y ) = %s' % (FT, FTB('j', 'y')))
    yc = sj([lift(w, ucc, ajy), yu], 'sseldd', 'y e. CC')
    j1 = sj([jn, w.inst('nnm1nn0')], 'syl', '( j - 1 ) e. NN0')
    gy = sj([lift(w, gff, ajy), yu], 'ffvelcdmd', '( G ` y ) e. CC')
    qj = sj([lift(w, qf, ajy), jn], 'ffvelcdmd', '( Q ` j ) e. CC')
    yp = sj([yc, j1], 'expcld', '( y ^ ( j - 1 ) ) e. CC')
    ab1 = sj([gy, sj([qj, yp], 'mulcld', '( ( Q ` j ) x. ( y ^ ( j - 1 ) ) ) e. CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` ( G ` y ) ) x. ( abs ` ( ( Q ` j ) x. ( y ^ ( j - 1 ) ) ) ) )' % FTB('j', 'y'))
    ab2 = sj([qj, yp], 'absmuld', '( abs ` ( ( Q ` j ) x. ( y ^ ( j - 1 ) ) ) ) = ( ( abs ` ( Q ` j ) ) x. ( abs ` ( y ^ ( j - 1 ) ) ) )')
    ab3 = sj([yc, j1], 'absexpd', '( abs ` ( y ^ ( j - 1 ) ) ) = ( ( abs ` y ) ^ ( j - 1 ) )')
    AGY = '( abs ` ( G ` y ) )'; AQJ = '( abs ` ( Q ` j ) )'; AYP = '( ( abs ` y ) ^ ( j - 1 ) )'
    RHS1 = '( %s x. ( %s x. %s ) )' % (AGY, AQJ, AYP)
    abv = sj([ab1, sj([sj([ab2, sj([ab3], 'oveq2d', '( %s x. ( abs ` ( y ^ ( j - 1 ) ) ) ) = ( %s x. %s )' % (AQJ, AQJ, AYP))], 'eqtrd',
                          '( abs ` ( ( Q ` j ) x. ( y ^ ( j - 1 ) ) ) ) = ( %s x. %s )' % (AQJ, AYP))], 'oveq2d',
                     '( %s x. ( abs ` ( ( Q ` j ) x. ( y ^ ( j - 1 ) ) ) ) ) = %s' % (AGY, RHS1))], 'eqtrd', '( abs ` %s ) = %s' % (FTB('j', 'y'), RHS1))
    def spec(al, P, v, t):
        idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, t, v, t))
        sb, _ = w.wcongr(P(v), {v: t}, '%s = %s' % (v, t), {v: idx})
        return sb
    gyb = sj([spec(gb, lambda v: '( abs ` ( G ` %s ) ) <_ H' % v, 'v', 'y'), lift(w, gb, ajy), yu], 'rspcdva', '%s <_ H' % AGY)
    yb = sj([spec(rb, lambda v: '( abs ` %s ) <_ R' % v, 'v', 'y'), lift(w, rb, ajy), yu], 'rspcdva', '( abs ` y ) <_ R')
    qjb = sj([spec(qb, lambda i: '( abs ` ( Q ` %s ) ) <_ ( K x. %s )' % (i, EXT('C', i)), 'i', 'j'), lift(w, qb, ajy), jn], 'rspcdva', '%s <_ ( K x. %s )' % (AQJ, EXT('C', 'j')))
    ayr = sj([yc], 'abscld', '( abs ` y ) e. RR'); ay0 = sj([yc], 'absge0d', '0 <_ ( abs ` y )')
    RJ = '( R ^ ( j - 1 ) )'
    ypb = sj([sj([ayr, lift(w, rr, ajy), j1], '3jca', '( ( abs ` y ) e. RR /\\ R e. RR /\\ ( j - 1 ) e. NN0 )'), sj([ay0, yb], 'jca', '( 0 <_ ( abs ` y ) /\\ ( abs ` y ) <_ R )'),
              w.inst('leexp1a')], 'syl2anc', '%s <_ %s' % (AYP, RJ))
    jfac = sj([j1, w.inst('faccl')], 'syl', '( ! ` ( j - 1 ) ) e. NN')
    extc = sj([sj([lift(w, cr, ajy), j1], 'reexpcld', '( C ^ ( j - 1 ) ) e. RR'), sj([jfac], 'nnred', '( ! ` ( j - 1 ) ) e. RR'), sj([jfac], 'nnne0d', '( ! ` ( j - 1 ) ) =/= 0')],
              'redivcld', '%s e. RR' % EXT('C', 'j'))
    kext = sj([lift(w, kr, ajy), extc], 'remulcld', '( K x. %s ) e. RR' % EXT('C', 'j'))
    aqr = sj([qj], 'abscld', '%s e. RR' % AQJ); aq0 = sj([qj], 'absge0d', '0 <_ %s' % AQJ)
    aypr = sj([ayr, j1], 'reexpcld', '%s e. RR' % AYP); ayp0 = sj([ayr, j1, ay0], 'expge0d', '0 <_ %s' % AYP)
    rjr = sj([lift(w, rr, ajy), j1], 'reexpcld', '%s e. RR' % RJ)
    b1 = sj([aqr, kext, aypr, rjr, aq0, ayp0, qjb, ypb], 'lemul12ad', '( %s x. %s ) <_ ( ( K x. %s ) x. %s )' % (AQJ, AYP, EXT('C', 'j'), RJ))
    agr = sj([gy], 'abscld', '%s e. RR' % AGY); ag0 = sj([gy], 'absge0d', '0 <_ %s' % AGY)
    b2 = sj([agr, lift(w, hr, ajy), sj([aqr, aypr], 'remulcld', '( %s x. %s ) e. RR' % (AQJ, AYP)), sj([sj([lift(w, kr, ajy), extc], 'remulcld', '( K x. %s ) e. RR' % EXT('C', 'j')), rjr],
                                                                                                     'remulcld', '( ( K x. %s ) x. %s ) e. RR' % (EXT('C', 'j'), RJ)),
             ag0, sj([aqr, aypr, aq0, ayp0], 'mulge0d', '0 <_ ( %s x. %s )' % (AQJ, AYP)), gyb, b1], 'lemul12ad',
            '%s <_ ( H x. ( ( K x. %s ) x. %s ) )' % (RHS1, EXT('C', 'j'), RJ))
    # H ( K C^(j-1) / (j-1)! ) R^(j-1) = ( H K ) ( C R )^(j-1) / (j-1)!
    FJ_ = '( ! ` ( j - 1 ) )'
    IF_ = '( 1 / %s )' % FJ_
    fjc = sj([jfac], 'nncnd', '%s e. CC' % FJ_); fjn = sj([jfac], 'nnne0d', '%s =/= 0' % FJ_)
    CJ = '( C ^ ( j - 1 ) )'; CRJ = '( %s ^ ( j - 1 ) )' % CR
    d1 = sj([sj([sj([lift(w, cr, ajy)], 'recnd', 'C e. CC'), j1], 'expcld', '%s e. CC' % CJ), fjc, fjn], 'divrecd', '%s = ( %s x. %s )' % (EXT('C', 'j'), CJ, IF_))
    crc = sj([lift(w, crr, ajy)], 'recnd', '%s e. CC' % CR)
    d2 = sj([sj([crc, j1], 'expcld', '%s e. CC' % CRJ), fjc, fjn], 'divrecd', '%s = ( %s x. %s )' % (EXT(CR, 'j'), CRJ, IF_))
    me = sj([sj([lift(w, cr, ajy)], 'recnd', 'C e. CC'), sj([lift(w, rr, ajy)], 'recnd', 'R e. CC'), j1], 'mulexpd', '%s = ( %s x. %s )' % (CRJ, CJ, RJ))
    ifr = sj([sj([jfac], 'nnrecred', '%s e. RR' % IF_)], 'recnd', '%s e. CC' % IF_)
    cl = Closure(w, ajy, {'H': lift(w, hr, ajy), 'K': lift(w, kr, ajy), CJ: sj([lift(w, cr, ajy), j1], 'reexpcld', '%s e. RR' % CJ), RJ: rjr, IF_: sj([jfac], 'nnrecred', '%s e. RR' % IF_)})
    LHSb = '( H x. ( ( K x. ( %s x. %s ) ) x. %s ) )' % (CJ, IF_, RJ)
    RHSb = '( ( H x. K ) x. ( ( %s x. %s ) x. %s ) )' % (CJ, RJ, IF_)
    rq = ringeq(w, ajy, LHSb, RHSb, cl)
    e1 = sj([sj([sj([d1], 'oveq2d', '( K x. %s ) = ( K x. ( %s x. %s ) )' % (EXT('C', 'j'), CJ, IF_))], 'oveq1d',
                '( ( K x. %s ) x. %s ) = ( ( K x. ( %s x. %s ) ) x. %s )' % (EXT('C', 'j'), RJ, CJ, IF_, RJ))], 'oveq2d',
            '( H x. ( ( K x. %s ) x. %s ) ) = %s' % (EXT('C', 'j'), RJ, LHSb))
    e2 = sj([sj([sj([d2, sj([me], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (CRJ, IF_, CJ, RJ, IF_))], 'eqtrd', '%s = ( ( %s x. %s ) x. %s )' % (EXT(CR, 'j'), CJ, RJ, IF_))],
                'oveq2d', '%s = %s' % (MSB('j'), RHSb))], 'eqcomd', '%s = %s' % (RHSb, MSB('j')))
    mjv, _ = mpv(w, ajy, 'm', 'NN', MSB('m'), 'j', jn)
    eqm = sj([sj([sj([e1, rq], 'eqtrd', '( H x. ( ( K x. %s ) x. %s ) ) = %s' % (EXT('C', 'j'), RJ, RHSb)), e2], 'eqtrd', '( H x. ( ( K x. %s ) x. %s ) ) = %s' % (EXT('C', 'j'), RJ, MSB('j'))),
              sj([mjv], 'eqcomd', '%s = ( %s ` j )' % (MSB('j'), MS))], 'eqtrd', '( H x. ( ( K x. %s ) x. %s ) ) = ( %s ` j )' % (EXT('C', 'j'), RJ, MS))
    bnd = sj([sj([sj([fjv], 'fveq2d', '( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s )' % (FT, FTB('j', 'y'))), abv], 'eqtrd', '( abs ` ( ( %s ` j ) ` y ) ) = %s' % (FT, RHS1)), b2], 'eqbrtrd',
             '( abs ` ( ( %s ` j ) ` y ) ) <_ ( H x. ( ( K x. %s ) x. %s ) )' % (FT, EXT('C', 'j'), RJ))
    bnd2 = sj([bnd, eqm], 'breqtrd', '( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (FT, MS))
    ral = st([bnd2], 'ralrimivva', 'A. j e. NN A. y e. U ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (FT, MS))
    MT = '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. U ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (MS, MS, FT, MS)
    mt = st([msf, mcv, ral], '3jca', MT)
    zl = st([st([ac, bc], 'jca', '( A e. CC /\\ B e. CC )'), st([sgu, st([ftf, mt], 'jca', '( %s : NN --> %s /\\ %s )' % (FT, CNU, MT))], 'jca',
                                                                '( ( A cseg B ) C_ U /\\ ( %s : NN --> %s /\\ %s ) )' % (FT, CNU, MT)), w.inst('z6lsum')], 'syl2anc',
            'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. A , B >. ) ) ) ~~> ( %s lint <. A , B >. )' % (FT, SFZ))
    zr = w.s([cg(w, 'sum_ k e. NN ( ( %s ` k ) ` z )' % FT, 'z', 'r')], 'cbvmptv', '%s = %s' % (SFZ, SF))
    zra = a1(w, a, zr, '%s = %s' % (SFZ, SF))
    zl = st([zl, st([zra], 'oveq1d', '( %s lint <. A , B >. ) = ( %s lint <. A , B >. )' % (SFZ, SF))], 'breqtrd',
            'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. A , B >. ) ) ) ~~> ( %s lint <. A , B >. )' % (FT, SF))
    # ---- ( F ` k ) lint = Q ( k ) LIG ( k )
    FK = '( x e. U |-> %s )' % FTB('k', 'x')
    fk1, _ = mpv(w, ak, 'm', 'NN', '( x e. U |-> %s )' % FTB('m', 'x'), 'k', kn, exs=sk([lift(w, uv, ak)], 'mptexd', '%s e. _V' % FK))
    fkc = sk([lift(w, ftf, ak), kn], 'ffvelcdmd', '( %s ` k ) e. %s' % (FT, CNU))
    k1 = sk([kn, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0')
    pwk = sk([lift(w, idch, ak), k1, w.inst('cncfexpb')], 'syl2anc', '( h e. U |-> ( h ^ ( k - 1 ) ) ) e. %s' % CNU)
    gpk = sk([lift(w, gmh, ak), pwk], 'mulcncf', '%s e. %s' % (GP('k'), CNU))
    qk = sk([lift(w, qf, ak), kn], 'ffvelcdmd', '( Q ` k ) e. CC')
    akz = '( %s /\\ z e. ( A cseg B ) )' % ak
    sz = mkst(w, akz)
    zu = sz([lift(w, sgu, akz), sz([], 'simpr', 'z e. ( A cseg B )')], 'sseldd', 'z e. U')
    fz1 = sz([lift(w, fk1, akz)], 'fveq1d', '( ( %s ` k ) ` z ) = ( %s ` z )' % (FT, FK))
    fz2, _ = mpv(w, akz, 'x', 'U', FTB('k', 'x'), 'z', zu)
    gz, _ = mpv(w, akz, 'h', 'U', '( ( G ` h ) x. ( h ^ ( k - 1 ) ) )', 'z', zu)
    zc = sz([lift(w, ucc, akz), zu], 'sseldd', 'z e. CC')
    gzc = sz([lift(w, gff, akz), zu], 'ffvelcdmd', '( G ` z ) e. CC')
    m12 = sz([gzc, lift(w, qk, akz), sz([zc, lift(w, k1, akz)], 'expcld', '( z ^ ( k - 1 ) ) e. CC')], 'mul12d',
             '%s = ( ( Q ` k ) x. ( ( G ` z ) x. ( z ^ ( k - 1 ) ) ) )' % FTB('k', 'z'))
    idz = sz([sz([sz([fz1, fz2], 'eqtrd', '( ( %s ` k ) ` z ) = %s' % (FT, FTB('k', 'z'))), m12], 'eqtrd', '( ( %s ` k ) ` z ) = ( ( Q ` k ) x. ( ( G ` z ) x. ( z ^ ( k - 1 ) ) ) )' % FT),
              sz([gz], 'oveq2d', '( ( Q ` k ) x. ( %s ` z ) ) = ( ( Q ` k ) x. ( ( G ` z ) x. ( z ^ ( k - 1 ) ) ) )' % GP('k'))], 'eqtr4d',
             '( ( %s ` k ) ` z ) = ( ( Q ` k ) x. ( %s ` z ) )' % (FT, GP('k')))
    rz = sk([idz], 'ralrimiva', 'A. z e. ( A cseg B ) ( ( %s ` k ) ` z ) = ( ( Q ` k ) x. ( %s ` z ) )' % (FT, GP('k')))
    lm = sk([sk([sk([lift(w, ac, ak), lift(w, bc, ak)], 'jca', '( A e. CC /\\ B e. CC )'), sk([fkc, lift(w, sgu, ak)], 'jca', '( ( %s ` k ) e. %s /\\ ( A cseg B ) C_ U )' % (FT, CNU))],
                'jca', '( ( A e. CC /\\ B e. CC ) /\\ ( ( %s ` k ) e. %s /\\ ( A cseg B ) C_ U ) )' % (FT, CNU)),
             sk([gpk, qk], 'jca', '( %s e. %s /\\ ( Q ` k ) e. CC )' % (GP('k'), CNU)), rz, w.inst('lintmulc2')], 'syl3anc',
            '( ( %s ` k ) lint <. A , B >. ) = ( ( Q ` k ) x. %s )' % (FT, LIG('k')))
    LF1 = '( k e. NN |-> ( ( %s ` k ) lint <. A , B >. ) )' % FT
    LF2 = '( k e. NN |-> ( ( Q ` k ) x. %s ) )' % LIG('k')
    lq = st([lm], 'mpteq2dva', '%s = %s' % (LF1, LF2))
    conv = st([zl, st([st([lq], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (LF1, LF2))], 'breq1d',
                      '( seq 1 ( + , %s ) ~~> ( %s lint <. A , B >. ) <-> seq 1 ( + , %s ) ~~> ( %s lint <. A , B >. ) )' % (LF1, SF, LF2, SF))], 'mpbid',
              'seq 1 ( + , %s ) ~~> ( %s lint <. A , B >. )' % (LF2, SF))
    # ---- continuity of the sum (uhlim, ulmcn)
    MU = '( CC ^m U )'
    ag = '( %s /\\ g e. %s )' % (a, CNU); tg = mkst(w, ag)
    cnex = a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V')
    gmm = tg([tg([tg([], 'simpr', 'g e. %s' % CNU), w.inst('cncff')], 'syl', 'g : U --> CC'),
              tg([lift(w, cnex, ag), lift(w, uv, ag), w.inst('elmapg')], 'syl2anc', '( g e. %s <-> g : U --> CC )' % MU)], 'mpbird', 'g e. %s' % MU)
    css = st([w.s([gmm], 'ex', '( %s -> ( g e. %s -> g e. %s ) )' % (a, CNU, MU))], 'ssrdv', '%s C_ %s' % (CNU, MU))
    fm = st([ftf, css], 'fssd', '%s : NN --> %s' % (FT, MU))
    PS = 'seq 1 ( oF + , %s )' % FT
    ul = st([fm, mt, w.inst('uhlim')], 'syl2anc', '%s ( ~~>u ` U ) %s' % (PS, SFZ))
    an = '( %s /\\ n e. NN )' % a; tn = mkst(w, an)
    ps = tn([lift(w, ftf, an), tn([], 'simpr', 'n e. NN'), w.inst('z6lps')], 'syl2anc',
            '( ( %s ` n ) e. %s /\\ A. z e. U ( ( %s ` n ) ` z ) = sum_ i e. ( 1 ... n ) ( ( %s ` i ) ` z ) )' % (PS, CNU, PS, FT))
    psc = tn([ps], 'simpld', '( %s ` n ) e. %s' % (PS, CNU))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    fnn = st([st([a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), w.inst('seqfn')], 'syl', '%s Fn ( ZZ>= ` 1 )' % PS),
              a1(w, a, w.s([nnuz], 'fneq2i', '( %s Fn NN <-> %s Fn ( ZZ>= ` 1 ) )' % (PS, PS)), '( %s Fn NN <-> %s Fn ( ZZ>= ` 1 ) )' % (PS, PS))], 'mpbird', '%s Fn NN' % PS)
    psf = st([st([fnn, st([psc], 'ralrimiva', 'A. n e. NN ( %s ` n ) e. %s' % (PS, CNU))], 'jca', '( %s Fn NN /\\ A. n e. NN ( %s ` n ) e. %s )' % (PS, PS, CNU)),
              a1(w, a, w.s([], 'ffnfv', '( %s : NN --> %s <-> ( %s Fn NN /\\ A. n e. NN ( %s ` n ) e. %s ) )' % (PS, CNU, PS, PS, CNU)),
                 '( %s : NN --> %s <-> ( %s Fn NN /\\ A. n e. NN ( %s ` n ) e. %s ) )' % (PS, CNU, PS, PS, CNU))], 'mpbird', '%s : NN --> %s' % (PS, CNU))
    gcn1 = st([nnuz, a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), psf, ul], 'ulmcn', '%s e. %s' % (SFZ, CNU))
    gcn2 = st([gcn1, st([zra], 'eleq1d', '( %s e. %s <-> %s e. %s )' % (SFZ, CNU, SF, CNU))], 'mpbid', '%s e. %s' % (SF, CNU))
    w.qed([st([gcn2, conv], 'jca', split_imp(S_['gf2tps'])[1])], 'idi', S_['gf2tps'])
    return w
    return w


S_['gf2fe'] = '( ( W e. CC /\\ Z e. CC /\\ X e. CC ) -> sum_ k e. NN ( W x. ( %s x. ( Z ^ ( k - 1 ) ) ) ) = ( W x. ( exp ` ( Z x. X ) ) ) )' % EXT('X', 'k')


def gf2fe():
    w = W('gf2fe', 'The exponential series in the product form used by the termwise integrations: ` sum_k W ( X ^ ( k - 1 ) / ( k - 1 ) ! ) Z ^ ( k - 1 ) = W e ^ ( Z X ) ` (~ gf2exps , ~ isermulc2 , ~ isumclim ).')
    a = '( W e. CC /\\ Z e. CC /\\ X e. CC )'
    st = mkst(w, a)
    wc = st([], 'simp1', 'W e. CC'); zc = st([], 'simp2', 'Z e. CC'); xc = st([], 'simp3', 'X e. CC')
    ZX = '( Z x. X )'
    zx = st([zc, xc], 'mulcld', '%s e. CC' % ZX)
    ex = st([zx, w.inst('gf2exps')], 'syl', 'seq 1 ( + , %s ) ~~> ( exp ` %s )' % (EXF(ZX), ZX))
    ak = '( %s /\\ k e. NN )' % a
    sk = mkst(w, ak)
    kn = sk([], 'simpr', 'k e. NN')
    k1 = sk([kn, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0')
    fac = sk([k1, w.inst('faccl')], 'syl', '( ! ` ( k - 1 ) ) e. NN')
    FC = '( ! ` ( k - 1 ) )'; IF_ = '( 1 / %s )' % FC
    fcc = sk([fac], 'nncnd', '%s e. CC' % FC); fcn = sk([fac], 'nnne0d', '%s =/= 0' % FC)
    ev, _ = mpv(w, ak, 'm', 'NN', EXT(ZX, 'm'), 'k', kn)
    zxk = sk([lift(w, zx, ak), k1], 'expcld', '( %s ^ ( k - 1 ) ) e. CC' % ZX)
    extc = sk([zxk, fcc, fcn], 'divcld', '%s e. CC' % EXT(ZX, 'k'))
    efc = sk([ev, extc], 'eqeltrd', '( %s ` k ) e. CC' % EXF(ZX))
    # W ( X^(k-1) / F ) Z^(k-1) = W ( ( Z X )^(k-1) / F )
    XK = '( X ^ ( k - 1 ) )'; ZK = '( Z ^ ( k - 1 ) )'
    me = sk([lift(w, zc, ak), lift(w, xc, ak), k1], 'mulexpd', '( %s ^ ( k - 1 ) ) = ( %s x. %s )' % (ZX, ZK, XK))
    d1 = sk([sk([lift(w, xc, ak), k1], 'expcld', '%s e. CC' % XK), fcc, fcn], 'divrecd', '%s = ( %s x. %s )' % (EXT('X', 'k'), XK, IF_))
    d2 = sk([zxk, fcc, fcn], 'divrecd', '%s = ( ( %s ^ ( k - 1 ) ) x. %s )' % (EXT(ZX, 'k'), ZX, IF_))
    ifc = sk([fcc, fcn], 'reccld', '%s e. CC' % IF_)
    cl = Closure(w, ak, {'W': lift(w, wc, ak), XK: sk([lift(w, xc, ak), k1], 'expcld', '%s e. CC' % XK), ZK: sk([lift(w, zc, ak), k1], 'expcld', '%s e. CC' % ZK), IF_: ifc})
    L1 = '( W x. ( %s x. %s ) )' % (EXT('X', 'k'), ZK)
    r1 = sk([sk([d1], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (EXT('X', 'k'), ZK, XK, IF_, ZK))], 'oveq2d', '%s = ( W x. ( ( %s x. %s ) x. %s ) )' % (L1, XK, IF_, ZK))
    R1 = '( W x. %s )' % EXT(ZX, 'k')
    r2 = sk([sk([d2, sk([me], 'oveq1d', '( ( %s ^ ( k - 1 ) ) x. %s ) = ( ( %s x. %s ) x. %s )' % (ZX, IF_, ZK, XK, IF_))], 'eqtrd',
                '%s = ( ( %s x. %s ) x. %s )' % (EXT(ZX, 'k'), ZK, XK, IF_))], 'oveq2d', '%s = ( W x. ( ( %s x. %s ) x. %s ) )' % (R1, ZK, XK, IF_))
    rq = ringeq(w, ak, '( W x. ( ( %s x. %s ) x. %s ) )' % (XK, IF_, ZK), '( W x. ( ( %s x. %s ) x. %s ) )' % (ZK, XK, IF_), cl)
    tk = sk([sk([r1, rq], 'eqtrd', '%s = ( W x. ( ( %s x. %s ) x. %s ) )' % (L1, ZK, XK, IF_)), r2], 'eqtr4d', '%s = %s' % (L1, R1))
    L1n = L1.replace('( k - 1 )', '( n - 1 )')
    GF = '( n e. NN |-> %s )' % L1n
    gv, _ = mpv(w, ak, 'n', 'NN', L1n, 'k', kn)
    l1c = sk([lift(w, wc, ak), sk([sk([sk([lift(w, xc, ak), k1], 'expcld', '%s e. CC' % XK), fcc, fcn], 'divcld', '%s e. CC' % EXT('X', 'k')),
                                  sk([lift(w, zc, ak), k1], 'expcld', '%s e. CC' % ZK)], 'mulcld', '( %s x. %s ) e. CC' % (EXT('X', 'k'), ZK))], 'mulcld', '%s e. CC' % L1)
    g7 = sk([sk([gv, tk], 'eqtrd', '( %s ` k ) = %s' % (GF, R1)), sk([ev], 'oveq2d', '( W x. ( %s ` k ) ) = %s' % (EXF(ZX), R1))], 'eqtr4d', '( %s ` k ) = ( W x. ( %s ` k ) )' % (GF, EXF(ZX)))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); one = a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    im = st([nnuz, one, wc, ex, efc, g7], 'isermulc2', 'seq 1 ( + , %s ) ~~> ( W x. ( exp ` %s ) )' % (GF, ZX))
    fin = st([nnuz, one, gv, l1c, im], 'isumclim', split_imp(S_['gf2fe'])[1])
    w.qed([fin], 'idi', S_['gf2fe'])
    return w


from gf1lib import tsub

FUBH1 = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( A cseg B ) C_ U ) /\\ ( G e. %s /\\ ( H e. RR /\\ A. v e. U ( abs ` ( G ` v ) ) <_ H ) ) /\\ '
         '( R e. RR /\\ A. v e. U ( abs ` v ) <_ R ) )') % CNU
FUBH2 = '( ( ( E e. CC /\\ F e. CC ) /\\ ( E cseg F ) C_ V ) /\\ ( V C_ CC /\\ ( P e. RR /\\ A. v e. V ( abs ` v ) <_ P ) ) )'
PHI_ = lambda e: '( x e. U |-> ( ( G ` x ) x. ( exp ` ( x x. %s ) ) ) )' % e
LHSF = '( e e. V |-> ( %s lint <. A , B >. ) )' % PHI_('e')
PSI_ = lambda x: '( ( e e. V |-> ( exp ` ( %s x. e ) ) ) lint <. E , F >. )' % x
RHSF = '( x e. U |-> ( ( G ` x ) x. %s ) )' % PSI_('x')
S_['gf2fub'] = '( ( %s /\\ %s ) -> ( ( ( E cseg F ) = V -> %s e. ( V -cn-> CC ) ) /\\ ( %s lint <. E , F >. ) = ( %s lint <. A , B >. ) ) )' % (FUBH1, FUBH2, LHSF, LHSF, RHSF)
ONE = '( w e. V |-> 1 )'


def tps_inst(w, ante, sub, f):
    """apply gf2tps under ante with the substitution sub (class vars -> texts); f: facts keyed by the TPH conjunct names.
    returns (cn step, conv step, SF text, FT text, LIG(k) text function)"""
    st = mkst(w, ante)
    T = lambda t: tsub(t, sub)
    A_, B_, U_, G_, H_, R_, Q_, K_, C_ = [sub.get(c, c) for c in 'ABUGHRQKC']
    c1 = st([st([f['ac'], f['bc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), f['sgu']], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s cseg %s ) C_ %s )' % (A_, B_, A_, B_, U_))
    GB = 'A. v e. %s ( abs ` ( %s ` v ) ) <_ %s' % (U_, G_, H_)
    c2 = st([f['gcn'], st([f['hr'], f['gb']], 'jca', '( %s e. RR /\\ %s )' % (H_, GB))], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s e. RR /\\ %s ) )' % (G_, U_, H_, GB))
    RB = 'A. v e. %s ( abs ` v ) <_ %s' % (U_, R_)
    c3 = st([f['rr'], f['rb']], 'jca', '( %s e. RR /\\ %s )' % (R_, RB))
    H1 = T(FUBH1.replace(' -cn-> CC )', ' -cn-> CC )'))
    h1 = st([c1, c2, c3], '3jca', T(FUBH1))
    QB = 'A. i e. NN ( abs ` ( %s ` i ) ) <_ ( %s x. %s )' % (Q_, K_, EXT(C_, 'i'))
    h2 = st([f['qf'], st([st([f['kr'], f['k0']], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (K_, K_)), st([f['cr'], f['c0']], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (C_, C_))], 'jca',
                         '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (K_, K_, C_, C_)), f['qb']], '3jca',
            '( %s : NN --> CC /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s )' % (Q_, K_, K_, C_, C_, QB))
    concl = T(split_imp(S_['gf2tps'])[1])
    r = st([h1, h2, w.inst('gf2tps')], 'syl2anc', concl)
    SFs = T(SF); FTs = T(FT)
    cn = st([r], 'simpld', '%s e. ( %s -cn-> CC )' % (SFs, U_))
    cv = st([r], 'simprd', concl.split(' /\\ ', 1)[1][:-2])
    return cn, cv, SFs, FTs, (lambda k: T(LIG(k)))


def gf2fub():
    w = W('gf2fub', 'Fubini for the exponential kernel along two segments (Lean ` intervalIntegral_integral_swap ` in the only case used): '
                    '` int_E^F int_A^B G ( x ) e ^ ( x e ) dx de = int_A^B G ( x ) int_E^F e ^ ( x e ) de dx ` , both sides the series '
                    '` sum_k int G ( x ) x ^ ( k - 1 ) . int e ^ ( k - 1 ) / ( k - 1 ) ! ` (~ gf2tps four times, ~ gf2fe , ~ climuni ).')
    a = split_imp(S_['gf2fub'])[0]
    f0 = unpack(w, a); st = mkst(w, a)
    ac = f0['A e. CC']; bc = f0['B e. CC']; sgu = f0['( A cseg B ) C_ U']; gcn = f0['G e. %s' % CNU]
    hr = f0['H e. RR']; gb = f0['A. v e. U ( abs ` ( G ` v ) ) <_ H']; rr = f0['R e. RR']; rb = f0['A. v e. U ( abs ` v ) <_ R']
    ec = f0['E e. CC']; fc = f0['F e. CC']; sgv = f0['( E cseg F ) C_ V']; vcc = f0['V C_ CC']; pr = f0['P e. RR']; pb = f0['A. v e. V ( abs ` v ) <_ P']
    ucc = st([gcn, w.inst('cncfrss')], 'syl', 'U C_ CC')
    gff = st([gcn, w.inst('cncff')], 'syl', 'G : U --> CC')
    geq = st([gff], 'feqmptd', 'G = ( x e. U |-> ( G ` x ) )')
    gm = st([gcn, st([geq], 'eleq1d', '( G e. %s <-> ( x e. U |-> ( G ` x ) ) e. %s )' % (CNU, CNU))], 'mpbid', '( x e. U |-> ( G ` x ) ) e. %s' % CNU)
    VCN = '( V -cn-> CC )'
    cc = a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    idu = st([ucc, cc, w.inst('cncfmptid')], 'syl2anc', '( h e. U |-> h ) e. %s' % CNU)
    idv = st([vcc, cc, w.inst('cncfmptid')], 'syl2anc', '( h e. V |-> h ) e. %s' % VCN)
    idcu = st([ucc, cc, w.inst('cncfmptid')], 'syl2anc', '( c e. U |-> c ) e. %s' % CNU)
    idcv = st([vcc, cc, w.inst('cncfmptid')], 'syl2anc', '( c e. V |-> c ) e. %s' % VCN)
    geqc = st([gff], 'feqmptd', 'G = ( c e. U |-> ( G ` c ) )')
    gmc = st([gcn, st([geqc], 'eleq1d', '( G e. %s <-> ( c e. U |-> ( G ` c ) ) e. %s )' % (CNU, CNU))], 'mpbid', '( c e. U |-> ( G ` c ) ) e. %s' % CNU)
    geqh = st([gff], 'feqmptd', 'G = ( h e. U |-> ( G ` h ) )')
    gmh = st([gcn, st([geqh], 'eleq1d', '( G e. %s <-> ( h e. U |-> ( G ` h ) ) e. %s )' % (CNU, CNU))], 'mpbid', '( h e. U |-> ( G ` h ) ) e. %s' % CNU)
    onecn = st([st([], '1cnd', '1 e. CC'), vcc, cc, w.inst('cncfmptc')], 'syl3anc', '%s e. %s' % (ONE, VCN))
    uv = st([a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), ucc], 'ssexd', 'U e. _V')
    vv = st([a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), vcc], 'ssexd', 'V e. _V')

    def spec(al, P, v, t, ante, mem):
        idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, t, v, t))
        sb, _ = w.wcongr(P(v), {v: t}, '%s = %s' % (v, t), {v: idx})
        return w.s([sb, lift(w, al, ante), mem], 'rspcdva', '( %s -> %s )' % (ante, P(t)))

    def ralv(stp, ante, X, P, var='o', to='v', eqf=None):
        """( ( ante /\\ var e. X ) -> P(var) ) to ( ante -> A. to e. X P(to) ); eqf = ( F1 , F2 ) for P(v) = ( F1 ` v ) = ( F2 ` v )"""
        r1 = w.s([stp], 'ralrimiva', '( %s -> A. %s e. %s %s )' % (ante, var, X, P(var)))
        if eqf:
            F1, F2 = eqf
            e1 = w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (var, to, F1, var, F1, to))
            e2 = w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (var, to, F2, var, F2, to))
            sb = w.s([e1, e2], 'eqeq12d', '( %s = %s -> ( %s <-> %s ) )' % (var, to, P(var), P(to)))
        else:
            idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, to, var, to))
            sb, _ = w.wcongr(P(var), {var: to}, '%s = %s' % (var, to), {var: idx})
        cb = w.s([sb], 'cbvralvw', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (var, X, P(var), to, X, P(to)))
        return w.s([r1, cb], 'sylib', '( %s -> A. %s e. %s %s )' % (ante, to, X, P(to)))

    au = st([sgu, st([ac, bc, w.inst('csegid1')], 'syl2anc', 'A e. ( A cseg B )')], 'sseldd', 'A e. U')
    ga = st([gff, au], 'ffvelcdmd', '( G ` A ) e. CC')
    h0 = st([st([], '0red', '0 e. RR'), st([ga], 'abscld', '( abs ` ( G ` A ) ) e. RR'), hr, st([ga], 'absge0d', '0 <_ ( abs ` ( G ` A ) )'),
             spec(gb, lambda v: '( abs ` ( G ` %s ) ) <_ H' % v, 'v', 'A', a, au)], 'letrd', '0 <_ H')
    r0 = st([st([], '0red', '0 e. RR'), st([ac], 'abscld', '( abs ` A ) e. RR'), rr, st([ac], 'absge0d', '0 <_ ( abs ` A )'),
             spec(rb, lambda v: '( abs ` %s ) <_ R' % v, 'v', 'A', a, au)], 'letrd', '0 <_ R')
    ev = st([sgv, st([ec, fc, w.inst('csegid1')], 'syl2anc', 'E e. ( E cseg F )')], 'sseldd', 'E e. V')
    p0 = st([st([], '0red', '0 e. RR'), st([ec], 'abscld', '( abs ` E ) e. RR'), pr, st([ec], 'absge0d', '0 <_ ( abs ` E )'),
             spec(pb, lambda v: '( abs ` %s ) <_ P' % v, 'v', 'E', a, ev)], 'letrd', '0 <_ P')
    # ( ONE ` o ) = 1 and its bound
    def onev(ante, mem, o):
        return mpv(w, ante, 'w', 'V', '1', o, mem, exs=a1(w, ante, w.s([], '1ex', '1 e. _V'), '1 e. _V'))[0]
    ao = '( %s /\\ o e. V )' % a
    so = mkst(w, ao)
    ov = onev(ao, so([], 'simpr', 'o e. V'), 'o')
    ob = so([so([ov], 'fveq2d', '( abs ` ( %s ` o ) ) = ( abs ` 1 )' % ONE), a1(w, ao, w.s([], 'abs1', '( abs ` 1 ) = 1'), '( abs ` 1 ) = 1')], 'eqtrd', '( abs ` ( %s ` o ) ) = 1' % ONE)
    ob2 = so([ob, so([so([], '1red', '1 e. RR')], 'leidd', '1 <_ 1')], 'eqbrtrd', '( abs ` ( %s ` o ) ) <_ 1' % ONE)
    oneb = ralv(ob2, a, 'V', lambda v: '( abs ` ( %s ` %s ) ) <_ 1' % (ONE, v))

    LIGG = lambda D, Gx, Ax, Bx, l, c='c': '( ( %s e. %s |-> ( ( %s ` %s ) x. ( %s ^ ( %s - 1 ) ) ) ) lint <. %s , %s >. )' % (c, D, Gx, c, c, l, Ax, Bx)

    def gpcn(ante, D, Gx, gxm, idx_, l, lnn, c='h'):
        """( ante -> ( c e. D |-> ( ( Gx ` c ) x. ( c ^ ( l - 1 ) ) ) ) e. ( D -cn-> CC ) )"""
        sa = mkst(w, ante)
        l1 = sa([lnn, w.inst('nnm1nn0')], 'syl', '( %s - 1 ) e. NN0' % l)
        pw = sa([lift(w, idx_, ante), l1, w.inst('cncfexpb')], 'syl2anc', '( %s e. %s |-> ( %s ^ ( %s - 1 ) ) ) e. ( %s -cn-> CC )' % (c, D, c, l, D))
        return sa([lift(w, gxm, ante), pw], 'mulcncf', '( %s e. %s |-> ( ( %s ` %s ) x. ( %s ^ ( %s - 1 ) ) ) ) e. ( %s -cn-> CC )' % (c, D, Gx, c, c, l, D))

    def coef(ante, D, Gx, Hx, Rx, Ax, Bx, fx):
        """Q = ( l e. NN |-> ( LIGG(l) / ( ! ` ( l - 1 ) ) ) ): Q : NN --> CC and the factorial bound with K = ( Hx x. ( abs ` ( Bx - Ax ) ) ), C = Rx"""
        sa = mkst(w, ante)
        Q = '( l e. NN |-> ( %s / ( ! ` ( l - 1 ) ) ) )' % LIGG(D, Gx, Ax, Bx, 'l')
        K = '( %s x. ( abs ` ( %s - %s ) ) )' % (Hx, Bx, Ax)
        al = '( %s /\\ l e. NN )' % ante
        sl = mkst(w, al)
        ln = sl([], 'simpr', 'l e. NN')
        l1 = sl([ln, w.inst('nnm1nn0')], 'syl', '( l - 1 ) e. NN0')
        fl = sl([l1, w.inst('faccl')], 'syl', '( ! ` ( l - 1 ) ) e. NN')
        seg = '( %s cseg %s )' % (Ax, Bx)
        lic = sl([sl([lift(w, fx['axc'], al), lift(w, fx['bxc'], al)], 'jca', '( %s e. CC /\\ %s e. CC )' % (Ax, Bx)),
                  sl([gpcn(al, D, Gx, fx['gxmc'], fx['idxc'], 'l', ln, 'c'), lift(w, fx['sgx'], al)], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (
                      '( c e. %s |-> ( ( %s ` c ) x. ( c ^ ( l - 1 ) ) ) )' % (D, Gx), D, seg, D)), w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIGG(D, Gx, Ax, Bx, 'l'))
        qv = sl([lic, sl([fl], 'nncnd', '( ! ` ( l - 1 ) ) e. CC'), sl([fl], 'nnne0d', '( ! ` ( l - 1 ) ) =/= 0')], 'divcld', '( %s / ( ! ` ( l - 1 ) ) ) e. CC' % LIGG(D, Gx, Ax, Bx, 'l'))
        qf = sa([qv], 'fmptd', '%s : NN --> CC' % Q)
        # the bound at i
        ai = '( %s /\\ i e. NN )' % ante
        si = mkst(w, ai)
        inn = si([], 'simpr', 'i e. NN')
        i1 = si([inn, w.inst('nnm1nn0')], 'syl', '( i - 1 ) e. NN0')
        fi = si([i1, w.inst('faccl')], 'syl', '( ! ` ( i - 1 ) ) e. NN')
        FI = '( ! ` ( i - 1 ) )'
        GPi = '( c e. %s |-> ( ( %s ` c ) x. ( c ^ ( i - 1 ) ) ) )' % (D, Gx)
        LI_ = LIGG(D, Gx, Ax, Bx, 'i')
        gpi = gpcn(ai, D, Gx, fx['gxmc'], fx['idxc'], 'i', inn, 'c')
        RI = '( %s ^ ( i - 1 ) )' % Rx
        MB = '( %s x. %s )' % (Hx, RI)
        rir = si([lift(w, fx['rxr'], ai), i1], 'reexpcld', '%s e. RR' % RI)
        mbr = si([lift(w, fx['hxr'], ai), rir], 'remulcld', '%s e. RR' % MB)
        aio = '( %s /\\ q e. %s )' % (ai, seg)
        sq = mkst(w, aio)
        qd = sq([lift(w, fx['sgx'], aio), sq([], 'simpr', 'q e. %s' % seg)], 'sseldd', 'q e. %s' % D)
        qc = sq([lift(w, fx['dcc'], aio), qd], 'sseldd', 'q e. CC')
        gv = fvd(w, aio, 'c', D, '( ( %s ` c ) x. ( c ^ ( i - 1 ) ) )' % Gx, 'q', qd, sq([], 'ovexd', '( ( %s ` q ) x. ( q ^ ( i - 1 ) ) ) e. _V' % Gx))
        gqc = sq([lift(w, fx['gxf'], aio), qd], 'ffvelcdmd', '( %s ` q ) e. CC' % Gx)
        i1q = lift(w, i1, aio)
        am = sq([gqc, sq([qc, i1q], 'expcld', '( q ^ ( i - 1 ) ) e. CC')], 'absmuld', '( abs ` ( ( %s ` q ) x. ( q ^ ( i - 1 ) ) ) ) = ( ( abs ` ( %s ` q ) ) x. ( abs ` ( q ^ ( i - 1 ) ) ) )' % (Gx, Gx))
        ae = sq([qc, i1q], 'absexpd', '( abs ` ( q ^ ( i - 1 ) ) ) = ( ( abs ` q ) ^ ( i - 1 ) )')
        AG = '( abs ` ( %s ` q ) )' % Gx; AQ = '( ( abs ` q ) ^ ( i - 1 ) )'
        gqb = spec(fx['gxb'], lambda v: '( abs ` ( %s ` %s ) ) <_ %s' % (Gx, v, Hx), 'v', 'q', aio, qd)
        qb_ = spec(fx['rxb'], lambda v: '( abs ` %s ) <_ %s' % (v, Rx), 'v', 'q', aio, qd)
        aqr = sq([qc], 'abscld', '( abs ` q ) e. RR'); aq0 = sq([qc], 'absge0d', '0 <_ ( abs ` q )')
        pwb = sq([sq([aqr, lift(w, fx['rxr'], aio), i1q], '3jca', '( ( abs ` q ) e. RR /\\ %s e. RR /\\ ( i - 1 ) e. NN0 )' % Rx), sq([aq0, qb_], 'jca', '( 0 <_ ( abs ` q ) /\\ ( abs ` q ) <_ %s )' % Rx),
                  w.inst('leexp1a')], 'syl2anc', '%s <_ %s' % (AQ, RI))
        pb2 = sq([sq([gqc], 'abscld', '%s e. RR' % AG), lift(w, fx['hxr'], aio), sq([aqr, i1q], 'reexpcld', '%s e. RR' % AQ), lift(w, rir, aio), sq([gqc], 'absge0d', '0 <_ %s' % AG),
                  sq([aqr, i1q, aq0], 'expge0d', '0 <_ %s' % AQ), gqb, pwb], 'lemul12ad', '( %s x. %s ) <_ %s' % (AG, AQ, MB))
        pb3 = sq([sq([sq([gv], 'fveq2d', '( abs ` ( %s ` q ) ) = ( abs ` ( ( %s ` q ) x. ( q ^ ( i - 1 ) ) ) )' % (GPi, Gx)), am], 'eqtrd',
                     '( abs ` ( %s ` q ) ) = ( ( abs ` ( %s ` q ) ) x. ( abs ` ( q ^ ( i - 1 ) ) ) )' % (GPi, Gx)),
                  sq([ae], 'oveq2d', '( %s x. ( abs ` ( q ^ ( i - 1 ) ) ) ) = ( %s x. %s )' % (AG, AG, AQ))], 'eqtrd', '( abs ` ( %s ` q ) ) = ( %s x. %s )' % (GPi, AG, AQ))
        pb4 = sq([pb3, pb2], 'eqbrtrd', '( abs ` ( %s ` q ) ) <_ %s' % (GPi, MB))
        allz = ralv(pb4, ai, seg, lambda z: '( abs ` ( %s ` %s ) ) <_ %s' % (GPi, z, MB), var='q', to='z')
        la = si([si([si([lift(w, fx['axc'], ai), lift(w, fx['bxc'], ai)], 'jca', '( %s e. CC /\\ %s e. CC )' % (Ax, Bx)), si([gpi, lift(w, fx['sgx'], ai)], 'jca',
                                                                                                                         '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GPi, D, seg, D))],
                     'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (Ax, Bx, GPi, D, seg, D)), mbr, allz, w.inst('lintabs')], 'syl3anc',
                '( abs ` %s ) <_ ( %s x. ( abs ` ( %s - %s ) ) )' % (LI_, MB, Bx, Ax))
        lic_i = si([si([lift(w, fx['axc'], ai), lift(w, fx['bxc'], ai)], 'jca', '( %s e. CC /\\ %s e. CC )' % (Ax, Bx)), si([gpi, lift(w, fx['sgx'], ai)], 'jca',
                                                                                                                  '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GPi, D, seg, D)), w.inst('lintcl')],
                   'syl2anc', '%s e. CC' % LI_)
        qiv, _ = mpv(w, ai, 'l', 'NN', '( %s / ( ! ` ( l - 1 ) ) )' % LIGG(D, Gx, Ax, Bx, 'l'), 'i', inn)
        fic = si([fi], 'nncnd', '%s e. CC' % FI); fin_ = si([fi], 'nnne0d', '%s =/= 0' % FI)
        fir = si([fi], 'nnrpd', '%s e. RR+' % FI)
        ad = si([lic_i, fic, fin_], 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (LI_, FI, LI_, FI))
        af = si([si([fir], 'rpred', '%s e. RR' % FI), si([fir], 'rpge0d', '0 <_ %s' % FI)], 'absidd', '( abs ` %s ) = %s' % (FI, FI))
        ad2 = si([ad, si([af], 'oveq2d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / %s )' % (LI_, FI, LI_, FI))], 'eqtrd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / %s )' % (LI_, FI, LI_, FI))
        BA_ = '( abs ` ( %s - %s ) )' % (Bx, Ax)
        bar = si([si([lift(w, fx['bxc'], ai), lift(w, fx['axc'], ai)], 'subcld', '( %s - %s ) e. CC' % (Bx, Ax))], 'abscld', '%s e. RR' % BA_)
        UP = '( %s x. %s )' % (MB, BA_)
        upr = si([mbr, bar], 'remulcld', '%s e. RR' % UP)
        dv = si([la, si([si([lic_i], 'abscld', '( abs ` %s ) e. RR' % LI_), upr, fir], 'lediv1d', '( ( abs ` %s ) <_ %s <-> ( ( abs ` %s ) / %s ) <_ ( %s / %s ) )' % (LI_, UP, LI_, FI, UP, FI))],
                'mpbid', '( ( abs ` %s ) / %s ) <_ ( %s / %s )' % (LI_, FI, UP, FI))
        IF_ = '( 1 / %s )' % FI
        ifr = si([fic, fin_], 'reccld', '%s e. CC' % IF_)
        d1 = si([si([upr], 'recnd', '%s e. CC' % UP), fic, fin_], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (UP, FI, UP, IF_))
        d2 = si([si([rir], 'recnd', '%s e. CC' % RI), fic, fin_], 'divrecd', '%s = ( %s x. %s )' % (EXT(Rx, 'i'), RI, IF_))
        cl = Closure(w, ai, {Hx: lift(w, fx['hxr'], ai), RI: rir, BA_: bar, IF_: ifr})
        rq = ringeq(w, ai, '( %s x. %s )' % (UP, IF_), '( ( %s x. %s ) x. ( %s x. %s ) )' % (Hx, BA_, RI, IF_), cl)
        eqK = si([si([d1, rq], 'eqtrd', '( %s / %s ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (UP, FI, Hx, BA_, RI, IF_)),
                  si([d2], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (K, EXT(Rx, 'i'), K, RI, IF_))], 'eqtr4d', '( %s / %s ) = ( %s x. %s )' % (UP, FI, K, EXT(Rx, 'i')))
        qib = si([si([si([qiv], 'fveq2d', '( abs ` ( %s ` i ) ) = ( abs ` ( %s / %s ) )' % (Q, LI_, FI)), ad2], 'eqtrd', '( abs ` ( %s ` i ) ) = ( ( abs ` %s ) / %s )' % (Q, LI_, FI)),
                  si([dv, eqK], 'breqtrd', '( ( abs ` %s ) / %s ) <_ ( %s x. %s )' % (LI_, FI, K, EXT(Rx, 'i')))], 'eqbrtrd', '( abs ` ( %s ` i ) ) <_ ( %s x. %s )' % (Q, K, EXT(Rx, 'i')))
        qb = sa([qib], 'ralrimiva', 'A. i e. NN ( abs ` ( %s ` i ) ) <_ ( %s x. %s )' % (Q, K, EXT(Rx, 'i')))
        ba0 = sa([sa([lift(w, fx['bxc'], ante), lift(w, fx['axc'], ante)], 'subcld', '( %s - %s ) e. CC' % (Bx, Ax))], 'absge0d', '0 <_ %s' % BA_)
        bar_a = sa([sa([lift(w, fx['bxc'], ante), lift(w, fx['axc'], ante)], 'subcld', '( %s - %s ) e. CC' % (Bx, Ax))], 'abscld', '%s e. RR' % BA_)
        kr = sa([lift(w, fx['hxr'], ante), bar_a], 'remulcld', '%s e. RR' % K)
        k0 = sa([lift(w, fx['hxr'], ante), bar_a, lift(w, fx['hx0'], ante), ba0], 'mulge0d', '0 <_ %s' % K)
        return Q, K, qf, qb, kr, k0

    FXU = dict(axc=ac, bxc=bc, sgx=sgu, gxm=gmh, idx=idu, gxmc=gmc, idxc=idcu, gxf=gff, gxb=gb, hxr=hr, hx0=h0, rxr=rr, rxb=rb, dcc=ucc)
    oneeqh = st([st([onecn, w.inst('cncff')], 'syl', '%s : V --> CC' % ONE)], 'feqmptd', '%s = ( h e. V |-> ( %s ` h ) )' % (ONE, ONE))
    oneeqc = st([st([onecn, w.inst('cncff')], 'syl', '%s : V --> CC' % ONE)], 'feqmptd', '%s = ( c e. V |-> ( %s ` c ) )' % (ONE, ONE))
    onemc = st([onecn, st([oneeqc], 'eleq1d', '( %s e. %s <-> ( c e. V |-> ( %s ` c ) ) e. %s )' % (ONE, VCN, ONE, VCN))], 'mpbid', '( c e. V |-> ( %s ` c ) ) e. %s' % (ONE, VCN))
    onem = st([onecn, st([oneeqh], 'eleq1d', '( %s e. %s <-> ( h e. V |-> ( %s ` h ) ) e. %s )' % (ONE, VCN, ONE, VCN))], 'mpbid', '( h e. V |-> ( %s ` h ) ) e. %s' % (ONE, VCN))
    FXV = dict(axc=ec, bxc=fc, sgx=sgv, gxm=onem, idx=idv, gxmc=onemc, idxc=idcv, gxf=st([onecn, w.inst('cncff')], 'syl', '%s : V --> CC' % ONE), gxb=oneb, hxr=st([], '1red', '1 e. RR'),
               hx0=a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), rxr=pr, rxb=pb, dcc=vcc)
    Q2, K2, qf2, qb2, kr2, k02 = coef(a, 'U', 'G', 'H', 'R', 'A', 'B', FXU)
    Q4, K4, qf4, qb4, kr4, k04 = coef(a, 'V', ONE, '1', 'P', 'E', 'F', FXV)

    def fv2(ph, x, A_, body, bex):
        """fvmpt2d: the value of ( x e. A_ |-> body ) at its own binder"""
        mp = '( %s e. %s |-> %s )' % (x, A_, body)
        return w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, mp, mp)), bex], 'fvmpt2d', '( ( %s /\\ %s e. %s ) -> ( %s ` %s ) = %s )' % (ph, x, A_, mp, x, body))

    def extcc(ante, X, xc, k, kn):
        sa = mkst(w, ante)
        k1 = sa([kn, w.inst('nnm1nn0')], 'syl', '( %s - 1 ) e. NN0' % k)
        fk = sa([k1, w.inst('faccl')], 'syl', '( ! ` ( %s - 1 ) ) e. NN' % k)
        return sa([sa([xc, k1], 'expcld', '( %s ^ ( %s - 1 ) ) e. CC' % (X, k)), sa([fk], 'nncnd', '( ! ` ( %s - 1 ) ) e. CC' % k), sa([fk], 'nnne0d', '( ! ` ( %s - 1 ) ) =/= 0' % k)],
                  'divcld', '%s e. CC' % EXT(X, k))

    def qexp(ante, X, xc):
        """QX = ( l e. NN |-> EXT(X, l) ): QX : NN --> CC and A. i e. NN ( abs ` ( QX ` i ) ) <_ ( 1 x. EXT(( abs ` X ), i) )"""
        sa = mkst(w, ante)
        QX = '( l e. NN |-> %s )' % EXT(X, 'l')
        al = '( %s /\\ l e. NN )' % ante
        qf = sa([extcc(al, X, lift(w, xc, al), 'l', mkst(w, al)([], 'simpr', 'l e. NN'))], 'fmptd', '%s : NN --> CC' % QX)
        ai = '( %s /\\ i e. NN )' % ante
        si = mkst(w, ai)
        inn = si([], 'simpr', 'i e. NN')
        i1 = si([inn, w.inst('nnm1nn0')], 'syl', '( i - 1 ) e. NN0')
        fi = si([i1, w.inst('faccl')], 'syl', '( ! ` ( i - 1 ) ) e. NN')
        FI = '( ! ` ( i - 1 ) )'; AX = '( abs ` %s )' % X
        qv, _ = mpv(w, ai, 'l', 'NN', EXT(X, 'l'), 'i', inn)
        xi = si([lift(w, xc, ai), i1], 'expcld', '( %s ^ ( i - 1 ) ) e. CC' % X)
        ad = si([xi, si([fi], 'nncnd', '%s e. CC' % FI), si([fi], 'nnne0d', '%s =/= 0' % FI)], 'absdivd', '( abs ` %s ) = ( ( abs ` ( %s ^ ( i - 1 ) ) ) / ( abs ` %s ) )' % (EXT(X, 'i'), X, FI))
        ae = si([lift(w, xc, ai), i1], 'absexpd', '( abs ` ( %s ^ ( i - 1 ) ) ) = ( %s ^ ( i - 1 ) )' % (X, AX))
        af = si([si([fi], 'nnred', '%s e. RR' % FI), si([si([fi], 'nnrpd', '%s e. RR+' % FI)], 'rpge0d', '0 <_ %s' % FI)], 'absidd', '( abs ` %s ) = %s' % (FI, FI))
        e1 = si([ad, si([ae, af], 'oveq12d', '( ( abs ` ( %s ^ ( i - 1 ) ) ) / ( abs ` %s ) ) = %s' % (X, FI, EXT(AX, 'i')))], 'eqtrd', '( abs ` %s ) = %s' % (EXT(X, 'i'), EXT(AX, 'i')))
        e2 = si([si([qv], 'fveq2d', '( abs ` ( %s ` i ) ) = ( abs ` %s )' % (QX, EXT(X, 'i'))), e1], 'eqtrd', '( abs ` ( %s ` i ) ) = %s' % (QX, EXT(AX, 'i')))
        exr = si([si([si([lift(w, xc, ai)], 'abscld', '%s e. RR' % AX), i1], 'reexpcld', '( %s ^ ( i - 1 ) ) e. RR' % AX), si([fi], 'nnred', '%s e. RR' % FI), si([fi], 'nnne0d', '%s =/= 0' % FI)],
                 'redivcld', '%s e. RR' % EXT(AX, 'i'))
        e3 = si([si([exr], 'recnd', '%s e. CC' % EXT(AX, 'i'))], 'mullidd', '( 1 x. %s ) = %s' % (EXT(AX, 'i'), EXT(AX, 'i')))
        e4 = si([si([e2, si([e3], 'eqcomd', '%s = ( 1 x. %s )' % (EXT(AX, 'i'), EXT(AX, 'i')))], 'eqtrd', '( abs ` ( %s ` i ) ) = ( 1 x. %s )' % (QX, EXT(AX, 'i'))),
                  si([si([si([], '1red', '1 e. RR'), exr], 'remulcld', '( 1 x. %s ) e. RR' % EXT(AX, 'i'))], 'leidd',
                     '( 1 x. %s ) <_ ( 1 x. %s )' % (EXT(AX, 'i'), EXT(AX, 'i')))], 'eqbrtrd', '( abs ` ( %s ` i ) ) <_ ( 1 x. %s )' % (QX, EXT(AX, 'i')))
        qb = sa([e4], 'ralrimiva', 'A. i e. NN ( abs ` ( %s ` i ) ) <_ ( 1 x. %s )' % (QX, EXT(AX, 'i')))
        return QX, qf, qb, sa([lift(w, xc, ante)], 'abscld', '%s e. RR' % AX), sa([lift(w, xc, ante)], 'absge0d', '0 <_ %s' % AX)

    one_r = st([], '1red', '1 e. RR'); one0 = a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1')
    LIG1 = lambda k: LIGG('U', 'G', 'A', 'B', k, 'h')
    LIG2 = lambda k: LIGG('V', ONE, 'E', 'F', k, 'h')
    LIG1c = lambda k: LIGG('U', 'G', 'A', 'B', k, 'c')
    LIG2c = lambda k: LIGG('V', ONE, 'E', 'F', k, 'c')

    def cvh(ante, D, Gx, Ax, Bx, k):
        """( ante -> LIGc(k) = LIGh(k) ) (renaming the bound variable)"""
        bc_ = '( ( %s ` c ) x. ( c ^ ( %s - 1 ) ) )' % (Gx, k)
        e = w.s([cg(w, bc_, 'c', 'h')], 'cbvmptv', '( c e. %s |-> %s ) = ( h e. %s |-> ( ( %s ` h ) x. ( h ^ ( %s - 1 ) ) ) )' % (D, bc_, D, Gx, k))
        e2 = w.s([e], 'oveq1i', '%s = %s' % (LIGG(D, Gx, Ax, Bx, k, 'c'), LIGG(D, Gx, Ax, Bx, k, 'h')))
        return a1(w, ante, e2, '%s = %s' % (LIGG(D, Gx, Ax, Bx, k, 'c'), LIGG(D, Gx, Ax, Bx, k, 'h')))
    S1 = '( A cseg B )'; S2 = '( E cseg F )'

    def block1(ante, qn, qmem):
        """under ante with qmem ( ante -> qn e. V ): sum_ k e. NN ( EXT(qn,k) x. LIG1(k) ) = ( PHI_(qn) lint <. A , B >. )"""
        sa = mkst(w, ante)
        qc = sa([lift(w, vcc, ante), qmem], 'sseldd', '%s e. CC' % qn)
        QX, qf, qb, cr, c0 = qexp(ante, qn, qc)
        L_ = lambda s_: lift(w, s_, ante)
        f1 = dict(ac=L_(ac), bc=L_(bc), sgu=L_(sgu), gcn=L_(gcn), hr=L_(hr), gb=L_(gb), rr=L_(rr), rb=L_(rb), qf=qf, kr=L_(one_r), k0=L_(one0), cr=cr, c0=c0, qb=qb)
        cn1, cv1, SF1, FT1, LIGf = tps_inst(w, ante, {'Q': QX, 'K': '1', 'C': '( abs ` %s )' % qn}, f1)
        # SF1 = PHI_(qn) on the segment: point b
        ab = '( %s /\\ q e. %s )' % (ante, S1)
        sb = mkst(w, ab)
        bu = sb([lift(w, sgu, ab), sb([], 'simpr', 'q e. %s' % S1)], 'sseldd', 'q e. U')
        bcc = sb([lift(w, ucc, ab), bu], 'sseldd', 'q e. CC')
        body = 'sum_ k e. NN ( ( %s ` k ) ` r )' % FT1
        v1, _ = mpv(w, ab, 'r', 'U', body, 'q', bu, exs=a1(w, ab, w.s([], 'sumex', '%s e. _V' % body.replace('` r )', '` q )')), '%s e. _V' % body.replace('` r )', '` q )')))
        abk = '( %s /\\ k e. NN )' % ab
        sk = mkst(w, abk)
        kn = sk([], 'simpr', 'k e. NN')
        FTK = '( x e. U |-> ( ( G ` x ) x. ( ( %s ` k ) x. ( x ^ ( k - 1 ) ) ) ) )' % QX
        t1, _ = mpv(w, abk, 'm', 'NN', '( x e. U |-> ( ( G ` x ) x. ( ( %s ` m ) x. ( x ^ ( m - 1 ) ) ) ) )' % QX, 'k', kn, exs=sk([lift(w, uv, abk)], 'mptexd', '%s e. _V' % FTK))
        t2 = fvd(w, abk, 'x', 'U', '( ( G ` x ) x. ( ( %s ` k ) x. ( x ^ ( k - 1 ) ) ) )' % QX, 'q', lift(w, bu, abk), sk([], 'ovexd', '( ( G ` q ) x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) ) e. _V' % QX))
        qv, _ = mpv(w, abk, 'l', 'NN', EXT(qn, 'l'), 'k', kn)
        TB = '( ( G ` q ) x. ( %s x. ( q ^ ( k - 1 ) ) ) )' % EXT(qn, 'k')
        t3 = sk([sk([sk([qv], 'oveq1d', '( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) = ( %s x. ( q ^ ( k - 1 ) ) )' % (QX, EXT(qn, 'k')))], 'oveq2d',
                    '( ( G ` q ) x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) ) = %s' % (QX, TB))], 'idi', '( ( G ` q ) x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) ) = %s' % (QX, TB))
        tk = sk([sk([sk([t1], 'fveq1d', '( ( %s ` k ) ` q ) = ( %s ` q )' % (FT1, FTK)), t2], 'eqtrd', '( ( %s ` k ) ` q ) = ( ( G ` q ) x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) )' % (FT1, QX)), t3],
                'eqtrd', '( ( %s ` k ) ` q ) = %s' % (FT1, TB))
        ss = sb([tk], 'sumeq2dv', 'sum_ k e. NN ( ( %s ` k ) ` q ) = sum_ k e. NN %s' % (FT1, TB))
        gbc = sb([lift(w, gff, ab), bu], 'ffvelcdmd', '( G ` q ) e. CC')
        fe = sb([gbc, bcc, lift(w, qc, ab), w.inst('gf2fe')], 'syl3anc', 'sum_ k e. NN %s = ( ( G ` q ) x. ( exp ` ( q x. %s ) ) )' % (TB, qn))
        pv = fvd(w, ab, 'x', 'U', '( ( G ` x ) x. ( exp ` ( x x. %s ) ) )' % qn, 'q', bu, sb([], 'ovexd', '( ( G ` q ) x. ( exp ` ( q x. %s ) ) ) e. _V' % qn))
        eqb = sb([sb([sb([v1, ss], 'eqtrd', '( %s ` q ) = sum_ k e. NN %s' % (SF1, TB)), fe], 'eqtrd', '( %s ` q ) = ( ( G ` q ) x. ( exp ` ( q x. %s ) ) )' % (SF1, qn)), pv], 'eqtr4d',
                 '( %s ` q ) = ( %s ` q )' % (SF1, PHI_(qn)))
        allz = ralv(eqb, ante, S1, lambda z: '( %s ` %s ) = ( %s ` %s )' % (SF1, z, PHI_(qn), z), var='q', to='z', eqf=(SF1, PHI_(qn)))
        le = sa([sa([sa([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'), sa([sa([cn1], 'elexd', '%s e. _V' % SF1), sa([L_(uv)], 'mptexd', '%s e. _V' % PHI_(qn))], 'jca',
                                                                                    '( %s e. _V /\\ %s e. _V )' % (SF1, PHI_(qn)))], 'jca',
                    '( ( A e. CC /\\ B e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SF1, PHI_(qn))), allz, w.inst('linteq')], 'syl2anc',
                '( %s lint <. A , B >. ) = ( %s lint <. A , B >. )' % (SF1, PHI_(qn)))
        cv = sa([cv1, le], 'breqtrd', 'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) x. %s ) ) ) ~~> ( %s lint <. A , B >. )' % (QX, LIG1('k'), PHI_(qn)))
        # the isum form
        SQF = '( k e. NN |-> ( ( %s ` k ) x. %s ) )' % (QX, LIG1('k'))
        CVR = '( %s lint <. A , B >. )' % PHI_(qn)
        ak = '( %s /\\ k e. NN )' % ante
        sk2 = mkst(w, ak)
        kn2 = sk2([], 'simpr', 'k e. NN')
        lic = sk2([sk2([lift(w, ac, ak), lift(w, bc, ak)], 'jca', '( A e. CC /\\ B e. CC )'), sk2([gpcn(ak, 'U', 'G', gmh, idu, 'k', kn2), lift(w, sgu, ak)], 'jca',
                                                                                                    '( %s e. %s /\\ %s C_ U )' % (GP('k'), CNU, S1)), w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIG1('k'))
        qv2, _ = mpv(w, ak, 'l', 'NN', EXT(qn, 'l'), 'k', kn2)
        TT = '( %s x. %s )' % (EXT(qn, 'k'), LIG1('k'))
        SQFn = '( n e. NN |-> ( ( %s ` n ) x. %s ) )' % (QX, LIG1('n'))
        eqn = w.s([cg(w, '( ( %s ` k ) x. %s )' % (QX, LIG1('k')), 'k', 'n')], 'cbvmptv', '%s = %s' % (SQF, SQFn))
        cv = sa([cv, sa([sa([a1(w, ante, eqn, '%s = %s' % (SQF, SQFn))], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (SQF, SQFn))], 'breq1d',
                     '( seq 1 ( + , %s ) ~~> %s <-> seq 1 ( + , %s ) ~~> %s )' % (SQF, CVR, SQFn, CVR))], 'mpbid', 'seq 1 ( + , %s ) ~~> %s' % (SQFn, CVR))
        fvq, _ = mpv(w, ak, 'n', 'NN', '( ( %s ` n ) x. %s )' % (QX, LIG1('n')), 'k', kn2)
        SQF = SQFn
        f3 = sk2([fvq, sk2([qv2], 'oveq1d', '( ( %s ` k ) x. %s ) = %s' % (QX, LIG1('k'), TT))], 'eqtrd', '( %s ` k ) = %s' % (SQF, TT))
        tc = sk2([extcc(ak, qn, lift(w, qc, ak), 'k', kn2), lic], 'mulcld', '%s e. CC' % TT)
        isum = sa([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, ante, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), f3, tc, cv], 'isumclim',
                  'sum_ k e. NN %s = ( %s lint <. A , B >. )' % (TT, PHI_(qn)))
        return isum

    onef = st([onecn, w.inst('cncff')], 'syl', '%s : V --> CC' % ONE)
    EPS = lambda qn: '( e e. V |-> ( exp ` ( %s x. e ) ) )' % qn

    def block3(ante, qn, qmem):
        """under ante with qmem ( ante -> qn e. U ): sum_ k e. NN ( EXT(qn,k) x. LIG2(k) ) = PSI_(qn)"""
        sa = mkst(w, ante)
        qc = sa([lift(w, ucc, ante), qmem], 'sseldd', '%s e. CC' % qn)
        QX, qf, qb, cr, c0 = qexp(ante, qn, qc)
        L_ = lambda s_: lift(w, s_, ante)
        f3 = dict(ac=L_(ec), bc=L_(fc), sgu=L_(sgv), gcn=L_(onecn), hr=L_(one_r), gb=L_(oneb), rr=L_(pr), rb=L_(pb), qf=qf, kr=L_(one_r), k0=L_(one0), cr=cr, c0=c0, qb=qb)
        sub = {'A': 'E', 'B': 'F', 'U': 'V', 'G': ONE, 'H': '1', 'R': 'P', 'Q': QX, 'K': '1', 'C': '( abs ` %s )' % qn}
        cn3, cv3, SF3, FT3, LIGf = tps_inst(w, ante, sub, f3)
        ab = '( %s /\\ q e. %s )' % (ante, S2)
        sb = mkst(w, ab)
        bv_ = sb([lift(w, sgv, ab), sb([], 'simpr', 'q e. %s' % S2)], 'sseldd', 'q e. V')
        bcc = sb([lift(w, vcc, ab), bv_], 'sseldd', 'q e. CC')
        body = 'sum_ k e. NN ( ( %s ` k ) ` r )' % FT3
        v1, _ = mpv(w, ab, 'r', 'V', body, 'q', bv_, exs=a1(w, ab, w.s([], 'sumex', '%s e. _V' % body.replace('` r )', '` q )')), '%s e. _V' % body.replace('` r )', '` q )')))
        abk = '( %s /\\ k e. NN )' % ab
        sk = mkst(w, abk)
        kn = sk([], 'simpr', 'k e. NN')
        FTK = '( x e. V |-> ( ( %s ` x ) x. ( ( %s ` k ) x. ( x ^ ( k - 1 ) ) ) ) )' % (ONE, QX)
        t1, _ = mpv(w, abk, 'm', 'NN', '( x e. V |-> ( ( %s ` x ) x. ( ( %s ` m ) x. ( x ^ ( m - 1 ) ) ) ) )' % (ONE, QX), 'k', kn, exs=sk([lift(w, vv, abk)], 'mptexd', '%s e. _V' % FTK))
        t2 = fvd(w, abk, 'x', 'V', '( ( %s ` x ) x. ( ( %s ` k ) x. ( x ^ ( k - 1 ) ) ) )' % (ONE, QX), 'q', lift(w, bv_, abk),
                 sk([], 'ovexd', '( ( %s ` q ) x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) ) e. _V' % (ONE, QX)))
        qv, _ = mpv(w, abk, 'l', 'NN', EXT(qn, 'l'), 'k', kn)
        OB = '( %s ` q )' % ONE
        TB = '( %s x. ( %s x. ( q ^ ( k - 1 ) ) ) )' % (OB, EXT(qn, 'k'))
        t3 = sk([sk([qv], 'oveq1d', '( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) = ( %s x. ( q ^ ( k - 1 ) ) )' % (QX, EXT(qn, 'k')))], 'oveq2d',
                '( %s x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) ) = %s' % (OB, QX, TB))
        tk = sk([sk([sk([t1], 'fveq1d', '( ( %s ` k ) ` q ) = ( %s ` q )' % (FT3, FTK)), t2], 'eqtrd', '( ( %s ` k ) ` q ) = ( %s x. ( ( %s ` k ) x. ( q ^ ( k - 1 ) ) ) )' % (FT3, OB, QX)), t3],
                'eqtrd', '( ( %s ` k ) ` q ) = %s' % (FT3, TB))
        ss = sb([tk], 'sumeq2dv', 'sum_ k e. NN ( ( %s ` k ) ` q ) = sum_ k e. NN %s' % (FT3, TB))
        obv = onev(ab, bv_, 'q')
        obc = sb([obv, sb([], '1cnd', '1 e. CC')], 'eqeltrd', '%s e. CC' % OB)
        fe = sb([obc, bcc, lift(w, qc, ab), w.inst('gf2fe')], 'syl3anc', 'sum_ k e. NN %s = ( %s x. ( exp ` ( q x. %s ) ) )' % (TB, OB, qn))
        ex_ = sb([sb([bcc, lift(w, qc, ab)], 'mulcld', '( q x. %s ) e. CC' % qn)], 'efcld', '( exp ` ( q x. %s ) ) e. CC' % qn)
        e1 = sb([sb([obv], 'oveq1d', '( %s x. ( exp ` ( q x. %s ) ) ) = ( 1 x. ( exp ` ( q x. %s ) ) )' % (OB, qn, qn)), sb([ex_], 'mullidd', '( 1 x. ( exp ` ( q x. %s ) ) ) = ( exp ` ( q x. %s ) )' % (qn, qn))],
                'eqtrd', '( %s x. ( exp ` ( q x. %s ) ) ) = ( exp ` ( q x. %s ) )' % (OB, qn, qn))
        e2 = sb([sb([bcc, lift(w, qc, ab)], 'mulcomd', '( q x. %s ) = ( %s x. q )' % (qn, qn))], 'fveq2d', '( exp ` ( q x. %s ) ) = ( exp ` ( %s x. q ) )' % (qn, qn))
        pv = fvd(w, ab, 'e', 'V', '( exp ` ( %s x. e ) )' % qn, 'q', bv_, sb([], 'fvexd', '( exp ` ( %s x. q ) ) e. _V' % qn))
        eqb = sb([sb([sb([sb([v1, ss], 'eqtrd', '( %s ` q ) = sum_ k e. NN %s' % (SF3, TB)), fe], 'eqtrd', '( %s ` q ) = ( %s x. ( exp ` ( q x. %s ) ) )' % (SF3, OB, qn)),
                      sb([e1, e2], 'eqtrd', '( %s x. ( exp ` ( q x. %s ) ) ) = ( exp ` ( %s x. q ) )' % (OB, qn, qn))], 'eqtrd', '( %s ` q ) = ( exp ` ( %s x. q ) )' % (SF3, qn)), pv],
                 'eqtr4d', '( %s ` q ) = ( %s ` q )' % (SF3, EPS(qn)))
        allz = ralv(eqb, ante, S2, lambda z: '( %s ` %s ) = ( %s ` %s )' % (SF3, z, EPS(qn), z), var='q', to='z', eqf=(SF3, EPS(qn)))
        le = sa([sa([sa([L_(ec), L_(fc)], 'jca', '( E e. CC /\\ F e. CC )'), sa([sa([cn3], 'elexd', '%s e. _V' % SF3), sa([L_(vv)], 'mptexd', '%s e. _V' % EPS(qn))], 'jca',
                                                                                  '( %s e. _V /\\ %s e. _V )' % (SF3, EPS(qn)))], 'jca',
                    '( ( E e. CC /\\ F e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SF3, EPS(qn))), allz, w.inst('linteq')], 'syl2anc',
                '( %s lint <. E , F >. ) = ( %s lint <. E , F >. )' % (SF3, EPS(qn)))
        cv = sa([cv3, le], 'breqtrd', 'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) x. %s ) ) ) ~~> ( %s lint <. E , F >. )' % (QX, LIG2('k'), EPS(qn)))
        SQF = '( k e. NN |-> ( ( %s ` k ) x. %s ) )' % (QX, LIG2('k'))
        CVR = '( %s lint <. E , F >. )' % EPS(qn)
        ak = '( %s /\\ k e. NN )' % ante
        sk2 = mkst(w, ak)
        kn2 = sk2([], 'simpr', 'k e. NN')
        lic = sk2([sk2([lift(w, ec, ak), lift(w, fc, ak)], 'jca', '( E e. CC /\\ F e. CC )'), sk2([gpcn(ak, 'V', ONE, onem, idv, 'k', kn2), lift(w, sgv, ak)], 'jca',
                                                                                                    '( ( h e. V |-> ( ( %s ` h ) x. ( h ^ ( k - 1 ) ) ) ) e. %s /\\ %s C_ V )' % (ONE, VCN, S2)),
                   w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIG2('k'))
        qv2, _ = mpv(w, ak, 'l', 'NN', EXT(qn, 'l'), 'k', kn2)
        TT = '( %s x. %s )' % (EXT(qn, 'k'), LIG2('k'))
        SQFn = '( n e. NN |-> ( ( %s ` n ) x. %s ) )' % (QX, LIG2('n'))
        eqn = w.s([cg(w, '( ( %s ` k ) x. %s )' % (QX, LIG2('k')), 'k', 'n')], 'cbvmptv', '%s = %s' % (SQF, SQFn))
        cv = sa([cv, sa([sa([a1(w, ante, eqn, '%s = %s' % (SQF, SQFn))], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (SQF, SQFn))], 'breq1d',
                     '( seq 1 ( + , %s ) ~~> %s <-> seq 1 ( + , %s ) ~~> %s )' % (SQF, CVR, SQFn, CVR))], 'mpbid', 'seq 1 ( + , %s ) ~~> %s' % (SQFn, CVR))
        fvq, _ = mpv(w, ak, 'n', 'NN', '( ( %s ` n ) x. %s )' % (QX, LIG2('n')), 'k', kn2)
        SQF = SQFn
        f3_ = sk2([fvq, sk2([qv2], 'oveq1d', '( ( %s ` k ) x. %s ) = %s' % (QX, LIG2('k'), TT))], 'eqtrd', '( %s ` k ) = %s' % (SQF, TT))
        tc = sk2([extcc(ak, qn, lift(w, qc, ak), 'k', kn2), lic], 'mulcld', '%s e. CC' % TT)
        isum = sa([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, ante, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), f3_, tc, cv], 'isumclim',
                  'sum_ k e. NN %s = ( %s lint <. E , F >. )' % (TT, EPS(qn)))
        return isum, cv, tc, f3_

    # ---------------- block 2: the outer integral of the left side
    f2 = dict(ac=ec, bc=fc, sgu=sgv, gcn=onecn, hr=one_r, gb=oneb, rr=pr, rb=pb, qf=qf2, kr=kr2, k0=k02, cr=rr, c0=r0, qb=qb2)
    cn2, cv2, SF2, FT2, _ = tps_inst(w, a, {'A': 'E', 'B': 'F', 'U': 'V', 'G': ONE, 'H': '1', 'R': 'P', 'Q': Q2, 'K': K2, 'C': 'R'}, f2)

    def ident(ante, bmem, D, SFx, FTx, Gx, Qx, LIGa, LIGb, gxf, dv, LIGbc=None, cvargs=None):
        """under ab = ( ante and b e. seg ) with bmem ( ab -> b e. D ): ( SFx ` b ) = sum_ k ( ( Gx ` b ) x. ( EXT(b,k) x. LIGb(k) ) ), Qx = ( l |-> ( LIGb(l) / ! ( l - 1 ) ) )"""
        sa = mkst(w, ante)
        body = 'sum_ k e. NN ( ( %s ` k ) ` r )' % FTx
        v1, _ = mpv(w, ante, 'r', D, body, 'b', bmem, exs=a1(w, ante, w.s([], 'sumex', '%s e. _V' % body.replace('` r )', '` b )')), '%s e. _V' % body.replace('` r )', '` b )')))
        ak = '( %s /\\ k e. NN )' % ante
        sk = mkst(w, ak)
        kn = sk([], 'simpr', 'k e. NN')
        FTK = '( x e. %s |-> ( ( %s ` x ) x. ( ( %s ` k ) x. ( x ^ ( k - 1 ) ) ) ) )' % (D, Gx, Qx)
        t1, _ = mpv(w, ak, 'm', 'NN', '( x e. %s |-> ( ( %s ` x ) x. ( ( %s ` m ) x. ( x ^ ( m - 1 ) ) ) ) )' % (D, Gx, Qx), 'k', kn, exs=sk([lift(w, dv, ak)], 'mptexd', '%s e. _V' % FTK))
        t2 = fvd(w, ak, 'x', D, '( ( %s ` x ) x. ( ( %s ` k ) x. ( x ^ ( k - 1 ) ) ) )' % (Gx, Qx), 'b', lift(w, bmem, ak),
                 sk([], 'ovexd', '( ( %s ` b ) x. ( ( %s ` k ) x. ( b ^ ( k - 1 ) ) ) ) e. _V' % (Gx, Qx)))
        qv0, _ = mpv(w, ak, 'l', 'NN', '( %s / ( ! ` ( l - 1 ) ) )' % LIGbc('l'), 'k', kn)
        qv = sk([qv0, sk([cvh(ak, *cvargs, 'k')], 'oveq1d', '( %s / ( ! ` ( k - 1 ) ) ) = ( %s / ( ! ` ( k - 1 ) ) )' % (LIGbc('k'), LIGb('k')))], 'eqtrd',
                '( %s ` k ) = ( %s / ( ! ` ( k - 1 ) ) )' % (Qx, LIGb('k')))
        GB_ = '( %s ` b )' % Gx
        k1 = sk([kn, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0')
        fk = sk([k1, w.inst('faccl')], 'syl', '( ! ` ( k - 1 ) ) e. NN')
        FK = '( ! ` ( k - 1 ) )'; IF_ = '( 1 / %s )' % FK
        fkc = sk([fk], 'nncnd', '%s e. CC' % FK); fkn = sk([fk], 'nnne0d', '%s =/= 0' % FK)
        LB = LIGb('k')
        return v1, t1, t2, qv, GB_, k1, fkc, fkn, IF_, FK, LB, ak, sk, kn, FTK

    ab2 = '( %s /\\ b e. %s )' % (a, S2)
    sb2 = mkst(w, ab2)
    bv2 = sb2([lift(w, sgv, ab2), sb2([], 'simpr', 'b e. %s' % S2)], 'sseldd', 'b e. V')
    bc2 = sb2([lift(w, vcc, ab2), bv2], 'sseldd', 'b e. CC')
    v1, t1, t2, qv, GB_, k1, fkc, fkn, IF_, FK, LB, ak, sk, kn, FTK = ident(ab2, bv2, 'V', SF2, FT2, ONE, Q2, LIG2, LIG1, onef, vv, LIG1c, ('U', 'G', 'A', 'B'))
    lic1 = sk([sk([lift(w, ac, ak), lift(w, bc, ak)], 'jca', '( A e. CC /\\ B e. CC )'), sk([gpcn(ak, 'U', 'G', gmh, idu, 'k', kn), lift(w, sgu, ak)], 'jca',
                                                                                           '( %s e. %s /\\ %s C_ U )' % (GP('k'), CNU, S1)), w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIG1('k'))
    obk = onev(ak, lift(w, bv2, ak), 'b')
    BK = '( b ^ ( k - 1 ) )'
    bkc = sk([lift(w, bc2, ak), k1], 'expcld', '%s e. CC' % BK)
    ifc = sk([fkc, fkn], 'reccld', '%s e. CC' % IF_)
    dA = sk([lic1, fkc, fkn], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (LIG1('k'), FK, LIG1('k'), IF_))
    dB = sk([bkc, fkc, fkn], 'divrecd', '%s = ( %s x. %s )' % (EXT('b', 'k'), BK, IF_))
    TERM2 = '( %s x. ( ( %s ` k ) x. %s ) )' % (GB_, Q2, BK)
    x1 = sk([obk, sk([sk([qv, dA], 'eqtrd', '( %s ` k ) = ( %s x. %s )' % (Q2, LIG1('k'), IF_))], 'oveq1d', '( ( %s ` k ) x. %s ) = ( ( %s x. %s ) x. %s )' % (Q2, BK, LIG1('k'), IF_, BK))],
            'oveq12d', '%s = ( 1 x. ( ( %s x. %s ) x. %s ) )' % (TERM2, LIG1('k'), IF_, BK))
    clk = Closure(w, ak, {LIG1('k'): lic1, IF_: ifc, BK: bkc})
    rqk = ringeq(w, ak, '( 1 x. ( ( %s x. %s ) x. %s ) )' % (LIG1('k'), IF_, BK), '( ( %s x. %s ) x. %s )' % (BK, IF_, LIG1('k')), clk)
    x2 = sk([dB], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (EXT('b', 'k'), LIG1('k'), BK, IF_, LIG1('k')))
    xt = sk([sk([x1, rqk], 'eqtrd', '%s = ( ( %s x. %s ) x. %s )' % (TERM2, BK, IF_, LIG1('k'))), x2], 'eqtr4d', '%s = ( %s x. %s )' % (TERM2, EXT('b', 'k'), LIG1('k')))
    tk = sk([sk([sk([t1], 'fveq1d', '( ( %s ` k ) ` b ) = ( %s ` b )' % (FT2, FTK)), t2], 'eqtrd', '( ( %s ` k ) ` b ) = %s' % (FT2, TERM2)), xt], 'eqtrd',
            '( ( %s ` k ) ` b ) = ( %s x. %s )' % (FT2, EXT('b', 'k'), LIG1('k')))
    ss = sb2([tk], 'sumeq2dv', 'sum_ k e. NN ( ( %s ` k ) ` b ) = sum_ k e. NN ( %s x. %s )' % (FT2, EXT('b', 'k'), LIG1('k')))
    b1 = block1(ab2, 'b', bv2)
    lv = fvd(w, ab2, 'e', 'V', '( %s lint <. A , B >. )' % PHI_('e'), 'b', bv2, sb2([], 'ovexd', '( %s lint <. A , B >. ) e. _V' % PHI_('b')))
    eqb2 = sb2([sb2([sb2([v1, ss], 'eqtrd', '( %s ` b ) = sum_ k e. NN ( %s x. %s )' % (SF2, EXT('b', 'k'), LIG1('k'))), b1], 'eqtrd', '( %s ` b ) = ( %s lint <. A , B >. )' % (SF2, PHI_('b'))),
                lv], 'eqtr4d', '( %s ` b ) = ( %s ` b )' % (SF2, LHSF))
    allz2 = ralv(eqb2, a, S2, lambda z: '( %s ` %s ) = ( %s ` %s )' % (SF2, z, LHSF, z), var='b', to='z', eqf=(SF2, LHSF))
    le2 = st([st([st([ec, fc], 'jca', '( E e. CC /\\ F e. CC )'), st([st([cn2], 'elexd', '%s e. _V' % SF2), st([vv], 'mptexd', '%s e. _V' % LHSF)], 'jca', '( %s e. _V /\\ %s e. _V )' % (SF2, LHSF))],
                 'jca', '( ( E e. CC /\\ F e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SF2, LHSF)), allz2, w.inst('linteq')], 'syl2anc',
             '( %s lint <. E , F >. ) = ( %s lint <. E , F >. )' % (SF2, LHSF))
    SEQ2 = '( k e. NN |-> ( ( %s ` k ) x. %s ) )' % (Q2, LIG2('k'))
    seqL = st([cv2, le2], 'breqtrd', 'seq 1 ( + , %s ) ~~> ( %s lint <. E , F >. )' % (SEQ2, LHSF))

    # ---------------- block 4: the outer integral of the right side
    f4 = dict(ac=ac, bc=bc, sgu=sgu, gcn=gcn, hr=hr, gb=gb, rr=rr, rb=rb, qf=qf4, kr=kr4, k0=k04, cr=pr, c0=p0, qb=qb4)
    cn4, cv4, SF4, FT4, _ = tps_inst(w, a, {'Q': Q4, 'K': K4, 'C': 'P'}, f4)
    ab4 = '( %s /\\ b e. %s )' % (a, S1)
    sb4 = mkst(w, ab4)
    bu4 = sb4([lift(w, sgu, ab4), sb4([], 'simpr', 'b e. %s' % S1)], 'sseldd', 'b e. U')
    bc4 = sb4([lift(w, ucc, ab4), bu4], 'sseldd', 'b e. CC')
    v1, t1, t2, qv, GB_, k1, fkc, fkn, IF_, FK, LB, ak, sk, kn, FTK = ident(ab4, bu4, 'U', SF4, FT4, 'G', Q4, LIG1, LIG2, gff, uv, LIG2c, ('V', ONE, 'E', 'F'))
    lic2 = sk([sk([lift(w, ec, ak), lift(w, fc, ak)], 'jca', '( E e. CC /\\ F e. CC )'), sk([gpcn(ak, 'V', ONE, onem, idv, 'k', kn), lift(w, sgv, ak)], 'jca',
                                                                                           '( ( h e. V |-> ( ( %s ` h ) x. ( h ^ ( k - 1 ) ) ) ) e. %s /\\ %s C_ V )' % (ONE, VCN, S2)),
                w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIG2('k'))
    BK = '( b ^ ( k - 1 ) )'
    bkc = sk([lift(w, bc4, ak), k1], 'expcld', '%s e. CC' % BK)
    ifc = sk([fkc, fkn], 'reccld', '%s e. CC' % IF_)
    gbc = sk([lift(w, gff, ak), lift(w, bu4, ak)], 'ffvelcdmd', '( G ` b ) e. CC')
    dA = sk([lic2, fkc, fkn], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (LIG2('k'), FK, LIG2('k'), IF_))
    dB = sk([bkc, fkc, fkn], 'divrecd', '%s = ( %s x. %s )' % (EXT('b', 'k'), BK, IF_))
    TERM4 = '( ( G ` b ) x. ( ( %s ` k ) x. %s ) )' % (Q4, BK)
    TT4 = '( ( G ` b ) x. ( %s x. %s ) )' % (EXT('b', 'k'), LIG2('k'))
    y1 = sk([sk([sk([qv, dA], 'eqtrd', '( %s ` k ) = ( %s x. %s )' % (Q4, LIG2('k'), IF_))], 'oveq1d', '( ( %s ` k ) x. %s ) = ( ( %s x. %s ) x. %s )' % (Q4, BK, LIG2('k'), IF_, BK))],
            'oveq2d', '%s = ( ( G ` b ) x. ( ( %s x. %s ) x. %s ) )' % (TERM4, LIG2('k'), IF_, BK))
    clk4 = Closure(w, ak, {LIG2('k'): lic2, IF_: ifc, BK: bkc, '( G ` b )': gbc})
    rq4 = ringeq(w, ak, '( ( G ` b ) x. ( ( %s x. %s ) x. %s ) )' % (LIG2('k'), IF_, BK), '( ( G ` b ) x. ( ( %s x. %s ) x. %s ) )' % (BK, IF_, LIG2('k')), clk4)
    y2 = sk([sk([dB], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (EXT('b', 'k'), LIG2('k'), BK, IF_, LIG2('k')))], 'oveq2d',
            '%s = ( ( G ` b ) x. ( ( %s x. %s ) x. %s ) )' % (TT4, BK, IF_, LIG2('k')))
    yt = sk([sk([y1, rq4], 'eqtrd', '%s = ( ( G ` b ) x. ( ( %s x. %s ) x. %s ) )' % (TERM4, BK, IF_, LIG2('k'))), y2], 'eqtr4d', '%s = %s' % (TERM4, TT4))
    tk4 = sk([sk([sk([t1], 'fveq1d', '( ( %s ` k ) ` b ) = ( %s ` b )' % (FT4, FTK)), t2], 'eqtrd', '( ( %s ` k ) ` b ) = %s' % (FT4, TERM4)), yt], 'eqtrd',
             '( ( %s ` k ) ` b ) = %s' % (FT4, TT4))
    ss4 = sb4([tk4], 'sumeq2dv', 'sum_ k e. NN ( ( %s ` k ) ` b ) = sum_ k e. NN %s' % (FT4, TT4))
    isum3, cv3, tc3, f33 = block3(ab4, 'b', bu4)
    # the series with the factor ( G ` b )
    QX3 = '( l e. NN |-> %s )' % EXT('b', 'l')
    SQ3 = '( n e. NN |-> ( ( %s ` n ) x. %s ) )' % (QX3, LIG2('n'))
    TTn = TT4.replace('( k - 1 )', '( n - 1 )')
    GFn = '( n e. NN |-> %s )' % TTn
    akk = '( %s /\\ k e. NN )' % ab4
    skk = mkst(w, akk)
    knn = skk([], 'simpr', 'k e. NN')
    gv, _ = mpv(w, akk, 'n', 'NN', TTn, 'k', knn)
    g7 = skk([gv, skk([f33], 'oveq2d', '( ( G ` b ) x. ( %s ` k ) ) = %s' % (SQ3, TT4))], 'eqtr4d', '( %s ` k ) = ( ( G ` b ) x. ( %s ` k ) )' % (GFn, SQ3))
    f3c = skk([f33, tc3], 'eqeltrd', '( %s ` k ) e. CC' % SQ3)
    gbc4 = sb4([lift(w, gff, ab4), bu4], 'ffvelcdmd', '( G ` b ) e. CC')
    PSIb = '( %s lint <. E , F >. )' % EPS('b')
    im = sb4([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, ab4, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), gbc4, cv3, f3c, g7], 'isermulc2', 'seq 1 ( + , %s ) ~~> ( ( G ` b ) x. %s )' % (GFn, PSIb))
    t4c = skk([lift(w, gbc4, akk), tc3], 'mulcld', '%s e. CC' % TT4)
    isum4 = sb4([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, ab4, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), gv, t4c, im], 'isumclim', 'sum_ k e. NN %s = ( ( G ` b ) x. %s )' % (TT4, PSIb))
    rv = fvd(w, ab4, 'x', 'U', '( ( G ` x ) x. %s )' % PSI_('x'), 'b', bu4, sb4([], 'ovexd', '( ( G ` b ) x. %s ) e. _V' % PSI_('b')))
    eqb4 = sb4([sb4([sb4([v1, ss4], 'eqtrd', '( %s ` b ) = sum_ k e. NN %s' % (SF4, TT4)), isum4], 'eqtrd', '( %s ` b ) = ( ( G ` b ) x. %s )' % (SF4, PSIb)), rv], 'eqtr4d',
               '( %s ` b ) = ( %s ` b )' % (SF4, RHSF))
    allz4 = ralv(eqb4, a, S1, lambda z: '( %s ` %s ) = ( %s ` %s )' % (SF4, z, RHSF, z), var='b', to='z', eqf=(SF4, RHSF))
    le4 = st([st([st([ac, bc], 'jca', '( A e. CC /\\ B e. CC )'), st([st([cn4], 'elexd', '%s e. _V' % SF4), st([uv], 'mptexd', '%s e. _V' % RHSF)], 'jca', '( %s e. _V /\\ %s e. _V )' % (SF4, RHSF))],
                 'jca', '( ( A e. CC /\\ B e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SF4, RHSF)), allz4, w.inst('linteq')], 'syl2anc',
             '( %s lint <. A , B >. ) = ( %s lint <. A , B >. )' % (SF4, RHSF))
    SEQ4 = '( k e. NN |-> ( ( %s ` k ) x. %s ) )' % (Q4, LIG1('k'))
    seqR = st([cv4, le4], 'breqtrd', 'seq 1 ( + , %s ) ~~> ( %s lint <. A , B >. )' % (SEQ4, RHSF))
    # ---------------- the two series have the same terms
    af = '( %s /\\ k e. NN )' % a
    sf = mkst(w, af)
    kf = sf([], 'simpr', 'k e. NN')
    k1f = sf([kf, w.inst('nnm1nn0')], 'syl', '( k - 1 ) e. NN0')
    fkf = sf([k1f, w.inst('faccl')], 'syl', '( ! ` ( k - 1 ) ) e. NN')
    FKc = sf([fkf], 'nncnd', '( ! ` ( k - 1 ) ) e. CC'); FKn = sf([fkf], 'nnne0d', '( ! ` ( k - 1 ) ) =/= 0')
    IFk = '( 1 / ( ! ` ( k - 1 ) ) )'
    l1c = sf([sf([lift(w, ac, af), lift(w, bc, af)], 'jca', '( A e. CC /\\ B e. CC )'), sf([gpcn(af, 'U', 'G', gmh, idu, 'k', kf), lift(w, sgu, af)], 'jca',
                                                                                           '( %s e. %s /\\ %s C_ U )' % (GP('k'), CNU, S1)), w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIG1('k'))
    l2c = sf([sf([lift(w, ec, af), lift(w, fc, af)], 'jca', '( E e. CC /\\ F e. CC )'), sf([gpcn(af, 'V', ONE, onem, idv, 'k', kf), lift(w, sgv, af)], 'jca',
                                                                                           '( ( h e. V |-> ( ( %s ` h ) x. ( h ^ ( k - 1 ) ) ) ) e. %s /\\ %s C_ V )' % (ONE, VCN, S2)),
               w.inst('lintcl')], 'syl2anc', '%s e. CC' % LIG2('k'))
    q2v0, _ = mpv(w, af, 'l', 'NN', '( %s / ( ! ` ( l - 1 ) ) )' % LIG1c('l'), 'k', kf)
    q4v0, _ = mpv(w, af, 'l', 'NN', '( %s / ( ! ` ( l - 1 ) ) )' % LIG2c('l'), 'k', kf)
    q2v = sf([q2v0, sf([cvh(af, 'U', 'G', 'A', 'B', 'k')], 'oveq1d', '( %s / ( ! ` ( k - 1 ) ) ) = ( %s / ( ! ` ( k - 1 ) ) )' % (LIG1c('k'), LIG1('k')))], 'eqtrd',
             '( %s ` k ) = ( %s / ( ! ` ( k - 1 ) ) )' % (Q2, LIG1('k')))
    q4v = sf([q4v0, sf([cvh(af, 'V', ONE, 'E', 'F', 'k')], 'oveq1d', '( %s / ( ! ` ( k - 1 ) ) ) = ( %s / ( ! ` ( k - 1 ) ) )' % (LIG2c('k'), LIG2('k')))], 'eqtrd',
             '( %s ` k ) = ( %s / ( ! ` ( k - 1 ) ) )' % (Q4, LIG2('k')))
    d2 = sf([l1c, FKc, FKn], 'divrecd', '( %s / ( ! ` ( k - 1 ) ) ) = ( %s x. %s )' % (LIG1('k'), LIG1('k'), IFk))
    d4 = sf([l2c, FKc, FKn], 'divrecd', '( %s / ( ! ` ( k - 1 ) ) ) = ( %s x. %s )' % (LIG2('k'), LIG2('k'), IFk))
    clf = Closure(w, af, {LIG1('k'): l1c, LIG2('k'): l2c, IFk: sf([FKc, FKn], 'reccld', '%s e. CC' % IFk)})
    rqf = ringeq(w, af, '( ( %s x. %s ) x. %s )' % (LIG1('k'), IFk, LIG2('k')), '( ( %s x. %s ) x. %s )' % (LIG2('k'), IFk, LIG1('k')), clf)
    tq = sf([sf([sf([sf([q2v, d2], 'eqtrd', '( %s ` k ) = ( %s x. %s )' % (Q2, LIG1('k'), IFk))], 'oveq1d', '( ( %s ` k ) x. %s ) = ( ( %s x. %s ) x. %s )' % (Q2, LIG2('k'), LIG1('k'), IFk, LIG2('k'))),
                 rqf], 'eqtrd', '( ( %s ` k ) x. %s ) = ( ( %s x. %s ) x. %s )' % (Q2, LIG2('k'), LIG2('k'), IFk, LIG1('k'))),
             sf([sf([q4v, d4], 'eqtrd', '( %s ` k ) = ( %s x. %s )' % (Q4, LIG2('k'), IFk))], 'oveq1d', '( ( %s ` k ) x. %s ) = ( ( %s x. %s ) x. %s )' % (Q4, LIG1('k'), LIG2('k'), IFk, LIG1('k')))],
            'eqtr4d', '( ( %s ` k ) x. %s ) = ( ( %s ` k ) x. %s )' % (Q2, LIG2('k'), Q4, LIG1('k')))
    meq = st([tq], 'mpteq2dva', '%s = %s' % (SEQ2, SEQ4))
    sL2 = st([seqL, st([st([meq], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (SEQ2, SEQ4))], 'breq1d',
                       '( seq 1 ( + , %s ) ~~> ( %s lint <. E , F >. ) <-> seq 1 ( + , %s ) ~~> ( %s lint <. E , F >. ) )' % (SEQ2, LHSF, SEQ4, LHSF))], 'mpbid',
             'seq 1 ( + , %s ) ~~> ( %s lint <. E , F >. )' % (SEQ4, LHSF))
    EQ = split_imp(S_['gf2fub'])[1].split(' /\\ ', 1)[1][:-2]
    fin = st([sL2, seqR, w.inst('climuni')], 'syl2anc', EQ)
    # continuity of the left integrand when V is the segment itself
    aV = '( %s /\\ ( E cseg F ) = V )' % a
    sV = mkst(w, aV)
    abV = '( %s /\\ b e. V )' % aV
    sbV = mkst(w, abV)
    bs2 = sbV([sbV([], 'simpr', 'b e. V'), lift(w, sV([], 'simpr', '( E cseg F ) = V'), abV)], 'eleqtrrd', 'b e. %s' % S2)
    tr_ = sbV([sbV([], 'simpll', a), bs2], 'jca', ab2)
    eqV = sbV([tr_, eqb2], 'syl', '( %s ` b ) = ( %s ` b )' % (SF2, LHSF))
    sffn = sV([sV([lift(w, cn2, aV), w.inst('cncff')], 'syl', '%s : V --> CC' % SF2)], 'ffnd', '%s Fn V' % SF2)
    aeV = '( %s /\\ e e. V )' % aV
    lfn = sV([mkst(w, aeV)([], 'ovexd', '( %s lint <. A , B >. ) e. _V' % PHI_('e'))], 'fnmptd', '%s Fn V' % LHSF)
    feq = sV([sffn, lfn, eqV], 'eqfnfvd', '%s = %s' % (SF2, LHSF))
    lcn = sV([lift(w, cn2, aV), sV([feq], 'eleq1d', '( %s e. ( V -cn-> CC ) <-> %s e. ( V -cn-> CC ) )' % (SF2, LHSF))], 'mpbid', '%s e. ( V -cn-> CC )' % LHSF)
    imp = st([lcn], 'ex', '( ( E cseg F ) = V -> %s e. ( V -cn-> CC ) )' % LHSF)
    w.qed([st([imp, fin], 'jca', split_imp(S_['gf2fub'])[1])], 'idi', S_['gf2fub'])
    return w


S_['gf2hl'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ A < B ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A [,] B ) C_ D ) ) -> '
               '( F lint <. A , B >. ) = S. ( A (,) B ) ( F ` u ) _d u )')


def gf2hl():
    w = W('gf2hl', 'A segment integral along a real interval is the Lebesgue integral: ` int_<. A , B >. F = S. ( A (,) B ) F ( u ) du ` (~ lintval , ~ z6aff ).')
    a = split_imp(S_['gf2hl'])[0]
    st = mkst(w, a)
    ar = st([], 'simplll', 'A e. RR'); br = st([], 'simpllr', 'B e. RR'); ab = st([], 'simplr', 'A < B')
    fcn = st([], 'simprl', 'F e. ( D -cn-> CC )'); ssd = st([], 'simprr', '( A [,] B ) C_ D')
    I = '( A [,] B )'; H = '( F |` %s )' % I
    hcn = st([fcn, st([ssd, w.inst('rescncf')], 'syl', '( F e. ( D -cn-> CC ) -> %s e. ( %s -cn-> CC ) )' % (H, I))], 'mpd', '%s e. ( %s -cn-> CC )' % (H, I))
    za = st([st([st([ar, br], 'jca', '( A e. RR /\\ B e. RR )'), ab], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ A < B )'), hcn, w.inst('z6aff')], 'syl2anc',
            'S. ( A (,) B ) ( %s ` u ) _d u = S. ( 0 (,) 1 ) ( ( %s ` ( A + ( t x. ( B - A ) ) ) ) x. ( B - A ) ) _d t' % (H, H))
    au = '( %s /\\ u e. ( A (,) B ) )' % a
    su = mkst(w, au)
    ui = su([a1(w, au, w.s([], 'ioossicc', '( A (,) B ) C_ %s' % I), '( A (,) B ) C_ %s' % I), su([], 'simpr', 'u e. ( A (,) B )')], 'sseldd', 'u e. %s' % I)
    e1 = st([su([ui, w.inst('fvres')], 'syl', '( %s ` u ) = ( F ` u )' % H)], 'itgeq2dv', 'S. ( A (,) B ) ( %s ` u ) _d u = S. ( A (,) B ) ( F ` u ) _d u' % H)
    at = '( %s /\\ t e. ( 0 (,) 1 ) )' % a
    sat = mkst(w, at)
    tin = sat([], 'simpr', 't e. ( 0 (,) 1 )')
    tel = sat([a1(w, at, w.s([], '0xr', '0 e. RR*'), '0 e. RR*'), a1(w, at, w.s([], '1xr', '1 e. RR*'), '1 e. RR*'), w.inst('elioo2')], 'syl2anc',
              '( t e. ( 0 (,) 1 ) <-> ( t e. RR /\\ 0 < t /\\ t < 1 ) )')
    tt = sat([tin, tel], 'mpbid', '( t e. RR /\\ 0 < t /\\ t < 1 )')
    tr = sat([tt], 'simp1d', 't e. RR'); t0 = sat([tt], 'simp2d', '0 < t'); t1 = sat([tt], 'simp3d', 't < 1')
    BA = '( B - A )'
    bar = sat([lift(w, br, at), lift(w, ar, at)], 'resubcld', '%s e. RR' % BA)
    ba0 = lin.linarith(w, at, [lift(w, ab, at)], '0 <_ %s' % BA, leaves={'A': lift(w, ar, at), 'B': lift(w, br, at), BA: bar})
    TB = '( t x. %s )' % BA
    tbr = sat([tr, bar], 'remulcld', '%s e. RR' % TB)
    tb0 = sat([tr, bar, lin.linarith(w, at, [t0], '0 <_ t', leaves={'t': tr}), ba0], 'mulge0d', '0 <_ %s' % TB)
    tb1 = sat([tr, sat([], '1red', '1 e. RR'), bar, ba0, lin.linarith(w, at, [t1], 't <_ 1', leaves={'t': tr})], 'lemul1ad', '%s <_ ( 1 x. %s )' % (TB, BA))
    P_ = '( A + %s )' % TB
    pr_ = sat([lift(w, ar, at), tbr], 'readdcld', '%s e. RR' % P_)
    lv = {'A': lift(w, ar, at), 'B': lift(w, br, at), TB: tbr}
    tb1b = sat([tb1, sat([sat([bar], 'recnd', '%s e. CC' % BA)], 'mullidd', '( 1 x. %s ) = %s' % (BA, BA))], 'breqtrd', '%s <_ %s' % (TB, BA))
    pa = lin.linarith(w, at, [tb0], 'A <_ %s' % P_, leaves=lv)
    pb = lin.linarith(w, at, [tb1b], '%s <_ B' % P_, leaves=lv)
    pin = sat([sat([pr_, pa, pb], '3jca', '( %s e. RR /\\ A <_ %s /\\ %s <_ B )' % (P_, P_, P_)), sat([lift(w, ar, at), lift(w, br, at), w.inst('elicc2')], 'syl2anc',
                                                                                                    '( %s e. %s <-> ( %s e. RR /\\ A <_ %s /\\ %s <_ B ) )' % (P_, I, P_, P_, P_))],
              'mpbird', '%s e. %s' % (P_, I))
    e2 = st([sat([sat([pin, w.inst('fvres')], 'syl', '( %s ` %s ) = ( F ` %s )' % (H, P_, P_))], 'oveq1d', '( ( %s ` %s ) x. %s ) = ( ( F ` %s ) x. %s )' % (H, P_, BA, P_, BA))], 'itgeq2dv',
            'S. ( 0 (,) 1 ) ( ( %s ` %s ) x. %s ) _d t = S. ( 0 (,) 1 ) ( ( F ` %s ) x. %s ) _d t' % (H, P_, BA, P_, BA))
    lv_ = st([st([fcn], 'elexd', 'F e. _V'), st([ar], 'recnd', 'A e. CC'), st([br], 'recnd', 'B e. CC'), w.inst('lintval')], 'syl3anc',
             '( F lint <. A , B >. ) = S. ( 0 (,) 1 ) ( ( F ` %s ) x. %s ) _d t' % (P_, BA))
    fin = st([lv_, st([st([e1], 'eqcomd', 'S. ( A (,) B ) ( F ` u ) _d u = S. ( A (,) B ) ( %s ` u ) _d u' % H), st([za, e2], 'eqtrd',
                                                                                                                 'S. ( A (,) B ) ( %s ` u ) _d u = S. ( 0 (,) 1 ) ( ( F ` %s ) x. %s ) _d t' % (H, P_, BA))],
                  'eqtrd', 'S. ( A (,) B ) ( F ` u ) _d u = S. ( 0 (,) 1 ) ( ( F ` %s ) x. %s ) _d t' % (P_, BA))], 'eqtr4d', split_imp(S_['gf2hl'])[1])
    w.qed([fin], 'idi', S_['gf2hl'])
    return w


DG = '( CC \\ ( ZZ \\ NN ) )'
GYF = lambda Y: '( w e. %s |-> ( ( _G ` w ) x. ( %s ^c -u w ) ) )' % (DG, Y)
LIt = lambda G, c, t: '( %s lint <. ( %s + ( _i x. -u %s ) ) , ( %s + ( _i x. %s ) ) >. )' % (G, c, t, c, t)
TPI = '( 2 x. ( _i x. _pi ) )'
MYF = lambda Y: '( ; 6 4 x. ( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) ) )' % (Y, Y)
BND = lambda M, t: '( ( ( 8 x. %s ) / ( log ` 2 ) ) x. ( 2 ^c -u ( %s / 4 ) ) )' % (M, t)
S_['gf2mt1'] = ('( ( Y e. RR+ /\\ ( T e. RR /\\ 1 <_ T ) ) -> ( abs ` ( %s - ( %s x. ( exp ` -u Y ) ) ) ) <_ %s )'
                % (LIt(GYF('Y'), '1', 'T'), TPI, BND(MYF('Y'), 'T')))


def gf2mt1():
    w = W('gf2mt1', 'The Mellin identity on the line ` Re w = 1 ` with its tail: ` | int_( 1 - i T )^( 1 + i T ) G ( w ) Y ^ -w dw - 2 pi i e ^ -Y | <_ ( 8 M / log 2 ) 2 ^ ( - T / 4 ) ` , '
                     '` M = 64 ( Y ^ -1/2 + Y ^ -3 ) ` (~ z6mellin , ~ z6vlcvg , ~ z6gyr ).')
    a = split_imp(S_['gf2mt1'])[0]
    st = mkst(w, a)
    yrp = st([], 'simpl', 'Y e. RR+'); tr = st([], 'simprl', 'T e. RR'); t1 = st([], 'simprr', '1 <_ T')
    G = GYF('Y')
    gh = st([yrp, w.inst('z6gyhol')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (G, DG, DG, G))
    gcn = st([gh], 'simpld', '%s e. ( %s -cn-> CC )' % (G, DG))
    au = '( %s /\\ u e. RR )' % a
    su = mkst(w, au)
    ur = su([], 'simpr', 'u e. RR')
    U = '( 1 + ( _i x. u ) )'
    uc = su([su([], '1cnd', '1 e. CC'), su([a1(w, au, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), su([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % U)
    reu = su([su([], '1red', '1 e. RR'), ur, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % U)
    imu = su([su([], '1red', '1 e. RR'), ur, w.inst('crim')], 'syl2anc', '( Im ` %s ) = u' % U)
    ne0 = su([reu, a1(w, au, w.s([], 'ax-1ne0', '1 =/= 0'), '1 =/= 0')], 'eqnetrd', '( Re ` %s ) =/= 0' % U)
    z0 = a1(w, au, w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (U, U)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (U, U)),
            '( %s = 0 -> ( Re ` %s ) = 0 )' % (U, U))
    un0 = su([ne0, su([z0], 'necon3d', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (U, U))], 'mpd', '%s =/= 0' % U)
    m1 = su([lin.linarith(w, au, [reu], '-u 1 < ( Re ` %s )' % U, leaves={'( Re ` %s )' % U: su([uc], 'recld', '( Re ` %s ) e. RR' % U)})], 'idi', '-u 1 < ( Re ` %s )' % U)
    udg = su([su([uc, su([m1, un0], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (U, U))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (U, U, U)), w.inst('z6rdg')],
             'syl', '%s e. %s' % (U, DG))
    ald = st([udg], 'ralrimiva', 'A. u e. RR %s e. %s' % (U, DG))
    MY = MYF('Y')
    gv, _ = mpv(w, au, 'w', DG, '( ( _G ` w ) x. ( Y ^c -u w ) )', U, udg)
    h1 = su([a1(w, au, num.le_lit(w, '( 1 / 2 )', '1'), '( 1 / 2 ) <_ 1'), reu], 'breqtrrd', '( 1 / 2 ) <_ ( Re ` %s )' % U)
    h2 = su([reu, a1(w, au, num.le_lit(w, '1', '3'), '1 <_ 3')], 'eqbrtrd', '( Re ` %s ) <_ 3' % U)
    gy = su([lift(w, yrp, au), su([uc, su([h1, h2], 'jca', '( ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (U, U))], 'jca',
                                   '( %s e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) )' % (U, U, U)), w.inst('z6gyr')], 'syl2anc',
            '( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) )' % (U, U, MY, U))
    rw_ = su([su([su([su([imu], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % U)], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % U)], 'negeqd',
                  '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % U)], 'oveq2d', '( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) = ( 2 ^c -u ( ( abs ` u ) / 4 ) )' % U)
    gy2 = su([su([su([gv], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) )' % (G, U, U, U)), gy], 'eqbrtrd',
                  '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) )' % (G, U, MY, U)), su([rw_], 'oveq2d',
                                                                                                                     '( %s x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) ) = ( %s x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) )' % (MY, U, MY))],
             'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) )' % (G, U, MY))
    gy3 = su([gy2], 'a1d', '( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) )' % (G, U, MY))
    alb = st([gy3], 'ralrimiva', 'A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) )' % (G, U, MY))
    myr = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), st([st([st([yrp, litr(w, a, '-u ( 1 / 2 )')], 'rpcxpcld', '( Y ^c -u ( 1 / 2 ) ) e. RR+')], 'rpred', '( Y ^c -u ( 1 / 2 ) ) e. RR'),
                                                                st([st([yrp, litr(w, a, '-u 3')], 'rpcxpcld', '( Y ^c -u 3 ) e. RR+')], 'rpred', '( Y ^c -u 3 ) e. RR')], 'readdcld',
                                                               '( ( Y ^c -u ( 1 / 2 ) ) + ( Y ^c -u 3 ) ) e. RR')], 'remulcld', '%s e. RR' % MY)
    VLF = '( t e. RR+ |-> %s )' % LIt(G, '1', 't')
    VL = '( ~~>r ` %s )' % VLF
    TAIL = 'A. t e. RR+ ( 1 <_ t -> ( abs ` ( %s - %s ) ) <_ %s )' % (VL, LIt(G, '1', 't'), BND(MY, 't'))
    vc = st([st([st([], '1red', '1 e. RR'), st([gcn, ald], 'jca', '( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s )' % (G, DG, U, DG))], 'jca',
                '( 1 e. RR /\\ ( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s ) )' % (G, DG, U, DG)),
             st([st([myr, a1(w, a, w.s([], '1rp', '1 e. RR+'), '1 e. RR+')], 'jca', '( %s e. RR /\\ 1 e. RR+ )' % MY), alb], 'jca',
                '( ( %s e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % (MY, G, U, MY)),
             w.inst('z6vlcvg')], 'syl2anc', '( %s ~~>r %s /\\ %s )' % (VLF, VL, TAIL))
    rl = st([vc], 'simpld', '%s ~~>r %s' % (VLF, VL)); tail = st([vc], 'simprd', TAIL)
    E_ = '( %s x. ( exp ` -u Y ) )' % TPI
    mel = st([yrp, st([st([], '1red', '1 e. RR'), st([a1(w, a, num.le_lit(w, '( 1 / 2 )', '1'), '( 1 / 2 ) <_ 1'), a1(w, a, num.le_lit(w, '1', '3'), '1 <_ 3')], 'jca',
                                                     '( ( 1 / 2 ) <_ 1 /\\ 1 <_ 3 )')], 'jca', '( 1 e. RR /\\ ( ( 1 / 2 ) <_ 1 /\\ 1 <_ 3 ) )'), w.inst('z6mellin')], 'syl2anc',
              '%s ~~>r %s' % (VLF, E_))
    fd = st([mel, w.inst('rlimf')], 'syl', '%s : dom %s --> CC' % (VLF, VLF))
    dm = a1(w, a, w.s([w.s([w.s([], 'ovex', '%s e. _V' % LIt(G, '1', 't'))], 'rgenw', 'A. t e. RR+ %s e. _V' % LIt(G, '1', 't')), w.inst('dmmptg')], 'ax-mp', 'dom %s = RR+' % VLF), 'dom %s = RR+' % VLF)
    ff = st([fd, st([dm], 'feq2d', '( %s : dom %s --> CC <-> %s : RR+ --> CC )' % (VLF, VLF, VLF))], 'mpbid', '%s : RR+ --> CC' % VLF)
    vv = st([ff, a1(w, a, w.s([], 'rpsup', 'sup ( RR+ , RR* , < ) = +oo'), 'sup ( RR+ , RR* , < ) = +oo'), rl, mel], 'rlimuni', '%s = %s' % (VL, E_))
    # replace the limit by its value under the quantifier, then instantiate the tail at T
    trp = st([tr, lin.linarith(w, a, [t1], '0 < T', leaves={'T': tr})], 'elrpd', 'T e. RR+')
    at_ = '( %s /\\ t e. RR+ )' % a
    stt = mkst(w, at_)
    Pv = lambda X, t: '( 1 <_ %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (t, X, LIt(G, '1', t), BND(MY, t))
    b1 = stt([stt([stt([lift(w, vv, at_)], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (VL, LIt(G, '1', 't'), E_, LIt(G, '1', 't')))], 'fveq2d',
                  '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (VL, LIt(G, '1', 't'), E_, LIt(G, '1', 't')))], 'breq1d',
             '( ( abs ` ( %s - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s )' % (VL, LIt(G, '1', 't'), BND(MY, 't'), E_, LIt(G, '1', 't'), BND(MY, 't')))
    b2 = stt([b1], 'imbi2d', '( %s <-> %s )' % (Pv(VL, 't'), Pv(E_, 't')))
    b3 = st([b2], 'ralbidva', '( A. t e. RR+ %s <-> A. t e. RR+ %s )' % (Pv(VL, 't'), Pv(E_, 't')))
    tail2 = st([tail, b3], 'mpbid', 'A. t e. RR+ %s' % Pv(E_, 't'))
    e1 = w.s([], 'breq2', '( t = T -> ( 1 <_ t <-> 1 <_ T ) )')
    idt = w.s([], 'id', '( t = T -> t = T )')
    c1, _ = w.congr(LIt(G, '1', 't'), {'t': 'T'}, 't = T', {'t': idt})
    c2, _ = w.congr(BND(MY, 't'), {'t': 'T'}, 't = T', {'t': idt})
    c3 = w.s([c1], 'oveq2d', '( t = T -> ( %s - %s ) = ( %s - %s ) )' % (E_, LIt(G, '1', 't'), E_, LIt(G, '1', 'T')))
    c4 = w.s([c3], 'fveq2d', '( t = T -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (E_, LIt(G, '1', 't'), E_, LIt(G, '1', 'T')))
    c5 = w.s([c4, c2], 'breq12d', '( t = T -> ( ( abs ` ( %s - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s ) )' % (E_, LIt(G, '1', 't'), BND(MY, 't'), E_, LIt(G, '1', 'T'), BND(MY, 'T')))
    c6 = w.s([e1, c5], 'imbi12d', '( t = T -> ( %s <-> %s ) )' % (Pv(E_, 't'), Pv(E_, 'T')))
    tT = st([c6, tail2, trp], 'rspcdva', Pv(E_, 'T'))
    tb2 = st([t1, tT], 'mpd', '( abs ` ( %s - %s ) ) <_ %s' % (E_, LIt(G, '1', 'T'), BND(MY, 'T')))
    ltc = st([ff, trp], 'ffvelcdmd', '( %s ` T ) e. CC' % VLF)
    lv_, _ = mpv(w, a, 't', 'RR+', LIt(G, '1', 't'), 'T', trp)
    ltc2 = st([st([lv_], 'eqcomd', '%s = ( %s ` T )' % (LIt(G, '1', 'T'), VLF)), ltc], 'eqeltrd', '%s e. CC' % LIt(G, '1', 'T'))
    ec = st([st([a1(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), a1(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mulcld',
                                                                        '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI),
             st([st([st([yrp], 'rpcnd', 'Y e. CC')], 'negcld', '-u Y e. CC')], 'efcld', '( exp ` -u Y ) e. CC')], 'mulcld', '%s e. CC' % E_)
    asub = st([ec, ltc2, w.inst('abssub')], 'syl2anc', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (E_, LIt(G, '1', 'T'), LIt(G, '1', 'T'), E_))
    fin = st([st([asub], 'eqcomd', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (LIt(G, '1', 'T'), E_, E_, LIt(G, '1', 'T'))), tb2], 'eqbrtrd', split_imp(S_['gf2mt1'])[1])
    w.qed([fin], 'idi', S_['gf2mt1'])
    return w


S_['gf2segb'] = '( ( A e. CC /\\ B e. CC ) -> A. v e. ( A cseg B ) ( abs ` v ) <_ ( ( abs ` A ) + ( abs ` ( B - A ) ) ) )'
S_['gf2csegr'] = '( ( A e. RR /\\ B e. RR /\\ A < B ) -> ( A cseg B ) = ( A [,] B ) )'


def gf2segb():
    w = W('gf2segb', 'A segment lies in the disc of radius ` | A | + | B - A | ` (~ csegel , ~ abstrid ).')
    a = '( A e. CC /\\ B e. CC )'
    st = mkst(w, a)
    ac = st([], 'simpl', 'A e. CC'); bc = st([], 'simpr', 'B e. CC')
    av = '( %s /\\ v e. ( A cseg B ) )' % a
    sv = mkst(w, av)
    ex = sv([sv([], 'simpr', 'v e. ( A cseg B )'), sv([lift(w, ac, av), lift(w, bc, av), w.inst('csegel')], 'syl2anc',
                                                    '( v e. ( A cseg B ) <-> E. t e. ( 0 [,] 1 ) v = ( A + ( t x. ( B - A ) ) ) )')], 'mpbid',
            'E. t e. ( 0 [,] 1 ) v = ( A + ( t x. ( B - A ) ) )')
    at = '( %s /\\ t e. ( 0 [,] 1 ) )' % av
    s2 = mkst(w, at)
    tt = s2([s2([], 'simpr', 't e. ( 0 [,] 1 )'), w.s([], 'elicc01', '( t e. ( 0 [,] 1 ) <-> ( t e. RR /\\ 0 <_ t /\\ t <_ 1 ) )')], 'sylib', '( t e. RR /\\ 0 <_ t /\\ t <_ 1 )')
    tr = s2([tt], 'simp1d', 't e. RR'); t0 = s2([tt], 'simp2d', '0 <_ t'); t1 = s2([tt], 'simp3d', 't <_ 1')
    BA = '( B - A )'
    bac = s2([lift(w, bc, at), lift(w, ac, at)], 'subcld', '%s e. CC' % BA)
    tb = '( t x. %s )' % BA
    tbc = s2([s2([tr], 'recnd', 't e. CC'), bac], 'mulcld', '%s e. CC' % tb)
    tri = s2([lift(w, ac, at), tbc], 'abstrid', '( abs ` ( A + %s ) ) <_ ( ( abs ` A ) + ( abs ` %s ) )' % (tb, tb))
    am = s2([s2([tr], 'recnd', 't e. CC'), bac], 'absmuld', '( abs ` %s ) = ( ( abs ` t ) x. ( abs ` %s ) )' % (tb, BA))
    at_ = s2([tr, t0], 'absidd', '( abs ` t ) = t')
    abr = s2([bac], 'abscld', '( abs ` %s ) e. RR' % BA); ab0 = s2([bac], 'absge0d', '0 <_ ( abs ` %s )' % BA)
    m1 = s2([tr, s2([], '1red', '1 e. RR'), abr, ab0, t1], 'lemul1ad', '( t x. ( abs ` %s ) ) <_ ( 1 x. ( abs ` %s ) )' % (BA, BA))
    m2 = s2([m1, s2([s2([abr], 'recnd', '( abs ` %s ) e. CC' % BA)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (BA, BA))], 'breqtrd', '( t x. ( abs ` %s ) ) <_ ( abs ` %s )' % (BA, BA))
    atb = s2([am, s2([at_], 'oveq1d', '( ( abs ` t ) x. ( abs ` %s ) ) = ( t x. ( abs ` %s ) )' % (BA, BA))], 'eqtrd', '( abs ` %s ) = ( t x. ( abs ` %s ) )' % (tb, BA))
    m3 = s2([atb, m2], 'eqbrtrd', '( abs ` %s ) <_ ( abs ` %s )' % (tb, BA))
    aar = s2([lift(w, ac, at)], 'abscld', '( abs ` A ) e. RR')
    m4 = s2([s2([tbc], 'abscld', '( abs ` %s ) e. RR' % tb), abr, aar, m3], 'leadd2dd', '( ( abs ` A ) + ( abs ` %s ) ) <_ ( ( abs ` A ) + ( abs ` %s ) )' % (tb, BA))
    ch = s2([s2([s2([lift(w, ac, at), tbc], 'addcld', '( A + %s ) e. CC' % tb)], 'abscld', '( abs ` ( A + %s ) ) e. RR' % tb),
             s2([aar, s2([tbc], 'abscld', '( abs ` %s ) e. RR' % tb)], 'readdcld', '( ( abs ` A ) + ( abs ` %s ) ) e. RR' % tb),
             s2([aar, abr], 'readdcld', '( ( abs ` A ) + ( abs ` %s ) ) e. RR' % BA), tri, m4], 'letrd', '( abs ` ( A + %s ) ) <_ ( ( abs ` A ) + ( abs ` %s ) )' % (tb, BA))
    e1 = w.s([w.s([w.s([], 'fveq2', '( v = ( A + %s ) -> ( abs ` v ) = ( abs ` ( A + %s ) ) )' % (tb, tb))], 'breq1d',
                  '( v = ( A + %s ) -> ( ( abs ` v ) <_ ( ( abs ` A ) + ( abs ` %s ) ) <-> ( abs ` ( A + %s ) ) <_ ( ( abs ` A ) + ( abs ` %s ) ) ) )' % (tb, BA, tb, BA))], 'idi',
             '( v = ( A + %s ) -> ( ( abs ` v ) <_ ( ( abs ` A ) + ( abs ` %s ) ) <-> ( abs ` ( A + %s ) ) <_ ( ( abs ` A ) + ( abs ` %s ) ) ) )' % (tb, BA, tb, BA))
    imp = w.s([ch, w.s([e1], 'biimprd', '( v = ( A + %s ) -> ( ( abs ` ( A + %s ) ) <_ ( ( abs ` A ) + ( abs ` %s ) ) -> ( abs ` v ) <_ ( ( abs ` A ) + ( abs ` %s ) ) ) )' % (tb, tb, BA, BA))],
              'syl5com', '( %s -> ( v = ( A + %s ) -> ( abs ` v ) <_ ( ( abs ` A ) + ( abs ` %s ) ) ) )' % (at, tb, BA))
    rx = sv([imp], 'rexlimdva', '( E. t e. ( 0 [,] 1 ) v = ( A + %s ) -> ( abs ` v ) <_ ( ( abs ` A ) + ( abs ` %s ) ) )' % (tb, BA))
    fin = st([sv([ex, rx], 'mpd', '( abs ` v ) <_ ( ( abs ` A ) + ( abs ` %s ) )' % BA)], 'ralrimiva', split_imp(S_['gf2segb'])[1])
    w.qed([fin], 'idi', S_['gf2segb'])
    return w


def gf2csegr():
    w = W('gf2csegr', 'A segment between two reals is the closed interval (~ csegicc , ~ cseglin ).')
    a = split_imp(S_['gf2csegr'])[0]
    st = mkst(w, a)
    ar = st([], 'simp1', 'A e. RR'); br = st([], 'simp2', 'B e. RR'); ab = st([], 'simp3', 'A < B')
    abl = st([ab], 'ltled', 'A <_ B')
    axr = st([ar], 'rexrd', 'A e. RR*'); bxr = st([br], 'rexrd', 'B e. RR*')
    ai = st([axr, bxr, abl, w.inst('lbicc2')], 'syl3anc', 'A e. ( A [,] B )')
    bi = st([axr, bxr, abl, w.inst('ubicc2')], 'syl3anc', 'B e. ( A [,] B )')
    s1 = st([st([ar, br], 'jca', '( A e. RR /\\ B e. RR )'), st([ai, bi], 'jca', '( A e. ( A [,] B ) /\\ B e. ( A [,] B ) )'), w.inst('csegicc')], 'syl2anc', '( A cseg B ) C_ ( A [,] B )')
    au = '( %s /\\ u e. ( A [,] B ) )' % a
    su = mkst(w, au)
    ue = su([su([], 'simpr', 'u e. ( A [,] B )'), su([lift(w, ar, au), lift(w, br, au), w.inst('elicc2')], 'syl2anc', '( u e. ( A [,] B ) <-> ( u e. RR /\\ A <_ u /\\ u <_ B ) )')], 'mpbid',
            '( u e. RR /\\ A <_ u /\\ u <_ B )')
    ur = su([ue], 'simp1d', 'u e. RR'); au_ = su([ue], 'simp2d', 'A <_ u'); ub = su([ue], 'simp3d', 'u <_ B')
    BA = '( B - A )'; UA = '( u - A )'; T_ = '( %s / %s )' % (UA, BA)
    bar = su([lift(w, br, au), lift(w, ar, au)], 'resubcld', '%s e. RR' % BA)
    uar = su([ur, lift(w, ar, au)], 'resubcld', '%s e. RR' % UA)
    lv = {'A': lift(w, ar, au), 'B': lift(w, br, au), 'u': ur}
    bap = su([bar, lin.linarith(w, au, [lift(w, ab, au)], '0 < %s' % BA, leaves=dict(lv, **{BA: bar}))], 'elrpd', '%s e. RR+' % BA)
    t0 = su([uar, bap, lin.linarith(w, au, [au_], '0 <_ %s' % UA, leaves=dict(lv, **{UA: uar}))], 'divge0d', '0 <_ %s' % T_)
    t1 = su([lin.linarith(w, au, [ub], '%s <_ ( %s x. 1 )' % (UA, BA), leaves=dict(lv, **{UA: uar, BA: bar})),
             su([uar, su([], '1red', '1 e. RR'), bap], 'ledivmuld', '( %s <_ 1 <-> %s <_ ( %s x. 1 ) )' % (T_, UA, BA))], 'mpbird', '%s <_ 1' % T_)
    tr = su([uar, bap], 'rerpdivcld', '%s e. RR' % T_)
    tin = su([su([tr, t0, t1], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 )' % (T_, T_, T_)), w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (T_, T_, T_, T_))],
             'sylibr', '%s e. ( 0 [,] 1 )' % T_)
    cl = su([su([lift(w, ar, au)], 'recnd', 'A e. CC'), su([lift(w, br, au)], 'recnd', 'B e. CC'), tin, w.inst('cseglin')], 'syl3anc', '( A + ( %s x. %s ) ) e. ( A cseg B )' % (T_, BA))
    dc = su([su([uar], 'recnd', '%s e. CC' % UA), su([bar], 'recnd', '%s e. CC' % BA), su([bap], 'rpne0d', '%s =/= 0' % BA)], 'divcan1d', '( %s x. %s ) = %s' % (T_, BA, UA))
    e2 = su([su([dc], 'oveq2d', '( A + ( %s x. %s ) ) = ( A + %s )' % (T_, BA, UA)), su([su([lift(w, ar, au)], 'recnd', 'A e. CC'), su([ur], 'recnd', 'u e. CC')], 'pncan3d', '( A + %s ) = u' % UA)],
            'eqtrd', '( A + ( %s x. %s ) ) = u' % (T_, BA))
    uc = su([e2, cl], 'eqeltrrd', 'u e. ( A cseg B )')
    s2 = st([st([uc], 'ex', '( u e. ( A [,] B ) -> u e. ( A cseg B ) )')], 'ssrdv', '( A [,] B ) C_ ( A cseg B )')
    w.qed([s1, s2], 'eqssd', S_['gf2csegr'])
    return w


S_['gf2negc.1'] = '( ph -> ( e e. X |-> B ) e. ( X -cn-> CC ) )'
S_['gf2negc'] = '( ph -> ( e e. X |-> -u B ) e. ( X -cn-> CC ) )'


def gf2negc():
    w = W('gf2negc', 'The negative of a continuous function is continuous (~ negcncf , ~ cncfmpt1f ).')
    a = 'ph'
    st = mkst(w, a)
    h1 = w.s([], 'gf2negc.1', S_['gf2negc.1'], name='h1')
    NF = '( o e. CC |-> -u o )'
    nc = a1(w, a, w.s([w.s([], 'ssid', 'CC C_ CC'), w.s([w.s([], 'eqid', '%s = %s' % (NF, NF))], 'negcncf', '( CC C_ CC -> %s e. ( CC -cn-> CC ) )' % NF)], 'ax-mp', '%s e. ( CC -cn-> CC )' % NF),
            '%s e. ( CC -cn-> CC )' % NF)
    c1 = st([nc, h1], 'cncfmpt1f', '( e e. X |-> ( %s ` B ) ) e. ( X -cn-> CC )' % NF)
    ff = st([h1, w.inst('cncff')], 'syl', '( e e. X |-> B ) : X --> CC')
    fa = st([ff, w.s([w.s([], 'eqid', '( e e. X |-> B ) = ( e e. X |-> B )')], 'fmpt', '( A. e e. X B e. CC <-> ( e e. X |-> B ) : X --> CC )')], 'sylibr', 'A. e e. X B e. CC')
    ae = '( ph /\\ e e. X )'
    bc = w.s([fa], 'r19.21bi', '( %s -> B e. CC )' % ae)
    v, _ = mpv(w, ae, 'o', 'CC', '-u o', 'B', bc, exs=a1(w, ae, w.s([], 'negex', '-u B e. _V'), '-u B e. _V'))
    eq = st([v], 'mpteq2dva', '( e e. X |-> ( %s ` B ) ) = ( e e. X |-> -u B )' % NF)
    fin = st([c1, st([eq], 'eleq1d', '( ( e e. X |-> ( %s ` B ) ) e. ( X -cn-> CC ) <-> ( e e. X |-> -u B ) e. ( X -cn-> CC ) )' % NF)], 'mpbid', '( e e. X |-> -u B ) e. ( X -cn-> CC )')
    w.qed([fin], 'idi', S_['gf2negc'])
    return w


AVGt = lambda A, L, W: G1L.AVG(A, L, W)
import gf1lib as G1L
GKF = '( w e. %s |-> ( ( ( _G ` w ) x. ( K ^c -u w ) ) x. %s ) )' % (DG, G1L.AVG('A', 'L', 'w'))
GKFF = GKF
AVK = '( ( 1 / L ) x. S_ [ A -> ( A + L ) ] ( exp ` ( -u K / ( exp ` t ) ) ) _d t )'
YM = '( K x. ( exp ` -u ( A + L ) ) )'
WMH = '( ( K e. NN /\\ ( A e. RR /\\ L e. RR+ ) ) /\\ ( T e. RR /\\ 1 <_ T ) )'
S_['gf2wm'] = '( %s -> ( abs ` ( %s - ( %s x. %s ) ) ) <_ %s )' % (WMH, LIt(GKF, '1', 'T'), TPI, AVK, BND(MYF(YM), 'T'))


def gf2wm():
    w = W('gf2wm', 'The Mellin representation of one averaged window, quantitative on ` Re w = 1 ` (Lean ` avg_window_eq_integral ` ): '
                   '` | int_( 1 - i T )^( 1 + i T ) G ( w ) K ^ -w avgExp ( A , L , w ) dw - 2 pi i ( 1 / L ) int_A^( A + L ) e ^ ( - K / e ^ t ) dt | <_ ( 8 M / log 2 ) 2 ^ ( - T / 4 ) ` '
                   '(~ gf2fub , ~ gf2mt1 , ~ gf1avgi , ~ gf2hl ).')
    a = WMH
    st = mkst(w, a)
    kn = st([], 'simpll', 'K e. NN'); ar = st([], 'simplrl', 'A e. RR'); lrp = st([], 'simplrr', 'L e. RR+')
    tr = st([], 'simprl', 'T e. RR'); t1 = st([], 'simprr', '1 <_ T')
    trp = st([tr, lin.linarith(w, a, [t1], '0 < T', leaves={'T': tr})], 'elrpd', 'T e. RR+')
    krp = st([kn], 'nnrpd', 'K e. RR+'); kc = st([krp], 'rpcnd', 'K e. CC')
    lr = st([lrp], 'rpred', 'L e. RR'); lc = st([lrp], 'rpcnd', 'L e. CC')
    AL = '( A + L )'
    alr = st([ar, lr], 'readdcld', '%s e. RR' % AL)
    aal = lin.linarith(w, a, [st([lrp], 'rpgt0d', '0 < L')], 'A < %s' % AL, leaves={'A': ar, 'L': lr})
    P1 = '( 1 + ( _i x. -u T ) )'; P2 = '( 1 + ( _i x. T ) )'
    U = '( %s cseg %s )' % (P1, P2); V = '( A cseg %s )' % AL
    ic = a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    p1c = st([st([], '1cnd', '1 e. CC'), st([ic, st([st([tr], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % P1)
    p2c = st([st([], '1cnd', '1 e. CC'), st([ic, st([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % P2)
    rp1 = st([st([], '1red', '1 e. RR'), st([tr], 'renegcld', '-u T e. RR'), w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % P1)
    rp2 = st([st([], '1red', '1 e. RR'), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % P2)
    rv = st([p1c, p2c, st([rp1, rp2], 'eqtr4d', '( Re ` %s ) = ( Re ` %s )' % (P1, P2)), w.inst('csegvre')], 'syl3anc', 'A. u e. %s ( Re ` u ) = ( Re ` %s )' % (U, P1))
    ucc = st([p1c, p2c, w.inst('csegcl')], 'syl2anc', '%s C_ CC' % U)
    # points of U: in the Gamma domain, Re = 1
    aq = '( %s /\\ q e. %s )' % (a, U)
    sq = mkst(w, aq)
    qin = sq([], 'simpr', 'q e. %s' % U)
    qc = sq([lift(w, ucc, aq), qin], 'sseldd', 'q e. CC')
    idq = w.s([], 'id', '( u = q -> u = q )')
    rsub = w.s([w.s([], 'fveq2', '( u = q -> ( Re ` u ) = ( Re ` q ) )')], 'eqeq1d', '( u = q -> ( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` q ) = ( Re ` %s ) ) )' % (P1, P1))
    rq = sq([sq([rsub, lift(w, rv, aq), qin], 'rspcdva', '( Re ` q ) = ( Re ` %s )' % P1), lift(w, rp1, aq)], 'eqtrd', '( Re ` q ) = 1')
    qne = sq([sq([rq, a1(w, aq, w.s([], 'ax-1ne0', '1 =/= 0'), '1 =/= 0')], 'eqnetrd', '( Re ` q ) =/= 0'),
              sq([a1(w, aq, w.s([w.s([], 'fveq2', '( q = 0 -> ( Re ` q ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( q = 0 -> ( Re ` q ) = 0 )'),
                     '( q = 0 -> ( Re ` q ) = 0 )')], 'necon3d', '( ( Re ` q ) =/= 0 -> q =/= 0 )')], 'mpd', 'q =/= 0')
    qm1 = lin.linarith(w, aq, [rq], '-u 1 < ( Re ` q )', leaves={'( Re ` q )': sq([qc], 'recld', '( Re ` q ) e. RR')})
    qdg = sq([sq([qc, sq([qm1, qne], 'jca', '( -u 1 < ( Re ` q ) /\\ q =/= 0 )')], 'jca', '( q e. CC /\\ ( -u 1 < ( Re ` q ) /\\ q =/= 0 ) )'), w.inst('z6rdg')], 'syl', 'q e. %s' % DG)
    udg = st([st([qdg], 'ex', '( q e. %s -> q e. %s )' % (U, DG))], 'ssrdv', '%s C_ %s' % (U, DG))
    GYK = GYF('K')
    G = '( w e. %s |-> ( ( _G ` w ) x. ( K ^c -u w ) ) )' % U
    gyh = st([krp, w.inst('z6gyhol')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (GYK, DG, DG, GYK))
    gyc = st([gyh], 'simpld', '%s e. ( %s -cn-> CC )' % (GYK, DG))
    rs = st([udg, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (GYK, U, G))
    gres = st([gyc, st([udg, w.inst('rescncf')], 'syl', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (GYK, DG, GYK, U, U))], 'mpd',
              '( %s |` %s ) e. ( %s -cn-> CC )' % (GYK, U, U))
    gcn = st([gres, st([rs], 'eleq1d', '( ( %s |` %s ) e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (GYK, U, U, G, U))], 'mpbid', '%s e. ( %s -cn-> CC )' % (G, U))
    # the bound of G on U
    MK = MYF('K')
    gqv, _ = mpv(w, aq, 'w', U, '( ( _G ` w ) x. ( K ^c -u w ) )', 'q', qin)
    h1 = sq([a1(w, aq, num.le_lit(w, '( 1 / 2 )', '1'), '( 1 / 2 ) <_ 1'), rq], 'breqtrrd', '( 1 / 2 ) <_ ( Re ` q )')
    h2 = sq([rq, a1(w, aq, num.le_lit(w, '1', '3'), '1 <_ 3')], 'eqbrtrd', '( Re ` q ) <_ 3')
    gy = sq([lift(w, krp, aq), sq([qc, sq([h1, h2], 'jca', '( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 3 )')], 'jca', '( q e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 3 ) )'),
             w.inst('z6gyr')], 'syl2anc', '( abs ` ( ( _G ` q ) x. ( K ^c -u q ) ) ) <_ ( %s x. ( 2 ^c -u ( ( abs ` ( Im ` q ) ) / 4 ) ) )' % MK)
    E4 = '( 2 ^c -u ( ( abs ` ( Im ` q ) ) / 4 ) )'
    iq = sq([sq([qc], 'imcld', '( Im ` q ) e. RR')], 'recnd', '( Im ` q ) e. CC')
    aiq = sq([iq], 'abscld', '( abs ` ( Im ` q ) ) e. RR'); aiq0 = sq([iq], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')
    ng = sq([sq([aiq, a1(w, aq, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, aq, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( ( abs ` ( Im ` q ) ) / 4 ) e. RR')], 'renegcld',
            '-u ( ( abs ` ( Im ` q ) ) / 4 ) e. RR')
    ng0 = lin.linarith(w, aq, [aiq0], '-u ( ( abs ` ( Im ` q ) ) / 4 ) <_ 0', leaves={'( abs ` ( Im ` q ) )': aiq})
    c2 = sq([sq([a1(w, aq, w.s([], '2re', '2 e. RR'), '2 e. RR'), a1(w, aq, w.s([], '1lt2', '1 < 2'), '1 < 2')], 'jca', '( 2 e. RR /\\ 1 < 2 )'),
             sq([ng, sq([], '0red', '0 e. RR')], 'jca', '( -u ( ( abs ` ( Im ` q ) ) / 4 ) e. RR /\\ 0 e. RR )'), w.inst('cxple')], 'syl2anc',
            '( -u ( ( abs ` ( Im ` q ) ) / 4 ) <_ 0 <-> %s <_ ( 2 ^c 0 ) )' % E4)
    e41 = sq([sq([ng0, c2], 'mpbid', '%s <_ ( 2 ^c 0 )' % E4), a1(w, aq, w.s([w.s([], '2cn', '2 e. CC'), w.inst('cxp0')], 'ax-mp', '( 2 ^c 0 ) = 1'), '( 2 ^c 0 ) = 1')], 'breqtrd', '%s <_ 1' % E4)
    mkr = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), st([st([st([krp, litr(w, a, '-u ( 1 / 2 )')], 'rpcxpcld', '( K ^c -u ( 1 / 2 ) ) e. RR+')], 'rpred', '( K ^c -u ( 1 / 2 ) ) e. RR'),
                                                                st([st([krp, litr(w, a, '-u 3')], 'rpcxpcld', '( K ^c -u 3 ) e. RR+')], 'rpred', '( K ^c -u 3 ) e. RR')], 'readdcld',
                                                               '( ( K ^c -u ( 1 / 2 ) ) + ( K ^c -u 3 ) ) e. RR')], 'remulcld', '%s e. RR' % MK)
    k12 = st([krp, litr(w, a, '-u ( 1 / 2 )')], 'rpcxpcld', '( K ^c -u ( 1 / 2 ) ) e. RR+')
    k3 = st([krp, litr(w, a, '-u 3')], 'rpcxpcld', '( K ^c -u 3 ) e. RR+')
    ksum = st([k12, k3], 'rpaddcld', '( ( K ^c -u ( 1 / 2 ) ) + ( K ^c -u 3 ) ) e. RR+')
    mk0 = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), st([ksum], 'rpred', '( ( K ^c -u ( 1 / 2 ) ) + ( K ^c -u 3 ) ) e. RR'), a1(w, a, num.ge0_nat(w, 64), '0 <_ ; 6 4'),
              st([ksum], 'rpge0d', '0 <_ ( ( K ^c -u ( 1 / 2 ) ) + ( K ^c -u 3 ) )')], 'mulge0d', '0 <_ %s' % MK)
    e4r = sq([sq([a1(w, aq, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), ng], 'rpcxpcld', '%s e. RR+' % E4)], 'rpred', '%s e. RR' % E4)
    mb = sq([e4r, sq([], '1red', '1 e. RR'), lift(w, mkr, aq), lift(w, mk0, aq), e41], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 1 )' % (MK, E4, MK))
    mb2 = sq([mb, sq([sq([lift(w, mkr, aq)], 'recnd', '%s e. CC' % MK)], 'mulridd', '( %s x. 1 ) = %s' % (MK, MK))], 'breqtrd', '( %s x. %s ) <_ %s' % (MK, E4, MK))
    gab = sq([sq([gqv], 'fveq2d', '( abs ` ( %s ` q ) ) = ( abs ` ( ( _G ` q ) x. ( K ^c -u q ) ) )' % G), gy], 'eqbrtrd', '( abs ` ( %s ` q ) ) <_ ( %s x. %s )' % (G, MK, E4))
    gqc = sq([gab, w.inst('z6absle')], 'syl', '( %s ` q ) e. CC' % G)
    gb = sq([sq([gqc], 'abscld', '( abs ` ( %s ` q ) ) e. RR' % G), sq([lift(w, mkr, aq), e4r], 'remulcld', '( %s x. %s ) e. RR' % (MK, E4)), lift(w, mkr, aq), gab, mb2], 'letrd',
            '( abs ` ( %s ` q ) ) <_ %s' % (G, MK))
    def ralq(stp, P, X, var='q', to='v'):
        r1 = w.s([stp], 'ralrimiva', '( %s -> A. %s e. %s %s )' % (a, var, X, P(var)))
        idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, to, var, to))
        sb, _ = w.wcongr(P(var), {var: to}, '%s = %s' % (var, to), {var: idx})
        cb = w.s([sb], 'cbvralvw', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (var, X, P(var), to, X, P(to)))
        return w.s([r1, cb], 'sylib', '( %s -> A. %s e. %s %s )' % (a, to, X, P(to)))
    gball = ralq(gb, lambda v: '( abs ` ( %s ` %s ) ) <_ %s' % (G, v, MK), U)
    # radius bounds
    R1 = '( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (P1, P2, P1)
    r1all = st([p1c, p2c, w.inst('gf2segb')], 'syl2anc', 'A. v e. %s ( abs ` v ) <_ %s' % (U, R1))
    r1r = st([st([p1c], 'abscld', '( abs ` %s ) e. RR' % P1), st([st([p2c, p1c], 'subcld', '( %s - %s ) e. CC' % (P2, P1))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (P2, P1))],
             'readdcld', '%s e. RR' % R1)
    acn = st([ar], 'recnd', 'A e. CC'); alc = st([alr], 'recnd', '%s e. CC' % AL)
    R2 = '( ( abs ` A ) + ( abs ` ( %s - A ) ) )' % AL
    r2all = st([acn, alc, w.inst('gf2segb')], 'syl2anc', 'A. v e. %s ( abs ` v ) <_ %s' % (V, R2))
    r2r = st([st([acn], 'abscld', '( abs ` A ) e. RR'), st([st([alc, acn], 'subcld', '( %s - A ) e. CC' % AL)], 'abscld', '( abs ` ( %s - A ) ) e. RR' % AL)], 'readdcld', '%s e. RR' % R2)
    vcc = st([acn, alc, w.inst('csegcl')], 'syl2anc', '%s C_ CC' % V)
    vI = st([ar, alr, aal, w.inst('gf2csegr')], 'syl3anc', '%s = ( A [,] %s )' % (V, AL))
    # ---- Fubini
    FS = {'A': P1, 'B': P2, 'U': U, 'G': G, 'H': MK, 'R': R1, 'E': 'A', 'F': AL, 'V': V, 'P': R2}
    FH = tsub(split_imp(S_['gf2fub'])[0], FS)
    FC = tsub(split_imp(S_['gf2fub'])[1], FS)
    fh1 = st([st([st([p1c, p2c], 'jca', '( %s e. CC /\\ %s e. CC )' % (P1, P2)), a1(w, a, w.s([], 'ssid', '%s C_ %s' % (U, U)), '%s C_ %s' % (U, U))], 'jca',
                 '( ( %s e. CC /\\ %s e. CC ) /\\ %s C_ %s )' % (P1, P2, U, U)),
              st([gcn, st([mkr, gball], 'jca', '( %s e. RR /\\ A. v e. %s ( abs ` ( %s ` v ) ) <_ %s )' % (MK, U, G, MK))], 'jca',
                 '( %s e. ( %s -cn-> CC ) /\\ ( %s e. RR /\\ A. v e. %s ( abs ` ( %s ` v ) ) <_ %s ) )' % (G, U, MK, U, G, MK)),
              st([r1r, r1all], 'jca', '( %s e. RR /\\ A. v e. %s ( abs ` v ) <_ %s )' % (R1, U, R1))], '3jca', tsub(FUBH1, FS))
    fh2 = st([st([st([acn, alc], 'jca', '( A e. CC /\\ %s e. CC )' % AL), a1(w, a, w.s([], 'ssid', '%s C_ %s' % (V, V)), '%s C_ %s' % (V, V))], 'jca',
                 '( ( A e. CC /\\ %s e. CC ) /\\ %s C_ %s )' % (AL, V, V)),
              st([vcc, st([r2r, r2all], 'jca', '( %s e. RR /\\ A. v e. %s ( abs ` v ) <_ %s )' % (R2, V, R2))], 'jca',
                 '( %s C_ CC /\\ ( %s e. RR /\\ A. v e. %s ( abs ` v ) <_ %s ) )' % (V, R2, V, R2))], 'jca', tsub(FUBH2, FS))
    fub = st([fh1, fh2, w.inst('gf2fub')], 'syl2anc', FC)
    LHSFs = tsub(LHSF, FS); RHSFs = tsub(RHSF, FS)
    S1_ = '<. %s , %s >.' % (P1, P2); S2_ = '<. A , %s >.' % AL
    fcn_imp = st([fub], 'simpld', '( %s = %s -> %s e. ( %s -cn-> CC ) )' % (V, V, LHSFs, V))
    lcn = st([a1(w, a, w.s([], 'eqid', '%s = %s' % (V, V)), '%s = %s' % (V, V)), fcn_imp], 'mpd', '%s e. ( %s -cn-> CC )' % (LHSFs, V))
    feq = st([fub], 'simprd', '( %s lint %s ) = ( %s lint %s )' % (LHSFs, S2_, RHSFs, S1_))
    # ---------------- the right side: RHSF = G ( x ) . L . AVG ( A , L , x )
    AVX = lambda x: G1L.AVG('A', 'L', x)
    ax = '( %s /\\ x e. %s )' % (a, U)
    sx = mkst(w, ax)
    xu = sx([], 'simpr', 'x e. %s' % U)
    xc = sx([lift(w, ucc, ax), xu], 'sseldd', 'x e. CC')
    FE = '( e e. %s |-> ( exp ` ( x x. e ) ) )' % V
    vcx = lift(w, vcc, ax)
    idvv = sx([vcx, a1(w, ax, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( e e. %s |-> e ) e. ( %s -cn-> CC )' % (V, V))
    cxv = sx([xc, vcx, a1(w, ax, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( e e. %s |-> x ) e. ( %s -cn-> CC )' % (V, V))
    xe = sx([cxv, idvv], 'mulcncf', '( e e. %s |-> ( x x. e ) ) e. ( %s -cn-> CC )' % (V, V))
    fecn = sx([a1(w, ax, w.s([], 'efcn', 'exp e. ( CC -cn-> CC )'), 'exp e. ( CC -cn-> CC )'), xe], 'cncfmpt1f', '%s e. ( %s -cn-> CC )' % (FE, V))
    iss = sx([lift(w, vI, ax), w.inst('eqimss2')], 'syl', '( A [,] %s ) C_ %s' % (AL, V))
    hl = sx([sx([sx([lift(w, ar, ax), lift(w, alr, ax)], 'jca', '( A e. RR /\\ %s e. RR )' % AL), lift(w, aal, ax)], 'jca', '( ( A e. RR /\\ %s e. RR ) /\\ A < %s )' % (AL, AL)),
             sx([fecn, iss], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( A [,] %s ) C_ %s )' % (FE, V, AL, V)), w.inst('gf2hl')], 'syl2anc',
            '( %s lint %s ) = S. ( A (,) %s ) ( %s ` u ) _d u' % (FE, S2_, AL, FE))
    axu = '( %s /\\ u e. ( A (,) %s ) )' % (ax, AL)
    sxu = mkst(w, axu)
    uV = sxu([lift(w, iss, axu), sxu([a1(w, axu, w.s([], 'ioossicc', '( A (,) %s ) C_ ( A [,] %s )' % (AL, AL)), '( A (,) %s ) C_ ( A [,] %s )' % (AL, AL)), sxu([], 'simpr', 'u e. ( A (,) %s )' % AL)],
                                       'sseldd', 'u e. ( A [,] %s )' % AL)], 'sseldd', 'u e. %s' % V)
    fev, _ = mpv(w, axu, 'e', V, '( exp ` ( x x. e ) )', 'u', uV)
    ie1 = sx([fev], 'itgeq2dv', 'S. ( A (,) %s ) ( %s ` u ) _d u = S. ( A (,) %s ) ( exp ` ( x x. u ) ) _d u' % (AL, FE, AL))
    cbt = w.s([w.s([w.s([], 'oveq2', '( u = t -> ( x x. u ) = ( x x. t ) )')], 'fveq2d', '( u = t -> ( exp ` ( x x. u ) ) = ( exp ` ( x x. t ) ) )')], 'cbvitgv',
              'S. ( A (,) %s ) ( exp ` ( x x. u ) ) _d u = S. ( A (,) %s ) ( exp ` ( x x. t ) ) _d t' % (AL, AL))
    ST = 'S. ( A (,) %s ) ( exp ` ( x x. t ) ) _d t' % AL
    ai_ = sx([sx([lift(w, ar, ax), lift(w, lrp, ax)], 'jca', '( A e. RR /\\ L e. RR+ )'), xc, w.inst('gf1avgi')], 'syl2anc',
             '( ( t e. ( A (,) %s ) |-> ( exp ` ( x x. t ) ) ) e. L^1 /\\ ( ( 1 / L ) x. %s ) = %s )' % (AL, ST, AVX('x')))
    avv = sx([ai_], 'simprd', '( ( 1 / L ) x. %s ) = %s' % (ST, AVX('x')))
    lcx = lift(w, lc, ax); lnz = sx([lift(w, lrp, ax)], 'rpne0d', 'L =/= 0')
    stc = sx([sx([ai_], 'simpld', '( t e. ( A (,) %s ) |-> ( exp ` ( x x. t ) ) ) e. L^1' % AL),
              mkst(w, '( %s /\\ t e. ( A (,) %s ) )' % (ax, AL))([], 'fvexd', '( exp ` ( x x. t ) ) e. _V')], 'itgcl', '%s e. CC' % ST)
    IL = '( L x. %s )' % AVX('x')
    e1 = sx([sx([avv], 'eqcomd', '%s = ( ( 1 / L ) x. %s )' % (AVX('x'), ST))], 'oveq2d', '%s = ( L x. ( ( 1 / L ) x. %s ) )' % (IL, ST))
    e2 = sx([lcx, sx([lcx, lnz], 'reccld', '( 1 / L ) e. CC'), stc], 'mulassd', '( ( L x. ( 1 / L ) ) x. %s ) = ( L x. ( ( 1 / L ) x. %s ) )' % (ST, ST))
    e3 = sx([sx([sx([lcx, lnz], 'recidd', '( L x. ( 1 / L ) ) = 1')], 'oveq1d', '( ( L x. ( 1 / L ) ) x. %s ) = ( 1 x. %s )' % (ST, ST)), sx([stc], 'mullidd', '( 1 x. %s ) = %s' % (ST, ST))],
            'eqtrd', '( ( L x. ( 1 / L ) ) x. %s ) = %s' % (ST, ST))
    e4 = sx([e1, sx([e2, e3], 'eqtr3d', '( L x. ( ( 1 / L ) x. %s ) ) = %s' % (ST, ST))], 'eqtrd', '%s = %s' % (IL, ST))
    iev = sx([sx([hl, ie1], 'eqtrd', '( %s lint %s ) = S. ( A (,) %s ) ( exp ` ( x x. u ) ) _d u' % (FE, S2_, AL)), a1(w, ax, cbt, 'S. ( A (,) %s ) ( exp ` ( x x. u ) ) _d u = %s' % (AL, ST))], 'eqtrd',
             '( %s lint %s ) = %s' % (FE, S2_, ST))
    iel = sx([iev, e4], 'eqtr4d', '( %s lint %s ) = %s' % (FE, S2_, IL))
    RHS2 = '( x e. %s |-> ( ( %s ` x ) x. %s ) )' % (U, G, IL)
    rq_ = st([sx([iel], 'oveq2d', '( ( %s ` x ) x. ( %s lint %s ) ) = ( ( %s ` x ) x. %s )' % (G, FE, S2_, G, IL))], 'mpteq2dva', '%s = %s' % (RHSFs, RHS2))
    rl1 = st([rq_], 'oveq1d', '( %s lint %s ) = ( %s lint %s )' % (RHSFs, S1_, RHS2, S1_))
    # continuity of RHS2 and GKU on U
    avh = st([st([st([ar, ar], 'jca', '( A e. RR /\\ A e. RR )'), lrp], 'jca', '( ( A e. RR /\\ A e. RR ) /\\ L e. RR+ )'), w.inst('gf1avgh')], 'syl', tsub(split_imp(G1L.S['gf1avgh'])[1], {'B': 'A'}))
    AVW = '( w e. CC |-> %s )' % AVX('w')
    avc = st([st([avh], 'simpld', G1L.HOL(AVW, 'CC'))], 'simpld', '%s e. ( CC -cn-> CC )' % AVW)
    uc2 = st([ucc], 'idi', '%s C_ CC' % U)
    avu0 = st([avc, st([ucc, w.inst('rescncf')], 'syl', '( %s e. ( CC -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (AVW, AVW, U, U))], 'mpd', '( %s |` %s ) e. ( %s -cn-> CC )' % (AVW, U, U))
    AVWU = '( w e. %s |-> %s )' % (U, AVX('w'))
    avu = st([avu0, st([st([ucc, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (AVW, U, AVWU))], 'eleq1d', '( ( %s |` %s ) e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (AVW, U, U, AVWU, U))],
             'mpbid', '%s e. ( %s -cn-> CC )' % (AVWU, U))
    AVXU = '( x e. %s |-> %s )' % (U, AVX('x'))
    cbx = w.s([cg(w, AVX('w'), 'w', 'x')], 'cbvmptv', '%s = %s' % (AVWU, AVXU))
    avxu = st([avu, a1(w, a, w.s([cbx], 'eleq1i', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (AVWU, U, AVXU, U)), '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (AVWU, U, AVXU, U))],
              'mpbid', '%s e. ( %s -cn-> CC )' % (AVXU, U))
    lcu = st([lc, ucc, a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( x e. %s |-> L ) e. ( %s -cn-> CC )' % (U, U))
    lav = st([lcu, avxu], 'mulcncf', '( x e. %s |-> %s ) e. ( %s -cn-> CC )' % (U, IL, U))
    gfx = st([st([gcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (G, U))], 'feqmptd', '%s = ( x e. %s |-> ( %s ` x ) )' % (G, U, G))
    gxm = st([gcn, st([gfx], 'eleq1d', '( %s e. ( %s -cn-> CC ) <-> ( x e. %s |-> ( %s ` x ) ) e. ( %s -cn-> CC ) )' % (G, U, U, G, U))], 'mpbid', '( x e. %s |-> ( %s ` x ) ) e. ( %s -cn-> CC )' % (U, G, U))
    r2c = st([gxm, lav], 'mulcncf', '%s e. ( %s -cn-> CC )' % (RHS2, U))
    GKU = '( w e. %s |-> ( ( ( _G ` w ) x. ( K ^c -u w ) ) x. %s ) )' % (U, AVX('w'))
    gku = st([gcn, avu], 'mulcncf', '%s e. ( %s -cn-> CC )' % (GKU, U))
    # pointwise on the segment: RHS2 ( z ) = L GKU ( z )
    az = '( %s /\\ z e. %s )' % (a, U)
    sz = mkst(w, az)
    zu = sz([], 'simpr', 'z e. %s' % U)
    rv2, _ = mpv(w, az, 'x', U, '( ( %s ` x ) x. %s )' % (G, IL), 'z', zu)
    gkv, _ = mpv(w, az, 'w', U, '( ( ( _G ` w ) x. ( K ^c -u w ) ) x. %s )' % AVX('w'), 'z', zu)
    gzv, _ = mpv(w, az, 'w', U, '( ( _G ` w ) x. ( K ^c -u w ) )', 'z', zu)
    zc = sz([lift(w, ucc, az), zu], 'sseldd', 'z e. CC')
    gzc = sz([sz([lift(w, gcn, az), w.inst('cncff')], 'syl', '%s : %s --> CC' % (G, U)), zu], 'ffvelcdmd', '( %s ` z ) e. CC' % G)
    avzc = sz([sz([lift(w, avu, az), w.inst('cncff')], 'syl', '%s : %s --> CC' % (AVWU, U)), zu], 'ffvelcdmd', '( %s ` z ) e. CC' % AVWU)
    avzv, _ = mpv(w, az, 'w', U, AVX('w'), 'z', zu)
    avz = sz([sz([avzv], 'eqcomd', '%s = ( %s ` z )' % (AVX('z'), AVWU)), avzc], 'eqeltrd', '%s e. CC' % AVX('z'))
    m12 = sz([gzc, lift(w, lc, az), avz], 'mul12d', '( ( %s ` z ) x. ( L x. %s ) ) = ( L x. ( ( %s ` z ) x. %s ) )' % (G, AVX('z'), G, AVX('z')))
    gz2 = sz([sz([sz([gzv], 'oveq1d', '( ( %s ` z ) x. %s ) = ( ( ( _G ` z ) x. ( K ^c -u z ) ) x. %s )' % (G, AVX('z'), AVX('z'))), sz([gkv], 'eqcomd',
                                                                                                                                       '( ( ( _G ` z ) x. ( K ^c -u z ) ) x. %s ) = ( %s ` z )' % (AVX('z'), GKU))],
                  'eqtrd', '( ( %s ` z ) x. %s ) = ( %s ` z )' % (G, AVX('z'), GKU))], 'oveq2d', '( L x. ( ( %s ` z ) x. %s ) ) = ( L x. ( %s ` z ) )' % (G, AVX('z'), GKU))
    pz = sz([sz([rv2, m12], 'eqtrd', '( %s ` z ) = ( L x. ( ( %s ` z ) x. %s ) )' % (RHS2, G, AVX('z'))), gz2], 'eqtrd', '( %s ` z ) = ( L x. ( %s ` z ) )' % (RHS2, GKU))
    pall = st([pz], 'ralrimiva', 'A. z e. %s ( %s ` z ) = ( L x. ( %s ` z ) )' % (U, RHS2, GKU))
    lm = st([st([st([p1c, p2c], 'jca', '( %s e. CC /\\ %s e. CC )' % (P1, P2)), st([r2c, a1(w, a, w.s([], 'ssid', '%s C_ %s' % (U, U)), '%s C_ %s' % (U, U))], 'jca',
                                                                                  '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (RHS2, U, U, U))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (P1, P2, RHS2, U, U, U)),
             st([gku, lc], 'jca', '( %s e. ( %s -cn-> CC ) /\\ L e. CC )' % (GKU, U)), pall, w.inst('lintmulc2')], 'syl3anc', '( %s lint %s ) = ( L x. ( %s lint %s ) )' % (RHS2, S1_, GKU, S1_))
    # GKU and GKF agree on the segment
    gkfv, _ = mpv(w, az, 'w', DG, '( ( ( _G ` w ) x. ( K ^c -u w ) ) x. %s )' % AVX('w'), 'z', sz([lift(w, udg, az), zu], 'sseldd', 'z e. %s' % DG))
    eqk = sz([gkv, gkfv], 'eqtr4d', '( %s ` z ) = ( %s ` z )' % (GKU, GKFF))
    ekall = st([eqk], 'ralrimiva', 'A. z e. %s ( %s ` z ) = ( %s ` z )' % (U, GKU, GKFF))
    cc12 = st([p1c, p2c], 'jca', '( %s e. CC /\\ %s e. CC )' % (P1, P2))
    uvv = st([a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), ucc], 'ssexd', '%s e. _V' % U)
    dgv = a1(w, a, w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '%s e. _V' % DG), '%s e. _V' % DG)
    lk = st([st([cc12, st([st([uvv], 'mptexd', '%s e. _V' % GKU), st([dgv], 'mptexd', '%s e. _V' % GKFF)], 'jca', '( %s e. _V /\\ %s e. _V )' % (GKU, GKFF))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (P1, P2, GKU, GKFF)), ekall, w.inst('linteq')], 'syl2anc', '( %s lint %s ) = ( %s lint %s )' % (GKU, S1_, GKFF, S1_))
    XX = '( %s lint %s )' % (GKFF, S1_)
    rhs = st([st([rl1, lm], 'eqtrd', '( %s lint %s ) = ( L x. ( %s lint %s ) )' % (RHSFs, S1_, GKU, S1_)), st([lk], 'oveq2d', '( L x. ( %s lint %s ) ) = ( L x. %s )' % (GKU, S1_, XX))],
             'eqtrd', '( %s lint %s ) = ( L x. %s )' % (RHSFs, S1_, XX))
    # ---------------- the left side, pointwise
    aqv = '( %s /\\ q e. %s )' % (a, V)
    s3 = mkst(w, aqv)
    qv = s3([], 'simpr', 'q e. %s' % V)
    qI = s3([qv, lift(w, vI, aqv)], 'eleqtrd', 'q e. ( A [,] %s )' % AL)
    qe = s3([qI, s3([lift(w, ar, aqv), lift(w, alr, aqv), w.inst('elicc2')], 'syl2anc', '( q e. ( A [,] %s ) <-> ( q e. RR /\\ A <_ q /\\ q <_ %s ) )' % (AL, AL))], 'mpbid',
            '( q e. RR /\\ A <_ q /\\ q <_ %s )' % AL)
    qr = s3([qe], 'simp1d', 'q e. RR'); qle = s3([qe], 'simp3d', 'q <_ %s' % AL)
    YQ = '( K x. ( exp ` -u q ) )'
    eq_ = s3([s3([qr], 'renegcld', '-u q e. RR')], 'rpefcld', '( exp ` -u q ) e. RR+')
    yq = s3([lift(w, krp, aqv), eq_], 'rpmulcld', '%s e. RR+' % YQ)
    PHq = tsub(PHI_('q'), FS)
    azq = '( %s /\\ z e. %s )' % (aqv, U)
    s4 = mkst(w, azq)
    zu4 = s4([], 'simpr', 'z e. %s' % U)
    zc4 = s4([lift(w, ucc, azq), zu4], 'sseldd', 'z e. CC')
    zdg4 = s4([lift(w, udg, azq), zu4], 'sseldd', 'z e. %s' % DG)
    phv, _ = mpv(w, azq, 'x', U, '( ( %s ` x ) x. ( exp ` ( x x. q ) ) )' % G, 'z', zu4)
    gyv, _ = mpv(w, azq, 'w', DG, '( ( _G ` w ) x. ( %s ^c -u w ) )' % YQ, 'z', zdg4)
    gz4, _ = mpv(w, azq, 'w', U, '( ( _G ` w ) x. ( K ^c -u w ) )', 'z', zu4)
    kr_ = lift(w, st([krp], 'rpred', 'K e. RR'), azq); k0_ = lift(w, st([krp], 'rpge0d', '0 <_ K'), azq)
    er_ = s4([lift(w, eq_, azq)], 'rpred', '( exp ` -u q ) e. RR'); e0_ = s4([lift(w, eq_, azq)], 'rpge0d', '0 <_ ( exp ` -u q )')
    nz = s4([zc4], 'negcld', '-u z e. CC')
    mc = s4([s4([kr_, k0_], 'jca', '( K e. RR /\\ 0 <_ K )'), s4([er_, e0_], 'jca', '( ( exp ` -u q ) e. RR /\\ 0 <_ ( exp ` -u q ) )'), nz, w.inst('mulcxp')], 'syl3anc',
            '( %s ^c -u z ) = ( ( K ^c -u z ) x. ( ( exp ` -u q ) ^c -u z ) )' % YQ)
    cef = s4([s4([lift(w, eq_, azq)], 'rpcnd', '( exp ` -u q ) e. CC'), s4([lift(w, eq_, azq)], 'rpne0d', '( exp ` -u q ) =/= 0'), nz, w.inst('cxpef')], 'syl3anc',
             '( ( exp ` -u q ) ^c -u z ) = ( exp ` ( -u z x. ( log ` ( exp ` -u q ) ) ) )')
    rl_ = s4([s4([lift(w, qr, azq)], 'renegcld', '-u q e. RR'), w.inst('relogef')], 'syl', '( log ` ( exp ` -u q ) ) = -u q')
    m2n = s4([zc4, s4([lift(w, qr, azq)], 'recnd', 'q e. CC'), w.inst('mul2neg')], 'syl2anc', '( -u z x. -u q ) = ( z x. q )')
    ce2 = s4([cef, s4([s4([s4([rl_], 'oveq2d', '( -u z x. ( log ` ( exp ` -u q ) ) ) = ( -u z x. -u q )'), m2n], 'eqtrd', '( -u z x. ( log ` ( exp ` -u q ) ) ) = ( z x. q )')], 'fveq2d',
                                                   '( exp ` ( -u z x. ( log ` ( exp ` -u q ) ) ) ) = ( exp ` ( z x. q ) )')], 'eqtrd', '( ( exp ` -u q ) ^c -u z ) = ( exp ` ( z x. q ) )')
    yz = s4([mc, s4([ce2], 'oveq2d', '( ( K ^c -u z ) x. ( ( exp ` -u q ) ^c -u z ) ) = ( ( K ^c -u z ) x. ( exp ` ( z x. q ) ) )')], 'eqtrd',
            '( %s ^c -u z ) = ( ( K ^c -u z ) x. ( exp ` ( z x. q ) ) )' % YQ)
    gzc_ = s4([s4([lift(w, gcn, azq), w.inst('cncff')], 'syl', '%s : %s --> CC' % (G, U)), zu4], 'ffvelcdmd', '( %s ` z ) e. CC' % G)
    gprod = s4([gz4, gzc_], 'eqeltrrd', '( ( _G ` z ) x. ( K ^c -u z ) ) e. CC')
    gmc = s4([zdg4, w.inst('gamcl')], 'syl', '( _G ` z ) e. CC')
    kzc = s4([lift(w, kc, azq), nz], 'cxpcld', '( K ^c -u z ) e. CC')
    ezc = s4([s4([zc4, s4([lift(w, qr, azq)], 'recnd', 'q e. CC')], 'mulcld', '( z x. q ) e. CC')], 'efcld', '( exp ` ( z x. q ) ) e. CC')
    ma = s4([gmc, kzc, ezc], 'mulassd', '( ( ( _G ` z ) x. ( K ^c -u z ) ) x. ( exp ` ( z x. q ) ) ) = ( ( _G ` z ) x. ( ( K ^c -u z ) x. ( exp ` ( z x. q ) ) ) )')
    pz4 = s4([s4([s4([phv, s4([gz4], 'oveq1d', '( ( %s ` z ) x. ( exp ` ( z x. q ) ) ) = ( ( ( _G ` z ) x. ( K ^c -u z ) ) x. ( exp ` ( z x. q ) ) )' % G)], 'eqtrd',
                     '( %s ` z ) = ( ( ( _G ` z ) x. ( K ^c -u z ) ) x. ( exp ` ( z x. q ) ) )' % PHq), ma], 'eqtrd',
                 '( %s ` z ) = ( ( _G ` z ) x. ( ( K ^c -u z ) x. ( exp ` ( z x. q ) ) ) )' % PHq),
              s4([gyv, s4([yz], 'oveq2d', '( ( _G ` z ) x. ( %s ^c -u z ) ) = ( ( _G ` z ) x. ( ( K ^c -u z ) x. ( exp ` ( z x. q ) ) ) )' % YQ)], 'eqtrd',
                 '( %s ` z ) = ( ( _G ` z ) x. ( ( K ^c -u z ) x. ( exp ` ( z x. q ) ) ) )' % GYF(YQ))], 'eqtr4d', '( %s ` z ) = ( %s ` z )' % (PHq, GYF(YQ)))
    pall4 = s3([pz4], 'ralrimiva', 'A. z e. %s ( %s ` z ) = ( %s ` z )' % (U, PHq, GYF(YQ)))
    lq = s3([s3([lift(w, cc12, aqv), s3([s3([lift(w, uvv, aqv)], 'mptexd', '%s e. _V' % PHq), s3([lift(w, dgv, aqv)], 'mptexd', '%s e. _V' % GYF(YQ))], 'jca',
                                                 '( %s e. _V /\\ %s e. _V )' % (PHq, GYF(YQ)))], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (P1, P2, PHq, GYF(YQ))),
             pall4, w.inst('linteq')], 'syl2anc', '( %s lint %s ) = %s' % (PHq, S1_, LIt(GYF(YQ), '1', 'T')))
    MTB = BND(MYF(YQ), 'T')
    mt = s3([yq, s3([lift(w, tr, aqv), lift(w, t1, aqv)], 'jca', '( T e. RR /\\ 1 <_ T )'), w.inst('gf2mt1')], 'syl2anc',
            '( abs ` ( %s - ( %s x. ( exp ` -u %s ) ) ) ) <_ %s' % (LIt(GYF(YQ), '1', 'T'), TPI, YQ, MTB))
    # MY is decreasing: YM <_ YQ
    eAL = st([st([alr], 'renegcld', '-u %s e. RR' % AL)], 'rpefcld', '( exp ` -u %s ) e. RR+' % AL)
    ymrp = st([krp, eAL], 'rpmulcld', '%s e. RR+' % YM)
    el = s3([s3([lift(w, alr, aqv)], 'renegcld', '-u %s e. RR' % AL), s3([qr], 'renegcld', '-u q e. RR'), w.inst('efle')], 'syl2anc',
            '( -u %s <_ -u q <-> ( exp ` -u %s ) <_ ( exp ` -u q ) )' % (AL, AL))
    nle = lin.linarith(w, aqv, [qle], '-u %s <_ -u q' % AL, leaves={AL: lift(w, alr, aqv), 'q': qr})
    ele = s3([nle, el], 'mpbid', '( exp ` -u %s ) <_ ( exp ` -u q )' % AL)
    yle = s3([s3([lift(w, eAL, aqv)], 'rpred', '( exp ` -u %s ) e. RR' % AL), s3([eq_], 'rpred', '( exp ` -u q ) e. RR'), lift(w, st([krp], 'rpred', 'K e. RR'), aqv),
              lift(w, st([krp], 'rpge0d', '0 <_ K'), aqv), ele], 'lemul2ad', '%s <_ %s' % (YM, YQ))
    def negpow(c, cr_):
        """YQ ^c -u c <_ YM ^c -u c"""
        c1_ = s3([s3([s3([lift(w, ymrp, aqv)], 'rpred', '%s e. RR' % YM), s3([lift(w, ymrp, aqv)], 'rpge0d', '0 <_ %s' % YM)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (YM, YM)),
                  s3([s3([yq], 'rpred', '%s e. RR' % YQ), s3([yq], 'rpge0d', '0 <_ %s' % YQ)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (YQ, YQ)), cr_, w.inst('cxple2')], 'syl3anc',
                 '( %s <_ %s <-> ( %s ^c %s ) <_ ( %s ^c %s ) )' % (YM, YQ, YM, c, YQ, c))
        p1 = s3([yle, c1_], 'mpbid', '( %s ^c %s ) <_ ( %s ^c %s )' % (YM, c, YQ, c))
        crr = s3([cr_], 'rpred', '%s e. RR' % c)
        ymc = s3([lift(w, ymrp, aqv), crr], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (YM, c)); yqc = s3([yq, crr], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (YQ, c))
        p2 = s3([p1, s3([ymc, yqc], 'lerecd', '( ( %s ^c %s ) <_ ( %s ^c %s ) <-> ( 1 / ( %s ^c %s ) ) <_ ( 1 / ( %s ^c %s ) ) )' % (YM, c, YQ, c, YQ, c, YM, c))], 'mpbid',
                 '( 1 / ( %s ^c %s ) ) <_ ( 1 / ( %s ^c %s ) )' % (YQ, c, YM, c))
        n1 = s3([s3([yq], 'rpcnd', '%s e. CC' % YQ), s3([yq], 'rpne0d', '%s =/= 0' % YQ), s3([crr], 'recnd', '%s e. CC' % c), w.inst('cxpneg')], 'syl3anc',
                '( %s ^c -u %s ) = ( 1 / ( %s ^c %s ) )' % (YQ, c, YQ, c))
        n2 = s3([s3([lift(w, ymrp, aqv)], 'rpcnd', '%s e. CC' % YM), s3([lift(w, ymrp, aqv)], 'rpne0d', '%s =/= 0' % YM), s3([crr], 'recnd', '%s e. CC' % c), w.inst('cxpneg')], 'syl3anc',
                '( %s ^c -u %s ) = ( 1 / ( %s ^c %s ) )' % (YM, c, YM, c))
        r = s3([s3([n1, p2], 'eqbrtrd', '( %s ^c -u %s ) <_ ( 1 / ( %s ^c %s ) )' % (YQ, c, YM, c)), n2], 'breqtrrd', '( %s ^c -u %s ) <_ ( %s ^c -u %s )' % (YQ, c, YM, c))
        yqr = s3([yq, s3([s3([crr], 'renegcld', '-u %s e. RR' % c)], 'idi', '-u %s e. RR' % c)], 'rpcxpcld', '( %s ^c -u %s ) e. RR+' % (YQ, c))
        ymr = s3([lift(w, ymrp, aqv), s3([crr], 'renegcld', '-u %s e. RR' % c)], 'rpcxpcld', '( %s ^c -u %s ) e. RR+' % (YM, c))
        return r, yqr, ymr
    h_ = s3([a1(w, aqv, num.rp(w, '( 1 / 2 )'), '( 1 / 2 ) e. RR+')], 'idi', '( 1 / 2 ) e. RR+')
    r12, yq12, ym12 = negpow('( 1 / 2 )', h_)
    r3, yq3, ym3 = negpow('3', a1(w, aqv, w.s([], '3rp', '3 e. RR+'), '3 e. RR+'))
    SQ = '( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) )' % (YQ, YQ); SM = '( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) )' % (YM, YM)
    sqr = s3([s3([yq12], 'rpred', '( %s ^c -u ( 1 / 2 ) ) e. RR' % YQ), s3([yq3], 'rpred', '( %s ^c -u 3 ) e. RR' % YQ)], 'readdcld', '%s e. RR' % SQ)
    smr = s3([s3([ym12], 'rpred', '( %s ^c -u ( 1 / 2 ) ) e. RR' % YM), s3([ym3], 'rpred', '( %s ^c -u 3 ) e. RR' % YM)], 'readdcld', '%s e. RR' % SM)
    sle = s3([s3([yq12], 'rpred', '( %s ^c -u ( 1 / 2 ) ) e. RR' % YQ), s3([yq3], 'rpred', '( %s ^c -u 3 ) e. RR' % YQ),
              s3([ym12], 'rpred', '( %s ^c -u ( 1 / 2 ) ) e. RR' % YM), s3([ym3], 'rpred', '( %s ^c -u 3 ) e. RR' % YM), r12, r3], 'le2addd', '%s <_ %s' % (SQ, SM))
    c64 = a1(w, aqv, num.re_nat(w, 64), '; 6 4 e. RR'); c640 = a1(w, aqv, num.ge0_nat(w, 64), '0 <_ ; 6 4')
    myle = s3([sqr, smr, c64, c640, sle], 'lemul2ad', '%s <_ %s' % (MYF(YQ), MYF(YM)))
    myqr = s3([c64, sqr], 'remulcld', '%s e. RR' % MYF(YQ)); mymr = s3([c64, smr], 'remulcld', '%s e. RR' % MYF(YM))
    c8 = a1(w, aqv, num.re_nat(w, 8), '8 e. RR'); c80 = a1(w, aqv, num.ge0_nat(w, 8), '0 <_ 8')
    m8 = s3([myqr, mymr, c8, c80, myle], 'lemul2ad', '( 8 x. %s ) <_ ( 8 x. %s )' % (MYF(YQ), MYF(YM)))
    lg0 = w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')
    l2rp = a1(w, aqv, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'), lg0], 'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    m8r = s3([c8, myqr], 'remulcld', '( 8 x. %s ) e. RR' % MYF(YQ)); m8mr = s3([c8, mymr], 'remulcld', '( 8 x. %s ) e. RR' % MYF(YM))
    dvl = s3([m8, s3([m8r, m8mr, l2rp], 'lediv1d', '( ( 8 x. %s ) <_ ( 8 x. %s ) <-> ( ( 8 x. %s ) / ( log ` 2 ) ) <_ ( ( 8 x. %s ) / ( log ` 2 ) ) )' % (MYF(YQ), MYF(YM), MYF(YQ), MYF(YM)))],
             'mpbid', '( ( 8 x. %s ) / ( log ` 2 ) ) <_ ( ( 8 x. %s ) / ( log ` 2 ) )' % (MYF(YQ), MYF(YM)))
    E4T = '( 2 ^c -u ( T / 4 ) )'
    e4t = s3([a1(w, aqv, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), s3([s3([lift(w, tr, aqv), a1(w, aqv, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, aqv, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                         'redivcld', '( T / 4 ) e. RR')], 'renegcld', '-u ( T / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E4T)
    bl = s3([s3([m8r, l2rp], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % MYF(YQ)), s3([m8mr, l2rp], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % MYF(YM)),
             s3([e4t], 'rpred', '%s e. RR' % E4T), s3([e4t], 'rpge0d', '0 <_ %s' % E4T), dvl], 'lemul1ad', '%s <_ %s' % (MTB, BND(MYF(YM), 'T')))
    BM_ = BND(MYF(YM), 'T')
    DQ = '( ( %s lint %s ) - ( %s x. ( exp ` -u %s ) ) )' % (PHq, S1_, TPI, YQ)
    dq1 = s3([s3([lq], 'oveq1d', '%s = ( %s - ( %s x. ( exp ` -u %s ) ) )' % (DQ, LIt(GYF(YQ), '1', 'T'), TPI, YQ))], 'fveq2d',
             '( abs ` %s ) = ( abs ` ( %s - ( %s x. ( exp ` -u %s ) ) ) )' % (DQ, LIt(GYF(YQ), '1', 'T'), TPI, YQ))
    mtbr = s3([s3([m8r, l2rp], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % MYF(YQ)), s3([e4t], 'rpred', '%s e. RR' % E4T)], 'remulcld', '%s e. RR' % MTB)
    bmr = s3([s3([m8mr, l2rp], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % MYF(YM)), s3([e4t], 'rpred', '%s e. RR' % E4T)], 'remulcld', '%s e. RR' % BM_)
    dqr = s3([s3([mt, w.inst('z6absle')], 'syl', '( %s - ( %s x. ( exp ` -u %s ) ) ) e. CC' % (LIt(GYF(YQ), '1', 'T'), TPI, YQ))], 'abscld',
             '( abs ` ( %s - ( %s x. ( exp ` -u %s ) ) ) ) e. RR' % (LIt(GYF(YQ), '1', 'T'), TPI, YQ))
    dqb = s3([dq1, s3([dqr, mtbr, bmr, mt, bl], 'letrd', '( abs ` ( %s - ( %s x. ( exp ` -u %s ) ) ) ) <_ %s' % (LIt(GYF(YQ), '1', 'T'), TPI, YQ, BM_))], 'eqbrtrd',
             '( abs ` %s ) <_ %s' % (DQ, BM_))
    # ---------------- the functions on V
    YE = '( K x. ( exp ` -u e ) )'
    D1B = '( %s x. ( exp ` -u %s ) )' % (TPI, YE)
    D1 = '( e e. %s |-> %s )' % (V, D1B)
    PHe = tsub(PHI_('e'), FS)
    DFB = '( ( %s lint %s ) - %s )' % (PHe, S1_, D1B)
    DF = '( e e. %s |-> %s )' % (V, DFB)
    idv_ = st([vcc, a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( e e. %s |-> e ) e. ( %s -cn-> CC )' % (V, V))
    def negc(stp, body):
        return w.s([stp], 'gf2negc', '( %s -> ( e e. %s |-> -u %s ) e. ( %s -cn-> CC ) )' % (a, V, body, V))
    efc_ = a1(w, a, w.s([], 'efcn', 'exp e. ( CC -cn-> CC )'), 'exp e. ( CC -cn-> CC )')
    cst = lambda c, cstep: st([cstep, vcc, a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( e e. %s |-> %s ) e. ( %s -cn-> CC )' % (V, c, V))
    m1 = negc(idv_, 'e')
    m2 = st([efc_, m1], 'cncfmpt1f', '( e e. %s |-> ( exp ` -u e ) ) e. ( %s -cn-> CC )' % (V, V))
    m3 = st([cst('K', kc), m2], 'mulcncf', '( e e. %s |-> %s ) e. ( %s -cn-> CC )' % (V, YE, V))
    m4 = negc(m3, YE)
    m5 = st([efc_, m4], 'cncfmpt1f', '( e e. %s |-> ( exp ` -u %s ) ) e. ( %s -cn-> CC )' % (V, YE, V))
    tpic = st([st([], '2cnd', '2 e. CC'), st([ic, a1(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')],
              'mulcld', '%s e. CC' % TPI)
    d1c = st([cst(TPI, tpic), m5], 'mulcncf', '%s e. ( %s -cn-> CC )' % (D1, V))
    dfc = st([lcn, d1c], 'subcncf', '%s e. ( %s -cn-> CC )' % (DF, V))
    # lintlc: LHSF = 1 . D1 + DF on the segment
    auv = '( %s /\\ u e. %s )' % (a, V)
    s5 = mkst(w, auv)
    uv5 = s5([], 'simpr', 'u e. %s' % V)
    lhv, _ = mpv(w, auv, 'e', V, '( %s lint %s )' % (PHe, S1_), 'u', uv5)
    d1v, _ = mpv(w, auv, 'e', V, D1B, 'u', uv5)
    dfv, _ = mpv(w, auv, 'e', V, DFB, 'u', uv5)
    PHu = tsub(PHI_('u'), FS)
    YU = '( K x. ( exp ` -u u ) )'
    D1U = '( %s x. ( exp ` -u %s ) )' % (TPI, YU)
    d1uc = s5([s5([lift(w, d1c, auv), w.inst('cncff')], 'syl', '%s : %s --> CC' % (D1, V)), uv5], 'ffvelcdmd',
              '( %s ` u ) e. CC' % D1)
    d1uc2 = s5([s5([d1v], 'eqcomd', '%s = ( %s ` u )' % (D1U, D1)), d1uc], 'eqeltrd', '%s e. CC' % D1U)
    lhc = s5([s5([lift(w, lcn, auv), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LHSFs, V)), uv5], 'ffvelcdmd', '( %s ` u ) e. CC' % LHSFs)
    lhc2 = s5([s5([lhv], 'eqcomd', '( %s lint %s ) = ( %s ` u )' % (PHu, S1_, LHSFs)), lhc], 'eqeltrd', '( %s lint %s ) e. CC' % (PHu, S1_))
    alg = s5([s5([s5([d1uc2], 'mullidd', '( 1 x. %s ) = %s' % (D1U, D1U))], 'oveq1d', '( ( 1 x. %s ) + ( ( %s lint %s ) - %s ) ) = ( %s + ( ( %s lint %s ) - %s ) )' % (D1U, PHu, S1_, D1U, D1U, PHu, S1_, D1U)),
              s5([d1uc2, lhc2], 'pncan3d', '( %s + ( ( %s lint %s ) - %s ) ) = ( %s lint %s )' % (D1U, PHu, S1_, D1U, PHu, S1_))], 'eqtrd',
             '( ( 1 x. %s ) + ( ( %s lint %s ) - %s ) ) = ( %s lint %s )' % (D1U, PHu, S1_, D1U, PHu, S1_))
    e_a = s5([s5([d1v], 'oveq2d', '( 1 x. ( %s ` u ) ) = ( 1 x. %s )' % (D1, D1U)), dfv], 'oveq12d', '( ( 1 x. ( %s ` u ) ) + ( %s ` u ) ) = ( ( 1 x. %s ) + ( ( %s lint %s ) - %s ) )' % (D1, DF, D1U, PHu, S1_, D1U))
    pw5 = s5([lhv, s5([e_a, alg], 'eqtrd', '( ( 1 x. ( %s ` u ) ) + ( %s ` u ) ) = ( %s lint %s )' % (D1, DF, PHu, S1_))], 'eqtr4d', '( %s ` u ) = ( ( 1 x. ( %s ` u ) ) + ( %s ` u ) )' % (LHSFs, D1, DF))
    pall5 = st([pw5], 'ralrimiva', 'A. u e. %s ( %s ` u ) = ( ( 1 x. ( %s ` u ) ) + ( %s ` u ) )' % (V, LHSFs, D1, DF))
    vvx = st([a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), vcc], 'ssexd', '%s e. _V' % V)
    lcv = st([st([acn, alc], 'jca', '( A e. CC /\\ %s e. CC )' % AL),
              st([st([vvx], 'mptexd', '%s e. _V' % LHSFs), st([], '1cnd', '1 e. CC'),
                  st([d1c, dfc, a1(w, a, w.s([], 'ssid', '%s C_ %s' % (V, V)), '%s C_ %s' % (V, V))], '3jca', '( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (D1, V, DF, V, V, V))],
                 '3jca', '( %s e. _V /\\ 1 e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (LHSFs, D1, V, DF, V, V, V)),
              pall5, w.inst('lintlc')], 'syl3anc', '( %s lint %s ) = ( ( 1 x. ( %s lint %s ) ) + ( %s lint %s ) )' % (LHSFs, S2_, D1, S2_, DF, S2_))
    # the remainder bound: | DF ( q ) | <_ BM_ on V
    dfq, _ = mpv(w, aqv, 'e', V, DFB, 'q', qv)
    dfqb = s3([s3([dfq], 'fveq2d', '( abs ` ( %s ` q ) ) = ( abs ` %s )' % (DF, DQ)), dqb], 'eqbrtrd', '( abs ` ( %s ` q ) ) <_ %s' % (DF, BM_))
    r1_ = st([dfqb], 'ralrimiva', 'A. q e. %s ( abs ` ( %s ` q ) ) <_ %s' % (V, DF, BM_))
    zsub = w.s([w.s([w.s([], 'fveq2', '( q = z -> ( %s ` q ) = ( %s ` z ) )' % (DF, DF))], 'fveq2d', '( q = z -> ( abs ` ( %s ` q ) ) = ( abs ` ( %s ` z ) ) )' % (DF, DF))], 'breq1d',
               '( q = z -> ( ( abs ` ( %s ` q ) ) <_ %s <-> ( abs ` ( %s ` z ) ) <_ %s ) )' % (DF, BM_, DF, BM_))
    rz_ = st([r1_, w.s([zsub], 'cbvralvw', '( A. q e. %s ( abs ` ( %s ` q ) ) <_ %s <-> A. z e. %s ( abs ` ( %s ` z ) ) <_ %s )' % (V, DF, BM_, V, DF, BM_))], 'sylib',
             'A. z e. %s ( abs ` ( %s ` z ) ) <_ %s' % (V, DF, BM_))
    halfa = st([a1(w, a, num.rp(w, '( 1 / 2 )'), '( 1 / 2 ) e. RR+')], 'rpred', '( 1 / 2 ) e. RR')
    ya12 = st([ymrp, st([halfa], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '( %s ^c -u ( 1 / 2 ) ) e. RR+' % YM)
    ya3 = st([ymrp, st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'renegcld', '-u 3 e. RR')], 'rpcxpcld', '( %s ^c -u 3 ) e. RR+' % YM)
    sma = st([st([ya12, ya3], 'rpaddcld', '%s e. RR+' % SM)], 'rpred', '%s e. RR' % SM)
    mya = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), sma], 'remulcld', '%s e. RR' % MYF(YM))
    m8a = st([a1(w, a, num.re_nat(w, 8), '8 e. RR'), mya], 'remulcld', '( 8 x. %s ) e. RR' % MYF(YM))
    l2a = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'), lg0], 'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    e4a = st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([st([tr, a1(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                    'redivcld', '( T / 4 ) e. RR')], 'renegcld', '-u ( T / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E4T)
    bmra = st([st([m8a, l2a], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % MYF(YM)), st([e4a], 'rpred', '%s e. RR' % E4T)], 'remulcld', '%s e. RR' % BM_)
    lab = st([st([st([acn, alc], 'jca', '( A e. CC /\\ %s e. CC )' % AL), st([dfc, a1(w, a, w.s([], 'ssid', '%s C_ %s' % (V, V)), '%s C_ %s' % (V, V))], 'jca',
                                                                               '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (DF, V, V, V))], 'jca',
                 '( ( A e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (AL, DF, V, V, V)), bmra, rz_, w.inst('lintabs')], 'syl3anc',
              '( abs ` ( %s lint %s ) ) <_ ( %s x. ( abs ` ( %s - A ) ) )' % (DF, S2_, BM_, AL))
    # the main term: D1 = TPI . G2 on the segment, G2 integrated along the real segment
    G2 = '( e e. %s |-> ( exp ` -u %s ) )' % (V, YE)
    d1q, _ = mpv(w, aqv, 'e', V, D1B, 'q', qv)
    g2q, _ = mpv(w, aqv, 'e', V, '( exp ` -u %s )' % YE, 'q', qv)
    pq = s3([d1q, s3([g2q], 'oveq2d', '( %s x. ( %s ` q ) ) = ( %s x. ( exp ` -u %s ) )' % (TPI, G2, TPI, YQ))], 'eqtr4d',
            '( %s ` q ) = ( %s x. ( %s ` q ) )' % (D1, TPI, G2))
    rq_ = st([pq], 'ralrimiva', 'A. q e. %s ( %s ` q ) = ( %s x. ( %s ` q ) )' % (V, D1, TPI, G2))
    zs2 = w.s([w.s([], 'fveq2', '( q = z -> ( %s ` q ) = ( %s ` z ) )' % (D1, D1)),
               w.s([w.s([], 'fveq2', '( q = z -> ( %s ` q ) = ( %s ` z ) )' % (G2, G2))], 'oveq2d', '( q = z -> ( %s x. ( %s ` q ) ) = ( %s x. ( %s ` z ) ) )' % (TPI, G2, TPI, G2))],
              'eqeq12d', '( q = z -> ( ( %s ` q ) = ( %s x. ( %s ` q ) ) <-> ( %s ` z ) = ( %s x. ( %s ` z ) ) ) )' % (D1, TPI, G2, D1, TPI, G2))
    rz2 = st([rq_, w.s([zs2], 'cbvralvw', '( A. q e. %s ( %s ` q ) = ( %s x. ( %s ` q ) ) <-> A. z e. %s ( %s ` z ) = ( %s x. ( %s ` z ) ) )' % (V, D1, TPI, G2, V, D1, TPI, G2))],
             'sylib', 'A. z e. %s ( %s ` z ) = ( %s x. ( %s ` z ) )' % (V, D1, TPI, G2))
    ccA = st([acn, alc], 'jca', '( A e. CC /\\ %s e. CC )' % AL)
    ssV = a1(w, a, w.s([], 'ssid', '%s C_ %s' % (V, V)), '%s C_ %s' % (V, V))
    lm1 = st([st([ccA, st([d1c, ssV], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (D1, V, V, V))], 'jca',
                 '( ( A e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (AL, D1, V, V, V)),
              st([m5, tpic], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s e. CC )' % (G2, V, TPI)), rz2, w.inst('lintmulc2')], 'syl3anc',
             '( %s lint %s ) = ( %s x. ( %s lint %s ) )' % (D1, S2_, TPI, G2, S2_))
    issa = st([vI, w.inst('eqimss2')], 'syl', '( A [,] %s ) C_ %s' % (AL, V))
    hl2 = st([st([st([ar, alr], 'jca', '( A e. RR /\\ %s e. RR )' % AL), aal], 'jca', '( ( A e. RR /\\ %s e. RR ) /\\ A < %s )' % (AL, AL)),
              st([m5, issa], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( A [,] %s ) C_ %s )' % (G2, V, AL, V)), w.inst('gf2hl')], 'syl2anc',
             '( %s lint %s ) = S. ( A (,) %s ) ( %s ` u ) _d u' % (G2, S2_, AL, G2))
    au2 = '( %s /\\ u e. ( A (,) %s ) )' % (a, AL)
    su2 = mkst(w, au2)
    uV2 = su2([lift(w, issa, au2), su2([a1(w, au2, w.s([], 'ioossicc', '( A (,) %s ) C_ ( A [,] %s )' % (AL, AL)), '( A (,) %s ) C_ ( A [,] %s )' % (AL, AL)),
                                        su2([], 'simpr', 'u e. ( A (,) %s )' % AL)], 'sseldd', 'u e. ( A [,] %s )' % AL)], 'sseldd', 'u e. %s' % V)
    g2u, _ = mpv(w, au2, 'e', V, '( exp ` -u %s )' % YE, 'u', uV2)
    uc = su2([lift(w, vcc, au2), uV2], 'sseldd', 'u e. CC')
    kcu = lift(w, kc, au2)
    euc = su2([uc], 'efcld', '( exp ` u ) e. CC'); eun = su2([uc], 'efne0d', '( exp ` u ) =/= 0')
    en = su2([uc, w.inst('efneg')], 'syl', '( exp ` -u u ) = ( 1 / ( exp ` u ) )')
    k1 = su2([su2([en], 'oveq2d', '( K x. ( exp ` -u u ) ) = ( K x. ( 1 / ( exp ` u ) ) )'),
              su2([kcu, euc, eun], 'divrecd', '( K / ( exp ` u ) ) = ( K x. ( 1 / ( exp ` u ) ) )')], 'eqtr4d', '( K x. ( exp ` -u u ) ) = ( K / ( exp ` u ) )')
    k3 = su2([su2([k1], 'negeqd', '-u ( K x. ( exp ` -u u ) ) = -u ( K / ( exp ` u ) )'),
              su2([kcu, euc, eun], 'divnegd', '-u ( K / ( exp ` u ) ) = ( -u K / ( exp ` u ) )')], 'eqtrd', '-u ( K x. ( exp ` -u u ) ) = ( -u K / ( exp ` u ) )')
    pu = su2([g2u, su2([k3], 'fveq2d', '( exp ` -u ( K x. ( exp ` -u u ) ) ) = ( exp ` ( -u K / ( exp ` u ) ) )')], 'eqtrd',
             '( %s ` u ) = ( exp ` ( -u K / ( exp ` u ) ) )' % G2)
    ie2 = st([pu], 'itgeq2dv', 'S. ( A (,) %s ) ( %s ` u ) _d u = S. ( A (,) %s ) ( exp ` ( -u K / ( exp ` u ) ) ) _d u' % (AL, G2, AL))
    IT = 'S. ( A (,) %s ) ( exp ` ( -u K / ( exp ` t ) ) ) _d t' % AL
    DT = 'S_ [ A -> %s ] ( exp ` ( -u K / ( exp ` t ) ) ) _d t' % AL
    cb2 = w.s([w.s([w.s([w.s([], 'fveq2', '( u = t -> ( exp ` u ) = ( exp ` t ) )')], 'oveq2d', '( u = t -> ( -u K / ( exp ` u ) ) = ( -u K / ( exp ` t ) ) )')],
                   'fveq2d', '( u = t -> ( exp ` ( -u K / ( exp ` u ) ) ) = ( exp ` ( -u K / ( exp ` t ) ) ) )')], 'cbvitgv',
              'S. ( A (,) %s ) ( exp ` ( -u K / ( exp ` u ) ) ) _d u = %s' % (AL, IT))
    g2it = st([st([hl2, ie2], 'eqtrd', '( %s lint %s ) = S. ( A (,) %s ) ( exp ` ( -u K / ( exp ` u ) ) ) _d u' % (G2, S2_, AL)), a1(w, a, cb2, 'S. ( A (,) %s ) ( exp ` ( -u K / ( exp ` u ) ) ) _d u = %s' % (AL, IT))], 'eqtrd',
              '( %s lint %s ) = %s' % (G2, S2_, IT))
    dp = st([st([ar, alr, aal], 'ltled', 'A <_ %s' % AL)], 'ditgpos', '%s = %s' % (DT, IT))
    g2c = st([ccA, st([m5, ssV], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (G2, V, V, V)), w.inst('lintcl')], 'syl2anc', '( %s lint %s ) e. CC' % (G2, S2_))
    itc = st([g2it, g2c], 'eqeltrrd', '%s e. CC' % IT)
    dtc = st([dp, itc], 'eqeltrd', '%s e. CC' % DT)
    lnza = st([lrp], 'rpne0d', 'L =/= 0'); recl = st([lc, lnza], 'reccld', '( 1 / L ) e. CC')
    avkc = st([recl, dtc], 'mulcld', '%s e. CC' % AVK)
    la = st([st([lc, recl, dtc], 'mulassd', '( ( L x. ( 1 / L ) ) x. %s ) = ( L x. %s )' % (DT, AVK)),
             st([st([st([lc, lnza], 'recidd', '( L x. ( 1 / L ) ) = 1')], 'oveq1d', '( ( L x. ( 1 / L ) ) x. %s ) = ( 1 x. %s )' % (DT, DT)),
                 st([dtc], 'mullidd', '( 1 x. %s ) = %s' % (DT, DT))], 'eqtrd', '( ( L x. ( 1 / L ) ) x. %s ) = %s' % (DT, DT))], 'eqtr3d', '( L x. %s ) = %s' % (AVK, DT))
    itl = st([st([dp], 'eqcomd', '%s = %s' % (IT, DT)), st([la], 'eqcomd', '%s = ( L x. %s )' % (DT, AVK))], 'eqtrd', '%s = ( L x. %s )' % (IT, AVK))
    I1 = '( %s lint %s )' % (D1, S2_); IDF = '( %s lint %s )' % (DF, S2_)
    PP = '( 1 x. ( %s x. ( L x. %s ) ) )' % (TPI, AVK)
    i1c = st([st([lm1, st([g2it], 'oveq2d', '( %s x. ( %s lint %s ) ) = ( %s x. %s )' % (TPI, G2, S2_, TPI, IT))], 'eqtrd', '%s = ( %s x. %s )' % (I1, TPI, IT)),
              st([itl], 'oveq2d', '( %s x. %s ) = ( %s x. ( L x. %s ) )' % (TPI, IT, TPI, AVK))], 'eqtrd', '%s = ( %s x. ( L x. %s ) )' % (I1, TPI, AVK))
    # the algebra
    E0 = st([rhs, st([feq, lcv], 'eqtr3d', '( %s lint %s ) = ( ( 1 x. %s ) + %s )' % (RHSFs, S1_, I1, IDF))], 'eqtr3d',
            '( L x. %s ) = ( ( 1 x. %s ) + %s )' % (XX, I1, IDF))
    E1 = st([E0, st([st([i1c], 'oveq2d', '( 1 x. %s ) = %s' % (I1, PP))], 'oveq1d', '( ( 1 x. %s ) + %s ) = ( %s + %s )' % (I1, IDF, PP, IDF))], 'eqtrd',
            '( L x. %s ) = ( %s + %s )' % (XX, PP, IDF))
    xxc = st([lk, st([cc12, st([gku, a1(w, a, w.s([], 'ssid', '%s C_ %s' % (U, U)), '%s C_ %s' % (U, U))], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GKU, U, U, U)),
                      w.inst('lintcl')], 'syl2anc', '( %s lint %s ) e. CC' % (GKU, S1_))], 'eqeltrrd', '%s e. CC' % XX)
    idfc = st([ccA, st([dfc, ssV], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (DF, V, V, V)), w.inst('lintcl')], 'syl2anc', '%s e. CC' % IDF)
    cl9 = Closure(w, a, {XX: xxc, AVK: avkc, 'L': lc, TPI: tpic})
    lxc = st([lc, xxc], 'mulcld', '( L x. %s ) e. CC' % XX)
    ppc = st([st([], '1cnd', '1 e. CC'), st([tpic, st([lc, avkc], 'mulcld', '( L x. %s ) e. CC' % AVK)], 'mulcld', '( %s x. ( L x. %s ) ) e. CC' % (TPI, AVK))], 'mulcld', '%s e. CC' % PP)
    E2 = st([st([E1], 'eqcomd', '( %s + %s ) = ( L x. %s )' % (PP, IDF, XX)), st([lxc, ppc, idfc], 'subaddd', '( ( ( L x. %s ) - %s ) = %s <-> ( %s + %s ) = ( L x. %s ) )' % (XX, PP, IDF, PP, IDF, XX))], 'mpbird',
            '( ( L x. %s ) - %s ) = %s' % (XX, PP, IDF))
    DL = '( %s - ( %s x. %s ) )' % (XX, TPI, AVK)
    rq9 = ringeq(w, a, '( ( L x. %s ) - %s )' % (XX, PP), '( L x. %s )' % DL, cl9)
    E3 = st([E2, rq9], 'eqtr3d', '%s = ( L x. %s )' % (IDF, DL))
    dlc = st([xxc, st([tpic, avkc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, AVK))], 'subcld', '%s e. CC' % DL)
    l0 = st([lrp], 'rpge0d', '0 <_ L')
    ab1 = st([st([E3], 'fveq2d', '( abs ` %s ) = ( abs ` ( L x. %s ) )' % (IDF, DL)),
              st([st([lc, dlc], 'absmuld', '( abs ` ( L x. %s ) ) = ( ( abs ` L ) x. ( abs ` %s ) )' % (DL, DL)),
                  st([st([lr, l0], 'absidd', '( abs ` L ) = L')], 'oveq1d', '( ( abs ` L ) x. ( abs ` %s ) ) = ( L x. ( abs ` %s ) )' % (DL, DL))], 'eqtrd',
                 '( abs ` ( L x. %s ) ) = ( L x. ( abs ` %s ) )' % (DL, DL))], 'eqtrd', '( abs ` %s ) = ( L x. ( abs ` %s ) )' % (IDF, DL))
    ab2 = st([st([st([acn, lc], 'pncan2d', '( %s - A ) = L' % AL)], 'fveq2d', '( abs ` ( %s - A ) ) = ( abs ` L )' % AL), st([lr, l0], 'absidd', '( abs ` L ) = L')], 'eqtrd',
             '( abs ` ( %s - A ) ) = L' % AL)
    ab3 = st([st([ab2], 'oveq2d', '( %s x. ( abs ` ( %s - A ) ) ) = ( %s x. L )' % (BM_, AL, BM_)), st([st([bmra], 'recnd', '%s e. CC' % BM_), lc], 'mulcomd',
             '( %s x. L ) = ( L x. %s )' % (BM_, BM_))], 'eqtrd', '( %s x. ( abs ` ( %s - A ) ) ) = ( L x. %s )' % (BM_, AL, BM_))
    lb = st([st([ab1, lab], 'eqbrtrrd', '( L x. ( abs ` %s ) ) <_ ( %s x. ( abs ` ( %s - A ) ) )' % (DL, BM_, AL)), ab3], 'breqtrd',
            '( L x. ( abs ` %s ) ) <_ ( L x. %s )' % (DL, BM_))
    fin = st([lb, st([st([dlc], 'abscld', '( abs ` %s ) e. RR' % DL), bmra, lrp], 'lemul2d', '( ( abs ` %s ) <_ %s <-> ( L x. ( abs ` %s ) ) <_ ( L x. %s ) )' % (DL, BM_, DL, BM_))],
             'mpbird', '( abs ` %s ) <_ %s' % (DL, BM_))
    w.qed([fin], 'idi', S_['gf2wm'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
