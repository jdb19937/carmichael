"""Sortie Z6b, section 4 (generic part): a uniformly summable series of continuous functions may be integrated termwise along a segment.
z6cnadd  ( F oF + G ) is continuous
z6lps    the partial sums of seq 1 ( oF + , F ): continuous, pointwise the finite sums
z6lsum   seq 1 ( + , lint ( F ` k ) ) ~~> lint ( sum_ k ( F ` k ) ) under an M-test majorant (uhlim, ulmcn, ulm2, lintfsum, lintlc, lintabs)
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_a.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import mpval
from z6b_m import inst_all
import lin
from lin import linarith
import num

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def asmpt(w, a, Fn, fcn, X, x):
    """( a -> ( x e. X |-> ( Fn ` x ) ) e. ( X -cn-> CC ) ) from fcn: ( a -> Fn e. ( X -cn-> CC ) ); returns (step, eq step Fn = mapping)"""
    st = mkst(w, a)
    ff = st([fcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (Fn, X))
    eq = st([ff], 'feqmptd', '%s = ( %s e. %s |-> ( %s ` %s ) )' % (Fn, x, X, Fn, x))
    return st([fcn, st([eq], 'eleq1d', '( %s e. ( %s -cn-> CC ) <-> ( %s e. %s |-> ( %s ` %s ) ) e. ( %s -cn-> CC ) )' % (Fn, X, x, X, Fn, x, X))], 'mpbid',
              '( %s e. %s |-> ( %s ` %s ) ) e. ( %s -cn-> CC )' % (x, X, Fn, x, X)), eq


def z6cnadd():
    w = W('z6cnadd', 'The pointwise sum of two continuous functions is continuous (~ offvalfv , ~ addcncf ).')
    a = ante('z6cnadd'); st = mkst(w, a)
    fc = st([], 'simpl', 'F e. %s' % CNU); gc = st([], 'simpr', 'G e. %s' % CNU)
    ucc = st([fc, w.inst('cncfrss')], 'syl', 'U C_ CC')
    uv = st([c_(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), ucc], 'ssexd', 'U e. _V')
    ff = st([fc, w.inst('cncff')], 'syl', 'F : U --> CC'); gf = st([gc, w.inst('cncff')], 'syl', 'G : U --> CC')
    MP_ = '( x e. U |-> ( ( F ` x ) + ( G ` x ) ) )'
    of = st([uv, st([ff], 'ffnd', 'F Fn U'), st([gf], 'ffnd', 'G Fn U')], 'offvalfv', '( F oF + G ) = %s' % MP_)
    m1, _ = asmpt(w, a, 'F', fc, 'U', 'x'); m2, _ = asmpt(w, a, 'G', gc, 'U', 'x')
    ad = w.s([m1, m2], 'addcncf', '( %s -> %s e. %s )' % (a, MP_, CNU))
    w.qed([ad, st([of], 'eleq1d', '( ( F oF + G ) e. %s <-> %s e. %s )' % (CNU, MP_, CNU))], 'mpbird', STATEMENTS['z6cnadd'])
    return w


def z6lps():
    w = W('z6lps', 'The partial sums of a sequence of continuous functions are continuous and are pointwise the finite sums (~ seqcl , ~ seqof , ~ fsumser ).')
    a = ante('z6lps'); st = mkst(w, a)
    ff = st([], 'simpl', 'F : NN --> %s' % CNU); nn = st([], 'simpr', 'N e. NN')
    nz1 = w.s([nn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( N e. NN <-> N e. ( ZZ>= ` 1 ) )')], 'sylib', '( %s -> N e. ( ZZ>= ` 1 ) )' % a)
    # continuity by seqcl
    ax = '( %s /\\ x e. ( 1 ... N ) )' % a
    xnn = w.s([w.s([], 'simpr', '( %s -> x e. ( 1 ... N ) )' % ax), w.inst('elfznn')], 'syl', '( %s -> x e. NN )' % ax)
    fxc = w.s([w.s([ff], 'adantr', '( %s -> F : NN --> %s )' % (ax, CNU)), xnn], 'ffvelcdmd', '( %s -> ( F ` x ) e. %s )' % (ax, CNU))
    axy = '( %s /\\ ( x e. %s /\\ y e. %s ) )' % (a, CNU, CNU)
    cl = w.s([w.s([], 'simprl', '( %s -> x e. %s )' % (axy, CNU)), w.s([], 'simprr', '( %s -> y e. %s )' % (axy, CNU)), w.inst('z6cnadd')], 'syl2anc',
             '( %s -> ( x oF + y ) e. %s )' % (axy, CNU))
    cn = w.s([nz1, fxc, cl], 'seqcl', '( %s -> %s e. %s )' % (a, PSN('N'), CNU))
    # values by seqof
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    ucc = st([st([ff, one], 'ffvelcdmd', '( F ` 1 ) e. %s' % CNU), w.inst('cncfrss')], 'syl', 'U C_ CC')
    uv = st([c_(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), ucc], 'ssexd', 'U e. _V')
    GV = '( m e. NN |-> ( ( F ` m ) ` v ) )'; GZ = '( m e. NN |-> ( ( F ` m ) ` z ) )'
    axz = '( %s /\\ v e. U )' % ax
    gv, _ = mpval(w, axz, 'm', 'NN', '( ( F ` m ) ` v )', 'x', lift(w, xnn, axz))
    mq = w.s([w.s([gv], 'eqcomd', '( %s -> ( ( F ` x ) ` v ) = ( %s ` x ) )' % (axz, GV))], 'mpteq2dva', '( %s -> ( v e. U |-> ( ( F ` x ) ` v ) ) = ( v e. U |-> ( %s ` x ) ) )' % (ax, GV))
    fxf = w.s([fxc, w.inst('cncff')], 'syl', '( %s -> ( F ` x ) : U --> CC )' % ax)
    fe = w.s([fxf], 'feqmptd', '( %s -> ( F ` x ) = ( v e. U |-> ( ( F ` x ) ` v ) ) )' % ax)
    h3 = w.s([fe, mq], 'eqtrd', '( %s -> ( F ` x ) = ( v e. U |-> ( %s ` x ) ) )' % (ax, GV))
    SQV = '( seq 1 ( + , %s ) ` N )' % GV; SQG = '( seq 1 ( + , %s ) ` N )' % GZ
    so = w.s([uv, nz1, h3], 'seqof', '( %s -> %s = ( v e. U |-> %s ) )' % (a, PSN('N'), SQV))
    az = '( %s /\\ z e. U )' % a; tz = mkst(w, az)
    zu2 = tz([], 'simpr', 'z e. U')
    v1 = tz([lift(w, so, az)], 'fveq1d', '( %s ` z ) = ( ( v e. U |-> %s ) ` z )' % (PSN('N'), SQV))
    v2, vv = mpval(w, az, 'v', 'U', SQV, 'z', zu2, exs=w.s([], 'fvexd', '( %s -> %s e. _V )' % (az, SQG)))
    assert vv == SQG, vv
    aiz = '( %s /\\ i e. ( 1 ... N ) )' % az
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... N ) )' % aiz), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % aiz)
    gi, _ = mpval(w, aiz, 'm', 'NN', '( ( F ` m ) ` z )', 'i', inn)
    fic = w.s([w.s([lift(w, ff, aiz), inn], 'ffvelcdmd', '( %s -> ( F ` i ) e. %s )' % (aiz, CNU)), w.inst('cncff')], 'syl', '( %s -> ( F ` i ) : U --> CC )' % aiz)
    zz = w.s([], 'simplr', '( %s -> z e. U )' % aiz)
    ficz = w.s([fic, zz], 'ffvelcdmd', '( %s -> ( ( F ` i ) ` z ) e. CC )' % aiz)
    fs = tz([gi, lift(w, nz1, az), ficz], 'fsumser', 'sum_ i e. ( 1 ... N ) ( ( F ` i ) ` z ) = %s' % SQG)
    val = tz([tz([v1, v2], 'eqtrd', '( %s ` z ) = %s' % (PSN('N'), SQG)), fs], 'eqtr4d', '( %s ` z ) = sum_ i e. ( 1 ... N ) ( ( F ` i ) ` z )' % PSN('N'))
    ral = st([val], 'ralrimiva', 'A. z e. U ( %s ` z ) = sum_ i e. ( 1 ... N ) ( ( F ` i ) ` z )' % PSN('N'))
    w.qed([cn, ral], 'jca', STATEMENTS['z6lps'])
    return w


def z6lsum():
    w = W('z6lsum', 'A series of continuous functions with a summable majorant (M-test) may be integrated termwise along a segment: the partial sums '
          'converge uniformly (~ uhlim ), the limit is continuous (~ ulmcn ), and the segment integral of the remainder is below ` | B - A | ` '
          'times its uniform bound (~ ulm2 , ~ lintfsum , ~ lintlc , ~ lintabs ).')
    a = ante('z6lsum'); f = unpack(w, a); st = mkst(w, a)
    ac = f['A e. CC']; bc = f['B e. CC']; sgu = f['( A cseg B ) C_ U']; ff = f['F : NN --> %s' % CNU]
    mf = f['M : NN --> RR']; mcv = f['seq 1 ( + , M ) e. dom ~~>']; MB = 'A. j e. NN A. y e. U ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j )'; mb = f[MB]
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    ucc = st([st([ff, one], 'ffvelcdmd', '( F ` 1 ) e. %s' % CNU), w.inst('cncfrss')], 'syl', 'U C_ CC')
    cnex = c_(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V')
    uv = st([cnex, ucc], 'ssexd', 'U e. _V')
    MU = '( CC ^m U )'
    # CNU C_ ( CC ^m U )
    ag = '( %s /\\ g e. %s )' % (a, CNU); tg = mkst(w, ag)
    gm = tg([tg([tg([], 'simpr', 'g e. %s' % CNU), w.inst('cncff')], 'syl', 'g : U --> CC'),
             tg([lift(w, cnex, ag), lift(w, uv, ag), w.inst('elmapg')], 'syl2anc', '( g e. %s <-> g : U --> CC )' % MU)], 'mpbird', 'g e. %s' % MU)
    css = st([w.s([gm], 'ex', '( %s -> ( g e. %s -> g e. %s ) )' % (a, CNU, MU))], 'ssrdv', '%s C_ %s' % (CNU, MU))
    fm = st([ff, css], 'fssd', 'F : NN --> %s' % MU)
    GGp = '( v e. U |-> sum_ p e. NN ( ( F ` p ) ` v ) )'
    PS = 'seq 1 ( oF + , F )'
    ul = st([fm, st([mf, mcv, mb], '3jca', MTEST), w.inst('uhlim')], 'syl2anc', '%s ( ~~>u ` U ) %s' % (PS, GGp))
    # the partial sums
    an = '( %s /\\ n e. NN )' % a; tn = mkst(w, an)
    ps = tn([lift(w, ff, an), tn([], 'simpr', 'n e. NN'), w.inst('z6lps')], 'syl2anc',
            '( ( %s ` n ) e. %s /\\ A. s e. U ( ( %s ` n ) ` s ) = sum_ i e. ( 1 ... n ) ( ( F ` i ) ` s ) )' % (PS, CNU, PS))
    psc = tn([ps], 'simpld', '( %s ` n ) e. %s' % (PS, CNU))
    psv = tn([ps], 'simprd', 'A. s e. U ( ( %s ` n ) ` s ) = sum_ i e. ( 1 ... n ) ( ( F ` i ) ` s )' % PS)
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    fnn = st([st([c_(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), w.inst('seqfn')], 'syl', '%s Fn ( ZZ>= ` 1 )' % PS),
              c_(w, a, w.s([nnuz], 'fneq2i', '( %s Fn NN <-> %s Fn ( ZZ>= ` 1 ) )' % (PS, PS)), '( %s Fn NN <-> %s Fn ( ZZ>= ` 1 ) )' % (PS, PS))], 'mpbird', '%s Fn NN' % PS)
    psf = st([st([fnn, st([psc], 'ralrimiva', 'A. n e. NN ( %s ` n ) e. %s' % (PS, CNU))], 'jca', '( %s Fn NN /\\ A. n e. NN ( %s ` n ) e. %s )' % (PS, PS, CNU)),
              c_(w, a, w.s([], 'ffnfv', '( %s : NN --> %s <-> ( %s Fn NN /\\ A. n e. NN ( %s ` n ) e. %s ) )' % (PS, CNU, PS, PS, CNU)),
                 '( %s : NN --> %s <-> ( %s Fn NN /\\ A. n e. NN ( %s ` n ) e. %s ) )' % (PS, CNU, PS, PS, CNU))], 'mpbird', '%s : NN --> %s' % (PS, CNU))
    z1 = c_(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    gcn = w.s([nnuz, z1, psf, ul], 'ulmcn', '( %s -> %s e. %s )' % (a, GGp, CNU))
    ggf = st([ul, w.inst('ulmcl')], 'syl', '%s : U --> CC' % GGp)
    BB = lambda n, z: 'sum_ i e. ( 1 ... %s ) ( ( F ` i ) ` %s )' % (n, z)
    AA = lambda z: 'sum_ p e. NN ( ( F ` p ) ` %s )' % z
    anz = '( ( %s /\\ n e. NN ) /\\ s e. U )' % a
    ub0 = w.s([psv], 'r19.21bi', '( %s -> ( ( %s ` n ) ` s ) = %s )' % (anz, PS, BB('n', 's')))
    ub = w.s([ub0], 'anasss', '( ( %s /\\ ( n e. NN /\\ s e. U ) ) -> ( ( %s ` n ) ` s ) = %s )' % (a, PS, BB('n', 's')))
    az = '( %s /\\ s e. U )' % a
    zu = w.s([], 'simpr', '( %s -> s e. U )' % az)
    from congr import parse as _p
    ua, _ = mpval(w, az, 'v', 'U', AA('v'), 's', zu, exs=w.s([w.s([], 'sumex', '%s e. _V' % AA('s'))], 'a1i', '( %s -> %s e. _V )' % (az, AA('s'))))
    UNI = 'A. d e. RR+ E. m e. NN A. n e. ( ZZ>= ` m ) A. s e. U ( abs ` ( %s - %s ) ) < d' % (BB('n', 's'), AA('s'))
    u2 = w.s([nnuz, z1, st([psf, css], 'fssd', '%s : NN --> %s' % (PS, MU)), ub, ua, ggf, uv], 'ulm2',
             '( %s -> ( %s ( ~~>u ` U ) %s <-> %s ) )' % (a, PS, GGp, UNI))
    uni = st([ul, u2], 'mpbid', UNI)
    # the target
    L = '( k e. NN |-> ( ( F ` k ) lint <. A , B >. ) )'
    SQ = 'seq 1 ( + , %s )' % L
    LG = '( %s lint <. A , B >. )' % GGp
    Q = '( abs ` ( B - A ) )'
    cx = '( %s /\\ x e. RR+ )' % a; tx = mkst(w, cx)
    xr = tx([], 'simpr', 'x e. RR+')
    qr = tx([tx([lift(w, bc, cx), lift(w, ac, cx)], 'subcld', '( B - A ) e. CC')], 'abscld', '%s e. RR' % Q)
    q0 = tx([tx([lift(w, bc, cx), lift(w, ac, cx)], 'subcld', '( B - A ) e. CC')], 'absge0d', '0 <_ %s' % Q)
    q1r = tx([qr, c_(w, cx, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'readdcld', '( %s + 1 ) e. RR' % Q)
    q1p = tx([q1r, linarith(w, cx, [q0], '0 < ( %s + 1 )' % Q, leaves={Q: qr})], 'elrpd', '( %s + 1 ) e. RR+' % Q)
    E_ = '( x / ( %s + 1 ) )' % Q
    erp = tx([xr, q1p], 'rpdivcld', '%s e. RR+' % E_)
    BODY = 'E. m e. NN A. n e. ( ZZ>= ` m ) A. s e. U ( abs ` ( %s - %s ) ) < d' % (BB('n', 's'), AA('s'))
    ue, uenew = inst_all(w, cx, lift(w, uni, cx), 'd', 'RR+', BODY, E_, erp)
    HN = 'A. s e. U ( abs ` ( %s - %s ) ) < %s' % (BB('n', 's'), AA('s'), E_)
    GOAL = '( ( %s ` n ) e. CC /\\ ( abs ` ( ( %s ` n ) - %s ) ) < x )' % (SQ, SQ, LG)
    cj = '( %s /\\ m e. NN )' % cx
    cn_ = '( %s /\\ n e. ( ZZ>= ` m ) )' % cj
    c = '( %s /\\ %s )' % (cn_, HN); t = mkst(w, c)
    mnn = w.s([], 'simplr', '( %s -> m e. NN )' % cn_)
    nuzm = w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` m ) )' % cn_)
    nnn0 = w.s([mnn, nuzm, w.inst('eluznn')], 'syl2anc', '( %s -> n e. NN )' % cn_)
    nnn = lift(w, nnn0, c)
    L_ = lambda s_: lift(w, s_, c)
    PSn = '( %s ` n )' % PS
    psn = t([L_(ff), nnn, w.inst('z6lps')], 'syl2anc', '( %s e. %s /\\ A. z e. U ( %s ` z ) = %s )' % (PSn, CNU, PSn, BB('n', 'z')))
    psnc = t([psn], 'simpld', '%s e. %s' % (PSn, CNU)); psnv = t([psn], 'simprd', 'A. z e. U ( %s ` z ) = %s' % (PSn, BB('n', 'z')))
    PN = '( z e. U |-> %s )' % BB('n', 'z')
    cu = '( %s /\\ z e. U )' % c
    pv = w.s([psnv], 'r19.21bi', '( %s -> ( %s ` z ) = %s )' % (cu, PSn, BB('n', 'z')))
    psf_ = t([psnc, w.inst('cncff')], 'syl', '%s : U --> CC' % PSn)
    pne = t([t([psf_], 'feqmptd', '%s = ( z e. U |-> ( %s ` z ) )' % (PSn, PSn)), t([pv], 'mpteq2dva', '( z e. U |-> ( %s ` z ) ) = %s' % (PSn, PN))], 'eqtrd', '%s = %s' % (PSn, PN))
    pncn = t([psnc, t([pne], 'eleq1d', '( %s e. %s <-> %s e. %s )' % (PSn, CNU, PN, CNU))], 'mpbid', '%s e. %s' % (PN, CNU))
    gcnc = L_(gcn)
    m1, _ = asmpt(w, c, GGp, gcnc, 'U', 'r'); m2, _ = asmpt(w, c, PN, pncn, 'U', 'r')
    DN = '( r e. U |-> ( ( %s ` r ) - ( %s ` r ) ) )' % (GGp, PN)
    dncn = w.s([m1, m2], 'subcncf', '( %s -> %s e. %s )' % (c, DN, CNU))
    # lintlc
    ct_ = '( %s /\\ t e. ( A cseg B ) )' % c; tt = mkst(w, ct_)
    tu_ = tt([L_(sgu) if False else lift(w, sgu, ct_), tt([], 'simpr', 't e. ( A cseg B )')], 'sseldd', 't e. U')
    dv, _ = mpval(w, ct_, 'r', 'U', '( ( %s ` r ) - ( %s ` r ) )' % (GGp, PN), 't', tu_)
    gtc = tt([lift(w, ggf, ct_), tu_], 'ffvelcdmd', '( %s ` t ) e. CC' % GGp)
    ptc = tt([tt([lift(w, pncn, ct_), w.inst('cncff')], 'syl', '%s : U --> CC' % PN), tu_], 'ffvelcdmd', '( %s ` t ) e. CC' % PN)
    e1 = tt([tt([ptc], 'mullidd', '( 1 x. ( %s ` t ) ) = ( %s ` t )' % (PN, PN)), dv], 'oveq12d',
            '( ( 1 x. ( %s ` t ) ) + ( %s ` t ) ) = ( ( %s ` t ) + ( ( %s ` t ) - ( %s ` t ) ) )' % (PN, DN, PN, GGp, PN))
    e2 = tt([e1, tt([ptc, gtc], 'pncan3d', '( ( %s ` t ) + ( ( %s ` t ) - ( %s ` t ) ) ) = ( %s ` t )' % (PN, GGp, PN, GGp))], 'eqtrd',
            '( ( 1 x. ( %s ` t ) ) + ( %s ` t ) ) = ( %s ` t )' % (PN, DN, GGp))
    e3 = tt([e2], 'eqcomd', '( %s ` t ) = ( ( 1 x. ( %s ` t ) ) + ( %s ` t ) )' % (GGp, PN, DN))
    ral = t([e3], 'ralrimiva', 'A. t e. ( A cseg B ) ( %s ` t ) = ( ( 1 x. ( %s ` t ) ) + ( %s ` t ) )' % (GGp, PN, DN))
    ggv = t([L_(uv)], 'mptexd', '%s e. _V' % GGp)
    IP = '( %s lint <. A , B >. )' % PN; ID = '( %s lint <. A , B >. )' % DN
    lc = t([t([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'),
            t([ggv, c_(w, c, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC'), t([pncn, dncn, L_(sgu)], '3jca', '( %s e. %s /\\ %s e. %s /\\ ( A cseg B ) C_ U )' % (PN, CNU, DN, CNU))],
              '3jca', '( %s e. _V /\\ 1 e. CC /\\ ( %s e. %s /\\ %s e. %s /\\ ( A cseg B ) C_ U ) )' % (GGp, PN, CNU, DN, CNU)), ral, w.inst('lintlc')], 'syl3anc',
           '%s = ( ( 1 x. %s ) + %s )' % (LG, IP, ID))
    # lintfsum and the partial sum of the target series
    cq = '( %s /\\ h e. ( 1 ... n ) )' % c
    qn = w.s([w.s([], 'simpr', '( %s -> h e. ( 1 ... n ) )' % cq), w.inst('elfznn')], 'syl', '( %s -> h e. NN )' % cq)
    fq = w.s([lift(w, ff, cq), qn], 'ffvelcdmd', '( %s -> ( F ` h ) e. %s )' % (cq, CNU))
    rq = t([fq], 'ralrimiva', 'A. h e. ( 1 ... n ) ( F ` h ) e. %s' % CNU)
    FZ = '( 1 ... n )'
    lf = t([t([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'),
            t([t([c_(w, c, w.s([], 'fzfi', '%s e. Fin' % FZ), '%s e. Fin' % FZ), L_(ucc)], 'jca', '( %s e. Fin /\\ U C_ CC )' % FZ),
               t([rq, L_(sgu)], 'jca', '( A. h e. %s ( F ` h ) e. %s /\\ ( A cseg B ) C_ U )' % (FZ, CNU))], 'jca',
              '( ( %s e. Fin /\\ U C_ CC ) /\\ ( A. h e. %s ( F ` h ) e. %s /\\ ( A cseg B ) C_ U ) )' % (FZ, FZ, CNU)), w.inst('lintfsum')], 'syl2anc',
           '%s = sum_ i e. %s ( ( F ` i ) lint <. A , B >. )' % (IP, FZ))
    idq = w.s([], 'id', '( i = q -> i = q )')
    sbq, _ = w.congr('( ( F ` i ) lint <. A , B >. )', {'i': 'q'}, 'i = q', {'i': idq})
    cbq = c_(w, c, w.s([sbq], 'cbvsumv', 'sum_ i e. %s ( ( F ` i ) lint <. A , B >. ) = sum_ q e. %s ( ( F ` q ) lint <. A , B >. )' % (FZ, FZ)),
             'sum_ i e. %s ( ( F ` i ) lint <. A , B >. ) = sum_ q e. %s ( ( F ` q ) lint <. A , B >. )' % (FZ, FZ))
    ci = '( %s /\\ q e. %s )' % (c, FZ)
    inn = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (ci, FZ)), w.inst('elfznn')], 'syl', '( %s -> q e. NN )' % ci)
    li, _ = mpval(w, ci, 'k', 'NN', '( ( F ` k ) lint <. A , B >. )', 'q', inn)
    fi = w.s([lift(w, ff, ci), inn], 'ffvelcdmd', '( %s -> ( F ` q ) e. %s )' % (ci, CNU))
    lic = w.s([w.s([w.s([lift(w, ac, ci), lift(w, bc, ci)], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % ci),
                    w.s([fi, lift(w, sgu, ci)], 'jca', '( %s -> ( ( F ` q ) e. %s /\\ ( A cseg B ) C_ U ) )' % (ci, CNU))], 'jca',
                   '( %s -> ( ( A e. CC /\\ B e. CC ) /\\ ( ( F ` q ) e. %s /\\ ( A cseg B ) C_ U ) ) )' % (ci, CNU)), w.inst('lintcl')], 'syl',
              '( %s -> ( ( F ` q ) lint <. A , B >. ) e. CC )' % ci)
    nz1 = t([nnn, c_(w, c, w.s([nnuz], 'eleq2i', '( n e. NN <-> n e. ( ZZ>= ` 1 ) )'), '( n e. NN <-> n e. ( ZZ>= ` 1 ) )')], 'mpbid', 'n e. ( ZZ>= ` 1 )')
    fs = t([li, nz1, lic], 'fsumser', 'sum_ q e. %s ( ( F ` q ) lint <. A , B >. ) = ( %s ` n )' % (FZ, SQ))
    sqn = t([t([fs], 'eqcomd', '( %s ` n ) = sum_ q e. %s ( ( F ` q ) lint <. A , B >. )' % (SQ, FZ)), t([t([lf, cbq], 'eqtrd', '%s = sum_ q e. %s ( ( F ` q ) lint <. A , B >. )' % (IP, FZ))], 'eqcomd', 'sum_ q e. %s ( ( F ` q ) lint <. A , B >. ) = %s' % (FZ, IP))],
            'eqtrd', '( %s ` n ) = %s' % (SQ, IP))
    ipc = t([t([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'), t([pncn, L_(sgu)], 'jca', '( %s e. %s /\\ ( A cseg B ) C_ U )' % (PN, CNU)), w.inst('lintcl')],
            'syl2anc', '%s e. CC' % IP)
    idc = t([t([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'), t([dncn, L_(sgu)], 'jca', '( %s e. %s /\\ ( A cseg B ) C_ U )' % (DN, CNU)), w.inst('lintcl')],
            'syl2anc', '%s e. CC' % ID)
    sqc = t([sqn, ipc], 'eqeltrd', '( %s ` n ) e. CC' % SQ)
    # | lint DN | <_ e | B - A |
    cz = '( %s /\\ t e. ( A cseg B ) )' % c; tz = mkst(w, cz)
    zseg = tz([], 'simpr', 't e. ( A cseg B )')
    zu = tz([lift(w, sgu, cz), zseg], 'sseldd', 't e. U')
    dz, _ = mpval(w, cz, 'r', 'U', '( ( %s ` r ) - ( %s ` r ) )' % (GGp, PN), 't', zu)
    gz, _ = mpval(w, cz, 'v', 'U', AA('v'), 't', zu, exs=w.s([w.s([], 'sumex', '%s e. _V' % AA('t'))], 'a1i', '( %s -> %s e. _V )' % (cz, AA('t'))))
    pz, _ = mpval(w, cz, 'z', 'U', BB('n', 'z'), 't', zu, exs=w.s([w.s([], 'sumex', '%s e. _V' % BB('n', 't'))], 'a1i', '( %s -> %s e. _V )' % (cz, BB('n', 't'))))
    hz, _ = inst_all(w, cz, lift(w, w.s([], 'simpr', '( %s -> %s )' % (c, HN)), cz), 's', 'U', '( abs ` ( %s - %s ) ) < %s' % (BB('n', 's'), AA('s'), E_), 't', zu)
    gzc = tz([lift(w, ggf, cz), zu], 'ffvelcdmd', '( %s ` t ) e. CC' % GGp)
    pzc = tz([tz([lift(w, pncn, cz), w.inst('cncff')], 'syl', '%s : U --> CC' % PN), zu], 'ffvelcdmd', '( %s ` t ) e. CC' % PN)
    d1 = tz([tz([dz], 'fveq2d', '( abs ` ( %s ` t ) ) = ( abs ` ( ( %s ` t ) - ( %s ` t ) ) )' % (DN, GGp, PN)), tz([gzc, pzc], 'abssubd',
                                                                                                                   '( abs ` ( ( %s ` t ) - ( %s ` t ) ) ) = ( abs ` ( ( %s ` t ) - ( %s ` t ) ) )' % (GGp, PN, PN, GGp))],
            'eqtrd', '( abs ` ( %s ` t ) ) = ( abs ` ( ( %s ` t ) - ( %s ` t ) ) )' % (DN, PN, GGp))
    d2 = tz([tz([pz, gz], 'oveq12d', '( ( %s ` t ) - ( %s ` t ) ) = ( %s - %s )' % (PN, GGp, BB('n', 't'), AA('t')))], 'fveq2d',
            '( abs ` ( ( %s ` t ) - ( %s ` t ) ) ) = ( abs ` ( %s - %s ) )' % (PN, GGp, BB('n', 't'), AA('t')))
    d3 = tz([tz([d1, d2], 'eqtrd', '( abs ` ( %s ` t ) ) = ( abs ` ( %s - %s ) )' % (DN, BB('n', 't'), AA('t'))), hz], 'eqbrtrd', '( abs ` ( %s ` t ) ) < %s' % (DN, E_))
    dtc = tz([dz, tz([gzc, pzc], 'subcld', '( ( %s ` t ) - ( %s ` t ) ) e. CC' % (GGp, PN))], 'eqeltrd', '( %s ` t ) e. CC' % DN)
    d4 = tz([tz([dtc], 'abscld', '( abs ` ( %s ` t ) ) e. RR' % DN), tz([lift(w, erp, cz)], 'rpred', '%s e. RR' % E_), d3], 'ltled', '( abs ` ( %s ` t ) ) <_ %s' % (DN, E_))
    rd = t([d4], 'ralrimiva', 'A. t e. ( A cseg B ) ( abs ` ( %s ` t ) ) <_ %s' % (DN, E_))
    ab = t([t([t([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'), t([dncn, L_(sgu)], 'jca', '( %s e. %s /\\ ( A cseg B ) C_ U )' % (DN, CNU))], 'jca',
              '( ( A e. CC /\\ B e. CC ) /\\ ( %s e. %s /\\ ( A cseg B ) C_ U ) )' % (DN, CNU)), t([L_(erp)], 'rpred', '%s e. RR' % E_), rd, w.inst('lintabs')],
           'syl3anc', '( abs ` %s ) <_ ( %s x. %s )' % (ID, E_, Q))
    # | SQ n - LG | = | lint DN |
    l1 = t([lc, t([t([ipc], 'mullidd', '( 1 x. %s ) = %s' % (IP, IP))], 'oveq1d', '( ( 1 x. %s ) + %s ) = ( %s + %s )' % (IP, ID, IP, ID))], 'eqtrd', '%s = ( %s + %s )' % (LG, IP, ID))
    l2 = t([t([l1, sqn], 'oveq12d', '( %s - ( %s ` n ) ) = ( ( %s + %s ) - %s )' % (LG, SQ, IP, ID, IP)), t([ipc, idc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (IP, ID, IP, ID))],
           'eqtrd', '( %s - ( %s ` n ) ) = %s' % (LG, SQ, ID))
    lgc = t([t([L_(ac), L_(bc)], 'jca', '( A e. CC /\\ B e. CC )'), t([gcnc, L_(sgu)], 'jca', '( %s e. %s /\\ ( A cseg B ) C_ U )' % (GGp, CNU)), w.inst('lintcl')],
            'syl2anc', '%s e. CC' % LG)
    l3 = t([t([sqc, lgc], 'abssubd', '( abs ` ( ( %s ` n ) - %s ) ) = ( abs ` ( %s - ( %s ` n ) ) )' % (SQ, LG, LG, SQ)), t([l2], 'fveq2d', '( abs ` ( %s - ( %s ` n ) ) ) = ( abs ` %s )' % (LG, SQ, ID))],
           'eqtrd', '( abs ` ( ( %s ` n ) - %s ) ) = ( abs ` %s )' % (SQ, LG, ID))
    qrc = L_(qr); q1rc = L_(q1r); erc = L_(erp)
    lt0 = linarith(w, c, [], '%s < ( %s + 1 )' % (Q, Q), leaves={Q: qrc})
    lt1 = t([lt0, t([qrc, q1rc, erc], 'ltmul2d', '( %s < ( %s + 1 ) <-> ( %s x. %s ) < ( %s x. ( %s + 1 ) ) )' % (Q, Q, E_, Q, E_, Q))], 'mpbid',
            '( %s x. %s ) < ( %s x. ( %s + 1 ) )' % (E_, Q, E_, Q))
    xc_ = t([t([L_(xr)], 'rpcnd', 'x e. CC'), t([q1rc], 'recnd', '( %s + 1 ) e. CC' % Q), t([L_(q1p)], 'rpne0d', '( %s + 1 ) =/= 0' % Q)], 'divcan1d',
            '( %s x. ( %s + 1 ) ) = x' % (E_, Q))
    lt2 = t([lt1, xc_], 'breqtrd', '( %s x. %s ) < x' % (E_, Q))
    idr = t([idc], 'abscld', '( abs ` %s ) e. RR' % ID)
    eqr = t([t([erc], 'rpred', '%s e. RR' % E_), qrc], 'remulcld', '( %s x. %s ) e. RR' % (E_, Q))
    fin0 = t([idr, eqr, t([L_(xr)], 'rpred', 'x e. RR'), ab, lt2], 'lelttrd', '( abs ` %s ) < x' % ID)
    fin = t([l3, fin0], 'eqbrtrd', '( abs ` ( ( %s ` n ) - %s ) ) < x' % (SQ, LG))
    goal = t([sqc, fin], 'jca', GOAL)
    ex = w.s([goal], 'ex', '( %s -> ( %s -> %s ) )' % (cn_, HN, GOAL))
    ri = w.s([ex], 'ralimdva', '( %s -> ( A. n e. ( ZZ>= ` m ) %s -> A. n e. ( ZZ>= ` m ) %s ) )' % (cj, HN, GOAL))
    re_ = w.s([ri], 'reximdva', '( %s -> ( E. m e. NN A. n e. ( ZZ>= ` m ) %s -> E. m e. NN A. n e. ( ZZ>= ` m ) %s ) )' % (cx, HN, GOAL))
    got = tx([ue, re_], 'mpd', 'E. m e. NN A. n e. ( ZZ>= ` m ) %s' % GOAL)
    allx = st([got], 'ralrimiva', 'A. x e. RR+ E. m e. NN A. n e. ( ZZ>= ` m ) %s' % GOAL)
    lga = st([st([ac, bc], 'jca', '( A e. CC /\\ B e. CC )'), st([gcn, sgu], 'jca', '( %s e. %s /\\ ( A cseg B ) C_ U )' % (GGp, CNU)), w.inst('lintcl')], 'syl2anc', '%s e. CC' % LG)
    an2 = '( %s /\\ n e. NN )' % a
    c2 = w.s([nnuz, z1, c_(w, a, w.s([], 'seqex', '%s e. _V' % SQ), '%s e. _V' % SQ), w.s([], 'eqidd', '( %s -> ( %s ` n ) = ( %s ` n ) )' % (an2, SQ, SQ))], 'clim2',
             '( %s -> ( %s ~~> %s <-> ( %s e. CC /\\ A. x e. RR+ E. m e. NN A. n e. ( ZZ>= ` m ) %s ) ) )' % (a, SQ, LG, LG, GOAL))
    cv = st([st([lga, allx], 'jca', '( %s e. CC /\\ A. x e. RR+ E. m e. NN A. n e. ( ZZ>= ` m ) %s )' % (LG, GOAL)), c2], 'mpbird', '%s ~~> %s' % (SQ, LG))
    # GGp = the stated mapping
    GG = '( z e. U |-> sum_ k e. NN ( ( F ` k ) ` z ) )'
    idk = w.s([], 'id', '( p = k -> p = k )')
    sb_, _ = w.congr('( ( F ` p ) ` v )', {'p': 'k'}, 'p = k', {'p': idk})
    cs = w.s([sb_], 'cbvsumv', '%s = sum_ k e. NN ( ( F ` k ) ` v )' % AA('v'))
    mp = w.s([cs], 'mpteq2i', '%s = ( v e. U |-> sum_ k e. NN ( ( F ` k ) ` v ) )' % GGp)
    idv = w.s([], 'id', '( v = z -> v = z )')
    sb2, _ = w.congr('sum_ k e. NN ( ( F ` k ) ` v )', {'v': 'z'}, 'v = z', {'v': idv})
    cm = w.s([sb2], 'cbvmptv', '( v e. U |-> sum_ k e. NN ( ( F ` k ) ` v ) ) = %s' % GG)
    geq = w.s([mp, cm], 'eqtri', '%s = %s' % (GGp, GG))
    leq = c_(w, a, w.s([geq], 'oveq1i', '%s = ( %s lint <. A , B >. )' % (LG, GG)), '%s = ( %s lint <. A , B >. )' % (LG, GG))
    w.qed([cv, leq], 'breqtrd', STATEMENTS['z6lsum'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6cnadd, z6lps, z6lsum]:
        if want(fn.__name__):
            if not run(fn()):
                break
