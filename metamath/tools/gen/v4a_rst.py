"""Sortie v4a: the inductive step of the radical-fibre Euler-product bound."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import RS, SMS, DEN, mkst, rsel
from cl import lift
from lin import linarith, nlinarith

QZ = '( Q u. { Z } )'
SU = RS(QZ, 'C')
ST = RS('Q', 'C')
AE = ('( ( ( Z e. Prime /\\ 3 <_ Z /\\ C e. NN ) /\\ '
      '( Q e. Fin /\\ Q C_ Prime /\\ A. e e. Q 3 <_ e ) ) /\\ -. Z e. Q )')


def FACT(P):
    return '( ( 2 / %s ) / ( 1 - ( 2 / %s ) ) )' % (P, P)


def PRODQ(E):
    return 'prod_ n e. %s %s' % (E, FACT('n'))


def SUMS(E, idx='j'):
    return 'sum_ %s e. %s %s' % (idx, RS(E, 'C'), DEN(idx))


def PAIR(t):
    return '<. ( Z pCnt %s ) , ( %s / ( Z ^ ( Z pCnt %s ) ) ) >.' % (t, t, t)


FMAP = '( t e. %s |-> %s )' % (SU, PAIR('t'))
GMAP = '( d e. ( 1 ... C ) |-> %s )' % DEN('( Z ^ d )')
HMAP = '( p e. %s |-> %s )' % (ST, DEN('p'))
XRS = '( ( 1 ... C ) X. %s )' % ST
BODY = ('( ( %s ` ( 1st ` ( %s ` m ) ) ) x. ( %s ` ( 2nd ` ( %s ` m ) ) ) )'
        % (GMAP, FMAP, HMAP, FMAP))
SBODY = 'sum_ m e. %s %s' % (SU, BODY)


def rege0(w, ante, expr, rp):
    f = mkst(w, ante)
    return f([f([rp], 'rpred', '%s e. RR' % expr), f([rp], 'rpge0d', '0 <_ %s' % expr),
              f([w.s([], 'elrege0',
                     '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
                'a1i',
                '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
             'mpbir2and', '%s e. ( 0 [,) +oo )' % expr)


def factrp(w, ante, P, nnst, ge3st):
    """( ante -> FACT( P ) e. RR+ ) from ( ante -> P e. NN ) and ( ante -> 3 <_ P )"""
    f = mkst(w, ante)
    prp = f([nnst], 'nnrpd', '%s e. RR+' % P)
    pre = f([prp], 'rpred', '%s e. RR' % P)
    two = f([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    three = f([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    lt23 = f([w.s([], '2lt3', '2 < 3')], 'a1i', '2 < 3')
    p2 = linarith(w, ante, [ge3st, lt23], '2 < %s' % P, leaves={P: pre, '3': three, '2': two})
    trp = f([f([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), prp], 'rpdivcld',
            '( 2 / %s ) e. RR+' % P)
    tre = f([trp], 'rpred', '( 2 / %s ) e. RR' % P)
    tlt = f([f([two, prp, w.inst('divlt1lt')], 'syl2anc',
               '( ( 2 / %s ) < 1 <-> 2 < %s )' % (P, P)), p2], 'mpbird', '( 2 / %s ) < 1' % P)
    one = f([], '1red', '1 e. RR')
    subr = f([one, tre], 'resubcld', '( 1 - ( 2 / %s ) ) e. RR' % P)
    sub0 = f([f([tre, one], 'posdifd',
               '( ( 2 / %s ) < 1 <-> 0 < ( 1 - ( 2 / %s ) ) )' % (P, P)), tlt], 'mpbid',
             '0 < ( 1 - ( 2 / %s ) )' % P)
    return f([trp, f([subr, sub0], 'elrpd', '( 1 - ( 2 / %s ) ) e. RR+' % P)], 'rpdivcld',
             '%s e. RR+' % FACT(P))


def rsstep():
    w = WS('rsstep', 'The inductive step of the radical-fibre Euler-product bound: adjoining '
                     'one prime to the radical multiplies the bound by its Euler factor.')
    st = mkst(w, AE)
    c1 = st([], 'simpll', '( Z e. Prime /\\ 3 <_ Z /\\ C e. NN )')
    c2 = st([], 'simplr', '( Q e. Fin /\\ Q C_ Prime /\\ A. e e. Q 3 <_ e )')
    zp = st([c1], 'simp1d', 'Z e. Prime')
    z3 = st([c1], 'simp2d', '3 <_ Z')
    cnn = st([c1], 'simp3d', 'C e. NN')
    qfin = st([c2], 'simp1d', 'Q e. Fin')
    qprm = st([c2], 'simp2d', 'Q C_ Prime')
    qge3 = st([c2], 'simp3d', 'A. e e. Q 3 <_ e')
    nzq = st([], 'simpr', '-. Z e. Q')
    znn = st([zp, w.inst('prmnn')], 'syl', 'Z e. NN')
    zz = st([znn], 'nnzd', 'Z e. ZZ')
    zrp = st([znn], 'nnrpd', 'Z e. RR+')
    # finiteness
    fz1 = st([], 'fzfid', '( 1 ... C ) e. Fin')
    stss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... C )' % ST)], 'a1i', '%s C_ ( 1 ... C )' % ST)
    stfin = st([fz1, stss], 'ssfid', '%s e. Fin' % ST)
    suss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... C )' % SU)], 'a1i', '%s C_ ( 1 ... C )' % SU)
    sufin = st([fz1, suss], 'ssfid', '%s e. Fin' % SU)
    # G is a nonnegative function on ( 1 ... C )
    AD = '( %s /\\ d e. ( 1 ... C ) )' % AE
    sd = mkst(w, AD)
    dnn = sd([sd([], 'simpr', 'd e. ( 1 ... C )'), w.inst('elfznn')], 'syl', 'd e. NN')
    dn0 = sd([dnn], 'nnnn0d', 'd e. NN0')
    zdnn = sd([lift(w, znn, AD), dn0], 'nnexpcld', '( Z ^ d ) e. NN')
    zdrp = sd([zdnn], 'nnrpd', '( Z ^ d ) e. RR+')
    sgd = sd([sd([sd([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), zdnn,
                  w.inst('sgmnncl')], 'syl2anc', '( 0 sigma ( Z ^ d ) ) e. NN')], 'nnrpd',
             '( 0 sigma ( Z ^ d ) ) e. RR+')
    gdrp = sd([sgd, zdrp], 'rpdivcld', '%s e. RR+' % DEN('( Z ^ d )'))
    gd = rege0(w, AD, DEN('( Z ^ d )'), gdrp)
    gfn = st([gd, w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fmptd',
             '%s : ( 1 ... C ) --> ( 0 [,) +oo )' % GMAP)
    # H is a nonnegative function on ST
    AP = '( %s /\\ p e. %s )' % (AE, ST)
    sp = mkst(w, AP)
    pfz = sp([lift(w, stss, AP), sp([], 'simpr', 'p e. %s' % ST)], 'sseldd', 'p e. ( 1 ... C )')
    pnn = sp([pfz, w.inst('elfznn')], 'syl', 'p e. NN')
    sgp = sp([sp([sp([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), pnn,
                  w.inst('sgmnncl')], 'syl2anc', '( 0 sigma p ) e. NN')], 'nnrpd',
             '( 0 sigma p ) e. RR+')
    hprp = sp([sgp, sp([pnn], 'nnrpd', 'p e. RR+')], 'rpdivcld', '%s e. RR+' % DEN('p'))
    hp = rege0(w, AP, DEN('p'), hprp)
    hfn = st([hp, w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fmptd',
             '%s : %s --> ( 0 [,) +oo )' % (HMAP, ST))
    # F is injective
    f1 = st([st([st([zp, cnn], 'jca', '( Z e. Prime /\\ C e. NN )'), nzq], 'jca',
                '( ( Z e. Prime /\\ C e. NN ) /\\ -. Z e. Q )'), w.inst('rsf1')], 'syl',
            '%s : %s -1-1-> %s' % (FMAP, SU, XRS))
    spu = st([st([fz1, stfin, sufin], '3jca',
                 '( ( 1 ... C ) e. Fin /\\ %s e. Fin /\\ %s e. Fin )' % (ST, SU)),
              st([gfn, hfn], 'jca',
                 '( %s : ( 1 ... C ) --> ( 0 [,) +oo ) /\\ %s : %s --> ( 0 [,) +oo ) )'
                 % (GMAP, HMAP, ST)), f1, w.inst('sumprodub')], 'syl3anc',
             '%s <_ ( sum_ i e. ( 1 ... C ) ( %s ` i ) x. sum_ j e. %s ( %s ` j ) )'
             % (SBODY, GMAP, ST, HMAP))
    # the two right-hand sums
    ga = w.s([], 'oveq2', '( d = i -> ( Z ^ d ) = ( Z ^ i ) )')
    gb = w.s([ga], 'oveq2d',
             '( d = i -> ( 0 sigma ( Z ^ d ) ) = ( 0 sigma ( Z ^ i ) ) )')
    gc = w.s([gb, ga], 'oveq12d',
             '( d = i -> %s = %s )' % (DEN('( Z ^ d )'), DEN('( Z ^ i )')))
    AI = '( %s /\\ i e. ( 1 ... C ) )' % AE
    si = mkst(w, AI)
    ifz = si([], 'simpr', 'i e. ( 1 ... C )')
    gival = si([si([ifz, si([w.s([], 'ovex', '%s e. _V' % DEN('( Z ^ i )'))], 'a1i',
                            '%s e. _V' % DEN('( Z ^ i )'))], 'jca',
                   '( i e. ( 1 ... C ) /\\ %s e. _V )' % DEN('( Z ^ i )')),
                si([w.s([gc,
                         w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fvmptg',
                        '( ( i e. ( 1 ... C ) /\\ %s e. _V ) -> ( %s ` i ) = %s )'
                        % (DEN('( Z ^ i )'), GMAP, DEN('( Z ^ i )')))], 'a1i',
                   '( ( i e. ( 1 ... C ) /\\ %s e. _V ) -> ( %s ` i ) = %s )'
                   % (DEN('( Z ^ i )'), GMAP, DEN('( Z ^ i )')))], 'mpd',
               '( %s ` i ) = %s' % (GMAP, DEN('( Z ^ i )')))
    gsum = st([gival], 'sumeq2dv',
              'sum_ i e. ( 1 ... C ) ( %s ` i ) = sum_ i e. ( 1 ... C ) %s'
              % (GMAP, DEN('( Z ^ i )')))
    ha = w.s([], 'oveq2', '( p = j -> ( 0 sigma p ) = ( 0 sigma j ) )')
    hb = w.s([], 'id', '( p = j -> p = j )')
    hc = w.s([ha, hb], 'oveq12d', '( p = j -> %s = %s )' % (DEN('p'), DEN('j')))
    AJ = '( %s /\\ j e. %s )' % (AE, ST)
    sj = mkst(w, AJ)
    jst = sj([], 'simpr', 'j e. %s' % ST)
    hjval = sj([sj([jst, sj([w.s([], 'ovex', '%s e. _V' % DEN('j'))], 'a1i',
                            '%s e. _V' % DEN('j'))], 'jca',
                   '( j e. %s /\\ %s e. _V )' % (ST, DEN('j'))),
                sj([w.s([hc,
                         w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fvmptg',
                        '( ( j e. %s /\\ %s e. _V ) -> ( %s ` j ) = %s )'
                        % (ST, DEN('j'), HMAP, DEN('j')))], 'a1i',
                   '( ( j e. %s /\\ %s e. _V ) -> ( %s ` j ) = %s )'
                   % (ST, DEN('j'), HMAP, DEN('j')))], 'mpd',
               '( %s ` j ) = %s' % (HMAP, DEN('j')))
    hsum = st([hjval], 'sumeq2dv',
              'sum_ j e. %s ( %s ` j ) = %s' % (ST, HMAP, SUMS('Q')))
    rhs = st([gsum, hsum], 'oveq12d',
             '( sum_ i e. ( 1 ... C ) ( %s ` i ) x. sum_ j e. %s ( %s ` j ) ) = '
             '( sum_ i e. ( 1 ... C ) %s x. %s )'
             % (GMAP, ST, HMAP, DEN('( Z ^ i )'), SUMS('Q')))
    spu2 = st([spu, rhs], 'breqtrd',
              '%s <_ ( sum_ i e. ( 1 ... C ) %s x. %s )' % (SBODY, DEN('( Z ^ i )'), SUMS('Q')))
    # the left-hand body is DEN( m )
    KM = '( Z pCnt m )'
    ZKM = '( Z ^ %s )' % KM
    BM = '( m / %s )' % ZKM
    AM = '( %s /\ m e. %s )' % (AE, SU)
    sm = mkst(w, AM)
    msu = sm([], 'simpr', 'm e. %s' % SU)
    spl = sm([sm([sm([sm([lift(w, zp, AM), lift(w, cnn, AM)], 'jca',
                         '( Z e. Prime /\ C e. NN )'), lift(w, nzq, AM)], 'jca',
                     '( ( Z e. Prime /\ C e. NN ) /\ -. Z e. Q )'), msu], 'jca',
                 '( ( ( Z e. Prime /\ C e. NN ) /\ -. Z e. Q ) /\ m e. %s )' % SU),
              w.inst('rssplit')], 'syl',
             '( %s e. ( 1 ... C ) /\ %s e. %s /\ ( %s x. %s ) = m )' % (KM, BM, ST, ZKM, BM))
    kfz = sm([spl], 'simp1d', '%s e. ( 1 ... C )' % KM)
    bst = sm([spl], 'simp2d', '%s e. %s' % (BM, ST))
    prod = sm([spl], 'simp3d', '( %s x. %s ) = m' % (ZKM, BM))
    cb1 = w.s([], 'oveq2', '( t = m -> ( Z pCnt t ) = %s )' % KM)
    cb2 = w.s([w.s([], 'id', '( t = m -> t = m )'),
               w.s([cb1], 'oveq2d', '( t = m -> ( Z ^ ( Z pCnt t ) ) = %s )' % ZKM)],
              'oveq12d', '( t = m -> ( t / ( Z ^ ( Z pCnt t ) ) ) = %s )' % BM)
    cb = w.s([cb1, cb2], 'opeq12d', '( t = m -> %s = %s )' % (PAIR('t'), PAIR('m')))
    fmv = sm([sm([msu, sm([w.s([], 'opex', '%s e. _V' % PAIR('m'))], 'a1i',
                          '%s e. _V' % PAIR('m'))], 'jca',
                 '( m e. %s /\ %s e. _V )' % (SU, PAIR('m'))),
              sm([w.s([cb, w.s([], 'eqid', '%s = %s' % (FMAP, FMAP))], 'fvmptg',
                      '( ( m e. %s /\ %s e. _V ) -> ( %s ` m ) = %s )'
                      % (SU, PAIR('m'), FMAP, PAIR('m')))], 'a1i',
                 '( ( m e. %s /\ %s e. _V ) -> ( %s ` m ) = %s )'
                 % (SU, PAIR('m'), FMAP, PAIR('m')))], 'mpd',
             '( %s ` m ) = %s' % (FMAP, PAIR('m')))
    kex = w.s([], 'ovex', '%s e. _V' % KM)
    bex = w.s([], 'ovex', '%s e. _V' % BM)
    o1 = w.s([kex, bex], 'op1st', '( 1st ` %s ) = %s' % (PAIR('m'), KM))
    o2 = w.s([kex, bex], 'op2nd', '( 2nd ` %s ) = %s' % (PAIR('m'), BM))
    f1st = sm([sm([fmv], 'fveq2d', '( 1st ` ( %s ` m ) ) = ( 1st ` %s )' % (FMAP, PAIR('m'))),
               sm([o1], 'a1i', '( 1st ` %s ) = %s' % (PAIR('m'), KM))], 'eqtrd',
              '( 1st ` ( %s ` m ) ) = %s' % (FMAP, KM))
    f2nd = sm([sm([fmv], 'fveq2d', '( 2nd ` ( %s ` m ) ) = ( 2nd ` %s )' % (FMAP, PAIR('m'))),
               sm([o2], 'a1i', '( 2nd ` %s ) = %s' % (PAIR('m'), BM))], 'eqtrd',
              '( 2nd ` ( %s ` m ) ) = %s' % (FMAP, BM))
    gka = w.s([], 'oveq2', '( d = %s -> ( Z ^ d ) = %s )' % (KM, ZKM))
    gkb = w.s([gka], 'oveq2d',
              '( d = %s -> ( 0 sigma ( Z ^ d ) ) = ( 0 sigma %s ) )' % (KM, ZKM))
    gkc = w.s([gkb, gka], 'oveq12d',
              '( d = %s -> %s = %s )' % (KM, DEN('( Z ^ d )'), DEN(ZKM)))
    gkv = sm([sm([kfz, sm([w.s([], 'ovex', '%s e. _V' % DEN(ZKM))], 'a1i',
                          '%s e. _V' % DEN(ZKM))], 'jca',
                 '( %s e. ( 1 ... C ) /\ %s e. _V )' % (KM, DEN(ZKM))),
              sm([w.s([gkc, w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fvmptg',
                      '( ( %s e. ( 1 ... C ) /\ %s e. _V ) -> ( %s ` %s ) = %s )'
                      % (KM, DEN(ZKM), GMAP, KM, DEN(ZKM)))], 'a1i',
                 '( ( %s e. ( 1 ... C ) /\ %s e. _V ) -> ( %s ` %s ) = %s )'
                 % (KM, DEN(ZKM), GMAP, KM, DEN(ZKM)))], 'mpd',
             '( %s ` %s ) = %s' % (GMAP, KM, DEN(ZKM)))
    hba = w.s([], 'oveq2', '( p = %s -> ( 0 sigma p ) = ( 0 sigma %s ) )' % (BM, BM))
    hbb = w.s([], 'id', '( p = %s -> p = %s )' % (BM, BM))
    hbc = w.s([hba, hbb], 'oveq12d', '( p = %s -> %s = %s )' % (BM, DEN('p'), DEN(BM)))
    hbv = sm([sm([bst, sm([w.s([], 'ovex', '%s e. _V' % DEN(BM))], 'a1i',
                          '%s e. _V' % DEN(BM))], 'jca',
                 '( %s e. %s /\ %s e. _V )' % (BM, ST, DEN(BM))),
              sm([w.s([hbc, w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fvmptg',
                      '( ( %s e. %s /\ %s e. _V ) -> ( %s ` %s ) = %s )'
                      % (BM, ST, DEN(BM), HMAP, BM, DEN(BM)))], 'a1i',
                 '( ( %s e. %s /\ %s e. _V ) -> ( %s ` %s ) = %s )'
                 % (BM, ST, DEN(BM), HMAP, BM, DEN(BM)))], 'mpd',
             '( %s ` %s ) = %s' % (HMAP, BM, DEN(BM)))
    be1 = sm([sm([f1st], 'fveq2d',
                 '( %s ` ( 1st ` ( %s ` m ) ) ) = ( %s ` %s )' % (GMAP, FMAP, GMAP, KM)),
              gkv], 'eqtrd', '( %s ` ( 1st ` ( %s ` m ) ) ) = %s' % (GMAP, FMAP, DEN(ZKM)))
    be2 = sm([sm([f2nd], 'fveq2d',
                 '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( %s ` %s )' % (HMAP, FMAP, HMAP, BM)),
              hbv], 'eqtrd', '( %s ` ( 2nd ` ( %s ` m ) ) ) = %s' % (HMAP, FMAP, DEN(BM)))
    bmul = sm([be1, be2], 'oveq12d', '%s = ( %s x. %s )' % (BODY, DEN(ZKM), DEN(BM)))
    # the two factors are coprime and the density is multiplicative
    mfz = sm([lift(w, suss, AM), msu], 'sseldd', 'm e. ( 1 ... C )')
    mnn = sm([mfz, w.inst('elfznn')], 'syl', 'm e. NN')
    kn0 = sm([lift(w, zp, AM), mnn, w.inst('pccl')], 'syl2anc', '%s e. NN0' % KM)
    zknn = sm([lift(w, znn, AM), kn0], 'nnexpcld', '%s e. NN' % ZKM)
    bfz = sm([lift(w, stss, AM), bst], 'sseldd', '%s e. ( 1 ... C )' % BM)
    bnn = sm([bfz, w.inst('elfznn')], 'syl', '%s e. NN' % BM)
    nzb = sm([lift(w, zp, AM), mnn, w.inst('pcndvds2')], 'syl2anc', '-. Z || %s' % BM)
    cop0 = sm([sm([lift(w, zp, AM), sm([bnn], 'nnzd', '%s e. ZZ' % BM), w.inst('coprm')],
                  'syl2anc', '( -. Z || %s <-> ( Z gcd %s ) = 1 )' % (BM, BM)), nzb], 'mpbid',
              '( Z gcd %s ) = 1' % BM)
    cop = sm([sm([lift(w, zz, AM), sm([bnn], 'nnzd', '%s e. ZZ' % BM), kn0], '3jca',
                 '( Z e. ZZ /\ %s e. ZZ /\ %s e. NN0 )' % (BM, KM)),
              w.inst('rpexp1i')], 'sylc', '( %s gcd %s ) = 1' % (ZKM, BM))
    sgm = sm([sm([sm([w.s([], '0cn', '0 e. CC')], 'a1i', '0 e. CC'),
                  sm([zknn, bnn, cop], '3jca',
                     '( %s e. NN /\ %s e. NN /\ ( %s gcd %s ) = 1 )' % (ZKM, BM, ZKM, BM))],
                 'jca',
                 '( 0 e. CC /\ ( %s e. NN /\ %s e. NN /\ ( %s gcd %s ) = 1 ) )'
                 % (ZKM, BM, ZKM, BM)), w.inst('sgmmul')], 'syl',
             '( 0 sigma ( %s x. %s ) ) = ( ( 0 sigma %s ) x. ( 0 sigma %s ) )'
             % (ZKM, BM, ZKM, BM))
    sgzk = sm([sm([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), zknn,
               w.inst('sgmnncl')], 'syl2anc', '( 0 sigma %s ) e. NN' % ZKM)
    sgb = sm([sm([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), bnn,
              w.inst('sgmnncl')], 'syl2anc', '( 0 sigma %s ) e. NN' % BM)
    dmd = sm([sm([sm([sgzk], 'nncnd', '( 0 sigma %s ) e. CC' % ZKM),
                  sm([sgb], 'nncnd', '( 0 sigma %s ) e. CC' % BM)], 'jca',
                 '( ( 0 sigma %s ) e. CC /\ ( 0 sigma %s ) e. CC )' % (ZKM, BM)),
              sm([sm([sm([zknn], 'nncnd', '%s e. CC' % ZKM),
                      sm([zknn], 'nnne0d', '%s =/= 0' % ZKM)], 'jca',
                     '( %s e. CC /\ %s =/= 0 )' % (ZKM, ZKM)),
                  sm([sm([bnn], 'nncnd', '%s e. CC' % BM),
                      sm([bnn], 'nnne0d', '%s =/= 0' % BM)], 'jca',
                     '( %s e. CC /\ %s =/= 0 )' % (BM, BM))], 'jca',
                 '( ( %s e. CC /\ %s =/= 0 ) /\ ( %s e. CC /\ %s =/= 0 ) )'
                 % (ZKM, ZKM, BM, BM)), w.inst('divmuldiv')], 'syl2anc',
             '( %s x. %s ) = ( ( ( 0 sigma %s ) x. ( 0 sigma %s ) ) / ( %s x. %s ) )'
             % (DEN(ZKM), DEN(BM), ZKM, BM, ZKM, BM))
    num = sm([sm([sgm], 'eqcomd',
                 '( ( 0 sigma %s ) x. ( 0 sigma %s ) ) = ( 0 sigma ( %s x. %s ) )'
                 % (ZKM, BM, ZKM, BM)),
              sm([prod], 'oveq2d',
                 '( 0 sigma ( %s x. %s ) ) = ( 0 sigma m )' % (ZKM, BM))], 'eqtrd',
             '( ( 0 sigma %s ) x. ( 0 sigma %s ) ) = ( 0 sigma m )' % (ZKM, BM))
    dmd2 = sm([dmd, sm([num, prod], 'oveq12d',
                       '( ( ( 0 sigma %s ) x. ( 0 sigma %s ) ) / ( %s x. %s ) ) = %s'
                       % (ZKM, BM, ZKM, BM, DEN('m')))], 'eqtrd',
              '( %s x. %s ) = %s' % (DEN(ZKM), DEN(BM), DEN('m')))
    bodyfin = sm([bmul, dmd2], 'eqtrd', '%s = %s' % (BODY, DEN('m')))
    lsum = st([bodyfin], 'sumeq2dv', '%s = sum_ m e. %s %s' % (SBODY, SU, DEN('m')))
    cbvm = w.s([w.s([w.s([], 'oveq2', '( m = j -> ( 0 sigma m ) = ( 0 sigma j ) )'),
                     w.s([], 'id', '( m = j -> m = j )')], 'oveq12d',
                    '( m = j -> %s = %s )' % (DEN('m'), DEN('j')))], 'cbvsumv',
               'sum_ m e. %s %s = %s' % (SU, DEN('m'), SUMS(QZ)))
    lsum2 = st([lsum, st([cbvm], 'a1i', 'sum_ m e. %s %s = %s' % (SU, DEN('m'), SUMS(QZ)))],
               'eqtrd', '%s = %s' % (SBODY, SUMS(QZ)))
    main = st([lsum2, spu2], 'eqbrtrrd',
              '%s <_ ( sum_ i e. ( 1 ... C ) %s x. %s )'
              % (SUMS(QZ), DEN('( Z ^ i )'), SUMS('Q')))
    # the prime-power sum is at most the Euler factor at Z
    cbvk = w.s([w.s([w.s([w.s([], 'oveq2', '( i = k -> ( Z ^ i ) = ( Z ^ k ) )')], 'oveq2d',
                         '( i = k -> ( 0 sigma ( Z ^ i ) ) = ( 0 sigma ( Z ^ k ) ) )'),
                     w.s([], 'oveq2', '( i = k -> ( Z ^ i ) = ( Z ^ k ) )')], 'oveq12d',
                    '( i = k -> %s = %s )' % (DEN('( Z ^ i )'), DEN('( Z ^ k )')))], 'cbvsumv',
               'sum_ i e. ( 1 ... C ) %s = sum_ k e. ( 1 ... C ) %s'
               % (DEN('( Z ^ i )'), DEN('( Z ^ k )')))
    pwle0 = st([st([zp, z3, st([cnn], 'nnnn0d', 'C e. NN0')], '3jca',
                   '( Z e. Prime /\ 3 <_ Z /\ C e. NN0 )'), w.inst('sgmpwle')], 'syl',
               'sum_ k e. ( 1 ... C ) %s <_ %s' % (DEN('( Z ^ k )'), FACT('Z')))
    pwle = st([st([cbvk], 'a1i',
                  'sum_ i e. ( 1 ... C ) %s = sum_ k e. ( 1 ... C ) %s'
                  % (DEN('( Z ^ i )'), DEN('( Z ^ k )'))), pwle0], 'eqbrtrd',
              'sum_ i e. ( 1 ... C ) %s <_ %s' % (DEN('( Z ^ i )'), FACT('Z')))
    # closures for the final arithmetic
    zfacrp = factrp(w, AE, 'Z', znn, z3)
    zfacre = st([zfacrp], 'rpred', '%s e. RR' % FACT('Z'))
    AN = '( %s /\ n e. Q )' % AE
    sn = mkst(w, AN)
    nprm = sn([lift(w, qprm, AN), sn([], 'simpr', 'n e. Q')], 'sseldd', 'n e. Prime')
    nnn = sn([nprm, w.inst('prmnn')], 'syl', 'n e. NN')
    sbe = w.s([], 'breq2', '( e = n -> ( 3 <_ e <-> 3 <_ n ) )')
    n3 = sn([sbe, lift(w, qge3, AN), sn([], 'simpr', 'n e. Q')], 'rspcdva', '3 <_ n')
    nfacrp = factrp(w, AN, 'n', nnn, n3)
    prqrp = st([qfin, nfacrp], 'fprodrpcl', '%s e. RR+' % PRODQ('Q'))
    prqre = st([prqrp], 'rpred', '%s e. RR' % PRODQ('Q'))
    prqge = st([prqrp], 'rpge0d', '0 <_ %s' % PRODQ('Q'))
    girp = si([si([si([si([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'),
                      si([lift(w, znn, AI), si([si([ifz, w.inst('elfznn')], 'syl', 'i e. NN')],
                                               'nnnn0d', 'i e. NN0')], 'nnexpcld',
                         '( Z ^ i ) e. NN')], 'syl2anc', '( 0 sigma ( Z ^ i ) ) e. NN')],
                  'nnrpd', '( 0 sigma ( Z ^ i ) ) e. RR+'),
               si([lift(w, zrp, AI), si([si([ifz, w.inst('elfznn')], 'syl', 'i e. NN')],
                                        'nnzd', 'i e. ZZ')], 'rpexpcld',
                  '( Z ^ i ) e. RR+')], 'rpdivcld',
              '%s e. RR+' % DEN('( Z ^ i )'))
    gire = si([girp], 'rpred', '%s e. RR' % DEN('( Z ^ i )'))
    gige = si([girp], 'rpge0d', '0 <_ %s' % DEN('( Z ^ i )'))
    geore = st([fz1, gire], 'fsumrecl', 'sum_ i e. ( 1 ... C ) %s e. RR' % DEN('( Z ^ i )'))
    geoge = st([fz1, gire, gige], 'fsumge0',
               '0 <_ sum_ i e. ( 1 ... C ) %s' % DEN('( Z ^ i )'))
    jrire = sj([sj([sj([sj([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'),
                       sj([sj([lift(w, stss, AJ), jst], 'sseldd', 'j e. ( 1 ... C )'),
                           w.inst('elfznn')], 'syl', 'j e. NN')], 'syl2anc',
                    '( 0 sigma j ) e. NN')], 'nnrpd', '( 0 sigma j ) e. RR+'),
                sj([sj([sj([lift(w, stss, AJ), jst], 'sseldd', 'j e. ( 1 ... C )'),
                        w.inst('elfznn')], 'syl', 'j e. NN')], 'nnrpd', 'j e. RR+')],
               'rpdivcld', '%s e. RR+' % DEN('j'))
    jre = sj([jrire], 'rpred', '%s e. RR' % DEN('j'))
    jge = sj([jrire], 'rpge0d', '0 <_ %s' % DEN('j'))
    sstre = st([stfin, jre], 'fsumrecl', '%s e. RR' % SUMS('Q'))
    sstge = st([stfin, jre, jge], 'fsumge0', '0 <_ %s' % SUMS('Q'))
    AJU = '( %s /\ j e. %s )' % (AE, SU)
    sju = mkst(w, AJU)
    jure = sju([sju([sju([sju([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'),
                         sju([sju([lift(w, suss, AJU), sju([], 'simpr', 'j e. %s' % SU)],
                                  'sseldd', 'j e. ( 1 ... C )'), w.inst('elfznn')], 'syl',
                              'j e. NN')], 'syl2anc', '( 0 sigma j ) e. NN')], 'nnrpd',
                     '( 0 sigma j ) e. RR+'),
                sju([sju([sju([lift(w, suss, AJU), sju([], 'simpr', 'j e. %s' % SU)], 'sseldd',
                              'j e. ( 1 ... C )'), w.inst('elfznn')], 'syl', 'j e. NN')],
                    'nnrpd', 'j e. RR+')], 'rpdivcld', '%s e. RR+' % DEN('j'))
    ssure = st([sufin, sju([jure], 'rpred', '%s e. RR' % DEN('j'))], 'fsumrecl',
               '%s e. RR' % SUMS(QZ))
    # the product splits off the factor at Z
    nfn = w.s([], 'nfv', 'F/ n %s' % AE)
    nfd = w.s([], 'nfcv', 'F/_ n %s' % FACT('Z'))
    subn = w.s([w.s([], 'oveq2', '( n = Z -> ( 2 / n ) = ( 2 / Z ) )'),
                w.s([w.s([], 'oveq2', '( n = Z -> ( 2 / n ) = ( 2 / Z ) )')], 'oveq2d',
                    '( n = Z -> ( 1 - ( 2 / n ) ) = ( 1 - ( 2 / Z ) ) )')], 'oveq12d',
               '( n = Z -> %s = %s )' % (FACT('n'), FACT('Z')))
    zvv = st([st([znn], 'nnred', 'Z e. RR')], 'elexd', 'Z e. _V')
    zfacc = st([zfacre], 'recnd', '%s e. CC' % FACT('Z'))
    nfacc = sn([sn([nfacrp], 'rpred', '%s e. RR' % FACT('n'))], 'recnd', '%s e. CC' % FACT('n'))
    psplit = st([nfn, nfd, qfin, zvv, nzq, nfacc, subn, zfacc], 'fprodsplitsn',
                '%s = ( %s x. %s )' % (PRODQ(QZ), PRODQ('Q'), FACT('Z')))
    # final arithmetic under the induction hypothesis
    AIH = '( %s /\ %s <_ %s )' % (AE, SUMS('Q'), PRODQ('Q'))
    sih = mkst(w, AIH)
    ih = sih([], 'simpr', '%s <_ %s' % (SUMS('Q'), PRODQ('Q')))
    mulle = nlinarith(w, AIH, [lift(w, pwle, AIH), ih, lift(w, geoge, AIH),
                               lift(w, sstge, AIH)],
                      '( sum_ i e. ( 1 ... C ) %s x. %s ) <_ ( %s x. %s )'
                      % (DEN('( Z ^ i )'), SUMS('Q'), FACT('Z'), PRODQ('Q')),
                      leaves={'sum_ i e. ( 1 ... C ) %s' % DEN('( Z ^ i )'):
                              lift(w, geore, AIH),
                              SUMS('Q'): lift(w, sstre, AIH),
                              FACT('Z'): lift(w, zfacre, AIH),
                              PRODQ('Q'): lift(w, prqre, AIH)})
    prodre = st([zfacre, prqre], 'remulcld', '( %s x. %s ) e. RR' % (FACT('Z'), PRODQ('Q')))
    prodre2 = st([geore, sstre], 'remulcld',
                 '( sum_ i e. ( 1 ... C ) %s x. %s ) e. RR' % (DEN('( Z ^ i )'), SUMS('Q')))
    chain = sih([lift(w, ssure, AIH), lift(w, prodre2, AIH), lift(w, prodre, AIH),
                 lift(w, main, AIH), mulle], 'letrd',
                '%s <_ ( %s x. %s )' % (SUMS(QZ), FACT('Z'), PRODQ('Q')))
    comm = st([zfacc, st([prqre], 'recnd', '%s e. CC' % PRODQ('Q'))], 'mulcomd',
              '( %s x. %s ) = ( %s x. %s )'
              % (FACT('Z'), PRODQ('Q'), PRODQ('Q'), FACT('Z')))
    eqp = st([comm, st([psplit], 'eqcomd',
                       '( %s x. %s ) = %s' % (PRODQ('Q'), FACT('Z'), PRODQ(QZ)))], 'eqtrd',
             '( %s x. %s ) = %s' % (FACT('Z'), PRODQ('Q'), PRODQ(QZ)))
    fin = sih([chain, lift(w, eqp, AIH)], 'breqtrd', '%s <_ %s' % (SUMS(QZ), PRODQ(QZ)))
    w.qed([fin], 'ex',
          '( %s -> ( %s <_ %s -> %s <_ %s ) )'
          % (AE, SUMS('Q'), PRODQ('Q'), SUMS(QZ), PRODQ(QZ)))
    return w


ALL = {'rsstep': rsstep}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
