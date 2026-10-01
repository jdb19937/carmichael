"""Sortie v3: the inductive step of the smooth Euler-product bound."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst, SMS, smel
from cl import lift
from lin import linarith, nlinarith

QZ = '( Q u. { Z } )'
SU = SMS(QZ, 'W')
ST = SMS('Q', 'W')
AE = ('( ( ( Z e. Prime /\\ W e. NN ) /\\ ( Q e. Fin /\\ Q C_ Prime ) ) /\\ -. Z e. Q )')
RI = '( 1 / Z )'
SUB = '( 1 - ( 1 / Z ) )'
RZ = '( 1 / ( 1 - ( 1 / Z ) ) )'
PRQ = 'prod_ p e. Q ( 1 / ( 1 - ( 1 / p ) ) )'
PRQZ = 'prod_ p e. %s ( 1 / ( 1 - ( 1 / p ) ) )' % QZ
GEOK = 'sum_ k e. ( 0 ... W ) ( ( 1 / Z ) ^ k )'
GEOI = 'sum_ i e. ( 0 ... W ) ( ( 1 / Z ) ^ i )'
GMAP = '( n e. ( 0 ... W ) |-> ( ( 1 / Z ) ^ n ) )'
HMAP = '( o e. %s |-> ( 1 / o ) )' % ST
SST = 'sum_ j e. %s ( 1 / j )' % ST
SSU = 'sum_ j e. %s ( 1 / j )' % SU
SSUM = 'sum_ m e. %s ( 1 / m )' % SU


def PAIR(t):
    return '<. ( Z pCnt %s ) , ( %s / ( Z ^ ( Z pCnt %s ) ) ) >.' % (t, t, t)


FMAP = '( t e. %s |-> %s )' % (SU, PAIR('t'))
XW = '( ( 0 ... W ) X. %s )' % ST
BODY = '( ( %s ` ( 1st ` ( %s ` m ) ) ) x. ( %s ` ( 2nd ` ( %s ` m ) ) ) )' % (GMAP, FMAP, HMAP, FMAP)
SBODY = 'sum_ m e. %s %s' % (SU, BODY)


def rege0(w, ante, expr, rp):
    """( ante -> expr e. ( 0 [,) +oo ) ) from ( ante -> expr e. RR+ )"""
    f = mkst(w, ante)
    return f([f([rp], 'rpred', '%s e. RR' % expr), f([rp], 'rpge0d', '0 <_ %s' % expr),
              f([w.s([], 'elrege0',
                     '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
                'a1i',
                '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
             'mpbir2and', '%s e. ( 0 [,) +oo )' % expr)


def smsumstep():
    w = WS('smsumstep', 'The inductive step of the smooth Euler-product bound: adjoining one '
                        'prime to the smoothness set multiplies the bound by its Euler factor.')
    st = mkst(w, AE)
    zp = st([], 'simplll', 'Z e. Prime')
    wnn = st([], 'simpllr', 'W e. NN')
    qfin = st([], 'simplrl', 'Q e. Fin')
    qprm = st([], 'simplrr', 'Q C_ Prime')
    nzq = st([], 'simpr', '-. Z e. Q')
    # ranges are finite
    fzfin = st([], 'fzfid', '( 0 ... W ) e. Fin')
    fzfin1 = st([], 'fzfid', '( 1 ... W ) e. Fin')
    stss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... W )' % ST)], 'a1i', '%s C_ ( 1 ... W )' % ST)
    stfin = st([fzfin1, stss], 'ssfid', '%s e. Fin' % ST)
    suss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... W )' % SU)], 'a1i', '%s C_ ( 1 ... W )' % SU)
    sufin = st([fzfin1, suss], 'ssfid', '%s e. Fin' % SU)
    # Z and 1 / Z
    znn = st([zp, w.inst('prmnn')], 'syl', 'Z e. NN')
    zrp = st([znn], 'nnrpd', 'Z e. RR+')
    zre = st([zrp], 'rpred', 'Z e. RR')
    rirp = st([zrp], 'rpreccld', '%s e. RR+' % RI)
    zge = st([st([zp, w.inst('prmuz2')], 'syl', 'Z e. ( ZZ>= ` 2 )'), w.inst('eluzle')],
             'syl', '2 <_ Z')
    z1lt = linarith(w, AE, [zge], '1 < Z', leaves={'Z': zre})
    zpos = st([zrp], 'rpgt0d', '0 < Z')
    rc = st([st([zre, zpos], 'jca', '( Z e. RR /\\ 0 < Z )'), w.inst('recgt1')], 'syl',
            '( 1 < Z <-> %s < 1 )' % RI)
    rilt = st([rc, z1lt], 'mpbid', '%s < 1' % RI)
    rire = st([rirp], 'rpred', '%s e. RR' % RI)
    rige = st([rirp], 'rpge0d', '0 <_ %s' % RI)
    one = st([], '1red', '1 e. RR')
    subr = st([one, rire], 'resubcld', '%s e. RR' % SUB)
    sub0 = st([st([rire, one], 'posdifd', '( %s < 1 <-> 0 < %s )' % (RI, SUB)), rilt],
              'mpbid', '0 < %s' % SUB)
    subrp = st([subr, sub0], 'elrpd', '%s e. RR+' % SUB)
    rzrp = st([subrp], 'rpreccld', '%s e. RR+' % RZ)
    rzre = st([rzrp], 'rpred', '%s e. RR' % RZ)
    rzge = st([rzrp], 'rpge0d', '0 <_ %s' % RZ)
    # G is a nonnegative function on ( 0 ... W )
    AN = '( %s /\\ n e. ( 0 ... W ) )' % AE
    sn = mkst(w, AN)
    nn0 = sn([sn([], 'simpr', 'n e. ( 0 ... W )'), w.inst('elfznn0')], 'syl', 'n e. NN0')
    nz = sn([nn0], 'nn0zd', 'n e. ZZ')
    gnrp = sn([lift(w, rirp, AN), nz, w.inst('rpexpcl')], 'syl2anc', '( %s ^ n ) e. RR+' % RI)
    gn = rege0(w, AN, '( %s ^ n )' % RI, gnrp)
    gfn = st([gn, w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fmptd',
             '%s : ( 0 ... W ) --> ( 0 [,) +oo )' % GMAP)
    # H is a nonnegative function on ST
    AY = '( %s /\\ o e. %s )' % (AE, ST)
    sy = mkst(w, AY)
    yfz = sy([lift(w, stss, AY), sy([], 'simpr', 'o e. %s' % ST)], 'sseldd', 'o e. ( 1 ... W )')
    ynn = sy([yfz, w.inst('elfznn')], 'syl', 'o e. NN')
    hyrp = sy([sy([ynn], 'nnrpd', 'o e. RR+')], 'rpreccld', '( 1 / o ) e. RR+')
    hy = rege0(w, AY, '( 1 / o )', hyrp)
    hfn = st([hy, w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fmptd',
             '%s : %s --> ( 0 [,) +oo )' % (HMAP, ST))
    # F is injective
    f1 = st([st([zp, wnn], 'jca', '( Z e. Prime /\\ W e. NN )'), w.inst('smsumf1')], 'syl',
            '%s : %s -1-1-> %s' % (FMAP, SU, XW))
    # sumprodub
    spu = st([st([fzfin, stfin, sufin], '3jca',
                 '( ( 0 ... W ) e. Fin /\\ %s e. Fin /\\ %s e. Fin )' % (ST, SU)),
              st([gfn, hfn], 'jca',
                 '( %s : ( 0 ... W ) --> ( 0 [,) +oo ) /\\ %s : %s --> ( 0 [,) +oo ) )'
                 % (GMAP, HMAP, ST)), f1, w.inst('sumprodub')], 'syl3anc',
             '%s <_ ( sum_ i e. ( 0 ... W ) ( %s ` i ) x. sum_ j e. %s ( %s ` j ) )'
             % (SBODY, GMAP, ST, HMAP))
    # the two right-hand sums
    AI = '( %s /\\ i e. ( 0 ... W ) )' % AE
    si = mkst(w, AI)
    ifz = si([], 'simpr', 'i e. ( 0 ... W )')
    gival = si([si([ifz, si([w.s([], 'ovex', '( %s ^ i ) e. _V' % RI)], 'a1i',
                            '( %s ^ i ) e. _V' % RI)], 'jca',
                   '( i e. ( 0 ... W ) /\\ ( %s ^ i ) e. _V )' % RI),
                si([w.s([w.s([], 'oveq2', '( n = i -> ( %s ^ n ) = ( %s ^ i ) )' % (RI, RI)),
                         w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fvmptg',
                        '( ( i e. ( 0 ... W ) /\\ ( %s ^ i ) e. _V ) -> ( %s ` i ) = ( %s ^ i ) )'
                        % (RI, GMAP, RI))], 'a1i',
                   '( ( i e. ( 0 ... W ) /\\ ( %s ^ i ) e. _V ) -> ( %s ` i ) = ( %s ^ i ) )'
                   % (RI, GMAP, RI))], 'mpd', '( %s ` i ) = ( %s ^ i )' % (GMAP, RI))
    gsum = st([gival], 'sumeq2dv', 'sum_ i e. ( 0 ... W ) ( %s ` i ) = %s' % (GMAP, GEOI))
    AJ = '( %s /\\ j e. %s )' % (AE, ST)
    sj = mkst(w, AJ)
    jst = sj([], 'simpr', 'j e. %s' % ST)
    hjval = sj([sj([jst, sj([w.s([], 'ovex', '( 1 / j ) e. _V')], 'a1i', '( 1 / j ) e. _V')],
                   'jca', '( j e. %s /\\ ( 1 / j ) e. _V )' % ST),
                sj([w.s([w.s([], 'oveq2', '( o = j -> ( 1 / o ) = ( 1 / j ) )'),
                         w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fvmptg',
                        '( ( j e. %s /\\ ( 1 / j ) e. _V ) -> ( %s ` j ) = ( 1 / j ) )'
                        % (ST, HMAP))], 'a1i',
                   '( ( j e. %s /\\ ( 1 / j ) e. _V ) -> ( %s ` j ) = ( 1 / j ) )' % (ST, HMAP))],
               'mpd', '( %s ` j ) = ( 1 / j )' % HMAP)
    hsum = st([hjval], 'sumeq2dv', 'sum_ j e. %s ( %s ` j ) = %s' % (ST, HMAP, SST))
    rhs = st([gsum, hsum], 'oveq12d',
             '( sum_ i e. ( 0 ... W ) ( %s ` i ) x. sum_ j e. %s ( %s ` j ) ) = ( %s x. %s )'
             % (GMAP, ST, HMAP, GEOI, SST))
    spu2 = st([spu, rhs], 'breqtrd', '%s <_ ( %s x. %s )' % (SBODY, GEOI, SST))
    # the left-hand body is 1 / m
    AM = '( %s /\\ m e. %s )' % (AE, SU)
    sm = mkst(w, AM)
    msu = sm([], 'simpr', 'm e. %s' % SU)
    spl = sm([sm([sm([lift(w, zp, AM), lift(w, wnn, AM)], 'jca', '( Z e. Prime /\\ W e. NN )'),
                  msu], 'jca', '( ( Z e. Prime /\\ W e. NN ) /\\ m e. %s )' % SU),
              w.inst('smsplit')], 'syl',
             '( ( Z pCnt m ) e. ( 0 ... W ) /\\ ( m / ( Z ^ ( Z pCnt m ) ) ) e. %s /\\ '
             '( ( Z ^ ( Z pCnt m ) ) x. ( m / ( Z ^ ( Z pCnt m ) ) ) ) = m )' % ST)
    kfz = sm([spl], 'simp1d', '( Z pCnt m ) e. ( 0 ... W )')
    bst = sm([spl], 'simp2d', '( m / ( Z ^ ( Z pCnt m ) ) ) e. %s' % ST)
    prod = sm([spl], 'simp3d',
              '( ( Z ^ ( Z pCnt m ) ) x. ( m / ( Z ^ ( Z pCnt m ) ) ) ) = m')
    # ( FMAP ` m ) = PAIR( m )
    cb1 = w.s([], 'oveq2', '( t = m -> ( Z pCnt t ) = ( Z pCnt m ) )')
    cb2 = w.s([w.s([], 'id', '( t = m -> t = m )'),
               w.s([cb1], 'oveq2d', '( t = m -> ( Z ^ ( Z pCnt t ) ) = ( Z ^ ( Z pCnt m ) ) )')],
              'oveq12d',
              '( t = m -> ( t / ( Z ^ ( Z pCnt t ) ) ) = ( m / ( Z ^ ( Z pCnt m ) ) ) )')
    cb = w.s([cb1, cb2], 'opeq12d', '( t = m -> %s = %s )' % (PAIR('t'), PAIR('m')))
    fmv = sm([sm([msu, sm([w.s([], 'opex', '%s e. _V' % PAIR('m'))], 'a1i',
                          '%s e. _V' % PAIR('m'))], 'jca',
                 '( m e. %s /\\ %s e. _V )' % (SU, PAIR('m'))),
              sm([w.s([cb, w.s([], 'eqid', '%s = %s' % (FMAP, FMAP))], 'fvmptg',
                      '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )'
                      % (SU, PAIR('m'), FMAP, PAIR('m')))], 'a1i',
                 '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )'
                 % (SU, PAIR('m'), FMAP, PAIR('m')))], 'mpd',
             '( %s ` m ) = %s' % (FMAP, PAIR('m')))
    kex = w.s([], 'ovex', '( Z pCnt m ) e. _V')
    bex = w.s([], 'ovex', '( m / ( Z ^ ( Z pCnt m ) ) ) e. _V')
    o1 = w.s([kex, bex], 'op1st', '( 1st ` %s ) = ( Z pCnt m )' % PAIR('m'))
    o2 = w.s([kex, bex], 'op2nd',
             '( 2nd ` %s ) = ( m / ( Z ^ ( Z pCnt m ) ) )' % PAIR('m'))
    f1st = sm([sm([fmv], 'fveq2d', '( 1st ` ( %s ` m ) ) = ( 1st ` %s )' % (FMAP, PAIR('m'))),
               sm([o1], 'a1i', '( 1st ` %s ) = ( Z pCnt m )' % PAIR('m'))], 'eqtrd',
              '( 1st ` ( %s ` m ) ) = ( Z pCnt m )' % FMAP)
    f2nd = sm([sm([fmv], 'fveq2d', '( 2nd ` ( %s ` m ) ) = ( 2nd ` %s )' % (FMAP, PAIR('m'))),
               sm([o2], 'a1i',
                  '( 2nd ` %s ) = ( m / ( Z ^ ( Z pCnt m ) ) )' % PAIR('m'))], 'eqtrd',
              '( 2nd ` ( %s ` m ) ) = ( m / ( Z ^ ( Z pCnt m ) ) )' % FMAP)
    gkv = sm([sm([kfz, sm([w.s([], 'ovex', '( %s ^ ( Z pCnt m ) ) e. _V' % RI)], 'a1i',
                          '( %s ^ ( Z pCnt m ) ) e. _V' % RI)], 'jca',
                 '( ( Z pCnt m ) e. ( 0 ... W ) /\\ ( %s ^ ( Z pCnt m ) ) e. _V )' % RI),
              sm([w.s([w.s([], 'oveq2',
                            '( n = ( Z pCnt m ) -> ( %s ^ n ) = ( %s ^ ( Z pCnt m ) ) )' % (RI, RI)),
                       w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fvmptg',
                      '( ( ( Z pCnt m ) e. ( 0 ... W ) /\\ ( %s ^ ( Z pCnt m ) ) e. _V ) -> '
                      '( %s ` ( Z pCnt m ) ) = ( %s ^ ( Z pCnt m ) ) )' % (RI, GMAP, RI))], 'a1i',
                 '( ( ( Z pCnt m ) e. ( 0 ... W ) /\\ ( %s ^ ( Z pCnt m ) ) e. _V ) -> '
                 '( %s ` ( Z pCnt m ) ) = ( %s ^ ( Z pCnt m ) ) )' % (RI, GMAP, RI))], 'mpd',
             '( %s ` ( Z pCnt m ) ) = ( %s ^ ( Z pCnt m ) )' % (GMAP, RI))
    BQ = '( m / ( Z ^ ( Z pCnt m ) ) )'
    hbv = sm([sm([bst, sm([w.s([], 'ovex', '( 1 / %s ) e. _V' % BQ)], 'a1i',
                          '( 1 / %s ) e. _V' % BQ)], 'jca',
                 '( %s e. %s /\\ ( 1 / %s ) e. _V )' % (BQ, ST, BQ)),
              sm([w.s([w.s([], 'oveq2', '( o = %s -> ( 1 / o ) = ( 1 / %s ) )' % (BQ, BQ)),
                       w.s([], 'eqid', '%s = %s' % (HMAP, HMAP))], 'fvmptg',
                      '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                      % (BQ, ST, BQ, HMAP, BQ, BQ))], 'a1i',
                 '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                 % (BQ, ST, BQ, HMAP, BQ, BQ))], 'mpd',
             '( %s ` %s ) = ( 1 / %s )' % (HMAP, BQ, BQ))
    bodyeq1 = sm([sm([f1st], 'fveq2d',
                     '( %s ` ( 1st ` ( %s ` m ) ) ) = ( %s ` ( Z pCnt m ) )' % (GMAP, FMAP, GMAP)),
                  gkv], 'eqtrd',
                 '( %s ` ( 1st ` ( %s ` m ) ) ) = ( %s ^ ( Z pCnt m ) )' % (GMAP, FMAP, RI))
    bodyeq2 = sm([sm([f2nd], 'fveq2d',
                     '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( %s ` %s )' % (HMAP, FMAP, HMAP, BQ)),
                  hbv], 'eqtrd',
                 '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( 1 / %s )' % (HMAP, FMAP, BQ))
    bodymul = sm([bodyeq1, bodyeq2], 'oveq12d',
                 '%s = ( ( %s ^ ( Z pCnt m ) ) x. ( 1 / %s ) )' % (BODY, RI, BQ))
    # ( ( 1 / Z ) ^ K ) x. ( 1 / B ) = ( 1 / m )
    ZK = '( Z ^ ( Z pCnt m ) )'
    mnn = sm([sm([lift(w, suss, AM), msu], 'sseldd', 'm e. ( 1 ... W )'), w.inst('elfznn')],
             'syl', 'm e. NN')
    kn0 = sm([lift(w, zp, AM), mnn, w.inst('pccl')], 'syl2anc', '( Z pCnt m ) e. NN0')
    zknn = sm([lift(w, znn, AM), kn0], 'nnexpcld', '%s e. NN' % ZK)
    onec = sm([sm([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    zc = sm([lift(w, znn, AM)], 'nncnd', 'Z e. CC')
    zne = sm([lift(w, znn, AM)], 'nnne0d', 'Z =/= 0')
    ed = sm([onec, sm([zc, zne], 'jca', '( Z e. CC /\\ Z =/= 0 )'), kn0,
             w.inst('expdiv')], 'syl3anc',
            '( %s ^ ( Z pCnt m ) ) = ( ( 1 ^ ( Z pCnt m ) ) / %s )' % (RI, ZK))
    oe = sm([sm([kn0], 'nn0zd', '( Z pCnt m ) e. ZZ'), w.inst('1exp')], 'syl',
            '( 1 ^ ( Z pCnt m ) ) = 1')
    ed2 = sm([ed, sm([oe], 'oveq1d',
                     '( ( 1 ^ ( Z pCnt m ) ) / %s ) = ( 1 / %s )' % (ZK, ZK))], 'eqtrd',
             '( %s ^ ( Z pCnt m ) ) = ( 1 / %s )' % (RI, ZK))
    bfz = sm([lift(w, stss, AM), bst], 'sseldd', '%s e. ( 1 ... W )' % BQ)
    bnn = sm([bfz, w.inst('elfznn')], 'syl', '%s e. NN' % BQ)
    zkc = sm([zknn], 'nncnd', '%s e. CC' % ZK)
    zkne = sm([zknn], 'nnne0d', '%s =/= 0' % ZK)
    bc = sm([bnn], 'nncnd', '%s e. CC' % BQ)
    bne = sm([bnn], 'nnne0d', '%s =/= 0' % BQ)
    dmd = sm([sm([onec, onec], 'jca', '( 1 e. CC /\\ 1 e. CC )'),
              sm([sm([zkc, zkne], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (ZK, ZK)),
                  sm([bc, bne], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (BQ, BQ))], 'jca',
                 '( ( %s e. CC /\\ %s =/= 0 ) /\\ ( %s e. CC /\\ %s =/= 0 ) )'
                 % (ZK, ZK, BQ, BQ)), w.inst('divmuldiv')], 'syl2anc',
             '( ( 1 / %s ) x. ( 1 / %s ) ) = ( ( 1 x. 1 ) / ( %s x. %s ) )' % (ZK, BQ, ZK, BQ))
    t11 = sm([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')
    dmd2 = sm([dmd, sm([sm([t11], 'oveq1d',
                           '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / ( %s x. %s ) )'
                           % (ZK, BQ, ZK, BQ)),
                        sm([prod], 'oveq2d',
                           '( 1 / ( %s x. %s ) ) = ( 1 / m )' % (ZK, BQ))], 'eqtrd',
                       '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / m )' % (ZK, BQ))], 'eqtrd',
              '( ( 1 / %s ) x. ( 1 / %s ) ) = ( 1 / m )' % (ZK, BQ))
    bodyfin = sm([bodymul, sm([sm([ed2], 'oveq1d',
                                  '( ( %s ^ ( Z pCnt m ) ) x. ( 1 / %s ) ) = '
                                  '( ( 1 / %s ) x. ( 1 / %s ) )' % (RI, BQ, ZK, BQ)),
                               dmd2], 'eqtrd',
                              '( ( %s ^ ( Z pCnt m ) ) x. ( 1 / %s ) ) = ( 1 / m )' % (RI, BQ))],
                 'eqtrd', '%s = ( 1 / m )' % BODY)
    lsum = st([bodyfin], 'sumeq2dv', '%s = %s' % (SBODY, SSUM))
    cbv = st([w.s([w.s([], 'oveq2', '( m = j -> ( 1 / m ) = ( 1 / j ) )')], 'cbvsumv',
                  '%s = %s' % (SSUM, SSU))], 'a1i', '%s = %s' % (SSUM, SSU))
    lsum2 = st([lsum, cbv], 'eqtrd', '%s = %s' % (SBODY, SSU))
    main = st([lsum2, spu2], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (SSU, GEOI, SST))
    # the geometric bound
    wn0 = st([wnn], 'nnnn0d', 'W e. NN0')
    geo = st([st([st([rire, rige, rilt], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s < 1 )' % (RI, RI, RI)),
                 wn0], 'jca',
                '( ( %s e. RR /\\ 0 <_ %s /\\ %s < 1 ) /\\ W e. NN0 )' % (RI, RI, RI)),
              w.inst('geosrle')], 'syl', '%s <_ %s' % (GEOK, RZ))
    cbg = st([w.s([w.s([], 'oveq2', '( k = i -> ( %s ^ k ) = ( %s ^ i ) )' % (RI, RI))],
                 'cbvsumv', '%s = %s' % (GEOK, GEOI))], 'a1i', '%s = %s' % (GEOK, GEOI))
    geo2 = st([cbg, geo], 'eqbrtrrd', '%s <_ %s' % (GEOI, RZ))
    # the product splits off the factor at Z
    AP = '( %s /\\ p e. Q )' % AE
    sp = mkst(w, AP)
    pprm = sp([lift(w, qprm, AP), sp([], 'simpr', 'p e. Q')], 'sseldd', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    pre = sp([prp], 'rpred', 'p e. RR')
    ppos = sp([prp], 'rpgt0d', '0 < p')
    pge = sp([sp([pprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'), w.inst('eluzle')],
             'syl', '2 <_ p')
    p1lt = linarith(w, AP, [pge], '1 < p', leaves={'p': pre})
    prc = sp([sp([sp([pre, ppos], 'jca', '( p e. RR /\\ 0 < p )'), w.inst('recgt1')], 'syl',
                 '( 1 < p <-> ( 1 / p ) < 1 )'), p1lt], 'mpbid', '( 1 / p ) < 1')
    prirp = sp([prp], 'rpreccld', '( 1 / p ) e. RR+')
    prire = sp([prirp], 'rpred', '( 1 / p ) e. RR')
    pone = sp([], '1red', '1 e. RR')
    psubr = sp([pone, prire], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    psub0 = sp([sp([prire, pone], 'posdifd', '( ( 1 / p ) < 1 <-> 0 < ( 1 - ( 1 / p ) ) )'),
                prc], 'mpbid', '0 < ( 1 - ( 1 / p ) )')
    psubrp = sp([psubr, psub0], 'elrpd', '( 1 - ( 1 / p ) ) e. RR+')
    pfacrp = sp([psubrp], 'rpreccld', '( 1 / ( 1 - ( 1 / p ) ) ) e. RR+')
    pfacc = sp([sp([pfacrp], 'rpred', '( 1 / ( 1 - ( 1 / p ) ) ) e. RR')], 'recnd',
               '( 1 / ( 1 - ( 1 / p ) ) ) e. CC')
    prqrp = st([qfin, pfacrp], 'fprodrpcl', '%s e. RR+' % PRQ)
    prqre = st([prqrp], 'rpred', '%s e. RR' % PRQ)
    prqge = st([prqrp], 'rpge0d', '0 <_ %s' % PRQ)
    nfd = w.s([], 'nfcv', 'F/_ p %s' % RZ)
    zvex = st([st([znn], 'nnred', 'Z e. RR')], 'elexd', 'Z e. _V')
    subp = w.s([w.s([], 'oveq2', '( p = Z -> ( 1 / p ) = ( 1 / Z ) )')], 'oveq2d',
               '( p = Z -> ( 1 - ( 1 / p ) ) = ( 1 - ( 1 / Z ) ) )')
    subpz = w.s([subp], 'oveq2d', '( p = Z -> ( 1 / ( 1 - ( 1 / p ) ) ) = %s )' % RZ)
    rzc = st([rzre], 'recnd', '%s e. CC' % RZ)
    psplit = st([nfd, qfin, zvex, nzq, pfacc, subpz, rzc], 'fprodsplitsn',
                '%s = ( %s x. %s )' % (PRQZ, PRQ, RZ))
    # final arithmetic under the induction hypothesis
    AIH = '( %s /\\ %s <_ %s )' % (AE, SST, PRQ)
    sih = mkst(w, AIH)
    ih = sih([], 'simpr', '%s <_ %s' % (SST, PRQ))
    jfz = sj([lift(w, stss, AJ), jst], 'sseldd', 'j e. ( 1 ... W )')
    jnn = sj([jfz, w.inst('elfznn')], 'syl', 'j e. NN')
    jrirp = sj([sj([jnn], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jrire = sj([jrirp], 'rpred', '( 1 / j ) e. RR')
    jrige = sj([jrirp], 'rpge0d', '0 <_ ( 1 / j )')
    sstre = st([stfin, jrire], 'fsumrecl', '%s e. RR' % SST)
    sstge = st([stfin, jrire, jrige], 'fsumge0', '0 <_ %s' % SST)
    girp = si([lift(w, rirp, AI), si([si([ifz, w.inst('elfznn0')], 'syl', 'i e. NN0')], 'nn0zd',
                                     'i e. ZZ'), w.inst('rpexpcl')], 'syl2anc',
              '( %s ^ i ) e. RR+' % RI)
    gire = si([girp], 'rpred', '( %s ^ i ) e. RR' % RI)
    geore = st([fzfin, gire], 'fsumrecl', '%s e. RR' % GEOI)
    geoge = st([fzfin, gire, si([girp], 'rpge0d', '0 <_ ( %s ^ i )' % RI)], 'fsumge0',
               '0 <_ %s' % GEOI)
    AJU = '( %s /\\ j e. %s )' % (AE, SU)
    sju = mkst(w, AJU)
    jufz = sju([lift(w, suss, AJU), sju([], 'simpr', 'j e. %s' % SU)], 'sseldd',
               'j e. ( 1 ... W )')
    junn = sju([jufz, w.inst('elfznn')], 'syl', 'j e. NN')
    jurire = sju([sju([sju([junn], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')],
                 'rpred', '( 1 / j ) e. RR')
    ssure = st([sufin, jurire], 'fsumrecl', '%s e. RR' % SSU)
    mulle = nlinarith(w, AIH, [lift(w, geo2, AIH), ih, lift(w, geoge, AIH), lift(w, sstge, AIH)],
                      '( %s x. %s ) <_ ( %s x. %s )' % (GEOI, SST, RZ, PRQ),
                      leaves={GEOI: lift(w, geore, AIH), SST: lift(w, sstre, AIH),
                              RZ: lift(w, rzre, AIH), PRQ: lift(w, prqre, AIH)})
    prodre = st([rzre, prqre], 'remulcld', '( %s x. %s ) e. RR' % (RZ, PRQ))
    prodre2 = st([geore, sstre], 'remulcld', '( %s x. %s ) e. RR' % (GEOI, SST))
    chain = sih([lift(w, ssure, AIH), lift(w, prodre2, AIH), lift(w, prodre, AIH),
                 lift(w, main, AIH), mulle], 'letrd', '%s <_ ( %s x. %s )' % (SSU, RZ, PRQ))
    comm = st([rzc, st([prqre], 'recnd', '%s e. CC' % PRQ)], 'mulcomd',
              '( %s x. %s ) = ( %s x. %s )' % (RZ, PRQ, PRQ, RZ))
    eqp = st([comm, st([psplit], 'eqcomd', '( %s x. %s ) = %s' % (PRQ, RZ, PRQZ))], 'eqtrd',
             '( %s x. %s ) = %s' % (RZ, PRQ, PRQZ))
    fin = sih([chain, lift(w, eqp, AIH)], 'breqtrd', '%s <_ %s' % (SSU, PRQZ))
    w.qed([fin], 'ex', '( %s -> ( %s <_ %s -> %s <_ %s ) )' % (AE, SST, PRQ, SSU, PRQZ))
    return w


if __name__ == '__main__':
    smsumstep().run()
