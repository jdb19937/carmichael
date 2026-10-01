"""EF1 sections 4-5, helpers: ef1u4, ef1fzs, ef1pfr, the three kernel bounds ef1kl, ef1kr, ef1kt.
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_e.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from lin import linarith, lineq

only = sys.argv[1:]

# ---------------------------------------------------------------- ef1u4
if __name__ == '__main__' and (not only or 'ef1u4' in only):
    w = W('ef1u4', '` U ^ C <_ 4 ` for ` 0 < U <_ 2 ` , ` 0 < C <_ 2 ` (the ` ( y / n ) ^ c <_ 4 ` step of Lean ` kerErr_near ` ).')
    A0 = STATEMENTS['ef1u4'].split(' -> ( U')[0][2:]
    urp = D(w, A0, 'simpll', [], 'U e. RR+'); u2 = D(w, A0, 'simplr', [], 'U <_ 2')
    crp = D(w, A0, 'simprl', [], 'C e. RR+'); c2 = D(w, A0, 'simprr', [], 'C <_ 2')
    ur = D(w, A0, 'rpred', [urp], 'U e. RR'); cr = D(w, A0, 'rpred', [crp], 'C e. RR')
    r2 = a1(w, A0, '2re', '2 e. RR')
    bi = w.s([D(w, A0, 'jca', [ur, D(w, A0, 'rpge0d', [urp], '0 <_ U')], '( U e. RR /\\ 0 <_ U )'), D(w, A0, 'jca', [r2, a1(w, A0, '0le2', '0 <_ 2')], '( 2 e. RR /\\ 0 <_ 2 )'), crp,
              w.inst('cxple2')], 'syl3anc', '( %s -> ( U <_ 2 <-> ( U ^c C ) <_ ( 2 ^c C ) ) )' % A0)
    l1 = w.s([u2, bi], 'mpbid', '( %s -> ( U ^c C ) <_ ( 2 ^c C ) )' % A0)
    l2 = w.s([D(w, A0, 'jca', [r2, a1(w, A0, '1le2', '1 <_ 2')], '( 2 e. RR /\\ 1 <_ 2 )'), D(w, A0, 'jca', [cr, r2], '( C e. RR /\\ 2 e. RR )'), c2, w.inst('cxplea')], 'syl3anc',
             '( %s -> ( 2 ^c C ) <_ ( 2 ^c 2 ) )' % A0)
    e4 = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2nn0', '2 e. NN0'), w.inst('cxpexp')], 'mp2an', '( 2 ^c 2 ) = ( 2 ^ 2 )'), w.s([], 'sq2', '( 2 ^ 2 ) = 4')], 'eqtri', '( 2 ^c 2 ) = 4')
    l3 = w.s([l2, w.s([e4], 'a1i', '( %s -> ( 2 ^c 2 ) = 4 )' % A0)], 'breqtrd', '( %s -> ( 2 ^c C ) <_ 4 )' % A0)
    uc = D(w, A0, 'rpcxpcld', [urp, cr], '( U ^c C ) e. RR+')
    w.qed([D(w, A0, 'rpred', [uc], '( U ^c C ) e. RR'), D(w, A0, 'rpred', [D(w, A0, 'rpcxpcld', [a1(w, A0, '2rp', '2 e. RR+'), cr], '( 2 ^c C ) e. RR+')], '( 2 ^c C ) e. RR'),
           a1(w, A0, '4re', '4 e. RR'), l1, l3], 'letrd', STATEMENTS['ef1u4'])
    go(w, only)

# ---------------------------------------------------------------- ef1fzs
if __name__ == '__main__' and (not only or 'ef1fzs' in only):
    w = W('ef1fzs', 'A finite sum over an integer interval split at ` K ` ( ~ fzsplit , ~ fsumsplit ).')
    for nm, f in HYPS['ef1fzs']:
        w.s([], 'ef1fzs.%s' % nm, f, name='h' + nm)
    kz = w.s(['h1', w.inst('elfzelz')], 'syl', '( ph -> K e. ZZ )')
    kr = D(w, 'ph', 'zred', [kz], 'K e. RR')
    lt = D(w, 'ph', 'ltp1d', [kr], 'K < ( K + 1 )')
    dj = w.s([lt, w.inst('fzdisj')], 'syl', '( ph -> ( ( M ... K ) i^i ( ( K + 1 ) ... N ) ) = (/) )')
    un = w.s(['h1', w.inst('fzsplit')], 'syl', '( ph -> ( M ... N ) = ( ( M ... K ) u. ( ( K + 1 ) ... N ) ) )')
    w.qed([dj, un, w.s([], 'fzfid', '( ph -> ( M ... N ) e. Fin )'), 'h2'], 'fsumsplit', STATEMENTS['ef1fzs'])
    go(w, only)

# ---------------------------------------------------------------- ef1pfr: the partial-fraction sum
if __name__ == '__main__' and (not only or 'ef1pfr' in only):
    w = W('ef1pfr', 'The left gap sum in partial fractions: ` sum_ ( 1 <_ n < floor y ) y / ( n ( y - n ) ) <_ 2 ( 1 + log y ) ` , since '
          '` y / ( n ( y - n ) ) = 1 / n + 1 / ( y - n ) ` and both sums are harmonic sums up to ` floor y ` ( ~ harmonicubnd , ~ fsumrev ; Lean '
          '` sum_inv_gap_left ` with ` harmonic_le ` , used for the whole left of the diagonal).')
    A0 = '( Y e. RR /\\ 1 <_ Y )'
    F = '( |_ ` Y )'; FM = '( %s - 1 )' % F; IV = '( 1 ... %s )' % FM
    yr = D(w, A0, 'simpl', [], 'Y e. RR')
    fnn = w.s([], 'flge1nn', '( %s -> %s e. NN )' % (A0, F))
    fr = D(w, A0, 'nnred', [fnn], '%s e. RR' % F); fz = D(w, A0, 'nnzd', [fnn], '%s e. ZZ' % F); fc = D(w, A0, 'nncnd', [fnn], '%s e. CC' % F)
    fle = w.s([yr, w.inst('flle')], 'syl', '( %s -> %s <_ Y )' % (A0, F))
    AN_ = '( %s /\\ n e. %s )' % (A0, IV)
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (AN_, IV))
    nn = w.s([nin, w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AN_)
    nle = w.s([nin, w.inst('elfzle2')], 'syl', '( %s -> n <_ %s )' % (AN_, FM))
    nr = D(w, AN_, 'nnred', [nn], 'n e. RR'); ncc = D(w, AN_, 'nncnd', [nn], 'n e. CC'); nne = D(w, AN_, 'nnne0d', [nn], 'n =/= 0')
    yra = w.s([yr], 'adantr', '( %s -> Y e. RR )' % AN_); fra = w.s([fr], 'adantr', '( %s -> %s e. RR )' % (AN_, F)); flea = w.s([fle], 'adantr', '( %s -> %s <_ Y )' % (AN_, F))
    cl = Closure(w, AN_, {'Y': ('RR', yra), 'n': ('RR', nr), F: ('RR', fra)})
    ynp = linarith(w, AN_, [nle, flea], '0 < ( Y - n )', closure=cl)
    fnp = linarith(w, AN_, [nle], '0 < ( %s - n )' % F, closure=cl)
    ynrp = D(w, AN_, 'elrpd', [cl.mem('( Y - n )', 'RR'), ynp], '( Y - n ) e. RR+')
    fnrp = D(w, AN_, 'elrpd', [cl.mem('( %s - n )' % F, 'RR'), fnp], '( %s - n ) e. RR+' % F)
    ync = D(w, AN_, 'rpcnd', [ynrp], '( Y - n ) e. CC'); ynn = D(w, AN_, 'rpne0d', [ynrp], '( Y - n ) =/= 0')
    c1 = a1(w, AN_, 'ax-1cn', '1 e. CC')
    add = D(w, AN_, 'divadddivd', [c1, ncc, c1, ync, nne, ynn], '( ( 1 / n ) + ( 1 / ( Y - n ) ) ) = ( ( ( 1 x. ( Y - n ) ) + ( 1 x. n ) ) / ( n x. ( Y - n ) ) )')
    num = lineq(w, AN_, '( ( 1 x. ( Y - n ) ) + ( 1 x. n ) )', 'Y', closure=cl)
    ide = w.s([add, w.s([num], 'oveq1d', '( %s -> ( ( ( 1 x. ( Y - n ) ) + ( 1 x. n ) ) / ( n x. ( Y - n ) ) ) = ( Y / ( n x. ( Y - n ) ) ) )' % AN_)], 'eqtrd',
              '( %s -> ( ( 1 / n ) + ( 1 / ( Y - n ) ) ) = ( Y / ( n x. ( Y - n ) ) ) )' % AN_)
    s1 = w.s([w.s([ide], 'eqcomd', '( %s -> ( Y / ( n x. ( Y - n ) ) ) = ( ( 1 / n ) + ( 1 / ( Y - n ) ) ) )' % AN_)], 'sumeq2dv',
             '( %s -> sum_ n e. %s ( Y / ( n x. ( Y - n ) ) ) = sum_ n e. %s ( ( 1 / n ) + ( 1 / ( Y - n ) ) ) )' % (A0, IV, IV))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IV))
    rn = D(w, AN_, 'nnrecred', [nn], '( 1 / n ) e. RR')
    ryn = D(w, AN_, 'rpreccld', [ynrp], '( 1 / ( Y - n ) ) e. RR+')
    s2 = w.s([fin, D(w, AN_, 'recnd', [rn], '( 1 / n ) e. CC'), D(w, AN_, 'rpcnd', [ryn], '( 1 / ( Y - n ) ) e. CC')], 'fsumadd',
             '( %s -> sum_ n e. %s ( ( 1 / n ) + ( 1 / ( Y - n ) ) ) = ( sum_ n e. %s ( 1 / n ) + sum_ n e. %s ( 1 / ( Y - n ) ) ) )' % (A0, IV, IV, IV))
    # the harmonic sum up to F - 1
    HB = 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % F
    hb = w.s([], 'harmonicubnd', '( %s -> %s <_ ( ( log ` Y ) + 1 ) )' % (A0, HB))
    fuz = w.s([fnn, w.s([], 'elnnuz', '( %s e. NN <-> %s e. ( ZZ>= ` 1 ) )' % (F, F))], 'sylib', '( %s -> %s e. ( ZZ>= ` 1 ) )' % (A0, F))
    AM = '( %s /\\ m e. ( 1 ... %s ) )' % (A0, F)
    mrc = D(w, AM, 'recnd', [D(w, AM, 'nnrecred', [w.s([w.s([], 'simpr', '( %s -> m e. ( 1 ... %s ) )' % (AM, F)), w.inst('elfznn')], 'syl', '( %s -> m e. NN )' % AM)], '( 1 / m ) e. RR')], '( 1 / m ) e. CC')
    fm1 = w.s([fuz, mrc, w.s([], 'oveq2', '( m = %s -> ( 1 / m ) = ( 1 / %s ) )' % (F, F))], 'fsumm1', '( %s -> %s = ( sum_ m e. %s ( 1 / m ) + ( 1 / %s ) ) )' % (A0, HB, IV, F))
    AMI = '( %s /\\ m e. %s )' % (A0, IV)
    hsr = w.s([fin, D(w, AMI, 'nnrecred', [w.s([w.s([], 'simpr', '( %s -> m e. %s )' % (AMI, IV)), w.inst('elfznn')], 'syl', '( %s -> m e. NN )' % AMI)], '( 1 / m ) e. RR')], 'fsumrecl',
              '( %s -> sum_ m e. %s ( 1 / m ) e. RR )' % (A0, IV))
    HS = 'sum_ m e. %s ( 1 / m )' % IV
    ly = D(w, A0, 'relogcld', [D(w, A0, 'elrpd', [yr, linarith(w, A0, [D(w, A0, 'simpr', [], '1 <_ Y')], '0 < Y', closure=Closure(w, A0, {'Y': ('RR', yr)}))], 'Y e. RR+')], '( log ` Y ) e. RR')
    cl0 = Closure(w, A0, {HS: ('RR', hsr), '( 1 / %s )' % F: ('RR', D(w, A0, 'nnrecred', [fnn], '( 1 / %s ) e. RR' % F)), HB: ('RR', w.s([fm1, D(w, A0, 'readdcld', [hsr, D(w, A0, 'nnrecred', [fnn], '( 1 / %s ) e. RR' % F)],
                                                                                                                                                                '( %s + ( 1 / %s ) ) e. RR' % (HS, F))], 'eqeltrd', '( %s -> %s e. RR )' % (A0, HB))),
                         '( log ` Y )': ('RR', ly)})
    r0 = w.s([D(w, A0, 'nnrpd', [fnn], '%s e. RR+' % F)], 'rpreccld', '( %s -> ( 1 / %s ) e. RR+ )' % (A0, F))
    hs1 = linarith(w, A0, [fm1, hb, D(w, A0, 'rpge0d', [r0], '0 <_ ( 1 / %s )' % F)], '%s <_ ( ( log ` Y ) + 1 )' % HS, closure=cl0)
    cbn = w.s([w.s([w.s([], 'oveq2', '( n = m -> ( 1 / n ) = ( 1 / m ) )')], 'cbvsumv', 'sum_ n e. %s ( 1 / n ) = %s' % (IV, HS))], 'a1i', '( %s -> sum_ n e. %s ( 1 / n ) = %s )' % (A0, IV, HS))
    b1 = w.s([cbn, hs1], 'eqbrtrd', '( %s -> sum_ n e. %s ( 1 / n ) <_ ( ( log ` Y ) + 1 ) )' % (A0, IV))
    rfn = D(w, AN_, 'rpreccld', [fnrp], '( 1 / ( %s - n ) ) e. RR+' % F)
    le1 = D(w, AN_, 'lediv2ad', [fnrp, ynrp, a1(w, AN_, '1re', '1 e. RR'), a1(w, AN_, '0le1', '0 <_ 1'), linarith(w, AN_, [flea], '( %s - n ) <_ ( Y - n )' % F, closure=cl)],
            '( 1 / ( Y - n ) ) <_ ( 1 / ( %s - n ) )' % F)
    S2 = 'sum_ n e. %s ( 1 / ( Y - n ) )' % IV; S3 = 'sum_ n e. %s ( 1 / ( %s - n ) )' % (IV, F)
    l2 = w.s([fin, D(w, AN_, 'rpred', [ryn], '( 1 / ( Y - n ) ) e. RR'), D(w, AN_, 'rpred', [rfn], '( 1 / ( %s - n ) ) e. RR' % F), le1], 'fsumle', '( %s -> %s <_ %s )' % (A0, S2, S3))
    fmz = w.s([fz, w.inst('peano2zm')], 'syl', '( %s -> %s e. ZZ )' % (A0, FM))
    RV = '( ( %s - %s ) ... ( %s - 1 ) )' % (F, FM, F)
    rev = w.s([fz, a1(w, A0, '1z', '1 e. ZZ'), fmz, D(w, AN_, 'rpcnd', [rfn], '( 1 / ( %s - n ) ) e. CC' % F),
               w.s([w.s([], 'oveq2', '( n = ( %s - k ) -> ( %s - n ) = ( %s - ( %s - k ) ) )' % (F, F, F, F))], 'oveq2d', '( n = ( %s - k ) -> ( 1 / ( %s - n ) ) = ( 1 / ( %s - ( %s - k ) ) ) )' % (F, F, F, F))],
              'fsumrev', '( %s -> %s = sum_ k e. %s ( 1 / ( %s - ( %s - k ) ) ) )' % (A0, S3, RV, F, F))
    one = w.s([fc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'nncand', '( %s -> ( %s - %s ) = 1 )' % (A0, F, FM))
    ivq = w.s([one], 'oveq1d', '( %s -> %s = %s )' % (A0, RV, IV))
    s3a = w.s([ivq], 'sumeq1d', '( %s -> sum_ k e. %s ( 1 / ( %s - ( %s - k ) ) ) = sum_ k e. %s ( 1 / ( %s - ( %s - k ) ) ) )' % (A0, RV, F, F, IV, F, F))
    AK_ = '( %s /\\ k e. %s )' % (A0, IV)
    kc_ = D(w, AK_, 'nncnd', [w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (AK_, IV)), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % AK_)], 'k e. CC')
    kk = w.s([w.s([w.s([fc], 'adantr', '( %s -> %s e. CC )' % (AK_, F)), kc_], 'nncand', '( %s -> ( %s - ( %s - k ) ) = k )' % (AK_, F, F))], 'oveq2d',
             '( %s -> ( 1 / ( %s - ( %s - k ) ) ) = ( 1 / k ) )' % (AK_, F, F))
    s3b = w.s([kk], 'sumeq2dv', '( %s -> sum_ k e. %s ( 1 / ( %s - ( %s - k ) ) ) = sum_ k e. %s ( 1 / k ) )' % (A0, IV, F, F, IV))
    cbk = w.s([w.s([w.s([], 'oveq2', '( k = m -> ( 1 / k ) = ( 1 / m ) )')], 'cbvsumv', 'sum_ k e. %s ( 1 / k ) = %s' % (IV, HS))], 'a1i', '( %s -> sum_ k e. %s ( 1 / k ) = %s )' % (A0, IV, HS))
    s3 = chain(w, A0, [S3, 'sum_ k e. %s ( 1 / ( %s - ( %s - k ) ) )' % (RV, F, F), 'sum_ k e. %s ( 1 / ( %s - ( %s - k ) ) )' % (IV, F, F), 'sum_ k e. %s ( 1 / k )' % IV, HS],
               [rev, s3a, s3b, cbk])
    s1r = w.s([fin, rn], 'fsumrecl', '( %s -> sum_ n e. %s ( 1 / n ) e. RR )' % (A0, IV))
    s2r = w.s([fin, D(w, AN_, 'rpred', [ryn], '( 1 / ( Y - n ) ) e. RR')], 'fsumrecl', '( %s -> %s e. RR )' % (A0, S2))
    s3r = w.s([fin, D(w, AN_, 'rpred', [rfn], '( 1 / ( %s - n ) ) e. RR' % F)], 'fsumrecl', '( %s -> %s e. RR )' % (A0, S3))
    cl0.leaf('sum_ n e. %s ( 1 / n )' % IV, 'RR', s1r); cl0.leaf(S2, 'RR', s2r); cl0.leaf(S3, 'RR', s3r)
    s3e = w.s([s3], 'idi', '( %s -> %s = %s )' % (A0, S3, HS))
    tot = linarith(w, A0, [b1, l2, s3e, hs1], '( sum_ n e. %s ( 1 / n ) + %s ) <_ ( 2 x. ( 1 + ( log ` Y ) ) )' % (IV, S2), closure=cl0)
    w.qed([w.s([s1, s2], 'eqtrd', '( %s -> sum_ n e. %s ( Y / ( n x. ( Y - n ) ) ) = ( sum_ n e. %s ( 1 / n ) + %s ) )' % (A0, IV, IV, S2)), tot], 'eqbrtrd', STATEMENTS['ef1pfr'])
    go(w, only)


def tpic(w, ante):
    """( ante -> ( 2 x. ( _i x. _pi ) ) e. CC )"""
    ip = D(w, ante, 'mulcld', [a1(w, ante, 'ax-icn', '_i e. CC'), a1(w, ante, 'picn', '_pi e. CC')], '( _i x. _pi ) e. CC')
    return D(w, ante, 'mulcld', [a1(w, ante, '2cn', '2 e. CC'), ip], '%s e. CC' % TPI)


def kbase(w, A0, yrp, crp, trp, nn):
    """U = Y / N facts under A0 and the pkind step"""
    d = {}
    U = '( Y / N )'
    d['nrp'] = D(w, A0, 'nnrpd', [nn], 'N e. RR+')
    d['urp'] = D(w, A0, 'rpdivcld', [yrp, d['nrp']], '%s e. RR+' % U)
    d['ur'] = D(w, A0, 'rpred', [d['urp']], '%s e. RR' % U)
    d['yr'] = D(w, A0, 'rpred', [yrp], 'Y e. RR')
    d['nr'] = D(w, A0, 'rpred', [d['nrp']], 'N e. RR')
    d['yc'] = D(w, A0, 'rpcnd', [yrp], 'Y e. CC'); d['yne'] = D(w, A0, 'rpne0d', [yrp], 'Y =/= 0')
    d['nc'] = D(w, A0, 'rpcnd', [d['nrp']], 'N e. CC'); d['nne'] = D(w, A0, 'rpne0d', [d['nrp']], 'N =/= 0')
    d['pkcl'] = w.s([d['urp'], crp, trp, w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (A0, KNL('N')))
    return d


def pkapp(w, A0, d, une, crp, trp):
    return w.s([D(w, A0, 'jca', [D(w, A0, 'jca', [d['urp'], une], '( ( Y / N ) e. RR+ /\\ ( Y / N ) =/= 1 )'), D(w, A0, 'jca', [crp, trp], '( C e. RR+ /\\ T e. RR+ )')],
                  '( ( ( Y / N ) e. RR+ /\\ ( Y / N ) =/= 1 ) /\\ ( C e. RR+ /\\ T e. RR+ ) )'), w.inst('pkind')], 'syl',
               '( %s -> ( abs ` ( %s - if ( 1 < ( Y / N ) , %s , 0 ) ) ) <_ ( ( 6 x. ( ( Y / N ) ^c C ) ) / ( T x. ( abs ` ( log ` ( Y / N ) ) ) ) ) )' % (A0, KNL('N'), TPI))


# ---------------------------------------------------------------- ef1kl: left of the diagonal
if __name__ == '__main__' and (not only or 'ef1kl' in only):
    w = W('ef1kl', 'The Perron kernel left of the diagonal ( ` n < y ` ): ` | K ( y / n ) - 2 pi i | <_ ( 6 y ^ c / T ) ( y / ( n ( y - n ) ) ) ` '
          '( ~ pkind with ` log ( y / n ) >_ 1 - n / y ` and ` ( y / n ) ^ c <_ y ^ c / n ` ; Lean ` kerErr_far_left ` and ` kerErr_mid_left ` '
          'in one bound, times ` 2 pi ` ).')
    A0 = STATEMENTS['ef1kl'].split(' -> ( abs')[0][2:]
    yrp = D(w, A0, 'simpl1', [], 'Y e. RR+'); cr = D(w, A0, 'simpl2', [], 'C e. RR'); c1 = D(w, A0, 'simpl3', [], '1 <_ C')
    trp = D(w, A0, 'simprl', [], 'T e. RR+'); nn = D(w, A0, 'simprrl', [], 'N e. NN'); nly = D(w, A0, 'simprrr', [], 'N < Y')
    cl = Closure(w, A0, {'C': ('RR', cr)})
    crp = D(w, A0, 'elrpd', [cr, linarith(w, A0, [c1], '0 < C', closure=cl)], 'C e. RR+')
    d = kbase(w, A0, yrp, crp, trp, nn)
    U = '( Y / N )'
    n1y = w.s([w.s([d['nc']], 'mullidd', '( %s -> ( 1 x. N ) = N )' % A0), nly], 'eqbrtrd', '( %s -> ( 1 x. N ) < Y )' % A0)
    u1 = w.s([n1y, D(w, A0, 'ltmuldivd', [a1(w, A0, '1re', '1 e. RR'), d['yr'], d['nrp']], '( ( 1 x. N ) < Y <-> 1 < %s )' % U)], 'mpbid', '( %s -> 1 < %s )' % (A0, U))
    une = D(w, A0, 'gtned', [a1(w, A0, '1re', '1 e. RR'), u1], '%s =/= 1' % U)
    pk = pkapp(w, A0, d, une, crp, trp)
    ift = w.s([u1], 'iftrued', '( %s -> if ( 1 < %s , %s , 0 ) = %s )' % (A0, U, TPI, TPI))
    P = '( abs ` ( %s - %s ) )' % (KNL('N'), TPI)
    peq = w.s([w.s([ift], 'oveq2d', '( %s -> ( %s - if ( 1 < %s , %s , 0 ) ) = ( %s - %s ) )' % (A0, KNL('N'), U, TPI, KNL('N'), TPI))], 'fveq2d',
              '( %s -> ( abs ` ( %s - if ( 1 < %s , %s , 0 ) ) ) = %s )' % (A0, KNL('N'), U, TPI, P))
    LU = '( log ` %s )' % U
    lurp = w.s([d['ur'], u1, w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A0, LU))
    alu = D(w, A0, 'absidd', [D(w, A0, 'rpred', [lurp], '%s e. RR' % LU), D(w, A0, 'rpge0d', [lurp], '0 <_ %s' % LU)], '( abs ` %s ) = %s' % (LU, LU))
    UC = '( %s ^c C )' % U
    R0 = '( ( 6 x. %s ) / ( T x. ( abs ` %s ) ) )' % (UC, LU)
    R1 = '( ( 6 x. %s ) / ( T x. %s ) )' % (UC, LU)
    req = w.s([w.s([alu], 'oveq2d', '( %s -> ( T x. ( abs ` %s ) ) = ( T x. %s ) )' % (A0, LU, LU))], 'oveq2d', '( %s -> %s = %s )' % (A0, R0, R1))
    p1 = w.s([w.s([peq, pk], 'eqbrtrrd', '( %s -> %s <_ %s )' % (A0, P, R0)), req], 'breqtrd', '( %s -> %s <_ %s )' % (A0, P, R1))
    YC = '( Y ^c C )'; NC = '( N ^c C )'
    ccc = D(w, A0, 'recnd', [cr], 'C e. CC')
    dcx = D(w, A0, 'divcxpd', [d['yr'], D(w, A0, 'rpge0d', [yrp], '0 <_ Y'), d['nrp'], ccc], '%s = ( %s / %s )' % (UC, YC, NC))
    n1 = w.s([w.s([d['nr'], w.s([nn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ N )' % A0)], 'jca', '( %s -> ( N e. RR /\\ 1 <_ N ) )' % A0),
              D(w, A0, 'jca', [a1(w, A0, '1re', '1 e. RR'), cr], '( 1 e. RR /\\ C e. RR )'), c1, w.inst('cxplea')], 'syl3anc', '( %s -> ( N ^c 1 ) <_ %s )' % (A0, NC))
    nle = w.s([w.s([d['nc']], 'cxp1d', '( %s -> ( N ^c 1 ) = N )' % A0), n1], 'eqbrtrrd', '( %s -> N <_ %s )' % (A0, NC))
    ycrp = D(w, A0, 'rpcxpcld', [yrp, cr], '%s e. RR+' % YC); ncrp = D(w, A0, 'rpcxpcld', [d['nrp'], cr], '%s e. RR+' % NC)
    ucle = w.s([dcx, D(w, A0, 'lediv2ad', [d['nrp'], ncrp, D(w, A0, 'rpred', [ycrp], '%s e. RR' % YC), D(w, A0, 'rpge0d', [ycrp], '0 <_ %s' % YC), nle], '( %s / %s ) <_ ( %s / N )' % (YC, NC, YC))],
               'eqbrtrd', '( %s -> %s <_ ( %s / N ) )' % (A0, UC, YC))
    zl = w.s([d['ur'], u1, w.inst('zdmlogl1')], 'syl2anc', '( %s -> ( 1 - ( 1 / %s ) ) <_ %s )' % (A0, U, LU))
    rd = D(w, A0, 'recdivd', [d['yc'], d['nc'], d['yne'], d['nne']], '( 1 / %s ) = ( N / Y )' % U)
    YN = '( ( Y - N ) / Y )'
    ds = D(w, A0, 'divsubdird', [d['yc'], d['nc'], d['yc'], d['yne']], '%s = ( ( Y / Y ) - ( N / Y ) )' % YN)
    dyy = w.s([d['yc'], d['yne'], w.inst('divid')], 'syl2anc', '( %s -> ( Y / Y ) = 1 )' % A0)
    e1n = chain(w, A0, ['( 1 - ( 1 / %s ) )' % U, '( 1 - ( N / Y ) )', '( ( Y / Y ) - ( N / Y ) )', YN],
                [w.s([rd], 'oveq2d', '( %s -> ( 1 - ( 1 / %s ) ) = ( 1 - ( N / Y ) ) )' % (A0, U)), w.s([w.s([dyy], 'eqcomd', '( %s -> 1 = ( Y / Y ) )' % A0)], 'oveq1d',
                 '( %s -> ( 1 - ( N / Y ) ) = ( ( Y / Y ) - ( N / Y ) ) )' % A0), ('r', ds)])
    lule = w.s([w.s([e1n], 'eqcomd', '( %s -> %s = ( 1 - ( 1 / %s ) ) )' % (A0, YN, U)), zl], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, YN, LU))
    cly = Closure(w, A0, {'Y': ('RR+', yrp), 'N': ('RR+', d['nrp'])})
    ynrp = D(w, A0, 'elrpd', [cly.mem('( Y - N )', 'RR'), linarith(w, A0, [nly], '0 < ( Y - N )', closure=cly)], '( Y - N ) e. RR+')
    ynyrp = D(w, A0, 'rpdivcld', [ynrp, yrp], '%s e. RR+' % YN)
    Q = '( %s / N )' % YC
    qrp = D(w, A0, 'rpdivcld', [ycrp, d['nrp']], '%s e. RR+' % Q)
    ucr = D(w, A0, 'rpred', [D(w, A0, 'rpcxpcld', [d['urp'], cr], '%s e. RR+' % UC)], '%s e. RR' % UC)
    cl2 = Closure(w, A0, {UC: ('RR', ucr), Q: ('RR+', qrp)})
    six = linarith(w, A0, [ucle], '( 6 x. %s ) <_ ( 6 x. %s )' % (UC, Q), closure=cl2)
    tlu = D(w, A0, 'rpmulcld', [trp, lurp], '( T x. %s ) e. RR+' % LU)
    q1 = D(w, A0, 'lediv1dd', [cl2.mem('( 6 x. %s )' % UC, 'RR'), cl2.mem('( 6 x. %s )' % Q, 'RR'), tlu, six], '%s <_ ( ( 6 x. %s ) / ( T x. %s ) )' % (R1, Q, LU))
    tyn = D(w, A0, 'rpmulcld', [trp, ynyrp], '( T x. %s ) e. RR+' % YN)
    tle = D(w, A0, 'lemul2ad', [D(w, A0, 'rpred', [ynyrp], '%s e. RR' % YN), D(w, A0, 'rpred', [lurp], '%s e. RR' % LU), D(w, A0, 'rpred', [trp], 'T e. RR'), D(w, A0, 'rpge0d', [trp], '0 <_ T'), lule],
            '( T x. %s ) <_ ( T x. %s )' % (YN, LU))
    SQ = '( 6 x. %s )' % Q
    q2 = D(w, A0, 'lediv2ad', [tyn, tlu, cl2.mem(SQ, 'RR'), D(w, A0, 'rpge0d', [D(w, A0, 'rpmulcld', [a1(w, A0, '6rp', '6 e. RR+'), qrp], '%s e. RR+' % SQ)], '0 <_ %s' % SQ), tle],
           '( %s / ( T x. %s ) ) <_ ( %s / ( T x. %s ) )' % (SQ, LU, SQ, YN))
    # the identity ( 6 ( YC / N ) ) / ( T ( ( Y - N ) / Y ) ) = ( 6 YC / T ) ( Y / ( N ( Y - N ) ) )
    c6 = a1(w, A0, '6cn', '6 e. CC'); ycc = D(w, A0, 'rpcnd', [ycrp], '%s e. CC' % YC); tc = D(w, A0, 'rpcnd', [trp], 'T e. CC'); tne = D(w, A0, 'rpne0d', [trp], 'T =/= 0')
    ync = D(w, A0, 'rpcnd', [ynrp], '( Y - N ) e. CC'); ynne = D(w, A0, 'rpne0d', [ynrp], '( Y - N ) =/= 0')
    SY = '( 6 x. %s )' % YC; TY = '( T x. ( Y - N ) )'; NY = '( N x. ( Y - N ) )'
    syc = D(w, A0, 'mulcld', [c6, ycc], '%s e. CC' % SY)
    tyc = D(w, A0, 'mulcld', [tc, ync], '%s e. CC' % TY); tyne = D(w, A0, 'mulne0d', [tc, ync, tne, ynne], '%s =/= 0' % TY)
    nyc = D(w, A0, 'mulcld', [d['nc'], ync], '%s e. CC' % NY); nyne = D(w, A0, 'mulne0d', [d['nc'], ync, d['nne'], ynne], '%s =/= 0' % NY)
    i1 = D(w, A0, 'divassd', [c6, ycc, d['nc'], d['nne']], '( %s / N ) = %s' % (SY, SQ))
    i2 = D(w, A0, 'divassd', [tc, ync, d['yc'], d['yne']], '( %s / Y ) = ( T x. %s )' % (TY, YN))
    i3 = D(w, A0, 'divdivdivd', [syc, d['nc'], tyc, d['yc'], d['nne'], d['yne'], tyne], '( ( %s / N ) / ( %s / Y ) ) = ( ( %s x. Y ) / ( N x. %s ) )' % (SY, TY, SY, TY))
    i4 = D(w, A0, 'mul12d', [d['nc'], tc, ync], '( N x. %s ) = ( T x. %s )' % (TY, NY))
    i5 = D(w, A0, 'divmuldivd', [syc, tc, d['yc'], nyc, tne, nyne], '( ( %s / T ) x. ( Y / %s ) ) = ( ( %s x. Y ) / ( T x. %s ) )' % (SY, NY, SY, NY))
    RHS = '( ( %s / T ) x. ( Y / %s ) )' % (SY, NY)
    ide = chain(w, A0, ['( %s / ( T x. %s ) )' % (SQ, YN), '( ( %s / N ) / ( %s / Y ) )' % (SY, TY), '( ( %s x. Y ) / ( N x. %s ) )' % (SY, TY), '( ( %s x. Y ) / ( T x. %s ) )' % (SY, NY), RHS],
                [w.s([w.s([i1], 'eqcomd', '( %s -> %s = ( %s / N ) )' % (A0, SQ, SY)), w.s([i2], 'eqcomd', '( %s -> ( T x. %s ) = ( %s / Y ) )' % (A0, YN, TY))], 'oveq12d',
                      '( %s -> ( %s / ( T x. %s ) ) = ( ( %s / N ) / ( %s / Y ) ) )' % (A0, SQ, YN, SY, TY)), i3, w.s([i4], 'oveq2d', '( %s -> ( ( %s x. Y ) / ( N x. %s ) ) = ( ( %s x. Y ) / ( T x. %s ) ) )' % (A0, SY, TY, SY, NY)), ('r', i5)])
    pr_ = D(w, A0, 'abscld', [D(w, A0, 'subcld', [d['pkcl'], tpic(w, A0)], '( %s - %s ) e. CC' % (KNL('N'), TPI))], '%s e. RR' % P)
    r1r = D(w, A0, 'rerpdivcld', [cl2.mem('( 6 x. %s )' % UC, 'RR'), tlu], '%s e. RR' % R1)
    m1 = '( %s / ( T x. %s ) )' % (SQ, LU); m2 = '( %s / ( T x. %s ) )' % (SQ, YN)
    m1r = D(w, A0, 'rerpdivcld', [cl2.mem(SQ, 'RR'), tlu], '%s e. RR' % m1)
    m2r = D(w, A0, 'rerpdivcld', [cl2.mem(SQ, 'RR'), tyn], '%s e. RR' % m2)
    a_ = D(w, A0, 'letrd', [pr_, r1r, m1r, p1, q1], '%s <_ %s' % (P, m1))
    b_ = w.s([q2, ide], 'breqtrd', '( %s -> %s <_ %s )' % (A0, m1, RHS))
    rr = w.s([ide, m2r], 'eqeltrrd', '( %s -> %s e. RR )' % (A0, RHS))
    w.qed([pr_, m1r, rr, a_, b_], 'letrd', STATEMENTS['ef1kl'])
    go(w, only)



def rightside(w, A0, d, yrp, crp, trp, ylt):
    """for Y < N: the pkind step with the indicator removed and | log ( Y / N ) | = log ( N / Y ) >_ ( N - Y ) / N"""
    U = '( Y / N )'; V = '( N / Y )'
    y1n = w.s([ylt, w.s([w.s([d['nc']], 'mullidd', '( %s -> ( 1 x. N ) = N )' % A0)], 'eqcomd', '( %s -> N = ( 1 x. N ) )' % A0)], 'breqtrd', '( %s -> Y < ( 1 x. N ) )' % A0)
    ult = w.s([y1n, w.s([d['yr'], a1(w, A0, '1re', '1 e. RR'), D(w, A0, 'jca', [d['nr'], D(w, A0, 'rpgt0d', [d['nrp']], '0 < N')], '( N e. RR /\\ 0 < N )'), w.inst('ltdivmul2')], 'syl3anc',
                         '( %s -> ( %s < 1 <-> Y < ( 1 x. N ) ) )' % (A0, U))], 'mpbird', '( %s -> %s < 1 )' % (A0, U))
    une = D(w, A0, 'ltned', [d['ur'], ult], '%s =/= 1' % U)
    pk = pkapp(w, A0, d, une, crp, trp)
    iff = w.s([D(w, A0, 'ltnsymd', [d['ur'], a1(w, A0, '1re', '1 e. RR'), ult], '-. 1 < %s' % U)], 'iffalsed', '( %s -> if ( 1 < %s , %s , 0 ) = 0 )' % (A0, U, TPI))
    P = '( abs ` %s )' % KNL('N')
    peq = w.s([w.s([w.s([iff], 'oveq2d', '( %s -> ( %s - if ( 1 < %s , %s , 0 ) ) = ( %s - 0 ) )' % (A0, KNL('N'), U, TPI, KNL('N'))), D(w, A0, 'subid1d', [d['pkcl']], '( %s - 0 ) = %s' % (KNL('N'), KNL('N')))],
                   'eqtrd', '( %s -> ( %s - if ( 1 < %s , %s , 0 ) ) = %s )' % (A0, KNL('N'), U, TPI, KNL('N')))], 'fveq2d', '( %s -> ( abs ` ( %s - if ( 1 < %s , %s , 0 ) ) ) = %s )' % (A0, KNL('N'), U, TPI, P))
    # V = N / Y > 1
    n1y = w.s([w.s([d['yc']], 'mullidd', '( %s -> ( 1 x. Y ) = Y )' % A0), ylt], 'eqbrtrd', '( %s -> ( 1 x. Y ) < N )' % A0)
    v1 = w.s([n1y, D(w, A0, 'ltmuldivd', [a1(w, A0, '1re', '1 e. RR'), d['nr'], yrp], '( ( 1 x. Y ) < N <-> 1 < %s )' % V)], 'mpbid', '( %s -> 1 < %s )' % (A0, V))
    vrp = D(w, A0, 'rpdivcld', [d['nrp'], yrp], '%s e. RR+' % V)
    LV = '( log ` %s )' % V; LU = '( log ` %s )' % U
    lvrp = w.s([D(w, A0, 'rpred', [vrp], '%s e. RR' % V), v1, w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A0, LV))
    ly = D(w, A0, 'relogcld', [yrp], '( log ` Y ) e. RR'); ln = D(w, A0, 'relogcld', [d['nrp']], '( log ` N ) e. RR')
    lu = D(w, A0, 'relogdivd', [yrp, d['nrp']], '%s = ( ( log ` Y ) - ( log ` N ) )' % LU)
    lv = D(w, A0, 'relogdivd', [d['nrp'], yrp], '%s = ( ( log ` N ) - ( log ` Y ) )' % LV)
    ng = D(w, A0, 'negsubdi2d', [D(w, A0, 'recnd', [ln], '( log ` N ) e. CC'), D(w, A0, 'recnd', [ly], '( log ` Y ) e. CC')], '-u ( ( log ` N ) - ( log ` Y ) ) = ( ( log ` Y ) - ( log ` N ) )')
    lun = w.s([lu, w.s([w.s([w.s([lv], 'negeqd', '( %s -> -u %s = -u ( ( log ` N ) - ( log ` Y ) ) )' % (A0, LV)), ng], 'eqtrd', '( %s -> -u %s = ( ( log ` Y ) - ( log ` N ) ) )' % (A0, LV))], 'eqcomd',
                                              '( %s -> ( ( log ` Y ) - ( log ` N ) ) = -u %s )' % (A0, LV))], 'eqtrd', '( %s -> %s = -u %s )' % (A0, LU, LV))
    lvc = D(w, A0, 'rpcnd', [lvrp], '%s e. CC' % LV)
    alu = chain(w, A0, ['( abs ` %s )' % LU, '( abs ` -u %s )' % LV, '( abs ` %s )' % LV, LV],
                [w.s([lun], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` -u %s ) )' % (A0, LU, LV)), D(w, A0, 'absnegd', [lvc], '( abs ` -u %s ) = ( abs ` %s )' % (LV, LV)),
                 D(w, A0, 'absidd', [D(w, A0, 'rpred', [lvrp], '%s e. RR' % LV), D(w, A0, 'rpge0d', [lvrp], '0 <_ %s' % LV)], '( abs ` %s ) = %s' % (LV, LV))])
    UC = '( %s ^c C )' % U
    R0 = '( ( 6 x. %s ) / ( T x. ( abs ` %s ) ) )' % (UC, LU)
    R1 = '( ( 6 x. %s ) / ( T x. %s ) )' % (UC, LV)
    req = w.s([w.s([alu], 'oveq2d', '( %s -> ( T x. ( abs ` %s ) ) = ( T x. %s ) )' % (A0, LU, LV))], 'oveq2d', '( %s -> %s = %s )' % (A0, R0, R1))
    p1 = w.s([w.s([peq, pk], 'eqbrtrrd', '( %s -> %s <_ %s )' % (A0, P, R0)), req], 'breqtrd', '( %s -> %s <_ %s )' % (A0, P, R1))
    return {'p1': p1, 'P': P, 'R1': R1, 'UC': UC, 'LV': LV, 'lvrp': lvrp, 'vrp': vrp, 'v1': v1, 'ult': ult, 'V': V}

# ---------------------------------------------------------------- ef1kr: right of the diagonal
if __name__ == '__main__' and (not only or 'ef1kr' in only):
    w = W('ef1kr', 'The Perron kernel right of the diagonal ( ` y < n ` ): ` | K ( y / n ) | <_ ( 6 / T ) ( n / ( n - y ) ) ` ( ~ pkind with '
          '` ( y / n ) ^ c <_ 1 ` and ` | log ( y / n ) | = log ( n / y ) >_ ( n - y ) / n ` ; Lean ` kerErr_mid_right ` , times ` 2 pi ` ).')
    A0 = STATEMENTS['ef1kr'].split(' -> ( abs')[0][2:]
    yrp = D(w, A0, 'simpll', [], 'Y e. RR+'); crp = D(w, A0, 'simplr', [], 'C e. RR+')
    trp = D(w, A0, 'simprl', [], 'T e. RR+'); nn = D(w, A0, 'simprrl', [], 'N e. NN'); ylt = D(w, A0, 'simprrr', [], 'Y < N')
    d = kbase(w, A0, yrp, crp, trp, nn)
    r = rightside(w, A0, d, yrp, crp, trp, ylt)
    UC, LV, V = r['UC'], r['LV'], r['V']
    # ( Y / N ) ^ C <_ 1
    cr = D(w, A0, 'rpred', [crp], 'C e. RR')
    bi = w.s([D(w, A0, 'jca', [d['ur'], D(w, A0, 'rpge0d', [d['urp']], '0 <_ ( Y / N )')], '( ( Y / N ) e. RR /\\ 0 <_ ( Y / N ) )'),
              D(w, A0, 'jca', [a1(w, A0, '1re', '1 e. RR'), a1(w, A0, '0le1', '0 <_ 1')], '( 1 e. RR /\\ 0 <_ 1 )'), crp, w.inst('cxple2')], 'syl3anc',
             '( %s -> ( ( Y / N ) <_ 1 <-> %s <_ ( 1 ^c C ) ) )' % (A0, UC))
    u1 = w.s([D(w, A0, 'ltled', [d['ur'], a1(w, A0, '1re', '1 e. RR'), r['ult']], '( Y / N ) <_ 1'), bi], 'mpbid', '( %s -> %s <_ ( 1 ^c C ) )' % (A0, UC))
    ucle = w.s([u1, w.s([D(w, A0, 'recnd', [cr], 'C e. CC'), w.inst('1cxp')], 'syl', '( %s -> ( 1 ^c C ) = 1 )' % A0)], 'breqtrd', '( %s -> %s <_ 1 )' % (A0, UC))
    ucr = D(w, A0, 'rpred', [D(w, A0, 'rpcxpcld', [d['urp'], cr], '%s e. RR+' % UC)], '%s e. RR' % UC)
    cl = Closure(w, A0, {UC: ('RR', ucr)})
    six = linarith(w, A0, [ucle], '( 6 x. %s ) <_ ( 6 x. 1 )' % UC, closure=cl)
    tlv = D(w, A0, 'rpmulcld', [trp, r['lvrp']], '( T x. %s ) e. RR+' % LV)
    q1 = D(w, A0, 'lediv1dd', [cl.mem('( 6 x. %s )' % UC, 'RR'), cl.mem('( 6 x. 1 )', 'RR'), tlv, six], '%s <_ ( ( 6 x. 1 ) / ( T x. %s ) )' % (r['R1'], LV))
    # log V >_ ( N - Y ) / N
    zl = w.s([D(w, A0, 'rpred', [r['vrp']], '%s e. RR' % V), r['v1'], w.inst('zdmlogl1')], 'syl2anc', '( %s -> ( 1 - ( 1 / %s ) ) <_ %s )' % (A0, V, LV))
    rd = D(w, A0, 'recdivd', [d['nc'], d['yc'], d['nne'], d['yne']], '( 1 / %s ) = ( Y / N )' % V)
    NY = '( ( N - Y ) / N )'
    ds = D(w, A0, 'divsubdird', [d['nc'], d['yc'], d['nc'], d['nne']], '%s = ( ( N / N ) - ( Y / N ) )' % NY)
    dnn = w.s([d['nc'], d['nne'], w.inst('divid')], 'syl2anc', '( %s -> ( N / N ) = 1 )' % A0)
    e1n = chain(w, A0, ['( 1 - ( 1 / %s ) )' % V, '( 1 - ( Y / N ) )', '( ( N / N ) - ( Y / N ) )', NY],
                [w.s([rd], 'oveq2d', '( %s -> ( 1 - ( 1 / %s ) ) = ( 1 - ( Y / N ) ) )' % (A0, V)), w.s([w.s([dnn], 'eqcomd', '( %s -> 1 = ( N / N ) )' % A0)], 'oveq1d',
                 '( %s -> ( 1 - ( Y / N ) ) = ( ( N / N ) - ( Y / N ) ) )' % A0), ('r', ds)])
    lvle = w.s([w.s([e1n], 'eqcomd', '( %s -> %s = ( 1 - ( 1 / %s ) ) )' % (A0, NY, V)), zl], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, NY, LV))
    cly = Closure(w, A0, {'Y': ('RR+', yrp), 'N': ('RR+', d['nrp'])})
    nyrp = D(w, A0, 'elrpd', [cly.mem('( N - Y )', 'RR'), linarith(w, A0, [ylt], '0 < ( N - Y )', closure=cly)], '( N - Y ) e. RR+')
    nynrp = D(w, A0, 'rpdivcld', [nyrp, d['nrp']], '%s e. RR+' % NY)
    tny = D(w, A0, 'rpmulcld', [trp, nynrp], '( T x. %s ) e. RR+' % NY)
    tle = D(w, A0, 'lemul2ad', [D(w, A0, 'rpred', [nynrp], '%s e. RR' % NY), D(w, A0, 'rpred', [r['lvrp']], '%s e. RR' % LV), D(w, A0, 'rpred', [trp], 'T e. RR'), D(w, A0, 'rpge0d', [trp], '0 <_ T'), lvle],
            '( T x. %s ) <_ ( T x. %s )' % (NY, LV))
    S1 = '( 6 x. 1 )'
    q2 = D(w, A0, 'lediv2ad', [tny, tlv, cl.mem(S1, 'RR'), linarith(w, A0, [], '0 <_ %s' % S1, closure=cl), tle], '( %s / ( T x. %s ) ) <_ ( %s / ( T x. %s ) )' % (S1, LV, S1, NY))
    # ( 6 x. 1 ) / ( T x. ( ( N - Y ) / N ) ) = ( 6 / T ) x. ( N / ( N - Y ) )
    tc = D(w, A0, 'rpcnd', [trp], 'T e. CC'); tne = D(w, A0, 'rpne0d', [trp], 'T =/= 0'); nyc = D(w, A0, 'rpcnd', [nyrp], '( N - Y ) e. CC'); nyne = D(w, A0, 'rpne0d', [nyrp], '( N - Y ) =/= 0')
    c6 = a1(w, A0, '6cn', '6 e. CC')
    TY = '( T x. ( N - Y ) )'
    tyc = D(w, A0, 'mulcld', [tc, nyc], '%s e. CC' % TY); tyne = D(w, A0, 'mulne0d', [tc, nyc, tne, nyne], '%s =/= 0' % TY)
    RHS = '( ( 6 / T ) x. ( N / ( N - Y ) ) )'
    ide = chain(w, A0, ['( %s / ( T x. %s ) )' % (S1, NY), '( 6 / ( %s / N ) )' % TY, '( ( 6 x. N ) / %s )' % TY, RHS],
                [w.s([D(w, A0, 'mulridd', [c6], '%s = 6' % S1), w.s([D(w, A0, 'divassd', [tc, nyc, d['nc'], d['nne']], '( %s / N ) = ( T x. %s )' % (TY, NY))], 'eqcomd', '( %s -> ( T x. %s ) = ( %s / N ) )' % (A0, NY, TY))],
                     'oveq12d', '( %s -> ( %s / ( T x. %s ) ) = ( 6 / ( %s / N ) ) )' % (A0, S1, NY, TY)),
                 D(w, A0, 'divdiv2d', [c6, tyc, d['nc'], tyne, d['nne']], '( 6 / ( %s / N ) ) = ( ( 6 x. N ) / %s )' % (TY, TY)),
                 ('r', D(w, A0, 'divmuldivd', [c6, tc, d['nc'], nyc, tne, nyne], '%s = ( ( 6 x. N ) / %s )' % (RHS, TY)))])
    P = r['P']
    pr_ = D(w, A0, 'abscld', [d['pkcl']], '%s e. RR' % P)
    r1r = D(w, A0, 'rerpdivcld', [cl.mem('( 6 x. %s )' % UC, 'RR'), tlv], '%s e. RR' % r['R1'])
    m1 = '( %s / ( T x. %s ) )' % (S1, LV); m2 = '( %s / ( T x. %s ) )' % (S1, NY)
    m1r = D(w, A0, 'rerpdivcld', [cl.mem(S1, 'RR'), tlv], '%s e. RR' % m1)
    m2r = D(w, A0, 'rerpdivcld', [cl.mem(S1, 'RR'), tny], '%s e. RR' % m2)
    a_ = D(w, A0, 'letrd', [pr_, r1r, m1r, r['p1'], q1], '%s <_ %s' % (P, m1))
    b_ = w.s([q2, ide], 'breqtrd', '( %s -> %s <_ %s )' % (A0, m1, RHS))
    rr = w.s([ide, m2r], 'eqeltrrd', '( %s -> %s e. RR )' % (A0, RHS))
    w.qed([pr_, m1r, rr, a_, b_], 'letrd', STATEMENTS['ef1kr'])
    go(w, only)

# ---------------------------------------------------------------- ef1kt: the far right
if __name__ == '__main__' and (not only or 'ef1kt' in only):
    w = W('ef1kt', 'The Perron kernel far right ( ` 2 y <_ n ` ): ` | K ( y / n ) | <_ ( 12 / T ) ( y / n ) ^ c ` ( ~ pkind with '
          '` | log ( y / n ) | >_ log 2 >_ 1 / 2 ` ; Lean ` kernel_norm_far_small ` in ` kerErr_far_right ` , times ` 2 pi ` ).')
    A0 = STATEMENTS['ef1kt'].split(' -> ( abs')[0][2:]
    yrp = D(w, A0, 'simpll', [], 'Y e. RR+'); crp = D(w, A0, 'simplr', [], 'C e. RR+')
    trp = D(w, A0, 'simprl', [], 'T e. RR+'); nn = D(w, A0, 'simprrl', [], 'N e. NN'); y2n = D(w, A0, 'simprrr', [], '( 2 x. Y ) <_ N')
    d = kbase(w, A0, yrp, crp, trp, nn)
    cly = Closure(w, A0, {'Y': ('RR+', yrp), 'N': ('RR+', d['nrp'])})
    ylt = linarith(w, A0, [y2n, D(w, A0, 'rpgt0d', [yrp], '0 < Y')], 'Y < N', closure=cly)
    r = rightside(w, A0, d, yrp, crp, trp, ylt)
    UC, LV, V = r['UC'], r['LV'], r['V']
    v2 = w.s([y2n, D(w, A0, 'lemuldivd', [a1(w, A0, '2re', '2 e. RR'), d['nr'], yrp], '( ( 2 x. Y ) <_ N <-> 2 <_ %s )' % V)], 'mpbid', '( %s -> 2 <_ %s )' % (A0, V))
    l2 = w.s([v2, D(w, A0, 'logled', [a1(w, A0, '2rp', '2 e. RR+'), r['vrp']], '( 2 <_ %s <-> ( log ` 2 ) <_ %s )' % (V, LV))], 'mpbid', '( %s -> ( log ` 2 ) <_ %s )' % (A0, LV))
    l2r = D(w, A0, 'relogcld', [a1(w, A0, '2rp', '2 e. RR+')], '( log ` 2 ) e. RR')
    hl = D(w, A0, 'letrd', [a1(w, A0, 'halfre', '( 1 / 2 ) e. RR'), l2r, D(w, A0, 'rpred', [r['lvrp']], '%s e. RR' % LV), a1(w, A0, 'log2ge', '( 1 / 2 ) <_ ( log ` 2 )'), l2], '( 1 / 2 ) <_ %s' % LV)
    tlv = D(w, A0, 'rpmulcld', [trp, r['lvrp']], '( T x. %s ) e. RR+' % LV)
    hrp = w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halfgt0', '0 < ( 1 / 2 )')], 'elrpii', '( 1 / 2 ) e. RR+')
    th = D(w, A0, 'rpmulcld', [trp, w.s([hrp], 'a1i', '( %s -> ( 1 / 2 ) e. RR+ )' % A0)], '( T x. ( 1 / 2 ) ) e. RR+')
    tle = D(w, A0, 'lemul2ad', [a1(w, A0, 'halfre', '( 1 / 2 ) e. RR'), D(w, A0, 'rpred', [r['lvrp']], '%s e. RR' % LV), D(w, A0, 'rpred', [trp], 'T e. RR'), D(w, A0, 'rpge0d', [trp], '0 <_ T'), hl],
            '( T x. ( 1 / 2 ) ) <_ ( T x. %s )' % LV)
    cr = D(w, A0, 'rpred', [crp], 'C e. RR')
    ucrp = D(w, A0, 'rpcxpcld', [d['urp'], cr], '%s e. RR+' % UC)
    S6 = '( 6 x. %s )' % UC
    s6rp = D(w, A0, 'rpmulcld', [a1(w, A0, '6rp', '6 e. RR+'), ucrp], '%s e. RR+' % S6)
    q2 = D(w, A0, 'lediv2ad', [th, tlv, D(w, A0, 'rpred', [s6rp], '%s e. RR' % S6), D(w, A0, 'rpge0d', [s6rp], '0 <_ %s' % S6), tle], '( %s / ( T x. %s ) ) <_ ( %s / ( T x. ( 1 / 2 ) ) )' % (S6, LV, S6))
    tc = D(w, A0, 'rpcnd', [trp], 'T e. CC'); tne = D(w, A0, 'rpne0d', [trp], 'T =/= 0')
    ucc = D(w, A0, 'rpcnd', [ucrp], '%s e. CC' % UC); s6c = D(w, A0, 'rpcnd', [s6rp], '%s e. CC' % S6)
    c2 = a1(w, A0, '2cn', '2 e. CC'); n2 = a1(w, A0, '2ne0', '2 =/= 0')
    RHS = '( ( ; 1 2 / T ) x. %s )' % UC
    cl = Closure(w, A0, {UC: ('RR+', ucrp)})
    ide = chain(w, A0, ['( %s / ( T x. ( 1 / 2 ) ) )' % S6, '( %s / ( T / 2 ) )' % S6, '( ( %s x. 2 ) / T )' % S6, '( ( ; 1 2 x. %s ) / T )' % UC, RHS],
                [w.s([w.s([D(w, A0, 'divrecd', [tc, c2, n2], '( T / 2 ) = ( T x. ( 1 / 2 ) )')], 'eqcomd', '( %s -> ( T x. ( 1 / 2 ) ) = ( T / 2 ) )' % A0)], 'oveq2d',
                      '( %s -> ( %s / ( T x. ( 1 / 2 ) ) ) = ( %s / ( T / 2 ) ) )' % (A0, S6, S6)),
                 D(w, A0, 'divdiv2d', [s6c, tc, c2, tne, n2], '( %s / ( T / 2 ) ) = ( ( %s x. 2 ) / T )' % (S6, S6)),
                 w.s([lineq(w, A0, '( %s x. 2 )' % S6, '( ; 1 2 x. %s )' % UC, closure=cl)], 'oveq1d', '( %s -> ( ( %s x. 2 ) / T ) = ( ( ; 1 2 x. %s ) / T ) )' % (A0, S6, UC)),
                 D(w, A0, 'div23d', [D(w, A0, 'recnd', [cl.mem('; 1 2', 'RR')], '; 1 2 e. CC'), ucc, tc, tne], '( ( ; 1 2 x. %s ) / T ) = %s' % (UC, RHS))])
    P = r['P']
    pr_ = D(w, A0, 'abscld', [d['pkcl']], '%s e. RR' % P)
    m1 = '( %s / ( T x. %s ) )' % (S6, LV); m2 = '( %s / ( T x. ( 1 / 2 ) ) )' % S6
    m1r = D(w, A0, 'rerpdivcld', [D(w, A0, 'rpred', [s6rp], '%s e. RR' % S6), tlv], '%s e. RR' % m1)
    m2r = D(w, A0, 'rerpdivcld', [D(w, A0, 'rpred', [s6rp], '%s e. RR' % S6), th], '%s e. RR' % m2)
    b_ = w.s([q2, ide], 'breqtrd', '( %s -> %s <_ %s )' % (A0, m1, RHS))
    rr = w.s([ide, m2r], 'eqeltrrd', '( %s -> %s e. RR )' % (A0, RHS))
    w.qed([pr_, m1r, rr, r['p1'], b_], 'letrd', STATEMENTS['ef1kt'])
    go(w, only)
