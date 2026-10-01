"""Sortie v2: the exponential bound for the products over ( 2 ... M ).

fz2m1rp    ( K e. ( 2 ... N ) -> ( K x. ( K - 1 ) ) e. RR+ )
prodefub   ( ( M e. NN /\\ C e. RR+ ) ->
             prod_ n e. ( 2 ... M ) ( 1 + ( C / ( n x. ( n - 1 ) ) ) ) <_ ( exp ` C ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

def fz2m1rp():
    A = 'K e. ( 2 ... N )'
    w = W('fz2m1rp', 'K x. ( K - 1 ) is positive for K in ( 2 ... N ).')
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (A, f))
    k = st([], 'elfz2nn', 'K e. NN')
    krp = st([k], 'nnrpd', 'K e. RR+')
    kr = st([k], 'nnred', 'K e. RR')
    k2 = st([], 'elfzle1', '2 <_ K')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    twor = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    zre = w.s([], '0red', '( %s -> 0 e. RR )' % A)
    k1r = st([kr, one], 'resubcld', '( K - 1 ) e. RR')
    sub = st([twor, kr, one, k2], 'lesub1dd', '( 2 - 1 ) <_ ( K - 1 )')
    e21 = st([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')
    ge1 = st([e21, sub], 'eqbrtrrd', '1 <_ ( K - 1 )')
    lt1 = st([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1')
    pos = st([zre, one, k1r, lt1, ge1], 'ltletrd', '0 < ( K - 1 )')
    k1rp = st([k1r, pos], 'elrpd', '( K - 1 ) e. RR+')
    w.qed([krp, k1rp], 'rpmulcld', '( %s -> ( K x. ( K - 1 ) ) e. RR+ )' % A)
    return w



def uz2m1rp():
    A = 'K e. ( ZZ>= ` 2 )'
    w = W('uz2m1rp', 'K x. ( K - 1 ) is positive for K at least 2.')
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (A, f))
    k = st([], 'eluz2nn', 'K e. NN')
    krp = st([k], 'nnrpd', 'K e. RR+')
    kr = st([k], 'nnred', 'K e. RR')
    ez = st([w.s([], 'eluz2', '( K e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ K e. ZZ /\\ 2 <_ K ) )')],
            'a1i', '( K e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ K e. ZZ /\\ 2 <_ K ) )')
    idk = w.s([], 'id', '( %s -> %s )' % (A, A))
    ez2 = st([ez, idk], 'mpbid', '( 2 e. ZZ /\\ K e. ZZ /\\ 2 <_ K )')
    k2 = st([ez2], 'simp3d', '2 <_ K')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    twor = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    zre = w.s([], '0red', '( %s -> 0 e. RR )' % A)
    k1r = st([kr, one], 'resubcld', '( K - 1 ) e. RR')
    sub = st([twor, kr, one, k2], 'lesub1dd', '( 2 - 1 ) <_ ( K - 1 )')
    e21 = st([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')
    ge1 = st([e21, sub], 'eqbrtrrd', '1 <_ ( K - 1 )')
    lt1 = st([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1')
    pos = st([zre, one, k1r, lt1, ge1], 'ltletrd', '0 < ( K - 1 )')
    k1rp = st([k1r, pos], 'elrpd', '( K - 1 ) e. RR+')
    w.qed([krp, k1rp], 'rpmulcld', '( %s -> ( K x. ( K - 1 ) ) e. RR+ )' % A)
    return w


TERM = '( C / ( n x. ( n - 1 ) ) )'
PROD = 'prod_ n e. ( 2 ... M ) ( 1 + %s )' % TERM
A = '( M e. ( ZZ>= ` 2 ) /\\ C e. RR+ )'
B = '( ( M e. ( ZZ>= ` 2 ) /\\ C e. RR+ ) /\\ n e. ( 2 ... M ) )'
BZ = '( ( M e. ( ZZ>= ` 2 ) /\\ C e. RR+ ) /\\ n e. ( ZZ>= ` 2 ) )'


def prodefublem():
    w = W('prodefublem', 'The product bound for M at least 2.')
    SUM = 'sum_ n e. ( 2 ... M ) ( 1 / ( n x. ( n - 1 ) ) )'
    SUMT = 'sum_ n e. ( 2 ... M ) %s' % TERM
    def st(hyps, ref, f, ante=A):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    crp = st([], 'simpr', 'C e. RR+')
    cr = st([crp], 'rpred', 'C e. RR')
    cc = st([crp], 'rpcnd', 'C e. CC')
    c0 = st([crp], 'rpge0d', '0 <_ C')
    muz = st([], 'simpl', 'M e. ( ZZ>= ` 2 )')
    mn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    # termwise on ( 2 ... M )
    crpb = st([crp], 'adantr', 'C e. RR+', B)
    nfz = w.s([], 'simpr', '( %s -> n e. ( 2 ... M ) )' % B)
    nrp = st([nfz, w.inst('fz2m1rp')], 'syl', '( n x. ( n - 1 ) ) e. RR+', B)
    trp = st([crpb, nrp], 'rpdivcld', '%s e. RR+' % TERM, B)
    tr = st([trp], 'rpred', '%s e. RR' % TERM, B)
    onb = w.s([], '1red', '( %s -> 1 e. RR )' % B)
    lhsr = st([onb, tr], 'readdcld', '( 1 + %s ) e. RR' % TERM, B)
    zle1 = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1', B)
    t0 = st([trp], 'rpge0d', '0 <_ %s' % TERM, B)
    lhs0 = st([onb, tr, zle1, t0], 'addge0d', '0 <_ ( 1 + %s )' % TERM, B)
    efr = st([tr], 'reefcld', '( exp ` %s ) e. RR' % TERM, B)
    gt = st([trp, w.inst('efgt1p')], 'syl', '( 1 + %s ) < ( exp ` %s )' % (TERM, TERM), B)
    le = st([gt], 'ltled', '( 1 + %s ) <_ ( exp ` %s )' % (TERM, TERM), B)
    nf = w.s([], 'nfv', 'F/ n %s' % A)
    fin = st([w.s([], 'fzfi', '( 2 ... M ) e. Fin')], 'a1i', '( 2 ... M ) e. Fin')
    ple = st([nf, fin, lhsr, lhs0, efr, le], 'fprodle',
             '%s <_ prod_ n e. ( 2 ... M ) ( exp ` %s )' % (PROD, TERM))
    # fprodefsum: the product of exponentials is the exponential of the sum
    zdef = w.s([], 'eqid', '( ZZ>= ` 2 ) = ( ZZ>= ` 2 )')
    crpz = st([crp], 'adantr', 'C e. RR+', BZ)
    nuz = w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` 2 ) )' % BZ)
    nrpz = st([nuz, w.inst('uz2m1rp')], 'syl', '( n x. ( n - 1 ) ) e. RR+', BZ)
    trpz = st([crpz, nrpz], 'rpdivcld', '%s e. RR+' % TERM, BZ)
    tcz = st([trpz], 'rpcnd', '%s e. CC' % TERM, BZ)
    efs = st([zdef, muz, tcz], 'fprodefsum',
             'prod_ n e. ( 2 ... M ) ( exp ` %s ) = ( exp ` %s )' % (TERM, SUMT))
    # the sum: C times the telescoping sum
    recbp = st([nrp], 'rpreccld', '( 1 / ( n x. ( n - 1 ) ) ) e. RR+', B)
    recb = st([recbp], 'rpred', '( 1 / ( n x. ( n - 1 ) ) ) e. RR', B)
    reccb = st([recb], 'recnd', '( 1 / ( n x. ( n - 1 ) ) ) e. CC', B)
    ncnb = st([nrp], 'rpcnd', '( n x. ( n - 1 ) ) e. CC', B)
    nneb = st([nrp], 'rpne0d', '( n x. ( n - 1 ) ) =/= 0', B)
    ccb = st([cc], 'adantr', 'C e. CC', B)
    dr = st([ccb, ncnb, nneb], 'divrecd', '%s = ( C x. ( 1 / ( n x. ( n - 1 ) ) ) )' % TERM, B)
    seq = st([dr], 'sumeq2dv',
             '%s = sum_ n e. ( 2 ... M ) ( C x. ( 1 / ( n x. ( n - 1 ) ) ) )' % SUMT)
    mul = st([fin, cc, reccb], 'fsummulc2',
             '( C x. %s ) = sum_ n e. ( 2 ... M ) ( C x. ( 1 / ( n x. ( n - 1 ) ) ) )' % SUM)
    sval = st([seq, mul], 'eqtr4d', '%s = ( C x. %s )' % (SUMT, SUM))
    # C x. SUM <_ C x. 1 = C
    tel = st([mn, w.inst('telsum')], 'syl', '%s <_ 1' % SUM)
    sre = st([fin, recb], 'fsumrecl', '%s e. RR' % SUM)
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    lem = st([sre, one, cr, c0, tel], 'lemul2ad', '( C x. %s ) <_ ( C x. 1 )' % SUM)
    c1 = st([cc], 'mulridd', '( C x. 1 ) = C')
    lem2 = st([lem, c1], 'breqtrd', '( C x. %s ) <_ C' % SUM)
    lem3 = st([sval, lem2], 'eqbrtrd', '%s <_ C' % SUMT)
    stre = st([sre, cr], 'remulcld', '( C x. %s ) e. RR' % SUM)
    stre2 = st([sval, stre], 'eqeltrd', '%s e. RR' % SUMT)
    ef = st([stre2, cr, w.inst('efle')], 'syl2anc',
            '( %s <_ C <-> ( exp ` %s ) <_ ( exp ` C ) )' % (SUMT, SUMT))
    efle_ = st([ef, lem3], 'mpbid', '( exp ` %s ) <_ ( exp ` C )' % SUMT)
    pr = st([efs, efle_], 'eqbrtrd', 'prod_ n e. ( 2 ... M ) ( exp ` %s ) <_ ( exp ` C )' % TERM)
    prodre = st([fin, lhsr], 'fprodrecl', '%s e. RR' % PROD)
    pere = st([fin, efr], 'fprodrecl', 'prod_ n e. ( 2 ... M ) ( exp ` %s ) e. RR' % TERM)
    cere = st([cr], 'reefcld', '( exp ` C ) e. RR')
    w.qed([prodre, pere, cere, ple, pr], 'letrd', '( %s -> %s <_ ( exp ` C ) )' % (A, PROD))
    return w


def prodefub():
    w = W('prodefub', 'The product of 1 + C / ( n x. ( n - 1 ) ) over ( 2 ... M ) is at most exp C.')
    AN = '( M e. NN /\\ C e. RR+ )'
    C1 = '( %s /\\ 2 <_ M )' % AN
    C2 = '( %s /\\ -. 2 <_ M )' % AN
    def st(hyps, ref, f, ante=AN):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    # case 2 <_ M
    m1 = st([], 'simpll', 'M e. NN', C1)
    c1 = st([], 'simplr', 'C e. RR+', C1)
    le1 = st([], 'simpr', '2 <_ M', C1)
    mz1 = st([m1], 'nnzd', 'M e. ZZ', C1)
    tz1 = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ', C1)
    uz = st([tz1, mz1, le1], 'syl3anbrc', 'M e. ( ZZ>= ` 2 )', C1)
    case1 = st([uz, c1, w.inst('prodefublem')], 'syl2anc', '%s <_ ( exp ` C )' % PROD, C1)
    # case -. 2 <_ M
    m2 = st([], 'simpll', 'M e. NN', C2)
    c2 = st([], 'simplr', 'C e. RR+', C2)
    nle = st([], 'simpr', '-. 2 <_ M', C2)
    mr2 = st([m2], 'nnred', 'M e. RR', C2)
    tr2 = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR', C2)
    bi = st([mr2, tr2], 'ltnled', '( M < 2 <-> -. 2 <_ M )', C2)
    lt = st([nle, bi], 'mpbird', 'M < 2', C2)
    mz2 = st([m2], 'nnzd', 'M e. ZZ', C2)
    tz2 = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ', C2)
    fz0 = st([tz2, mz2, w.inst('fzn')], 'syl2anc', '( M < 2 <-> ( 2 ... M ) = (/) )', C2)
    emp = st([fz0, lt], 'mpbid', '( 2 ... M ) = (/)', C2)
    pr0 = st([emp], 'prodeq1d', '%s = prod_ n e. (/) ( 1 + %s )' % (PROD, TERM), C2)
    p0 = st([w.s([], 'prod0', 'prod_ n e. (/) ( 1 + %s ) = 1' % TERM)], 'a1i',
            'prod_ n e. (/) ( 1 + %s ) = 1' % TERM, C2)
    pr1 = st([pr0, p0], 'eqtrd', '%s = 1' % PROD, C2)
    e1 = st([c2, w.inst('efgt1')], 'syl', '1 < ( exp ` C )', C2)
    one2 = w.s([], '1red', '( %s -> 1 e. RR )' % C2)
    cr2 = st([c2], 'rpred', 'C e. RR', C2)
    efre2 = st([cr2], 'reefcld', '( exp ` C ) e. RR', C2)
    e1l = st([one2, efre2, e1], 'ltled', '1 <_ ( exp ` C )', C2)
    case2 = st([pr1, e1l], 'eqbrtrd', '%s <_ ( exp ` C )' % PROD, C2)
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s <_ ( exp ` C ) )' % (AN, PROD))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['fz2m1rp']:
        globals()[f]().run()
