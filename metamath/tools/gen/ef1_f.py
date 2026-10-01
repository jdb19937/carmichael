"""EF1 sections 4-5, the region sums: ef1lft, ef1nr, ef1mr, ef1tl.
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_f.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from lin import linarith, lineq, nlinarith
from cl import formula_of

only = sys.argv[1:]
LY = '( log ` Y )'
Q = '( Y / T )'
QL = '( %s x. ( %s ^ 2 ) )' % (Q, LL)


def yctx(w, A0, yt=None):
    """facts under A0; yt: ( A0 -> YT ) (None: A0 is YT)"""
    d = {}
    if yt is None:
        yt = w.s([], 'id', '( %s -> %s )' % (A0, YT))
    c1 = D(w, A0, 'simpld', [yt], '( Y e. RR /\\ ; ; 1 0 0 <_ Y )')
    c2 = D(w, A0, 'simprd', [yt], '( T e. RR /\\ 2 <_ T )')
    d['yr'] = D(w, A0, 'simpld', [c1], 'Y e. RR'); d['y100'] = D(w, A0, 'simprd', [c1], '; ; 1 0 0 <_ Y')
    d['tr'] = D(w, A0, 'simpld', [c2], 'T e. RR'); d['t2'] = D(w, A0, 'simprd', [c2], '2 <_ T')
    cl = Closure(w, A0, {'Y': ('RR', d['yr']), 'T': ('RR', d['tr'])})
    d['yrp'] = D(w, A0, 'elrpd', [d['yr'], linarith(w, A0, [d['y100']], '0 < Y', closure=cl)], 'Y e. RR+')
    d['trp'] = D(w, A0, 'elrpd', [d['tr'], linarith(w, A0, [d['t2']], '0 < T', closure=cl)], 'T e. RR+')
    d['l4'] = w.s([c1, w.inst('ef1l4')], 'syl', '( %s -> 4 <_ %s )' % (A0, LY))
    d['ly'] = D(w, A0, 'relogcld', [d['yrp']], '%s e. RR' % LY)
    cl.leaf(LY, 'RR', d['ly'])
    d['lyrp'] = D(w, A0, 'elrpd', [d['ly'], linarith(w, A0, [d['l4']], '0 < %s' % LY, closure=cl)], '%s e. RR+' % LY)
    IL = '( 1 / %s )' % LY
    ilrp = D(w, A0, 'rpreccld', [d['lyrp']], '%s e. RR+' % IL)
    il4 = D(w, A0, 'lediv2ad', [a1(w, A0, '4rp', '4 e. RR+'), d['lyrp'], a1(w, A0, '1re', '1 e. RR'), a1(w, A0, '0le1', '0 <_ 1'), d['l4']], '%s <_ ( 1 / 4 )' % IL)
    cl.leaf(IL, 'RR+', ilrp)
    ilp = D(w, A0, 'rpgt0d', [ilrp], '0 < %s' % IL)
    d['c0r'] = cl.mem(C0, 'RR')
    d['c01'] = linarith(w, A0, [ilp], '1 <_ %s' % C0, closure=cl)
    d['c0gt'] = linarith(w, A0, [ilp], '1 < %s' % C0, closure=cl)
    d['c02'] = linarith(w, A0, [il4], '%s <_ 2' % C0, closure=cl)
    d['c0rp'] = D(w, A0, 'elrpd', [d['c0r'], linarith(w, A0, [ilp], '0 < %s' % C0, closure=cl)], '%s e. RR+' % C0)
    d['il'] = IL; d['ilrp'] = ilrp
    y1 = linarith(w, A0, [d['y100']], '1 < Y', closure=cl)
    yc = w.s([D(w, A0, 'jca', [d['yr'], y1], '( Y e. RR /\\ 1 < Y )'), w.inst('ef1yc')], 'syl', '( %s -> ( ( Y ^c %s ) = ( ( exp ` 1 ) x. Y ) /\\ ( Y ^c %s ) <_ ( 3 x. Y ) ) )' % (A0, C0, C0))
    d['yc3'] = D(w, A0, 'simprd', [yc], '( Y ^c %s ) <_ ( 3 x. Y )' % C0)
    d['ycrp'] = D(w, A0, 'rpcxpcld', [d['yrp'], d['c0r']], '( Y ^c %s ) e. RR+' % C0)
    # the floor
    d['fnn'] = w.s([d['yr'], linarith(w, A0, [d['y100']], '1 <_ Y', closure=cl), w.inst('flge1nn')], 'syl2anc', '( %s -> %s e. NN )' % (A0, FL))
    d['fr'] = D(w, A0, 'nnred', [d['fnn']], '%s e. RR' % FL)
    d['fz'] = D(w, A0, 'nnzd', [d['fnn']], '%s e. ZZ' % FL)
    d['fle'] = w.s([d['yr'], w.inst('flle')], 'syl', '( %s -> %s <_ Y )' % (A0, FL))
    d['flt'] = w.s([d['yr'], w.inst('flltp1')], 'syl', '( %s -> Y < ( %s + 1 ) )' % (A0, FL))
    # L = log ( T Y )
    tyrp = D(w, A0, 'rpmulcld', [d['trp'], d['yrp']], '( T x. Y ) e. RR+')
    d['L'] = D(w, A0, 'relogcld', [tyrp], '%s e. RR' % LL)
    d['lt'] = D(w, A0, 'relogcld', [d['trp']], '( log ` T ) e. RR')
    d['lsum'] = D(w, A0, 'relogmuld', [d['trp'], d['yrp']], '%s = ( ( log ` T ) + %s )' % (LL, LY))
    d['lt0'] = w.s([d['tr'], linarith(w, A0, [d['t2']], '1 <_ T', closure=cl), w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` T ) )' % A0)
    d['qrp'] = D(w, A0, 'rpdivcld', [d['yrp'], d['trp']], '%s e. RR+' % Q)
    d['qeq'] = D(w, A0, 'div23d', [D(w, A0, 'rpcnd', [d['yrp']], 'Y e. CC'), D(w, A0, 'recnd', [D(w, A0, 'resqcld', [d['L']], '( %s ^ 2 ) e. RR' % LL)], '( %s ^ 2 ) e. CC' % LL),
                                   D(w, A0, 'rpcnd', [d['trp']], 'T e. CC'), D(w, A0, 'rpne0d', [d['trp']], 'T =/= 0')], '%s = %s' % (YL, QL))
    cl.leaf(LL, 'RR', d['L']); cl.leaf('( log ` T )', 'RR', d['lt']); cl.leaf(Q, 'RR+', d['qrp']); cl.leaf('( Y ^c %s )' % C0, 'RR+', d['ycrp'])
    cl.leaf(FL, 'RR', d['fr'])
    d['cl'] = cl
    return d


def lift(w, C, to0, step, f):
    """( C -> f ) from step: ( A0 -> f ) and to0: ( C -> A0 )"""
    return w.s([to0, step], 'syl', '( %s -> %s )' % (C, f))

# ---------------------------------------------------------------- ef1lft: left of the diagonal
if __name__ == '__main__' and (not only or 'ef1lft' in only):
    w = W('ef1lft', 'The kernel error left of the diagonal, ` 1 <_ n <_ floor y - 1 ` : ` sum Lam ( n ) | K ( y / n ) - 2 pi i | <_ 46 y L ^ 2 / T ` '
          'with ` L = log ( T y ) ` ( ~ ef1kl , ~ ef1pfr ; Lean ` perronSum_sub_psiChi_le ` regions A and mid-left).')
    A0 = YT
    d = yctx(w, A0); cl = d['cl']
    IV = '( 1 ... ( %s - 1 ) )' % FL
    AN_ = '( %s /\\ n e. %s )' % (A0, IV)
    to0 = w.s([], 'simpl', '( %s -> %s )' % (AN_, A0))
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (AN_, IV))
    nn = w.s([nin, w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AN_)
    nle = w.s([nin, w.inst('elfzle2')], 'syl', '( %s -> n <_ ( %s - 1 ) )' % (AN_, FL))
    L_ = lambda k: lift(w, AN_, to0, d[k], formula_of(w, d[k]).split(' -> ', 1)[1][:-2])
    yrn = L_('yr'); fln = L_('fle')
    cln = Closure(w, AN_, {'Y': ('RR', yrn), 'n': ('RR', D(w, AN_, 'nnred', [nn], 'n e. RR')), FL: ('RR', L_('fr'))})
    nly = linarith(w, AN_, [nle, fln], 'n < Y', closure=cln)
    A = '( ( 6 x. ( Y ^c %s ) ) / T )' % C0
    W_ = '( Y / ( n x. ( Y - n ) ) )'
    kl = w.s([D(w, AN_, 'jca', [D(w, AN_, '3jca', [L_('yrp'), L_('c0r'), L_('c01')], '( Y e. RR+ /\\ %s e. RR /\\ 1 <_ %s )' % (C0, C0)),
                                D(w, AN_, 'jca', [L_('trp'), D(w, AN_, 'jca', [nn, nly], '( n e. NN /\\ n < Y )')], '( T e. RR+ /\\ ( n e. NN /\\ n < Y ) )')],
                 '( ( Y e. RR+ /\\ %s e. RR /\\ 1 <_ %s ) /\\ ( T e. RR+ /\\ ( n e. NN /\\ n < Y ) ) )' % (C0, C0)), w.inst('ef1kl')], 'syl',
             '( %s -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )' % (AN_, KC('n'), TPI, A, W_))
    lam = w.s([nn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % AN_)
    lam0 = w.s([nn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` n ) )' % AN_)
    lln = w.s([nn, w.inst('vmalelog')], 'syl', '( %s -> ( Lam ` n ) <_ ( log ` n ) )' % AN_)
    nrp = D(w, AN_, 'nnrpd', [nn], 'n e. RR+')
    lny = w.s([D(w, AN_, 'ltled', [cln.mem('n', 'RR'), yrn, nly], 'n <_ Y'), D(w, AN_, 'logled', [nrp, L_('yrp')], '( n <_ Y <-> ( log ` n ) <_ %s )' % LY)], 'mpbid',
              '( %s -> ( log ` n ) <_ %s )' % (AN_, LY))
    lamle = D(w, AN_, 'letrd', [lam, D(w, AN_, 'relogcld', [nrp], '( log ` n ) e. RR'), L_('ly'), lln, lny], '( Lam ` n ) <_ %s' % LY)
    urp = D(w, AN_, 'rpdivcld', [L_('yrp'), nrp], '( Y / n ) e. RR+')
    kcc = w.s([urp, L_('c0rp'), L_('trp'), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (AN_, KC('n')))
    tpc = D(w, AN_, 'mulcld', [a1(w, AN_, '2cn', '2 e. CC'), D(w, AN_, 'mulcld', [a1(w, AN_, 'ax-icn', '_i e. CC'), a1(w, AN_, 'picn', '_pi e. CC')], '( _i x. _pi ) e. CC')], '%s e. CC' % TPI)
    ab = D(w, AN_, 'abscld', [D(w, AN_, 'subcld', [kcc, tpc], '( %s - %s ) e. CC' % (KC('n'), TPI))], '( abs ` ( %s - %s ) ) e. RR' % (KC('n'), TPI))
    ab0 = D(w, AN_, 'absge0d', [D(w, AN_, 'subcld', [kcc, tpc], '( %s - %s ) e. CC' % (KC('n'), TPI))], '0 <_ ( abs ` ( %s - %s ) )' % (KC('n'), TPI))
    ynrp = D(w, AN_, 'elrpd', [cln.mem('( Y - n )', 'RR'), linarith(w, AN_, [nly], '0 < ( Y - n )', closure=cln)], '( Y - n ) e. RR+')
    wr = D(w, AN_, 'rerpdivcld', [yrn, D(w, AN_, 'rpmulcld', [nrp, ynrp], '( n x. ( Y - n ) ) e. RR+')], '%s e. RR' % W_)
    ar = D(w, AN_, 'rerpdivcld', [D(w, AN_, 'remulcld', [a1(w, AN_, '6re', '6 e. RR'), D(w, AN_, 'rpred', [L_('ycrp')], '( Y ^c %s ) e. RR' % C0)], '( 6 x. ( Y ^c %s ) ) e. RR' % C0), L_('trp')],
           '%s e. RR' % A)
    awr = D(w, AN_, 'remulcld', [ar, wr], '( %s x. %s ) e. RR' % (A, W_))
    en = D(w, AN_, 'lemul12ad', [lam, L_('ly'), ab, awr, lam0, ab0, lamle, kl], '%s <_ ( %s x. ( %s x. %s ) )' % (EL('n'), LY, A, W_))
    K1 = '( %s x. %s )' % (LY, A)
    asc = D(w, AN_, 'mulassd', [D(w, AN_, 'recnd', [L_('ly')], '%s e. CC' % LY), D(w, AN_, 'recnd', [ar], '%s e. CC' % A), D(w, AN_, 'recnd', [wr], '%s e. CC' % W_)],
            '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (K1, W_, LY, A, W_))
    en2 = w.s([en, asc], 'breqtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (AN_, EL('n'), K1, W_))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IV))
    enr = D(w, AN_, 'remulcld', [lam, ab], '%s e. RR' % EL('n'))
    k1r = D(w, A0, 'remulcld', [d['ly'], D(w, A0, 'rerpdivcld', [D(w, A0, 'remulcld', [a1(w, A0, '6re', '6 e. RR'), D(w, A0, 'rpred', [d['ycrp']], '( Y ^c %s ) e. RR' % C0)],
                                                                 '( 6 x. ( Y ^c %s ) ) e. RR' % C0), d['trp']], '%s e. RR' % A)], '%s e. RR' % K1)
    s1 = w.s([fin, enr, D(w, AN_, 'remulcld', [lift(w, AN_, to0, k1r, '%s e. RR' % K1), wr], '( %s x. %s ) e. RR' % (K1, W_)), en2], 'fsumle',
             '( %s -> sum_ n e. %s %s <_ sum_ n e. %s ( %s x. %s ) )' % (A0, IV, EL('n'), IV, K1, W_))
    SW = 'sum_ n e. %s %s' % (IV, W_)
    s2 = w.s([fin, D(w, A0, 'recnd', [k1r], '%s e. CC' % K1), D(w, AN_, 'recnd', [wr], '%s e. CC' % W_)], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ n e. %s ( %s x. %s ) )' % (A0, K1, SW, IV, K1, W_))
    y1 = linarith(w, A0, [d['y100']], '1 <_ Y', closure=cl)
    pf = w.s([D(w, A0, 'jca', [d['yr'], y1], '( Y e. RR /\\ 1 <_ Y )'), w.inst('ef1pfr')], 'syl', '( %s -> %s <_ ( 2 x. ( 1 + %s ) ) )' % (A0, SW, LY))
    swr = w.s([fin, wr], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SW))
    ar0 = D(w, A0, 'rerpdivcld', [D(w, A0, 'remulcld', [a1(w, A0, '6re', '6 e. RR'), D(w, A0, 'rpred', [d['ycrp']], '( Y ^c %s ) e. RR' % C0)], '( 6 x. ( Y ^c %s ) ) e. RR' % C0), d['trp']], '%s e. RR' % A)
    a0 = D(w, A0, 'divge0d', [D(w, A0, 'remulcld', [a1(w, A0, '6re', '6 e. RR'), D(w, A0, 'rpred', [d['ycrp']], '( Y ^c %s ) e. RR' % C0)], '( 6 x. ( Y ^c %s ) ) e. RR' % C0), d['trp'],
                                 D(w, A0, 'rpge0d', [D(w, A0, 'rpmulcld', [a1(w, A0, '6rp', '6 e. RR+'), d['ycrp']], '( 6 x. ( Y ^c %s ) ) e. RR+' % C0)], '0 <_ ( 6 x. ( Y ^c %s ) )' % C0)], '0 <_ %s' % A)
    k10 = D(w, A0, 'mulge0d', [d['ly'], ar0, D(w, A0, 'rpge0d', [d['lyrp']], '0 <_ %s' % LY), a0], '0 <_ %s' % K1)
    cl.leaf(A, 'RR', ar0); cl.leaf(SW, 'RR', swr)
    s3 = D(w, A0, 'lemul2ad', [swr, cl.mem('( 2 x. ( 1 + %s ) )' % LY, 'RR'), k1r, k10, pf], '( %s x. %s ) <_ ( %s x. ( 2 x. ( 1 + %s ) ) )' % (K1, SW, K1, LY))
    # numerics
    six = linarith(w, A0, [d['yc3']], '( 6 x. ( Y ^c %s ) ) <_ ( ; 1 8 x. Y )' % C0, closure=cl)
    a18 = D(w, A0, 'lediv1dd', [cl.mem('( 6 x. ( Y ^c %s ) )' % C0, 'RR'), cl.mem('( ; 1 8 x. Y )', 'RR'), d['trp'], six], '%s <_ ( ( ; 1 8 x. Y ) / T )' % A)
    d18 = D(w, A0, 'divassd', [D(w, A0, 'recnd', [cl.mem('; 1 8', 'RR')], '; 1 8 e. CC'), D(w, A0, 'rpcnd', [d['yrp']], 'Y e. CC'), D(w, A0, 'rpcnd', [d['trp']], 'T e. CC'), D(w, A0, 'rpne0d', [d['trp']], 'T =/= 0')],
            '( ( ; 1 8 x. Y ) / T ) = ( ; 1 8 x. %s )' % Q)
    a18b = w.s([a18, d18], 'breqtrd', '( %s -> %s <_ ( ; 1 8 x. %s ) )' % (A0, A, Q))
    lyl = linarith(w, A0, [d['lsum'], d['lt0']], '%s <_ %s' % (LY, LL), closure=cl)
    l54 = linarith(w, A0, [d['l4'], lyl], '( 1 + %s ) <_ ( ( 5 / 4 ) x. %s )' % (LY, LL), closure=cl)
    p1 = D(w, A0, 'lemul12ad', [d['ly'], d['L'], cl.mem('( 1 + %s )' % LY, 'RR'), cl.mem('( ( 5 / 4 ) x. %s )' % LL, 'RR'), D(w, A0, 'rpge0d', [d['lyrp']], '0 <_ %s' % LY),
                                linarith(w, A0, [d['l4']], '0 <_ ( 1 + %s )' % LY, closure=cl), lyl, l54], '( %s x. ( 1 + %s ) ) <_ ( %s x. ( ( 5 / 4 ) x. %s ) )' % (LY, LY, LL, LL))
    P1 = '( %s x. ( 1 + %s ) )' % (LY, LY)
    p1r = cl.mem(P1, 'RR')
    p10 = D(w, A0, 'mulge0d', [d['ly'], cl.mem('( 1 + %s )' % LY, 'RR'), D(w, A0, 'rpge0d', [d['lyrp']], '0 <_ %s' % LY), linarith(w, A0, [d['l4']], '0 <_ ( 1 + %s )' % LY, closure=cl)], '0 <_ %s' % P1)
    p2 = D(w, A0, 'lemul12ad', [ar0, cl.mem('( ; 1 8 x. %s )' % Q, 'RR'), p1r, cl.mem('( %s x. ( ( 5 / 4 ) x. %s ) )' % (LL, LL), 'RR'), a0, p10, a18b, p1],
           '( %s x. %s ) <_ ( ( ; 1 8 x. %s ) x. ( %s x. ( ( 5 / 4 ) x. %s ) ) )' % (A, P1, Q, LL, LL))
    ql0 = D(w, A0, 'mulge0d', [cl.mem(Q, 'RR'), D(w, A0, 'resqcld', [d['L']], '( %s ^ 2 ) e. RR' % LL), D(w, A0, 'rpge0d', [d['qrp']], '0 <_ %s' % Q), D(w, A0, 'sqge0d', [d['L']], '0 <_ ( %s ^ 2 )' % LL)],
            '0 <_ %s' % QL)
    num = linarith(w, A0, [p2, ql0], '( %s x. ( 2 x. ( 1 + %s ) ) ) <_ ( ; 4 6 x. %s )' % (K1, LY, QL), closure=cl, products=True)
    SE = 'sum_ n e. %s %s' % (IV, EL('n'))
    ser = w.s([fin, enr], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SE))
    t12 = w.s([s1, w.s([s2], 'eqcomd', '( %s -> sum_ n e. %s ( %s x. %s ) = ( %s x. %s ) )' % (A0, IV, K1, W_, K1, SW))], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, SE, K1, SW))
    k1sw = D(w, A0, 'remulcld', [k1r, swr], '( %s x. %s ) e. RR' % (K1, SW))
    k12 = D(w, A0, 'remulcld', [k1r, cl.mem('( 2 x. ( 1 + %s ) )' % LY, 'RR')], '( %s x. ( 2 x. ( 1 + %s ) ) ) e. RR' % (K1, LY))
    t3 = D(w, A0, 'letrd', [ser, k1sw, k12, t12, s3], '%s <_ ( %s x. ( 2 x. ( 1 + %s ) ) )' % (SE, K1, LY))
    q46 = D(w, A0, 'remulcld', [cl.mem('; 4 6', 'RR'), cl.mem(QL, 'RR')], '( ; 4 6 x. %s ) e. RR' % QL)
    t4 = D(w, A0, 'letrd', [ser, k12, q46, t3, num], '%s <_ ( ; 4 6 x. %s )' % (SE, QL))
    w.qed([t4, w.s([w.s([d['qeq']], 'eqcomd', '( %s -> %s = %s )' % (A0, QL, YL))], 'oveq2d', '( %s -> ( ; 4 6 x. %s ) = ( ; 4 6 x. %s ) )' % (A0, QL, YL))], 'breqtrd', STATEMENTS['ef1lft'])
    go(w, only)


def tpiabs(w, A):
    """( A -> TPI e. CC ) and ( A -> ( abs ` TPI ) = ( 2 x. _pi ) )"""
    ic = a1(w, A, 'ax-icn', '_i e. CC'); pc = a1(w, A, 'picn', '_pi e. CC'); c2 = a1(w, A, '2cn', '2 e. CC')
    ipc = D(w, A, 'mulcld', [ic, pc], '( _i x. _pi ) e. CC')
    tc = D(w, A, 'mulcld', [c2, ipc], '%s e. CC' % TPI)
    pr = a1(w, A, 'pire', '_pi e. RR')
    p0 = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), pr, a1(w, A, 'pipos', '0 < _pi')], '0 <_ _pi')
    e = chain(w, A, ['( abs ` %s )' % TPI, '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )', '( 2 x. ( ( abs ` _i ) x. ( abs ` _pi ) ) )', '( 2 x. ( 1 x. _pi ) )', '( 2 x. _pi )'],
              [D(w, A, 'absmuld', [c2, ipc], '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI),
               w.s([D(w, A, 'absidd', [a1(w, A, '2re', '2 e. RR'), a1(w, A, '0le2', '0 <_ 2')], '( abs ` 2 ) = 2'), D(w, A, 'absmuld', [ic, pc], '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )')],
                   'oveq12d', '( %s -> ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. ( ( abs ` _i ) x. ( abs ` _pi ) ) ) )' % A),
               w.s([w.s([a1(w, A, 'absi', '( abs ` _i ) = 1'), D(w, A, 'absidd', [pr, p0], '( abs ` _pi ) = _pi')], 'oveq12d', '( %s -> ( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi ) )' % A)],
                   'oveq2d', '( %s -> ( 2 x. ( ( abs ` _i ) x. ( abs ` _pi ) ) ) = ( 2 x. ( 1 x. _pi ) ) )' % A),
               w.s([D(w, A, 'mullidd', [pc], '( 1 x. _pi ) = _pi')], 'oveq2d', '( %s -> ( 2 x. ( 1 x. _pi ) ) = ( 2 x. _pi ) )' % A)])
    return tc, e


# ---------------------------------------------------------------- ef1nr: the two terms at the diagonal
if __name__ == '__main__' and (not only or 'ef1nr' in only):
    w = W('ef1nr', 'The kernel error at the diagonal, ` n = floor y ` and ` floor y + 1 ` : at most ` 16 L ^ 2 ` ( ~ pkbnd , ~ ef1u4 , '
          '` | 2 pi i | < 8 ` ; Lean ` kerErr_near ` ).')
    A0 = YT
    d = yctx(w, A0); cl = d['cl']
    F1 = '( %s + 1 )' % FL
    f1nn = D(w, A0, 'peano2nnd', [d['fnn']], '%s e. NN' % F1)
    frp = D(w, A0, 'nnrpd', [d['fnn']], '%s e. RR+' % FL); f1rp = D(w, A0, 'nnrpd', [f1nn], '%s e. RR+' % F1)
    f1 = D(w, A0, 'nnge1d', [d['fnn']], '1 <_ %s' % FL)
    lyl = linarith(w, A0, [d['lsum'], d['lt0']], '%s <_ %s' % (LY, LL), closure=cl)
    c0t = linarith(w, A0, [d['c02'], d['t2']], '%s <_ T' % C0, closure=cl)
    TC = '( T / %s )' % C0
    tcrp = D(w, A0, 'rpdivcld', [d['trp'], d['c0rp']], '%s e. RR+' % TC)
    c1m = w.s([D(w, A0, 'mullidd', [D(w, A0, 'rpcnd', [d['c0rp']], '%s e. CC' % C0)], '( 1 x. %s ) = %s' % (C0, C0)), c0t], 'eqbrtrd', '( %s -> ( 1 x. %s ) <_ T )' % (A0, C0))
    tc1 = w.s([c1m, D(w, A0, 'lemuldivd', [a1(w, A0, '1re', '1 e. RR'), d['tr'], d['c0rp']], '( ( 1 x. %s ) <_ T <-> 1 <_ %s )' % (C0, TC))], 'mpbid', '( %s -> 1 <_ %s )' % (A0, TC))
    LTC = '( log ` %s )' % TC
    G = '( 1 + %s )' % LTC
    lg0 = w.s([D(w, A0, 'rpred', [tcrp], '%s e. RR' % TC), tc1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (A0, LTC))
    tct = w.s([D(w, A0, 'lediv2ad', [a1(w, A0, '1rp', '1 e. RR+'), d['c0rp'], d['tr'], D(w, A0, 'rpge0d', [d['trp']], '0 <_ T'), d['c01']], '%s <_ ( T / 1 )' % TC),
               D(w, A0, 'div1d', [D(w, A0, 'rpcnd', [d['trp']], 'T e. CC')], '( T / 1 ) = T')], 'breqtrd', '( %s -> %s <_ T )' % (A0, TC))
    lgl = w.s([tct, D(w, A0, 'logled', [tcrp, d['trp']], '( %s <_ T <-> %s <_ ( log ` T ) )' % (TC, LTC))], 'mpbid', '( %s -> %s <_ ( log ` T ) )' % (A0, LTC))
    ltcr = D(w, A0, 'relogcld', [tcrp], '%s e. RR' % LTC)
    cl.leaf(LTC, 'RR', ltcr)
    gle = linarith(w, A0, [lgl, d['lsum'], d['l4']], '%s <_ ( %s - 3 )' % (G, LL), closure=cl)
    g0 = linarith(w, A0, [lg0], '0 <_ %s' % G, closure=cl)
    tpc, tpa = tpiabs(w, A0)

    def term(N, NRP, ule2, minus):
        U = '( Y / %s )' % N
        urp = D(w, A0, 'rpdivcld', [d['yrp'], NRP], '%s e. RR+' % U)
        u2 = w.s([ule2, D(w, A0, 'ledivmuld', [d['yr'], a1(w, A0, '2re', '2 e. RR'), NRP], '( %s <_ 2 <-> Y <_ ( %s x. 2 ) )' % (U, N))], 'mpbird', '( %s -> %s <_ 2 )' % (A0, U))
        UC = '( %s ^c %s )' % (U, C0)
        u4 = w.s([D(w, A0, 'jca', [D(w, A0, 'jca', [urp, u2], '( %s e. RR+ /\\ %s <_ 2 )' % (U, U)), D(w, A0, 'jca', [d['c0rp'], d['c02']], '( %s e. RR+ /\\ %s <_ 2 )' % (C0, C0))],
                         '( ( %s e. RR+ /\\ %s <_ 2 ) /\\ ( %s e. RR+ /\\ %s <_ 2 ) )' % (U, U, C0, C0)), w.inst('ef1u4')], 'syl', '( %s -> %s <_ 4 )' % (A0, UC))
        ucrp = D(w, A0, 'rpcxpcld', [urp, d['c0r']], '%s e. RR+' % UC)
        cl.leaf(UC, 'RR+', ucrp)
        pb = w.s([D(w, A0, 'jca', [D(w, A0, '3jca', [urp, d['c0rp'], d['trp']], '( %s e. RR+ /\\ %s e. RR+ /\\ T e. RR+ )' % (U, C0)), c0t],
                    '( ( %s e. RR+ /\\ %s e. RR+ /\\ T e. RR+ ) /\\ %s <_ T )' % (U, C0, C0)), w.inst('pkbnd')], 'syl',
                 '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. %s ) )' % (A0, KC(N), UC, G))
        ug = D(w, A0, 'lemul12ad', [cl.mem(UC, 'RR'), a1(w, A0, '4re', '4 e. RR'), cl.mem(G, 'RR'), cl.mem('( %s - 3 )' % LL, 'RR'), D(w, A0, 'rpge0d', [ucrp], '0 <_ %s' % UC), g0, u4, gle],
               '( %s x. %s ) <_ ( 4 x. ( %s - 3 ) )' % (UC, G, LL))
        kcc = w.s([urp, d['c0rp'], d['trp'], w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (A0, KC(N)))
        lam = w.s([NN_[N], w.inst('vmacl')], 'syl', '( %s -> ( Lam ` %s ) e. RR )' % (A0, N))
        return {'U': U, 'UC': UC, 'pb': pb, 'ug': ug, 'kcc': kcc, 'lam': lam, 'ucrp': ucrp}

    NN_ = {FL: d['fnn'], F1: f1nn}
    uF = linarith(w, A0, [d['flt'], f1], 'Y <_ ( %s x. 2 )' % FL, closure=cl)
    uF1 = linarith(w, A0, [d['flt'], f1], 'Y <_ ( %s x. 2 )' % F1, closure=cl)
    tF = term(FL, frp, uF, True); tG = term(F1, f1rp, uF1, False)
    X1 = '( ( ( 2 x. %s ) x. %s ) + ( 2 x. _pi ) )' % (tF['UC'], G)
    X2 = '( ( 2 x. %s ) x. %s )' % (tG['UC'], G)
    kd = D(w, A0, 'subcld', [tF['kcc'], tpc], '( %s - %s ) e. CC' % (KC(FL), TPI))
    a2 = D(w, A0, 'abs2dif2d', [tF['kcc'], tpc], '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (KC(FL), TPI, KC(FL), TPI))
    akF = D(w, A0, 'abscld', [tF['kcc']], '( abs ` %s ) e. RR' % KC(FL))
    atp = D(w, A0, 'abscld', [tpc], '( abs ` %s ) e. RR' % TPI)
    cl.leaf('( abs ` %s )' % KC(FL), 'RR', akF); cl.leaf('( abs ` %s )' % TPI, 'RR', atp); cl.leaf('_pi', 'RR', a1(w, A0, 'pire', '_pi e. RR'))
    cl.leaf('( abs ` ( %s - %s ) )' % (KC(FL), TPI), 'RR', D(w, A0, 'abscld', [kd], '( abs ` ( %s - %s ) ) e. RR' % (KC(FL), TPI)))
    x1 = linarith(w, A0, [a2, tF['pb'], tpa], '( abs ` ( %s - %s ) ) <_ %s' % (KC(FL), TPI, X1), closure=cl, products=True)
    lamF = w.s([d['fnn'], w.inst('vmalelog')], 'syl', '( %s -> ( Lam ` %s ) <_ ( log ` %s ) )' % (A0, FL, FL))
    lf = w.s([d['fle'], D(w, A0, 'logled', [frp, d['yrp']], '( %s <_ Y <-> ( log ` %s ) <_ %s )' % (FL, FL, LY))], 'mpbid', '( %s -> ( log ` %s ) <_ %s )' % (A0, FL, LY))
    cl.leaf('( log ` %s )' % FL, 'RR', D(w, A0, 'relogcld', [frp], '( log ` %s ) e. RR' % FL))
    cl.leaf('( Lam ` %s )' % FL, 'RR', tF['lam'])
    lamFL = linarith(w, A0, [lamF, lf, lyl], '( Lam ` %s ) <_ %s' % (FL, LL), closure=cl)
    lamG = w.s([f1nn, w.inst('vmalelog')], 'syl', '( %s -> ( Lam ` %s ) <_ ( log ` %s ) )' % (A0, F1, F1))
    y1 = linarith(w, A0, [d['y100']], '1 <_ Y', closure=cl)
    f12 = linarith(w, A0, [d['fle'], y1], '%s <_ ( 2 x. Y )' % F1, closure=cl)
    ty = D(w, A0, 'lemul1ad', [a1(w, A0, '2re', '2 e. RR'), d['tr'], d['yr'], D(w, A0, 'rpge0d', [d['yrp']], '0 <_ Y'), d['t2']], '( 2 x. Y ) <_ ( T x. Y )')
    f1ty = D(w, A0, 'letrd', [cl.mem(F1, 'RR'), cl.mem('( 2 x. Y )', 'RR'), cl.mem('( T x. Y )', 'RR'), f12, ty], '%s <_ ( T x. Y )' % F1)
    lg1 = w.s([f1ty, D(w, A0, 'logled', [f1rp, D(w, A0, 'rpmulcld', [d['trp'], d['yrp']], '( T x. Y ) e. RR+')], '( %s <_ ( T x. Y ) <-> ( log ` %s ) <_ %s )' % (F1, F1, LL))], 'mpbid',
              '( %s -> ( log ` %s ) <_ %s )' % (A0, F1, LL))
    cl.leaf('( log ` %s )' % F1, 'RR', D(w, A0, 'relogcld', [f1rp], '( log ` %s ) e. RR' % F1))
    cl.leaf('( Lam ` %s )' % F1, 'RR', tG['lam'])
    lamGL = linarith(w, A0, [lamG, lg1], '( Lam ` %s ) <_ %s' % (F1, LL), closure=cl)
    abd0 = D(w, A0, 'absge0d', [kd], '0 <_ ( abs ` ( %s - %s ) )' % (KC(FL), TPI))
    eF = D(w, A0, 'lemul12ad', [tF['lam'], d['L'], D(w, A0, 'abscld', [kd], '( abs ` ( %s - %s ) ) e. RR' % (KC(FL), TPI)), cl.mem(X1, 'RR'),
                                w.s([d['fnn'], w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` %s ) )' % (A0, FL)), abd0, lamFL, x1], '%s <_ ( %s x. %s )' % (EL(FL), LL, X1))
    eG = D(w, A0, 'lemul12ad', [tG['lam'], d['L'], D(w, A0, 'abscld', [tG['kcc']], '( abs ` %s ) e. RR' % KC(F1)), cl.mem(X2, 'RR'),
                                w.s([f1nn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` %s ) )' % (A0, F1)), D(w, A0, 'absge0d', [tG['kcc']], '0 <_ ( abs ` %s )' % KC(F1)), lamGL, tG['pb']],
           '%s <_ ( %s x. %s )' % (ER(F1), LL, X2))
    cl.leaf('( abs ` %s )' % KC(F1), 'RR', D(w, A0, 'abscld', [tG['kcc']], '( abs ` %s ) e. RR' % KC(F1)))
    l0 = linarith(w, A0, [lyl, d['l4']], '0 <_ %s' % LL, closure=cl)
    m1 = D(w, A0, 'lemul2ad', [cl.mem('( %s x. %s )' % (tF['UC'], G), 'RR'), cl.mem('( 4 x. ( %s - 3 ) )' % LL, 'RR'), d['L'], l0, tF['ug']],
           '( %s x. ( %s x. %s ) ) <_ ( %s x. ( 4 x. ( %s - 3 ) ) )' % (LL, tF['UC'], G, LL, LL))
    m2 = D(w, A0, 'lemul2ad', [cl.mem('( %s x. %s )' % (tG['UC'], G), 'RR'), cl.mem('( 4 x. ( %s - 3 ) )' % LL, 'RR'), d['L'], l0, tG['ug']],
           '( %s x. ( %s x. %s ) ) <_ ( %s x. ( 4 x. ( %s - 3 ) ) )' % (LL, tG['UC'], G, LL, LL))
    pi4 = w.s([w.s([], 'pigt2lt4', '( 2 < _pi /\\ _pi < 4 )')], 'simpri', '_pi < 4')
    pi4d = D(w, A0, 'ltled', [a1(w, A0, 'pire', '_pi e. RR'), a1(w, A0, '4re', '4 e. RR'), w.s([pi4], 'a1i', '( %s -> _pi < 4 )' % A0)], '_pi <_ 4')
    m3 = D(w, A0, 'lemul2ad', [a1(w, A0, 'pire', '_pi e. RR'), a1(w, A0, '4re', '4 e. RR'), d['L'], l0, pi4d], '( %s x. _pi ) <_ ( %s x. 4 )' % (LL, LL))
    w.qed([linarith(w, A0, [eF, eG, m1, m2, m3, l0], '( %s + %s ) <_ ( ; 1 6 x. %s )' % (EL(FL), ER(F1), L2), closure=cl, products=True)], 'idi', STATEMENTS['ef1nr'])
    go(w, only)

# ---------------------------------------------------------------- ef1mr: right of the diagonal, up to 2 F + 1
if __name__ == '__main__' and (not only or 'ef1mr' in only):
    w = W('ef1mr', 'The kernel error right of the diagonal, ` floor y + 2 <_ n <_ 2 floor y + 1 ` : at most ` 45 y L ^ 2 / T ` '
          '( ~ ef1kr , ` n / ( n - y ) <_ 3 y / ( n - floor y - 1 ) ` , a shifted harmonic sum; Lean ` kerErr_mid_right ` , ` sum_inv_gap_right ` ).')
    A0 = YT
    d = yctx(w, A0); cl = d['cl']
    F1 = '( %s + 1 )' % FL
    IVR = '( ( %s + 2 ) ... ( ( 2 x. %s ) + 1 ) )' % (FL, FL)
    AN_ = '( %s /\\ n e. %s )' % (A0, IVR)
    to0 = w.s([], 'simpl', '( %s -> %s )' % (AN_, A0))
    L_ = lambda k: lift(w, AN_, to0, d[k], formula_of(w, d[k]).split(' -> ', 1)[1][:-2])
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (AN_, IVR))
    nz = w.s([nin, w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % AN_)
    nge = w.s([nin, w.inst('elfzle1')], 'syl', '( %s -> ( %s + 2 ) <_ n )' % (AN_, FL))
    nle = w.s([nin, w.inst('elfzle2')], 'syl', '( %s -> n <_ ( ( 2 x. %s ) + 1 ) )' % (AN_, FL))
    cln = Closure(w, AN_, {'Y': ('RR', L_('yr')), 'n': ('RR', D(w, AN_, 'zred', [nz], 'n e. RR')), FL: ('RR', L_('fr')), 'T': ('RR', L_('tr'))})
    f1n = L_('fnn')
    n1 = linarith(w, AN_, [nge, D(w, AN_, 'nnge1d', [f1n], '1 <_ %s' % FL)], '1 <_ n', closure=cln)
    nn = w.s([D(w, AN_, 'jca', [nz, n1], '( n e. ZZ /\\ 1 <_ n )'), w.s([], 'elnnz1', '( n e. NN <-> ( n e. ZZ /\\ 1 <_ n ) )')], 'sylibr', '( %s -> n e. NN )' % AN_)
    flt = L_('flt'); fle = L_('fle'); y100 = L_('y100')
    yln = linarith(w, AN_, [nge, flt], 'Y < n', closure=cln)
    kr = w.s([D(w, AN_, 'jca', [D(w, AN_, 'jca', [L_('yrp'), L_('c0rp')], '( Y e. RR+ /\\ %s e. RR+ )' % C0), D(w, AN_, 'jca', [L_('trp'), D(w, AN_, 'jca', [nn, yln], '( n e. NN /\\ Y < n )')],
                                                                                                                 '( T e. RR+ /\\ ( n e. NN /\\ Y < n ) )')],
                 '( ( Y e. RR+ /\\ %s e. RR+ ) /\\ ( T e. RR+ /\\ ( n e. NN /\\ Y < n ) ) )' % C0), w.inst('ef1kr')], 'syl', '( %s -> ( abs ` %s ) <_ ( ( 6 / T ) x. ( n / ( n - Y ) ) ) )' % (AN_, KC('n')))
    DN = '( n - %s )' % F1
    dnrp = D(w, AN_, 'elrpd', [cln.mem(DN, 'RR'), linarith(w, AN_, [nge], '0 < %s' % DN, closure=cln)], '%s e. RR+' % DN)
    nyrp = D(w, AN_, 'elrpd', [cln.mem('( n - Y )', 'RR'), linarith(w, AN_, [yln], '0 < ( n - Y )', closure=cln)], '( n - Y ) e. RR+')
    n3y = linarith(w, AN_, [nle, fle, y100], 'n <_ ( 3 x. Y )', closure=cln)
    q1 = D(w, AN_, 'lediv1dd', [cln.mem('n', 'RR'), cln.mem('( 3 x. Y )', 'RR'), nyrp, n3y], '( n / ( n - Y ) ) <_ ( ( 3 x. Y ) / ( n - Y ) )')
    y3rp = D(w, AN_, 'rpmulcld', [a1(w, AN_, '3rp', '3 e. RR+'), L_('yrp')], '( 3 x. Y ) e. RR+')
    q2 = D(w, AN_, 'lediv2ad', [dnrp, nyrp, cln.mem('( 3 x. Y )', 'RR'), D(w, AN_, 'rpge0d', [y3rp], '0 <_ ( 3 x. Y )'), linarith(w, AN_, [flt], '%s <_ ( n - Y )' % DN, closure=cln)],
           '( ( 3 x. Y ) / ( n - Y ) ) <_ ( ( 3 x. Y ) / %s )' % DN)
    ndr = D(w, AN_, 'rerpdivcld', [cln.mem('n', 'RR'), nyrp], '( n / ( n - Y ) ) e. RR')
    m1r = D(w, AN_, 'rerpdivcld', [cln.mem('( 3 x. Y )', 'RR'), nyrp], '( ( 3 x. Y ) / ( n - Y ) ) e. RR')
    m2r = D(w, AN_, 'rerpdivcld', [cln.mem('( 3 x. Y )', 'RR'), dnrp], '( ( 3 x. Y ) / %s ) e. RR' % DN)
    q12 = D(w, AN_, 'letrd', [ndr, m1r, m2r, q1, q2], '( n / ( n - Y ) ) <_ ( ( 3 x. Y ) / %s )' % DN)
    s6t = D(w, AN_, 'rerpdivcld', [a1(w, AN_, '6re', '6 e. RR'), L_('trp')], '( 6 / T ) e. RR')
    s6t0 = D(w, AN_, 'divge0d', [a1(w, AN_, '6re', '6 e. RR'), L_('trp'), D(w, AN_, 'ltled', [a1(w, AN_, '0re', '0 e. RR'), a1(w, AN_, '6re', '6 e. RR'), a1(w, AN_, '6pos', '0 < 6')], '0 <_ 6')],
             '0 <_ ( 6 / T )')
    KB = '( ( 6 / T ) x. ( ( 3 x. Y ) / %s ) )' % DN
    kb = D(w, AN_, 'letrd', [D(w, AN_, 'abscld', [w.s([D(w, AN_, 'rpdivcld', [L_('yrp'), D(w, AN_, 'nnrpd', [nn], 'n e. RR+')], '( Y / n ) e. RR+'), L_('c0rp'), L_('trp'), w.inst('pkcl')], 'syl3anc',
                                                       '( %s -> %s e. CC )' % (AN_, KC('n')))], '( abs ` %s ) e. RR' % KC('n')),
                             D(w, AN_, 'remulcld', [s6t, ndr], '( ( 6 / T ) x. ( n / ( n - Y ) ) ) e. RR'), D(w, AN_, 'remulcld', [s6t, m2r], '%s e. RR' % KB), kr,
                             D(w, AN_, 'lemul2ad', [ndr, m2r, s6t, s6t0, q12], '( ( 6 / T ) x. ( n / ( n - Y ) ) ) <_ %s' % KB)], '( abs ` %s ) <_ %s' % (KC('n'), KB))
    TY = '( T x. Y )'
    clA = Closure(w, A0, {'Y': ('RR', d['yr']), 'T': ('RR', d['tr'])})
    ty200 = D(w, A0, 'lemul12ad', [a1(w, A0, '2re', '2 e. RR'), d['tr'], clA.mem('; ; 1 0 0', 'RR'), d['yr'], a1(w, A0, '0le2', '0 <_ 2'), linarith(w, A0, [], '0 <_ ; ; 1 0 0', closure=clA), d['t2'], d['y100']],
              '( 2 x. ; ; 1 0 0 ) <_ %s' % TY)
    tyr = clA.mem(TY, 'RR')
    ty0 = linarith(w, A0, [ty200], '0 <_ %s' % TY, closure=clA)
    tyty = D(w, A0, 'lemul1ad', [clA.mem('( 2 x. ; ; 1 0 0 )', 'RR'), tyr, tyr, ty0, ty200], '( ( 2 x. ; ; 1 0 0 ) x. %s ) <_ ( %s x. %s )' % (TY, TY, TY))
    ty2y = D(w, A0, 'lemul1ad', [a1(w, A0, '2re', '2 e. RR'), d['tr'], d['yr'], D(w, A0, 'rpge0d', [d['yrp']], '0 <_ Y'), d['t2']], '( 2 x. Y ) <_ ( T x. Y )')
    y3 = linarith(w, A0, [tyty, ty2y, D(w, A0, 'rpge0d', [d['yrp']], '0 <_ Y')], '( 3 x. Y ) <_ ( %s x. %s )' % (TY, TY), closure=clA, products=True)
    nty = linarith(w, AN_, [n3y, lift(w, AN_, to0, y3, '( 3 x. Y ) <_ ( %s x. %s )' % (TY, TY))], 'n <_ ( %s x. %s )' % (TY, TY), closure=cln, products=True)
    tyrp = D(w, AN_, 'rpmulcld', [L_('trp'), L_('yrp')], '%s e. RR+' % TY)
    nrp = D(w, AN_, 'nnrpd', [nn], 'n e. RR+')
    lnt = w.s([nty, D(w, AN_, 'logled', [nrp, D(w, AN_, 'rpmulcld', [tyrp, tyrp], '( %s x. %s ) e. RR+' % (TY, TY))], '( n <_ ( %s x. %s ) <-> ( log ` n ) <_ ( log ` ( %s x. %s ) ) )' % (TY, TY, TY, TY))],
              'mpbid', '( %s -> ( log ` n ) <_ ( log ` ( %s x. %s ) ) )' % (AN_, TY, TY))
    l2 = D(w, AN_, 'relogmuld', [tyrp, tyrp], '( log ` ( %s x. %s ) ) = ( %s + %s )' % (TY, TY, LL, LL))
    LL2 = '( %s + %s )' % (LL, LL)
    lam = w.s([nn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % AN_)
    lamle = D(w, AN_, 'letrd', [lam, D(w, AN_, 'relogcld', [nrp], '( log ` n ) e. RR'), D(w, AN_, 'readdcld', [L_('L'), L_('L')], '%s e. RR' % LL2),
                                w.s([nn, w.inst('vmalelog')], 'syl', '( %s -> ( Lam ` n ) <_ ( log ` n ) )' % AN_), w.s([lnt, l2], 'breqtrd', '( %s -> ( log ` n ) <_ %s )' % (AN_, LL2))],
            '( Lam ` n ) <_ %s' % LL2)
    kcn = w.s([D(w, AN_, 'rpdivcld', [L_('yrp'), nrp], '( Y / n ) e. RR+'), L_('c0rp'), L_('trp'), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (AN_, KC('n')))
    en = D(w, AN_, 'lemul12ad', [lam, D(w, AN_, 'readdcld', [L_('L'), L_('L')], '%s e. RR' % LL2), D(w, AN_, 'abscld', [kcn], '( abs ` %s ) e. RR' % KC('n')), D(w, AN_, 'remulcld', [s6t, m2r], '%s e. RR' % KB),
                                  w.s([nn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` n ) )' % AN_), D(w, AN_, 'absge0d', [kcn], '0 <_ ( abs ` %s )' % KC('n')), lamle, kb],
            '%s <_ ( %s x. %s )' % (ER('n'), LL2, KB))
    ID = '( 1 / %s )' % DN
    K2 = '( %s x. ( ( 6 / T ) x. ( 3 x. Y ) ) )' % LL2
    dr = D(w, AN_, 'divrecd', [D(w, AN_, 'rpcnd', [y3rp], '( 3 x. Y ) e. CC'), D(w, AN_, 'rpcnd', [dnrp], '%s e. CC' % DN), D(w, AN_, 'rpne0d', [dnrp], '%s =/= 0' % DN)],
           '( ( 3 x. Y ) / %s ) = ( ( 3 x. Y ) x. %s )' % (DN, ID))
    idr = D(w, AN_, 'rpreccld', [dnrp], '%s e. RR+' % ID)
    cln.leaf('( 6 / T )', 'RR', s6t); cln.leaf(ID, 'RR+', idr); cln.leaf(LL, 'RR', L_('L'))
    e2 = w.s([w.s([w.s([dr], 'oveq2d', '( %s -> %s = ( ( 6 / T ) x. ( ( 3 x. Y ) x. %s ) ) )' % (AN_, KB, ID))], 'oveq2d',
                  '( %s -> ( %s x. %s ) = ( %s x. ( ( 6 / T ) x. ( ( 3 x. Y ) x. %s ) ) ) )' % (AN_, LL2, KB, LL2, ID)),
              lineq(w, AN_, '( %s x. ( ( 6 / T ) x. ( ( 3 x. Y ) x. %s ) ) )' % (LL2, ID), '( %s x. %s )' % (K2, ID), closure=cln, products=True)], 'eqtrd',
             '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (AN_, LL2, KB, K2, ID))
    en2 = w.s([en, e2], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (AN_, ER('n'), K2, ID))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IVR))
    s6t0A = D(w, A0, 'rerpdivcld', [a1(w, A0, '6re', '6 e. RR'), d['trp']], '( 6 / T ) e. RR')
    cl.leaf('( 6 / T )', 'RR', s6t0A)
    k2r = cl.mem(K2, 'RR')
    enr = D(w, AN_, 'remulcld', [lam, D(w, AN_, 'abscld', [kcn], '( abs ` %s ) e. RR' % KC('n'))], '%s e. RR' % ER('n'))
    kid = D(w, AN_, 'remulcld', [lift(w, AN_, to0, k2r, '%s e. RR' % K2), D(w, AN_, 'rpred', [idr], '%s e. RR' % ID)], '( %s x. %s ) e. RR' % (K2, ID))
    s1 = w.s([fin, enr, kid, en2], 'fsumle', '( %s -> sum_ n e. %s %s <_ sum_ n e. %s ( %s x. %s ) )' % (A0, IVR, ER('n'), IVR, K2, ID))
    SID = 'sum_ n e. %s %s' % (IVR, ID)
    s2 = w.s([fin, D(w, A0, 'recnd', [k2r], '%s e. CC' % K2), D(w, AN_, 'rpcnd', [idr], '%s e. CC' % ID)], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ n e. %s ( %s x. %s ) )' % (A0, K2, SID, IVR, K2, ID))
    HB = 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % FL
    AMF = '( %s /\\ m e. ( 1 ... %s ) )' % (A0, FL)
    mcc = D(w, AMF, 'recnd', [D(w, AMF, 'nnrecred', [w.s([w.s([], 'simpr', '( %s -> m e. ( 1 ... %s ) )' % (AMF, FL)), w.inst('elfznn')], 'syl', '( %s -> m e. NN )' % AMF)], '( 1 / m ) e. RR')], '( 1 / m ) e. CC')
    RV = '( ( 1 + %s ) ... ( %s + %s ) )' % (F1, FL, F1)
    sh = w.s([D(w, A0, 'peano2zd', [d['fz']], '%s e. ZZ' % F1), a1(w, A0, '1z', '1 e. ZZ'), d['fz'], mcc,
              w.s([], 'oveq2', '( m = ( n - %s ) -> ( 1 / m ) = ( 1 / ( n - %s ) ) )' % (F1, F1))], 'fsumshft', '( %s -> %s = sum_ n e. %s %s )' % (A0, HB, RV, ID))
    iv = w.s([lineq(w, A0, '( 1 + %s )' % F1, '( %s + 2 )' % FL, closure=cl), lineq(w, A0, '( %s + %s )' % (FL, F1), '( ( 2 x. %s ) + 1 )' % FL, closure=cl)], 'oveq12d', '( %s -> %s = %s )' % (A0, RV, IVR))
    sh2 = w.s([sh, w.s([iv], 'sumeq1d', '( %s -> sum_ n e. %s %s = %s )' % (A0, RV, ID, SID))], 'eqtrd', '( %s -> %s = %s )' % (A0, HB, SID))
    y1 = linarith(w, A0, [d['y100']], '1 <_ Y', closure=cl)
    hb = w.s([D(w, A0, 'jca', [d['yr'], y1], '( Y e. RR /\\ 1 <_ Y )'), w.inst('harmonicubnd')], 'syl', '( %s -> %s <_ ( %s + 1 ) )' % (A0, HB, LY))
    sidle = w.s([sh2, hb], 'eqbrtrrd', '( %s -> %s <_ ( %s + 1 ) )' % (A0, SID, LY))
    sidr = w.s([fin, D(w, AN_, 'rpred', [idr], '%s e. RR' % ID)], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SID))
    lyl = linarith(w, A0, [d['lsum'], d['lt0']], '%s <_ %s' % (LY, LL), closure=cl)
    l0 = linarith(w, A0, [lyl, d['l4']], '0 <_ %s' % LL, closure=cl)
    k20 = D(w, A0, 'mulge0d', [cl.mem(LL2, 'RR'), cl.mem('( ( 6 / T ) x. ( 3 x. Y ) )', 'RR'), linarith(w, A0, [l0], '0 <_ %s' % LL2, closure=cl),
                               D(w, A0, 'mulge0d', [s6t0A, cl.mem('( 3 x. Y )', 'RR'), D(w, A0, 'divge0d', [a1(w, A0, '6re', '6 e. RR'), d['trp'], D(w, A0, 'ltled', [a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '6re', '6 e. RR'), a1(w, A0, '6pos', '0 < 6')], '0 <_ 6')], '0 <_ ( 6 / T )'),
                                                     D(w, A0, 'rpge0d', [D(w, A0, 'rpmulcld', [a1(w, A0, '3rp', '3 e. RR+'), d['yrp']], '( 3 x. Y ) e. RR+')], '0 <_ ( 3 x. Y )')], '0 <_ ( ( 6 / T ) x. ( 3 x. Y ) )')],
              '0 <_ %s' % K2)
    cl.leaf(SID, 'RR', sidr)
    s3 = D(w, A0, 'lemul2ad', [sidr, cl.mem('( %s + 1 )' % LY, 'RR'), k2r, k20, sidle], '( %s x. %s ) <_ ( %s x. ( %s + 1 ) )' % (K2, SID, K2, LY))
    l54 = linarith(w, A0, [d['l4'], lyl], '( %s + 1 ) <_ ( ( 5 / 4 ) x. %s )' % (LY, LL), closure=cl)
    s4 = D(w, A0, 'lemul2ad', [cl.mem('( %s + 1 )' % LY, 'RR'), cl.mem('( ( 5 / 4 ) x. %s )' % LL, 'RR'), k2r, k20, l54], '( %s x. ( %s + 1 ) ) <_ ( %s x. ( ( 5 / 4 ) x. %s ) )' % (K2, LY, K2, LL))
    tc = D(w, A0, 'rpcnd', [d['trp']], 'T e. CC'); tne = D(w, A0, 'rpne0d', [d['trp']], 'T =/= 0')
    y3c = D(w, A0, 'recnd', [cl.mem('( 3 x. Y )', 'RR')], '( 3 x. Y ) e. CC')
    kq = chain(w, A0, ['( ( 6 / T ) x. ( 3 x. Y ) )', '( 6 x. ( ( 3 x. Y ) / T ) )', '( 6 x. ( 3 x. %s ) )' % Q],
               [D(w, A0, 'div32d', [a1(w, A0, '6cn', '6 e. CC'), tc, y3c, tne], '( ( 6 / T ) x. ( 3 x. Y ) ) = ( 6 x. ( ( 3 x. Y ) / T ) )'),
                w.s([D(w, A0, 'divassd', [a1(w, A0, '3cn', '3 e. CC'), D(w, A0, 'rpcnd', [d['yrp']], 'Y e. CC'), tc, tne], '( ( 3 x. Y ) / T ) = ( 3 x. %s )' % Q)], 'oveq2d',
                    '( %s -> ( 6 x. ( ( 3 x. Y ) / T ) ) = ( 6 x. ( 3 x. %s ) ) )' % (A0, Q))])
    K2Q = '( %s x. ( 6 x. ( 3 x. %s ) ) )' % (LL2, Q)
    s5 = w.s([w.s([w.s([kq], 'oveq2d', '( %s -> %s = %s )' % (A0, K2, K2Q))], 'oveq1d', '( %s -> ( %s x. ( ( 5 / 4 ) x. %s ) ) = ( %s x. ( ( 5 / 4 ) x. %s ) ) )' % (A0, K2, LL, K2Q, LL)),
              lineq(w, A0, '( %s x. ( ( 5 / 4 ) x. %s ) )' % (K2Q, LL), '( ; 4 5 x. %s )' % QL, closure=cl, products=True)], 'eqtrd', '( %s -> ( %s x. ( ( 5 / 4 ) x. %s ) ) = ( ; 4 5 x. %s ) )' % (A0, K2, LL, QL))
    SE = 'sum_ n e. %s %s' % (IVR, ER('n'))
    ser = w.s([fin, enr], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SE))
    c1 = w.s([s1, w.s([s2], 'eqcomd', '( %s -> sum_ n e. %s ( %s x. %s ) = ( %s x. %s ) )' % (A0, IVR, K2, ID, K2, SID))], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, SE, K2, SID))
    c2 = D(w, A0, 'letrd', [ser, cl.mem('( %s x. %s )' % (K2, SID), 'RR'), cl.mem('( %s x. ( %s + 1 ) )' % (K2, LY), 'RR'), c1, s3], '%s <_ ( %s x. ( %s + 1 ) )' % (SE, K2, LY))
    c3 = D(w, A0, 'letrd', [ser, cl.mem('( %s x. ( %s + 1 ) )' % (K2, LY), 'RR'), cl.mem('( %s x. ( ( 5 / 4 ) x. %s ) )' % (K2, LL), 'RR'), c2, s4], '%s <_ ( %s x. ( ( 5 / 4 ) x. %s ) )' % (SE, K2, LL))
    c4 = w.s([c3, s5], 'breqtrd', '( %s -> %s <_ ( ; 4 5 x. %s ) )' % (A0, SE, QL))
    w.qed([c4, w.s([w.s([d['qeq']], 'eqcomd', '( %s -> %s = %s )' % (A0, QL, YL))], 'oveq2d', '( %s -> ( ; 4 5 x. %s ) = ( ; 4 5 x. %s ) )' % (A0, QL, YL))], 'breqtrd', STATEMENTS['ef1mr'])
    go(w, only)

# ---------------------------------------------------------------- ef1tl: the tail, 2 F + 2 <_ n <_ M
if __name__ == '__main__' and (not only or 'ef1tl' in only):
    w = W('ef1tl', 'The kernel error in the far right, ` 2 floor y + 2 <_ n <_ M ` : at most ` 216 y L ^ 2 / T ` for every ` M ` '
          '( ~ ef1kt , ` ( y / n ) ^ c = y ^ c n ^ -c ` , the von Mangoldt series at ` c = 1 + 1 / log y ` , ~ vmbnd ; Lean ` kerErr_far_right ` and the tail of '
          '` perronSum_sub_psiChi_le ` ).')
    A0 = STATEMENTS['ef1tl'].split(' -> sum_')[0][2:]
    yt = D(w, A0, 'simpl', [], YT)
    d = yctx(w, A0, yt); cl = d['cl']
    mz = D(w, A0, 'simpr', [], 'M e. ( ZZ>= ` %s )' % F2)
    IVT = '( %s ... M )' % F2
    AN_ = '( %s /\\ n e. %s )' % (A0, IVT)
    to0 = w.s([], 'simpl', '( %s -> %s )' % (AN_, A0))
    L_ = lambda k: lift(w, AN_, to0, d[k], formula_of(w, d[k]).split(' -> ', 1)[1][:-2])
    f2nn = D(w, A0, 'nnaddcld', [D(w, A0, 'nnmulcld', [a1(w, A0, '2nn', '2 e. NN'), d['fnn']], '( 2 x. %s ) e. NN' % FL), a1(w, A0, '2nn', '2 e. NN')], '%s e. NN' % F2)
    ssn = w.s([f2nn, w.inst('fzssnn')], 'syl', '( %s -> %s C_ NN )' % (A0, IVT))
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (AN_, IVT))
    nn = w.s([lift(w, AN_, to0, ssn, '%s C_ NN' % IVT), nin], 'sseldd', '( %s -> n e. NN )' % AN_)
    nge = w.s([nin, w.inst('elfzle1')], 'syl', '( %s -> %s <_ n )' % (AN_, F2))
    cln = Closure(w, AN_, {'Y': ('RR', L_('yr')), 'n': ('RR', D(w, AN_, 'nnred', [nn], 'n e. RR')), FL: ('RR', L_('fr')), 'T': ('RR', L_('tr'))})
    y2n = linarith(w, AN_, [nge, L_('flt')], '( 2 x. Y ) <_ n', closure=cln)
    UCn = '( ( Y / n ) ^c %s )' % C0
    kt = w.s([D(w, AN_, 'jca', [D(w, AN_, 'jca', [L_('yrp'), L_('c0rp')], '( Y e. RR+ /\\ %s e. RR+ )' % C0), D(w, AN_, 'jca', [L_('trp'), D(w, AN_, 'jca', [nn, y2n], '( n e. NN /\\ ( 2 x. Y ) <_ n )')],
                                                                                                                 '( T e. RR+ /\\ ( n e. NN /\\ ( 2 x. Y ) <_ n ) )')],
                 '( ( Y e. RR+ /\\ %s e. RR+ ) /\\ ( T e. RR+ /\\ ( n e. NN /\\ ( 2 x. Y ) <_ n ) ) )' % C0), w.inst('ef1kt')], 'syl', '( %s -> ( abs ` %s ) <_ ( ( ; 1 2 / T ) x. %s ) )' % (AN_, KC('n'), UCn))
    nrp = D(w, AN_, 'nnrpd', [nn], 'n e. RR+')
    YCs = '( Y ^c %s )' % C0; NCs = '( n ^c %s )' % C0; NNC = '( n ^c -u %s )' % C0
    c0c = D(w, AN_, 'recnd', [L_('c0r')], '%s e. CC' % C0)
    dcx = D(w, AN_, 'divcxpd', [L_('yr'), D(w, AN_, 'rpge0d', [L_('yrp')], '0 <_ Y'), nrp, c0c], '%s = ( %s / %s )' % (UCn, YCs, NCs))
    ncrp = D(w, AN_, 'rpcxpcld', [nrp, L_('c0r')], '%s e. RR+' % NCs)
    ycc = D(w, AN_, 'rpcnd', [L_('ycrp')], '%s e. CC' % YCs)
    ng = w.s([D(w, AN_, 'rpcnd', [nrp], 'n e. CC'), D(w, AN_, 'rpne0d', [nrp], 'n =/= 0'), c0c, w.inst('cxpneg')], 'syl3anc', '( %s -> %s = ( 1 / %s ) )' % (AN_, NNC, NCs))
    urw = chain(w, AN_, [UCn, '( %s / %s )' % (YCs, NCs), '( %s x. ( 1 / %s ) )' % (YCs, NCs), '( %s x. %s )' % (YCs, NNC)],
                [dcx, D(w, AN_, 'divrecd', [ycc, D(w, AN_, 'rpcnd', [ncrp], '%s e. CC' % NCs), D(w, AN_, 'rpne0d', [ncrp], '%s =/= 0' % NCs)], '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (YCs, NCs, YCs, NCs)),
                 w.s([w.s([ng], 'eqcomd', '( %s -> ( 1 / %s ) = %s )' % (AN_, NCs, NNC))], 'oveq2d', '( %s -> ( %s x. ( 1 / %s ) ) = ( %s x. %s ) )' % (AN_, YCs, NCs, YCs, NNC))])
    lam = w.s([nn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % AN_)
    lam0 = w.s([nn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` n ) )' % AN_)
    kcn = w.s([D(w, AN_, 'rpdivcld', [L_('yrp'), nrp], '( Y / n ) e. RR+'), L_('c0rp'), L_('trp'), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (AN_, KC('n')))
    t12 = D(w, AN_, 'rerpdivcld', [cln.mem('; 1 2', 'RR'), L_('trp')], '( ; 1 2 / T ) e. RR')
    ucr = D(w, AN_, 'rpred', [D(w, AN_, 'rpcxpcld', [D(w, AN_, 'rpdivcld', [L_('yrp'), nrp], '( Y / n ) e. RR+'), L_('c0r')], '%s e. RR+' % UCn)], '%s e. RR' % UCn)
    KB = '( ( ; 1 2 / T ) x. %s )' % UCn
    en = D(w, AN_, 'lemul2ad', [D(w, AN_, 'abscld', [kcn], '( abs ` %s ) e. RR' % KC('n')), D(w, AN_, 'remulcld', [t12, ucr], '%s e. RR' % KB), lam, lam0, kt], '%s <_ ( ( Lam ` n ) x. %s )' % (ER('n'), KB))
    K3 = '( ( ; 1 2 / T ) x. %s )' % YCs
    VT = '( ( Lam ` n ) x. %s )' % NNC
    nncr = D(w, AN_, 'rpred', [D(w, AN_, 'rpcxpcld', [nrp, D(w, AN_, 'renegcld', [L_('c0r')], '-u %s e. RR' % C0)], '%s e. RR+' % NNC)], '%s e. RR' % NNC)
    cln.leaf('( ; 1 2 / T )', 'RR', t12); cln.leaf(YCs, 'RR+', L_('ycrp')); cln.leaf('( Lam ` n )', 'RR', lam); cln.leaf(NNC, 'RR', nncr)
    e2 = w.s([w.s([w.s([urw], 'oveq2d', '( %s -> %s = ( ( ; 1 2 / T ) x. ( %s x. %s ) ) )' % (AN_, KB, YCs, NNC))], 'oveq2d',
                  '( %s -> ( ( Lam ` n ) x. %s ) = ( ( Lam ` n ) x. ( ( ; 1 2 / T ) x. ( %s x. %s ) ) ) )' % (AN_, KB, YCs, NNC)),
              lineq(w, AN_, '( ( Lam ` n ) x. ( ( ; 1 2 / T ) x. ( %s x. %s ) ) )' % (YCs, NNC), '( %s x. %s )' % (K3, VT), closure=cln, products=True)], 'eqtrd',
             '( %s -> ( ( Lam ` n ) x. %s ) = ( %s x. %s ) )' % (AN_, KB, K3, VT))
    en2 = w.s([en, e2], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (AN_, ER('n'), K3, VT))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IVT))
    t12A = D(w, A0, 'rerpdivcld', [cl.mem('; 1 2', 'RR'), d['trp']], '( ; 1 2 / T ) e. RR')
    cl.leaf('( ; 1 2 / T )', 'RR', t12A)
    k3r = cl.mem(K3, 'RR')
    enr = D(w, AN_, 'remulcld', [lam, D(w, AN_, 'abscld', [kcn], '( abs ` %s ) e. RR' % KC('n'))], '%s e. RR' % ER('n'))
    vtr = D(w, AN_, 'remulcld', [lam, nncr], '%s e. RR' % VT)
    kvr = D(w, AN_, 'remulcld', [lift(w, AN_, to0, k3r, '%s e. RR' % K3), vtr], '( %s x. %s ) e. RR' % (K3, VT))
    s1 = w.s([fin, enr, kvr, en2], 'fsumle', '( %s -> sum_ n e. %s %s <_ sum_ n e. %s ( %s x. %s ) )' % (A0, IVT, ER('n'), IVT, K3, VT))
    SV = 'sum_ n e. %s %s' % (IVT, VT)
    s2 = w.s([fin, D(w, A0, 'recnd', [k3r], '%s e. CC' % K3), D(w, AN_, 'recnd', [vtr], '%s e. CC' % VT)], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ n e. %s ( %s x. %s ) )' % (A0, K3, SV, IVT, K3, VT))
    BK = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % C0
    cbv = w.s([w.s([w.s([], 'fveq2', '( n = k -> ( Lam ` n ) = ( Lam ` k ) )'), w.s([], 'oveq1', '( n = k -> %s = ( k ^c -u %s ) )' % (NNC, C0))], 'oveq12d', '( n = k -> %s = %s )' % (VT, BK))],
              'cbvsumv', '%s = sum_ k e. %s %s' % (SV, IVT, BK))
    VMn = '( n e. NN |-> %s )' % VT
    AK = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % AK)
    krp = D(w, AK, 'nnrpd', [kn], 'k e. RR+')
    bkr = D(w, AK, 'remulcld', [w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % AK),
                                  D(w, AK, 'rpred', [D(w, AK, 'rpcxpcld', [krp, D(w, AK, 'renegcld', [lift(w, AK, w.s([], 'simpl', '( %s -> %s )' % (AK, A0)), d['c0r'], '%s e. RR' % C0)], '-u %s e. RR' % C0)],
                                                        '( k ^c -u %s ) e. RR+' % C0)], '( k ^c -u %s ) e. RR' % C0)], '%s e. RR' % BK)
    bk0 = D(w, AK, 'mulge0d', [w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % AK),
                               D(w, AK, 'rpred', [D(w, AK, 'rpcxpcld', [krp, D(w, AK, 'renegcld', [lift(w, AK, w.s([], 'simpl', '( %s -> %s )' % (AK, A0)), d['c0r'], '%s e. RR' % C0)], '-u %s e. RR' % C0)],
                                                   '( k ^c -u %s ) e. RR+' % C0)], '( k ^c -u %s ) e. RR' % C0),
                               w.s([kn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` k ) )' % AK),
                               D(w, AK, 'rpge0d', [D(w, AK, 'rpcxpcld', [krp, D(w, AK, 'renegcld', [lift(w, AK, w.s([], 'simpl', '( %s -> %s )' % (AK, A0)), d['c0r'], '%s e. RR' % C0)], '-u %s e. RR' % C0)],
                                                    '( k ^c -u %s ) e. RR+' % C0)], '0 <_ ( k ^c -u %s )' % C0)], '0 <_ %s' % BK)
    subk = w.s([w.s([], 'fveq2', '( n = k -> ( Lam ` n ) = ( Lam ` k ) )'), w.s([], 'oveq1', '( n = k -> %s = ( k ^c -u %s ) )' % (NNC, C0))], 'oveq12d', '( n = k -> %s = %s )' % (VT, BK))
    vmk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (VMn, VMn))], 'a1i', '( %s -> %s = %s )' % (AK, VMn, VMn)), w.s([subk], 'adantl', '( ( %s /\\ n = k ) -> %s = %s )' % (AK, VT, BK)), kn,
               bkr], 'fvmptd', '( %s -> ( %s ` k ) = %s )' % (AK, VMn, BK))
    vcv = w.s([D(w, A0, 'jca', [d['c0r'], d['c0gt']], '( %s e. RR /\\ 1 < %s )' % (C0, C0)), w.inst('vmsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, VMn))
    SNN = 'sum_ k e. NN %s' % BK
    il = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, A0, '1z', '1 e. ZZ'), fin, ssn, vmk, bkr, bk0, vcv], 'isumless', '( %s -> sum_ k e. %s %s <_ %s )' % (A0, IVT, BK, SNN))
    vb = w.s([D(w, A0, '3jca', [d['c0r'], d['c0gt'], d['c02']], '( %s e. RR /\\ 1 < %s /\\ %s <_ 2 )' % (C0, C0, C0)), w.inst('vmbnd')], 'syl', '( %s -> %s <_ ( 6 / ( ( %s - 1 ) ^ 2 ) ) )' % (A0, SNN, C0))
    IL = d['il']
    lyc = D(w, A0, 'rpcnd', [d['lyrp']], '%s e. CC' % LY); lyn = D(w, A0, 'rpne0d', [d['lyrp']], '%s =/= 0' % LY)
    ilc = D(w, A0, 'rpcnd', [d['ilrp']], '%s e. CC' % IL)
    c1c = a1(w, A0, 'ax-1cn', '1 e. CC')
    LY2 = '( %s ^ 2 )' % LY
    ly2c = D(w, A0, 'sqcld', [lyc], '%s e. CC' % LY2); ly2n = D(w, A0, 'rpne0d', [D(w, A0, 'rpexpcld', [d['lyrp'], a1(w, A0, '2z', '2 e. ZZ')], '%s e. RR+' % LY2)], '%s =/= 0' % LY2)
    six = chain(w, A0, ['( 6 / ( ( %s - 1 ) ^ 2 ) )' % C0, '( 6 / ( %s ^ 2 ) )' % IL, '( 6 / ( ( 1 ^ 2 ) / %s ) )' % LY2, '( 6 / ( 1 / %s ) )' % LY2, '( ( 6 x. %s ) / 1 )' % LY2, '( 6 x. %s )' % LY2],
                [w.s([w.s([D(w, A0, 'pncan2d', [c1c, ilc], '( %s - 1 ) = %s' % (C0, IL))], 'oveq1d', '( %s -> ( ( %s - 1 ) ^ 2 ) = ( %s ^ 2 ) )' % (A0, C0, IL))], 'oveq2d',
                     '( %s -> ( 6 / ( ( %s - 1 ) ^ 2 ) ) = ( 6 / ( %s ^ 2 ) ) )' % (A0, C0, IL)),
                 w.s([D(w, A0, 'sqdivd', [c1c, lyc, lyn], '( %s ^ 2 ) = ( ( 1 ^ 2 ) / %s )' % (IL, LY2))], 'oveq2d', '( %s -> ( 6 / ( %s ^ 2 ) ) = ( 6 / ( ( 1 ^ 2 ) / %s ) ) )' % (A0, IL, LY2)),
                 w.s([w.s([w.s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'oveq1i', '( ( 1 ^ 2 ) / %s ) = ( 1 / %s )' % (LY2, LY2))], 'oveq2i', '( 6 / ( ( 1 ^ 2 ) / %s ) ) = ( 6 / ( 1 / %s ) )' % (LY2, LY2))],
                     'a1i', '( %s -> ( 6 / ( ( 1 ^ 2 ) / %s ) ) = ( 6 / ( 1 / %s ) ) )' % (A0, LY2, LY2)),
                 D(w, A0, 'divdiv2d', [a1(w, A0, '6cn', '6 e. CC'), c1c, ly2c, a1(w, A0, 'ax-1ne0', '1 =/= 0'), ly2n], '( 6 / ( 1 / %s ) ) = ( ( 6 x. %s ) / 1 )' % (LY2, LY2)),
                 D(w, A0, 'div1d', [D(w, A0, 'mulcld', [a1(w, A0, '6cn', '6 e. CC'), ly2c], '( 6 x. %s ) e. CC' % LY2)], '( ( 6 x. %s ) / 1 ) = ( 6 x. %s )' % (LY2, LY2))])
    SA = 'sum_ k e. %s %s' % (IVT, BK)
    sar = w.s([fin, w.s([w.s([], 'simpl', '( ( %s /\\ k e. %s ) -> %s )' % (A0, IVT, A0)), w.s([lift(w, '( %s /\\ k e. %s )' % (A0, IVT), w.s([], 'simpl', '( ( %s /\\ k e. %s ) -> %s )' % (A0, IVT, A0)), ssn, '%s C_ NN' % IVT),
                                                                                          w.s([], 'simpr', '( ( %s /\\ k e. %s ) -> k e. %s )' % (A0, IVT, IVT))], 'sseldd', '( ( %s /\\ k e. %s ) -> k e. NN )' % (A0, IVT)),
                                w.s([bkr], 'ex', '( %s -> ( k e. NN -> %s e. RR ) )' % (A0, BK))], 'sylc', '( ( %s /\\ k e. %s ) -> %s e. RR )' % (A0, IVT, BK))], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SA))
    snr = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, A0, '1z', '1 e. ZZ'), vmk, bkr, vcv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SNN))
    svr = w.s([fin, vtr], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SV))
    sv1 = w.s([w.s([cbv], 'a1i', '( %s -> %s = %s )' % (A0, SV, SA)), il], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, SV, SNN))
    sv2 = w.s([vb, six], 'breqtrd', '( %s -> %s <_ ( 6 x. %s ) )' % (A0, SNN, LY2))
    cl.leaf(SV, 'RR', svr); cl.leaf(SNN, 'RR', snr)
    svle = D(w, A0, 'letrd', [svr, snr, cl.mem('( 6 x. %s )' % LY2, 'RR'), sv1, sv2], '%s <_ ( 6 x. %s )' % (SV, LY2))
    t120 = D(w, A0, 'divge0d', [cl.mem('; 1 2', 'RR'), d['trp'], linarith(w, A0, [], '0 <_ ; 1 2', closure=cl)], '0 <_ ( ; 1 2 / T )')
    k30 = D(w, A0, 'mulge0d', [t12A, D(w, A0, 'rpred', [d['ycrp']], '%s e. RR' % YCs), t120, D(w, A0, 'rpge0d', [d['ycrp']], '0 <_ %s' % YCs)], '0 <_ %s' % K3)
    s3 = D(w, A0, 'lemul2ad', [svr, cl.mem('( 6 x. %s )' % LY2, 'RR'), k3r, k30, svle], '( %s x. %s ) <_ ( %s x. ( 6 x. %s ) )' % (K3, SV, K3, LY2))
    tc = D(w, A0, 'rpcnd', [d['trp']], 'T e. CC'); tne = D(w, A0, 'rpne0d', [d['trp']], 'T =/= 0')
    YCT = '( %s / T )' % YCs
    k3e = D(w, A0, 'div32d', [D(w, A0, 'recnd', [cl.mem('; 1 2', 'RR')], '; 1 2 e. CC'), tc, D(w, A0, 'rpcnd', [d['ycrp']], '%s e. CC' % YCs), tne], '%s = ( ; 1 2 x. %s )' % (K3, YCT))
    yctr = D(w, A0, 'rerpdivcld', [D(w, A0, 'rpred', [d['ycrp']], '%s e. RR' % YCs), d['trp']], '%s e. RR' % YCT)
    yct0 = D(w, A0, 'divge0d', [D(w, A0, 'rpred', [d['ycrp']], '%s e. RR' % YCs), d['trp'], D(w, A0, 'rpge0d', [d['ycrp']], '0 <_ %s' % YCs)], '0 <_ %s' % YCT)
    y3t = D(w, A0, 'lediv1dd', [D(w, A0, 'rpred', [d['ycrp']], '%s e. RR' % YCs), cl.mem('( 3 x. Y )', 'RR'), d['trp'], d['yc3']], '%s <_ ( ( 3 x. Y ) / T )' % YCT)
    y3q = w.s([y3t, D(w, A0, 'divassd', [a1(w, A0, '3cn', '3 e. CC'), D(w, A0, 'rpcnd', [d['yrp']], 'Y e. CC'), tc, tne], '( ( 3 x. Y ) / T ) = ( 3 x. %s )' % Q)], 'breqtrd',
              '( %s -> %s <_ ( 3 x. %s ) )' % (A0, YCT, Q))
    lyl = linarith(w, A0, [d['lsum'], d['lt0']], '%s <_ %s' % (LY, LL), closure=cl)
    ly0 = D(w, A0, 'rpge0d', [d['lyrp']], '0 <_ %s' % LY)
    sq = D(w, A0, 'lemul12ad', [d['ly'], d['L'], d['ly'], d['L'], ly0, ly0, lyl, lyl], '( %s x. %s ) <_ ( %s x. %s )' % (LY, LY, LL, LL))
    pr = D(w, A0, 'lemul12ad', [yctr, cl.mem('( 3 x. %s )' % Q, 'RR'), cl.mem('( %s x. %s )' % (LY, LY), 'RR'), cl.mem('( %s x. %s )' % (LL, LL), 'RR'), yct0,
                                D(w, A0, 'mulge0d', [d['ly'], d['ly'], ly0, ly0], '0 <_ ( %s x. %s )' % (LY, LY)), y3q, sq],
           '( %s x. ( %s x. %s ) ) <_ ( ( 3 x. %s ) x. ( %s x. %s ) )' % (YCT, LY, LY, Q, LL, LL))
    cl.leaf(YCT, 'RR', yctr)
    ql0 = D(w, A0, 'mulge0d', [cl.mem(Q, 'RR'), D(w, A0, 'resqcld', [d['L']], '( %s ^ 2 ) e. RR' % LL), D(w, A0, 'rpge0d', [d['qrp']], '0 <_ %s' % Q), D(w, A0, 'sqge0d', [d['L']], '0 <_ ( %s ^ 2 )' % LL)],
            '0 <_ %s' % QL)
    K3Q = '( ; 1 2 x. %s )' % YCT
    num = linarith(w, A0, [pr, ql0], '( %s x. ( 6 x. %s ) ) <_ ( ; ; 2 1 6 x. %s )' % (K3Q, LY2, QL), closure=cl, products=True)
    num2 = w.s([w.s([k3e], 'oveq1d', '( %s -> ( %s x. ( 6 x. %s ) ) = ( %s x. ( 6 x. %s ) ) )' % (A0, K3, LY2, K3Q, LY2)), num], 'eqbrtrd',
               '( %s -> ( %s x. ( 6 x. %s ) ) <_ ( ; ; 2 1 6 x. %s ) )' % (A0, K3, LY2, QL))
    SE = 'sum_ n e. %s %s' % (IVT, ER('n'))
    ser = w.s([fin, enr], 'fsumrecl', '( %s -> %s e. RR )' % (A0, SE))
    c1 = w.s([s1, w.s([s2], 'eqcomd', '( %s -> sum_ n e. %s ( %s x. %s ) = ( %s x. %s ) )' % (A0, IVT, K3, VT, K3, SV))], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, SE, K3, SV))
    c2 = D(w, A0, 'letrd', [ser, cl.mem('( %s x. %s )' % (K3, SV), 'RR'), cl.mem('( %s x. ( 6 x. %s ) )' % (K3, LY2), 'RR'), c1, s3], '%s <_ ( %s x. ( 6 x. %s ) )' % (SE, K3, LY2))
    c3 = D(w, A0, 'letrd', [ser, cl.mem('( %s x. ( 6 x. %s ) )' % (K3, LY2), 'RR'), cl.mem('( ; ; 2 1 6 x. %s )' % QL, 'RR'), c2, num2], '%s <_ ( ; ; 2 1 6 x. %s )' % (SE, QL))
    w.qed([c3, w.s([w.s([d['qeq']], 'eqcomd', '( %s -> %s = %s )' % (A0, QL, YL))], 'oveq2d', '( %s -> ( ; ; 2 1 6 x. %s ) = ( ; ; 2 1 6 x. %s ) )' % (A0, QL, YL))], 'breqtrd', STATEMENTS['ef1tl'])
    go(w, only)
