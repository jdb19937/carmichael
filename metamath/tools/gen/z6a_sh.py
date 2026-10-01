"""Sortie Z6a, block C: the generic contour shift (z6hedge, z6shl, z6shift)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z6alib import *
from cl import Closure, lift, split_imp, formula_of
import lin
from lin import linarith, lineq, nlinarith
import num

only = sys.argv[1:]
L2 = '( log ` 2 )'
X1 = '( P + ( _i x. H ) )'
X2 = '( Q + ( _i x. H ) )'
HSs = ('( ( ( A e. RR /\\ B e. RR ) /\\ A <_ B ) /\\ ( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) ) )' % (STRIPD, STRIPM))
SDB = '( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ ( ( ( Re ` z ) = A \\/ ( Re ` z ) = B ) \\/ Y <_ ( abs ` ( Im ` z ) ) ) ) -> z e. D )'
SMB = '( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ Y <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( G ` z ) ) <_ ( M x. %s ) )' % E4('( abs ` ( Im ` z ) )')


def want(lab):
    return not only or lab in only


def ante_of(lab):
    return split_imp(STATEMENTS[lab])[0]


def stripparts(w, A, h):
    """conjuncts of a step h: ( A -> ( ( G cont /\\ STRIPD ) /\\ ( ( M RR /\\ Y RR+ ) /\\ STRIPM ) ) )"""
    st = mkst(w, A)
    d = {}
    l = st([h], 'simpld', '( G e. ( D -cn-> CC ) /\\ %s )' % STRIPD)
    r = st([h], 'simprd', '( ( M e. RR /\\ Y e. RR+ ) /\\ %s )' % STRIPM)
    d['gcn'] = st([l], 'simpld', 'G e. ( D -cn-> CC )'); d['sd'] = st([l], 'simprd', STRIPD)
    my = st([r], 'simpld', '( M e. RR /\\ Y e. RR+ )')
    d['mr'] = st([my], 'simpld', 'M e. RR'); d['yrp'] = st([my], 'simprd', 'Y e. RR+'); d['sm'] = st([r], 'simprd', STRIPM)
    return d


def strip_at(w, A, d, key, body, U, uc):
    """instance of STRIPD / STRIPM at z := U: ( A -> body[U/z] )"""
    idk = w.s([], 'id', '( z = %s -> z = %s )' % (U, U))
    sb, new = w.wcongr(body, {'z': U}, 'z = %s' % U, {'z': idk})
    full = STRIPD if key == 'sd' else STRIPM
    rs = w.s([sb], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (U, full, new))
    return w.s([uc, lift(w, d[key], A), rs], 'sylc', '( %s -> %s )' % (A, new)), new


# ---------------------------------------------------------------- z6hedge
def z6hedge():
    w = W('z6hedge', 'A horizontal segment at height ` H ` , ` | H | >_ Y ` , between two points of ` [ A , B ] ` lies in ` D ` '
          'and carries the ML bound ` M | Q - P | 2 ^ ( - | H | / 4 ) ` ( ~ lintabs ; its points lie in the rectangle '
          '~ crectcvx , their imaginary part is ` H ` , ~ cseghim ).')
    A = ante_of('z6hedge')
    st = mkst(w, A)
    hs = st([], 'simpl', HSs)
    ab = st([hs], 'simpld', '( ( A e. RR /\\ B e. RR ) /\\ A <_ B )')
    ar = st([st([ab], 'simpld', '( A e. RR /\\ B e. RR )')], 'simpld', 'A e. RR'); br = st([st([ab], 'simpld', '( A e. RR /\\ B e. RR )')], 'simprd', 'B e. RR')
    d = stripparts(w, A, st([hs], 'simprd', '( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) )' % (STRIPD, STRIPM)))
    hh = st([], 'simpr', '( ( H e. RR /\\ Y <_ ( abs ` H ) ) /\\ ( P e. ( A [,] B ) /\\ Q e. ( A [,] B ) ) )')
    hr = st([st([hh], 'simpld', '( H e. RR /\\ Y <_ ( abs ` H ) )')], 'simpld', 'H e. RR'); yh = st([st([hh], 'simpld', '( H e. RR /\\ Y <_ ( abs ` H ) )')], 'simprd', 'Y <_ ( abs ` H )')
    pab = st([st([hh], 'simprd', '( P e. ( A [,] B ) /\\ Q e. ( A [,] B ) )')], 'simpld', 'P e. ( A [,] B )')
    qab = st([st([hh], 'simprd', '( P e. ( A [,] B ) /\\ Q e. ( A [,] B ) )')], 'simprd', 'Q e. ( A [,] B )')
    ib = st([ar, br, w.inst('elicc2')], 'syl2anc', '( P e. ( A [,] B ) <-> ( P e. RR /\\ A <_ P /\\ P <_ B ) )')
    pr = st([st([pab, ib], 'mpbid', '( P e. RR /\\ A <_ P /\\ P <_ B )')], 'simp1d', 'P e. RR')
    ibq = st([ar, br, w.inst('elicc2')], 'syl2anc', '( Q e. ( A [,] B ) <-> ( Q e. RR /\\ A <_ Q /\\ Q <_ B ) )')
    qr = st([st([qab, ibq], 'mpbid', '( Q e. RR /\\ A <_ Q /\\ Q <_ B )')], 'simp1d', 'Q e. RR')
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    ihc = st([ic, st([hr], 'recnd', 'H e. CC')], 'mulcld', '( _i x. H ) e. CC')
    cpt = lambda X, xr: st([st([xr], 'recnd', '%s e. CC' % X), ihc], 'addcld', '( %s + ( _i x. H ) ) e. CC' % X)
    x1c = cpt('P', pr); x2c = cpt('Q', qr)
    CA = '( A + ( _i x. H ) )'; CB = '( B + ( _i x. H ) )'
    cac = cpt('A', ar); cbc = cpt('B', br)
    CR = '( %s crect %s )' % (CA, CB)
    riv = st([st([ar, hr], 'crred', '( Re ` %s ) = A' % CA), st([br, hr], 'crred', '( Re ` %s ) = B' % CB)], 'oveq12d', '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( A [,] B )' % (CA, CB))
    iiv = st([st([ar, hr], 'crimd', '( Im ` %s ) = H' % CA), st([br, hr], 'crimd', '( Im ` %s ) = H' % CB)], 'oveq12d', '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( H [,] H )' % (CA, CB))
    hxr = st([hr], 'rexrd', 'H e. RR*')
    hhh = st([hxr, hxr, st([hr], 'leidd', 'H <_ H'), w.inst('lbicc2')], 'syl3anc', 'H e. ( H [,] H )')

    def incr(X, xr, xab, xc):
        re = st([st([st([xr, hr], 'crred', '( Re ` ( %s + ( _i x. H ) ) ) = %s' % (X, X)), xab], 'eqeltrd', '( Re ` ( %s + ( _i x. H ) ) ) e. ( A [,] B )' % X), riv], 'eleqtrrd',
                '( Re ` ( %s + ( _i x. H ) ) ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (X, CA, CB))
        im = st([st([st([xr, hr], 'crimd', '( Im ` ( %s + ( _i x. H ) ) ) = H' % X), hhh], 'eqeltrd', '( Im ` ( %s + ( _i x. H ) ) ) e. ( H [,] H )' % X), iiv], 'eleqtrrd',
                '( Im ` ( %s + ( _i x. H ) ) ) e. ( ( Im ` %s ) [,] ( Im ` %s ) )' % (X, CA, CB))
        ec = st([cac, cbc, w.inst('elcrect')], 'syl2anc', '( ( %s + ( _i x. H ) ) e. %s <-> ( ( %s + ( _i x. H ) ) e. CC /\\ ( Re ` ( %s + ( _i x. H ) ) ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ '
                                                          '( Im ` ( %s + ( _i x. H ) ) ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (X, CR, X, X, CA, CB, X, CA, CB))
        return st([xc, re, im, ec], 'mpbir3and', '( %s + ( _i x. H ) ) e. %s' % (X, CR))
    x1r_ = incr('P', pr, pab, x1c); x2r_ = incr('Q', qr, qab, x2c)
    SG = '( %s cseg %s )' % (X1, X2)
    sgcr = st([st([cac, cbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (CA, CB)), st([x1r_, x2r_], 'jca', '( %s e. %s /\\ %s e. %s )' % (X1, CR, X2, CR)), w.inst('crectcvx')], 'syl2anc',
              '%s C_ %s' % (SG, CR))
    imeq = st([st([pr, hr], 'crimd', '( Im ` %s ) = H' % X1), st([qr, hr], 'crimd', '( Im ` %s ) = H' % X2)], 'eqtr4d', '( Im ` %s ) = ( Im ` %s )' % (X1, X2))
    alim = st([x1c, x2c, imeq, w.inst('cseghim')], 'syl3anc', 'A. u e. %s ( Im ` u ) = ( Im ` %s )' % (SG, X1))
    Au = '( %s /\\ u e. %s )' % (A, SG)
    su = mkst(w, Au)
    uin = su([], 'simpr', 'u e. %s' % SG)
    ucr = su([lift(w, sgcr, Au), uin], 'sseldd', 'u e. %s' % CR)
    ecu = su([lift(w, cac, Au), lift(w, cbc, Au), w.inst('elcrect')], 'syl2anc', '( u e. %s <-> ( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )'
                % (CR, CA, CB, CA, CB))
    u3 = su([ucr, ecu], 'mpbid', '( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (CA, CB, CA, CB))
    uc = su([u3], 'simp1d', 'u e. CC')
    rab = su([su([u3], 'simp2d', '( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (CA, CB)), lift(w, riv, Au)], 'eleqtrd', '( Re ` u ) e. ( A [,] B )')
    rb = su([rab, su([lift(w, ar, Au), lift(w, br, Au), w.inst('elicc2')], 'syl2anc', '( ( Re ` u ) e. ( A [,] B ) <-> ( ( Re ` u ) e. RR /\\ A <_ ( Re ` u ) /\\ ( Re ` u ) <_ B ) )')],
            'mpbid', '( ( Re ` u ) e. RR /\\ A <_ ( Re ` u ) /\\ ( Re ` u ) <_ B )')
    rlo = su([rb], 'simp2d', 'A <_ ( Re ` u )'); rhi = su([rb], 'simp3d', '( Re ` u ) <_ B')
    imu = su([w.s([alim], 'r19.21bi', '( %s -> ( Im ` u ) = ( Im ` %s ) )' % (Au, X1)), lift(w, st([pr, hr], 'crimd', '( Im ` %s ) = H' % X1), Au)], 'eqtrd', '( Im ` u ) = H')
    aim = su([imu], 'fveq2d', '( abs ` ( Im ` u ) ) = ( abs ` H )')
    yim = su([lift(w, yh, Au), aim], 'breqtrrd', 'Y <_ ( abs ` ( Im ` u ) )')
    rr2 = su([rlo, rhi], 'jca', '( A <_ ( Re ` u ) /\\ ( Re ` u ) <_ B )')
    sdu, sdf = strip_at(w, Au, d, 'sd', SDB, 'u', uc)
    ud = su([su([rr2, su([yim], 'olcd', '( ( ( Re ` u ) = A \\/ ( Re ` u ) = B ) \\/ Y <_ ( abs ` ( Im ` u ) ) )')], 'jca',
                '( ( A <_ ( Re ` u ) /\\ ( Re ` u ) <_ B ) /\\ ( ( ( Re ` u ) = A \\/ ( Re ` u ) = B ) \\/ Y <_ ( abs ` ( Im ` u ) ) ) )'), sdu], 'mpd', 'u e. D')
    smu, smf = strip_at(w, Au, d, 'sm', SMB, 'u', uc)
    gb = su([su([rr2, yim], 'jca', '( ( A <_ ( Re ` u ) /\\ ( Re ` u ) <_ B ) /\\ Y <_ ( abs ` ( Im ` u ) ) )'), smu], 'mpd', '( abs ` ( G ` u ) ) <_ ( M x. %s )' % E4('( abs ` ( Im ` u ) )'))
    EH = E4('( abs ` H )')
    e4e = su([su([su([su([aim], 'oveq1d', '( ( abs ` ( Im ` u ) ) / 4 ) = ( ( abs ` H ) / 4 )')], 'negeqd', '-u ( ( abs ` ( Im ` u ) ) / 4 ) = -u ( ( abs ` H ) / 4 )')], 'oveq2d',
                  '%s = %s' % (E4('( abs ` ( Im ` u ) )'), EH))], 'oveq2d', '( M x. %s ) = ( M x. %s )' % (E4('( abs ` ( Im ` u ) )'), EH))
    gb2 = su([gb, e4e], 'breqtrd', '( abs ` ( G ` u ) ) <_ ( M x. %s )' % EH)
    sgd = st([w.s([ud], 'ex', '( %s -> ( u e. %s -> u e. D ) )' % (A, SG))], 'ssrdv', '%s C_ D' % SG)
    algb = st([gb2], 'ralrimiva', 'A. u e. %s ( abs ` ( G ` u ) ) <_ ( M x. %s )' % (SG, EH))
    cl = Closure(w, A, {'M': ('RR', d['mr']), 'H': ('RR', hr)})
    meh = cl.mem('( M x. %s )' % EH, 'RR')
    la = st([st([st([x1c, x2c], 'jca', '( %s e. CC /\\ %s e. CC )' % (X1, X2)), st([d['gcn'], sgd], 'jca', '( G e. ( D -cn-> CC ) /\\ %s C_ D )' % SG)], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (X1, X2, SG)), meh, algb, w.inst('lintabs')], 'syl3anc',
            '( abs ` ( G lint <. %s , %s >. ) ) <_ ( ( M x. %s ) x. ( abs ` ( %s - %s ) ) )' % (X1, X2, EH, X2, X1))
    dq = st([st([qr], 'recnd', 'Q e. CC'), st([pr], 'recnd', 'P e. CC'), ihc], 'pnpcan2d', '( %s - %s ) = ( Q - P )' % (X2, X1))
    la2 = st([la, st([st([dq], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( Q - P ) )' % (X2, X1))], 'oveq2d',
                     '( ( M x. %s ) x. ( abs ` ( %s - %s ) ) ) = ( ( M x. %s ) x. ( abs ` ( Q - P ) ) )' % (EH, X2, X1, EH))], 'breqtrd',
             '( abs ` ( G lint <. %s , %s >. ) ) <_ ( ( M x. %s ) x. ( abs ` ( Q - P ) ) )' % (X1, X2, EH))
    aqp = st([st([st([qr, pr], 'resubcld', '( Q - P ) e. RR')], 'recnd', '( Q - P ) e. CC')], 'abscld', '( abs ` ( Q - P ) ) e. RR')
    m3 = st([st([d['mr']], 'recnd', 'M e. CC'), st([cl.mem(EH, 'RR')], 'recnd', '%s e. CC' % EH), st([aqp], 'recnd', '( abs ` ( Q - P ) ) e. CC')], 'mul32d',
            '( ( M x. %s ) x. ( abs ` ( Q - P ) ) ) = ( ( M x. ( abs ` ( Q - P ) ) ) x. %s )' % (EH, EH))
    la3 = st([la2, m3], 'breqtrd', '( abs ` ( G lint <. %s , %s >. ) ) <_ ( ( M x. ( abs ` ( Q - P ) ) ) x. %s )' % (X1, X2, EH))
    w.qed([sgd, la3], 'jca', STATEMENTS['z6hedge'])
    return w


# ---------------------------------------------------------------- z6shl
def VLs(c):
    return '( ~~>r ` ( s e. RR+ |-> %s ) )' % LI('G', c, 's')


def z6shl():
    w = W('z6shl', 'The generic contour shift, with the rectangle heights bound by ` r ` and the line integrals by ` s ` : '
          '~ rectintshlr on ` S = [ Y , +oo ) ` , the vertical limits from ~ z6vlcvg , the horizontal edges ` -> 0 ` by '
          '~ z6hedge , ~ z6e4lim and ~ rlimsqzlem .')
    A = ante_of('z6shl')
    st = mkst(w, A)
    p1 = st([], 'simp1', '( ( A e. RR /\\ B e. RR ) /\\ A < B )')
    P2 = '( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) )' % (STRIPD, STRIPM)
    p2 = st([], 'simp2', P2)
    RI = lambda r: '( G rectint <. ( A + ( _i x. -u %s ) ) , ( B + ( _i x. %s ) ) >. )' % (r, r)
    RALL = 'A. r e. RR+ ( Y <_ r -> %s = K )' % RI('r')
    p3 = st([], 'simp3', '( K e. CC /\\ %s )' % RALL)
    ar = st([st([p1], 'simpld', '( A e. RR /\\ B e. RR )')], 'simpld', 'A e. RR'); br = st([st([p1], 'simpld', '( A e. RR /\\ B e. RR )')], 'simprd', 'B e. RR')
    alt = st([p1], 'simprd', 'A < B'); ale = st([ar, br, alt], 'ltled', 'A <_ B')
    d = stripparts(w, A, p2)
    kc = st([p3], 'simpld', 'K e. CC'); rall = st([p3], 'simprd', RALL)
    yr = st([d['yrp']], 'rpred', 'Y e. RR')
    S = '( Y [,) +oo )'
    sre = st([yr, a1c(w, A, 'pnfxr', '+oo e. RR*'), w.inst('icossre')], 'syl2anc', '%s C_ RR' % S)
    sup = st([st([yr], 'rexrd', 'Y e. RR*'), st([yr], 'renepnfd', 'Y =/= +oo'), w.inst('icopnfsup')], 'syl2anc', 'sup ( %s , RR* , < ) = +oo' % S)
    At = '( %s /\\ t e. %s )' % (A, S)
    sa = mkst(w, At)
    tb = sa([sa([], 'simpr', 't e. %s' % S), sa([lift(w, yr, At), w.inst('elicopnf')], 'syl', '( t e. %s <-> ( t e. RR /\\ Y <_ t ) )' % S)], 'mpbid', '( t e. RR /\\ Y <_ t )')
    tr = sa([tb], 'simpld', 't e. RR'); yt = sa([tb], 'simprd', 'Y <_ t')
    clt = Closure(w, At, {'t': ('RR', tr), 'Y': ('RR+', lift(w, d['yrp'], At))})
    trp = sa([tr, linarith(w, At, [yt, clt.gt0('Y')], '0 < t', closure=clt)], 'elrpd', 't e. RR+')
    srp = st([w.s([trp], 'ex', '( %s -> ( t e. %s -> t e. RR+ ) )' % (A, S))], 'ssrdv', '%s C_ RR+' % S)
    HSt = '( ( ( A e. RR /\\ B e. RR ) /\\ A <_ B ) /\\ %s )' % P2
    hs = st([st([st([ar, br], 'jca', '( A e. RR /\\ B e. RR )'), ale], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ A <_ B )'), p2], 'jca', HSt)
    axr = st([ar], 'rexrd', 'A e. RR*'); bxr = st([br], 'rexrd', 'B e. RR*')
    aab = st([axr, bxr, ale, w.inst('lbicc2')], 'syl3anc', 'A e. ( A [,] B )')
    bab = st([axr, bxr, ale, w.inst('ubicc2')], 'syl3anc', 'B e. ( A [,] B )')

    def vline(c, left):
        """( ph -> ( t e. S |-> LI ( c , t ) ) ~~>r VLs ( c ) ) and ( ph -> A. u e. RR ( c + ( _i x. u ) ) e. D )"""
        cr = ar if left else br
        Au = '( %s /\\ u e. RR )' % A
        su = mkst(w, Au)
        ur = su([], 'simpr', 'u e. RR')
        Z = '( %s + ( _i x. u ) )' % c
        zc = su([su([lift(w, cr, Au)], 'recnd', '%s e. CC' % c), su([a1c(w, Au, 'ax-icn', '_i e. CC'), su([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % Z)
        rz = su([lift(w, cr, Au), ur], 'crred', '( Re ` %s ) = %s' % (Z, c))
        izz = su([lift(w, cr, Au), ur], 'crimd', '( Im ` %s ) = u' % Z)
        if left:
            lo = su([rz, su([lift(w, ar, Au)], 'leidd', 'A <_ A')], 'breqtrrd' if False else 'eqbrtrrd', 'A <_ ( Re ` %s )' % Z) if False else \
                su([su([lift(w, ar, Au)], 'leidd', 'A <_ A'), rz], 'breqtrrd', 'A <_ ( Re ` %s )' % Z)
            hi = su([rz, lift(w, ale, Au)], 'eqbrtrd', '( Re ` %s ) <_ B' % Z)
            dj = su([su([rz], 'orcd', '( ( Re ` %s ) = A \\/ ( Re ` %s ) = B )' % (Z, Z))], 'orcd',
                    '( ( ( Re ` %s ) = A \\/ ( Re ` %s ) = B ) \\/ Y <_ ( abs ` ( Im ` %s ) ) )' % (Z, Z, Z))
        else:
            lo = su([lift(w, ale, Au), rz], 'breqtrrd', 'A <_ ( Re ` %s )' % Z)
            hi = su([rz, su([lift(w, br, Au)], 'leidd', 'B <_ B')], 'eqbrtrd', '( Re ` %s ) <_ B' % Z)
            dj = su([su([rz], 'olcd', '( ( Re ` %s ) = A \\/ ( Re ` %s ) = B )' % (Z, Z))], 'orcd',
                    '( ( ( Re ` %s ) = A \\/ ( Re ` %s ) = B ) \\/ Y <_ ( abs ` ( Im ` %s ) ) )' % (Z, Z, Z))
        lohi = su([lo, hi], 'jca', '( A <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ B )' % (Z, Z))
        sdz, _ = strip_at(w, Au, d, 'sd', SDB, Z, zc)
        zd = su([su([lohi, dj], 'jca', '( ( A <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ B ) /\\ ( ( ( Re ` %s ) = A \\/ ( Re ` %s ) = B ) \\/ Y <_ ( abs ` ( Im ` %s ) ) ) )' % (Z, Z, Z, Z, Z)), sdz],
                'mpd', '%s e. D' % Z)
        ald = st([zd], 'ralrimiva', 'A. u e. RR %s e. D' % Z)
        Ay = '( %s /\\ Y <_ ( abs ` u ) )' % Au
        sy_ = mkst(w, Ay)
        aiz = sy_([lift(w, izz, Ay)], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % Z)
        yiz = sy_([sy_([], 'simpr', 'Y <_ ( abs ` u )'), aiz], 'breqtrrd', 'Y <_ ( abs ` ( Im ` %s ) )' % Z)
        smz, _ = strip_at(w, Ay, d, 'sm', SMB, Z, lift(w, zc, Ay))
        gb = sy_([sy_([lift(w, lohi, Ay), yiz], 'jca', '( ( A <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ B ) /\\ Y <_ ( abs ` ( Im ` %s ) ) )' % (Z, Z, Z)), smz], 'mpd',
                 '( abs ` ( G ` %s ) ) <_ ( M x. %s )' % (Z, E4('( abs ` ( Im ` %s ) )' % Z)))
        ee = sy_([sy_([sy_([sy_([aiz], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % Z)], 'negeqd', '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % Z)], 'oveq2d',
                      '%s = %s' % (E4('( abs ` ( Im ` %s ) )' % Z), E4('( abs ` u )')))], 'oveq2d', '( M x. %s ) = ( M x. %s )' % (E4('( abs ` ( Im ` %s ) )' % Z), E4('( abs ` u )')))
        gb2 = sy_([gb, ee], 'breqtrd', '( abs ` ( G ` %s ) ) <_ ( M x. %s )' % (Z, E4('( abs ` u )')))
        BU = '( Y <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. %s ) )' % (Z, E4('( abs ` u )'))
        alb = st([w.s([gb2], 'ex', '( %s -> %s )' % (Au, BU))], 'ralrimiva', 'A. u e. RR %s' % BU)
        hv = st([st([cr, st([d['gcn'], ald], 'jca', '( G e. ( D -cn-> CC ) /\\ A. u e. RR %s e. D )' % Z)], 'jca', '( %s e. RR /\\ ( G e. ( D -cn-> CC ) /\\ A. u e. RR %s e. D ) )' % (c, Z)),
                 st([st([d['mr'], d['yrp']], 'jca', '( M e. RR /\\ Y e. RR+ )'), alb], 'jca', '( ( M e. RR /\\ Y e. RR+ ) /\\ A. u e. RR %s )' % BU)], 'jca',
                '( ( %s e. RR /\\ ( G e. ( D -cn-> CC ) /\\ A. u e. RR %s e. D ) ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ A. u e. RR %s ) )' % (c, Z, BU))
        VF = VLF('G', c); VLc = VL('G', c)
        cv = st([hv, w.inst('z6vlcvg')], 'syl', '( %s ~~>r %s /\\ A. t e. RR+ ( Y <_ t -> ( abs ` ( %s - %s ) ) <_ ( ( ( 8 x. M ) / ( log ` 2 ) ) x. %s ) ) )'
                % (VF, VLc, VLc, LI('G', c), E4('t')))
        lim = st([cv], 'simpld', '%s ~~>r %s' % (VF, VLc))
        rres = st([lim, w.inst('rlimres')], 'syl', '( %s |` %s ) ~~>r %s' % (VF, S, VLc))
        rm = st([srp, w.inst('resmpt')], 'syl', '( %s |` %s ) = ( t e. %s |-> %s )' % (VF, S, S, LI('G', c)))
        l2 = st([rm, rres], 'eqbrtrrd', '( t e. %s |-> %s ) ~~>r %s' % (S, LI('G', c), VLc))
        idk = w.s([], 'id', '( t = s -> t = s )')
        sb, _ = w.congr(LI('G', c, 't'), {'t': 's'}, 't = s', {'t': idk})
        cbv = w.s([w.s([sb], 'cbvmptv', '%s = ( s e. RR+ |-> %s )' % (VF, LI('G', c, 's')))], 'fveq2i', '%s = %s' % (VLc, VLs(c)))
        return st([l2, a1(w, A, cbv, '%s = %s' % (VLc, VLs(c)))], 'breqtrd', '( t e. %s |-> %s ) ~~>r %s' % (S, LI('G', c), VLs(c))), ald
    limB, _ = vline('B', False)
    limA, aldA = vline('A', True)
    # the left segment in D
    sege = sa([sa([sa([lift(w, ar, At), trp], 'jca', '( A e. RR /\\ t e. RR+ )'), lift(w, aldA, At)], 'jca', '( ( A e. RR /\\ t e. RR+ ) /\\ A. u e. RR ( A + ( _i x. u ) ) e. D )'),
               w.inst('z6segd')], 'syl', '( ( A + ( _i x. -u t ) ) cseg ( A + ( _i x. t ) ) ) C_ D')
    # the rectangle identities
    idk = w.s([], 'id', '( r = t -> r = t )')
    sb, new = w.wcongr('( Y <_ r -> %s = K )' % RI('r'), {'r': 't'}, 'r = t', {'r': idk})
    rs = w.s([sb], 'rspcv', '( t e. RR+ -> ( %s -> %s ) )' % (RALL, new))
    rt = sa([yt, sa([trp, lift(w, rall, At), rs], 'sylc', new)], 'mpd', '%s = K' % RI('t'))
    # the horizontal edges
    E4T = E4('t')
    e4r = st([st([a1c(w, A, 'rpssre', 'RR+ C_ RR') and srp, w.inst('resmpt')], 'syl', '( ( t e. RR+ |-> %s ) |` %s ) = ( t e. %s |-> %s )' % (E4T, S, S, E4T)),
              st([a1(w, A, w.s([], 'z6e4lim', STATEMENTS['z6e4lim']), STATEMENTS['z6e4lim']), w.inst('rlimres')], 'syl', '( ( t e. RR+ |-> %s ) |` %s ) ~~>r 0' % (E4T, S))], 'eqbrtrrd',
             '( t e. %s |-> %s ) ~~>r 0' % (S, E4T))

    def hedge(H, P, Q, pab, qab, hr, yh, absH):
        """( ph -> ( t e. S |-> ( G lint <. ( P + i H ) , ( Q + i H ) >. ) ) ~~>r 0 )"""
        X1_ = '( %s + ( _i x. %s ) )' % (P, H); X2_ = '( %s + ( _i x. %s ) )' % (Q, H)
        ED = '( G lint <. %s , %s >. )' % (X1_, X2_)
        MC = '( M x. ( abs ` ( %s - %s ) ) )' % (Q, P)
        hz = sa([sa([lift(w, hs, At), sa([sa([hr, yh], 'jca', '( %s e. RR /\\ Y <_ ( abs ` %s ) )' % (H, H)), sa([lift(w, pab, At), lift(w, qab, At)], 'jca',
                                                                                                        '( %s e. ( A [,] B ) /\\ %s e. ( A [,] B ) )' % (P, Q))], 'jca',
                                                    '( ( %s e. RR /\\ Y <_ ( abs ` %s ) ) /\\ ( %s e. ( A [,] B ) /\\ %s e. ( A [,] B ) ) )' % (H, H, P, Q))], 'jca',
                    '( %s /\\ ( ( %s e. RR /\\ Y <_ ( abs ` %s ) ) /\\ ( %s e. ( A [,] B ) /\\ %s e. ( A [,] B ) ) ) )' % (HSt, H, H, P, Q)), w.inst('z6hedge')], 'syl',
                '( ( %s cseg %s ) C_ D /\\ ( abs ` %s ) <_ ( %s x. %s ) )' % (X1_, X2_, ED, MC, E4('( abs ` %s )' % H)))
        sg = sa([hz], 'simpld', '( %s cseg %s ) C_ D' % (X1_, X2_))
        bd = sa([hz], 'simprd', '( abs ` %s ) <_ ( %s x. %s )' % (ED, MC, E4('( abs ` %s )' % H)))
        ee = sa([sa([sa([sa([absH], 'oveq1d', '( ( abs ` %s ) / 4 ) = ( t / 4 )' % H)], 'negeqd', '-u ( ( abs ` %s ) / 4 ) = -u ( t / 4 )' % H)], 'oveq2d', '%s = %s' % (E4('( abs ` %s )' % H), E4T))],
                'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (MC, E4('( abs ` %s )' % H), MC, E4T))
        BD = '( %s x. %s )' % (MC, E4T)
        bd2 = sa([bd, ee], 'breqtrd', '( abs ` %s ) <_ %s' % (ED, BD))
        pr_ = lift(w, ar if P == 'A' else br, At); qr_ = lift(w, ar if Q == 'A' else br, At)
        ic = a1c(w, At, 'ax-icn', '_i e. CC')
        hc = sa([hr], 'recnd', '%s e. CC' % H)
        x1c = sa([sa([pr_], 'recnd', '%s e. CC' % P), sa([ic, hc], 'mulcld', '( _i x. %s ) e. CC' % H)], 'addcld', '%s e. CC' % X1_)
        x2c = sa([sa([qr_], 'recnd', '%s e. CC' % Q), sa([ic, hc], 'mulcld', '( _i x. %s ) e. CC' % H)], 'addcld', '%s e. CC' % X2_)
        edc = sa([sa([x1c, x2c], 'jca', '( %s e. CC /\\ %s e. CC )' % (X1_, X2_)), sa([lift(w, d['gcn'], At), sg], 'jca', '( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (X1_, X2_)),
                  w.inst('lintcl')], 'syl2anc', '%s e. CC' % ED)
        clm = Closure(w, A, {'M': ('RR', d['mr']), 'A': ('RR', ar), 'B': ('RR', br)})
        mcr = clm.mem(MC, 'RR')
        mcc = st([mcr], 'recnd', '%s e. CC' % MC)
        Att = '( %s /\\ t e. %s )' % (A, S)
        lc = st([sre, mcc, w.inst('rlimconst')], 'syl2anc', '( t e. %s |-> %s ) ~~>r %s' % (S, MC, MC))
        bl0 = st([w.s([lift(w, mcc, Att)], 'elexd', '( %s -> %s e. _V )' % (Att, MC)), w.s([], 'ovexd', '( %s -> %s e. _V )' % (Att, E4T)), lc, e4r], 'rlimmul',
                 '( t e. %s |-> %s ) ~~>r ( %s x. 0 )' % (S, BD, MC))
        bl = st([bl0, st([mcc], 'mul01d', '( %s x. 0 ) = 0' % MC)], 'breqtrd', '( t e. %s |-> %s ) ~~>r 0' % (S, BD))
        bdr = sa([lift(w, mcr, At), sa([a1c(w, At, '2rp', '2 e. RR+'), clt.mem('-u ( t / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % E4T) and
                  sa([sa([a1c(w, At, '2rp', '2 e. RR+'), clt.mem('-u ( t / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % E4T)], 'rpred', '%s e. RR' % E4T)], 'remulcld', '%s e. RR' % BD)
        bge = sa([sa([edc], 'absge0d', '0 <_ ( abs ` %s )' % ED), bd2, sa([], '0red', '0 e. RR') and sa([edc], 'abscld', '( abs ` %s ) e. RR' % ED)], 'jca' if False else 'jca',
                 '( 0 <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ %s )' % (ED, ED, BD)) if False else \
            sa([sa([], '0red', '0 e. RR'), sa([edc], 'abscld', '( abs ` %s ) e. RR' % ED), bdr, sa([edc], 'absge0d', '0 <_ ( abs ` %s )' % ED), bd2], 'letrd', '0 <_ %s' % BD)
        e0 = sa([sa([edc], 'subid1d', '( %s - 0 ) = %s' % (ED, ED))], 'fveq2d', '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (ED, ED))
        b0 = sa([sa([sa([bdr], 'recnd', '%s e. CC' % BD)], 'subid1d', '( %s - 0 ) = %s' % (BD, BD))], 'fveq2d', '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (BD, BD))
        bab_ = sa([bdr, bge], 'absidd', '( abs ` %s ) = %s' % (BD, BD))
        c4 = sa([sa([e0, bd2], 'eqbrtrd', '( abs ` ( %s - 0 ) ) <_ %s' % (ED, BD)), sa([b0, bab_], 'eqtrd', '( abs ` ( %s - 0 ) ) = %s' % (BD, BD))], 'breqtrrd',
                '( abs ` ( %s - 0 ) ) <_ ( abs ` ( %s - 0 ) )' % (ED, BD))
        c4b = w.s([c4], 'adantrr', '( ( %s /\\ ( t e. %s /\\ Y <_ t ) ) -> ( abs ` ( %s - 0 ) ) <_ ( abs ` ( %s - 0 ) ) )' % (A, S, ED, BD))
        return st([yr, a1c(w, A, '0cn', '0 e. CC'), bl, sa([bdr], 'recnd', '%s e. CC' % BD), edc, c4b], 'rlimsqzlem', '( t e. %s |-> %s ) ~~>r 0' % (S, ED))
    ntr = sa([tr], 'renegcld', '-u t e. RR')
    ant = sa([sa([sa([tr], 'recnd', 't e. CC')], 'absnegd', '( abs ` -u t ) = ( abs ` t )'), sa([tr, sa([sa([], '0red', '0 e. RR'), tr, sa([trp], 'rpgt0d', '0 < t')], 'ltled', '0 <_ t')], 'absidd', '( abs ` t ) = t')],
             'eqtrd', '( abs ` -u t ) = t')
    at = sa([tr, sa([sa([], '0red', '0 e. RR'), tr, sa([trp], 'rpgt0d', '0 < t')], 'ltled', '0 <_ t')], 'absidd', '( abs ` t ) = t')
    bot = hedge('-u t', 'A', 'B', aab, bab, ntr, sa([yt, ant], 'breqtrrd', 'Y <_ ( abs ` -u t )'), ant)
    top = hedge('t', 'B', 'A', bab, aab, tr, sa([yt, at], 'breqtrrd', 'Y <_ ( abs ` t )'), at)
    w.qed([ar, br, d['gcn'], kc, sre, sup, sege, rt, bot, limB, top, limA], 'rectintshlr', STATEMENTS['z6shl'])
    return w


# ---------------------------------------------------------------- z6shift
def z6shift():
    w = W('z6shift', 'The generic contour shift: a function continuous on a domain containing the two vertical lines '
          '` Re = A ` , ` Re = B ` and the horizontal segments at heights ` >_ Y ` , bounded there by ` M 2 ^ ( - | Im z | / 4 ) ` , '
          'whose rectangle integrals over ` [ A , B ] x [ -u t , t ] ` equal ` K ` for ` t >_ Y ` , has ` VL ( B ) - VL ( A ) = K ` '
          '(DetectionShift.lean ` shift_lines_residue ` ; ~ z6shl with the bound variables renamed).')
    A = ante_of('z6shift')
    st = mkst(w, A)
    RI = lambda r: '( G rectint <. ( A + ( _i x. -u %s ) ) , ( B + ( _i x. %s ) ) >. )' % (r, r)
    idk = w.s([], 'id', '( t = r -> t = r )')
    sb, new = w.wcongr('( Y <_ t -> %s = K )' % RI('t'), {'t': 'r'}, 't = r', {'t': idk})
    cb = w.s([sb], 'cbvralvw', '( A. t e. RR+ ( Y <_ t -> %s = K ) <-> A. r e. RR+ %s )' % (RI('t'), new))
    P1 = '( ( A e. RR /\\ B e. RR ) /\\ A < B )'
    P2 = '( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) )' % (STRIPD, STRIPM)
    p3 = st([], 'simp3', '( K e. CC /\\ A. t e. RR+ ( Y <_ t -> %s = K ) )' % RI('t'))
    p3r = st([st([p3], 'simpld', 'K e. CC'), st([st([p3], 'simprd', 'A. t e. RR+ ( Y <_ t -> %s = K )' % RI('t')), a1(w, A, cb, '( A. t e. RR+ ( Y <_ t -> %s = K ) <-> A. r e. RR+ %s )' % (RI('t'), new))],
                                              'mpbid', 'A. r e. RR+ %s' % new)], 'jca', '( K e. CC /\\ A. r e. RR+ %s )' % new)
    h = st([st([], 'simp1', P1), st([], 'simp2', P2), p3r], '3jca', split_imp(STATEMENTS['z6shl'])[0])
    sh = st([h, w.inst('z6shl')], 'syl', '( %s - %s ) = K' % (VLs('B'), VLs('A')))

    def cbv(c):
        idk = w.s([], 'id', '( t = s -> t = s )')
        sb, _ = w.congr(LI('G', c, 't'), {'t': 's'}, 't = s', {'t': idk})
        return a1(w, A, w.s([w.s([sb], 'cbvmptv', '%s = ( s e. RR+ |-> %s )' % (VLF('G', c), LI('G', c, 's')))], 'fveq2i', '%s = %s' % (VL('G', c), VLs(c))),
                  '%s = %s' % (VL('G', c), VLs(c)))
    eq = st([cbv('B'), cbv('A')], 'oveq12d', '( %s - %s ) = ( %s - %s )' % (VL('G', 'B'), VL('G', 'A'), VLs('B'), VLs('A')))
    w.qed([eq, sh], 'eqtrd', STATEMENTS['z6shift'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6hedge, z6shl, z6shift]:
        if want(f.__name__):
            run(f())
