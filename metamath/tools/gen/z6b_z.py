"""Sortie Z6b, section 4: the anchor identity z6anchor (Lean anchor_identity).
z6ancv   the detector series and 2 pi i times it converge (absolutely, against K^-2)
z6anbd   | LI ( G3 , 3 , T ) - 2 pi i sum STERM | <_ K1 Z2 2 ^ ( - T / 4 )
z6anchor
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_z.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import mpval, cbvm
from z6b_m import inst_all
import lin
from lin import linarith
import num

only = sys.argv[1:]
ZF = '( n e. NN |-> ( n ^c -u 2 ) )'
NNUZ = 'NN = ( ZZ>= ` 1 )'


def want(lab):
    return not only or lab in only


def m2(w, am, mn):
    st = mkst(w, am)
    return st([st([mn], 'nnrpd', 'm e. RR+'), c_(w, am, w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR'), '-u 2 e. RR')], 'rpcxpcld', '( m ^c -u 2 ) e. RR+')


def zcv(w, a):
    """( a -> seq 1 ( + , ZF ) e. dom ~~> )"""
    st = mkst(w, a)
    ak = '( %s /\\ k e. NN )' % a
    zv, _ = mpval(w, ak, 'n', 'NN', '( n ^c -u 2 )', 'k', w.s([], 'simpr', '( %s -> k e. NN )' % ak))
    re2 = c_(w, a, w.s([w.s([], '2re', '2 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 2 ) = 2'), '( Re ` 2 ) = 2')
    return st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], '1lt2', '1 < 2'), '1 < 2'), re2], 'breqtrrd', '1 < ( Re ` 2 )'), zv], 'zetacvg',
              'seq 1 ( + , %s ) e. dom ~~>' % ZF)


def cvg(w, a, G, body, C, cr, zc=None):
    """( a -> seq 1 ( + , G ) e. dom ~~> ) by cvgcmpce against C m^-2 ; body(am, mn) -> (eq: ( G ` m ) = V , vc: V e. CC , vb: ( abs ` V ) <_ ( C x. ( m ^c -u 2 ) ) )"""
    st = mkst(w, a)
    am = '( %s /\\ m e. NN )' % a; t = mkst(w, am)
    mn = t([], 'simpr', 'm e. NN')
    eq, vc, vb = body(am, mn)
    from congr import parse_wff
    V = parse_wff(split_imp(__import__('cl').formula_of(w, eq))[1]).kids[1].text()
    zv, _ = mpval(w, am, 'n', 'NN', '( n ^c -u 2 )', 'm', mn)
    ZFm = '( %s ` m )' % ZF
    gc = t([eq, vc], 'eqeltrd', '( %s ` m ) e. CC' % G)
    zre = t([zv, t([m2(w, am, mn)], 'rpred', '( m ^c -u 2 ) e. RR')], 'eqeltrd', '%s e. RR' % ZFm)
    b1 = t([t([t([eq], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` %s )' % (G, V)), vb], 'eqbrtrd', '( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c -u 2 ) )' % (G, C)),
            t([t([zv], 'eqcomd', '( m ^c -u 2 ) = %s' % ZFm)], 'oveq2d', '( %s x. ( m ^c -u 2 ) ) = ( %s x. %s )' % (C, C, ZFm))], 'breqtrd',
           '( abs ` ( %s ` m ) ) <_ ( %s x. %s )' % (G, C, ZFm))
    am1 = '( %s /\\ m e. ( ZZ>= ` 1 ) )' % a
    mn1 = w.s([w.s([], 'simpr', '( %s -> m e. ( ZZ>= ` 1 ) )' % am1), w.s([w.s([w.s([], 'nnuz', NNUZ)], 'eleq2i', '( m e. NN <-> m e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                   '( m e. ( ZZ>= ` 1 ) -> m e. NN )')], 'syl', '( %s -> m e. NN )' % am1)
    b2 = w.s([w.s([w.s([b1], 'ex', '( %s -> ( m e. NN -> ( abs ` ( %s ` m ) ) <_ ( %s x. %s ) ) )' % (a, G, C, ZFm))], 'adantr',
                  '( %s -> ( m e. NN -> ( abs ` ( %s ` m ) ) <_ ( %s x. %s ) ) )' % (am1, G, C, ZFm)), mn1], 'mpd', '( %s -> ( abs ` ( %s ` m ) ) <_ ( %s x. %s ) )' % (am1, G, C, ZFm))
    return st([w.s([], 'nnuz', NNUZ), c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'), zre, gc, zc or zcv(w, a), cr, b2], 'cvgcmpce', 'seq 1 ( + , %s ) e. dom ~~>' % G)


def z6ancv():
    w = W('z6ancv', 'The detector series at one modulus ` r ` and ` 2 pi i ` times it converge absolutely: at height ` T = 1 ` , '
          '` | 2 pi i STERM ( K ) | <_ | lint | + | lint - 2 pi i STERM | ` (~ z6anb , ~ z6aerr ) is ` O ( K ^ -u 2 ) ` , and ` | 2 pi i | >_ 1 ` '
          '(Lean ` summable_Sterm ` ).')
    a = ante('z6ancv'); f = unpack(w, a); st = mkst(w, a)
    e1 = E4('1')
    C3 = '( ( %s x. ( 2 x. 1 ) ) + ( %s x. %s ) )' % (K0A, K1A, e1)
    zc = zcv(w, a)
    def reals(ctx):
        t = mkst(w, ctx)
        from z6b_r import dfacts
        fl = LZ(w, f, ctx)
        d = dfacts(w, ctx, fl)
        three = c_(w, ctx, w.s([], '3re', '3 e. RR'), '3 e. RR')
        x3r = t([t([d['xrp'], three], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
        rr = t([fl['R e. NN']], 'nnred', 'R e. RR')
        k0r = t([t([c_(w, ctx, num.real(w, '; 3 2'), '; 3 2 e. RR'), rr], 'remulcld', '( ; 3 2 x. R ) e. RR'), x3r], 'remulcld', '%s e. RR' % K0A)
        l2r = t([c_(w, ctx, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')], 'relogcld', '( log ` 2 ) e. RR')
        l2p = linarith(w, ctx, [c_(w, ctx, w.s([], 'z5dlog2', '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )'), '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )')], '0 < ( log ` 2 )', leaves={'( log ` 2 )': l2r})
        c2r = t([c_(w, ctx, num.real(w, '; ; 2 5 6'), '; ; 2 5 6 e. RR'), l2r, t([l2p], 'gt0ne0d', '( log ` 2 ) =/= 0')], 'redivcld', '( ; ; 2 5 6 / ( log ` 2 ) ) e. RR')
        k1r = t([t([rr, x3r], 'remulcld', '( R x. ( %s ^c 3 ) ) e. RR' % XPD), c2r], 'remulcld', '%s e. RR' % K1A)
        return k0r, k1r
    k0r, k1r = reals(a)
    e1r = st([st([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), c_(w, a, w.s([w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '4ne0', '4 =/= 0')], 'redivcli',
                                                                                                       '( 1 / 4 ) e. RR')], 'renegcli', '-u ( 1 / 4 ) e. RR')], 'x', 'x'), 'x') if False else
                  c_(w, a, w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '4ne0', '4 =/= 0')], 'redivcli', '( 1 / 4 ) e. RR')], 'renegcli', '-u ( 1 / 4 ) e. RR'),
                     '-u ( 1 / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % e1)], 'rpred', '%s e. RR' % e1)
    c3r = st([st([k0r, st([c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'remulcld', '( 2 x. 1 ) e. RR')], 'remulcld',
                 '( %s x. ( 2 x. 1 ) ) e. RR' % K0A), st([k1r, e1r], 'remulcld', '( %s x. %s ) e. RR' % (K1A, e1))], 'readdcld', '%s e. RR' % C3)
    ST = lambda n: STERM('R', n)

    def tsbody(am, mn):
        t = mkst(w, am)
        fl = LZ(w, f, am); fl['1 e. RR+'] = c_(w, am, w.s([], '1rp', '1 e. RR+'), '1 e. RR+'); fl['m e. NN'] = mn
        mp = {'T': '1', 'K': 'm'}
        b1, b1c = applyn(w, am, 'z6anb', mp, fl)
        b2, b2c = applyn(w, am, 'z6aerr', mp, fl)
        LF1 = sub(LFK, mp)
        TS = '( %s x. %s )' % (TPI, ST('m'))
        lfc = t([b1, w.inst('z6absle')], 'syl', '%s e. CC' % LF1)
        dfc = t([b2, w.inst('z6absle')], 'syl', '( %s - %s ) e. CC' % (LF1, TS))
        # TS = LF - ( LF - TS ) needs TS e. CC: from ( LF - TS ) e. CC and LF e. CC
        return b1, b1c, b2, b2c, LF1, TS, lfc, dfc
    # the proof of the TS bound needs TS e. CC: 2 pi i STERM ; get STERM e. CC from its factors
    def stcc(am, mn):
        t = mkst(w, am)
        fl = LZ(w, f, am)
        from z6b_r import dfacts
        d = dfacts(w, am, fl)
        bv = t([t([t([d['hab'], mn], 'jca', '( %s /\\ m e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5bvaabs')], 'syl', '( abs ` ( ( %s bvA %s ) ` m ) ) <_ m' % (Z1D, Z2D)),
                w.inst('z6absle')], 'syl', '( ( %s bvA %s ) ` m ) e. CC' % (Z1D, Z2D))
        ps = t([t([fl['R e. NN'], mn, w.inst('z5psiabs')], 'syl2anc', '( abs ` ( ( mmu ` ( R gcd m ) ) x. ( phi ` ( R gcd m ) ) ) ) <_ R'), w.inst('z6absle')], 'syl',
               '( ( mmu ` ( R gcd m ) ) x. ( phi ` ( R gcd m ) ) ) e. CC')
        cm = t([fl['C : NN --> CC'], mn], 'ffvelcdmd', '( C ` m ) e. CC')
        CO = COEFG(Z1D, Z2D, 'R', 'm')
        coc = t([t([bv, ps], 'mulcld', '( ( ( %s bvA %s ) ` m ) x. ( ( mmu ` ( R gcd m ) ) x. ( phi ` ( R gcd m ) ) ) ) e. CC' % (Z1D, Z2D)), cm], 'mulcld', '%s e. CC' % CO)
        EX = '( exp ` ( -u m / %s ) )' % XPD
        exc = t([t([t([t([mn], 'nncnd', 'm e. CC')], 'negcld', '-u m e. CC'), t([d['xrp']], 'rpcnd', '%s e. CC' % XPD), t([d['xrp']], 'rpne0d', '%s =/= 0' % XPD)], 'divcld',
                   '( -u m / %s ) e. CC' % XPD)], 'efcld', '%s e. CC' % EX)
        kc = t([t([mn], 'nncnd', 'm e. CC'), t([fl['S e. CC']], 'negcld', '-u S e. CC')], 'cxpcld', '( m ^c -u S ) e. CC')
        return t([coc, t([exc, kc], 'mulcld', '( %s x. ( m ^c -u S ) ) e. CC' % EX)], 'mulcld', '%s e. CC' % ST('m'))
    tpc = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                  'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)

    def tsb(am, mn):
        t = mkst(w, am)
        b1, b1c, b2, b2c, LF1, TS, lfc, dfc = tsbody(am, mn)
        sc_ = stcc(am, mn)
        tsc = t([lift(w, tpc, am), sc_], 'mulcld', '%s e. CC' % TS)
        e = t([lfc, tsc], 'nncand', '( %s - ( %s - %s ) ) = %s' % (LF1, LF1, TS, TS))
        tri = t([lfc, dfc], 'abs2dif2d', '( abs ` ( %s - ( %s - %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (LF1, LF1, TS, LF1, LF1, TS))
        tri2 = t([t([t([e], 'fveq2d', '( abs ` ( %s - ( %s - %s ) ) ) = ( abs ` %s )' % (LF1, LF1, TS, TS))], 'eqcomd', '( abs ` %s ) = ( abs ` ( %s - ( %s - %s ) ) )' % (TS, LF1, LF1, TS)),
                  tri], 'eqbrtrd', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (TS, LF1, LF1, TS))
        M2 = '( m ^c -u 2 )'
        A1 = '( abs ` %s )' % LF1; A2 = '( abs ` ( %s - %s ) )' % (LF1, TS)
        L = {A1: t([lfc], 'abscld', '%s e. RR' % A1), A2: t([dfc], 'abscld', '%s e. RR' % A2), '( abs ` %s )' % TS: t([tsc], 'abscld', '( abs ` %s ) e. RR' % TS),
             K0A: lift(w, k0r, am), K1A: lift(w, k1r, am), e1: lift(w, e1r, am), M2: t([m2(w, am, mn)], 'rpred', '%s e. RR' % M2)}
        old = lin.MAXDEG; lin.MAXDEG = 6
        bnd = linarith(w, am, [tri2, b1, b2], '( abs ` %s ) <_ ( %s x. %s )' % (TS, C3, M2), leaves=L, products=True, atoms=[K0A, K1A, e1, M2, A1, A2])
        lin.MAXDEG = old
        return tsc, bnd, sc_

    def tsfbody(am, mn):
        tsc, bnd, _ = tsb(am, mn)
        eq, _ = mpval(w, am, 'n', 'NN', '( %s x. %s )' % (TPI, ST('n')), 'm', mn)
        return eq, tsc, bnd
    cv2 = cvg(w, a, TSF, tsfbody, C3, c3r, zc)

    def stfbody(am, mn):
        t = mkst(w, am)
        tsc, bnd, sc_ = tsb(am, mn)
        eq, _ = mpval(w, am, 'n', 'NN', ST('n'), 'm', mn)
        TS = '( %s x. %s )' % (TPI, ST('m'))
        # | STERM | <_ | 2 pi i STERM | since | 2 pi i | >_ 1
        pi3 = c_(w, am, w.s([], 'pige3', '3 <_ _pi'), '3 <_ _pi')
        pir = c_(w, am, w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
        ic = c_(w, am, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
        a1 = t([c_(w, am, w.s([], '2cn', '2 e. CC'), '2 e. CC'), t([ic, t([pir], 'recnd', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'absmuld',
               '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
        a2 = t([ic, t([pir], 'recnd', '_pi e. CC')], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )')
        ap = t([pir, linarith(w, am, [pi3], '0 <_ _pi', leaves={'_pi': pir})], 'absidd', '( abs ` _pi ) = _pi')
        a2b = t([a2, t([c_(w, am, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1'), ap], 'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtrd',
                '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')
        a3 = t([c_(w, am, w.s([], '2re', '2 e. RR'), '2 e. RR'), c_(w, am, w.s([], '0le2', '0 <_ 2'), '0 <_ 2')], 'absidd', '( abs ` 2 ) = 2')
        atp = t([a1, t([a3, a2b], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. ( 1 x. _pi ) )')], 'eqtrd', '( abs ` %s ) = ( 2 x. ( 1 x. _pi ) )' % TPI)
        AS = '( abs ` %s )' % ST('m')
        asr = t([sc_], 'abscld', '%s e. RR' % AS); as0 = t([sc_], 'absge0d', '0 <_ %s' % AS)
        tpr = t([lift(w, tpc, am)], 'abscld', '( abs ` %s ) e. RR' % TPI)
        t1 = t([linarith(w, am, [pi3], '1 <_ ( 2 x. ( 1 x. _pi ) )', leaves={'_pi': pir}), atp], 'breqtrrd', '1 <_ ( abs ` %s )' % TPI)
        m1 = t([c_(w, am, w.s([], '1re', '1 e. RR'), '1 e. RR'), tpr, asr, as0, t1], 'lemul1ad', '( 1 x. %s ) <_ ( ( abs ` %s ) x. %s )' % (AS, TPI, AS))
        ab = t([lift(w, tpc, am), sc_], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (TS, TPI, AS))
        m2_ = t([t([t([t([asr], 'recnd', '%s e. CC' % AS)], 'mullidd', '( 1 x. %s ) = %s' % (AS, AS))], 'eqcomd', '%s = ( 1 x. %s )' % (AS, AS)), m1], 'eqbrtrd',
                '%s <_ ( ( abs ` %s ) x. %s )' % (AS, TPI, AS))
        m3 = t([m2_, t([ab], 'eqcomd', '( ( abs ` %s ) x. %s ) = ( abs ` %s )' % (TPI, AS, TS))], 'breqtrd', '%s <_ ( abs ` %s )' % (AS, TS))
        M2 = '( m ^c -u 2 )'
        c3m = t([lift(w, c3r, am), t([m2(w, am, mn)], 'rpred', '%s e. RR' % M2)], 'remulcld', '( %s x. %s ) e. RR' % (C3, M2))
        b = t([asr, t([tsc], 'abscld', '( abs ` %s ) e. RR' % TS), c3m, m3, bnd], 'letrd', '%s <_ ( %s x. %s )' % (AS, C3, M2))
        return eq, sc_, b
    cv1 = cvg(w, a, STF, stfbody, C3, c3r, zc)
    w.qed([cv1, cv2], 'jca', STATEMENTS['z6ancv'])
    return w


def k1real(w, ctx, fl):
    t = mkst(w, ctx)
    from z6b_r import dfacts
    d = dfacts(w, ctx, fl)
    three = c_(w, ctx, w.s([], '3re', '3 e. RR'), '3 e. RR')
    x3r = t([t([d['xrp'], three], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
    rr = t([fl['R e. NN']], 'nnred', 'R e. RR')
    l2r = t([c_(w, ctx, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')], 'relogcld', '( log ` 2 ) e. RR')
    l2p = linarith(w, ctx, [c_(w, ctx, w.s([], 'z5dlog2', '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )'), '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )')], '0 < ( log ` 2 )', leaves={'( log ` 2 )': l2r})
    c2r = t([c_(w, ctx, num.real(w, '; ; 2 5 6'), '; ; 2 5 6 e. RR'), l2r, t([l2p], 'gt0ne0d', '( log ` 2 ) =/= 0')], 'redivcld', '( ; ; 2 5 6 / ( log ` 2 ) ) e. RR')
    return t([t([rr, x3r], 'remulcld', '( R x. ( %s ^c 3 ) ) e. RR' % XPD), c2r], 'remulcld', '%s e. RR' % K1A)


def e4real(w, ctx, tr, T):
    t = mkst(w, ctx)
    return t([t([c_(w, ctx, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), t([t([tr, c_(w, ctx, w.s([], '4re', '4 e. RR'), '4 e. RR'), c_(w, ctx, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                       'redivcld', '( %s / 4 ) e. RR' % T)], 'renegcld', '-u ( %s / 4 ) e. RR' % T)], 'rpcxpcld', '%s e. RR+' % E4(T))],
             'rpred', '%s e. RR' % E4(T))


def z6anbd():
    w = W('z6anbd', 'At every height ` T ` the truncated anchor line integral is within ` K1 Z2 2 ^ ( - T / 4 ) ` of ` 2 pi i ` times the detector series '
          '(~ z6anl , ~ z6aerr , ~ isumadd , ~ iserabs , ~ isumle ).')
    a = ante('z6anbd'); f = unpack(w, a); st = mkst(w, a)
    trp = f['T e. RR+']; tr = st([trp], 'rpred', 'T e. RR')
    ST = lambda n: STERM('R', n)
    LF = lambda n: sub(LFK, {'K': n})
    LIT = LI(G3('R'), '3', 'T')
    E_ = E4('T'); CE = '( %s x. %s )' % (K1A, E_)
    anl, _ = applyn(w, a, 'z6anl', {}, f)
    LFF = '( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) )' % (FNS, SA, SB)
    cv, _ = applyn(w, a, 'z6ancv', {}, f)
    stcv = st([cv], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % STF); tscv = st([cv], 'simprd', 'seq 1 ( + , %s ) e. dom ~~>' % TSF)
    k1r = k1real(w, a, f); e4r = e4real(w, a, tr, 'T')
    cer = st([k1r, e4r], 'remulcld', '%s e. RR' % CE)
    zc = zcv(w, a)
    EF = '( q e. NN |-> ( %s - ( %s x. %s ) ) )' % (LF('q'), TPI, ST('q'))
    AEF = '( q e. NN |-> ( abs ` ( %s - ( %s x. %s ) ) ) )' % (LF('q'), TPI, ST('q'))
    BF = '( q e. NN |-> ( %s x. ( q ^c -u 2 ) ) )' % CE
    Em = '( %s - ( %s x. %s ) )' % (LF('m'), TPI, ST('m'))
    M2 = '( m ^c -u 2 )'

    def err(am, mn):
        fl = LZ(w, f, am); fl['m e. NN'] = mn
        b, _ = applyn(w, am, 'z6aerr', {'K': 'm'}, fl)
        return b

    def efb(am, mn):
        t = mkst(w, am)
        b = err(am, mn)
        eq, _ = mpval(w, am, 'q', 'NN', '( %s - ( %s x. %s ) )' % (LF('q'), TPI, ST('q')), 'm', mn)
        return eq, t([b, w.inst('z6absle')], 'syl', '%s e. CC' % Em), b
    ecv = cvg(w, a, EF, efb, CE, cer, zc)

    def aefb(am, mn):
        t = mkst(w, am)
        b = err(am, mn)
        emc = t([b, w.inst('z6absle')], 'syl', '%s e. CC' % Em)
        eq, _ = mpval(w, am, 'q', 'NN', '( abs ` ( %s - ( %s x. %s ) ) )' % (LF('q'), TPI, ST('q')), 'm', mn)
        aer = t([emc], 'abscld', '( abs ` %s ) e. RR' % Em)
        aa = t([aer, t([emc], 'absge0d', '0 <_ ( abs ` %s )' % Em)], 'absidd', '( abs ` ( abs ` %s ) ) = ( abs ` %s )' % (Em, Em))
        return eq, t([aer], 'recnd', '( abs ` %s ) e. CC' % Em), t([aa, b], 'eqbrtrd', '( abs ` ( abs ` %s ) ) <_ ( %s x. %s )' % (Em, CE, M2))
    aecv = cvg(w, a, AEF, aefb, CE, cer, zc)

    def bfb(am, mn):
        t = mkst(w, am)
        eq, _ = mpval(w, am, 'q', 'NN', '( %s x. ( q ^c -u 2 ) )' % CE, 'm', mn)
        m2r = t([m2(w, am, mn)], 'rpred', '%s e. RR' % M2)
        vr = t([lift(w, cer, am), m2r], 'remulcld', '( %s x. %s ) e. RR' % (CE, M2))
        # CE >_ 0 : K1 >_ 0 , E4 > 0
        return eq, t([vr], 'recnd', '( %s x. %s ) e. CC' % (CE, M2)), None
    # BF: the bound | BF m | <_ CE m^-2 needs CE >_ 0; get it from | E | <_ CE m^-2 at m = 1
    am1_ = '( %s /\\ 1 e. NN )' % a
    b1 = err1 = None
    fl1 = LZ(w, f, a); fl1['1 e. NN'] = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    eb1, _ = applyn(w, a, 'z6aerr', {'K': '1'}, fl1)
    E1 = sub(Em, {'m': '1'})
    e1c = st([eb1, w.inst('z6absle')], 'syl', '%s e. CC' % E1)
    one2 = c_(w, a, w.s([w.s([w.s([], '2cn', '2 e. CC')], 'negcli', '-u 2 e. CC'), w.inst('1cxp')], 'ax-mp', '( 1 ^c -u 2 ) = 1'), '( 1 ^c -u 2 ) = 1')
    ceb = st([eb1, st([st([one2], 'oveq2d', '( %s x. ( 1 ^c -u 2 ) ) = ( %s x. 1 )' % (CE, CE)), st([st([cer], 'recnd', '%s e. CC' % CE)], 'mulridd', '( %s x. 1 ) = %s' % (CE, CE))],
                      'eqtrd', '( %s x. ( 1 ^c -u 2 ) ) = %s' % (CE, CE))], 'breqtrd', '( abs ` %s ) <_ %s' % (E1, CE))
    ce0 = linarith(w, a, [st([e1c], 'absge0d', '0 <_ ( abs ` %s )' % E1), ceb], '0 <_ %s' % CE, leaves={'( abs ` %s )' % E1: st([e1c], 'abscld', '( abs ` %s ) e. RR' % E1), CE: cer})

    def bfb2(am, mn):
        t = mkst(w, am)
        eq, _ = mpval(w, am, 'q', 'NN', '( %s x. ( q ^c -u 2 ) )' % CE, 'm', mn)
        m2p = m2(w, am, mn); m2r = t([m2p], 'rpred', '%s e. RR' % M2)
        vr = t([lift(w, cer, am), m2r], 'remulcld', '( %s x. %s ) e. RR' % (CE, M2))
        v0 = t([lift(w, cer, am), m2r, lift(w, ce0, am), t([m2p], 'rpge0d', '0 <_ %s' % M2)], 'mulge0d', '0 <_ ( %s x. %s )' % (CE, M2))
        return eq, t([vr], 'recnd', '( %s x. %s ) e. CC' % (CE, M2)), t([t([vr, v0], 'absidd', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (CE, M2, CE, M2))], 'eqled',
                                                                          '( abs ` ( %s x. %s ) ) <_ ( %s x. %s )' % (CE, M2, CE, M2))
    bcv = cvg(w, a, BF, bfb2, CE, cer, zc)
    # the sums over m
    am = '( %s /\\ m e. NN )' % a; t = mkst(w, am)
    mn = t([], 'simpr', 'm e. NN')
    fl = LZ(w, f, am); fl['m e. NN'] = mn
    lfb, _ = applyn(w, am, 'z6anb', {'K': 'm'}, fl)
    lfc = t([lfb, w.inst('z6absle')], 'syl', '%s e. CC' % LF('m'))
    lfv, _ = mpval(w, am, 'k', 'NN', '( ( %s ` k ) lint <. %s , %s >. )' % (FNS, SA, SB), 'm', mn)
    nnuz = w.s([], 'nnuz', NNUZ); z1 = c_(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    s1 = w.s([nnuz, z1, lfv, lfc, anl], 'isumclim', '( %s -> sum_ m e. NN %s = %s )' % (a, LF('m'), LIT))
    eb = err(am, mn)
    emc = t([eb, w.inst('z6absle')], 'syl', '%s e. CC' % Em)
    TSm = '( %s x. %s )' % (TPI, ST('m'))
    tpc0 = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                   'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    tsc = t([lift(w, tpc0, am), stcc_(w, am, f, mn)], 'mulcld', '%s e. CC' % TSm)
    dec = t([t([tsc, lfc], 'pncan3d', '( %s + %s ) = %s' % (TSm, Em, LF('m')))], 'eqcomd', '%s = ( %s + %s )' % (LF('m'), TSm, Em))
    s2 = st([dec], 'sumeq2dv', 'sum_ m e. NN %s = sum_ m e. NN ( %s + %s )' % (LF('m'), TSm, Em))
    tsv, _ = mpval(w, am, 'n', 'NN', '( %s x. %s )' % (TPI, ST('n')), 'm', mn)
    efv, _ = mpval(w, am, 'q', 'NN', '( %s - ( %s x. %s ) )' % (LF('q'), TPI, ST('q')), 'm', mn)
    s3 = w.s([nnuz, z1, tsv, tsc, efv, emc, tscv, ecv], 'isumadd', '( %s -> sum_ m e. NN ( %s + %s ) = ( sum_ m e. NN %s + sum_ m e. NN %s ) )' % (a, TSm, Em, TSm, Em))
    stv, _ = mpval(w, am, 'n', 'NN', ST('n'), 'm', mn)
    # STERM m e. CC from TSm = TPI x. ST and TPI =/= 0
    tpc = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                  'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    i0 = st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC'), c_(w, a, w.s([], 'ine0', '_i =/= 0'), '_i =/= 0'),
             c_(w, a, w.s([], 'pine0', '_pi =/= 0'), '_pi =/= 0')], 'mulne0d', '( _i x. _pi ) =/= 0')
    tp0 = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                  'mulcld', '( _i x. _pi ) e. CC'), c_(w, a, w.s([], '2ne0', '2 =/= 0'), '2 =/= 0'), i0], 'mulne0d', '%s =/= 0' % TPI)
    stc0 = t([tsc, lift(w, tpc, am), lift(w, tp0, am)], 'divcld', '( %s / %s ) e. CC' % (TSm, TPI))
    # ST m = ( TSm / TPI ) by divcan3
    ST_ = ST('m')
    stm = stcc_(w, am, f, mn)
    s4 = w.s([nnuz, z1, stv, stm, stcv, tpc], 'isummulc2', '( %s -> ( %s x. sum_ m e. NN %s ) = sum_ m e. NN ( %s x. %s ) )' % (a, TPI, ST('m'), TPI, ST('m')))
    SE = 'sum_ m e. NN %s' % Em; STS = 'sum_ m e. NN %s' % ST('m')
    lit = st([st([st([s1], 'eqcomd', '%s = sum_ m e. NN %s' % (LIT, LF('m'))), s2], 'eqtrd', '%s = sum_ m e. NN ( %s + %s )' % (LIT, TSm, Em)),
              st([s3, st([st([s4], 'eqcomd', 'sum_ m e. NN %s = ( %s x. %s )' % (TSm, TPI, STS))], 'oveq1d', '( sum_ m e. NN %s + %s ) = ( ( %s x. %s ) + %s )' % (TSm, SE, TPI, STS, SE))],
                 'eqtrd', 'sum_ m e. NN ( %s + %s ) = ( ( %s x. %s ) + %s )' % (TSm, Em, TPI, STS, SE))], 'eqtrd', '%s = ( ( %s x. %s ) + %s )' % (LIT, TPI, STS, SE))
    stsc = w.s([nnuz, z1, stv, stm, stcv], 'isumcl', '( %s -> %s e. CC )' % (a, STS))
    sec = w.s([nnuz, z1, efv, emc, ecv], 'isumcl', '( %s -> %s e. CC )' % (a, SE))
    tstc = st([tpc, stsc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, STS))
    df = st([st([lit], 'oveq1d', '( %s - ( %s x. %s ) ) = ( ( ( %s x. %s ) + %s ) - ( %s x. %s ) )' % (LIT, TPI, STS, TPI, STS, SE, TPI, STS)),
             st([tstc, sec], 'pncan2d', '( ( ( %s x. %s ) + %s ) - ( %s x. %s ) ) = %s' % (TPI, STS, SE, TPI, STS, SE))], 'eqtrd', '( %s - ( %s x. %s ) ) = %s' % (LIT, TPI, STS, SE))
    # | SE | <_ sum | E | <_ CE Z2
    ASE = 'sum_ m e. NN ( abs ` %s )' % Em
    aefv, _ = mpval(w, am, 'q', 'NN', '( abs ` ( %s - ( %s x. %s ) ) )' % (LF('q'), TPI, ST('q')), 'm', mn)
    ec1 = w.s([nnuz, z1, efv, emc, ecv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (a, EF, SE))
    aemc = t([t([emc], 'abscld', '( abs ` %s ) e. RR' % Em)], 'recnd', '( abs ` %s ) e. CC' % Em)
    ec2 = w.s([nnuz, z1, aefv, aemc, aecv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (a, AEF, ASE))
    efc = t([efv, emc], 'eqeltrd', '( %s ` m ) e. CC' % EF)
    ga = t([aefv, t([efv], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` %s )' % (EF, Em))], 'eqtr4d', '( %s ` m ) = ( abs ` ( %s ` m ) )' % (AEF, EF))
    ia = w.s([nnuz, ec1, ec2, z1, efc, ga], 'iserabs', '( %s -> ( abs ` %s ) <_ %s )' % (a, SE, ASE))
    bfv, _ = mpval(w, am, 'q', 'NN', '( %s x. ( q ^c -u 2 ) )' % CE, 'm', mn)
    m2r = t([m2(w, am, mn)], 'rpred', '%s e. RR' % M2)
    il = w.s([nnuz, z1, aefv, t([emc], 'abscld', '( abs ` %s ) e. RR' % Em), bfv, t([lift(w, cer, am), m2r], 'remulcld', '( %s x. %s ) e. RR' % (CE, M2)), eb, aecv, bcv], 'isumle',
             '( %s -> %s <_ sum_ m e. NN ( %s x. %s ) )' % (a, ASE, CE, M2))
    zv, _ = mpval(w, am, 'n', 'NN', '( n ^c -u 2 )', 'm', mn)
    im2 = w.s([nnuz, z1, zv, t([m2r], 'recnd', '%s e. CC' % M2), zc, st([cer], 'recnd', '%s e. CC' % CE)], 'isummulc2',
              '( %s -> ( %s x. %s ) = sum_ m e. NN ( %s x. %s ) )' % (a, CE, Z2S, CE, M2))
    b2 = st([il, st([im2], 'eqcomd', 'sum_ m e. NN ( %s x. %s ) = ( %s x. %s )' % (CE, M2, CE, Z2S))], 'breqtrd', '%s <_ ( %s x. %s )' % (ASE, CE, Z2S))
    z2r = w.s([nnuz, z1, zv, m2r, zc], 'isumrecl', '( %s -> %s e. RR )' % (a, Z2S))
    ser = st([sec], 'abscld', '( abs ` %s ) e. RR' % SE)
    aser = w.s([nnuz, z1, aefv, t([emc], 'abscld', '( abs ` %s ) e. RR' % Em), aecv], 'isumrecl', '( %s -> %s e. RR )' % (a, ASE))
    b3 = st([ser, aser, st([cer, z2r], 'remulcld', '( %s x. %s ) e. RR' % (CE, Z2S)), ia, b2], 'letrd', '( abs ` %s ) <_ ( %s x. %s )' % (SE, CE, Z2S))
    m32 = st([st([k1r], 'recnd', '%s e. CC' % K1A), st([e4r], 'recnd', '%s e. CC' % E_), st([z2r], 'recnd', '%s e. CC' % Z2S)], 'mul32d',
             '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (K1A, E_, Z2S, K1A, Z2S, E_))
    b4 = st([b3, m32], 'breqtrd', '( abs ` %s ) <_ ( ( %s x. %s ) x. %s )' % (SE, K1A, Z2S, E_))
    w.qed([st([df], 'fveq2d', '( abs ` ( %s - ( %s x. %s ) ) ) = ( abs ` %s )' % (LIT, TPI, STS, SE)), b4], 'eqbrtrd', STATEMENTS['z6anbd'])
    return w


def stcc_(w, am, f, mn):
    """( am -> STERM ( R , m ) e. CC )"""
    t = mkst(w, am)
    fl = LZ(w, f, am)
    from z6b_r import dfacts
    d = dfacts(w, am, fl)
    bv = t([t([t([d['hab'], mn], 'jca', '( %s /\\ m e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5bvaabs')], 'syl', '( abs ` ( ( %s bvA %s ) ` m ) ) <_ m' % (Z1D, Z2D)),
            w.inst('z6absle')], 'syl', '( ( %s bvA %s ) ` m ) e. CC' % (Z1D, Z2D))
    ps = t([t([fl['R e. NN'], mn, w.inst('z5psiabs')], 'syl2anc', '( abs ` ( ( mmu ` ( R gcd m ) ) x. ( phi ` ( R gcd m ) ) ) ) <_ R'), w.inst('z6absle')], 'syl',
           '( ( mmu ` ( R gcd m ) ) x. ( phi ` ( R gcd m ) ) ) e. CC')
    cm = t([fl['C : NN --> CC'], mn], 'ffvelcdmd', '( C ` m ) e. CC')
    CO = COEFG(Z1D, Z2D, 'R', 'm')
    coc = t([t([bv, ps], 'mulcld', '( ( ( %s bvA %s ) ` m ) x. ( ( mmu ` ( R gcd m ) ) x. ( phi ` ( R gcd m ) ) ) ) e. CC' % (Z1D, Z2D)), cm], 'mulcld', '%s e. CC' % CO)
    EX = '( exp ` ( -u m / %s ) )' % XPD
    exc = t([t([t([t([mn], 'nncnd', 'm e. CC')], 'negcld', '-u m e. CC'), t([d['xrp']], 'rpcnd', '%s e. CC' % XPD), t([d['xrp']], 'rpne0d', '%s =/= 0' % XPD)], 'divcld',
               '( -u m / %s ) e. CC' % XPD)], 'efcld', '%s e. CC' % EX)
    kc = t([t([mn], 'nncnd', 'm e. CC'), t([fl['S e. CC']], 'negcld', '-u S e. CC')], 'cxpcld', '( m ^c -u S ) e. CC')
    return t([coc, t([exc, kc], 'mulcld', '( %s x. ( m ^c -u S ) ) e. CC' % EX)], 'mulcld', '%s e. CC' % STERM('R', 'm'))


def z6anchor():
    w = W('z6anchor', 'Blueprint Lemma 4.1 on the anchor line (Lean ` anchor_identity ` ): the detector series at one squarefree modulus ` R ` '
          'converges and ` 2 pi i ` times its sum is the vertical line integral ` int_(3) Gamma ( w ) X ^ w L ( S + w , chi ) M_r ( S + w ) ` '
          '(~ z6ancv , ~ z6anbd , ~ z6e4lim , ~ rlimsqzlem , ~ rlimuni ).')
    a = ante('z6anchor'); f = unpack(w, a); st = mkst(w, a)
    ST = lambda n: STERM('R', n)
    cv, _ = applyn(w, a, 'z6ancv', {}, f)
    stcv = st([cv], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % STF)
    STS = 'sum_ m e. NN %s' % ST('m'); VV = '( %s x. %s )' % (TPI, STS)
    nnuz = w.s([], 'nnuz', NNUZ); z1 = c_(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    am = '( %s /\\ m e. NN )' % a; t = mkst(w, am)
    mn = t([], 'simpr', 'm e. NN')
    stv, _ = mpval(w, am, 'n', 'NN', ST('n'), 'm', mn)
    stm = stcc_(w, am, f, mn)
    stsc = w.s([nnuz, z1, stv, stm, stcv], 'isumcl', '( %s -> %s e. CC )' % (a, STS))
    tpc = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                  'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    vvc = st([tpc, stsc], 'mulcld', '%s e. CC' % VV)
    k1r = k1real(w, a, f)
    zv, _ = mpval(w, am, 'n', 'NN', '( n ^c -u 2 )', 'm', mn)
    m2r = t([m2(w, am, mn)], 'rpred', '( m ^c -u 2 ) e. RR')
    z2r = w.s([nnuz, z1, zv, m2r, zcv(w, a)], 'isumrecl', '( %s -> %s e. RR )' % (a, Z2S))
    KZ = '( %s x. %s )' % (K1A, Z2S)
    kzr = st([k1r, z2r], 'remulcld', '%s e. RR' % KZ)
    B = '( %s x. %s )' % (KZ, E4('t'))
    at = '( %s /\\ t e. RR+ )' % a; tt = mkst(w, at)
    trp = tt([], 'simpr', 't e. RR+'); tr = tt([trp], 'rpred', 't e. RR')
    e4r = e4real(w, at, tr, 't')
    br = tt([lift(w, kzr, at), e4r], 'remulcld', '%s e. RR' % B)
    # the limit of B
    kzc = st([kzr], 'recnd', '%s e. CC' % KZ)
    rc = st([c_(w, a, w.s([], 'rpssre', 'RR+ C_ RR'), 'RR+ C_ RR'), kzc, w.inst('rlimconst')], 'syl2anc', '( t e. RR+ |-> %s ) ~~>r %s' % (KZ, KZ))
    e4l = c_(w, a, w.s([], 'z6e4lim', STATEMENTS['z6e4lim']), STATEMENTS['z6e4lim'])
    rm = w.s([w.s([lift(w, kzc, at)], 'elexd', '( %s -> %s e. _V )' % (at, KZ)), w.s([], 'ovexd', '( %s -> %s e. _V )' % (at, E4('t'))), rc, e4l], 'rlimmul',
             '( %s -> ( t e. RR+ |-> %s ) ~~>r ( %s x. 0 ) )' % (a, B, KZ))
    rm0 = st([rm, st([kzc], 'mul01d', '( %s x. 0 ) = 0' % KZ)], 'breqtrd', '( t e. RR+ |-> %s ) ~~>r 0' % B)
    # C e. CC and the bound
    fl = LZ(w, f, at); fl['t e. RR+'] = trp
    bd, _ = applyn(w, at, 'z6anbd', {'T': 't'}, fl)
    LIt = LI(G3('R'), '3', 't')
    an, _ = applyn(w, at, 'z6anl', {'T': 't'}, fl)
    lic = tt([an, w.inst('climcl')], 'syl', '%s e. CC' % LIt)
    b0 = '( ( %s /\\ ( t e. RR+ /\\ 0 <_ t ) ) )' % a
    at0 = '( %s /\\ ( t e. RR+ /\\ 0 <_ t ) )' % a; t0 = mkst(w, at0)
    trp0 = t0([], 'simprl', 't e. RR+')
    fl0 = LZ(w, f, at0); fl0['t e. RR+'] = trp0
    bd0, _ = applyn(w, at0, 'z6anbd', {'T': 't'}, fl0)
    tr0 = t0([trp0], 'rpred', 't e. RR')
    br0 = t0([lift(w, kzr, at0), e4real(w, at0, tr0, 't')], 'remulcld', '%s e. RR' % B)
    bb = t0([t0([br0], 'leabsd', '%s <_ ( abs ` %s )' % (B, B)), t0([t0([t0([br0], 'recnd', '%s e. CC' % B)], 'subid1d', '( %s - 0 ) = %s' % (B, B))], 'fveq2d',
                                                                                           '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (B, B))], 'breqtrrd', '%s <_ ( abs ` ( %s - 0 ) )' % (B, B))
    an0, _ = applyn(w, at0, 'z6anl', {'T': 't'}, fl0)
    lic0 = t0([an0, w.inst('climcl')], 'syl', '%s e. CC' % LIt)
    dr = t0([t0([lic0, lift(w, vvc, at0)], 'subcld', '( %s - %s ) e. CC' % (LIt, VV))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (LIt, VV))
    abr = t0([t0([t0([br0], 'recnd', '%s e. CC' % B), c_(w, at0, w.s([], '0cn', '0 e. CC'), '0 e. CC')], 'subcld', '( %s - 0 ) e. CC' % B)], 'abscld', '( abs ` ( %s - 0 ) ) e. RR' % B)
    h4 = t0([dr, br0, abr, bd0, bb], 'letrd', '( abs ` ( %s - %s ) ) <_ ( abs ` ( %s - 0 ) )' % (LIt, VV, B))
    sq = w.s([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), vvc, rm0, tt([br], 'recnd', '%s e. CC' % B), lic, h4], 'rlimsqzlem',
             '( %s -> %s ~~>r %s )' % (a, VLF(G3('R'), '3'), VV))
    # uniqueness
    VF = VLF(G3('R'), '3')
    ff = st([lic, w.s([], 'eqid', '%s = %s' % (VF, VF))], 'fmptd', '%s : RR+ --> CC' % VF)
    sp = c_(w, a, w.s([], 'rpsup', 'sup ( RR+ , RR* , < ) = +oo'), 'sup ( RR+ , RR* , < ) = +oo')
    dm = st([c_(w, a, w.s([], 'rlimrel', 'Rel ~~>r'), 'Rel ~~>r'), sq, w.inst('releldm')], 'syl2anc', '%s e. dom ~~>r' % VF)
    rd = st([dm, w.s([ff, sp], 'rlimdm', '( %s -> ( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) ) )' % (a, VF, VF, VF))], 'mpbid', '%s ~~>r ( ~~>r ` %s )' % (VF, VF))
    un = w.s([ff, sp, rd, sq], 'rlimuni', '( %s -> ( ~~>r ` %s ) = %s )' % (a, VF, VV))
    idk = w.s([], 'id', '( m = n -> m = n )')
    sb_, _ = w.congr(ST('m'), {'m': 'n'}, 'm = n', {'m': idk})
    cb = c_(w, a, w.s([sb_], 'cbvsumv', '%s = sum_ n e. NN %s' % (STS, ST('n'))), '%s = sum_ n e. NN %s' % (STS, ST('n')))
    fin = st([st([st([cb], 'oveq2d', '%s = ( %s x. sum_ n e. NN %s )' % (VV, TPI, ST('n')))], 'eqcomd', '( %s x. sum_ n e. NN %s ) = %s' % (TPI, ST('n'), VV)),
              st([un], 'eqcomd', '%s = ( ~~>r ` %s )' % (VV, VF))], 'eqtrd', '( %s x. sum_ n e. NN %s ) = %s' % (TPI, ST('n'), VL(G3('R'), '3')))
    w.qed([stcv, fin], 'jca', STATEMENTS['z6anchor'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6ancv, z6anbd, z6anchor]:
        if want(fn.__name__):
            if not run(fn()):
                break
