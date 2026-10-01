"""Sortie CM: one zero per bad character (cmzero) and the detection window (cmdet).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_d.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *
from cen2lib import ZFB, BOX

only = sys.argv[1:]
HP = "( `' Re \" ( 0 (,) +oo ) )"


def hp0(w, ctx, P, pc, p0):
    """( ctx -> P e. HP0 ) from P e. CC and 0 < Re P (CEN2's route)"""
    s = mk(w, ctx)
    fn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    ep = w.s([fn, w.inst('elpreima')], 'ax-mp', "( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) ) )" % (P, HP, P, P))
    eo = w.s([w.s([], '0xr', '0 e. RR*'), w.inst('elioopnf')], 'ax-mp', '( ( Re ` %s ) e. ( 0 (,) +oo ) <-> ( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) ) )' % (P, P, P))
    rr = s('recld', [pc], '( Re ` %s ) e. RR' % P)
    io = s('mpbird', [s('jca', [rr, p0], '( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) )' % (P, P)), w.s([eo], 'a1i', '( %s -> ( ( Re ` %s ) e. ( 0 (,) +oo ) <-> ( ( Re ` %s ) e. RR /\\ 0 < ( Re ` %s ) ) ) )' % (ctx, P, P, P))],
           '( Re ` %s ) e. ( 0 (,) +oo )' % P)
    return s('mpbird', [s('jca', [pc, io], "( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) )" % (P, P)), w.s([ep], 'a1i', "( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) ) ) )" % (ctx, P, HP, P, P))],
             '%s e. %s' % (P, HP))


def gen_zero():
    w = W('cmzero', 'A bad character mod ` N >_ 2 ` is nonprincipal and its L-function (the Abel series) has a zero ` z ` with ` S <_ Re z <_ 1 ` , ` abs ( Im z ) <_ V ` ( ~ elrab , ~ dchrprimne1 , ~ rabn0 , ~ elcrect , ~ zc1eord ; Lean ` perchar_window ` 414-418).')
    A0, C0 = split_imp(S['cmzero'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    nn = F['N e. NN']; n2 = F['2 <_ N']; sr = F['S e. RR']; s0 = F['0 < S']; vr = F['V e. RR']
    BCN = BC('S', 'V', 'N')
    xbc = F['X e. %s' % BCN]
    BODY = '( ( N DChrCond y ) = N /\\ %s =/= (/) )' % ZFB('S', 'V', 'N', 'y')
    eqy = 'y = X'
    idy = w.s([], 'id', '( %s -> %s )' % (eqy, eqy))
    stb, bodyx = w.wcongr(BODY, {'y': 'X'}, eqy, {'y': idy})
    er = w.s([stb], 'elrab', '( X e. %s <-> ( X e. %s /\\ %s ) )' % (BCN, BASE('N'), bodyx))
    g = d('sylib', [xbc, er], '( X e. %s /\\ %s )' % (BASE('N'), bodyx))
    xb = d('simpld', [g], 'X e. %s' % BASE('N'))
    bx = d('simprd', [g], bodyx)
    cond = d('simpld', [bx], '( N DChrCond X ) = N')
    ZF = ZFB('S', 'V', 'N', 'X')
    zne = d('simprd', [bx], '%s =/= (/)' % ZF)
    ne0 = d('syl2anc', [d('jca', [nn, n2], '( N e. NN /\\ 2 <_ N )'), d('jca', [xb, cond], '( X e. %s /\\ ( N DChrCond X ) = N )' % BASE('N')), w.inst('dchrprimne1')],
            'X =/= ( 0g ` ( DChr ` N ) )')
    B = BOX('S', 'V')
    LFo = lambda o: '( %s =/= 1 /\\ ( ( N DChrLF X ) ` %s ) = 0 )' % (o, o)
    rn = d('mpbid', [zne, a1(w, A0, 'rabn0', '( %s =/= (/) <-> E. o e. %s %s )' % (ZF, B, LFo('o')))], 'E. o e. %s %s' % (B, LFo('o')))
    eqc = 'o = c'
    idc = w.s([], 'id', '( %s -> %s )' % (eqc, eqc))
    stc, bc_ = w.wcongr(LFo('o'), {'o': 'c'}, eqc, {'o': idc})
    assert bc_ == LFo('c')
    cb = d('mpbid', [rn, a1(w, A0, 'cbvrexvw' if False else 'cbvrexv', '( E. o e. %s %s <-> E. c e. %s %s )' % (B, LFo('o'), B, LFo('c')), [stc])], 'E. c e. %s %s' % (B, LFo('c')))
    C1 = '( ( %s /\\ c e. %s ) /\\ %s )' % (A0, B, LFo('c'))
    c1 = mk(w, C1)
    cin = proj(w, C1, 'c e. %s' % B)
    ic = a1(w, C1, 'ax-icn', '_i e. CC')
    vr1 = lift(w, vr, C1); sr1 = lift(w, sr, C1)
    nv = c1('renegcld', [vr1], '-u V e. RR')
    LO = '( S + ( _i x. -u V ) )'; HI = '( 1 + ( _i x. V ) )'
    loc = c1('addcld', [c1('recnd', [sr1], 'S e. CC'), c1('mulcld', [ic, c1('recnd', [nv], '-u V e. CC')], '( _i x. -u V ) e. CC')], '%s e. CC' % LO)
    hic = c1('addcld', [a1(w, C1, 'ax-1cn', '1 e. CC'), c1('mulcld', [ic, c1('recnd', [vr1], 'V e. CC')], '( _i x. V ) e. CC')], '%s e. CC' % HI)
    el = c1('mpbid', [cin, c1('syl2anc', [loc, hic, w.inst('elcrect')], '( c e. %s <-> ( c e. CC /\\ ( Re ` c ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` c ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (B, LO, HI, LO, HI))],
             '( c e. CC /\\ ( Re ` c ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` c ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (LO, HI, LO, HI))
    cc = c1('simp1d', [el], 'c e. CC')
    one = a1(w, C1, '1re', '1 e. RR')
    rlo = c1('syl2anc', [sr1, nv, w.inst('crre')], '( Re ` %s ) = S' % LO)
    rhi = c1('syl2anc', [one, vr1, w.inst('crre')], '( Re ` %s ) = 1' % HI)
    ilo = c1('syl2anc', [sr1, nv, w.inst('crim')], '( Im ` %s ) = -u V' % LO)
    ihi = c1('syl2anc', [one, vr1, w.inst('crim')], '( Im ` %s ) = V' % HI)
    rin = c1('eleqtrd', [c1('simp2d', [el], '( Re ` c ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (LO, HI)), c1('oveq12d', [rlo, rhi], '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( S [,] 1 )' % (LO, HI))],
             '( Re ` c ) e. ( S [,] 1 )')
    iin = c1('eleqtrd', [c1('simp3d', [el], '( Im ` c ) e. ( ( Im ` %s ) [,] ( Im ` %s ) )' % (LO, HI)), c1('oveq12d', [ilo, ihi], '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( -u V [,] V )' % (LO, HI))],
             '( Im ` c ) e. ( -u V [,] V )')
    re = c1('mpbid', [rin, c1('syl2anc', [sr1, one, w.inst('elicc2')], '( ( Re ` c ) e. ( S [,] 1 ) <-> ( ( Re ` c ) e. RR /\\ S <_ ( Re ` c ) /\\ ( Re ` c ) <_ 1 ) )')],
              '( ( Re ` c ) e. RR /\\ S <_ ( Re ` c ) /\\ ( Re ` c ) <_ 1 )')
    im = c1('mpbid', [iin, c1('syl2anc', [nv, vr1, w.inst('elicc2')], '( ( Im ` c ) e. ( -u V [,] V ) <-> ( ( Im ` c ) e. RR /\\ -u V <_ ( Im ` c ) /\\ ( Im ` c ) <_ V ) )')],
              '( ( Im ` c ) e. RR /\\ -u V <_ ( Im ` c ) /\\ ( Im ` c ) <_ V )')
    rr = c1('simp1d', [re], '( Re ` c ) e. RR'); sre = c1('simp2d', [re], 'S <_ ( Re ` c )'); re1 = c1('simp3d', [re], '( Re ` c ) <_ 1')
    ir = c1('simp1d', [im], '( Im ` c ) e. RR')
    ab = c1('mpbird', [c1('jca', [c1('simp2d', [im], '-u V <_ ( Im ` c )'), c1('simp3d', [im], '( Im ` c ) <_ V')], '( -u V <_ ( Im ` c ) /\\ ( Im ` c ) <_ V )'),
                       c1('syl2anc', [ir, vr1, w.inst('absle')], '( ( abs ` ( Im ` c ) ) <_ V <-> ( -u V <_ ( Im ` c ) /\\ ( Im ` c ) <_ V ) )')], '( abs ` ( Im ` c ) ) <_ V')
    p0 = c1('ltletrd', [a1(w, C1, '0re', '0 e. RR'), sr1, rr, lift(w, s0, C1), sre], '0 < ( Re ` c )')
    hp = hp0(w, C1, 'c', cc, p0)
    c1ne = proj(w, C1, 'c =/= 1'); lf0 = proj(w, C1, '( ( N DChrLF X ) ` c ) = 0')
    CHI = '( ( N e. NN /\\ X e. %s ) /\\ X =/= ( 0g ` ( DChr ` N ) ) )' % BASE('N')
    chi = c1('jca', [c1('jca', [lift(w, nn, C1), lift(w, xb, C1)], NX), lift(w, ne0, C1)], CHI)
    ZE = inst('zc1eord', {'P': 'c'})[1]
    ze = c1('syl2anc', [chi, c1('jca', [hp, c1ne], '( c e. %s /\\ c =/= 1 )' % HP), w.inst('zc1eord')], ZE)
    from c9lib import top_and
    iff = top_and(ZE)[1]
    lfn0 = c1('mpbid', [lf0, c1('simprd', [ze], iff)], '( %s ` c ) = 0' % LFN)
    LZ = LFNZ.replace('z', 'c') if False else None
    eqz = 'z = c'
    idz = w.s([], 'id', '( %s -> %s )' % (eqz, eqz))
    stz, lzc = w.wcongr(LFNZ, {'z': 'c'}, eqz, {'z': idz})
    body = c1('jca', [lfn0, c1('jca', [c1('jca', [sre, re1], '( S <_ ( Re ` c ) /\\ ( Re ` c ) <_ 1 )'), ab], '( ( S <_ ( Re ` c ) /\\ ( Re ` c ) <_ 1 ) /\\ ( abs ` ( Im ` c ) ) <_ V )')], lzc)
    ex_ = c1('syl2anc', [cc, body, w.s([stz], 'rspcev', '( ( c e. CC /\\ %s ) -> E. z e. CC %s )' % (lzc, LFNZ))], 'E. z e. CC %s' % LFNZ)
    rl = d('rexlimdva', [w.s([ex_], 'ex', '( ( %s /\\ c e. %s ) -> ( %s -> E. z e. CC %s ) )' % (A0, B, LFo('c'), LFNZ))], '( E. c e. %s %s -> E. z e. CC %s )' % (B, LFo('c'), LFNZ))
    ez = d('mpd', [cb, rl], 'E. z e. CC %s' % LFNZ)
    fin = d('jca', [d('jca', [xb, ne0], '( X e. %s /\\ X =/= ( 0g ` ( DChr ` N ) ) )' % BASE('N')), ez], C0)
    w.qed([fin], 'idi', S['cmzero'])
    return run(w, only)


def gen_det():
    from lin import linarith, nlinarith
    w = W('cmdet', 'THE DETECTION WINDOW (the Phi-trick): a bad character mod ` N ` with ` 2 <_ N <_ W ` detects on every height of a window of width ` 2 D ` around the ordinate of its zero, so ` 2 D <_ E ^ 3 M exp ( 6 M ) S. ( -u ( V + 1 ) , V + 1 ) S. ( X1 , X2 ) abs ( PWS ( t , X1 , u ) ) ^ 2 / u _d u _d t ` ( ~ kd2det , ~ cmzero , ~ itgle , ~ itgless ; Lean ` perchar_window ` ).')
    A0, C0 = split_imp(S['cmdet'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    nn = g('N e. NN'); n2 = g('2 <_ N'); sr = g('S e. RR'); vr = g('V e. RR'); wr = g('W e. RR'); s0 = g('0 < S'); s1 = g('S <_ 1')
    nw = g('N <_ W'); v3 = g('( V + 3 ) <_ W'); ep = g('E e. RR+'); e5 = g('E <_ %s' % R5000); e12 = g('1 <_ ( ( ; 1 2 x. E ) x. %s )' % LW)
    dp = g('D e. RR+'); d1 = g('D <_ 1'); dist = g('( ( ( 1 - S ) ^ 2 ) + ( D ^ 2 ) ) <_ ( E ^ 2 )')
    BCN = BC('S', 'V', 'N')
    zh = d('jca', [d('jca', [d('jca', [nn, n2], '( N e. NN /\\ 2 <_ N )'), g('X e. %s' % BCN)], '( ( N e. NN /\\ 2 <_ N ) /\\ X e. %s )' % BCN),
                   d('jca', [d('jca', [sr, s0], '( S e. RR /\\ 0 < S )'), vr], '( ( S e. RR /\\ 0 < S ) /\\ V e. RR )')], split_imp(S['cmzero'])[0])
    zer = d('syl', [zh, w.inst('cmzero')], split_imp(S['cmzero'])[1])
    xbn = d('simpld', [zer], '( X e. %s /\\ X =/= ( 0g ` ( DChr ` N ) ) )' % BASE('N'))
    xb = d('simpld', [xbn], 'X e. %s' % BASE('N')); ne0 = d('simprd', [xbn], 'X =/= ( 0g ` ( DChr ` N ) )')
    exz = d('simprd', [zer], 'E. z e. CC %s' % LFNZ)
    nx = d('jca', [nn, xb], NX)
    er = d('rpred', [ep], 'E e. RR'); dr = d('rpred', [dp], 'D e. RR')
    c0 = Closure(w, A0, {'N': ('NN', nn), 'S': ('RR', sr), 'V': ('RR', vr), 'W': ('RR', wr), 'E': ('RR+', ep), 'D': ('RR+', dp)})
    w1 = linarith(w, A0, [nw, linarith(w, A0, [n2], '1 <_ N', closure=c0)], '1 <_ W', closure=c0)
    lw0 = d('syl2anc', [wr, w1, w.inst('logge0')], '0 <_ %s' % LW)
    lwr = d('syl', [d('jca', [wr, linarith(w, A0, [w1], '0 < W', closure=c0)], '( W e. RR /\\ 0 < W )'), w.inst('elrp')], 'W e. RR+') if False else None
    wp = d('elrpd', [wr, linarith(w, A0, [w1], '0 < W', closure=c0)], 'W e. RR+')
    lwr_ = d('relogcld', [wp], '%s e. RR' % LW)
    kx = d('syl3anc', [ep, lwr_, lw0, w.inst('kdxlt')], '( %s e. NN /\\ %s < %s )' % (MW, X1, X2))
    mn = d('simpld', [kx], '%s e. NN' % MW); x12 = d('simprd', [kx], '%s < %s' % (X1, X2))
    mr = d('nnred', [mn], '%s e. RR' % MW)
    ex1 = d('redivcld', [mr, d('remulcld', [a1(w, A0, '1nn0' if False else 'nnrei', '; 1 6 e. RR', [w.s([], '1nn0' if False else 'dec1nn' if False else 'id', 'x')]) if False else d('id' if False else 'eqid' if False else 'a1i', [w.s([], '1nn0' if False else '6nn0' if False else 'id', 'x')], 'x') if False else c0.mem('; 1 6', 'RR'), er], '( ; 1 6 x. E ) e. RR'),
                         d('gt0ne0d', [d('mulgt0d' if False else 'remulcld' if False else 'mulgt0d', [c0.mem('; 1 6', 'RR'), er, c0.gt0('; 1 6'), d('rpgt0d', [ep], '0 < E')], '0 < ( ; 1 6 x. E )')], '( ; 1 6 x. E ) =/= 0')],
                '( %s / ( ; 1 6 x. E ) ) e. RR' % MW)
    x1p = d('rpefcld', [ex1], '%s e. RR+' % X1)
    x1r = d('rpred', [x1p], '%s e. RR' % X1)
    ex2 = d('redivcld', [d('remulcld', [c0.mem('; 1 6', 'RR'), mr], '( ; 1 6 x. %s ) e. RR' % MW), er, d('rpne0d', [ep], 'E =/= 0')], '( ( ; 1 6 x. %s ) / E ) e. RR' % MW)
    x2r = d('reefcld', [ex2], '%s e. RR' % X2)
    x12l = d('ltled', [x1r, x2r, x12], '%s <_ %s' % (X1, X2))
    TT = '( -u %s (,) %s )' % (V1, V1)
    v1r = d('peano2red' if False else 'readdcld', [vr, a1(w, A0, '1re', '1 e. RR')], '%s e. RR' % V1)
    SWP = inst('cmswp', {'H': V1, 'Y': X1, 'Z': X2})
    sw = d('syl3anc', [nx, v1r, d('3jca', [x1p, x2r, x12l], '( %s e. RR+ /\\ %s e. RR /\\ %s <_ %s )' % (X1, X2, X1, X2)), w.inst('cmswp')], SWP[1])
    IIT = II('t', X1, X2)
    ibt = d('simp1d', [sw], '( t e. %s |-> %s ) e. L^1' % (TT, IIT))
    # II real and nonnegative on TT
    At = '( %s /\\ t e. %s )' % (A0, TT)
    at = mk(w, At)
    tr = at('syl', [w.s([], 'simpr', '( %s -> t e. %s )' % (At, TT)), w.inst('elioore')], 't e. RR')
    ibu = at('syl3anc', [lift(w, nx, At), tr, lift(w, d('3jca', [x1p, x2r, x12l], '( %s e. RR+ /\\ %s e. RR /\\ %s <_ %s )' % (X1, X2, X1, X2)), At), w.inst('kd2ibl')],
             inst('kd2ibl', {'T': 't', 'Y': X1, 'Z': X2})[1])
    YZ = '( %s (,) %s )' % (X1, X2)
    Au = '( %s /\\ u e. %s )' % (At, YZ)
    au = mk(w, Au)
    ug = au('mpbid', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, YZ)), au('syl2anc', [au('rexrd', [lift(w, x1r, Au)], '%s e. RR*' % X1), au('rexrd', [lift(w, x2r, Au)], '%s e. RR*' % X2), w.inst('elioo2')],
                                                                              '( u e. %s <-> ( u e. RR /\\ %s < u /\\ u < %s ) )' % (YZ, X1, X2))], '( u e. RR /\\ %s < u /\\ u < %s )' % (X1, X2))
    ur = au('simp1d', [ug], 'u e. RR')
    upos = au('lttrd', [a1(w, Au, '0re', '0 e. RR'), lift(w, x1r, Au), ur, au('rpgt0d', [lift(w, x1p, Au)], '0 < %s' % X1), au('simp2d', [ug], '%s < u' % X1)], '0 < u')
    PWU = PWS('t', X1, 'u')
    import cm_c
    PSU = PSET(X1, 'u')
    Aup = '( %s /\\ p e. %s )' % (Au, PSU)
    nnp = cm_c.psmem(w, Aup, 'p', X1, 'u')[0]
    cpc = cm_c.cpin(w, Aup, lift(w, nx, Aup), 'p', nnp, lift(w, tr, Aup))
    pfu = au('ssfid', [au('fzfid', [], '( 1 ... ( |_ ` u ) ) e. Fin'), a1(w, Au, 'ssrab2', '%s C_ ( 1 ... ( |_ ` u ) )' % PSU)], '%s e. Fin' % PSU)
    pwc = au('fsumcl', [pfu, cpc], '%s e. CC' % PWU)
    ab = au('abscld', [pwc], '( abs ` %s ) e. RR' % PWU)
    INT = '( %s / u )' % ABS2(PWU)
    irr = au('redivcld', [au('resqcld', [ab], '%s e. RR' % ABS2(PWU)), ur, au('gt0ne0d', [upos], 'u =/= 0')], '%s e. RR' % INT)
    ig0 = au('divge0d' if False else 'divge0d', [au('resqcld', [ab], '%s e. RR' % ABS2(PWU)), au('elrpd', [ur, upos], 'u e. RR+'), au('sqge0d', [ab], '0 <_ %s' % ABS2(PWU))], '0 <_ %s' % INT)
    iir = at('itgrecl', [irr, ibu], '%s e. RR' % IIT)
    ii0 = at('itgge0', [ibu, irr, ig0], '0 <_ %s' % IIT)
    CD = CDET
    c0.have(MW, 'NN', mn)
    cr = c0.mem(CD, 'RR'); cge = c0.ge0(CD)
    cii = at('remulcld', [lift(w, cr, At), iir], '( %s x. %s ) e. RR' % (CD, IIT))
    cii0 = at('mulge0d', [lift(w, cr, At), iir, lift(w, cge, At), ii0], '0 <_ ( %s x. %s )' % (CD, IIT))
    ibc = d('iblmulc2', [d('recnd', [cr], '%s e. CC' % CD), at('recnd', [iir], '%s e. CC' % IIT), ibt], '( t e. %s |-> ( %s x. %s ) ) e. L^1' % (TT, CD, IIT))
    # the zero
    C1 = '( ( %s /\\ z e. CC ) /\\ %s )' % (A0, LFNZ)
    c1 = mk(w, C1)
    L1 = lambda s_: lift(w, s_, C1)
    zc = proj(w, C1, 'z e. CC')
    lf0 = proj(w, C1, '( %s ` z ) = 0' % LFN)
    srz = proj(w, C1, 'S <_ ( Re ` z )'); rz1 = proj(w, C1, '( Re ` z ) <_ 1'); aim = proj(w, C1, '( abs ` ( Im ` z ) ) <_ V')
    rzr = c1('recld', [zc], '( Re ` z ) e. RR'); izr = c1('imcld', [zc], '( Im ` z ) e. RR')
    G = '( Im ` z )'
    imb = c1('mpbid', [aim, c1('syl2anc', [izr, L1(vr), w.inst('absle')], '( ( abs ` %s ) <_ V <-> ( -u V <_ %s /\\ %s <_ V ) )' % (G, G, G))], '( -u V <_ %s /\\ %s <_ V )' % (G, G))
    iml = c1('simpld', [imb], '-u V <_ %s' % G); imu = c1('simprd', [imb], '%s <_ V' % G)
    cc1 = Closure(w, C1, {'S': ('RR', L1(sr)), 'V': ('RR', L1(vr)), 'W': ('RR', L1(wr)), 'E': ('RR+', L1(ep)), 'D': ('RR+', L1(dp)), G: ('RR', izr), '( Re ` z )': ('RR', rzr)})
    LOW = '( %s - D )' % G; HIG = '( %s + D )' % G
    WD = '( %s (,) %s )' % (LOW, HIG)
    lor = cc1.mem(LOW, 'RR'); hir = cc1.mem(HIG, 'RR')
    l1 = linarith(w, C1, [iml, L1(d1)], '-u %s <_ %s' % (V1, LOW), closure=cc1)
    h1 = linarith(w, C1, [imu, L1(d1)], '%s <_ %s' % (HIG, V1), closure=cc1)
    sub = c1('syl2anc', [c1('jca', [c1('rexrd', [cc1.mem('-u %s' % V1, 'RR')], '-u %s e. RR*' % V1), c1('rexrd', [cc1.mem(V1, 'RR')], '%s e. RR*' % V1)], '( -u %s e. RR* /\\ %s e. RR* )' % (V1, V1)),
                         c1('jca', [l1, h1], '( -u %s <_ %s /\\ %s <_ %s )' % (V1, LOW, HIG, V1)), w.inst('ioossioo')], '%s C_ %s' % (WD, TT))
    wdm = a1(w, C1, 'ioombl', '%s e. dom vol' % WD)
    C1t = '( %s /\\ t e. %s )' % (C1, TT)
    ciic = rean(w, at('recnd', [cii], '( %s x. %s ) e. CC' % (CD, IIT)), C1t)
    ibw = c1('iblss', [sub, wdm, ciic, L1(ibc)], '( t e. %s |-> ( %s x. %s ) ) e. L^1' % (WD, CD, IIT))
    lehi = linarith(w, C1, [L1(dp) if False else c1('rpge0d', [L1(dp)], '0 <_ D')], '%s <_ %s' % (LOW, HIG), closure=cc1)
    vw = c1('syl3anc', [lor, hir, lehi, w.inst('volioo')], '( vol ` %s ) = ( %s - %s )' % (WD, HIG, LOW))
    vwr = c1('eqeltrd', [vw, cc1.mem('( %s - %s )' % (HIG, LOW), 'RR')], '( vol ` %s ) e. RR' % WD)
    ib1 = c1('eqeltrd', [a1(w, C1, 'fconstmpt', '( t e. %s |-> 1 ) = ( %s X. { 1 } )' % (WD, WD)) if False else c1('eqcomd', [a1(w, C1, 'fconstmpt', '( %s X. { 1 } ) = ( t e. %s |-> 1 )' % (WD, WD))], '( t e. %s |-> 1 ) = ( %s X. { 1 } )' % (WD, WD)),
                         c1('syl3anc', [wdm, vwr, a1(w, C1, 'ax-1cn', '1 e. CC'), w.inst('iblconst')], '( %s X. { 1 } ) e. L^1' % WD)], '( t e. %s |-> 1 ) e. L^1' % WD)
    # pointwise detection on the window
    C2 = '( %s /\\ t e. %s )' % (C1, WD)
    c2 = mk(w, C2)
    L2 = lambda s_: lift(w, s_, C2)
    tg = c2('mpbid', [w.s([], 'simpr', '( %s -> t e. %s )' % (C2, WD)), c2('syl2anc', [c2('rexrd', [L2(lor)], '%s e. RR*' % LOW), c2('rexrd', [L2(hir)], '%s e. RR*' % HIG), w.inst('elioo2')],
                                                                              '( t e. %s <-> ( t e. RR /\\ %s < t /\\ t < %s ) )' % (WD, LOW, HIG))], '( t e. RR /\\ %s < t /\\ t < %s )' % (LOW, HIG))
    tr2 = c2('simp1d', [tg], 't e. RR'); tl = c2('simp2d', [tg], '%s < t' % LOW); th = c2('simp3d', [tg], 't < %s' % HIG)
    cc2 = Closure(w, C2, {'S': ('RR', L2(sr)), 'V': ('RR', L2(vr)), 'W': ('RR', L2(wr)), 'E': ('RR+', L2(ep)), 'D': ('RR+', L2(dp)), G: ('RR', L2(izr)), '( Re ` z )': ('RR', L2(rzr)), 't': ('RR', tr2)})
    ta = c2('mpbird', [c2('jca', [linarith(w, C2, [tl, L2(iml), L2(d1)], '-u %s <_ t' % V1, closure=cc2), linarith(w, C2, [th, L2(imu), L2(d1)], 't <_ %s' % V1, closure=cc2)], '( -u %s <_ t /\\ t <_ %s )' % (V1, V1)),
                       c2('syl2anc', [tr2, cc2.mem(V1, 'RR'), w.inst('absle')], '( ( abs ` t ) <_ %s <-> ( -u %s <_ t /\\ t <_ %s ) )' % (V1, V1, V1))], '( abs ` t ) <_ %s' % V1)
    cc2.have('( abs ` t )', 'RR', c2('recnd' if False else 'abscld', [c2('recnd', [tr2], 't e. CC')], '( abs ` t ) e. RR')); cc2.atom('( abs ` t )')
    t2w = linarith(w, C2, [ta, L2(v3)], '( ( abs ` t ) + 2 ) <_ W', closure=cc2)
    ONE = '( 1 + ( _i x. t ) )'
    WW = '( z - %s )' % ONE
    onec = c2('addcld', [a1(w, C2, 'ax-1cn', '1 e. CC'), c2('mulcld', [a1(w, C2, 'ax-icn', '_i e. CC'), c2('recnd', [tr2], 't e. CC')], '( _i x. t ) e. CC')], '%s e. CC' % ONE)
    wwc = c2('subcld', [L2(zc), onec], '%s e. CC' % WW)
    rw = c2('eqtrd', [c2('resubd', [L2(zc), onec], '( Re ` %s ) = ( ( Re ` z ) - ( Re ` %s ) )' % (WW, ONE)),
                      c2('oveq2d', [c2('syl2anc', [a1(w, C2, '1re', '1 e. RR'), tr2, w.inst('crre')], '( Re ` %s ) = 1' % ONE)], '( ( Re ` z ) - ( Re ` %s ) ) = ( ( Re ` z ) - 1 )' % ONE)],
             '( Re ` %s ) = ( ( Re ` z ) - 1 )' % WW)
    iw = c2('eqtrd', [c2('imsubd', [L2(zc), onec], '( Im ` %s ) = ( %s - ( Im ` %s ) )' % (WW, G, ONE)),
                      c2('oveq2d', [c2('syl2anc', [a1(w, C2, '1re', '1 e. RR'), tr2, w.inst('crim')], '( Im ` %s ) = t' % ONE)], '( %s - ( Im ` %s ) ) = ( %s - t )' % (G, ONE, G))],
             '( Im ` %s ) = ( %s - t )' % (WW, G))
    RW = '( Re ` %s )' % WW; IW = '( Im ` %s )' % WW
    rwr = c2('recld', [wwc], '%s e. RR' % RW); iwr = c2('imcld', [wwc], '%s e. RR' % IW)
    rl = c2('replimd', [wwc], '%s = ( %s + ( _i x. %s ) )' % (WW, RW, IW))
    a2 = c2('eqtrd', [c2('oveq1d', [c2('fveq2d', [rl], '( abs ` %s ) = ( abs ` ( %s + ( _i x. %s ) ) )' % (WW, RW, IW))], '( ( abs ` %s ) ^ 2 ) = ( ( abs ` ( %s + ( _i x. %s ) ) ) ^ 2 )' % (WW, RW, IW)),
                      c2('syl2anc', [rwr, iwr, w.inst('absreimsq')], '( ( abs ` ( %s + ( _i x. %s ) ) ) ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (RW, IW, RW, IW))],
             '( ( abs ` %s ) ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (WW, RW, IW))
    r2 = c2('oveq1d', [rw], '( %s ^ 2 ) = ( ( ( Re ` z ) - 1 ) ^ 2 )' % RW)
    i2 = c2('oveq1d', [iw], '( %s ^ 2 ) = ( ( %s - t ) ^ 2 )' % (IW, G))
    rb = nlinarith(w, C2, [L2(srz), L2(rz1), L2(s1)], '( ( ( Re ` z ) - 1 ) ^ 2 ) <_ ( ( 1 - S ) ^ 2 )', closure=cc2)
    ib_ = nlinarith(w, C2, [tl, th], '( ( %s - t ) ^ 2 ) <_ ( D ^ 2 )' % G, closure=cc2)
    for at_ in ('( ( abs ` %s ) ^ 2 )' % WW, '( %s ^ 2 )' % RW, '( %s ^ 2 )' % IW, '( ( ( Re ` z ) - 1 ) ^ 2 )', '( ( %s - t ) ^ 2 )' % G, '( ( 1 - S ) ^ 2 )', '( D ^ 2 )', '( E ^ 2 )'):
        cc2.atom(at_)
    cc2.have('( ( abs ` %s ) ^ 2 )' % WW, 'RR', c2('resqcld', [c2('abscld', [wwc], '( abs ` %s ) e. RR' % WW)], '( ( abs ` %s ) ^ 2 ) e. RR' % WW))
    cc2.have('( %s ^ 2 )' % RW, 'RR', c2('resqcld', [rwr], '( %s ^ 2 ) e. RR' % RW)); cc2.have('( %s ^ 2 )' % IW, 'RR', c2('resqcld', [iwr], '( %s ^ 2 ) e. RR' % IW))
    ww2 = linarith(w, C2, [a2, r2, i2, rb, ib_, L2(dist)], '( ( abs ` %s ) ^ 2 ) <_ ( E ^ 2 )' % WW, closure=cc2)
    awr = c2('abscld', [wwc], '( abs ` %s ) e. RR' % WW)
    wle = c2('mpbird', [ww2, c2('syl2anc', [c2('jca', [awr, c2('absge0d', [wwc], '0 <_ ( abs ` %s )' % WW)], '( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) )' % (WW, WW)),
                                          c2('jca', [L2(er), c2('rpge0d', [L2(ep)], '0 <_ E')], '( E e. RR /\\ 0 <_ E )'), w.inst('le2sq')],
                                  '( ( abs ` %s ) <_ E <-> ( ( abs ` %s ) ^ 2 ) <_ ( E ^ 2 ) )' % (WW, WW))], '( abs ` %s ) <_ E' % WW)
    ZP = '( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E )' % (LFN, ONE)
    eqp = 'p = z'
    idp = w.s([], 'id', '( %s -> %s )' % (eqp, eqp))
    stp, zpz = w.wcongr(ZP, {'p': 'z'}, eqp, {'p': idp})
    exp_ = c2('syl2anc', [L2(zc), c2('jca', [L2(lf0), wle], zpz), w.s([stp], 'rspcev', '( ( z e. CC /\\ %s ) -> E. p e. CC %s )' % (zpz, ZP))], 'E. p e. CC %s' % ZP)
    KH, KC = inst('kd2det', {'T': 't', 'Y': 'W'})
    CHI = '( ( N e. NN /\\ X e. %s ) /\\ X =/= ( 0g ` ( DChr ` N ) ) )' % BASE('N')
    kh = c2('jca', [c2('3jca', [c2('jca', [L2(nx), L2(ne0)], CHI), c2('jca', [tr2, L2(wr)], '( t e. RR /\\ W e. RR )'), c2('jca', [L2(nw), t2w], '( N <_ W /\\ ( ( abs ` t ) + 2 ) <_ W )')],
                               '( %s /\\ ( t e. RR /\\ W e. RR ) /\\ ( N <_ W /\\ ( ( abs ` t ) + 2 ) <_ W ) )' % CHI),
                    c2('3jca', [c2('jca', [L2(ep), L2(e5)], '( E e. RR+ /\\ E <_ %s )' % R5000), L2(e12), exp_], '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ E. p e. CC %s )' % (R5000, LW, ZP))], KH)
    det = c2('syl', [kh, w.inst('kd2det')], KC)
    assert KC == '1 <_ ( %s x. %s )' % (CD, IIT), KC
    # integrate over the window
    CI = '( %s x. %s )' % (CD, IIT)
    ciw = rean(w, cii, C2) if False else rean(w, at('id', [cii], '( %s x. %s ) e. RR' % (CD, IIT)) if False else cii, '( %s /\\ t e. %s )' % (C1, TT))
    ciw2 = c2('ssseldd' if False else 'id', [], 'x') if False else None
    tTT = c2('sseldd', [L2(sub), w.s([], 'simpr', '( %s -> t e. %s )' % (C2, WD))], 't e. %s' % TT)
    ciR = c2('syl2anc' if False else 'mpd', [tTT, lift(w, w.s([ciw], 'ex', '( %s -> ( t e. %s -> %s e. RR ) )' % (C1, TT, CI)), C2)], '%s e. RR' % CI)
    ile = c1('itgle', [ib1, ibw, a1(w, C2, '1re', '1 e. RR'), ciR, det], 'S. %s 1 _d t <_ S. %s %s _d t' % (WD, WD, CI))
    ic = c1('syl3anc', [wdm, vwr, a1(w, C1, 'ax-1cn', '1 e. CC'), w.inst('itgconst')], 'S. %s 1 _d t = ( 1 x. ( vol ` %s ) )' % (WD, WD))
    ic2 = c1('eqtrd', [ic, c1('eqtrd', [c1('mullidd', [c1('recnd', [vwr], '( vol ` %s ) e. CC' % WD)], '( 1 x. ( vol ` %s ) ) = ( vol ` %s )' % (WD, WD)), vw], '( 1 x. ( vol ` %s ) ) = ( %s - %s )' % (WD, HIG, LOW))],
               'S. %s 1 _d t = ( %s - %s )' % (WD, HIG, LOW))
    cc1.atom('S. %s 1 _d t' % WD)
    ciTT = rean(w, cii, C1t); ci0TT = rean(w, cii0, C1t)
    ils = c1('itgless', [sub, wdm, ciTT, ci0TT, L1(ibc)], 'S. %s %s _d t <_ S. %s %s _d t' % (WD, CI, TT, CI))
    im = d('itgmulc2', [d('recnd', [cr], '%s e. CC' % CD), at('recnd', [iir], '%s e. CC' % IIT), ibt], '( %s x. S. %s %s _d t ) = S. %s %s _d t' % (CD, TT, IIT, TT, CI))
    I1 = 'S. %s 1 _d t' % WD; IW_ = 'S. %s %s _d t' % (WD, CI); IT_ = 'S. %s %s _d t' % (TT, CI)
    cc1.have(I1, 'RR', c1('eqeltrd', [ic2, cc1.mem('( %s - %s )' % (HIG, LOW), 'RR')], '%s e. RR' % I1))
    cc1.have(IW_, 'RR', c1('itgrecl', [ciR if False else rean(w, cii, '( %s /\\ t e. %s )' % (C1, WD)) if False else c2('id', [ciR], '%s e. RR' % CI) if False else ciR, ibw], '%s e. RR' % IW_)) if False else None
    iwr_ = c1('itgrecl', [ciR, ibw], '%s e. RR' % IW_)
    itr_ = c1('itgrecl', [ciTT, L1(ibc)], '%s e. RR' % IT_)
    cc1.have(IW_, 'RR', iwr_); cc1.have(IT_, 'RR', itr_)
    for at_ in (I1, IW_, IT_):
        cc1.atom(at_)
    from lin import lineq
    e0 = lineq(w, C1, '( 2 x. D )', '( %s - %s )' % (HIG, LOW), closure=cc1)
    sa = c1('eqtrd', [e0, c1('eqcomd', [ic2], '( %s - %s ) = %s' % (HIG, LOW, I1))], '( 2 x. D ) = %s' % I1)
    le1 = c1('eqbrtrd', [sa, ile], '( 2 x. D ) <_ %s' % IW_)
    le2 = c1('letrd', [cc1.mem('( 2 x. D )', 'RR'), iwr_, itr_, le1, ils], '( 2 x. D ) <_ %s' % IT_)
    fin1 = c1('breqtrrd', [le2, L1(im)], '( 2 x. D ) <_ ( %s x. S. %s %s _d t )' % (CD, TT, IIT))
    rl_ = d('rexlimdva', [w.s([fin1], 'ex', '( ( %s /\\ z e. CC ) -> ( %s -> %s ) )' % (A0, LFNZ, C0))], '( E. z e. CC %s -> %s )' % (LFNZ, C0))
    fin = d('mpd', [exz, rl_], C0)
    w.qed([fin], 'idi', S['cmdet'])
    return run(w, only)


if __name__ == '__main__':
    gen_zero()
    gen_det()
