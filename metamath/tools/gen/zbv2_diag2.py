"""Sortie ZBV2, section 4 part B: the Selberg diagonalisation for a generic weight L vanishing on
non-squarefree indices (Lean sum_lcm_eq_sum_phiSig_Ssum_sq, lcm_rpow_neg_eq, filter_dvd_eq_divisors_gcd).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbv2lib import *
import num
import lin
lin.MAXDEG = 5
from zbv2_phisg import prfacts
from zbv2_diag1 import lcmnn

PH = 'ph'


def phsre(w, ante, mnn, sr, m):
    """( ante -> PHS(S,m) e. RR ) from m e. NN, S e. RR"""
    AP = '( %s /\\ p e. %s )' % (ante, PRF(m)); sp = mkst(w, AP)
    pf = prfacts(w, AP, sp([], 'simpr', 'p e. %s' % PRF(m)), m)
    ps = sp([sp([pf['rp'], lift(w, sr, AP)], 'rpcxpcld', '( p ^c S ) e. RR+')], 'rpred', '( p ^c S ) e. RR')
    m1 = sp([ps, sp([], '1red', '1 e. RR')], 'resubcld', '( ( p ^c S ) - 1 ) e. RR')
    return w.s([sy(w, ante, mnn, 'pffinq', '%s e. Fin' % PRF(m)), m1], 'fprodrecl', '( %s -> %s e. RR )' % (ante, PHS('S', m)))


def bvlcmcxp():
    w = W('bvlcmcxp', 'lcm ( D , E )^-S = gcd ( D , E )^S D^-S E^-S (Lean lcm_rpow_neg_eq; lcmgcd, mulcxp).')
    A = '( ( D e. NN /\\ E e. NN ) /\\ S e. RR )'
    st = mkst(w, A)
    dnn = st([], 'simpll', 'D e. NN'); enn = st([], 'simplr', 'E e. NN'); sr = st([], 'simpr', 'S e. RR')
    ns = st([sr], 'renegcld', '-u S e. RR'); nsc = st([ns], 'recnd', '-u S e. CC')
    g = '( D gcd E )'; l = '( D lcm E )'
    gnn = st([dnn, enn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % g)
    lnn = lcmnn(w, A, dnn, enn, 'D', 'E')
    dz = st([dnn], 'nnzd', 'D e. ZZ'); ez = st([enn], 'nnzd', 'E e. ZZ')
    lg = st([dz, ez, w.inst('lcmgcd')], 'syl2anc', '( %s x. %s ) = ( abs ` ( D x. E ) )' % (l, g))
    de = st([dnn, enn], 'nnmulcld', '( D x. E ) e. NN')
    ab = st([st([de], 'nnred', '( D x. E ) e. RR'), st([st([de], 'nnrpd', '( D x. E ) e. RR+')], 'rpge0d', '0 <_ ( D x. E )')], 'absidd', '( abs ` ( D x. E ) ) = ( D x. E )')
    lgde = st([lg, ab], 'eqtrd', '( %s x. %s ) = ( D x. E )' % (l, g))
    def rge(nn, x):
        return st([nn], 'nnred', '%s e. RR' % x), st([st([nn], 'nnrpd', '%s e. RR+' % x)], 'rpge0d', '0 <_ %s' % x)
    lr, l0 = rge(lnn, l); gr, g0 = rge(gnn, g); drr, d0 = rge(dnn, 'D'); er, e0 = rge(enn, 'E')
    m1 = st([lr, l0, gr, g0, nsc], 'mulcxpd', '( ( %s x. %s ) ^c -u S ) = ( ( %s ^c -u S ) x. ( %s ^c -u S ) )' % (l, g, l, g))
    m2 = st([drr, d0, er, e0, nsc], 'mulcxpd', '( ( D x. E ) ^c -u S ) = ( ( D ^c -u S ) x. ( E ^c -u S ) )')
    e1 = st([lgde], 'oveq1d', '( ( %s x. %s ) ^c -u S ) = ( ( D x. E ) ^c -u S )' % (l, g))
    key = eqtr(w, A, [st([m1], 'eqcomd', '( ( %s ^c -u S ) x. ( %s ^c -u S ) ) = ( ( %s x. %s ) ^c -u S )' % (l, g, l, g)), e1, m2], None)
    def cc(nn, x, e):
        return st([st([st([nn], 'nnrpd', '%s e. RR+' % x), e], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (x, 'S' if e == sr else '-u S'))], 'rpcnd',
                  '( %s ^c %s ) e. CC' % (x, 'S' if e == sr else '-u S'))
    gsc = cc(gnn, g, sr); gnsc = cc(gnn, g, ns); lnsc = cc(lnn, l, ns)
    gsne = st([st([st([gnn], 'nnrpd', '%s e. RR+' % g), sr], 'rpcxpcld', '( %s ^c S ) e. RR+' % g)], 'rpne0d', '( %s ^c S ) =/= 0' % g)
    GS_, GN, LN = '( %s ^c S )' % g, '( %s ^c -u S )' % g, '( %s ^c -u S )' % l
    neg = st([st([gnn], 'nncnd', '%s e. CC' % g), st([st([gnn], 'nnrpd', '%s e. RR+' % g)], 'rpne0d', '%s =/= 0' % g), st([sr], 'recnd', 'S e. CC')], 'cxpnegd',
             '%s = ( 1 / %s )' % (GN, GS_))
    one = st([st([neg], 'oveq2d', '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (GS_, GN, GS_, GS_)), st([gsc, gsne], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (GS_, GS_))], 'eqtrd',
             '( %s x. %s ) = 1' % (GS_, GN))
    r = eqtr(w, A, [st([st([key], 'eqcomd', '( ( D ^c -u S ) x. ( E ^c -u S ) ) = ( %s x. %s )' % (LN, GN))], 'oveq2d',
                       '( %s x. ( ( D ^c -u S ) x. ( E ^c -u S ) ) ) = ( %s x. ( %s x. %s ) )' % (GS_, GS_, LN, GN)),
                    st([gsc, lnsc, gnsc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (GS_, LN, GN, LN, GS_, GN)),
                    st([one], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. 1 )' % (LN, GS_, GN, LN)),
                    st([lnsc], 'mulridd', '( %s x. 1 ) = %s' % (LN, LN))], None)
    w.qed([r], 'eqcomd', STATEMENTS['bvlcmcxp'])
    return w


def bvdiagsum():
    w = W('bvdiagsum', 'sum_ m <= N [ m | D /\\ m | E ] phiSig ( m ) = gcd ( D , E )^S for squarefree D, E <= N '
                       '(Lean filter_dvd_eq_divisors_gcd with sum_divisors_phiSig).')
    A = '( ( S e. RR /\\ N e. NN ) /\\ ( ( D e. ( 1 ... N ) /\\ E e. ( 1 ... N ) ) /\\ ( ( mmu ` D ) =/= 0 /\\ ( mmu ` E ) =/= 0 ) ) )'
    st = mkst(w, A)
    sr = st([], 'simpll', 'S e. RR'); nnn = st([], 'simplr', 'N e. NN')
    dfz = st([], 'simprll', 'D e. ( 1 ... N )'); efz = st([], 'simprlr', 'E e. ( 1 ... N )')
    mud = st([], 'simprrl', '( mmu ` D ) =/= 0')
    dnn = sy(w, A, dfz, 'elfznn', 'D e. NN'); enn = sy(w, A, efz, 'elfznn', 'E e. NN')
    dz = st([dnn], 'nnzd', 'D e. ZZ'); ez = st([enn], 'nnzd', 'E e. ZZ'); nz = st([nnn], 'nnzd', 'N e. ZZ')
    g = '( D gcd E )'
    gnn = st([dnn, enn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % g)
    gd = st([st([dz, ez, w.inst('gcddvds')], 'syl2anc', '( %s || D /\\ %s || E )' % (g, g))], 'simpld', '%s || D' % g)
    mug = st([mud, w.s([bind3(w, A, dnn, gnn, gd, 'D e. NN', '%s e. NN' % g, '%s || D' % g), w.inst('dvdssqf')], 'syl', '( %s -> ( ( mmu ` D ) =/= 0 -> ( mmu ` %s ) =/= 0 ) )' % (A, g))],
             'mpd', '( mmu ` %s ) =/= 0' % g)
    gle = st([gd, st([st([gnn], 'nnzd', '%s e. ZZ' % g), dnn, w.inst('dvdsle')], 'syl2anc', '( %s || D -> %s <_ D )' % (g, g))], 'mpd', '%s <_ D' % g)
    dle = sy(w, A, dfz, 'elfzle2', 'D <_ N')
    DVg = DV(g)
    COND = lambda m: '( %s || D /\\ %s || E )' % (m, m)
    IFC = lambda m: 'if ( %s , %s , 0 )' % (COND(m), PHS('S', m))
    # DVg C_ ( 1 ... N )
    AY = '( %s /\\ y e. %s )' % (A, DVg); sy_ = mkst(w, AY)
    suby = w.s([], 'breq1', '( x = y -> ( x || %s <-> y || %s ) )' % (g, g))
    ely = w.s([suby], 'elrab', '( y e. %s <-> ( y e. NN /\\ y || %s ) )' % (DVg, g))
    yb = sy_([sy_([], 'simpr', 'y e. %s' % DVg), ely], 'sylib', '( y e. NN /\\ y || %s )' % g)
    ynn = sy_([yb], 'simpld', 'y e. NN'); ydv = sy_([yb], 'simprd', 'y || %s' % g)
    yle = sy_([ydv, sy_([sy_([ynn], 'nnzd', 'y e. ZZ'), lift(w, gnn, AY), w.inst('dvdsle')], 'syl2anc', '( y || %s -> y <_ %s )' % (g, g))], 'mpd', 'y <_ %s' % g)
    yre = sy_([ynn], 'nnred', 'y e. RR')
    ylen = linarith(w, AY, [yle, lift(w, gle, AY), lift(w, dle, AY)], 'y <_ N', leaves={'y': yre, g: lift(w, st([gnn], 'nnred', '%s e. RR' % g), AY),
                                                                                    'D': lift(w, st([dnn], 'nnred', 'D e. RR'), AY), 'N': lift(w, st([nnn], 'nnred', 'N e. RR'), AY)})
    yfz = sy_([sy_([ynn, ylen], 'jca', '( y e. NN /\\ y <_ N )'), sy(w, AY, lift(w, nz, AY), 'fznn', '( y e. ( 1 ... N ) <-> ( y e. NN /\\ y <_ N ) )')], 'mpbird', 'y e. ( 1 ... N )')
    ss = w.s([w.s([yfz], 'ex', '( %s -> ( y e. %s -> y e. ( 1 ... N ) ) )' % (A, DVg))], 'ssrdv', '( %s -> %s C_ ( 1 ... N ) )' % (A, DVg))
    # closure on DVg and on ( 1 ... N )
    def ifcc(ante, mnn):
        s_ = mkst(w, ante)
        pr = phsre(w, ante, mnn, lift(w, sr, ante), 'm')
        return s_([s_([pr], 'recnd', '%s e. CC' % PHS('S', 'm')), s_([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFC('m'))
    AM = '( %s /\\ m e. %s )' % (A, DVg); sm = mkst(w, AM)
    subm = w.s([], 'breq1', '( x = m -> ( x || %s <-> m || %s ) )' % (g, g))
    elm = w.s([subm], 'elrab', '( m e. %s <-> ( m e. NN /\\ m || %s ) )' % (DVg, g))
    mb = sm([sm([], 'simpr', 'm e. %s' % DVg), elm], 'sylib', '( m e. NN /\\ m || %s )' % g)
    mnn = sm([mb], 'simpld', 'm e. NN'); mdv = sm([mb], 'simprd', 'm || %s' % g)
    c_dv = ifcc(AM, mnn)
    mz = sm([mnn], 'nnzd', 'm e. ZZ')
    gb = w.s([bind3(w, AM, mz, lift(w, dz, AM), lift(w, ez, AM), 'm e. ZZ', 'D e. ZZ', 'E e. ZZ'), w.inst('dvdsgcdb')], 'syl', '( %s -> ( %s <-> m || %s ) )' % (AM, COND('m'), g))
    cm = sm([mdv, gb], 'mpbird', COND('m'))
    tru = sm([cm], 'iftrued', '%s = %s' % (IFC('m'), PHS('S', 'm')))
    # zero outside
    AO = '( %s /\\ m e. ( ( 1 ... N ) \\ %s ) )' % (A, DVg); so = mkst(w, AO)
    mo = so([], 'simpr', 'm e. ( ( 1 ... N ) \\ %s )' % DVg)
    mofz = so([mo], 'eldifad', 'm e. ( 1 ... N )'); mnot = so([mo], 'eldifbd', '-. m e. %s' % DVg)
    AOC = '( %s /\\ %s )' % (AO, COND('m')); soc = mkst(w, AOC)
    mnn2 = sy(w, AOC, lift(w, mofz, AOC), 'elfznn', 'm e. NN')
    gb2 = w.s([bind3(w, AOC, soc([mnn2], 'nnzd', 'm e. ZZ'), lift(w, dz, AOC), lift(w, ez, AOC), 'm e. ZZ', 'D e. ZZ', 'E e. ZZ'), w.inst('dvdsgcdb')], 'syl',
              '( %s -> ( %s <-> m || %s ) )' % (AOC, COND('m'), g))
    mg2 = soc([soc([], 'simpr', COND('m')), gb2], 'mpbid', 'm || %s' % g)
    inn = soc([soc([mnn2, mg2], 'jca', '( m e. NN /\\ m || %s )' % g), elm], 'sylibr', 'm e. %s' % DVg)
    ncond = so([mnot, w.s([inn], 'ex', '( %s -> ( %s -> m e. %s ) )' % (AO, COND('m'), DVg))], 'mtod', '-. %s' % COND('m'))
    zero = so([ncond], 'iffalsed', '%s = 0' % IFC('m'))
    fss = st([ss, c_dv, zero, st([], 'fzfid', '( 1 ... N ) e. Fin')], 'fsumss', 'sum_ m e. %s %s = sum_ m e. ( 1 ... N ) %s' % (DVg, IFC('m'), IFC('m')))
    s2 = st([tru], 'sumeq2dv', 'sum_ m e. %s %s = sum_ m e. %s %s' % (DVg, IFC('m'), DVg, PHS('S', 'm')))
    idm = w.s([], 'id', '( d = m -> d = m )')
    cgd, _ = w.congr(PHS('S', 'd'), {'d': 'm'}, 'd = m', {'d': idm})
    cb = st([w.s([cgd], 'cbvsumv', 'sum_ d e. %s %s = sum_ m e. %s %s' % (DVg, PHS('S', 'd'), DVg, PHS('S', 'm')))], 'a1i',
            'sum_ d e. %s %s = sum_ m e. %s %s' % (DVg, PHS('S', 'd'), DVg, PHS('S', 'm')))
    ph_ = sy(w, A, bind(w, A, sr, st([gnn, mug], 'jca', SQF(g)), 'S e. RR', SQF(g)), 'bvphisgsum', 'sum_ d e. %s %s = ( %s ^c S )' % (DVg, PHS('S', 'd'), g))
    full = eqtr(w, A, [st([fss], 'eqcomd', 'sum_ m e. ( 1 ... N ) %s = sum_ m e. %s %s' % (IFC('m'), DVg, IFC('m'))), s2,
                       st([cb], 'eqcomd', 'sum_ m e. %s %s = sum_ d e. %s %s' % (DVg, PHS('S', 'm'), DVg, PHS('S', 'd'))), ph_], None)
    w.qed([full, w.inst('id')], 'syl', STATEMENTS['bvdiagsum'])
    return w


def bvdiagpt():
    w = W('bvdiagpt', 'Pointwise gcd insertion (the hpt step of Lean sum_lcm_eq_sum_phiSig_Ssum_sq): '
                      'L_D L_E lcm^-S = sum_ m phiSig ( m ) [ m | D ] L_D D^-S [ m | E ] L_E E^-S.')
    h1, h2, h3, h4 = hyps_of(w, 'bvdiagpt')
    st = mkst(w, PH)
    sr = st([h1], 'simpld', 'S e. RR'); nnn = st([h1], 'simprd', 'N e. NN')
    dfz = st([h2], 'simpld', 'D e. ( 1 ... N )'); efz = st([h2], 'simprd', 'E e. ( 1 ... N )')
    dnn = sy(w, PH, dfz, 'elfznn', 'D e. NN'); enn = sy(w, PH, efz, 'elfznn', 'E e. NN')
    ldr = st([h3], 'simpld', '( L ` D ) e. RR'); ler = st([h3], 'simprd', '( L ` E ) e. RR')
    ns = st([sr], 'renegcld', '-u S e. RR')
    DS = '( D ^c -u S )'; ES = '( E ^c -u S )'
    dsr = st([st([st([dnn], 'nnrpd', 'D e. RR+'), ns], 'rpcxpcld', '%s e. RR+' % DS)], 'rpred', '%s e. RR' % DS)
    esr = st([st([st([enn], 'nnrpd', 'E e. RR+'), ns], 'rpcxpcld', '%s e. RR+' % ES)], 'rpred', '%s e. RR' % ES)
    XD = '( ( L ` D ) x. %s )' % DS; XE = '( ( L ` E ) x. %s )' % ES
    xdr = st([ldr, dsr], 'remulcld', '%s e. RR' % XD); xer = st([ler, esr], 'remulcld', '%s e. RR' % XE)
    T = lambda m: '( %s x. ( %s x. %s ) )' % (PHS('S', m), XDm(m, 'D'), XDm(m, 'E'))
    RHS = 'sum_ m e. ( 1 ... N ) %s' % T('m')
    LHS = LCMS('D', 'E')
    fin = st([], 'fzfid', '( 1 ... N ) e. Fin')
    # case: one weight vanishes
    def vanish(ante, lzero, which):
        s_ = mkst(w, ante)
        other = 'E' if which == 'D' else 'D'
        XW = XD if which == 'D' else XE
        WS = DS if which == 'D' else ES
        # X_which = 0
        xw0 = s_([s_([lzero], 'oveq1d', '( ( L ` %s ) x. %s ) = ( 0 x. %s )' % (which, WS, WS)),
                  s_([s_([lift(w, dsr if which == 'D' else esr, ante)], 'recnd', '%s e. CC' % WS)], 'mul02d', '( 0 x. %s ) = 0' % WS)], 'eqtrd', '%s = 0' % XW)
        AMm = '( %s /\\ m e. ( 1 ... N ) )' % ante; sm = mkst(w, AMm)
        ifw = sm([lift(w, xw0, AMm)], 'ifeq1d', '%s = if ( m || %s , 0 , 0 )' % (XDm('m', which), which))
        ifw0 = sm([ifw, sm([w.s([], 'ifid', 'if ( m || %s , 0 , 0 ) = 0' % which)], 'a1i', 'if ( m || %s , 0 , 0 ) = 0' % which)], 'eqtrd', '%s = 0' % XDm('m', which))
        mnn = sy(w, AMm, sm([], 'simpr', 'm e. ( 1 ... N )'), 'elfznn', 'm e. NN')
        phr = phsre(w, AMm, mnn, lift(w, sr, AMm), 'm')
        XO = XD if which == 'E' else XE
        xoc = sm([lift(w, xdr if other == 'D' else xer, AMm)], 'recnd', '%s e. CC' % XO)
        ifo = sm([xoc, sm([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XDm('m', other))
        if which == 'D':
            pr0 = sm([sm([ifw0], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (XDm('m', 'D'), XDm('m', 'E'), XDm('m', 'E'))), sm([ifo], 'mul02d', '( 0 x. %s ) = 0' % XDm('m', 'E'))],
                     'eqtrd', '( %s x. %s ) = 0' % (XDm('m', 'D'), XDm('m', 'E')))
        else:
            pr0 = sm([sm([ifw0], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (XDm('m', 'D'), XDm('m', 'E'), XDm('m', 'D'))), sm([ifo], 'mul01d', '( %s x. 0 ) = 0' % XDm('m', 'D'))],
                     'eqtrd', '( %s x. %s ) = 0' % (XDm('m', 'D'), XDm('m', 'E')))
        t0 = sm([sm([pr0], 'oveq2d', '%s = ( %s x. 0 )' % (T('m'), PHS('S', 'm'))), sm([sm([phr], 'recnd', '%s e. CC' % PHS('S', 'm'))], 'mul01d', '( %s x. 0 ) = 0' % PHS('S', 'm'))],
                'eqtrd', '%s = 0' % T('m'))
        r0 = s_([s_([t0], 'sumeq2dv', '%s = sum_ m e. ( 1 ... N ) 0' % RHS), s_([s_([lift(w, fin, ante)], 'olcd', '( ( 1 ... N ) C_ ( ZZ>= ` 1 ) \\/ ( 1 ... N ) e. Fin )'), w.inst('sumz')],
                                                                              'syl', 'sum_ m e. ( 1 ... N ) 0 = 0')], 'eqtrd', '%s = 0' % RHS)
        lc = s_([lift(w, ldr, ante)], 'recnd', '( L ` D ) e. CC'); lec_ = s_([lift(w, ler, ante)], 'recnd', '( L ` E ) e. CC')
        lnn = lcmnn(w, ante, lift(w, dnn, ante), lift(w, enn, ante), 'D', 'E')
        lsc = s_([s_([s_([lnn], 'nnrpd', '( D lcm E ) e. RR+'), lift(w, ns, ante)], 'rpcxpcld', '( ( D lcm E ) ^c -u S ) e. RR+')], 'rpcnd', '( ( D lcm E ) ^c -u S ) e. CC')
        if which == 'D':
            ll0 = s_([s_([lzero], 'oveq1d', '( ( L ` D ) x. ( L ` E ) ) = ( 0 x. ( L ` E ) )'), s_([lec_], 'mul02d', '( 0 x. ( L ` E ) ) = 0')], 'eqtrd', '( ( L ` D ) x. ( L ` E ) ) = 0')
        else:
            ll0 = s_([s_([lzero], 'oveq2d', '( ( L ` D ) x. ( L ` E ) ) = ( ( L ` D ) x. 0 )'), s_([lc], 'mul01d', '( ( L ` D ) x. 0 ) = 0')], 'eqtrd', '( ( L ` D ) x. ( L ` E ) ) = 0')
        l0 = s_([s_([ll0], 'oveq1d', '%s = ( 0 x. ( ( D lcm E ) ^c -u S ) )' % LHS), s_([lsc], 'mul02d', '( 0 x. ( ( D lcm E ) ^c -u S ) ) = 0')], 'eqtrd', '%s = 0' % LHS)
        return s_([l0, r0], 'eqtr4d', '%s = %s' % (LHS, RHS))
    AP = '( ph /\\ ( mmu ` D ) = 0 )'
    cD = vanish(AP, mkst(w, AP)([mkst(w, AP)([], 'simpr', '( mmu ` D ) = 0'), lift(w, st([h4], 'simpld', '( ( mmu ` D ) = 0 -> ( L ` D ) = 0 )'), AP)], 'mpd', '( L ` D ) = 0'), 'D')
    AN = '( ph /\\ -. ( mmu ` D ) = 0 )'
    AQ = '( %s /\\ ( mmu ` E ) = 0 )' % AN
    cE = vanish(AQ, mkst(w, AQ)([mkst(w, AQ)([], 'simpr', '( mmu ` E ) = 0'), lift(w, st([h4], 'simprd', '( ( mmu ` E ) = 0 -> ( L ` E ) = 0 )'), AQ)], 'mpd', '( L ` E ) = 0'), 'E')
    # main case
    AM = '( %s /\\ -. ( mmu ` E ) = 0 )' % AN; sm = mkst(w, AM)
    mud = sm([lift(w, mkst(w, AN)([], 'simpr', '-. ( mmu ` D ) = 0'), AM)], 'neqned', '( mmu ` D ) =/= 0')
    mue = sm([sm([], 'simpr', '-. ( mmu ` E ) = 0')], 'neqned', '( mmu ` E ) =/= 0')
    COND = lambda m: '( %s || D /\\ %s || E )' % (m, m)
    IFC = lambda m: 'if ( %s , %s , 0 )' % (COND(m), PHS('S', m))
    XX = '( %s x. %s )' % (XD, XE)
    AMm = '( %s /\\ m e. ( 1 ... N ) )' % AM; smm = mkst(w, AMm)
    mnn = sy(w, AMm, smm([], 'simpr', 'm e. ( 1 ... N )'), 'elfznn', 'm e. NN')
    phr = phsre(w, AMm, mnn, lift(w, sr, AMm), 'm')
    phc = smm([phr], 'recnd', '%s e. CC' % PHS('S', 'm'))
    xdc = smm([lift(w, xdr, AMm)], 'recnd', '%s e. CC' % XD); xec = smm([lift(w, xer, AMm)], 'recnd', '%s e. CC' % XE)
    xxc = smm([xdc, xec], 'mulcld', '%s e. CC' % XX)
    im = w.s([smm([xdc, xec], 'jca', '( %s e. CC /\\ %s e. CC )' % (XD, XE)), w.inst('ifmul2')], 'syl', '( %s -> if ( %s , %s , 0 ) = ( %s x. %s ) )' % (AMm, COND('m'), XX, XDm('m', 'D'), XDm('m', 'E')))
    z2 = w.s([phc, w.inst('ifmulz2')], 'syl', '( %s -> ( %s x. if ( %s , %s , 0 ) ) = if ( %s , ( %s x. %s ) , 0 ) )' % (AMm, PHS('S', 'm'), COND('m'), XX, COND('m'), PHS('S', 'm'), XX))
    z1 = w.s([xxc, w.inst('ifmulz')], 'syl', '( %s -> ( %s x. %s ) = if ( %s , ( %s x. %s ) , 0 ) )' % (AMm, IFC('m'), XX, COND('m'), PHS('S', 'm'), XX))
    term = eqtr(w, AMm, [smm([smm([im], 'eqcomd', '( %s x. %s ) = if ( %s , %s , 0 )' % (XDm('m', 'D'), XDm('m', 'E'), COND('m'), XX))], 'oveq2d',
                             '%s = ( %s x. if ( %s , %s , 0 ) )' % (T('m'), PHS('S', 'm'), COND('m'), XX)), z2,
                         smm([z1], 'eqcomd', 'if ( %s , ( %s x. %s ) , 0 ) = ( %s x. %s )' % (COND('m'), PHS('S', 'm'), XX, IFC('m'), XX))], None)
    ifcc = smm([phc, smm([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFC('m'))
    s1 = sm([term], 'sumeq2dv', '%s = sum_ m e. ( 1 ... N ) ( %s x. %s )' % (RHS, IFC('m'), XX))
    fm = sm([lift(w, fin, AM), sm([lift(w, xdr, AM), lift(w, xer, AM)], 'remulcld', '%s e. RR' % XX) and sm([sm([lift(w, xdr, AM), lift(w, xer, AM)], 'remulcld', '%s e. RR' % XX)], 'recnd', '%s e. CC' % XX), ifcc],
            'fsummulc1', '( sum_ m e. ( 1 ... N ) %s x. %s ) = sum_ m e. ( 1 ... N ) ( %s x. %s )' % (IFC('m'), XX, IFC('m'), XX))
    ds = sy(w, AM, bind(w, AM, lift(w, h1, AM), bind(w, AM, lift(w, h2, AM), sm([mud, mue], 'jca', '( ( mmu ` D ) =/= 0 /\\ ( mmu ` E ) =/= 0 )'),
                                                                        '( D e. ( 1 ... N ) /\\ E e. ( 1 ... N ) )', '( ( mmu ` D ) =/= 0 /\\ ( mmu ` E ) =/= 0 )'),
                                 '( S e. RR /\\ N e. NN )', '( ( D e. ( 1 ... N ) /\\ E e. ( 1 ... N ) ) /\\ ( ( mmu ` D ) =/= 0 /\\ ( mmu ` E ) =/= 0 ) )'),
            'bvdiagsum', 'sum_ m e. ( 1 ... N ) %s = ( ( D gcd E ) ^c S )' % IFC('m'))
    G = '( ( D gcd E ) ^c S )'
    rhs = eqtr(w, AM, [s1, sm([fm], 'eqcomd', 'sum_ m e. ( 1 ... N ) ( %s x. %s ) = ( sum_ m e. ( 1 ... N ) %s x. %s )' % (IFC('m'), XX, IFC('m'), XX)),
                       sm([ds], 'oveq1d', '( sum_ m e. ( 1 ... N ) %s x. %s ) = ( %s x. %s )' % (IFC('m'), XX, G, XX))], None)
    lc = w.s([bind(w, AM, bind(w, AM, lift(w, dnn, AM), lift(w, enn, AM), 'D e. NN', 'E e. NN'), lift(w, sr, AM), '( D e. NN /\\ E e. NN )', 'S e. RR'), w.inst('bvlcmcxp')], 'syl',
             '( %s -> ( ( D lcm E ) ^c -u S ) = ( %s x. ( %s x. %s ) ) )' % (AM, G, DS, ES))
    l1 = sm([lc], 'oveq2d', '%s = ( ( ( L ` D ) x. ( L ` E ) ) x. ( %s x. ( %s x. %s ) ) )' % (LHS, G, DS, ES))
    gnn = sm([lift(w, dnn, AM), lift(w, enn, AM), w.inst('gcdnncl')], 'syl2anc', '( D gcd E ) e. NN')
    gr = sm([sm([sm([gnn], 'nnrpd', '( D gcd E ) e. RR+'), lift(w, sr, AM)], 'rpcxpcld', '%s e. RR+' % G)], 'rpred', '%s e. RR' % G)
    lv = {'( L ` D )': lift(w, ldr, AM), '( L ` E )': lift(w, ler, AM), G: gr, DS: lift(w, dsr, AM), ES: lift(w, esr, AM)}
    rr = lineq(w, AM, '( ( ( L ` D ) x. ( L ` E ) ) x. ( %s x. ( %s x. %s ) ) )' % (G, DS, ES), '( %s x. %s )' % (G, XX), leaves=lv, products=True, atoms=list(lv))
    cM = eqtr(w, AM, [l1, rr, sm([rhs], 'eqcomd', '( %s x. %s ) = %s' % (G, XX, RHS))], None)
    cN = w.s([cE, cM], 'pm2.61dan', '( %s -> %s = %s )' % (AN, LHS, RHS))
    w.qed([cD, cN], 'pm2.61dan', STATEMENTS['bvdiagpt'])
    return w


def bvdiag():
    w = W('bvdiag', 'The Selberg diagonalisation (Lean sum_lcm_eq_sum_phiSig_Ssum_sq): sum_ d sum_ e L_d L_e lcm^-S '
                    '= sum_ m phiSig ( m ) S_m^2 with S_m = sum_ d [ m | d ] L_d d^-S.')
    h1, h2, h3, h4 = hyps_of(w, 'bvdiag')
    st = mkst(w, PH)
    fin = st([], 'fzfid', '( 1 ... N ) e. Fin')
    ns = st([h1], 'renegcld', '-u S e. RR')
    T = lambda m, d, e: '( %s x. ( %s x. %s ) )' % (PHS('S', m), XDm(m, d), XDm(m, e))
    AD = '( ph /\\ d e. ( 1 ... N ) )'; sd = mkst(w, AD)
    ADE = '( %s /\\ e e. ( 1 ... N ) )' % AD; sde = mkst(w, ADE)
    h3e, _ = rename(w, PH, '( 1 ... N )', 'd', 'e', h3, '( L ` d ) e. RR')
    h4e, _ = rename(w, PH, '( 1 ... N )', 'd', 'e', h4, '( ( mmu ` d ) = 0 -> ( L ` d ) = 0 )')
    phde = lift(w, w.s([], 'id', '( ph -> ph )'), ADE)
    efz = sde([], 'simpr', 'e e. ( 1 ... N )'); dfz = lift(w, sd([], 'simpr', 'd e. ( 1 ... N )'), ADE)
    pt = w.s([sde([lift(w, h1, ADE), lift(w, h2, ADE)], 'jca', '( S e. RR /\\ N e. NN )'), sde([dfz, efz], 'jca', '( d e. ( 1 ... N ) /\\ e e. ( 1 ... N ) )'),
              sde([lift(w, h3, ADE), hyp2(w, ADE, phde, efz, h3e, '( L ` e ) e. RR')], 'jca', '( ( L ` d ) e. RR /\\ ( L ` e ) e. RR )'),
              sde([lift(w, h4, ADE), hyp2(w, ADE, phde, efz, h4e, '( ( mmu ` e ) = 0 -> ( L ` e ) = 0 )')], 'jca',
                  '( ( ( mmu ` d ) = 0 -> ( L ` d ) = 0 ) /\\ ( ( mmu ` e ) = 0 -> ( L ` e ) = 0 ) )')], 'bvdiagpt',
             '( %s -> %s = sum_ m e. ( 1 ... N ) %s )' % (ADE, LCMS(), T('m', 'd', 'e')))
    SM = lambda: 'sum_ m e. ( 1 ... N ) %s' % T('m', 'd', 'e')
    e1 = st([sd([pt], 'sumeq2dv', 'sum_ e e. ( 1 ... N ) %s = sum_ e e. ( 1 ... N ) %s' % (LCMS(), SM()))], 'sumeq2dv',
            '%s = sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s' % (DSUM(), SM()))
    # closure of T under ( ( AD /\ e ) /\ m ) style antecedents
    def tcc(ante, dfz_, efz_, mfz_, ldr_, ler_):
        s_ = mkst(w, ante)
        dnn = sy(w, ante, dfz_, 'elfznn', 'd e. NN'); enn = sy(w, ante, efz_, 'elfznn', 'e e. NN'); mnn = sy(w, ante, mfz_, 'elfznn', 'm e. NN')
        nsA = lift(w, ns, ante)
        xd = s_([s_([ldr_, s_([s_([s_([dnn], 'nnrpd', 'd e. RR+'), nsA], 'rpcxpcld', '( d ^c -u S ) e. RR+')], 'rpred', '( d ^c -u S ) e. RR')], 'remulcld',
                    '( ( L ` d ) x. ( d ^c -u S ) ) e. RR')], 'recnd', '( ( L ` d ) x. ( d ^c -u S ) ) e. CC')
        xe = s_([s_([ler_, s_([s_([s_([enn], 'nnrpd', 'e e. RR+'), nsA], 'rpcxpcld', '( e ^c -u S ) e. RR+')], 'rpred', '( e ^c -u S ) e. RR')], 'remulcld',
                    '( ( L ` e ) x. ( e ^c -u S ) ) e. RR')], 'recnd', '( ( L ` e ) x. ( e ^c -u S ) ) e. CC')
        ifd = s_([xd, s_([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XDm('m', 'd'))
        ife = s_([xe, s_([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XDm('m', 'e'))
        ph_ = s_([phsre(w, ante, mnn, lift(w, h1, ante), 'm')], 'recnd', '%s e. CC' % PHS('S', 'm'))
        return s_([ph_, s_([ifd, ife], 'mulcld', '( %s x. %s ) e. CC' % (XDm('m', 'd'), XDm('m', 'e')))], 'mulcld', '%s e. CC' % T('m', 'd', 'e'))
    # inner swap: sum_ e sum_ m = sum_ m sum_ e, under AD
    A1 = '( %s /\\ ( e e. ( 1 ... N ) /\\ m e. ( 1 ... N ) ) )' % AD; s1 = mkst(w, A1)
    ph1 = lift(w, w.s([], 'id', '( ph -> ph )'), A1)
    t1 = tcc(A1, lift(w, sd([], 'simpr', 'd e. ( 1 ... N )'), A1), s1([], 'simprl', 'e e. ( 1 ... N )'), s1([], 'simprr', 'm e. ( 1 ... N )'),
             lift(w, h3, A1), hyp2(w, A1, ph1, s1([], 'simprl', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR'))
    c1 = sd([sd([], 'fzfid', '( 1 ... N ) e. Fin'), sd([], 'fzfid', '( 1 ... N ) e. Fin'), t1], 'fsumcom',
            'sum_ e e. ( 1 ... N ) %s = sum_ m e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s' % (SM(), T('m', 'd', 'e')))
    e2 = st([c1], 'sumeq2dv', 'sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = sum_ d e. ( 1 ... N ) sum_ m e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s' % (SM(), T('m', 'd', 'e')))
    # outer swap: sum_ d sum_ m = sum_ m sum_ d
    A2 = '( ph /\\ ( d e. ( 1 ... N ) /\\ m e. ( 1 ... N ) ) )'; s2 = mkst(w, A2)
    A2e = '( %s /\\ e e. ( 1 ... N ) )' % A2; s2e = mkst(w, A2e)
    ph2 = lift(w, w.s([], 'id', '( ph -> ph )'), A2e)
    d2 = lift(w, s2([], 'simprl', 'd e. ( 1 ... N )'), A2e)
    t2 = tcc(A2e, d2, s2e([], 'simpr', 'e e. ( 1 ... N )'), lift(w, s2([], 'simprr', 'm e. ( 1 ... N )'), A2e),
             hyp2(w, A2e, ph2, d2, h3, '( L ` d ) e. RR'), hyp2(w, A2e, ph2, s2e([], 'simpr', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR'))
    se2 = s2([s2([], 'fzfid', '( 1 ... N ) e. Fin'), t2], 'fsumcl', 'sum_ e e. ( 1 ... N ) %s e. CC' % T('m', 'd', 'e'))
    c2 = st([fin, fin, se2], 'fsumcom', 'sum_ d e. ( 1 ... N ) sum_ m e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = sum_ m e. ( 1 ... N ) sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s'
            % (T('m', 'd', 'e'), T('m', 'd', 'e')))
    # evaluate for each m
    AM = '( ph /\\ m e. ( 1 ... N ) )'; sm = mkst(w, AM)
    mnn = sy(w, AM, sm([], 'simpr', 'm e. ( 1 ... N )'), 'elfznn', 'm e. NN')
    phc = sm([phsre(w, AM, mnn, lift(w, h1, AM), 'm')], 'recnd', '%s e. CC' % PHS('S', 'm'))
    AMD = '( %s /\\ d e. ( 1 ... N ) )' % AM; smd = mkst(w, AMD)
    AMDE = '( %s /\\ e e. ( 1 ... N ) )' % AMD; smde = mkst(w, AMDE)
    ph3 = lift(w, w.s([], 'id', '( ph -> ph )'), AMDE)
    d3 = lift(w, smd([], 'simpr', 'd e. ( 1 ... N )'), AMDE); e3 = smde([], 'simpr', 'e e. ( 1 ... N )')
    def xcc(ante, fz, v, lr):
        s_ = mkst(w, ante)
        vn = sy(w, ante, fz, 'elfznn', '%s e. NN' % v)
        x = s_([s_([lr, s_([s_([s_([vn], 'nnrpd', '%s e. RR+' % v), lift(w, ns, ante)], 'rpcxpcld', '( %s ^c -u S ) e. RR+' % v)], 'rpred', '( %s ^c -u S ) e. RR' % v)], 'remulcld',
                   '( ( L ` %s ) x. ( %s ^c -u S ) ) e. RR' % (v, v))], 'recnd', '( ( L ` %s ) x. ( %s ^c -u S ) ) e. CC' % (v, v))
        return s_([x, s_([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XDm('m', v))
    xd3 = xcc(AMD, smd([], 'simpr', 'd e. ( 1 ... N )'), 'd', hyp2(w, AMD, lift(w, w.s([], 'id', '( ph -> ph )'), AMD), smd([], 'simpr', 'd e. ( 1 ... N )'), h3, '( L ` d ) e. RR'))
    xe3 = xcc(AMDE, e3, 'e', hyp2(w, AMDE, ph3, e3, h3e, '( L ` e ) e. RR'))
    P = '( %s x. %s )' % (XDm('m', 'd'), XDm('m', 'e'))
    pc = smde([lift(w, xd3, AMDE), xe3], 'mulcld', '%s e. CC' % P)
    mi = smd([smd([], 'fzfid', '( 1 ... N ) e. Fin'), lift(w, phc, AMD), pc], 'fsummulc2', '( %s x. sum_ e e. ( 1 ... N ) %s ) = sum_ e e. ( 1 ... N ) %s' % (PHS('S', 'm'), P, T('m', 'd', 'e')))
    ipc = smd([smd([], 'fzfid', '( 1 ... N ) e. Fin'), pc], 'fsumcl', 'sum_ e e. ( 1 ... N ) %s e. CC' % P)
    mo = sm([sm([], 'fzfid', '( 1 ... N ) e. Fin'), phc, ipc], 'fsummulc2',
            '( %s x. sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s ) = sum_ d e. ( 1 ... N ) ( %s x. sum_ e e. ( 1 ... N ) %s )' % (PHS('S', 'm'), P, PHS('S', 'm'), P))
    AME = '( %s /\\ e e. ( 1 ... N ) )' % AM; sme = mkst(w, AME)
    xe4 = xcc(AME, sme([], 'simpr', 'e e. ( 1 ... N )'), 'e', hyp2(w, AME, lift(w, w.s([], 'id', '( ph -> ph )'), AME), sme([], 'simpr', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR'))
    SGE = 'sum_ e e. ( 1 ... N ) %s' % XDm('m', 'e')
    f2 = sm([sm([], 'fzfid', '( 1 ... N ) e. Fin'), sm([], 'fzfid', '( 1 ... N ) e. Fin'), xd3, xe4], 'fsum2mul', 'sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = ( %s x. %s )' % (P, SG('m'), SGE))
    ide = w.s([], 'id', '( d = e -> d = e )')
    cg, _ = w.congr(XDm('m', 'd'), {'d': 'e'}, 'd = e', {'d': ide})
    cb = sm([w.s([cg], 'cbvsumv', '%s = %s' % (SG('m'), SGE))], 'a1i', '%s = %s' % (SG('m'), SGE))
    sgc = sm([sm([], 'fzfid', '( 1 ... N ) e. Fin'), xd3], 'fsumcl', '%s e. CC' % SG('m'))
    sq = sm([sm([sgc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (SG('m'), SG('m'), SG('m'))), sm([cb], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (SG('m'), SG('m'), SG('m'), SGE))], 'eqtrd',
            '( %s ^ 2 ) = ( %s x. %s )' % (SG('m'), SG('m'), SGE))
    inner = sm([smd([mi], 'eqcomd', 'sum_ e e. ( 1 ... N ) %s = ( %s x. sum_ e e. ( 1 ... N ) %s )' % (T('m', 'd', 'e'), PHS('S', 'm'), P))], 'sumeq2dv',
               'sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = sum_ d e. ( 1 ... N ) ( %s x. sum_ e e. ( 1 ... N ) %s )' % (T('m', 'd', 'e'), PHS('S', 'm'), P))
    val = eqtr(w, AM, [inner, sm([mo], 'eqcomd', 'sum_ d e. ( 1 ... N ) ( %s x. sum_ e e. ( 1 ... N ) %s ) = ( %s x. sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s )'
                                % (PHS('S', 'm'), P, PHS('S', 'm'), P)),
                       sm([sm([f2, sm([sq], 'eqcomd', '( %s x. %s ) = ( %s ^ 2 )' % (SG('m'), SGE, SG('m')))], 'eqtrd',
                              'sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = ( %s ^ 2 )' % (P, SG('m')))], 'oveq2d',
                          '( %s x. sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s ) = ( %s x. ( %s ^ 2 ) )' % (PHS('S', 'm'), P, PHS('S', 'm'), SG('m')))], None)
    e3_ = st([val], 'sumeq2dv', 'sum_ m e. ( 1 ... N ) sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = sum_ m e. ( 1 ... N ) ( %s x. ( %s ^ 2 ) )' % (T('m', 'd', 'e'), PHS('S', 'm'), SG('m')))
    full = eqtr(w, PH, [e1, e2, c2, e3_], None)
    w.qed([full, w.inst('id')], 'syl', STATEMENTS['bvdiag'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvlcmcxp', 'bvdiagsum', 'bvdiagpt', 'bvdiag']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
