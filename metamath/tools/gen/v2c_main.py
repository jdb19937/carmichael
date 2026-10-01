"""Sortie v2c: the main term of the Selberg Lambda squared sieve.

musq1   the square of the Moebius value at a squarefree argument is one
ifsq    the square of an indicator term
lwff    the Selberg weights as a function NN --> RR
lwfv    its values
mpfv    the Lambda squared coefficient of the weight function
mpmss   the diagonalised summand evaluated by the weight diagonalisation
mpmev   the resulting sum is one over the bounding sum
mpmain  the main term of the sieve
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2c_lib import *
from cl import lift

LWF = '( t e. NN |-> %s )' % LW('t')


def musq1():
    w = W('musq1', 'The square of the Moebius value at a squarefree argument is one.')
    A = '( N e. NN /\\ ( mmu ` N ) =/= 0 )'
    st = mkst(w, A)
    nnn = w.s([], 'simpl', '( %s -> N e. NN )' % A)
    sqf = w.s([], 'simpr', '( %s -> ( mmu ` N ) =/= 0 )' % A)
    OMN = OM('N', 'p')
    fin = st([nnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('N', 'p'))
    k0 = st([fin, w.inst('hashcl')], 'syl', '%s e. NN0' % OMN)
    kz = st([k0], 'nn0zd', '%s e. ZZ' % OMN)
    mv = st([w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('muval2')], 'syl',
            '( mmu ` N ) = ( -u 1 ^ %s )' % OMN)
    m1c = w.s([], 'neg1cn', '-u 1 e. CC')
    m1cd = st([m1c], 'a1i', '-u 1 e. CC')
    two = w.s([], '2nn0', '2 e. NN0')
    twod = st([two], 'a1i', '2 e. NN0')
    e1 = st([st([m1cd, k0, twod, w.inst('expmul')], 'syl3anc',
                '( -u 1 ^ ( %s x. 2 ) ) = ( ( -u 1 ^ %s ) ^ 2 )' % (OMN, OMN))], 'eqcomd',
             '( ( -u 1 ^ %s ) ^ 2 ) = ( -u 1 ^ ( %s x. 2 ) )' % (OMN, OMN))
    e2 = st([st([st([k0], 'nn0cnd', '%s e. CC' % OMN),
                 st([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')], 'mulcomd',
                '( %s x. 2 ) = ( 2 x. %s )' % (OMN, OMN))], 'oveq2d',
             '( -u 1 ^ ( %s x. 2 ) ) = ( -u 1 ^ ( 2 x. %s ) )' % (OMN, OMN))
    e3 = st([m1cd, twod, k0, w.inst('expmul')], 'syl3anc',
            '( -u 1 ^ ( 2 x. %s ) ) = ( ( -u 1 ^ 2 ) ^ %s )' % (OMN, OMN))
    e4 = st([st([w.s([], 'neg1sqe1', '( -u 1 ^ 2 ) = 1')], 'a1i', '( -u 1 ^ 2 ) = 1')], 'oveq1d',
            '( ( -u 1 ^ 2 ) ^ %s ) = ( 1 ^ %s )' % (OMN, OMN))
    e5 = st([kz, w.inst('1exp')], 'syl', '( 1 ^ %s ) = 1' % OMN)
    rhs = st([st([e1, e2], 'eqtrd',
                 '( ( -u 1 ^ %s ) ^ 2 ) = ( -u 1 ^ ( 2 x. %s ) )' % (OMN, OMN)),
              st([st([e3, e4], 'eqtrd',
                     '( -u 1 ^ ( 2 x. %s ) ) = ( 1 ^ %s )' % (OMN, OMN)), e5], 'eqtrd',
                 '( -u 1 ^ ( 2 x. %s ) ) = 1' % OMN)], 'eqtrd',
             '( ( -u 1 ^ %s ) ^ 2 ) = 1' % OMN)
    w.qed([st([mv], 'oveq1d', '( ( mmu ` N ) ^ 2 ) = ( ( -u 1 ^ %s ) ^ 2 )' % OMN), rhs],
          'eqtrd', '( %s -> ( ( mmu ` N ) ^ 2 ) = 1 )' % A)
    return w


def ifsq():
    w = W('ifsq', 'The square of an indicator term.')
    A0 = 'if ( ph , A , 0 )'
    A1 = 'if ( ph , ( A ^ 2 ) , 0 )'
    T = '( A e. CC /\\ ph )'
    F = '( A e. CC /\\ -. ph )'
    pt = w.s([], 'simpr', '( %s -> ph )' % T)
    tt = w.s([w.s([w.s([pt], 'iftrued', '( %s -> %s = A )' % (T, A0))], 'oveq1d',
                  '( %s -> ( %s ^ 2 ) = ( A ^ 2 ) )' % (T, A0)),
              w.s([w.s([pt], 'iftrued', '( %s -> %s = ( A ^ 2 ) )' % (T, A1))], 'eqcomd',
                  '( %s -> ( A ^ 2 ) = %s )' % (T, A1))], 'eqtrd',
             '( %s -> ( %s ^ 2 ) = %s )' % (T, A0, A1))
    pf = w.s([], 'simpr', '( %s -> -. ph )' % F)
    z = w.s([w.s([], 'sq0', '( 0 ^ 2 ) = 0')], 'a1i', '( %s -> ( 0 ^ 2 ) = 0 )' % F)
    ff = w.s([w.s([w.s([w.s([pf], 'iffalsed', '( %s -> %s = 0 )' % (F, A0))], 'oveq1d',
                        '( %s -> ( %s ^ 2 ) = ( 0 ^ 2 ) )' % (F, A0)), z], 'eqtrd',
                  '( %s -> ( %s ^ 2 ) = 0 )' % (F, A0)),
              w.s([w.s([pf], 'iffalsed', '( %s -> %s = 0 )' % (F, A1))], 'eqcomd',
                  '( %s -> 0 = %s )' % (F, A1))], 'eqtrd',
             '( %s -> ( %s ^ 2 ) = %s )' % (F, A0, A1))
    w.qed([tt, ff], 'pm2.61dan', '( A e. CC -> ( %s ^ 2 ) = %s )' % (A0, A1))
    return w



def lwff():
    w = W('lwff', 'The Selberg weights as a real-valued function on the positive integers.')
    AT = '( %s /\\ t e. NN )' % SH
    st = mkst(w, SH)
    lwr = w.s([], 'lwre', '( %s -> %s e. RR )' % (AT, LW('t')))
    ral = st([lwr], 'ralrimiva', 'A. t e. NN %s e. RR' % LW('t'))
    eqf = w.s([], 'eqid', '%s = %s' % (LWF, LWF))
    bi = st([w.s([eqf], 'fmpt', '( A. t e. NN %s e. RR <-> %s : NN --> RR )' % (LW('t'), LWF))],
            'a1i', '( A. t e. NN %s e. RR <-> %s : NN --> RR )' % (LW('t'), LWF))
    w.qed([ral, bi], 'mpbid', '( %s -> %s : NN --> RR )' % (SH, LWF))
    return w


def lwfv():
    w = W('lwfv', 'The values of the Selberg weight function.')
    A = '( %s /\\ D e. NN )' % SH
    st = mkst(w, A)
    idt = w.s([], 'id', '( t = D -> t = D )')
    n0 = len(w.lines)
    hsub, new = w.congr(LW('t'), {'t': 'D'}, 't = D', {'t': idt})
    sdvfix(w, n0)
    assert (new if isinstance(new, str) else ' '.join(new)) == LW('D')
    eqf = w.s([], 'eqid', '%s = %s' % (LWF, LWF))
    inst = w.s([hsub, eqf], 'fvmptg',
               '( ( D e. NN /\\ %s e. RR ) -> ( %s ` D ) = %s )' % (LW('D'), LWF, LW('D')))
    dnn = w.s([], 'simpr', '( %s -> D e. NN )' % A)
    lwr = w.s([], 'lwre', '( %s -> %s e. RR )' % (A, LW('D')))
    w.qed([dnn, lwr, inst], 'syl2anc',
          '( %s -> ( %s ` D ) = %s )' % (A, LWF, LW('D')))
    return w



def MPF(N):
    """the Lambda squared coefficient of the weight function at N, over y-sets"""
    return ('sum_ u e. %s sum_ e e. %s if ( %s = ( u lcm e ) , '
            '( ( %s ` u ) x. ( %s ` e ) ) , 0 )'
            % (DV(N, 'y'), DV(N, 'y'), N, LWF, LWF))


def mpfv():
    w = W('mpfv', 'The Lambda squared coefficient of the Selberg weight function is the '
                  'Selberg Lambda squared coefficient.')
    A = '( %s /\\ N e. NN )' % SH
    st = mkst(w, A)
    nnn = w.s([], 'simpr', '( %s -> N e. NN )' % A)
    sh = w.s([], 'simpl', '( %s -> %s )' % (A, SH))
    DVy, DVx = DV('N', 'y'), DV('N')
    IFF = 'if ( N = ( u lcm e ) , ( ( %s ` u ) x. ( %s ` e ) ) , 0 )' % (LWF, LWF)
    IFW = 'if ( N = ( u lcm e ) , ( %s x. %s ) , 0 )' % (LW('u'), LW('e'))
    # ---- the range conversion
    cbv = w.s([w.s([w.s([], 'breq1', '( x = y -> ( x || N <-> y || N ) )')], 'cbvrabv',
                   '%s = %s' % (DVx, DVy))], 'eqcomi', '%s = %s' % (DVy, DVx))
    AUY = '( %s /\\ u e. %s )' % (A, DVy)
    r1 = w.s([w.s([cbv], 'a1i', '( %s -> %s = %s )' % (AUY, DVy, DVx))], 'sumeq1d',
             '( %s -> sum_ e e. %s %s = sum_ e e. %s %s )' % (AUY, DVy, IFF, DVx, IFF))
    r2 = st([r1], 'sumeq2dv',
            'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s'
            % (DVy, DVy, IFF, DVy, DVx, IFF))
    r3 = st([st([cbv], 'a1i', '%s = %s' % (DVy, DVx))], 'sumeq1d',
            'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s'
            % (DVy, DVx, IFF, DVx, DVx, IFF))
    rng = st([r2, r3], 'eqtrd',
             '%s = sum_ u e. %s sum_ e e. %s %s' % (MPF('N'), DVx, DVx, IFF))
    # ---- the body conversion
    AU = '( %s /\\ u e. %s )' % (A, DVx)
    du = dvdfacts(w, A, AU, 'u', 'N', sh, st([nnn], 'nnzd', 'N e. ZZ'),
                  st([], 'id', 'N || N') if False else None, None) if False else None
    su = mkst(w, AU)
    elu = w.s([w.s([], 'breq1', '( x = u -> ( x || N <-> u || N ) )')], 'elrab',
              '( u e. %s <-> ( u e. NN /\\ u || N ) )' % DVx)
    unn = su([su([su([elu], 'a1i', '( u e. %s <-> ( u e. NN /\\ u || N ) )' % DVx),
                  su([], 'simpr', 'u e. %s' % DVx)], 'mpbid', '( u e. NN /\\ u || N )')],
             'simpld', 'u e. NN')
    AUE = '( %s /\\ e e. %s )' % (AU, DVx)
    se = mkst(w, AUE)
    ele = w.s([w.s([], 'breq1', '( x = e -> ( x || N <-> e || N ) )')], 'elrab',
              '( e e. %s <-> ( e e. NN /\\ e || N ) )' % DVx)
    enn = se([se([se([ele], 'a1i', '( e e. %s <-> ( e e. NN /\\ e || N ) )' % DVx),
                  se([], 'simpr', 'e e. %s' % DVx)], 'mpbid', '( e e. NN /\\ e || N )')],
             'simpld', 'e e. NN')
    vu = se([se([lift(w, sh, AUE), lift(w, unn, AUE)], 'jca', '( %s /\\ u e. NN )' % SH),
             w.inst('lwfv')], 'syl', '( %s ` u ) = %s' % (LWF, LW('u')))
    ve = se([se([lift(w, sh, AUE), enn], 'jca', '( %s /\\ e e. NN )' % SH),
             w.inst('lwfv')], 'syl', '( %s ` e ) = %s' % (LWF, LW('e')))
    bod = se([se([vu, ve], 'oveq12d',
                 '( ( %s ` u ) x. ( %s ` e ) ) = ( %s x. %s )'
                 % (LWF, LWF, LW('u'), LW('e')))], 'ifeq1d', '%s = %s' % (IFF, IFW))
    b1 = su([bod], 'sumeq2dv',
            'sum_ e e. %s %s = sum_ e e. %s %s' % (DVx, IFF, DVx, IFW))
    b2 = st([b1], 'sumeq2dv',
            'sum_ u e. %s sum_ e e. %s %s = %s' % (DVx, DVx, IFF, MP('N', d='u', e='e')))
    w.qed([rng, b2], 'eqtrd', '( %s -> %s = %s )' % (A, MPF('N'), MP('N', d='u', e='e')))
    return w



def mpmss():
    w = W('mpmss', 'The diagonalised summand of the Selberg main term.')
    A = '( %s /\\ ( N e. NN /\\ N || P ) )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    nnn = st([], 'simprl', 'N e. NN')
    ndp = st([], 'simprr', 'N || P')
    DVx = DV('P')
    GN = GT('N')
    GG = '( ( %s x. ( mmu ` N ) ) x. ( 1 / %s ) )' % (GN, SS())
    COND = '( N ^ 2 ) <_ Y'
    SST = SSTERM('N')
    INS = 'sum_ j e. %s if ( N || j , ( ( V ` j ) x. %s ) , 0 )' % (DVx, LW('j'))
    # ---- closures
    grp = st([d['sh'], st([nnn, ndp], 'jca', '( N e. NN /\\ N || P )'), w.inst('gtrp')],
             'syl2anc', '%s e. RR+' % GN)
    gc = st([grp], 'rpcnd', '%s e. CC' % GN)
    gne = st([grp], 'rpne0d', '%s =/= 0' % GN)
    igc = st([st([grp], 'rpreccld', '( 1 / %s ) e. RR+' % GN)], 'rpcnd', '( 1 / %s ) e. CC' % GN)
    srp = st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())
    sc = st([st([srp], 'rpreccld', '( 1 / %s ) e. RR+' % SS())], 'rpcnd',
            '( 1 / %s ) e. CC' % SS())
    muc = st([st([nnn, w.inst('mucl')], 'syl', '( mmu ` N ) e. ZZ')], 'zcnd',
             '( mmu ` N ) e. CC')
    ggc = st([st([gc, muc], 'mulcld', '( %s x. ( mmu ` N ) ) e. CC' % GN), sc], 'mulcld',
             '%s e. CC' % GG)
    nsqf = st([st([st([d['pnn'], nnn, ndp], '3jca', '( P e. NN /\\ N e. NN /\\ N || P )'),
                   w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` N ) =/= 0 )'),
               d['psqf']], 'mpd', '( mmu ` N ) =/= 0')
    musq = st([st([nnn, nsqf], 'jca', '( N e. NN /\\ ( mmu ` N ) =/= 0 )'), w.inst('musq1')],
              'syl', '( ( mmu ` N ) ^ 2 ) = 1')
    # ---- the inner sum by the weight diagonalisation
    ld = st([], 'lwdiag', '%s = if ( %s , %s , 0 )' % (INS, COND, GG))
    sq = st([st([ld], 'oveq1d', '( %s ^ 2 ) = ( if ( %s , %s , 0 ) ^ 2 )' % (INS, COND, GG)),
             st([ggc, w.inst('ifsq')], 'syl',
                '( if ( %s , %s , 0 ) ^ 2 ) = if ( %s , ( %s ^ 2 ) , 0 )'
                % (COND, GG, COND, GG))], 'eqtrd',
            '( %s ^ 2 ) = if ( %s , ( %s ^ 2 ) , 0 )' % (INS, COND, GG))
    pull = st([igc, w.inst('ifmulz2')], 'syl',
              '( ( 1 / %s ) x. if ( %s , ( %s ^ 2 ) , 0 ) ) = '
              'if ( %s , ( ( 1 / %s ) x. ( %s ^ 2 ) ) , 0 )' % (GN, COND, GG, COND, GN, GG))
    # ---- the algebra inside the branch
    gmc = st([gc, muc], 'mulcld', '( %s x. ( mmu ` N ) ) e. CC' % GN)
    a1 = st([gmc, sc], 'sqmuld',
            '( %s ^ 2 ) = ( ( ( %s x. ( mmu ` N ) ) ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) )'
            % (GG, GN, SS()))
    a2 = st([st([st([gc, muc], 'sqmuld',
                    '( ( %s x. ( mmu ` N ) ) ^ 2 ) = ( ( %s ^ 2 ) x. ( ( mmu ` N ) ^ 2 ) )'
                    % (GN, GN)),
                 st([musq], 'oveq2d',
                    '( ( %s ^ 2 ) x. ( ( mmu ` N ) ^ 2 ) ) = ( ( %s ^ 2 ) x. 1 )' % (GN, GN))],
                'eqtrd', '( ( %s x. ( mmu ` N ) ) ^ 2 ) = ( ( %s ^ 2 ) x. 1 )' % (GN, GN)),
             st([st([gc, gc], 'mulcld', '( %s x. %s ) e. CC' % (GN, GN))], 'id',
                '( %s x. %s ) e. CC' % (GN, GN))], 'id', 'x = x') if False else None
    gsq = st([gc], 'sqcld', '( %s ^ 2 ) e. CC' % GN)
    a2 = st([st([gc, muc], 'sqmuld',
                '( ( %s x. ( mmu ` N ) ) ^ 2 ) = ( ( %s ^ 2 ) x. ( ( mmu ` N ) ^ 2 ) )'
                % (GN, GN)),
             st([st([musq], 'oveq2d',
                    '( ( %s ^ 2 ) x. ( ( mmu ` N ) ^ 2 ) ) = ( ( %s ^ 2 ) x. 1 )' % (GN, GN)),
                 st([gsq], 'mulridd', '( ( %s ^ 2 ) x. 1 ) = ( %s ^ 2 )' % (GN, GN))], 'eqtrd',
                '( ( %s ^ 2 ) x. ( ( mmu ` N ) ^ 2 ) ) = ( %s ^ 2 )' % (GN, GN))], 'eqtrd',
             '( ( %s x. ( mmu ` N ) ) ^ 2 ) = ( %s ^ 2 )' % (GN, GN))
    ssq = st([sc], 'sqcld', '( ( 1 / %s ) ^ 2 ) e. CC' % SS())
    a3 = st([a1, st([a2], 'oveq1d',
                    '( ( ( %s x. ( mmu ` N ) ) ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) ) = '
                    '( ( %s ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) )' % (GN, SS(), GN, SS()))], 'eqtrd',
             '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) )' % (GG, GN, SS()))
    b1 = st([st([a3], 'oveq2d',
                '( ( 1 / %s ) x. ( %s ^ 2 ) ) = '
                '( ( 1 / %s ) x. ( ( %s ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) ) )'
                % (GN, GG, GN, GN, SS())),
             st([st([igc, gsq, ssq], 'mulassd',
                    '( ( ( 1 / %s ) x. ( %s ^ 2 ) ) x. ( ( 1 / %s ) ^ 2 ) ) = '
                    '( ( 1 / %s ) x. ( ( %s ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) ) )'
                    % (GN, GN, SS(), GN, GN, SS()))], 'eqcomd',
                '( ( 1 / %s ) x. ( ( %s ^ 2 ) x. ( ( 1 / %s ) ^ 2 ) ) ) = '
                '( ( ( 1 / %s ) x. ( %s ^ 2 ) ) x. ( ( 1 / %s ) ^ 2 ) )'
                % (GN, GN, SS(), GN, GN, SS()))], 'eqtrd',
             '( ( 1 / %s ) x. ( %s ^ 2 ) ) = '
             '( ( ( 1 / %s ) x. ( %s ^ 2 ) ) x. ( ( 1 / %s ) ^ 2 ) )' % (GN, GG, GN, GN, SS()))
    rid = st([st([st([st([gc, gne], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (GN, GN)),
                     w.inst('recid2')], 'syl', '( ( 1 / %s ) x. %s ) = 1' % (GN, GN))], 'oveq1d',
                 '( ( ( 1 / %s ) x. %s ) x. %s ) = ( 1 x. %s )' % (GN, GN, GN, GN)),
              st([gc], 'mullidd', '( 1 x. %s ) = %s' % (GN, GN))], 'eqtrd',
             '( ( ( 1 / %s ) x. %s ) x. %s ) = %s' % (GN, GN, GN, GN))
    b2 = st([st([st([gc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (GN, GN, GN))], 'oveq2d',
                '( ( 1 / %s ) x. ( %s ^ 2 ) ) = ( ( 1 / %s ) x. ( %s x. %s ) )'
                % (GN, GN, GN, GN, GN)),
             st([st([st([igc, gc, gc], 'mulassd',
                        '( ( ( 1 / %s ) x. %s ) x. %s ) = ( ( 1 / %s ) x. ( %s x. %s ) )'
                        % (GN, GN, GN, GN, GN, GN))], 'eqcomd',
                    '( ( 1 / %s ) x. ( %s x. %s ) ) = ( ( ( 1 / %s ) x. %s ) x. %s )'
                    % (GN, GN, GN, GN, GN, GN)), rid], 'eqtrd',
                '( ( 1 / %s ) x. ( %s x. %s ) ) = %s' % (GN, GN, GN, GN))], 'eqtrd',
             '( ( 1 / %s ) x. ( %s ^ 2 ) ) = %s' % (GN, GN, GN))
    alg = st([b1, st([b2], 'oveq1d',
                     '( ( ( 1 / %s ) x. ( %s ^ 2 ) ) x. ( ( 1 / %s ) ^ 2 ) ) = '
                     '( %s x. ( ( 1 / %s ) ^ 2 ) )' % (GN, GN, SS(), GN, SS()))], 'eqtrd',
              '( ( 1 / %s ) x. ( %s ^ 2 ) ) = ( %s x. ( ( 1 / %s ) ^ 2 ) )'
              % (GN, GG, GN, SS()))
    # ---- assemble
    ifeq = st([alg], 'ifeq1d',
              'if ( %s , ( ( 1 / %s ) x. ( %s ^ 2 ) ) , 0 ) = '
              'if ( %s , ( %s x. ( ( 1 / %s ) ^ 2 ) ) , 0 )' % (COND, GN, GG, COND, GN, SS()))
    last = st([st([ssq, w.inst('ifmulz')], 'syl',
                  '( %s x. ( ( 1 / %s ) ^ 2 ) ) = if ( %s , ( %s x. ( ( 1 / %s ) ^ 2 ) ) , 0 )'
                  % (SST, SS(), COND, GN, SS()))], 'eqcomd',
              'if ( %s , ( %s x. ( ( 1 / %s ) ^ 2 ) ) , 0 ) = ( %s x. ( ( 1 / %s ) ^ 2 ) )'
              % (COND, GN, SS(), SST, SS()))
    w.qed([st([sq], 'oveq2d',
              '( ( 1 / %s ) x. ( %s ^ 2 ) ) = ( ( 1 / %s ) x. if ( %s , ( %s ^ 2 ) , 0 ) )'
              % (GN, INS, GN, COND, GG)),
           st([pull, st([ifeq, last], 'eqtrd',
                        'if ( %s , ( ( 1 / %s ) x. ( %s ^ 2 ) ) , 0 ) = '
                        '( %s x. ( ( 1 / %s ) ^ 2 ) )' % (COND, GN, GG, SST, SS()))], 'eqtrd',
              '( ( 1 / %s ) x. if ( %s , ( %s ^ 2 ) , 0 ) ) = ( %s x. ( ( 1 / %s ) ^ 2 ) )'
              % (GN, COND, GG, SST, SS()))], 'eqtrd',
          '( %s -> ( ( 1 / %s ) x. ( %s ^ 2 ) ) = ( %s x. ( ( 1 / %s ) ^ 2 ) ) )'
          % (A, GN, INS, SST, SS()))
    return w



def mpmev():
    w = W('mpmev', 'The diagonalised Selberg main term evaluates to one over the bounding sum.')
    d = shsteps(w, SH, ())
    st = d['st']
    DVx = DV('P')
    SST = SSTERM('n')
    RT = '( %s x. ( ( 1 / %s ) ^ 2 ) )' % (SST, SS())
    srp = st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())
    ssc = st([srp], 'rpcnd', '%s e. CC' % SS())
    ssn = st([srp], 'rpne0d', '%s =/= 0' % SS())
    sc = st([st([srp], 'rpreccld', '( 1 / %s ) e. RR+' % SS())], 'rpcnd',
            '( 1 / %s ) e. CC' % SS())
    ssq = st([sc], 'sqcld', '( ( 1 / %s ) ^ 2 ) e. CC' % SS())
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVx)
    AN = '( %s /\\ n e. %s )' % (SH, DVx)
    dn = dvpel(w, AN, 'n', d['pnn'])
    sn = dn['st']
    gtn = sn([lift(w, d['sh'], AN), sn([dn['nn'], dn['dP']], 'jca', '( n e. NN /\\ n || P )'),
              w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('n'))
    sstc = sn([sn([gtn], 'rpcnd', '%s e. CC' % GT('n')),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % AN)], 'ifcld', '%s e. CC' % SST)
    mul = st([finP, ssq, sstc], 'fsummulc1',
             '( sum_ n e. %s %s x. ( ( 1 / %s ) ^ 2 ) ) = sum_ n e. %s %s'
             % (DVx, SST, SS(), DVx, RT))
    idn = w.s([], 'id', '( n = l -> n = l )')
    hcb, new = w.congr(SST, {'n': 'l'}, 'n = l', {'n': idn})
    cbv = st([w.s([hcb], 'cbvsumv', 'sum_ n e. %s %s = %s' % (DVx, SST, SS()))], 'a1i',
             'sum_ n e. %s %s = %s' % (DVx, SST, SS()))
    alg = st([st([st([ssq], 'oveq2d' if False else 'id', 'x = x')], 'id', 'x = x')], 'id',
             'x = x') if False else None
    e1 = st([st([sc], 'sqvald', '( ( 1 / %s ) ^ 2 ) = ( ( 1 / %s ) x. ( 1 / %s ) )'
                 % (SS(), SS(), SS()))], 'oveq2d',
            '( %s x. ( ( 1 / %s ) ^ 2 ) ) = ( %s x. ( ( 1 / %s ) x. ( 1 / %s ) ) )'
            % (SS(), SS(), SS(), SS(), SS()))
    e2 = st([st([ssc, sc, sc], 'mulassd',
                '( ( %s x. ( 1 / %s ) ) x. ( 1 / %s ) ) = ( %s x. ( ( 1 / %s ) x. ( 1 / %s ) ) )'
                % (SS(), SS(), SS(), SS(), SS(), SS()))], 'eqcomd',
            '( %s x. ( ( 1 / %s ) x. ( 1 / %s ) ) ) = ( ( %s x. ( 1 / %s ) ) x. ( 1 / %s ) )'
            % (SS(), SS(), SS(), SS(), SS(), SS()))
    e3 = st([st([st([st([ssc, ssn], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (SS(), SS())),
                    w.inst('recid')], 'syl', '( %s x. ( 1 / %s ) ) = 1' % (SS(), SS()))],
                'oveq1d',
                '( ( %s x. ( 1 / %s ) ) x. ( 1 / %s ) ) = ( 1 x. ( 1 / %s ) )'
                % (SS(), SS(), SS(), SS())),
             st([sc], 'mullidd', '( 1 x. ( 1 / %s ) ) = ( 1 / %s )' % (SS(), SS()))], 'eqtrd',
            '( ( %s x. ( 1 / %s ) ) x. ( 1 / %s ) ) = ( 1 / %s )' % (SS(), SS(), SS(), SS()))
    fin = st([e1, st([e2, e3], 'eqtrd',
                     '( %s x. ( ( 1 / %s ) x. ( 1 / %s ) ) ) = ( 1 / %s )'
                     % (SS(), SS(), SS(), SS()))], 'eqtrd',
             '( %s x. ( ( 1 / %s ) ^ 2 ) ) = ( 1 / %s )' % (SS(), SS(), SS()))
    w.qed([st([mul], 'eqcomd',
              'sum_ n e. %s %s = ( sum_ n e. %s %s x. ( ( 1 / %s ) ^ 2 ) )'
              % (DVx, RT, DVx, SST, SS())),
           st([st([cbv], 'oveq1d',
                  '( sum_ n e. %s %s x. ( ( 1 / %s ) ^ 2 ) ) = ( %s x. ( ( 1 / %s ) ^ 2 ) )'
                  % (DVx, SST, SS(), SS(), SS())), fin], 'eqtrd',
              '( sum_ n e. %s %s x. ( ( 1 / %s ) ^ 2 ) ) = ( 1 / %s )' % (DVx, SST, SS(), SS()))],
          'eqtrd', '( %s -> sum_ n e. %s %s = ( 1 / %s ) )' % (SH, DVx, RT, SS()))
    return w



def mpmain():
    w = W('mpmain', 'The main term of the Selberg Lambda squared sieve is one over the '
                    'bounding sum.')
    d = shsteps(w, SH, ())
    st = d['st']
    DVy, DVx = DV('P', 'y'), DV('P')
    MPFd = MPF('d')
    MPd = MP('d', d='u', e='e')
    BF = 'if ( n || j , ( ( V ` j ) x. ( %s ` j ) ) , 0 )' % LWF
    BW = 'if ( n || j , ( ( V ` j ) x. %s ) , 0 )' % LW('j')
    INSy = 'sum_ j e. %s %s' % (DVy, BF)
    INSx = 'sum_ j e. %s %s' % (DVx, BW)
    RTy = '( ( 1 / %s ) x. ( %s ^ 2 ) )' % (GT('n'), INSy)
    RTx = '( ( 1 / %s ) x. ( %s ^ 2 ) )' % (GT('n'), INSx)
    ST = '( %s x. ( ( 1 / %s ) ^ 2 ) )' % (SSTERM('n'), SS())
    eqset = w.s([w.s([], 'breq1', '( x = y -> ( x || P <-> y || P ) )')], 'cbvrabv',
                '%s = %s' % (DVx, DVy))
    eqsetr = w.s([eqset], 'eqcomi', '%s = %s' % (DVy, DVx))
    # ---- the diagonalisation at the Selberg weights
    lf = st([d['sh'], w.inst('lwff')], 'syl', '%s : NN --> RR' % LWF)
    gen = st([st([d['sh'], lf], 'jca', '( %s /\\ %s : NN --> RR )' % (SH, LWF)),
              w.inst('mpgen')], 'syl',
             'sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ n e. %s %s' % (DVy, MPFd, DVy, RTy))
    # ---- the left side
    l1 = st([st([eqset], 'a1i', '%s = %s' % (DVx, DVy))], 'sumeq1d',
            'sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ d e. %s ( %s x. ( V ` d ) )'
            % (DVx, MPd, DVy, MPd))
    AD = '( %s /\\ d e. %s )' % (SH, DVy)
    sd = mkst(w, AD)
    eld = w.s([w.s([], 'breq1', '( y = d -> ( y || P <-> d || P ) )')], 'elrab',
              '( d e. %s <-> ( d e. NN /\\ d || P ) )' % DVy)
    dc = sd([sd([eld], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || P ) )' % DVy),
             sd([], 'simpr', 'd e. %s' % DVy)], 'mpbid', '( d e. NN /\\ d || P )')
    dnn = sd([dc], 'simpld', 'd e. NN')
    ddp = sd([dc], 'simprd', 'd || P')
    fv = sd([sd([lift(w, d['sh'], AD), dnn], 'jca', '( %s /\\ d e. NN )' % SH),
             w.inst('mpfv')], 'syl', '%s = %s' % (MPF('d'), MPd))
    l2 = st([sd([fv], 'oveq1d', '( %s x. ( V ` d ) ) = ( %s x. ( V ` d ) )' % (MPFd, MPd))],
            'sumeq2dv',
            'sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ d e. %s ( %s x. ( V ` d ) )'
            % (DVy, MPFd, DVy, MPd))
    # ---- the right side
    AN = '( %s /\\ n e. %s )' % (SH, DVy)
    sn = mkst(w, AN)
    eln = w.s([w.s([], 'breq1', '( y = n -> ( y || P <-> n || P ) )')], 'elrab',
              '( n e. %s <-> ( n e. NN /\\ n || P ) )' % DVy)
    nc = sn([sn([eln], 'a1i', '( n e. %s <-> ( n e. NN /\\ n || P ) )' % DVy),
             sn([], 'simpr', 'n e. %s' % DVy)], 'mpbid', '( n e. NN /\\ n || P )')
    nnn = sn([nc], 'simpld', 'n e. NN')
    ndp = sn([nc], 'simprd', 'n || P')
    j1 = sn([sn([eqsetr], 'a1i', '%s = %s' % (DVy, DVx))], 'sumeq1d',
            '%s = sum_ j e. %s %s' % (INSy, DVx, BF))
    ANJ = '( %s /\\ j e. %s )' % (AN, DVx)
    sj = mkst(w, ANJ)
    elj = w.s([w.s([], 'breq1', '( x = j -> ( x || P <-> j || P ) )')], 'elrab',
              '( j e. %s <-> ( j e. NN /\\ j || P ) )' % DVx)
    jnn = sj([sj([sj([elj], 'a1i', '( j e. %s <-> ( j e. NN /\\ j || P ) )' % DVx),
                  sj([], 'simpr', 'j e. %s' % DVx)], 'mpbid', '( j e. NN /\\ j || P )')],
             'simpld', 'j e. NN')
    jfv = sj([sj([lift(w, d['sh'], ANJ), jnn], 'jca', '( %s /\\ j e. NN )' % SH),
              w.inst('lwfv')], 'syl', '( %s ` j ) = %s' % (LWF, LW('j')))
    jbod = sj([sj([jfv], 'oveq2d',
                  '( ( V ` j ) x. ( %s ` j ) ) = ( ( V ` j ) x. %s )' % (LWF, LW('j')))],
              'ifeq1d', '%s = %s' % (BF, BW))
    j2 = sn([jbod], 'sumeq2dv', 'sum_ j e. %s %s = %s' % (DVx, BF, INSx))
    ins = sn([j1, j2], 'eqtrd', '%s = %s' % (INSy, INSx))
    rt = sn([sn([sn([ins], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (INSy, INSx))], 'oveq2d',
                '%s = %s' % (RTy, RTx)),
             sn([sn([lift(w, d['sh'], AN), sn([nnn, ndp], 'jca', '( n e. NN /\\ n || P )')],
                    'jca', '( %s /\\ ( n e. NN /\\ n || P ) )' % SH),
                 w.inst('mpmss')], 'syl', '%s = %s' % (RTx, ST))], 'eqtrd', '%s = %s' % (RTy, ST))
    r1 = st([rt], 'sumeq2dv', 'sum_ n e. %s %s = sum_ n e. %s %s' % (DVy, RTy, DVy, ST))
    r2 = st([st([eqsetr], 'a1i', '%s = %s' % (DVy, DVx))], 'sumeq1d',
            'sum_ n e. %s %s = sum_ n e. %s %s' % (DVy, ST, DVx, ST))
    ev = st([d['sh'], w.inst('mpmev')], 'syl', 'sum_ n e. %s %s = ( 1 / %s )' % (DVx, ST, SS()))
    left = st([l1, st([l2], 'eqcomd',
                      'sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ d e. %s ( %s x. ( V ` d ) )'
                      % (DVy, MPd, DVy, MPFd))], 'eqtrd',
              'sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ d e. %s ( %s x. ( V ` d ) )'
              % (DVx, MPd, DVy, MPFd))
    right = st([r1, st([r2, ev], 'eqtrd',
                       'sum_ n e. %s %s = ( 1 / %s )' % (DVy, ST, SS()))], 'eqtrd',
               'sum_ n e. %s %s = ( 1 / %s )' % (DVy, RTy, SS()))
    w.qed([left, st([gen, right], 'eqtrd',
                    'sum_ d e. %s ( %s x. ( V ` d ) ) = ( 1 / %s )' % (DVy, MPFd, SS()))],
          'eqtrd', '( %s -> sum_ d e. %s ( %s x. ( V ` d ) ) = ( 1 / %s ) )'
          % (SH, DVx, MPd, SS()))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['musq1', 'ifsq']:
        globals()[f]().run()
