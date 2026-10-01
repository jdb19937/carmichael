"""Sortie v2c: the bound on the Selberg weights.

mucanc  the commutative cancellation behind the weight identity
muabs1  the Moebius value at a squarefree argument has absolute value one
lwmu1   ( lambda_D mu ( D ) ) SS as a truncated divisor sum
gcdfib  the gcd fibre of the bounding sum
lwmuss  ( lambda_D mu ( D ) ) SS <_ SS
lwabs   | lambda_D | <_ 1
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from v2c_lib import *
from cl import lift
from c0lib import runh, hyp


def mucanc():
    w = W('mucanc', 'Cancellation of a squared sign and a reciprocal in a product of five '
                    'factors.')
    h1 = hyp(w, '1', 'mucanc.1', '( ph -> A e. CC )')
    h2 = hyp(w, '2', 'mucanc.2', '( ph -> A =/= 0 )')
    h3 = hyp(w, '3', 'mucanc.3', '( ph -> B e. CC )')
    h4 = hyp(w, '4', 'mucanc.4', '( ph -> B =/= 0 )')
    h5 = hyp(w, '5', 'mucanc.5', '( ph -> C e. CC )')
    h6 = hyp(w, '6', 'mucanc.6', '( ph -> D e. CC )')
    h7 = hyp(w, '7', 'mucanc.7', '( ph -> E e. CC )')
    h8 = hyp(w, '8', 'mucanc.8', '( ph -> ( D x. D ) = 1 )')
    h9 = hyp(w, '9', 'mucanc.9', '( ph -> ( A x. C ) = ( ( ( 1 / B ) x. D ) x. E ) )')
    st = mkst(w, 'ph')
    U = '( 1 / B )'
    uc = st([st([h3, h4], 'jca', '( B e. CC /\\ B =/= 0 )'), w.inst('reccl')], 'syl',
            '%s e. CC' % U)
    iac = st([st([h1, h2], 'jca', '( A e. CC /\\ A =/= 0 )'), w.inst('reccl')], 'syl',
             '( 1 / A ) e. CC')
    cd = st([h5, h6], 'mulcld', '( C x. D ) e. CC')
    cdb = st([cd, h3], 'mulcld', '( ( C x. D ) x. B ) e. CC')

    def recmul(av, ac, ane, X, xc, recc):
        c1 = st([ac, xc], 'mulcld', '( %s x. %s ) e. CC' % (av, X))
        e1 = st([recc, c1], 'mulcomd',
                '( ( 1 / %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( 1 / %s ) )'
                % (av, av, X, av, X, av))
        e2 = st([st([c1, ac, ane], 'divrecd',
                    '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) x. ( 1 / %s ) )'
                    % (av, X, av, av, X, av))], 'eqcomd',
                '( ( %s x. %s ) x. ( 1 / %s ) ) = ( ( %s x. %s ) / %s )'
                % (av, X, av, av, X, av))
        e3 = st([xc, ac, ane], 'divcan3d', '( ( %s x. %s ) / %s ) = %s' % (av, X, av, X))
        return st([e1, st([e2, e3], 'eqtrd',
                          '( ( %s x. %s ) x. ( 1 / %s ) ) = %s' % (av, X, av, X))], 'eqtrd',
                  '( ( 1 / %s ) x. ( %s x. %s ) ) = %s' % (av, av, X, X))

    outer = recmul('A', h1, h2, '( ( C x. D ) x. B )', cdb, iac)
    # ---- A x. ( ( C x. D ) x. B ) = E
    a1 = st([st([h1, cd, h3], 'mulassd',
                '( ( A x. ( C x. D ) ) x. B ) = ( A x. ( ( C x. D ) x. B ) )')], 'eqcomd',
            '( A x. ( ( C x. D ) x. B ) ) = ( ( A x. ( C x. D ) ) x. B )')
    a2 = st([st([st([h1, h5, h6], 'mulassd',
                    '( ( A x. C ) x. D ) = ( A x. ( C x. D ) )')], 'eqcomd',
                '( A x. ( C x. D ) ) = ( ( A x. C ) x. D )')], 'oveq1d',
            '( ( A x. ( C x. D ) ) x. B ) = ( ( ( A x. C ) x. D ) x. B )')
    a3 = st([st([h9], 'oveq1d',
                '( ( A x. C ) x. D ) = ( ( ( ( 1 / B ) x. D ) x. E ) x. D )')], 'oveq1d',
            '( ( ( A x. C ) x. D ) x. B ) = ( ( ( ( ( 1 / B ) x. D ) x. E ) x. D ) x. B )')
    udc = st([uc, h6], 'mulcld', '( %s x. D ) e. CC' % U)
    x1c = st([udc, h7], 'mulcld', '( ( %s x. D ) x. E ) e. CC' % U)
    a4 = st([x1c, h6, h3], 'mulassd',
            '( ( ( ( %s x. D ) x. E ) x. D ) x. B ) = '
            '( ( ( %s x. D ) x. E ) x. ( D x. B ) )' % (U, U))
    a5 = st([udc, h7, h6, h3], 'mul4d',
            '( ( ( %s x. D ) x. E ) x. ( D x. B ) ) = '
            '( ( ( %s x. D ) x. D ) x. ( E x. B ) )' % (U, U))
    a6 = st([st([st([uc, h6, h6], 'mulassd',
                    '( ( %s x. D ) x. D ) = ( %s x. ( D x. D ) )' % (U, U)),
                 st([h8], 'oveq2d', '( %s x. ( D x. D ) ) = ( %s x. 1 )' % (U, U))], 'eqtrd',
                '( ( %s x. D ) x. D ) = ( %s x. 1 )' % (U, U)),
             st([uc], 'mulridd', '( %s x. 1 ) = %s' % (U, U))], 'eqtrd',
            '( ( %s x. D ) x. D ) = %s' % (U, U))
    a7 = st([a6], 'oveq1d',
            '( ( ( %s x. D ) x. D ) x. ( E x. B ) ) = ( %s x. ( E x. B ) )' % (U, U))
    a8 = st([st([h7, h3], 'mulcomd', '( E x. B ) = ( B x. E )')], 'oveq2d',
            '( %s x. ( E x. B ) ) = ( %s x. ( B x. E ) )' % (U, U))
    a9 = recmul('B', h3, h4, 'E', h7, uc)
    right = st([st([a4, a5], 'eqtrd',
                   '( ( ( ( %s x. D ) x. E ) x. D ) x. B ) = '
                   '( ( ( %s x. D ) x. D ) x. ( E x. B ) )' % (U, U)),
                st([st([a7, a8], 'eqtrd',
                       '( ( ( %s x. D ) x. D ) x. ( E x. B ) ) = ( %s x. ( B x. E ) )'
                       % (U, U)), a9], 'eqtrd',
                   '( ( ( %s x. D ) x. D ) x. ( E x. B ) ) = E' % U)], 'eqtrd',
               '( ( ( ( %s x. D ) x. E ) x. D ) x. B ) = E' % U)
    ae = st([st([a1, a2], 'eqtrd',
                '( A x. ( ( C x. D ) x. B ) ) = ( ( ( A x. C ) x. D ) x. B )'),
             st([a3, right], 'eqtrd',
                '( ( ( A x. C ) x. D ) x. B ) = E')], 'eqtrd',
            '( A x. ( ( C x. D ) x. B ) ) = E')
    w.qed([st([outer], 'eqcomd',
              '( ( C x. D ) x. B ) = ( ( 1 / A ) x. ( A x. ( ( C x. D ) x. B ) ) )'),
           st([ae], 'oveq2d',
              '( ( 1 / A ) x. ( A x. ( ( C x. D ) x. B ) ) ) = ( ( 1 / A ) x. E )')], 'eqtrd',
          '( ph -> ( ( C x. D ) x. B ) = ( ( 1 / A ) x. E ) )')
    return w


def muabs1():
    w = W('muabs1', 'The Moebius value at a squarefree argument has absolute value one.')
    A = '( N e. NN /\\ ( mmu ` N ) =/= 0 )'
    st = mkst(w, A)
    nnn = w.s([], 'simpl', '( %s -> N e. NN )' % A)
    OMN = OM('N', 'p')
    fin = st([nnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('N', 'p'))
    k0 = st([fin, w.inst('hashcl')], 'syl', '%s e. NN0' % OMN)
    kz = st([k0], 'nn0zd', '%s e. ZZ' % OMN)
    mv = st([w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('muval2')], 'syl',
            '( mmu ` N ) = ( -u 1 ^ %s )' % OMN)
    m1c = st([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '-u 1 e. CC')
    ae = st([m1c, k0, w.inst('absexp')], 'syl2anc',
            '( abs ` ( -u 1 ^ %s ) ) = ( ( abs ` -u 1 ) ^ %s )' % (OMN, OMN))
    an = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('absneg')], 'ax-mp',
                  '( abs ` -u 1 ) = ( abs ` 1 )'),
              w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtri', '( abs ` -u 1 ) = 1')
    ax = st([st([an], 'a1i', '( abs ` -u 1 ) = 1')], 'oveq1d',
            '( ( abs ` -u 1 ) ^ %s ) = ( 1 ^ %s )' % (OMN, OMN))
    one = st([kz, w.inst('1exp')], 'syl', '( 1 ^ %s ) = 1' % OMN)
    w.qed([st([mv], 'fveq2d', '( abs ` ( mmu ` N ) ) = ( abs ` ( -u 1 ^ %s ) )' % OMN),
           st([ae, st([ax, one], 'eqtrd', '( ( abs ` -u 1 ) ^ %s ) = 1' % OMN)], 'eqtrd',
              '( abs ` ( -u 1 ^ %s ) ) = 1' % OMN)], 'eqtrd',
          '( %s -> ( abs ` ( mmu ` N ) ) = 1 )' % A)
    return w



DVP = DV('P')


def TD(D, l='l'):
    return ('sum_ %s e. %s if ( ( %s || %s /\\ ( %s ^ 2 ) <_ Y ) , %s , 0 )'
            % (l, DVP, D, l, l, GT(l)))


def lwmu1():
    w = W('lwmu1', 'The Selberg weight times the Moebius value times the bounding sum is the '
                   'truncated divisor sum above D divided by the density at D.')
    A = '( %s /\\ ( D e. NN /\\ D || P ) )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    shd = st([d['sh'], dnn], 'jca', '( %s /\\ D e. NN )' % SH)
    vrp = st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\\ D || P )'), w.inst('vdrp')],
             'syl2anc', '( V ` D ) e. RR+')
    srp = st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())
    lwc = st([st([shd, w.inst('lwre')], 'syl', '%s e. RR' % LW('D'))], 'recnd',
             '%s e. CC' % LW('D'))
    muc = st([st([dnn, w.inst('mucl')], 'syl', '( mmu ` D ) e. ZZ')], 'zcnd', '( mmu ` D ) e. CC')
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    AL = '( %s /\\ l e. %s )' % (A, DVP)
    dl = dvpel(w, AL, 'l', d['pnn'])
    sl = dl['st']
    gtl = sl([lift(w, d['sh'], AL), sl([dl['nn'], dl['dP']], 'jca', '( l e. NN /\\ l || P )'),
              w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('l'))
    bodyc = sl([sl([gtl], 'rpcnd', '%s e. CC' % GT('l')),
                w.s([], '0cnd', '( %s -> 0 e. CC )' % AL)], 'ifcld',
               'if ( ( D || l /\\ ( l ^ 2 ) <_ Y ) , %s , 0 ) e. CC' % GT('l'))
    tdc = st([finP, bodyc], 'fsumcl', '%s e. CC' % TD('D'))
    nsqf = st([st([st([d['pnn'], dnn, ddp], '3jca', '( P e. NN /\\ D e. NN /\\ D || P )'),
                   w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` D ) =/= 0 )'),
               d['psqf']], 'mpd', '( mmu ` D ) =/= 0')
    musq = st([st([st([muc], 'sqvald', '( ( mmu ` D ) ^ 2 ) = ( ( mmu ` D ) x. ( mmu ` D ) )')],
                  'eqcomd', '( ( mmu ` D ) x. ( mmu ` D ) ) = ( ( mmu ` D ) ^ 2 )'),
               st([st([dnn, nsqf], 'jca', '( D e. NN /\\ ( mmu ` D ) =/= 0 )'),
                   w.inst('musq1')], 'syl', '( ( mmu ` D ) ^ 2 ) = 1')], 'eqtrd',
              '( ( mmu ` D ) x. ( mmu ` D ) ) = 1')
    ld = st([shd, w.inst('lwdvds')], 'syl',
            '( ( V ` D ) x. %s ) = ( ( ( 1 / %s ) x. ( mmu ` D ) ) x. %s )'
            % (LW('D'), SS(), TD('D')))
    w.qed([st([vrp], 'rpcnd', '( V ` D ) e. CC'), st([vrp], 'rpne0d', '( V ` D ) =/= 0'),
           st([srp], 'rpcnd', '%s e. CC' % SS()), st([srp], 'rpne0d', '%s =/= 0' % SS()),
           lwc, muc, tdc, musq, ld], 'mucanc',
          '( %s -> ( ( %s x. ( mmu ` D ) ) x. %s ) = ( ( 1 / ( V ` D ) ) x. %s ) )'
          % (A, LW('D'), SS(), TD('D')))
    return w



AG = '( %s /\\ ( D e. NN /\\ D || P ) /\\ ( K e. NN /\\ K || D ) )' % SH
QQ = '( P / K )'
RR_ = '( D / K )'
DVQ = DV(QQ)
KM = '( K x. m )'
JM = '( j x. m )'
BMP = 'if ( ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , %s , 0 )' % (KM, GT('m'))
BM = 'if ( ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , %s , 0 )' % (KM, GT(KM))
CL = 'if ( ( K = ( D gcd l ) /\\ ( l ^ 2 ) <_ Y ) , %s , 0 )' % GT('l')
CJM = ('if ( ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) , %s , 0 )' % (JM, JM, GT(JM)))
AJ = 'if ( j = K , 1 , 0 )'


def gbase(w):
    """the shared facts under AG"""
    d = shsteps(w, AG, ((SH, 'simp1d'),))
    st = d['st']
    d['dnn'] = dnn = st([], 'simp2l', 'D e. NN')
    d['ddp'] = ddp = st([], 'simp2r', 'D || P')
    d['knn'] = knn = st([], 'simp3l', 'K e. NN')
    d['kdD'] = kdD = st([], 'simp3r', 'K || D')
    d['dz'] = dz = st([dnn], 'nnzd', 'D e. ZZ')
    d['kz'] = kz = st([knn], 'nnzd', 'K e. ZZ')
    d['pz'] = pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    d['kdP'] = kdP = st([st([st([kz, dz, pz], '3jca', '( K e. ZZ /\\ D e. ZZ /\\ P e. ZZ )'),
                            w.inst('dvdstr')], 'syl', '( ( K || D /\\ D || P ) -> K || P )'),
                        st([kdD, ddp], 'jca', '( K || D /\\ D || P )')], 'mpd', 'K || P')
    # the cofactor Q = P / K
    pcn = st([d['pnn']], 'nncnd', 'P e. CC')
    kcn = st([knn], 'nncnd', 'K e. CC')
    kne = st([knn], 'nnne0d', 'K =/= 0')
    d['qnn'] = qnn = st([st([d['pnn'], knn, w.inst('nndivdvds')], 'syl2anc',
                            '( K || P <-> %s e. NN )' % QQ), kdP], 'mpbid', '%s e. NN' % QQ)
    d['kq'] = kq = st([pcn, kcn, kne], 'divcan2d', '( K x. %s ) = P' % QQ)
    musq = st([st([kq], 'fveq2d', '( mmu ` ( K x. %s ) ) = ( mmu ` P )' % QQ), d['psqf']],
              'eqnetrd', '( mmu ` ( K x. %s ) ) =/= 0' % QQ)
    d['cop'] = st([st([knn, qnn, musq], '3jca',
                      '( K e. NN /\\ %s e. NN /\\ ( mmu ` ( K x. %s ) ) =/= 0 )' % (QQ, QQ)),
                   w.inst('sqfcop')], 'syl', '( K gcd %s ) = 1' % QQ)
    d['qz'] = qz = st([qnn], 'nnzd', '%s e. ZZ' % QQ)
    d['qdp'] = st([st([st([kz, qz], 'jca', '( K e. ZZ /\\ %s e. ZZ )' % QQ),
                       w.inst('dvdsmul2')], 'syl', '%s || ( K x. %s )' % (QQ, QQ)), kq],
                  'breqtrd', '%s || P' % QQ)
    # the cofactor R = D / K
    dcn = st([dnn], 'nncnd', 'D e. CC')
    d['rnn'] = rnn = st([st([dnn, knn, w.inst('nndivdvds')], 'syl2anc',
                            '( K || D <-> %s e. NN )' % RR_), kdD], 'mpbid', '%s e. NN' % RR_)
    d['kr'] = kr = st([dcn, kcn, kne], 'divcan2d', '( K x. %s ) = D' % RR_)
    dsqf = st([st([st([d['pnn'], dnn, ddp], '3jca', '( P e. NN /\\ D e. NN /\\ D || P )'),
                   w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` D ) =/= 0 )'),
               d['psqf']], 'mpd', '( mmu ` D ) =/= 0')
    rsq = st([st([kr], 'fveq2d', '( mmu ` ( K x. %s ) ) = ( mmu ` D )' % RR_), dsqf],
             'eqnetrd', '( mmu ` ( K x. %s ) ) =/= 0' % RR_)
    d['copr'] = st([st([knn, rnn, rsq], '3jca',
                       '( K e. NN /\\ %s e. NN /\\ ( mmu ` ( K x. %s ) ) =/= 0 )'
                       % (RR_, RR_)), w.inst('sqfcop')], 'syl', '( K gcd %s ) = 1' % RR_)
    d['rz'] = st([rnn], 'nnzd', '%s e. ZZ' % RR_)
    d['finP'] = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    d['finQ'] = st([qnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVQ)
    return d


def mfacts(w, d, ante, mem=None):
    """facts about m e. DV ( Q ) under `ante`"""
    sb = mkst(w, ante)
    if mem is None:
        mem = sb([], 'simpr', 'm e. %s' % DVQ)
    elm = w.s([w.s([], 'breq1', '( x = m -> ( x || %s <-> m || %s ) )' % (QQ, QQ))], 'elrab',
              '( m e. %s <-> ( m e. NN /\\ m || %s ) )' % (DVQ, QQ))
    mc = sb([sb([elm], 'a1i', '( m e. %s <-> ( m e. NN /\\ m || %s ) )' % (DVQ, QQ)),
             mem], 'mpbid', '( m e. NN /\\ m || %s )' % QQ)
    mnn = sb([mc], 'simpld', 'm e. NN')
    mdQ = sb([mc], 'simprd', 'm || %s' % QQ)
    mz = sb([mnn], 'nnzd', 'm e. ZZ')
    mdP = sb([sb([sb([mz, lift(w, d['qz'], ante), lift(w, d['pz'], ante)], '3jca',
                     '( m e. ZZ /\\ %s e. ZZ /\\ P e. ZZ )' % QQ), w.inst('dvdstr')], 'syl',
                  '( ( m || %s /\\ %s || P ) -> m || P )' % (QQ, QQ)),
              sb([mdQ, lift(w, d['qdp'], ante)], 'jca', '( m || %s /\\ %s || P )' % (QQ, QQ))],
             'mpd', 'm || P')
    kgm = sb([sb([sb([lift(w, d['kz'], ante), mz, lift(w, d['qz'], ante)], '3jca',
                     '( K e. ZZ /\\ m e. ZZ /\\ %s e. ZZ )' % QQ),
                  sb([lift(w, d['cop'], ante), mdQ], 'jca',
                     '( ( K gcd %s ) = 1 /\\ m || %s )' % (QQ, QQ))], 'jca',
                 '( ( K e. ZZ /\\ m e. ZZ /\\ %s e. ZZ ) /\\ ( ( K gcd %s ) = 1 /\\ m || %s ) )'
                 % (QQ, QQ, QQ)), w.inst('rpdvds')], 'syl', '( K gcd m ) = 1')
    return {'st': sb, 'nn': mnn, 'z': mz, 'dQ': mdQ, 'dP': mdP, 'kgm': kgm}


def gfinner():
    w = W('gfinner', 'The inner sum of the gcd fibre runs over the divisors of P / K.')
    d = gbase(w)
    st = d['st']
    # ---- DV ( Q ) C_ DV ( P )
    AX = '( %s /\\ x e. NN )' % AG
    sx = mkst(w, AX)
    imp = sx([sx([sx([w.s([], 'simpr', '( %s -> x e. NN )' % AX)], 'nnzd', 'x e. ZZ'),
                  lift(w, d['qz'], AX), lift(w, d['pz'], AX)], '3jca',
                 '( x e. ZZ /\\ %s e. ZZ /\\ P e. ZZ )' % QQ), w.inst('dvdstr')], 'syl',
             '( ( x || %s /\\ %s || P ) -> x || P )' % (QQ, QQ))
    imp2 = w.s([lift(w, d['qdp'], AX), imp], 'mpan2d', '( %s -> ( x || %s -> x || P ) )'
               % (AX, QQ))
    sub = w.s([imp2], 'ss2rabdv', '( %s -> %s C_ %s )' % (AG, DVQ, DVP))
    # ---- the body is a complex number on DV ( Q )
    AM = '( %s /\\ m e. %s )' % (AG, DVQ)
    mf = mfacts(w, d, AM)
    sm = mf['st']
    gmc = sm([sm([lift(w, d['sh'], AM), sm([mf['nn'], mf['dP']], 'jca',
                                           '( m e. NN /\\ m || P )'), w.inst('gtrp')],
                 'syl2anc', '%s e. RR+' % GT('m'))], 'rpcnd', '%s e. CC' % GT('m'))
    bodyc = sm([gmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % AM)], 'ifcld', '%s e. CC' % BMP)
    # ---- the body vanishes off DV ( Q )
    AE = '( %s /\\ m e. ( %s \\ %s ) )' % (AG, DVP, DVQ)
    se = mkst(w, AE)
    mdif = se([], 'simpr', 'm e. ( %s \\ %s )' % (DVP, DVQ))
    mdvp = se([mdif, w.inst('eldifi')], 'syl', 'm e. %s' % DVP)
    mnotq = se([mdif, w.inst('eldifn')], 'syl', '-. m e. %s' % DVQ)
    mnn2 = se([mdvp, w.inst('elrabi')], 'syl', 'm e. NN')
    mz2 = se([mnn2], 'nnzd', 'm e. ZZ')
    mdP2 = se([se([mdvp], 'elrab', '( m e. %s <-> ( m e. NN /\\ m || P ) )' % DVP)], 'id',
              'x = x') if False else None
    elmp = w.s([w.s([], 'breq1', '( x = m -> ( x || P <-> m || P ) )')], 'elrab',
               '( m e. %s <-> ( m e. NN /\\ m || P ) )' % DVP)
    mdP2 = se([se([se([elmp], 'a1i', '( m e. %s <-> ( m e. NN /\\ m || P ) )' % DVP), mdvp],
                  'mpbid', '( m e. NN /\\ m || P )')], 'simprd', 'm || P')
    elmq = w.s([w.s([], 'breq1', '( x = m -> ( x || %s <-> m || %s ) )' % (QQ, QQ))], 'elrab',
               '( m e. %s <-> ( m e. NN /\\ m || %s ) )' % (DVQ, QQ))
    bi2 = se([se([elmq], 'a1i', '( m e. %s <-> ( m e. NN /\\ m || %s ) )' % (DVQ, QQ)),
              se([mnn2], 'biantrurd', '( m || %s <-> ( m e. NN /\\ m || %s ) )' % (QQ, QQ))],
             'bitr4d', '( m e. %s <-> m || %s )' % (DVQ, QQ))
    nmq = se([mnotq, bi2], 'mtbid', '-. m || %s' % QQ)
    # from ( m gcd D ) = 1 derive m || Q
    AEC = '( %s /\\ ( m gcd D ) = 1 )' % AE
    sc = mkst(w, AEC)
    mgk = sc([sc([sc([sc([mz2], 'adantr', 'm e. ZZ'), lift(w, d['kz'], AEC),
                      lift(w, d['dz'], AEC)], '3jca',
                     '( m e. ZZ /\\ K e. ZZ /\\ D e. ZZ )'),
                  sc([sc([], 'simpr', '( m gcd D ) = 1'),
                      lift(w, d['kdD'], AEC)], 'jca',
                     '( ( m gcd D ) = 1 /\\ K || D )')], 'jca',
                 '( ( m e. ZZ /\\ K e. ZZ /\\ D e. ZZ ) /\\ '
                 '( ( m gcd D ) = 1 /\\ K || D ) )'), w.inst('rpdvds')], 'syl',
             '( m gcd K ) = 1')
    mdkq = sc([sc([mdP2], 'adantr', 'm || P'),
               sc([lift(w, d['kq'], AEC)], 'eqcomd', 'P = ( K x. %s )' % QQ)], 'breqtrd',
              'm || ( K x. %s )' % QQ)
    mdq = sc([sc([sc([sc([mz2], 'adantr', 'm e. ZZ'), lift(w, d['kz'], AEC),
                      lift(w, d['qz'], AEC)], '3jca',
                     '( m e. ZZ /\\ K e. ZZ /\\ %s e. ZZ )' % QQ), w.inst('coprmdvds')], 'syl',
                  '( ( m || ( K x. %s ) /\\ ( m gcd K ) = 1 ) -> m || %s )' % (QQ, QQ)),
               sc([mdkq, mgk], 'jca', '( m || ( K x. %s ) /\\ ( m gcd K ) = 1 )' % QQ)], 'mpd',
              'm || %s' % QQ)
    ncop = se([nmq, sc([mdq], 'ex', '( ( m gcd D ) = 1 -> m || %s )' % QQ) if False else
               w.s([mdq], 'ex', '( %s -> ( ( m gcd D ) = 1 -> m || %s ) )' % (AE, QQ))],
              'mtod', '-. ( m gcd D ) = 1')
    zero = se([se([ncop], 'intnand', '-. ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 )' % KM)],
              'iffalsed', '%s = 0' % BMP)
    w.qed([sub, bodyc, zero, d['finP']], 'fsumss',
          '( %s -> sum_ m e. %s %s = sum_ m e. %s %s )' % (AG, DVQ, BMP, DVP, BMP))
    return w



def gfiff():
    w = W('gfiff', 'The gcd fibre condition at K times m.')
    A = '( %s /\\ m e. %s )' % (AG, DVQ)
    d = gbase(w)
    mf = mfacts(w, d, A)
    sm = mf['st']
    kz = lift(w, d['kz'], A)
    dz = lift(w, d['dz'], A)
    rz = lift(w, d['rz'], A)
    mz = mf['z']
    kcn = sm([lift(w, d['knn'], A)], 'nncnd', 'K e. CC')
    kne = sm([lift(w, d['knn'], A)], 'nnne0d', 'K =/= 0')
    k0 = sm([lift(w, d['knn'], A)], 'nnnn0d', 'K e. NN0')
    rgm = sm([sm([rz, mz], 'jca', '( %s e. ZZ /\\ m e. ZZ )' % RR_), w.inst('gcdnncl')], 'syl',
             '( %s gcd m ) e. NN' % RR_) if False else None
    rgmn = sm([sm([lift(w, d['rnn'], A), mf['nn']], 'jca', '( %s e. NN /\\ m e. NN )' % RR_),
               w.inst('gcdnncl')], 'syl', '( %s gcd m ) e. NN' % RR_)
    rgmc = sm([rgmn], 'nncnd', '( %s gcd m ) e. CC' % RR_)
    mgrn = sm([sm([mf['nn'], lift(w, d['rnn'], A)], 'jca', '( m e. NN /\\ %s e. NN )' % RR_),
               w.inst('gcdnncl')], 'syl', '( m gcd %s ) e. NN' % RR_)
    mgrc = sm([mgrn], 'nncnd', '( m gcd %s ) e. CC' % RR_)
    # ---- ( D gcd ( K x. m ) ) = ( K x. ( R gcd m ) )
    e1 = sm([sm([lift(w, d['kr'], A)], 'eqcomd', 'D = ( K x. %s )' % RR_)], 'oveq1d',
            '( D gcd %s ) = ( ( K x. %s ) gcd %s )' % (KM, RR_, KM))
    e2 = sm([k0, rz, mz, w.inst('mulgcd')], 'syl3anc',
            '( ( K x. %s ) gcd %s ) = ( K x. ( %s gcd m ) )' % (RR_, KM, RR_))
    gde = sm([e1, e2], 'eqtrd', '( D gcd %s ) = ( K x. ( %s gcd m ) )' % (KM, RR_))
    b1 = sm([gde], 'eqeq2d',
            '( K = ( D gcd %s ) <-> K = ( K x. ( %s gcd m ) ) )' % (KM, RR_))
    b2 = sm([sm([sm([kcn], 'mulridd', '( K x. 1 ) = K')], 'eqcomd', 'K = ( K x. 1 )')],
            'eqeq1d', '( K = ( K x. ( %s gcd m ) ) <-> ( K x. 1 ) = ( K x. ( %s gcd m ) ) )'
            % (RR_, RR_))
    b3 = sm([w.s([], '1cnd', '( %s -> 1 e. CC )' % A), rgmc, kcn, kne], 'mulcand',
            '( ( K x. 1 ) = ( K x. ( %s gcd m ) ) <-> 1 = ( %s gcd m ) )' % (RR_, RR_))
    b4 = sm([w.s([], 'eqcom', '( 1 = ( %s gcd m ) <-> ( %s gcd m ) = 1 )' % (RR_, RR_))], 'a1i',
            '( 1 = ( %s gcd m ) <-> ( %s gcd m ) = 1 )' % (RR_, RR_))
    left = sm([sm([b1, b2], 'bitrd',
                  '( K = ( D gcd %s ) <-> ( K x. 1 ) = ( K x. ( %s gcd m ) ) )' % (KM, RR_)),
               sm([b3, b4], 'bitrd',
                  '( ( K x. 1 ) = ( K x. ( %s gcd m ) ) <-> ( %s gcd m ) = 1 )' % (RR_, RR_))],
              'bitrd', '( K = ( D gcd %s ) <-> ( %s gcd m ) = 1 )' % (KM, RR_))
    # ---- ( m gcd D ) = ( R gcd m )
    f1 = sm([sm([lift(w, d['kr'], A)], 'eqcomd', 'D = ( K x. %s )' % RR_)], 'oveq2d',
            '( m gcd D ) = ( m gcd ( K x. %s ) )' % RR_)
    f2 = sm([sm([sm([mz, kz, rz], '3jca', '( m e. ZZ /\\ K e. ZZ /\\ %s e. ZZ )' % RR_),
                 lift(w, d['copr'], A)], 'jca',
                '( ( m e. ZZ /\\ K e. ZZ /\\ %s e. ZZ ) /\\ ( K gcd %s ) = 1 )' % (RR_, RR_)),
             w.inst('rpmulgcd2')], 'syl',
            '( m gcd ( K x. %s ) ) = ( ( m gcd K ) x. ( m gcd %s ) )' % (RR_, RR_))
    mgk = sm([sm([sm([mz, kz], 'jca', '( m e. ZZ /\\ K e. ZZ )'), w.inst('gcdcom')], 'syl',
                 '( m gcd K ) = ( K gcd m )'), mf['kgm']], 'eqtrd', '( m gcd K ) = 1')
    f3 = sm([sm([mgk], 'oveq1d',
                '( ( m gcd K ) x. ( m gcd %s ) ) = ( 1 x. ( m gcd %s ) )' % (RR_, RR_)),
             sm([mgrc], 'mullidd', '( 1 x. ( m gcd %s ) ) = ( m gcd %s )' % (RR_, RR_))],
            'eqtrd', '( ( m gcd K ) x. ( m gcd %s ) ) = ( m gcd %s )' % (RR_, RR_))
    f4 = sm([sm([mz, rz], 'jca', '( m e. ZZ /\\ %s e. ZZ )' % RR_), w.inst('gcdcom')], 'syl',
            '( m gcd %s ) = ( %s gcd m )' % (RR_, RR_))
    fq = sm([sm([f1, f2], 'eqtrd',
                '( m gcd D ) = ( ( m gcd K ) x. ( m gcd %s ) )' % RR_),
             sm([f3, f4], 'eqtrd',
                '( ( m gcd K ) x. ( m gcd %s ) ) = ( %s gcd m )' % (RR_, RR_))], 'eqtrd',
            '( m gcd D ) = ( %s gcd m )' % RR_)
    right = sm([fq], 'eqeq1d', '( ( m gcd D ) = 1 <-> ( %s gcd m ) = 1 )' % RR_)
    core = sm([left, right], 'bitr4d', '( K = ( D gcd %s ) <-> ( m gcd D ) = 1 )' % KM)
    conj = sm([core], 'anbi1d',
              '( ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) <-> '
              '( ( m gcd D ) = 1 /\\ ( %s ^ 2 ) <_ Y ) )' % (KM, KM, KM))
    com = sm([w.s([], 'ancom', '( ( ( m gcd D ) = 1 /\\ ( %s ^ 2 ) <_ Y ) <-> '
                  '( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % (KM, KM))], 'a1i',
             '( ( ( m gcd D ) = 1 /\\ ( %s ^ 2 ) <_ Y ) <-> '
             '( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % (KM, KM))
    w.qed([conj, com], 'bitrd',
          '( %s -> ( ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) <-> '
          '( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) ) )' % (A, KM, KM, KM))
    return w



CKM = ('if ( ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) , %s , 0 )' % (KM, KM, GT(KM)))


def bmcc(w, d, ante, mf):
    """( ante -> BM e. CC ) given the facts about m e. DV ( Q )"""
    sb = mkst(w, ante)
    kmnn = sb([lift(w, d['knn'], ante), mf['nn']], 'nnmulcld', '%s e. NN' % KM)
    kmd = sb([sb([sb([mf['z'], lift(w, d['qz'], ante), lift(w, d['kz'], ante)], '3jca',
                     '( m e. ZZ /\\ %s e. ZZ /\\ K e. ZZ )' % QQ), w.inst('dvdscmul')], 'syl',
                 '( m || %s -> %s || ( K x. %s ) )' % (QQ, KM, QQ)), mf['dQ']], 'mpd',
              '%s || ( K x. %s )' % (KM, QQ))
    kmdp = sb([kmd, lift(w, d['kq'], ante)], 'breqtrd', '%s || P' % KM)
    gkmc = sb([sb([lift(w, d['sh'], ante),
                   sb([kmnn, kmdp], 'jca', '( %s e. NN /\\ %s || P )' % (KM, KM)),
                   w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT(KM))], 'rpcnd',
              '%s e. CC' % GT(KM))
    return sb([gkmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % ante)], 'ifcld', '%s e. CC' % BM)


def gfbm():
    w = W('gfbm', 'The inner sum of the gcd fibre factors out the Selberg term of K.')
    d = gbase(w)
    st = d['st']
    AM = '( %s /\\ m e. %s )' % (AG, DVQ)
    mf = mfacts(w, d, AM)
    sm = mf['st']
    gkrp = st([d['sh'], st([d['knn'], d['kdP']], 'jca', '( K e. NN /\\ K || P )'),
               w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('K'))
    gkc = st([gkrp], 'rpcnd', '%s e. CC' % GT('K'))
    gmc = sm([sm([lift(w, d['sh'], AM), sm([mf['nn'], mf['dP']], 'jca',
                                           '( m e. NN /\\ m || P )'), w.inst('gtrp')],
                 'syl2anc', '%s e. RR+' % GT('m'))], 'rpcnd', '%s e. CC' % GT('m'))
    bmpc = sm([gmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % AM)], 'ifcld', '%s e. CC' % BMP)
    mul = sm([sm([lift(w, d['sh'], AM),
                  sm([sm([lift(w, d['knn'], AM), lift(w, d['kdP'], AM)], 'jca',
                         '( K e. NN /\\ K || P )'),
                      sm([mf['nn'], mf['dP']], 'jca', '( m e. NN /\\ m || P )'),
                      mf['kgm']], '3jca',
                     '( ( K e. NN /\\ K || P ) /\\ ( m e. NN /\\ m || P ) /\\ ( K gcd m ) = 1 )')],
                 'jca',
                 '( %s /\\ ( ( K e. NN /\\ K || P ) /\\ ( m e. NN /\\ m || P ) /\\ '
                 '( K gcd m ) = 1 ) )' % SH), w.inst('gtmul')], 'syl',
             '%s = ( %s x. %s )' % (GT(KM), GT('K'), GT('m')))
    term = sm([sm([mul], 'ifeq1d',
                  '%s = if ( ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , ( %s x. %s ) , 0 )'
                  % (BM, KM, GT('K'), GT('m'))),
               sm([sm([lift(w, gkc, AM), w.inst('ifmulz2')], 'syl',
                      '( %s x. %s ) = if ( ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , '
                      '( %s x. %s ) , 0 )' % (GT('K'), BMP, KM, GT('K'), GT('m')))], 'eqcomd',
                  'if ( ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , ( %s x. %s ) , 0 ) = '
                  '( %s x. %s )' % (KM, GT('K'), GT('m'), GT('K'), BMP))], 'eqtrd',
              '%s = ( %s x. %s )' % (BM, GT('K'), BMP))
    s1 = st([term], 'sumeq2dv',
            'sum_ m e. %s %s = sum_ m e. %s ( %s x. %s )' % (DVQ, BM, DVQ, GT('K'), BMP))
    s2 = st([st([d['finQ'], gkc, bmpc], 'fsummulc2',
                '( %s x. sum_ m e. %s %s ) = sum_ m e. %s ( %s x. %s )'
                % (GT('K'), DVQ, BMP, DVQ, GT('K'), BMP))], 'eqcomd',
            'sum_ m e. %s ( %s x. %s ) = ( %s x. sum_ m e. %s %s )'
            % (DVQ, GT('K'), BMP, GT('K'), DVQ, BMP))
    s3 = st([st([w.s([], 'gfinner',
                     '( %s -> sum_ m e. %s %s = sum_ m e. %s %s )' % (AG, DVQ, BMP, DVP, BMP))],
                'oveq2d', '( %s x. sum_ m e. %s %s ) = ( %s x. sum_ m e. %s %s )'
                % (GT('K'), DVQ, BMP, GT('K'), DVP, BMP))], 'id',
            '( %s x. sum_ m e. %s %s ) = ( %s x. sum_ m e. %s %s )'
            % (GT('K'), DVQ, BMP, GT('K'), DVP, BMP)) if False else st(
        [w.s([], 'gfinner',
             '( %s -> sum_ m e. %s %s = sum_ m e. %s %s )' % (AG, DVQ, BMP, DVP, BMP))],
        'oveq2d', '( %s x. sum_ m e. %s %s ) = ( %s x. sum_ m e. %s %s )'
        % (GT('K'), DVQ, BMP, GT('K'), DVP, BMP))
    w.qed([s1, st([s2, s3], 'eqtrd',
                  'sum_ m e. %s ( %s x. %s ) = ( %s x. sum_ m e. %s %s )'
                  % (DVQ, GT('K'), BMP, GT('K'), DVP, BMP))], 'eqtrd',
          '( %s -> sum_ m e. %s %s = ( %s x. sum_ m e. %s %s ) )'
          % (AG, DVQ, BM, GT('K'), DVP, BMP))
    return w


def gcdfib():
    w = W('gcdfib', 'The gcd fibre of the Selberg bounding sum.')
    d = gbase(w)
    st = d['st']
    DVK = DV('K')
    DVZ = DV('( K x. %s )' % QQ)
    finK = st([d['knn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVK)
    # ---- the indicator sum over the divisors of K
    kdvk = st([st([st([d['knn'], st([d['kz'], w.inst('iddvds')], 'syl', 'K || K')], 'jca',
                      '( K e. NN /\\ K || K )'),
                   st([w.s([w.s([], 'breq1', '( x = K -> ( x || K <-> K || K ) )')], 'elrab',
                           '( K e. %s <-> ( K e. NN /\\ K || K ) )' % DVK)], 'a1i',
                      '( K e. %s <-> ( K e. NN /\\ K || K ) )' % DVK)], 'mpbird',
                  'K e. %s' % DVK)], 'id', 'K e. %s' % DVK) if False else st(
        [st([d['knn'], st([d['kz'], w.inst('iddvds')], 'syl', 'K || K')], 'jca',
            '( K e. NN /\\ K || K )'),
         st([w.s([w.s([], 'breq1', '( x = K -> ( x || K <-> K || K ) )')], 'elrab',
                 '( K e. %s <-> ( K e. NN /\\ K || K ) )' % DVK)], 'a1i',
            '( K e. %s <-> ( K e. NN /\\ K || K ) )' % DVK)], 'mpbird', 'K e. %s' % DVK)
    hone = w.s([w.s([], 'eqid', '1 = 1')], 'a1i', '( j = K -> 1 = 1 )')
    onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % AG)
    sumj = w.s([hone, finK, kdvk, onec], 'sumite',
               '( %s -> sum_ j e. %s %s = 1 )' % (AG, DVK, AJ))
    # ---- the hypotheses of fsumdvdsmul
    ex = w.s([], 'eqid', '%s = %s' % (DVK, DVK))
    ey = w.s([], 'eqid', '%s = %s' % (DVQ, DVQ))
    ez = w.s([], 'eqid', '%s = %s' % (DVZ, DVZ))
    AJD = '( %s /\\ j e. %s )' % (AG, DVK)
    h4 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % AJD),
              w.s([], '0cnd', '( %s -> 0 e. CC )' % AJD)], 'ifcld',
             '( %s -> %s e. CC )' % (AJD, AJ))
    AMD = '( %s /\\ m e. %s )' % (AG, DVQ)
    mf0 = mfacts(w, d, AMD)
    h5 = bmcc(w, d, AMD, mf0)
    # ---- the product obligation
    AJM = '( %s /\\ ( j e. %s /\\ m e. %s ) )' % (AG, DVK, DVQ)
    sjm = mkst(w, AJM)
    prj = sjm([], 'simpr', '( j e. %s /\\ m e. %s )' % (DVK, DVQ))
    jmem = sjm([prj], 'simpld', 'j e. %s' % DVK)
    mmem = sjm([prj], 'simprd', 'm e. %s' % DVQ)
    mf1 = mfacts(w, d, AJM, mmem)
    elj = w.s([w.s([], 'breq1', '( x = j -> ( x || K <-> j || K ) )')], 'elrab',
              '( j e. %s <-> ( j e. NN /\\ j || K ) )' % DVK)
    jc = sjm([sjm([elj], 'a1i', '( j e. %s <-> ( j e. NN /\\ j || K ) )' % DVK), jmem],
             'mpbid', '( j e. NN /\\ j || K )')
    jnn = sjm([jc], 'simpld', 'j e. NN')
    jdK = sjm([jc], 'simprd', 'j || K')
    jz = sjm([jnn], 'nnzd', 'j e. ZZ')
    bmc = bmcc(w, d, AJM, mf1)
    # case j = K
    AJE = '( %s /\\ j = K )' % AJM
    sje = mkst(w, AJE)
    jeq = sje([], 'simpr', 'j = K')
    idj = w.s([], 'id', '( j = K -> j = K )')
    n0 = len(w.lines)
    hcj, newc = w.congr(CJM, {'j': 'K'}, 'j = K', {'j': idj})
    sdvfix(w, n0)
    cong = sje([jeq, hcj], 'syl', '%s = %s' % (CJM, CKM))
    iff = sje([sje([lift(w, d['sh'], AJE)], 'id', SH) and
               sje([], 'id', 'x = x')], 'id', 'x = x') if False else None
    gf = sje([sje([lift(w, w.s([], 'id', '( %s -> %s )' % (AG, AG)), AJE), mmem], 'jca',
                  'x = x')], 'id', 'x = x') if False else None
    gfi = w.s([], 'gfiff',
              '( ( %s /\\ m e. %s ) -> ( ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) <-> '
              '( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) ) )' % (AG, DVQ, KM, KM, KM))
    gfd = sje([sje([sje([sje([], 'simpll', AG) if False else
                        lift(w, w.s([], 'id', '( %s -> %s )' % (AG, AG)), AJE),
                        lift(w, mmem, AJE)], 'jca',
                       '( %s /\\ m e. %s )' % (AG, DVQ)), gfi], 'syl',
                   '( ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) <-> '
                   '( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % (KM, KM, KM))], 'bicomd',
              '( ( ( %s ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) <-> '
              '( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y ) )' % (KM, KM, KM))
    bmeq = sje([gfd], 'ifbid', '%s = %s' % (BM, CKM))
    lhs1 = sje([sje([sje([jeq], 'iftrued', '%s = 1' % AJ)], 'oveq1d',
                    '( %s x. %s ) = ( 1 x. %s )' % (AJ, BM, BM)),
                sje([lift(w, bmc, AJE)], 'mullidd', '( 1 x. %s ) = %s' % (BM, BM))], 'eqtrd',
               '( %s x. %s ) = %s' % (AJ, BM, BM))
    case1 = sje([lhs1, sje([bmeq, sje([cong], 'eqcomd', '%s = %s' % (CKM, CJM))], 'eqtrd',
                           '%s = %s' % (BM, CJM))], 'eqtrd', '( %s x. %s ) = %s' % (AJ, BM, CJM))
    # case -. j = K
    AJF = '( %s /\\ -. j = K )' % AJM
    sjf = mkst(w, AJF)
    AJFG = '( %s /\\ K = ( D gcd %s ) )' % (AJF, JM)
    sfg = mkst(w, AJFG)
    kdjm = sfg([sfg([], 'simpr', 'K = ( D gcd %s )' % JM),
                sfg([sfg([lift(w, d['dz'], AJFG),
                          sfg([lift(w, jz, AJFG), sfg([mf1['z']], 'adantr',
                                                                   'm e. ZZ')], 'nnmulcld'
                              if False else 'zmulcld', '%s e. ZZ' % JM)], 'jca',
                         '( D e. ZZ /\\ %s e. ZZ )' % JM), w.inst('gcddvds')], 'syl',
                    '( ( D gcd %s ) || D /\\ ( D gcd %s ) || %s )' % (JM, JM, JM))], 'id',
               'x = x') if False else None
    gdv = sfg([sfg([sfg([lift(w, d['dz'], AJFG),
                         sfg([lift(w, jz, AJFG),
                              lift(w, mf1['z'], AJFG)], 'zmulcld',
                             '%s e. ZZ' % JM)], 'jca', '( D e. ZZ /\\ %s e. ZZ )' % JM),
                   w.inst('gcddvds')], 'syl',
                  '( ( D gcd %s ) || D /\\ ( D gcd %s ) || %s )' % (JM, JM, JM))], 'simprd',
              '( D gcd %s ) || %s' % (JM, JM))
    kdjm = sfg([sfg([], 'simpr', 'K = ( D gcd %s )' % JM), gdv], 'eqbrtrd', 'K || %s' % JM)
    kdmj = sfg([kdjm, sfg([sfg([lift(w, jz, AJFG)], 'zcnd', 'j e. CC'),
                           sfg([lift(w, mf1['z'], AJFG)], 'zcnd', 'm e. CC')],
                          'mulcomd', '%s = ( m x. j )' % JM)], 'breqtrd', 'K || ( m x. j )')
    kdj = sfg([sfg([sfg([lift(w, d['kz'], AJFG), lift(w, mf1['z'], AJFG),
                         lift(w, jz, AJFG)], '3jca',
                        '( K e. ZZ /\\ m e. ZZ /\\ j e. ZZ )'), w.inst('coprmdvds')], 'syl',
                   '( ( K || ( m x. j ) /\\ ( K gcd m ) = 1 ) -> K || j )'),
               sfg([kdmj, lift(w, mf1['kgm'], AJFG)], 'jca',
                   '( K || ( m x. j ) /\\ ( K gcd m ) = 1 )')], 'mpd', 'K || j')
    jeqk = sfg([sfg([sfg([sfg([lift(w, jnn, AJFG)], 'nnnn0d', 'j e. NN0'),
                          sfg([lift(w, d['knn'], AJFG)], 'nnnn0d', 'K e. NN0')], 'jca',
                         '( j e. NN0 /\\ K e. NN0 )'),
                     sfg([lift(w, jdK, AJFG), kdj], 'jca',
                         '( j || K /\\ K || j )')], 'jca',
                    '( ( j e. NN0 /\\ K e. NN0 ) /\\ ( j || K /\\ K || j ) )')], 'id',
               'x = x') if False else None
    jeqk = sfg([sfg([sfg([lift(w, jnn, AJFG)], 'nnnn0d', 'j e. NN0'),
                     sfg([lift(w, d['knn'], AJFG)], 'nnnn0d', 'K e. NN0')], 'jca',
                    '( j e. NN0 /\\ K e. NN0 )'),
                sfg([lift(w, jdK, AJFG), kdj], 'jca',
                    '( j || K /\\ K || j )'), w.inst('dvdseq')], 'syl2anc', 'j = K')
    nogcd = sjf([sjf([], 'simpr', '-. j = K'), jeqk], 'mtand', '-. K = ( D gcd %s )' % JM)
    case2 = sjf([sjf([sjf([sjf([], 'iffalsed', '%s = 0' % AJ)], 'oveq1d',
                          '( %s x. %s ) = ( 0 x. %s )' % (AJ, BM, BM)),
                      sjf([lift(w, bmc, AJF)], 'mul02d', '( 0 x. %s ) = 0' % BM)], 'eqtrd',
                     '( %s x. %s ) = 0' % (AJ, BM)),
                 sjf([sjf([sjf([nogcd], 'intnanrd',
                               '-. ( K = ( D gcd %s ) /\\ ( %s ^ 2 ) <_ Y )' % (JM, JM))],
                          'iffalsed', '%s = 0' % CJM)], 'eqcomd', '0 = %s' % CJM)], 'eqtrd',
                '( %s x. %s ) = %s' % (AJ, BM, CJM))
    h6 = sjm([case1, case2], 'pm2.61dan', '( %s x. %s ) = %s' % (AJ, BM, CJM))
    # ---- the substitution hypothesis
    idl = w.s([], 'id', '( l = %s -> l = %s )' % (JM, JM))
    n1 = len(w.lines)
    h7, _ = w.congr(CL, {'l': JM}, 'l = %s' % JM, {'l': idl})
    sdvfix(w, n1)
    # ---- fsumdvdsmul
    dm = w.s([d['knn'], d['qnn'], d['cop'], ex, ey, ez, h4, h5, h6, h7], 'fsumdvdsmul',
             '( %s -> ( sum_ j e. %s %s x. sum_ m e. %s %s ) = sum_ l e. %s %s )'
             % (AG, DVK, AJ, DVQ, BM, DVZ, CL))
    zeq = st([st([st([d['kq']], 'breq2d', '( x || ( K x. %s ) <-> x || P )' % QQ)], 'rabbidv',
                 '%s = %s' % (DVZ, DVP))], 'sumeq1d',
             'sum_ l e. %s %s = sum_ l e. %s %s' % (DVZ, CL, DVP, CL))
    bmsum = st([d['finQ'], h5], 'fsumcl', 'sum_ m e. %s %s e. CC' % (DVQ, BM))
    lhs = st([st([sumj], 'oveq1d',
                 '( sum_ j e. %s %s x. sum_ m e. %s %s ) = ( 1 x. sum_ m e. %s %s )'
                 % (DVK, AJ, DVQ, BM, DVQ, BM)),
              st([bmsum], 'mullidd',
                 '( 1 x. sum_ m e. %s %s ) = sum_ m e. %s %s' % (DVQ, BM, DVQ, BM))], 'eqtrd',
             '( sum_ j e. %s %s x. sum_ m e. %s %s ) = sum_ m e. %s %s'
             % (DVK, AJ, DVQ, BM, DVQ, BM))
    gb = st([], 'gfbm', 'sum_ m e. %s %s = ( %s x. sum_ m e. %s %s )'
             % (DVQ, BM, GT('K'), DVP, BMP))
    w.qed([st([st([dm, zeq], 'eqtrd',
                  '( sum_ j e. %s %s x. sum_ m e. %s %s ) = sum_ l e. %s %s'
                  % (DVK, AJ, DVQ, BM, DVP, CL))], 'eqcomd',
              'sum_ l e. %s %s = ( sum_ j e. %s %s x. sum_ m e. %s %s )'
              % (DVP, CL, DVK, AJ, DVQ, BM)),
           st([lhs, gb], 'eqtrd',
              '( sum_ j e. %s %s x. sum_ m e. %s %s ) = ( %s x. sum_ m e. %s %s )'
              % (DVK, AJ, DVQ, BM, GT('K'), DVP, BMP))], 'eqtrd',
          '( %s -> sum_ l e. %s %s = ( %s x. sum_ m e. %s %s ) )'
          % (AG, DVP, CL, GT('K'), DVP, BMP))
    return w



AD2 = '( %s /\\ ( D e. NN /\\ D || P ) )' % SH


def JD(v):
    return ('sum_ m e. %s if ( ( ( ( %s x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , %s , 0 )'
            % (DVP, v, GT('m')))


def GFIB(v):
    return ('sum_ l e. %s if ( ( %s = ( D gcd l ) /\\ ( l ^ 2 ) <_ Y ) , %s , 0 )'
            % (DVP, v, GT('l')))


def lwmuss():
    w = W('lwmuss', 'The Selberg weight times the Moebius value times the bounding sum is at '
                    'most the bounding sum.')
    A = AD2
    DVD = DV('D')
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    dnnp = st([dnn, ddp], 'jca', '( D e. NN /\\ D || P )')
    finD = st([dnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVD)
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    vrp = st([d['sh'], dnnp, w.inst('vdrp')], 'syl2anc', '( V ` D ) e. RR+')
    ivc = st([st([vrp], 'rpreccld', '( 1 / ( V ` D ) ) e. RR+')], 'rpcnd',
             '( 1 / ( V ` D ) ) e. CC')
    gdrp = st([d['sh'], dnnp, w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('D'))
    gdc = st([gdrp], 'rpcnd', '%s e. CC' % GT('D'))
    # ---- the inner sum INNER ( D ) and the sums JD
    AM = '( %s /\\ m e. %s )' % (A, DVP)
    dm = dvpel(w, AM, 'm', d['pnn'])
    sm = dm['st']
    gmrp = sm([lift(w, d['sh'], AM), sm([dm['nn'], dm['dP']], 'jca', '( m e. NN /\\ m || P )'),
               w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('m'))
    gmr = sm([gmrp], 'rpred', '%s e. RR' % GT('m'))
    gmc = sm([gmrp], 'rpcnd', '%s e. CC' % GT('m'))
    ITD = INTERM('D')
    itdc = sm([gmc, w.s([], '0cnd', '( %s -> 0 e. CC )' % AM)], 'ifcld', '%s e. CC' % ITD)
    innc = st([finP, itdc], 'fsumcl', '%s e. CC' % INNER('D'))
    innr = st([finP, sm([gmrp], 'rpred', '%s e. RR' % GT('m')) and
               sm([gmr, w.s([], '0red', '( %s -> 0 e. RR )' % AM)], 'ifcld',
                  '%s e. RR' % ITD)], 'fsumrecl', '%s e. RR' % INNER('D'))
    # ---- step 1 and 2 : the identity
    lm1 = st([d['sh'], dnnp, w.inst('lwmu1')], 'syl2anc',
             '( ( %s x. ( mmu ` D ) ) x. %s ) = ( ( 1 / ( V ` D ) ) x. %s )'
             % (LW('D'), SS(), TD('D')))
    ls = st([d['sh'], dnnp, w.inst('lwsum')], 'syl2anc',
            '%s = ( %s x. %s )' % (TD('D'), GT('D'), INNER('D')))
    gs = st([d['sh'], dnnp, w.inst('gtsum')], 'syl2anc',
            'sum_ d e. %s %s = ( ( 1 / ( V ` D ) ) x. %s )' % (DVD, GT('d'), GT('D')))
    a1 = st([st([ls], 'oveq2d',
                '( ( 1 / ( V ` D ) ) x. %s ) = ( ( 1 / ( V ` D ) ) x. ( %s x. %s ) )'
                % (TD('D'), GT('D'), INNER('D'))),
             st([st([ivc, gdc, innc], 'mulassd',
                    '( ( ( 1 / ( V ` D ) ) x. %s ) x. %s ) = '
                    '( ( 1 / ( V ` D ) ) x. ( %s x. %s ) )'
                    % (GT('D'), INNER('D'), GT('D'), INNER('D')))], 'eqcomd',
                '( ( 1 / ( V ` D ) ) x. ( %s x. %s ) ) = '
                '( ( ( 1 / ( V ` D ) ) x. %s ) x. %s )'
                % (GT('D'), INNER('D'), GT('D'), INNER('D')))], 'eqtrd',
            '( ( 1 / ( V ` D ) ) x. %s ) = ( ( ( 1 / ( V ` D ) ) x. %s ) x. %s )'
            % (TD('D'), GT('D'), INNER('D')))
    a2 = st([st([gs], 'eqcomd',
                '( ( 1 / ( V ` D ) ) x. %s ) = sum_ d e. %s %s' % (GT('D'), DVD, GT('d')))],
            'oveq1d',
            '( ( ( 1 / ( V ` D ) ) x. %s ) x. %s ) = ( sum_ d e. %s %s x. %s )'
            % (GT('D'), INNER('D'), DVD, GT('d'), INNER('D')))
    # ---- facts for d e. DV ( D )
    AJ2 = '( %s /\\ d e. %s )' % (A, DVD)
    dd = dvdfacts(w, A, AJ2, 'd', 'D', d['sh'], dz, ddp, pz)
    sj = dd['st']
    gjrp = sj([lift(w, d['sh'], AJ2), sj([dd['nn'], dd['dP']], 'jca', '( d e. NN /\\ d || P )'),
               w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('d'))
    gjr = sj([gjrp], 'rpred', '%s e. RR' % GT('d'))
    gjc = sj([gjrp], 'rpcnd', '%s e. CC' % GT('d'))
    a3 = st([finD, innc, gjc], 'fsummulc1',
            '( sum_ d e. %s %s x. %s ) = sum_ d e. %s ( %s x. %s )'
            % (DVD, GT('d'), INNER('D'), DVD, GT('d'), INNER('D')))
    ident = st([lm1, st([a1, st([a2, a3], 'eqtrd',
                                '( ( ( 1 / ( V ` D ) ) x. %s ) x. %s ) = '
                                'sum_ d e. %s ( %s x. %s )'
                                % (GT('D'), INNER('D'), DVD, GT('d'), INNER('D')))], 'eqtrd',
                        '( ( 1 / ( V ` D ) ) x. %s ) = sum_ d e. %s ( %s x. %s )'
                        % (TD('D'), DVD, GT('d'), INNER('D')))], 'eqtrd',
               '( ( %s x. ( mmu ` D ) ) x. %s ) = sum_ d e. %s ( %s x. %s )'
               % (LW('D'), SS(), DVD, GT('d'), INNER('D')))
    # ---- the termwise comparison
    ITJ = 'if ( ( ( ( d x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) , %s , 0 )' % GT('m')
    AJM = '( %s /\\ m e. %s )' % (AJ2, DVP)
    dm2 = dvpel(w, AJM, 'm', d['pnn'])
    sjm = dm2['st']
    gm2rp = sjm([lift(w, d['sh'], AJM),
                 sjm([dm2['nn'], dm2['dP']], 'jca', '( m e. NN /\\ m || P )'),
                 w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('m'))
    gm2r = sjm([gm2rp], 'rpred', '%s e. RR' % GT('m'))
    zre = w.s([], '0red', '( %s -> 0 e. RR )' % AJM)
    itdr = sjm([gm2r, zre], 'ifcld', '%s e. RR' % ITD)
    itjr = sjm([gm2r, zre], 'ifcld', '%s e. RR' % ITJ)
    # 0 <_ ITJ
    AJMT = '( %s /\\ ( ( ( d x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % AJM
    sjt = mkst(w, AJMT)
    ge1 = sjt([sjt([lift(w, gm2rp, AJMT)], 'rpge0d', '0 <_ %s' % GT('m')),
               sjt([], 'iftrued', '%s = %s' % (ITJ, GT('m')))], 'breqtrrd',
              '0 <_ %s' % ITJ)
    AJMF = '( %s /\\ -. ( ( ( d x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % AJM
    sjf2 = mkst(w, AJMF)
    ge2 = sjf2([w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % AJMF),
                sjf2([], 'iffalsed', '%s = 0' % ITJ)], 'breqtrrd', '0 <_ %s' % ITJ)
    itjge0 = sjm([ge1, ge2], 'pm2.61dan', '0 <_ %s' % ITJ)
    # the condition implication
    AJMD = '( %s /\\ ( ( ( D x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % AJM
    sjd = mkst(w, AJMD)
    dle = sjd([sjd([sjd([lift(w, dd['z'], AJMD), lift(w, dnn, AJMD)], 'jca',
                        '( d e. ZZ /\\ D e. NN )'), w.inst('dvdsle')], 'syl',
                   '( d || D -> d <_ D )'), lift(w, dd['dD'], AJMD)], 'mpd', 'd <_ D')
    dmr = sjd([sjd([lift(w, dd['nn'], AJMD)], 'nnred', 'd e. RR'),
               sjd([lift(w, dm2['nn'], AJMD)], 'nnred', 'm e. RR')], 'remulcld',
              '( d x. m ) e. RR')
    Dmr = sjd([sjd([lift(w, dnn, AJMD)], 'nnred', 'D e. RR'),
               sjd([lift(w, dm2['nn'], AJMD)], 'nnred', 'm e. RR')], 'remulcld',
              '( D x. m ) e. RR')
    dm0 = sjd([sjd([sjd([lift(w, dd['nn'], AJMD)], 'nnnn0d', 'd e. NN0'),
                    sjd([lift(w, dm2['nn'], AJMD)], 'nnnn0d', 'm e. NN0')], 'nn0mulcld',
                   '( d x. m ) e. NN0')], 'nn0ge0d', '0 <_ ( d x. m )')
    mul = sjd([sjd([lift(w, dd['nn'], AJMD)], 'nnred', 'd e. RR'),
               sjd([lift(w, dnn, AJMD)], 'nnred', 'D e. RR'),
               sjd([lift(w, dm2['nn'], AJMD)], 'nnred', 'm e. RR'),
               sjd([sjd([lift(w, dm2['nn'], AJMD)], 'nnnn0d', 'm e. NN0')], 'nn0ge0d',
                   '0 <_ m'), dle], 'lemul1ad', '( d x. m ) <_ ( D x. m )')
    sq2 = sjd([sjd([sjd([dmr, dm0], 'jca', '( ( d x. m ) e. RR /\\ 0 <_ ( d x. m ) )'),
                    sjd([Dmr, mul], 'jca',
                        '( ( D x. m ) e. RR /\\ ( d x. m ) <_ ( D x. m ) )')], 'jca',
                   '( ( ( d x. m ) e. RR /\\ 0 <_ ( d x. m ) ) /\\ '
                   '( ( D x. m ) e. RR /\\ ( d x. m ) <_ ( D x. m ) ) )'), w.inst('le2sq2')],
              'syl', '( ( d x. m ) ^ 2 ) <_ ( ( D x. m ) ^ 2 )')
    yle = sjd([sjd([sq2, sjd([sjd([], 'simpr',
                                  '( ( ( D x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 )')], 'simpld',
                             '( ( D x. m ) ^ 2 ) <_ Y')], 'jca',
                   '( ( ( d x. m ) ^ 2 ) <_ ( ( D x. m ) ^ 2 ) /\\ ( ( D x. m ) ^ 2 ) <_ Y )')],
              'id', 'x = x') if False else None
    dmsq = sjd([sjd([dmr], 'resqcld', '( ( d x. m ) ^ 2 ) e. RR'),
                sjd([Dmr], 'resqcld', '( ( D x. m ) ^ 2 ) e. RR'),
                lift(w, d['yr'], AJMD), sq2,
                sjd([sjd([], 'simpr', '( ( ( D x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 )')],
                    'simpld', '( ( D x. m ) ^ 2 ) <_ Y')], 'letrd',
               '( ( d x. m ) ^ 2 ) <_ Y')
    condimp = sjd([dmsq, sjd([sjd([], 'simpr',
                                  '( ( ( D x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 )')],
                             'simprd', '( m gcd D ) = 1')], 'jca',
                  '( ( ( d x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 )')
    cmp1 = sjd([sjd([sjd([], 'iftrued', '%s = %s' % (ITD, GT('m'))),
                     sjd([sjd([condimp], 'iftrued', '%s = %s' % (ITJ, GT('m')))], 'eqcomd',
                         '%s = %s' % (GT('m'), ITJ))], 'eqtrd', '%s = %s' % (ITD, ITJ)),
                sjd([lift(w, itjr, AJMD)], 'leidd', '%s <_ %s' % (ITJ, ITJ))], 'eqbrtrd',
               '%s <_ %s' % (ITD, ITJ))
    AJMDF = '( %s /\\ -. ( ( ( D x. m ) ^ 2 ) <_ Y /\\ ( m gcd D ) = 1 ) )' % AJM
    sjdf = mkst(w, AJMDF)
    cmp2 = sjdf([sjdf([], 'iffalsed', '%s = 0' % ITD), lift(w, itjge0, AJMDF)], 'eqbrtrd',
                '%s <_ %s' % (ITD, ITJ))
    cmp = sjm([cmp1, cmp2], 'pm2.61dan', '%s <_ %s' % (ITD, ITJ))
    innle = sj([lift(w, finP, AJ2), itdr, itjr, cmp], 'fsumle',
               '%s <_ %s' % (INNER('D'), JD('d')))
    jdr = sj([lift(w, finP, AJ2), itjr], 'fsumrecl', '%s e. RR' % JD('d'))
    termle = sj([lift(w, innr, AJ2), jdr, gjr, sj([gjrp], 'rpge0d', '0 <_ %s' % GT('d')),
                 innle], 'lemul2ad',
                '( %s x. %s ) <_ ( %s x. %s )' % (GT('d'), INNER('D'), GT('d'), JD('d')))
    innrj = sj([lift(w, innr, AJ2)], 'id', '%s e. RR' % INNER('D')) if False else None
    sumle = st([finD, sj([gjr, lift(w, innr, AJ2)], 'remulcld',
                         '( %s x. %s ) e. RR' % (GT('d'), INNER('D'))),
                sj([gjr, jdr], 'remulcld', '( %s x. %s ) e. RR' % (GT('d'), JD('d'))),
                termle], 'fsumle',
               'sum_ d e. %s ( %s x. %s ) <_ sum_ d e. %s ( %s x. %s )'
               % (DVD, GT('d'), INNER('D'), DVD, GT('d'), JD('d')))
    # ---- the gcd fibre
    gf = sj([sj([lift(w, d['sh'], AJ2), lift(w, dnnp, AJ2),
                 sj([dd['nn'], dd['dD']], 'jca', '( d e. NN /\\ d || D )')], '3jca',
                '( %s /\\ ( D e. NN /\\ D || P ) /\\ ( d e. NN /\\ d || D ) )' % SH),
             w.inst('gcdfib')], 'syl',
            '%s = ( %s x. %s )' % (GFIB('d'), GT('d'), JD('d')))
    fib = st([sj([gf], 'eqcomd', '( %s x. %s ) = %s' % (GT('d'), JD('d'), GFIB('d')))],
             'sumeq2dv',
             'sum_ d e. %s ( %s x. %s ) = sum_ d e. %s %s'
             % (DVD, GT('d'), JD('d'), DVD, GFIB('d')))
    # ---- the swap and the collapse
    CLD = 'if ( ( d = ( D gcd l ) /\\ ( l ^ 2 ) <_ Y ) , %s , 0 )' % GT('l')
    AJL = '( %s /\\ ( d e. %s /\\ l e. %s ) )' % (A, DVD, DVP)
    sjl = mkst(w, AJL)
    prjl = sjl([], 'simpr', '( d e. %s /\\ l e. %s )' % (DVD, DVP))
    ljl = sjl([prjl], 'simprd', 'l e. %s' % DVP)
    elll = w.s([w.s([], 'breq1', '( x = l -> ( x || P <-> l || P ) )')], 'elrab',
               '( l e. %s <-> ( l e. NN /\\ l || P ) )' % DVP)
    lcl = sjl([sjl([elll], 'a1i', '( l e. %s <-> ( l e. NN /\\ l || P ) )' % DVP), ljl],
              'mpbid', '( l e. NN /\\ l || P )')
    glrp = sjl([lift(w, d['sh'], AJL), lcl, w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('l'))
    cldc = sjl([sjl([glrp], 'rpcnd', '%s e. CC' % GT('l')),
                w.s([], '0cnd', '( %s -> 0 e. CC )' % AJL)], 'ifcld', '%s e. CC' % CLD)
    swap = st([finD, finP, cldc], 'fsumcom',
              'sum_ d e. %s sum_ l e. %s %s = sum_ l e. %s sum_ d e. %s %s'
              % (DVD, DVP, CLD, DVP, DVD, CLD))
    AL = '( %s /\\ l e. %s )' % (A, DVP)
    dl = dvpel(w, AL, 'l', d['pnn'])
    sl = dl['st']
    gl2rp = sl([lift(w, d['sh'], AL), sl([dl['nn'], dl['dP']], 'jca', '( l e. NN /\\ l || P )'),
                w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('l'))
    sstc = sl([sl([gl2rp], 'rpcnd', '%s e. CC' % GT('l')),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % AL)], 'ifcld', '%s e. CC' % SSTERM('l'))
    split = sl([sl([w.s([], 'ifan',
                        '%s = if ( d = ( D gcd l ) , %s , 0 )' % (CLD, SSTERM('l')))], 'a1i',
                   '%s = if ( d = ( D gcd l ) , %s , 0 )' % (CLD, SSTERM('l')))], 'sumeq2sdv',
               'sum_ d e. %s %s = sum_ d e. %s if ( d = ( D gcd l ) , %s , 0 )'
               % (DVD, CLD, DVD, SSTERM('l')))
    gnn = sl([sl([lift(w, dnn, AL), dl['nn']], 'jca', '( D e. NN /\\ l e. NN )'),
              w.inst('gcdnncl')], 'syl', '( D gcd l ) e. NN')
    gdD = sl([sl([sl([lift(w, dz, AL), sl([dl['nn']], 'nnzd', 'l e. ZZ')], 'jca',
                     '( D e. ZZ /\\ l e. ZZ )'), w.inst('gcddvds')], 'syl',
                 '( ( D gcd l ) || D /\\ ( D gcd l ) || l )')], 'simpld', '( D gcd l ) || D')
    gmem = sl([sl([gnn, gdD], 'jca', '( ( D gcd l ) e. NN /\\ ( D gcd l ) || D )'),
               sl([w.s([w.s([], 'breq1',
                             '( x = ( D gcd l ) -> ( x || D <-> ( D gcd l ) || D ) )')], 'elrab',
                       '( ( D gcd l ) e. %s <-> '
                       '( ( D gcd l ) e. NN /\\ ( D gcd l ) || D ) )' % DVD)], 'a1i',
                  '( ( D gcd l ) e. %s <-> '
                  '( ( D gcd l ) e. NN /\\ ( D gcd l ) || D ) )' % DVD)], 'mpbird',
              '( D gcd l ) e. %s' % DVD)
    hsub = w.s([w.s([], 'eqid', '%s = %s' % (SSTERM('l'), SSTERM('l')))], 'a1i',
               '( d = ( D gcd l ) -> %s = %s )' % (SSTERM('l'), SSTERM('l')))
    coll = sl([hsub, lift(w, finD, AL), gmem, sstc], 'sumite',
              'sum_ d e. %s if ( d = ( D gcd l ) , %s , 0 ) = %s' % (DVD, SSTERM('l'), SSTERM('l')))
    inner2 = st([sl([split, coll], 'eqtrd',
                    'sum_ d e. %s %s = %s' % (DVD, CLD, SSTERM('l')))], 'sumeq2dv',
                'sum_ l e. %s sum_ d e. %s %s = %s' % (DVP, DVD, CLD, SS()))
    ssum = st([swap, inner2], 'eqtrd',
              'sum_ d e. %s sum_ l e. %s %s = %s' % (DVD, DVP, CLD, SS()))
    # ---- assemble
    ssr = st([st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())], 'rpred',
             '%s e. RR' % SS())
    lhsr = st([ident, st([finD, sj([gjr, lift(w, innr, AJ2)], 'remulcld',
                                   '( %s x. %s ) e. RR' % (GT('d'), INNER('D')))], 'fsumrecl',
                         'sum_ d e. %s ( %s x. %s ) e. RR' % (DVD, GT('d'), INNER('D')))],
              'eqeltrd', '( ( %s x. ( mmu ` D ) ) x. %s ) e. RR' % (LW('D'), SS()))
    rhsr = st([finD, sj([gjr, jdr], 'remulcld', '( %s x. %s ) e. RR' % (GT('d'), JD('d')))],
              'fsumrecl', 'sum_ d e. %s ( %s x. %s ) e. RR' % (DVD, GT('d'), JD('d')))
    eqchain = st([fib, ssum], 'eqtrd',
                 'sum_ d e. %s ( %s x. %s ) = %s' % (DVD, GT('d'), JD('d'), SS()))
    le1 = st([ident, sumle], 'eqbrtrd',
             '( ( %s x. ( mmu ` D ) ) x. %s ) <_ sum_ d e. %s ( %s x. %s )'
             % (LW('D'), SS(), DVD, GT('d'), JD('d')))
    w.qed([le1, eqchain], 'breqtrd',
          '( %s -> ( ( %s x. ( mmu ` D ) ) x. %s ) <_ %s )' % (A, LW('D'), SS(), SS()))
    return w



def lwabs():
    w = W('lwabs', 'The Selberg weights are bounded by one in absolute value.')
    A = '( %s /\\ D e. NN )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simpr', 'D e. NN')
    lwr = st([w.s([], 'lwre', '( %s -> %s e. RR )' % (A, LW('D')))], 'id',
             '%s e. RR' % LW('D')) if False else w.s([], 'lwre',
                                                     '( %s -> %s e. RR )' % (A, LW('D')))
    # ---- case D || P
    AP = '( %s /\\ D || P )' % A
    d2 = shsteps(w, AP, (A, SH))
    sp = d2['st']
    dnn2 = sp([dnn], 'adantr', 'D e. NN')
    ddp2 = sp([], 'simpr', 'D || P')
    dnnp = sp([dnn2, ddp2], 'jca', '( D e. NN /\\ D || P )')
    lwr2 = sp([lwr], 'adantr', '%s e. RR' % LW('D'))
    muz = sp([sp([dnn2, w.inst('mucl')], 'syl', '( mmu ` D ) e. ZZ')], 'zred',
             '( mmu ` D ) e. RR')
    prodr = sp([lwr2, muz], 'remulcld', '( %s x. ( mmu ` D ) ) e. RR' % LW('D'))
    srp = sp([d2['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())
    ssr = sp([srp], 'rpred', '%s e. RR' % SS())
    ssgt = sp([srp], 'rpgt0d', '0 < %s' % SS())
    vrp = sp([d2['sh'], dnnp, w.inst('vdrp')], 'syl2anc', '( V ` D ) e. RR+')
    ivrp = sp([vrp], 'rpreccld', '( 1 / ( V ` D ) ) e. RR+')
    # TD ( D ) is nonnegative
    finP = sp([d2['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    AL = '( %s /\\ l e. %s )' % (AP, DVP)
    dl = dvpel(w, AL, 'l', d2['pnn'])
    sl = dl['st']
    glrp = sl([lift(w, d2['sh'], AL), sl([dl['nn'], dl['dP']], 'jca', '( l e. NN /\\ l || P )'),
               w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('l'))
    TERM = 'if ( ( D || l /\\ ( l ^ 2 ) <_ Y ) , %s , 0 )' % GT('l')
    termr = sl([sl([glrp], 'rpred', '%s e. RR' % GT('l')),
                w.s([], '0red', '( %s -> 0 e. RR )' % AL)], 'ifcld', '%s e. RR' % TERM)
    ALT = '( %s /\\ ( D || l /\\ ( l ^ 2 ) <_ Y ) )' % AL
    slt = mkst(w, ALT)
    tge1 = slt([slt([lift(w, glrp, ALT)], 'rpge0d', '0 <_ %s' % GT('l')),
                slt([], 'iftrued', '%s = %s' % (TERM, GT('l')))], 'breqtrrd', '0 <_ %s' % TERM)
    ALF = '( %s /\\ -. ( D || l /\\ ( l ^ 2 ) <_ Y ) )' % AL
    slf = mkst(w, ALF)
    tge2 = slf([w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % ALF),
                slf([], 'iffalsed', '%s = 0' % TERM)], 'breqtrrd', '0 <_ %s' % TERM)
    tge = sl([tge1, tge2], 'pm2.61dan', '0 <_ %s' % TERM)
    tdge0 = sp([finP, termr, tge], 'fsumge0', '0 <_ %s' % TD('D'))
    tdr = sp([finP, termr], 'fsumrecl', '%s e. RR' % TD('D'))
    xr = sp([sp([ivrp], 'rpred', '( 1 / ( V ` D ) ) e. RR'), tdr], 'remulcld',
            '( ( 1 / ( V ` D ) ) x. %s ) e. RR' % TD('D'))
    xge0 = sp([sp([ivrp], 'rpred', '( 1 / ( V ` D ) ) e. RR'), tdr,
               sp([ivrp], 'rpge0d', '0 <_ ( 1 / ( V ` D ) )'), tdge0], 'mulge0d',
              '0 <_ ( ( 1 / ( V ` D ) ) x. %s )' % TD('D'))
    lm1 = sp([d2['sh'], dnnp, w.inst('lwmu1')], 'syl2anc',
             '( ( %s x. ( mmu ` D ) ) x. %s ) = ( ( 1 / ( V ` D ) ) x. %s )'
             % (LW('D'), SS(), TD('D')))
    quot = sp([sp([sp([lm1], 'eqcomd',
                      '( ( 1 / ( V ` D ) ) x. %s ) = ( ( %s x. ( mmu ` D ) ) x. %s )'
                      % (TD('D'), LW('D'), SS()))], 'oveq1d',
                  '( ( ( 1 / ( V ` D ) ) x. %s ) / %s ) = '
                  '( ( ( %s x. ( mmu ` D ) ) x. %s ) / %s )'
                  % (TD('D'), SS(), LW('D'), SS(), SS())),
               sp([sp([prodr], 'recnd', '( %s x. ( mmu ` D ) ) e. CC' % LW('D')),
                   sp([srp], 'rpcnd', '%s e. CC' % SS()),
                   sp([srp], 'rpne0d', '%s =/= 0' % SS())], 'divcan4d',
                  '( ( ( %s x. ( mmu ` D ) ) x. %s ) / %s ) = ( %s x. ( mmu ` D ) )'
                  % (LW('D'), SS(), SS(), LW('D')))], 'eqtrd',
              '( ( ( 1 / ( V ` D ) ) x. %s ) / %s ) = ( %s x. ( mmu ` D ) )'
              % (TD('D'), SS(), LW('D')))
    nn0 = sp([sp([xr, tdr and xge0, ssr, ssgt], 'divge0d' if False else 'id', 'x = x')], 'id',
             'x = x') if False else sp([xr, srp, xge0], 'divge0d',
                                       '0 <_ ( ( ( 1 / ( V ` D ) ) x. %s ) / %s )'
                                       % (TD('D'), SS()))
    nonneg = sp([nn0, quot], 'breqtrd', '0 <_ ( %s x. ( mmu ` D ) )' % LW('D'))
    # ---- the bound
    lms = sp([d2['sh'], dnnp, w.inst('lwmuss')], 'syl2anc',
             '( ( %s x. ( mmu ` D ) ) x. %s ) <_ %s' % (LW('D'), SS(), SS()))
    one = w.s([], '1red', '( %s -> 1 e. RR )' % AP)
    lms2 = sp([lms, sp([sp([ssr], 'recnd', '%s e. CC' % SS())], 'mullidd',
                       '( 1 x. %s ) = %s' % (SS(), SS()))], 'breqtrrd',
              '( ( %s x. ( mmu ` D ) ) x. %s ) <_ ( 1 x. %s )' % (LW('D'), SS(), SS()))
    lem = sp([sp([sp([prodr, one, sp([ssr, ssgt], 'jca',
                                     '( %s e. RR /\\ 0 < %s )' % (SS(), SS()))], '3jca',
                     '( ( %s x. ( mmu ` D ) ) e. RR /\\ 1 e. RR /\\ '
                     '( %s e. RR /\\ 0 < %s ) )' % (LW('D'), SS(), SS())),
                 w.inst('lemul1')], 'syl',
                '( ( %s x. ( mmu ` D ) ) <_ 1 <-> '
                '( ( %s x. ( mmu ` D ) ) x. %s ) <_ ( 1 x. %s ) )'
                % (LW('D'), LW('D'), SS(), SS())), lms2], 'mpbird',
             '( %s x. ( mmu ` D ) ) <_ 1' % LW('D'))
    # ---- the absolute value
    dsqf = sp([sp([sp([d2['pnn'], dnn2, ddp2], '3jca', '( P e. NN /\\ D e. NN /\\ D || P )'),
                   w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` D ) =/= 0 )'),
               d2['psqf']], 'mpd', '( mmu ` D ) =/= 0')
    ab1 = sp([sp([dnn2, dsqf], 'jca', '( D e. NN /\\ ( mmu ` D ) =/= 0 )'), w.inst('muabs1')],
             'syl', '( abs ` ( mmu ` D ) ) = 1')
    absr = sp([lwr2], 'recnd', '%s e. CC' % LW('D'))
    e1 = sp([sp([sp([absr], 'abscld', '( abs ` %s ) e. RR' % LW('D'))], 'recnd',
                '( abs ` %s ) e. CC' % LW('D'))], 'mulridd',
            '( ( abs ` %s ) x. 1 ) = ( abs ` %s )' % (LW('D'), LW('D')))
    e2 = sp([sp([ab1], 'oveq2d',
                '( ( abs ` %s ) x. ( abs ` ( mmu ` D ) ) ) = ( ( abs ` %s ) x. 1 )'
                % (LW('D'), LW('D'))), e1], 'eqtrd',
            '( ( abs ` %s ) x. ( abs ` ( mmu ` D ) ) ) = ( abs ` %s )' % (LW('D'), LW('D')))
    e3 = sp([sp([absr, sp([muz], 'recnd', '( mmu ` D ) e. CC')], 'absmuld',
                '( abs ` ( %s x. ( mmu ` D ) ) ) = '
                '( ( abs ` %s ) x. ( abs ` ( mmu ` D ) ) )' % (LW('D'), LW('D'))), e2], 'eqtrd',
            '( abs ` ( %s x. ( mmu ` D ) ) ) = ( abs ` %s )' % (LW('D'), LW('D')))
    e4 = sp([sp([prodr, nonneg], 'jca',
                '( ( %s x. ( mmu ` D ) ) e. RR /\\ 0 <_ ( %s x. ( mmu ` D ) ) )'
                % (LW('D'), LW('D'))), w.inst('absid')], 'syl',
            '( abs ` ( %s x. ( mmu ` D ) ) ) = ( %s x. ( mmu ` D ) )' % (LW('D'), LW('D')))
    case1 = sp([sp([sp([e3], 'eqcomd',
                       '( abs ` %s ) = ( abs ` ( %s x. ( mmu ` D ) ) )' % (LW('D'), LW('D'))),
                    e4], 'eqtrd',
                   '( abs ` %s ) = ( %s x. ( mmu ` D ) )' % (LW('D'), LW('D'))), lem], 'eqbrtrd',
               '( abs ` %s ) <_ 1' % LW('D'))
    # ---- case -. D || P
    AN = '( %s /\\ -. D || P )' % A
    sn = mkst(w, AN)
    zer = sn([sn([], 'simpr', '-. D || P')], 'iffalsed', '%s = 0' % LW('D'))
    case2 = sn([sn([sn([zer], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % LW('D')),
                    sn([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd',
                   '( abs ` %s ) = 0' % LW('D')),
                w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % AN)], 'eqbrtrd',
               '( abs ` %s ) <_ 1' % LW('D'))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> ( abs ` %s ) <_ 1 )' % (A, LW('D')))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['muabs1']:
        wk = globals()[f]()
        runh(wk) if f in ('mucanc',) else wk.run()
