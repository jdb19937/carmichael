"""Sortie z4c: radfib (Lean fiber_inv_sum_le) and sumphiinv (Lean sum_inv_totient_ge)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
from z4clib import STATEMENTS as S, CS, RAD, TS, FLA
from z4c_a import mk, a1


def ifnn(w, et, P, V, Vge):
    """( et -> 0 <_ if ( P , V , 0 ) ) from Vge : ( et -> 0 <_ V )"""
    IF = 'if ( %s , %s , 0 )' % (P, V)
    h1 = w.s([], 'breq2', '( %s = %s -> ( 0 <_ %s <-> 0 <_ %s ) )' % (V, IF, V, IF))
    h2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (IF, IF))
    h3 = w.s([Vge], 'adantr', '( ( %s /\\ %s ) -> 0 <_ %s )' % (et, P, V))
    h4 = w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( ( %s /\\ -. %s ) -> 0 <_ 0 )' % (et, P))
    return w.s([h1, h2, h3, h4], 'ifbothda', '( %s -> 0 <_ %s )' % (et, IF))


def radeq(w, a, b):
    """( a = b -> RAD(a) = RAD(b) )"""
    e1 = w.s([], 'breq2', '( %s = %s -> ( u || %s <-> u || %s ) )' % (a, b, a, b))
    e2 = w.s([e1], 'rabbidv', '( %s = %s -> { u e. Prime | u || %s } = { u e. Prime | u || %s } )' % (a, b, a, b))
    return w.s([e2], 'prodeq1d', '( %s = %s -> %s = %s )' % (a, b, RAD(a), RAD(b)))


def radfib():
    w = W('radfib', 'The harmonic mass of the integers j <_ X coprime to F whose radical is the '
          'squarefree D is at most 1 / phi ( D ) (Lean fiber_inv_sum_le).')
    AR = '( X e. NN /\\ ( D e. NN /\\ ( mmu ` D ) =/= 0 ) )'
    st = mk(w, AR)
    CSX = CS('F', 'X')
    FZ = '( 1 ... X )'
    BW = 'if ( %s = D , ( 1 / w ) , 0 )' % RAD('w')
    BJ = 'if ( D = %s , ( 1 / j ) , 0 )' % RAD('j')
    PRQD = 'prod_ q e. { r e. Prime | r || D } ( 1 / ( 1 - ( 1 / q ) ) )'
    pf = w.s([], 'progfib', '( %s -> sum_ w e. %s %s <_ ( ( 1 / D ) x. %s ) )' % (AR, FZ, BW, PRQD))
    dnn = st([], 'simprl', 'D e. NN')
    phv = st([dnn, w.inst('phiinvpf')], 'syl', '( ( 1 / D ) x. %s ) = ( 1 / ( phi ` D ) )' % PRQD)
    pf2 = st([pf, phv], 'breqtrd', 'sum_ w e. %s %s <_ ( 1 / ( phi ` D ) )' % (FZ, BW))
    # the coprime subset
    AW = '( %s /\\ w e. %s )' % (AR, FZ)
    sw = mk(w, AW)
    wrp = sw([sw([sw([sw([], 'simpr', 'w e. %s' % FZ), w.inst('elfznn')], 'syl', 'w e. NN')], 'nnrpd', 'w e. RR+')],
             'rpreccld', '( 1 / w ) e. RR+')
    bre = sw([sw([wrp], 'rpred', '( 1 / w ) e. RR'), sw([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % BW)
    bge = ifnn(w, AW, '%s = D' % RAD('w'), '( 1 / w )', sw([wrp], 'rpge0d', '0 <_ ( 1 / w )'))
    ss = a1(w, AR, 'ssrab2', '%s C_ %s' % (CSX, FZ))
    less = st([st([], 'fzfid', '%s e. Fin' % FZ), bre, bge, ss], 'fsumless',
              'sum_ w e. %s %s <_ sum_ w e. %s %s' % (CSX, BW, FZ, BW))
    # rename the index and the orientation of the fibre condition
    jw = 'j = w'
    rj = radeq(w, 'j', 'w')
    c1 = w.s([w.s([rj], 'eqeq2d', '( %s -> ( D = %s <-> D = %s ) )' % (jw, RAD('j'), RAD('w'))),
              w.s([], 'eqcom', '( D = %s <-> %s = D )' % (RAD('w'), RAD('w')))], 'bitrdi',
             '( %s -> ( D = %s <-> %s = D ) )' % (jw, RAD('j'), RAD('w')))
    c2 = w.s([], 'oveq2', '( %s -> ( 1 / j ) = ( 1 / w ) )' % jw)
    c3 = w.s([], 'eqidd', '( %s -> 0 = 0 )' % jw)
    cb = w.s([w.s([c1, c2, c3], 'ifbieq12d', '( %s -> %s = %s )' % (jw, BJ, BW))], 'cbvsumv',
             'sum_ j e. %s %s = sum_ w e. %s %s' % (CSX, BJ, CSX, BW))
    ch = st([st([cb], 'a1i', 'sum_ j e. %s %s = sum_ w e. %s %s' % (CSX, BJ, CSX, BW)), less], 'eqbrtrd',
            'sum_ j e. %s %s <_ sum_ w e. %s %s' % (CSX, BJ, FZ, BW))
    phire = st([st([st([st([dnn], 'phicld', '( phi ` D ) e. NN')], 'nnrpd', '( phi ` D ) e. RR+')], 'rpreccld',
                   '( 1 / ( phi ` D ) ) e. RR+')], 'rpred', '( 1 / ( phi ` D ) ) e. RR')
    fzfin = st([], 'fzfid', '%s e. Fin' % FZ)
    csfin = st([fzfin, ss], 'ssfid', '%s e. Fin' % CSX)
    AJ = '( %s /\\ j e. %s )' % (AR, CSX)
    sj = mk(w, AJ)
    jrp = sj([sj([sj([sj([a1(w, AJ, 'ssrab2', '%s C_ %s' % (CSX, FZ)), sj([], 'simpr', 'j e. %s' % CSX)], 'sseldd',
                          'j e. %s' % FZ), w.inst('elfznn')], 'syl', 'j e. NN')], 'nnrpd', 'j e. RR+')],
             'rpreccld', '( 1 / j ) e. RR+')
    bjre = sj([sj([jrp], 'rpred', '( 1 / j ) e. RR'), sj([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % BJ)
    lre = st([csfin, bjre], 'fsumrecl', 'sum_ j e. %s %s e. RR' % (CSX, BJ))
    mre = st([fzfin, bre], 'fsumrecl', 'sum_ w e. %s %s e. RR' % (FZ, BW))
    w.qed([lre, mre, phire, ch, pf2], 'letrd', S['radfib'])
    return w


ALL = {'radfib': radfib}


def elrabst(w, ante, mem, x, X, B, cond_x, cond_X, hyp):
    """( ante -> ( X e. B /\\ cond_X ) ) from mem : ( ante -> X e. { x e. B | cond_x } ); hyp : ( x = X -> ( cond_x <-> cond_X ) )"""
    SET = '{ %s e. %s | %s }' % (x, B, cond_x)
    el = w.s([hyp], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (X, SET, X, B, cond_X))
    return w.s([mem, w.s([el], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. %s /\\ %s ) ) )' % (ante, X, SET, X, B, cond_X))],
               'mpbid', '( %s -> ( %s e. %s /\\ %s ) )' % (ante, X, B, cond_X))


def tcond(r):
    return '( ( mmu ` %s ) =/= 0 /\\ ( %s gcd F ) = 1 )' % (r, r)


def tcondeq(w, a, b):
    """( a = b -> ( tcond(a) <-> tcond(b) ) )"""
    m = w.s([w.s([], 'fveq2', '( %s = %s -> ( mmu ` %s ) = ( mmu ` %s ) )' % (a, b, a, b))], 'neeq1d',
            '( %s = %s -> ( ( mmu ` %s ) =/= 0 <-> ( mmu ` %s ) =/= 0 ) )' % (a, b, a, b))
    g = w.s([w.s([], 'oveq1', '( %s = %s -> ( %s gcd F ) = ( %s gcd F ) )' % (a, b, a, b))], 'eqeq1d',
            '( %s = %s -> ( ( %s gcd F ) = 1 <-> ( %s gcd F ) = 1 ) )' % (a, b, a, b))
    return w.s([m, g], 'anbi12d', '( %s = %s -> ( %s <-> %s ) )' % (a, b, tcond(a), tcond(b)))


def sumphiinv():
    w = W('sumphiinv', 'The totient-quotient lower bound (Lean sum_inv_totient_ge): ( phi ( F ) / F ) log A '
          'is at most the sum of 1 / phi ( r ) over the squarefree r <_ A coprime to F.')
    AS = '( F e. NN /\\ A e. RR /\\ 1 <_ A )'
    st = mk(w, AS)
    X = FLA
    FZ = '( 1 ... %s )' % X
    CSX = CS('F', X)
    T = TS(X, 'F')
    INN = lambda d, j='j': 'if ( %s = %s , ( 1 / %s ) , 0 )' % (d, RAD(j), j)
    SJ = 'sum_ j e. %s ( 1 / j )' % CSX
    SDJ = 'sum_ d e. %s sum_ j e. %s %s' % (T, CSX, INN('d'))
    SJD = 'sum_ j e. %s sum_ d e. %s %s' % (CSX, T, INN('d'))
    SD = 'sum_ d e. %s ( 1 / ( phi ` d ) )' % T
    LHS = '( ( ( phi ` F ) / F ) x. ( log ` A ) )'
    fnn = st([], 'simp1', 'F e. NN')
    are = st([], 'simp2', 'A e. RR')
    a1le = st([], 'simp3', '1 <_ A')
    xnn = st([are, a1le, w.inst('flge1nn')], 'syl2anc', '%s e. NN' % X)
    xz = st([xnn], 'nnzd', '%s e. ZZ' % X)
    fzfin = st([], 'fzfid', '%s e. Fin' % FZ)
    csfin = st([fzfin, a1(w, AS, 'ssrab2', '%s C_ %s' % (CSX, FZ))], 'ssfid', '%s e. Fin' % CSX)
    tfin = st([fzfin, a1(w, AS, 'ssrab2', '%s C_ %s' % (T, FZ))], 'ssfid', '%s e. Fin' % T)
    c1 = w.s([], 'cophrmfl', '( %s -> %s <_ %s )' % (AS, LHS, SJ))
    cseq = w.s([w.s([], 'oveq1', '( x = j -> ( x gcd F ) = ( j gcd F ) )')], 'eqeq1d',
               '( x = j -> ( ( x gcd F ) = 1 <-> ( j gcd F ) = 1 ) )')

    def jfacts(ante, jmem):
        s = mk(w, ante)
        jc = elrabst(w, ante, jmem, 'x', 'j', FZ, '( x gcd F ) = 1', '( j gcd F ) = 1', cseq)
        jfz = s([jc], 'simpld', 'j e. %s' % FZ)
        jnn = s([jfz, w.inst('elfznn')], 'syl', 'j e. NN')
        jrp = s([s([jnn], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
        return jc, jfz, jnn, jrp

    # the radical of j lies in T, and the fibre decomposition of 1 / j
    AJ = '( %s /\\ j e. %s )' % (AS, CSX)
    sj = mk(w, AJ)
    jc, jfz, jnn, jrp = jfacts(AJ, sj([], 'simpr', 'j e. %s' % CSX))
    R = RAD('j')
    rl = sj([jnn, w.inst('radlem')], 'syl',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = { u e. Prime | u || j } /\\ %s || j )' % (R, R, R, R))
    r1 = sj([rl], 'simp1d', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (R, R))
    rnn = sj([r1], 'simpld', '%s e. NN' % R)
    rmu = sj([r1], 'simprd', '( mmu ` %s ) =/= 0' % R)
    rdv = sj([rl], 'simp3d', '%s || j' % R)
    rz = sj([rnn], 'nnzd', '%s e. ZZ' % R)
    rle = sj([sj([rz, jnn, w.inst('dvdsle')], 'syl2anc', '( %s || j -> %s <_ j )' % (R, R)), rdv], 'mpd', '%s <_ j' % R)
    jlx = sj([jfz, w.inst('elfzle2')], 'syl', 'j <_ %s' % X)
    rlx = sj([sj([rnn], 'nnred', '%s e. RR' % R), sj([jnn], 'nnred', 'j e. RR'),
              sj([sj([xnn], 'adantr', '%s e. NN' % X)], 'nnred', '%s e. RR' % X), rle, jlx],
             'letrd', '%s <_ %s' % (R, X))
    rfz = sj([sj([sj([xz], 'adantr', '%s e. ZZ' % X), w.inst('fznn')], 'syl',
                 '( %s e. %s <-> ( %s e. NN /\\ %s <_ %s ) )' % (R, FZ, R, R, X)),
              sj([rnn, rlx], 'jca', '( %s e. NN /\\ %s <_ %s )' % (R, R, X))], 'mpbird', '%s e. %s' % (R, FZ))
    fz_ = sj([fnn], 'adantr', 'F e. NN')
    fzz = sj([fz_], 'nnzd', 'F e. ZZ')
    jz = sj([jnn], 'nnzd', 'j e. ZZ')
    jg = sj([jc], 'simprd', '( j gcd F ) = 1')
    fj = sj([sj([jz, fzz, w.inst('gcdcom')], 'syl2anc', '( j gcd F ) = ( F gcd j )'), jg], 'eqtr3d', '( F gcd j ) = 1')
    frg = sj([sj([fzz, rz, jz], '3jca', '( F e. ZZ /\\ %s e. ZZ /\\ j e. ZZ )' % R),
              sj([fj, rdv], 'jca', '( ( F gcd j ) = 1 /\\ %s || j )' % R), w.inst('rpdvds')], 'syl2anc',
             '( F gcd %s ) = 1' % R)
    rgf = sj([sj([rz, fzz, w.inst('gcdcom')], 'syl2anc', '( %s gcd F ) = ( F gcd %s )' % (R, R)), frg], 'eqtrd',
             '( %s gcd F ) = 1' % R)
    TSET = T
    elT = w.s([tcondeq(w, 'r', R)], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (R, TSET, R, FZ, tcond(R)))
    rT = sj([sj([elT], 'a1i', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (R, TSET, R, FZ, tcond(R))),
             sj([rfz, sj([rmu, rgf], 'jca', tcond(R))], 'jca', '( %s e. %s /\\ %s )' % (R, FZ, tcond(R)))],
            'mpbird', '%s e. %s' % (R, TSET))
    tfin_j = sj([tfin], 'adantr', '%s e. Fin' % T)
    jcc = sj([sj([jrp], 'rpred', '( 1 / j ) e. RR')], 'recnd', '( 1 / j ) e. CC')
    ite = sj([w.s([], 'eqidd', '( d = %s -> ( 1 / j ) = ( 1 / j ) )' % R), tfin_j, rT, jcc], 'sumite',
             'sum_ d e. %s %s = ( 1 / j )' % (T, INN('d')))
    e1 = st([sj([ite], 'eqcomd', '( 1 / j ) = sum_ d e. %s %s' % (T, INN('d')))], 'sumeq2dv', '%s = %s' % (SJ, SJD))
    # swap the two sums
    AJD = '( %s /\\ ( j e. %s /\\ d e. %s ) )' % (AS, CSX, T)
    sjd = mk(w, AJD)
    _, _, _, jrp2 = jfacts(AJD, sjd([], 'simprl', 'j e. %s' % CSX))
    icc = sjd([sjd([sjd([jrp2], 'rpred', '( 1 / j ) e. RR')], 'recnd', '( 1 / j ) e. CC'), sjd([], '0cnd', '0 e. CC')],
              'ifcld', '%s e. CC' % INN('d'))
    e2 = st([csfin, tfin, icc], 'fsumcom', '%s = %s' % (SJD, SDJ))
    # the fibre bound at each d
    AD = '( %s /\\ d e. %s )' % (AS, T)
    sd = mk(w, AD)
    dc = elrabst(w, AD, sd([], 'simpr', 'd e. %s' % T), 'r', 'd', FZ, tcond('r'), tcond('d'), tcondeq(w, 'r', 'd'))
    dfz = sd([dc], 'simpld', 'd e. %s' % FZ)
    dnn = sd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    dmu = sd([sd([dc], 'simprd', tcond('d'))], 'simpld', '( mmu ` d ) =/= 0')
    fib = sd([sd([xnn], 'adantr', '%s e. NN' % X), sd([dnn, dmu], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'),
              w.inst('radfib')], 'syl2anc', 'sum_ j e. %s %s <_ ( 1 / ( phi ` d ) )' % (CSX, INN('d')))
    AA3 = '( %s /\\ j e. %s )' % (AD, CSX)
    s3 = mk(w, AA3)
    _, _, _, jrp3 = jfacts(AA3, s3([], 'simpr', 'j e. %s' % CSX))
    ire = s3([s3([jrp3], 'rpred', '( 1 / j ) e. RR'), s3([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % INN('d'))
    innre = sd([sd([csfin], 'adantr', '%s e. Fin' % CSX), ire], 'fsumrecl', 'sum_ j e. %s %s e. RR' % (CSX, INN('d')))
    phdre = sd([sd([sd([sd([dnn], 'phicld', '( phi ` d ) e. NN')], 'nnrpd', '( phi ` d ) e. RR+')], 'rpreccld',
                   '( 1 / ( phi ` d ) ) e. RR+')], 'rpred', '( 1 / ( phi ` d ) ) e. RR')
    le = st([tfin, innre, phdre, fib], 'fsumle', '%s <_ %s' % (SDJ, SD))
    sjle = st([st([e1, e2], 'eqtrd', '%s = %s' % (SJ, SDJ)), le], 'eqbrtrd', '%s <_ %s' % (SJ, SD))
    # reals of the chain
    apos = st([st([], '0red', '0 e. RR'), st([], '1red', '1 e. RR'), are, a1(w, AS, '0lt1', '0 < 1'), a1le],
              'ltletrd', '0 < A')
    arp = st([are, apos], 'elrpd', 'A e. RR+')
    lhsre = st([st([st([st([fnn], 'phicld', '( phi ` F ) e. NN')], 'nnred', '( phi ` F ) e. RR'),
                    st([fnn], 'nnred', 'F e. RR'), st([fnn], 'nnne0d', 'F =/= 0')], 'redivcld', '( ( phi ` F ) / F ) e. RR'),
                st([arp], 'relogcld', '( log ` A ) e. RR')], 'remulcld', '%s e. RR' % LHS)
    sjre = st([csfin, sj([jrp], 'rpred', '( 1 / j ) e. RR')], 'fsumrecl', '%s e. RR' % SJ)
    sdre = st([tfin, phdre], 'fsumrecl', '%s e. RR' % SD)
    ch = st([lhsre, sjre, sdre, c1, sjle], 'letrd', '%s <_ %s' % (LHS, SD))
    cb = w.s([w.s([w.s([], 'fveq2', '( d = r -> ( phi ` d ) = ( phi ` r ) )')], 'oveq2d',
                  '( d = r -> ( 1 / ( phi ` d ) ) = ( 1 / ( phi ` r ) ) )')], 'cbvsumv',
             '%s = sum_ r e. %s ( 1 / ( phi ` r ) )' % (SD, T))
    w.qed([ch, st([cb], 'a1i', '%s = sum_ r e. %s ( 1 / ( phi ` r ) )' % (SD, T))], 'breqtrd', S['sumphiinv'])
    return w


ALL['sumphiinv'] = sumphiinv


if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
