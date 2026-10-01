"""Sortie v3: the smooth-number factorisation for the Euler-product bound.

smsplit  ( ( ( Z e. Prime /\\ W e. NN ) /\\ N e. SM( ( Q u. { Z } ) , W ) ) ->
             ( ( Z pCnt N ) e. ( 0 ... W ) /\\
               ( N / ( Z ^ ( Z pCnt N ) ) ) e. SM( Q , W ) /\\
               ( ( Z ^ ( Z pCnt N ) ) x. ( N / ( Z ^ ( Z pCnt N ) ) ) ) = N ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst, SMS, smel
from cl import lift

QZ = '( Q u. { Z } )'
SU = SMS(QZ, 'W')
ST = SMS('Q', 'W')
K = '( Z pCnt N )'
ZK = '( Z ^ %s )' % K
B = '( N / %s )' % ZK
A = '( ( Z e. Prime /\\ W e. NN ) /\\ N e. %s )' % SU


def smsplit():
    w = WS('smsplit', 'A Q-and-Z-smooth integer splits as a power of Z times a Q-smooth '
                      'integer, with the exponent bounded by the range.')
    st = mkst(w, A)
    zp = st([], 'simpll', 'Z e. Prime')
    wnn = st([], 'simplr', 'W e. NN')
    nu = st([], 'simpr', 'N e. %s' % SU)
    el = smel(w, A, st, 'N', QZ, 'W')
    memb = st([st([el], 'a1i',
                  '( N e. %s <-> ( N e. ( 1 ... W ) /\\ { r e. Prime | r || N } C_ %s ) )'
                  % (SU, QZ)), nu], 'mpbid',
              '( N e. ( 1 ... W ) /\\ { r e. Prime | r || N } C_ %s )' % QZ)
    nfz = st([memb], 'simpld', 'N e. ( 1 ... W )')
    npf = st([memb], 'simprd', '{ r e. Prime | r || N } C_ %s' % QZ)
    nnn = st([nfz, w.inst('elfznn')], 'syl', 'N e. NN')
    nlew = st([nfz, w.inst('elfzle2')], 'syl', 'N <_ W')
    znn = st([zp, w.inst('prmnn')], 'syl', 'Z e. NN')
    kn0 = st([zp, nnn, w.inst('pccl')], 'syl2anc', '%s e. NN0' % K)
    zknn = st([znn, kn0], 'nnexpcld', '%s e. NN' % ZK)
    dvd = st([zp, nnn, w.inst('pcdvds')], 'syl2anc', '%s || N' % ZK)
    bnn = st([st([nnn, zknn, w.inst('nndivdvds')], 'syl2anc',
                 '( %s || N <-> %s e. NN )' % (ZK, B)), dvd], 'mpbid', '%s e. NN' % B)
    nc = st([nnn], 'nncnd', 'N e. CC')
    zkc = st([zknn], 'nncnd', '%s e. CC' % ZK)
    zkne = st([zknn], 'nnne0d', '%s =/= 0' % ZK)
    prod = st([nc, zkc, zkne, w.inst('divcan2')], 'syl3anc', '( %s x. %s ) = N' % (ZK, B))
    # ( N / ZK ) || N
    bz = st([bnn], 'nnzd', '%s e. ZZ' % B)
    zkz = st([zknn], 'nnzd', '%s e. ZZ' % ZK)
    bdv0 = st([zkz, bz, w.inst('dvdsmul2')], 'syl2anc', '%s || ( %s x. %s )' % (B, ZK, B))
    bdv = st([bdv0, prod], 'breqtrd', '%s || N' % B)
    blen = st([st([bz, nnn, w.inst('dvdsle')], 'syl2anc', '( %s || N -> %s <_ N )' % (B, B)),
               bdv], 'mpd', '%s <_ N' % B)
    bre = st([bnn], 'nnred', '%s e. RR' % B)
    nre = st([nnn], 'nnred', 'N e. RR')
    wre = st([wnn], 'nnred', 'W e. RR')
    blew = st([bre, nre, wre, blen, nlew], 'letrd', '%s <_ W' % B)
    bfz = st([st([bnn, wnn, blew], '3jca', '( %s e. NN /\\ W e. NN /\\ %s <_ W )' % (B, B)),
              st([w.s([], 'elfz1b',
                      '( %s e. ( 1 ... W ) <-> ( %s e. NN /\\ W e. NN /\\ %s <_ W ) )' % (B, B, B))],
                 'a1i', '( %s e. ( 1 ... W ) <-> ( %s e. NN /\\ W e. NN /\\ %s <_ W ) )' % (B, B, B))],
             'mpbird', '%s e. ( 1 ... W )' % B)
    # the prime divisors of B lie in Q
    AP = '( %s /\\ p e. { r e. Prime | r || %s } )' % (A, B)
    sp = mkst(w, AP)
    sbp = w.s([w.s([], 'breq1', '( r = p -> ( r || %s <-> p || %s ) )' % (B, B))], 'elrab',
              '( p e. { r e. Prime | r || %s } <-> ( p e. Prime /\\ p || %s ) )' % (B, B))
    pmem = sp([sp([sbp], 'a1i',
                  '( p e. { r e. Prime | r || %s } <-> ( p e. Prime /\\ p || %s ) )' % (B, B)),
               sp([], 'simpr', 'p e. { r e. Prime | r || %s }' % B)], 'mpbid',
              '( p e. Prime /\\ p || %s )' % B)
    pprm = sp([pmem], 'simpld', 'p e. Prime')
    pdb = sp([pmem], 'simprd', 'p || %s' % B)
    pz = sp([sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')], 'nnzd', 'p e. ZZ')
    pdn = sp([sp([sp([pz, lift(w, bz, AP), lift(w, st([nnn], 'nnzd', 'N e. ZZ'), AP)], '3jca',
                     '( p e. ZZ /\\ %s e. ZZ /\\ N e. ZZ )' % B), w.inst('dvdstr')], 'syl',
                  '( ( p || %s /\\ %s || N ) -> p || N )' % (B, B)),
               sp([pdb, lift(w, bdv, AP)], 'jca', '( p || %s /\\ %s || N )' % (B, B))],
              'mpd', 'p || N')
    sbn = w.s([w.s([], 'breq1', '( r = p -> ( r || N <-> p || N ) )')], 'elrab',
              '( p e. { r e. Prime | r || N } <-> ( p e. Prime /\\ p || N ) )')
    pinn = sp([sp([sbn], 'a1i',
                  '( p e. { r e. Prime | r || N } <-> ( p e. Prime /\\ p || N ) )'),
               sp([pprm, pdn], 'jca', '( p e. Prime /\\ p || N )')], 'mpbird',
              'p e. { r e. Prime | r || N }')
    pqz = sp([lift(w, npf, AP), pinn], 'sseldd', 'p e. %s' % QZ)
    por = sp([sp([w.s([], 'elun', '( p e. %s <-> ( p e. Q \\/ p e. { Z } ) )' % QZ)], 'a1i',
                 '( p e. %s <-> ( p e. Q \\/ p e. { Z } ) )' % QZ), pqz], 'mpbid',
             '( p e. Q \\/ p e. { Z } )')
    # p = Z is impossible
    ndz = sp([lift(w, zp, AP), lift(w, nnn, AP), w.inst('pcndvds2')], 'syl2anc',
             '-. Z || %s' % B)
    # ( p e. { Z } -> Z || B ) under sp
    APZ2 = '( %s /\\ p e. { Z } )' % AP
    s2 = mkst(w, APZ2)
    peq = s2([s2([], 'simpr', 'p e. { Z }'), w.inst('elsni')], 'syl', 'p = Z')
    zd2 = s2([s2([peq], 'breq1d', '( p || %s <-> Z || %s )' % (B, B)), lift(w, pdb, APZ2)],
             'mpbid', 'Z || %s' % B)
    nel2 = sp([zd2, lift(w, ndz, AP)], 'mtand', '-. p e. { Z }')
    pinq = sp([sp([por], 'ord', '( -. p e. Q -> p e. { Z } )'), nel2], 'mt3d', 'p e. Q')
    bpfimp = st([pinq], 'ex', '( p e. { r e. Prime | r || %s } -> p e. Q )' % B)
    bpf = st([bpfimp], 'ssrdv', '{ r e. Prime | r || %s } C_ Q' % B)
    # B is Q-smooth
    elb = smel(w, A, st, B, 'Q', 'W')
    bsm = st([st([bfz, bpf], 'jca',
                 '( %s e. ( 1 ... W ) /\\ { r e. Prime | r || %s } C_ Q )' % (B, B)),
              st([elb], 'a1i',
                 '( %s e. %s <-> ( %s e. ( 1 ... W ) /\\ { r e. Prime | r || %s } C_ Q ) )'
                 % (B, ST, B, B))], 'mpbird', '%s e. %s' % (B, ST))
    # the exponent is at most W
    zuz = st([zp, w.inst('prmuz2')], 'syl', 'Z e. ( ZZ>= ` 2 )')
    ber = st([zuz, kn0, w.inst('bernneq3')], 'syl2anc', '%s < %s' % (K, ZK))
    zkle = st([st([zkz, nnn, w.inst('dvdsle')], 'syl2anc', '( %s || N -> %s <_ N )' % (ZK, ZK)),
               dvd], 'mpd', '%s <_ N' % ZK)
    kre = st([kn0], 'nn0red', '%s e. RR' % K)
    zkre = st([zknn], 'nnred', '%s e. RR' % ZK)
    from lin import linarith
    klew = linarith(w, A, [ber, zkle, nlew], '%s <_ W' % K,
                    leaves={K: kre, ZK: zkre, 'N': nre, 'W': wre})
    wn0 = st([wnn], 'nnnn0d', 'W e. NN0')
    kfz = st([st([kn0, klew], 'jca', '( %s e. NN0 /\\ %s <_ W )' % (K, K)),
              st([wn0, w.inst('fznn0')], 'syl',
                 '( %s e. ( 0 ... W ) <-> ( %s e. NN0 /\\ %s <_ W ) )' % (K, K, K))],
             'mpbird', '%s e. ( 0 ... W )' % K)
    w.qed([kfz, bsm, prod], '3jca',
          '( %s -> ( %s e. ( 0 ... W ) /\\ %s e. %s /\\ ( %s x. %s ) = N ) )'
          % (A, K, B, ST, ZK, B))
    return w





# ------------------------------------------------------------------ injection
AF = '( Z e. Prime /\\ W e. NN )'


def PAIR(t):
    return '<. ( Z pCnt %s ) , ( %s / ( Z ^ ( Z pCnt %s ) ) ) >.' % (t, t, t)


FMAP = '( t e. %s |-> %s )' % (SU, PAIR('t'))
XW = '( ( 0 ... W ) X. %s )' % ST


def smsumf1():
    w = WS('smsumf1', 'The map taking a Q-and-Z-smooth integer to its Z-exponent and its '
                      'Q-smooth part is injective into the product of the two ranges.')
    st = mkst(w, AF)
    zp = st([], 'simpl', 'Z e. Prime')
    wnn = st([], 'simpr', 'W e. NN')
    # the substitution hypothesis of f1mpt
    sb1 = w.s([], 'oveq2', '( t = s -> ( Z pCnt t ) = ( Z pCnt s ) )')
    sb2a = w.s([sb1], 'oveq2d', '( t = s -> ( Z ^ ( Z pCnt t ) ) = ( Z ^ ( Z pCnt s ) ) )')
    sb2 = w.s([w.s([], 'id', '( t = s -> t = s )'), sb2a], 'oveq12d',
              '( t = s -> ( t / ( Z ^ ( Z pCnt t ) ) ) = ( s / ( Z ^ ( Z pCnt s ) ) ) )')
    sb = w.s([sb1, sb2], 'opeq12d', '( t = s -> %s = %s )' % (PAIR('t'), PAIR('s')))
    eqi = w.s([], 'eqid', '%s = %s' % (FMAP, FMAP))
    bic = w.s([eqi, sb], 'f1mpt',
              '( %s : %s -1-1-> %s <-> ( A. t e. %s %s e. %s /\\ '
              'A. t e. %s A. s e. %s ( %s = %s -> t = s ) ) )'
              % (FMAP, SU, XW, SU, PAIR('t'), XW, SU, SU, PAIR('t'), PAIR('s')))
    # maps into the product
    AT = '( %s /\\ t e. %s )' % (AF, SU)
    stt = mkst(w, AT)
    sp = stt([], 'id', AT)
    spl = stt([sp, w.inst('smsplit')], 'syl',
              '( ( Z pCnt t ) e. ( 0 ... W ) /\\ %s e. %s /\\ ( ( Z ^ ( Z pCnt t ) ) x. %s ) = t )'
              % ('( t / ( Z ^ ( Z pCnt t ) ) )', ST, '( t / ( Z ^ ( Z pCnt t ) ) )'))
    k1 = stt([spl], 'simp1d', '( Z pCnt t ) e. ( 0 ... W )')
    b1 = stt([spl], 'simp2d', '( t / ( Z ^ ( Z pCnt t ) ) ) e. %s' % ST)
    pxp = stt([k1, b1, w.inst('opelxpi')], 'syl2anc', '%s e. %s' % (PAIR('t'), XW))
    r1 = st([pxp], 'ralrimiva', 'A. t e. %s %s e. %s' % (SU, PAIR('t'), XW))
    # injectivity
    AST = '( ( %s /\\ t e. %s ) /\\ s e. %s )' % (AF, SU, SU)
    sts = mkst(w, AST)
    afs = sts([sts([], 'simpl', AT)], 'simpld', AF)
    ssu = sts([], 'simpr', 's e. %s' % SU)
    spl2 = sts([sts([afs, ssu], 'jca', '( %s /\\ s e. %s )' % (AF, SU)), w.inst('smsplit')],
               'syl',
               '( ( Z pCnt s ) e. ( 0 ... W ) /\\ %s e. %s /\\ ( ( Z ^ ( Z pCnt s ) ) x. %s ) = s )'
               % ('( s / ( Z ^ ( Z pCnt s ) ) )', ST, '( s / ( Z ^ ( Z pCnt s ) ) )'))
    prods = sts([spl2], 'simp3d', '( ( Z ^ ( Z pCnt s ) ) x. ( s / ( Z ^ ( Z pCnt s ) ) ) ) = s')
    prodt = sts([lift(w, spl, AST)], 'simp3d',
                '( ( Z ^ ( Z pCnt t ) ) x. ( t / ( Z ^ ( Z pCnt t ) ) ) ) = t')
    kex = w.s([], 'ovex', '( Z pCnt t ) e. _V')
    bex = w.s([], 'ovex', '( t / ( Z ^ ( Z pCnt t ) ) ) e. _V')
    oth = w.s([kex, bex], 'opth',
              '( %s = %s <-> ( ( Z pCnt t ) = ( Z pCnt s ) /\\ %s = %s ) )'
              % (PAIR('t'), PAIR('s'),
                 '( t / ( Z ^ ( Z pCnt t ) ) )', '( s / ( Z ^ ( Z pCnt s ) ) )'))
    APE = '( %s /\\ %s = %s )' % (AST, PAIR('t'), PAIR('s'))
    spe = mkst(w, APE)
    cnj = spe([spe([oth], 'a1i',
                   '( %s = %s <-> ( ( Z pCnt t ) = ( Z pCnt s ) /\\ %s = %s ) )'
                   % (PAIR('t'), PAIR('s'),
                      '( t / ( Z ^ ( Z pCnt t ) ) )', '( s / ( Z ^ ( Z pCnt s ) ) )')),
               spe([], 'simpr', '%s = %s' % (PAIR('t'), PAIR('s')))], 'mpbid',
              '( ( Z pCnt t ) = ( Z pCnt s ) /\\ %s = %s )'
              % ('( t / ( Z ^ ( Z pCnt t ) ) )', '( s / ( Z ^ ( Z pCnt s ) ) )'))
    keq = spe([cnj], 'simpld', '( Z pCnt t ) = ( Z pCnt s )')
    beq = spe([cnj], 'simprd',
              '( t / ( Z ^ ( Z pCnt t ) ) ) = ( s / ( Z ^ ( Z pCnt s ) ) )')
    zkeq = spe([keq], 'oveq2d', '( Z ^ ( Z pCnt t ) ) = ( Z ^ ( Z pCnt s ) )')
    mm = spe([zkeq, beq], 'oveq12d',
             '( ( Z ^ ( Z pCnt t ) ) x. ( t / ( Z ^ ( Z pCnt t ) ) ) ) = '
             '( ( Z ^ ( Z pCnt s ) ) x. ( s / ( Z ^ ( Z pCnt s ) ) ) )')
    teqs = spe([spe([lift(w, prodt, APE)], 'eqcomd',
                    't = ( ( Z ^ ( Z pCnt t ) ) x. ( t / ( Z ^ ( Z pCnt t ) ) ) )'),
                spe([mm, lift(w, prods, APE)], 'eqtrd',
                    '( ( Z ^ ( Z pCnt t ) ) x. ( t / ( Z ^ ( Z pCnt t ) ) ) ) = s')],
               'eqtrd', 't = s')
    ex1 = sts([teqs], 'ex', '( %s = %s -> t = s )' % (PAIR('t'), PAIR('s')))
    r2a = stt([ex1], 'ralrimiva', 'A. s e. %s ( %s = %s -> t = s )' % (SU, PAIR('t'), PAIR('s')))
    r2 = st([r2a], 'ralrimiva',
            'A. t e. %s A. s e. %s ( %s = %s -> t = s )' % (SU, SU, PAIR('t'), PAIR('s')))
    both = st([r1, r2], 'jca',
              '( A. t e. %s %s e. %s /\\ A. t e. %s A. s e. %s ( %s = %s -> t = s ) )'
              % (SU, PAIR('t'), XW, SU, SU, PAIR('t'), PAIR('s')))
    w.qed([st([bic], 'a1i',
              '( %s : %s -1-1-> %s <-> ( A. t e. %s %s e. %s /\\ '
              'A. t e. %s A. s e. %s ( %s = %s -> t = s ) ) )'
              % (FMAP, SU, XW, SU, PAIR('t'), XW, SU, SU, PAIR('t'), PAIR('s'))), both],
          'mpbird', '( %s -> %s : %s -1-1-> %s )' % (AF, FMAP, SU, XW))
    return w


ALL = {'smsplit': smsplit, 'smsumf1': smsumf1}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
