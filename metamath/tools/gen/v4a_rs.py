"""Sortie v4a: the radical-fibre factorisation for the inflated-density sum."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import RS, SMS, DEN, mkst, rsel, smel, pfel
from cl import lift
from lin import linarith

QZ = '( Q u. { Z } )'
SU = RS(QZ, 'C')
ST = RS('Q', 'C')
K = '( Z pCnt N )'
ZK = '( Z ^ %s )' % K
B = '( N / %s )' % ZK
AR = '( ( ( Z e. Prime /\\ C e. NN ) /\\ -. Z e. Q ) /\\ N e. %s )' % SU


def rssplit():
    w = WS('rssplit', 'An integer whose prime divisors are exactly Q and Z splits as a '
                      'positive power of Z times an integer whose prime divisors are exactly Q.')
    st = mkst(w, AR)
    zp = st([], 'simplll', 'Z e. Prime')
    cnn = st([], 'simpllr', 'C e. NN')
    nzq = st([], 'simplr', '-. Z e. Q')
    nsu = st([], 'simpr', 'N e. %s' % SU)
    el = rsel(w, 'N', QZ, 'C')
    memb = st([st([el], 'a1i',
                  '( N e. %s <-> ( N e. ( 1 ... C ) /\\ { r e. Prime | r || N } = %s ) )'
                  % (SU, QZ)), nsu], 'mpbid',
              '( N e. ( 1 ... C ) /\\ { r e. Prime | r || N } = %s )' % QZ)
    nfz = st([memb], 'simpld', 'N e. ( 1 ... C )')
    pfeq = st([memb], 'simprd', '{ r e. Prime | r || N } = %s' % QZ)
    nnn = st([nfz, w.inst('elfznn')], 'syl', 'N e. NN')
    pfss = st([pfeq], 'eqimssd', '{ r e. Prime | r || N } C_ %s' % QZ)
    sel = smel(w, 'N', QZ, 'C')
    nsm = st([st([nfz, pfss], 'jca',
                 '( N e. ( 1 ... C ) /\\ { r e. Prime | r || N } C_ %s )' % QZ),
              st([sel], 'a1i',
                 '( N e. %s <-> ( N e. ( 1 ... C ) /\\ { r e. Prime | r || N } C_ %s ) )'
                 % (SMS(QZ, 'C'), QZ))], 'mpbird', 'N e. %s' % SMS(QZ, 'C'))
    spl = st([st([st([zp, cnn], 'jca', '( Z e. Prime /\\ C e. NN )'), nsm], 'jca',
                 '( ( Z e. Prime /\\ C e. NN ) /\\ N e. %s )' % SMS(QZ, 'C')),
              w.inst('smsplit')], 'syl',
             '( %s e. ( 0 ... C ) /\\ %s e. %s /\\ ( %s x. %s ) = N )'
             % (K, B, SMS('Q', 'C'), ZK, B))
    kfz0 = st([spl], 'simp1d', '%s e. ( 0 ... C )' % K)
    bsm = st([spl], 'simp2d', '%s e. %s' % (B, SMS('Q', 'C')))
    prod = st([spl], 'simp3d', '( %s x. %s ) = N' % (ZK, B))
    # the exponent is at least 1
    zvv = st([st([st([zp, w.inst('prmnn')], 'syl', 'Z e. NN')], 'nnred', 'Z e. RR')], 'elexd',
             'Z e. _V')
    zqz = st([st([w.s([], 'ssun2', '{ Z } C_ %s' % QZ)], 'a1i', '{ Z } C_ %s' % QZ),
              st([zvv, w.inst('snidg')], 'syl', 'Z e. { Z }')], 'sseldd', 'Z e. %s' % QZ)
    zpf = st([zqz, st([pfeq], 'eqcomd', '%s = { r e. Prime | r || N }' % QZ)], 'eleqtrd',
             'Z e. { r e. Prime | r || N }')
    pe = pfel(w, 'Z', 'N')
    zdvd = st([st([st([pe], 'a1i',
                      '( Z e. { r e. Prime | r || N } <-> ( Z e. Prime /\\ Z || N ) )'),
                   zpf], 'mpbid', '( Z e. Prime /\\ Z || N )')], 'simprd', 'Z || N')
    knn = st([st([zp, nnn, w.inst('pcelnn')], 'syl2anc', '( %s e. NN <-> Z || N )' % K),
              zdvd], 'mpbird', '%s e. NN' % K)
    klec = st([kfz0, w.inst('elfzle2')], 'syl', '%s <_ C' % K)
    kfz = st([st([knn, cnn, klec], '3jca', '( %s e. NN /\\ C e. NN /\\ %s <_ C )' % (K, K)),
              st([w.s([], 'elfz1b',
                      '( %s e. ( 1 ... C ) <-> ( %s e. NN /\\ C e. NN /\\ %s <_ C ) )'
                      % (K, K, K))], 'a1i',
                 '( %s e. ( 1 ... C ) <-> ( %s e. NN /\\ C e. NN /\\ %s <_ C ) )' % (K, K, K))],
             'mpbird', '%s e. ( 1 ... C )' % K)
    # the Q-part has prime divisors exactly Q
    bel = smel(w, B, 'Q', 'C')
    bmm = st([st([bel], 'a1i',
                 '( %s e. %s <-> ( %s e. ( 1 ... C ) /\\ { r e. Prime | r || %s } C_ Q ) )'
                 % (B, SMS('Q', 'C'), B, B)), bsm], 'mpbid',
             '( %s e. ( 1 ... C ) /\\ { r e. Prime | r || %s } C_ Q )' % (B, B))
    bfz = st([bmm], 'simpld', '%s e. ( 1 ... C )' % B)
    bss = st([bmm], 'simprd', '{ r e. Prime | r || %s } C_ Q' % B)
    znn = st([zp, w.inst('prmnn')], 'syl', 'Z e. NN')
    zz = st([znn], 'nnzd', 'Z e. ZZ')
    bnn = st([bfz, w.inst('elfznn')], 'syl', '%s e. NN' % B)
    bz = st([bnn], 'nnzd', '%s e. ZZ' % B)
    AM = '( %s /\\ m e. Q )' % AR
    sm = mkst(w, AM)
    mq = sm([], 'simpr', 'm e. Q')
    mqz = sm([sm([w.s([], 'ssun1', 'Q C_ %s' % QZ)], 'a1i', 'Q C_ %s' % QZ), mq], 'sseldd',
             'm e. %s' % QZ)
    mpf = sm([mqz, sm([lift(w, pfeq, AM)], 'eqcomd',
                      '%s = { r e. Prime | r || N }' % QZ)], 'eleqtrd',
             'm e. { r e. Prime | r || N }')
    pem = pfel(w, 'm', 'N')
    mmem = sm([sm([pem], 'a1i',
                  '( m e. { r e. Prime | r || N } <-> ( m e. Prime /\\ m || N ) )'), mpf],
              'mpbid', '( m e. Prime /\\ m || N )')
    mprm = sm([mmem], 'simpld', 'm e. Prime')
    mdvd = sm([mmem], 'simprd', 'm || N')
    AMZ = '( %s /\\ m = Z )' % AM
    smz = mkst(w, AMZ)
    zq = smz([smz([smz([], 'simpr', 'm = Z')], 'eleq1d', '( m e. Q <-> Z e. Q )'),
              lift(w, mq, AMZ)], 'mpbid', 'Z e. Q')
    nmz = sm([lift(w, nzq, AM), zq], 'mtand', '-. m = Z')
    zknn = sm([lift(w, znn, AM), sm([lift(w, knn, AM)], 'nnnn0d', '%s e. NN0' % K)],
              'nnexpcld', '%s e. NN' % ZK)
    mdp = sm([sm([mdvd, sm([lift(w, prod, AM)], 'eqcomd', 'N = ( %s x. %s )' % (ZK, B))],
                 'breqtrd', 'm || ( %s x. %s )' % (ZK, B))], 'id', 'x')
    w.lines.pop()
    mdp = w.lines[-1].split(':')[0]
    eucl = sm([mprm, sm([zknn], 'nnzd', '%s e. ZZ' % ZK), lift(w, bz, AM),
               w.inst('euclemma')], 'syl3anc',
              '( m || ( %s x. %s ) <-> ( m || %s \\/ m || %s ) )' % (ZK, B, ZK, B))
    ordv = sm([eucl, mdp], 'mpbid', '( m || %s \\/ m || %s )' % (ZK, B))
    pexp = sm([mprm, lift(w, zz, AM), lift(w, knn, AM), w.inst('prmdvdsexp')], 'syl3anc',
              '( m || %s <-> m || Z )' % ZK)
    muz2 = sm([mprm, w.inst('prmuz2')], 'syl', 'm e. ( ZZ>= ` 2 )')
    mzeq = sm([muz2, lift(w, zp, AM), w.inst('dvdsprm')], 'syl2anc', '( m || Z <-> m = Z )')
    nmzk = sm([sm([pexp, mzeq], 'bitrd', '( m || %s <-> m = Z )' % ZK), nmz], 'mtbird',
              '-. m || %s' % ZK)
    mdb = sm([sm([ordv], 'ord', '( -. m || %s -> m || %s )' % (ZK, B)), nmzk], 'mpd',
             'm || %s' % B)
    peb = pfel(w, 'm', B)
    minb = sm([sm([mprm, mdb], 'jca', '( m e. Prime /\\ m || %s )' % B),
               sm([peb], 'a1i',
                  '( m e. { r e. Prime | r || %s } <-> ( m e. Prime /\\ m || %s ) )' % (B, B))],
              'mpbird', 'm e. { r e. Prime | r || %s }' % B)
    qsub = st([st([minb], 'ex', '( m e. Q -> m e. { r e. Prime | r || %s } )' % B)], 'ssrdv',
              'Q C_ { r e. Prime | r || %s }' % B)
    bpf = st([bss, qsub], 'eqssd', '{ r e. Prime | r || %s } = Q' % B)
    belr = rsel(w, B, 'Q', 'C')
    brs = st([st([bfz, bpf], 'jca',
                 '( %s e. ( 1 ... C ) /\\ { r e. Prime | r || %s } = Q )' % (B, B)),
              st([belr], 'a1i',
                 '( %s e. %s <-> ( %s e. ( 1 ... C ) /\\ { r e. Prime | r || %s } = Q ) )'
                 % (B, ST, B, B))], 'mpbird', '%s e. %s' % (B, ST))
    w.qed([kfz, brs, prod], '3jca',
          '( %s -> ( %s e. ( 1 ... C ) /\\ %s e. %s /\\ ( %s x. %s ) = N ) )'
          % (AR, K, B, ST, ZK, B))
    return w


ALL = {'rssplit': rssplit}



# ---------------------------------------------------------------- the injection
AF = '( ( Z e. Prime /\\ C e. NN ) /\\ -. Z e. Q )'


def PAIR(t):
    return '<. ( Z pCnt %s ) , ( %s / ( Z ^ ( Z pCnt %s ) ) ) >.' % (t, t, t)


FMAP = '( t e. %s |-> %s )' % (SMS(QZ, 'C'), PAIR('t'))
GMAP = '( t e. %s |-> %s )' % (SU, PAIR('t'))
XSM = '( ( 0 ... C ) X. %s )' % SMS('Q', 'C')
XRS = '( ( 1 ... C ) X. %s )' % ST


def rsf1():
    w = WS('rsf1', 'The map taking an integer with prime divisors exactly Q and Z to its '
                   'Z-exponent and its Q-part is injective.')
    st = mkst(w, AF)
    zp = st([], 'simpll', 'Z e. Prime')
    cnn = st([], 'simplr', 'C e. NN')
    AV = '( %s /\\ v e. ( 1 ... C ) )' % AF
    sv = mkst(w, AV)
    imp = sv([], 'a1i',
             '( { r e. Prime | r || v } = %s -> { r e. Prime | r || v } C_ %s )' % (QZ, QZ))
    w.lines.pop()
    eqi = w.s([], 'eqimss',
              '( { r e. Prime | r || v } = %s -> { r e. Prime | r || v } C_ %s )' % (QZ, QZ))
    imp = sv([eqi], 'a1i',
             '( { r e. Prime | r || v } = %s -> { r e. Prime | r || v } C_ %s )' % (QZ, QZ))
    sub = st([imp], 'ss2rabdv', '%s C_ %s' % (SU, SMS(QZ, 'C')))
    sm1 = st([st([zp, cnn], 'jca', '( Z e. Prime /\\ C e. NN )'), w.inst('smsumf1')], 'syl',
             '%s : %s -1-1-> %s' % (FMAP, SMS(QZ, 'C'), XSM))
    rm = st([sub, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (FMAP, SU, GMAP))
    AT = '( %s /\\ t e. %s )' % (AF, SU)
    stt = mkst(w, AT)
    spl = stt([stt([], 'id', AT), w.inst('rssplit')], 'syl',
              '( ( Z pCnt t ) e. ( 1 ... C ) /\\ ( t / ( Z ^ ( Z pCnt t ) ) ) e. %s /\\ '
              '( ( Z ^ ( Z pCnt t ) ) x. ( t / ( Z ^ ( Z pCnt t ) ) ) ) = t )' % ST)
    k1 = stt([spl], 'simp1d', '( Z pCnt t ) e. ( 1 ... C )')
    b1 = stt([spl], 'simp2d', '( t / ( Z ^ ( Z pCnt t ) ) ) e. %s' % ST)
    pxp = stt([k1, b1, w.inst('opelxpi')], 'syl2anc', '%s e. %s' % (PAIR('t'), XRS))
    gf = st([pxp, w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fmptd',
            '%s : %s --> %s' % (GMAP, SU, XRS))
    rf = st([gf, st([rm], 'feq1d',
                    '( ( %s |` %s ) : %s --> %s <-> %s : %s --> %s )'
                    % (FMAP, SU, SU, XRS, GMAP, SU, XRS))], 'mpbird',
            '( %s |` %s ) : %s --> %s' % (FMAP, SU, SU, XRS))
    f1r = st([sm1, sub, rf, w.inst('f1resf1')], 'syl3anc',
             '( %s |` %s ) : %s -1-1-> %s' % (FMAP, SU, SU, XRS))
    w.qed([f1r, st([rm, w.inst('f1eq1')], 'syl',
                   '( ( %s |` %s ) : %s -1-1-> %s <-> %s : %s -1-1-> %s )'
                   % (FMAP, SU, SU, XRS, GMAP, SU, XRS))], 'mpbid',
          '( %s -> %s : %s -1-1-> %s )' % (AF, GMAP, SU, XRS))
    return w


ALL['rsf1'] = rsf1

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
