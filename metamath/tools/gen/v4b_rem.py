"""Sortie v4b block 4b: the multiplicity sum and the remainder bound."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import A, P, PH, V, WF, X, T, CT, MS, mkst
from cl import lift

ANTM = '( %s /\\ D e. NN )' % PH
ANTR = '( %s /\\ ( D e. NN /\\ D || %s ) )' % (PH, P)
IFW = 'if ( D || n , ( %s ` n ) , 0 )' % WF
IF1 = 'if ( D || n , 1 , 0 )'
DM = '( D x. M )'
CTD = CT('D')
EX = lambda v: 'E. %s e. Prime ( %s || D /\\ %s || M )' % (v, v, v)


MOD = '( n mod M ) = ( 1 mod M )'
RABI = '( n e. %s <-> ( n e. ( 1 ... N ) /\\ ( %s /\\ D || n ) ) )' % (CT('D'), MOD)
RABA = '( n e. %s <-> ( n e. ( 1 ... N ) /\\ %s ) )' % (A, MOD)


def _elrabs(w):
    sb1 = w.s([w.s([w.s([], 'oveq1', '( i = n -> ( i mod M ) = ( n mod M ) )')], 'eqeq1d',
                   '( i = n -> ( ( i mod M ) = ( 1 mod M ) <-> %s ) )' % MOD),
               w.s([], 'breq2', '( i = n -> ( D || i <-> D || n ) )')], 'anbi12d',
              '( i = n -> ( ( ( i mod M ) = ( 1 mod M ) /\\ D || i ) <-> ( %s /\\ D || n ) ) )' % MOD)
    ri = w.s([sb1], 'elrab', RABI)
    sb2 = w.s([w.s([], 'oveq1', '( i = n -> ( i mod M ) = ( n mod M ) )')], 'eqeq1d',
              '( i = n -> ( ( i mod M ) = ( 1 mod M ) <-> %s ) )' % MOD)
    ra = w.s([sb2], 'elrab', RABA)
    return ri, ra


def progmsum():
    w = W('progmsum', 'The multiplicity sum of the progression sieve counts the integers '
                      'up to N in the class that are divisible by D.')
    AP = CT('D')
    st = mkst(w, ANTM)
    fzf = st([], 'fzfid', '( 1 ... N ) e. Fin')
    ass = st([w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % A)], 'a1i', '%s C_ ( 1 ... N )' % A)
    afin = st([fzf, ass], 'ssfid', '%s e. Fin' % A)
    sub = w.s([w.s([w.s([], 'simpl',
                         '( ( ( i mod M ) = ( 1 mod M ) /\\ D || i ) -> ( i mod M ) = ( 1 mod M ) )')],
                   'a1i',
                   '( i e. ( 1 ... N ) -> ( ( ( i mod M ) = ( 1 mod M ) /\\ D || i ) -> ( i mod M ) = ( 1 mod M ) ) )')],
              'ss2rabi', '%s C_ %s' % (AP, A))
    apss = st([sub], 'a1i', '%s C_ %s' % (AP, A))
    apfin = st([afin, apss], 'ssfid', '%s e. Fin' % AP)
    ri, ra = _elrabs(w)
    # ( W ` n ) = 1 on the support
    AN = '( %s /\\ n e. %s )' % (ANTM, A)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % A)
    nfz = sn([nel, w.inst('elrabi')], 'syl', 'n e. ( 1 ... N )')
    fss = sn([w.s([], 'fz1ssnn', '( 1 ... N ) C_ NN')], 'a1i', '( 1 ... N ) C_ NN')
    nnn = sn([fss, nfz], 'sseldd', 'n e. NN')
    wv0 = w.s([w.s([], 'eqidd', '( c = n -> 1 = 1 )'),
               w.s([], 'eqid', '%s = %s' % (WF, WF))], 'fvmptg',
              '( ( n e. NN /\\ 1 e. _V ) -> ( %s ` n ) = 1 )' % WF)
    wv = sn([nnn, sn([w.s([], '1ex', '1 e. _V')], 'a1i', '1 e. _V'), wv0], 'syl2anc',
            '( %s ` n ) = 1' % WF)
    s1 = st([sn([wv], 'ifeq1d', '%s = %s' % (IFW, IF1))], 'sumeq2dv',
            'sum_ n e. %s %s = sum_ n e. %s %s' % (A, IFW, A, IF1))
    # the summand on the filtered set
    AQ = '( %s /\\ n e. %s )' % (ANTM, AP)
    sq = mkst(w, AQ)
    qd2 = sq([sq([sq([], 'simpr', 'n e. %s' % AP), sq([ri], 'a1i', RABI)], 'mpbid',
                 '( n e. ( 1 ... N ) /\\ ( %s /\\ D || n ) )' % MOD)], 'simprrd', 'D || n')
    qcl = sq([sq([], '1cnd', '1 e. CC'), sq([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF1)
    # the summand vanishes off it
    AR = '( %s /\\ n e. ( %s \\ %s ) )' % (ANTM, A, AP)
    sr = mkst(w, AR)
    rel = sr([], 'simpr', 'n e. ( %s \\ %s )' % (A, AP))
    rin = sr([rel, w.inst('eldifi')], 'syl', 'n e. %s' % A)
    rnin = sr([rel, w.inst('eldifn')], 'syl', '-. n e. %s' % AP)
    rpair = sr([rin, sr([ra], 'a1i', RABA)], 'mpbid',
               '( n e. ( 1 ... N ) /\\ %s )' % MOD)
    rfz = sr([rpair], 'simpld', 'n e. ( 1 ... N )')
    rmod = sr([rpair], 'simprd', MOD)
    AS = '( %s /\\ D || n )' % AR
    ss2 = mkst(w, AS)
    sdv = ss2([], 'simpr', 'D || n')
    sin = ss2([lift(w, rfz, AS), ss2([lift(w, rmod, AS), sdv], 'jca',
                                     '( %s /\\ D || n )' % MOD)], 'jca',
              '( n e. ( 1 ... N ) /\\ ( %s /\\ D || n ) )' % MOD)
    sctd = ss2([ss2([ri], 'a1i', RABI), sin], 'mpbird', 'n e. %s' % AP)
    imp = sr([sctd], 'ex', '( D || n -> n e. %s )' % AP)
    ndvd = sr([rnin, imp], 'mtod', '-. D || n')
    rz = sr([ndvd], 'iffalsed', '%s = 0' % IF1)
    ss = st([apss, qcl, rz, afin], 'fsumss',
            'sum_ n e. %s %s = sum_ n e. %s %s' % (AP, IF1, A, IF1))
    tr = st([sq([qd2], 'iftrued', '%s = 1' % IF1)], 'sumeq2dv',
            'sum_ n e. %s %s = sum_ n e. %s 1' % (AP, IF1, AP))
    cst = st([apfin, st([], '1cnd', '1 e. CC'), w.inst('fsumconst')], 'syl2anc',
             'sum_ n e. %s 1 = ( ( # ` %s ) x. 1 )' % (AP, AP))
    hcl = st([st([apfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % AP)], 'nn0cnd',
             '( # ` %s ) e. CC' % AP)
    mr = st([hcl], 'mulridd', '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (AP, AP))
    chain = st([st([tr, cst], 'eqtrd',
                   'sum_ n e. %s %s = ( ( # ` %s ) x. 1 )' % (AP, IF1, AP)), mr], 'eqtrd',
               'sum_ n e. %s %s = ( # ` %s )' % (AP, IF1, AP))
    w.qed([s1, st([ss, chain], 'eqtr3d',
                   'sum_ n e. %s %s = ( # ` %s )' % (A, IF1, AP))], 'eqtrd',
          '( %s -> %s = ( # ` %s ) )' % (ANTM, MS('D'), AP))
    return w


def progcop():
    w = W('progcop', 'A divisor of the sifting product is coprime to the modulus.')
    st = mkst(w, ANTR)
    dnn = st([], 'simprl', 'D e. NN')
    ddv = st([], 'simprr', 'D || %s' % P)
    muz = st([], 'simpl1', 'M e. ( ZZ>= ` 2 )')
    mnn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    ph0 = st([], 'simpl', PH)
    pn = w.s([ph0, w.inst('progpnn')], 'syl',
             '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s ) )'
             % (ANTR, P, P, P, T))
    pnn = st([st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))], 'simpld',
             '%s e. NN' % P)
    AQ = '( %s /\\ q e. Prime )' % ANTR
    sq = mkst(w, AQ)
    LQ = lambda s: lift(w, s, AQ)
    qpr = sq([], 'simpr', 'q e. Prime')
    AD = '( %s /\\ q || D )' % AQ
    sd = mkst(w, AD)
    LD = lambda s: lift(w, s, AD)
    qd = sd([], 'simpr', 'q || D')
    qz = sd([sd([LD(qpr), w.inst('prmnn')], 'syl', 'q e. NN')], 'nnzd', 'q e. ZZ')
    dz = sd([LD(dnn)], 'nnzd', 'D e. ZZ')
    pz = sd([LD(pnn)], 'nnzd', '%s e. ZZ' % P)
    tr = sd([sd([qz, dz, pz], '3jca', '( q e. ZZ /\\ D e. ZZ /\\ %s e. ZZ )' % P),
             w.inst('dvdstr')], 'syl',
            '( ( q || D /\\ D || %s ) -> q || %s )' % (P, P))
    qP = sd([tr, qd, LD(ddv)], 'mp2and', 'q || %s' % P)
    pel = sd([LD(ph0), LD(qpr), w.inst('progpel')],
             'syl2anc', '( q || %s <-> ( q <_ Z /\\ -. q || M ) )' % P)
    nm = sd([sd([pel, qP], 'mpbid', '( q <_ Z /\\ -. q || M )')], 'simprd', '-. q || M')
    exq = sq([nm], 'ex', '( q || D -> -. q || M )')
    nan = sq([sq([w.s([], 'imnan',
                       '( ( q || D -> -. q || M ) <-> -. ( q || D /\\ q || M ) )')], 'a1i',
                 '( ( q || D -> -. q || M ) <-> -. ( q || D /\\ q || M ) )'), exq], 'mpbid',
             '-. ( q || D /\\ q || M )')
    ral = st([nan], 'ralrimiva', 'A. q e. Prime -. ( q || D /\\ q || M )')
    nex = st([st([w.s([], 'ralnex',
                       '( A. q e. Prime -. ( q || D /\\ q || M ) <-> -. %s )' % EX('q'))], 'a1i',
                  '( A. q e. Prime -. ( q || D /\\ q || M ) <-> -. %s )' % EX('q')), ral],
             'mpbid', '-. %s' % EX('q'))
    cbv = w.s([w.s([w.s([], 'breq1', '( q = p -> ( q || D <-> p || D ) )'),
                    w.s([], 'breq1', '( q = p -> ( q || M <-> p || M ) )')], 'anbi12d',
                   '( q = p -> ( ( q || D /\\ q || M ) <-> ( p || D /\\ p || M ) ) )')],
              'cbvrexvw', '( %s <-> %s )' % (EX('q'), EX('p')))
    nexp = st([nex, st([cbv], 'a1i', '( %s <-> %s )' % (EX('q'), EX('p')))], 'mtbid',
              '-. %s' % EX('p'))
    AB = '( D e. NN /\\ M e. NN )'
    ncb = w.s([w.s([], 'simpl', '( %s -> D e. NN )' % AB),
               w.s([], 'simpr', '( %s -> M e. NN )' % AB)], 'prmdvdsncoprmbd',
              '( %s -> ( %s <-> ( D gcd M ) =/= 1 ) )' % (AB, EX('p')))
    bic = st([dnn, mnn, ncb], 'syl2anc', '( %s <-> ( D gcd M ) =/= 1 )' % EX('p'))
    nne0 = st([nexp, bic], 'mtbid', '-. ( D gcd M ) =/= 1')
    w.qed([st([w.s([], 'nne', '( -. ( D gcd M ) =/= 1 <-> ( D gcd M ) = 1 )')], 'a1i',
               '( -. ( D gcd M ) =/= 1 <-> ( D gcd M ) = 1 )'), nne0], 'mpbid',
          '( %s -> ( D gcd M ) = 1 )' % ANTR)
    return w


def progrem():
    w = W('progrem', 'The remainder of the progression sieve is at most 1 in absolute '
                     'value at every divisor of the sifting product.')
    st = mkst(w, ANTR)
    dnn = st([], 'simprl', 'D e. NN')
    ddv = st([], 'simprr', 'D || %s' % P)
    ph0 = st([], 'simpl', PH)
    muz = st([], 'simpl1', 'M e. ( ZZ>= ` 2 )')
    mnn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    nn0 = st([], 'simpl3', 'N e. NN0')
    gcd = st([], 'progcop', '( D gcd M ) = 1')
    pn = w.s([ph0, w.inst('progpnn')], 'syl',
             '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s ) )'
             % (ANTR, P, P, P, T))
    pp = st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))
    pnn = st([pp], 'simpld', '%s e. NN' % P)
    psq = st([pp], 'simprd', '( mmu ` %s ) =/= 0' % P)
    dsq = st([st([pnn, dnn, ddv, w.inst('dvdssqf')], 'syl3anc',
                 '( ( mmu ` %s ) =/= 0 -> ( mmu ` D ) =/= 0 )' % P), psq], 'mpd',
             '( mmu ` D ) =/= 0')
    vd = st([dnn, dsq, w.inst('progvsqf')], 'syl2anc', '( %s ` D ) = ( 1 / D )' % V)
    ms = st([st([ph0, dnn], 'jca', ANTM), w.inst('progmsum')], 'syl',
            '%s = ( # ` %s )' % (MS('D'), CTD))
    cnt = st([st([st([dnn, mnn, gcd], '3jca',
                     '( D e. NN /\\ M e. NN /\\ ( D gcd M ) = 1 )'), nn0], 'jca',
                 '( ( D e. NN /\\ M e. NN /\\ ( D gcd M ) = 1 ) /\\ N e. NN0 )'),
              w.inst('crtcnt')], 'syl',
             '( abs ` ( ( # ` %s ) - ( N / %s ) ) ) <_ 1' % (CTD, DM))
    onec = st([], '1cnd', '1 e. CC')
    ncc = st([nn0], 'nn0cnd', 'N e. CC')
    dcc = st([dnn], 'nncnd', 'D e. CC')
    dne = st([dnn], 'nnne0d', 'D =/= 0')
    mcc = st([mnn], 'nncnd', 'M e. CC')
    mne = st([mnn], 'nnne0d', 'M =/= 0')
    dmd = st([st([onec, ncc], 'jca', '( 1 e. CC /\\ N e. CC )'),
              st([st([dcc, dne], 'jca', '( D e. CC /\\ D =/= 0 )'),
                  st([mcc, mne], 'jca', '( M e. CC /\\ M =/= 0 )')], 'jca',
                 '( ( D e. CC /\\ D =/= 0 ) /\\ ( M e. CC /\\ M =/= 0 ) )')], 'jca',
             '( ( 1 e. CC /\\ N e. CC ) /\\ ( ( D e. CC /\\ D =/= 0 ) /\\ ( M e. CC /\\ M =/= 0 ) ) )')
    dmul = st([dmd, w.inst('divmuldiv')], 'syl',
              '( ( 1 / D ) x. %s ) = ( ( 1 x. N ) / %s )' % (X, DM))
    m1 = st([st([ncc], 'mullidd', '( 1 x. N ) = N')], 'oveq1d',
            '( ( 1 x. N ) / %s ) = ( N / %s )' % (DM, DM))
    ar = st([st([vd], 'oveq1d', '( ( %s ` D ) x. %s ) = ( ( 1 / D ) x. %s )' % (V, X, X)),
             st([dmul, m1], 'eqtrd', '( ( 1 / D ) x. %s ) = ( N / %s )' % (X, DM))], 'eqtrd',
            '( ( %s ` D ) x. %s ) = ( N / %s )' % (V, X, DM))
    e1 = st([ms, ar], 'oveq12d',
            '( %s - ( ( %s ` D ) x. %s ) ) = ( ( # ` %s ) - ( N / %s ) )' % (MS('D'), V, X, CTD, DM))
    e2 = st([e1], 'fveq2d',
            '( abs ` ( %s - ( ( %s ` D ) x. %s ) ) ) = ( abs ` ( ( # ` %s ) - ( N / %s ) ) )'
            % (MS('D'), V, X, CTD, DM))
    w.qed([e2, cnt], 'eqbrtrd',
          '( %s -> ( abs ` ( %s - ( ( %s ` D ) x. %s ) ) ) <_ 1 )' % (ANTR, MS('D'), V, X))
    return w


def main(names=None):
    fns = {'progmsum': progmsum, 'progcop': progcop, 'progrem': progrem}
    order = ['progmsum', 'progcop', 'progrem']
    ok = True
    for nm in (names or order):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
