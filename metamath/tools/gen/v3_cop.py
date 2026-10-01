"""Sortie v3: the coprime/smooth factorisation and the coprime harmonic sum.

cosplit  ( ( ( K e. NN /\\ W e. NN ) /\\ N e. ( 1 ... W ) ) ->
             ( ( N gcd ( K ^ N ) ) e. SM( PF( K ) , W ) /\\
               ( N / ( N gcd ( K ^ N ) ) ) e. CS( K , W ) /\\
               ( ( N gcd ( K ^ N ) ) x. ( N / ( N gcd ( K ^ N ) ) ) ) = N ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst, SMS, smel
from cl import lift
from lin import linarith, nlinarith

PFK = '{ q e. Prime | q || K }'
SMK = SMS(PFK, 'W')
CSK = '{ x e. ( 1 ... W ) | ( x gcd K ) = 1 }'
KN = '( K ^ N )'
GC = '( N gcd ( K ^ N ) )'
BB = '( N / %s )' % GC
A = '( ( K e. NN /\\ W e. NN ) /\\ N e. ( 1 ... W ) )'


def cosplit():
    w = WS('cosplit', 'A positive integer factors as its part supported on the prime divisors '
                      'of K times a part coprime to K.')
    st = mkst(w, A)
    knn = st([], 'simpll', 'K e. NN')
    wnn = st([], 'simplr', 'W e. NN')
    nfz = st([], 'simpr', 'N e. ( 1 ... W )')
    nnn = st([nfz, w.inst('elfznn')], 'syl', 'N e. NN')
    nlew = st([nfz, w.inst('elfzle2')], 'syl', 'N <_ W')
    nz = st([nnn], 'nnzd', 'N e. ZZ')
    nn0 = st([nnn], 'nnnn0d', 'N e. NN0')
    knnn = st([knn, nn0], 'nnexpcld', '%s e. NN' % KN)
    knz = st([knnn], 'nnzd', '%s e. ZZ' % KN)
    gnn = st([nnn, knnn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % GC)
    gz = st([gnn], 'nnzd', '%s e. ZZ' % GC)
    gd = st([nz, knz, w.inst('gcddvds')], 'syl2anc', '( %s || N /\\ %s || %s )' % (GC, GC, KN))
    gdn = st([gd], 'simpld', '%s || N' % GC)
    gdk = st([gd], 'simprd', '%s || %s' % (GC, KN))
    bnn = st([st([nnn, gnn, w.inst('nndivdvds')], 'syl2anc', '( %s || N <-> %s e. NN )' % (GC, BB)),
              gdn], 'mpbid', '%s e. NN' % BB)
    nc = st([nnn], 'nncnd', 'N e. CC')
    gcc = st([gnn], 'nncnd', '%s e. CC' % GC)
    gne = st([gnn], 'nnne0d', '%s =/= 0' % GC)
    prod = st([nc, gcc, gne, w.inst('divcan2')], 'syl3anc', '( %s x. %s ) = N' % (GC, BB))
    # GC and B are at most N, hence in ( 1 ... W )
    gle = st([st([gz, nnn, w.inst('dvdsle')], 'syl2anc', '( %s || N -> %s <_ N )' % (GC, GC)),
              gdn], 'mpd', '%s <_ N' % GC)
    bz = st([bnn], 'nnzd', '%s e. ZZ' % BB)
    bdv0 = st([gz, bz, w.inst('dvdsmul2')], 'syl2anc', '%s || ( %s x. %s )' % (BB, GC, BB))
    bdv = st([bdv0, prod], 'breqtrd', '%s || N' % BB)
    ble = st([st([bz, nnn, w.inst('dvdsle')], 'syl2anc', '( %s || N -> %s <_ N )' % (BB, BB)),
              bdv], 'mpd', '%s <_ N' % BB)
    nre = st([nnn], 'nnred', 'N e. RR')
    wre = st([wnn], 'nnred', 'W e. RR')
    gre = st([gnn], 'nnred', '%s e. RR' % GC)
    bre = st([bnn], 'nnred', '%s e. RR' % BB)
    glew = st([gre, nre, wre, gle, nlew], 'letrd', '%s <_ W' % GC)
    blew = st([bre, nre, wre, ble, nlew], 'letrd', '%s <_ W' % BB)

    def infz(x, xnn, xlew):
        return st([st([xnn, wnn, xlew], '3jca', '( %s e. NN /\\ W e. NN /\\ %s <_ W )' % (x, x)),
                   st([w.s([], 'elfz1b',
                           '( %s e. ( 1 ... W ) <-> ( %s e. NN /\\ W e. NN /\\ %s <_ W ) )'
                           % (x, x, x))], 'a1i',
                      '( %s e. ( 1 ... W ) <-> ( %s e. NN /\\ W e. NN /\\ %s <_ W ) )'
                      % (x, x, x))], 'mpbird', '%s e. ( 1 ... W )' % x)

    gfz = infz(GC, gnn, glew)
    bfz = infz(BB, bnn, blew)
    # PF( GC ) C_ PF( K )
    AP = '( %s /\\ p e. { r e. Prime | r || %s } )' % (A, GC)
    sp = mkst(w, AP)
    elg = w.s([w.s([], 'breq1', '( r = p -> ( r || %s <-> p || %s ) )' % (GC, GC))], 'elrab',
              '( p e. { r e. Prime | r || %s } <-> ( p e. Prime /\\ p || %s ) )' % (GC, GC))
    pmem = sp([sp([elg], 'a1i',
                  '( p e. { r e. Prime | r || %s } <-> ( p e. Prime /\\ p || %s ) )' % (GC, GC)),
               sp([], 'simpr', 'p e. { r e. Prime | r || %s }' % GC)], 'mpbid',
              '( p e. Prime /\\ p || %s )' % GC)
    pprm = sp([pmem], 'simpld', 'p e. Prime')
    pdg = sp([pmem], 'simprd', 'p || %s' % GC)
    pz = sp([sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')], 'nnzd', 'p e. ZZ')
    pdkn = sp([sp([sp([pz, lift(w, gz, AP), lift(w, knz, AP)], '3jca',
                      '( p e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ )' % (GC, KN)), w.inst('dvdstr')], 'syl',
                   '( ( p || %s /\\ %s || %s ) -> p || %s )' % (GC, GC, KN, KN)),
               sp([pdg, lift(w, gdk, AP)], 'jca', '( p || %s /\\ %s || %s )' % (GC, GC, KN))],
              'mpd', 'p || %s' % KN)
    pdk = sp([sp([pprm, lift(w, st([knn], 'nnzd', 'K e. ZZ'), AP), lift(w, nnn, AP),
                  w.inst('prmdvdsexp')], 'syl3anc', '( p || %s <-> p || K )' % KN), pdkn],
             'mpbid', 'p || K')
    elk = w.s([w.s([], 'breq1', '( q = p -> ( q || K <-> p || K ) )')], 'elrab',
              '( p e. %s <-> ( p e. Prime /\\ p || K ) )' % PFK)
    pink = sp([sp([elk], 'a1i', '( p e. %s <-> ( p e. Prime /\\ p || K ) )' % PFK),
               sp([pprm, pdk], 'jca', '( p e. Prime /\\ p || K )')], 'mpbird', 'p e. %s' % PFK)
    pfss = st([st([pink], 'ex',
                  '( p e. { r e. Prime | r || %s } -> p e. %s )' % (GC, PFK))], 'ssrdv',
              '{ r e. Prime | r || %s } C_ %s' % (GC, PFK))
    elsm = smel(w, A, st, GC, PFK, 'W')
    gsm = st([st([gfz, pfss], 'jca',
                 '( %s e. ( 1 ... W ) /\\ { r e. Prime | r || %s } C_ %s )' % (GC, GC, PFK)),
              st([elsm], 'a1i',
                 '( %s e. %s <-> ( %s e. ( 1 ... W ) /\\ { r e. Prime | r || %s } C_ %s ) )'
                 % (GC, SMK, GC, GC, PFK))], 'mpbird', '%s e. %s' % (GC, SMK))
    # ( B gcd K ) = 1: no prime divides both B and K
    APR = '( %s /\\ p e. Prime )' % A
    AC = '( %s /\\ ( p || %s /\\ p || K ) )' % (APR, BB)
    sc = mkst(w, AC)
    cprm = sc([], 'simplr', 'p e. Prime')
    cpb = sc([], 'simprl', 'p || %s' % BB)
    cpk = sc([], 'simprr', 'p || K')
    # ( p pCnt N ) <_ N
    pcn0 = sc([cprm, lift(w, nnn, AC), w.inst('pccl')], 'syl2anc', '( p pCnt N ) e. NN0')
    ppw = sc([cprm, lift(w, nnn, AC), w.inst('pcdvds')], 'syl2anc',
             '( p ^ ( p pCnt N ) ) || N')
    ppwnn = sc([sc([cprm, w.inst('prmnn')], 'syl', 'p e. NN'), pcn0], 'nnexpcld',
               '( p ^ ( p pCnt N ) ) e. NN')
    ppwle = sc([sc([sc([ppwnn], 'nnzd', '( p ^ ( p pCnt N ) ) e. ZZ'), lift(w, nnn, AC),
                    w.inst('dvdsle')], 'syl2anc',
                   '( ( p ^ ( p pCnt N ) ) || N -> ( p ^ ( p pCnt N ) ) <_ N )'), ppw],
               'mpd', '( p ^ ( p pCnt N ) ) <_ N')
    bern = sc([sc([cprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'), pcn0,
               w.inst('bernneq3')], 'syl2anc', '( p pCnt N ) < ( p ^ ( p pCnt N ) )')
    pcnre = sc([pcn0], 'nn0red', '( p pCnt N ) e. RR')
    ppwre = sc([ppwnn], 'nnred', '( p ^ ( p pCnt N ) ) e. RR')
    pcnle = linarith(w, AC, [bern, ppwle], '( p pCnt N ) <_ N',
                     leaves={'( p pCnt N )': pcnre, '( p ^ ( p pCnt N ) )': ppwre,
                             'N': lift(w, nre, AC)})
    # ( p pCnt ( K ^ N ) ) = ( N x. ( p pCnt K ) ) and 1 <_ ( p pCnt K )
    kqq = sc([lift(w, knn, AC), w.inst('nnq')], 'syl', 'K e. QQ')
    kne = sc([lift(w, knn, AC)], 'nnne0d', 'K =/= 0')
    pcke = sc([cprm, sc([kqq, kne], 'jca', '( K e. QQ /\\ K =/= 0 )'), lift(w, nz, AC),
               w.inst('pcexp')], 'syl3anc',
              '( p pCnt %s ) = ( N x. ( p pCnt K ) )' % KN)
    pcknn = sc([sc([cprm, lift(w, knn, AC), w.inst('pcelnn')], 'syl2anc',
                   '( ( p pCnt K ) e. NN <-> p || K )'), cpk], 'mpbird',
               '( p pCnt K ) e. NN')
    pck1 = sc([pcknn, w.inst('nnge1')], 'syl', '1 <_ ( p pCnt K )')
    pckre = sc([pcknn], 'nnred', '( p pCnt K ) e. RR')
    nge1 = sc([lift(w, nnn, AC), w.inst('nnge1')], 'syl', '1 <_ N')
    prodge = nlinarith(w, AC, [pck1, nge1], 'N <_ ( N x. ( p pCnt K ) )',
                       leaves={'N': lift(w, nre, AC), '( p pCnt K )': pckre})
    pckn = sc([prodge, sc([pcke], 'eqcomd', '( N x. ( p pCnt K ) ) = ( p pCnt %s )' % KN)],
              'breqtrd', 'N <_ ( p pCnt %s )' % KN)
    pcknre = sc([lift(w, nre, AC), pckre], 'remulcld', '( N x. ( p pCnt K ) ) e. RR')
    pckre2 = sc([pcke, pcknre], 'eqeltrd', '( p pCnt %s ) e. RR' % KN)
    cmp = sc([pcnre, lift(w, nre, AC), pckre2, pcnle, pckn], 'letrd',
             '( p pCnt N ) <_ ( p pCnt %s )' % KN)
    # pcgcd1 and pcdiv give ( p pCnt B ) = 0
    pcg = sc([sc([sc([cprm, lift(w, nz, AC), lift(w, knz, AC)], '3jca',
                     '( p e. Prime /\\ N e. ZZ /\\ %s e. ZZ )' % KN), cmp], 'jca',
                 '( ( p e. Prime /\\ N e. ZZ /\\ %s e. ZZ ) /\\ ( p pCnt N ) <_ ( p pCnt %s ) )'
                 % (KN, KN)), w.inst('pcgcd1')], 'syl',
             '( p pCnt %s ) = ( p pCnt N )' % GC)
    pcd = sc([cprm, sc([lift(w, nz, AC), sc([lift(w, nnn, AC)], 'nnne0d', 'N =/= 0')], 'jca',
                       '( N e. ZZ /\\ N =/= 0 )'), lift(w, gnn, AC), w.inst('pcdiv')], 'syl3anc',
             '( p pCnt %s ) = ( ( p pCnt N ) - ( p pCnt %s ) )' % (BB, GC))
    pcb0 = sc([pcd, sc([sc([pcg], 'oveq2d',
                           '( ( p pCnt N ) - ( p pCnt %s ) ) = ( ( p pCnt N ) - ( p pCnt N ) )'
                           % GC),
                        sc([sc([pcnre], 'recnd', '( p pCnt N ) e. CC')], 'subidd',
                           '( ( p pCnt N ) - ( p pCnt N ) ) = 0')], 'eqtrd',
                       '( ( p pCnt N ) - ( p pCnt %s ) ) = 0' % GC)], 'eqtrd',
              '( p pCnt %s ) = 0' % BB)
    nbdv = sc([sc([cprm, lift(w, bnn, AC), w.inst('pceq0')], 'syl2anc',
                  '( ( p pCnt %s ) = 0 <-> -. p || %s )' % (BB, BB)), pcb0], 'mpbid',
              '-. p || %s' % BB)
    spr = mkst(w, APR)
    nboth = spr([cpb, nbdv], 'pm2.65da', '-. ( p || %s /\\ p || K )' % BB)
    ral = st([nboth], 'ralrimiva', 'A. p e. Prime -. ( p || %s /\\ p || K )' % BB)
    nex = st([st([w.s([], 'ralnex',
                      '( A. p e. Prime -. ( p || %s /\\ p || K ) <-> '
                      '-. E. p e. Prime ( p || %s /\\ p || K ) )' % (BB, BB))], 'a1i',
                 '( A. p e. Prime -. ( p || %s /\\ p || K ) <-> '
                 '-. E. p e. Prime ( p || %s /\\ p || K ) )' % (BB, BB)), ral], 'mpbid',
             '-. E. p e. Prime ( p || %s /\\ p || K )' % BB)
    nco = st([bnn, knn], 'prmdvdsncoprmbd',
             '( E. p e. Prime ( p || %s /\\ p || K ) <-> ( %s gcd K ) =/= 1 )' % (BB, BB))
    gcd1 = st([st([nco, nex], 'mtbid', '-. ( %s gcd K ) =/= 1' % BB), w.inst('nne')], 'sylib',
              '( %s gcd K ) = 1' % BB)
    # B is coprime and in range
    elcs = w.s([w.s([w.s([], 'oveq1', '( x = %s -> ( x gcd K ) = ( %s gcd K ) )' % (BB, BB))],
                    'eqeq1d', '( x = %s -> ( ( x gcd K ) = 1 <-> ( %s gcd K ) = 1 ) )' % (BB, BB))],
               'elrab',
               '( %s e. %s <-> ( %s e. ( 1 ... W ) /\\ ( %s gcd K ) = 1 ) )' % (BB, CSK, BB, BB))
    bcs = st([st([bfz, gcd1], 'jca',
                 '( %s e. ( 1 ... W ) /\\ ( %s gcd K ) = 1 )' % (BB, BB)),
              st([elcs], 'a1i',
                 '( %s e. %s <-> ( %s e. ( 1 ... W ) /\\ ( %s gcd K ) = 1 ) )'
                 % (BB, CSK, BB, BB))], 'mpbird', '%s e. %s' % (BB, CSK))
    w.qed([gsm, bcs, prod], '3jca',
          '( %s -> ( %s e. %s /\\ %s e. %s /\\ ( %s x. %s ) = N ) )'
          % (A, GC, SMK, BB, CSK, GC, BB))
    return w


AK = '( K e. NN /\\ W e. NN )'
FZW = '( 1 ... W )'


def PAIRC(t):
    return '<. ( %s gcd ( K ^ %s ) ) , ( %s / ( %s gcd ( K ^ %s ) ) ) >.' % (t, t, t, t, t)


FMAPC = '( t e. %s |-> %s )' % (FZW, PAIRC('t'))
XSC = '( %s X. %s )' % (SMK, CSK)


def cof1():
    w = WS('cof1', 'The map taking a positive integer to its K-smooth part and its part '
                   'coprime to K is injective into the product of the two ranges.')
    st = mkst(w, AK)
    knn = st([], 'simpl', 'K e. NN')
    wnn = st([], 'simpr', 'W e. NN')
    ts = w.s([], 'id', '( t = s -> t = s )')
    kts = w.s([ts], 'oveq2d', '( t = s -> ( K ^ t ) = ( K ^ s ) )')
    gts = w.s([ts, kts], 'oveq12d',
              '( t = s -> ( t gcd ( K ^ t ) ) = ( s gcd ( K ^ s ) ) )')
    bts = w.s([ts, gts], 'oveq12d',
              '( t = s -> ( t / ( t gcd ( K ^ t ) ) ) = ( s / ( s gcd ( K ^ s ) ) ) )')
    sb = w.s([gts, bts], 'opeq12d', '( t = s -> %s = %s )' % (PAIRC('t'), PAIRC('s')))
    eqi = w.s([], 'eqid', '%s = %s' % (FMAPC, FMAPC))
    bic = w.s([eqi, sb], 'f1mpt',
              '( %s : %s -1-1-> %s <-> ( A. t e. %s %s e. %s /\\ '
              'A. t e. %s A. s e. %s ( %s = %s -> t = s ) ) )'
              % (FMAPC, FZW, XSC, FZW, PAIRC('t'), XSC, FZW, FZW, PAIRC('t'), PAIRC('s')))
    AT = '( %s /\\ t e. %s )' % (AK, FZW)
    stt = mkst(w, AT)
    spl = stt([stt([], 'id', AT), w.inst('cosplit')], 'syl',
              '( ( t gcd ( K ^ t ) ) e. %s /\\ ( t / ( t gcd ( K ^ t ) ) ) e. %s /\\ '
              '( ( t gcd ( K ^ t ) ) x. ( t / ( t gcd ( K ^ t ) ) ) ) = t )' % (SMK, CSK))
    a1 = stt([spl], 'simp1d', '( t gcd ( K ^ t ) ) e. %s' % SMK)
    a2 = stt([spl], 'simp2d', '( t / ( t gcd ( K ^ t ) ) ) e. %s' % CSK)
    pxp = stt([a1, a2, w.inst('opelxpi')], 'syl2anc', '%s e. %s' % (PAIRC('t'), XSC))
    r1 = st([pxp], 'ralrimiva', 'A. t e. %s %s e. %s' % (FZW, PAIRC('t'), XSC))
    AST = '( ( %s /\\ t e. %s ) /\\ s e. %s )' % (AK, FZW, FZW)
    sts = mkst(w, AST)
    aks = sts([sts([], 'simpl', AT)], 'simpld', AK)
    sfz = sts([], 'simpr', 's e. %s' % FZW)
    spl2 = sts([sts([aks, sfz], 'jca', '( %s /\\ s e. %s )' % (AK, FZW)), w.inst('cosplit')],
               'syl',
               '( ( s gcd ( K ^ s ) ) e. %s /\\ ( s / ( s gcd ( K ^ s ) ) ) e. %s /\\ '
               '( ( s gcd ( K ^ s ) ) x. ( s / ( s gcd ( K ^ s ) ) ) ) = s )' % (SMK, CSK))
    prods = sts([spl2], 'simp3d',
                '( ( s gcd ( K ^ s ) ) x. ( s / ( s gcd ( K ^ s ) ) ) ) = s')
    prodt = sts([lift(w, spl, AST)], 'simp3d',
                '( ( t gcd ( K ^ t ) ) x. ( t / ( t gcd ( K ^ t ) ) ) ) = t')
    gex = w.s([], 'ovex', '( t gcd ( K ^ t ) ) e. _V')
    bex = w.s([], 'ovex', '( t / ( t gcd ( K ^ t ) ) ) e. _V')
    oth = w.s([gex, bex], 'opth',
              '( %s = %s <-> ( ( t gcd ( K ^ t ) ) = ( s gcd ( K ^ s ) ) /\\ '
              '( t / ( t gcd ( K ^ t ) ) ) = ( s / ( s gcd ( K ^ s ) ) ) ) )'
              % (PAIRC('t'), PAIRC('s')))
    APE = '( %s /\\ %s = %s )' % (AST, PAIRC('t'), PAIRC('s'))
    spe = mkst(w, APE)
    cnj = spe([spe([oth], 'a1i',
                   '( %s = %s <-> ( ( t gcd ( K ^ t ) ) = ( s gcd ( K ^ s ) ) /\\ '
                   '( t / ( t gcd ( K ^ t ) ) ) = ( s / ( s gcd ( K ^ s ) ) ) ) )'
                   % (PAIRC('t'), PAIRC('s'))),
               spe([], 'simpr', '%s = %s' % (PAIRC('t'), PAIRC('s')))], 'mpbid',
              '( ( t gcd ( K ^ t ) ) = ( s gcd ( K ^ s ) ) /\\ '
              '( t / ( t gcd ( K ^ t ) ) ) = ( s / ( s gcd ( K ^ s ) ) ) )')
    e1 = spe([cnj], 'simpld', '( t gcd ( K ^ t ) ) = ( s gcd ( K ^ s ) )')
    e2 = spe([cnj], 'simprd',
             '( t / ( t gcd ( K ^ t ) ) ) = ( s / ( s gcd ( K ^ s ) ) )')
    mm = spe([e1, e2], 'oveq12d',
             '( ( t gcd ( K ^ t ) ) x. ( t / ( t gcd ( K ^ t ) ) ) ) = '
             '( ( s gcd ( K ^ s ) ) x. ( s / ( s gcd ( K ^ s ) ) ) )')
    teqs = spe([spe([lift(w, prodt, APE)], 'eqcomd',
                    't = ( ( t gcd ( K ^ t ) ) x. ( t / ( t gcd ( K ^ t ) ) ) )'),
                spe([mm, lift(w, prods, APE)], 'eqtrd',
                    '( ( t gcd ( K ^ t ) ) x. ( t / ( t gcd ( K ^ t ) ) ) ) = s')],
               'eqtrd', 't = s')
    ex1 = sts([teqs], 'ex', '( %s = %s -> t = s )' % (PAIRC('t'), PAIRC('s')))
    r2a = stt([ex1], 'ralrimiva',
              'A. s e. %s ( %s = %s -> t = s )' % (FZW, PAIRC('t'), PAIRC('s')))
    r2 = st([r2a], 'ralrimiva',
            'A. t e. %s A. s e. %s ( %s = %s -> t = s )' % (FZW, FZW, PAIRC('t'), PAIRC('s')))
    both = st([r1, r2], 'jca',
              '( A. t e. %s %s e. %s /\\ A. t e. %s A. s e. %s ( %s = %s -> t = s ) )'
              % (FZW, PAIRC('t'), XSC, FZW, FZW, PAIRC('t'), PAIRC('s')))
    w.qed([st([bic], 'a1i',
              '( %s : %s -1-1-> %s <-> ( A. t e. %s %s e. %s /\\ '
              'A. t e. %s A. s e. %s ( %s = %s -> t = s ) ) )'
              % (FMAPC, FZW, XSC, FZW, PAIRC('t'), XSC, FZW, FZW, PAIRC('t'), PAIRC('s'))),
           both], 'mpbird', '( %s -> %s : %s -1-1-> %s )' % (AK, FMAPC, FZW, XSC))
    return w




GMAPC = '( o e. %s |-> ( 1 / o ) )' % SMK
HMAPC = '( f e. %s |-> ( 1 / f ) )' % CSK
BODYC = ('( ( %s ` ( 1st ` ( %s ` m ) ) ) x. ( %s ` ( 2nd ` ( %s ` m ) ) ) )'
         % (GMAPC, FMAPC, HMAPC, FMAPC))
SBODYC = 'sum_ m e. %s %s' % (FZW, BODYC)
HARM = 'sum_ m e. %s ( 1 / m )' % FZW
SMSUMI = 'sum_ i e. %s ( %s ` i )' % (SMK, GMAPC)
SMSUMJ = 'sum_ j e. %s ( 1 / j )' % SMK
SMSUMII = 'sum_ i e. %s ( 1 / i )' % SMK
SCOPH = 'sum_ j e. %s ( %s ` j )' % (CSK, HMAPC)
SCOP = 'sum_ j e. %s ( 1 / j )' % CSK
PRPFK = 'prod_ p e. %s ( 1 / ( 1 - ( 1 / p ) ) )' % PFK
PHIK = '( ( phi ` K ) / K )'
KPHI = '( K / ( phi ` K ) )'


def rege0c(w, ante, expr, rp):
    f = mkst(w, ante)
    return f([f([rp], 'rpred', '%s e. RR' % expr), f([rp], 'rpge0d', '0 <_ %s' % expr),
              f([w.s([], 'elrege0',
                     '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
                'a1i',
                '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (expr, expr, expr))],
             'mpbir2and', '%s e. ( 0 [,) +oo )' % expr)


def cophrm():
    w = WS('cophrm', 'The harmonic sum over the integers up to W coprime to K is at least '
                     'phi ( K ) / K times log W.')
    st = mkst(w, AK)
    knn = st([], 'simpl', 'K e. NN')
    wnn = st([], 'simpr', 'W e. NN')
    fzfin = st([], 'fzfid', '%s e. Fin' % FZW)
    smss = st([w.s([], 'ssrab2', '%s C_ %s' % (SMK, FZW))], 'a1i', '%s C_ %s' % (SMK, FZW))
    smfin = st([fzfin, smss], 'ssfid', '%s e. Fin' % SMK)
    csss = st([w.s([], 'ssrab2', '%s C_ %s' % (CSK, FZW))], 'a1i', '%s C_ %s' % (CSK, FZW))
    csfin = st([fzfin, csss], 'ssfid', '%s e. Fin' % CSK)
    # G and H are nonnegative functions
    AO = '( %s /\\ o e. %s )' % (AK, SMK)
    so = mkst(w, AO)
    onn = so([so([lift(w, smss, AO), so([], 'simpr', 'o e. %s' % SMK)], 'sseldd',
                 'o e. %s' % FZW), w.inst('elfznn')], 'syl', 'o e. NN')
    orp = so([so([onn], 'nnrpd', 'o e. RR+')], 'rpreccld', '( 1 / o ) e. RR+')
    gel = rege0c(w, AO, '( 1 / o )', orp)
    gfn = st([gel, w.s([], 'eqid', '%s = %s' % (GMAPC, GMAPC))], 'fmptd',
             '%s : %s --> ( 0 [,) +oo )' % (GMAPC, SMK))
    AFF = '( %s /\\ f e. %s )' % (AK, CSK)
    sff = mkst(w, AFF)
    fnn = sff([sff([lift(w, csss, AFF), sff([], 'simpr', 'f e. %s' % CSK)], 'sseldd',
                   'f e. %s' % FZW), w.inst('elfznn')], 'syl', 'f e. NN')
    frp = sff([sff([fnn], 'nnrpd', 'f e. RR+')], 'rpreccld', '( 1 / f ) e. RR+')
    hel = rege0c(w, AFF, '( 1 / f )', frp)
    hfn = st([hel, w.s([], 'eqid', '%s = %s' % (HMAPC, HMAPC))], 'fmptd',
             '%s : %s --> ( 0 [,) +oo )' % (HMAPC, CSK))
    f1 = st([], 'cof1', '%s : %s -1-1-> %s' % (FMAPC, FZW, XSC))
    spu = st([st([smfin, csfin, fzfin], '3jca',
                 '( %s e. Fin /\\ %s e. Fin /\\ %s e. Fin )' % (SMK, CSK, FZW)),
              st([gfn, hfn], 'jca',
                 '( %s : %s --> ( 0 [,) +oo ) /\\ %s : %s --> ( 0 [,) +oo ) )'
                 % (GMAPC, SMK, HMAPC, CSK)), f1, w.inst('sumprodub')], 'syl3anc',
             '%s <_ ( %s x. %s )' % (SBODYC, SMSUMI, SCOPH))
    # the two right-hand sums
    AI = '( %s /\\ i e. %s )' % (AK, SMK)
    si = mkst(w, AI)
    gival = si([si([si([], 'simpr', 'i e. %s' % SMK),
                    si([w.s([], 'ovex', '( 1 / i ) e. _V')], 'a1i', '( 1 / i ) e. _V')], 'jca',
                   '( i e. %s /\\ ( 1 / i ) e. _V )' % SMK),
                si([w.s([w.s([], 'oveq2', '( o = i -> ( 1 / o ) = ( 1 / i ) )'),
                         w.s([], 'eqid', '%s = %s' % (GMAPC, GMAPC))], 'fvmptg',
                        '( ( i e. %s /\\ ( 1 / i ) e. _V ) -> ( %s ` i ) = ( 1 / i ) )'
                        % (SMK, GMAPC))], 'a1i',
                   '( ( i e. %s /\\ ( 1 / i ) e. _V ) -> ( %s ` i ) = ( 1 / i ) )'
                   % (SMK, GMAPC))], 'mpd', '( %s ` i ) = ( 1 / i )' % GMAPC)
    gsum = st([gival], 'sumeq2dv', '%s = %s' % (SMSUMI, SMSUMII))
    cbg = st([w.s([w.s([], 'oveq2', '( i = j -> ( 1 / i ) = ( 1 / j ) )')], 'cbvsumv',
                  '%s = %s' % (SMSUMII, SMSUMJ))], 'a1i', '%s = %s' % (SMSUMII, SMSUMJ))
    gsum2 = st([gsum, cbg], 'eqtrd', '%s = %s' % (SMSUMI, SMSUMJ))
    AJ = '( %s /\\ j e. %s )' % (AK, CSK)
    sj = mkst(w, AJ)
    hjval = sj([sj([sj([], 'simpr', 'j e. %s' % CSK),
                    sj([w.s([], 'ovex', '( 1 / j ) e. _V')], 'a1i', '( 1 / j ) e. _V')], 'jca',
                   '( j e. %s /\\ ( 1 / j ) e. _V )' % CSK),
                sj([w.s([w.s([], 'oveq2', '( f = j -> ( 1 / f ) = ( 1 / j ) )'),
                         w.s([], 'eqid', '%s = %s' % (HMAPC, HMAPC))], 'fvmptg',
                        '( ( j e. %s /\\ ( 1 / j ) e. _V ) -> ( %s ` j ) = ( 1 / j ) )'
                        % (CSK, HMAPC))], 'a1i',
                   '( ( j e. %s /\\ ( 1 / j ) e. _V ) -> ( %s ` j ) = ( 1 / j ) )'
                   % (CSK, HMAPC))], 'mpd', '( %s ` j ) = ( 1 / j )' % HMAPC)
    hsum = st([hjval], 'sumeq2dv', '%s = %s' % (SCOPH, SCOP))
    rhs = st([gsum2, hsum], 'oveq12d',
             '( %s x. %s ) = ( %s x. %s )' % (SMSUMI, SCOPH, SMSUMJ, SCOP))
    spu2 = st([spu, rhs], 'breqtrd', '%s <_ ( %s x. %s )' % (SBODYC, SMSUMJ, SCOP))
    # the left-hand body is 1 / m
    AM = '( %s /\\ m e. %s )' % (AK, FZW)
    sm = mkst(w, AM)
    mfz = sm([], 'simpr', 'm e. %s' % FZW)
    spl = sm([sm([], 'id', AM), w.inst('cosplit')], 'syl',
             '( ( m gcd ( K ^ m ) ) e. %s /\\ ( m / ( m gcd ( K ^ m ) ) ) e. %s /\\ '
             '( ( m gcd ( K ^ m ) ) x. ( m / ( m gcd ( K ^ m ) ) ) ) = m )' % (SMK, CSK))
    GM = '( m gcd ( K ^ m ) )'
    BM = '( m / ( m gcd ( K ^ m ) ) )'
    gsm = sm([spl], 'simp1d', '%s e. %s' % (GM, SMK))
    bcs = sm([spl], 'simp2d', '%s e. %s' % (BM, CSK))
    prodm = sm([spl], 'simp3d', '( %s x. %s ) = m' % (GM, BM))
    tm = w.s([], 'id', '( t = m -> t = m )')
    ktm = w.s([tm], 'oveq2d', '( t = m -> ( K ^ t ) = ( K ^ m ) )')
    gtm = w.s([tm, ktm], 'oveq12d', '( t = m -> ( t gcd ( K ^ t ) ) = %s )' % GM)
    btm = w.s([tm, gtm], 'oveq12d',
              '( t = m -> ( t / ( t gcd ( K ^ t ) ) ) = %s )' % BM)
    cbp = w.s([gtm, btm], 'opeq12d', '( t = m -> %s = %s )' % (PAIRC('t'), PAIRC('m')))
    fmv = sm([sm([mfz, sm([w.s([], 'opex', '%s e. _V' % PAIRC('m'))], 'a1i',
                          '%s e. _V' % PAIRC('m'))], 'jca',
                 '( m e. %s /\\ %s e. _V )' % (FZW, PAIRC('m'))),
              sm([w.s([cbp, w.s([], 'eqid', '%s = %s' % (FMAPC, FMAPC))], 'fvmptg',
                      '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )'
                      % (FZW, PAIRC('m'), FMAPC, PAIRC('m')))], 'a1i',
                 '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )'
                 % (FZW, PAIRC('m'), FMAPC, PAIRC('m')))], 'mpd',
             '( %s ` m ) = %s' % (FMAPC, PAIRC('m')))
    gex = w.s([], 'ovex', '%s e. _V' % GM)
    bex = w.s([], 'ovex', '%s e. _V' % BM)
    o1 = w.s([gex, bex], 'op1st', '( 1st ` %s ) = %s' % (PAIRC('m'), GM))
    o2 = w.s([gex, bex], 'op2nd', '( 2nd ` %s ) = %s' % (PAIRC('m'), BM))
    f1st = sm([sm([fmv], 'fveq2d',
                  '( 1st ` ( %s ` m ) ) = ( 1st ` %s )' % (FMAPC, PAIRC('m'))),
               sm([o1], 'a1i', '( 1st ` %s ) = %s' % (PAIRC('m'), GM))], 'eqtrd',
              '( 1st ` ( %s ` m ) ) = %s' % (FMAPC, GM))
    f2nd = sm([sm([fmv], 'fveq2d',
                  '( 2nd ` ( %s ` m ) ) = ( 2nd ` %s )' % (FMAPC, PAIRC('m'))),
               sm([o2], 'a1i', '( 2nd ` %s ) = %s' % (PAIRC('m'), BM))], 'eqtrd',
              '( 2nd ` ( %s ` m ) ) = %s' % (FMAPC, BM))
    gval = sm([sm([gsm, sm([w.s([], 'ovex', '( 1 / %s ) e. _V' % GM)], 'a1i',
                           '( 1 / %s ) e. _V' % GM)], 'jca',
                  '( %s e. %s /\\ ( 1 / %s ) e. _V )' % (GM, SMK, GM)),
               sm([w.s([w.s([], 'oveq2', '( o = %s -> ( 1 / o ) = ( 1 / %s ) )' % (GM, GM)),
                        w.s([], 'eqid', '%s = %s' % (GMAPC, GMAPC))], 'fvmptg',
                       '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                       % (GM, SMK, GM, GMAPC, GM, GM))], 'a1i',
                  '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                  % (GM, SMK, GM, GMAPC, GM, GM))], 'mpd',
              '( %s ` %s ) = ( 1 / %s )' % (GMAPC, GM, GM))
    hval = sm([sm([bcs, sm([w.s([], 'ovex', '( 1 / %s ) e. _V' % BM)], 'a1i',
                           '( 1 / %s ) e. _V' % BM)], 'jca',
                  '( %s e. %s /\\ ( 1 / %s ) e. _V )' % (BM, CSK, BM)),
               sm([w.s([w.s([], 'oveq2', '( f = %s -> ( 1 / f ) = ( 1 / %s ) )' % (BM, BM)),
                        w.s([], 'eqid', '%s = %s' % (HMAPC, HMAPC))], 'fvmptg',
                       '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                       % (BM, CSK, BM, HMAPC, BM, BM))], 'a1i',
                  '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                  % (BM, CSK, BM, HMAPC, BM, BM))], 'mpd',
              '( %s ` %s ) = ( 1 / %s )' % (HMAPC, BM, BM))
    b1 = sm([sm([f1st], 'fveq2d',
                '( %s ` ( 1st ` ( %s ` m ) ) ) = ( %s ` %s )' % (GMAPC, FMAPC, GMAPC, GM)),
             gval], 'eqtrd',
            '( %s ` ( 1st ` ( %s ` m ) ) ) = ( 1 / %s )' % (GMAPC, FMAPC, GM))
    b2 = sm([sm([f2nd], 'fveq2d',
                '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( %s ` %s )' % (HMAPC, FMAPC, HMAPC, BM)),
             hval], 'eqtrd',
            '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( 1 / %s )' % (HMAPC, FMAPC, BM))
    bmul = sm([b1, b2], 'oveq12d',
              '%s = ( ( 1 / %s ) x. ( 1 / %s ) )' % (BODYC, GM, BM))
    mnn = sm([mfz, w.inst('elfznn')], 'syl', 'm e. NN')
    gmnn = sm([sm([lift(w, smss, AM), gsm], 'sseldd', '%s e. %s' % (GM, FZW)),
               w.inst('elfznn')], 'syl', '%s e. NN' % GM)
    bmnn = sm([sm([lift(w, csss, AM), bcs], 'sseldd', '%s e. %s' % (BM, FZW)),
               w.inst('elfznn')], 'syl', '%s e. NN' % BM)
    onec = sm([sm([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    dmd = sm([sm([onec, onec], 'jca', '( 1 e. CC /\\ 1 e. CC )'),
              sm([sm([sm([gmnn], 'nncnd', '%s e. CC' % GM),
                      sm([gmnn], 'nnne0d', '%s =/= 0' % GM)], 'jca',
                     '( %s e. CC /\\ %s =/= 0 )' % (GM, GM)),
                  sm([sm([bmnn], 'nncnd', '%s e. CC' % BM),
                      sm([bmnn], 'nnne0d', '%s =/= 0' % BM)], 'jca',
                     '( %s e. CC /\\ %s =/= 0 )' % (BM, BM))], 'jca',
                 '( ( %s e. CC /\\ %s =/= 0 ) /\\ ( %s e. CC /\\ %s =/= 0 ) )'
                 % (GM, GM, BM, BM)), w.inst('divmuldiv')], 'syl2anc',
             '( ( 1 / %s ) x. ( 1 / %s ) ) = ( ( 1 x. 1 ) / ( %s x. %s ) )' % (GM, BM, GM, BM))
    t11 = sm([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')
    dmd2 = sm([dmd, sm([sm([t11], 'oveq1d',
                           '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / ( %s x. %s ) )'
                           % (GM, BM, GM, BM)),
                        sm([prodm], 'oveq2d',
                           '( 1 / ( %s x. %s ) ) = ( 1 / m )' % (GM, BM))], 'eqtrd',
                       '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / m )' % (GM, BM))], 'eqtrd',
              '( ( 1 / %s ) x. ( 1 / %s ) ) = ( 1 / m )' % (GM, BM))
    bfin = sm([bmul, dmd2], 'eqtrd', '%s = ( 1 / m )' % BODYC)
    lsum = st([bfin], 'sumeq2dv', '%s = %s' % (SBODYC, HARM))
    main = st([lsum, spu2], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (HARM, SMSUMJ, SCOP))
    # log W <_ HARM
    wrp = st([wnn], 'nnrpd', 'W e. RR+')
    hl = st([wrp, w.inst('harmoniclbnd')], 'syl',
            '( log ` W ) <_ sum_ m e. ( 1 ... ( |_ ` W ) ) ( 1 / m )')
    flw = st([st([wnn], 'nnzd', 'W e. ZZ'), w.inst('flid')], 'syl', '( |_ ` W ) = W')
    hl2 = st([hl, st([st([flw], 'oveq2d', '( 1 ... ( |_ ` W ) ) = %s' % FZW)], 'sumeq1d',
                     'sum_ m e. ( 1 ... ( |_ ` W ) ) ( 1 / m ) = %s' % HARM)], 'breqtrd',
             '( log ` W ) <_ %s' % HARM)
    # smsum at Q = PF( K )
    sbq = w.s([], 'breq1', '( p = q -> ( p || K <-> q || K ) )')
    cbk = w.s([sbq], 'cbvrabv', '{ p e. Prime | p || K } = %s' % PFK)
    pffin0 = st([knn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || K } e. Fin')
    pffin = st([st([cbk], 'a1i', '{ p e. Prime | p || K } = %s' % PFK), pffin0], 'eqeltrrd',
               '%s e. Fin' % PFK)
    pfsub = st([w.s([], 'ssrab2', '%s C_ Prime' % PFK)], 'a1i', '%s C_ Prime' % PFK)
    sms = st([pffin, pfsub, wnn, w.inst('smsum')], 'syl3anc', '%s <_ %s' % (SMSUMJ, PRPFK))
    # PRPFK = K / phi ( K )
    AP = '( %s /\\ p e. %s )' % (AK, PFK)
    sp = mkst(w, AP)
    pprm = sp([lift(w, pfsub, AP), sp([], 'simpr', 'p e. %s' % PFK)], 'sseldd', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    pre = sp([prp], 'rpred', 'p e. RR')
    ppos = sp([prp], 'rpgt0d', '0 < p')
    pge = sp([sp([pprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'), w.inst('eluzle')],
             'syl', '2 <_ p')
    p1lt = linarith(w, AP, [pge], '1 < p', leaves={'p': pre})
    prc = sp([sp([sp([pre, ppos], 'jca', '( p e. RR /\\ 0 < p )'), w.inst('recgt1')], 'syl',
                 '( 1 < p <-> ( 1 / p ) < 1 )'), p1lt], 'mpbid', '( 1 / p ) < 1')
    prire = sp([sp([prp], 'rpreccld', '( 1 / p ) e. RR+')], 'rpred', '( 1 / p ) e. RR')
    pone = sp([], '1red', '1 e. RR')
    psubr = sp([pone, prire], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    psub0 = sp([sp([prire, pone], 'posdifd', '( ( 1 / p ) < 1 <-> 0 < ( 1 - ( 1 / p ) ) )'),
                prc], 'mpbid', '0 < ( 1 - ( 1 / p ) )')
    psubrp = sp([psubr, psub0], 'elrpd', '( 1 - ( 1 / p ) ) e. RR+')
    psubc = sp([psubr], 'recnd', '( 1 - ( 1 / p ) ) e. CC')
    psubne = sp([psubrp], 'rpne0d', '( 1 - ( 1 / p ) ) =/= 0')
    onec2 = sp([sp([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    fd = st([pffin, onec2, psubc, psubne], 'fproddiv',
            '%s = ( prod_ p e. %s 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) )' % (PRPFK, PFK, PFK))
    p1v = st([st([pffin], 'olcd', '( %s C_ ( ZZ>= ` M ) \\/ %s e. Fin )' % (PFK, PFK)),
              w.inst('prod1')], 'syl', 'prod_ p e. %s 1 = 1' % PFK)
    phival = st([knn, w.inst('phipfprod')], 'syl',
                'prod_ p e. %s ( 1 - ( 1 / p ) ) = %s' % (PFK, PHIK))
    phinn = st([knn], 'phicld', '( phi ` K ) e. NN')
    phirp = st([phinn], 'nnrpd', '( phi ` K ) e. RR+')
    krp = st([knn], 'nnrpd', 'K e. RR+')
    phikrp = st([phirp, krp], 'rpdivcld', '%s e. RR+' % PHIK)
    phikc = st([st([phikrp], 'rpred', '%s e. RR' % PHIK)], 'recnd', '%s e. CC' % PHIK)
    phikne = st([phikrp], 'rpne0d', '%s =/= 0' % PHIK)
    fd2 = st([fd, st([st([p1v], 'oveq1d',
                         '( prod_ p e. %s 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) ) = '
                         '( 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) )' % (PFK, PFK, PFK)),
                      st([phival], 'oveq2d',
                         '( 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) ) = ( 1 / %s )' % (PFK, PHIK))],
                     'eqtrd',
                     '( prod_ p e. %s 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) ) = ( 1 / %s )'
                     % (PFK, PFK, PHIK))], 'eqtrd', '%s = ( 1 / %s )' % (PRPFK, PHIK))
    rd = st([st([st([st([phinn], 'nncnd', '( phi ` K ) e. CC'),
                     st([phinn], 'nnne0d', '( phi ` K ) =/= 0')], 'jca',
                    '( ( phi ` K ) e. CC /\\ ( phi ` K ) =/= 0 )'),
                 st([st([knn], 'nncnd', 'K e. CC'), st([knn], 'nnne0d', 'K =/= 0')], 'jca',
                    '( K e. CC /\\ K =/= 0 )')], 'jca',
                '( ( ( phi ` K ) e. CC /\\ ( phi ` K ) =/= 0 ) /\\ ( K e. CC /\\ K =/= 0 ) )'),
             w.inst('recdiv')], 'syl', '( 1 / %s ) = %s' % (PHIK, KPHI))
    prval = st([fd2, rd], 'eqtrd', '%s = %s' % (PRPFK, KPHI))
    sms2 = st([sms, prval], 'breqtrd', '%s <_ %s' % (SMSUMJ, KPHI))
    # assemble
    ANJ = '( %s /\\ j e. %s )' % (AK, SMK)
    snj = mkst(w, ANJ)
    jnn1 = snj([snj([lift(w, smss, ANJ), snj([], 'simpr', 'j e. %s' % SMK)], 'sseldd',
                    'j e. %s' % FZW), w.inst('elfznn')], 'syl', 'j e. NN')
    jrp1 = snj([snj([jnn1], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jre1 = snj([jrp1], 'rpred', '( 1 / j ) e. RR')
    smre = st([smfin, jre1], 'fsumrecl', '%s e. RR' % SMSUMJ)
    smge = st([smfin, jre1, snj([jrp1], 'rpge0d', '0 <_ ( 1 / j )')], 'fsumge0',
              '0 <_ %s' % SMSUMJ)
    ACJ = '( %s /\\ j e. %s )' % (AK, CSK)
    scj = mkst(w, ACJ)
    jnn2 = scj([scj([lift(w, csss, ACJ), scj([], 'simpr', 'j e. %s' % CSK)], 'sseldd',
                    'j e. %s' % FZW), w.inst('elfznn')], 'syl', 'j e. NN')
    jrp2 = scj([scj([jnn2], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jre2 = scj([jrp2], 'rpred', '( 1 / j ) e. RR')
    scre = st([csfin, jre2], 'fsumrecl', '%s e. RR' % SCOP)
    scge = st([csfin, jre2, scj([jrp2], 'rpge0d', '0 <_ ( 1 / j )')], 'fsumge0', '0 <_ %s' % SCOP)
    AMM = '( %s /\\ m e. %s )' % (AK, FZW)
    smm = mkst(w, AMM)
    mre = smm([smm([smm([smm([], 'simpr', 'm e. %s' % FZW), w.inst('elfznn')], 'syl', 'm e. NN')],
                   'nnrpd', 'm e. RR+')], 'rpreccld', '( 1 / m ) e. RR+')
    hre = st([fzfin, smm([mre], 'rpred', '( 1 / m ) e. RR')], 'fsumrecl', '%s e. RR' % HARM)
    kphire = st([st([krp, phirp], 'rpdivcld', '%s e. RR+' % KPHI)], 'rpred', '%s e. RR' % KPHI)
    mulle = st([smre, kphire, scre, scge, sms2], 'lemul1ad',
               '( %s x. %s ) <_ ( %s x. %s )' % (SMSUMJ, SCOP, KPHI, SCOP))
    p1re = st([smre, scre], 'remulcld', '( %s x. %s ) e. RR' % (SMSUMJ, SCOP))
    p2re = st([kphire, scre], 'remulcld', '( %s x. %s ) e. RR' % (KPHI, SCOP))
    logre = st([wrp], 'relogcld', '( log ` W ) e. RR')
    ch1 = st([logre, hre, p1re, hl2, main], 'letrd', '( log ` W ) <_ ( %s x. %s )' % (SMSUMJ, SCOP))
    ch2 = st([logre, p1re, p2re, ch1, mulle], 'letrd',
             '( log ` W ) <_ ( %s x. %s )' % (KPHI, SCOP))
    phikre = st([phikrp], 'rpred', '%s e. RR' % PHIK)
    phikge = st([phikrp], 'rpge0d', '0 <_ %s' % PHIK)
    mul2 = st([logre, p2re, phikre, phikge, ch2], 'lemul2ad',
              '( %s x. ( log ` W ) ) <_ ( %s x. ( %s x. %s ) )' % (PHIK, PHIK, KPHI, SCOP))
    kphic = st([kphire], 'recnd', '%s e. CC' % KPHI)
    scopc = st([scre], 'recnd', '%s e. CC' % SCOP)
    assoc = st([phikc, kphic, scopc], 'mulassd',
               '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (PHIK, KPHI, SCOP, PHIK, KPHI, SCOP))
    prod1v = st([phikc, phikne], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (PHIK, PHIK))
    kk = st([st([prod1v], 'eqcomd', '1 = ( %s x. ( 1 / %s ) )' % (PHIK, PHIK)),
             st([rd], 'oveq2d', '( %s x. ( 1 / %s ) ) = ( %s x. %s )' % (PHIK, PHIK, PHIK, KPHI))],
            'eqtrd', '1 = ( %s x. %s )' % (PHIK, KPHI))
    m1 = st([st([kk], 'oveq1d', '( 1 x. %s ) = ( ( %s x. %s ) x. %s )' % (SCOP, PHIK, KPHI, SCOP)),
             assoc], 'eqtrd', '( 1 x. %s ) = ( %s x. ( %s x. %s ) )' % (SCOP, PHIK, KPHI, SCOP))
    m2 = st([st([scopc], 'mullidd', '( 1 x. %s ) = %s' % (SCOP, SCOP))], 'eqcomd',
            '%s = ( 1 x. %s )' % (SCOP, SCOP))
    m3 = st([m2, m1], 'eqtrd', '%s = ( %s x. ( %s x. %s ) )' % (SCOP, PHIK, KPHI, SCOP))
    w.qed([mul2, st([m3], 'eqcomd', '( %s x. ( %s x. %s ) ) = %s' % (PHIK, KPHI, SCOP, SCOP))],
          'breqtrd', '( %s -> ( %s x. ( log ` W ) ) <_ %s )' % (AK, PHIK, SCOP))
    return w


ALL2 = {'cophrm': cophrm}


ALL = {'cosplit': cosplit, 'cof1': cof1, 'cophrm': cophrm}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
