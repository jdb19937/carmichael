"""Sortie v2: TotientSum.lean (tskey, tsconst, totsuminv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

def PF(X, v='q'): return '{ %s e. Prime | %s || %s }' % (v, v, X)
def PRD(X, b='p'): return 'prod_ %s e. %s %s' % (b, X, b)
def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))

GT = '( t e. Prime |-> ( 1 / ( t - 1 ) ) )'
DVM = '{ x e. NN | x || M }'
SDM = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || M ) }'
def SQF(v): return 'if ( ( mmu ` %s ) =/= 0 , ( 1 / ( phi ` %s ) ) , 0 )' % (v, v)
PM = '( ( 1 ... M ) i^i Prime )'
NPM = PRD(PM)
SDN = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || %s ) }' % NPM
# sqfdvdprod ( a squarefree D <_ M divides the product of the primes up to M ) was
# generated here; its worksheet is worksheets/sqfdvdprod.mmp


def pclos(w, f, v, prm):
    """closures for a prime v from a step prm proving ( ctx -> v e. Prime )"""
    pnn = f([prm, w.inst('prmnn')], 'syl', '%s e. NN' % v)
    pc = f([pnn], 'nncnd', '%s e. CC' % v)
    pne = f([pnn], 'nnne0d', '%s =/= 0' % v)
    puz = f([prm, w.inst('prmuz2')], 'syl', '%s e. ( ZZ>= ` 2 )' % v)
    pm1rp = f([puz, w.inst('uz2m1rp')], 'syl', '( %s x. ( %s - 1 ) ) e. RR+' % (v, v))
    onec = f([], '1cnd', '1 e. CC')
    p1c = f([pc, onec], 'subcld', '( %s - 1 ) e. CC' % v)
    mne = f([pm1rp], 'rpne0d', '( %s x. ( %s - 1 ) ) =/= 0' % (v, v))
    p1ne = f([pc, p1c, mne], 'mulne0bbd', '( %s - 1 ) =/= 0' % v)
    return dict(pnn=pnn, pc=pc, pne=pne, p1c=p1c, p1ne=p1ne, onec=onec, pm1rp=pm1rp)


def tskey():
    w = W('tskey', 'The divisor sum of the squarefree totient reciprocal is M over its totient.')
    A = 'M e. NN'
    T = PF('M')
    S0 = 'sum_ d e. %s %s' % (DVM, SQF('d'))
    S1 = 'sum_ d e. %s %s' % (SDM, SQF('d'))
    S2 = 'sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SDM, PF('d'), GT)
    P1 = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (T, GT)
    P2 = 'prod_ p e. %s ( p / ( p - 1 ) )' % T
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    fin = st([m, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVM)
    gf1 = w.s([], 'eqid', '%s = %s' % (GT, GT))
    # G : Prime --> CC
    CT = '( %s /\\ t e. Prime )' % A
    ft = mkst(w, CT)
    ct = pclos(w, ft, 't', ft([], 'simpr', 't e. Prime'))
    gcl = ft([ct['onec'], ct['p1c'], ct['p1ne']], 'divcld', '( 1 / ( t - 1 ) ) e. CC')
    gfn = st([gcl, gf1], 'fmptd', '%s : Prime --> CC' % GT)
    elq = w.s([w.s([], 'breq1', '( q = r -> ( q || D <-> r || D ) )')], 'elrab',
              '( r e. %s <-> ( r e. Prime /\\ r || D ) )' % TD)
    CR = '( %s /\\ r e. %s )' % (A, TD)
    fr = mkst(w, CR)
    rin = fr([], 'simpr', 'r e. %s' % TD)
    rf = fr([fr([elq], 'a1i', '( r e. %s <-> ( r e. Prime /\\ r || D ) )' % TD), rin], 'mpbid',
            '( r e. Prime /\\ r || D )')
    rprm = fr([rf], 'simpld', 'r e. Prime')
    rdvd = fr([rf], 'simprd', 'r || D')
    rnn = fr([rprm, w.inst('prmnn')], 'syl', 'r e. NN')
    rz = fr([rnn], 'nnzd', 'r e. ZZ')
    rle = fr([fr([rz, fr([d], 'adantr', 'D e. NN'), w.inst('dvdsle')], 'syl2anc',
                 '( r || D -> r <_ D )'), rdvd], 'mpd', 'r <_ D')
    rleM = fr([fr([rnn], 'nnred', 'r e. RR'), fr([d], 'adantr', 'D e. NN'),
               fr([m], 'adantr', 'M e. NN'), rle, fr([dle], 'adantr', 'D <_ M')], 'x', 'x') if False else None
    rr = fr([rnn], 'nnred', 'r e. RR')
    dr = fr([fr([d], 'adantr', 'D e. NN')], 'nnred', 'D e. RR')
    mr = fr([fr([m], 'adantr', 'M e. NN')], 'nnred', 'M e. RR')
    rleM = fr([rr, dr, mr, rle, fr([dle], 'adantr', 'D <_ M')], 'letrd', 'r <_ M')
    r1 = fr([rnn, w.inst('nnge1')], 'syl', '1 <_ r')
    rfz = fr([fr([rz, fr([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'),
                  fr([fr([m], 'adantr', 'M e. NN')], 'nnzd', 'M e. ZZ'), w.inst('elfz')], 'syl3anc',
                 '( r e. ( 1 ... M ) <-> ( 1 <_ r /\\ r <_ M ) )'),
               fr([r1, rleM], 'jca', '( 1 <_ r /\\ r <_ M )')], 'mpbird', 'r e. ( 1 ... M )')
    rpm = fr([fr([w.s([], 'elin', '( r e. %s <-> ( r e. ( 1 ... M ) /\\ r e. Prime ) )' % PM)], 'a1i',
                 '( r e. %s <-> ( r e. ( 1 ... M ) /\\ r e. Prime ) )' % PM),
              fr([rfz, rprm], 'jca', '( r e. ( 1 ... M ) /\\ r e. Prime )')], 'mpbird',
             'r e. %s' % PM)
    ssd = w.s([rpm], 'ex', '( %s -> ( r e. %s -> r e. %s ) )' % (A, TD, PM))
    ss = st([ssd], 'ssrdv', '%s C_ %s' % (TD, PM))
    # split the product
    disj = st([w.s([], 'disjdif', '( %s i^i ( %s \\ %s ) ) = (/)' % (TD, PM, TD))], 'a1i',
              '( %s i^i ( %s \\ %s ) ) = (/)' % (TD, PM, TD))
    uni = st([st([ss, w.inst('undif')], 'sylib', '( %s u. ( %s \\ %s ) ) = %s' % (TD, PM, TD, PM))],
             'eqcomd', '%s = ( %s u. ( %s \\ %s ) )' % (PM, TD, PM, TD))
    CP = '( %s /\\ p e. %s )' % (A, PM)
    fp = mkst(w, CP)
    psspm = fp([w.s([], 'inss2', '%s C_ Prime' % PM)], 'a1i', '%s C_ Prime' % PM)
    pprm = fp([psspm, fp([], 'simpr', 'p e. %s' % PM)], 'sseldd', 'p e. Prime')
    pnn = fp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    pc = fp([pnn], 'nncnd', 'p e. CC')
    spl = st([disj, uni, finpm, pc], 'fsumsplit' if False else 'fprodsplit',
             '%s = ( %s x. prod_ p e. ( %s \\ %s ) p )' % (NPM, PRD(TD), PM, TD))
    pid = st([st([d, sq], 'jca', '( D e. NN /\\ ( mmu ` D ) =/= 0 )'), w.inst('sqfprodid')], 'syl',
             '%s = D' % PRD(TD))
    spl2 = st([spl, st([pid], 'oveq1d',
              '( %s x. prod_ p e. ( %s \\ %s ) p ) = ( D x. prod_ p e. ( %s \\ %s ) p )'
              % (PRD(TD), PM, TD, PM, TD))], 'eqtrd',
              '%s = ( D x. prod_ p e. ( %s \\ %s ) p )' % (NPM, PM, TD))
    # the cofactor is a positive integer
    CDF = '( %s /\\ p e. ( %s \\ %s ) )' % (A, PM, TD)
    fdf = mkst(w, CDF)
    pdif = fdf([], 'simpr', 'p e. ( %s \\ %s )' % (PM, TD))
    ppm = fdf([pdif, w.inst('eldifi')], 'syl', 'p e. %s' % PM)
    pprmf = fdf([fdf([w.s([], 'inss2', '%s C_ Prime' % PM)], 'a1i', '%s C_ Prime' % PM), ppm],
                'sseldd', 'p e. Prime')
    pnnf = fdf([pprmf, w.inst('prmnn')], 'syl', 'p e. NN')
    findf = st([finpm, st([w.s([], 'difss', '( %s \\ %s ) C_ %s' % (PM, TD, PM))], 'a1i',
                          '( %s \\ %s ) C_ %s' % (PM, TD, PM))], 'ssfid',
               '( %s \\ %s ) e. Fin' % (PM, TD))
    cofnn = st([findf, pnnf], 'fprodnncl', 'prod_ p e. ( %s \\ %s ) p e. NN' % (PM, TD))
    dz = st([d], 'nnzd', 'D e. ZZ')
    cofz = st([cofnn], 'nnzd', 'prod_ p e. ( %s \\ %s ) p e. ZZ' % (PM, TD))
    dvd = st([dz, cofz, w.inst('dvdsmul1')], 'syl2anc',
             'D || ( D x. prod_ p e. ( %s \\ %s ) p )' % (PM, TD))
    w.qed([dvd, st([spl2], 'eqcomd', '( D x. prod_ p e. ( %s \\ %s ) p ) = %s' % (PM, TD, NPM))],
          'breqtrd', '( %s -> D || %s )' % (A, NPM))
    return w


def tsctrm():
    w = W('tsctrm',
          'The reciprocal of d times its totient, as a product over the prime divisors.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    T = PF('D')
    PP = PRD(T)
    PP1 = 'prod_ p e. %s ( p - 1 )' % T
    PX = 'prod_ p e. %s ( p x. ( p - 1 ) )' % T
    PR = 'prod_ p e. %s ( 1 / ( p x. ( p - 1 ) ) )' % T
    st = mkst(w, A)
    d = st([], 'simpl', 'D e. NN')
    sq = st([], 'simpr', '( mmu ` D ) =/= 0')
    dc = st([d], 'nncnd', 'D e. CC')
    dne = st([d], 'nnne0d', 'D =/= 0')
    phn = st([d, w.inst('phicl')], 'syl', '( phi ` D ) e. NN')
    phc = st([phn], 'nncnd', '( phi ` D ) e. CC')
    phne = st([phn], 'nnne0d', '( phi ` D ) =/= 0')
    finp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), T))], 'a1i',
             '%s = %s' % (PF('D', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    CP = '( %s /\\ p e. %s )' % (A, T)
    fp = mkst(w, CP)
    pprm = fp([fp([], 'simpr', 'p e. %s' % T), w.inst('elrabi')], 'syl', 'p e. Prime')
    c = pclos(w, fp, 'p', pprm)
    pxc = fp([c['pc'], c['p1c']], 'mulcld', '( p x. ( p - 1 ) ) e. CC')
    pxne = fp([c['pc'], c['p1c'], c['pne'], c['p1ne']], 'mulne0d', '( p x. ( p - 1 ) ) =/= 0')
    onecp = fp([], '1cnd', '1 e. CC')
    dv = st([fin, onecp, pxc, pxne], 'fproddiv', '%s = ( prod_ p e. %s 1 / %s )' % (PR, T, PX))
    p1 = st([st([fin], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (T, T)), w.inst('prod1')],
            'syl', 'prod_ p e. %s 1 = 1' % T)
    dv2 = st([dv, st([p1], 'oveq1d', '( prod_ p e. %s 1 / %s ) = ( 1 / %s )' % (T, PX, PX))],
             'eqtrd', '%s = ( 1 / %s )' % (PR, PX))
    ml = st([fin, c['pc'], c['p1c']], 'fprodmul', '%s = ( %s x. %s )' % (PX, PP, PP1))
    pid = st([], 'sqfprodid', '%s = D' % PP)
    phs = st([], 'phisqf', '( phi ` D ) = %s' % PP1)
    ml2 = st([ml, st([pid, st([phs], 'eqcomd', '%s = ( phi ` D )' % PP1)], 'oveq12d',
             '( %s x. %s ) = ( D x. ( phi ` D ) )' % (PP, PP1))], 'eqtrd',
             '%s = ( D x. ( phi ` D ) )' % PX)
    rhs = st([dv2, st([ml2], 'oveq2d', '( 1 / %s ) = ( 1 / ( D x. ( phi ` D ) ) )' % PX)], 'eqtrd',
             '%s = ( 1 / ( D x. ( phi ` D ) ) )' % PR)
    onec = st([], '1cnd', '1 e. CC')
    lhs = st([onec, phc, phne, dc, dne], 'divdiv1d',
             '( ( 1 / ( phi ` D ) ) / D ) = ( 1 / ( ( phi ` D ) x. D ) )')
    cm = st([phc, dc], 'mulcomd', '( ( phi ` D ) x. D ) = ( D x. ( phi ` D ) )')
    lhs2 = st([lhs, st([cm], 'oveq2d',
              '( 1 / ( ( phi ` D ) x. D ) ) = ( 1 / ( D x. ( phi ` D ) ) )')], 'eqtrd',
              '( ( 1 / ( phi ` D ) ) / D ) = ( 1 / ( D x. ( phi ` D ) ) )')
    w.qed([lhs2, st([rhs], 'eqcomd', '( 1 / ( D x. ( phi ` D ) ) ) = %s' % PR)], 'eqtrd',
          '( %s -> ( ( 1 / ( phi ` D ) ) / D ) = %s )' % (A, PR))
    return w


G2 = '( t e. Prime |-> ( 1 / ( t x. ( t - 1 ) ) ) )'
NR = 'prod_ r e. %s r' % PM
SDR = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || %s ) }' % NR
SQM = '{ x e. ( 1 ... M ) | ( mmu ` x ) =/= 0 }'
def TERM(v): return '( %s / %s )' % (SQF(v), v)


def tsconst():
    w = W('tsconst',
          'The sum of one over d times the totient of d, over the squarefree d up to M, is at '
          'most e.')
    A = 'M e. NN'
    S0 = 'sum_ d e. ( 1 ... M ) %s' % TERM('d')
    S1 = 'sum_ d e. %s %s' % (SQM, TERM('d'))
    S2 = 'sum_ d e. %s %s' % (SDR, TERM('d'))
    S3 = 'sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SDR, PF('d'), G2)
    P1 = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (PF(NR), G2)
    P2 = 'prod_ p e. %s ( 1 + ( 1 / ( p x. ( p - 1 ) ) ) )' % PM
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    finM = st([], 'fzfid', '( 1 ... M ) e. Fin')
    finpm = st([finM, st([w.s([], 'inss1', '%s C_ ( 1 ... M )' % PM)], 'a1i',
                         '%s C_ ( 1 ... M )' % PM)], 'ssfid', '%s e. Fin' % PM)
    sspm = st([w.s([], 'inss2', '%s C_ Prime' % PM)], 'a1i', '%s C_ Prime' % PM)
    spd = st([finpm, sspm, w.inst('sqfprod')], 'syl2anc',
             '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )'
             % (PRD(PM), PRD(PM), PF(PRD(PM)), PM))
    cbp = st([w.s([w.s([], 'id', '( p = r -> p = r )')], 'cbvprodv', '%s = %s' % (PRD(PM), NR))],
             'a1i', '%s = %s' % (PRD(PM), NR))
    n12 = st([spd], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PRD(PM), PRD(PM)))
    nnn = st([cbp, st([n12], 'simpld', '%s e. NN' % PRD(PM))], 'eqeltrrd', '%s e. NN' % NR)
    nset = st([spd], 'simprd', '%s = %s' % (PF(PRD(PM)), PM))
    nset2 = st([st([st([cbp], 'breq2d', '( q || %s <-> q || %s )' % (PRD(PM), NR))], 'rabbidv',
                   '%s = %s' % (PF(PRD(PM)), PF(NR))), nset], 'eqtr3d', '%s = %s' % (PF(NR), PM))
    finsd = st([st([nnn, w.inst('dvdsfi')], 'syl', '{ x e. NN | x || %s } e. Fin' % NR),
                st([w.s([w.s([w.s([], 'simpr',
                   '( ( ( mmu ` x ) =/= 0 /\\ x || %s ) -> x || %s )' % (NR, NR))], 'a1i',
                   '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || %s ) -> x || %s ) )' % (NR, NR))],
                   'ss2rabi', '%s C_ { x e. NN | x || %s }' % (SDR, NR))], 'a1i',
                   '%s C_ { x e. NN | x || %s }' % (SDR, NR))], 'ssfid', '%s e. Fin' % SDR)
    # G2 : Prime --> CC
    gf1 = w.s([], 'eqid', '%s = %s' % (G2, G2))
    CT = '( %s /\\ t e. Prime )' % A
    ft = mkst(w, CT)
    ct = pclos(w, ft, 't', ft([], 'simpr', 't e. Prime'))
    txc = ft([ct['pc'], ct['p1c']], 'mulcld', '( t x. ( t - 1 ) ) e. CC')
    txne = ft([ct['pc'], ct['p1c'], ct['pne'], ct['p1ne']], 'mulne0d', '( t x. ( t - 1 ) ) =/= 0')
    gcl = ft([ct['onec'], txc, txne], 'divcld', '( 1 / ( t x. ( t - 1 ) ) ) e. CC')
    gfn = st([gcl, gf1], 'fmptd', '%s : Prime --> CC' % G2)
    gsub1 = w.s([], 'id', '( t = p -> t = p )')
    gsub2 = w.s([], 'oveq1', '( t = p -> ( t - 1 ) = ( p - 1 ) )')
    gsub3 = w.s([gsub1, gsub2], 'oveq12d',
                '( t = p -> ( t x. ( t - 1 ) ) = ( p x. ( p - 1 ) ) )')
    gsub4 = w.s([gsub3], 'oveq2d',
                '( t = p -> ( 1 / ( t x. ( t - 1 ) ) ) = ( 1 / ( p x. ( p - 1 ) ) ) )')
    gv = w.s([gsub4, gf1], 'fvmptg',
             '( ( p e. Prime /\\ ( 1 / ( p x. ( p - 1 ) ) ) e. _V ) -> ( %s ` p ) = ( 1 / ( p x. ( p - 1 ) ) ) )'
             % G2)
    key = st([nnn, gfn, w.inst('sqfdvdsum')], 'syl2anc', '%s = %s' % (S3, P1))
    # the termwise identity on the squarefree divisors of NR
    elsdr = w.s([w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d',
                          '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
                      w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (NR, NR))], 'anbi12d',
                     '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || %s ) <-> ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )'
                     % (NR, NR))], 'elrab',
                '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )' % (SDR, NR))
    CD = '( %s /\\ d e. %s )' % (A, SDR)
    fd = mkst(w, CD)
    din = fd([], 'simpr', 'd e. %s' % SDR)
    dfacts = fd([fd([elsdr], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )' % (SDR, NR)),
                 din], 'mpbid', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) )' % NR)
    dnn = fd([dfacts], 'simpld', 'd e. NN')
    dsq = fd([fd([dfacts], 'simprd', '( ( mmu ` d ) =/= 0 /\\ d || %s )' % NR)], 'simpld',
             '( mmu ` d ) =/= 0')
    iftr = fd([dsq], 'iftrued', '%s = ( 1 / ( phi ` d ) )' % SQF('d'))
    lhsd = fd([iftr], 'oveq1d', '%s = ( ( 1 / ( phi ` d ) ) / d )' % TERM('d'))
    trm = fd([fd([dnn, dsq], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'), w.inst('tsctrm')], 'syl',
             '( ( 1 / ( phi ` d ) ) / d ) = prod_ p e. %s ( 1 / ( p x. ( p - 1 ) ) )' % PF('d'))
    CDP = '( %s /\\ p e. %s )' % (CD, PF('d'))
    fdp = mkst(w, CDP)
    pprmd = fdp([fdp([], 'simpr', 'p e. %s' % PF('d')), w.inst('elrabi')], 'syl', 'p e. Prime')
    cdp = pclos(w, fdp, 'p', pprmd)
    pxcd = fdp([cdp['pc'], cdp['p1c']], 'mulcld', '( p x. ( p - 1 ) ) e. CC')
    pxned = fdp([cdp['pc'], cdp['p1c'], cdp['pne'], cdp['p1ne']], 'mulne0d',
                '( p x. ( p - 1 ) ) =/= 0')
    gexd = fdp([fdp([cdp['onec'], pxcd, pxned], 'divcld', '( 1 / ( p x. ( p - 1 ) ) ) e. CC'),
                w.inst('elex')], 'syl', '( 1 / ( p x. ( p - 1 ) ) ) e. _V')
    gvd = fdp([pprmd, gexd, gv], 'syl2anc', '( %s ` p ) = ( 1 / ( p x. ( p - 1 ) ) )' % G2)
    prdd = fd([gvd], 'prodeq2dv',
              'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 / ( p x. ( p - 1 ) ) )'
              % (PF('d'), G2, PF('d')))
    term = fd([fd([lhsd, trm], 'eqtrd',
                  '%s = prod_ p e. %s ( 1 / ( p x. ( p - 1 ) ) )' % (TERM('d'), PF('d'))),
               fd([prdd], 'eqcomd',
                  'prod_ p e. %s ( 1 / ( p x. ( p - 1 ) ) ) = prod_ p e. %s ( %s ` p )'
                  % (PF('d'), PF('d'), G2))], 'eqtrd',
              '%s = prod_ p e. %s ( %s ` p )' % (TERM('d'), PF('d'), G2))
    e1 = st([term], 'sumeq2dv', '%s = %s' % (S2, S3))
    # closures of the summand on SDR
    phnd = fd([dnn, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phrd = fd([phnd], 'nnred', '( phi ` d ) e. RR')
    phrpd = fd([phnd], 'nnrpd', '( phi ` d ) e. RR+')
    drpd = fd([dnn], 'nnrpd', 'd e. RR+')
    oned = fd([], '1red', '1 e. RR')
    recd = fd([oned, phrpd], 'rerpdivcld', '( 1 / ( phi ` d ) ) e. RR')
    zred = fd([], '0red', '0 e. RR')
    ifrd = fd([recd, zred], 'ifcld', '%s e. RR' % SQF('d'))
    trmre = fd([ifrd, drpd], 'rerpdivcld', '%s e. RR' % TERM('d'))
    z1d = fd([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    rec0 = fd([oned, phrpd, z1d], 'divge0d', '0 <_ ( 1 / ( phi ` d ) )')
    bb1 = w.s([], 'breq2', '( ( 1 / ( phi ` d ) ) = %s -> ( 0 <_ ( 1 / ( phi ` d ) ) <-> 0 <_ %s ) )'
              % (SQF('d'), SQF('d')))
    bb2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (SQF('d'), SQF('d')))
    hh3 = w.s([rec0], 'adantr',
              '( ( %s /\\ ( mmu ` d ) =/= 0 ) -> 0 <_ ( 1 / ( phi ` d ) ) )' % CD)
    hh4 = w.s([fd([zred], 'leidd', '0 <_ 0')], 'adantr',
              '( ( %s /\\ -. ( mmu ` d ) =/= 0 ) -> 0 <_ 0 )' % CD)
    if0 = fd([bb1, bb2, hh3, hh4], 'ifbothda', '0 <_ %s' % SQF('d'))
    trm0 = fd([ifrd, drpd, if0], 'divge0d', '0 <_ %s' % TERM('d'))
    # SQM C_ SDR
    CQ = '( %s /\\ d e. %s )' % (A, SQM)
    fqm = mkst(w, CQ)
    dsqm = fqm([], 'simpr', 'd e. %s' % SQM)
    elsqm = w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d',
                     '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )')], 'elrab',
                '( d e. %s <-> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % SQM)
    qf = fqm([fqm([elsqm], 'a1i',
                  '( d e. %s <-> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % SQM), dsqm],
             'mpbid', '( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 )')
    qfz = fqm([qf], 'simpld', 'd e. ( 1 ... M )')
    qsq = fqm([qf], 'simprd', '( mmu ` d ) =/= 0')
    qnn = fqm([qfz, w.inst('elfznn')], 'syl', 'd e. NN')
    qdv = fqm([fqm([fqm([fqm([m], 'adantr', 'M e. NN'), qfz], 'jca',
                        '( M e. NN /\\ d e. ( 1 ... M ) )'), qsq], 'jca',
                   '( ( M e. NN /\\ d e. ( 1 ... M ) ) /\\ ( mmu ` d ) =/= 0 )'),
               w.inst('sqfdvdprod')], 'syl', 'd || %s' % PRD(PM))
    qdv2 = fqm([qdv, fqm([cbp], 'adantr', '%s = %s' % (PRD(PM), NR))], 'breqtrd', 'd || %s' % NR)
    qsdr = fqm([fqm([elsdr], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) ) )' % (SDR, NR)),
                fqm([qnn, fqm([qsq, qdv2], 'jca', '( ( mmu ` d ) =/= 0 /\\ d || %s )' % NR)], 'jca',
                    '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || %s ) )' % NR)], 'mpbird',
               'd e. %s' % SDR)
    sqmss = st([w.s([qsdr], 'ex', '( %s -> ( d e. %s -> d e. %s ) )' % (A, SQM, SDR))], 'ssrdv',
               '%s C_ %s' % (SQM, SDR))
    less = st([finsd, trmre, trm0, sqmss], 'fsumless', '%s <_ %s' % (S1, S2))
    # the sum over ( 1 ... M ) restricted to the squarefree part
    ssm = st([w.s([], 'ssrab2', '%s C_ ( 1 ... M )' % SQM)], 'a1i', '%s C_ ( 1 ... M )' % SQM)
    CM = '( %s /\\ d e. ( 1 ... M ) )' % A
    fm2 = mkst(w, CM)
    dnnm = fm2([fm2([], 'simpr', 'd e. ( 1 ... M )'), w.inst('elfznn')], 'syl', 'd e. NN')
    phnm = fm2([dnnm, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phrpm = fm2([phnm], 'nnrpd', '( phi ` d ) e. RR+')
    onem = fm2([], '1red', '1 e. RR')
    recm = fm2([onem, phrpm], 'rerpdivcld', '( 1 / ( phi ` d ) ) e. RR')
    zrem = fm2([], '0red', '0 e. RR')
    ifrm = fm2([recm, zrem], 'ifcld', '%s e. RR' % SQF('d'))
    drpm = fm2([dnnm], 'nnrpd', 'd e. RR+')
    trmm = fm2([ifrm, drpm], 'rerpdivcld', '%s e. RR' % TERM('d'))
    trmcm = fm2([trmm], 'recnd', '%s e. CC' % TERM('d'))
    CQD = '( %s /\\ d e. ( ( 1 ... M ) \\ %s ) )' % (A, SQM)
    fqd = mkst(w, CQD)
    ddif = fqd([], 'simpr', 'd e. ( ( 1 ... M ) \\ %s )' % SQM)
    dfzq = fqd([ddif, w.inst('eldifi')], 'syl', 'd e. ( 1 ... M )')
    dnsq = fqd([ddif, w.inst('eldifn')], 'syl', '-. d e. %s' % SQM)
    nsq2 = fqd([fqd([elsqm], 'a1i',
                    '( d e. %s <-> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % SQM), dnsq],
               'mtbid', '-. ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 )')
    CJ = '( %s /\\ ( mmu ` d ) =/= 0 )' % CQD
    jcq = w.s([w.s([dfzq], 'adantr', '( %s -> d e. ( 1 ... M ) )' % CJ),
               w.s([], 'simpr', '( %s -> ( mmu ` d ) =/= 0 )' % CJ)], 'jca',
              '( %s -> ( d e. ( 1 ... M ) /\\ ( mmu ` d ) =/= 0 ) )' % CJ)
    mu0q = fqd([nsq2, jcq], 'mtand', '-. ( mmu ` d ) =/= 0')
    ifq = fqd([mu0q], 'iffalsed', '%s = 0' % SQF('d'))
    dnnq = fqd([dfzq, w.inst('elfznn')], 'syl', 'd e. NN')
    vanq = fqd([fqd([ifq], 'oveq1d', '%s = ( 0 / d )' % TERM('d')),
                fqd([fqd([dnnq], 'nncnd', 'd e. CC'), fqd([dnnq], 'nnne0d', 'd =/= 0')], 'div0d',
                    '( 0 / d ) = 0')], 'eqtrd', '%s = 0' % TERM('d'))
    phnq = fqm([qnn, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phrpq = fqm([phnq], 'nnrpd', '( phi ` d ) e. RR+')
    oneq = fqm([], '1red', '1 e. RR')
    recq = fqm([oneq, phrpq], 'rerpdivcld', '( 1 / ( phi ` d ) ) e. RR')
    zreq = fqm([], '0red', '0 e. RR')
    ifrq = fqm([recq, zreq], 'ifcld', '%s e. RR' % SQF('d'))
    drpq = fqm([qnn], 'nnrpd', 'd e. RR+')
    trmq = fqm([ifrq, drpq], 'rerpdivcld', '%s e. RR' % TERM('d'))
    trmcq = fqm([trmq], 'recnd', '%s e. CC' % TERM('d'))
    ssum = st([ssm, trmcq, vanq, finM], 'fsumss', '%s = %s' % (S1, S0))
    # the outer product over the primes up to M
    CP2 = '( %s /\\ p e. %s )' % (A, PF(NR))
    fp2 = mkst(w, CP2)
    pprm2 = fp2([fp2([], 'simpr', 'p e. %s' % PF(NR)), w.inst('elrabi')], 'syl', 'p e. Prime')
    cp2 = pclos(w, fp2, 'p', pprm2)
    pxc2 = fp2([cp2['pc'], cp2['p1c']], 'mulcld', '( p x. ( p - 1 ) ) e. CC')
    pxne2 = fp2([cp2['pc'], cp2['p1c'], cp2['pne'], cp2['p1ne']], 'mulne0d',
                '( p x. ( p - 1 ) ) =/= 0')
    gex2 = fp2([fp2([cp2['onec'], pxc2, pxne2], 'divcld', '( 1 / ( p x. ( p - 1 ) ) ) e. CC'),
                w.inst('elex')], 'syl', '( 1 / ( p x. ( p - 1 ) ) ) e. _V')
    gv2 = fp2([pprm2, gex2, gv], 'syl2anc', '( %s ` p ) = ( 1 / ( p x. ( p - 1 ) ) )' % G2)
    pe1 = st([fp2([gv2], 'oveq2d',
             '( 1 + ( %s ` p ) ) = ( 1 + ( 1 / ( p x. ( p - 1 ) ) ) )' % G2)], 'prodeq2dv',
             '%s = prod_ p e. %s ( 1 + ( 1 / ( p x. ( p - 1 ) ) ) )' % (P1, PF(NR)))
    pe2 = st([nset2], 'prodeq1d',
             'prod_ p e. %s ( 1 + ( 1 / ( p x. ( p - 1 ) ) ) ) = %s' % (PF(NR), P2))
    pe3 = st([pe1, pe2], 'eqtrd', '%s = %s' % (P1, P2))
    onerp = st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')
    ppu = st([m, onerp, w.inst('primprodub')], 'syl2anc', '%s <_ ( exp ` 1 )' % P2)
    # assemble
    a1 = st([e1, key], 'eqtrd', '%s = %s' % (S2, P1))
    a2 = st([a1, pe3], 'eqtrd', '%s = %s' % (S2, P2))
    a3 = st([less, a2], 'breqtrd', '%s <_ %s' % (S1, P2))
    a4 = st([st([ssum], 'eqcomd', '%s = %s' % (S0, S1)), a3], 'eqbrtrd', '%s <_ %s' % (S0, P2))
    s0re = st([finM, trmm], 'fsumrecl', '%s e. RR' % S0)
    CPM = '( %s /\\ p e. %s )' % (A, PM)
    fpm = mkst(w, CPM)
    pprm3 = fpm([fpm([w.s([], 'inss2', '%s C_ Prime' % PM)], 'a1i', '%s C_ Prime' % PM),
                 fpm([], 'simpr', 'p e. %s' % PM)], 'sseldd', 'p e. Prime')
    cp3 = pclos(w, fpm, 'p', pprm3)
    pxrp3 = fpm([cp3['pm1rp']], 'rpreccld', '( 1 / ( p x. ( p - 1 ) ) ) e. RR+')
    pxr3 = fpm([pxrp3], 'rpred', '( 1 / ( p x. ( p - 1 ) ) ) e. RR')
    one3 = fpm([], '1red', '1 e. RR')
    bd3 = fpm([one3, pxr3], 'readdcld', '( 1 + ( 1 / ( p x. ( p - 1 ) ) ) ) e. RR')
    p2re = st([finpm, bd3], 'fprodrecl', '%s e. RR' % P2)
    efre = st([st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'reefcld', '( exp ` 1 ) e. RR')
    w.qed([s0re, p2re, efre, a4, ppu], 'letrd', '( %s -> %s <_ ( exp ` 1 ) )' % (A, S0))
    return w



def tsinner():
    w = W('tsinner', 'The inner sum bound for the totient reciprocal estimate.')
    A = '( M e. NN /\\ D e. ( 1 ... M ) )'
    FZ = '( 1 ... ( |_ ` ( M / D ) ) )'
    LOG = '( 1 + ( log ` M ) )'
    SUM = 'sum_ m e. %s ( %s / ( D x. m ) )' % (FZ, SQF('D'))
    HS = 'sum_ m e. %s ( 1 / m )' % FZ
    st = mkst(w, A)
    m = st([], 'simpl', 'M e. NN')
    dfz = st([], 'simpr', 'D e. ( 1 ... M )')
    d = st([dfz, w.inst('elfznn')], 'syl', 'D e. NN')
    dc = st([d], 'nncnd', 'D e. CC')
    dne = st([d], 'nnne0d', 'D =/= 0')
    drp = st([d], 'nnrpd', 'D e. RR+')
    phn = st([d, w.inst('phicl')], 'syl', '( phi ` D ) e. NN')
    phrp = st([phn], 'nnrpd', '( phi ` D ) e. RR+')
    one = st([], '1red', '1 e. RR')
    rec = st([one, phrp], 'rerpdivcld', '( 1 / ( phi ` D ) ) e. RR')
    zre = st([], '0red', '0 e. RR')
    ifre = st([rec, zre], 'ifcld', '%s e. RR' % SQF('D'))
    z1 = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    rec0 = st([one, phrp, z1], 'divge0d', '0 <_ ( 1 / ( phi ` D ) )')
    bb1 = w.s([], 'breq2',
              '( ( 1 / ( phi ` D ) ) = %s -> ( 0 <_ ( 1 / ( phi ` D ) ) <-> 0 <_ %s ) )'
              % (SQF('D'), SQF('D')))
    bb2 = w.s([], 'breq2', '( 0 = %s -> ( 0 <_ 0 <-> 0 <_ %s ) )' % (SQF('D'), SQF('D')))
    h3 = w.s([rec0], 'adantr',
             '( ( %s /\\ ( mmu ` D ) =/= 0 ) -> 0 <_ ( 1 / ( phi ` D ) ) )' % A)
    h4 = w.s([st([zre], 'leidd', '0 <_ 0')], 'adantr',
             '( ( %s /\\ -. ( mmu ` D ) =/= 0 ) -> 0 <_ 0 )' % A)
    if0 = st([bb1, bb2, h3, h4], 'ifbothda', '0 <_ %s' % SQF('D'))
    ifc = st([ifre], 'recnd', '%s e. CC' % SQF('D'))
    edr = st([ifre, drp], 'rerpdivcld', '( %s / D ) e. RR' % SQF('D'))
    ed0 = st([ifre, drp, if0], 'divge0d', '0 <_ ( %s / D )' % SQF('D'))
    edc = st([ifc, dc, dne], 'divcld', '( %s / D ) e. CC' % SQF('D'))
    fin = st([], 'fzfid', '%s e. Fin' % FZ)
    harm = st([m, dfz, w.inst('harmub')], 'syl2anc', '%s <_ %s' % (HS, LOG))
    # termwise
    BM = '( %s /\\ m e. %s )' % (A, FZ)
    fm = mkst(w, BM)
    mnn = fm([fm([], 'simpr', 'm e. %s' % FZ), w.inst('elfznn')], 'syl', 'm e. NN')
    mc = fm([mnn], 'nncnd', 'm e. CC')
    mne = fm([mnn], 'nnne0d', 'm =/= 0')
    mrp = fm([mnn], 'nnrpd', 'm e. RR+')
    ifcm = fm([ifc], 'adantr', '%s e. CC' % SQF('D'))
    dcm = fm([dc], 'adantr', 'D e. CC')
    dnem = fm([dne], 'adantr', 'D =/= 0')
    edcm = fm([edc], 'adantr', '( %s / D ) e. CC' % SQF('D'))
    dd = fm([ifcm, dcm, dnem, mc, mne], 'divdiv1d',
            '( ( %s / D ) / m ) = ( %s / ( D x. m ) )' % (SQF('D'), SQF('D')))
    dr = fm([edcm, mc, mne], 'divrecd',
            '( ( %s / D ) / m ) = ( ( %s / D ) x. ( 1 / m ) )' % (SQF('D'), SQF('D')))
    teq = fm([dd, dr], 'eqtr3d',
             '( %s / ( D x. m ) ) = ( ( %s / D ) x. ( 1 / m ) )' % (SQF('D'), SQF('D')))
    recc = fm([fm([mrp], 'rpreccld', '( 1 / m ) e. RR+')], 'rpcnd', '( 1 / m ) e. CC')
    recr = fm([fm([mrp], 'rpreccld', '( 1 / m ) e. RR+')], 'rpred', '( 1 / m ) e. RR')
    e1 = st([teq], 'sumeq2dv',
            '%s = sum_ m e. %s ( ( %s / D ) x. ( 1 / m ) )' % (SUM, FZ, SQF('D')))
    mul = st([fin, edc, recc], 'fsummulc2',
             '( ( %s / D ) x. %s ) = sum_ m e. %s ( ( %s / D ) x. ( 1 / m ) )'
             % (SQF('D'), HS, FZ, SQF('D')))
    e2 = st([e1, mul], 'eqtr4d', '%s = ( ( %s / D ) x. %s )' % (SUM, SQF('D'), HS))
    hsre = st([fin, recr], 'fsumrecl', '%s e. RR' % HS)
    mrp2 = st([m], 'nnrpd', 'M e. RR+')
    logm = st([mrp2], 'relogcld', '( log ` M ) e. RR')
    logr = st([one, logm], 'readdcld', '%s e. RR' % LOG)
    lem = st([hsre, logr, edr, ed0, harm], 'lemul2ad',
             '( ( %s / D ) x. %s ) <_ ( ( %s / D ) x. %s )' % (SQF('D'), HS, SQF('D'), LOG))
    w.qed([e2, lem], 'eqbrtrd',
          '( %s -> %s <_ ( ( %s / D ) x. %s ) )' % (A, SUM, SQF('D'), LOG))
    return w


def totsuminv():
    w = W('totsuminv',
          'The sum of the reciprocal of the totient up to M is at most e x. ( 1 + log M ).')
    A = 'M e. NN'
    LOG = '( 1 + ( log ` M ) )'
    FY = '( 1 ... ( |_ ` M ) )'
    FZd = '( 1 ... ( |_ ` ( M / d ) ) )'
    DVN = '{ x e. NN | x || n }'
    IB = '( %s / n )' % SQF('d')
    IC = '( %s / ( d x. m ) )' % SQF('d')
    S0 = 'sum_ n e. ( 1 ... M ) ( 1 / ( phi ` n ) )'
    SM = 'sum_ m e. ( 1 ... M ) ( 1 / ( phi ` m ) )'
    S1 = 'sum_ n e. ( 1 ... M ) sum_ d e. %s %s' % (DVN, IB)
    S1F = 'sum_ n e. %s sum_ d e. %s %s' % (FY, DVN, IB)
    S2F = 'sum_ d e. %s sum_ m e. %s %s' % (FY, FZd, IC)
    S2 = 'sum_ d e. ( 1 ... M ) sum_ m e. %s %s' % (FZd, IC)
    S3 = 'sum_ d e. ( 1 ... M ) ( ( %s / d ) x. %s )' % (SQF('d'), LOG)
    SK = 'sum_ d e. ( 1 ... M ) ( %s / d )' % SQF('d')
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    mz = st([m], 'nnzd', 'M e. ZZ')
    mr = st([m], 'nnred', 'M e. RR')
    mrp = st([m], 'nnrpd', 'M e. RR+')
    fl = st([mz, w.inst('flid')], 'syl', '( |_ ` M ) = M')
    fzeq = st([fl], 'oveq2d', '%s = ( 1 ... M )' % FY)
    fin = st([], 'fzfid', '( 1 ... M ) e. Fin')
    logm = st([mrp], 'relogcld', '( log ` M ) e. RR')
    one = st([], '1red', '1 e. RR')
    logr = st([one, logm], 'readdcld', '%s e. RR' % LOG)
    m1 = st([m, w.inst('nnge1')], 'syl', '1 <_ M')
    log0 = st([mr, m1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` M )')
    z1 = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    logge = st([one, logm, z1, log0], 'addge0d', '0 <_ %s' % LOG)
    # ( 1 ) the termwise divisor expansion
    BN = '( %s /\\ n e. ( 1 ... M ) )' % A
    fn = mkst(w, BN)
    nnn = fn([fn([], 'simpr', 'n e. ( 1 ... M )'), w.inst('elfznn')], 'syl', 'n e. NN')
    nc = fn([nnn], 'nncnd', 'n e. CC')
    nne = fn([nnn], 'nnne0d', 'n =/= 0')
    phnn = fn([nnn, w.inst('phicl')], 'syl', '( phi ` n ) e. NN')
    phc = fn([phnn], 'nncnd', '( phi ` n ) e. CC')
    phne = fn([phnn], 'nnne0d', '( phi ` n ) =/= 0')
    finn = fn([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVN)
    tsk = fn([nnn, w.inst('tskey')], 'syl', 'sum_ d e. %s %s = ( n / ( phi ` n ) )' % (DVN, SQF('d')))
    BND = '( %s /\\ d e. %s )' % (BN, DVN)
    fnd = mkst(w, BND)
    dnn = fnd([fnd([], 'simpr', 'd e. %s' % DVN), w.inst('elrabi')], 'syl', 'd e. NN')
    phnd = fnd([dnn, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phrpd = fnd([phnd], 'nnrpd', '( phi ` d ) e. RR+')
    oned = fnd([], '1red', '1 e. RR')
    recd = fnd([oned, phrpd], 'rerpdivcld', '( 1 / ( phi ` d ) ) e. RR')
    zred = fnd([], '0red', '0 e. RR')
    ifrd = fnd([recd, zred], 'ifcld', '%s e. RR' % SQF('d'))
    ifcd = fnd([ifrd], 'recnd', '%s e. CC' % SQF('d'))
    dvc = fn([finn, nc, ifcd, nne], 'fsumdivc',
             '( sum_ d e. %s %s / n ) = sum_ d e. %s %s' % (DVN, SQF('d'), DVN, IB))
    t1 = fn([nc, phc, nc, phne, nne], 'divdiv32d',
            '( ( n / ( phi ` n ) ) / n ) = ( ( n / n ) / ( phi ` n ) )')
    t2 = fn([nc, nne], 'dividd', '( n / n ) = 1')
    t3 = fn([t1, fn([t2], 'oveq1d', '( ( n / n ) / ( phi ` n ) ) = ( 1 / ( phi ` n ) )')], 'eqtrd',
            '( ( n / ( phi ` n ) ) / n ) = ( 1 / ( phi ` n ) )')
    t4 = fn([fn([tsk], 'oveq1d',
            '( sum_ d e. %s %s / n ) = ( ( n / ( phi ` n ) ) / n )' % (DVN, SQF('d'))), t3], 'eqtrd',
            '( sum_ d e. %s %s / n ) = ( 1 / ( phi ` n ) )' % (DVN, SQF('d')))
    term = fn([fn([dvc], 'eqcomd', 'sum_ d e. %s %s = ( sum_ d e. %s %s / n )'
                  % (DVN, IB, DVN, SQF('d'))), t4], 'eqtrd',
              'sum_ d e. %s %s = ( 1 / ( phi ` n ) )' % (DVN, IB))
    e1 = st([fn([term], 'eqcomd', '( 1 / ( phi ` n ) ) = sum_ d e. %s %s' % (DVN, IB))],
            'sumeq2dv', '%s = %s' % (S0, S1))
    # ( 2 ) the double-sum swap
    sub = w.s([], 'oveq2', '( n = ( d x. m ) -> %s = %s )' % (IB, IC))
    BND2 = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (A, FY, DVN)
    fnd2 = mkst(w, BND2)
    pr = fnd2([], 'simpr', '( n e. %s /\\ d e. %s )' % (FY, DVN))
    nfz2 = fnd2([pr], 'simpld', 'n e. %s' % FY)
    dvs2 = fnd2([pr], 'simprd', 'd e. %s' % DVN)
    nnn2 = fnd2([nfz2, w.inst('elfznn')], 'syl', 'n e. NN')
    dnn2 = fnd2([dvs2, w.inst('elrabi')], 'syl', 'd e. NN')
    phnd2 = fnd2([dnn2, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phrpd2 = fnd2([phnd2], 'nnrpd', '( phi ` d ) e. RR+')
    oned2 = fnd2([], '1red', '1 e. RR')
    recd2 = fnd2([oned2, phrpd2], 'rerpdivcld', '( 1 / ( phi ` d ) ) e. RR')
    zred2 = fnd2([], '0red', '0 e. RR')
    ifrd2 = fnd2([recd2, zred2], 'ifcld', '%s e. RR' % SQF('d'))
    nrp2 = fnd2([nnn2], 'nnrpd', 'n e. RR+')
    ibre = fnd2([ifrd2, nrp2], 'rerpdivcld', '%s e. RR' % IB)
    ibc = fnd2([ibre], 'recnd', '%s e. CC' % IB)
    swap = st([sub, mr, ibc], 'dvdsflsumcom', '%s = %s' % (S1F, S2F))
    e2a = st([fzeq], 'sumeq1d', '%s = %s' % (S1F, S1))
    e2b = st([fzeq], 'sumeq1d', '%s = %s' % (S2F, S2))
    e2 = st([st([e2a], 'eqcomd', '%s = %s' % (S1, S1F)),
             st([swap, e2b], 'eqtrd', '%s = %s' % (S1F, S2))], 'eqtrd', '%s = %s' % (S1, S2))
    e3 = st([e1, e2], 'eqtrd', '%s = %s' % (S0, S2))
    # ( 3 ) the inner bound
    BD = '( %s /\\ d e. ( 1 ... M ) )' % A
    fd = mkst(w, BD)
    dfz = fd([], 'simpr', 'd e. ( 1 ... M )')
    dnnd = fd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    inner = fd([fd([m], 'adantr', 'M e. NN'), dfz, w.inst('tsinner')], 'syl2anc',
               'sum_ m e. %s %s <_ ( ( %s / d ) x. %s )' % (FZd, IC, SQF('d'), LOG))
    phnD = fd([dnnd, w.inst('phicl')], 'syl', '( phi ` d ) e. NN')
    phrpD = fd([phnD], 'nnrpd', '( phi ` d ) e. RR+')
    oneD = fd([], '1red', '1 e. RR')
    recD = fd([oneD, phrpD], 'rerpdivcld', '( 1 / ( phi ` d ) ) e. RR')
    zreD = fd([], '0red', '0 e. RR')
    ifrD = fd([recD, zreD], 'ifcld', '%s e. RR' % SQF('d'))
    drpD = fd([dnnd], 'nnrpd', 'd e. RR+')
    edrD = fd([ifrD, drpD], 'rerpdivcld', '( %s / d ) e. RR' % SQF('d'))
    edcD = fd([edrD], 'recnd', '( %s / d ) e. CC' % SQF('d'))
    logrD = fd([logr], 'adantr', '%s e. RR' % LOG)
    prrD = fd([edrD, logrD], 'remulcld', '( ( %s / d ) x. %s ) e. RR' % (SQF('d'), LOG))
    finD = fd([], 'fzfid', '%s e. Fin' % FZd)
    BDM = '( %s /\\ m e. %s )' % (BD, FZd)
    fdm = mkst(w, BDM)
    mnnD = fdm([fdm([], 'simpr', 'm e. %s' % FZd), w.inst('elfznn')], 'syl', 'm e. NN')
    dnnD2 = fdm([dnnd], 'adantr', 'd e. NN')
    dmD = fdm([dnnD2, mnnD], 'nnmulcld', '( d x. m ) e. NN')
    dmrpD = fdm([dmD], 'nnrpd', '( d x. m ) e. RR+')
    ifrDm = fdm([ifrD], 'adantr', '%s e. RR' % SQF('d'))
    icre = fdm([ifrDm, dmrpD], 'rerpdivcld', '%s e. RR' % IC)
    insre = fd([finD, icre], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (FZd, IC))
    sle = st([fin, insre, prrD, inner], 'fsumle', '%s <_ %s' % (S2, S3))
    # ( 4 ) factor out and apply tsconst
    logc = st([logr], 'recnd', '%s e. CC' % LOG)
    mulc = st([fin, logc, edcD], 'fsummulc1', '( %s x. %s ) = %s' % (SK, LOG, S3))
    skre = st([fin, edrD], 'fsumrecl', '%s e. RR' % SK)
    tsc = st([], 'tsconst', '%s <_ ( exp ` 1 )' % SK)
    efre = st([st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'reefcld', '( exp ` 1 ) e. RR')
    lem = st([skre, efre, logr, logge, tsc], 'lemul1ad',
             '( %s x. %s ) <_ ( ( exp ` 1 ) x. %s )' % (SK, LOG, LOG))
    le3 = st([st([mulc], 'eqcomd', '%s = ( %s x. %s )' % (S3, SK, LOG)), lem], 'eqbrtrd',
             '%s <_ ( ( exp ` 1 ) x. %s )' % (S3, LOG))
    s2re = st([fin, insre], 'fsumrecl', '%s e. RR' % S2)
    s3re = st([fin, prrD], 'fsumrecl', '%s e. RR' % S3)
    efl = st([efre, logr], 'remulcld', '( ( exp ` 1 ) x. %s ) e. RR' % LOG)
    tot = st([s2re, s3re, efl, sle, le3], 'letrd', '%s <_ ( ( exp ` 1 ) x. %s )' % (S2, LOG))
    fin2 = st([e3, tot], 'eqbrtrd', '%s <_ ( ( exp ` 1 ) x. %s )' % (S0, LOG))
    cbs = st([w.s([w.s([w.s([], 'fveq2', '( n = m -> ( phi ` n ) = ( phi ` m ) )')], 'oveq2d',
                       '( n = m -> ( 1 / ( phi ` n ) ) = ( 1 / ( phi ` m ) ) )')], 'cbvsumv',
                  '%s = %s' % (S0, SM))], 'a1i', '%s = %s' % (S0, SM))
    w.qed([st([cbs], 'eqcomd', '%s = %s' % (SM, S0)), fin2], 'eqbrtrd',
          '( %s -> %s <_ ( ( exp ` 1 ) x. %s ) )' % (A, SM, LOG))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['tskey']:
        globals()[f]().run()
