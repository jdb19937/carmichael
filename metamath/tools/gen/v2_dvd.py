"""Sortie v2: sqfdvdsum, the divisor sum of a multiplicative weight over a squarefree modulus."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

GP = '( G ` p )'
SUP = 'G : Prime --> CC'
def PF(X, v='q'): return '{ %s e. Prime | %s || %s }' % (v, v, X)
SD = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || N ) }'
FM = '( n e. %s |-> %s )' % (SD, PF('n', 'p'))
AN = '( N e. NN /\\ %s )' % SUP


def sqfdvdsum():
    w = W('sqfdvdsum',
          'The sum over the squarefree divisors of N of the product of the values of G over the '
          'prime factors is the product of 1 + ( G ` p ) over the prime factors of N.')
    T = PF('N')
    TP = PF('N', 'p')
    SUMT = 'sum_ t e. ~P %s prod_ p e. t %s' % (T, GP)
    SUMD = 'sum_ d e. %s prod_ p e. %s %s' % (SD, PF('d'), GP)
    PRT = 'prod_ p e. %s ( 1 + %s )' % (T, GP)
    def st(hyps, ref, f, ante=AN):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    n = st([], 'simpl', 'N e. NN')
    gf = st([], 'simpr', SUP)
    cbv = w.s([], 'cbvrabv', '%s = %s' % (TP, T))
    cbva = st([cbv], 'a1i', '%s = %s' % (TP, T))
    finp = st([n, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % TP)
    fin = st([cbva, finp], 'eqeltrrd', '%s e. Fin' % T)
    sst = st([w.s([], 'ssrab2', '%s C_ Prime' % T)], 'a1i', '%s C_ Prime' % T)
    # pwprod
    pw = st([fin, st([gf, sst], 'jca', '( %s /\\ %s C_ Prime )' % (SUP, T)), w.inst('pwprod')],
            'syl2anc', '%s = %s' % (SUMT, PRT))
    # sqff1o
    sdef = w.s([], 'eqid', '%s = %s' % (SD, SD))
    fdef = w.s([], 'eqid', '%s = %s' % (FM, FM))
    q1 = w.s([], 'oveq1', '( r = p -> ( r pCnt m ) = ( p pCnt m ) )')
    g1 = w.s([q1], 'cbvmptv', '( r e. Prime |-> ( r pCnt m ) ) = ( p e. Prime |-> ( p pCnt m ) )')
    g2 = w.s([g1], 'mpteq2i',
             '( m e. NN |-> ( r e. Prime |-> ( r pCnt m ) ) ) = ( m e. NN |-> ( p e. Prime |-> ( p pCnt m ) ) )')
    q2 = w.s([], 'oveq2', '( m = n -> ( p pCnt m ) = ( p pCnt n ) )')
    q3 = w.s([q2], 'mpteq2dv', '( m = n -> ( p e. Prime |-> ( p pCnt m ) ) = ( p e. Prime |-> ( p pCnt n ) ) )')
    g3 = w.s([q3], 'cbvmptv',
             '( m e. NN |-> ( p e. Prime |-> ( p pCnt m ) ) ) = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )')
    gdef = w.s([g2, g3], 'eqtri',
               '( m e. NN |-> ( r e. Prime |-> ( r pCnt m ) ) ) = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )')
    f1oi = w.s([sdef, fdef, gdef], 'sqff1o',
               '( N e. NN -> %s : %s -1-1-onto-> ~P %s )' % (FM, SD, TP))
    f1op = st([n, f1oi], 'syl', '%s : %s -1-1-onto-> ~P %s' % (FM, SD, TP))
    pweq = st([cbva], 'pweqd', '~P %s = ~P %s' % (TP, T))
    f1obi = st([pweq], 'f1oeq3d',
               '( %s : %s -1-1-onto-> ~P %s <-> %s : %s -1-1-onto-> ~P %s )' % (FM, SD, TP, FM, SD, T))
    f1o = st([f1obi, f1op], 'mpbid', '%s : %s -1-1-onto-> ~P %s' % (FM, SD, T))
    # ( F ` d ) = { q e. Prime | q || d }
    BD = '( %s /\\ d e. %s )' % (AN, SD)
    din = w.s([], 'simpr', '( %s -> d e. %s )' % (BD, SD))
    breqi = w.s([], 'breq2', '( n = d -> ( p || n <-> p || d ) )')
    subf = w.s([breqi], 'rabbidv', '( n = d -> %s = %s )' % (PF('n', 'p'), PF('d', 'p')))
    prmset = st([w.s([], 'prmex', 'Prime e. _V')], 'a1i', 'Prime e. _V', BD)
    dexeq = w.s([], 'eqid', '%s = %s' % (PF('d', 'p'), PF('d', 'p')))
    dex = st([dexeq, prmset], 'rabexd', '%s e. _V' % PF('d', 'p'), BD)
    fvi = w.s([subf, fdef], 'fvmptg',
              '( ( d e. %s /\\ %s e. _V ) -> ( %s ` d ) = %s )' % (SD, PF('d', 'p'), FM, PF('d', 'p')))
    fvd = st([din, dex, fvi], 'syl2anc', '( %s ` d ) = %s' % (FM, PF('d', 'p')), BD)
    cbvd = st([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
              '%s = %s' % (PF('d', 'p'), PF('d')), BD)
    fval = st([fvd, cbvd], 'eqtrd', '( %s ` d ) = %s' % (FM, PF('d')), BD)
    # closure of the summand on ~P T
    BT = '( %s /\\ t e. ~P %s )' % (AN, T)
    tss = st([w.s([], 'simpr', '( %s -> t e. ~P %s )' % (BT, T)), w.inst('elpwi')], 'syl',
             't C_ %s' % T, BT)
    tfin = st([st([fin], 'adantr', '%s e. Fin' % T, BT), tss], 'ssfid', 't e. Fin', BT)
    tsP = st([tss, st([sst], 'adantr', '%s C_ Prime' % T, BT)], 'sstrd', 't C_ Prime', BT)
    BTP = '( %s /\\ p e. t )' % BT
    pip = st([st([tsP], 'adantr', 't C_ Prime', BTP), w.s([], 'simpr', '( %s -> p e. t )' % BTP)],
             'sseldd', 'p e. Prime', BTP)
    gcl = st([st([st([gf], 'adantr', SUP, BT)], 'adantr', SUP, BTP), pip], 'ffvelcdmd',
             '%s e. CC' % GP, BTP)
    pcl = st([tfin, gcl], 'fprodcl', 'prod_ p e. t %s e. CC' % GP, BT)
    sub2 = w.s([], 'prodeq1', '( t = %s -> prod_ p e. t %s = prod_ p e. %s %s )'
               % (PF('d'), GP, PF('d'), GP))
    sdfin = st([n, w.inst('dvdsfi')], 'syl', '{ x e. NN | x || N } e. Fin')
    simpi0 = w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N )')
    simpi = w.s([simpi0], 'a1i', '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N ) )')
    sdssi = w.s([simpi], 'ss2rabi', '%s C_ { x e. NN | x || N }' % SD)
    sdss = st([sdssi], 'a1i', '%s C_ { x e. NN | x || N }' % SD)
    sdfin2 = st([sdfin, sdss], 'ssfid', '%s e. Fin' % SD)
    e1 = st([sub2, sdfin2, f1o, fval, pcl], 'fsumf1o', '%s = %s' % (SUMT, SUMD))
    w.qed([e1, pw], 'eqtr3d', '( %s -> %s = %s )' % (AN, SUMD, PRT))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['sqfdvdsum']:
        globals()[f]().run()
