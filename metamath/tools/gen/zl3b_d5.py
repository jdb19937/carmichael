"""ZL3b D5-D6: the limit N -> oo (zl3wbd, zl3wlim), zl3wpois, zl3pois.
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_d5.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of, twopi, TP, MP
from zl3b_d2 import cst, reim_cp, cpcl
from zl3b_d3 import pteq
from zl3b_d4 import (chain_eq, hctx, hdec_at, fk_at, d0_mem, hol_expmul, fv_expmul, abs_exp, pow4, SUMH, PAIR, SUMP, EDGA_L, GB, PV, PVb, RR_)

only = sys.argv[1:]
S = STATEMENTS


def tsub(text, m):
    return ' '.join(m.get(t, t) for t in text.split())


if __name__ == '__main__' and (not only or 'zl3wbd' in only):
    w = W('zl3wbd', 'The rectangle identity at ` R_N `: ` i ` times the residue sum differs from the two long-side series by ` O ( 2 ^ ( -N / 4 ) ) `.')
    ph, concl = ante_of(S['zl3wbd'])
    hc_ = w.s([], 'simpl', '( %s -> %s )' % (ph, HCTX))
    hent, krp, hdec = hctx(w, ph, hc_)
    nN = w.s([], 'simpr', '( %s -> N e. NN )' % ph)
    nr = D(w, ph, 'nnred', [nN], 'N e. RR'); nc = D(w, ph, 'nncnd', [nN], 'N e. CC'); nz = D(w, ph, 'nnzd', [nN], 'N e. ZZ')
    kr = D(w, ph, 'rpred', [krp], 'K e. RR'); kc = D(w, ph, 'recnd', [kr], 'K e. CC')
    hf = w.s([w.s([hent, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % ph), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % ph)
    tpr = D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), cst(w, ph, 'pire', '_pi e. RR')], '( 2 x. _pi ) e. RR')
    tpc = D(w, ph, 'recnd', [tpr], '( 2 x. _pi ) e. CC')
    tprp = D(w, ph, 'rpmulcld', [cst(w, ph, '2rp', '2 e. RR+'), cst(w, ph, 'pirp', '_pi e. RR+')], '( 2 x. _pi ) e. RR+')
    ntpr = D(w, ph, 'renegcld', [tpr], '%s e. RR' % TPN); ntpc = D(w, ph, 'recnd', [ntpr], '%s e. CC' % TPN)
    ntp0 = D(w, ph, 'mpbid', [D(w, ph, 'rpgt0d', [tprp], '0 < ( 2 x. _pi )'), D(w, ph, 'lt0neg2d', [tpr], '( 0 < ( 2 x. _pi ) <-> %s < 0 )' % TPN)], '%s < 0' % TPN)
    one = cst(w, ph, '1re', '1 e. RR'); m1 = cst(w, ph, 'neg1rr', '-u 1 e. RR')
    HOLt = lambda f: '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (f, f)
    # ---------------- right edge: EDGA at C = 1, A = -2pi, G = H, P = FK
    mR = {'C': '1', 'A': TPN, 'G': 'H', 'P': FK, 'V': '_V'}
    A1 = '( %s /\\ b e. RR )' % ph
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
    bR = w.s([], 'simpr', '( %s -> b e. RR )' % A1)
    def line_pt(Cv, cr_):
        p = CP(Cv, 'b')
        pc = cpcl(w, A1, Cv, 'b', cr_, bR)
        rp, ip = reim_cp(w, A1, Cv, 'b', cr_, bR)
        return p, pc, rp, ip
    def hb_line(p, pc, rp, ip, Cv, cabs):
        """( A1 -> ( abs ` ( H ` p ) ) <_ ( K x. ( 2 ^c -u ( abs ` b ) ) ) ) given cabs: ( A1 -> ( abs ` Cv ) <_ 1 )"""
        r1 = D(w, A1, 'eqbrtrd', [D(w, A1, 'fveq2d', [rp], '( abs ` ( Re ` %s ) ) = ( abs ` %s )' % (p, Cv)), cabs], '( abs ` ( Re ` %s ) ) <_ 1' % p)
        h = D(w, A1, 'mpd', [r1, w.s([pc, l1(hdec, HDEC), hdec_at(w, A1, None, p)], 'sylc', '( %s -> ( ( abs ` ( Re ` %s ) ) <_ 1 -> ( abs ` ( H ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) ) )' % (A1, p, p, p))],
              '( abs ` ( H ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % (p, p))
        return D(w, A1, 'breqtrd', [h, D(w, A1, 'oveq2d', [D(w, A1, 'oveq2d', [D(w, A1, 'negeqd', [D(w, A1, 'fveq2d', [ip], '( abs ` ( Im ` %s ) ) = ( abs ` b )' % p)], '-u ( abs ` ( Im ` %s ) ) = -u ( abs ` b )' % p)],
                                                                       '( 2 ^c -u ( abs ` ( Im ` %s ) ) ) = ( 2 ^c -u ( abs ` b ) )' % p)], '( K x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) = ( K x. ( 2 ^c -u ( abs ` b ) ) )' % p)],
                 '( abs ` ( H ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` b ) ) )' % p)
    pR, pRc, rpR, ipR = line_pt('1', cst(w, A1, '1re', '1 e. RR'))
    abs1 = D(w, A1, 'eqbrtrd', [cst(w, A1, 'abs1', '( abs ` 1 ) = 1'), D(w, A1, 'leidd', [cst(w, A1, '1re', '1 e. RR')], '1 <_ 1')], '( abs ` 1 ) <_ 1')
    gbR = w.s([hb_line(pR, pRc, rpR, ipR, '1', abs1)], 'ralrimiva', '( %s -> %s )' % (ph, tsub(GB, mR)))
    # FK = H Q / ( 1 - Q ) on Re = 1, Q = exp ( -2pi w )
    pRd0 = w.s([pRc, D(w, A1, 'eqnetrd', [rpR, cst(w, A1, 'ax-1ne0', '1 =/= 0')], '( Re ` %s ) =/= 0' % pR), w.inst('zl3d0')], 'syl2anc', '( %s -> %s e. %s )' % (A1, pR, D0))
    fkv = w.s([pRd0, fk_at(w, pR)], 'syl', '( %s -> ( %s ` %s ) = ( ( H ` %s ) / ( %s - 1 ) ) )' % (A1, FK, pR, pR, E2(pR)))
    tc1, _ = twopi(w, A1)
    tp_p = D(w, A1, 'mulcld', [tc1, pRc], '( ( 2 x. _pi ) x. %s ) e. CC' % pR)
    Ec = w.s([tp_p, w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A1, E2(pR)))
    En = D(w, A1, 'efne0d', [tp_p], '%s =/= 0' % E2(pR))
    Q = '( exp ` ( %s x. %s ) )' % (TPN, pR)
    q1 = D(w, A1, 'fveq2d', [D(w, A1, 'mulneg1d', [tc1, pRc], '( %s x. %s ) = -u ( ( 2 x. _pi ) x. %s )' % (TPN, pR, pR))], '%s = ( exp ` -u ( ( 2 x. _pi ) x. %s ) )' % (Q, pR))
    q2 = w.s([tp_p, w.inst('efneg')], 'syl', '( %s -> ( exp ` -u ( ( 2 x. _pi ) x. %s ) ) = ( 1 / %s ) )' % (A1, pR, E2(pR)))
    qv = D(w, A1, 'eqtrd', [q1, q2], '%s = ( 1 / %s )' % (Q, E2(pR)))
    qc = D(w, A1, 'eqeltrd', [qv, D(w, A1, 'reccld', [Ec, En], '( 1 / %s ) e. CC' % E2(pR))], '%s e. CC' % Q)
    qe = D(w, A1, 'eqtrd', [D(w, A1, 'oveq1d', [qv], '( %s x. %s ) = ( ( 1 / %s ) x. %s )' % (Q, E2(pR), E2(pR), E2(pR))), D(w, A1, 'recid2d', [Ec, En], '( ( 1 / %s ) x. %s ) = 1' % (E2(pR), E2(pR)))],
           '( %s x. %s ) = 1' % (Q, E2(pR)))
    hpc = D(w, A1, 'ffvelcdmd', [l1(hf, 'H : CC --> CC'), pRc], '( H ` %s ) e. CC' % pR)
    one1 = cst(w, A1, 'ax-1cn', '1 e. CC')
    num = D(w, A1, 'eqtrd', [D(w, A1, 'mulassd', [hpc, qc, Ec], '( ( ( H ` %s ) x. %s ) x. %s ) = ( ( H ` %s ) x. ( %s x. %s ) )' % (pR, Q, E2(pR), pR, Q, E2(pR))),
                             D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [qe], '( ( H ` %s ) x. ( %s x. %s ) ) = ( ( H ` %s ) x. 1 )' % (pR, Q, E2(pR), pR)), D(w, A1, 'mulridd', [hpc], '( ( H ` %s ) x. 1 ) = ( H ` %s )' % (pR, pR))],
                               '( ( H ` %s ) x. ( %s x. %s ) ) = ( H ` %s )' % (pR, Q, E2(pR), pR))], '( ( ( H ` %s ) x. %s ) x. %s ) = ( H ` %s )' % (pR, Q, E2(pR), pR))
    den = D(w, A1, 'eqtrd', [D(w, A1, 'subdird', [one1, qc, Ec], '( ( 1 - %s ) x. %s ) = ( ( 1 x. %s ) - ( %s x. %s ) )' % (Q, E2(pR), E2(pR), Q, E2(pR))),
                             D(w, A1, 'oveq12d', [D(w, A1, 'mullidd', [Ec], '( 1 x. %s ) = %s' % (E2(pR), E2(pR))), qe], '( ( 1 x. %s ) - ( %s x. %s ) ) = ( %s - 1 )' % (E2(pR), Q, E2(pR), E2(pR)))],
            '( ( 1 - %s ) x. %s ) = ( %s - 1 )' % (Q, E2(pR), E2(pR)))
    # E - 1 =/= 0 from D0 membership
    def d0ne(pt, ptd0, A_):
        E_ = 'v = %s' % pt
        vsub = D(w, E_, 'neeq1d', [D(w, E_, 'fveq2d', [D(w, E_, 'oveq2d', [w.s([], 'id', '( %s -> %s )' % (E_, E_))], '( %s x. v ) = ( %s x. %s )' % (TP, TP, pt))], '%s = %s' % (E2('v'), E2(pt)))],
                 '( %s =/= 1 <-> %s =/= 1 )' % (E2('v'), E2(pt)))
        el = w.s([ptd0, w.s([vsub], 'elrab', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 1 ) )' % (pt, D0, pt, E2(pt)))], 'sylib', '( %s -> ( %s e. CC /\\ %s =/= 1 ) )' % (A_, pt, E2(pt)))
        return w.s([el, w.inst('simpr')], 'syl', '( %s -> %s =/= 1 )' % (A_, E2(pt)))
    ne1 = d0ne(pR, pRd0, A1)
    em1n = D(w, A1, 'subne0d', [Ec, one1, ne1], '( %s - 1 ) =/= 0' % E2(pR))
    omq = D(w, A1, 'subcld', [one1, qc], '( 1 - %s ) e. CC' % Q)
    omqn = D(w, A1, 'mulne0bad', [omq, Ec, D(w, A1, 'eqnetrd', [den, em1n], '( ( 1 - %s ) x. %s ) =/= 0' % (Q, E2(pR)))], '( 1 - %s ) =/= 0' % Q)
    c5 = D(w, A1, 'divcan5rd', [D(w, A1, 'mulcld', [hpc, qc], '( ( H ` %s ) x. %s ) e. CC' % (pR, Q)), omq, Ec, omqn, En],
           '( ( ( ( H ` %s ) x. %s ) x. %s ) / ( ( 1 - %s ) x. %s ) ) = ( ( ( H ` %s ) x. %s ) / ( 1 - %s ) )' % (pR, Q, E2(pR), Q, E2(pR), pR, Q, Q))
    pvR0 = D(w, A1, 'eqtr3d', [c5, D(w, A1, 'oveq12d', [num, den], '( ( ( ( H ` %s ) x. %s ) x. %s ) / ( ( 1 - %s ) x. %s ) ) = ( ( H ` %s ) / ( %s - 1 ) )' % (pR, Q, E2(pR), Q, E2(pR), pR, E2(pR)))],
             '( ( ( H ` %s ) x. %s ) / ( 1 - %s ) ) = ( ( H ` %s ) / ( %s - 1 ) )' % (pR, Q, Q, pR, E2(pR)))
    pvR = D(w, A1, 'eqtr4d', [fkv, pvR0], '( %s ` %s ) = ( ( ( H ` %s ) x. %s ) / ( 1 - %s ) )' % (FK, pR, pR, Q, Q))
    pvRall = w.s([pvR], 'ralrimiva', '( %s -> %s )' % (ph, tsub(PV, mR)))
    fkv_ = w.s([w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'rabex', '%s e. _V' % D0)], 'mptex', '%s e. _V' % FK)], 'a1i', '( %s -> %s e. _V )' % (ph, FK))
    acR = D(w, ph, 'eqbrtrd', [D(w, ph, 'mulridd', [ntpc], '( %s x. 1 ) = %s' % (TPN, TPN)), ntp0], '( %s x. 1 ) < 0' % TPN)
    EA_R = tsub(EDGA, mR)
    ear = D(w, ph, 'jca', [D(w, ph, 'jca', [D(w, ph, 'jca', [one, ntpr], '( 1 e. RR /\\ %s e. RR )' % TPN), acR], '( ( 1 e. RR /\\ %s e. RR ) /\\ ( %s x. 1 ) < 0 )' % (TPN, TPN)),
                          D(w, ph, 'jca', [D(w, ph, 'jca', [D(w, ph, 'jca', [w.s([hent, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % ph), krp], '( H e. ( CC -cn-> CC ) /\\ K e. RR+ )'), gbR],
                                            '( ( H e. ( CC -cn-> CC ) /\\ K e. RR+ ) /\\ %s )' % tsub(GB, mR)),
                                           D(w, ph, 'jca', [fkv_, pvRall], '( %s e. _V /\\ %s )' % (FK, tsub(PV, mR)))], tsub(EDGA[EDGA.index(' /\\ ( ( ( G') + 4:-2], mR))], EA_R)
    VR = VL(GKE('H', TPN), '1'); SRR = 'sum_ k e. NN %s' % VR
    EB = lambda s_, KK, AC: '( ( ( 8 x. %s ) / ( log ` 2 ) ) x. ( ( 2 ^c -u ( %s / 4 ) ) x. ( ( exp ` %s ) / ( 1 - ( exp ` %s ) ) ) ) )' % (KK, s_, AC, AC)
    edR = w.s([ear, w.inst('zl3edge')], 'syl', '( %s -> ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ %s e. CC ) /\\ A. s e. RR+ ( 1 <_ s -> ( abs ` ( %s - %s ) ) <_ %s ) ) )'
              % (ph, VR, SRR, LT(FK, '1', 's'), SRR, EB('s', 'K', '( %s x. 1 )' % TPN)))
    # ---------------- left edge: C = -1, A = 2pi, G = GL, K = KL, P = FKL
    KL_ = '( K x. ( exp ` ( 2 x. _pi ) ) )'
    mL = {'C': '-u 1', 'A': '( 2 x. _pi )', 'G': GL, 'K': KL_, 'P': FKL, 'V': '_V'}
    glh = hol_expmul(w, ph, 'H', hent, TPN, ntpc, 'w')
    glcn = w.s([glh, w.inst('simpl')], 'syl', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, GL))
    etp = w.s([tpr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( 2 x. _pi ) ) e. RR )' % ph)
    klrp = D(w, ph, 'rpmulcld', [krp, D(w, ph, 'rpefcld', [tpr], '( exp ` ( 2 x. _pi ) ) e. RR+')], '%s e. RR+' % KL_)
    pL, pLc, rpL, ipL = line_pt('-u 1', cst(w, A1, 'neg1rr', '-u 1 e. RR'))
    absm1 = D(w, A1, 'eqbrtrd', [D(w, A1, 'eqtrd', [D(w, A1, 'absnegd', [cst(w, A1, 'ax-1cn', '1 e. CC')], '( abs ` -u 1 ) = ( abs ` 1 )'), cst(w, A1, 'abs1', '( abs ` 1 ) = 1')], '( abs ` -u 1 ) = 1'),
                                 D(w, A1, 'leidd', [cst(w, A1, '1re', '1 e. RR')], '1 <_ 1')], '( abs ` -u 1 ) <_ 1')
    hbL = hb_line(pL, pLc, rpL, ipL, '-u 1', absm1)
    glv = fv_expmul(w, A1, 'H', TPN, 'w', pL, pLc)
    ea = abs_exp(w, A1, TPN, l1(ntpr, '%s e. RR' % TPN), pL, pLc)
    ea2 = D(w, A1, 'eqtrd', [ea, D(w, A1, 'fveq2d', [D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [rpL], '( %s x. ( Re ` %s ) ) = ( %s x. -u 1 )' % (TPN, pL, TPN)),
                                                                        D(w, A1, 'eqtrd', [D(w, A1, 'mul2negd', [l1(tpc, '( 2 x. _pi ) e. CC'), one1], '( %s x. -u 1 ) = ( ( 2 x. _pi ) x. 1 )' % TPN),
                                                                                           D(w, A1, 'mulridd', [l1(tpc, '( 2 x. _pi ) e. CC')], '( ( 2 x. _pi ) x. 1 ) = ( 2 x. _pi )')], '( %s x. -u 1 ) = ( 2 x. _pi )' % TPN)],
                                                          '( %s x. ( Re ` %s ) ) = ( 2 x. _pi )' % (TPN, pL))], '( exp ` ( %s x. ( Re ` %s ) ) ) = ( exp ` ( 2 x. _pi ) )' % (TPN, pL))],
              '( abs ` ( exp ` ( %s x. %s ) ) ) = ( exp ` ( 2 x. _pi ) )' % (TPN, pL))
    hlc = D(w, A1, 'ffvelcdmd', [l1(hf, 'H : CC --> CC'), pLc], '( H ` %s ) e. CC' % pL)
    eLc = D(w, A1, 'efcld', [D(w, A1, 'mulcld', [l1(ntpc, '%s e. CC' % TPN), pLc], '( %s x. %s ) e. CC' % (TPN, pL))], '( exp ` ( %s x. %s ) ) e. CC' % (TPN, pL))
    KB = '( K x. ( 2 ^c -u ( abs ` b ) ) )'
    kbr = D(w, A1, 'remulcld', [l1(kr, 'K e. RR'), D(w, A1, 'rpred', [D(w, A1, 'rpcxpcld', [cst(w, A1, '2rp', '2 e. RR+'), D(w, A1, 'renegcld', [D(w, A1, 'abscld', [D(w, A1, 'recnd', [bR], 'b e. CC')], '( abs ` b ) e. RR')], '-u ( abs ` b ) e. RR')],
                                                                                      '( 2 ^c -u ( abs ` b ) ) e. RR+')], '( 2 ^c -u ( abs ` b ) ) e. RR')], '%s e. RR' % KB)
    glb = D(w, A1, 'eqtrd', [D(w, A1, 'fveq2d', [glv], '( abs ` ( %s ` %s ) ) = ( abs ` ( ( H ` %s ) x. ( exp ` ( %s x. %s ) ) ) )' % (GL, pL, pL, TPN, pL)),
                             D(w, A1, 'eqtrd', [D(w, A1, 'absmuld', [hlc, eLc], '( abs ` ( ( H ` %s ) x. ( exp ` ( %s x. %s ) ) ) ) = ( ( abs ` ( H ` %s ) ) x. ( abs ` ( exp ` ( %s x. %s ) ) ) )' % (pL, TPN, pL, pL, TPN, pL)),
                                                D(w, A1, 'oveq2d', [ea2], '( ( abs ` ( H ` %s ) ) x. ( abs ` ( exp ` ( %s x. %s ) ) ) ) = ( ( abs ` ( H ` %s ) ) x. ( exp ` ( 2 x. _pi ) ) )' % (pL, TPN, pL, pL))],
                               '( abs ` ( ( H ` %s ) x. ( exp ` ( %s x. %s ) ) ) ) = ( ( abs ` ( H ` %s ) ) x. ( exp ` ( 2 x. _pi ) ) )' % (pL, TPN, pL, pL))],
            '( abs ` ( %s ` %s ) ) = ( ( abs ` ( H ` %s ) ) x. ( exp ` ( 2 x. _pi ) ) )' % (GL, pL, pL))
    etp1 = l1(etp, '( exp ` ( 2 x. _pi ) ) e. RR')
    glb2 = D(w, A1, 'lemul1ad', [D(w, A1, 'abscld', [hlc], '( abs ` ( H ` %s ) ) e. RR' % pL), kbr, etp1, D(w, A1, 'ltled', [cst(w, A1, '0re', '0 e. RR'), etp1, w.s([l1(tpr, '( 2 x. _pi ) e. RR'), w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` ( 2 x. _pi ) ) )' % A1)],
                                                                                                                            '0 <_ ( exp ` ( 2 x. _pi ) )'), hbL],
             '( ( abs ` ( H ` %s ) ) x. ( exp ` ( 2 x. _pi ) ) ) <_ ( %s x. ( exp ` ( 2 x. _pi ) ) )' % (pL, KB))
    glb3 = D(w, A1, 'mul32d', [l1(kc, 'K e. CC'), D(w, A1, 'recnd', [D(w, A1, 'rpred', [D(w, A1, 'rpcxpcld', [cst(w, A1, '2rp', '2 e. RR+'), D(w, A1, 'renegcld', [D(w, A1, 'abscld', [D(w, A1, 'recnd', [bR], 'b e. CC')], '( abs ` b ) e. RR')], '-u ( abs ` b ) e. RR')],
                                                                                          '( 2 ^c -u ( abs ` b ) ) e. RR+')], '( 2 ^c -u ( abs ` b ) ) e. RR')], '( 2 ^c -u ( abs ` b ) ) e. CC'), D(w, A1, 'recnd', [etp1], '( exp ` ( 2 x. _pi ) ) e. CC')],
             '( %s x. ( exp ` ( 2 x. _pi ) ) ) = ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (KB, KL_))
    gbL1 = D(w, A1, 'breqtrd', [D(w, A1, 'eqbrtrd', [glb, glb2], '( abs ` ( %s ` %s ) ) <_ ( %s x. ( exp ` ( 2 x. _pi ) ) )' % (GL, pL, KB)), glb3], '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (GL, pL, KL_))
    gbL = w.s([gbL1], 'ralrimiva', '( %s -> %s )' % (ph, tsub(GB, mL)))
    # FKL = GL E / ( 1 - E ) on Re = -1
    pLd0 = w.s([pLc, D(w, A1, 'eqnetrd', [rpL, cst(w, A1, 'neg1ne0', '-u 1 =/= 0')], '( Re ` %s ) =/= 0' % pL), w.inst('zl3d0')], 'syl2anc', '( %s -> %s e. %s )' % (A1, pL, D0))
    Ew = w.s([], 'id', '( w = %s -> w = %s )' % (pL, pL))
    fklsub = D(w, 'w = %s' % pL, 'oveq12d', [D(w, 'w = %s' % pL, 'fveq2d', [Ew], '( H ` w ) = ( H ` %s )' % pL),
                                              D(w, 'w = %s' % pL, 'oveq2d', [D(w, 'w = %s' % pL, 'fveq2d', [D(w, 'w = %s' % pL, 'oveq2d', [Ew], '( %s x. w ) = ( %s x. %s )' % (TP, TP, pL))], '%s = %s' % (E2('w'), E2(pL)))],
                                                '( 1 - %s ) = ( 1 - %s )' % (E2('w'), E2(pL)))], '( ( H ` w ) / ( 1 - %s ) ) = ( ( H ` %s ) / ( 1 - %s ) )' % (E2('w'), pL, E2(pL)))
    fklv = w.s([pLd0, w.s([fklsub, w.s([], 'eqid', '%s = %s' % (FKL, FKL)), w.s([], 'ovex', '( ( H ` %s ) / ( 1 - %s ) ) e. _V' % (pL, E2(pL)))], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = ( ( H ` %s ) / ( 1 - %s ) ) )' % (pL, D0, FKL, pL, pL, E2(pL)))],
               'syl', '( %s -> ( %s ` %s ) = ( ( H ` %s ) / ( 1 - %s ) ) )' % (A1, FKL, pL, pL, E2(pL)))
    ELp = E2(pL); QLn = '( exp ` ( %s x. %s ) )' % (TPN, pL)
    tpp = D(w, A1, 'mulcld', [l1(tpc, '( 2 x. _pi ) e. CC'), pLc], '( ( 2 x. _pi ) x. %s ) e. CC' % pL)
    x1 = D(w, A1, 'fveq2d', [D(w, A1, 'mulneg1d', [l1(tpc, '( 2 x. _pi ) e. CC'), pLc], '( %s x. %s ) = -u ( ( 2 x. _pi ) x. %s )' % (TPN, pL, pL))], '%s = ( exp ` -u ( ( 2 x. _pi ) x. %s ) )' % (QLn, pL))
    x2 = D(w, A1, 'oveq2d', [x1], '( %s x. %s ) = ( %s x. ( exp ` -u ( ( 2 x. _pi ) x. %s ) ) )' % (ELp, QLn, ELp, pL))
    x3 = w.s([tpp, w.inst('efcan')], 'syl', '( %s -> ( %s x. ( exp ` -u ( ( 2 x. _pi ) x. %s ) ) ) = 1 )' % (A1, ELp, pL))
    eq_ = D(w, A1, 'eqtrd', [x2, x3], '( %s x. %s ) = 1' % (ELp, QLn))
    ELc = w.s([tpp, w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A1, ELp))
    gle = D(w, A1, 'eqtrd', [D(w, A1, 'oveq1d', [glv], '( ( %s ` %s ) x. %s ) = ( ( ( H ` %s ) x. %s ) x. %s )' % (GL, pL, ELp, pL, QLn, ELp)),
                             D(w, A1, 'eqtrd', [D(w, A1, 'mulassd', [hlc, eLc, ELc], '( ( ( H ` %s ) x. %s ) x. %s ) = ( ( H ` %s ) x. ( %s x. %s ) )' % (pL, QLn, ELp, pL, QLn, ELp)),
                                                D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [D(w, A1, 'eqtrd', [D(w, A1, 'mulcomd', [eLc, ELc], '( %s x. %s ) = ( %s x. %s )' % (QLn, ELp, ELp, QLn)), eq_], '( %s x. %s ) = 1' % (QLn, ELp))],
                                                                                    '( ( H ` %s ) x. ( %s x. %s ) ) = ( ( H ` %s ) x. 1 )' % (pL, QLn, ELp, pL)), D(w, A1, 'mulridd', [hlc], '( ( H ` %s ) x. 1 ) = ( H ` %s )' % (pL, pL))],
                                                  '( ( H ` %s ) x. ( %s x. %s ) ) = ( H ` %s )' % (pL, QLn, ELp, pL))],
                               '( ( ( H ` %s ) x. %s ) x. %s ) = ( H ` %s )' % (pL, QLn, ELp, pL))],
            '( ( %s ` %s ) x. %s ) = ( H ` %s )' % (GL, pL, ELp, pL))
    # the frozen PV form uses ( exp ` ( A x. p ) ) with A = ( 2 x. _pi ): that is E2(pL)
    pvL0 = D(w, A1, 'oveq1d', [gle], '( ( ( %s ` %s ) x. %s ) / ( 1 - %s ) ) = ( ( H ` %s ) / ( 1 - %s ) )' % (GL, pL, ELp, ELp, pL, ELp))
    pvL = D(w, A1, 'eqtr4d', [fklv, pvL0], '( %s ` %s ) = ( ( ( %s ` %s ) x. %s ) / ( 1 - %s ) )' % (FKL, pL, GL, pL, ELp, ELp))
    pvLall = w.s([pvL], 'ralrimiva', '( %s -> %s )' % (ph, tsub(PV, mL)))
    fklv_ = w.s([w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'rabex', '%s e. _V' % D0)], 'mptex', '%s e. _V' % FKL)], 'a1i', '( %s -> %s e. _V )' % (ph, FKL))
    acL = D(w, ph, 'eqbrtrd', [D(w, ph, 'eqtrd', [D(w, ph, 'mulneg2d', [tpc, cst(w, ph, 'ax-1cn', '1 e. CC')], '( ( 2 x. _pi ) x. -u 1 ) = -u ( ( 2 x. _pi ) x. 1 )'),
                                                  D(w, ph, 'negeqd', [D(w, ph, 'mulridd', [tpc], '( ( 2 x. _pi ) x. 1 ) = ( 2 x. _pi )')], '-u ( ( 2 x. _pi ) x. 1 ) = %s' % TPN)], '( ( 2 x. _pi ) x. -u 1 ) = %s' % TPN), ntp0],
              '( ( 2 x. _pi ) x. -u 1 ) < 0')
    EA_L = tsub(EDGA, mL)
    eal = D(w, ph, 'jca', [D(w, ph, 'jca', [D(w, ph, 'jca', [m1, tpr], '( -u 1 e. RR /\\ ( 2 x. _pi ) e. RR )'), acL], '( ( -u 1 e. RR /\\ ( 2 x. _pi ) e. RR ) /\\ ( ( 2 x. _pi ) x. -u 1 ) < 0 )'),
                          D(w, ph, 'jca', [D(w, ph, 'jca', [D(w, ph, 'jca', [glcn, klrp], '( %s e. ( CC -cn-> CC ) /\\ %s e. RR+ )' % (GL, KL_)), gbL], '( ( %s e. ( CC -cn-> CC ) /\\ %s e. RR+ ) /\\ %s )' % (GL, KL_, tsub(GB, mL))),
                                           D(w, ph, 'jca', [fklv_, pvLall], '( %s e. _V /\\ %s )' % (FKL, tsub(PV, mL)))], tsub(EDGA[EDGA.index(' /\\ ( ( ( G') + 4:-2], mL))], EA_L)
    VLL = VL(GKE(GL, '( 2 x. _pi )'), '-u 1'); SLL = 'sum_ k e. NN %s' % VLL
    edL = w.s([eal, w.inst('zl3edge')], 'syl', '( %s -> ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ %s e. CC ) /\\ A. s e. RR+ ( 1 <_ s -> ( abs ` ( %s - %s ) ) <_ %s ) ) )'
              % (ph, VLL, SLL, LT(FKL, '-u 1', 's'), SLL, EB('s', KL_, '( ( 2 x. _pi ) x. -u 1 )')))
    edR1 = w.s([edR, w.inst('simpl')], 'syl', '( %s -> ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ %s e. CC ) )' % (ph, VR, SRR))
    edL1 = w.s([edL, w.inst('simpl')], 'syl', '( %s -> ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ %s e. CC ) )' % (ph, VLL, SLL))
    convs = D(w, ph, 'jca', [w.s([edR1, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (ph, VR)),
                             w.s([edL1, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (ph, VLL))],
              '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (VR, VLL))
    src = w.s([edR1, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (ph, SRR))
    slc = w.s([edL1, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (ph, SLL))
    # ---------------- the rectangle R_N
    a = '( N + ( 1 / 2 ) )'; na = '-u %s' % a
    hr = cst(w, ph, 'halfre', '( 1 / 2 ) e. RR')
    ar = D(w, ph, 'readdcld', [nr, hr], '%s e. RR' % a); nar = D(w, ph, 'renegcld', [ar], '%s e. RR' % na)
    ac_ = D(w, ph, 'recnd', [ar], '%s e. CC' % a)
    n1 = D(w, ph, 'nnge1d', [nN], '1 <_ N')
    na_ = D(w, ph, 'ltaddrpd', [nr, D(w, ph, 'elrpd', [hr, cst(w, ph, 'halfgt0', '0 < ( 1 / 2 )')], '( 1 / 2 ) e. RR+')], 'N < %s' % a)
    a1 = D(w, ph, 'letrd', [one, nr, ar, n1, D(w, ph, 'ltled', [nr, ar, na_], 'N <_ %s' % a)], '1 <_ %s' % a)
    arp = D(w, ph, 'elrpd', [ar, D(w, ph, 'ltletrd', [cst(w, ph, '0re', '0 e. RR'), one, ar, cst(w, ph, '0lt1', '0 < 1'), a1], '0 < %s' % a)], '%s e. RR+' % a)
    rs = w.s([D(w, ph, 'jca', [hent, D(w, ph, 'nnnn0d', [nN], 'N e. NN0')], '( %s /\\ N e. NN0 )' % HENT), w.inst('zl3rsum')], 'syl',
             '( %s -> %s = ( _i x. %s ) )' % (ph, RI(FK, *RN('N')), SUMH('-u N', 'N')))
    fkvv = w.s([w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'rabex', '%s e. _V' % D0)], 'mptex', '%s e. _V' % FK)], 'a1i', '( %s -> %s e. _V )' % (ph, FK))
    BOT = LI(FK, CP('-u 1', na), CP('1', na)); RGT = LI(FK, CP('1', na), CP('1', a)); TOP = LI(FK, CP('1', a), CP('-u 1', a)); LFT = LI(FK, CP('-u 1', a), CP('-u 1', na))
    rv = w.s([w.s([D(w, ph, 'jca', [m1, one], '( -u 1 e. RR /\\ 1 e. RR )'), D(w, ph, 'jca', [nar, ar], '( %s e. RR /\\ %s e. RR )' % (na, a)), fkvv], '3jca',
                  '( %s -> ( ( -u 1 e. RR /\\ 1 e. RR ) /\\ ( %s e. RR /\\ %s e. RR ) /\\ %s e. _V ) )' % (ph, na, a, FK)), w.inst('zl3rval')], 'syl',
             '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (ph, RI(FK, CP('-u 1', na), CP('1', a)), BOT, RGT, TOP, LFT))
    # ---------------- the left side through zl3lrn
    LA, LB = CP('-u 1', na), CP('-u 1', a)
    lac = cpcl(w, ph, '-u 1', na, m1, nar); lbc = cpcl(w, ph, '-u 1', a, m1, ar)
    rLA, iLA = reim_cp(w, ph, '-u 1', na, m1, nar); rLB, iLB = reim_cp(w, ph, '-u 1', a, m1, ar)
    nale = D(w, ph, 'ltled', [nar, ar, D(w, ph, 'lttrd', [nar, cst(w, ph, '0re', '0 e. RR'), ar, D(w, ph, 'mpbid', [D(w, ph, 'rpgt0d', [arp], '0 < %s' % a), D(w, ph, 'lt0neg2d', [ar], '( 0 < %s <-> %s < 0 )' % (a, na))], '%s < 0' % na),
                                                                                   D(w, ph, 'rpgt0d', [arp], '0 < %s' % a)], '%s < %s' % (na, a))], '%s <_ %s' % (na, a))
    GEO = '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (LA, LB, LA, LB)
    geo = D(w, ph, 'jca', [D(w, ph, '3brtr4d', [D(w, ph, 'leidd', [m1], '-u 1 <_ -u 1'), rLA, rLB], '( Re ` %s ) <_ ( Re ` %s )' % (LA, LB)), D(w, ph, '3brtr4d', [nale, iLA, iLB], '( Im ` %s ) <_ ( Im ` %s )' % (LA, LB))], GEO)
    abl = D(w, ph, 'jca', [lac, lbc], '( %s e. CC /\\ %s e. CC )' % (LA, LB))
    abg = D(w, ph, 'jca', [abl, geo], '( ( %s e. CC /\\ %s e. CC ) /\\ %s )' % (LA, LB, GEO))
    cvx = w.s([abl, D(w, ph, 'jca', [w.s([abg, w.inst('crectcnr1')], 'syl', '( %s -> %s e. ( %s crect %s ) )' % (ph, LA, LA, LB)), w.s([abg, w.inst('crectcnr3')], 'syl', '( %s -> %s e. ( %s crect %s ) )' % (ph, LB, LA, LB))],
                                      '( %s e. ( %s crect %s ) /\\ %s e. ( %s crect %s ) )' % (LA, LA, LB, LB, LA, LB)), w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( %s crect %s ) )' % (ph, LA, LB, LA, LB))
    A2 = '( %s /\\ b e. ( %s cseg %s ) )' % (ph, LA, LB)
    l2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    bcr = D(w, A2, 'sseldd', [l2(cvx, '( %s cseg %s ) C_ ( %s crect %s )' % (LA, LB, LA, LB)), w.s([], 'simpr', '( %s -> b e. ( %s cseg %s ) )' % (A2, LA, LB))], 'b e. ( %s crect %s )' % (LA, LB))
    ec = w.s([l2(abl, '( %s e. CC /\\ %s e. CC )' % (LA, LB)), w.inst('elcrect')], 'syl',
             '( %s -> ( b e. ( %s crect %s ) <-> ( b e. CC /\\ ( Re ` b ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` b ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A2, LA, LB, LA, LB, LA, LB))
    e3 = D(w, A2, 'mpbid', [bcr, ec], '( b e. CC /\\ ( Re ` b ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` b ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (LA, LB, LA, LB))
    bc_ = w.s([e3, w.inst('simp1')], 'syl', '( %s -> b e. CC )' % A2)
    rbI = D(w, A2, 'eleqtrd', [w.s([e3, w.inst('simp2')], 'syl', '( %s -> ( Re ` b ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) )' % (A2, LA, LB)),
                               D(w, A2, 'oveq12d', [l2(rLA, '( Re ` %s ) = -u 1' % LA), l2(rLB, '( Re ` %s ) = -u 1' % LB)], '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( -u 1 [,] -u 1 )' % (LA, LB))], '( Re ` b ) e. ( -u 1 [,] -u 1 )')
    m1_2 = cst(w, A2, 'neg1rr', '-u 1 e. RR')
    rb3 = D(w, A2, 'mpbid', [rbI, w.s([m1_2, m1_2, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` b ) e. ( -u 1 [,] -u 1 ) <-> ( ( Re ` b ) e. RR /\\ -u 1 <_ ( Re ` b ) /\\ ( Re ` b ) <_ -u 1 ) ) )' % A2)],
            '( ( Re ` b ) e. RR /\\ -u 1 <_ ( Re ` b ) /\\ ( Re ` b ) <_ -u 1 )')
    rbe = D(w, A2, 'mpbird', [D(w, A2, 'jca', [w.s([rb3, w.inst('simp3')], 'syl', '( %s -> ( Re ` b ) <_ -u 1 )' % A2), w.s([rb3, w.inst('simp2')], 'syl', '( %s -> -u 1 <_ ( Re ` b ) )' % A2)],
                                    '( ( Re ` b ) <_ -u 1 /\\ -u 1 <_ ( Re ` b ) )'), D(w, A2, 'letri3d', [w.s([rb3, w.inst('simp1')], 'syl', '( %s -> ( Re ` b ) e. RR )' % A2), m1_2],
                                                                                         '( ( Re ` b ) = -u 1 <-> ( ( Re ` b ) <_ -u 1 /\\ -u 1 <_ ( Re ` b ) ) )')], '( Re ` b ) = -u 1')
    bd0 = w.s([bc_, D(w, A2, 'eqnetrd', [rbe, cst(w, A2, 'neg1ne0', '-u 1 =/= 0')], '( Re ` b ) =/= 0'), w.inst('zl3d0')], 'syl2anc', '( %s -> b e. %s )' % (A2, D0))
    fkb = w.s([bd0, fk_at(w, 'b')], 'syl', '( %s -> ( %s ` b ) = ( ( H ` b ) / ( %s - 1 ) ) )' % (A2, FK, E2('b')))
    Eb = 'w = b'
    ebb = w.s([], 'id', '( w = b -> w = b )')
    fklsubb = D(w, Eb, 'oveq12d', [D(w, Eb, 'fveq2d', [ebb], '( H ` w ) = ( H ` b )'), D(w, Eb, 'oveq2d', [D(w, Eb, 'fveq2d', [D(w, Eb, 'oveq2d', [ebb], '( %s x. w ) = ( %s x. b )' % (TP, TP))], '%s = %s' % (E2('w'), E2('b')))],
                                                                                                          '( 1 - %s ) = ( 1 - %s )' % (E2('w'), E2('b')))], '( ( H ` w ) / ( 1 - %s ) ) = ( ( H ` b ) / ( 1 - %s ) )' % (E2('w'), E2('b')))
    fklb = w.s([bd0, w.s([fklsubb, w.s([], 'eqid', '%s = %s' % (FKL, FKL)), w.s([], 'ovex', '( ( H ` b ) / ( 1 - %s ) ) e. _V' % E2('b'))], 'fvmpt', '( b e. %s -> ( %s ` b ) = ( ( H ` b ) / ( 1 - %s ) ) )' % (D0, FKL, E2('b')))],
               'syl', '( %s -> ( %s ` b ) = ( ( H ` b ) / ( 1 - %s ) ) )' % (A2, FKL, E2('b')))
    tcb, _ = twopi(w, A2)
    ebc = w.s([D(w, A2, 'mulcld', [tcb, bc_], '( %s x. b ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A2, E2('b')))
    hbc = D(w, A2, 'ffvelcdmd', [l2(hf, 'H : CC --> CC'), bc_], '( H ` b ) e. CC')
    ne1b = d0ne('b', bd0, A2)
    emb = D(w, A2, 'subcld', [ebc, cst(w, A2, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2('b'))
    embn = D(w, A2, 'subne0d', [ebc, cst(w, A2, 'ax-1cn', '1 e. CC'), ne1b], '( %s - 1 ) =/= 0' % E2('b'))
    ng = D(w, A2, 'eqtrd', [D(w, A2, 'negeqd', [fkb], '-u ( %s ` b ) = -u ( ( H ` b ) / ( %s - 1 ) )' % (FK, E2('b'))),
                            D(w, A2, 'eqtrd', [D(w, A2, 'divneg2d', [hbc, emb, embn], '-u ( ( H ` b ) / ( %s - 1 ) ) = ( ( H ` b ) / -u ( %s - 1 ) )' % (E2('b'), E2('b'))),
                                               D(w, A2, 'oveq2d', [D(w, A2, 'negsubdi2d', [ebc, cst(w, A2, 'ax-1cn', '1 e. CC')], '-u ( %s - 1 ) = ( 1 - %s )' % (E2('b'), E2('b')))],
                                                 '( ( H ` b ) / -u ( %s - 1 ) ) = ( ( H ` b ) / ( 1 - %s ) )' % (E2('b'), E2('b')))],
                              '-u ( ( H ` b ) / ( %s - 1 ) ) = ( ( H ` b ) / ( 1 - %s ) )' % (E2('b'), E2('b')))], '-u ( %s ` b ) = ( ( H ` b ) / ( 1 - %s ) )' % (FK, E2('b')))
    kl = D(w, A2, 'eqtr4d', [fklb, ng], '( %s ` b ) = -u ( %s ` b )' % (FKL, FK))
    klall = w.s([kl], 'ralrimiva', '( %s -> A. b e. ( %s cseg %s ) ( %s ` b ) = -u ( %s ` b ) )' % (ph, LA, LB, FKL, FK))
    sd0 = w.s([w.s([bd0], 'ex', '( %s -> ( b e. ( %s cseg %s ) -> b e. %s ) )' % (ph, LA, LB, D0))], 'ssrdv', '( %s -> ( %s cseg %s ) C_ %s )' % (ph, LA, LB, D0))
    fkcn = w.s([hent, w.inst('zl3fkcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ph, FK, D0))
    lrn = w.s([D(w, ph, 'jca', [abl, D(w, ph, 'jca', [fkcn, sd0], '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (FK, D0, LA, LB, D0))],
                    '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (LA, LB, FK, D0, LA, LB, D0)),
               D(w, ph, 'jca', [fklv_, klall], '( %s e. _V /\\ A. b e. ( %s cseg %s ) ( %s ` b ) = -u ( %s ` b ) )' % (FKL, LA, LB, FKL, FK)), w.inst('zl3lrn')], 'syl2anc',
              '( %s -> %s = ( %s lint <. %s , %s >. ) )' % (ph, LFT, FKL, LA, LB))
    LFT2 = LT(FKL, '-u 1', a)
    assert '( %s lint <. %s , %s >. )' % (FKL, LA, LB) == LFT2
    exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'zl3b_d5b.py')).read())


# ---------------------------------------------------------------- zl3wlim
if __name__ == '__main__' and (not only or 'zl3wlim' in only):
    w = W('zl3wlim', 'Poisson summation in the rotated plane, first form: ` i ` times the symmetric sum of ` H ( i n ) ` equals the sum of the two long-side series.')
    ph = HCTX
    VR = VL(GKE('H', TPN), '1'); VLL = VL(GKE(GL, '( 2 x. _pi )'), '-u 1')
    SRR = 'sum_ k e. NN %s' % VR; SLL = 'sum_ k e. NN %s' % VLL
    X = '( %s + %s )' % (SRR, SLL)
    CONV = '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (VR, VLL)
    BND = lambda N_: '( abs ` ( ( _i x. sum_ n e. ( -u %s ... %s ) ( H ` ( _i x. n ) ) ) - %s ) ) <_ ( %s x. ( ( 2 ^c -u ( 1 / 4 ) ) ^ %s ) )' % (N_, N_, X, CT, N_)
    w1 = w.s([w.s([], 'id', '( %s -> %s )' % (ph, ph)), cst(w, ph, '1nn', '1 e. NN'), w.inst('zl3wbd')], 'syl2anc', '( %s -> ( ( %s /\\ %s e. CC ) /\\ %s ) )' % (ph, CONV, X, BND('1')))
    conv = w.s([w.s([w1, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ %s e. CC ) )' % (ph, CONV, X)), w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, CONV))
    xc = w.s([w.s([w1, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ %s e. CC ) )' % (ph, CONV, X)), w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (ph, X))
    hent = w.s([], 'simpl', '( %s -> %s )' % (ph, HENT))
    hf = w.s([w.s([hent, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % ph), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % ph)
    ic = cst(w, ph, 'ax-icn', '_i e. CC'); inz = cst(w, ph, 'ine0', '_i =/= 0')
    H0 = '( H ` ( _i x. 0 ) )'
    h0c = D(w, ph, 'ffvelcdmd', [hf, D(w, ph, 'mulcld', [ic, cst(w, ph, '0cn', '0 e. CC')], '( _i x. 0 ) e. CC')], '%s e. CC' % H0)
    XI = '( %s / _i )' % X
    xic = D(w, ph, 'divcld', [xc, ic, inz], '%s e. CC' % XI)
    Lp = '( %s - %s )' % (XI, H0)
    lpc = D(w, ph, 'subcld', [xic, h0c], '%s e. CC' % Lp)
    PAm = '( ( H ` ( _i x. m ) ) + ( H ` ( _i x. -u m ) ) )'
    PF = '( m e. NN |-> %s )' % PAm
    SQ = 'seq 1 ( + , %s )' % PF
    R4 = '( 2 ^c -u ( 1 / 4 ) )'
    # per index j
    A1 = '( %s /\\ j e. NN )' % ph
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
    jN = w.s([], 'simpr', '( %s -> j e. NN )' % A1)
    bj = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ph)), jN, w.inst('zl3wbd')], 'syl2anc', '( %s -> ( ( %s /\\ %s e. CC ) /\\ %s ) )' % (A1, CONV, X, BND('j')))
    bj2 = w.s([bj, w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, BND('j')))
    fz = w.s([l1(hf, 'H : CC --> CC'), D(w, A1, 'nnnn0d', [jN], 'j e. NN0'), w.inst('zl3fzs')], 'syl2anc',
             '( %s -> %s = ( %s + %s ) )' % (A1, SUMH('-u j', 'j'), H0, SUMP('j')))
    # the partial sum of the pairs
    A2 = '( %s /\\ n e. ( 1 ... j ) )' % A1
    nz2 = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... j ) )' % A2), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % A2)
    nN2 = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... j ) )' % A2), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % A2)
    nc2 = D(w, A2, 'zcnd', [nz2], 'n e. CC')
    hf2 = w.s([l1(hf, 'H : CC --> CC')], 'adantr', '( %s -> H : CC --> CC )' % A2)
    ic2 = cst(w, A2, 'ax-icn', '_i e. CC')
    pc2 = D(w, A2, 'addcld', [D(w, A2, 'ffvelcdmd', [hf2, D(w, A2, 'mulcld', [ic2, nc2], '( _i x. n ) e. CC')], '( H ` ( _i x. n ) ) e. CC'),
                              D(w, A2, 'ffvelcdmd', [hf2, D(w, A2, 'mulcld', [ic2, D(w, A2, 'negcld', [nc2], '-u n e. CC')], '( _i x. -u n ) e. CC')], '( H ` ( _i x. -u n ) ) e. CC')], '%s e. CC' % PAIR)
    Emn = 'm = n'
    emn = w.s([], 'id', '( m = n -> m = n )')
    psub = D(w, Emn, 'oveq12d', [D(w, Emn, 'fveq2d', [D(w, Emn, 'oveq2d', [emn], '( _i x. m ) = ( _i x. n )')], '( H ` ( _i x. m ) ) = ( H ` ( _i x. n ) )'),
                                 D(w, Emn, 'fveq2d', [D(w, Emn, 'oveq2d', [D(w, Emn, 'negeqd', [emn], '-u m = -u n')], '( _i x. -u m ) = ( _i x. -u n )')], '( H ` ( _i x. -u m ) ) = ( H ` ( _i x. -u n ) )')],
           '%s = %s' % (PAm, PAIR))
    pfv = w.s([w.s([psub, w.s([], 'eqid', '%s = %s' % (PF, PF)), w.s([], 'ovex', '%s e. _V' % PAIR)], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (PF, PAIR))], 'x', 'x') if False else \
        w.s([psub, w.s([], 'eqid', '%s = %s' % (PF, PF)), w.s([], 'ovex', '%s e. _V' % PAIR)], 'fvmpt', '( n e. NN -> ( %s ` n ) = %s )' % (PF, PAIR))
    pfv2 = w.s([nN2, pfv], 'syl', '( %s -> ( %s ` n ) = %s )' % (A2, PF, PAIR))
    juz = D(w, A1, 'eleqtrd', [jN, cst(w, A1, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'j e. ( ZZ>= ` 1 )')
    fs = w.s([pfv2, juz, pc2], 'fsumser', '( %s -> %s = ( %s ` j ) )' % (A1, SUMP('j'), SQ))
    sqc = D(w, A1, 'eqeltrrd', [fs, w.s([w.s([], 'fzfid', '( %s -> ( 1 ... j ) e. Fin )' % A1), pc2], 'fsumcl', '( %s -> %s e. CC )' % (A1, SUMP('j')))], '( %s ` j ) e. CC' % SQ)
    # | S ( j ) - L' | = | i Sum - X |
    SUMJ = SUMH('-u j', 'j')
    sjc = D(w, A1, 'eqeltrrd' if False else 'eqeltrd', [fz, D(w, A1, 'addcld', [l1(h0c, '%s e. CC' % H0), w.s([w.s([], 'fzfid', '( %s -> ( 1 ... j ) e. Fin )' % A1), pc2], 'fsumcl', '( %s -> %s e. CC )' % (A1, SUMP('j')))],
                                                         '( %s + %s ) e. CC' % (H0, SUMP('j')))], '%s e. CC' % SUMJ)
    ic1 = cst(w, A1, 'ax-icn', '_i e. CC'); inz1 = cst(w, A1, 'ine0', '_i =/= 0')
    xc1 = l1(xc, '%s e. CC' % X)
    e1 = D(w, A1, 'eqtrd', [D(w, A1, 'oveq1d', [D(w, A1, 'eqcomd', [fs], '( %s ` j ) = %s' % (SQ, SUMP('j')))], '( ( %s ` j ) - %s ) = ( %s - %s )' % (SQ, Lp, SUMP('j'), Lp)),
                            D(w, A1, 'subsub3d', [w.s([w.s([], 'fzfid', '( %s -> ( 1 ... j ) e. Fin )' % A1), pc2], 'fsumcl', '( %s -> %s e. CC )' % (A1, SUMP('j'))), l1(xic, '%s e. CC' % XI), l1(h0c, '%s e. CC' % H0)],
                              '( %s - %s ) = ( ( %s + %s ) - %s )' % (SUMP('j'), Lp, SUMP('j'), H0, XI))], '( ( %s ` j ) - %s ) = ( ( %s + %s ) - %s )' % (SQ, Lp, SUMP('j'), H0, XI))
    e2 = D(w, A1, 'oveq1d', [D(w, A1, 'eqtr4d', [D(w, A1, 'addcomd', [w.s([w.s([], 'fzfid', '( %s -> ( 1 ... j ) e. Fin )' % A1), pc2], 'fsumcl', '( %s -> %s e. CC )' % (A1, SUMP('j'))), l1(h0c, '%s e. CC' % H0)],
                                                   '( %s + %s ) = ( %s + %s )' % (SUMP('j'), H0, H0, SUMP('j'))), fz], '( %s + %s ) = %s' % (SUMP('j'), H0, SUMJ))], '( ( %s + %s ) - %s ) = ( %s - %s )' % (SUMP('j'), H0, XI, SUMJ, XI))
    IS = '( _i x. %s )' % SUMJ
    e3 = D(w, A1, 'eqtr4d', [D(w, A1, 'eqidd', [], '( %s - %s ) = ( %s - %s )' % (SUMJ, XI, SUMJ, XI)),
                             D(w, A1, 'eqtrd', [D(w, A1, 'divsubdird', [D(w, A1, 'mulcld', [ic1, sjc], '%s e. CC' % IS), xc1, ic1, inz1], '( ( %s - %s ) / _i ) = ( ( %s / _i ) - %s )' % (IS, X, IS, XI)),
                                                D(w, A1, 'oveq1d', [D(w, A1, 'eqtrd', [D(w, A1, 'mulcomd', [ic1, sjc], '%s = ( %s x. _i )' % (IS, SUMJ)) if False else
                                                                                       D(w, A1, 'divcan3d', [sjc, ic1, inz1], '( %s / _i ) = %s' % (IS, SUMJ)), D(w, A1, 'eqidd', [], '%s = %s' % (SUMJ, SUMJ))], '( %s / _i ) = %s' % (IS, SUMJ))],
                                                  '( ( %s / _i ) - %s ) = ( %s - %s )' % (IS, XI, SUMJ, XI))], '( ( %s - %s ) / _i ) = ( %s - %s )' % (IS, X, SUMJ, XI))],
           '( %s - %s ) = ( ( %s - %s ) / _i )' % (SUMJ, XI, IS, X))
    dd = D(w, A1, 'subcld', [D(w, A1, 'mulcld', [ic1, sjc], '%s e. CC' % IS), xc1], '( %s - %s ) e. CC' % (IS, X))
    e4 = D(w, A1, 'eqtrd', [D(w, A1, 'fveq2d', [e3], '( abs ` ( %s - %s ) ) = ( abs ` ( ( %s - %s ) / _i ) )' % (SUMJ, XI, IS, X)),
                            D(w, A1, 'eqtrd', [D(w, A1, 'absdivd', [dd, ic1, inz1], '( abs ` ( ( %s - %s ) / _i ) ) = ( ( abs ` ( %s - %s ) ) / ( abs ` _i ) )' % (IS, X, IS, X)),
                                               D(w, A1, 'eqtrd', [D(w, A1, 'oveq2d', [cst(w, A1, 'absi', '( abs ` _i ) = 1')], '( ( abs ` ( %s - %s ) ) / ( abs ` _i ) ) = ( ( abs ` ( %s - %s ) ) / 1 )' % (IS, X, IS, X)),
                                                                  D(w, A1, 'div1d', [D(w, A1, 'recnd', [D(w, A1, 'abscld', [dd], '( abs ` ( %s - %s ) ) e. RR' % (IS, X))], '( abs ` ( %s - %s ) ) e. CC' % (IS, X))],
                                                                    '( ( abs ` ( %s - %s ) ) / 1 ) = ( abs ` ( %s - %s ) )' % (IS, X, IS, X))], '( ( abs ` ( %s - %s ) ) / ( abs ` _i ) ) = ( abs ` ( %s - %s ) )' % (IS, X, IS, X))],
                              '( abs ` ( ( %s - %s ) / _i ) ) = ( abs ` ( %s - %s ) )' % (IS, X, IS, X))], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (SUMJ, XI, IS, X))
    e5 = D(w, A1, 'eqtrd', [D(w, A1, 'fveq2d', [D(w, A1, 'eqtrd', [e1, e2], '( ( %s ` j ) - %s ) = ( %s - %s )' % (SQ, Lp, SUMJ, XI))], '( abs ` ( ( %s ` j ) - %s ) ) = ( abs ` ( %s - %s ) )' % (SQ, Lp, SUMJ, XI)), e4],
           '( abs ` ( ( %s ` j ) - %s ) ) = ( abs ` ( %s - %s ) )' % (SQ, Lp, IS, X))
    bnd = D(w, A1, 'eqbrtrd', [e5, bj2], '( abs ` ( ( %s ` j ) - %s ) ) <_ ( %s x. ( %s ^ j ) )' % (SQ, Lp, CT, R4))
    body = lambda v: '( ( %s ` %s ) e. CC /\\ ( abs ` ( ( %s ` %s ) - %s ) ) <_ ( %s x. ( %s ^ %s ) ) )' % (SQ, v, SQ, v, Lp, CT, R4, v)
    allj = w.s([D(w, A1, 'jca', [sqc, bnd], body('j'))], 'ralrimiva', '( %s -> A. j e. NN %s )' % (ph, body('j')))
    Ejn = 'j = n'
    ejn = w.s([], 'id', '( j = n -> j = n )')
    sqj = D(w, Ejn, 'fveq2d', [ejn], '( %s ` j ) = ( %s ` n )' % (SQ, SQ))
    bjn = D(w, Ejn, 'anbi12d', [D(w, Ejn, 'eleq1d', [sqj], '( ( %s ` j ) e. CC <-> ( %s ` n ) e. CC )' % (SQ, SQ)),
                                D(w, Ejn, 'breq12d', [D(w, Ejn, 'fveq2d', [D(w, Ejn, 'oveq1d', [sqj], '( ( %s ` j ) - %s ) = ( ( %s ` n ) - %s )' % (SQ, Lp, SQ, Lp))], '( abs ` ( ( %s ` j ) - %s ) ) = ( abs ` ( ( %s ` n ) - %s ) )' % (SQ, Lp, SQ, Lp)),
                                                      D(w, Ejn, 'oveq2d', [D(w, Ejn, 'oveq2d', [ejn], '( %s ^ j ) = ( %s ^ n )' % (R4, R4))], '( %s x. ( %s ^ j ) ) = ( %s x. ( %s ^ n ) )' % (CT, R4, CT, R4))],
                                  '( ( abs ` ( ( %s ` j ) - %s ) ) <_ ( %s x. ( %s ^ j ) ) <-> ( abs ` ( ( %s ` n ) - %s ) ) <_ ( %s x. ( %s ^ n ) ) )' % (SQ, Lp, CT, R4, SQ, Lp, CT, R4))],
              '( %s <-> %s )' % (body('j'), body('n')))
    alln = D(w, ph, 'mpbid', [allj, w.s([w.s([bjn], 'cbvralvw', '( A. j e. NN %s <-> A. n e. NN %s )' % (body('j'), body('n')))], 'a1i', '( %s -> ( A. j e. NN %s <-> A. n e. NN %s ) )' % (ph, body('j'), body('n')))],
             'A. n e. NN %s' % body('n'))
    # constants
    kr = D(w, ph, 'rpred', [w.s([w.s([], 'simpr', '( %s -> ( K e. RR+ /\\ %s ) )' % (ph, HDEC)), w.inst('simpl')], 'syl', '( %s -> K e. RR+ )' % ph)], 'K e. RR')
    from zl3b_d5 import tsub as _t
    r4rp = D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), cst(w, ph, '4rp', '4 e. RR+')], '( 1 / 4 ) e. RR')], '-u ( 1 / 4 ) e. RR')], '%s e. RR+' % R4)
    r4r = D(w, ph, 'rpred', [r4rp], '%s e. RR' % R4)
    r40 = D(w, ph, 'rpge0d', [r4rp], '0 <_ %s' % R4)
    q4 = D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), cst(w, ph, '4rp', '4 e. RR+')], '( 1 / 4 ) e. RR')
    q4p = D(w, ph, 'divgt0d' if False else 'elrpd', [q4, D(w, ph, 'divgt0d', [cst(w, ph, '1re', '1 e. RR'), cst(w, ph, '4re', '4 e. RR'), cst(w, ph, '0lt1', '0 < 1'), cst(w, ph, '4pos', '0 < 4')], '0 < ( 1 / 4 )')], '( 1 / 4 ) e. RR+')
    nq = D(w, ph, 'mpbid', [D(w, ph, 'rpgt0d', [q4p], '0 < ( 1 / 4 )'), D(w, ph, 'lt0neg2d', [q4], '( 0 < ( 1 / 4 ) <-> -u ( 1 / 4 ) < 0 )')], '-u ( 1 / 4 ) < 0')
    r41 = D(w, ph, 'breqtrd', [D(w, ph, 'mpbid', [nq, w.s([w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2')], 'jca', '( %s -> ( 2 e. RR /\\ 1 < 2 ) )' % ph),
                                                            D(w, ph, 'jca', [D(w, ph, 'renegcld', [q4], '-u ( 1 / 4 ) e. RR'), cst(w, ph, '0re', '0 e. RR')], '( -u ( 1 / 4 ) e. RR /\\ 0 e. RR )'), w.inst('cxplt')], 'syl2anc',
                                                           '( %s -> ( -u ( 1 / 4 ) < 0 <-> %s < ( 2 ^c 0 ) ) )' % (ph, R4))], '%s < ( 2 ^c 0 )' % R4),
                               w.s([cst(w, ph, '2cn', '2 e. CC'), w.inst('cxp0')], 'syl', '( %s -> ( 2 ^c 0 ) = 1 )' % ph)], '%s < 1' % R4)
    # CT e. RR: from the bound at 1 it is real
    ctr = D(w, ph, 'readdcld', [D(w, ph, 'remulcld', [cst(w, ph, '4re', '4 e. RR'), kr], '( 4 x. K ) e. RR'), cst(w, ph, 'x', 'x') if False else None], 'x') if False else None
    import zl3blib as _ZB
    KL_ = '( K x. ( exp ` ( 2 x. _pi ) ) )'
    def cterm(KK, AC, kkr, acr):
        X_ = '( ( 8 x. %s ) / ( log ` 2 ) )' % KK; RHO = '( ( exp ` %s ) / ( 1 - ( exp ` %s ) ) )' % (AC, AC)
        l2rp = w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)
        xr = D(w, ph, 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), kkr], '( 8 x. %s ) e. RR' % KK), l2rp], '%s e. RR' % X_)
        rr_ = w.s([acr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` %s ) e. RR )' % (ph, AC))
        # 1 - exp AC =/= 0 : exp AC < 1 since AC < 0
        return xr, rr_, X_, RHO
    tpr = D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), cst(w, ph, 'pire', '_pi e. RR')], '( 2 x. _pi ) e. RR')
    ntpr = D(w, ph, 'renegcld', [tpr], '%s e. RR' % TPN)
    acR = D(w, ph, 'remulcld', [ntpr, cst(w, ph, '1re', '1 e. RR')], '( %s x. 1 ) e. RR' % TPN)
    acL = D(w, ph, 'remulcld', [tpr, cst(w, ph, 'neg1rr', '-u 1 e. RR')], '( ( 2 x. _pi ) x. -u 1 ) e. RR')
    klr = D(w, ph, 'remulcld', [kr, w.s([tpr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` ( 2 x. _pi ) ) e. RR )' % ph)], '%s e. RR' % KL_)
    def rho_r(AC, acr):
        rr_ = w.s([acr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` %s ) e. RR )' % (ph, AC))
        rrc = D(w, ph, 'recnd', [rr_], '( exp ` %s ) e. CC' % AC)
        # ( 1 - exp ) =/= 0 via exp ( AC ) =/= 1 : AC =/= 0 ... use: 1 - exp = exp ( 0 ) - exp ( AC ), AC < 0
        acn = D(w, ph, 'recnd', [acr], '%s e. CC' % AC)
        return rr_, rrc
    # simpler: CT e. RR from the per-index bound: abs <_ CT x. R4 ^ 1 with ...; instead obtain CT e. RR from zl3wbd is not exported; derive directly
    def rr_parts(KK, kkr, AC, acr, neg_lt):
        X_ = '( ( 8 x. %s ) / ( log ` 2 ) )' % KK; RHO = '( ( exp ` %s ) / ( 1 - ( exp ` %s ) ) )' % (AC, AC)
        l2rp = w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)
        xr = D(w, ph, 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), kkr], '( 8 x. %s ) e. RR' % KK), l2rp], '%s e. RR' % X_)
        rr_ = w.s([acr, w.inst('reefcl')], 'syl', '( %s -> ( exp ` %s ) e. RR )' % (ph, AC))
        r1_ = D(w, ph, 'breqtrd', [D(w, ph, 'mpbid', [neg_lt, w.s([acr, cst(w, ph, '0re', '0 e. RR'), w.inst('eflt')], 'syl2anc', '( %s -> ( %s < 0 <-> ( exp ` %s ) < ( exp ` 0 ) ) )' % (ph, AC, AC))],
                                       '( exp ` %s ) < ( exp ` 0 )' % AC), cst(w, ph, 'ef0', '( exp ` 0 ) = 1')], '( exp ` %s ) < 1' % AC)
        omr = D(w, ph, 'resubcld', [cst(w, ph, '1re', '1 e. RR'), rr_], '( 1 - ( exp ` %s ) ) e. RR' % AC)
        omp = D(w, ph, 'mpbid', [r1_, D(w, ph, 'posdifd', [rr_, cst(w, ph, '1re', '1 e. RR')], '( ( exp ` %s ) < 1 <-> 0 < ( 1 - ( exp ` %s ) ) )' % (AC, AC))], '0 < ( 1 - ( exp ` %s ) )' % AC)
        rhor = D(w, ph, 'redivcld', [rr_, omr, D(w, ph, 'gt0ne0d', [omp], '( 1 - ( exp ` %s ) ) =/= 0' % AC)], '%s e. RR' % RHO)
        return D(w, ph, 'remulcld', [xr, rhor], '( %s x. %s ) e. RR' % (X_, RHO))
    tpp = D(w, ph, 'rpgt0d', [D(w, ph, 'rpmulcld', [cst(w, ph, '2rp', '2 e. RR+'), cst(w, ph, 'pirp', '_pi e. RR+')], '( 2 x. _pi ) e. RR+')], '0 < ( 2 x. _pi )')
    ntp0 = D(w, ph, 'mpbid', [tpp, D(w, ph, 'lt0neg2d', [tpr], '( 0 < ( 2 x. _pi ) <-> %s < 0 )' % TPN)], '%s < 0' % TPN)
    ltR = D(w, ph, 'eqbrtrd', [D(w, ph, 'mulridd', [D(w, ph, 'recnd', [ntpr], '%s e. CC' % TPN)], '( %s x. 1 ) = %s' % (TPN, TPN)), ntp0], '( %s x. 1 ) < 0' % TPN)
    ltL = D(w, ph, 'eqbrtrd', [D(w, ph, 'eqtrd', [D(w, ph, 'mulneg2d', [D(w, ph, 'recnd', [tpr], '( 2 x. _pi ) e. CC'), cst(w, ph, 'ax-1cn', '1 e. CC')], '( ( 2 x. _pi ) x. -u 1 ) = -u ( ( 2 x. _pi ) x. 1 )'),
                                                  D(w, ph, 'negeqd', [D(w, ph, 'mulridd', [D(w, ph, 'recnd', [tpr], '( 2 x. _pi ) e. CC')], '( ( 2 x. _pi ) x. 1 ) = ( 2 x. _pi )')], '-u ( ( 2 x. _pi ) x. 1 ) = %s' % TPN)],
                                    '( ( 2 x. _pi ) x. -u 1 ) = %s' % TPN), ntp0], '( ( 2 x. _pi ) x. -u 1 ) < 0')
    cRr = rr_parts('K', kr, '( %s x. 1 )' % TPN, acR, ltR)
    cLr = rr_parts(KL_, klr, '( ( 2 x. _pi ) x. -u 1 )', acL, ltL)
    ctr = D(w, ph, 'readdcld', [D(w, ph, 'remulcld', [cst(w, ph, '4re', '4 e. RR'), kr], '( 4 x. K ) e. RR'), D(w, ph, 'readdcld', [cRr, cLr], 'x')], '%s e. RR' % CT) if False else None
    CR = '( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( ( exp ` ( %s x. 1 ) ) / ( 1 - ( exp ` ( %s x. 1 ) ) ) ) )' % (TPN, TPN)
    CL = '( ( ( 8 x. %s ) / ( log ` 2 ) ) x. ( ( exp ` ( ( 2 x. _pi ) x. -u 1 ) ) / ( 1 - ( exp ` ( ( 2 x. _pi ) x. -u 1 ) ) ) ) )' % KL_
    ctr = D(w, ph, 'readdcld', [D(w, ph, 'remulcld', [cst(w, ph, '4re', '4 e. RR'), kr], '( 4 x. K ) e. RR'), D(w, ph, 'readdcld', [cRr, cLr], '( %s + %s ) e. RR' % (CR, CL))], '%s e. RR' % CT)
    sq = w.s([w.s([D(w, ph, 'jca', [lpc, ctr], '( %s e. CC /\\ %s e. RR )' % (Lp, CT)), D(w, ph, 'jca', [r4r, D(w, ph, 'jca', [r40, r41], '( 0 <_ %s /\\ %s < 1 )' % (R4, R4))], '( %s e. RR /\\ ( 0 <_ %s /\\ %s < 1 ) )' % (R4, R4, R4)),
                   D(w, ph, 'jca', [cst(w, ph, 'seqex', '%s e. _V' % SQ), alln], '( %s e. _V /\\ A. n e. NN %s )' % (SQ, body('n')))], '3jca',
                  '( %s -> ( ( %s e. CC /\\ %s e. RR ) /\\ ( %s e. RR /\\ ( 0 <_ %s /\\ %s < 1 ) ) /\\ ( %s e. _V /\\ A. n e. NN %s ) ) )' % (ph, Lp, CT, R4, R4, R4, SQ, body('n'))), w.inst('zl3sqz')], 'syl',
             '( %s -> %s ~~> %s )' % (ph, SQ, Lp))
    # the series of pairs sums to L'
    P3 = '( %s /\\ n e. NN )' % ph
    nN3 = w.s([], 'simpr', '( %s -> n e. NN )' % P3)
    nc3 = D(w, P3, 'nncnd', [nN3], 'n e. CC')
    hf3 = w.s([hf], 'adantr', '( %s -> H : CC --> CC )' % P3)
    ic3 = cst(w, P3, 'ax-icn', '_i e. CC')
    pc3 = D(w, P3, 'addcld', [D(w, P3, 'ffvelcdmd', [hf3, D(w, P3, 'mulcld', [ic3, nc3], '( _i x. n ) e. CC')], '( H ` ( _i x. n ) ) e. CC'),
                              D(w, P3, 'ffvelcdmd', [hf3, D(w, P3, 'mulcld', [ic3, D(w, P3, 'negcld', [nc3], '-u n e. CC')], '( _i x. -u n ) e. CC')], '( H ` ( _i x. -u n ) ) e. CC')], '%s e. CC' % PAIR)
    ic_ = w.s([cst(w, ph, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'idi', '( %s -> NN = ( ZZ>= ` 1 ) )' % ph)
    isc = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, ph, '1z', '1 e. ZZ'), w.s([nN3, pfv], 'syl', '( %s -> ( %s ` n ) = %s )' % (P3, PF, PAIR)), pc3, sq], 'isumclim',
              '( %s -> sum_ n e. NN %s = %s )' % (ph, PAIR, Lp))
    pz = D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [isc], '( %s + sum_ n e. NN %s ) = ( %s + %s )' % (H0, PAIR, H0, Lp)), D(w, ph, 'pncan3d', [h0c, xic], '( %s + %s ) = %s' % (H0, Lp, XI))],
           '%s = %s' % (PZH, XI))
    fin = D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [pz], '( _i x. %s ) = ( _i x. %s )' % (PZH, XI)), D(w, ph, 'divcan2d', [xc, ic, inz], '( _i x. %s ) = %s' % (XI, X))], '( _i x. %s ) = %s' % (PZH, X))
    w.qed([conv, D(w, ph, 'jca', [D(w, ph, 'eqeltrd', [pz, xic], '%s e. CC' % PZH), fin], '( %s e. CC /\\ ( _i x. %s ) = %s )' % (PZH, PZH, X))], 'jca', S['zl3wlim'])
    go(w, only)


# ---------------------------------------------------------------- zl3wpois
def vl_sub(w, E, a, b, G, A, C):
    """( E -> VL(GKE(G,A,a),C) = VL(GKE(G,A,b),C) ) where E is ( a = b ) and e proves it"""
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    gk = w.s([D(w, E, 'oveq2d', [D(w, E, 'fveq2d', [D(w, E, 'oveq1d', [D(w, E, 'oveq1d', [e], '( %s x. %s ) = ( %s x. %s )' % (a, A, b, A))], '( ( %s x. %s ) x. y ) = ( ( %s x. %s ) x. y )' % (a, A, b, A))],
                                                    '( exp ` ( ( %s x. %s ) x. y ) ) = ( exp ` ( ( %s x. %s ) x. y ) )' % (a, A, b, A))],
                          '( ( %s ` y ) x. ( exp ` ( ( %s x. %s ) x. y ) ) ) = ( ( %s ` y ) x. ( exp ` ( ( %s x. %s ) x. y ) ) )' % (G, a, A, G, b, A))],
             'mpteq2dv', '( %s -> %s = %s )' % (E, GKE(G, A, a), GKE(G, A, b)))
    Et = '( %s /\\ t e. RR+ )' % E
    lt = D(w, Et, 'oveq1d', [w.s([gk], 'adantr', '( %s -> %s = %s )' % (Et, GKE(G, A, a), GKE(G, A, b)))], '%s = %s' % (LT(GKE(G, A, a), C, 't'), LT(GKE(G, A, b), C, 't')))
    return D(w, E, 'fveq2d', [w.s([lt], 'mpteq2dva', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (E, LT(GKE(G, A, a), C, 't'), LT(GKE(G, A, b), C, 't')))],
             '%s = %s' % (VL(GKE(G, A, a), C), VL(GKE(G, A, b), C)))


def subk(stmt, val):
    t = stmt.replace(HT, ' @HT@ ')
    t = ' '.join(val if x == 'k' else x for x in t.split())
    return t.replace('@HT@', HT)


