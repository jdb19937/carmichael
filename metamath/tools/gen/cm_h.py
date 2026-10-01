"""Sortie CM: the machine bound (cmmach) and the discharge of MidCensusHyp (cmmch).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_h.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *
from lin import linarith, nlinarith, lineq

only = sys.argv[1:]


def gen_mach():
    from mvlib import ringeq
    w = W('cmmach', 'THE MACHINE BOUND: in the middle window ` 1 - S < 2 / 10 ^ 13 ` , ` 10 ^ -10 < ( 1 - S ) log ( Z ( V + 2 ) ) ` the census up to ` Z ` is at most ` exp ( 4 . 10 ^ 9 + 4 . 10 ^ 10 ( 1 - S ) log ( Z ( V + 2 ) ) ) ` ( ~ cmfam at ` W = Z ( V + 2 ) ` , ` eta0 = ( 1 - S ) + 1 / ( 12 L ) ` , ` E = ( 11 / 10 ) eta0 ` , ` D = eta0 / 3 ` ; ~ cmbud ; the conductor ` 1 ` by ~ cen2bcf ; Lean ` censusCount_le_machine ` ).')
    A0, C0 = split_imp(S['cmmach'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    sr = g('S e. RR'); vr = g('V e. RR'); zr = g('Z e. RR'); s39 = g('%s <_ S' % F3940); s1 = g('S <_ 1'); v1 = g('1 <_ V'); z2 = g('2 <_ Z')
    Q2 = '( 2 / %s )' % C3
    LZ = LOGZ('Z', 'V')
    wa = g('( 1 - S ) < %s' % Q2); wb = g('%s < ( ( 1 - S ) x. %s )' % (THR, LZ))
    c0 = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'Z': ('RR', zr)})
    WW = '( Z x. ( V + 2 ) )'
    zp = linarith(w, A0, [z2], '0 < Z', closure=c0); c0.have('Z', 'gt0', zp)
    vp = linarith(w, A0, [v1], '0 < ( V + 2 )', closure=c0); c0.have('( V + 2 )', 'gt0', vp)
    wr = c0.mem(WW, 'RR'); wrp = c0.mem(WW, 'RR+')
    lr = d('relogcld', [wrp], '%s e. RR' % LZ)
    q2r = d('redivcld', [c0.mem('2', 'RR'), c0.mem(C3, 'RR'), c0.ne0(C3)], '%s e. RR' % Q2)
    q2e = d('divcan2d', [c0.mem('2', 'CC'), c0.mem(C3, 'CC'), c0.ne0(C3)], '( %s x. %s ) = 2' % (C3, Q2))
    cl = Closure(w, A0, {'S': ('RR', sr), LZ: ('RR', lr), Q2: ('RR', q2r)})
    cl.atom(LZ); cl.atom(Q2)
    wa2 = d('mpbird', [wa, d('ltmuldivd', [cl.mem('( 1 - S )', 'RR'), cl.mem('2', 'RR'), cl.mem(C3, 'RR+')], '( ( ( 1 - S ) x. %s ) < 2 <-> ( 1 - S ) < %s )' % (C3, Q2))], '( ( 1 - S ) x. %s ) < 2' % C3)
    s0 = linarith(w, A0, [s1], '0 <_ ( 1 - S )', closure=cl)
    # L > 500
    A1 = '( %s /\\ %s <_ ; ; 5 0 0 )' % (A0, LZ)
    cl1 = Closure(w, A1, {'S': ('RR', lift(w, sr, A1)), LZ: ('RR', lift(w, lr, A1)), Q2: ('RR', lift(w, q2r, A1))})
    cl1.atom(LZ); cl1.atom(Q2)
    P = '( ( 1 - S ) x. %s )' % LZ
    small = nlinarith(w, A1, [w.s([], 'simpr', '( %s -> %s <_ ; ; 5 0 0 )' % (A1, LZ)), lift(w, s0, A1), lift(w, wa2, A1)], '%s < %s' % (P, THR), closure=cl1)
    nle = d('mtand', [d('ltnsymd', [cl.mem(THR, 'RR'), cl.mem(P, 'RR'), wb], '-. %s < %s' % (P, THR)), small], '-. %s <_ ; ; 5 0 0' % LZ)
    l500 = d('mpbird', [nle, d('ltnled', [cl.mem('; ; 5 0 0', 'RR'), lr], '( ; ; 5 0 0 < %s <-> -. %s <_ ; ; 5 0 0 )' % (LZ, LZ))], '; ; 5 0 0 < %s' % LZ)
    # parameters
    IL = '( 1 / ( ; 1 2 x. %s ) )' % LZ
    cl.have(LZ, 'gt0', linarith(w, A0, [l500], '0 < %s' % LZ, closure=cl))
    ilr = cl.mem(IL, 'RR'); ilp = cl.gt0(IL)
    ill = d('syl2anc', [cl.mem('( ; 1 2 x. %s )' % LZ, 'CC'), cl.ne0('( ; 1 2 x. %s )' % LZ), w.inst('recid2')], '( %s x. ( ; 1 2 x. %s ) ) = 1' % (IL, LZ))
    cl.atom(IL)
    E = EEX(LZ); D_ = DDX(LZ); ET = ETA0(LZ)
    pl = d('mulge0d', [cl.mem('( 1 - S )', 'RR'), lr, s0, linarith(w, A0, [l500], '0 <_ %s' % LZ, closure=cl)], '0 <_ %s' % P)
    il6 = nlinarith(w, A0, [ill, l500, ilp], '%s <_ ( 1 / ; ; ; 6 0 0 0 )' % IL, closure=cl)
    etp = linarith(w, A0, [s0, ilp], '0 < %s' % ET, closure=cl)
    er = cl.mem(E, 'RR'); erp = d('elrpd', [er, linarith(w, A0, [etp], '0 < %s' % E, closure=cl)], '%s e. RR+' % E)
    e5 = linarith(w, A0, [wa2, il6], '%s <_ %s' % (E, R5000), closure=cl)
    e12 = nlinarith(w, A0, [ill, pl], '1 <_ ( ( ; 1 2 x. %s ) x. %s )' % (E, LZ), closure=cl)
    dr = cl.mem(D_, 'RR'); drp = d('elrpd', [dr, linarith(w, A0, [etp], '0 < %s' % D_, closure=cl)], '%s e. RR+' % D_)
    d1 = linarith(w, A0, [wa2, il6], '%s <_ 1' % D_, closure=cl)
    dist = nlinarith(w, A0, [s0, ilp], '( ( ( 1 - S ) ^ 2 ) + ( %s ^ 2 ) ) <_ ( %s ^ 2 )' % (D_, E), closure=cl)
    # W facts
    K = '( |_ ` Z )'
    kz = d('flcld', [zr], '%s e. ZZ' % K)
    kle = d('syl', [zr, w.inst('flle')], '%s <_ Z' % K)
    cw = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'Z': ('RR', zr), K: ('ZZ', kz)})
    zv = nlinarith(w, A0, [z2, v1], '( 2 x. ( V + 2 ) ) <_ %s' % WW, closure=cw)
    zv2 = nlinarith(w, A0, [z2, v1], 'Z <_ %s' % WW, closure=cw)
    cw.atom(WW); cw.have(WW, 'RR', wr)
    w2 = linarith(w, A0, [zv, v1], '2 <_ %s' % WW, closure=cw)
    v3 = linarith(w, A0, [zv, v1], '( V + 3 ) <_ %s' % WW, closure=cw)
    kw = linarith(w, A0, [kle, zv2], '%s <_ %s' % (K, WW), closure=cw)
    s0p = linarith(w, A0, [s39], '0 < S', closure=cw)
    # W ^ 5 <_ X1
    kn = d('syl', [d('jca', [d('jca', [er, d('rpge0d', [erp], '0 <_ %s' % E)], '( %s e. RR /\\ 0 <_ %s )' % (E, E)), d('jca', [lr, linarith(w, A0, [l500], '0 <_ %s' % LZ, closure=cl)], '( %s e. RR /\\ 0 <_ %s )' % (LZ, LZ))],
                   '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (E, E, LZ, LZ)), w.inst('kdndet')], inst('kdndet', {'E': E, 'L': LZ})[1])
    KN = split_all(w, A0, inst('kdndet', {'E': E, 'L': LZ})[1], kn)
    N = NDET(E, LZ); M = MDET(E, LZ)
    CN = '; ; ; ; ; ; ; ; 8 4 0 0 0 0 0 0 0'
    nge = KN['( 6 + ( ( %s x. %s ) x. %s ) ) <_ %s' % (CN, E, LZ, N)]
    nr = d('nnred', [KN['%s e. NN' % N]], '%s e. RR' % N)
    ce = Closure(w, A0, {E: ('RR+', erp), LZ: ('RR', lr), N: ('RR', nr)})
    ce.have(LZ, 'gt0', linarith(w, A0, [l500], '0 < %s' % LZ, closure=cl))
    for at_ in (E, LZ, N):
        ce.atom(at_)
    el0 = d('mulge0d', [er, lr, d('rpge0d', [erp], '0 <_ %s' % E), linarith(w, A0, [l500], '0 <_ %s' % LZ, closure=cl)], '0 <_ ( %s x. %s )' % (E, LZ))
    m80 = nlinarith(w, A0, [nge, el0], '( ( 5 x. %s ) x. ( ; 1 6 x. %s ) ) <_ %s' % (LZ, E, M), closure=ce)
    X1_ = XONE(E, LZ)
    Q1 = '( %s / ( ; 1 6 x. %s ) )' % (M, E)
    q1 = d('mpbid', [m80, d('syl3anc', [ce.mem('( 5 x. %s )' % LZ, 'RR'), ce.mem(M, 'RR'), d('jca', [ce.mem('( ; 1 6 x. %s )' % E, 'RR'), ce.gt0('( ; 1 6 x. %s )' % E)], '( ( ; 1 6 x. %s ) e. RR /\\ 0 < ( ; 1 6 x. %s ) )' % (E, E)), w.inst('lemuldiv')],
                                     '( ( ( 5 x. %s ) x. ( ; 1 6 x. %s ) ) <_ %s <-> ( 5 x. %s ) <_ %s )' % (LZ, E, M, LZ, Q1))], '( 5 x. %s ) <_ %s' % (LZ, Q1))
    ef = d('mpbid', [q1, d('syl2anc', [ce.mem('( 5 x. %s )' % LZ, 'RR'), ce.mem(Q1, 'RR'), w.inst('efle')], '( ( 5 x. %s ) <_ %s <-> ( exp ` ( 5 x. %s ) ) <_ %s )' % (LZ, Q1, LZ, X1_))], '( exp ` ( 5 x. %s ) ) <_ %s' % (LZ, X1_))
    w5e = chain(w, A0, ['( exp ` ( 5 x. %s ) )' % LZ, '( ( exp ` %s ) ^ 5 )' % LZ, '( %s ^ 5 )' % WW],
                [d('syl2anc', [d('recnd', [lr], '%s e. CC' % LZ), a1(w, A0, '5nn' if False else 'nnzi', '5 e. ZZ', [w.s([], '5nn', '5 e. NN')]), w.inst('efexp')], '( exp ` ( 5 x. %s ) ) = ( ( exp ` %s ) ^ 5 )' % (LZ, LZ)),
                 d('oveq1d', [d('syl', [wrp, w.inst('reeflog')], '( exp ` %s ) = %s' % (LZ, WW))], '( ( exp ` %s ) ^ 5 ) = ( %s ^ 5 )' % (LZ, WW))])
    w5 = d('eqbrtrrd', [w5e, ef], '( %s ^ 5 ) <_ %s' % (WW, X1_))
    # the family bound at W = Z ( V + 2 )
    FM = inst('cmfam', {'W': WW, 'K': K, 'E': E, 'D': D_})
    fh = d('jca', [d('jca', [d('3jca', [d('3jca', [sr, vr, wr], '( S e. RR /\\ V e. RR /\\ %s e. RR )' % WW), d('jca', [s0p, s1], '( 0 < S /\\ S <_ 1 )'), d('jca', [v1, w2], '( 1 <_ V /\\ 2 <_ %s )' % WW)],
                                     '( ( S e. RR /\\ V e. RR /\\ %s e. RR ) /\\ ( 0 < S /\\ S <_ 1 ) /\\ ( 1 <_ V /\\ 2 <_ %s ) )' % (WW, WW)),
                             d('3jca', [kz, kw, v3], '( %s e. ZZ /\\ %s <_ %s /\\ ( V + 3 ) <_ %s )' % (K, K, WW, WW))],
                       '( ( ( S e. RR /\\ V e. RR /\\ %s e. RR ) /\\ ( 0 < S /\\ S <_ 1 ) /\\ ( 1 <_ V /\\ 2 <_ %s ) ) /\\ ( %s e. ZZ /\\ %s <_ %s /\\ ( V + 3 ) <_ %s ) )' % (WW, WW, K, K, WW, WW)),
                   d('3jca', [d('jca', [erp, e5], '( %s e. RR+ /\\ %s <_ %s )' % (E, E, R5000)), e12,
                              d('jca', [d('jca', [d('jca', [drp, d1], '( %s e. RR+ /\\ %s <_ 1 )' % (D_, D_)), dist], '( ( %s e. RR+ /\\ %s <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( %s ^ 2 ) ) <_ ( %s ^ 2 ) )' % (D_, D_, D_, E)), w5],
                                    '( ( ( %s e. RR+ /\\ %s <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( %s ^ 2 ) ) <_ ( %s ^ 2 ) ) /\\ ( %s ^ 5 ) <_ %s )' % (D_, D_, D_, E, WW, X1_))],
                         FM[0].split(' ) /\\ ( ( %s e. RR+' % E, 1)[0] and ('( ( %s e. RR+ /\\ %s <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. %s ) x. %s ) /\\ ( ( ( %s e. RR+ /\\ %s <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( %s ^ 2 ) ) <_ ( %s ^ 2 ) ) /\\ ( %s ^ 5 ) <_ %s ) )' % (E, E, R5000, E, LZ, D_, D_, D_, E, WW, X1_)))],
           FM[0])
    fam = d('syl', [fh, w.inst('cmfam')], FM[1])
    # R
    R = RCNT.replace('( 2 ... K )', '( 2 ... %s )' % K)
    BCd = BC('S', 'V', 'd')
    Cd = '( %s /\\ d e. ( 2 ... %s ) )' % (A0, K)
    cd = mk(w, Cd)
    dnn = cd('syl', [cd('syl', [w.s([], 'simpr', '( %s -> d e. ( 2 ... %s ) )' % (Cd, K)), w.inst('elfzuz')], 'd e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'd e. NN')
    hn = cd('syl', [cd('simpld', [cd('syl', [dnn, w.inst('cen2bcf')], '( %s e. Fin /\\ ( # ` %s ) <_ d )' % (BCd, BCd))], '%s e. Fin' % BCd), w.inst('hashcl')], '( # ` %s ) e. NN0' % BCd)
    rr = d('fsumrecl', [d('fzfid', [], '( 2 ... %s ) e. Fin' % K), cd('nn0red', [hn], '( # ` %s ) e. RR' % BCd)], '%s e. RR' % R)
    r0 = d('fsumge0', [d('fzfid', [], '( 2 ... %s ) e. Fin' % K), cd('nn0red', [hn], '( # ` %s ) e. RR' % BCd), cd('nn0ge0d', [hn], '0 <_ ( # ` %s )' % BCd)], '0 <_ %s' % R)
    BD = inst('cmbud', {'L': LZ, 'R': R})
    assert BD[0].endswith(FM[1] + ' )'), (BD[0][-400:], FM[1][-400:])
    bud = d('syl', [d('jca', [d('3jca', [d('jca', [sr, s1], '( S e. RR /\\ S <_ 1 )'), d('jca', [lr, l500], '( %s e. RR /\\ ; ; 5 0 0 < %s )' % (LZ, LZ)), d('jca', [rr, r0], '( %s e. RR /\\ 0 <_ %s )' % (R, R))],
                                    '( ( S e. RR /\\ S <_ 1 ) /\\ ( %s e. RR /\\ ; ; 5 0 0 < %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (LZ, LZ, R, R)), fam], BD[0]), w.inst('cmbud')], BD[1])
    # the census: conductor 1 plus R
    CN_ = CNT('S', 'V', K)
    Bm = BC('S', 'V', 'm'); B1 = BC('S', 'V', '1')
    Cm = '( %s /\\ m e. ( 1 ... %s ) )' % (A0, K)
    cm = mk(w, Cm)
    mn = cm('syl', [w.s([], 'simpr', '( %s -> m e. ( 1 ... %s ) )' % (Cm, K)), w.inst('elfznn')], 'm e. NN')
    hm = cm('syl', [cm('simpld', [cm('syl', [mn, w.inst('cen2bcf')], '( %s e. Fin /\\ ( # ` %s ) <_ m )' % (Bm, Bm))], '%s e. Fin' % Bm), w.inst('hashcl')], '( # ` %s ) e. NN0' % Bm)
    eqm = 'm = 1'
    idm = w.s([], 'id', '( %s -> %s )' % (eqm, eqm))
    st1, b1 = w.congr('( # ` %s )' % Bm, {'m': '1'}, eqm, {'m': idm})
    assert b1 == '( # ` %s )' % B1
    ku = d('mpbird', [d('3jca', [a1(w, A0, '1z', '1 e. ZZ'), kz, linarith(w, A0, [d('mpbid', [z2, d('syl2anc', [zr, a1(w, A0, '2z', '2 e. ZZ'), w.inst('flge')], '( 2 <_ Z <-> 2 <_ %s )' % K)], '2 <_ %s' % K)], '1 <_ %s' % K, closure=cw)],
                                '( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s )' % (K, K)), a1(w, A0, 'eluz2', '( %s e. ( ZZ>= ` 1 ) <-> ( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s ) )' % (K, K, K))], '%s e. ( ZZ>= ` 1 )' % K)
    fp = d('fsum1p', [ku, cm('nn0cnd', [hm], '( # ` %s ) e. CC' % Bm), st1], '%s = ( ( # ` %s ) + sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) )' % (CN_, B1, K, Bm))
    eqd = 'm = d'
    idd = w.s([], 'id', '( %s -> %s )' % (eqd, eqd))
    std, bd_ = w.congr('( # ` %s )' % Bm, {'m': 'd'}, eqd, {'m': idd})
    rn = a1(w, A0, 'cbvsumv', 'sum_ m e. ( 2 ... %s ) ( # ` %s ) = %s' % (K, Bm, R), [std])
    r12 = d('sumeq1d', [d('oveq1d', [a1(w, A0, '1p1e2', '( 1 + 1 ) = 2')], '( ( 1 + 1 ) ... %s ) = ( 2 ... %s )' % (K, K))], 'sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) = sum_ m e. ( 2 ... %s ) ( # ` %s )' % (K, Bm, K, Bm))
    cq = chain(w, A0, [CN_, '( ( # ` %s ) + sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) )' % (B1, K, Bm), '( ( # ` %s ) + %s )' % (B1, R)],
               [fp, d('oveq2d', [d('eqtrd', [r12, rn], 'sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) = %s' % (K, Bm, R))], '( ( # ` %s ) + sum_ m e. ( ( 1 + 1 ) ... %s ) ( # ` %s ) ) = ( ( # ` %s ) + %s )' % (B1, K, Bm, B1, R))])
    b1f = d('syl', [a1(w, A0, '1nn', '1 e. NN'), w.inst('cen2bcf')], '( %s e. Fin /\\ ( # ` %s ) <_ 1 )' % (B1, B1))
    h1 = d('simprd', [b1f], '( # ` %s ) <_ 1' % B1)
    MX = MEXPL(LZ)
    cf = Closure(w, A0, {R: ('RR', rr), '( # ` %s )' % B1: ('RR', d('nn0red', [d('syl', [d('simpld', [b1f], '%s e. Fin' % B1), w.inst('hashcl')], '( # ` %s ) e. NN0' % B1)], '( # ` %s ) e. RR' % B1)),
                         CN_: ('RR', d('eqeltrd', [cq, d('readdcld', [d('nn0red', [d('syl', [d('simpld', [b1f], '%s e. Fin' % B1), w.inst('hashcl')], '( # ` %s ) e. NN0' % B1)], '( # ` %s ) e. RR' % B1), rr], '( ( # ` %s ) + %s ) e. RR' % (B1, R))], '%s e. RR' % CN_)),
                         MX: ('RR', d('reefcld', [cl.mem('( %s + ( ( %s x. ( 1 - S ) ) x. %s ) )' % (AMACH, BMACH, LZ), 'RR')], '%s e. RR' % MX))})
    for at_ in (R, '( # ` %s )' % B1, CN_, MX):
        cf.atom(at_)
    fin = linarith(w, A0, [cq, h1, bud], C0, closure=cf)
    w.qed([fin], 'idi', S['cmmach'])
    return run(w, only)


def gen_abs():
    from mvlib import ringeq
    from kd2lib import numpow
    w = W('cmabs', 'THE ABSORPTION: in the middle window the census is at most ` 10 ^ ( 10 ^ 10 ) ( V + 2 ) Z ^ ( 10 ^ 13 ( 1 - S ) ) ` : ` exp ( 4 . 10 ^ 9 ) <_ e ^ ( 10 ^ 10 ) <_ 10 ^ ( 10 ^ 10 ) ` , ` 4 . 10 ^ 10 <_ 10 ^ 13 ` , and ` 4 . 10 ^ 10 ( 1 - S ) <_ 1 ` ( ~ cmmach ; Lean ` midCensusHyp ` , ` exp_le_tower ` ; C10-HANDOFF s6 item 4, NUMERALS.md).')
    A0, C0 = split_imp(S['cmabs'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    sr = g('S e. RR'); vr = g('V e. RR'); zr = g('Z e. RR'); s39 = g('%s <_ S' % F3940); s1 = g('S <_ 1'); v1 = g('1 <_ V'); z2 = g('2 <_ Z')
    Q2 = '( 2 / %s )' % C3
    LZ = LOGZ('Z', 'V')
    wa = g('( 1 - S ) < %s' % Q2); wb = g('%s < ( ( 1 - S ) x. %s )' % (THR, LZ))
    MC = S['cmmach']
    mh = d('3jca', [g(TYP), d('jca', [d('jca', [s39, s1], '( %s <_ S /\\ S <_ 1 )' % F3940), d('jca', [v1, z2], '( 1 <_ V /\\ 2 <_ Z )')], RNG), d('jca', [wa, wb], WIN)], split_imp(MC)[0])
    mach = d('syl', [mh, w.inst('cmmach')], split_imp(MC)[1])
    c0 = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'Z': ('RR', zr)})
    zp = linarith(w, A0, [z2], '0 < Z', closure=c0); c0.have('Z', 'gt0', zp)
    vp = linarith(w, A0, [v1], '0 < ( V + 2 )', closure=c0); c0.have('( V + 2 )', 'gt0', vp)
    V2 = '( V + 2 )'
    C = '( %s x. ( 1 - S ) )' % BMACH
    cr = c0.mem(C, 'RR')
    LZ1 = '( log ` Z )'; LV = '( log ` %s )' % V2
    lm = d('syl2anc', [c0.mem('Z', 'RR+'), c0.mem(V2, 'RR+'), w.inst('relogmul')], '%s = ( %s + %s )' % (LZ, LZ1, LV))
    cc = Closure(w, A0, {C: ('CC', d('recnd', [cr], '%s e. CC' % C)), LZ1: ('CC', d('recnd', [c0.mem(LZ1, 'RR')], '%s e. CC' % LZ1)), LV: ('CC', d('recnd', [c0.mem(LV, 'RR')], '%s e. CC' % LV))})
    for at_ in (C, LZ1, LV):
        cc.atom(at_)
    ARG = '( %s + ( %s x. %s ) )' % (AMACH, C, LZ)
    ARG2 = '( %s + ( ( %s x. %s ) + ( %s x. %s ) ) )' % (AMACH, C, LZ1, C, LV)
    aq = d('oveq2d', [d('eqtrd', [d('oveq2d', [lm], '( %s x. %s ) = ( %s x. ( %s + %s ) )' % (C, LZ, C, LZ1, LV)), ringeq(w, A0, '( %s x. ( %s + %s ) )' % (C, LZ1, LV), '( ( %s x. %s ) + ( %s x. %s ) )' % (C, LZ1, C, LV), cc)],
                                  '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (C, LZ, C, LZ1, C, LV))], '%s = %s' % (ARG, ARG2))
    EA = '( exp ` %s )' % AMACH
    ZC = '( Z ^c %s )' % C; VC = '( %s ^c %s )' % (V2, C)
    c1 = cc.mem('( %s x. %s )' % (C, LZ1), 'CC'); c2 = cc.mem('( %s x. %s )' % (C, LV), 'CC')
    ex = chain(w, A0, ['( exp ` %s )' % ARG, '( exp ` %s )' % ARG2, '( %s x. ( exp ` ( ( %s x. %s ) + ( %s x. %s ) ) ) )' % (EA, C, LZ1, C, LV),
                       '( %s x. ( ( exp ` ( %s x. %s ) ) x. ( exp ` ( %s x. %s ) ) ) )' % (EA, C, LZ1, C, LV), '( %s x. ( %s x. %s ) )' % (EA, ZC, VC)],
               [d('fveq2d', [aq], '( exp ` %s ) = ( exp ` %s )' % (ARG, ARG2)),
                d('syl2anc', [c0.mem(AMACH, 'CC'), d('addcld', [c1, c2], '( ( %s x. %s ) + ( %s x. %s ) ) e. CC' % (C, LZ1, C, LV)), w.inst('efadd')], '( exp ` %s ) = ( %s x. ( exp ` ( ( %s x. %s ) + ( %s x. %s ) ) ) )' % (ARG2, EA, C, LZ1, C, LV)),
                d('oveq2d', [d('syl2anc', [c1, c2, w.inst('efadd')], '( exp ` ( ( %s x. %s ) + ( %s x. %s ) ) ) = ( ( exp ` ( %s x. %s ) ) x. ( exp ` ( %s x. %s ) ) )' % (C, LZ1, C, LV, C, LZ1, C, LV))],
                  '( %s x. ( exp ` ( ( %s x. %s ) + ( %s x. %s ) ) ) ) = ( %s x. ( ( exp ` ( %s x. %s ) ) x. ( exp ` ( %s x. %s ) ) ) )' % (EA, C, LZ1, C, LV, EA, C, LZ1, C, LV)),
                d('oveq2d', [d('oveq12d', [d('eqcomd', [d('syl3anc', [c0.mem('Z', 'CC'), c0.ne0('Z'), cc.mem(C, 'CC'), w.inst('cxpef')], '%s = ( exp ` ( %s x. %s ) )' % (ZC, C, LZ1))], '( exp ` ( %s x. %s ) ) = %s' % (C, LZ1, ZC)),
                                           d('eqcomd', [d('syl3anc', [c0.mem(V2, 'CC'), c0.ne0(V2), cc.mem(C, 'CC'), w.inst('cxpef')], '%s = ( exp ` ( %s x. %s ) )' % (VC, C, LV))], '( exp ` ( %s x. %s ) ) = %s' % (C, LV, VC))],
                             '( ( exp ` ( %s x. %s ) ) x. ( exp ` ( %s x. %s ) ) ) = ( %s x. %s )' % (C, LZ1, C, LV, ZC, VC))],
                  '( %s x. ( ( exp ` ( %s x. %s ) ) x. ( exp ` ( %s x. %s ) ) ) ) = ( %s x. ( %s x. %s ) )' % (EA, C, LZ1, C, LV, EA, ZC, VC))])
    # exp a <_ 10 ^ ( 10 ^ 10 )
    T10 = '( ; 1 0 ^ ; 1 0 )'; P10 = '( ; 1 0 ^ %s )' % T10
    tv = numpow(w, 10, 10)
    TD = dec('1' + '0' * 10)
    t10n = w.s([w.s([], '10nn', '; 1 0 e. NN'), w.s([w.s([], '10nn', '; 1 0 e. NN')], 'nnnn0i', '; 1 0 e. NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % T10)
    at = d('breqtrrd', [linarith(w, A0, [], '%s <_ %s' % (AMACH, TD), closure=c0), a1(w, A0, 'idi', '%s = %s' % (T10, TD), [tv])], '%s <_ %s' % (AMACH, T10))
    t10r = w.s([t10n], 'nnrei', '%s e. RR' % T10)
    e1 = d('mpbid', [at, d('syl2anc', [c0.mem(AMACH, 'RR'), a1(w, A0, 'idi', '%s e. RR' % T10, [t10r]), w.inst('efle')], '( %s <_ %s <-> %s <_ ( exp ` %s ) )' % (AMACH, T10, EA, T10))], '%s <_ ( exp ` %s )' % (EA, T10))
    e2 = chain(w, A0, ['( exp ` %s )' % T10, '( exp ` ( %s x. 1 ) )' % T10, '( ( exp ` 1 ) ^ %s )' % T10],
               [d('fveq2d', [d('eqcomd', [d('mulridd', [d('recnd', [a1(w, A0, 'idi', '%s e. RR' % T10, [t10r])], '%s e. CC' % T10)], '( %s x. 1 ) = %s' % (T10, T10))], '%s = ( %s x. 1 )' % (T10, T10))],
                  '( exp ` %s ) = ( exp ` ( %s x. 1 ) )' % (T10, T10)),
                d('syl2anc', [a1(w, A0, 'ax-1cn', '1 e. CC'), a1(w, A0, 'nnzi', '%s e. ZZ' % T10, [t10n]), w.inst('efexp')], '( exp ` ( %s x. 1 ) ) = ( ( exp ` 1 ) ^ %s )' % (T10, T10))])
    import cm_g
    e3 = cm_g.elt3(w, A0)
    le10 = linarith(w, A0, [e3], '( exp ` 1 ) <_ ; 1 0', closure=Closure(w, A0, {'( exp ` 1 )': ('RR', ere(w, A0))}), atoms=['( exp ` 1 )'])
    e4 = d('syl2anc', [d('3jca', [ere(w, A0), a1(w, A0, '10re', '; 1 0 e. RR'), a1(w, A0, 'nnnn0i', '%s e. NN0' % T10, [t10n])], '( ( exp ` 1 ) e. RR /\\ ; 1 0 e. RR /\\ %s e. NN0 )' % T10),
                       d('jca', [d('ltled', [a1(w, A0, '0re', '0 e. RR'), ere(w, A0), epos(w, A0)], '0 <_ ( exp ` 1 )'), le10], '( 0 <_ ( exp ` 1 ) /\\ ( exp ` 1 ) <_ ; 1 0 )'), w.inst('leexp1a')],
           '( ( exp ` 1 ) ^ %s ) <_ %s' % (T10, P10))
    p10r = d('reexpcld', [a1(w, A0, '10re', '; 1 0 e. RR'), a1(w, A0, 'nnnn0i', '%s e. NN0' % T10, [t10n])], '%s e. RR' % P10)
    ear = d('reefcld', [c0.mem(AMACH, 'RR')], '%s e. RR' % EA)
    et10 = d('reefcld', [a1(w, A0, 'idi', '%s e. RR' % T10, [t10r])], '( exp ` %s ) e. RR' % T10)
    eap = d('letrd', [ear, et10, p10r, e1, d('eqbrtrd', [e2, e4], '( exp ` %s ) <_ %s' % (T10, P10))], '%s <_ %s' % (EA, P10))
    # Z ^ c <_ Z ^ ( C3 ( 1 - S ) ), ( V + 2 ) ^ c <_ V + 2
    wa2 = d('mpbird', [wa, d('ltmuldivd', [c0.mem('( 1 - S )', 'RR'), c0.mem('2', 'RR'), c0.mem(C3, 'RR+')], '( ( ( 1 - S ) x. %s ) < 2 <-> ( 1 - S ) < %s )' % (C3, Q2))], '( ( 1 - S ) x. %s ) < 2' % C3)
    s0 = linarith(w, A0, [s1], '0 <_ ( 1 - S )', closure=c0)
    CE = '( %s x. ( 1 - S ) )' % C3
    cle = linarith(w, A0, [s0], '%s <_ %s' % (C, CE), closure=c0)
    c1_ = linarith(w, A0, [wa2, s0], '%s <_ 1' % C, closure=c0)
    ZE = '( Z ^c %s )' % CE
    zle = d('syl3anc', [d('jca', [zr, linarith(w, A0, [z2], '1 <_ Z', closure=c0)], '( Z e. RR /\\ 1 <_ Z )'), d('jca', [cr, c0.mem(CE, 'RR')], '( %s e. RR /\\ %s e. RR )' % (C, CE)), cle, w.inst('cxplea')], '%s <_ %s' % (ZC, ZE))
    vle = d('breqtrd', [d('syl3anc', [d('jca', [c0.mem(V2, 'RR'), linarith(w, A0, [v1], '1 <_ %s' % V2, closure=c0)], '( %s e. RR /\\ 1 <_ %s )' % (V2, V2)), d('jca', [cr, a1(w, A0, '1re', '1 e. RR')], '( %s e. RR /\\ 1 e. RR )' % C), c1_, w.inst('cxplea')],
                                  '%s <_ ( %s ^c 1 )' % (VC, V2)), d('cxp1d', [c0.mem(V2, 'CC')], '( %s ^c 1 ) = %s' % (V2, V2))], '%s <_ %s' % (VC, V2))
    zcr = d('rpred', [d('rpcxpcld', [c0.mem('Z', 'RR+'), cr], '%s e. RR+' % ZC)], '%s e. RR' % ZC); zc0 = d('rpge0d', [d('rpcxpcld', [c0.mem('Z', 'RR+'), cr], '%s e. RR+' % ZC)], '0 <_ %s' % ZC)
    vcr = d('rpred', [d('rpcxpcld', [c0.mem(V2, 'RR+'), cr], '%s e. RR+' % VC)], '%s e. RR' % VC); vc0 = d('rpge0d', [d('rpcxpcld', [c0.mem(V2, 'RR+'), cr], '%s e. RR+' % VC)], '0 <_ %s' % VC)
    zer = d('rpred', [d('rpcxpcld', [c0.mem('Z', 'RR+'), c0.mem(CE, 'RR')], '%s e. RR+' % ZE)], '%s e. RR' % ZE)
    m1 = d('lemul12ad', [zcr, zer, vcr, c0.mem(V2, 'RR'), zc0, vc0, zle, vle], '( %s x. %s ) <_ ( %s x. %s )' % (ZC, VC, ZE, V2))
    m2 = d('lemul12ad', [ear, p10r, d('remulcld', [zcr, vcr], '( %s x. %s ) e. RR' % (ZC, VC)), d('remulcld', [zer, c0.mem(V2, 'RR')], '( %s x. %s ) e. RR' % (ZE, V2)),
                         d('rpge0d', [d('rpefcld', [c0.mem(AMACH, 'RR')], '%s e. RR+' % EA)], '0 <_ %s' % EA), d('mulge0d', [zcr, vcr, zc0, vc0], '0 <_ ( %s x. %s )' % (ZC, VC)), eap, m1],
           '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (EA, ZC, VC, P10, ZE, V2))
    BN = BND('S', 'V', 'Z')
    cb = Closure(w, A0, {P10: ('CC', d('recnd', [p10r], '%s e. CC' % P10)), ZE: ('CC', d('recnd', [zer], '%s e. CC' % ZE)), 'V': ('CC', c0.mem('V', 'CC'))})
    for at_ in (P10, ZE):
        cb.atom(at_)
    rq = ringeq(w, A0, '( %s x. ( %s x. %s ) )' % (P10, ZE, V2), BN, cb)
    MEX = '( exp ` %s )' % ARG
    fin = d('breqtrd', [d('letrd', [c0.mem(CNT('S', 'V', '( |_ ` Z )'), 'RR') if False else d('eqeltrrd' if False else 'id', [], 'x') if False else None, None, None, None, None], 'x') if False else
                        d('breqtrd', [mach, ex], '%s <_ ( %s x. ( %s x. %s ) )' % (CNT('S', 'V', '( |_ ` Z )'), EA, ZC, VC)), rq], 'x') if False else None
    cn1 = d('breqtrd', [mach, ex], '%s <_ ( %s x. ( %s x. %s ) )' % (CNT('S', 'V', '( |_ ` Z )'), EA, ZC, VC))
    cnr = [l for l in w.lines if False]
    CNZ = CNT('S', 'V', '( |_ ` Z )')
    cnre = d('letrd' if False else 'id', [], 'x') if False else None
    # CNT real: from the machine bound's left side (fsum of finite hashes)
    from cm_h_aux import cntre
    cnrr = cntre(w, A0, zr)
    f1 = d('letrd', [cnrr, d('remulcld', [ear, d('remulcld', [zcr, vcr], '( %s x. %s ) e. RR' % (ZC, VC))], '( %s x. ( %s x. %s ) ) e. RR' % (EA, ZC, VC)),
                     d('remulcld', [p10r, d('remulcld', [zer, c0.mem(V2, 'RR')], '( %s x. %s ) e. RR' % (ZE, V2))], '( %s x. ( %s x. %s ) ) e. RR' % (P10, ZE, V2)), cn1, m2],
           '%s <_ ( %s x. ( %s x. %s ) )' % (CNZ, P10, ZE, V2))
    fin = d('breqtrd', [f1, rq], '%s <_ %s' % (CNZ, BN))
    w.qed([fin], 'idi', S['cmabs'])
    return run(w, only)


def gen_mch():
    w = W('cmmch', 'THE Z7 DISCHARGE: the middle-regime census hypothesis ` MidCensusHyp ` holds (CEN2 frozen text), so CEN2 ~ cen2cc ( ` census_contract ` ) and ~ cen2bad are unconditional (Lean ` midCensusHyp ` ).')
    AB = S['cmabs']
    AB2 = ' '.join({'S': 'u', 'V': 'v', 'Z': 'w'}.get(x, x) for x in AB.split())
    A, Cn = split_imp(AB2)
    from c9lib import top_and
    typ, body = top_and(A)
    s1 = w.s([], 'cmabs', AB2)
    s2 = w.s([s1], 'ex', '( %s -> ( %s -> %s ) )' % (typ, body, Cn))
    w.qed([s2], 'rgen3', S['cmmch'])
    return run(w, only)


def gen_cc():
    w = W('cmcc', 'The Z7 contract without hypothesis: ` census_contract ` ( CEN2 ~ cen2cc ) with ` MidCensusHyp ` discharged by ~ cmmch .')
    s1 = w.s([], 'cmmch', MCH)
    w.qed([s1, w.inst('cen2cc')], 'mpan', S['cmcc'])
    return run(w, only)


def gen_bad():
    w = W('cmbad', 'The consumption form of the Z7 contract without hypothesis: CEN2 ~ cen2bad ( ` card_badConductors_le ` ) with ` MidCensusHyp ` discharged by ~ cmmch .')
    s1 = w.s([], 'cmmch', MCH)
    w.qed([s1, w.inst('cen2bad')], 'mp3an1', S['cmbad'])
    return run(w, only)


if __name__ == '__main__':
    gen_mach()
    gen_abs()
    gen_mch()
    gen_cc()
    gen_bad()
