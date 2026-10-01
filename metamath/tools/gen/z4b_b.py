"""Sortie Z4b, section B: the trigonometric polynomial f ( t ) = sum_n A ( n ) e ( ( n - M ) t ),
its derivative and continuity, and the finite Parseval identity over a unit
period (LargeSieve parseval_period)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z4blib import *
from z4alib import win
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def hwm(w, A0):
    P = parts(w, A0)
    hw = P[HW]; mz = P['M e. ZZ']
    return P, hw, mz


def nctx(w, An, hw, mz, n='n'):
    """under An ( containing n e. W ): steps nz, an, ( n - M ) e. ZZ"""
    nmem = w.s([], 'simpr', '( %s -> %s e. W )' % (An, n))
    nz, an = win(w, An, lift(w, hw, An), nmem, n)
    nm = st(w, An, [nz, lift(w, mz, An)], 'zsubcld', '( %s - M ) e. ZZ' % n)
    return nmem, nz, an, nm


if __name__ == '__main__':
    # ---- lsdw
    A0 = HWM
    w = W('lsdw', 'The derivative weights of a trigonometric polynomial form a function on the window.')
    P, hw, mz = hwm(w, A0)
    Aj = '( %s /\\ j e. W )' % A0
    jm, jz, aj, jmz = nctx(w, Aj, hw, mz, 'j')
    c2 = lift(w, c2cl(w, A0), Aj)
    w.qed([st(w, Aj, [aj, st(w, Aj, [c2, st(w, Aj, [jmz], 'zcnd', '( j - M ) e. CC')], 'mulcld', '( %s x. ( j - M ) ) e. CC' % C2)], 'mulcld',
              '( ( A ` j ) x. ( %s x. ( j - M ) ) ) e. CC' % C2)], 'fmptd', STATEMENTS['lsdw']); go(w)

    # ---- lstrigdv
    w = W('lstrigdv', 'The derivative of a trigonometric polynomial f ( t ) = sum_n A ( n ) e ( ( n - M ) t ) is the trigonometric polynomial with the weights A ( n ) 2 pi i ( n - M ).')
    P, hw, mz = hwm(w, A0)
    wf = st(w, A0, [hw], 'simp1d', 'W e. Fin')
    TOP = '( TopOpen ` CCfld )'; JR = '( %s |`t RR )' % TOP
    jeq = w.s([], 'eqid', '%s = %s' % (JR, JR)); keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    rr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    kt = w.s([keq], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)
    rt = w.s([kt, w.s([], 'ax-resscn', 'RR C_ CC'), w.inst('resttopon')], 'mp2an', '%s e. ( TopOn ` RR )' % JR)
    rj = w.s([w.s([rt, w.inst('toponmax')], 'ax-mp', 'RR e. %s' % JR)], 'a1i', '( %s -> RR e. %s )' % (A0, JR))
    Ant = '( %s /\\ n e. W /\\ t e. RR )' % A0
    An = '( %s /\\ n e. W )' % A0
    nmem, nz, an, nm = nctx(w, An, hw, mz)
    E = EAT('( n - M )', 't'); K = '( %s x. ( n - M ) )' % C2
    nmc = st(w, An, [nm], 'zcnd', '( n - M ) e. CC')
    tr = w.s([], 'simp3', '( %s -> t e. RR )' % Ant); tc = st(w, Ant, [tr], 'recnd', 't e. CC')
    an3 = w.s([an], '3adant3', '( %s -> ( A ` n ) e. CC )' % Ant); nmc3 = w.s([nmc], '3adant3', '( %s -> ( n - M ) e. CC )' % Ant)
    ec = ap(w, Ant, 'eatcl', [nmc3, tc], '%s e. CC' % E)
    c23 = lift(w, c2cl(w, A0), Ant)
    kc = st(w, Ant, [c23, nmc3], 'mulcld', '%s e. CC' % K)
    ke = st(w, Ant, [kc, ec], 'mulcld', '( %s x. %s ) e. CC' % (K, E))
    ta = st(w, Ant, [an3, ec], 'mulcld', '( ( A ` n ) x. %s ) e. CC' % E)
    tb = st(w, Ant, [an3, ke], 'mulcld', '( ( A ` n ) x. ( %s x. %s ) ) e. CC' % (K, E))
    Anx = '( %s /\\ t e. RR )' % An
    ec2 = ap(w, Anx, 'eatcl', [lift(w, nmc, Anx), st(w, Anx, [w.s([], 'simpr', '( %s -> t e. RR )' % Anx)], 'recnd', 't e. CC')], '%s e. CC' % E)
    ke2 = st(w, Anx, [st(w, Anx, [lift(w, c2cl(w, A0), Anx), lift(w, nmc, Anx)], 'mulcld', '%s e. CC' % K), ec2], 'mulcld', '( %s x. %s ) e. CC' % (K, E))
    de = ap(w, An, 'eatdv', [nmc], '( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( %s x. %s ) )' % (E, K, E))
    rrn = lift(w, rr, An)
    dterm = st(w, An, [rrn, ec2, ke2, de, an], 'dvmptcmul', '( RR _D ( t e. RR |-> ( ( A ` n ) x. %s ) ) ) = ( t e. RR |-> ( ( A ` n ) x. ( %s x. %s ) ) )' % (E, K, E))
    SUMB = 'sum_ n e. W ( ( A ` n ) x. ( %s x. %s ) )' % (K, E)
    dsum = st(w, A0, [jeq, keq, rr, rj, wf, ta, tb, dterm], 'dvmptfsum', '( RR _D %s ) = ( t e. RR |-> %s )' % (FT('A'), SUMB))
    # rewrite the weights as AD ` n
    Atn = '( ( %s /\\ t e. RR ) /\\ n e. W )' % A0
    nmem2 = w.s([], 'simpr', '( %s -> n e. W )' % Atn)
    nz2, an2 = win(w, Atn, lift(w, hw, Atn), nmem2)
    nmc2 = st(w, Atn, [st(w, Atn, [nz2, lift(w, mz, Atn)], 'zsubcld', '( n - M ) e. ZZ')], 'zcnd', '( n - M ) e. CC')
    tc2 = st(w, Atn, [lift(w, w.s([], 'simpr', '( ( %s /\\ t e. RR ) -> t e. RR )' % A0), Atn)], 'recnd', 't e. CC')
    ec3 = ap(w, Atn, 'eatcl', [nmc2, tc2], '%s e. CC' % E)
    kc3 = st(w, Atn, [lift(w, c2cl(w, A0), Atn), nmc2], 'mulcld', '%s e. CC' % K)
    r1 = eqc(w, Atn, st(w, Atn, [an2, kc3, ec3], 'mulassd', '( ( ( A ` n ) x. %s ) x. %s ) = ( ( A ` n ) x. ( %s x. %s ) )' % (K, E, K, E)))
    akc = st(w, Atn, [an2, kc3], 'mulcld', '( ( A ` n ) x. %s ) e. CC' % K)
    fv = fvmd(w, Atn, 'j', 'W', '( ( A ` j ) x. ( %s x. ( j - M ) ) )' % C2, 'n', nmem2, akc)
    r2 = st(w, Atn, [eqc(w, Atn, fv)], 'oveq1d', '( ( ( A ` n ) x. %s ) x. %s ) = ( ( %s ` n ) x. %s )' % (K, E, AD, E))
    r = eqt(w, Atn, r1, r2)
    ATN = '( %s /\\ t e. RR )' % A0
    sm = st(w, ATN, [r], 'sumeq2dv', '%s = %s' % (SUMB, TRIG(AD, 't')))
    mp = st(w, A0, [sm], 'mpteq2dva', '( t e. RR |-> %s ) = %s' % (SUMB, FT(AD)))
    w.qed([dsum, mp], 'eqtrd', STATEMENTS['lstrigdv']); go(w)

    # ---- lstrigcn
    w = W('lstrigcn', 'A trigonometric polynomial is continuous on RR (from its derivative).')
    P, hw, mz = hwm(w, A0)
    wf = st(w, A0, [hw], 'simp1d', 'W e. Fin')
    def trigcl(Aname, fst):
        """( ( A0 /\\ t e. RR ) -> TRIG(Aname) e. CC ) given fst: ( A0 -> Aname : W --> CC )"""
        At = '( %s /\\ t e. RR )' % A0
        Atn = '( %s /\\ n e. W )' % At
        nmem = w.s([], 'simpr', '( %s -> n e. W )' % Atn)
        nz = st(w, Atn, [lift(w, P['W C_ ZZ'], Atn), nmem], 'sseldd', 'n e. ZZ')
        an = st(w, Atn, [lift(w, fst, Atn), nmem], 'ffvelcdmd', '( %s ` n ) e. CC' % Aname)
        nmc = st(w, Atn, [st(w, Atn, [nz, lift(w, mz, Atn)], 'zsubcld', '( n - M ) e. ZZ')], 'zcnd', '( n - M ) e. CC')
        tc = st(w, Atn, [lift(w, w.s([], 'simpr', '( %s -> t e. RR )' % At), Atn)], 'recnd', 't e. CC')
        ec = ap(w, Atn, 'eatcl', [nmc, tc], '%s e. CC' % E)
        return st(w, At, [lift(w, wf, At), st(w, Atn, [an, ec], 'mulcld', '( ( %s ` n ) x. %s ) e. CC' % (Aname, E))], 'fsumcl', '%s e. CC' % TRIG(Aname, 't'))
    fm = st(w, A0, [trigcl('A', P['A : W --> CC'])], 'fmptd', '%s : RR --> CC' % FT('A'))
    adf = ap(w, A0, 'lsdw', [P[A0] if A0 in P else w.s([], 'id', '( %s -> %s )' % (A0, A0))], '%s : W --> CC' % AD)
    ral = st(w, A0, [trigcl(AD, adf)], 'ralrimiva', 'A. t e. RR %s e. CC' % TRIG(AD, 't'))
    dm = ap(w, A0, 'dmmptg', [ral], 'dom %s = RR' % FT(AD))
    dv = ap(w, A0, 'lstrigdv', [w.s([], 'id', '( %s -> %s )' % (A0, A0))], '( RR _D %s ) = %s' % (FT('A'), FT(AD)))
    dmr = eqt(w, A0, st(w, A0, [dv], 'dmeqd', 'dom ( RR _D %s ) = dom %s' % (FT('A'), FT(AD))), dm)
    j3 = J(w, A0, a1(w, A0, 'ax-resscn', 'RR C_ CC'), fm, a1(w, A0, 'ssid', 'RR C_ RR'))
    w.qed([J(w, A0, j3, dmr), w.inst('dvcn')], 'syl', STATEMENTS['lstrigcn']); go(w)

    # ---- lsparlem1: the pointwise expansion of | f ( t ) | ^ 2
    A0 = '( %s /\\ t e. RR )' % HWM
    w = W('lsparlem1', 'The squared modulus of a trigonometric polynomial as a double sum over frequency differences (LargeSieve parseval_period, hpt).')
    P = parts(w, A0)
    hw = P[HW]; mz = P['M e. ZZ']; tr = P['t e. RR']
    wf = st(w, A0, [hw], 'simp1d', 'W e. Fin')
    S = TRIG('A', 't'); SM = TRIG('A', 't', 'm')
    def term(v):
        return '( ( A ` %s ) x. %s )' % (v, EAT('( %s - M )' % v, 't'))
    def tcl(ante, v, mem):
        vz = st(w, ante, [lift(w, P['W C_ ZZ'], ante), mem], 'sseldd', '%s e. ZZ' % v)
        av = st(w, ante, [lift(w, P['A : W --> CC'], ante), mem], 'ffvelcdmd', '( A ` %s ) e. CC' % v)
        vm = st(w, ante, [vz, lift(w, mz, ante)], 'zsubcld', '( %s - M ) e. ZZ' % v)
        e = ap(w, ante, 'eatcl', [st(w, ante, [vm], 'zcnd', '( %s - M ) e. CC' % v), st(w, ante, [lift(w, tr, ante)], 'recnd', 't e. CC')],
               '%s e. CC' % EAT('( %s - M )' % v, 't'))
        return vz, av, vm, e, st(w, ante, [av, e], 'mulcld', '%s e. CC' % term(v))
    An = '( %s /\\ n e. W )' % A0; Am = '( %s /\\ m e. W )' % A0
    _, _, _, _, tn = tcl(An, 'n', w.s([], 'simpr', '( %s -> n e. W )' % An))
    _, _, _, _, tm = tcl(Am, 'm', w.s([], 'simpr', '( %s -> m e. W )' % Am))
    sc = st(w, A0, [wf, tn], 'fsumcl', '%s e. CC' % S)
    a1s = ap(w, A0, 'absvalsq', [sc], '%s = ( %s x. ( * ` %s ) )' % (ABS2(S), S, S))
    cj = st(w, A0, [wf, tn], 'fsumcj', '( * ` %s ) = sum_ n e. W ( * ` %s )' % (S, term('n')))
    sub, _ = w.congr('( * ` %s )' % term('n'), {'n': 'm'}, 'n = m', {'n': w.s([], 'id', '( n = m -> n = m )')})
    cbv = w.s([sub], 'cbvsumv', 'sum_ n e. W ( * ` %s ) = sum_ m e. W ( * ` %s )' % (term('n'), term('m')))
    cj2 = eqt(w, A0, cj, w.s([cbv], 'a1i', '( %s -> sum_ n e. W ( * ` %s ) = sum_ m e. W ( * ` %s ) )' % (A0, term('n'), term('m'))))
    p1 = st(w, A0, [cj2], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. sum_ m e. W ( * ` %s ) )' % (S, S, S, term('m')))
    cjm = st(w, Am, [tm], 'cjcld', '( * ` %s ) e. CC' % term('m'))
    f2 = st(w, A0, [wf, wf, tn, cjm], 'fsum2mul', 'sum_ n e. W sum_ m e. W ( %s x. ( * ` %s ) ) = ( %s x. sum_ m e. W ( * ` %s ) )' % (term('n'), term('m'), S, term('m')))
    # the summand
    Anm = '( ( %s /\\ n e. W ) /\\ m e. W )' % A0
    nmem = lift(w, w.s([], 'simpr', '( %s -> n e. W )' % An), Anm); mmem = w.s([], 'simpr', '( %s -> m e. W )' % Anm)
    nz, an, nmz, en, _ = tcl(Anm, 'n', nmem)
    mz_, am, mmz, em, _ = tcl(Anm, 'm', mmem)
    En = EAT('( n - M )', 't'); Em = EAT('( m - M )', 't'); CAm = '( * ` ( A ` m ) )'; CEm = '( * ` %s )' % Em
    q1 = st(w, Anm, [am, em], 'cjmuld', '( * ` %s ) = ( %s x. %s )' % (term('m'), CAm, CEm))
    q2 = st(w, Anm, [q1], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. ( %s x. %s ) )' % (term('n'), term('m'), term('n'), CAm, CEm))
    cam = st(w, Anm, [am], 'cjcld', '%s e. CC' % CAm); cem = st(w, Anm, [em], 'cjcld', '%s e. CC' % CEm)
    q3 = st(w, Anm, [an, en, cam, cem], 'mul4d', '( %s x. ( %s x. %s ) ) = ( ( ( A ` n ) x. %s ) x. ( %s x. %s ) )' % (term('n'), CAm, CEm, CAm, En, CEm))
    mmr = st(w, Anm, [mmz], 'zred', '( m - M ) e. RR'); trr = lift(w, tr, Anm)
    q4 = ap(w, Anm, 'eatcj', [mmr, trr], '%s = %s' % (CEm, EAT('-u ( m - M )', 't')))
    q5 = st(w, Anm, [q4], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (En, CEm, En, EAT('-u ( m - M )', 't')))
    nmc = st(w, Anm, [nmz], 'zcnd', '( n - M ) e. CC'); mmc = st(w, Anm, [mmz], 'zcnd', '( m - M ) e. CC')
    tcn = st(w, Anm, [trr], 'recnd', 't e. CC')
    q6 = eqc(w, Anm, ap(w, Anm, 'eatadd', [nmc, st(w, Anm, [mmc], 'negcld', '-u ( m - M ) e. CC'), tcn],
                        '%s = ( %s x. %s )' % (EAT('( ( n - M ) + -u ( m - M ) )', 't'), En, EAT('-u ( m - M )', 't'))))
    ncc = st(w, Anm, [nz], 'zcnd', 'n e. CC'); mcc = st(w, Anm, [mz_], 'zcnd', 'm e. CC'); Mc = st(w, Anm, [lift(w, mz, Anm)], 'zcnd', 'M e. CC')
    q7 = eqt(w, Anm, st(w, Anm, [nmc, mmc], 'negsubd', '( ( n - M ) + -u ( m - M ) ) = ( ( n - M ) - ( m - M ) )'),
             st(w, Anm, [ncc, mcc, Mc], 'nnncan2d', '( ( n - M ) - ( m - M ) ) = ( n - m )'))
    q8 = st(w, Anm, [st(w, Anm, [st(w, Anm, [q7], 'oveq1d', '( ( ( n - M ) + -u ( m - M ) ) x. t ) = ( ( n - m ) x. t )')], 'oveq2d',
                                  '( %s x. ( ( ( n - M ) + -u ( m - M ) ) x. t ) ) = ( %s x. ( ( n - m ) x. t ) )' % (C2, C2))], 'fveq2d',
            '%s = %s' % (EAT('( ( n - M ) + -u ( m - M ) )', 't'), EAT('( n - m )', 't')))
    q9 = eqt(w, Anm, eqt(w, Anm, q5, q6), q8)
    q10 = st(w, Anm, [q9], 'oveq2d', '( ( ( A ` n ) x. %s ) x. ( %s x. %s ) ) = ( ( ( A ` n ) x. %s ) x. %s )' % (CAm, En, CEm, CAm, EAT('( n - m )', 't')))
    summ = eqt(w, Anm, eqt(w, Anm, q2, q3), q10)
    s1 = st(w, An, [summ], 'sumeq2dv', 'sum_ m e. W ( %s x. ( * ` %s ) ) = sum_ m e. W ( ( ( A ` n ) x. %s ) x. %s )' % (term('n'), term('m'), CAm, EAT('( n - m )', 't')))
    s2 = st(w, A0, [s1], 'sumeq2dv', 'sum_ n e. W sum_ m e. W ( %s x. ( * ` %s ) ) = sum_ n e. W sum_ m e. W ( ( ( A ` n ) x. %s ) x. %s )' % (term('n'), term('m'), CAm, EAT('( n - m )', 't')))
    fin = eqt(w, A0, eqt(w, A0, eqt(w, A0, a1s, p1), eqc(w, A0, f2)), s2)
    last = w.lines.pop(); w.lines.append('qed' + last[len(fin):]); go(w)

    # ---- lsparlem2: the inner integral at one n
    O = IOO('C', '( C + 1 )')
    A0 = '( ( %s /\\ C e. RR ) /\\ n e. W )' % HWM
    w = W('lsparlem2', 'Lemma for lsparper: at a fixed frequency n, the integral over a unit period of the row sum_m A ( n ) conj A ( m ) e ( ( n - m ) t ) is | A ( n ) | ^ 2 (LargeSieve parseval_period, hone).')
    P = parts(w, A0)
    hw, mz, cr, nmem = P[HW], P['M e. ZZ'], P['C e. RR'], P['n e. W']
    wf = st(w, A0, [hw], 'simp1d', 'W e. Fin')
    nz, an = win(w, A0, hw, nmem)
    CNM = '( ( A ` n ) x. ( * ` ( A ` m ) ) )'; E = EAT('( n - m )', 't')
    Am = '( %s /\\ m e. W )' % A0
    Lm = lambda s_: lift(w, s_, Am)
    mmem = w.s([], 'simpr', '( %s -> m e. W )' % Am)
    mz_, am = win(w, Am, Lm(hw), mmem, 'm')
    cnm = st(w, Am, [Lm(an), st(w, Am, [am], 'cjcld', '( * ` ( A ` m ) ) e. CC')], 'mulcld', '%s e. CC' % CNM)
    nmz = st(w, Am, [Lm(nz), mz_], 'zsubcld', '( n - m ) e. ZZ'); nmc = st(w, Am, [nmz], 'zcnd', '( n - m ) e. CC')
    c1r = st(w, Am, [Lm(cr), w.s([], '1red', '( %s -> 1 e. RR )' % Am)], 'readdcld', '( C + 1 ) e. RR')
    ibE = w.s([Lm(cr), c1r, ap(w, Am, 'eatcn', [nmc], '( t e. RR |-> %s ) e. %s' % (E, CNR))], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (Am, O, E))
    Amt = '( %s /\\ t e. %s )' % (Am, O)
    tr = ap(w, Amt, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Amt, O))], 't e. RR')
    ec = ap(w, Amt, 'eatcl', [lift(w, nmc, Amt), st(w, Amt, [tr], 'recnd', 't e. CC')], '%s e. CC' % E)
    ibT = st(w, Am, [cnm, ec, ibE], 'iblmulc2', '( t e. %s |-> ( %s x. %s ) ) e. L^1' % (O, CNM, E))
    # itgfsum wants the body closure under ( A0 /\\ ( t e. O /\\ m e. W ) )
    Atm = '( %s /\\ ( t e. %s /\\ m e. W ) )' % (A0, O)
    re_ = st(w, Atm, [w.s([], 'simpl', '( %s -> %s )' % (Atm, A0)), w.s([], 'simprr', '( %s -> m e. W )' % Atm)], 'jca', '%s' % Am)
    re2 = st(w, Atm, [re_, w.s([], 'simprl', '( %s -> t e. %s )' % (Atm, O))], 'jca', Amt)
    bcl = w.s([re2, st(w, Amt, [lift(w, cnm, Amt), ec], 'mulcld', '( %s x. %s ) e. CC' % (CNM, E))], 'syl', '( %s -> ( %s x. %s ) e. CC )' % (Atm, CNM, E))
    SUMM = 'sum_ m e. W ( %s x. %s )' % (CNM, E)
    fs = st(w, A0, [a1(w, A0, 'ioombl', '%s e. dom vol' % O), wf, bcl, ibT], 'itgfsum',
            '( ( t e. %s |-> %s ) e. L^1 /\\ %s = sum_ m e. W %s )' % (O, SUMM, ITG(O, SUMM), ITG(O, '( %s x. %s )' % (CNM, E))))
    # each term
    mc = eqc(w, Am, st(w, Am, [cnm, ec, ibE], 'itgmulc2', '( %s x. %s ) = %s' % (CNM, ITG(O, E), ITG(O, '( %s x. %s )' % (CNM, E)))))
    ei = ap(w, Am, 'eatitg', [nmz, Lm(cr)], '%s = if ( ( n - m ) = 0 , 1 , 0 )' % ITG(O, E))
    t1 = st(w, Am, [ei], 'oveq2d', '( %s x. %s ) = ( %s x. if ( ( n - m ) = 0 , 1 , 0 ) )' % (CNM, ITG(O, E), CNM))
    t2 = a1(w, Am, 'ovif2', '( %s x. if ( ( n - m ) = 0 , 1 , 0 ) ) = if ( ( n - m ) = 0 , ( %s x. 1 ) , ( %s x. 0 ) )' % (CNM, CNM, CNM))
    t3 = st(w, Am, [st(w, Am, [cnm], 'mulridd', '( %s x. 1 ) = %s' % (CNM, CNM)), st(w, Am, [cnm], 'mul01d', '( %s x. 0 ) = 0' % CNM)], 'ifeq12d',
            'if ( ( n - m ) = 0 , ( %s x. 1 ) , ( %s x. 0 ) ) = if ( ( n - m ) = 0 , %s , 0 )' % (CNM, CNM, CNM))
    bi = st(w, Am, [st(w, Am, [st(w, Am, [Lm(nz)], 'zcnd', 'n e. CC'), st(w, Am, [mz_], 'zcnd', 'm e. CC')], 'subeq0ad', '( ( n - m ) = 0 <-> n = m )'),
                    a1(w, Am, 'eqcom', '( n = m <-> m = n )')], 'bitrd', '( ( n - m ) = 0 <-> m = n )')
    t4 = st(w, Am, [bi], 'ifbid', 'if ( ( n - m ) = 0 , %s , 0 ) = if ( m = n , %s , 0 )' % (CNM, CNM))
    term = eqt(w, Am, eqt(w, Am, eqt(w, Am, eqt(w, Am, mc, t1), t2), t3), t4)
    sm = st(w, A0, [term], 'sumeq2dv', 'sum_ m e. W %s = sum_ m e. W if ( m = n , %s , 0 )' % (ITG(O, '( %s x. %s )' % (CNM, E)), CNM))
    sub, _ = w.congr(CNM, {'m': 'n'}, 'm = n', {'m': w.s([], 'id', '( m = n -> m = n )')})
    CNN = '( ( A ` n ) x. ( * ` ( A ` n ) ) )'
    si = st(w, A0, [sub, wf, nmem, st(w, A0, [an, st(w, A0, [an], 'cjcld', '( * ` ( A ` n ) ) e. CC')], 'mulcld', '%s e. CC' % CNN)], 'sumite', 'sum_ m e. W if ( m = n , %s , 0 ) = %s' % (CNM, CNN))
    av = eqc(w, A0, ap(w, A0, 'absvalsq', [an], '( ( abs ` ( A ` n ) ) ^ 2 ) = %s' % CNN))
    val = eqt(w, A0, eqt(w, A0, eqt(w, A0, st(w, A0, [fs], 'simprd', '%s = sum_ m e. W %s' % (ITG(O, SUMM), ITG(O, '( %s x. %s )' % (CNM, E)))), sm), si), av)
    w.qed([st(w, A0, [fs], 'simpld', '( t e. %s |-> %s ) e. L^1' % (O, SUMM)), val], 'jca', STATEMENTS['lsparlem2']); go(w)

    # ---- lsparper
    A0 = '( %s /\\ C e. RR )' % HWM
    w = W('lsparper', 'Finite Parseval over a unit period: the integral over ( C , C + 1 ) of | sum_n A ( n ) e ( ( n - M ) t ) | ^ 2 is sum_n | A ( n ) | ^ 2 (LargeSieve parseval_period).')
    P = parts(w, A0)
    hwm, hw, cr = P[HWM], P[HW], P['C e. RR']
    wf = st(w, A0, [hw], 'simp1d', 'W e. Fin')
    DS = 'sum_ n e. W sum_ m e. W ( ( ( A ` n ) x. ( * ` ( A ` m ) ) ) x. %s )' % EAT('( n - m )', 't')
    INN = 'sum_ m e. W ( ( ( A ` n ) x. ( * ` ( A ` m ) ) ) x. %s )' % EAT('( n - m )', 't')
    At = '( %s /\\ t e. %s )' % (A0, O)
    tr = ap(w, At, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (At, O))], 't e. RR')
    pl = ap(w, At, 'lsparlem1', [J(w, At, lift(w, hwm, At), tr)], '%s = %s' % (ABS2(TRIG('A', 't')), DS))
    i1 = st(w, A0, [pl], 'itgeq2dv', '%s = %s' % (ITG(O, ABS2(TRIG('A', 't'))), ITG(O, DS)))
    An = '( %s /\\ n e. W )' % A0
    l2 = ap(w, An, 'lsparlem2', [w.s([], 'id', '( %s -> %s )' % (An, An))], STATEMENTS['lsparlem2'].split(' -> ', 1)[1][:-2])
    ibn = st(w, An, [l2], 'simpld', '( t e. %s |-> %s ) e. L^1' % (O, INN))
    vn = st(w, An, [l2], 'simprd', '%s = ( ( abs ` ( A ` n ) ) ^ 2 )' % ITG(O, INN))
    # the inner sum is a complex number at each t
    Atn = '( %s /\\ ( t e. %s /\\ n e. W ) )' % (A0, O)
    Atn2 = '( ( %s /\\ n e. W ) /\\ t e. %s )' % (A0, O)
    Atnm = '( %s /\\ m e. W )' % Atn2
    nm_ = lift(w, w.s([], 'simpr', '( %s -> n e. W )' % An), Atnm)
    nz, an = win(w, Atnm, lift(w, hw, Atnm), nm_)
    mz_, am = win(w, Atnm, lift(w, hw, Atnm), w.s([], 'simpr', '( %s -> m e. W )' % Atnm), 'm')
    trm = lift(w, ap(w, Atn2, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Atn2, O))], 't e. RR'), Atnm)
    ecm = ap(w, Atnm, 'eatcl', [st(w, Atnm, [st(w, Atnm, [nz, mz_], 'zsubcld', '( n - m ) e. ZZ')], 'zcnd', '( n - m ) e. CC'), st(w, Atnm, [trm], 'recnd', 't e. CC')],
             '%s e. CC' % EAT('( n - m )', 't'))
    bdy = st(w, Atnm, [st(w, Atnm, [an, st(w, Atnm, [am], 'cjcld', '( * ` ( A ` m ) ) e. CC')], 'mulcld', '( ( A ` n ) x. ( * ` ( A ` m ) ) ) e. CC'), ecm], 'mulcld',
             '( ( ( A ` n ) x. ( * ` ( A ` m ) ) ) x. %s ) e. CC' % EAT('( n - m )', 't'))
    inn = st(w, Atn2, [lift(w, wf, Atn2), bdy], 'fsumcl', '%s e. CC' % INN)
    inn2 = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Atn, A0)), w.s([], 'simprr', '( %s -> n e. W )' % Atn)], 'jca', '( %s -> %s )' % (Atn, An)),
                     w.s([], 'simprl', '( %s -> t e. %s )' % (Atn, O))], 'jca', '( %s -> %s )' % (Atn, Atn2)), inn], 'syl', '( %s -> %s e. CC )' % (Atn, INN))
    fs = st(w, A0, [a1(w, A0, 'ioombl', '%s e. dom vol' % O), wf, inn2, ibn], 'itgfsum',
            '( ( t e. %s |-> %s ) e. L^1 /\\ %s = sum_ n e. W %s )' % (O, DS, ITG(O, DS), ITG(O, INN)))
    i2 = st(w, A0, [fs], 'simprd', '%s = sum_ n e. W %s' % (ITG(O, DS), ITG(O, INN)))
    i3 = st(w, A0, [vn], 'sumeq2dv', 'sum_ n e. W %s = %s' % (ITG(O, INN), SW('A')))
    fin = eqt(w, A0, eqt(w, A0, i1, i2), i3); qedlast(w); go(w)
