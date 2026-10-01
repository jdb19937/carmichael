"""Sortie T21b: t21efa (explicit_formula_all)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *

RNG = '( 1 ... ( |_ ` Y ) )'


def PS(n, x):
    return 'sum_ n e. %s ( ( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` n ) ) x. ( Lam ` n ) )' % (RNG, x, n)


def gen_efa():
    w = W('t21efa', 'The explicit formula for every character mod ` N ` , principal included: the principal character through the level-1 formula ( ` zeta ` ), with the imprimitive correction ` omega ( N ) log Y ` (Lean ` explicit_formula_all ` ; ~ ef6ef , ~ t21zse , ~ t21psd ).')
    A0, concl = split_imp(SB['t21efa'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    nn = u['N e. NN']; xb = u['X e. ( Base ` ( DChr ` N ) )']; yr = u['Y e. RR']; y100 = u['; ; 1 0 0 <_ Y']; tr = u['T e. RR']; t2 = u['2 <_ T']; ny = u['N <_ Y']
    y1 = lin.linarith(w, A0, [y100], '1 <_ Y', leaves={'Y': yr})
    nr = s([nn], 'nnred', 'N e. RR')
    n1 = s([nn], 'nnge1d', '1 <_ N')
    EFN = EFERR('N', 'T', 'Y'); EF1 = EFERR('1', 'T', 'Y')
    OML = '( %s x. ( log ` Y ) )' % OM('N')
    pN = eferr_parts(w, A0, 'N', nr, n1, yr, y1, tr, t2)
    omr = s([s([s([s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OM('N'))], 'nn0red', '%s e. RR' % OM('N'))], 'x', 'x') if False else None
    omn = s([s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OM('N'))
    lyr = s([pN['yp']], 'relogcld', '( log ` Y ) e. RR')
    ly0 = ap(w, A0, [yr, y1], 'logge0', '0 <_ ( log ` Y )')
    omlr = s([s([omn], 'nn0red', '%s e. RR' % OM('N')), lyr], 'remulcld', '%s e. RR' % OML)
    oml0 = s([s([omn], 'nn0red', '%s e. RR' % OM('N')), lyr, s([omn], 'nn0ge0d', '0 <_ %s' % OM('N')), ly0], 'mulge0d', '0 <_ %s' % OML)
    rhs_ge = s([pN['er'], omlr], 'addge01d', '( 0 <_ %s <-> %s <_ ( %s + %s ) )' % (OML, EFN, EFN, OML))
    rhs_ge = s([oml0, rhs_ge], 'mpbid', '%s <_ ( %s + %s )' % (EFN, EFN, OML))
    PSI = '( X ( psiChar ` N ) Y )'
    IFX = 'if ( X = %s , Y , 0 )' % U0
    SCN = SC(EN, 'T', 'Y')
    LHS = '( abs ` ( ( %s - %s ) + %s ) )' % (PSI, IFX, SCN)
    pv = s([s([nn, xb, yr], '3jca', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) /\\ Y e. RR )'), w.inst('psicharval')], 'syl', '%s = %s' % (PSI, PS('N', 'X')))
    lhs_eq = s([s([s([pv], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (PSI, IFX, PS('N', 'X'), IFX))], 'oveq1d', '( ( %s - %s ) + %s ) = ( ( %s - %s ) + %s )' % (PSI, IFX, SCN, PS('N', 'X'), IFX, SCN))], 'fveq2d',
               '%s = ( abs ` ( ( %s - %s ) + %s ) )' % (LHS, PS('N', 'X'), IFX, SCN))
    # ---- nonprincipal
    An = '( %s /\\ X =/= %s )' % (A0, U0)
    sn = S_(w, An)
    L = lambda st: lift(w, st, An)
    DJ = '( X =/= %s \\/ ( N = 1 /\\ X = %s ) )' % (U0, U0)
    dj = sn([sn([], 'simpr', 'X =/= %s' % U0)], 'orcd', DJ)
    ef = ap(w, An, [L(nn), L(xb), dj, L(yr), L(y100), L(tr), L(t2), L(ny)], 'ef6ef', '( abs ` ( ( %s - %s ) + %s ) ) <_ %s' % (PS('N', 'X'), IFX, SCN, EFN))
    lhsr = s([s([s([s([s([nn, xb, yr], '3jca', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) /\\ Y e. RR )'), w.inst('psicharcl')], 'syl', '%s e. CC' % PSI),
                    s([s([yr], 'recnd', 'Y e. CC'), s([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFX)], 'subcld', '( %s - %s ) e. CC' % (PSI, IFX)),
                 sc_cc(w, A0, 'N', 'X', nn, xb, tr, yr)], 'addcld', '( ( %s - %s ) + %s ) e. CC' % (PSI, IFX, SCN))], 'abscld', '%s e. RR' % LHS)
    case_n = sn([L(lhsr), L(pN['er']), sn([L(pN['er']), L(omlr)], 'readdcld', '( %s + %s ) e. RR' % (EFN, OML)), sn([L(lhs_eq), ef], 'eqbrtrd', '%s <_ %s' % (LHS, EFN)), L(rhs_ge)], 'letrd',
                '%s <_ ( %s + %s )' % (LHS, EFN, OML))
    # ---- principal
    Ap = '( %s /\\ X = %s )' % (A0, U0)
    sp = S_(w, Ap)
    P_ = lambda st: lift(w, st, Ap)
    xu = sp([], 'simpr', 'X = %s' % U0)
    one = sp([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    import t21b_ps
    ab1, gi1 = t21b_ps.u0base(w, Ap, '1')
    u1b = sp([w.s([w.s([w.s([w.s([], '1nn', '1 e. NN'), ab1], 'ax-mp', '( DChr ` 1 ) e. Abel'), w.inst('ablgrp')], 'ax-mp', '( DChr ` 1 ) e. Grp'), gi1], 'ax-mp', '%s e. ( Base ` ( DChr ` 1 ) )' % U01)], 'a1i',
             '%s e. ( Base ` ( DChr ` 1 ) )' % U01)
    DJ1 = '( %s =/= %s \\/ ( 1 = 1 /\\ %s = %s ) )' % (U01, U01, U01, U01)
    dj1 = sp([sp([sp([w.s([], 'eqid', '1 = 1')], 'a1i', '1 = 1'), sp([w.s([], 'eqid', '%s = %s' % (U01, U01))], 'a1i', '%s = %s' % (U01, U01))], 'jca', '( 1 = 1 /\\ %s = %s )' % (U01, U01))], 'olcd', DJ1)
    IF1 = 'if ( %s = %s , Y , 0 )' % (U01, U01)
    SC1 = SC(E1, 'T', 'Y')
    y1p = P_(y1)
    ef1 = ap(w, Ap, [one, u1b, dj1, P_(yr), P_(y100), P_(tr), P_(t2), y1p], 'ef6ef', '( abs ` ( ( %s - %s ) + %s ) ) <_ %s' % (PS('1', U01), IF1, SC1, EF1))
    it1 = sp([w.s([w.s([], 'eqid', '%s = %s' % (U01, U01)), w.s([], 'iftrue', '( %s = %s -> %s = Y )' % (U01, U01, IF1))], 'ax-mp', '%s = Y' % IF1)], 'a1i', '%s = Y' % IF1)
    PS1 = '( %s ( psiChar ` 1 ) Y )' % U01
    pv1 = sp([sp([one, u1b, P_(yr)], '3jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) /\\ Y e. RR )' % U01), w.inst('psicharval')], 'syl', '%s = %s' % (PS1, PS('1', U01)))
    B1 = '( abs ` ( ( %s - Y ) + %s ) )' % (PS1, SC1)
    b1eq = sp([sp([sp([sp([pv1, sp([it1], 'eqcomd', 'Y = %s' % IF1)], 'oveq12d', '( %s - Y ) = ( %s - %s )' % (PS1, PS('1', U01), IF1))], 'oveq1d', '( ( %s - Y ) + %s ) = ( ( %s - %s ) + %s )' % (PS1, SC1, PS('1', U01), IF1, SC1))], 'fveq2d',
                  '%s = ( abs ` ( ( %s - %s ) + %s ) )' % (B1, PS('1', U01), IF1, SC1)), ef1], 'eqbrtrd', '%s <_ %s' % (B1, EF1))
    # LHS rewrite: if -> Y, SC_N -> SC_1, psiChar X -> psiChar U0
    itx = sp([xu, w.s([], 'iftrue', '( X = %s -> %s = Y )' % (U0, IFX))], 'syl', '%s = Y' % IFX)
    zse = ap(w, Ap, [P_(nn), P_(xb), xu, P_(tr), P_(s([yr], 'recnd', 'Y e. CC'))], 't21zse', '%s = %s' % (SCN, SC1))
    PSU = '( %s ( psiChar ` N ) Y )' % U0
    pxu = sp([xu], 'oveq1d', '( X ( psiChar ` N ) ) = ( %s ( psiChar ` N ) )' % U0) if False else sp([xu, w.s([], 'oveq1', '( X = %s -> ( X ( psiChar ` N ) Y ) = ( %s ( psiChar ` N ) Y ) )' % (U0, U0))], 'syl', '%s = %s' % (PSI, PSU))
    l2 = sp([sp([pxu, itx], 'oveq12d', '( %s - %s ) = ( %s - Y )' % (PSI, IFX, PSU)), zse], 'oveq12d', '( ( %s - %s ) + %s ) = ( ( %s - Y ) + %s )' % (PSI, IFX, SCN, PSU, SC1))
    # ( ( a - y ) + s ) = ( ( a - b ) + ( ( b - y ) + s ) )
    import t21b_ps as _ps
    ab_, gi_ = _ps.u0base(w, Ap)
    u0b = sp([sp([sp([P_(nn), ab_], 'syl', '( DChr ` N ) e. Abel'), w.inst('ablgrp')], 'syl', '( DChr ` N ) e. Grp'), gi_], 'syl', '%s e. ( Base ` ( DChr ` N ) )' % U0)
    pac = sp([sp([P_(nn), u0b, P_(yr)], '3jca', '( N e. NN /\\ %s e. ( Base ` ( DChr ` N ) ) /\\ Y e. RR )' % U0), w.inst('psicharcl')], 'syl', '%s e. CC' % PSU)
    pbc = sp([sp([one, u1b, P_(yr)], '3jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) /\\ Y e. RR )' % U01), w.inst('psicharcl')], 'syl', '%s e. CC' % PS1)
    yc = sp([P_(yr)], 'recnd', 'Y e. CC')
    s1c = sc_cc(w, Ap, '1', U01, one, u1b, P_(tr), P_(yr))
    e1 = sp([pac, pbc, yc], 'npncand', '( ( %s - %s ) + ( %s - Y ) ) = ( %s - Y )' % (PSU, PS1, PS1, PSU))
    D1 = '( %s - %s )' % (PSU, PS1)
    e2 = sp([sp([pac, pbc], 'subcld', '%s e. CC' % D1), sp([pbc, yc], 'subcld', '( %s - Y ) e. CC' % PS1), s1c], 'addassd', '( ( %s + ( %s - Y ) ) + %s ) = ( %s + ( ( %s - Y ) + %s ) )' % (D1, PS1, SC1, D1, PS1, SC1))
    e3 = sp([sp([sp([e1], 'eqcomd', '( %s - Y ) = ( %s + ( %s - Y ) )' % (PSU, D1, PS1))], 'oveq1d', '( ( %s - Y ) + %s ) = ( ( %s + ( %s - Y ) ) + %s )' % (PSU, SC1, D1, PS1, SC1)), e2], 'eqtrd',
            '( ( %s - Y ) + %s ) = ( %s + ( ( %s - Y ) + %s ) )' % (PSU, SC1, D1, PS1, SC1))
    INN = '( ( %s - Y ) + %s )' % (PS1, SC1)
    tri = sp([sp([pac, pbc], 'subcld', '%s e. CC' % D1), sp([sp([pbc, yc], 'subcld', '( %s - Y ) e. CC' % PS1), s1c], 'addcld', '%s e. CC' % INN)], 'abstrid', '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (D1, INN, D1, INN))
    psd = ap(w, Ap, [P_(nn), P_(yr), P_(y1)], 't21psd', '( abs ` %s ) <_ %s' % (D1, OML))
    pE1 = eferr_parts(w, Ap, '1', sp([], '1red', '1 e. RR'), sp([sp([], '1red', '1 e. RR')], 'leidd', '1 <_ 1'), P_(yr), P_(y1), P_(tr), P_(t2))
    # EF1 <_ EFN
    pNp = {k: (P_(v) if isinstance(v, str) and v.startswith(('s', 'i', 'm', 'c')) and k not in ('L1', 'L2', 'NTY', 'N2', 'NT') else v) for k, v in pN.items()}
    L11, L1N, L21, L2N = pE1['L1'], pN['L1'], pE1['L2'], pN['L2']
    one_r = sp([], '1red', '1 e. RR')
    ntr1 = sp([pE1['ntp']], 'rpred', '%s e. RR' % pE1['NT'])
    # ( 1 x. T ) <_ ( N x. T ) , ( ( 1 x. T ) x. Y ) <_ ( ( N x. T ) x. Y ), ( 1 x. ( T + 2 ) ) <_ ( N x. ( T + 2 ) )
    t0 = lin.linarith(w, Ap, [P_(t2)], '0 <_ T', leaves={'T': P_(tr)})
    y0 = lin.linarith(w, Ap, [P_(y1)], '0 <_ Y', leaves={'Y': P_(yr)})
    m1 = sp([one_r, P_(nr), P_(tr), t0, P_(n1)], 'lemul1ad', '( 1 x. T ) <_ ( N x. T )')
    m2 = sp([ntr1, sp([pN['ntp']], 'x', 'x') if False else sp([P_(pN['ntp'])], 'rpred', '( N x. T ) e. RR'), P_(yr), y0, m1], 'lemul1ad', '( ( 1 x. T ) x. Y ) <_ ( ( N x. T ) x. Y )')
    t2r_ = P_(pN['t2r'])
    m3 = sp([one_r, P_(nr), t2r_, lin.linarith(w, Ap, [P_(t2)], '0 <_ ( T + 2 )', leaves={'T': P_(tr)}), P_(n1)], 'lemul1ad', '( 1 x. ( T + 2 ) ) <_ ( N x. ( T + 2 ) )')
    lg1 = sp([m2, sp([pE1['ntyp'], P_(pN['ntyp'])], 'logled', '( ( ( 1 x. T ) x. Y ) <_ ( ( N x. T ) x. Y ) <-> %s <_ %s )' % (L11, L1N))], 'mpbid', '%s <_ %s' % (L11, L1N))
    lg2 = sp([m3, sp([pE1['n2p'], P_(pN['n2p'])], 'logled', '( ( 1 x. ( T + 2 ) ) <_ ( N x. ( T + 2 ) ) <-> %s <_ %s )' % (L21, L2N))], 'mpbid', '%s <_ %s' % (L21, L2N))
    sq1 = sp([lg1, sp([pE1['l1r'], P_(pN['l1r']), pE1['l10'], P_(pN['l10'])], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (L11, L1N, L11, L1N))], 'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (L11, L1N))
    sq2 = sp([lg2, sp([pE1['l2r'], P_(pN['l2r']), pE1['l20'], P_(pN['l20'])], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (L21, L2N, L21, L2N))], 'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (L21, L2N))
    Y58 = '( Y ^c ( 5 / 8 ) )'
    q1 = sp([pE1['l1s'], P_(pN['l1s']), P_(yr), y0, sq1], 'lemul2ad', '( Y x. ( %s ^ 2 ) ) <_ ( Y x. ( %s ^ 2 ) )' % (L11, L1N))
    q1b = sp([sp([P_(yr), pE1['l1s']], 'remulcld', '( Y x. ( %s ^ 2 ) ) e. RR' % L11), sp([P_(yr), P_(pN['l1s'])], 'remulcld', '( Y x. ( %s ^ 2 ) ) e. RR' % L1N), P_(pN['tp']), q1], 'lediv1dd',
             '( ( Y x. ( %s ^ 2 ) ) / T ) <_ ( ( Y x. ( %s ^ 2 ) ) / T )' % (L11, L1N))
    y58r = P_(s([pN['y58']], 'rpred', '%s e. RR' % Y58))
    y580 = P_(s([pN['y58']], 'rpge0d', '0 <_ %s' % Y58))
    q2 = sp([pE1['l2s'], P_(pN['l2s']), y58r, y580, sq2], 'lemul2ad', '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( %s ^ 2 ) )' % (Y58, L21, Y58, L2N))
    A1a = '( ( Y x. ( %s ^ 2 ) ) / T )' % L11; A1b = '( ( Y x. ( %s ^ 2 ) ) / T )' % L1N
    A2a = '( %s x. ( %s ^ 2 ) )' % (Y58, L21); A2b = '( %s x. ( %s ^ 2 ) )' % (Y58, L2N)
    q12 = sp([pE1['a1r'], pE1['a2r'], P_(pN['a1r']), P_(pN['a2r']), q1b, q2], 'le2addd', '( %s + %s ) <_ ( %s + %s )' % (A1a, A2a, A1b, A2b))
    q123 = sp([sp([pE1['a1r'], pE1['a2r']], 'readdcld', '( %s + %s ) e. RR' % (A1a, A2a)), pE1['l1s'], sp([P_(pN['a1r']), P_(pN['a2r'])], 'readdcld', '( %s + %s ) e. RR' % (A1b, A2b)), P_(pN['l1s']), q12, sq1], 'le2addd',
              '( ( %s + %s ) + ( %s ^ 2 ) ) <_ ( ( %s + %s ) + ( %s ^ 2 ) )' % (A1a, A2a, L11, A1b, A2b, L1N))
    c120 = sp([num.le_lit(w, '0', C12) if False else sp([pE1['c12'], w.inst('x')], 'x', 'x') if False else None], 'x', 'x') if False else None
    c12p = sp([w.s([], 'x', 'x')], 'x', 'x') if False else None
    c120 = sp([num.ge0_nat(w, 10**12)], 'a1i', '0 <_ %s' % C12)
    efle = sp([pE1['ir'], P_(pN['ir']), pE1['c12'], c120, q123], 'lemul2ad', '%s <_ %s' % (EF1, EFN))
    # assemble
    b1r = sp([sp([sp([pbc, yc], 'subcld', '( %s - Y ) e. CC' % PS1), s1c], 'addcld', '%s e. CC' % INN)], 'abscld', '%s e. RR' % B1)
    d1r = sp([sp([pac, pbc], 'subcld', '%s e. CC' % D1)], 'abscld', '( abs ` %s ) e. RR' % D1)
    sumle = sp([d1r, b1r, P_(omlr), P_(pN['er']), psd, sp([b1r, pE1['er'], P_(pN['er']), b1eq, efle], 'letrd', '%s <_ %s' % (B1, EFN))], 'le2addd', '( ( abs ` %s ) + %s ) <_ ( %s + %s )' % (D1, B1, OML, EFN))
    lhs2 = sp([P_(lhs_eq), sp([sp([sp([l2, e3], 'eqtrd', '( ( %s - %s ) + %s ) = ( %s + %s )' % (PSI, IFX, SCN, D1, INN))], 'fveq2d', '%s = ( abs ` ( %s + %s ) )' % (LHS, D1, INN))], 'x', 'x') if False else None], 'x', 'x') if False else None
    lhs3 = sp([sp([l2, e3], 'eqtrd', '( ( %s - %s ) + %s ) = ( %s + %s )' % (PSI, IFX, SCN, D1, INN))], 'fveq2d', '%s = ( abs ` ( %s + %s ) )' % (LHS, D1, INN))
    c1 = sp([lhs3, tri], 'eqbrtrd', '%s <_ ( ( abs ` %s ) + %s )' % (LHS, D1, B1))
    c1 = sp([c1, sumle], 'x', 'x') if False else sp([P_(lhsr), sp([d1r, b1r], 'readdcld', '( ( abs ` %s ) + %s ) e. RR' % (D1, B1)), sp([P_(omlr), P_(pN['er'])], 'readdcld', '( %s + %s ) e. RR' % (OML, EFN)), c1, sumle], 'letrd', '%s <_ ( %s + %s )' % (LHS, OML, EFN))
    case_p = sp([c1, sp([P_(omlr), P_(pN['er'])], 'x', 'x') if False else sp([sp([P_(omlr), P_(pN['er'])], 'x', 'x')], 'x', 'x') if False else sp([s([omlr], 'recnd', '%s e. CC' % OML) and P_(s([omlr], 'recnd', '%s e. CC' % OML)), P_(s([pN['er']], 'recnd', '%s e. CC' % EFN))], 'addcomd', '( %s + %s ) = ( %s + %s )' % (OML, EFN, EFN, OML))], 'breqtrd', '%s <_ ( %s + %s )' % (LHS, EFN, OML))
    w.qed([case_p, case_n], 'pm2.61dane', SB['t21efa'])
    return go(w)


if __name__ == '__main__':
    gen_efa()
