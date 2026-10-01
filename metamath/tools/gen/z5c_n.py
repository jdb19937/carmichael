"""Sortie Z5c, section N: Lemma 3.4, the size bounds for M_r (Detector.lean 973-1276)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5clib import *
from cl import Closure, lift, split_imp
import lin

AB = lambda x: '( abs ` %s )' % x


def cxpabs1(w, a, vn, sc, sre, v, S='S'):
    """( a -> ( abs ` ( v ^c -u S ) ) <_ 1 ) from vn: ( a -> v e. NN ), sc: ( a -> S e. CC ), sre: ( a -> 0 <_ ( Re ` S ) )"""
    st = mkst(w, a)
    Z = '( %s ^c -u %s )' % (v, S)
    vrp = st([vn], 'nnrpd', '%s e. RR+' % v); vr = st([vn], 'nnred', '%s e. RR' % v)
    ns = st([sc], 'negcld', '-u %s e. CC' % S)
    z1 = st([vrp, ns, w.inst('abscxp')], 'syl2anc', '%s = ( %s ^c ( Re ` -u %s ) )' % (AB(Z), v, S))
    z2 = st([st([sc, w.inst('reneg')], 'syl', '( Re ` -u %s ) = -u ( Re ` %s )' % (S, S))], 'oveq2d', '( %s ^c ( Re ` -u %s ) ) = ( %s ^c -u ( Re ` %s ) )' % (v, S, v, S))
    rsr = st([sc], 'recld', '( Re ` %s ) e. RR' % S)
    nrs = st([rsr], 'renegcld', '-u ( Re ` %s ) e. RR' % S)
    le0 = lin.linarith(w, a, [sre], '-u ( Re ` %s ) <_ 0' % S, leaves={'( Re ` %s )' % S: ('RR', rsr)}, atoms=['( Re ` %s )' % S])
    k1 = st([vr, st([vn], 'nnge1d', '1 <_ %s' % v)], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (v, v))
    bz = st([nrs, st([], '0red', '0 e. RR')], 'jca', '( -u ( Re ` %s ) e. RR /\\ 0 e. RR )' % S)
    z3 = st([k1, bz, le0, w.inst('cxplea')], 'syl3anc', '( %s ^c -u ( Re ` %s ) ) <_ ( %s ^c 0 )' % (v, S, v))
    z4 = st([st([vn], 'nncnd', '%s e. CC' % v), w.inst('cxp0')], 'syl', '( %s ^c 0 ) = 1' % v)
    zz = st([st([z1, z2], 'eqtrd', '%s = ( %s ^c -u ( Re ` %s ) )' % (AB(Z), v, S)), z3], 'eqbrtrd', '%s <_ ( %s ^c 0 )' % (AB(Z), v))
    return st([zz, z4], 'breqtrd', '%s <_ 1' % AB(Z))


def cbinst(w, a, cb, v, vn):
    """( a -> ( abs ` ( C ` v ) ) <_ 1 ) from cb: ( a -> CB ), vn: ( a -> v e. NN )"""
    c = w.s([w.s([w.s([], 'fveq2', '( j = %s -> ( C ` j ) = ( C ` %s ) )' % (v, v))], 'fveq2d', '( j = %s -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` %s ) ) )' % (v, v))], 'breq1d',
            '( j = %s -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` %s ) ) <_ 1 ) )' % (v, v))
    return w.s([c, cb, vn], 'rspcdva', '( %s -> ( abs ` ( C ` %s ) ) <_ 1 )' % (a, v))


def z5efabs():
    w = W('z5efabs', "Lean hfactor of norm_eulerT_le: for a prime P, | C ( P ) | <_ 1 and 0 <_ Re S, the Euler factor "
                     "1 + ( f ( P ) - 1 ) C ( P ) P ^ -S has absolute value at most P + 1 (f ( P ) - 1 = - P).")
    ante = split_imp(STATEMENTS['z5efabs'])[0]
    st = mkst(w, ante)
    ppr = st([], 'simpl', 'P e. Prime'); cP = st([], 'simprll', '( C ` P ) e. CC'); cP1 = st([], 'simprlr', '( abs ` ( C ` P ) ) <_ 1')
    sS = st([], 'simprr', SRE0); sc = st([sS], 'simpld', 'S e. CC'); sre = st([sS], 'simprd', '0 <_ ( Re ` S )')
    pn = sy(w, ante, ppr, 'prmnn', 'P e. NN')
    pr = st([pn], 'nnred', 'P e. RR'); pc = st([pn], 'nncnd', 'P e. CC')
    F = FMP('P'); F1 = '( %s - 1 )' % F
    fv = sy(w, ante, ppr, 'z5fmpprm', '%s = -u ( P - 1 )' % F)
    f1 = st([fv], 'oveq1d', '%s = ( -u ( P - 1 ) - 1 )' % F1)
    f2 = lin.lineq(w, ante, '( -u ( P - 1 ) - 1 )', '-u P', leaves={'P': ('RR', pr)})
    f12 = st([f1, f2], 'eqtrd', '%s = -u P' % F1)
    af = st([st([f12], 'fveq2d', '%s = ( abs ` -u P )' % AB(F1)), st([pc], 'absnegd', '( abs ` -u P ) = ( abs ` P )')], 'eqtrd', '%s = ( abs ` P )' % AB(F1))
    af = st([af, st([pr, st([st([pn], 'nnrpd', 'P e. RR+')], 'rpge0d', '0 <_ P')], 'absidd', '( abs ` P ) = P')], 'eqtrd', '%s = P' % AB(F1))
    Z = '( P ^c -u S )'
    zb = cxpabs1(w, ante, pn, sc, sre, 'P')
    f1c = st([f12, st([pc], 'negcld', '-u P e. CC')], 'eqeltrd', '%s e. CC' % F1)
    zc = st([pc, st([sc], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % Z)
    XC = '( %s x. ( C ` P ) )' % F1
    Y = '( %s x. %s )' % (XC, Z)
    xcc = st([f1c, cP], 'mulcld', '%s e. CC' % XC)
    ay = st([st([xcc, zc], 'absmuld', '%s = ( %s x. %s )' % (AB(Y), AB(XC), AB(Z))),
             st([st([f1c, cP], 'absmuld', '%s = ( %s x. %s )' % (AB(XC), AB(F1), AB('( C ` P )')))], 'oveq1d',
                '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (AB(XC), AB(Z), AB(F1), AB('( C ` P )'), AB(Z)))], 'eqtrd',
            '%s = ( ( %s x. %s ) x. %s )' % (AB(Y), AB(F1), AB('( C ` P )'), AB(Z)))
    a1r = st([f1c], 'abscld', '%s e. RR' % AB(F1)); acr = st([cP], 'abscld', '%s e. RR' % AB('( C ` P )')); azr = st([zc], 'abscld', '%s e. RR' % AB(Z))
    one = st([], '1red', '1 e. RR')
    b1 = st([a1r, pr, acr, one, st([f1c], 'absge0d', '0 <_ %s' % AB(F1)), st([cP], 'absge0d', '0 <_ %s' % AB('( C ` P )')), st([a1r, af], 'eqled', '%s <_ P' % AB(F1)), cP1],
            'lemul12ad', '( %s x. %s ) <_ ( P x. 1 )' % (AB(F1), AB('( C ` P )')))
    V1 = '( %s x. %s )' % (AB(F1), AB('( C ` P )'))
    v1r = st([a1r, acr], 'remulcld', '%s e. RR' % V1)
    v10 = st([a1r, acr, st([f1c], 'absge0d', '0 <_ %s' % AB(F1)), st([cP], 'absge0d', '0 <_ %s' % AB('( C ` P )'))], 'mulge0d', '0 <_ %s' % V1)
    b2 = st([v1r, st([pr, one], 'remulcld', '( P x. 1 ) e. RR'), azr, one, v10, st([zc], 'absge0d', '0 <_ %s' % AB(Z)), b1, zb], 'lemul12ad',
            '( %s x. %s ) <_ ( ( P x. 1 ) x. 1 )' % (V1, AB(Z)))
    e1 = st([st([pc], 'mulridd', '( P x. 1 ) = P')], 'oveq1d', '( ( P x. 1 ) x. 1 ) = ( P x. 1 )')
    e2 = st([e1, st([pc], 'mulridd', '( P x. 1 ) = P')], 'eqtrd', '( ( P x. 1 ) x. 1 ) = P')
    yb = st([st([ay, b2], 'eqbrtrd', '%s <_ ( ( P x. 1 ) x. 1 )' % AB(Y)), e2], 'breqtrd', '%s <_ P' % AB(Y))
    EFP = EF('P')
    yc = st([xcc, zc], 'mulcld', '%s e. CC' % Y)
    t1 = st([st([], '1cnd', '1 e. CC'), yc], 'abstrid', '%s <_ ( ( abs ` 1 ) + %s )' % (AB(EFP), AB(Y)))
    t2 = st([t1, st([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % ante)], 'oveq1d', '( ( abs ` 1 ) + %s ) = ( 1 + %s )' % (AB(Y), AB(Y)))],
            'breqtrd', '%s <_ ( 1 + %s )' % (AB(EFP), AB(Y)))
    efc = st([st([], '1cnd', '1 e. CC'), yc], 'addcld', '%s e. CC' % EFP)
    q = lin.linarith(w, ante, [t2, yb], '%s <_ ( P + 1 )' % AB(EFP), leaves={AB(EFP): ('RR', st([efc], 'abscld', '%s e. RR' % AB(EFP))), AB(Y): ('RR', st([yc], 'abscld', '%s e. RR' % AB(Y))),
                                                                          'P': ('RR', pr)}, atoms=[AB(EFP), AB(Y)])
    last = w.lines.pop()
    w.lines.append('qed:' + last.split(':', 1)[1])
    return w


def z5eunorm():
    w = W('z5eunorm', "Lean norm_eulerT_le: for a finite set Q of primes, | C | <_ 1 and 0 <_ Re S, the Euler product "
                      "prod_ p e. Q ( 1 + ( f ( p ) - 1 ) C ( p ) p ^ -S ) has absolute value at most prod_ p e. Q ( p + 1 ).")
    ante = split_imp(STATEMENTS['z5eunorm'])[0]
    st = mkst(w, ante)
    qf = st([], 'simpll', 'Q e. Fin'); qp = st([], 'simplr', 'Q C_ Prime')
    cf = st([], 'simprll', 'C : NN --> CC'); cb = st([], 'simprlr', CB); sS = st([], 'simprr', SRE0)
    a = '( %s /\\ p e. Q )' % ante
    sa = mkst(w, a)
    ppr = sa([lift(w, qp, a), sa([], 'simpr', 'p e. Q')], 'sseldd', 'p e. Prime')
    pn = sy(w, a, ppr, 'prmnn', 'p e. NN')
    cp = sa([lift(w, cf, a), pn], 'ffvelcdmd', '( C ` p ) e. CC')
    cp1 = cbinst(w, a, lift(w, cb, a), 'p', pn)
    hyp = sa([ppr, sa([sa([cp, cp1], 'jca', '( ( C ` p ) e. CC /\\ ( abs ` ( C ` p ) ) <_ 1 )'), lift(w, sS, a)], 'jca',
                      '( ( ( C ` p ) e. CC /\\ ( abs ` ( C ` p ) ) <_ 1 ) /\\ %s )' % SRE0)], 'jca',
             '( p e. Prime /\\ ( ( ( C ` p ) e. CC /\\ ( abs ` ( C ` p ) ) <_ 1 ) /\\ %s ) )' % SRE0)
    eb = sa([hyp, w.inst('z5efabs')], 'syl', '%s <_ ( p + 1 )' % AB(EF('p')))
    sc = lift(w, st([sS], 'simpld', 'S e. CC'), a)
    PE = EF('p')
    efc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % a), w.s([w.s([w.s([w.s([fmpre(w, a, pn)], 'recnd', '( %s -> %s e. CC )' % (a, FMP('p'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % a)],
                                                                  'subcld', '( %s -> ( %s - 1 ) e. CC )' % (a, FMP('p'))), cp], 'mulcld', '( %s -> ( ( %s - 1 ) x. ( C ` p ) ) e. CC )' % (a, FMP('p'))),
                                                   w.s([w.s([pn], 'nncnd', '( %s -> p e. CC )' % a), w.s([sc], 'negcld', '( %s -> -u S e. CC )' % a)], 'cxpcld', '( %s -> ( p ^c -u S ) e. CC )' % a)],
                                                  'mulcld', '( %s -> ( ( ( %s - 1 ) x. ( C ` p ) ) x. ( p ^c -u S ) ) e. CC )' % (a, FMP('p')))], 'addcld', '( %s -> %s e. CC )' % (a, PE))
    pa = w.s([qf, efc], 'z5fprodabs', '( %s -> ( abs ` %s ) = prod_ p e. Q ( abs ` %s ) )' % (ante, EU('Q'), PE))
    pr = sa([pn], 'nnred', 'p e. RR')
    le = st([w.s([], 'nfv', 'F/ p %s' % ante), qf, sa([efc], 'abscld', '( abs ` %s ) e. RR' % PE), sa([efc], 'absge0d', '0 <_ ( abs ` %s )' % PE),
             sa([pr, sa([], '1red', '1 e. RR')], 'readdcld', '( p + 1 ) e. RR'), eb], 'fprodle', 'prod_ p e. Q ( abs ` %s ) <_ prod_ p e. Q ( p + 1 )' % PE)
    w.qed([pa, le], 'eqbrtrd', STATEMENTS['z5eunorm'])
    return w


def z5pp1ss():
    w = W('z5pp1ss', "Lean hone of norm_Mr_le: for Q C_ { p | R }, prod_ p e. Q ( p + 1 ) <_ prod_ ( p | R ) ( p + 1 ) (the factors over "
                     "the complement are at least 1).")
    ante = split_imp(STATEMENTS['z5pp1ss'])[0]
    st = mkst(w, ante)
    rn = st([], 'simpl', 'R e. NN'); qs = st([], 'simpr', 'Q C_ %s' % PF('R'))
    U = PF('R'); B = '( %s \\ Q )' % U
    uf = sy(w, ante, rn, 'pffinq', '%s e. Fin' % U)
    qf = st([uf, qs], 'ssfid', 'Q e. Fin')
    bf = sy(w, ante, uf, 'diffi', '%s e. Fin' % B)
    un = st([qs, w.s([], 'undif', '( Q C_ %s <-> ( Q u. %s ) = %s )' % (U, B, U))], 'sylib', '( Q u. %s ) = %s' % (B, U))
    dj = w.s([w.s([], 'disjdif', '( Q i^i %s ) = (/)' % B)], 'a1i', '( %s -> ( Q i^i %s ) = (/) )' % (ante, B))
    au = '( %s /\\ p e. %s )' % (ante, U)
    pnu = sy(w, au, pp(w, au, w.s([], 'simpr', '( %s -> p e. %s )' % (au, U))), 'prmnn', 'p e. NN')
    pcu = w.s([w.s([w.s([pnu], 'nnred', '( %s -> p e. RR )' % au), w.s([], '1red', '( %s -> 1 e. RR )' % au)], 'readdcld', '( %s -> ( p + 1 ) e. RR )' % au)], 'recnd',
              '( %s -> ( p + 1 ) e. CC )' % au)
    spl = st([dj, st([un], 'eqcomd', '%s = ( Q u. %s )' % (U, B)), uf, pcu], 'fprodsplit', 'prod_ p e. %s ( p + 1 ) = ( prod_ p e. Q ( p + 1 ) x. prod_ p e. %s ( p + 1 ) )' % (U, B))
    ab = '( %s /\\ p e. %s )' % (ante, B)
    pnb = sy(w, ab, pp(w, ab, w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (ab, B))], 'eldifad', '( %s -> p e. %s )' % (ab, U))), 'prmnn', 'p e. NN')
    sab = mkst(w, ab)
    prb = sab([pnb], 'nnred', 'p e. RR')
    p1b = sab([prb, sab([], '1red', '1 e. RR')], 'readdcld', '( p + 1 ) e. RR')
    g1 = lin.linarith(w, ab, [sab([pnb], 'nnge1d', '1 <_ p')], '1 <_ ( p + 1 )', leaves={'p': ('RR', prb)})
    ge1 = st([w.s([], 'nfv', 'F/ p %s' % ante), bf, p1b, g1], 'fprodge1', '1 <_ prod_ p e. %s ( p + 1 )' % B)
    aq = '( %s /\\ p e. Q )' % ante
    saq = mkst(w, aq)
    pnq = sy(w, aq, pp(w, aq, saq([lift(w, qs, aq), saq([], 'simpr', 'p e. Q')], 'sseldd', 'p e. %s' % U)), 'prmnn', 'p e. NN')
    prq = saq([pnq], 'nnred', 'p e. RR')
    p1q = saq([prq, saq([], '1red', '1 e. RR')], 'readdcld', '( p + 1 ) e. RR')
    g0 = lin.linarith(w, aq, [saq([pnq], 'nnge1d', '1 <_ p')], '0 <_ ( p + 1 )', leaves={'p': ('RR', prq)})
    PQ = 'prod_ p e. Q ( p + 1 )'; PB = 'prod_ p e. %s ( p + 1 )' % B
    ge0 = st([w.s([], 'nfv', 'F/ p %s' % ante), qf, p1q, g0], 'fprodge0', '0 <_ %s' % PQ)
    pqr = st([qf, p1q], 'fprodrecl', '%s e. RR' % PQ)
    pbr = st([bf, p1b], 'fprodrecl', '%s e. RR' % PB)
    lm = st([pqr, pbr, ge0, ge1], 'lemulge11d', '%s <_ ( %s x. %s )' % (PQ, PQ, PB))
    w.qed([lm, spl], 'breqtrrd', STATEMENTS['z5pp1ss'])
    return w


def z5pp1sq():
    w = W('z5pp1sq', "Lean prod_primeFactors_add_one_le: for squarefree R, prod_ ( p | R ) ( p + 1 ) <_ R ^ 2 (p + 1 <_ 2 p <_ p p, and "
                     "prod_ ( p | R ) p = R).")
    ante = SQF('R')
    st = mkst(w, ante)
    rn = st([], 'simpl', 'R e. NN'); r0 = st([], 'simpr', '( mmu ` R ) =/= 0')
    U = PF('R')
    uf = sy(w, ante, rn, 'pffinq', '%s e. Fin' % U)
    a = '( %s /\\ p e. %s )' % (ante, U)
    sa = mkst(w, a)
    ppr = pp(w, a, sa([], 'simpr', 'p e. %s' % U))
    pn = sy(w, a, ppr, 'prmnn', 'p e. NN')
    pr = sa([pn], 'nnred', 'p e. RR')
    p2 = sa([sy(w, a, ppr, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), w.inst('eluzle')], 'syl', '2 <_ p')
    l1 = lin.linarith(w, a, [p2], '( p + 1 ) <_ ( 2 x. p )', leaves={'p': ('RR', pr)})
    g0p = lin.linarith(w, a, [p2], '0 <_ p', leaves={'p': ('RR', pr)})
    l2 = sa([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % a), pr, pr, g0p, p2], 'lemul1ad', '( 2 x. p ) <_ ( p x. p )')
    p1r = sa([pr, sa([], '1red', '1 e. RR')], 'readdcld', '( p + 1 ) e. RR')
    ppr_ = sa([pr, pr], 'remulcld', '( p x. p ) e. RR')
    l3 = sa([p1r, sa([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % a), pr], 'remulcld', '( 2 x. p ) e. RR'), ppr_, l1, l2], 'letrd', '( p + 1 ) <_ ( p x. p )')
    g0 = lin.linarith(w, a, [p2], '0 <_ ( p + 1 )', leaves={'p': ('RR', pr)})
    le = st([w.s([], 'nfv', 'F/ p %s' % ante), uf, p1r, g0, ppr_, l3], 'fprodle', 'prod_ p e. %s ( p + 1 ) <_ prod_ p e. %s ( p x. p )' % (U, U))
    pc = sa([pn], 'nncnd', 'p e. CC')
    pm = st([uf, pc, pc], 'fprodmul', 'prod_ p e. %s ( p x. p ) = ( prod_ p e. %s p x. prod_ p e. %s p )' % (U, U, U))
    sid = st([rn, r0, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = R' % U)
    rr = st([pm, st([sid, sid], 'oveq12d', '( prod_ p e. %s p x. prod_ p e. %s p ) = ( R x. R )' % (U, U))], 'eqtrd', 'prod_ p e. %s ( p x. p ) = ( R x. R )' % U)
    rsq = st([st([rn], 'nncnd', 'R e. CC')], 'sqvald', '( R ^ 2 ) = ( R x. R )')
    w.qed([le, st([rr, rsq], 'eqtr4d', 'prod_ p e. %s ( p x. p ) = ( R ^ 2 )' % U)], 'breqtrd', STATEMENTS['z5pp1sq'])
    return w



def r3eq(w, a, rc):
    """( a -> ( R x. ( R ^ 2 ) ) = ( R ^ 3 ) ) from rc: ( a -> R e. CC )"""
    st = mkst(w, a)
    e1 = st([rc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a), w.inst('expp1')], 'syl2anc', '( R ^ ( 2 + 1 ) ) = ( ( R ^ 2 ) x. R )')
    e2 = st([w.s([w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( R ^ ( 2 + 1 ) ) = ( R ^ 3 )')], 'a1i', '( %s -> ( R ^ ( 2 + 1 ) ) = ( R ^ 3 ) )' % a), e1], 'eqtr3d',
            '( R ^ 3 ) = ( ( R ^ 2 ) x. R )')
    r2c = st([rc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a)], 'expcld', '( R ^ 2 ) e. CC')
    e3 = st([e2, st([r2c, rc], 'mulcomd', '( ( R ^ 2 ) x. R ) = ( R x. ( R ^ 2 ) )')], 'eqtrd', '( R ^ 3 ) = ( R x. ( R ^ 2 ) )')
    return st([e3], 'eqcomd', '( R x. ( R ^ 2 ) ) = ( R ^ 3 )')


def eufacts(w, a, rn, cf, sc, D, S='S'):
    """steps ( a -> QS(D,R) e. Fin ), ( a -> QS(D,R) C_ Prime ), ( a -> QS(D,R) C_ PF(R) ), ( a -> EU(QS(D,R)) e. CC )"""
    st = mkst(w, a)
    Q = QS(D, 'R')
    qss = w.s([w.s([w.s([], 'simpl', '( ( q || R /\\ -. q || %s ) -> q || R )' % D)], 'a1i', '( q e. Prime -> ( ( q || R /\\ -. q || %s ) -> q || R ) )' % D)], 'ss2rabi',
              '%s C_ %s' % (Q, PF('R')))
    qssd = w.s([qss], 'a1i', '( %s -> %s C_ %s )' % (a, Q, PF('R')))
    qfin = st([st([rn, w.inst('pffinq')], 'syl', '%s e. Fin' % PF('R')), qssd], 'ssfid', '%s e. Fin' % Q)
    qp = w.s([w.s([], 'ssrab2', '%s C_ Prime' % Q)], 'a1i', '( %s -> %s C_ Prime )' % (a, Q))
    bq = '( %s /\\ p e. %s )' % (a, Q)
    pbq = sy(w, bq, pp(w, bq, w.s([], 'simpr', '( %s -> p e. %s )' % (bq, Q))), 'prmnn', 'p e. NN')
    sbq = mkst(w, bq)
    f1 = sbq([sbq([fmpre(w, bq, pbq)], 'recnd', '%s e. CC' % FMP('p')), sbq([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % FMP('p'))
    cpp = sbq([lift(w, cf, bq), pbq], 'ffvelcdmd', '( C ` p ) e. CC')
    xpp = sbq([sbq([pbq], 'nncnd', 'p e. CC'), sbq([lift(w, sc, bq)], 'negcld', '-u %s e. CC' % S)], 'cxpcld', '( p ^c -u %s ) e. CC' % S)
    bb = sbq([sbq([f1, cpp], 'mulcld', '( ( %s - 1 ) x. ( C ` p ) ) e. CC' % FMP('p')), xpp], 'mulcld', '( ( ( %s - 1 ) x. ( C ` p ) ) x. ( p ^c -u %s ) ) e. CC' % (FMP('p'), S))
    efc = sbq([sbq([], '1cnd', '1 e. CC'), bb], 'addcld', '%s e. CC' % EF('p', S))
    euc = st([qfin, efc], 'fprodcl', '%s e. CC' % EU(Q, S))
    eufacts.efc = efc
    return qfin, qp, qssd, euc


def z5mrtabs():
    w = W('z5mrtabs', "Lean hterm of norm_Mr_le: each term of M_R ( S , chi ) has absolute value at most R ^ 3 for 0 <_ Re S "
                      "( | lambda_D | <_ 1, | f ( ( R , D ) ) | <_ R, | chi | <_ 1, | D ^ -S | <_ 1, | eulerT | <_ prod ( p + 1 ) <_ R ^ 2 ).")
    ante = split_imp(STATEMENTS['z5mrtabs'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); sqr = st([], 'simplr', SQF('R'))
    cfn = st([], 'simprll', CFN); sS = st([], 'simprlr', SRE0); dn = st([], 'simprr', 'D e. NN')
    cf = st([cfn], 'simpld', 'C : NN --> CC'); cb = st([cfn], 'simprd', CB)
    sc = st([sS], 'simpld', 'S e. CC'); sre = st([sS], 'simprd', '0 <_ ( Re ` S )')
    rn = st([sqr], 'simpld', 'R e. NN')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    LAM = '( ( A bvLam B ) ` D )'; FG = FMP('( R gcd D )'); CDv = '( C ` D )'; Z = '( D ^c -u S )'
    Q = QS('D', 'R'); E = EU(Q)
    X = '( %s x. %s )' % (LAM, FG)
    lr = st([abr, dn, w.inst('bvlamre')], 'syl2anc', '%s e. RR' % LAM)
    gn = st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd D ) e. NN')
    fgr = fmpre(w, ante, gn, '( R gcd D )')
    lc = st([lr], 'recnd', '%s e. CC' % LAM); fgc = st([fgr], 'recnd', '%s e. CC' % FG)
    lb = st([hab, dn, w.inst('z5lamabs')], 'syl2anc', '%s <_ 1' % AB(LAM))
    fb = st([rn, dn, w.inst('z5psiabs')], 'syl2anc', '%s <_ R' % AB(FG))
    cdc = st([cf, dn], 'ffvelcdmd', '%s e. CC' % CDv)
    cdb = cbinst(w, ante, cb, 'D', dn)
    zc = st([st([dn], 'nncnd', 'D e. CC'), st([sc], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % Z)
    zb = cxpabs1(w, ante, dn, sc, sre, 'D')
    qfin, qp, qss, ec = eufacts(w, ante, rn, cf, sc, 'D')
    e1 = st([st([qfin, qp], 'jca', '( %s e. Fin /\\ %s C_ Prime )' % (Q, Q)), st([cfn, sS], 'jca', '( %s /\\ %s )' % (CFN, SRE0)), w.inst('z5eunorm')], 'syl2anc',
            '%s <_ prod_ p e. %s ( p + 1 )' % (AB(E), Q))
    e2 = st([rn, qss, w.inst('z5pp1ss')], 'syl2anc', 'prod_ p e. %s ( p + 1 ) <_ prod_ p e. %s ( p + 1 )' % (Q, PF('R')))
    e3 = st([sqr, w.inst('z5pp1sq')], 'syl', 'prod_ p e. %s ( p + 1 ) <_ ( R ^ 2 )' % PF('R'))
    aq = '( %s /\\ p e. %s )' % (ante, Q)
    pq = sy(w, aq, pp(w, aq, w.s([], 'simpr', '( %s -> p e. %s )' % (aq, Q))), 'prmnn', 'p e. NN')
    p1q = w.s([w.s([pq], 'nnred', '( %s -> p e. RR )' % aq), w.s([], '1red', '( %s -> 1 e. RR )' % aq)], 'readdcld', '( %s -> ( p + 1 ) e. RR )' % aq)
    au = '( %s /\\ p e. %s )' % (ante, PF('R'))
    pu = sy(w, au, pp(w, au, w.s([], 'simpr', '( %s -> p e. %s )' % (au, PF('R')))), 'prmnn', 'p e. NN')
    p1u = w.s([w.s([pu], 'nnred', '( %s -> p e. RR )' % au), w.s([], '1red', '( %s -> 1 e. RR )' % au)], 'readdcld', '( %s -> ( p + 1 ) e. RR )' % au)
    pqr = st([qfin, p1q], 'fprodrecl', 'prod_ p e. %s ( p + 1 ) e. RR' % Q)
    pur = st([st([rn, w.inst('pffinq')], 'syl', '%s e. Fin' % PF('R')), p1u], 'fprodrecl', 'prod_ p e. %s ( p + 1 ) e. RR' % PF('R'))
    rr = st([rn], 'nnred', 'R e. RR'); rc = st([rn], 'nncnd', 'R e. CC')
    r2r = st([rr, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ante)], 'reexpcld', '( R ^ 2 ) e. RR')
    aer = st([ec], 'abscld', '%s e. RR' % AB(E))
    eb = st([aer, pqr, r2r, e1, st([pqr, pur, r2r, e2, e3], 'letrd', 'prod_ p e. %s ( p + 1 ) <_ ( R ^ 2 )' % Q)], 'letrd', '%s <_ ( R ^ 2 )' % AB(E))
    # absolute values
    xc = st([lc, fgc], 'mulcld', '%s e. CC' % X)
    XC = '( %s x. %s )' % (X, CDv); XCZ = '( %s x. %s )' % (XC, Z); T = '( %s x. %s )' % (XCZ, E)
    xcc = st([xc, cdc], 'mulcld', '%s e. CC' % XC); xczc = st([xcc, zc], 'mulcld', '%s e. CC' % XCZ)
    ax = st([lc, fgc], 'absmuld', '%s = ( %s x. %s )' % (AB(X), AB(LAM), AB(FG)))
    at1 = st([xczc, ec], 'absmuld', '%s = ( %s x. %s )' % (AB(T), AB(XCZ), AB(E)))
    at2 = st([xcc, zc], 'absmuld', '%s = ( %s x. %s )' % (AB(XCZ), AB(XC), AB(Z)))
    at3 = st([xc, cdc], 'absmuld', '%s = ( %s x. %s )' % (AB(XC), AB(X), AB(CDv)))
    one = st([], '1red', '1 e. RR')
    alr = st([lc], 'abscld', '%s e. RR' % AB(LAM)); afr = st([fgc], 'abscld', '%s e. RR' % AB(FG)); axr = st([xc], 'abscld', '%s e. RR' % AB(X))
    acr = st([cdc], 'abscld', '%s e. RR' % AB(CDv)); azr = st([zc], 'abscld', '%s e. RR' % AB(Z))
    bx = st([ax, st([alr, one, afr, rr, st([lc], 'absge0d', '0 <_ %s' % AB(LAM)), st([fgc], 'absge0d', '0 <_ %s' % AB(FG)), lb, fb], 'lemul12ad',
                    '( %s x. %s ) <_ ( 1 x. R )' % (AB(LAM), AB(FG)))], 'eqbrtrd', '%s <_ ( 1 x. R )' % AB(X))
    B1 = '( 1 x. R )'; B2 = '( %s x. 1 )' % B1; B3 = '( %s x. 1 )' % B2; B4 = '( %s x. ( R ^ 2 ) )' % B3
    b1r = st([one, rr], 'remulcld', '%s e. RR' % B1); b2r = st([b1r, one], 'remulcld', '%s e. RR' % B2); b3r = st([b2r, one], 'remulcld', '%s e. RR' % B3)
    b2 = st([axr, b1r, acr, one, st([xc], 'absge0d', '0 <_ %s' % AB(X)), st([cdc], 'absge0d', '0 <_ %s' % AB(CDv)), bx, cdb], 'lemul12ad',
            '( %s x. %s ) <_ %s' % (AB(X), AB(CDv), B2))
    V2 = '( %s x. %s )' % (AB(X), AB(CDv))
    v2r = st([axr, acr], 'remulcld', '%s e. RR' % V2)
    v20 = st([axr, acr, st([xc], 'absge0d', '0 <_ %s' % AB(X)), st([cdc], 'absge0d', '0 <_ %s' % AB(CDv))], 'mulge0d', '0 <_ %s' % V2)
    b3 = st([v2r, b2r, azr, one, v20, st([zc], 'absge0d', '0 <_ %s' % AB(Z)), b2, zb], 'lemul12ad', '( %s x. %s ) <_ %s' % (V2, AB(Z), B3))
    V3 = '( %s x. %s )' % (V2, AB(Z))
    v3r = st([v2r, azr], 'remulcld', '%s e. RR' % V3)
    v30 = st([v2r, azr, v20, st([zc], 'absge0d', '0 <_ %s' % AB(Z))], 'mulge0d', '0 <_ %s' % V3)
    b4 = st([v3r, b3r, aer, r2r, v30, st([ec], 'absge0d', '0 <_ %s' % AB(E)), b3, eb], 'lemul12ad', '( %s x. %s ) <_ %s' % (V3, AB(E), B4))
    # |T| = V3 x. |E|
    q1 = st([at2, st([at3], 'oveq1d', '( %s x. %s ) = %s' % (AB(XC), AB(Z), V3))], 'eqtrd', '%s = %s' % (AB(XCZ), V3))
    q2 = st([at1, st([q1], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (AB(XCZ), AB(E), V3, AB(E)))], 'eqtrd', '%s = ( %s x. %s )' % (AB(T), V3, AB(E)))
    # B4 = R ^ 3
    s1 = st([st([st([st([rc], 'mullidd', '%s = R' % B1)], 'oveq1d', '%s = ( R x. 1 )' % B2), st([rc], 'mulridd', '( R x. 1 ) = R')], 'eqtrd', '%s = R' % B2)], 'oveq1d',
            '%s = ( R x. 1 )' % B3)
    s2 = st([s1, st([rc], 'mulridd', '( R x. 1 ) = R')], 'eqtrd', '%s = R' % B3)
    s3 = st([st([s2], 'oveq1d', '%s = ( R x. ( R ^ 2 ) )' % B4), r3eq(w, ante, rc)], 'eqtrd', '%s = ( R ^ 3 )' % B4)
    w.qed([st([q2, b4], 'eqbrtrd', '%s <_ %s' % (AB(T), B4)), s3], 'breqtrd', STATEMENTS['z5mrtabs'])
    return w


def z5mrnorm():
    w = W('z5mrnorm', "Blueprint Lemma 3.4(c) (Lean norm_Mr_le): | M_R ( S , chi ) | <_ z2 R ^ 3 for 0 <_ Re S and squarefree R "
                      "(|_ z2 terms, each at most R ^ 3).")
    ante = split_imp(STATEMENTS['z5mrnorm'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); sqr = st([], 'simplr', SQF('R'))
    cfn = st([], 'simprl', CFN); sS = st([], 'simprr', SRE0)
    cf = st([cfn], 'simpld', 'C : NN --> CC'); sc = st([sS], 'simpld', 'S e. CC')
    rn = st([sqr], 'simpld', 'R e. NN')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    I = '( 1 ... ( |_ ` B ) )'
    cvx = st([cf, w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ante), w.inst('fex')], 'syl2anc', 'C e. _V')
    mrv = st([st([st([Ar, Br], 'jca', '( A e. RR /\\ B e. RR )'), st([cvx, rn], 'jca', '( C e. _V /\\ R e. NN )')], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ R e. NN ) )'),
              sc, w.inst('z5mrval')], 'syl2anc', '%s = sum_ d e. %s %s' % (MR(), I, MRT('d')))
    ifin = st([], 'fzfid', '%s e. Fin' % I)
    a = '( %s /\\ d e. %s )' % (ante, I)
    sa = mkst(w, a)
    dn = sa([sa([], 'simpr', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    tb = sa([lift(w, st([hab, sqr], 'jca', '( %s /\\ %s )' % (HAB0, SQF('R'))), a), sa([sa([lift(w, cfn, a), lift(w, sS, a)], 'jca', '( %s /\\ %s )' % (CFN, SRE0)), dn], 'jca',
                                                                                          '( ( %s /\\ %s ) /\\ d e. NN )' % (CFN, SRE0)), w.inst('z5mrtabs')], 'syl2anc',
            '( abs ` %s ) <_ ( R ^ 3 )' % MRT('d'))
    # MRT(d) in CC
    LAM = '( ( A bvLam B ) ` d )'; FG = FMP('( R gcd d )')
    lr = sa([lift(w, abr, a), dn, w.inst('bvlamre')], 'syl2anc', '%s e. RR' % LAM)
    gn = sa([lift(w, rn, a), dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd d ) e. NN')
    xc = sa([sa([sa([lr, fmpre(w, a, gn, '( R gcd d )')], 'remulcld', '( %s x. %s ) e. RR' % (LAM, FG))], 'recnd', '( %s x. %s ) e. CC' % (LAM, FG)),
             sa([lift(w, cf, a), dn], 'ffvelcdmd', '( C ` d ) e. CC')], 'mulcld', '( ( %s x. %s ) x. ( C ` d ) ) e. CC' % (LAM, FG))
    xz = sa([xc, sa([sa([dn], 'nncnd', 'd e. CC'), sa([lift(w, sc, a)], 'negcld', '-u S e. CC')], 'cxpcld', '( d ^c -u S ) e. CC')], 'mulcld',
            '( ( ( %s x. %s ) x. ( C ` d ) ) x. ( d ^c -u S ) ) e. CC' % (LAM, FG))
    qfin, qp, qss, ec = eufacts(w, a, lift(w, rn, a), lift(w, cf, a), lift(w, sc, a), 'd')
    mc = sa([xz, ec], 'mulcld', '%s e. CC' % MRT('d'))
    fa = st([ifin, mc], 'fsumabs', '( abs ` sum_ d e. %s %s ) <_ sum_ d e. %s ( abs ` %s )' % (I, MRT('d'), I, MRT('d')))
    rr = st([rn], 'nnred', 'R e. RR')
    r3 = st([rr, w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ante)], 'reexpcld', '( R ^ 3 ) e. RR')
    fl = st([ifin, sa([mc], 'abscld', '( abs ` %s ) e. RR' % MRT('d')), lift(w, r3, a), tb], 'fsumle', 'sum_ d e. %s ( abs ` %s ) <_ sum_ d e. %s ( R ^ 3 )' % (I, MRT('d'), I))
    fc = st([ifin, st([r3], 'recnd', '( R ^ 3 ) e. CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ d e. %s ( R ^ 3 ) = ( ( # ` %s ) x. ( R ^ 3 ) )' % (I, I))
    b0 = lin.linarith(w, ante, [A0, AB_], '0 <_ B', leaves={'A': ('RR', Ar), 'B': ('RR', Br)})
    fln = st([Br, b0, w.inst('flge0nn0')], 'syl2anc', '( |_ ` B ) e. NN0')
    hs = st([fln, w.inst('hashfz1')], 'syl', '( # ` %s ) = ( |_ ` B )' % I)
    fc2 = st([fc, st([hs], 'oveq1d', '( ( # ` %s ) x. ( R ^ 3 ) ) = ( ( |_ ` B ) x. ( R ^ 3 ) )' % I)], 'eqtrd', 'sum_ d e. %s ( R ^ 3 ) = ( ( |_ ` B ) x. ( R ^ 3 ) )' % I)
    r30 = st([rr, w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ante), st([st([rn], 'nnrpd', 'R e. RR+')], 'rpge0d', '0 <_ R')], 'expge0d', '0 <_ ( R ^ 3 )')
    fb = st([st([fln], 'nn0red', '( |_ ` B ) e. RR'), Br, r3, r30, st([Br, w.inst('flle')], 'syl', '( |_ ` B ) <_ B')], 'lemul1ad', '( ( |_ ` B ) x. ( R ^ 3 ) ) <_ ( B x. ( R ^ 3 ) )')
    c1 = st([st([mrv], 'fveq2d', '( abs ` %s ) = ( abs ` sum_ d e. %s %s )' % (MR(), I, MRT('d'))), fa], 'eqbrtrd', '( abs ` %s ) <_ sum_ d e. %s ( abs ` %s )' % (MR(), I, MRT('d')))
    SA = 'sum_ d e. %s ( abs ` %s )' % (I, MRT('d'))
    sar = st([ifin, sa([mc], 'abscld', '( abs ` %s ) e. RR' % MRT('d'))], 'fsumrecl', '%s e. RR' % SA)
    s3r = st([ifin, lift(w, r3, a)], 'fsumrecl', 'sum_ d e. %s ( R ^ 3 ) e. RR' % I)
    amr = st([st([mrv, st([ifin, mc], 'fsumcl', 'sum_ d e. %s %s e. CC' % (I, MRT('d')))], 'eqeltrd', '%s e. CC' % MR())], 'abscld', '( abs ` %s ) e. RR' % MR())
    c2 = st([amr, sar, s3r, c1, fl], 'letrd', '( abs ` %s ) <_ sum_ d e. %s ( R ^ 3 )' % (MR(), I))
    c3 = st([c2, fc2], 'breqtrd', '( abs ` %s ) <_ ( ( |_ ` B ) x. ( R ^ 3 ) )' % MR())
    w.qed([amr, st([st([fln], 'nn0red', '( |_ ` B ) e. RR'), r3], 'remulcld', '( ( |_ ` B ) x. ( R ^ 3 ) ) e. RR'), st([Br, r3], 'remulcld', '( B x. ( R ^ 3 ) ) e. RR'), c3, fb],
          'letrd', STATEMENTS['z5mrnorm'])
    return w



def z5mrtcl():
    w = W('z5mrtcl', "Each term of the mollifier M_R ( S , chi ) is a complex number.")
    ante = split_imp(STATEMENTS['z5mrtcl'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); rn = st([], 'simplr', 'R e. NN')
    cf = st([], 'simprll', 'C : NN --> CC'); sc = st([], 'simprlr', 'S e. CC'); dn = st([], 'simprr', 'D e. NN')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    LAM = '( ( A bvLam B ) ` D )'; FG = FMP('( R gcd D )')
    lr = st([abr, dn, w.inst('bvlamre')], 'syl2anc', '%s e. RR' % LAM)
    gn = st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd D ) e. NN')
    xc = st([st([st([lr, fmpre(w, ante, gn, '( R gcd D )')], 'remulcld', '( %s x. %s ) e. RR' % (LAM, FG))], 'recnd', '( %s x. %s ) e. CC' % (LAM, FG)),
             st([cf, dn], 'ffvelcdmd', '( C ` D ) e. CC')], 'mulcld', '( ( %s x. %s ) x. ( C ` D ) ) e. CC' % (LAM, FG))
    xz = st([xc, st([st([dn], 'nncnd', 'D e. CC'), st([sc], 'negcld', '-u S e. CC')], 'cxpcld', '( D ^c -u S ) e. CC')], 'mulcld',
            '( ( ( %s x. %s ) x. ( C ` D ) ) x. ( D ^c -u S ) ) e. CC' % (LAM, FG))
    qfin, qp, qss, ec = eufacts(w, ante, rn, cf, sc, 'D')
    w.qed([xz, ec], 'mulcld', STATEMENTS['z5mrtcl'])
    return w


def z5mrcl():
    w = W('z5mrcl', "The mollifier M_R ( S , chi ) is a complex number (a finite sum of z5mrtcl's terms).")
    ante = split_imp(STATEMENTS['z5mrcl'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); rn = st([], 'simplr', 'R e. NN')
    cf = st([], 'simprl', 'C : NN --> CC'); sc = st([], 'simprr', 'S e. CC')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    I = '( 1 ... ( |_ ` B ) )'
    cvx = st([cf, w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ante), w.inst('fex')], 'syl2anc', 'C e. _V')
    mrv = st([st([st([Ar, Br], 'jca', '( A e. RR /\\ B e. RR )'), st([cvx, rn], 'jca', '( C e. _V /\\ R e. NN )')], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ R e. NN ) )'),
              sc, w.inst('z5mrval')], 'syl2anc', '%s = sum_ d e. %s %s' % (MR(), I, MRT('d')))
    a = '( %s /\\ d e. %s )' % (ante, I)
    sa = mkst(w, a)
    dn = sa([sa([], 'simpr', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    mc = sa([lift(w, st([hab, rn], 'jca', '( %s /\\ R e. NN )' % HAB0), a), sa([lift(w, st([cf, sc], 'jca', '( C : NN --> CC /\\ S e. CC )'), a), dn], 'jca',
                                                                                  '( ( C : NN --> CC /\\ S e. CC ) /\\ d e. NN )'), w.inst('z5mrtcl')], 'syl2anc', '%s e. CC' % MRT('d'))
    w.qed([mrv, st([st([], 'fzfid', '%s e. Fin' % I), mc], 'fsumcl', 'sum_ d e. %s %s e. CC' % (I, MRT('d')))], 'eqeltrd', STATEMENTS['z5mrcl'])
    return w


def y3eq(w, a, yc, Bc):
    """( a -> ( Y x. ( B x. ( Y ^ 2 ) ) ) = ( B x. ( Y ^ 3 ) ) )"""
    st = mkst(w, a)
    e0 = st([yc, Bc, st([yc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a)], 'expcld', '( Y ^ 2 ) e. CC')], 'mul12d',
            '( Y x. ( B x. ( Y ^ 2 ) ) ) = ( B x. ( Y x. ( Y ^ 2 ) ) )')
    e1 = st([yc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a), w.inst('expp1')], 'syl2anc', '( Y ^ ( 2 + 1 ) ) = ( ( Y ^ 2 ) x. Y )')
    e2 = st([w.s([w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( Y ^ ( 2 + 1 ) ) = ( Y ^ 3 )')], 'a1i', '( %s -> ( Y ^ ( 2 + 1 ) ) = ( Y ^ 3 ) )' % a), e1], 'eqtr3d',
            '( Y ^ 3 ) = ( ( Y ^ 2 ) x. Y )')
    y2c = st([yc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a)], 'expcld', '( Y ^ 2 ) e. CC')
    e3 = st([e2, st([y2c, yc], 'mulcomd', '( ( Y ^ 2 ) x. Y ) = ( Y x. ( Y ^ 2 ) )')], 'eqtrd', '( Y ^ 3 ) = ( Y x. ( Y ^ 2 ) )')
    return st([e0, st([st([e3], 'eqcomd', '( Y x. ( Y ^ 2 ) ) = ( Y ^ 3 )')], 'oveq2d', '( B x. ( Y x. ( Y ^ 2 ) ) ) = ( B x. ( Y ^ 3 ) )')], 'eqtrd',
              '( Y x. ( B x. ( Y ^ 2 ) ) ) = ( B x. ( Y ^ 3 ) )')


def z5mrsum():
    w = W('z5mrsum', "Summed form of Lemma 3.4(c) (Lean sum_inv_mul_norm_Mr_le): sum_ ( r e. RSet ) r ^ -1 | M_r ( S , chi ) | <_ z2 Y ^ 3 "
                     "for 1 <_ Y (each term at most z2 r ^ 2 <_ z2 Y ^ 2, at most |_ Y terms).")
    ante = split_imp(STATEMENTS['z5mrsum'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); nv = st([], 'simplrl', 'N e. V'); yy = st([], 'simplrr', '( Y e. RR /\\ 1 <_ Y )')
    cfn = st([], 'simprl', CFN); sS = st([], 'simprr', SRE0)
    yr = st([yy], 'simpld', 'Y e. RR'); y1 = st([yy], 'simprd', '1 <_ Y')
    cf = st([cfn], 'simpld', 'C : NN --> CC'); sc = st([sS], 'simpld', 'S e. CC')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    RS = '( N RSet Y )'
    rf = st([nv, yr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` Y ) ) /\\ %s e. Fin )' % (RS, RS))
    rsf = st([rf], 'simprd', '%s e. Fin' % RS); rss = st([rf], 'simpld', '%s C_ ( 1 ... ( |_ ` Y ) )' % RS)
    a = '( %s /\\ r e. %s )' % (ante, RS)
    sa = mkst(w, a)
    el = sa([sa([], 'simpr', 'r e. %s' % RS), sa([lift(w, nv, a), lift(w, yr, a), w.inst('z5elrset')], 'syl2anc',
                                   '( r e. %s <-> ( r e. ( 1 ... ( |_ ` Y ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) ) )' % RS)], 'mpbid',
            '( r e. ( 1 ... ( |_ ` Y ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) )')
    rfz = sa([el], 'simpld', 'r e. ( 1 ... ( |_ ` Y ) )')
    rn = sa([rfz, w.inst('elfznn')], 'syl', 'r e. NN')
    r0 = sa([el], 'simprld', '( mmu ` r ) =/= 0')
    rr = sa([rn], 'nnred', 'r e. RR'); rc = sa([rn], 'nncnd', 'r e. CC')
    rly = sa([rr, sa([sa([lift(w, yr, a)], 'flcld', '( |_ ` Y ) e. ZZ')], 'zred', '( |_ ` Y ) e. RR'),
              lift(w, yr, a), sa([rfz, w.inst('elfzle2')], 'syl', 'r <_ ( |_ ` Y )'), sa([lift(w, yr, a), w.inst('flle')], 'syl', '( |_ ` Y ) <_ Y')], 'letrd', 'r <_ Y')
    MRr = MR('S', 'r')
    nb = sa([lift(w, hab, a), sa([rn, r0], 'jca', '( r e. NN /\\ ( mmu ` r ) =/= 0 )'), lift(w, st([cfn, sS], 'jca', '( %s /\\ %s )' % (CFN, SRE0)), a),
             w.inst('z5mrnorm')], 'syl21anc', '( abs ` %s ) <_ ( B x. ( r ^ 3 ) )' % MRr)
    mrc = sa([lift(w, hab, a), rn, lift(w, cf, a), lift(w, sc, a), w.inst('z5mrcl')], 'syl22anc', '%s e. CC' % MRr)
    amr = sa([mrc], 'abscld', '( abs ` %s ) e. RR' % MRr)
    rir = sa([rn], 'nnrecred', '( 1 / r ) e. RR')
    ri0 = sa([sa([rn], 'nnrpd', 'r e. RR+')], 'rpreccld', '( 1 / r ) e. RR+')
    Br_ = lift(w, Br, a)
    r3 = sa([rr, w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % a)], 'reexpcld', '( r ^ 3 ) e. RR')
    t1 = sa([amr, sa([Br_, r3], 'remulcld', '( B x. ( r ^ 3 ) ) e. RR'), rir, sa([ri0], 'rpge0d', '0 <_ ( 1 / r )'), nb], 'lemul2ad',
            '( ( 1 / r ) x. ( abs ` %s ) ) <_ ( ( 1 / r ) x. ( B x. ( r ^ 3 ) ) )' % MRr)
    # ( 1 / r ) x. ( B x. ( r ^ 3 ) ) = B x. ( r ^ 2 )
    r2c = sa([rc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a)], 'expcld', '( r ^ 2 ) e. CC')
    Bc = sa([Br_], 'recnd', 'B e. CC')
    e1 = sa([rc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a), w.inst('expp1')], 'syl2anc', '( r ^ ( 2 + 1 ) ) = ( ( r ^ 2 ) x. r )')
    e2 = sa([w.s([w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( r ^ ( 2 + 1 ) ) = ( r ^ 3 )')], 'a1i', '( %s -> ( r ^ ( 2 + 1 ) ) = ( r ^ 3 ) )' % a), e1], 'eqtr3d',
            '( r ^ 3 ) = ( ( r ^ 2 ) x. r )')
    e3 = sa([sa([e2], 'oveq2d', '( B x. ( r ^ 3 ) ) = ( B x. ( ( r ^ 2 ) x. r ) )'), sa([sa([Bc, r2c, rc], 'mulassd', '( ( B x. ( r ^ 2 ) ) x. r ) = ( B x. ( ( r ^ 2 ) x. r ) )')],
                                                                                              'eqcomd', '( B x. ( ( r ^ 2 ) x. r ) ) = ( ( B x. ( r ^ 2 ) ) x. r )')],
            'eqtrd', '( B x. ( r ^ 3 ) ) = ( ( B x. ( r ^ 2 ) ) x. r )')
    br2c = sa([Bc, r2c], 'mulcld', '( B x. ( r ^ 2 ) ) e. CC')
    rn0 = sa([rn], 'nnne0d', 'r =/= 0')
    e4 = sa([sa([sa([sa([br2c, rc], 'mulcld', '( ( B x. ( r ^ 2 ) ) x. r ) e. CC'), rc, rn0], 'divrec2d', '( ( ( B x. ( r ^ 2 ) ) x. r ) / r ) = ( ( 1 / r ) x. ( ( B x. ( r ^ 2 ) ) x. r ) )')],
                'eqcomd', '( ( 1 / r ) x. ( ( B x. ( r ^ 2 ) ) x. r ) ) = ( ( ( B x. ( r ^ 2 ) ) x. r ) / r )'),
             sa([br2c, rc, rn0], 'divcan4d', '( ( ( B x. ( r ^ 2 ) ) x. r ) / r ) = ( B x. ( r ^ 2 ) )')], 'eqtrd', '( ( 1 / r ) x. ( ( B x. ( r ^ 2 ) ) x. r ) ) = ( B x. ( r ^ 2 ) )')
    e5 = sa([sa([e3], 'oveq2d', '( ( 1 / r ) x. ( B x. ( r ^ 3 ) ) ) = ( ( 1 / r ) x. ( ( B x. ( r ^ 2 ) ) x. r ) )'), e4], 'eqtrd', '( ( 1 / r ) x. ( B x. ( r ^ 3 ) ) ) = ( B x. ( r ^ 2 ) )')
    # B r ^ 2 <_ B Y ^ 2
    r0le = sa([sa([rn], 'nnrpd', 'r e. RR+')], 'rpge0d', '0 <_ r')
    rrY = sa([rr, lift(w, yr, a), rr, lift(w, yr, a), r0le, r0le, rly, rly], 'lemul12ad', '( r x. r ) <_ ( Y x. Y )')
    sq = sa([sa([sa([rc], 'sqvald', '( r ^ 2 ) = ( r x. r )'), rrY], 'eqbrtrd', '( r ^ 2 ) <_ ( Y x. Y )'), sa([sa([lift(w, yr, a)], 'recnd', 'Y e. CC')], 'sqvald', '( Y ^ 2 ) = ( Y x. Y )')],
            'breqtrrd', '( r ^ 2 ) <_ ( Y ^ 2 )')
    b0 = lin.linarith(w, ante, [A0, AB_], '0 <_ B', leaves={'A': ('RR', Ar), 'B': ('RR', Br)})
    y2r = st([yr, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ante)], 'reexpcld', '( Y ^ 2 ) e. RR')
    t2 = sa([sa([rr, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a)], 'reexpcld', '( r ^ 2 ) e. RR'), lift(w, y2r, a), Br_, lift(w, b0, a), sq], 'lemul2ad',
            '( B x. ( r ^ 2 ) ) <_ ( B x. ( Y ^ 2 ) )')
    by2 = st([Br, y2r], 'remulcld', '( B x. ( Y ^ 2 ) ) e. RR')
    TR = '( ( 1 / r ) x. ( abs ` %s ) )' % MRr
    trr = sa([rir, amr], 'remulcld', '%s e. RR' % TR)
    tb = sa([trr, sa([Br_, sa([rr, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % a)], 'reexpcld', '( r ^ 2 ) e. RR')], 'remulcld', '( B x. ( r ^ 2 ) ) e. RR'),
              lift(w, by2, a), sa([t1, e5], 'breqtrd', '%s <_ ( B x. ( r ^ 2 ) )' % TR), t2], 'letrd', '%s <_ ( B x. ( Y ^ 2 ) )' % TR)
    fl = st([rsf, trr, lift(w, by2, a), tb], 'fsumle', 'sum_ r e. %s %s <_ sum_ r e. %s ( B x. ( Y ^ 2 ) )' % (RS, TR, RS))
    fc = st([rsf, st([by2], 'recnd', '( B x. ( Y ^ 2 ) ) e. CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ r e. %s ( B x. ( Y ^ 2 ) ) = ( ( # ` %s ) x. ( B x. ( Y ^ 2 ) ) )' % (RS, RS))
    y0 = lin.linarith(w, ante, [y1], '0 <_ Y', leaves={'Y': ('RR', yr)})
    card = st([nv, yr, y0, w.inst('z5rsetcard')], 'syl12anc', '( # ` %s ) <_ ( |_ ` Y )' % RS)
    by20 = st([Br, y2r, b0, st([yr, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ante), y0], 'expge0d', '0 <_ ( Y ^ 2 )')], 'mulge0d', '0 <_ ( B x. ( Y ^ 2 ) )')
    hr = st([st([rsf, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RS)], 'nn0red', '( # ` %s ) e. RR' % RS)
    flr = st([st([yr], 'flcld', '( |_ ` Y ) e. ZZ')], 'zred', '( |_ ` Y ) e. RR')
    c1 = st([hr, flr, by2, by20, card], 'lemul1ad', '( ( # ` %s ) x. ( B x. ( Y ^ 2 ) ) ) <_ ( ( |_ ` Y ) x. ( B x. ( Y ^ 2 ) ) )' % RS)
    c2 = st([flr, yr, by2, by20, st([yr, w.inst('flle')], 'syl', '( |_ ` Y ) <_ Y')], 'lemul1ad', '( ( |_ ` Y ) x. ( B x. ( Y ^ 2 ) ) ) <_ ( Y x. ( B x. ( Y ^ 2 ) ) )')
    c3 = y3eq(w, ante, st([yr], 'recnd', 'Y e. CC'), st([Br], 'recnd', 'B e. CC'))
    SL = 'sum_ r e. %s %s' % (RS, TR)
    slr = st([rsf, trr], 'fsumrecl', '%s e. RR' % SL)
    m1 = st([hr, by2], 'remulcld', '( ( # ` %s ) x. ( B x. ( Y ^ 2 ) ) ) e. RR' % RS)
    m2 = st([flr, by2], 'remulcld', '( ( |_ ` Y ) x. ( B x. ( Y ^ 2 ) ) ) e. RR')
    m3 = st([yr, by2], 'remulcld', '( Y x. ( B x. ( Y ^ 2 ) ) ) e. RR')
    k1 = st([slr, m1, m2, st([fl, fc], 'breqtrd', '%s <_ ( ( # ` %s ) x. ( B x. ( Y ^ 2 ) ) )' % (SL, RS)), c1], 'letrd', '%s <_ ( ( |_ ` Y ) x. ( B x. ( Y ^ 2 ) ) )' % SL)
    k2 = st([slr, m2, m3, k1, c2], 'letrd', '%s <_ ( Y x. ( B x. ( Y ^ 2 ) ) )' % SL)
    w.qed([k2, c3], 'breqtrd', STATEMENTS['z5mrsum'])
    return w



def z5invmul():
    w = W('z5invmul', "Lean sum_inv_multiples_le at M = |_ Z: sum over the multiples d <_ Z of R of 1 / d is at most ( 1 / R ) ( 1 + log Z ) "
                      "(reindex d = R n by dvdsflf1o, then the harmonic bound harmonicubnd on 1 ... |_ ( Z / R ) C_ 1 ... |_ Z).")
    ante = split_imp(STATEMENTS['z5invmul'])[0]
    st = mkst(w, ante)
    rn = st([], 'simpl', 'R e. NN'); zr = st([], 'simprl', 'Z e. RR'); z1 = st([], 'simprr', '1 <_ Z')
    rc = st([rn], 'nncnd', 'R e. CC'); rr = st([rn], 'nnred', 'R e. RR'); rrp = st([rn], 'nnrpd', 'R e. RR+')
    zpos = lin.linarith(w, ante, [z1], '0 < Z', leaves={'Z': ('RR', zr)})
    zrp = st([zr, zpos], 'elrpd', 'Z e. RR+')
    M = '( 1 ... ( |_ ` ( Z / R ) ) )'; X = '{ x e. ( 1 ... ( |_ ` Z ) ) | R || x }'; IZ = '( 1 ... ( |_ ` Z ) )'
    F = '( m e. %s |-> ( R x. m ) )' % M
    f1o = st([zr, rn, w.s([], 'eqid', '%s = %s' % (F, F))], 'dvdsflf1o', '%s : %s -1-1-onto-> %s' % (F, M, X))
    an = '( %s /\\ n e. %s )' % (ante, M)
    san = mkst(w, an)
    nn_ = san([san([], 'simpr', 'n e. %s' % M), w.inst('elfznn')], 'syl', 'n e. NN')
    rnn = san([lift(w, rn, an), nn_], 'nnmulcld', '( R x. n ) e. NN')
    fv, _ = mpv(w, an, 'm', M, '( R x. m )', 'n', san([], 'simpr', 'n e. %s' % M))
    ad = '( %s /\\ d e. %s )' % (ante, X)
    sad = mkst(w, ad)
    dnn = sad([sad([sad([], 'simpr', 'd e. %s' % X), w.inst('elrabi')], 'syl', 'd e. %s' % IZ), w.inst('elfznn')], 'syl', 'd e. NN')
    dc = sad([sad([dnn], 'nncnd', 'd e. CC'), sad([dnn], 'nnne0d', 'd =/= 0')], 'reccld', '( 1 / d ) e. CC')
    cgf = w.s([], 'oveq2', '( d = ( R x. n ) -> ( 1 / d ) = ( 1 / ( R x. n ) ) )')
    fo = st([cgf, st([], 'fzfid', '%s e. Fin' % M), f1o, fv, dc], 'fsumf1o', 'sum_ d e. %s ( 1 / d ) = sum_ n e. %s ( 1 / ( R x. n ) )' % (X, M))
    ncc = san([nn_], 'nncnd', 'n e. CC'); n0 = san([nn_], 'nnne0d', 'n =/= 0')
    rc_ = lift(w, rc, an); r0 = san([lift(w, rn, an)], 'nnne0d', 'R =/= 0')
    t1 = san([san([san([], '1cnd', '1 e. CC'), rc_, ncc, r0, n0], 'divdiv1d', '( ( 1 / R ) / n ) = ( 1 / ( R x. n ) )')], 'eqcomd',
             '( 1 / ( R x. n ) ) = ( ( 1 / R ) / n )')
    t2 = san([san([rc_, r0], 'reccld', '( 1 / R ) e. CC'), ncc, n0], 'divrecd', '( ( 1 / R ) / n ) = ( ( 1 / R ) x. ( 1 / n ) )')
    t12 = san([t1, t2], 'eqtrd', '( 1 / ( R x. n ) ) = ( ( 1 / R ) x. ( 1 / n ) )')
    s1 = st([t12], 'sumeq2dv', 'sum_ n e. %s ( 1 / ( R x. n ) ) = sum_ n e. %s ( ( 1 / R ) x. ( 1 / n ) )' % (M, M))
    rec = st([rc, st([rn], 'nnne0d', 'R =/= 0')], 'reccld', '( 1 / R ) e. CC')
    s2 = st([st([], 'fzfid', '%s e. Fin' % M), rec, san([ncc, n0], 'reccld', '( 1 / n ) e. CC')], 'fsummulc2',
            '( ( 1 / R ) x. sum_ n e. %s ( 1 / n ) ) = sum_ n e. %s ( ( 1 / R ) x. ( 1 / n ) )' % (M, M))
    # M C_ 1 ... |_ Z
    zdr = st([zr, rrp], 'rerpdivcld', '( Z / R ) e. RR')
    zle = st([st([zr, zrp, st([rrp, st([rn], 'nnge1d', '1 <_ R')], 'jca', '( R e. RR+ /\\ 1 <_ R )'), w.inst('ledivge1le')], 'syl3anc', '( Z <_ Z -> ( Z / R ) <_ Z )'),
              st([zr], 'leidd', 'Z <_ Z')], 'mpd', '( Z / R ) <_ Z')
    fw = st([zdr, zr, zle, w.inst('flwordi')], 'syl3anc', '( |_ ` ( Z / R ) ) <_ ( |_ ` Z )')
    fz1 = st([zdr], 'flcld', '( |_ ` ( Z / R ) ) e. ZZ'); fz2 = st([zr], 'flcld', '( |_ ` Z ) e. ZZ')
    eu = st([fw, st([fz1, fz2, w.inst('eluz')], 'syl2anc', '( ( |_ ` Z ) e. ( ZZ>= ` ( |_ ` ( Z / R ) ) ) <-> ( |_ ` ( Z / R ) ) <_ ( |_ ` Z ) )')], 'mpbird',
            '( |_ ` Z ) e. ( ZZ>= ` ( |_ ` ( Z / R ) ) )')
    mss = st([eu, w.inst('fzss2')], 'syl', '%s C_ %s' % (M, IZ))
    aiz = '( %s /\\ n e. %s )' % (ante, IZ)
    saz = mkst(w, aiz)
    niz = saz([saz([], 'simpr', 'n e. %s' % IZ), w.inst('elfznn')], 'syl', 'n e. NN')
    rinr = saz([niz], 'nnrecred', '( 1 / n ) e. RR')
    rin0 = saz([saz([saz([niz], 'nnrpd', 'n e. RR+')], 'rpreccld', '( 1 / n ) e. RR+')], 'rpge0d', '0 <_ ( 1 / n )')
    le1 = st([st([], 'fzfid', '%s e. Fin' % IZ), rinr, rin0, mss], 'fsumless', 'sum_ n e. %s ( 1 / n ) <_ sum_ n e. %s ( 1 / n )' % (M, IZ))
    hb = st([zr, z1, w.inst('harmonicubnd')], 'syl2anc', 'sum_ m e. %s ( 1 / m ) <_ ( ( log ` Z ) + 1 )' % IZ)
    cbs = w.s([w.s([], 'oveq2', '( m = n -> ( 1 / m ) = ( 1 / n ) )')], 'cbvsumv', 'sum_ m e. %s ( 1 / m ) = sum_ n e. %s ( 1 / n )' % (IZ, IZ))
    hb2 = st([w.s([cbs], 'a1i', '( %s -> sum_ m e. %s ( 1 / m ) = sum_ n e. %s ( 1 / n ) )' % (ante, IZ, IZ)), hb], 'eqbrtrrd', 'sum_ n e. %s ( 1 / n ) <_ ( ( log ` Z ) + 1 )' % IZ)
    SM = 'sum_ n e. %s ( 1 / n )' % M; SZ = 'sum_ n e. %s ( 1 / n )' % IZ
    am = '( %s /\\ n e. %s )' % (ante, M)
    smr = st([st([], 'fzfid', '%s e. Fin' % M), w.s([nn_], 'nnrecred', '( %s -> ( 1 / n ) e. RR )' % am)], 'fsumrecl', '%s e. RR' % SM)
    szr = st([st([], 'fzfid', '%s e. Fin' % IZ), rinr], 'fsumrecl', '%s e. RR' % SZ)
    lg = st([st([zrp], 'relogcld', '( log ` Z ) e. RR'), st([], '1red', '1 e. RR')], 'readdcld', '( ( log ` Z ) + 1 ) e. RR')
    le2 = st([smr, szr, lg, le1, hb2], 'letrd', '%s <_ ( ( log ` Z ) + 1 )' % SM)
    le3 = st([smr, lg, st([rn], 'nnrecred', '( 1 / R ) e. RR'), st([st([rrp], 'rpreccld', '( 1 / R ) e. RR+')], 'rpge0d', '0 <_ ( 1 / R )'), le2], 'lemul2ad',
             '( ( 1 / R ) x. %s ) <_ ( ( 1 / R ) x. ( ( log ` Z ) + 1 ) )' % SM)
    ac = st([st([st([zrp], 'relogcld', '( log ` Z ) e. RR')], 'recnd', '( log ` Z ) e. CC'), st([], '1cnd', '1 e. CC')], 'addcomd', '( ( log ` Z ) + 1 ) = ( 1 + ( log ` Z ) )')
    le4 = st([le3, st([ac], 'oveq2d', '( ( 1 / R ) x. ( ( log ` Z ) + 1 ) ) = ( ( 1 / R ) x. ( 1 + ( log ` Z ) ) )')], 'breqtrd',
             '( ( 1 / R ) x. %s ) <_ ( ( 1 / R ) x. ( 1 + ( log ` Z ) ) )' % SM)
    ch = st([fo, st([s1, st([s2], 'eqcomd', 'sum_ n e. %s ( ( 1 / R ) x. ( 1 / n ) ) = ( ( 1 / R ) x. %s )' % (M, SM))], 'eqtrd',
                    'sum_ n e. %s ( 1 / ( R x. n ) ) = ( ( 1 / R ) x. %s )' % (M, SM))], 'eqtrd', 'sum_ d e. %s ( 1 / d ) = ( ( 1 / R ) x. %s )' % (X, SM))
    w.qed([ch, le4], 'eqbrtrd', STATEMENTS['z5invmul'])
    return w


def z5sqfpdvd():
    w = W('z5sqfpdvd', "A squarefree R all of whose primes divide D divides D (Lean Finset.prod_primes_dvd in norm_Mr_one_principal_le): "
                       "( R , D ) is squarefree with the prime set of R, so ( R , D ) = R.")
    ante = split_imp(STATEMENTS['z5sqfpdvd'])[0]
    st = mkst(w, ante)
    rn = st([], 'simpll', 'R e. NN'); r0 = st([], 'simplr', '( mmu ` R ) =/= 0'); dn = st([], 'simprl', 'D e. NN')
    hal = st([], 'simprr', 'A. p e. Prime ( p || R -> p || D )')
    g = '( R gcd D )'
    rz = st([rn], 'nnzd', 'R e. ZZ'); dz = st([dn], 'nnzd', 'D e. ZZ')
    gn = st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % g)
    gd = st([rz, dz, w.inst('gcddvds')], 'syl2anc', '( %s || R /\\ %s || D )' % (g, g))
    gs = st([rn, r0, gn, st([gd], 'simpld', '%s || R' % g), w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` %s ) =/= 0' % g)
    b = '( %s /\\ q e. Prime )' % ante
    sb = mkst(w, b)
    qz = sy(w, b, sb([], 'simpr', 'q e. Prime'), 'prmz', 'q e. ZZ')
    b1 = sb([sb([qz, lift(w, rz, b), lift(w, dz, b), w.inst('dvdsgcdb')], 'syl3anc', '( ( q || R /\\ q || D ) <-> q || %s )' % g)], 'bicomd', '( q || %s <-> ( q || R /\\ q || D ) )' % g)
    idq = w.s([], 'id', '( p = q -> p = q )')
    cgw, neww = w.wcongr('( p || R -> p || D )', {'p': 'q'}, 'p = q', {'p': idq})
    imp = sb([cgw, lift(w, hal, b), sb([], 'simpr', 'q e. Prime')], 'rspcdva', '( q || R -> q || D )')
    b2 = sb([imp], 'pm4.71d', '( q || R <-> ( q || R /\\ q || D ) )')
    bq = sb([b1, b2], 'bitr4d', '( q || %s <-> q || R )' % g)
    rab = st([bq], 'rabbidva', '%s = %s' % (PF(g), PF('R')))
    s1 = st([gn, gs, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = %s' % (PF(g), g))
    s2 = st([rn, r0, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = R' % PF('R'))
    ge = st([st([s1, st([rab], 'prodeq1d', 'prod_ p e. %s p = prod_ p e. %s p' % (PF(g), PF('R')))], 'eqtr3d', '%s = prod_ p e. %s p' % (g, PF('R'))), s2], 'eqtrd', '%s = R' % g)
    gD = st([gd], 'simprd', '%s || D' % g)
    w.qed([gD, st([ge], 'breq1d', '( %s || D <-> R || D )' % g)], 'mpbid', STATEMENTS['z5sqfpdvd'])
    return w




HPC = 'A. c e. Prime ( c || R -> ( C ` c ) = 1 )'


def elqs_t(w, v, D):
    """closed: ( v e. QS(D,R) <-> ( v e. Prime /\\ ( v || R /\\ -. v || D ) ) )"""
    cg_ = w.s([w.s([], 'breq1', '( q = %s -> ( q || R <-> %s || R ) )' % (v, v)),
               w.s([w.s([], 'breq1', '( q = %s -> ( q || %s <-> %s || %s ) )' % (v, D, v, D))], 'notbid', '( q = %s -> ( -. q || %s <-> -. %s || %s ) )' % (v, D, v, D))],
              'anbi12d', '( q = %s -> ( ( q || R /\\ -. q || %s ) <-> ( %s || R /\\ -. %s || %s ) ) )' % (v, D, v, v, D))
    return w.s([cg_], 'elrab', '( %s e. %s <-> ( %s e. Prime /\\ ( %s || R /\\ -. %s || %s ) ) )' % (v, QS(D, 'R'), v, v, v, D))


def z5mrt1():
    w = W('z5mrt1', "Lean hterm of norm_Mr_one_principal_le: at S = 1 and a character equal to 1 at the primes of R, the D-th term of "
                    "M_R has absolute value at most phi ( R ) / D if R | D (then t ( D ; R ) = 1) and 0 otherwise (a prime p | R, "
                    "-. p | D gives the Euler factor 1 + ( - p ) p ^ -1 = 0).")
    ante = split_imp(STATEMENTS['z5mrt1'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); sqr = st([], 'simplr', SQF('R'))
    cfn = st([], 'simprll', CFN); hp = st([], 'simprlr', HPC); dn = st([], 'simprr', 'D e. NN')
    cf = st([cfn], 'simpld', 'C : NN --> CC'); cb = st([cfn], 'simprd', CB)
    rn = st([sqr], 'simpld', 'R e. NN')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    one_c = st([], '1cnd', '1 e. CC')
    LAM = '( ( A bvLam B ) ` D )'; FG = FMP('( R gcd D )'); CDv = '( C ` D )'; Z1 = '( D ^c -u 1 )'
    Q = QS('D', 'R'); E1 = EU(Q, '1')
    X = '( %s x. %s )' % (LAM, FG); XC = '( %s x. %s )' % (X, CDv); XCZ = '( %s x. %s )' % (XC, Z1); T = '( %s x. %s )' % (XCZ, E1)
    Y = '( ( phi ` R ) x. ( 1 / D ) )'
    lr = st([abr, dn, w.inst('bvlamre')], 'syl2anc', '%s e. RR' % LAM)
    gn = st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd D ) e. NN')
    fgr = fmpre(w, ante, gn, '( R gcd D )')
    lc = st([lr], 'recnd', '%s e. CC' % LAM); fgc = st([fgr], 'recnd', '%s e. CC' % FG)
    xc = st([lc, fgc], 'mulcld', '%s e. CC' % X)
    cdc = st([cf, dn], 'ffvelcdmd', '%s e. CC' % CDv)
    dc = st([dn], 'nncnd', 'D e. CC'); d0 = st([dn], 'nnne0d', 'D =/= 0')
    zc = st([dc, st([one_c], 'negcld', '-u 1 e. CC')], 'cxpcld', '%s e. CC' % Z1)
    xcc = st([xc, cdc], 'mulcld', '%s e. CC' % XC); xczc = st([xcc, zc], 'mulcld', '%s e. CC' % XCZ)
    zv = st([st([dc, d0, one_c, w.inst('cxpneg')], 'syl3anc', '%s = ( 1 / ( D ^c 1 ) )' % Z1),
             st([st([dc, w.inst('cxp1')], 'syl', '( D ^c 1 ) = D')], 'oveq2d', '( 1 / ( D ^c 1 ) ) = ( 1 / D )')], 'eqtrd', '%s = ( 1 / D )' % Z1)
    ridr = st([dn], 'nnrecred', '( 1 / D ) e. RR')
    rid0 = st([st([st([dn], 'nnrpd', 'D e. RR+')], 'rpreccld', '( 1 / D ) e. RR+')], 'rpge0d', '0 <_ ( 1 / D )')
    az = st([st([zv], 'fveq2d', '( abs ` %s ) = ( abs ` ( 1 / D ) )' % Z1), st([ridr, rid0], 'absidd', '( abs ` ( 1 / D ) ) = ( 1 / D )')], 'eqtrd',
            '( abs ` %s ) = ( 1 / D )' % Z1)
    one = st([], '1red', '1 e. RR')
    # ---- case R || D
    t = '( %s /\\ R || D )' % ante
    stt = mkst(w, t)
    L = lambda x: lift(w, x, t)
    rd = stt([], 'simpr', 'R || D')
    tq = '( %s /\\ q e. Prime )' % t
    stq = mkst(w, tq)
    qz = sy(w, tq, stq([], 'simpr', 'q e. Prime'), 'prmz', 'q e. ZZ')
    tr = stq([qz, stq([lift(w, rn, tq)], 'nnzd', 'R e. ZZ'), stq([lift(w, dn, tq)], 'nnzd', 'D e. ZZ'), w.inst('dvdstr')], 'syl3anc', '( ( q || R /\\ R || D ) -> q || D )')
    tr2 = stq([lift(w, rd, tq), tr], 'mpan2d', '( q || R -> q || D )')
    nq = stq([tr2, w.s([], 'iman', '( ( q || R -> q || D ) <-> -. ( q || R /\\ -. q || D ) )')], 'sylib', '-. ( q || R /\\ -. q || D )')
    ral = stt([nq], 'ralrimiva', 'A. q e. Prime -. ( q || R /\\ -. q || D )')
    qe = stt([ral, w.s([], 'rabeq0', '( %s = (/) <-> A. q e. Prime -. ( q || R /\\ -. q || D ) )' % Q)], 'sylibr', '%s = (/)' % Q)
    p0 = w.s([w.s([], 'prod0', 'prod_ p e. (/) %s = 1' % EF('p', '1'))], 'a1i', '( %s -> prod_ p e. (/) %s = 1 )' % (t, EF('p', '1')))
    e1v = stt([stt([qe], 'prodeq1d', '%s = prod_ p e. (/) %s' % (E1, EF('p', '1'))), p0], 'eqtrd', '%s = 1' % E1)
    ge = stt([rd, stt([L(rn), L(dn), w.inst('gcdeq')], 'syl2anc', '( ( R gcd D ) = R <-> R || D )')], 'mpbird', '( R gcd D ) = R')
    fge = stt([stt([ge], 'fveq2d', '( mmu ` ( R gcd D ) ) = ( mmu ` R )'), stt([ge], 'fveq2d', '( phi ` ( R gcd D ) ) = ( phi ` R )')], 'oveq12d', '%s = %s' % (FG, FMP('R')))
    mur = stt([stt([L(rn), w.inst('mucl')], 'syl', '( mmu ` R ) e. ZZ')], 'zcnd', '( mmu ` R ) e. CC')
    phn = stt([L(rn), w.inst('phicl')], 'syl', '( phi ` R ) e. NN')
    phr = stt([phn], 'nnred', '( phi ` R ) e. RR'); phc = stt([phn], 'nncnd', '( phi ` R ) e. CC')
    ph0 = stt([stt([phn], 'nnrpd', '( phi ` R ) e. RR+')], 'rpge0d', '0 <_ ( phi ` R )')
    aF = stt([stt([fge], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (FG, FMP('R'))),
              stt([mur, phc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( mmu ` R ) ) x. ( abs ` ( phi ` R ) ) )' % FMP('R'))],
             'eqtrd', '( abs ` %s ) = ( ( abs ` ( mmu ` R ) ) x. ( abs ` ( phi ` R ) ) )' % FG)
    aph = stt([phr, ph0], 'absidd', '( abs ` ( phi ` R ) ) = ( phi ` R )')
    aF2 = stt([aF, stt([aph], 'oveq2d', '( ( abs ` ( mmu ` R ) ) x. ( abs ` ( phi ` R ) ) ) = ( ( abs ` ( mmu ` R ) ) x. ( phi ` R ) )')], 'eqtrd',
              '( abs ` %s ) = ( ( abs ` ( mmu ` R ) ) x. ( phi ` R ) )' % FG)
    amu = stt([L(rn), w.inst('mule1')], 'syl', '( abs ` ( mmu ` R ) ) <_ 1')
    amr = stt([mur], 'abscld', '( abs ` ( mmu ` R ) ) e. RR')
    fb0 = stt([amr, L(one), phr, ph0, amu], 'lemul1ad', '( ( abs ` ( mmu ` R ) ) x. ( phi ` R ) ) <_ ( 1 x. ( phi ` R ) )')
    fb1 = stt([aF2, fb0], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. ( phi ` R ) )' % FG)
    fb = stt([fb1, stt([phc], 'mullidd', '( 1 x. ( phi ` R ) ) = ( phi ` R )')], 'breqtrd', '( abs ` %s ) <_ ( phi ` R )' % FG)
    lb = stt([L(hab), L(dn), w.inst('z5lamabs')], 'syl2anc', '( abs ` %s ) <_ 1' % LAM)
    cdb = cbinst(w, t, L(cb), 'D', L(dn))
    alr = stt([L(lc)], 'abscld', '( abs ` %s ) e. RR' % LAM); afr = stt([L(fgc)], 'abscld', '( abs ` %s ) e. RR' % FG)
    axr = stt([L(xc)], 'abscld', '( abs ` %s ) e. RR' % X); acr = stt([L(cdc)], 'abscld', '( abs ` %s ) e. RR' % CDv)
    ax = stt([L(lc), L(fgc)], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X, LAM, FG))
    bx0 = stt([alr, L(one), afr, phr, stt([L(lc)], 'absge0d', '0 <_ ( abs ` %s )' % LAM), stt([L(fgc)], 'absge0d', '0 <_ ( abs ` %s )' % FG), lb, fb], 'lemul12ad',
              '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( 1 x. ( phi ` R ) )' % (LAM, FG))
    bx = stt([ax, bx0], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. ( phi ` R ) )' % X)
    B1 = '( 1 x. ( phi ` R ) )'; B2 = '( %s x. 1 )' % B1; B3 = '( %s x. ( 1 / D ) )' % B2
    b1r = stt([L(one), phr], 'remulcld', '%s e. RR' % B1); b2r = stt([b1r, L(one)], 'remulcld', '%s e. RR' % B2)
    V2 = '( ( abs ` %s ) x. ( abs ` %s ) )' % (X, CDv)
    b2 = stt([axr, b1r, acr, L(one), stt([L(xc)], 'absge0d', '0 <_ ( abs ` %s )' % X), stt([L(cdc)], 'absge0d', '0 <_ ( abs ` %s )' % CDv), bx, cdb], 'lemul12ad',
             '%s <_ %s' % (V2, B2))
    v2r = stt([axr, acr], 'remulcld', '%s e. RR' % V2)
    b3 = stt([v2r, b2r, L(ridr), L(rid0), b2], 'lemul1ad', '( %s x. ( 1 / D ) ) <_ %s' % (V2, B3))
    tv = stt([stt([e1v], 'oveq2d', '%s = ( %s x. 1 )' % (T, XCZ)), stt([L(xczc)], 'mulridd', '( %s x. 1 ) = %s' % (XCZ, XCZ))], 'eqtrd', '%s = %s' % (T, XCZ))
    at2 = stt([L(xcc), L(zc)], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (XCZ, XC, Z1))
    at3 = stt([L(xc), L(cdc)], 'absmuld', '( abs ` %s ) = %s' % (XC, V2))
    at = stt([stt([tv], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (T, XCZ)), at2], 'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (T, XC, Z1))
    at = stt([at, stt([at3, L(az)], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( 1 / D ) )' % (XC, Z1, V2))], 'eqtrd', '( abs ` %s ) = ( %s x. ( 1 / D ) )' % (T, V2))
    s0 = stt([stt([stt([phc], 'mullidd', '%s = ( phi ` R )' % B1)], 'oveq1d', '%s = ( ( phi ` R ) x. 1 )' % B2), stt([phc], 'mulridd', '( ( phi ` R ) x. 1 ) = ( phi ` R )')],
             'eqtrd', '%s = ( phi ` R )' % B2)
    s1 = stt([s0], 'oveq1d', '%s = %s' % (B3, Y))
    ct = stt([stt([at, b3], 'eqbrtrd', '( abs ` %s ) <_ %s' % (T, B3)), s1], 'breqtrd', '( abs ` %s ) <_ %s' % (T, Y))
    # ---- case -. R || D
    f = '( %s /\\ -. R || D )' % ante
    sf = mkst(w, f)
    AP = 'A. p e. Prime ( p || R -> p || D )'
    fa = '( %s /\\ %s )' % (f, AP)
    sfa = mkst(w, fa)
    hyp = sfa([lift(w, sqr, fa), sfa([lift(w, dn, fa), sfa([], 'simpr', AP)], 'jca', '( D e. NN /\\ %s )' % AP)], 'jca', '( %s /\\ ( D e. NN /\\ %s ) )' % (SQF('R'), AP))
    sp = sfa([hyp, w.inst('z5sqfpdvd')], 'syl', 'R || D')
    nall = w.s([sp, lift(w, sf([], 'simpr', '-. R || D'), fa)], 'pm2.65da', '( %s -> -. %s )' % (f, AP))
    ex_ = sf([nall, w.s([], 'rexanali', '( E. p e. Prime ( p || R /\\ -. p || D ) <-> -. %s )' % AP)], 'sylibr', 'E. p e. Prime ( p || R /\\ -. p || D )')
    cbx = w.s([w.s([w.s([], 'breq1', '( p = t -> ( p || R <-> t || R ) )'), w.s([w.s([], 'breq1', '( p = t -> ( p || D <-> t || D ) )')], 'notbid', '( p = t -> ( -. p || D <-> -. t || D ) )')],
                   'anbi12d', '( p = t -> ( ( p || R /\\ -. p || D ) <-> ( t || R /\\ -. t || D ) ) )')], 'cbvrexvw',
              '( E. p e. Prime ( p || R /\\ -. p || D ) <-> E. t e. Prime ( t || R /\\ -. t || D ) )')
    ext = sf([ex_, cbx], 'sylib', 'E. t e. Prime ( t || R /\\ -. t || D )')
    g = '( ( %s /\\ t e. Prime ) /\\ ( t || R /\\ -. t || D ) )' % f
    sg = mkst(w, g)
    G = lambda x: lift(w, x, g)
    tp = sg([], 'simplr', 't e. Prime'); tr_ = sg([], 'simprl', 't || R'); tnd = sg([], 'simprr', '-. t || D')
    tn = sy(w, g, tp, 'prmnn', 't e. NN')
    tc = sg([tn], 'nncnd', 't e. CC'); t0 = sg([tn], 'nnne0d', 't =/= 0')
    intq = sg([tp, sg([tr_, tnd], 'jca', '( t || R /\\ -. t || D )'), w.s([elqs_t(w, 't', 'D')], 'a1i', '( %s -> ( t e. %s <-> ( t e. Prime /\\ ( t || R /\\ -. t || D ) ) ) )' % (g, Q))],
              'mpbir2and', 't e. %s' % Q)
    # the Euler factor at t vanishes
    fmt = sy(w, g, tp, 'z5fmpprm', '%s = -u ( t - 1 )' % FMP('t'))
    tr__ = sg([tn], 'nnred', 't e. RR')
    fm1 = sg([sg([fmt], 'oveq1d', '( %s - 1 ) = ( -u ( t - 1 ) - 1 )' % FMP('t')), lin.lineq(w, g, '( -u ( t - 1 ) - 1 )', '-u t', leaves={'t': ('RR', tr__)})], 'eqtrd',
             '( %s - 1 ) = -u t' % FMP('t'))
    ccp = w.s([w.s([], 'breq1', '( c = t -> ( c || R <-> t || R ) )'),
               w.s([w.s([], 'fveq2', '( c = t -> ( C ` c ) = ( C ` t ) )')], 'eqeq1d', '( c = t -> ( ( C ` c ) = 1 <-> ( C ` t ) = 1 ) )')], 'imbi12d',
              '( c = t -> ( ( c || R -> ( C ` c ) = 1 ) <-> ( t || R -> ( C ` t ) = 1 ) ) )')
    ct1 = sg([sg([ccp, G(hp), tp], 'rspcdva', '( t || R -> ( C ` t ) = 1 )'), tr_], 'mpd', '( C ` t ) = 1')
    zt = sg([sg([tc, t0, sg([], '1cnd', '1 e. CC'), w.inst('cxpneg')], 'syl3anc', '( t ^c -u 1 ) = ( 1 / ( t ^c 1 ) )'),
             sg([sg([tc, w.inst('cxp1')], 'syl', '( t ^c 1 ) = t')], 'oveq2d', '( 1 / ( t ^c 1 ) ) = ( 1 / t )')], 'eqtrd', '( t ^c -u 1 ) = ( 1 / t )')
    BT = '( ( ( %s - 1 ) x. ( C ` t ) ) x. ( t ^c -u 1 ) )' % FMP('t')
    b1_ = sg([fm1, ct1], 'oveq12d', '( ( %s - 1 ) x. ( C ` t ) ) = ( -u t x. 1 )' % FMP('t'))
    bt = sg([b1_, zt], 'oveq12d', '%s = ( ( -u t x. 1 ) x. ( 1 / t ) )' % BT)
    nt = sg([tc], 'negcld', '-u t e. CC')
    q1 = sg([sg([sg([nt], 'mulridd', '( -u t x. 1 ) = -u t')], 'oveq1d', '( ( -u t x. 1 ) x. ( 1 / t ) ) = ( -u t x. ( 1 / t ) )'),
             sg([tc, sg([tc, t0], 'reccld', '( 1 / t ) e. CC')], 'mulneg1d', '( -u t x. ( 1 / t ) ) = -u ( t x. ( 1 / t ) )')], 'eqtrd',
            '( ( -u t x. 1 ) x. ( 1 / t ) ) = -u ( t x. ( 1 / t ) )')
    q2 = sg([sg([tc, t0], 'recidd', '( t x. ( 1 / t ) ) = 1')], 'negeqd', '-u ( t x. ( 1 / t ) ) = -u 1')
    btv = sg([sg([bt, q1], 'eqtrd', '%s = -u ( t x. ( 1 / t ) )' % BT), q2], 'eqtrd', '%s = -u 1' % BT)
    eft = sg([sg([btv], 'oveq2d', '%s = ( 1 + -u 1 )' % EF('t', '1')), sg([sg([], '1cnd', '1 e. CC')], 'negidd', '( 1 + -u 1 ) = 0')], 'eqtrd', '%s = 0' % EF('t', '1'))
    # fprodeq0g
    qfin, qp_, qss, e1c = eufacts(w, g, G(rn), G(cf), sg([], '1cnd', '1 e. CC'), 'D', '1')
    efcp = eufacts.efc
    cgp = cg(w, EF('p', '1'), 'p', 't')
    gp = '( %s /\\ p = t )' % g
    z0p = w.s([w.s([w.s([], 'simpr', '( %s -> p = t )' % gp), cgp], 'syl', '( %s -> %s = %s )' % (gp, EF('p', '1'), EF('t', '1'))), lift(w, eft, gp)], 'eqtrd',
              '( %s -> %s = 0 )' % (gp, EF('p', '1')))
    e10 = w.s([w.s([], 'nfv', 'F/ p %s' % g), qfin, efcp, intq, z0p], 'fprodeq0g', '( %s -> %s = 0 )' % (g, E1))
    tz = sg([sg([e10], 'oveq2d', '%s = ( %s x. 0 )' % (T, XCZ)), sg([G(xczc)], 'mul01d', '( %s x. 0 ) = 0' % XCZ)], 'eqtrd', '%s = 0' % T)
    atz = sg([sg([tz], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % T), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % g)], 'eqtrd', '( abs ` %s ) = 0' % T)
    tcc = sg([G(xczc), e1c], 'mulcld', '%s e. CC' % T)
    atle = sg([sg([tcc], 'abscld', '( abs ` %s ) e. RR' % T), atz], 'eqled', '( abs ` %s ) <_ 0' % T)
    rl = w.s([w.s([atle], 'ex', '( ( %s /\\ t e. Prime ) -> ( ( t || R /\\ -. t || D ) -> ( abs ` %s ) <_ 0 ) )' % (f, T))], 'rexlimdva',
             '( %s -> ( E. t e. Prime ( t || R /\\ -. t || D ) -> ( abs ` %s ) <_ 0 ) )' % (f, T))
    cf_ = sf([ext, rl], 'mpd', '( abs ` %s ) <_ 0' % T)
    IF = 'if ( R || D , %s , 0 )' % Y
    h1 = w.s([], 'breq2', '( %s = %s -> ( ( abs ` %s ) <_ %s <-> ( abs ` %s ) <_ %s ) )' % (Y, IF, T, Y, T, IF))
    h2 = w.s([], 'breq2', '( 0 = %s -> ( ( abs ` %s ) <_ 0 <-> ( abs ` %s ) <_ %s ) )' % (IF, T, T, IF))
    w.qed([h1, h2, ct, cf_], 'ifbothda', STATEMENTS['z5mrt1'])
    return w



def z5mr1():
    w = W('z5mr1', "Blueprint Lemma 3.4(d) (Lean norm_Mr_one_principal_le): at S = 1 and a character equal to 1 at the primes of the "
                   "squarefree R, | M_R ( 1 , chi ) | <_ ( phi ( R ) / R ) ( 1 + log z2 ) (only the multiples d of R survive, z5mrt1, "
                   "and sum_ ( R | d <_ z2 ) 1 / d <_ ( 1 / R ) ( 1 + log z2 ), z5invmul).")
    ante = split_imp(STATEMENTS['z5mr1'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); b1 = st([], 'simplr', '1 <_ B'); sqr = st([], 'simprl', SQF('R'))
    cfn = st([], 'simprrl', CFN); hp = st([], 'simprrr', HPC)
    cf = st([cfn], 'simpld', 'C : NN --> CC')
    rn = st([sqr], 'simpld', 'R e. NN')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    one_c = st([], '1cnd', '1 e. CC')
    I = '( 1 ... ( |_ ` B ) )'; X = '{ x e. %s | R || x }' % I
    L = '( 1 + ( log ` B ) )'
    PH = '( phi ` R )'
    Yd = '( %s x. ( 1 / d ) )' % PH
    IFd = 'if ( R || d , %s , 0 )' % Yd
    M1 = MRT('d', 'R', '1')
    cvx = st([cf, w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ante), w.inst('fex')], 'syl2anc', 'C e. _V')
    mrv = st([st([st([Ar, Br], 'jca', '( A e. RR /\\ B e. RR )'), st([cvx, rn], 'jca', '( C e. _V /\\ R e. NN )')], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ R e. NN ) )'),
              one_c, w.inst('z5mrval')], 'syl2anc', '%s = sum_ d e. %s %s' % (MR1(), I, M1))
    ifin = st([], 'fzfid', '%s e. Fin' % I)
    a = '( %s /\\ d e. %s )' % (ante, I)
    sa = mkst(w, a)
    dn = sa([sa([], 'simpr', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    mc = sa([lift(w, st([hab, rn], 'jca', '( %s /\\ R e. NN )' % HAB0), a), sa([lift(w, st([cf, one_c], 'jca', '( C : NN --> CC /\\ 1 e. CC )'), a), dn], 'jca',
                                                                                  '( ( C : NN --> CC /\\ 1 e. CC ) /\\ d e. NN )'), w.inst('z5mrtcl')], 'syl2anc', '%s e. CC' % M1)
    tb = sa([lift(w, st([hab, sqr], 'jca', '( %s /\\ %s )' % (HAB0, SQF('R'))), a), sa([lift(w, st([cfn, hp], 'jca', '( %s /\\ %s )' % (CFN, HPC)), a), dn], 'jca',
                                                                                          '( ( %s /\\ %s ) /\\ d e. NN )' % (CFN, HPC)), w.inst('z5mrt1')], 'syl2anc',
            '( abs ` %s ) <_ %s' % (M1, IFd))
    phr = st([st([rn, w.inst('phicl')], 'syl', '%s e. NN' % PH)], 'nnred', '%s e. RR' % PH)
    ydr = sa([lift(w, phr, a), sa([dn], 'nnrecred', '( 1 / d ) e. RR')], 'remulcld', '%s e. RR' % Yd)
    ifr = sa([ydr, sa([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFd)
    fa = st([ifin, mc], 'fsumabs', '( abs ` sum_ d e. %s %s ) <_ sum_ d e. %s ( abs ` %s )' % (I, M1, I, M1))
    fl = st([ifin, sa([mc], 'abscld', '( abs ` %s ) e. RR' % M1), ifr, tb], 'fsumle', 'sum_ d e. %s ( abs ` %s ) <_ sum_ d e. %s %s' % (I, M1, I, IFd))
    # sum over I of the if = sum over the multiples
    elx = w.s([w.s([], 'breq2', '( x = d -> ( R || x <-> R || d ) )')], 'elrab', '( d e. %s <-> ( d e. %s /\\ R || d ) )' % (X, I))
    ax = '( %s /\\ d e. %s )' % (ante, X)
    sx = mkst(w, ax)
    xp = sx([sx([], 'simpr', 'd e. %s' % X), w.s([elx], 'a1i', '( %s -> ( d e. %s <-> ( d e. %s /\\ R || d ) ) )' % (ax, X, I))], 'mpbid', '( d e. %s /\\ R || d )' % I)
    xa = w.s([w.s([], 'simpl', '( %s -> %s )' % (ax, ante)), sx([xp], 'simpld', 'd e. %s' % I)], 'jca', '( %s -> %s )' % (ax, a))
    ifx = sx([sx([xp], 'simprd', 'R || d')], 'iftrued', '%s = %s' % (IFd, Yd))
    ifxc = sx([sx([xa, ifr], 'syl', '%s e. RR' % IFd)], 'recnd', '%s e. CC' % IFd)
    ad_ = '( %s /\\ d e. ( %s \\ %s ) )' % (ante, I, X)
    sd_ = mkst(w, ad_)
    dI = sd_([sd_([], 'simpr', 'd e. ( %s \\ %s )' % (I, X))], 'eldifad', 'd e. %s' % I)
    dnX = sd_([sd_([], 'simpr', 'd e. ( %s \\ %s )' % (I, X))], 'eldifbd', '-. d e. %s' % X)
    e_ = '( %s /\\ R || d )' % ad_
    inX = w.s([lift(w, dI, e_), w.s([], 'simpr', '( %s -> R || d )' % e_), w.s([elx], 'a1i', '( %s -> ( d e. %s <-> ( d e. %s /\\ R || d ) ) )' % (e_, X, I))], 'mpbir2and',
              '( %s -> d e. %s )' % (e_, X))
    nrd = w.s([inX, lift(w, dnX, e_)], 'pm2.65da', '( %s -> -. R || d )' % ad_)
    if0 = sd_([nrd], 'iffalsed', '%s = 0' % IFd)
    xss = w.s([w.s([], 'ssrab2', '%s C_ %s' % (X, I))], 'a1i', '( %s -> %s C_ %s )' % (ante, X, I))
    fs = st([xss, ifxc, if0, ifin], 'fsumss', 'sum_ d e. %s %s = sum_ d e. %s %s' % (X, IFd, I, IFd))
    sx2 = st([ifx], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (X, IFd, X, Yd))
    xfin = st([ifin, xss], 'ssfid', '%s e. Fin' % X)
    dnx = sx([sx([xp], 'simpld', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    fm = st([xfin, st([phr], 'recnd', '%s e. CC' % PH), sx([sx([dnx], 'nncnd', 'd e. CC'), sx([dnx], 'nnne0d', 'd =/= 0')], 'reccld', '( 1 / d ) e. CC')], 'fsummulc2',
            '( %s x. sum_ d e. %s ( 1 / d ) ) = sum_ d e. %s %s' % (PH, X, X, Yd))
    SX = 'sum_ d e. %s ( 1 / d )' % X
    iv = st([rn, st([Br, b1], 'jca', '( B e. RR /\\ 1 <_ B )'), w.inst('z5invmul')], 'syl2anc', '%s <_ ( ( 1 / R ) x. %s )' % (SX, L))
    brp = st([Br, lin.linarith(w, ante, [b1], '0 < B', leaves={'B': ('RR', Br)})], 'elrpd', 'B e. RR+')
    lr = st([st([], '1red', '1 e. RR'), st([brp], 'relogcld', '( log ` B ) e. RR')], 'readdcld', '%s e. RR' % L)
    rinv = st([rn], 'nnrecred', '( 1 / R ) e. RR')
    sxr = st([xfin, sx([dnx], 'nnrecred', '( 1 / d ) e. RR')], 'fsumrecl', '%s e. RR' % SX)
    ph0 = st([st([st([rn, w.inst('phicl')], 'syl', '%s e. NN' % PH)], 'nnrpd', '%s e. RR+' % PH)], 'rpge0d', '0 <_ %s' % PH)
    b2 = st([sxr, st([rinv, lr], 'remulcld', '( ( 1 / R ) x. %s ) e. RR' % L), phr, ph0, iv], 'lemul2ad',
            '( %s x. %s ) <_ ( %s x. ( ( 1 / R ) x. %s ) )' % (PH, SX, PH, L))
    phc = st([phr], 'recnd', '%s e. CC' % PH); rc = st([rn], 'nncnd', 'R e. CC'); r0 = st([rn], 'nnne0d', 'R =/= 0')
    rrc = st([rc, r0], 'reccld', '( 1 / R ) e. CC'); lc = st([lr], 'recnd', '%s e. CC' % L)
    q1 = st([st([phc, rrc, lc], 'mulassd', '( ( %s x. ( 1 / R ) ) x. %s ) = ( %s x. ( ( 1 / R ) x. %s ) )' % (PH, L, PH, L))], 'eqcomd',
            '( %s x. ( ( 1 / R ) x. %s ) ) = ( ( %s x. ( 1 / R ) ) x. %s )' % (PH, L, PH, L))
    q2 = st([st([st([phc, rc, r0], 'divrecd', '( %s / R ) = ( %s x. ( 1 / R ) )' % (PH, PH))], 'eqcomd', '( %s x. ( 1 / R ) ) = ( %s / R )' % (PH, PH))], 'oveq1d',
            '( ( %s x. ( 1 / R ) ) x. %s ) = ( ( %s / R ) x. %s )' % (PH, L, PH, L))
    qq = st([q1, q2], 'eqtrd', '( %s x. ( ( 1 / R ) x. %s ) ) = ( ( %s / R ) x. %s )' % (PH, L, PH, L))
    # the chain
    amr = st([st([hab, rn, cf, one_c, w.inst('z5mrcl')], 'syl22anc', '%s e. CC' % MR1())], 'abscld', '( abs ` %s ) e. RR' % MR1())
    SA = 'sum_ d e. %s ( abs ` %s )' % (I, M1); SI = 'sum_ d e. %s %s' % (I, IFd)
    sar = st([ifin, sa([mc], 'abscld', '( abs ` %s ) e. RR' % M1)], 'fsumrecl', '%s e. RR' % SA)
    sir = st([ifin, ifr], 'fsumrecl', '%s e. RR' % SI)
    c1 = st([st([mrv], 'fveq2d', '( abs ` %s ) = ( abs ` sum_ d e. %s %s )' % (MR1(), I, M1)), fa], 'eqbrtrd', '( abs ` %s ) <_ %s' % (MR1(), SA))
    c2 = st([amr, sar, sir, c1, fl], 'letrd', '( abs ` %s ) <_ %s' % (MR1(), SI))
    ev = st([st([st([fs], 'eqcomd', '%s = sum_ d e. %s %s' % (SI, X, IFd)), sx2], 'eqtrd', '%s = sum_ d e. %s %s' % (SI, X, Yd)),
             st([fm], 'eqcomd', 'sum_ d e. %s %s = ( %s x. %s )' % (X, Yd, PH, SX))], 'eqtrd', '%s = ( %s x. %s )' % (SI, PH, SX))
    c3 = st([c2, ev], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (MR1(), PH, SX))
    c4 = st([amr, st([phr, sxr], 'remulcld', '( %s x. %s ) e. RR' % (PH, SX)), st([phr, st([rinv, lr], 'remulcld', '( ( 1 / R ) x. %s ) e. RR' % L)], 'remulcld',
                                                                                  '( %s x. ( ( 1 / R ) x. %s ) ) e. RR' % (PH, L)), c3, b2], 'letrd',
            '( abs ` %s ) <_ ( %s x. ( ( 1 / R ) x. %s ) )' % (MR1(), PH, L))
    w.qed([c4, qq], 'breqtrd', STATEMENTS['z5mr1'])
    return w


def z5mr1sum():
    w = W('z5mr1sum', "Summed form of Lemma 3.4(d) (Lean sum_inv_mul_norm_Mr_one_le): sum_ ( r e. RSet ) r ^ -1 | M_r ( 1 , chi ) | <_ "
                      "( sum_ r phi ( r ) / r ^ 2 ) ( 1 + log z2 ) for a character equal to 1 at the primes coprime to N (every r in RSet "
                      "is coprime to N, so z5mr1 applies).")
    ante = split_imp(STATEMENTS['z5mr1sum'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); b1 = st([], 'simplr', '1 <_ B')
    nn = st([], 'simprll', 'N e. NN'); yr = st([], 'simprlr', 'Y e. RR')
    cfn = st([], 'simprrl', CFN); hpn = st([], 'simprrr', 'A. c e. Prime ( ( c gcd N ) = 1 -> ( C ` c ) = 1 )')
    cf = st([cfn], 'simpld', 'C : NN --> CC')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    RS = '( N RSet Y )'
    L = '( 1 + ( log ` B ) )'
    rf = st([nn, yr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` Y ) ) /\\ %s e. Fin )' % (RS, RS))
    rsf = st([rf], 'simprd', '%s e. Fin' % RS)
    a = '( %s /\\ r e. %s )' % (ante, RS)
    sa = mkst(w, a)
    el = sa([sa([], 'simpr', 'r e. %s' % RS), sa([lift(w, nn, a), lift(w, yr, a), w.inst('z5elrset')], 'syl2anc',
                                                '( r e. %s <-> ( r e. ( 1 ... ( |_ ` Y ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) ) )' % RS)], 'mpbid',
            '( r e. ( 1 ... ( |_ ` Y ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) )')
    rn = sa([sa([el], 'simpld', 'r e. ( 1 ... ( |_ ` Y ) )'), w.inst('elfznn')], 'syl', 'r e. NN')
    r0 = sa([el], 'simprld', '( mmu ` r ) =/= 0'); rg = sa([el], 'simprrd', '( r gcd N ) = 1')
    # the character is 1 at the primes of r
    ae = '( %s /\\ e e. Prime )' % a
    se = mkst(w, ae)
    ez = sy(w, ae, se([], 'simpr', 'e e. Prime'), 'prmz', 'e e. ZZ')
    rz = se([lift(w, rn, ae)], 'nnzd', 'r e. ZZ'); nz = se([lift(w, nn, ae)], 'nnzd', 'N e. ZZ')
    ngr = se([se([nz, rz, w.inst('gcdcom')], 'syl2anc', '( N gcd r ) = ( r gcd N )'), lift(w, rg, ae)], 'eqtrd', '( N gcd r ) = 1')
    ef = '( %s /\\ e || r )' % ae
    sef = mkst(w, ef)
    nge = sef([lift(w, nz, ef), lift(w, ez, ef), lift(w, rz, ef), lift(w, ngr, ef), sef([], 'simpr', 'e || r'), w.inst('rpdvds')], 'syl32anc', '( N gcd e ) = 1')
    egn = sef([sef([lift(w, ez, ef), lift(w, nz, ef), w.inst('gcdcom')], 'syl2anc', '( e gcd N ) = ( N gcd e )'), nge], 'eqtrd', '( e gcd N ) = 1')
    cce = w.s([w.s([w.s([], 'oveq1', '( c = e -> ( c gcd N ) = ( e gcd N ) )')], 'eqeq1d', '( c = e -> ( ( c gcd N ) = 1 <-> ( e gcd N ) = 1 ) )'),
                    w.s([w.s([], 'fveq2', '( c = e -> ( C ` c ) = ( C ` e ) )')], 'eqeq1d', '( c = e -> ( ( C ` c ) = 1 <-> ( C ` e ) = 1 ) )')], 'imbi12d',
                   '( c = e -> ( ( ( c gcd N ) = 1 -> ( C ` c ) = 1 ) <-> ( ( e gcd N ) = 1 -> ( C ` e ) = 1 ) ) )')
    hpe = sef([cce, lift(w, hpn, ef), lift(w, se([], 'simpr', 'e e. Prime'), ef)], 'rspcdva', '( ( e gcd N ) = 1 -> ( C ` e ) = 1 )')
    ce1 = sef([egn, hpe], 'mpd', '( C ` e ) = 1')
    hpr_e = sa([w.s([ce1], 'ex', '( %s -> ( e || r -> ( C ` e ) = 1 ) )' % ae)], 'ralrimiva', 'A. e e. Prime ( e || r -> ( C ` e ) = 1 )')
    cbc = w.s([w.s([w.s([], 'breq1', '( e = c -> ( e || r <-> c || r ) )'), w.s([w.s([], 'fveq2', '( e = c -> ( C ` e ) = ( C ` c ) )')], 'eqeq1d',
                                                                               '( e = c -> ( ( C ` e ) = 1 <-> ( C ` c ) = 1 ) )')], 'imbi12d',
                   '( e = c -> ( ( e || r -> ( C ` e ) = 1 ) <-> ( c || r -> ( C ` c ) = 1 ) ) )')], 'cbvralvw',
              '( A. e e. Prime ( e || r -> ( C ` e ) = 1 ) <-> A. c e. Prime ( c || r -> ( C ` c ) = 1 ) )')
    hpr = sa([hpr_e, cbc], 'sylib', 'A. c e. Prime ( c || r -> ( C ` c ) = 1 )')
    MR1r = MR1('r')
    mb = sa([sa([lift(w, st([hab, b1], 'jca', '( %s /\\ 1 <_ B )' % HAB0), a), sa([sa([rn, r0], 'jca', '( r e. NN /\\ ( mmu ` r ) =/= 0 )'),
                                                                                     sa([lift(w, cfn, a), hpr], 'jca', '( %s /\\ A. c e. Prime ( c || r -> ( C ` c ) = 1 ) )' % CFN)],
                                                                                    'jca', '( ( r e. NN /\\ ( mmu ` r ) =/= 0 ) /\\ ( %s /\\ A. c e. Prime ( c || r -> ( C ` c ) = 1 ) ) )' % CFN)],
                'jca', '( ( %s /\\ 1 <_ B ) /\\ ( ( r e. NN /\\ ( mmu ` r ) =/= 0 ) /\\ ( %s /\\ A. c e. Prime ( c || r -> ( C ` c ) = 1 ) ) ) )' % (HAB0, CFN)),
             w.inst('z5mr1')], 'syl', '( abs ` %s ) <_ ( ( ( phi ` r ) / r ) x. %s )' % (MR1r, L))
    mrc = sa([lift(w, hab, a), rn, lift(w, cf, a), sa([], '1cnd', '1 e. CC'), w.inst('z5mrcl')], 'syl22anc', '%s e. CC' % MR1r)
    amr = sa([mrc], 'abscld', '( abs ` %s ) e. RR' % MR1r)
    rir = sa([rn], 'nnrecred', '( 1 / r ) e. RR')
    ri0 = sa([sa([sa([rn], 'nnrpd', 'r e. RR+')], 'rpreccld', '( 1 / r ) e. RR+')], 'rpge0d', '0 <_ ( 1 / r )')
    brp = st([Br, lin.linarith(w, ante, [b1], '0 < B', leaves={'B': ('RR', Br)})], 'elrpd', 'B e. RR+')
    lr = st([st([], '1red', '1 e. RR'), st([brp], 'relogcld', '( log ` B ) e. RR')], 'readdcld', '%s e. RR' % L)
    phn = sa([rn, w.inst('phicl')], 'syl', '( phi ` r ) e. NN')
    phr = sa([phn], 'nnred', '( phi ` r ) e. RR'); phc = sa([phn], 'nncnd', '( phi ` r ) e. CC')
    rrp = sa([rn], 'nnrpd', 'r e. RR+'); rc = sa([rn], 'nncnd', 'r e. CC'); r0_ = sa([rn], 'nnne0d', 'r =/= 0')
    pr_ = sa([phr, rrp], 'rerpdivcld', '( ( phi ` r ) / r ) e. RR')
    t1 = sa([amr, sa([pr_, lift(w, lr, a)], 'remulcld', '( ( ( phi ` r ) / r ) x. %s ) e. RR' % L), rir, ri0, mb], 'lemul2ad',
            '( ( 1 / r ) x. ( abs ` %s ) ) <_ ( ( 1 / r ) x. ( ( ( phi ` r ) / r ) x. %s ) )' % (MR1r, L))
    lc = lift(w, st([lr], 'recnd', '%s e. CC' % L), a)
    q1 = sa([sa([sa([rc, r0_], 'reccld', '( 1 / r ) e. CC'), sa([phc, rc, r0_], 'divcld', '( ( phi ` r ) / r ) e. CC'), lc], 'mulassd',
                '( ( ( 1 / r ) x. ( ( phi ` r ) / r ) ) x. %s ) = ( ( 1 / r ) x. ( ( ( phi ` r ) / r ) x. %s ) )' % (L, L))], 'eqcomd',
            '( ( 1 / r ) x. ( ( ( phi ` r ) / r ) x. %s ) ) = ( ( ( 1 / r ) x. ( ( phi ` r ) / r ) ) x. %s )' % (L, L))
    q2 = sa([sa([], '1cnd', '1 e. CC'), rc, phc, rc, r0_, r0_], 'divmuldivd', '( ( 1 / r ) x. ( ( phi ` r ) / r ) ) = ( ( 1 x. ( phi ` r ) ) / ( r x. r ) )')
    q3 = sa([sa([phc], 'mullidd', '( 1 x. ( phi ` r ) ) = ( phi ` r )'), sa([sa([rc], 'sqvald', '( r ^ 2 ) = ( r x. r )')], 'eqcomd', '( r x. r ) = ( r ^ 2 )')], 'oveq12d',
            '( ( 1 x. ( phi ` r ) ) / ( r x. r ) ) = ( ( phi ` r ) / ( r ^ 2 ) )')
    q23 = sa([q2, q3], 'eqtrd', '( ( 1 / r ) x. ( ( phi ` r ) / r ) ) = ( ( phi ` r ) / ( r ^ 2 ) )')
    qq = sa([q1, sa([q23], 'oveq1d', '( ( ( 1 / r ) x. ( ( phi ` r ) / r ) ) x. %s ) = ( ( ( phi ` r ) / ( r ^ 2 ) ) x. %s )' % (L, L))], 'eqtrd',
            '( ( 1 / r ) x. ( ( ( phi ` r ) / r ) x. %s ) ) = ( ( ( phi ` r ) / ( r ^ 2 ) ) x. %s )' % (L, L))
    TR = '( ( 1 / r ) x. ( abs ` %s ) )' % MR1r
    tb = sa([t1, qq], 'breqtrd', '%s <_ ( ( ( phi ` r ) / ( r ^ 2 ) ) x. %s )' % (TR, L))
    r2rp = sa([rrp, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % a)], 'rpexpcld', '( r ^ 2 ) e. RR+')
    pq = sa([phr, r2rp], 'rerpdivcld', '( ( phi ` r ) / ( r ^ 2 ) ) e. RR')
    fl = st([rsf, sa([rir, amr], 'remulcld', '%s e. RR' % TR), sa([pq, lift(w, lr, a)], 'remulcld', '( ( ( phi ` r ) / ( r ^ 2 ) ) x. %s ) e. RR' % L), tb], 'fsumle',
            'sum_ r e. %s %s <_ sum_ r e. %s ( ( ( phi ` r ) / ( r ^ 2 ) ) x. %s )' % (RS, TR, RS, L))
    fm = st([rsf, st([lr], 'recnd', '%s e. CC' % L), sa([pq], 'recnd', '( ( phi ` r ) / ( r ^ 2 ) ) e. CC')], 'fsummulc1',
            '( sum_ r e. %s ( ( phi ` r ) / ( r ^ 2 ) ) x. %s ) = sum_ r e. %s ( ( ( phi ` r ) / ( r ^ 2 ) ) x. %s )' % (RS, L, RS, L))
    w.qed([fl, fm], 'breqtrrd', STATEMENTS['z5mr1sum'])
    return w


if __name__ == '__main__':
    import z5clib
    for f in sys.argv[1:]:
        z5clib.run(globals()[f]())
