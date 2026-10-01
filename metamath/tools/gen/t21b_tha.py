"""Sortie T21b: t21tha (thetaAP_sub_le)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from t21b_psi import *


def gen_tha():
    w = W('t21tha', 'theta in progressions from the explicit formula: ~ t21psi plus the prime-power gap ` 0 <_ psi - theta <_ 2 sqrt Y log Y ` (Lean ` thetaAP_sub_le ` ; ~ psiapsubsqrt , ~ thetaaplepsiap ).')
    A0, concl = split_imp(SB['t21tha'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    nn = u['N e. NN']; az = u['A e. ZZ']; yr = u['Y e. RR']; y100 = u['; ; 1 0 0 <_ Y']
    y1 = lin.linarith(w, A0, [y100], '1 <_ Y', leaves={'Y': yr})
    ERRS = SB['t21psi'].rsplit(' <_ ', 1)[1][:-2]
    TH = '( A ( thetaAP ` N ) Y )'
    C = '( Y / %s )' % PHI
    ps = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    p1 = s([ps, w.inst('t21psi')], 'syl', '( abs ` ( %s - %s ) ) <_ %s' % (PSIAP, C, ERRS))
    g = ap(w, A0, [nn, az, yr, y1], 'psiapsubsqrt', '( %s - %s ) <_ %s' % (PSIAP, TH, SQL('Y')))
    tl = ap(w, A0, [nn, az, yr], 'thetaaplepsiap', '%s <_ %s' % (TH, PSIAP))
    phn = s([nn, w.inst('phicl')], 'syl', '%s e. NN' % PHI)
    cr = s([yr, s([phn], 'nnrpd', '%s e. RR+' % PHI)], 'rerpdivcld', '%s e. RR' % C)
    psr = ap(w, A0, [nn, az, yr], 'psiapcl', '%s e. RR' % PSIAP)
    thr = ap(w, A0, [nn, az, yr], 'thetaapcl', '%s e. RR' % TH)
    yp = rp_of(w, A0, yr, y1, 'Y')
    sqr = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+') and s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpred', '( sqrt ` Y ) e. RR')], 'remulcld', '( 2 x. ( sqrt ` Y ) ) e. RR')
    sqr = s([sqr, s([yp], 'relogcld', '( log ` Y ) e. RR')], 'remulcld', '%s e. RR' % SQL('Y'))
    er = s([s([s([p1], 'x', 'x')], 'x', 'x') if False else None], 'x', 'x') if False else None
    # ERRS real: recover from p1 by letrd-free route: abs <_ ERRS needs ERRS real for absled; get it as a leaf via absge0 bound
    import t21b_h as H
    pN = eferr_parts(w, A0, 'N', s([nn], 'nnred', 'N e. RR'), s([nn], 'nnge1d', '1 <_ N'), yr, y1, u['T e. RR'], u['2 <_ T'])
    omn = s([s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OM('N'))
    omlr = s([s([omn], 'nn0red', '%s e. RR' % OM('N')), s([yp], 'relogcld', '( log ` Y ) e. RR')], 'remulcld', '%s e. RR' % OML)
    errr = s([pN['er'], omlr], 'readdcld', '%s e. RR' % ERR)
    dfin = s([nn, w.s([w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'), w.s([], 'eqid', '%s = %s' % (DBN, DBN))], 'dchrfi', '( N e. NN -> %s e. Fin )' % DBN)], 'syl', '%s e. Fin' % DBN)
    Ax = '( %s /\\ x e. %s )' % (A0, DBN)
    fin_, tc_, dd = sc_terms(w, Ax, 'N', 'x', lift(w, nn, Ax), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, DBN)), lift(w, u['T e. RR'], Ax), lift(w, yr, Ax))
    C2 = dd['C2']; s2 = S_(w, C2)
    import t21alib as _ta
    orr = s2([dd['ordn']], 'nnred', '( %s holord q ) e. RR' % EX_)
    wr, _, _ = _ta.wt_facts(w, C2, orr, s2([s2([dd['ordn']], 'nnnn0d', '( %s holord q ) e. NN0' % EX_)], 'nn0ge0d', '0 <_ ( %s holord q )' % EX_), dd['qf'])
    yre = s2([lift(w, yp, C2), dd['qf']['re']], 'rpcxpcld', '( Y ^c ( Re ` q ) ) e. RR+')
    wxr = w.s([fin_, s2([wr, s2([yre], 'rpred', '( Y ^c ( Re ` q ) ) e. RR')], 'remulcld', '( %s x. ( Y ^c ( Re ` q ) ) ) e. RR' % WT(EX_))], 'fsumrecl', '( %s -> %s e. RR )' % (Ax, Wx))
    ztr = s([dfin, wxr], 'fsumrecl', '%s e. RR' % ZTT)
    phr = s([phn], 'nnred', '%s e. RR' % PHI)
    q3 = s([s([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), s([phn], 'nnrpd', '%s e. RR+' % PHI)], 'rerpdivcld', '( 3 / %s ) e. RR' % PHI)
    errsr = s([errr, s([q3, ztr], 'remulcld', '( ( 3 / %s ) x. %s ) e. RR' % (PHI, ZTT))], 'readdcld', '%s e. RR' % ERRS)
    D1 = '( %s - %s )' % (PSIAP, C)
    ab1 = s([p1, s([s([psr, cr], 'resubcld', '%s e. RR' % D1), errsr], 'absled', '( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (D1, ERRS, ERRS, D1, D1, ERRS))], 'mpbid', '( -u %s <_ %s /\\ %s <_ %s )' % (ERRS, D1, D1, ERRS))
    lo = s([ab1], 'simpld', '-u %s <_ %s' % (ERRS, D1)); hi = s([ab1], 'simprd', '%s <_ %s' % (D1, ERRS))
    G = SQL('Y')
    RHS = '( %s + %s )' % (ERRS, G)
    D2 = '( %s - %s )' % (TH, C)
    lv = {PSIAP: psr, TH: thr, C: cr, ERRS: errsr, G: sqr}
    D3 = '( %s - %s )' % (PSIAP, TH)
    d1r = s([psr, cr], 'resubcld', '%s e. RR' % D1); d3r = s([psr, thr], 'resubcld', '%s e. RR' % D3)
    nE = s([errsr], 'renegcld', '-u %s e. RR' % ERRS)
    a = s([nE, sqr, d1r, d3r, lo, g], 'le2subd', '( -u %s - %s ) <_ ( %s - %s )' % (ERRS, G, D1, D3))
    b = s([s([errsr], 'recnd', '%s e. CC' % ERRS), s([sqr], 'recnd', '%s e. CC' % G)], 'negdi2d', '-u %s = ( -u %s - %s )' % (RHS, ERRS, G))
    c = s([s([psr], 'recnd', '%s e. CC' % PSIAP), s([cr], 'recnd', '%s e. CC' % C), s([thr], 'recnd', '%s e. CC' % TH)], 'nnncan1d', '( %s - %s ) = ( %s - %s )' % (D1, D3, TH, C))
    l2 = s([s([b, a], 'eqbrtrd', '-u %s <_ ( %s - %s )' % (RHS, D1, D3)), c], 'breqtrd', '-u %s <_ %s' % (RHS, D2))
    e1 = s([thr, psr, cr, tl], 'lesub1dd', '%s <_ %s' % (D2, D1))
    g0 = s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpred', '( sqrt ` Y ) e. RR'),
               s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpge0d', '0 <_ ( sqrt ` Y )')], 'mulge0d', '0 <_ ( 2 x. ( sqrt ` Y ) )') if False else None], 'x', 'x') if False else None
    sq0 = s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpred', '( sqrt ` Y ) e. RR')], 'remulcld', '( 2 x. ( sqrt ` Y ) ) e. RR'),
             s([yp], 'relogcld', '( log ` Y ) e. RR'),
             s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpred', '( sqrt ` Y ) e. RR'),
                s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpge0d', '0 <_ ( sqrt ` Y )')], 'mulge0d', '0 <_ ( 2 x. ( sqrt ` Y ) )'),
             ap(w, A0, [yr, y1], 'logge0', '0 <_ ( log ` Y )')], 'mulge0d', '0 <_ %s' % G)
    e2 = s([s([errsr, sqr], 'addge01d', '( 0 <_ %s <-> %s <_ %s )' % (G, ERRS, RHS)), sq0], 'mpbird', '%s <_ %s' % (ERRS, RHS)) if False else s([sq0, s([errsr, sqr], 'addge01d', '( 0 <_ %s <-> %s <_ %s )' % (G, ERRS, RHS))], 'mpbid', '%s <_ %s' % (ERRS, RHS))
    rr = s([errsr, sqr], 'readdcld', '%s e. RR' % RHS)
    h2 = s([s([thr, cr], 'resubcld', '%s e. RR' % D2), d1r, rr, e1, s([d1r, errsr, rr, hi, e2], 'letrd', '%s <_ %s' % (D1, RHS))], 'letrd', '%s <_ %s' % (D2, RHS))
    fin = s([s([l2, h2], 'jca', '( -u %s <_ %s /\\ %s <_ %s )' % (RHS, D2, D2, RHS)), s([s([thr, cr], 'resubcld', '%s e. RR' % D2), s([errsr, sqr], 'readdcld', '%s e. RR' % RHS)], 'absled',
             '( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (D2, RHS, RHS, D2, D2, RHS))], 'mpbird', concl)
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21tha']))
    return go(w)


if __name__ == '__main__':
    gen_tha()
