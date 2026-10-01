"""Sortie T21b: t21rv (the pinned constants rho, nu)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
import cl as _cl


def gen_rv():
    w = W('t21rv', 'The pinned constants of T2.1: ` rho = ( 200 / 9 ) log ( 6912 G / E ) > 0 ` with ` 6912 G e ^ ( - ( 9 / 200 ) rho ) = E ` , and ` nu = 27 G e ^ ( 28 rho ) / E >_ 1 ` (Lean ` theta_AP_T21 ` 1945-1966).')
    A0, concl = split_imp(SB['t21rv'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    gr, g1, er, e0, e3 = u['G e. RR'], u['1 <_ G'], u['E e. RR'], u['0 < E'], u['E < ( 1 / 3 )']
    ep = s([er, e0], 'elrpd', 'E e. RR+')
    gp = s([gr, lin.linarith(w, A0, [g1], '0 < G', leaves={'G': gr})], 'elrpd', 'G e. RR+')
    GG = '( %s x. G )' % N6912
    ggp = s([s([num.rp_nat(w, 6912)], 'a1i', '%s e. RR+' % N6912), gp], 'rpmulcld', '%s e. RR+' % GG)
    Q = '( %s / E )' % GG
    qp = s([ggp, ep], 'rpdivcld', '%s e. RR+' % Q)
    lt = lin.linarith(w, A0, [e3, g1], '( 1 x. E ) < %s' % GG, leaves={'E': er, 'G': gr})
    q1 = s([lt, s([s([], '1red', '1 e. RR'), s([ggp], 'rpred', '%s e. RR' % GG), ep], 'ltmuldivd', '( ( 1 x. E ) < %s <-> 1 < %s )' % (GG, Q))], 'mpbid', '1 < %s' % Q)
    LQ = '( log ` %s )' % Q
    lq = s([s([q1, s([s([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+'), qp], 'logltb', '( 1 < %s <-> ( log ` 1 ) < %s )' % (Q, LQ))], 'mpbid', '( log ` 1 ) < %s' % LQ)], 'x', 'x') if False else None
    lq = s([q1, ap(w, A0, [s([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+'), qp], 'logltb', '( 1 < %s <-> ( log ` 1 ) < %s )' % (Q, LQ))], 'mpbid', '( log ` 1 ) < %s' % LQ)
    lq0 = s([s([s([w.s([], 'log1', '( log ` 1 ) = 0')], 'a1i', '( log ` 1 ) = 0')], 'eqcomd', '0 = ( log ` 1 )'), lq], 'eqbrtrd', '0 < %s' % LQ)
    lqr = s([qp], 'relogcld', '%s e. RR' % LQ)
    lqp = s([lqr, lq0], 'elrpd', '%s e. RR+' % LQ)
    rp_ = s([s([num.rp(w, '( ; ; 2 0 0 / 9 )')], 'a1i', '( ; ; 2 0 0 / 9 ) e. RR+'), lqp], 'rpmulcld', '%s e. RR+' % RHO)
    # exp ( - ( 9 / 200 ) rho ) = E / ( 6912 G )
    cl = _cl.Closure(w, A0, {})
    cl.leaf(LQ, 'RR', lqr); cl.atom(LQ)
    cl.leaf('( ; ; 2 0 0 / 9 )', 'RR', s([num.real(w, '( ; ; 2 0 0 / 9 )')], 'a1i', '( ; ; 2 0 0 / 9 ) e. RR'))
    cl.leaf(F9200, 'RR', s([num.real(w, F9200)], 'a1i', '%s e. RR' % F9200))
    from mvlib import ringeq as ringeq_d
    ex_ = ringeq_d(w, A0, '( -u %s x. %s )' % (F9200, RHO), '-u %s' % LQ, cl)
    EX = '( exp ` ( -u %s x. %s ) )' % (F9200, RHO)
    en = s([s([lqr], 'recnd', '%s e. CC' % LQ), w.inst('efneg')], 'syl', '( exp ` -u %s ) = ( 1 / ( exp ` %s ) )' % (LQ, LQ))
    el = s([qp, w.inst('reeflog')], 'syl', '( exp ` %s ) = %s' % (LQ, Q))
    ggc = s([ggp], 'rpcnd', '%s e. CC' % GG); ec = s([ep], 'rpcnd', 'E e. CC')
    rd = s([ggc, ec, s([ggp], 'rpne0d', '%s =/= 0' % GG), s([ep], 'rpne0d', 'E =/= 0')], 'recdivd', '( 1 / %s ) = ( E / %s )' % (Q, GG))
    exe = s([s([s([ex_], 'fveq2d', '%s = ( exp ` -u %s )' % (EX, LQ)), en], 'eqtrd', '%s = ( 1 / ( exp ` %s ) )' % (EX, LQ)), s([s([el], 'oveq2d', '( 1 / ( exp ` %s ) ) = ( 1 / %s )' % (LQ, Q)), rd], 'eqtrd', '( 1 / ( exp ` %s ) ) = ( E / %s )' % (LQ, GG))], 'eqtrd', '%s = ( E / %s )' % (EX, GG))
    c69 = s([num.cc(w, N6912)], 'a1i', '%s e. CC' % N6912); n69 = s([num.ne0_nat(w, 6912)], 'a1i', '%s =/= 0' % N6912) if hasattr(num, 'ne0_nat') else None
    gc = s([gp], 'rpcnd', 'G e. CC'); gn = s([gp], 'rpne0d', 'G =/= 0')
    dd = s([ec, c69, gc, n69, gn], 'divdiv1d', '( ( E / %s ) / G ) = ( E / %s )' % (N6912, GG))
    e69 = '( E / %s )' % N6912
    e69c = s([ec, c69, n69], 'divcld', '%s e. CC' % e69)
    g1_ = s([e69c, gc, gn], 'divcan2d', '( G x. ( %s / G ) ) = %s' % (e69, e69))
    s1 = s([s([exe, s([dd], 'eqcomd', '( E / %s ) = ( %s / G )' % (GG, e69))], 'eqtrd', '%s = ( %s / G )' % (EX, e69))], 'oveq2d', '( G x. %s ) = ( G x. ( %s / G ) )' % (EX, e69))
    s2 = s([s1, g1_], 'eqtrd', '( G x. %s ) = %s' % (EX, e69))
    s3 = s([s([s2], 'oveq2d', '( %s x. ( G x. %s ) ) = ( %s x. %s )' % (N6912, EX, N6912, e69)), s([ec, c69, n69], 'divcan2d', '( %s x. %s ) = E' % (N6912, e69))], 'eqtrd', '( %s x. ( G x. %s ) ) = E' % (N6912, EX))
    h3 = s([s3, s([er], 'leidd', 'E <_ E')], 'eqbrtrd', '( %s x. ( G x. %s ) ) <_ E' % (N6912, EX))
    # nu
    R28 = '( ; 2 8 x. %s )' % RHO
    r28p = s([s([num.rp_nat(w, 28)], 'a1i', '; 2 8 e. RR+'), rp_], 'rpmulcld', '%s e. RR+' % R28)
    e28p = s([s([r28p], 'rpred', '%s e. RR' % R28)], 'rpefcld', '%s e. RR+' % E28R)
    GE = '( G x. %s )' % E28R
    gep = s([gp, e28p], 'rpmulcld', '%s e. RR+' % GE)
    NUM = '( ; 2 7 x. %s )' % GE
    nump = s([s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+'), gep], 'rpmulcld', '%s e. RR+' % NUM)
    vp = s([nump, ep], 'rpdivcld', '%s e. RR+' % VV)
    ev = s([s([nump], 'rpcnd', '%s e. CC' % NUM), ec, s([ep], 'rpne0d', 'E =/= 0')], 'divcan2d', '( E x. %s ) = %s' % (VV, NUM))
    h4 = s([s([s([nump], 'rpred', '%s e. RR' % NUM)], 'leidd', '%s <_ %s' % (NUM, NUM)), s([ev], 'eqcomd', '%s = ( E x. %s )' % (NUM, VV))], 'breqtrd', '%s <_ ( E x. %s )' % (NUM, VV))
    eg = ap(w, A0, [r28p], 'efgt1p', '( 1 + %s ) < %s' % (R28, E28R))
    from c8lib import lin8
    e1 = lin8(w, A0, [eg, s([r28p], 'rpge0d', '0 <_ %s' % R28)], '1 <_ %s' % E28R, {R28: s([r28p], 'rpred', '%s e. RR' % R28), E28R: s([e28p], 'rpred', '%s e. RR' % E28R)})
    z1 = s([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    one = s([], '1red', '1 e. RR')
    ge = s([one, gr, one, s([e28p], 'rpred', '%s e. RR' % E28R), z1, z1, g1, e1], 'lemul12ad', '( 1 x. 1 ) <_ %s' % GE)
    ge1 = s([s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), ge], 'eqbrtrrd', '1 <_ %s' % GE)
    le = lin8(w, A0, [e3, ge1], '( 1 x. E ) <_ %s' % NUM, {'E': er, GE: s([gep], 'rpred', '%s e. RR' % GE)})
    v1 = s([le, s([one, s([nump], 'rpred', '%s e. RR' % NUM), ep], 'lemuldivd', '( ( 1 x. E ) <_ %s <-> 1 <_ %s )' % (NUM, VV))], 'mpbid', '1 <_ %s' % VV)
    fin = s([s([s([rp_, vp], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (RHO, VV)), s([h3, h4], 'jca', '( ( %s x. ( G x. %s ) ) <_ E /\\ %s <_ ( E x. %s ) )' % (N6912, EX, NUM, VV))], 'jca',
             '( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( ( %s x. ( G x. %s ) ) <_ E /\\ %s <_ ( E x. %s ) ) )' % (RHO, VV, N6912, EX, NUM, VV)), v1], 'jca', concl)
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21rv']))
    return go(w)


if __name__ == '__main__':
    gen_rv()
