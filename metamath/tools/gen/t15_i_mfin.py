import sys, os
sys.path.insert(0,'/Users/dan/carmichael/metamath/tools'); sys.path.insert(0,'/Users/dan/carmichael/metamath/tools/gen')
from t15_h_inst import *
import t15_e_kind


def closed_S0(w):
    k = t15_e_kind.Kind.__new__(t15_e_kind.Kind)
    k.w = w; k.memo = {}
    return k.closed_st(S0)


def t15mfin():
    w = W('t15mfin', 'The concrete machine is a finite TM2 machine (Lean: FinTM2).')
    ph = '( C e. NN0 /\\ K e. NN )'
    g1, l1, st, gl = sets(w)
    G2 = '<. <. TMGam , %s >. , TMSt >.' % LB
    TUP = '<. <. <. <. TMGam , %s >. , TMSt >. , <. 0 , 1 >. >. , <. <. %s , %s >. , %s >. >.' % (LB, MAIN, S0, PG)
    mdf = w.s([], 'df-tmmach', '%s = <. <. %s , <. 0 , 1 >. >. , <. <. %s , %s >. , %s >. >.' % (MACH, TY, MAIN, S0, PG))
    tdf = w.s([], 'df-tmty', '%s = %s' % (TY, G2))
    e1 = w.s([tdf], 'opeq1i', '<. %s , <. 0 , 1 >. >. = <. %s , <. 0 , 1 >. >.' % (TY, G2))
    e2 = w.s([e1], 'opeq1i', '<. <. %s , <. 0 , 1 >. >. , <. <. %s , %s >. , %s >. >. = %s' % (TY, MAIN, S0, PG, TUP))
    meq = w.s([mdf, e2], 'eqtri', '%s = %s' % (MACH, TUP))
    # sets
    body = 'if ( ( %s TMWalk ( x ` -u 1 ) ) e. ( TM2Stmt ` %s ) , ( %s TMWalk ( x ` -u 1 ) ) , <. 6 , (/) >. )' % (RT, TY, RT)
    pdf = w.s([], 'df-tmprog', '%s = ( x e. %s |-> %s )' % (PG, LB, body))
    pv = w.s([pdf, w.s([l1], 'mptex', '( x e. %s |-> %s ) e. _V' % (LB, body))], 'eqeltri', '%s e. _V' % PG)
    j1 = w.s([g1, l1, st], '3pm3.2i', '( TMGam e. _V /\\ %s e. _V /\\ TMSt e. _V )' % LB)
    j2 = w.s([w.s([], 'c0ex', '0 e. _V'), w.s([], '1ex', '1 e. _V')], 'pm3.2i', '( 0 e. _V /\\ 1 e. _V )')
    j3 = w.s([w.s([], 'fvex', '%s e. _V' % MAIN), w.s([], 'opex', '%s e. _V' % S0), pv], '3pm3.2i', '( %s e. _V /\\ %s e. _V /\\ %s e. _V )' % (MAIN, S0, PG))
    RHS = ('( ( Fun TMGam /\\ dom TMGam e. Fin /\\ ( 0 e. dom TMGam /\\ 1 e. dom TMGam /\\ ( TMGam ` 0 ) e. Fin ) ) /\\ ( %s e. Fin /\\ %s e. %s ) /\\ ( TMSt e. Fin /\\ %s e. TMSt /\\ %s : %s --> ( TM2Stmt ` %s ) ) )'
           % (LB, MAIN, LB, S0, PG, LB, G2))
    ef = w.s([j1, j2, j3, w.inst('elfintm2')], 'mp3an', '( %s e. FinTM2 <-> %s )' % (TUP, RHS))
    fn = w.s([], 'tmgamfn', 'TMGam Fn ( 0 ..^ 8 )')
    fu = w.s([fn, w.inst('fnfun')], 'ax-mp', 'Fun TMGam')
    dm = w.s([fn, w.inst('fndm')], 'ax-mp', 'dom TMGam = ( 0 ..^ 8 )')
    dfi = w.s([], 'tmgamdm', 'dom TMGam e. Fin')

    def in8(k):
        a = num.nn0(w, k); b = w.s([], '8nn', '8 e. NN'); c = num.le_nat(w, k, 8, strict=True)
        e = w.s([], 'elfzo0', '( %d e. ( 0 ..^ 8 ) <-> ( %d e. NN0 /\\ 8 e. NN /\\ %d < 8 ) )' % (k, k, k))
        f = w.s([a, b, c, e], 'mpbir3an', '%d e. ( 0 ..^ 8 )' % k)
        return w.s([f, dm], 'eleqtrri', '%d e. dom TMGam' % k), f
    d0, f0 = in8(0)
    d1, _ = in8(1)
    g0 = w.s([w.s([f0, w.inst('tmgamfv')], 'ax-mp', "( TMGam ` 0 ) = Gamma'"), w.s([], 'gammafi', "Gamma' e. Fin")], 'eqeltri', '( TMGam ` 0 ) e. Fin')
    a = w.s([fu, dfi, w.s([d0, d1, g0], '3pm3.2i', '( 0 e. dom TMGam /\\ 1 e. dom TMGam /\\ ( TMGam ` 0 ) e. Fin )')], '3pm3.2i',
            '( Fun TMGam /\\ dom TMGam e. Fin /\\ ( 0 e. dom TMGam /\\ 1 e. dom TMGam /\\ ( TMGam ` 0 ) e. Fin ) )')
    lf = w.s([], 't15lblfi', '( %s -> ( %s e. Fin /\\ %s e. %s ) )' % (ph, LB, MAIN, LB))
    sz = closed_S0(w)
    pg = w.s([], 't15prog', '( %s -> %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) )' % (ph, PG, TY, TY))
    ty = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    tl = w.s([ty], 'simp2i', '( 2nd ` ( 1st ` %s ) ) = %s' % (TY, LB))
    s1 = w.s([tdf], 'fveq2i', '( TM2Stmt ` %s ) = ( TM2Stmt ` %s )' % (TY, G2))
    fq = w.s([tl, s1], 'feq23i', '( %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) <-> %s : %s --> ( TM2Stmt ` %s ) )' % (PG, TY, TY, PG, LB, G2))
    pg2 = w.s([pg, fq], 'sylib', '( %s -> %s : %s --> ( TM2Stmt ` %s ) )' % (ph, PG, LB, G2))
    c = w.s([a1(w, ph, w.s([], 'tmstfi', 'TMSt e. Fin'), 'TMSt e. Fin'), a1(w, ph, sz, '%s e. TMSt' % S0), pg2], '3jca',
            '( %s -> ( TMSt e. Fin /\\ %s e. TMSt /\\ %s : %s --> ( TM2Stmt ` %s ) ) )' % (ph, S0, PG, LB, G2))
    allr = w.s([a1(w, ph, a, '( Fun TMGam /\\ dom TMGam e. Fin /\\ ( 0 e. dom TMGam /\\ 1 e. dom TMGam /\\ ( TMGam ` 0 ) e. Fin ) )'), lf, c], '3jca', '( %s -> %s )' % (ph, RHS))
    mt = w.s([allr, a1(w, ph, ef, '( %s e. FinTM2 <-> %s )' % (TUP, RHS))], 'mpbird', '( %s -> %s e. FinTM2 )' % (ph, TUP))
    w.qed([a1(w, ph, meq, '%s = %s' % (MACH, TUP)), mt], 'eqeltrd', '( %s -> %s e. FinTM2 )' % (ph, MACH))
    return w


if __name__ == '__main__':
    t15mfin().run()
