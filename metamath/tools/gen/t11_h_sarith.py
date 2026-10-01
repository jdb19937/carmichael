"""T11: the arithmetic of the scan loop (Steps23.lean ` scanIters ` and the facts ` scanBody_runs ` reads).

  tmscsome  a successful scan stops at a success ` k' ` with ` k <_ k' < k + fuel ` and returns its pool
  tmscmin   no success below the one returned
  tmscnone  a failed scan has no success in its range

    MM_DB=sorties/t11.mm python3 tools/gen/t11_h_sarith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
from lin import linarith, lineq
from cl import Closure
from t5lib import Ctx

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


STMTS = {}
SC = lambda k, f: '( ( ( ( ( W Scan F ) ` Z ) ` O ) ` %s ) ` %s )' % (k, f)
SCO = lambda k, f: '( 1st ` %s )' % SC(k, f)
SOME = lambda k, f: '%s =/= ( inr ` (/) )' % SCO(k, f)
KF = lambda k, f: '( 1st ` ( 2nd ` %s ) )' % SCO(k, f)
PF = lambda k, f: '( 2nd ` ( 2nd ` %s ) )' % SCO(k, f)
PA = lambda j: '( ( ( W PoolAlg F ) ` Z ) ` %s )' % j
CP = lambda j: '( W CoprimeTo %s )' % j
SUC = lambda j: '( ( 1st ` %s ) = 1o /\\ O <_ ( # ` ( 1st ` %s ) ) )' % (CP(j), PA(j))
CONC = lambda k, f: '( ( %s <_ %s /\\ %s < ( %s + %s ) ) /\\ ( %s /\\ %s = ( 1st ` %s ) ) )' % (k, KF(k, f), KF(k, f), k, f, SUC(KF(k, f)), PF(k, f), PA(KF(k, f)))
HYP = '( W e. Word NN0 /\\ ( F e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) )'
QS = lambda k, f: '( %s -> %s )' % (SOME(k, f), CONC(k, f))
PHI_S = '( %s -> A. k e. NN0 %s )' % (HYP, QS('k', 'f'))
STMTS['tmscsome'] = '( ( %s /\\ ( ( G e. NN0 /\\ H e. NN0 ) /\\ %s ) ) -> %s )' % (HYP, SOME('G', 'H'), CONC('G', 'H'))


def cf(w, ph, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            f = l.split('|-', 1)[1].strip()
            assert f.startswith('( %s -> ' % ph), (f[:150], ph[:150])
            return f[len('( %s -> ' % ph):-2]
    raise KeyError(st)


def cong(w, X, var, repl):
    ante = '%s = %s' % (var, repl)
    idst = w.s([], 'id', '( %s -> %s )' % (ante, ante))
    return w.wcongr(X, {var: repl}, ante, {var: idst})


def hypc(w, ph, st):
    """the four facts of HYP from st : ( ph -> HYP )"""
    s = w.s
    ww = s([st], 'simpld', '( %s -> W e. Word NN0 )' % ph)
    r = s([st], 'simprd', '( %s -> ( F e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) )' % ph)
    return ww, s([r, w.inst('simp1')], 'syl', '( %s -> F e. NN0 )' % ph), s([r, w.inst('simp2')], 'syl', '( %s -> Z e. NN0 )' % ph), \
        s([r, w.inst('simp3')], 'syl', '( %s -> O e. NN0 )' % ph)


def base5(w, ph, h4, k, kn):
    """( ph -> ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ k e. NN0 ) )"""
    s = w.s
    ww, fn, zn, on = h4
    a = s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph)
    b = s([a, zn], 'jca', '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % ph)
    c = s([b, on], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % ph)
    return s([c, kn], 'jca', '( %s -> ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ %s e. NN0 ) )' % (ph, k))


def _bs(w, goal):
    s = w.s
    A = '( %s /\\ k e. NN0 )' % HYP
    h4 = hypc(w, A, s([], 'simpl', '( %s -> %s )' % (A, HYP)))
    kn = s([], 'simpr', '( %s -> k e. NN0 )' % A)
    z = s([base5(w, A, h4, 'k', kn), w.inst('scan0')], 'syl', '( %s -> %s = <. ( inr ` (/) ) , 0 >. )' % (A, SC('k', '0')))
    p = projeq(w, A, SC('k', '0'), z, '( inr ` (/) )', '0', s([s([], 'fvex', '( inr ` (/) ) e. _V')], 'a1i', '( %s -> ( inr ` (/) ) e. _V )' % A),
               s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A), 1)
    n = s([s([p], 'necon3ad' if False else 'neneqd', '') if False else None], 'id', '') if False else None
    ns = s([p, s([s([s([], 'eqid', '( inr ` (/) ) = ( inr ` (/) )')], 'a1i', '( %s -> ( inr ` (/) ) = ( inr ` (/) ) )' % A)], 'id', '') if False else None], 'id', '') if False else None
    nsome = s([s([p], 'neeq1d', '( %s -> ( %s <-> ( inr ` (/) ) =/= ( inr ` (/) ) ) )' % (A, SOME('k', '0'))),
               s([s([s([], 'eqid', '( inr ` (/) ) = ( inr ` (/) )')], 'nne', '') if False else s([s([], 'eqid', '( inr ` (/) ) = ( inr ` (/) )'), w.inst('nne')], 'mpbir',
                                                                                              '-. ( inr ` (/) ) =/= ( inr ` (/) )')], 'a1i',
                 '( %s -> -. ( inr ` (/) ) =/= ( inr ` (/) ) )' % A)], 'mtbird', '( %s -> -. %s )' % (A, SOME('k', '0')))
    im = s([nsome], 'pm2.21d', '( %s -> %s )' % (A, QS('k', '0')))
    w.qed([im], 'ralrimiva', goal)


def tmscsomes():
    """the step theorem: ( ( y e. NN0 /\\ PHI[y] ) -> PHI[y+1] )"""
    w = W('tmscsomes', 'Step of the fuel induction for ~ tmscsome .')
    s = w.s
    y1 = '( y + 1 )'
    A = '( y e. NN0 /\\ %s )' % subst(PHI_S, 'f', 'y')
    A2 = '( %s /\\ %s )' % (A, HYP)
    yn = s([], 'simpll', '( %s -> y e. NN0 )' % A2)
    hy = s([], 'simpr', '( %s -> %s )' % (A2, HYP))
    ihv = s([s([], 'simplr', '( %s -> %s )' % (A2, subst(PHI_S, 'f', 'y'))), hy], 'mpd', '( %s -> A. k e. NN0 %s )' % (A2, QS('k', 'y')))
    BN = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (A2, SOME('n', y1))
    L = lambda st: lift(w, BN, A2, st)
    nn = s([], 'simplr', '( %s -> n e. NN0 )' % BN)
    some = s([], 'simpr', '( %s -> %s )' % (BN, SOME('n', y1)))
    h4 = hypc(w, BN, L(hy))
    b5 = base5(w, BN, h4, 'n', nn)
    C1 = '( 1st ` %s ) = 1o' % CP('n')
    C2 = 'O <_ ( # ` ( 1st ` %s ) )' % PA('n')
    PN = '( 1st ` %s )' % PA('n')
    NP_ = '<. n , %s >.' % PN
    SUCC = '<. ( inl ` %s ) , ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) >.' % (NP_, CP('n'), PA('n'))
    C2T = '( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % (SC('( n + 1 )', 'y'), CP('n'), PA('n'))
    C3T = '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (SC('( n + 1 )', 'y'), CP('n'))
    CONT2 = '<. %s , %s >.' % (SCO('( n + 1 )', 'y'), C2T)
    CONT3 = '<. %s , %s >.' % (SCO('( n + 1 )', 'y'), C3T)
    IN = 'if ( %s , %s , %s )' % (C2, SUCC, CONT2)
    sp = s([b5, L(yn), w.inst('scanp1')], 'syl2anc', '( %s -> %s = if ( %s , %s , %s ) )' % (BN, SC('n', y1), C1, IN, CONT3))
    tA, tB = ifproj(w, BN, SC('n', y1), sp, C1, IN, CONT3)
    BT = '( %s /\\ %s )' % (BN, C1)
    tTT, tTF = ifproj(w, BT, SC('n', y1), tA, C2, SUCC, CONT2)
    CO = CONC('n', y1)
    # ---- success
    BTT = '( %s /\\ %s )' % (BT, C2)
    nnt = lift(w, BTT, BN, nn)
    q1 = s([tTT], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (BTT, SCO('n', y1), SUCC))
    sc1 = s([s([s([], 'fvex', '( inl ` %s ) e. _V' % NP_)], 'a1i', '( %s -> ( inl ` %s ) e. _V )' % (BTT, NP_)),
             s([s([], 'ovex', '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) e. _V' % (CP('n'), PA('n')))], 'a1i',
               '( %s -> ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 ) e. _V )' % (BTT, CP('n'), PA('n'))), w.inst('op1stg')], 'syl2anc',
            '( %s -> ( 1st ` %s ) = ( inl ` %s ) )' % (BTT, SUCC, NP_))
    so = s([q1, sc1], 'eqtrd', '( %s -> %s = ( inl ` %s ) )' % (BTT, SCO('n', y1), NP_))
    npv = s([s([], 'opex', '%s e. _V' % NP_)], 'a1i', '( %s -> %s e. _V )' % (BTT, NP_))
    il = s([npv, w.inst('inlval')], 'syl', '( %s -> ( inl ` %s ) = <. (/) , %s >. )' % (BTT, NP_, NP_))
    s2 = s([s([so], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` ( inl ` %s ) ) )' % (BTT, SCO('n', y1), NP_)),
            s([s([il], 'fveq2d', '( %s -> ( 2nd ` ( inl ` %s ) ) = ( 2nd ` <. (/) , %s >. ) )' % (BTT, NP_, NP_)),
               s([s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % BTT), npv, w.inst('op2ndg')], 'syl2anc',
                 '( %s -> ( 2nd ` <. (/) , %s >. ) = %s )' % (BTT, NP_, NP_))], 'eqtrd', '( %s -> ( 2nd ` ( inl ` %s ) ) = %s )' % (BTT, NP_, NP_))],
           'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (BTT, SCO('n', y1), NP_))
    pnv = s([s([], 'fvex', '%s e. _V' % PN)], 'a1i', '( %s -> %s e. _V )' % (BTT, PN))
    kf = s([s([s2], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (BTT, KF('n', y1), NP_)),
            s([nnt, pnv, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = n )' % (BTT, NP_))], 'eqtrd', '( %s -> %s = n )' % (BTT, KF('n', y1)))
    pf = s([s([s2], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (BTT, PF('n', y1), NP_)),
            s([nnt, pnv, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (BTT, NP_, PN))], 'eqtrd', '( %s -> %s = %s )' % (BTT, PF('n', y1), PN))
    clt = Closure(w, BTT, {'n': ('NN0', nnt), 'y': ('NN0', lift(w, BTT, A2, yn))})
    b1 = s([s([nnt], 'nn0red', '( %s -> n e. RR )' % BTT)], 'leidd', '( %s -> n <_ n )' % BTT)
    b2 = linarith(w, BTT, [clt.ge0('y')], 'n < ( n + %s )' % y1, closure=clt)
    sucn = s([s([], 'simplr', '( %s -> %s )' % (BTT, C1)), s([], 'simpr', '( %s -> %s )' % (BTT, C2))], 'jca', '( %s -> %s )' % (BTT, SUC('n')))
    CONn = '( ( n <_ n /\\ n < ( n + %s ) ) /\\ ( %s /\\ %s = ( 1st ` %s ) ) )' % (y1, SUC('n'), PN, PA('n'))
    stn = s([s([b1, b2], 'jca', '( %s -> ( n <_ n /\\ n < ( n + %s ) ) )' % (BTT, y1)),
             s([sucn, s([s([], 'eqid', '%s = %s' % (PN, PN))], 'a1i', '( %s -> %s = %s )' % (BTT, PN, PN))], 'jca',
               '( %s -> ( %s /\\ %s = ( 1st ` %s ) ) )' % (BTT, SUC('n'), PN, PA('n')))], 'jca', '( %s -> %s )' % (BTT, CONn))
    rr = w.wcongr(CO, {}, BTT, {}, rules={KF('n', y1): ('n', kf), PF('n', y1): (PN, pf)})
    assert rr[1] == CONn, (rr[1], CONn)
    kTT = s([rr[0], stn], 'mpbird', '( %s -> %s )' % (BTT, CO))

    # ---- continuing: SCO( n , y + 1 ) = SCO( n + 1 , y )
    def cont(Bx, tx, CONT, CT):
        Lx = lambda st: lift(w, Bx, BN, st)
        q = s([tx], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (Bx, SCO('n', y1), CONT))
        cc = s([s([s([], 'fvex', '%s e. _V' % SCO('( n + 1 )', 'y'))], 'a1i', '( %s -> %s e. _V )' % (Bx, SCO('( n + 1 )', 'y'))),
                s([s([], 'ovex', '%s e. _V' % CT)], 'a1i', '( %s -> %s e. _V )' % (Bx, CT)), w.inst('op1stg')], 'syl2anc',
               '( %s -> ( 1st ` %s ) = %s )' % (Bx, CONT, SCO('( n + 1 )', 'y')))
        eq = s([q, cc], 'eqtrd', '( %s -> %s = %s )' % (Bx, SCO('n', y1), SCO('( n + 1 )', 'y')))
        so2 = s([s([eq], 'neeq1d', '( %s -> ( %s <-> %s ) )' % (Bx, SOME('n', y1), SOME('( n + 1 )', 'y'))), Lx(some)], 'mpbid',
                '( %s -> %s )' % (Bx, SOME('( n + 1 )', 'y')))
        n1 = s([Lx(nn), w.inst('peano2nn0')], 'syl', '( %s -> ( n + 1 ) e. NN0 )' % Bx)
        cg, xm = cong(w, QS('k', 'y'), 'k', '( n + 1 )')
        rsp = s([cg], 'rspcv', '( ( n + 1 ) e. NN0 -> ( A. k e. NN0 %s -> %s ) )' % (QS('k', 'y'), xm))
        ih1 = s([s([n1, lift(w, Bx, A2, ihv), rsp], 'sylc', '( %s -> %s )' % (Bx, xm)), so2], 'mpd', '( %s -> %s )' % (Bx, CONC('( n + 1 )', 'y')))
        K1 = KF('( n + 1 )', 'y')
        a = s([ih1], 'simpld', '( %s -> ( ( n + 1 ) <_ %s /\\ %s < ( ( n + 1 ) + y ) ) )' % (Bx, K1, K1))
        rest = s([ih1], 'simprd', '( %s -> ( %s /\\ %s = ( 1st ` %s ) ) )' % (Bx, SUC(K1), PF('( n + 1 )', 'y'), PA(K1)))
        b5n = base5(w, Bx, hypc(w, Bx, lift(w, Bx, A2, hy)), '( n + 1 )', n1)
        dj = s([s([b5n, s([n1, lift(w, Bx, A2, yn)], 'jca', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
        # K1 e. NN0 via scandj at ( n + 1 , y )
        h4x = hypc(w, Bx, lift(w, Bx, A2, hy))
        ww, fn, zn, on = h4x
        pre = s([s([s([s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % Bx), zn], 'jca', '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % Bx),
                    on], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % Bx),
                 s([n1, lift(w, Bx, A2, yn)], 'jca', '( %s -> ( ( n + 1 ) e. NN0 /\\ y e. NN0 ) )' % Bx)], 'jca',
                '( %s -> ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( ( n + 1 ) e. NN0 /\\ y e. NN0 ) ) )' % Bx)
        djs = s([s([pre, so2], 'jca', '( %s -> ( ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( ( n + 1 ) e. NN0 /\\ y e. NN0 ) ) /\\ %s ) )'
                   % (Bx, SOME('( n + 1 )', 'y'))), w.inst('scandj')], 'syl', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (Bx, K1, PF('( n + 1 )', 'y')))
        k1n = s([djs], 'simpld', '( %s -> %s e. NN0 )' % (Bx, K1))
        clx = Closure(w, Bx, {'n': ('NN0', Lx(nn)), 'y': ('NN0', lift(w, Bx, A2, yn))})
        clx.leaf(K1, 'NN0', k1n)
        l1 = linarith(w, Bx, [s([a], 'simpld', '( %s -> ( n + 1 ) <_ %s )' % (Bx, K1))], 'n <_ %s' % K1, closure=clx)
        l2 = linarith(w, Bx, [s([a], 'simprd', '( %s -> %s < ( ( n + 1 ) + y ) )' % (Bx, K1))], '%s < ( n + %s )' % (K1, y1), closure=clx)
        CON1 = '( ( n <_ %s /\\ %s < ( n + %s ) ) /\\ ( %s /\\ %s = ( 1st ` %s ) ) )' % (K1, K1, y1, SUC(K1), PF('( n + 1 )', 'y'), PA(K1))
        st1 = s([s([l1, l2], 'jca', '( %s -> ( n <_ %s /\\ %s < ( n + %s ) ) )' % (Bx, K1, K1, y1)), rest], 'jca', '( %s -> %s )' % (Bx, CON1))
        r2 = w.wcongr(CO, {}, Bx, {}, rules={SCO('n', y1): (SCO('( n + 1 )', 'y'), eq)})
        assert r2[1] == CON1, (r2[1], CON1)
        return s([r2[0], st1], 'mpbird', '( %s -> %s )' % (Bx, CO))
    BTF = '( %s /\\ -. %s )' % (BT, C2)
    kTF = cont(BTF, tTF, CONT2, C2T)
    BF = '( %s /\\ -. %s )' % (BN, C1)
    kF = cont(BF, tB, CONT3, C3T)
    kT = s([kTT, kTF], 'pm2.61dan', '( %s -> %s )' % (BT, CO))
    kk = s([kT, kF], 'pm2.61dan', '( %s -> %s )' % (BN, CO))
    q = s([s([kk], 'ex', '( ( %s /\\ n e. NN0 ) -> %s )' % (A2, QS('n', y1)))], 'ralrimiva', '( %s -> A. n e. NN0 %s )' % (A2, QS('n', y1)))
    cg2, xk = cong(w, QS('n', y1), 'n', 'k')
    cb = s([cg2], 'cbvralvw', '( A. n e. NN0 %s <-> A. k e. NN0 %s )' % (QS('n', y1), xk))
    w.qed([s([q, cb], 'sylib', '( %s -> A. k e. NN0 %s )' % (A2, xk))], 'ex', '( %s -> %s )' % (A, subst(PHI_S, 'f', y1)))
    return run(w)


def tmscsomeb():
    w = W('tmscsomeb', 'Base of the fuel induction for ~ tmscsome .')
    _bs(w, subst(PHI_S, 'f', '0'))
    return run(w)


def tmscsome():
    w = W('tmscsome', 'A successful scan (Lean ` scan ` returning ` some ( k\' , P ) ` ) stops at a success: ` k <_ k\' < k + fuel ` , '
                      '` k\' ` is coprime to ` Q ` with a pool of at least ` theta ` primes, and the returned pool is that pool.')
    s = w.s
    st, phit = fuelind(w, PHI_S, 'H', 'tmscsomeb', 'tmscsomes')
    T = '( %s /\\ ( ( G e. NN0 /\\ H e. NN0 ) /\\ %s ) )' % (HYP, SOME('G', 'H'))
    hn = s([], 'simprlr' if False else 'simprl', '( %s -> ( G e. NN0 /\\ H e. NN0 ) )' % T)
    a = s([s([s([hn], 'simprd', '( %s -> H e. NN0 )' % T), s([st], 'a1i', '( %s -> ( H e. NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           s([], 'simpl', '( %s -> %s )' % (T, HYP))], 'mpd', '( %s -> A. k e. NN0 %s )' % (T, QS('k', 'H')))
    cg, xg = cong(w, QS('k', 'H'), 'k', 'G')
    r = s([cg], 'rspcv', '( G e. NN0 -> ( A. k e. NN0 %s -> %s ) )' % (QS('k', 'H'), xg))
    im = s([s([hn], 'simpld', '( %s -> G e. NN0 )' % T), a, r], 'sylc', '( %s -> %s )' % (T, xg))
    w.qed([s([], 'simprr', '( %s -> %s )' % (T, SOME('G', 'H'))), im], 'mpd', STMTS['tmscsome'])
    return run(w)


def lift(w, ph2, ph, st):
    X = cf(w, ph, st)
    chain = []
    t = ph2
    while t != ph:
        inner = t[2:-2]
        toks = inner.split(' ')
        d = 0
        cut = None
        for j, tk in enumerate(toks):
            if tk in ('(', '<.', '{', '<"'):
                d += 1
            elif tk in (')', '>.', '}', '">'):
                d -= 1
            elif d == 0 and tk == '/\\':
                cut = j
        assert cut is not None, t[:200]
        chain.append(t)
        t = ' '.join(toks[:cut])
    cur = st
    for t2 in reversed(chain):
        cur = w.s([cur], 'adantr', '( %s -> %s )' % (t2, X))
    return cur


NONE_ = lambda k, f: '%s = ( inr ` (/) )' % SCO(k, f)
HGH = '( %s /\\ ( G e. NN0 /\\ H e. NN0 ) )' % HYP
STMTS['tmscmin'] = '( ( %s /\\ ( %s /\\ ( J e. NN0 /\\ G <_ J /\\ J < %s ) ) ) -> -. %s )' % (HGH, SOME('G', 'H'), KF('G', 'H'), SUC('J'))
STMTS['tmscnone'] = '( ( %s /\\ ( %s /\\ ( J e. NN0 /\\ G <_ J /\\ J < ( G + H ) ) ) ) -> -. %s )' % (HGH, NONE_('G', 'H'), SUC('J'))


def go_inst(w, ph, h4, gn, hn, jn, suc, gle, jlt):
    """scango at K := G , F := H , X := F : the conclusion step"""
    s = w.s
    ww, fn, zn, on = h4
    a1 = s([ww, fn, zn], '3jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 /\\ Z e. NN0 ) )' % ph)
    a2 = s([on, jn], 'jca', '( %s -> ( O e. NN0 /\\ J e. NN0 ) )' % ph)
    A1 = s([a1, a2, suc], '3jca', '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 /\\ Z e. NN0 ) /\\ ( O e. NN0 /\\ J e. NN0 ) /\\ %s ) )' % (ph, SUC('J')))
    A2 = s([hn, gn], 'jca', '( %s -> ( H e. NN0 /\\ G e. NN0 ) )' % ph)
    A3 = s([gle, jlt], 'jca', '( %s -> ( G <_ J /\\ J < ( G + H ) ) )' % ph)
    ante, concl = split_imp_(stmt_('scango'))
    m = {'X': 'F', 'F': 'H', 'K': 'G'}
    c2 = ' '.join(m.get(x, x) for x in concl.split())
    full = s([A1, A2, A3], '3jca', '( %s -> %s )' % (ph, ' '.join(m.get(x, x) for x in ante.split())))
    return s([full, w.inst('scango')], 'syl', '( %s -> %s )' % (ph, c2)), c2


def split_imp_(text):
    from t6blib import split_imp
    return split_imp(text)


def stmt_(l):
    from t6blib import stmt
    return stmt(l)


def tmscmin():
    w = W('tmscmin', 'No success below the one a scan returns (Lean: the recursion of ` scan ` stops at the first success; ~ scango ).')
    s = w.s
    ph = '( ( %s /\\ ( %s /\\ ( J e. NN0 /\\ G <_ J /\\ J < %s ) ) ) /\\ %s )' % (HGH, SOME('G', 'H'), KF('G', 'H'), SUC('J'))
    c = Ctx(w, ph, (((HYP, ('G e. NN0', 'H e. NN0')), (SOME('G', 'H'), ('J e. NN0', 'G <_ J', 'J < %s' % KF('G', 'H')))), SUC('J')))
    h4 = hypc(w, ph, c[HYP])
    gn, hn, jn = c['G e. NN0'], c['H e. NN0'], c['J e. NN0']
    so = s([s([c[HYP], s([gn, hn], 'jca', '( %s -> ( G e. NN0 /\\ H e. NN0 ) )' % ph), c[SOME('G', 'H')]], 'jca', '') if False else None], 'id', '') if False else None
    sm = s([s([c[HYP], s([s([gn, hn], 'jca', '( %s -> ( G e. NN0 /\\ H e. NN0 ) )' % ph), c[SOME('G', 'H')]], 'jca',
                         '( %s -> ( ( G e. NN0 /\\ H e. NN0 ) /\\ %s ) )' % (ph, SOME('G', 'H')))], 'jca',
              '( %s -> ( %s /\\ ( ( G e. NN0 /\\ H e. NN0 ) /\\ %s ) ) )' % (ph, HYP, SOME('G', 'H'))), w.inst('tmscsome')], 'syl', '( %s -> %s )' % (ph, CONC('G', 'H')))
    kb = s([sm], 'simpld', '( %s -> ( G <_ %s /\\ %s < ( G + H ) ) )' % (ph, KF('G', 'H'), KF('G', 'H')))
    K_ = KF('G', 'H')
    dj = s([s([s([s([s([s([h4[0], h4[1]], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph), h4[2]], 'jca',
                        '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % ph), h4[3]], 'jca',
                     '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % ph),
                  s([gn, hn], 'jca', '( %s -> ( G e. NN0 /\\ H e. NN0 ) )' % ph)], 'jca',
                 '( %s -> ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( G e. NN0 /\\ H e. NN0 ) ) )' % ph), c[SOME('G', 'H')]], 'jca',
               '( %s -> ( ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( G e. NN0 /\\ H e. NN0 ) ) /\\ %s ) )' % (ph, SOME('G', 'H'))),
            w.inst('scandj')], 'syl', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (ph, K_, PF('G', 'H')))
    cl = Closure(w, ph, {'J': ('NN0', jn), 'G': ('NN0', gn), 'H': ('NN0', hn)})
    cl.leaf(K_, 'NN0', s([dj], 'simpld', '( %s -> %s e. NN0 )' % (ph, K_)))
    jlt = linarith(w, ph, [c['J < %s' % K_], s([kb], 'simprd', '( %s -> %s < ( G + H ) )' % (ph, K_))], 'J < ( G + H )', closure=cl)
    go, c2 = go_inst(w, ph, h4, gn, hn, jn, c[SUC('J')], c['G <_ J'], jlt)
    kj = s([s([s([go], 'simpld', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
    g1 = s([go], 'simpld', '( %s -> %s )' % (ph, c2[2:].split(' ) /\\ ( ( ( 1st')[0] + ' )' if False else '')) if False else None
    # the first conjunct: ( SOME /\ ( G <_ KF /\ KF <_ J ) )
    first = '( %s /\\ ( G <_ %s /\\ %s <_ J ) )' % (SOME('G', 'H'), K_, K_)
    f1 = s([go], 'simpld', '( %s -> %s )' % (ph, first))
    kle = s([s([f1], 'simprd', '( %s -> ( G <_ %s /\\ %s <_ J ) )' % (ph, K_, K_))], 'simprd', '( %s -> %s <_ J )' % (ph, K_))
    ff = linarith(w, ph, [kle, c['J < %s' % K_]], 'J < J', closure=cl) if False else None
    nl = s([s([cl.mem(K_, 'RR'), cl.mem('J', 'RR')], 'lenltd', '( %s -> ( %s <_ J <-> -. J < %s ) )' % (ph, K_, K_)), kle], 'mpbid', '( %s -> -. J < %s )' % (ph, K_))
    ph0 = '( %s /\\ ( %s /\\ ( J e. NN0 /\\ G <_ J /\\ J < %s ) ) )' % (HGH, SOME('G', 'H'), K_)
    w.qed([s([s([s([], 'simplrr', '') if False else None], 'id', '') if False else None], 'id', '') if False else
           s([s([c['J < %s' % K_], nl], 'pm2.65da' if False else 'pm2.21dd', '( %s -> F. )' % ph)], 'inegd', '( %s -> -. %s )' % (ph0, SUC('J')))], 'id', STMTS['tmscmin']) if False else \
        w.qed([s([c['J < %s' % K_], nl], 'pm2.21dd', '( %s -> F. )' % ph)], 'inegd', STMTS['tmscmin'])
    return run(w)


def tmscnone():
    w = W('tmscnone', 'A failed scan has no success in its range (Lean: ` scan ` returns ` none ` only when every ` k ` fails; ~ scango ).')
    s = w.s
    ph = '( ( %s /\\ ( %s /\\ ( J e. NN0 /\\ G <_ J /\\ J < ( G + H ) ) ) ) /\\ %s )' % (HGH, NONE_('G', 'H'), SUC('J'))
    c = Ctx(w, ph, (((HYP, ('G e. NN0', 'H e. NN0')), (NONE_('G', 'H'), ('J e. NN0', 'G <_ J', 'J < ( G + H )'))), SUC('J')))
    h4 = hypc(w, ph, c[HYP])
    gn, hn, jn = c['G e. NN0'], c['H e. NN0'], c['J e. NN0']
    go, c2 = go_inst(w, ph, h4, gn, hn, jn, c[SUC('J')], c['G <_ J'], c['J < ( G + H )'])
    first = '( %s /\\ ( G <_ %s /\\ %s <_ J ) )' % (SOME('G', 'H'), KF('G', 'H'), KF('G', 'H'))
    so = s([s([go], 'simpld', '( %s -> %s )' % (ph, first))], 'simpld', '( %s -> %s )' % (ph, SOME('G', 'H')))
    w.qed([s([c[NONE_('G', 'H')], so], 'pm2.21dd' if False else 'eqnetrd' if False else 'nsyl3' if False else 'pm2.21dd', '') if False else
           s([so, s([c[NONE_('G', 'H')]], 'id', '') if False else None], 'id', '') if False else None], 'id', '') if False else None
    nn_ = s([so], 'neneqd', '( %s -> -. %s )' % (ph, NONE_('G', 'H')))
    w.qed([s([c[NONE_('G', 'H')], nn_], 'pm2.21dd', '( %s -> F. )' % ph)], 'inegd', STMTS['tmscnone'])
    return run(w)


if __name__ == '__main__':
    for l in only:
        globals()[l]()
