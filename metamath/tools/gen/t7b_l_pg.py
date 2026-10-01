"""T7b: the iteration count of Lean's ` primeGo ` loop (PrimTD.lean ` primeIters ` ,
which equals the charged cost ` ( primeGo m d fuel ).2 ` , ` primeIters_eq ` ): the facts the
machine's loop invariant ` PGInv ` needs, on A1b's ` PrimeGo ` .

  tmipgp1   one unit of fuel costs at least one iteration
  tmipgleb, tmipgles, tmipgle   Lean ` primeIters_le_fuel `
  tmipg0    no iteration iff no fuel, and the result is true then
  tmipgshb, tmipgshs, tmipgsh   Lean ` primeGo_shift `
  tmipgit   the three exits of iteration ` i ` (Lean ` primeIters_succ_lt/_dvd/_next ` shifted)

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_l_pg.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith, lineq
from a4alib import fuelind, ifproj, projeq, paircl, zne1o

SEL = sys.argv[1:]


def PG(d, f):
    return '( ( M PrimeGo %s ) ` %s )' % (d, f)


def C2(d, f):
    return '( 2nd ` %s )' % PG(d, f)


def C1(d, f):
    return '( 1st ` %s )' % PG(d, f)


def IFV(d, f):
    """primegop1's value at ( d , f + 1 )"""
    return ('if ( M < ( %s x. %s ) , <. 1o , 1 >. , if ( ( M mod %s ) = 0 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) )'
            % (d, d, d, C1('( %s + 1 )' % d, f), C2('( %s + 1 )' % d, f)))


ST_P1 = '( ( ( M e. NN0 /\\ D e. NN0 ) /\\ F e. NN0 ) -> 1 <_ %s )' % C2('D', '( F + 1 )')
PHLE = lambda f: '( M e. NN0 -> A. d e. NN0 %s <_ %s )' % (C2('d', f), f)
ST_LE = '( ( M e. NN0 /\\ D e. NN0 /\\ F e. NN0 ) -> %s <_ F )' % C2('D', 'F')
ST_0 = '( ( M e. NN0 /\\ D e. NN0 /\\ F e. NN0 ) -> ( ( %s = 0 <-> F = 0 ) /\\ ( F = 0 -> %s = 1o ) ) )' % (C2('D', 'F'), C1('D', 'F'))
H3 = '( M e. NN0 /\\ D e. NN0 /\\ F e. NN0 )'
RR_ = C2('D', 'F')
def PHSH(i):
    return ('( %s -> ( %s < %s -> ( %s = %s /\\ %s = ( %s + %s ) ) ) )'
            % (H3, i, RR_, C1('D', 'F'), C1('( D + %s )' % i, '( F - %s )' % i), RR_, C2('( D + %s )' % i, '( F - %s )' % i), i))
ST_SH = '( ( %s /\\ ( I e. NN0 /\\ I < %s ) ) -> ( %s = %s /\\ %s = ( %s + I ) ) )' % (
    H3, RR_, C1('D', 'F'), C1('( D + I )', '( F - I )'), RR_, C2('( D + I )', '( F - I )'))
DI = '( D + I )'
DD = '( %s x. %s )' % (DI, DI)
I1 = '( I + 1 )'
FI1 = '( F - %s )' % I1
ST_IT = ('( ( %s /\\ ( I e. NN0 /\\ I < %s ) ) -> ( ( M < %s -> ( %s = %s /\\ %s = 1o ) ) /\\ '
         '( ( -. M < %s /\\ ( M mod %s ) = 0 ) -> ( %s = %s /\\ %s = (/) ) ) /\\ '
         '( ( -. M < %s /\\ -. ( M mod %s ) = 0 ) -> ( ( %s < %s <-> -. %s = 0 ) /\\ ( %s = 0 -> ( %s = %s /\\ %s = 1o ) ) ) ) ) )'
         % (H3, RR_, DD, RR_, I1, C1('D', 'F'), DD, DI, RR_, I1, C1('D', 'F'), DD, DI, I1, RR_, FI1, FI1, RR_, I1, C1('D', 'F')))
STMTS = {'tmipgp1': ST_P1, 'tmipgle': ST_LE, 'tmipg0': ST_0, 'tmipgsh': ST_SH, 'tmipgit': ST_IT}


def vex(w, a, e, lab):
    return w.s([w.s([], lab, '%s e. _V' % e)], 'a1i', '( %s -> %s e. _V )' % (a, e))


def cases(w, ph, d, f, dn, mn, fn):
    """primegop1 at ( d , f + 1 ): returns the value step and the case contexts T1 ( M < d d ),
    T2 ( -. , mod = 0 ), T3 ( -. , -. ) with the value steps vt1, vt2, vf2"""
    val = PG(d, '( %s + 1 )' % f)
    pgp1 = w.s([w.s([mn, dn], 'jca', '( %s -> ( M e. NN0 /\\ %s e. NN0 ) )' % (ph, d)), fn, w.inst('primegop1')], 'syl2anc',
               '( %s -> %s = %s )' % (ph, val, IFV(d, f)))
    Cc1 = 'M < ( %s x. %s )' % (d, d)
    Cc2 = '( M mod %s ) = 0' % d
    PGN = '<. %s , ( %s + 1 ) >.' % (C1('( %s + 1 )' % d, f), C2('( %s + 1 )' % d, f))
    IF2 = 'if ( %s , <. (/) , 1 >. , %s )' % (Cc2, PGN)
    vt1, vf1 = ifproj(w, ph, val, pgp1, Cc1, '<. 1o , 1 >.', IF2)
    NF = '( %s /\\ -. %s )' % (ph, Cc1)
    vt2, vf2 = ifproj(w, NF, val, vf1, Cc2, '<. (/) , 1 >.', PGN)
    return dict(val=val, C1=Cc1, C2=Cc2, T1='( %s /\\ %s )' % (ph, Cc1), NF=NF, T2='( %s /\\ %s )' % (NF, Cc2),
                T3='( %s /\\ -. %s )' % (NF, Cc2), vt1=vt1, vt2=vt2, vf2=vf2, PGN=PGN)


def tmipgp1():
    ph = split_imp(ST_P1)[0]
    w = W('tmipgp1', 'One unit of fuel costs at least one iteration of ` primeGo ` (Lean ` primeIters_pos ` ).')
    mn = w.s([], 'simpll', '( %s -> M e. NN0 )' % ph)
    dn = w.s([], 'simplr', '( %s -> D e. NN0 )' % ph)
    fn = w.s([], 'simpr', '( %s -> F e. NN0 )' % ph)
    k = cases(w, ph, 'D', 'F', dn, mn, fn)
    one = lambda a: w.s([w.s([], '1le1' if False else '1re', '1 e. RR')], 'leidi' if False else 'a1i', '') if False else \
        w.s([w.s([w.s([], '1re', '1 e. RR')], 'leidi', '1 <_ 1')], 'a1i', '( %s -> 1 <_ 1 )' % a)
    p1 = projeq(w, k['T1'], k['val'], k['vt1'], '1o', '1', vex(w, k['T1'], '1o', '1oex'), vex(w, k['T1'], '1', '1ex'), 2)
    c1 = w.s([p1, one(k['T1'])], 'eqbrtrd' if False else 'eqbrtrrd' if False else 'breqtrrd', '( %s -> 1 <_ %s )' % (k['T1'], C2('D', '( F + 1 )')))
    p2 = projeq(w, k['T2'], k['val'], k['vt2'], '(/)', '1', vex(w, k['T2'], '(/)', '0ex'), vex(w, k['T2'], '1', '1ex'), 2)
    c2 = w.s([p2, one(k['T2'])], 'breqtrrd', '( %s -> 1 <_ %s )' % (k['T2'], C2('D', '( F + 1 )')))
    T3 = k['T3']
    L3 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (T3, f))
    d1 = w.s([L3(dn, 'D e. NN0'), w.inst('peano2nn0')], 'syl', '( %s -> ( D + 1 ) e. NN0 )' % T3)
    cl3 = w.s([w.s([L3(mn, 'M e. NN0'), d1], 'jca', '( %s -> ( M e. NN0 /\\ ( D + 1 ) e. NN0 ) )' % T3), L3(fn, 'F e. NN0'), w.inst('primegocl')],
              'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (T3, PG('( D + 1 )', 'F')))
    q1, q2 = paircl(w, T3, PG('( D + 1 )', 'F'), cl3, '2o', 'NN0')
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (T3, C2('( D + 1 )', 'F')))
    p3 = projeq(w, T3, k['val'], k['vf2'], C1('( D + 1 )', 'F'), '( %s + 1 )' % C2('( D + 1 )', 'F'), q1, q2p, 2)
    c = Closure(w, T3, {C2('( D + 1 )', 'F'): ('NN0', q2)})
    c.atom(C2('( D + 1 )', 'F'))
    l3 = linarith(w, T3, [c.ge0(C2('( D + 1 )', 'F'))], '1 <_ ( %s + 1 )' % C2('( D + 1 )', 'F'), closure=c)
    c3 = w.s([p3, l3], 'breqtrrd', '( %s -> 1 <_ %s )' % (T3, C2('D', '( F + 1 )')))
    cnf = w.s([c2, c3], 'pm2.61dan', '( %s -> 1 <_ %s )' % (k['NF'], C2('D', '( F + 1 )')))
    w.qed([c1, cnf], 'pm2.61dan', ST_P1)
    return w.run()



def pgcl(w, ph, d, f, mn, dn, fn):
    """( ph -> PG( d , f ) e. ( 2o X. NN0 ) ), and its projections"""
    cl = w.s([w.s([mn, dn], 'jca', '( %s -> ( M e. NN0 /\\ %s e. NN0 ) )' % (ph, d)), fn, w.inst('primegocl')], 'syl2anc',
             '( %s -> %s e. ( 2o X. NN0 ) )' % (ph, PG(d, f)))
    return paircl(w, ph, PG(d, f), cl, '2o', 'NN0')


def tmipgleb():
    w = W('tmipgleb', 'Base of the induction for Lean ` primeIters_le_fuel ` : no fuel, no iteration.')
    A = '( M e. NN0 /\\ d e. NN0 )'
    mn = w.s([], 'simpl', '( %s -> M e. NN0 )' % A)
    dn = w.s([], 'simpr', '( %s -> d e. NN0 )' % A)
    pg0 = w.s([mn, dn, w.inst('primego0')], 'syl2anc', '( %s -> %s = <. 1o , 0 >. )' % (A, PG('d', '0')))
    p2 = projeq(w, A, PG('d', '0'), pg0, '1o', '0', vex(w, A, '1o', '1oex'), vex(w, A, '0', 'c0ex'), 2)
    z = w.s([w.s([w.s([], '0re', '0 e. RR')], 'leidi', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % A)
    b = w.s([p2, z], 'eqbrtrd', '( %s -> %s <_ 0 )' % (A, C2('d', '0')))
    w.qed([b], 'ralrimiva', PHLE('0'))
    return w.run()


def tmipgles():
    w = W('tmipgles', 'Step of the induction for Lean ` primeIters_le_fuel ` : one more unit of fuel, at most one more '
                      'iteration.')
    IHD = 'A. d e. NN0 %s <_ N' % C2('d', 'N')
    IHC = 'A. c e. NN0 %s <_ N' % C2('c', 'N')
    A = '( N e. NN0 /\\ ( M e. NN0 -> %s ) )' % IHD
    AC = '( N e. NN0 /\\ ( M e. NN0 -> %s ) )' % IHC
    idc = w.s([], 'id', '( d = c -> d = c )')
    cg, new = w.wcongr('%s <_ N' % C2('d', 'N'), {'d': 'c'}, 'd = c', {'d': idc})
    cbv = w.s([cg], 'cbvralvw', '( %s <-> %s )' % (IHD, IHC))
    conv = w.s([w.s([], 'simpl', '( %s -> N e. NN0 )' % A),
                w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 -> %s ) )' % (A, IHD)),
                     w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd', '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))],
                    'syld', '( %s -> ( M e. NN0 -> %s ) )' % (A, IHC))], 'jca', '( %s -> %s )' % (A, AC))
    B1 = '( %s /\\ M e. NN0 )' % AC
    B = '( %s /\\ d e. NN0 )' % B1
    nn = w.s([], 'simpll', '( %s -> N e. NN0 )' % B) if False else w.s([w.s([], 'simpl', '( %s -> %s )' % (B, B1))], 'simpld', '( %s -> %s )' % (B, AC))
    nn = w.s([nn], 'simpld', '( %s -> N e. NN0 )' % B)
    mn = w.s([], 'simplr', '( %s -> M e. NN0 )' % B)
    dn = w.s([], 'simpr', '( %s -> d e. NN0 )' % B)
    ihc = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (B, B1))], 'simpld', '( %s -> %s )' % (B, AC))], 'simprd',
                   '( %s -> ( M e. NN0 -> %s ) )' % (B, IHC)), mn], 'mpd', '( %s -> %s )' % (B, IHC))
    d1n = w.s([dn, w.inst('peano2nn0')], 'syl', '( %s -> ( d + 1 ) e. NN0 )' % B)
    idd = w.s([], 'id', '( c = ( d + 1 ) -> c = ( d + 1 ) )')
    cg2, new2 = w.wcongr('%s <_ N' % C2('c', 'N'), {'c': '( d + 1 )'}, 'c = ( d + 1 )', {'c': idd})
    ih1 = w.s([cg2, ihc, d1n], 'rspcdva', '( %s -> %s <_ N )' % (B, C2('( d + 1 )', 'N')))
    k = cases(w, B, 'd', 'N', dn, mn, nn)
    N1 = '( N + 1 )'
    cl = Closure(w, B, {'N': ('NN0', nn)})
    def le1(T):
        cT = Closure(w, T, {'N': ('NN0', w.s([nn], 'adantr', '( %s -> N e. NN0 )' % T) if T.count('/\\') == B.count('/\\') + 1 else
                                   w.s([nn], 'ad2antrr', '( %s -> N e. NN0 )' % T))})
        return linarith(w, T, [cT.ge0('N')], '1 <_ %s' % N1, closure=cT)
    p1 = projeq(w, k['T1'], k['val'], k['vt1'], '1o', '1', vex(w, k['T1'], '1o', '1oex'), vex(w, k['T1'], '1', '1ex'), 2)
    c1 = w.s([p1, le1(k['T1'])], 'eqbrtrd', '( %s -> %s <_ %s )' % (k['T1'], C2('d', N1), N1))
    p2 = projeq(w, k['T2'], k['val'], k['vt2'], '(/)', '1', vex(w, k['T2'], '(/)', '0ex'), vex(w, k['T2'], '1', '1ex'), 2)
    c2 = w.s([p2, le1(k['T2'])], 'eqbrtrd', '( %s -> %s <_ %s )' % (k['T2'], C2('d', N1), N1))
    T3 = k['T3']
    L3 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (T3, f))
    q1, q2 = pgcl(w, T3, '( d + 1 )', 'N', L3(mn, 'M e. NN0'), L3(d1n, '( d + 1 ) e. NN0'), L3(nn, 'N e. NN0'))
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (T3, C2('( d + 1 )', 'N')))
    p3 = projeq(w, T3, k['val'], k['vf2'], C1('( d + 1 )', 'N'), '( %s + 1 )' % C2('( d + 1 )', 'N'), q1, q2p, 2)
    c3c = Closure(w, T3, {'N': ('NN0', L3(nn, 'N e. NN0')), C2('( d + 1 )', 'N'): ('NN0', q2)})
    c3c.atom(C2('( d + 1 )', 'N'))
    l3 = linarith(w, T3, [L3(ih1, '%s <_ N' % C2('( d + 1 )', 'N'))], '( %s + 1 ) <_ %s' % (C2('( d + 1 )', 'N'), N1), closure=c3c)
    c3 = w.s([p3, l3], 'eqbrtrd', '( %s -> %s <_ %s )' % (T3, C2('d', N1), N1))
    cnf = w.s([c2, c3], 'pm2.61dan', '( %s -> %s <_ %s )' % (k['NF'], C2('d', N1), N1))
    main = w.s([c1, cnf], 'pm2.61dan', '( %s -> %s <_ %s )' % (B, C2('d', N1), N1))
    r = w.s([main], 'ralrimiva', '( %s -> A. d e. NN0 %s <_ %s )' % (B1, C2('d', N1), N1))
    e = w.s([r], 'ex', '( %s -> %s )' % (AC, PHLE(N1)))
    w.qed([conv, e], 'syl', '( %s -> %s )' % (A, PHLE(N1)))
    return w.run()


def tmipgle():
    w = W('tmipgle', 'Lean ` primeIters_le_fuel ` : the ` primeGo ` loop runs at most ` fuel ` times.')
    ph = split_imp(ST_LE)[0]
    st, pt = fuelind(w, PHLE('f'), 'F', 'tmipgleb', 'tmipgles', fvar='f')
    mn = w.s([], 'simp1', '( %s -> M e. NN0 )' % ph)
    dn = w.s([], 'simp2', '( %s -> D e. NN0 )' % ph)
    fn = w.s([], 'simp3', '( %s -> F e. NN0 )' % ph)
    ral = w.s([w.s([fn, st], 'syl', '( %s -> %s )' % (ph, pt)), mn], 'mpd', '( %s -> A. d e. NN0 %s <_ F )' % (ph, C2('d', 'F')))
    idd = w.s([], 'id', '( d = D -> d = D )')
    cg, new = w.wcongr('%s <_ F' % C2('d', 'F'), {'d': 'D'}, 'd = D', {'d': idd})
    w.qed([cg, ral, dn], 'rspcdva', ST_LE)
    return w.run()


def tmipg0():
    ph = split_imp(ST_0)[0]
    w = W('tmipg0', 'The ` primeGo ` loop runs not at all exactly when there is no fuel, and then answers true '
                    '(Lean ` primeIters_zero ` , ` primeIters_pos ` , ` primeGo_zero ` ).')
    mn = w.s([], 'simp1', '( %s -> M e. NN0 )' % ph)
    dn = w.s([], 'simp2', '( %s -> D e. NN0 )' % ph)
    fn = w.s([], 'simp3', '( %s -> F e. NN0 )' % ph)
    # F = 0
    p0 = '( %s /\\ F = 0 )' % ph
    f0 = w.s([], 'simpr', '( %s -> F = 0 )' % p0)
    pe = w.s([f0], 'fveq2d', '( %s -> %s = %s )' % (p0, PG('D', 'F'), PG('D', '0')))
    pg0 = w.s([w.s([mn], 'adantr', '( %s -> M e. NN0 )' % p0), w.s([dn], 'adantr', '( %s -> D e. NN0 )' % p0), w.inst('primego0')], 'syl2anc',
              '( %s -> %s = <. 1o , 0 >. )' % (p0, PG('D', '0')))
    pv = w.s([pe, pg0], 'eqtrd', '( %s -> %s = <. 1o , 0 >. )' % (p0, PG('D', 'F')))
    r0 = projeq(w, p0, PG('D', 'F'), pv, '1o', '0', vex(w, p0, '1o', '1oex'), vex(w, p0, '0', 'c0ex'), 2)
    t0 = projeq(w, p0, PG('D', 'F'), pv, '1o', '0', vex(w, p0, '1o', '1oex'), vex(w, p0, '0', 'c0ex'), 1)
    a1 = w.s([r0], 'ex', '( %s -> ( F = 0 -> %s = 0 ) )' % (ph, C2('D', 'F')))
    a2 = w.s([t0], 'ex', '( %s -> ( F = 0 -> %s = 1o ) )' % (ph, C1('D', 'F')))
    # -. F = 0
    p1 = '( %s /\\ -. F = 0 )' % ph
    nf = w.s([], 'simpr', '( %s -> -. F = 0 )' % p1)
    fn1 = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % p1)
    fnn = w.s([w.s([fn1, w.s([nf], 'neqned', '( %s -> F =/= 0 )' % p1)], 'jca', '( %s -> ( F e. NN0 /\\ F =/= 0 ) )' % p1),
               w.s([], 'elnnne0', '( F e. NN <-> ( F e. NN0 /\\ F =/= 0 ) )')], 'sylibr', '( %s -> F e. NN )' % p1)
    fm = w.s([fnn, w.inst('nnm1nn0')], 'syl', '( %s -> ( F - 1 ) e. NN0 )' % p1)
    np1 = w.s([w.s([fn1], 'nn0cnd', '( %s -> F e. CC )' % p1), w.s([], '1cnd', '( %s -> 1 e. CC )' % p1)], 'npcand', '( %s -> ( ( F - 1 ) + 1 ) = F )' % p1)
    g1 = w.s([w.s([w.s([mn], 'adantr', '( %s -> M e. NN0 )' % p1), w.s([dn], 'adantr', '( %s -> D e. NN0 )' % p1)], 'jca',
                  '( %s -> ( M e. NN0 /\\ D e. NN0 ) )' % p1), fm, w.inst('tmipgp1')], 'syl2anc', '( %s -> 1 <_ %s )' % (p1, C2('D', '( ( F - 1 ) + 1 )')))
    g2 = w.s([g1, w.s([w.s([w.s([np1], 'fveq2d', '( %s -> %s = %s )' % (p1, PG('D', '( ( F - 1 ) + 1 )'), PG('D', 'F')))], 'fveq2d',
                          '( %s -> %s = %s )' % (p1, C2('D', '( ( F - 1 ) + 1 )'), C2('D', 'F')))], 'id', '') if False else
              w.s([w.s([np1], 'fveq2d', '( %s -> %s = %s )' % (p1, PG('D', '( ( F - 1 ) + 1 )'), PG('D', 'F')))], 'fveq2d',
                  '( %s -> %s = %s )' % (p1, C2('D', '( ( F - 1 ) + 1 )'), C2('D', 'F')))], 'breqtrd', '( %s -> 1 <_ %s )' % (p1, C2('D', 'F')))
    c = Closure(w, p1, {})
    c.atom(C2('D', 'F'))
    _, q2 = pgcl(w, p1, 'D', 'F', w.s([mn], 'adantr', '( %s -> M e. NN0 )' % p1), w.s([dn], 'adantr', '( %s -> D e. NN0 )' % p1), fn1)
    c.leaf(C2('D', 'F'), 'NN0', q2)
    lt = linarith(w, p1, [g2], '0 < %s' % C2('D', 'F'), closure=c)
    nz = w.s([w.s([lt], 'gt0ne0d' if False else 'ltned', '( %s -> 0 =/= %s )' % (p1, C2('D', 'F')))], 'necomd', '( %s -> %s =/= 0 )' % (p1, C2('D', 'F')))
    nz2 = w.s([nz], 'neneqd', '( %s -> -. %s = 0 )' % (p1, C2('D', 'F')))
    b1 = w.s([nz2], 'ex', '( %s -> ( -. F = 0 -> -. %s = 0 ) )' % (ph, C2('D', 'F')))
    b2 = w.s([b1], 'con4d', '( %s -> ( %s = 0 -> F = 0 ) )' % (ph, C2('D', 'F')))
    bi = w.s([b2, a1], 'impbid', '( %s -> ( %s = 0 <-> F = 0 ) )' % (ph, C2('D', 'F')))
    w.qed([bi, a2], 'jca', ST_0)
    return w.run()



def tmipgshb():
    w = W('tmipgshb', 'Base of the induction for Lean ` primeGo_shift ` .')
    ph = H3
    ps = '( %s /\\ 0 < %s )' % (ph, RR_)
    dn = w.s([w.s([], 'simp2', '( %s -> D e. NN0 )' % ph)], 'adantr', '( %s -> D e. NN0 )' % ps)
    fn = w.s([w.s([], 'simp3', '( %s -> F e. NN0 )' % ph)], 'adantr', '( %s -> F e. NN0 )' % ps)
    a0 = w.s([w.s([dn], 'nn0cnd', '( %s -> D e. CC )' % ps)], 'addridd', '( %s -> ( D + 0 ) = D )' % ps)
    s0 = w.s([w.s([fn], 'nn0cnd', '( %s -> F e. CC )' % ps)], 'subid1d', '( %s -> ( F - 0 ) = F )' % ps)
    pe = w.s([w.s([a0], 'oveq2d', '( %s -> ( M PrimeGo ( D + 0 ) ) = ( M PrimeGo D ) )' % ps), s0], 'fveq12d',
             '( %s -> %s = %s )' % (ps, PG('( D + 0 )', '( F - 0 )'), PG('D', 'F')))
    e1 = w.s([w.s([pe], 'fveq2d', '( %s -> %s = %s )' % (ps, C1('( D + 0 )', '( F - 0 )'), C1('D', 'F')))], 'eqcomd',
             '( %s -> %s = %s )' % (ps, C1('D', 'F'), C1('( D + 0 )', '( F - 0 )')))
    e2a = w.s([pe], 'fveq2d', '( %s -> %s = %s )' % (ps, C2('( D + 0 )', '( F - 0 )'), RR_))
    _, q2 = pgcl(w, ps, 'D', 'F', w.s([w.s([], 'simp1', '( %s -> M e. NN0 )' % ph)], 'adantr', '( %s -> M e. NN0 )' % ps), dn, fn)
    e2b = w.s([w.s([q2], 'nn0cnd', '( %s -> %s e. CC )' % (ps, C2('( D + 0 )', '( F - 0 )'))) if False else
               w.s([w.s([e2a, w.s([q2], 'nn0cnd', '( %s -> %s e. CC )' % (ps, RR_))], 'eqeltrd', '( %s -> %s e. CC )' % (ps, C2('( D + 0 )', '( F - 0 )')))],
                   'id', '') if False else
               w.s([e2a, w.s([q2], 'nn0cnd', '( %s -> %s e. CC )' % (ps, RR_))], 'eqeltrd', '( %s -> %s e. CC )' % (ps, C2('( D + 0 )', '( F - 0 )')))],
              'addridd', '( %s -> ( %s + 0 ) = %s )' % (ps, C2('( D + 0 )', '( F - 0 )'), C2('( D + 0 )', '( F - 0 )')))
    e2 = w.s([w.s([e2b, e2a], 'eqtrd', '( %s -> ( %s + 0 ) = %s )' % (ps, C2('( D + 0 )', '( F - 0 )'), RR_))], 'eqcomd',
             '( %s -> %s = ( %s + 0 ) )' % (ps, RR_, C2('( D + 0 )', '( F - 0 )')))
    j = w.s([e1, e2], 'jca', '( %s -> ( %s = %s /\\ %s = ( %s + 0 ) ) )' % (ps, C1('D', 'F'), C1('( D + 0 )', '( F - 0 )'), RR_, C2('( D + 0 )', '( F - 0 )')))
    w.qed([j], 'ex', PHSH('0'))
    return w.run()


def tmipgshs():
    w = W('tmipgshs', 'Step of the induction for Lean ` primeGo_shift ` : an iteration that is not the last passes to '
                      '` ( d + 1 , fuel - 1 ) ` with the same result and one iteration fewer.')
    A = '( N e. NN0 /\\ %s )' % PHSH('N')
    N1 = '( N + 1 )'
    B = '( ( %s /\\ %s ) /\\ %s < %s )' % (A, H3, N1, RR_)
    L = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (B, f))
    h3 = w.s([], 'simplr', '( %s -> %s )' % (B, H3))
    mn = w.s([h3], 'simp1d', '( %s -> M e. NN0 )' % B)
    dn = w.s([h3], 'simp2d', '( %s -> D e. NN0 )' % B)
    fn = w.s([h3], 'simp3d', '( %s -> F e. NN0 )' % B)
    nn = w.s([w.s([], 'simpll', '( %s -> %s )' % (B, A))], 'simpld', '( %s -> N e. NN0 )' % B)
    ih = w.s([w.s([], 'simpll', '( %s -> %s )' % (B, A))], 'simprd', '( %s -> %s )' % (B, PHSH('N')))
    lt1 = w.s([], 'simpr', '( %s -> %s < %s )' % (B, N1, RR_))
    _, rn = pgcl(w, B, 'D', 'F', mn, dn, fn)
    cl = Closure(w, B, {'N': ('NN0', nn), 'F': ('NN0', fn), 'D': ('NN0', dn), RR_: ('NN0', rn)})
    cl.atom(RR_)
    nlt = linarith(w, B, [lt1], 'N < %s' % RR_, closure=cl)
    ihb = w.s([w.s([ih, h3], 'mpd', '( %s -> ( N < %s -> ( %s = %s /\\ %s = ( %s + N ) ) ) )'
                   % (B, RR_, C1('D', 'F'), C1('( D + N )', '( F - N )'), RR_, C2('( D + N )', '( F - N )'))), nlt], 'mpd',
              '( %s -> ( %s = %s /\\ %s = ( %s + N ) ) )' % (B, C1('D', 'F'), C1('( D + N )', '( F - N )'), RR_, C2('( D + N )', '( F - N )')))
    e1 = w.s([ihb], 'simpld', '( %s -> %s = %s )' % (B, C1('D', 'F'), C1('( D + N )', '( F - N )')))
    e2 = w.s([ihb], 'simprd', '( %s -> %s = ( %s + N ) )' % (B, RR_, C2('( D + N )', '( F - N )')))
    le = w.s([h3, w.inst('tmipgle')], 'syl', '( %s -> %s <_ F )' % (B, RR_))
    DN = '( D + N )'; FN = '( F - ( N + 1 ) )'
    dnn = cl.mem(DN, 'NN0')
    fsub = w.s([w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (B, N1)), fn,
                linarith(w, B, [lt1, le], '%s <_ F' % N1, closure=cl), w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (B, FN))
    cl.have(FN, 'NN0', fsub)
    fe = lineq(w, B, '( F - N )', '( %s + 1 )' % FN, closure=cl)
    pe = w.s([fe], 'fveq2d', '( %s -> %s = %s )' % (B, PG(DN, '( F - N )'), PG(DN, '( %s + 1 )' % FN)))
    k = cases(w, B, DN, FN, dnn, mn, fsub)
    RDN = C2(DN, '( F - N )')
    rdn2 = linarith(w, B, [e2, lt1], '2 <_ %s' % RDN, closure=cl, atoms=[RDN]) if False else None
    _, rdnn = pgcl(w, B, DN, '( F - N )', mn, dnn, cl.mem('( F - N )', 'NN0') if False else
                   w.s([nn, fn, linarith(w, B, [nlt, le], 'N <_ F', closure=cl), w.inst('nn0sub2')], 'syl3anc', '( %s -> ( F - N ) e. NN0 )' % B))
    cl.leaf(RDN, 'NN0', rdnn)
    two = linarith(w, B, [e2, lt1], '1 < %s' % RDN, closure=cl)
    VAL = k['val']
    c2v = w.s([w.s([pe], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (B, RDN, VAL))], 'id', '') if False else w.s([pe], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (B, RDN, VAL))
    GOAL = '( %s = %s /\\ %s = ( %s + %s ) )' % (C1('D', 'F'), C1('( D + %s )' % N1, '( F - %s )' % N1), RR_, C2('( D + %s )' % N1, '( F - %s )' % N1), N1)
    def contra(T, v, one_lab):
        """in case T the cost is 1 < 2 <_ RDN: anything"""
        p = projeq(w, T, VAL, v, one_lab, '1', vex(w, T, one_lab, '1oex' if one_lab == '1o' else '0ex'), vex(w, T, '1', '1ex'), 2)
        LT = lambda st, f: w.s([st], 'adantr' if T.count(' /\\ ') == B.count(' /\\ ') + 1 else 'ad2antrr', '( %s -> %s )' % (T, f))
        r1 = w.s([LT(c2v, '%s = ( 2nd ` %s )' % (RDN, VAL)), p], 'eqtrd', '( %s -> %s = 1 )' % (T, RDN))
        cT = Closure(w, T, {RDN: ('NN0', LT(rdnn, '%s e. NN0' % RDN))})
        cT.atom(RDN)
        a = linarith(w, T, [r1], '%s <_ 1' % RDN, closure=cT)
        b = w.s([cT.mem(RDN, 'RR'), cT.mem('1', 'RR')], 'lenltd', '( %s -> ( %s <_ 1 <-> -. 1 < %s ) )' % (T, RDN, RDN))
        nb = w.s([a, b], 'mpbid', '( %s -> -. 1 < %s )' % (T, RDN))
        return w.s([LT(two, '1 < %s' % RDN), nb], 'pm2.21dd', '( %s -> %s )' % (T, GOAL))
    g1 = contra(k['T1'], k['vt1'], '1o')
    g2 = contra(k['T2'], k['vt2'], '(/)')
    T3 = k['T3']
    L3 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (T3, f))
    D1 = '( %s + 1 )' % DN
    d1n = w.s([L3(dnn, '%s e. NN0' % DN), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (T3, D1))
    q1, q2 = pgcl(w, T3, D1, FN, L3(mn, 'M e. NN0'), d1n, L3(fsub, '%s e. NN0' % FN))
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (T3, C2(D1, FN)))
    p1_ = projeq(w, T3, VAL, k['vf2'], C1(D1, FN), '( %s + 1 )' % C2(D1, FN), q1, q2p, 1)
    p2_ = projeq(w, T3, VAL, k['vf2'], C1(D1, FN), '( %s + 1 )' % C2(D1, FN), q1, q2p, 2)
    da = w.s([w.s([L3(dn, 'D e. NN0')], 'nn0cnd', '( %s -> D e. CC )' % T3), w.s([L3(nn, 'N e. NN0')], 'nn0cnd', '( %s -> N e. CC )' % T3),
              w.s([], '1cnd', '( %s -> 1 e. CC )' % T3)], 'addassd', '( %s -> %s = ( D + %s ) )' % (T3, D1, N1))
    pg1 = w.s([da], 'oveq2d', '( %s -> ( M PrimeGo %s ) = ( M PrimeGo ( D + %s ) ) )' % (T3, D1, N1))
    pgq = w.s([pg1], 'fveq1d', '( %s -> %s = %s )' % (T3, PG(D1, FN), PG('( D + %s )' % N1, FN)))
    c1e = w.s([pgq], 'fveq2d', '( %s -> %s = %s )' % (T3, C1(D1, FN), C1('( D + %s )' % N1, FN)))
    c2e = w.s([pgq], 'fveq2d', '( %s -> %s = %s )' % (T3, C2(D1, FN), C2('( D + %s )' % N1, FN)))
    # 1st
    f1 = w.s([w.s([L3(e1, '%s = %s' % (C1('D', 'F'), C1(DN, '( F - N )'))), L3(w.s([pe], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (B, C1(DN, '( F - N )'), VAL)),
                                                                              '%s = ( 1st ` %s )' % (C1(DN, '( F - N )'), VAL))], 'eqtrd',
                  '( %s -> %s = ( 1st ` %s ) )' % (T3, C1('D', 'F'), VAL)), p1_], 'eqtrd', '( %s -> %s = %s )' % (T3, C1('D', 'F'), C1(D1, FN)))
    f1b = w.s([f1, c1e], 'eqtrd', '( %s -> %s = %s )' % (T3, C1('D', 'F'), C1('( D + %s )' % N1, FN)))
    # 2nd
    r2 = w.s([L3(c2v, '%s = ( 2nd ` %s )' % (RDN, VAL)), p2_], 'eqtrd', '( %s -> %s = ( %s + 1 ) )' % (T3, RDN, C2(D1, FN)))
    c3 = Closure(w, T3, {'N': ('NN0', L3(nn, 'N e. NN0'))})
    for a_ in [RR_, RDN, C2(D1, FN), C2('( D + %s )' % N1, FN)]:
        c3.atom(a_)
    c3.have(RR_, 'NN0', L3(rn, '%s e. NN0' % RR_)); c3.have(RDN, 'NN0', L3(rdnn, '%s e. NN0' % RDN)); c3.have(C2(D1, FN), 'NN0', q2)
    c3.have(C2('( D + %s )' % N1, FN), 'NN0', w.s([c2e, q2], 'eqeltrrd', '( %s -> %s e. NN0 )' % (T3, C2('( D + %s )' % N1, FN))))
    r3 = lineq(w, T3, RR_, '( %s + %s )' % (C2('( D + %s )' % N1, FN), N1), hyps=[L3(e2, '%s = ( %s + N )' % (RR_, RDN)), r2, c2e], closure=c3)
    g3 = w.s([f1b, r3], 'jca', '( %s -> %s )' % (T3, GOAL))
    gnf = w.s([g2, g3], 'pm2.61dan', '( %s -> %s )' % (k['NF'], GOAL))
    gb = w.s([g1, gnf], 'pm2.61dan', '( %s -> %s )' % (B, GOAL))
    e_ = w.s([gb], 'ex', '( ( %s /\\ %s ) -> ( %s < %s -> %s ) )' % (A, H3, N1, RR_, GOAL))
    w.qed([e_], 'ex', '( %s -> %s )' % (A, PHSH(N1)))
    return w.run()


def tmipgsh():
    w = W('tmipgsh', 'Lean ` primeGo_shift ` : after ` I ` iterations that are not the last, the loop is at '
                     '` ( d + I , fuel - I ) ` with the same result and ` I ` iterations fewer.')
    ph = split_imp(ST_SH)[0]
    st, pt = fuelind(w, PHSH('f'), 'I', 'tmipgshb', 'tmipgshs', fvar='f')
    inn = w.s([], 'simprl', '( %s -> I e. NN0 )' % ph)
    ilt = w.s([], 'simprr', '( %s -> I < %s )' % (ph, RR_))
    h = w.s([], 'simpl', '( %s -> %s )' % (ph, H3))
    a = w.s([w.s([inn, st], 'syl', '( %s -> %s )' % (ph, pt)), h], 'mpd', '( %s -> ( I < %s -> %s ) )' % (ph, RR_, split_imp(ST_SH)[1]))
    w.qed([a, ilt], 'mpd', ST_SH)
    return w.run()



def tmipgit():
    ph = split_imp(ST_IT)[0]
    w = W('tmipgit', 'The three exits of iteration ` I ` of the ` primeGo ` loop (Lean ` primeIters_succ_lt ` , '
                     '` _succ_dvd ` , ` _succ_next ` after ` primeGo_shift ` ): if ` m < ( d + I ) ^ 2 ` it is the last '
                     'and the answer is true; if ` d + I ` divides ` m ` it is the last and the answer is false; otherwise '
                     'another iteration follows exactly when fuel remains, and without fuel the answer is true.')
    h3 = w.s([], 'simpl', '( %s -> %s )' % (ph, H3))
    mn = w.s([h3], 'simp1d', '( %s -> M e. NN0 )' % ph)
    dn = w.s([h3], 'simp2d', '( %s -> D e. NN0 )' % ph)
    fn = w.s([h3], 'simp3d', '( %s -> F e. NN0 )' % ph)
    inn = w.s([], 'simprl', '( %s -> I e. NN0 )' % ph)
    ilt = w.s([], 'simprr', '( %s -> I < %s )' % (ph, RR_))
    sh = w.s([], 'tmipgsh', ST_SH) if False else w.s([w.inst('tmipgsh')], 'id', '') if False else None
    sh = w.s([w.s([], 'id', '( %s -> %s )' % (ph, ph)) if False else h3, w.s([inn, ilt], 'jca', '( %s -> ( I e. NN0 /\\ I < %s ) )' % (ph, RR_)),
              w.inst('tmipgsh')], 'syl2anc', '( %s -> %s )' % (ph, split_imp(ST_SH)[1]))
    e1 = w.s([sh], 'simpld', '( %s -> %s = %s )' % (ph, C1('D', 'F'), C1(DI, '( F - I )')))
    e2 = w.s([sh], 'simprd', '( %s -> %s = ( %s + I ) )' % (ph, RR_, C2(DI, '( F - I )')))
    le = w.s([h3, w.inst('tmipgle')], 'syl', '( %s -> %s <_ F )' % (ph, RR_))
    _, rn = pgcl(w, ph, 'D', 'F', mn, dn, fn)
    cl = Closure(w, ph, {'I': ('NN0', inn), 'F': ('NN0', fn), 'D': ('NN0', dn), RR_: ('NN0', rn)})
    cl.atom(RR_)
    dinn = cl.mem(DI, 'NN0')
    zl = w.s([cl.mem('I', 'ZZ'), cl.mem(RR_, 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( I < %s <-> %s <_ %s ) )' % (ph, RR_, I1, RR_))
    i1le = w.s([ilt, zl], 'mpbid', '( %s -> %s <_ %s )' % (ph, I1, RR_))
    fsub = w.s([w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, I1)), fn,
                linarith(w, ph, [i1le, le], '%s <_ F' % I1, closure=cl), w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, FI1))
    cl.have(FI1, 'NN0', fsub)
    fe = lineq(w, ph, '( F - I )', '( %s + 1 )' % FI1, closure=cl)
    pe = w.s([fe], 'fveq2d', '( %s -> %s = %s )' % (ph, PG(DI, '( F - I )'), PG(DI, '( %s + 1 )' % FI1)))
    k = cases(w, ph, DI, FI1, dinn, mn, fsub)
    VAL = k['val']
    c1v = w.s([pe], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, C1(DI, '( F - I )'), VAL))
    c2v = w.s([pe], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (ph, C2(DI, '( F - I )'), VAL))
    RDI = C2(DI, '( F - I )')
    fmi = w.s([inn, fn, linarith(w, ph, [ilt, le], 'I <_ F', closure=cl), w.inst('nn0sub2')], 'syl3anc', '( %s -> ( F - I ) e. NN0 )' % ph)
    _, rdin = pgcl(w, ph, DI, '( F - I )', mn, dinn, fmi)
    def lift(T, st):
        f = concl(w, ph, st)
        n = T.count(' /\\ ') - ph.count(' /\\ ')
        return w.s([st], 'adantr' if n == 1 else 'ad2antrr', '( %s -> %s )' % (T, f))
    out = []
    for case, (T, v, b) in enumerate([(k['T1'], k['vt1'], '1o'), (k['T2'], k['vt2'], '(/)')]):
        p2 = projeq(w, T, VAL, v, b, '1', vex(w, T, b, '1oex' if b == '1o' else '0ex'), vex(w, T, '1', '1ex'), 2)
        p1 = projeq(w, T, VAL, v, b, '1', vex(w, T, b, '1oex' if b == '1o' else '0ex'), vex(w, T, '1', '1ex'), 1)
        r1 = w.s([lift(T, c2v), p2], 'eqtrd', '( %s -> %s = 1 )' % (T, RDI))
        cT = Closure(w, T, {'I': ('NN0', lift(T, inn))})
        cT.atom(RR_); cT.atom(RDI)
        cT.have(RR_, 'NN0', lift(T, rn)); cT.have(RDI, 'NN0', lift(T, rdin))
        rr = lineq(w, T, RR_, I1, hyps=[lift(T, e2), r1], closure=cT)
        res = w.s([w.s([lift(T, e1), lift(T, c1v)], 'eqtrd', '( %s -> %s = ( 1st ` %s ) )' % (T, C1('D', 'F'), VAL)), p1], 'eqtrd',
                  '( %s -> %s = %s )' % (T, C1('D', 'F'), b))
        out.append(w.s([rr, res], 'jca', '( %s -> ( %s = %s /\\ %s = %s ) )' % (T, RR_, I1, C1('D', 'F'), b)))
    part1 = w.s([out[0]], 'ex', '( %s -> ( %s -> ( %s = %s /\\ %s = 1o ) ) )' % (ph, k['C1'], RR_, I1, C1('D', 'F')))
    x2 = w.s([out[1]], 'ex', '( %s -> ( %s -> ( %s = %s /\\ %s = (/) ) ) )' % (k['NF'], k['C2'], RR_, I1, C1('D', 'F')))
    x2b = w.s([x2], 'ex', '( %s -> ( -. %s -> ( %s -> ( %s = %s /\\ %s = (/) ) ) ) )' % (ph, k['C1'], k['C2'], RR_, I1, C1('D', 'F')))
    part2 = w.s([x2b], 'impd', '( %s -> ( ( -. %s /\\ %s ) -> ( %s = %s /\\ %s = (/) ) ) )' % (ph, k['C1'], k['C2'], RR_, I1, C1('D', 'F')))
    # case 3
    T3 = k['T3']
    D1 = '( %s + 1 )' % DI
    d1n = w.s([lift(T3, dinn), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (T3, D1))
    q1, q2 = pgcl(w, T3, D1, FI1, lift(T3, mn), d1n, lift(T3, fsub))
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (T3, C2(D1, FI1)))
    p1_ = projeq(w, T3, VAL, k['vf2'], C1(D1, FI1), '( %s + 1 )' % C2(D1, FI1), q1, q2p, 1)
    p2_ = projeq(w, T3, VAL, k['vf2'], C1(D1, FI1), '( %s + 1 )' % C2(D1, FI1), q1, q2p, 2)
    X = C2(D1, FI1)
    r3 = w.s([lift(T3, c2v), p2_], 'eqtrd', '( %s -> %s = ( %s + 1 ) )' % (T3, RDI, X))
    z3 = w.s([w.s([w.s([lift(T3, mn), d1n, lift(T3, fsub)], '3jca', '( %s -> ( M e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (T3, D1, FI1)),
                   w.inst('tmipg0')], 'syl', '( %s -> ( ( %s = 0 <-> %s = 0 ) /\\ ( %s = 0 -> %s = 1o ) ) )' % (T3, X, FI1, FI1, C1(D1, FI1)))], 'id', '') if False else \
        w.s([w.s([lift(T3, mn), d1n, lift(T3, fsub)], '3jca', '( %s -> ( M e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (T3, D1, FI1)), w.inst('tmipg0')], 'syl',
            '( %s -> ( ( %s = 0 <-> %s = 0 ) /\\ ( %s = 0 -> %s = 1o ) ) )' % (T3, X, FI1, FI1, C1(D1, FI1)))
    zb = w.s([z3], 'simpld', '( %s -> ( %s = 0 <-> %s = 0 ) )' % (T3, X, FI1))
    zr = w.s([z3], 'simprd', '( %s -> ( %s = 0 -> %s = 1o ) )' % (T3, FI1, C1(D1, FI1)))
    c3 = Closure(w, T3, {'I': ('NN0', lift(T3, inn))})
    for a_, st_ in [(RR_, lift(T3, rn)), (RDI, lift(T3, rdin)), (X, q2)]:
        c3.atom(a_); c3.have(a_, 'NN0', st_)
    e2_3 = lift(T3, e2)
    # ( I + 1 < R -> -. FI1 = 0 )
    pa = '( %s /\\ %s < %s )' % (T3, I1, RR_)
    La = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pa, concl(w, T3, st)))
    ca = Closure(w, pa, {'I': ('NN0', La(lift(T3, inn)))})
    for a_, st_ in [(RR_, La(lift(T3, rn))), (RDI, La(lift(T3, rdin))), (X, La(q2))]:
        ca.atom(a_); ca.have(a_, 'NN0', st_)
    xpos = linarith(w, pa, [La(e2_3), La(r3), w.s([], 'simpr', '( %s -> %s < %s )' % (pa, I1, RR_))], '0 < %s' % X, closure=ca)
    xn0 = w.s([w.s([xpos], 'gt0ne0d', '( %s -> %s =/= 0 )' % (pa, X))], 'neneqd', '( %s -> -. %s = 0 )' % (pa, X))
    fn0 = w.s([xn0, La(zb)], 'mtbid' if False else 'mtbird', '') if False else w.s([La(zb), xn0], 'mtbid', '( %s -> -. %s = 0 )' % (pa, FI1))
    ia = w.s([fn0], 'ex', '( %s -> ( %s < %s -> -. %s = 0 ) )' % (T3, I1, RR_, FI1))
    # ( -. FI1 = 0 -> I + 1 < R )
    pb = '( %s /\\ -. %s = 0 )' % (T3, FI1)
    Lb = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pb, concl(w, T3, st)))
    xn = w.s([Lb(zb), w.s([], 'simpr', '( %s -> -. %s = 0 )' % (pb, FI1))], 'mtbird', '( %s -> -. %s = 0 )' % (pb, X))
    xnn = w.s([w.s([Lb(q2), w.s([xn], 'neqned', '( %s -> %s =/= 0 )' % (pb, X))], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (pb, X, X)),
               w.s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (X, X, X))], 'sylibr', '( %s -> %s e. NN )' % (pb, X))
    x1 = w.s([xnn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pb, X))
    cb_ = Closure(w, pb, {'I': ('NN0', Lb(lift(T3, inn)))})
    for a_, st_ in [(RR_, Lb(lift(T3, rn))), (RDI, Lb(lift(T3, rdin))), (X, Lb(q2))]:
        cb_.atom(a_); cb_.have(a_, 'NN0', st_)
    lt_ = linarith(w, pb, [Lb(e2_3), Lb(r3), x1], '%s < %s' % (I1, RR_), closure=cb_)
    ib = w.s([lt_], 'ex', '( %s -> ( -. %s = 0 -> %s < %s ) )' % (T3, FI1, I1, RR_))
    bi = w.s([ia, ib], 'impbid', '( %s -> ( %s < %s <-> -. %s = 0 ) )' % (T3, I1, RR_, FI1))
    # ( FI1 = 0 -> ( R = I + 1 /\ result = 1o ) )
    pc = '( %s /\\ %s = 0 )' % (T3, FI1)
    Lc = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pc, concl(w, T3, st)))
    x0 = w.s([Lc(zb), w.s([], 'simpr', '( %s -> %s = 0 )' % (pc, FI1))], 'mpbird', '( %s -> %s = 0 )' % (pc, X))
    cc_ = Closure(w, pc, {'I': ('NN0', Lc(lift(T3, inn)))})
    for a_, st_ in [(RR_, Lc(lift(T3, rn))), (RDI, Lc(lift(T3, rdin))), (X, Lc(q2))]:
        cc_.atom(a_); cc_.have(a_, 'NN0', st_)
    rr1 = lineq(w, pc, RR_, I1, hyps=[Lc(e2_3), Lc(r3), x0], closure=cc_)
    res1 = w.s([w.s([w.s([Lc(lift(T3, e1)), Lc(lift(T3, c1v))], 'eqtrd', '( %s -> %s = ( 1st ` %s ) )' % (pc, C1('D', 'F'), VAL)), Lc(p1_)], 'eqtrd',
                    '( %s -> %s = %s )' % (pc, C1('D', 'F'), C1(D1, FI1))),
                w.s([Lc(zr), w.s([], 'simpr', '( %s -> %s = 0 )' % (pc, FI1))], 'mpd', '( %s -> %s = 1o )' % (pc, C1(D1, FI1)))], 'eqtrd',
               '( %s -> %s = 1o )' % (pc, C1('D', 'F')))
    ic = w.s([w.s([rr1, res1], 'jca', '( %s -> ( %s = %s /\\ %s = 1o ) )' % (pc, RR_, I1, C1('D', 'F')))], 'ex',
             '( %s -> ( %s = 0 -> ( %s = %s /\\ %s = 1o ) ) )' % (T3, FI1, RR_, I1, C1('D', 'F')))
    G3 = '( ( %s < %s <-> -. %s = 0 ) /\\ ( %s = 0 -> ( %s = %s /\\ %s = 1o ) ) )' % (I1, RR_, FI1, FI1, RR_, I1, C1('D', 'F'))
    g3 = w.s([bi, ic], 'jca', '( %s -> %s )' % (T3, G3))
    x3 = w.s([g3], 'ex', '( %s -> ( -. %s -> %s ) )' % (k['NF'], k['C2'], G3))
    x3b = w.s([x3], 'ex', '( %s -> ( -. %s -> ( -. %s -> %s ) ) )' % (ph, k['C1'], k['C2'], G3))
    part3 = w.s([x3b], 'impd', '( %s -> ( ( -. %s /\\ -. %s ) -> %s ) )' % (ph, k['C1'], k['C2'], G3))
    w.qed([part1, part2, part3], '3jca', ST_IT)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
