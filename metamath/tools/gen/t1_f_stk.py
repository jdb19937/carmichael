"""T1: the stack-assignment algebra of the machine layer --- the value of an
updated assignment and the two collapse identities every scan loop needs."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GK = '( %s ` K )' % G('T')
RES = '( D |` ( %s \\ { K } ) )' % DG
SNG = '{ <. K , Y >. }'
U = UPD('T', 'D', 'K', 'Y')


def tm2stkupv():
    lab = 'tm2stkupv'
    ph = '( ( T e. V /\\ D e. %s ) /\\ ( K e. %s /\\ Y e. W ) /\\ J e. %s )' % (STK('T'), DG, DG)
    w = W(lab, 'The value of a stack assignment updated at one index.  Lean: '
               '` Function.update S k x ` .')
    tv = w.s([], 'simp1l', '( %s -> T e. V )' % ph)
    dd = w.s([], 'simp1r', '( %s -> D e. %s )' % (ph, STK('T')))
    kk = w.s([], 'simp2l', '( %s -> K e. %s )' % (ph, DG))
    yy = w.s([], 'simp2r', '( %s -> Y e. W )' % ph)
    jj = w.s([], 'simp3', '( %s -> J e. %s )' % (ph, DG))
    dfn = w.s([tv, dd, w.inst('tm2stkfn')], 'syl2anc', '( %s -> D Fn %s )' % (ph, DG))
    dss = w.s([], 'difss', '( %s \\ { K } ) C_ %s' % (DG, DG))
    dssa = w.s([dss], 'a1i', '( %s -> ( %s \\ { K } ) C_ %s )' % (ph, DG, DG))
    rfn = w.s([dfn, dssa, w.inst('fnssres')], 'syl2anc', '( %s -> %s Fn ( %s \\ { K } ) )' % (ph, RES, DG))
    kv = w.s([kk], 'elexd', '( %s -> K e. _V )' % ph)
    sfn = w.s([kv, yy, w.inst('fnsng')], 'syl2anc', '( %s -> %s Fn { K } )' % (ph, SNG))
    dj = w.s([], 'disjdifr', '( ( %s \\ { K } ) i^i { K } ) = (/)' % DG)
    dja = w.s([dj], 'a1i', '( %s -> ( ( %s \\ { K } ) i^i { K } ) = (/) )' % (ph, DG))
    IFF = 'if ( J = K , Y , ( D ` J ) )'
    # case J = K
    ph1 = '( %s /\\ J = K )' % ph
    jk = w.s([], 'simpr', '( %s -> J = K )' % ph1)
    kva = w.s([kv], 'adantr', '( %s -> K e. _V )' % ph1)
    ksn = w.s([kva, w.inst('snidg')], 'syl', '( %s -> K e. { K } )' % ph1)
    jsn = w.s([jk, ksn], 'eqeltrd', '( %s -> J e. { K } )' % ph1)
    dja1 = w.s([dja], 'adantr', '( %s -> ( ( %s \\ { K } ) i^i { K } ) = (/) )' % (ph1, DG))
    j1 = w.s([dja1, jsn], 'jca', '( %s -> ( ( ( %s \\ { K } ) i^i { K } ) = (/) /\\ J e. { K } ) )' % (ph1, DG))
    rfn1 = w.s([rfn], 'adantr', '( %s -> %s Fn ( %s \\ { K } ) )' % (ph1, RES, DG))
    sfn1 = w.s([sfn], 'adantr', '( %s -> %s Fn { K } )' % (ph1, SNG))
    u1 = w.s([rfn1, sfn1, j1, w.inst('fvun2')], 'syl3anc', '( %s -> ( %s ` J ) = ( %s ` J ) )' % (ph1, U, SNG))
    u2 = w.s([jk], 'fveq2d', '( %s -> ( %s ` J ) = ( %s ` K ) )' % (ph1, SNG, SNG))
    yy1 = w.s([yy], 'adantr', '( %s -> Y e. W )' % ph1)
    u3 = w.s([kva, yy1, w.inst('fvsng')], 'syl2anc', '( %s -> ( %s ` K ) = Y )' % (ph1, SNG))
    u4 = w.s([u1, u2], 'eqtrd', '( %s -> ( %s ` J ) = ( %s ` K ) )' % (ph1, U, SNG))
    u5 = w.s([u4, u3], 'eqtrd', '( %s -> ( %s ` J ) = Y )' % (ph1, U))
    i1 = w.s([jk], 'iftrued', '( %s -> %s = Y )' % (ph1, IFF))
    c1 = w.s([u5, i1], 'eqtr4d', '( %s -> ( %s ` J ) = %s )' % (ph1, U, IFF))
    # case J =/= K
    ph2 = '( %s /\\ -. J = K )' % ph
    njk = w.s([], 'simpr', '( %s -> -. J = K )' % ph2)
    nje = w.s([njk], 'neqned', '( %s -> J =/= K )' % ph2)
    jj2 = w.s([jj], 'adantr', '( %s -> J e. %s )' % (ph2, DG))
    jd0 = w.s([jj2, nje], 'jca', '( %s -> ( J e. %s /\\ J =/= K ) )' % (ph2, DG))
    jd1 = w.s([jd0, w.inst('eldifsn')], 'sylibr', '( %s -> J e. ( %s \\ { K } ) )' % (ph2, DG))
    dja2 = w.s([dja], 'adantr', '( %s -> ( ( %s \\ { K } ) i^i { K } ) = (/) )' % (ph2, DG))
    j2 = w.s([dja2, jd1], 'jca', '( %s -> ( ( ( %s \\ { K } ) i^i { K } ) = (/) /\\ J e. ( %s \\ { K } ) ) )' % (ph2, DG, DG))
    rfn2 = w.s([rfn], 'adantr', '( %s -> %s Fn ( %s \\ { K } ) )' % (ph2, RES, DG))
    sfn2 = w.s([sfn], 'adantr', '( %s -> %s Fn { K } )' % (ph2, SNG))
    v1 = w.s([rfn2, sfn2, j2, w.inst('fvun1')], 'syl3anc', '( %s -> ( %s ` J ) = ( %s ` J ) )' % (ph2, U, RES))
    v2 = w.s([jd1, w.inst('fvres')], 'syl', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph2, RES))
    v3 = w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph2, U))
    i2 = w.s([njk], 'iffalsed', '( %s -> %s = ( D ` J ) )' % (ph2, IFF))
    c2 = w.s([v3, i2], 'eqtr4d', '( %s -> ( %s ` J ) = %s )' % (ph2, U, IFF))
    w.qed([c1, c2], 'pm2.61dan', '( %s -> ( %s ` J ) = %s )' % (ph, U, IFF))
    return w.run()


def tm2stkupid():
    lab = 'tm2stkupid'
    ph = '( T e. V /\\ D e. %s /\\ K e. %s )' % (STK('T'), DG)
    UU = UPD('T', 'D', 'K', '( D ` K )')
    w = W(lab, 'Updating a stack assignment at an index with its own value '
               'changes nothing.')
    tv = w.s([], 'simp1', '( %s -> T e. V )' % ph)
    dd = w.s([], 'simp2', '( %s -> D e. %s )' % (ph, STK('T')))
    kk = w.s([], 'simp3', '( %s -> K e. %s )' % (ph, DG))
    dk = w.s([tv, dd, kk, w.inst('tm2stkfv')], 'syl3anc', '( %s -> ( D ` K ) e. Word %s )' % (ph, GK))
    upd = w.s([tv, dd, w.s([kk, dk], 'jca', '( %s -> ( K e. %s /\\ ( D ` K ) e. Word %s ) )' % (ph, DG, GK)),
               w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UU, STK('T')))
    ufn = w.s([tv, upd, w.inst('tm2stkfn')], 'syl2anc', '( %s -> %s Fn %s )' % (ph, UU, DG))
    dfn = w.s([tv, dd, w.inst('tm2stkfn')], 'syl2anc', '( %s -> D Fn %s )' % (ph, DG))
    ph1 = '( %s /\\ j e. %s )' % (ph, DG)
    tva = w.s([tv], 'adantr', '( %s -> T e. V )' % ph1)
    dda = w.s([dd], 'adantr', '( %s -> D e. %s )' % (ph1, STK('T')))
    kka = w.s([kk], 'adantr', '( %s -> K e. %s )' % (ph1, DG))
    dka = w.s([dk], 'adantr', '( %s -> ( D ` K ) e. Word %s )' % (ph1, GK))
    jja = w.s([], 'simpr', '( %s -> j e. %s )' % (ph1, DG))
    a1 = w.s([tva, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph1, STK('T')))
    a2 = w.s([kka, dka], 'jca', '( %s -> ( K e. %s /\\ ( D ` K ) e. Word %s ) )' % (ph1, DG, GK))
    val = w.s([a1, a2, jja, w.inst('tm2stkupv')], 'syl3anc',
              '( %s -> ( %s ` j ) = if ( j = K , ( D ` K ) , ( D ` j ) ) )' % (ph1, UU))
    ph2 = '( %s /\\ j = K )' % ph1
    jk = w.s([], 'simpr', '( %s -> j = K )' % ph2)
    t1 = w.s([jk], 'iftrued', '( %s -> if ( j = K , ( D ` K ) , ( D ` j ) ) = ( D ` K ) )' % ph2)
    t2 = w.s([jk], 'fveq2d', '( %s -> ( D ` j ) = ( D ` K ) )' % ph2)
    t3 = w.s([t1, t2], 'eqtr4d', '( %s -> if ( j = K , ( D ` K ) , ( D ` j ) ) = ( D ` j ) )' % ph2)
    ph3 = '( %s /\\ -. j = K )' % ph1
    njk = w.s([], 'simpr', '( %s -> -. j = K )' % ph3)
    t4 = w.s([njk], 'iffalsed', '( %s -> if ( j = K , ( D ` K ) , ( D ` j ) ) = ( D ` j ) )' % ph3)
    t5 = w.s([t3, t4], 'pm2.61dan', '( %s -> if ( j = K , ( D ` K ) , ( D ` j ) ) = ( D ` j ) )' % ph1)
    t6 = w.s([val, t5], 'eqtrd', '( %s -> ( %s ` j ) = ( D ` j ) )' % (ph1, UU))
    rg = w.s([t6], 'ralrimiva', '( %s -> A. j e. %s ( %s ` j ) = ( D ` j ) )' % (ph, DG, UU))
    bi = w.s([ufn, dfn, w.inst('eqfnfv')], 'syl2anc',
             '( %s -> ( %s = D <-> A. j e. %s ( %s ` j ) = ( D ` j ) ) )' % (ph, UU, DG, UU))
    w.qed([bi, rg], 'mpbird', '( %s -> %s = D )' % (ph, UU))
    return w.run()


def tm2stkup2():
    lab = 'tm2stkup2'
    ph = ('( ( T e. V /\\ D e. %s ) /\\ K e. %s /\\ ( Y e. Word %s /\\ Z e. Word %s ) )'
          % (STK('T'), DG, GK, GK))
    U1 = UPD('T', 'D', 'K', 'Y')
    UU = UPD('T', U1, 'K', 'Z')
    U2 = UPD('T', 'D', 'K', 'Z')
    w = W(lab, 'Two updates of a stack assignment at the same index collapse '
               'to the second.')
    tv = w.s([], 'simp1l', '( %s -> T e. V )' % ph)
    dd = w.s([], 'simp1r', '( %s -> D e. %s )' % (ph, STK('T')))
    kk = w.s([], 'simp2', '( %s -> K e. %s )' % (ph, DG))
    yy = w.s([], 'simp3l', '( %s -> Y e. Word %s )' % (ph, GK))
    zz = w.s([], 'simp3r', '( %s -> Z e. Word %s )' % (ph, GK))
    ky = w.s([kk, yy], 'jca', '( %s -> ( K e. %s /\\ Y e. Word %s ) )' % (ph, DG, GK))
    kz = w.s([kk, zz], 'jca', '( %s -> ( K e. %s /\\ Z e. Word %s ) )' % (ph, DG, GK))
    up1 = w.s([tv, dd, ky, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, U1, STK('T')))
    upA = w.s([tv, up1, kz, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UU, STK('T')))
    upB = w.s([tv, dd, kz, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, U2, STK('T')))
    fnA = w.s([tv, upA, w.inst('tm2stkfn')], 'syl2anc', '( %s -> %s Fn %s )' % (ph, UU, DG))
    fnB = w.s([tv, upB, w.inst('tm2stkfn')], 'syl2anc', '( %s -> %s Fn %s )' % (ph, U2, DG))
    ph1 = '( %s /\\ j e. %s )' % (ph, DG)
    tva = w.s([tv], 'adantr', '( %s -> T e. V )' % ph1)
    dda = w.s([dd], 'adantr', '( %s -> D e. %s )' % (ph1, STK('T')))
    up1a = w.s([up1], 'adantr', '( %s -> %s e. %s )' % (ph1, U1, STK('T')))
    kka = w.s([kk], 'adantr', '( %s -> K e. %s )' % (ph1, DG))
    yya = w.s([yy], 'adantr', '( %s -> Y e. Word %s )' % (ph1, GK))
    zza = w.s([zz], 'adantr', '( %s -> Z e. Word %s )' % (ph1, GK))
    jja = w.s([], 'simpr', '( %s -> j e. %s )' % (ph1, DG))
    p1 = w.s([tva, up1a], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph1, U1, STK('T')))
    p2 = w.s([kka, zza], 'jca', '( %s -> ( K e. %s /\\ Z e. Word %s ) )' % (ph1, DG, GK))
    vA = w.s([p1, p2, jja, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` j ) = if ( j = K , Z , ( %s ` j ) ) )' % (ph1, UU, U1))
    p3 = w.s([tva, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph1, STK('T')))
    vB = w.s([p3, p2, jja, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` j ) = if ( j = K , Z , ( D ` j ) ) )' % (ph1, U2))
    p4 = w.s([kka, yya], 'jca', '( %s -> ( K e. %s /\\ Y e. Word %s ) )' % (ph1, DG, GK))
    v1 = w.s([p3, p4, jja, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` j ) = if ( j = K , Y , ( D ` j ) ) )' % (ph1, U1))
    ph2 = '( %s /\\ j = K )' % ph1
    jk = w.s([], 'simpr', '( %s -> j = K )' % ph2)
    e1 = w.s([jk], 'iftrued', '( %s -> if ( j = K , Z , ( %s ` j ) ) = Z )' % (ph2, U1))
    e2 = w.s([jk], 'iftrued', '( %s -> if ( j = K , Z , ( D ` j ) ) = Z )' % ph2)
    e3 = w.s([e1, e2], 'eqtr4d', '( %s -> if ( j = K , Z , ( %s ` j ) ) = if ( j = K , Z , ( D ` j ) ) )' % (ph2, U1))
    ph3 = '( %s /\\ -. j = K )' % ph1
    njk = w.s([], 'simpr', '( %s -> -. j = K )' % ph3)
    f1 = w.s([njk], 'iffalsed', '( %s -> if ( j = K , Z , ( %s ` j ) ) = ( %s ` j ) )' % (ph3, U1, U1))
    f2 = w.s([njk], 'iffalsed', '( %s -> if ( j = K , Z , ( D ` j ) ) = ( D ` j ) )' % ph3)
    v1a = w.s([v1], 'adantr', '( %s -> ( %s ` j ) = if ( j = K , Y , ( D ` j ) ) )' % (ph3, U1))
    f3 = w.s([njk], 'iffalsed', '( %s -> if ( j = K , Y , ( D ` j ) ) = ( D ` j ) )' % ph3)
    f4 = w.s([v1a, f3], 'eqtrd', '( %s -> ( %s ` j ) = ( D ` j ) )' % (ph3, U1))
    f5 = w.s([f1, f4], 'eqtrd', '( %s -> if ( j = K , Z , ( %s ` j ) ) = ( D ` j ) )' % (ph3, U1))
    f6 = w.s([f5, f2], 'eqtr4d', '( %s -> if ( j = K , Z , ( %s ` j ) ) = if ( j = K , Z , ( D ` j ) ) )' % (ph3, U1))
    g1 = w.s([e3, f6], 'pm2.61dan', '( %s -> if ( j = K , Z , ( %s ` j ) ) = if ( j = K , Z , ( D ` j ) ) )' % (ph1, U1))
    g2 = w.s([vA, g1], 'eqtrd', '( %s -> ( %s ` j ) = if ( j = K , Z , ( D ` j ) ) )' % (ph1, UU))
    g3 = w.s([g2, vB], 'eqtr4d', '( %s -> ( %s ` j ) = ( %s ` j ) )' % (ph1, UU, U2))
    rg = w.s([g3], 'ralrimiva', '( %s -> A. j e. %s ( %s ` j ) = ( %s ` j ) )' % (ph, DG, UU, U2))
    bi = w.s([fnA, fnB, w.inst('eqfnfv')], 'syl2anc',
             '( %s -> ( %s = %s <-> A. j e. %s ( %s ` j ) = ( %s ` j ) ) )' % (ph, UU, U2, DG, UU, U2))
    w.qed([bi, rg], 'mpbird', '( %s -> %s = %s )' % (ph, UU, U2))
    return w.run()


if __name__ == '__main__':
    if want('tm2stkupv'): tm2stkupv()
    if want('tm2stkupid'): tm2stkupid()
    if want('tm2stkup2'): tm2stkup2()
