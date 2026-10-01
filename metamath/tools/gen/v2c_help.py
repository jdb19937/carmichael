"""Sortie v2c: general helpers for sums with indicator summands.

ifmulz    ( if ( ph , A , 0 ) x. C ) = if ( ph , ( A x. C ) , 0 )
ifmulz2   ( C x. if ( ph , A , 0 ) ) = if ( ph , ( C x. A ) , 0 )
ifmul2    if ( ( ph /\\ ps ) , ( A x. B ) , 0 ) = ( if ( ph , A , 0 ) x. if ( ps , B , 0 ) )
sumite    sum_ k e. A if ( k = M , B , 0 ) = C
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from c0lib import runh, hyp


def ifmulz():
    w = W('ifmulz', 'A product of an indicator term with a constant on the left.')
    A0 = 'if ( ph , A , 0 )'
    A1 = 'if ( ph , ( A x. C ) , 0 )'
    T = '( C e. CC /\\ ph )'
    F = '( C e. CC /\\ -. ph )'
    pt = w.s([], 'simpr', '( %s -> ph )' % T)
    t1 = w.s([pt], 'iftrued', '( %s -> %s = A )' % (T, A0))
    t2 = w.s([pt], 'iftrued', '( %s -> %s = ( A x. C ) )' % (T, A1))
    ct = w.s([t1], 'oveq1d', '( %s -> ( %s x. C ) = ( A x. C ) )' % (T, A0))
    tt = w.s([ct, w.s([t2], 'eqcomd', '( %s -> ( A x. C ) = %s )' % (T, A1))], 'eqtrd',
             '( %s -> ( %s x. C ) = %s )' % (T, A0, A1))
    pf = w.s([], 'simpr', '( %s -> -. ph )' % F)
    f1 = w.s([pf], 'iffalsed', '( %s -> %s = 0 )' % (F, A0))
    f2 = w.s([pf], 'iffalsed', '( %s -> %s = 0 )' % (F, A1))
    cf = w.s([f1], 'oveq1d', '( %s -> ( %s x. C ) = ( 0 x. C ) )' % (F, A0))
    z = w.s([w.s([], 'simpl', '( %s -> C e. CC )' % F)], 'mul02d',
            '( %s -> ( 0 x. C ) = 0 )' % F)
    ff = w.s([w.s([cf, z], 'eqtrd', '( %s -> ( %s x. C ) = 0 )' % (F, A0)),
              w.s([f2], 'eqcomd', '( %s -> 0 = %s )' % (F, A1))], 'eqtrd',
             '( %s -> ( %s x. C ) = %s )' % (F, A0, A1))
    w.qed([tt, ff], 'pm2.61dan', '( C e. CC -> ( %s x. C ) = %s )' % (A0, A1))
    return w


def ifmulz2():
    w = W('ifmulz2', 'A product of an indicator term with a constant on the right.')
    A0 = 'if ( ph , A , 0 )'
    A1 = 'if ( ph , ( C x. A ) , 0 )'
    T = '( C e. CC /\\ ph )'
    F = '( C e. CC /\\ -. ph )'
    pt = w.s([], 'simpr', '( %s -> ph )' % T)
    t1 = w.s([pt], 'iftrued', '( %s -> %s = A )' % (T, A0))
    t2 = w.s([pt], 'iftrued', '( %s -> %s = ( C x. A ) )' % (T, A1))
    ct = w.s([t1], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. A ) )' % (T, A0))
    tt = w.s([ct, w.s([t2], 'eqcomd', '( %s -> ( C x. A ) = %s )' % (T, A1))], 'eqtrd',
             '( %s -> ( C x. %s ) = %s )' % (T, A0, A1))
    pf = w.s([], 'simpr', '( %s -> -. ph )' % F)
    f1 = w.s([pf], 'iffalsed', '( %s -> %s = 0 )' % (F, A0))
    f2 = w.s([pf], 'iffalsed', '( %s -> %s = 0 )' % (F, A1))
    cf = w.s([f1], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. 0 ) )' % (F, A0))
    z = w.s([w.s([], 'simpl', '( %s -> C e. CC )' % F)], 'mul01d',
            '( %s -> ( C x. 0 ) = 0 )' % F)
    ff = w.s([w.s([cf, z], 'eqtrd', '( %s -> ( C x. %s ) = 0 )' % (F, A0)),
              w.s([f2], 'eqcomd', '( %s -> 0 = %s )' % (F, A1))], 'eqtrd',
             '( %s -> ( C x. %s ) = %s )' % (F, A0, A1))
    w.qed([tt, ff], 'pm2.61dan', '( C e. CC -> ( C x. %s ) = %s )' % (A0, A1))
    return w


def ifmul2():
    w = W('ifmul2', 'An indicator term at a conjunction splits into a product of indicator '
                    'terms.')
    H = '( A e. CC /\\ B e. CC )'
    L0 = 'if ( ( ph /\\ ps ) , ( A x. B ) , 0 )'
    R0 = '( if ( ph , A , 0 ) x. if ( ps , B , 0 ) )'
    TT = '( ( %s /\\ ph ) /\\ ps )' % H
    TF = '( ( %s /\\ ph ) /\\ -. ps )' % H
    FA = '( %s /\\ -. ph )' % H
    # -- ph and ps
    both = w.s([w.s([], 'simplr', '( %s -> ph )' % TT), w.s([], 'simpr', '( %s -> ps )' % TT)],
               'jca', '( %s -> ( ph /\\ ps ) )' % TT)
    l1 = w.s([both], 'iftrued', '( %s -> %s = ( A x. B ) )' % (TT, L0))
    r1 = w.s([w.s([w.s([], 'simplr', '( %s -> ph )' % TT)], 'iftrued',
                  '( %s -> if ( ph , A , 0 ) = A )' % TT),
              w.s([w.s([], 'simpr', '( %s -> ps )' % TT)], 'iftrued',
                  '( %s -> if ( ps , B , 0 ) = B )' % TT)], 'oveq12d',
             '( %s -> %s = ( A x. B ) )' % (TT, R0))
    tt = w.s([l1, w.s([r1], 'eqcomd', '( %s -> ( A x. B ) = %s )' % (TT, R0))], 'eqtrd',
             '( %s -> %s = %s )' % (TT, L0, R0))
    # -- ph and not ps
    nb = w.s([w.s([], 'simpr', '( %s -> -. ps )' % TF)], 'intnand',
             '( %s -> -. ( ph /\\ ps ) )' % TF)
    l2 = w.s([nb], 'iffalsed', '( %s -> %s = 0 )' % (TF, L0))
    r2 = w.s([w.s([w.s([], 'simplr', '( %s -> ph )' % TF)], 'iftrued',
                  '( %s -> if ( ph , A , 0 ) = A )' % TF),
              w.s([w.s([], 'simpr', '( %s -> -. ps )' % TF)], 'iffalsed',
                  '( %s -> if ( ps , B , 0 ) = 0 )' % TF)], 'oveq12d',
             '( %s -> %s = ( A x. 0 ) )' % (TF, R0))
    z2 = w.s([w.s([], 'simplll', '( %s -> A e. CC )' % TF)], 'mul01d',
             '( %s -> ( A x. 0 ) = 0 )' % TF)
    tf = w.s([l2, w.s([w.s([r2, z2], 'eqtrd', '( %s -> %s = 0 )' % (TF, R0))], 'eqcomd',
                      '( %s -> 0 = %s )' % (TF, R0))], 'eqtrd',
             '( %s -> %s = %s )' % (TF, L0, R0))
    ph1 = w.s([tt, tf], 'pm2.61dan',
              '( ( %s /\\ ph ) -> %s = %s )' % (H, L0, R0))
    # -- not ph
    na = w.s([w.s([], 'simpr', '( %s -> -. ph )' % FA)], 'intnanrd',
             '( %s -> -. ( ph /\\ ps ) )' % FA)
    l3 = w.s([na], 'iffalsed', '( %s -> %s = 0 )' % (FA, L0))
    ifb = w.s([w.s([], 'simplr', '( %s -> B e. CC )' % FA),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % FA)], 'ifcld',
              '( %s -> if ( ps , B , 0 ) e. CC )' % FA)
    r3 = w.s([w.s([w.s([], 'simpr', '( %s -> -. ph )' % FA)], 'iffalsed',
                  '( %s -> if ( ph , A , 0 ) = 0 )' % FA)], 'oveq1d',
             '( %s -> %s = ( 0 x. if ( ps , B , 0 ) ) )' % (FA, R0))
    z3 = w.s([ifb], 'mul02d', '( %s -> ( 0 x. if ( ps , B , 0 ) ) = 0 )' % FA)
    fa = w.s([l3, w.s([w.s([r3, z3], 'eqtrd', '( %s -> %s = 0 )' % (FA, R0))], 'eqcomd',
                      '( %s -> 0 = %s )' % (FA, R0))], 'eqtrd',
             '( %s -> %s = %s )' % (FA, L0, R0))
    w.qed([ph1, fa], 'pm2.61dan', '( %s -> %s = %s )' % (H, L0, R0))
    return w


def sumite():
    w = W('sumite', 'A sum over a finite set of an indicator term supported at one point.')
    BODY = 'if ( k = M , B , 0 )'
    h1 = hyp(w, '1', 'sumite.1', '( k = M -> B = C )')
    h2 = hyp(w, '2', 'sumite.2', '( ph -> A e. Fin )')
    h3 = hyp(w, '3', 'sumite.3', '( ph -> M e. A )')
    h4 = hyp(w, '4', 'sumite.4', '( ph -> C e. CC )')
    # -- the substitution hypothesis of sumsn
    idk = w.s([], 'id', '( k = M -> k = M )')
    sub = w.s([w.s([idk], 'iftrued', '( k = M -> %s = B )' % BODY), h1], 'eqtrd',
              '( k = M -> %s = C )' % BODY)
    # -- the value on the singleton
    mex = w.s([h3], 'elexd', '( ph -> M e. _V )')
    inst = w.s([sub], 'sumsn',
               '( ( M e. _V /\\ C e. CC ) -> sum_ k e. { M } %s = C )' % BODY)
    snv = w.s([mex, h4, inst], 'syl2anc', '( ph -> sum_ k e. { M } %s = C )' % BODY)
    # -- the extension to A
    sub2 = w.s([h3], 'snssd', '( ph -> { M } C_ A )')
    AS = '( ph /\\ k e. { M } )'
    keq = w.s([w.s([], 'simpr', '( %s -> k e. { M } )' % AS), w.inst('elsni')], 'syl',
              '( %s -> k = M )' % AS)
    bcc = w.s([w.s([w.s([keq], 'iftrued', '( %s -> %s = B )' % (AS, BODY)),
                    w.s([keq, h1], 'syl', '( %s -> B = C )' % AS)], 'eqtrd',
                   '( %s -> %s = C )' % (AS, BODY)),
               w.s([h4], 'adantr', '( %s -> C e. CC )' % AS)], 'eqeltrd',
              '( %s -> %s e. CC )' % (AS, BODY))
    AD = '( ph /\\ k e. ( A \\ { M } ) )'
    nin = w.s([w.s([], 'simpr', '( %s -> k e. ( A \\ { M } ) )' % AD), w.inst('eldifn')], 'syl',
              '( %s -> -. k e. { M } )' % AD)
    vel = w.s([w.s([], 'velsn', '( k e. { M } <-> k = M )')], 'a1i',
              '( %s -> ( k e. { M } <-> k = M ) )' % AD)
    nk = w.s([nin, vel], 'mtbid', '( %s -> -. k = M )' % AD)
    bz = w.s([nk], 'iffalsed', '( %s -> %s = 0 )' % (AD, BODY))
    ss = w.s([sub2, bcc, bz, h2], 'fsumss',
             '( ph -> sum_ k e. { M } %s = sum_ k e. A %s )' % (BODY, BODY))
    w.qed([w.s([ss], 'eqcomd', '( ph -> sum_ k e. A %s = sum_ k e. { M } %s )' % (BODY, BODY)),
           snv], 'eqtrd', '( ph -> sum_ k e. A %s = C )' % BODY)
    return w



def ifabs():
    w = W('ifabs', 'The absolute value of an indicator term.')
    A0 = 'if ( ph , A , 0 )'
    A1 = 'if ( ph , ( abs ` A ) , 0 )'
    t1 = w.s([w.s([], 'id', '( ph -> ph )')], 'iftrued', '( ph -> %s = A )' % A0)
    t2 = w.s([w.s([], 'id', '( ph -> ph )')], 'iftrued', '( ph -> %s = ( abs ` A ) )' % A1)
    tt = w.s([w.s([t1], 'fveq2d', '( ph -> ( abs ` %s ) = ( abs ` A ) )' % A0),
              w.s([t2], 'eqcomd', '( ph -> ( abs ` A ) = %s )' % A1)], 'eqtrd',
             '( ph -> ( abs ` %s ) = %s )' % (A0, A1))
    f1 = w.s([w.s([], 'id', '( -. ph -> -. ph )')], 'iffalsed', '( -. ph -> %s = 0 )' % A0)
    f2 = w.s([w.s([], 'id', '( -. ph -> -. ph )')], 'iffalsed', '( -. ph -> %s = 0 )' % A1)
    z = w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( -. ph -> ( abs ` 0 ) = 0 )')
    ff = w.s([w.s([w.s([f1], 'fveq2d', '( -. ph -> ( abs ` %s ) = ( abs ` 0 ) )' % A0), z],
                  'eqtrd', '( -. ph -> ( abs ` %s ) = 0 )' % A0),
              w.s([f2], 'eqcomd', '( -. ph -> 0 = %s )' % A1)], 'eqtrd',
             '( -. ph -> ( abs ` %s ) = %s )' % (A0, A1))
    w.qed([tt, ff], 'pm2.61i', '( abs ` %s ) = %s' % (A0, A1))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['ifmulz', 'ifmulz2', 'ifmul2']:
        wk = globals()[f]()
        (runh(wk) if f in ('sumite',) else wk.run())
