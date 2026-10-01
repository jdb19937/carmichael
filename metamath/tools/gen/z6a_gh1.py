"""Z6a (block z6ab): the iterated functional equation of Gamma, z6gamfe."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z6alib import *

DGm = DG
P = lambda x: 'prod_ j e. ( 0 ..^ %s ) ( Z + j )' % x
EQ = lambda x: '( _G ` ( Z + %s ) ) = ( ( _G ` Z ) x. %s )' % (x, P(x))
PH = lambda x: '( Z e. %s -> %s )' % (DGm, EQ(x))


def gamfe():
    w = W('z6gamfe', 'The iterated functional equation of the Gamma function: '
          '` Gamma ( Z + K ) = Gamma ( Z ) prod_ ( j < K ) ( Z + j ) ` ( Lean ` Complex.Gamma_add_one ` '
          'iterated; induction on ` K ` with ~ gamp1 ).')

    def eqv(T):
        a = '( x = %s )' % T
        s1 = w.s([], 'oveq2', '( x = %s -> ( Z + x ) = ( Z + %s ) )' % (T, T))
        s2 = w.s([s1], 'fveq2d', '( x = %s -> ( _G ` ( Z + x ) ) = ( _G ` ( Z + %s ) ) )' % (T, T))
        s3 = w.s([], 'oveq2', '( x = %s -> ( 0 ..^ x ) = ( 0 ..^ %s ) )' % (T, T))
        s4 = w.s([s3], 'prodeq1d', '( x = %s -> %s = %s )' % (T, P('x'), P(T)))
        s5 = w.s([s4], 'oveq2d', '( x = %s -> ( ( _G ` Z ) x. %s ) = ( ( _G ` Z ) x. %s ) )' % (T, P('x'), P(T)))
        s6 = w.s([s2, s5], 'eqeq12d', '( x = %s -> ( %s <-> %s ) )' % (T, EQ('x'), EQ(T)))
        return w.s([s6], 'imbi2d', '( x = %s -> ( %s <-> %s ) )' % (T, PH('x'), PH(T)))
    h1 = eqv('0'); h2 = eqv('y'); h3 = eqv('( y + 1 )'); h4 = eqv('K')
    # base
    A0 = 'Z e. %s' % DG
    zc = w.s([], 'eldifi', '( %s -> Z e. CC )' % A0)
    b1 = w.s([w.s([zc], 'addridd', '( %s -> ( Z + 0 ) = Z )' % A0)], 'fveq2d', '( %s -> ( _G ` ( Z + 0 ) ) = ( _G ` Z ) )' % A0)
    p0 = w.s([w.s([w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'prodeq1i', '%s = prod_ j e. (/) ( Z + j )' % P('0')),
              w.s([], 'prod0', 'prod_ j e. (/) ( Z + j ) = 1')], 'eqtri', '%s = 1' % P('0'))
    gc = w.s([], 'gamcl', '( %s -> ( _G ` Z ) e. CC )' % A0)
    b2 = w.s([w.s([w.s([p0], 'oveq2i', '( ( _G ` Z ) x. %s ) = ( ( _G ` Z ) x. 1 )' % P('0'))], 'a1i',
                  '( %s -> ( ( _G ` Z ) x. %s ) = ( ( _G ` Z ) x. 1 ) )' % (A0, P('0'))),
              w.s([gc], 'mulridd', '( %s -> ( ( _G ` Z ) x. 1 ) = ( _G ` Z ) )' % A0)], 'eqtrd',
             '( %s -> ( ( _G ` Z ) x. %s ) = ( _G ` Z ) )' % (A0, P('0')))
    h5 = w.s([b1, b2], 'eqtr4d', PH('0'))
    # step, under B = ( y e. NN0 /\ Z e. DG )
    B = '( y e. NN0 /\\ Z e. %s )' % DG
    yn = w.s([], 'simpl', '( %s -> y e. NN0 )' % B)
    zd = w.s([], 'simpr', '( %s -> Z e. %s )' % (B, DG))
    zcb = w.s([zd], 'eldifad', '( %s -> Z e. CC )' % B)
    yc = w.s([yn], 'nn0cnd', '( %s -> y e. CC )' % B)
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % B)
    zy = w.s([zd, yn], 'dmgmaddnn0', '( %s -> ( Z + y ) e. %s )' % (B, DG))
    zyc = w.s([zcb, yc], 'addcld', '( %s -> ( Z + y ) e. CC )' % B)
    g1 = w.s([zy, w.inst('gamp1')], 'syl', '( %s -> ( _G ` ( ( Z + y ) + 1 ) ) = ( ( _G ` ( Z + y ) ) x. ( Z + y ) ) )' % B)
    as_ = w.s([zcb, yc, one], 'addassd', '( %s -> ( ( Z + y ) + 1 ) = ( Z + ( y + 1 ) ) )' % B)
    g2 = w.s([w.s([as_], 'fveq2d', '( %s -> ( _G ` ( ( Z + y ) + 1 ) ) = ( _G ` ( Z + ( y + 1 ) ) ) )' % B), g1], 'eqtr3d',
             '( %s -> ( _G ` ( Z + ( y + 1 ) ) ) = ( ( _G ` ( Z + y ) ) x. ( Z + y ) ) )' % B)
    yuz = w.s([yn, w.inst('elnn0uz')], 'sylib', '( %s -> y e. ( ZZ>= ` 0 ) )' % B)
    fz = w.s([yuz, w.inst('fzosplitsn')], 'syl', '( %s -> ( 0 ..^ ( y + 1 ) ) = ( ( 0 ..^ y ) u. { y } ) )' % B)
    pe = w.s([fz], 'prodeq1d', '( %s -> %s = prod_ j e. ( ( 0 ..^ y ) u. { y } ) ( Z + j ) )' % (B, P('( y + 1 )')))
    Bj = '( %s /\\ j e. ( 0 ..^ y ) )' % B
    jc = w.s([w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ y ) )' % Bj), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % Bj)], 'nn0cnd', '( %s -> j e. CC )' % Bj)
    zjc = w.s([w.s([zcb], 'adantr', '( %s -> Z e. CC )' % Bj), jc], 'addcld', '( %s -> ( Z + j ) e. CC )' % Bj)
    fin = w.s([w.s([], 'fzofi', '( 0 ..^ y ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ y ) e. Fin )' % B)
    nel = w.s([w.s([], 'fzonel', '-. y e. ( 0 ..^ y )')], 'a1i', '( %s -> -. y e. ( 0 ..^ y ) )' % B)
    sp = w.s([w.s([], 'nfv', 'F/ j %s' % B), w.s([], 'nfcv', 'F/_ j ( Z + y )'), fin, yn, nel, zjc,
              w.s([], 'oveq2', '( j = y -> ( Z + j ) = ( Z + y ) )'), zyc], 'fprodsplitsn',
             '( %s -> prod_ j e. ( ( 0 ..^ y ) u. { y } ) ( Z + j ) = ( %s x. ( Z + y ) ) )' % (B, P('y')))
    ps = w.s([pe, sp], 'eqtrd', '( %s -> %s = ( %s x. ( Z + y ) ) )' % (B, P('( y + 1 )'), P('y')))
    pyc = w.s([fin, zjc], 'fprodcl', '( %s -> %s e. CC )' % (B, P('y')))
    gcb = w.s([zd, w.inst('gamcl')], 'syl', '( %s -> ( _G ` Z ) e. CC )' % B)
    ma = w.s([gcb, pyc, zyc], 'mulassd', '( %s -> ( ( ( _G ` Z ) x. %s ) x. ( Z + y ) ) = ( ( _G ` Z ) x. ( %s x. ( Z + y ) ) ) )' % (B, P('y'), P('y')))
    rhs = w.s([ma, w.s([ps], 'oveq2d', '( %s -> ( ( _G ` Z ) x. %s ) = ( ( _G ` Z ) x. ( %s x. ( Z + y ) ) ) )' % (B, P('( y + 1 )'), P('y')))], 'eqtr4d',
              '( %s -> ( ( ( _G ` Z ) x. %s ) x. ( Z + y ) ) = ( ( _G ` Z ) x. %s ) )' % (B, P('y'), P('( y + 1 )')))
    A = '( %s /\\ %s )' % (B, EQ('y'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (A, EQ('y')))
    c1 = w.s([ih], 'oveq1d', '( %s -> ( ( _G ` ( Z + y ) ) x. ( Z + y ) ) = ( ( ( _G ` Z ) x. %s ) x. ( Z + y ) ) )' % (A, P('y')))
    c2 = w.s([w.s([g2], 'adantr', '( %s -> ( _G ` ( Z + ( y + 1 ) ) ) = ( ( _G ` ( Z + y ) ) x. ( Z + y ) ) )' % A), c1], 'eqtrd',
             '( %s -> ( _G ` ( Z + ( y + 1 ) ) ) = ( ( ( _G ` Z ) x. %s ) x. ( Z + y ) ) )' % (A, P('y')))
    c3 = w.s([c2, w.s([rhs], 'adantr', '( %s -> ( ( ( _G ` Z ) x. %s ) x. ( Z + y ) ) = ( ( _G ` Z ) x. %s ) )' % (A, P('y'), P('( y + 1 )')))], 'eqtrd',
             '( %s -> %s )' % (A, EQ('( y + 1 )')))
    e1 = w.s([c3], 'ex', '( %s -> ( %s -> %s ) )' % (B, EQ('y'), EQ('( y + 1 )')))
    e2 = w.s([e1], 'ex', '( y e. NN0 -> ( Z e. %s -> ( %s -> %s ) ) )' % (DG, EQ('y'), EQ('( y + 1 )')))
    h6 = w.s([e2], 'a2d', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH('( y + 1 )')))
    ind = w.s([h1, h2, h3, h4, h5, h6], 'nn0ind', '( K e. NN0 -> %s )' % PH('K'))
    w.qed([ind], 'impcom', '( ( Z e. %s /\\ K e. NN0 ) -> %s )' % (DG, EQ('K')))
    assert '( ( Z e. %s /\\ K e. NN0 ) -> %s )' % (DG, EQ('K')) == STATEMENTS['z6gamfe']
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    if 'z6gamfe' in want: gamfe()
