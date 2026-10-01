"""Sortie TP: Lean newton_telescope (tptelq: one step; tptel: the telescoping sum of the Newton basis)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *
import mvlib
import cl as _cl

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


QA = '( ( A e. CC /\\ B e. CC /\\ B =/= 0 ) /\\ ( X e. CC /\\ Z e. CC ) /\\ ( C e. CC /\\ ( Z - C ) =/= 0 ) )'
DD = '( B x. ( Z - C ) )'
S['tptelq'] = '( %s -> ( ( A / B ) - ( ( A x. ( X - C ) ) / %s ) ) = ( ( Z - X ) x. ( A / %s ) ) )' % (QA, DD, DD)


def gen_telq():
    w = W('tptelq', 'One step of Lean ` newton_telescope ` : ` A / B - A ( X - C ) / ( B ( Z - C ) ) = ( Z - X ) A / ( B ( Z - C ) ) ` .')
    A0 = QA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( A e. CC /\\ B e. CC /\\ B =/= 0 )'); t2 = s([], 'simp2', '( X e. CC /\\ Z e. CC )'); t3 = s([], 'simp3', '( C e. CC /\\ ( Z - C ) =/= 0 )')
    c = Closure(w, A0, {'A': ('CC', s([t1], 'simp1d', 'A e. CC')), 'B': ('CC', s([t1], 'simp2d', 'B e. CC')),
                        'X': ('CC', s([t2], 'simpld', 'X e. CC')), 'Z': ('CC', s([t2], 'simprd', 'Z e. CC')), 'C': ('CC', s([t3], 'simpld', 'C e. CC'))})
    c.have('B', 'ne0', s([t1], 'simp3d', 'B =/= 0'))
    c.have('( Z - C )', 'ne0', s([t3], 'simprd', '( Z - C ) =/= 0'))
    c.have(DD, 'ne0', ap(w, A0, 'mulne0d', '%s =/= 0' % DD, c))
    e1 = ap(w, A0, 'divcan5rd', '( ( A x. ( Z - C ) ) / %s ) = ( A / B )' % DD, c)
    e2 = ap(w, A0, 'divsubdird', '( ( ( A x. ( Z - C ) ) - ( A x. ( X - C ) ) ) / %s ) = ( ( ( A x. ( Z - C ) ) / %s ) - ( ( A x. ( X - C ) ) / %s ) )' % (DD, DD, DD), c)
    e3 = s([e1], 'oveq1d', '( ( ( A x. ( Z - C ) ) / %s ) - ( ( A x. ( X - C ) ) / %s ) ) = ( ( A / B ) - ( ( A x. ( X - C ) ) / %s ) )' % (DD, DD, DD))
    e4 = s([mvlib.ringeq(w, A0, '( ( A x. ( Z - C ) ) - ( A x. ( X - C ) ) )', '( ( Z - X ) x. A )', c)], 'oveq1d',
           '( ( ( A x. ( Z - C ) ) - ( A x. ( X - C ) ) ) / %s ) = ( ( ( Z - X ) x. A ) / %s )' % (DD, DD))
    e5 = ap(w, A0, 'divassd', '( ( ( Z - X ) x. A ) / %s ) = ( ( Z - X ) x. ( A / %s ) )' % (DD, DD), c)
    x1 = s([e2, e3], 'eqtrd', '( ( ( A x. ( Z - C ) ) - ( A x. ( X - C ) ) ) / %s ) = ( ( A / B ) - ( ( A x. ( X - C ) ) / %s ) )' % (DD, DD))
    x2 = s([e4, e5], 'eqtrd', '( ( ( A x. ( Z - C ) ) - ( A x. ( X - C ) ) ) / %s ) = ( ( Z - X ) x. ( A / %s ) )' % (DD, DD))
    w.qed([x1, x2], 'eqtr3d', S['tptelq'])
    return run(w)


VB = {'X': 'h', 'Z': 'g'}


def OM(x, n, h=None):
    """the Newton basis prod_ ( h < n ) ( x - V_h ); the X-products bind h, the Z-products bind g"""
    h = h or VB.get(x, 'h')
    return 'prod_ %s e. ( 0 ..^ %s ) ( %s - ( V ` %s ) )' % (h, n, x, h)


TA = '( ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( X e. CC /\\ Z e. CC /\\ Z =/= X ) /\\ A. y e. ( 0 ..^ N ) Z =/= ( V ` y ) )'
TSUM = 'sum_ i e. ( 0 ..^ N ) ( %s / %s )' % (OM('X', 'i'), OM('Z', '( i + 1 )'))
S['tptel'] = '( %s -> %s = ( ( 1 - ( %s / %s ) ) / ( Z - X ) ) )' % (TA, TSUM, OM('X', 'N'), OM('Z', 'N'))


def gen_tel():
    w = W('tptel', 'Lean ` newton_telescope ` : ` sum_ ( i < N ) prod_ ( h < i ) ( X - v_h ) / prod_ ( h <_ i ) ( Z - v_h ) = '
               '( 1 - prod_ ( h < N ) ( X - v_h ) / prod_ ( h < N ) ( Z - v_h ) ) / ( Z - X ) ` .')
    A0 = TA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )'); t2 = s([], 'simp2', '( X e. CC /\\ Z e. CC /\\ Z =/= X )')
    t3 = s([], 'simp3', 'A. y e. ( 0 ..^ N ) Z =/= ( V ` y )')
    nn = s([t1], 'simpld', 'N e. NN0'); vf = s([t1], 'simprd', 'V : ( 0 ..^ N ) --> CC')
    xc = s([t2], 'simp1d', 'X e. CC'); zc = s([t2], 'simp2d', 'Z e. CC'); zx = s([t2], 'simp3d', 'Z =/= X')
    c = Closure(w, A0, {'N': ('NN0', nn), 'X': ('CC', xc), 'Z': ('CC', zc)})
    # facts about a node index hv of a context K with ( K -> hv e. ( 0 ..^ N ) )
    def nodefacts(K, hin, ck, hv):
        vh = w.s([_cl.lift(w, vf, K), hin], 'ffvelcdmd', '( %s -> ( V ` %s ) e. CC )' % (K, hv))
        ck.have('( V ` %s )' % hv, 'CC', vh); ck.atom('( V ` %s )' % hv)
        idyh = w.s([], 'id', '( y = %s -> y = %s )' % (hv, hv))
        cg, nw = w.wcongr('Z =/= ( V ` y )', {'y': hv}, 'y = %s' % hv, {'y': idyh})
        r = w.s([cg], 'rspcv', '( %s e. ( 0 ..^ N ) -> ( A. y e. ( 0 ..^ N ) Z =/= ( V ` y ) -> %s ) )' % (hv, nw))
        ne = w.s([hin, _cl.lift(w, t3, K), r], 'sylc', '( %s -> Z =/= ( V ` %s ) )' % (K, hv))
        ck.have('( Z - ( V ` %s ) )' % hv, 'ne0', ap(w, K, 'subne0d', '( Z - ( V ` %s ) ) =/= 0' % hv, ck, facts=[ne]))
        return vh
    # products over ( 0 ..^ k ) with k <_ N are complex, and the Z-product is nonzero
    def prodfacts(K, kuz, ck, k):
        """kuz: ( K -> N e. ( ZZ>= ` k ) ) for the product length k"""
        sub = w.s([kuz, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ %s ) C_ ( 0 ..^ N ) )' % (K, k))
        fz = w.s([w.s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % k)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (K, k))
        for x in ('X', 'Z'):
            hv = VB[x]
            Kh = '( %s /\\ %s e. ( 0 ..^ %s ) )' % (K, hv, k)
            ch = Closure(w, Kh, {'X': ('CC', _cl.lift(w, xc, Kh)), 'Z': ('CC', _cl.lift(w, zc, Kh))})
            hin = w.s([_cl.lift(w, sub, Kh), w.s([], 'simpr', '( %s -> %s e. ( 0 ..^ %s ) )' % (Kh, hv, k))], 'sseldd', '( %s -> %s e. ( 0 ..^ N ) )' % (Kh, hv))
            nodefacts(Kh, hin, ch, hv)
            fac = '( %s - ( V ` %s ) )' % (x, hv)
            px = w.s([fz, ch.mem(fac, 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (K, OM(x, k)))
            ck.have(OM(x, k), 'CC', px); ck.atom(OM(x, k))
            if x == 'Z':
                pn = w.s([fz, ch.mem(fac, 'CC'), ch.ne0(fac)], 'fprodn0', '( %s -> %s =/= 0 )' % (K, OM(x, k)))
                ck.have(OM(x, k), 'ne0', pn)
    U = lambda k: '( %s / %s )' % (OM('X', k), OM('Z', k))
    # telescoping over k e. ( 0 ... N )
    Ak = '( %s /\\ k e. ( 0 ... N ) )' % A0
    ck = Closure(w, Ak, {'X': ('CC', _cl.lift(w, xc, Ak)), 'Z': ('CC', _cl.lift(w, zc, Ak))})
    kuz = w.s([w.s([], 'simpr', '( %s -> k e. ( 0 ... N ) )' % Ak), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` k ) )' % Ak)
    prodfacts(Ak, kuz, ck, 'k')
    ukc = ck.mem(U('k'), 'CC')
    def cg(val):
        idk = w.s([], 'id', '( k = %s -> k = %s )' % (val, val))
        st, nw = w.congr(U('k'), {'k': val}, 'k = %s' % val, {'k': idk})
        assert nw == U(val), nw
        return st
    nuz = s([nn, w.inst('elnn0uz')], 'sylib', 'N e. ( ZZ>= ` 0 )')
    tel = s([cg('i'), cg('( i + 1 )'), cg('0'), cg('N'), nuz, ukc], 'telfsumo',
            'sum_ i e. ( 0 ..^ N ) ( %s - %s ) = ( %s - %s )' % (U('i'), U('( i + 1 )'), U('0'), U('N')))
    # U(0) = 1
    p0x = w.s([w.s([w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'prodeq1i', '%s = prod_ h e. (/) ( X - ( V ` h ) )' % OM('X', '0')),
               w.s([], 'prod0', 'prod_ h e. (/) ( X - ( V ` h ) ) = 1')], 'eqtri', '%s = 1' % OM('X', '0'))
    p0z = w.s([w.s([w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'prodeq1i', '%s = prod_ g e. (/) ( Z - ( V ` g ) )' % OM('Z', '0')),
               w.s([], 'prod0', 'prod_ g e. (/) ( Z - ( V ` g ) ) = 1')], 'eqtri', '%s = 1' % OM('Z', '0'))
    u0 = w.s([w.s([p0x, p0z], 'oveq12i', '%s = ( 1 / 1 )' % U('0')), w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'eqtri', '%s = 1' % U('0'))
    tel = s([tel, s([s([u0], 'a1i', '%s = 1' % U('0'))], 'oveq1d', '( %s - %s ) = ( 1 - %s )' % (U('0'), U('N'), U('N')))], 'eqtrd',
            'sum_ i e. ( 0 ..^ N ) ( %s - %s ) = ( 1 - %s )' % (U('i'), U('( i + 1 )'), U('N')))
    # each term
    Ai = '( %s /\\ i e. ( 0 ..^ N ) )' % A0
    ci = Closure(w, Ai, {'X': ('CC', _cl.lift(w, xc, Ai)), 'Z': ('CC', _cl.lift(w, zc, Ai))})
    iin = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai)
    ci.have('i', 'NN0', w.s([iin, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai))
    iuz = w.s([w.s([iin, w.inst('fzofzp1')], 'syl', '( %s -> ( i + 1 ) e. ( 0 ... N ) )' % Ai), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` ( i + 1 ) ) )' % Ai)
    iuz0 = w.s([w.s([iin, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... N ) )' % Ai), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` i ) )' % Ai)
    prodfacts(Ai, iuz, ci, '( i + 1 )')
    prodfacts(Ai, iuz0, ci, 'i')
    # V_i facts
    Vi = '( V ` i )'
    nodes_i = w.s([_cl.lift(w, vf, Ai), iin], 'ffvelcdmd', '( %s -> %s e. CC )' % (Ai, Vi))
    ci.have(Vi, 'CC', nodes_i); ci.atom(Vi)
    idyi = w.s([], 'id', '( y = i -> y = i )')
    cgi, nwi = w.wcongr('Z =/= ( V ` y )', {'y': 'i'}, 'y = i', {'y': idyi})
    zvi = w.s([iin, _cl.lift(w, t3, Ai), w.s([cgi], 'rspcv', '( i e. ( 0 ..^ N ) -> ( A. y e. ( 0 ..^ N ) Z =/= ( V ` y ) -> %s ) )' % nwi)], 'sylc', '( %s -> %s )' % (Ai, nwi))
    ci.have('( Z - %s )' % Vi, 'ne0', ap(w, Ai, 'subne0d', '( Z - %s ) =/= 0' % Vi, ci, facts=[zvi]))
    # split the ( i + 1 ) products
    spl = w.s([w.s([ci.mem('i', 'NN0'), w.inst('elnn0uz')], 'sylib', '( %s -> i e. ( ZZ>= ` 0 ) )' % Ai), w.inst('fzosplitsn')], 'syl',
              '( %s -> ( 0 ..^ ( i + 1 ) ) = ( ( 0 ..^ i ) u. { i } ) )' % Ai)
    def split(x):
        hv = VB[x]
        e1 = w.s([spl], 'prodeq1d', '( %s -> %s = prod_ %s e. ( ( 0 ..^ i ) u. { i } ) ( %s - ( V ` %s ) ) )' % (Ai, OM(x, '( i + 1 )'), hv, x, hv))
        idhi = w.s([], 'id', '( %s = i -> %s = i )' % (hv, hv))
        cgh, nh = w.congr('( %s - ( V ` %s ) )' % (x, hv), {hv: 'i'}, '%s = i' % hv, {hv: idhi})
        Aih = '( %s /\\ %s e. ( 0 ..^ i ) )' % (Ai, hv)
        ch = Closure(w, Aih, {x: ('CC', _cl.lift(w, xc if x == 'X' else zc, Aih))})
        sub = w.s([iuz0, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ i ) C_ ( 0 ..^ N ) )' % Ai)
        hin = w.s([_cl.lift(w, sub, Aih), w.s([], 'simpr', '( %s -> %s e. ( 0 ..^ i ) )' % (Aih, hv))], 'sseldd', '( %s -> %s e. ( 0 ..^ N ) )' % (Aih, hv))
        vh = w.s([_cl.lift(w, vf, Aih), hin], 'ffvelcdmd', '( %s -> ( V ` %s ) e. CC )' % (Aih, hv))
        ch.have('( V ` %s )' % hv, 'CC', vh); ch.atom('( V ` %s )' % hv)
        e2 = w.s([w.s([], 'nfv', 'F/ %s %s' % (hv, Ai)), w.s([], 'nfcv', 'F/_ %s ( %s - %s )' % (hv, x, Vi)),
                  w.s([w.s([], 'fzofi', '( 0 ..^ i ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ i ) e. Fin )' % Ai), ci.mem('i', 'NN0'),
                  w.s([w.s([], 'fzonel', '-. i e. ( 0 ..^ i )')], 'a1i', '( %s -> -. i e. ( 0 ..^ i ) )' % Ai), ch.mem('( %s - ( V ` %s ) )' % (x, hv), 'CC'), cgh,
                  ci.mem('( %s - %s )' % (x, Vi), 'CC')], 'fprodsplitsn',
                 '( %s -> prod_ %s e. ( ( 0 ..^ i ) u. { i } ) ( %s - ( V ` %s ) ) = ( %s x. ( %s - %s ) ) )' % (Ai, hv, x, hv, OM(x, 'i'), x, Vi))
        return w.s([e1, e2], 'eqtrd', '( %s -> %s = ( %s x. ( %s - %s ) ) )' % (Ai, OM(x, '( i + 1 )'), OM(x, 'i'), x, Vi))
    sx = split('X'); sz = split('Z')
    ui1 = w.s([sx, sz], 'oveq12d', '( %s -> %s = ( ( %s x. ( X - %s ) ) / ( %s x. ( Z - %s ) ) ) )' % (Ai, U('( i + 1 )'), OM('X', 'i'), Vi, OM('Z', 'i'), Vi))
    d1 = w.s([ui1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - ( ( %s x. ( X - %s ) ) / ( %s x. ( Z - %s ) ) ) ) )'
             % (Ai, U('i'), U('( i + 1 )'), U('i'), OM('X', 'i'), Vi, OM('Z', 'i'), Vi))
    q = apc(w, Ai, 'tptelq', '( %s - ( ( %s x. ( X - %s ) ) / ( %s x. ( Z - %s ) ) ) ) = ( ( Z - X ) x. ( %s / ( %s x. ( Z - %s ) ) ) )'
            % (U('i'), OM('X', 'i'), Vi, OM('Z', 'i'), Vi, OM('X', 'i'), OM('Z', 'i'), Vi), ci)
    d2 = w.s([sz], 'oveq2d', '( %s -> ( %s / %s ) = ( %s / ( %s x. ( Z - %s ) ) ) )' % (Ai, OM('X', 'i'), OM('Z', '( i + 1 )'), OM('X', 'i'), OM('Z', 'i'), Vi))
    d3 = w.s([d2], 'oveq2d', '( %s -> ( ( Z - X ) x. ( %s / %s ) ) = ( ( Z - X ) x. ( %s / ( %s x. ( Z - %s ) ) ) ) )'
             % (Ai, OM('X', 'i'), OM('Z', '( i + 1 )'), OM('X', 'i'), OM('Z', 'i'), Vi))
    T = '( %s / %s )' % (OM('X', 'i'), OM('Z', '( i + 1 )'))
    termeq = w.s([w.s([d1, q], 'eqtrd', '( %s -> ( %s - %s ) = ( ( Z - X ) x. ( %s / ( %s x. ( Z - %s ) ) ) ) )' % (Ai, U('i'), U('( i + 1 )'), OM('X', 'i'), OM('Z', 'i'), Vi)), d3],
                 'eqtr4d', '( %s -> ( %s - %s ) = ( ( Z - X ) x. %s ) )' % (Ai, U('i'), U('( i + 1 )'), T))
    se = s([termeq], 'sumeq2dv', 'sum_ i e. ( 0 ..^ N ) ( %s - %s ) = sum_ i e. ( 0 ..^ N ) ( ( Z - X ) x. %s )' % (U('i'), U('( i + 1 )'), T))
    fz = s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    mc = s([fz, c.mem('( Z - X )', 'CC'), ci.mem(T, 'CC')], 'fsummulc2', '( ( Z - X ) x. %s ) = sum_ i e. ( 0 ..^ N ) ( ( Z - X ) x. %s )' % (TSUM, T))
    tot = s([mc, s([se, tel], 'eqtr3d', 'sum_ i e. ( 0 ..^ N ) ( ( Z - X ) x. %s ) = ( 1 - %s )' % (T, U('N')))], 'eqtrd', '( ( Z - X ) x. %s ) = ( 1 - %s )' % (TSUM, U('N')))
    c.have('( Z - X )', 'ne0', ap(w, A0, 'subne0d', '( Z - X ) =/= 0', c, facts=[zx]))
    c.have(TSUM, 'CC', s([fz, ci.mem(T, 'CC')], 'fsumcl', '%s e. CC' % TSUM)); c.atom(TSUM)
    w.qed([c.mem('( Z - X )', 'CC'), c.mem(TSUM, 'CC'), c.ne0('( Z - X )'), tot], 'mvllmuld', S['tptel'])
    return run(w)


if __name__ == '__main__':
    gen_telq()
    gen_tel()
