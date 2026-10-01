"""Sortie TP: the power-sum functional on the Newton basis (tplam: ` abs sum_j v_j ^ ( M + 1 ) prod_( h < i ) ( v_j - v_h ) <_ 2 ^ i C `
when every window power sum is at most C in modulus and every node has modulus <_ 1; replaces Lean's l1 chain)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift, WIN
import cl as _cl
import ef2lib as E
import mvlib

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


PSQ = lambda k: 'sum_ q e. ( 0 ..^ N ) ( ( V ` q ) ^ %s )' % k
WINH = 'A. k e. %s ( abs ` %s ) <_ C' % (WIN(), PSQ('k'))
EXP = lambda t: '( ( M + 1 ) + %s )' % t
OMJ = lambda x: 'prod_ h e. ( 0 ..^ %s ) ( ( V ` j ) - ( V ` h ) )' % x
SL = lambda x, t: 'sum_ j e. ( 0 ..^ N ) ( ( ( V ` j ) ^ %s ) x. %s )' % (EXP(t), OMJ(x))
BODY = lambda x, s: '( ( %s + %s ) < N -> ( abs ` %s ) <_ ( ( 2 ^ %s ) x. C ) )' % (x, s, SL(x, s), x)
PS = lambda x: 'A. s e. NN0 %s' % BODY(x, 's')
LA = ('( ( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 /\\ ( C e. RR /\\ %s ) ) )' % WINH)
OUT = 'A. i e. ( 0 ..^ N ) ( abs ` sum_ j e. ( 0 ..^ N ) ( ( ( V ` j ) ^ ( M + 1 ) ) x. %s ) ) <_ ( ( 2 ^ i ) x. C )' % OMJ('i')
S['tplam'] = '( %s -> %s )' % (LA, OUT)


def gen_lam():
    w = W('tplam', 'The window power sums control the Newton basis: if every node has modulus <_ 1 and every power sum with exponent in '
               '` [ M + 1 , M + N ] ` has modulus <_ C , then ` abs sum_j v_j ^ ( M + 1 ) prod_( h < i ) ( v_j - v_h ) <_ 2 ^ i C ` for ` i < N ` '
               '(induction on i with the exponent shift; replaces Lean ` l1 ` , ` l1_mul_le ` , ` l1_prod_X_sub_C_le ` ).')
    A0 = LA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simpl', '( N e. NN /\\ M e. NN0 /\\ V : ( 0 ..^ N ) --> CC )')
    t2 = s([], 'simpr', '( A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 /\\ ( C e. RR /\\ %s ) )' % WINH)
    nn = s([t1], 'simp1d', 'N e. NN'); mm = s([t1], 'simp2d', 'M e. NN0'); vf = s([t1], 'simp3d', 'V : ( 0 ..^ N ) --> CC')
    vb = s([t2], 'simpld', 'A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1')
    cw = s([t2], 'simprd', '( C e. RR /\\ %s )' % WINH)
    cr = s([cw], 'simpld', 'C e. RR'); wh = s([cw], 'simprd', WINH)
    c = Closure(w, A0, {'N': ('NN', nn), 'M': ('NN0', mm), 'C': ('RR', cr)})
    # window membership of ( M + 1 ) + t for t < N, and the bound there
    def inwin(K, tv, tlt, ck):
        """( K -> ( abs ` PSQ ( EXP ( tv ) ) ) <_ C ), given tlt: ( K -> tv < N ) and ck knowing tv NN0"""
        tz = ck.mem(tv, 'NN0')
        lo = lin.linarith(w, K, [ck.ge0(tv)], '( M + 1 ) <_ %s' % EXP(tv), closure=ck)
        # integer step: tv < N gives tv + 1 <_ N
        t1le = w.s([ck.mem(tv, 'ZZ'), ck.mem('N', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < N <-> ( %s + 1 ) <_ N ) )' % (K, tv, tv))
        t1l = w.s([tlt, t1le], 'mpbid', '( %s -> ( %s + 1 ) <_ N )' % (K, tv))
        hi = lin.linarith(w, K, [t1l], '%s <_ ( M + N )' % EXP(tv), closure=ck)
        ew = w.s([ck.mem('( M + 1 )', 'ZZ'), ck.mem('( M + N )', 'ZZ'), ck.mem(EXP(tv), 'ZZ'), lo, hi], 'elfzd', '( %s -> %s e. %s )' % (K, EXP(tv), WIN()))
        idk = w.s([], 'id', '( k = %s -> k = %s )' % (EXP(tv), EXP(tv)))
        cg, nw = w.wcongr('( abs ` %s ) <_ C' % PSQ('k'), {'k': EXP(tv)}, 'k = %s' % EXP(tv), {'k': idk})
        return w.s([ew, _cl.lift(w, wh, K), w.s([cg], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (EXP(tv), WIN(), WINH, nw))], 'sylc', '( %s -> %s )' % (K, nw))
    # C >_ 0
    c.have('0', 'NN0', s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'))
    b0 = inwin(A0, '0', s([nn], 'nngt0d', '0 < N'), c)
    ps0c = s([s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin'),
              w.s([w.s([_cl.lift(w, vf, '( %s /\\ q e. ( 0 ..^ N ) )' % A0), w.s([], 'simpr', '( ( %s /\\ q e. ( 0 ..^ N ) ) -> q e. ( 0 ..^ N ) )' % A0)], 'ffvelcdmd',
                        '( ( %s /\\ q e. ( 0 ..^ N ) ) -> ( V ` q ) e. CC )' % A0),
                   _cl.lift(w, c.mem(EXP('0'), 'NN0'), '( %s /\\ q e. ( 0 ..^ N ) )' % A0)], 'expcld', '( ( %s /\\ q e. ( 0 ..^ N ) ) -> ( ( V ` q ) ^ %s ) e. CC )' % (A0, EXP('0')))],
             'fsumcl', '%s e. CC' % PSQ(EXP('0')))
    c0 = s([s([ps0c], 'absge0d', '0 <_ ( abs ` %s )' % PSQ(EXP('0'))), b0], 'letrd', '0 <_ C')
    c.have('C', 'ge0', c0)
    # nn0indd substitutions
    def sub(val):
        idst = w.s([], 'id', '( x = %s -> x = %s )' % (val, val))
        st, new = w.wcongr(PS('x'), {'x': val}, 'x = %s' % val, {'x': idst})
        assert new == PS(val), (new, PS(val))
        return st
    hx0 = sub('0'); hxy = sub('y'); hxy1 = sub('( y + 1 )'); hxi = sub('i')
    # ---- base
    Ab = '( %s /\\ s e. NN0 )' % A0
    Ab2 = '( %s /\\ ( 0 + s ) < N )' % Ab
    cb = Closure(w, Ab2, {'N': ('NN', _cl.lift(w, nn, Ab2)), 'M': ('NN0', _cl.lift(w, mm, Ab2)), 'C': ('RR', _cl.lift(w, cr, Ab2)),
                          's': ('NN0', _cl.lift(w, w.s([], 'simpr', '( %s -> s e. NN0 )' % Ab), Ab2))})
    cb.have('C', 'ge0', _cl.lift(w, c0, Ab2))
    slt = lin.linarith(w, Ab2, [w.s([], 'simpr', '( %s -> ( 0 + s ) < N )' % Ab2)], 's < N', closure=cb)
    bw = inwin(Ab2, 's', slt, cb)
    Abj = '( %s /\\ j e. ( 0 ..^ N ) )' % Ab2
    p0 = w.s([w.s([w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'prodeq1i', '%s = prod_ h e. (/) ( ( V ` j ) - ( V ` h ) )' % OMJ('0')),
              w.s([], 'prod0', 'prod_ h e. (/) ( ( V ` j ) - ( V ` h ) ) = 1')], 'eqtri', '%s = 1' % OMJ('0'))
    vj = w.s([_cl.lift(w, vf, Abj), w.s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % Abj)], 'ffvelcdmd', '( %s -> ( V ` j ) e. CC )' % Abj)
    cbj = Closure(w, Abj, {'( V ` j )': ('CC', vj), 'M': ('NN0', _cl.lift(w, mm, Abj)), 's': ('NN0', _cl.lift(w, cb.mem('s', 'NN0'), Abj))}); cbj.atom('( V ` j )')
    VE = '( ( V ` j ) ^ %s )' % EXP('s')
    pb = w.s([w.s([w.s([p0], 'a1i', '( %s -> %s = 1 )' % (Abj, OMJ('0')))], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. 1 ) )' % (Abj, VE, OMJ('0'), VE)),
              ap(w, Abj, 'mulridd', '( %s x. 1 ) = %s' % (VE, VE), cbj)], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (Abj, VE, OMJ('0'), VE))
    sb = w.s([pb], 'sumeq2dv', '( %s -> %s = sum_ j e. ( 0 ..^ N ) %s )' % (Ab2, SL('0', 's'), VE))
    # rename the power sum's index to q
    idjq = w.s([], 'id', '( j = q -> j = q )')
    cjq, _ = w.congr(VE, {'j': 'q'}, 'j = q', {'j': idjq})
    cbs = w.s([cjq], 'cbvsumv', 'sum_ j e. ( 0 ..^ N ) %s = %s' % (VE, PSQ(EXP('s'))))
    sb2 = w.s([sb, w.s([cbs], 'a1i', '( %s -> sum_ j e. ( 0 ..^ N ) %s = %s )' % (Ab2, VE, PSQ(EXP('s'))))], 'eqtrd', '( %s -> %s = %s )' % (Ab2, SL('0', 's'), PSQ(EXP('s'))))
    ab0 = w.s([w.s([sb2], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (Ab2, SL('0', 's'), PSQ(EXP('s')))), bw], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ C )' % (Ab2, SL('0', 's')))
    e0 = w.s([w.s([w.s([cb.mem('2', 'CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % Ab2)], 'oveq1d', '( %s -> ( ( 2 ^ 0 ) x. C ) = ( 1 x. C ) )' % Ab2),
              ap(w, Ab2, 'mullidd', '( 1 x. C ) = C', cb)], 'eqtrd', '( %s -> ( ( 2 ^ 0 ) x. C ) = C )' % Ab2)
    ab1 = w.s([ab0, e0], 'breqtrrd', '( %s -> ( abs ` %s ) <_ ( ( 2 ^ 0 ) x. C ) )' % (Ab2, SL('0', 's')))
    base = s([w.s([ab1], 'ex', '( %s -> %s )' % (Ab, BODY('0', 's')))], 'ralrimiva', PS('0'))
    # ---- step: algebra without the induction hypothesis
    H = '( ( ( %s /\\ y e. NN0 ) /\\ t e. NN0 ) /\\ ( ( y + 1 ) + t ) < N )' % A0
    gh = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (H, f))
    LH = lambda st: _cl.lift(w, st, H)
    ch = Closure(w, H, {'N': ('NN', LH(nn)), 'M': ('NN0', LH(mm)), 'C': ('RR', LH(cr)),
                        'y': ('NN0', LH(w.s([], 'simpr', '( ( %s /\\ y e. NN0 ) -> y e. NN0 )' % A0))),
                        't': ('NN0', LH(w.s([], 'simpr', '( ( ( %s /\\ y e. NN0 ) /\\ t e. NN0 ) -> t e. NN0 )' % A0)))})
    ch.have('C', 'ge0', LH(c0))
    hlt = w.s([], 'simpr', '( %s -> ( ( y + 1 ) + t ) < N )' % H)
    ylt = lin.linarith(w, H, [hlt, ch.ge0('t')], 'y < N', closure=ch)
    yin = gh([gh([ch.mem('y', 'NN0'), ch.mem('N', 'NN'), ylt], '3jca', '( y e. NN0 /\\ N e. NN /\\ y < N )'), w.inst('elfzo0')], 'sylibr', 'y e. ( 0 ..^ N )')
    vy = gh([LH(vf), yin], 'ffvelcdmd', '( V ` y ) e. CC')
    ch.have('( V ` y )', 'CC', vy); ch.atom('( V ` y )')
    y1le = lin.linarith(w, H, [hlt, ch.ge0('t')], '( y + 1 ) <_ N', closure=ch)
    y1uz = gh([gh([ch.mem('( y + 1 )', 'ZZ'), ch.mem('N', 'ZZ'), y1le], '3jca', '( ( y + 1 ) e. ZZ /\\ N e. ZZ /\\ ( y + 1 ) <_ N )'), w.inst('eluz2')], 'sylibr', 'N e. ( ZZ>= ` ( y + 1 ) )')
    sub1 = gh([y1uz, w.inst('fzoss2')], 'syl', '( 0 ..^ ( y + 1 ) ) C_ ( 0 ..^ N )')
    subY = gh([gh([ch.mem('y', 'NN0'), w.inst('fzossfzop1')], 'syl', '( 0 ..^ y ) C_ ( 0 ..^ ( y + 1 ) )'), sub1], 'sstrd', '( 0 ..^ y ) C_ ( 0 ..^ N )')
    Hj = '( %s /\\ j e. ( 0 ..^ N ) )' % H
    gj = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Hj, f))
    Lj = lambda st: _cl.lift(w, st, Hj)
    vjj = gj([Lj(LH(vf)), w.s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % Hj)], 'ffvelcdmd', '( V ` j ) e. CC')
    cj = Closure(w, Hj, {'( V ` j )': ('CC', vjj), '( V ` y )': ('CC', Lj(vy)), 'M': ('NN0', Lj(LH(mm))), 't': ('NN0', Lj(ch.mem('t', 'NN0'))), 'y': ('NN0', Lj(ch.mem('y', 'NN0')))})
    cj.atom('( V ` j )'); cj.atom('( V ` y )')
    Hjh = '( %s /\\ h e. ( 0 ..^ y ) )' % Hj
    vhh = w.s([_cl.lift(w, LH(vf), Hjh), w.s([_cl.lift(w, subY, Hjh), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ y ) )' % Hjh)], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % Hjh)],
              'ffvelcdmd', '( %s -> ( V ` h ) e. CC )' % Hjh)
    cjh = Closure(w, Hjh, {'( V ` j )': ('CC', _cl.lift(w, vjj, Hjh)), '( V ` h )': ('CC', vhh)}); cjh.atom('( V ` j )'); cjh.atom('( V ` h )')
    fy = gj([w.s([], 'fzofi', '( 0 ..^ y ) e. Fin')], 'a1i', '( 0 ..^ y ) e. Fin')
    omc = gj([fy, cjh.mem('( ( V ` j ) - ( V ` h ) )', 'CC')], 'fprodcl', '%s e. CC' % OMJ('y'))
    cj.have(OMJ('y'), 'CC', omc); cj.atom(OMJ('y'))
    spl = gj([gj([cj.mem('y', 'NN0'), w.inst('elnn0uz')], 'sylib', 'y e. ( ZZ>= ` 0 )'), w.inst('fzosplitsn')], 'syl', '( 0 ..^ ( y + 1 ) ) = ( ( 0 ..^ y ) u. { y } )')
    e1 = gj([spl], 'prodeq1d', '%s = prod_ h e. ( ( 0 ..^ y ) u. { y } ) ( ( V ` j ) - ( V ` h ) )' % OMJ('( y + 1 )'))
    idhy = w.s([], 'id', '( h = y -> h = y )')
    cgh, nh = w.congr('( ( V ` j ) - ( V ` h ) )', {'h': 'y'}, 'h = y', {'h': idhy})
    e2 = gj([w.s([], 'nfv', 'F/ h %s' % Hj), w.s([], 'nfcv', 'F/_ h ( ( V ` j ) - ( V ` y ) )'), fy, cj.mem('y', 'NN0'),
             gj([w.s([], 'fzonel', '-. y e. ( 0 ..^ y )')], 'a1i', '-. y e. ( 0 ..^ y )'), cjh.mem('( ( V ` j ) - ( V ` h ) )', 'CC'), cgh,
             cj.mem('( ( V ` j ) - ( V ` y ) )', 'CC')], 'fprodsplitsn',
            'prod_ h e. ( ( 0 ..^ y ) u. { y } ) ( ( V ` j ) - ( V ` h ) ) = ( %s x. ( ( V ` j ) - ( V ` y ) ) )' % OMJ('y'))
    om1 = gj([e1, e2], 'eqtrd', '%s = ( %s x. ( ( V ` j ) - ( V ` y ) ) )' % (OMJ('( y + 1 )'), OMJ('y')))
    VT = '( ( V ` j ) ^ %s )' % EXP('t'); VT1 = '( ( V ` j ) ^ %s )' % EXP('( t + 1 )')
    cj.have(VT, 'CC', cj.mem(VT, 'CC')); cj.atom(VT)
    q1 = gj([om1], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. ( ( V ` j ) - ( V ` y ) ) ) )' % (VT, OMJ('( y + 1 )'), VT, OMJ('y')))
    q2 = mvlib.ringeq(w, Hj, '( %s x. ( %s x. ( ( V ` j ) - ( V ` y ) ) ) )' % (VT, OMJ('y')),
                      '( ( ( %s x. ( V ` j ) ) x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) )' % (VT, OMJ('y'), VT, OMJ('y')), cj)
    ex1 = ap(w, Hj, 'expp1d', '( ( V ` j ) ^ ( %s + 1 ) ) = ( %s x. ( V ` j ) )' % (EXP('t'), VT), cj)
    as1 = ap(w, Hj, 'addassd', '( %s + 1 ) = %s' % (EXP('t'), EXP('( t + 1 )')), cj)
    ex2 = gj([gj([as1], 'oveq2d', '( ( V ` j ) ^ ( %s + 1 ) ) = %s' % (EXP('t'), VT1)), ex1], 'eqtr3d', '%s = ( %s x. ( V ` j ) )' % (VT1, VT))
    q3 = gj([gj([ex2], 'oveq1d', '( %s x. %s ) = ( ( %s x. ( V ` j ) ) x. %s )' % (VT1, OMJ('y'), VT, OMJ('y')))], 'oveq1d',
            '( ( %s x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) ) = ( ( ( %s x. ( V ` j ) ) x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) )' % (VT1, OMJ('y'), VT, OMJ('y'), VT, OMJ('y'), VT, OMJ('y')))
    pt = gj([gj([q1, q2], 'eqtrd', '( %s x. %s ) = ( ( ( %s x. ( V ` j ) ) x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) )' % (VT, OMJ('( y + 1 )'), VT, OMJ('y'), VT, OMJ('y'))), q3],
            'eqtr4d', '( %s x. %s ) = ( ( %s x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) )' % (VT, OMJ('( y + 1 )'), VT1, OMJ('y'), VT, OMJ('y')))
    s1 = gh([pt], 'sumeq2dv', '%s = sum_ j e. ( 0 ..^ N ) ( ( %s x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) )' % (SL('( y + 1 )', 't'), VT1, OMJ('y'), VT, OMJ('y')))
    fzN = gh([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    cj.have(VT1, 'CC', cj.mem(VT1, 'CC')); cj.atom(VT1)
    s2 = gh([fzN, cj.mem('( %s x. %s )' % (VT1, OMJ('y')), 'CC'), cj.mem('( ( V ` y ) x. ( %s x. %s ) )' % (VT, OMJ('y')), 'CC')], 'fsumsub',
            'sum_ j e. ( 0 ..^ N ) ( ( %s x. %s ) - ( ( V ` y ) x. ( %s x. %s ) ) ) = ( %s - sum_ j e. ( 0 ..^ N ) ( ( V ` y ) x. ( %s x. %s ) ) )'
            % (VT1, OMJ('y'), VT, OMJ('y'), SL('y', '( t + 1 )'), VT, OMJ('y')))
    s3 = gh([fzN, ch.mem('( V ` y )', 'CC'), cj.mem('( %s x. %s )' % (VT, OMJ('y')), 'CC')], 'fsummulc2',
            '( ( V ` y ) x. %s ) = sum_ j e. ( 0 ..^ N ) ( ( V ` y ) x. ( %s x. %s ) )' % (SL('y', 't'), VT, OMJ('y')))
    s4 = gh([s3], 'oveq2d', '( %s - ( ( V ` y ) x. %s ) ) = ( %s - sum_ j e. ( 0 ..^ N ) ( ( V ` y ) x. ( %s x. %s ) ) )' % (SL('y', '( t + 1 )'), SL('y', 't'), SL('y', '( t + 1 )'), VT, OMJ('y')))
    alg = gh([gh([s1, s2], 'eqtrd', '%s = ( %s - sum_ j e. ( 0 ..^ N ) ( ( V ` y ) x. ( %s x. %s ) ) )' % (SL('( y + 1 )', 't'), SL('y', '( t + 1 )'), VT, OMJ('y'))), s4],
             'eqtr4d', '%s = ( %s - ( ( V ` y ) x. %s ) )' % (SL('( y + 1 )', 't'), SL('y', '( t + 1 )'), SL('y', 't')))
    sa = gh([fzN, cj.mem('( %s x. %s )' % (VT1, OMJ('y')), 'CC')], 'fsumcl', '%s e. CC' % SL('y', '( t + 1 )'))
    sb_ = gh([fzN, cj.mem('( %s x. %s )' % (VT, OMJ('y')), 'CC')], 'fsumcl', '%s e. CC' % SL('y', 't'))
    ry = w.s([], 'id', '( r = y -> r = y )')
    cry, nry = w.wcongr('( abs ` ( V ` r ) ) <_ 1', {'r': 'y'}, 'r = y', {'r': ry})
    vyb = gh([yin, LH(vb), w.s([cry], 'rspcv', '( y e. ( 0 ..^ N ) -> ( A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 -> %s ) )' % nry)], 'sylc', nry)
    # ---- step with the induction hypothesis
    G0 = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (A0, PS('y'))
    G2 = '( ( %s /\\ t e. NN0 ) /\\ ( ( y + 1 ) + t ) < N )' % G0
    g2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (G2, f))
    L2 = lambda st: _cl.lift(w, st, G2)
    hG = g2([g2([g2([L2(w.s([], 'simpll', '( %s -> %s )' % (G0, A0))), L2(w.s([], 'simplr', '( %s -> y e. NN0 )' % G0))], 'jca', '( %s /\\ y e. NN0 )' % A0),
                 L2(w.s([], 'simpr', '( ( %s /\\ t e. NN0 ) -> t e. NN0 )' % G0))], 'jca', '( ( %s /\\ y e. NN0 ) /\\ t e. NN0 )' % A0),
             w.s([], 'simpr', '( %s -> ( ( y + 1 ) + t ) < N )' % G2)], 'jca', H)
    FH = lambda st: w.s([hG, st], 'syl', '( %s -> %s )' % (G2, body_of(w, st)))
    c2 = Closure(w, G2, {'y': ('NN0', FH(ch.mem('y', 'NN0'))), 't': ('NN0', FH(ch.mem('t', 'NN0'))), 'N': ('NN', FH(ch.mem('N', 'NN'))), 'C': ('RR', FH(ch.mem('C', 'RR')))})
    c2.have('C', 'ge0', FH(ch.ge0('C')))
    ih = L2(w.s([], 'simpr', '( %s -> %s )' % (G0, PS('y'))))
    def inst(tv):
        idst = w.s([], 'id', '( s = %s -> s = %s )' % (tv, tv))
        cg, nw = w.wcongr(BODY('y', 's'), {'s': tv}, 's = %s' % tv, {'s': idst})
        r = w.s([cg], 'rspcv', '( %s e. NN0 -> ( %s -> %s ) )' % (tv, PS('y'), nw))
        m = g2([c2.mem(tv, 'NN0'), ih, r], 'sylc', nw)
        cond = lin.linarith(w, G2, [w.s([], 'simpr', '( %s -> ( ( y + 1 ) + t ) < N )' % G2)], '( y + %s ) < N' % tv, closure=c2)
        return g2([cond, m], 'mpd', '( abs ` %s ) <_ ( ( 2 ^ y ) x. C )' % SL('y', tv))
    ia = inst('( t + 1 )'); ib = inst('t')
    A_ = SL('y', '( t + 1 )'); B_ = SL('y', 't')
    for tt, st in ((A_, FH(sa)), (B_, FH(sb_)), ('( V ` y )', FH(vy))):
        c2.have(tt, 'CC', st); c2.atom(tt)
    tri = ap(w, G2, 'abs2dif2d', '( abs ` ( %s - ( ( V ` y ) x. %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( ( V ` y ) x. %s ) ) )' % (A_, B_, A_, B_), c2)
    am = ap(w, G2, 'absmuld', '( abs ` ( ( V ` y ) x. %s ) ) = ( ( abs ` ( V ` y ) ) x. ( abs ` %s ) )' % (B_, B_), c2)
    for tt in ('( abs ` %s )' % A_, '( abs ` %s )' % B_, '( abs ` ( V ` y ) )', '( 2 ^ y )'):
        c2.have(tt, 'RR', c2.mem(tt, 'RR')); c2.atom(tt)
    bl = ap(w, G2, 'lemul1ad', '( ( abs ` ( V ` y ) ) x. ( abs ` %s ) ) <_ ( 1 x. ( abs ` %s ) )' % (B_, B_), c2, facts=[FH(vyb)])
    PY = '( ( 2 ^ y ) x. C )'
    c2.have(PY, 'RR', c2.mem(PY, 'RR')); c2.atom(PY)
    e2 = ap(w, G2, 'expp1d', '( 2 ^ ( y + 1 ) ) = ( ( 2 ^ y ) x. 2 )', c2)
    e3 = g2([e2], 'oveq1d', '( ( 2 ^ ( y + 1 ) ) x. C ) = ( ( ( 2 ^ y ) x. 2 ) x. C )')
    c2.atom('( 2 ^ ( y + 1 ) )')
    e4 = mvlib.ringeq(w, G2, '( ( ( 2 ^ y ) x. 2 ) x. C )', '( 2 x. %s )' % PY, c2)
    e5 = g2([e3, e4], 'eqtrd', '( ( 2 ^ ( y + 1 ) ) x. C ) = ( 2 x. %s )' % PY)
    fin = lin.linarith(w, G2, [tri, am, bl, ia, ib, e5], '( abs ` ( %s - ( ( V ` y ) x. %s ) ) ) <_ ( ( 2 ^ ( y + 1 ) ) x. C )' % (A_, B_), closure=c2)
    fin2 = g2([g2([FH(alg)], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s - ( ( V ` y ) x. %s ) ) )' % (SL('( y + 1 )', 't'), A_, B_)), fin], 'eqbrtrd',
              '( abs ` %s ) <_ ( ( 2 ^ ( y + 1 ) ) x. C )' % SL('( y + 1 )', 't'))
    stp = w.s([fin2], 'ex', '( ( %s /\\ t e. NN0 ) -> %s )' % (G0, BODY('( y + 1 )', 't')))
    stp = w.s([stp], 'ralrimiva', '( %s -> A. t e. NN0 %s )' % (G0, BODY('( y + 1 )', 't')))
    idts = w.s([], 'id', '( t = s -> t = s )')
    cgt, newt = w.wcongr(BODY('( y + 1 )', 't'), {'t': 's'}, 't = s', {'t': idts})
    step = w.s([stp, w.s([cgt], 'cbvralvw', '( A. t e. NN0 %s <-> A. s e. NN0 %s )' % (BODY('( y + 1 )', 't'), newt))], 'sylib', '( %s -> %s )' % (G0, PS('( y + 1 )')))
    ind = w.s([hx0, hxy, hxy1, hxi, base, step], 'nn0indd', '( ( %s /\\ i e. NN0 ) -> %s )' % (A0, PS('i')))
    # specialise s := 0 for i e. ( 0 ..^ N )
    Ai = '( %s /\\ i e. ( 0 ..^ N ) )' % A0
    si = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    iin = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai)
    inn = si([iin, w.inst('elfzonn0')], 'syl', 'i e. NN0')
    psi = si([si([w.s([], 'simpl', '( %s -> %s )' % (Ai, A0)), inn], 'jca', '( %s /\\ i e. NN0 )' % A0), ind], 'syl', PS('i'))
    ids0 = w.s([], 'id', '( s = 0 -> s = 0 )')
    cg0, n0 = w.wcongr(BODY('i', 's'), {'s': '0'}, 's = 0', {'s': ids0})
    b0i = si([si([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), psi, w.s([cg0], 'rspcv', '( 0 e. NN0 -> ( %s -> %s ) )' % (PS('i'), n0))], 'sylc', n0)
    ci = Closure(w, Ai, {'i': ('NN0', inn), 'N': ('NN', _cl.lift(w, nn, Ai)), 'M': ('NN0', _cl.lift(w, mm, Ai))})
    ilt = si([iin, w.inst('elfzolt2')], 'syl', 'i < N')
    cond = lin.linarith(w, Ai, [ilt], '( i + 0 ) < N', closure=ci)
    b1 = si([cond, b0i], 'mpd', '( abs ` %s ) <_ ( ( 2 ^ i ) x. C )' % SL('i', '0'))
    ad0 = ap(w, Ai, 'addridd', '( ( M + 1 ) + 0 ) = ( M + 1 )', ci)
    SLi = 'sum_ j e. ( 0 ..^ N ) ( ( ( V ` j ) ^ ( M + 1 ) ) x. %s )' % OMJ('i')
    Aij = '( %s /\\ j e. ( 0 ..^ N ) )' % Ai
    e0j = w.s([w.s([_cl.lift(w, ad0, Aij)], 'oveq2d', '( %s -> ( ( V ` j ) ^ ( ( M + 1 ) + 0 ) ) = ( ( V ` j ) ^ ( M + 1 ) ) )' % Aij)], 'oveq1d',
              '( %s -> ( ( ( V ` j ) ^ ( ( M + 1 ) + 0 ) ) x. %s ) = ( ( ( V ` j ) ^ ( M + 1 ) ) x. %s ) )' % (Aij, OMJ('i'), OMJ('i')))
    se = si([e0j], 'sumeq2dv', '%s = %s' % (SL('i', '0'), SLi))
    b2 = si([si([se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (SL('i', '0'), SLi)), b1], 'eqbrtrrd', '( abs ` %s ) <_ ( ( 2 ^ i ) x. C )' % SLi)
    w.qed([b2], 'ralrimiva', S['tplam'])
    return run(w)


if __name__ == '__main__':
    gen_lam()
