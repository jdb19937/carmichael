"""Sortie ZC1: real parts of m / z (redivnn, redivge: Lean re_natCast_div_nonneg, re_natCast_div_ge)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import cl as _cl
from c8_o import numst
import lin
lin.FASTPATH = True

S['redivnn'] = '( ( ( M e. RR /\\ 0 <_ M ) /\\ ( Z e. CC /\\ 0 < ( Re ` Z ) ) ) -> 0 <_ ( Re ` ( M / Z ) ) )'
S['redivge'] = '( ( ( M e. RR /\\ 0 <_ M ) /\\ ( W e. RR+ /\\ Z e. CC ) /\\ ( W <_ ( Re ` Z ) /\\ ( abs ` Z ) <_ ( 2 x. W ) ) ) -> ( M / ( 4 x. W ) ) <_ ( Re ` ( M / Z ) ) )'
AZ2 = '( ( abs ` Z ) ^ 2 )'


def reid(w, ante, mr, zc, zne):
    """( ante -> ( Re ` ( M / Z ) ) = ( ( M x. ( Re ` Z ) ) / AZ2 ) ), ( ante -> AZ2 e. RR+ )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
    mc = s([mr], 'recnd', 'M e. CC')
    azp = s([s([zc, zne], 'absrpcld', '( abs ` Z ) e. RR+'), s([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld', '%s e. RR+' % AZ2)
    rv = s([s([zc, zne], 'jca', '( Z e. CC /\\ Z =/= 0 )'), w.inst('recval')], 'syl', '( 1 / Z ) = ( ( * ` Z ) / %s )' % AZ2)
    dr = s([mc, zc, zne], 'divrecd', '( M / Z ) = ( M x. ( 1 / Z ) )')
    e1 = s([dr, s([rv], 'oveq2d', '( M x. ( 1 / Z ) ) = ( M x. ( ( * ` Z ) / %s ) )' % AZ2)], 'eqtrd', '( M / Z ) = ( M x. ( ( * ` Z ) / %s ) )' % AZ2)
    cz = s([zc], 'cjcld', '( * ` Z ) e. CC')
    qc = s([cz, s([azp], 'rpcnd', '%s e. CC' % AZ2), s([azp], 'rpne0d', '%s =/= 0' % AZ2)], 'divcld', '( ( * ` Z ) / %s ) e. CC' % AZ2)
    r1 = s([s([mr, qc], 'jca', '( M e. RR /\\ ( ( * ` Z ) / %s ) e. CC )' % AZ2), w.inst('remul2')], 'syl', '( Re ` ( M x. ( ( * ` Z ) / %s ) ) ) = ( M x. ( Re ` ( ( * ` Z ) / %s ) ) )' % (AZ2, AZ2))
    r2 = s([s([azp], 'rpred', '%s e. RR' % AZ2), cz, s([azp], 'rpne0d', '%s =/= 0' % AZ2)], 'redivd', '( Re ` ( ( * ` Z ) / %s ) ) = ( ( Re ` ( * ` Z ) ) / %s )' % (AZ2, AZ2))
    r3 = s([s([zc], 'recjd', '( Re ` ( * ` Z ) ) = ( Re ` Z )')], 'oveq1d', '( ( Re ` ( * ` Z ) ) / %s ) = ( ( Re ` Z ) / %s )' % (AZ2, AZ2))
    rzc = s([s([zc], 'recld', '( Re ` Z ) e. RR')], 'recnd', '( Re ` Z ) e. CC')
    da = s([mc, rzc, s([azp], 'rpcnd', '%s e. CC' % AZ2), s([azp], 'rpne0d', '%s =/= 0' % AZ2)], 'divassd', '( ( M x. ( Re ` Z ) ) / %s ) = ( M x. ( ( Re ` Z ) / %s ) )' % (AZ2, AZ2))
    ch = s([s([s([e1], 'fveq2d', '( Re ` ( M / Z ) ) = ( Re ` ( M x. ( ( * ` Z ) / %s ) ) )' % AZ2), r1], 'eqtrd', '( Re ` ( M / Z ) ) = ( M x. ( Re ` ( ( * ` Z ) / %s ) ) )' % AZ2),
            s([s([r2, r3], 'eqtrd', '( Re ` ( ( * ` Z ) / %s ) ) = ( ( Re ` Z ) / %s )' % (AZ2, AZ2))], 'oveq2d', '( M x. ( Re ` ( ( * ` Z ) / %s ) ) ) = ( M x. ( ( Re ` Z ) / %s ) )' % (AZ2, AZ2))],
           'eqtrd', '( Re ` ( M / Z ) ) = ( M x. ( ( Re ` Z ) / %s ) )' % AZ2)
    return s([ch, s([da], 'eqcomd', '( M x. ( ( Re ` Z ) / %s ) ) = ( ( M x. ( Re ` Z ) ) / %s )' % (AZ2, AZ2))], 'eqtrd', '( Re ` ( M / Z ) ) = ( ( M x. ( Re ` Z ) ) / %s )' % AZ2), azp


def zne_of(w, ante, zc, rzpos):
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
    rz0 = s([rzpos], 'x', 'x') if False else None
    # Re Z > 0 gives Z =/= 0
    A1 = '( %s /\\ Z = 0 )' % ante
    r0 = w.s([w.s([w.s([], 'simpr', '( %s -> Z = 0 )' % A1)], 'fveq2d', '( %s -> ( Re ` Z ) = ( Re ` 0 ) )' % A1), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % A1)],
             'eqtrd', '( %s -> ( Re ` Z ) = 0 )' % A1)
    rzr = s([zc], 'recld', '( Re ` Z ) e. RR')
    nl = w.s([lift(w, rzpos, A1), r0], 'x', 'x') if False else None
    contra = w.s([lift(w, rzpos, A1), r0], 'breqtrd', '( %s -> 0 < 0 )' % A1)
    n00 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A1)], 'ltnrd', '( %s -> -. 0 < 0 )' % A1)
    nz = w.s([contra, n00], 'pm2.65da', '( %s -> -. Z = 0 )' % ante)
    return s([nz], 'neqned', 'Z =/= 0')


def gen_redivnn():
    w = W('redivnn', 'For ` 0 <_ M ` real and ` 0 < Re Z ` , ` 0 <_ Re ( M / Z ) ` (Lean Census ` re_natCast_div_nonneg ` ; ~ recval ).')
    A0 = ante_of(S['redivnn'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    mr = s([], 'simpll', 'M e. RR'); m0 = s([], 'simplr', '0 <_ M'); zc = s([], 'simprl', 'Z e. CC'); zp = s([], 'simprr', '0 < ( Re ` Z )')
    zne = zne_of(w, A0, zc, zp)
    idv, azp = reid(w, A0, mr, zc, zne)
    rzr = s([zc], 'recld', '( Re ` Z ) e. RR')
    num0 = s([mr, rzr, m0, s([rzr, zp], 'x', 'x') if False else lin8(w, A0, [zp], '0 <_ ( Re ` Z )', {'( Re ` Z )': rzr})], 'mulge0d', '0 <_ ( M x. ( Re ` Z ) )')
    q0 = s([s([mr, rzr], 'remulcld', '( M x. ( Re ` Z ) ) e. RR'), azp, num0], 'divge0d', '0 <_ ( ( M x. ( Re ` Z ) ) / %s )' % AZ2)
    w.qed([q0, idv], 'breqtrrd', S['redivnn'])
    return run8(w)


def gen_redivge():
    w = W('redivge', 'For ` 0 <_ M ` real, ` W <_ Re Z ` and ` abs Z <_ 2 W ` , ` M / ( 4 W ) <_ Re ( M / Z ) ` (Lean ` re_natCast_div_ge ` ; ~ recval ).')
    A0 = ante_of(S['redivge'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2, X3 = top_and(A0)
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2); x3 = s([], 'simp3', X3)
    mr = s([x1, w.inst('simpl')], 'syl', 'M e. RR'); m0 = s([x1, w.inst('simpr')], 'syl', '0 <_ M')
    wp = s([x2, w.inst('simpl')], 'syl', 'W e. RR+'); zc = s([x2, w.inst('simpr')], 'syl', 'Z e. CC')
    wz = s([x3, w.inst('simpl')], 'syl', 'W <_ ( Re ` Z )'); az = s([x3, w.inst('simpr')], 'syl', '( abs ` Z ) <_ ( 2 x. W )')
    wr = s([wp], 'rpred', 'W e. RR')
    rzr = s([zc], 'recld', '( Re ` Z ) e. RR')
    zp = lin8(w, A0, [wz, s([wp], 'rpgt0d', '0 < W')], '0 < ( Re ` Z )', {'W': wr, '( Re ` Z )': rzr})
    zne = zne_of(w, A0, zc, zp)
    idv, azp = reid(w, A0, mr, zc, zne)
    azr = s([zc], 'abscld', '( abs ` Z ) e. RR')
    sq = s([az, s([azr, s([s([numst(w, A0, '2', 'RR'), wr], 'remulcld', '( 2 x. W ) e. RR')], 'x', 'x') if False else s([numst(w, A0, '2', 'RR'), wr], 'remulcld', '( 2 x. W ) e. RR'),
                    s([zc], 'absge0d', '0 <_ ( abs ` Z )'), s([numst(w, A0, '2', 'RR'), wr, numst(w, A0, '2', 'ge0'), s([wp], 'rpge0d', '0 <_ W')], 'mulge0d', '0 <_ ( 2 x. W )')], 'le2sqd',
               '( ( abs ` Z ) <_ ( 2 x. W ) <-> %s <_ ( ( 2 x. W ) ^ 2 ) )' % AZ2)], 'mpbid', '%s <_ ( ( 2 x. W ) ^ 2 )' % AZ2)
    w2 = s([s([s([numst(w, A0, '2', 'RR'), wr], 'remulcld', '( 2 x. W ) e. RR')], 'recnd', '( 2 x. W ) e. CC')], 'sqvald', '( ( 2 x. W ) ^ 2 ) = ( ( 2 x. W ) x. ( 2 x. W ) )')
    W4 = '( 4 x. W )'
    D = '( M / %s )' % W4
    w4p = s([numst(w, A0, '4', 'RR+'), wp], 'rpmulcld', '%s e. RR+' % W4)
    dr = s([mr, w4p], 'rerpdivcld', '%s e. RR' % D)
    d0 = s([mr, w4p, m0], 'divge0d', '0 <_ %s' % D)
    dm = s([s([mr], 'recnd', 'M e. CC'), s([w4p], 'rpcnd', '%s e. CC' % W4), s([w4p], 'rpne0d', '%s =/= 0' % W4)], 'divcan1d', '( %s x. %s ) = M' % (D, W4))
    dmw = s([dm], 'oveq1d', '( ( %s x. %s ) x. W ) = ( M x. W )' % (D, W4))
    azr2 = s([azp], 'rpred', '%s e. RR' % AZ2)
    lv = {'M': mr, 'W': wr, '( Re ` Z )': rzr, AZ2: azr2, D: dr}
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    h1 = s([dr, c.mem('( ( ( 2 x. W ) x. ( 2 x. W ) ) - %s )' % AZ2, 'RR'), d0, lin.linarith(w, A0, [sq, w2], '0 <_ ( ( ( 2 x. W ) x. ( 2 x. W ) ) - %s )' % AZ2, closure=c, products=True)], 'mulge0d',
           '0 <_ ( %s x. ( ( ( 2 x. W ) x. ( 2 x. W ) ) - %s ) )' % (D, AZ2))
    h2 = s([mr, c.mem('( ( Re ` Z ) - W )', 'RR'), m0, lin8(w, A0, [wz], '0 <_ ( ( Re ` Z ) - W )', lv)], 'mulge0d', '0 <_ ( M x. ( ( Re ` Z ) - W ) )')
    key = lin.linarith(w, A0, [h1, h2, dmw], '( %s x. %s ) <_ ( M x. ( Re ` Z ) )' % (D, AZ2), closure=c, products=True)
    fin0 = s([key, s([dr, s([mr, rzr], 'remulcld', '( M x. ( Re ` Z ) ) e. RR'), azp], 'lemuldivd', '( ( %s x. %s ) <_ ( M x. ( Re ` Z ) ) <-> %s <_ ( ( M x. ( Re ` Z ) ) / %s ) )' % (D, AZ2, D, AZ2))],
             'mpbid', '%s <_ ( ( M x. ( Re ` Z ) ) / %s )' % (D, AZ2))
    w.qed([fin0, idv], 'breqtrrd', S['redivge'])
    return run8(w)


if __name__ == '__main__':
    gen_redivnn()
    gen_redivge()
