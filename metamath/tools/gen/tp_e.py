"""Sortie TP: the radius selection (tpquad: one factor on the unit circle; tprad: Lean exists_cheb_radius
with ( E / 4 ) ^ N, by averaging over the roots of unity)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *
import mvlib
import cl as _cl
from tp_d import UU, TPI, consts

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


QA = '( ( W e. CC /\\ ( abs ` W ) = 1 ) /\\ ( E e. RR+ /\\ X e. RR ) )'
EE = '( ( 4 x. X ) / E )'
RR_ = '( ( E / 2 ) x. ( 1 + ( Re ` W ) ) )'
S['tpquad'] = ('( %s -> ( abs ` ( ( ( W + 1 ) ^ 2 ) - ( %s x. W ) ) ) = ( ( 4 / E ) x. ( abs ` ( %s - X ) ) ) )' % (QA, EE, RR_))


def gen_quad():
    w = W('tpquad', 'One factor of the roots-of-unity average on the unit circle: '
               '` abs ( ( w + 1 ) ^ 2 - ( 4 X / E ) w ) = ( 4 / E ) abs ( ( E / 2 ) ( 1 + Re w ) - X ) ` for ` abs w = 1 ` .')
    A = QA
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    wc = s([], 'simpll', 'W e. CC'); wa = s([], 'simplr', '( abs ` W ) = 1')
    ep = s([], 'simprl', 'E e. RR+'); xr = s([], 'simprr', 'X e. RR')
    c = Closure(w, A, {'W': ('CC', wc), 'E': ('RR+', ep), 'X': ('RR', xr)})
    CJ = '( * ` W )'; RW = '( Re ` W )'
    c.have(CJ, 'CC', ap(w, A, 'cjcld', '%s e. CC' % CJ, c))
    c.have(RW, 'RR', apc(w, A, 'recl', '%s e. RR' % RW, c))
    f1 = apc(w, A, 'absvalsq', '( ( abs ` W ) ^ 2 ) = ( W x. %s )' % CJ, c)
    f2 = s([s([wa], 'oveq1d', '( ( abs ` W ) ^ 2 ) = ( 1 ^ 2 )'), s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')],
           'eqtrd', '( ( abs ` W ) ^ 2 ) = 1')
    wcj = s([f1, f2], 'eqtr3d', '( W x. %s ) = 1' % CJ)
    f3 = apc(w, A, 'reval', '%s = ( ( W + %s ) / 2 )' % (RW, CJ), c)
    f4a = s([f3], 'oveq2d', '( 2 x. %s ) = ( 2 x. ( ( W + %s ) / 2 ) )' % (RW, CJ))
    f4b = ap(w, A, 'divcan2d', '( 2 x. ( ( W + %s ) / 2 ) ) = ( W + %s )' % (CJ, CJ), c)
    f4 = s([f4a, f4b], 'eqtrd', '( 2 x. %s ) = ( W + %s )' % (RW, CJ))
    c.atom(EE); c.have(EE, 'CC', c.mem(EE, 'CC'))
    Z = '( ( ( W + 1 ) ^ 2 ) - ( %s x. W ) )' % EE
    g1 = mvlib.ringeqp(w, A, Z, '( ( W x. ( ( W + 2 ) - %s ) ) + 1 )' % EE, c)
    g2 = s([s([wcj], 'eqcomd', '1 = ( W x. %s )' % CJ)], 'oveq2d',
           '( ( W x. ( ( W + 2 ) - %s ) ) + 1 ) = ( ( W x. ( ( W + 2 ) - %s ) ) + ( W x. %s ) )' % (EE, EE, CJ))
    c.atom(CJ)
    g3 = mvlib.ringeq(w, A, '( ( W x. ( ( W + 2 ) - %s ) ) + ( W x. %s ) )' % (EE, CJ), '( W x. ( ( ( W + %s ) + 2 ) - %s ) )' % (CJ, EE), c)
    g4 = s([s([s([f4], 'eqcomd', '( W + %s ) = ( 2 x. %s )' % (CJ, RW))], 'oveq1d', '( ( W + %s ) + 2 ) = ( ( 2 x. %s ) + 2 )' % (CJ, RW))],
           'oveq1d', '( ( ( W + %s ) + 2 ) - %s ) = ( ( ( 2 x. %s ) + 2 ) - %s )' % (CJ, EE, RW, EE))
    g4 = s([g4], 'oveq2d', '( W x. ( ( ( W + %s ) + 2 ) - %s ) ) = ( W x. ( ( ( 2 x. %s ) + 2 ) - %s ) )' % (CJ, EE, RW, EE))
    zeq = s([g1, g2, g3], '3eqtrd', '%s = ( W x. ( ( ( W + %s ) + 2 ) - %s ) )' % (Z, CJ, EE))
    zeq = s([zeq, g4], 'eqtrd', '%s = ( W x. ( ( ( 2 x. %s ) + 2 ) - %s ) )' % (Z, RW, EE))
    FE = '( 4 / E )'
    h1a = ap(w, A, 'divassd', '( ( %s x. E ) / 2 ) = ( %s x. ( E / 2 ) )' % (FE, FE), c)
    h1b = s([ap(w, A, 'divcan1d', '( %s x. E ) = 4' % FE, c)], 'oveq1d', '( ( %s x. E ) / 2 ) = ( 4 / 2 )' % FE)
    h1c = s([w.s([], '4div2e2', '( 4 / 2 ) = 2')], 'a1i', '( 4 / 2 ) = 2')
    h1 = s([h1a, h1b, h1c], '3eqtr3d', '( %s x. ( E / 2 ) ) = 2' % FE)
    h2 = ap(w, A, 'subdid', '( %s x. ( %s - X ) ) = ( ( %s x. %s ) - ( %s x. X ) )' % (FE, RR_, FE, RR_, FE), c)
    h3a = ap(w, A, 'mulassd', '( ( %s x. ( E / 2 ) ) x. ( 1 + %s ) ) = ( %s x. %s )' % (FE, RW, FE, RR_), c)
    h3b = s([h1], 'oveq1d', '( ( %s x. ( E / 2 ) ) x. ( 1 + %s ) ) = ( 2 x. ( 1 + %s ) )' % (FE, RW, RW))
    h3 = s([h3a, h3b], 'eqtr3d', '( %s x. %s ) = ( 2 x. ( 1 + %s ) )' % (FE, RR_, RW))
    h4 = ap(w, A, 'div23d', '%s = ( %s x. X )' % (EE, FE), c)
    h5 = s([h3, s([h4], 'eqcomd', '( %s x. X ) = %s' % (FE, EE))], 'oveq12d',
           '( ( %s x. %s ) - ( %s x. X ) ) = ( ( 2 x. ( 1 + %s ) ) - %s )' % (FE, RR_, FE, RW, EE))
    h6 = mvlib.ringeq(w, A, '( ( 2 x. ( 1 + %s ) ) - %s )' % (RW, EE), '( ( ( 2 x. %s ) + 2 ) - %s )' % (RW, EE), c)
    hh = s([h2, h5, h6], '3eqtrd', '( %s x. ( %s - X ) ) = ( ( ( 2 x. %s ) + 2 ) - %s )' % (FE, RR_, RW, EE))
    zeq2 = s([zeq, s([hh], 'oveq2d', '( W x. ( %s x. ( %s - X ) ) ) = ( W x. ( ( ( 2 x. %s ) + 2 ) - %s ) )' % (FE, RR_, RW, EE))],
             'eqtr4d', '%s = ( W x. ( %s x. ( %s - X ) ) )' % (Z, FE, RR_))
    a1 = s([zeq2], 'fveq2d', '( abs ` %s ) = ( abs ` ( W x. ( %s x. ( %s - X ) ) ) )' % (Z, FE, RR_))
    a2 = ap(w, A, 'absmuld', '( abs ` ( W x. ( %s x. ( %s - X ) ) ) ) = ( ( abs ` W ) x. ( abs ` ( %s x. ( %s - X ) ) ) )' % (FE, RR_, FE, RR_), c)
    a3 = ap(w, A, 'absmuld', '( abs ` ( %s x. ( %s - X ) ) ) = ( ( abs ` %s ) x. ( abs ` ( %s - X ) ) )' % (FE, RR_, FE, RR_), c)
    a4 = s([ap(w, A, 'absidd', '( abs ` %s ) = %s' % (FE, FE), c)], 'oveq1d',
           '( ( abs ` %s ) x. ( abs ` ( %s - X ) ) ) = ( %s x. ( abs ` ( %s - X ) ) )' % (FE, RR_, FE, RR_))
    a34 = s([a3, a4], 'eqtrd', '( abs ` ( %s x. ( %s - X ) ) ) = ( %s x. ( abs ` ( %s - X ) ) )' % (FE, RR_, FE, RR_))
    a5 = s([wa, a34], 'oveq12d', '( ( abs ` W ) x. ( abs ` ( %s x. ( %s - X ) ) ) ) = ( 1 x. ( %s x. ( abs ` ( %s - X ) ) ) )' % (FE, RR_, FE, RR_))
    a6 = ap(w, A, 'mullidd', '( 1 x. ( %s x. ( abs ` ( %s - X ) ) ) ) = ( %s x. ( abs ` ( %s - X ) ) )' % (FE, RR_, FE, RR_), c)
    b1 = s([a1, a2, a5], '3eqtrd', '( abs ` %s ) = ( 1 x. ( %s x. ( abs ` ( %s - X ) ) ) )' % (Z, FE, RR_))
    w.qed([b1, a6], 'eqtrd', S['tpquad'])
    return run(w)


LL = '( ( 2 x. N ) + 1 )'
UL = UU(LL)
GM = '( y e. ( 0 ..^ N ) |-> ( ( 4 x. ( F ` y ) ) / E ) )'
S['tprad'] = ('( ( N e. NN /\\ F : ( 0 ..^ N ) --> RR /\\ E e. RR+ ) -> E. r e. ( 0 [,] E ) '
              '( ( E / 4 ) ^ N ) <_ prod_ h e. ( 0 ..^ N ) ( abs ` ( r - ( F ` h ) ) ) )')


def FAC(wv, x):
    return '( ( ( %s + 1 ) ^ 2 ) - ( %s x. %s ) )' % (wv, x, wv)


def QP(wv):
    return 'prod_ h e. ( 0 ..^ N ) %s' % FAC(wv, '( ( 4 x. ( F ` h ) ) / E )')


def gen_rad():
    w = W('tprad', 'Lean ` exists_cheb_radius ` with ` ( E / 4 ) ^ N ` : some ` r e. [ 0 , E ] ` keeps ` prod_h abs ( r - F_h ) >_ ( E / 4 ) ^ N ` '
               '(the average of ` prod_h ( ( w + 1 ) ^ 2 - ( 4 F_h / E ) w ) ` over the ( 2 N + 1 )-th roots of unity is 1, and at a root '
               'with modulus >_ 1 the factors are ` ( 4 / E ) abs ( r - F_h ) ` , ` r = ( E / 2 ) ( 1 + Re w ) ` ).')
    A = '( N e. NN /\\ F : ( 0 ..^ N ) --> RR /\\ E e. RR+ )'
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    nn = s([], 'simp1', 'N e. NN'); ff = s([], 'simp2', 'F : ( 0 ..^ N ) --> RR'); ep = s([], 'simp3', 'E e. RR+')
    c = Closure(w, A, {'N': ('NN', nn), 'E': ('RR+', ep)})
    consts(w, A, c)
    lnn = c.mem(LL, 'NN')
    n2 = lin.linarith(w, A, [], '( 2 x. N ) < %s' % LL, closure=c)
    Ah = '( %s /\\ h e. ( 0 ..^ N ) )' % A
    ch = Closure(w, Ah, {'E': ('RR+', _cl.lift(w, ep, Ah))})
    fh = w.s([_cl.lift(w, ff, Ah), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % Ah)], 'ffvelcdmd', '( %s -> ( F ` h ) e. RR )' % Ah)
    ch.have('( F ` h )', 'RR', fh); ch.atom('( F ` h )')
    gv = ch.mem('( ( 4 x. ( F ` h ) ) / E )', 'CC')
    Ay = '( %s /\\ y e. ( 0 ..^ N ) )' % A
    cy = Closure(w, Ay, {'E': ('RR+', _cl.lift(w, ep, Ay))})
    fy = w.s([_cl.lift(w, ff, Ay), w.s([], 'simpr', '( %s -> y e. ( 0 ..^ N ) )' % Ay)], 'ffvelcdmd', '( %s -> ( F ` y ) e. RR )' % Ay)
    cy.have('( F ` y )', 'RR', fy); cy.atom('( F ` y )')
    gf = s([cy.mem('( ( 4 x. ( F ` y ) ) / E )', 'CC'), w.s([], 'eqid', '%s = %s' % (GM, GM))], 'fmptd', '%s : ( 0 ..^ N ) --> CC' % GM)
    WJ = '( %s ^ j )' % UL
    QG = 'prod_ h e. ( 0 ..^ N ) %s' % FAC(WJ, '( %s ` h )' % GM)
    ru = apc(w, A, 'tprui', 'sum_ j e. ( 0 ..^ %s ) %s = %s' % (LL, QG, LL), c, facts=[lnn, c.mem('N', 'NN0'), gf, n2])
    # rewrite ( G ` h )
    Aj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (A, LL)
    Ajh = '( %s /\\ h e. ( 0 ..^ N ) )' % Aj
    cjh = Closure(w, Ajh, {'E': ('RR+', _cl.lift(w, ep, Ajh))})
    fjh = w.s([_cl.lift(w, ff, Ajh), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % Ajh)], 'ffvelcdmd', '( %s -> ( F ` h ) e. RR )' % Ajh)
    cjh.have('( F ` h )', 'RR', fjh); cjh.atom('( F ` h )')
    gvv = cjh.mem('( ( 4 x. ( F ` h ) ) / E )', 'CC')
    idyh = w.s([], 'id', '( y = h -> y = h )')
    cgy, newy = w.congr('( ( 4 x. ( F ` y ) ) / E )', {'y': 'h'}, 'y = h', {'y': idyh})
    fv0 = w.s([cgy, w.s([], 'eqid', '%s = %s' % (GM, GM)), w.s([], 'ovex', '( ( 4 x. ( F ` h ) ) / E ) e. _V')], 'fvmpt',
              '( h e. ( 0 ..^ N ) -> ( %s ` h ) = ( ( 4 x. ( F ` h ) ) / E ) )' % GM)
    fv = w.s([w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % Ajh), fv0], 'syl', '( %s -> ( %s ` h ) = ( ( 4 x. ( F ` h ) ) / E ) )' % (Ajh, GM))
    fv2 = w.s([w.s([fv], 'oveq1d', '( %s -> ( ( %s ` h ) x. %s ) = ( ( ( 4 x. ( F ` h ) ) / E ) x. %s ) )' % (Ajh, GM, WJ, WJ))], 'oveq2d',
              '( %s -> %s = %s )' % (Ajh, FAC(WJ, '( %s ` h )' % GM), FAC(WJ, '( ( 4 x. ( F ` h ) ) / E )')))
    pq = w.s([fv2], 'prodeq2dv', '( %s -> %s = %s )' % (Aj, QG, QP(WJ)))
    sq = s([pq], 'sumeq2dv', 'sum_ j e. ( 0 ..^ %s ) %s = sum_ j e. ( 0 ..^ %s ) %s' % (LL, QG, LL, QP(WJ)))
    SQ = 'sum_ j e. ( 0 ..^ %s ) %s' % (LL, QP(WJ))
    sl = s([sq, ru], 'eqtr3d', '%s = %s' % (SQ, LL))
    # membership of the products
    cj = Closure(w, Aj, {'E': ('RR+', _cl.lift(w, ep, Aj)), 'N': ('NN', _cl.lift(w, nn, Aj))})
    consts(w, Aj, cj)
    cj.have(LL, 'NN', _cl.lift(w, lnn, Aj))
    cj.have('j', 'NN0', w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (Aj, LL)), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % Aj))
    uj = apc(w, Aj, 'efcl', '%s e. CC' % UL, cj); cj.have(UL, 'CC', uj); cj.atom(UL)
    wjc = cj.mem(WJ, 'CC'); cj.atom(WJ)
    cjh.have(WJ, 'CC', _cl.lift(w, wjc, Ajh)); cjh.atom(WJ)
    fz = w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % Aj)
    qc = w.s([fz, cjh.mem(FAC(WJ, '( ( 4 x. ( F ` h ) ) / E )'), 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Aj, QP(WJ)))
    # ---- contradiction: not every product has modulus < 1
    WI = '( %s ^ i )' % UL
    ALL = 'A. i e. ( 0 ..^ %s ) ( abs ` %s ) < 1' % (LL, QP(WI))
    B = '( %s /\\ %s )' % (A, ALL)
    sB = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (B, f))
    cB = Closure(w, B, {'N': ('NN', _cl.lift(w, nn, B))})
    cB.have(LL, 'NN', _cl.lift(w, lnn, B))
    Bj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (B, LL)
    # ( abs ` Q_j ) < 1 from ALL
    idij = w.s([], 'id', '( i = j -> i = j )')
    cgi, newi = w.wcongr('( abs ` %s ) < 1' % QP(WI), {'i': 'j'}, 'i = j', {'i': idij})
    assert newi == '( abs ` %s ) < 1' % QP(WJ), newi
    rj = w.s([cgi], 'rspcv', '( j e. ( 0 ..^ %s ) -> ( %s -> %s ) )' % (LL, ALL, newi))
    lt1 = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (Bj, LL)), _cl.lift(w, w.s([], 'simpr', '( %s -> %s )' % (B, ALL)), Bj), rj],
              'sylc', '( %s -> %s )' % (Bj, newi))
    # Q_j e. CC under Bj: lift from Aj via a conjunction step
    bjaj = w.s([_cl.lift(w, w.s([], 'simpl', '( %s -> %s )' % (B, A)), Bj), w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (Bj, LL))], 'jca', '( %s -> %s )' % (Bj, Aj))
    qcb = w.s([bjaj, qc], 'syl', '( %s -> %s e. CC )' % (Bj, QP(WJ)))
    abr = w.s([qcb], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Bj, QP(WJ)))
    one = w.s([], '1red', '( %s -> 1 e. RR )' % Bj)
    fzl = sB([w.s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % LL)], 'a1i', '( 0 ..^ %s ) e. Fin' % LL)
    ne0 = sB([cB.mem(LL, 'NN'), w.inst('fzo0n0')], 'sylibr', '( 0 ..^ %s ) =/= (/)' % LL)
    slt = sB([fzl, ne0, abr, one, lt1], 'fsumlt', 'sum_ j e. ( 0 ..^ %s ) ( abs ` %s ) < sum_ j e. ( 0 ..^ %s ) 1' % (LL, QP(WJ), LL))
    sab = sB([fzl, qcb], 'fsumabs', '( abs ` %s ) <_ sum_ j e. ( 0 ..^ %s ) ( abs ` %s )' % (SQ, LL, QP(WJ)))
    s1a = sB([fzl, sB([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), w.inst('fsumconst')], 'syl2anc',
             'sum_ j e. ( 0 ..^ %s ) 1 = ( ( # ` ( 0 ..^ %s ) ) x. 1 )' % (LL, LL))
    s1b = sB([sB([cB.mem(LL, 'NN0'), w.inst('hashfzo0')], 'syl', '( # ` ( 0 ..^ %s ) ) = %s' % (LL, LL))], 'oveq1d',
             '( ( # ` ( 0 ..^ %s ) ) x. 1 ) = ( %s x. 1 )' % (LL, LL))
    s1c = ap(w, B, 'mulridd', '( %s x. 1 ) = %s' % (LL, LL), cB)
    s1 = sB([s1a, s1b, s1c], '3eqtrd', 'sum_ j e. ( 0 ..^ %s ) 1 = %s' % (LL, LL))
    slb = _cl.lift(w, sl, B)
    sabs = sB([sB([slb], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (SQ, LL)), ap(w, B, 'absidd', '( abs ` %s ) = %s' % (LL, LL), cB)], 'eqtrd',
              '( abs ` %s ) = %s' % (SQ, LL))
    cB.atom('sum_ j e. ( 0 ..^ %s ) ( abs ` %s )' % (LL, QP(WJ)))
    cB.have('sum_ j e. ( 0 ..^ %s ) ( abs ` %s )' % (LL, QP(WJ)), 'RR', sB([fzl, abr], 'fsumrecl', 'sum_ j e. ( 0 ..^ %s ) ( abs ` %s ) e. RR' % (LL, QP(WJ))))
    cB.atom('sum_ j e. ( 0 ..^ %s ) 1' % LL); cB.atom('( abs ` %s )' % SQ)
    cB.have('( abs ` %s )' % SQ, 'RR', sB([sabs, cB.mem(LL, 'RR')], 'eqeltrd', '( abs ` %s ) e. RR' % SQ))
    cB.have('sum_ j e. ( 0 ..^ %s ) 1' % LL, 'RR', sB([s1, cB.mem(LL, 'RR')], 'eqeltrd', 'sum_ j e. ( 0 ..^ %s ) 1 e. RR' % LL))
    cB.atom(LL)
    llt = lin.linarith(w, B, [sab, slt, s1, sabs], '%s < %s' % (LL, LL), closure=cB)
    nlt = ap(w, B, 'ltnrd', '-. %s < %s' % (LL, LL), cB)
    nall = s([llt, nlt], 'pm2.65da', '-. %s' % ALL)
    ex = s([nall, w.s([], 'rexnal', '( E. i e. ( 0 ..^ %s ) -. ( abs ` %s ) < 1 <-> -. %s )' % (LL, QP(WI), ALL))], 'sylibr',
           'E. i e. ( 0 ..^ %s ) -. ( abs ` %s ) < 1' % (LL, QP(WI)))
    # ---- at a good root
    Ai = '( %s /\\ i e. ( 0 ..^ %s ) )' % (A, LL)
    si = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    ci = Closure(w, Ai, {'E': ('RR+', _cl.lift(w, ep, Ai)), 'N': ('NN', _cl.lift(w, nn, Ai))})
    consts(w, Ai, ci)
    ci.have(LL, 'NN', _cl.lift(w, lnn, Ai))
    ci.have('i', 'NN0', w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (Ai, LL)), w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai))
    ui = apc(w, Ai, 'efcl', '%s e. CC' % UL, ci); ci.have(UL, 'CC', ui)
    # abs U = 1
    X2 = '( ( 2 x. _pi ) / %s )' % LL
    da = ap(w, Ai, 'divassd', '( %s / %s ) = ( _i x. %s )' % (TPI, LL, X2), ci)
    u1 = si([da], 'fveq2d', '%s = ( exp ` ( _i x. %s ) )' % (UL, X2))
    u2 = si([si([u1], 'fveq2d', '( abs ` %s ) = ( abs ` ( exp ` ( _i x. %s ) ) )' % (UL, X2)), apc(w, Ai, 'absefi', '( abs ` ( exp ` ( _i x. %s ) ) ) = 1' % X2, ci)],
            'eqtrd', '( abs ` %s ) = 1' % UL)
    ci.atom(UL)
    wic = ci.mem(WI, 'CC')
    a1 = apc(w, Ai, 'absexp', '( abs ` %s ) = ( ( abs ` %s ) ^ i )' % (WI, UL), ci)
    a2 = si([u2], 'oveq1d', '( ( abs ` %s ) ^ i ) = ( 1 ^ i )' % UL)
    a3 = si([ci.mem('i', 'ZZ'), w.inst('1exp')], 'syl', '( 1 ^ i ) = 1')
    wi1 = si([a1, a2, a3], '3eqtrd', '( abs ` %s ) = 1' % WI)
    ci.atom(WI)
    RI = '( ( E / 2 ) x. ( 1 + ( Re ` %s ) ) )' % WI
    # abs of the product
    Aih = '( %s /\\ h e. ( 0 ..^ N ) )' % Ai
    cih = Closure(w, Aih, {'E': ('RR+', _cl.lift(w, ep, Aih))})
    fih = w.s([_cl.lift(w, ff, Aih), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % Aih)], 'ffvelcdmd', '( %s -> ( F ` h ) e. RR )' % Aih)
    cih.have('( F ` h )', 'RR', fih); cih.atom('( F ` h )')
    cih.have(WI, 'CC', _cl.lift(w, wic, Aih)); cih.atom(WI)
    qd = w.s([_cl.lift(w, wic, Aih), _cl.lift(w, wi1, Aih), _cl.lift(w, ep, Aih), fih, w.inst('tpquad')], 'syl22anc',
             '( %s -> ( abs ` %s ) = ( ( 4 / E ) x. ( abs ` ( %s - ( F ` h ) ) ) ) )' % (Aih, FAC(WI, '( ( 4 x. ( F ` h ) ) / E )'), RI))
    fzi = si([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    fci = cih.mem(FAC(WI, '( ( 4 x. ( F ` h ) ) / E )'), 'CC')
    pa = si([fzi, fci], 'z5fprodabs', '( abs ` %s ) = prod_ h e. ( 0 ..^ N ) ( abs ` %s )' % (QP(WI), FAC(WI, '( ( 4 x. ( F ` h ) ) / E )')))
    pb = si([qd], 'prodeq2dv', 'prod_ h e. ( 0 ..^ N ) ( abs ` %s ) = prod_ h e. ( 0 ..^ N ) ( ( 4 / E ) x. ( abs ` ( %s - ( F ` h ) ) ) )'
            % (FAC(WI, '( ( 4 x. ( F ` h ) ) / E )'), RI))
    ci.atom(RI); ci.have(RI, 'RR', ci.mem(RI, 'RR'))
    cih.have(RI, 'RR', _cl.lift(w, ci.mem(RI, 'RR'), Aih)); cih.atom(RI)
    AB = '( abs ` ( %s - ( F ` h ) ) )' % RI
    PI_ = 'prod_ h e. ( 0 ..^ N ) %s' % AB
    pc = si([fzi, cih.mem('( 4 / E )', 'CC'), cih.mem(AB, 'CC')], 'fprodmul',
            'prod_ h e. ( 0 ..^ N ) ( ( 4 / E ) x. %s ) = ( prod_ h e. ( 0 ..^ N ) ( 4 / E ) x. %s )' % (AB, PI_))
    pd0 = si([fzi, ci.mem('( 4 / E )', 'CC'), w.inst('fprodconst')], 'syl2anc', 'prod_ h e. ( 0 ..^ N ) ( 4 / E ) = ( ( 4 / E ) ^ ( # ` ( 0 ..^ N ) ) )')
    pd1 = si([si([ci.mem('N', 'NN0'), w.inst('hashfzo0')], 'syl', '( # ` ( 0 ..^ N ) ) = N')], 'oveq2d', '( ( 4 / E ) ^ ( # ` ( 0 ..^ N ) ) ) = ( ( 4 / E ) ^ N )')
    pd = si([pd0, pd1], 'eqtrd', 'prod_ h e. ( 0 ..^ N ) ( 4 / E ) = ( ( 4 / E ) ^ N )')
    pe = si([pd], 'oveq1d', '( prod_ h e. ( 0 ..^ N ) ( 4 / E ) x. %s ) = ( ( ( 4 / E ) ^ N ) x. %s )' % (PI_, PI_))
    qab = si([pa, pb, pc], '3eqtrd', '( abs ` %s ) = ( prod_ h e. ( 0 ..^ N ) ( 4 / E ) x. %s )' % (QP(WI), PI_))
    qab = si([qab, pe], 'eqtrd', '( abs ` %s ) = ( ( ( 4 / E ) ^ N ) x. %s )' % (QP(WI), PI_))
    # r in [ 0 , E ]
    rew = apc(w, Ai, 'recl', '( Re ` %s ) e. RR' % WI, ci)
    ci.have('( Re ` %s )' % WI, 'RR', rew); ci.atom('( Re ` %s )' % WI)
    rle = si([apc(w, Ai, 'absrele', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (WI, WI), ci), wi1], 'breqtrd', '( abs ` ( Re ` %s ) ) <_ 1' % WI)
    rab = ap(w, Ai, 'absled', '( ( abs ` ( Re ` %s ) ) <_ 1 <-> ( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 ) )' % (WI, WI, WI), ci)
    rab = si([rle, rab], 'mpbid', '( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 )' % (WI, WI))
    rlo = si([rab], 'simpld', '-u 1 <_ ( Re ` %s )' % WI); rhi = si([rab], 'simprd', '( Re ` %s ) <_ 1' % WI)
    e2g = ci.ge0('( E / 2 )')
    opg = lin.linarith(w, Ai, [rlo], '0 <_ ( 1 + ( Re ` %s ) )' % WI, closure=ci)
    r0 = ap(w, Ai, 'mulge0d', '0 <_ %s' % RI, ci, facts=[e2g, opg])
    op2 = lin.linarith(w, Ai, [rhi], '( 1 + ( Re ` %s ) ) <_ 2' % WI, closure=ci)
    r1 = ap(w, Ai, 'lemul2ad', '%s <_ ( ( E / 2 ) x. 2 )' % RI, ci, facts=[op2])
    r2 = mvlib.ringeq(w, Ai, '( ( E / 2 ) x. 2 )', 'E', ci)
    rE = si([r1, r2], 'breqtrd', '%s <_ E' % RI)
    ric = si([si([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), ci.mem('E', 'RR'), w.inst('elicc2')], 'syl2anc',
             '( %s e. ( 0 [,] E ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ E ) )' % (RI, RI, RI, RI))
    rin = si([si([ci.mem(RI, 'RR'), r0, rE], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ E )' % (RI, RI, RI)), ric], 'mpbird', '%s e. ( 0 [,] E )' % RI)
    # the bound at a root with abs Q >_ 1
    Ai2 = '( %s /\\ -. ( abs ` %s ) < 1 )' % (Ai, QP(WI))
    s2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai2, f))
    c2 = Closure(w, Ai2, {'E': ('RR+', _cl.lift(w, ep, Ai2)), 'N': ('NN', _cl.lift(w, nn, Ai2))})
    PIc = _cl.lift(w, si([fzi, cih.mem(AB, 'RR')], 'fprodrecl', '%s e. RR' % PI_), Ai2)
    c2.have(PI_, 'RR', PIc); c2.atom(PI_)
    qcI = si([fzi, fci], 'fprodcl', '%s e. CC' % QP(WI))
    qab2 = _cl.lift(w, qab, Ai2)
    one2 = s2([s2([_cl.lift(w, qcI, Ai2)], 'abscld', '( abs ` %s ) e. RR' % QP(WI)), w.s([], '1red', '( %s -> 1 e. RR )' % Ai2),
               w.s([], 'simpr', '( %s -> -. ( abs ` %s ) < 1 )' % (Ai2, QP(WI)))], 'nltled', '1 <_ ( abs ` %s )' % QP(WI))
    one3 = s2([one2, qab2], 'breqtrd', '1 <_ ( ( ( 4 / E ) ^ N ) x. %s )' % PI_)
    E4 = '( ( E / 4 ) ^ N )'; F4 = '( ( 4 / E ) ^ N )'
    c2.atom(E4); c2.atom(F4)
    e4g = c2.ge0(E4)
    m1 = ap(w, Ai2, 'lemul2ad', '( %s x. 1 ) <_ ( %s x. ( %s x. %s ) )' % (E4, E4, F4, PI_), c2, facts=[one3])
    m2 = ap(w, Ai2, 'mulridd', '( %s x. 1 ) = %s' % (E4, E4), c2)
    m3 = ap(w, Ai2, 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (E4, F4, PI_, E4, F4, PI_), c2)
    m4 = ap(w, Ai2, 'mulexpd', '( ( ( E / 4 ) x. ( 4 / E ) ) ^ N ) = ( %s x. %s )' % (E4, F4), c2)
    m5 = s2([ap(w, Ai2, 'divcan6d', '( ( E / 4 ) x. ( 4 / E ) ) = 1', c2)], 'oveq1d', '( ( ( E / 4 ) x. ( 4 / E ) ) ^ N ) = ( 1 ^ N )')
    m6 = s2([c2.mem('N', 'ZZ'), w.inst('1exp')], 'syl', '( 1 ^ N ) = 1')
    m7 = s2([m4, m5, m6], '3eqtr3d', '( %s x. %s ) = 1' % (E4, F4))
    m8 = s2([s2([m7], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (E4, F4, PI_, PI_)), ap(w, Ai2, 'mullidd', '( 1 x. %s ) = %s' % (PI_, PI_), c2)],
            'eqtrd', '( ( %s x. %s ) x. %s ) = %s' % (E4, F4, PI_, PI_))
    m9 = s2([m3, m8], 'eqtr3d', '( %s x. ( %s x. %s ) ) = %s' % (E4, F4, PI_, PI_))
    bnd = s2([m1, m2, m9], '3brtr3d', '%s <_ %s' % (E4, PI_))
    # exhibit r
    PIr = 'prod_ h e. ( 0 ..^ N ) ( abs ` ( r - ( F ` h ) ) )'
    idr = w.s([], 'id', '( r = %s -> r = %s )' % (RI, RI))
    cgr, newr = w.wcongr('%s <_ %s' % (E4, PIr), {'r': RI}, 'r = %s' % RI, {'r': idr})
    assert newr == '%s <_ %s' % (E4, PI_), newr
    ev = w.s([cgr], 'rspcev', '( ( %s e. ( 0 [,] E ) /\\ %s ) -> E. r e. ( 0 [,] E ) %s <_ %s )' % (RI, newr, E4, PIr))
    GOAL = 'E. r e. ( 0 [,] E ) %s <_ %s' % (E4, PIr)
    fin = s2([_cl.lift(w, rin, Ai2), bnd, ev], 'syl2anc', GOAL)
    fin = w.s([fin], 'ex', '( %s -> ( -. ( abs ` %s ) < 1 -> %s ) )' % (Ai, QP(WI), GOAL))
    fin = s([fin], 'rexlimdva', '( E. i e. ( 0 ..^ %s ) -. ( abs ` %s ) < 1 -> %s )' % (LL, QP(WI), GOAL))
    w.qed([ex, fin], 'mpd', S['tprad'])
    return run(w)


if __name__ == '__main__':
    gen_quad()
    gen_rad()
