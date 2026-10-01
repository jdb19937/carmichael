"""Sortie C0c batch 4: the coordinate invariants of a horizontal or vertical
segment, and the slit-plane hypotheses of the four edges."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

def coordconst(label, desc, F, eqlab, linlab):
    w = W(label, desc)
    A0 = '( A e. CC /\\ B e. CC /\\ ( %s ` A ) = ( %s ` B ) )' % (F, F)
    A1 = '( %s /\\ u e. ( A cseg B ) )' % A0
    A2 = '( %s /\\ t e. %s )' % (A1, U01)
    L = LIN('A', 'B')
    A3 = '( %s /\\ u = %s )' % (A2, L)
    ac = w.s([], 'simp1', '( %s -> A e. CC )' % A0)
    bc = w.s([], 'simp2', '( %s -> B e. CC )' % A0)
    eq = w.s([], 'simp3', '( %s -> ( %s ` A ) = ( %s ` B ) )' % (A0, F, F))
    umem = w.s([], 'simpr', '( %s -> u e. ( A cseg B ) )' % A1)
    ex = w.s([w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % A1), w.s([bc], 'adantr', '( %s -> B e. CC )' % A1), w.inst('csegel')], 'syl2anc',
                  '( %s -> ( u e. ( A cseg B ) <-> E. t e. %s u = %s ) )' % (A1, U01, L)), umem], 'mpbid',
             '( %s -> E. t e. %s u = %s )' % (A1, U01, L))
    t01 = w.s([], 'simpr', '( %s -> t e. %s )' % (A2, U01))
    tssr = closed(w, A2, 'unitssre', '%s C_ RR' % U01)
    tr = w.s([tssr, t01], 'sseldd', '( %s -> t e. RR )' % A2)
    ac2 = w.s([ac], 'ad2antrr', '( %s -> A e. CC )' % A2)
    bc2 = w.s([bc], 'ad2antrr', '( %s -> B e. CC )' % A2)
    eq2 = w.s([eq], 'ad2antrr', '( %s -> ( %s ` A ) = ( %s ` B ) )' % (A2, F, F))
    lin = w.s([ac2, bc2, tr, w.inst(linlab)], 'syl3anc',
              '( %s -> ( %s ` %s ) = ( ( %s ` A ) + ( t x. ( ( %s ` B ) - ( %s ` A ) ) ) ) )' % (A2, F, L, F, F, F))
    fa = w.s([ac2, w.inst(eqlab)], 'syl', '( %s -> ( %s ` A ) e. RR )' % (A2, F))
    fb = w.s([bc2, w.inst(eqlab)], 'syl', '( %s -> ( %s ` B ) e. RR )' % (A2, F))
    z0 = w.s([w.s([fb], 'recnd', '( %s -> ( %s ` B ) e. CC )' % (A2, F)),
              w.s([eq2], 'eqcomd', '( %s -> ( %s ` B ) = ( %s ` A ) )' % (A2, F, F))], 'subeq0bd',
             '( %s -> ( ( %s ` B ) - ( %s ` A ) ) = 0 )' % (A2, F, F))
    m0 = w.s([w.s([z0], 'oveq2d', '( %s -> ( t x. ( ( %s ` B ) - ( %s ` A ) ) ) = ( t x. 0 ) )' % (A2, F, F)),
              w.s([w.s([tr], 'recnd', '( %s -> t e. CC )' % A2)], 'mul01d', '( %s -> ( t x. 0 ) = 0 )' % A2)], 'eqtrd',
             '( %s -> ( t x. ( ( %s ` B ) - ( %s ` A ) ) ) = 0 )' % (A2, F, F))
    v = w.s([w.s([lin, w.s([m0], 'oveq2d', '( %s -> ( ( %s ` A ) + ( t x. ( ( %s ` B ) - ( %s ` A ) ) ) ) = ( ( %s ` A ) + 0 ) )' % (A2, F, F, F, F))], 'eqtrd',
                 '( %s -> ( %s ` %s ) = ( ( %s ` A ) + 0 ) )' % (A2, F, L, F)),
             w.s([w.s([fa], 'recnd', '( %s -> ( %s ` A ) e. CC )' % (A2, F))], 'addridd', '( %s -> ( ( %s ` A ) + 0 ) = ( %s ` A ) )' % (A2, F, F))],
            'eqtrd', '( %s -> ( %s ` %s ) = ( %s ` A ) )' % (A2, F, L, F))
    ueq = w.s([], 'simpr', '( %s -> u = %s )' % (A3, L))
    fu = w.s([ueq], 'fveq2d', '( %s -> ( %s ` u ) = ( %s ` %s ) )' % (A3, F, F, L))
    tgt = w.s([fu, w.s([v], 'adantr', '( %s -> ( %s ` %s ) = ( %s ` A ) )' % (A3, F, L, F))], 'eqtrd',
              '( %s -> ( %s ` u ) = ( %s ` A ) )' % (A3, F, F))
    imp = w.s([tgt], 'ex', '( %s -> ( u = %s -> ( %s ` u ) = ( %s ` A ) ) )' % (A2, L, F, F))
    rl = w.s([imp], 'rexlimdva', '( %s -> ( E. t e. %s u = %s -> ( %s ` u ) = ( %s ` A ) ) )' % (A1, U01, L, F, F))
    pt = w.s([rl, ex], 'mpd', '( %s -> ( %s ` u ) = ( %s ` A ) )' % (A1, F, F))
    w.qed([pt], 'ralrimiva', '( %s -> A. u e. ( A cseg B ) ( %s ` u ) = ( %s ` A ) )' % (A0, F, F)); run(w)


coordconst('cseghim', 'On a horizontal segment the imaginary part is constant.', 'Im', 'imcl', 'cseglinim')
coordconst('csegvre', 'On a vertical segment the real part is constant.', 'Re', 'recl', 'cseglinre')

GEOH = '( A e. CC /\\ B e. CC /\\ ( Im ` A ) = ( Im ` B ) )'
GEOV = '( A e. CC /\\ B e. CC /\\ ( Re ` A ) = ( Re ` B ) )'


def segdd(label, desc, GEO, F, clab, cons, hyp, body):
    w = W(label, desc)
    A0 = '( %s /\\ ( P e. CC /\\ %s ) )' % (GEO, hyp)
    A1 = '( %s /\\ u e. ( A cseg B ) )' % A0
    geo = w.s([], 'simpl', '( %s -> %s )' % (A0, GEO))
    pn = w.s([], 'simpr', '( %s -> ( P e. CC /\\ %s ) )' % (A0, hyp))
    ac = w.s([geo, w.inst('simp1')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([geo, w.inst('simp2')], 'syl', '( %s -> B e. CC )' % A0)
    pc = w.s([pn, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    hy = w.s([pn, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, hyp))
    con = w.s([geo, w.inst(cons)], 'syl', '( %s -> A. u e. ( A cseg B ) ( %s ` u ) = ( %s ` A ) )' % (A0, F, F))
    umem = w.s([], 'simpr', '( %s -> u e. ( A cseg B ) )' % A1)
    ac1 = w.s([ac], 'adantr', '( %s -> A e. CC )' % A1)
    bc1 = w.s([bc], 'adantr', '( %s -> B e. CC )' % A1)
    pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
    hy1 = w.s([hy], 'adantr', '( %s -> %s )' % (A1, hyp))
    uc = w.s([w.s([ac1, bc1, w.inst('csegcl')], 'syl2anc', '( %s -> ( A cseg B ) C_ CC )' % A1), umem], 'sseldd', '( %s -> u e. CC )' % A1)
    cst = w.s([w.s([con], 'adantr', '( %s -> A. u e. ( A cseg B ) ( %s ` u ) = ( %s ` A ) )' % (A1, F, F)), umem, w.inst('rspa')], 'syl2anc',
              '( %s -> ( %s ` u ) = ( %s ` A ) )' % (A1, F, F))
    tgt, txt = body(w, A1, uc, pc1, ac1, hy1, cst, clab)
    w.qed([tgt], 'ralrimiva', '( %s -> A. u e. ( A cseg B ) %s )' % (A0, txt)); run(w)


def bodyim(w, A1, uc, pc, ac, hy, cst, clab):
    E = '( u - P )'
    ec = w.s([uc, pc], 'subcld', '( %s -> %s e. CC )' % (A1, E))
    ims = w.s([uc, pc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` %s ) = ( ( Im ` u ) - ( Im ` P ) ) )' % (A1, E))
    ims2 = w.s([ims, w.s([cst], 'oveq1d', '( %s -> ( ( Im ` u ) - ( Im ` P ) ) = ( ( Im ` A ) - ( Im ` P ) ) )' % A1)], 'eqtrd',
               '( %s -> ( Im ` %s ) = ( ( Im ` A ) - ( Im ` P ) ) )' % (A1, E))
    iac = w.s([w.s([ac, w.inst('imcl')], 'syl', '( %s -> ( Im ` A ) e. RR )' % A1)], 'recnd', '( %s -> ( Im ` A ) e. CC )' % A1)
    ipc = w.s([w.s([pc, w.inst('imcl')], 'syl', '( %s -> ( Im ` P ) e. RR )' % A1)], 'recnd', '( %s -> ( Im ` P ) e. CC )' % A1)
    ne = w.s([iac, ipc, hy], 'subne0d', '( %s -> ( ( Im ` A ) - ( Im ` P ) ) =/= 0 )' % A1)
    ne2 = w.s([ims2, ne], 'eqnetrd', '( %s -> ( Im ` %s ) =/= 0 )' % (A1, E))
    return w.s([ec, ne2, w.inst('elslitim')], 'syl2anc', '( %s -> %s e. %s )' % (A1, E, DD)), '%s e. %s' % (E, DD)


def bodyre(E, swap):
    def f(w, A1, uc, pc, ac, hy, cst, clab):
        X, Y = ('u', 'P') if not swap else ('P', 'u')
        ec = w.s([uc, pc] if not swap else [pc, uc], 'subcld', '( %s -> %s e. CC )' % (A1, E))
        rs = w.s([w.s([], 'id', '') ] if False else ([uc, pc] if not swap else [pc, uc]) + [w.inst('resub')], 'syl2anc',
                 '( %s -> ( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) ) )' % (A1, E, X, Y))
        if not swap:
            rs2 = w.s([rs, w.s([cst], 'oveq1d', '( %s -> ( ( Re ` u ) - ( Re ` P ) ) = ( ( Re ` A ) - ( Re ` P ) ) )' % A1)], 'eqtrd',
                      '( %s -> ( Re ` %s ) = ( ( Re ` A ) - ( Re ` P ) ) )' % (A1, E))
            DIF = '( ( Re ` A ) - ( Re ` P ) )'
            pos = w.s([hy, w.s([w.s([pc, w.inst('recl')], 'syl', '( %s -> ( Re ` P ) e. RR )' % A1),
                                w.s([ac, w.inst('recl')], 'syl', '( %s -> ( Re ` A ) e. RR )' % A1)], 'posdifd',
                               '( %s -> ( ( Re ` P ) < ( Re ` A ) <-> 0 < %s ) )' % (A1, DIF))], 'mpbid', '( %s -> 0 < %s )' % (A1, DIF))
        else:
            rs2 = w.s([rs, w.s([cst], 'oveq2d', '( %s -> ( ( Re ` P ) - ( Re ` u ) ) = ( ( Re ` P ) - ( Re ` A ) ) )' % A1)], 'eqtrd',
                      '( %s -> ( Re ` %s ) = ( ( Re ` P ) - ( Re ` A ) ) )' % (A1, E))
            DIF = '( ( Re ` P ) - ( Re ` A ) )'
            pos = w.s([hy, w.s([w.s([ac, w.inst('recl')], 'syl', '( %s -> ( Re ` A ) e. RR )' % A1),
                                w.s([pc, w.inst('recl')], 'syl', '( %s -> ( Re ` P ) e. RR )' % A1)], 'posdifd',
                               '( %s -> ( ( Re ` A ) < ( Re ` P ) <-> 0 < %s ) )' % (A1, DIF))], 'mpbid', '( %s -> 0 < %s )' % (A1, DIF))
        pos2 = w.s([pos, rs2], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A1, E))
        return w.s([ec, pos2, w.inst('elslitre')], 'syl2anc', '( %s -> %s e. %s )' % (A1, E, DD)), '%s e. %s' % (E, DD)
    return f


segdd('csegdd1', 'A horizontal segment off the height of P has z - P in the slit plane.',
      GEOH, 'Im', 'imcl', 'cseghim', '( Im ` A ) =/= ( Im ` P )', bodyim)
segdd('csegdd2', 'A vertical segment to the right of P has z - P in the slit plane.',
      GEOV, 'Re', 'recl', 'csegvre', '( Re ` P ) < ( Re ` A )', bodyre('( u - P )', False))
segdd('csegdd3', 'A vertical segment to the left of P has P - z in the slit plane.',
      GEOV, 'Re', 'recl', 'csegvre', '( Re ` A ) < ( Re ` P )', bodyre('( P - u )', True))
