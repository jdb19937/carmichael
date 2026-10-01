"""Sortie C8: the open rectangle (orectopn, orectss, crectorect)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *

OR = ORECT('A', 'B')
IRE = '( ( Re ` A ) (,) ( Re ` B ) )'
IIM = '( ( Im ` A ) (,) ( Im ` B ) )'
PRE = "( `' Re \" %s )" % IRE
PIM = "( `' Im \" %s )" % IIM


def gen_orectopn():
    w = W('orectopn', 'The open rectangle is an open set of the complex plane.')
    s1 = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    s3 = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    s4 = w.s([], 'tgioo4', '( topGen ` ran (,) ) = ( %s |`t RR )' % TOP)
    s5 = w.s([s1, s3, s4], 'cncfcn', '( ( CC C_ CC /\\ RR C_ CC ) -> ( CC -cn-> RR ) = ( %s Cn ( topGen ` ran (,) ) ) )' % TOP)
    s8 = w.s([w.s([], 'ssid', 'CC C_ CC'), w.s([], 'ax-resscn', 'RR C_ CC'), s5], 'mp2an', '( CC -cn-> RR ) = ( %s Cn ( topGen ` ran (,) ) )' % TOP)
    re = w.s([w.s([], 'recncf', 'Re e. ( CC -cn-> RR )'), s8], 'eleqtri', 'Re e. ( %s Cn ( topGen ` ran (,) ) )' % TOP)
    im = w.s([w.s([], 'imcncf', 'Im e. ( CC -cn-> RR )'), s8], 'eleqtri', 'Im e. ( %s Cn ( topGen ` ran (,) ) )' % TOP)
    o1 = w.s([re, w.s([], 'iooretop', '%s e. ( topGen ` ran (,) )' % IRE), w.inst('cnima')], 'mp2an', '%s e. %s' % (PRE, TOP))
    o2 = w.s([im, w.s([], 'iooretop', '%s e. ( topGen ` ran (,) )' % IIM), w.inst('cnima')], 'mp2an', '%s e. %s' % (PIM, TOP))
    w.qed([w.s([s1], 'cnfldtop', '%s e. Top' % TOP), o1, o2, w.inst('inopn')], 'mp3an', '%s e. %s' % (OR, TOP))
    return run8(w)


def preim(w, ante, xin_or, x='x'):
    """from ( ante -> x e. OR ): steps x e. CC, ( Re ` x ) e. IRE, ( Im ` x ) e. IIM"""
    both = w.s([xin_or, w.s([], 'elin', '( %s e. %s <-> ( %s e. %s /\\ %s e. %s ) )' % (x, OR, x, PRE, x, PIM))], 'sylib',
               '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ante, x, PRE, x, PIM))
    refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    imfn = w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC')
    e1 = w.s([refn, w.inst('elpreima')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. %s ) )' % (x, PRE, x, x, IRE))
    e2 = w.s([imfn, w.inst('elpreima')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ ( Im ` %s ) e. %s ) )' % (x, PIM, x, x, IIM))
    r = w.s([w.s([both, w.inst('simpl')], 'syl', '( %s -> %s e. %s )' % (ante, x, PRE)), e1], 'sylib', '( %s -> ( %s e. CC /\\ ( Re ` %s ) e. %s ) )' % (ante, x, x, IRE))
    i = w.s([w.s([both, w.inst('simpr')], 'syl', '( %s -> %s e. %s )' % (ante, x, PIM)), e2], 'sylib', '( %s -> ( %s e. CC /\\ ( Im ` %s ) e. %s ) )' % (ante, x, x, IIM))
    xc = w.s([r, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (ante, x))
    xr = w.s([r, w.inst('simpr')], 'syl', '( %s -> ( Re ` %s ) e. %s )' % (ante, x, IRE))
    xi = w.s([i, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) e. %s )' % (ante, x, IIM))
    return xc, xr, xi, e1, e2, both


def gen_orectss():
    w = W('orectss', 'The open rectangle lies in the closed one.')
    A0 = AB
    A1 = '( %s /\\ x e. %s )' % (A0, OR)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (A1, OR))
    xc, xr, xi, _, _, _ = preim(w, A1, xin)
    r2 = w.s([w.s([], 'ioossicc', '%s C_ ( ( Re ` A ) [,] ( Re ` B ) )' % IRE), xr], 'sselid', '( %s -> ( Re ` x ) e. ( ( Re ` A ) [,] ( Re ` B ) ) )' % A1)
    i2 = w.s([w.s([], 'ioossicc', '%s C_ ( ( Im ` A ) [,] ( Im ` B ) )' % IIM), xi], 'sselid', '( %s -> ( Im ` x ) e. ( ( Im ` A ) [,] ( Im ` B ) ) )' % A1)
    ab = w.s([], 'simpl', '( %s -> %s )' % (A1, AB))
    el = w.s([ab, w.inst('elcrect')], 'syl', '( %s -> ( x e. ( A crect B ) <-> ( x e. CC /\\ ( Re ` x ) e. ( ( Re ` A ) [,] ( Re ` B ) ) /\\ ( Im ` x ) e. ( ( Im ` A ) [,] ( Im ` B ) ) ) ) )' % A1)
    xk = w.s([w.s([xc, r2, i2], '3jca', '( %s -> ( x e. CC /\\ ( Re ` x ) e. ( ( Re ` A ) [,] ( Re ` B ) ) /\\ ( Im ` x ) e. ( ( Im ` A ) [,] ( Im ` B ) ) ) )' % A1), el],
             'mpbird', '( %s -> x e. ( A crect B ) )' % A1)
    w.qed([w.s([xk], 'ex', '( %s -> ( x e. %s -> x e. ( A crect B ) ) )' % (A0, OR))], 'ssrdv', '( %s -> %s C_ ( A crect B ) )' % (A0, OR))
    return run8(w)


def gen_crectorect():
    w = W('crectorect', 'A closed rectangle whose corners lie strictly inside a second rectangle lies in the open second rectangle.')
    STR = '( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` Q ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` Q ) < ( Im ` B ) ) )'
    A0 = '( ( A e. CC /\\ B e. CC ) /\\ ( P e. CC /\\ Q e. CC ) /\\ %s )' % STR
    A1 = '( %s /\\ x e. ( P crect Q ) )' % A0
    a0 = w.s([], 'simpl', '( %s -> %s )' % (A1, A0))
    ab = w.s([a0, w.inst('simp1')], 'syl', '( %s -> %s )' % (A1, AB))
    pq = w.s([a0, w.inst('simp2')], 'syl', '( %s -> ( P e. CC /\\ Q e. CC ) )' % A1)
    st = w.s([a0, w.inst('simp3')], 'syl', '( %s -> %s )' % (A1, STR))
    sr = w.s([st, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` Q ) < ( Re ` B ) ) )' % A1)
    si = w.s([st, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` Q ) < ( Im ` B ) ) )' % A1)
    xin = w.s([], 'simpr', '( %s -> x e. ( P crect Q ) )' % A1)
    # rectel on ( P crect Q )
    el = w.s([pq, w.inst('elcrect')], 'syl', '( %s -> ( x e. ( P crect Q ) <-> ( x e. CC /\\ ( Re ` x ) e. ( ( Re ` P ) [,] ( Re ` Q ) ) /\\ ( Im ` x ) e. ( ( Im ` P ) [,] ( Im ` Q ) ) ) ) )' % A1)
    tri = w.s([xin, el], 'mpbid', '( %s -> ( x e. CC /\\ ( Re ` x ) e. ( ( Re ` P ) [,] ( Re ` Q ) ) /\\ ( Im ` x ) e. ( ( Im ` P ) [,] ( Im ` Q ) ) ) )' % A1)
    xc = w.s([tri, w.inst('simp1')], 'syl', '( %s -> x e. CC )' % A1)
    rei = w.s([tri, w.inst('simp2')], 'syl', '( %s -> ( Re ` x ) e. ( ( Re ` P ) [,] ( Re ` Q ) ) )' % A1)
    imi = w.s([tri, w.inst('simp3')], 'syl', '( %s -> ( Im ` x ) e. ( ( Im ` P ) [,] ( Im ` Q ) ) )' % A1)
    pc = w.s([pq, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A1)
    qc = w.s([pq, w.inst('simpr')], 'syl', '( %s -> Q e. CC )' % A1)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A1)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A1)
    rp = w.s([pc], 'recld', '( %s -> ( Re ` P ) e. RR )' % A1); rq = w.s([qc], 'recld', '( %s -> ( Re ` Q ) e. RR )' % A1)
    ip = w.s([pc], 'imcld', '( %s -> ( Im ` P ) e. RR )' % A1); iq = w.s([qc], 'imcld', '( %s -> ( Im ` Q ) e. RR )' % A1)
    ra = w.s([ac], 'recld', '( %s -> ( Re ` A ) e. RR )' % A1); rb = w.s([bc], 'recld', '( %s -> ( Re ` B ) e. RR )' % A1)
    ia = w.s([ac], 'imcld', '( %s -> ( Im ` A ) e. RR )' % A1); ib = w.s([bc], 'imcld', '( %s -> ( Im ` B ) e. RR )' % A1)
    r3 = w.s([w.s([rp, rq, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` x ) e. ( ( Re ` P ) [,] ( Re ` Q ) ) <-> ( ( Re ` x ) e. RR /\\ ( Re ` P ) <_ ( Re ` x ) /\\ ( Re ` x ) <_ ( Re ` Q ) ) ) )' % A1), rei],
             'mpbid', '( %s -> ( ( Re ` x ) e. RR /\\ ( Re ` P ) <_ ( Re ` x ) /\\ ( Re ` x ) <_ ( Re ` Q ) ) )' % A1)
    i3 = w.s([w.s([ip, iq, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Im ` x ) e. ( ( Im ` P ) [,] ( Im ` Q ) ) <-> ( ( Im ` x ) e. RR /\\ ( Im ` P ) <_ ( Im ` x ) /\\ ( Im ` x ) <_ ( Im ` Q ) ) ) )' % A1), imi],
             'mpbid', '( %s -> ( ( Im ` x ) e. RR /\\ ( Im ` P ) <_ ( Im ` x ) /\\ ( Im ` x ) <_ ( Im ` Q ) ) )' % A1)
    xr = w.s([r3, w.inst('simp1')], 'syl', '( %s -> ( Re ` x ) e. RR )' % A1)
    xi = w.s([i3, w.inst('simp1')], 'syl', '( %s -> ( Im ` x ) e. RR )' % A1)
    lr1 = w.s([ra, rp, xr, w.s([sr, w.inst('simpl')], 'syl', '( %s -> ( Re ` A ) < ( Re ` P ) )' % A1), w.s([r3, w.inst('simp2')], 'syl', '( %s -> ( Re ` P ) <_ ( Re ` x ) )' % A1)],
              'ltletrd', '( %s -> ( Re ` A ) < ( Re ` x ) )' % A1)
    lr2 = w.s([xr, rq, rb, w.s([r3, w.inst('simp3')], 'syl', '( %s -> ( Re ` x ) <_ ( Re ` Q ) )' % A1), w.s([sr, w.inst('simpr')], 'syl', '( %s -> ( Re ` Q ) < ( Re ` B ) )' % A1)],
              'lelttrd', '( %s -> ( Re ` x ) < ( Re ` B ) )' % A1)
    li1 = w.s([ia, ip, xi, w.s([si, w.inst('simpl')], 'syl', '( %s -> ( Im ` A ) < ( Im ` P ) )' % A1), w.s([i3, w.inst('simp2')], 'syl', '( %s -> ( Im ` P ) <_ ( Im ` x ) )' % A1)],
              'ltletrd', '( %s -> ( Im ` A ) < ( Im ` x ) )' % A1)
    li2 = w.s([xi, iq, ib, w.s([i3, w.inst('simp3')], 'syl', '( %s -> ( Im ` x ) <_ ( Im ` Q ) )' % A1), w.s([si, w.inst('simpr')], 'syl', '( %s -> ( Im ` Q ) < ( Im ` B ) )' % A1)],
              'lelttrd', '( %s -> ( Im ` x ) < ( Im ` B ) )' % A1)
    oir = w.s([w.s([w.s([ra], 'rexrd', '( %s -> ( Re ` A ) e. RR* )' % A1), w.s([rb], 'rexrd', '( %s -> ( Re ` B ) e. RR* )' % A1), w.inst('elioo2')], 'syl2anc',
                   '( %s -> ( ( Re ` x ) e. %s <-> ( ( Re ` x ) e. RR /\\ ( Re ` A ) < ( Re ` x ) /\\ ( Re ` x ) < ( Re ` B ) ) ) )' % (A1, IRE)),
               w.s([xr, lr1, lr2], '3jca', '( %s -> ( ( Re ` x ) e. RR /\\ ( Re ` A ) < ( Re ` x ) /\\ ( Re ` x ) < ( Re ` B ) ) )' % A1)], 'mpbird',
              '( %s -> ( Re ` x ) e. %s )' % (A1, IRE))
    oii = w.s([w.s([w.s([ia], 'rexrd', '( %s -> ( Im ` A ) e. RR* )' % A1), w.s([ib], 'rexrd', '( %s -> ( Im ` B ) e. RR* )' % A1), w.inst('elioo2')], 'syl2anc',
                   '( %s -> ( ( Im ` x ) e. %s <-> ( ( Im ` x ) e. RR /\\ ( Im ` A ) < ( Im ` x ) /\\ ( Im ` x ) < ( Im ` B ) ) ) )' % (A1, IIM)),
               w.s([xi, li1, li2], '3jca', '( %s -> ( ( Im ` x ) e. RR /\\ ( Im ` A ) < ( Im ` x ) /\\ ( Im ` x ) < ( Im ` B ) ) )' % A1)], 'mpbird',
              '( %s -> ( Im ` x ) e. %s )' % (A1, IIM))
    refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    imfn = w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC')
    e1 = w.s([refn, w.inst('elpreima')], 'ax-mp', '( x e. %s <-> ( x e. CC /\\ ( Re ` x ) e. %s ) )' % (PRE, IRE))
    e2 = w.s([imfn, w.inst('elpreima')], 'ax-mp', '( x e. %s <-> ( x e. CC /\\ ( Im ` x ) e. %s ) )' % (PIM, IIM))
    x1 = w.s([w.s([xc, oir], 'jca', '( %s -> ( x e. CC /\\ ( Re ` x ) e. %s ) )' % (A1, IRE)), e1], 'sylibr', '( %s -> x e. %s )' % (A1, PRE))
    x2 = w.s([w.s([xc, oii], 'jca', '( %s -> ( x e. CC /\\ ( Im ` x ) e. %s ) )' % (A1, IIM)), e2], 'sylibr', '( %s -> x e. %s )' % (A1, PIM))
    xo = w.s([w.s([x1, x2], 'jca', '( %s -> ( x e. %s /\\ x e. %s ) )' % (A1, PRE, PIM)),
              w.s([], 'elin', '( x e. %s <-> ( x e. %s /\\ x e. %s ) )' % (OR, PRE, PIM))], 'sylibr', '( %s -> x e. %s )' % (A1, OR))
    w.qed([w.s([xo], 'ex', '( %s -> ( x e. ( P crect Q ) -> x e. %s ) )' % (A0, OR))], 'ssrdv', '( %s -> ( P crect Q ) C_ %s )' % (A0, OR))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_orectopn, gen_orectss, gen_crectorect]:
        g()
