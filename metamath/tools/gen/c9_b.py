"""Sortie C9: square geometry (sqfrd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from c8_n import sqparts, sqre_at, sqcc, reim_leaves
from c9_freeze import S as FS
import lin
lin.FASTPATH = True


def decode(w, A0, um, ac, bc, a, b, sq, U='U'):
    """from um : ( A0 -> U e. ( a crect b ) ): [U e. CC, Re a <_ Re U, Re U <_ Re b, Im a <_ Im U, Im U <_ Im b]"""
    EL = '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (U, U, a, b, U, a, b)
    el = w.s([um, w.s([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, a, b)), w.inst('elcrect')], 'syl', '( %s -> ( %s e. %s <-> %s ) )' % (A0, U, sq, EL))],
             'mpbid', '( %s -> %s )' % (A0, EL))
    out = [w.s([el, w.inst('simp1')], 'syl', '( %s -> %s e. CC )' % (A0, U))]
    for part, k, lem in (('Re', 'simp2', 'recld'), ('Im', 'simp3', 'imcld')):
        mem = w.s([el, w.inst(k)], 'syl', '( %s -> ( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) )' % (A0, part, U, part, a, part, b))
        E2 = '( ( %s ` %s ) e. RR /\\ ( %s ` %s ) <_ ( %s ` %s ) /\\ ( %s ` %s ) <_ ( %s ` %s ) )' % (part, U, part, a, part, U, part, U, part, b)
        e2 = w.s([mem, w.s([w.s([ac], lem, '( %s -> ( %s ` %s ) e. RR )' % (A0, part, a)), w.s([bc], lem, '( %s -> ( %s ` %s ) e. RR )' % (A0, part, b)), w.inst('elicc2')], 'syl2anc',
                           '( %s -> ( ( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> %s ) )' % (A0, part, U, part, a, part, b, E2))], 'mpbid', '( %s -> %s )' % (A0, E2))
        out.append(w.s([e2, w.inst('simp2')], 'syl', '( %s -> ( %s ` %s ) <_ ( %s ` %s ) )' % (A0, part, a, part, U)))
        out.append(w.s([e2, w.inst('simp3')], 'syl', '( %s -> ( %s ` %s ) <_ ( %s ` %s ) )' % (A0, part, U, part, b)))
    return out


def gen_sqfrd():
    w = W('sqfrd', 'A point of the square of half-side ` T ` about ` C ` lies strictly inside the square of half-side ` V ` , at distance at least ` R ` from its frame, when ` T + R <_ V ` .')
    SQT = SQ('C', 'T')
    at, bt = SQA('C', 'T'), SQB('C', 'T')
    av, bv = SQA('C', 'V'), SQB('C', 'V')
    X1 = '( C e. CC /\\ ( T e. RR /\\ R e. RR+ /\\ V e. RR ) )'
    X2 = '( ( T + R ) <_ V /\\ U e. %s )' % SQT
    A0 = '( %s /\\ %s )' % (X1, X2)
    cs = w.s([], 'simpll', '( %s -> C e. CC )' % A0)
    t3 = w.s([], 'simplr', '( %s -> ( T e. RR /\\ R e. RR+ /\\ V e. RR ) )' % A0)
    ts = w.s([t3, w.inst('simp1')], 'syl', '( %s -> T e. RR )' % A0)
    rp = w.s([t3, w.inst('simp2')], 'syl', '( %s -> R e. RR+ )' % A0)
    vs = w.s([t3, w.inst('simp3')], 'syl', '( %s -> V e. RR )' % A0)
    le = w.s([], 'simprl', '( %s -> ( T + R ) <_ V )' % A0)
    um = w.s([], 'simprr', '( %s -> U e. %s )' % (A0, SQT))
    rr = w.s([rp], 'rpred', '( %s -> R e. RR )' % A0)
    r0 = w.s([rp], 'rpgt0d', '( %s -> 0 < R )' % A0)
    pt = sqparts(w, A0, sqre_at(w, A0, cs, ts, r='T'), r='T')
    pv = sqparts(w, A0, sqre_at(w, A0, cs, vs, r='V'), r='V')
    atc, btc = sqcc(w, A0, cs, ts, r='T')
    avc, bvc = sqcc(w, A0, cs, vs, r='V')
    d = decode(w, A0, um, atc, btc, at, bt, SQT)
    us = d[0]
    lv = reim_leaves(w, A0, {at: atc, bt: btc, av: avc, bv: bvc, 'U': us, 'C': cs})
    lv['T'] = ts; lv['R'] = rr; lv['V'] = vs
    # strict interior and the gaps
    RU, IU = '( Re ` U )', '( Im ` U )'
    lt = [lin8(w, A0, [pv[0], pt[0], d[1], le, r0], '( Re ` %s ) < %s' % (av, RU), lv),
          lin8(w, A0, [pv[1], pt[1], d[2], le, r0], '%s < ( Re ` %s )' % (RU, bv), lv),
          lin8(w, A0, [pv[2], pt[2], d[3], le, r0], '( Im ` %s ) < %s' % (av, IU), lv),
          lin8(w, A0, [pv[3], pt[3], d[4], le, r0], '%s < ( Im ` %s )' % (IU, bv), lv)]
    gp = [lin8(w, A0, [pv[0], pt[0], d[1], le], 'R <_ ( %s - ( Re ` %s ) )' % (RU, av), lv),
          lin8(w, A0, [pv[1], pt[1], d[2], le], 'R <_ ( ( Re ` %s ) - %s )' % (bv, RU), lv),
          lin8(w, A0, [pv[2], pt[2], d[3], le], 'R <_ ( %s - ( Im ` %s ) )' % (IU, av), lv),
          lin8(w, A0, [pv[3], pt[3], d[4], le], 'R <_ ( ( Im ` %s ) - %s )' % (bv, IU), lv)]
    INT = INTG(av, bv, 'U')
    j1 = w.s([lt[0], lt[1]], 'jca', '( %s -> ( ( Re ` %s ) < %s /\\ %s < ( Re ` %s ) ) )' % (A0, av, RU, RU, bv))
    j2 = w.s([lt[2], lt[3]], 'jca', '( %s -> ( ( Im ` %s ) < %s /\\ %s < ( Im ` %s ) ) )' % (A0, av, IU, IU, bv))
    inn = w.s([us, w.s([j1, j2], 'jca', '( %s -> %s )' % (A0, INT[len('( U e. CC /\\ '):-2]))], 'jca', '( %s -> %s )' % (A0, INT))
    RBD = RBDG(av, bv, 'U', 'R')
    g1 = w.s([gp[0], gp[1]], 'jca', '( %s -> ( R <_ ( %s - ( Re ` %s ) ) /\\ R <_ ( ( Re ` %s ) - %s ) ) )' % (A0, RU, av, bv, RU))
    g2 = w.s([gp[2], gp[3]], 'jca', '( %s -> ( R <_ ( %s - ( Im ` %s ) ) /\\ R <_ ( ( Im ` %s ) - %s ) ) )' % (A0, IU, av, bv, IU))
    rbd = w.s([rr, w.s([g1, g2], 'jca', '( %s -> %s )' % (A0, RBD[len('( R e. RR /\\ '):-2]))], 'jca', '( %s -> %s )' % (A0, RBD))
    DIS = 'A. u e. %s R <_ ( abs ` ( u - U ) )' % FRG(av, bv)
    dis = w.s([w.s([avc, bvc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, av, bv)), inn, rbd, w.inst('crectdis')], 'syl3anc', '( %s -> %s )' % (A0, DIS))
    goal = '( %s -> ( %s /\\ %s ) )' % (A0, INT, DIS)
    assert goal == FS['sqfrd'], (goal, FS['sqfrd'])
    w.qed([inn, dis], 'jca', goal)
    return run8(w)


if __name__ == '__main__':
    gen_sqfrd()
