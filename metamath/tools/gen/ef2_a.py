"""Sortie EF2: the DiskData basics (ef2x2, ef2cnz)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import c9_h
patch(c9_h)
from c9_h import c0_facts
import cl as _cl
import lin
lin.FASTPATH = True


def gen_x2():
    w = W('ef2x2', 'Lean ` DiskData.scale_two_le ` : the scale ` A ( abs T + 2 ) ` of a ` DiskData ` function is at least 2.')
    A0, _ = ante_of(S['ef2x2'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dd = s([], 'simpl', DD()); tr = s([], 'simpr', 'T e. RR')
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    tc = s([tr], 'recnd', 'T e. CC')
    at = s([tc], 'abscld', '( abs ` T ) e. RR'); ag = s([tc], 'absge0d', '0 <_ ( abs ` T )')
    lv = {'A': ar, '( abs ` T )': at}
    pr = s([ar, at, s([numst(w, A0, '0', 'RR'), numst(w, A0, '1', 'RR'), ar, lin8(w, A0, [], '0 <_ 1', {}), a1], 'letrd', '0 <_ A'), ag], 'mulge0d', '0 <_ ( A x. ( abs ` T ) )')
    lv['( A x. ( abs ` T ) )'] = s([ar, at], 'remulcld', '( A x. ( abs ` T ) ) e. RR')
    ex = s([s([ar], 'recnd', 'A e. CC'), s([at], 'recnd', '( abs ` T ) e. CC'), numst(w, A0, '2', 'CC')], 'adddid',
           '%s = ( ( A x. ( abs ` T ) ) + ( A x. 2 ) )' % XA())
    le = lin8(w, A0, [pr, a1], '2 <_ ( ( A x. ( abs ` T ) ) + ( A x. 2 ) )', lv)
    w.qed([le, ex], 'breqtrrd', S['ef2x2'])
    return run8(w)


def gen_cnz():
    w = W('ef2cnz', 'Lean ` DiskData.center_ne_zero ` : a ` DiskData ` function does not vanish at ` 2 + i T ` .')
    A0, _ = ante_of(S['ef2cnz'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dd = s([], 'simpl', DD()); tr = s([], 'simpr', 'T e. RR')
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    lo, bd = dd_at(w, A0, allt, 'T', tr)
    c0, re0, im0 = c0_facts(w, A0, tr)
    FC = '( F ` %s )' % CT('T')
    hp = s([s([numst(w, A0, '0', 'RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (CT('T'), HP0, CT('T'), CT('T'))),
            s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % CT('T'))], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (CT('T'), CT('T')))],
           'mpbird', '%s e. %s' % (CT('T'), HP0))
    fc = fcc(w, A0, hol, 'F', HP0, CT('T'), hp)
    ab = s([fc], 'abscld', '( abs ` %s ) e. RR' % FC)
    gt = lin8(w, A0, [lo], '0 < ( abs ` %s )' % FC, {'( abs ` %s )' % FC: ab})
    w.qed([s([fc, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (FC, FC)), gt], 'mpbird', S['ef2cnz'])
    return run8(w)


if __name__ == '__main__':
    gen_x2()
    gen_cnz()
