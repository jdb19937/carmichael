"""Sortie T21b: shared generator helpers (label index over carmichael.mm + sorties/t21b.mm)."""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21blib import *
import t21alib as _t21a
import t21blib as _t21b
import num, lin
import cl as _cl
from cl import lift, split_imp
from tm import W
lin.FASTPATH = True
lin.MAXDEG = 6
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
only = [a for a in sys.argv[1:] if not a.startswith('-')]


def _own(label):
    txt = open(os.path.join(ROOT, 'sorties', 't21b.mm')).read()
    m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
    return ' '.join(m.group(1).split()) if m else None


_old_thm = _t21a.thm


def thm(lab):
    if lab in SB:
        return '|- ' + SB[lab]
    o = _own(lab)
    if o is not None:
        return '|- ' + o
    return _old_thm(lab)


_t21a.thm = thm
_old_stmt = _t21a.stmt


def stmt2(lab):
    if lab in SB:
        return SB[lab]
    o = _own(lab)
    if o is not None:
        return o
    try:
        return _old_stmt(lab)
    except FileNotFoundError:
        txt = open(os.path.join(ROOT, 'carmichael.mm')).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(lab), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
        raise KeyError(lab)


_t21a.stmt = stmt2
ap = _t21a.ap


def unpackA(w, ante):
    return _t21a.unpack(w, ante)


def go(w):
    """check cited labels, then add (unless the command line names other labels)"""
    if only and w.label not in only:
        return True
    return _t21a.run(w)


def A1(w, ante, step_closed, f):
    """lift a closed step to ( ante -> f )"""
    return w.s([step_closed], 'a1i', '( %s -> %s )' % (ante, f))


def S_(w, ante):
    return lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
