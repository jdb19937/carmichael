"""Sortie C8, section 3: Cauchy's estimate from a given Cauchy identity
(rectintce0g), its one-exceptional-point form (rectintce0x).  rectintce0g is
C1's rectintce0 generator (tools/gen/c1_ce.py) with the holomorphy hypothesis
replaced by continuity plus the Cauchy identity itself; the source is read
from that file and patched, so the two proofs stay in step."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
from c1_lib import *
import c8lib


def ce0g_source():
    L = open(os.path.join(HERE, 'c1_ce.py')).read().split('\n')
    head = '\n'.join(L[4:16])                  # RP .. QF definitions
    body = '\n'.join(L[51:237])
    HC = '( F e. ( D -cn-> CC ) /\\\\ ( A crect B ) C_ D )'
    rep = [
        ("w = W('rectintce0', 'Cauchy estimate of order zero: the value of a holomorphic '",
         "w = W('rectintce0g', 'Cauchy estimate of order zero from a Cauchy identity: the value of a continuous '"),
        ("A0 = '( ( %s /\\\\ %s /\\\\ %s ) /\\\\ ( %s /\\\\ 0 < R ) /\\\\ ( M e. RR /\\\\ %s ) )' % (AB, INT, HOLO, RBD, ALF)",
         "HC = '%s'\nCAU = '%%s = ( %%s x. ( F ` P ) )' %% (RINT(QF(PU), 'A', 'B'), TPI)\n"
         "A00 = '( ( %%s /\\\\ %%s /\\\\ %%s ) /\\\\ ( %%s /\\\\ 0 < R ) /\\\\ ( M e. RR /\\\\ %%s ) )' %% (AB, INT, HC, RBD, ALF)\n"
         "A0 = '( %%s /\\\\ %%s )' %% (A00, CAU)\na00 = w.s([], 'simpl', '( %%s -> %%s )' %% (A0, A00))" % HC),
        ("bs = w.s([], 'simp1', '( %s -> ( %s /\\\\ %s /\\\\ %s ) )' % (A0, AB, INT, HOLO))",
         "bs = w.s([a00, w.inst('simp1')], 'syl', '( %s -> ( %s /\\\\ %s /\\\\ %s ) )' % (A0, AB, INT, HC))"),
        ("rb0 = w.s([], 'simp2', '( %s -> ( %s /\\\\ 0 < R ) )' % (A0, RBD))",
         "rb0 = w.s([a00, w.inst('simp2')], 'syl', '( %s -> ( %s /\\\\ 0 < R ) )' % (A0, RBD))"),
        ("mm = w.s([], 'simp3', '( %s -> ( M e. RR /\\\\ %s ) )' % (A0, ALF))",
         "mm = w.s([a00, w.inst('simp3')], 'syl', '( %s -> ( M e. RR /\\\\ %s ) )' % (A0, ALF))"),
        ("holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))",
         "holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HC))"),
        ("hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)",
         "crd = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)"),
        ("cau = w.s([bs, w.inst('rectintcau')], 'syl', '( %s -> %s = ( %s x. ( F ` P ) ) )' % (A0, RINT(QF(PU), 'A', 'B'), TPI))",
         "cau = w.s([], 'simpr', '( %s -> %s )' % (A0, CAU))"),
        ("dvb = w.s([ssc, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)", ""),
        ("crd = w.s([hss, dvb], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)", ""),
        ("'mpbird', '( %s -> %s <_ %s )' % (A0, GL, GR)); run1(w)", "'mpbird', '( %s -> %s <_ %s )' % (A0, GL, GR))"),
    ]
    for a, b in rep:
        assert a in body, a
        body = body.replace(a, b)
    return head + '\n' + body


def gen_rectintce0g():
    ns = dict(globals())
    exec(ce0g_source(), ns)
    return c8lib.run8(ns['w'])


if __name__ == '__main__':
    for g in [gen_rectintce0g]:
        g()
