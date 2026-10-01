"""Sortie ZD2: zd2thr (Lean thresholds_eventually at the constants 2 10^14 CTau and 320000 C12 C11)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *


def gen_thr():
    w = W('zd2thr', 'The machine thresholds (Lean ` thresholds_eventually ` ): beyond some ` u >_ 1 ` , ` 200 <_ log v ` , (T1) ` 2 10 ^ 14 CTau log v <_ v ^c ( 79 / 4000 ) ` and (T2) ` 320000 C12 C11 log v <_ v ^c ( 13 / 500 ) ` hold ( ~ zdthresh at the two constants).')
    k = closed_consts(w)
    pa = w.s([k[A1C][0], k[A1C][1]], 'pm3.2i', '( %s e. RR /\\ 0 <_ %s )' % (A1C, A1C))
    pb = w.s([k[B2C][0], k[B2C][1]], 'pm3.2i', '( %s e. RR /\\ 0 <_ %s )' % (B2C, B2C))
    w.qed([pa, pb, w.inst('zdthresh')], 'mp2an', S['zd2thr'])
    return go(w)


if __name__ == '__main__':
    gen_thr()
