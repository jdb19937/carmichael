"""Sortie T21b: t21thm (theta_AP_T21 from DensityInputs)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from c8lib import tsub


def gen_thm():
    w = W('t21thm', 'T2.1 (Lean ` theta_AP_T21 ` , routez/Z0a-ledger.md section 4): under the two zone-density inputs ` DensityInputs = LogFreeDensity /\\ LoggedDensity ` , for ` 0 < E < 1 / 3 ` there are ` D ` , ` x_2 ` and exceptional sets ` bad ( x ) ` of at most ` D ` conductors ` >_ 2 ` such that ` abs ( theta ( y ; d , a ) - y / phi ( d ) ) <_ E y / phi ( d ) ` for ` x >_ x_2 ` , ` a ` a unit mod ` d <_ x ^ ( 191 / 900 ) ` , ` d x ^ ( 709 / 900 ) <_ y <_ x ` and no member of ` bad ( x ) ` dividing ` d ` ( ~ t21cor ).')
    A0, concl = split_imp(SB['t21thm'])
    GOALt = concl
    EH_ = '( E e. RR /\\ 0 < E /\\ E < ( 1 / 3 ) )'
    R_ = '( %s -> %s )' % (EH_, GOALt)
    LF = lambda g, c: '( ( %s e. RR /\\ %s e. RR ) /\\ ( 1 <_ %s /\\ 1 <_ %s /\\ %s <_ 2 ) /\\ A. m e. NN %s )' % (g, c, g, c, c, LFD_BODY(g, c, 'm'))
    LGb = lambda c: '( ( ( h e. RR /\\ w e. RR /\\ %s e. RR ) /\\ k e. NN0 ) /\\ ( ( 1 <_ h /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) ) /\\ ( 1 <_ %s /\\ %s <_ ( 5 / 4 ) ) ) /\\ A. m e. NN %s )' % (c, c, c, LGD_BODY('h', 'w', c, 'k', 'm'))
    assert LOGFREE == 'E. g E. c %s' % LF('g', 'c'), LOGFREE[:100]
    assert LOGGED == 'E. h E. w E. c E. k %s' % LGb('c'), LOGGED[:100]
    COR = tsub(SB['t21cor'], {'G': 'g', 'C': 'c', 'H': 'h', 'P': 'w', 'B': 'n', 'K': 'k'})
    ca, cc_ = split_imp(COR)
    assert ca == '( ( %s /\\ %s ) /\\ %s )' % (LF('g', 'c'), LGb('n'), EH_), ca[:200]
    cor = w.s([], 't21cor', COR)
    c1 = w.s([cor], 'exp31', '( %s -> ( %s -> %s ) )' % (LF('g', 'c'), LGb('n'), R_))
    c2 = w.s([c1], 'com12', '( %s -> ( %s -> %s ) )' % (LGb('n'), LF('g', 'c'), R_))
    c3 = w.s([c2], 'exlimivv', '( E. n E. k %s -> ( %s -> %s ) )' % (LGb('n'), LF('g', 'c'), R_))
    c4 = w.s([c3], 'exlimivv', '( E. h E. w E. n E. k %s -> ( %s -> %s ) )' % (LGb('n'), LF('g', 'c'), R_))
    LGn = 'E. h E. w E. n E. k %s' % LGb('n')
    c5 = w.s([c4], 'com12', '( %s -> ( %s -> %s ) )' % (LF('g', 'c'), LGn, R_))
    c6 = w.s([c5], 'exlimivv', '( %s -> ( %s -> %s ) )' % (LOGFREE, LGn, R_))
    # LOGGED <-> LGn (rename c -> n)
    e = 'c = n'
    k1, _ = w.wcongr(LGb('c'), {'c': 'n'}, e, {'c': w.s([], 'id', '( c = n -> c = n )')})
    k2 = w.s([k1], 'exbidv', '( %s -> ( E. k %s <-> E. k %s ) )' % (e, LGb('c'), LGb('n')))
    k3 = w.s([k2], 'cbvexvw', '( E. c E. k %s <-> E. n E. k %s )' % (LGb('c'), LGb('n')))
    k4 = w.s([k3], 'exbii', '( E. w E. c E. k %s <-> E. w E. n E. k %s )' % (LGb('c'), LGb('n')))
    k5 = w.s([k4], 'exbii', '( %s <-> %s )' % (LOGGED, LGn))
    c7 = w.s([c6, k5], 'x', 'x') if False else None
    c7 = w.s([k5, c6], 'syl6bir' if False else 'x', 'x') if False else None
    # ( LOGFREE -> ( LOGGED -> R ) )
    c7 = w.s([c6, w.s([k5], 'biimpi', '( %s -> %s )' % (LOGGED, LGn))], 'x', 'x') if False else None
    c7 = w.s([w.s([k5], 'biimpi', '( %s -> %s )' % (LOGGED, LGn)), c6], 'syl9r' if False else 'x', 'x') if False else None
    li = w.s([k5], 'biimpi', '( %s -> %s )' % (LOGGED, LGn))
    c8 = w.s([c6], 'imp', '( ( %s /\\ %s ) -> %s )' % (LOGFREE, LGn, R_))
    c9 = w.s([li], 'anim2i', '( ( %s /\\ %s ) -> ( %s /\\ %s ) )' % (LOGFREE, LOGGED, LOGFREE, LGn))
    c10 = w.s([c9, c8], 'syl', '( ( %s /\\ %s ) -> %s )' % (LOGFREE, LOGGED, R_))
    w.qed([c10], 'imp', SB['t21thm'])
    return go(w)


if __name__ == '__main__':
    gen_thm()
