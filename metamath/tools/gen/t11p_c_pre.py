"""T11 helper (pool): the straight pieces of Lean's ` poolGoBody ` at the machine.

  tmippr   poolPre_runs: ` dup 2 4 6 ; mulC 5 4 7 6 3 ; incr 7 4 ; dup 7 4 6 ; dup 0 6 4 ; cmpFrag 4 6 ` : the entry ` d ` is
           consumed from 5, ` p = d k + 1 ` pushed on 7, ` cmp := compare p x `
  tmipcz   poolCmpZ_runs: ` dup 1 4 6 ; dup 7 6 4 ; cmpFrag 4 6 ` : ` cmp := compare z p ` , every stack restored

    MM_DB=sorties/t11p.mm python3 tools/gen/t11p_c_pre.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith
from cl import Closure

SEL = sys.argv[1:]

PPA = '( ( A x. G ) + 1 )'
DATA_PPR = ((STKD('D'), ('F e. NN0', 'G e. NN0', 'A e. NN0'), 'N e. NN0'),
            ((LT2('F', 'N'), LT2('G', 'N'), LT2('A', 'N')), LT2(PPA, 'N'), (WG('X'), WG('Y'), WG("X'"))),
            (DEQ(0, EWg('F', 'X')), DEQ(2, EWg('G', 'Y')), DEQ(5, EWg('A', "X'"))))
TREE_PPR = TREE0('ppr', DATA_PPR)
CONCL_PPR = TRI(CS('ppr'), CLN('E', CMPC(PPA, 'F'), UPS('D', ('5', "X'"), ('7', EWg(PPA, DK(7))))), '( 6 x. ( TMB ` N ) )')
add11('tmippr', TREE_PPR, CONCL_PPR)

DATA_PCZ = ((STKD('D'), ('Z e. NN0', 'Q e. NN0', 'N e. NN0')), (LT2('Z', 'N'), LT2('Q', 'N'), (WG('X'), WG('Y'))),
            (DEQ(1, EWg('Z', 'X')), DEQ(7, EWg('Q', 'Y'))))
TREE_PCZ = TREE0('pcz', DATA_PCZ)
CONCL_PCZ = TRI(CS('pcz'), CLN('E', CMPC('Z', 'Q'), 'D'), '( 3 x. ( TMB ` N ) )')
add11('tmipcz', TREE_PCZ, CONCL_PCZ)
STMTS_C = {l: STMTS11[l] for l in ('tmippr', 'tmipcz')}


def tbn(w, ph, nn, x='N'):
    T_ = '( TMB ` %s )' % x
    return w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, T_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, T_))


def tmippr():
    lab = 'tmippr'
    T = numtree11(TREE_PPR)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` poolPre_runs ` at the machine: ` dup 2 4 6 ; mulC 5 4 7 6 3 ; incr 7 4 ; dup 7 4 6 ; dup 0 6 4 ; '
               'cmpFrag 4 6 ` consumes the entry ` d ` of stack 5, pushes ` p = d k + 1 ` on 7 and sets ` cmp ` to the comparison '
               'of ` p ` with ` x ` , every other stack restored, within ` 6 B N ` steps (~ tmidupb , ~ tmimulb , ~ tmiincbs , '
               '~ tmicmpb ).')
    s = w.s
    c0 = Ctx(w, ph, T)
    fn, gn, an = c0['F e. NN0'], c0['G e. NN0'], c0['A e. NN0']
    eqs = {'0': (EWg('F', 'X'), ewg_(w, ph, 'F', fn, 'X', c0[WG('X')])), '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', c0[WG('Y')])),
           '5': (EWg('A', "X'"), ewg_(w, ph, 'A', an, "X'", c0[WG("X'")]))}
    B = Base(w, ph, T, N8, 'ppr', eqs)
    c = B.c
    LM = FRAGS['ppr'].lmap()
    g = lambda k: B.S0.vals[k][2]
    cl = Closure(w, ph, {'A': ('NN0', an), 'G': ('NN0', gn), 'N': ('NN0', c['N e. NN0'])})
    AG = '( A x. G )'
    agn = s([an, gn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, AG))
    ppn = s([agn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, PPA))
    P2 = '( 2 ^ N )'
    cl.atom(P2)
    cl.leaf(AG, 'NN0', agn)
    aglt = linarith(w, ph, [c[LT2(PPA, 'N')]], '%s < %s' % (AG, P2), closure=cl)
    R = B.run()
    E4 = EWg('G', DK(4))
    B.call(R, 'tmidupb', {'K': '2', 'J': '4', 'I': '6', 'F': 'G', 'N': 'N', 'X': 'Y', 'P': PL('P', 0), 'E': LM['Y2']}, {},
           [('4', E4, B.g(E4, ewg_(w, ph, 'G', gn, DK(4), g('4'))))])
    E7 = EWg(AG, DK(7))
    B.call(R, 'tmimulb', {'K': '5', 'J': '4', 'I': '7', "I'": '6', 'I"': '3', 'F': 'A', 'G': 'G', 'N': 'N', 'X': "X'", 'Y': DK(4),
                          'P': PL('P', 1), 'E': LM['Y3']}, {},
           [('7', E7, B.g(E7, ewg_(w, ph, AG, agn, DK(7), g('7')))), ('5', "X'", c[WG("X'")]), ('4', DK(4), g('4'))])
    E7b = EWg(PPA, DK(7))
    B.call(R, 'tmiincbs', {'K': '7', 'J': '4', 'F': AG, 'N': 'N', 'X': DK(7), 'P': PL('P', 2), 'E': LM['Y4']},
           {'%s e. NN0' % AG: agn, '%s < %s' % (AG, P2): aglt}, [('7', E7b, B.g(E7b, ewg_(w, ph, PPA, ppn, DK(7), g('7'))))])
    E4b = EWg(PPA, DK(4))
    B.call(R, 'tmidupb', {'K': '7', 'J': '4', 'I': '6', 'F': PPA, 'N': 'N', 'X': DK(7), 'P': PL('P', 3), 'E': LM['Y5']},
           {'%s e. NN0' % PPA: ppn}, [('4', E4b, B.g(E4b, ewg_(w, ph, PPA, ppn, DK(4), g('4'))))])
    E6 = EWg('F', DK(6))
    B.call(R, 'tmidupb', {'K': '0', 'J': '6', 'I': '4', 'F': 'F', 'N': 'N', 'X': 'X', 'P': PL('P', 4), 'E': LM['Y6']}, {},
           [('6', E6, B.g(E6, ewg_(w, ph, 'F', fn, DK(6), g('6'))))])
    B.call(R, 'tmicmpb', {'K': '4', 'J': '6', 'F': PPA, 'G': 'F', 'N': 'N', 'X': DK(4), 'Y': DK(6), 'P': PL('P', 5), 'E': 'E'},
           {'%s e. NN0' % PPA: ppn}, [('4', DK(4), g('4')), ('6', DK(6), g('6'))])
    cur, out = R.normalize(N8)
    assert out == [('5', "X'"), ('7', E7b)], out
    TB_ = '( TMB ` N )'
    cl.leaf(TB_, 'NN0', tbn(w, ph, c['N e. NN0']))
    B6 = '( 6 x. %s )' % TB_
    le = linarith(w, ph, [], '%s <_ %s' % (R.n, B6), closure=cl)
    st = hrle(w, ph, B.mk['phm'], R.tri, R.C0, R.cur, R.n, B6, cl.mem(B6, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def tmipcz():
    lab = 'tmipcz'
    T = numtree11(TREE_PCZ)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` poolCmpZ_runs ` at the machine: ` dup 1 4 6 ; dup 7 6 4 ; cmpFrag 4 6 ` sets ` cmp ` to the comparison of '
               '` z ` (stack 1) with ` p ` (stack 7), every stack restored, within ` 3 B N ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    zn, qn = c0['Z e. NN0'], c0['Q e. NN0']
    eqs = {'1': (EWg('Z', 'X'), ewg_(w, ph, 'Z', zn, 'X', c0[WG('X')])), '7': (EWg('Q', 'Y'), ewg_(w, ph, 'Q', qn, 'Y', c0[WG('Y')]))}
    B = Base(w, ph, T, N8, 'pcz', eqs)
    c = B.c
    LM = FRAGS['pcz'].lmap()
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    E4 = EWg('Z', DK(4))
    B.call(R, 'tmidupb', {'K': '1', 'J': '4', 'I': '6', 'F': 'Z', 'N': 'N', 'X': 'X', 'P': PL('P', 0), 'E': LM['Y2']}, {},
           [('4', E4, B.g(E4, ewg_(w, ph, 'Z', zn, DK(4), g('4'))))])
    E6 = EWg('Q', DK(6))
    B.call(R, 'tmidupb', {'K': '7', 'J': '6', 'I': '4', 'F': 'Q', 'N': 'N', 'X': 'Y', 'P': PL('P', 1), 'E': LM['Y3']}, {},
           [('6', E6, B.g(E6, ewg_(w, ph, 'Q', qn, DK(6), g('6'))))])
    B.call(R, 'tmicmpb', {'K': '4', 'J': '6', 'F': 'Z', 'G': 'Q', 'N': 'N', 'X': DK(4), 'Y': DK(6), 'P': PL('P', 2), 'E': 'E'}, {},
           [('4', DK(4), g('4')), ('6', DK(6), g('6'))])
    cur, out = R.normalize(N8)
    assert out == [], out
    cl = Closure(w, ph, {'N': ('NN0', c['N e. NN0'])})
    TB_ = '( TMB ` N )'
    cl.leaf(TB_, 'NN0', tbn(w, ph, c['N e. NN0']))
    B3 = '( 3 x. %s )' % TB_
    le = linarith(w, ph, [], '%s <_ %s' % (R.n, B3), closure=cl)
    st = hrle(w, ph, B.mk['phm'], R.tri, R.C0, R.cur, R.n, B3, cl.mem(B3, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
