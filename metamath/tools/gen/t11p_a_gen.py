"""T11 helper (pool): the generic core of Lean's ` poolGoF ` (Steps23.lean ` poolGoF_runs ` ).

  tmipzg   ~ tm2fmla with the Sigma-cost entry loop ~ tm2lfes in place of ~ tm2lfe : ` pushSym I bra ` , ` forEntries K body `
           (one triple per entry of cost ` ( Y ` j ) ` ), ` popTop K ` , a closing triple

    MM_DB=sorties/t11p.mm python3 tools/gen/t11p_a_gen.py tmipzg
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *
from tpl_f_list import pushsym, poptopnl, sumcl

SEL = sys.argv[1:]

S_J = SUM('j', NL, '( %s + 2 )' % YF('j'))
TREE_PZG = ((TREE_FES, (MEQ('P0', PSH('I', '2', 'P1')), MEQ('E', POPL('K', 'F"', "E'")))),
            (((LAB('P0'), LAB("E'"), LAB('E"')), (GAMK('I'), 'K =/= I'), FTG('F"')), ((STKD('D'), INIT_MLA), (SSS("N'"), SSS('N"'), 'U e. NN0'))),
            (HPK(NFIN, 'F"', '2', "N'"), TRIP_MLA))
CONCL_PZG = HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E"', 'N"', "D'"), '( ( %s + U ) + 4 )' % S_J)
ST_PZG = statement(TREE_PZG, CONCL_PZG)


def tmipzg():
    lab = 'tmipzg'
    tree, ph = TREE_PZG, cj(TREE_PZG)
    w = W(lab, 'The generic core of Lean\'s ` poolGoF ` (Steps23.lean): ` pushSym I bra ` opens the kept list (~ tm2fpshn ), '
               '` forEntries K body ` is the Sigma-cost loop ~ tm2lfes (one triple per entry, of cost ` ( Y ` j ) ` ), '
               '` popTop K ` removes the consumed list\'s ` bra ` (~ tm2lpop ) and the closing ` revList ` is a hypothesis triple.  '
               '~ tm2fmla with a per-entry charge.')
    c = Ctx(w, ph, tree)
    cf = Ctx(w, ph, TREE_FES, root=c[PHFS])
    phm, geq = cf[PHM], cf[GEQ]
    u = dict(phm=phm, pk=cf[fe.PK], pty=cf[fe.PTY], nss=cf['N C_ %s' % SS],
             nl=w.s([cf['L e. %s' % WWB], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL)))
    dd, init = c[STKD('D')], c[INIT_MLA]
    DI2 = UPDT('D', 'I', CC(S1('2'), '( D ` I )'))
    s1, C0, C1x, _, _ = pushsym(w, ph, c, phm, geq, 'P0', 'P1', 'I', '2', 'N', 'D', dd, u['nss'], c['I e. %s' % FZ8])
    initc = w.s([init], 'eqcomd', '( %s -> %s = %s )' % (ph, DI2, PF('0')))
    C1 = CL('P1', 'N', PF('0'))
    s1r, _, _, _ = hrrw(w, ph, s1, C0, C1x, '1', deq=clneq(w, ph, 'P1', 'N', initc, DI2, PF('0')))
    lfes, cc = inst(w, ph, 'tm2lfes', {}, bldr(w, ph, cf, phm))
    C2 = CL('E', NFIN, PF(NL))
    assert triple_parts(cc)[0] == C1 and triple_parts(cc)[1] == C2 and triple_parts(cc)[2] == '( %s + 2 )' % S_J, cc
    pop, Ca, C3 = poptopnl(w, ph, c, u, 'E', "E'", "N'")
    trm = c[TRIP_MLA]
    C4 = CL('E"', 'N"', "D'")
    q = hrseq(w, ph, phm, s1r, lfes, C0, C1, C2, '1', '( %s + 2 )' % S_J); n = '( 1 + ( %s + 2 ) )' % S_J
    q = hrseq(w, ph, phm, q, pop, C0, C2, C3, n, '1'); n = '( %s + 1 )' % n
    q = hrseq(w, ph, phm, q, trm, C0, C3, C4, n, 'U'); n = '( %s + U )' % n
    sn = sumcl(w, ph, cf[HBS])
    bound0(w, ph, phm, q, C0, C4, n, triple_parts(CONCL_PZG)[2], {'U': c['U e. NN0'], S_J: sn}, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
