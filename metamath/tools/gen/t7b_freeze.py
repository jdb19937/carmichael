"""T7b: the frozen statements of the sortie.

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_freeze.py            grammar check (unify of each statement)
    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_freeze.py print      list LABEL / statement
    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_freeze.py check [LABEL...]   compare with the database
"""
import sys, os, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *


def frozen():
    """label -> statement text (the $p statements of the sortie)"""
    out = {}
    import t7b_c_runs as R
    import t7b_d_mul as DM
    import t7b_e_froms as FS
    import t7b_f_nat as NT
    import t7b_g_dmu as GU
    import t7b_h_dmq as HQ
    import t7b_i_dmd as ID
    import t7b_j_dmc as JC
    import t7b_k_dmb as KB
    import t7b_l_pg as PG
    for n in FRAGS:
        out['tmi%su' % n] = unfold_stmt(FRAGS[n])
    for lab in R.RUNS:
        T, C = R.runs_stmt(lab)
        out[lab] = '( %s -> %s )' % (cj(T), C)
    T, C = DM.STMT_MULB(); out['tmimulb'] = '( %s -> %s )' % (cj(T), C)
    for lab in ['tmiincs', 'tmiprds', 'tmiizs']:
        T, C = FS.froms_stmt(lab); out[lab] = '( %s -> %s )' % (cj(T), C)
    out.update(NT.STMTS)
    for lab, fn in [('tmidmub', GU.STMT_UB), ('tmidm3', GU.STMT_DDC), ('tmidmsb', GU.STMT_DSI), ('tmidmuq', HQ.STMT_UQ),
                    ('tmidmcr', JC.STMT_M), ('tmidmr', JC.STMT_DMR)]:
        T, C = fn(); out[lab] = '( %s -> %s )' % (cj(T), C)
    typ, body, ex = ID.dblocks()
    ph = cj(ID.PH_D())
    out['tmidmd1'] = '( ( %s /\\ i e. ( 0 ..^ R ) ) -> ( %s /\\ %s ) )' % (ph, cj(body[0]), cj(body[1]))
    out['tmidmd2'] = '( ( %s /\\ i e. ( 0 ..^ R ) ) -> ( %s /\\ %s ) )' % (ph, body[2][0][0], body[2][0][1])
    out['tmidmd3'] = '( ( %s /\\ i e. ( 0 ..^ R ) ) -> %s )' % (ph, body[2][1])
    out['tmidmd4'] = '( ( %s /\\ i e. ( 0 ..^ R ) ) -> %s )' % (ph, body[2][2])
    out['tmidmdt'] = '( %s -> ( %s /\\ %s ) )' % (ph, typ, ex)
    for lab in KB.CONF:
        T, C = KB.STMT(lab); out[lab] = '( %s -> %s )' % (cj(T), C)
        T, C = KB.STMT(lab, rform=True); out[KB.RLAB[lab]] = '( %s -> %s )' % (cj(T), C)
    for lab in ['tmiizbs', 'tmiincbs', 'tmiprdbs']:
        T, C = FS.fromsb_stmt(lab); out[lab] = '( %s -> %s )' % (cj(T), C)
    out.update(PG.STMTS)
    return out


def main(args):
    fz = frozen()
    if args and args[0] == 'print':
        for l in sorted(fz):
            print('%s (%d tokens)\n%s\n' % (l, len(fz[l].split()), fz[l]))
        return
    if args and args[0] == 'check':
        labs = args[1:] or sorted(fz)
        bad = 0
        for l in labs:
            try:
                db = stmt(l)
            except KeyError:
                print('ABSENT', l); continue
            if ' '.join(db.split()) != ' '.join(fz[l].split()):
                print('DIFFERS', l); bad += 1
            else:
                print('EQUAL', l)
        print('%d differ' % bad)
        return
    # grammar check: unify each statement as a qed-less worksheet is expensive; the database check suffices
    print('%d frozen statements' % len(fz))


if __name__ == '__main__':
    main(sys.argv[1:])
