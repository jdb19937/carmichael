"""T7c: the frozen statements of the sortie.

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_freeze.py print      list LABEL / statement
    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_freeze.py check [LABEL...]   compare with the database
    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_freeze.py clash [FILE...]    labels reused as handlers or numbers
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *


def frozen():
    out = {}
    import t7c_a_drn as A
    import t7c_b_drc as B
    import t7c_c_pgt as C
    import t7c_d_pgl as D
    import t7c_e_ipt as E
    out.update(A.STMTS)
    out.update(B.STMTS)
    for l in ['tmipgt1', 'tmipgt2', 'tmipgt3']:
        T, Cc = C.STMT(l)
        out[l] = '( %s -> %s )' % (cj(T), Cc)
    out.update(D.STMTS)
    out.update(E.STMTS)
    import t7c_f_p2 as F
    import t7c_g_bl as G
    import t7c_h_lst as H
    out.update(F.STMTS)
    out.update(G.STMTS)
    out.update(H.STMTS)
    # the copyList chain with the handler G: the delivered statements with the handler F0 renamed
    from t7c_i_cpyg import RENAME, handler_f0
    for src, dst in RENAME.items():
        out[dst] = ' '.join(handler_f0(stmt(src).split()))
    return out


def clashes(paths):
    """Hoare theorems whose statement uses one class variable both as a label ( ( M ` X ) = ... )
    and as a handler, test or push function, or as a number (an iteration bound)"""
    import re
    out = []
    for fn in paths:
        txt = open(fn).read()
        for m in re.finditer(r'(\S+)\s+\$p\s+\|-(.*?)\$=', txt, re.S):
            lab, st = m.group(1), ' '.join(m.group(2).split())
            if 'TM2Hoare' not in st:
                continue
            labs = set(re.findall(r'\( M ` (\S+) \) =', st))
            hd = set(re.findall(r"(\S+) e\. \( (?:\( 2nd ` T \)|2o|Gamma'|\( \( 1st ` \( 1st ` T \) \) ` \S+ \)) \^m", st))
            hd |= set(re.findall(r'\( (\S+) ` <\. r ,', st))
            num = set(re.findall(r'\( 0 \.\.\.?\^? (\S+) \)', st)) | set(re.findall(r'\( (\S+) [+-] ', st))
            both = labs & (hd | num)
            if both:
                out.append((fn, lab, sorted(both)))
    return out


def main(args):
    if args and args[0] == 'clash':
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        paths = args[1:] or [os.path.join(root, 'carmichael.mm'), os.path.join(root, os.environ.get('MM_DB', 'carmichael.mm'))]
        for fn, lab, xs in clashes(paths):
            print('CLASH', os.path.basename(fn), lab, ' '.join(xs))
        return
    fz = frozen()
    if args and args[0] == 'print':
        for l in sorted(fz):
            print('%s (%d tokens)\n%s\n' % (l, len(fz[l].split()), fz[l]))
        return
    labs = args[1:] if args and args[0] == 'check' else sorted(fz)
    bad = 0
    for l in labs:
        try:
            db = stmt(l)
        except KeyError:
            print('ABSENT', l)
            continue
        if ' '.join(db.split()) != ' '.join(fz[l].split()):
            print('DIFFERS', l)
            bad += 1
        else:
            print('EQUAL', l)
    print('%d frozen statements, %d differ' % (len(fz), bad))


if __name__ == '__main__':
    main(sys.argv[1:])
