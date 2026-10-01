"""Sortie v4a: regenerate every worksheet, in dependency order.

    MM_DB=sorties/v4a.mm python3 tools/gen/v4a_all.py            # all 46
    MM_DB=sorties/v4a.mm python3 tools/gen/v4a_all.py twinfib    # a subset
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import v4a_rc, v4a_crt, v4a_rcp, v4a_den, v4a_rs, v4a_rst, v4a_rss, v4a_sq
import v4a_tb, v4a_fib, v4a_nuc, v4a_ss, v4a_v, v4a_sh, v4a_c, v4a_rem, v4a_err
import v4a_asm, v4a_arc, v4a_fin

ORDER = [
    ('quadmod', v4a_rc), ('rc1', v4a_rc), ('rcprm', v4a_rc),
    ('rcmul', v4a_crt),
    ('rcpstep', v4a_rcp), ('rcprod', v4a_rcp), ('rcdvds', v4a_rcp),
    ('sgmpwle', v4a_den),
    ('rssplit', v4a_rs), ('rsf1', v4a_rs),
    ('rsstep', v4a_rst),
    ('rs0', v4a_rss), ('rssum', v4a_rss),
    ('twinsq', v4a_sq),
    ('twinp3', v4a_tb), ('twinps', v4a_tb), ('twinpg', v4a_tb),
    ('twincop', v4a_tb), ('twingf', v4a_tb),
    ('twinfib', v4a_fib),
    ('twinnuc', v4a_nuc),
    ('flsqrt2', v4a_ss), ('twinssge', v4a_ss),
    ('twinvval', v4a_v), ('twinvf', v4a_v), ('twinv1', v4a_v), ('twinvp', v4a_v),
    ('twinvmul', v4a_v),
    ('twinpp', v4a_sh), ('twinsupp', v4a_sh), ('twinwt', v4a_sh), ('twinsh', v4a_sh),
    ('twinmono', v4a_c), ('twinqinj', v4a_c), ('twinms', v4a_c), ('twinsfe', v4a_c),
    ('twincnt', v4a_c),
    ('twinrem', v4a_rem),
    ('twinerr', v4a_err),
    ('twinpz', v4a_sh),
    ('flsqge', v4a_asm), ('flsqle', v4a_asm), ('twinsqf', v4a_asm),
    ('twinarc', v4a_arc),
    ('twinsvx', v4a_fin), ('twinsv', v4a_fin),
]


def main(names):
    bad = []
    for label, mod in ORDER:
        if names and label not in names:
            continue
        if not mod.ALL[label]().run():
            bad.append(label)
    if bad:
        print('FAILED: ' + ' '.join(bad))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(set(sys.argv[1:])))
