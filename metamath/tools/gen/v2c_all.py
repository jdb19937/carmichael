"""Sortie v2c: run every generator in dependency order.

    MM_DB=sorties/v2c.mm python3 tools/gen/v2c_all.py            # all of them
    MM_DB=sorties/v2c.mm python3 tools/gen/v2c_all.py gcdfib     # a subset
"""
import sys, os, subprocess
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HERE = os.path.dirname(os.path.abspath(__file__))

ORDER = [
    ('v2c_help', ['ifmulz', 'ifmulz2', 'ifmul2', 'sumite']),
    ('v2c_inv', ['gtfprodi', 'gtsuminv', 'gtsinv2']),
    ('v2c_lcm', ['vlcm']),
    ('v2c_diag', ['mpgex1', 'mpgex2', 'mpggcd', 'mpgsw', 'mpgsq', 'mpgen']),
    ('v2c_main', ['ifsq', 'musq1', 'lwff', 'lwfv', 'mpfv', 'mpmss', 'mpmev', 'mpmain']),
    ('v2c_wt', ['muabs1', 'mucanc', 'lwmu1', 'gfinner', 'gfiff', 'gfbm', 'gcdfib',
                'lwmuss', 'lwabs']),
    ('v2c_help', ['ifabs']),
    ('v2c_err', ['mpabs', 'selberr']),
    ('v2c_sieve', ['muone', 'lwone', 'lwzeq', 'lwzf', 'lwzv', 'mpzre', 'mpzf', 'mpzlam',
                   'mpzv', 'mpzum', 'selbsieve']),
]
def main(argv):
    only = set(argv)
    for mod, labels in ORDER:
        for lab in labels:
            if only and lab not in only:
                continue
            r = subprocess.run([sys.executable, os.path.join(HERE, mod + '.py'), lab],
                               cwd=ROOT, capture_output=True, text=True)
            out = '\n'.join(l for l in (r.stdout + r.stderr).split('\n')
                            if not l.startswith('  ') and 'SyntaxWarning' not in l).strip()
            print(out)
            if 'OK   ' + lab not in out:
                return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
