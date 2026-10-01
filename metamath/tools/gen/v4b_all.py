"""Sortie v4b: regenerate every worksheet in dependency order.

MM_DB=sorties/v4b.mm python3 tools/gen/v4b_all.py            # all 32
MM_DB=sorties/v4b.mm python3 tools/gen/v4b_all.py progfib    # a subset
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v4b_prm, v4b_nu, v4b_sh, v4b_crt, v4b_rem, v4b_cnt, v4b_err
import v4b_rad, v4b_fib, v4b_sum, v4b_asm, v4b_poly, v4b_bt, v4b_lev, v4b_fin

ORDER = [
    ('progtfi', v4b_prm.progtfi), ('progpnn', v4b_prm.progpnn), ('progpel', v4b_prm.progpel),
    ('progvval', v4b_nu.progvval), ('progvcl', v4b_nu.progvcl), ('progv1', v4b_nu.progv1),
    ('progvsqf', v4b_nu.progvsqf), ('progvmul', v4b_nu.progvmul),
    ('progvprm', v4b_nu.progvprm),
    ('progsh', v4b_sh.progsh), ('progsel', v4b_sh.progsel),
    ('crtres', v4b_crt.crtres), ('crtcnt', v4b_crt.crtcnt),
    ('progmsum', v4b_rem.progmsum), ('progcop', v4b_rem.progcop), ('progrem', v4b_rem.progrem),
    ('gcdnprm', v4b_cnt.gcdnprm), ('progcnt', v4b_cnt.progcnt),
    ('progerr', v4b_err.progerr),
    ('radlem', v4b_rad.radlem), ('progvgt', v4b_rad.progvgt),
    ('progfib', v4b_fib.progfib), ('progsum', v4b_sum.progsum),
    ('progssge', v4b_sum.progssge),
    ('progmain', v4b_asm.progmain),
    ('poly4le', v4b_poly.poly4le),
    ('mainid', v4b_bt.mainid), ('errid', v4b_bt.errid), ('btmain', v4b_bt.btmain),
    ('btlev', v4b_lev.btlev), ('bterr', v4b_lev.bterr),
    ('bruntit', v4b_fin.bruntit),
]


def main(names=None):
    ok = True
    for nm, fn in ORDER:
        if names and nm not in names:
            continue
        r = fn()
        w = r[0] if isinstance(r, tuple) else r
        ok = w.run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
