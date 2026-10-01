"""Sortie v3: run every generator in dependency order.

    MM_DB=sorties/v3.mm python3 tools/gen/v3_all.py            # all 24
    MM_DB=sorties/v3.mm python3 tools/gen/v3_all.py cntmod     # a subset
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v3_geo, v3_elem, v3_log, v3_cnt, v3_dm, v3_pf, v3_nu, v3_spu, v3_sm, v3_step, v3_base, v3_cop

ORDER = [
    ('geosrle', v3_geo.geosrle), ('geoslle', v3_geo.geoslle),
    ('phipfprod', v3_elem.phipfprod), ('sqf2omle', v3_elem.sqf2omle),
    ('sqf3omle', v3_elem.sqf3omle),
    ('logp1le', v3_log.logp1le), ('logp1le2', v3_log.logp1le2),
    ('logpwub', v3_log.logpwub),
    ('cntmod', v3_cnt.cntmod), ('sum3omle', v3_dm.sum3omle),
    ('pfmul', v3_pf.pfmul), ('pfdisj', v3_pf.pfdisj),
    ('pffinq', v3_nu.pffinq), ('pfprodmul', v3_nu.pfprodmul),
    ('phi2mule', v3_nu.phi2mule),
    ('sumprodub', v3_spu.sumprodub),
    ('smsplit', v3_sm.smsplit), ('smsumf1', v3_sm.smsumf1),
    ('smsumstep', v3_step.smsumstep),
    ('smsum0', v3_base.smsum0), ('smsum', v3_base.smsum),
    ('cosplit', v3_cop.cosplit), ('cof1', v3_cop.cof1), ('cophrm', v3_cop.cophrm),
]

if __name__ == '__main__':
    want = set(sys.argv[1:])
    for name, fn in ORDER:
        if want and name not in want:
            continue
        fn().run()
