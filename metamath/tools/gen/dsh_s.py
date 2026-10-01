"""Sortie DSH: parameter facts (dshzz is a hand worksheet): dsh151rp, dshyp.
Run: MM_DB=sorties/dsh.mm MM_ENGINE=mmatch python3 tools/gen/dsh_s.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dshlib import *
from tm import W
from z6a_e3 import unpack, c_

import num

only = sys.argv[1:]
want = lambda l: not only or l in only
mk = lambda w, a: (lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g)))

if want('dsh151rp'):
    w = W('dsh151rp', 'The exponent of ` Ypar D = D ^ ( 151 / 100 ) ` is positive.')
    s = num.rp(w, Y151)
    toqed(w, s, 'dsh151rp'); w.run()

if want('dshyp'):
    w = W('dshyp', 'Lean ` Ypar_pos ` , ` one_lt_Ypar ` : for ` 1 < D ` , ` Ypar D = D ^ ( 151 / 100 ) ` is positive and larger than 1.')
    a = '( D e. RR /\\ 1 < D )'; t = mk(w, a)
    dr = t([], 'simpl', 'D e. RR'); d1 = t([], 'simpr', '1 < D')
    zz = t([w.s([], 'id', '( %s -> %s )' % (a, a)), w.inst('dshzz')], 'syl', '( D e. RR+ /\\ ( 2 x. D ) e. RR+ /\\ D < ( 2 x. D ) )')
    drp = t([zz], 'simp1d', 'D e. RR+')
    er = c_(w, a, num.real(w, Y151), '%s e. RR' % Y151)
    yrp = t([drp, er], 'rpcxpcld', '%s e. RR+' % YP)
    z0 = c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR')
    g0 = t([c_(w, a, w.s([], 'dsh151rp', '%s e. RR+' % Y151), '%s e. RR+' % Y151)], 'rpgt0d', '0 < %s' % Y151)
    cl = t([t([t([dr, d1], 'jca', a), t([z0, er], 'jca', '( 0 e. RR /\\ %s e. RR )' % Y151)], 'jca',
              '( %s /\\ ( 0 e. RR /\\ %s e. RR ) )' % (a, Y151)), w.inst('cxplt')], 'syl', '( 0 < %s <-> ( D ^c 0 ) < %s )' % (Y151, YP))
    lt = t([g0, cl], 'mpbid', '( D ^c 0 ) < %s' % YP)
    c0 = t([t([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1')
    one = t([c0, lt], 'eqbrtrrd', '1 < %s' % YP)
    s = t([yrp, one], 'jca', '( %s e. RR+ /\\ 1 < %s )' % (YP, YP))
    toqed(w, s, 'dshyp'); w.run()

if want('dshpdg'):
    w = W('dshpdg', 'The pole ` 1 - S ` of ` L ( S + w ) ` is in the domain of Gamma, for ` 39 / 50 <_ Re S <_ 1 ` , ` S =/= 1 ` (~ z6rdg ; the half-line form of ~ z6pdg ).')
    a = '( %s /\\ S =/= 1 )' % SRNGH; f = unpack(w, a); t = mk(w, a)
    sc = f['S e. CC']; hi = f['( Re ` S ) <_ 1']; ne = f['S =/= 1']
    one = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    u = t([one, sc], 'subcld', '( 1 - S ) e. CC')
    rs = t([sc], 'recld', '( Re ` S ) e. RR')
    o1 = c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')
    re = t([one, sc], 'resubd', '( Re ` ( 1 - S ) ) = ( ( Re ` 1 ) - ( Re ` S ) )')
    r1 = c_(w, a, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    re2 = t([re, t([r1], 'oveq1d', '( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) )')], 'eqtrd', '( Re ` ( 1 - S ) ) = ( 1 - ( Re ` S ) )')
    g0 = t([hi, t([o1, rs], 'subge0d', '( 0 <_ ( 1 - ( Re ` S ) ) <-> ( Re ` S ) <_ 1 )')], 'mpbird', '0 <_ ( 1 - ( Re ` S ) )')
    m1 = c_(w, a, w.s([], 'neg1lt0', '-u 1 < 0'), '-u 1 < 0')
    lt = t([c_(w, a, w.s([w.s([], '1re', '1 e. RR')], 'renegcli', '-u 1 e. RR'), '-u 1 e. RR'), c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'),
            t([o1, rs], 'resubcld', '( 1 - ( Re ` S ) ) e. RR'), m1, g0], 'ltletrd', '-u 1 < ( 1 - ( Re ` S ) )')
    lt2 = t([lt, re2], 'breqtrrd', '-u 1 < ( Re ` ( 1 - S ) )')
    n0 = t([one, sc, t([ne], 'necomd', '1 =/= S')], 'subne0d', '( 1 - S ) =/= 0')
    s = t([t([u, t([lt2, n0], 'jca', '( -u 1 < ( Re ` ( 1 - S ) ) /\\ ( 1 - S ) =/= 0 )')], 'jca',
            '( ( 1 - S ) e. CC /\\ ( -u 1 < ( Re ` ( 1 - S ) ) /\\ ( 1 - S ) =/= 0 ) )'), w.inst('z6rdg')], 'syl', '( 1 - S ) e. %s' % DG)
    toqed(w, s, 'dshpdg'); w.run()
