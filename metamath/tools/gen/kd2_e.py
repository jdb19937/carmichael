"""Sortie KD2: the window (kd2wb, kd2pwsif).  MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_e.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from kd2lib import *
from cl import formula_of, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, nlinarith
from mvlib import ringeq, ringeqp
from kd2_d import vmfacts, vmcong
import num

only = sys.argv[1:]


def psmem(w, Ah, p, pmem, Y, U):
    """from pmem : ( Ah -> p e. PSET(Y,U) ): p e. NN, p e. Prime, Y < p, p <_ ( |_ ` U )"""
    d = lambda ref, h, c: D(w, Ah, ref, h, c)
    ae = w.s([w.s([], 'eleq1', '( a = %s -> ( a e. Prime <-> %s e. Prime ) )' % (p, p)), w.s([], 'breq2', '( a = %s -> ( %s < a <-> %s < %s ) )' % (p, Y, Y, p))], 'anbi12d',
             '( a = %s -> ( ( a e. Prime /\\ %s < a ) <-> ( %s e. Prime /\\ %s < %s ) ) )' % (p, Y, p, Y, p))
    FL = '( 1 ... ( |_ ` %s ) )' % U
    el = w.s([ae], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ ( %s e. Prime /\\ %s < %s ) ) )' % (p, PSET(Y, U), p, FL, p, Y, p))
    g = d('mpbid', [pmem, w.s([el], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. %s /\\ ( %s e. Prime /\\ %s < %s ) ) ) )' % (Ah, p, PSET(Y, U), p, FL, p, Y, p))],
          '( %s e. %s /\\ ( %s e. Prime /\\ %s < %s ) )' % (p, FL, p, Y, p))
    pf = d('simpld', [g], '%s e. %s' % (p, FL))
    pn = d('syl', [pf, w.inst('elfznn')], '%s e. NN' % p)
    pr = d('simpld', [d('simprd', [g], '( %s e. Prime /\\ %s < %s )' % (p, Y, p))], '%s e. Prime' % p)
    yp = d('simprd', [d('simprd', [g], '( %s e. Prime /\\ %s < %s )' % (p, Y, p))], '%s < %s' % (Y, p))
    pl = d('syl', [pf, w.inst('elfzle2')], '%s <_ ( |_ ` %s )' % (p, U))
    return dict(pn=pn, pr=pr, yp=yp, pl=pl, pf=pf)


def gen_wb():
    w = W('kd2wb', 'Lean ` KDerivDetect.norm_primeWindowSum_le ` at the Metamath constants: below ` X2 >_ e^20 ` , ` abs S ( u ) <_ e ( ( 5 / 4 ) log X2 + 5 ) ` ( ~ kd2vmp at ` 1 / log X2 ` ; Lean ` e ( log X2 + 2 ) ` ).')
    A0 = S['kd2wb'].split(' -> ( abs `')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    nxh = d('simp1', [], NXH); g2 = d('simp2', [], '( T e. RR /\\ Y e. RR /\\ U e. RR )'); g3 = d('simp3', [], '( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z /\\ U <_ Z )')
    tr = d('simp1d', [g2], 'T e. RR'); yr = d('simp2d', [g2], 'Y e. RR'); ur = d('simp3d', [g2], 'U e. RR')
    zr = d('simp1d', [g3], 'Z e. RR'); ez = d('simp2d', [g3], '( exp ` ; 2 0 ) <_ Z'); uz_ = d('simp3d', [g3], 'U <_ Z')
    c20 = w.s([num.real(w, '; 2 0')], 'a1i', '( %s -> ; 2 0 e. RR )' % A0)
    e20p = d('rpefcld', [c20], '( exp ` ; 2 0 ) e. RR+')
    zp = d('elrpd', [zr, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), d('rpred', [e20p], '( exp ` ; 2 0 ) e. RR'), zr, d('rpgt0d', [e20p], '0 < ( exp ` ; 2 0 )'), ez], '0 < Z')], 'Z e. RR+')
    LZ = '( log ` Z )'
    l20 = d('eqbrtrrd', [d('relogefd', [c20], '( log ` ( exp ` ; 2 0 ) ) = ; 2 0'), d('mpbid', [ez, d('logled', [e20p, zp], '( ( exp ` ; 2 0 ) <_ Z <-> ( log ` ( exp ` ; 2 0 ) ) <_ %s )' % LZ)],
                                                                                              '( log ` ( exp ` ; 2 0 ) ) <_ %s' % LZ)], '; 2 0 <_ %s' % LZ)
    lzr = d('relogcld', [zp], '%s e. RR' % LZ)
    clz = Closure(w, A0, {LZ: ('RR', lzr)}); clz.atom(LZ)
    lz1 = linarith(w, A0, [l20], '1 <_ %s' % LZ, closure=clz)
    lzp = d('elrpd', [lzr, linarith(w, A0, [l20], '0 < %s' % LZ, closure=clz)], '%s e. RR+' % LZ)
    U0 = '( 1 / %s )' % LZ
    u0p = d('rpreccld', [lzp], '%s e. RR+' % U0)
    u01 = d('breqtrd', [d('lediv2ad', [w.s([num.rp(w, '1')], 'a1i', '( %s -> 1 e. RR+ )' % A0), lzp, a1(w, A0, '1re', '1 e. RR'), a1(w, A0, '0le1', '0 <_ 1'), lz1], '%s <_ ( 1 / 1 )' % U0),
                        a1(w, A0, '1div1e1', '( 1 / 1 ) = 1')], '%s <_ 1' % U0)
    PSU = PSET('Y', 'U')
    Ap = '( %s /\\ p e. %s )' % (A0, PSU)
    dp = lambda ref, h, c: D(w, Ap, ref, h, c)
    L = lambda st: lift(w, st, Ap)
    pm = psmem(w, Ap, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PSU)), 'Y', 'U')
    pn = pm['pn']; prp = dp('nnrpd', [pn], 'p e. RR+'); prr = dp('nnred', [pn], 'p e. RR'); pc = dp('nncnd', [pn], 'p e. CC')
    pleu = dp('letrd', [prr, dp('zred', [dp('flcld', [L(ur)], '( |_ ` U ) e. ZZ')], '( |_ ` U ) e. RR'), L(ur), pm['pl'], dp('syl', [L(ur), w.inst('flle')], '( |_ ` U ) <_ U')], 'p <_ U')
    plz = dp('letrd', [prr, L(ur), L(zr), pleu, L(uz_)], 'p <_ Z')
    CH = CHV('p')
    chc = dp('syl2anc', [L(nxh), pn, w.inst('lchrcl')], '%s e. CC' % CH)
    ch1 = dp('syl2anc', [L(nxh), pn, w.inst('lchrabs')], '( abs ` %s ) <_ 1' % CH)
    lp = dp('relogcld', [prp], '( log ` p ) e. RR'); lp0 = dp('logge0d', [prr, dp('nnge1d', [pn], '1 <_ p')], '0 <_ ( log ` p )')
    MT = '( -u 1 - ( T x. _i ) )'
    clm = Closure(w, Ap, {'T': ('RR', L(tr)), '_i': ('CC', a1(w, Ap, 'ax-icn', '_i e. CC'))}); clm.atom('_i')
    mtc = clm.mem(MT, 'CC')
    PM = '( p ^c %s )' % MT
    ab1 = dp('absmuld', [dp('mulcld', [chc, dp('recnd', [lp], '( log ` p ) e. CC')], '( %s x. ( log ` p ) ) e. CC' % CH), dp('cxpcld', [pc, mtc], '%s e. CC' % PM)],
             '( abs ` %s ) = ( ( abs ` ( %s x. ( log ` p ) ) ) x. ( abs ` %s ) )' % (CP('p'), CH, PM))
    ab2 = dp('absmuld', [chc, dp('recnd', [lp], '( log ` p ) e. CC')], '( abs ` ( %s x. ( log ` p ) ) ) = ( ( abs ` %s ) x. ( abs ` ( log ` p ) ) )' % (CH, CH))
    ab3 = dp('absidd', [lp, lp0], '( abs ` ( log ` p ) ) = ( log ` p )')
    ab4 = dp('syl2anc', [prp, mtc, w.inst('abscxp')], '( abs ` %s ) = ( p ^c ( Re ` %s ) )' % (PM, MT))
    re1 = ringeq(w, Ap, MT, '( -u 1 + ( _i x. -u T ) )', clm)
    re2 = dp('eqtrd', [dp('fveq2d', [re1], '( Re ` %s ) = ( Re ` ( -u 1 + ( _i x. -u T ) ) )' % MT),
                       dp('syl2anc', [dp('renegcld', [a1(w, Ap, '1re', '1 e. RR')], '-u 1 e. RR'), dp('renegcld', [L(tr)], '-u T e. RR'), w.inst('crre')], '( Re ` ( -u 1 + ( _i x. -u T ) ) ) = -u 1')],
              '( Re ` %s ) = -u 1' % MT)
    ab5 = dp('eqtrd', [ab4, dp('oveq2d', [re2], '( p ^c ( Re ` %s ) ) = ( p ^c -u 1 )' % MT)], '( abs ` %s ) = ( p ^c -u 1 )' % PM)
    PM1 = '( p ^c -u 1 )'
    abs_ = chain(w, Ap, ['( abs ` %s )' % CP('p'), '( ( abs ` ( %s x. ( log ` p ) ) ) x. ( abs ` %s ) )' % (CH, PM), '( ( ( abs ` %s ) x. ( abs ` ( log ` p ) ) ) x. ( abs ` %s ) )' % (CH, PM),
                         '( ( ( abs ` %s ) x. ( log ` p ) ) x. %s )' % (CH, PM1)],
                 [ab1, dp('oveq1d', [ab2], '( ( abs ` ( %s x. ( log ` p ) ) ) x. ( abs ` %s ) ) = ( ( ( abs ` %s ) x. ( abs ` ( log ` p ) ) ) x. ( abs ` %s ) )' % (CH, PM, CH, PM)),
                  dp('oveq12d', [dp('oveq2d', [ab3], '( ( abs ` %s ) x. ( abs ` ( log ` p ) ) ) = ( ( abs ` %s ) x. ( log ` p ) )' % (CH, CH)), ab5],
                     '( ( ( abs ` %s ) x. ( abs ` ( log ` p ) ) ) x. ( abs ` %s ) ) = ( ( ( abs ` %s ) x. ( log ` p ) ) x. %s )' % (CH, PM, CH, PM1))])
    pm1p = dp('rpcxpcld', [prp, dp('renegcld', [a1(w, Ap, '1re', '1 e. RR')], '-u 1 e. RR')], '%s e. RR+' % PM1)
    ach = dp('abscld', [chc], '( abs ` %s ) e. RR' % CH)
    k1 = dp('lemul1ad', [ach, a1(w, Ap, '1re', '1 e. RR'), lp, lp0, ch1], '( ( abs ` %s ) x. ( log ` p ) ) <_ ( 1 x. ( log ` p ) )' % CH)
    k2 = dp('lemul1ad', [dp('remulcld', [ach, lp], '( ( abs ` %s ) x. ( log ` p ) ) e. RR' % CH), dp('remulcld', [a1(w, Ap, '1re', '1 e. RR'), lp], '( 1 x. ( log ` p ) ) e. RR'),
                         dp('rpred', [pm1p], '%s e. RR' % PM1), dp('rpge0d', [pm1p], '0 <_ %s' % PM1), k1], '( ( ( abs ` %s ) x. ( log ` p ) ) x. %s ) <_ ( ( 1 x. ( log ` p ) ) x. %s )' % (CH, PM1, PM1))
    # p^-1 = p^-(1+u0) p^u0, p^u0 <_ e
    u0r = L(d('rpred', [u0p], '%s e. RR' % U0))
    PU = '( p ^c %s )' % U0; PV = '( p ^c -u ( 1 + %s ) )' % U0
    cla = Closure(w, Ap, {U0: ('RR', u0r)}); cla.atom(U0)
    ex = ringeq(w, Ap, '-u 1', '( -u ( 1 + %s ) + %s )' % (U0, U0), cla)
    ca = dp('cxpaddd', [pc, dp('nnne0d', [pn], 'p =/= 0'), cla.mem('-u ( 1 + %s )' % U0, 'CC'), cla.mem(U0, 'CC')], '( p ^c ( -u ( 1 + %s ) + %s ) ) = ( %s x. %s )' % (U0, U0, PV, PU))
    pm1e = dp('eqtrd', [dp('oveq2d', [ex], '%s = ( p ^c ( -u ( 1 + %s ) + %s ) )' % (PM1, U0, U0)), ca], '%s = ( %s x. %s )' % (PM1, PV, PU))
    pue = dp('cxpefd', [pc, dp('nnne0d', [pn], 'p =/= 0'), cla.mem(U0, 'CC')], '%s = ( exp ` ( %s x. ( log ` p ) ) )' % (PU, U0))
    llz = dp('mpbid', [plz, dp('logled', [prp, L(zp)], '( p <_ Z <-> ( log ` p ) <_ %s )' % LZ)], '( log ` p ) <_ %s' % LZ)
    ul = dp('lemul2ad', [lp, L(lzr), u0r, dp('rpge0d', [L(u0p)], '0 <_ %s' % U0), llz], '( %s x. ( log ` p ) ) <_ ( %s x. %s )' % (U0, U0, LZ))
    u1 = dp('eqtrd', [dp('mulcomd', [cla.mem(U0, 'CC'), dp('recnd', [L(lzr)], '%s e. CC' % LZ)], '( %s x. %s ) = ( %s x. %s )' % (U0, LZ, LZ, U0)),
                      dp('recidd', [dp('recnd', [L(lzr)], '%s e. CC' % LZ), dp('rpne0d', [L(lzp)], '%s =/= 0' % LZ)], '( %s x. %s ) = 1' % (LZ, U0))], '( %s x. %s ) = 1' % (U0, LZ))
    ul1 = dp('breqtrd', [ul, u1], '( %s x. ( log ` p ) ) <_ 1' % U0)
    ee = dp('mpbid', [ul1, dp('syl2anc', [dp('remulcld', [u0r, lp], '( %s x. ( log ` p ) ) e. RR' % U0), a1(w, Ap, '1re', '1 e. RR'), w.inst('efle')],
                              '( ( %s x. ( log ` p ) ) <_ 1 <-> ( exp ` ( %s x. ( log ` p ) ) ) <_ ( exp ` 1 ) )' % (U0, U0))], '( exp ` ( %s x. ( log ` p ) ) ) <_ ( exp ` 1 )' % U0)
    pule = dp('eqbrtrd', [pue, ee], '%s <_ ( exp ` 1 )' % PU)
    pvp = dp('rpcxpcld', [prp, cla.mem('-u ( 1 + %s )' % U0, 'RR')], '%s e. RR+' % PV)
    k3 = dp('lemul2ad', [dp('rpred', [dp('rpcxpcld', [prp, u0r], '%s e. RR+' % PU)], '%s e. RR' % PU), dp('rpred', [a1(w, Ap, None, None)] if False else [dp('syl', [a1(w, Ap, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR'),
                         dp('rpred', [pvp], '%s e. RR' % PV), dp('rpge0d', [pvp], '0 <_ %s' % PV), pule], '( %s x. %s ) <_ ( %s x. ( exp ` 1 ) )' % (PV, PU, PV))
    k4 = dp('eqbrtrd', [pm1e, k3], '%s <_ ( %s x. ( exp ` 1 ) )' % (PM1, PV))
    k5 = dp('lemul2ad', [dp('rpred', [pm1p], '%s e. RR' % PM1), dp('remulcld', [dp('rpred', [pvp], '%s e. RR' % PV), dp('rpred', [dp('syl', [a1(w, Ap, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR')],
                                                                         '( %s x. ( exp ` 1 ) ) e. RR' % PV),
                         dp('remulcld', [a1(w, Ap, '1re', '1 e. RR'), lp], '( 1 x. ( log ` p ) ) e. RR'), dp('mulge0d', [a1(w, Ap, '1re', '1 e. RR'), lp, a1(w, Ap, '0le1', '0 <_ 1'), lp0], '0 <_ ( 1 x. ( log ` p ) )'), k4],
            '( ( 1 x. ( log ` p ) ) x. %s ) <_ ( ( 1 x. ( log ` p ) ) x. ( %s x. ( exp ` 1 ) ) )' % (PM1, PV))
    VP = VMT('p', U0)
    vmp = dp('syl', [pm['pr'], w.inst('vmaprm')], '( Lam ` p ) = ( log ` p )')
    clr = Closure(w, Ap, {'( log ` p )': ('CC', dp('recnd', [lp], '( log ` p ) e. CC')), PV: ('CC', dp('rpcnd', [pvp], '%s e. CC' % PV)), '( exp ` 1 )': ('CC', dp('rpcnd', [dp('syl', [a1(w, Ap, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. CC'))})
    for a in ('( log ` p )', PV, '( exp ` 1 )'):
        clr.atom(a)
    r1 = ringeq(w, Ap, '( ( 1 x. ( log ` p ) ) x. ( %s x. ( exp ` 1 ) ) )' % PV, '( ( exp ` 1 ) x. ( ( log ` p ) x. %s ) )' % PV, clr)
    r2 = dp('oveq2d', [dp('oveq1d', [vmp], '%s = ( ( log ` p ) x. %s )' % (VP, PV))], '( ( exp ` 1 ) x. %s ) = ( ( exp ` 1 ) x. ( ( log ` p ) x. %s ) )' % (VP, PV))
    k6 = dp('breqtrd', [k5, dp('eqtr4d', [r1, r2], '( ( 1 x. ( log ` p ) ) x. ( %s x. ( exp ` 1 ) ) ) = ( ( exp ` 1 ) x. %s )' % (PV, VP))], '( ( 1 x. ( log ` p ) ) x. %s ) <_ ( ( exp ` 1 ) x. %s )' % (PM1, VP))
    # |CP| <_ e VMT
    acp = dp('eqbrtrd', [abs_, dp('letrd', [dp('remulcld', [dp('remulcld', [ach, lp], '( ( abs ` %s ) x. ( log ` p ) ) e. RR' % CH), dp('rpred', [pm1p], '%s e. RR' % PM1)], '( ( ( abs ` %s ) x. ( log ` p ) ) x. %s ) e. RR' % (CH, PM1)),
                                           dp('remulcld', [dp('remulcld', [a1(w, Ap, '1re', '1 e. RR'), lp], '( 1 x. ( log ` p ) ) e. RR'), dp('rpred', [pm1p], '%s e. RR' % PM1)], '( ( 1 x. ( log ` p ) ) x. %s ) e. RR' % PM1),
                                           dp('remulcld', [dp('rpred', [dp('syl', [a1(w, Ap, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR'), vmfacts(w, Ap, 'p', pn, u0r)[0]], '( ( exp ` 1 ) x. %s ) e. RR' % VP),
                                           k2, k6], '( ( ( abs ` %s ) x. ( log ` p ) ) x. %s ) <_ ( ( exp ` 1 ) x. %s )' % (CH, PM1, VP))], '( abs ` %s ) <_ ( ( exp ` 1 ) x. %s )' % (CP('p'), VP))
    # sums
    psf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` U ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` U ) )' % PSU)], '%s e. Fin' % PSU)
    cpc = dp('mulcld', [dp('mulcld', [chc, dp('recnd', [lp], '( log ` p ) e. CC')], '( %s x. ( log ` p ) ) e. CC' % CH), dp('cxpcld', [pc, mtc], '%s e. CC' % PM)], '%s e. CC' % CP('p'))
    SW = PWS('T', 'Y', 'U')
    s1 = d('fsumabs', [psf, cpc], '( abs ` %s ) <_ sum_ p e. %s ( abs ` %s )' % (SW, PSU, CP('p')))
    e1r = dp('rpred', [dp('syl', [a1(w, Ap, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR')
    s2 = d('fsumle', [psf, dp('abscld', [cpc], '( abs ` %s ) e. RR' % CP('p')), dp('remulcld', [e1r, vmfacts(w, Ap, 'p', pn, u0r)[0]], '( ( exp ` 1 ) x. %s ) e. RR' % VP), acp],
           'sum_ p e. %s ( abs ` %s ) <_ sum_ p e. %s ( ( exp ` 1 ) x. %s )' % (PSU, CP('p'), PSU, VP))
    e1a = d('rpred', [d('syl', [a1(w, A0, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '( exp ` 1 ) e. RR')
    s3 = d('fsummulc2', [psf, d('recnd', [e1a], '( exp ` 1 ) e. CC'), dp('recnd', [vmfacts(w, Ap, 'p', pn, u0r)[0]], '%s e. CC' % VP)],
           '( ( exp ` 1 ) x. sum_ p e. %s %s ) = sum_ p e. %s ( ( exp ` 1 ) x. %s )' % (PSU, VP, PSU, VP))
    cb = w.s([vmcong(w, 'p', 'k', U0)], 'cbvsumv', 'sum_ p e. %s %s = sum_ k e. %s %s' % (PSU, VP, PSU, VMT('k', U0)))
    pss = d('sstrd', [a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` U ) )' % PSU), d('syl', [a1(w, A0, '1nn', '1 e. NN'), w.inst('fzssnn')], '( 1 ... ( |_ ` U ) ) C_ NN')], '%s C_ NN' % PSU)
    vm = use(w, A0, 'kd2vmp', {'U': U0, 'A': PSU}, d('jca', [d('jca', [u0p, u01], '( %s e. RR+ /\\ %s <_ 1 )' % (U0, U0)), d('jca', [psf, pss], '( %s e. Fin /\\ %s C_ NN )' % (PSU, PSU))],
                                                         '( ( %s e. RR+ /\\ %s <_ 1 ) /\\ ( %s e. Fin /\\ %s C_ NN ) )' % (U0, U0, PSU, PSU)))
    VS = 'sum_ p e. %s %s' % (PSU, VP)
    vm2 = d('eqbrtrd', [w.s([cb], 'a1i', '( %s -> %s = sum_ k e. %s %s )' % (A0, VS, PSU, VMT('k', U0))), vm], '%s <_ ( ( ( 5 / 4 ) / %s ) + 5 )' % (VS, U0))
    q1 = d('divdiv2d', [w.s([num.cc(w, '( 5 / 4 )')], 'a1i', '( %s -> ( 5 / 4 ) e. CC )' % A0), a1(w, A0, 'ax-1cn', '1 e. CC'), d('recnd', [lzr], '%s e. CC' % LZ), a1(w, A0, 'ax-1ne0', '1 =/= 0'), d('rpne0d', [lzp], '%s =/= 0' % LZ)],
           '( ( 5 / 4 ) / %s ) = ( ( ( 5 / 4 ) x. %s ) / 1 )' % (U0, LZ))
    q2 = d('eqtrd', [q1, d('div1d', [d('mulcld', [w.s([num.cc(w, '( 5 / 4 )')], 'a1i', '( %s -> ( 5 / 4 ) e. CC )' % A0), d('recnd', [lzr], '%s e. CC' % LZ)], '( ( 5 / 4 ) x. %s ) e. CC' % LZ)],
                                  '( ( ( 5 / 4 ) x. %s ) / 1 ) = ( ( 5 / 4 ) x. %s )' % (LZ, LZ))], '( ( 5 / 4 ) / %s ) = ( ( 5 / 4 ) x. %s )' % (U0, LZ))
    vm3 = d('breqtrd', [vm2, d('oveq1d', [q2], '( ( ( 5 / 4 ) / %s ) + 5 ) = ( ( ( 5 / 4 ) x. %s ) + 5 )' % (U0, LZ))], '%s <_ ( ( ( 5 / 4 ) x. %s ) + 5 )' % (VS, LZ))
    vsr = d('fsumrecl', [psf, vmfacts(w, Ap, 'p', pn, u0r)[0]], '%s e. RR' % VS)
    s4 = d('lemul2ad', [vsr, clz.mem('( ( ( 5 / 4 ) x. %s ) + 5 )' % LZ, 'RR'), e1a, d('rpge0d', [d('syl', [a1(w, A0, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')], '0 <_ ( exp ` 1 )'), vm3],
           '( ( exp ` 1 ) x. %s ) <_ ( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) )' % (VS, LZ))
    RH = '( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) )' % LZ
    t1 = d('letrd', [d('abscld', [d('fsumcl', [psf, cpc], '%s e. CC' % SW)], '( abs ` %s ) e. RR' % SW), d('fsumrecl', [psf, dp('abscld', [cpc], '( abs ` %s ) e. RR' % CP('p'))], 'sum_ p e. %s ( abs ` %s ) e. RR' % (PSU, CP('p'))),
                     d('fsumrecl', [psf, dp('remulcld', [e1r, vmfacts(w, Ap, 'p', pn, u0r)[0]], '( ( exp ` 1 ) x. %s ) e. RR' % VP)], 'sum_ p e. %s ( ( exp ` 1 ) x. %s ) e. RR' % (PSU, VP)), s1, s2],
            '( abs ` %s ) <_ sum_ p e. %s ( ( exp ` 1 ) x. %s )' % (SW, PSU, VP))
    t2 = d('breqtrrd', [t1, s3], '( abs ` %s ) <_ ( ( exp ` 1 ) x. %s )' % (SW, VS))
    fin = d('letrd', [d('abscld', [d('fsumcl', [psf, cpc], '%s e. CC' % SW)], '( abs ` %s ) e. RR' % SW), d('remulcld', [e1a, vsr], '( ( exp ` 1 ) x. %s ) e. RR' % VS),
                      d('remulcld', [e1a, clz.mem('( ( ( 5 / 4 ) x. %s ) + 5 )' % LZ, 'RR')], '%s e. RR' % RH), t2, s4], '( abs ` %s ) <_ %s' % (SW, RH))
    w.qed([fin], 'idi', S['kd2wb'])
    return only_run(w, only)


def cpcc(w, Ah, p, pn, nxh, tr):
    dd = lambda ref, h, c: D(w, Ah, ref, h, c)
    CH = CHV(p)
    pc = dd('nncnd', [pn], '%s e. CC' % p)
    lg = dd('recnd', [dd('relogcld', [dd('nnrpd', [pn], '%s e. RR+' % p)], '( log ` %s ) e. RR' % p)], '( log ` %s ) e. CC' % p)
    MT = '( -u 1 - ( T x. _i ) )'
    mtc = dd('subcld', [dd('negcld', [a1(w, Ah, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), dd('mulcld', [dd('recnd', [tr], 'T e. CC'), a1(w, Ah, 'ax-icn', '_i e. CC')], '( T x. _i ) e. CC')], '%s e. CC' % MT)
    return dd('mulcld', [dd('mulcld', [dd('syl2anc', [nxh, pn, w.inst('lchrcl')], '%s e. CC' % CH), lg], '( %s x. ( log ` %s ) ) e. CC' % (CH, p)),
                         dd('cxpcld', [pc, mtc], '( %s ^c %s ) e. CC' % (p, MT))], '%s e. CC' % CP(p))


def gen_pwsif():
    w = W('kd2pwsif', 'The window sum below ` Z ` as an indicator sum over the fixed window ` PS ( Y , Z ) ` : ` S ( U ) = sum_ p e. PS ( Y , Z ) if ( p <_ U , c_p , 0 ) ` for ` U <_ Z ` (Lean ` sum_Icc_eq_primeWindowSum ` ).')
    A0 = S['kd2pwsif'].split(' -> sum_')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    nxh = d('simp1', [], NXH); g2 = d('simp2', [], '( T e. RR /\\ Y e. RR )'); g3 = d('simp3', [], '( Z e. RR /\\ U e. RR /\\ U <_ Z )')
    tr = d('simpld', [g2], 'T e. RR'); yr = d('simprd', [g2], 'Y e. RR')
    zr = d('simp1d', [g3], 'Z e. RR'); ur = d('simp2d', [g3], 'U e. RR'); uz_ = d('simp3d', [g3], 'U <_ Z')
    PU = PSET('Y', 'U'); PZ = PSET('Y', 'Z')
    IF = lambda p: 'if ( %s <_ U , %s , 0 )' % (p, CP(p))
    # A C_ B
    fl = d('syl3anc', [ur, zr, uz_, w.inst('flword2')], '( |_ ` Z ) e. ( ZZ>= ` ( |_ ` U ) )')
    fss = d('syl', [fl, w.inst('fzss2')], '( 1 ... ( |_ ` U ) ) C_ ( 1 ... ( |_ ` Z ) )')
    Ap = '( %s /\\ p e. %s )' % (A0, PU)
    pm = psmem(w, Ap, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PU)), 'Y', 'U')
    ae = w.s([w.s([], 'eleq1', '( a = p -> ( a e. Prime <-> p e. Prime ) )'), w.s([], 'breq2', '( a = p -> ( Y < a <-> Y < p ) )')], 'anbi12d',
             '( a = p -> ( ( a e. Prime /\\ Y < a ) <-> ( p e. Prime /\\ Y < p ) ) )')
    pinz = D(w, Ap, 'elrabd', [ae, D(w, Ap, 'sseldd', [lift(w, fss, Ap), pm['pf']], 'p e. ( 1 ... ( |_ ` Z ) )'), D(w, Ap, 'jca', [pm['pr'], pm['yp']], '( p e. Prime /\\ Y < p )')], 'p e. %s' % PZ)
    sub = d('ssrdv', [w.s([pinz], 'ex', '( %s -> ( p e. %s -> p e. %s ) )' % (A0, PU, PZ))], '%s C_ %s' % (PU, PZ))
    # on A: if = CP
    prr = D(w, Ap, 'nnred', [pm['pn']], 'p e. RR')
    ple = D(w, Ap, 'letrd', [prr, D(w, Ap, 'zred', [D(w, Ap, 'flcld', [lift(w, ur, Ap)], '( |_ ` U ) e. ZZ')], '( |_ ` U ) e. RR'), lift(w, ur, Ap), pm['pl'], D(w, Ap, 'syl', [lift(w, ur, Ap), w.inst('flle')], '( |_ ` U ) <_ U')], 'p <_ U')
    ifa = D(w, Ap, 'syl', [ple, w.inst('iftrue')], '%s = %s' % (IF('p'), CP('p')))
    s1 = d('sumeq2dv', [D(w, Ap, 'eqcomd', [ifa], '%s = %s' % (CP('p'), IF('p')))], '%s = sum_ p e. %s %s' % (PWS('T', 'Y', 'U'), PU, IF('p')))
    # sumss
    ifc = D(w, Ap, 'eqeltrd', [ifa, cpcc(w, Ap, 'p', pm['pn'], lift(w, nxh, Ap), lift(w, tr, Ap))], '%s e. CC' % IF('p'))
    Ad = '( %s /\\ p e. ( %s \\ %s ) )' % (A0, PZ, PU)
    pd = w.s([], 'simpr', '( %s -> p e. ( %s \\ %s ) )' % (Ad, PZ, PU))
    pdz = D(w, Ad, 'syl', [pd, w.inst('eldifi')], 'p e. %s' % PZ); pdn = D(w, Ad, 'syl', [pd, w.inst('eldifn')], '-. p e. %s' % PU)
    pmz = psmem(w, Ad, 'p', pdz, 'Y', 'Z')
    Adl = '( %s /\\ p <_ U )' % Ad
    pz_ = D(w, Adl, 'nnzd', [lift(w, pmz['pn'], Adl)], 'p e. ZZ')
    pfl = D(w, Adl, 'mpbid', [w.s([], 'simpr', '( %s -> p <_ U )' % Adl), D(w, Adl, 'syl2anc', [lift(w, ur, Adl), pz_, w.inst('flge')], '( p <_ U <-> p <_ ( |_ ` U ) )')], 'p <_ ( |_ ` U )')
    pinu = D(w, Adl, 'elfzd', [a1(w, Adl, '1z', '1 e. ZZ'), D(w, Adl, 'flcld', [lift(w, ur, Adl)], '( |_ ` U ) e. ZZ'), pz_, D(w, Adl, 'nnge1d', [lift(w, pmz['pn'], Adl)], '1 <_ p'), pfl], 'p e. ( 1 ... ( |_ ` U ) )')
    inpu = D(w, Adl, 'elrabd', [ae, pinu, D(w, Adl, 'jca', [lift(w, pmz['pr'], Adl), lift(w, pmz['yp'], Adl)], '( p e. Prime /\\ Y < p )')], 'p e. %s' % PU)
    nle = D(w, Ad, 'mtod', [pdn, w.s([inpu], 'ex', '( %s -> ( p <_ U -> p e. %s ) )' % (Ad, PU))], '-. p <_ U')
    ifz = D(w, Ad, 'syl', [nle, w.inst('iffalse')], '%s = 0' % IF('p'))
    bss = d('sstrd', [a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PZ), a1(w, A0, 'fzssuz', '( 1 ... ( |_ ` Z ) ) C_ ( ZZ>= ` 1 )')], '%s C_ ( ZZ>= ` 1 )' % PZ)
    s2 = d('sumss', [sub, ifc, ifz, bss], 'sum_ p e. %s %s = sum_ p e. %s %s' % (PU, IF('p'), PZ, IF('p')))
    fin = d('eqtrd', [s1, s2], '%s = sum_ p e. %s %s' % (PWS('T', 'Y', 'U'), PZ, IF('p')))
    w.qed([fin], 'idi', S['kd2pwsif'])
    return only_run(w, only)


if __name__ == '__main__':
    gen_wb()
    gen_pwsif()
