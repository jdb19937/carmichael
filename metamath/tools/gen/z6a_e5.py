"""Sortie Z6a (block E-late): the contour integrand GR(R) of DetectionShift section 2 and blueprint Lemma 4.2.

z6grcn   GR(R) is continuous on DS (z6gamhold, cxfcn, E ( S + w ) through cncfcompt2, z6mrhol).
z6ectri  the pointwise bound on Re ( S + W ) = 1/100 (helpers z6eci1 .. z6eci3).
z6ectrl  the line integral on Re w = CL exists and is below X ^ CL KPT z2 KGL R ^ 3 (helpers z6ecl0 .. z6ecl3, z6eck).
z6ectr   | E_ctr | <_ P1 / 8 under (T1) (helpers z6ect1, z6ect3 .. z6ect6, z6ecalg).
Run: MM_DB=sorties/z6a.mm LIN_FAST=1 python3 tools/gen/z6a_e5.py LABEL ..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6alib import *
from z6alib import _C6
from tm import sub
from cl import Closure, split_imp
import lin
import num
from z6a_e3 import conjs, build, apply, unpack, c_
from z5clib import STATEMENTS as Z5CS
for _k, _v in Z5CS.items():
    STATEMENTS.setdefault(_k, _v)

HS = "( `' Re \" ( -u ( Re ` S ) (,) +oo ) )"
CN = lambda X, Y='CC': '( %s -cn-> %s )' % (X, Y)


def hpzss(w, a):
    """( a -> HPZ C_ CC )"""
    dm = w.s([w.s([], 'ref', 'Re : CC --> RR')], 'fdmi', 'dom Re = CC')
    s = w.s([w.s([], 'cnvimass', '%s C_ dom Re' % HPZ), dm], 'sseqtri', '%s C_ CC' % HPZ)
    return c_(w, a, s, '%s C_ CC' % HPZ)


def z6grcn():
    w = W('z6grcn', 'The contour integrand GR(R) of DetectionShift section 2 is continuous on DS: Gamma (z6gamhold), X ^ w (cxfcn), '
                    'E ( S + w ) with Re ( S + w ) > 0, the division by ( S + w ) - 1 =/= 0, and M_r ( S + w ) (z6mrhol).')
    a = ante('z6grcn'); f = unpack(w, a); st = mkst(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']; sc = f['S e. CC']; ecn = f['E e. %s' % CN(HPZ)]
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D); z12 = st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))
    hab = st([st([st([z1rp], 'rpred', '%s e. RR' % Z1D), st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
              st([st([z2rp], 'rpred', '%s e. RR' % Z2D), z12], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca',
             '( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ %s < %s ) )' % (Z1D, Z1D, Z2D, Z1D, Z2D))
    MS = '( s e. CC |-> %s )' % MRr('R', 's')
    mh = st([st([st([hab, f['R e. NN']], 'jca', '( %s /\\ R e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), f['C : NN --> CC']], 'jca',
                '( ( %s /\\ R e. NN ) /\\ C : NN --> CC )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z6mrhol')], 'syl',
            '( %s e. %s /\\ CC C_ dom ( CC _D %s ) )' % (MS, CN('CC'), MS))
    mcn = st([mh], 'simpld', '%s e. %s' % (MS, CN('CC')))
    # the domains
    dsdg = w.s([], 'inss1', '%s C_ %s' % (DS, DG))
    dgcc = w.s([], 'difss', '%s C_ CC' % DG)
    dscc = w.s([dsdg, dgcc], 'sstri', '%s C_ CC' % DS)
    ccss = w.s([], 'ssid', 'CC C_ CC')
    nf = w.s([], 'nfv', 'F/ w %s' % a)
    # Gamma
    idg = w.s([w.s([dsdg, dgcc], 'pm3.2i', '( %s C_ %s /\\ %s C_ CC )' % (DS, DG, DG)), w.inst('cncfmptid')], 'ax-mp',
              '( w e. %s |-> w ) e. %s' % (DS, CN(DS, DG)))
    GM = '( z e. %s |-> ( _G ` z ) )' % DG
    gam = w.s([w.s([], 'z6gamhold', STATEMENTS['z6gamhold'])], 'simpli', '%s e. %s' % (GM, CN(DG)))
    A1 = st([nf, c_(w, a, idg, '( w e. %s |-> w ) e. %s' % (DS, CN(DS, DG))), c_(w, a, gam, '%s e. %s' % (GM, CN(DG))),
             c_(w, a, w.s([], 'ssid', '%s C_ %s' % (DG, DG)), '%s C_ %s' % (DG, DG)), w.s([], 'fveq2', '( z = w -> ( _G ` z ) = ( _G ` w ) )')],
            'cncfcompt2', '( w e. %s |-> ( _G ` w ) ) e. %s' % (DS, CN(DS)))
    # X ^ w
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    xrp = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    A2 = st([xrp, c_(w, a, dscc, '%s C_ CC' % DS), w.inst('cxfcn')], 'syl2anc', '( w e. %s |-> ( %s ^c w ) ) e. %s' % (DS, XPD, CN(DS)))
    A12 = w.s([A1, A2], 'mulcncf', '( %s -> ( w e. %s |-> ( ( _G ` w ) x. ( %s ^c w ) ) ) e. %s )' % (a, DS, XPD, CN(DS)))
    # S + w
    dsccA = c_(w, a, dscc, '%s C_ CC' % DS); ccA = c_(w, a, ccss, 'CC C_ CC')
    cs = st([sc, dsccA, ccA, w.inst('cncfmptc')], 'syl3anc', '( w e. %s |-> S ) e. %s' % (DS, CN(DS)))
    ci = st([dsccA, ccA, w.inst('cncfmptid')], 'syl2anc', '( w e. %s |-> w ) e. %s' % (DS, CN(DS)))
    SP = '( w e. %s |-> ( S + w ) )' % DS
    spc = w.s([cs, ci], 'addcncf', '( %s -> %s e. %s )' % (a, SP, CN(DS)))
    # pointwise facts on DS
    b = '( %s /\\ w e. %s )' % (a, DS); sb = mkst(w, b)
    wds = sb([], 'simpr', 'w e. %s' % DS)
    wdg = sb([wds], 'elin1d', 'w e. %s' % DG)
    wh1 = sb([wds], 'elin2d', 'w e. ( %s \\ { ( 1 - S ) } )' % HS)
    whs = sb([wh1], 'eldifad', 'w e. %s' % HS)
    wns = sb([wh1], 'eldifbd', '-. w e. { ( 1 - S ) }')
    wne = sb([sb([wns, w.s([], 'velsn', '( w e. { ( 1 - S ) } <-> w = ( 1 - S ) )')], 'sylnib', '-. w = ( 1 - S )')], 'neqned', 'w =/= ( 1 - S )')
    scb = w.s([sc], 'adantr', '( %s -> S e. CC )' % b)
    rsb = sb([scb, w.inst('recl')], 'syl', '( Re ` S ) e. RR')
    mel = sb([sb([sb([rsb], 'renegcld', '-u ( Re ` S ) e. RR'), w.inst('rexr')], 'syl', '-u ( Re ` S ) e. RR*'),
              c_(w, b, w.s([], 'pnfxr', '+oo e. RR*'), '+oo e. RR*'), w.inst('z6melst')], 'syl2anc',
             '( w e. %s <-> ( w e. CC /\\ ( -u ( Re ` S ) < ( Re ` w ) /\\ ( Re ` w ) < +oo ) ) )' % HS)
    wel = sb([whs, mel], 'mpbid', '( w e. CC /\\ ( -u ( Re ` S ) < ( Re ` w ) /\\ ( Re ` w ) < +oo ) )')
    wc = sb([wel], 'simpld', 'w e. CC')
    wlt = sb([sb([wel], 'simprd', '( -u ( Re ` S ) < ( Re ` w ) /\\ ( Re ` w ) < +oo )')], 'simpld', '-u ( Re ` S ) < ( Re ` w )')
    rwb = sb([wc, w.inst('recl')], 'syl', '( Re ` w ) e. RR')
    swc = sb([scb, wc], 'addcld', '( S + w ) e. CC')
    rsw = sb([scb, wc, w.inst('readd')], 'syl2anc', '( Re ` ( S + w ) ) = ( ( Re ` S ) + ( Re ` w ) )')
    rswr = sb([swc, w.inst('recl')], 'syl', '( Re ` ( S + w ) ) e. RR')
    cl = Closure(w, b, {'( Re ` S )': ('RR', rsb), '( Re ` w )': ('RR', rwb), '( Re ` ( S + w ) )': ('RR', rswr)})
    for x in ('( Re ` S )', '( Re ` w )', '( Re ` ( S + w ) )'):
        cl.atom(x)
    p0 = lin.linarith(w, b, [wlt, rsw], '0 < ( Re ` ( S + w ) )', closure=cl)
    mel0 = sb([c_(w, b, w.s([], '0xr', '0 e. RR*'), '0 e. RR*'), c_(w, b, w.s([], 'pnfxr', '+oo e. RR*'), '+oo e. RR*'), w.inst('z6melst')], 'syl2anc',
              '( ( S + w ) e. %s <-> ( ( S + w ) e. CC /\\ ( 0 < ( Re ` ( S + w ) ) /\\ ( Re ` ( S + w ) ) < +oo ) ) )' % HPZ)
    swh = sb([sb([swc, sb([p0, sb([rswr, w.inst('ltpnf')], 'syl', '( Re ` ( S + w ) ) < +oo')], 'jca',
                          '( 0 < ( Re ` ( S + w ) ) /\\ ( Re ` ( S + w ) ) < +oo )')], 'jca',
                  '( ( S + w ) e. CC /\\ ( 0 < ( Re ` ( S + w ) ) /\\ ( Re ` ( S + w ) ) < +oo ) )'), mel0], 'mpbird', '( S + w ) e. %s' % HPZ)
    one = c_(w, b, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    sa = sb([one, scb, wc, w.inst('subadd')], 'syl3anc', '( ( 1 - S ) = w <-> ( S + w ) = 1 )')
    sne = sb([sb([wne], 'necomd', '( 1 - S ) =/= w'), sb([sa], 'necon3bid', '( ( 1 - S ) =/= w <-> ( S + w ) =/= 1 )')], 'mpbid', '( S + w ) =/= 1')
    dn0 = sb([swc, one, sne], 'subne0d', '( ( S + w ) - 1 ) =/= 0')
    dcc = sb([swc, one], 'subcld', '( ( S + w ) - 1 ) e. CC')
    dmem = sb([sb([dcc, dn0], 'jca', '( ( ( S + w ) - 1 ) e. CC /\\ ( ( S + w ) - 1 ) =/= 0 )'),
               w.s([], 'eldifsn', '( ( ( S + w ) - 1 ) e. ( CC \\ { 0 } ) <-> ( ( ( S + w ) - 1 ) e. CC /\\ ( ( S + w ) - 1 ) =/= 0 ) )')],
              'sylibr', '( ( S + w ) - 1 ) e. ( CC \\ { 0 } )')
    # E ( S + w )
    spf = w.s([swh], 'fmpttd', '( %s -> %s : %s --> %s )' % (a, SP, DS, HPZ))
    sph = st([st([hpzss(w, a), spc], 'jca', '( %s C_ CC /\\ %s e. %s )' % (HPZ, SP, CN(DS))), w.inst('cncfcdm')], 'syl',
             '( %s e. %s <-> %s : %s --> %s )' % (SP, CN(DS, HPZ), SP, DS, HPZ))
    spH = st([spf, sph], 'mpbird', '%s e. %s' % (SP, CN(DS, HPZ)))
    NUM = '( E ` ( S + w ) )'
    EM = '( s e. %s |-> ( E ` s ) )' % HPZ
    efn = st([st([ecn, w.inst('cncff')], 'syl', 'E : %s --> CC' % HPZ)], 'ffnd', 'E Fn %s' % HPZ)
    eeq = st([efn, w.s([], 'dffn5', '( E Fn %s <-> E = %s )' % (HPZ, EM))], 'sylib', 'E = %s' % EM)
    em = st([eeq, ecn], 'eqeltrrd', '%s e. %s' % (EM, CN(HPZ)))
    nm = w.s([nf, spH, em, c_(w, a, w.s([], 'ssid', '%s C_ %s' % (HPZ, HPZ)), '%s C_ %s' % (HPZ, HPZ)),
              w.s([], 'fveq2', '( s = ( S + w ) -> ( E ` s ) = %s )' % NUM)], 'cncfcompt2', '( %s -> ( w e. %s |-> %s ) e. %s )' % (a, DS, NUM, CN(DS)))
    # ( S + w ) - 1
    c1 = st([c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC'), dsccA, ccA, w.inst('cncfmptc')], 'syl3anc', '( w e. %s |-> 1 ) e. %s' % (DS, CN(DS)))
    DM = '( w e. %s |-> ( ( S + w ) - 1 ) )' % DS
    dmc = w.s([spc, c1], 'subcncf', '( %s -> %s e. %s )' % (a, DM, CN(DS)))
    dmf = w.s([dmem], 'fmpttd', '( %s -> %s : %s --> ( CC \\ { 0 } ) )' % (a, DM, DS))
    dmh = st([st([c_(w, a, w.s([], 'difss', '( CC \\ { 0 } ) C_ CC'), '( CC \\ { 0 } ) C_ CC'), dmc], 'jca',
                 '( ( CC \\ { 0 } ) C_ CC /\\ %s e. %s )' % (DM, CN(DS))), w.inst('cncfcdm')], 'syl',
             '( %s e. %s <-> %s : %s --> ( CC \\ { 0 } ) )' % (DM, CN(DS, '( CC \\ { 0 } )'), DM, DS))
    dmH = st([dmf, dmh], 'mpbird', '%s e. %s' % (DM, CN(DS, '( CC \\ { 0 } )')))
    A3 = w.s([nm, dmH], 'divcncf', '( %s -> ( w e. %s |-> ( %s / ( ( S + w ) - 1 ) ) ) e. %s )' % (a, DS, NUM, CN(DS)))
    # M_r ( S + w )
    A4 = st([nf, spc, mcn, c_(w, a, ccss, 'CC C_ CC'), w.s([], 'fveq2', '( s = ( S + w ) -> %s = %s )' % (MRr('R', 's'), MRr('R', '( S + w )')))],
            'cncfcompt2', '( w e. %s |-> %s ) e. %s' % (DS, MRr('R', '( S + w )'), CN(DS)))
    A34 = w.s([A3, A4], 'mulcncf', '( %s -> ( w e. %s |-> ( ( %s / ( ( S + w ) - 1 ) ) x. %s ) ) e. %s )' % (a, DS, NUM, MRr('R', '( S + w )'), CN(DS)))
    w.qed([A12, A34], 'mulcncf', STATEMENTS['z6grcn'])
    return w


# ------------------------------------------------------------------ z6ectri and its helpers
def z6eci1():
    w = W('z6eci1', 'Helper of z6ectri: ( G X ) ( V M ) <_ ( ( X K ) Z ) ( G Q ) for nonnegative G , X , V , M with V <_ K Q and M <_ Z.')
    a = ante('z6eci1'); f = unpack(w, a); st = mkst(w, a)
    R = lambda x: f['%s e. RR' % x]
    cl = Closure(w, a, {x: ('RR', R(x)) for x in 'G X V M K Q Z'.split()})
    for x in 'G X V M K Q Z'.split():
        cl.atom(x)
    KQ = '( K x. Q )'
    vm = st([R('V'), cl.mem(KQ, 'RR'), R('M'), R('Z'), f['0 <_ V'], f['0 <_ M'], f['V <_ %s' % KQ], f['M <_ Z']], 'lemul12ad',
            '( V x. M ) <_ ( %s x. Z )' % KQ)
    gx0 = st([R('G'), R('X'), f['0 <_ G'], f['0 <_ X']], 'mulge0d', '0 <_ ( G x. X )')
    p = st([cl.mem('( V x. M )', 'RR'), cl.mem('( %s x. Z )' % KQ, 'RR'), cl.mem('( G x. X )', 'RR'), gx0, vm], 'lemul2ad',
           '( ( G x. X ) x. ( V x. M ) ) <_ ( ( G x. X ) x. ( %s x. Z ) )' % KQ)
    old = lin.MAXDEG; lin.MAXDEG = 6
    e = lin.lineq(w, a, '( ( G x. X ) x. ( %s x. Z ) )' % KQ, '( ( ( X x. K ) x. Z ) x. ( G x. Q ) )', closure=cl, products=True)
    lin.MAXDEG = old
    w.qed([p, e], 'breqtrd', STATEMENTS['z6eci1'])
    return w


def z6eci2():
    w = W('z6eci2', 'Helper of z6ectri: a point Z on Re = 1/100 lies in HP 0, and 1/200 <_ Re Z <_ 2, Z =/= 1 (the hypotheses of CVXH).')
    a = ante('z6eci2'); st = mkst(w, a)
    RZ = '( Re ` Z )'
    zc = st([], 'simpl', 'Z e. CC'); req = st([], 'simpr', '%s = ( 1 / ; ; 1 0 0 )' % RZ)
    rz = st([zc, w.inst('recl')], 'syl', '%s e. RR' % RZ)
    cl = Closure(w, a, {RZ: ('RR', rz)}); cl.atom(RZ)
    p0 = lin.linarith(w, a, [req], '0 < %s' % RZ, closure=cl)
    g0 = lin.linarith(w, a, [req], '0 <_ %s' % RZ, closure=cl)
    g1 = lin.linarith(w, a, [req], '( 1 / ; ; 2 0 0 ) <_ %s' % RZ, closure=cl)
    g2 = lin.linarith(w, a, [req], '%s <_ 2' % RZ, closure=cl)
    lt1 = lin.linarith(w, a, [req], '%s < 1' % RZ, closure=cl)
    rne = st([rz, lt1], 'ltned', '%s =/= 1' % RZ)
    fv = w.s([w.s([], 'fveq2', '( Z = 1 -> ( Re ` Z ) = ( Re ` 1 ) )'), w.s([], 're1', '( Re ` 1 ) = 1')], 'eqtrdi', '( Z = 1 -> ( Re ` Z ) = 1 )')
    zne = st([rne, w.s([fv], 'necon3i', '( ( Re ` Z ) =/= 1 -> Z =/= 1 )')], 'syl', 'Z =/= 1')
    mel = st([c_(w, a, w.s([], '0xr', '0 e. RR*'), '0 e. RR*'), c_(w, a, w.s([], 'pnfxr', '+oo e. RR*'), '+oo e. RR*'), w.inst('z6melst')], 'syl2anc',
             '( Z e. %s <-> ( Z e. CC /\\ ( 0 < %s /\\ %s < +oo ) ) )' % (HPZ, RZ, RZ))
    zh = st([st([zc, st([p0, st([rz, w.inst('ltpnf')], 'syl', '%s < +oo' % RZ)], 'jca', '( 0 < %s /\\ %s < +oo )' % (RZ, RZ))], 'jca',
                '( Z e. CC /\\ ( 0 < %s /\\ %s < +oo ) )' % (RZ, RZ)), mel], 'mpbird', 'Z e. %s' % HPZ)
    w.qed([st([zh, g0], 'jca', '( Z e. %s /\\ 0 <_ %s )' % (HPZ, RZ)), st([g1, g2, zne], '3jca', '( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 /\\ Z =/= 1 )' % (RZ, RZ))],
          'jca', STATEMENTS['z6eci2'])
    return w


N98 = '-u ( ; 9 8 / ; ; 1 0 0 )'


def z6eci3():
    w = W('z6eci3', 'Helper of z6ectri and z6ectrl: a point W with Re S + Re W = 1/100 (99/100 <_ Re S <_ 1) lies in DS, '
                    'and -1 < Re W <_ -98/100.')
    a = ante('z6eci3'); f = unpack(w, a); st = mkst(w, a)
    RS = '( Re ` S )'; RW = '( Re ` W )'
    sc = f['S e. CC']; wc = f['W e. CC']; heq = f['( %s + %s ) = ( 1 / ; ; 1 0 0 )' % (RS, RW)]
    rs = st([sc, w.inst('recl')], 'syl', '%s e. RR' % RS); rw = st([wc, w.inst('recl')], 'syl', '%s e. RR' % RW)
    one = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    s1 = st([one, sc], 'subcld', '( 1 - S ) e. CC')
    r1s = st([s1, w.inst('recl')], 'syl', '( Re ` ( 1 - S ) ) e. RR')
    cl = Closure(w, a, {RS: ('RR', rs), RW: ('RR', rw), '( Re ` ( 1 - S ) )': ('RR', r1s)})
    for x in (RS, RW, '( Re ` ( 1 - S ) )'):
        cl.atom(x)
    hs1 = f['%s <_ 1' % RS]
    hs99 = f['( ; 9 9 / ; ; 1 0 0 ) <_ %s' % RS]
    gm1 = lin.linarith(w, a, [heq, hs1], '-u 1 < %s' % RW, closure=cl)
    g49 = lin.linarith(w, a, [heq, hs99], '%s <_ -u ( ; 4 9 / ; 5 0 )' % RW, closure=cl)
    r98 = w.s([num._reduce_frac(w, 98, 100)], 'negeqi', '%s = -u ( ; 4 9 / ; 5 0 )' % N98)
    g98 = st([g49, c_(w, a, r98, '%s = -u ( ; 4 9 / ; 5 0 )' % N98)], 'breqtrrd', '%s <_ %s' % (RW, N98))
    IW = '( Im ` W )'
    iw = st([wc, w.inst('imcl')], 'syl', '%s e. RR' % IW)
    gl = st([st([st([rw, gm1, g98], '3jca', '( %s e. RR /\\ -u 1 < %s /\\ %s <_ %s )' % (RW, RW, RW, N98)), iw], 'jca',
                '( ( %s e. RR /\\ -u 1 < %s /\\ %s <_ %s ) /\\ %s e. RR )' % (RW, RW, RW, N98, IW)), w.inst('z6gaml1')], 'syl',
            sub(cns('z6gaml1'), {'C': RW, 'U': IW}))
    WW = '( %s + ( _i x. %s ) )' % (RW, IW)
    wdg0 = st([st([gl], 'simpld', '( %s e. %s /\\ %s =/= 0 )' % (WW, DG, WW))], 'simpld', '%s e. %s' % (WW, DG))
    wdg = st([st([wc, w.inst('replim')], 'syl', 'W = %s' % WW), wdg0], 'eqeltrd', 'W e. %s' % DG)
    # W e. HS
    mel = st([st([st([rs], 'renegcld', '-u %s e. RR' % RS), w.inst('rexr')], 'syl', '-u %s e. RR*' % RS),
              c_(w, a, w.s([], 'pnfxr', '+oo e. RR*'), '+oo e. RR*'), w.inst('z6melst')], 'syl2anc',
             '( W e. %s <-> ( W e. CC /\\ ( -u %s < %s /\\ %s < +oo ) ) )' % (HS, RS, RW, RW))
    lt = lin.linarith(w, a, [heq], '-u %s < %s' % (RS, RW), closure=cl)
    whs = st([st([wc, st([lt, st([rw, w.inst('ltpnf')], 'syl', '%s < +oo' % RW)], 'jca', '( -u %s < %s /\\ %s < +oo )' % (RS, RW, RW))], 'jca',
                 '( W e. CC /\\ ( -u %s < %s /\\ %s < +oo ) )' % (RS, RW, RW)), mel], 'mpbird', 'W e. %s' % HS)
    # W =/= 1 - S
    rsb = st([one, sc, w.inst('resub')], 'syl2anc', '( Re ` ( 1 - S ) ) = ( ( Re ` 1 ) - %s )' % RS)
    re1 = c_(w, a, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    cl.atom('( Re ` 1 )'); cl.leaf('( Re ` 1 )', 'RR', st([one, w.inst('recl')], 'syl', '( Re ` 1 ) e. RR'))
    ltr = lin.linarith(w, a, [heq, rsb, re1], '%s < ( Re ` ( 1 - S ) )' % RW, closure=cl)
    rne = st([rw, ltr], 'ltned', '%s =/= ( Re ` ( 1 - S ) )' % RW)
    wne = st([rne, w.s([w.s([], 'fveq2', '( W = ( 1 - S ) -> %s = ( Re ` ( 1 - S ) ) )' % RW)], 'necon3i',
                       '( %s =/= ( Re ` ( 1 - S ) ) -> W =/= ( 1 - S ) )' % RW)], 'syl', 'W =/= ( 1 - S )')
    wd = st([st([whs, wne], 'jca', '( W e. %s /\\ W =/= ( 1 - S ) )' % HS),
             c_(w, a, w.s([], 'eldifsn', '( W e. ( %s \\ { ( 1 - S ) } ) <-> ( W e. %s /\\ W =/= ( 1 - S ) ) )' % (HS, HS)),
                '( W e. ( %s \\ { ( 1 - S ) } ) <-> ( W e. %s /\\ W =/= ( 1 - S ) ) )' % (HS, HS))], 'mpbird', 'W e. ( %s \\ { ( 1 - S ) } )' % HS)
    wds = st([wdg, wd], 'elind', 'W e. %s' % DS)
    w.qed([wds, st([gm1, g98], 'jca', '( -u 1 < %s /\\ %s <_ %s )' % (RW, RW, N98))], 'jca', STATEMENTS['z6eci3'])
    return w


def z6ectri():
    w = W('z6ectri', 'Lean norm_ectrInt_le: on the line Re ( S + W ) = 1/100 the contour integrand is at most '
                     'X ^ Re W KPT z2 R ^ 3 | Gamma ( W ) | ( 1 + | Im W | ) ^ 2 (abscxp; CVXH at S + W with z6lshift; z5mrnorm).')
    a = ante('z6ectri'); f = unpack(w, a); st = mkst(w, a)
    SW = '( S + W )'
    sc = f['S e. CC']; wc = f['W e. CC']; dr = f['D e. RR']; d1 = f['1 < D']
    swc = st([sc, wc], 'addcld', '%s e. CC' % SW); f['%s e. CC' % SW] = swc
    rsw = st([sc, wc, w.inst('readd')], 'syl2anc', '( Re ` %s ) = ( ( Re ` S ) + ( Re ` W ) )' % SW)
    f['( Re ` %s ) = ( 1 / ; ; 1 0 0 )' % SW] = st([rsw, f['( ( Re ` S ) + ( Re ` W ) ) = ( 1 / ; ; 1 0 0 )']], 'eqtrd',
                                                  '( Re ` %s ) = ( 1 / ; ; 1 0 0 )' % SW)
    s2, c2 = apply(w, a, 'z6eci2', {'Z': SW}, f); conjs(w, a, s2, c2, f)
    s3, c3 = apply(w, a, 'z6eci3', {}, f); conjs(w, a, s3, c3, f)
    # the convexity bound at s = S + W
    body = CVXH[len('A. s e. %s ' % HPZ):]
    idk = w.s([], 'id', '( s = %s -> s = %s )' % (SW, SW))
    cg, inst = w.wcongr(body, {'s': SW}, 's = %s' % SW, {'s': idk})
    cv = w.s([cg], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (SW, HPZ, CVXH, inst))
    cond, vb = split_imp(inst)
    i1 = st([st([f['%s e. %s' % (SW, HPZ)], cv], 'syl', '( %s -> %s )' % (CVXH, inst)), f[CVXH]], 'mpd', inst)
    vle = st([f[cond], i1], 'mpd', vb)
    Q = '( ( E ` %s ) / ( %s - 1 ) )' % (SW, SW); V = '( abs ` %s )' % Q
    ef = st([f['E e. ( %s -cn-> CC )' % HPZ], w.inst('cncff')], 'syl', 'E : %s --> CC' % HPZ)
    ev = st([ef, f['%s e. %s' % (SW, HPZ)]], 'ffvelcdmd', '( E ` %s ) e. CC' % SW)
    one = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    dn = st([swc, one, f['%s =/= 1' % SW]], 'subne0d', '( %s - 1 ) =/= 0' % SW)
    qc = st([ev, st([swc, one], 'subcld', '( %s - 1 ) e. CC' % SW), dn], 'divcld', '%s e. CC' % Q)
    f['%s e. RR' % V] = st([qc, w.inst('abscl')], 'syl', '%s e. RR' % V)
    f['0 <_ %s' % V] = st([qc, w.inst('absge0')], 'syl', '0 <_ %s' % V)
    f['%s <_ %s' % (V, CVXB(SW))] = vle
    ls, lc = apply(w, a, 'z6lshift', {'W': SW, 'V': V}, f)
    # Im ( S + W ) - Im S = Im W
    IS = '( Im ` S )'; IW = '( Im ` W )'
    isc = st([st([sc, w.inst('imcl')], 'syl', '%s e. RR' % IS)], 'recnd', '%s e. CC' % IS)
    iwc = st([st([wc, w.inst('imcl')], 'syl', '%s e. RR' % IW)], 'recnd', '%s e. CC' % IW)
    e1 = st([st([sc, wc, w.inst('imadd')], 'syl2anc', '( Im ` %s ) = ( %s + %s )' % (SW, IS, IW))], 'oveq1d',
            '( ( Im ` %s ) - %s ) = ( ( %s + %s ) - %s )' % (SW, IS, IS, IW, IS))
    e2 = st([e1, st([isc, iwc, w.inst('pncan2')], 'syl2anc', '( ( %s + %s ) - %s ) = %s' % (IS, IW, IS, IW))], 'eqtrd',
            '( ( Im ` %s ) - %s ) = %s' % (SW, IS, IW))
    e3 = st([e2], 'fveq2d', '( abs ` ( ( Im ` %s ) - %s ) ) = ( abs ` %s )' % (SW, IS, IW))
    e4 = st([e3], 'oveq2d', '( 1 + ( abs ` ( ( Im ` %s ) - %s ) ) ) = ( 1 + ( abs ` %s ) )' % (SW, IS, IW))
    e5 = st([e4], 'oveq1d', '( ( 1 + ( abs ` ( ( Im ` %s ) - %s ) ) ) ^ 2 ) = ( ( 1 + ( abs ` %s ) ) ^ 2 )' % (SW, IS, IW))
    QQ = '( ( 1 + ( abs ` %s ) ) ^ 2 )' % IW
    e6 = st([e5], 'oveq2d', '( %s x. ( ( 1 + ( abs ` ( ( Im ` %s ) - %s ) ) ) ^ 2 ) ) = ( %s x. %s )' % (KPT, SW, IS, KPT, QQ))
    vq = st([ls, e6], 'breqtrd', '%s <_ ( %s x. %s )' % (V, KPT, QQ))
    # M_r
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D)
    HABD = sub(HAB0, {'A': Z1D, 'B': Z2D})
    f[HABD] = st([st([st([z1rp], 'rpred', '%s e. RR' % Z1D), st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
                  st([st([z2rp], 'rpred', '%s e. RR' % Z2D), st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))],
                 'jca', HABD)
    ms, mc = apply(w, a, 'z5mrnorm', {'A': Z1D, 'B': Z2D, 'S': SW}, f)
    MV = MRr('R', SW); M = '( abs ` %s )' % MV
    mcc = st([ms, w.inst('z6absle')], 'syl', '%s e. CC' % MV)
    # Gamma ( W ) and X ^ W
    GW = '( _G ` W )'
    gc = st([st([f['W e. %s' % DS]], 'elin1d', 'W e. %s' % DG), w.inst('gamcl')], 'syl', '%s e. CC' % GW)
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    xrp = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    XW = '( %s ^c W )' % XPD; XR = '( %s ^c ( Re ` W ) )' % XPD
    xwc = st([st([xrp], 'rpcnd', '%s e. CC' % XPD), wc], 'cxpcld', '%s e. CC' % XW)
    axw = st([xrp, wc, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = %s' % (XW, XR))
    # | WPT | = ( | G | | X ^ W | ) ( V | M | )
    GX = '( %s x. %s )' % (GW, XW); QM = '( %s x. %s )' % (Q, MV)
    a1 = st([st([gc, xwc], 'mulcld', '%s e. CC' % GX), st([qc, mcc], 'mulcld', '%s e. CC' % QM), w.inst('absmul')], 'syl2anc',
            '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (WPT, GX, QM))
    a2 = st([gc, xwc, w.inst('absmul')], 'syl2anc', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GX, GW, XW))
    a2b = st([a2, st([axw], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (GW, XW, GW, XR))], 'eqtrd',
             '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (GX, GW, XR))
    a3 = st([qc, mcc, w.inst('absmul')], 'syl2anc', '( abs ` %s ) = ( %s x. %s )' % (QM, V, M))
    a4 = st([a1, st([a2b, a3], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( ( abs ` %s ) x. %s ) x. ( %s x. %s ) )' % (GX, QM, GW, XR, V, M))],
            'eqtrd', '( abs ` %s ) = ( ( ( abs ` %s ) x. %s ) x. ( %s x. %s ) )' % (WPT, GW, XR, V, M))
    # the algebra
    AG = '( abs ` %s )' % GW; ZR = '( %s x. ( R ^ 3 ) )' % Z2D
    f['%s e. RR' % AG] = st([gc, w.inst('abscl')], 'syl', '%s e. RR' % AG)
    f['0 <_ %s' % AG] = st([gc, w.inst('absge0')], 'syl', '0 <_ %s' % AG)
    f['%s e. RR' % XR] = st([st([xrp, st([wc, w.inst('recl')], 'syl', '( Re ` W ) e. RR')], 'rpcxpcld', '%s e. RR+' % XR)], 'rpred', '%s e. RR' % XR)
    f['0 <_ %s' % XR] = st([st([xrp, st([wc, w.inst('recl')], 'syl', '( Re ` W ) e. RR')], 'rpcxpcld', '%s e. RR+' % XR)], 'rpge0d', '0 <_ %s' % XR)
    f['%s <_ ( %s x. %s )' % (V, KPT, QQ)] = vq
    f['%s e. RR' % M] = st([mcc, w.inst('abscl')], 'syl', '%s e. RR' % M)
    f['0 <_ %s' % M] = st([mcc, w.inst('absge0')], 'syl', '0 <_ %s' % M)
    f['%s <_ %s' % (M, ZR)] = ms
    cl = Closure(w, a, {'D': ('RR+', drp)})
    f['%s e. RR' % KPT] = kptre(w, a, drp)
    f['%s e. RR' % QQ] = st([st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), st([iwc, w.inst('abscl')], 'syl', '( abs ` %s ) e. RR' % IW)], 'readdcld',
                                '( 1 + ( abs ` %s ) ) e. RR' % IW)], 'resqcld', '%s e. RR' % QQ)
    f['%s e. RR' % ZR] = st([st([z2rp], 'rpred', '%s e. RR' % Z2D), st([st([f['R e. NN']], 'nnred', 'R e. RR'), c_(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')],
                                                                          'reexpcld', '( R ^ 3 ) e. RR')], 'remulcld', '%s e. RR' % ZR)
    bs, bc = apply(w, a, 'z6eci1', {'G': AG, 'X': XR, 'V': V, 'M': M, 'K': KPT, 'Q': QQ, 'Z': ZR}, f)
    w.qed([a4, bs], 'eqbrtrd', STATEMENTS['z6ectri'])
    return w


def kptre(w, a, drp):
    """( a -> KPT e. RR ) from ( a -> D e. RR+ )"""
    st = mkst(w, a)
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    ctre = w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
                w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('reexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR')],
               'eqeltri', 'CTau e. RR')
    C6 = '; ; ; ; ; 6 0 0 0 0 0'; D397 = '( D ^c ( ; ; 3 9 7 / ; ; 8 0 0 ) )'
    k1 = st([c_(w, a, num.real(w, C6), '%s e. RR' % C6), c_(w, a, ctre, 'CTau e. RR')], 'remulcld', '( %s x. CTau ) e. RR' % C6)
    k2 = st([k1, st([st([drp, c_(w, a, num.real(w, '( ; ; 3 9 7 / ; ; 8 0 0 )'), '( ; ; 3 9 7 / ; ; 8 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % D397)], 'rpred',
                    '%s e. RR' % D397)], 'remulcld', '( ( %s x. CTau ) x. %s ) e. RR' % (C6, D397))
    return st([k2, st([drp], 'relogcld', '( log ` D ) e. RR')], 'remulcld', '%s e. RR' % KPT)


# ------------------------------------------------------------------ z6ectrl and its helpers
def r98(w, a):
    """( a -> -u ( 98 / 100 ) = -u ( 49 / 50 ) )"""
    r = w.s([num._reduce_frac(w, 98, 100)], 'negeqi', '%s = -u ( ; 4 9 / ; 5 0 )' % N98)
    return c_(w, a, r, '%s = -u ( ; 4 9 / ; 5 0 )' % N98)


def z6ecl0():
    w = W('z6ecl0', 'Helper of z6ectrl: the left contour line CL = 1/100 - Re S lies in [ -99/100 , -98/100 ].')
    a = ante('z6ecl0'); f = unpack(w, a); st = mkst(w, a)
    RS = '( Re ` S )'
    rs = st([f['S e. CC'], w.inst('recl')], 'syl', '%s e. RR' % RS)
    cl = Closure(w, a, {RS: ('RR', rs)}); cl.atom(RS)
    clr = cl.mem(CL, 'RR')
    g1 = lin.linarith(w, a, [f['%s <_ 1' % RS]], '-u ( ; 9 9 / ; ; 1 0 0 ) <_ %s' % CL, closure=cl)
    g2 = lin.linarith(w, a, [f['( ; 9 9 / ; ; 1 0 0 ) <_ %s' % RS]], '%s <_ -u ( ; 4 9 / ; 5 0 )' % CL, closure=cl)
    g3 = st([g2, r98(w, a)], 'breqtrrd', '%s <_ %s' % (CL, N98))
    w.qed([clr, g1, g3], '3jca', STATEMENTS['z6ecl0'])
    return w


def z6eck():
    w = W('z6eck', 'Helper of z6ectrl: the constant X ^ Q KPT z2 R ^ 3 is positive.')
    a = ante('z6eck'); f = unpack(w, a); st = mkst(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    xrp = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    xq = st([xrp, f['Q e. RR']], 'rpcxpcld', '( %s ^c Q ) e. RR+' % XPD)
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    ctrp = w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
                w.s([w.s([], '2rp', '2 e. RR+'), w.s([knn], 'nnzi', '( 2 ^ ; ; 8 0 0 ) e. ZZ'), w.inst('rpexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR+')],
               'eqeltri', 'CTau e. RR+')
    C6 = '; ; ; ; ; 6 0 0 0 0 0'; D397 = '( D ^c ( ; ; 3 9 7 / ; ; 8 0 0 ) )'
    k1 = st([c_(w, a, num.rp(w, C6), '%s e. RR+' % C6), c_(w, a, ctrp, 'CTau e. RR+')], 'rpmulcld', '( %s x. CTau ) e. RR+' % C6)
    k2 = st([k1, st([drp, c_(w, a, num.real(w, '( ; ; 3 9 7 / ; ; 8 0 0 )'), '( ; ; 3 9 7 / ; ; 8 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % D397)],
            'rpmulcld', '( ( %s x. CTau ) x. %s ) e. RR+' % (C6, D397))
    kp = st([k2, st([dr, d1, w.inst('rplogcl')], 'syl2anc', '( log ` D ) e. RR+')], 'rpmulcld', '%s e. RR+' % KPT)
    z2 = st([drp, c_(w, a, num.real(w, '( ; 6 3 / ; ; 1 0 0 )'), '( ; 6 3 / ; ; 1 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % Z2D)
    r3 = st([st([f['R e. NN']], 'nnrpd', 'R e. RR+'), c_(w, a, w.s([], '3z', '3 e. ZZ'), '3 e. ZZ')], 'rpexpcld', '( R ^ 3 ) e. RR+')
    w.qed([st([xq, kp], 'rpmulcld', '( ( %s ^c Q ) x. %s ) e. RR+' % (XPD, KPT)), st([z2, r3], 'rpmulcld', '( %s x. ( R ^ 3 ) ) e. RR+' % Z2D)],
          'rpmulcld', STATEMENTS['z6eck'])
    return w


def z6ecl2():
    w = W('z6ecl2', 'Helper of z6ectrl: on -99/100 <_ C <_ -98/100, | Gamma ( C + i U ) | ( 1 + | U | ) ^ 2 <_ ( 50/49 ) 1632 128 2 ^ ( - | U | / 4 ) '
                    '(z6gaml1, z6gam1632 at ( C + 1 ) + i U, pol2exp).')
    a = ante('z6ecl2'); f = unpack(w, a); st = mkst(w, a)
    cr = f['C e. RR']; ur = f['U e. RR']
    c98 = st([f['C <_ %s' % N98], r98(w, a)], 'breqtrd', 'C <_ -u ( ; 4 9 / ; 5 0 )')
    cl = Closure(w, a, {'C': ('RR', cr), 'U': ('RR', ur)}); cl.atom('C'); cl.atom('U')
    gm1 = lin.linarith(w, a, [f['-u ( ; 9 9 / ; ; 1 0 0 ) <_ C']], '-u 1 < C', closure=cl)
    gl = st([st([st([cr, gm1, f['C <_ %s' % N98]], '3jca', '( C e. RR /\\ -u 1 < C /\\ C <_ %s )' % N98), ur], 'jca',
                '( ( C e. RR /\\ -u 1 < C /\\ C <_ %s ) /\\ U e. RR )' % N98), w.inst('z6gaml1')], 'syl', cns('z6gaml1'))
    Z1 = '( ( C + 1 ) + ( _i x. U ) )'; Z0 = '( C + ( _i x. U ) )'
    g = '( abs ` ( _G ` %s ) )' % Z0; g1 = '( abs ` ( _G ` %s ) )' % Z1
    gg1 = st([st([gl], 'simprd', '( ( _G ` %s ) = ( ( _G ` %s ) / %s ) /\\ %s <_ ( ( ; 5 0 / ; 4 9 ) x. %s ) )' % (Z0, Z1, Z0, g, g1))],
             'simprd', '%s <_ ( ( ; 5 0 / ; 4 9 ) x. %s )' % (g, g1))
    dg0 = st([st([gl], 'simpld', '( %s e. %s /\\ %s =/= 0 )' % (Z0, DG, Z0))], 'simpld', '%s e. %s' % (Z0, DG))
    # z6gam1632 at Z1
    c1r = st([cr, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'readdcld', '( C + 1 ) e. RR')
    z1c = st([st([c1r], 'recnd', '( C + 1 ) e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), st([ur], 'recnd', 'U e. CC')], 'mulcld',
                                                         '( _i x. U ) e. CC')], 'addcld', '%s e. CC' % Z1)
    re1 = st([c1r, ur], 'crred', '( Re ` %s ) = ( C + 1 )' % Z1)
    im1 = st([c1r, ur], 'crimd', '( Im ` %s ) = U' % Z1)
    body = GAMH1632[len('A. d e. CC '):]
    idk = w.s([], 'id', '( d = %s -> d = %s )' % (Z1, Z1))
    cg, inst = w.wcongr(body, {'d': Z1}, 'd = %s' % Z1, {'d': idk})
    cv = w.s([cg], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (Z1, GAMH1632, inst))
    cond, gb = split_imp(inst)
    i1 = st([z1c, cv], 'syl', '( %s -> %s )' % (GAMH1632, inst))
    i2 = st([c_(w, a, w.s([], 'z6gam1632', GAMH1632), GAMH1632), i1], 'mpd', inst)
    lo = lin.linarith(w, a, [f['-u ( ; 9 9 / ; ; 1 0 0 ) <_ C']], '( 1 / ; ; 1 0 0 ) <_ ( C + 1 )', closure=cl)
    hi = lin.linarith(w, a, [c98], '( C + 1 ) <_ 3', closure=cl)
    cnd = st([st([lo, re1], 'breqtrrd', '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % Z1), st([re1, hi], 'eqbrtrd', '( Re ` %s ) <_ 3' % Z1)], 'jca', cond)
    gb1 = st([cnd, i2], 'mpd', gb)
    AU = '( abs ` U )'
    E2U = E2(AU)
    e1 = st([st([st([st([im1], 'fveq2d', '( abs ` ( Im ` %s ) ) = %s' % (Z1, AU))], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 2 ) = ( %s / 2 )' % (Z1, AU))],
                'negeqd', '-u ( ( abs ` ( Im ` %s ) ) / 2 ) = -u ( %s / 2 )' % (Z1, AU))], 'oveq2d', '%s = %s' % (E2('( abs ` ( Im ` %s ) )' % Z1), E2U))
    e2 = st([e1], 'oveq2d', '( ; ; ; 1 6 3 2 x. %s ) = ( ; ; ; 1 6 3 2 x. %s )' % (E2('( abs ` ( Im ` %s ) )' % Z1), E2U))
    g1b = st([gb1, e2], 'breqtrd', '%s <_ ( ; ; ; 1 6 3 2 x. %s )' % (g1, E2U))
    # pol2exp
    auc = st([ur], 'recnd', 'U e. CC')
    aur = st([auc, w.inst('abscl')], 'syl', '%s e. RR' % AU); au0 = st([auc, w.inst('absge0')], 'syl', '0 <_ %s' % AU)
    Q = '( ( 1 + %s ) ^ 2 )' % AU
    pe = st([aur, au0, w.inst('pol2exp')], 'syl2anc', '( %s x. %s ) <_ ( ; ; 1 2 8 x. %s )' % (Q, E2U, E4(AU)))
    # reals
    gc = st([dg0, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % Z0)
    gr = st([gc, w.inst('abscl')], 'syl', '%s e. RR' % g); g0 = st([gc, w.inst('absge0')], 'syl', '0 <_ %s' % g)
    e2r = st([st([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([st([aur], 'rehalfcld', '( %s / 2 ) e. RR' % AU)], 'renegcld', '-u ( %s / 2 ) e. RR' % AU)],
                 'rpcxpcld', '%s e. RR+' % E2U)], 'rpred', '%s e. RR' % E2U)
    e4r = st([st([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([st([aur, c_(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'),
                                                                          c_(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( %s / 4 ) e. RR' % AU)],
                                                                    'renegcld', '-u ( %s / 4 ) e. RR' % AU)], 'rpcxpcld', '%s e. RR+' % E4(AU))], 'rpred', '%s e. RR' % E4(AU))
    qr = st([st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), aur], 'readdcld', '( 1 + %s ) e. RR' % AU)], 'resqcld', '%s e. RR' % Q)
    q0 = st([st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), aur], 'readdcld', '( 1 + %s ) e. RR' % AU)], 'sqge0d', '0 <_ %s' % Q)
    cl2 = Closure(w, a, {})
    for x, r_ in ((g, gr), (E2U, e2r), (E4(AU), e4r), (Q, qr)):
        cl2.leaf(x, 'RR', r_); cl2.atom(x)
    g1r = st([gb1, w.inst('z6absle')], 'syl', '( _G ` %s ) e. CC' % Z1)
    g1rr = st([g1r, w.inst('abscl')], 'syl', '%s e. RR' % g1); cl2.leaf(g1, 'RR', g1rr); cl2.atom(g1)
    K = '( ; 5 0 / ; 4 9 )'
    s1a = st([g1rr, cl2.mem('( ; ; ; 1 6 3 2 x. %s )' % E2U, 'RR'), c_(w, a, num.real(w, K), '%s e. RR' % K), c_(w, a, num.fact(w, K, 'ge0'), '0 <_ %s' % K), g1b],
             'lemul2ad', '( %s x. %s ) <_ ( %s x. ( ; ; ; 1 6 3 2 x. %s ) )' % (K, g1, K, E2U))
    s1 = st([gr, cl2.mem('( %s x. %s )' % (K, g1), 'RR'), cl2.mem('( %s x. ( ; ; ; 1 6 3 2 x. %s ) )' % (K, E2U), 'RR'), gg1, s1a], 'letrd',
            '%s <_ ( %s x. ( ; ; ; 1 6 3 2 x. %s ) )' % (g, K, E2U))
    s2 = st([gr, cl2.mem('( %s x. ( ; ; ; 1 6 3 2 x. %s ) )' % (K, E2U), 'RR'), qr, q0, s1], 'lemul1ad',
            '( %s x. %s ) <_ ( ( %s x. ( ; ; ; 1 6 3 2 x. %s ) ) x. %s )' % (g, Q, K, E2U, Q))
    P = '( %s x. %s )' % (Q, E2U)
    s3 = lin.lineq(w, a, '( ( %s x. ( ; ; ; 1 6 3 2 x. %s ) ) x. %s )' % (K, E2U, Q), '( ( %s x. ; ; ; 1 6 3 2 ) x. %s )' % (K, P), closure=cl2, products=True)
    s5 = st([cl2.mem(P, 'RR'), cl2.mem('( ; ; 1 2 8 x. %s )' % E4(AU), 'RR'), cl2.mem('( %s x. ; ; ; 1 6 3 2 )' % K, 'RR'),
             cl2.ge0('( %s x. ; ; ; 1 6 3 2 )' % K), pe], 'lemul2ad',
            '( ( %s x. ; ; ; 1 6 3 2 ) x. %s ) <_ ( ( %s x. ; ; ; 1 6 3 2 ) x. ( ; ; 1 2 8 x. %s ) )' % (K, P, K, E4(AU)))
    s6 = lin.lineq(w, a, '( ( %s x. ; ; ; 1 6 3 2 ) x. ( ; ; 1 2 8 x. %s ) )' % (K, E4(AU)), '( ( %s x. ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) ) x. %s )' % (K, E4(AU)),
                   closure=cl2, products=True)
    t1 = st([s2, s3], 'breqtrd', '( %s x. %s ) <_ ( ( %s x. ; ; ; 1 6 3 2 ) x. %s )' % (g, Q, K, P))
    t2 = st([cl2.mem('( %s x. %s )' % (g, Q), 'RR'), cl2.mem('( ( %s x. ; ; ; 1 6 3 2 ) x. %s )' % (K, P), 'RR'),
             cl2.mem('( ( %s x. ; ; ; 1 6 3 2 ) x. ( ; ; 1 2 8 x. %s ) )' % (K, E4(AU)), 'RR'), t1, s5], 'letrd',
            '( %s x. %s ) <_ ( ( %s x. ; ; ; 1 6 3 2 ) x. ( ; ; 1 2 8 x. %s ) )' % (g, Q, K, E4(AU)))
    w.qed([t2, s6], 'breqtrd', STATEMENTS['z6ecl2'])
    return w


def _gbody():
    g = GR('R'); pre = '( w e. %s |-> ' % DS
    assert g.startswith(pre) and g.endswith(' )')
    return g[len(pre):-2]


def z6ecl1():
    w = W('z6ecl1', 'Helper of z6ectrl: at the point CL + i U of the left line, which lies in DS, | GR(R) | <_ K0 | Gamma | ( 1 + | U | ) ^ 2 (z6ectri).')
    from z6a_ghlib import mpval
    a = ante('z6ecl1'); f = unpack(w, a); st = mkst(w, a)
    s0, c0 = apply(w, a, 'z6ecl0', {}, f); conjs(w, a, s0, c0, f)
    ur = f['U e. RR']; clr = f['%s e. RR' % CL]
    Z = '( %s + ( _i x. U ) )' % CL
    zc = st([st([clr], 'recnd', '%s e. CC' % CL), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), st([ur], 'recnd', 'U e. CC')], 'mulcld', '( _i x. U ) e. CC')],
            'addcld', '%s e. CC' % Z)
    rew = st([clr, ur], 'crred', '( Re ` %s ) = %s' % (Z, CL)); imw = st([clr, ur], 'crimd', '( Im ` %s ) = U' % Z)
    RS = '( Re ` S )'
    rsc = st([st([f['S e. CC'], w.inst('recl')], 'syl', '%s e. RR' % RS)], 'recnd', '%s e. CC' % RS)
    e1 = st([rew], 'oveq2d', '( %s + ( Re ` %s ) ) = ( %s + %s )' % (RS, Z, RS, CL))
    e2 = st([rsc, c_(w, a, num.cc(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. CC'), w.inst('pncan3')], 'syl2anc', '( %s + %s ) = ( 1 / ; ; 1 0 0 )' % (RS, CL))
    f['%s e. CC' % Z] = zc
    f['( %s + ( Re ` %s ) ) = ( 1 / ; ; 1 0 0 )' % (RS, Z)] = st([e1, e2], 'eqtrd', '( %s + ( Re ` %s ) ) = ( 1 / ; ; 1 0 0 )' % (RS, Z))
    s3, c3 = apply(w, a, 'z6eci3', {'W': Z}, f); conjs(w, a, s3, c3, f)
    mem = f['%s e. %s' % (Z, DS)]
    s4, c4 = apply(w, a, 'z6ectri', {'W': Z}, f)
    v, V = mpval(w, a, 'w', DS, _gbody(), Z, mem)
    ab = st([v], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (GR('R'), Z, V))
    RHS = c4.split(' <_ ', 1)[1]
    b1 = st([ab, s4], 'eqbrtrd', '( abs ` ( %s ` %s ) ) <_ %s' % (GR('R'), Z, RHS))
    rw, new = w.rewrite(RHS, {'( Re ` %s )' % Z: (CL, rew), '( Im ` %s )' % Z: ('U', imw)}, a)
    b2 = st([b1, rw], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ %s' % (GR('R'), Z, new))
    w.qed([mem, b2], 'jca', STATEMENTS['z6ecl1'])
    return w


def z6ecl3():
    w = W('z6ecl3', 'Helper of z6ectrl: the truncated line integral of GR(R) on Re w = CL is at most K0 KGL '
                    '(z6lvert, itgabs, the pointwise bound z6ecl1, the left line moment z6gmoml).')
    a = ante('z6ecl3'); f = unpack(w, a); st = mkst(w, a)
    s0, c0 = apply(w, a, 'z6ecl0', {}, f); conjs(w, a, s0, c0, f)
    clr = f['%s e. RR' % CL]; trp = f['T e. RR+']
    G = GR('R')
    gcs, gcc = apply(w, a, 'z6grcn', {}, f)
    # the line lies in DS
    Zu = '( %s + ( _i x. u ) )' % CL
    au = '( %s /\\ u e. RR )' % a
    ar_ = w.s([w.s([], 'simpll', '( %s -> %s )' % (au, AR)), w.s([], 'simpr', '( %s -> u e. RR )' % au)], 'jca', '( %s -> ( %s /\\ u e. RR ) )' % (au, AR))
    e1u = w.s([ar_, w.inst('z6ecl1')], 'syl', '( %s -> %s )' % (au, sub(cns('z6ecl1'), {'U': 'u'})))
    zdu = w.s([e1u], 'simpld', '( %s -> %s e. %s )' % (au, Zu, DS))
    ald = st([zdu], 'ralrimiva', 'A. u e. RR %s e. %s' % (Zu, DS))
    seg = st([st([st([clr, trp], 'jca', '( %s e. RR /\\ T e. RR+ )' % CL), ald], 'jca', '( ( %s e. RR /\\ T e. RR+ ) /\\ A. u e. RR %s e. %s )' % (CL, Zu, DS)),
              w.inst('z6segd')], 'syl', '( ( %s + ( _i x. -u T ) ) cseg ( %s + ( _i x. T ) ) ) C_ %s' % (CL, CL, DS))
    IO = '( -u T (,) T )'; FU = '( %s ` %s )' % (G, Zu); ITG = 'S. %s %s _d u' % (IO, FU); LIT = LI(G, CL, 'T')
    lv = st([st([st([clr, trp], 'jca', '( %s e. RR /\\ T e. RR+ )' % CL), st([gcs, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( ( %s + ( _i x. -u T ) ) cseg ( %s + ( _i x. T ) ) ) C_ %s )' % (G, DS, CL, CL, DS))],
                'jca', '( ( %s e. RR /\\ T e. RR+ ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( ( %s + ( _i x. -u T ) ) cseg ( %s + ( _i x. T ) ) ) C_ %s ) )' % (CL, G, DS, CL, CL, DS)),
             w.inst('z6lvert')], 'syl', '( ( u e. %s |-> %s ) e. L^1 /\\ %s = ( _i x. %s ) )' % (IO, FU, LIT, ITG))
    ibl = st([lv], 'simpld', '( u e. %s |-> %s ) e. L^1' % (IO, FU)); leq = st([lv], 'simprd', '%s = ( _i x. %s )' % (LIT, ITG))
    # pointwise on ( -T , T )
    Au = '( %s /\\ u e. %s )' % (a, IO); t = mkst(w, Au)
    ur = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au, IO)), w.inst('elioore')], 'syl', '( %s -> u e. RR )' % Au)
    e1 = w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (Au, AR)), ur], 'jca', '( %s -> ( %s /\\ u e. RR ) )' % (Au, AR)), w.inst('z6ecl1')], 'syl',
             '( %s -> %s )' % (Au, sub(cns('z6ecl1'), {'U': 'u'})))
    K0c = K0(CL); g = '( abs ` ( _G ` %s ) )' % Zu; Q = '( ( 1 + ( abs ` u ) ) ^ 2 )'; GQ = '( %s x. %s )' % (g, Q)
    RHS = '( %s x. %s )' % (K0c, GQ)
    pb = t([e1], 'simprd', '( abs ` %s ) <_ %s' % (FU, RHS))
    zdt = t([e1], 'simpld', '%s e. %s' % (Zu, DS))
    fuc = t([pb, w.inst('z6absle')], 'syl', '%s e. CC' % FU)
    gc = t([t([zdt], 'elin1d', '%s e. %s' % (Zu, DG)), w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % Zu)
    gr = t([gc], 'abscld', '%s e. RR' % g)
    uc = t([ur], 'recnd', 'u e. CC')
    qr = t([t([c_(w, Au, w.s([], '1re', '1 e. RR'), '1 e. RR'), t([uc], 'abscld', '( abs ` u ) e. RR')], 'readdcld', '( 1 + ( abs ` u ) ) e. RR')], 'resqcld', '%s e. RR' % Q)
    gqr = t([gr, qr], 'remulcld', '%s e. RR' % GQ)
    gqc = t([gqr], 'recnd', '%s e. CC' % GQ)
    # K0
    krp = st([st([f[HZD3], st([f['R e. NN'], clr], 'jca', '( R e. NN /\\ %s e. RR )' % CL)], 'jca', '( %s /\\ ( R e. NN /\\ %s e. RR ) )' % (HZD3, CL)),
              w.inst('z6eck')], 'syl', '%s e. RR+' % K0c)
    kr = st([krp], 'rpred', '%s e. RR' % K0c); kc = st([kr], 'recnd', '%s e. CC' % K0c); k0 = st([krp], 'rpge0d', '0 <_ %s' % K0c)
    krt = w.s([kr], 'adantr', '( %s -> %s e. RR )' % (Au, K0c))
    rhsr = t([krt, gqr], 'remulcld', '%s e. RR' % RHS)
    # the moment
    mom = st([st([st([clr, f['-u ( ; 9 9 / ; ; 1 0 0 ) <_ %s' % CL], f['%s <_ %s' % (CL, N98)]], '3jca',
                     '( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ %s )' % (CL, CL, CL, N98)), trp], 'jca',
                 '( ( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ %s ) /\\ T e. RR+ )' % (CL, CL, CL, N98)), w.inst('z6gmoml')], 'syl',
              '( %s e. L^1 /\\ %s <_ %s )' % (MOMF(CL), MOM(CL), KGL))
    mibl = st([mom], 'simpld', '%s e. L^1' % MOMF(CL)); mle = st([mom], 'simprd', '%s <_ %s' % (MOM(CL), KGL))
    ib2 = st([kc, gqc, mibl], 'iblmulc2', '( u e. %s |-> %s ) e. L^1' % (IO, RHS))
    AFU = '( abs ` %s )' % FU
    afr = t([fuc], 'abscld', '%s e. RR' % AFU)
    ib1 = st([fuc, ibl], 'iblabs', '( u e. %s |-> %s ) e. L^1' % (IO, AFU))
    ia = st([fuc, ibl], 'itgabs', '( abs ` %s ) <_ S. %s %s _d u' % (ITG, IO, AFU))
    il = st([ib1, ib2, afr, rhsr, pb], 'itgle', 'S. %s %s _d u <_ S. %s %s _d u' % (IO, AFU, IO, RHS))
    im = st([kc, gqc, mibl], 'itgmulc2', '( %s x. %s ) = S. %s %s _d u' % (K0c, MOM(CL), IO, RHS))
    momr = w.s([gqr, mibl], 'itgrecl', '( %s -> %s e. RR )' % (a, MOM(CL)))
    cl = Closure(w, a, {})
    kglr = cl.mem(KGL, 'RR')
    ml = st([momr, kglr, kr, k0, mle], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (K0c, MOM(CL), K0c, KGL))
    itgc = st([fuc, ibl], 'itgcl', '%s e. CC' % ITG)
    itgabsr = st([itgc], 'abscld', '( abs ` %s ) e. RR' % ITG)
    i1r = w.s([afr, ib1], 'itgrecl', '( %s -> S. %s %s _d u e. RR )' % (a, IO, AFU))
    i2r = w.s([rhsr, ib2], 'itgrecl', '( %s -> S. %s %s _d u e. RR )' % (a, IO, RHS))
    ch1 = st([itgabsr, i1r, i2r, ia, il], 'letrd', '( abs ` %s ) <_ S. %s %s _d u' % (ITG, IO, RHS))
    ch2 = st([ch1, im], 'breqtrrd', '( abs ` %s ) <_ ( %s x. %s )' % (ITG, K0c, MOM(CL)))
    ch3 = st([itgabsr, st([kr, momr], 'remulcld', '( %s x. %s ) e. RR' % (K0c, MOM(CL))), st([kr, kglr], 'remulcld', '( %s x. %s ) e. RR' % (K0c, KGL)), ch2, ml],
             'letrd', '( abs ` %s ) <_ ( %s x. %s )' % (ITG, K0c, KGL))
    ic = c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    ae = st([st([leq], 'fveq2d', '( abs ` %s ) = ( abs ` ( _i x. %s ) )' % (LIT, ITG)), st([ic, itgc], 'absmuld', '( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (ITG, ITG))],
            'eqtrd', '( abs ` %s ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (LIT, ITG))
    ai = st([st([c_(w, a, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')], 'oveq1d', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) )' % (ITG, ITG)),
             st([st([itgabsr], 'recnd', '( abs ` %s ) e. CC' % ITG)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (ITG, ITG))], 'eqtrd',
            '( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s )' % (ITG, ITG))
    w.qed([st([ae, ai], 'eqtrd', '( abs ` %s ) = ( abs ` %s )' % (LIT, ITG)), ch3], 'eqbrtrd', STATEMENTS['z6ecl3'])
    return w


def z6ectrl():
    w = W('z6ectrl', 'Lean norm_integral_ectrInt_le: the line integral of GR(R) on Re w = eps2 - beta exists (z6vlcvg with the majorant '
                     'z6ecl1 + z6ecl2) and is at most X ^ CL KPT z2 KGL R ^ 3 (z6rlimle over z6ecl3).')
    a = ante('z6ectrl'); f = unpack(w, a); st = mkst(w, a)
    assert a == AR
    s0, c0 = apply(w, a, 'z6ecl0', {}, f); conjs(w, a, s0, c0, f)
    clr = f['%s e. RR' % CL]
    G = GR('R'); K0c = K0(CL)
    gcs, gcc = apply(w, a, 'z6grcn', {}, f)
    krp = st([st([f[HZD3], st([f['R e. NN'], clr], 'jca', '( R e. NN /\\ %s e. RR )' % CL)], 'jca', '( %s /\\ ( R e. NN /\\ %s e. RR ) )' % (HZD3, CL)),
              w.inst('z6eck')], 'syl', '%s e. RR+' % K0c)
    kr = st([krp], 'rpred', '%s e. RR' % K0c)
    # pointwise on the line
    Zu = '( %s + ( _i x. u ) )' % CL
    au = '( %s /\\ u e. RR )' % a; t = mkst(w, au)
    e1u = w.s([w.s([], 'id', '( %s -> %s )' % (au, au)), w.inst('z6ecl1')], 'syl', '( %s -> %s )' % (au, sub(cns('z6ecl1'), {'U': 'u'})))
    zdu = t([e1u], 'simpld', '%s e. %s' % (Zu, DS))
    ald = st([zdu], 'ralrimiva', 'A. u e. RR %s e. %s' % (Zu, DS))
    g = '( abs ` ( _G ` %s ) )' % Zu; Q = '( ( 1 + ( abs ` u ) ) ^ 2 )'; GQ = '( %s x. %s )' % (g, Q)
    FU = '( %s ` %s )' % (G, Zu)
    pb = t([e1u], 'simprd', '( abs ` %s ) <_ ( %s x. %s )' % (FU, K0c, GQ))
    CC_ = '( ( ; 5 0 / ; 4 9 ) x. ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) )'
    E4u = E4('( abs ` u )')
    hc = t([t([lift_a(w, au, clr), lift_a(w, au, f['-u ( ; 9 9 / ; ; 1 0 0 ) <_ %s' % CL]), lift_a(w, au, f['%s <_ %s' % (CL, N98)])], '3jca',
              '( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ %s )' % (CL, CL, CL, N98)), w.s([], 'simpr', '( %s -> u e. RR )' % au)], 'jca',
           '( ( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ %s ) /\\ u e. RR )' % (CL, CL, CL, N98))
    g2 = t([hc, w.inst('z6ecl2')], 'syl', '%s <_ ( %s x. %s )' % (GQ, CC_, E4u))
    # reals
    ur = w.s([], 'simpr', '( %s -> u e. RR )' % au); uc = t([ur], 'recnd', 'u e. CC')
    gc = t([t([zdu], 'elin1d', '%s e. %s' % (Zu, DG)), w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % Zu)
    gqr = t([t([gc], 'abscld', '%s e. RR' % g), t([t([c_(w, au, w.s([], '1re', '1 e. RR'), '1 e. RR'), t([uc], 'abscld', '( abs ` u ) e. RR')], 'readdcld',
                                                      '( 1 + ( abs ` u ) ) e. RR')], 'resqcld', '%s e. RR' % Q)], 'remulcld', '%s e. RR' % GQ)
    aur = t([uc], 'abscld', '( abs ` u ) e. RR')
    e4r = t([t([c_(w, au, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), t([t([aur, c_(w, au, w.s([], '4re', '4 e. RR'), '4 e. RR'),
                                                                        c_(w, au, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( ( abs ` u ) / 4 ) e. RR')],
                                                                  'renegcld', '-u ( ( abs ` u ) / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E4u)], 'rpred', '%s e. RR' % E4u)
    ccr = c_(w, au, w.s([num.real(w, '( ; 5 0 / ; 4 9 )'), w.s([num.real(w, '; ; ; 1 6 3 2'), num.real(w, '; ; 1 2 8')], 'remulcli',
                                                                                       '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR')], 'remulcli', '%s e. RR' % CC_), '%s e. RR' % CC_)
    cer = t([ccr, e4r], 'remulcld', '( %s x. %s ) e. RR' % (CC_, E4u))
    krt = lift_a(w, au, kr); k0t = lift_a(w, au, st([krp], 'rpge0d', '0 <_ %s' % K0c))
    m1 = t([gqr, cer, krt, k0t, g2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (K0c, GQ, K0c, CC_, E4u))
    FUR = '( abs ` %s )' % FU
    furr = t([t([pb, w.inst('z6absle')], 'syl', '%s e. CC' % FU)], 'abscld', '%s e. RR' % FUR)
    m2 = t([furr, t([krt, gqr], 'remulcld', '( %s x. %s ) e. RR' % (K0c, GQ)), t([krt, cer], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (K0c, CC_, E4u)), pb, m1],
           'letrd', '%s <_ ( %s x. ( %s x. %s ) )' % (FUR, K0c, CC_, E4u))
    MM = '( %s x. %s )' % (K0c, CC_)
    m3 = t([t([krt], 'recnd', '%s e. CC' % K0c), t([ccr], 'recnd', '%s e. CC' % CC_), t([e4r], 'recnd', '%s e. CC' % E4u)], 'mulassd',
           '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (MM, E4u, K0c, CC_, E4u))
    m4 = t([m2, m3], 'breqtrrd', '%s <_ ( %s x. %s )' % (FUR, MM, E4u))
    m5 = t([m4], 'a1d', '( 1 <_ ( abs ` u ) -> %s <_ ( %s x. %s ) )' % (FUR, MM, E4u))
    alm = st([m5], 'ralrimiva', 'A. u e. RR ( 1 <_ ( abs ` u ) -> %s <_ ( %s x. %s ) )' % (FUR, MM, E4u))
    ccc = w.s([num.real(w, '( ; 5 0 / ; 4 9 )'), w.s([num.real(w, '; ; ; 1 6 3 2'), num.real(w, '; ; 1 2 8')], 'remulcli',
              '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR')], 'remulcli', '%s e. RR' % CC_)
    mmr = st([kr, c_(w, a, ccc, '%s e. RR' % CC_)], 'remulcld', '%s e. RR' % MM)
    vc = sub(STATEMENTS['z6vlcvg'], {'C': CL, 'G': G, 'D': DS, 'M': MM, 'Y': '1'})
    van, vco = split_imp(vc)
    h = st([st([clr, st([gcs, ald], 'jca', '( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s )' % (G, DS, Zu, DS))], 'jca',
               '( %s e. RR /\\ ( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s ) )' % (CL, G, DS, Zu, DS)),
            st([st([mmr, c_(w, a, w.s([], '1rp', '1 e. RR+'), '1 e. RR+')], 'jca', '( %s e. RR /\\ 1 e. RR+ )' % MM), alm], 'jca',
               '( ( %s e. RR /\\ 1 e. RR+ ) /\\ A. u e. RR ( 1 <_ ( abs ` u ) -> %s <_ ( %s x. %s ) ) )' % (MM, FUR, MM, E4u))], 'jca', van)
    vl = st([h, w.inst('z6vlcvg')], 'syl', vco)
    lim = st([vl], 'simpld', '%s ~~>r %s' % (VLF(G, CL), VL(G, CL)))
    # the bound
    at = '( %s /\\ t e. RR+ )' % a
    l3 = w.s([w.s([], 'id', '( %s -> %s )' % (at, at)), w.inst('z6ecl3')], 'syl', '( %s -> %s )' % (at, sub(cns('z6ecl3'), {'T': 't'})))
    B = '( %s x. %s )' % (K0c, KGL)
    ral = st([l3], 'ralrimiva', 'A. t e. RR+ ( abs ` %s ) <_ %s' % (LI(G, CL), B))
    cl = Closure(w, a, {})
    kglr = cl.mem(KGL, 'RR')
    br = st([kr, kglr], 'remulcld', '%s e. RR' % B)
    rl = st([st([lim, st([br, ral], 'jca', '( %s e. RR /\\ A. t e. RR+ ( abs ` %s ) <_ %s )' % (B, LI(G, CL), B))], 'jca',
                '( %s ~~>r %s /\\ ( %s e. RR /\\ A. t e. RR+ ( abs ` %s ) <_ %s ) )' % (VLF(G, CL), VL(G, CL), B, LI(G, CL), B)), w.inst('z6rlimle')], 'syl',
            '( abs ` %s ) <_ %s' % (VL(G, CL), B))
    # K0 KGL = ( ( ( X ^ CL KPT ) z2 ) KGL ) R ^ 3
    P = '( ( %s ^c %s ) x. %s )' % (XPD, CL, KPT); R3 = '( R ^ 3 )'
    dr = f['D e. RR']; d1 = f['1 < D']
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    xrp = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    xcr = st([st([xrp, clr], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (XPD, CL))], 'rpred', '( %s ^c %s ) e. RR' % (XPD, CL))
    pcc = st([st([xcr, kptre(w, a, drp)], 'remulcld', '%s e. RR' % P)], 'recnd', '%s e. CC' % P)
    z2c = st([st([st([drp, c_(w, a, num.real(w, '( ; 6 3 / ; ; 1 0 0 )'), '( ; 6 3 / ; ; 1 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % Z2D)], 'rpred', '%s e. RR' % Z2D)],
             'recnd', '%s e. CC' % Z2D)
    r3c = st([st([f['R e. NN']], 'nncnd', 'R e. CC'), c_(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'expcld', '%s e. CC' % R3)
    kgc = st([kglr], 'recnd', '%s e. CC' % KGL)
    q1 = st([pcc, z2c, r3c], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (P, Z2D, R3, P, Z2D, R3))
    q2 = st([q1], 'oveq1d', '( ( ( %s x. %s ) x. %s ) x. %s ) = %s' % (P, Z2D, R3, KGL, B))
    q3 = st([st([pcc, z2c], 'mulcld', '( %s x. %s ) e. CC' % (P, Z2D)), r3c, kgc], 'mul32d',
            '( ( ( %s x. %s ) x. %s ) x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (P, Z2D, R3, KGL, P, Z2D, KGL, R3))
    q4 = st([q2, q3], 'eqtr3d', '%s = ( ( ( %s x. %s ) x. %s ) x. %s )' % (B, P, Z2D, KGL, R3))
    fin = st([rl, q4], 'breqtrd', '( abs ` %s ) <_ ( ( ( %s x. %s ) x. %s ) x. %s )' % (VL(G, CL), P, Z2D, KGL, R3))
    w.qed([lim, fin], 'jca', STATEMENTS['z6ectrl'])
    return w


def lift_a(w, a2, step):
    """( a -> X ) to ( a2 -> X ) where a2 = ( a /\\ ... )"""
    from cl import formula_of
    fo = formula_of(w, step)
    x = split_imp(fo)[1]
    return w.s([step], 'adantr', '( %s -> %s )' % (a2, x))


# ------------------------------------------------------------------ z6ectr and its helpers
def z6ecalg():
    w = W('z6ecalg', 'Helper of z6ect3: ( ( ( A ( ( K B ) L ) ) C ) G ) E = ( ( K L ) G ) ( ( ( A B ) C ) E ).')
    a = ante('z6ecalg'); f = unpack(w, a)
    cmul_eq(w, a, f)
    return w


def cmul_eq(w, a, f):
    """the rearrangement by mulassd / mulcomd / mul32d steps (complex atoms)"""
    st = mkst(w, a)
    c = lambda x: f['%s e. CC' % x]
    KB = '( K x. B )'; KBL = '( %s x. L )' % KB
    kb = st([c('K'), c('B')], 'mulcld', '%s e. CC' % KB)
    # A ( ( K B ) L ) = ( K L ) ( A B )
    e1 = st([c('A'), kb, c('L')], 'mul12d', '( A x. ( %s x. L ) ) = ( %s x. ( A x. L ) )' % (KB, KB))
    e2 = st([c('K'), c('B'), st([c('A'), c('L')], 'mulcld', '( A x. L ) e. CC')], 'mulassd', '( ( K x. B ) x. ( A x. L ) ) = ( K x. ( B x. ( A x. L ) ) )')
    e3 = st([c('B'), c('A'), c('L')], 'mul12d', '( B x. ( A x. L ) ) = ( A x. ( B x. L ) )')
    e4 = st([c('A'), c('B'), c('L')], 'mulassd', '( ( A x. B ) x. L ) = ( A x. ( B x. L ) )')
    e5 = st([st([c('A'), c('B')], 'mulcld', '( A x. B ) e. CC'), c('L')], 'mulcomd', '( ( A x. B ) x. L ) = ( L x. ( A x. B ) )')
    # ( A ( B L ) ) = ( L ( A B ) )
    e6 = st([e4, e5], 'eqtr3d', '( A x. ( B x. L ) ) = ( L x. ( A x. B ) )')
    e7 = st([e3, e6], 'eqtrd', '( B x. ( A x. L ) ) = ( L x. ( A x. B ) )')
    e8 = st([e7], 'oveq2d', '( K x. ( B x. ( A x. L ) ) ) = ( K x. ( L x. ( A x. B ) ) )')
    AB = '( A x. B )'
    e9 = st([c('K'), c('L'), st([c('A'), c('B')], 'mulcld', '%s e. CC' % AB)], 'mulassd', '( ( K x. L ) x. %s ) = ( K x. ( L x. %s ) )' % (AB, AB))
    X1 = st([st([st([e1, e2], 'eqtrd', '( A x. %s ) = ( K x. ( B x. ( A x. L ) ) )' % KBL), e8], 'eqtrd',
                '( A x. %s ) = ( K x. ( L x. %s ) )' % (KBL, AB)), e9], 'eqtr4d', '( A x. %s ) = ( ( K x. L ) x. %s )' % (KBL, AB))
    KL = '( K x. L )'
    kl = st([c('K'), c('L')], 'mulcld', '%s e. CC' % KL); ab = st([c('A'), c('B')], 'mulcld', '%s e. CC' % AB)
    # ( ( KL AB ) C ) G ) E
    y1 = st([X1], 'oveq1d', '( ( A x. %s ) x. C ) = ( ( %s x. %s ) x. C )' % (KBL, KL, AB))
    y2 = st([kl, ab, c('C')], 'mulassd', '( ( %s x. %s ) x. C ) = ( %s x. ( %s x. C ) )' % (KL, AB, KL, AB))
    ABC = '( %s x. C )' % AB
    y3 = st([y1, y2], 'eqtrd', '( ( A x. %s ) x. C ) = ( %s x. %s )' % (KBL, KL, ABC))
    y4 = st([y3], 'oveq1d', '( ( ( A x. %s ) x. C ) x. G ) = ( ( %s x. %s ) x. G )' % (KBL, KL, ABC))
    abc = st([ab, c('C')], 'mulcld', '%s e. CC' % ABC)
    y5 = st([kl, abc, c('G')], 'mul32d', '( ( %s x. %s ) x. G ) = ( ( %s x. G ) x. %s )' % (KL, ABC, KL, ABC))
    y6 = st([y4, y5], 'eqtrd', '( ( ( A x. %s ) x. C ) x. G ) = ( ( %s x. G ) x. %s )' % (KBL, KL, ABC))
    y7 = st([y6], 'oveq1d', '( ( ( ( A x. %s ) x. C ) x. G ) x. E ) = ( ( ( %s x. G ) x. %s ) x. E )' % (KBL, KL, ABC))
    y8 = st([st([kl, c('G')], 'mulcld', '( %s x. G ) e. CC' % KL), abc, c('E')], 'mulassd',
            '( ( ( %s x. G ) x. %s ) x. E ) = ( ( %s x. G ) x. ( %s x. E ) )' % (KL, ABC, KL, ABC))
    w.qed([y7, y8], 'eqtrd', STATEMENTS['z6ecalg'])


def z6ect6():
    w = W('z6ect6', 'Helper of z6ectr: KGL = ( 50/49 ) 1024 1632 / log 2 <_ 2470000 (1 / log 2 <_ 81/56, z5dlog2).')
    a = 'T.'; st = mkst(w, a)
    X = '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 )'; L2 = '( log ` 2 )'; F = '( ; 5 6 / ; 8 1 )'; K = '( ; 5 0 / ; 4 9 )'
    xr = w.s([num.real(w, '; ; ; 1 0 2 4'), num.real(w, '; ; ; 1 6 3 2')], 'remulcli', '%s e. RR' % X)
    x0 = w.s([num.fact(w, '; ; ; 1 0 2 4', 'ge0'), num.fact(w, '; ; ; 1 6 3 2', 'ge0'),
              w.s([num.real(w, '; ; ; 1 0 2 4'), num.real(w, '; ; ; 1 6 3 2')], 'mulge0i', '( ( 0 <_ ; ; ; 1 0 2 4 /\\ 0 <_ ; ; ; 1 6 3 2 ) -> 0 <_ %s )' % X)],
             'mp2an', '0 <_ %s' % X)
    l2rp = w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('rplogcl')], 'mp2an', '%s e. RR+' % L2)
    d1 = st([c_(w, a, num.rp(w, F), '%s e. RR+' % F), c_(w, a, l2rp, '%s e. RR+' % L2), c_(w, a, xr, '%s e. RR' % X), c_(w, a, x0, '0 <_ %s' % X),
             c_(w, a, w.s([], 'z5dlog2', '%s <_ %s' % (F, L2)), '%s <_ %s' % (F, L2))], 'lediv2ad', '( %s / %s ) <_ ( %s / %s )' % (X, L2, X, F))
    d2 = st([st([c_(w, a, xr, '%s e. RR' % X), c_(w, a, l2rp, '%s e. RR+' % L2)], 'rerpdivcld', '( %s / %s ) e. RR' % (X, L2)),
             st([c_(w, a, xr, '%s e. RR' % X), c_(w, a, num.rp(w, F), '%s e. RR+' % F)], 'rerpdivcld', '( %s / %s ) e. RR' % (X, F)),
             c_(w, a, num.real(w, K), '%s e. RR' % K), c_(w, a, num.fact(w, K, 'ge0'), '0 <_ %s' % K), d1], 'lemul2ad',
            '%s <_ ( %s x. ( %s / %s ) )' % (KGL, K, X, F))
    X81 = '( ( %s x. ; 8 1 ) / ; 5 6 )' % X
    dd = w.s([w.s([xr], 'recni', '%s e. CC' % X), w.s([num.cc(w, '; 5 6'), num.fact(w, '; 5 6', 'ne0')], 'pm3.2i', '( ; 5 6 e. CC /\\ ; 5 6 =/= 0 )'),
              w.s([num.cc(w, '; 8 1'), num.fact(w, '; 8 1', 'ne0')], 'pm3.2i', '( ; 8 1 e. CC /\\ ; 8 1 =/= 0 )'), w.inst('divdiv2')], 'mp3an',
             '( %s / %s ) = %s' % (X, F, X81))
    n0 = lin.linarith(w, a, [], '( %s x. %s ) <_ %s' % (K, X81, K247), leaves={}, cert={})
    n = st([c_(w, a, w.s([dd], 'oveq2i', '( %s x. ( %s / %s ) ) = ( %s x. %s )' % (K, X, F, K, X81)), '( %s x. ( %s / %s ) ) = ( %s x. %s )' % (K, X, F, K, X81)), n0],
           'eqbrtrd', '( %s x. ( %s / %s ) ) <_ %s' % (K, X, F, K247))
    kr = st([c_(w, a, num.real(w, K), '%s e. RR' % K), st([c_(w, a, xr, '%s e. RR' % X), c_(w, a, l2rp, '%s e. RR+' % L2)], 'rerpdivcld', '( %s / %s ) e. RR' % (X, L2))],
            'remulcld', '%s e. RR' % KGL)
    kr2 = st([c_(w, a, num.real(w, K), '%s e. RR' % K), st([c_(w, a, xr, '%s e. RR' % X), c_(w, a, num.rp(w, F), '%s e. RR+' % F)], 'rerpdivcld', '( %s / %s ) e. RR' % (X, F))],
             'remulcld', '( %s x. ( %s / %s ) ) e. RR' % (K, X, F))
    fin = st([kr, kr2, c_(w, a, num.real(w, K247), '%s e. RR' % K247), d2, n], 'letrd', '%s <_ %s' % (KGL, K247))
    w.qed([fin], 'mptru', STATEMENTS['z6ect6'])
    return w


def z6ect5():
    w = W('z6ect5', 'Helper of z6ectr: the final arithmetic of (T1), P <_ 600000 2470000 M and 2 10 ^ 14 M <_ 1 give P <_ 1/8.')
    a = ante('z6ect5'); f = unpack(w, a)
    cl = Closure(w, a, {'M': [('RR', f['M e. RR']), ('ge0', f['0 <_ M'])], 'P': ('RR', f['P e. RR'])})
    cl.atom('M'); cl.atom('P')
    from fractions import Fraction as Fr
    h1 = f['( %s x. M ) <_ 1' % N14]; h2 = f['P <_ ( ( %s x. %s ) x. M )' % (_C6, K247)]
    lin.linarith(w, a, [h1, h2], 'P <_ ( 1 / 8 )', closure=cl, name='qed', cert={h1: Fr(600000 * 2470000, 2 * 10 ** 14), h2: 1})
    return w


def z6ect3():
    w = W('z6ect3', 'Helper of z6ectr: the exponent walk X ^ Q KPT z2 KGL R ^ 3 = 600000 C_tau log D KGL D ^ ( ( 6/5 ) Q + 37/32 ) '
                    '(cxpmul, cxpmul2, cxpadd; 397/800 + 63/100 + 3/100 = 37/32).')
    a = ante('z6ect3'); f = unpack(w, a); st = mkst(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']; qr = f['Q e. RR']
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    dc = st([dr], 'recnd', 'D e. CC'); dne = st([drp], 'rpne0d', 'D =/= 0'); qc = st([qr], 'recnd', 'Q e. CC')
    A_ = '( ( 6 / 5 ) x. Q )'; B_ = '( ; ; 3 9 7 / ; ; 8 0 0 )'; C_ = '( ; 6 3 / ; ; 1 0 0 )'; D_ = '( ( 1 / ; ; 1 0 0 ) x. 3 )'
    Dx = lambda e: '( D ^c %s )' % e
    x1 = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR'), qc, w.inst('cxpmul')], 'syl3anc', '%s = ( %s ^c Q )' % (Dx(A_), XPD))
    x2 = st([dc, c_(w, a, num.cc(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. CC'), c_(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0'), w.inst('cxpmul2')],
            'syl3anc', '%s = ( %s ^ 3 )' % (Dx(D_), RPD))
    x1r = st([x1], 'eqcomd', '( %s ^c Q ) = %s' % (XPD, Dx(A_)))
    x2r = st([x2], 'eqcomd', '( %s ^ 3 ) = %s' % (RPD, Dx(D_)))
    rw, new = w.rewrite(PEX('Q'), {'( %s ^c Q )' % XPD: (Dx(A_), x1r), '( %s ^ 3 )' % RPD: (Dx(D_), x2r)}, a)
    # the algebra
    K = '( %s x. CTau )' % _C6; L = '( log ` D )'
    ere = lambda e, r: st([st([drp, r], 'rpcxpcld', '%s e. RR+' % Dx(e))], 'rpcnd', '%s e. CC' % Dx(e))
    ar = st([c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR'), qr], 'remulcld', '%s e. RR' % A_)
    br = c_(w, a, num.real(w, B_), '%s e. RR' % B_); cr = c_(w, a, num.real(w, C_), '%s e. RR' % C_)
    dr_ = st([c_(w, a, num.real(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. RR'), c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'remulcld', '%s e. RR' % D_)
    f[Dx(A_) + ' e. CC'] = ere(A_, ar); f[Dx(B_) + ' e. CC'] = ere(B_, br); f[Dx(C_) + ' e. CC'] = ere(C_, cr); f[Dx(D_) + ' e. CC'] = ere(D_, dr_)
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    ctre = w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
                w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('reexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR')],
               'eqeltri', 'CTau e. RR')
    f['%s e. CC' % K] = st([c_(w, a, num.cc(w, _C6), '%s e. CC' % _C6), c_(w, a, w.s([ctre], 'recni', 'CTau e. CC'), 'CTau e. CC')], 'mulcld', '%s e. CC' % K)
    f['%s e. CC' % L] = st([st([drp], 'relogcld', '%s e. RR' % L)], 'recnd', '%s e. CC' % L)
    f['%s e. CC' % KGL] = st([Closure(w, a, {}).mem(KGL, 'RR')], 'recnd', '%s e. CC' % KGL)
    ag, agc = apply(w, a, 'z6ecalg', {'A': Dx(A_), 'B': Dx(B_), 'C': Dx(C_), 'E': Dx(D_), 'K': K, 'L': L, 'G': KGL}, f)
    # D ^ a D ^ b D ^ c D ^ d = D ^ ( a + b + c + d )
    dcn = st([dc, dne], 'jca', '( D e. CC /\\ D =/= 0 )')
    acc = st([ar], 'recnd', '%s e. CC' % A_); bcc = st([br], 'recnd', '%s e. CC' % B_); ccc_ = st([cr], 'recnd', '%s e. CC' % C_); dcc = st([dr_], 'recnd', '%s e. CC' % D_)
    AB = '( %s + %s )' % (A_, B_); ABC = '( %s + %s )' % (AB, C_); ABCD = '( %s + %s )' % (ABC, D_)
    y3 = st([dcn, acc, bcc, w.inst('cxpadd')], 'syl3anc', '%s = ( %s x. %s )' % (Dx(AB), Dx(A_), Dx(B_)))
    abc_ = st([acc, bcc], 'addcld', '%s e. CC' % AB)
    y2 = st([dcn, abc_, ccc_, w.inst('cxpadd')], 'syl3anc', '%s = ( %s x. %s )' % (Dx(ABC), Dx(AB), Dx(C_)))
    y2b = st([y2, st([y3], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (Dx(AB), Dx(C_), Dx(A_), Dx(B_), Dx(C_)))], 'eqtrd',
             '%s = ( ( %s x. %s ) x. %s )' % (Dx(ABC), Dx(A_), Dx(B_), Dx(C_)))
    y1 = st([dcn, st([abc_, ccc_], 'addcld', '%s e. CC' % ABC), dcc, w.inst('cxpadd')], 'syl3anc', '%s = ( %s x. %s )' % (Dx(ABCD), Dx(ABC), Dx(D_)))
    P4 = '( ( ( %s x. %s ) x. %s ) x. %s )' % (Dx(A_), Dx(B_), Dx(C_), Dx(D_))
    y1b = st([y1, st([y2b], 'oveq1d', '( %s x. %s ) = %s' % (Dx(ABC), Dx(D_), P4))], 'eqtrd', '%s = %s' % (Dx(ABCD), P4))
    cl = Closure(w, a, {'Q': ('RR', qr)}); cl.atom('Q')
    ex = lin.lineq(w, a, ABCD, '( %s + ( ; 3 7 / ; 3 2 ) )' % A_, closure=cl)
    EF = Dx('( %s + ( ; 3 7 / ; 3 2 ) )' % A_)
    y0 = st([st([ex], 'oveq2d', '%s = %s' % (Dx(ABCD), EF)), y1b], 'eqtr3d', '%s = %s' % (EF, P4))
    KLG = '( ( %s x. %s ) x. %s )' % (K, L, KGL)
    z1 = st([rw, ag], 'eqtrd', '%s = ( %s x. %s )' % (PEX('Q'), KLG, P4))
    z2 = st([z1, st([y0], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (KLG, EF, KLG, P4))], 'eqtr4d', '%s = ( %s x. %s )' % (PEX('Q'), KLG, EF))
    w.lines[-1] = 'qed' + w.lines[-1][len(z2):]
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS['z6ect3'], (w.lines[-1], STATEMENTS['z6ect3'])
    return w


def pow10(w, n):
    """closed step ( ; 1 0 ^ n ) = 10^n for n in (1, 2, 3, 6, 7, 14)"""
    nt = num.nat_text
    T = nt(10)
    P = lambda k: '( %s ^ %s )' % (T, nt(k))
    ten = num.nn0(w, 10)
    memo = {}
    memo[1] = w.s([ten], 'numexp1', '%s = %s' % (P(1), T))
    def sq(m, n_):   # n_ = 2 m
        return w.s([ten, num.nn0(w, m), num.mul_nat(w, 2, m), memo[m], num.mul_nat(w, 10 ** m, 10 ** m)], 'numexp2x', '%s = %s' % (P(n_), nt(10 ** n_)))
    def p1(m, n_):   # n_ = m + 1
        e = w.s([memo[m]], 'oveq1i', '( %s x. %s ) = ( %s x. %s )' % (P(m), T, nt(10 ** m), T))
        e2 = w.s([e, num.mul_nat(w, 10 ** m, 10)], 'eqtri', '( %s x. %s ) = %s' % (P(m), T, nt(10 ** n_)))
        return w.s([ten, num.nn0(w, m), num.add_nat(w, m, 1), e2], 'numexpp1', '%s = %s' % (P(n_), nt(10 ** n_)))
    memo[2] = sq(1, 2); memo[3] = p1(2, 3); memo[6] = sq(3, 6); memo[7] = p1(6, 7); memo[14] = sq(7, 14)
    return memo[n]


def leq_c(w, a, lhs, rhs, cl):
    """( a -> lhs = rhs ) for a polynomial identity (two linarith calls with the empty certificate)"""
    x = lin.linarith(w, a, [], '%s <_ %s' % (lhs, rhs), closure=cl, products=True, cert={})
    y = lin.linarith(w, a, [], '%s <_ %s' % (rhs, lhs), closure=cl, products=True, cert={})
    both = '( %s <_ %s /\\ %s <_ %s )' % (lhs, rhs, rhs, lhs)
    j = w.s([x, y], 'jca', '( %s -> %s )' % (a, both))
    bi = w.s([cl.mem(lhs, 'RR'), cl.mem(rhs, 'RR')], 'letri3d', '( %s -> ( %s = %s <-> %s ) )' % (a, lhs, rhs, both))
    return w.s([j, bi], 'mpbird', '( %s -> %s = %s )' % (a, lhs, rhs))


def ctau_rp(w):
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    return w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
                w.s([w.s([], '2rp', '2 e. RR+'), w.s([knn], 'nnzi', '( 2 ^ ; ; 8 0 0 ) e. ZZ'), w.inst('rpexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR+')],
               'eqeltri', 'CTau e. RR+')


def kgl_rp(w, a):
    """( a -> KGL e. RR+ )"""
    st = mkst(w, a)
    X = '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 )'
    l2rp = w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('rplogcl')], 'mp2an', '( log ` 2 ) e. RR+')
    xrp = st([c_(w, a, num.rp(w, '; ; ; 1 0 2 4'), '; ; ; 1 0 2 4 e. RR+'), c_(w, a, num.rp(w, '; ; ; 1 6 3 2'), '; ; ; 1 6 3 2 e. RR+')], 'rpmulcld', '%s e. RR+' % X)
    return st([c_(w, a, num.rp(w, '( ; 5 0 / ; 4 9 )'), '( ; 5 0 / ; 4 9 ) e. RR+'),
               st([xrp, c_(w, a, l2rp, '( log ` 2 ) e. RR+')], 'rpdivcld', '( %s / ( log ` 2 ) ) e. RR+' % X)], 'rpmulcld', '%s e. RR+' % KGL)


def z6ect4():
    w = W('z6ect4', 'Helper of z6ectr: (T1) and Q <_ -98/100 give 600000 C_tau log D KGL D ^ ( ( 6/5 ) Q + 37/32 ) <_ 1/8 '
                    '(( 6/5 ) Q + 37/32 <_ -79/4000, KGL <_ 2470000, 8 600000 2470000 < 2 10 ^ 14).')
    a = ante('z6ect4'); f = unpack(w, a); st = mkst(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']; qr = f['Q e. RR']
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    dc = st([dr], 'recnd', 'D e. CC'); dne = st([drp], 'rpne0d', 'D =/= 0')
    L = '( log ` D )'
    lr = st([drp], 'relogcld', '%s e. RR' % L)
    lrp = st([dr, d1, w.inst('rplogcl')], 'syl2anc', '%s e. RR+' % L)
    q49 = st([f['Q <_ %s' % N98], r98(w, a)], 'breqtrd', 'Q <_ -u ( ; 4 9 / ; 5 0 )')
    e = '( ( ( 6 / 5 ) x. Q ) + ( ; 3 7 / ; 3 2 ) )'; m79 = '-u ( ; 7 9 / ; ; ; 4 0 0 0 )'; p79 = '( ; 7 9 / ; ; ; 4 0 0 0 )'
    cl = Closure(w, a, {'Q': ('RR', qr)}); cl.atom('Q')
    er = cl.mem(e, 'RR')
    ele = lin.linarith(w, a, [q49], '%s <_ %s' % (e, m79), closure=cl)
    m79r = c_(w, a, num.real(w, m79), '%s e. RR' % m79)
    E = '( D ^c %s )' % e; Yn = '( D ^c %s )' % m79; Y = '( D ^c %s )' % p79
    cx = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), st([er, m79r], 'jca', '( %s e. RR /\\ %s e. RR )' % (e, m79)), w.inst('cxple')], 'syl2anc',
            '( %s <_ %s <-> %s <_ %s )' % (e, m79, E, Yn))
    eyn = st([ele, cx], 'mpbid', '%s <_ %s' % (E, Yn))
    yrp = st([drp, c_(w, a, num.real(w, p79), '%s e. RR' % p79)], 'rpcxpcld', '%s e. RR+' % Y)
    ynrp = st([drp, m79r], 'rpcxpcld', '%s e. RR+' % Yn)
    erp = st([drp, er], 'rpcxpcld', '%s e. RR+' % E)
    cn = st([dc, dne, c_(w, a, num.cc(w, p79), '%s e. CC' % p79), w.inst('cxpneg')], 'syl3anc', '%s = ( 1 / %s )' % (Yn, Y))
    yy0 = st([st([yrp], 'rpcnd', '%s e. CC' % Y), st([yrp], 'rpne0d', '%s =/= 0' % Y)], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (Y, Y))
    yy = st([st([cn], 'oveq2d', '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (Y, Yn, Y, Y)), yy0], 'eqtrd', '( %s x. %s ) = 1' % (Y, Yn))
    # (T1) with 2 10 ^ 14 as a numeral
    T14 = '( 2 x. ( ; 1 0 ^ ; 1 4 ) )'
    n14 = w.s([w.s([pow10(w, 14)], 'oveq2i', '%s = ( 2 x. %s )' % (T14, num.nat_text(10 ** 14))), num.mul_nat(w, 2, 10 ** 14)], 'eqtri', '%s = %s' % (T14, N14))
    t1a = st([st([c_(w, a, n14, '%s = %s' % (T14, N14))], 'oveq1d', '( %s x. CTau ) = ( %s x. CTau )' % (T14, N14))], 'oveq1d',
             '( ( %s x. CTau ) x. %s ) = ( ( %s x. CTau ) x. %s )' % (T14, L, N14, L))
    T1n = '( ( %s x. CTau ) x. %s ) <_ %s' % (N14, L, Y)
    t1n = st([t1a, f[T1]], 'eqbrtrrd', T1n)
    ct = c_(w, a, ctau_rp(w), 'CTau e. RR+')
    cl2 = Closure(w, a, {'CTau': ('RR+', ct), L: ('RR+', lrp), Yn: ('RR+', ynrp), Y: ('RR+', yrp), KGL: ('RR+', kgl_rp(w, a)), E: ('RR+', erp)})
    for x in ('CTau', L, Yn, Y, KGL, E):
        cl2.atom(x)
    A4 = '( ( %s x. CTau ) x. %s )' % (N14, L)
    a4 = st([cl2.mem(A4, 'RR'), cl2.mem(Y, 'RR'), cl2.mem(Yn, 'RR'), cl2.ge0(Yn), t1n], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (A4, Yn, Y, Yn))
    M = '( ( CTau x. %s ) x. %s )' % (L, Yn)
    from fractions import Fraction as Fr
    nm = lin.linarith(w, a, [a4, yy], '( %s x. %s ) <_ 1' % (N14, M), closure=cl2, products=True, cert={a4: 1, yy: 1})
    # KGL E <_ 2470000 Yn
    kg = c_(w, a, w.s([], 'z6ect6', STATEMENTS['z6ect6']), STATEMENTS['z6ect6'])
    ke = st([cl2.mem(KGL, 'RR'), cl2.mem(K247, 'RR'), cl2.mem(E, 'RR'), cl2.mem(Yn, 'RR'), cl2.ge0(KGL), cl2.ge0(E), kg, eyn], 'lemul12ad',
            '( %s x. %s ) <_ ( %s x. %s )' % (KGL, E, K247, Yn))
    P0 = '( ( %s x. CTau ) x. %s )' % (_C6, L)
    p1 = st([cl2.mem(P0, 'CC'), cl2.mem(KGL, 'CC'), cl2.mem(E, 'CC')], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (P0, KGL, E, P0, KGL, E))
    p2 = st([cl2.mem('( %s x. %s )' % (KGL, E), 'RR'), cl2.mem('( %s x. %s )' % (K247, Yn), 'RR'), cl2.mem(P0, 'RR'), cl2.ge0(P0), ke], 'lemul2ad',
            '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (P0, KGL, E, P0, K247, Yn))
    p3 = leq_c(w, a, '( %s x. ( %s x. %s ) )' % (P0, K247, Yn), '( ( %s x. %s ) x. %s )' % (_C6, K247, M), cl2)
    RX = R3X('Q')
    assert RX == '( ( %s x. %s ) x. %s )' % (P0, KGL, E)
    pb = st([st([p1, p2], 'eqbrtrd', '%s <_ ( %s x. ( %s x. %s ) )' % (RX, P0, K247, Yn)), p3], 'breqtrd', '%s <_ ( ( %s x. %s ) x. %s )' % (RX, _C6, K247, M))
    f['%s e. RR' % M] = cl2.mem(M, 'RR'); f['0 <_ %s' % M] = cl2.ge0(M); f['( %s x. %s ) <_ 1' % (N14, M)] = nm
    f['%s e. RR' % RX] = cl2.mem(RX, 'RR'); f['%s <_ ( ( %s x. %s ) x. %s )' % (RX, _C6, K247, M)] = pb
    s5, c5 = apply(w, a, 'z6ect5', {'M': M, 'P': RX}, f)
    w.lines[-1] = 'qed' + w.lines[-1][len(s5):]
    return w


def kpt_rp(w, a, drp, dr, d1):
    st = mkst(w, a)
    C6 = _C6; D397 = '( D ^c ( ; ; 3 9 7 / ; ; 8 0 0 ) )'
    k1 = st([c_(w, a, num.rp(w, C6), '%s e. RR+' % C6), c_(w, a, ctau_rp(w), 'CTau e. RR+')], 'rpmulcld', '( %s x. CTau ) e. RR+' % C6)
    k2 = st([k1, st([drp, c_(w, a, num.real(w, '( ; ; 3 9 7 / ; ; 8 0 0 )'), '( ; ; 3 9 7 / ; ; 8 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % D397)],
            'rpmulcld', '( ( %s x. CTau ) x. %s ) e. RR+' % (C6, D397))
    return st([k2, st([dr, d1, w.inst('rplogcl')], 'syl2anc', '( log ` D ) e. RR+')], 'rpmulcld', '%s e. RR+' % KPT)


def z6ect1():
    w = W('z6ect1', 'Helper of z6ectr: | ECTR | <_ X ^ CL KPT z2 KGL R ^ 3 (| 1 / 2 pi i | <_ 1, fsumabs, z6ectrl for each r e. RSet, z6cube).')
    a = ante('z6ect1'); f = unpack(w, a); st = mkst(w, a)
    dr = f['D e. RR']; d1 = f['1 < D']; nn = f['N e. NN']; sc = f['S e. CC']
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    R1 = '( 1 / ; ; 1 0 0 )'
    rprp = st([drp, c_(w, a, num.real(w, R1), '%s e. RR' % R1)], 'rpcxpcld', '%s e. RR+' % RPD)
    RS = '( N RSet %s )' % RPD
    hv = st([nn, rprp], 'jca', '( N e. NN /\\ %s e. RR+ )' % RPD)
    fin = st([st([hv, w.inst('z5rsetfi')], 'syl', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simprd', '%s e. Fin' % RS)
    # the constant
    clr = st([c_(w, a, num.real(w, R1), '%s e. RR' % R1), st([sc, w.inst('recl')], 'syl', '( Re ` S ) e. RR')], 'resubcld', '%s e. RR' % CL)
    xrp = st([drp, c_(w, a, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    Kc = '( ( ( ( %s ^c %s ) x. %s ) x. %s ) x. %s )' % (XPD, CL, KPT, Z2D, KGL)
    z2 = st([drp, c_(w, a, num.real(w, '( ; 6 3 / ; ; 1 0 0 )'), '( ; 6 3 / ; ; 1 0 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % Z2D)
    kcp = st([st([st([st([xrp, clr], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (XPD, CL)), kpt_rp(w, a, drp, dr, d1)], 'rpmulcld', '( ( %s ^c %s ) x. %s ) e. RR+' % (XPD, CL, KPT)),
                  z2], 'rpmulcld', '( ( ( %s ^c %s ) x. %s ) x. %s ) e. RR+' % (XPD, CL, KPT, Z2D)), kgl_rp(w, a)], 'rpmulcld', '%s e. RR+' % Kc)
    kcr = st([kcp], 'rpred', '%s e. RR' % Kc); kcc = st([kcp], 'rpcnd', '%s e. CC' % Kc); kc0 = st([kcp], 'rpge0d', '0 <_ %s' % Kc)
    # per r
    ar = '( %s /\\ r e. %s )' % (a, RS); sr = mkst(w, ar)
    el = sr([sr([w.s([hv], 'adantr', '( %s -> ( N e. NN /\\ %s e. RR+ ) )' % (ar, RPD)), w.inst('z5elrset')], 'syl',
               '( r e. %s <-> ( r e. ( 1 ... ( |_ ` %s ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) ) )' % (RS, RPD)),
             w.s([], 'simpr', '( %s -> r e. %s )' % (ar, RS))][::-1], 'mpbid',
            '( r e. ( 1 ... ( |_ ` %s ) ) /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 ) )' % RPD)
    rn = sr([sr([el], 'simpld', 'r e. ( 1 ... ( |_ ` %s ) )' % RPD), w.inst('elfznn')], 'syl', 'r e. NN')
    mu = sr([sr([el], 'simprd', '( ( mmu ` r ) =/= 0 /\\ ( r gcd N ) = 1 )')], 'simpld', '( mmu ` r ) =/= 0')
    ec = sr([sr([w.s([], 'simpl', '( %s -> %s )' % (ar, a)), sr([rn, mu], 'jca', '( r e. NN /\\ ( mmu ` r ) =/= 0 )')], 'jca',
                '( %s /\\ ( r e. NN /\\ ( mmu ` r ) =/= 0 ) )' % a), w.inst('z6ectrl')], 'syl', sub(cns('z6ectrl'), {'R': 'r'}))
    V = VL(GR('r'), CL); R3 = '( r ^ 3 )'
    vb = sr([ec], 'simprd', '( abs ` %s ) <_ %s' % (V, sub(cns('z6ectrl'), {'R': 'r'}).split(' <_ ', 1)[1][:-2]))
    assert formula_rhs(w, vb) == '( %s x. %s )' % (Kc, R3), formula_rhs(w, vb)
    vc = sr([vb, w.inst('z6absle')], 'syl', '%s e. CC' % V)
    IR = '( 1 / r )'
    irr = sr([rn], 'nnrecred', '%s e. RR' % IR)
    ir0 = sr([sr([sr([rn], 'nnrpd', 'r e. RR+')], 'rpreccld', '%s e. RR+' % IR)], 'rpge0d', '0 <_ %s' % IR)
    irc = sr([irr], 'recnd', '%s e. CC' % IR)
    TR = '( %s x. %s )' % (IR, V)
    trc = sr([irc, vc], 'mulcld', '%s e. CC' % TR)
    a1 = sr([irc, vc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TR, IR, V))
    a2 = sr([irr, ir0, w.inst('absid')], 'syl2anc', '( abs ` %s ) = %s' % (IR, IR))
    a3 = sr([a1, sr([a2], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (IR, V, IR, V))], 'eqtrd',
            '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (TR, IR, V))
    kcrr = w.s([kcr], 'adantr', '( %s -> %s e. RR )' % (ar, Kc))
    r3r = sr([sr([rn], 'nnred', 'r e. RR'), c_(w, ar, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '%s e. RR' % R3)
    kr3 = sr([kcrr, r3r], 'remulcld', '( %s x. %s ) e. RR' % (Kc, R3))
    b1 = sr([sr([vc], 'abscld', '( abs ` %s ) e. RR' % V), kr3, irr, ir0, vb], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. ( %s x. %s ) )' % (IR, V, IR, Kc, R3))
    IRR = '( %s x. %s )' % (IR, R3)
    b2 = sr([irc, sr([kcrr], 'recnd', '%s e. CC' % Kc), sr([r3r], 'recnd', '%s e. CC' % R3)], 'mul12d',
            '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (IR, Kc, R3, Kc, IRR))
    bnd = sr([sr([a3, b1], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( %s x. %s ) )' % (TR, IR, Kc, R3)), b2], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (TR, Kc, IRR))
    irrr = sr([irr, r3r], 'remulcld', '%s e. RR' % IRR)
    # the sums
    SUM = 'sum_ r e. %s %s' % (RS, TR)
    fa = w.s([fin, trc], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ r e. %s ( abs ` %s ) )' % (a, SUM, RS, TR))
    fl = w.s([fin, sr([trc], 'abscld', '( abs ` %s ) e. RR' % TR), sr([kcrr, irrr], 'remulcld', '( %s x. %s ) e. RR' % (Kc, IRR)), bnd], 'fsumle',
             '( %s -> sum_ r e. %s ( abs ` %s ) <_ sum_ r e. %s ( %s x. %s ) )' % (a, RS, TR, RS, Kc, IRR))
    fm = w.s([fin, kcc, sr([irrr], 'recnd', '%s e. CC' % IRR)], 'fsummulc2', '( %s -> ( %s x. sum_ r e. %s %s ) = sum_ r e. %s ( %s x. %s ) )' % (a, Kc, RS, IRR, RS, Kc, IRR))
    one = c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')
    rp1a = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), c_(w, a, num.real(w, R1), '%s e. RR' % R1)], 'jca',
                                                                  '( 0 e. RR /\\ %s e. RR )' % R1), w.inst('cxple')], 'syl2anc', '( 0 <_ %s <-> ( D ^c 0 ) <_ %s )' % (R1, RPD))
    rp1b = st([c_(w, a, num.fact(w, R1, 'ge0'), '0 <_ %s' % R1), rp1a], 'mpbid', '( D ^c 0 ) <_ %s' % RPD)
    rp1 = st([st([st([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1'), rp1b], 'eqbrtrrd', '1 <_ %s' % RPD)
    SC = 'sum_ r e. %s %s' % (RS, IRR)
    cube = st([st([nn, st([st([rprp], 'rpred', '%s e. RR' % RPD), rp1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (RPD, RPD))], 'jca',
                  '( N e. NN /\\ ( %s e. RR /\\ 1 <_ %s ) )' % (RPD, RPD)), w.inst('z6cube')], 'syl', '%s <_ ( %s ^ 3 )' % (SC, RPD))
    scr = w.s([fin, irrr], 'fsumrecl', '( %s -> %s e. RR )' % (a, SC))
    rp3 = st([st([rprp], 'rpred', '%s e. RR' % RPD), c_(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '( %s ^ 3 ) e. RR' % RPD)
    kb = st([scr, rp3, kcr, kc0, cube], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s ^ 3 ) )' % (Kc, SC, Kc, RPD))
    assert PEX(CL) == '( %s x. ( %s ^ 3 ) )' % (Kc, RPD)
    sumc = w.s([fin, trc], 'fsumcl', '( %s -> %s e. CC )' % (a, SUM))
    asr = st([sumc], 'abscld', '( abs ` %s ) e. RR' % SUM)
    s1r = w.s([fin, sr([trc], 'abscld', '( abs ` %s ) e. RR' % TR)], 'fsumrecl', '( %s -> sum_ r e. %s ( abs ` %s ) e. RR )' % (a, RS, TR))
    s2r = w.s([fin, sr([kcrr, irrr], 'remulcld', '( %s x. %s ) e. RR' % (Kc, IRR))], 'fsumrecl', '( %s -> sum_ r e. %s ( %s x. %s ) e. RR )' % (a, RS, Kc, IRR))
    c1 = st([asr, s1r, s2r, fa, fl], 'letrd', '( abs ` %s ) <_ sum_ r e. %s ( %s x. %s )' % (SUM, RS, Kc, IRR))
    c2 = st([c1, fm], 'breqtrrd', '( abs ` %s ) <_ ( %s x. %s )' % (SUM, Kc, SC))
    c3 = st([asr, st([kcr, scr], 'remulcld', '( %s x. %s ) e. RR' % (Kc, SC)), st([kcr, rp3], 'remulcld', '%s e. RR' % PEX(CL)), c2, kb], 'letrd',
            '( abs ` %s ) <_ %s' % (SUM, PEX(CL)))
    # | 1 / 2 pi i | <_ 1
    TP = TPI
    tpc = w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TP)
    tpn = w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'),
               w.s([], '2ne0', '2 =/= 0'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')],
                                             'mulne0i', '( _i x. _pi ) =/= 0')], 'mulne0i', '%s =/= 0' % TP)
    IT = '( 1 / %s )' % TP
    ad = w.s([w.s([], 'ax-1cn', '1 e. CC'), tpc, tpn, w.inst('absdiv')], 'mp3an', '( abs ` %s ) = ( ( abs ` 1 ) / ( abs ` %s ) )' % (IT, TP))
    ad2 = w.s([ad, w.s([w.s([], 'abs1', '( abs ` 1 ) = 1'), w.s([], 'abstpi', '( abs ` %s ) = ( 2 x. _pi )' % TP)], 'oveq12i',
                       '( ( abs ` 1 ) / ( abs ` %s ) ) = ( 1 / ( 2 x. _pi ) )' % TP)], 'eqtri', '( abs ` %s ) = ( 1 / ( 2 x. _pi ) )' % IT)
    cl = Closure(w, a, {'_pi': ('RR+', c_(w, a, w.s([], 'pirp', '_pi e. RR+'), '_pi e. RR+'))}); cl.atom('_pi')
    p3 = c_(w, a, w.s([], 'pige3', '3 <_ _pi'), '3 <_ _pi')
    tp1 = lin.linarith(w, a, [p3], '1 <_ ( 2 x. _pi )', closure=cl)
    lr = st([st([st([one, c_(w, a, w.s([], '0lt1', '0 < 1'), '0 < 1')], 'jca', '( 1 e. RR /\\ 0 < 1 )'),
                 st([cl.mem('( 2 x. _pi )', 'RR'), cl.gt0('( 2 x. _pi )')], 'jca', '( ( 2 x. _pi ) e. RR /\\ 0 < ( 2 x. _pi ) )')], 'jca',
                '( ( 1 e. RR /\\ 0 < 1 ) /\\ ( ( 2 x. _pi ) e. RR /\\ 0 < ( 2 x. _pi ) ) )'), w.inst('lerec')], 'syl',
            '( 1 <_ ( 2 x. _pi ) <-> ( 1 / ( 2 x. _pi ) ) <_ ( 1 / 1 ) )')
    ile = st([st([tp1, lr], 'mpbid', '( 1 / ( 2 x. _pi ) ) <_ ( 1 / 1 )'), c_(w, a, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')], 'breqtrd', '( 1 / ( 2 x. _pi ) ) <_ 1')
    itl = st([c_(w, a, ad2, '( abs ` %s ) = ( 1 / ( 2 x. _pi ) )' % IT), ile], 'eqbrtrd', '( abs ` %s ) <_ 1' % IT)
    itc = c_(w, a, w.s([w.s([], 'ax-1cn', '1 e. CC'), tpc, tpn], 'divcli', '%s e. CC' % IT), '%s e. CC' % IT)
    e1 = st([itc, sumc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (ECTR, IT, SUM))
    assert ECTR == '( %s x. %s )' % (IT, SUM)
    e2 = st([st([itc], 'abscld', '( abs ` %s ) e. RR' % IT), one, asr, st([sumc], 'absge0d', '0 <_ ( abs ` %s )' % SUM), itl], 'lemul1ad',
            '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( 1 x. ( abs ` %s ) )' % (IT, SUM, SUM))
    e3 = st([st([asr], 'recnd', '( abs ` %s ) e. CC' % SUM)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (SUM, SUM))
    e4 = st([st([e1, e2], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. ( abs ` %s ) )' % (ECTR, SUM)), e3], 'breqtrd', '( abs ` %s ) <_ ( abs ` %s )' % (ECTR, SUM))
    w.qed([st([st([itc, sumc], 'mulcld', '%s e. CC' % ECTR)], 'abscld', '( abs ` %s ) e. RR' % ECTR), asr,
           st([kcr, rp3], 'remulcld', '%s e. RR' % PEX(CL)), e4, c3], 'letrd', STATEMENTS['z6ect1'])
    return w


def formula_rhs(w, step):
    from cl import formula_of
    return split_imp(formula_of(w, step))[1].split(' <_ ', 1)[1]


def z6ectr():
    w = W('z6ectr', 'Lean norm_Ectr_le (blueprint Lemma 4.2): under (T1), | E_ctr | <_ P1 / 8.  | E_ctr | <_ X ^ CL KPT z2 KGL R ^ 3 (z6ect1) '
                    '= 600000 C_tau log D KGL D ^ ( ( 6/5 ) CL + 37/32 ) (z6ect3) <_ 1/8 (z6ect4, CL <_ -98/100 by z6ecl0) <_ P1 / 8 (z6p1ge1).')
    a = ante('z6ectr'); f = unpack(w, a); st = mkst(w, a)
    s0, c0 = apply(w, a, 'z6ecl0', {}, f); conjs(w, a, s0, c0, f)
    e1, _ = apply(w, a, 'z6ect1', {}, f)
    f['Q e. RR'] = f['%s e. RR' % CL]
    e3, _ = apply(w, a, 'z6ect3', {'Q': CL}, f)
    e4, _ = apply(w, a, 'z6ect4', {'Q': CL}, f)
    dr = f['D e. RR']; d1 = f['1 < D']
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    R1 = '( 1 / ; ; 1 0 0 )'
    rp1a = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), c_(w, a, num.real(w, R1), '%s e. RR' % R1)], 'jca',
                                                                  '( 0 e. RR /\\ %s e. RR )' % R1), w.inst('cxple')], 'syl2anc', '( 0 <_ %s <-> ( D ^c 0 ) <_ %s )' % (R1, RPD))
    rp1b = st([c_(w, a, num.fact(w, R1, 'ge0'), '0 <_ %s' % R1), rp1a], 'mpbid', '( D ^c 0 ) <_ %s' % RPD)
    f['1 <_ %s' % RPD] = st([st([st([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1'), rp1b], 'eqbrtrrd', '1 <_ %s' % RPD)
    f['%s e. RR' % RPD] = st([st([drp, c_(w, a, num.real(w, R1), '%s e. RR' % R1)], 'rpcxpcld', '%s e. RR+' % RPD)], 'rpred', '%s e. RR' % RPD)
    p1, _ = apply(w, a, 'z6p1ge1', {'R': RPD}, f)
    cl = Closure(w, a, {'D': ('RR+', drp), 'CTau': ('RR+', c_(w, a, ctau_rp(w), 'CTau e. RR+')), CL: ('RR', f['%s e. RR' % CL])})
    cl.atom(CL); cl.atom('CTau')
    RS = '( N RSet %s )' % RPD
    rprp = st([drp, c_(w, a, num.real(w, R1), '%s e. RR' % R1)], 'rpcxpcld', '%s e. RR+' % RPD)
    hv = st([f['N e. NN'], rprp], 'jca', '( N e. NN /\\ %s e. RR+ )' % RPD)
    fs = st([hv, w.inst('z5rsetfi')], 'syl', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))
    fin = st([fs], 'simprd', '%s e. Fin' % RS)
    ar = '( %s /\\ r e. %s )' % (a, RS)
    rin = w.s([w.s([fs], 'simpld', '( %s -> %s C_ ( 1 ... ( |_ ` %s ) ) )' % (a, RS, RPD))], 'adantr', '( %s -> %s C_ ( 1 ... ( |_ ` %s ) ) )' % (ar, RS, RPD))
    rn = w.s([w.s([rin, w.s([], 'simpr', '( %s -> r e. %s )' % (ar, RS))], 'sseldd', '( %s -> r e. ( 1 ... ( |_ ` %s ) ) )' % (ar, RPD)), w.inst('elfznn')], 'syl',
             '( %s -> r e. NN )' % ar)
    p1rr = w.s([fin, w.s([rn], 'nnrecred', '( %s -> ( 1 / r ) e. RR )' % ar)], 'fsumrecl', '( %s -> %s e. RR )' % (a, P1D))
    cl.leaf(P1D, 'RR', p1rr); cl.atom(P1D)
    q = lin.linarith(w, a, [p1], '( 1 / 8 ) <_ ( %s / 8 )' % P1D, closure=cl)
    RX = R3X(CL)
    t1 = st([e1, e3], 'breqtrd', '( abs ` %s ) <_ %s' % (ECTR, RX))
    ae = st([st([e1, w.inst('z6absle')], 'syl', '%s e. CC' % ECTR)], 'abscld', '( abs ` %s ) e. RR' % ECTR)
    kg = kgl_rp(w, a); cl.leaf(KGL, 'RR+', kg); cl.atom(KGL)
    h8 = c_(w, a, num.real(w, '( 1 / 8 )'), '( 1 / 8 ) e. RR')
    t2 = st([ae, cl.mem(RX, 'RR'), h8, t1, e4], 'letrd', '( abs ` %s ) <_ ( 1 / 8 )' % ECTR)
    w.qed([ae, h8, cl.mem('( %s / 8 )' % P1D, 'RR'), t2, q], 'letrd', STATEMENTS['z6ectr'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        run(w)
