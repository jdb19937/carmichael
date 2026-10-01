"""Sortie Z6b, section 5: the strip hypotheses of z6shift for GR(R) and the shift z6shiftr.
z6gmaj   the product of the four factor bounds (real algebra)
z6grsd   STRIPD for DS, A = CL, B = 3, Y = | Im S | + 1
z6grmaj  STRIPM with M5
z6shiftr the contour shift Re w = 3 -> Re w = CL (Lean Ghat_line_shift, Ghat_line_shift_principal)
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_s.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import mpval
from z6b_k import hpzpt
from z6b_r import dfacts, mrcc
from z6b_m import inst_all, omgfacts
import lin
from lin import linarith
import num

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def one(w, a):
    return c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')


def z6gmaj():
    w = W('z6gmaj', 'The four factor bounds of the contour integrand multiply to the majorant (real algebra; ~ lemul12ad ).')
    a = ante('z6gmaj'); f = unpack(w, a); st = mkst(w, a)
    g = {k: f['%s e. RR' % k] for k in 'GXVMAKBZEQF'}
    L = {k: g[k] for k in g}
    ge = {k: f['0 <_ %s' % k] for k in 'GXVMAB'}
    ae = st([g['A'], g['E']], 'remulcld', '( A x. E ) e. RR'); bq = st([g['B'], g['Q']], 'remulcld', '( B x. Q ) e. RR')
    p1 = st([g['G'], ae, g['X'], g['K'], ge['G'], ge['X'], f['G <_ ( A x. E )'], f['X <_ K']], 'lemul12ad', '( G x. X ) <_ ( ( A x. E ) x. K )')
    p2 = st([g['V'], bq, g['M'], g['Z'], ge['V'], ge['M'], f['V <_ ( B x. Q )'], f['M <_ Z']], 'lemul12ad', '( V x. M ) <_ ( ( B x. Q ) x. Z )')
    gx = st([g['G'], g['X']], 'remulcld', '( G x. X ) e. RR'); vm = st([g['V'], g['M']], 'remulcld', '( V x. M ) e. RR')
    aek = st([ae, g['K']], 'remulcld', '( ( A x. E ) x. K ) e. RR'); bqz = st([bq, g['Z']], 'remulcld', '( ( B x. Q ) x. Z ) e. RR')
    p3 = st([gx, aek, vm, bqz, st([g['G'], g['X'], ge['G'], ge['X']], 'mulge0d', '0 <_ ( G x. X )'), st([g['V'], g['M'], ge['V'], ge['M']], 'mulge0d', '0 <_ ( V x. M )'), p1, p2],
            'lemul12ad', '( ( G x. X ) x. ( V x. M ) ) <_ ( ( ( A x. E ) x. K ) x. ( ( B x. Q ) x. Z ) )')
    k0 = st([g['X'], g['K'], ge['X'], f['X <_ K']], 'letrd' if False else 'x', 'x') if False else None
    k0 = linarith(w, a, [ge['X'], f['X <_ K']], '0 <_ K', leaves=L)
    z0 = linarith(w, a, [ge['M'], f['M <_ Z']], '0 <_ Z', leaves=L)
    P = '( ( A x. K ) x. ( B x. Z ) )'
    ak = st([g['A'], g['K']], 'remulcld', '( A x. K ) e. RR'); bz = st([g['B'], g['Z']], 'remulcld', '( B x. Z ) e. RR')
    pr = st([ak, bz], 'remulcld', '%s e. RR' % P)
    p0 = st([ak, bz, st([g['A'], g['K'], ge['A'], k0], 'mulge0d', '0 <_ ( A x. K )'), st([g['B'], g['Z'], ge['B'], z0], 'mulge0d', '0 <_ ( B x. Z )')], 'mulge0d', '0 <_ %s' % P)
    qe = st([g['Q'], g['E']], 'remulcld', '( Q x. E ) e. RR')
    f128 = st([c_(w, a, num.real(w, '; ; 1 2 8'), '; ; 1 2 8 e. RR'), g['F']], 'remulcld', '( ; ; 1 2 8 x. F ) e. RR')
    p4 = st([qe, f128, pr, p0, f['( Q x. E ) <_ ( ; ; 1 2 8 x. F )']], 'lemul2ad', '( %s x. ( Q x. E ) ) <_ ( %s x. ( ; ; 1 2 8 x. F ) )' % (P, P))
    old = lin.MAXDEG
    lin.MAXDEG = 6
    e1 = lin.lineq(w, a, '( ( ( A x. E ) x. K ) x. ( ( B x. Q ) x. Z ) )', '( %s x. ( Q x. E ) )' % P, leaves=L, products=True)
    e2 = lin.lineq(w, a, '( %s x. ( ; ; 1 2 8 x. F ) )' % P, '( ( ( ( A x. ; ; 1 2 8 ) x. K ) x. ( B x. Z ) ) x. F )', leaves=L, products=True)
    lin.MAXDEG = old
    s1 = st([p3, e1], 'breqtrd', '( ( G x. X ) x. ( V x. M ) ) <_ ( %s x. ( Q x. E ) )' % P)
    s2 = st([s1, p4], 'letrd' if False else 'x', 'x') if False else None
    lhs = st([gx, vm], 'remulcld', '( ( G x. X ) x. ( V x. M ) ) e. RR')
    s2 = st([lhs, st([pr, qe], 'remulcld', '( %s x. ( Q x. E ) ) e. RR' % P), st([pr, f128], 'remulcld', '( %s x. ( ; ; 1 2 8 x. F ) ) e. RR' % P), s1, p4], 'letrd',
            '( ( G x. X ) x. ( V x. M ) ) <_ ( %s x. ( ; ; 1 2 8 x. F ) )' % P)
    w.qed([s2, e2], 'breqtrd', STATEMENTS['z6gmaj'])
    return w


def notpt(w, c, V, reeq, rv, imeq, iv, rs, ais, zc):
    """( c -> z =/= V ) where c carries ( ( CL <_ Re z /\\ Re z <_ 3 ) /\\ D ) as its last conjunct,
    reeq: ( c -> ( Re ` V ) = rv ), imeq: ( c -> ( abs ` ( Im ` V ) ) = iv ), with CL < rv < 3 and iv < Y5 derivable by lin"""
    D = '( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 ) \\/ %s <_ ( abs ` ( Im ` z ) ) )' % (CL, Y5)
    c2 = '( %s /\\ z = %s )' % (c, V); t = mkst(w, c2)
    zv = t([], 'simpr', 'z = %s' % V)
    rz = t([t([zv], 'fveq2d', '( Re ` z ) = ( Re ` %s )' % V), lift(w, reeq, c2)], 'eqtrd', '( Re ` z ) = %s' % rv)
    iz = t([t([t([zv], 'fveq2d', '( Im ` z ) = ( Im ` %s )' % V)], 'fveq2d', '( abs ` ( Im ` z ) ) = ( abs ` ( Im ` %s ) )' % V), lift(w, imeq, c2)], 'eqtrd',
           '( abs ` ( Im ` z ) ) = %s' % iv)
    L = {'( Re ` S )': lift(w, rs, c2), '( abs ` ( Im ` S ) )': lift(w, ais, c2)}
    rzr = t([lift(w, zc, c2)], 'recld', '( Re ` z ) e. RR')
    izr = t([t([t([lift(w, zc, c2)], 'imcld', '( Im ` z ) e. RR')], 'recnd', '( Im ` z ) e. CC')], 'abscld', '( abs ` ( Im ` z ) ) e. RR')
    L.update({'( Re ` z )': rzr, '( abs ` ( Im ` z ) )': izr})
    lo = linarith(w, c2, [rz, lift(w, c.hyps_lo, c2)] if False else [rz] + c_hyps(w, c, c2), '%s < ( Re ` z )' % CL, leaves=L)
    hi = linarith(w, c2, [rz] + c_hyps(w, c, c2), '( Re ` z ) < 3', leaves=L)
    im = linarith(w, c2, [iz] + c_hyps(w, c, c2), '( abs ` ( Im ` z ) ) < %s' % Y5, leaves=L)
    clr = t([c_(w, c2, num.real(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. RR'), L['( Re ` S )']], 'resubcld', '%s e. RR' % CL)
    n1 = t([t([t([lo], 'ltned', '%s =/= ( Re ` z )' % CL)], 'necomd', '( Re ` z ) =/= %s' % CL)], 'neneqd', '-. ( Re ` z ) = %s' % CL)
    n2 = t([t([hi], 'ltned', '( Re ` z ) =/= 3')], 'neneqd', '-. ( Re ` z ) = 3')
    y5r = t([L['( abs ` ( Im ` S ) )'], one(w, c2)], 'readdcld', '%s e. RR' % Y5)
    n3 = t([im, t([izr, y5r], 'ltnled', '( ( abs ` ( Im ` z ) ) < %s <-> -. %s <_ ( abs ` ( Im ` z ) ) )' % (Y5, Y5))], 'mpbid', '-. %s <_ ( abs ` ( Im ` z ) )' % Y5)
    D1 = '( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 )' % CL
    nd1 = t([t([n1, n2], 'jca', '( -. ( Re ` z ) = %s /\\ -. ( Re ` z ) = 3 )' % CL), c_(w, c2, w.s([], 'ioran', '( -. %s <-> ( -. ( Re ` z ) = %s /\\ -. ( Re ` z ) = 3 ) )' % (D1, CL)),
                                                                                  '( -. %s <-> ( -. ( Re ` z ) = %s /\\ -. ( Re ` z ) = 3 ) )' % (D1, CL))], 'mpbird', '-. %s' % D1)
    nd = t([t([nd1, n3], 'jca', '( -. %s /\\ -. %s <_ ( abs ` ( Im ` z ) ) )' % (D1, Y5)), c_(w, c2, w.s([], 'ioran', '( -. %s <-> ( -. %s /\\ -. %s <_ ( abs ` ( Im ` z ) ) ) )' % (D, D1, Y5)),
                                                                                   '( -. %s <-> ( -. %s /\\ -. %s <_ ( abs ` ( Im ` z ) ) ) )' % (D, D1, Y5))], 'mpbird', '-. %s' % D)
    dd = w.s([], 'simprr' if False else 'x', 'x') if False else None
    dstep = lift(w, CTX[c]['D'], c2)
    nz = w.s([dstep, nd], 'pm2.65da', '( %s -> -. z = %s )' % (c, V))
    return w.s([nz], 'neqned', '( %s -> z =/= %s )' % (c, V))


CTX = {}


def c_hyps(w, c, c2):
    return [lift(w, h, c2) for h in CTX[c]['hyps']]


def z6grsd():
    w = W('z6grsd', 'The strip hypothesis ` STRIPD ` of ~ z6shift for the contour integrand: the two vertical lines ` Re w = CL ` , ` Re w = 3 ` and '
          'the horizontal edges at heights ` >_ | Im S | + 1 ` avoid ` 0 ` and the pole ` 1 - S ` , so they lie in ` DS ` (~ z6rdg ).')
    a = ante('z6grsd'); fa = unpack(w, a); st = mkst(w, a)
    H = '( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) /\\ ( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 ) \\/ %s <_ ( abs ` ( Im ` z ) ) ) )' % (CL, CL, Y5)
    c0 = '( %s /\\ z e. CC )' % a
    c = '( %s /\\ %s )' % (c0, H); t = mkst(w, c)
    f = unpack(w, c)
    zc = f['z e. CC']; sc = f['S e. CC']; lo = f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']; hi = f['( Re ` S ) <_ 1']
    rs = t([sc], 'recld', '( Re ` S ) e. RR')
    isr = t([sc], 'imcld', '( Im ` S ) e. RR'); isc = t([isr], 'recnd', '( Im ` S ) e. CC')
    ais = t([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR'); ag0 = t([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')
    CTX[c] = {'hyps': [lo, hi, ag0], 'D': f['( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 ) \\/ %s <_ ( abs ` ( Im ` z ) ) )' % (CL, Y5)]}
    one_ = c_(w, c, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    P = '( 1 - S )'
    rp = t([t([one_, sc], 'resubd', '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` S ) )' % P),
            t([c_(w, c, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'oveq1d', '( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) )')], 'eqtrd', '( Re ` %s ) = ( 1 - ( Re ` S ) )' % P)
    ip = t([t([one_, sc], 'imsubd', '( Im ` %s ) = ( ( Im ` 1 ) - ( Im ` S ) )' % P),
            t([c_(w, c, w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')], 'oveq1d', '( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) )')], 'eqtrd', '( Im ` %s ) = ( 0 - ( Im ` S ) )' % P)
    ng = c_(w, c, w.s([w.s([], 'df-neg', '-u ( Im ` S ) = ( 0 - ( Im ` S ) )')], 'eqcomi', '( 0 - ( Im ` S ) ) = -u ( Im ` S )'), '( 0 - ( Im ` S ) ) = -u ( Im ` S )')
    ipa = t([t([t([ip, ng], 'eqtrd', '( Im ` %s ) = -u ( Im ` S )' % P)], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` -u ( Im ` S ) )' % P), t([isc], 'absnegd',
                                                                                                                             '( abs ` -u ( Im ` S ) ) = ( abs ` ( Im ` S ) )')],
            'eqtrd', '( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` S ) )' % P)
    zp = notpt(w, c, P, rp, '( 1 - ( Re ` S ) )', ipa, '( abs ` ( Im ` S ) )', rs, ais, zc)
    r0 = c_(w, c, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')
    i0 = c_(w, c, w.s([w.s([w.s([], 'im0', '( Im ` 0 ) = 0')], 'fveq2i', '( abs ` ( Im ` 0 ) ) = ( abs ` 0 )'), w.s([], 'abs0', '( abs ` 0 ) = 0')], 'eqtri',
                      '( abs ` ( Im ` 0 ) ) = 0'), '( abs ` ( Im ` 0 ) ) = 0')
    z0 = notpt(w, c, '0', r0, '0', i0, '0', rs, ais, zc)
    rz = t([zc], 'recld', '( Re ` z ) e. RR')
    cl_ = f['%s <_ ( Re ` z )' % CL]
    L = {'( Re ` S )': rs, '( Re ` z )': rz}
    m1 = linarith(w, c, [cl_, hi], '-u 1 < ( Re ` z )', leaves=L)
    gs = linarith(w, c, [cl_], '-u ( Re ` S ) < ( Re ` z )', leaves=L)
    zdg = t([t([zc, t([m1, z0], 'jca', '( -u 1 < ( Re ` z ) /\\ z =/= 0 )')], 'jca', '( z e. CC /\\ ( -u 1 < ( Re ` z ) /\\ z =/= 0 ) )'), w.inst('z6rdg')], 'syl', 'z e. %s' % DG)
    zu = t([t([zc, gs], 'jca', '( z e. CC /\\ -u ( Re ` S ) < ( Re ` z ) )'), t([t([rs], 'renegcld', '-u ( Re ` S ) e. RR'), w.inst('elhp2')], 'syl',
                                                                               '( z e. %s <-> ( z e. CC /\\ -u ( Re ` S ) < ( Re ` z ) ) )' % U5)], 'mpbird', 'z e. %s' % U5)
    UP = '( %s \\ { %s } )' % (U5, P)
    zup = t([t([zu, zp], 'jca', '( z e. %s /\\ z =/= %s )' % (U5, P)), c_(w, c, w.s([], 'eldifsn', '( z e. %s <-> ( z e. %s /\\ z =/= %s ) )' % (UP, U5, P)),
                                                                          '( z e. %s <-> ( z e. %s /\\ z =/= %s ) )' % (UP, U5, P))], 'mpbird', 'z e. %s' % UP)
    zds = t([t([zdg, zup], 'jca', '( z e. %s /\\ z e. %s )' % (DG, UP)), c_(w, c, w.s([], 'elin', '( z e. %s <-> ( z e. %s /\\ z e. %s ) )' % (DS, DG, UP)),
                                                                        '( z e. %s <-> ( z e. %s /\\ z e. %s ) )' % (DS, DG, UP))], 'mpbird', 'z e. %s' % DS)
    ex = w.s([zds], 'ex', '( %s -> ( %s -> z e. %s ) )' % (c0, H, DS))
    w.qed([ex], 'ralrimiva', STATEMENTS['z6grsd'])
    return w


def z6grmaj():
    w = W('z6grmaj', 'The strip hypothesis ` STRIPM ` of ~ z6shift for the contour integrand (Lean ` norm_Hfun_le ` , ` norm_Ghat_le ` ): '
          '` | GR ( z ) | <_ M5 2 ^ ( - | Im z | / 4 ) ` on ` CL <_ Re z <_ 3 ` , ` | Im z | >_ | Im S | + 1 ` (~ z6gstrip , ~ z6lstrip , ~ z5mrnorm , '
          '~ pol2exp , ~ z6gmaj ).')
    a = ante('z6grmaj'); st = mkst(w, a)
    H = '( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) /\\ %s <_ ( abs ` ( Im ` z ) ) )' % (CL, Y5)
    c0 = '( %s /\\ z e. CC )' % a
    c = '( %s /\\ %s )' % (c0, H); t = mkst(w, c)
    f = unpack(w, c)
    zc = f['z e. CC']; sc = f['S e. CC']; lo = f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']; hi = f['( Re ` S ) <_ 1']
    cl_ = f['%s <_ ( Re ` z )' % CL]; zh = f['( Re ` z ) <_ 3']; y5 = f['%s <_ ( abs ` ( Im ` z ) )' % Y5]
    rs = t([sc], 'recld', '( Re ` S ) e. RR'); rz = t([zc], 'recld', '( Re ` z ) e. RR')
    isr = t([sc], 'imcld', '( Im ` S ) e. RR'); isc = t([isr], 'recnd', '( Im ` S ) e. CC')
    ais = t([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR'); ag0 = t([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')
    izr = t([zc], 'imcld', '( Im ` z ) e. RR'); izc = t([izr], 'recnd', '( Im ` z ) e. CC')
    Y = '( abs ` ( Im ` z ) )'
    yr = t([izc], 'abscld', '%s e. RR' % Y); y0 = t([izc], 'absge0d', '0 <_ %s' % Y)
    L = {'( Re ` S )': rs, '( Re ` z )': rz, '( abs ` ( Im ` S ) )': ais, Y: yr}
    d = dfacts(w, c, f)
    # z e. DS by z6grsd
    gsd = w.s([st([], 'z6grsd' if False else 'x', 'x')] if False else [], 'z6grsd', STATEMENTS['z6grsd'])
    body = split_imp(STATEMENTS['z6grsd'])[1]
    BD = body[len('A. z e. CC '):]
    r19 = w.s([gsd], 'r19.21bi', '( %s -> %s )' % (c0, BD))
    Hp = '( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) /\\ ( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 ) \\/ %s <_ ( abs ` ( Im ` z ) ) ) )' % (CL, CL, Y5)
    hp = t([t([cl_, zh], 'jca', '( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 )' % CL), t([y5], 'olcd', '( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 ) \\/ %s <_ ( abs ` ( Im ` z ) ) )' % (CL, Y5))],
           'jca', Hp)
    zds = t([hp, lift(w, r19, c)], 'mpd', 'z e. %s' % DS)
    zdg = t([zds], 'elin1d', 'z e. %s' % DG)
    zup = t([zds], 'elin2d', 'z e. ( %s \\ { ( 1 - S ) } )' % U5)
    zu = t([zup], 'eldifad', 'z e. %s' % U5)
    zne = t([t([zup], 'eldifbd', '-. z e. { ( 1 - S ) }'), c_(w, c, w.s([], 'velsn', '( z e. { ( 1 - S ) } <-> z = ( 1 - S ) )'), '( z e. { ( 1 - S ) } <-> z = ( 1 - S ) )')],
            'mtbid' if False else 'x', 'x') if False else None
    zne = t([t([t([zup], 'eldifbd', '-. z e. { ( 1 - S ) }'), c_(w, c, w.s([], 'velsn', '( z e. { ( 1 - S ) } <-> z = ( 1 - S ) )'), '( z e. { ( 1 - S ) } <-> z = ( 1 - S ) )')],
                'mtbid' if False else 'x', 'x')] if False else [], 'x', 'x') if False else None
    nsn = t([zup], 'eldifbd', '-. z e. { ( 1 - S ) }')
    vel = w.s([], 'velsn', '( z e. { ( 1 - S ) } <-> z = ( 1 - S ) )')
    zne = t([w.s([nsn, vel], 'sylnib', '( %s -> -. z = ( 1 - S ) )' % c)], 'neqned', 'z =/= ( 1 - S )')
    # the value
    grb = '( ( ( _G ` w ) x. ( %s ^c w ) ) x. ( ( ( E ` ( S + w ) ) / ( ( S + w ) - 1 ) ) x. %s ) )' % (XPD, MRr('R', '( S + w )'))
    gv, gval = mpval(w, c, 'w', DS, grb, 'z', zds)
    Gz = '( _G ` z )'; Xz = '( %s ^c z )' % XPD; Ez = '( E ` ( S + z ) )'; Dn = '( ( S + z ) - 1 )'; Mz = MRr('R', '( S + z )')
    Qz = '( %s / %s )' % (Ez, Dn)
    gc = t([zdg, w.inst('gamcl')], 'syl', '%s e. CC' % Gz)
    xc = t([d['xrp']], 'rpcnd', '%s e. CC' % XPD)
    xzc = t([xc, zc], 'cxpcld', '%s e. CC' % Xz)
    gs_ = linarith(w, c, [cl_], '-u ( Re ` S ) < ( Re ` z )', leaves=L)
    suh = hpzpt(w, c, 'z', zc, gs_, sc, rev=True)
    ef = t([f['E e. ( %s -cn-> CC )' % HPZ], w.inst('cncff')], 'syl', 'E : %s --> CC' % HPZ)
    ezc = t([ef, suh], 'ffvelcdmd', '%s e. CC' % Ez)
    suc = t([sc, zc], 'addcld', '( S + z ) e. CC')
    one_ = c_(w, c, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    dnc = t([suc, one_], 'subcld', '%s e. CC' % Dn)
    dq = t([t([zc, one_, sc], 'subsub3d', '( z - ( 1 - S ) ) = ( ( z + S ) - 1 )'), t([t([zc, sc], 'addcomd', '( z + S ) = ( S + z )')], 'oveq1d', '( ( z + S ) - 1 ) = %s' % Dn)],
           'eqtrd', '( z - ( 1 - S ) ) = %s' % Dn)
    dn0 = t([dq, t([zc, t([one_, sc], 'subcld', '( 1 - S ) e. CC'), zne], 'subne0d', '( z - ( 1 - S ) ) =/= 0')], 'eqnetrrd', '%s =/= 0' % Dn)
    qc = t([ezc, dnc, dn0], 'divcld', '%s e. CC' % Qz)
    mzc = mrcc(w, c, d['mff'], '( S + z )', suc)
    GX = '( %s x. %s )' % (Gz, Xz); QM = '( %s x. %s )' % (Qz, Mz)
    ab1 = t([t([gc, xzc], 'mulcld', '%s e. CC' % GX), t([qc, mzc], 'mulcld', '%s e. CC' % QM)], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GX, QM, GX, QM))
    ab2 = t([gc, xzc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GX, Gz, Xz))
    ab3 = t([qc, mzc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (QM, Qz, Mz))
    PROD = '( ( ( abs ` %s ) x. ( abs ` %s ) ) x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Gz, Xz, Qz, Mz)
    ab = t([ab1, t([ab2, ab3], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = %s' % (GX, QM, PROD))], 'eqtrd', '( abs ` ( %s x. %s ) ) = %s' % (GX, QM, PROD))
    assert gval == '( %s x. %s )' % (GX, QM), gval
    agr = t([t([gv], 'fveq2d', '( abs ` ( %s ` z ) ) = ( abs ` %s )' % (GR('R'), gval)), ab], 'eqtrd', '( abs ` ( %s ` z ) ) = %s' % (GR('R'), PROD))
    # Gamma
    y1 = linarith(w, c, [y5, ag0], '1 <_ %s' % Y, leaves=L)
    zlo = linarith(w, c, [cl_, hi], '-u ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` z )', leaves=L)
    fg = {'W e. CC': zc, '-u ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` W )': zlo, '( Re ` W ) <_ 3': zh, '1 <_ ( abs ` ( Im ` W ) )': y1}
    fg = {sub(k, {'W': 'z'}): v for k, v in fg.items()}
    gb, _ = applyn(w, c, 'z6gstrip', {'W': 'z'}, fg)
    # X ^ z
    dr = f['D e. RR']; d1 = f['1 < D']
    xgt = t([t([c_(w, c, w.s([], '0lt1', '0 < 1') if False else num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'x', 'x')], 'x', 'x') if False else None
    c65 = c_(w, c, num.real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')
    c0r = c_(w, c, w.s([], '0re', '0 e. RR'), '0 e. RR')
    cxl = t([t([t([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), t([c0r, c65], 'jca', '( 0 e. RR /\\ ( 6 / 5 ) e. RR )')], 'jca',
                '( ( D e. RR /\\ 1 < D ) /\\ ( 0 e. RR /\\ ( 6 / 5 ) e. RR ) )'), w.inst('cxplt')], 'syl', '( 0 < ( 6 / 5 ) <-> ( D ^c 0 ) < %s )' % XPD)
    g65 = c_(w, c, num.fact(w, '( 6 / 5 )', 'gt0'), '0 < ( 6 / 5 )')
    x1 = t([t([t([g65, cxl], 'mpbid', '( D ^c 0 ) < %s' % XPD), t([t([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1')], 'x', 'x')], 'x', 'x') if False else None
    x1 = t([t([t([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1'), t([g65, cxl], 'mpbid', '( D ^c 0 ) < %s' % XPD)], 'eqbrtrrd', '1 < %s' % XPD)
    xr = t([d['xrp']], 'rpred', '%s e. RR' % XPD)
    three = c_(w, c, w.s([], '3re', '3 e. RR'), '3 e. RR')
    cxl2 = t([t([t([xr, x1], 'jca', '( %s e. RR /\\ 1 < %s )' % (XPD, XPD)), t([rz, three], 'jca', '( ( Re ` z ) e. RR /\\ 3 e. RR )')], 'jca',
                 '( ( %s e. RR /\\ 1 < %s ) /\\ ( ( Re ` z ) e. RR /\\ 3 e. RR ) )' % (XPD, XPD)), w.inst('cxple')], 'syl',
             '( ( Re ` z ) <_ 3 <-> ( %s ^c ( Re ` z ) ) <_ ( %s ^c 3 ) )' % (XPD, XPD))
    xb0 = t([zh, cxl2], 'mpbid', '( %s ^c ( Re ` z ) ) <_ ( %s ^c 3 )' % (XPD, XPD))
    axz = t([d['xrp'], zc, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( %s ^c ( Re ` z ) )' % (Xz, XPD))
    xb = t([axz, xb0], 'eqbrtrd', '( abs ` %s ) <_ ( %s ^c 3 )' % (Xz, XPD))
    # E / ( s - 1 )
    W_ = '( S + z )'
    rsz = t([t([sc, zc], 'readdd', '( Re ` %s ) = ( ( Re ` S ) + ( Re ` z ) )' % W_)], 'id' if False else 'x', 'x') if False else None
    rsz = t([sc, zc], 'readdd', '( Re ` %s ) = ( ( Re ` S ) + ( Re ` z ) )' % W_)
    wlo = t([linarith(w, c, [cl_], '( 1 / ; ; 1 0 0 ) <_ ( ( Re ` S ) + ( Re ` z ) )', leaves=L), rsz], 'breqtrrd', '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_)
    isz = t([sc, zc], 'imaddd', '( Im ` %s ) = ( ( Im ` S ) + ( Im ` z ) )' % W_)
    AIW = '( abs ` ( Im ` %s ) )' % W_
    ad = t([izc, t([isc], 'negcld', '-u ( Im ` S ) e. CC')], 'abs2difd', '( ( abs ` ( Im ` z ) ) - ( abs ` -u ( Im ` S ) ) ) <_ ( abs ` ( ( Im ` z ) - -u ( Im ` S ) ) )')
    e_ = t([t([izc, isc], 'subnegd', '( ( Im ` z ) - -u ( Im ` S ) ) = ( ( Im ` z ) + ( Im ` S ) )'),
            t([t([izc, isc], 'addcomd', '( ( Im ` z ) + ( Im ` S ) ) = ( ( Im ` S ) + ( Im ` z ) )'), t([isz], 'eqcomd', '( ( Im ` S ) + ( Im ` z ) ) = ( Im ` %s )' % W_)],
              'eqtrd', '( ( Im ` z ) + ( Im ` S ) ) = ( Im ` %s )' % W_)], 'eqtrd', '( ( Im ` z ) - -u ( Im ` S ) ) = ( Im ` %s )' % W_)
    ad2 = t([t([ad, t([e_], 'fveq2d', '( abs ` ( ( Im ` z ) - -u ( Im ` S ) ) ) = %s' % AIW)], 'breqtrd',
               '( ( abs ` ( Im ` z ) ) - ( abs ` -u ( Im ` S ) ) ) <_ %s' % AIW),
             t([t([t([isc], 'absnegd', '( abs ` -u ( Im ` S ) ) = ( abs ` ( Im ` S ) )')], 'oveq2d',
                  '( ( abs ` ( Im ` z ) ) - ( abs ` -u ( Im ` S ) ) ) = ( ( abs ` ( Im ` z ) ) - ( abs ` ( Im ` S ) ) )')], 'eqcomd',
               '( ( abs ` ( Im ` z ) ) - ( abs ` ( Im ` S ) ) ) = ( ( abs ` ( Im ` z ) ) - ( abs ` -u ( Im ` S ) ) )')], 'eqbrtrd' if False else 'x', 'x') if False else None
    adv = t([ad, t([e_], 'fveq2d', '( abs ` ( ( Im ` z ) - -u ( Im ` S ) ) ) = %s' % AIW)], 'breqtrd', '( ( abs ` ( Im ` z ) ) - ( abs ` -u ( Im ` S ) ) ) <_ %s' % AIW)
    ane = t([isc], 'absnegd', '( abs ` -u ( Im ` S ) ) = ( abs ` ( Im ` S ) )')
    awr = t([t([t([suc], 'imcld', '( Im ` %s ) e. RR' % W_)], 'recnd', '( Im ` %s ) e. CC' % W_)], 'abscld', '%s e. RR' % AIW)
    anr = t([t([isc], 'negcld', '-u ( Im ` S ) e. CC')], 'abscld', '( abs ` -u ( Im ` S ) ) e. RR')
    L2 = dict(L); L2.update({AIW: awr, '( abs ` -u ( Im ` S ) )': anr})
    w1 = linarith(w, c, [adv, ane, y5], '1 <_ %s' % AIW, leaves=L2)
    fl = {'N e. NN': f['N e. NN'], 'C : NN --> CC': f['C : NN --> CC'], CB: f[CB], DSER: f[DSER], CVXH: f[CVXH], '%s e. CC' % W_: suc,
          '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_: wlo, '1 <_ %s' % AIW: w1}
    lb, lbc = applyn(w, c, 'z6lstrip', {'W': W_}, fl)
    # CVX4 ( S + z ) <_ LB0 ( 1 + y ) ^ 2
    tri = t([isr, izr], 'x', 'x') if False else None
    tri = t([t([isr], 'recnd', '( Im ` S ) e. CC'), izc], 'abstrid', '( abs ` ( ( Im ` S ) + ( Im ` z ) ) ) <_ ( ( abs ` ( Im ` S ) ) + %s )' % Y)
    tri2 = t([t([t([isz], 'fveq2d', '%s = ( abs ` ( ( Im ` S ) + ( Im ` z ) ) )' % AIW)], 'x', 'x')], 'x', 'x') if False else None
    tri2 = t([t([isz], 'fveq2d', '%s = ( abs ` ( ( Im ` S ) + ( Im ` z ) ) )' % AIW), tri], 'eqbrtrd', '%s <_ ( ( abs ` ( Im ` S ) ) + %s )' % (AIW, Y))
    ASY = '( ( abs ` ( Im ` S ) ) x. %s )' % Y
    asy0 = t([ais, yr, ag0, y0], 'mulge0d', '0 <_ %s' % ASY)
    asyr = t([ais, yr], 'remulcld', '%s e. RR' % ASY)
    A3 = '( ( abs ` ( Im ` S ) ) + 3 )'; Y1 = '( 1 + %s )' % Y
    L3 = dict(L2); L3.update({ASY: asyr})
    lhs3 = '( %s + 3 )' % AIW
    old = lin.MAXDEG
    u1 = linarith(w, c, [tri2, asy0, y0], '%s <_ ( %s x. %s )' % (lhs3, A3, Y1), leaves=L3, products=True)
    nr = t([f['N e. NN']], 'nnred', 'N e. RR'); n0 = t([t([f['N e. NN']], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N')
    l3r = t([awr, three], 'readdcld', '%s e. RR' % lhs3)
    a3r = t([ais, three], 'readdcld', '%s e. RR' % A3); y1r = t([one(w, c), yr], 'readdcld', '%s e. RR' % Y1)
    ayr = t([a3r, y1r], 'remulcld', '( %s x. %s ) e. RR' % (A3, Y1))
    u2 = t([l3r, ayr, nr, n0, u1], 'lemul2ad', '( N x. %s ) <_ ( N x. ( %s x. %s ) )' % (lhs3, A3, Y1))
    NA = '( N x. %s )' % A3
    u3 = t([u2, t([t([nr], 'recnd', 'N e. CC'), t([a3r], 'recnd', '%s e. CC' % A3), t([y1r], 'recnd', '%s e. CC' % Y1)], 'mulassd',
                  '( %s x. %s ) = ( N x. ( %s x. %s ) )' % (NA, Y1, A3, Y1))], 'breqtrrd', '( N x. %s ) <_ ( %s x. %s )' % (lhs3, NA, Y1))
    LN = '( N x. %s )' % lhs3; RN = '( %s x. %s )' % (NA, Y1)
    lnr = t([nr, l3r], 'remulcld', '%s e. RR' % LN); rnr = t([t([nr, a3r], 'remulcld', '%s e. RR' % NA), y1r], 'remulcld', '%s e. RR' % RN)
    ln0 = t([nr, l3r, n0, linarith(w, c, [], '0 <_ %s' % lhs3, leaves=L2) if False else linarith(w, c, [t([t([t([suc], 'imcld', '( Im ` %s ) e. RR' % W_)], 'recnd',
                                                                                                         '( Im ` %s ) e. CC' % W_)], 'absge0d', '0 <_ %s' % AIW)],
                                                                                                    '0 <_ %s' % lhs3, leaves=L2)], 'mulge0d', '0 <_ %s' % LN)
    rn0 = linarith(w, c, [u3, ln0], '0 <_ %s' % RN, leaves={LN: lnr, RN: rnr})
    sq = t([u3, t([lnr, rnr, ln0, rn0], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (LN, RN, LN, RN))], 'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LN, RN))
    sqm = t([t([t([nr, a3r], 'remulcld', '%s e. RR' % NA)], 'recnd', '%s e. CC' % NA), t([y1r], 'recnd', '%s e. CC' % Y1)], 'sqmuld',
            '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (RN, NA, Y1))
    sq2 = t([sq, sqm], 'breqtrd', '( %s ^ 2 ) <_ ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (LN, NA, Y1))
    rr, ge1 = omgfacts(w, c, f['N e. NN'])
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    k4r = t([c_(w, c, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr], 'remulcld', '%s e. RR' % K4)
    k40 = linarith(w, c, [ge1], '0 <_ %s' % K4, leaves={OMGN: rr})
    ln2 = t([lnr], 'resqcld', '( %s ^ 2 ) e. RR' % LN)
    na2 = t([t([nr, a3r], 'remulcld', '%s e. RR' % NA)], 'resqcld', '( %s ^ 2 ) e. RR' % NA); y12 = t([y1r], 'resqcld', '( %s ^ 2 ) e. RR' % Y1)
    sq3 = t([ln2, t([na2, y12], 'remulcld', '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) e. RR' % (NA, Y1)), k4r, k40, sq2], 'lemul2ad',
            '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( ( %s ^ 2 ) x. ( %s ^ 2 ) ) )' % (K4, LN, K4, NA, Y1))
    LB0Q = '( %s x. ( %s ^ 2 ) )' % (LB0, Y1)
    assert LB0 == '( %s x. ( %s ^ 2 ) )' % (K4, NA), LB0
    sq4 = t([sq3, t([t([k4r], 'recnd', '%s e. CC' % K4), t([na2], 'recnd', '( %s ^ 2 ) e. CC' % NA), t([y12], 'recnd', '( %s ^ 2 ) e. CC' % Y1)], 'mulassd',
                    '( ( %s x. ( %s ^ 2 ) ) x. ( %s ^ 2 ) ) = ( %s x. ( ( %s ^ 2 ) x. ( %s ^ 2 ) ) )' % (K4, NA, Y1, K4, NA, Y1))], 'breqtrrd',
            '( %s x. ( %s ^ 2 ) ) <_ %s' % (K4, LN, LB0Q))
    assert lbc.endswith('<_ ( %s x. ( %s ^ 2 ) )' % (K4, LN)), lbc
    AQ = '( abs ` %s )' % Qz
    aqr = t([qc], 'abscld', '%s e. RR' % AQ)
    c4r = t([k4r, ln2], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (K4, LN))
    lbr = t([t([k4r, na2], 'remulcld', '%s e. RR' % LB0), y12], 'remulcld', '%s e. RR' % LB0Q)
    vb = t([aqr, c4r, lbr, lb, sq4], 'letrd', '%s <_ %s' % (AQ, LB0Q))
    # M_r
    rsz0 = t([linarith(w, c, [cl_, lo], '0 <_ ( ( Re ` S ) + ( Re ` z ) )', leaves=L), rsz], 'breqtrrd', '0 <_ ( Re ` %s )' % W_)
    fm = {sub(HAB0, {'A': Z1D, 'B': Z2D}): d['hab'], 'R e. NN': f['R e. NN'], '( mmu ` R ) =/= 0': f['( mmu ` R ) =/= 0'], 'C : NN --> CC': f['C : NN --> CC'],
          CB: f[CB], '%s e. CC' % W_: suc, '0 <_ ( Re ` %s )' % W_: rsz0}
    mb, _ = applyn(w, c, 'z5mrnorm', {'A': Z1D, 'B': Z2D, 'S': W_}, fm)
    # pol2exp
    pe = t([yr, y0, w.inst('pol2exp')], 'syl2anc', '( ( ( 1 + %s ) ^ 2 ) x. %s ) <_ ( ; ; 1 2 8 x. %s )' % (Y, E2(Y), E4(Y)))
    # z6gmaj
    G_ = '( abs ` %s )' % Gz; X_ = '( abs ` %s )' % Xz; M_ = '( abs ` %s )' % Mz
    ZR = '( %s x. ( R ^ 3 ) )' % Z2D
    fg = {}
    fg['%s e. RR' % G_] = t([gc], 'abscld', '%s e. RR' % G_); fg['0 <_ %s' % G_] = t([gc], 'absge0d', '0 <_ %s' % G_)
    fg['%s e. RR' % X_] = t([xzc], 'abscld', '%s e. RR' % X_); fg['0 <_ %s' % X_] = t([xzc], 'absge0d', '0 <_ %s' % X_)
    fg['%s e. RR' % AQ] = aqr; fg['0 <_ %s' % AQ] = t([qc], 'absge0d', '0 <_ %s' % AQ)
    fg['%s e. RR' % M_] = t([mzc], 'abscld', '%s e. RR' % M_); fg['0 <_ %s' % M_] = t([mzc], 'absge0d', '0 <_ %s' % M_)
    fg['%s <_ ( ; ; ; 1 6 3 2 x. %s )' % (G_, E2(Y))] = gb
    fg['%s <_ ( %s ^c 3 )' % (X_, XPD)] = xb
    fg['%s <_ %s' % (AQ, LB0Q)] = vb
    fg['%s <_ %s' % (M_, ZR)] = mb
    fg['; ; ; 1 6 3 2 e. RR'] = c_(w, c, num.real(w, '; ; ; 1 6 3 2'), '; ; ; 1 6 3 2 e. RR')
    fg['0 <_ ; ; ; 1 6 3 2'] = c_(w, c, num.fact(w, '; ; ; 1 6 3 2', 'ge0'), '0 <_ ; ; ; 1 6 3 2')
    fg['( %s ^c 3 ) e. RR' % XPD] = t([t([d['xrp'], three], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
    fg['%s e. RR' % LB0] = t([k4r, na2], 'remulcld', '%s e. RR' % LB0)
    fg['0 <_ %s' % LB0] = t([k4r, na2, k40, t([t([nr, a3r], 'remulcld', '%s e. RR' % NA)], 'sqge0d', '0 <_ ( %s ^ 2 )' % NA)], 'mulge0d', '0 <_ %s' % LB0)
    fg['%s e. RR' % ZR] = t([t([d['z2rp']], 'rpred', '%s e. RR' % Z2D), t([t([f['R e. NN']], 'nnred', 'R e. RR'), c_(w, c, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld',
                                                                                       '( R ^ 3 ) e. RR')], 'remulcld', '%s e. RR' % ZR)
    two = c_(w, c, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')
    fg['%s e. RR' % E2(Y)] = t([t([two, t([t([yr], 'rehalfcld', '( %s / 2 ) e. RR' % Y)], 'renegcld', '-u ( %s / 2 ) e. RR' % Y)], 'rpcxpcld', '%s e. RR+' % E2(Y))],
                               'rpred', '%s e. RR' % E2(Y))
    fg['%s e. RR' % E4(Y)] = t([t([two, t([t([yr, c_(w, c, w.s([], '4re', '4 e. RR'), '4 e. RR'), c_(w, c, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( %s / 4 ) e. RR' % Y)],
                                          'renegcld', '-u ( %s / 4 ) e. RR' % Y)], 'rpcxpcld', '%s e. RR+' % E4(Y))], 'rpred', '%s e. RR' % E4(Y))
    fg['( ( 1 + %s ) ^ 2 ) e. RR' % Y] = y12
    fg['( ( ( 1 + %s ) ^ 2 ) x. %s ) <_ ( ; ; 1 2 8 x. %s )' % (Y, E2(Y), E4(Y))] = pe
    gm, gmc = applyn(w, c, 'z6gmaj', {'G': G_, 'X': X_, 'V': AQ, 'M': M_, 'A': '; ; ; 1 6 3 2', 'E': E2(Y), 'K': '( %s ^c 3 )' % XPD, 'B': LB0, 'Q': '( ( 1 + %s ) ^ 2 )' % Y,
                                              'Z': ZR, 'F': E4(Y)}, fg)
    fin = t([agr, gm], 'eqbrtrd', '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (GR('R'), M5, E4(Y)))
    ex = w.s([fin], 'ex', '( %s -> ( %s -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )' % (c0, H, GR('R'), M5, E4(Y)))
    w.qed([ex], 'ralrimiva', STATEMENTS['z6grmaj'])
    return w


def z6shiftr():
    w = W('z6shiftr', 'The contour shift from ` Re w = 3 ` to ` Re w = CL = eps2 - Re S ` (Lean ` Ghat_line_shift ` and ` Ghat_line_shift_principal ` in one '
          'statement): ~ z6shift with the rectangle identity ~ z6rect , the strip ~ z6grsd and the majorant ~ z6grmaj .')
    a = ante('z6shiftr'); f = unpack(w, a); st = mkst(w, a)
    sc = f['S e. CC']; lo = f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']
    d = dfacts(w, a, f)
    rs = st([sc], 'recld', '( Re ` S ) e. RR')
    c100 = c_(w, a, num.real(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. RR')
    fz = {}
    fz['%s e. RR' % CL] = st([c100, rs], 'resubcld', '%s e. RR' % CL)
    fz['3 e. RR'] = c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')
    fz['%s < 3' % CL] = linarith(w, a, [lo], '%s < 3' % CL, leaves={'( Re ` S )': rs})
    fz['%s e. ( %s -cn-> CC )' % (GR('R'), DS)], _ = applyn(w, a, 'z6grcn', {}, f)
    fz[split_imp(STATEMENTS['z6grsd'])[1]] = w.s([], 'z6grsd', STATEMENTS['z6grsd'])
    fz[split_imp(STATEMENTS['z6grmaj'])[1]] = w.s([], 'z6grmaj', STATEMENTS['z6grmaj'])
    isc = st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')
    ais = st([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR'); ag0 = st([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')
    y5r = st([ais, one(w, a)], 'readdcld', '%s e. RR' % Y5)
    fz['%s e. RR+' % Y5] = st([y5r, linarith(w, a, [ag0], '0 < %s' % Y5, leaves={'( abs ` ( Im ` S ) )': ais})], 'elrpd', '%s e. RR+' % Y5)
    # M5 e. RR
    rr, ge1 = omgfacts(w, a, f['N e. NN'])
    nr = st([f['N e. NN']], 'nnred', 'N e. RR')
    three = c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    NA = '( N x. ( ( abs ` ( Im ` S ) ) + 3 ) )'
    lb0 = st([st([c_(w, a, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr], 'remulcld', '%s e. RR' % K4),
              st([st([nr, st([ais, three], 'readdcld', '( ( abs ` ( Im ` S ) ) + 3 ) e. RR')], 'remulcld', '%s e. RR' % NA)], 'resqcld', '( %s ^ 2 ) e. RR' % NA)],
             'remulcld', '%s e. RR' % LB0)
    ZR = '( %s x. ( R ^ 3 ) )' % Z2D
    zr = st([st([d['z2rp']], 'rpred', '%s e. RR' % Z2D), st([st([f['R e. NN']], 'nnred', 'R e. RR'), c_(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld',
                                                                                      '( R ^ 3 ) e. RR')], 'remulcld', '%s e. RR' % ZR)
    x3 = st([st([d['xrp'], three], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
    c12 = st([c_(w, a, num.real(w, '; ; ; 1 6 3 2'), '; ; ; 1 6 3 2 e. RR'), c_(w, a, num.real(w, '; ; 1 2 8'), '; ; 1 2 8 e. RR')], 'remulcld', '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR')
    fz['%s e. RR' % M5] = st([st([c12, x3], 'remulcld', '( ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) x. ( %s ^c 3 ) ) e. RR' % XPD), st([lb0, zr], 'remulcld', '( %s x. %s ) e. RR' % (LB0, ZR))],
                             'remulcld', '%s e. RR' % M5)
    # K5 e. CC
    P = '( 1 - S )'
    one_ = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    pc = st([one_, sc], 'subcld', '%s e. CC' % P)
    pdg, _ = applyn(w, a, 'z6pdg', {}, f)
    gpc = st([pdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % P)
    xpc = st([st([d['xrp']], 'rpcnd', '%s e. CC' % XPD), pc], 'cxpcld', '( %s ^c %s ) e. CC' % (XPD, P))
    oneh = st([st([one_, st([c_(w, a, w.s([], '0lt1', '0 < 1'), '0 < 1'), c_(w, a, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'breqtrrd', '0 < ( Re ` 1 )')],
                  'jca', '( 1 e. CC /\\ 0 < ( Re ` 1 ) )'), st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl',
                                                             '( 1 e. %s <-> ( 1 e. CC /\\ 0 < ( Re ` 1 ) ) )' % HPZ)], 'mpbird', '1 e. %s' % HPZ)
    e1c = st([st([f['E e. ( %s -cn-> CC )' % HPZ], w.inst('cncff')], 'syl', 'E : %s --> CC' % HPZ), oneh], 'ffvelcdmd', '( E ` 1 ) e. CC')
    resc = st([f['( E ` 1 ) = %s' % RESV], e1c], 'eqeltrrd', '%s e. CC' % RESV)
    m1c = mrcc(w, a, d['mff'], '1', one_)
    tpi = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                  'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    fz['%s e. CC' % K5] = st([tpi, st([st([gpc, xpc], 'mulcld', '( ( _G ` %s ) x. ( %s ^c %s ) ) e. CC' % (P, XPD, P)),
                                        st([resc, m1c], 'mulcld', '( %s x. %s ) e. CC' % (RESV, MRr('R', '1')))], 'mulcld', '%s e. CC' % RES5)], 'mulcld', '%s e. CC' % K5)
    # the rectangle identity for every height t >_ Y5
    ct = '( %s /\\ t e. RR+ )' % a
    c2 = '( %s /\\ %s <_ t )' % (ct, Y5)
    tr = w.s([w.s([], 'simplr' , '( %s -> t e. RR+ )' % c2)], 'rpred', '( %s -> t e. RR )' % c2)
    hy = w.s([], 'simpr', '( %s -> %s <_ t )' % (c2, Y5))
    h = w.s([w.s([], 'simpll', '( %s -> %s )' % (c2, a)), w.s([tr, hy], 'jca', '( %s -> ( t e. RR /\\ %s <_ t ) )' % (c2, Y5))], 'jca',
            '( %s -> ( %s /\\ ( t e. RR /\\ %s <_ t ) ) )' % (c2, a, Y5))
    rct = w.s([h, w.inst('z6rect')], 'syl', '( %s -> %s = %s )' % (c2, RECT5('t'), K5))
    RTT = '( %s <_ t -> %s = %s )' % (Y5, RECT5('t'), K5)
    fz['A. t e. RR+ %s' % RTT] = st([w.s([rct], 'ex', '( %s -> %s )' % (ct, RTT))], 'ralrimiva', 'A. t e. RR+ %s' % RTT)
    sh, shc = applyn(w, a, 'z6shift', {'A': CL, 'B': '3', 'G': GR('R'), 'D': DS, 'M': M5, 'Y': Y5, 'K': K5}, fz)
    assert '( %s -> %s )' % (a, shc) == STATEMENTS['z6shiftr'], shc
    from z6a_mlib import toqed
    toqed(w, sh, 'z6shiftr')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6gmaj, z6grsd, z6grmaj, z6shiftr]:
        if want(fn.__name__):
            if not run(fn()):
                break
