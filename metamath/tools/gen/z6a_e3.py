"""Sortie Z6a (agent z6ae): Lean norm_LFunction_shifted_le (DetectionShift.lean section 2), stated for a real V below the
convexity bound CVXB(W) on Re W = 1/100 (z6lshift), with its helpers z6els1 .. z6els5.

With u = | Im W - Im S | and U = 1 + u:  N ( | Im W | + 2 ) <_ D U,  N ( | Im W | + 3 ) <_ 2 D U (z6els1);  the exponent
if ( 1 <_ Re W , 0 , ( 1 - Re W ) / 2 ) is 99/200 and 1 / | W - 1 | <_ 2 (z6els4);  ( N ( | Im W | + 2 ) ) ^ ( 99/200 ) <_
D ^ ( 99/200 ) U (z6els3);  log ( N ( | Im W | + 3 ) ) <_ 2 log D U (z6els2);  2 ^ omega ( N ) <_ C_tau D ^ ( 1/800 ) (z6omgd);
the algebra (z6els5) and D ^ ( 1/800 ) D ^ ( 99/200 ) = D ^ ( 397/800 )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6alib import *
from tm import sub
from cl import Closure, split_imp
import lin
import num

E = '( ; 9 9 / ; ; 2 0 0 )'
R8 = '( 1 / ; ; 8 0 0 )'
C2 = '; ; ; ; ; 2 0 0 0 0 0'
C6 = '; ; ; ; ; 6 0 0 0 0 0'


# ------------------------------------------------------------------ wff plumbing
def _split(f):
    """top-level conjuncts of '( X /\\ Y )' or '( X /\\ Y /\\ Z )', else None"""
    toks = f.split()
    if toks[0] != '(' or toks[-1] != ')':
        return None
    parts = []; d = 0; cur = []
    for tk in toks[1:-1]:
        if tk == '(':
            d += 1
        elif tk == ')':
            d -= 1
        if d == 0 and tk == '/\\':
            parts.append(' '.join(cur)); cur = []
        else:
            cur.append(tk)
    parts.append(' '.join(cur))
    return parts if len(parts) in (2, 3) else None


def conjs(w, a, step, f, out):
    """record in out every sub-conjunct of f (proved by step under a)"""
    out[f] = step
    p = _split(f)
    if p is None:
        return out
    refs = ['simpld', 'simprd'] if len(p) == 2 else ['simp1d', 'simp2d', 'simp3d']
    for x, r in zip(p, refs):
        conjs(w, a, w.s([step], r, '( %s -> %s )' % (a, x)), x, out)
    return out


def build(w, a, f, facts):
    """( a -> f ) from facts (formula -> step), splitting conjunctions"""
    if f in facts:
        return facts[f]
    p = _split(f)
    if p is None:
        raise KeyError('no fact for ' + f)
    subs = [build(w, a, x, facts) for x in p]
    st_ = w.s(subs, 'jca' if len(p) == 2 else '3jca', '( %s -> %s )' % (a, f))
    facts[f] = st_
    return st_


def apply(w, a, lab, m, facts):
    """( a -> concl ) by lab instantiated with m; antecedent built from facts"""
    an, co = split_imp(STATEMENTS[lab])
    an = sub(an, m); co = sub(co, m)
    h = build(w, a, an, facts)
    return w.s([h, w.inst(lab)], 'syl', '( %s -> %s )' % (a, co)), co


def unpack(w, a):
    top = w.s([], 'id', '( %s -> %s )' % (a, a))
    return conjs(w, a, top, a, {})


def c_(w, a, step, f):
    return w.s([step], 'a1i', '( %s -> %s )' % (a, f))


# ------------------------------------------------------------------ helpers
def z6els1():
    w = W('z6els1', 'Helper of z6lshift: N ( T + 2 ) <_ D ( 1 + U ) and N ( T + 3 ) <_ 2 D ( 1 + U ) from T - A <_ U and N ( A + 2 ) <_ D.')
    a = ante('z6els1'); f = unpack(w, a); st = mkst(w, a)
    nn = f['N e. NN']; dr = f['D e. RR']
    n0 = st([st([nn], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N'); nre = st([nn], 'nnred', 'N e. RR')
    cl = Closure(w, a, {'N': [('NN', nn), ('ge0', n0)], 'D': ('RR', dr), 'T': [('RR', f['T e. RR']), ('ge0', f['0 <_ T'])],
                        'A': [('RR', f['A e. RR']), ('ge0', f['0 <_ A'])], 'U': [('RR', f['U e. RR']), ('ge0', f['0 <_ U'])]})
    tri = f['( T - A ) <_ U']; hdn = f['( N x. ( A + 2 ) ) <_ D']
    na0 = st([nre, f['A e. RR'], n0, f['0 <_ A']], 'mulge0d', '0 <_ ( N x. A )')
    nu0 = st([nre, f['U e. RR'], n0, f['0 <_ U']], 'mulge0d', '0 <_ ( N x. U )')
    nD = lin.linarith(w, a, [hdn, na0, n0], 'N <_ D', closure=cl, products=True)
    tle = lin.linarith(w, a, [tri], 'T <_ ( A + U )', closure=cl)
    f1 = st([f['T e. RR'], cl.mem('( A + U )', 'RR'), nre, n0, tle], 'lemul2ad', '( N x. T ) <_ ( N x. ( A + U ) )')
    f4 = st([nre, dr, f['U e. RR'], f['0 <_ U'], nD], 'lemul1ad', '( N x. U ) <_ ( D x. U )')
    ale = lin.linarith(w, a, [f1, hdn, f4], '( N x. ( T + 2 ) ) <_ ( D x. ( 1 + U ) )', closure=cl, products=True)
    ble = lin.linarith(w, a, [f1, hdn, f4, na0, n0, nu0], '( N x. ( T + 3 ) ) <_ ( ( 2 x. D ) x. ( 1 + U ) )', closure=cl, products=True)
    w.qed([ale, ble], 'jca', STATEMENTS['z6els1'])
    return w


def z6els2():
    w = W('z6els2', 'Helper of z6lshift: log B <_ 2 log D ( 1 + U ) from B <_ 2 D ( 1 + U ), log D >_ 200 (log 2 < 1, log ( 1 + U ) <_ U).')
    a = ante('z6els2'); f = unpack(w, a); st = mkst(w, a)
    L = '( log ` D )'; U = '( 1 + U )'; D2U = '( ( 2 x. D ) x. ( 1 + U ) )'
    drp = f['D e. RR+']; ur = f['U e. RR']; u0 = f['0 <_ U']; brp = f['B e. RR+']; l200 = f['; ; 2 0 0 <_ ( log ` D )']
    lr = st([drp], 'relogcld', '%s e. RR' % L)
    cl = Closure(w, a, {'D': ('RR+', drp), 'U': [('RR', ur), ('ge0', u0)], 'B': ('RR+', brp), L: ('RR', lr)})
    cl.atom(L)
    tworp = c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')
    Urp = st([cl.mem(U, 'RR'), lin.linarith(w, a, [u0], '0 < %s' % U, closure=cl)], 'elrpd', '%s e. RR+' % U)
    D2rp = st([tworp, drp], 'rpmulcld', '( 2 x. D ) e. RR+')
    D2Urp = st([D2rp, Urp], 'rpmulcld', '%s e. RR+' % D2U)
    g1b = st([brp, D2Urp, w.inst('logleb')], 'syl2anc', '( B <_ %s <-> ( log ` B ) <_ ( log ` %s ) )' % (D2U, D2U))
    g1 = st([f['B <_ %s' % D2U], g1b], 'mpbid', '( log ` B ) <_ ( log ` %s )' % D2U)
    g2a = st([D2rp, Urp, w.inst('relogmul')], 'syl2anc', '( log ` %s ) = ( ( log ` ( 2 x. D ) ) + ( log ` %s ) )' % (D2U, U))
    g2b = st([tworp, drp, w.inst('relogmul')], 'syl2anc', '( log ` ( 2 x. D ) ) = ( ( log ` 2 ) + %s )' % L)
    eu = '( exp ` U )'
    g3a = st([ur, u0, w.inst('bvefge1p')], 'syl2anc', '%s <_ %s' % (U, eu))
    eurp = st([ur, w.inst('rpefcl')], 'syl', '%s e. RR+' % eu)
    g3b = st([Urp, eurp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (U, eu, U, eu))
    g3c = st([g3a, g3b], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (U, eu))
    g3d = st([ur, w.inst('relogef')], 'syl', '( log ` %s ) = U' % eu)
    g3 = st([g3c, g3d], 'breqtrd', '( log ` %s ) <_ U' % U)
    l2 = c_(w, a, w.s([], 'log2le1', '( log ` 2 ) < 1'), '( log ` 2 ) < 1')
    L1 = lin.linarith(w, a, [l200], '1 <_ %s' % L, closure=cl)
    pu = st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), lr, ur, u0, L1], 'lemul1ad', '( 1 x. U ) <_ ( %s x. U )' % L)
    for x, s_ in (('( log ` B )', st([brp], 'relogcld', '( log ` B ) e. RR')), ('( log ` %s )' % D2U, st([D2Urp], 'relogcld', '( log ` %s ) e. RR' % D2U)),
                  ('( log ` ( 2 x. D ) )', st([D2rp], 'relogcld', '( log ` ( 2 x. D ) ) e. RR')), ('( log ` %s )' % U, st([Urp], 'relogcld', '( log ` %s ) e. RR' % U)),
                  ('( log ` 2 )', c_(w, a, w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'), '( log ` 2 ) e. RR'))):
        cl.leaf(x, 'RR', s_)
    lin.linarith(w, a, [g1, g2a, g2b, l2, g3, L1, pu, u0], '( log ` B ) <_ ( ( 2 x. %s ) x. %s )' % (L, U), closure=cl, products=True, name='qed')
    return w


def z6els3():
    w = W('z6els3', 'Helper of z6lshift: A ^ ( 99/200 ) <_ D ^ ( 99/200 ) ( 1 + U ) from 0 <_ A <_ D ( 1 + U ), and 1 <_ D ^ ( 99/200 ).')
    a = ante('z6els3'); f = unpack(w, a); st = mkst(w, a)
    U = '( 1 + U )'; DU = '( D x. ( 1 + U ) )'; Pd = '( D ^c %s )' % E; PIe = '( A ^c %s )' % E; Ue = '( %s ^c %s )' % (U, E)
    dr = f['D e. RR']; d1 = f['1 <_ D']; ur = f['U e. RR']; u0 = f['0 <_ U']; Ar = f['A e. RR']; A0 = f['0 <_ A']
    cl = Closure(w, a, {'D': ('RR', dr), 'U': [('RR', ur), ('ge0', u0)], 'A': [('RR', Ar), ('ge0', A0)]})
    Ur = cl.mem(U, 'RR'); U0 = lin.linarith(w, a, [u0], '0 <_ %s' % U, closure=cl); U1 = lin.linarith(w, a, [u0], '1 <_ %s' % U, closure=cl)
    d0 = lin.linarith(w, a, [d1], '0 <_ D', closure=cl)
    DUr = st([dr, Ur], 'remulcld', '%s e. RR' % DU); DU0 = st([dr, Ur, d0, U0], 'mulge0d', '0 <_ %s' % DU)
    erp = c_(w, a, num.rp(w, E), '%s e. RR+' % E); ere = c_(w, a, num.real(w, E), '%s e. RR' % E); ecc = c_(w, a, num.cc(w, E), '%s e. CC' % E)
    e0 = c_(w, a, num.fact(w, E, 'ge0'), '0 <_ %s' % E)
    one = c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')
    c1b = st([st([Ar, A0], 'jca', '( A e. RR /\\ 0 <_ A )'), st([DUr, DU0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (DU, DU)), erp,
              w.inst('cxple2')], 'syl3anc', '( A <_ %s <-> %s <_ ( %s ^c %s ) )' % (DU, PIe, DU, E))
    c1 = st([f['A <_ %s' % DU], c1b], 'mpbid', '%s <_ ( %s ^c %s )' % (PIe, DU, E))
    c2 = st([st([dr, d0], 'jca', '( D e. RR /\\ 0 <_ D )'), st([Ur, U0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (U, U)), ecc, w.inst('mulcxp')], 'syl3anc',
            '( %s ^c %s ) = ( %s x. %s )' % (DU, E, Pd, Ue))
    c3 = st([st([Ur, U1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (U, U)), st([ere, one], 'jca', '( %s e. RR /\\ 1 e. RR )' % E),
             c_(w, a, num.le_lit(w, E, '1'), '%s <_ 1' % E), w.inst('cxplea')], 'syl3anc', '%s <_ ( %s ^c 1 )' % (Ue, U))
    c4 = st([st([Ur], 'recnd', '%s e. CC' % U), w.inst('cxp1')], 'syl', '( %s ^c 1 ) = %s' % (U, U))
    c5 = st([c3, c4], 'breqtrd', '%s <_ %s' % (Ue, U))
    Pdr = st([dr, d0, ere], 'recxpcld', '%s e. RR' % Pd)
    p0 = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 <_ D )'), st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), ere], 'jca', '( 0 e. RR /\\ %s e. RR )' % E),
             e0, w.inst('cxplea')], 'syl3anc', '( D ^c 0 ) <_ %s' % Pd)
    p1 = st([st([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1')
    Pd1 = st([p1, p0], 'eqbrtrrd', '1 <_ %s' % Pd)
    Pd0 = st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), one, Pdr, c_(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), Pd1], 'letrd', '0 <_ %s' % Pd)
    Uer = st([Ur, U0, ere], 'recxpcld', '%s e. RR' % Ue)
    c6 = st([Uer, Ur, Pdr, Pd0, c5], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (Pd, Ue, Pd, U))
    PIer = st([Ar, A0, ere], 'recxpcld', '%s e. RR' % PIe)
    c12 = st([c1, c2], 'breqtrd', '%s <_ ( %s x. %s )' % (PIe, Pd, Ue))
    hPI = st([PIer, st([Pdr, Uer], 'remulcld', '( %s x. %s ) e. RR' % (Pd, Ue)), st([Pdr, Ur], 'remulcld', '( %s x. %s ) e. RR' % (Pd, U)), c12, c6],
             'letrd', '%s <_ ( %s x. %s )' % (PIe, Pd, U))
    w.qed([hPI, Pd1], 'jca', STATEMENTS['z6els3'])
    return w


def z6els4():
    w = W('z6els4', 'Helper of z6lshift: on Re W = 1/100, 1 / | W - 1 | <_ 2 (| W - 1 | >_ Re ( 1 - W ) = 99/100) and the convexity exponent is 99/200.')
    a = ante('z6els4'); st = mkst(w, a)
    RW = '( Re ` W )'; I = '( 1 / ( abs ` ( W - 1 ) ) )'
    IFE = 'if ( 1 <_ %s , 0 , ( ( 1 - %s ) / 2 ) )' % (RW, RW)
    wc = st([], 'simpl', 'W e. CC'); rew = st([], 'simpr', '%s = ( 1 / ; ; 1 0 0 )' % RW)
    rw = st([wc, w.inst('recl')], 'syl', '%s e. RR' % RW)
    one_c = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    w1 = st([one_c, wc], 'subcld', '( 1 - W ) e. CC'); wm1 = st([wc, one_c], 'subcld', '( W - 1 ) e. CC')
    cl = Closure(w, a, {RW: ('RR', rw), '( Re ` ( 1 - W ) )': ('RR', st([w1, w.inst('recl')], 'syl', '( Re ` ( 1 - W ) ) e. RR')),
                        '( Re ` 1 )': ('RR', st([one_c, w.inst('recl')], 'syl', '( Re ` 1 ) e. RR')),
                        '( abs ` ( 1 - W ) )': ('RR', st([w1, w.inst('abscl')], 'syl', '( abs ` ( 1 - W ) ) e. RR')),
                        '( abs ` ( W - 1 ) )': ('RR', st([wm1, w.inst('abscl')], 'syl', '( abs ` ( W - 1 ) ) e. RR'))})
    for x in (RW, '( Re ` ( 1 - W ) )', '( Re ` 1 )', '( abs ` ( 1 - W ) )', '( abs ` ( W - 1 ) )'):
        cl.atom(x)
    rs = st([one_c, wc, w.inst('resub')], 'syl2anc', '( Re ` ( 1 - W ) ) = ( ( Re ` 1 ) - %s )' % RW)
    re1 = c_(w, a, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    rl = st([w1, w.inst('releabs')], 'syl', '( Re ` ( 1 - W ) ) <_ ( abs ` ( 1 - W ) )')
    asb = st([wc, one_c, w.inst('abssub')], 'syl2anc', '( abs ` ( W - 1 ) ) = ( abs ` ( 1 - W ) )')
    half = lin.linarith(w, a, [rs, re1, rew, rl, asb], '( 1 / 2 ) <_ ( abs ` ( W - 1 ) )', closure=cl)
    awp = lin.linarith(w, a, [half], '0 < ( abs ` ( W - 1 ) )', closure=cl)
    awr = cl.mem('( abs ` ( W - 1 ) )', 'RR')
    lrb = st([st([c_(w, a, num.real(w, '( 1 / 2 )'), '( 1 / 2 ) e. RR'), c_(w, a, num.fact(w, '( 1 / 2 )', 'gt0'), '0 < ( 1 / 2 )')], 'jca',
                 '( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) )'),
              st([awr, awp], 'jca', '( ( abs ` ( W - 1 ) ) e. RR /\\ 0 < ( abs ` ( W - 1 ) ) )'), w.inst('lerec')], 'syl2anc',
             '( ( 1 / 2 ) <_ ( abs ` ( W - 1 ) ) <-> %s <_ ( 1 / ( 1 / 2 ) ) )' % I)
    i1 = st([half, lrb], 'mpbid', '%s <_ ( 1 / ( 1 / 2 ) )' % I)
    rr2 = c_(w, a, w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0'), w.inst('recrec')], 'mp2an', '( 1 / ( 1 / 2 ) ) = 2'), '( 1 / ( 1 / 2 ) ) = 2')
    hI = st([i1, rr2], 'breqtrd', '%s <_ 2' % I)
    rlt = lin.linarith(w, a, [rew], '%s < 1' % RW, closure=cl)
    nle = st([rlt, st([rw, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'ltnled', '( %s < 1 <-> -. 1 <_ %s )' % (RW, RW))], 'mpbid', '-. 1 <_ %s' % RW)
    if1 = st([nle], 'iffalsed', '%s = ( ( 1 - %s ) / 2 )' % (IFE, RW))
    if2 = lin.lineq(w, a, '( ( 1 - %s ) / 2 )' % RW, E, hyps=[rew], closure=cl)
    ife = st([if1, if2], 'eqtrd', '%s = %s' % (IFE, E))
    w.qed([hI, ife], 'jca', STATEMENTS['z6els4'])
    return w


def z6els5():
    w = W('z6els5', 'Helper of z6lshift: the final algebra, 200000 O ( P G + I ) <_ 600000 C F H L ( 1 + U ) ^ 2 from O <_ C F, '
                    'P <_ H ( 1 + U ), G <_ 2 L ( 1 + U ), I <_ 2, 1 <_ H, 200 <_ L.')
    a = ante('z6els5'); f = unpack(w, a); st = mkst(w, a)
    U = '( 1 + U )'; UU = '( %s x. %s )' % (U, U); HL = '( H x. L )'
    R = lambda x: f['%s e. RR' % x]
    cl = Closure(w, a, {x: ('RR', R(x)) for x in 'V O C F P G I H L U'.split()})
    for x in 'V O C F P G I H L U'.split():
        cl.atom(x)
    Ur = cl.mem(U, 'RR'); u0 = f['0 <_ U']
    U1 = lin.linarith(w, a, [u0], '1 <_ %s' % U, closure=cl)
    m1 = st([R('P'), cl.mem('( H x. %s )' % U, 'RR'), R('G'), cl.mem('( ( 2 x. L ) x. %s )' % U, 'RR'), f['0 <_ P'], f['0 <_ G'],
             f['P <_ ( H x. %s )' % U], f['G <_ ( ( 2 x. L ) x. %s )' % U]], 'lemul12ad', '( P x. G ) <_ ( ( H x. %s ) x. ( ( 2 x. L ) x. %s ) )' % (U, U))
    L0 = lin.linarith(w, a, [f['; ; 2 0 0 <_ L']], '0 <_ L', closure=cl)
    one = c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')
    q1 = st([one, R('H'), R('L'), L0, f['1 <_ H']], 'lemul1ad', '( 1 x. L ) <_ %s' % HL)
    HLr = st([R('H'), R('L')], 'remulcld', '%s e. RR' % HL)
    H0 = lin.linarith(w, a, [f['1 <_ H']], '0 <_ H', closure=cl)
    HL0 = st([R('H'), R('L'), H0, L0], 'mulge0d', '0 <_ %s' % HL)
    UUr = st([Ur, Ur], 'remulcld', '%s e. RR' % UU)
    UU1 = lin.nlinarith(w, a, [U1], '1 <_ %s' % UU, closure=cl)
    q2 = st([one, UUr, HLr, HL0, UU1], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (HL, HL, UU))
    two = lin.linarith(w, a, [q1, q2, f['; ; 2 0 0 <_ L']], '2 <_ ( %s x. %s )' % (HL, UU), closure=cl, products=True)
    Xe = '( ( P x. G ) + I )'; Y = '( 3 x. ( %s x. %s ) )' % (HL, UU)
    xy = lin.linarith(w, a, [m1, two, f['I <_ 2']], '%s <_ %s' % (Xe, Y), closure=cl, products=True)
    pg0 = st([R('P'), R('G'), f['0 <_ P'], f['0 <_ G']], 'mulge0d', '0 <_ ( P x. G )')
    Xer = cl.mem(Xe, 'RR'); Yr = cl.mem(Y, 'RR')
    Xe0 = lin.linarith(w, a, [pg0, f['0 <_ I']], '0 <_ %s' % Xe, closure=cl, products=True)
    m2 = st([R('O'), cl.mem('( C x. F )', 'RR'), Xer, Yr, f['0 <_ O'], Xe0, f['O <_ ( C x. F )'], xy], 'lemul12ad',
            '( O x. %s ) <_ ( ( C x. F ) x. %s )' % (Xe, Y))
    cl.leaf(Xe, 'RR', Xer); cl.leaf(Y, 'RR', Yr)
    vle = f['V <_ ( ( %s x. O ) x. %s )' % (C2, Xe)]
    g1 = lin.linarith(w, a, [vle, m2], 'V <_ ( %s x. ( ( C x. F ) x. %s ) )' % (C2, Y), closure=cl, products=True)
    # the target ( ( ( C6 C ) ( F H ) ) L ) ( 1 + U ) ^ 2 is C2 ( ( C F ) Y ) with Y = 3 ( H L ) ( ( 1 + U ) ( 1 + U ) )
    sq = st([st([Ur], 'recnd', '%s e. CC' % U)], 'sqvald', '( %s ^ 2 ) = %s' % (U, UU))
    T1_ = '( ( ( ( %s x. C ) x. ( F x. H ) ) x. L ) x. ( %s ^ 2 ) )' % (C6, U)
    T2_ = '( ( ( ( %s x. C ) x. ( F x. H ) ) x. L ) x. %s )' % (C6, UU)
    e1 = st([sq], 'oveq2d', '%s = %s' % (T1_, T2_))
    cl2 = Closure(w, a, {x: ('RR', R(x)) for x in 'C F H L'.split()})
    for x in 'C F H L'.split():
        cl2.atom(x)
    cl2.leaf(UU, 'RR', UUr)
    old = lin.MAXDEG; lin.MAXDEG = 6
    e2 = lin.lineq(w, a, T2_, '( %s x. ( ( C x. F ) x. %s ) )' % (C2, Y), closure=cl2, products=True)
    lin.MAXDEG = old
    e3 = st([e1, e2], 'eqtrd', '%s = ( %s x. ( ( C x. F ) x. %s ) )' % (T1_, C2, Y))
    w.qed([g1, e3], 'breqtrrd', STATEMENTS['z6els5'])
    return w


# ------------------------------------------------------------------ the theorem
def z6lshift():
    w = W('z6lshift', 'Lean norm_LFunction_shifted_le (generic in the value): a real V below the convexity bound I1 at W, Re W = 1/100, '
                      'is at most 600000 C_tau D ^ ( 397/800 ) log D ( 1 + | Im W - Im S | ) ^ 2 when N ( | Im S | + 2 ) <_ D.')
    a = ante('z6lshift'); f = unpack(w, a); st = mkst(w, a)
    IW = '( Im ` W )'; IS = '( Im ` S )'; RW = '( Re ` W )'
    t = '( abs ` %s )' % IW; aa = '( abs ` %s )' % IS; u = '( abs ` ( %s - %s ) )' % (IW, IS)
    A_ = '( N x. ( %s + 2 ) )' % t; B_ = '( N x. ( %s + 3 ) )' % t
    IFE = 'if ( 1 <_ %s , 0 , ( ( 1 - %s ) / 2 ) )' % (RW, RW)
    PI = '( %s ^c %s )' % (A_, IFE); PIe = '( %s ^c %s )' % (A_, E)
    G = '( log ` %s )' % B_; I = '( 1 / ( abs ` ( W - 1 ) ) )'
    O = OMG(); D1 = '( D ^c %s )' % R8; Pd = '( D ^c %s )' % E; L = '( log ` D )'
    nn = f['N e. NN']; sc = f['S e. CC']; wc = f['W e. CC']; dr = f['D e. RR']; d1 = f['1 < D']
    iwc = st([st([wc, w.inst('imcl')], 'syl', '%s e. RR' % IW)], 'recnd', '%s e. CC' % IW)
    isc = st([st([sc, w.inst('imcl')], 'syl', '%s e. RR' % IS)], 'recnd', '%s e. CC' % IS)
    dfc = st([iwc, isc], 'subcld', '( %s - %s ) e. CC' % (IW, IS))
    for x, cc_ in ((t, iwc), (aa, isc), (u, dfc)):
        f['%s e. RR' % x] = st([cc_, w.inst('abscl')], 'syl', '%s e. RR' % x)
        f['0 <_ %s' % x] = st([cc_, w.inst('absge0')], 'syl', '0 <_ %s' % x)
    f['( %s - %s ) <_ %s' % (t, aa, u)] = st([iwc, isc, w.inst('abs2dif')], 'syl2anc', '( %s - %s ) <_ %s' % (t, aa, u))
    n0 = st([st([nn], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    f['D e. RR+'] = drp
    f['1 <_ D'] = lin.linarith(w, a, [d1], '1 <_ D', leaves={'D': ('RR', dr)})
    s1, c1 = apply(w, a, 'z6els1', {'T': t, 'A': aa, 'U': u}, f)
    conjs(w, a, s1, c1, f)
    cl = Closure(w, a, {'N': [('NN', nn), ('ge0', n0)], 'D': ('RR+', drp), t: [('RR', f['%s e. RR' % t]), ('ge0', f['0 <_ %s' % t])]})
    cl.atom(t)
    cl.have('( %s + 3 )' % t, 'ge1', lin.linarith(w, a, [f['0 <_ %s' % t]], '1 <_ ( %s + 3 )' % t, closure=cl))
    f['%s e. RR' % A_] = cl.mem(A_, 'RR'); f['0 <_ %s' % A_] = cl.ge0(A_)
    f['%s e. RR+' % B_] = cl.mem(B_, 'RR+')
    s3, c3 = apply(w, a, 'z6els3', {'A': A_, 'U': u}, f); conjs(w, a, s3, c3, f)
    s2, c2 = apply(w, a, 'z6els2', {'B': B_, 'U': u}, f); conjs(w, a, s2, c2, f)
    s4, c4 = apply(w, a, 'z6els4', {}, f); conjs(w, a, s4, c4, f)
    f['N <_ D'] = lin_nd(w, a, f, n0)
    om, _ = apply(w, a, 'z6omgd', {}, f)
    f['%s <_ ( CTau x. %s )' % (O, D1)] = om
    # G >_ 0, the reals
    f['%s e. RR' % G] = st([f['%s e. RR+' % B_]], 'relogcld', '%s e. RR' % G)
    f['0 <_ %s' % G] = st([cl.mem(B_, 'RR'), cl.prove(B_, 'ge1'), w.inst('logge0')], 'syl2anc', '0 <_ %s' % G)
    ere = c_(w, a, num.real(w, E), '%s e. RR' % E)
    f['%s e. RR' % PIe] = st([f['%s e. RR' % A_], f['0 <_ %s' % A_], ere], 'recxpcld', '%s e. RR' % PIe)
    f['0 <_ %s' % PIe] = st([f['%s e. RR' % A_], f['0 <_ %s' % A_], ere], 'cxpge0d', '0 <_ %s' % PIe)
    one_c = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    wm1 = st([wc, one_c], 'subcld', '( W - 1 ) e. CC')
    awp = st([wm1, st([wc, one_c, w1ne(w, a, f)], 'subne0d', '( W - 1 ) =/= 0'), w.inst('absrpcl')], 'syl2anc', '( abs ` ( W - 1 ) ) e. RR+')
    f['%s e. RR' % I] = st([awp], 'rprecred', '%s e. RR' % I)
    f['0 <_ %s' % I] = st([st([awp], 'rpreccld', '%s e. RR+' % I)], 'rpge0d', '0 <_ %s' % I)
    pf = st([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin')
    hc = st([pf, w.inst('hashcl')], 'syl', '( # ` { p e. Prime | p || N } ) e. NN0')
    two = c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')
    f['%s e. RR' % O] = st([two, hc], 'reexpcld', '%s e. RR' % O)
    f['0 <_ %s' % O] = st([two, c_(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2'), hc], 'expge0d', '0 <_ %s' % O)
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    ctre = w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
                w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('reexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR')],
               'eqeltri', 'CTau e. RR')
    f['CTau e. RR'] = c_(w, a, ctre, 'CTau e. RR')
    d0 = st([drp], 'rpge0d', '0 <_ D')
    f['%s e. RR' % D1] = st([dr, d0, c_(w, a, num.real(w, R8), '%s e. RR' % R8)], 'recxpcld', '%s e. RR' % D1)
    f['%s e. RR' % Pd] = st([dr, d0, ere], 'recxpcld', '%s e. RR' % Pd)
    f['%s e. RR' % L] = st([drp], 'relogcld', '%s e. RR' % L)
    # V <_ CVXB ( W ) at the exponent 99/200
    ife = f['%s = %s' % (IFE, E)]
    k1 = st([st([ife], 'oveq2d', '%s = %s' % (PI, PIe))], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (PI, G, PIe, G))
    k2 = st([k1], 'oveq1d', '( ( %s x. %s ) + %s ) = ( ( %s x. %s ) + %s )' % (PI, G, I, PIe, G, I))
    k3 = st([k2], 'oveq2d', '%s = ( ( %s x. %s ) x. ( ( %s x. %s ) + %s ) )' % (CVXB('W'), C2, O, PIe, G, I))
    VB = 'V <_ ( ( %s x. %s ) x. ( ( %s x. %s ) + %s ) )' % (C2, O, PIe, G, I)
    f[VB] = st([f['V <_ %s' % CVXB('W')], k3], 'breqtrd', VB)
    s5, c5 = apply(w, a, 'z6els5', {'O': O, 'C': 'CTau', 'F': D1, 'P': PIe, 'G': G, 'I': I, 'H': Pd, 'L': L, 'U': u}, f)
    # D ^ ( 1/800 ) D ^ ( 99/200 ) = D ^ ( 397/800 )
    D397 = '( D ^c ( ; ; 3 9 7 / ; ; 8 0 0 ) )'
    ad = st([st([st([dr], 'recnd', 'D e. CC'), st([drp], 'rpne0d', 'D =/= 0')], 'jca', '( D e. CC /\\ D =/= 0 )'),
             c_(w, a, num.cc(w, R8), '%s e. CC' % R8), c_(w, a, num.cc(w, E), '%s e. CC' % E), w.inst('cxpadd')], 'syl3anc',
            '( D ^c ( %s + %s ) ) = ( %s x. %s )' % (R8, E, D1, Pd))
    ex = lin.lineq(w, a, '( %s + %s )' % (R8, E), '( ; ; 3 9 7 / ; ; 8 0 0 )', leaves={})
    ad2 = st([ex], 'oveq2d', '( D ^c ( %s + %s ) ) = %s' % (R8, E, D397))
    ad3 = st([ad2, ad], 'eqtr3d', '%s = ( %s x. %s )' % (D397, D1, Pd))
    U2 = '( ( 1 + %s ) ^ 2 )' % u
    r1 = st([ad3], 'oveq2d', '( ( %s x. CTau ) x. %s ) = ( ( %s x. CTau ) x. ( %s x. %s ) )' % (C6, D397, C6, D1, Pd))
    r2 = st([r1], 'oveq1d', '( ( ( %s x. CTau ) x. %s ) x. %s ) = ( ( ( %s x. CTau ) x. ( %s x. %s ) ) x. %s )' % (C6, D397, L, C6, D1, Pd, L))
    r3 = st([r2], 'oveq1d', '( %s x. %s ) = ( ( ( ( %s x. CTau ) x. ( %s x. %s ) ) x. %s ) x. %s )' % (KPT, U2, C6, D1, Pd, L, U2))
    w.qed([s5, r3], 'breqtrrd', STATEMENTS['z6lshift'])
    return w


def lin_nd(w, a, f, n0):
    """( a -> N <_ D ) from N ( | Im S | + 2 ) <_ D"""
    aa = '( abs ` ( Im ` S ) )'
    nre = w.s([f['N e. NN']], 'nnred', '( %s -> N e. RR )' % a)
    na0 = w.s([nre, f['%s e. RR' % aa], n0, f['0 <_ %s' % aa]], 'mulge0d', '( %s -> 0 <_ ( N x. %s ) )' % (a, aa))
    cl = Closure(w, a, {'N': [('NN', f['N e. NN']), ('ge0', n0)], 'D': ('RR', f['D e. RR']), aa: [('RR', f['%s e. RR' % aa]), ('ge0', f['0 <_ %s' % aa])]})
    cl.atom(aa)
    return lin.linarith(w, a, [f[HDN], na0, n0], 'N <_ D', closure=cl, products=True)


def w1ne(w, a, f):
    """( a -> W =/= 1 ): Re W = 1/100 < 1 = Re 1"""
    RW = '( Re ` W )'
    rew = f['%s = ( 1 / ; ; 1 0 0 )' % RW]
    rw = w.s([f['W e. CC'], w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (a, RW))
    rlt = lin.linarith(w, a, [rew], '%s < 1' % RW, leaves={RW: ('RR', rw)}, atoms=[RW])
    rne = w.s([rw, rlt], 'ltned', '( %s -> %s =/= 1 )' % (a, RW))
    fv = w.s([w.s([], 'fveq2', '( W = 1 -> ( Re ` W ) = ( Re ` 1 ) )'), w.s([], 're1', '( Re ` 1 ) = 1')], 'eqtrdi', '( W = 1 -> ( Re ` W ) = 1 )')
    nf = w.s([fv], 'necon3i', '( ( Re ` W ) =/= 1 -> W =/= 1 )')
    return w.s([rne, nf], 'syl', '( %s -> W =/= 1 )' % a)


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        run(w)
