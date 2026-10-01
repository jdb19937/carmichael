"""Sortie EF2: the DiskData instances (ef2ddl for L(s, chi) nonprincipal, ef2dde for eta, ef2ddg for gFun)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import c9_h
patch(c9_h)
from c9_h import lf_hol
from zc1_c import u1base, U1
from z4blib import fvmd
import zc1_g
patch(zc1_g)
from zc1_g import eta_hol
import lin
lin.FASTPATH = True


def allt_part(w, A0, F, A, ctr, ctrnum, rct, conv=None):
    """( A0 -> A. t e. RR DDT(t) ); ctr and rct cited at T := t"""
    At = '( %s /\\ t e. RR )' % A0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (At, f))
    tr = s([], 'simpr', 't e. RR')
    FC = '( abs ` ( %s ` %s ) )' % (F, CT('t'))
    ca, cc = ante_of(tsub(stmt(ctr), {'T': 't'}))
    c1 = w.s([], ctr, '( %s -> %s )' % (ca, cc)) if ca == At else s([tr, w.inst(ctr)], 'syl', cc)
    le14 = lin8(w, At, [], '( 1 / 4 ) <_ %s' % ctrnum, {})
    lo = le_tr(w, At, le14, '( 1 / 4 )', ctrnum, c1, FC)
    ra, rc = ante_of(tsub(stmt(rct), {'T': 't'}))
    b1 = w.s([], rct, '( %s -> %s )' % (ra, rc)) if ra == At else s([tr, w.inst(rct)], 'syl', rc)
    if conv:
        b1 = conv(w, At, b1, tr)
    body = s([lo, b1], 'jca', DDT('t', F, A))
    return w.s([body], 'ralrimiva', '( %s -> A. t e. RR %s )' % (A0, DDT('t', F, A)))


def gen_ddl():
    w = W('ef2ddl', 'Lean ` diskData_LFunction ` on squares: the Abel-summed ` L ( s , chi ) ` of a nonprincipal character mod ` N ` is ` DiskData ` with ` A = N ` ( ~ lchrhol0 , ~ lchrctr , ~ lchrrct , ~ lchragr , ~ lchrne0 ).')
    A0 = CHI
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'id', CHI)
    hol = lf_hol(w, A0, chi)
    nn = s([], 'simpll', 'N e. NN')
    ar = s([nn], 'nnred', 'N e. RR'); a1 = s([nn], 'nnge1d', '1 <_ N')
    allt = allt_part(w, A0, LFN, 'N', 'lchrctr', '( 1 / 2 )', 'lchrrct')
    Aw = '( %s /\\ w e. %s )' % (A0, HP0)
    Aw1 = '( %s /\\ 1 < ( Re ` w ) )' % Aw
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aw1, f))
    whp = s1([], 'simplr', 'w e. %s' % HP0)
    wc = s1([w.s([w.s([], 'hpss', '%s C_ CC' % HP0)], 'a1i', '( %s -> %s C_ CC )' % (Aw1, HP0)), whp], 'sseldd', 'w e. CC')
    g1 = s1([], 'simpr', '1 < ( Re ` w )')
    exs = w.s([w.s([], 'sumex', '%s e. _V' % LSs('w'))], 'a1i', '( %s -> %s e. _V )' % (Aw1, LSs('w')))
    val = fvmd(w, Aw1, v, HP0, body(v), 'w', whp, exs_of(w, Aw1, body('w')))
    DS = 'sum_ k e. NN ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u w ) )'
    chi1 = s1([], 'simpll', CHI)
    wcg = s1([wc, g1], 'jca', '( w e. CC /\\ 1 < ( Re ` w ) )')
    agr = s1([chi1, wcg, w.inst('lchragr')], 'syl2anc', '%s = %s' % (LSs('w'), DS))
    ne = s1([s1([chi1, w.inst('simpl')], 'syl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), wcg, w.inst('lchrne0')], 'syl2anc', '%s =/= 0' % DS)
    fne = s1([s1([val, agr], 'eqtrd', '( %s ` w ) = %s' % (LFN, DS)), ne], 'eqnetrd', '( %s ` w ) =/= 0' % LFN)
    NZB = '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN
    nz = w.s([w.s([fne], 'ex', '( %s -> %s )' % (Aw, NZB))], 'ralrimiva', '( %s -> A. w e. %s %s )' % (A0, HP0, NZB))
    P1, P2, P3 = top_and(DD(LFN, 'N'))
    w.qed([hol, s([ar, a1], 'jca', P2), s([allt, nz], 'jca', P3)], '3jca', S['ef2ddl'])
    return run8(w)


ETB = lambda v: 'sum_ k e. NN ( ( k mod 2 ) x. ( ( k ^c -u %s ) - ( ( k + 1 ) ^c -u %s ) ) )' % (v, v)
GFB = lambda v: '( 1 - ( 2 ^c ( 1 - %s ) ) )' % v
ZT = 'sum_ k e. NN ( k ^c -u w )'


def conv_mul1(w, At, b1, tr, B0):
    """rewrite the bound B0 = ( ; 2 5 x. ( ( abs ` t ) + 2 ) ) of b1 to ( ; 2 5 x. ( 1 x. ( ( abs ` t ) + 2 ) ) )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (At, f))
    T2 = '( ( abs ` t ) + 2 )'
    t2c = s([s([s([tr], 'recnd', 't e. CC')], 'abscld', '( abs ` t ) e. RR'), numst(w, At, '2', 'RR')], 'readdcld', '%s e. RR' % T2)
    e = s([s([t2c], 'recnd', '%s e. CC' % T2)], 'mullidd', '( 1 x. %s ) = %s' % (T2, T2))
    e2 = s([e], 'oveq2d', '( ; 2 5 x. ( 1 x. %s ) ) = ( ; 2 5 x. %s )' % (T2, T2))
    body = ante_of(w_formula(w, b1))[1]
    FX = body.split(' <_ ')[0]
    x_part = body[:body.index(' ( abs ` ')]
    new = body.replace('<_ %s' % B0, '<_ ( ; 2 5 x. ( 1 x. %s ) )' % T2)
    # A. x e. R ( abs F x ) <_ B0  ->  <_ 25 ( 1 ( abs t + 2 ) )
    Ax = '( %s /\\ x e. %s )' % (At, RCT('t'))
    pre = 'A. x e. %s ' % RCT('t')
    lx = w.s([b1], 'r19.21bi', '( %s -> %s )' % (Ax, body[len(pre):]))
    le = w.s([lx, w.s([e2], 'adantr', '( %s -> ( ; 2 5 x. ( 1 x. %s ) ) = ( ; 2 5 x. %s ) )' % (Ax, T2, T2))], 'breqtrrd',
             '( %s -> %s )' % (Ax, new[len(pre):]))
    return w.s([le], 'ralrimiva', '( %s -> %s )' % (At, new))


def w_formula(w, step):
    for l in w.lines:
        if l.startswith(step + ':'):
            return l.split(' |- ', 1)[1]
    raise KeyError(step)


def conv_le3(w, At, b1, tr):
    """A. x e. RCT(t) abs GF x <_ 3  ->  <_ ( ; 2 5 x. ( 1 x. ( ( abs ` t ) + 2 ) ) )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (At, f))
    T2 = '( ( abs ` t ) + 2 )'
    body = ante_of(w_formula(w, b1))[1]
    Ax = '( %s /\\ x e. %s )' % (At, RCT('t'))
    inner = body[len('A. x e. %s ' % RCT('t')):]
    FX = inner.split(' <_ ')[0]
    lx = w.s([b1], 'r19.21bi', '( %s -> %s )' % (Ax, inner))
    at = s([s([tr], 'recnd', 't e. CC')], 'abscld', '( abs ` t ) e. RR')
    ag = s([s([tr], 'recnd', 't e. CC')], 'absge0d', '0 <_ ( abs ` t )')
    B = '( ; 2 5 x. ( 1 x. %s ) )' % T2
    le3 = w.s([lin8(w, At, [ag], '3 <_ %s' % B, {'( abs ` t )': at})], 'adantr', '( %s -> 3 <_ %s )' % (Ax, B))
    le = le_tr(w, Ax, lx, FX, '3', le3, B)
    return w.s([le], 'ralrimiva', '( %s -> A. x e. %s %s <_ %s )' % (At, RCT('t'), FX, B))


def nz_part(w, A0, F, v, body, fne_fn):
    """( A0 -> A. w e. HP0 ( 1 < Re w -> F w =/= 0 ) ); fne_fn(w, Aw1, whp, wc, g1, val) -> step ( Aw1 -> body(w) =/= 0 )"""
    Aw = '( %s /\\ w e. %s )' % (A0, HP0)
    Aw1 = '( %s /\\ 1 < ( Re ` w ) )' % Aw
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aw1, f))
    whp = s1([], 'simplr', 'w e. %s' % HP0)
    wc = s1([w.s([w.s([], 'hpss', '%s C_ CC' % HP0)], 'a1i', '( %s -> %s C_ CC )' % (Aw1, HP0)), whp], 'sseldd', 'w e. CC')
    g1 = s1([], 'simpr', '1 < ( Re ` w )')
    val = fvmd(w, Aw1, v, HP0, body(v), 'w', whp, exs_of(w, Aw1, body('w')))
    ne = fne_fn(w, Aw1, whp, wc, g1)
    fne = s1([val, ne], 'eqnetrd', '( %s ` w ) =/= 0' % F)
    NZB = '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % F
    return w.s([w.s([fne], 'ex', '( %s -> %s )' % (Aw, NZB))], 'ralrimiva', '( %s -> A. w e. %s %s )' % (A0, HP0, NZB))


def exs_of(w, A, val):
    if val.startswith('sum_'):
        return w.s([w.s([], 'sumex', '%s e. _V' % val)], 'a1i', '( %s -> %s e. _V )' % (A, val))
    return w.s([], 'ovexd', '( %s -> %s e. _V )' % (A, val))


def eta_ne(w, A, whp, wc, g1):
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    wcg = s([wc, g1], 'jca', '( w e. CC /\\ 1 < ( Re ` w ) )')
    ez = s([wcg, w.inst('etazser')], 'syl', '%s = ( %s x. %s )' % (ETB('w'), GFB('w'), ZT))
    ga = s([numst(w, A, '1', 'CC'), s([numst(w, A, '2', 'CC'), s([numst(w, A, '1', 'CC'), wc], 'subcld', '( 1 - w ) e. CC')], 'cxpcld', '( 2 ^c ( 1 - w ) ) e. CC')], 'subcld', '%s e. CC' % GFB('w'))
    gn = s([wcg, w.inst('gfunne0')], 'syl', '%s =/= 0' % GFB('w'))
    # the zeta series: in CC (isumcl) and nonzero (lchrne0 at N = 1)
    Ak = '( %s /\\ k e. NN )' % A
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    kn = sk([], 'simpr', 'k e. NN')
    nw = w.s([w.s([wc], 'negcld', '( %s -> -u w e. CC )' % A)], 'adantr', '( %s -> -u w e. CC )' % Ak)
    kcx = sk([sk([kn], 'nncnd', 'k e. CC'), nw], 'cxpcld', '( k ^c -u w ) e. CC')
    MP = '( n e. NN |-> ( n ^c -u w ) )'
    fv = fvmd(w, Ak, 'n', 'NN', '( n ^c -u w )', 'k', kn, w.s([], 'ovexd', '( %s -> ( k ^c -u w ) e. _V )' % Ak))
    cvg = s([wc, g1, fv], 'zetacvg', 'seq 1 ( + , %s ) e. dom ~~>' % MP)
    zc = s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), fv, kcx, cvg], 'isumcl', '%s e. CC' % ZT)
    CH = '( ( 0g ` ( DChr ` 1 ) ) ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) )'
    x1 = sk([w.s([u1base(w, A)], 'adantr', '( %s -> ( 0g ` ( DChr ` 1 ) ) e. ( Base ` ( DChr ` 1 ) ) )' % Ak), sk([kn], 'nnzd', 'k e. ZZ'), w.inst('zc1x1')], 'syl2anc', '%s = 1' % CH)
    tm = sk([sk([x1], 'oveq1d', '( %s x. ( k ^c -u w ) ) = ( 1 x. ( k ^c -u w ) )' % CH), sk([kcx], 'mullidd', '( 1 x. ( k ^c -u w ) ) = ( k ^c -u w )')], 'eqtrd',
            '( %s x. ( k ^c -u w ) ) = ( k ^c -u w )' % CH)
    DS1 = 'sum_ k e. NN ( %s x. ( k ^c -u w ) )' % CH
    se = s([tm], 'sumeq2dv', '%s = %s' % (DS1, ZT))
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), u1base(w, A)], 'jca', '( 1 e. NN /\\ ( 0g ` ( DChr ` 1 ) ) e. ( Base ` ( DChr ` 1 ) ) )')
    n1 = s([nx1, wcg, w.inst('lchrne0')], 'syl2anc', '%s =/= 0' % DS1)
    zn = s([n1, s([se], 'neeq1d', '( %s =/= 0 <-> %s =/= 0 )' % (DS1, ZT))], 'mpbid', '%s =/= 0' % ZT)
    return s([ez, s([ga, gn, zc, zn], 'mulne0d', '( %s x. %s ) =/= 0' % (GFB('w'), ZT))], 'eqnetrd', '%s =/= 0' % ETB('w'))


def gf_ne(w, A, whp, wc, g1):
    return w.s([w.s([wc, g1], 'jca', '( %s -> ( w e. CC /\\ 1 < ( Re ` w ) ) )' % A), w.inst('gfunne0')], 'syl', '( %s -> %s =/= 0 )' % (A, GFB('w')))


def gen_ddeg(label, F, holf, ctr, ctrnum, rct, conv, body, fne, desc):
    w = W(label, desc)
    A0 = '1 e. RR'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    hol = holf(w, A0)
    one = s([], 'id', '1 e. RR')
    le1 = lin8(w, A0, [], '1 <_ 1', {})
    allt = allt_part(w, A0, F, '1', ctr, ctrnum, rct, conv=conv)
    nz = nz_part(w, A0, F, 'z', body, fne)
    P1, P2, P3 = top_and(DD(F, '1'))
    dd = s([hol, s([one, le1], 'jca', P2), s([allt, nz], 'jca', P3)], '3jca', DD(F, '1'))
    w.qed([w.s([], '1re', '1 e. RR'), dd], 'ax-mp', S[label])
    return run8(w)


def gen_dde():
    return gen_ddeg('ef2dde', ETA, eta_hol, 'etactr', '( 1 / 4 )', 'etarct',
                    lambda w, At, b1, tr: conv_mul1(w, At, b1, tr, '( ; 2 5 x. ( ( abs ` t ) + 2 ) )'), ETB, eta_ne,
                    'Lean ` diskData_etaFun ` on squares: the Abel-summed eta function is ` DiskData ` with ` A = 1 ` ( ~ etahol , ~ etactr , ~ etarct ; no zeros on ` Re > 1 ` by ~ etazser , ~ gfunne0 , ~ lchrne0 at the character mod 1).')


def gen_ddg():
    return gen_ddeg('ef2ddg', GF, lambda w, A0: w.s([w.s([], 'gfhol', HOLF(GF, HP0))], 'a1i', '( %s -> %s )' % (A0, HOLF(GF, HP0))), 'gfctr', '( 1 / 2 )', 'gfrct',
                    conv_le3, GFB, gf_ne,
                    'Lean ` diskData_gFun ` on squares: ` 1 - 2 ^ ( 1 - s ) ` is ` DiskData ` with ` A = 1 ` ( ~ gfhol , ~ gfctr , ~ gfrct , ~ gfunne0 ).')


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2ddl', 'ef2dde', 'ef2ddg']:
        {'ef2ddl': gen_ddl, 'ef2dde': gen_dde, 'ef2ddg': gen_ddg}[g]()
