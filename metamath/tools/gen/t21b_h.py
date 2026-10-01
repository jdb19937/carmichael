"""Sortie T21b: shared step helpers (zero sums, the explicit-formula error)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *
import t21alib as _t21a


def rp_of(w, ante, xr, lo, x, lit='0'):
    """( ante -> x e. RR+ ) from xr : x e. RR, lo : lit < x or 1 <_ x style fact giving 0 < x"""
    pos = lin.linarith(w, ante, [lo], '0 < %s' % x, leaves={x: xr})
    return w.s([xr, pos], 'elrpd', '( %s -> %s e. RR+ )' % (ante, x))


def sc_terms(w, ante, n, x, nn, xb, tr, yr, a=HALF):
    """steps for the zero sum SC(( n DChrLF x ), T, Y) at abscissa a (1/2):
    returns (fin, term_cc) where term_cc proves ( ( ante /\\ q e. ZF ) -> term e. CC )"""
    E_ = '( %s DChrLF %s )' % (n, x)
    Z = ZF(E_, a, 'T')
    ar = w.s([num.real(w, a)], 'a1i', '( %s -> %s e. RR )' % (ante, a))
    a0 = w.s([], 'halfgt0', '0 < %s' % a) if a == HALF else None
    a0 = w.s([a0], 'a1i', '( %s -> 0 < %s )' % (ante, a))
    a1 = w.s([w.s([], 'halflt1', '%s < 1' % a)], 'a1i', '( %s -> %s < 1 )' % (ante, a))
    a1 = w.s([a1], 'ltled', '( %s -> %s <_ 1 )' % (ante, a)) if False else lin.linarith(w, ante, [a1], '%s <_ 1' % a, leaves={a: ar})
    ez = ap(w, ante, [nn, xb, ar, a0, a1, tr], 'ezf', '( %s e. Fin /\\ A. q e. %s ( %s holord q ) e. NN )' % (Z, Z, E_))
    fin = w.s([ez], 'simpld', '( %s -> %s e. Fin )' % (ante, Z))
    C2 = '( %s /\\ q e. %s )' % (ante, Z)
    s2 = S_(w, C2)
    qin = s2([], 'simpr', 'q e. %s' % Z)
    ordn = s2([lift(w, w.s([ez], 'simprd', '( %s -> A. q e. %s ( %s holord q ) e. NN )' % (ante, Z, E_)), C2), qin,
               w.s([], 'rsp', '( A. q e. %s ( %s holord q ) e. NN -> ( q e. %s -> ( %s holord q ) e. NN ) )' % (Z, E_, Z, E_))], 'sylc', '( %s holord q ) e. NN' % E_)
    qf = _t21a.q_facts(w, C2, qin, lift(w, ar, C2), lift(w, tr, C2), a, 'T', E_)
    q0 = lin.linarith(w, C2, [qf['lo'], lift(w, a0, C2)], '0 < ( Re ` q )', leaves={'( Re ` q )': qf['re'], a: lift(w, ar, C2)})
    Cz = '( %s /\\ q = 0 )' % C2
    rz = w.s([w.s([w.s([], 'simpr', '( %s -> q = 0 )' % Cz)], 'fveq2d', '( %s -> ( Re ` q ) = ( Re ` 0 ) )' % Cz), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % Cz)],
             'eqtrd', '( %s -> ( Re ` q ) = 0 )' % Cz)
    rn = w.s([lift(w, s2([q0], 'gt0ne0d', '( Re ` q ) =/= 0'), Cz)], 'neneqd', '( %s -> -. ( Re ` q ) = 0 )' % Cz)
    qn0 = s2([s2([rz, rn], 'pm2.65da', '-. q = 0')], 'neqned', 'q =/= 0')
    yc = lift(w, w.s([yr], 'recnd', '( %s -> Y e. CC )' % ante), C2)
    yq = s2([s2([yc, qf['qc']], 'cxpcld', '( Y ^c q ) e. CC'), qf['qc'], qn0], 'divcld', '( ( Y ^c q ) / q ) e. CC')
    tc = s2([s2([ordn], 'nncnd', '( %s holord q ) e. CC' % E_), yq], 'mulcld', '( ( %s holord q ) x. ( ( Y ^c q ) / q ) ) e. CC' % E_)
    return fin, tc, dict(C2=C2, qf=qf, ordn=ordn, qn0=qn0, q0=q0, Z=Z, E=E_)


def sc_cc(w, ante, n, x, nn, xb, tr, yr):
    fin, tc, _ = sc_terms(w, ante, n, x, nn, xb, tr, yr)
    E_ = '( %s DChrLF %s )' % (n, x)
    return w.s([fin, tc], 'fsumcl', '( %s -> %s e. CC )' % (ante, SC(E_, 'T', 'Y')))


def eferr_parts(w, ante, n, nr, n1, yr, y1, tr, t2, T='T'):
    """reals and signs of EFERR(n,T,Y): nr : n e. RR, n1 : 1 <_ n, y1 : 1 <_ Y, t2 : 2 <_ T"""
    s = S_(w, ante)
    yp = rp_of(w, ante, yr, y1, 'Y'); tp = s([tr, lin.linarith(w, ante, [t2], '0 < %s' % T, leaves={T: tr})], 'elrpd', '%s e. RR+' % T); np_ = rp_of(w, ante, nr, n1, n)
    T2 = '( %s + 2 )' % T
    t2r = s([tr, s([], '2re', '2 e. RR') if False else s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % T2)
    t2p = rp_of(w, ante, t2r, lin.linarith(w, ante, [t2], '0 <_ %s' % T2, leaves={'T': tr}), T2) if False else s([tp, s([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')], 'rpaddcld', '%s e. RR+' % T2)
    NT = '( %s x. %s )' % (n, T)
    NTY = '( %s x. Y )' % NT
    ntp = s([np_, tp], 'rpmulcld', '%s e. RR+' % NT)
    ntyp = s([ntp, yp], 'rpmulcld', '%s e. RR+' % NTY)
    N2 = '( %s x. %s )' % (n, T2)
    n2p = s([np_, t2p], 'rpmulcld', '%s e. RR+' % N2)
    L1 = '( log ` %s )' % NTY
    L2 = '( log ` %s )' % N2
    l1r = s([ntyp], 'relogcld', '%s e. RR' % L1)
    l2r = s([n2p], 'relogcld', '%s e. RR' % L2)
    # 1 <_ n T y, 1 <_ n ( T + 2 )
    ntr = s([ntp], 'rpred', '%s e. RR' % NT); ntyr = s([ntyp], 'rpred', '%s e. RR' % NTY); n2r = s([n2p], 'rpred', '%s e. RR' % N2)
    nt1 = s([s([], '1red', '1 e. RR') if False else w.s([], '1red', '( %s -> 1 e. RR )' % ante), nr, s([w.s([], '1red', '( %s -> 1 e. RR )' % ante), n1], 'x', 'x') if False else None], 'x', 'x') if False else None
    one = w.s([], '1red', '( %s -> 1 e. RR )' % ante)
    t1 = lin.linarith(w, ante, [t2], '1 <_ %s' % T, leaves={T: tr})
    z1 = s([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    nt_1 = s([one, nr, one, tr, z1, z1, n1, t1], 'lemul12ad', '( 1 x. 1 ) <_ %s' % NT)
    nt_1 = s([s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), nt_1], 'eqbrtrrd', '1 <_ %s' % NT)
    nty1 = s([one, ntr, one, yr, z1, z1, nt_1, y1], 'lemul12ad', '( 1 x. 1 ) <_ %s' % NTY)
    nty1 = s([s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), nty1], 'eqbrtrrd', '1 <_ %s' % NTY)
    t21 = lin.linarith(w, ante, [t2], '1 <_ %s' % T2, leaves={T: tr})
    n21 = s([one, nr, one, t2r, z1, z1, n1, t21], 'lemul12ad', '( 1 x. 1 ) <_ %s' % N2)
    n21 = s([s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), n21], 'eqbrtrrd', '1 <_ %s' % N2)
    l10 = ap(w, ante, [ntyr, nty1], 'logge0', '0 <_ %s' % L1)
    l20 = ap(w, ante, [n2r, n21], 'logge0', '0 <_ %s' % L2)
    Y58 = '( Y ^c ( 5 / 8 ) )'
    y58 = s([yp, s([num.real(w, '( 5 / 8 )')], 'a1i', '( 5 / 8 ) e. RR')], 'rpcxpcld', '%s e. RR+' % Y58)
    A1 = '( ( Y x. ( %s ^ 2 ) ) / %s )' % (L1, T)
    A2 = '( %s x. ( %s ^ 2 ) )' % (Y58, L2)
    A3 = '( %s ^ 2 )' % L1
    l1s = s([l1r], 'resqcld', '%s e. RR' % A3); l2s = s([l2r], 'resqcld', '( %s ^ 2 ) e. RR' % L2)
    a1r = s([s([yr, l1s], 'remulcld', '( Y x. %s ) e. RR' % A3), tp], 'rerpdivcld', '%s e. RR' % A1)
    a2r = s([s([y58], 'rpred', '%s e. RR' % Y58), l2s], 'remulcld', '%s e. RR' % A2)
    inner = '( ( %s + %s ) + %s )' % (A1, A2, A3)
    ir = s([s([a1r, a2r], 'readdcld', '( %s + %s ) e. RR' % (A1, A2)), l1s], 'readdcld', '%s e. RR' % inner)
    c12 = s([num.real(w, C12)], 'a1i', '%s e. RR' % C12)
    er = s([c12, ir], 'remulcld', '%s e. RR' % EFERR(n, T, 'Y'))
    return dict(er=er, l1r=l1r, l2r=l2r, l10=l10, l20=l20, ntyp=ntyp, n2p=n2p, yp=yp, tp=tp, y58=y58, t2p=t2p, t2r=t2r,
                a1r=a1r, a2r=a2r, l1s=l1s, l2s=l2s, ir=ir, c12=c12, L1=L1, L2=L2, NTY=NTY, N2=N2, NT=NT, ntp=ntp, one=one)
