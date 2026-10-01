"""Sortie T21a: zero-set helpers (t21zfel: membership of ZF(F,A,T); t21zfss: monotonicity)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W
from t21alib import run

C1 = '( A + ( _i x. -u T ) )'
C2 = '( 1 + ( _i x. T ) )'
BX = '( %s crect %s )' % (C1, C2)
PH = '( Q =/= 1 /\\ ( F ` Q ) = 0 )'
RE, IM = '( Re ` Q )', '( Im ` Q )'


def gen_zfel():
    w = W('t21zfel', 'Membership in the zero set ` ZF ( F , A , T ) ` of the box ` [ A , 1 ] x. [ - T , T ] ` (Lean ` mem_zeroFinset ` ; ~ elcrect ).')
    A0 = '( A e. RR /\\ T e. RR )'
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ar = st([], 'simpl', 'A e. RR'); tr = st([], 'simpr', 'T e. RR')
    tn = st([tr], 'renegcld', '-u T e. RR')
    # the substitution instance of elrab
    sb = w.s([w.s([], 'neeq1', '( r = Q -> ( r =/= 1 <-> Q =/= 1 ) )'),
              w.s([w.s([], 'fveq2', '( r = Q -> ( F ` r ) = ( F ` Q ) )')], 'eqeq1d', '( r = Q -> ( ( F ` r ) = 0 <-> ( F ` Q ) = 0 ) )')],
             'anbi12d', '( r = Q -> ( ( r =/= 1 /\\ ( F ` r ) = 0 ) <-> %s ) )' % PH)
    ZFT = ZF('F', 'A', 'T')
    e1 = st([w.s([sb], 'elrab', '( Q e. %s <-> ( Q e. %s /\\ %s ) )' % (ZFT, BX, PH))], 'a1i', '( Q e. %s <-> ( Q e. %s /\\ %s ) )' % (ZFT, BX, PH))
    c1 = st([st([ar], 'recnd', 'A e. CC'), st([st([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), st([tn], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % C1)
    c2 = st([st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), st([st([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), st([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % C2)
    RI = '( ( Re ` %s ) [,] ( Re ` %s ) )' % (C1, C2)
    II = '( ( Im ` %s ) [,] ( Im ` %s ) )' % (C1, C2)
    e2 = ap_(w, A0, [c1, c2], 'elcrect', '( Q e. %s <-> ( Q e. CC /\\ %s e. %s /\\ %s e. %s ) )' % (BX, RE, RI, IM, II))
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    r1 = st([ar, tn], 'crred', '( Re ` %s ) = A' % C1); r2 = st([one, tr], 'crred', '( Re ` %s ) = 1' % C2)
    i1 = st([ar, tn], 'crimd', '( Im ` %s ) = -u T' % C1); i2 = st([one, tr], 'crimd', '( Im ` %s ) = T' % C2)
    ri = st([r1, r2], 'oveq12d', '%s = ( A [,] 1 )' % RI); ii = st([i1, i2], 'oveq12d', '%s = ( -u T [,] T )' % II)
    # under Q e. CC
    A1 = '( %s /\\ Q e. CC )' % A0
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    qc = s1([], 'simpr', 'Q e. CC')
    rq = s1([qc], 'recld', '%s e. RR' % RE); iq = s1([qc], 'imcld', '%s e. RR' % IM)
    L = lambda s_: _cl.lift(w, s_, A1)
    x = lambda s_, t_: s1([s_], 'rexrd', '%s e. RR*' % t_)
    ra = ap_(w, A1, [x(L(ar), 'A'), x(L(one), '1'), x(rq, RE)], 'elicc4', '( %s e. ( A [,] 1 ) <-> ( A <_ %s /\\ %s <_ 1 ) )' % (RE, RE, RE))
    ia = ap_(w, A1, [x(L(tn), '-u T'), x(L(tr), 'T'), x(iq, IM)], 'elicc4', '( %s e. ( -u T [,] T ) <-> ( -u T <_ %s /\\ %s <_ T ) )' % (IM, IM, IM))
    ab = s1([iq, L(tr)], 'absled', '( ( abs ` %s ) <_ T <-> ( -u T <_ %s /\\ %s <_ T ) )' % (IM, IM, IM))
    ia2 = s1([ia, ab], 'bitr4d', '( %s e. ( -u T [,] T ) <-> ( abs ` %s ) <_ T )' % (IM, IM))
    re2 = s1([L(ri)], 'eleq2d', '( %s e. %s <-> %s e. ( A [,] 1 ) )' % (RE, RI, RE))
    im2 = s1([L(ii)], 'eleq2d', '( %s e. %s <-> %s e. ( -u T [,] T ) )' % (IM, II, IM))
    RR_ = '( ( A <_ %s /\\ %s <_ 1 ) /\\ ( abs ` %s ) <_ T )' % (RE, RE, IM)
    both = s1([s1([re2, ra], 'bitrd', '( %s e. %s <-> ( A <_ %s /\\ %s <_ 1 ) )' % (RE, RI, RE, RE)),
               s1([im2, ia2], 'bitrd', '( %s e. %s <-> ( abs ` %s ) <_ T )' % (IM, II, IM))], 'anbi12d',
              '( ( %s e. %s /\\ %s e. %s ) <-> %s )' % (RE, RI, IM, II, RR_))
    p = w.s([both], 'pm5.32da', '( %s -> ( ( Q e. CC /\\ ( %s e. %s /\\ %s e. %s ) ) <-> ( Q e. CC /\\ %s ) ) )' % (A0, RE, RI, IM, II, RR_))
    t3 = st([w.s([], '3anass', '( ( Q e. CC /\\ %s e. %s /\\ %s e. %s ) <-> ( Q e. CC /\\ ( %s e. %s /\\ %s e. %s ) ) )' % (RE, RI, IM, II, RE, RI, IM, II))], 'a1i',
            '( ( Q e. CC /\\ %s e. %s /\\ %s e. %s ) <-> ( Q e. CC /\\ ( %s e. %s /\\ %s e. %s ) ) )' % (RE, RI, IM, II, RE, RI, IM, II))
    bx = st([st([e2, t3], 'bitrd', '( Q e. %s <-> ( Q e. CC /\\ ( %s e. %s /\\ %s e. %s ) ) )' % (BX, RE, RI, IM, II)), p], 'bitrd', '( Q e. %s <-> ( Q e. CC /\\ %s ) )' % (BX, RR_))
    e3 = st([bx], 'anbi1d', '( ( Q e. %s /\\ %s ) <-> ( ( Q e. CC /\\ %s ) /\\ %s ) )' % (BX, PH, RR_, PH))
    d3 = st([w.s([], 'df-3an', '( ( Q e. CC /\\ %s /\\ %s ) <-> ( ( Q e. CC /\\ %s ) /\\ %s ) )' % (RR_, PH, RR_, PH))], 'a1i',
            '( ( Q e. CC /\\ %s /\\ %s ) <-> ( ( Q e. CC /\\ %s ) /\\ %s ) )' % (RR_, PH, RR_, PH))
    fin = st([st([e1, e3], 'bitrd', '( Q e. %s <-> ( ( Q e. CC /\\ %s ) /\\ %s ) )' % (ZFT, RR_, PH)), d3], 'bitr4d', '( Q e. %s <-> ( Q e. CC /\\ %s /\\ %s ) )' % (ZFT, RR_, PH))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21zfel']))
    return w.run()


def zfel_inst(w, ante, a, t, qv, F, ar, tr):
    """step ( ante -> ( qv e. ZF(F,a,t) <-> ( ... ) ) ) from t21zfel"""
    m = {'A': a, 'T': t, 'Q': qv, 'F': F}
    body = S['t21zfel'].split(' -> ', 1)[1][:-2]
    f = tsub_cls(body, m)
    return ap_(w, ante, [ar, tr], 't21zfel', f)


def tsub_cls(text, m):
    """substitute class variables (single tokens) by class texts"""
    return ' '.join(m.get(tok, tok) for tok in text.split())


def gen_zfss():
    w = W('t21zfss', 'The zero set of the box ` [ B , 1 ] x. [ - U , U ] ` lies in that of ` [ A , 1 ] x. [ - T , T ] ` for ` A <_ B ` , ` U <_ T ` (Lean ` zeroFinset_subset_of_le ` , ` zeroFinset_eq_filter ` ).')
    A0 = ante_of(S['t21zfss'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    h1 = st([], 'simpl', '( A e. RR /\\ B e. RR /\\ A <_ B )'); h2 = st([], 'simpr', '( U e. RR /\\ T e. RR /\\ U <_ T )')
    ar = st([h1], 'simp1d', 'A e. RR'); br = st([h1], 'simp2d', 'B e. RR'); ab = st([h1], 'simp3d', 'A <_ B')
    ur = st([h2], 'simp1d', 'U e. RR'); tr = st([h2], 'simp2d', 'T e. RR'); ut = st([h2], 'simp3d', 'U <_ T')
    A1 = '( %s /\\ q e. %s )' % (A0, ZF('F', 'B', 'U'))
    L = lambda s_: _cl.lift(w, s_, A1)
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    e1 = zfel_inst(w, A1, 'B', 'U', 'q', 'F', L(br), L(ur))
    CND = lambda a, t: '( q e. CC /\\ ( ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) /\\ ( q =/= 1 /\\ ( F ` q ) = 0 ) )' % (a, t)
    c = s1([s1([], 'simpr', 'q e. %s' % ZF('F', 'B', 'U')), e1], 'mpbid', CND('B', 'U'))
    qc = s1([c], 'simp1d', 'q e. CC'); m = s1([c], 'simp2d', '( ( B <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ U )')
    z = s1([c], 'simp3d', '( q =/= 1 /\\ ( F ` q ) = 0 )')
    rr = s1([m], 'simpld', '( B <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )')
    rq = s1([qc], 'recld', '( Re ` q ) e. RR'); iq = s1([s1([qc], 'imcld', '( Im ` q ) e. RR')], 'recnd', '( Im ` q ) e. CC')
    aq = s1([iq], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    lo = s1([L(ar), L(br), rq, L(ab), s1([rr], 'simpld', 'B <_ ( Re ` q )')], 'letrd', 'A <_ ( Re ` q )')
    hi = s1([rr], 'simprd', '( Re ` q ) <_ 1')
    im = s1([aq, L(ur), L(tr), s1([m], 'simprd', '( abs ` ( Im ` q ) ) <_ U'), L(ut)], 'letrd', '( abs ` ( Im ` q ) ) <_ T')
    c2 = s1([qc, s1([s1([lo, hi], 'jca', '( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )'), im], 'jca', '( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T )'), z], '3jca', CND('A', 'T'))
    e2 = zfel_inst(w, A1, 'A', 'T', 'q', 'F', L(ar), L(tr))
    fin = s1([c2, e2], 'mpbird', 'q e. %s' % ZF('F', 'A', 'T'))
    imp = w.s([fin], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, ZF('F', 'B', 'U'), ZF('F', 'A', 'T')))
    w.qed([imp], 'ssrdv', S['t21zfss'])
    return w.run()

def gen_zfd():
    w = W('t21zfd', 'A zero of the difference ` ZF ( F , A , T ) \\ ZF ( F , B , T ) ` has real part below ` B ` (Lean: the filter ` A <_ Re < B ` of ` zoneSum ` ; ~ t21zfel ).')
    A0 = ante_of(S['t21zfd'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    ar, br, tr = u['A e. RR'], u['B e. RR'], u['T e. RR']
    ZA, ZB = ZF('F', 'A', 'T'), ZF('F', 'B', 'T')
    DD = '( %s \\ %s )' % (ZA, ZB)
    ed = st([u['Q e. %s' % DD], w.s([], 'eldif', '( Q e. %s <-> ( Q e. %s /\\ -. Q e. %s ) )' % (DD, ZA, ZB))], 'sylib', '( Q e. %s /\\ -. Q e. %s )' % (ZA, ZB))
    qa = st([ed], 'simpld', 'Q e. %s' % ZA); qnb = st([ed], 'simprd', '-. Q e. %s' % ZB)
    CT = lambda a: '( Q e. CC /\\ ( ( %s <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) /\\ ( abs ` ( Im ` Q ) ) <_ T ) /\\ ( Q =/= 1 /\\ ( F ` Q ) = 0 ) )' % a
    ea = ap_(w, A0, [ar, tr], 't21zfel', '( Q e. %s <-> %s )' % (ZA, CT('A')))
    ca = st([qa, ea], 'mpbid', CT('A'))
    C1 = '( %s /\\ B <_ ( Re ` Q ) )' % A0
    L = lambda s_: _cl.lift(w, s_, C1)
    ca1 = L(ca)
    m = w.s([ca1], 'simp2d', '( %s -> ( ( A <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) /\\ ( abs ` ( Im ` Q ) ) <_ T ) )' % C1)
    cb = w.s([w.s([ca1], 'simp1d', '( %s -> Q e. CC )' % C1),
              w.s([w.s([w.s([], 'simpr', '( %s -> B <_ ( Re ` Q ) )' % C1), w.s([w.s([m], 'simpld', '( %s -> ( A <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) )' % C1)], 'simprd', '( %s -> ( Re ` Q ) <_ 1 )' % C1)], 'jca',
                        '( %s -> ( B <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) )' % C1), w.s([m], 'simprd', '( %s -> ( abs ` ( Im ` Q ) ) <_ T )' % C1)], 'jca', '( %s -> ( ( B <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) /\\ ( abs ` ( Im ` Q ) ) <_ T ) )' % C1),
              w.s([ca1], 'simp3d', '( %s -> ( Q =/= 1 /\\ ( F ` Q ) = 0 ) )' % C1)], '3jca', '( %s -> %s )' % (C1, CT('B')))
    eb = ap_(w, C1, [L(br), L(tr)], 't21zfel', '( Q e. %s <-> %s )' % (ZB, CT('B')))
    qb = w.s([cb, eb], 'mpbird', '( %s -> Q e. %s )' % (C1, ZB))
    nle = st([qnb, st([w.s([qb], 'ex', '( %s -> ( B <_ ( Re ` Q ) -> Q e. %s ) )' % (A0, ZB))], 'con3d', '( -. Q e. %s -> -. B <_ ( Re ` Q ) )' % ZB)], 'mpd', '-. B <_ ( Re ` Q )')
    re = st([st([ca], 'simp1d', 'Q e. CC')], 'recld', '( Re ` Q ) e. RR')
    lt = st([nle, st([re, br], 'ltnled', '( ( Re ` Q ) < B <-> -. B <_ ( Re ` Q ) )')], 'mpbird', '( Re ` Q ) < B')
    w.qed([qa, lt], 'jca', S['t21zfd'])
    return run(w)


if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21zfel', gen_zfel), ('t21zfss', gen_zfss), ('t21zfd', gen_zfd)]:
        if not only or lab in only:
            f()
