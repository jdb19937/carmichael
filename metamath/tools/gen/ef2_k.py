"""Sortie EF2: Lean logDeriv_split on the square (ef2lds): with zdfac's cofactor h, F'/F = sum_k m_k / ( z - k ) + h'/h
off the zeros of the 13/8 square (C10 holzlogdvlem at o := ( m e. Z |-> ( F holord m ) ), by vtocl)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import zc1_h
patch(zc1_h)
from zc1_h import geo_data
import c9_h
patch(c9_h)
from c9_h import c0_facts
import lin
lin.FASTPATH = True

C0_ = CT('T')
QA_, QB_ = SQA(C0_, R138), SQB(C0_, R138)
Q_ = SQ(C0_, R138)
Z_ = ZS('F', 'T')
HB = tsub(ante_of(stmt('zdfac'))[1], {})[len('E. h '):]
OM = '( m e. %s |-> ( F holord m ) )' % Z_
S['ef2lds'] = ('( ( %s /\\ T e. RR ) /\\ %s ) -> A. z e. ( %s \\ %s ) ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = '
               '( sum_ k e. %s ( ( F holord k ) / ( z - k ) ) + ( ( ( CC _D h ) ` z ) / ( h ` z ) ) )') % (DD(), HB, Q_, Z_, Z_)
S['ef2lds'] = '( ' + S['ef2lds'] + ' )'


def gen_lds():
    w = W('ef2lds', 'Lean ` logDeriv_split ` on the square: with the cofactor ` h ` of ~ zdfac , ` F-prime / F = sum_k m_k / ( z - k ) + h-prime / h ` at the non-zeros of the ` 13 / 8 ` square about ` 2 + i T ` ( C10 ~ holzlogdvlem at the orders ` F holord k ` ).')
    A0, GC = ante_of(S['ef2lds'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dt = s([], 'simpl', '( %s /\\ T e. RR )' % DD()); hb = s([], 'simpr', HB)
    dd = s([dt, w.inst('simpl')], 'syl', DD()); tr = s([dt, w.inst('simpr')], 'syl', 'T e. RR')
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    c0, re0, im0 = c0_facts(w, A0, tr)
    cin, a, b, geo, nest = geo_data(w, A0, c0, re0, im0, R138, '( 1 / 8 )', R74)
    B1, B2, B3 = top_and(HB)
    hh = s([hb, w.inst('simp1')], 'syl', B1); fac = s([hb, w.inst('simp2')], 'syl', B2); nzq = s([hb, w.inst('simp3')], 'syl', B3)
    fc0 = s([dt, w.inst('ef2cnz')], 'syl', '( F ` %s ) =/= 0' % C0_)
    EXW = 'E. w e. %s ( F ` w ) =/= 0' % Q_
    sub = w.s([w.s([], 'fveq2', '( w = %s -> ( F ` w ) = ( F ` %s ) )' % (C0_, C0_))], 'neeq1d', '( w = %s -> ( ( F ` w ) =/= 0 <-> ( F ` %s ) =/= 0 ) )' % (C0_, C0_))
    exw = s([cin, fc0, w.s([sub], 'rspcev', '( ( %s e. %s /\\ ( F ` %s ) =/= 0 ) -> %s )' % (C0_, Q_, C0_, EXW))], 'syl2anc', EXW)
    # the order map
    zc = tsub(ante_of(S['ef2zs'])[1], {})
    zs = s([dt, w.inst('ef2zs')], 'syl', zc)
    alln = s([zs, w.inst('simp2')], 'syl', top_and(zc)[1])
    Am = '( %s /\\ m e. %s )' % (A0, Z_)
    subq = w.s([w.s([], 'oveq2', '( q = m -> ( F holord q ) = ( F holord m ) )')], 'eleq1d', '( q = m -> ( ( F holord q ) e. NN <-> ( F holord m ) e. NN ) )')
    mn = w.s([subq, up(w, alln, Am), w.s([], 'simpr', '( %s -> m e. %s )' % (Am, Z_))], 'rspcdva', '( %s -> ( F holord m ) e. NN )' % Am)
    omf = s([mn], 'fmptd', '%s : %s --> NN' % (OM, Z_))
    # closed rewriting of the exponents: ( OM ` k ) = ( F holord k ) for k in Z
    em = w.s([w.s([], 'oveq2', '( m = k -> ( F holord m ) = ( F holord k ) )')], 'cbvmptv', '%s = ( k e. %s |-> ( F holord k ) )' % (OM, Z_))
    c1 = w.s([w.s([em], 'fvmpt2', '( ( k e. %s /\\ ( F holord k ) e. _V ) -> ( %s ` k ) = ( F holord k ) )' % (Z_, OM)), w.s([], 'ovex', '( F holord k ) e. _V')], 'mpan2',
             '( k e. %s -> ( %s ` k ) = ( F holord k ) )' % (Z_, OM))
    PQ = 'prod_ q e. %s ( ( z - q ) ^ ( F holord q ) )' % Z_
    PKh = 'prod_ k e. %s ( ( z - k ) ^ ( F holord k ) )' % Z_
    PKo = 'prod_ k e. %s ( ( z - k ) ^ ( %s ` k ) )' % (Z_, OM)
    idqk = w.s([], 'id', '( q = k -> q = k )')
    cq, _ = w.congr('( ( z - q ) ^ ( F holord q ) )', {'q': 'k'}, 'q = k', {'q': idqk})
    p1 = w.s([cq], 'cbvprodv', '%s = %s' % (PQ, PKh))
    p2 = w.s([w.s([w.s([c1], 'eqcomd', '( k e. %s -> ( F holord k ) = ( %s ` k ) )' % (Z_, OM))], 'oveq2d', '( k e. %s -> ( ( z - k ) ^ ( F holord k ) ) = ( ( z - k ) ^ ( %s ` k ) ) )' % (Z_, OM))],
             'prodeq2i', '%s = %s' % (PKh, PKo))
    p3 = w.s([w.s([w.s([p1, p2], 'eqtri', '%s = %s' % (PQ, PKo))], 'oveq1i', '( %s x. ( h ` z ) ) = ( %s x. ( h ` z ) )' % (PQ, PKo))], 'eqeq2i',
             '( ( F ` z ) = ( %s x. ( h ` z ) ) <-> ( F ` z ) = ( %s x. ( h ` z ) ) )' % (PQ, PKo))
    FACo = 'A. z e. %s ( F ` z ) = ( %s x. ( h ` z ) )' % (HP0, PKo)
    p4 = w.s([p3], 'ralbii', '( %s <-> %s )' % (B2, FACo))
    faco = s([fac, p4], 'sylib', FACo)
    # holzlogdvlem at o, then at OM
    HZo = tsub(stmt('holzlogdvlem'), {'A': QA_, 'B': QB_, 'R': '( 1 / 8 )', 'D': HP0, 'q': 'k'})
    HZm = tsub(HZo, {'o': OM})
    hzo = w.s([], 'holzlogdvlem', HZo)
    ido = w.s([], 'id', '( o = %s -> o = %s )' % (OM, OM))
    co, _ = w.wcongr(HZo, {'o': OM}, 'o = %s' % OM, {'o': ido})
    omx = w.s([w.s([w.s([], 'ovex', '%s e. _V' % Q_)], 'rabex', '%s e. _V' % Z_)], 'mptex', '%s e. _V' % OM)
    hzm = w.s([omx, co, hzo], 'vtocl', HZm)
    ha, hc = ante_of(HZm)
    have = {HOLF('F', HP0): hol, '( %s e. CC /\\ %s e. CC )' % (QA_, QB_): s([a, b], 'jca', '( %s e. CC /\\ %s e. CC )' % (QA_, QB_)), body_of(w, geo): geo,
            body_of(w, nest): nest, EXW: exw, '%s : %s --> NN' % (OM, Z_): omf, B1: hh, FACo: faco, B3: nzq}
    lds = s([conj(w, A0, ha, have), hzm], 'syl', hc)
    # back to the orders
    SO = 'sum_ k e. %s ( ( %s ` k ) / ( z - k ) )' % (Z_, OM)
    SH = 'sum_ k e. %s ( ( F holord k ) / ( z - k ) )' % Z_
    HH = '( ( ( CC _D h ) ` z ) / ( h ` z ) )'
    q1 = w.s([w.s([c1], 'oveq1d', '( k e. %s -> ( ( %s ` k ) / ( z - k ) ) = ( ( F holord k ) / ( z - k ) ) )' % (Z_, OM))], 'sumeq2i', '%s = %s' % (SO, SH))
    q2 = w.s([w.s([q1], 'oveq1i', '( %s + %s ) = ( %s + %s )' % (SO, HH, SH, HH))], 'eqeq2i',
             '( ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( %s + %s ) <-> ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( %s + %s ) )' % (SO, HH, SH, HH))
    q3 = w.s([q2], 'ralbii', '( %s <-> %s )' % (hc, GC))
    w.qed([lds, q3], 'sylib', S['ef2lds'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2lds']:
        {'ef2lds': gen_lds}[g]()
