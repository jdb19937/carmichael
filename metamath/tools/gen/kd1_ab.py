"""Sortie KD1: mass of the zeros within W of s0 (kdnear)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_near():
    w = W('kdnear', 'Lean ` KDerivDetect.sum_ord_near_s0_le ` : the zeros within ` W ` of ` s0 = ( 1 + E ) + i T ` have mass at most ` 6 + 70000000 ( W + E ) log ( N ( abs T + 2 ) ) ` (ZC1 ` sdzc ` at radius ` W + E ` about ` 1 + i T ` ; Lean ` 5 + 2400000 ( r + eta ) log ` ).')
    A0 = S['kdnear'].split(' -> sum_')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    g = s([], 'simpr', '( T e. RR /\\ E e. RR+ /\\ ( W e. RR+ /\\ ( W + E ) <_ %s ) )' % R120)
    tr = s([g], 'simp1d', 'T e. RR'); ep = s([g], 'simp2d', 'E e. RR+'); wg = s([g], 'simp3d', '( W e. RR+ /\\ ( W + E ) <_ %s )' % R120)
    wp = s([wg], 'simpld', 'W e. RR+'); we = s([wg], 'simprd', '( W + E ) <_ %s' % R120)
    er = s([ep], 'rpred', 'E e. RR')
    wep = s([wp, ep], 'rpaddcld', '( W + E ) e. RR+')
    SDZ = tsub(stmt('sdzc'), {'W': '( W + E )'})
    sa, sc = split_imp(SDZ)
    sd = s([chi, s([tr, s([wep, we], 'jca', '( ( W + E ) e. RR+ /\\ ( W + E ) <_ %s )' % R120)], 'jca', top_and(sa)[1]), w.inst('sdzc')], 'syl2anc', sc)
    N2 = '{ p e. %s | ( abs ` ( p - %s ) ) <_ ( W + E ) }' % (ZD(), ONE('T'))
    N1 = '{ p e. %s | ( abs ` ( %s - p ) ) <_ W }' % (ZD(), S0())
    SS = S0()
    # subset
    Ap = '( %s /\\ p e. %s )' % (A0, ZD())
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ap, f))
    L = lambda st: lift(w, st, Ap)
    pz = a([], 'simpr', 'p e. %s' % ZD())
    SQ13 = SQ(CT('T'), R138)
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    cq = Closure(w, Ap, {'T': ('RR', L(tr))})
    cct = a([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % Ap), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Ap), a([L(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CT('T'))
    ric = a([a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Ap), a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
            'addcld', '%s e. CC' % RI_)
    sqcc = a([a([a([cct, ric], 'subcld', '%s e. CC' % A13), a([cct, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    pc = a([sqcc, a([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Ap, ZD(), SQ13)), pz], 'sseldd', 'p e. %s' % SQ13)], 'sseldd', 'p e. CC')
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Ap)
    tcc = a([L(tr)], 'recnd', 'T e. CC'); ecc = a([L(er)], 'recnd', 'E e. CC')
    cr = Closure(w, Ap, {'p': ('CC', pc), 'T': ('CC', tcc), 'E': ('CC', ecc), '_i': ('CC', ic)})
    cr.atom('_i')
    e1 = ringeq(w, Ap, '( p - %s )' % ONE('T'), '( ( p - %s ) + E )' % SS, cr)
    tri = a([a([pc, cr.mem(SS, 'CC')], 'subcld', '( p - %s ) e. CC' % SS), ecc], 'abstrid', '( abs ` ( ( p - %s ) + E ) ) <_ ( ( abs ` ( p - %s ) ) + ( abs ` E ) )' % (SS, SS))
    t2 = a([a([a([pc, cr.mem(SS, 'CC')], 'abssubd', '( abs ` ( p - %s ) ) = ( abs ` ( %s - p ) )' % (SS, SS)), a([L(er), a([L(ep)], 'rpge0d', '0 <_ E')], 'absidd', '( abs ` E ) = E')], 'oveq12d',
               '( ( abs ` ( p - %s ) ) + ( abs ` E ) ) = ( ( abs ` ( %s - p ) ) + E )' % (SS, SS))], 'id', 'T.') if False else \
        a([a([pc, cr.mem(SS, 'CC')], 'abssubd', '( abs ` ( p - %s ) ) = ( abs ` ( %s - p ) )' % (SS, SS)), a([L(er), a([L(ep)], 'rpge0d', '0 <_ E')], 'absidd', '( abs ` E ) = E')], 'oveq12d',
          '( ( abs ` ( p - %s ) ) + ( abs ` E ) ) = ( ( abs ` ( %s - p ) ) + E )' % (SS, SS))
    t3 = a([a([a([e1], 'fveq2d', '( abs ` ( p - %s ) ) = ( abs ` ( ( p - %s ) + E ) )' % (ONE('T'), SS)), tri], 'eqbrtrd', '( abs ` ( p - %s ) ) <_ ( ( abs ` ( p - %s ) ) + ( abs ` E ) )' % (ONE('T'), SS)), t2],
           'breqtrd', '( abs ` ( p - %s ) ) <_ ( ( abs ` ( %s - p ) ) + E )' % (ONE('T'), SS))
    Ah = '( %s /\\ ( abs ` ( %s - p ) ) <_ W )' % (Ap, SS)
    h_ = w.s([], 'simpr', '( %s -> ( abs ` ( %s - p ) ) <_ W )' % (Ah, SS))
    ch = Closure(w, Ah, {'E': ('RR', lift(w, er, Ah)), 'W': ('RR', lift(w, s([wp], 'rpred', 'W e. RR'), Ah)),
                         '( abs ` ( %s - p ) )' % SS: ('RR', w.s([lift(w, a([a([cr.mem(SS, 'CC'), pc], 'subcld', '( %s - p ) e. CC' % SS)], 'abscld', '( abs ` ( %s - p ) ) e. RR' % SS), Ah)], 'id' if False else 'T.', 'T.') if False else
                                                          lift(w, a([a([cr.mem(SS, 'CC'), pc], 'subcld', '( %s - p ) e. CC' % SS)], 'abscld', '( abs ` ( %s - p ) ) e. RR' % SS), Ah)),
                         '( abs ` ( p - %s ) )' % ONE('T'): ('RR', lift(w, a([a([pc, cr.mem(ONE('T'), 'CC')], 'subcld', '( p - %s ) e. CC' % ONE('T'))], 'abscld', '( abs ` ( p - %s ) ) e. RR' % ONE('T')), Ah))})
    ch.atom('( abs ` ( %s - p ) )' % SS); ch.atom('( abs ` ( p - %s ) )' % ONE('T'))
    t4 = linarith(w, Ah, [lift(w, t3, Ah), h_], '( abs ` ( p - %s ) ) <_ ( W + E )' % ONE('T'), closure=ch)
    ss = s([w.s([t4], 'ex', '( %s -> ( ( abs ` ( %s - p ) ) <_ W -> ( abs ` ( p - %s ) ) <_ ( W + E ) ) )' % (Ap, SS, ONE('T')))], 'ss2rabdv', '%s C_ %s' % (N1, N2))
    # sum monotone
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0]); zord = s([lz], 'simp2d', top_and(lzc)[1])
    n2f = s([zfin, w.s([w.s([], 'ssrab2', '%s C_ %s' % (N2, ZD()))], 'a1i', '( %s -> %s C_ %s )' % (A0, N2, ZD()))], 'ssfid', '%s e. Fin' % N2)
    Aq = '( %s /\\ q e. %s )' % (A0, N2)
    qz = w.s([w.s([w.s([], 'ssrab2', '%s C_ %s' % (N2, ZD()))], 'a1i', '( %s -> %s C_ %s )' % (Aq, N2, ZD())), w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, N2))], 'sseldd', '( %s -> q e. %s )' % (Aq, ZD()))
    mn = w.s([qz, w.s([lift(w, zord, Aq), w.inst('rsp')], 'syl', '( %s -> ( q e. %s -> %s e. NN ) )' % (Aq, ZD(), MU()))], 'mpd', '( %s -> %s e. NN )' % (Aq, MU()))
    le = s([n2f, w.s([mn], 'nnred', '( %s -> %s e. RR )' % (Aq, MU())), w.s([w.s([mn], 'nnrpd', '( %s -> %s e. RR+ )' % (Aq, MU()))], 'rpge0d', '( %s -> 0 <_ %s )' % (Aq, MU())), ss], 'fsumless',
           'sum_ q e. %s %s <_ sum_ q e. %s %s' % (N1, MU(), N2, MU()))
    RHS = '( 6 + ( ( ; ; ; ; ; ; ; 7 0 0 0 0 0 0 0 x. ( W + E ) ) x. %s ) )' % LOGX
    assert sc == 'sum_ q e. %s %s <_ %s' % (N2, MU(), RHS), sc[-200:]
    n1f = s([zfin, w.s([w.s([], 'ssrab2', '%s C_ %s' % (N1, ZD()))], 'a1i', '( %s -> %s C_ %s )' % (A0, N1, ZD()))], 'ssfid', '%s e. Fin' % N1)
    Aq1 = '( %s /\\ q e. %s )' % (A0, N1)
    qz1 = w.s([w.s([w.s([], 'ssrab2', '%s C_ %s' % (N1, ZD()))], 'a1i', '( %s -> %s C_ %s )' % (Aq1, N1, ZD())), w.s([], 'simpr', '( %s -> q e. %s )' % (Aq1, N1))], 'sseldd', '( %s -> q e. %s )' % (Aq1, ZD()))
    mn1 = w.s([qz1, w.s([lift(w, zord, Aq1), w.inst('rsp')], 'syl', '( %s -> ( q e. %s -> %s e. NN ) )' % (Aq1, ZD(), MU()))], 'mpd', '( %s -> %s e. NN )' % (Aq1, MU()))
    s1r = s([n1f, w.s([mn1], 'nnred', '( %s -> %s e. RR )' % (Aq1, MU()))], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (N1, MU()))
    s2r = s([n2f, w.s([mn], 'nnred', '( %s -> %s e. RR )' % (Aq, MU()))], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (N2, MU()))
    at = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ca = Closure(w, A0, {'( abs ` T )': ('RR', at), 'W': ('RR', s([wp], 'rpred', 'W e. RR')), 'E': ('RR', er)}); ca.atom('( abs ` T )')
    nn_ = s([s([chi], 'simpld', NXH)], 'simpld', 'N e. NN')
    t2p = s([ca.mem('( ( abs ` T ) + 2 )', 'RR'), linarith(w, A0, [s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')], '0 < ( ( abs ` T ) + 2 )', closure=ca)], 'elrpd', '( ( abs ` T ) + 2 ) e. RR+')
    lg = s([s([s([nn_], 'nnrpd', 'N e. RR+'), t2p], 'rpmulcld', '( N x. ( ( abs ` T ) + 2 ) ) e. RR+')], 'relogcld', '%s e. RR' % LOGX)
    ca.leaf(LOGX, 'RR', lg); ca.atom(LOGX)
    fin = s([s1r, s2r, ca.mem(RHS, 'RR'), le, sd], 'letrd', 'sum_ q e. %s %s <_ %s' % (N1, MU(), RHS))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdnear']))
    return run(w)


if __name__ == '__main__':
    gen_near()
