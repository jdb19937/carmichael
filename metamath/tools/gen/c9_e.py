"""Sortie C9: lndhbd (the cofactor H is bounded by B / (1/8)^n on SQ(C,13/8):
the product lower bound on the frame of SQ(C,7/4) and the maximum modulus
principle rectintmm)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from cl import lift
from c8_o import numst
from c9_freeze import S as FS
import lin
lin.FASTPATH = True

E18 = EXPL('Z', R18)
FRM74 = FRG(A74, B74)


def sqfrd_at(w, ante, cs, U, ust):
    """( ante -> ( INT(A74,B74,U) /\\ A. u e. FRM74 ( 1 / 8 ) <_ ( abs ` ( u - U ) ) ) ) from ust : ( ante -> U e. SQ138 )"""
    f = tsub(stmt('sqfrd'), {'T': R138, 'R': R18, 'V': R74, 'U': U})
    a, c = ante_of(f)
    r138 = numst(w, ante, R138, 'RR'); r18 = numst(w, ante, R18, 'RR+'); r74 = numst(w, ante, R74, 'RR')
    le = lin8(w, ante, [], '( %s + %s ) <_ %s' % (R138, R18, R74), {})
    j = w.s([w.s([cs, w.s([r138, r18, r74], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR+ /\\ %s e. RR ) )' % (ante, R138, R18, R74))], 'jca',
                 '( %s -> ( C e. CC /\\ ( %s e. RR /\\ %s e. RR+ /\\ %s e. RR ) ) )' % (ante, R138, R18, R74)),
             w.s([le, ust], 'jca', '( %s -> ( ( %s + %s ) <_ %s /\\ %s e. %s ) )' % (ante, R138, R18, R74, U, SQ138))], 'jca', '( %s -> %s )' % (ante, a))
    return w.s([j, w.inst('sqfrd')], 'syl', '( %s -> %s )' % (ante, c)), c


def sq_cc(w, ante, cs, r, rst):
    """( ante -> SQA(C,r) e. CC ), ( ante -> SQB(C,r) e. CC )"""
    from c8_n import sqcc
    return sqcc(w, ante, cs, rst, r=r)


def gen_lndhbd():
    w = W('lndhbd', 'The cofactor of a factorisation over zeros in the square of half-side ` 13 / 8 ` is bounded on that square by ` B / ( 1 / 8 ) ^ n ` , ` B ` a bound of ` F ` on the square of half-side ` 7 / 4 ` ( ~ fprodlbe on its frame, ~ rectintmm ).')
    A0 = '( ( %s /\\ %s ) /\\ Y e. %s )' % (DATA, FBD, SQ138)
    dst = w.s([], 'simpll', '( %s -> %s )' % (A0, DATA))
    fbd = w.s([], 'simplr', '( %s -> %s )' % (A0, FBD))
    ys = w.s([], 'simpr', '( %s -> Y e. %s )' % (A0, SQ138))
    d = data_parts(w, A0, dst)
    cs = d['cs']
    bst = w.s([fbd, w.inst('simpl')], 'syl', '( %s -> B e. RR )' % A0)
    fb = w.s([fbd, w.inst('simpr')], 'syl', '( %s -> A. x e. %s ( abs ` ( F ` x ) ) <_ B )' % (A0, SQ74))
    sy, syc = sqfrd_at(w, A0, cs, 'Y', ys)
    INTY = INTG(A74, B74, 'Y')
    inty = w.s([sy, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, INTY))
    r74 = numst(w, A0, R74, 'RR')
    a74c, b74c = sq_cc(w, A0, cs, R74, r74)
    ab = w.s([a74c, b74c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A74, B74))
    # n and E
    NS = NSUM('Z')
    ZO = '( Z e. Fin /\\ O : Z --> NN )'
    Zq = '( %s /\\ q e. Z )' % ZO
    oqr = w.s([w.s([w.s([], 'simplr', '( %s -> O : Z --> NN )' % Zq), w.s([], 'simpr', '( %s -> q e. Z )' % Zq)], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN )' % Zq)],
              'nnred', '( %s -> ( O ` q ) e. RR )' % Zq)
    nsr0 = w.s([w.s([], 'simpl', '( %s -> Z e. Fin )' % ZO), oqr], 'fsumrecl', '( %s -> %s e. RR )' % (ZO, NS))
    nsr = w.s([w.s([d['zfin'], d['of']], 'jca', '( %s -> %s )' % (A0, ZO)), nsr0], 'syl', '( %s -> %s e. RR )' % (A0, NS))
    l18 = w.s([numst(w, A0, R18, 'RR+')], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (A0, R18))
    ep = w.s([w.s([nsr, l18], 'remulcld', '( %s -> ( %s x. ( log ` %s ) ) e. RR )' % (A0, NS, R18))], 'rpefcld', '( %s -> %s e. RR+ )' % (A0, E18))
    # the frame bound
    Au = '( %s /\\ u e. %s )' % (A0, FRM74)
    L = lambda st: lift(w, st, Au)
    uf = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, FRM74))
    frp = w.s([L(ab), L(inty), w.inst('crectfrp')], 'syl2anc', '( %s -> %s C_ ( %s \\ { Y } ) )' % (Au, FRM74, SQ74))
    us74 = w.s([w.s([frp, uf], 'sseldd', '( %s -> u e. ( %s \\ { Y } ) )' % (Au, SQ74)), w.inst('eldifi')], 'syl', '( %s -> u e. %s )' % (Au, SQ74))
    ud = w.s([L(d['s74d']), us74], 'sseldd', '( %s -> u e. D )' % Au)
    ucc = w.s([w.s([L(ab), w.inst('crectss')], 'syl', '( %s -> %s C_ CC )' % (Au, SQ74)), us74], 'sseldd', '( %s -> u e. CC )' % Au)
    PU = PRZ('Z', 'u')
    subz = w.s([w.s([], 'fveq2', '( z = u -> ( F ` z ) = ( F ` u ) )'),
                w.s([w.s([w.s([w.s([], 'oveq1', '( z = u -> ( z - q ) = ( u - q ) )')], 'oveq1d', '( z = u -> ( ( z - q ) ^ ( O ` q ) ) = ( ( u - q ) ^ ( O ` q ) ) )')], 'prodeq2sdv',
                          '( z = u -> %s = %s )' % (PRZ('Z', 'z'), PU)), w.s([], 'fveq2', '( z = u -> ( H ` z ) = ( H ` u ) )')], 'oveq12d',
                    '( z = u -> ( %s x. ( H ` z ) ) = ( %s x. ( H ` u ) ) )' % (PRZ('Z', 'z'), PU))], 'eqeq12d',
               '( z = u -> ( ( F ` z ) = ( %s x. ( H ` z ) ) <-> ( F ` u ) = ( %s x. ( H ` u ) ) ) )' % (PRZ('Z', 'z'), PU))
    fu = w.s([subz, L(d['fac']), ud], 'rspcdva', '( %s -> ( F ` u ) = ( %s x. ( H ` u ) ) )' % (Au, PU))
    subx = w.s([w.s([w.s([], 'fveq2', '( x = u -> ( F ` x ) = ( F ` u ) )')], 'fveq2d', '( x = u -> ( abs ` ( F ` x ) ) = ( abs ` ( F ` u ) ) )')], 'breq1d',
               '( x = u -> ( ( abs ` ( F ` x ) ) <_ B <-> ( abs ` ( F ` u ) ) <_ B ) )')
    fub = w.s([subx, L(fb), us74], 'rspcdva', '( %s -> ( abs ` ( F ` u ) ) <_ B )' % Au)
    # distances from u to the zeros
    Auj = '( %s /\\ j e. Z )' % Au
    js = w.s([lift(w, d['zsq'], Auj), w.s([], 'simpr', '( %s -> j e. Z )' % Auj)], 'sseldd', '( %s -> j e. %s )' % (Auj, SQ138))
    sj, sjc = sqfrd_at(w, Auj, lift(w, cs, Auj), 'j', js)
    DJ = 'A. u e. %s %s <_ ( abs ` ( u - j ) )' % (FRM74, R18)
    dj = w.s([sj, w.inst('simpr')], 'syl', '( %s -> %s )' % (Auj, DJ))
    dju = w.s([lift(w, uf, Auj), w.s([dj], 'r19.21bi', '( ( %s /\\ u e. %s ) -> %s <_ ( abs ` ( u - j ) ) )' % (Auj, FRM74, R18))], 'mpdan', '( %s -> %s <_ ( abs ` ( u - j ) ) )' % (Auj, R18))
    DALL = 'A. j e. Z %s <_ ( abs ` ( u - j ) )' % R18
    dall = w.s([dju], 'ralrimiva', '( %s -> %s )' % (Au, DALL))
    a138c, b138c = sq_cc(w, Au, L(cs), R138, numst(w, Au, R138, 'RR'))
    s138cc = w.s([w.s([a138c, b138c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Au, A138, B138)), w.inst('crectss')], 'syl', '( %s -> %s C_ CC )' % (Au, SQ138))
    zc = w.s([L(d['zsq']), s138cc], 'sstrd', '( %s -> Z C_ CC )' % Au)
    of0 = w.s([L(d['of']), w.s([w.s([], 'nnssnn0', 'NN C_ NN0')], 'a1i', '( %s -> NN C_ NN0 )' % Au)], 'fssd', '( %s -> O : Z --> NN0 )' % Au)
    PL = tsub(stmt('fprodlbe'), {'S': 'Z', 'U': 'u', 'R': R18})
    pa, pc = ante_of(PL)
    pl = w.s([w.s([w.s([L(d['zfin']), zc, of0], '3jca', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % Au),
                   w.s([ucc, numst(w, Au, R18, 'RR+'), dall], '3jca', '( %s -> ( u e. CC /\\ %s e. RR+ /\\ %s ) )' % (Au, R18, DALL))], 'jca', '( %s -> %s )' % (Au, pa)),
              w.inst('fprodlbe')], 'syl', '( %s -> %s )' % (Au, pc))
    assert pc == '%s <_ ( abs ` %s )' % (E18, PU), pc
    # E |H u| <_ |P u| |H u| = |F u| <_ B
    hf = w.s([L(d['holh']), w.inst('simpl')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % Au)
    hu = w.s([w.s([hf, w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % Au), ud], 'ffvelcdmd', '( %s -> ( H ` u ) e. CC )' % Au)
    ahu = w.s([hu], 'abscld', '( %s -> ( abs ` ( H ` u ) ) e. RR )' % Au)
    er = w.s([L(ep)], 'rpred', '( %s -> %s e. RR )' % (Au, E18))
    pc_ = w.s([w.s([L(d['zfin']), zc, of0], '3jca', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % Au), ucc], 'jca', '( %s -> ( ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) /\\ u e. CC ) )' % Au)
    PC0 = '( ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) /\\ u e. CC )'
    Pq = '( %s /\\ q e. Z )' % PC0
    zs3 = w.s([], 'simpll', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % Pq)
    qz = w.s([], 'simpr', '( %s -> q e. Z )' % Pq)
    qcq = w.s([w.s([zs3, w.inst('simp2')], 'syl', '( %s -> Z C_ CC )' % Pq), qz], 'sseldd', '( %s -> q e. CC )' % Pq)
    oqq = w.s([w.s([zs3, w.inst('simp3')], 'syl', '( %s -> O : Z --> NN0 )' % Pq), qz], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN0 )' % Pq)
    tq0 = w.s([w.s([w.s([], 'simplr', '( %s -> u e. CC )' % Pq), qcq], 'subcld', '( %s -> ( u - q ) e. CC )' % Pq), oqq], 'expcld', '( %s -> ( ( u - q ) ^ ( O ` q ) ) e. CC )' % Pq)
    pcc0 = w.s([w.s([w.s([], 'simpl', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % PC0), w.inst('simp1')], 'syl', '( %s -> Z e. Fin )' % PC0), tq0], 'fprodcl', '( %s -> %s e. CC )' % (PC0, PU))
    puc = w.s([pc_, pcc0], 'syl', '( %s -> %s e. CC )' % (Au, PU))
    apu = w.s([puc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Au, PU))
    m1 = w.s([er, apu, ahu, pl, w.s([hu], 'absge0d', '( %s -> 0 <_ ( abs ` ( H ` u ) ) )' % Au)], 'lemul1ad', '( %s -> ( %s x. ( abs ` ( H ` u ) ) ) <_ ( ( abs ` %s ) x. ( abs ` ( H ` u ) ) ) )' % (Au, E18, PU))
    am = w.s([w.s([fu], 'fveq2d', '( %s -> ( abs ` ( F ` u ) ) = ( abs ` ( %s x. ( H ` u ) ) ) )' % (Au, PU)), w.s([puc, hu], 'absmuld', '( %s -> ( abs ` ( %s x. ( H ` u ) ) ) = ( ( abs ` %s ) x. ( abs ` ( H ` u ) ) ) )' % (Au, PU, PU))],
             'eqtrd', '( %s -> ( abs ` ( F ` u ) ) = ( ( abs ` %s ) x. ( abs ` ( H ` u ) ) ) )' % (Au, PU))
    m2 = w.s([w.s([m1, am], 'breqtrrd', '( %s -> ( %s x. ( abs ` ( H ` u ) ) ) <_ ( abs ` ( F ` u ) ) )' % (Au, E18)), fub], 'letrd', '( %s -> ( %s x. ( abs ` ( H ` u ) ) ) <_ B )' % (Au, E18))
    M = '( B / %s )' % E18
    hub = w.s([m2, w.s([ahu, L(bst), L(ep)], 'lemuldiv2d', '( %s -> ( ( %s x. ( abs ` ( H ` u ) ) ) <_ B <-> ( abs ` ( H ` u ) ) <_ %s ) )' % (Au, E18, M))], 'mpbid', '( %s -> ( abs ` ( H ` u ) ) <_ %s )' % (Au, M))
    ALF = 'A. u e. %s ( abs ` ( H ` u ) ) <_ %s' % (FRM74, M)
    alf = w.s([hub], 'ralrimiva', '( %s -> %s )' % (A0, ALF))
    # rectintmm
    RM = tsub(stmt('rectintmm'), {'A': A74, 'B': B74, 'P': 'Y', 'F': 'H', 'M': M})
    ra, rc = ante_of(RM)
    mr = w.s([bst, ep], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, M))
    P1 = '( ( %s e. CC /\\ %s e. CC ) /\\ %s /\\ ( %s /\\ %s C_ D ) )' % (A74, B74, INTY, HOLG('H', 'D'), SQ74)
    rj = w.s([w.s([ab, inty, w.s([d['holh'], d['s74d']], 'jca', '( %s -> ( %s /\\ %s C_ D ) )' % (A0, HOLG('H', 'D'), SQ74))], '3jca', '( %s -> %s )' % (A0, P1)),
              w.s([mr, alf], 'jca', '( %s -> ( %s e. RR /\\ %s ) )' % (A0, M, ALF))], 'jca', '( %s -> %s )' % (A0, ra))
    goal = '( %s -> ( abs ` ( H ` Y ) ) <_ %s )' % (A0, M)
    assert goal == FS['lndhbd'], (goal, FS['lndhbd'])
    assert rc == '( abs ` ( H ` Y ) ) <_ %s' % M, rc
    w.qed([rj, w.inst('rectintmm')], 'syl', goal)
    return run8(w)


if __name__ == '__main__':
    gen_lndhbd()
