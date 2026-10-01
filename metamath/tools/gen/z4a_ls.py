"""Sortie Z4a, batch 5: the per-modulus block bound of the large sieve
(LargeSieve fiber_block_le)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from z4alib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DQ = DB('Q'); LQ = LZ('Q'); CRQ = CR('Q'); DIVQ = DIV('Q'); PHI = '( phi ` Q )'
AL = '( ( Q e. NN /\\ M e. RR ) /\\ %s /\\ %s )' % (HW, COPALL('Q'))
def H(x): return ABS2('sum_ u e. %s ( %s x. %s )' % (CRQ, EV(x, 'Q', 'u'), TZ('Q', 'u')))
def FM(f): return '( t e. %s |-> %s )' % (PC(f), EMB(f, 'Q', 't'))
def IMG(f): return 'ran %s' % FM(f)
ESQ = ABS2(ESUM('( n - M )', '( u / Q )'))


def al_parts(w, ante, alst):
    """q, m, hw, cop under ante from alst: ( ante -> AL )"""
    qm = w.s([alst], 'simp1d', '( %s -> ( Q e. NN /\\ M e. RR ) )' % ante)
    q = w.s([qm], 'simpld', '( %s -> Q e. NN )' % ante); m = w.s([qm], 'simprd', '( %s -> M e. RR )' % ante)
    hw = w.s([alst], 'simp2d', '( %s -> %s )' % (ante, HW)); cop = w.s([alst], 'simp3d', '( %s -> %s )' % (ante, COPALL('Q')))
    return q, m, hw, cop


def rabmem(w, ante, mem, v, dom, body, a):
    """( ante -> ( a e. dom /\\ body[v:=a] ) ) from mem: ( ante -> a e. { v e. dom | body } ); returns (step, body')"""
    eq = '%s = %s' % (v, a)
    idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, nb = w.wcongr(body, {v: a}, eq, {v: idst})
    er = w.s([st], 'elrab', '( %s e. { %s e. %s | %s } <-> ( %s e. %s /\\ %s ) )' % (a, v, dom, body, a, dom, nb))
    return w.s([mem, er], 'sylib', '( %s -> ( %s e. %s /\\ %s ) )' % (ante, a, dom, nb)), nb


DIVBODY = '( d || Q /\\ ( ( mmu ` ( Q / d ) ) =/= 0 /\\ ( ( Q / d ) gcd d ) = 1 ) )'
def divparts(w, ante, mem, f='f'):
    """from mem: ( ante -> f e. DIV(Q) ): f e. NN, f || Q, the squarefree-coprime pair"""
    st, nb = rabmem(w, ante, mem, 'd', 'NN', DIVBODY, f)
    fnn = w.s([st], 'simpld', '( %s -> %s e. NN )' % (ante, f))
    rest = w.s([st], 'simprd', '( %s -> %s )' % (ante, nb))
    dv = w.s([rest], 'simpld', '( %s -> %s || Q )' % (ante, f))
    sq = w.s([rest], 'simprd', '( %s -> ( ( mmu ` ( Q / %s ) ) =/= 0 /\\ ( ( Q / %s ) gcd %s ) = 1 ) )' % (ante, f, f, f))
    return fnn, dv, sq


def pcparts(w, ante, mem, f, t):
    """from mem: ( ante -> t e. PC(f) ): t e. Df, ( f DChrCond t ) = f"""
    st, nb = rabmem(w, ante, mem, 'y', DB(f), '( %s DChrCond y ) = %s' % (f, f), t)
    return w.s([st], 'simpld', '( %s -> %s e. %s )' % (ante, t, DB(f))), w.s([st], 'simprd', '( %s -> %s )' % (ante, nb))


def tzcl(w, ante, qst, hwst, umem, u='u'):
    """( ante -> TZ(Q,u) e. CC ) from umem: ( ante -> u e. CR(Q) )"""
    An = '( %s /\\ n e. W )' % ante
    nz, an = win(w, An, w.s([hwst], 'adantr', '( %s -> %s )' % (An, HW)), w.s([], 'simpr', '( %s -> n e. W )' % An))
    uz = crz(w, An, w.s([umem], 'adantr', '( %s -> %s e. %s )' % (An, u, CRQ)), u, 'Q')
    nu = w.s([nz, uz], 'zmulcld', '( %s -> ( n x. %s ) e. ZZ )' % (An, u))
    e = ecl(w, An, w.s([qst], 'adantr', '( %s -> Q e. NN )' % An), w.s([nu], 'zcnd', '( %s -> ( n x. %s ) e. CC )' % (An, u)), '( n x. %s )' % u, 'Q')
    t = w.s([an, e], 'mulcld', '( %s -> ( ( A ` n ) x. %s ) e. CC )' % (An, E('( n x. %s )' % u, 'Q')))
    return w.s([w.s([hwst], 'simp1d', '( %s -> W e. Fin )' % ante), t], 'fsumcl', '( %s -> %s e. CC )' % (ante, TZ('Q', u)))


def hcl(w, ante, qst, hwst, xmem, x='x'):
    """( ante -> H(x) e. RR ), ( ante -> 0 <_ H(x) ) from xmem: ( ante -> x e. DQ )"""
    Au = '( %s /\\ u e. %s )' % (ante, CRQ)
    umem = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, CRQ))
    g, z, d, l = dchyp(w, 'Q')
    xu = w.s([g, z, d, l, w.s([xmem], 'adantr', '( %s -> %s e. %s )' % (Au, x, DQ)), crz(w, Au, umem, 'u', 'Q')], 'dchrzrhcl', '( %s -> %s e. CC )' % (Au, EV(x, 'Q', 'u')))
    tz = tzcl(w, Au, w.s([qst], 'adantr', '( %s -> Q e. NN )' % Au), w.s([hwst], 'adantr', '( %s -> %s )' % (Au, HW)), umem)
    S = 'sum_ u e. %s ( %s x. %s )' % (CRQ, EV(x, 'Q', 'u'), TZ('Q', 'u'))
    s = w.s([crfin(w, ante, 'Q'), w.s([xu, tz], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Au, EV(x, 'Q', 'u'), TZ('Q', 'u')))], 'fsumcl', '( %s -> %s e. CC )' % (ante, S))
    a = w.s([s], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ante, S))
    return w.s([a], 'resqcld', '( %s -> %s e. RR )' % (ante, H(x))), w.s([a], 'sqge0d', '( %s -> 0 <_ %s )' % (ante, H(x)))


if __name__ == '__main__':
    # ---- lsfiberlem1: the bridge (Lean hbridge)
    A0 = '( %s /\\ u e. %s )' % (AL, CRQ)
    An = '( %s /\\ n e. W )' % A0
    w = W('lsfiberlem1', 'Lemma for lsfiber: the additive-character sum at the residue u has the modulus of the recentred exponential sum at the Farey point u / Q (Lean hbridge).')
    al = w.s([], 'simpl', '( %s -> %s )' % (A0, AL)); q, m, hw, cop = al_parts(w, A0, al)
    umem = w.s([], 'simpr', '( %s -> u e. %s )' % (A0, CRQ)); uz = crz(w, A0, umem, 'u', 'Q')
    nz, an = win(w, An, w.s([hw], 'adantr', '( %s -> %s )' % (An, HW)), w.s([], 'simpr', '( %s -> n e. W )' % An))
    qn = w.s([q], 'adantr', '( %s -> Q e. NN )' % An)
    da = w.s([w.s([nz], 'zcnd', '( %s -> n e. CC )' % An), w.s([w.s([uz], 'adantr', '( %s -> u e. ZZ )' % An)], 'zcnd', '( %s -> u e. CC )' % An), w.s([qn], 'nncnd', '( %s -> Q e. CC )' % An), w.s([qn], 'nnne0d', '( %s -> Q =/= 0 )' % An)], 'divassd', '( %s -> ( ( n x. u ) / Q ) = ( n x. ( u / Q ) ) )' % An)
    e1 = w.s([w.s([w.s([da], 'oveq2d', '( %s -> ( %s x. ( ( n x. u ) / Q ) ) = ( %s x. ( n x. ( u / Q ) ) ) )' % (An, C2, C2))], 'fveq2d', '( %s -> %s = %s )' % (An, E('( n x. u )', 'Q'), EAT('n', '( u / Q )')))], 'oveq2d', '( %s -> ( ( A ` n ) x. %s ) = ( ( A ` n ) x. %s ) )' % (An, E('( n x. u )', 'Q'), EAT('n', '( u / Q )')))
    s1 = w.s([e1], 'sumeq2dv', '( %s -> %s = %s )' % (A0, TZ('Q', 'u'), ESUM('n', '( u / Q )')))
    uq = w.s([w.s([uz], 'zred', '( %s -> u e. RR )' % A0), w.s([q], 'nnred', '( %s -> Q e. RR )' % A0), w.s([q], 'nnne0d', '( %s -> Q =/= 0 )' % A0)], 'redivcld', '( %s -> ( u / Q ) e. RR )' % A0)
    ce = w.s([hw, m, uq, w.inst('eatcenter')], 'syl3anc', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, ESUM('n', '( u / Q )'), ESUM('( n - M )', '( u / Q )')))
    ab = w.s([w.s([s1], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, TZ('Q', 'u'), ESUM('n', '( u / Q )'))), ce], 'eqtrd', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, TZ('Q', 'u'), ESUM('( n - M )', '( u / Q )')))
    w.qed([ab], 'oveq1d', '( %s -> %s = %s )' % (A0, ABS2(TZ('Q', 'u')), ESQ)); run(w)

    # ---- lsfiberlem2: one selected character (Lean hval)
    A1 = '( %s /\\ f e. %s )' % (AL, DIVQ); A0 = '( %s /\\ x e. %s )' % (A1, PC('f'))
    w = W('lsfiberlem2', 'Lemma for lsfiber: f times the squared window sum twisted by a primitive character x mod f is the squared twisted unit average of its induced inverse at level Q (Lean hval, from W_norm_eq).')
    al = w.s([], 'simpll', '( %s -> %s )' % (A0, AL)); q, m, hw, cop = al_parts(w, A0, al)
    fnn, dv, sq = divparts(w, A0, w.s([], 'simplr', '( %s -> f e. %s )' % (A0, DIVQ)))
    xd, xc = pcparts(w, A0, w.s([], 'simpr', '( %s -> x e. %s )' % (A0, PC('f'))), 'f', 'x')
    HWNf = '( ( Q e. NN /\\ f e. NN /\\ f || Q ) /\\ ( ( mmu ` ( Q / f ) ) =/= 0 /\\ ( ( Q / f ) gcd f ) = 1 ) /\\ ( x e. %s /\\ ( f DChrCond x ) = f ) )' % DB('f')
    hwn = w.s([w.s([q, fnn, dv], '3jca', '( %s -> ( Q e. NN /\\ f e. NN /\\ f || Q ) )' % A0), sq, w.s([xd, xc], 'jca', '( %s -> ( x e. %s /\\ ( f DChrCond x ) = f ) )' % (A0, DB('f')))], '3jca', '( %s -> %s )' % (A0, HWNf))
    wn = w.s([hwn, hw, cop, w.inst('dchrwnorm')], 'syl3anc', '( %s -> %s = ( f x. %s ) )' % (A0, H(EMB('f', 'Q', 'x')), ABS2(WSUM('x', 'f'))))
    w.qed([wn], 'eqcomd', '( %s -> ( f x. %s ) = %s )' % (A0, ABS2(WSUM('x', 'f')), H(EMB('f', 'Q', 'x')))); run(w)


def fvmd(w, ante, v, dom, body, a, memst, exs):
    """( ante -> ( ( v e. dom |-> body ) ` a ) = body[v:=a] ) by fvmptd; exs: ( ante -> body[v:=a] e. _V )"""
    eq = '%s = %s' % (v, a)
    idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, val = w.congr(body, {v: a}, eq, {v: idst})
    mp = '( %s e. %s |-> %s )' % (v, dom, body)
    sub = w.s([st], 'adantl', '( ( %s /\\ %s ) -> %s = %s )' % (ante, eq, body, val))
    return w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, mp, mp)), sub, memst, exs], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, a, val))


def grp(w, ante, nst, n):
    g = w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n))
    ab = w.s([nst, w.s([g], 'dchrabl', '( %s e. NN -> ( DChr ` %s ) e. Abel )' % (n, n))], 'syl', '( %s -> ( DChr ` %s ) e. Abel )' % (ante, n))
    return w.s([ab, w.inst('ablgrp')], 'syl', '( %s -> ( DChr ` %s ) e. Grp )' % (ante, n))


def pcfin(w, ante, fnn, f='f'):
    return w.s([fnn, w.inst('dchrprimsfi')], 'syl', '( %s -> %s e. Fin )' % (ante, PC(f)))


def divfin(w, ante, q):
    """( ante -> DIV(Q) e. Fin )"""
    DV = '{ d e. NN | d || Q }'
    ss = w.s([w.s([w.s([], 'simpl', '( %s -> d || Q )' % DIVBODY)], 'a1i', '( d e. NN -> ( %s -> d || Q ) )' % DIVBODY)], 'ss2rabi', '%s C_ %s' % (DIVQ, DV))
    fi = w.s([q, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (ante, DV))
    return w.s([fi, w.s([ss], 'a1i', '( %s -> %s C_ %s )' % (ante, DIVQ, DV))], 'ssfid', '( %s -> %s e. Fin )' % (ante, DIVQ))


def rnsub(w, ante, f1st, f='f'):
    """( ante -> IMG(f) C_ DQ ) from f1st: ( ante -> FM(f) : PC(f) -1-1-> DQ )"""
    ff = w.s([f1st, w.inst('f1f')], 'syl', '( %s -> %s : %s --> %s )' % (ante, FM(f), PC(f), DQ))
    return w.s([ff, w.inst('frn')], 'syl', '( %s -> %s C_ %s )' % (ante, IMG(f), DQ))


if __name__ == '__main__':
    # ---- lsfiberlem3: the embedding is injective (Lean hinj, one level)
    A1 = '( %s /\\ f e. %s )' % (AL, DIVQ)
    w = W('lsfiberlem3', 'Lemma for lsfiber: inducing the inverse of a primitive character mod f up to level Q is an injection of the primitive characters mod f into the characters mod Q (Lean hinj at one level).')
    al = w.s([], 'simpl', '( %s -> %s )' % (A1, AL)); q, m, hw, cop = al_parts(w, A1, al)
    fnn, dv, sq = divparts(w, A1, w.s([], 'simpr', '( %s -> f e. %s )' % (A1, DIVQ)))
    h3 = w.s([fnn, q, dv], '3jca', '( %s -> ( f e. NN /\\ Q e. NN /\\ f || Q ) )' % A1)
    At = '( %s /\\ t e. %s )' % (A1, PC('f'))
    td, _ = pcparts(w, At, w.s([], 'simpr', '( %s -> t e. %s )' % (At, PC('f'))), 'f', 't')
    ift = grpinv(w, At, w.s([fnn], 'adantr', '( %s -> f e. NN )' % At), td, 'f', 't')
    IFt = '( %s ` t )' % INV('f'); IFz = '( %s ` z )' % INV('f')
    cl = w.s([w.s([w.s([h3], 'adantr', '( %s -> ( f e. NN /\\ Q e. NN /\\ f || Q ) )' % At), ift], 'jca', '( %s -> ( ( f e. NN /\\ Q e. NN /\\ f || Q ) /\\ %s e. %s ) )' % (At, IFt, DB('f'))), w.inst('dchrindcl')], 'syl', '( %s -> %s e. %s )' % (At, EMB('f', 'Q', 't'), DQ))
    r1 = w.s([cl], 'ralrimiva', '( %s -> A. t e. %s %s e. %s )' % (A1, PC('f'), EMB('f', 'Q', 't'), DQ))
    Atz = '( %s /\\ ( t e. %s /\\ z e. %s ) )' % (A1, PC('f'), PC('f'))
    tz = w.s([], 'simpr', '( %s -> ( t e. %s /\\ z e. %s ) )' % (Atz, PC('f'), PC('f')))
    td2, _ = pcparts(w, Atz, w.s([tz], 'simpld', '( %s -> t e. %s )' % (Atz, PC('f'))), 'f', 't')
    zd2, _ = pcparts(w, Atz, w.s([tz], 'simprd', '( %s -> z e. %s )' % (Atz, PC('f'))), 'f', 'z')
    fz = w.s([fnn], 'adantr', '( %s -> f e. NN )' % Atz)
    ift2 = grpinv(w, Atz, fz, td2, 'f', 't'); ifz2 = grpinv(w, Atz, fz, zd2, 'f', 'z')
    b1 = w.s([w.s([h3], 'adantr', '( %s -> ( f e. NN /\\ Q e. NN /\\ f || Q ) )' % Atz), ift2, ifz2, w.inst('dchrindinj')], 'syl3anc', '( %s -> ( %s = %s <-> %s = %s ) )' % (Atz, EMB('f', 'Q', 't'), EMB('f', 'Q', 'z'), IFt, IFz))
    b2 = w.s([w.s([], 'eqid', '%s = %s' % (DB('f'), DB('f'))), w.s([], 'eqid', '%s = %s' % (INV('f'), INV('f'))), grp(w, Atz, fz, 'f'), td2, zd2], 'grpinv11', '( %s -> ( %s = %s <-> t = z ) )' % (Atz, IFt, IFz))
    imp = w.s([w.s([b1, b2], 'bitrd', '( %s -> ( %s = %s <-> t = z ) )' % (Atz, EMB('f', 'Q', 't'), EMB('f', 'Q', 'z')))], 'biimpd', '( %s -> ( %s = %s -> t = z ) )' % (Atz, EMB('f', 'Q', 't'), EMB('f', 'Q', 'z')))
    r2 = w.s([imp], 'ralrimivva', '( %s -> A. t e. %s A. z e. %s ( %s = %s -> t = z ) )' % (A1, PC('f'), PC('f'), EMB('f', 'Q', 't'), EMB('f', 'Q', 'z')))
    eq = 't = z'; idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    cst, D = w.congr(EMB('f', 'Q', 't'), {'t': 'z'}, eq, {'t': idst})
    fm = w.s([w.s([], 'eqid', '%s = %s' % (FM('f'), FM('f'))), cst], 'f1mpt', '( %s : %s -1-1-> %s <-> ( A. t e. %s %s e. %s /\\ A. t e. %s A. z e. %s ( %s = %s -> t = z ) ) )' % (FM('f'), PC('f'), DQ, PC('f'), EMB('f', 'Q', 't'), DQ, PC('f'), PC('f'), EMB('f', 'Q', 't'), D))
    w.qed([w.s([r1, r2], 'jca', '( %s -> ( A. t e. %s %s e. %s /\\ A. t e. %s A. z e. %s ( %s = %s -> t = z ) ) )' % (A1, PC('f'), EMB('f', 'Q', 't'), DQ, PC('f'), PC('f'), EMB('f', 'Q', 't'), D)), fm], 'sylibr', '( %s -> %s : %s -1-1-> %s )' % (A1, FM('f'), PC('f'), DQ)); run(w)

    # ---- lsfiberlem4: one divisor's block as a sum over its image
    w = W('lsfiberlem4', 'Lemma for lsfiber: f times the block of primitive characters mod f is the sum of the squared twisted unit averages over the image of the embedding at level Q (Lean hSigma, hval, himg at one level).')
    al = w.s([], 'simpl', '( %s -> %s )' % (A1, AL)); q, m, hw, cop = al_parts(w, A1, al)
    fmem = w.s([], 'simpr', '( %s -> f e. %s )' % (A1, DIVQ))
    fnn, dv, sq = divparts(w, A1, fmem)
    pf = pcfin(w, A1, fnn)
    Ax = '( %s /\\ x e. %s )' % (A1, PC('f'))
    xd, _ = pcparts(w, Ax, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, PC('f'))), 'f', 'x')
    Axn = '( %s /\\ n e. W )' % Ax
    nz, an = win(w, Axn, w.s([w.s([hw], 'adantr', '( %s -> %s )' % (Ax, HW))], 'adantr', '( %s -> %s )' % (Axn, HW)), w.s([], 'simpr', '( %s -> n e. W )' % Axn))
    g, z, d, l = dchyp(w, 'f')
    xn = w.s([g, z, d, l, w.s([xd], 'adantr', '( %s -> x e. %s )' % (Axn, DB('f'))), nz], 'dchrzrhcl', '( %s -> %s e. CC )' % (Axn, EV('x', 'f', 'n')))
    ws = w.s([w.s([w.s([hw], 'simp1d', '( %s -> W e. Fin )' % A1)], 'adantr', '( %s -> W e. Fin )' % Ax), w.s([an, xn], 'mulcld', '( %s -> ( ( A ` n ) x. %s ) e. CC )' % (Axn, EV('x', 'f', 'n')))], 'fsumcl', '( %s -> %s e. CC )' % (Ax, WSUM('x', 'f')))
    wsq = w.s([w.s([w.s([ws], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ax, WSUM('x', 'f')))], 'resqcld', '( %s -> %s e. RR )' % (Ax, ABS2(WSUM('x', 'f'))))], 'recnd', '( %s -> %s e. CC )' % (Ax, ABS2(WSUM('x', 'f'))))
    s1 = w.s([pf, w.s([fnn], 'nncnd', '( %s -> f e. CC )' % A1), wsq], 'fsummulc2', '( %s -> ( f x. %s ) = sum_ x e. %s ( f x. %s ) )' % (A1, BLK('f'), PC('f'), ABS2(WSUM('x', 'f'))))
    s2 = w.s([w.s([], 'lsfiberlem2', '( %s -> ( f x. %s ) = %s )' % (Ax, ABS2(WSUM('x', 'f')), H(EMB('f', 'Q', 'x'))))], 'sumeq2dv', '( %s -> sum_ x e. %s ( f x. %s ) = sum_ x e. %s %s )' % (A1, PC('f'), ABS2(WSUM('x', 'f')), PC('f'), H(EMB('f', 'Q', 'x'))))
    f1 = w.s([], 'lsfiberlem3', '( %s -> %s : %s -1-1-> %s )' % (A1, FM('f'), PC('f'), DQ))
    bij = w.s([f1, w.inst('f1f1orn')], 'syl', '( %s -> %s : %s -1-1-onto-> %s )' % (A1, FM('f'), PC('f'), IMG('f')))
    val = fvmd(w, Ax, 't', PC('f'), EMB('f', 'Q', 't'), 'x', w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, PC('f'))), w.s([], 'fvexd', '( %s -> %s e. _V )' % (Ax, EMB('f', 'Q', 'x'))))
    Az = '( %s /\\ z e. %s )' % (A1, IMG('f'))
    zdq = w.s([rnsub(w, A1, f1)], 'sselda', '( %s -> z e. %s )' % (Az, DQ))
    hz, _ = hcl(w, Az, w.s([q], 'adantr', '( %s -> Q e. NN )' % Az), w.s([hw], 'adantr', '( %s -> %s )' % (Az, HW)), zdq, 'z')
    bcl = w.s([hz], 'recnd', '( %s -> %s e. CC )' % (Az, H('z')))
    s3, D = fsumf1o(w, A1, 'z', IMG('f'), H('z'), 'x', PC('f'), FM('f'), EMB('f', 'Q', 'x'), pf, bij, val, bcl)
    assert D == H(EMB('f', 'Q', 'x')), D
    cv, C = cbvsum(w, IMG('f'), H('z'), 'z', 'x')
    s4 = w.s([cv], 'a1i', '( %s -> sum_ z e. %s %s = sum_ x e. %s %s )' % (A1, IMG('f'), H('z'), IMG('f'), C))
    c1 = w.s([s1, s2], 'eqtrd', '( %s -> ( f x. %s ) = sum_ x e. %s %s )' % (A1, BLK('f'), PC('f'), D))
    c2 = w.s([c1, s3], 'eqtr4d', '( %s -> ( f x. %s ) = sum_ z e. %s %s )' % (A1, BLK('f'), IMG('f'), H('z')))
    w.qed([c2, s4], 'eqtrd', '( %s -> ( f x. %s ) = sum_ x e. %s %s )' % (A1, BLK('f'), IMG('f'), H('x'))); run(w)

    # ---- lsfiberlem5: the selected characters are dominated by all characters (Lean hsel)
    UIMG = 'U_ f e. %s %s' % (DIVQ, IMG('f'))
    w = W('lsfiberlem5', 'Lemma for lsfiber: the f-weighted blocks of primitive characters over the admissible divisors f of Q are dominated by the sum over all characters mod Q of the squared twisted unit averages (Lean hsel).')
    q, m, hw, cop = al_parts(w, AL, w.s([], 'id', '( %s -> %s )' % (AL, AL)))
    dfin = divfin(w, AL, q)
    A1 = '( %s /\\ f e. %s )' % (AL, DIVQ)
    a = w.s([w.s([], 'lsfiberlem4', '( %s -> ( f x. %s ) = sum_ x e. %s %s )' % (A1, BLK('f'), IMG('f'), H('x')))], 'sumeq2dv', '( %s -> sum_ f e. %s ( f x. %s ) = sum_ f e. %s sum_ x e. %s %s )' % (AL, DIVQ, BLK('f'), DIVQ, IMG('f'), H('x')))
    # image finiteness
    fnn, dv, sq = divparts(w, A1, w.s([], 'simpr', '( %s -> f e. %s )' % (A1, DIVQ)))
    ifin = w.s([w.s([pcfin(w, A1, fnn), w.inst('mptfi')], 'syl', '( %s -> %s e. Fin )' % (A1, FM('f'))), w.inst('rnfi')], 'syl', '( %s -> %s e. Fin )' % (A1, IMG('f')))
    # disjointness by the conductor
    At = '( %s /\\ t e. %s )' % (A1, PC('f'))
    td, tc = pcparts(w, At, w.s([], 'simpr', '( %s -> t e. %s )' % (At, PC('f'))), 'f', 't')
    ft = w.s([fnn], 'adantr', '( %s -> f e. NN )' % At)
    IFt = '( %s ` t )' % INV('f')
    ift = grpinv(w, At, ft, td, 'f', 't')
    h3 = w.s([ft, w.s([w.s([q], 'adantr', '( %s -> Q e. NN )' % A1)], 'adantr', '( %s -> Q e. NN )' % At), w.s([dv], 'adantr', '( %s -> f || Q )' % At)], '3jca', '( %s -> ( f e. NN /\\ Q e. NN /\\ f || Q ) )' % At)
    ci = w.s([w.s([h3, ift], 'jca', '( %s -> ( ( f e. NN /\\ Q e. NN /\\ f || Q ) /\\ %s e. %s ) )' % (At, IFt, DB('f'))), w.inst('dchrcondind')], 'syl', '( %s -> ( Q DChrCond %s ) = ( f DChrCond %s ) )' % (At, EMB('f', 'Q', 't'), IFt))
    cv = w.s([w.s([ft, td], 'jca', '( %s -> ( f e. NN /\\ t e. %s ) )' % (At, DB('f'))), w.inst('dchrcondinv')], 'syl', '( %s -> ( f DChrCond %s ) = ( f DChrCond t ) )' % (At, IFt))
    cond = w.s([w.s([ci, cv], 'eqtrd', '( %s -> ( Q DChrCond %s ) = ( f DChrCond t ) )' % (At, EMB('f', 'Q', 't'))), tc], 'eqtrd', '( %s -> ( Q DChrCond %s ) = f )' % (At, EMB('f', 'Q', 't')))
    rt = w.s([cond], 'ralrimiva', '( %s -> A. t e. %s ( Q DChrCond %s ) = f )' % (A1, PC('f'), EMB('f', 'Q', 't')))
    eq = 'x = %s' % EMB('f', 'Q', 't'); idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    wst, ch = w.wcongr('( Q DChrCond x ) = f', {'x': EMB('f', 'Q', 't')}, eq, {'x': idst})
    rr = w.s([w.s([], 'eqid', '%s = %s' % (FM('f'), FM('f'))), wst], 'ralrnmptw', '( A. t e. %s %s e. _V -> ( A. x e. %s ( Q DChrCond x ) = f <-> A. t e. %s %s ) )' % (PC('f'), EMB('f', 'Q', 't'), IMG('f'), PC('f'), ch))
    ex = w.s([w.s([], 'fvex', '%s e. _V' % EMB('f', 'Q', 't'))], 'rgenw', 'A. t e. %s %s e. _V' % (PC('f'), EMB('f', 'Q', 't')))
    rx = w.s([rt, w.s([ex, rr], 'ax-mp', '( A. x e. %s ( Q DChrCond x ) = f <-> A. t e. %s %s )' % (IMG('f'), PC('f'), ch))], 'sylibr', '( %s -> A. x e. %s ( Q DChrCond x ) = f )' % (A1, IMG('f')))
    rf = w.s([rx], 'ralrimiva', '( %s -> A. f e. %s A. x e. %s ( Q DChrCond x ) = f )' % (AL, DIVQ, IMG('f')))
    disj = w.s([rf, w.inst('invdisj')], 'syl', '( %s -> Disj_ f e. %s %s )' % (AL, DIVQ, IMG('f')))
    # the image lies in the characters mod Q
    f1 = w.s([], 'lsfiberlem3', '( %s -> %s : %s -1-1-> %s )' % (A1, FM('f'), PC('f'), DQ))
    rs = rnsub(w, A1, f1)
    uss = w.s([w.s([rs], 'ralrimiva', '( %s -> A. f e. %s %s C_ %s )' % (AL, DIVQ, IMG('f'), DQ)), w.s([], 'iunss', '( %s C_ %s <-> A. f e. %s %s C_ %s )' % (UIMG, DQ, DIVQ, IMG('f'), DQ))], 'sylibr', '( %s -> %s C_ %s )' % (AL, UIMG, DQ))
    Afx = '( %s /\\ ( f e. %s /\\ x e. %s ) )' % (AL, DIVQ, IMG('f'))
    fx = w.s([], 'simpr', '( %s -> ( f e. %s /\\ x e. %s ) )' % (Afx, DIVQ, IMG('f')))
    xin = w.s([w.s([rs], 'adantrr', '( %s -> %s C_ %s )' % (Afx, IMG('f'), DQ)), w.s([fx], 'simprd', '( %s -> x e. %s )' % (Afx, IMG('f')))], 'sseldd', '( %s -> x e. %s )' % (Afx, DQ))

    hx, _ = hcl(w, Afx, w.s([q], 'adantr', '( %s -> Q e. NN )' % Afx), w.s([hw], 'adantr', '( %s -> %s )' % (Afx, HW)), xin)
    iu = w.s([dfin, ifin, disj, w.s([hx], 'recnd', '( %s -> %s e. CC )' % (Afx, H('x')))], 'fsumiun', '( %s -> sum_ x e. %s %s = sum_ f e. %s sum_ x e. %s %s )' % (AL, UIMG, H('x'), DIVQ, IMG('f'), H('x')))
    Ax = '( %s /\\ x e. %s )' % (AL, DQ)
    hq, hq0 = hcl(w, Ax, w.s([q], 'adantr', '( %s -> Q e. NN )' % Ax), w.s([hw], 'adantr', '( %s -> %s )' % (Ax, HW)), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, DQ)))
    g0 = w.s([], 'eqid', '( DChr ` Q ) = ( DChr ` Q )'); d0 = w.s([], 'eqid', '%s = %s' % (DQ, DQ))
    dqf = w.s([q, w.s([g0, d0], 'dchrfi', '( Q e. NN -> %s e. Fin )' % DQ)], 'syl', '( %s -> %s e. Fin )' % (AL, DQ))
    le = w.s([dqf, hq, hq0, uss], 'fsumless', '( %s -> sum_ x e. %s %s <_ sum_ x e. %s %s )' % (AL, UIMG, H('x'), DQ, H('x')))
    c1 = w.s([a, iu], 'eqtr4d', '( %s -> sum_ f e. %s ( f x. %s ) = sum_ x e. %s %s )' % (AL, DIVQ, BLK('f'), UIMG, H('x')))
    w.qed([c1, le], 'eqbrtrd', '( %s -> sum_ f e. %s ( f x. %s ) <_ sum_ x e. %s %s )' % (AL, DIVQ, BLK('f'), DQ, H('x'))); run(w)

    # ---- lsfiberlem6: Parseval over the characters mod Q and the bridge (Lean hpars, hbridge)
    GM = '( j e. %s |-> %s )' % (CRQ, TZ('Q', 'j'))
    def SG(x): return 'sum_ u e. %s ( %s x. ( %s ` u ) )' % (CRQ, EV(x, 'Q', 'u'), GM)
    w = W('lsfiberlem6', 'Lemma for lsfiber: the sum over all characters mod Q of the squared twisted unit averages is phi ( Q ) times the sum over the coprime residues u of the squared recentred exponential sums at u / Q (Lean hpars, hbridge).')
    q, m, hw, cop = al_parts(w, AL, w.s([], 'id', '( %s -> %s )' % (AL, AL)))
    Aj = '( %s /\\ j e. %s )' % (AL, CRQ)
    tj = tzcl(w, Aj, w.s([q], 'adantr', '( %s -> Q e. NN )' % Aj), w.s([hw], 'adantr', '( %s -> %s )' % (Aj, HW)), w.s([], 'simpr', '( %s -> j e. %s )' % (Aj, CRQ)), 'j')
    gf = w.s([tj, w.s([], 'eqid', '%s = %s' % (GM, GM))], 'fmptd', '( %s -> %s : %s --> CC )' % (AL, GM, CRQ))
    par = w.s([q, gf, w.inst('dchrparu')], 'syl2anc', '( %s -> sum_ x e. %s %s = ( %s x. sum_ u e. %s %s ) )' % (AL, DQ, ABS2(SG('x')), PHI, CRQ, ABS2('( %s ` u )' % GM)))
    Au = '( %s /\\ u e. %s )' % (AL, CRQ)
    umem = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, CRQ))
    tu = tzcl(w, Au, w.s([q], 'adantr', '( %s -> Q e. NN )' % Au), w.s([hw], 'adantr', '( %s -> %s )' % (Au, HW)), umem)
    gv = fvmd(w, Au, 'j', CRQ, TZ('Q', 'j'), 'u', umem, w.s([tu], 'elexd', '( %s -> %s e. _V )' % (Au, TZ('Q', 'u'))))
    Axu = '( ( %s /\\ x e. %s ) /\\ u e. %s )' % (AL, DQ, CRQ)
    gv2 = w.s([gv], 'adantlr', '( %s -> ( %s ` u ) = %s )' % (Axu, GM, TZ('Q', 'u')))
    inner = w.s([w.s([gv2], 'oveq2d', '( %s -> ( %s x. ( %s ` u ) ) = ( %s x. %s ) )' % (Axu, EV('x', 'Q', 'u'), GM, EV('x', 'Q', 'u'), TZ('Q', 'u')))], 'sumeq2dv', '( ( %s /\\ x e. %s ) -> %s = sum_ u e. %s ( %s x. %s ) )' % (AL, DQ, SG('x'), CRQ, EV('x', 'Q', 'u'), TZ('Q', 'u')))
    Ax = '( %s /\\ x e. %s )' % (AL, DQ)
    l1 = w.s([w.s([w.s([inner], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` sum_ u e. %s ( %s x. %s ) ) )' % (Ax, SG('x'), CRQ, EV('x', 'Q', 'u'), TZ('Q', 'u')))], 'oveq1d', '( %s -> %s = %s )' % (Ax, ABS2(SG('x')), H('x')))], 'sumeq2dv', '( %s -> sum_ x e. %s %s = sum_ x e. %s %s )' % (AL, DQ, ABS2(SG('x')), DQ, H('x')))
    r1 = w.s([w.s([w.s([gv], 'fveq2d', '( %s -> ( abs ` ( %s ` u ) ) = ( abs ` %s ) )' % (Au, GM, TZ('Q', 'u')))], 'oveq1d', '( %s -> %s = %s )' % (Au, ABS2('( %s ` u )' % GM), ABS2(TZ('Q', 'u')))), w.s([], 'lsfiberlem1', '( %s -> %s = %s )' % (Au, ABS2(TZ('Q', 'u')), ESQ))], 'eqtrd', '( %s -> %s = %s )' % (Au, ABS2('( %s ` u )' % GM), ESQ))
    r2 = w.s([w.s([r1], 'sumeq2dv', '( %s -> sum_ u e. %s %s = sum_ u e. %s %s )' % (AL, CRQ, ABS2('( %s ` u )' % GM), CRQ, ESQ))], 'oveq2d', '( %s -> ( %s x. sum_ u e. %s %s ) = ( %s x. sum_ u e. %s %s ) )' % (AL, PHI, CRQ, ABS2('( %s ` u )' % GM), PHI, CRQ, ESQ))
    w.qed([w.s([l1, par], 'eqtr3d', '( %s -> sum_ x e. %s %s = ( %s x. sum_ u e. %s %s ) )' % (AL, DQ, H('x'), PHI, CRQ, ABS2('( %s ` u )' % GM))), r2], 'eqtrd', '( %s -> sum_ x e. %s %s = ( %s x. sum_ u e. %s %s ) )' % (AL, DQ, H('x'), PHI, CRQ, ESQ)); run(w)

    # ---- lsfiber
    S1 = 'sum_ f e. %s ( f x. %s )' % (DIVQ, BLK('f')); S2 = 'sum_ x e. %s %s' % (DQ, H('x')); RR_ = 'sum_ u e. %s %s' % (CRQ, ESQ)
    w = W('lsfiber', 'The per-modulus block bound of the multiplicative large sieve (LargeSieve fiber_block_le): for coefficients on a finite set of integers coprime to Q, the sum over the divisors f of Q with squarefree cofactor coprime to f of f / phi ( Q ) times the primitive-character block mod f is at most the sum over the coprime residues u mod Q of the squared recentred exponential sums at the Farey points u / Q.')
    q, m, hw, cop = al_parts(w, AL, w.s([], 'id', '( %s -> %s )' % (AL, AL)))
    ph = w.s([q, w.inst('phicl')], 'syl', '( %s -> %s e. NN )' % (AL, PHI))
    phc = w.s([ph], 'nncnd', '( %s -> %s e. CC )' % (AL, PHI)); phn = w.s([ph], 'nnne0d', '( %s -> %s =/= 0 )' % (AL, PHI))
    dfin = divfin(w, AL, q)
    A1 = '( %s /\\ f e. %s )' % (AL, DIVQ)
    fnn, dv, sq = divparts(w, A1, w.s([], 'simpr', '( %s -> f e. %s )' % (A1, DIVQ)))
    Ax = '( %s /\\ x e. %s )' % (A1, PC('f'))
    xd, _ = pcparts(w, Ax, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, PC('f'))), 'f', 'x')
    Axn = '( %s /\\ n e. W )' % Ax
    nz, an = win(w, Axn, w.s([w.s([w.s([hw], 'adantr', '( %s -> %s )' % (A1, HW))], 'adantr', '( %s -> %s )' % (Ax, HW))], 'adantr', '( %s -> %s )' % (Axn, HW)), w.s([], 'simpr', '( %s -> n e. W )' % Axn))
    g, z, d, l = dchyp(w, 'f')
    xn = w.s([g, z, d, l, w.s([xd], 'adantr', '( %s -> x e. %s )' % (Axn, DB('f'))), nz], 'dchrzrhcl', '( %s -> %s e. CC )' % (Axn, EV('x', 'f', 'n')))
    ws = w.s([w.s([w.s([w.s([hw], 'simp1d', '( %s -> W e. Fin )' % AL)], 'adantr', '( %s -> W e. Fin )' % A1)], 'adantr', '( %s -> W e. Fin )' % Ax), w.s([an, xn], 'mulcld', '( %s -> ( ( A ` n ) x. %s ) e. CC )' % (Axn, EV('x', 'f', 'n')))], 'fsumcl', '( %s -> %s e. CC )' % (Ax, WSUM('x', 'f')))
    wsq = w.s([w.s([ws], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ax, WSUM('x', 'f')))], 'resqcld', '( %s -> %s e. RR )' % (Ax, ABS2(WSUM('x', 'f'))))
    blk = w.s([pcfin(w, A1, fnn), wsq], 'fsumrecl', '( %s -> %s e. RR )' % (A1, BLK('f')))
    fb = w.s([w.s([fnn], 'nnred', '( %s -> f e. RR )' % A1), blk], 'remulcld', '( %s -> ( f x. %s ) e. RR )' % (A1, BLK('f')))
    phc1 = w.s([phc], 'adantr', '( %s -> %s e. CC )' % (A1, PHI)); phn1 = w.s([phn], 'adantr', '( %s -> %s =/= 0 )' % (A1, PHI))
    e1 = w.s([w.s([fnn], 'nncnd', '( %s -> f e. CC )' % A1), w.s([blk], 'recnd', '( %s -> %s e. CC )' % (A1, BLK('f'))), phc1, phn1], 'div23d', '( %s -> ( ( f x. %s ) / %s ) = ( ( f / %s ) x. %s ) )' % (A1, BLK('f'), PHI, PHI, BLK('f')))
    s1 = w.s([w.s([e1], 'eqcomd', '( %s -> ( ( f / %s ) x. %s ) = ( ( f x. %s ) / %s ) )' % (A1, PHI, BLK('f'), BLK('f'), PHI))], 'sumeq2dv', '( %s -> sum_ f e. %s ( ( f / %s ) x. %s ) = sum_ f e. %s ( ( f x. %s ) / %s ) )' % (AL, DIVQ, PHI, BLK('f'), DIVQ, BLK('f'), PHI))
    s2 = w.s([dfin, phc, w.s([fb], 'recnd', '( %s -> ( f x. %s ) e. CC )' % (A1, BLK('f'))), phn], 'fsumdivc', '( %s -> ( %s / %s ) = sum_ f e. %s ( ( f x. %s ) / %s ) )' % (AL, S1, PHI, DIVQ, BLK('f'), PHI))
    c1 = w.s([s1, s2], 'eqtr4d', '( %s -> sum_ f e. %s ( ( f / %s ) x. %s ) = ( %s / %s ) )' % (AL, DIVQ, PHI, BLK('f'), S1, PHI))
    s1r = w.s([dfin, fb], 'fsumrecl', '( %s -> %s e. RR )' % (AL, S1))
    Ax2 = '( %s /\\ x e. %s )' % (AL, DQ)
    hq, _ = hcl(w, Ax2, w.s([q], 'adantr', '( %s -> Q e. NN )' % Ax2), w.s([hw], 'adantr', '( %s -> %s )' % (Ax2, HW)), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax2, DQ)))
    g0 = w.s([], 'eqid', '( DChr ` Q ) = ( DChr ` Q )'); d0 = w.s([], 'eqid', '%s = %s' % (DQ, DQ))
    dqf = w.s([q, w.s([g0, d0], 'dchrfi', '( Q e. NN -> %s e. Fin )' % DQ)], 'syl', '( %s -> %s e. Fin )' % (AL, DQ))
    s2r = w.s([dqf, hq], 'fsumrecl', '( %s -> %s e. RR )' % (AL, S2))
    le = w.s([s1r, s2r, w.s([ph], 'nnrpd', '( %s -> %s e. RR+ )' % (AL, PHI)), w.s([], 'lsfiberlem5', '( %s -> %s <_ %s )' % (AL, S1, S2))], 'lediv1dd', '( %s -> ( %s / %s ) <_ ( %s / %s ) )' % (AL, S1, PHI, S2, PHI))
    p6 = w.s([], 'lsfiberlem6', '( %s -> %s = ( %s x. %s ) )' % (AL, S2, PHI, RR_))
    Au = '( %s /\\ u e. %s )' % (AL, CRQ)
    umem = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, CRQ))
    Aun = '( %s /\\ n e. W )' % Au
    nz2, an2 = win(w, Aun, w.s([w.s([hw], 'adantr', '( %s -> %s )' % (Au, HW))], 'adantr', '( %s -> %s )' % (Aun, HW)), w.s([], 'simpr', '( %s -> n e. W )' % Aun))
    uz = crz(w, Au, umem, 'u', 'Q')
    uq = w.s([w.s([w.s([uz], 'zred', '( %s -> u e. RR )' % Au), w.s([w.s([q], 'adantr', '( %s -> Q e. NN )' % Au)], 'nnred', '( %s -> Q e. RR )' % Au), w.s([w.s([q], 'adantr', '( %s -> Q e. NN )' % Au)], 'nnne0d', '( %s -> Q =/= 0 )' % Au)], 'redivcld', '( %s -> ( u / Q ) e. RR )' % Au)], 'adantr', '( %s -> ( u / Q ) e. RR )' % Aun)
    nm = w.s([w.s([nz2], 'zcnd', '( %s -> n e. CC )' % Aun), w.s([w.s([w.s([m], 'adantr', '( %s -> M e. RR )' % Au)], 'adantr', '( %s -> M e. RR )' % Aun)], 'recnd', '( %s -> M e. CC )' % Aun)], 'subcld', '( %s -> ( n - M ) e. CC )' % Aun)
    ea = w.s([nm, w.s([uq], 'recnd', '( %s -> ( u / Q ) e. CC )' % Aun), w.inst('eatcl')], 'syl2anc', '( %s -> %s e. CC )' % (Aun, EAT('( n - M )', '( u / Q )')))
    es = w.s([w.s([w.s([hw], 'simp1d', '( %s -> W e. Fin )' % AL)], 'adantr', '( %s -> W e. Fin )' % Au), w.s([an2, ea], 'mulcld', '( %s -> ( ( A ` n ) x. %s ) e. CC )' % (Aun, EAT('( n - M )', '( u / Q )')))], 'fsumcl', '( %s -> %s e. CC )' % (Au, ESUM('( n - M )', '( u / Q )')))
    esq = w.s([w.s([es], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Au, ESUM('( n - M )', '( u / Q )')))], 'resqcld', '( %s -> %s e. RR )' % (Au, ESQ))
    rc = w.s([w.s([crfin(w, AL, 'Q'), esq], 'fsumrecl', '( %s -> %s e. RR )' % (AL, RR_))], 'recnd', '( %s -> %s e. CC )' % (AL, RR_))
    e3 = w.s([w.s([p6], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s x. %s ) / %s ) )' % (AL, S2, PHI, PHI, RR_, PHI)), w.s([rc, phc, phn], 'divcan3d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (AL, PHI, RR_, PHI, RR_))], 'eqtrd', '( %s -> ( %s / %s ) = %s )' % (AL, S2, PHI, RR_))
    w.qed([w.s([c1, le], 'eqbrtrd', '( %s -> sum_ f e. %s ( ( f / %s ) x. %s ) <_ ( %s / %s ) )' % (AL, DIVQ, PHI, BLK('f'), S2, PHI)), e3], 'breqtrd', '( %s -> sum_ f e. %s ( ( f / %s ) x. %s ) <_ %s )' % (AL, DIVQ, PHI, BLK('f'), RR_)); run(w)
    assert '( %s -> sum_ f e. %s ( ( f / %s ) x. %s ) <_ %s )' % (AL, DIVQ, PHI, BLK('f'), RR_) == S_lsfiber()
