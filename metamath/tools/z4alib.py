"""Shared expressions of sortie Z4a (LargeSieve.lean 495-1800: the Gauss-sum
transfer, the unit-group Parseval, the induced-character step and the
per-modulus block bound of the large sieve)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zf2lib import DB, LZ, BZ, UZ, ONE, MUL, INV, IND, INDOP, COND, FZO, EV, COP
from zf4lib import E, GS, R, RP, HC, dchyp, sylanc, zrh_el, dchr_conj, fsumf1o, cbvsum

def CR(n): return '{ k e. ( 0 ..^ %s ) | ( k gcd %s ) = 1 }' % (n, n)
def PC(f): return '{ y e. %s | ( %s DChrCond y ) = %s }' % (DB(f), f, f)
def DIV(q): return '{ d e. NN | ( d || %s /\\ ( ( mmu ` ( %s / d ) ) =/= 0 /\\ ( ( %s / d ) gcd d ) = 1 ) ) }' % (q, q, q)
def EAT(v, b): return '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. %s ) ) )' % (v, b)
HW = '( W e. Fin /\\ W C_ ZZ /\\ A : W --> CC )'
def COPALL(n): return 'A. m e. W ( m gcd %s ) = 1' % n
def AN(n='n'): return '( A ` %s )' % n
def TZ(n, u, nv='n'):
    """sum_ n e. W ( ( A ` n ) x. E_N( ( n x. u ) ) ) (Lean Tzu u)"""
    return 'sum_ %s e. W ( ( A ` %s ) x. %s )' % (nv, nv, E('( %s x. %s )' % (nv, u), n))
def ABS2(e): return '( ( abs ` %s ) ^ 2 )' % e
def CJ(e): return '( * ` %s )' % e
def WSUM(x, f, nv='n'): return 'sum_ %s e. W ( ( A ` %s ) x. %s )' % (nv, nv, EV(x, f, nv))
def BLK(f): return 'sum_ x e. %s %s' % (PC(f), ABS2(WSUM('x', f)))
def EMB(f, q, y): return IND(f, q, '( %s ` %s )' % (INV(f), y))
def IX(x, n, u): return '( ( %s ` %s ) ` ( %s ` %s ) )' % (INV(n), x, LZ(n), u)
def ESUM(m, b, nv='n'): return 'sum_ %s e. W ( ( A ` %s ) x. %s )' % (nv, nv, EAT(m, b))

# the frozen statements
def S_dchrtwsum(n='N', x='X'):
    return '( ( %s /\\ %s /\\ %s ) -> sum_ u e. %s ( %s x. %s ) = ( %s x. sum_ n e. W ( ( A ` n ) x. %s ) ) )' % (
        '( %s e. NN /\\ %s e. %s )' % (n, x, DB(n)), HW, COPALL(n), CR(n), EV(x, n, 'u'), TZ(n, 'u'), GS(n, x), IX(x, n, 'n'))
def S_dchrparu(n='N'):
    return '( ( %s e. NN /\\ G : %s --> CC ) -> sum_ x e. %s %s = ( ( phi ` %s ) x. sum_ u e. %s %s ) )' % (
        n, CR(n), DB(n), ABS2('sum_ u e. %s ( %s x. ( G ` u ) )' % (CR(n), EV('x', n, 'u'))), n, CR(n), ABS2('( G ` u )'))
HWN = '( ( Q e. NN /\\ F e. NN /\\ F || Q ) /\\ ( ( mmu ` ( Q / F ) ) =/= 0 /\\ ( ( Q / F ) gcd F ) = 1 ) /\\ ( Y e. %s /\\ ( F DChrCond Y ) = F ) )' % DB('F')
def S_dchrwnorm():
    return '( ( %s /\\ %s /\\ %s ) -> %s = ( F x. %s ) )' % (
        HWN, HW, COPALL('Q'), ABS2('sum_ u e. %s ( %s x. %s )' % (CR('Q'), EV(EMB('F', 'Q', 'Y'), 'Q', 'u'), TZ('Q', 'u'))), ABS2(WSUM('Y', 'F')))
def S_lsfiber():
    return '( ( ( Q e. NN /\\ M e. RR ) /\\ %s /\\ %s ) -> sum_ f e. %s ( ( f / ( phi ` Q ) ) x. %s ) <_ sum_ u e. %s %s )' % (
        HW, COPALL('Q'), DIV('Q'), BLK('f'), CR('Q'), ABS2(ESUM('( n - M )', '( u / Q )')))


def hyp(w, i, ref, formula):
    """an $e hypothesis step h<i>::REF |- formula; mmj2 names the step <i>"""
    w.s([], ref, formula, name='h%d' % i)
    return str(i)


C2 = '( 2 x. ( _i x. _pi ) )'
def c2cl(w, ante):
    ip = w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')
    c = w.s([w.s([], '2cn', '2 e. CC'), ip], 'mulcli', '%s e. CC' % C2)
    return w.s([c], 'a1i', '( %s -> %s e. CC )' % (ante, C2))


def ecl(w, ante, nst, ast, A, n='N'):
    """( ante -> E_n( A ) e. CC ) from nst: n e. NN, ast: A e. CC"""
    q = w.s([ast, w.s([nst], 'nncnd', '( %s -> %s e. CC )' % (ante, n)), w.s([nst], 'nnne0d', '( %s -> %s =/= 0 )' % (ante, n))], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (ante, A, n))
    return w.s([w.s([c2cl(w, ante), q], 'mulcld', '( %s -> ( %s x. ( %s / %s ) ) e. CC )' % (ante, C2, A, n))], 'efcld', '( %s -> %s e. CC )' % (ante, E(A, n)))


def crfin(w, ante, n='N'):
    """( ante -> CR(n) e. Fin )"""
    f = w.s([w.s([], 'fzofi', '%s e. Fin' % FZO(n)), w.inst('rabfi')], 'ax-mp', '%s e. Fin' % CR(n))
    return w.s([f], 'a1i', '( %s -> %s e. Fin )' % (ante, CR(n)))


def crz(w, ante, mem, u='u', n='N'):
    """( ante -> u e. ZZ ) from mem: ( ante -> u e. CR(n) )"""
    return w.s([w.s([mem, w.inst('elrabi')], 'syl', '( %s -> %s e. %s )' % (ante, u, FZO(n))), w.inst('elfzoelz')], 'syl', '( %s -> %s e. ZZ )' % (ante, u))


def crcop(w, ante, mem, u='u', n='N'):
    """( ante -> ( u gcd n ) = 1 ) from mem: ( ante -> u e. CR(n) )"""
    sub = w.s([w.s([], 'oveq1', '( k = %s -> ( k gcd %s ) = ( %s gcd %s ) )' % (u, n, u, n))], 'eqeq1d', '( k = %s -> ( ( k gcd %s ) = 1 <-> ( %s gcd %s ) = 1 ) )' % (u, n, u, n))
    er = w.s([sub], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ ( %s gcd %s ) = 1 ) )' % (u, CR(n), u, FZO(n), u, n))
    return w.s([w.s([mem, er], 'sylib', '( %s -> ( %s e. %s /\\ ( %s gcd %s ) = 1 ) )' % (ante, u, FZO(n), u, n))], 'simprd', '( %s -> ( %s gcd %s ) = 1 )' % (ante, u, n))


def grpinv(w, ante, nst, xst, n='N', x='X'):
    """( ante -> ( IN ` X ) e. DN )"""
    g = w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n))
    ab = w.s([nst, w.s([g], 'dchrabl', '( %s e. NN -> ( DChr ` %s ) e. Abel )' % (n, n))], 'syl', '( %s -> ( DChr ` %s ) e. Abel )' % (ante, n))
    gr = w.s([ab, w.inst('ablgrp')], 'syl', '( %s -> ( DChr ` %s ) e. Grp )' % (ante, n))
    d = w.s([], 'eqid', '%s = %s' % (DB(n), DB(n))); i = w.s([], 'eqid', '%s = %s' % (INV(n), INV(n)))
    return w.s([gr, xst, w.s([d, i], 'grpinvcl', '( ( ( DChr ` %s ) e. Grp /\\ %s e. %s ) -> ( %s ` %s ) e. %s )' % (n, x, DB(n), INV(n), x, DB(n)))], 'syl2anc', '( %s -> ( %s ` %s ) e. %s )' % (ante, INV(n), x, DB(n)))


def ixcl(w, ante, nst, xst, ast, n='N', x='X', A='A'):
    """( ante -> ( ( IN ` X ) ` ( LN ` A ) ) e. CC )"""
    ix = grpinv(w, ante, nst, xst, n, x)
    g, z, d, l = dchyp(w, n)
    return w.s([g, z, d, l, ix, ast], 'dchrzrhcl', '( %s -> %s e. CC )' % (ante, IX(x, n, A)))


def win(w, ante, hwst, nmem, n='n'):
    """(nz, an): ( ante -> n e. ZZ ), ( ante -> ( A ` n ) e. CC ) from hwst: ( ante -> HW ), nmem: ( ante -> n e. W )"""
    wss = w.s([hwst], 'simp2d', '( %s -> W C_ ZZ )' % ante); af = w.s([hwst], 'simp3d', '( %s -> A : W --> CC )' % ante)
    nz = w.s([wss, nmem, w.inst('ssel2')], 'syl2anc', '( %s -> %s e. ZZ )' % (ante, n))
    an = w.s([af, nmem], 'ffvelcdmd', '( %s -> ( A ` %s ) e. CC )' % (ante, n))
    return nz, an


def copn(w, ante, copst, nmem, n='N', v='n'):
    """( ante -> ( v gcd n ) = 1 ) from copst: ( ante -> A. m e. W ( m gcd n ) = 1 ), nmem: ( ante -> v e. W )"""
    sub = w.s([w.s([], 'oveq1', '( m = %s -> ( m gcd %s ) = ( %s gcd %s ) )' % (v, n, v, n))], 'eqeq1d', '( m = %s -> ( ( m gcd %s ) = 1 <-> ( %s gcd %s ) = 1 ) )' % (v, n, v, n))
    return w.s([sub, copst, nmem], 'rspcdva', '( %s -> ( %s gcd %s ) = 1 )' % (ante, v, n))
