"""Sortie v2b: shared expressions for the Selberg sieve block."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W


# ---------------------------------------------------------------- expressions
def PF(X, v='r'):
    """the set of prime divisors of X, as a rab over v"""
    return '{ %s e. Prime | %s || %s }' % (v, v, X)


def OM(X, v='r'):
    return '( # ` %s )' % PF(X, v)


def DV(X, v='x'):
    """the divisors of X"""
    return '{ %s e. NN | %s || %s }' % (v, v, X)


def GT(X, q='q'):
    """the Selberg term g( X )"""
    return '( ( V ` %s ) x. prod_ %s e. %s ( 1 / ( 1 - ( V ` %s ) ) ) )' % (X, q, PF(X), q)


def SSTERM(l='l'):
    return 'if ( ( %s ^ 2 ) <_ Y , %s , 0 )' % (l, GT(l))


def SS(l='l'):
    return 'sum_ %s e. %s %s' % (l, DV('P'), SSTERM(l))


def LW(D, m='m', l='l'):
    """the Selberg weight lambda_D"""
    inner = ('sum_ %s e. %s if ( ( ( ( %s x. %s ) ^ 2 ) <_ Y /\\ ( %s gcd %s ) = 1 ) , %s , 0 )'
             % (m, DV('P'), D, m, m, D, GT(m)))
    return ('if ( %s || P , ( ( ( ( 1 / ( V ` %s ) ) x. %s ) x. ( ( mmu ` %s ) x. ( 1 / %s ) ) ) '
            'x. %s ) , 0 )' % (D, D, GT(D), D, SS(l), inner))


def INTERM(D, m='m'):
    return ('if ( ( ( ( %s x. %s ) ^ 2 ) <_ Y /\\ ( %s gcd %s ) = 1 ) , %s , 0 )'
            % (D, m, m, D, GT(m)))


def INNER(D, m='m'):
    return 'sum_ %s e. %s %s' % (m, DV('P'), INTERM(D, m))


def FAC(D, l='l'):
    return ('( ( ( 1 / ( V ` %s ) ) x. %s ) x. ( ( mmu ` %s ) x. ( 1 / %s ) ) )'
            % (D, GT(D), D, SS(l)))


def MP(N, d='d', e='e'):
    """the Selberg Lambda squared coefficient at N"""
    return ('sum_ %s e. %s sum_ %s e. %s if ( %s = ( %s lcm %s ) , ( %s x. %s ) , 0 )'
            % (d, DV(N), e, DV(N), N, d, e, LW(d), LW(e)))


def MS(D, n='n'):
    return 'sum_ %s e. A if ( %s || %s , ( W ` %s ) , 0 )' % (n, D, n, n)


def RM(D, n='n'):
    return '( %s - ( ( V ` %s ) x. X ) )' % (MS(D, n), D)


SF = 'sum_ n e. A if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )'

# ---------------------------------------------------------------- hypotheses
SH_A = '( A e. Fin /\\ A C_ NN /\\ W : NN --> RR )'
SH_B = '( A. k e. NN 0 <_ ( W ` k ) /\\ X e. RR /\\ ( Y e. RR /\\ 1 <_ Y ) )'
SH_P = '( P e. NN /\\ ( mmu ` P ) =/= 0 )'
VMUL = ('A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> '
        '( V ` ( a x. b ) ) = ( ( V ` a ) x. ( V ` b ) ) )')
VPRM = 'A. s e. Prime ( s || P -> ( 0 < ( V ` s ) /\\ ( V ` s ) < 1 ) )'
SH_V = '( V : NN --> RR /\\ ( V ` 1 ) = 1 /\\ ( %s /\\ %s ) )' % (VMUL, VPRM)
SH = '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (SH_A, SH_B, SH_P, SH_V)

VH = '( V : NN --> RR /\\ ( V ` 1 ) = 1 /\\ %s )' % VMUL


def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))


def shsteps(w, ante, chain=()):
    """Extract the sieve hypotheses under the antecedent `ante`.

    `chain` lists the successive sub-antecedents from `ante` down to SH
    (exclusive of `ante`, inclusive of SH), each the left conjunct of the
    previous.  Returns a dict of step names.
    """
    st = mkst(w, ante)
    cur = w.s([], 'id', '( %s -> %s )' % (ante, ante))
    for nxt in chain:
        ref = 'simpld'
        if isinstance(nxt, tuple):
            nxt, ref = nxt
        cur = w.s([cur], ref, '( %s -> %s )' % (ante, nxt))
    d = {'sh': cur}
    ab = st([cur], 'simpld', '( %s /\\ %s )' % (SH_A, SH_B))
    pv = st([cur], 'simprd', '( %s /\\ %s )' % (SH_P, SH_V))
    a3 = st([ab], 'simpld', SH_A)
    b3 = st([ab], 'simprd', SH_B)
    p2 = st([pv], 'simpld', SH_P)
    v3 = st([pv], 'simprd', SH_V)
    d['afin'] = st([a3], 'simp1d', 'A e. Fin')
    d['assnn'] = st([a3], 'simp2d', 'A C_ NN')
    d['wf'] = st([a3], 'simp3d', 'W : NN --> RR')
    d['wge0'] = st([b3], 'simp1d', 'A. k e. NN 0 <_ ( W ` k )')
    d['xr'] = st([b3], 'simp2d', 'X e. RR')
    yr = st([b3], 'simp3d', '( Y e. RR /\\ 1 <_ Y )')
    d['yr'] = st([yr], 'simpld', 'Y e. RR')
    d['y1'] = st([yr], 'simprd', '1 <_ Y')
    d['pnn'] = st([p2], 'simpld', 'P e. NN')
    d['psqf'] = st([p2], 'simprd', '( mmu ` P ) =/= 0')
    d['vf'] = st([v3], 'simp1d', 'V : NN --> RR')
    d['v1'] = st([v3], 'simp2d', '( V ` 1 ) = 1')
    mp = st([v3], 'simp3d', '( %s /\\ %s )' % (VMUL, VPRM))
    d['vmul'] = st([mp], 'simpld', VMUL)
    d['vprm'] = st([mp], 'simprd', VPRM)
    d['vh'] = st([d['vf'], d['v1'], d['vmul']], '3jca', VH)
    d['st'] = st
    return d
