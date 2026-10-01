"""Closed facts about numeral literals for mmj2 worksheets (sortie G).

A literal is a set.mm numeral (`0`..`9`, decimals `; 1 2`, `; ; 5 6 1`), a
negated literal `-u 3`, or a fraction `( p / q )` of positive numerals, and
`-u ( p / q )`.  Values are fractions.Fraction.  Every function takes the
worksheet builder `w` (tools/tm.py `W`) and returns the name of a closed
step (no antecedent) that it appends to the worksheet; steps are memoized by
formula in `w.memo`, so repeated requests cost nothing.

    lit_value('; 1 2')          -> Fraction(12)
    lit_text(Fraction(-3, 2))   -> '-u ( 3 / 2 )'
    add_nat(w, 17, 25)          -> step proving ( ; 1 7 + ; 2 5 ) = ; 4 2
    mul_nat(w, 12, 12)          -> step proving ( ; 1 2 x. ; 1 2 ) = ; ; 1 4 4
    add_int(w, 2, -5)           -> step proving ( 2 + -u 5 ) = -u 3
    mul_lit(w, -2, '( 3 / 2 )') -> step proving ( -u 2 x. ( 3 / 2 ) ) = -u 3
    cc(w, '-u ( 3 / 2 )')       -> step proving -u ( 3 / 2 ) e. CC
    fact(w, '; 1 2', 'NN')      -> step proving ; 1 2 e. NN
    fact(w, '( 1 / 2 )', 'gt0') -> step proving 0 < ( 1 / 2 )

Digit sums and products come from set.mm's tables (`7p5e12`, `9t8e72`,
flipped with `addcomi`/`mulcomi` when only the other orientation exists);
multi-digit numbers use `decaddi`/`decaddci`, `decadd`/`decaddc`,
`decmul1`/`decmul1c` and `decmul10add`.  Signed sums use `negsubi`,
`subaddrii`, `negsubdi2i`, `negdii`, `negidi`; scaled fractions use
`divassi` and `divmuli`.
"""
import os, re, sys
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_LABELS = None

# set.mm's digit tables, restricted to the labels of its MAIN BODY.  set.mm
# carries one orientation of most pairs in the main body and the other in a
# mathbox (`3p2e5` is main, `2p3e5` is a mathbox theorem; `5t4e20` is main,
# `4t5e20` is a mathbox theorem), so the orientation is chosen from these
# sets and flipped with `addcomi` / `mulcomi` when the direct label is not
# main-body.  Keeping the tables explicit makes the automation independent
# of what the mathboxes happen to contain.
MAIN_ADD = set("""0p1e1 1p0e1 1p1e2 1p2e3 2p1e3 2p2e4 3p1e4 3p2e5 3p3e6 4p1e5
4p2e6 4p3e7 4p4e8 5p1e6 5p2e7 5p3e8 5p4e9 5p5e10 6p1e7 6p2e8 6p3e9 6p4e10
6p5e11 6p6e12 7p1e8 7p2e9 7p3e10 7p4e11 7p5e12 7p6e13 7p7e14 8p1e9 8p2e10
8p3e11 8p4e12 8p5e13 8p6e14 8p7e15 8p8e16 9p1e10 9p2e11 9p3e12 9p4e13 9p5e14
9p6e15 9p7e16 9p8e17 9p9e18""".split())

MAIN_MUL = set("""1t1e1 2t0e0 2t1e2 2t2e4 2t3e6 2t4e8 3t1e3 3t2e6 3t3e9 4t2e8
4t3e12 4t4e16 5t2e10 5t3e15 5t4e20 5t5e25 6t2e12 6t3e18 6t4e24 6t5e30 6t6e36
7t2e14 7t3e21 7t4e28 7t5e35 7t6e42 7t7e49 8t2e16 8t3e24 8t4e32 8t5e40 8t6e48
8t7e56 8t8e64 9t2e18 9t3e27 9t4e36 9t5e45 9t6e54 9t7e63 9t8e72 9t9e81""".split())

# the digit facts whose one-symbol labels are main-body (`4rp`, `6rp`, `9rp`,
# `5ne0` ... `9ne0` are mathbox theorems; those go through `nnrp` / `nnne0i`)
MAIN_RP = {1, 2, 3, 5}
MAIN_NE0 = {2, 3, 4}


def labels():
    """set of all assertion labels of set.mm + the database (from mm.py's index)"""
    global _LABELS
    if _LABELS is None:
        import mm
        if not os.path.exists(mm.INDEX):
            mm.build_index()
        _LABELS = set()
        with open(mm.INDEX) as f:
            for l in f:
                _LABELS.add(l.split(' ', 1)[0])
    return _LABELS


# ---------------------------------------------------------------- literals

def nat_text(n):
    """canonical set.mm numeral for a nonnegative integer"""
    n = int(n)
    assert n >= 0
    if n < 10:
        return str(n)
    return '; %s %d' % (nat_text(n // 10), n % 10)


def lit_text(v):
    """canonical literal text for a Fraction"""
    v = Fraction(v)
    if v < 0:
        return '-u ' + lit_text(-v)
    if v.denominator == 1:
        return nat_text(v.numerator)
    return '( %s / %s )' % (nat_text(v.numerator), nat_text(v.denominator))


def _nat_toks(toks, i):
    """parse a numeral at toks[i]; return (value, next index) or None"""
    if i >= len(toks):
        return None
    t = toks[i]
    if re.match(r'^[0-9]$', t):
        return int(t), i + 1
    if t == ';':
        a = _nat_toks(toks, i + 1)
        if a is None:
            return None
        v, j = a
        if j < len(toks) and re.match(r'^[0-9]$', toks[j]) and v > 0:
            return v * 10 + int(toks[j]), j + 1
    return None


def _lit_toks(toks, i):
    if i >= len(toks):
        return None
    if toks[i] == '-u':
        r = _lit_toks(toks, i + 1)
        if r is None:
            return None
        v, j = r
        return -v, j
    if toks[i] == '(':
        a = _nat_toks(toks, i + 1)
        if a is None:
            return None
        p, j = a
        if j < len(toks) and toks[j] == '/':
            b = _nat_toks(toks, j + 1)
            if b is None:
                return None
            q, k = b
            if k < len(toks) and toks[k] == ')' and q > 0:
                return Fraction(p, q), k + 1
        return None
    return _nat_toks(toks, i)


def lit_value(text):
    """Fraction value of a literal, or None if text is not a literal"""
    toks = text.split()
    r = _lit_toks(toks, 0)
    if r is None or r[1] != len(toks):
        return None
    return Fraction(r[0])


def is_lit(text):
    return lit_value(text) is not None


def nat_value(text):
    v = lit_value(text)
    return v.numerator if v is not None and v >= 0 and v.denominator == 1 else None


# ---------------------------------------------------------------- steps

def _memo(w):
    if not hasattr(w, 'memo'):
        w.memo = {}
    return w.memo


def closed(w, hyps, ref, formula):
    """closed step, memoized by formula"""
    m = _memo(w)
    if formula in m:
        return m[formula]
    st = w.s(hyps, ref, formula)
    m[formula] = st
    return st


def _dec(n):
    """split a numeral >= 10 into (high, digit)"""
    return n // 10, n % 10


# closed membership and sign facts for nonnegative integer numerals

def nn0(w, n):
    n = int(n)
    if n < 10:
        return closed(w, [], '%dnn0' % n, '%d e. NN0' % n)
    a, b = _dec(n)
    return closed(w, [nn0(w, a), nn0(w, b)], 'deccl', '%s e. NN0' % nat_text(n))


def nn(w, n):
    n = int(n)
    assert n > 0
    if n < 10:
        return closed(w, [], '%dnn' % n, '%d e. NN' % n)
    a, b = _dec(n)
    if b == 0:
        return closed(w, [nn(w, a)], 'decnncl2', '%s e. NN' % nat_text(n))
    return closed(w, [nn0(w, a), nn(w, b)], 'decnncl', '%s e. NN' % nat_text(n))


def cc_nat(w, n):
    n = int(n)
    if n == 1:
        return closed(w, [], 'ax-1cn', '1 e. CC')
    if n < 10:
        return closed(w, [], '%dcn' % n, '%d e. CC' % n)
    return closed(w, [nn0(w, n)], 'nn0cni', '%s e. CC' % nat_text(n))


def re_nat(w, n):
    n = int(n)
    if n < 10:
        return closed(w, [], '%dre' % n, '%d e. RR' % n)
    return closed(w, [nn0(w, n)], 'nn0rei', '%s e. RR' % nat_text(n))


def z_nat(w, n):
    n = int(n)
    if n < 5:
        return closed(w, [], '%dz' % n, '%d e. ZZ' % n)
    return closed(w, [nn0(w, n)], 'nn0zi', '%s e. ZZ' % nat_text(n))


def rp_nat(w, n):
    n = int(n)
    assert n > 0
    if n in MAIN_RP:
        return closed(w, [], '%drp' % n, '%d e. RR+' % n)
    i = w.inst('nnrp')
    return closed(w, [nn(w, n), i], 'ax-mp', '%s e. RR+' % nat_text(n))


def ge0_nat(w, n):
    n = int(n)
    if n <= 2:
        return closed(w, [], '0le%d' % n, '0 <_ %d' % n)
    return closed(w, [nn0(w, n)], 'nn0ge0i', '0 <_ %s' % nat_text(n))


def gt0_nat(w, n):
    n = int(n)
    assert n > 0
    if n == 1:
        return closed(w, [], '0lt1', '0 < 1')
    if n < 10:
        return closed(w, [], '%dpos' % n, '0 < %d' % n)
    return closed(w, [nn(w, n)], 'nngt0i', '0 < %s' % nat_text(n))


def ne0_nat(w, n):
    n = int(n)
    assert n > 0
    if n == 1:
        return closed(w, [], 'ax-1ne0', '1 =/= 0')
    if n in MAIN_NE0:
        return closed(w, [], '%dne0' % n, '%d =/= 0' % n)
    return closed(w, [nn(w, n)], 'nnne0i', '%s =/= 0' % nat_text(n))


# facts for general literal texts (numeral, -u L, ( p / q ))

def _split_lit(text):
    """('nat', n) | ('neg', inner text) | ('frac', p, q)"""
    toks = text.split()
    if toks[0] == '-u':
        return ('neg', ' '.join(toks[1:]))
    if toks[0] == '(':
        v = lit_value(text)
        return ('frac', v.numerator, v.denominator)
    return ('nat', nat_value(text))


def rp(w, text):
    k = _split_lit(text)
    if k[0] == 'nat':
        return rp_nat(w, k[1])
    if k[0] == 'frac':
        p, q = k[1], k[2]
        i = w.inst('rpdivcl')
        return closed(w, [rp_nat(w, p), rp_nat(w, q), i], 'mp2an', '%s e. RR+' % text)
    raise ValueError('not positive: ' + text)


def cc(w, text):
    k = _split_lit(text)
    if k[0] == 'nat':
        return cc_nat(w, k[1])
    if k[0] == 'neg':
        return closed(w, [cc(w, k[1])], 'negcli', '-u %s e. CC' % k[1])
    i = w.inst('rpcn')
    return closed(w, [rp(w, text), i], 'ax-mp', '%s e. CC' % text)


def real(w, text):
    k = _split_lit(text)
    if k[0] == 'nat':
        return re_nat(w, k[1])
    if k[0] == 'neg':
        return closed(w, [real(w, k[1])], 'renegcli', '-u %s e. RR' % k[1])
    i = w.inst('rpre')
    return closed(w, [rp(w, text), i], 'ax-mp', '%s e. RR' % text)


def fact(w, text, kind):
    """closed step for a literal: kind in NN0 NN ZZ RR CC RR+ ge0 gt0 ne0"""
    k = _split_lit(text)
    if kind == 'CC':
        return cc(w, text)
    if kind == 'RR':
        return real(w, text)
    if kind == 'RR+':
        return rp(w, text)
    if k[0] == 'nat':
        n = k[1]
        if kind == 'NN0':
            return nn0(w, n)
        if kind == 'NN':
            return nn(w, n)
        if kind == 'ZZ':
            return z_nat(w, n)
        if kind == 'ge0':
            return ge0_nat(w, n)
        if kind == 'gt0':
            return gt0_nat(w, n)
        if kind == 'ne0':
            return ne0_nat(w, n)
        if kind == 'gt1' and 2 <= n <= 9:
            return closed(w, [], '1lt%d' % n, '1 < %d' % n)
        if kind == 'ge1' and n >= 1:
            if n <= 3:
                return closed(w, [], '1le%d' % n, '1 <_ %d' % n)
            i = w.inst('nnge1')
            return closed(w, [nn(w, n), i], 'ax-mp', '1 <_ %s' % nat_text(n))
    if k[0] == 'frac':
        lem = {'ge0': 'rpge0', 'gt0': 'rpgt0', 'ne0': 'rpne0'}.get(kind)
        if lem:
            i = w.inst(lem)
            f = {'ge0': '0 <_ %s', 'gt0': '0 < %s', 'ne0': '%s =/= 0'}[kind] % text
            return closed(w, [rp(w, text), i], 'ax-mp', f)
    if k[0] == 'neg' and kind == 'ZZ':
        i = w.inst('znegcl')
        return closed(w, [fact(w, k[1], 'ZZ'), i], 'ax-mp', '%s e. ZZ' % text)
    raise ValueError('no closed fact %s for literal %s' % (kind, text))


# ---------------------------------------------------------------- arithmetic

def _eqid(w, text):
    return closed(w, [], 'eqid', '%s = %s' % (text, text))


def add_nat(w, a, b):
    """closed step: ( a + b ) = c for nonnegative integers"""
    a, b = int(a), int(b)
    ta, tb, tc = nat_text(a), nat_text(b), nat_text(a + b)
    f = '( %s + %s ) = %s' % (ta, tb, tc)
    if f in _memo(w):
        return _memo(w)[f]
    if a == 0:
        return closed(w, [cc_nat(w, b)], 'addlidi', f)
    if b == 0:
        return closed(w, [cc_nat(w, a)], 'addridi', f)
    if a < 10 and b < 10:
        lab = '%dp%de%d' % (a, b, a + b)
        if lab in MAIN_ADD:
            return closed(w, [], lab, f)
        lab2 = '%dp%de%d' % (b, a, a + b)
        assert lab2 in MAIN_ADD, lab
        s1 = closed(w, [cc_nat(w, a), cc_nat(w, b)], 'addcomi', '( %s + %s ) = ( %s + %s )' % (ta, tb, tb, ta))
        s2 = closed(w, [], lab2, '( %s + %s ) = %s' % (tb, ta, tc))
        return closed(w, [s1, s2], 'eqtri', f)
    if a < 10:   # digit + decimal: flip
        s1 = closed(w, [cc_nat(w, a), cc_nat(w, b)], 'addcomi', '( %s + %s ) = ( %s + %s )' % (ta, tb, tb, ta))
        s2 = add_nat(w, b, a)
        return closed(w, [s1, s2], 'eqtri', f)
    A, B = _dec(a)
    if b < 10:   # decimal + digit: decaddi / decaddci
        s = B + b
        if s < 10:
            hyps = [nn0(w, A), nn0(w, B), nn0(w, b), _eqid(w, ta), add_nat(w, B, b)]
            return closed(w, hyps, 'decaddi', f)
        C = s - 10
        hyps = [nn0(w, A), nn0(w, B), nn0(w, b), _eqid(w, ta), add_nat(w, A, 1), nn0(w, C), add_nat(w, B, b)]
        return closed(w, hyps, 'decaddci', f)
    C, D = _dec(b)
    s = B + D
    if s < 10:
        hyps = [nn0(w, A), nn0(w, B), nn0(w, C), nn0(w, D), _eqid(w, ta), _eqid(w, tb), add_nat(w, A, C), add_nat(w, B, D)]
        return closed(w, hyps, 'decadd', f)
    F = s - 10
    # ( ( A + C ) + 1 ) = E
    e1 = add_nat(w, A, C)
    x = A + C
    e2 = closed(w, [e1], 'oveq1i', '( ( %s + %s ) + 1 ) = ( %s + 1 )' % (nat_text(A), nat_text(C), nat_text(x)))
    e3 = add_nat(w, x, 1)
    e4 = closed(w, [e2, e3], 'eqtri', '( ( %s + %s ) + 1 ) = %s' % (nat_text(A), nat_text(C), nat_text(x + 1)))
    hyps = [nn0(w, A), nn0(w, B), nn0(w, C), nn0(w, D), _eqid(w, ta), _eqid(w, tb), e4, nn0(w, F), add_nat(w, B, D)]
    return closed(w, hyps, 'decaddc', f)


def mul_nat(w, a, b):
    """closed step: ( a x. b ) = c for nonnegative integers"""
    a, b = int(a), int(b)
    ta, tb, tc = nat_text(a), nat_text(b), nat_text(a * b)
    f = '( %s x. %s ) = %s' % (ta, tb, tc)
    if f in _memo(w):
        return _memo(w)[f]
    if a == 0:
        return closed(w, [cc_nat(w, b)], 'mul02i', f)
    if b == 0:
        return closed(w, [cc_nat(w, a)], 'mul01i', f)
    if a == 1:
        return closed(w, [cc_nat(w, b)], 'mullidi', f)
    if b == 1:
        return closed(w, [cc_nat(w, a)], 'mulridi', f)
    if a < 10 and b < 10:
        lab = '%dt%de%d' % (a, b, a * b)
        if lab in MAIN_MUL:
            return closed(w, [], lab, f)
        lab2 = '%dt%de%d' % (b, a, a * b)
        assert lab2 in MAIN_MUL, lab
        s1 = closed(w, [cc_nat(w, a), cc_nat(w, b)], 'mulcomi', '( %s x. %s ) = ( %s x. %s )' % (ta, tb, tb, ta))
        s2 = closed(w, [], lab2, '( %s x. %s ) = %s' % (tb, ta, tc))
        return closed(w, [s1, s2], 'eqtri', f)
    if a < 10:   # digit x decimal: flip
        s1 = closed(w, [cc_nat(w, a), cc_nat(w, b)], 'mulcomi', '( %s x. %s ) = ( %s x. %s )' % (ta, tb, tb, ta))
        s2 = mul_nat(w, b, a)
        return closed(w, [s1, s2], 'eqtri', f)
    A, B = _dec(a)
    if b < 10:   # decimal x digit: decmul1 / decmul1c
        d = B * b
        if d < 10:
            hyps = [nn0(w, b), nn0(w, A), nn0(w, B), _eqid(w, ta), mul_nat(w, A, b), mul_nat(w, B, b)]
            return closed(w, hyps, 'decmul1', f)
        E, D = _dec(d)
        m1 = mul_nat(w, A, b)
        x = A * b
        m2 = closed(w, [m1], 'oveq1i', '( ( %s x. %s ) + %s ) = ( %s + %s )' % (nat_text(A), tb, nat_text(E), nat_text(x), nat_text(E)))
        m3 = add_nat(w, x, E)
        m4 = closed(w, [m2, m3], 'eqtri', '( ( %s x. %s ) + %s ) = %s' % (nat_text(A), tb, nat_text(E), nat_text(x + E)))
        hyps = [nn0(w, b), nn0(w, A), nn0(w, B), _eqid(w, ta), nn0(w, D), nn0(w, E), m4, mul_nat(w, B, b)]
        return closed(w, hyps, 'decmul1c', f)
    # decimal x decimal: decmul10add then add
    C, D = _dec(b)
    E, F = a * C, a * D
    e1 = closed(w, [mul_nat(w, a, C)], 'eqcomi', '%s = ( %s x. %s )' % (nat_text(E), ta, nat_text(C)))
    e2 = closed(w, [mul_nat(w, a, D)], 'eqcomi', '%s = ( %s x. %s )' % (nat_text(F), ta, nat_text(D)))
    hyps = [nn0(w, C), nn0(w, D), nn0(w, a), e1, e2]
    s1 = closed(w, hyps, 'decmul10add', '( %s x. %s ) = ( ; %s 0 + %s )' % (ta, tb, nat_text(E), nat_text(F)))
    s2 = add_nat(w, E * 10, F)
    return closed(w, [s1, s2], 'eqtri', f)


def sub_nat(w, a, b):
    """closed step: ( a - b ) = c for integers a >= b >= 0"""
    a, b = int(a), int(b)
    assert a >= b
    c = a - b
    f = '( %s - %s ) = %s' % (nat_text(a), nat_text(b), nat_text(c))
    return closed(w, [cc_nat(w, a), cc_nat(w, b), cc_nat(w, c), add_nat(w, b, c)], 'subaddrii', f)


def add_int(w, x, y):
    """closed step: ( lit(x) + lit(y) ) = lit(x+y) for integers x, y"""
    x, y = Fraction(x), Fraction(y)
    assert x.denominator == 1 and y.denominator == 1
    tx, ty, tz = lit_text(x), lit_text(y), lit_text(x + y)
    f = '( %s + %s ) = %s' % (tx, ty, tz)
    if f in _memo(w):
        return _memo(w)[f]
    if x == 0:
        return closed(w, [cc(w, ty)], 'addlidi', f)
    if y == 0:
        return closed(w, [cc(w, tx)], 'addridi', f)
    if x > 0 and y > 0:
        return add_nat(w, x, y)
    if x < 0 and y < 0:
        a, b = -x, -y
        s1 = closed(w, [cc_nat(w, a), cc_nat(w, b)], 'negdii', '-u ( %s + %s ) = ( %s + %s )' % (nat_text(a), nat_text(b), tx, ty))
        s2 = closed(w, [s1], 'eqcomi', '( %s + %s ) = -u ( %s + %s )' % (tx, ty, nat_text(a), nat_text(b)))
        s3 = closed(w, [add_nat(w, a, b)], 'negeqi', '-u ( %s + %s ) = %s' % (nat_text(a), nat_text(b), tz))
        return closed(w, [s2, s3], 'eqtri', f)
    if x < 0:   # ( -u a + b ) = ( b + -u a )
        s1 = closed(w, [cc(w, tx), cc_nat(w, y)], 'addcomi', '( %s + %s ) = ( %s + %s )' % (tx, ty, ty, tx))
        return closed(w, [s1, add_int(w, y, x)], 'eqtri', f)
    # x > 0, y < 0
    a, b = x, -y
    if a == b:
        return closed(w, [cc_nat(w, a)], 'negidi', f)
    s1 = closed(w, [cc_nat(w, a), cc_nat(w, b)], 'negsubi', '( %s + %s ) = ( %s - %s )' % (tx, ty, nat_text(a), nat_text(b)))
    if a > b:
        return closed(w, [s1, sub_nat(w, a, b)], 'eqtri', f)
    c = b - a
    s2 = closed(w, [cc_nat(w, b), cc_nat(w, a)], 'negsubdi2i', '-u ( %s - %s ) = ( %s - %s )' % (nat_text(b), nat_text(a), nat_text(a), nat_text(b)))
    s3 = closed(w, [s2], 'eqcomi', '( %s - %s ) = -u ( %s - %s )' % (nat_text(a), nat_text(b), nat_text(b), nat_text(a)))
    s4 = closed(w, [sub_nat(w, b, a)], 'negeqi', '-u ( %s - %s ) = %s' % (nat_text(b), nat_text(a), tz))
    s5 = closed(w, [s3, s4], 'eqtri', '( %s - %s ) = %s' % (nat_text(a), nat_text(b), tz))
    return closed(w, [s1, s5], 'eqtri', f)


def _mul_pos(w, a, P):
    """closed step: ( a x. P ) = m for a positive integer, P a positive literal
    text (numeral or fraction) with a*value(P) an integer m"""
    v = lit_value(P)
    m = a * v
    assert m.denominator == 1
    m = m.numerator
    if v.denominator == 1:
        return mul_nat(w, a, v.numerator)
    p, q = v.numerator, v.denominator
    ta, tp, tq, tm = nat_text(a), nat_text(p), nat_text(q), nat_text(m)
    f = '( %s x. %s ) = %s' % (ta, P, tm)
    if f in _memo(w):
        return _memo(w)[f]
    s1 = closed(w, [cc_nat(w, a), cc_nat(w, p), cc_nat(w, q), ne0_nat(w, q)], 'divassi', '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (ta, tp, tq, ta, P))
    s2 = closed(w, [s1], 'eqcomi', '( %s x. %s ) = ( ( %s x. %s ) / %s )' % (ta, P, ta, tp, tq))
    M = a * p
    s3 = closed(w, [mul_nat(w, a, p)], 'oveq1i', '( ( %s x. %s ) / %s ) = ( %s / %s )' % (ta, tp, tq, nat_text(M), tq))
    bi = closed(w, [cc_nat(w, M), cc_nat(w, q), cc_nat(w, m), ne0_nat(w, q)], 'divmuli', '( ( %s / %s ) = %s <-> ( %s x. %s ) = %s )' % (nat_text(M), tq, tm, tq, tm, nat_text(M)))
    s4 = closed(w, [mul_nat(w, q, m), bi], 'mpbir', '( %s / %s ) = %s' % (nat_text(M), tq, tm))
    s5 = closed(w, [s3, s4], 'eqtri', '( ( %s x. %s ) / %s ) = %s' % (ta, tp, tq, tm))
    return closed(w, [s2, s5], 'eqtri', f)


def mul_lit(w, s, L):
    """closed step: ( lit(s) x. L ) = lit(s*value(L)) for a nonzero integer s
    and a literal text L with s*value(L) an integer"""
    s = Fraction(s)
    assert s.denominator == 1 and s != 0
    v = lit_value(L)
    r = s * v
    assert r.denominator == 1, (s, L)
    ts, tr = lit_text(s), lit_text(r)
    f = '( %s x. %s ) = %s' % (ts, L, tr)
    if f in _memo(w):
        return _memo(w)[f]
    if v == 0:
        return closed(w, [cc(w, ts)], 'mul01i', f)
    a = abs(s).numerator
    ta = nat_text(a)
    k = _split_lit(L)
    P = k[1] if k[0] == 'neg' else L
    core = _mul_pos(w, a, P)
    m = nat_text(abs(r).numerator)
    if s > 0 and v > 0:
        return core
    if s < 0 and v < 0:
        s1 = closed(w, [cc_nat(w, a), cc(w, P)], 'mul2negi', '( %s x. %s ) = ( %s x. %s )' % (ts, L, ta, P))
        return closed(w, [s1, core], 'eqtri', f)
    if s < 0:
        s1 = closed(w, [cc_nat(w, a), cc(w, P)], 'mulneg1i', '( %s x. %s ) = -u ( %s x. %s )' % (ts, L, ta, P))
    else:
        s1 = closed(w, [cc_nat(w, a), cc(w, P)], 'mulneg2i', '( %s x. %s ) = -u ( %s x. %s )' % (ts, L, ta, P))
    s2 = closed(w, [core], 'negeqi', '-u ( %s x. %s ) = -u %s' % (ta, P, m))
    return closed(w, [s1, s2], 'eqtri', f)


def neg_lit(w, L):
    """closed step: -u L = lit(-value(L)) when L is a negative literal
    (so the result strips the double negation); None if L is nonnegative
    (then -u L is already canonical)"""
    k = _split_lit(L)
    if k[0] != 'neg':
        return None
    return closed(w, [cc(w, k[1])], 'negnegi', '-u %s = %s' % (L, k[1]))


# ---------------------------------------------------------------- comparison
# and products of literals (sortie G5: the closed facts tools/lin.py's fast
# path needs -- `a <_ b` / `a < b` for two nonnegative literals, and the
# product of two positive literals in canonical form)

def _lcm(a, b):
    from math import gcd
    return a * b // gcd(a, b)


def le_nat(w, a, b, strict=False):
    """closed step: a <_ b (a < b with strict) for nonnegative integers"""
    a, b = int(a), int(b)
    assert 0 <= a <= b and (a < b or not strict), (a, b, strict)
    ta, tb = nat_text(a), nat_text(b)
    rel = '<' if strict else '<_'
    f = '%s %s %s' % (ta, rel, tb)
    if f in _memo(w):
        return _memo(w)[f]
    if a == 0:
        return gt0_nat(w, b) if strict else ge0_nat(w, b)
    if a == b:
        i = w.inst('leid')
        return closed(w, [re_nat(w, a), i], 'ax-mp', f)
    k = b - a; tk = nat_text(k)
    if strict:
        i = w.inst('ltaddpos')
        bi = closed(w, [re_nat(w, k), re_nat(w, a), i], 'mp2an',
                    '( 0 < %s <-> %s < ( %s + %s ) )' % (tk, ta, ta, tk))
        s = closed(w, [gt0_nat(w, k), bi], 'mpbi', '%s < ( %s + %s )' % (ta, ta, tk))
    else:
        i = w.inst('addge01')
        bi = closed(w, [re_nat(w, a), re_nat(w, k), i], 'mp2an',
                    '( 0 <_ %s <-> %s <_ ( %s + %s ) )' % (tk, ta, ta, tk))
        s = closed(w, [ge0_nat(w, k), bi], 'mpbi', '%s <_ ( %s + %s )' % (ta, ta, tk))
    return closed(w, [s, add_nat(w, a, k)], 'breqtri', f)


def _pos(w, q):
    """closed step: `( q e. RR /\\ 0 < q )` for a positive integer q"""
    tq = nat_text(q)
    return closed(w, [re_nat(w, q), gt0_nat(w, q)], 'pm3.2i', '( %s e. RR /\\ 0 < %s )' % (tq, tq))


def le_lit(w, A, B, strict=False):
    """closed step: A <_ B (A < B with strict) for two nonnegative literal
    texts (numerals or fractions).  A fraction on the left is cleared by
    `ledivmul` / `ltdivmul`, one on the right by `lemuldiv` / `ltmuldiv`."""
    va, vb = lit_value(A), lit_value(B)
    assert va is not None and vb is not None and 0 <= va <= vb and (va < vb or not strict), (A, B)
    if va.denominator == 1 and vb.denominator == 1:
        return le_nat(w, va, vb, strict)
    rel = '<' if strict else '<_'
    f = '%s %s %s' % (A, rel, B)
    if f in _memo(w):
        return _memo(w)[f]
    if va.denominator != 1:
        # ( p / q ) rel B  <->  p rel ( q x. B )
        p, q = va.numerator, va.denominator; tp, tq = nat_text(p), nat_text(q)
        i = w.inst('ltdivmul' if strict else 'ledivmul')
        bi = closed(w, [re_nat(w, p), real(w, B), _pos(w, q), i], 'mp3an',
                    '( %s <-> %s %s ( %s x. %s ) )' % (f, tp, rel, tq, B))
        M = q * vb
        core = le_lit(w, tp, lit_text(M), strict)
        s = closed(w, [core, mul_lits(w, tq, B)], 'breqtrri', '%s %s ( %s x. %s )' % (tp, rel, tq, B))
        return closed(w, [s, bi], 'mpbir', f)
    # n rel ( r / s )  <->  ( n x. s ) rel r
    n = va.numerator; r_, s_ = vb.numerator, vb.denominator
    tn, tr, ts = nat_text(n), nat_text(r_), nat_text(s_)
    i = w.inst('ltmuldiv' if strict else 'lemuldiv')
    bi = closed(w, [re_nat(w, n), re_nat(w, r_), _pos(w, s_), i], 'mp3an',
                '( ( %s x. %s ) %s %s <-> %s )' % (tn, ts, rel, tr, f))
    core = le_nat(w, n * s_, r_, strict)
    s = closed(w, [mul_nat(w, n, s_), core], 'eqbrtri', '( %s x. %s ) %s %s' % (tn, ts, rel, tr))
    return closed(w, [s, bi], 'mpbir', f)


def _reduce_frac(w, M, N):
    """closed step: ( M / N ) = canonical literal of M/N, for positive
    integers M, N; None when ( M / N ) is already canonical"""
    from math import gcd
    M, N = int(M), int(N)
    tM, tN = nat_text(M), nat_text(N)
    if N == 1:
        return closed(w, [cc_nat(w, M)], 'div1i', '( %s / 1 ) = %s' % (tM, tM))
    if M % N == 0:
        t = M // N
        bi = closed(w, [cc_nat(w, M), cc_nat(w, N), cc_nat(w, t), ne0_nat(w, N)], 'divmuli',
                    '( ( %s / %s ) = %s <-> ( %s x. %s ) = %s )' % (tM, tN, nat_text(t), tN, nat_text(t), tM))
        return closed(w, [mul_nat(w, N, t), bi], 'mpbir', '( %s / %s ) = %s' % (tM, tN, nat_text(t)))
    g = gcd(M, N)
    if g == 1:
        return None
    u, v = M // g, N // g
    tu, tv, tg = nat_text(u), nat_text(v), nat_text(g)
    p2 = closed(w, [cc_nat(w, v), ne0_nat(w, v)], 'pm3.2i', '( %s e. CC /\\ %s =/= 0 )' % (tv, tv))
    p3 = closed(w, [cc_nat(w, g), ne0_nat(w, g)], 'pm3.2i', '( %s e. CC /\\ %s =/= 0 )' % (tg, tg))
    i = w.inst('divcan5')
    c5 = closed(w, [cc_nat(w, u), p2, p3, i], 'mp3an',
                '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (tg, tu, tg, tv, tu, tv))
    e = closed(w, [mul_nat(w, g, u), mul_nat(w, g, v)], 'oveq12i',
               '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (tg, tu, tg, tv, tM, tN))
    e2 = closed(w, [e], 'eqcomi', '( %s / %s ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (tM, tN, tg, tu, tg, tv))
    return closed(w, [e2, c5], 'eqtri', '( %s / %s ) = ( %s / %s )' % (tM, tN, tu, tv))


def mul_lits(w, K, L):
    """closed step: ( K x. L ) = lit(K*L) for two positive literal texts
    (numerals or fractions), the result in canonical form"""
    vk, vl = lit_value(K), lit_value(L)
    assert vk is not None and vl is not None and vk >= 0 and vl >= 0, (K, L)
    r = vk * vl
    f = '( %s x. %s ) = %s' % (K, L, lit_text(r))
    if f in _memo(w):
        return _memo(w)[f]
    if vl == 0:
        return closed(w, [cc(w, K)], 'mul01i', f)
    if vk == 0:
        return closed(w, [cc(w, L)], 'mul02i', f)
    if vk.denominator == 1 and vl.denominator == 1:
        return mul_nat(w, vk, vl)
    if r.denominator == 1 and vk.denominator == 1:
        return mul_lit(w, vk, L)
    if vk.denominator == 1:
        # ( k x. ( p / q ) ) = ( ( k x. p ) / q )
        k = vk.numerator; p, q = vl.numerator, vl.denominator
        tk, tp, tq = nat_text(k), nat_text(p), nat_text(q)
        s1 = closed(w, [cc_nat(w, k), cc_nat(w, p), cc_nat(w, q), ne0_nat(w, q)], 'divassi',
                    '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (tk, tp, tq, tk, L))
        s2 = closed(w, [s1], 'eqcomi', '( %s x. %s ) = ( ( %s x. %s ) / %s )' % (tk, L, tk, tp, tq))
        M = k * p; N = q
        s3 = closed(w, [mul_nat(w, k, p)], 'oveq1i',
                    '( ( %s x. %s ) / %s ) = ( %s / %s )' % (tk, tp, tq, nat_text(M), tq))
    elif vl.denominator == 1:
        # ( ( p / q ) x. b ) = ( ( p x. b ) / q )
        b = vl.numerator; p, q = vk.numerator, vk.denominator
        tb, tp, tq = nat_text(b), nat_text(p), nat_text(q)
        s1 = closed(w, [cc_nat(w, p), cc_nat(w, b), cc_nat(w, q), ne0_nat(w, q)], 'div23i',
                    '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (tp, tb, tq, K, tb))
        s2 = closed(w, [s1], 'eqcomi', '( %s x. %s ) = ( ( %s x. %s ) / %s )' % (K, tb, tp, tb, tq))
        M = p * b; N = q
        s3 = closed(w, [mul_nat(w, p, b)], 'oveq1i',
                    '( ( %s x. %s ) / %s ) = ( %s / %s )' % (tp, tb, tq, nat_text(M), tq))
    else:
        p, q = vk.numerator, vk.denominator; r_, s_ = vl.numerator, vl.denominator
        tp, tq, tr, ts = nat_text(p), nat_text(q), nat_text(r_), nat_text(s_)
        s2 = closed(w, [cc_nat(w, p), cc_nat(w, q), cc_nat(w, r_), cc_nat(w, s_), ne0_nat(w, q), ne0_nat(w, s_)],
                    'divmuldivi', '( %s x. %s ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (K, L, tp, tr, tq, ts))
        M = p * r_; N = q * s_
        s3 = closed(w, [mul_nat(w, p, r_), mul_nat(w, q, s_)], 'oveq12i',
                    '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (tp, tr, tq, ts, nat_text(M), nat_text(N)))
    acc = closed(w, [s2, s3], 'eqtri', '( %s x. %s ) = ( %s / %s )' % (K, L, nat_text(M), nat_text(N)))
    red = _reduce_frac(w, M, N)
    if red is None:
        return acc
    return closed(w, [acc, red], 'eqtri', f)
