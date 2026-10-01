"""Sortie V5 helpers: the smooth-shifted primes (SmoothShifted.lean) and the
sieve-side discharge of carmsalg (carmsw).

Expressions are built here so that every generator and the blueprint agree
token for token.  The density statement is read out of the database
(a5lib.dbhyps('carmsalg')), never retyped.
"""
import os, sys, subprocess, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W, ROOT, WSDIR
import a5lib
import num


def mkst(w, a):
    """st(hyps, ref, goal) writes ( a -> goal )"""
    return lambda hyps, ref, g, name=None: w.s(hyps, ref, '( %s -> %s )' % (a, g), name=name)


FACT = {'ge0': '0 <_ %s', 'gt0': '0 < %s', 'ne0': '%s =/= 0', 'ge1': '1 <_ %s', 'gt1': '1 < %s'}


def lit(w, ante, t, kind):
    """( ante -> t e. kind ) / sign fact for a numeral literal, by a1i"""
    f = FACT[kind] % t if kind in FACT else '%s e. %s' % (t, kind)
    return w.s([num.fact(w, t, kind)], 'a1i', '( %s -> %s )' % (ante, f))


# ---------------------------------------------------------------- sets

def INNER(X, E, a='a', q='q'):
    """A. q e. Prime ( q || ( a - 1 ) -> q <_ ( X ^c ( 1 - E ) ) )"""
    return 'A. %s e. Prime ( %s || ( %s - 1 ) -> %s <_ ( %s ^c ( 1 - %s ) ) )' % (q, q, a, q, X, E)


def SG(X, E, a='a', q='q'):
    """the smooth-shifted primes up to X (Lean: Sgood; the set of searchw.10)"""
    return '{ %s e. ( 0 ... %s ) | ( %s e. Prime /\\ %s ) }' % (a, X, a, INNER(X, E, a, q))


def SB(X, E, a='a', q='q'):
    """the bad primes (Lean: Sbad)"""
    return '{ %s e. ( 0 ... %s ) | ( %s e. Prime /\\ -. %s ) }' % (a, X, a, INNER(X, E, a, q))


def TW(N, Z, v='v'):
    """twinsv's set: the primes v <_ Z with N v + 1 prime"""
    return '{ %s e. ( 1 ... %s ) | ( %s e. Prime /\\ ( ( %s x. %s ) + 1 ) e. Prime ) }' % (v, Z, v, N, v)


def MM(X, E):
    """the cofactor cutoff M = |_ X ^c E _|"""
    return '( |_ ` ( %s ^c %s ) )' % (X, E)


def FL(X, N):
    """Nat.div: |_ X / N _|"""
    return '( |_ ` ( %s / %s ) )' % (X, N)


def UU(X, E, m='j'):
    """the tagged union of the twin sets, U_ m e. ( 1 ... M ) ( { m } X. TW( m , |_ X / m _| ) )"""
    return 'U_ %s e. ( 1 ... %s ) ( { %s } X. %s )' % (m, MM(X, E), m, TW(m, FL(X, m)))


def FF(X, E, u='u', m='j'):
    """the map ( u e. UU |-> ( ( 1st u ) ( 2nd u ) + 1 ) )"""
    return '( %s e. %s |-> ( ( ( 1st ` %s ) x. ( 2nd ` %s ) ) + 1 ) )' % (u, UU(X, E, m), u, u)


def TWIN(C, T, n='n', z='z', v='v'):
    """twinsv's body: A. n e. NN A. z e. ( ZZ>= ` T ) ( # TW ) <_ ( ( C ( n / phi n ) ^ 2 ) z ) / ( log z ) ^ 2"""
    return ('A. %s e. NN A. %s e. ( ZZ>= ` %s ) ( # ` %s ) <_ ( ( ( %s x. ( ( %s / ( phi ` %s ) ) ^ 2 ) ) x. %s ) / ( ( log ` %s ) ^ 2 ) )'
            % (n, z, T, TW(n, z, v), C, n, n, z, z))


def RQ(N):
    """( N / phi N ) ^ 2"""
    return '( ( %s / ( phi ` %s ) ) ^ 2 )' % (N, N)


# ---------------------------------------------------------------- the frozen texts

_HYPS = None


def carmsalg_hyps():
    global _HYPS
    if _HYPS is None:
        _HYPS = a5lib.dbhyps('carmsalg')
    return _HYPS


def strip_ph(t):
    a, b = a5lib.split_imp(t)
    assert a == 'ph', t[:40]
    return b


def dens_text(E='E', G='G', X='X'):
    """the text of carmsalg.10 with E, G, X substituted"""
    h = strip_ph(carmsalg_hyps()[9])
    return a5lib.subvars(h, {'E': E, 'G': G, 'X': X})


def smshw_text(t='t', g='g', w='w'):
    """the headline: the existential closure of carmsalg.3 .. .10"""
    hs = [strip_ph(x) for x in carmsalg_hyps()]
    sub = {'E': t, 'G': g, 'X': w}
    h3, h4, h5, h6, h7, h9, h10 = [a5lib.subvars(hs[i], sub) for i in (2, 3, 4, 5, 6, 8, 9)]
    assert h3 == '%s e. RR' % t and h6 == '%s e. RR' % g and h9 == '%s e. NN0' % w
    return ('E. %s e. RR ( ( %s /\\ %s ) /\\ E. %s e. RR ( %s /\\ E. %s e. NN0 %s ) )'
            % (t, h4, h5, g, h7, w, h10))


def grammar_check(label, stmt):
    """write scratch/LABEL.mmp with the statement as its qed line and run the
    unifier; return True when mmj2 parses the formula (the only diagnostic is
    the incomplete proof)"""
    path = os.path.join(ROOT, 'scratch', label + '.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=%s  LOC_AFTER=?\n\n* grammar check\n\nqed:: |- %s\n$)\n' % (label, stmt))
    r = subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'mm.py'), 'unify', path],
                       cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    bad = [l for l in out.split('\n') if l.startswith('E-') and 'I-PA-0411' not in l and 'E-PA-0411' not in l]
    return (not bad), out


# ---------------------------------------------------------------- frozen statements

E3 = '( exp ` 3 )'
HALF = '( 1 / 2 )'


def K(C, X, L):
    """the per-cofactor constant 16 C X / L ^ 2"""
    return '( ( ; 1 6 x. ( %s x. %s ) ) / ( %s ^ 2 ) )' % (C, X, L)


def H96(C, E):
    return '( ; 9 6 x. ( ( %s x. %s ) x. %s ) ) <_ %s' % (C, E3, E, HALF)


def EE(C):
    """the exponent chosen at twin constant C"""
    return '( 1 / ( 2 + ( ; ; 2 0 0 x. ( %s x. %s ) ) ) )' % (E3, C)


def PH(C='C', T='T', E='E'):
    """the analytic parameters: the twin constant and threshold with twinsv's body, the exponent"""
    return ('( ( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. NN /\\ %s ) ) /\\ ( ( %s e. RR /\\ 0 < %s /\\ %s <_ %s ) /\\ %s ) )'
            % (C, C, T, TWIN(C, T), E, E, E, HALF, H96(C, E)))


def XC(X, T='T', E='E'):
    """the pointwise conditions on x"""
    return ('( %s e. NN /\\ ( ( 4 + ( 1 / %s ) ) <_ ( log ` %s ) /\\ ( %s + 2 ) <_ ( sqrt ` %s ) ) /\\ ( %s / ( 3 x. ( log ` %s ) ) ) <_ ( ppi ` %s ) )'
            % (X, E, X, T, X, X, X, X))


def SUMTW(X, E, j='j'):
    return 'sum_ %s e. ( 1 ... %s ) ( # ` %s )' % (j, MM(X, E), TW(j, FL(X, j)))


def GOAL(X, E):
    """( 1 / 2 ) ppi X <_ # SG"""
    return '( %s x. ( ppi ` %s ) ) <_ ( # ` %s )' % (HALF, X, SG(X, E))


def BOUND5(C, X, E):
    """# SB <_ K ( e^3 ( 1 + log M ) )"""
    return '( # ` %s ) <_ ( %s x. ( %s x. ( 1 + ( log ` %s ) ) ) )' % (SB(X, E), K(C, X, '( log ` %s )' % X), E3, MM(X, E))


PH5 = ('( ( ( C e. RR /\\ 0 <_ C ) /\\ ( X e. NN /\\ E e. RR ) /\\ 4 <_ ( log ` X ) ) /\\ ( ( T e. NN /\\ %s ) /\\ '
       '( ( 0 < E /\\ E <_ %s ) /\\ ( T + 2 ) <_ ( sqrt ` X ) ) ) )' % (TWIN('C', 'T'), HALF))
PH6 = ('( ( ( C e. RR /\\ 0 <_ C ) /\\ ( X e. NN /\\ E e. RR ) ) /\\ ( ( ( 0 < E /\\ %s ) /\\ '
       '( ( 4 + ( 1 / E ) ) <_ ( log ` X ) /\\ ( X / ( 3 x. ( log ` X ) ) ) <_ ( ppi ` X ) ) ) /\\ %s ) )'
       % (H96('C', 'E'), BOUND5('C', 'X', 'E')))

STATEMENTS = {
    'smshbad': '( ( X e. NN /\\ E e. RR ) -> %s C_ ran %s )' % (SB('X', 'E'), FF('X', 'E')),
    'smshcnt': '( ( X e. NN /\\ E e. RR ) -> ( # ` %s ) <_ %s )' % (SB('X', 'E'), SUMTW('X', 'E')),
    'smshlog': ('( ( ( X e. RR+ /\\ 4 <_ ( log ` X ) ) /\\ ( E e. RR /\\ E <_ %s ) /\\ '
                '( Z e. RR /\\ ( ( X ^c ( 1 - E ) ) / 2 ) <_ Z ) ) -> ( ( log ` X ) / 4 ) <_ ( log ` Z ) )' % HALF),
    'smshdiv': ('( ( ( ( ( C e. RR /\\ 0 <_ C ) /\\ ( R e. RR /\\ 0 <_ R ) ) /\\ ( ( N e. RR /\\ 0 < N ) /\\ ( X e. RR /\\ 0 <_ X ) ) /\\ '
                '( ( L e. RR /\\ 0 < L ) /\\ ( W e. RR /\\ ( L / 4 ) <_ W ) ) ) /\\ ( Z e. RR /\\ 0 <_ Z /\\ Z <_ ( X / N ) ) ) -> '
                '( ( ( C x. R ) x. Z ) / ( W ^ 2 ) ) <_ ( %s x. ( R / N ) ) )' % K('C', 'X', 'L')),
    'smshsum': '( %s -> %s )' % (PH5, BOUND5('C', 'X', 'E')),
    'smshpi': '( %s -> ( # ` %s ) <_ ( %s x. ( ppi ` X ) ) )' % (PH6, SB('X', 'E'), HALF),
    'smshsplit': '( ( X e. NN /\\ E e. RR ) -> ( ppi ` X ) <_ ( ( # ` %s ) + ( # ` %s ) ) )' % (SG('X', 'E'), SB('X', 'E')),
    'smshx': '( ( %s /\\ %s ) -> %s )' % (PH(), XC('X'), GOAL('X', 'E')),
    'smshev': '( %s -> E. w e. NN0 A. x e. ( ZZ>= ` w ) %s )' % (PH(), GOAL('x', 'E')),
    'smshe': ('( ( C e. RR /\\ 0 < C ) -> ( ( %s e. RR /\\ 0 < %s /\\ %s <_ %s ) /\\ %s ) )'
              % (EE('C'), EE('C'), EE('C'), HALF, H96('C', EE('C')))),
}
STATEMENTS['smshw'] = smshw_text()


def carmsw_text():
    """the sieve-side discharge of carmsalg: its conclusion at C := c, E := t"""
    concl = a5lib.split_imp(a5lib.dbstmt('carmsalg'))[1]
    body = a5lib.subvars(concl, {'C': 'c', 'E': 't'})
    return ('( ph -> E. c e. RR E. t e. RR ( ( ; ; ; 1 0 0 0 <_ c /\\ ( 0 < t /\\ t <_ %s ) ) /\\ %s ) )'
            % (HALF, body))


if __name__ == '__main__':
    import sys
    labs = sys.argv[1:] or list(STATEMENTS) + ['carmsw']
    for lab in labs:
        s = carmsw_text() if lab == 'carmsw' else STATEMENTS[lab]
        ok, out = grammar_check('v5gc_' + lab, s)
        print('GRAMMAR', 'OK  ' if ok else 'FAIL', lab, len(s.split()), 'tokens')
        if not ok:
            print(out[-800:])


# ---------------------------------------------------------------- conjunct projection

def _split_conj(t):
    """top-level conjuncts of `( A /\\ B )` or `( A /\\ B /\\ C )`, else None"""
    t = ' '.join(t.split())
    if not (t.startswith('( ') and t.endswith(' )')):
        return None
    toks = t.split()[1:-1]
    parts, cur, d = [], [], 0
    for tk in toks:
        if tk in ('(', '{', '<.'):
            d += 1
        elif tk in (')', '}', '>.'):
            d -= 1
        if tk == '/\\' and d == 0:
            parts.append(' '.join(cur)); cur = []
        else:
            cur.append(tk)
    parts.append(' '.join(cur))
    if len(parts) in (2, 3):
        return parts
    return None


def _find(t, target, path):
    if ' '.join(t.split()) == ' '.join(target.split()):
        return path
    parts = _split_conj(t)
    if not parts:
        return None
    for i, p in enumerate(parts):
        r = _find(p, target, path + [(i, len(parts))])
        if r is not None:
            return r
    return None


class Proj:
    """steps ( ante -> P ) for any conjunct P of the antecedent, by a chain of
    simpld / simprd / simp1d / simp2d / simp3d from ( ante -> ante ), prefixes shared"""
    def __init__(self, w, ante):
        self.w, self.ante = w, ' '.join(ante.split())
        self.memo = {}

    def __call__(self, target):
        target = ' '.join(target.split())
        path = _find(self.ante, target, [])
        assert path is not None, 'not a conjunct: %s\n of %s' % (target, self.ante)
        cur, t = None, self.ante
        for k, (i, n) in enumerate(path):
            key = tuple(path[:k + 1])
            parts = _split_conj(t)
            t = parts[i]
            if key in self.memo:
                cur = self.memo[key]; continue
            if cur is None:
                lemma = {2: ('simpl', 'simpr'), 3: ('simp1', 'simp2', 'simp3')}[n][i]
                cur = self.w.s([], lemma, '( %s -> %s )' % (self.ante, t))
            else:
                lemma = {2: ('simpld', 'simprd'), 3: ('simp1d', 'simp2d', 'simp3d')}[n][i]
                cur = self.w.s([cur], lemma, '( %s -> %s )' % (self.ante, t))
            self.memo[key] = cur
        if not path:
            cur = self.w.s([], 'id', '( %s -> %s )' % (self.ante, self.ante))
        return cur


def subst(w, var, val, wff):
    """closed step ( var = val -> ( wff <-> wff[var := val] ) ); returns (step, new wff)"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))
    return w.wcongr(wff, {var: val}, '%s = %s' % (var, val), {var: idst})


def csubst(w, var, val, expr):
    """closed step ( var = val -> expr = expr[var := val] ) for a class expression"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))
    return w.congr(expr, {var: val}, '%s = %s' % (var, val), {var: idst})
