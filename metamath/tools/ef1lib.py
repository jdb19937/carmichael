"""Sortie EF1 helpers (Route Z: ExplicitFormula.lean 56-1582, the series side
and the interchange; PerronKernel.lean's remnants).

STATEMENTS / HYPS / ORDER are the frozen statements of EF1-blueprint.md, one
place.  `MM_DB=sorties/ef1.mm python3 tools/ef1lib.py [LABEL...]` grammar-checks
them with tools/mmatch (a worksheet `h -> idi -> qed` on the statement).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from c7lib import *                        # W, a1, PKF, CPT, HP, TPI, ...
from cl import Closure
import lin as LIN
LIN.FASTPATH = True

# ------------------------------------------------------------------ objects
NX = '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'
XC = lambda n: '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % n       # chi ( n )
LAM = lambda n: '( Lam ` %s )' % n
AN = lambda n: '( %s x. ( Lam ` %s ) )' % (XC(n), n)                 # chi ( n ) Lam ( n )
C0 = '( 1 + ( 1 / ( log ` Y ) ) )'                                    # c = 1 + 1 / log y
FL = '( |_ ` Y )'                                                     # F = floor y
LL = '( log ` ( T x. Y ) )'                                           # L = log ( T y )
LO = lambda C='C', T='T': CPT(C, '-u %s' % T)
HI = lambda C='C', T='T': CPT(C, T)


def PKL(U, C='C', T='T'):
    """the Perron kernel line: 2 pi i times Lean's perronKernel U C T"""
    return '( %s lint <. %s , %s >. )' % (PKF(U), LO(C, T), HI(C, T))


PSI = 'sum_ n e. ( 1 ... ( |_ ` Y ) ) ( %s x. ( Lam ` n ) )' % XC('n')     # psiChi chi y
PTERM = lambda n, C='C': '( %s x. %s )' % (AN(n), PKL('( Y / %s )' % n, C))
PSER = lambda C='C': 'seq 1 ( + , ( n e. NN |-> %s ) )' % PTERM('n', C)
PS = lambda C='C': 'sum_ n e. NN %s' % PTERM('n', C)                  # perronSum ( 2 pi i normalised )
# the right-edge integrand -L'/L ( s ) y ^ s / s, the Dirichlet series written out
DLV = lambda z: 'sum_ k e. NN ( %s x. ( k ^c -u %s ) )' % (AN('k'), z)
RHF = '( z e. ( CC \\ { 0 } ) |-> ( %s x. ( ( Y ^c z ) / z ) ) )' % DLV('z')
YL = '( ( Y x. ( %s ^ 2 ) ) / T )' % LL                               # y L ^ 2 / T
L2 = '( %s ^ 2 )' % LL
BND = '( ( 2 x. _pi ) x. ( ( ; ; 2 0 0 x. %s ) + ( ; 3 0 x. %s ) ) )' % (YL, L2)
YT = '( ( Y e. RR /\\ ; ; 1 0 0 <_ Y ) /\\ ( T e. RR /\\ 2 <_ T ) )'
KC = lambda n: PKL('( Y / %s )' % n, C0)                              # K_n at c = C0
EL = lambda n: '( ( Lam ` %s ) x. ( abs ` ( %s - %s ) ) )' % (n, KC(n), TPI)   # kerErr, n <_ F
ER = lambda n: '( ( Lam ` %s ) x. ( abs ` %s ) )' % (n, KC(n))                  # kerErr, F < n
F2 = '( ( 2 x. ( |_ ` Y ) ) + 2 )'                                    # R = 2 F + 2

STATEMENTS = {}
HYPS = {}

# ================================================================== 1. elementary (56-237)
STATEMENTS['ef1l4'] = '( ( Y e. RR /\\ ; ; 1 0 0 <_ Y ) -> 4 <_ ( log ` Y ) )'
STATEMENTS['ef1yc'] = ('( ( Y e. RR /\\ 1 < Y ) -> ( ( Y ^c %s ) = ( ( exp ` 1 ) x. Y ) /\\ ( Y ^c %s ) <_ ( 3 x. Y ) ) )'
                       % (C0, C0))
# ================================================================== 2. integral helpers (238-443)
ABT = '( 1 / ( 1 + ( abs ` t ) ) )'
HYPS['ef1ftc'] = [('1', '( ph -> ( P e. RR /\\ Q e. RR /\\ P <_ Q ) )'),
                  ('2', '( ph -> ( t e. ( P [,] Q ) |-> G ) e. ( ( P [,] Q ) -cn-> CC ) )'),
                  ('3', '( ph -> ( RR _D ( t e. ( P (,) Q ) |-> G ) ) = ( t e. ( P (,) Q ) |-> H ) )'),
                  ('4', '( ph -> ( t e. ( P [,] Q ) |-> H ) e. ( ( P [,] Q ) -cn-> CC ) )'),
                  ('5', '( t = P -> G = R )'),
                  ('6', '( t = Q -> G = S )')]
STATEMENTS['ef1ftc'] = '( ph -> ( ( t e. ( P (,) Q ) |-> H ) e. L^1 /\\ S. ( P (,) Q ) H _d t = ( S - R ) ) )'
HYPS['ef1faf'] = [('1', '( ph -> ( ( K e. RR /\\ K =/= 0 /\\ H e. RR ) /\\ ( P e. RR /\\ Q e. RR /\\ P <_ Q ) ) )'),
                  ('2', '( ph -> A. t e. ( P [,] Q ) 0 < ( ( K x. t ) + H ) )'),
                  ('3', '( ( ph /\\ y e. RR+ ) -> A e. CC )'),
                  ('4', '( ph -> ( RR _D ( y e. RR+ |-> A ) ) = ( y e. RR+ |-> B ) )'),
                  ('5', '( ph -> ( y e. RR+ |-> B ) e. ( RR+ -cn-> CC ) )'),
                  ('6', '( y = ( ( K x. t ) + H ) -> A = C )'),
                  ('7', '( y = ( ( K x. t ) + H ) -> B = E )'),
                  ('8', '( t = P -> C = R )'),
                  ('9', '( t = Q -> C = S )')]
STATEMENTS['ef1faf'] = '( ph -> ( ( t e. ( P (,) Q ) |-> E ) e. L^1 /\\ S. ( P (,) Q ) E _d t = ( ( S - R ) / K ) ) )'
STATEMENTS['ef1ilaf'] = ('( ( ( K e. RR /\\ K =/= 0 /\\ H e. RR ) /\\ ( ( P e. RR /\\ Q e. RR /\\ P <_ Q ) /\\ '
                         'A. u e. ( P [,] Q ) 0 < ( ( K x. u ) + H ) ) ) -> ( ( t e. ( P (,) Q ) |-> ( 1 / ( ( K x. t ) + H ) ) ) e. L^1 /\\ '
                         'S. ( P (,) Q ) ( 1 / ( ( K x. t ) + H ) ) _d t = ( ( ( log ` ( ( K x. Q ) + H ) ) - ( log ` ( ( K x. P ) + H ) ) ) / K ) ) )')
STATEMENTS['ef1iac'] = '( ( U e. RR /\\ V e. RR ) -> ( t e. ( U (,) V ) |-> %s ) e. L^1 )' % ABT
STATEMENTS['ef1ia'] = ('( ( ( U e. RR /\\ U <_ 0 ) /\\ ( V e. RR /\\ 0 <_ V ) ) -> S. ( U (,) V ) %s _d t = '
                       '( ( log ` ( 1 - U ) ) + ( log ` ( 1 + V ) ) ) )' % ABT)
STATEMENTS['ef1ial'] = ('( ( ( U e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( ( U <_ 0 /\\ 0 <_ V ) /\\ ( -u W <_ U /\\ V <_ W ) ) ) -> '
                        'S. ( U (,) V ) %s _d t <_ ( 2 x. ( log ` ( 1 + W ) ) ) )' % ABT)
STATEMENTS['ef1ipaf'] = ('( ( ( K e. RR /\\ K =/= 0 /\\ H e. RR ) /\\ ( ( P e. RR /\\ Q e. RR /\\ P <_ Q ) /\\ '
                         'A. u e. ( P [,] Q ) 0 < ( ( K x. u ) + H ) ) ) -> ( ( t e. ( P (,) Q ) |-> ( ( ( K x. t ) + H ) ^c -u ( 1 / 2 ) ) ) e. L^1 /\\ '
                         'S. ( P (,) Q ) ( ( ( K x. t ) + H ) ^c -u ( 1 / 2 ) ) _d t = '
                         '( ( ( 2 x. ( ( ( K x. Q ) + H ) ^c ( 1 / 2 ) ) ) - ( 2 x. ( ( ( K x. P ) + H ) ^c ( 1 / 2 ) ) ) ) / K ) ) )')
RG = '( ( ( abs ` ( t - B ) ) + E ) ^c -u ( 1 / 2 ) )'
STATEMENTS['ef1ir'] = ('( ( ( B e. RR /\\ E e. RR+ ) /\\ ( ( P e. RR /\\ Q e. RR /\\ P <_ Q ) /\\ ( D e. RR /\\ ( Q - B ) <_ D /\\ ( B - P ) <_ D ) ) ) -> '
                       '( ( t e. ( P (,) Q ) |-> %s ) e. L^1 /\\ S. ( P (,) Q ) %s _d t <_ ( 4 x. ( ( D + E ) ^c ( 1 / 2 ) ) ) ) )' % (RG, RG))
# ================================================================== 3. the measure pigeonhole (444-522)
STATEMENTS['ef1pgh'] = ('( ( ( P e. RR /\\ Q e. RR /\\ P < Q ) /\\ ( F : ( P (,) Q ) --> RR /\\ F e. L^1 ) /\\ '
                        '( ( M e. RR /\\ S. ( P (,) Q ) ( F ` t ) _d t <_ ( M x. ( Q - P ) ) ) /\\ S e. Fin ) ) -> '
                        'E. t e. ( P (,) Q ) ( -. t e. S /\\ ( F ` t ) <_ M ) )')
# ================================================================== 4-5. the series side (523-1366)
STATEMENTS['ef1u4'] = '( ( ( U e. RR+ /\\ U <_ 2 ) /\\ ( C e. RR+ /\\ C <_ 2 ) ) -> ( U ^c C ) <_ 4 )'
HYPS['ef1fzs'] = [('1', '( ph -> K e. ( M ... N ) )'), ('2', '( ( ph /\\ k e. ( M ... N ) ) -> A e. CC )')]
STATEMENTS['ef1fzs'] = '( ph -> sum_ k e. ( M ... N ) A = ( sum_ k e. ( M ... K ) A + sum_ k e. ( ( K + 1 ) ... N ) A ) )'
STATEMENTS['ef1pfr'] = ('( ( Y e. RR /\\ 1 <_ Y ) -> sum_ n e. ( 1 ... ( ( |_ ` Y ) - 1 ) ) ( Y / ( n x. ( Y - n ) ) ) <_ '
                        '( 2 x. ( 1 + ( log ` Y ) ) ) )')
KNL = lambda N, C='C', T='T': PKL('( Y / %s )' % N, C, T)
STATEMENTS['ef1kl'] = ('( ( ( Y e. RR+ /\\ C e. RR /\\ 1 <_ C ) /\\ ( T e. RR+ /\\ ( N e. NN /\\ N < Y ) ) ) -> '
                       '( abs ` ( %s - %s ) ) <_ ( ( ( 6 x. ( Y ^c C ) ) / T ) x. ( Y / ( N x. ( Y - N ) ) ) ) )' % (KNL('N'), TPI))
STATEMENTS['ef1kr'] = ('( ( ( Y e. RR+ /\\ C e. RR+ ) /\\ ( T e. RR+ /\\ ( N e. NN /\\ Y < N ) ) ) -> '
                       '( abs ` %s ) <_ ( ( 6 / T ) x. ( N / ( N - Y ) ) ) )' % KNL('N'))
STATEMENTS['ef1kt'] = ('( ( ( Y e. RR+ /\\ C e. RR+ ) /\\ ( T e. RR+ /\\ ( N e. NN /\\ ( 2 x. Y ) <_ N ) ) ) -> '
                       '( abs ` %s ) <_ ( ( ; 1 2 / T ) x. ( ( Y / N ) ^c C ) ) )' % KNL('N'))
STATEMENTS['ef1lft'] = ('( %s -> sum_ n e. ( 1 ... ( ( |_ ` Y ) - 1 ) ) %s <_ ( ; 4 6 x. %s ) )' % (YT, EL('n'), YL))
STATEMENTS['ef1nr'] = ('( %s -> ( %s + %s ) <_ ( ; 1 6 x. %s ) )' % (YT, EL(FL), ER('( ( |_ ` Y ) + 1 )'), L2))
STATEMENTS['ef1mr'] = ('( %s -> sum_ n e. ( ( ( |_ ` Y ) + 2 ) ... ( ( 2 x. ( |_ ` Y ) ) + 1 ) ) %s <_ ( ; 4 5 x. %s ) )'
                       % (YT, ER('n'), YL))
STATEMENTS['ef1tl'] = ('( ( %s /\\ M e. ( ZZ>= ` %s ) ) -> sum_ n e. ( %s ... M ) %s <_ ( ; ; 2 1 6 x. %s ) )'
                       % (YT, F2, F2, ER('n'), YL))
STATEMENTS['ef1an'] = ('( ( %s /\\ ( K e. NN /\\ Z e. CC ) ) -> ( abs ` ( %s x. Z ) ) <_ ( ( Lam ` K ) x. ( abs ` Z ) ) )' % (NX, AN('K')))
STATEMENTS['ef1pt'] = ('( ( ( %s /\\ %s ) /\\ M e. ( ZZ>= ` %s ) ) -> ( abs ` ( sum_ n e. ( 1 ... M ) %s - ( %s x. %s ) ) ) '
                       '<_ ( ( ; ; 3 1 0 x. %s ) + ( ; 1 6 x. %s ) ) )' % (NX, YT, F2, PTERM('n', C0), TPI, PSI, YL, L2))
STATEMENTS['ef1psb'] = ('( ( %s /\\ %s ) -> ( abs ` ( %s - ( %s x. %s ) ) ) <_ %s )' % (NX, YT, PS(C0), TPI, PSI, BND))
# ================================================================== 6. the interchange (1366-1582)
FSEQ = '( k e. NN |-> ( F ` k ) )'
HYPS['ef1lser'] = [('1', '( ph -> ( A e. CC /\\ B e. CC ) )'),
                   ('2', '( ph -> ( F : NN --> ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )'),
                   ('3', '( ph -> ( G : NN --> RR /\\ seq 1 ( + , G ) e. dom ~~> ) )'),
                   ('4', '( ( ph /\\ ( k e. NN /\\ z e. ( A cseg B ) ) ) -> ( abs ` ( ( F ` k ) ` z ) ) <_ ( G ` k ) )')]
STATEMENTS['ef1lser'] = ('( ph -> seq 1 ( + , ( k e. NN |-> ( ( F ` k ) lint <. A , B >. ) ) ) ~~> '
                         '( ( z e. D |-> sum_ k e. NN ( ( F ` k ) ` z ) ) lint <. A , B >. ) )')
STATEMENTS['ef1redge'] = ('( ( %s /\\ ( ( Y e. RR+ /\\ C e. RR /\\ 1 < C ) /\\ T e. RR ) ) -> ( %s ~~> ( %s lint <. %s , %s >. ) /\\ '
                          '%s = ( %s lint <. %s , %s >. ) ) )' % (NX, PSER(), RHF, LO(), HI(), PS(), RHF, LO(), HI()))

ORDER = ['ef1l4', 'ef1yc', 'ef1ftc', 'ef1faf', 'ef1ilaf', 'ef1iac', 'ef1ia', 'ef1ial', 'ef1ipaf', 'ef1ir', 'ef1pgh',
         'ef1u4', 'ef1fzs', 'ef1pfr', 'ef1kl', 'ef1kr', 'ef1kt', 'ef1lft', 'ef1nr', 'ef1mr', 'ef1tl', 'ef1lser', 'ef1redge', 'ef1an', 'ef1pt', 'ef1psb']


def gramcheck(labels):
    """grammar-check each statement with tools/mmatch: h1 |- S, qed:h1:idi |- S"""
    import mm as _MM
    out = {}
    for lab in labels:
        w = W('ef1g' + lab, 'grammar check of %s' % lab)
        n = 0
        for nm, f in HYPS.get(lab, []):
            w.s([], '%s.%s' % (lab, nm), f, name='h' + nm); n += 1
        w.s([], 'ef1g%s.x' % lab, STATEMENTS[lab], name='h99')
        w.qed(['h99'], 'idi', STATEMENTS[lab])
        path = w.write()
        ok, text, rc = _MM.run_mmatch(path)
        out[lab] = [] if ok else [l for l in text.split('\n') if l.strip()][:6]
        try:
            os.remove(path)
        except OSError:
            pass
    return out


# ------------------------------------------------------------------ step helpers
def E(w, ante, ref, hyps, l, r):
    return w.s(hyps, ref, '( %s -> %s = %s )' % (ante, l, r))


def D(w, ante, ref, hyps, concl, name=None):
    """deduction step ( ante -> concl )"""
    return w.s(hyps, ref, '( %s -> %s )' % (ante, concl), name=name)


def chain(w, ante, terms, steps, name=None, rel='='):
    """( ante -> t0 = tn ) from steps[i]: ( ante -> t_i = t_(i+1) ) (or ('r', st) reversed)"""
    cur = None
    for i, st in enumerate(steps):
        a, b = terms[i], terms[i + 1]
        if isinstance(st, tuple):
            st = w.s([st[1]], 'eqcomd', '( %s -> %s = %s )' % (ante, a, b))
        if cur is None:
            cur = st
        else:
            last = i == len(steps) - 1
            cur = w.s([cur, st], 'eqtrd', '( %s -> %s = %s )' % (ante, terms[0], b), name=(name if last else None))
    return cur


def dedupe(w):
    """rename repeated step names (tools/lin.py's power rewriting restarts its p-counter per call);
    a reference means the latest step of that name"""
    import re as _re
    cur, seen, out, k = {}, set(), [], 0
    for line in w.lines:
        m = _re.match(r'^([^:]*):([^:]*):(.*)$', line)
        if not m:
            out.append(line); continue
        name, hyps, rest = m.groups()
        hl = [cur.get(h, h) for h in hyps.split(',')] if hyps else []
        if name in seen and name != 'qed':
            k += 1
            new = '%sd%d' % (name, k)
        else:
            new = name
        seen.add(name); cur[name] = new
        out.append('%s:%s:%s' % (new, ','.join(hl), rest))
    w.lines = out


def go(w, only):
    if only and w.label not in only:
        return True
    dedupe(w)
    if os.environ.get('EF1_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines), 'lines'); return True
    ok = w.run()
    if not ok:
        sys.exit(1)
    return ok


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])
