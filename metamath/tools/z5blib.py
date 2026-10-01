"""Sortie Z5b helpers (Route Z: Detector.lean's arithmetic core).

STATEMENTS / HYPS are the frozen statements of Z5b-blueprint.md, one place,
so that the blueprint, the grammar check and the generators cannot drift apart.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *          # PSI, FDT, HAB0, zd1lib's DV, W, mkst, sy, ...
from c0lib import hyp

# ---- the objects of Detector.lean 139-575 (campaign conventions)
PF = lambda X: '{ q e. Prime | q || %s }' % X                       # X.primeFactors
FMP = lambda X: '( ( mmu ` %s ) x. ( phi ` %s ) )' % (X, X)         # fmp X
IFP = lambda p, R: 'if ( %s || %s , %s , 1 )' % (p, R, FMP(p))     # if p | r then fmp p else 1
HP = lambda R, S, p: '( ( %s x. %s ) - 1 )' % (IFP(p, R), IFP(p, S))   # hPrime r r' p
HB = lambda R, S, D: '( ( %s hBV %s ) ` %s )' % (R, S, D)            # hBV r r' d
SQF = lambda X: '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (X, X)      # squarefree X (X > 0)
HRS = '( %s /\\ %s )' % (SQF('R'), SQF('S'))
IF1 = lambda p, R, E: 'if ( %s || %s , %s , 1 )' % (p, R, E)
PFD = lambda R: '( N PFun %s )' % R
FDK = lambda K: FDT('A', 'B', PFD('R'), 'X', 'C', 'S', K)            # the detector summand at K
HFD = '( %s /\\ ( X e. RR+ /\\ ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) ) )' % HAB0
QX = '( exp ` ( -u 1 / X ) )'

STATEMENTS = {
    # section E: the Euler-product engine (Detector.lean 139-192)
    'z5fprodabs': '( ph -> ( abs ` prod_ k e. A B ) = prod_ k e. A ( abs ` B ) )',
    'z5sfrad': '( ( %s /\\ ( N e. NN /\\ D || N ) ) -> D || prod_ p e. %s p )' % (SQF('D'), PF('N')),
    'z5sqfeul': '( ph -> sum_ d e. %s if ( ( mmu ` d ) =/= 0 , prod_ p e. %s B , 0 ) = prod_ p e. %s ( 1 + B ) )' % (DV('N'), PF('d'), PF('N')),
    # section M: multiplicativity of f = mu phi (Detector.lean 283-340)
    'z5fmpprm': '( P e. Prime -> %s = -u ( P - 1 ) )' % FMP('P'),
    'z5fmpmul': '( ( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 ) -> %s = ( %s x. %s ) )' % (FMP('( A x. B )'), FMP('A'), FMP('B')),
    'z5fmpprod': '( %s -> %s = prod_ p e. %s %s )' % (SQF('M'), FMP('M'), PF('M'), FMP('p')),
    'z5pfif': '( ph -> prod_ p e. %s if ( p || R , C , 1 ) = prod_ p e. %s C )' % (PF('M'), PF('R')),
    # section L: Lemmas 3.2 and 3.3 (Detector.lean 394-575)
    'z5sqfdvd': '( ( %s /\\ ( D e. NN /\\ D || M ) ) -> ( mmu ` D ) =/= 0 )' % SQF('M'),
    'z5hbvval': '( ( ( R e. V /\\ S e. W ) /\\ D e. NN ) -> %s = if ( ( mmu ` D ) =/= 0 , prod_ p e. %s %s , 0 ) )' % (HB('R', 'S', 'D'), PF('D'), HP('R', 'S', 'p')),
    'z5hbvre': '( ( ( R e. V /\\ S e. W ) /\\ D e. NN ) -> %s e. RR )' % HB('R', 'S', 'D'),
    'z5psiprod': '( ( %s /\\ N e. NN ) -> %s = prod_ p e. %s %s )' % (SQF('R'), PSI('R', 'N'), PF('N'), IFP('p', 'R')),
    'z5psipsi': '( ( %s /\\ %s /\\ N e. NN ) -> ( %s x. %s ) = sum_ d e. %s %s )' % (SQF('R'), SQF('S'), PSI('R', 'N'), PSI('S', 'N'), DV('N'), HB('R', 'S', 'd')),
    'z5hbvdiv': '( ( ( R e. V /\\ S e. W ) /\\ D e. NN ) -> ( %s / D ) = if ( ( mmu ` D ) =/= 0 , prod_ p e. %s ( %s / p ) , 0 ) )' % (HB('R', 'S', 'D'), PF('D'), HP('R', 'S', 'p')),
    'z5hpone': '( ( P e. Prime /\\ ( P || R /\\ -. P || S ) ) -> ( 1 + ( %s / P ) ) = 0 )' % HP('R', 'S', 'P'),
    'z5hptwo': '( ( P e. Prime /\\ ( P || R /\\ P || S ) ) -> ( 1 + ( %s / P ) ) = ( P - 1 ) )' % HP('R', 'S', 'P'),
    'z5sqfne': '( ( %s /\\ R =/= S ) -> E. c e. Prime ( ( c || R /\\ -. c || S ) \\/ ( c || S /\\ -. c || R ) ) )' % HRS,
    'z5hbvorth': '( %s -> sum_ d e. %s ( %s / d ) = if ( R = S , ( phi ` R ) , 0 ) )' % (HRS, DV('( R x. S )'), HB('R', 'S', 'd')),
    'z5hpabs': '( P e. Prime -> ( 1 + ( abs ` %s ) ) <_ ( %s x. %s ) )' % (HP('R', 'S', 'P'), IF1('P', 'R', '( P + 1 )'), IF1('P', 'S', '( P + 1 )')),
    'z5hbvabs': '( %s -> sum_ d e. %s ( abs ` %s ) <_ ( prod_ p e. %s ( p + 1 ) x. prod_ p e. %s ( p + 1 ) ) )' % (HRS, DV('( R x. S )'), HB('R', 'S', 'd'), PF('R'), PF('S')),
    # section S: summable_fdetTerm (Detector.lean 1396-1446)
    'z5fdtabs': '( ( %s /\\ ( ( ( C ` K ) e. CC /\\ ( abs ` ( C ` K ) ) <_ 1 ) /\\ ( ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ K e. NN ) ) ) -> '
                '( abs ` %s ) <_ ( ( |_ ` R ) x. ( K x. ( %s ^ K ) ) ) )' % (HFD, FDK('K'), QX),
    'z5fdetcvg': '( ( %s /\\ ( ( C : NN --> CC /\\ A. j e. NN ( abs ` ( C ` j ) ) <_ 1 ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) ) -> '
                 '( seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~> /\\ seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> ) )' % (HFD, FDK('n'), FDK('n')),
}

HYPS = {
    'z5fprodabs': [('1', '( ph -> A e. Fin )'), ('2', '( ( ph /\\ k e. A ) -> B e. CC )')],
    'z5sqfeul': [('1', '( ph -> N e. NN )'), ('2', '( ( ph /\\ p e. Prime ) -> B e. CC )')],
    'z5pfif': [('1', '( ph -> M e. NN )'), ('2', '( ph -> R e. NN )'), ('3', '( ph -> R || M )'), ('4', '( ( ph /\\ p e. Prime ) -> C e. CC )')],
}

ORDER = ['z5fprodabs', 'z5sfrad', 'z5sqfeul',
         'z5fmpprm', 'z5fmpmul', 'z5fmpprod', 'z5pfif',
         'z5sqfdvd', 'z5hbvval', 'z5hbvre', 'z5psiprod', 'z5psipsi', 'z5hbvdiv', 'z5hpone', 'z5hptwo', 'z5sqfne', 'z5hbvorth', 'z5hpabs', 'z5hbvabs',
         'z5fdtabs', 'z5fdetcvg']


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('z5bg' + lab, 'grammar check of %s' % lab)
        for n, f in HYPS.get(lab, []):
            hyp(w, n, '%s.%s' % (lab, n), f)
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


def hyps_of(w, lab):
    return [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]


def run(w):
    return (runh if HYPS.get(w.label) else (lambda x: x.run()))(w)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])
