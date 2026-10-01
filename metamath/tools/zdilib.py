"""DensityInterface.lean's two statements, frozen once (ZPLAN section 3: by whichever of
T21a and ZD2 starts first; T21a did).  Closed wffs over ZC1's zeroCountBox rendering, no
new symbol.  T21a, T21b, ZD2, LDEN and F2 read these texts.

  LOGFREE  = Lean `LogFreeDensity` (Z6d, coefficient 9/2 on 9/10 <_ s <_ 1, c in [1,2])
  LOGGED   = Lean `LoggedDensity` (uniform profile p <_ 7/2 on 39/50 <_ s <_ 1, c in [1,5/4])

Bound letters: modulus m, characters y, zeros p, the box binder o, height v, abscissa u;
constants g c (LOGFREE), h w c k (LOGGED).  The letters avoid x q r t s k n, which the
proofs that carry these bodies in their antecedents bind (a `$d` against a bound
occurrence fails).  The per-modulus bodies with the modulus a
class variable are `t21alib.LFD_BODY(G, C, N)` and `t21alib.LGD_BODY(H, P, C, K, N)`;
T21a's zone theorems t21z2/t21z3/t21z4 take exactly those bodies as hypotheses.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t21alib import LOGFREE, LOGGED, LFD_BODY, LGD_BODY

if __name__ == '__main__':
    print('LOGFREE =', LOGFREE)
    print('LOGGED  =', LOGGED)
