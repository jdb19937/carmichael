"""Sortie Z6c helpers (Route Z: DetectionShift.lean sections 6-7).

Statements of Z6c-blueprint.md, one place.  They are added to z6alib's
STATEMENTS dict in memory (tools/z6alib.py and tools/z6blib.py are not
edited).  The frozen text of the two deviating headlines is kept as
STATEMENTS['z6split_frozen'] and STATEMENTS['z6dlbz_frozen'].
`MM_DB=sorties/z6c.mm python3 tools/z6clib.py [LABEL...]` grammar-checks them.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from z6blib import STATEMENTS, HYPS, gramcheck, LATER
from tm import sub

RSD = '( N RSet %s )' % RPD
PFD = '( N PFun %s )' % RPD
E1 = '( exp ` ( -u 1 / %s ) )' % XPD
# the detector summand a ( m ) P ( m ) e ^ ( - m / X ) C ( m ) m ^ -S (z5fdetval's body without the cut)
XM = lambda m: ('( ( ( ( ( ( %s bvA %s ) ` %s ) x. ( %s ` %s ) ) x. ( exp ` ( -u %s / %s ) ) ) x. ( C ` %s ) ) x. ( %s ^c -u S ) )'
                % (Z1D, Z2D, m, PFD, m, m, XPD, m, m))
STFR = lambda r: '( n e. NN |-> %s )' % STERM(r, 'n')
SSUM = lambda r: 'sum_ n e. NN %s' % STERM(r, 'n')
RES5R = lambda r: sub(RES5, {'R': r})
GRr = lambda r: GR(r)
W3 = '( 3 + ( _i x. U ) )'

# the deviation of z6split: C ( 1 ) = 1 (Lean map_one); the frozen A6 lacks it and the frozen statement is false at C = 0
A6C = ('( ( ( %s /\\ N e. NN ) /\\ ( ( C : NN --> CC /\\ ( C ` 1 ) = 1 ) /\\ %s ) ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) )' % (HZD3, CB))
STATEMENTS['z6split_frozen'] = STATEMENTS['z6split']
STATEMENTS['z6split'] = ('( %s -> ( %s + ( %s x. %s ) ) = sum_ r e. %s ( ( 1 / r ) x. %s ) )'
                         % (A6C, FDV, E1, P1D, RSD, SSUM('r')))
# the deviation of z6dlbz: the frozen text leaves T (Lean's sigma) free and unconstrained; T gets Lean's range
TRNG = '( T e. RR /\\ ( 0 <_ T /\\ T <_ ( Re ` S ) ) )'
STATEMENTS['z6dlbz_frozen'] = STATEMENTS['z6dlbz']
STATEMENTS['z6dlbz'] = ('( ( %s /\\ ( %s /\\ ( C = %s -> %s <_ ( abs ` ( Im ` S ) ) ) ) ) -> ( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ ( abs ` %s ) )'
                        % (A7, TRNG, PRN, LAM60, FDV))

# ---- helpers, section 6
# z6geo: sum n q ^ n converges for q = e ^ ( -1 / X ) (the majorant of Lean summable_Sterm; z5fdetcvg's first block)
GEOM = '( m e. NN0 |-> ( m x. ( ( exp ` ( -u 1 / X ) ) ^ m ) ) )'
STATEMENTS['z6geo'] = '( X e. RR+ -> seq 1 ( + , %s ) e. dom ~~> )' % GEOM
# z6stcv: the per-modulus detector series converges (Lean summable_Sterm; no multiplicativity)
STATEMENTS['z6stcv'] = ('( ( ( %s /\\ ( ( C : NN --> CC /\\ %s ) /\\ R e. NN ) ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) -> seq 1 ( + , %s ) e. dom ~~> )'
                        % (HZD3, CB, STFR('R')))
# z6fdvcl: the detector value is a complex number (z5fdetval, z5fdetcvg)
STATEMENTS['z6fdvcl'] = '( %s -> %s e. CC )' % (A6, FDV)
# z6hval: the r-sum of the per-modulus summands is the detector summand (Lean sum_Rset_Sterm, ofReal_Pfun)
STATEMENTS['z6hval'] = '( ( %s /\\ M e. NN ) -> sum_ r e. %s ( ( 1 / r ) x. %s ) = %s )' % (A6, RSD, STERM('r', 'M'), XM('M'))
# z6xcut: beyond m = 1 the cut z1 < m of the detector is invisible (bvA vanishes on 1 < m <_ z1)
STATEMENTS['z6xcut'] = ('( ( %s /\\ M e. ( ZZ>= ` 2 ) ) -> if ( %s < M , %s , 0 ) = %s )' % (A6, Z1D, XM('M'), XM('M')))
# z6x1: the m = 1 summand is e ^ ( -1 / X ) P ( 1 ) and the cut removes it from the detector
STATEMENTS['z6x1'] = ('( ( ( ( %s /\\ N e. NN ) /\\ ( C : NN --> CC /\\ ( C ` 1 ) = 1 ) ) /\\ S e. CC ) -> ( %s = ( %s x. %s ) /\\ if ( %s < 1 , %s , 0 ) = 0 ) )'
                      % (HZD3, XM('1'), E1, P1D, Z1D, XM('1')))

# ---- helpers, section 7
# z6g3gr: on Re w = 3 the anchor integrand G3 is the shifted integrand GR (DSER; Lean ectrInt_line_eq_Ghat at c = 3)
STATEMENTS['z6g3gr'] = ('( ( ( ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ ( C : NN --> CC /\\ %s ) ) /\\ ( %s /\\ U e. RR ) ) -> ( %s ` %s ) = ( %s ` %s ) )'
                        % (CB, DSER, G3('R'), W3, GR('R'), W3))
# z6detr: one modulus, shifted (Lean tsum_Sterm_eq_integral_shift, tsum_Sterm_eq_integral_shift_principal, one statement)
STATEMENTS['z6detr'] = ('( ( %s /\\ R e. %s ) -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( 1 / R ) x. %s ) = ( ( ( 1 / %s ) x. ( ( 1 / R ) x. %s ) ) + ( ( 1 / R ) x. %s ) ) ) )'
                        % (A7, RSD, VL(GR('R'), CL), RES5, SSUM('R'), TPI, VL(GR('R'), CL), RES5))
# z6epsum: the residues summed are Epole (z5epval, z5ep0)
STATEMENTS['z6epsum'] = '( %s -> sum_ r e. %s ( ( 1 / r ) x. %s ) = %s )' % (A7, RSD, RES5R('r'), EPC)

ORDER6 = ['z6geo', 'z6stcv', 'z6fdvcl', 'z6hval', 'z6xcut', 'z6x1', 'z6split']
ORDER7 = ['z6g3gr', 'z6detr', 'z6epsum', 'z6detid', 'z6detall', 'z6dlbz']

if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or (ORDER6 + ORDER7))
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])
