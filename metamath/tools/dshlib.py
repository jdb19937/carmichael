"""Sortie DSH helpers (Route Z: DetectionShiftHalf.lean + LoggedParams.lean).

STATEMENTS / ORDER are the frozen statements of DSH-HANDOFF.md, one place.
`MM_DB=sorties/dsh.mm python3 tools/dshlib.py [LABEL...]` grammar-checks them through mmatch.

Route: the half-line detector is Z6's detector at z1 = D, z2 = 2 D, R = 1, X = Ypar D = D ^ (151/100),
shifted to the line Re w = 1/2 - Re S (HL) instead of CL = 1/100 - Re S, for 39/50 <_ Re S <_ 1.
Z6's theorems are transcribed by the text substitution `dsub` (worksheet transform or generator copy,
tools/gen/dsh_*.py); the transformed labels are z6X -> dshX (TR below).
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z6clib as Z6
from z5clib import PRIN, HAB0, MR, EPV
from z6alib import TPI, VL, LIF, CHRB, CB, CHR, DG

# ------------------------------------------------------------------ LoggedParams (written-out classes, no df-)
Y151 = '( ; ; 1 5 1 / ; ; 1 0 0 )'
YPF = lambda D='D': '( %s ^c %s )' % (D, Y151)                        # Ypar D = D ^ ( 151 / 100 )
YP = YPF()
NMAXF = lambda D='D': '( |^ ` ( ( 8 x. %s ) x. ( log ` %s ) ) )' % (YPF(D), D)   # Nmax D = ceil ( 8 Y log D )
JPARF = lambda D='D': '( |^ ` ( log ` %s ) )' % D                    # Jpar D = ceil ( log D )
NMAX = NMAXF(); JPAR = JPARF()
BLK = lambda j, D='D': '( 1 ... ( |^ ` ( ( 2 ^ ( %s + 1 ) ) x. %s ) ) )' % (j, D)  # blockRange D j
COEFF = lambda j, k, n, T='T', D='D': (
    'if ( ( ( ( 2 ^ %s ) x. %s ) < %s /\\ %s <_ ( ( 2 ^ ( %s + 1 ) ) x. %s ) /\\ %s <_ %s ) , '
    '( ( ( ( ( %s bvA ( 2 x. %s ) ) ` %s ) x. ( exp ` ( -u %s / %s ) ) ) x. ( -u ( log ` ( %s / ( ( 2 ^ %s ) x. %s ) ) ) ^ %s ) ) x. ( %s ^c -u %s ) ) , 0 )'
    % (j, D, n, n, j, D, n, NMAXF(D), D, D, n, n, YPF(D), n, j, D, k, n, T))   # coeffJK D sigma j k n
HL = '( ( 1 / 2 ) - ( Re ` S ) )'                                      # the half line Re w = 1/2 - Re S

# ------------------------------------------------------------------ the substitution Z6 -> DSH
Z1D, Z2D, XPD, RPD, CL = Z6.Z1D, Z6.Z2D, Z6.XPD, Z6.RPD, Z6.CL
SUBS = [('; ; 2 0 0 <_ ( log ` D )', '; 4 0 <_ ( log ` D )'),
        (Z1D, 'D'), (Z2D, '( 2 x. D )'), (XPD, YP), (RPD, '1'), (CL, HL),
        ('( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )', '( ; 3 9 / ; 5 0 ) <_ ( Re ` S )')]


def dsub(t):
    for a, b in SUBS:
        t = t.replace(a, b)
    return t


TR = ['hm', 'ff', 'ffv', 'pdg', 'grcn', 'rect', 'grsd', 'grmaj', 'shiftr',
      'anp', 'anv', 'aerr', 'anb', 'anl', 'ancv', 'anbd', 'anchor',
      'stcv', 'hval', 'xcut', 'x1', 'split', 'g3gr', 'detr', 'epsum', 'detid']
LABMAP = dict(('z6' + x, 'dsh' + x) for x in TR)
LABMAP['zdz12'] = 'dshzz'

HZH = '( D e. RR /\\ 1 < D /\\ ; 4 0 <_ ( log ` D ) )'
SRNGH = '( S e. CC /\\ ( ( ; 3 9 / ; 5 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )'
GRH = dsub(Z6.GR('1'))                                                 # the half-line integrand at r = 1
ECTRH = '( ( 1 / %s ) x. %s )' % (TPI, VL(GRH, HL))                    # EctrHalf chi D ( Ypar D ) rho
FDVH = '( ( <. D , ( 2 x. D ) >. FDet <. ( N PFun 1 ) , %s , C >. ) ` S )' % YP
EPH = lambda C='C': '( ( <. D , ( 2 x. D ) , %s >. EPole <. %s , N , 1 >. ) ` S )' % (YP, C)
PRN = PRIN('N')
A7H = ('( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( %s /\\ S =/= 1 ) ) ) /\\ ( %s /\\ ( E ` S ) = 0 ) )'
       % (HZH, CHRB, SRNGH, LIF))

STATEMENTS = {}
HYPS = {}
# parameter facts
STATEMENTS['dshzz'] = '( ( D e. RR /\\ 1 < D ) -> ( D e. RR+ /\\ ( 2 x. D ) e. RR+ /\\ D < ( 2 x. D ) ) )'
STATEMENTS['dsh151rp'] = '%s e. RR+' % Y151
STATEMENTS['dshyp'] = '( ( D e. RR /\\ 1 < D ) -> ( %s e. RR+ /\\ 1 < %s ) )' % (YP, YP)
# section A: the R = 1 collapse (Rset_one, P1_one, psi_one_left/Pfun_one_eq_one, Mr_one_eq, Epole_one_eq)
STATEMENTS['dshrs1'] = '( N e. NN -> ( N RSet 1 ) = { 1 } )'
STATEMENTS['dshp11'] = '( N e. NN -> sum_ r e. ( N RSet 1 ) ( 1 / r ) = 1 )'
STATEMENTS['dshpf1'] = '( ( N e. NN /\\ M e. NN ) -> ( ( N PFun 1 ) ` M ) = 1 )'
STATEMENTS['dshmr1'] = ('( ( %s /\\ ( C : NN --> CC /\\ S e. CC ) ) -> %s = sum_ d e. ( 1 ... ( |_ ` B ) ) '
                        '( ( ( ( A bvLam B ) ` d ) x. ( C ` d ) ) x. ( d ^c -u S ) ) )' % (HAB0, MR('S', '1')))
STATEMENTS['dshep1'] = ('( ( ( ( %s /\\ X e. W ) /\\ ( C e. T /\\ N e. NN ) ) /\\ S e. CC ) -> '
                        '( ( <. A , B , X >. EPole <. C , N , 1 >. ) ` S ) = if ( C = %s , '
                        '( ( ( ( _G ` ( 1 - S ) ) x. ( X ^c ( 1 - S ) ) ) x. ( ( phi ` N ) / N ) ) x. ( ( <. A , B >. Mr <. C , 1 >. ) ` 1 ) ) , 0 ) )'
                        % (HAB0, PRN))
# section D: L1.b norm_Epole_le_of_height (sigma folded into 39/50 <_ Re S; 1 < D added, the consumer has it)
STATEMENTS['dshepb'] = ('( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( log ` D ) <_ ( abs ` ( Im ` S ) ) ) ) -> ( abs ` %s ) <_ ( 1 / 8 ) )'
                        % (HZH, SRNGH, EPH(PRN)))
# the numeric threshold (Lean pole_threshold_numeric: 16671744 x <_ e ^ ( ( 3339 / 5000 ) x ); here 960 x, the constant K = 60 of z5dgamh)
STATEMENTS['dshnum'] = '( ( X e. RR /\\ ; 4 0 <_ X ) -> ( ; ; 9 6 0 x. X ) <_ ( exp ` ( ( ; ; ; 3 3 3 9 / ; ; ; 5 0 0 0 ) x. X ) ) )'
# section C: L1.a detection_identity_half
STATEMENTS['dshdih'] = '( %s -> ( %s + ( exp ` ( -u 1 / %s ) ) ) = ( %s + %s ) )' % (A7H, FDVH, YP, ECTRH, EPH())

# the transformed Z6 statements (z6X -> dshX), each dsub of the database statement unless overridden
ZS = {}


def z6stmt(lab):
    """statement of a carmichael.mm theorem (cached)"""
    if not ZS:
        cur = None; buf = []
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'carmichael.mm')) as fh:
            for line in fh:
                if cur is None:
                    i = line.find(' $p ')
                    if i < 0:
                        continue
                    cur = line[:i].split()[-1]; buf = [line[i + 4:]]
                else:
                    buf.append(line)
                if cur is not None and '$=' in line:
                    s = ''.join(buf).split('$=', 1)[0]
                    ZS[cur] = ' '.join(s.split())[3:]
                    cur = None
    return ZS[lab]


HDN, T1 = Z6.HDN, Z6.T1
A7SUB = [(HDN, 'S e. CC'), (T1, 'D e. RR')]      # section 7: the Lemma 4.2 hypotheses (unused by the identity) become duplicates
A7TR = ['epsum', 'detr', 'detid']


def trstmt(x):
    t = dsub(z6stmt('z6' + x))
    if x in A7TR:
        for a, b in A7SUB:
            t = t.replace(dsub(a), b)
    return t


ORDER = ['dshzz', 'dsh151rp', 'dshyp', 'dshrs1', 'dshp11', 'dshpf1', 'dshmr1', 'dshep1', 'dshnum', 'dshepb', 'dshdih']


def gramcheck(labels):
    out = {}
    for lab in labels:
        st = STATEMENTS[lab] if lab in STATEMENTS else trstmt(lab[3:])
        p = os.path.join('worksheets', 'dshg_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=dshg_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('%s::? |- %s\n' % (n, h))
            f.write('qed::ax-1 |- %s\n$)\n' % st)
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower() or 'parse' in l.lower()]
        os.remove(p)
    return out



def toqed(w, step, label=None):
    """rename the LAST worksheet step to qed and check its formula against the frozen statement"""
    last = w.lines[-1]
    assert last.startswith(step + ':'), (step, last[:80])
    w.lines[-1] = 'qed' + last[len(step):]
    if label:
        f = last.split('|-', 1)[1].strip()
        want = STATEMENTS[label] if label in STATEMENTS else trstmt(label[3:])
        assert f == want, '\n%s\n%s' % (f, want)


def _ante(f):
    t = f.split(); d = 0
    for i, x in enumerate(t):
        d += (x == '(') - (x == ')')
        if x == '->' and d == 1:
            return ' '.join(t[1:i])


# the closure that replaces z6ectrl in dshdetr (Z6's z6ectrl bounds VL ( GR , CL ); only its closure is used)
STATEMENTS['dshvlc'] = '( %s -> %s e. CC )' % (_ante(trstmt('shiftr')), VL(dsub(Z6.GR('R')), HL))


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
