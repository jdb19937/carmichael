"""Sortie ZL3e helpers: section H of ZL3-blueprint.md (the assembly: PCONT discharged).
STATEMENTS / ORDER are this sortie's frozen statements (headlines zl3cvxh, zl3dlbz verbatim
from tools/zl3lib.py).  `MM_DB=sorties/zl3e.mm python3 tools/zl3elib.py [LABEL...]`
grammar-checks them with mmatch."""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import zl3lib as Z3
import zl3dlib as ZD
import zl3clib as ZC
import zl2lib as Z2
import zl1lib as Z1

STATEMENTS = {}
HYPS = {}
ORDER = []


def st(label, text, hyps=()):
    STATEMENTS[label] = ' '.join(text.split())
    HYPS[label] = list(hyps)
    ORDER.append(label)


def tsub(txt, m):
    return ' '.join(m.get(tk, tk) for tk in txt.split())


HOL = Z2.HOL
PR, LM, CYM, YB, CYBM, PAR, RM, EPS = Z3.PR, Z3.LM, Z3.CYM, Z3.YB, Z3.CYBM, Z3.PAR, Z3.RM, Z3.EPS
STR = Z2.STR
UO = "( `' Re \" ( -u 1 (,) 3 ) )"                         # U, the open strip -1 < Re < 3
AIM = lambda z: '( abs ` ( Im ` %s ) )' % z
EXB = lambda b, z: '( exp ` ( %s x. %s ) )' % (b, AIM(z))


# ------------------------------------------------------------------ generic-parity objects
def THG(C, y, P):
    return ('sum_ n e. NN ( ( %s ` n ) x. ( ( n ^ %s ) x. ( exp ` -u ( ( _pi x. ( n ^ 2 ) ) x. ( %s / M ) ) ) ) )' % (C, P, y))


def ILG(C, s, P):
    """IL with the parity P"""
    return ('( ~~>r ` ( t e. RR+ |-> S. ( 1 (,) t ) ( %s x. ( y ^c ( ( ( %s + %s ) / 2 ) - 1 ) ) ) _d y ) )' % (THG(C, 'y', P), s, P))


assert ILG(CYM, 's', PAR) == Z3.IL(CYM, 's') and ILG(CYBM, '( 1 - s )', PAR) == Z3.IL(CYBM, '( 1 - s )')
GAMFG = lambda s, P: ('( ( ( M / _pi ) ^c ( ( %s + %s ) / 2 ) ) x. ( _G ` ( ( %s + %s ) / 2 ) ) )' % (s, P, s, P))
assert GAMFG('s', PAR) == Z3.GAMF('s')
WV = lambda v, P='P': '( ( %s + %s ) / 2 )' % (v, P)                                   # w = ( v + P ) / 2
HV = lambda v, P='P': '( ( ( _pi / M ) ^c %s ) / ( _G ` ( %s + 1 ) ) )' % (WV(v, P), WV(v, P))   # h = ( pi / M ) ^ w / Gamma ( w + 1 )
GV = lambda v, P='P': '( %s x. %s )' % (WV(v, P), HV(v, P))                               # g = w h = 1 / GAMF
GM = lambda P='P': '( x e. %s |-> ( %s - %s ) )' % (UO, GV('x', P), GV('1', P))          # g - g ( 1 )
DQ = lambda P='P': ('( u e. %s |-> if ( u = 1 , ( ( CC _D %s ) ` 1 ) , ( ( %s ` u ) / ( u - 1 ) ) ) )' % (UO, GM(P), GM(P)))
MPW = lambda C, P: '( w e. CC |-> %s )' % ILG(C, 'w', P)                                 # the entire IL map
QQ = Z3.QQ


def FG(I1='I', I2='J', E='E', R='R', D='D', P='P'):
    """the continuation F in closed form (binder v)"""
    return ('( v e. %s |-> ( ( ( ( ( %s ` v ) + ( %s x. ( %s ` ( 1 - v ) ) ) ) x. %s ) - ( %s x. ( %s / 2 ) ) ) + ( %s x. ( %s ` v ) ) ) )'
            % (UO, I1, E, I2, GV('v', P), R, HV('v', P), R, D))


FC = FG(MPW(CYM, PAR), MPW(CYBM, PAR), EPS, RM, DQ(PAR), PAR)                               # the concrete F at ( M , Y )
MP = '( M e. NN /\\ P e. { 0 , 1 } )'
TA = ZD.TA
EUT = ZC.EUT

# ------------------------------------------------------------------ G: the exponential bound on 1 / Gamma
KS = '( ( 2 x. K ) + 1 )'
st('zl3tsb', '( ( K e. NN0 /\\ N e. NN0 ) -> sum_ m e. ( 1 ... N ) ( %s / ( ( m ^ 2 ) + ( K ^ 2 ) ) ) <_ 8 )' % KS)
st('zl3ppb', '( ( K e. NN0 /\\ N e. NN ) -> prod_ m e. ( 1 ... N ) ( 1 + ( ( K ^ 2 ) / ( m ^ 2 ) ) ) <_ ( exp ` ( 8 x. K ) ) )')
HVK = '( ( V e. CC /\\ 0 <_ ( Re ` V ) ) /\\ ( K e. NN0 /\\ ( abs ` ( Im ` V ) ) <_ K ) )'
st('zl3gfc', '( ( %s /\\ M e. NN ) -> ( ( %s ` M ) ^ 2 ) <_ ( ( ( abs ` ( %s ` M ) ) ^ 2 ) x. ( 1 + ( ( K ^ 2 ) / ( M ^ 2 ) ) ) ) )'
   % (HVK, EUT('( Re ` V )'), EUT('V')))
GSQ = lambda A: 'seq 1 ( x. , %s )' % EUT(A)
st('zl3gsq', '( ( %s /\\ N e. NN ) -> ( ( %s ` N ) ^ 2 ) <_ ( ( ( abs ` ( %s ` N ) ) ^ 2 ) x. ( exp ` ( 8 x. K ) ) ) )'
   % (HVK, GSQ('( Re ` V )'), GSQ('V')))
st('zl3glb', '( ( ( V e. CC /\\ 0 < ( Re ` V ) ) /\\ ( K e. NN0 /\\ ( abs ` ( Im ` V ) ) <_ K ) ) -> '
   '( ( _G ` ( Re ` V ) ) x. ( Re ` V ) ) <_ ( ( exp ` ( 4 x. K ) ) x. ( abs ` ( ( _G ` V ) x. V ) ) ) )')
st('zl3igb', 'E. c e. RR+ A. u e. CC ( ( ( 3 / 4 ) <_ ( Re ` u ) /\\ ( Re ` u ) <_ ( 5 / 2 ) ) -> '
   '( ( _G ` u ) =/= 0 /\\ ( 1 / ( abs ` ( _G ` u ) ) ) <_ ( c x. %s ) ) )' % EXB('5', 'u'))
st('zl3hgb', '( %s -> E. c e. RR+ A. v e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) -> '
   '( ( abs ` %s ) <_ ( c x. %s ) /\\ ( abs ` %s ) <_ ( c x. %s ) ) ) )' % (MP, HV('v'), EXB('3', 'v'), GV('v'), EXB('3', 'v')))

# ------------------------------------------------------------------ I: the theta integrals IL, entire and bounded
PHV = ZD.PHV
MJ = ZD.MJ
IMP = ZD.IMP
st('zl3pib', '( ( %s /\\ ( S e. CC /\\ R e. RR /\\ ( ( abs ` ( Re ` S ) ) + 1 ) <_ R ) ) -> '
   '( ( ~~>r ` %s ) e. CC /\\ ( abs ` ( ~~>r ` %s ) ) <_ sum_ j e. NN %s ) )' % (PHV, IMP('S'), IMP('S'), MJ('j')))
GR = '( r e. ( 1 [,) +oo ) |-> %s )' % tsub(THG('C', 'r', 'P'), {'n': 'm'})
PHR = tsub(PHV, {'G': GR, 'K': ZD.KT, 'B': '( _pi / M )'})
IMR = lambda s: '( t e. RR+ |-> S. ( 1 (,) t ) ( ( %s ` y ) x. ( y ^c %s ) ) _d y )' % (GR, s)
st('zl3ilv', '( %s -> ( %s /\\ A. w e. CC %s = ( ~~>r ` %s ) ) )' % (TA, PHR, ILG('C', 'w', 'P'), IMR('( ( ( w + P ) / 2 ) - 1 )')))
st('zl3ilh', '( %s -> %s )' % (TA, HOL(MPW('C', 'P'), 'CC')))
st('zl3ilb', '( %s -> E. c e. RR A. w e. CC ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ c ) )' % (TA, ILG('C', 'w', 'P')))

# ------------------------------------------------------------------ C: characters
MC, YP, RP = Z2.MC, Z2.YP, Z2.RP
PRC = tsub(PR, {'M': MC, 'Y': YP})
RMC = tsub(RM, {'M': MC})
st('zl3brg', '( %s -> ( %s /\\ %s = %s ) )' % (Z1.NX, PRC, RP, RMC))
st('zl3gsp', '( %s -> ( ( M DChrGS Y ) x. ( M DChrGS %s ) ) = ( ( Y ` ( %s ` -u 1 ) ) x. M ) )' % (PR, YB, LM))
PARB = tsub(PAR, {'Y': YB})
EPSB = tsub(EPS, {'Y': YB})
PRB = tsub(PR, {'Y': YB})
INVB = '( ( invg ` ( DChr ` M ) ) ` %s )' % YB
st('zl3yb', '( %s -> ( ( %s /\\ %s = %s ) /\\ ( %s = Y /\\ ( %s x. %s ) = 1 ) ) )' % (PR, PRB, PARB, PAR, INVB, EPS, EPSB))
st('zl3ilp', '( ( P = Q /\\ C = D ) -> %s = %s )' % (ILG('C', 'S', 'P'), ILG('D', 'S', 'Q')))
st('zl3mlb', '( %s -> A. s e. CC ( 1 < ( Re ` s ) -> ( %s x. %s ) = ( ( %s + ( %s x. %s ) ) - ( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) ) ) )'
   % (PR, Z3.GAMF('s'), Z3.LS(CYBM, 's'), Z3.IL(CYBM, 's'), EPSB, Z3.IL(CYM, '( 1 - s )'), RM))

# ------------------------------------------------------------------ F: the closed form
st('zl3gga', '( ( %s /\\ ( Z e. CC /\\ 0 < ( Re ` %s ) ) ) -> ( %s x. %s ) = 1 )' % (MP, WV('Z'), GV('Z'), GAMFG('Z', 'P')))
st('zl3gfr', '( ( %s /\\ ( Z e. CC /\\ -u 1 < ( Re ` Z ) /\\ ( Re ` Z ) < 1 ) ) -> ( %s x. %s ) = ( ( M ^c ( ( 1 / 2 ) - Z ) ) x. ( %s ` Z ) ) )'
   % (MP, GAMFG('( 1 - Z )', 'P'), GV('Z'), QQ('P')))
st('zl3fal', '( ( ( ( L e. CC /\\ H e. CC ) /\\ ( G e. CC /\\ B e. CC ) ) /\\ ( Z e. CC /\\ Z =/= 0 /\\ Z =/= 1 ) /\\ ( R e. { 0 , 1 } /\\ ( R = 1 -> ( G = ( ( Z / 2 ) x. H ) /\\ B = 1 ) ) ) ) -> '
   '( ( ( ( L x. G ) - ( R x. ( H / 2 ) ) ) + ( R x. ( ( G - B ) / ( Z - 1 ) ) ) ) + ( R / ( Z - 1 ) ) ) = ( ( L - ( R x. ( ( 1 / Z ) + ( 1 / ( 1 - Z ) ) ) ) ) x. G ) )')
HOLG = HOL('G', 'D')
RECT = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( P e. CC /\\ ( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) ) ) ) /\\ ( A crect B ) C_ D )')
QR = '( u e. D |-> if ( u = P , ( ( CC _D G ) ` P ) , ( ( G ` u ) / ( u - P ) ) ) )'
st('zl3rem', '( ( %s /\\ %s /\\ ( G ` P ) = 0 ) -> %s )' % (HOLG, RECT, HOL(QR, 'D')))
st('zl3ghl', '( %s -> ( %s /\\ %s ) )' % (MP, HOL('( x e. %s |-> %s )' % (UO, HV('x')), UO), HOL('( x e. %s |-> %s )' % (UO, GV('x')), UO)))
st('zl3dq', '( %s -> ( ( %s /\\ A. v e. %s ( v =/= 1 -> ( %s ` v ) = ( ( %s - %s ) / ( v - 1 ) ) ) ) /\\ '
   'E. c e. RR A. v e. %s ( abs ` ( %s ` v ) ) <_ ( c + ( ( abs ` %s ) + ( abs ` %s ) ) ) ) )'
   % (MP, HOL(DQ(), UO), UO, DQ(), GV('v'), GV('1'), STR, DQ(), GV('v'), GV('1')))
st('zl3fh', '( ( ( %s /\\ %s ) /\\ ( %s /\\ ( E e. CC /\\ R e. CC ) ) /\\ %s ) -> %s )'
   % (HOL('I', 'CC'), HOL('J', 'CC'), MP, HOL('D', UO), HOL(FG(), UO)))
L0 = lambda Z: '( %s + ( %s x. %s ) )' % (Z3.IL(CYM, Z), EPS, Z3.IL(CYBM, '( 1 - %s )' % Z))
FV = lambda Z: ('( ( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) + ( %s x. ( ( %s - %s ) / ( %s - 1 ) ) ) )'
                % (L0(Z), GV(Z, PAR), RM, HV(Z, PAR), RM, GV(Z, PAR), GV('1', PAR), Z))
st('zl3fch', '( %s -> %s )' % (PR, HOL(FC, UO)))
st('zl3fcv', '( ( %s /\\ ( Z e. %s /\\ Z =/= 1 ) ) -> ( %s ` Z ) = %s )' % (PR, UO, FC, FV('Z')))
st('zl3g1', '( ( %s /\\ M = 1 ) -> %s = 1 )' % (PR, GV('1', PAR)))

# ------------------------------------------------------------------ the five parts at ( M , Y ), residue R
def pc_sub(txt):
    """ZL2's PCONT pieces at the primitive level: MC -> M, YP -> Y, RP -> R"""
    return txt.replace(RP, 'R').replace(Z2.LMC, LM).replace(MC, 'M').replace(YP, 'Y')


SERYM = pc_sub(Z2.SERY)
FEYM = pc_sub(Z2.FEY)
assert CYM in SERYM and CYBM in FEYM
PCM = pc_sub(Z2.PCONT)
st('zl3sery', '( ( %s /\\ R = %s ) -> %s )' % (PR, RM, tsub(SERYM, {'F': FC})))
st('zl3fey', '( ( %s /\\ R = %s ) -> %s )' % (PR, RM, tsub(FEYM, {'F': FC, 'T': EPS, 'Q': QQ(PAR)})))
st('zl3fgr', '( %s -> E. c e. RR+ A. z e. %s ( abs ` ( %s ` z ) ) <_ ( c x. %s ) )' % (PR, STR, FC, EXB('3', 'z')))
st('zl3pc', '( ( %s /\\ R = %s ) -> E. c e. RR+ %s )' % (PR, RM, tsub(PCM, {'F': FC, 'U': UO, 'K': 'c', 'B': '3', 'T': EPS, 'Q': QQ(PAR)})))

# ------------------------------------------------------------------ headlines
st('zl3cvxh', Z3.STATEMENTS['zl3cvxh'])
FCN = tsub(FC, {'M': MC, 'Y': YP})
st('zl3lfe', '( ( %s /\\ ( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) ) ) -> ( %s ` S ) = %s )'
   % (Z1.NX, Z1.LF, tsub(Z2.GPR('S'), {'F': FCN})))
st('zl3dlbz', Z3.STATEMENTS['zl3dlbz'])


def gramcheck(labels):
    out = {}
    for lab in labels:
        p = os.path.join('worksheets', 'zl3eg_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=zl3eg_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('%s::? |- %s\n' % (n, h))
            f.write('qed::ax-1 |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower() or 'parse' in l.lower()]
        os.remove(p)
    return out


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
