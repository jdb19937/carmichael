"""Sortie EF56: helpers and the frozen statements (ExplicitFormula 5665-7480: gFun, the eta/zeta order
bookkeeping, the lower bounds of gFun, contour_zeta, the combined explicit_formula).  Built on tools/ef4lib.py.

    python3 tools/gen/ef56_main.py print                                  # the frozen table
    MM_DB=sorties/ef56.mm python3 tools/gen/ef56_main.py check [LABEL...]  # grammar check (mmatch)

Letters: ETA and GF bind z k; E1 = ( 1 DChrLF ( 0g ` ( DChr ` 1 ) ) ); LFN binds s k i; LDI binds u v;
DD binds t x w; zeros q, filters p r; cuts j; heights U (bottom, -u U) and V (top); abscissa S.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from ef4lib import *
import ef4lib as _ef4
import ef3lib as _ef3
import ef2lib as _ef2
import zc1lib as _zc1
import c10lib as _c10
import ef1lib as _ef1


def stmt(label):
    """the assertion of LABEL from sorties/ef56.mm or carmichael.mm, without |-"""
    for fn in ('sorties/ef56.mm', 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if not os.path.exists(p):
            continue
        txt = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


for _m in (_ef4, _ef3, _ef2, _c10, _zc1, _ef1):
    _m.stmt = stmt

# ---- objects -----------------------------------------------------------------------
U1 = '( 0g ` ( DChr ` 1 ) )'
Z1F = '( z e. %s |-> ( z - 1 ) )' % HP0
DLAM = lambda s: 'sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u %s ) )' % s
LDF = lambda F, s: '( ( ( CC _D %s ) ` %s ) / ( %s ` %s ) )' % (F, s, F, s)
ONE = lambda P: 'if ( %s = 1 , 1 , 0 )' % P
GFZ = lambda n: '( 1 + ( _i x. ( ( 2 x. ( _pi x. %s ) ) / ( log ` 2 ) ) ) )' % n

# ---- frozen statements (EF5) ---------------------------------------------------------
S = {}
S['ef5e11'] = '( %s ` 1 ) = 1' % E1
S['ef5em'] = '( ( S e. %s /\\ S =/= 1 ) -> ( %s ` S ) = ( ( %s ` S ) x. ( ( %s ` S ) / ( S - 1 ) ) ) )' % (HP0, ETA, GF, E1)
S['ef5gd'] = '( S e. %s -> ( ( CC _D %s ) ` S ) = ( ( log ` 2 ) x. ( 2 ^c ( 1 - S ) ) ) )' % (HP0, GF)
S['ef5g0'] = '( S e. %s -> ( ( %s ` S ) = 0 <-> E. n e. ZZ S = %s ) )' % (HP0, GF, GFZ('n'))
S['ef5ez'] = '( P e. %s -> ( ( %s holord P ) + %s ) = ( ( %s holord P ) + ( %s holord P ) ) )' % (HP0, ETA, ONE('P'), GF, E1)
S['ef5lds'] = '( ( S e. CC /\\ 1 < ( Re ` S ) ) -> %s = ( %s - %s ) )' % (LDF(ETA, 'S'), LDF(GF, 'S'), DLAM('S'))
HYPS = {}


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'ef56', 'gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'ef56gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ef56gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            hs = HYPS.get(lab, [])
            for i, (n, h) in enumerate(hs):
                f.write('h%d::ef56gc%s.%s |- %s\n' % (i + 10, lab, n, h))
            f.write('h1::ef56gc%s.x |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


def ORDER():
    return list(S)




# ---- step helpers ---------------------------------------------------------------------
def hol_eta(w, A0):
    """( A0 -> HOLF(ETA, HP0) )"""
    z = w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], '0le0', '0 <_ 0')], 'pm3.2i', '( 0 e. RR /\\ 0 <_ 0 )')], 'a1i', '( %s -> ( 0 e. RR /\\ 0 <_ 0 ) )' % A0)
    return w.s([z, w.inst('etahol')], 'syl', '( %s -> %s )' % (A0, HOLF(ETA, HP0)))


def hol_gf(w, A0):
    return w.s([w.s([], 'gfhol', HOLF(GF, HP0))], 'a1i', '( %s -> %s )' % (A0, HOLF(GF, HP0)))


def nx1(w, A0):
    """( A0 -> ( 1 e. NN /\\ U1 e. ( Base ` ( DChr ` 1 ) ) ) )"""
    from zc1_c import u1base
    return w.s([w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0), u1base(w, A0)], 'jca',
               '( %s -> ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) )' % (A0, U1))


def hol_e1(w, A0):
    return w.s([nx1(w, A0), w.inst('zl1ehol')], 'syl', '( %s -> %s )' % (A0, HOLF(E1, HP0)))


def hp_facts(w, A0, xh, x):
    """( A0 -> x e. CC ), ( A0 -> 0 < ( Re ` x ) ) from ( A0 -> x e. HP0 )"""
    from zc1_q import hp_cc
    return hp_cc(w, A0, xh, x)

# ---- EF6 objects ---------------------------------------------------------------------
HDG = '( b e. ( D i^i E ) |-> ( ( F ` b ) - ( G ` b ) ) )'
S['ef6ldf'] = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ G e. ( E -cn-> CC ) ) /\\ ( A cseg B ) C_ ( D i^i E ) ) -> '
               '( %s e. ( ( D i^i E ) -cn-> CC ) /\\ ( %s lint <. A , B >. ) = ( ( F lint <. A , B >. ) - ( G lint <. A , B >. ) ) ) )') % (HDG, HDG)


# ---- (statements added below this line are frozen as they are written) ----
LD0E = '{ v e. %s | ( %s ` v ) =/= 0 }' % (HP0, ETA)
LD0G = '{ v e. %s | ( %s ` v ) =/= 0 }' % (HP0, GF)
HE = LDI(ETA)
HG = LDI(GF)
D2 = '( %s i^i %s )' % (LD0E, LD0G)
HD = '( b e. %s |-> ( ( %s ` b ) - ( %s ` b ) ) )' % (D2, HE, HG)
DLVZ = lambda z: 'sum_ k e. NN ( ( ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) ) x. ( Lam ` k ) ) x. ( k ^c -u %s ) )' % (U1, z)
S['ef6pt'] = '( ( Y e. RR+ /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) -> ( Z e. %s /\\ ( %s ` Z ) = -u ( %s x. ( ( Y ^c Z ) / Z ) ) ) )' % (D2, HD, DLVZ('Z'))


def dlvz_cc(w, A, Sp, sc, s1):
    """( A -> DLVZ(Sp) e. CC ) from Sp e. CC and 1 < Re Sp (lchvmcvg, isumcl at the character mod 1); A must not contain k, n"""
    import congr as _cg
    from cl import lift
    c = Ctx(w, A)
    Ak = '( %s /\\ k e. NN )' % A
    sk = Ctx(w, Ak)
    kn = sk([], 'simpr', 'k e. NN')
    NX1 = '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1
    nx = nx1(w, A)
    CHK = '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) )' % U1
    xk = sk([sk([lift(w, nx, Ak), kn], 'jca', '( %s /\\ k e. NN )' % NX1), w.inst('lchrcl')], 'syl', '%s e. CC' % CHK)
    lk = sk([sk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    kz = sk([sk([kn], 'nncnd', 'k e. CC'), sk([lift(w, sc, Ak)], 'negcld', '-u %s e. CC' % Sp)], 'cxpcld', '( k ^c -u %s ) e. CC' % Sp)
    VK = '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u %s ) )' % (CHK, Sp)
    vk = sk([sk([xk, lk], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHK), kz], 'mulcld', '%s e. CC' % VK)
    VN = '( ( ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` n ) ) x. ( Lam ` n ) ) x. ( n ^c -u %s ) )' % (U1, Sp)
    fv, _ = _cg.mptval(w, Ak, 'n', 'NN', VN, 'k', kn, exs=sk([vk], 'elexd', '%s e. _V' % VK), gen=w.g)
    cvg = c([c([nx, c([sc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (Sp, Sp))], 'jca', '( %s /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (NX1, Sp, Sp)), w.inst('lchvmcvg')], 'syl',
            'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % VN)
    return c([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c([], '1zzd', '1 e. ZZ'), fv, vk, cvg], 'isumcl', '%s e. CC' % DLVZ(Sp))
Z1S = {'N': '1', 'X': U1}
RHZ = tsub(_ef1.RHF, Z1S)
PSZ = lambda C: tsub(_ef1.PS(C), Z1S)
S['ef6rm'] = '( ( ( Y e. RR+ /\\ C e. RR /\\ 1 < C ) /\\ T e. RR ) -> ( %s lint <. %s , %s >. ) = -u %s )' % (HD, _ef1.LO('C', 'T'), _ef1.HI('C', 'T'), PSZ('C'))


def hd_cn(w, A0, yp):
    """( A0 -> HD e. ( D2 -cn-> CC ) ) from yp : ( A0 -> Y e. RR+ ) (ef3ldc, rescncf, subcncf)"""
    c = Ctx(w, A0)
    he = c([hol_eta(w, A0), yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (HE, LD0E))
    hg = c([hol_gf(w, A0), yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (HG, LD0G))
    s1 = c.a1(w.s([], 'inss1', '%s C_ %s' % (D2, LD0E)), '%s C_ %s' % (D2, LD0E))
    s2 = c.a1(w.s([], 'inss2', '%s C_ %s' % (D2, LD0G)), '%s C_ %s' % (D2, LD0G))
    def resmp(M, Dm, sst, mcn):
        mf = c([mcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (M, Dm))
        rc = c([mcn, c([sst, w.inst('rescncf')], 'syl', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (M, Dm, M, D2, D2))], 'mpd', '( %s |` %s ) e. ( %s -cn-> CC )' % (M, D2, D2))
        eq = c([mf, sst], 'feqresmpt', '( %s |` %s ) = ( b e. %s |-> ( %s ` b ) )' % (M, D2, D2, M))
        return c([eq, rc], 'eqeltrrd', '( b e. %s |-> ( %s ` b ) ) e. ( %s -cn-> CC )' % (D2, M, D2))
    fr = resmp(HE, LD0E, s1, he); gr = resmp(HG, LD0G, s2, hg)
    return c([fr, gr], 'subcncf', '%s e. ( %s -cn-> CC )' % (HD, D2))


S['ef6rx'] = ('( ( ( Y e. RR /\\ ; ; 1 0 0 <_ Y ) /\\ ( ( T e. RR /\\ 0 < T ) /\\ ( U e. RR /\\ V e. RR ) /\\ ( U <_ V /\\ ( V - U ) <_ 1 ) ) /\\ '
              'A. t e. ( U [,] V ) T <_ ( abs ` t ) ) -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ ( 8 x. ( ( Y x. ( log ` Y ) ) / T ) ) )') % (HD, PTL(C1, 'U'), PTL(C1, 'V'))
ZSK = '( %s u. %s )' % (ZS('F', 'K'), ZS('F', '( K + 1 )'))
S['ef6gg'] = ('( ( ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) /\\ ( ( K e. RR /\\ H e. ( K [,] ( K + 1 ) ) ) /\\ ( abs ` H ) <_ ( T + 1 ) ) /\\ '
              'A. p e. %s ( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - ( Im ` p ) ) ) ) -> A. v e. ( ( 1 / 2 ) [,] 3 ) %s )') % (DD(), ZSK, GAP, LT4, GOOD(PTL('v', 'H')))
IMN = lambda n: '( ( 2 x. ( _pi x. %s ) ) / ( log ` 2 ) )' % n
S['ef6gz'] = '( ( ( n e. ZZ /\\ m e. ZZ ) /\\ ( abs ` ( %s - %s ) ) <_ ( ; 1 3 / 4 ) ) -> n = m )' % (IMN('n'), IMN('m'))
AIM = '( abs o. Im )'
ZSG = lambda K: ZS(GF, K)
S['ef6go'] = '( K e. RR -> ( ( %s " %s ) e. Fin /\\ ( # ` ( %s " %s ) ) <_ 1 ) )' % (AIM, ZSG('K'), AIM, ZSG('K'))
BZF = BZ('F', '( T + 4 )')
NZE = 'A. v e. ( ( 1 / 2 ) [,] 3 ) ( ( F ` %s ) =/= 0 /\\ ( F ` %s ) =/= 0 )' % (PTL('v', '-u U'), PTL('v', 'V'))
HLN6 = ('( ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ -. S e. ( Re " %s ) ) /\\ ( ( K e. NN /\\ G : ( 0 ... K ) --> RR ) /\\ ( ( G ` 0 ) = -u U /\\ ( G ` K ) = V ) ) /\\ '
        '( A. e e. ( 1 ..^ K ) -. ( G ` e ) e. ( Im " %s ) /\\ A. e e. ( 0 ... K ) ( -u U <_ ( G ` e ) /\\ ( G ` e ) <_ V ) ) ) )') % (YT, HUV, NZE, SS8, BZF, BZF)
S['ef6ln'] = '( %s -> ( A. j e. ( 0 ... K ) A. x e. ( S [,] %s ) ( F ` %s ) =/= 0 /\\ A. t e. ( -u U [,] ( T + 2 ) ) ( F ` %s ) =/= 0 ) )' % (
    HLN6, C1, PTL('x', CHN('j')), PTL('S', 't'))


def bz_inF(E, A, U_, ur, q, qcc, fz, hy, lv, F='F'):
    """( A -> q e. BZ(F, U_) ) from lin facts 1/2 <_ Re q <_ 3/2, -U_ <_ Im q <_ U_ (EF4's bz_in for any F)"""
    from ef4_a import ptc
    from ef4_g import elrab_pack
    w = E.w
    cc = Ctx(w, A)
    half, th = numst8(w, A, '( 1 / 2 )', 'RR'), numst8(w, A, '( 3 / 2 )', 'RR')
    nu = cc([ur], 'renegcld', '-u %s e. RR' % U_)
    ac = ptc(cc, '( 1 / 2 )', '-u %s' % U_, half, nu); bc = ptc(cc, '( 3 / 2 )', U_, th, ur)
    A_, B_ = '( ( 1 / 2 ) + ( _i x. -u %s ) )' % U_, '( ( 3 / 2 ) + ( _i x. %s ) )' % U_
    hy2 = hy + E.corners(cc, '( 1 / 2 )', '-u %s' % U_, half, nu) + E.corners(cc, '( 3 / 2 )', U_, th, ur)
    qin = crect_in(w, A, A_, B_, ac, bc, q, qcc, hy2, lv)
    return elrab_pack(w, A, 'r', '( %s crect %s )' % (A_, B_), '( %s ` r ) = 0' % F, q, qin, fz)


def numst8(w, A, n, dom):
    from c8_o import numst
    return numst(w, A, n, dom)
LDF_ = LDI('F')
HCHF = HCH.replace(LFN, 'F')
SRF = 'sum_ q e. %s ( ( F holord q ) x. ( ( Y ^c q ) / q ) )' % ZR('S', C1, '-u U', 'V', 'F')
LIF = lambda a, b, F='F': '( %s lint <. %s , %s >. )' % (LDI(F), a, b)
BOTF = LIF(PTL('S', '-u U'), PTL(C1, '-u U'))
TOPF = LIF(PTL('S', 'V'), PTL(C1, 'V'))
LEFTF = LIF(PTL('S', '-u U'), PTL('S', 'V'))
RF = LIF(PTL(C1, '-u U'), PTL(C1, 'V'))
S['ef6rid'] = ('( ( ( %s /\\ %s ) /\\ ( ( ( U e. RR /\\ V e. RR ) /\\ ( T <_ U /\\ T <_ V ) ) /\\ ( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < %s ) ) ) /\\ %s ) -> '
               '( ( %s x. %s ) = ( ( ( %s + %s ) - %s ) - %s ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) ) )') % (
    DD(), YT, C1, HCHF, TPI, SRF, BOTF, RF, TOPF, LEFTF, BOTF, TOPF, LEFTF, RF)


def DDR(F='F', A='A'):
    """DD with the bound letters t, x, w renamed h, m, n"""
    return tsub(DD(F, A), {'t': 'h', 'x': 'm', 'w': 'n'})


def dd_ren(w, F='F', A='A'):
    """closed step ( DD(F, A) <-> DDR(F, A) )"""
    P1, P2, P3 = top_and(DD(F, A))
    Q1, Q2 = top_and(P3)
    body_t = Q1[len('A. t e. RR '):]
    ph_t, al_x = top_and(body_t)
    X = al_x.split(' ( abs ` ')[0][len('A. x e. '):]
    psi = al_x[len('A. x e. %s ' % X):]
    e1, psm = cbvral(w, X, 'x', 'm', psi)
    al_m = 'A. m e. %s %s' % (X, psm)
    e2 = w.s([e1], 'anbi2i', '( ( %s /\\ %s ) <-> ( %s /\\ %s ) )' % (ph_t, al_x, ph_t, al_m))
    B1 = '( %s /\\ %s )' % (ph_t, al_x)
    B2 = '( %s /\\ %s )' % (ph_t, al_m)
    e3 = w.s([e2], 'ralbii', '( A. t e. RR %s <-> A. t e. RR %s )' % (B1, B2))
    e4, B3 = cbvral(w, 'RR', 't', 'h', B2)
    e34 = w.s([e3, e4], 'bitri', '( A. t e. RR %s <-> A. h e. RR %s )' % (B1, B3))
    chi = Q2[len('A. w e. %s ' % HP0):]
    e5, chn = cbvral(w, HP0, 'w', 'n', chi)
    Q2n = 'A. n e. %s %s' % (HP0, chn)
    P3n = '( A. h e. RR %s /\\ %s )' % (B3, Q2n)
    e6 = w.s([e34, e5], 'anbi12i', '( %s <-> %s )' % (P3, P3n))
    DN = '( %s /\\ %s /\\ %s )' % (P1, P2, P3n)
    assert ' '.join(DN.split()) == DDR(F, A), (DN, DDR(F, A))
    return w.s([w.s([], 'biid', '( %s <-> %s )' % (P1, P1)), w.s([], 'biid', '( %s <-> %s )' % (P2, P2)), e6], '3anbi123i', '( %s <-> %s )' % (DD(F, A), DN))
CUTS, _zfF = top_and(HCHF)
ZFX = lambda F: _zfF.replace('( F ` ', '( %s ` ' % F)
SRX = lambda F: SRF.replace('( F ` p )', '( %s ` p )' % F).replace('( F holord q )', '( %s holord q )' % F)
LIX = lambda a, b, F: '( %s lint <. %s , %s >. )' % (LDI(F), a, b)
EDG = {}
for _F, _n in ((ETA, 'E'), (GF, 'G')):
    EDG['BOT' + _n] = LIX(PTL('S', '-u U'), PTL(C1, '-u U'), _F)
    EDG['TOP' + _n] = LIX(PTL('S', 'V'), PTL(C1, 'V'), _F)
    EDG['LEFT' + _n] = LIX(PTL('S', '-u U'), PTL('S', 'V'), _F)
    EDG['R' + _n] = LIX(PTL(C1, '-u U'), PTL(C1, 'V'), _F)
EBD = '( %s lint <. %s , %s >. )' % (HD, PTL(C1, '-u U'), PTL(C1, '-u T'))
ETD = '( %s lint <. %s , %s >. )' % (HD, PTL(C1, 'T'), PTL(C1, 'V'))
PSZ1 = PSZ(C1)
SRE, SRG = SRX(ETA), SRX(GF)
UVT = '( ( U e. RR /\\ V e. RR ) /\\ ( T <_ U /\\ T <_ V ) )'
SSC = '( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < %s ) )' % C1
HID = '( ( ( %s /\\ %s ) /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (YT, UVT, SSC, CUTS, ZFX(ETA), ZFX(GF))
IDL = '( %s + ( ( %s x. %s ) - ( %s x. %s ) ) )' % (PSZ1, TPI, SRE, TPI, SRG)
IDR = '( ( ( ( %s - %s ) - ( %s - %s ) ) + ( %s + %s ) ) - ( %s - %s ) )' % (EDG['BOTE'], EDG['BOTG'], EDG['TOPE'], EDG['TOPG'], EBD, ETD, EDG['LEFTE'], EDG['LEFTG'])
IDC = '( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) /\\ %s e. CC )' % (
    EDG['BOTE'], EDG['BOTG'], EDG['TOPE'], EDG['TOPG'], EDG['LEFTE'], EDG['LEFTG'], EBD, ETD, PSZ1)
S['ef6id'] = '( %s -> ( %s = %s /\\ %s ) )' % (HID, IDL, IDR, IDC)
S['ef6o0'] = '( ( %s /\\ ( P e. %s /\\ ( F ` P ) =/= 0 ) ) -> ( F holord P ) = 0 )' % (HOLF('F', HP0), HP0)
ZRC = lambda F: ZR('S', 'C', '-u U', 'V', F)
TRM = lambda F, q='q': '( ( %s holord %s ) x. ( ( Y ^c %s ) / %s ) )' % (F, q, q, q)
SREc = 'sum_ q e. %s %s' % (ZRC(ETA), TRM(ETA))
SRGc = 'sum_ q e. %s %s' % (ZRC(GF), TRM(GF))
SRZc = 'sum_ q e. %s %s' % (ZRC(ETA), TRM(E1))
HBK = ('( ( Y e. RR+ /\\ ( S e. RR /\\ ( ( 1 / 2 ) <_ S /\\ S < 1 ) ) ) /\\ ( ( C e. RR /\\ ( 1 < C /\\ C <_ ( 3 / 2 ) ) ) /\\ '
       '( ( U e. RR /\\ V e. RR ) /\\ ( 0 < U /\\ 0 < V ) ) ) )')
S['ef6bk'] = '( %s -> ( ( %s - %s ) = ( %s - Y ) /\\ ( %s e. CC /\\ %s e. CC /\\ %s e. CC ) ) )' % (HBK, SREc, SRGc, SRZc, SREc, SRGc, SRZc)
CFZ = ZF(E1, '( 1 / 2 )', 'T')
RFE = ZR('S', C1, '-u U', 'V', ETA)
TZ = TRM(E1)
SCz = 'sum_ q e. %s %s' % (CFZ, TZ)
SRz = 'sum_ q e. %s %s' % (RFE, TZ)
NZ2E = 'A. v e. ( ( 1 / 2 ) [,] 3 ) ( ( %s ` %s ) =/= 0 /\\ ( %s ` %s ) =/= 0 )' % (ETA, PTL('v', '-u U'), ETA, PTL('v', 'V'))
HZ6 = '( %s /\\ ( %s /\\ %s ) /\\ %s )' % (YT, HUV, SS8, NZ2E)
LNTz = '( log ` ( 1 x. ( T + 2 ) ) )'
LN4z = '( log ` ( 1 x. ( T + 4 ) ) )'
ZB1 = '( ( ; ; ; ; 7 2 0 0 0 x. ( Y ^c S ) ) x. ( %s ^ 2 ) )' % LNTz
ZB2 = '( ( %s x. Y ) x. ( %s / T ) )' % (KB, LN4z)
S['ef6zs1'] = '( %s -> ( abs ` sum_ q e. ( %s \\ %s ) %s ) <_ %s )' % (HZ6, CFZ, RFE, TZ, ZB1)
S['ef6zs2'] = '( %s -> ( abs ` sum_ q e. ( %s \\ %s ) %s ) <_ %s )' % (HZ6, RFE, CFZ, TZ, ZB2)
S['ef6zs'] = '( %s -> ( ( abs ` ( %s - %s ) ) <_ ( %s + %s ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (HZ6, SCz, SRz, ZB1, ZB2, SCz, SRz)
LT41 = '( log ` ( 1 x. ( T + 4 ) ) )'
S['ef6pw'] = '( ( %s /\\ ( S e. RR /\\ S <_ ( 5 / 8 ) ) ) -> ( A. j e. ( 0 ..^ M ) A. q e. %s ( Re ` q ) =/= S /\\ %s <_ ( %s x. ( %s ^ 2 ) ) ) )' % (
    _ef3.SGH, ZK('j', 'P', GF), PHI('S', 'P', 'M', GF), KS, LT41)
KZ = '; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0'      # contour_zeta 1000000000 (Lean's; 2 pi normalised)
EDGE6 = '( ( ( 4 x. %s ) + ( 2 x. %s ) ) + ( 2 x. %s ) )' % (HB, RB, LB)
S['ef6nm'] = ('( ( ( N e. NN /\\ %s ) /\\ %s /\\ ( ( A e. RR /\\ B e. RR ) /\\ ( A <_ %s /\\ B <_ %s ) ) ) -> '
              '( A + ( ( 2 x. _pi ) x. B ) ) <_ ( ( 2 x. _pi ) x. ( %s x. ( %s + %s ) ) ) )') % (YT, SS8, EDGE6, ZB, KZ, P1, P2)
L4 = LT41
BZE4, BZG4 = BZ(ETA, '( T + 4 )'), BZ(GF, '( T + 4 )')
HGDX = lambda F: 'A. v e. ( ( 1 / 2 ) [,] 3 ) ( %s /\\ %s )' % (GOOD(PTL('v', '-u U'), F, L4), GOOD(PTL('v', 'V'), F, L4))
HWM6 = '( M e. NN0 /\\ ( V <_ ( -u U + ( M / 2 ) ) /\\ ( -u U + ( M / 2 ) ) <_ ( T + 2 ) ) )'
HSG6 = ('( ( %s /\\ ( -. S e. ( Re " %s ) /\\ -. S e. ( Re " %s ) ) ) /\\ %s /\\ ( A. j e. ( 0 ..^ M ) A. q e. %s ( Re ` q ) =/= S /\\ %s <_ ( %s x. ( %s ^ 2 ) ) ) )') % (
    SS8, BZE4, BZG4, HWM6, ZK('j', '-u U', ETA), PHI('S', '-u U', 'M', ETA), KS, L4)
STEP6 = 'A. j e. ( 0 ..^ K ) ( %s < %s /\\ ( %s - %s ) <_ 1 )' % (CHN('j'), GJ1, GJ1, CHN('j'))
HCT6 = ('( ( ( K e. NN /\\ G : ( 0 ... K ) --> RR ) /\\ %s /\\ ( ( G ` 0 ) = -u U /\\ ( G ` K ) = V ) ) /\\ '
        '( A. j e. ( 1 ..^ K ) -. ( G ` j ) e. ( Im " %s ) /\\ A. j e. ( 1 ..^ K ) -. ( G ` j ) e. ( Im " %s ) /\\ A. j e. ( 0 ... K ) ( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V ) ) )') % (
    STEP6, BZE4, BZG4)
P1z, P2z = tsub(P1, {'N': '1'}), tsub(P2, {'N': '1'})
CBNDZ = '( abs ` ( ( %s + ( %s x. %s ) ) - ( %s x. Y ) ) ) <_ ( ( 2 x. _pi ) x. ( %s x. ( %s + %s ) ) )' % (PSZ1, TPI, SCz, TPI, KZ, P1z, P2z)
S['ef6core'] = '( ( ( %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) /\\ %s /\\ %s ) -> %s )' % (YT, HUV, HGDX(ETA), HGDX(GF), HSG6, HCT6, CBNDZ)
KB1 = '( -u ( T + 1 ) + 1 )'
WG4 = '( ( %s u. %s ) u. ( %s u. %s ) )' % (ZSG('T'), ZSG('( T + 1 )'), ZSG('-u ( T + 1 )'), ZSG(KB1))
GG = '( %s " %s )' % (AIM, WG4)
S['ef6gc'] = '( ( T e. RR /\\ 2 <_ T ) -> ( %s e. Fin /\\ %s C_ RR /\\ ( # ` %s ) <_ ( ; 1 6 x. %s ) ) )' % (GG, GG, GG, L4)
IVT = '( T [,] ( T + 1 ) )'
S['ef6gd'] = ('( ( ( T e. RR /\\ 2 <_ T ) /\\ ( H e. %s /\\ A. g e. %s ( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - g ) ) ) ) -> '
              '( A. v e. ( ( 1 / 2 ) [,] 3 ) %s /\\ A. v e. ( ( 1 / 2 ) [,] 3 ) %s ) )') % (IVT, GG, GAP, L4, GOOD(PTL('v', 'H'), GF, L4), GOOD(PTL('v', '-u H'), GF, L4))
S['ef6cnt'] = '( %s -> %s )' % (YT, CBNDZ)
KF = '; ; ; ; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0 0 0 0'      # explicit_formula C5 = 10^12 (Lean's)
PSIz = tsub(PSI, Z1S)
LNYz = tsub(LNY, {'N': '1'})
S['ef6z1'] = '( %s -> ( abs ` ( ( %s - Y ) + %s ) ) <_ ( %s x. ( ( %s + %s ) + ( %s ^ 2 ) ) ) )' % (YT, PSIz, SCz, KF, P1z, P2z, LNYz)
U0N = '( 0g ` ( DChr ` N ) )'
S['ef6ef'] = ('( ( ( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ ( X =/= %s \\/ ( N = 1 /\\ X = %s ) ) ) /\\ ( %s /\\ N <_ Y ) ) -> '
              '( abs ` ( ( %s - if ( X = %s , Y , 0 ) ) + %s ) ) <_ ( %s x. ( ( %s + %s ) + ( %s ^ 2 ) ) ) )') % (U0N, U0N, YT, PSI, U0N, SCE, KF, P1, P2, LNY)
