"""T6: the entry loop `forEntries` (blueprint 3.3): the peek at a position
(`tm2lfe1a`, `tm2lfe1b`, `tm2lfe1`), one iteration (`tm2lfe2`), the loop
by `tm2hitr` (`tm2lfe3`) and the assembly (`tm2lfe`)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

PEEKS = PEEKL('K', 'F', 'A')
TESTS = TESTL('C', "A'", 'E')
FTY = "F e. ( %s ^m ( %s X. %s ) )" % (S('T'), S('T'), OPT)
CTY = 'C e. ( 2o ^m %s )' % S('T')
NL = '( # ` L )'
def NVR(r, z): return NV('F', r, z)
IF1 = 'A. r e. N A. z e. %s ( %s e. N /\\ ( C ` %s ) = 1o )' % (B4, NVR('r', 'z'), NVR('r', 'z'))
IF2 = 'A. r e. N ( %s e. N /\\ -. ( C ` %s ) = 1o )' % (NVR('r', '2'), NVR('r', '2'))
IFACE = '( %s /\\ %s )' % (IF1, IF2)
PTY = 'P : ( 0 ... %s ) --> %s' % (NL, STK('T'))
def PKF(j): return '( ( P ` %s ) ` K ) = %s' % (j, LST(DROP('L', j), 'R'))
PK = 'A. j e. ( 0 ... %s ) %s' % (NL, PKF('j'))
def HBF(j): return HR(CL("A'", 'N', '( P ` %s )' % j), 'T', 'M', CL('A"', 'N', '( P ` ( %s + 1 ) )' % j), 'Y')
HB = 'A. j e. ( 0 ..^ %s ) %s' % (NL, HBF('j'))
LAB1 = "( P1 e. %s /\\ A e. %s /\\ A' e. %s )" % (L('T'), L('T'), L('T'))
LAB2 = '( A" e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), FZ8)
PROG = '( ( M ` P1 ) = %s /\\ ( M ` A ) = %s /\\ ( M ` A" ) = %s )' % (PEEKS, TESTS, PEEKS)
PHF = ('( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( N C_ %s /\\ %s ) ) '
       '/\\ ( ( L e. %s /\\ R e. %s /\\ Y e. NN0 ) /\\ ( %s /\\ %s ) /\\ %s ) )'
       % (PHM6, PROG, LAB1, LAB2, FTY, CTY, S('T'), IFACE, WWB, WG, PTY, PK, HB))
def NF(j): return '{ q e. N | ( ( C ` q ) = 1o <-> %s < %s ) }' % (j, NL)
NFIN = '{ q e. N | -. ( C ` q ) = 1o }'
def DJ(j): return '( P ` %s )' % j
def ZJ(j): return '( ( %s ` K ) ` 0 )' % DJ(j)
def XJ(j): return '( ( %s ` K ) substr <. 1 , ( # ` ( %s ` K ) ) >. )' % (DJ(j), DJ(j))


def prelude(w, ph, lift):
    """steps for the conjuncts of PHF; `lift(st, f)` moves a step at PHF to ph"""
    def sp(hyps, ref, f):
        return lift(w.s(hyps, ref, '( %s -> %s )' % (PHF, f)), f)
    p1 = sp([], 'simp1', '( %s /\\ %s )' % (PHM6, PROG))
    p6 = w.s([p1], 'simpld', '( %s -> %s )' % (ph, PHM6))
    phm = w.s([p6], 'simpld', '( %s -> %s )' % (ph, PHM))
    geq = w.s([p6], 'simprd', '( %s -> ( 1st ` ( 1st ` T ) ) = TMGam )' % ph)
    prog = w.s([p1], 'simprd', '( %s -> %s )' % (ph, PROG))
    mp1 = w.s([prog, w.inst('simp1')], 'syl', '( %s -> ( M ` P1 ) = %s )' % (ph, PEEKS))
    ma = w.s([prog, w.inst('simp2')], 'syl', '( %s -> ( M ` A ) = %s )' % (ph, TESTS))
    ma2 = w.s([prog, w.inst('simp3')], 'syl', '( %s -> ( M ` A" ) = %s )' % (ph, PEEKS))
    p2 = sp([], 'simp2', '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( N C_ %s /\\ %s ) )' % (LAB1, LAB2, FTY, CTY, S('T'), IFACE))
    labs = w.s([p2, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, LAB1, LAB2))
    lab1 = w.s([labs], 'simpld', '( %s -> %s )' % (ph, LAB1))
    lab2 = w.s([labs], 'simprd', '( %s -> %s )' % (ph, LAB2))
    p1l = w.s([lab1, w.inst('simp1')], 'syl', '( %s -> P1 e. %s )' % (ph, L('T')))
    al = w.s([lab1, w.inst('simp2')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    a1l = w.s([lab1, w.inst('simp3')], 'syl', "( %s -> A' e. %s )" % (ph, L('T')))
    a2l = w.s([lab2, w.inst('simp1')], 'syl', '( %s -> A" e. %s )' % (ph, L('T')))
    el = w.s([lab2, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([lab2, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, FZ8))
    fc = w.s([p2, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, CTY))
    ff = w.s([fc], 'simpld', '( %s -> %s )' % (ph, FTY))
    cc = w.s([fc], 'simprd', '( %s -> %s )' % (ph, CTY))
    ni = w.s([p2, w.inst('simp3')], 'syl', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), IFACE))
    nss = w.s([ni], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    ifc = w.s([ni], 'simprd', '( %s -> %s )' % (ph, IFACE))
    if1 = w.s([ifc], 'simpld', '( %s -> %s )' % (ph, IF1))
    if2 = w.s([ifc], 'simprd', '( %s -> %s )' % (ph, IF2))
    p3 = sp([], 'simp3', '( ( L e. %s /\\ R e. %s /\\ Y e. NN0 ) /\\ ( %s /\\ %s ) /\\ %s )' % (WWB, WG, PTY, PK, HB))
    lry = w.s([p3, w.inst('simp1')], 'syl', '( %s -> ( L e. %s /\\ R e. %s /\\ Y e. NN0 ) )' % (ph, WWB, WG))
    ll = w.s([lry, w.inst('simp1')], 'syl', '( %s -> L e. %s )' % (ph, WWB))
    rr = w.s([lry, w.inst('simp2')], 'syl', '( %s -> R e. %s )' % (ph, WG))
    yy = w.s([lry, w.inst('simp3')], 'syl', '( %s -> Y e. NN0 )' % ph)
    ppk = w.s([p3, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, PTY, PK))
    pty = w.s([ppk], 'simpld', '( %s -> %s )' % (ph, PTY))
    pk = w.s([ppk], 'simprd', '( %s -> %s )' % (ph, PK))
    hb = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HB))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kd, ge = gamk(w, ph, 'K', geq, kk)
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    return dict(phm=phm, geq=geq, mp1=mp1, ma=ma, ma2=ma2, p1l=p1l, al=al, a1l=a1l, a2l=a2l, el=el,
                kk=kk, ff=ff, cc=cc, nss=nss, if1=if1, if2=if2, ll=ll, rr=rr, yy=yy, pty=pty, pk=pk,
                hb=hb, tv=tv, kd=kd, ge=ge, nl=nl)


def pkat(w, ph, u, J, jfz):
    """( ph -> ( ( P ` J ) ` K ) = LST( DROP( L , J ) , R ) ) from jfz : J e. ( 0 ... NL )"""
    cg, new = w.wcongr(PKF('j'), {'j': J}, 'j = %s' % J, {'j': w.s([], 'id', '( j = %s -> j = %s )' % (J, J))})
    assert new == PKF(J), new
    return w.s([cg, u['pk'], jfz], 'rspcdva', '( %s -> %s )' % (ph, PKF(J)))


def nfss(w, ph, j, nss):
    """( ph -> NF(j) C_ S ) and ( ph -> NF(j) C_ N )"""
    a = w.s([], 'ssrab2', '%s C_ N' % NF(j))
    aa = w.s([a], 'a1i', '( %s -> %s C_ N )' % (ph, NF(j)))
    return w.s([aa, nss], 'sstrd', '( %s -> %s C_ %s )' % (ph, NF(j), S('T'))), aa


def innf(w, ante, X, j, xin, bic):
    """( ante -> X e. NF(j) ) from xin : X e. N, bic : ( ( C ` X ) = 1o <-> j < NL )"""
    c1 = w.s([], 'fveq2', '( q = %s -> ( C ` q ) = ( C ` %s ) )' % (X, X))
    c2 = w.s([c1], 'eqeq1d', '( q = %s -> ( ( C ` q ) = 1o <-> ( C ` %s ) = 1o ) )' % (X, X))
    c3 = w.s([c2], 'bibi1d', '( q = %s -> ( ( ( C ` q ) = 1o <-> %s < %s ) <-> ( ( C ` %s ) = 1o <-> %s < %s ) ) )' % (X, j, NL, X, j, NL))
    return w.s([c3, xin, bic], 'elrabd', '( %s -> %s e. %s )' % (ante, X, NF(j)))


def outnf(w, ante, X, j, xin):
    """( ante -> ( ( C ` X ) = 1o <-> j < NL ) ) from xin : X e. NF(j)"""
    c1 = w.s([], 'fveq2', '( q = %s -> ( C ` q ) = ( C ` %s ) )' % (X, X))
    c2 = w.s([c1], 'eqeq1d', '( q = %s -> ( ( C ` q ) = 1o <-> ( C ` %s ) = 1o ) )' % (X, X))
    c3 = w.s([c2], 'bibi1d', '( q = %s -> ( ( ( C ` q ) = 1o <-> %s < %s ) <-> ( ( C ` %s ) = 1o <-> %s < %s ) ) )' % (X, j, NL, X, j, NL))
    return w.s([c3, xin], 'elrabrd', '( %s -> ( ( C ` %s ) = 1o <-> %s < %s ) )' % (ante, X, j, NL))


RAL = lambda j: 'A. r e. N %s e. %s' % (NVR('r', ZJ(j)), NF(j))
RALU = lambda j: 'A. u e. N %s e. %s' % (NVR('u', ZJ(j)), NF(j))


def genr(w, ph, inn, j):
    """from inn at ( ph /\ u e. N ), conclude ( ph -> RAL(j) ) (T2 trap 3: the
    antecedent binds r, so generalise over u and rename)"""
    ru = w.s([inn], 'ralrimiva', '( %s -> %s )' % (ph, RALU(j)))
    B = lambda x: '%s e. %s' % (NVR(x, ZJ(j)), NF(j))
    cg, new = w.wcongr(B('u'), {'u': 'r'}, 'u = r', {'u': w.s([], 'id', '( u = r -> u = r )')})
    assert new == B('r'), new
    cb = w.s([cg], 'cbvralvw', '( %s <-> %s )' % (RALU(j), RAL(j)))
    cba = w.s([cb], 'a1i', '( %s -> ( %s <-> %s ) )' % (ph, RALU(j), RAL(j)))
    w.qed([cba, ru], 'mpbid', '( %s -> %s )' % (ph, RAL(j)))


def tm2lfe1a():
    lab = 'tm2lfe1a'
    ph = '( %s /\\ J e. ( 0 ..^ %s ) )' % (PHF, NL)
    w = W(lab, 'The entry loop, the peek before the end of the list: the head of the '
               'stack is a bit or a comma, so the handler sets the loop test.')
    u = prelude(w, ph, lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph, f)))
    jo = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ %s ) )' % (ph, NL))
    jfz = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... %s ) )' % (ph, NL))
    pkj = pkat(w, ph, u, 'J', jfz)
    DR = DROP('L', 'J'); DR1 = DROP('L', '( J + 1 )')
    dr = w.s([u['ll'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DR, WWB))
    d1 = w.s([u['ll'], jo, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( <" ( L ` J ) "> ++ %s ) )' % (ph, DR, DR1))
    lj = w.s([u['ll'], jo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` J ) e. %s )' % (ph, WB))
    ljs = w.s([lj], 's1cld', '( %s -> <" ( L ` J ) "> e. %s )' % (ph, WWB))
    s1n = w.s([], 's1nz', '<" ( L ` J ) "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" ( L ` J ) "> =/= (/) )' % ph)
    dr1 = w.s([u['ll'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DR1, WWB))
    cn = w.s([ljs, s1na, dr1, w.inst('ccatn0')], 'syl3anc', '( %s -> ( <" ( L ` J ) "> ++ %s ) =/= (/) )' % (ph, DR1))
    drn = w.s([d1, cn], 'eqnetrd', '( %s -> %s =/= (/) )' % (ph, DR))
    hd = w.s([dr, u['rr'], drn, w.inst('tm2lencbhd1')], 'syl3anc', '( %s -> ( %s ` 0 ) e. %s )' % (ph, LST(DR, 'R'), B4))
    z0 = w.s([pkj], 'fveq1d', '( %s -> %s = ( %s ` 0 ) )' % (ph, ZJ('J'), LST(DR, 'R')))
    zb = w.s([z0, hd], 'eqeltrd', '( %s -> %s e. %s )' % (ph, ZJ('J'), B4))
    jlt = w.s([jo, w.inst('elfzolt2')], 'syl', '( %s -> J < %s )' % (ph, NL))
    an = '( %s /\\ u e. N )' % ph
    rn = w.s([], 'simpr', '( %s -> u e. N )' % an)
    if1a = w.s([u['if1']], 'adantr', '( %s -> %s )' % (an, IF1))
    INN = lambda r, z: '( %s e. N /\\ ( C ` %s ) = 1o )' % (NVR(r, z), NVR(r, z))
    RZ = lambda r: 'A. z e. %s %s' % (B4, INN(r, 'z'))
    cg0, new0 = w.wcongr(RZ('r'), {'r': 'u'}, 'r = u', {'r': w.s([], 'id', '( r = u -> r = u )')})
    assert new0 == RZ('u'), new0
    ral2 = w.s([cg0, if1a, rn], 'rspcdva', '( %s -> %s )' % (an, RZ('u')))
    zba = w.s([zb], 'adantr', '( %s -> %s e. %s )' % (an, ZJ('J'), B4))
    cg, new = w.wcongr(INN('u', 'z'), {'z': ZJ('J')}, 'z = %s' % ZJ('J'), {'z': w.s([], 'id', '( z = %s -> z = %s )' % (ZJ('J'), ZJ('J')))})
    assert new == INN('u', ZJ('J')), new
    inz = w.s([cg, ral2, zba], 'rspcdva', '( %s -> %s )' % (an, INN('u', ZJ('J'))))
    nvn = w.s([inz], 'simpld', '( %s -> %s e. N )' % (an, NVR('u', ZJ('J'))))
    nvc = w.s([inz], 'simprd', '( %s -> ( C ` %s ) = 1o )' % (an, NVR('u', ZJ('J'))))
    jlta = w.s([jlt], 'adantr', '( %s -> J < %s )' % (an, NL))
    bic = w.s([nvc, jlta], '2thd', '( %s -> ( ( C ` %s ) = 1o <-> J < %s ) )' % (an, NVR('u', ZJ('J')), NL))
    inn = innf(w, an, NVR('u', ZJ('J')), 'J', nvn, bic)
    genr(w, ph, inn, 'J')
    return w.run()


def tm2lfe1b():
    lab = 'tm2lfe1b'
    ph = '( %s /\\ J = %s )' % (PHF, NL)
    w = W(lab, 'The entry loop, the peek at the end of the list: the head of the '
               'stack is ` bra ` , so the handler clears the loop test.')
    u = prelude(w, ph, lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph, f)))
    je = w.s([], 'simpr', '( %s -> J = %s )' % (ph, NL))
    nlf = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    jfz = w.s([je, nlf], 'eqeltrd', '( %s -> J e. ( 0 ... %s ) )' % (ph, NL))
    pkj = pkat(w, ph, u, 'J', jfz)
    DR = DROP('L', 'J')
    o1 = w.s([je], 'opeq1d', '( %s -> <. J , %s >. = <. %s , %s >. )' % (ph, NL, NL, NL))
    o2 = w.s([o1], 'oveq2d', '( %s -> %s = ( L substr <. %s , %s >. ) )' % (ph, DR, NL, NL))
    s0 = w.s([], 'swrd00', '( L substr <. %s , %s >. ) = (/)' % (NL, NL))
    s0a = w.s([s0], 'a1i', '( %s -> ( L substr <. %s , %s >. ) = (/) )' % (ph, NL, NL))
    dr0 = w.s([o2, s0a], 'eqtrd', '( %s -> %s = (/) )' % (ph, DR))
    e1 = w.s([dr0], 'fveq2d', '( %s -> %s = %s )' % (ph, ENCB(DR), ENCB('(/)')))
    e2 = w.s([e1], 'oveq1d', '( %s -> %s = %s )' % (ph, LST(DR, 'R'), LST('(/)', 'R')))
    e3 = w.s([pkj, e2], 'eqtrd', '( %s -> ( ( P ` J ) ` K ) = %s )' % (ph, LST('(/)', 'R')))
    z0 = w.s([e3], 'fveq1d', '( %s -> %s = ( %s ` 0 ) )' % (ph, ZJ('J'), LST('(/)', 'R')))
    h0 = w.s([u['rr'], w.inst('tm2lencbhd0')], 'syl', '( %s -> ( %s ` 0 ) = 2 )' % (ph, LST('(/)', 'R')))
    z2 = w.s([z0, h0], 'eqtrd', '( %s -> %s = 2 )' % (ph, ZJ('J')))
    nlr = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    nlt = w.s([nlr], 'ltnrd', '( %s -> -. %s < %s )' % (ph, NL, NL))
    jl0 = w.s([je], 'breq1d', '( %s -> ( J < %s <-> %s < %s ) )' % (ph, NL, NL, NL))
    njl = w.s([nlt, jl0], 'mtbird', '( %s -> -. J < %s )' % (ph, NL))
    an = '( %s /\\ u e. N )' % ph
    rn = w.s([], 'simpr', '( %s -> u e. N )' % an)
    if2a = w.s([u['if2']], 'adantr', '( %s -> %s )' % (an, IF2))
    INN = lambda r: '( %s e. N /\\ -. ( C ` %s ) = 1o )' % (NVR(r, '2'), NVR(r, '2'))
    cg0, new0 = w.wcongr(INN('r'), {'r': 'u'}, 'r = u', {'r': w.s([], 'id', '( r = u -> r = u )')})
    assert new0 == INN('u'), new0
    i2 = w.s([cg0, if2a, rn], 'rspcdva', '( %s -> %s )' % (an, INN('u')))
    nvn = w.s([i2], 'simpld', '( %s -> %s e. N )' % (an, NVR('u', '2')))
    nvc = w.s([i2], 'simprd', '( %s -> -. ( C ` %s ) = 1o )' % (an, NVR('u', '2')))
    z2a = w.s([z2], 'adantr', '( %s -> %s = 2 )' % (an, ZJ('J')))
    q1 = w.s([z2a], 'fveq2d', '( %s -> ( inl ` %s ) = ( inl ` 2 ) )' % (an, ZJ('J')))
    q2 = w.s([q1], 'opeq2d', '( %s -> <. u , ( inl ` %s ) >. = <. u , ( inl ` 2 ) >. )' % (an, ZJ('J')))
    q3 = w.s([q2], 'fveq2d', '( %s -> %s = %s )' % (an, NVR('u', ZJ('J')), NVR('u', '2')))
    nvn2 = w.s([q3, nvn], 'eqeltrd', '( %s -> %s e. N )' % (an, NVR('u', ZJ('J'))))
    q4 = w.s([q3], 'fveq2d', '( %s -> ( C ` %s ) = ( C ` %s ) )' % (an, NVR('u', ZJ('J')), NVR('u', '2')))
    q5 = w.s([q4], 'eqeq1d', '( %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (an, NVR('u', ZJ('J')), NVR('u', '2')))
    nvc2 = w.s([nvc, q5], 'mtbird', '( %s -> -. ( C ` %s ) = 1o )' % (an, NVR('u', ZJ('J'))))
    njla = w.s([njl], 'adantr', '( %s -> -. J < %s )' % (an, NL))
    bic = w.s([nvc2, njla], '2falsed', '( %s -> ( ( C ` %s ) = 1o <-> J < %s ) )' % (an, NVR('u', ZJ('J')), NL))
    inn = innf(w, an, NVR('u', ZJ('J')), 'J', nvn2, bic)
    genr(w, ph, inn, 'J')
    return w.run()


def tm2lfe1():
    lab = 'tm2lfe1'
    UH = '( U e. %s /\\ ( M ` U ) = %s )' % (L('T'), PEEKS)
    ph = '( %s /\\ %s /\\ J e. ( 0 ... %s ) )' % (PHF, UH, NL)
    w = W(lab, 'The entry loop, the peek at position ` J ` : from any label carrying '
               '` peekBra ` the machine reaches the test label with the loop test '
               'set exactly when entries remain.  Lean: ` peekBra_runs ` with '
               '` flag_encListB_drop ` , inside ` forEntries_runs ` .')
    u = prelude(w, ph, lambda st, f: w.s([st, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, f)))
    phf = w.s([], 'simp1', '( %s -> %s )' % (ph, PHF))
    uh = w.s([], 'simp2', '( %s -> %s )' % (ph, UH))
    ul = w.s([uh], 'simpld', '( %s -> U e. %s )' % (ph, L('T')))
    mu = w.s([uh], 'simprd', '( %s -> ( M ` U ) = %s )' % (ph, PEEKS))
    jfz = w.s([], 'simp3', '( %s -> J e. ( 0 ... %s ) )' % (ph, NL))
    # the interface fact by cases on J = NL
    c1 = '( %s /\\ J = %s )' % (ph, NL)
    phf1 = w.s([phf], 'adantr', '( %s -> %s )' % (c1, PHF))
    je1 = w.s([], 'simpr', '( %s -> J = %s )' % (c1, NL))
    r1 = w.s([phf1, je1, w.inst('tm2lfe1b')], 'syl2anc', '( %s -> %s )' % (c1, RAL('J')))
    r1e = w.s([r1], 'ex', '( %s -> ( J = %s -> %s ) )' % (ph, NL, RAL('J')))
    c2 = '( %s /\\ J =/= %s )' % (ph, NL)
    phf2 = w.s([phf], 'adantr', '( %s -> %s )' % (c2, PHF))
    jne = w.s([], 'simpr', '( %s -> J =/= %s )' % (c2, NL))
    jfz2 = w.s([jfz], 'adantr', '( %s -> J e. ( 0 ... %s ) )' % (c2, NL))
    jo = w.s([jne, jfz2, w.inst('fzofzim')], 'syl2anc', '( %s -> J e. ( 0 ..^ %s ) )' % (c2, NL))
    r2 = w.s([phf2, jo, w.inst('tm2lfe1a')], 'syl2anc', '( %s -> %s )' % (c2, RAL('J')))
    r2e = w.s([r2], 'ex', '( %s -> ( J =/= %s -> %s ) )' % (ph, NL, RAL('J')))
    ral = w.s([r1e, r2e], 'pm2.61dne', '( %s -> %s )' % (ph, RAL('J')))
    # the head letter and the tail
    D = DJ('J'); DK = '( %s ` K )' % D
    dd = w.s([u['pty'], jfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, D, STK('T')))
    dkw = stkfvg(w, ph, D, 'K', u['tv'], dd, u['kd'], u['ge'])
    pkj = pkat(w, ph, u, 'J', jfz)
    DR = DROP('L', 'J')
    dr = w.s([u['ll'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DR, WWB))
    ev = w.s([dr, w.inst('tm2lencbval')], 'syl', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (ph, ENCB(DR), ENT(DR)))
    et = w.s([dr, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT(DR), WG))
    en0 = w.s([et, w.inst('ccatws1n0')], 'syl', '( %s -> ( %s ++ <" 2 "> ) =/= (/) )' % (ph, ENT(DR)))
    en = w.s([ev, en0], 'eqnetrd', '( %s -> %s =/= (/) )' % (ph, ENCB(DR)))
    ec = w.s([dr, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(DR), WG))
    ln0 = w.s([ec, en, u['rr'], w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, LST(DR, 'R')))
    dkn = w.s([pkj, ln0], 'eqnetrd', '( %s -> %s =/= (/) )' % (ph, DK))
    hdtl = w.s([dkw, dkn, w.inst('wrdhdtl')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, DK, ZJ('J'), XJ('J')))
    dkv = w.s([dkw], 'elexd', '( %s -> %s e. _V )' % (ph, DK))
    h0 = w.s([dkv, w.inst('hashneq0')], 'syl', '( %s -> ( 0 < ( # ` %s ) <-> %s =/= (/) ) )' % (ph, DK, DK))
    hp = w.s([h0, dkn], 'mpbird', '( %s -> 0 < ( # ` %s ) )' % (ph, DK))
    ln = w.s([dkw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, DK))
    lnn = w.s([ln, hp, w.inst('elnnnn0b')], 'sylanbrc', '( %s -> ( # ` %s ) e. NN )' % (ph, DK))
    z0 = w.s([lnn, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` %s ) ) )' % (ph, DK))
    zg = w.s([dkw, z0, w.inst('wrdsymbcl')], 'syl2anc', "( %s -> %s e. Gamma' )" % (ph, ZJ('J')))
    xg = w.s([dkw, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, XJ('J'), WG))
    nfs, _ = nfss(w, ph, 'J', u['nss'])
    # tm2lpk's antecedent
    a1 = w.s([u['phm'], u['geq']], 'jca', '( %s -> %s )' % (ph, PHM6))
    a2 = w.s([a1, mu], 'jca', '( %s -> ( %s /\\ ( M ` U ) = %s ) )' % (ph, PHM6, PEEKS))
    b1 = w.s([ul, u['al'], u['kk']], '3jca', '( %s -> ( U e. %s /\\ A e. %s /\\ K e. %s ) )' % (ph, L('T'), L('T'), FZ8))
    b2 = w.s([u['ff'], dd], 'jca', '( %s -> ( %s /\\ %s e. %s ) )' % (ph, FTY, D, STK('T')))
    b3 = w.s([b1, b2], 'jca', '( %s -> ( ( U e. %s /\\ A e. %s /\\ K e. %s ) /\\ ( %s /\\ %s e. %s ) ) )' % (ph, L('T'), L('T'), FZ8, FTY, D, STK('T')))
    HDK = '( %s = ( <" %s "> ++ %s ) /\\ %s e. Gamma\' /\\ %s e. %s )' % (DK, ZJ('J'), XJ('J'), ZJ('J'), XJ('J'), WG)
    c3 = w.s([hdtl, zg, xg], '3jca', '( %s -> %s )' % (ph, HDK))
    nn = w.s([u['nss'], nfs], 'jca', '( %s -> ( N C_ %s /\\ %s C_ %s ) )' % (ph, S('T'), NF('J'), S('T')))
    c4 = w.s([c3, nn, ral], '3jca', '( %s -> ( %s /\\ ( N C_ %s /\\ %s C_ %s ) /\\ %s ) )' % (ph, HDK, S('T'), NF('J'), S('T'), RAL('J')))
    ant = w.s([a2, b3, c4], '3jca', '( %s -> ( ( %s /\\ ( M ` U ) = %s ) /\\ ( ( U e. %s /\\ A e. %s /\\ K e. %s ) /\\ ( %s /\\ %s e. %s ) ) /\\ ( %s /\\ ( N C_ %s /\\ %s C_ %s ) /\\ %s ) ) )'
              % (ph, PHM6, PEEKS, L('T'), L('T'), FZ8, FTY, D, STK('T'), HDK, S('T'), NF('J'), S('T'), RAL('J')))
    w.qed([ant, w.inst('tm2lpk')], 'syl', '( %s -> %s )' % (ph, HR(CL('U', 'N', D), 'T', 'M', CL('A', NF('J'), D), '1')))
    return w.run()


def tm2lfe2():
    lab = 'tm2lfe2'
    ph = '( %s /\\ J e. ( 0 ..^ %s ) )' % (PHF, NL)
    w = W(lab, 'One iteration of the entry loop: the test succeeds, the body consumes '
               'the ` J ` -th entry, the peek after it resets the test.  Lean: the '
               'body argument of ` Frag.loop_runs ` inside ` forEntries_runs ` .')
    u = prelude(w, ph, lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph, f)))
    phf = w.s([], 'simpl', '( %s -> %s )' % (ph, PHF))
    jo = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ %s ) )' % (ph, NL))
    jfz = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... %s ) )' % (ph, NL))
    jfz1 = w.s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... %s ) )' % (ph, NL))
    jlt = w.s([jo, w.inst('elfzolt2')], 'syl', '( %s -> J < %s )' % (ph, NL))
    D = DJ('J'); D1 = DJ('( J + 1 )')
    dd = w.s([u['pty'], jfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, D, STK('T')))
    nfs, nfn = nfss(w, ph, 'J', u['nss'])
    # step 1: the test, true on NF(J)
    an = '( %s /\\ m e. %s )' % (ph, NF('J'))
    mn = w.s([], 'simpr', '( %s -> m e. %s )' % (an, NF('J')))
    bic = outnf(w, an, 'm', 'J', mn)
    jlta = w.s([jlt], 'adantr', '( %s -> J < %s )' % (an, NL))
    cm = w.s([bic, jlta], 'mpbird', '( %s -> ( C ` m ) = 1o )' % an)
    he = w.s([cm], 'ralrimiva', '( %s -> A. m e. %s ( C ` m ) = 1o )' % (ph, NF('J')))
    _, gq = gotost(w, ph, 'E', u['tv'], u['el'])
    t1a = w.s([u['phm'], u['ma']], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, TESTS))
    t1b = w.s([u['al'], u['a1l'], dd], '3jca', "( %s -> ( A e. %s /\\ A' e. %s /\\ %s e. %s ) )" % (ph, L('T'), L('T'), D, STK('T')))
    t1c1 = w.s([u['cc'], gq], 'jca', '( %s -> ( %s /\\ %s e. %s ) )' % (ph, CTY, GOTOL('E'), STMT_T))
    t1c2 = w.s([nfs, he], 'jca', '( %s -> ( %s C_ %s /\\ A. m e. %s ( C ` m ) = 1o ) )' % (ph, NF('J'), S('T'), NF('J')))
    t1c = w.s([t1c1, t1c2], 'jca', '( %s -> ( ( %s /\\ %s e. %s ) /\\ ( %s C_ %s /\\ A. m e. %s ( C ` m ) = 1o ) ) )' % (ph, CTY, GOTOL('E'), STMT_T, NF('J'), S('T'), NF('J')))
    t1 = w.s([t1a, t1b, t1c], '3jca', "( %s -> ( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ A' e. %s /\\ %s e. %s ) /\\ ( ( %s /\\ %s e. %s ) /\\ ( %s C_ %s /\\ A. m e. %s ( C ` m ) = 1o ) ) ) )"
             % (ph, PHM, TESTS, L('T'), L('T'), D, STK('T'), CTY, GOTOL('E'), STMT_T, NF('J'), S('T'), NF('J')))
    C0 = CL('A', NF('J'), D); C1 = CL("A'", NF('J'), D)
    s1 = w.s([t1, w.inst('tm2lbrt')], 'syl', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C1, '1')))
    # step 2: the body from C( A' , N , D ), shrunk to NF(J)
    cg, new = w.wcongr(HBF('j'), {'j': 'J'}, 'j = J', {'j': w.s([], 'id', '( j = J -> j = J )')})
    assert new == HBF('J'), new
    s2 = w.s([cg, u['hb'], jo], 'rspcdva', '( %s -> %s )' % (ph, HBF('J')))
    C1N = CL("A'", 'N', D); C2 = CL('A"', 'N', D1)
    ssa = w.s([], 'ssid', "{ ( inl ` A' ) } C_ { ( inl ` A' ) }")
    ssaa = w.s([ssa], 'a1i', "( %s -> { ( inl ` A' ) } C_ { ( inl ` A' ) } )" % ph)
    ssd = w.s([], 'ssid', '{ %s } C_ { %s }' % (D, D))
    ssda = w.s([ssd], 'a1i', '( %s -> { %s } C_ { %s } )' % (ph, D, D))
    x1 = w.s([nfn, ssda, w.inst('xpss12')], 'syl2anc', '( %s -> ( %s X. { %s } ) C_ ( N X. { %s } ) )' % (ph, NF('J'), D, D))
    x2 = w.s([ssaa, x1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ph, C1, C1N))
    s2b = hssc(w, ph, u['phm'], C1N, C2, 'Y', C1, s2, x2)
    # step 3: the peek after the body
    a2h = w.s([u['a2l'], u['ma2']], 'jca', '( %s -> ( A" e. %s /\\ ( M ` A" ) = %s ) )' % (ph, L('T'), PEEKS))
    s3 = w.s([phf, a2h, jfz1, w.inst('tm2lfe1')], 'syl3anc', '( %s -> %s )' % (ph, HR(C2, 'T', 'M', CL('A', NF('( J + 1 )'), D1), '1')))
    C3 = CL('A', NF('( J + 1 )'), D1)
    q1 = hseq(w, ph, u['phm'], C0, C1, C2, '1', 'Y', s1, s2b)
    q2 = hseq(w, ph, u['phm'], C0, C2, C3, '( 1 + Y )', '1', q1, s3)
    # ( ( 1 + Y ) + 1 ) = ( Y + 2 )
    yc = w.s([u['yy']], 'nn0cnd', '( %s -> Y e. CC )' % ph)
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % ph)
    e1 = w.s([onea, yc], 'addcomd', '( %s -> ( 1 + Y ) = ( Y + 1 ) )' % ph)
    e2 = w.s([e1], 'oveq1d', '( %s -> ( ( 1 + Y ) + 1 ) = ( ( Y + 1 ) + 1 ) )' % ph)
    e3 = w.s([yc, onea, onea], 'addassd', '( %s -> ( ( Y + 1 ) + 1 ) = ( Y + ( 1 + 1 ) ) )' % ph)
    e4 = w.s([], '1p1e2', '( 1 + 1 ) = 2')
    e5 = w.s([e4], 'oveq2i', '( Y + ( 1 + 1 ) ) = ( Y + 2 )')
    e5a = w.s([e5], 'a1i', '( %s -> ( Y + ( 1 + 1 ) ) = ( Y + 2 ) )' % ph)
    e6 = w.s([e2, e3], 'eqtrd', '( %s -> ( ( 1 + Y ) + 1 ) = ( Y + ( 1 + 1 ) ) )' % ph)
    e7 = w.s([e6, e5a], 'eqtrd', '( %s -> ( ( 1 + Y ) + 1 ) = ( Y + 2 ) )' % ph)
    o = w.s([e7], 'opeq2d', '( %s -> <. %s , ( ( 1 + Y ) + 1 ) >. = <. %s , ( Y + 2 ) >. )' % (ph, C3, C3))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C3, '( ( 1 + Y ) + 1 )'), HR(C0, 'T', 'M', C3, '( Y + 2 )')))
    w.qed([b, q2], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C3, '( Y + 2 )')))
    return w.run()


IF = '( k e. NN0 |-> %s )' % CL('A', NF('k'), DJ('k'))


def ifval(w, ph, X, xnn0, nss, dcl):
    """( ph -> ( IF ` X ) = CL( A , NF(X) , ( P ` X ) ) )"""
    aq = '( %s /\\ k = %s )' % (ph, X)
    lj = w.s([], 'simpr', '( %s -> k = %s )' % (aq, X))
    st, res = w.congr(CL('A', NF('k'), DJ('k')), {'k': X}, aq, {'k': lj})
    assert res == CL('A', NF(X), DJ(X)), res
    eqi = w.s([], 'eqid', '%s = %s' % (IF, IF))
    sv = w.s([], 'fvex', '%s e. _V' % S('T'))
    sva = w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    nv = w.s([nss, sva, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ph)
    nfa = w.s([], 'ssrab2', '%s C_ N' % NF(X))
    nfaa = w.s([nfa], 'a1i', '( %s -> %s C_ N )' % (ph, NF(X)))
    nfv = w.s([nfaa, nv, w.inst('ssexg')], 'syl2anc', '( %s -> %s e. _V )' % (ph, NF(X)))
    dv = w.s([dcl], 'elexd', '( %s -> %s e. _V )' % (ph, DJ(X)))
    sdv = w.s([dv, w.inst('snexg')], 'syl', '( %s -> { %s } e. _V )' % (ph, DJ(X)))
    xv = w.s([nfv, sdv, w.inst('xpexg')], 'syl2anc', '( %s -> ( %s X. { %s } ) e. _V )' % (ph, NF(X), DJ(X)))
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    aa = w.s([a], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ph)
    cv = w.s([aa, xv, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ph, CL('A', NF(X), DJ(X))))
    return w.s([eqi, st, xnn0, cv], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ph, IF, X, CL('A', NF(X), DJ(X))))


def tm2lfe3():
    lab = 'tm2lfe3'
    ph = PHF
    w = W(lab, 'The entry loop iterated over all entries, by ~ tm2hitr on the family '
               'of test-label configurations.  Lean: ` Frag.loop_runs ` inside '
               '` forEntries_runs ` .')
    u = prelude(w, ph, lambda st, f: st)
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, NL)
    io = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NL))
    def Ai(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pi, f))
    ptya = Ai(u['pty'], PTY); nssa = Ai(u['nss'], 'N C_ %s' % S('T'))
    inn0 = w.s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    i1n0 = w.s([inn0, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    ifz = w.s([io, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (pi, NL))
    i1fz = w.s([io, w.inst('fzofzp1')], 'syl', '( %s -> ( i + 1 ) e. ( 0 ... %s ) )' % (pi, NL))
    di = w.s([ptya, ifz], 'ffvelcdmd', '( %s -> %s e. %s )' % (pi, DJ('i'), STK('T')))
    di1 = w.s([ptya, i1fz], 'ffvelcdmd', '( %s -> %s e. %s )' % (pi, DJ('( i + 1 )'), STK('T')))
    jvi = ifval(w, pi, 'i', inn0, nssa, di)
    jvi1 = ifval(w, pi, '( i + 1 )', i1n0, nssa, di1)
    tri = w.s([w.s([], 'simpl', '( %s -> %s )' % (pi, PHF)), io, w.inst('tm2lfe2')], 'syl2anc',
              '( %s -> %s )' % (pi, HR(CL('A', NF('i'), DJ('i')), 'T', 'M', CL('A', NF('( i + 1 )'), DJ('( i + 1 )')), '( Y + 2 )')))
    Ci = CL('A', NF('i'), DJ('i')); Ci1 = CL('A', NF('( i + 1 )'), DJ('( i + 1 )'))
    jvi1r = w.s([jvi1], 'eqcomd', '( %s -> %s = ( %s ` ( i + 1 ) ) )' % (pi, Ci1, IF))
    jvir = w.s([jvi], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (pi, Ci, IF))
    t2 = hrtransport(w, pi, tri, Ci, Ci1, '( Y + 2 )', '( %s ` i )' % IF, '( %s ` ( i + 1 ) )' % IF, eqc=jvir, eqd=jvi1r)
    HYP = 'A. i e. ( 0 ..^ %s ) %s' % (NL, HR('( %s ` i )' % IF, 'T', 'M', '( %s ` ( i + 1 ) )' % IF, '( Y + 2 )'))
    hyp = w.s([t2], 'ralrimiva', '( %s -> %s )' % (ph, HYP))
    # ( IF ` 0 ) C_ Cfg
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    z0fz = w.s([u['nl'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NL))
    d0 = w.s([u['pty'], z0fz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, DJ('0'), STK('T')))
    jv0 = ifval(w, ph, '0', z0a, u['nss'], d0)
    nf0s, _ = nfss(w, ph, '0', u['nss'])
    ss0 = cfgcl(w, ph, 'A', NF('0'), DJ('0'), u['tv'], u['al'], nf0s, d0)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IF, CFG('T')))
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    y2 = w.s([u['yy'], twoa], 'nn0addcld', '( %s -> ( Y + 2 ) e. NN0 )' % ph)
    pj = w.s([ss0j, y2], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ ( Y + 2 ) e. NN0 ) )' % (ph, IF, CFG('T')))
    ant = w.s([u['phm'], pj, hyp], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ ( Y + 2 ) e. NN0 ) /\\ %s ) )' % (ph, PHM, IF, CFG('T'), HYP))
    itr0 = w.s([u['nl'], w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ ( Y + 2 ) e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IF, CFG('T'), HYP, HR('( %s ` 0 )' % IF, 'T', 'M', '( %s ` %s )' % (IF, NL), '( %s x. ( Y + 2 ) )' % NL)))
    itr = w.s([ant, itr0], 'mpd', '( %s -> %s )' % (ph, HR('( %s ` 0 )' % IF, 'T', 'M', '( %s ` %s )' % (IF, NL), '( %s x. ( Y + 2 ) )' % NL)))
    nlfz = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    dn = w.s([u['pty'], nlfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, DJ(NL), STK('T')))
    jvn = ifval(w, ph, NL, u['nl'], u['nss'], dn)
    fin = hrtransport(w, ph, itr, '( %s ` 0 )' % IF, '( %s ` %s )' % (IF, NL), '( %s x. ( Y + 2 ) )' % NL,
                      CL('A', NF('0'), DJ('0')), CL('A', NF(NL), DJ(NL)), eqc=jv0, eqd=jvn)
    w.qed([fin], 'id' if False else 'a1i_placeholder', '')
    w.lines.pop()
    # fin already proves the goal; restate as qed
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    return w.run()


def tm2lfe():
    lab = 'tm2lfe'
    ph = PHF
    w = W(lab, 'The entry loop ` forEntries ` of TM/Lists.lean: from the entry peek, '
               'through the loop, to the exit with the loop test cleared and the list '
               'reduced to its ` bra ` .  Lean: ` forEntries_runs ` , with the invariant '
               '` ForInv ` carried by the family of ~ tm2lfe3 (blueprint decisions 4, 5).')
    u = prelude(w, ph, lambda st, f: st)
    # entry peek
    p1h = w.s([u['p1l'], u['mp1']], 'jca', '( %s -> ( P1 e. %s /\\ ( M ` P1 ) = %s ) )' % (ph, L('T'), PEEKS))
    z0fz = w.s([u['nl'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NL))
    idp = w.s([], 'id', '( %s -> %s )' % (ph, PHF))
    C0 = CL('P1', 'N', DJ('0')); C1 = CL('A', NF('0'), DJ('0'))
    e1 = w.s([idp, p1h, z0fz, w.inst('tm2lfe1')], 'syl3anc', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C1, '1')))
    C2 = CL('A', NF(NL), DJ(NL))
    e2 = w.s([], 'tm2lfe3', '( %s -> %s )' % (ph, HR(C1, 'T', 'M', C2, '( %s x. ( Y + 2 ) )' % NL)))
    # exit: the test fails on NF( NL )
    nlfz = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    dn = w.s([u['pty'], nlfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, DJ(NL), STK('T')))
    nlr = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    nlt = w.s([nlr], 'ltnrd', '( %s -> -. %s < %s )' % (ph, NL, NL))
    an = '( %s /\\ m e. %s )' % (ph, NF(NL))
    mn = w.s([], 'simpr', '( %s -> m e. %s )' % (an, NF(NL)))
    bic = outnf(w, an, 'm', NL, mn)
    nlta = w.s([nlt], 'adantr', '( %s -> -. %s < %s )' % (an, NL, NL))
    cm = w.s([nlta, bic], 'mtbird', '( %s -> -. ( C ` m ) = 1o )' % an)
    he = w.s([cm], 'ralrimiva', '( %s -> A. m e. %s -. ( C ` m ) = 1o )' % (ph, NF(NL)))
    nfs, nfn = nfss(w, ph, NL, u['nss'])
    _, gq = gotost(w, ph, "A'", u['tv'], u['a1l'])
    t1a = w.s([u['phm'], u['ma']], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, TESTS))
    t1b = w.s([u['al'], u['el'], dn], '3jca', '( %s -> ( A e. %s /\\ E e. %s /\\ %s e. %s ) )' % (ph, L('T'), L('T'), DJ(NL), STK('T')))
    t1c1 = w.s([u['cc'], gq], 'jca', '( %s -> ( %s /\\ %s e. %s ) )' % (ph, CTY, GOTOL("A'"), STMT_T))
    t1c2 = w.s([nfs, he], 'jca', '( %s -> ( %s C_ %s /\\ A. m e. %s -. ( C ` m ) = 1o ) )' % (ph, NF(NL), S('T'), NF(NL)))
    t1c = w.s([t1c1, t1c2], 'jca', '( %s -> ( ( %s /\\ %s e. %s ) /\\ ( %s C_ %s /\\ A. m e. %s -. ( C ` m ) = 1o ) ) )' % (ph, CTY, GOTOL("A'"), STMT_T, NF(NL), S('T'), NF(NL)))
    t1 = w.s([t1a, t1b, t1c], '3jca', '( %s -> ( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ %s e. %s ) /\\ ( ( %s /\\ %s e. %s ) /\\ ( %s C_ %s /\\ A. m e. %s -. ( C ` m ) = 1o ) ) ) )'
             % (ph, PHM, TESTS, L('T'), L('T'), DJ(NL), STK('T'), CTY, GOTOL("A'"), STMT_T, NF(NL), S('T'), NF(NL)))
    C3 = CL('E', NF(NL), DJ(NL))
    e3 = w.s([t1, w.inst('tm2fbrg')], 'syl', '( %s -> %s )' % (ph, HR(C2, 'T', 'M', C3, '1')))
    # grow the exit class to NFIN
    C4 = CL('E', NFIN, DJ(NL))
    aq = '( %s /\\ q e. N )' % ph
    aqb = '( %s /\\ ( ( C ` q ) = 1o <-> %s < %s ) )' % (aq, NL, NL)
    bq = w.s([], 'simpr', '( %s -> ( ( C ` q ) = 1o <-> %s < %s ) )' % (aqb, NL, NL))
    nltb = w.s([nlt], 'ad2antrr', '( %s -> -. %s < %s )' % (aqb, NL, NL))
    cq = w.s([nltb, bq], 'mtbird', '( %s -> -. ( C ` q ) = 1o )' % aqb)
    cqe = w.s([cq], 'ex', '( %s -> ( ( ( C ` q ) = 1o <-> %s < %s ) -> -. ( C ` q ) = 1o ) )' % (aq, NL, NL))
    rss = w.s([cqe], 'ss2rabdv', '( %s -> %s C_ %s )' % (ph, NF(NL), NFIN))
    ssd = w.s([], 'ssid', '{ %s } C_ { %s }' % (DJ(NL), DJ(NL)))
    ssda = w.s([ssd], 'a1i', '( %s -> { %s } C_ { %s } )' % (ph, DJ(NL), DJ(NL)))
    x1 = w.s([rss, ssda, w.inst('xpss12')], 'syl2anc', '( %s -> ( %s X. { %s } ) C_ ( %s X. { %s } ) )' % (ph, NF(NL), DJ(NL), NFIN, DJ(NL)))
    sse = w.s([], 'ssid', '{ ( inl ` E ) } C_ { ( inl ` E ) }')
    ssea = w.s([sse], 'a1i', '( %s -> { ( inl ` E ) } C_ { ( inl ` E ) } )' % ph)
    x2 = w.s([ssea, x1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ph, C3, C4))
    nfin0 = w.s([], 'ssrab2', '%s C_ N' % NFIN)
    nfin0a = w.s([nfin0], 'a1i', '( %s -> %s C_ N )' % (ph, NFIN))
    nfins = w.s([nfin0a, u['nss']], 'sstrd', '( %s -> %s C_ %s )' % (ph, NFIN, S('T')))
    c4cfg = cfgcl(w, ph, 'E', NFIN, DJ(NL), u['tv'], u['el'], nfins, dn)
    e3b = hssd(w, ph, u['phm'], C2, C3, '1', C4, e3, x2, c4cfg)
    q1 = hseq(w, ph, u['phm'], C0, C1, C2, '1', '( %s x. ( Y + 2 ) )' % NL, e1, e2)
    q2 = hseq(w, ph, u['phm'], C0, C2, C4, '( 1 + ( %s x. ( Y + 2 ) ) )' % NL, '1', q1, e3b)
    # ( ( 1 + X ) + 1 ) = ( X + 2 )
    X = '( %s x. ( Y + 2 ) )' % NL
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    y2 = w.s([u['yy'], twoa], 'nn0addcld', '( %s -> ( Y + 2 ) e. NN0 )' % ph)
    xn = w.s([u['nl'], y2], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, X))
    xc = w.s([xn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, X))
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % ph)
    f1 = w.s([onea, xc], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (ph, X, X))
    f2 = w.s([f1], 'oveq1d', '( %s -> ( ( 1 + %s ) + 1 ) = ( ( %s + 1 ) + 1 ) )' % (ph, X, X))
    f3 = w.s([xc, onea, onea], 'addassd', '( %s -> ( ( %s + 1 ) + 1 ) = ( %s + ( 1 + 1 ) ) )' % (ph, X, X))
    f4 = w.s([], '1p1e2', '( 1 + 1 ) = 2')
    f5 = w.s([f4], 'oveq2i', '( %s + ( 1 + 1 ) ) = ( %s + 2 )' % (X, X))
    f5a = w.s([f5], 'a1i', '( %s -> ( %s + ( 1 + 1 ) ) = ( %s + 2 ) )' % (ph, X, X))
    f6 = w.s([f2, f3], 'eqtrd', '( %s -> ( ( 1 + %s ) + 1 ) = ( %s + ( 1 + 1 ) ) )' % (ph, X, X))
    f7 = w.s([f6, f5a], 'eqtrd', '( %s -> ( ( 1 + %s ) + 1 ) = ( %s + 2 ) )' % (ph, X, X))
    o = w.s([f7], 'opeq2d', '( %s -> <. %s , ( ( 1 + %s ) + 1 ) >. = <. %s , ( %s + 2 ) >. )' % (ph, C4, X, C4, X))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C4, '( ( 1 + %s ) + 1 )' % X), HR(C0, 'T', 'M', C4, '( %s + 2 )' % X)))
    w.qed([b, q2], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C4, '( %s + 2 )' % X)))
    return w.run()


if __name__ == '__main__':
    for f in [tm2lfe1a, tm2lfe1b, tm2lfe1, tm2lfe2, tm2lfe3, tm2lfe]:
        if want(f.__name__): f()
