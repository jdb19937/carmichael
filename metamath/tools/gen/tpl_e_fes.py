"""T-PL: the list-layer primitives PrimList.lean adds: ~ tm2fpshf (a push of a
state-dependent letter, Lean ` pushBit_runs `) and the Sigma-cost entry loop
~ tm2lfes (Lean ` forEntries_runs' `): T6's ~ tm2lfe1a - ~ tm2lfe rebuilt with
the per-entry bound family ` ( Y ` j ) ` , the peek lemmas at the Y-free
antecedent ` PHP ` (blueprint section 1, D4)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *
from t6lib import gamk, wgk, lgk, stkfvg, gotost, hseq, hle, hssc, hssd, hrtransport, cleq
from t6lib import cfgcl as cfgcl6, updcl as updcl6
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GEQ = '( 1st ` ( 1st ` T ) ) = TMGam'
T_PHM6 = (PHM, GEQ)
TREE_PHP_ = ((T_PHM6, T_PROG_FE), (T_LABS_FE, T_TYPS_FE, T_IFS_FE), (T_LR, T_PP))
TREE_FES_ = ((T_PHM6, T_PROG_FE), (T_LABS_FE, T_TYPS_FE, T_IFS_FE), (T_LR, T_PP, HBS))
assert cj(TREE_PHP_) == PHP and cj(TREE_FES_) == PHFS
PEEKS, TESTS = fe.PEEKS, fe.TESTS
FTY, CTYS = fe.FTY, fe.CTY
IF1, IF2 = fe.IF1, fe.IF2
PTYS, PK, PKF = fe.PTY, fe.PK, fe.PKF
NFJ = fe.NF
DJ = PF
ZJ = lambda j: '( ( %s ` K ) ` 0 )' % DJ(j)
XJ = lambda j: '( ( %s ` K ) substr <. 1 , ( # ` ( %s ` K ) ) >. )' % (DJ(j), DJ(j))
NVR = lambda r, z: NV('F', r, z)
RAL = fe.RAL
RALU = fe.RALU


# ------------------------------------------------------------- the push of a state-dependent letter

def tm2fpshf():
    lab = 'tm2fpshf'
    tree, ph = TREE_PSHF, cj(TREE_PSHF)
    STM = STM_PSHF
    D2 = UP('D', 'K', CC(S1('Z'), '( D ` K )'))
    w = W(lab, 'The step ` push K P ( goto E ) ` whose letter function ` P ` is constant ` Z ` on the state class '
               '` N ` : the letter ` Z ` is pushed on stack ` K ` and the state is untouched.  ~ tm2fpshn is the '
               'instance at a constant function; this form carries Lean\'s ` pushBit_runs ` (PrimList.lean), the '
               'push of ` cmp =/= lt ` as a bit after the coprimality loop.')
    c = Ctx(w, ph, tree)
    phm, meq = c[PHM], c[MEQ('A', STM)]
    al, el, kk, zz = c[LAB('A')], c[LAB('E')], c['K e. %s' % DG], c['Z e. %s' % GK]
    pty, ral, dd, nss = c[PTY('P', 'K')], c['A. r e. N ( P ` r ) = Z'], c[STKD('D')], c[SSS('N')]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe_ = constfty(w, ph, 'E', LL, el)
    ge = w.s([tv, fe_, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GT('E'), STMT_T))
    dkw = stkfv(w, ph, 'D', 'K', tv, dd, kk)
    zdw = ccatw(w, ph, s1w(w, ph, zz, 'Z', GK), dkw, S1('Z'), '( D ` K )', GK)
    d2cl = updcl(w, ph, 'D', 'K', CC(S1('Z'), '( D ` K )'), tv, dd, kk, zdw)

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, STKD('D'))
        gea = A_(ge, STMT(GT('E'))); kka = A_(kk, 'K e. %s' % DG)
        fea = A_(fe_, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), LL, SS))
        pa = A_(pty, PTY('P', 'K'))
        nssa = A_(nss, SSS('N')); ela = A_(el, LAB('E')); d2a = A_(d2cl, STKD(D2))
        rala = A_(ral, 'A. r e. N ( P ` r ) = Z')
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, SS))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, vv, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` v ) = E )' % (av, CONSTF('T', 'E')))
        g1 = w.s([], 'fveq2', '( r = v -> ( P ` r ) = ( P ` v ) )')
        g2 = w.s([g1], 'eqeq1d', '( r = v -> ( ( P ` r ) = Z <-> ( P ` v ) = Z ) )')
        rgz = w.s([g2, rala, vn], 'rspcdva', '( %s -> ( P ` v ) = Z )' % av)
        facts = {'T e. V': tva, 'v e. %s' % SS: vv, STKD('D'): dda, STKD(D2): d2a, STMT(GT('E')): gea, 'K e. %s' % DG: kka,
                 PTY('P', 'K'): pa, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), LL, SS): fea}
        rules = {'( %s ` v )' % CONSTF('T', 'E'): ('E', rge), '( P ` v )': ('Z', rgz)}
        ex = Exec(w, av, 'T', facts, rules=rules)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. v , %s >. >.' % D2
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, MEQ('A', STM))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) ( TM2sa ` T ) <. v , D >. ) = ( %s ( TM2sa ` T ) <. v , D >. ) )' % (av, STM))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) ( TM2sa ` T ) <. v , D >. ) = %s )' % (av, res))
        return fin, 'v', vn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', D2, (meq, phm), al, el, nss, nss, dd, d2cl, body, qed=True)
    return w.run()


# ------------------------------------------------------------- the entry loop, Sigma cost

def prel(w, ph, root, sigma):
    """the conjuncts of PHP (sigma=False) or PHFS (True) under ph, root a step ( ph -> PHP/PHFS ) or None"""
    tree = TREE_FES_ if sigma else TREE_PHP_
    c = Ctx(w, ph, tree, root=root)
    u = dict(phm=c[PHM], geq=c[GEQ], mp1=c[MEQ('P1', PEEKS)], ma=c[MEQ('A', TESTS)], ma2=c[MEQ('A"', PEEKS)],
             p1l=c[LAB('P1')], al=c[LAB('A')], a1l=c[LAB("A'")], a2l=c[LAB('A"')], el=c[LAB('E')], kk=c['K e. %s' % FZ8],
             ff=c[FTY], cc=c[CTYS], nss=c['N C_ %s' % SS], if1=c[IF1], if2=c[IF2], ll=c['L e. %s' % WWB], rr=c['R e. %s' % WG],
             pty=c[PTYS], pk=c[PK])
    if sigma:
        u['hb'] = c[HBS]
    u['tv'] = w.s([u['phm'], w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    u['kd'], u['ge'] = gamk(w, ph, 'K', u['geq'], u['kk'])
    u['nl'] = w.s([u['ll'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    return u


def pkat(w, ph, u, J, jfz):
    cg, new = w.wcongr(PKF('j'), {'j': J}, 'j = %s' % J, {'j': w.s([], 'id', '( j = %s -> j = %s )' % (J, J))})
    assert new == PKF(J), new
    return w.s([cg, u['pk'], jfz], 'rspcdva', '( %s -> %s )' % (ph, PKF(J)))


def nfss(w, ph, j, nss):
    a = w.s([], 'ssrab2', '%s C_ N' % NFJ(j))
    aa = w.s([a], 'a1i', '( %s -> %s C_ N )' % (ph, NFJ(j)))
    return w.s([aa, nss], 'sstrd', '( %s -> %s C_ %s )' % (ph, NFJ(j), SS)), aa


def innf(w, ante, X, j, xin, bic):
    c1 = w.s([], 'fveq2', '( q = %s -> ( C ` q ) = ( C ` %s ) )' % (X, X))
    c2 = w.s([c1], 'eqeq1d', '( q = %s -> ( ( C ` q ) = 1o <-> ( C ` %s ) = 1o ) )' % (X, X))
    c3 = w.s([c2], 'bibi1d', '( q = %s -> ( ( ( C ` q ) = 1o <-> %s < %s ) <-> ( ( C ` %s ) = 1o <-> %s < %s ) ) )' % (X, j, NL, X, j, NL))
    return w.s([c3, xin, bic], 'elrabd', '( %s -> %s e. %s )' % (ante, X, NFJ(j)))


def outnf(w, ante, X, j, xin):
    c1 = w.s([], 'fveq2', '( q = %s -> ( C ` q ) = ( C ` %s ) )' % (X, X))
    c2 = w.s([c1], 'eqeq1d', '( q = %s -> ( ( C ` q ) = 1o <-> ( C ` %s ) = 1o ) )' % (X, X))
    c3 = w.s([c2], 'bibi1d', '( q = %s -> ( ( ( C ` q ) = 1o <-> %s < %s ) <-> ( ( C ` %s ) = 1o <-> %s < %s ) ) )' % (X, j, NL, X, j, NL))
    return w.s([c3, xin], 'elrabrd', '( %s -> ( ( C ` %s ) = 1o <-> %s < %s ) )' % (ante, X, j, NL))


def genr(w, ph, inn, j):
    ru = w.s([inn], 'ralrimiva', '( %s -> %s )' % (ph, RALU(j)))
    B = lambda x: '%s e. %s' % (NVR(x, ZJ(j)), NFJ(j))
    cg, new = w.wcongr(B('u'), {'u': 'r'}, 'u = r', {'u': w.s([], 'id', '( u = r -> u = r )')})
    assert new == B('r'), new
    cb = w.s([cg], 'cbvralvw', '( %s <-> %s )' % (RALU(j), RAL(j)))
    cba = w.s([cb], 'a1i', '( %s -> ( %s <-> %s ) )' % (ph, RALU(j), RAL(j)))
    w.qed([cba, ru], 'mpbid', '( %s -> %s )' % (ph, RAL(j)))


def tm2lfes1a():
    lab = 'tm2lfes1a'
    ph = '( %s /\\ J e. ( 0 ..^ %s ) )' % (PHP, NL)
    w = W(lab, 'The entry loop, the peek before the end of the list: the head of the stack is a bit or a comma, '
               'so the handler sets the loop test.  ~ tm2lfe1a at the Y-free antecedent of the Sigma-cost loop.')
    u = prel(w, ph, w.s([], 'simpl', '( %s -> %s )' % (ph, PHP)), False)
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


def tm2lfes1b():
    lab = 'tm2lfes1b'
    ph = '( %s /\\ J = %s )' % (PHP, NL)
    w = W(lab, 'The entry loop, the peek at the end of the list: the head of the stack is ` bra ` , so the handler '
               'clears the loop test.  ~ tm2lfe1b at the Y-free antecedent of the Sigma-cost loop.')
    u = prel(w, ph, w.s([], 'simpl', '( %s -> %s )' % (ph, PHP)), False)
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


def tm2lfes1():
    lab = 'tm2lfes1'
    UH = UH_FES
    ph = '( %s /\\ %s /\\ J e. ( 0 ... %s ) )' % (PHP, UH, NL)
    w = W(lab, 'The entry loop, the peek at position ` J ` : from any label carrying ` peekBra ` the machine reaches '
               'the test label with the loop test set exactly when entries remain.  ~ tm2lfe1 at the Y-free '
               'antecedent of the Sigma-cost loop.')
    php = w.s([], 'simp1', '( %s -> %s )' % (ph, PHP))
    u = prel(w, ph, php, False)
    uh = w.s([], 'simp2', '( %s -> %s )' % (ph, UH))
    ul = w.s([uh], 'simpld', '( %s -> U e. %s )' % (ph, LL))
    mu = w.s([uh], 'simprd', '( %s -> ( M ` U ) = %s )' % (ph, PEEKS))
    jfz = w.s([], 'simp3', '( %s -> J e. ( 0 ... %s ) )' % (ph, NL))
    c1 = '( %s /\\ J = %s )' % (ph, NL)
    php1 = w.s([php], 'adantr', '( %s -> %s )' % (c1, PHP))
    je1 = w.s([], 'simpr', '( %s -> J = %s )' % (c1, NL))
    r1 = w.s([php1, je1, w.inst('tm2lfes1b')], 'syl2anc', '( %s -> %s )' % (c1, RAL('J')))
    r1e = w.s([r1], 'ex', '( %s -> ( J = %s -> %s ) )' % (ph, NL, RAL('J')))
    c2 = '( %s /\\ J =/= %s )' % (ph, NL)
    php2 = w.s([php], 'adantr', '( %s -> %s )' % (c2, PHP))
    jne = w.s([], 'simpr', '( %s -> J =/= %s )' % (c2, NL))
    jfz2 = w.s([jfz], 'adantr', '( %s -> J e. ( 0 ... %s ) )' % (c2, NL))
    jo = w.s([jne, jfz2, w.inst('fzofzim')], 'syl2anc', '( %s -> J e. ( 0 ..^ %s ) )' % (c2, NL))
    r2 = w.s([php2, jo, w.inst('tm2lfes1a')], 'syl2anc', '( %s -> %s )' % (c2, RAL('J')))
    r2e = w.s([r2], 'ex', '( %s -> ( J =/= %s -> %s ) )' % (ph, NL, RAL('J')))
    ral = w.s([r1e, r2e], 'pm2.61dne', '( %s -> %s )' % (ph, RAL('J')))
    D = DJ('J'); DK = '( %s ` K )' % D
    dd = w.s([u['pty'], jfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, D, STK_T))
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
    a1 = w.s([u['phm'], u['geq']], 'jca', '( %s -> %s )' % (ph, PHM6))
    a2 = w.s([a1, mu], 'jca', '( %s -> ( %s /\\ ( M ` U ) = %s ) )' % (ph, PHM6, PEEKS))
    b1 = w.s([ul, u['al'], u['kk']], '3jca', '( %s -> ( U e. %s /\\ A e. %s /\\ K e. %s ) )' % (ph, LL, LL, FZ8))
    b2 = w.s([u['ff'], dd], 'jca', '( %s -> ( %s /\\ %s e. %s ) )' % (ph, FTY, D, STK_T))
    b3 = w.s([b1, b2], 'jca', '( %s -> ( ( U e. %s /\\ A e. %s /\\ K e. %s ) /\\ ( %s /\\ %s e. %s ) ) )' % (ph, LL, LL, FZ8, FTY, D, STK_T))
    HDK = '( %s = ( <" %s "> ++ %s ) /\\ %s e. Gamma\' /\\ %s e. %s )' % (DK, ZJ('J'), XJ('J'), ZJ('J'), XJ('J'), WG)
    c3 = w.s([hdtl, zg, xg], '3jca', '( %s -> %s )' % (ph, HDK))
    nn = w.s([u['nss'], nfs], 'jca', '( %s -> ( N C_ %s /\\ %s C_ %s ) )' % (ph, SS, NFJ('J'), SS))
    c4 = w.s([c3, nn, ral], '3jca', '( %s -> ( %s /\\ ( N C_ %s /\\ %s C_ %s ) /\\ %s ) )' % (ph, HDK, SS, NFJ('J'), SS, RAL('J')))
    ant = w.s([a2, b3, c4], '3jca', '( %s -> ( ( %s /\\ ( M ` U ) = %s ) /\\ ( ( U e. %s /\\ A e. %s /\\ K e. %s ) /\\ ( %s /\\ %s e. %s ) ) /\\ ( %s /\\ ( N C_ %s /\\ %s C_ %s ) /\\ %s ) ) )'
              % (ph, PHM6, PEEKS, LL, LL, FZ8, FTY, D, STK_T, HDK, SS, NFJ('J'), SS, RAL('J')))
    w.qed([ant, w.inst('tm2lpk')], 'syl', '( %s -> %s )' % (ph, HR(CL('U', 'N', D), 'T', 'M', CL('A', NFJ('J'), D), '1')))
    return w.run()


def php_of(w, ph, root=None):
    """( ph -> PHP ) from ( ph -> PHFS ) (root; None when ph == PHFS)"""
    def sp(i, f):
        return w.s([] if root is None else [root, w.inst('simp%d' % i)], 'simp%d' % i if root is None else 'syl', '( %s -> %s )' % (ph, f))
    x1 = sp(1, cj(TREE_FES_[0])); x2 = sp(2, cj(TREE_FES_[1])); x3 = sp(3, cj(TREE_FES_[2]))
    lr = w.s([x3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, cj(T_LR)))
    pp = w.s([x3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, cj(T_PP)))
    lp = w.s([lr, pp], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, cj(T_LR), cj(T_PP)))
    return w.s([x1, x2, lp], '3jca', '( %s -> %s )' % (ph, PHP))


def tm2lfes2():
    lab = 'tm2lfes2'
    ph = '( %s /\\ J e. ( 0 ..^ %s ) )' % (PHFS, NL)
    w = W(lab, 'One iteration of the entry loop with a per-entry cost: the test succeeds, the body consumes the '
               '` J ` -th entry within ` ( Y ` J ) ` steps, the peek after it resets the test.  ~ tm2lfe2 in the '
               'Sigma-cost setting; Lean: the body argument of ` Frag.loop_runs\' ` inside ` forEntries_runs\' ` .')
    phfs = w.s([], 'simpl', '( %s -> %s )' % (ph, PHFS))
    u = prel(w, ph, phfs, True)
    php = php_of(w, ph, phfs)
    jo = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ %s ) )' % (ph, NL))
    jfz = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... %s ) )' % (ph, NL))
    jfz1 = w.s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... %s ) )' % (ph, NL))
    jlt = w.s([jo, w.inst('elfzolt2')], 'syl', '( %s -> J < %s )' % (ph, NL))
    D = DJ('J'); D1 = DJ('( J + 1 )')
    dd = w.s([u['pty'], jfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, D, STK_T))
    nfs, nfn = nfss(w, ph, 'J', u['nss'])
    an = '( %s /\\ m e. %s )' % (ph, NFJ('J'))
    mn = w.s([], 'simpr', '( %s -> m e. %s )' % (an, NFJ('J')))
    bic = outnf(w, an, 'm', 'J', mn)
    jlta = w.s([jlt], 'adantr', '( %s -> J < %s )' % (an, NL))
    cm = w.s([bic, jlta], 'mpbird', '( %s -> ( C ` m ) = 1o )' % an)
    he = w.s([cm], 'ralrimiva', '( %s -> A. m e. %s ( C ` m ) = 1o )' % (ph, NFJ('J')))
    _, gq = gotost(w, ph, 'E', u['tv'], u['el'])
    C0 = CL('A', NFJ('J'), D); C1 = CL("A'", NFJ('J'), D)
    s1 = brstep(w, ph, 'tm2lbrt', u['phm'], u['ma'], u['al'], u['a1l'], dd, u['cc'], gq, nfs, he, 'A', "A'", NFJ('J'), D)
    cg, new = w.wcongr(HBSF('j'), {'j': 'J'}, 'j = J', {'j': w.s([], 'id', '( j = J -> j = J )')})
    assert new == HBSF('J'), new
    hbj = w.s([cg, u['hb'], jo], 'rspcdva', '( %s -> %s )' % (ph, HBSF('J')))
    yn = w.s([hbj], 'simpld', '( %s -> %s e. NN0 )' % (ph, YF('J')))
    C1N = CL("A'", 'N', D); C2 = CL('A"', 'N', D1)
    s2 = w.s([hbj], 'simprd', '( %s -> %s )' % (ph, HR(C1N, 'T', 'M', C2, YF('J'))))
    s2b = hrssc(w, ph, u['phm'], s2, C1N, C2, YF('J'), C1, clnss(w, ph, "A'", NFJ('J'), 'N', D, nfn))
    a2h = w.s([u['a2l'], u['ma2']], 'jca', '( %s -> ( A" e. %s /\\ ( M ` A" ) = %s ) )' % (ph, LL, PEEKS))
    C3 = CL('A', NFJ('( J + 1 )'), D1)
    s3 = w.s([php, a2h, jfz1, w.inst('tm2lfes1')], 'syl3anc', '( %s -> %s )' % (ph, HR(C2, 'T', 'M', C3, '1')))
    q1 = hrseq(w, ph, u['phm'], s1, s2b, C0, C1, C2, '1', YF('J'))
    q2 = hrseq(w, ph, u['phm'], q1, s3, C0, C2, C3, '( 1 + %s )' % YF('J'), '1')
    bound0(w, ph, u['phm'], q2, C0, C3, '( ( 1 + %s ) + 1 )' % YF('J'), '( %s + 2 )' % YF('J'), {YF('J'): yn}, qed=True)
    return w.run()


IFF = '( k e. NN0 |-> %s )' % CL('A', NFJ('k'), DJ('k'))
BODYF = CL('A', NFJ('k'), DJ('k'))
UPY = '( k e. NN0 |-> ( ( Y ` k ) + 2 ) )'


def ifvalf(w, ph, X, xnn0, nss, dcl):
    """( ph -> ( IFF ` X ) = CL( A , NF(X) , ( P ` X ) ) )"""
    aq = '( %s /\\ k = %s )' % (ph, X)
    lj = w.s([], 'simpr', '( %s -> k = %s )' % (aq, X))
    st, res = w.congr(BODYF, {'k': X}, aq, {'k': lj})
    assert res == CL('A', NFJ(X), DJ(X)), res
    eqi = w.s([], 'eqid', '%s = %s' % (IFF, IFF))
    sv = w.s([], 'fvex', '%s e. _V' % SS)
    sva = w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ph, SS))
    nv = w.s([nss, sva, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ph)
    nfa = w.s([], 'ssrab2', '%s C_ N' % NFJ(X))
    nfaa = w.s([nfa], 'a1i', '( %s -> %s C_ N )' % (ph, NFJ(X)))
    nfv = w.s([nfaa, nv, w.inst('ssexg')], 'syl2anc', '( %s -> %s e. _V )' % (ph, NFJ(X)))
    dv = w.s([dcl], 'elexd', '( %s -> %s e. _V )' % (ph, DJ(X)))
    sdv = w.s([dv, w.inst('snexg')], 'syl', '( %s -> { %s } e. _V )' % (ph, DJ(X)))
    xv = w.s([nfv, sdv, w.inst('xpexg')], 'syl2anc', '( %s -> ( %s X. { %s } ) e. _V )' % (ph, NFJ(X), DJ(X)))
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    aa = w.s([a], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ph)
    cv = w.s([aa, xv, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ph, CL('A', NFJ(X), DJ(X))))
    return w.s([eqi, st, xnn0, cv], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ph, IFF, X, CL('A', NFJ(X), DJ(X))))


def tm2lfes3():
    lab = 'tm2lfes3'
    ph = PHFS
    w = W(lab, 'The entry loop iterated over all entries with per-entry costs, by ~ tm2hitsum on the family of '
               'test-label configurations.  ~ tm2lfe3 in the Sigma-cost setting; Lean: ` Frag.loop_runs\' ` inside '
               '` forEntries_runs\' ` .')
    u = prel(w, ph, None, True)
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, NL)
    io = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NL))
    def Ai(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pi, f))
    ptya = Ai(u['pty'], PTYS); nssa = Ai(u['nss'], 'N C_ %s' % SS)
    inn0 = w.s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    i1n0 = w.s([inn0, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    ifz = w.s([io, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... %s ) )' % (pi, NL))
    i1fz = w.s([io, w.inst('fzofzp1')], 'syl', '( %s -> ( i + 1 ) e. ( 0 ... %s ) )' % (pi, NL))
    di = w.s([ptya, ifz], 'ffvelcdmd', '( %s -> %s e. %s )' % (pi, DJ('i'), STK_T))
    di1 = w.s([ptya, i1fz], 'ffvelcdmd', '( %s -> %s e. %s )' % (pi, DJ('( i + 1 )'), STK_T))
    jvi = ifvalf(w, pi, 'i', inn0, nssa, di)
    jvi1 = ifvalf(w, pi, '( i + 1 )', i1n0, nssa, di1)
    YI2 = '( %s + 2 )' % YF('i')
    tri = w.s([w.s([], 'simpl', '( %s -> %s )' % (pi, PHFS)), io, w.inst('tm2lfes2')], 'syl2anc',
              '( %s -> %s )' % (pi, HR(CL('A', NFJ('i'), DJ('i')), 'T', 'M', CL('A', NFJ('( i + 1 )'), DJ('( i + 1 )')), YI2)))
    Ci = CL('A', NFJ('i'), DJ('i')); Ci1 = CL('A', NFJ('( i + 1 )'), DJ('( i + 1 )'))
    jvi1r = w.s([jvi1], 'eqcomd', '( %s -> %s = ( %s ` ( i + 1 ) ) )' % (pi, Ci1, IFF))
    jvir = w.s([jvi], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (pi, Ci, IFF))
    # ( UPY ` i ) = ( ( Y ` i ) + 2 ), and its NN0-ness from HBS at i
    vex = w.s([], 'ovex', '%s e. _V' % YI2); vexa = w.s([vex], 'a1i', '( %s -> %s e. _V )' % (pi, YI2))
    aq = '( %s /\\ k = i )' % pi
    lj = w.s([], 'simpr', '( %s -> k = i )' % aq)
    stc, resc = w.congr('( ( Y ` k ) + 2 )', {'k': 'i'}, aq, {'k': lj})
    assert resc == YI2
    eqi = w.s([], 'eqid', '%s = %s' % (UPY, UPY))
    upi = w.s([eqi, stc, inn0, vexa], 'fvmptd2', '( %s -> ( %s ` i ) = %s )' % (pi, UPY, YI2))
    upir = w.s([upi], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (pi, YI2, UPY))
    t2 = hrtransport(w, pi, tri, Ci, Ci1, YI2, '( %s ` i )' % IFF, '( %s ` ( i + 1 ) )' % IFF, eqc=jvir, eqd=jvi1r)
    o = w.s([upir], 'opeq2d', '( %s -> <. ( %s ` ( i + 1 ) ) , %s >. = <. ( %s ` ( i + 1 ) ) , ( %s ` i ) >. )' % (pi, IFF, YI2, IFF, UPY))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (pi, HR('( %s ` i )' % IFF, 'T', 'M', '( %s ` ( i + 1 ) )' % IFF, YI2),
                                                        HR('( %s ` i )' % IFF, 'T', 'M', '( %s ` ( i + 1 ) )' % IFF, '( %s ` i )' % UPY)))
    t3 = w.s([b, t2], 'mpbid', '( %s -> %s )' % (pi, HR('( %s ` i )' % IFF, 'T', 'M', '( %s ` ( i + 1 ) )' % IFF, '( %s ` i )' % UPY)))
    cg, new = w.wcongr(HBSF('j'), {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    assert new == HBSF('i'), new
    hbi = w.s([cg, Ai(u['hb'], HBS), io], 'rspcdva', '( %s -> %s )' % (pi, HBSF('i')))
    yn = w.s([hbi], 'simpld', '( %s -> %s e. NN0 )' % (pi, YF('i')))
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % pi)
    y2n = w.s([yn, twoa], 'nn0addcld', '( %s -> %s e. NN0 )' % (pi, YI2))
    upn = w.s([upi, y2n], 'eqeltrd', '( %s -> ( %s ` i ) e. NN0 )' % (pi, UPY))
    pair = w.s([upn, t3], 'jca', '( %s -> ( ( %s ` i ) e. NN0 /\\ %s ) )' % (pi, UPY, HR('( %s ` i )' % IFF, 'T', 'M', '( %s ` ( i + 1 ) )' % IFF, '( %s ` i )' % UPY)))
    HYP = 'A. i e. ( 0 ..^ %s ) ( ( %s ` i ) e. NN0 /\\ %s )' % (NL, UPY, HR('( %s ` i )' % IFF, 'T', 'M', '( %s ` ( i + 1 ) )' % IFF, '( %s ` i )' % UPY))
    hyp = w.s([pair], 'ralrimiva', '( %s -> %s )' % (ph, HYP))
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    z0fz = w.s([u['nl'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NL))
    d0 = w.s([u['pty'], z0fz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, DJ('0'), STK_T))
    jv0 = ifvalf(w, ph, '0', z0a, u['nss'], d0)
    nf0s, _ = nfss(w, ph, '0', u['nss'])
    ss0 = cfgcl6(w, ph, 'A', NFJ('0'), DJ('0'), u['tv'], u['al'], nf0s, d0)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFF, CFG_T))
    ant = w.s([u['phm'], ss0j, hyp], '3jca', '( %s -> ( %s /\\ ( %s ` 0 ) C_ %s /\\ %s ) )' % (ph, PHM, IFF, CFG_T, HYP))
    S_I = SUM('i', NL, '( %s ` i )' % UPY)
    RUN = HR('( %s ` 0 )' % IFF, 'T', 'M', '( %s ` %s )' % (IFF, NL), S_I)
    itr0 = w.s([u['nl'], w.inst('tm2hitsum')], 'syl', '( %s -> ( ( %s /\\ ( %s ` 0 ) C_ %s /\\ %s ) -> %s ) )' % (ph, PHM, IFF, CFG_T, HYP, RUN))
    itr = w.s([ant, itr0], 'mpd', '( %s -> %s )' % (ph, RUN))
    nlfz = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    dn = w.s([u['pty'], nlfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, DJ(NL), STK_T))
    jvn = ifvalf(w, ph, NL, u['nl'], u['nss'], dn)
    # the sum: sum_ i ( UPY ` i ) = sum_ i ( ( Y ` i ) + 2 ) = sum_ j ( ( Y ` j ) + 2 )
    f1 = w.s([], 'fveq2', '( k = i -> ( Y ` k ) = ( Y ` i ) )')
    f2 = w.s([f1], 'oveq1d', '( k = i -> ( ( Y ` k ) + 2 ) = ( ( Y ` i ) + 2 ) )')
    vx = w.s([], 'ovex', '%s e. _V' % YI2)
    fv = w.s([f2, eqi, vx], 'fvmpt', '( i e. NN0 -> ( %s ` i ) = %s )' % (UPY, YI2))
    fv2 = w.s([w.inst('elfzonn0'), fv], 'syl', '( i e. ( 0 ..^ %s ) -> ( %s ` i ) = %s )' % (NL, UPY, YI2))
    rg = w.s([fv2], 'rgen', 'A. i e. ( 0 ..^ %s ) ( %s ` i ) = %s' % (NL, UPY, YI2))
    S_I2 = SUM('i', NL, YI2)
    se = w.s([rg, w.inst('sumeq2')], 'ax-mp', '%s = %s' % (S_I, S_I2))
    g1 = w.s([], 'fveq2', '( i = j -> ( Y ` i ) = ( Y ` j ) )')
    g2 = w.s([g1], 'oveq1d', '( i = j -> ( ( Y ` i ) + 2 ) = ( ( Y ` j ) + 2 ) )')
    S_J = SUM('j', NL, '( %s + 2 )' % YF('j'))
    cb = w.s([g2], 'cbvsumv', '%s = %s' % (S_I2, S_J))
    se2 = w.s([se, cb], 'eqtri', '%s = %s' % (S_I, S_J))
    se2a = w.s([se2], 'a1i', '( %s -> %s = %s )' % (ph, S_I, S_J))
    fin = hrtransport(w, ph, itr, '( %s ` 0 )' % IFF, '( %s ` %s )' % (IFF, NL), S_I, CL('A', NFJ('0'), DJ('0')), CL('A', NFJ(NL), DJ(NL)), eqc=jv0, eqd=jvn)
    o2 = w.s([se2a], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, CL('A', NFJ(NL), DJ(NL)), S_I, CL('A', NFJ(NL), DJ(NL)), S_J))
    b2 = w.s([o2], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(CL('A', NFJ('0'), DJ('0')), 'T', 'M', CL('A', NFJ(NL), DJ(NL)), S_I),
                                                          HR(CL('A', NFJ('0'), DJ('0')), 'T', 'M', CL('A', NFJ(NL), DJ(NL)), S_J)))
    w.qed([b2, fin], 'mpbid', ST_FES3)
    return w.run()


def tm2lfes():
    lab = 'tm2lfes'
    ph = PHFS
    w = W(lab, 'The entry loop ` forEntries ` of TM/Lists.lean with a per-entry cost family: from the entry peek, '
               'through the loop, to the exit with the loop test cleared and the list reduced to its ` bra ` , within '
               '` sum_ j e. ( 0 ..^ ( # ` L ) ) ( ( Y ` j ) + 2 ) + 2 ` steps.  ~ tm2lfe is the uniform case.  Lean: '
               '` forEntries_runs\' ` (PrimList.lean; ` forEntriesN_runs\' ` at ` L := ( encNatGam o. l ) `), the rule '
               'of ` divisorsOfF ` whose body costs grow with the entry index.')
    u = prel(w, ph, None, True)
    php = php_of(w, ph, None)
    p1h = w.s([u['p1l'], u['mp1']], 'jca', '( %s -> ( P1 e. %s /\\ ( M ` P1 ) = %s ) )' % (ph, LL, PEEKS))
    z0fz = w.s([u['nl'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NL))
    C0 = CL('P1', 'N', DJ('0')); C1 = CL('A', NFJ('0'), DJ('0'))
    e1 = w.s([php, p1h, z0fz, w.inst('tm2lfes1')], 'syl3anc', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C1, '1')))
    C2 = CL('A', NFJ(NL), DJ(NL))
    S_J = SUM('j', NL, '( %s + 2 )' % YF('j'))
    e2 = w.s([], 'tm2lfes3', '( %s -> %s )' % (ph, HR(C1, 'T', 'M', C2, S_J)))
    nlfz = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    dn = w.s([u['pty'], nlfz], 'ffvelcdmd', '( %s -> %s e. %s )' % (ph, DJ(NL), STK_T))
    nlr = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    nlt = w.s([nlr], 'ltnrd', '( %s -> -. %s < %s )' % (ph, NL, NL))
    an = '( %s /\\ m e. %s )' % (ph, NFJ(NL))
    mn = w.s([], 'simpr', '( %s -> m e. %s )' % (an, NFJ(NL)))
    bic = outnf(w, an, 'm', NL, mn)
    nlta = w.s([nlt], 'adantr', '( %s -> -. %s < %s )' % (an, NL, NL))
    cm = w.s([nlta, bic], 'mtbird', '( %s -> -. ( C ` m ) = 1o )' % an)
    he = w.s([cm], 'ralrimiva', '( %s -> A. m e. %s -. ( C ` m ) = 1o )' % (ph, NFJ(NL)))
    nfs, nfn = nfss(w, ph, NL, u['nss'])
    _, gq = gotost(w, ph, "A'", u['tv'], u['a1l'])
    C3 = CL('E', NFJ(NL), DJ(NL))
    e3 = brstep(w, ph, 'tm2fbrg', u['phm'], u['ma'], u['al'], u['el'], dn, u['cc'], gq, nfs, he, 'A', 'E', NFJ(NL), DJ(NL))
    C4 = CL('E', NFIN, DJ(NL))
    aq = '( %s /\\ q e. N )' % ph
    aqb = '( %s /\\ ( ( C ` q ) = 1o <-> %s < %s ) )' % (aq, NL, NL)
    bq = w.s([], 'simpr', '( %s -> ( ( C ` q ) = 1o <-> %s < %s ) )' % (aqb, NL, NL))
    nltb = w.s([nlt], 'ad2antrr', '( %s -> -. %s < %s )' % (aqb, NL, NL))
    cq = w.s([nltb, bq], 'mtbird', '( %s -> -. ( C ` q ) = 1o )' % aqb)
    cqe = w.s([cq], 'ex', '( %s -> ( ( ( C ` q ) = 1o <-> %s < %s ) -> -. ( C ` q ) = 1o ) )' % (aq, NL, NL))
    rss = w.s([cqe], 'ss2rabdv', '( %s -> %s C_ %s )' % (ph, NFJ(NL), NFIN))
    x2 = clnss(w, ph, 'E', NFJ(NL), NFIN, DJ(NL), rss)
    nfin0 = w.s([], 'ssrab2', '%s C_ N' % NFIN)
    nfin0a = w.s([nfin0], 'a1i', '( %s -> %s C_ N )' % (ph, NFIN))
    nfins = w.s([nfin0a, u['nss']], 'sstrd', '( %s -> %s C_ %s )' % (ph, NFIN, SS))
    c4cfg = cfgcl6(w, ph, 'E', NFIN, DJ(NL), u['tv'], u['el'], nfins, dn)
    e3b = hssd(w, ph, u['phm'], C2, C3, '1', C4, e3, x2, c4cfg)
    q1 = hrseq(w, ph, u['phm'], e1, e2, C0, C1, C2, '1', S_J)
    q2 = hrseq(w, ph, u['phm'], q1, e3b, C0, C2, C4, '( 1 + %s )' % S_J, '1')
    # ( ( 1 + S ) + 1 ) = ( S + 2 )
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, NL)
    io = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NL))
    cgi, newi = w.wcongr(HBSF('j'), {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    assert newi == HBSF('i'), newi
    hba = w.s([u['hb']], 'adantr', '( %s -> %s )' % (pi, HBS))
    hbi = w.s([cgi, hba, io], 'rspcdva', '( %s -> %s )' % (pi, HBSF('i')))
    yni = w.s([hbi], 'simpld', '( %s -> %s e. NN0 )' % (pi, YF('i')))
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % pi)
    y2n = w.s([yni, twoa], 'nn0addcld', '( %s -> ( %s + 2 ) e. NN0 )' % (pi, YF('i')))
    S_I = SUM('i', NL, '( %s + 2 )' % YF('i'))
    fia = w.s([w.s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NL)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NL))
    sni = w.s([fia, y2n], 'fsumnn0cl', '( %s -> %s e. NN0 )' % (ph, S_I))
    g1 = w.s([], 'fveq2', '( i = j -> ( Y ` i ) = ( Y ` j ) )')
    g2 = w.s([g1], 'oveq1d', '( i = j -> ( ( Y ` i ) + 2 ) = ( ( Y ` j ) + 2 ) )')
    cbs = w.s([g2], 'cbvsumv', '%s = %s' % (S_I, S_J))
    cbsa = w.s([cbs], 'a1i', '( %s -> %s = %s )' % (ph, S_I, S_J))
    sn = w.s([cbsa, sni], 'eqeltrrd', '( %s -> %s e. NN0 )' % (ph, S_J))
    sc = w.s([sn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, S_J))
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % ph)
    f1 = w.s([onea, sc], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (ph, S_J, S_J))
    f2 = w.s([f1], 'oveq1d', '( %s -> ( ( 1 + %s ) + 1 ) = ( ( %s + 1 ) + 1 ) )' % (ph, S_J, S_J))
    f3 = w.s([sc, onea, onea], 'addassd', '( %s -> ( ( %s + 1 ) + 1 ) = ( %s + ( 1 + 1 ) ) )' % (ph, S_J, S_J))
    f4 = w.s([], '1p1e2', '( 1 + 1 ) = 2')
    f5 = w.s([f4], 'oveq2i', '( %s + ( 1 + 1 ) ) = ( %s + 2 )' % (S_J, S_J))
    f5a = w.s([f5], 'a1i', '( %s -> ( %s + ( 1 + 1 ) ) = ( %s + 2 ) )' % (ph, S_J, S_J))
    f6 = w.s([f2, f3], 'eqtrd', '( %s -> ( ( 1 + %s ) + 1 ) = ( %s + ( 1 + 1 ) ) )' % (ph, S_J, S_J))
    f7 = w.s([f6, f5a], 'eqtrd', '( %s -> ( ( 1 + %s ) + 1 ) = ( %s + 2 ) )' % (ph, S_J, S_J))
    o = w.s([f7], 'opeq2d', '( %s -> <. %s , ( ( 1 + %s ) + 1 ) >. = <. %s , ( %s + 2 ) >. )' % (ph, C4, S_J, C4, S_J))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C4, '( ( 1 + %s ) + 1 )' % S_J), HR(C0, 'T', 'M', C4, '( %s + 2 )' % S_J)))
    w.qed([b, q2], 'mpbid', ST_FES)
    return w.run()


if __name__ == '__main__':
    for f in [tm2fpshf, tm2lfes1a, tm2lfes1b, tm2lfes1, tm2lfes2, tm2lfes3, tm2lfes]:
        if want(f.__name__): f()
