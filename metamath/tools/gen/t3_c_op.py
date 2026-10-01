"""T3: the body lemmas of the two-operand loops `addLoop`, `subLoop` and
`cmpFrag` (blueprint 2).

Each takes the read phase --- two instances of ~ tm2frd composed --- as the
hypothesis

  A. r e. N E. p e. O ( ( M ` A ) ( TM2sa ` T ) <. r , D >. ) = ( REST ( TM2sa ` T ) <. p , D' >. )

with ` N ` the incoming state class, ` O ` the post-read class (Lean's
anonymous ` v2 ` with its property list) and ` D' ` the stacks after the
reads; and the interface of the body proper on ` O ` .
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepE
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GI = '( %s ` I )' % G('T')
STMT_T = '( TM2Stmt ` T )'
CTY = 'C e. ( 2o ^m %s )' % S('T')
CTY2 = "C' e. ( 2o ^m %s )" % S('T')
PTY = 'P e. ( %s ^m %s )' % (GI, S('T'))
FTY = 'F e. ( %s ^m %s )' % (S('T'), S('T'))
GA = GOTO(CONSTF('T', 'A'))
GE = GOTO(CONSTF('T', 'E'))
NSS = "( N C_ %s /\\ O C_ %s /\\ N' C_ %s )" % (S('T'), S('T'), S('T'))
SAP = lambda st, x, y: '( %s %s <. %s , %s >. )' % (st, SA('T'), x, y)
D3 = UPD('T', "D'", 'I', '( <" Z "> ++ ( %s ` I ) )' % "D'")
MA = lambda x: '( ( M ` A ) %s <. %s , D >. )' % (SA('T'), x)


def H1(REST):
    return 'A. r e. N E. p e. O %s = %s' % (MA('r'), SAP(REST, 'p', "D'"))


def readh(w, av, REST, h1a):
    """H1 at r := v, with the existential's binder renamed to q"""
    eqf = lambda x, y: '%s = %s' % (MA(x), SAP(REST, y, "D'"))
    i1 = w.s([], 'opeq1', '( r = v -> <. r , D >. = <. v , D >. )')
    i2 = w.s([i1], 'oveq2d', '( r = v -> %s = %s )' % (MA('r'), MA('v')))
    i3 = w.s([i2], 'eqeq1d', '( r = v -> ( %s <-> %s ) )' % (eqf('r', 'p'), eqf('v', 'p')))
    i4 = w.s([i3], 'rexbidv', '( r = v -> ( E. p e. O %s <-> E. p e. O %s ) )'
             % (eqf('r', 'p'), eqf('v', 'p')))
    vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
    ex = w.s([i4, h1a, vn], 'rspcdva', '( %s -> E. p e. O %s )' % (av, eqf('v', 'p')))
    j1 = w.s([], 'opeq1', "( p = q -> <. p , D' >. = <. q , D' >. )")
    j2 = w.s([j1], 'oveq2d', '( p = q -> %s = %s )' % (SAP(REST, 'p', "D'"), SAP(REST, 'q', "D'")))
    j3 = w.s([j2], 'eqeq2d', '( p = q -> ( %s <-> %s ) )' % (eqf('v', 'p'), eqf('v', 'q')))
    cb = w.s([j3], 'cbvrexvw', '( E. p e. O %s <-> E. q e. O %s )' % (eqf('v', 'p'), eqf('v', 'q')))
    cba = w.s([cb], 'a1i', '( %s -> ( E. p e. O %s <-> E. q e. O %s ) )'
              % (av, eqf('v', 'p'), eqf('v', 'q')))
    exq = w.s([cba, ex], 'mpbid', '( %s -> E. q e. O %s )' % (av, eqf('v', 'q')))
    return exq, eqf


def h2at(w, a3, H2BODY, h2a, qo):
    """H2 at p := q; H2BODY(x) is the interface's text at the state x"""
    st, new = W.wcongr(w, H2BODY('p'), {'p': 'q'}, 'p = q', {'p': w.s([], 'id', '( p = q -> p = q )')})
    assert new == H2BODY('q'), new
    return w.s([st, h2a, qo], 'rspcdva', '( %s -> %s )' % (a3, H2BODY('q')))


def common(w, ph, LABTY, FUNTY, H1T, H2T):
    """the shared context of a body lemma"""
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    lab = w.s([], 'simp1r', '( %s -> %s )' % (ph, LABTY))
    fun = w.s([], 'simp2', '( %s -> %s )' % (ph, FUNTY))
    hyp = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, NSS, H1T, H2T))
    nss = w.s([hyp, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, NSS))
    n1s = w.s([nss, w.inst('simp1')], 'syl', '( %s -> N C_ %s )' % (ph, S('T')))
    nos = w.s([nss, w.inst('simp2')], 'syl', '( %s -> O C_ %s )' % (ph, S('T')))
    n2s = w.s([nss, w.inst('simp3')], 'syl', "( %s -> N' C_ %s )" % (ph, S('T')))
    h1 = w.s([hyp, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, H1T))
    h2 = w.s([hyp, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, H2T))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, lab=lab, fun=fun, n1s=n1s, nos=nos, n2s=n2s, h1=h1, h2=h2, tv=tv)


def postcl(w, ph, LB, NC, DC, tv, lcl, dcl, ncss):
    """( ph -> ( { ( inl ` LB ) } X. ( NC X. { DC } ) ) C_ ( TM2Cfg ` T ) )"""
    POST = '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (LB, NC, DC)
    sn = w.s([dcl], 'snssd', '( %s -> { %s } C_ %s )' % (ph, DC, STK('T')))
    xs = w.s([ncss, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ ( %s X. %s ) )' % (ph, NC, DC, S('T'), STK('T')))
    return POST, w.s([tv, lcl, xs, w.inst('tm2hcfgss')], 'syl3anc',
                     '( %s -> %s C_ %s )' % (ph, POST, CFG('T')))


def memb(w, a3, LB, NC, DC, NEWV, nvcl, dccl, lcl):
    """( a3 -> <. ( inl ` LB ) , <. NEWV , DC >. >. e. ( { ( inl ` LB ) } X. ( NC X. { DC } ) ) )"""
    POST = '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (LB, NC, DC)
    RES = '<. ( inl ` %s ) , <. %s , %s >. >.' % (LB, NEWV, DC)
    inle = w.s([], 'fvex', '( inl ` %s ) e. _V' % LB)
    sn1 = w.s([inle, w.inst('snidg')], 'ax-mp', '( inl ` %s ) e. { ( inl ` %s ) }' % (LB, LB))
    sn1a = w.s([sn1], 'a1i', '( %s -> ( inl ` %s ) e. { ( inl ` %s ) } )' % (a3, LB, LB))
    dv = w.s([dccl], 'elexd', '( %s -> %s e. _V )' % (a3, DC))
    sn2 = w.s([dv, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (a3, DC, DC))
    pr = w.s([nvcl, sn2], 'opelxpd', '( %s -> <. %s , %s >. e. ( %s X. { %s } ) )' % (a3, NEWV, DC, NC, DC))
    return RES, w.s([sn1a, pr], 'opelxpd', '( %s -> %s e. %s )' % (a3, RES, POST))


# ------------------------------------------------------------------ tm2fad1

def tm2fad1():
    lab = 'tm2fad1'
    CONT = PUSH('I', 'P', LOAD('F', GA))
    REST = BRANCH('C', 'Q', CONT)
    LABTY = ("( A e. %s /\\ ( I e. %s /\\ Z e. %s ) /\\ ( D e. %s /\\ D' e. %s ) )"
             % (L('T'), DG, GI, STK('T'), STK('T')))
    FUNTY = '( ( %s /\\ %s /\\ %s ) /\\ Q e. %s )' % (CTY, PTY, FTY, STMT_T)
    H2B = lambda x: ("( -. ( C ` %s ) = 1o /\\ ( P ` %s ) = Z /\\ ( F ` %s ) e. N' )" % (x, x, x))
    H2T = 'A. p e. O %s' % H2B('p')
    H1T = H1(REST)
    ph = '( ( %s /\\ %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )' % (PHM, LABTY, FUNTY, NSS, H1T, H2T)
    w = W(lab, 'The continue step of the two-operand adder and subtractor: '
               'after the read phase the operands are not both exhausted, the '
               'letter ` Z ` is pushed on the output stack ` I ` , the carry is '
               'updated by ` F ` and the machine loops.  Lean: '
               '` addLoop_loop ` cases 2, 3, 4 and ` subLoop_loop ` cases 2, 3, '
               '4 --- ` subBody ` is ` addBody ` with a different exit branch, '
               'and the exit branch ` Q ` is a class variable, so the two share '
               'this lemma.')
    u = common(w, ph, LABTY, FUNTY, H1T, H2T)
    al = w.s([u['lab'], w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    iz = w.s([u['lab'], w.inst('simp2')], 'syl', '( %s -> ( I e. %s /\\ Z e. %s ) )' % (ph, DG, GI))
    ii = w.s([iz], 'simpld', '( %s -> I e. %s )' % (ph, DG))
    zz = w.s([iz], 'simprd', '( %s -> Z e. %s )' % (ph, GI))
    dds = w.s([u['lab'], w.inst('simp3')], 'syl',
              "( %s -> ( D e. %s /\\ D' e. %s ) )" % (ph, STK('T'), STK('T')))
    dd = w.s([dds], 'simpld', '( %s -> D e. %s )' % (ph, STK('T')))
    dp = w.s([dds], 'simprd', "( %s -> D' e. %s )" % (ph, STK('T')))
    f3 = w.s([u['fun']], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, CTY, PTY, FTY))
    cc = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, CTY))
    pp = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, PTY))
    ff = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, FTY))
    qq = w.s([u['fun']], 'simprd', '( %s -> Q e. %s )' % (ph, STMT_T))
    fa = constfty(w, ph, 'A', L('T'), al)
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ld = w.s([u['tv'], ff, ga, w.inst('tm2load')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, LOAD('F', GA), STMT_T))
    ip = w.s([ii, pp], 'jca', '( %s -> ( I e. %s /\\ %s ) )' % (ph, DG, PTY))
    cnt = w.s([u['tv'], ip, ld, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, CONT, STMT_T))
    dkw = w.s([u['tv'], dp, ii, w.inst('tm2stkfv')], 'syl3anc',
              "( %s -> ( D' ` I ) e. Word %s )" % (ph, GI))
    s1c = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ph, GI))
    zdw = w.s([s1c, dkw, w.inst('ccatcl')], 'syl2anc',
              "( %s -> ( <\" Z \"> ++ ( D' ` I ) ) e. Word %s )" % (ph, GI))
    kj = w.s([ii, zdw], 'jca', "( %s -> ( I e. %s /\\ ( <\" Z \"> ++ ( D' ` I ) ) e. Word %s ) )"
             % (ph, DG, GI))
    d3cl = w.s([u['tv'], dp, kj, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D3, STK('T')))
    POST, pss = postcl(w, ph, 'A', "N'", D3, u['tv'], al, d3cl, u['n2s'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        h1a = A_(u['h1'], H1T)
        exq, eqf = readh(w, av, REST, h1a)
        a3 = '( %s /\\ ( q e. O /\\ %s ) )' % (av, eqf('v', 'q'))
        def B_(st, f): return w.s([st], 'ad2antrr', '( %s -> %s )' % (a3, f))
        tv = B_(u['tv'], 'T e. V'); dpa = B_(dp, "D' e. %s" % STK('T'))
        cca = B_(cc, CTY); ppa = B_(pp, PTY); ffa = B_(ff, FTY); qqa = B_(qq, 'Q e. %s' % STMT_T)
        iia = B_(ii, 'I e. %s' % DG); zza = B_(zz, 'Z e. %s' % GI)
        ala = B_(al, 'A e. %s' % L('T')); faa = B_(fa, '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        gaa = B_(ga, '%s e. %s' % (GA, STMT_T)); lda = B_(ld, '%s e. %s' % (LOAD('F', GA), STMT_T))
        cnta = B_(cnt, '%s e. %s' % (CONT, STMT_T)); d3a = B_(d3cl, '%s e. %s' % (D3, STK('T')))
        nosa = B_(u['nos'], 'O C_ %s' % S('T')); n2sa = B_(u['n2s'], "N' C_ %s" % S('T'))
        h2a = B_(u['h2'], H2T)
        qo = w.s([], 'simprl', '( %s -> q e. O )' % a3)
        eqs = w.s([], 'simprr', '( %s -> %s )' % (a3, eqf('v', 'q')))
        trip = h2at(w, a3, H2B, h2a, qo)
        cq = w.s([trip, w.inst('simp1')], 'syl', '( %s -> -. ( C ` q ) = 1o )' % a3)
        pq = w.s([trip, w.inst('simp2')], 'syl', '( %s -> ( P ` q ) = Z )' % a3)
        fq = w.s([trip, w.inst('simp3')], 'syl', "( %s -> ( F ` q ) e. N' )" % a3)
        qs = w.s([nosa, qo], 'sseldd', '( %s -> q e. %s )' % (a3, S('T')))
        fqs = w.s([n2sa, fq], 'sseldd', '( %s -> ( F ` q ) e. %s )' % (a3, S('T')))
        avv = w.s([ala], 'elexd', '( %s -> A e. _V )' % a3)
        rga = w.s([avv, fqs, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` ( F ` q ) ) = A )' % (a3, CONSTF('T', 'A')))
        facts = {'T e. V': tv, 'q e. %s' % S('T'): qs, '( F ` q ) e. %s' % S('T'): fqs,
                 "D' e. %s" % STK('T'): dpa, '%s e. %s' % (D3, STK('T')): d3a,
                 CTY: cca, PTY: ppa, FTY: ffa, 'Q e. %s' % STMT_T: qqa,
                 '%s e. %s' % (CONT, STMT_T): cnta, '%s e. %s' % (LOAD('F', GA), STMT_T): lda,
                 '%s e. %s' % (GA, STMT_T): gaa, 'I e. %s' % DG: iia,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): faa}
        rules = {'( P ` q )': ('Z', pq), '( %s ` ( F ` q ) )' % CONSTF('T', 'A'): ('A', rga)}
        ifr = {'( C ` q ) = 1o': (False, cq)}
        ex = Exec(w, a3, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(REST, "<. q , D' >.")
        RES, mem = memb(w, a3, 'A', "N'", D3, '( F ` q )', fq, d3a, ala)
        assert res == RES, 'GOT %s\nWANT %s' % (res, RES)
        tot = w.s([eqs, st], 'eqtrd', '( %s -> %s = %s )' % (a3, MA('v'), res))
        inc = w.s([tot, mem], 'eqeltrd', '( %s -> %s e. %s )' % (a3, MA('v'), POST))
        imp = w.s([inc], 'rexlimdvaa', '( %s -> ( E. q e. O %s -> %s e. %s ) )'
                  % (av, eqf('v', 'q'), MA('v'), POST))
        return w.s([imp, exq], 'mpd', '( %s -> %s e. %s )' % (av, MA('v'), POST))
    hstepE(w, ph, 'T', 'M', 'A', 'N', 'D', POST, (None, u['phm']), al, pss, u['n1s'], dd,
           body, qed=True)
    return w.run()



# ------------------------------------------------------------ the exit steps

EXIT = BRANCH("C'", PUSH('I', 'P', GE), GE)


def _common2(w, ph, LABTY, FUNTY, H1T, H2T, withE=True, withI=True):
    u = common(w, ph, LABTY, FUNTY, H1T, H2T)
    fst = ((lambda f: w.s([u['lab'], w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, f))) if withI
           else (lambda f: w.s([u['lab']], 'simpld', '( %s -> %s )' % (ph, f))))
    if withE:
        ae = fst('( A e. %s /\\ E e. %s )' % (L('T'), L('T')))
        al = w.s([ae], 'simpld', '( %s -> A e. %s )' % (ph, L('T')))
        el = w.s([ae], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    else:
        al = fst('A e. %s' % L('T'))
        el = None
    if withI:
        iz = w.s([u['lab'], w.inst('simp2')], 'syl',
                 '( %s -> ( I e. %s /\\ Z e. %s ) )' % (ph, DG, GI))
        ii = w.s([iz], 'simpld', '( %s -> I e. %s )' % (ph, DG))
        zz = w.s([iz], 'simprd', '( %s -> Z e. %s )' % (ph, GI))
        dds = w.s([u['lab'], w.inst('simp3')], 'syl',
                  "( %s -> ( D e. %s /\\ D' e. %s ) )" % (ph, STK('T'), STK('T')))
    else:
        ii = zz = None
        dds = w.s([u['lab']], 'simprd', "( %s -> ( D e. %s /\\ D' e. %s ) )" % (ph, STK('T'), STK('T')))
    dd = w.s([dds], 'simpld', '( %s -> D e. %s )' % (ph, STK('T')))
    dp = w.s([dds], 'simprd', "( %s -> D' e. %s )" % (ph, STK('T')))
    u.update(al=al, el=el, ii=ii, zz=zz, dd=dd, dp=dp)
    return u


def _d3(w, ph, u):
    dkw = w.s([u['tv'], u['dp'], u['ii'], w.inst('tm2stkfv')], 'syl3anc',
              "( %s -> ( D' ` I ) e. Word %s )" % (ph, GI))
    s1c = w.s([u['zz']], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ph, GI))
    zdw = w.s([s1c, dkw, w.inst('ccatcl')], 'syl2anc',
              "( %s -> ( <\" Z \"> ++ ( D' ` I ) ) e. Word %s )" % (ph, GI))
    kj = w.s([u['ii'], zdw], 'jca',
             "( %s -> ( I e. %s /\\ ( <\" Z \"> ++ ( D' ` I ) ) e. Word %s ) )" % (ph, DG, GI))
    return w.s([u['tv'], u['dp'], kj, w.inst('tm2stkupd')], 'syl3anc',
               '( %s -> %s e. %s )' % (ph, D3, STK('T')))


def tm2fad0c():
    lab = 'tm2fad0c'
    REST = BRANCH('C', EXIT, 'R')
    LABTY = ("( ( A e. %s /\\ E e. %s ) /\\ ( I e. %s /\\ Z e. %s ) /\\ ( D e. %s /\\ D' e. %s ) )"
             % (L('T'), L('T'), DG, GI, STK('T'), STK('T')))
    FUNTY = '( ( %s /\\ %s /\\ %s ) /\\ R e. %s )' % (CTY, CTY2, PTY, STMT_T)
    H2B = lambda x: ("( ( ( C ` %s ) = 1o /\\ ( C' ` %s ) = 1o ) /\\ ( ( P ` %s ) = Z /\\ %s e. N' ) )"
                     % (x, x, x, x))
    H2T = 'A. p e. O %s' % H2B('p')
    H1T = H1(REST)
    ph = '( ( %s /\\ %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )' % (PHM, LABTY, FUNTY, NSS, H1T, H2T)
    w = W(lab, 'The exit step of the two-operand adder when the carry is set: '
               'after the read phase both operands are exhausted and the carry '
               'is flushed as the letter ` Z ` on the output stack ` I ` .  '
               'Lean: ` addLoop_loop ` case 1 with ` c = true ` (the '
               '` addCarry ` clause of ` addBits ` ).')
    u = _common2(w, ph, LABTY, FUNTY, H1T, H2T)
    f3 = w.s([u['fun']], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, CTY, CTY2, PTY))
    cc = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY2))
    pp = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    rr = w.s([u['fun']], 'simprd', '( %s -> R e. %s )' % (ph, STMT_T))
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    ip = w.s([u['ii'], pp], 'jca', '( %s -> ( I e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], ip, ge, w.inst('tm2push')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, PUSH('I', 'P', GE), STMT_T))
    pg = w.s([pu, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
             % (ph, PUSH('I', 'P', GE), STMT_T, GE, STMT_T))
    ex = w.s([u['tv'], c2, pg, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, EXIT, STMT_T))
    d3cl = _d3(w, ph, u)
    POST, pss = postcl(w, ph, 'E', "N'", D3, u['tv'], u['el'], d3cl, u['n2s'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        exq, eqf = readh(w, av, REST, A_(u['h1'], H1T))
        a3 = '( %s /\\ ( q e. O /\\ %s ) )' % (av, eqf('v', 'q'))
        def B_(st, f): return w.s([st], 'ad2antrr', '( %s -> %s )' % (a3, f))
        tv = B_(u['tv'], 'T e. V'); dpa = B_(u['dp'], "D' e. %s" % STK('T'))
        cca = B_(cc, CTY); c2a = B_(c2, CTY2); ppa = B_(pp, PTY); rra = B_(rr, 'R e. %s' % STMT_T)
        iia = B_(u['ii'], 'I e. %s' % DG); ela = B_(u['el'], 'E e. %s' % L('T'))
        fea = B_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        gea = B_(ge, '%s e. %s' % (GE, STMT_T)); pua = B_(pu, '%s e. %s' % (PUSH('I', 'P', GE), STMT_T))
        exa = B_(ex, '%s e. %s' % (EXIT, STMT_T)); d3a = B_(d3cl, '%s e. %s' % (D3, STK('T')))
        nosa = B_(u['nos'], 'O C_ %s' % S('T')); n2sa = B_(u['n2s'], "N' C_ %s" % S('T'))
        h2a = B_(u['h2'], H2T)
        qo = w.s([], 'simprl', '( %s -> q e. O )' % a3)
        eqs = w.s([], 'simprr', '( %s -> %s )' % (a3, eqf('v', 'q')))
        trip = h2at(w, a3, H2B, h2a, qo)
        t1 = w.s([trip], 'simpld', "( %s -> ( ( C ` q ) = 1o /\\ ( C' ` q ) = 1o ) )" % a3)
        t2 = w.s([trip], 'simprd', "( %s -> ( ( P ` q ) = Z /\\ q e. N' ) )" % a3)
        cq = w.s([t1], 'simpld', '( %s -> ( C ` q ) = 1o )' % a3)
        c2q = w.s([t1], 'simprd', "( %s -> ( C' ` q ) = 1o )" % a3)
        pq = w.s([t2], 'simpld', '( %s -> ( P ` q ) = Z )' % a3)
        qn = w.s([t2], 'simprd', "( %s -> q e. N' )" % a3)
        qs = w.s([nosa, qo], 'sseldd', '( %s -> q e. %s )' % (a3, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % a3)
        rge = w.s([evv, qs, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` q ) = E )' % (a3, CONSTF('T', 'E')))
        facts = {'T e. V': tv, 'q e. %s' % S('T'): qs,
                 "D' e. %s" % STK('T'): dpa, '%s e. %s' % (D3, STK('T')): d3a,
                 CTY: cca, CTY2: c2a, PTY: ppa, 'R e. %s' % STMT_T: rra,
                 '%s e. %s' % (EXIT, STMT_T): exa, '%s e. %s' % (GE, STMT_T): gea,
                 '%s e. %s' % (PUSH('I', 'P', GE), STMT_T): pua, 'I e. %s' % DG: iia,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( P ` q )': ('Z', pq), '( %s ` q )' % CONSTF('T', 'E'): ('E', rge)}
        ifr = {'( C ` q ) = 1o': (True, cq), "( C' ` q ) = 1o": (True, c2q)}
        exe = Exec(w, a3, 'T', facts, rules=rules, ifrules=ifr)
        st, res = exe.run(REST, "<. q , D' >.")
        RES, mem = memb(w, a3, 'E', "N'", D3, 'q', qn, d3a, ela)
        assert res == RES, 'GOT %s\nWANT %s' % (res, RES)
        tot = w.s([eqs, st], 'eqtrd', '( %s -> %s = %s )' % (a3, MA('v'), res))
        inc = w.s([tot, mem], 'eqeltrd', '( %s -> %s e. %s )' % (a3, MA('v'), POST))
        imp = w.s([inc], 'rexlimdvaa', '( %s -> ( E. q e. O %s -> %s e. %s ) )'
                  % (av, eqf('v', 'q'), MA('v'), POST))
        return w.s([imp, exq], 'mpd', '( %s -> %s e. %s )' % (av, MA('v'), POST))
    hstepE(w, ph, 'T', 'M', 'A', 'N', 'D', POST, (None, u['phm']), u['al'], pss, u['n1s'],
           u['dd'], body, qed=True)
    return w.run()


def tm2fad0n():
    lab = 'tm2fad0n'
    REST = BRANCH('C', EXIT, 'R')
    LABTY = ("( ( A e. %s /\\ E e. %s ) /\\ ( I e. %s /\\ Z e. %s ) /\\ ( D e. %s /\\ D' e. %s ) )"
             % (L('T'), L('T'), DG, GI, STK('T'), STK('T')))
    FUNTY = '( ( %s /\\ %s /\\ %s ) /\\ R e. %s )' % (CTY, CTY2, PTY, STMT_T)
    H2B = lambda x: ("( ( C ` %s ) = 1o /\\ -. ( C' ` %s ) = 1o /\\ %s e. N' )" % (x, x, x))
    H2T = 'A. p e. O %s' % H2B('p')
    H1T = H1(REST)
    ph = '( ( %s /\\ %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )' % (PHM, LABTY, FUNTY, NSS, H1T, H2T)
    w = W(lab, 'The exit step of the two-operand adder when the carry is clear: '
               'after the read phase both operands are exhausted and nothing is '
               'pushed.  Lean: ` addLoop_loop ` case 1 with ` c = false ` .')
    u = _common2(w, ph, LABTY, FUNTY, H1T, H2T)
    f3 = w.s([u['fun']], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, CTY, CTY2, PTY))
    cc = w.s([f3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, CTY))
    c2 = w.s([f3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY2))
    pp = w.s([f3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    rr = w.s([u['fun']], 'simprd', '( %s -> R e. %s )' % (ph, STMT_T))
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    ip = w.s([u['ii'], pp], 'jca', '( %s -> ( I e. %s /\\ %s ) )' % (ph, DG, PTY))
    pu = w.s([u['tv'], ip, ge, w.inst('tm2push')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, PUSH('I', 'P', GE), STMT_T))
    pg = w.s([pu, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
             % (ph, PUSH('I', 'P', GE), STMT_T, GE, STMT_T))
    ex = w.s([u['tv'], c2, pg, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, EXIT, STMT_T))
    POST, pss = postcl(w, ph, 'E', "N'", "D'", u['tv'], u['el'], u['dp'], u['n2s'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        exq, eqf = readh(w, av, REST, A_(u['h1'], H1T))
        a3 = '( %s /\\ ( q e. O /\\ %s ) )' % (av, eqf('v', 'q'))
        def B_(st, f): return w.s([st], 'ad2antrr', '( %s -> %s )' % (a3, f))
        tv = B_(u['tv'], 'T e. V'); dpa = B_(u['dp'], "D' e. %s" % STK('T'))
        cca = B_(cc, CTY); c2a = B_(c2, CTY2); ppa = B_(pp, PTY); rra = B_(rr, 'R e. %s' % STMT_T)
        iia = B_(u['ii'], 'I e. %s' % DG); ela = B_(u['el'], 'E e. %s' % L('T'))
        fea = B_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        gea = B_(ge, '%s e. %s' % (GE, STMT_T)); pua = B_(pu, '%s e. %s' % (PUSH('I', 'P', GE), STMT_T))
        exa = B_(ex, '%s e. %s' % (EXIT, STMT_T))
        nosa = B_(u['nos'], 'O C_ %s' % S('T'))
        h2a = B_(u['h2'], H2T)
        qo = w.s([], 'simprl', '( %s -> q e. O )' % a3)
        eqs = w.s([], 'simprr', '( %s -> %s )' % (a3, eqf('v', 'q')))
        trip = h2at(w, a3, H2B, h2a, qo)
        cq = w.s([trip, w.inst('simp1')], 'syl', '( %s -> ( C ` q ) = 1o )' % a3)
        c2q = w.s([trip, w.inst('simp2')], 'syl', "( %s -> -. ( C' ` q ) = 1o )" % a3)
        qn = w.s([trip, w.inst('simp3')], 'syl', "( %s -> q e. N' )" % a3)
        qs = w.s([nosa, qo], 'sseldd', '( %s -> q e. %s )' % (a3, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % a3)
        rge = w.s([evv, qs, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` q ) = E )' % (a3, CONSTF('T', 'E')))
        facts = {'T e. V': tv, 'q e. %s' % S('T'): qs,
                 "D' e. %s" % STK('T'): dpa,
                 CTY: cca, CTY2: c2a, PTY: ppa, 'R e. %s' % STMT_T: rra,
                 '%s e. %s' % (EXIT, STMT_T): exa, '%s e. %s' % (GE, STMT_T): gea,
                 '%s e. %s' % (PUSH('I', 'P', GE), STMT_T): pua, 'I e. %s' % DG: iia,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` q )' % CONSTF('T', 'E'): ('E', rge)}
        ifr = {'( C ` q ) = 1o': (True, cq), "( C' ` q ) = 1o": (False, c2q)}
        exe = Exec(w, a3, 'T', facts, rules=rules, ifrules=ifr)
        st, res = exe.run(REST, "<. q , D' >.")
        RES, mem = memb(w, a3, 'E', "N'", "D'", 'q', qn, dpa, ela)
        assert res == RES, 'GOT %s\nWANT %s' % (res, RES)
        tot = w.s([eqs, st], 'eqtrd', '( %s -> %s = %s )' % (a3, MA('v'), res))
        inc = w.s([tot, mem], 'eqeltrd', '( %s -> %s e. %s )' % (a3, MA('v'), POST))
        imp = w.s([inc], 'rexlimdvaa', '( %s -> ( E. q e. O %s -> %s e. %s ) )'
                  % (av, eqf('v', 'q'), MA('v'), POST))
        return w.s([imp, exq], 'mpd', '( %s -> %s e. %s )' % (av, MA('v'), POST))
    hstepE(w, ph, 'T', 'M', 'A', 'N', 'D', POST, (None, u['phm']), u['al'], pss, u['n1s'],
           u['dd'], body, qed=True)
    return w.run()


def tm2fcm1():
    lab = 'tm2fcm1'
    REST = BRANCH('C', 'Q', LOAD('F', GA))
    LABTY = "( A e. %s /\\ ( D e. %s /\\ D' e. %s ) )" % (L('T'), STK('T'), STK('T'))
    FUNTY = '( ( %s /\\ %s ) /\\ Q e. %s )' % (CTY, FTY, STMT_T)
    H2B = lambda x: ("( -. ( C ` %s ) = 1o /\\ ( F ` %s ) e. N' )" % (x, x))
    H2T = 'A. p e. O %s' % H2B('p')
    H1T = H1(REST)
    ph = '( ( %s /\\ %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )' % (PHM, LABTY, FUNTY, NSS, H1T, H2T)
    w = W(lab, 'The continue step of the two-operand comparator: after the read '
               'phase the operands are not both exhausted, the comparison so '
               'far is folded into the state by ` F ` and the machine loops.  '
               'Lean: ` cmpFrag_loop ` cases 2, 3, 4.  No stack is touched.')
    u = _common2(w, ph, LABTY, FUNTY, H1T, H2T, withE=False, withI=False)
    f2 = w.s([u['fun']], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, CTY, FTY))
    cc = w.s([f2], 'simpld', '( %s -> %s )' % (ph, CTY))
    ff = w.s([f2], 'simprd', '( %s -> %s )' % (ph, FTY))
    qq = w.s([u['fun']], 'simprd', '( %s -> Q e. %s )' % (ph, STMT_T))
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T))
    ld = w.s([u['tv'], ff, ga, w.inst('tm2load')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, LOAD('F', GA), STMT_T))
    POST, pss = postcl(w, ph, 'A', "N'", "D'", u['tv'], u['al'], u['dp'], u['n2s'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        exq, eqf = readh(w, av, REST, A_(u['h1'], H1T))
        a3 = '( %s /\\ ( q e. O /\\ %s ) )' % (av, eqf('v', 'q'))
        def B_(st, f): return w.s([st], 'ad2antrr', '( %s -> %s )' % (a3, f))
        tv = B_(u['tv'], 'T e. V'); dpa = B_(u['dp'], "D' e. %s" % STK('T'))
        cca = B_(cc, CTY); ffa = B_(ff, FTY); qqa = B_(qq, 'Q e. %s' % STMT_T)
        ala = B_(u['al'], 'A e. %s' % L('T'))
        faa = B_(fa, '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        gaa = B_(ga, '%s e. %s' % (GA, STMT_T)); lda = B_(ld, '%s e. %s' % (LOAD('F', GA), STMT_T))
        nosa = B_(u['nos'], 'O C_ %s' % S('T')); n2sa = B_(u['n2s'], "N' C_ %s" % S('T'))
        h2a = B_(u['h2'], H2T)
        qo = w.s([], 'simprl', '( %s -> q e. O )' % a3)
        eqs = w.s([], 'simprr', '( %s -> %s )' % (a3, eqf('v', 'q')))
        trip = h2at(w, a3, H2B, h2a, qo)
        cq = w.s([trip], 'simpld', '( %s -> -. ( C ` q ) = 1o )' % a3)
        fq = w.s([trip], 'simprd', "( %s -> ( F ` q ) e. N' )" % a3)
        qs = w.s([nosa, qo], 'sseldd', '( %s -> q e. %s )' % (a3, S('T')))
        fqs = w.s([n2sa, fq], 'sseldd', '( %s -> ( F ` q ) e. %s )' % (a3, S('T')))
        avv = w.s([ala], 'elexd', '( %s -> A e. _V )' % a3)
        rga = w.s([avv, fqs, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` ( F ` q ) ) = A )' % (a3, CONSTF('T', 'A')))
        facts = {'T e. V': tv, 'q e. %s' % S('T'): qs, '( F ` q ) e. %s' % S('T'): fqs,
                 "D' e. %s" % STK('T'): dpa, CTY: cca, FTY: ffa, 'Q e. %s' % STMT_T: qqa,
                 '%s e. %s' % (LOAD('F', GA), STMT_T): lda, '%s e. %s' % (GA, STMT_T): gaa,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): faa}
        rules = {'( %s ` ( F ` q ) )' % CONSTF('T', 'A'): ('A', rga)}
        ifr = {'( C ` q ) = 1o': (False, cq)}
        exe = Exec(w, a3, 'T', facts, rules=rules, ifrules=ifr)
        st, res = exe.run(REST, "<. q , D' >.")
        RES, mem = memb(w, a3, 'A', "N'", "D'", '( F ` q )', fq, dpa, ala)
        assert res == RES, 'GOT %s\nWANT %s' % (res, RES)
        tot = w.s([eqs, st], 'eqtrd', '( %s -> %s = %s )' % (a3, MA('v'), res))
        inc = w.s([tot, mem], 'eqeltrd', '( %s -> %s e. %s )' % (a3, MA('v'), POST))
        imp = w.s([inc], 'rexlimdvaa', '( %s -> ( E. q e. O %s -> %s e. %s ) )'
                  % (av, eqf('v', 'q'), MA('v'), POST))
        return w.s([imp, exq], 'mpd', '( %s -> %s e. %s )' % (av, MA('v'), POST))
    hstepE(w, ph, 'T', 'M', 'A', 'N', 'D', POST, (None, u['phm']), u['al'], pss, u['n1s'],
           u['dd'], body, qed=True)
    return w.run()


def tm2fcm0():
    lab = 'tm2fcm0'
    REST = BRANCH('C', GE, 'R')
    LABTY = "( ( A e. %s /\\ E e. %s ) /\\ ( D e. %s /\\ D' e. %s ) )" % (L('T'), L('T'), STK('T'), STK('T'))
    FUNTY = '( %s /\\ R e. %s )' % (CTY, STMT_T)
    H2B = lambda x: ("( ( C ` %s ) = 1o /\\ %s e. N' )" % (x, x))
    H2T = 'A. p e. O %s' % H2B('p')
    H1T = H1(REST)
    ph = '( ( %s /\\ %s ) /\\ %s /\\ ( %s /\\ %s /\\ %s ) )' % (PHM, LABTY, FUNTY, NSS, H1T, H2T)
    w = W(lab, 'The exit step of a two-operand loop whose exit is a plain '
               '` goto ` : after the read phase both operands are exhausted and '
               'the machine leaves the loop with the stacks as the read phase '
               'left them.  Lean: ` cmpFrag_loop ` case 1 and ` subLoop_loop ` '
               'case 1 --- the continue branch ` R ` is a class variable, so '
               'the comparator and the subtractor share this lemma.')
    u = _common2(w, ph, LABTY, FUNTY, H1T, H2T, withE=True, withI=False)
    cc = w.s([u['fun']], 'simpld', '( %s -> %s )' % (ph, CTY))
    rr = w.s([u['fun']], 'simprd', '( %s -> R e. %s )' % (ph, STMT_T))
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    POST, pss = postcl(w, ph, 'E', "N'", "D'", u['tv'], u['el'], u['dp'], u['n2s'])

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        exq, eqf = readh(w, av, REST, A_(u['h1'], H1T))
        a3 = '( %s /\\ ( q e. O /\\ %s ) )' % (av, eqf('v', 'q'))
        def B_(st, f): return w.s([st], 'ad2antrr', '( %s -> %s )' % (a3, f))
        tv = B_(u['tv'], 'T e. V'); dpa = B_(u['dp'], "D' e. %s" % STK('T'))
        cca = B_(cc, CTY); rra = B_(rr, 'R e. %s' % STMT_T)
        ela = B_(u['el'], 'E e. %s' % L('T'))
        fea = B_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        gea = B_(ge, '%s e. %s' % (GE, STMT_T))
        nosa = B_(u['nos'], 'O C_ %s' % S('T'))
        h2a = B_(u['h2'], H2T)
        qo = w.s([], 'simprl', '( %s -> q e. O )' % a3)
        eqs = w.s([], 'simprr', '( %s -> %s )' % (a3, eqf('v', 'q')))
        trip = h2at(w, a3, H2B, h2a, qo)
        cq = w.s([trip], 'simpld', '( %s -> ( C ` q ) = 1o )' % a3)
        qn = w.s([trip], 'simprd', "( %s -> q e. N' )" % a3)
        qs = w.s([nosa, qo], 'sseldd', '( %s -> q e. %s )' % (a3, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % a3)
        rge = w.s([evv, qs, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` q ) = E )' % (a3, CONSTF('T', 'E')))
        facts = {'T e. V': tv, 'q e. %s' % S('T'): qs, "D' e. %s" % STK('T'): dpa,
                 CTY: cca, 'R e. %s' % STMT_T: rra, '%s e. %s' % (GE, STMT_T): gea,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` q )' % CONSTF('T', 'E'): ('E', rge)}
        ifr = {'( C ` q ) = 1o': (True, cq)}
        exe = Exec(w, a3, 'T', facts, rules=rules, ifrules=ifr)
        st, res = exe.run(REST, "<. q , D' >.")
        RES, mem = memb(w, a3, 'E', "N'", "D'", 'q', qn, dpa, ela)
        assert res == RES, 'GOT %s\nWANT %s' % (res, RES)
        tot = w.s([eqs, st], 'eqtrd', '( %s -> %s = %s )' % (a3, MA('v'), res))
        inc = w.s([tot, mem], 'eqeltrd', '( %s -> %s e. %s )' % (a3, MA('v'), POST))
        imp = w.s([inc], 'rexlimdvaa', '( %s -> ( E. q e. O %s -> %s e. %s ) )'
                  % (av, eqf('v', 'q'), MA('v'), POST))
        return w.s([imp, exq], 'mpd', '( %s -> %s e. %s )' % (av, MA('v'), POST))
    hstepE(w, ph, 'T', 'M', 'A', 'N', 'D', POST, (None, u['phm']), u['al'], pss, u['n1s'],
           u['dd'], body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fad1'): tm2fad1()
    if want('tm2fad0c'): tm2fad0c()
    if want('tm2fad0n'): tm2fad0n()
    if want('tm2fcm1'): tm2fcm1()
    if want('tm2fcm0'): tm2fcm0()
