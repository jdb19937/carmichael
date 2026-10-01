"""T6: `moveEntries` (blueprint 3.4): the entry loop ~ tm2lfe with the body
~ tm2lme , then ~ tm2lpop on the closing ` bra ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6lib import *
from lin import lineq, linarith

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

NL = '( # ` L )'
FT = lambda F: "%s e. ( %s ^m ( %s X. %s ) )" % (F, S('T'), S('T'), OPT)
CT = lambda C: '%s e. ( 2o ^m %s )' % (C, S('T'))
PTY = "P e. ( Gamma' ^m %s )" % S('T')
NVF = lambda F, r, z: NV(F, r, z)
IF1 = 'A. r e. N A. z e. %s ( %s e. N /\\ ( C ` %s ) = 1o )' % (B4, NVF('F', 'r', 'z'), NVF('F', 'r', 'z'))
IF2 = 'A. r e. N ( %s e. N /\\ -. ( C ` %s ) = 1o )' % (NVF('F', 'r', '2'), NVF('F', 'r', '2'))
IFACE = '( %s /\\ %s )' % (IF1, IF2)
MI1 = "A. r e. N A. z e. %s ( ( C' ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. N )" % (BITS, NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'))
MI2 = "A. r e. N ( -. ( C' ` %s ) = 1o /\\ %s e. N )" % (NVF("F'", 'r', '4'), NVF("F'", 'r', '4'))
MIFACE = '( %s /\\ %s )' % (MI1, MI2)
HPOP = "A. r e. N %s e. N'" % NVF('F"', 'r', '2')
def MOVEP(A, K, J, E):
    return POP(K, "F'", BRANCH("C'", PUSH(J, 'P', GOTOL(A)), GOTOL(E)))
PEEKS = PEEKL('K', 'F', 'A')
TESTS = TESTL('C', "A'", "E'")
PROG1 = '( ( M ` P1 ) = %s /\\ ( M ` A ) = %s /\\ ( M ` A" ) = %s )' % (PEEKS, TESTS, PEEKS)
PROG2 = "( ( M ` A' ) = %s /\\ ( M ` B' ) = %s )" % (PSH('I', '4', "B'"), MOVEP("B'", 'K', 'I', 'B"'))
PROG3 = "( ( M ` B\" ) = %s /\\ ( M ` Q' ) = %s /\\ ( M ` E' ) = %s )" % (PSH('J', '4', "Q'"), MOVEP("Q'", 'I', 'J', 'A"'), POPL('K', 'F"', 'E'))
PROG = '( %s /\\ %s /\\ %s )' % (PROG1, PROG2, PROG3)
LAB = ("( ( P1 e. %s /\\ A e. %s /\\ A' e. %s ) /\\ ( A\" e. %s /\\ B' e. %s /\\ B\" e. %s ) /\\ ( Q' e. %s /\\ E' e. %s /\\ E e. %s ) )" % ((L('T'),) * 9))
IDX = '( ( K e. %s /\\ J e. %s /\\ I e. %s ) /\\ ( K =/= J /\\ K =/= I /\\ J =/= I ) )' % (FZ8, FZ8, FZ8)
HNDS = "( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) )" % (FT('F'), FT("F'"), FT('F"'), CT('C'), CT("C'"), PTY)
NSS2 = "( N C_ %s /\\ N' C_ %s )" % (S('T'), S('T'))
IFS = '( %s /\\ %s /\\ %s )' % (IFACE, MIFACE, HPOP)
DATA = ('( ( D e. %s /\\ ( D ` K ) = %s ) /\\ ( L e. %s /\\ R e. %s ) /\\ ( B e. NN0 /\\ A. w e. ran L ( # ` w ) <_ B ) )'
        % (STK('T'), LST('L', 'R'), WWB, WG))
PHS = '( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) /\\ %s )' % (PHM6, PROG, LAB, IDX, HNDS, NSS2, IFS, DATA)
NFIN = '{ q e. N | -. ( C ` q ) = 1o }'
YB = '( ( 2 x. B ) + 4 )'
def RP(j): return '( reverse ` %s )' % PFX('L', j)
def EJ(j): return '( %s ++ ( D ` J ) )' % ENT(RP(j))
def PJ(j): return UPDT(UPDT('D', 'K', LST(DROP('L', j), 'R')), 'J', EJ(j))
PDEF = '( n e. ( 0 ... %s ) |-> %s )' % (NL, PJ('n'))
DFIN = UPDT(UPDT('D', 'K', 'R'), 'J', '( %s ++ ( D ` J ) )' % ENT('( reverse ` L )'))


def prelude(w, ph):
    p1 = w.s([], 'simp1', '( %s -> ( %s /\\ %s ) )' % (ph, PHM6, PROG))
    p6 = w.s([p1], 'simpld', '( %s -> %s )' % (ph, PHM6))
    phm = w.s([p6], 'simpld', '( %s -> %s )' % (ph, PHM))
    geq = w.s([p6], 'simprd', '( %s -> ( 1st ` ( 1st ` T ) ) = TMGam )' % ph)
    prog = w.s([p1], 'simprd', '( %s -> %s )' % (ph, PROG))
    pg1 = w.s([prog, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, PROG1))
    pg2 = w.s([prog, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, PROG2))
    pg3 = w.s([prog, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PROG3))
    ms = {}
    ms['P1'] = w.s([pg1, w.inst('simp1')], 'syl', '( %s -> ( M ` P1 ) = %s )' % (ph, PEEKS))
    ms['A'] = w.s([pg1, w.inst('simp2')], 'syl', '( %s -> ( M ` A ) = %s )' % (ph, TESTS))
    ms['A"'] = w.s([pg1, w.inst('simp3')], 'syl', '( %s -> ( M ` A" ) = %s )' % (ph, PEEKS))
    ms["A'"] = w.s([pg2], 'simpld', "( %s -> ( M ` A' ) = %s )" % (ph, PSH('I', '4', "B'")))
    ms["B'"] = w.s([pg2], 'simprd', "( %s -> ( M ` B' ) = %s )" % (ph, MOVEP("B'", 'K', 'I', 'B"')))
    ms['B"'] = w.s([pg3, w.inst('simp1')], 'syl', '( %s -> ( M ` B" ) = %s )' % (ph, PSH('J', '4', "Q'")))
    ms["Q'"] = w.s([pg3, w.inst('simp2')], 'syl', "( %s -> ( M ` Q' ) = %s )" % (ph, MOVEP("Q'", 'I', 'J', 'A"')))
    ms["E'"] = w.s([pg3, w.inst('simp3')], 'syl', "( %s -> ( M ` E' ) = %s )" % (ph, POPL('K', 'F"', 'E')))
    p2 = w.s([], 'simp2', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) )' % (ph, LAB, IDX, HNDS, NSS2, IFS))
    li = w.s([p2, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, LAB, IDX))
    lab = w.s([li], 'simpld', '( %s -> %s )' % (ph, LAB))
    idx = w.s([li], 'simprd', '( %s -> %s )' % (ph, IDX))
    ls = {}
    for grp, names in ((1, ['P1', 'A', "A'"]), (2, ['A"', "B'", 'B"']), (3, ["Q'", "E'", 'E'])):
        g = w.s([lab, w.inst('simp%d' % grp)], 'syl', '( %s -> ( %s e. %s /\\ %s e. %s /\\ %s e. %s ) )' % (ph, names[0], L('T'), names[1], L('T'), names[2], L('T')))
        for k, nm in enumerate(names):
            ls[nm] = w.s([g, w.inst('simp%d' % (k + 1))], 'syl', '( %s -> %s e. %s )' % (ph, nm, L('T')))
    i3 = w.s([idx], 'simpld', '( %s -> ( K e. %s /\\ J e. %s /\\ I e. %s ) )' % (ph, FZ8, FZ8, FZ8))
    n3 = w.s([idx], 'simprd', '( %s -> ( K =/= J /\\ K =/= I /\\ J =/= I ) )' % ph)
    kk = w.s([i3, w.inst('simp1')], 'syl', '( %s -> K e. %s )' % (ph, FZ8))
    jj = w.s([i3, w.inst('simp2')], 'syl', '( %s -> J e. %s )' % (ph, FZ8))
    ii = w.s([i3, w.inst('simp3')], 'syl', '( %s -> I e. %s )' % (ph, FZ8))
    nkj = w.s([n3, w.inst('simp1')], 'syl', '( %s -> K =/= J )' % ph)
    nki = w.s([n3, w.inst('simp2')], 'syl', '( %s -> K =/= I )' % ph)
    nji = w.s([n3, w.inst('simp3')], 'syl', '( %s -> J =/= I )' % ph)
    hn = w.s([p2, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, HNDS, NSS2))
    hnds = w.s([hn], 'simpld', '( %s -> %s )' % (ph, HNDS))
    nss2 = w.s([hn], 'simprd', '( %s -> %s )' % (ph, NSS2))
    nss = w.s([nss2], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    n2ss = w.s([nss2], 'simprd', "( %s -> N' C_ %s )" % (ph, S('T')))
    fs = w.s([hnds], 'simpld', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, FT('F'), FT("F'"), FT('F"')))
    cs = w.s([hnds], 'simprd', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, CT('C'), CT("C'"), PTY))
    ff = w.s([fs, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FT('F')))
    f1 = w.s([fs, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, FT("F'")))
    f2 = w.s([fs, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, FT('F"')))
    cc = w.s([cs, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, CT('C')))
    c1 = w.s([cs, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CT("C'")))
    pp = w.s([cs, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    ifs = w.s([p2, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, IFS))
    iface = w.s([ifs, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, IFACE))
    mif = w.s([ifs, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, MIFACE))
    hpop = w.s([ifs, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HPOP))
    p3 = w.s([], 'simp3', '( %s -> %s )' % (ph, DATA))
    dk2 = w.s([p3, w.inst('simp1')], 'syl', '( %s -> ( D e. %s /\\ ( D ` K ) = %s ) )' % (ph, STK('T'), LST('L', 'R')))
    dd = w.s([dk2], 'simpld', '( %s -> D e. %s )' % (ph, STK('T')))
    dk = w.s([dk2], 'simprd', '( %s -> ( D ` K ) = %s )' % (ph, LST('L', 'R')))
    lr = w.s([p3, w.inst('simp2')], 'syl', '( %s -> ( L e. %s /\\ R e. %s ) )' % (ph, WWB, WG))
    ll = w.s([lr], 'simpld', '( %s -> L e. %s )' % (ph, WWB))
    rr = w.s([lr], 'simprd', '( %s -> R e. %s )' % (ph, WG))
    bb2 = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( B e. NN0 /\\ A. w e. ran L ( # ` w ) <_ B ) )' % ph)
    bb = w.s([bb2], 'simpld', '( %s -> B e. NN0 )' % ph)
    bw = w.s([bb2], 'simprd', '( %s -> A. w e. ran L ( # ` w ) <_ B )' % ph)
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kd, gk = gamk(w, ph, 'K', geq, kk)
    jd, gj = gamk(w, ph, 'J', geq, jj)
    idd, gi = gamk(w, ph, 'I', geq, ii)
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    return dict(phm=phm, geq=geq, ms=ms, ls=ls, kk=kk, jj=jj, ii=ii, nkj=nkj, nki=nki, nji=nji,
                ff=ff, f1=f1, f2=f2, cc=cc, c1=c1, pp=pp, nss=nss, n2ss=n2ss, iface=iface, mif=mif, hpop=hpop,
                dd=dd, dk=dk, ll=ll, rr=rr, bb=bb, bw=bw, tv=tv, kd=kd, gk=gk, jd=jd, gj=gj, idd=idd, gi=gi, nl=nl)


def lstcl(w, ph, u, j):
    """( ph -> LST( DROP( L , j ) , R ) e. Word Gamma' )"""
    dr = w.s([u['ll'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DROP('L', j), WWB))
    ec = w.s([dr, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(DROP('L', j)), WG))
    return ccatg(w, ph, ENCB(DROP('L', j)), 'R', ec, u['rr']), dr


def ejcl(w, ph, u, j, djw):
    """( ph -> EJ(j) e. Word Gamma' ), EJ(j) = ( entries ( reverse ( L prefix j ) ) ++ ( D ` J ) )"""
    pf = w.s([u['ll'], w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, PFX('L', j), WWB))
    rv = w.s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, RP(j), WWB))
    en = w.s([rv, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT(RP(j)), WG))
    return ccatg(w, ph, ENT(RP(j)), '( D ` J )', en, djw), rv


def pjcl(w, ph, u, j, djw):
    """( ph -> PJ(j) e. Stk ), with the inner closures"""
    lc, dr = lstcl(w, ph, u, j)
    inner = updcl(w, ph, 'D', 'K', LST(DROP('L', j), 'R'), u['tv'], u['dd'], u['kd'], u['gk'], lc)
    ec, rv = ejcl(w, ph, u, j, djw)
    outer = updcl(w, ph, UPDT('D', 'K', LST(DROP('L', j), 'R')), 'J', EJ(j), u['tv'], inner, u['jd'], u['gj'], ec)
    return outer, inner, lc, ec


def pval(w, ph, u, X, xfz, djw):
    """( ph -> ( PDEF ` X ) = PJ(X) )"""
    cg = w.s([], 'id', '( n = %s -> n = %s )' % (X, X))
    st, res = w.congr(PJ('n'), {'n': X}, 'n = %s' % X, {'n': cg})
    assert res == PJ(X), res
    eqi = w.s([], 'eqid', '%s = %s' % (PDEF, PDEF))
    cl, _, _, _ = pjcl(w, ph, u, X, djw)
    return w.s([eqi, st, xfz, cl], 'fvmptd3', '( %s -> ( %s ` %s ) = %s )' % (ph, PDEF, X, PJ(X)))


def tm2lmes():
    lab = 'tm2lmes'
    ph = PHS
    w = W(lab, 'The fragment ` moveEntries ` of TM/Lists.lean: every entry of the list on '
               'stack ` K ` is moved onto stack ` J ` (entries intact, order reversed, no '
               '` bra ` pushed) and the ` bra ` of ` K ` is popped; the scratch stack ` I ` is '
               'restored.  Lean: ` moveEntries_runs ` ; the loop is ~ tm2lfe with the body '
               '~ tm2lme and the invariant the explicit stack family ` P ` .')
    u = prelude(w, ph)
    tv, dd = u['tv'], u['dd']
    djw = stkfvg(w, ph, 'D', 'J', tv, dd, u['jd'], u['gj'])
    dkw = stkfvg(w, ph, 'D', 'K', tv, dd, u['kd'], u['gk'])
    # ---- the family: P : ( 0 ... NL ) --> Stk
    pn = '( %s /\\ n e. ( 0 ... %s ) )' % (ph, NL)
    def An(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pn, f))
    un = dict(u); un.update(tv=An(tv, 'T e. V'), dd=An(dd, 'D e. %s' % STK('T')), ll=An(u['ll'], 'L e. %s' % WWB),
              rr=An(u['rr'], 'R e. %s' % WG), kd=An(u['kd'], 'K e. %s' % DG), jd=An(u['jd'], 'J e. %s' % DG),
              gk=An(u['gk'], "%s = Gamma'" % GT('K')), gj=An(u['gj'], "%s = Gamma'" % GT('J')))
    djwn = An(djw, '( D ` J ) e. %s' % WG)
    pnc, _, _, _ = pjcl(w, pn, un, 'n', djwn)
    pty = w.s([pnc], 'fmptd', '( %s -> %s : ( 0 ... %s ) --> %s )' % (ph, PDEF, NL, STK('T')))
    pj = '( %s /\\ j e. ( 0 ... %s ) )' % (ph, NL)
    def Aj(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pj, f))
    uj = dict(u); uj.update(tv=Aj(tv, 'T e. V'), dd=Aj(dd, 'D e. %s' % STK('T')), ll=Aj(u['ll'], 'L e. %s' % WWB),
              rr=Aj(u['rr'], 'R e. %s' % WG), kd=Aj(u['kd'], 'K e. %s' % DG), jd=Aj(u['jd'], 'J e. %s' % DG),
              gk=Aj(u['gk'], "%s = Gamma'" % GT('K')), gj=Aj(u['gj'], "%s = Gamma'" % GT('J')))
    djwj = Aj(djw, '( D ` J ) e. %s' % WG)
    # ---- PK: ( ( P ` j ) ` K ) = LST( DROP j , R )
    jfz = w.s([], 'simpr', '( %s -> j e. ( 0 ... %s ) )' % (pj, NL))
    pvj = pval(w, pj, uj, 'j', jfz, djwj)
    _, innerj, lcj, ecj = pjcl(w, pj, uj, 'j', djwj)
    ecv = w.s([ecj], 'elexd', '( %s -> %s e. _V )' % (pj, EJ('j')))
    njk = Aj(w.s([u['nkj']], 'necomd', '( %s -> J =/= K )' % ph), 'J =/= K')
    nkj_j = Aj(u['nkj'], 'K =/= J')
    k1 = updn(w, pj, UPDT('D', 'K', LST(DROP('L', 'j'), 'R')), 'J', EJ('j'), 'K', uj['tv'], innerj, uj['jd'], ecv, uj['kd'], nkj_j)
    lcv = w.s([lcj], 'elexd', '( %s -> %s e. _V )' % (pj, LST(DROP('L', 'j'), 'R')))
    k2 = updk(w, pj, 'D', 'K', LST(DROP('L', 'j'), 'R'), uj['tv'], uj['dd'], uj['kd'], lcv)
    k3 = w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (pj, PJ('j'), LST(DROP('L', 'j'), 'R')))
    k4 = w.s([pvj], 'fveq1d', '( %s -> ( ( %s ` j ) ` K ) = ( %s ` K ) )' % (pj, PDEF, PJ('j')))
    k5 = w.s([k4, k3], 'eqtrd', '( %s -> ( ( %s ` j ) ` K ) = %s )' % (pj, PDEF, LST(DROP('L', 'j'), 'R')))
    PK = 'A. j e. ( 0 ... %s ) ( ( %s ` j ) ` K ) = %s' % (NL, PDEF, LST(DROP('L', 'j'), 'R'))
    pk = w.s([k5], 'ralrimiva', '( %s -> %s )' % (ph, PK))
    # ---- HB: the body at j e. ( 0 ..^ NL )
    po = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NL)
    def Ao(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (po, f))
    uo = dict(u)
    for key, f in (('tv', 'T e. V'), ('dd', 'D e. %s' % STK('T')), ('ll', 'L e. %s' % WWB), ('rr', 'R e. %s' % WG),
                   ('kd', 'K e. %s' % DG), ('jd', 'J e. %s' % DG), ('idd', 'I e. %s' % DG),
                   ('gk', "%s = Gamma'" % GT('K')), ('gj', "%s = Gamma'" % GT('J')), ('gi', "%s = Gamma'" % GT('I')),
                   ('phm', PHM), ('geq', '( 1st ` ( 1st ` T ) ) = TMGam'), ('nss', 'N C_ %s' % S('T')),
                   ('mif', MIFACE), ('f1', FT("F'")), ('c1', CT("C'")), ('pp', PTY), ('nkj', 'K =/= J'), ('nki', 'K =/= I'),
                   ('nji', 'J =/= I'), ('kk', 'K e. %s' % FZ8), ('jj', 'J e. %s' % FZ8), ('ii', 'I e. %s' % FZ8),
                   ('bb', 'B e. NN0'), ('bw', 'A. w e. ran L ( # ` w ) <_ B')):
        uo[key] = Ao(u[key], f)
    for nm in ["A'", "B'", 'B"', "Q'", 'A"']:
        uo['l_' + nm] = Ao(u['ls'][nm], '%s e. %s' % (nm, L('T')))
    for nm in ["A'", "B'", 'B"', "Q'"]:
        uo['m_' + nm] = Ao(u['ms'][nm], '( M ` %s ) = %s' % (nm, {
            "A'": PSH('I', '4', "B'"), "B'": MOVEP("B'", 'K', 'I', 'B"'), 'B"': PSH('J', '4', "Q'"), "Q'": MOVEP("Q'", 'I', 'J', 'A"')}[nm]))
    jo = w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (po, NL))
    jfzo = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> j e. ( 0 ... %s ) )' % (po, NL))
    j1fzo = w.s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( j + 1 ) e. ( 0 ... %s ) )' % (po, NL))
    djwo = Ao(djw, '( D ` J ) e. %s' % WG)
    pvo = pval(w, po, uo, 'j', jfzo, djwo)
    pvo1 = pval(w, po, uo, '( j + 1 )', j1fzo, djwo)
    pjco, innero, lco, eco = pjcl(w, po, uo, 'j', djwo)
    Pj = '( %s ` j )' % PDEF; Pj1 = '( %s ` ( j + 1 ) )' % PDEF
    pjstk = w.s([pvo, pjco], 'eqeltrd', '( %s -> %s e. %s )' % (po, Pj, STK('T')))
    # ( Pj ` K ) = ( ( L ` j ) ++ ( <" 4 "> ++ LST( DROP( j + 1 ) , R ) ) )
    pko = w.s([pk], 'adantr', '( %s -> %s )' % (po, PK))
    pkj = w.s([pko, jfzo, w.inst('rspa')], 'syl2anc', '( %s -> ( %s ` K ) = %s )' % (po, Pj, LST(DROP('L', 'j'), 'R')))
    LJ = '( L ` j )'; X1 = LST(DROP('L', '( j + 1 )'), 'R')
    ed = w.s([uo['ll'], jo, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, ENCB(DROP('L', 'j')), LJ, ENCB(DROP('L', '( j + 1 )'))))
    ed2 = w.s([ed], 'oveq1d', '( %s -> %s = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ R ) )' % (po, LST(DROP('L', 'j'), 'R'), LJ, ENCB(DROP('L', '( j + 1 )'))))
    lj = w.s([uo['ll'], jo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (po, LJ, WB))
    ljg = wbtog(w, po, LJ, lj)
    c4 = s1g(w, po, '4')
    dr1 = w.s([uo['ll'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (po, DROP('L', '( j + 1 )'), WWB))
    ec1 = w.s([dr1, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (po, ENCB(DROP('L', '( j + 1 )')), WG))
    c4e = ccatg(w, po, '<" 4 ">', ENCB(DROP('L', '( j + 1 )')), c4, ec1)
    as1 = w.s([ljg, c4e, uo['rr'], w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ R ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (po, LJ, ENCB(DROP('L', '( j + 1 )')), LJ, ENCB(DROP('L', '( j + 1 )'))))
    as2 = w.s([c4, ec1, uo['rr'], w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ R ) = ( <" 4 "> ++ %s ) )' % (po, ENCB(DROP('L', '( j + 1 )')), X1))
    as3 = w.s([as2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ R ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LJ, ENCB(DROP('L', '( j + 1 )')), LJ, X1))
    ed3 = w.s([ed2, as1], 'eqtrd', '( %s -> %s = ( %s ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (po, LST(DROP('L', 'j'), 'R'), LJ, ENCB(DROP('L', '( j + 1 )'))))
    ed4 = w.s([ed3, as3], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LST(DROP('L', 'j'), 'R'), LJ, X1))
    pkj2 = w.s([pkj, ed4], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, Pj, LJ, X1))
    x1cl, _ = lstcl(w, po, uo, '( j + 1 )')
    # tm2lme's antecedent at A := A', A' := B', A" := B", E' := Q', E := A", F := F', C := C', D := Pj, W := LJ, X := X1
    PROGe = ("( ( ( M ` A' ) = %s /\\ ( M ` B' ) = %s ) /\\ ( ( M ` B\" ) = %s /\\ ( M ` Q' ) = %s ) )"
             % (PSH('I', '4', "B'"), MOVEP("B'", 'K', 'I', 'B"'), PSH('J', '4', "Q'"), MOVEP("Q'", 'I', 'J', 'A"')))
    LABSe = "( ( A' e. %s /\\ B' e. %s /\\ B\" e. %s ) /\\ ( Q' e. %s /\\ A\" e. %s ) )" % ((L('T'),) * 5)
    HNDe = '( %s /\\ %s /\\ %s )' % (FT("F'"), CT("C'"), PTY)
    WXe = '( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, X1)
    a0 = w.s([uo['phm'], uo['geq']], 'jca', '( %s -> %s )' % (po, PHM6))
    pa = w.s([uo["m_A'"], uo["m_B'"]], 'jca', "( %s -> ( ( M ` A' ) = %s /\\ ( M ` B' ) = %s ) )" % (po, PSH('I', '4', "B'"), MOVEP("B'", 'K', 'I', 'B"')))
    pb = w.s([uo['m_B"'], uo["m_Q'"]], 'jca', "( %s -> ( ( M ` B\" ) = %s /\\ ( M ` Q' ) = %s ) )" % (po, PSH('J', '4', "Q'"), MOVEP("Q'", 'I', 'J', 'A"')))
    pab = w.s([pa, pb], 'jca', '( %s -> %s )' % (po, PROGe))
    a1 = w.s([a0, pab], 'jca', '( %s -> ( %s /\\ %s ) )' % (po, PHM6, PROGe))
    la = w.s([uo["l_A'"], uo["l_B'"], uo['l_B"']], '3jca', "( %s -> ( A' e. %s /\\ B' e. %s /\\ B\" e. %s ) )" % (po, L('T'), L('T'), L('T')))
    lb = w.s([uo["l_Q'"], uo['l_A"']], 'jca', "( %s -> ( Q' e. %s /\\ A\" e. %s ) )" % (po, L('T'), L('T')))
    labe = w.s([la, lb], 'jca', '( %s -> %s )' % (po, LABSe))
    i3 = w.s([uo['kk'], uo['jj'], uo['ii']], '3jca', '( %s -> ( K e. %s /\\ J e. %s /\\ I e. %s ) )' % (po, FZ8, FZ8, FZ8))
    n3 = w.s([uo['nkj'], uo['nki'], uo['nji']], '3jca', '( %s -> ( K =/= J /\\ K =/= I /\\ J =/= I ) )' % po)
    idxe = w.s([i3, n3], 'jca', '( %s -> %s )' % (po, IDX))
    hnde = w.s([uo['f1'], uo['c1'], uo['pp']], '3jca', '( %s -> %s )' % (po, HNDe))
    a2 = w.s([labe, idxe, hnde], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (po, LABSe, IDX, HNDe))
    nm = w.s([uo['nss'], uo['mif']], 'jca', '( %s -> ( N C_ %s /\\ %s ) )' % (po, S('T'), MIFACE))
    dpk = w.s([pjstk, pkj2], 'jca', '( %s -> ( %s e. %s /\\ ( %s ` K ) = %s ) )' % (po, Pj, STK('T'), Pj, WXe))
    wx = w.s([lj, x1cl], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (po, LJ, WB, X1, WG))
    a3 = w.s([nm, dpk, wx], '3jca', '( %s -> ( ( N C_ %s /\\ %s ) /\\ ( %s e. %s /\\ ( %s ` K ) = %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) )' % (po, S('T'), MIFACE, Pj, STK('T'), Pj, WXe, LJ, WB, X1, WG))
    ant = w.s([a1, a2, a3], '3jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) /\\ ( ( N C_ %s /\\ %s ) /\\ ( %s e. %s /\\ ( %s ` K ) = %s ) /\\ ( %s e. %s /\\ %s e. %s ) ) ) )'
              % (po, PHM6, PROGe, LABSe, IDX, HNDe, S('T'), MIFACE, Pj, STK('T'), Pj, WXe, LJ, WB, X1, WG))
    POSTe = UPDT(UPDT(Pj, 'K', X1), 'J', '( %s ++ ( <" 4 "> ++ ( %s ` J ) ) )' % (LJ, Pj))
    BND = '( ( 2 x. ( # ` %s ) ) + 4 )' % LJ
    tri = w.s([ant, w.inst('tm2lme')], 'syl', '( %s -> %s )' % (po, HR(CL("A'", 'N', Pj), 'T', 'M', CL('A"', 'N', POSTe), BND)))
    # POSTe = Pj1
    st1, r1 = w.rewrite(POSTe, {Pj: (PJ('j'), pvo)}, po)
    POST2 = UPDT(UPDT(PJ('j'), 'K', X1), 'J', '( %s ++ ( <" 4 "> ++ ( %s ` J ) ) )' % (LJ, PJ('j')))
    assert r1 == POST2, r1
    ecvo = w.s([eco], 'elexd', '( %s -> %s e. _V )' % (po, EJ('j')))
    kv = updk(w, po, UPDT('D', 'K', LST(DROP('L', 'j'), 'R')), 'J', EJ('j'), uo['tv'], innero, uo['jd'], ecvo)
    kv2 = w.s([kv], 'oveq2d', '( %s -> ( <" 4 "> ++ ( %s ` J ) ) = ( <" 4 "> ++ %s ) )' % (po, PJ('j'), EJ('j')))
    kv3 = w.s([kv2], 'oveq2d', '( %s -> ( %s ++ ( <" 4 "> ++ ( %s ` J ) ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LJ, PJ('j'), LJ, EJ('j')))
    # ( LJ ++ ( <" 4 "> ++ EJ(j) ) ) = EJ( j + 1 )
    ps1 = w.s([uo['ll'], jo, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (po, PFX('L', '( j + 1 )'), PFX('L', 'j'), LJ))
    rv1 = w.s([ps1], 'fveq2d', '( %s -> %s = ( reverse ` ( %s ++ <" %s "> ) ) )' % (po, RP('( j + 1 )'), PFX('L', 'j'), LJ))
    pfc = w.s([uo['ll'], w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (po, PFX('L', 'j'), WWB))
    ljs = w.s([lj], 's1cld', '( %s -> <" %s "> e. %s )' % (po, LJ, WWB))
    rc = w.s([pfc, ljs, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ %s ) )' % (po, PFX('L', 'j'), LJ, LJ, RP('j')))
    rs = w.s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (LJ, LJ))
    rs2 = w.s([rs], 'oveq1i', '( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s )' % (LJ, RP('j'), LJ, RP('j')))
    rs2a = w.s([rs2], 'a1i', '( %s -> ( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (po, LJ, RP('j'), LJ, RP('j')))
    rv2 = w.s([rv1, rc], 'eqtrd', '( %s -> %s = ( ( reverse ` <" %s "> ) ++ %s ) )' % (po, RP('( j + 1 )'), LJ, RP('j')))
    rv3 = w.s([rv2, rs2a], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (po, RP('( j + 1 )'), LJ, RP('j')))
    en1 = w.s([rv3], 'fveq2d', '( %s -> %s = %s )' % (po, ENT(RP('( j + 1 )')), ENT('( <" %s "> ++ %s )' % (LJ, RP('j')))))
    rpc = w.s([pfc, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (po, RP('j'), WWB))
    en2 = w.s([lj, rpc, w.inst('tm2lentcons')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, ENT('( <" %s "> ++ %s )' % (LJ, RP('j'))), LJ, ENT(RP('j'))))
    en3 = w.s([en1, en2], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, ENT(RP('( j + 1 )')), LJ, ENT(RP('j'))))
    en4 = w.s([en3], 'oveq1d', '( %s -> %s = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ ( D ` J ) ) )' % (po, EJ('( j + 1 )'), LJ, ENT(RP('j'))))
    enc = w.s([rpc, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (po, ENT(RP('j')), WG))
    c4en = ccatg(w, po, '<" 4 ">', ENT(RP('j')), c4, enc)
    b1 = w.s([ljg, c4en, djwo, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ ( D ` J ) ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` J ) ) ) )' % (po, LJ, ENT(RP('j')), LJ, ENT(RP('j'))))
    b2 = w.s([c4, enc, djwo, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` J ) ) = ( <" 4 "> ++ %s ) )' % (po, ENT(RP('j')), EJ('j')))
    b3 = w.s([b2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` J ) ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LJ, ENT(RP('j')), LJ, EJ('j')))
    b4 = w.s([en4, b1], 'eqtrd', '( %s -> %s = ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` J ) ) ) )' % (po, EJ('( j + 1 )'), LJ, ENT(RP('j'))))
    b5 = w.s([b4, b3], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, EJ('( j + 1 )'), LJ, EJ('j')))
    kv4 = w.s([kv3, b5], 'eqtr4d', '( %s -> ( %s ++ ( <" 4 "> ++ ( %s ` J ) ) ) = %s )' % (po, LJ, PJ('j'), EJ('( j + 1 )')))
    st2, r2 = w.rewrite(POST2, {'( %s ++ ( <" 4 "> ++ ( %s ` J ) ) )' % (LJ, PJ('j')): (EJ('( j + 1 )'), kv4)}, po)
    POST3 = UPDT(UPDT(PJ('j'), 'K', X1), 'J', EJ('( j + 1 )'))
    assert r2 == POST3, r2
    # tm2stkup4 collapse
    ec1o, _ = ejcl(w, po, uo, '( j + 1 )', djwo)
    lcjk = wgk(w, po, LST(DROP('L', 'j'), 'R'), 'K', uo['gk'], lco)
    x1k = wgk(w, po, X1, 'K', uo['gk'], x1cl)
    ejj = wgk(w, po, EJ('j'), 'J', uo['gj'], eco)
    ej1j = wgk(w, po, EJ('( j + 1 )'), 'J', uo['gj'], ec1o)
    u4a = w.s([w.s([uo['tv'], uo['dd']], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (po, STK('T'))), uo['nkj']], 'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (po, STK('T')))
    u4b = w.s([uo['kd'], w.s([lcjk, x1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, LST(DROP('L', 'j'), 'R'), GT('K'), X1, GT('K')))], 'jca',
               '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (po, DG, LST(DROP('L', 'j'), 'R'), GT('K'), X1, GT('K')))
    u4c = w.s([uo['jd'], w.s([ejj, ej1j], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, EJ('j'), GT('J'), EJ('( j + 1 )'), GT('J')))], 'jca',
               '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (po, DG, EJ('j'), GT('J'), EJ('( j + 1 )'), GT('J')))
    up4 = w.s([u4a, u4b, u4c, w.inst('tm2stkup4')], 'syl3anc', '( %s -> %s = %s )' % (po, POST3, PJ('( j + 1 )')))
    st3 = w.s([st1, st2], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST3))
    st4 = w.s([st3, up4], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, PJ('( j + 1 )')))
    pvo1r = w.s([pvo1], 'eqcomd', '( %s -> %s = %s )' % (po, PJ('( j + 1 )'), Pj1))
    st5 = w.s([st4, pvo1r], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, Pj1))
    tri2 = hrtransport(w, po, tri, CL("A'", 'N', Pj), CL('A"', 'N', POSTe), BND, None, CL('A"', 'N', Pj1), eqd=cleq(w, po, 'A"', 'N', POSTe, Pj1, st5))
    # raise the bound to YB
    lfn = w.s([uo['ll'], w.inst('wrdfn')], 'syl', '( %s -> L Fn ( 0 ..^ %s ) )' % (po, NL))
    ljr = w.s([lfn, jo, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran L )' % (po, LJ))
    cgw, neww = w.wcongr('( # ` w ) <_ B', {'w': LJ}, 'w = %s' % LJ, {'w': w.s([], 'id', '( w = %s -> w = %s )' % (LJ, LJ))})
    lb = w.s([cgw, uo['bw'], ljr], 'rspcdva', '( %s -> ( # ` %s ) <_ B )' % (po, LJ))
    ln = w.s([lj, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (po, LJ))
    lnr = w.s([ln], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (po, LJ))
    br = w.s([uo['bb']], 'nn0red', '( %s -> B e. RR )' % po)
    le = linarith(w, po, [lb], '%s <_ %s' % (BND, YB), leaves={'( # ` %s )' % LJ: lnr, 'B': br})
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % po)
    four = w.s([], '4nn0', '4 e. NN0'); foura = w.s([four], 'a1i', '( %s -> 4 e. NN0 )' % po)
    tb = w.s([twoa, uo['bb']], 'nn0mulcld', '( %s -> ( 2 x. B ) e. NN0 )' % po)
    yb = w.s([tb, foura], 'nn0addcld', '( %s -> %s e. NN0 )' % (po, YB))
    tri3 = hle(w, po, uo['phm'], CL("A'", 'N', Pj), CL('A"', 'N', Pj1), BND, YB, tri2, yb, le)
    HBF = HR(CL("A'", 'N', Pj), 'T', 'M', CL('A"', 'N', Pj1), YB)
    HB = 'A. j e. ( 0 ..^ %s ) %s' % (NL, HBF)
    hb = w.s([tri3], 'ralrimiva', '( %s -> %s )' % (ph, HB))
    # ---- tm2lfe's antecedent (with P := PDEF, Y := YB, E := E')
    PROGf = '( ( M ` P1 ) = %s /\\ ( M ` A ) = %s /\\ ( M ` A" ) = %s )' % (PEEKS, TESTS, PEEKS)
    LAB1 = "( P1 e. %s /\\ A e. %s /\\ A' e. %s )" % (L('T'), L('T'), L('T'))
    LAB2 = "( A\" e. %s /\\ E' e. %s /\\ K e. %s )" % (L('T'), L('T'), FZ8)
    PTYf = '%s : ( 0 ... %s ) --> %s' % (PDEF, NL, STK('T'))
    f0 = w.s([u['phm'], u['geq']], 'jca', '( %s -> %s )' % (ph, PHM6))
    fp = w.s([u['ms']['P1'], u['ms']['A'], u['ms']['A"']], '3jca', '( %s -> %s )' % (ph, PROGf))
    f1 = w.s([f0, fp], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, PHM6, PROGf))
    l1 = w.s([u['ls']['P1'], u['ls']['A'], u['ls']["A'"]], '3jca', '( %s -> %s )' % (ph, LAB1))
    l2 = w.s([u['ls']['A"'], u['ls']["E'"], u['kk']], '3jca', '( %s -> %s )' % (ph, LAB2))
    l12 = w.s([l1, l2], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, LAB1, LAB2))
    fc = w.s([u['ff'], u['cc']], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FT('F'), CT('C')))
    ni = w.s([u['nss'], u['iface']], 'jca', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), IFACE))
    f2 = w.s([l12, fc, ni], '3jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( N C_ %s /\\ %s ) ) )' % (ph, LAB1, LAB2, FT('F'), CT('C'), S('T'), IFACE))
    two2 = w.s([], '2nn0', '2 e. NN0'); two2a = w.s([two2], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    four2 = w.s([], '4nn0', '4 e. NN0'); four2a = w.s([four2], 'a1i', '( %s -> 4 e. NN0 )' % ph)
    tb2 = w.s([two2a, u['bb']], 'nn0mulcld', '( %s -> ( 2 x. B ) e. NN0 )' % ph)
    yb2 = w.s([tb2, four2a], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, YB))
    lry = w.s([u['ll'], u['rr'], yb2], '3jca', '( %s -> ( L e. %s /\\ R e. %s /\\ %s e. NN0 ) )' % (ph, WWB, WG, YB))
    ppk = w.s([pty, pk], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, PTYf, PK))
    f3 = w.s([lry, ppk, hb], '3jca', '( %s -> ( ( L e. %s /\\ R e. %s /\\ %s e. NN0 ) /\\ ( %s /\\ %s ) /\\ %s ) )' % (ph, WWB, WG, YB, PTYf, PK, HB))
    fant = w.s([f1, f2, f3], '3jca', '( %s -> ( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( N C_ %s /\\ %s ) ) /\\ ( ( L e. %s /\\ R e. %s /\\ %s e. NN0 ) /\\ ( %s /\\ %s ) /\\ %s ) ) )'
              % (ph, PHM6, PROGf, LAB1, LAB2, FT('F'), CT('C'), S('T'), IFACE, WWB, WG, YB, PTYf, PK, HB))
    P0 = '( %s ` 0 )' % PDEF; PN = '( %s ` %s )' % (PDEF, NL)
    FB = '( ( %s x. ( %s + 2 ) ) + 2 )' % (NL, YB)
    loop = w.s([fant, w.inst('tm2lfe')], 'syl', '( %s -> %s )' % (ph, HR(CL('P1', 'N', P0), 'T', 'M', CL("E'", NFIN, PN), FB)))
    # ---- ( P ` 0 ) = D and ( P ` NL ) = PNL
    z0fz = w.s([u['nl'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NL))
    pv0 = pval(w, ph, u, '0', z0fz, djw)
    d0 = w.s([u['ll'], w.inst('tm2ldrop0')], 'syl', '( %s -> %s = L )' % (ph, DROP('L', '0')))
    d0b = w.s([d0], 'fveq2d', '( %s -> %s = %s )' % (ph, ENCB(DROP('L', '0')), ENCB('L')))
    d0c = w.s([d0b], 'oveq1d', '( %s -> %s = %s )' % (ph, LST(DROP('L', '0'), 'R'), LST('L', 'R')))
    d0d = w.s([d0c, u['dk']], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (ph, LST(DROP('L', '0'), 'R')))
    p00 = w.s([], 'pfx00', '%s = (/)' % PFX('L', '0'))
    p01 = w.s([p00], 'fveq2i', '%s = ( reverse ` (/) )' % RP('0'))
    r0 = w.s([], 'rev0', '( reverse ` (/) ) = (/)')
    p02 = w.s([p01, r0], 'eqtri', '%s = (/)' % RP('0'))
    p03 = w.s([p02], 'fveq2i', '%s = %s' % (ENT(RP('0')), ENT('(/)')))
    e0 = w.s([], 'tm2lent0', '%s = (/)' % ENT('(/)'))
    p04 = w.s([p03, e0], 'eqtri', '%s = (/)' % ENT(RP('0')))
    p05 = w.s([p04], 'oveq1i', '%s = ( (/) ++ ( D ` J ) )' % EJ('0'))
    p05a = w.s([p05], 'a1i', '( %s -> %s = ( (/) ++ ( D ` J ) ) )' % (ph, EJ('0')))
    lid = w.s([djw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( D ` J ) ) = ( D ` J ) )' % ph)
    p06 = w.s([p05a, lid], 'eqtrd', '( %s -> %s = ( D ` J ) )' % (ph, EJ('0')))
    st0, r0x = w.rewrite(PJ('0'), {LST(DROP('L', '0'), 'R'): ('( D ` K )', d0d), EJ('0'): ('( D ` J )', p06)}, ph)
    PJ0 = UPDT(UPDT('D', 'K', '( D ` K )'), 'J', '( D ` J )')
    assert r0x == PJ0, r0x
    upk = w.s([tv, dd, u['kd'], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = D )' % (ph, UPDT('D', 'K', '( D ` K )')))
    r1s = w.s([upk], 'reseq1d', '( %s -> ( %s |` ( %s \\ { J } ) ) = ( D |` ( %s \\ { J } ) ) )' % (ph, UPDT('D', 'K', '( D ` K )'), DG, DG))
    r2s = w.s([r1s], 'uneq1d', '( %s -> %s = %s )' % (ph, PJ0, UPDT('D', 'J', '( D ` J )')))
    upj = w.s([tv, dd, u['jd'], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = D )' % (ph, UPDT('D', 'J', '( D ` J )')))
    pd1 = w.s([pv0, st0], 'eqtrd', '( %s -> %s = %s )' % (ph, P0, PJ0))
    pd2 = w.s([pd1, r2s], 'eqtrd', '( %s -> %s = %s )' % (ph, P0, UPDT('D', 'J', '( D ` J )')))
    pd = w.s([pd2, upj], 'eqtrd', '( %s -> %s = D )' % (ph, P0))
    nlfz = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    pvn = pval(w, ph, u, NL, nlfz, djw)
    s00 = w.s([], 'swrd00', '%s = (/)' % DROP('L', NL))
    s01 = w.s([s00], 'fveq2i', '%s = %s' % (ENCB(DROP('L', NL)), ENCB('(/)')))
    eb0 = w.s([], 'tm2lencb0', '%s = <" 2 ">' % ENCB('(/)'))
    s02 = w.s([s01, eb0], 'eqtri', '%s = <" 2 ">' % ENCB(DROP('L', NL)))
    s03 = w.s([s02], 'oveq1i', '%s = ( <" 2 "> ++ R )' % LST(DROP('L', NL), 'R'))
    s03a = w.s([s03], 'a1i', '( %s -> %s = ( <" 2 "> ++ R ) )' % (ph, LST(DROP('L', NL), 'R')))
    pid = w.s([u['ll'], w.inst('pfxid')], 'syl', '( %s -> %s = L )' % (ph, PFX('L', NL)))
    pid2 = w.s([pid], 'fveq2d', '( %s -> %s = ( reverse ` L ) )' % (ph, RP(NL)))
    pid3 = w.s([pid2], 'fveq2d', '( %s -> %s = %s )' % (ph, ENT(RP(NL)), ENT('( reverse ` L )')))
    pid4 = w.s([pid3], 'oveq1d', '( %s -> %s = ( %s ++ ( D ` J ) ) )' % (ph, EJ(NL), ENT('( reverse ` L )')))
    stn, rn = w.rewrite(PJ(NL), {LST(DROP('L', NL), 'R'): ('( <" 2 "> ++ R )', s03a), EJ(NL): ('( %s ++ ( D ` J ) )' % ENT('( reverse ` L )'), pid4)}, ph)
    ERL = '( %s ++ ( D ` J ) )' % ENT('( reverse ` L )')
    PNL = UPDT(UPDT('D', 'K', '( <" 2 "> ++ R )'), 'J', ERL)
    assert rn == PNL, rn
    pvn2 = w.s([pvn, stn], 'eqtrd', '( %s -> %s = %s )' % (ph, PN, PNL))
    loop2 = hrtransport(w, ph, loop, CL('P1', 'N', P0), CL("E'", NFIN, PN), FB, CL('P1', 'N', 'D'), CL("E'", NFIN, PNL),
                        eqc=cleq(w, ph, 'P1', 'N', P0, 'D', pd), eqd=cleq(w, ph, "E'", NFIN, PN, PNL, pvn2))
    # ---- popTop on PNL
    c2 = s1g(w, ph, '2')
    tr = ccatg(w, ph, '<" 2 ">', 'R', c2, u['rr'])
    inn = updcl(w, ph, 'D', 'K', '( <" 2 "> ++ R )', tv, dd, u['kd'], u['gk'], tr)
    rvl = w.s([u['ll'], w.inst('revcl')], 'syl', '( %s -> ( reverse ` L ) e. %s )' % (ph, WWB))
    erc = w.s([rvl, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT('( reverse ` L )'), WG))
    erl = ccatg(w, ph, ENT('( reverse ` L )'), '( D ` J )', erc, djw)
    pnlcl = updcl(w, ph, UPDT('D', 'K', '( <" 2 "> ++ R )'), 'J', ERL, tv, inn, u['jd'], u['gj'], erl)
    erlv = w.s([erl], 'elexd', '( %s -> %s e. _V )' % (ph, ERL))
    trv = w.s([tr], 'elexd', '( %s -> ( <" 2 "> ++ R ) e. _V )' % ph)
    njk2 = w.s([u['nkj']], 'necomd', '( %s -> J =/= K )' % ph)
    q1 = updn(w, ph, UPDT('D', 'K', '( <" 2 "> ++ R )'), 'J', ERL, 'K', tv, inn, u['jd'], erlv, u['kd'], u['nkj'])
    q2 = updk(w, ph, 'D', 'K', '( <" 2 "> ++ R )', tv, dd, u['kd'], trv)
    q3 = w.s([q1, q2], 'eqtrd', '( %s -> ( %s ` K ) = ( <" 2 "> ++ R ) )' % (ph, PNL))
    nfs = w.s([], 'ssrab2', '%s C_ N' % NFIN); nfsa = w.s([nfs], 'a1i', '( %s -> %s C_ N )' % (ph, NFIN))
    nfss = w.s([nfsa, u['nss']], 'sstrd', '( %s -> %s C_ %s )' % (ph, NFIN, S('T')))
    hpi = w.inst('ssralv')
    hp = w.s([nfsa, hpi], 'syl', "( %s -> ( %s -> A. r e. %s %s e. N' ) )" % (ph, HPOP, NFIN, NVF('F"', 'r', '2')))
    hp2 = w.s([hp, u['hpop']], 'mpd', "( %s -> A. r e. %s %s e. N' )" % (ph, NFIN, NVF('F"', 'r', '2')))
    a0 = w.s([u['phm'], u['geq']], 'jca', '( %s -> %s )' % (ph, PHM6))
    pa1 = w.s([a0, u['ms']["E'"]], 'jca', "( %s -> ( %s /\\ ( M ` E' ) = %s ) )" % (ph, PHM6, POPL('K', 'F"', 'E')))
    pl = w.s([u['ls']["E'"], u['ls']['E'], u['kk']], '3jca', "( %s -> ( E' e. %s /\\ E e. %s /\\ K e. %s ) )" % (ph, L('T'), L('T'), FZ8))
    pf = w.s([u['f2'], pnlcl], 'jca', '( %s -> ( %s /\\ %s e. %s ) )' % (ph, FT('F"'), PNL, STK('T')))
    pa2 = w.s([pl, pf], 'jca', "( %s -> ( ( E' e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s e. %s ) ) )" % (ph, L('T'), L('T'), FZ8, FT('F"'), PNL, STK('T')))
    g2 = gamlet(w, ph, '2')
    HDK = "( ( %s ` K ) = ( <\" 2 \"> ++ R ) /\\ 2 e. Gamma' /\\ R e. %s )" % (PNL, WG)
    hdk = w.s([q3, g2, u['rr']], '3jca', '( %s -> %s )' % (ph, HDK))
    nn2 = w.s([nfss, u['n2ss']], 'jca', "( %s -> ( %s C_ %s /\\ N' C_ %s ) )" % (ph, NFIN, S('T'), S('T')))
    pa3 = w.s([hdk, nn2, hp2], '3jca', "( %s -> ( %s /\\ ( %s C_ %s /\\ N' C_ %s ) /\\ A. r e. %s %s e. N' ) )" % (ph, HDK, NFIN, S('T'), S('T'), NFIN, NVF('F"', 'r', '2')))
    pant = w.s([pa1, pa2, pa3], '3jca', "( %s -> ( ( %s /\\ ( M ` E' ) = %s ) /\\ ( ( E' e. %s /\\ E e. %s /\\ K e. %s ) /\\ ( %s /\\ %s e. %s ) ) /\\ ( %s /\\ ( %s C_ %s /\\ N' C_ %s ) /\\ A. r e. %s %s e. N' ) ) )"
               % (ph, PHM6, POPL('K', 'F"', 'E'), L('T'), L('T'), FZ8, FT('F"'), PNL, STK('T'), HDK, NFIN, S('T'), S('T'), NFIN, NVF('F"', 'r', '2')))
    POP = UPDT(PNL, 'K', 'R')
    pop = w.s([pant, w.inst('tm2lpop')], 'syl', '( %s -> %s )' % (ph, HR(CL("E'", NFIN, PNL), 'T', 'M', CL('E', "N'", POP), '1')))
    # collapse by tm2stkup3
    trk = wgk(w, ph, '( <" 2 "> ++ R )', 'K', u['gk'], tr)
    rk = wgk(w, ph, 'R', 'K', u['gk'], u['rr'])
    erj = wgk(w, ph, ERL, 'J', u['gj'], erl)
    u3a = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK('T'))), u['nkj']], 'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (ph, STK('T')))
    u3b = w.s([u['kd'], w.s([trk, rk], 'jca', '( %s -> ( ( <" 2 "> ++ R ) e. Word %s /\\ R e. Word %s ) )' % (ph, GT('K'), GT('K')))], 'jca',
               '( %s -> ( K e. %s /\\ ( ( <" 2 "> ++ R ) e. Word %s /\\ R e. Word %s ) ) )' % (ph, DG, GT('K'), GT('K')))
    u3c = w.s([u['jd'], erj], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, ERL, GT('J')))
    up3 = w.s([u3a, u3b, u3c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (ph, POP, DFIN))
    pop2 = hrtransport(w, ph, pop, CL("E'", NFIN, PNL), CL('E', "N'", POP), '1', None, CL('E', "N'", DFIN), eqd=cleq(w, ph, 'E', "N'", POP, DFIN, up3))
    # ---- the chain and the bound
    C0 = CL('P1', 'N', 'D'); C2c = CL("E'", NFIN, PNL); C3 = CL('E', "N'", DFIN)
    q = hseq(w, ph, u['phm'], C0, C2c, C3, FB, '1', loop2, pop2)
    TOT = '( %s + 1 )' % FB
    GOAL = '( ( %s x. ( ( 2 x. B ) + 6 ) ) + 3 )' % NL
    br2 = w.s([u['bb']], 'nn0red', '( %s -> B e. RR )' % ph)
    i1 = lineq(w, ph, '( %s + 2 )' % YB, '( ( 2 x. B ) + 6 )', leaves={'B': br2})
    i2 = w.s([i1], 'oveq2d', '( %s -> ( %s x. ( %s + 2 ) ) = ( %s x. ( ( 2 x. B ) + 6 ) ) )' % (ph, NL, YB, NL))
    nlr = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    s6 = w.s([], '6re', '6 e. RR'); s6a = w.s([s6], 'a1i', '( %s -> 6 e. RR )' % ph)
    two3 = w.s([], '2re', '2 e. RR'); two3a = w.s([two3], 'a1i', '( %s -> 2 e. RR )' % ph)
    tb3 = w.s([two3a, br2], 'remulcld', '( %s -> ( 2 x. B ) e. RR )' % ph)
    b6 = w.s([tb3, s6a], 'readdcld', '( %s -> ( ( 2 x. B ) + 6 ) e. RR )' % ph)
    prr = w.s([nlr, b6], 'remulcld', '( %s -> ( %s x. ( ( 2 x. B ) + 6 ) ) e. RR )' % (ph, NL))
    i3 = lineq(w, ph, TOT, GOAL, hyps=[i2], leaves={'( %s x. ( %s + 2 ) )' % (NL, YB): w.s([i2, prr], 'eqeltrd', '( %s -> ( %s x. ( %s + 2 ) ) e. RR )' % (ph, NL, YB)),
                                                     '( %s x. ( ( 2 x. B ) + 6 ) )' % NL: prr},
               atoms=['( %s x. ( %s + 2 ) )' % (NL, YB), '( %s x. ( ( 2 x. B ) + 6 ) )' % NL])
    o = w.s([i3], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C3, TOT, C3, GOAL))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C3, TOT), HR(C0, 'T', 'M', C3, GOAL)))
    w.qed([b, q], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C3, GOAL)))
    return w.run()


if __name__ == '__main__':
    if want('tm2lmes'): tm2lmes()
