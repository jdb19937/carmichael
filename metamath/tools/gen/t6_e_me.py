"""T6: `moveEntry` (blueprint 3.4): push a comma on the scratch stack, move
the number onto it, push a comma on the destination, move it back --- four
`tm2hseq` stages over ~ tm2fpshn and ~ tm2fmvn , with the stack algebra
between them."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6lib import *
from lin import lineq

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

FTY = "F e. ( %s ^m ( %s X. %s ) )" % (S('T'), S('T'), OPT)
CTY = 'C e. ( 2o ^m %s )' % S('T')
PTY = "P e. ( Gamma' ^m %s )" % S('T')
def NVR(r, z): return NV('F', r, z)
MI1 = 'A. r e. N A. z e. %s ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. N )' % (BITS, NVR('r', 'z'), NVR('r', 'z'), NVR('r', 'z'))
MI2 = 'A. r e. N ( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NVR('r', '4'), NVR('r', '4'))
MIFACE = '( %s /\\ %s )' % (MI1, MI2)
PROG = ("( ( ( M ` A ) = %s /\\ ( M ` A' ) = %s ) /\\ ( ( M ` A\" ) = %s /\\ ( M ` E' ) = %s ) )"
        % (PSH('I', '4', "A'"), MOVE("A'", 'K', 'I', 'A"'), PSH('J', '4', "E'"), MOVE("E'", 'I', 'J', 'E')))
LABS = "( ( A e. %s /\\ A' e. %s /\\ A\" e. %s ) /\\ ( E' e. %s /\\ E e. %s ) )" % ((L('T'),) * 5)
IDX = '( ( K e. %s /\\ J e. %s /\\ I e. %s ) /\\ ( K =/= J /\\ K =/= I /\\ J =/= I ) )' % (FZ8, FZ8, FZ8)
HND = '( %s /\\ %s /\\ %s )' % (FTY, CTY, PTY)
WX = '( W ++ ( <" 4 "> ++ X ) )'
PHE = ('( ( %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) /\\ ( ( N C_ %s /\\ %s ) /\\ ( D e. %s /\\ ( D ` K ) = %s ) /\\ ( W e. %s /\\ X e. %s ) ) )'
       % (PHM6, PROG, LABS, IDX, HND, S('T'), MIFACE, STK('T'), WX, WB, WG))
DFIN = UPDT(UPDT('D', 'K', 'X'), 'J', '( W ++ ( <" 4 "> ++ ( D ` J ) ) )')


def prelude(w, ph):
    p1 = w.s([], 'simp1', '( %s -> ( %s /\\ %s ) )' % (ph, PHM6, PROG))
    p6 = w.s([p1], 'simpld', '( %s -> %s )' % (ph, PHM6))
    phm = w.s([p6], 'simpld', '( %s -> %s )' % (ph, PHM))
    geq = w.s([p6], 'simprd', '( %s -> ( 1st ` ( 1st ` T ) ) = TMGam )' % ph)
    prog = w.s([p1], 'simprd', '( %s -> %s )' % (ph, PROG))
    pr1 = w.s([prog], 'simpld', "( %s -> ( ( M ` A ) = %s /\\ ( M ` A' ) = %s ) )" % (ph, PSH('I', '4', "A'"), MOVE("A'", 'K', 'I', 'A"')))
    pr2 = w.s([prog], 'simprd', "( %s -> ( ( M ` A\" ) = %s /\\ ( M ` E' ) = %s ) )" % (ph, PSH('J', '4', "E'"), MOVE("E'", 'I', 'J', 'E')))
    m1 = w.s([pr1], 'simpld', '( %s -> ( M ` A ) = %s )' % (ph, PSH('I', '4', "A'")))
    m2 = w.s([pr1], 'simprd', "( %s -> ( M ` A' ) = %s )" % (ph, MOVE("A'", 'K', 'I', 'A"')))
    m3 = w.s([pr2], 'simpld', '( %s -> ( M ` A" ) = %s )' % (ph, PSH('J', '4', "E'")))
    m4 = w.s([pr2], 'simprd', "( %s -> ( M ` E' ) = %s )" % (ph, MOVE("E'", 'I', 'J', 'E')))
    p2 = w.s([], 'simp2', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, LABS, IDX, HND))
    labs = w.s([p2, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, LABS))
    l3 = w.s([labs], 'simpld', "( %s -> ( A e. %s /\\ A' e. %s /\\ A\" e. %s ) )" % (ph, L('T'), L('T'), L('T')))
    l2 = w.s([labs], 'simprd', "( %s -> ( E' e. %s /\\ E e. %s ) )" % (ph, L('T'), L('T')))
    al = w.s([l3, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    a1l = w.s([l3, w.inst('simp2')], 'syl', "( %s -> A' e. %s )" % (ph, L('T')))
    a2l = w.s([l3, w.inst('simp3')], 'syl', '( %s -> A" e. %s )' % (ph, L('T')))
    e1l = w.s([l2], 'simpld', "( %s -> E' e. %s )" % (ph, L('T')))
    el = w.s([l2], 'simprd', '( %s -> E e. %s )' % (ph, L('T')))
    idx = w.s([p2, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, IDX))
    i3 = w.s([idx], 'simpld', '( %s -> ( K e. %s /\\ J e. %s /\\ I e. %s ) )' % (ph, FZ8, FZ8, FZ8))
    n3 = w.s([idx], 'simprd', '( %s -> ( K =/= J /\\ K =/= I /\\ J =/= I ) )' % ph)
    kk = w.s([i3, w.inst('simp1')], 'syl', '( %s -> K e. %s )' % (ph, FZ8))
    jj = w.s([i3, w.inst('simp2')], 'syl', '( %s -> J e. %s )' % (ph, FZ8))
    ii = w.s([i3, w.inst('simp3')], 'syl', '( %s -> I e. %s )' % (ph, FZ8))
    nkj = w.s([n3, w.inst('simp1')], 'syl', '( %s -> K =/= J )' % ph)
    nki = w.s([n3, w.inst('simp2')], 'syl', '( %s -> K =/= I )' % ph)
    nji = w.s([n3, w.inst('simp3')], 'syl', '( %s -> J =/= I )' % ph)
    hnd = w.s([p2, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HND))
    ff = w.s([hnd, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, FTY))
    cc = w.s([hnd, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, CTY))
    pp = w.s([hnd, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, PTY))
    p3 = w.s([], 'simp3', '( %s -> ( ( N C_ %s /\\ %s ) /\\ ( D e. %s /\\ ( D ` K ) = %s ) /\\ ( W e. %s /\\ X e. %s ) ) )' % (ph, S('T'), MIFACE, STK('T'), WX, WB, WG))
    ni = w.s([p3, w.inst('simp1')], 'syl', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), MIFACE))
    nss = w.s([ni], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    mif = w.s([ni], 'simprd', '( %s -> %s )' % (ph, MIFACE))
    dk2 = w.s([p3, w.inst('simp2')], 'syl', '( %s -> ( D e. %s /\\ ( D ` K ) = %s ) )' % (ph, STK('T'), WX))
    dd = w.s([dk2], 'simpld', '( %s -> D e. %s )' % (ph, STK('T')))
    dk = w.s([dk2], 'simprd', '( %s -> ( D ` K ) = %s )' % (ph, WX))
    wx2 = w.s([p3, w.inst('simp3')], 'syl', '( %s -> ( W e. %s /\\ X e. %s ) )' % (ph, WB, WG))
    ww = w.s([wx2], 'simpld', '( %s -> W e. %s )' % (ph, WB))
    xx = w.s([wx2], 'simprd', '( %s -> X e. %s )' % (ph, WG))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kd, gk = gamk(w, ph, 'K', geq, kk)
    jd, gj = gamk(w, ph, 'J', geq, jj)
    idd, gi = gamk(w, ph, 'I', geq, ii)
    return dict(phm=phm, geq=geq, m1=m1, m2=m2, m3=m3, m4=m4, al=al, a1l=a1l, a2l=a2l, e1l=e1l, el=el,
                kk=kk, jj=jj, ii=ii, nkj=nkj, nki=nki, nji=nji, ff=ff, cc=cc, pp=pp, nss=nss, mif=mif,
                dd=dd, dk=dk, ww=ww, xx=xx, tv=tv, kd=kd, gk=gk, jd=jd, gj=gj, idd=idd, gi=gi)


def pushstage(w, ph, u, A, E, Kk, kd, ge, D, dcl, meq):
    """tm2fpshn at label A, stack Kk, letter 4, exit E, stacks D: returns
    (triple step, D2)"""
    D2 = UPDT(D, Kk, '( <" 4 "> ++ ( %s ` %s ) )' % (D, Kk))
    al = {'A': u['al'], "A'": u['a1l'], 'A"': u['a2l'], "E'": u['e1l'], 'E': u['el']}
    g4 = gamlet(w, ph, '4')
    g4k = lgk(w, ph, '4', Kk, ge, g4)
    a1 = w.s([u['phm'], meq], 'jca', '( %s -> ( %s /\\ ( M ` %s ) = %s ) )' % (ph, PHM, A, PSH(Kk, '4', E)))
    kz = w.s([kd, g4k], 'jca', '( %s -> ( %s e. %s /\\ 4 e. %s ) )' % (ph, Kk, DG, GT(Kk)))
    a2 = w.s([al[A], al[E], kz], '3jca', '( %s -> ( %s e. %s /\\ %s e. %s /\\ ( %s e. %s /\\ 4 e. %s ) ) )' % (ph, A, L('T'), E, L('T'), Kk, DG, GT(Kk)))
    a3 = w.s([dcl, u['nss']], 'jca', '( %s -> ( %s e. %s /\\ N C_ %s ) )' % (ph, D, STK('T'), S('T')))
    ant = w.s([a1, a2, a3], '3jca', '( %s -> ( ( %s /\\ ( M ` %s ) = %s ) /\\ ( %s e. %s /\\ %s e. %s /\\ ( %s e. %s /\\ 4 e. %s ) ) /\\ ( %s e. %s /\\ N C_ %s ) ) )'
              % (ph, PHM, A, PSH(Kk, '4', E), A, L('T'), E, L('T'), Kk, DG, GT(Kk), D, STK('T'), S('T')))
    tri = w.s([ant, w.inst('tm2fpshn')], 'syl', '( %s -> %s )' % (ph, HR(CL(A, 'N', D), 'T', 'M', CL(E, 'N', D2), '1')))
    return tri, D2


def movestage(w, ph, u, A, E, Kk, Jj, kd, jd, gk, gj, nkj, D, dcl, meq, Wd, wcl, Xd, xcl, H, hcl):
    """tm2fmvn at label A from Kk to Jj exiting to E, base stacks D, word Wd,
    rest Xd, destination contents H (all class expressions; wcl : Wd e. WB,
    xcl : Xd e. Word Gamma', hcl : H e. Word Gamma').  Returns (triple, pre, post)."""
    al = {'A': u['al'], "A'": u['a1l'], 'A"': u['a2l'], "E'": u['e1l'], 'E': u['el']}
    STM = MOVE(A, Kk, Jj, E)
    a1 = w.s([u['phm'], meq], 'jca', '( %s -> ( %s /\\ ( M ` %s ) = %s ) )' % (ph, PHM, A, STM))
    b1 = w.s([al[A], al[E]], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, A, L('T'), E, L('T')))
    b2 = w.s([kd, jd], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, Kk, DG, Jj, DG))
    b = w.s([b1, b2, nkj], '3jca', '( %s -> ( ( %s e. %s /\\ %s e. %s ) /\\ ( %s e. %s /\\ %s e. %s ) /\\ %s =/= %s ) )' % (ph, A, L('T'), E, L('T'), Kk, DG, Jj, DG, Kk, Jj))
    fk = fmapg(w, ph, 'F', Kk, gk, u['ff'])
    pj = pmapg(w, ph, 'P', Jj, gj, u['pp'])
    c1 = w.s([fk, u['cc'], pj], '3jca', '( %s -> ( F e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) /\\ %s /\\ P e. ( %s ^m %s ) ) )' % (ph, S('T'), S('T'), GT(Kk), CTY, GT(Jj), S('T')))
    bs = bitsss(w, ph)
    bk = w.s([bs, gk], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, BITS, GT(Kk)))
    bj = w.s([bs, gj], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, BITS, GT(Jj)))
    bkj = w.s([bk, bj], 'jca', '( %s -> ( %s C_ %s /\\ %s C_ %s ) )' % (ph, BITS, GT(Kk), BITS, GT(Jj)))
    g4 = gamlet(w, ph, '4')
    g4k = lgk(w, ph, '4', Kk, gk, g4)
    xk = wgk(w, ph, Xd, Kk, gk, xcl)
    hj = wgk(w, ph, H, Jj, gj, hcl)
    c2b = w.s([g4k, xk, hj], '3jca', '( %s -> ( 4 e. %s /\\ %s e. Word %s /\\ %s e. Word %s ) )' % (ph, GT(Kk), Xd, GT(Kk), H, GT(Jj)))
    c2 = w.s([bkj, c2b, dcl], '3jca', '( %s -> ( ( %s C_ %s /\\ %s C_ %s ) /\\ ( 4 e. %s /\\ %s e. Word %s /\\ %s e. Word %s ) /\\ %s e. %s ) )'
             % (ph, BITS, GT(Kk), BITS, GT(Jj), GT(Kk), Xd, GT(Kk), H, GT(Jj), D, STK('T')))
    c3 = w.s([u['nss'], u['mif']], 'jca', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), MIFACE))
    c = w.s([c1, c2, c3], '3jca', '( %s -> ( ( F e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) /\\ %s /\\ P e. ( %s ^m %s ) ) /\\ ( ( %s C_ %s /\\ %s C_ %s ) /\\ ( 4 e. %s /\\ %s e. Word %s /\\ %s e. Word %s ) /\\ %s e. %s ) /\\ ( N C_ %s /\\ %s ) ) )'
             % (ph, S('T'), S('T'), GT(Kk), CTY, GT(Jj), S('T'), BITS, GT(Kk), BITS, GT(Jj), GT(Kk), Xd, GT(Kk), H, GT(Jj), D, STK('T'), S('T'), MIFACE))
    abc = w.s([a1, b, c], '3jca', '( %s -> ( ( %s /\\ ( M ` %s ) = %s ) /\\ ( ( %s e. %s /\\ %s e. %s ) /\\ ( %s e. %s /\\ %s e. %s ) /\\ %s =/= %s ) /\\ ( ( F e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) /\\ %s /\\ P e. ( %s ^m %s ) ) /\\ ( ( %s C_ %s /\\ %s C_ %s ) /\\ ( 4 e. %s /\\ %s e. Word %s /\\ %s e. Word %s ) /\\ %s e. %s ) /\\ ( N C_ %s /\\ %s ) ) ) )'
              % (ph, PHM, A, STM, A, L('T'), E, L('T'), Kk, DG, Jj, DG, Kk, Jj, S('T'), S('T'), GT(Kk), CTY, GT(Jj), S('T'), BITS, GT(Kk), BITS, GT(Jj), GT(Kk), Xd, GT(Kk), H, GT(Jj), D, STK('T'), S('T'), MIFACE))
    ant = w.s([abc, wcl], 'jca', '( %s -> ( ( ( %s /\\ ( M ` %s ) = %s ) /\\ ( ( %s e. %s /\\ %s e. %s ) /\\ ( %s e. %s /\\ %s e. %s ) /\\ %s =/= %s ) /\\ ( ( F e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) /\\ %s /\\ P e. ( %s ^m %s ) ) /\\ ( ( %s C_ %s /\\ %s C_ %s ) /\\ ( 4 e. %s /\\ %s e. Word %s /\\ %s e. Word %s ) /\\ %s e. %s ) /\\ ( N C_ %s /\\ %s ) ) ) /\\ %s e. %s ) )'
              % (ph, PHM, A, STM, A, L('T'), E, L('T'), Kk, DG, Jj, DG, Kk, Jj, S('T'), S('T'), GT(Kk), CTY, GT(Jj), S('T'), BITS, GT(Kk), BITS, GT(Jj), GT(Kk), Xd, GT(Kk), H, GT(Jj), D, STK('T'), S('T'), MIFACE, Wd, WB))
    PRE = UPDT(UPDT(D, Kk, '( %s ++ ( <" 4 "> ++ %s ) )' % (Wd, Xd)), Jj, H)
    POST = UPDT(UPDT(D, Kk, Xd), Jj, '( ( reverse ` %s ) ++ %s )' % (Wd, H))
    NW = '( ( # ` %s ) + 1 )' % Wd
    tri = w.s([ant, w.inst('tm2fmvn')], 'syl', '( %s -> %s )' % (ph, HR(CL(A, 'N', PRE), 'T', 'M', CL(E, 'N', POST), NW)))
    return tri, PRE, POST


def tm2lme():
    lab = 'tm2lme'
    ph = PHE
    w = W(lab, 'The fragment ` moveEntry ` of TM/Lists.lean: the top number of stack '
               '` K ` is moved onto stack ` J ` with its orientation preserved, by two '
               'reversals through the scratch stack ` I ` (a comma is pushed on ` I ` , '
               'the number reversed onto it, a comma pushed on ` J ` , the number '
               'reversed back onto ` J ` ); ` I ` is restored.  Lean: ` moveEntry_runs ` , '
               'whose preserved state fields are the class ` N ` here.')
    u = prelude(w, ph)
    tv, dd, dk = u['tv'], u['dd'], u['dk']
    # stage 1: push 4 on I
    s1, D1 = pushstage(w, ph, u, 'A', "A'", 'I', u['idd'], u['gi'], 'D', dd, u['m1'])
    # present D1 as UPD( UPD( D , K , WX ) , I , H )
    H1 = '( <" 4 "> ++ ( D ` I ) )'
    dkv = w.s([dd], 'elexd', '( %s -> D e. _V )' % ph)
    dkw = stkfvg(w, ph, 'D', 'K', tv, dd, u['kd'], u['gk'])
    dkx = w.s([dkw], 'elexd', '( %s -> ( D ` K ) e. _V )' % ph)
    upid = w.s([tv, dd, u['kd'], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = D )' % (ph, UPDT('D', 'K', '( D ` K )')))
    c1 = w.s([dk], 'opeq2d', '( %s -> <. K , ( D ` K ) >. = <. K , %s >. )' % (ph, WX))
    c2 = w.s([c1], 'sneqd', '( %s -> { <. K , ( D ` K ) >. } = { <. K , %s >. } )' % (ph, WX))
    c3 = w.s([c2], 'uneq2d', '( %s -> %s = %s )' % (ph, UPDT('D', 'K', '( D ` K )'), UPDT('D', 'K', WX)))
    deq = w.s([upid, c3], 'eqtr3d', '( %s -> D = %s )' % (ph, UPDT('D', 'K', WX)))
    r1 = w.s([deq], 'reseq1d', '( %s -> ( D |` ( %s \\ { I } ) ) = ( %s |` ( %s \\ { I } ) ) )' % (ph, DG, UPDT('D', 'K', WX), DG))
    PRE2 = UPDT(UPDT('D', 'K', WX), 'I', H1)
    r2 = w.s([r1], 'uneq1d', '( %s -> %s = %s )' % (ph, D1, PRE2))
    s1b = hrtransport(w, ph, s1, CL('A', 'N', 'D'), CL("A'", 'N', D1), '1', None, CL("A'", 'N', PRE2), eqd=cleq(w, ph, "A'", 'N', D1, PRE2, r2))
    # stage 2: mover K -> I
    g4 = gamlet(w, ph, '4'); c4 = s1g(w, ph, '4')
    diw = stkfvg(w, ph, 'D', 'I', tv, dd, u['idd'], u['gi'])
    h1cl = ccatg(w, ph, '<" 4 ">', '( D ` I )', c4, diw)
    s2, PRE2b, POST2 = movestage(w, ph, u, "A'", 'A"', 'K', 'I', u['kd'], u['idd'], u['gk'], u['gi'], u['nki'],
                                 'D', dd, u['m2'], 'W', u['ww'], 'X', u['xx'], H1, h1cl)
    assert PRE2b == PRE2, PRE2b
    # stage 3: push 4 on J; POST2 e. Stk
    DKX = UPDT('D', 'K', 'X')
    dkxcl = updcl(w, ph, 'D', 'K', 'X', tv, dd, u['kd'], u['gk'], u['xx'])
    rvw = w.s([u['ww'], w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. %s )' % (ph, WB))
    rvg = wbtog(w, ph, '( reverse ` W )', rvw)
    RH = '( ( reverse ` W ) ++ %s )' % H1
    rhcl = ccatg(w, ph, '( reverse ` W )', H1, rvg, h1cl)
    d2cl = updcl(w, ph, DKX, 'I', RH, tv, dkxcl, u['idd'], u['gi'], rhcl)
    s3, D3 = pushstage(w, ph, u, 'A"', "E'", 'J', u['jd'], u['gj'], POST2, d2cl, u['m3'])
    # ( POST2 ` J ) = ( D ` J )
    rhv = w.s([rhcl], 'elexd', '( %s -> %s e. _V )' % (ph, RH))
    xv = w.s([u['xx']], 'elexd', '( %s -> X e. _V )' % ph)
    nji_ = u['nji']
    njk = w.s([u['nkj']], 'necomd', '( %s -> J =/= K )' % ph)
    e1 = updn(w, ph, DKX, 'I', RH, 'J', tv, dkxcl, u['idd'], rhv, u['jd'], nji_)
    e2 = updn(w, ph, 'D', 'K', 'X', 'J', tv, dd, u['kd'], xv, u['jd'], njk)
    e3 = w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, POST2))
    e4 = w.s([e3], 'oveq2d', '( %s -> ( <" 4 "> ++ ( %s ` J ) ) = ( <" 4 "> ++ ( D ` J ) ) )' % (ph, POST2))
    e5 = w.s([e4], 'opeq2d', '( %s -> <. J , ( <" 4 "> ++ ( %s ` J ) ) >. = <. J , ( <" 4 "> ++ ( D ` J ) ) >. )' % (ph, POST2))
    e6 = w.s([e5], 'sneqd', '( %s -> { <. J , ( <" 4 "> ++ ( %s ` J ) ) >. } = { <. J , ( <" 4 "> ++ ( D ` J ) ) >. } )' % (ph, POST2))
    H4 = '( <" 4 "> ++ ( D ` J ) )'
    D3b = UPDT(POST2, 'J', H4)
    e7 = w.s([e6], 'uneq2d', '( %s -> %s = %s )' % (ph, D3, D3b))
    s3b = hrtransport(w, ph, s3, CL('A"', 'N', POST2), CL("E'", 'N', D3), '1', None, CL("E'", 'N', D3b), eqd=cleq(w, ph, "E'", 'N', D3, D3b, e7))
    # stage 4: mover I -> J with base DKX, word ( reverse ` W ), rest ( D ` I ), H4
    djw = stkfvg(w, ph, 'D', 'J', tv, dd, u['jd'], u['gj'])
    h4cl = ccatg(w, ph, '<" 4 ">', '( D ` J )', c4, djw)
    nij = w.s([u['nji']], 'necomd', '( %s -> I =/= J )' % ph)
    s4, PRE4, POST4 = movestage(w, ph, u, "E'", 'E', 'I', 'J', u['idd'], u['jd'], u['gi'], u['gj'], nij,
                                DKX, dkxcl, u['m4'], '( reverse ` W )', rvw, '( D ` I )', diw, H4, h4cl)
    assert PRE4 == D3b, '%s\n%s' % (PRE4, D3b)
    # simplify POST4 to DFIN
    rr = w.s([u['ww'], w.inst('revrev')], 'syl', '( %s -> ( reverse ` ( reverse ` W ) ) = W )' % ph)
    div = w.s([diw], 'elexd', '( %s -> ( D ` I ) e. _V )' % ph)
    nik = w.s([u['nki']], 'necomd', '( %s -> I =/= K )' % ph)
    f1 = updn(w, ph, 'D', 'K', 'X', 'I', tv, dd, u['kd'], xv, u['idd'], nik)
    f1r = w.s([f1], 'eqcomd', '( %s -> ( D ` I ) = ( %s ` I ) )' % (ph, DKX))
    f2 = w.s([f1r], 'opeq2d', '( %s -> <. I , ( D ` I ) >. = <. I , ( %s ` I ) >. )' % (ph, DKX))
    f3 = w.s([f2], 'sneqd', '( %s -> { <. I , ( D ` I ) >. } = { <. I , ( %s ` I ) >. } )' % (ph, DKX))
    f4 = w.s([f3], 'uneq2d', '( %s -> %s = %s )' % (ph, UPDT(DKX, 'I', '( D ` I )'), UPDT(DKX, 'I', '( %s ` I )' % DKX)))
    f5 = w.s([tv, dkxcl, u['idd'], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = %s )' % (ph, UPDT(DKX, 'I', '( %s ` I )' % DKX), DKX))
    f6 = w.s([f4, f5], 'eqtrd', '( %s -> %s = %s )' % (ph, UPDT(DKX, 'I', '( D ` I )'), DKX))
    st, res = w.rewrite(POST4, {'( reverse ` ( reverse ` W ) )': ('W', rr), UPDT(DKX, 'I', '( D ` I )'): (DKX, f6)}, ph)
    assert res == DFIN, '%s\n%s' % (res, DFIN)
    s4b = hrtransport(w, ph, s4, CL("E'", 'N', PRE4), CL('E', 'N', POST4), '( ( # ` ( reverse ` W ) ) + 1 )', None, CL('E', 'N', DFIN), eqd=cleq(w, ph, 'E', 'N', POST4, DFIN, st))
    # the chain
    C0 = CL('A', 'N', 'D'); C1 = CL("A'", 'N', PRE2); C2 = CL('A"', 'N', POST2); C3 = CL("E'", 'N', D3b); C4 = CL('E', 'N', DFIN)
    NW = '( ( # ` W ) + 1 )'; NR = '( ( # ` ( reverse ` W ) ) + 1 )'
    q1 = hseq(w, ph, u['phm'], C0, C1, C2, '1', NW, s1b, s2)
    q2 = hseq(w, ph, u['phm'], C0, C2, C3, '( 1 + %s )' % NW, '1', q1, s3b)
    q3 = hseq(w, ph, u['phm'], C0, C3, C4, '( ( 1 + %s ) + 1 )' % NW, NR, q2, s4b)
    TOT = '( ( ( 1 + %s ) + 1 ) + %s )' % (NW, NR)
    GOAL = '( ( 2 x. ( # ` W ) ) + 4 )'
    nw = w.s([u['ww'], w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    nwr = w.s([nw], 'nn0red', '( %s -> ( # ` W ) e. RR )' % ph)
    rl = w.s([u['ww'], w.inst('revlen')], 'syl', '( %s -> ( # ` ( reverse ` W ) ) = ( # ` W ) )' % ph)
    rlr = w.s([rl, nwr], 'eqeltrd', '( %s -> ( # ` ( reverse ` W ) ) e. RR )' % ph)
    eq = lineq(w, ph, TOT, GOAL, hyps=[rl], leaves={'( # ` W )': nwr, '( # ` ( reverse ` W ) )': rlr})
    o = w.s([eq], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C4, TOT, C4, GOAL))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C4, TOT), HR(C0, 'T', 'M', C4, GOAL)))
    w.qed([b, q3], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C4, GOAL)))
    return w.run()


if __name__ == '__main__':
    if want('tm2lme'): tm2lme()
