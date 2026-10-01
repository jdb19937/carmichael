"""T3: the two-operand read phase --- Lean's `OpA.read` / `OpB.read` of
TM/Arith.lean (blueprint 1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GK = '( %s ` K )' % G('T')
OPT = '( %s |_| 1o )' % GK
RATY = 'F e. ( %s ^m ( %s X. %s ) )' % (S('T'), S('T'), OPT)
CTY = 'C e. ( 2o ^m %s )' % S('T')
STMT_T = '( TM2Stmt ` T )'
POPS = POP('K', 'F', 'Q')
RD = BRANCH('C', 'Q', POPS)
ZX = '( <" Z "> ++ X )'
NV = '( F ` <. A , ( inl ` Z ) >. )'
UPDX = UPD('T', 'D', 'K', 'X')

TY = '( T e. V /\\ %s /\\ %s )' % (CTY, RATY)
KQ = '( K e. %s /\\ Q e. %s /\\ ( A e. %s /\\ D e. %s ) )' % (DG, STMT_T, S('T'), STK('T'))
DJ1 = "( ( C ` A ) = 1o /\\ A' = A /\\ D' = D )"
DJ2 = ("( -. ( C ` A ) = 1o /\\ ( ( D ` K ) = %s /\\ Z e. %s /\\ X e. Word %s ) "
       "/\\ ( A' = %s /\\ D' = %s ) )" % (ZX, GK, GK, NV, UPDX))
PH = '( %s /\\ %s /\\ ( %s \\/ %s ) )' % (TY, KQ, DJ1, DJ2)

SAP = lambda st, x, y: '( %s %s <. %s , %s >. )' % (st, SA('T'), x, y)
GOAL = '%s = %s' % (SAP(RD, 'A', 'D'), SAP('Q', "A'", "D'"))


def ctx(w, ph, lift=None):
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    tv = g('simp11', 'T e. V')
    cc = g('simp12', CTY)
    ff = g('simp13', RATY)
    kk = g('simp21', 'K e. %s' % DG)
    qq = g('simp22', 'Q e. %s' % STMT_T)
    ad = g('simp23', '( A e. %s /\\ D e. %s )' % (S('T'), STK('T')))
    aa = w.s([ad], 'simpld', '( %s -> A e. %s )' % (ph, S('T')))
    dd = w.s([ad], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    return dict(tv=tv, cc=cc, ff=ff, kk=kk, qq=qq, ad=ad, aa=aa, dd=dd)


def tm2frd():
    lab = 'tm2frd'
    w = W(lab, 'The read phase of one operand of a two-operand loop: the '
               'statement ` branch C Q ( pop K F Q ) ` steps to its '
               'continuation ` Q ` either at the unchanged configuration (the '
               'operand is exhausted, the branch is taken) or with the head of '
               'stack ` K ` popped into the handler ` F ` .  Lean: '
               '` OpA.read ` and ` OpB.read ` of TM/Arith.lean, whose '
               '` exists v1 S1 ` are the class variables ` A\' ` , ` D\' ` and '
               'whose disjunction is ` OpA ` itself.  The continuation ` Q ` is '
               'a class variable, so one instance per operand assembles the '
               'read phase of ` addBody ` , ` subBody ` and ` cmpBody ` .')
    u = ctx(w, PH)
    kf = w.s([u['kk'], u['ff']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (PH, DG, RATY))
    popcl = w.s([u['tv'], kf, u['qq'], w.inst('tm2pop')], 'syl3anc',
                '( %s -> %s e. %s )' % (PH, POPS, STMT_T))
    cqp = w.s([u['cc'], u['qq'], popcl], '3jca',
              '( %s -> ( %s /\\ Q e. %s /\\ %s e. %s ) )' % (PH, CTY, STMT_T, POPS, STMT_T))
    IFT = 'if ( ( C ` A ) = 1o , %s , %s )' % (SAP('Q', 'A', 'D'), SAP(POPS, 'A', 'D'))
    brval = w.s([u['tv'], cqp, u['ad'], w.inst('tm2sabr')], 'syl3anc',
                '( %s -> %s = %s )' % (PH, SAP(RD, 'A', 'D'), IFT))

    # ---- case 1: the operand is exhausted, the branch is taken
    a1 = '( %s /\\ %s )' % (PH, DJ1)
    d1 = w.s([], 'simpr', '( %s -> %s )' % (a1, DJ1))
    c1 = w.s([d1, w.inst('simp1')], 'syl', '( %s -> ( C ` A ) = 1o )' % a1)
    e1a = w.s([d1, w.inst('simp2')], 'syl', "( %s -> A' = A )" % a1)
    e1d = w.s([d1, w.inst('simp3')], 'syl', "( %s -> D' = D )" % a1)
    bv1 = w.s([brval], 'adantr', '( %s -> %s = %s )' % (a1, SAP(RD, 'A', 'D'), IFT))
    it1 = w.s([c1], 'iftrued', '( %s -> %s = %s )' % (a1, IFT, SAP('Q', 'A', 'D')))
    s1 = w.s([bv1, it1], 'eqtrd', '( %s -> %s = %s )' % (a1, SAP(RD, 'A', 'D'), SAP('Q', 'A', 'D')))
    o1 = w.s([e1a, e1d], 'opeq12d', "( %s -> <. A' , D' >. = <. A , D >. )" % a1)
    v1 = w.s([o1], 'oveq2d', '( %s -> %s = %s )' % (a1, SAP('Q', "A'", "D'"), SAP('Q', 'A', 'D')))
    v1c = w.s([v1], 'eqcomd', '( %s -> %s = %s )' % (a1, SAP('Q', 'A', 'D'), SAP('Q', "A'", "D'")))
    case1 = w.s([s1, v1c], 'eqtrd', '( %s -> %s )' % (a1, GOAL))

    # ---- case 2: the operand is live, the head of stack K is popped
    a2 = '( %s /\\ %s )' % (PH, DJ2)
    u2 = ctx(w, a2, 'adantr')
    d2 = w.s([], 'simpr', '( %s -> %s )' % (a2, DJ2))
    c2 = w.s([d2, w.inst('simp1')], 'syl', '( %s -> -. ( C ` A ) = 1o )' % a2)
    st2 = w.s([d2, w.inst('simp2')], 'syl',
              '( %s -> ( ( D ` K ) = %s /\\ Z e. %s /\\ X e. Word %s ) )' % (a2, ZX, GK, GK))
    dk = w.s([st2, w.inst('simp1')], 'syl', '( %s -> ( D ` K ) = %s )' % (a2, ZX))
    zz = w.s([st2, w.inst('simp2')], 'syl', '( %s -> Z e. %s )' % (a2, GK))
    xx = w.s([st2, w.inst('simp3')], 'syl', '( %s -> X e. Word %s )' % (a2, GK))
    eq2 = w.s([d2, w.inst('simp3')], 'syl', "( %s -> ( A' = %s /\\ D' = %s ) )" % (a2, NV, UPDX))
    e2a = w.s([eq2], 'simpld', "( %s -> A' = %s )" % (a2, NV))
    e2d = w.s([eq2], 'simprd', "( %s -> D' = %s )" % (a2, UPDX))
    bv2 = w.s([brval], 'adantr', '( %s -> %s = %s )' % (a2, SAP(RD, 'A', 'D'), IFT))
    if2 = w.s([c2], 'iffalsed', '( %s -> %s = %s )' % (a2, IFT, SAP(POPS, 'A', 'D')))
    s2 = w.s([bv2, if2], 'eqtrd',
             '( %s -> %s = %s )' % (a2, SAP(RD, 'A', 'D'), SAP(POPS, 'A', 'D')))
    kfq = w.s([u2['kk'], u2['ff'], u2['qq']], '3jca',
              '( %s -> ( K e. %s /\\ %s /\\ Q e. %s ) )' % (a2, DG, RATY, STMT_T))
    RES0 = SAP('Q', '( F ` <. A , %s >. )' % HEAD('D', 'K'), UPD('T', 'D', 'K', TAIL('D', 'K')))
    pv = w.s([u2['tv'], kfq, u2['ad'], w.inst('tm2sapop')], 'syl3anc',
             '( %s -> %s = %s )' % (a2, SAP(POPS, 'A', 'D'), RES0))
    rw, RES1 = w.rewrite(RES0, {'( D ` K )': (ZX, dk)}, a2)
    # ( <" Z "> ++ X ) =/= (/) , its 0th letter, its tail
    s1c = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (a2, GK))
    s1n = w.s([], 's1nz', '<" Z "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Z "> =/= (/) )' % a2)
    zxn = w.s([s1c, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (a2, ZX))
    zxnn = w.s([zxn], 'neneqd', '( %s -> -. %s = (/) )' % (a2, ZX))
    zj = w.s([zz, xx], 'jca', '( %s -> ( Z e. %s /\\ X e. Word %s ) )' % (a2, GK, GK))
    zfv = w.s([zj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Z )' % (a2, ZX))
    ztl = w.s([zj, w.inst('wrdtls1')], 'syl',
              '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = X )' % (a2, ZX, ZX))
    ev, RES2 = evaluate(w, a2, RES1, {},
                        ifrules={'%s = (/)' % ZX: (False, zxnn)},
                        extra_rules=(lambda n: {'( %s ` 0 )' % ZX: ('Z', zfv),
                                                '( %s substr <. 1 , ( # ` %s ) >. )' % (ZX, ZX): ('X', ztl)}.get(n.text())))
    want2 = SAP('Q', NV, UPDX)
    assert RES2 == want2, 'GOT %s\nWANT %s' % (RES2, want2)
    p1 = w.s([pv, rw], 'eqtrd', '( %s -> %s = %s )' % (a2, SAP(POPS, 'A', 'D'), RES1))
    p2 = w.s([p1, ev], 'eqtrd', '( %s -> %s = %s )' % (a2, SAP(POPS, 'A', 'D'), RES2))
    s3 = w.s([s2, p2], 'eqtrd', '( %s -> %s = %s )' % (a2, SAP(RD, 'A', 'D'), RES2))
    o2 = w.s([e2a, e2d], 'opeq12d', "( %s -> <. A' , D' >. = <. %s , %s >. )" % (a2, NV, UPDX))
    v2 = w.s([o2], 'oveq2d', '( %s -> %s = %s )' % (a2, SAP('Q', "A'", "D'"), RES2))
    v2c = w.s([v2], 'eqcomd', '( %s -> %s = %s )' % (a2, RES2, SAP('Q', "A'", "D'")))
    case2 = w.s([s3, v2c], 'eqtrd', '( %s -> %s )' % (a2, GOAL))

    dj = w.s([], 'simp3', '( %s -> ( %s \\/ %s ) )' % (PH, DJ1, DJ2))
    w.qed([case1, case2, dj], 'mpjaodan', '( %s -> %s )' % (PH, GOAL))
    return w.run()



# ------------------------------------------------- the composed read phase

GJ = '( %s ` J )' % G('T')
OPTJ = '( %s |_| 1o )' % GJ
RBTY = "F' e. ( %s ^m ( %s X. %s ) )" % (S('T'), S('T'), OPTJ)
CBTY = "C' e. ( 2o ^m %s )" % S('T')
RDY = BRANCH("C'", 'R', POP('J', "F'", 'R'))
BODY = BRANCH('C', RDY, POP('K', 'F', RDY))
ZXJ = "( <\" Z' \"> ++ X' )"
D1 = UPD('T', 'D', 'K', 'X')
D2 = UPD('T', D1, 'J', "X'")
V1 = lambda r: '( F ` <. %s , ( inl ` Z ) >. )' % r
V2 = lambda r: "( F' ` <. %s , ( inl ` Z' ) >. )" % V1(r)
MA = lambda x: '( ( M ` A ) %s <. %s , D >. )' % (SA('T'), x)


def frd2(lab, popA, popB):
    """the composed read phase; `popA`/`popB` say whether the operand is live
    (a symbol is popped) or exhausted (the branch skips the pop)"""
    V1 = (lambda r: '( F ` <. %s , ( inl ` Z ) >. )' % r) if popA else (lambda r: r)
    V2 = ((lambda r: "( F' ` <. %s , ( inl ` Z' ) >. )" % V1(r)) if popB else V1)
    D1 = UPD('T', 'D', 'K', 'X') if popA else 'D'
    D2 = UPD('T', D1, 'J', "X'") if popB else D1
    CA = ('-. ( C ` %s ) = 1o' if popA else '( C ` %s ) = 1o')
    CB = ("-. ( C' ` %s ) = 1o" if popB else "( C' ` %s ) = 1o")
    HRB = lambda m: ('( %s /\\ %s /\\ %s e. O )' % (CA % m, CB % V1(m), V2(m)))
    TY = ("( T e. V /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s ) )" % (CTY, CBTY, RATY, RBTY))
    KJP = ('( K e. %s /\\ J e. %s /\\ K =/= J )' % (DG, DG)) if (popA and popB) else \
          ('( K e. %s /\\ J e. %s )' % (DG, DG))
    KJ = ('( %s /\\ ( R e. %s /\\ D e. %s ) /\\ ( M ` A ) = %s )'
          % (KJP, STMT_T, STK('T'), BODY))
    SKA = '( ( D ` K ) = %s /\\ Z e. %s /\\ X e. Word %s )' % (ZX, GK, GK)
    SKB = "( ( D ` J ) = %s /\\ Z' e. %s /\\ X' e. Word %s )" % (ZXJ, GJ, GJ)
    parts = ([SKA] if popA else []) + ([SKB] if popB else [])
    NN = '( N C_ %s /\\ A. m e. N %s )' % (S('T'), HRB('m'))
    if len(parts) == 2:
        third = '( ( %s /\\ %s ) /\\ %s )' % (parts[0], parts[1], NN)
    elif len(parts) == 1:
        third = '( %s /\\ %s )' % (parts[0], NN)
    else:
        third = NN
    ph = '( %s /\\ %s /\\ %s )' % (TY, KJ, third)
    GOAL2 = 'A. r e. N E. p e. O %s = ( R %s <. p , %s >. )' % (MA('r'), SA('T'), D2)
    desc = ('The two-operand read phase, %s.  The body of a two-operand loop '
            'reaches its rest ` R ` in one machine step, the two operand reads '
            'composed by two instances of ~ tm2frd .  Lean: ` OpA.read ` '
            'followed by ` OpB.read ` inside ` addLoop_loop ` , '
            '` subLoop_loop ` and ` cmpFrag_loop ` .  The conclusion is the '
            'hypothesis the body lemmas ~ tm2fad1 , ~ tm2fad0c , ~ tm2fad0n , '
            '~ tm2fcm1 and ~ tm2fcm0 take.'
            % ({(True, True): 'both operands live',
                (True, False): 'the first operand live, the second exhausted',
                (False, True): 'the first operand exhausted, the second live',
                (False, False): 'both operands exhausted'}[(popA, popB)]))
    w = W(lab, desc)
    tv = w.s([], 'simp11', '( %s -> T e. V )' % ph)
    cs = w.s([], 'simp12', '( %s -> ( %s /\\ %s ) )' % (ph, CTY, CBTY))
    cc = w.s([cs], 'simpld', '( %s -> %s )' % (ph, CTY))
    cb = w.s([cs], 'simprd', '( %s -> %s )' % (ph, CBTY))
    fs = w.s([], 'simp13', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, RBTY))
    fa = w.s([fs], 'simpld', '( %s -> %s )' % (ph, RATY))
    fb = w.s([fs], 'simprd', '( %s -> %s )' % (ph, RBTY))
    kj = w.s([], 'simp21', '( %s -> %s )' % (ph, KJP))
    if popA and popB:
        kk = w.s([kj, w.inst('simp1')], 'syl', '( %s -> K e. %s )' % (ph, DG))
        jj = w.s([kj, w.inst('simp2')], 'syl', '( %s -> J e. %s )' % (ph, DG))
        ne = w.s([kj, w.inst('simp3')], 'syl', '( %s -> K =/= J )' % ph)
        nes = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    else:
        kk = w.s([kj], 'simpld', '( %s -> K e. %s )' % (ph, DG))
        jj = w.s([kj], 'simprd', '( %s -> J e. %s )' % (ph, DG))
    rd = w.s([], 'simp22', '( %s -> ( R e. %s /\\ D e. %s ) )' % (ph, STMT_T, STK('T')))
    rr = w.s([rd], 'simpld', '( %s -> R e. %s )' % (ph, STMT_T))
    dd = w.s([rd], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    meq = w.s([], 'simp23', '( %s -> ( M ` A ) = %s )' % (ph, BODY))
    if len(parts) == 2:
        sab = w.s([], 'simp3l', '( %s -> ( %s /\\ %s ) )' % (ph, parts[0], parts[1]))
        sa = w.s([sab], 'simpld', '( %s -> %s )' % (ph, parts[0]))
        sb = w.s([sab], 'simprd', '( %s -> %s )' % (ph, parts[1]))
        nh = w.s([], 'simp3r', '( %s -> %s )' % (ph, NN))
    elif len(parts) == 1:
        one = w.s([], 'simp3l', '( %s -> %s )' % (ph, parts[0]))
        sa = one if popA else None
        sb = None if popA else one
        nh = w.s([], 'simp3r', '( %s -> %s )' % (ph, NN))
    else:
        sa = sb = None
        nh = w.s([], 'simp3', '( %s -> %s )' % (ph, NN))
    if popA:
        dkk = w.s([sa, w.inst('simp1')], 'syl', '( %s -> ( D ` K ) = %s )' % (ph, ZX))
        zz = w.s([sa, w.inst('simp2')], 'syl', '( %s -> Z e. %s )' % (ph, GK))
        xx = w.s([sa, w.inst('simp3')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    if popB:
        djj = w.s([sb, w.inst('simp1')], 'syl', '( %s -> ( D ` J ) = %s )' % (ph, ZXJ))
        zb = w.s([sb, w.inst('simp2')], 'syl', "( %s -> Z' e. %s )" % (ph, GJ))
        xb = w.s([sb, w.inst('simp3')], 'syl', "( %s -> X' e. Word %s )" % (ph, GJ))
    nss = w.s([nh], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    hr = w.s([nh], 'simprd', '( %s -> A. m e. N %s )' % (ph, HRB('m')))
    jf = w.s([jj, fb], 'jca', '( %s -> ( J e. %s /\\ %s ) )' % (ph, DG, RBTY))
    pj = w.s([tv, jf, rr, w.inst('tm2pop')], 'syl3anc',
             '( %s -> %s e. %s )' % (ph, POP('J', "F'", 'R'), STMT_T))
    rp = w.s([rr, pj], 'jca', '( %s -> ( R e. %s /\\ %s e. %s ) )'
             % (ph, STMT_T, POP('J', "F'", 'R'), STMT_T))
    rdy = w.s([tv, cb, rp, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, RDY, STMT_T))
    if popA:
        kx = w.s([kk, xx], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (ph, DG, GK))
        d1cl = w.s([tv, dd, kx, w.inst('tm2stkupd')], 'syl3anc',
                   '( %s -> %s e. %s )' % (ph, D1, STK('T')))
    else:
        d1cl = dd
    if popB:
        if popA:
            n1 = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK('T')))
            n2 = w.s([kk, xx], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (ph, DG, GK))
            n3 = w.s([jj, nes], 'jca', '( %s -> ( J e. %s /\\ J =/= K ) )' % (ph, DG))
            dj1 = w.s([n1, n2, n3, w.inst('tm2stkupn')], 'syl3anc',
                      '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, D1))
            dj2 = w.s([dj1, djj], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1, ZXJ))
        else:
            dj2 = djj

    av = '( %s /\\ r e. N )' % ph
    def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
    tva = A_(tv, 'T e. V'); cca = A_(cc, CTY); cba = A_(cb, CBTY)
    faa = A_(fa, RATY); fba = A_(fb, RBTY); kka = A_(kk, 'K e. %s' % DG)
    jja = A_(jj, 'J e. %s' % DG); rra = A_(rr, 'R e. %s' % STMT_T)
    dda = A_(dd, 'D e. %s' % STK('T')); rdya = A_(rdy, '%s e. %s' % (RDY, STMT_T))
    d1a = A_(d1cl, '%s e. %s' % (D1, STK('T'))) if popA else dda
    nssa = A_(nss, 'N C_ %s' % S('T'))
    hra = A_(hr, 'A. m e. N %s' % HRB('m')); meqa = A_(meq, '( M ` A ) = %s' % BODY)
    if popA:
        dkka = A_(dkk, '( D ` K ) = %s' % ZX); zza = A_(zz, 'Z e. %s' % GK)
        xxa = A_(xx, 'X e. Word %s' % GK)
    if popB:
        dj2a = A_(dj2, '( %s ` J ) = %s' % (D1, ZXJ)); zba = A_(zb, "Z' e. %s" % GJ)
        xba = A_(xb, "X' e. Word %s" % GJ)
    rn = w.s([], 'simpr', '( %s -> r e. N )' % av)
    rs = w.s([nssa, rn], 'sseldd', '( %s -> r e. %s )' % (av, S('T')))
    cg, new = W.wcongr(w, HRB('m'), {'m': 'r'}, 'm = r',
                       {'m': w.s([], 'id', '( m = r -> m = r )')})
    assert new == HRB('r'), new
    trip = w.s([cg, hra, rn], 'rspcdva', '( %s -> %s )' % (av, HRB('r')))
    c1n = w.s([trip, w.inst('simp1')], 'syl', '( %s -> %s )' % (av, CA % 'r'))
    c2n = w.s([trip, w.inst('simp2')], 'syl', '( %s -> %s )' % (av, CB % V1('r')))
    vo = w.s([trip, w.inst('simp3')], 'syl', '( %s -> %s e. O )' % (av, V2('r')))
    # ---- the first operand
    ty1 = w.s([tva, cca, faa], '3jca', '( %s -> ( T e. V /\\ %s /\\ %s ) )' % (av, CTY, RATY))
    rd1 = w.s([rs, dda], 'jca', '( %s -> ( r e. %s /\\ D e. %s ) )' % (av, S('T'), STK('T')))
    kq1 = w.s([kka, rdya, rd1], '3jca',
              '( %s -> ( K e. %s /\\ %s e. %s /\\ ( r e. %s /\\ D e. %s ) ) )'
              % (av, DG, RDY, STMT_T, S('T'), STK('T')))
    ei1 = w.s([], 'eqid', '%s = %s' % (V1('r'), V1('r')))
    ei1a = w.s([ei1], 'a1i', '( %s -> %s = %s )' % (av, V1('r'), V1('r')))
    ei2 = w.s([], 'eqid', '%s = %s' % (D1, D1))
    ei2a = w.s([ei2], 'a1i', '( %s -> %s = %s )' % (av, D1, D1))
    DJ1i = ("( ( C ` r ) = 1o /\\ %s = r /\\ %s = D )" % (V1('r'), D1))
    DJ2i = ("( -. ( C ` r ) = 1o /\\ ( ( D ` K ) = %s /\\ Z e. %s /\\ X e. Word %s ) "
            "/\\ ( %s = ( F ` <. r , ( inl ` Z ) >. ) /\\ %s = %s ) )"
            % (ZX, GK, GK, V1('r'), D1, UPD('T', 'D', 'K', 'X')))
    if popA:
        sa1 = w.s([dkka, zza, xxa], '3jca',
                  '( %s -> ( ( D ` K ) = %s /\\ Z e. %s /\\ X e. Word %s ) )' % (av, ZX, GK, GK))
        eij = w.s([ei1a, ei2a], 'jca',
                  '( %s -> ( %s = ( F ` <. r , ( inl ` Z ) >. ) /\\ %s = %s ) )'
                  % (av, V1('r'), D1, UPD('T', 'D', 'K', 'X')))
        dis1 = w.s([c1n, sa1, eij], '3jca', '( %s -> %s )' % (av, DJ2i))
        or1 = w.s([dis1], 'olcd', '( %s -> ( %s \\/ %s ) )' % (av, DJ1i, DJ2i))
    else:
        dis1 = w.s([c1n, ei1a, ei2a], '3jca', '( %s -> %s )' % (av, DJ1i))
        or1 = w.s([dis1], 'orcd', '( %s -> ( %s \\/ %s ) )' % (av, DJ1i, DJ2i))
    ant1 = w.s([ty1, kq1, or1], '3jca', '( %s -> ( ( T e. V /\\ %s /\\ %s ) /\\ '
               '( K e. %s /\\ %s e. %s /\\ ( r e. %s /\\ D e. %s ) ) /\\ ( %s \\/ %s ) ) )'
               % (av, CTY, RATY, DG, RDY, STMT_T, S('T'), STK('T'), DJ1i, DJ2i))
    step1 = w.s([ant1, w.inst('tm2frd')], 'syl',
                '( %s -> ( %s %s <. r , D >. ) = ( %s %s <. %s , %s >. ) )'
                % (av, BODY, SA('T'), RDY, SA('T'), V1('r'), D1))
    # ---- the intermediate state is a state
    if popA:
        sev = w.s([], 'fvex', '%s e. _V' % S('T'))
        seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (av, S('T')))
        gev = w.s([], 'fvex', '%s e. _V' % GK)
        o1e = w.s([], '1oex', '1o e. _V')
        oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
        xev = w.s([sev, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
        xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (av, S('T'), OPT))
        rbi = w.s([seva, xeva, w.inst('elmapg')], 'syl2anc',
                  '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (av, RATY, S('T'), OPT, S('T')))
        rf = w.s([rbi, faa], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (av, S('T'), OPT, S('T')))
        zil = w.s([zza, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Z ) e. %s )' % (av, OPT))
        op1 = w.s([rs, zil], 'opelxpd',
                  '( %s -> <. r , ( inl ` Z ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        v1s = w.s([rf, op1], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, V1('r'), S('T')))
    else:
        v1s = rs
    # ---- the second operand
    ty2 = w.s([tva, cba, fba], '3jca', '( %s -> ( T e. V /\\ %s /\\ %s ) )' % (av, CBTY, RBTY))
    rd2 = w.s([v1s, d1a], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
              % (av, V1('r'), S('T'), D1, STK('T')))
    kq2 = w.s([jja, rra, rd2], '3jca',
              '( %s -> ( J e. %s /\\ R e. %s /\\ ( %s e. %s /\\ %s e. %s ) ) )'
              % (av, DG, STMT_T, V1('r'), S('T'), D1, STK('T')))
    fi1 = w.s([], 'eqid', '%s = %s' % (V2('r'), V2('r')))
    fi1a = w.s([fi1], 'a1i', '( %s -> %s = %s )' % (av, V2('r'), V2('r')))
    fi2 = w.s([], 'eqid', '%s = %s' % (D2, D2))
    fi2a = w.s([fi2], 'a1i', '( %s -> %s = %s )' % (av, D2, D2))
    EJ1i = ("( ( C' ` %s ) = 1o /\\ %s = %s /\\ %s = %s )" % (V1('r'), V2('r'), V1('r'), D2, D1))
    EJ2i = ("( -. ( C' ` %s ) = 1o /\\ ( ( %s ` J ) = %s /\\ Z' e. %s /\\ X' e. Word %s ) "
            "/\\ ( %s = ( F' ` <. %s , ( inl ` Z' ) >. ) /\\ %s = %s ) )"
            % (V1('r'), D1, ZXJ, GJ, GJ, V2('r'), V1('r'), D2, UPD('T', D1, 'J', "X'")))
    if popB:
        sa2 = w.s([dj2a, zba, xba], '3jca',
                  "( %s -> ( ( %s ` J ) = %s /\\ Z' e. %s /\\ X' e. Word %s ) )"
                  % (av, D1, ZXJ, GJ, GJ))
        fij = w.s([fi1a, fi2a], 'jca',
                  "( %s -> ( %s = ( F' ` <. %s , ( inl ` Z' ) >. ) /\\ %s = %s ) )"
                  % (av, V2('r'), V1('r'), D2, UPD('T', D1, 'J', "X'")))
        dis2 = w.s([c2n, sa2, fij], '3jca', '( %s -> %s )' % (av, EJ2i))
        or2 = w.s([dis2], 'olcd', '( %s -> ( %s \\/ %s ) )' % (av, EJ1i, EJ2i))
    else:
        dis2 = w.s([c2n, fi1a, fi2a], '3jca', '( %s -> %s )' % (av, EJ1i))
        or2 = w.s([dis2], 'orcd', '( %s -> ( %s \\/ %s ) )' % (av, EJ1i, EJ2i))
    ant2 = w.s([ty2, kq2, or2], '3jca', "( %s -> ( ( T e. V /\\ %s /\\ %s ) /\\ "
               '( J e. %s /\\ R e. %s /\\ ( %s e. %s /\\ %s e. %s ) ) /\\ ( %s \\/ %s ) ) )'
               % (av, CBTY, RBTY, DG, STMT_T, V1('r'), S('T'), D1, STK('T'), EJ1i, EJ2i))
    step2 = w.s([ant2, w.inst('tm2frd')], 'syl',
                '( %s -> ( %s %s <. %s , %s >. ) = ( R %s <. %s , %s >. ) )'
                % (av, RDY, SA('T'), V1('r'), D1, SA('T'), V2('r'), D2))
    tot = w.s([step1, step2], 'eqtrd', '( %s -> ( %s %s <. r , D >. ) = ( R %s <. %s , %s >. ) )'
              % (av, BODY, SA('T'), SA('T'), V2('r'), D2))
    o1 = w.s([meqa], 'oveq1d', '( %s -> %s = ( %s %s <. r , D >. ) )' % (av, MA('r'), BODY, SA('T')))
    tot2 = w.s([o1, tot], 'eqtrd', '( %s -> %s = ( R %s <. %s , %s >. ) )'
               % (av, MA('r'), SA('T'), V2('r'), D2))
    g1 = w.s([], 'opeq1', '( p = %s -> <. p , %s >. = <. %s , %s >. )' % (V2('r'), D2, V2('r'), D2))
    g2 = w.s([g1], 'oveq2d', '( p = %s -> ( R %s <. p , %s >. ) = ( R %s <. %s , %s >. ) )'
             % (V2('r'), SA('T'), D2, SA('T'), V2('r'), D2))
    g3 = w.s([g2], 'eqeq2d', '( p = %s -> ( %s = ( R %s <. p , %s >. ) <-> %s = ( R %s <. %s , %s >. ) ) )'
             % (V2('r'), MA('r'), SA('T'), D2, MA('r'), SA('T'), V2('r'), D2))
    g4 = w.s([g3], 'adantl',
             '( ( %s /\\ p = %s ) -> ( %s = ( R %s <. p , %s >. ) <-> %s = ( R %s <. %s , %s >. ) ) )'
             % (av, V2('r'), MA('r'), SA('T'), D2, MA('r'), SA('T'), V2('r'), D2))
    ex = w.s([vo, g4, tot2], 'rspcedvd', '( %s -> E. p e. O %s = ( R %s <. p , %s >. ) )'
             % (av, MA('r'), SA('T'), D2))
    w.qed([ex], 'ralrimiva', '( %s -> %s )' % (ph, GOAL2))
    return w.run()


if __name__ == '__main__':
    if want('tm2frd'): tm2frd()
    if want('tm2frd2'): frd2('tm2frd2', True, True)
    if want('tm2frd2a'): frd2('tm2frd2a', True, False)
    if want('tm2frd2b'): frd2('tm2frd2b', False, True)
    if want('tm2frd2c'): frd2('tm2frd2c', False, False)
