"""T1: the fragment `dropNum` of TM/Prims.lean (a pop-branch-goto scan loop)
as an instantiation of the fragment calculus."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GK = '( %s ` K )' % G('T')
ST = '( %s X. %s )' % (S('T'), STK('T'))
OPT = '( %s |_| 1o )' % GK
RATY = 'F e. ( %s ^m ( %s X. %s ) )' % (S('T'), S('T'), OPT)
CTY = 'C e. ( 2o ^m %s )' % S('T')
GA = GOTO(CONSTF('T', 'A'))
GE = GOTO(CONSTF('T', 'E'))
BR = BRANCH('C', GA, GE)
STMT = POP('K', 'F', BR)
TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)
def HCF(Bv='B'):
    return 'A. r e. %s A. z e. %s ( C ` ( F ` <. r , ( inl ` z ) >. ) ) = 1o' % (S('T'), Bv)


HC = HCF('B')
def PH1F(R, Bv='B'):
    return ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ '
            '( ( %s /\\ %s ) /\\ ( %s C_ %s /\\ %s e. Word %s /\\ D e. %s ) /\\ %s ) )'
            % (PHM, STMT, L('T'), L('T'), DG, RATY, CTY, Bv, GK, R, GK, STK('T'), HCF(Bv)))


PH1 = PH1F('R')
JJ = ('( z e. Word B |-> ( { ( inl ` A ) } X. ( %s X. { %s } ) ) )'
      % (S('T'), UPD('T', 'D', 'K', '( z ++ R )')))
def CLF(x, R='R'):
    return '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (S('T'), UPD('T', 'D', 'K', '( %s ++ %s )' % (x, R)))


def CL(x):
    return CLF(x, 'R')


def ctxsteps(w, ph, lift=None):
    """the components of PH1 under an antecedent ph reached from PH1 by `lift`"""
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH1, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    return {
        'phm': g('simp1l', PHM),
        'meq': g('simp1r', '( M ` A ) = %s' % STMT),
        'al': g('simp2l' if False else 'simp2', '( A e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), DG)),
        'p3': g('simp3', '( ( %s /\\ %s ) /\\ ( B C_ %s /\\ R e. Word %s /\\ D e. %s ) /\\ %s )'
                % (RATY, CTY, GK, GK, STK('T'), HC)),
    }


def unpack(w, ph, c):
    """A, E, K, RA, C, B, R, D, HC steps from the two grouped steps"""
    al = w.s([c['al'], w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([c['al'], w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([c['al'], w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    p1 = w.s([c['p3'], w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    ra = w.s([p1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([p1], 'simprd', '( %s -> %s )' % (ph, CTY))
    p2 = w.s([c['p3'], w.inst('simp2')], 'syl', '( %s -> ( B C_ %s /\\ R e. Word %s /\\ D e. %s ) )'
             % (ph, GK, GK, STK('T')))
    bs = w.s([p2], 'simp1d', '( %s -> B C_ %s )' % (ph, GK))
    rw = w.s([p2], 'simp2d', '( %s -> R e. Word %s )' % (ph, GK))
    dd = w.s([p2], 'simp3d', '( %s -> D e. %s )' % (ph, STK('T')))
    hc = w.s([c['p3'], w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HC))
    tv = w.s([c['phm'], w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(al=al, el=el, kk=kk, ra=ra, cc=cc, bs=bs, rw=rw, dd=dd, hc=hc, tv=tv,
                phm=c['phm'], meq=c['meq'])


def stmtty(w, ph, u):
    """the three statement typings of the fragment's code"""
    fa = constfty(w, ph, 'A', L('T'), u['al'])
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ga = w.s([u['tv'], fa, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GA, STMT_T()))
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T()))
    j = w.s([ga, ge], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )'
             % (ph, GA, STMT_T(), GE, STMT_T()))
    br = w.s([u['tv'], u['cc'], j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BR, STMT_T()))
    kj = w.s([u['kk'], u['ra']], 'jca', '( %s -> ( K e. %s /\\ %s ) )' % (ph, DG, RATY))
    pp = w.s([u['tv'], kj, br, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, STMT, STMT_T()))
    return dict(fa=fa, fe=fe, ga=ga, ge=ge, br=br, pop=pp)


def constfty(w, ante, X, COD, xcl):
    f = w.s([xcl, w.inst('fconst6g')], 'syl', '( %s -> %s : %s --> %s )' % (ante, CONSTF('T', X), S('T'), COD))
    c1 = w.s([], 'fvex', '%s e. _V' % COD)
    c1a = w.s([c1], 'a1i', '( %s -> %s e. _V )' % (ante, COD))
    c2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    c2a = w.s([c2], 'a1i', '( %s -> %s e. _V )' % (ante, S('T')))
    bi = w.s([c1a, c2a, w.inst('elmapg')], 'syl2anc',
             '( %s -> ( %s e. ( %s ^m %s ) <-> %s : %s --> %s ) )'
             % (ante, CONSTF('T', X), COD, S('T'), CONSTF('T', X), S('T'), COD))
    return w.s([bi, f], 'mpbird', '( %s -> %s e. ( %s ^m %s ) )' % (ante, CONSTF('T', X), COD, S('T')))


def STMT_T():
    return STMT_TT


STMT_TT = '( TM2Stmt ` T )'


def tm2fdrop1():
    lab = 'tm2fdrop1'
    ph = '( ( %s /\\ x e. Word B ) /\\ x =/= (/) )' % PH1
    UPD1 = UPD('T', 'D', 'K', '( x ++ R )')
    UPD2 = UPD('T', 'D', 'K', '( %s ++ R )' % TL('x'))
    NV = '( F ` <. v , ( inl ` ( x ` 0 ) ) >. )'
    w = W(lab, 'One iteration of the fragment ` dropNum ` of TM/Prims.lean: '
               'the label pops a symbol of the scanned word, the branch on the '
               'internal state is true, and the machine returns to the same '
               'label with one letter less on the stack.  Lean: '
               '` dropNum_loop ` , the ` cons ` case.')
    c = ctxsteps(w, ph, 'ad2antrr')
    u = unpack(w, ph, c)
    t = stmtty(w, ph, u)
    xw = w.s([], 'simplr', '( %s -> x e. Word B )' % ph)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ph)
    sw = w.s([u['bs'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GK))
    xwg = w.s([sw, xw], 'sseldd', '( %s -> x e. Word %s )' % (ph, GK))
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( x ` 0 ) e. B )' % ph)
    x0g = w.s([u['bs'], x0], 'sseldd', '( %s -> ( x ` 0 ) e. %s )' % (ph, GK))
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ph, TL('x')))
    tlwg = w.s([sw, tlw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, TL('x'), GK))
    cc1 = w.s([xwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> ( x ++ R ) e. Word %s )' % (ph, GK))
    cc2 = w.s([tlwg, u['rw'], w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ R ) e. Word %s )' % (ph, TL('x'), GK))
    ccn = w.s([xwg, xn, u['rw'], w.inst('ccatn0')], 'syl3anc', '( %s -> ( x ++ R ) =/= (/) )' % ph)
    k1 = w.s([u['kk'], cc1], 'jca', '( %s -> ( K e. %s /\\ ( x ++ R ) e. Word %s ) )' % (ph, DG, GK))
    k2 = w.s([u['kk'], cc2], 'jca', '( %s -> ( K e. %s /\\ ( %s ++ R ) e. Word %s ) )' % (ph, DG, TL('x'), GK))
    up1 = w.s([u['tv'], u['dd'], k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UPD1, STK('T')))
    up2 = w.s([u['tv'], u['dd'], k2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UPD2, STK('T')))
    # RA as a function
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    gev = w.s([], 'fvex', '%s e. _V' % GK)
    o1e = w.s([], '1oex', '1o e. _V')
    oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xev = w.s([sev, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
    xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (ph, S('T'), OPT))
    rbi = w.s([seva, xeva, w.inst('elmapg')], 'syl2anc',
              '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (ph, RATY, S('T'), OPT, S('T')))
    rf = w.s([rbi, u['ra']], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (ph, S('T'), OPT, S('T')))
    def body(av):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = L_(u['tv'], 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kk = L_(u['kk'], 'K e. %s' % DG)
        ra = L_(u['ra'], RATY)
        u1 = L_(up1, '%s e. %s' % (UPD1, STK('T')))
        u2 = L_(up2, '%s e. %s' % (UPD2, STK('T')))
        pop = L_(t['pop'], '%s e. %s' % (STMT, STMT_T()))
        br = L_(t['br'], '%s e. %s' % (BR, STMT_T()))
        ga = L_(t['ga'], '%s e. %s' % (GA, STMT_T()))
        ge = L_(t['ge'], '%s e. %s' % (GE, STMT_T()))
        cc = L_(u['cc'], CTY)
        fa = L_(t['fa'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')))
        dd = L_(u['dd'], 'D e. %s' % STK('T'))
        c1 = L_(cc1, '( x ++ R ) e. Word %s' % GK)
        c2 = L_(cc2, '( %s ++ R ) e. Word %s' % (TL('x'), GK))
        cn = L_(ccn, '( x ++ R ) =/= (/)')
        xg = L_(xwg, 'x e. Word %s' % GK)
        xn2 = L_(xn, 'x =/= (/)')
        rww = L_(u['rw'], 'R e. Word %s' % GK)
        x0b = L_(x0, '( x ` 0 ) e. B')
        x0gg = L_(x0g, '( x ` 0 ) e. %s' % GK)
        aa = L_(u['al'], 'A e. %s' % L('T'))
        rff = L_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        hcc = L_(u['hc'], HC)
        # the rewrite rules
        c1v = w.s([c1], 'elexd', '( %s -> ( x ++ R ) e. _V )' % av)
        c2v = w.s([c2], 'elexd', '( %s -> ( %s ++ R ) e. _V )' % (av, TL('x')))
        rk = updkval(w, av, 'T', 'D', 'K', '( x ++ R )', tv, dd, kk, c1v)
        cnn = w.s([cn], 'neneqd', '( %s -> -. ( x ++ R ) = (/) )' % av)
        nnx = w.s([xg, xn2, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` x ) e. NN )' % av)
        xpos = w.s([nnx, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` x ) )' % av)
        rfv = w.s([xg, rww, xpos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( ( x ++ R ) ` 0 ) = ( x ` 0 ) )' % av)
        rtl = w.s([xg, xn2, rww, w.inst('wrdtlcc')], 'syl3anc',
                  '( %s -> %s = ( %s ++ R ) )' % (av, TL('( x ++ R )'), TL('x')))
        p1 = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        p2 = w.s([c1, c2], 'jca', '( %s -> ( ( x ++ R ) e. Word %s /\\ ( %s ++ R ) e. Word %s ) )'
                 % (av, GK, TL('x'), GK))
        rup = w.s([p1, kk, p2, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', UPD1, 'K', '( %s ++ R )' % TL('x')), UPD2))
        # the new state and the branch condition
        dj = w.s([x0gg, w.inst('djulcl')], 'syl', '( %s -> ( inl ` ( x ` 0 ) ) e. %s )' % (av, OPT))
        pr = w.s([vv, dj], 'opelxpd', '( %s -> <. v , ( inl ` ( x ` 0 ) ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        nvcl = w.s([rff, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        # HC at r := v, z := ( x ` 0 )
        i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
        i2 = w.s([i1], 'fveq2d', '( r = v -> ( F ` <. r , ( inl ` z ) >. ) = ( F ` <. v , ( inl ` z ) >. ) )')
        i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` ( F ` <. r , ( inl ` z ) >. ) ) = ( C ` ( F ` <. v , ( inl ` z ) >. ) ) )')
        i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` ( F ` <. r , ( inl ` z ) >. ) ) = 1o <-> ( C ` ( F ` <. v , ( inl ` z ) >. ) ) = 1o ) )')
        i5 = w.s([i4], 'ralbidv', '( r = v -> ( A. z e. B ( C ` ( F ` <. r , ( inl ` z ) >. ) ) = 1o <-> A. z e. B ( C ` ( F ` <. v , ( inl ` z ) >. ) ) = 1o ) )')
        h1 = w.s([i5, hcc, vv], 'rspcdva', '( %s -> A. z e. B ( C ` ( F ` <. v , ( inl ` z ) >. ) ) = 1o )' % av)
        j1 = w.s([], 'fveq2', '( z = ( x ` 0 ) -> ( inl ` z ) = ( inl ` ( x ` 0 ) ) )')
        j2 = w.s([j1], 'opeq2d', '( z = ( x ` 0 ) -> <. v , ( inl ` z ) >. = <. v , ( inl ` ( x ` 0 ) ) >. )')
        j3 = w.s([j2], 'fveq2d', '( z = ( x ` 0 ) -> ( F ` <. v , ( inl ` z ) >. ) = %s )' % NV)
        j4 = w.s([j3], 'fveq2d', '( z = ( x ` 0 ) -> ( C ` ( F ` <. v , ( inl ` z ) >. ) ) = ( C ` %s ) )' % NV)
        j5 = w.s([j4], 'eqeq1d', '( z = ( x ` 0 ) -> ( ( C ` ( F ` <. v , ( inl ` z ) >. ) ) = 1o <-> ( C ` %s ) = 1o ) )' % NV)
        rc = w.s([j5, h1, x0b], 'rspcdva', '( %s -> ( C ` %s ) = 1o )' % (av, NV))
        av2 = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([av2, nvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NV))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '%s e. %s' % (UPD1, STK('T')): u1,
                 '%s e. %s' % (NV, S('T')): nvcl, '%s e. %s' % (UPD2, STK('T')): u2,
                 'K e. %s' % DG: kk, RATY: ra, CTY: cc,
                 '%s e. %s' % (BR, STMT_T()): br, '%s e. %s' % (GA, STMT_T()): ga,
                 '%s e. %s' % (GE, STMT_T()): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): fa}
        rules = {'( %s ` K )' % UPD1: ('( x ++ R )', rk),
                 '( ( x ++ R ) ` 0 )': ('( x ` 0 )', rfv),
                 TL('( x ++ R )'): ('( %s ++ R )' % TL('x'), rtl),
                 UPD('T', UPD1, 'K', '( %s ++ R )' % TL('x')): (UPD2, rup),
                 '( %s ` %s )' % (CONSTF('T', 'A'), NV): ('A', rga)}
        ifr = {'( x ++ R ) = (/)': (False, cnn), '( C ` %s ) = 1o' % NV: (True, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STMT, '<. v , %s >.' % UPD1)
        want_res = '<. ( inl ` A ) , <. %s , %s >. >.' % (NV, UPD2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = w.s([u['meq']], 'ad3antrrr' if False else 'adantr', '( %s -> ( M ` A ) = %s )' % (av, STMT))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), UPD1, STMT, SA('T'), UPD1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), UPD1, res))
        return fin, NV, nvcl
    aa1 = u['al']
    hstepc(w, ph, 'T', 'M', 'A', 'A', UPD1, UPD2, (u['meq'], u['phm']), aa1, aa1,
           up1, up2, body, qed=True)
    return w.run()


HE = 'A. r e. %s -. ( C ` ( F ` <. r , ( inl ` Y ) >. ) ) = 1o' % S('T')
RY = '( <" Y "> ++ X )'
PH0 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ '
       '( ( %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) /\\ %s ) )'
       % (PHM, STMT, L('T'), L('T'), DG, RATY, CTY, GK, GK, STK('T'), HE))


def tm2fdrop0():
    lab = 'tm2fdrop0'
    ph = PH0
    UPD1 = UPD('T', 'D', 'K', RY)
    UPD2 = UPD('T', 'D', 'K', 'X')
    C1 = '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (S('T'), UPD1)
    C2 = '( { ( inl ` E ) } X. ( %s X. { %s } ) )' % (S('T'), UPD2)
    NV = '( F ` <. v , ( inl ` Y ) >. )'
    w = W(lab, 'The exit step of the fragment ` dropNum ` of TM/Prims.lean: the '
               'label pops the terminator, the branch on the internal state is '
               'false, and the machine jumps to the exit.  Lean: '
               '` dropNum_loop ` , the ` nil ` case.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STMT))
    g2 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )' % (ph, L('T'), L('T'), DG))
    al = w.s([g2, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([g2, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([g2, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    g3 = w.s([], 'simp3', '( %s -> ( ( %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) /\\ %s ) )'
             % (ph, RATY, CTY, GK, GK, STK('T'), HE))
    q1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    ra = w.s([q1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([q1], 'simprd', '( %s -> %s )' % (ph, CTY))
    q2 = w.s([g3, w.inst('simp2')], 'syl', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) )'
             % (ph, GK, GK, STK('T')))
    yy = w.s([q2], 'simp1d', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([q2], 'simp2d', '( %s -> X e. Word %s )' % (ph, GK))
    dd = w.s([q2], 'simp3d', '( %s -> D e. %s )' % (ph, STK('T')))
    he = w.s([g3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    u = dict(al=al, el=el, kk=kk, ra=ra, cc=cc, dd=dd, tv=tv, phm=phm, meq=meq)
    t = stmtty(w, ph, u)
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    s1n = w.s([], 's1nz', '<" Y "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    ryw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    ryn = w.s([s1c, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, RY))
    k1 = w.s([kk, ryw], 'jca', '( %s -> ( K e. %s /\\ %s e. Word %s ) )' % (ph, DG, RY, GK))
    k2 = w.s([kk, xx], 'jca', '( %s -> ( K e. %s /\\ X e. Word %s ) )' % (ph, DG, GK))
    up1 = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UPD1, STK('T')))
    up2 = w.s([tv, dd, k2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UPD2, STK('T')))
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    gev = w.s([], 'fvex', '%s e. _V' % GK)
    o1e = w.s([], '1oex', '1o e. _V')
    oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xev = w.s([sev, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
    xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (ph, S('T'), OPT))
    rbi = w.s([seva, xeva, w.inst('elmapg')], 'syl2anc',
              '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (ph, RATY, S('T'), OPT, S('T')))
    rf = w.s([rbi, ra], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (ph, S('T'), OPT, S('T')))
    def body(av):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = L_(tv, 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kka = L_(kk, 'K e. %s' % DG)
        raa = L_(ra, RATY)
        u1 = L_(up1, '%s e. %s' % (UPD1, STK('T')))
        u2 = L_(up2, '%s e. %s' % (UPD2, STK('T')))
        pop = L_(t['pop'], '%s e. %s' % (STMT, STMT_T()))
        br = L_(t['br'], '%s e. %s' % (BR, STMT_T()))
        ga = L_(t['ga'], '%s e. %s' % (GA, STMT_T()))
        ge = L_(t['ge'], '%s e. %s' % (GE, STMT_T()))
        cca = L_(cc, CTY)
        fe = L_(t['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        dda = L_(dd, 'D e. %s' % STK('T'))
        yya = L_(yy, 'Y e. %s' % GK)
        xxa = L_(xx, 'X e. Word %s' % GK)
        rywa = L_(ryw, '%s e. Word %s' % (RY, GK))
        ryna = L_(ryn, '%s =/= (/)' % RY)
        ela = L_(el, 'E e. %s' % L('T'))
        rff = L_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        hea = L_(he, HE)
        ryv = w.s([rywa], 'elexd', '( %s -> %s e. _V )' % (av, RY))
        rk = updkval(w, av, 'T', 'D', 'K', RY, tva, dda, kka, ryv)
        rnn = w.s([ryna], 'neneqd', '( %s -> -. %s = (/) )' % (av, RY))
        yj = w.s([yya, xxa], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        rfv = w.s([yj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Y )' % (av, RY))
        rtl = w.s([yj, w.inst('wrdtls1')], 'syl', '( %s -> %s = X )' % (av, TL(RY)))
        p1 = w.s([tva, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        p2 = w.s([rywa, xxa], 'jca', '( %s -> ( %s e. Word %s /\\ X e. Word %s ) )' % (av, RY, GK, GK))
        rup = w.s([p1, kka, p2, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', UPD1, 'K', 'X'), UPD2))
        dj = w.s([yya, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. %s )' % (av, OPT))
        pr = w.s([vv, dj], 'opelxpd', '( %s -> <. v , ( inl ` Y ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        nvcl = w.s([rff, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` Y ) >. = <. v , ( inl ` Y ) >. )')
        i2 = w.s([i1], 'fveq2d', '( r = v -> ( F ` <. r , ( inl ` Y ) >. ) = %s )' % NV)
        i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` ( F ` <. r , ( inl ` Y ) >. ) ) = ( C ` %s ) )' % NV)
        i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` ( F ` <. r , ( inl ` Y ) >. ) ) = 1o <-> ( C ` %s ) = 1o ) )' % NV)
        i5 = w.s([i4], 'notbid', '( r = v -> ( -. ( C ` ( F ` <. r , ( inl ` Y ) >. ) ) = 1o <-> -. ( C ` %s ) = 1o ) )' % NV)
        rc = w.s([i5, hea, vv], 'rspcdva', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, '%s e. %s' % (UPD1, STK('T')): u1,
                 '%s e. %s' % (NV, S('T')): nvcl, '%s e. %s' % (UPD2, STK('T')): u2,
                 'K e. %s' % DG: kka, RATY: raa, CTY: cca,
                 '%s e. %s' % (BR, STMT_T()): br, '%s e. %s' % (GA, STMT_T()): ga,
                 '%s e. %s' % (GE, STMT_T()): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe}
        rules = {'( %s ` K )' % UPD1: (RY, rk),
                 '( %s ` 0 )' % RY: ('Y', rfv),
                 TL(RY): ('X', rtl),
                 UPD('T', UPD1, 'K', 'X'): (UPD2, rup),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NV): ('E', rge)}
        ifr = {'%s = (/)' % RY: (False, rnn), '( C ` %s ) = 1o' % NV: (False, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STMT, '<. v , %s >.' % UPD1)
        want_res = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV, UPD2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = w.s([meq], 'adantr', '( %s -> ( M ` A ) = %s )' % (av, STMT))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), UPD1, STMT, SA('T'), UPD1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), UPD1, res))
        return fin, NV, nvcl
    hstepc(w, ph, 'T', 'M', 'A', 'E', UPD1, UPD2, (meq, phm), al, el, up1, up2, body, qed=True)
    return w.run()




def clex(w, ante, Z):
    """( ante -> CL(Z) e. _V )"""
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    b = w.s([], 'fvex', '%s e. _V' % S('T'))
    c = w.s([], 'snex', '{ %s } e. _V' % UPD('T', 'D', 'K', '( %s ++ R )' % Z))
    d = w.s([b, c], 'xpex', '( %s X. { %s } ) e. _V' % (S('T'), UPD('T', 'D', 'K', '( %s ++ R )' % Z)))
    e = w.s([a, d], 'xpex', '%s e. _V' % CL(Z))
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, CL(Z)))


def jval(w, ante, Z, zcl):
    """( ante -> ( JJ ` Z ) = CL(Z) ) for a step zcl : Z e. Word B"""
    sub, new = W.congr(w, CL('z'), {'z': Z}, 'z = %s' % Z,
                       {'z': w.s([], 'id', '( z = %s -> z = %s )' % (Z, Z))})
    assert new == CL(Z), new
    e = w.s([], 'eqid', '%s = %s' % (JJ, JJ))
    vea = clex(w, ante, Z)
    st = w.s([sub, e], 'fvmptg', '( ( %s e. Word B /\\ %s e. _V ) -> ( %s ` %s ) = %s )'
             % (Z, CL(Z), JJ, Z, CL(Z)))
    return w.s([zcl, vea, st], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, JJ, Z, CL(Z)))


def tm2fdropw():
    lab = 'tm2fdropw'
    ph = '( %s /\\ W e. Word B )' % PH1
    phx = '( %s /\\ x e. Word B )' % ph
    ante2 = '( %s /\\ x =/= (/) )' % phx
    HRx = HR('( %s ` x )' % JJ, 'T', 'M', '( %s ` %s )' % (JJ, TL('x')), '1')
    HYPJ = 'A. x e. Word B ( x =/= (/) -> %s )' % HRx
    w = W(lab, 'The scan loop of the fragment ` dropNum ` of TM/Prims.lean: the '
               'label consumes the whole scanned word, one step per letter.  An '
               'instantiation of ~ tm2hwrd , which does once and for all the '
               'induction Lean\'s ` dropNum_loop ` does by hand.')
    # the iteration hypothesis
    p1 = w.s([], 'simplll', '( %s -> %s )' % (ante2, PH1))
    xw2 = w.s([], 'simplr', '( %s -> x e. Word B )' % ante2)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    j1 = w.s([p1, xw2], 'jca', '( %s -> ( %s /\\ x e. Word B ) )' % (ante2, PH1))
    j2 = w.s([j1, xn], 'jca', '( %s -> ( ( %s /\\ x e. Word B ) /\\ x =/= (/) ) )' % (ante2, PH1))
    one = w.s([j2, w.inst('tm2fdrop1')], 'syl', '( %s -> %s )'
              % (ante2, HR(CL('x'), 'T', 'M', CL(TL('x')), '1')))
    tlw2 = w.s([xw2, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    jx = jval(w, ante2, 'x', xw2)
    jt = jval(w, ante2, TL('x'), tlw2)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` %s ) , 1 >. = <. %s , 1 >. )' % (ante2, JJ, TL('x'), CL(TL('x'))))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HR(CL('x'), 'T', 'M', '( %s ` %s )' % (JJ, TL('x')), '1'),
                HR(CL('x'), 'T', 'M', CL(TL('x')), '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (ante2, HR(CL('x'), 'T', 'M', '( %s ` %s )' % (JJ, TL('x')), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ante2, HRx, HR(CL('x'), 'T', 'M', '( %s ` %s )' % (JJ, TL('x')), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    hyp = w.s([ex1], 'ralrimiva', '( %s -> %s )' % (ph, HYPJ))
    # the context at ph
    c = ctxsteps(w, ph, 'adantr')
    u = unpack(w, ph, c)
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    j0 = jval(w, ph, '(/)', w0a)
    sw = w.s([u['bs'], w.inst('sswrd')], 'syl', '( %s -> Word B C_ Word %s )' % (ph, GK))
    wwg = w.s([sw, ww], 'sseldd', '( %s -> W e. Word %s )' % (ph, GK))
    cc0 = w.s([u['rw'], w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ R ) = R )' % ph)
    cc0c = w.s([cc0], 'eqcomd', '( %s -> R = ( (/) ++ R ) )' % ph)
    up0 = w.s([u['tv'], u['dd'], w.s([u['kk'], w.s([cc0, u['rw']], 'eqeltrd',
              '( %s -> ( (/) ++ R ) e. Word %s )' % (ph, GK))], 'jca',
              '( %s -> ( K e. %s /\\ ( (/) ++ R ) e. Word %s ) )' % (ph, DG, GK)),
              w.inst('tm2stkupd')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), STK('T')))
    sn0 = w.s([up0], 'snssd', '( %s -> { %s } C_ %s )' % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), STK('T')))
    ssr = w.s([], 'ssid', '%s C_ %s' % (S('T'), S('T')))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (ph, S('T'), S('T')))
    x0 = w.s([ssra, sn0, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ ( %s X. %s ) )'
             % (ph, S('T'), UPD('T', 'D', 'K', '( (/) ++ R )'), S('T'), STK('T')))
    cl0 = w.s([u['tv'], u['al'], x0, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ph, CL('(/)'), CFG('T')))
    j0ss = w.s([j0, cl0], 'eqsstrd', '( %s -> ( %s ` (/) ) C_ %s )' % (ph, JJ, CFG('T')))
    n1 = w.s([], '1nn0', '1 e. NN0')
    n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([n1a, j0ss], 'jca', '( %s -> ( 1 e. NN0 /\\ ( %s ` (/) ) C_ %s ) )' % (ph, JJ, CFG('T')))
    ant = w.s([u['phm'], pj, hyp], '3jca',
              '( %s -> ( %s /\\ ( 1 e. NN0 /\\ ( %s ` (/) ) C_ %s ) /\\ %s ) )' % (ph, PHM, JJ, CFG('T'), HYPJ))
    ant2 = w.s([ant, ww], 'jca',
               '( %s -> ( ( %s /\\ ( 1 e. NN0 /\\ ( %s ` (/) ) C_ %s ) /\\ %s ) /\\ W e. Word B ) )'
               % (ph, PHM, JJ, CFG('T'), HYPJ))
    run = w.s([ant2, w.inst('tm2hwrd')], 'syl', '( %s -> %s )'
              % (ph, HR('( %s ` W )' % JJ, 'T', 'M', '( %s ` (/) )' % JJ, '( ( # ` W ) x. 1 )')))
    # unfold the family and the bound
    jw = jval(w, ph, 'W', ww)
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    q1 = w.s([j0, m1], 'opeq12d', '( %s -> <. ( %s ` (/) ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )' % (ph, JJ, CL('(/)')))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` W )' % JJ, 'T', 'M', '( %s ` (/) )' % JJ, '( ( # ` W ) x. 1 )'),
                HR('( %s ` W )' % JJ, 'T', 'M', CL('(/)'), '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )' % (ph, HR('( %s ` W )' % JJ, 'T', 'M', CL('(/)'), '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` W )' % JJ, 'T', 'M', CL('(/)'), '( # ` W )'),
                HR(CL('W'), 'T', 'M', CL('(/)'), '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )' % (ph, HR(CL('W'), 'T', 'M', CL('(/)'), '( # ` W )')))
    return w.run()


def tm2fdrop():
    lab = 'tm2fdrop'
    EXTRA = '( Y e. %s /\\ X e. Word %s /\\ %s )' % (GK, GK, HE)
    ph = '( ( %s /\\ %s ) /\\ W e. Word B )' % (PH1F(RY), EXTRA)
    UPD1 = UPD('T', 'D', 'K', RY)
    UPD2 = UPD('T', 'D', 'K', 'X')
    CA = '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (S('T'), UPD1)
    CE = '( { ( inl ` E ) } X. ( %s X. { %s } ) )' % (S('T'), UPD2)
    w = W(lab, 'The fragment ` dropNum ` of TM/Prims.lean: the label pops the '
               'whole scanned word and its terminator and jumps to the exit, in '
               '` ( # ` W ) + 1 ` steps --- Lean\'s ` dropNum_runs ` bound '
               '` l.length + 1 ` .  Two one-step lemmas, ~ tm2hwrd and '
               '~ tm2hseq .')
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ph, PH1F(RY)))
    ex = w.s([], 'simplr', '( %s -> %s )' % (ph, EXTRA))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    loop0 = w.s([p1, ww], 'jca', '( %s -> ( %s /\\ W e. Word B ) )' % (ph, PH1F(RY)))
    loop = w.s([loop0, w.inst('tm2fdropw')], 'syl', '( %s -> %s )'
               % (ph, HR(CLF('W', RY), 'T', 'M', CLF('(/)', RY), '( # ` W )')))
    # the exit step
    phm = w.s([p1, w.inst('simp1l')], 'syl', '( %s -> %s )' % (ph, PHM))
    meq = w.s([p1, w.inst('simp1r')], 'syl', '( %s -> ( M ` A ) = %s )' % (ph, STMT))
    g2 = w.s([p1, w.inst('simp2')], 'syl', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )'
             % (ph, L('T'), L('T'), DG))
    g3 = w.s([p1, w.inst('simp3')], 'syl',
             '( %s -> ( ( %s /\\ %s ) /\\ ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) /\\ %s ) )'
             % (ph, RATY, CTY, GK, RY, GK, STK('T'), HC))
    q1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    q2 = w.s([g3, w.inst('simp2')], 'syl', '( %s -> ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) )'
             % (ph, GK, RY, GK, STK('T')))
    dd = w.s([q2], 'simp3d', '( %s -> D e. %s )' % (ph, STK('T')))
    yy = w.s([ex, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([ex, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    he = w.s([ex, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HE))
    r1 = w.s([yy, xx, dd], '3jca', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) )'
             % (ph, GK, GK, STK('T')))
    r2 = w.s([q1, r1, he], '3jca',
             '( %s -> ( ( %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) /\\ %s ) )'
             % (ph, RATY, CTY, GK, GK, STK('T'), HE))
    r3 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STMT))
    r4 = w.s([r3, g2, r2], '3jca', '( %s -> %s )' % (ph, PH0))
    exit_ = w.s([r4, w.inst('tm2fdrop0')], 'syl', '( %s -> %s )' % (ph, HR(CA, 'T', 'M', CE, '1')))
    # ( (/) ++ RY ) = RY
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    ryw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    lid = w.s([ryw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, RY, RY))
    st, new = W.congr(w, CLF('(/)', RY), {}, ph, {}, rules={'( (/) ++ %s )' % RY: (RY, lid)})
    assert new == CA, new
    b1 = w.s([st], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CLF('(/)', RY), 'T', 'M', CE, '1'), HR(CA, 'T', 'M', CE, '1')))
    ex2 = w.s([b1, exit_], 'mpbird', '( %s -> %s )' % (ph, HR(CLF('(/)', RY), 'T', 'M', CE, '1')))
    w.qed([phm, loop, ex2], 'tm2hseq' if False else 'syl3anc', '( %s -> %s )'
          % (ph, HR(CLF('W', RY), 'T', 'M', CE, '( ( # ` W ) + 1 )')))
    return w.run()


HZ = 'A. r e. %s -. ( C ` ( F ` <. r , ( inr ` (/) ) >. ) ) = 1o' % S('T')
PHZ = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ '
       '( ( %s /\\ %s ) /\\ D e. %s /\\ %s ) )'
       % (PHM, STMT, L('T'), L('T'), DG, RATY, CTY, STK('T'), HZ))


def tm2fclr0():
    lab = 'tm2fclr0'
    ph = PHZ
    UPD1 = UPD('T', 'D', 'K', '(/)')
    C1 = '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (S('T'), UPD1)
    NV = '( F ` <. v , ( inr ` (/) ) >. )'
    w = W(lab, 'The exit step of the fragment ` clear ` of TM/Prims.lean: the '
               'label pops an empty stack, the branch on the internal state is '
               'false, and the machine jumps to the exit.  Lean: '
               '` clear_loop ` , the ` nil ` case.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STMT))
    g2 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )' % (ph, L('T'), L('T'), DG))
    al = w.s([g2, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([g2, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([g2, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    g3 = w.s([], 'simp3', '( %s -> ( ( %s /\\ %s ) /\\ D e. %s /\\ %s ) )' % (ph, RATY, CTY, STK('T'), HZ))
    q1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    ra = w.s([q1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([q1], 'simprd', '( %s -> %s )' % (ph, CTY))
    dd = w.s([g3, w.inst('simp2')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    hz = w.s([g3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HZ))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    u = dict(al=al, el=el, kk=kk, ra=ra, cc=cc, dd=dd, tv=tv, phm=phm, meq=meq)
    t = stmtty(w, ph, u)
    w0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word %s )' % (ph, GK))
    k1 = w.s([kk, w0a], 'jca', '( %s -> ( K e. %s /\\ (/) e. Word %s ) )' % (ph, DG, GK))
    up1 = w.s([tv, dd, k1, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UPD1, STK('T')))
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    gev = w.s([], 'fvex', '%s e. _V' % GK)
    o1e = w.s([], '1oex', '1o e. _V')
    oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xev = w.s([sev, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
    xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (ph, S('T'), OPT))
    rbi = w.s([seva, xeva, w.inst('elmapg')], 'syl2anc',
              '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (ph, RATY, S('T'), OPT, S('T')))
    rf = w.s([rbi, ra], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (ph, S('T'), OPT, S('T')))
    def body(av):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = L_(tv, 'T e. V')
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        kka = L_(kk, 'K e. %s' % DG)
        raa = L_(ra, RATY)
        u1 = L_(up1, '%s e. %s' % (UPD1, STK('T')))
        br = L_(t['br'], '%s e. %s' % (BR, STMT_T()))
        ga = L_(t['ga'], '%s e. %s' % (GA, STMT_T()))
        ge = L_(t['ge'], '%s e. %s' % (GE, STMT_T()))
        cca = L_(cc, CTY)
        fe = L_(t['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        dda = L_(dd, 'D e. %s' % STK('T'))
        ela = L_(el, 'E e. %s' % L('T'))
        rff = L_(rf, 'F : ( %s X. %s ) --> %s' % (S('T'), OPT, S('T')))
        hza = L_(hz, HZ)
        w0b = L_(w0a, '(/) e. Word %s' % GK)
        z0 = w.s([], '0ex', '(/) e. _V')
        z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % av)
        rk = updkval(w, av, 'T', 'D', 'K', '(/)', tva, dda, kka, z0a)
        # the head of an empty stack is none
        eqz = w.s([], 'eqid', '(/) = (/)')
        eqza = w.s([eqz], 'a1i', '( %s -> (/) = (/) )' % av)
        # the tail of the empty word
        sw0 = w.s([], 'swrd0', '( (/) substr <. 1 , ( # ` (/) ) >. ) = (/)')
        sw0a = w.s([sw0], 'a1i', '( %s -> ( (/) substr <. 1 , ( # ` (/) ) >. ) = (/) )' % av)
        p1 = w.s([tva, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK('T')))
        p2 = w.s([w0b, w0b], 'jca', '( %s -> ( (/) e. Word %s /\\ (/) e. Word %s ) )' % (av, GK, GK))
        rup = w.s([p1, kka, p2, w.inst('tm2stkup2')], 'syl3anc',
                  '( %s -> %s = %s )' % (av, UPD('T', UPD1, 'K', '(/)'), UPD1))
        dj = w.s([], '0lt1o', '(/) e. 1o')
        djr = w.s([dj, w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. %s' % OPT)
        djra = w.s([djr], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (av, OPT))
        pr = w.s([vv, djra], 'opelxpd', '( %s -> <. v , ( inr ` (/) ) >. e. ( %s X. %s ) )' % (av, S('T'), OPT))
        nvcl = w.s([rff, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV, S('T')))
        i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inr ` (/) ) >. = <. v , ( inr ` (/) ) >. )')
        i2 = w.s([i1], 'fveq2d', '( r = v -> ( F ` <. r , ( inr ` (/) ) >. ) = %s )' % NV)
        i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` ( F ` <. r , ( inr ` (/) ) >. ) ) = ( C ` %s ) )' % NV)
        i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` ( F ` <. r , ( inr ` (/) ) >. ) ) = 1o <-> ( C ` %s ) = 1o ) )' % NV)
        i5 = w.s([i4], 'notbid', '( r = v -> ( -. ( C ` ( F ` <. r , ( inr ` (/) ) >. ) ) = 1o <-> -. ( C ` %s ) = 1o ) )' % NV)
        rc = w.s([i5, hza, vv], 'rspcdva', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NV))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, '%s e. %s' % (UPD1, STK('T')): u1,
                 '%s e. %s' % (NV, S('T')): nvcl,
                 'K e. %s' % DG: kka, RATY: raa, CTY: cca,
                 '%s e. %s' % (BR, STMT_T()): br, '%s e. %s' % (GA, STMT_T()): ga,
                 '%s e. %s' % (GE, STMT_T()): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe}
        rules = {'( %s ` K )' % UPD1: ('(/)', rk),
                 '( (/) substr <. 1 , ( # ` (/) ) >. )': ('(/)', sw0a),
                 UPD('T', UPD1, 'K', '(/)'): (UPD1, rup),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NV): ('E', rge)}
        ifr = {'( C ` %s ) = 1o' % NV: (False, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STMT, '<. v , %s >.' % UPD1)
        want_res = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV, UPD1)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = w.s([meq], 'adantr', '( %s -> ( M ` A ) = %s )' % (av, STMT))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), UPD1, STMT, SA('T'), UPD1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), UPD1, res))
        return fin, NV, nvcl
    hstepc(w, ph, 'T', 'M', 'A', 'E', UPD1, UPD1, (meq, phm), al, el, up1, up1, body, qed=True)
    return w.run()


def tm2fclr():
    lab = 'tm2fclr'
    HCK = HCF(GK)
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ '
          '( ( %s /\\ %s ) /\\ D e. %s /\\ ( %s /\\ %s ) ) )'
          % (PHM, STMT, L('T'), L('T'), DG, RATY, CTY, STK('T'), HCK, HZ))
    DK = '( D ` K )'
    UPD0 = UPD('T', 'D', 'K', '(/)')
    CA = '( { ( inl ` A ) } X. ( %s X. { D } ) )' % S('T')
    CZ = '( { ( inl ` A ) } X. ( %s X. { %s } ) )' % (S('T'), UPD0)
    CE = '( { ( inl ` E ) } X. ( %s X. { %s } ) )' % (S('T'), UPD0)
    w = W(lab, 'The fragment ` clear ` of TM/Prims.lean: the label empties '
               'stack ` K ` and jumps to the exit, in '
               '` ( # ` ( D ` K ) ) + 1 ` steps --- Lean\'s ` clear_runs ` bound '
               '` ( S k ).length + 1 ` .  Its scan loop is ~ tm2fdropw at '
               '` B = ( G ` K ) ` and no terminator, so only the exit step '
               '~ tm2fclr0 is new: a second fragment in the same family costs '
               'two theorems, not four.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STMT))
    g2 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )' % (ph, L('T'), L('T'), DG))
    kk = w.s([g2, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    g3 = w.s([], 'simp3', '( %s -> ( ( %s /\\ %s ) /\\ D e. %s /\\ ( %s /\\ %s ) ) )'
             % (ph, RATY, CTY, STK('T'), HCK, HZ))
    q1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    dd = w.s([g3, w.inst('simp2')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    q3 = w.s([g3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, HCK, HZ))
    hck = w.s([q3], 'simpld', '( %s -> %s )' % (ph, HCK))
    hz = w.s([q3], 'simprd', '( %s -> %s )' % (ph, HZ))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    # the loop, at B := ( G ` K ) and no terminator
    ssi = w.s([], 'ssid', '%s C_ %s' % (GK, GK))
    ssia = w.s([ssi], 'a1i', '( %s -> %s C_ %s )' % (ph, GK, GK))
    w0 = w.s([], 'wrd0', '(/) e. Word %s' % GK)
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word %s )' % (ph, GK))
    t1 = w.s([ssia, w0a, dd], '3jca', '( %s -> ( %s C_ %s /\\ (/) e. Word %s /\\ D e. %s ) )'
             % (ph, GK, GK, GK, STK('T')))
    t2 = w.s([q1, t1, hck], '3jca',
             '( %s -> ( ( %s /\\ %s ) /\\ ( %s C_ %s /\\ (/) e. Word %s /\\ D e. %s ) /\\ %s ) )'
             % (ph, RATY, CTY, GK, GK, GK, STK('T'), HCK))
    t3 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STMT))
    t4 = w.s([t3, g2, t2], '3jca', '( %s -> %s )' % (ph, PH1F('(/)', GK)))
    dk = w.s([tv, dd, kk, w.inst('tm2stkfv')], 'syl3anc', '( %s -> %s e. Word %s )' % (ph, DK, GK))
    t5 = w.s([t4, dk], 'jca', '( %s -> ( %s /\\ %s e. Word %s ) )' % (ph, PH1F('(/)', GK), DK, GK))
    loop = w.s([t5, w.inst('tm2fdropw')], 'syl', '( %s -> %s )'
               % (ph, HR(CLF(DK, '(/)'), 'T', 'M', CLF('(/)', '(/)'), '( # ` %s )' % DK)))
    # ( ( D ` K ) ++ (/) ) = ( D ` K ) and UPD(D,K,( D ` K )) = D
    rid = w.s([dk, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, DK, DK))
    upi = w.s([tv, dd, kk, w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = D )' % (ph, UPD('T', 'D', 'K', DK)))
    tbl1 = {'( %s ++ (/) )' % DK: (DK, rid), UPD('T', 'D', 'K', DK): ('D', upi)}
    c1, n1 = evaluate(w, ph, CLF(DK, '(/)'), {}, extra_rules=(lambda n: tbl1.get(n.text())))
    assert n1 == CA, n1
    rid0 = w.s([w0a, w.inst('ccatrid')], 'syl', '( %s -> ( (/) ++ (/) ) = (/) )' % ph)
    tbl2 = {'( (/) ++ (/) )': ('(/)', rid0)}
    c2, n2 = evaluate(w, ph, CLF('(/)', '(/)'), {}, extra_rules=(lambda n: tbl2.get(n.text())))
    assert n2 == CZ, n2
    o1 = w.s([c2], 'opeq1d', '( %s -> <. %s , ( # ` %s ) >. = <. %s , ( # ` %s ) >. )'
             % (ph, CLF('(/)', '(/)'), DK, CZ, DK))
    b1 = w.s([c1, o1], 'breq12d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CLF(DK, '(/)'), 'T', 'M', CLF('(/)', '(/)'), '( # ` %s )' % DK),
                HR(CA, 'T', 'M', CZ, '( # ` %s )' % DK)))
    loop2 = w.s([b1, loop], 'mpbid', '( %s -> %s )' % (ph, HR(CA, 'T', 'M', CZ, '( # ` %s )' % DK)))
    # the exit step
    e1 = w.s([q1, dd, hz], '3jca', '( %s -> ( ( %s /\\ %s ) /\\ D e. %s /\\ %s ) )'
             % (ph, RATY, CTY, STK('T'), HZ))
    e2 = w.s([t3, g2, e1], '3jca', '( %s -> %s )' % (ph, PHZ))
    exit_ = w.s([e2, w.inst('tm2fclr0')], 'syl', '( %s -> %s )' % (ph, HR(CZ, 'T', 'M', CE, '1')))
    w.qed([phm, loop2, exit_], 'syl3anc', '( %s -> %s )'
          % (ph, HR(CA, 'T', 'M', CE, '( ( # ` %s ) + 1 )' % DK)))
    return w.run()


if __name__ == '__main__':
    if want('tm2fdrop1'): tm2fdrop1()
    if want('tm2fdrop0'): tm2fdrop0()
    if want('tm2fdropw'): tm2fdropw()
    if want('tm2fdrop'): tm2fdrop()
    if want('tm2fclr0'): tm2fclr0()
    if want('tm2fclr'): tm2fclr()
