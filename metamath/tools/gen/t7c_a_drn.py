"""T7c: the fragment ` dropNum ` with the internal state confined to a class
` N ` closed under the pop handler (Lean's ` dropNum_runs ` read at a class:
the fields outside the read interface survive), on the pattern of
~ tm2fmvn1 / ~ tm2fmvnw / ~ tm2fmvn0 / ~ tm2fmvn and ~ tm2fdrop .

  tm2fdrn1   one iteration (pop a bit, branch true, back to the label)
  tm2fdrn0   the exit step (pop the terminator, branch false, to the exit)
  tm2fdrnw   the scan loop over the popped word (tm2hwrd)
  tm2fdropn  the fragment: ( # ` W ) + 1 steps, class N preserved

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_a_drn.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t2_lib import hstepcp
from t1_h_drop import (DG, GK, OPT, RATY, CTY, GA, GE, BR, STMT, TL, stmtty, constfty, STMT_T)

SEL = sys.argv[1:]

NSS = 'N C_ %s' % S('T')
def NV(r, z): return '( F ` <. %s , ( inl ` %s ) >. )' % (r, z)
HCN = 'A. r e. N A. z e. B ( ( C ` %s ) = 1o /\\ %s e. N )' % (NV('r', 'z'), NV('r', 'z'))
HEN = 'A. r e. N ( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NV('r', 'Y'), NV('r', 'Y'))
RY = '( <" Y "> ++ X )'


def PH1F(R):
    return ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ '
            '( ( %s /\\ %s ) /\\ ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
            % (PHM, STMT, L('T'), L('T'), DG, RATY, CTY, GK, R, GK, STK('T'), NSS, HCN))


PH1 = PH1F('R')
PH0 = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ K e. %s ) /\\ '
       '( ( %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
       % (PHM, STMT, L('T'), L('T'), DG, RATY, CTY, GK, GK, STK('T'), NSS, HEN))
JJ = ('( z e. Word B |-> ( { ( inl ` A ) } X. ( N X. { %s } ) ) )'
      % UPD('T', 'D', 'K', '( z ++ R )'))


def CLF(x, R='R', lab='A', X=None):
    X = X if X is not None else '( %s ++ %s )' % (x, R)
    return '( { ( inl ` %s ) } X. ( N X. { %s } ) )' % (lab, UPD('T', 'D', 'K', X))


def CL(x):
    return CLF(x, 'R')


def ctx1(w, ph, lift=None, PH=None, R='R'):
    """the components of PH1F(R) under ph"""
    PH = PH or PH1F(R)
    def g(ref, f):
        st = w.s([], ref, '( %s -> %s )' % (PH, f))
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    phm = g('simp1l', PHM)
    meq = g('simp1r', '( M ` A ) = %s' % STMT)
    g2 = g('simp2', '( A e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), DG))
    g3 = g('simp3', '( ( %s /\\ %s ) /\\ ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) /\\ ( %s /\\ %s ) )'
           % (RATY, CTY, GK, R, GK, STK('T'), NSS, HCN))
    al = w.s([g2, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([g2, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([g2, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    p1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    ra = w.s([p1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([p1], 'simprd', '( %s -> %s )' % (ph, CTY))
    p2 = w.s([g3, w.inst('simp2')], 'syl', '( %s -> ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) )'
             % (ph, GK, R, GK, STK('T')))
    bs = w.s([p2], 'simp1d', '( %s -> B C_ %s )' % (ph, GK))
    rw = w.s([p2], 'simp2d', '( %s -> %s e. Word %s )' % (ph, R, GK))
    dd = w.s([p2], 'simp3d', '( %s -> D e. %s )' % (ph, STK('T')))
    nh = w.s([g3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HCN))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    hc = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HCN))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, el=el, kk=kk, ra=ra, cc=cc, bs=bs, rw=rw, dd=dd, nss=nss, hc=hc, tv=tv,
                g2=g2, p1=p1, p2=p2, nh=nh)


def rfun(w, ph, ra):
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, S('T')))
    gev = w.s([], 'fvex', '%s e. _V' % GK)
    o1e = w.s([], '1oex', '1o e. _V')
    oev = w.s([gev, o1e, w.inst('djuex')], 'mp2an', '%s e. _V' % OPT)
    xev = w.s([sev, oev], 'xpex', '( %s X. %s ) e. _V' % (S('T'), OPT))
    xeva = w.s([xev], 'a1i', '( %s -> ( %s X. %s ) e. _V )' % (ph, S('T'), OPT))
    rbi = w.s([seva, xeva, w.inst('elmapg')], 'syl2anc',
              '( %s -> ( %s <-> F : ( %s X. %s ) --> %s ) )' % (ph, RATY, S('T'), OPT, S('T')))
    return w.s([rbi, ra], 'mpbid', '( %s -> F : ( %s X. %s ) --> %s )' % (ph, S('T'), OPT, S('T')))


def hc_at(w, av, vn, ZT, zcl, hca):
    """HCN at ( r := v , z := ZT ): ( C ` NV ) = 1o and NV e. N"""
    NVv = NV('v', ZT); NZ = NV('v', 'z'); RZ = NV('r', 'z')
    def pair(x): return '( ( C ` %s ) = 1o /\\ %s e. N )' % (x, x)
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` z ) >. = <. v , ( inl ` z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (RZ, NZ))
    i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (RZ, NZ))
    i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (RZ, NZ))
    i7 = w.s([i2], 'eleq1d', '( r = v -> ( %s e. N <-> %s e. N ) )' % (RZ, NZ))
    i8 = w.s([i4, i7], 'anbi12d', '( r = v -> ( %s <-> %s ) )' % (pair(RZ), pair(NZ)))
    i9 = w.s([i8], 'ralbidv', '( r = v -> ( A. z e. B %s <-> A. z e. B %s ) )' % (pair(RZ), pair(NZ)))
    h1 = w.s([i9, hca, vn], 'rspcdva', '( %s -> A. z e. B %s )' % (av, pair(NZ)))
    j1 = w.s([], 'fveq2', '( z = %s -> ( inl ` z ) = ( inl ` %s ) )' % (ZT, ZT))
    j2 = w.s([j1], 'opeq2d', '( z = %s -> <. v , ( inl ` z ) >. = <. v , ( inl ` %s ) >. )' % (ZT, ZT))
    j3 = w.s([j2], 'fveq2d', '( z = %s -> %s = %s )' % (ZT, NZ, NVv))
    j4 = w.s([j3], 'fveq2d', '( z = %s -> ( C ` %s ) = ( C ` %s ) )' % (ZT, NZ, NVv))
    j5 = w.s([j4], 'eqeq1d', '( z = %s -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (ZT, NZ, NVv))
    j8 = w.s([j3], 'eleq1d', '( z = %s -> ( %s e. N <-> %s e. N ) )' % (ZT, NZ, NVv))
    j9 = w.s([j5, j8], 'anbi12d', '( z = %s -> ( %s <-> %s ) )' % (ZT, pair(NZ), pair(NVv)))
    h2 = w.s([j9, h1, zcl], 'rspcdva', '( %s -> %s )' % (av, pair(NVv)))
    bc = w.s([h2], 'simpld', '( %s -> ( C ` %s ) = 1o )' % (av, NVv))
    nv = w.s([h2], 'simprd', '( %s -> %s e. N )' % (av, NVv))
    return bc, nv


def tm2fdrn1():
    lab = 'tm2fdrn1'
    ph = '( ( %s /\\ x e. Word B ) /\\ x =/= (/) )' % PH1
    UPD1 = UPD('T', 'D', 'K', '( x ++ R )')
    UPD2 = UPD('T', 'D', 'K', '( %s ++ R )' % TL('x'))
    NVx = NV('v', '( x ` 0 )')
    w = W(lab, 'One iteration of the fragment ` dropNum ` of TM/Prims.lean with the internal state confined to a '
               'class ` N ` closed under the pop handler: the label pops a letter of the scanned word, the branch '
               'is true, and the machine returns to the label with one letter less, the state still in ` N ` .  '
               'Lean: ` dropNum_loop ` , the ` cons ` case, read at a class (as ~ tm2fmvn1 for the mover).')
    u = ctx1(w, ph, 'ad2antrr')
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
    rf = rfun(w, ph, u['ra'])

    def body(av):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = L_(u['tv'], 'T e. V')
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = L_(u['nss'], NSS)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        kk = L_(u['kk'], 'K e. %s' % DG)
        ra = L_(u['ra'], RATY)
        u1 = L_(up1, '%s e. %s' % (UPD1, STK('T')))
        u2 = L_(up2, '%s e. %s' % (UPD2, STK('T')))
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
        aa = L_(u['al'], 'A e. %s' % L('T'))
        hcc = L_(u['hc'], HCN)
        c1v = w.s([c1], 'elexd', '( %s -> ( x ++ R ) e. _V )' % av)
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
        rc, nvn = hc_at(w, av, vn, '( x ` 0 )', x0b, hcc)
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NVx, S('T')))
        av2 = w.s([aa], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([av2, nvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = A )' % (av, CONSTF('T', 'A'), NVx))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '%s e. %s' % (UPD1, STK('T')): u1,
                 '%s e. %s' % (NVx, S('T')): nvcl, '%s e. %s' % (UPD2, STK('T')): u2,
                 'K e. %s' % DG: kk, RATY: ra, CTY: cc,
                 '%s e. %s' % (BR, STMT_T()): br, '%s e. %s' % (GA, STMT_T()): ga,
                 '%s e. %s' % (GE, STMT_T()): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'A'), L('T'), S('T')): fa}
        rules = {'( %s ` K )' % UPD1: ('( x ++ R )', rk),
                 '( ( x ++ R ) ` 0 )': ('( x ` 0 )', rfv),
                 TL('( x ++ R )'): ('( %s ++ R )' % TL('x'), rtl),
                 UPD('T', UPD1, 'K', '( %s ++ R )' % TL('x')): (UPD2, rup),
                 '( %s ` %s )' % (CONSTF('T', 'A'), NVx): ('A', rga)}
        ifr = {'( x ++ R ) = (/)': (False, cnn), '( C ` %s ) = 1o' % NVx: (True, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STMT, '<. v , %s >.' % UPD1)
        want_res = '<. ( inl ` A ) , <. %s , %s >. >.' % (NVx, UPD2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = w.s([u['meq']], 'adantr', '( %s -> ( M ` A ) = %s )' % (av, STMT))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), UPD1, STMT, SA('T'), UPD1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), UPD1, res))
        return fin, NVx, nvn
    hstepcp(w, ph, 'T', 'M', 'A', 'A', 'N', UPD1, UPD2, (u['meq'], u['phm']), u['al'], u['al'],
            u['nss'], up1, up2, body, qed=True)
    return w.run()


def tm2fdrn0():
    lab = 'tm2fdrn0'
    ph = PH0
    UPD1 = UPD('T', 'D', 'K', RY)
    UPD2 = UPD('T', 'D', 'K', 'X')
    NVy = NV('v', 'Y')
    w = W(lab, 'The exit step of the fragment ` dropNum ` of TM/Prims.lean with the internal state confined to a '
               'class ` N ` : the label pops the terminator, the branch is false, the machine jumps to the exit, '
               'the state still in ` N ` .  Lean: ` dropNum_loop ` , the ` nil ` case, read at a class.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STMT))
    g2 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )' % (ph, L('T'), L('T'), DG))
    al = w.s([g2, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([g2, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([g2, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, DG))
    g3 = w.s([], 'simp3', '( %s -> ( ( %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
             % (ph, RATY, CTY, GK, GK, STK('T'), NSS, HEN))
    q1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    ra = w.s([q1], 'simpld', '( %s -> %s )' % (ph, RATY))
    cc = w.s([q1], 'simprd', '( %s -> %s )' % (ph, CTY))
    q2 = w.s([g3, w.inst('simp2')], 'syl', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) )'
             % (ph, GK, GK, STK('T')))
    yy = w.s([q2], 'simp1d', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([q2], 'simp2d', '( %s -> X e. Word %s )' % (ph, GK))
    dd = w.s([q2], 'simp3d', '( %s -> D e. %s )' % (ph, STK('T')))
    nh = w.s([g3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HEN))
    nss = w.s([nh], 'simpld', '( %s -> %s )' % (ph, NSS))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HEN))
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

    def body(av):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = L_(tv, 'T e. V')
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = L_(nss, NSS)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        kka = L_(kk, 'K e. %s' % DG)
        raa = L_(ra, RATY)
        u1 = L_(up1, '%s e. %s' % (UPD1, STK('T')))
        u2 = L_(up2, '%s e. %s' % (UPD2, STK('T')))
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
        hea = L_(he, HEN)
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
        PAIR = '( -. ( C ` %s ) = 1o /\\ %s e. N )'
        i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` Y ) >. = <. v , ( inl ` Y ) >. )')
        i2 = w.s([i1], 'fveq2d', '( r = v -> %s = %s )' % (NV('r', 'Y'), NVy))
        i3 = w.s([i2], 'fveq2d', '( r = v -> ( C ` %s ) = ( C ` %s ) )' % (NV('r', 'Y'), NVy))
        i4 = w.s([i3], 'eqeq1d', '( r = v -> ( ( C ` %s ) = 1o <-> ( C ` %s ) = 1o ) )' % (NV('r', 'Y'), NVy))
        i5 = w.s([i4], 'notbid', '( r = v -> ( -. ( C ` %s ) = 1o <-> -. ( C ` %s ) = 1o ) )' % (NV('r', 'Y'), NVy))
        i6 = w.s([i2], 'eleq1d', '( r = v -> ( %s e. N <-> %s e. N ) )' % (NV('r', 'Y'), NVy))
        i7 = w.s([i5, i6], 'anbi12d', '( r = v -> ( %s <-> %s ) )'
                 % (PAIR % (NV('r', 'Y'), NV('r', 'Y')), PAIR % (NVy, NVy)))
        h2 = w.s([i7, hea, vn], 'rspcdva', '( %s -> %s )' % (av, PAIR % (NVy, NVy)))
        rc = w.s([h2], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (av, NVy))
        nvn = w.s([h2], 'simprd', '( %s -> %s e. N )' % (av, NVy))
        nvcl = w.s([nssa, nvn], 'sseldd', '( %s -> %s e. %s )' % (av, NVy, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NVy))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, '%s e. %s' % (UPD1, STK('T')): u1,
                 '%s e. %s' % (NVy, S('T')): nvcl, '%s e. %s' % (UPD2, STK('T')): u2,
                 'K e. %s' % DG: kka, RATY: raa, CTY: cca,
                 '%s e. %s' % (BR, STMT_T()): br, '%s e. %s' % (GA, STMT_T()): ga,
                 '%s e. %s' % (GE, STMT_T()): ge,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe}
        rules = {'( %s ` K )' % UPD1: (RY, rk),
                 '( %s ` 0 )' % RY: ('Y', rfv),
                 TL(RY): ('X', rtl),
                 UPD('T', UPD1, 'K', 'X'): (UPD2, rup),
                 '( %s ` %s )' % (CONSTF('T', 'E'), NVy): ('E', rge)}
        ifr = {'%s = (/)' % RY: (False, rnn), '( C ` %s ) = 1o' % NVy: (False, rc)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STMT, '<. v , %s >.' % UPD1)
        want_res = '<. ( inl ` E ) , <. %s , %s >. >.' % (NVy, UPD2)
        assert res == want_res, 'GOT %s\nWANT %s' % (res, want_res)
        meqa = w.s([meq], 'adantr', '( %s -> ( M ` A ) = %s )' % (av, STMT))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )'
                 % (av, SA('T'), UPD1, STMT, SA('T'), UPD1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), UPD1, res))
        return fin, NVy, nvn
    hstepcp(w, ph, 'T', 'M', 'A', 'E', 'N', UPD1, UPD2, (meq, phm), al, el, nss, up1, up2, body, qed=True)
    return w.run()


def clex(w, ante, Z):
    """( ante -> CL(Z) e. _V ) (N e. _V from N C_ S)"""
    a = w.s([], 'snex', '{ ( inl ` A ) } e. _V')
    aa = w.s([a], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ante)
    c = w.s([], 'snex', '{ %s } e. _V' % UPD('T', 'D', 'K', '( %s ++ R )' % Z))
    ca = w.s([c], 'a1i', '( %s -> { %s } e. _V )' % (ante, UPD('T', 'D', 'K', '( %s ++ R )' % Z)))
    return a, aa, c, ca


def jval(w, ante, Z, zcl, nex):
    """( ante -> ( JJ ` Z ) = CL(Z) ) for zcl : Z e. Word B, nex : ( ante -> N e. _V )"""
    sub, new = W.congr(w, CL('z'), {'z': Z}, 'z = %s' % Z,
                       {'z': w.s([], 'id', '( z = %s -> z = %s )' % (Z, Z))})
    assert new == CL(Z), new
    e = w.s([], 'eqid', '%s = %s' % (JJ, JJ))
    a, aa, c, ca = clex(w, ante, Z)
    xp1 = w.s([nex, ca, w.inst('xpexg')], 'syl2anc', '( %s -> ( N X. { %s } ) e. _V )'
              % (ante, UPD('T', 'D', 'K', '( %s ++ R )' % Z)))
    vea = w.s([aa, xp1, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ante, CL(Z)))
    st = w.s([sub, e], 'fvmptg', '( ( %s e. Word B /\\ %s e. _V ) -> ( %s ` %s ) = %s )'
             % (Z, CL(Z), JJ, Z, CL(Z)))
    return w.s([zcl, vea, st], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, JJ, Z, CL(Z)))


def nexf(w, ante, nss):
    sev = w.s([], 'fvex', '%s e. _V' % S('T'))
    seva = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ante, S('T')))
    return w.s([nss, seva, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ante)


def tm2fdrnw():
    lab = 'tm2fdrnw'
    ph = '( %s /\\ W e. Word B )' % PH1
    phx = '( %s /\\ x e. Word B )' % ph
    ante2 = '( %s /\\ x =/= (/) )' % phx
    HRx = HR('( %s ` x )' % JJ, 'T', 'M', '( %s ` %s )' % (JJ, TL('x')), '1')
    HYPJ = 'A. x e. Word B ( x =/= (/) -> %s )' % HRx
    w = W(lab, 'The scan loop of the fragment ` dropNum ` of TM/Prims.lean with the internal state confined to a '
               'class ` N ` : the label consumes the whole scanned word, one step per letter.  An instantiation of '
               '~ tm2hwrd ; the class rides in the family.')
    p1 = w.s([], 'simplll', '( %s -> %s )' % (ante2, PH1))
    xw2 = w.s([], 'simplr', '( %s -> x e. Word B )' % ante2)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ante2)
    j1 = w.s([p1, xw2], 'jca', '( %s -> ( %s /\\ x e. Word B ) )' % (ante2, PH1))
    j2 = w.s([j1, xn], 'jca', '( %s -> ( ( %s /\\ x e. Word B ) /\\ x =/= (/) ) )' % (ante2, PH1))
    one = w.s([j2, w.inst('tm2fdrn1')], 'syl', '( %s -> %s )'
              % (ante2, HR(CL('x'), 'T', 'M', CL(TL('x')), '1')))
    tlw2 = w.s([xw2, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (ante2, TL('x')))
    u2 = ctx1(w, ante2, 'ad3antrrr')
    nex2 = nexf(w, ante2, u2['nss'])
    jx = jval(w, ante2, 'x', xw2, nex2)
    jt = jval(w, ante2, TL('x'), tlw2, nex2)
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
    u = ctx1(w, ph, 'adantr')
    nex = nexf(w, ph, u['nss'])
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    j0 = jval(w, ph, '(/)', w0a, nex)
    cc0 = w.s([u['rw'], w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ R ) = R )' % ph)
    up0 = w.s([u['tv'], u['dd'], w.s([u['kk'], w.s([cc0, u['rw']], 'eqeltrd',
              '( %s -> ( (/) ++ R ) e. Word %s )' % (ph, GK))], 'jca',
              '( %s -> ( K e. %s /\\ ( (/) ++ R ) e. Word %s ) )' % (ph, DG, GK)),
              w.inst('tm2stkupd')], 'syl3anc',
              '( %s -> %s e. %s )' % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), STK('T')))
    sn0 = w.s([up0], 'snssd', '( %s -> { %s } C_ %s )' % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), STK('T')))
    x0 = w.s([u['nss'], sn0, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( N X. { %s } ) C_ ( %s X. %s ) )'
             % (ph, UPD('T', 'D', 'K', '( (/) ++ R )'), S('T'), STK('T')))
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
    jw = jval(w, ph, 'W', ww, nex)
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


EXTRA = '( Y e. %s /\\ X e. Word %s /\\ %s )' % (GK, GK, HEN)
PHD = '( ( %s /\\ %s ) /\\ W e. Word B )' % (PH1F(RY), EXTRA)
CA = '( { ( inl ` A ) } X. ( N X. { %s } ) )' % UPD('T', 'D', 'K', RY)
CE = '( { ( inl ` E ) } X. ( N X. { %s } ) )' % UPD('T', 'D', 'K', 'X')
CONCL_D = HR(CLF('W', RY), 'T', 'M', CE, '( ( # ` W ) + 1 )')


def tm2fdropn():
    lab = 'tm2fdropn'
    ph = PHD
    w = W(lab, 'The fragment ` dropNum ` of TM/Prims.lean with the internal state confined to a class ` N ` '
               'closed under the pop handler: the label pops the whole scanned word and its terminator and jumps '
               'to the exit in ` ( # ` W ) + 1 ` steps, and the state stays in ` N ` .  At '
               '` N = { r e. ( 2nd ` T ) | ( U ` r ) = O } ` it says the field ` U ` (Lean\'s ` flag ` after '
               '` isZero ` ) survives ` dropNum ` ; ~ tm2fdrop is the case ` N = ( 2nd ` T ) ` .')
    p1 = w.s([], 'simpll', '( %s -> %s )' % (ph, PH1F(RY)))
    ex = w.s([], 'simplr', '( %s -> %s )' % (ph, EXTRA))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ph)
    loop0 = w.s([p1, ww], 'jca', '( %s -> ( %s /\\ W e. Word B ) )' % (ph, PH1F(RY)))
    loop = w.s([loop0, w.inst('tm2fdrnw')], 'syl', '( %s -> %s )'
               % (ph, HR(CLF('W', RY), 'T', 'M', CLF('(/)', RY), '( # ` W )')))
    u = ctx1(w, ph, 'syl' if False else None, PH=PH1F(RY), R=RY) if False else None
    phm = w.s([p1, w.inst('simp1l')], 'syl', '( %s -> %s )' % (ph, PHM))
    meq = w.s([p1, w.inst('simp1r')], 'syl', '( %s -> ( M ` A ) = %s )' % (ph, STMT))
    g2 = w.s([p1, w.inst('simp2')], 'syl', '( %s -> ( A e. %s /\\ E e. %s /\\ K e. %s ) )'
             % (ph, L('T'), L('T'), DG))
    g3 = w.s([p1, w.inst('simp3')], 'syl',
             '( %s -> ( ( %s /\\ %s ) /\\ ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
             % (ph, RATY, CTY, GK, RY, GK, STK('T'), NSS, HCN))
    q1 = w.s([g3, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RATY, CTY))
    q2 = w.s([g3, w.inst('simp2')], 'syl', '( %s -> ( B C_ %s /\\ %s e. Word %s /\\ D e. %s ) )'
             % (ph, GK, RY, GK, STK('T')))
    dd = w.s([q2], 'simp3d', '( %s -> D e. %s )' % (ph, STK('T')))
    q3 = w.s([g3, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HCN))
    nss = w.s([q3], 'simpld', '( %s -> %s )' % (ph, NSS))
    yy = w.s([ex, w.inst('simp1')], 'syl', '( %s -> Y e. %s )' % (ph, GK))
    xx = w.s([ex, w.inst('simp2')], 'syl', '( %s -> X e. Word %s )' % (ph, GK))
    he = w.s([ex, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HEN))
    r1 = w.s([yy, xx, dd], '3jca', '( %s -> ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) )'
             % (ph, GK, GK, STK('T')))
    nhe = w.s([nss, he], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, NSS, HEN))
    r2 = w.s([q1, r1, nhe], '3jca',
             '( %s -> ( ( %s /\\ %s ) /\\ ( Y e. %s /\\ X e. Word %s /\\ D e. %s ) /\\ ( %s /\\ %s ) ) )'
             % (ph, RATY, CTY, GK, GK, STK('T'), NSS, HEN))
    r3 = w.s([phm, meq], 'jca', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM, STMT))
    r4 = w.s([r3, g2, r2], '3jca', '( %s -> %s )' % (ph, PH0))
    exit_ = w.s([r4, w.inst('tm2fdrn0')], 'syl', '( %s -> %s )' % (ph, HR(CA, 'T', 'M', CE, '1')))
    s1c = w.s([yy], 's1cld', '( %s -> <" Y "> e. Word %s )' % (ph, GK))
    ryw = w.s([s1c, xx, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, RY, GK))
    lid = w.s([ryw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, RY, RY))
    st, new = W.congr(w, CLF('(/)', RY), {}, ph, {}, rules={'( (/) ++ %s )' % RY: (RY, lid)})
    assert new == CA, new
    b1 = w.s([st], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CLF('(/)', RY), 'T', 'M', CE, '1'), HR(CA, 'T', 'M', CE, '1')))
    ex2 = w.s([b1, exit_], 'mpbird', '( %s -> %s )' % (ph, HR(CLF('(/)', RY), 'T', 'M', CE, '1')))
    w.qed([phm, loop, ex2], 'syl3anc', '( %s -> %s )' % (ph, CONCL_D))
    return w.run()


STMTS = {}


def _stmts():
    STMTS['tm2fdropn'] = '( %s -> %s )' % (PHD, CONCL_D)


_stmts()

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
