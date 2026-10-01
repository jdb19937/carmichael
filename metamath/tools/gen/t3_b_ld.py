"""T3: the straight-line steps `load ; goto` and `load ; push ; goto` --- the
initialisation labels of `addLoop`, `subLoop`, `cmpFrag` and Lean's
`Frag.load'` (blueprint 2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GI = '( %s ` I )' % G('T')
STMT_T = '( TM2Stmt ` T )'
LTY = 'F e. ( %s ^m %s )' % (S('T'), S('T'))
GE = GOTO(CONSTF('T', 'E'))
NSS = "( N C_ %s /\\ N' C_ %s )" % (S('T'), S('T'))
HCL = "A. r e. N ( F ` r ) e. N'"


def base(w, ph, STM, extra):
    """the common context of both lemmas"""
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    lab = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ D e. %s ) )'
              % (ph, L('T'), L('T'), STK('T')))
    al = w.s([lab, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lab, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    dd = w.s([lab, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    p3 = w.s([], 'simp3', '( %s -> %s )' % (ph, extra))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    return dict(phm=phm, meq=meq, al=al, el=el, dd=dd, p3=p3, tv=tv)


def fvn(w, av, ncl):
    """( av -> ( F ` v ) e. N' ) from ncl : ( av -> A. r e. N ( F ` r ) e. N' )
    and v e. N"""
    vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
    i1 = w.s([], 'fveq2', '( r = v -> ( F ` r ) = ( F ` v ) )')
    i2 = w.s([i1], 'eleq1d', "( r = v -> ( ( F ` r ) e. N' <-> ( F ` v ) e. N' ) )")
    return vn, w.s([i2, ncl, vn], 'rspcdva', "( %s -> ( F ` v ) e. N' )" % av)


def tm2flg():
    lab = 'tm2flg'
    STM = LOAD('F', GE)
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ D e. %s ) '
          '/\\ ( %s /\\ %s /\\ %s ) )' % (PHM, STM, L('T'), L('T'), STK('T'), LTY, NSS, HCL))
    w = W(lab, 'The step ` load F ( goto E ) ` : the internal state moves by '
               '` F ` from a class ` N ` into a class ` N\' ` and the stacks are '
               'untouched.  Lean: ` Frag.load\'_runs ` , and the entry label of '
               '` cmpFrag ` .')
    u = base(w, ph, STM, '( %s /\\ %s /\\ %s )' % (LTY, NSS, HCL))
    ff = w.s([u['p3'], w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, LTY))
    n2 = w.s([u['p3'], w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, NSS))
    n1s = w.s([n2], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    n2s = w.s([n2], 'simprd', "( %s -> N' C_ %s )" % (ph, S('T')))
    hcl = w.s([u['p3'], w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HCL))
    fe = constfty(w, ph, 'E', L('T'), u['el'])
    ge = w.s([u['tv'], fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tv = A_(u['tv'], 'T e. V'); dd = A_(u['dd'], 'D e. %s' % STK('T'))
        ffa = A_(ff, LTY); gea = A_(ge, '%s e. %s' % (GE, STMT_T))
        fea = A_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        n1sa = A_(n1s, 'N C_ %s' % S('T')); n2sa = A_(n2s, "N' C_ %s" % S('T'))
        ela = A_(u['el'], 'E e. %s' % L('T'))
        hcla = A_(hcl, HCL)
        vn, nvn = fvn(w, av, hcla)
        vv = w.s([n1sa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        nvcl = w.s([n2sa, nvn], 'sseldd', '( %s -> ( F ` v ) e. %s )' % (av, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` ( F ` v ) ) = E )' % (av, CONSTF('T', 'E')))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, '( F ` v ) e. %s' % S('T'): nvcl,
                 'D e. %s' % STK('T'): dd, LTY: ffa, '%s e. %s' % (GE, STMT_T): gea,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` ( F ` v ) )' % CONSTF('T', 'E'): ('E', rge)}
        ex = Exec(w, av, 'T', facts, rules=rules)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. ( F ` v ) , D >. >.'
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, '( F ` v )', nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', 'D', (u['meq'], u['phm']),
            u['al'], u['el'], n1s, n2s, u['dd'], u['dd'], body, qed=True)
    return w.run()


def tm2flpg():
    lab = 'tm2flpg'
    PU = PUSH('I', CONSTF('T', 'Z'), GE)
    STM = LOAD('F', PU)
    IZ = '( I e. %s /\\ Z e. %s )' % (DG, GI)
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( ( A e. %s /\\ E e. %s /\\ D e. %s ) /\\ %s ) '
          '/\\ ( %s /\\ %s /\\ %s ) )'
          % (PHM, STM, L('T'), L('T'), STK('T'), IZ, LTY, NSS, HCL))
    D2 = UPD('T', 'D', 'I', '( <" Z "> ++ ( D ` I ) )')
    w = W(lab, 'The step ` load F ( push I Z ( goto E ) ) ` : the internal state '
               'moves by ` F ` from a class ` N ` into a class ` N\' ` and the '
               'constant letter ` Z ` is pushed on stack ` I ` .  The entry '
               'label of ` addLoop ` and ` subLoop ` (TM/Arith.lean, '
               'TM/Sub.lean), which sets the carry and pushes the output '
               'terminator.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    p2 = w.s([], 'simp2', '( %s -> ( ( A e. %s /\\ E e. %s /\\ D e. %s ) /\\ %s ) )'
             % (ph, L('T'), L('T'), STK('T'), IZ))
    lab3 = w.s([p2], 'simpld', '( %s -> ( A e. %s /\\ E e. %s /\\ D e. %s ) )'
               % (ph, L('T'), L('T'), STK('T')))
    izs = w.s([p2], 'simprd', '( %s -> %s )' % (ph, IZ))
    ii = w.s([izs], 'simpld', '( %s -> I e. %s )' % (ph, DG))
    zz = w.s([izs], 'simprd', '( %s -> Z e. %s )' % (ph, GI))
    al = w.s([lab3, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lab3, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    dd = w.s([lab3, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    p3 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, LTY, NSS, HCL))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    ff = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, LTY))
    n2 = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, NSS))
    n1s = w.s([n2], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    n2s = w.s([n2], 'simprd', "( %s -> N' C_ %s )" % (ph, S('T')))
    hcl = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HCL))
    fe = constfty(w, ph, 'E', L('T'), el)
    fz = constfty(w, ph, 'Z', GI, zz)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    izp = w.s([ii, fz], 'jca', '( %s -> ( I e. %s /\\ %s e. ( %s ^m %s ) ) )'
              % (ph, DG, CONSTF('T', 'Z'), GI, S('T')))
    pu = w.s([tv, izp, ge, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PU, STMT_T))
    dkw = w.s([tv, dd, ii, w.inst('tm2stkfv')], 'syl3anc', '( %s -> ( D ` I ) e. Word %s )' % (ph, GI))
    s1c = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ph, GI))
    zdw = w.s([s1c, dkw, w.inst('ccatcl')], 'syl2anc',
              '( %s -> ( <" Z "> ++ ( D ` I ) ) e. Word %s )' % (ph, GI))
    kj = w.s([ii, zdw], 'jca', '( %s -> ( I e. %s /\\ ( <" Z "> ++ ( D ` I ) ) e. Word %s ) )'
             % (ph, DG, GI))
    d2cl = w.s([tv, dd, kj, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, 'D e. %s' % STK('T'))
        ffa = A_(ff, LTY); gea = A_(ge, '%s e. %s' % (GE, STMT_T))
        pua = A_(pu, '%s e. %s' % (PU, STMT_T))
        fea = A_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        fza = A_(fz, '%s e. ( %s ^m %s )' % (CONSTF('T', 'Z'), GI, S('T')))
        n1sa = A_(n1s, 'N C_ %s' % S('T')); n2sa = A_(n2s, "N' C_ %s" % S('T'))
        ela = A_(el, 'E e. %s' % L('T')); zza = A_(zz, 'Z e. %s' % GI)
        iia = A_(ii, 'I e. %s' % DG); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        hcla = A_(hcl, HCL)
        vn, nvn = fvn(w, av, hcla)
        vv = w.s([n1sa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        nvcl = w.s([n2sa, nvn], 'sseldd', '( %s -> ( F ` v ) e. %s )' % (av, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        zvv = w.s([zza], 'elexd', '( %s -> Z e. _V )' % av)
        rge = w.s([evv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` ( F ` v ) ) = E )' % (av, CONSTF('T', 'E')))
        rgz = w.s([zvv, nvcl, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` ( F ` v ) ) = Z )' % (av, CONSTF('T', 'Z')))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, '( F ` v ) e. %s' % S('T'): nvcl,
                 'D e. %s' % STK('T'): dda, '%s e. %s' % (D2, STK('T')): d2a,
                 LTY: ffa, '%s e. %s' % (GE, STMT_T): gea, '%s e. %s' % (PU, STMT_T): pua,
                 'I e. %s' % DG: iia,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'Z'), GI, S('T')): fza,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` ( F ` v ) )' % CONSTF('T', 'E'): ('E', rge),
                 '( %s ` ( F ` v ) )' % CONSTF('T', 'Z'): ('Z', rgz)}
        ex = Exec(w, av, 'T', facts, rules=rules)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. ( F ` v ) , %s >. >.' % D2
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, '( F ` v )', nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', D2, (meq, phm),
            al, el, n1s, n2s, dd, d2cl, body, qed=True)
    return w.run()



def tm2fbrg():
    lab = 'tm2fbrg'
    STM = BRANCH('C', 'Q', GE)
    CTY = 'C e. ( 2o ^m %s )' % S('T')
    HE = 'A. m e. N -. ( C ` m ) = 1o'
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ D e. %s ) '
          '/\\ ( ( %s /\\ Q e. %s ) /\\ ( N C_ %s /\\ %s ) ) )'
          % (PHM, STM, L('T'), L('T'), STK('T'), CTY, STMT_T, S('T'), HE))
    w = W(lab, 'The step ` branch C Q ( goto E ) ` when the test fails on the '
               'whole state class ` N ` : the machine leaves for ` E ` with '
               'nothing changed.  Lean: the ` v.carry = false ` branch of '
               '` zeroIfBorrow_runs ` , and the false half of every '
               '` Frag.ite ` .')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    lab3 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ D e. %s ) )'
               % (ph, L('T'), L('T'), STK('T')))
    al = w.s([lab3, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lab3, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    dd = w.s([lab3, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    p3 = w.s([], 'simp3', '( %s -> ( ( %s /\\ Q e. %s ) /\\ ( N C_ %s /\\ %s ) ) )'
             % (ph, CTY, STMT_T, S('T'), HE))
    cq = w.s([p3], 'simpld', '( %s -> ( %s /\\ Q e. %s ) )' % (ph, CTY, STMT_T))
    cc = w.s([cq], 'simpld', '( %s -> %s )' % (ph, CTY))
    qq = w.s([cq], 'simprd', '( %s -> Q e. %s )' % (ph, STMT_T))
    nh = w.s([p3], 'simprd', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), HE))
    nss = w.s([nh], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe = constfty(w, ph, 'E', L('T'), el)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, 'D e. %s' % STK('T'))
        cca = A_(cc, CTY); qqa = A_(qq, 'Q e. %s' % STMT_T)
        gea = A_(ge, '%s e. %s' % (GE, STMT_T)); ela = A_(el, 'E e. %s' % L('T'))
        fea = A_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        nssa = A_(nss, 'N C_ %s' % S('T')); hea = A_(he, HE)
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        i1 = w.s([], 'fveq2', '( m = v -> ( C ` m ) = ( C ` v ) )')
        i2 = w.s([i1], 'eqeq1d', '( m = v -> ( ( C ` m ) = 1o <-> ( C ` v ) = 1o ) )')
        i3 = w.s([i2], 'notbid', '( m = v -> ( -. ( C ` m ) = 1o <-> -. ( C ` v ) = 1o ) )')
        cf = w.s([i3, hea, vn], 'rspcdva', '( %s -> -. ( C ` v ) = 1o )' % av)
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, vv, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` v ) = E )' % (av, CONSTF('T', 'E')))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, 'D e. %s' % STK('T'): dda,
                 CTY: cca, 'Q e. %s' % STMT_T: qqa, '%s e. %s' % (GE, STMT_T): gea,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` v )' % CONSTF('T', 'E'): ('E', rge)}
        ifr = {'( C ` v ) = 1o': (False, cf)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. v , D >. >.'
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, 'v', vn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', 'D', (meq, phm),
            al, el, nss, nss, dd, dd, body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2flg'): tm2flg()
    if want('tm2flpg'): tm2flpg()
    if want('tm2fbrg'): tm2fbrg()
