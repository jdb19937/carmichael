"""T6: the one-step lemmas of the list layer --- `peek K F ( goto E )` with a
known head (`peekBra`, `peekBraOr`), `pop K F ( goto E )` with a known head
(`popTop`), and the true half of a loop test (blueprint 3.2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

FTY = "F e. ( %s ^m ( %s X. %s ) )" % (S('T'), S('T'), OPT)
LAB = '( A e. %s /\\ E e. %s /\\ K e. %s )' % (L('T'), L('T'), FZ8)
HDK = '( ( D ` K ) = ( <" Z "> ++ X ) /\\ Z e. Gamma\' /\\ X e. %s )' % WG
NSS = "( N C_ %s /\\ N' C_ %s )" % (S('T'), S('T'))
HCL = "A. r e. N ( F ` <. r , ( inl ` Z ) >. ) e. N'"


def prelude(w, ph, STM):
    """the common context: returns a dict of steps at antecedent ph =
    ( ( PHM6 /\ ( M ` A ) = STM ) /\ ( LAB /\ ( FTY /\ D e. Stk ) ) /\ ( HDK /\ NSS /\ HCL ) )"""
    p1 = w.s([], 'simp1', '( %s -> ( %s /\\ ( M ` A ) = %s ) )' % (ph, PHM6, STM))
    p6 = w.s([p1], 'simpld', '( %s -> %s )' % (ph, PHM6))
    phm = w.s([p6], 'simpld', '( %s -> %s )' % (ph, PHM))
    geq = w.s([p6], 'simprd', '( %s -> ( 1st ` ( 1st ` T ) ) = TMGam )' % ph)
    meq = w.s([p1], 'simprd', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    p2 = w.s([], 'simp2', '( %s -> ( %s /\\ ( %s /\\ D e. %s ) ) )' % (ph, LAB, FTY, STK('T')))
    lab = w.s([p2], 'simpld', '( %s -> %s )' % (ph, LAB))
    al = w.s([lab, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lab, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kk = w.s([lab, w.inst('simp3')], 'syl', '( %s -> K e. %s )' % (ph, FZ8))
    fd = w.s([p2], 'simprd', '( %s -> ( %s /\\ D e. %s ) )' % (ph, FTY, STK('T')))
    ff = w.s([fd], 'simpld', '( %s -> %s )' % (ph, FTY))
    dd = w.s([fd], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    p3 = w.s([], 'simp3', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, HDK, NSS, HCL))
    hdk = w.s([p3, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, HDK))
    dk = w.s([hdk, w.inst('simp1')], 'syl', '( %s -> ( D ` K ) = ( <" Z "> ++ X ) )' % ph)
    zz = w.s([hdk, w.inst('simp2')], 'syl', "( %s -> Z e. Gamma' )" % ph)
    xx = w.s([hdk, w.inst('simp3')], 'syl', '( %s -> X e. %s )' % (ph, WG))
    nss = w.s([p3, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, NSS))
    n1s = w.s([nss], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    n2s = w.s([nss], 'simprd', "( %s -> N' C_ %s )" % (ph, S('T')))
    hcl = w.s([p3, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, HCL))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kd, ge = gamk(w, ph, 'K', geq, kk)
    fk = fmapg(w, ph, 'F', 'K', ge, ff)
    fe, gs = gotost(w, ph, 'E', tv, el)
    # the head is not empty
    zs = w.s([zz], 's1cld', '( %s -> <" Z "> e. %s )' % (ph, WG))
    zne = w.s([zz], 's1nz' if False else 'elexd', '( %s -> Z e. _V )' % ph)
    s1n = w.s([], 's1nz', '<" Z "> =/= (/)')
    s1na = w.s([s1n], 'a1i', '( %s -> <" Z "> =/= (/) )' % ph)
    zxn = w.s([zs, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> ( <" Z "> ++ X ) =/= (/) )' % ph)
    dkn = w.s([dk, zxn], 'eqnetrd', '( %s -> ( D ` K ) =/= (/) )' % ph)
    dkn2 = w.s([dkn], 'neneqd', '( %s -> -. ( D ` K ) = (/) )' % ph)
    hd0 = w.s([dk], 'fveq1d', '( %s -> ( ( D ` K ) ` 0 ) = ( ( <" Z "> ++ X ) ` 0 ) )' % ph)
    hdz = w.s([zz, xx, w.inst('ccats1fv0')], 'syl2anc', '( %s -> ( ( <" Z "> ++ X ) ` 0 ) = Z )' % ph)
    hd = w.s([hd0, hdz], 'eqtrd', '( %s -> ( ( D ` K ) ` 0 ) = Z )' % ph)
    return dict(phm=phm, geq=geq, meq=meq, al=al, el=el, kk=kk, ff=ff, dd=dd, dk=dk, zz=zz, xx=xx,
                n1s=n1s, n2s=n2s, hcl=hcl, tv=tv, kd=kd, ge=ge, fk=fk, fe=fe, gs=gs,
                dkn2=dkn2, hd=hd, zs=zs)


def nvsteps(w, av, u):
    """at av = ( ph /\ v e. N ): v e. S, NV e. N', NV e. S"""
    vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
    n1sa = A_(w, av, u['n1s'], 'N C_ %s' % S('T'))
    n2sa = A_(w, av, u['n2s'], "N' C_ %s" % S('T'))
    vv = w.s([n1sa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
    hcla = A_(w, av, u['hcl'], HCL)
    i1 = w.s([], 'opeq1', '( r = v -> <. r , ( inl ` Z ) >. = <. v , ( inl ` Z ) >. )')
    i2 = w.s([i1], 'fveq2d', '( r = v -> ( F ` <. r , ( inl ` Z ) >. ) = ( F ` <. v , ( inl ` Z ) >. ) )')
    i3 = w.s([i2], 'eleq1d', "( r = v -> ( ( F ` <. r , ( inl ` Z ) >. ) e. N' <-> ( F ` <. v , ( inl ` Z ) >. ) e. N' ) )")
    nvn = w.s([i3, hcla, vn], 'rspcdva', "( %s -> ( F ` <. v , ( inl ` Z ) >. ) e. N' )" % av)
    nvs = w.s([n2sa, nvn], 'sseldd', '( %s -> ( F ` <. v , ( inl ` Z ) >. ) e. %s )' % (av, S('T')))
    return vv, nvn, nvs


def onestep(lab, desc, STM, pop):
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( %s /\\ ( %s /\\ D e. %s ) ) /\\ ( %s /\\ %s /\\ %s ) )'
          % (PHM6, STM, LAB, FTY, STK('T'), HDK, NSS, HCL))
    w = W(lab, desc)
    u = prelude(w, ph, STM)
    D2 = UPDT('D', 'K', 'X') if pop else 'D'
    d2cl = updcl(w, ph, 'D', 'K', 'X', u['tv'], u['dd'], u['kd'], u['ge'], u['xx']) if pop else u['dd']
    NVZ = '( F ` <. v , ( inl ` Z ) >. )'

    def body(av):
        vv, nvn, nvs = nvsteps(w, av, u)
        tv = A_(w, av, u['tv'], 'T e. V'); dd = A_(w, av, u['dd'], 'D e. %s' % STK('T'))
        kd = A_(w, av, u['kd'], 'K e. %s' % DG)
        fk = A_(w, av, u['fk'], 'F e. ( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (S('T'), S('T'), GT('K')))
        gs = A_(w, av, u['gs'], '%s e. %s' % (GOTOL('E'), STMT_T))
        fe = A_(w, av, u['fe'], '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        ela = A_(w, av, u['el'], 'E e. %s' % L('T'))
        dkn = A_(w, av, u['dkn2'], '-. ( D ` K ) = (/)')
        hd = A_(w, av, u['hd'], '( ( D ` K ) ` 0 ) = Z')
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvs, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CONSTF('T', 'E'), NVZ))
        facts = {'T e. V': tv, 'v e. %s' % S('T'): vv, 'D e. %s' % STK('T'): dd,
                 'K e. %s' % DG: kd, '%s e. %s' % (GOTOL('E'), STMT_T): gs,
                 'F e. ( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (S('T'), S('T'), GT('K')): fk,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fe,
                 '%s e. %s' % (NVZ, S('T')): nvs}
        rules = {'( ( D ` K ) ` 0 )': ('Z', hd), '( %s ` %s )' % (CONSTF('T', 'E'), NVZ): ('E', rge)}
        if pop:
            d2a = A_(w, av, d2cl, '%s e. %s' % (D2, STK('T')))
            facts['%s e. %s' % (D2, STK('T'))] = d2a
            dka = A_(w, av, u['dk'], '( D ` K ) = ( <" Z "> ++ X )')
            zz = A_(w, av, u['zz'], "Z e. Gamma'"); xx = A_(w, av, u['xx'], 'X e. %s' % WG)
            t1 = w.s([dka], 'fveq2d', '( %s -> ( # ` ( D ` K ) ) = ( # ` ( <" Z "> ++ X ) ) )' % av)
            t2 = w.s([t1], 'opeq2d', '( %s -> <. 1 , ( # ` ( D ` K ) ) >. = <. 1 , ( # ` ( <" Z "> ++ X ) ) >. )' % av)
            t3 = w.s([dka, t2], 'oveq12d', '( %s -> %s = ( ( <" Z "> ++ X ) substr <. 1 , ( # ` ( <" Z "> ++ X ) ) >. ) )' % (av, TAIL('D', 'K')))
            t4 = w.s([zz, xx, w.inst('wrdtls1')], 'syl2anc', '( %s -> ( ( <" Z "> ++ X ) substr <. 1 , ( # ` ( <" Z "> ++ X ) ) >. ) = X )' % av)
            t5 = w.s([t3, t4], 'eqtrd', '( %s -> %s = X )' % (av, TAIL('D', 'K')))
            rules[TAIL('D', 'K')] = ('X', t5)
        ifr = {'( D ` K ) = (/)': (False, dkn)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (NVZ, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(w, av, u['meq'], '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )' % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, NVZ, nvn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', D2, (u['meq'], u['phm']),
            u['al'], u['el'], u['n1s'], u['n2s'], u['dd'], d2cl, body, qed=True)
    return w.run()


def tm2lpk():
    return onestep('tm2lpk', 'The step ` peek K F ( goto E ) ` on a stack with a known head letter '
                   '` Z ` : the internal state moves by the handler applied to ` Z ` from a class '
                   '` N ` into a class ` N\' ` , the stacks are untouched.  Lean: ` peekBra_runs ` , '
                   '` peekBraOr_runs ` (TM/Lists.lean) with their concrete handlers.',
                   PEEKL('K', 'F', 'E'), False)


def tm2lpop():
    return onestep('tm2lpop', 'The step ` pop K F ( goto E ) ` on a stack with a known head letter '
                   '` Z ` : the head is removed and the internal state moves by the handler applied '
                   'to ` Z ` from a class ` N ` into a class ` N\' ` .  Lean: ` popTop_runs ` '
                   '(TM/Lists.lean).', POPL('K', 'F', 'E'), True)


def tm2lbrt():
    lab = 'tm2lbrt'
    STM = BRANCH('C', GOTOL('E'), 'Q')
    CTY = 'C e. ( 2o ^m %s )' % S('T')
    HE = 'A. m e. N ( C ` m ) = 1o'
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ D e. %s ) '
          '/\\ ( ( %s /\\ Q e. %s ) /\\ ( N C_ %s /\\ %s ) ) )'
          % (PHM, STM, L('T'), L('T'), STK('T'), CTY, STMT_T, S('T'), HE))
    w = W(lab, 'The step ` branch C ( goto E ) Q ` when the test succeeds on the whole state '
               'class ` N ` : the machine goes to ` E ` with nothing changed.  The true half of '
               'the test of Lean\'s ` Frag.loop ` and of ` Frag.ite ` ; ~ tm2fbrg is the false half.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    lab3 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ D e. %s ) )' % (ph, L('T'), L('T'), STK('T')))
    al = w.s([lab3, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lab3, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    dd = w.s([lab3, w.inst('simp3')], 'syl', '( %s -> D e. %s )' % (ph, STK('T')))
    p3 = w.s([], 'simp3', '( %s -> ( ( %s /\\ Q e. %s ) /\\ ( N C_ %s /\\ %s ) ) )' % (ph, CTY, STMT_T, S('T'), HE))
    cq = w.s([p3], 'simpld', '( %s -> ( %s /\\ Q e. %s ) )' % (ph, CTY, STMT_T))
    cc = w.s([cq], 'simpld', '( %s -> %s )' % (ph, CTY))
    qq = w.s([cq], 'simprd', '( %s -> Q e. %s )' % (ph, STMT_T))
    nh = w.s([p3], 'simprd', '( %s -> ( N C_ %s /\\ %s ) )' % (ph, S('T'), HE))
    nss = w.s([nh], 'simpld', '( %s -> N C_ %s )' % (ph, S('T')))
    he = w.s([nh], 'simprd', '( %s -> %s )' % (ph, HE))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe, ge = gotost(w, ph, 'E', tv, el)

    def body(av):
        tva = A_(w, av, tv, 'T e. V'); dda = A_(w, av, dd, 'D e. %s' % STK('T'))
        cca = A_(w, av, cc, CTY); qqa = A_(w, av, qq, 'Q e. %s' % STMT_T)
        gea = A_(w, av, ge, '%s e. %s' % (GOTOL('E'), STMT_T)); ela = A_(w, av, el, 'E e. %s' % L('T'))
        fea = A_(w, av, fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        nssa = A_(w, av, nss, 'N C_ %s' % S('T')); hea = A_(w, av, he, HE)
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        i1 = w.s([], 'fveq2', '( m = v -> ( C ` m ) = ( C ` v ) )')
        i2 = w.s([i1], 'eqeq1d', '( m = v -> ( ( C ` m ) = 1o <-> ( C ` v ) = 1o ) )')
        cf = w.s([i2, hea, vn], 'rspcdva', '( %s -> ( C ` v ) = 1o )' % av)
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, vv, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` v ) = E )' % (av, CONSTF('T', 'E')))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, 'D e. %s' % STK('T'): dda,
                 CTY: cca, 'Q e. %s' % STMT_T: qqa, '%s e. %s' % (GOTOL('E'), STMT_T): gea,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` v )' % CONSTF('T', 'E'): ('E', rge)}
        ifr = {'( C ` v ) = 1o': (True, cf)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. v , D >. >.'
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(w, av, meq, '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )' % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, 'v', vn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', 'D', (meq, phm),
            al, el, nss, nss, dd, dd, body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2lpk'): tm2lpk()
    if want('tm2lpop'): tm2lpop()
    if want('tm2lbrt'): tm2lbrt()
