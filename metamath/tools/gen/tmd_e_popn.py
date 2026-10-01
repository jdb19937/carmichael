"""T-MD: the step ` pop K F ( goto E ) ` from a state class ` N ` into a class
` N' ` (~ tm2fpopn ): the generic form of T6's ~ tm2lpop , Lean's ` popBit_runs_bit `
and ` popBit_runs_end ` (the letter ` Z ` is a bit or the terminator, the
consumer's ` N' ` pins ` ra ` and ` da ` )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fpopn():
    lab = 'tm2fpopn'
    tree, ph = TREE_POPN, cj(TREE_POPN)
    ZX = CC(S1('Z'), 'X')
    D2 = UP('D', 'K', 'X')
    NV1 = NV('F', 'v', 'Z')
    w = W(lab, 'The step ` pop K F ( goto E ) ` with the internal state confined to a class '
               '` N ` and the popped letter ` Z ` carrying it into ` N\' ` : the letter is '
               'removed from stack ` K ` .  Lean: ` popBit_runs_bit ` , ` popBit_runs_end ` '
               '(` readBit ` sets ` ra ` , ` da ` from ` Z ` : the consumer\'s ` N\' ` ).  The '
               'generic form of ~ tm2lpop .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, el, kk = c[LAB('A')], c[LAB('E')], c['K e. %s' % DG]
    ff, dd = c[RTY('F', 'K')], c[STKD('D')]
    dke, zz, xx = c['( D ` K ) = %s' % ZX], c['Z e. %s' % GK], c[WRD('X', GK)]
    nss, n2s, hp = c[SSS('N')], c[SSS("N'")], c["A. r e. N %s e. N'" % NV('F', 'r', 'Z')]
    fe = constfty(w, ph, 'E', LL, el)
    ge = gotocl(w, ph, tv, 'E', el)
    s1z = s1w(w, ph, zz, 'Z', GK)
    s1n = w.s([], 's1nz', '<" Z "> =/= (/)'); s1na = w.s([s1n], 'a1i', '( %s -> <" Z "> =/= (/) )' % ph)
    zxn = w.s([s1z, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, ZX))
    d2cl = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, STKD('D')); kka = A_(kk, 'K e. %s' % DG)
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([A_(nss, SSS('N')), vn], 'sseldd', '( %s -> v e. %s )' % (av, SS))
        h, _ = ralat(w, av, "%s e. N'" % NV('F', 'r', 'Z'), A_(hp, "A. r e. N %s e. N'" % NV('F', 'r', 'Z')), vn, m='r')
        nvs = w.s([A_(n2s, SSS("N'")), h], 'sseldd', '( %s -> %s e. %s )' % (av, NV1, SS))
        zxnn = w.s([A_(zxn, '%s =/= (/)' % ZX)], 'neneqd', '( %s -> -. %s = (/) )' % (av, ZX))
        zj = w.s([A_(zz, 'Z e. %s' % GK), A_(xx, WRD('X', GK))], 'jca', '( %s -> ( Z e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        zfv = w.s([zj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Z )' % (av, ZX))
        ztl = w.s([zj, w.inst('wrdtls1')], 'syl', '( %s -> ( %s substr <. 1 , ( # ` %s ) >. ) = X )' % (av, ZX, ZX))
        evv = w.s([A_(el, LAB('E'))], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nvs, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CONST('E'), NV1))
        facts = {'T e. V': tva, 'v e. %s' % SS: vv, '%s e. %s' % (NV1, SS): nvs, STKD('D'): dda, STKD(D2): A_(d2cl, STKD(D2)),
                 'K e. %s' % DG: kka, RTY('F', 'K'): A_(ff, RTY('F', 'K')), STMT(GE): A_(ge, STMT(GE)),
                 '%s e. ( %s ^m %s )' % (CONST('E'), LL, SS): A_(fe, '%s e. ( %s ^m %s )' % (CONST('E'), LL, SS))}
        rules = {'( D ` K )': (ZX, A_(dke, '( D ` K ) = %s' % ZX)), '( %s ` 0 )' % ZX: ('Z', zfv),
                 '( %s substr <. 1 , ( # ` %s ) >. )' % (ZX, ZX): ('X', ztl), '( %s ` %s )' % (CONST('E'), NV1): ('E', rge)}
        ifr = {'%s = (/)' % ZX: (False, zxnn)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM_POPN, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , %s >. >.' % (NV1, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(c[MEQ('A', STM_POPN)], MEQ('A', STM_POPN))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )' % (av, SA('T'), STM_POPN, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, NV1, h
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', "N'", 'D', D2, (c[MEQ('A', STM_POPN)], phm),
            al, el, nss, n2s, dd, d2cl, body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fpopn'): tm2fpopn()
