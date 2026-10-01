"""T3: the primitives of TM/Prims.lean in the state-class form (blueprint 4)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *
from t3_lib import hstepc2
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GK = '( %s ` K )' % G('T')
STMT_T = '( TM2Stmt ` T )'
GE = GOTO(CONSTF('T', 'E'))


def tm2fpshn():
    lab = 'tm2fpshn'
    STM = PUSH('K', CONSTF('T', 'Z'), GE)
    D2 = UPD('T', 'D', 'K', '( <" Z "> ++ ( D ` K ) )')
    ph = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ ( K e. %s /\\ Z e. %s ) ) '
          '/\\ ( D e. %s /\\ N C_ %s ) )'
          % (PHM, STM, L('T'), L('T'), DG, GK, STK('T'), S('T')))
    w = W(lab, 'The step ` push K Z ( goto E ) ` with the internal state '
               'confined to a class ` N ` : the letter ` Z ` is pushed on stack '
               '` K ` and the state is untouched, so the same class ` N ` '
               'describes it at the exit.  Lean: ` Frag.pushSym_runs ` .  '
               '~ tm2fpush is the instance at ` N = ( 2nd ` T ) ` ; the class '
               'form is what a composite fragment needs, because its '
               'postcondition speaks of the state.')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ph, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ph, STM))
    lab3 = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ ( K e. %s /\\ Z e. %s ) ) )'
               % (ph, L('T'), L('T'), DG, GK))
    al = w.s([lab3, w.inst('simp1')], 'syl', '( %s -> A e. %s )' % (ph, L('T')))
    el = w.s([lab3, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (ph, L('T')))
    kz = w.s([lab3, w.inst('simp3')], 'syl', '( %s -> ( K e. %s /\\ Z e. %s ) )' % (ph, DG, GK))
    kk = w.s([kz], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    zz = w.s([kz], 'simprd', '( %s -> Z e. %s )' % (ph, GK))
    dn = w.s([], 'simp3', '( %s -> ( D e. %s /\\ N C_ %s ) )' % (ph, STK('T'), S('T')))
    dd = w.s([dn], 'simpld', '( %s -> D e. %s )' % (ph, STK('T')))
    nss = w.s([dn], 'simprd', '( %s -> N C_ %s )' % (ph, S('T')))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    fe = constfty(w, ph, 'E', L('T'), el)
    fz = constfty(w, ph, 'Z', GK, zz)
    ge = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GE, STMT_T))
    dkw = w.s([tv, dd, kk, w.inst('tm2stkfv')], 'syl3anc', '( %s -> ( D ` K ) e. Word %s )' % (ph, GK))
    s1c = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ph, GK))
    zdw = w.s([s1c, dkw, w.inst('ccatcl')], 'syl2anc',
              '( %s -> ( <" Z "> ++ ( D ` K ) ) e. Word %s )' % (ph, GK))
    kj = w.s([kk, zdw], 'jca', '( %s -> ( K e. %s /\\ ( <" Z "> ++ ( D ` K ) ) e. Word %s ) )'
             % (ph, DG, GK))
    d2cl = w.s([tv, dd, kj, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, 'D e. %s' % STK('T'))
        gea = A_(ge, '%s e. %s' % (GE, STMT_T)); iia = A_(kk, 'K e. %s' % DG)
        fea = A_(fe, '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')))
        fza = A_(fz, '%s e. ( %s ^m %s )' % (CONSTF('T', 'Z'), GK, S('T')))
        nssa = A_(nss, 'N C_ %s' % S('T')); ela = A_(el, 'E e. %s' % L('T'))
        zza = A_(zz, 'Z e. %s' % GK); d2a = A_(d2cl, '%s e. %s' % (D2, STK('T')))
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, S('T')))
        evv = w.s([ela], 'elexd', '( %s -> E e. _V )' % av)
        zvv = w.s([zza], 'elexd', '( %s -> Z e. _V )' % av)
        rge = w.s([evv, vv, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` v ) = E )' % (av, CONSTF('T', 'E')))
        rgz = w.s([zvv, vv, w.inst('fvconst2g')], 'syl2anc',
                  '( %s -> ( %s ` v ) = Z )' % (av, CONSTF('T', 'Z')))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, 'D e. %s' % STK('T'): dda,
                 '%s e. %s' % (D2, STK('T')): d2a, '%s e. %s' % (GE, STMT_T): gea,
                 'K e. %s' % DG: iia,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'Z'), GK, S('T')): fza,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea}
        rules = {'( %s ` v )' % CONSTF('T', 'E'): ('E', rge),
                 '( %s ` v )' % CONSTF('T', 'Z'): ('Z', rgz)}
        ex = Exec(w, av, 'T', facts, rules=rules)
        st, res = ex.run(STM, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. v , %s >. >.' % D2
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(meq, '( M ` A ) = %s' % STM)
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STM, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, 'v', vn
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', D2, (meq, phm),
            al, el, nss, nss, dd, d2cl, body, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fpshn'): tm2fpshn()
