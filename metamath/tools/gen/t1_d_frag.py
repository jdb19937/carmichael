"""T1: concrete fragments of Lean's TM/Prims.lean as instantiations of the
fragment calculus, written by the symbolic machine-execution generator."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

CFGT = CFG('T')
ST = '( %s X. %s )' % (S('T'), STK('T'))
GK = '( %s ` K )' % G('T')


def constfty(w, ante, X, COD, xcl):
    """( ante -> ( S X. { X } ) e. ( COD ^m S ) ) from a step xcl : X e. COD"""
    f = w.s([xcl, w.inst('fconst6g')], 'syl', '( %s -> %s : %s --> %s )' % (ante, CONSTF('T', X), S('T'), COD))
    c1 = w.s([], 'fvex', '%s e. _V' % COD) if COD.startswith('( ') else w.s([], 'fvex', '%s e. _V' % COD)
    c1a = w.s([c1], 'a1i', '( %s -> %s e. _V )' % (ante, COD))
    c2 = w.s([], 'fvex', '%s e. _V' % S('T'))
    c2a = w.s([c2], 'a1i', '( %s -> %s e. _V )' % (ante, S('T')))
    bi = w.s([c1a, c2a, w.inst('elmapg')], 'syl2anc',
             '( %s -> ( %s e. ( %s ^m %s ) <-> %s : %s --> %s ) )'
             % (ante, CONSTF('T', X), COD, S('T'), CONSTF('T', X), S('T'), COD))
    return w.s([bi, f], 'mpbird', '( %s -> %s e. ( %s ^m %s ) )' % (ante, CONSTF('T', X), COD, S('T')))


def tm2fpush():
    lab = 'tm2fpush'
    GOT = GOTO(CONSTF('T', 'E'))
    STMT = PUSH('K', CONSTF('T', 'Z'), GOT)
    UPDD = UPD('T', 'D', 'K', '( <" Z "> ++ ( D ` K ) )')
    ante = ('( ( %s /\\ ( M ` A ) = %s ) /\\ ( A e. %s /\\ E e. %s /\\ ( K e. %s /\\ Z e. %s ) ) /\\ D e. %s )'
            % (PHM, STMT, L('T'), L('T'), K('T'), GK, STK('T')))
    w = W(lab, 'The fragment ` pushSym k s ` of TM/Prims.lean as a Hoare '
               'triple: one label whose statement pushes a fixed symbol on '
               'stack ` K ` and jumps to the exit, one step.  Lean: '
               '` Frag.pushSym_runs ` , ` Frag.straight ` .')
    phm = w.s([], 'simp1l', '( %s -> %s )' % (ante, PHM))
    meq = w.s([], 'simp1r', '( %s -> ( M ` A ) = %s )' % (ante, STMT))
    el = w.s([], 'simp2', '( %s -> ( A e. %s /\\ E e. %s /\\ ( K e. %s /\\ Z e. %s ) ) )'
             % (ante, L('T'), L('T'), K('T'), GK))
    al = w.s([el], 'simp1d', '( %s -> A e. %s )' % (ante, L('T')))
    ell = w.s([el], 'simp2d', '( %s -> E e. %s )' % (ante, L('T')))
    kz = w.s([el], 'simp3d', '( %s -> ( K e. %s /\\ Z e. %s ) )' % (ante, K('T'), GK))
    kk = w.s([kz], 'simpld', '( %s -> K e. %s )' % (ante, K('T')))
    zz = w.s([kz], 'simprd', '( %s -> Z e. %s )' % (ante, GK))
    dd = w.s([], 'simp3', '( %s -> D e. %s )' % (ante, STK('T')))
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ante)
    # typing of the two constant functions and of the goto statement
    fz = constfty(w, ante, 'Z', GK, zz)
    fe = constfty(w, ante, 'E', L('T'), ell)
    gst = w.s([tv, fe, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ante, GOT, STMT_T()))
    # the new stack assignment is a stack assignment
    z1 = w.s([zz], 's1cld', '( %s -> <" Z "> e. Word %s )' % (ante, GK))
    dk = w.s([tv, dd, kk, w.inst('tm2stkfv')], 'syl3anc', '( %s -> ( D ` K ) e. Word %s )' % (ante, GK))
    cc = w.s([z1, dk, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" Z "> ++ ( D ` K ) ) e. Word %s )' % (ante, GK))
    kc = w.s([kk, cc], 'jca', '( %s -> ( K e. %s /\\ ( <" Z "> ++ ( D ` K ) ) e. Word %s ) )' % (ante, K('T'), GK))
    upd = w.s([tv, dd, kc, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ante, UPDD, STK('T')))
    def body(av):
        tva = w.s([tv], 'adantr', '( %s -> T e. V )' % av)
        vv = w.s([], 'simpr', '( %s -> v e. %s )' % (av, S('T')))
        dda = w.s([dd], 'adantr', '( %s -> D e. %s )' % (av, STK('T')))
        kka = w.s([kk], 'adantr', '( %s -> K e. %s )' % (av, K('T')))
        fza = w.s([fz], 'adantr', '( %s -> %s e. ( %s ^m %s ) )' % (av, CONSTF('T', 'Z'), GK, S('T')))
        fea = w.s([fe], 'adantr', '( %s -> %s e. ( %s ^m %s ) )' % (av, CONSTF('T', 'E'), L('T'), S('T')))
        gsta = w.s([gst], 'adantr', '( %s -> %s e. %s )' % (av, GOT, STMT_T()))
        upda = w.s([upd], 'adantr', '( %s -> %s e. %s )' % (av, UPDD, STK('T')))
        zza = w.s([zz], 'adantr', '( %s -> Z e. %s )' % (av, GK))
        ella = w.s([ell], 'adantr', '( %s -> E e. %s )' % (av, L('T')))
        zv = w.s([zza], 'elexd', '( %s -> Z e. _V )' % av)
        ev = w.s([ella], 'elexd', '( %s -> E e. _V )' % av)
        rz = w.s([zv, vv, w.inst('fvconst2g')], 'syl2anc',
                 '( %s -> ( %s ` v ) = Z )' % (av, CONSTF('T', 'Z')))
        re = w.s([ev, vv, w.inst('fvconst2g')], 'syl2anc',
                 '( %s -> ( %s ` v ) = E )' % (av, CONSTF('T', 'E')))
        facts = {'T e. V': tva, 'v e. %s' % S('T'): vv, 'D e. %s' % STK('T'): dda,
                 '%s e. %s' % (UPDD, STK('T')): upda,
                 'K e. %s' % K('T'): kka,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'Z'), GK, S('T')): fza,
                 '%s e. ( %s ^m %s )' % (CONSTF('T', 'E'), L('T'), S('T')): fea,
                 '%s e. %s' % (GOT, STMT_T()): gsta}
        rules = {'( %s ` v )' % CONSTF('T', 'Z'): ('Z', rz),
                 '( %s ` v )' % CONSTF('T', 'E'): ('E', re)}
        ex = Exec(w, av, 'T', facts, rules=rules)
        st, res = ex.run(STMT, '<. v , D >.')
        meqa = w.s([meq], 'adantr', '( %s -> ( M ` A ) = %s )' % (av, STMT))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )'
                 % (av, SA('T'), STMT, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, 'v', vv
    hstepc(w, ante, 'T', 'M', 'A', 'E', 'D', UPDD, (meq, phm), al, ell, dd, upd, body, qed=True)
    return w.run()


def STMT_T():
    return STMT('T')


if __name__ == '__main__':
    if want('tm2fpush'): tm2fpush()
