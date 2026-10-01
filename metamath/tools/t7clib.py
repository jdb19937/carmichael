r"""Sortie T7c: helpers for runs of installed fragments at the machine.

`Run` sequences the triples of consecutive calls (each an instance of a
delivered wrapper), tracking the stack term as a chain of updates of a
base stack with simplified values (a `t7blib.Stacks`), rewriting every
( Dcur ` s ) the wrappers' conclusions carry into its known value, and
normalising the chain at the end (`t7blib.stk_normalize`).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t7blib import *
from t7_e_cmp import machine

K6 = ['K', 'J', 'I', "I'", 'I"', 'I0']
ENC = lambda t: '( encodeNat ` %s )' % t
ENG = lambda t: '( encNatGam ` %s )' % t
YX = lambda X: '( <" 4 "> ++ %s )' % X
EW = lambda t, X: CC(ENG(t), YX(X))          # ( encNatGam ` t ) ++ ( <" 4 "> ++ X )


def setup(w, ph, T, ks, pred=None, fname=None):
    """Ctx, machine facts, ne, the one-level unfolding of the predicate, and the base extras"""
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ks)
    ne = ne_fn(w, ph, c, set(flat(dist_tree(ks))))
    base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
    if pred is not None:
        base.update(unfold_all(w, ph, c[pred], fname, ks, 'P', 'E', rec=False))
    for s_ in ks:
        base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
    for i_, a in enumerate(ks):
        for b in ks[i_ + 1:]:
            base['%s =/= %s' % (a, b)] = ne(a, b)
            base['%s =/= %s' % (b, a)] = ne(b, a)
    return c, mk, ne, base


def selfval(w, ph, mk, D, dd, s):
    """( text , ( ph -> ( D ` s ) = ( D ` s ) ) , ( ph -> ( D ` s ) e. Word Gamma' ) )"""
    return (('( %s ` %s )' % (D, s)), w.s([], 'eqidd', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, D, s, D, s)),
            w.s([stkfv(w, ph, D, s, mk['tv'], dd, mk['k'][s]['kd']), mk['k'][s]['wge']], 'eleqtrd',
                "( %s -> ( %s ` %s ) e. Word Gamma' )" % (ph, D, s)))


def encw(w, ph, t, tn):
    """( ph -> ( encNatGam ` t ) e. Word Gamma' ) from tn : t e. NN0"""
    return w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` %s ) e. Word Gamma' )" % (ph, t))


def ewg(w, ph, t, tn, X, xg):
    """( ph -> EW( t , X ) e. Word Gamma' )"""
    return wgcat(w, ph, ENG(t), YX(X), encw(w, ph, t, tn), wg4(w, ph, X, xg))


class Run:
    """a sequence of triples from the configuration class C( A0 , N0 , D ) on"""
    def __init__(self, w, ph, mk, S, base, bld_ctx):
        self.w, self.ph, self.mk, self.S0, self.S = w, ph, mk, S, S
        self.base = dict(base); self.c = bld_ctx
        self.tri = None; self.C0 = None; self.cur = None; self.n = None
        self.chain = []
        self.gam = {}
        for s_, (txt, st, g) in S.vals.items():
            self.gam[txt] = g

    def rules(self, S=None):
        S = S or self.S
        D = S.D
        return {'( %s ` %s )' % (D, s_): (v[0], v[1]) for s_, v in S.vals.items()
                if '( %s ` %s )' % (D, s_) != v[0]}

    def rebase(self, S, chain):
        """declare the current stacks to be the Stacks S (same text), with the update chain of the base"""
        assert S.D == self.S.D, (S.D, self.S.D)
        self.S = S; self.chain = list(chain)

    def at(self, updates):
        """the Stacks of the base with the updates ( s , v ) applied"""
        S = self.S0
        for s_, v in updates:
            S = S.upd(s_, v, self.gam[v])
        return S

    def call(self, label, m, extra, updates, cls_rw=None, on=None, pre=None):
        """instantiate `label` at m (D := current stacks) with extra leaves; `updates` the list of
        ( s , value text , gam step ) the call performs (in order); cls_rw : optional
        ( step ( ph -> Npost = N' ) , N' ) rewriting the post class"""
        w, ph = self.w, self.ph
        Son, chain_on = on if on is not None else (self.S, self.chain)
        m = dict(m); m['D'] = Son.D
        ex = dict(self.base); ex.update(extra)
        ex[STKD(Son.D)] = Son.memb
        t, cc = inst(w, ph, label, m, Bld(w, ph, self.c, ex))
        Ca, Da, n1 = triple_parts(cc)
        if pre is not None:
            # shrink the pre class: pre = ( N2 , ss : ( ph -> N2 C_ Npre ) )
            N2, ss = pre
            head = Ca[:-len(' X. { %s } ) )' % Son.D)]
            lab0 = head.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
            npre = head.split(' } X. ( ', 1)[1]
            Cn = CLN(lab0, N2, Son.D)
            t = hrssc(w, ph, self.mk['phm'], t, Ca, Da, n1, Cn, clnss(w, ph, lab0, N2, npre, Son.D, ss))
            Ca = Cn
        # rewrite ( Dcur ` s ) in the post stacks
        toks = Da.split()
        post_cls = None
        rl = {k: v for k, v in self.rules(Son).items() if k in Da}
        deq = None
        Dnew = Da
        if rl:
            deq, Dnew = w.rewrite(Da, rl, ph)
        S2 = Son
        self.chain = list(chain_on)
        for (s_, v, g) in updates:
            S2 = S2.upd(s_, v, g)
            self.chain.append((s_, v))
            self.gam[v] = g
        # the class text of the post
        pre_d = self.S.D
        # parse Dnew = ( { ( inl ` E ) } X. ( N X. { D' } ) ) : compare with S2.D
        want_tail = ' X. { %s } ) )' % S2.D
        assert Dnew.endswith(want_tail), 'post stacks\nGOT  %s\nWANT ...%s' % (Dnew, want_tail)
        if cls_rw is not None:
            head = Dnew[:-len(want_tail)]
            ncls_old = head.split(' } X. ( ', 1)[1]
            lab = head.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
            e2 = clnneq(w, ph, lab, cls_rw[0], ncls_old, cls_rw[1], S2.D)
            if deq is None:
                deq = e2
            else:
                deq = w.s([deq, e2], 'eqtrd', '( %s -> %s = %s )' % (ph, Da, CLN(lab, cls_rw[1], S2.D)))
            Dnew = CLN(lab, cls_rw[1], S2.D)
        if deq is not None:
            t, Ca, Dnew2, n1 = hrrw(w, ph, t, Ca, Da, n1, deq=deq)
            assert Dnew2 == Dnew, (Dnew2, Dnew)
        if self.tri is None:
            self.tri, self.C0, self.cur, self.n = t, Ca, Dnew, n1
        else:
            assert Ca == self.cur, 'pre class\nGOT  %s\nWANT %s' % (Ca, self.cur)
            self.tri = hrseq(w, ph, self.mk['phm'], self.tri, t, self.C0, self.cur, Dnew, self.n, n1)
            self.n = '( %s + %s )' % (self.n, n1)
            self.cur = Dnew
        self.S = S2
        return t, n1

    def normalize(self, order):
        """rewrite the current stacks (a chain of updates of the base) into their normal form"""
        w, ph = self.w, self.ph
        D0 = self.S0.D
        st, out = stk_normalize(w, ph, self.mk, D0, self.S0.memb, self.S0.ne, self.chain, self.gam, order)
        if st is None:
            return self.cur, out
        txt = chain_text(D0, out)
        head = self.cur[:-len(' X. { %s } ) )' % self.S.D)]
        lab = head.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
        ncls = head.split(' } X. ( ', 1)[1]
        e = clneq(w, ph, lab, ncls, st, self.S.D, txt)
        self.tri, _, self.cur, _ = hrrw(w, ph, self.tri, self.C0, self.cur, self.n, deq=e)
        S = self.at(out)
        assert S.D == txt, (S.D, txt)
        self.S = S; self.chain = list(out)
        return self.cur, out


# ------------------------------------------------------------ bitlen (Prims.lean): the installation predicate
# stacks K = x , J = y , I = s , I' = s'
LORB = LSET(fl='if ( ( ( TMfl ` u ) = 1o \\/ ( bitOf ` ( TMra ` u ) ) = 1o ) , 1o , (/) )')
LCAR1 = LSET(car='1o')
LBL0 = LSET(car='(/)', fl='(/)')
CNCAR = CNOT('car')
ST_BLS = POP('I', 'TMrdBit', BRANCH('TMda', LOAD(LCAR1, GT('Q')), PUSH('K', PBR, LOAD(LORB, GT('Q')))))
comp('bl', 'TMIbitlen', ['K', 'J', 'I', "I'"], ['A', "A'", 'A"', 'A0', 'P1', 'L', 'B', 'Q', 'Q1', 'Q2', 'Q3'], 'E',
     (((MEQ('A', PUSH('I', CONST('4'), GT("A'"))), MEQ("A'", POP('K', 'TMrdA', BRANCH(CIS, PUSH('I', PBR, GT("A'")), GT('A"'))))),
       (MEQ('A"', PUSH('K', CONST('4'), GT('A0'))), MEQ('A0', PUSH('J', CONST('4'), GT('P1'))), MEQ('P1', LOAD(LBL0, GT('L'))))),
      ((MEQ('L', BRANCH(CNCAR, GT('B'), GT('E'))), MEQ('B', ST_BLS)),
       (MEQ('Q', BRANCH('TMda', GT('Q1'), GT('Q2'))), MEQ('Q1', LOAD(LID, GT('L')))),
       (MEQ('Q2', BRANCH('TMfl', GT('Z0'), GT('Q3'))), MEQ('Q3', LOAD(LID, GT('L')))))),
     (((LAB('A'), LAB("A'")), (LAB('A"'), LAB('A0'), LAB('P1'))), ((LAB('L'), LAB('B')), (LAB('Q'), LAB('Q1')), (LAB('Q2'), LAB('Q3'))),
      LAB('E')),
     "` bitlen x y s s' = pushSym s comma ; moveNum x s ; pushSym x comma ; pushNum y 0 ; "
     "load' ( flag := false , carry := false ) ; loop ( !carry ) ( blScan s x ; ite da skip ( ite flag ( incr y s' ) skip ) ) `",
     [('inc', ['J', "I'"], 'Z0', 'L')])


# ------------------------------------------------------------ pow2 (Prims.lean): the installation predicate
# stacks K = x , J = y , I = s , I' = s'
comp('p2', 'TMIpow2', ['K', 'J', 'I', "I'"], ['A', "A'", 'L', 'Q'], 'E',
     ((MEQ('A', PUSH('J', CONST('4'), GT("A'"))), MEQ("A'", PUSH('J', CONST(BIT1B), GT('Z0')))),
      (MEQ('L', BRANCH(CNOT('fl'), GT('B0'), GT('X0'))), MEQ('Q', PUSH('J', CONST(Z0B), GT('Z1'))))),
     ((LAB('A'), LAB("A'")), (LAB('L'), LAB('Q'))),
     "` pow2 x y s s' = pushSym y comma ; pushSym y ( bit true ) ; isZero x s ; loop ( !flag ) "
     "( predNum x s' ; pushSym y ( bit false ) ; isZero x s ) ; dropNum x `",
     [('iz', ['K', 'I'], 'Z0', 'L'), ('prd', ['K', "I'"], 'B0', 'Q'), ('iz', ['K', 'I'], 'Z1', 'L'), ('drop', ['K'], 'X0', 'E')])
