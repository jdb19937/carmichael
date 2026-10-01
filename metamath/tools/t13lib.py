r"""Sortie T13: searchF at the concrete machine (Lean ` searchF_le_B ` , ` searchF_runs ` ; T12's D7 redesigned).

Built on tools/t12lib.py and tools/gen/t12_p_srch.py (both read-only, merged work): the D7 letters, the
frozen statements (` tmisrc4 tmisrc3 tmisrc2 tmisrchb tmisrch ` ) and the proof pieces (` search_value ` ,
` reduce_if ` , ` out_init ` , ` lenfacts ` , ` init_stacks ` , ...) are reused as they are.

What is new here (T13-blueprint.md section 1):
* ` setup_light ` : the machine facts and the one-level unfolding of a predicate WITHOUT the numeral-stack
  facts in the antecedent (` k e. ( 0 ..^ 8 ) ` and the distinctness of the numerals are proved closed), so
  the assemblies' antecedents are 240 tokens shorter and ` finish ` / ` t10stk ` are not needed;
* ` LBase ` : a ` Base ` on the light setup with given stack values;
* the statement table ` STMTS13 ` (` add13 ` ) and ` qed13 ` .
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
_argv = sys.argv
sys.argv = sys.argv[:1]
from t12lib import *
import t12lib as T12
import t12_p_srch as P
sys.argv = _argv
from t12_d_fal import idx8, num_ne, init_vals, to_init, EQ8_
from t7_e_cmp import machine
from t7blib import ne_fn, unfold_all, Stacks, Bld
from t7lib import parts, IDX
from t5lib import Ctx, cj
import t8alib as A8
import lin
lin.FASTPATH = True

FLT = P.FLT


class CtxX(Ctx):
    """a Ctx whose missing leaves ` k e. ( 0 ..^ 8 ) ` and ` a =/= b ` (numerals) are proved closed"""
    def __init__(self, w, ph, tree, root=None):
        Ctx.__init__(self, w, ph, tree, root)
        self.fb = {}

    def __getitem__(self, leaf):
        try:
            return Ctx.__getitem__(self, leaf)
        except KeyError:
            pass
        if leaf in self.fb:
            return self.fb[leaf]
        w, ph = self.w, self.ph
        toks = leaf.split()
        if len(toks) == 7 and toks[1:] == ['e.', '(', '0', '..^', '8', ')']:
            st = idx8(w, ph, toks[0])
        elif len(toks) == 3 and toks[1] == '=/=' and toks[0].isdigit() and toks[2].isdigit():
            st = w.s([num_ne(w, ph, toks[0], toks[2])], 'neqned', '( %s -> %s =/= %s )' % (ph, toks[0], toks[2]))
        else:
            raise KeyError(leaf)
        self.fb[leaf] = st
        return st


def setup_light(w, ph, T, pred, fname, ks=N8, children=None):
    """Ctx (with closed numeral facts), machine, ne, and the leaves: the predicate unfolded one level, its
    children (all, or the slot indices listed) one level, the flag tests' typing, the letters 0 2 3 4, ` S C_ S `
    (no list handlers)"""
    c = CtxX(w, ph, T)
    mk = machine(w, ph, c, ks)
    ne = ne_fn(w, ph, c, set())
    base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
    base.update(unfold_all(w, ph, c[pred], fname, [], 'P', 'E', rec=False))
    f = FRAGS[fname]
    lm = f.lmap()
    for j, (fn, cks, en, exn) in enumerate(f.children):
        if children is not None and j not in children:
            continue
        P_ = PL('P', f.slot(j))
        pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
        base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
    for s_ in ks:
        base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
    for i_, a in enumerate(ks):
        for b in ks[i_ + 1:]:
            base['%s =/= %s' % (a, b)] = ne(a, b)
            base['%s =/= %s' % (b, a)] = ne(b, a)
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ph, cj(FLT)))
    base.update(parts(w, ph, fl, FLT))
    for n in ('0', '2', '3', '4'):
        base["%s e. Gamma'" % n] = closed(w, ph, 'gamma%s' % n, "%s e. Gamma'" % n)
    base[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    return c, mk, ne, base


class LBase(Base):
    """a Base on the light setup: stack values from ` eqs ` {k: (text, gam step)} (the antecedent's
    equations ` ( D ` k ) = text ` ), selfval elsewhere"""
    def __init__(self, w, ph, T, fname, eqs=None, pred=None, children=None):
        self.w, self.ph, self.ks = w, ph, N8
        c, mk, ne, ex = setup_light(w, ph, T, pred or FRAGS[fname].pred(), fname, children=children)
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        self.dd = c[STKD('D')]
        vals = {k: selfval(w, ph, mk, 'D', self.dd, k) for k in N8}
        self.gam = {v[0]: v[2] for v in vals.values()}
        for k, (txt, gst) in (eqs or {}).items():
            vals[k] = (txt, c['( D ` %s ) = %s' % (k, txt)], gst)
            self.gam[txt] = gst
        self.S0 = Stacks(w, ph, mk, 'D', self.dd, ne, vals)


def deep2(B, fname, j, slot):
    """unfold the callee at child j of fname one level, then its child at the given slot one level (for an entry label
    two calls deep, such as the scan's ` ( ( ( P ` 7 ) ` 2 ) ` 0 ) ` )"""
    w, ph = B.w, B.ph
    f = FRAGS[fname]
    lm = f.lmap()
    fn, cks, en, exn = f.children[j]
    P_ = PL('P', f.slot(j))
    g = FRAGS[fn]
    lm2 = g.lmap(P_, lm[exn])
    for jj, (fn2, cks2, en2, exn2) in enumerate(g.children):
        if g.slot(jj) != slot:
            continue
        P2 = PL(P_, slot)
        pr2 = FRAGS[fn2].pred(cks2, 'T', 'M', P2, lm2[exn2])
        B.ex.update(unfold_all(w, ph, B.ex[pr2], fn2, cks2, P2, lm2[exn2], rec=False))


# ============================================================ the statement table
STMTS13 = {}
TREES13 = {}
ORDER13 = []


def add13(label, tree, concl):
    STMTS13[label] = '( %s -> %s )' % (cj(tree), concl)
    TREES13[label] = (tree, concl)
    if label not in ORDER13:
        ORDER13.append(label)
    T12EXTRA[label] = STMTS13[label]


def add13s(label, stmt):
    """a statement given as text"""
    STMTS13[label] = stmt
    TREES13[label] = (None, None)
    if label not in ORDER13:
        ORDER13.append(label)
    T12EXTRA[label] = stmt


def allstmts13():
    return [(l, STMTS13[l]) for l in ORDER13]


def qed13(w, st, label):
    """qed: the step st already proves the statement (no numeral facts to discharge): rename it"""
    line = None
    for i, l in enumerate(w.lines):
        if l.startswith(st + ':'):
            line = i
    assert line is not None
    w.lines[line] = 'qed:' + w.lines[line].split(':', 1)[1]
    assert w.lines[line].split('|-', 1)[1].strip() == STMTS13[label], \
        '\nGOT  %s\nWANT %s' % (w.lines[line].split('|-', 1)[1].strip()[:300], STMTS13[label][:300])


def bld_tree(w, ph, tree, leaf):
    """( ph -> cj(tree) ) from leaf(text) -> step"""
    if isinstance(tree, str):
        return leaf(tree)
    ps = [bld_tree(w, ph, t, leaf) for t in tree]
    return w.s(ps, 'jca' if len(ps) == 2 else '3jca', '( %s -> %s )' % (ph, cj(tree)))


def prune(tree, drop):
    """the tree with the leaves in ` drop ` removed (a tuple with one member left collapses to it)"""
    if isinstance(tree, str):
        return None if tree in drop else tree
    kids = [prune(t, drop) for t in tree]
    kids = [k for k in kids if k is not None]
    if not kids:
        return None
    if len(kids) == 1:
        return kids[0]
    return tuple(kids)


def tree_leaves(tree):
    if isinstance(tree, str):
        return [tree]
    out = []
    for t in tree:
        out += tree_leaves(t)
    return out


# ============================================================ copies of D7 proof pieces with unification fixes
# (the D7 stage lemmas were generated but never unified: ~ alginl2 and ~ tmcinlne are implications, and the scan's
# ` =/= ` transfer needs ~ fveq2d before ~ neeq1d )
INR = P.INR
EQ, LEQD = P.EQ, P.LEQD
E2 = P.E2
SE, GETD, OUTS, COMMA1_ = P.SE, P.GETD, P.OUTS, COMMA1
from t12_d_fal import init_vals as _iv
init_eq = P.init_eq
from t5lib import concl

def some_typing13(w, ph, c, cl, ty):
    """with ( 1st J ) =/= inr : J' e. NN0 , W e. Word NN0 (~ scandj ); X' typing, e , F , A , Q' , w"""
    s = w.s
    out = {}
    jne = c["( 1st ` J ) =/= %s" % INR]
    j1 = s([s([s([s([ty['Q'], ty['X']], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % ph), ty['zn0']], 'jca',
                '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % ph), c['O e. NN0']], 'jca',
             '( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % ph),
            s([closed(w, ph, '1nn0', '1 e. NN0'), ty['X']], 'jca', '( %s -> ( 1 e. NN0 /\\ X e. NN0 ) )' % ph)], 'jca',
           '( %s -> ( ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( 1 e. NN0 /\\ X e. NN0 ) ) )' % ph)
    jne2 = s([jne, s([s([c[EQ('J')]], 'fveq2d', '( %s -> ( 1st ` J ) = ( 1st ` %s ) )' % (ph, LEQD['J']))], 'neeq1d',
                     '( %s -> ( ( 1st ` J ) =/= %s <-> ( 1st ` %s ) =/= %s ) )' % (ph, INR, LEQD['J'], INR))], 'mpbid',
             '( %s -> ( 1st ` %s ) =/= %s )' % (ph, LEQD['J'], INR))
    dj = s([s([j1, jne2], 'jca', '( %s -> ( %s /\\ ( 1st ` %s ) =/= %s ) )' % (ph, concl(w, ph, j1), LEQD['J'], INR)), w.inst('scandj')], 'syl',
           '( %s -> ( ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) e. NN0 /\\ ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) e. Word NN0 ) )' % (ph, LEQD['J'], LEQD['J']))
    rj = s([c[EQ('J')]], 'fveq2d', '( %s -> ( 1st ` J ) = ( 1st ` %s ) )' % (ph, LEQD['J']))
    k1 = s([rj], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` J ) ) = ( 2nd ` ( 1st ` %s ) ) )' % (ph, LEQD['J']))
    kk = s([k1], 'fveq2d', "( %s -> %s = ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) )" % (ph, LEQD["J'"], LEQD['J']))
    ww = s([k1], 'fveq2d', "( %s -> %s = ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) )" % (ph, LEQD['W'], LEQD['J']))
    out["J'"] = s([s([c[EQ("J'")], kk], 'eqtrd', "( %s -> J' = ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) )" % (ph, LEQD['J'])), s([dj], 'simpld', '( %s -> ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) e. NN0 )' % (ph, LEQD['J']))],
                  'eqeltrd', "( %s -> J' e. NN0 )" % ph)
    cl.leaf("J'", 'NN0', out["J'"])
    out['W'] = s([s([c[EQ('W')], ww], 'eqtrd', '( %s -> W = ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) )' % (ph, LEQD['J'])), s([dj], 'simprd', '( %s -> ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) e. Word NN0 )' % (ph, LEQD['J']))],
                'eqeltrd', '( %s -> W e. Word NN0 )' % ph)
    # the extraction
    lnn = s([s([ty['L'], c['1 <_ L']], 'jca', '( %s -> ( L e. NN0 /\\ 1 <_ L ) )' % ph), w.inst('elnnnn0c')], 'sylibr', '( %s -> L e. NN )' % ph) if '1 <_ L' in c.all() else None
    out['Lnn'] = lnn
    xcl = s([s([s([lnn, c['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), out['W']], 'jca', '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ W e. Word NN0 ) )' % ph), w.inst('extractcl')],
            'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, LEQD["X'"]))
    xcl2 = s([c[EQ("X'")], xcl], 'eqeltrd', "( %s -> X' e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )" % ph)
    out['E2'] = s([xcl2, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` X' ) e. NN0 )" % ph)
    cl.leaf(E2, 'NN0', out['E2'])
    return out


def out_init13(w, ph, st_se_pair, ifq_eq, cst_txt, out_txt, out_eq_txt, is_some, F_=None, A_=None, fv=None, av=None):
    """( ph -> INIT( 1 , out_txt ) = INIT( 1 , OUTS ) ) : st_se_pair : ( ph -> SE = <. IFQ' , cst >. ) with IFQ' the first
    component text ifq_eq[0] and ifq_eq[1] : ( ph -> IFQ' = ( inl <. F , A >. ) ) (some) or ( ph -> IFQ' = inr ) (none)"""
    s = w.s
    first_txt, feq = ifq_eq
    p1 = s([st_se_pair], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ph, SE, first_txt, cst_txt))
    o1 = s([s([s([], 'ifex' if first_txt.startswith('if (') else 'fvex', '%s e. _V' % first_txt)], 'a1i', '( %s -> %s e. _V )' % (ph, first_txt)),
            s([s([], 'ovex', '%s e. _V' % cst_txt)], 'a1i', '( %s -> %s e. _V )' % (ph, cst_txt)), w.inst('op1stg')], 'syl2anc',
           '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, first_txt, cst_txt, first_txt))
    f1 = s([p1, o1, feq], '3eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ph, SE, 'INL' if False else (('( inl ` <. %s , %s >. )' % (F_, A_)) if is_some else INR)))
    if is_some:
        INL = '( inl ` <. %s , %s >. )' % (F_, A_)
        opv = s([], 'opex', '<. %s , %s >. e. _V' % (F_, A_))
        ne = s([s([opv, w.inst('tmcinlne')], 'ax-mp', '-. %s = %s' % (INL, INR))], 'a1i', '( %s -> -. %s = %s )' % (ph, INL, INR))
        ne2 = s([ne, s([f1], 'eqeq1d', '( %s -> ( ( 1st ` %s ) = %s <-> %s = %s ) )' % (ph, SE, INR, INL, INR))], 'mtbird', '( %s -> -. ( 1st ` %s ) = %s )' % (ph, SE, INR))
        g = s([ne2], 'iffalsed', '( %s -> %s = ( 2nd ` ( 1st ` %s ) ) )' % (ph, GETD, SE))
        i2 = s([s([opv, w.inst('alginl2')], 'ax-mp', '( 2nd ` %s ) = <. %s , %s >.' % (INL, F_, A_))], 'a1i', '( %s -> ( 2nd ` %s ) = <. %s , %s >. )' % (ph, INL, F_, A_))
        g2 = s([g, s([f1], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` %s ) )' % (ph, SE, INL)), i2], '3eqtrd', '( %s -> %s = <. %s , %s >. )' % (ph, GETD, F_, A_))
        if fv is None:
            fv = s([s([], 'fvex', '%s e. _V' % F_)], 'a1i', '( %s -> %s e. _V )' % (ph, F_))
            av = s([s([], 'fvex', '%s e. _V' % A_)], 'a1i', '( %s -> %s e. _V )' % (ph, A_))
        a1 = s([fv, av, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, F_, A_, F_))
        a2 = s([fv, av, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, F_, A_, A_))
        p1_ = s([s([g2], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ph, GETD, F_, A_)), a1], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ph, GETD, F_))
        p2_ = s([s([g2], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (ph, GETD, F_, A_)), a2], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (ph, GETD, A_))
        oe = s([p1_, p2_], 'oveq12d', '( %s -> %s = ( %s encodeOutput %s ) )' % (ph, OUTS, F_, A_))
        assert out_txt == '( %s encodeOutput %s )' % (F_, A_), out_txt
        return init_eq(w, ph, '1', out_txt, OUTS, s([oe], 'eqcomd', '( %s -> %s = %s )' % (ph, out_txt, OUTS)))
    # none: GETD = <. 0 , (/) >. , OUTS = ( 0 encodeOutput (/) ) = <" 4 ">
    g = s([f1], 'iftrued', '( %s -> %s = <. 0 , (/) >. )' % (ph, GETD))
    a1 = s([s([s([], 'c0ex', '0 e. _V'), s([], '0ex', '(/) e. _V')], 'op1st', '( 1st ` <. 0 , (/) >. ) = 0')], 'a1i', '( %s -> ( 1st ` <. 0 , (/) >. ) = 0 )' % ph)
    a2 = s([s([s([], 'c0ex', '0 e. _V'), s([], '0ex', '(/) e. _V')], 'op2nd', '( 2nd ` <. 0 , (/) >. ) = (/)')], 'a1i', '( %s -> ( 2nd ` <. 0 , (/) >. ) = (/) )' % ph)
    p1_ = s([s([g], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. 0 , (/) >. ) )' % (ph, GETD)), a1], 'eqtrd', '( %s -> ( 1st ` %s ) = 0 )' % (ph, GETD))
    p2_ = s([s([g], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. 0 , (/) >. ) )' % (ph, GETD)), a2], 'eqtrd', '( %s -> ( 2nd ` %s ) = (/) )' % (ph, GETD))
    oe = s([p1_, p2_], 'oveq12d', '( %s -> %s = ( 0 encodeOutput (/) ) )' % (ph, OUTS))
    from t12_j_acc import encgam0
    en = s([closed(w, ph, '0nn0', '0 e. NN0'), w.inst('encoutnil')], 'syl', '( %s -> ( 0 encodeOutput (/) ) = ( ( encNatGam ` 0 ) ++ <" 4 "> ) )' % ph)
    e0 = s([encgam0(w, ph)], 'oveq1d', '( %s -> ( ( encNatGam ` 0 ) ++ <" 4 "> ) = ( (/) ++ <" 4 "> ) )' % ph)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    e1 = s([s4, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ <" 4 "> ) = <" 4 "> )' % ph)
    full = s([oe, en, e0, e1], '4eqtrd' if False else '3eqtrd', '') if False else None
    q1 = s([oe, en], 'eqtrd', '( %s -> %s = ( ( encNatGam ` 0 ) ++ <" 4 "> ) )' % (ph, OUTS))
    q2 = s([q1, e0, e1], '3eqtrd', '( %s -> %s = <" 4 "> )' % (ph, OUTS))
    return init_eq(w, ph, '1', COMMA1, OUTS, s([q2], 'eqcomd', '( %s -> <" 4 "> = %s )' % (ph, OUTS)))
