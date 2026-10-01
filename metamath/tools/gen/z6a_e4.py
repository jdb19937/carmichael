"""Sortie Z6a (agent z6ae): M_r is entire (Lean differentiable_Mr), z6mrhol, with the helpers z6ehtr .. z6ehfp:
entire functions of s (HOL on CC) are closed under constants, s |-> A ^ -s (A > 0), +, x., finite sums and finite
products.  The derivative of each piece is carried generically as ( ( CC _D F ) ` s ) (z6ehder), so dvmptadd / dvmptmul /
dvmptfsum / dvmptfprod apply without an explicit formula; z6ehdv turns a derivative mapping back into HOL (dvcn).
M_r ( s ) is z5mrval's finite sum over d of a coefficient times d ^ -s times a finite product over primes."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6alib import *
from c0lib import hyp
from cl import split_imp

TOPS = '( TopOpen ` CCfld )'
JC = '( %s |`t CC )' % TOPS
PRCC = 'CC e. { RR , CC }'


def D_(F):
    return '( CC _D %s )' % F


def z6ehtr():
    w = W('z6ehtr', 'Helper of z6mrhol: HOL on CC transfers along an equality of functions.')
    a = 'F = G'
    e1 = w.s([], 'eleq1', '( F = G -> ( F e. ( CC -cn-> CC ) <-> G e. ( CC -cn-> CC ) ) )')
    d = w.s([w.s([], 'oveq2', '( F = G -> ( CC _D F ) = ( CC _D G ) )')], 'dmeqd', '( F = G -> dom ( CC _D F ) = dom ( CC _D G ) )')
    e2 = w.s([d], 'sseq2d', '( F = G -> ( CC C_ dom ( CC _D F ) <-> CC C_ dom ( CC _D G ) ) )')
    w.qed([e1, e2], 'anbi12d', STATEMENTS['z6ehtr'])
    return w


def z6ehdv():
    w = W('z6ehdv', 'Helper of z6mrhol: a function CC --> CC whose derivative is a mapping defined on all of CC is HOL on CC (dvcn).')
    a = ante('z6ehdv'); st = mkst(w, a); F = MSS('A')
    h1 = st([], 'simpl', 'A. s e. CC A e. CC')
    fm = w.s([w.s([], 'eqid', '%s = %s' % (F, F))], 'fmpt', '( A. s e. CC A e. CC <-> %s : CC --> CC )' % F)
    ff = st([h1, fm], 'sylib', '%s : CC --> CC' % F)
    dq = st([], 'simprl', '%s = ( s e. CC |-> B )' % D_(F))
    dv = st([], 'simprr', 'A. s e. CC B e. V')
    dm1 = st([dv, w.inst('dmmptg')], 'syl', 'dom ( s e. CC |-> B ) = CC')
    dm2 = st([dq], 'dmeqd', 'dom %s = dom ( s e. CC |-> B )' % D_(F))
    dm = st([dm2, dm1], 'eqtrd', 'dom %s = CC' % D_(F))
    ss = w.s([], 'ssid', 'CC C_ CC')
    ssa = st([ss], 'a1i', 'CC C_ CC')
    cn = st([st([st([ssa, ff, ssa], '3jca', '( CC C_ CC /\\ %s : CC --> CC /\\ CC C_ CC )' % F), dm], 'jca',
                '( ( CC C_ CC /\\ %s : CC --> CC /\\ CC C_ CC ) /\\ dom %s = CC )' % (F, D_(F))), w.inst('dvcn')], 'syl', '%s e. ( CC -cn-> CC )' % F)
    sd = st([dm, w.inst('eqimss2')], 'syl', 'CC C_ dom %s' % D_(F))
    w.qed([cn, sd], 'jca', STATEMENTS['z6ehdv'])
    return w


def z6ehder():
    w = W('z6ehder', 'Helper of z6mrhol: the derivative of a function HOL on CC is a function CC --> CC, equal to the mapping of its values.')
    a = ante('z6ehder'); st = mkst(w, a); F = MSS('A'); DF = D_(F)
    ss = st([], 'simpr', 'CC C_ dom %s' % DF)
    dmle = st([w.s([], 'dvbsss', 'dom %s C_ CC' % DF)], 'a1i', 'dom %s C_ CC' % DF)
    dmeq = st([dmle, ss], 'eqssd', 'dom %s = CC' % DF)
    ff0 = st([w.s([], 'dvfcn', '%s : dom %s --> CC' % (DF, DF))], 'a1i', '%s : dom %s --> CC' % (DF, DF))
    fe = st([dmeq], 'feq2d', '( %s : dom %s --> CC <-> %s : CC --> CC )' % (DF, DF, DF))
    ff = st([ff0, fe], 'mpbid', '%s : CC --> CC' % DF)
    fn = st([ff], 'ffnd', '%s Fn CC' % DF)
    nf = w.s([w.s([], 'nfcv', 'F/_ s CC'), w.s([], 'nfcv', 'F/_ s _D'), w.s([], 'nfmpt1', 'F/_ s %s' % F)], 'nfov', 'F/_ s %s' % DF)
    d5 = w.s([nf], 'dffn5f', '( %s Fn CC <-> %s = ( s e. CC |-> ( %s ` s ) ) )' % (DF, DF, DF))
    eq = st([fn, st([d5], 'a1i', '( %s Fn CC <-> %s = ( s e. CC |-> ( %s ` s ) ) )' % (DF, DF, DF))], 'mpbid', '%s = ( s e. CC |-> ( %s ` s ) )' % (DF, DF))
    w.qed([ff, eq], 'jca', STATEMENTS['z6ehder'])
    return w


def _vals(w, ph, h, A, pre=None):
    """from h: ( ph -> ENT ( s |-> A ) ): steps ( ( ph /\\ s e. CC ) -> A e. CC ), ( ( ph /\\ s e. CC ) -> ( ( CC _D F ) ` s ) e. CC ),
    ( ph -> ( CC _D F ) = ( s e. CC |-> ( ( CC _D F ) ` s ) ) )"""
    F = MSS(A); DF = D_(F)
    cn = w.s([h], 'simpld', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, F))
    ff = w.s([cn, w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (ph, F))
    fm = w.s([w.s([], 'eqid', '%s = %s' % (F, F))], 'fmpt', '( A. s e. CC %s e. CC <-> %s : CC --> CC )' % (A, F))
    al = w.s([ff, fm], 'sylibr', '( %s -> A. s e. CC %s e. CC )' % (ph, A))
    av = w.s([al], 'r19.21bi', '( ( %s /\\ s e. CC ) -> %s e. CC )' % (ph, A))
    dr = w.s([h, w.inst('z6ehder')], 'syl', '( %s -> ( %s : CC --> CC /\\ %s = ( s e. CC |-> ( %s ` s ) ) ) )' % (ph, DF, DF, DF))
    dff = w.s([dr], 'simpld', '( %s -> %s : CC --> CC )' % (ph, DF))
    deq = w.s([dr], 'simprd', '( %s -> %s = ( s e. CC |-> ( %s ` s ) ) )' % (ph, DF, DF))
    dv = w.s([dff], 'ffvelcdmda', '( ( %s /\\ s e. CC ) -> ( %s ` s ) e. CC )' % (ph, DF))
    return av, dv, deq, '( %s ` s )' % DF


def _binop(lab, op, ref, res):
    w = W(lab, 'Helper of z6mrhol: HOL on CC is closed under %s (%s).' % (op, ref))
    h1 = hyp(w, '1', lab + '.1', HYPS[lab][0][1]); h2 = hyp(w, '2', lab + '.2', HYPS[lab][1][1])
    ph = 'ph'
    av, adv, aeq, A1 = _vals(w, ph, h1, 'A')
    bv, bdv, beq, B1 = _vals(w, ph, h2, 'B')
    s_ = w.s([w.s([], 'cnelprrecn', PRCC)], 'a1i', '( ph -> %s )' % PRCC)
    R = res(A1, B1)
    d = w.s([s_, av, adv, aeq, bv, bdv, beq], ref, '( ph -> %s = ( s e. CC |-> %s ) )' % (D_(MSS('( A %s B )' % op)), R))
    cl_ = w.s([av, bv], 'addcld' if op == '+' else 'mulcld', '( ( ph /\\ s e. CC ) -> ( A %s B ) e. CC )' % op)
    al = w.s([cl_], 'ralrimiva', '( ph -> A. s e. CC ( A %s B ) e. CC )' % op)
    vx = w.s([w.s([w.s([], 'ovex', '%s e. _V' % R)], 'rgenw', 'A. s e. CC %s e. _V' % R)], 'a1i', '( ph -> A. s e. CC %s e. _V )' % R)
    j = w.s([al, w.s([d, vx], 'jca', '( ph -> ( %s = ( s e. CC |-> %s ) /\\ A. s e. CC %s e. _V ) )' % (D_(MSS('( A %s B )' % op)), R, R))], 'jca',
            '( ph -> ( A. s e. CC ( A %s B ) e. CC /\\ ( %s = ( s e. CC |-> %s ) /\\ A. s e. CC %s e. _V ) ) )' % (op, D_(MSS('( A %s B )' % op)), R, R))
    w.qed([j, w.inst('z6ehdv')], 'syl', STATEMENTS[lab])
    return w


def z6ehadd():
    return _binop('z6ehadd', '+', 'dvmptadd', lambda a, b: '( %s + %s )' % (a, b))


def z6ehmul():
    return _binop('z6ehmul', 'x.', 'dvmptmul', lambda a, b: '( ( %s x. B ) + ( %s x. A ) )' % (a, b))


def z6ehc():
    w = W('z6ehc', 'Helper of z6mrhol: a constant is HOL on CC.')
    hyp(w, '1', 'z6ehc.1', HYPS['z6ehc'][0][1])
    s_ = w.s([w.s([], 'cnelprrecn', PRCC)], 'a1i', '( ph -> %s )' % PRCC)
    d = w.s([s_, '1'], 'dvmptc', '( ph -> %s = ( s e. CC |-> 0 ) )' % D_(MSS('B')))
    al = w.s([w.s(['1'], 'adantr', '( ( ph /\\ s e. CC ) -> B e. CC )')], 'ralrimiva', '( ph -> A. s e. CC B e. CC )')
    vx = w.s([w.s([w.s([], 'c0ex', '0 e. _V')], 'rgenw', 'A. s e. CC 0 e. _V')], 'a1i', '( ph -> A. s e. CC 0 e. _V )')
    j = w.s([al, w.s([d, vx], 'jca', '( ph -> ( %s = ( s e. CC |-> 0 ) /\\ A. s e. CC 0 e. _V ) )' % D_(MSS('B')))], 'jca',
            '( ph -> ( A. s e. CC B e. CC /\\ ( %s = ( s e. CC |-> 0 ) /\\ A. s e. CC 0 e. _V ) ) )' % D_(MSS('B')))
    w.qed([j, w.inst('z6ehdv')], 'syl', STATEMENTS['z6ehc'])
    return w


def z6ehx():
    w = W('z6ehx', 'Helper of z6mrhol: s |-> A ^ -s is HOL on CC for A > 0 (it is ( 1 / A ) ^ s, cxfhol).')
    a = 'A e. RR+'; st = mkst(w, a)
    u = st([w.s([], 'id', '( A e. RR+ -> A e. RR+ )')], 'rpreccld', '( 1 / A ) e. RR+')
    h = st([u, w.inst('cxfhol')], 'syl', ENTS(MSS('( ( 1 / A ) ^c s )')))
    b = '( A e. RR+ /\\ s e. CC )'
    ar = w.s([], 'simpl', '( %s -> A e. RR+ )' % b); sc = w.s([], 'simpr', '( %s -> s e. CC )' % b)
    e1 = w.s([ar, sc, w.inst('cxprec')], 'syl2anc', '( %s -> ( ( 1 / A ) ^c s ) = ( 1 / ( A ^c s ) ) )' % b)
    e2 = w.s([w.s([ar], 'rpcnd', '( %s -> A e. CC )' % b), w.s([ar], 'rpne0d', '( %s -> A =/= 0 )' % b), sc, w.inst('cxpneg')], 'syl3anc',
             '( %s -> ( A ^c -u s ) = ( 1 / ( A ^c s ) ) )' % b)
    e3 = w.s([e1, e2], 'eqtr4d', '( %s -> ( ( 1 / A ) ^c s ) = ( A ^c -u s ) )' % b)
    eq = st([e3], 'mpteq2dva', '%s = %s' % (MSS('( ( 1 / A ) ^c s )'), MSS('( A ^c -u s )')))
    tr = st([eq, w.inst('z6ehtr')], 'syl', '( %s <-> %s )' % (ENTS(MSS('( ( 1 / A ) ^c s )')), ENTS(MSS('( A ^c -u s )'))))
    w.qed([h, tr], 'mpbid', STATEMENTS['z6ehx'])
    return w


def _big(lab, kind):
    """z6ehfs / z6ehfp"""
    w = W(lab, 'Helper of z6mrhol: HOL on CC is closed under finite %s (%s).' % ('sums' if kind == 'sum' else 'products',
                                                                              'dvmptfsum' if kind == 'sum' else 'dvmptfprod'))
    for n_, f_ in HYPS[lab]:
        hyp(w, n_, lab + '.' + n_, f_)
    pi = '( ph /\\ i e. I )'
    av, adv, aeq, A1 = _vals(w, pi, '2', 'A')
    a3 = w.s([av], '3impa', '( ( ph /\\ i e. I /\\ s e. CC ) -> A e. CC )')
    b3 = w.s([adv], '3impa', '( ( ph /\\ i e. I /\\ s e. CC ) -> %s e. CC )' % A1)
    s_ = w.s([w.s([], 'cnelprrecn', PRCC)], 'a1i', '( ph -> %s )' % PRCC)
    jeq = w.s([], 'eqid', '%s = %s' % (JC, JC)); keq = w.s([], 'eqid', '%s = %s' % (TOPS, TOPS))
    top = w.s([keq], 'cnfldtop', '%s e. Top' % TOPS)
    rid = w.s([top, w.s([w.s([], 'unicntop', 'CC = U. %s' % TOPS)], 'restid', '( %s e. Top -> %s = %s )' % (TOPS, JC, TOPS))], 'ax-mp', '%s = %s' % (JC, TOPS))
    ccin = w.s([w.s([keq], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOPS), w.inst('toponmax')], 'ax-mp', 'CC e. %s' % TOPS)
    ccj = w.s([ccin, rid], 'eleqtrri', 'CC e. %s' % JC)
    x_ = w.s([ccj], 'a1i', '( ph -> CC e. %s )' % JC)
    if kind == 'sum':
        R = 'sum_ i e. I %s' % A1
        d = w.s([jeq, keq, s_, x_, '1', a3, b3, aeq], 'dvmptfsum', '( ph -> %s = ( s e. CC |-> %s ) )' % (D_(MSS('sum_ i e. I A')), R))
        body = 'sum_ i e. I A'
    else:
        Cj = '( ( CC _D ( s e. CC |-> E ) ) ` s )'
        e2 = w.s(['3'], 'mpteq2dv', '( i = j -> %s = ( s e. CC |-> E ) )' % MSS('A'))
        e3 = w.s([e2], 'oveq2d', '( i = j -> %s = ( CC _D ( s e. CC |-> E ) ) )' % D_(MSS('A')))
        bc = w.s([e3], 'fveq1d', '( i = j -> %s = %s )' % (A1, Cj))
        R = 'sum_ j e. I ( %s x. prod_ i e. ( I \\ { j } ) A )' % Cj
        d = w.s([w.s([], 'nfv', 'F/ i ph'), w.s([], 'nfv', 'F/ j ph'), jeq, keq, s_, x_, '1', a3, b3, aeq, bc], 'dvmptfprod',
                '( ph -> %s = ( s e. CC |-> %s ) )' % (D_(MSS('prod_ i e. I A')), R))
        body = 'prod_ i e. I A'
    ps = '( ph /\\ s e. CC )'
    fin = w.s(['1'], 'adantr', '( %s -> I e. Fin )' % ps)
    a32 = w.s([av], 'an32s', '( ( %s /\\ i e. I ) -> A e. CC )' % ps)
    cl_ = w.s([fin, a32], 'fsumcl' if kind == 'sum' else 'fprodcl', '( %s -> %s e. CC )' % (ps, body))
    al = w.s([cl_], 'ralrimiva', '( ph -> A. s e. CC %s e. CC )' % body)
    vx = w.s([w.s([w.s([], 'sumex', '%s e. _V' % R)], 'rgenw', 'A. s e. CC %s e. _V' % R)], 'a1i', '( ph -> A. s e. CC %s e. _V )' % R)
    j = w.s([al, w.s([d, vx], 'jca', '( ph -> ( %s = ( s e. CC |-> %s ) /\\ A. s e. CC %s e. _V ) )' % (D_(MSS(body)), R, R))], 'jca',
            '( ph -> ( A. s e. CC %s e. CC /\\ ( %s = ( s e. CC |-> %s ) /\\ A. s e. CC %s e. _V ) ) )' % (body, D_(MSS(body)), R, R))
    w.qed([j, w.inst('z6ehdv')], 'syl', STATEMENTS[lab])
    return w


def z6ehfs():
    return _big('z6ehfs', 'sum')





def _nfent(w, A):
    """F/ s ENT ( s e. CC |-> A )"""
    F = MSS(A)
    m = w.s([], 'nfmpt1', 'F/_ s %s' % F)
    e1 = w.s([m], 'nfel1', 'F/ s %s e. ( CC -cn-> CC )' % F)
    dv = w.s([w.s([], 'nfcv', 'F/_ s CC'), w.s([], 'nfcv', 'F/_ s _D'), m], 'nfov', 'F/_ s %s' % D_(F))
    e2 = w.s([w.s([], 'nfcv', 'F/_ s CC'), w.s([dv], 'nfdm', 'F/_ s dom %s' % D_(F))], 'nfss', 'F/ s CC C_ dom %s' % D_(F))
    return w.s([e1, e2], 'nfan', 'F/ s %s' % ENTS(F))


def z6ehmulc():
    w = W('z6ehmulc', 'Helper of z6mrhol: z6ehmul in closed form (holmul, then the bound variable t renamed to s).')
    a = ante('z6ehmulc'); st = mkst(w, a)
    FA = MSS('A'); FB = MSS('B')
    Xt = '( ( %s ` t ) x. ( %s ` t ) )' % (FA, FB); Xs = '( ( %s ` s ) x. ( %s ` s ) )' % (FA, FB)
    h = w.s([], 'holmul', '( %s -> %s )' % (a, ENTS('( t e. CC |-> %s )' % Xt)))
    nA = w.s([w.s([], 'nfmpt1', 'F/_ s %s' % FA), w.s([], 'nfcv', 'F/_ s t')], 'nffv', 'F/_ s ( %s ` t )' % FA)
    nB = w.s([w.s([], 'nfmpt1', 'F/_ s %s' % FB), w.s([], 'nfcv', 'F/_ s t')], 'nffv', 'F/_ s ( %s ` t )' % FB)
    n1 = w.s([nA, w.s([], 'nfcv', 'F/_ s x.'), nB], 'nfov', 'F/_ s %s' % Xt)
    n2 = w.s([], 'nfcv', 'F/_ t %s' % Xs)
    t3 = w.s([w.s([], 'fveq2', '( t = s -> ( %s ` t ) = ( %s ` s ) )' % (FA, FA)), w.s([], 'fveq2', '( t = s -> ( %s ` t ) = ( %s ` s ) )' % (FB, FB))],
             'oveq12d', '( t = s -> %s = %s )' % (Xt, Xs))
    cb = w.s([n1, n2, t3], 'cbvmpt', '( t e. CC |-> %s ) = ( s e. CC |-> %s )' % (Xt, Xs))
    b = '( %s /\\ s e. CC )' % a
    vals = []
    for X, F, part in (('A', FA, 'simpld'), ('B', FB, 'simprd')):
        en = st([], 'simpl' if X == 'A' else 'simpr', ENTS(F))
        ff = st([st([en], 'simpld', '%s e. ( CC -cn-> CC )' % F), w.inst('cncff')], 'syl', '%s : CC --> CC' % F)
        fm = w.s([w.s([], 'eqid', '%s = %s' % (F, F))], 'fmpt', '( A. s e. CC %s e. CC <-> %s : CC --> CC )' % (X, F))
        al = st([ff, fm], 'sylibr', 'A. s e. CC %s e. CC' % X)
        xv = w.s([al], 'r19.21bi', '( %s -> %s e. CC )' % (b, X))
        fv = w.s([w.s([], 'simpr', '( %s -> s e. CC )' % b), xv, w.s([w.s([], 'eqid', '%s = %s' % (F, F))], 'fvmpt2', '( ( s e. CC /\\ %s e. CC ) -> ( %s ` s ) = %s )' % (X, F, X))],
                 'syl2anc', '( %s -> ( %s ` s ) = %s )' % (b, F, X))
        vals.append(fv)
    pe = w.s(vals, 'oveq12d', '( %s -> %s = ( A x. B ) )' % (b, Xs))
    nfa = w.s([_nfent(w, 'A'), _nfent(w, 'B')], 'nfan', 'F/ s %s' % a)
    me = w.s([nfa, pe], 'mpteq2da', '( %s -> ( s e. CC |-> %s ) = %s )' % (a, Xs, MSS('( A x. B )')))
    eq = st([st([cb], 'a1i', '( t e. CC |-> %s ) = ( s e. CC |-> %s )' % (Xt, Xs)), me], 'eqtrd', '( t e. CC |-> %s ) = %s' % (Xt, MSS('( A x. B )')))
    tr = st([eq, w.inst('z6ehtr')], 'syl', '( %s <-> %s )' % (ENTS('( t e. CC |-> %s )' % Xt), ENTS(MSS('( A x. B )'))))
    w.qed([h, tr], 'mpbid', STATEMENTS['z6ehmulc'])
    return w


def z6ehfp():
    w = W('z6ehfp', 'Helper of z6mrhol: HOL on CC is closed under finite products (induction on the index set, findcard2d, with z6ehmulc).')
    for n_, f_ in HYPS['z6ehfp']:
        hyp(w, n_, 'z6ehfp.' + n_, f_)
    PS = lambda X: ENTS(MSS('prod_ i e. %s A' % X))
    def subst(Y):
        e = w.s([], 'prodeq1', '( x = %s -> prod_ i e. x A = prod_ i e. %s A )' % (Y, Y))
        m = w.s([e], 'mpteq2dv', '( x = %s -> %s = %s )' % (Y, MSS('prod_ i e. x A'), MSS('prod_ i e. %s A' % Y)))
        return w.s([m, w.inst('z6ehtr')], 'syl', '( x = %s -> ( %s <-> %s ) )' % (Y, PS('x'), PS(Y)))
    s0 = subst('(/)'); sy = subst('y'); syj = subst('( y u. { j } )'); sI = subst('I')
    # the base case
    p0 = w.s([w.s([], 'prod0', 'prod_ i e. (/) A = 1')], 'mpteq2i', '%s = %s' % (MSS('prod_ i e. (/) A'), MSS('1')))
    c1 = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( ph -> 1 e. CC )')], 'z6ehc', '( ph -> %s )' % ENTS(MSS('1')))
    t0 = w.s([p0, w.inst('z6ehtr')], 'ax-mp', '( %s <-> %s )' % (PS('(/)'), ENTS(MSS('1'))))
    ch = w.s([c1, t0], 'sylibr', '( ph -> %s )' % PS('(/)'))
    # the step
    q = '( ph /\\ ( y C_ I /\\ j e. ( I \\ y ) ) )'
    sq = mkst(w, q)
    jd = sq([], 'simprr', 'j e. ( I \\ y )')
    jI = sq([jd, w.inst('eldifi')], 'syl', 'j e. I'); njy = sq([jd, w.inst('eldifn')], 'syl', '-. j e. y')
    yI = sq([], 'simprl', 'y C_ I')
    yf = sq([w.s(['1'], 'adantr', '( %s -> I e. Fin )' % q), yI], 'ssfid', 'y e. Fin')
    al = w.s([w.s(['2'], 'ralrimiva', '( ph -> A. i e. I %s )' % ENTS(MSS('A')))], 'adantr', '( %s -> A. i e. I %s )' % (q, ENTS(MSS('A'))))
    t3 = w.s([w.s(['3'], 'mpteq2dv', '( i = j -> %s = %s )' % (MSS('A'), MSS('E'))), w.inst('z6ehtr')], 'syl',
             '( i = j -> ( %s <-> %s ) )' % (ENTS(MSS('A')), ENTS(MSS('E'))))
    eE = w.s([t3, al, jI], 'rspcdva', '( %s -> %s )' % (q, ENTS(MSS('E'))))
    qs = '( %s /\\ s e. CC )' % q
    # E e. CC
    ffE = sq([sq([eE], 'simpld', '%s e. ( CC -cn-> CC )' % MSS('E')), w.inst('cncff')], 'syl', '%s : CC --> CC' % MSS('E'))
    fmE = w.s([w.s([], 'eqid', '%s = %s' % (MSS('E'), MSS('E')))], 'fmpt', '( A. s e. CC E e. CC <-> %s : CC --> CC )' % MSS('E'))
    Ev = w.s([sq([ffE, fmE], 'sylibr', 'A. s e. CC E e. CC')], 'r19.21bi', '( %s -> E e. CC )' % qs)
    # A e. CC on y
    av, adv, aeq, A1 = _vals(w, '( ph /\\ i e. I )', '2', 'A')
    a3 = w.s([av], '3impa', '( ( ph /\\ i e. I /\\ s e. CC ) -> A e. CC )')
    T = '( %s /\\ i e. y )' % qs
    tph = w.s([], 'simplll', '( %s -> ph )' % T)
    tyI = w.s([w.s([], 'simpllr', '( %s -> ( y C_ I /\\ j e. ( I \\ y ) ) )' % T)], 'simpld', '( %s -> y C_ I )' % T)
    tiI = w.s([tyI, w.s([], 'simpr', '( %s -> i e. y )' % T)], 'sseldd', '( %s -> i e. I )' % T)
    tA = w.s([tph, tiI, w.s([], 'simplr', '( %s -> s e. CC )' % T), a3], 'syl3anc', '( %s -> A e. CC )' % T)
    PY = 'prod_ i e. y A'
    sp = w.s([w.s([], 'nfv', 'F/ i %s' % qs), w.s([], 'nfcv', 'F/_ i E'), w.s([yf], 'adantr', '( %s -> y e. Fin )' % qs),
              w.s([w.s([], 'vex', 'j e. _V')], 'a1i', '( %s -> j e. _V )' % qs), w.s([njy], 'adantr', '( %s -> -. j e. y )' % qs), tA, '3', Ev],
             'fprodsplitsn', '( %s -> prod_ i e. ( y u. { j } ) A = ( %s x. E ) )' % (qs, PY))
    me = sq([sp], 'mpteq2dva', '%s = %s' % (MSS('prod_ i e. ( y u. { j } ) A'), MSS('( %s x. E )' % PY)))
    tr2 = sq([me, w.inst('z6ehtr')], 'syl', '( %s <-> %s )' % (PS('( y u. { j } )'), ENTS(MSS('( %s x. E )' % PY))))
    mc = w.s([], 'z6ehmulc', '( ( %s /\\ %s ) -> %s )' % (PS('y'), ENTS(MSS('E')), ENTS(MSS('( %s x. E )' % PY))))
    mc2 = w.s([w.s([mc], 'ancoms', '( ( %s /\\ %s ) -> %s )' % (ENTS(MSS('E')), PS('y'), ENTS(MSS('( %s x. E )' % PY))))], 'ex',
              '( %s -> ( %s -> %s ) )' % (ENTS(MSS('E')), PS('y'), ENTS(MSS('( %s x. E )' % PY))))
    st1 = sq([eE, mc2], 'syl', '( %s -> %s )' % (PS('y'), ENTS(MSS('( %s x. E )' % PY))))
    stp = sq([st1, tr2], 'sylibrd', '( %s -> %s )' % (PS('y'), PS('( y u. { j } )')))
    w.qed([s0, sy, syj, sI, ch, stp, '1'], 'findcard2d', STATEMENTS['z6ehfp'])
    return w


def z6mrhol():
    w = W('z6mrhol', 'Lean differentiable_Mr: M_r is entire (HOL on CC).  By z5mrval M_r ( s ) is a finite sum over d of a constant times '
                     'd ^ -s times a finite product over primes p of ( 1 + c_p p ^ -s ); z6ehc, z6ehx, z6ehadd, z6ehmul, z6ehfs, z6ehfp.')
    a = ante('z6mrhol'); st = mkst(w, a)
    ar = st([], 'simplll', '( A e. RR /\\ 0 < A )')
    arr = st([ar], 'simpld', 'A e. RR'); a0 = st([ar], 'simprd', '0 < A')
    bb = st([], 'simpllr', '( B e. RR /\\ A < B )')
    brr = st([bb], 'simpld', 'B e. RR'); ab = st([bb], 'simprd', 'A < B')
    rn = st([], 'simplr', 'R e. NN'); cf = st([], 'simpr', 'C : NN --> CC')
    arp = st([arr, a0], 'elrpd', 'A e. RR+')
    brp = st([brr, st([st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), arr, brr, a0, ab], 'lttrd', '0 < B')], 'elrpd', 'B e. RR+')
    cex = st([cf, st([w.s([], 'nnex', 'NN e. _V')], 'a1i', 'NN e. _V'), w.inst('fex')], 'syl2anc', 'C e. _V')
    I = '( 1 ... ( |_ ` B ) )'
    Q = '{ q e. Prime | ( q || R /\\ -. q || d ) }'
    KD = '( ( ( ( A bvLam B ) ` d ) x. ( ( mmu ` ( R gcd d ) ) x. ( phi ` ( R gcd d ) ) ) ) x. ( C ` d ) )'
    CP = '( ( ( ( mmu ` p ) x. ( phi ` p ) ) - 1 ) x. ( C ` p ) )'
    FP = '( 1 + ( %s x. ( p ^c -u s ) ) )' % CP
    PD = 'prod_ p e. %s %s' % (Q, FP)
    TD = '( %s x. ( d ^c -u s ) )' % KD
    SUMM = '( %s x. %s )' % (TD, PD)
    SUMX = 'sum_ d e. %s %s' % (I, SUMM)
    # step 1: the values
    b = '( %s /\\ s e. CC )' % a
    zz = w.s([w.s([w.s([w.s([arr], 'adantr', '( %s -> A e. RR )' % b), w.s([brr], 'adantr', '( %s -> B e. RR )' % b)], 'jca', '( %s -> ( A e. RR /\\ B e. RR ) )' % b),
                   w.s([w.s([cex], 'adantr', '( %s -> C e. _V )' % b), w.s([rn], 'adantr', '( %s -> R e. NN )' % b)], 'jca', '( %s -> ( C e. _V /\\ R e. NN ) )' % b)],
                  'jca', '( %s -> ( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ R e. NN ) ) )' % b),
             w.s([], 'simpr', '( %s -> s e. CC )' % b)], 'jca', '( %s -> ( ( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ R e. NN ) ) /\\ s e. CC ) )' % b)
    v = w.s([zz, w.inst('z5mrval')], 'syl', '( %s -> %s = %s )' % (b, MR('s'), SUMX))
    eq = st([v], 'mpteq2dva', '%s = %s' % (MSS(MR('s')), MSS(SUMX)))
    # step 2: per d
    ad = '( %s /\\ d e. %s )' % (a, I)
    sd = mkst(w, ad)
    dn = sd([w.s([], 'simpr', '( %s -> d e. %s )' % (ad, I)), w.inst('elfznn')], 'syl', 'd e. NN')
    rnd = w.s([rn], 'adantr', '( %s -> R e. NN )' % ad)
    bl = sd([sd([w.s([arp], 'adantr', '( %s -> A e. RR+ )' % ad), w.s([brp], 'adantr', '( %s -> B e. RR+ )' % ad), w.s([ab], 'adantr', '( %s -> A < B )' % ad)], '3jca',
                '( A e. RR+ /\\ B e. RR+ /\\ A < B )'), dn, w.inst('bvlamre')], 'syl2anc', '( ( A bvLam B ) ` d ) e. RR')
    g = sd([rnd, dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd d ) e. NN')
    mu = sd([sd([g, w.inst('mucl')], 'syl', '( mmu ` ( R gcd d ) ) e. ZZ')], 'zcnd', '( mmu ` ( R gcd d ) ) e. CC')
    ph_ = sd([sd([g, w.inst('phicl')], 'syl', '( phi ` ( R gcd d ) ) e. NN')], 'nncnd', '( phi ` ( R gcd d ) ) e. CC')
    cfd = w.s([cf], 'adantr', '( %s -> C : NN --> CC )' % ad)
    cd = sd([cfd, dn], 'ffvelcdmd', '( C ` d ) e. CC')
    kd = sd([sd([sd([bl], 'recnd', '( ( A bvLam B ) ` d ) e. CC'), sd([mu, ph_], 'mulcld', '( ( mmu ` ( R gcd d ) ) x. ( phi ` ( R gcd d ) ) ) e. CC')], 'mulcld',
                '( ( ( A bvLam B ) ` d ) x. ( ( mmu ` ( R gcd d ) ) x. ( phi ` ( R gcd d ) ) ) ) e. CC'), cd], 'mulcld', '%s e. CC' % KD)
    e1 = w.s([kd], 'z6ehc', '( %s -> %s )' % (ad, ENTS(MSS(KD))))
    e2 = sd([sd([dn], 'nnrpd', 'd e. RR+'), w.inst('z6ehx')], 'syl', ENTS(MSS('( d ^c -u s )')))
    e3 = w.s([e1, e2], 'z6ehmul', '( %s -> %s )' % (ad, ENTS(MSS(TD))))
    # the product over p
    qs = w.s([w.s([w.s([], 'simpl', '( ( q || R /\\ -. q || d ) -> q || R )')], 'a1i', '( q e. Prime -> ( ( q || R /\\ -. q || d ) -> q || R ) )')],
             'ss2rabi', '%s C_ { q e. Prime | q || R }' % Q)
    qf = sd([sd([rnd, w.inst('prmdvdsfi')], 'syl', '{ q e. Prime | q || R } e. Fin'), sd([qs], 'a1i', '%s C_ { q e. Prime | q || R }' % Q)], 'ssfid', '%s e. Fin' % Q)
    adp = '( %s /\\ p e. %s )' % (ad, Q)
    sp = mkst(w, adp)
    pp = sp([w.s([], 'simpr', '( %s -> p e. %s )' % (adp, Q)), w.inst('elrabi')], 'syl', 'p e. Prime')
    pn = sp([pp, w.inst('prmnn')], 'syl', 'p e. NN')
    cfp = w.s([cfd], 'adantr', '( %s -> C : NN --> CC )' % adp)
    cp = sp([sp([sp([sp([sp([pn, w.inst('mucl')], 'syl', '( mmu ` p ) e. ZZ')], 'zcnd', '( mmu ` p ) e. CC'),
                     sp([sp([pn, w.inst('phicl')], 'syl', '( phi ` p ) e. NN')], 'nncnd', '( phi ` p ) e. CC')], 'mulcld', '( ( mmu ` p ) x. ( phi ` p ) ) e. CC'),
                 sp([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'subcld', '( ( ( mmu ` p ) x. ( phi ` p ) ) - 1 ) e. CC'),
             sp([cfp, pn], 'ffvelcdmd', '( C ` p ) e. CC')], 'mulcld', '%s e. CC' % CP)
    f1 = w.s([sp([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'z6ehc', '( %s -> %s )' % (adp, ENTS(MSS('1'))))
    f2 = w.s([cp], 'z6ehc', '( %s -> %s )' % (adp, ENTS(MSS(CP))))
    f3 = sp([sp([pn], 'nnrpd', 'p e. RR+'), w.inst('z6ehx')], 'syl', ENTS(MSS('( p ^c -u s )')))
    f4 = w.s([f2, f3], 'z6ehmul', '( %s -> %s )' % (adp, ENTS(MSS('( %s x. ( p ^c -u s ) )' % CP))))
    f5 = w.s([f1, f4], 'z6ehadd', '( %s -> %s )' % (adp, ENTS(MSS(FP))))
    CPJ = '( ( ( ( mmu ` j ) x. ( phi ` j ) ) - 1 ) x. ( C ` j ) )'
    FPJ = '( 1 + ( %s x. ( j ^c -u s ) ) )' % CPJ
    k1 = w.s([w.s([], 'fveq2', '( p = j -> ( mmu ` p ) = ( mmu ` j ) )'), w.s([], 'fveq2', '( p = j -> ( phi ` p ) = ( phi ` j ) )')], 'oveq12d',
             '( p = j -> ( ( mmu ` p ) x. ( phi ` p ) ) = ( ( mmu ` j ) x. ( phi ` j ) ) )')
    k2 = w.s([k1], 'oveq1d', '( p = j -> ( ( ( mmu ` p ) x. ( phi ` p ) ) - 1 ) = ( ( ( mmu ` j ) x. ( phi ` j ) ) - 1 ) )')
    k3 = w.s([k2, w.s([], 'fveq2', '( p = j -> ( C ` p ) = ( C ` j ) )')], 'oveq12d', '( p = j -> %s = %s )' % (CP, CPJ))
    k4 = w.s([k3, w.s([], 'oveq1', '( p = j -> ( p ^c -u s ) = ( j ^c -u s ) )')], 'oveq12d',
             '( p = j -> ( %s x. ( p ^c -u s ) ) = ( %s x. ( j ^c -u s ) ) )' % (CP, CPJ))
    k5 = w.s([k4], 'oveq2d', '( p = j -> %s = %s )' % (FP, FPJ))
    pr = w.s([qf, f5, k5], 'z6ehfp', '( %s -> %s )' % (ad, ENTS(MSS(PD))))
    e4 = w.s([e3, pr], 'z6ehmul', '( %s -> %s )' % (ad, ENTS(MSS(SUMM))))
    sm = w.s([st([w.s([], 'fzfi', '%s e. Fin' % I)], 'a1i', '%s e. Fin' % I), e4], 'z6ehfs', '( %s -> %s )' % (a, ENTS(MSS(SUMX))))
    tr = st([eq, w.inst('z6ehtr')], 'syl', '( %s <-> %s )' % (ENTS(MSS(MR('s'))), ENTS(MSS(SUMX))))
    w.qed([sm, tr], 'mpbird', STATEMENTS['z6mrhol'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        run(w)
