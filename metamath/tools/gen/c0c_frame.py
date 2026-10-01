"""Sortie C0c batch 7: the four edges of a rectangle avoid a strictly interior
point, and the punctured-frame rectangle calculus."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

RP = RE('P'); IP = IM('P')
B1 = PT(RB, IA); A1 = PT(RA, IB)
EDGES = [('A', B1), (B1, 'B'), ('B', A1), (A1, 'A')]
INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
PUNC = '( ( A crect B ) \\ { P } )'


def wctx(w, A0, base=None):
    """the geometric context of ( AB /\\ INT ) under the antecedent A0; base is a
    step proving ( A0 -> ( AB /\\ INT ) ), by default A0 itself is that conjunction."""
    d = {}
    if base is None:
        ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB)); it = w.s([], 'simpr', '( %s -> %s )' % (A0, INT))
    else:
        ab = w.s([base, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
        it = w.s([base, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, INT))
    d['base'] = base
    d['ab'] = ab
    d['ac'] = ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    d['bc'] = bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    d['pc'] = pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
    d['lr'] = lr = w.s([ineq, w.inst('simpll')], 'syl', '( %s -> %s < %s )' % (A0, RA, RP))
    d['rr'] = rr = w.s([ineq, w.inst('simplr')], 'syl', '( %s -> %s < %s )' % (A0, RP, RB))
    d['li'] = li = w.s([ineq, w.inst('simprl')], 'syl', '( %s -> %s < %s )' % (A0, IA, IP))
    d['ri'] = ri = w.s([ineq, w.inst('simprr')], 'syl', '( %s -> %s < %s )' % (A0, IP, IB))
    d['ar'] = ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
    d['br'] = br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
    d['ai'] = ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
    d['bi'] = bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
    d['pr'] = pr = w.s([pc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RP))
    d['pi'] = pi = w.s([pc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IP))
    d['ler'] = w.s([w.s([ar, pr, br, lr, rr], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB))
    d['lei'] = w.s([w.s([ai, pi, bi, li, ri], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))
    d['geo'] = w.s([d['ler'], d['lei']], 'jca', '( %s -> %s )' % (A0, GEO))
    d['abg'] = abg = w.s([ab, d['geo']], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
    ic = closed(w, A0, 'ax-icn', '_i e. CC')
    d['b1c'] = w.s([w.s([br], 'recnd', '( %s -> %s e. CC )' % (A0, RB)),
                    w.s([ic, w.s([ai], 'recnd', '( %s -> %s e. CC )' % (A0, IA))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IA))],
                   'addcld', '( %s -> %s e. CC )' % (A0, B1))
    d['a1c'] = w.s([w.s([ar], 'recnd', '( %s -> %s e. CC )' % (A0, RA)),
                    w.s([ic, w.s([bi], 'recnd', '( %s -> %s e. CC )' % (A0, IB))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IB))],
                   'addcld', '( %s -> %s e. CC )' % (A0, A1))
    d['reB1'] = w.s([br, ai, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, B1, RB))
    d['imB1'] = w.s([br, ai, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, B1, IA))
    d['reA1'] = w.s([ar, bi, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, A1, RA))
    d['imA1'] = w.s([ar, bi, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, A1, IB))
    for nm, lab, pt in (('pA', 'crectcnr1', 'A'), ('pP10', 'crectcnr2', B1), ('pB', 'crectcnr3', 'B'), ('pP01', 'crectcnr4', A1)):
        d[nm] = w.s([abg, w.inst(lab)], 'syl', '( %s -> %s e. ( A crect B ) )' % (A0, pt))
    d['cc'] = {'A': ac, 'B': bc, B1: d['b1c'], A1: d['a1c']}
    d['pt'] = {'A': d['pA'], B1: d['pP10'], 'B': d['pB'], A1: d['pP01']}
    return d


def frame(label, S, T, F, cons, eqS, eqT, hypne, desc):
    w = W(label, desc)
    A0 = '( %s /\\ %s )' % (AB, INT)
    A1 = '( %s /\\ u e. ( %s cseg %s ) )' % (A0, S, T)
    d = wctx(w, A0)
    geoeq = w.s([d[eqS], d[eqT]], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A0, F, S, F, T)) if eqS != eqT else None
    con = w.s([w.s([d['cc'][S], d['cc'][T], geoeq], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ ( %s ` %s ) = ( %s ` %s ) ) )' % (A0, S, T, F, S, F, T)),
               w.inst(cons)], 'syl', '( %s -> A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` %s ) )' % (A0, S, T, F, F, S))
    pq = w.s([d['pt'][S], d['pt'][T]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, S, T))
    cvx = w.s([d['ab'], pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A0, S, T))
    umem = w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (A1, S, T))
    inr = w.s([w.s([cvx], 'adantr', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A1, S, T)), umem], 'sseldd', '( %s -> u e. ( A crect B ) )' % A1)
    cst = w.s([w.s([con], 'adantr', '( %s -> A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` %s ) )' % (A1, S, T, F, F, S)), umem, w.inst('rspa')],
              'syl2anc', '( %s -> ( %s ` u ) = ( %s ` %s ) )' % (A1, F, F, S))
    ne1 = w.s([cst, w.s([w.s([d[eqS]], 'adantr', '( %s -> ( %s ` %s ) = %s )' % (A1, F, S, hypne[0])), w.s([hypne[1]], 'adantr', '( %s -> %s )' % (A1, hypne[2]))],
                        'eqnetrd', '( %s -> ( %s ` %s ) =/= ( %s ` P ) )' % (A1, F, S, F))], 'eqnetrd', '( %s -> ( %s ` u ) =/= ( %s ` P ) )' % (A1, F, F))
    fq = w.s([], 'fveq2', '( u = P -> ( %s ` u ) = ( %s ` P ) )' % (F, F))
    une = w.s([w.s([w.s([ne1], 'neneqd', '( %s -> -. ( %s ` u ) = ( %s ` P ) )' % (A1, F, F)), w.s([fq], 'a1i', '( %s -> ( u = P -> ( %s ` u ) = ( %s ` P ) ) )' % (A1, F, F))],
                   'mtod', '( %s -> -. u = P )' % A1)], 'neqned', '( %s -> u =/= P )' % A1)
    mem = w.s([w.s([inr, une], 'jca', '( %s -> ( u e. ( A crect B ) /\\ u =/= P ) )' % A1), w.inst('eldifsn')], 'sylibr', '( %s -> u e. %s )' % (A1, PUNC))
    w.qed([w.s([mem], 'ex', '( %s -> ( u e. ( %s cseg %s ) -> u e. %s ) )' % (A0, S, T, PUNC))], 'ssrdv',
          '( %s -> ( %s cseg %s ) C_ %s )' % (A0, S, T, PUNC)); run(w)


if True:
    # the =/= facts for the four coordinate values, built inside each lemma
    def mk(label, S, T, F, cons, eqS, eqT, which, desc):
        w = W(label, desc)
        A0 = '( %s /\\ %s )' % (AB, INT)
        A1 = '( %s /\\ u e. ( %s cseg %s ) )' % (A0, S, T)
        d = wctx(w, A0)
        VAL = {'ia': IA, 'ib': IB, 'ra': RA, 'rb': RB}[which]
        FP = '( %s ` P )' % F
        if which == 'ia':
            ne = w.s([d['ai'], d['li']], 'ltned', '( %s -> %s =/= %s )' % (A0, VAL, FP))
        elif which == 'ib':
            ne = w.s([d['pi'], d['ri']], 'gtned', '( %s -> %s =/= %s )' % (A0, VAL, FP))
        elif which == 'ra':
            ne = w.s([d['ar'], d['lr']], 'ltned', '( %s -> %s =/= %s )' % (A0, VAL, FP))
        else:
            ne = w.s([d['pr'], d['rr']], 'gtned', '( %s -> %s =/= %s )' % (A0, VAL, FP))
        cS = d[eqS] if eqS else w.s([], 'eqidd', '( %s -> ( %s ` %s ) = %s )' % (A0, F, S, VAL))
        cT = d[eqT] if eqT else w.s([], 'eqidd', '( %s -> ( %s ` %s ) = %s )' % (A0, F, T, VAL))
        geoeq = w.s([cS, cT], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A0, F, S, F, T))
        con = w.s([w.s([d['cc'][S], d['cc'][T], geoeq], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ ( %s ` %s ) = ( %s ` %s ) ) )' % (A0, S, T, F, S, F, T)),
                   w.inst(cons)], 'syl', '( %s -> A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` %s ) )' % (A0, S, T, F, F, S))
        pq = w.s([d['pt'][S], d['pt'][T]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, S, T))
        cvx = w.s([d['ab'], pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A0, S, T))
        umem = w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (A1, S, T))
        inr = w.s([w.s([cvx], 'adantr', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A1, S, T)), umem], 'sseldd', '( %s -> u e. ( A crect B ) )' % A1)
        cst = w.s([w.s([con], 'adantr', '( %s -> A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` %s ) )' % (A1, S, T, F, F, S)), umem, w.inst('rspa')],
                  'syl2anc', '( %s -> ( %s ` u ) = ( %s ` %s ) )' % (A1, F, F, S))
        ne2 = w.s([cst, w.s([w.s([cS], 'adantr', '( %s -> ( %s ` %s ) = %s )' % (A1, F, S, VAL)), w.s([ne], 'adantr', '( %s -> %s =/= %s )' % (A1, VAL, FP))],
                            'eqnetrd', '( %s -> ( %s ` %s ) =/= %s )' % (A1, F, S, FP))], 'eqnetrd', '( %s -> ( %s ` u ) =/= %s )' % (A1, F, FP))
        fq = w.s([], 'fveq2', '( u = P -> ( %s ` u ) = %s )' % (F, FP))
        une = w.s([w.s([w.s([ne2], 'neneqd', '( %s -> -. ( %s ` u ) = %s )' % (A1, F, FP)),
                        w.s([fq], 'a1i', '( %s -> ( u = P -> ( %s ` u ) = %s ) )' % (A1, F, FP))], 'mtod', '( %s -> -. u = P )' % A1)],
                  'neqned', '( %s -> u =/= P )' % A1)
        mem = w.s([w.s([inr, une], 'jca', '( %s -> ( u e. ( A crect B ) /\\ u =/= P ) )' % A1), w.inst('eldifsn')], 'sylibr', '( %s -> u e. %s )' % (A1, PUNC))
        w.qed([w.s([mem], 'ex', '( %s -> ( u e. ( %s cseg %s ) -> u e. %s ) )' % (A0, S, T, PUNC))], 'ssrdv',
              '( %s -> ( %s cseg %s ) C_ %s )' % (A0, S, T, PUNC)); run(w)

    mk('crectfe1', 'A', B1, 'Im', 'cseghim', None, 'imB1', 'ia', 'The bottom edge of a rectangle avoids a strictly interior point.')
    mk('crectfe2', B1, 'B', 'Re', 'csegvre', 'reB1', None, 'rb', 'The right edge of a rectangle avoids a strictly interior point.')
    mk('crectfe3', 'B', A1, 'Im', 'cseghim', None, 'imA1', 'ib', 'The top edge of a rectangle avoids a strictly interior point.')
    mk('crectfe4', A1, 'A', 'Re', 'csegvre', 'reA1', None, 'ra', 'The left edge of a rectangle avoids a strictly interior point.')

# ---- lintlc: a pointwise linear combination of two continuous functions
KY = '( y e. D |-> ( ( C x. ( G ` y ) ) + ( H ` y ) ) )'
MY = '( y e. D |-> ( C x. ( G ` y ) ) )'
GH = '( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D )'
FCG = '( F e. V /\\ C e. CC /\\ %s )' % GH
w = W('lintlc', 'The line integral of a pointwise linear combination of two continuous functions.')
A0 = '( %s /\\ %s /\\ A. u e. ( A cseg B ) ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) )' % (AB, FCG)
A1 = '( %s /\\ v e. ( A cseg B ) )' % A0
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
fcg = w.s([], 'simp2', '( %s -> %s )' % (A0, FCG))
alu = w.s([], 'simp3', '( %s -> A. u e. ( A cseg B ) ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) )' % A0)
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
fv = w.s([fcg, w.inst('simp1')], 'syl', '( %s -> F e. V )' % A0)
cc = w.s([fcg, w.inst('simp2')], 'syl', '( %s -> C e. CC )' % A0)
gh = w.s([fcg, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, GH))
gcn = w.s([gh, w.inst('simp1')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
hcn = w.s([gh, w.inst('simp2')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
sg = w.s([gh, w.inst('simp3')], 'syl', '( %s -> ( A cseg B ) C_ D )' % A0)
dss = w.s([gcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A0)
hf = w.s([hcn, w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % A0)
gmp = w.s([w.s([gf], 'feqmptd', '( %s -> G = ( y e. D |-> ( G ` y ) ) )' % A0), gcn], 'eqeltrrd',
          '( %s -> ( y e. D |-> ( G ` y ) ) e. ( D -cn-> CC ) )' % A0)
hmp = w.s([w.s([hf], 'feqmptd', '( %s -> H = ( y e. D |-> ( H ` y ) ) )' % A0), hcn], 'eqeltrrd',
          '( %s -> ( y e. D |-> ( H ` y ) ) e. ( D -cn-> CC ) )' % A0)
ccc = closed(w, A0, 'ssid', 'CC C_ CC')
cmp = w.s([cc, dss, ccc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( y e. D |-> C ) e. ( D -cn-> CC ) )' % A0)
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn0 = w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
mcn = w.s([mcn0], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
acn0 = w.s([ej], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
acn = w.s([acn0], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
mmp = w.s([ej, mcn, cmp, gmp], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, MY))
kmp = w.s([ej, acn, mmp, hmp], 'cncfmpt2f', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, KY))
# the three pointwise identities, in the fresh variable v
vmem = w.s([], 'simpr', '( %s -> v e. ( A cseg B ) )' % A1)
sg1 = w.s([sg], 'adantr', '( %s -> ( A cseg B ) C_ D )' % A1)
vd = w.s([sg1, vmem], 'sseldd', '( %s -> v e. D )' % A1)
gv = w.s([w.s([gf], 'adantr', '( %s -> G : D --> CC )' % A1), vd], 'ffvelcdmd', '( %s -> ( G ` v ) e. CC )' % A1)
hv = w.s([w.s([hf], 'adantr', '( %s -> H : D --> CC )' % A1), vd], 'ffvelcdmd', '( %s -> ( H ` v ) e. CC )' % A1)
cc1 = w.s([cc], 'adantr', '( %s -> C e. CC )' % A1)
cgv = w.s([cc1, gv], 'mulcld', '( %s -> ( C x. ( G ` v ) ) e. CC )' % A1)
kvv = w.s([cgv, hv], 'addcld', '( %s -> ( ( C x. ( G ` v ) ) + ( H ` v ) ) e. CC )' % A1)
s1 = w.s([], 'fveq2', '( y = v -> ( G ` y ) = ( G ` v ) )')
s2 = w.s([s1], 'oveq2d', '( y = v -> ( C x. ( G ` y ) ) = ( C x. ( G ` v ) ) )')
s3 = w.s([], 'fveq2', '( y = v -> ( H ` y ) = ( H ` v ) )')
s4 = w.s([s2, s3], 'oveq12d', '( y = v -> ( ( C x. ( G ` y ) ) + ( H ` y ) ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) )')
eqk = w.s([], 'eqid', '%s = %s' % (KY, KY))
eqm = w.s([], 'eqid', '%s = %s' % (MY, MY))
kvi = w.s([s4, eqk], 'fvmptg', '( ( v e. D /\\ ( ( C x. ( G ` v ) ) + ( H ` v ) ) e. CC ) -> ( %s ` v ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) )' % KY)
kv = w.s([vd, kvv, kvi], 'syl2anc', '( %s -> ( %s ` v ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) )' % (A1, KY))
mvi = w.s([s2, eqm], 'fvmptg', '( ( v e. D /\\ ( C x. ( G ` v ) ) e. CC ) -> ( %s ` v ) = ( C x. ( G ` v ) ) )' % MY)
mv = w.s([vd, cgv, mvi], 'syl2anc', '( %s -> ( %s ` v ) = ( C x. ( G ` v ) ) )' % (A1, MY))
u1 = w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')
u2 = w.s([], 'fveq2', '( u = v -> ( G ` u ) = ( G ` v ) )')
u3 = w.s([u2], 'oveq2d', '( u = v -> ( C x. ( G ` u ) ) = ( C x. ( G ` v ) ) )')
u4 = w.s([], 'fveq2', '( u = v -> ( H ` u ) = ( H ` v ) )')
u5 = w.s([u3, u4], 'oveq12d', '( u = v -> ( ( C x. ( G ` u ) ) + ( H ` u ) ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) )')
usub = w.s([u1, u5], 'eqeq12d', '( u = v -> ( ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) <-> ( F ` v ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) ) )')
fv1 = w.s([usub, w.s([alu], 'adantr', '( %s -> A. u e. ( A cseg B ) ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) )' % A1), vmem], 'rspcdva',
          '( %s -> ( F ` v ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) )' % A1)
alfk = w.s([w.s([fv1, kv], 'eqtr4d', '( %s -> ( F ` v ) = ( %s ` v ) )' % (A1, KY))], 'ralrimiva',
           '( %s -> A. v e. ( A cseg B ) ( F ` v ) = ( %s ` v ) )' % (A0, KY))
alkmh = w.s([w.s([kv, w.s([mv], 'oveq1d', '( %s -> ( ( %s ` v ) + ( H ` v ) ) = ( ( C x. ( G ` v ) ) + ( H ` v ) ) )' % (A1, MY))], 'eqtr4d',
                 '( %s -> ( %s ` v ) = ( ( %s ` v ) + ( H ` v ) ) )' % (A1, KY, MY))], 'ralrimiva',
            '( %s -> A. v e. ( A cseg B ) ( %s ` v ) = ( ( %s ` v ) + ( H ` v ) ) )' % (A0, KY, MY))
almg = w.s([mv], 'ralrimiva', '( %s -> A. v e. ( A cseg B ) ( %s ` v ) = ( C x. ( G ` v ) ) )' % (A0, MY))
# assemble
kex = w.s([kmp, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, KY))
fex = w.s([fv, w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
leq = w.s([w.s([w.s([ac, bc], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A0), w.s([fex, kex], 'jca', '( %s -> ( F e. _V /\\ %s e. _V ) )' % (A0, KY))], 'jca',
               '( %s -> ( ( A e. CC /\\ B e. CC ) /\\ ( F e. _V /\\ %s e. _V ) ) )' % (A0, KY)), alfk, w.inst('linteq')], 'syl2anc',
          '( %s -> %s = %s )' % (A0, LINT('F', 'A', 'B'), LINT(KY, 'A', 'B')))
phk = w.s([w.s([ac, bc], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A0), w.s([kmp, sg], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % (A0, KY))],
          'jca', '( %s -> ( ( A e. CC /\\ B e. CC ) /\\ ( %s e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) ) )' % (A0, KY))
add = w.s([phk, w.s([mmp, hcn], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) ) )' % (A0, MY)), alkmh, w.inst('lintadd2')], 'syl3anc',
          '( %s -> %s = ( %s + %s ) )' % (A0, LINT(KY, 'A', 'B'), LINT(MY, 'A', 'B'), LINT('H', 'A', 'B')))
phm = w.s([w.s([ac, bc], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A0), w.s([mmp, sg], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % (A0, MY))],
          'jca', '( %s -> ( ( A e. CC /\\ B e. CC ) /\\ ( %s e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) ) )' % (A0, MY))
mul = w.s([phm, w.s([gcn, cc], 'jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ C e. CC ) )' % A0), almg, w.inst('lintmulc2')], 'syl3anc',
          '( %s -> %s = ( C x. %s ) )' % (A0, LINT(MY, 'A', 'B'), LINT('G', 'A', 'B')))
w.qed([w.s([leq, add], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, LINT('F', 'A', 'B'), LINT(MY, 'A', 'B'), LINT('H', 'A', 'B'))),
       w.s([mul], 'oveq1d', '( %s -> ( %s + %s ) = ( ( C x. %s ) + %s ) )' % (A0, LINT(MY, 'A', 'B'), LINT('H', 'A', 'B'), LINT('G', 'A', 'B'), LINT('H', 'A', 'B')))],
      'eqtrd', '( %s -> %s = ( ( C x. %s ) + %s ) )' % (A0, LINT('F', 'A', 'B'), LINT('G', 'A', 'B'), LINT('H', 'A', 'B'))); run(w)

A1 = PT(RA, IB)
FEQ = {('A', B1): 'crectfe1', (B1, 'B'): 'crectfe2', ('B', A1): 'crectfe3', (A1, 'A'): 'crectfe4'}

# ---- rectinteqp: the boundary integral depends only on the values off P
w = W('rectinteqp', 'A rectangle boundary integral depends only on the values of the function on the rectangle with a strictly interior point removed.')
FG = '( F e. V /\\ G e. V )'
EQP = 'A. u e. %s ( F ` u ) = ( G ` u )' % PUNC
A0 = '( ( %s /\\ %s ) /\\ %s /\\ %s )' % (AB, INT, FG, EQP)
base = w.s([], 'simp1', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT))
d = wctx(w, A0, base)
fg = w.s([], 'simp2', '( %s -> %s )' % (A0, FG))
eqp = w.s([], 'simp3', '( %s -> %s )' % (A0, EQP))
fv = w.s([fg, w.inst('simpl')], 'syl', '( %s -> F e. V )' % A0)
gv = w.s([fg, w.inst('simpr')], 'syl', '( %s -> G e. V )' % A0)
fex = w.s([fv, w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
gex = w.s([gv, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
fgex = w.s([fex, gex], 'jca', '( %s -> ( F e. _V /\\ G e. _V ) )' % A0)
eqs = []
for S, T in EDGES:
    ss = w.s([base, w.inst(FEQ[(S, T)])], 'syl', '( %s -> ( %s cseg %s ) C_ %s )' % (A0, S, T, PUNC))
    sr = w.s([ss, w.inst('ssralv')], 'syl', '( %s -> ( %s -> A. u e. ( %s cseg %s ) ( F ` u ) = ( G ` u ) ) )' % (A0, EQP, S, T))
    al = w.s([sr, eqp], 'mpd', '( %s -> A. u e. ( %s cseg %s ) ( F ` u ) = ( G ` u ) )' % (A0, S, T))
    h = w.s([w.s([d['cc'][S], d['cc'][T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T)), fgex], 'jca',
            '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. _V /\\ G e. _V ) ) )' % (A0, S, T))
    eqs.append(w.s([h, al, w.inst('linteq')], 'syl2anc', '( %s -> %s = %s )' % (A0, LINT('F', S, T), LINT('G', S, T))))
rvf = w.s([fv, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B')))
rvg = w.s([gv, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('G', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
p1 = w.s([eqs[0], eqs[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]), LINT('G', *EDGES[0]), LINT('G', *EDGES[1])))
p2 = w.s([eqs[2], eqs[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3]), LINT('G', *EDGES[2]), LINT('G', *EDGES[3])))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
w.qed([w.s([rvf, p3], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint'))), rvg], 'eqtr4d',
      '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RINT('G', 'A', 'B'))); run(w)

# ---- rectintlcp: a pointwise linear combination off a strictly interior point
w = W('rectintlcp', 'The rectangle boundary integral of a pointwise linear combination of two functions continuous off a strictly interior point.')
GHP = '( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ %s C_ D )' % PUNC
FCGP = '( F e. V /\\ C e. CC /\\ %s )' % GHP
EQL = 'A. u e. %s ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) )' % PUNC
A0 = '( ( %s /\\ %s ) /\\ %s /\\ %s )' % (AB, INT, FCGP, EQL)
base = w.s([], 'simp1', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT))
d = wctx(w, A0, base)
fcg = w.s([], 'simp2', '( %s -> %s )' % (A0, FCGP))
eql = w.s([], 'simp3', '( %s -> %s )' % (A0, EQL))
fv = w.s([fcg, w.inst('simp1')], 'syl', '( %s -> F e. V )' % A0)
cc = w.s([fcg, w.inst('simp2')], 'syl', '( %s -> C e. CC )' % A0)
gh = w.s([fcg, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, GHP))
gcn = w.s([gh, w.inst('simp1')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
hcn = w.s([gh, w.inst('simp2')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
pss = w.s([gh, w.inst('simp3')], 'syl', '( %s -> %s C_ D )' % (A0, PUNC))
gex = w.s([gcn, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
hex = w.s([hcn, w.inst('elex')], 'syl', '( %s -> H e. _V )' % A0)
G4 = []; H4 = []; CG4 = []; ccm = {}; sts = []
for S, T in EDGES:
    ss = w.s([base, w.inst(FEQ[(S, T)])], 'syl', '( %s -> ( %s cseg %s ) C_ %s )' % (A0, S, T, PUNC))
    sd = w.s([ss, pss], 'sstrd', '( %s -> ( %s cseg %s ) C_ D )' % (A0, S, T))
    sr = w.s([ss, w.inst('ssralv')], 'syl', '( %s -> ( %s -> A. u e. ( %s cseg %s ) ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) ) )' % (A0, EQL, S, T))
    al = w.s([sr, eql], 'mpd', '( %s -> A. u e. ( %s cseg %s ) ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) )' % (A0, S, T))
    st_ = w.s([gcn, hcn, sd], '3jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (A0, S, T))
    h2 = w.s([fv, cc, st_], '3jca', '( %s -> ( F e. V /\\ C e. CC /\\ ( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) ) )' % (A0, S, T))
    h1 = w.s([d['cc'][S], d['cc'][T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    sts.append(w.s([h1, h2, al, w.inst('lintlc')], 'syl3anc',
                   '( %s -> %s = ( ( C x. %s ) + %s ) )' % (A0, LINT('F', S, T), LINT('G', S, T), LINT('H', S, T))))
    phg = w.s([h1, w.s([gcn, sd], 'jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (A0, S, T))], 'jca',
              '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) ) )' % (A0, S, T, S, T))
    phh = w.s([h1, w.s([hcn, sd], 'jca', '( %s -> ( H e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (A0, S, T))], 'jca',
              '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( H e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) ) )' % (A0, S, T, S, T))
    gcl = w.s([phg, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('G', S, T)))
    hcl = w.s([phh, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('H', S, T)))
    ccm[LINT('G', S, T)] = gcl; ccm[LINT('H', S, T)] = hcl
    ccm['( C x. %s )' % LINT('G', S, T)] = w.s([cc, gcl], 'mulcld', '( %s -> ( C x. %s ) e. CC )' % (A0, LINT('G', S, T)))
    G4.append(LINT('G', S, T)); H4.append(LINT('H', S, T)); CG4.append('( C x. %s )' % LINT('G', S, T))
rvf = w.s([fv, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B')))
rvg = w.s([gex, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('G', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
rvh = w.s([hex, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('H', 'A', 'B'), RAW('A', 'B').replace('F lint', 'H lint')))
treeL = ('+', ('+', ('+', CG4[0], H4[0]), ('+', CG4[1], H4[1])), ('+', ('+', CG4[2], H4[2]), ('+', CG4[3], H4[3])))
p1 = w.s([sts[0], sts[1]], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]), tree_text(treeL[1])))
p2 = w.s([sts[2], sts[3]], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3]), tree_text(treeL[2])))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), tree_text(treeL)))
key = {}
for i, x in enumerate(CG4): key[x] = i
for i, x in enumerate(H4): key[x] = 4 + i
cs = CxSum(w, A0, ccm, key)
nL, atL = cs.nf(treeL)
lhs = w.s([w.s([rvf, p3], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), tree_text(treeL))), nL], 'eqtrd',
          '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), rn(atL)))
# the right-hand side: expand C x. ( G rectint ) by adddid three times
GS1 = '( %s + %s )' % (G4[0], G4[1]); GS2 = '( %s + %s )' % (G4[2], G4[3])
cg1 = w.s([ccm[G4[0]], ccm[G4[1]]], 'addcld', '( %s -> %s e. CC )' % (A0, GS1))
cg2 = w.s([ccm[G4[2]], ccm[G4[3]]], 'addcld', '( %s -> %s e. CC )' % (A0, GS2))
a1 = w.s([cc, ccm[G4[0]], ccm[G4[1]]], 'adddid', '( %s -> ( C x. %s ) = ( %s + %s ) )' % (A0, GS1, CG4[0], CG4[1]))
a2 = w.s([cc, ccm[G4[2]], ccm[G4[3]]], 'adddid', '( %s -> ( C x. %s ) = ( %s + %s ) )' % (A0, GS2, CG4[2], CG4[3]))
a3 = w.s([cc, cg1, cg2], 'adddid', '( %s -> ( C x. ( %s + %s ) ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, GS1, GS2, GS1, GS2))
treeCG = ('+', ('+', CG4[0], CG4[1]), ('+', CG4[2], CG4[3]))
a4 = w.s([a3, w.s([a1, a2], 'oveq12d', '( %s -> ( ( C x. %s ) + ( C x. %s ) ) = %s )' % (A0, GS1, GS2, tree_text(treeCG)))], 'eqtrd',
         '( %s -> ( C x. ( %s + %s ) ) = %s )' % (A0, GS1, GS2, tree_text(treeCG)))
cgr = w.s([w.s([rvg], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. ( %s + %s ) ) )' % (A0, RINT('G', 'A', 'B'), GS1, GS2)), a4], 'eqtrd',
          '( %s -> ( C x. %s ) = %s )' % (A0, RINT('G', 'A', 'B'), tree_text(treeCG)))
treeH = ('+', ('+', H4[0], H4[1]), ('+', H4[2], H4[3]))
treeR = ('+', treeCG, treeH)
sm = w.s([cgr, rvh], 'oveq12d', '( %s -> ( ( C x. %s ) + %s ) = %s )' % (A0, RINT('G', 'A', 'B'), RINT('H', 'A', 'B'), tree_text(treeR)))
nR, atR = cs.nf(treeR)
rhs = w.s([sm, nR], 'eqtrd', '( %s -> ( ( C x. %s ) + %s ) = %s )' % (A0, RINT('G', 'A', 'B'), RINT('H', 'A', 'B'), rn(atR)))
w.qed([lhs, rhs], 'eqtr4d', '( %s -> %s = ( ( C x. %s ) + %s ) )' % (A0, RINT('F', 'A', 'B'), RINT('G', 'A', 'B'), RINT('H', 'A', 'B'))); run(w)
