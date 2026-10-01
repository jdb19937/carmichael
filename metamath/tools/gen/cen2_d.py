"""Sortie CEN2: series algebra (cen2sadd) and the summed positivity (cen2lim; Lean Census htsum, hpos, hre_eq,
Summable.tsum_finsetSum through bvswap)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from congr import mptval

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_sadd():
    w = W('cen2sadd', 'The sum of two convergent series converges to the sum of the values ( ~ climadd on the partial sums, ~ seradd ).')
    A0, C0 = split_imp(S['cen2sadd'])
    P1 = '( %s /\\ k e. NN )' % A0
    P2 = '( %s /\\ j e. ( 1 ... k ) )' % P1
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (P1, f))
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (P2, f))
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); h3 = s([], 'simp3', H3)
    ff = s([h1], 'simp1d', 'F : NN --> CC'); gf = s([h1], 'simp2d', 'G : NN --> CC')
    lf = s([h2], 'simpld', 'seq 1 ( + , F ) ~~> A'); lg = s([h2], 'simprd', 'seq 1 ( + , G ) ~~> B')
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = s([], '1zzd', '1 e. ZZ')
    kn = a([], 'simpr', 'k e. NN')
    def ser(fs, X):
        v = a([lift(w, fs, P1), kn], 'ffvelcdmd', '( %s ` k ) e. CC' % X)
        sf = s([nnuz, one, v], 'serf', 'seq 1 ( + , %s ) : NN --> CC' % X)
        return a([lift(w, sf, P1), kn], 'ffvelcdmd', '( seq 1 ( + , %s ) ` k ) e. CC' % X)
    sfk = ser(ff, 'F'); sgk = ser(gf, 'G')
    jn = b([b([], 'simpr', 'j e. ( 1 ... k )'), w.inst('elfznn')], 'syl', 'j e. NN')
    fj = b([lift(w, ff, P2), jn], 'ffvelcdmd', '( F ` j ) e. CC')
    gj = b([lift(w, gf, P2), jn], 'ffvelcdmd', '( G ` j ) e. CC')
    Q = lambda v: '( H ` %s ) = ( ( F ` %s ) + ( G ` %s ) )' % (v, v, v)
    e1 = w.s([], 'fveq2', '( a = j -> ( H ` a ) = ( H ` j ) )')
    e2 = w.s([w.s([], 'fveq2', '( a = j -> ( F ` a ) = ( F ` j ) )'), w.s([], 'fveq2', '( a = j -> ( G ` a ) = ( G ` j ) )')], 'oveq12d',
             '( a = j -> ( ( F ` a ) + ( G ` a ) ) = ( ( F ` j ) + ( G ` j ) ) )')
    e3 = w.s([e1, e2], 'eqeq12d', '( a = j -> ( %s <-> %s ) )' % (Q('a'), Q('j')))
    rs = w.s([e3], 'rspcv', '( j e. NN -> ( A. a e. NN %s -> %s ) )' % (Q('a'), Q('j')))
    hj = b([jn, lift(w, h3, P2), rs], 'sylc', Q('j'))
    kuz = a([kn, nnuz], 'eleqtrdi', 'k e. ( ZZ>= ` 1 )')
    sa = a([kuz, fj, gj, hj], 'seradd', '( seq 1 ( + , H ) ` k ) = ( ( seq 1 ( + , F ) ` k ) + ( seq 1 ( + , G ) ` k ) )')
    hx = s([w.s([], 'seqex', 'seq 1 ( + , H ) e. _V')], 'a1i', 'seq 1 ( + , H ) e. _V')
    w.qed([nnuz, one, lf, hx, lg, sfk, sgk, sa], 'climadd', S['cen2sadd'])
    return run(w)


def gen_lim():
    w = W('cen2lim', 'Positivity of the summed expansion: if ` 0 <_ A ( k ) + 2 sum_J B ( k ) + sum_J C ( k ) + sum_J sum_( J \\ { j } ) E ( k ) ` for every ` k ` and every series converges, the same combination of the sums is nonnegative (Lean Census ` htsum ` , ` hpos ` , ` hre_eq ` ; ` Summable.tsum_finsetSum ` is ~ bvswap ).')
    h = {}
    for i in range(1, 9):
        h[i] = w.s([], 'cen2lim.%d' % i, S['cen2lim.%d' % i], name='h%d' % i)
    s = lambda hh, r, f: w.s(hh, r, '( ph -> %s )' % f)
    def c(ctx):
        return lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (ctx, f))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = s([], '1zzd', '1 e. ZZ')
    PJ = '( ph /\\ j e. J )'
    PJL = '( ph /\\ ( j e. J /\\ l e. %s ) )' % JL
    pj = c(PJ)
    bf = pj([h[4]], 'simpld', 'B : NN --> RR'); cf = pj([h[4]], 'simprd', 'C : NN --> RR')

    def facts(ctx, v, phs, vs):
        """RR steps for the four bodies at the point v under ctx"""
        f = c(ctx)
        out = {}
        out['A'] = f([f([phs, h[3]], 'syl', 'A : NN --> RR'), vs], 'ffvelcdmd', '( A ` %s ) e. RR' % v)
        cj = '( %s /\\ j e. J )' % ctx
        g = c(cj)
        pjs = g([g([g([], 'simpl', ctx), phs], 'syl', 'ph'), g([], 'simpr', 'j e. J')], 'jca', PJ)
        vj = g([g([], 'simpl', ctx), vs], 'syl', '%s e. NN' % v)
        fin = f([phs, h[1]], 'syl', 'J e. Fin')
        for X, st in (('B', bf), ('C', cf)):
            xv = g([g([pjs, st], 'syl', '%s : NN --> RR' % X), vj], 'ffvelcdmd', '( %s ` %s ) e. RR' % (X, v))
            out[X] = f([fin, xv], 'fsumrecl', 'sum_ j e. J ( %s ` %s ) e. RR' % (X, v))
        cl_ = '( %s /\\ l e. %s )' % (cj, JL)
        q = c(cl_)
        pl = q([q([q([], 'simpll', ctx), phs], 'syl', 'ph'), q([q([], 'simplr', 'j e. J'), q([], 'simpr', 'l e. %s' % JL)], 'jca', '( j e. J /\\ l e. %s )' % JL)],
               'jca', PJL)
        ev = q([q([pl, h[5]], 'syl', 'E : NN --> RR'), q([q([], 'simpll', ctx), vs], 'syl', '%s e. NN' % v)], 'ffvelcdmd', '( E ` %s ) e. RR' % v)
        finl = g([g([g([], 'simpl', ctx), fin], 'syl', 'J e. Fin'), w.inst('diffi')], 'syl', '%s e. Fin' % JL)
        el = g([finl, ev], 'fsumrecl', 'sum_ l e. %s ( E ` %s ) e. RR' % (JL, v))
        out['E'] = f([fin, el], 'fsumrecl', 'sum_ j e. J sum_ l e. %s ( E ` %s ) e. RR' % (JL, v))
        out['El'] = el
        return out

    # ---- the four limits
    PK = '( ph /\\ k e. NN )'
    pk = c(PK)
    fk = facts(PK, 'k', pk([], 'simpl', 'ph'), pk([], 'simpr', 'k e. NN'))
    VA = 'sum_ k e. NN ( A ` k )'
    la = w.s([nnuz, one, pk([], 'eqidd', '( A ` k ) = ( A ` k )'), pk([fk['A']], 'recnd', '( A ` k ) e. CC'), h[6]], 'isumclim2', '( ph -> seq 1 ( + , A ) ~~> %s )' % VA)
    PJK = '( ph /\\ ( j e. J /\\ k e. NN ) )'
    pjk = c(PJK)
    def lim1(X, st, cvsel):
        xk = pjk([pjk([pjk([pjk([], 'simpl', 'ph'), pjk([], 'simprl', 'j e. J')], 'jca', PJ), st], 'syl', '%s : NN --> RR' % X), pjk([], 'simprr', 'k e. NN')],
                 'ffvelcdmd', '( %s ` k ) e. RR' % X)
        MT = '( t e. NN |-> ( %s ` t ) )' % X
        fe = pj([st], 'feqmptd', '%s = %s' % (X, MT))
        cvx = pj([h[7]], cvsel, 'seq 1 ( + , %s ) e. dom ~~>' % X)
        cvt = pj([pj([fe], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (X, MT)), cvx], 'eqeltrd', 'seq 1 ( + , %s ) e. dom ~~>' % MT) if False else \
            pj([pj([pj([fe], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (X, MT))], 'eqcomd', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (MT, X)), cvx], 'eqeltrd',
               'seq 1 ( + , %s ) e. dom ~~>' % MT)
        e4 = w.s([], 'fveq2', '( k = t -> ( %s ` k ) = ( %s ` t ) )' % (X, X))
        return w.s([h[1], pjk([xk], 'recnd', '( %s ` k ) e. CC' % X), cvt, e4], 'bvswap',
                   '( ph -> seq 1 ( + , ( t e. NN |-> sum_ j e. J ( %s ` t ) ) ) ~~> sum_ j e. J sum_ k e. NN ( %s ` k ) )' % (X, X))
    lb = lim1('B', bf, 'simpld'); lc = lim1('C', cf, 'simprd')
    # E: inner over l, then outer over j
    PJLK = '( %s /\\ ( l e. %s /\\ k e. NN ) )' % (PJ, JL)
    q = c(PJLK)
    pjl2 = q([q([q([], 'simpll', 'ph'), q([q([], 'simplr', 'j e. J'), q([], 'simprl', 'l e. %s' % JL)], 'jca', '( j e. J /\\ l e. %s )' % JL)], 'jca', PJL), h[5]],
             'syl', 'E : NN --> RR')
    ek = q([pjl2, q([], 'simprr', 'k e. NN')], 'ffvelcdmd', '( E ` k ) e. RR')
    PJ_L = '( %s /\\ l e. %s )' % (PJ, JL)
    r = c(PJ_L)
    pjl = r([r([r([], 'simpll', 'ph'), r([r([], 'simplr', 'j e. J'), r([], 'simpr', 'l e. %s' % JL)], 'jca', '( j e. J /\\ l e. %s )' % JL)], 'jca', PJL), h[5]],
            'syl', 'E : NN --> RR')
    ME = '( t e. NN |-> ( E ` t ) )'
    fe = r([pjl], 'feqmptd', 'E = %s' % ME)
    cve = r([r([], 'simpll', 'ph'), r([r([], 'simplr', 'j e. J'), r([], 'simpr', 'l e. %s' % JL)], 'jca', '( j e. J /\\ l e. %s )' % JL)], 'jca', PJL)
    cve = r([cve, h[8]], 'syl', 'seq 1 ( + , E ) e. dom ~~>')
    cvet = r([r([r([fe], 'seqeq3d', 'seq 1 ( + , E ) = seq 1 ( + , %s )' % ME)], 'eqcomd', 'seq 1 ( + , %s ) = seq 1 ( + , E )' % ME), cve], 'eqeltrd',
             'seq 1 ( + , %s ) e. dom ~~>' % ME)
    finl = pj([pj([pj([], 'simpl', 'ph'), h[1]], 'syl', 'J e. Fin'), w.inst('diffi')], 'syl', '%s e. Fin' % JL)
    SL = 'sum_ l e. %s ( E ` t )' % JL; SLk = 'sum_ l e. %s ( E ` k )' % JL
    MSL = '( t e. NN |-> %s )' % SL
    li = w.s([finl, q([ek], 'recnd', '( E ` k ) e. CC'), cvet, w.s([], 'fveq2', '( k = t -> ( E ` k ) = ( E ` t ) )')], 'bvswap',
             '( %s -> seq 1 ( + , %s ) ~~> sum_ l e. %s sum_ k e. NN ( E ` k ) )' % (PJ, MSL, JL))
    ldom = pj([pj([], 'climrel', 'Rel ~~>') if False else pj([w.s([], 'climrel', 'Rel ~~>')], 'a1i', 'Rel ~~>'), li], 'releldmd', 'seq 1 ( + , %s ) e. dom ~~>' % MSL) if False else None
    ldom = pj([pj([w.s([], 'climrel', 'Rel ~~>')], 'a1i', 'Rel ~~>'), li, w.inst('releldm')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % MSL)
    PJK2 = '( %s /\\ k e. NN )' % PJ
    u = c(PJK2)
    ukk = u([u([], 'simpl', PJ), u([], 'simpr', 'k e. NN')], 'jca', '( %s /\\ k e. NN )' % PJ) if False else None
    # ( ( ph /\ j e. J ) /\ k e. NN ) -> sum_l ( E ` k ) e. CC
    U2 = '( %s /\\ l e. %s )' % (PJK2, JL)
    u2 = c(U2)
    e2 = u2([u2([u2([u2([], 'simplll', 'ph'), u2([u2([], 'simpllr', 'j e. J'), u2([], 'simpr', 'l e. %s' % JL)], 'jca', '( j e. J /\\ l e. %s )' % JL)], 'jca', PJL), h[5]], 'syl', 'E : NN --> RR'),
             u2([], 'simplr', 'k e. NN')], 'ffvelcdmd', '( E ` k ) e. RR')
    slk = u([u([u([], 'simpl', PJ), finl], 'syl', '%s e. Fin' % JL), u2([e2], 'recnd', '( E ` k ) e. CC')], 'fsumcl', '%s e. CC' % SLk)
    fvl, vl = mptval(w, PJK2, 't', 'NN', SL, 'k', u([], 'simpr', 'k e. NN'), exs=u([slk], 'elexd', '%s e. _V' % SLk), gen=w.g)
    assert vl == SLk
    swp = w.s([nnuz, pj([], '1zzd', '1 e. ZZ'), fvl, slk, li], 'isumclim', '( %s -> sum_ k e. NN %s = sum_ l e. %s sum_ k e. NN ( E ` k ) )' % (PJ, SLk, JL))
    # outer
    PJK = '( ph /\\ ( j e. J /\\ k e. NN ) )'
    v_ = c(PJK)
    V2 = '( %s /\\ l e. %s )' % (PJK, JL)
    v2 = c(V2)
    e3 = v2([v2([v2([v2([], 'simpll', 'ph'), v2([v2([], 'simplrl', 'j e. J'), v2([], 'simpr', 'l e. %s' % JL)], 'jca', '( j e. J /\\ l e. %s )' % JL)], 'jca', PJL), h[5]], 'syl', 'E : NN --> RR'),
             v2([], 'simplrr', 'k e. NN')], 'ffvelcdmd', '( E ` k ) e. RR')
    finl2 = v_([v_([v_([v_([], 'simpl', 'ph'), h[1]], 'syl', 'J e. Fin'), w.inst('diffi')], 'syl', '%s e. Fin' % JL)], 'id', 'x') if False else \
        v_([v_([v_([], 'simpl', 'ph'), h[1]], 'syl', 'J e. Fin'), w.inst('diffi')], 'syl', '%s e. Fin' % JL)
    slk2 = v_([finl2, v2([e3], 'recnd', '( E ` k ) e. CC')], 'fsumcl', '%s e. CC' % SLk)
    e4 = w.s([w.s([w.s([], 'fveq2', '( k = t -> ( E ` k ) = ( E ` t ) )')], 'adantr', '( ( k = t /\\ l e. %s ) -> ( E ` k ) = ( E ` t ) )' % JL)], 'sumeq2dv',
             '( k = t -> %s = %s )' % (SLk, SL))
    SE = '( t e. NN |-> sum_ j e. J %s )' % SL
    lo = w.s([h[1], slk2, ldom, e4], 'bvswap', '( ph -> seq 1 ( + , %s ) ~~> sum_ j e. J sum_ k e. NN %s )' % (SE, SLk))
    VE = 'sum_ j e. J sum_ l e. %s sum_ k e. NN ( E ` k )' % JL
    le_ = s([lo, s([swp], 'sumeq2dv', 'sum_ j e. J sum_ k e. NN %s = %s' % (SLk, VE))], 'breqtrd', 'seq 1 ( + , %s ) ~~> %s' % (SE, VE))
    # ---- combine with cen2sadd
    PT = '( ph /\\ t e. NN )'
    ft = facts(PT, 't', c(PT)([], 'simpl', 'ph'), c(PT)([], 'simpr', 't e. NN'))
    PA = '( ph /\\ a e. NN )'
    fa = facts(PA, 'a', c(PA)([], 'simpl', 'ph'), c(PA)([], 'simpr', 'a e. NN'))
    def fmap(body, rr):
        M = '( t e. NN |-> %s )' % body
        return s([c(PT)([rr], 'recnd', '%s e. CC' % body), w.s([], 'eqid', '%s = %s' % (M, M))], 'fmptd', '%s : NN --> CC' % M)
    def val(body, rra):
        from cen2lib import tokrep
        ba = tokrep(body, {'t': 'a'})
        st, v = mptval(w, PA, 't', 'NN', body, 'a', c(PA)([], 'simpr', 'a e. NN'), exs=c(PA)([rra], 'elexd', '%s e. _V' % ba), gen=w.g)
        assert v == ba, (v, ba)
        return st, ba
    SBt = 'sum_ j e. J ( B ` t )'; SCt = 'sum_ j e. J ( C ` t )'; SEt = 'sum_ j e. J %s' % SL
    VB = 'sum_ j e. J sum_ k e. NN ( B ` k )'; VC = 'sum_ j e. J sum_ k e. NN ( C ` k )'
    MB = '( t e. NN |-> %s )' % SBt; MC = '( t e. NN |-> %s )' % SCt
    B2 = '( 2 x. %s )' % SBt
    X1 = '( ( A ` t ) + %s )' % B2
    X2 = '( %s + %s )' % (X1, SCt)
    X3 = '( %s + %s )' % (X2, SEt)
    assert X3 == TOT('t'), (X3, TOT('t'))
    pt = c(PT); pa = c(PA)
    rr = {}
    rr[SBt] = ft['B']; rr[SCt] = ft['C']; rr[SEt] = ft['E']
    rr[B2] = pt([pt([], '2re', '2 e. RR') if False else pt([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), ft['B']], 'remulcld', '%s e. RR' % B2)
    rr[X1] = pt([ft['A'], rr[B2]], 'readdcld', '%s e. RR' % X1)
    rr[X2] = pt([rr[X1], ft['C']], 'readdcld', '%s e. RR' % X2)
    rr[X3] = pt([rr[X2], ft['E']], 'readdcld', '%s e. RR' % X3)
    ra = {}
    from cen2lib import tokrep
    T2A = lambda x: tokrep(x, {'t': 'a'})
    ra[SBt] = fa['B']; ra[SCt] = fa['C']; ra[SEt] = fa['E']
    ra[B2] = pa([pa([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), fa['B']], 'remulcld', '%s e. RR' % T2A(B2))
    ra[X1] = pa([fa['A'], ra[B2]], 'readdcld', '%s e. RR' % T2A(X1))
    ra[X2] = pa([ra[X1], fa['C']], 'readdcld', '%s e. RR' % T2A(X2))
    ra[X3] = pa([ra[X2], fa['E']], 'readdcld', '%s e. RR' % T2A(X3))
    def sadd(Fm, Ff, Fl, Fv, Gm, Gf, Gl, Gv, Hbody, pw):
        """cen2sadd for F G mappings/functions with limits Fv Gv; pw(a-step list) proves ( PA -> ( H ` a ) = ( ( F ` a ) + ( G ` a ) ) )"""
        Hm = '( t e. NN |-> %s )' % Hbody
        hf = fmap(Hbody, rr[Hbody])
        ral = s([pw], 'ralrimiva', 'A. a e. NN ( %s ` a ) = ( ( %s ` a ) + ( %s ` a ) )' % (Hm, Fm, Gm))
        ant = s([s([Ff, Gf, hf], '3jca', '( %s : NN --> CC /\\ %s : NN --> CC /\\ %s : NN --> CC )' % (Fm, Gm, Hm)), s([Fl, Gl], 'jca', '( seq 1 ( + , %s ) ~~> %s /\\ seq 1 ( + , %s ) ~~> %s )' % (Fm, Fv, Gm, Gv)), ral],
                '3jca', split_imp(tokrep(S['cen2sadd'], {'F': Fm, 'G': Gm, 'H': Hm, 'A': Fv, 'B': Gv}))[0])
        return s([ant, w.inst('cen2sadd')], 'syl', 'seq 1 ( + , %s ) ~~> ( %s + %s )' % (Hm, Fv, Gv)), Hm, hf
    # 2 x. SB = SB + SB
    mbf = fmap(SBt, ft['B'])
    vb, vba = val(SBt, fa['B'])
    v2, v2a = val(B2, ra[B2])
    p2 = pa([v2, pa([pa([fa['B']], 'recnd', '%s e. CC' % vba)], '2timesd', '( 2 x. %s ) = ( %s + %s )' % (vba, vba, vba))], 'eqtrd', '( ( t e. NN |-> %s ) ` a ) = ( %s + %s )' % (B2, vba, vba))
    p2 = pa([p2, pa([vb, vb], 'oveq12d', '( ( %s ` a ) + ( %s ` a ) ) = ( %s + %s )' % (MB, MB, vba, vba))], 'eqtr4d', '( ( t e. NN |-> %s ) ` a ) = ( ( %s ` a ) + ( %s ` a ) )' % (B2, MB, MB))
    l2, M2, m2f = sadd(MB, mbf, lb, VB, MB, mbf, lb, VB, B2, p2)
    # value of the limit: VB + VB = 2 x. VB needs VB e. CC
    vbc = s([lb, w.inst('climcl')], 'syl', '%s e. CC' % VB)
    l2c = s([l2, s([vbc], '2timesd', '( 2 x. %s ) = ( %s + %s )' % (VB, VB, VB))], 'breqtrrd', 'seq 1 ( + , %s ) ~~> ( 2 x. %s )' % (M2, VB))
    # X1 = A + M2
    af = s([h[3], s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', 'RR C_ CC')], 'fssd', 'A : NN --> CC')
    x1v, x1a = val(X1, ra[X1])
    x1p = pa([x1v, pa([pa([], 'eqidd', '( A ` a ) = ( A ` a )'), v2], 'oveq12d', '( ( A ` a ) + ( %s ` a ) ) = %s' % (M2, x1a))], 'eqtr4d',
             '( ( t e. NN |-> %s ) ` a ) = ( ( A ` a ) + ( %s ` a ) )' % (X1, M2))
    VX1 = '( %s + ( 2 x. %s ) )' % (VA, VB)
    l3, M3, m3f = sadd('A', af, la, VA, M2, m2f, l2c, '( 2 x. %s )' % VB, X1, x1p)
    # X2 = X1 + SC
    mcf = fmap(SCt, ft['C'])
    vc, vca = val(SCt, fa['C'])
    x2v, x2a = val(X2, ra[X2])
    x2p = pa([x2v, pa([x1v, vc], 'oveq12d', '( ( %s ` a ) + ( %s ` a ) ) = %s' % (M3, MC, x2a))], 'eqtr4d', '( ( t e. NN |-> %s ) ` a ) = ( ( %s ` a ) + ( %s ` a ) )' % (X2, M3, MC))
    l4, M4, m4f = sadd(M3, m3f, l3, VX1, MC, mcf, lc, VC, X2, x2p)
    VX2 = '( %s + %s )' % (VX1, VC)
    # X3 = X2 + SE
    mef = fmap(SEt, ft['E'])
    ve, vea = val(SEt, fa['E'])
    x3v, x3a = val(X3, ra[X3])
    x3p = pa([x3v, pa([x2v, ve], 'oveq12d', '( ( %s ` a ) + ( %s ` a ) ) = %s' % (M4, SE, x3a))], 'eqtr4d', '( ( t e. NN |-> %s ) ` a ) = ( ( %s ` a ) + ( %s ` a ) )' % (X3, M4, SE))
    l5, M5, m5f = sadd(M4, m4f, l4, VX2, SE, mef, le_, VE, X3, x3p)
    # iserge0 at the letter x
    PX = '( ph /\\ x e. NN )'
    fx = facts(PX, 'x', c(PX)([], 'simpl', 'ph'), c(PX)([], 'simpr', 'x e. NN'))
    X3x = tokrep(X3, {'t': 'x'})
    px = c(PX)
    xr = px([px([px([fx['A'], px([px([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), fx['B']], 'remulcld', '%s e. RR' % tokrep(B2, {'t': 'x'}))], 'readdcld', '%s e. RR' % tokrep(X1, {'t': 'x'})), fx['C']],
                 'readdcld', '%s e. RR' % tokrep(X2, {'t': 'x'})), fx['E']], 'readdcld', '%s e. RR' % X3x)
    xv, _ = mptval(w, PX, 't', 'NN', X3, 'x', px([], 'simpr', 'x e. NN'), exs=px([xr], 'elexd', '%s e. _V' % X3x), gen=w.g)
    ral0 = s([h[2]], 'ralrimiva', 'A. k e. NN 0 <_ %s' % TOT('k'))
    eqkx, _ = ren(w, TOT('k'), 'k', 'x')
    bk = w.s([eqkx], 'breq2d', '( k = x -> ( 0 <_ %s <-> 0 <_ %s ) )' % (TOT('k'), X3x))
    rsx = w.s([bk], 'rspcv', '( x e. NN -> ( A. k e. NN 0 <_ %s -> 0 <_ %s ) )' % (TOT('k'), X3x))
    g0 = px([px([], 'simpr', 'x e. NN'), px([px([], 'simpl', 'ph'), ral0], 'syl', 'A. k e. NN 0 <_ %s' % TOT('k')), rsx], 'sylc', '0 <_ %s' % X3x)
    M5x = '( %s ` x )' % M5
    w.qed([nnuz, one, l5, px([xv, xr], 'eqeltrd', '%s e. RR' % M5x), px([g0, xv], 'breqtrrd', '0 <_ %s' % M5x)], 'iserge0', S['cen2lim'])
    return run(w)


if __name__ == '__main__':
    gen_sadd()
    gen_lim()
