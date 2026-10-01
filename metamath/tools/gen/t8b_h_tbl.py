"""T8b: the table-level forms (Lean ` lookupSlot_le_B ` , ` copyTbl_le_B ` ) and their word lemmas.

  tttblw    the slot word ( A |` ( 0 ..^ L ) ) of a table is a word of length L
  tttbles   encTblAsc / encTblDesc as encSlots of the slot word / its reverse
  tttbsb    TblBounded (TTAB's letters d q) gives the slot bounds of the slot word (letters o a)
  tmilksb   lookupSlot_le_B
  tmictbb   copyTbl_le_B

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_h_tbl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import linarith, nlinarith
from t7_e_cmp import machine

SEL = sys.argv[1:]
WL = '( A |` ( 0 ..^ L ) )'
IX = '( 0 ..^ L )'
PH0 = '( A e. Tbl /\\ L e. NN0 )'
ST = {
    'tttblw': '( %s -> ( %s e. %s /\\ ( # ` %s ) = L ) )' % (PH0, WL, WSLOT, WL),
    'tttbles': '( %s -> ( ( L encTblAsc A ) = %s /\\ ( L encTblDesc A ) = %s ) )' % (PH0, ES(WL), ES(REV(WL))),
    'tttbsb': '( ( %s /\\ %s ) -> A. o e. ran %s %s )' % (PH0, TBB('A'), WL, SB('o')),
}


def base(w, ph, at, lt):
    """A : NN0 --> SLOT, the restriction typing and length"""
    s = w.s
    af = s([at, w.inst('tblf')], 'syl', '( %s -> A : NN0 --> %s )' % (ph, SLOT))
    ss0 = s([s([], '0nn0', '0 e. NN0'), s([], 'fzossnn0', '( 0 e. NN0 -> %s C_ NN0 )' % IX)], 'ax-mp', '%s C_ NN0' % IX)
    ss = s([ss0], 'a1i', '( %s -> %s C_ NN0 )' % (ph, IX))
    gf = s([af, ss], 'fssresd', '( %s -> %s : %s --> %s )' % (ph, WL, IX, SLOT))
    return af, ss, gf


def tttblw():
    ph = PH0
    w = W('tttblw', 'The first ` L ` slots of a DP table form a word of length ` L ` .')
    s = w.s
    at, lt = s([], 'simpl', '( %s -> A e. Tbl )' % ph), s([], 'simpr', '( %s -> L e. NN0 )' % ph)
    af, ss, gf = base(w, ph, at, lt)
    ww = s([gf, w.inst('iswrdi')], 'syl', '( %s -> %s e. %s )' % (ph, WL, WSLOT))
    ln = s([lt, gf, w.inst('fnfzo0hash')], 'syl2anc', '( %s -> ( # ` %s ) = L )' % (ph, WL))
    w.qed([ww, ln], 'jca', ST['tttblw'])
    return w.run()


def tttbles():
    ph = PH0
    w = W('tttbles', 'The table on a stack as the word of its slot list: Lean\'s ` encTblAsc_eq ` , ` encTblDesc_eq ` '
                     '( ` encSlots ( ( List.range L ).map t ) ` and its reverse).')
    s = w.s
    at, lt = s([], 'simpl', '( %s -> A e. Tbl )' % ph), s([], 'simpr', '( %s -> L e. NN0 )' % ph)
    tw = s([s([at, lt], 'jca', '( %s -> %s )' % (ph, PH0)) if False else s([], 'id', '( %s -> %s )' % (ph, ph)), w.inst('tttblw')], 'syl',
           '( %s -> ( %s e. %s /\\ ( # ` %s ) = L ) )' % (ph, WL, WSLOT, WL))
    ww = s([tw], 'simpld', '( %s -> %s e. %s )' % (ph, WL, WSLOT))
    GS = lambda X: "( ( freeMnd ` Gamma' ) gsum ( encSlot o. %s ) )" % X
    av = s([lt, at, w.inst('ttabtbav')], 'syl2anc', '( %s -> ( L encTblAsc A ) = %s )' % (ph, GS(WL)))
    ev = s([ww, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES(WL), GS(WL)))
    a1 = s([av, ev], 'eqtr4d', '( %s -> ( L encTblAsc A ) = %s )' % (ph, ES(WL)))
    # the value of df-tm2enctbld
    R_, G_, S_ = GS('( reverse ` ( t |` ( 0 ..^ l ) ) )'), GS('( reverse ` ( t |` ( 0 ..^ L ) ) )'), GS(REV(WL))
    h1, n1 = w.congr(R_, {'l': 'L'}, 'l = L', {'l': s([], 'id', '( l = L -> l = L )')})
    assert n1 == G_, n1
    h2, n2 = w.congr(G_, {'t': 'A'}, 't = A', {'t': s([], 'id', '( t = A -> t = A )')})
    assert n2 == S_, n2
    df = s([], 'df-tm2enctbld', 'encTblDesc = ( l e. NN0 , t e. Tbl |-> %s )' % R_)
    ov = s([h1, h2, df], 'ovmpog', '( ( L e. NN0 /\\ A e. Tbl /\\ %s e. _V ) -> ( L encTblDesc A ) = %s )' % (S_, S_))
    sv = s([s([], 'ovex', '%s e. _V' % S_)], 'a1i', '( %s -> %s e. _V )' % (ph, S_))
    dv = s([lt, at, sv, ov], 'syl3anc', '( %s -> ( L encTblDesc A ) = %s )' % (ph, S_))
    rw = s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REV(WL), WSLOT))
    erv = s([rw, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES(REV(WL)), S_))
    a2 = s([dv, erv], 'eqtr4d', '( %s -> ( L encTblDesc A ) = %s )' % (ph, ES(REV(WL))))
    w.qed([a1, a2], 'jca', ST['tttbles'])
    return w.run()


def tttbsb():
    ph = '( %s /\\ %s )' % (PH0, TBB('A'))
    w = W('tttbsb', 'Every slot of the slot word of a table bounded in the sense of TTAB\'s inlined ` TblBounded ` '
                    '(Lean ` tblBounded_map_range ` ), with the bound letter ` q ` renamed ` a ` (~ cbvralvw ).')
    s = w.s
    pa = s([], 'simpl', '( %s -> %s )' % (ph, PH0))
    at, lt = s([pa], 'simpld', '( %s -> A e. Tbl )' % ph), s([pa], 'simprd', '( %s -> L e. NN0 )' % ph)
    tb = s([], 'simpr', '( %s -> %s )' % (ph, TBB('A')))
    # q -> a
    Ad = '( A ` d )'
    X = '( 2nd ` %s )' % Ad
    cq = s([], 'breq1', '( q = a -> ( q < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')
    cb = s([cq], 'cbvralvw', '( A. q e. ran %s q < ( 2 ^ B ) <-> A. a e. ran %s a < ( 2 ^ B ) )' % (X, X))
    an = s([cb], 'anbi2i', '( ( ( # ` %s ) <_ N /\\ A. q e. ran %s q < ( 2 ^ B ) ) <-> ( ( # ` %s ) <_ N /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (X, X, X, X))
    im = s([an], 'imbi2i', '( ( %s =/= ( inr ` (/) ) -> ( ( # ` %s ) <_ N /\\ A. q e. ran %s q < ( 2 ^ B ) ) ) <-> %s )' % (Ad, X, X, SB(Ad)))
    rb = s([im], 'ralbii', '( %s <-> A. d e. NN0 %s )' % (TBB('A'), SB(Ad)))
    t2 = s([tb, rb], 'sylib', '( %s -> A. d e. NN0 %s )' % (ph, SB(Ad)))
    af, ss, gf = base(w, ph, at, lt)
    t3 = s([ss, t2, w.inst('ssralv')], 'sylc', '( %s -> A. d e. %s %s )' % (ph, IX, SB(Ad)))
    fn = s([af, w.inst('ffn')], 'syl', '( %s -> A Fn NN0 )' % ph)
    ido = s([], 'id', '( o = %s -> o = %s )' % (Ad, Ad))
    cg, new = w.wcongr(SB('o'), {'o': Ad}, 'o = %s' % Ad, {'o': ido})
    assert new == SB(Ad), new
    ri = s([cg], 'ralima', '( ( A Fn NN0 /\\ %s C_ NN0 ) -> ( A. o e. ( A " %s ) %s <-> A. d e. %s %s ) )' % (IX, IX, SB('o'), IX, SB(Ad)))
    r4 = s([fn, ss, ri], 'syl2anc', '( %s -> ( A. o e. ( A " %s ) %s <-> A. d e. %s %s ) )' % (ph, IX, SB('o'), IX, SB(Ad)))
    t5 = s([t3, r4], 'mpbird', '( %s -> A. o e. ( A " %s ) %s )' % (ph, IX, SB('o')))
    di = s([], 'df-ima', '( A " %s ) = ran %s' % (IX, WL))
    rq = s([di], 'raleqi', '( A. o e. ( A " %s ) %s <-> A. o e. ran %s %s )' % (IX, SB('o'), WL, SB('o')))
    w.qed([t5, rq], 'sylib', ST['tttbsb'])
    return w.run()


def tbl_prep(w, ph, c, extra_tbb=True):
    """the slot word facts under ph from the table data"""
    s = w.s
    at, ln = c['A e. Tbl'], c['L e. NN0']
    ph0 = s([at, ln], 'jca', '( %s -> %s )' % (ph, PH0))
    tw = s([ph0, w.inst('tttblw')], 'syl', '( %s -> ( %s e. %s /\\ ( # ` %s ) = L ) )' % (ph, WL, WSLOT, WL))
    ww = s([tw], 'simpld', '( %s -> %s e. %s )' % (ph, WL, WSLOT))
    wl = s([tw], 'simprd', '( %s -> ( # ` %s ) = L )' % (ph, WL))
    te = s([ph0, w.inst('tttbles')], 'syl', '( %s -> ( ( L encTblAsc A ) = %s /\\ ( L encTblDesc A ) = %s ) )' % (ph, ES(WL), ES(REV(WL))))
    ea = s([te], 'simpld', '( %s -> ( L encTblAsc A ) = %s )' % (ph, ES(WL)))
    ed = s([te], 'simprd', '( %s -> ( L encTblDesc A ) = %s )' % (ph, ES(REV(WL))))
    sb = s([ph0, c[TBB('A')], w.inst('tttbsb')], 'sylancl' if False else 'syl2anc', '( %s -> A. o e. ran %s %s )' % (ph, WL, SB('o')))
    return dict(ww=ww, wl=wl, ea=ea, ed=ed, sb=sb, ln=ln, at=at)


def tmilksb():
    lab = 'tmilksb'
    ph = cj(TREE_LKSB)
    w = W(lab, 'Lean\'s ` lookupSlot_le_B ` at the machine: ~ tmilks on the slot word of a table ` A ` bounded by '
               '` TblBounded ` , the index below ` L ` of at most ` 2 b ` bits, within ` ( L + 1 ) ( N + 2 ) B b ` steps '
               '(~ ttablkb ).')
    c = Ctx(w, ph, TREE_LKSB)
    s = w.s
    t = tbl_prep(w, ph, c)
    dk = s([c['( D ` K ) = ( ( L encTblAsc A ) ++ X )'], s([t['ea']], 'oveq1d', '( %s -> ( ( L encTblAsc A ) ++ X ) = ( %s ++ X ) )' % (ph, ES(WL)))],
           'eqtrd', '( %s -> ( D ` K ) = ( %s ++ X ) )' % (ph, ES(WL)))
    jl = s([c['%s < L' % JN], t['wl']], 'breqtrrd', '( %s -> %s < ( # ` %s ) )' % (ph, JN, WL))
    cl = Closure(w, ph, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0'])})
    H2 = '( 2 x. B )'
    ex = {'%s e. %s' % (WL, WSLOT): t['ww'], '( D ` K ) = ( %s ++ X )' % ES(WL): dk, '%s < ( # ` %s )' % (JN, WL): jl,
          '%s e. NN0' % H2: cl.mem(H2, 'NN0'), 'A. o e. ran %s %s' % (WL, SB('o')): t['sb']}
    t1, cc = inst(w, ph, 'tmilks', {'L': WL, 'H': H2}, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    # ( WL ` jn ) = ( A ` jn )
    jnn = s([c['G e. Word 2o'], w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, JN))
    lz = s([t['ln']], 'nn0zd', '( %s -> L e. ZZ )' % ph)
    j3 = s([jnn, lz, c['%s < L' % JN]], '3jca', '( %s -> ( %s e. NN0 /\\ L e. ZZ /\\ %s < L ) )' % (ph, JN, JN))
    jo = s([j3, w.inst('elfzo0z')], 'sylibr', '( %s -> %s e. %s )' % (ph, JN, IX))
    fv = s([jo, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( A ` %s ) )' % (ph, WL, JN, JN))
    r, new = w.rewrite(D1, {'( %s ` %s )' % (WL, JN): ('( A ` %s )' % JN, fv)}, ph)
    assert new == CE(DFIN_LKSB), new
    t2, C2, D2, n2 = hrrw(w, ph, t1, C1, D1, n1, deq=r)
    # the bound
    lk = s([s([jnn, c['N e. NN0'], c['B e. NN0']], '3jca', '( %s -> ( %s e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) )' % (ph, JN)), w.inst('ttablkb')], 'syl',
           '( %s -> %s <_ ( ( ( %s + 1 ) x. ( N + 2 ) ) x. ( TMB ` B ) ) )' % (ph, n2, JN))
    cl.leaf(JN, 'NN0', jnn)
    tb = s([s([c['B e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
    cl.leaf('( TMB ` B )', 'NN0', tb)
    cl.leaf('L', 'NN0', t['ln'])
    jle = s([c['%s < L' % JN]], 'ltled' if False else 'id', '') if False else None
    j1 = linarith(w, ph, [c['%s < L' % JN]], '( %s + 1 ) <_ ( L + 1 )' % JN, closure=cl)
    m1 = s([cl.mem('( %s + 1 )' % JN, 'RR'), cl.mem('( L + 1 )', 'RR'), cl.mem('( N + 2 )', 'RR'), cl.ge0('( N + 2 )'), j1], 'lemul1ad',
           '( %s -> ( ( %s + 1 ) x. ( N + 2 ) ) <_ ( ( L + 1 ) x. ( N + 2 ) ) )' % (ph, JN))
    m2 = s([cl.mem('( ( %s + 1 ) x. ( N + 2 ) )' % JN, 'RR'), cl.mem('( ( L + 1 ) x. ( N + 2 ) )', 'RR'), cl.mem('( TMB ` B )', 'RR'),
            cl.ge0('( TMB ` B )'), m1], 'lemul1ad', '( %s -> ( ( ( %s + 1 ) x. ( N + 2 ) ) x. ( TMB ` B ) ) <_ %s )' % (ph, JN, BLB('L')))
    le = s([cl.mem(n2, 'RR'), cl.mem('( ( ( %s + 1 ) x. ( N + 2 ) ) x. ( TMB ` B ) )' % JN, 'RR'), cl.mem(BLB('L'), 'RR'), lk, m2], 'letrd',
           '( %s -> %s <_ %s )' % (ph, n2, BLB('L')))
    mk = machine(w, ph, c, K5)
    hrle(w, ph, mk['phm'], t2, C2, D2, n2, BLB('L'), cl.mem(BLB('L'), 'NN0'), le, qed=True)
    return w.run()


def tmictbb():
    lab = 'tmictbb'
    ph = cj(TREE_CTBB)
    w = W(lab, 'Lean\'s ` copyTbl_le_B ` at the machine: ~ tmictb on the slot word of a table ` A ` bounded by '
               '` TblBounded ` : ` dst ` gets the descending table ` encTblDesc L A ` , within ` ( L + 1 ) ( N + 2 ) B b ` '
               'steps (~ ttabcpb ).')
    c = Ctx(w, ph, TREE_CTBB)
    s = w.s
    t = tbl_prep(w, ph, c)
    Z0 = '( <" 0 "> ++ X )'
    dk = s([c['( D ` K ) = ( ( L encTblAsc A ) ++ %s )' % Z0], s([t['ea']], 'oveq1d', '( %s -> ( ( L encTblAsc A ) ++ %s ) = ( %s ++ %s ) )' % (ph, Z0, ES(WL), Z0))],
           'eqtrd', '( %s -> ( D ` K ) = ( %s ++ %s ) )' % (ph, ES(WL), Z0))
    ex = {'%s e. %s' % (WL, WSLOT): t['ww'], '( D ` K ) = ( %s ++ %s )' % (ES(WL), Z0): dk, 'A. o e. ran %s %s' % (WL, SB('o')): t['sb']}
    t1, cc = inst(w, ph, 'tmictb', {'L': WL}, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    edr = s([t['ed']], 'eqcomd', '( %s -> %s = ( L encTblDesc A ) )' % (ph, ES(REV(WL))))
    r, new = w.rewrite(D1, {ES(REV(WL)): ('( L encTblDesc A )', edr)}, ph)
    assert new == CE(DFIN_CTBB), new
    r2, n2t = w.rewrite(n1, {'( # ` %s )' % WL: ('L', t['wl'])}, ph)
    t2, C2, D2, n2 = hrrw(w, ph, t1, C1, D1, n1, deq=r, neq=r2)
    cb = s([s([t['ln'], c['N e. NN0'], c['B e. NN0']], '3jca', '( %s -> ( L e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) )' % ph), w.inst('ttabcpb')], 'syl',
           '( %s -> %s <_ %s )' % (ph, n2, BLB('L')))
    cl = Closure(w, ph, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0']), 'L': ('NN0', t['ln'])})
    tb = s([s([c['B e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
    cl.leaf('( TMB ` B )', 'NN0', tb)
    mk = machine(w, ph, c, K5)
    hrle(w, ph, mk['phm'], t2, C2, D2, n2, BLB('L'), cl.mem(BLB('L'), 'NN0'), cb, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
