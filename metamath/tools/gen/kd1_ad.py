"""Sortie KD1: the Turan event over the 6 eta family (kdturan)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_turan():
    w = W('kdturan', 'Lean ` KDerivDetect.exists_turan_index ` (with ` turan_family_power_sum ` ): given a zero within ` E ` of ` 1 + i T ` and mass ` <_ J ` of the ` 6 E ` family, some ` k e. ( M + 1 ) ... ( M + J ) ` has ` ( J / ( 8 e ( M + J ) ) ) ^ J ( 1 / ( 2 E ) ) ^ k <_ abs sum m / ( s0 - q ) ^ k ` (TP ` tpmaxg ` on the flattened index set ` U_ a e. Z6 ( { a } X. ( 0 ..^ m ( a ) ) ) ` ).')
    A0 = S['kdturan'].split(' -> E. l e.')[0][2:]
    GOAL = S['kdturan'].split(' -> ', 1)[1][:-2]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t0, t1 = top_and(A0)
    g0 = s([], 'simpl', t0); g1 = s([], 'simpr', t1)
    chi = s([g0], 'simpld', CHI); tee = s([g0], 'simprd', '( T e. RR /\\ E e. RR+ /\\ E <_ ( 1 / 2 ) )')
    tr = s([tee], 'simp1d', 'T e. RR'); ep = s([tee], 'simp2d', 'E e. RR+'); e12 = s([tee], 'simp3d', 'E <_ ( 1 / 2 )')
    er = s([ep], 'rpred', 'E e. RR')
    u = top_and(t1)
    jm = s([g1], 'simp1d', u[0]); hz = s([g1], 'simp2d', u[1]); mm = s([g1], 'simp3d', 'M e. NN0')
    jn = s([jm], 'simpld', 'J e. NN'); hm = s([jm], 'simprd', top_and(u[0])[1])
    SS = S0(); O1 = ONE('T')
    Z6 = '{ p e. %s | ( abs ` ( p - %s ) ) <_ ( 6 x. E ) }' % (ZD(), O1)
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0]); zord = s([lz], 'simp2d', top_and(lzc)[1])
    z6s = w.s([w.s([], 'ssrab2', '%s C_ %s' % (Z6, ZD()))], 'a1i', '( %s -> %s C_ %s )' % (A0, Z6, ZD()))
    z6f = s([zfin, z6s], 'ssfid', '%s e. Fin' % Z6)
    c = Closure(w, A0, {'E': ('RR', er), 'T': ('RR', tr)})
    oe = c.mem('( 1 + E )', 'RR')
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
    s0c = s([s([oe], 'recnd', '( 1 + E ) e. CC'), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SS)
    rs0 = s([oe, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + E )' % SS)
    Ma = lambda a: MU(a)
    # per a in Z6: a in CC, S0 - a =/= 0, m(a) in NN
    def afacts(ante, azst, a_='a'):
        b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        L = lambda st: lift(w, st, ante)
        azd = b([L(z6s), azst], 'sseldd', '%s e. %s' % (a_, ZD()))
        cmp = w.s([w.s([], 'oveq2', '( q = %s -> %s = %s )' % (a_, MU('q'), Ma(a_)))], 'eleq1d', '( q = %s -> ( %s e. NN <-> %s e. NN ) )' % (a_, MU('q'), Ma(a_)))
        mn = b([azd, L(zord), w.s([cmp], 'rspcv', '( %s e. %s -> ( %s -> %s e. NN ) )' % (a_, ZD(), top_and(lzc)[1], Ma(a_)))], 'sylc', '%s e. NN' % Ma(a_))
        rq = b([L(chi), L(tr), azd, w.s([], 'kdre1', '( ( %s /\\ T e. RR /\\ %s e. %s ) -> ( Re ` %s ) <_ 1 )' % (CHI, a_, ZD(), a_))], 'syl3anc', '( Re ` %s ) <_ 1' % a_)
        SQ13 = SQ(CT('T'), R138)
        RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
        cq = Closure(w, ante, {'T': ('RR', L(tr)), 'E': ('RR', L(er))})
        cct = b([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % ante), b([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante), b([L(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
                'addcld', '%s e. CC' % CT('T'))
        ric = b([b([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), b([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante), b([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
                'addcld', '%s e. CC' % RI_)
        sqcc = b([b([b([cct, ric], 'subcld', '%s e. CC' % A13), b([cct, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
        ac = b([sqcc, b([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (ante, ZD(), SQ13)), azd], 'sseldd', '%s e. %s' % (a_, SQ13))], 'sseldd', '%s e. CC' % a_)
        D_ = '( %s - %s )' % (SS, a_)
        dc = b([L(s0c), ac], 'subcld', '%s e. CC' % D_)
        rd = b([L(s0c), ac], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (D_, SS, a_))
        cq.leaf('( Re ` %s )' % a_, 'RR', b([ac], 'recld', '( Re ` %s ) e. RR' % a_)); cq.atom('( Re ` %s )' % a_)
        cq.leaf('( Re ` %s )' % SS, 'RR', b([L(s0c)], 'recld', '( Re ` %s ) e. RR' % SS)); cq.atom('( Re ` %s )' % SS)
        cq.leaf('( Re ` %s )' % D_, 'RR', b([dc], 'recld', '( Re ` %s ) e. RR' % D_)); cq.atom('( Re ` %s )' % D_)
        rpos = linarith(w, ante, [rd, L(rs0), rq, L(s([ep], 'rpgt0d', '0 < E'))], '0 < ( Re ` %s )' % D_, closure=cq)
        rne0 = b([b([rpos], 'gt0ne0d', '( Re ` %s ) =/= 0' % D_), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % ante)], 'neeqtrrd', '( Re ` %s ) =/= ( Re ` 0 )' % D_)
        dn = b([rne0, w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (D_, D_))], 'necon3i', '( ( Re ` %s ) =/= ( Re ` 0 ) -> %s =/= 0 )' % (D_, D_))], 'syl', '%s =/= 0' % D_)
        return dict(azd=azd, mn=mn, ac=ac, dc=dc, dn=dn, D=D_)
    BI = lambda a_: '( 0 ..^ %s )' % Ma(a_)
    I_ = 'U_ a e. %s ( { a } X. %s )' % (Z6, BI('a'))
    Aa = '( %s /\\ a e. %s )' % (A0, Z6)
    fa = afacts(Aa, w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, Z6)))
    # I finite
    bif = w.s([w.s([w.s([], 'snfi', '{ a } e. Fin'), w.s([], 'fzofi', '%s e. Fin' % BI('a'))], 'xpfi' if False else 'pm3.2i', '( { a } e. Fin /\\ %s e. Fin )' % BI('a')) and
               w.s([w.s([w.s([], 'snfi', '{ a } e. Fin'), w.s([], 'fzofi', '%s e. Fin' % BI('a'))], 'pm3.2i', '( { a } e. Fin /\\ %s e. Fin )' % BI('a')), w.inst('xpfi')], 'ax-mp', '( { a } X. %s ) e. Fin' % BI('a'))],
              'a1i', '( %s -> ( { a } X. %s ) e. Fin )' % (Aa, BI('a')))
    iF = s([z6f, s([bif], 'ralrimiva', 'A. a e. %s ( { a } X. %s ) e. Fin' % (Z6, BI('a'))), w.inst('iunfi')], 'syl2anc', '%s e. Fin' % I_)
    # # I = sum m
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)
    Aab = '( %s /\\ ( a e. %s /\\ b e. %s ) )' % (A0, Z6, BI('a'))
    f2 = w.s([w.s([], 'eqidd', '( c = <. a , b >. -> 1 = 1 )'), z6f, w.s([w.s([], 'fzofi', '%s e. Fin' % BI('a'))], 'a1i', '( %s -> %s e. Fin )' % (Aa, BI('a'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % Aab)],
             'fsum2d', '( %s -> sum_ a e. %s sum_ b e. %s 1 = sum_ c e. %s 1 )' % (A0, Z6, BI('a'), I_))
    cI = s([iF, one, w.inst('fsumconst')], 'syl2anc', 'sum_ c e. %s 1 = ( ( # ` %s ) x. 1 )' % (I_, I_))
    hI = s([s([iF, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % I_)], 'nn0cnd', '( # ` %s ) e. CC' % I_)
    cI2 = s([cI, s([hI], 'mulridd', '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (I_, I_))], 'eqtrd', 'sum_ c e. %s 1 = ( # ` %s )' % (I_, I_))
    ib = w.s([w.s([w.s([w.s([], 'fzofi', '%s e. Fin' % BI('a'))], 'a1i', '( %s -> %s e. Fin )' % (Aa, BI('a'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % Aa), w.inst('fsumconst')], 'syl2anc',
                   '( %s -> sum_ b e. %s 1 = ( ( # ` %s ) x. 1 ) )' % (Aa, BI('a'), BI('a'))),
              w.s([w.s([w.s([fa['mn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (Aa, Ma('a'))), w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (Aa, BI('a'), Ma('a')))], 'oveq1d',
                  '( %s -> ( ( # ` %s ) x. 1 ) = ( %s x. 1 ) )' % (Aa, BI('a'), Ma('a'))),
              w.s([w.s([fa['mn']], 'nncnd', '( %s -> %s e. CC )' % (Aa, Ma('a')))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (Aa, Ma('a'), Ma('a')))],
             '3eqtrd', '( %s -> sum_ b e. %s 1 = %s )' % (Aa, BI('a'), Ma('a')))
    sb = s([ib], 'sumeq2dv', 'sum_ a e. %s sum_ b e. %s 1 = sum_ a e. %s %s' % (Z6, BI('a'), Z6, Ma('a')))
    hsum = s([cI2, f2, sb], '3eqtr3rd' if False else 'T.', 'T.') if False else None
    hsum = s([s([f2, cI2], 'eqtrd', 'sum_ a e. %s sum_ b e. %s 1 = ( # ` %s )' % (Z6, BI('a'), I_)), sb], 'eqtr3d', '( # ` %s ) = sum_ a e. %s %s' % (I_, Z6, Ma('a')))
    idaq = w.s([], 'id', '( a = q -> a = q )')
    caq, naq = w.congr(Ma('a'), {'a': 'q'}, 'a = q', {'a': idaq})
    cbq = w.s([caq], 'cbvsumv', 'sum_ a e. %s %s = sum_ q e. %s %s' % (Z6, Ma('a'), Z6, MU()))
    hI2 = s([hsum, w.s([cbq], 'a1i', '( %s -> sum_ a e. %s %s = sum_ q e. %s %s )' % (A0, Z6, Ma('a'), Z6, MU()))], 'eqtrd', '( # ` %s ) = sum_ q e. %s %s' % (I_, Z6, MU()))
    hJ = s([hI2, hm], 'eqbrtrd', '( # ` %s ) <_ J' % I_)
    # I C_ ( Z6 X. NN0 ) and the first coordinate
    xs = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, Z6))], 'snssd', '( %s -> { a } C_ %s )' % (Aa, Z6)),
                   w.s([w.s([w.s([], '0nn0', '0 e. NN0'), w.inst('fzossnn0')], 'ax-mp', '%s C_ NN0' % BI('a'))], 'a1i', '( %s -> %s C_ NN0 )' % (Aa, BI('a')))], 'jca',
                  '( %s -> ( { a } C_ %s /\\ %s C_ NN0 ) )' % (Aa, Z6, BI('a'))), w.inst('xpss12')], 'syl', '( %s -> ( { a } X. %s ) C_ ( %s X. NN0 ) )' % (Aa, BI('a'), Z6))
    iss = s([s([xs], 'ralrimiva', 'A. a e. %s ( { a } X. %s ) C_ ( %s X. NN0 )' % (Z6, BI('a'), Z6)), w.s([], 'iunss', '( %s C_ ( %s X. NN0 ) <-> A. a e. %s ( { a } X. %s ) C_ ( %s X. NN0 ) )' % (I_, Z6, Z6, BI('a'), Z6))],
            'sylibr', '%s C_ ( %s X. NN0 )' % (I_, Z6))
    def first(ante, jin, j_):
        b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        return b([b([lift(w, iss, ante), jin], 'sseldd', '%s e. ( %s X. NN0 )' % (j_, Z6)), w.inst('xp1st')], 'syl', '( 1st ` %s ) e. %s' % (j_, Z6))
    ZF_ = '( c e. %s |-> ( 1 / ( %s - ( 1st ` c ) ) ) )' % (I_, SS)
    Ac = '( %s /\\ c e. %s )' % (A0, I_)
    f1c = first(Ac, w.s([], 'simpr', '( %s -> c e. %s )' % (Ac, I_)), 'c')
    fc = afacts(Ac, f1c, '( 1st ` c )')
    zfv = w.s([fc['dc'], fc['dn']], 'reccld', '( %s -> ( 1 / %s ) e. CC )' % (Ac, fc['D']))
    zff = s([zfv], 'fmptd', '%s : %s --> CC' % (ZF_, I_))
    # the given zero p and the nearest zero d
    HZ = u[1]
    PB = tsub(HZ[len('E. p e. CC '):], {'p': 'o'})
    HZo = 'E. o e. CC %s' % PB
    cpo = w.s([w.s([w.s([], 'fveqeq2', '( p = o -> ( ( %s ` p ) = 0 <-> ( %s ` o ) = 0 ) )' % (LFN, LFN)), w.s([w.s([w.s([], 'oveq1', '( p = o -> ( p - %s ) = ( o - %s ) )' % (O1, O1))], 'fveq2d', '( p = o -> ( abs ` ( p - %s ) ) = ( abs ` ( o - %s ) ) )' % (O1, O1))], 'breq1d', '( p = o -> ( ( abs ` ( p - %s ) ) <_ E <-> ( abs ` ( o - %s ) ) <_ E ) )' % (O1, O1))], 'anbi12d', '( p = o -> ( %s <-> %s ) )' % (HZ[len('E. p e. CC '):], PB))], 'cbvrexvw', '( %s <-> %s )' % (HZ, HZo))
    hzo = s([hz, cpo], 'sylib', HZo)
    C1 = '( %s /\\ ( o e. CC /\\ %s ) )' % (A0, PB)
    b1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C1, f))
    L1 = lambda st: lift(w, st, C1)
    pc = b1([], 'simprl', 'o e. CC'); pb = b1([], 'simprr', PB)
    pl0 = b1([pb], 'simpld', '( %s ` o ) = 0' % LFN); pd = b1([pb], 'simprd', '( abs ` ( o - %s ) ) <_ E' % O1)
    MZ = tsub(S['kdmemzd'], {'Q': 'o', 'W': 'E'})
    mza, mzc = split_imp(MZ)
    pzd = b1([b1([L1(chi), L1(tr)], 'jca', '( %s /\\ T e. RR )' % CHI), b1([pc, pl0], 'jca', '( o e. CC /\\ ( %s ` o ) = 0 )' % LFN), b1([L1(er), L1(e12), pd], '3jca', '( E e. RR /\\ E <_ ( 1 / 2 ) /\\ ( abs ` ( o - %s ) ) <_ E )' % O1),
              w.inst('kdmemzd')], 'syl3anc', mzc)
    c1 = Closure(w, C1, {'E': ('RR', L1(er)), '( abs ` ( o - %s ) )' % O1: ('RR', b1([b1([pc, b1([w.s([], '1cnd', '( %s -> 1 e. CC )' % C1), b1([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % C1), b1([L1(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % O1)], 'subcld', '( o - %s ) e. CC' % O1)], 'abscld', '( abs ` ( o - %s ) ) e. RR' % O1))})
    c1.atom('( abs ` ( o - %s ) )' % O1)
    p6e = linarith(w, C1, [pd, L1(s([ep], 'rpgt0d', '0 < E'))], '( abs ` ( o - %s ) ) <_ ( 6 x. E )' % O1, closure=c1)
    elo = w.s([w.s([w.s([w.s([], 'oveq1', '( p = o -> ( p - %s ) = ( o - %s ) )' % (O1, O1))], 'fveq2d', '( p = o -> ( abs ` ( p - %s ) ) = ( abs ` ( o - %s ) ) )' % (O1, O1))], 'breq1d',
                    '( p = o -> ( ( abs ` ( p - %s ) ) <_ ( 6 x. E ) <-> ( abs ` ( o - %s ) ) <_ ( 6 x. E ) ) )' % (O1, O1))], 'elrab', '( o e. %s <-> ( o e. %s /\\ ( abs ` ( o - %s ) ) <_ ( 6 x. E ) ) )' % (Z6, ZD(), O1))
    p6 = b1([b1([pzd, p6e], 'jca', '( o e. %s /\\ ( abs ` ( o - %s ) ) <_ ( 6 x. E ) )' % (ZD(), O1)), elo], 'sylibr', 'o e. %s' % Z6)
    GM = '( v e. %s |-> ( abs ` ( %s - v ) ) )' % (Z6, SS)
    G_ = 'ran %s' % GM
    Cv = '( %s /\\ v e. %s )' % (C1, Z6)
    fv = afacts(Cv, w.s([], 'simpr', '( %s -> v e. %s )' % (Cv, Z6)), 'v')
    gvr = w.s([fv['dc']], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Cv, fv['D']))
    gf = b1([gvr], 'fmptd', '%s : %s --> RR' % (GM, Z6))
    gss = b1([gf, w.inst('frn')], 'syl', '%s C_ RR' % G_)
    gfi = b1([b1([L1(z6f), w.inst('mptfi')], 'syl', '%s e. Fin' % GM), w.inst('rnfi')], 'syl', '%s e. Fin' % G_)
    def ing(ante, a_, ain):
        """( ante -> ( abs ` ( SS - a_ ) ) e. G )"""
        cva = w.s([w.s([w.s([], 'oveq2', '( v = %s -> ( %s - v ) = ( %s - %s ) )' % (a_, SS, SS, a_))], 'fveq2d', '( v = %s -> ( abs ` ( %s - v ) ) = ( abs ` ( %s - %s ) ) )' % (a_, SS, SS, a_))], 'eqeq2d',
                  '( v = %s -> ( ( abs ` ( %s - %s ) ) = ( abs ` ( %s - v ) ) <-> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) ) )' % (a_, SS, a_, SS, SS, a_, SS, a_))
        ex_ = w.s([ain, w.s([], 'eqidd', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (ante, SS, a_, SS, a_)),
                   w.s([cva], 'rspcev', '( ( %s e. %s /\\ ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) ) -> E. v e. %s ( abs ` ( %s - %s ) ) = ( abs ` ( %s - v ) ) )' % (a_, Z6, SS, a_, SS, a_, Z6, SS, a_, SS))],
                  'syl2anc', '( %s -> E. v e. %s ( abs ` ( %s - %s ) ) = ( abs ` ( %s - v ) ) )' % (ante, Z6, SS, a_, SS))
        return w.s([w.s([], 'eqid', '%s = %s' % (GM, GM)), ex_, w.s([w.s([], 'fvex', '( abs ` ( %s - %s ) ) e. _V' % (SS, a_))], 'a1i', '( %s -> ( abs ` ( %s - %s ) ) e. _V )' % (ante, SS, a_))],
                   'elrnmptd', '( %s -> ( abs ` ( %s - %s ) ) e. %s )' % (ante, SS, a_, G_))
    pg = ing(C1, 'o', p6)
    gn0 = b1([pg, w.inst('ne0i')], 'syl', '%s =/= (/)' % G_)
    MIN = 'A. y e. %s x <_ y' % G_
    fmin = b1([gss, gfi, gn0, w.inst('fiminre')], 'syl3anc', 'E. x e. %s %s' % (G_, MIN))
    C2 = '( %s /\\ ( x e. %s /\\ %s ) )' % (C1, G_, MIN)
    b2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C2, f))
    L2 = lambda st: lift(w, st, C2)
    xg = b2([], 'simprl', 'x e. %s' % G_); xall = b2([], 'simprr', MIN)
    xr = w.s([w.s([], 'vex', 'x e. _V'), w.s([], 'elrnmpt' if False else 'T.', 'T.')], 'T.', 'T.') if False else None
    erm = w.s([w.s([], 'vex', 'x e. _V'), w.s([w.s([], 'eqid', '%s = %s' % (GM, GM))], 'elrnmpt', '( x e. _V -> ( x e. %s <-> E. v e. %s x = ( abs ` ( %s - v ) ) ) )' % (G_, Z6, SS))],
              'ax-mp', '( x e. %s <-> E. v e. %s x = ( abs ` ( %s - v ) ) )' % (G_, Z6, SS))
    exv = b2([xg, erm], 'sylib', 'E. v e. %s x = ( abs ` ( %s - v ) )' % (Z6, SS))
    cvd = w.s([w.s([w.s([], 'oveq2', '( v = d -> ( %s - v ) = ( %s - d ) )' % (SS, SS))], 'fveq2d', '( v = d -> ( abs ` ( %s - v ) ) = ( abs ` ( %s - d ) ) )' % (SS, SS))], 'eqeq2d',
              '( v = d -> ( x = ( abs ` ( %s - v ) ) <-> x = ( abs ` ( %s - d ) ) ) )' % (SS, SS))
    exd = b2([exv, w.s([cvd], 'cbvrexvw', '( E. v e. %s x = ( abs ` ( %s - v ) ) <-> E. d e. %s x = ( abs ` ( %s - d ) ) )' % (Z6, SS, Z6, SS))], 'sylib', 'E. d e. %s x = ( abs ` ( %s - d ) )' % (Z6, SS))
    C3 = '( %s /\\ ( d e. %s /\\ x = ( abs ` ( %s - d ) ) ) )' % (C2, Z6, SS)
    b3 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C3, f))
    L3 = lambda st: lift(w, st, C3)
    dz = b3([], 'simprl', 'd e. %s' % Z6); xd = b3([], 'simprr', 'x = ( abs ` ( %s - d ) )' % SS)
    fd = afacts(C3, dz, 'd')
    # d is nearest
    C3a = '( %s /\\ a e. %s )' % (C3, Z6)
    az = w.s([], 'simpr', '( %s -> a e. %s )' % (C3a, Z6))
    ag = ing(C3a, 'a', az)
    cy = w.s([w.s([], 'breq2', '( y = ( abs ` ( %s - a ) ) -> ( x <_ y <-> x <_ ( abs ` ( %s - a ) ) ) )' % (SS, SS))], 'rspcv', '( ( abs ` ( %s - a ) ) e. %s -> ( %s -> x <_ ( abs ` ( %s - a ) ) ) )' % (SS, G_, MIN, SS))
    xa = w.s([ag, lift(w, xall, C3a), cy], 'sylc', '( %s -> x <_ ( abs ` ( %s - a ) ) )' % (C3a, SS))
    da = w.s([lift(w, xd, C3a), xa], 'eqbrtrrd' if False else 'T.', 'T.') if False else w.s([xa, lift(w, xd, C3a)], 'T.', 'T.') if False else \
        w.s([lift(w, xd, C3a), xa], 'eqbrtrrd', '( %s -> ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - a ) ) )' % (C3a, SS, SS))
    dmin = b3([da], 'ralrimiva', 'A. a e. %s ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - a ) )' % (Z6, SS, SS))
    X_ = '<. d , 0 >.'
    # X e. I
    zb = b3([fd['mn']], 'T.', 'T.') if False else None
    z0b = b3([fd['mn'], w.s([], 'lbfzo0', '( 0 e. %s <-> %s e. NN )' % (BI('d'), Ma('d')))], 'sylibr', '0 e. %s' % BI('d'))
    xin0 = b3([b3([w.s([w.s([], 'vsnid', 'd e. { d }')], 'a1i', '( %s -> d e. { d } )' % C3), z0b], 'jca', '( d e. { d } /\\ 0 e. %s )' % BI('d')),
               w.s([], 'opelxp', '( %s e. ( { d } X. %s ) <-> ( d e. { d } /\\ 0 e. %s ) )' % (X_, BI('d'), BI('d')))], 'sylibr', '%s e. ( { d } X. %s )' % (X_, BI('d')))
    cad = w.s([w.s([w.s([], 'sneq', '( a = d -> { a } = { d } )'), w.s([w.s([], 'oveq2', '( a = d -> %s = %s )' % (Ma('a'), Ma('d')))], 'oveq2d', '( a = d -> %s = %s )' % (BI('a'), BI('d')))], 'xpeq12d',
                   '( a = d -> ( { a } X. %s ) = ( { d } X. %s ) )' % (BI('a'), BI('d')))], 'eleq2d', '( a = d -> ( %s e. ( { a } X. %s ) <-> %s e. ( { d } X. %s ) ) )' % (X_, BI('a'), X_, BI('d')))
    xin1 = b3([dz, xin0, w.s([cad], 'rspcev', '( ( d e. %s /\\ %s e. ( { d } X. %s ) ) -> E. a e. %s %s e. ( { a } X. %s ) )' % (Z6, X_, BI('d'), Z6, X_, BI('a')))], 'syl2anc',
              'E. a e. %s %s e. ( { a } X. %s )' % (Z6, X_, BI('a')))
    xin = b3([xin1, w.s([], 'eliun', '( %s e. %s <-> E. a e. %s %s e. ( { a } X. %s ) )' % (X_, I_, Z6, X_, BI('a')))], 'sylibr', '%s e. %s' % (X_, I_))
    # Zf values
    def zval(ante, jj, jin):
        a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        f1 = first(ante, jin, jj)
        ff = afacts(ante, f1, '( 1st ` %s )' % jj)
        vv = a([ff['dc'], ff['dn']], 'reccld', '( 1 / %s ) e. CC' % ff['D'])
        cz = w.s([w.s([w.s([], 'fveq2', '( c = %s -> ( 1st ` c ) = ( 1st ` %s ) )' % (jj, jj))], 'oveq2d', '( c = %s -> ( %s - ( 1st ` c ) ) = %s )' % (jj, SS, ff['D']))], 'oveq2d',
                 '( c = %s -> ( 1 / ( %s - ( 1st ` c ) ) ) = ( 1 / %s ) )' % (jj, SS, ff['D']))
        return fvmd(w, ante, ZF_, jj, '( 1 / %s )' % ff['D'], jin, vv, cz, var='c'), ff, f1
    zX, fX, _ = zval(C3, X_, xin)
    o1d = w.s([w.s([w.s([], 'op1st', '( 1st ` %s ) = d' % X_)], 'oveq2i', '( %s - ( 1st ` %s ) ) = ( %s - d )' % (SS, X_, SS))], 'oveq2i', '( 1 / ( %s - ( 1st ` %s ) ) ) = ( 1 / ( %s - d ) )' % (SS, X_, SS))
    zX2 = b3([zX, w.s([o1d], 'a1i', '( %s -> ( 1 / ( %s - ( 1st ` %s ) ) ) = ( 1 / ( %s - d ) ) )' % (C3, SS, X_, SS))], 'eqtrd', '( %s ` %s ) = ( 1 / ( %s - d ) )' % (ZF_, X_, SS))
    dp = b3([fd['dc'], fd['dn']], 'absrpcld', '( abs ` ( %s - d ) ) e. RR+' % SS)
    azx = b3([b3([zX2], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` ( 1 / ( %s - d ) ) )' % (ZF_, X_, SS)),
              b3([w.s([], '1cnd', '( %s -> 1 e. CC )' % C3), fd['dc'], fd['dn']], 'absdivd', '( abs ` ( 1 / ( %s - d ) ) ) = ( ( abs ` 1 ) / ( abs ` ( %s - d ) ) )' % (SS, SS)),
              b3([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % C3)], 'oveq1d', '( ( abs ` 1 ) / ( abs ` ( %s - d ) ) ) = ( 1 / ( abs ` ( %s - d ) ) )' % (SS, SS))],
             '3eqtrd', '( abs ` ( %s ` %s ) ) = ( 1 / ( abs ` ( %s - d ) ) )' % (ZF_, X_, SS))
    # max over I
    Cw = '( %s /\\ w e. %s )' % (C3, I_)
    win = w.s([], 'simpr', '( %s -> w e. %s )' % (Cw, I_))
    zw, fw, f1w = zval(Cw, 'w', win)
    DW = fw['D']
    wdp = w.s([fw['dc'], fw['dn']], 'absrpcld', '( %s -> ( abs ` %s ) e. RR+ )' % (Cw, DW))
    azw = w.s([w.s([zw], 'fveq2d', '( %s -> ( abs ` ( %s ` w ) ) = ( abs ` ( 1 / %s ) ) )' % (Cw, ZF_, DW)),
               w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % Cw), fw['dc'], fw['dn']], 'absdivd', '( %s -> ( abs ` ( 1 / %s ) ) = ( ( abs ` 1 ) / ( abs ` %s ) ) )' % (Cw, DW, DW)),
               w.s([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % Cw)], 'oveq1d', '( %s -> ( ( abs ` 1 ) / ( abs ` %s ) ) = ( 1 / ( abs ` %s ) ) )' % (Cw, DW, DW))],
              '3eqtrd', '( %s -> ( abs ` ( %s ` w ) ) = ( 1 / ( abs ` %s ) ) )' % (Cw, ZF_, DW))
    cda = w.s([w.s([w.s([], 'oveq2', '( a = ( 1st ` w ) -> ( %s - a ) = %s )' % (SS, DW))], 'fveq2d', '( a = ( 1st ` w ) -> ( abs ` ( %s - a ) ) = ( abs ` %s ) )' % (SS, DW))], 'breq2d',
              '( a = ( 1st ` w ) -> ( ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - a ) ) <-> ( abs ` ( %s - d ) ) <_ ( abs ` %s ) ) )' % (SS, SS, SS, DW))
    dle = w.s([f1w, lift(w, dmin, Cw), w.s([cda], 'rspcv', '( ( 1st ` w ) e. %s -> ( A. a e. %s ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - a ) ) -> ( abs ` ( %s - d ) ) <_ ( abs ` %s ) ) )' % (Z6, Z6, SS, SS, SS, DW))],
              'sylc', '( %s -> ( abs ` ( %s - d ) ) <_ ( abs ` %s ) )' % (Cw, SS, DW))
    rw = w.s([lift(w, dp, Cw), wdp, w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Cw)], 'T.', 'T.') if False else w.s([], '1red', '( %s -> 1 e. RR )' % Cw), w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % Cw), dle],
             'lediv2ad', '( %s -> ( 1 / ( abs ` %s ) ) <_ ( 1 / ( abs ` ( %s - d ) ) ) )' % (Cw, DW, SS))
    mw = w.s([w.s([azw, rw], 'eqbrtrd', '( %s -> ( abs ` ( %s ` w ) ) <_ ( 1 / ( abs ` ( %s - d ) ) ) )' % (Cw, ZF_, SS)), lift(w, azx, Cw)], 'breqtrrd',
             '( %s -> ( abs ` ( %s ` w ) ) <_ ( abs ` ( %s ` %s ) ) )' % (Cw, ZF_, ZF_, X_))
    mall = b3([mw], 'ralrimiva', 'A. w e. %s ( abs ` ( %s ` w ) ) <_ ( abs ` ( %s ` %s ) )' % (I_, ZF_, ZF_, X_))
    cwy = w.s([w.s([w.s([], 'fveq2', '( w = y -> ( %s ` w ) = ( %s ` y ) )' % (ZF_, ZF_))], 'fveq2d', '( w = y -> ( abs ` ( %s ` w ) ) = ( abs ` ( %s ` y ) ) )' % (ZF_, ZF_))], 'breq1d',
              '( w = y -> ( ( abs ` ( %s ` w ) ) <_ ( abs ` ( %s ` %s ) ) <-> ( abs ` ( %s ` y ) ) <_ ( abs ` ( %s ` %s ) ) ) )' % (ZF_, ZF_, X_, ZF_, ZF_, X_))
    MY = 'A. y e. %s ( abs ` ( %s ` y ) ) <_ ( abs ` ( %s ` %s ) )' % (I_, ZF_, ZF_, X_)
    maly = b3([mall, w.s([cwy], 'cbvralvw', '( A. w e. %s ( abs ` ( %s ` w ) ) <_ ( abs ` ( %s ` %s ) ) <-> %s )' % (I_, ZF_, ZF_, X_, MY))], 'sylib', MY)
    # T <_ abs ( Zf ` X )
    L3o = lambda st: lift(w, st, C3)
    oc = L3o(pc); od = L3o(pd); o6 = L3o(p6)
    ic3 = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % C3)
    tc3 = b3([L3o(tr)], 'recnd', 'T e. CC'); ec3 = b3([L3o(er)], 'recnd', 'E e. CC')
    cr = Closure(w, C3, {'o': ('CC', oc), 'T': ('CC', tc3), 'E': ('CC', ec3), '_i': ('CC', ic3)}); cr.atom('_i')
    eo = __import__('mvlib').ringeq(w, C3, '( %s - o )' % SS, '( E + ( %s - o ) )' % O1, cr)
    o1c = cr.mem(O1, 'CC')
    tri = b3([ec3, b3([o1c, oc], 'subcld', '( %s - o ) e. CC' % O1)], 'abstrid', '( abs ` ( E + ( %s - o ) ) ) <_ ( ( abs ` E ) + ( abs ` ( %s - o ) ) )' % (O1, O1))
    t2 = b3([b3([L3o(er), b3([L3o(ep)], 'rpge0d', '0 <_ E')], 'absidd', '( abs ` E ) = E'), b3([o1c, oc], 'abssubd', '( abs ` ( %s - o ) ) = ( abs ` ( o - %s ) )' % (O1, O1))], 'oveq12d',
            '( ( abs ` E ) + ( abs ` ( %s - o ) ) ) = ( E + ( abs ` ( o - %s ) ) )' % (O1, O1))
    t3 = b3([b3([b3([eo], 'fveq2d', '( abs ` ( %s - o ) ) = ( abs ` ( E + ( %s - o ) ) )' % (SS, O1)), tri], 'eqbrtrd', '( abs ` ( %s - o ) ) <_ ( ( abs ` E ) + ( abs ` ( %s - o ) ) )' % (SS, O1)), t2], 'breqtrd',
            '( abs ` ( %s - o ) ) <_ ( E + ( abs ` ( o - %s ) ) )' % (SS, O1))
    cda2 = w.s([w.s([w.s([], 'oveq2', '( a = o -> ( %s - a ) = ( %s - o ) )' % (SS, SS))], 'fveq2d', '( a = o -> ( abs ` ( %s - a ) ) = ( abs ` ( %s - o ) ) )' % (SS, SS))], 'breq2d',
               '( a = o -> ( ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - a ) ) <-> ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - o ) ) ) )' % (SS, SS, SS, SS))
    dlo = b3([o6, dmin, w.s([cda2], 'rspcv', '( o e. %s -> ( A. a e. %s ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - a ) ) -> ( abs ` ( %s - d ) ) <_ ( abs ` ( %s - o ) ) ) )' % (Z6, Z6, SS, SS, SS, SS))],
             'sylc', '( abs ` ( %s - d ) ) <_ ( abs ` ( %s - o ) )' % (SS, SS))
    c3 = Closure(w, C3, {'E': ('RR', L3o(er)), '( abs ` ( %s - d ) )' % SS: ('RR', b3([dp], 'rpred', '( abs ` ( %s - d ) ) e. RR' % SS)),
                         '( abs ` ( %s - o ) )' % SS: ('RR', b3([b3([L3o(s0c), oc], 'subcld', '( %s - o ) e. CC' % SS)], 'abscld', '( abs ` ( %s - o ) ) e. RR' % SS)),
                         '( abs ` ( o - %s ) )' % O1: ('RR', b3([b3([oc, o1c], 'subcld', '( o - %s ) e. CC' % O1)], 'abscld', '( abs ` ( o - %s ) ) e. RR' % O1))})
    for e_ in ('( abs ` ( %s - d ) )' % SS, '( abs ` ( %s - o ) )' % SS, '( abs ` ( o - %s ) )' % O1):
        c3.atom(e_)
    d2e = linarith(w, C3, [dlo, t3, od], '( abs ` ( %s - d ) ) <_ ( 2 x. E )' % SS, closure=c3)
    TT = '( 1 / ( 2 x. E ) )'
    e2p = b3([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % C3), L3o(ep)], 'rpmulcld', '( 2 x. E ) e. RR+')
    tle = b3([dp, e2p, w.s([], '1red', '( %s -> 1 e. RR )' % C3), w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % C3), d2e], 'lediv2ad', '%s <_ ( 1 / ( abs ` ( %s - d ) ) )' % (TT, SS))
    tle2 = b3([tle, azx], 'breqtrrd', '%s <_ ( abs ` ( %s ` %s ) )' % (TT, ZF_, X_))
    ttr = b3([e2p], 'rprecred', '%s e. RR' % TT); tt0 = b3([b3([e2p], 'rpreccld', '%s e. RR+' % TT)], 'rpge0d', '0 <_ %s' % TT)
    # tpmaxg
    TPM = tsub(stmt('tpmaxg'), {'N': 'J', 'M': 'M', 'I': I_, 'Z': ZF_, 'X': X_, 'T': TT, 'k': 'l'})
    tpa, tpc = split_imp(TPM)
    ta = top_and(tpa)
    tp = b3([b3([L3o(jn), L3o(mm)], 'jca', ta[0]), b3([L3o(iF), L3o(hJ), L3o(zff)], '3jca', ta[1]), b3([xin, maly, b3([ttr, tt0, tle2], '3jca', top_and(ta[2])[2])], '3jca', ta[2]), w.inst('tpmaxg')],
            'syl3anc', tpc)
    WIN = '( ( M + 1 ) ... ( M + J ) )'
    Ck = '( %s /\\ l e. %s )' % (C3, WIN)
    k_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ck, f))
    Lk = lambda st: lift(w, st, Ck)
    lw = k_([], 'simpr', 'l e. %s' % WIN)
    m1n = k_([Lk(L3o(mm)), w.inst('nn0p1nn')], 'syl', '( M + 1 ) e. NN')
    ln = k_([m1n, k_([lw, w.inst('elfzuz')], 'syl', 'l e. ( ZZ>= ` ( M + 1 ) )'), w.inst('eluznn')], 'syl2anc', 'l e. NN')
    l0 = k_([ln], 'nnnn0d', 'l e. NN0')
    Yf = lambda f_: '( ( 1 / ( %s - %s ) ) ^ l )' % (SS, f_)
    I_f = 'U_ f e. %s ( { f } X. %s )' % (Z6, BI('f'))
    Dj = '( ( 1 / ( %s - ( 1st ` j ) ) ) ^ l )' % SS
    h1 = w.s([w.s([w.s([w.s([w.s([], 'fveq2', '( j = <. f , g >. -> ( 1st ` j ) = ( 1st ` <. f , g >. ) )'), w.s([], 'op1st', '( 1st ` <. f , g >. ) = f')], 'eqtrdi', '( j = <. f , g >. -> ( 1st ` j ) = f )')],
                            'oveq2d', '( j = <. f , g >. -> ( %s - ( 1st ` j ) ) = ( %s - f ) )' % (SS, SS))], 'oveq2d', '( j = <. f , g >. -> ( 1 / ( %s - ( 1st ` j ) ) ) = ( 1 / ( %s - f ) ) )' % (SS, SS))],
             'oveq1d', '( j = <. f , g >. -> %s = %s )' % (Dj, Yf('f')))
    Cf = '( %s /\\ f e. %s )' % (Ck, Z6)
    ff = afacts(Cf, w.s([], 'simpr', '( %s -> f e. %s )' % (Cf, Z6)), 'f')
    yfc = w.s([w.s([ff['dc'], ff['dn']], 'reccld', '( %s -> ( 1 / %s ) e. CC )' % (Cf, ff['D'])), lift(w, l0, Cf)], 'expcld', '( %s -> %s e. CC )' % (Cf, Yf('f')))
    Cfg = '( %s /\\ ( f e. %s /\\ g e. %s ) )' % (Ck, Z6, BI('f'))
    yfc2 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Cfg, Ck)), w.s([], 'simprl', '( %s -> f e. %s )' % (Cfg, Z6))], 'jca', '( %s -> %s )' % (Cfg, Cf)), yfc], 'syl', '( %s -> %s e. CC )' % (Cfg, Yf('f')))
    f2d = w.s([h1, Lk(z6f), w.s([w.s([], 'fzofi', '%s e. Fin' % BI('f'))], 'a1i', '( %s -> %s e. Fin )' % (Cf, BI('f'))), yfc2], 'fsum2d',
              '( %s -> sum_ f e. %s sum_ g e. %s %s = sum_ j e. %s %s )' % (Ck, Z6, BI('f'), Yf('f'), I_f, Dj))
    cbi = w.s([w.s([w.s([], 'sneq', '( f = a -> { f } = { a } )'), w.s([w.s([], 'oveq2', '( f = a -> %s = %s )' % (Ma('f'), Ma('a')))], 'oveq2d', '( f = a -> %s = %s )' % (BI('f'), BI('a')))], 'xpeq12d',
                   '( f = a -> ( { f } X. %s ) = ( { a } X. %s ) )' % (BI('f'), BI('a')))], 'cbviunv', '%s = %s' % (I_f, I_))
    sI = k_([w.s([cbi], 'a1i', '( %s -> %s = %s )' % (Ck, I_f, I_))], 'sumeq1d', 'sum_ j e. %s %s = sum_ j e. %s %s' % (I_f, Dj, I_, Dj))
    # Zf values on I
    Cj = '( %s /\\ j e. %s )' % (Ck, I_)
    zj, fjj, _ = zval(Cj, 'j', w.s([], 'simpr', '( %s -> j e. %s )' % (Cj, I_)))
    zjk = w.s([zj], 'oveq1d', '( %s -> ( ( %s ` j ) ^ l ) = %s )' % (Cj, ZF_, Dj))
    sZ = k_([zjk], 'sumeq2dv', 'sum_ j e. %s ( ( %s ` j ) ^ l ) = sum_ j e. %s %s' % (I_, ZF_, I_, Dj))
    # inner sums
    fcn = w.s([w.s([w.s([], 'fzofi', '%s e. Fin' % BI('f'))], 'a1i', '( %s -> %s e. Fin )' % (Cf, BI('f'))), yfc, w.inst('fsumconst')], 'syl2anc',
              '( %s -> sum_ g e. %s %s = ( ( # ` %s ) x. %s ) )' % (Cf, BI('f'), Yf('f'), BI('f'), Yf('f')))
    hf = w.s([w.s([ff['mn']], 'nnnn0d', '( %s -> %s e. NN0 )' % (Cf, Ma('f'))), w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (Cf, BI('f'), Ma('f')))
    er_ = w.s([ff['dc'], ff['dn'], w.s([lift(w, l0, Cf)], 'nn0zd', '( %s -> l e. ZZ )' % Cf)], 'exprecd', '( %s -> %s = ( 1 / ( %s ^ l ) ) )' % (Cf, Yf('f'), ff['D']))
    pw = w.s([ff['dc'], lift(w, l0, Cf)], 'expcld', '( %s -> ( %s ^ l ) e. CC )' % (Cf, ff['D']))
    pwn = w.s([ff['dc'], ff['dn'], w.s([lift(w, l0, Cf)], 'nn0zd', '( %s -> l e. ZZ )' % Cf)], 'expne0d', '( %s -> ( %s ^ l ) =/= 0 )' % (Cf, ff['D']))
    mfc = w.s([ff['mn']], 'nncnd', '( %s -> %s e. CC )' % (Cf, Ma('f')))
    dvr = w.s([mfc, pw, pwn], 'divrecd', '( %s -> ( %s / ( %s ^ l ) ) = ( %s x. ( 1 / ( %s ^ l ) ) ) )' % (Cf, Ma('f'), ff['D'], Ma('f'), ff['D']))
    inn = w.s([fcn, w.s([hf, er_], 'oveq12d', '( %s -> ( ( # ` %s ) x. %s ) = ( %s x. ( 1 / ( %s ^ l ) ) ) )' % (Cf, BI('f'), Yf('f'), Ma('f'), ff['D'])), dvr], '3eqtr4d' if False else 'T.', 'T.') if False else None
    inn = w.s([w.s([fcn, w.s([hf, er_], 'oveq12d', '( %s -> ( ( # ` %s ) x. %s ) = ( %s x. ( 1 / ( %s ^ l ) ) ) )' % (Cf, BI('f'), Yf('f'), Ma('f'), ff['D']))], 'eqtrd',
                   '( %s -> sum_ g e. %s %s = ( %s x. ( 1 / ( %s ^ l ) ) ) )' % (Cf, BI('f'), Yf('f'), Ma('f'), ff['D'])), dvr], 'eqtr4d', '( %s -> sum_ g e. %s %s = ( %s / ( %s ^ l ) ) )' % (Cf, BI('f'), Yf('f'), Ma('f'), ff['D']))
    sO = k_([inn], 'sumeq2dv', 'sum_ f e. %s sum_ g e. %s %s = sum_ f e. %s ( %s / ( %s ^ l ) )' % (Z6, BI('f'), Yf('f'), Z6, Ma('f'), ff['D']))
    idfq = w.s([], 'id', '( f = q -> f = q )')
    cfq, nfq = w.congr('( %s / ( %s ^ l ) )' % (Ma('f'), ff['D']), {'f': 'q'}, 'f = q', {'f': idfq})
    cbf = w.s([cfq], 'cbvsumv', 'sum_ f e. %s ( %s / ( %s ^ l ) ) = sum_ q e. %s %s' % (Z6, Ma('f'), ff['D'], Z6, nfq))
    SQl = 'sum_ q e. %s %s' % (Z6, nfq)
    tot = k_([sZ, k_([k_([sI], 'eqcomd', 'sum_ j e. %s %s = sum_ j e. %s %s' % (I_, Dj, I_f, Dj)), k_([f2d], 'eqcomd', 'sum_ j e. %s %s = sum_ f e. %s sum_ g e. %s %s' % (I_f, Dj, Z6, BI('f'), Yf('f')))],
                               'eqtrd', 'sum_ j e. %s %s = sum_ f e. %s sum_ g e. %s %s' % (I_, Dj, Z6, BI('f'), Yf('f')))], 'eqtrd', 'sum_ j e. %s ( ( %s ` j ) ^ l ) = sum_ f e. %s sum_ g e. %s %s' % (I_, ZF_, Z6, BI('f'), Yf('f')))
    tot2 = k_([tot, sO, w.s([cbf], 'a1i', '( %s -> sum_ f e. %s ( %s / ( %s ^ l ) ) = %s )' % (Ck, Z6, Ma('f'), ff['D'], SQl))], '3eqtrd', 'sum_ j e. %s ( ( %s ` j ) ^ l ) = %s' % (I_, ZF_, SQl))
    CNT = tpc.split(' ( ', 1)[1] if False else None
    B1 = tpc[len('E. l e. %s ' % WIN):]
    B2 = GOAL[len('E. l e. %s ' % WIN):]
    lhs = B1.split(' <_ ( abs ` ')[0]
    assert B2 == '%s <_ ( abs ` %s )' % (lhs, SQl), (B2[-300:], SQl[-200:])
    stp = w.s([k_([tot2], 'fveq2d', '( abs ` sum_ j e. %s ( ( %s ` j ) ^ l ) ) = ( abs ` %s )' % (I_, ZF_, SQl))], 'breq2d', '( %s -> ( %s <-> %s ) )' % (Ck, B1, B2))
    imp = w.s([stp], 'biimpd', '( %s -> ( %s -> %s ) )' % (Ck, B1, B2))
    rx = b3([imp], 'reximdva', '( %s -> %s )' % (tpc, GOAL))
    g3 = b3([tp, rx], 'mpd', GOAL)
    g2 = b2([exd, g3], 'rexlimddv', GOAL)
    g1 = b1([fmin, g2], 'rexlimddv', GOAL)
    w.qed([hzo, g1], 'rexlimddv', S['kdturan'])
    return run(w)








if __name__ == '__main__':
    gen_turan()
