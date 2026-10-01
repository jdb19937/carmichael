"""Sortie GF1, section C: avgExp, Kker, KQ (gf1cibl, gf1avgi, gf1avgh, gf1avgb, gf1kq, gf1kb, gf1kqb).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_c.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *
from mvlib import ringeq

only = sys.argv[1:]
S['gf1cibl.1'] = '( ph -> A e. RR )'
S['gf1cibl.2'] = '( ph -> B e. RR )'
S['gf1cibl.3'] = '( ph -> ( s e. CC |-> X ) e. ( CC -cn-> CC ) )'
S['gf1cibl.4'] = '( s = t -> X = Y )'
S['gf1cibl'] = ('( ph -> ( ( t e. ( A (,) B ) |-> Y ) e. ( ( A (,) B ) -cn-> CC ) /\\ '
                '( t e. ( A (,) B ) |-> Y ) e. L^1 ) )')


def gen_cibl():
    w = W('gf1cibl', 'An entire function restricted to a bounded open real interval is continuous and integrable there ( ~ rescncf , ~ cniccibl , ~ iblss ).')
    h1, h2, h3, h4 = ehyps(w, 'gf1cibl')
    A = 'ph'
    d = mk(w, A)
    G = '( s e. CC |-> X )'
    I = '( A [,] B )'; O = '( A (,) B )'
    icr = d('syl2anc', [h1, h2, w.inst('iccssre')], '%s C_ RR' % I)
    icc = d('sstrd', [icr, a1(w, A, 'ax-resscn', 'RR C_ CC')], '%s C_ CC' % I)
    oi = a1(w, A, 'ioossicc', '%s C_ %s' % (O, I))
    occ = d('sstrd', [oi, icc], '%s C_ CC' % O)
    # restriction to [A,B]
    rc1 = w.s([icc, w.inst('rescncf')], 'syl', '( ph -> ( %s e. ( CC -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (G, G, I, I))
    rc2 = d('mpd', [h3, rc1], '( %s |` %s ) e. ( %s -cn-> CC )' % (G, I, I))
    rm = w.s([icc, w.inst('resmpt')], 'syl', '( ph -> ( %s |` %s ) = ( s e. %s |-> X ) )' % (G, I, I))
    cI = d('eqeltrrd', [rm, rc2], '( s e. %s |-> X ) e. ( %s -cn-> CC )' % (I, I))
    iI = d('3jca', [h1, h2, cI], '( A e. RR /\\ B e. RR /\\ ( s e. %s |-> X ) e. ( %s -cn-> CC ) )' % (I, I))
    ibI = w.s([iI, w.inst('cniccibl')], 'syl', '( ph -> ( s e. %s |-> X ) e. L^1 )' % I)
    # X e. CC for s e. [A,B]
    ff = d('syl', [h3, w.inst('cncff')], '%s : CC --> CC' % G) if False else w.s([h3, w.inst('cncff')], 'syl', '( ph -> %s : CC --> CC )' % G)
    fm = w.s([w.s([], 'eqid', '%s = %s' % (G, G))], 'fmpt', '( A. s e. CC X e. CC <-> %s : CC --> CC )' % G)
    ra = d('mpbird', [ff, a1(w, A, 'ax-mp', '( A. s e. CC X e. CC <-> %s : CC --> CC )' % G, []) if False else w.s([fm], 'a1i', '( ph -> ( A. s e. CC X e. CC <-> %s : CC --> CC ) )' % G)], 'A. s e. CC X e. CC')
    As = '( ph /\\ s e. %s )' % I
    sI = w.s([], 'simpr', '( %s -> s e. %s )' % (As, I))
    sC = D(w, As, 'sseldd', [lift(w, icc, As), sI], 's e. CC')
    xc = D(w, As, 'syl', [lift(w, ra, As), w.inst('rsp')], '( s e. CC -> X e. CC )')
    xc2 = D(w, As, 'mpd', [sC, xc], 'X e. CC')
    ibO = d('iblss', [oi, a1(w, A, 'ioombl', '%s e. dom vol' % O), xc2, ibI], '( s e. %s |-> X ) e. L^1' % O)
    cb = w.s([h4], 'cbvmptv', '( s e. %s |-> X ) = ( t e. %s |-> Y )' % (O, O))
    ib = d('eqeltrrd', [w.s([cb], 'a1i', '( ph -> ( s e. %s |-> X ) = ( t e. %s |-> Y ) )' % (O, O)), ibO], '( t e. %s |-> Y ) e. L^1' % O)
    # continuity on ( A , B )
    ro1 = w.s([occ, w.inst('rescncf')], 'syl', '( ph -> ( %s e. ( CC -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (G, G, O, O))
    ro2 = d('mpd', [h3, ro1], '( %s |` %s ) e. ( %s -cn-> CC )' % (G, O, O))
    rmo = w.s([occ, w.inst('resmpt')], 'syl', '( ph -> ( %s |` %s ) = ( s e. %s |-> X ) )' % (G, O, O))
    rmo2 = d('eqtrd', [rmo, w.s([cb], 'a1i', '( ph -> ( s e. %s |-> X ) = ( t e. %s |-> Y ) )' % (O, O))], '( %s |` %s ) = ( t e. %s |-> Y )' % (G, O, O))
    cO = d('eqeltrrd', [rmo2, ro2], '( t e. %s |-> Y ) e. ( %s -cn-> CC )' % (O, O))
    fin = d('jca', [cO, ib], split_imp(S['gf1cibl'])[1])
    w.qed([fin], 'idi', S['gf1cibl'])
    return run(w, only)


ES = '( exp ` ( W x. s ) )'
S['gf1eh'] = '( W e. CC -> %s )' % HOL('( s e. CC |-> %s )' % ES, 'CC')


def gen_eh():
    w = W('gf1eh', 'The function ` s |-> exp ( W s ) ` is entire ( ~ gf1edvc , ~ z6ehdv ).')
    A = 'W e. CC'
    d = mk(w, A)
    As = '( W e. CC /\\ s e. CC )'
    ds = mk(w, As)
    wc = w.s([], 'simpl', '( %s -> W e. CC )' % As)
    e = ds('efcld', [ds('mulcld', [wc, w.s([], 'simpr', '( %s -> s e. CC )' % As)], '( W x. s ) e. CC')], '%s e. CC' % ES)
    ew = ds('mulcld', [e, wc], '( %s x. W ) e. CC' % ES)
    ra = d('ralrimiva', [e], 'A. s e. CC %s e. CC' % ES)
    rb = d('ralrimiva', [ew], 'A. s e. CC ( %s x. W ) e. CC' % ES)
    dv = w.s([w.s([], 'id', '( W e. CC -> W e. CC )'), w.inst('gf1edvc')], 'syl', '( W e. CC -> ( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> ( %s x. W ) ) )' % (ES, ES))
    j = d('jca', [dv, rb], '( ( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> ( %s x. W ) ) /\\ A. s e. CC ( %s x. W ) e. CC )' % (ES, ES, ES))
    j2 = d('jca', [ra, j], '( A. s e. CC %s e. CC /\\ ( ( CC _D ( s e. CC |-> %s ) ) = ( s e. CC |-> ( %s x. W ) ) /\\ A. s e. CC ( %s x. W ) e. CC ) )' % (ES, ES, ES, ES))
    fin = w.s([j2, w.inst('z6ehdv')], 'syl', S['gf1eh'])
    w.qed([fin], 'idi', S['gf1eh'])
    return run(w, only)


def gen_avgi():
    w = W('gf1avgi', 'The integral form of ` avgExp ` (Lean\'s definition): ` ( 1 / L ) S. ( A , A + L ) exp ( W t ) dt = exp ( A W ) PH ( L , W ) / L ` ( ~ ftc2 ; ` W = 0 ` by ~ itgconst ; Lean ` avgExp ` , ` avgExp_eq_of_ne ` , ` avgExp_zero ` ).')
    X0, CONC = split_imp(S['gf1avgi'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); lp = proj(w, X0, 'L e. RR+'); wc = proj(w, X0, 'W e. CC')
    lr = d('rpred', [lp], 'L e. RR'); lc = d('rpcnd', [lp], 'L e. CC'); ln0 = d('rpne0d', [lp], 'L =/= 0')
    BP = '( A + L )'
    bpr = d('readdcld', [ar, lr], '%s e. RR' % BP)
    O = '( A (,) %s )' % BP
    I_ = '( A [,] %s )' % BP
    EWT = '( exp ` ( W x. t ) )'
    # entire functions and their restrictions
    eh = w.s([wc, w.inst('gf1eh')], 'syl', '( %s -> %s )' % (X0, HOL('( s e. CC |-> %s )' % ES, 'CC')))
    ehc = d('z6ehc', [wc], HOL('( s e. CC |-> W )', 'CC'))
    ehm = d('z6ehmul', [eh, ehc], HOL('( s e. CC |-> ( %s x. W ) )' % ES, 'CC'))
    sb1 = w.s([w.s([w.s([], 'oveq2', '( s = t -> ( W x. s ) = ( W x. t ) )')], 'fveq2d', '( s = t -> %s = %s )' % (ES, EWT))], 'idi', '( s = t -> %s = %s )' % (ES, EWT))
    sb2 = w.s([sb1], 'oveq1d', '( s = t -> ( %s x. W ) = ( %s x. W ) )' % (ES, EWT))
    c1 = d('gf1cibl', [ar, bpr, d('simpld', [eh], '( s e. CC |-> %s ) e. ( CC -cn-> CC )' % ES), sb1],
           '( ( t e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( t e. %s |-> %s ) e. L^1 )' % (O, EWT, O, O, EWT))
    c2 = d('gf1cibl', [ar, bpr, d('simpld', [ehm], '( s e. CC |-> ( %s x. W ) ) e. ( CC -cn-> CC )' % ES), sb2],
           '( ( t e. %s |-> ( %s x. W ) ) e. ( %s -cn-> CC ) /\\ ( t e. %s |-> ( %s x. W ) ) e. L^1 )' % (O, EWT, O, O, EWT))
    ibl = d('simprd', [c1], '( t e. %s |-> %s ) e. L^1' % (O, EWT))
    # the primitive on [ A , A + L ]
    FTt = '( t e. RR |-> %s )' % EWT
    FT = '( x e. RR |-> ( exp ` ( W x. x ) ) )'
    Xt = '( %s /\\ x e. RR )' % X0
    dt = mk(w, Xt)
    tr = w.s([], 'simpr', '( %s -> x e. RR )' % Xt)
    ez = dt('efcld', [dt('mulcld', [lift(w, wc, Xt), dt('recnd', [tr], 'x e. CC')], '( W x. x ) e. CC')], '( exp ` ( W x. x ) ) e. CC')
    ff = d('fmptd', [ez], '%s : RR --> CC' % FT)
    cbx = w.s([w.s([w.s([], 'oveq2', '( x = t -> ( W x. x ) = ( W x. t ) )')], 'fveq2d', '( x = t -> ( exp ` ( W x. x ) ) = %s )' % EWT)], 'cbvmptv', '%s = %s' % (FT, FTt))
    edv0 = w.s([wc, w.inst('gf1edv')], 'syl', '( %s -> ( RR _D %s ) = ( t e. RR |-> ( %s x. W ) ) )' % (X0, FTt, EWT))
    edv = d('eqtrd', [a1(w, X0, 'oveq2i', '( RR _D %s ) = ( RR _D %s )' % (FT, FTt), [cbx]), edv0], '( RR _D %s ) = ( t e. RR |-> ( %s x. W ) )' % (FT, EWT))
    Xt2 = '( %s /\\ t e. RR )' % X0
    ezt = D(w, Xt2, 'efcld', [D(w, Xt2, 'mulcld', [lift(w, wc, Xt2), D(w, Xt2, 'recnd', [w.s([], 'simpr', '( %s -> t e. RR )' % Xt2)], 't e. CC')], '( W x. t ) e. CC')], '%s e. CC' % EWT)
    ezz = D(w, Xt2, 'mulcld', [ezt, lift(w, wc, Xt2)], '( %s x. W ) e. CC' % EWT)
    dm = d('eqtrd', [d('dmeqd', [edv], 'dom ( RR _D %s ) = dom ( t e. RR |-> ( %s x. W ) )' % (FT, EWT)), d('dmmptd', [ezz], 'dom ( t e. RR |-> ( %s x. W ) ) = RR' % EWT)],
           'dom ( RR _D %s ) = RR' % FT)
    rc = a1(w, X0, 'ax-resscn', 'RR C_ CC')
    rr = a1(w, X0, 'ssid', 'RR C_ RR')
    j1 = d('3jca', [rc, ff, rr], '( RR C_ CC /\\ %s : RR --> CC /\\ RR C_ RR )' % FT)
    fcn = w.s([d('jca', [j1, dm], '( ( RR C_ CC /\\ %s : RR --> CC /\\ RR C_ RR ) /\\ dom ( RR _D %s ) = RR )' % (FT, FT)), w.inst('dvcn')], 'syl', '( %s -> %s e. ( RR -cn-> CC ) )' % (X0, FT))
    F1 = '( %s |` %s )' % (FT, I_)
    isr = d('syl2anc', [ar, bpr, w.inst('iccssre')], '%s C_ RR' % I_)
    f1cn = d('mpd', [fcn, w.s([isr, w.inst('rescncf')], 'syl', '( %s -> ( %s e. ( RR -cn-> CC ) -> %s e. ( %s -cn-> CC ) ) )' % (X0, FT, F1, I_))], '%s e. ( %s -cn-> CC )' % (F1, I_))
    TT = '( ( TopOpen ` CCfld ) |`t RR )'
    j5 = d('jca', [d('jca', [rc, ff], '( RR C_ CC /\\ %s : RR --> CC )' % FT), d('jca', [rr, isr], '( RR C_ RR /\\ %s C_ RR )' % I_)],
           '( ( RR C_ CC /\\ %s : RR --> CC ) /\\ ( RR C_ RR /\\ %s C_ RR ) )' % (FT, I_))
    k1 = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    k2 = w.s([], 'eqid', '%s = %s' % (TT, TT))
    dres = w.s([k1, k2], 'dvres', '( ( ( RR C_ CC /\\ %s : RR --> CC ) /\\ ( RR C_ RR /\\ %s C_ RR ) ) -> ( RR _D %s ) = ( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (FT, I_, F1, FT, TT, I_))
    dr = w.s([j5, dres], 'syl', '( %s -> ( RR _D %s ) = ( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (X0, F1, FT, TT, I_))
    tg = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % TT)], 'eqcomi', '%s = ( topGen ` ran (,) )' % TT)
    tg3 = w.s([w.s([tg], 'fveq2i', '( int ` %s ) = ( int ` ( topGen ` ran (,) ) )' % TT)], 'fveq1i', '( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s )' % (TT, I_, I_))
    icn = d('syl2anc', [ar, bpr, w.inst('iccntr')], '( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s' % (I_, O))
    it = d('eqtrd', [w.s([tg3], 'a1i', '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s ) )' % (X0, TT, I_, I_)), icn], '( ( int ` %s ) ` %s ) = %s' % (TT, I_, O))
    G = '( t e. RR |-> ( %s x. W ) )' % EWT
    GO = '( t e. %s |-> ( %s x. W ) )' % (O, EWT)
    rs = d('reseq12d', [edv, it], '( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( %s |` %s )' % (FT, TT, I_, G, O))
    rm = a1(w, X0, 'ax-mp', '( %s |` %s ) = %s' % (G, O, GO), [w.s([], 'ioossre', '%s C_ RR' % O), w.inst('resmpt')])
    dF = chain(w, X0, ['( RR _D %s )' % F1, '( ( RR _D %s ) |` ( ( int ` %s ) ` %s ) )' % (FT, TT, I_), '( %s |` %s )' % (G, O), GO], [dr, rs, rm])
    dcn = d('eqeltrrd', [d('eqcomd', [dF], '%s = ( RR _D %s )' % (GO, F1)), d('simpld', [c2], '%s e. ( %s -cn-> CC )' % (GO, O))], '( RR _D %s ) e. ( %s -cn-> CC )' % (F1, O))
    dib = d('eqeltrrd', [d('eqcomd', [dF], '%s = ( RR _D %s )' % (GO, F1)), d('simprd', [c2], '%s e. L^1' % GO)], '( RR _D %s ) e. L^1' % F1)
    alb = d('ltled', [ar, bpr, d('ltaddrpd', [ar, lp], 'A < %s' % BP)], 'A <_ %s' % BP)
    ftc = d('ftc2', [ar, bpr, alb, dcn, dib, f1cn], 'S. %s ( ( RR _D %s ) ` t ) _d t = ( ( %s ` %s ) - ( %s ` A ) )' % (O, F1, F1, BP, F1))
    # integrand
    Xo = '( %s /\\ t e. %s )' % (X0, O)
    do = mk(w, Xo)
    to = w.s([], 'simpr', '( %s -> t e. %s )' % (Xo, O))
    tor = do('sseldd', [a1(w, Xo, 'ioossre', '%s C_ RR' % O), to], 't e. RR')
    eo = do('efcld', [do('mulcld', [lift(w, wc, Xo), do('recnd', [tor], 't e. CC')], '( W x. t ) e. CC')], '%s e. CC' % EWT)
    fv1 = do('fveq1d', [lift(w, dF, Xo)], '( ( RR _D %s ) ` t ) = ( %s ` t )' % (F1, GO))
    fv2 = do('fvmpt2d' if False else 'syl2anc', [to, do('mulcld', [eo, lift(w, wc, Xo)], '( %s x. W ) e. CC' % EWT), w.inst('fvmpt3i') if False else w.inst('fvmpt2')], '( %s ` t ) = ( %s x. W )' % (GO, EWT)) if False else None
    fv2 = w.s([w.s([], 'eqid', '%s = %s' % (GO, GO))], 'fvmpt2i' if False else 'fvmpt2i', '( t e. %s -> ( %s ` t ) = ( _I ` ( %s x. W ) ) )' % (O, GO, EWT)) if False else None
    fv2 = do('fvmptd2' if False else 'syl2anc', [to, do('mulcld', [eo, lift(w, wc, Xo)], '( %s x. W ) e. CC' % EWT), w.inst('fvmpt2')], '( %s ` t ) = ( %s x. W )' % (GO, EWT))
    cm = do('mulcomd', [eo, lift(w, wc, Xo)], '( %s x. W ) = ( W x. %s )' % (EWT, EWT))
    ig = do('eqtrd', [do('eqtrd', [fv1, fv2], '( ( RR _D %s ) ` t ) = ( %s x. W )' % (F1, EWT)), cm], '( ( RR _D %s ) ` t ) = ( W x. %s )' % (F1, EWT))
    ieq = d('itgeq2dv', [ig], 'S. %s ( ( RR _D %s ) ` t ) _d t = S. %s ( W x. %s ) _d t' % (O, F1, O, EWT))
    IT = 'S. %s %s _d t' % (O, EWT)
    imc = d('itgmulc2', [wc, eo, ibl], '( W x. %s ) = S. %s ( W x. %s ) _d t' % (IT, O, EWT))
    # endpoint values
    def endv(p, pin, pr):
        r1 = d('fvresd' if False else 'syl', [pin, w.inst('fvres')], '( %s ` %s ) = ( %s ` %s )' % (F1, p, FT, p))
        sv = w.s([w.s([], 'oveq2', '( x = %s -> ( W x. x ) = ( W x. %s ) )' % (p, p))], 'fveq2d', '( x = %s -> ( exp ` ( W x. x ) ) = ( exp ` ( W x. %s ) ) )' % (p, p))
        pv = d('efcld', [d('mulcld', [wc, d('recnd', [pr], '%s e. CC' % p)], '( W x. %s ) e. CC' % p)], '( exp ` ( W x. %s ) ) e. CC' % p)
        r2 = d('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (X0, FT, FT)), w.s([sv], 'adantl', '( ( %s /\\ x = %s ) -> ( exp ` ( W x. x ) ) = ( exp ` ( W x. %s ) ) )' % (X0, p, p)), pr, pv],
                 '( %s ` %s ) = ( exp ` ( W x. %s ) )' % (FT, p, p))
        return d('eqtrd', [r1, r2], '( %s ` %s ) = ( exp ` ( W x. %s ) )' % (F1, p, p)), pv
    ubp = d('syl2anc', [bpr, alb] if False else [ar, bpr], '') if False else None
    ubin = d('mpbird', [d('3jca', [bpr, alb, d('leidd', [bpr], '%s <_ %s' % (BP, BP))], '( %s e. RR /\\ A <_ %s /\\ %s <_ %s )' % (BP, BP, BP, BP)),
                        d('syl2anc', [ar, bpr, w.inst('elicc2')], '( %s e. %s <-> ( %s e. RR /\\ A <_ %s /\\ %s <_ %s ) )' % (BP, I_, BP, BP, BP, BP))], '%s e. %s' % (BP, I_))
    lbin = d('mpbird', [d('3jca', [ar, d('leidd', [ar], 'A <_ A'), alb], '( A e. RR /\\ A <_ A /\\ A <_ %s )' % BP),
                        d('syl2anc', [ar, bpr, w.inst('elicc2')], '( A e. %s <-> ( A e. RR /\\ A <_ A /\\ A <_ %s ) )' % (I_, BP))], 'A e. %s' % I_)
    vB, e1c = endv(BP, ubin, bpr)
    vA, e0c = endv('A', lbin, ar)
    E1 = '( exp ` ( W x. %s ) )' % BP
    E0 = '( exp ` ( W x. A ) )'
    eqW = chain(w, X0, ['( W x. %s )' % IT, 'S. %s ( W x. %s ) _d t' % (O, EWT), 'S. %s ( ( RR _D %s ) ` t ) _d t' % (O, F1),
                        '( ( %s ` %s ) - ( %s ` A ) )' % (F1, BP, F1), '( %s - %s )' % (E1, E0)],
                [imc, ('r', ieq), ftc, d('oveq12d', [vB, vA], '( ( %s ` %s ) - ( %s ` A ) ) = ( %s - %s )' % (F1, BP, F1, E1, E0))])
    Ic = d('itgcl', [eo, ibl], '%s e. CC' % IT)
    AV = AVG('A', 'L', 'W')
    P = PH('L', 'W')
    LHS = '( ( 1 / L ) x. %s )' % IT
    # ---- W = 0
    Xz = '( %s /\\ W = 0 )' % X0
    dz = mk(w, Xz)
    w0 = w.s([], 'simpr', '( %s -> W = 0 )' % Xz)
    Xzo = '( %s /\\ t e. %s )' % (Xz, O)
    dzo = mk(w, Xzo)
    tzr = dzo('sseldd', [a1(w, Xzo, 'ioossre', '%s C_ RR' % O), w.s([], 'simpr', '( %s -> t e. %s )' % (Xzo, O))], 't e. RR')
    wt0 = dzo('eqtrd', [dzo('oveq1d', [lift(w, w0, Xzo)], '( W x. t ) = ( 0 x. t )'), dzo('mul02d', [dzo('recnd', [tzr], 't e. CC')], '( 0 x. t ) = 0')], '( W x. t ) = 0')
    ew1 = dzo('eqtrd', [dzo('fveq2d', [wt0], '%s = ( exp ` 0 )' % EWT), a1(w, Xzo, 'ef0', '( exp ` 0 ) = 1')], '%s = 1' % EWT)
    iz = dz('itgeq2dv', [ew1], '%s = S. %s 1 _d t' % (IT, O))
    vo = dz('3jca', [lift(w, ar, Xz), lift(w, bpr, Xz), lift(w, alb, Xz)], '( A e. RR /\\ %s e. RR /\\ A <_ %s )' % (BP, BP))
    vol = dz('syl', [vo, w.inst('volioo')], '( vol ` %s ) = ( %s - A )' % (O, BP))
    vol2 = dz('eqtrd', [vol, dz('pncan2d', [dz('recnd', [lift(w, ar, Xz)], 'A e. CC'), lift(w, lc, Xz)], '( %s - A ) = L' % BP)], '( vol ` %s ) = L' % O)
    vr = dz('eqeltrd', [vol2, lift(w, lr, Xz)], '( vol ` %s ) e. RR' % O)
    ic = dz('syl3anc', [a1(w, Xz, 'ioombl', '%s e. dom vol' % O), vr, a1(w, Xz, 'ax-1cn', '1 e. CC'), w.inst('itgconst')], 'S. %s 1 _d t = ( 1 x. ( vol ` %s ) )' % (O, O))
    ic2 = dz('eqtrd', [ic, dz('oveq2d', [vol2], '( 1 x. ( vol ` %s ) ) = ( 1 x. L )' % O)], 'S. %s 1 _d t = ( 1 x. L )' % O)
    ic3 = dz('eqtrd', [ic2, dz('mullidd', [lift(w, lc, Xz)], '( 1 x. L ) = L')], 'S. %s 1 _d t = L' % O)
    iL = dz('eqtrd', [iz, ic3], '%s = L' % IT)
    lz = dz('eqtrd', [dz('oveq2d', [iL], '%s = ( ( 1 / L ) x. L )' % LHS), dz('recid2d', [lift(w, lc, Xz), lift(w, ln0, Xz)], '( ( 1 / L ) x. L ) = 1')], '%s = 1' % LHS)
    aw0 = dz('eqtrd', [dz('oveq2d', [w0], '( A x. W ) = ( A x. 0 )'), dz('mul01d', [dz('recnd', [lift(w, ar, Xz)], 'A e. CC')], '( A x. 0 ) = 0')], '( A x. W ) = 0')
    ea1 = dz('eqtrd', [dz('fveq2d', [aw0], '( exp ` ( A x. W ) ) = ( exp ` 0 )'), a1(w, Xz, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( A x. W ) ) = 1')
    pl = dz('iftrued', [w0], '%s = L' % P)
    pl2 = dz('eqtrd', [dz('oveq1d', [pl], '( %s / L ) = ( L / L )' % P), dz('dividd', [lift(w, lc, Xz), lift(w, ln0, Xz)], '( L / L ) = 1')], '( %s / L ) = 1' % P)
    av1 = dz('eqtrd', [dz('oveq12d', [ea1, pl2], '%s = ( 1 x. 1 )' % AV), a1(w, Xz, '1t1e1', '( 1 x. 1 ) = 1')], '%s = 1' % AV)
    bz = dz('eqtr4d', [lz, av1], '%s = %s' % (LHS, AV))
    # ---- W =/= 0
    Xn = '( %s /\\ W =/= 0 )' % X0
    dn = mk(w, Xn)
    wn = w.s([], 'simpr', '( %s -> W =/= 0 )' % Xn)
    L_ = lambda st: lift(w, st, Xn)
    acc = dn('recnd', [L_(ar)], 'A e. CC')
    pv = dn('syl2anc', [L_(lc), L_(wc), w.inst('gf1phv')], split_imp(tsub(S['gf1phv'], {'C': 'L'}))[1])
    pc = dn('simp1d', [pv], '%s e. CC' % P)
    pw = dn('simp2d', [pv], '( %s x. W ) = ( ( exp ` ( L x. W ) ) - 1 )' % P)
    EA = '( exp ` ( A x. W ) )'; EL = '( exp ` ( L x. W ) )'
    eac = dn('efcld', [dn('mulcld', [acc, L_(wc)], '( A x. W ) e. CC')], '%s e. CC' % EA)
    elc = dn('efcld', [dn('mulcld', [L_(lc), L_(wc)], '( L x. W ) e. CC')], '%s e. CC' % EL)
    IL = '( 1 / L )'
    ilc = dn('reccld', [L_(lc), L_(ln0)], '%s e. CC' % IL)
    clr = Closure(w, Xn, {'W': ('CC', L_(wc)), 'L': ('CC', L_(lc)), 'A': ('CC', acc), IL: ('CC', ilc), IT: ('CC', L_(Ic)), EA: ('CC', eac), EL: ('CC', elc), P: ('CC', pc)})
    for a_ in [IL, IT, EA, EL, P]:
        clr.atom(a_)
    # e1 - e0 = eA ( eL - 1 )
    r1 = ringeq(w, Xn, '( W x. %s )' % BP, '( ( A x. W ) + ( L x. W ) )', clr)
    ef1 = dn('eqtrd', [dn('fveq2d', [r1], '%s = ( exp ` ( ( A x. W ) + ( L x. W ) ) )' % E1),
                       dn('efaddd' if False else 'syl2anc', [dn('mulcld', [acc, L_(wc)], '( A x. W ) e. CC'), dn('mulcld', [L_(lc), L_(wc)], '( L x. W ) e. CC'), w.inst('efadd')],
                          '( exp ` ( ( A x. W ) + ( L x. W ) ) ) = ( %s x. %s )' % (EA, EL))], '%s = ( %s x. %s )' % (E1, EA, EL))
    ef0 = dn('fveq2d', [dn('mulcomd', [L_(wc), acc], '( W x. A ) = ( A x. W )')], '%s = %s' % (E0, EA))
    dif = dn('oveq12d', [ef1, ef0], '( %s - %s ) = ( ( %s x. %s ) - %s )' % (E1, E0, EA, EL, EA))
    dif2 = dn('eqtrd', [dif, ringeq(w, Xn, '( ( %s x. %s ) - %s )' % (EA, EL, EA), '( %s x. ( %s - 1 ) )' % (EA, EL), clr)], '( %s - %s ) = ( %s x. ( %s - 1 ) )' % (E1, E0, EA, EL))
    WL = '( W x. L )'
    rec = dn('recidd', [L_(lc), L_(ln0)], '( L x. %s ) = 1' % IL)
    l1 = ringeq(w, Xn, '( %s x. %s )' % (WL, LHS), '( ( L x. %s ) x. ( W x. %s ) )' % (IL, IT), clr)
    l2 = dn('oveq12d', [rec, L_(eqW)], '( ( L x. %s ) x. ( W x. %s ) ) = ( 1 x. ( %s - %s ) )' % (IL, IT, E1, E0))
    l3 = dn('mullidd', [dn('subcld', [L_(e1c), L_(e0c)], '( %s - %s ) e. CC' % (E1, E0))], '( 1 x. ( %s - %s ) ) = ( %s - %s )' % (E1, E0, E1, E0))
    LW = chain(w, Xn, ['( %s x. %s )' % (WL, LHS), '( ( L x. %s ) x. ( W x. %s ) )' % (IL, IT), '( 1 x. ( %s - %s ) )' % (E1, E0), '( %s - %s )' % (E1, E0), '( %s x. ( %s - 1 ) )' % (EA, EL)],
               [l1, l2, l3, dif2])
    RP = '( %s x. ( %s x. %s ) )' % (EA, P, IL)
    q1 = dn('oveq2d', [dn('divrecd', [pc, L_(lc), L_(ln0)], '( %s / L ) = ( %s x. %s )' % (P, P, IL))], '%s = %s' % (AV, RP))
    q2 = dn('oveq2d', [q1], '( %s x. %s ) = ( %s x. %s )' % (WL, AV, WL, RP))
    q3 = ringeq(w, Xn, '( %s x. %s )' % (WL, RP), '( ( L x. %s ) x. ( %s x. ( %s x. W ) ) )' % (IL, EA, P), clr)
    q4 = dn('oveq12d', [rec, dn('oveq2d', [pw], '( %s x. ( %s x. W ) ) = ( %s x. ( %s - 1 ) )' % (EA, P, EA, EL))],
            '( ( L x. %s ) x. ( %s x. ( %s x. W ) ) ) = ( 1 x. ( %s x. ( %s - 1 ) ) )' % (IL, EA, P, EA, EL))
    q5 = dn('mullidd', [dn('mulcld', [eac, dn('subcld', [elc, dn('1cnd', [], '1 e. CC')], '( %s - 1 ) e. CC' % EL)], '( %s x. ( %s - 1 ) ) e. CC' % (EA, EL))],
            '( 1 x. ( %s x. ( %s - 1 ) ) ) = ( %s x. ( %s - 1 ) )' % (EA, EL, EA, EL))
    RW = chain(w, Xn, ['( %s x. %s )' % (WL, AV), '( %s x. %s )' % (WL, RP), '( ( L x. %s ) x. ( %s x. ( %s x. W ) ) )' % (IL, EA, P),
                       '( 1 x. ( %s x. ( %s - 1 ) ) )' % (EA, EL), '( %s x. ( %s - 1 ) )' % (EA, EL)], [q2, q3, q4, q5])
    both = dn('eqtr4d', [LW, RW], '( %s x. %s ) = ( %s x. %s )' % (WL, LHS, WL, AV))
    lhc = dn('mulcld', [ilc, L_(Ic)], '%s e. CC' % LHS)
    avc = dn('mulcld', [eac, dn('divcld', [pc, L_(lc), L_(ln0)], '( %s / L ) e. CC' % P)], '%s e. CC' % AV)
    wlc = dn('mulcld', [L_(wc), L_(lc)], '%s e. CC' % WL)
    wl0 = dn('mulne0d', [L_(wc), L_(lc), wn, L_(ln0)], '%s =/= 0' % WL)
    bn = dn('mpbid', [both, dn('mulcand', [lhc, avc, wlc, wl0], '( ( %s x. %s ) = ( %s x. %s ) <-> %s = %s )' % (WL, LHS, WL, AV, LHS, AV))], '%s = %s' % (LHS, AV))
    ex = a1(w, X0, 'exmidne', '( W = 0 \\/ W =/= 0 )')
    val = d('mpjaodan', [bz, bn, ex], '%s = %s' % (LHS, AV))
    fin = d('jca', [ibl, val], CONC)
    w.qed([fin], 'idi', S['gf1avgi'])
    return run(w, only)


def hol_ph_s(w, A, cst, cc):
    """( A -> HOL( s |-> PH(cst, s) ) ) from cc ( A -> cst e. CC )"""
    PW = '( w e. CC |-> %s )' % PH(cst, 'w')
    PS = '( s e. CC |-> %s )' % PH(cst, 's')
    h = w.s([cc, w.inst('gf1ph')], 'syl', '( %s -> %s )' % (A, HOL(PW, 'CC')))
    cb = w.s([phsub(w, cst, 'w', 's')], 'cbvmptv', '%s = %s' % (PW, PS))
    return D(w, A, 'mpd', [h, holeq(w, A, w.s([cb], 'a1i', '( %s -> %s = %s )' % (A, PW, PS)), PW, PS, 'CC')], HOL(PS, 'CC'))


def hol_phl_s(w, A, L, lc, ln0):
    """( A -> HOL( s |-> ( PH(L, s) / L ) ) )"""
    hp = hol_ph_s(w, A, L, lc)
    il = D(w, A, 'reccld', [lc, ln0], '( 1 / %s ) e. CC' % L)
    hi = D(w, A, 'z6ehc', [il], HOL('( s e. CC |-> ( 1 / %s ) )' % L, 'CC'))
    hm = D(w, A, 'z6ehmul', [hp, hi], HOL('( s e. CC |-> ( %s x. ( 1 / %s ) ) )' % (PH(L, 's'), L), 'CC'))
    As = '( %s /\\ s e. CC )' % A
    pc = D(w, As, 'simp1d', [D(w, As, 'syl2anc', [lift(w, lc, As), w.s([], 'simpr', '( %s -> s e. CC )' % As), w.inst('gf1phv')],
                               split_imp(tsub(S['gf1phv'], {'C': L, 'W': 's'}))[1])], '%s e. CC' % PH(L, 's'))
    dr = D(w, As, 'divrecd', [pc, lift(w, lc, As), lift(w, ln0, As)], '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (PH(L, 's'), L, PH(L, 's'), L))
    eq = D(w, A, 'mpteq2dva', [D(w, As, 'eqcomd', [dr], '( %s x. ( 1 / %s ) ) = ( %s / %s )' % (PH(L, 's'), L, PH(L, 's'), L))],
           '( s e. CC |-> ( %s x. ( 1 / %s ) ) ) = ( s e. CC |-> ( %s / %s ) )' % (PH(L, 's'), L, PH(L, 's'), L))
    hd = D(w, A, 'mpd', [hm, holeq(w, A, eq, '( s e. CC |-> ( %s x. ( 1 / %s ) ) )' % (PH(L, 's'), L), '( s e. CC |-> ( %s / %s ) )' % (PH(L, 's'), L), 'CC')],
           HOL('( s e. CC |-> ( %s / %s ) )' % (PH(L, 's'), L), 'CC'))
    return hd


def hol_avg_s(w, A, a, L, ac, lc, ln0):
    """( A -> HOL( s |-> AVG(a, L, s) ) )"""
    Aa = w.s([ac, w.inst('gf1eh')], 'syl', '( %s -> %s )' % (A, HOL('( s e. CC |-> ( exp ` ( %s x. s ) ) )' % a, 'CC')))
    hd = hol_phl_s(w, A, L, lc, ln0)
    return D(w, A, 'z6ehmul', [Aa, hd], HOL('( s e. CC |-> %s )' % AVG(a, L, 's'), 'CC'))


def avgsub(w, a, L, x, y):
    """( x = y -> AVG(a, L, x) = AVG(a, L, y) )"""
    e1 = w.s([w.s([], 'oveq2', '( %s = %s -> ( %s x. %s ) = ( %s x. %s ) )' % (x, y, a, x, a, y))], 'fveq2d',
             '( %s = %s -> ( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. %s ) ) )' % (x, y, a, x, a, y))
    e2 = w.s([phsub(w, L, x, y)], 'oveq1d', '( %s = %s -> ( %s / %s ) = ( %s / %s ) )' % (x, y, PH(L, x), L, PH(L, y), L))
    return w.s([e1, e2], 'oveq12d', '( %s = %s -> %s = %s )' % (x, y, AVG(a, L, x), AVG(a, L, y)))


def gen_avgh():
    w = W('gf1avgh', '` avgExp ` and ` Kker ` are entire (Lean ` differentiable_avgExp ` , ` differentiable_Kker ` ).')
    X0, CONC = split_imp(S['gf1avgh'])
    d = mk(w, X0)
    ac = d('recnd', [proj(w, X0, 'A e. RR')], 'A e. CC')
    bc = d('recnd', [proj(w, X0, 'B e. RR')], 'B e. CC')
    lp = proj(w, X0, 'L e. RR+')
    lc = d('rpcnd', [lp], 'L e. CC'); ln0 = d('rpne0d', [lp], 'L =/= 0')
    ha = hol_avg_s(w, X0, 'A', 'L', ac, lc, ln0)
    hb = hol_avg_s(w, X0, 'B', 'L', bc, lc, ln0)
    # K = AVG_B + -1 AVG_A
    hm1 = d('z6ehc', [a1(w, X0, 'neg1cn', '-u 1 e. CC')], HOL('( s e. CC |-> -u 1 )', 'CC'))
    hn = d('z6ehmul', [hm1, ha], HOL('( s e. CC |-> ( -u 1 x. %s ) )' % AVG('A', 'L', 's'), 'CC'))
    hs = d('z6ehadd', [hb, hn], HOL('( s e. CC |-> ( %s + ( -u 1 x. %s ) ) )' % (AVG('B', 'L', 's'), AVG('A', 'L', 's')), 'CC'))
    Xs = '( %s /\\ s e. CC )' % X0
    ds = mk(w, Xs)
    sc = w.s([], 'simpr', '( %s -> s e. CC )' % Xs)
    def avc(a, acs):
        pc = ds('simp1d', [ds('syl2anc', [lift(w, lc, Xs), sc, w.inst('gf1phv')], split_imp(tsub(S['gf1phv'], {'C': 'L', 'W': 's'}))[1])], '%s e. CC' % PH('L', 's'))
        return ds('mulcld', [ds('efcld', [ds('mulcld', [lift(w, acs, Xs), sc], '( %s x. s ) e. CC' % a)], '( exp ` ( %s x. s ) ) e. CC' % a),
                             ds('divcld', [pc, lift(w, lc, Xs), lift(w, ln0, Xs)], '( %s / L ) e. CC' % PH('L', 's'))], '%s e. CC' % AVG(a, 'L', 's'))
    va = avc('A', ac); vb = avc('B', bc)
    m1 = ds('mulm1d', [va], '( -u 1 x. %s ) = -u %s' % (AVG('A', 'L', 's'), AVG('A', 'L', 's')))
    e1 = ds('oveq2d', [m1], '( %s + ( -u 1 x. %s ) ) = ( %s + -u %s )' % (AVG('B', 'L', 's'), AVG('A', 'L', 's'), AVG('B', 'L', 's'), AVG('A', 'L', 's')))
    e2 = ds('negsubd', [vb, va], '( %s + -u %s ) = %s' % (AVG('B', 'L', 's'), AVG('A', 'L', 's'), KK('A', 'B', 'L', 's')))
    eK = d('mpteq2dva', [ds('eqtrd', [e1, e2], '( %s + ( -u 1 x. %s ) ) = %s' % (AVG('B', 'L', 's'), AVG('A', 'L', 's'), KK('A', 'B', 'L', 's')))],
           '( s e. CC |-> ( %s + ( -u 1 x. %s ) ) ) = ( s e. CC |-> %s )' % (AVG('B', 'L', 's'), AVG('A', 'L', 's'), KK('A', 'B', 'L', 's')))
    KS = '( s e. CC |-> %s )' % KK('A', 'B', 'L', 's')
    hK = d('mpd', [hs, holeq(w, X0, eK, '( s e. CC |-> ( %s + ( -u 1 x. %s ) ) )' % (AVG('B', 'L', 's'), AVG('A', 'L', 's')), KS, 'CC')], HOL(KS, 'CC'))
    # rename s to w
    AS = '( s e. CC |-> %s )' % AVG('A', 'L', 's'); AW = '( w e. CC |-> %s )' % AVG('A', 'L', 'w')
    cba = w.s([avgsub(w, 'A', 'L', 's', 'w')], 'cbvmptv', '%s = %s' % (AS, AW))
    ha2 = d('mpd', [ha, holeq(w, X0, w.s([cba], 'a1i', '( %s -> %s = %s )' % (X0, AS, AW)), AS, AW, 'CC')], HOL(AW, 'CC'))
    KW = '( w e. CC |-> %s )' % KK('A', 'B', 'L', 'w')
    ksub = w.s([avgsub(w, 'B', 'L', 's', 'w'), avgsub(w, 'A', 'L', 's', 'w')], 'oveq12d', '( s = w -> %s = %s )' % (KK('A', 'B', 'L', 's'), KK('A', 'B', 'L', 'w')))
    cbk = w.s([ksub], 'cbvmptv', '%s = %s' % (KS, KW))
    hK2 = d('mpd', [hK, holeq(w, X0, w.s([cbk], 'a1i', '( %s -> %s = %s )' % (X0, KS, KW)), KS, KW, 'CC')], HOL(KW, 'CC'))
    fin = d('jca', [ha2, hK2], CONC)
    w.qed([fin], 'idi', S['gf1avgh'])
    return run(w, only)


def avgabs(w, X, a, ar, lp, wc):
    """facts on AVG(a, L, W) under X: |AVG| = exp ( a Re W ) ( |PH| / L ) and the pieces"""
    d = mk(w, X)
    lr = d('rpred', [lp], 'L e. RR'); lc = d('rpcnd', [lp], 'L e. CC'); ln0 = d('rpne0d', [lp], 'L =/= 0')
    ac = d('recnd', [ar], '%s e. CC' % a)
    P = PH('L', 'W')
    pv = d('syl2anc', [lc, wc, w.inst('gf1phv')], split_imp(tsub(S['gf1phv'], {'C': 'L'}))[1])
    pc = d('simp1d', [pv], '%s e. CC' % P)
    aw = d('mulcld', [ac, wc], '( %s x. W ) e. CC' % a)
    eaw = d('efcld', [aw], '( exp ` ( %s x. W ) ) e. CC' % a)
    pl = d('divcld', [pc, lc, ln0], '( %s / L ) e. CC' % P)
    avc = d('mulcld', [eaw, pl], '%s e. CC' % AVG(a, 'L', 'W'))
    e1 = d('absmuld', [eaw, pl], '( abs ` %s ) = ( ( abs ` ( exp ` ( %s x. W ) ) ) x. ( abs ` ( %s / L ) ) )' % (AVG(a, 'L', 'W'), a, P))
    e2 = d('syl', [aw, w.inst('absef')], '( abs ` ( exp ` ( %s x. W ) ) ) = ( exp ` ( Re ` ( %s x. W ) ) )' % (a, a))
    e3 = d('syl2anc', [ar, wc, w.inst('remul2')], '( Re ` ( %s x. W ) ) = ( %s x. ( Re ` W ) )' % (a, a))
    e4 = d('eqtrd', [e2, d('fveq2d', [e3], '( exp ` ( Re ` ( %s x. W ) ) ) = ( exp ` ( %s x. ( Re ` W ) ) )' % (a, a))], '( abs ` ( exp ` ( %s x. W ) ) ) = ( exp ` ( %s x. ( Re ` W ) ) )' % (a, a))
    e5 = d('absdivd', [pc, lc, ln0], '( abs ` ( %s / L ) ) = ( ( abs ` %s ) / ( abs ` L ) )' % (P, P))
    e6 = d('eqtrd', [e5, d('oveq2d', [d('absidd', [lr, d('rpge0d', [lp], '0 <_ L')], '( abs ` L ) = L')], '( ( abs ` %s ) / ( abs ` L ) ) = ( ( abs ` %s ) / L )' % (P, P))],
           '( abs ` ( %s / L ) ) = ( ( abs ` %s ) / L )' % (P, P))
    EX = '( exp ` ( %s x. ( Re ` W ) ) )' % a
    Q = '( ( abs ` %s ) / L )' % P
    eq = d('eqtrd', [e1, d('oveq12d', [e4, e6], '( ( abs ` ( exp ` ( %s x. W ) ) ) x. ( abs ` ( %s / L ) ) ) = ( %s x. %s )' % (a, P, EX, Q))],
           '( abs ` %s ) = ( %s x. %s )' % (AVG(a, 'L', 'W'), EX, Q))
    rw = d('recld', [wc], '( Re ` W ) e. RR')
    exr = d('reefcld', [d('remulcld', [ar, rw], '( %s x. ( Re ` W ) ) e. RR' % a)], '%s e. RR' % EX)
    ex0 = d('ltled', [a1(w, X, '0re', '0 e. RR'), exr, d('syl', [d('remulcld', [ar, rw], '( %s x. ( Re ` W ) ) e. RR' % a), w.inst('efgt0')], '0 < %s' % EX)], '0 <_ %s' % EX)
    par = d('abscld', [pc], '( abs ` %s ) e. RR' % P)
    qr = d('redivcld', [par, lr, ln0], '%s e. RR' % Q)
    q0 = d('divge0d', [par, lp, d('absge0d', [pc], '0 <_ ( abs ` %s )' % P)], '0 <_ %s' % Q)
    return dict(eq=eq, EX=EX, Q=Q, exr=exr, ex0=ex0, qr=qr, q0=q0, par=par, pc=pc, avc=avc, lr=lr, lc=lc, ln0=ln0, rw=rw, ac=ac, eaw=eaw, pl=pl)


def phb(w, X, C, cr, c0, wc):
    """the gf1phb conjunction for PH(C, W) under X"""
    return D(w, X, 'syl', [D(w, X, 'jca', [D(w, X, 'jca', [cr, c0], '( %s e. RR /\\ 0 <_ %s )' % (C, C)), wc], '( ( %s e. RR /\\ 0 <_ %s ) /\\ W e. CC )' % (C, C)), w.inst('gf1phb')],
             split_imp(tsub(S['gf1phb'], {'C': C}))[1])


def gen_avgb():
    w = W('gf1avgb', 'Bounds on ` avgExp ` : ` abs avgExp ( A , L , W ) <_ exp ( A Re W ) ` on ` Re W <_ 0 ` , ` <_ exp ( A + L ) ` on ` Re W <_ 1 ` (Lean ` norm_avgExp_le_of_re_nonpos ` , ` norm_avgExp_le_of_re_le_one ` ).')
    X0, CONC = split_imp(S['gf1avgb'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); a0 = proj(w, X0, '0 <_ A'); lp = proj(w, X0, 'L e. RR+'); wc = proj(w, X0, 'W e. CC')
    P = PH('L', 'W'); AV = AVG('A', 'L', 'W')
    f = avgabs(w, X0, 'A', ar, lp, wc)
    pb = phb(w, X0, 'L', f['lr'], d('rpge0d', [lp], '0 <_ L'), wc)
    # (1)
    X1 = '( %s /\\ ( Re ` W ) <_ 0 )' % X0
    d1 = mk(w, X1); L1 = lambda st: lift(w, st, X1)
    pL = d1('mpd', [w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 0 )' % X1), L1(d('simp1d', [pb], '( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ L )' % P))], '( abs ` %s ) <_ L' % P)
    q1 = d1('mpbird', [pL, d1('syl2anc', [L1(f['par']), L1(lp), w.inst('divle1le')], '( %s <_ 1 <-> ( abs ` %s ) <_ L )' % (f['Q'], P))], '%s <_ 1' % f['Q'])
    cl1 = Closure(w, X1, {f['EX']: L1(f['exr']), f['Q']: L1(f['qr'])})
    cl1.atom(f['EX']); cl1.atom(f['Q'])
    b1 = lin.nlinarith(w, X1, [q1, L1(f['ex0'])], '( %s x. %s ) <_ %s' % (f['EX'], f['Q'], f['EX']), closure=cl1)
    r1 = d1('eqbrtrd', [L1(f['eq']), b1], '( abs ` %s ) <_ %s' % (AV, f['EX']))
    # (2)
    X2 = '( %s /\\ ( Re ` W ) <_ 1 )' % X0
    d2 = mk(w, X2); L2 = lambda st: lift(w, st, X2)
    EL = '( exp ` L )'
    pL2 = d2('mpd', [w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 1 )' % X2), L2(d('simp2d', [pb], '( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( L x. %s ) )' % (P, EL)))],
             '( abs ` %s ) <_ ( L x. %s )' % (P, EL))
    elr = d2('reefcld', [L2(f['lr'])], '%s e. RR' % EL)
    q2 = d2('mpbird', [pL2, d2('ledivmuld', [L2(f['par']), elr, L2(lp)], '( %s <_ %s <-> ( abs ` %s ) <_ ( L x. %s ) )' % (f['Q'], EL, P, EL))], '%s <_ %s' % (f['Q'], EL))
    EA = '( exp ` A )'
    ear = d2('reefcld', [L2(ar)], '%s e. RR' % EA)
    arw = d2('remulcld', [L2(ar), L2(f['rw'])], '( A x. ( Re ` W ) ) e. RR')
    cla = Closure(w, X2, {'A': L2(ar), '( Re ` W )': L2(f['rw'])})
    le_a = lin.nlinarith(w, X2, [L2(a0), w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 1 )' % X2)], '( A x. ( Re ` W ) ) <_ A', closure=cla)
    eb = d2('mpbid', [le_a, d2('syl2anc', [arw, L2(ar), w.inst('efle')], '( ( A x. ( Re ` W ) ) <_ A <-> %s <_ %s )' % (f['EX'], EA))], '%s <_ %s' % (f['EX'], EA))
    mm = d2('lemul12ad', [L2(f['exr']), ear, L2(f['qr']), elr, L2(f['ex0']), eb, L2(f['q0']), q2], '( %s x. %s ) <_ ( %s x. %s )' % (f['EX'], f['Q'], EA, EL))
    efa = d2('syl2anc', [d2('recnd', [L2(ar)], 'A e. CC'), d2('recnd', [L2(f['lr'])], 'L e. CC'), w.inst('efadd')], '( exp ` ( A + L ) ) = ( %s x. %s )' % (EA, EL))
    r2 = chain(w, X2, ['( abs ` %s )' % AV, '( %s x. %s )' % (f['EX'], f['Q']), '( %s x. %s )' % (EA, EL), '( exp ` ( A + L ) )'],
               [L2(f['eq']), mm, d2('eqcomd', [efa], '( %s x. %s ) = ( exp ` ( A + L ) )' % (EA, EL))], ['=', '<_', '='])
    fin = d('jca', [w.s([r1], 'ex', '( %s -> ( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ %s ) )' % (X0, AV, f['EX'])),
                    w.s([r2], 'ex', '( %s -> ( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( exp ` ( A + L ) ) ) )' % (X0, AV))], CONC)
    w.qed([fin], 'idi', S['gf1avgb'])
    return run(w, only)


def gen_kq():
    w = W('gf1kq', '` Kker ( W ) = W KQ ( W ) ` for every ` W ` , with ` KQ = ( PH ( L , W ) / L ) exp ( A W ) PH ( B - A , W ) ` (Lean ` dslope_Kker_of_ne ` , ` Kker_zero ` ).')
    X0, CONC = split_imp(S['gf1kq'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); lp = proj(w, X0, 'L e. RR+'); wc = proj(w, X0, 'W e. CC')
    ac = d('recnd', [ar], 'A e. CC'); bc = d('recnd', [br], 'B e. CC')
    lc = d('rpcnd', [lp], 'L e. CC'); ln0 = d('rpne0d', [lp], 'L =/= 0')
    BA = '( B - A )'
    bac = d('subcld', [bc, ac], '%s e. CC' % BA)
    P = PH('L', 'W'); Dp = PH(BA, 'W')
    pv = d('syl2anc', [lc, wc, w.inst('gf1phv')], split_imp(tsub(S['gf1phv'], {'C': 'L'}))[1])
    pc = d('simp1d', [pv], '%s e. CC' % P)
    dv = d('syl2anc', [bac, wc, w.inst('gf1phv')], split_imp(tsub(S['gf1phv'], {'C': BA}))[1])
    dc = d('simp1d', [dv], '%s e. CC' % Dp)
    dw = d('simp2d', [dv], '( %s x. W ) = ( ( exp ` ( %s x. W ) ) - 1 )' % (Dp, BA))
    Q = '( %s / L )' % P
    qc = d('divcld', [pc, lc, ln0], '%s e. CC' % Q)
    EA = '( exp ` ( A x. W ) )'; EB = '( exp ` ( B x. W ) )'; EBA = '( exp ` ( %s x. W ) )' % BA
    awc = d('mulcld', [ac, wc], '( A x. W ) e. CC'); bawc = d('mulcld', [bac, wc], '( %s x. W ) e. CC' % BA)
    eac = d('efcld', [awc], '%s e. CC' % EA); ebac = d('efcld', [bawc], '%s e. CC' % EBA)
    KQv = KQ('A', 'B', 'L', 'W')
    kqc = d('mulcld', [qc, d('mulcld', [eac, dc], '( %s x. %s ) e. CC' % (EA, Dp))], '%s e. CC' % KQv)
    cl = Closure(w, X0, {'W': ('CC', wc), 'A': ('CC', ac), 'B': ('CC', bc), Q: ('CC', qc), EA: ('CC', eac), EBA: ('CC', ebac), Dp: ('CC', dc)})
    for a_ in [Q, EA, EBA, Dp]:
        cl.atom(a_)
    ex1 = ringeq(w, X0, '( ( A x. W ) + ( %s x. W ) )' % BA, '( B x. W )', cl)
    efa = d('syl2anc', [awc, bawc, w.inst('efadd')], '( exp ` ( ( A x. W ) + ( %s x. W ) ) ) = ( %s x. %s )' % (BA, EA, EBA))
    eb = d('eqtr3d', [efa, d('fveq2d', [ex1], '( exp ` ( ( A x. W ) + ( %s x. W ) ) ) = %s' % (BA, EB))], '( %s x. %s ) = %s' % (EA, EBA, EB))
    t1 = '( W x. %s )' % KQv
    t2 = '( %s x. ( %s x. ( %s x. W ) ) )' % (Q, EA, Dp)
    t3 = '( %s x. ( %s x. ( %s - 1 ) ) )' % (Q, EA, EBA)
    t4 = '( ( ( %s x. %s ) x. %s ) - ( %s x. %s ) )' % (EA, EBA, Q, EA, Q)
    t5 = '( ( %s x. %s ) - ( %s x. %s ) )' % (EB, Q, EA, Q)
    s1 = ringeq(w, X0, t1, t2, cl)
    s2 = d('oveq2d', [d('oveq2d', [dw], '( %s x. ( %s x. W ) ) = ( %s x. ( %s - 1 ) )' % (EA, Dp, EA, EBA))], '%s = %s' % (t2, t3))
    s3 = ringeq(w, X0, t3, t4, cl)
    s4 = d('oveq1d', [d('oveq1d', [eb], '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (EA, EBA, Q, EB, Q))], '%s = %s' % (t4, t5))
    ch = chain(w, X0, [t1, t2, t3, t4, t5], [s1, s2, s3, s4])
    Kv = KK('A', 'B', 'L', 'W')
    assert t5 == Kv, (t5, Kv)
    fin = d('jca', [kqc, d('eqcomd', [ch], '%s = %s' % (Kv, t1))], CONC)
    w.qed([fin], 'idi', S['gf1kq'])
    return run(w, only)


def gen_kqb():
    w = W('gf1kqb', '` abs KQ ( W ) <_ B - A ` on ` Re W <_ 0 ` for ` 0 <_ A <_ B ` (Lean ` norm_dslope_Kker_le ` , sharpened: ` B - A <_ log X + log M0 + 2 L ` ).')
    X0, CONC = split_imp(S['gf1kqb'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); a0 = proj(w, X0, '0 <_ A'); ab = proj(w, X0, 'A <_ B')
    lp = proj(w, X0, 'L e. RR+'); wc = proj(w, X0, 'W e. CC'); rw0 = proj(w, X0, '( Re ` W ) <_ 0')
    f = avgabs(w, X0, 'A', ar, lp, wc)
    P = PH('L', 'W'); BA = '( B - A )'; Dp = PH(BA, 'W')
    bar = d('resubcld', [br, ar], '%s e. RR' % BA)
    ba0 = d('subge0d', [br, ar], '( 0 <_ %s <-> A <_ B )' % BA)
    ba0 = d('mpbird', [ab, ba0], '0 <_ %s' % BA)
    pbL = phb(w, X0, 'L', f['lr'], d('rpge0d', [lp], '0 <_ L'), wc)
    pbD = phb(w, X0, BA, bar, ba0, wc)
    pL = d('mpd', [rw0, d('simp1d', [pbL], '( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ L )' % P)], '( abs ` %s ) <_ L' % P)
    dD = d('mpd', [rw0, d('simp1d', [pbD], '( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ %s )' % (Dp, BA))], '( abs ` %s ) <_ %s' % (Dp, BA))
    Q = '( %s / L )' % P
    aq = d('eqtrd', [d('absdivd', [f['pc'], f['lc'], f['ln0']], '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` L ) )' % (Q, P)),
                     d('oveq2d', [d('absidd', [f['lr'], d('rpge0d', [lp], '0 <_ L')], '( abs ` L ) = L')], '( ( abs ` %s ) / ( abs ` L ) ) = ( ( abs ` %s ) / L )' % (P, P))],
           '( abs ` %s ) = ( ( abs ` %s ) / L )' % (Q, P))
    q1 = d('mpbird', [pL, d('syl2anc', [f['par'], lp, w.inst('divle1le')], '( ( ( abs ` %s ) / L ) <_ 1 <-> ( abs ` %s ) <_ L )' % (P, P))], '( ( abs ` %s ) / L ) <_ 1' % P)
    aq1 = d('eqbrtrd', [aq, q1], '( abs ` %s ) <_ 1' % Q)
    EA = '( exp ` ( A x. W ) )'
    ae = d('syl', [f['aw'] if 'aw' in f else d('mulcld', [f['ac'], wc], '( A x. W ) e. CC'), w.inst('absef')], '( abs ` %s ) = ( exp ` ( Re ` ( A x. W ) ) )' % EA)
    ae2 = d('eqtrd', [ae, d('fveq2d', [d('syl2anc', [ar, wc, w.inst('remul2')], '( Re ` ( A x. W ) ) = ( A x. ( Re ` W ) )')], '( exp ` ( Re ` ( A x. W ) ) ) = %s' % f['EX'])],
            '( abs ` %s ) = %s' % (EA, f['EX']))
    cla = Closure(w, X0, {'A': ar, '( Re ` W )': f['rw']})
    arw = lin.nlinarith(w, X0, [a0, rw0], '( A x. ( Re ` W ) ) <_ 0', closure=cla)
    ex1 = d('mpbid', [arw, d('syl2anc', [d('remulcld', [ar, f['rw']], '( A x. ( Re ` W ) ) e. RR'), a1(w, X0, '0re', '0 e. RR'), w.inst('efle')],
                                  '( ( A x. ( Re ` W ) ) <_ 0 <-> %s <_ ( exp ` 0 ) )' % f['EX'])], '%s <_ ( exp ` 0 )' % f['EX'])
    ex2 = d('breqtrd', [ex1, a1(w, X0, 'ef0', '( exp ` 0 ) = 1')], '%s <_ 1' % f['EX'])
    ae1 = d('eqbrtrd', [ae2, ex2], '( abs ` %s ) <_ 1' % EA)
    dc = d('simp1d', [d('syl2anc', [d('recnd', [bar], '%s e. CC' % BA), wc, w.inst('gf1phv')], split_imp(tsub(S['gf1phv'], {'C': BA}))[1])], '%s e. CC' % Dp)
    aqr = d('abscld', [f['pl']], '( abs ` %s ) e. RR' % Q); aq0 = d('absge0d', [f['pl']], '0 <_ ( abs ` %s )' % Q)
    aer = d('abscld', [f['eaw']], '( abs ` %s ) e. RR' % EA); ae0 = d('absge0d', [f['eaw']], '0 <_ ( abs ` %s )' % EA)
    adr = d('abscld', [dc], '( abs ` %s ) e. RR' % Dp); ad0 = d('absge0d', [dc], '0 <_ ( abs ` %s )' % Dp)
    one = a1(w, X0, '1re', '1 e. RR')
    m1 = d('lemul12ad', [aer, one, adr, bar, ae0, ae1, ad0, dD], '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( 1 x. %s )' % (EA, Dp, BA))
    edr = d('remulcld', [aer, adr], '( ( abs ` %s ) x. ( abs ` %s ) ) e. RR' % (EA, Dp))
    ed0 = d('mulge0d', [aer, adr, ae0, ad0], '0 <_ ( ( abs ` %s ) x. ( abs ` %s ) )' % (EA, Dp))
    m2 = d('lemul12ad', [aqr, one, edr, d('remulcld', [one, bar], '( 1 x. %s ) e. RR' % BA), aq0, aq1, ed0, m1],
           '( ( abs ` %s ) x. ( ( abs ` %s ) x. ( abs ` %s ) ) ) <_ ( 1 x. ( 1 x. %s ) )' % (Q, EA, Dp, BA))
    KQv = KQ('A', 'B', 'L', 'W')
    e1 = d('absmuld', [f['pl'], d('mulcld', [f['eaw'], dc], '( %s x. %s ) e. CC' % (EA, Dp))], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (KQv, Q, EA, Dp))
    e2 = d('oveq2d', [d('absmuld', [f['eaw'], dc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (EA, Dp, EA, Dp))],
           '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) ) = ( ( abs ` %s ) x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Q, EA, Dp, Q, EA, Dp))
    bac = d('recnd', [bar], '%s e. CC' % BA)
    e3 = d('eqtrd', [d('mullidd', [d('mulcld', [a1(w, X0, 'ax-1cn', '1 e. CC'), bac], '( 1 x. %s ) e. CC' % BA)], '( 1 x. ( 1 x. %s ) ) = ( 1 x. %s )' % (BA, BA)),
                     d('mullidd', [bac], '( 1 x. %s ) = %s' % (BA, BA))], '( 1 x. ( 1 x. %s ) ) = %s' % (BA, BA))
    fin = chain(w, X0, ['( abs ` %s )' % KQv, '( ( abs ` %s ) x. ( abs ` ( %s x. %s ) ) )' % (Q, EA, Dp), '( ( abs ` %s ) x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Q, EA, Dp),
                        '( 1 x. ( 1 x. %s ) )' % BA, BA], [e1, e2, m2, e3], ['=', '=', '<_', '='])
    w.qed([fin], 'idi', S['gf1kqb'])
    return run(w, only)


def gen_kb():
    w = W('gf1kb', 'Bounds on ` Kker ` : (K1prime) ` abs Kker <_ exp ( B Re W ) + exp ( A Re W ) ` , (K1) ` <_ 2 ` , (K2) ` abs Kker L abs W <_ 4 ` on ` Re W <_ 0 ` ; (K4) ` <_ exp ( B + L ) + exp ( A + L ) ` on ` Re W <_ 1 ` (Lean ` norm_Kker_le_of_re_nonpos ` , ` norm_Kker_le_two ` , ` norm_Kker_le_div ` , ` norm_Kker_le_of_re_le_one ` ).')
    X0, CONC = split_imp(S['gf1kb'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); a0 = proj(w, X0, '0 <_ A'); b0 = proj(w, X0, '0 <_ B')
    lp = proj(w, X0, 'L e. RR+'); wc = proj(w, X0, 'W e. CC')
    fa = avgabs(w, X0, 'A', ar, lp, wc)
    fb = avgabs(w, X0, 'B', br, lp, wc)
    AVA = AVG('A', 'L', 'W'); AVB = AVG('B', 'L', 'W'); Kv = KK('A', 'B', 'L', 'W')
    def avb(a, ar_, a0_):
        return d('syl', [d('3jca', [d('jca', [ar_, a0_], '( %s e. RR /\\ 0 <_ %s )' % (a, a)), lp, wc], '( ( %s e. RR /\\ 0 <_ %s ) /\\ L e. RR+ /\\ W e. CC )' % (a, a)), w.inst('gf1avgb')],
                 split_imp(tsub(S['gf1avgb'], {'A': a}))[1])
    ba = avb('A', ar, a0); bb = avb('B', br, b0)
    tri = d('syl2anc', [fb['avc'], fa['avc'], w.inst('abs2dif2')], '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (Kv, AVB, AVA))
    kr = d('abscld', [d('subcld', [fb['avc'], fa['avc']], '%s e. CC' % Kv)], '( abs ` %s ) e. RR' % Kv)
    aar = d('abscld', [fa['avc']], '( abs ` %s ) e. RR' % AVA); abr = d('abscld', [fb['avc']], '( abs ` %s ) e. RR' % AVB)
    # ---- Re W <_ 0
    X1 = '( %s /\\ ( Re ` W ) <_ 0 )' % X0
    d1 = mk(w, X1); L1 = lambda st: lift(w, st, X1)
    r0 = w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 0 )' % X1)
    EXA = fa['EX']; EXB = fb['EX']
    uA = d1('mpd', [r0, L1(d('simpld', [ba], '( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ %s )' % (AVA, EXA)))], '( abs ` %s ) <_ %s' % (AVA, EXA))
    uB = d1('mpd', [r0, L1(d('simpld', [bb], '( ( Re ` W ) <_ 0 -> ( abs ` %s ) <_ %s )' % (AVB, EXB)))], '( abs ` %s ) <_ %s' % (AVB, EXB))
    clk = Closure(w, X1, {})
    for E_, st in [('( abs ` %s )' % Kv, kr), ('( abs ` %s )' % AVA, aar), ('( abs ` %s )' % AVB, abr), (EXA, fa['exr']), (EXB, fb['exr'])]:
        clk.leaf(E_, 'RR', L1(st))
    ka = lin.linarith(w, X1, [L1(tri), uA, uB], '( abs ` %s ) <_ ( %s + %s )' % (Kv, EXB, EXA), closure=clk)
    def le1(a, ar_, a0_, EX):
        cl_ = Closure(w, X1, {a: L1(ar_), '( Re ` W )': L1(fa['rw'])})
        t = lin.nlinarith(w, X1, [L1(a0_), r0], '( %s x. ( Re ` W ) ) <_ 0' % a, closure=cl_)
        e = d1('mpbid', [t, d1('syl2anc', [d1('remulcld', [L1(ar_), L1(fa['rw'])], '( %s x. ( Re ` W ) ) e. RR' % a), a1(w, X1, '0re', '0 e. RR'), w.inst('efle')],
                                  '( ( %s x. ( Re ` W ) ) <_ 0 <-> %s <_ ( exp ` 0 ) )' % (a, EX))], '%s <_ ( exp ` 0 )' % EX)
        return d1('breqtrd', [e, a1(w, X1, 'ef0', '( exp ` 0 ) = 1')], '%s <_ 1' % EX)
    eA1 = le1('A', ar, a0, EXA); eB1 = le1('B', br, b0, EXB)
    k2 = lin.linarith(w, X1, [ka, eA1, eB1], '( abs ` %s ) <_ 2' % Kv, closure=clk)
    # K2
    P = PH('L', 'W')
    LW = '( L x. ( abs ` W ) )'
    Xz = '( %s /\\ W = 0 )' % X1
    dz = mk(w, Xz)
    az = dz('eqtrd', [dz('fveq2d', [w.s([], 'simpr', '( %s -> W = 0 )' % Xz)], '( abs ` W ) = ( abs ` 0 )'), a1(w, Xz, 'abs0', '( abs ` 0 ) = 0')], '( abs ` W ) = 0')
    lz = dz('eqtrd', [dz('oveq2d', [az], '%s = ( L x. 0 )' % LW), dz('mul01d', [lift(w, fa['lc'], Xz)], '( L x. 0 ) = 0')], '%s = 0' % LW)
    kz = dz('eqtrd', [dz('oveq2d', [lz], '( ( abs ` %s ) x. %s ) = ( ( abs ` %s ) x. 0 )' % (Kv, LW, Kv)), dz('mul01d', [dz('recnd', [lift(w, kr, Xz)], '( abs ` %s ) e. CC' % Kv)], '( ( abs ` %s ) x. 0 ) = 0' % Kv)],
                      '( ( abs ` %s ) x. %s ) = 0' % (Kv, LW))
    k4z = dz('eqbrtrd', [kz, a1(w, Xz, '0le4' if False else 'ax-mp', '0 <_ 4', [w.s([], '4re', '4 e. RR'), w.s([], '4pos', '0 < 4')] if False else []) if False else dz('ltled', [a1(w, Xz, '0re', '0 e. RR'), a1(w, Xz, '4re', '4 e. RR'), a1(w, Xz, '4pos', '0 < 4')], '0 <_ 4')],
                 '( ( abs ` %s ) x. %s ) <_ 4' % (Kv, LW))
    Xn = '( %s /\\ W =/= 0 )' % X1
    dn = mk(w, Xn); Ln = lambda st: lift(w, st, Xn)
    pbL = phb(w, Xn, 'L', Ln(fa['lr']), dn('rpge0d', [Ln(lp)], '0 <_ L'), Ln(wc))
    pw2 = dn('mpd', [dn('jca', [lift(w, r0, Xn), w.s([], 'simpr', '( %s -> W =/= 0 )' % Xn)], '( ( Re ` W ) <_ 0 /\\ W =/= 0 )'),
                     dn('simp3d', [pbL], '( ( ( Re ` W ) <_ 0 /\\ W =/= 0 ) -> ( ( abs ` %s ) x. ( abs ` W ) ) <_ 2 )' % P)], '( ( abs ` %s ) x. ( abs ` W ) ) <_ 2' % P)
    awr = dn('abscld', [Ln(wc)], '( abs ` W ) e. RR'); aw0 = dn('absge0d', [Ln(wc)], '0 <_ ( abs ` W )')
    qL = lambda f: dn('divcan1d', [dn('recnd', [Ln(f['par'])], '( abs ` %s ) e. CC' % P), Ln(fa['lc']), Ln(fa['ln0'])], '( ( ( abs ` %s ) / L ) x. L ) = ( abs ` %s )' % (P, P))
    def piece(f, a):
        """( ( abs AVG ) x. LW ) <_ 2"""
        AV = AVG(a, 'L', 'W')
        EX = f['EX']; Q = f['Q']
        clr = Closure(w, Xn, {EX: ('CC', dn('recnd', [Ln(f['exr'])], '%s e. CC' % EX)), Q: ('CC', dn('recnd', [Ln(f['qr'])], '%s e. CC' % Q)),
                              'L': ('CC', Ln(fa['lc'])), '( abs ` W )': ('CC', dn('recnd', [awr], '( abs ` W ) e. CC'))})
        for a_ in [EX, Q, '( abs ` W )']:
            clr.atom(a_)
        r1 = dn('oveq1d', [Ln(f['eq'])], '( ( abs ` %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (AV, LW, EX, Q, LW))
        r2 = ringeq(w, Xn, '( ( %s x. %s ) x. %s )' % (EX, Q, LW), '( %s x. ( ( %s x. L ) x. ( abs ` W ) ) )' % (EX, Q), clr)
        r3 = dn('oveq2d', [dn('oveq1d', [qL(f)], '( ( %s x. L ) x. ( abs ` W ) ) = ( ( abs ` %s ) x. ( abs ` W ) )' % (Q, P))],
                '( %s x. ( ( %s x. L ) x. ( abs ` W ) ) ) = ( %s x. ( ( abs ` %s ) x. ( abs ` W ) ) )' % (EX, Q, EX, P))
        pwr = dn('remulcld', [Ln(f['par']), awr], '( ( abs ` %s ) x. ( abs ` W ) ) e. RR' % P)
        pw0 = dn('mulge0d', [Ln(f['par']), awr, dn('absge0d', [Ln(f['pc'])], '0 <_ ( abs ` %s )' % P), aw0], '0 <_ ( ( abs ` %s ) x. ( abs ` W ) )' % P)
        e1 = eA1 if a == 'A' else eB1
        m = dn('lemul12ad', [Ln(f['exr']), a1(w, Xn, '1re', '1 e. RR'), pwr, a1(w, Xn, '2re', '2 e. RR'), Ln(f['ex0']), lift(w, e1, Xn), pw0, pw2],
               '( %s x. ( ( abs ` %s ) x. ( abs ` W ) ) ) <_ ( 1 x. 2 )' % (EX, P))
        m2 = dn('breqtrd', [m, a1(w, Xn, '2t1e2' if False else 'mullidi', '( 1 x. 2 ) = 2', [w.s([], '2cn', '2 e. CC')])], '( %s x. ( ( abs ` %s ) x. ( abs ` W ) ) ) <_ 2' % (EX, P))
        return chain(w, Xn, ['( ( abs ` %s ) x. %s )' % (AV, LW), '( ( %s x. %s ) x. %s )' % (EX, Q, LW), '( %s x. ( ( %s x. L ) x. ( abs ` W ) ) )' % (EX, Q),
                             '( %s x. ( ( abs ` %s ) x. ( abs ` W ) ) )' % (EX, P), '2'], [r1, r2, r3, m2], ['=', '=', '=', '<_'])
    pA = piece(fa, 'A'); pB = piece(fb, 'B')
    lwr = dn('remulcld', [Ln(fa['lr']), awr], '%s e. RR' % LW)
    lw0 = dn('mulge0d', [Ln(fa['lr']), awr, dn('rpge0d', [Ln(lp)], '0 <_ L'), aw0], '0 <_ %s' % LW)
    kt = dn('lemul1ad', [Ln(kr), dn('readdcld', [Ln(abr), Ln(aar)], '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (AVB, AVA)), lwr, lw0, Ln(tri)],
            '( ( abs ` %s ) x. %s ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) x. %s )' % (Kv, LW, AVB, AVA, LW))
    cln = Closure(w, Xn, {'( abs ` %s )' % AVA: Ln(aar), '( abs ` %s )' % AVB: Ln(abr), LW: lwr, '( abs ` %s )' % Kv: Ln(kr)})
    for a_ in ['( abs ` %s )' % AVA, '( abs ` %s )' % AVB, LW, '( abs ` %s )' % Kv]:
        cln.atom(a_)
    k4n = lin.nlinarith(w, Xn, [kt, pA, pB], '( ( abs ` %s ) x. %s ) <_ 4' % (Kv, LW), closure=cln)
    k4 = d1('mpjaodan', [k4z, k4n, a1(w, X1, 'exmidne', '( W = 0 \\/ W =/= 0 )')], '( ( abs ` %s ) x. %s ) <_ 4' % (Kv, LW))
    c1 = d1('3jca', [ka, k2, k4], '( ( abs ` %s ) <_ ( %s + %s ) /\\ ( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. %s ) <_ 4 )' % (Kv, EXB, EXA, Kv, Kv, LW))
    # ---- Re W <_ 1
    X2 = '( %s /\\ ( Re ` W ) <_ 1 )' % X0
    d2 = mk(w, X2); L2 = lambda st: lift(w, st, X2)
    r1_ = w.s([], 'simpr', '( %s -> ( Re ` W ) <_ 1 )' % X2)
    vA = d2('mpd', [r1_, L2(d('simprd', [ba], '( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( exp ` ( A + L ) ) )' % AVA))], '( abs ` %s ) <_ ( exp ` ( A + L ) )' % AVA)
    vB = d2('mpd', [r1_, L2(d('simprd', [bb], '( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( exp ` ( B + L ) ) )' % AVB))], '( abs ` %s ) <_ ( exp ` ( B + L ) )' % AVB)
    cl2 = Closure(w, X2, {})
    for E_, st in [('( abs ` %s )' % Kv, kr), ('( abs ` %s )' % AVA, aar), ('( abs ` %s )' % AVB, abr)]:
        cl2.leaf(E_, 'RR', L2(st))
    cl2.leaf('( exp ` ( A + L ) )', 'RR', d2('reefcld', [d2('readdcld', [L2(ar), L2(fa['lr'])], '( A + L ) e. RR')], '( exp ` ( A + L ) ) e. RR'))
    cl2.leaf('( exp ` ( B + L ) )', 'RR', d2('reefcld', [d2('readdcld', [L2(br), L2(fa['lr'])], '( B + L ) e. RR')], '( exp ` ( B + L ) ) e. RR'))
    c2 = lin.linarith(w, X2, [L2(tri), vA, vB], '( abs ` %s ) <_ ( ( exp ` ( B + L ) ) + ( exp ` ( A + L ) ) )' % Kv, closure=cl2)
    fin = d('jca', [w.s([c1], 'ex', '( %s -> ( ( Re ` W ) <_ 0 -> ( ( abs ` %s ) <_ ( %s + %s ) /\\ ( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. %s ) <_ 4 ) ) )' % (X0, Kv, EXB, EXA, Kv, Kv, LW)),
                    w.s([c2], 'ex', '( %s -> ( ( Re ` W ) <_ 1 -> ( abs ` %s ) <_ ( ( exp ` ( B + L ) ) + ( exp ` ( A + L ) ) ) ) )' % (X0, Kv))], CONC)
    w.qed([fin], 'idi', S['gf1kb'])
    return run(w, only)


if __name__ == '__main__':
    gen_cibl()
    gen_eh()
    gen_avgi()
    gen_avgh()
    gen_avgb()
    gen_kq()
    gen_kqb()
    gen_kb()
