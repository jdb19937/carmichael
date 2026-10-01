"""EF1 section 3: the measure pigeonhole (ExplicitFormula 444-522).
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_c.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from lin import linarith

only = sys.argv[1:]
X = '( P (,) Q )'

# ---------------------------------------------------------------- ef1pgh
if __name__ == '__main__' and (not only or 'ef1pgh' in only):
    w = W('ef1pgh', 'The measure pigeonhole: if ` S. ( P , Q ) F <_ M ( Q - P ) ` then some point of ` ( P , Q ) ` '
          'outside a given finite set ` S ` has ` F ( t ) <_ M ` ( Lean ` exists_le_avg_off_finset ` ; otherwise '
          '` F - M ` is positive on ` ( P , Q ) \\ S ` , a set of measure ` Q - P ` , and ~ itggt0 contradicts the '
          'average).  ` F ` is a function so that the contradiction hypothesis stays apart from the integration variable.')
    A0 = STATEMENTS['ef1pgh'].split(' -> E. t')[0][2:]
    c1 = D(w, A0, 'simp1', [], '( P e. RR /\\ Q e. RR /\\ P < Q )')
    c2 = D(w, A0, 'simp2', [], '( F : %s --> RR /\\ F e. L^1 )' % X)
    c3 = D(w, A0, 'simp3', [], '( ( M e. RR /\\ S. %s ( F ` t ) _d t <_ ( M x. ( Q - P ) ) ) /\\ S e. Fin )' % X)
    pr = D(w, A0, 'simp1d', [c1], 'P e. RR'); qr = D(w, A0, 'simp2d', [c1], 'Q e. RR'); pq = D(w, A0, 'simp3d', [c1], 'P < Q')
    pql = D(w, A0, 'ltled', [pr, qr, pq], 'P <_ Q')
    fx = D(w, A0, 'simpld', [c2], 'F : %s --> RR' % X); fl = D(w, A0, 'simprd', [c2], 'F e. L^1')
    c31 = D(w, A0, 'simpld', [c3], '( M e. RR /\\ S. %s ( F ` t ) _d t <_ ( M x. ( Q - P ) ) )' % X)
    mr = D(w, A0, 'simpld', [c31], 'M e. RR'); ib = D(w, A0, 'simprd', [c31], 'S. %s ( F ` t ) _d t <_ ( M x. ( Q - P ) )' % X)
    sf = D(w, A0, 'simprd', [c3], 'S e. Fin')
    mc = D(w, A0, 'recnd', [mr], 'M e. CC')
    xss = a1(w, A0, 'ioossre', '%s C_ RR' % X)
    SX = '( S i^i %s )' % X; G = '( %s \\ %s )' % (X, SX)
    sxf = w.s([sf, w.inst('infi')], 'syl', '( %s -> %s e. Fin )' % (A0, SX))
    sxx = a1(w, A0, 'inss2', '%s C_ %s' % (SX, X))
    sxr = w.s([sxx, xss], 'sstrd', '( %s -> %s C_ RR )' % (A0, SX))
    sxv = w.s([sxf, sxr, w.inst('ovolfi')], 'syl2anc', '( %s -> ( vol* ` %s ) = 0 )' % (A0, SX))
    sxm = w.s([sxr, sxv, w.inst('nulmbl')], 'syl2anc', '( %s -> %s e. dom vol )' % (A0, SX))
    xm = a1(w, A0, 'ioombl', '%s e. dom vol' % X)
    gm = w.s([xm, sxm, w.inst('difmbl')], 'syl2anc', '( %s -> %s e. dom vol )' % (A0, G))
    gx = a1(w, A0, 'difss', '%s C_ %s' % (G, X))
    gr = w.s([gx, xss], 'sstrd', '( %s -> %s C_ RR )' % (A0, G))
    # vol ( G ) = Q - P
    un1 = a1(w, A0, 'undif1', '( %s u. %s ) = ( %s u. %s )' % (G, SX, X, SX))
    un2 = w.s([sxx, w.s([], 'ssequn2', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (SX, X, X, SX, X))], 'sylib',
              '( %s -> ( %s u. %s ) = %s )' % (A0, X, SX, X))
    un = w.s([un1, un2], 'eqtrd', '( %s -> ( %s u. %s ) = %s )' % (A0, G, SX, X))
    ovu = w.s([gr, sxr, sxv, w.inst('ovolunnul')], 'syl3anc', '( %s -> ( vol* ` ( %s u. %s ) ) = ( vol* ` %s ) )' % (A0, G, SX, G))
    ovx = w.s([pr, qr, pql, w.inst('ovolioo')], 'syl3anc', '( %s -> ( vol* ` %s ) = ( Q - P ) )' % (A0, X))
    ovg = w.s([w.s([ovu], 'eqcomd', '( %s -> ( vol* ` %s ) = ( vol* ` ( %s u. %s ) ) )' % (A0, G, G, SX)),
               w.s([w.s([un], 'fveq2d', '( %s -> ( vol* ` ( %s u. %s ) ) = ( vol* ` %s ) )' % (A0, G, SX, X)), ovx], 'eqtrd', '( %s -> ( vol* ` ( %s u. %s ) ) = ( Q - P ) )' % (A0, G, SX))],
              'eqtrd', '( %s -> ( vol* ` %s ) = ( Q - P ) )' % (A0, G))
    vg = w.s([w.s([gm, w.inst('mblvol')], 'syl', '( %s -> ( vol ` %s ) = ( vol* ` %s ) )' % (A0, G, G)), ovg], 'eqtrd', '( %s -> ( vol ` %s ) = ( Q - P ) )' % (A0, G))
    cl = Closure(w, A0, {'P': ('RR', pr), 'Q': ('RR', qr), 'M': ('RR', mr)})
    qp0 = linarith(w, A0, [pq], '0 < ( Q - P )', closure=cl)
    vgr = w.s([vg, cl.mem('( Q - P )', 'RR')], 'eqeltrd', '( %s -> ( vol ` %s ) e. RR )' % (A0, G))
    # integrability
    FM = '( x e. %s |-> ( F ` x ) )' % X
    feq = w.s([fx], 'feqmptd', '( %s -> F = %s )' % (A0, FM))
    fml = w.s([feq, fl], 'eqeltrrd', '( %s -> %s e. L^1 )' % (A0, FM))
    AX = '( %s /\\ x e. %s )' % (A0, X)
    fxr = w.s([w.s([fx], 'adantr', '( %s -> F : %s --> RR )' % (AX, X)), w.s([], 'simpr', '( %s -> x e. %s )' % (AX, X))], 'ffvelcdmd', '( %s -> ( F ` x ) e. RR )' % AX)
    fxc = D(w, AX, 'recnd', [fxr], '( F ` x ) e. CC')
    AG = '( %s /\\ x e. %s )' % (A0, G)
    xgx = w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (AG, G)), w.inst('eldifi')], 'syl', '( %s -> x e. %s )' % (AG, X))
    fgr = w.s([w.s([fx], 'adantr', '( %s -> F : %s --> RR )' % (AG, X)), xgx], 'ffvelcdmd', '( %s -> ( F ` x ) e. RR )' % AG)
    fgc = D(w, AG, 'recnd', [fgr], '( F ` x ) e. CC')
    fgl = w.s([gx, gm, fxc, fml], 'iblss', '( %s -> ( x e. %s |-> ( F ` x ) ) e. L^1 )' % (A0, G))
    cgl = w.s([w.s([], 'fconstmpt', '( %s X. { M } ) = ( x e. %s |-> M )' % (G, G)), w.s([gm, vgr, mc, w.inst('iblconst')], 'syl3anc', '( %s -> ( %s X. { M } ) e. L^1 )' % (A0, G))],
              'eqeltrrid', '( %s -> ( x e. %s |-> M ) e. L^1 )' % (A0, G))
    mcg = w.s([mc], 'adantr', '( %s -> M e. CC )' % AG)
    dgl = w.s([fgc, fgl, mcg, cgl], 'iblsub', '( %s -> ( x e. %s |-> ( ( F ` x ) - M ) ) e. L^1 )' % (A0, G))
    # the integral of F - M over G
    vx = w.s([pr, qr, pql, w.inst('volioo')], 'syl3anc', '( %s -> ( vol ` %s ) = ( Q - P ) )' % (A0, X))
    vxr = w.s([vx, cl.mem('( Q - P )', 'RR')], 'eqeltrd', '( %s -> ( vol ` %s ) e. RR )' % (A0, X))
    cxl = w.s([w.s([], 'fconstmpt', '( %s X. { M } ) = ( x e. %s |-> M )' % (X, X)), w.s([xm, vxr, mc, w.inst('iblconst')], 'syl3anc', '( %s -> ( %s X. { M } ) e. L^1 )' % (A0, X))],
              'eqeltrrid', '( %s -> ( x e. %s |-> M ) e. L^1 )' % (A0, X))
    mcx = w.s([mc], 'adantr', '( %s -> M e. CC )' % AX)
    DX = '( X \\ %s )'.replace('X', X) % G
    ing = w.s([w.s([], 'dfin4', '( %s i^i %s ) = ( %s \\ ( %s \\ %s ) )' % (X, SX, X, X, SX))], 'eqcomi', '%s = ( %s i^i %s )' % (DX, X, SX))
    ings = w.s([w.s([ing, w.s([], 'inss2', '( %s i^i %s ) C_ %s' % (X, SX, SX))], 'eqsstri', '%s C_ %s' % (DX, SX))], 'a1i', '( %s -> %s C_ %s )' % (A0, DX, SX))
    dxv = w.s([ings, sxr, sxv, w.inst('ovolssnul')], 'syl3anc', '( %s -> ( vol* ` %s ) = 0 )' % (A0, DX))
    FMx = '( ( F ` x ) - M )'
    s3 = w.s([gx, xss, dxv, D(w, AX, 'subcld', [fxc, mcx], '%s e. CC' % FMx)], 'itgss3', '( %s -> ( ( ( x e. %s |-> %s ) e. L^1 <-> ( x e. %s |-> %s ) e. L^1 ) /\\ S. %s %s _d x = S. %s %s _d x ) )'
             % (A0, G, FMx, X, FMx, G, FMx, X, FMx))
    s3e = D(w, A0, 'simprd', [s3], 'S. %s %s _d x = S. %s %s _d x' % (G, FMx, X, FMx))
    sub = w.s([fxc, fml, mcx, cxl], 'itgsub', '( %s -> S. %s %s _d x = ( S. %s ( F ` x ) _d x - S. %s M _d x ) )' % (A0, X, FMx, X, X))
    cst = w.s([xm, vxr, mc, w.inst('itgconst')], 'syl3anc', '( %s -> S. %s M _d x = ( M x. ( vol ` %s ) ) )' % (A0, X, X))
    cst2 = w.s([cst, w.s([vx], 'oveq2d', '( %s -> ( M x. ( vol ` %s ) ) = ( M x. ( Q - P ) ) )' % (A0, X))], 'eqtrd', '( %s -> S. %s M _d x = ( M x. ( Q - P ) ) )' % (A0, X))
    cbv0 = w.s([w.s([], 'fveq2', '( x = t -> ( F ` x ) = ( F ` t ) )')], 'cbvitgv', 'S. %s ( F ` x ) _d x = S. %s ( F ` t ) _d t' % (X, X))
    cbv = w.s([cbv0], 'a1i', '( %s -> S. %s ( F ` x ) _d x = S. %s ( F ` t ) _d t )' % (A0, X, X))
    IT = 'S. %s ( F ` t ) _d t' % X
    val = chain(w, A0, ['S. %s %s _d x' % (G, FMx), 'S. %s %s _d x' % (X, FMx), '( S. %s ( F ` x ) _d x - S. %s M _d x )' % (X, X), '( %s - ( M x. ( Q - P ) ) )' % IT],
                [s3e, sub, w.s([cbv, cst2], 'oveq12d', '( %s -> ( S. %s ( F ` x ) _d x - S. %s M _d x ) = ( %s - ( M x. ( Q - P ) ) ) )' % (A0, X, X, IT))])
    ITr = w.s([fxr, fml], 'itgrecl', '( %s -> S. %s ( F ` x ) _d x e. RR )' % (A0, X))
    ITr2 = w.s([w.s([cbv], 'eqcomd', '( %s -> %s = S. %s ( F ` x ) _d x )' % (A0, IT, X)), ITr], 'eqeltrd', '( %s -> %s e. RR )' % (A0, IT))
    le0 = w.s([ib, w.s([ITr2, cl.mem('( M x. ( Q - P ) )', 'RR')], 'suble0d', '( %s -> ( ( %s - ( M x. ( Q - P ) ) ) <_ 0 <-> %s <_ ( M x. ( Q - P ) ) ) )' % (A0, IT, IT))], 'mpbird',
              '( %s -> ( %s - ( M x. ( Q - P ) ) ) <_ 0 )' % (A0, IT))
    gle = w.s([val, le0], 'eqbrtrd', '( %s -> S. %s %s _d x <_ 0 )' % (A0, G, FMx))
    AGR = w.s([fgr, w.s([mr], 'adantr', '( %s -> M e. RR )' % AG)], 'resubcld', '( %s -> %s e. RR )' % (AG, FMx))
    gr_ = w.s([AGR, dgl], 'itgrecl', '( %s -> S. %s %s _d x e. RR )' % (A0, G, FMx))
    # the contradiction hypothesis
    PSI_ = 'E. t e. %s ( -. t e. S /\\ ( F ` t ) <_ M )' % X
    N0 = '( %s /\\ -. %s )' % (A0, PSI_)
    nn = w.s([], 'simpr', '( %s -> -. %s )' % (N0, PSI_))
    ral = w.s([nn, w.s([], 'ralnex', '( A. t e. %s -. ( -. t e. S /\\ ( F ` t ) <_ M ) <-> -. %s )' % (X, PSI_))], 'sylibr',
              '( %s -> A. t e. %s -. ( -. t e. S /\\ ( F ` t ) <_ M ) )' % (N0, X))
    NG = '( %s /\\ x e. %s )' % (N0, G)
    a0n = w.s([w.s([], 'simpl', '( %s -> %s )' % (NG, N0)), w.s([], 'simpl', '( %s -> %s )' % (N0, A0))], 'syl', '( %s -> %s )' % (NG, A0))
    xg = w.s([], 'simpr', '( %s -> x e. %s )' % (NG, G))
    xx = w.s([xg, w.inst('eldifi')], 'syl', '( %s -> x e. %s )' % (NG, X))
    xnsx = w.s([xg, w.inst('eldifn')], 'syl', '( %s -> -. x e. %s )' % (NG, SX))
    NGS = '( %s /\\ x e. S )' % NG
    insx = w.s([w.s([], 'simpr', '( %s -> x e. S )' % NGS), w.s([xx], 'adantr', '( %s -> x e. %s )' % (NGS, X))], 'elind', '( %s -> x e. %s )' % (NGS, SX))
    xns = w.s([insx, w.s([xnsx], 'adantr', '( %s -> -. x e. %s )' % (NGS, SX))], 'pm2.65da', '( %s -> -. x e. S )' % NG)
    sbx = w.s([w.s([w.s([], 'eleq1', '( t = x -> ( t e. S <-> x e. S ) )')], 'notbid', '( t = x -> ( -. t e. S <-> -. x e. S ) )'),
               w.s([w.s([], 'fveq2', '( t = x -> ( F ` t ) = ( F ` x ) )')], 'breq1d', '( t = x -> ( ( F ` t ) <_ M <-> ( F ` x ) <_ M ) )')], 'anbi12d',
              '( t = x -> ( ( -. t e. S /\\ ( F ` t ) <_ M ) <-> ( -. x e. S /\\ ( F ` x ) <_ M ) ) )')
    sbn = w.s([sbx], 'notbid', '( t = x -> ( -. ( -. t e. S /\\ ( F ` t ) <_ M ) <-> -. ( -. x e. S /\\ ( F ` x ) <_ M ) ) )')
    inst = w.s([xx, w.s([ral], 'adantr', '( %s -> A. t e. %s -. ( -. t e. S /\\ ( F ` t ) <_ M ) )' % (NG, X)), w.s([sbn], 'rspcv',
               '( x e. %s -> ( A. t e. %s -. ( -. t e. S /\\ ( F ` t ) <_ M ) -> -. ( -. x e. S /\\ ( F ` x ) <_ M ) ) )' % (X, X))], 'sylc', '( %s -> -. ( -. x e. S /\\ ( F ` x ) <_ M ) )' % NG)
    imp = w.s([inst, w.s([], 'imnan', '( ( -. x e. S -> -. ( F ` x ) <_ M ) <-> -. ( -. x e. S /\\ ( F ` x ) <_ M ) )')], 'sylibr', '( %s -> ( -. x e. S -> -. ( F ` x ) <_ M ) )' % NG)
    nle = w.s([xns, imp], 'mpd', '( %s -> -. ( F ` x ) <_ M )' % NG)
    fr2 = w.s([w.s([a0n, fx], 'syl', '( %s -> F : %s --> RR )' % (NG, X)), xx], 'ffvelcdmd', '( %s -> ( F ` x ) e. RR )' % NG)
    mr2 = w.s([a0n, mr], 'syl', '( %s -> M e. RR )' % NG)
    lt = w.s([nle, w.s([mr2, fr2], 'ltnled', '( %s -> ( M < ( F ` x ) <-> -. ( F ` x ) <_ M ) )' % NG)], 'mpbird', '( %s -> M < ( F ` x ) )' % NG)
    rp = w.s([lt, w.s([mr2, fr2, w.inst('difrp')], 'syl2anc', '( %s -> ( M < ( F ` x ) <-> %s e. RR+ ) )' % (NG, FMx))], 'mpbid', '( %s -> %s e. RR+ )' % (NG, FMx))
    a0 = w.s([], 'simpl', '( %s -> %s )' % (N0, A0))
    vpos = w.s([a0, w.s([vg, qp0], 'breqtrrd', '( %s -> 0 < ( vol ` %s ) )' % (A0, G))], 'syl', '( %s -> 0 < ( vol ` %s ) )' % (N0, G))
    gt = w.s([vpos, w.s([a0, dgl], 'syl', '( %s -> ( x e. %s |-> %s ) e. L^1 )' % (N0, G, FMx)), rp], 'itggt0', '( %s -> 0 < S. %s %s _d x )' % (N0, G, FMx))
    ngt = w.s([gle, w.s([gr_, a1(w, A0, '0re', '0 e. RR')], 'lenltd', '( %s -> ( S. %s %s _d x <_ 0 <-> -. 0 < S. %s %s _d x ) )' % (A0, G, FMx, G, FMx))], 'mpbid',
              '( %s -> -. 0 < S. %s %s _d x )' % (A0, G, FMx))
    ngt2 = w.s([a0, ngt], 'syl', '( %s -> -. 0 < S. %s %s _d x )' % (N0, G, FMx))
    w.qed([gt, ngt2], 'condan', STATEMENTS['ef1pgh'])
    go(w, only)
