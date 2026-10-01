"""ZL3c section B: Euler's integral.  `MM_DB=sorties/zl3c.mm python3 tools/gen/zl3c_b.py LABEL...`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import W, D, E, a1, Closure, chain, efle_, efadd_
from lin import linarith, nlinarith, lineq
import zl3clib as L
from c0lib import runh
from zl1lib import mptv

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL3C_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if L.HYPS.get(w.label) else w.run()


def want(label):
    return __name__ == '__main__' and (not only or label in only)


def ante_of(label):
    s = L.STATEMENTS[label]
    toks = s[2:-2].split(' ')
    depth = 0
    for i, t in enumerate(toks):
        if t == '(':
            depth += 1
        elif t == ')':
            depth -= 1
        elif t == '->' and depth == 0:
            return ' '.join(toks[:i]), ' '.join(toks[i + 1:])
    raise ValueError(label)


J = '( TopOpen ` CCfld )'
R0 = '( 0 [,) +oo )'
DD = "( `' Re \" RR+ )"
KK = '( %s |`t %s )' % (J, R0)
LL = '( %s |`t %s )' % (J, DD)
FF = '( a e. %s , b e. %s |-> ( a ^c b ) )' % (R0, DD)

# ---------------------------------------------------------------- zl3cx0
if want('zl3cx0'):
    w = W('zl3cx0', 'For ` 0 < Re A ` the power ` x ^c A ` is continuous on ` [ 0 , +oo ) ` , the point ` 0 ` included ( ~ cxpcn3 ).')
    A, C = ante_of('zl3cx0')
    ac = D(w, A, 'simpl', [], 'A e. CC'); a0 = D(w, A, 'simpr', [], '0 < ( Re ` A )')
    jt = w.s([w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'cnfldtopon', '%s e. ( TopOn ` CC )' % J)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (A, J))
    r0c = w.s([w.s([w.s([], 'rge0ssre', '%s C_ RR' % R0), w.s([], 'ax-resscn', 'RR C_ CC')], 'sstri', '%s C_ CC' % R0)], 'a1i', '( %s -> %s C_ CC )' % (A, R0))
    dmre = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom Re = CC')
    dc = w.s([w.s([w.s([], 'cnvimass', '%s C_ dom Re' % DD), dmre], 'sseqtri', '%s C_ CC' % DD)], 'a1i', '( %s -> %s C_ CC )' % (A, DD))
    kt = w.s([jt, r0c, w.inst('resttopon')], 'syl2anc', '( %s -> %s e. ( TopOn ` %s ) )' % (A, KK, R0))
    lt = w.s([jt, dc, w.inst('resttopon')], 'syl2anc', '( %s -> %s e. ( TopOn ` %s ) )' % (A, LL, DD))
    cx3 = w.s([w.s([], 'eqid', '%s = %s' % (DD, DD)), w.s([], 'eqid', '%s = %s' % (J, J)), w.s([], 'eqid', '%s = %s' % (KK, KK)), w.s([], 'eqid', '%s = %s' % (LL, LL))],
              'cxpcn3', '%s e. ( ( %s tX %s ) Cn %s )' % (FF, KK, LL, J))
    refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    rap = w.s([w.s([D(w, A, 'recld', [ac], '( Re ` A ) e. RR'), a0], 'jca', '( %s -> ( ( Re ` A ) e. RR /\\ 0 < ( Re ` A ) ) )' % A),
               w.s([], 'elrp', '( ( Re ` A ) e. RR+ <-> ( ( Re ` A ) e. RR /\\ 0 < ( Re ` A ) ) )')], 'sylibr', '( %s -> ( Re ` A ) e. RR+ )' % A)
    ad = w.s([w.s([ac, rap], 'jca', '( %s -> ( A e. CC /\\ ( Re ` A ) e. RR+ ) )' % A),
              w.s([refn, w.inst('elpreima')], 'ax-mp', '( A e. %s <-> ( A e. CC /\\ ( Re ` A ) e. RR+ ) )' % DD)], 'sylibr', '( %s -> A e. %s )' % (A, DD))
    idm = w.s([kt], 'cnmptid', '( %s -> ( x e. %s |-> x ) e. ( %s Cn %s ) )' % (A, R0, KK, KK))
    cm = w.s([kt, lt, ad], 'cnmptc', '( %s -> ( x e. %s |-> A ) e. ( %s Cn %s ) )' % (A, R0, KK, LL))
    c12 = w.s([kt, idm, cm, w.s([cx3], 'a1i', '( %s -> %s e. ( ( %s tX %s ) Cn %s ) )' % (A, FF, KK, LL, J))], 'cnmpt12f',
              '( %s -> ( x e. %s |-> ( x %s A ) ) e. ( %s Cn %s ) )' % (A, R0, FF, KK, J))
    Ax = '( %s /\\ x e. %s )' % (A, R0)
    ov = w.s([w.s([], 'oveq1', '( a = x -> ( a ^c b ) = ( x ^c b ) )'), w.s([], 'oveq2', '( b = A -> ( x ^c b ) = ( x ^c A ) )'),
              w.s([], 'eqid', '%s = %s' % (FF, FF)), w.s([], 'ovex', '( x ^c A ) e. _V')], 'ovmpo', '( ( x e. %s /\\ A e. %s ) -> ( x %s A ) = ( x ^c A ) )' % (R0, DD, FF))
    ovx = w.s([D(w, Ax, 'simpr', [], 'x e. %s' % R0), D(w, Ax, 'adantr', [ad], 'A e. %s' % DD), ov], 'syl2anc', '( %s -> ( x %s A ) = ( x ^c A ) )' % (Ax, FF))
    meq = w.s([ovx], 'mpteq2dva', '( %s -> ( x e. %s |-> ( x %s A ) ) = ( x e. %s |-> ( x ^c A ) ) )' % (A, R0, FF, R0))
    cc = w.s([meq, c12], 'eqeltrrd', '( %s -> ( x e. %s |-> ( x ^c A ) ) e. ( %s Cn %s ) )' % (A, R0, KK, J))
    cuni = w.s([w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'cnfldtopon', '%s e. ( TopOn ` CC )' % J), w.inst('toponuni')], 'ax-mp', 'CC = U. %s' % J)
    rid = w.s([cuni, w.s([w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'cnfldtopon', '%s e. ( TopOn ` CC )' % J), w.inst('topontop')], 'ax-mp', '%s e. Top' % J)],
              'restid', '( %s |`t CC ) = %s' % (J, J)) if False else None
    ridx = w.s([cuni, w.inst('restid')], 'syl' if False else 'idi', 'x') if False else None
    rid = w.s([w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'cnfldtop', '%s e. Top' % J), w.s([cuni], 'restid', '( %s e. Top -> ( %s |`t CC ) = %s )' % (J, J, J))],
              'ax-mp', '( %s |`t CC ) = %s' % (J, J))
    cf = w.s([w.s([], 'eqid', '%s = %s' % (J, J)), w.s([], 'eqid', '%s = %s' % (KK, KK)), w.s([], 'eqid', '( %s |`t CC ) = ( %s |`t CC )' % (J, J))], 'cncfcn',
             '( ( %s C_ CC /\\ CC C_ CC ) -> ( %s -cn-> CC ) = ( %s Cn ( %s |`t CC ) ) )' % (R0, R0, KK, J))
    cf2 = w.s([r0c, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A), cf], 'syl2anc', '( %s -> ( %s -cn-> CC ) = ( %s Cn ( %s |`t CC ) ) )' % (A, R0, KK, J))
    cf3 = w.s([cf2, w.s([w.s([rid], 'oveq2i', '( %s Cn ( %s |`t CC ) ) = ( %s Cn %s )' % (KK, J, KK, J))], 'a1i', '( %s -> ( %s Cn ( %s |`t CC ) ) = ( %s Cn %s ) )' % (A, KK, J, KK, J))],
              'eqtrd', '( %s -> ( %s -cn-> CC ) = ( %s Cn %s ) )' % (A, R0, KK, J))
    w.qed([cc, cf3], 'eleqtrrd', L.STATEMENTS['zl3cx0'])
    go(w)


# ---------------------------------------------------------------- zl3dvi
if want('zl3dvi'):
    w = W('zl3dvi', 'The derivative of a function on a closed interval is the derivative of its restriction to the open interval '
          '( ~ dvres twice, ~ iccntr ).')
    A, C = ante_of('zl3dvi')
    ar = D(w, A, 'simpll', [], 'A e. RR'); br = D(w, A, 'simplr', [], 'B e. RR'); ff = D(w, A, 'simpr', [], 'F : ( A [,] B ) --> CC')
    T = '( %s |`t RR )' % J
    tg = w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'tgioo2', '( topGen ` ran (,) ) = %s' % T)
    rc = a1(w, A, 'ax-resscn', 'RR C_ CC')
    icr = w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> ( A [,] B ) C_ RR )' % A)
    ior = w.s([w.s([], 'ioossre', '( A (,) B ) C_ RR')], 'a1i', '( %s -> ( A (,) B ) C_ RR )' % A)
    base = w.s([rc, ff], 'jca', '( %s -> ( RR C_ CC /\\ F : ( A [,] B ) --> CC ) )' % A)
    d1 = w.s([w.s([base, w.s([icr, icr], 'jca', '( %s -> ( ( A [,] B ) C_ RR /\\ ( A [,] B ) C_ RR ) )' % A)], 'jca',
                  '( %s -> ( ( RR C_ CC /\\ F : ( A [,] B ) --> CC ) /\\ ( ( A [,] B ) C_ RR /\\ ( A [,] B ) C_ RR ) ) )' % A),
              w.s([w.s([], 'eqid', '%s = %s' % (J, J)), w.s([], 'eqid', '%s = %s' % (T, T))], 'dvres',
                  '( ( ( RR C_ CC /\\ F : ( A [,] B ) --> CC ) /\\ ( ( A [,] B ) C_ RR /\\ ( A [,] B ) C_ RR ) ) -> ( RR _D ( F |` ( A [,] B ) ) ) = ( ( RR _D F ) |` ( ( int ` %s ) ` ( A [,] B ) ) ) )' % T)],
             'syl', '( %s -> ( RR _D ( F |` ( A [,] B ) ) ) = ( ( RR _D F ) |` ( ( int ` %s ) ` ( A [,] B ) ) ) )' % (A, T))
    d2 = w.s([w.s([base, w.s([icr, ior], 'jca', '( %s -> ( ( A [,] B ) C_ RR /\\ ( A (,) B ) C_ RR ) )' % A)], 'jca',
                  '( %s -> ( ( RR C_ CC /\\ F : ( A [,] B ) --> CC ) /\\ ( ( A [,] B ) C_ RR /\\ ( A (,) B ) C_ RR ) ) )' % A),
              w.s([w.s([], 'eqid', '%s = %s' % (J, J)), w.s([], 'eqid', '%s = %s' % (T, T))], 'dvres',
                  '( ( ( RR C_ CC /\\ F : ( A [,] B ) --> CC ) /\\ ( ( A [,] B ) C_ RR /\\ ( A (,) B ) C_ RR ) ) -> ( RR _D ( F |` ( A (,) B ) ) ) = ( ( RR _D F ) |` ( ( int ` %s ) ` ( A (,) B ) ) ) )' % T)],
             'syl', '( %s -> ( RR _D ( F |` ( A (,) B ) ) ) = ( ( RR _D F ) |` ( ( int ` %s ) ` ( A (,) B ) ) ) )' % (A, T))
    tgi = w.s([tg], 'a1i', '( %s -> ( topGen ` ran (,) ) = %s )' % (A, T))
    i1 = w.s([w.s([w.s([tgi], 'fveq2d', '( %s -> ( int ` ( topGen ` ran (,) ) ) = ( int ` %s ) )' % (A, T))], 'fveq1d',
                  '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` ( A [,] B ) ) = ( ( int ` %s ) ` ( A [,] B ) ) )' % (A, T)),
              w.s([ar, br, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` ( A [,] B ) ) = ( A (,) B ) )' % A)], 'eqtr3d',
             '( %s -> ( ( int ` %s ) ` ( A [,] B ) ) = ( A (,) B ) )' % (A, T))
    i2 = w.s([w.s([w.s([tgi], 'fveq2d', '( %s -> ( int ` ( topGen ` ran (,) ) ) = ( int ` %s ) )' % (A, T))], 'fveq1d',
                  '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` ( A (,) B ) ) = ( ( int ` %s ) ` ( A (,) B ) ) )' % (A, T)),
              w.s([w.s([w.s([], 'retop', '( topGen ` ran (,) ) e. Top'), w.s([], 'iooretop', '( A (,) B ) e. ( topGen ` ran (,) )'), w.inst('isopn3i')], 'mp2an',
                       '( ( int ` ( topGen ` ran (,) ) ) ` ( A (,) B ) ) = ( A (,) B )')], 'a1i', '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` ( A (,) B ) ) = ( A (,) B ) )' % A)],
             'eqtr3d', '( %s -> ( ( int ` %s ) ` ( A (,) B ) ) = ( A (,) B ) )' % (A, T))
    rid = w.s([ff, w.inst('fresid' if False else 'ffn')], 'syl', '( %s -> F Fn ( A [,] B ) )' % A)
    rid2 = w.s([rid, w.inst('fnresdm')], 'syl', '( %s -> ( F |` ( A [,] B ) ) = F )' % A)
    e1 = w.s([w.s([w.s([rid2], 'oveq2d', '( %s -> ( RR _D ( F |` ( A [,] B ) ) ) = ( RR _D F ) )' % A), d1], 'eqtr3d',
                  '( %s -> ( RR _D F ) = ( ( RR _D F ) |` ( ( int ` %s ) ` ( A [,] B ) ) ) )' % (A, T)),
              w.s([i1], 'reseq2d', '( %s -> ( ( RR _D F ) |` ( ( int ` %s ) ` ( A [,] B ) ) ) = ( ( RR _D F ) |` ( A (,) B ) ) )' % (A, T))], 'eqtrd',
             '( %s -> ( RR _D F ) = ( ( RR _D F ) |` ( A (,) B ) ) )' % A)
    e2 = w.s([d2, w.s([i2], 'reseq2d', '( %s -> ( ( RR _D F ) |` ( ( int ` %s ) ` ( A (,) B ) ) ) = ( ( RR _D F ) |` ( A (,) B ) ) )' % (A, T))], 'eqtrd',
             '( %s -> ( RR _D ( F |` ( A (,) B ) ) ) = ( ( RR _D F ) |` ( A (,) B ) ) )' % A)
    w.qed([e1, e2], 'eqtr4d', L.STATEMENTS['zl3dvi'])
    go(w)


def icc_re(w, C, x, lo, hi, xin, lor, hir):
    """( C -> x e. RR ) from ( C -> x e. ( lo [,] hi ) )"""
    return w.s([w.s([lor, hir, w.inst('iccssre')], 'syl2anc', '( %s -> ( %s [,] %s ) C_ RR )' % (C, lo, hi)), xin], 'sseldd', '( %s -> %s e. RR )' % (C, x))


def ioo_rp(w, C, x, N, xin, nr):
    """( C -> x e. RR+ ) from ( C -> x e. ( 0 (,) N ) )"""
    ss = w.s([w.s([w.s([nr], 'rexrd', '( %s -> %s e. RR* )' % (C, N)), w.inst('pnfge')], 'syl', '( %s -> %s <_ +oo )' % (C, N)),
              w.s([], 'pnfxr', '+oo e. RR*')], 'idi', 'x') if False else None
    le = w.s([w.s([nr], 'rexrd', '( %s -> %s e. RR* )' % (C, N)), w.inst('pnfge')], 'syl', '( %s -> %s <_ +oo )' % (C, N))
    ss = w.s([a1(w, C, 'pnfxr', '+oo e. RR*'), le, w.inst('iooss2')], 'syl2anc', '( %s -> ( 0 (,) %s ) C_ ( 0 (,) +oo ) )' % (C, N))
    ss2 = w.s([ss, w.s([w.s([], 'ioorp', '( 0 (,) +oo ) = RR+')], 'a1i', '( %s -> ( 0 (,) +oo ) = RR+ )' % C)], 'sseqtrd', '( %s -> ( 0 (,) %s ) C_ RR+ )' % (C, N))
    return w.s([ss2, xin], 'sseldd', '( %s -> %s e. RR+ )' % (C, x)), ss2


# ---------------------------------------------------------------- zl3dvc
if want('zl3dvc'):
    w = W('zl3dvc', 'The derivative of ` x ^c W / W ` on ` [ 0 , N ] ` is ` x ^c ( W - 1 ) ` on the open interval ( ~ zl3dvi , ~ dvcxp1 , ~ dvmptres ).')
    A, C = ante_of('zl3dvc')
    wc = D(w, A, 'simpll', [], 'W e. CC'); wn = D(w, A, 'simplr', [], 'W =/= 0'); nrp = D(w, A, 'simpr', [], 'N e. RR+')
    nr = D(w, A, 'rpred', [nrp], 'N e. RR'); z0 = a1(w, A, '0re', '0 e. RR')
    G = '( x e. ( 0 [,] N ) |-> ( ( x ^c W ) / W ) )'
    Ax = '( %s /\\ x e. ( 0 [,] N ) )' % A
    xr = icc_re(w, Ax, 'x', '0', 'N', D(w, Ax, 'simpr', [], 'x e. ( 0 [,] N )'), a1(w, Ax, '0re', '0 e. RR'), D(w, Ax, 'adantr', [nr], 'N e. RR'))
    xc = D(w, Ax, 'recnd', [xr], 'x e. CC')
    wcx = D(w, Ax, 'adantr', [wc], 'W e. CC')
    gv = D(w, Ax, 'divcld', [D(w, Ax, 'cxpcld', [xc, wcx], '( x ^c W ) e. CC'), wcx, D(w, Ax, 'adantr', [wn], 'W =/= 0')], '( ( x ^c W ) / W ) e. CC')
    gf = w.s([gv, w.s([], 'eqid', '%s = %s' % (G, G))], 'fmptd', '( %s -> %s : ( 0 [,] N ) --> CC )' % (A, G))
    dvi = w.s([w.s([w.s([z0, nr], 'jca', '( %s -> ( 0 e. RR /\\ N e. RR ) )' % A), gf], 'jca', '( %s -> ( ( 0 e. RR /\\ N e. RR ) /\\ %s : ( 0 [,] N ) --> CC ) )' % (A, G)),
               w.inst('zl3dvi')], 'syl', '( %s -> ( RR _D %s ) = ( RR _D ( %s |` ( 0 (,) N ) ) ) )' % (A, G, G))
    GO = '( x e. ( 0 (,) N ) |-> ( ( x ^c W ) / W ) )'
    rs = w.s([w.s([w.s([], 'ioossicc', '( 0 (,) N ) C_ ( 0 [,] N )'), w.inst('resmpt')], 'ax-mp', '( %s |` ( 0 (,) N ) ) = %s' % (G, GO))], 'a1i',
             '( %s -> ( %s |` ( 0 (,) N ) ) = %s )' % (A, G, GO))
    S = w.s([w.s([], 'reelprrecn', 'RR e. { RR , CC }')], 'a1i', '( %s -> RR e. { RR , CC } )' % A)
    Ap = '( %s /\\ x e. RR+ )' % A
    xpc = D(w, Ap, 'rpcnd', [D(w, Ap, 'simpr', [], 'x e. RR+')], 'x e. CC')
    wcp = D(w, Ap, 'adantr', [wc], 'W e. CC')
    d0 = w.s([wc, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( x e. RR+ |-> ( x ^c W ) ) ) = ( x e. RR+ |-> ( W x. ( x ^c ( W - 1 ) ) ) ) )' % A)
    WM = '( W - 1 )'
    wm1 = D(w, Ap, 'subcld', [wcp, a1(w, Ap, 'ax-1cn', '1 e. CC')], '%s e. CC' % WM)
    bb = D(w, Ap, 'mulcld', [wcp, D(w, Ap, 'cxpcld', [xpc, wm1], '( x ^c %s ) e. CC' % WM)], '( W x. ( x ^c %s ) ) e. CC' % WM)
    d1 = w.s([S, D(w, Ap, 'cxpcld', [xpc, wcp], '( x ^c W ) e. CC'), bb, d0, wc, wn], 'dvmptdivc',
             '( %s -> ( RR _D ( x e. RR+ |-> ( ( x ^c W ) / W ) ) ) = ( x e. RR+ |-> ( ( W x. ( x ^c %s ) ) / W ) ) )' % (A, WM))
    Ao = '( %s /\\ x e. RR+ )' % A
    xrp_, ss = ioo_rp(w, A, 'N', 'N', None, nr) if False else (None, None)
    le = w.s([w.s([nr], 'rexrd', '( %s -> N e. RR* )' % A), w.inst('pnfge')], 'syl', '( %s -> N <_ +oo )' % A)
    ss = w.s([a1(w, A, 'pnfxr', '+oo e. RR*'), le, w.inst('iooss2')], 'syl2anc', '( %s -> ( 0 (,) N ) C_ ( 0 (,) +oo ) )' % A)
    ss2 = w.s([ss, w.s([w.s([], 'ioorp', '( 0 (,) +oo ) = RR+')], 'a1i', '( %s -> ( 0 (,) +oo ) = RR+ )' % A)], 'sseqtrd', '( %s -> ( 0 (,) N ) C_ RR+ )' % A)
    T = '( %s |`t RR )' % J
    op = w.s([w.s([w.s([], 'iooretop', '( 0 (,) N ) e. ( topGen ` ran (,) )'), w.s([w.s([], 'eqid', '%s = %s' % (J, J))], 'tgioo2', '( topGen ` ran (,) ) = %s' % T)],
                  'eleqtri', '( 0 (,) N ) e. %s' % T)], 'a1i', '( %s -> ( 0 (,) N ) e. %s )' % (A, T))
    bdiv = D(w, Ap, 'divcld', [bb, wcp, D(w, Ap, 'adantr', [wn], 'W =/= 0')], '( ( W x. ( x ^c %s ) ) / W ) e. CC' % WM)
    d2 = w.s([S, D(w, Ap, 'divcld', [D(w, Ap, 'cxpcld', [xpc, wcp], '( x ^c W ) e. CC'), wcp, D(w, Ap, 'adantr', [wn], 'W =/= 0')], '( ( x ^c W ) / W ) e. CC'),
              bdiv, d1, ss2, w.s([], 'eqid', '%s = %s' % (T, T)), w.s([], 'eqid', '%s = %s' % (J, J)), op], 'dvmptres',
             '( %s -> ( RR _D %s ) = ( x e. ( 0 (,) N ) |-> ( ( W x. ( x ^c %s ) ) / W ) ) )' % (A, GO, WM))
    Aq = '( %s /\\ x e. ( 0 (,) N ) )' % A
    xq = D(w, Aq, 'rpcnd', [w.s([w.s([ss2], 'adantr', '( %s -> ( 0 (,) N ) C_ RR+ )' % Aq), D(w, Aq, 'simpr', [], 'x e. ( 0 (,) N )')], 'sseldd', '( %s -> x e. RR+ )' % Aq)], 'x e. CC')
    wq = D(w, Aq, 'adantr', [wc], 'W e. CC')
    sim = E(w, Aq, 'divcan3d', [D(w, Aq, 'cxpcld', [xq, D(w, Aq, 'subcld', [wq, a1(w, Aq, 'ax-1cn', '1 e. CC')], '%s e. CC' % WM)], '( x ^c %s ) e. CC' % WM), wq,
                                 D(w, Aq, 'adantr', [wn], 'W =/= 0')], '( ( W x. ( x ^c %s ) ) / W )' % WM, '( x ^c %s )' % WM)
    m = w.s([sim], 'mpteq2dva', '( %s -> ( x e. ( 0 (,) N ) |-> ( ( W x. ( x ^c %s ) ) / W ) ) = ( x e. ( 0 (,) N ) |-> ( x ^c %s ) ) )' % (A, WM, WM))
    w.qed([dvi, E(w, A, 'oveq2d', [rs], '( RR _D ( %s |` ( 0 (,) N ) ) )' % G, '( RR _D %s )' % GO), d2, m], 'eqtr4d' if False else 'idi', 'x') if False else None
    r = chain(w, A, ['( RR _D %s )' % G, '( RR _D ( %s |` ( 0 (,) N ) ) )' % G, '( RR _D %s )' % GO, '( x e. ( 0 (,) N ) |-> ( ( W x. ( x ^c %s ) ) / W ) )' % WM,
                     '( x e. ( 0 (,) N ) |-> ( x ^c %s ) )' % WM], [dvi, E(w, A, 'oveq2d', [rs], '( RR _D ( %s |` ( 0 (,) N ) ) )' % G, '( RR _D %s )' % GO), d2, m])
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
    w.lines[-1] = w.lines[-1].split(' |- ')[0] + ' |- ' + L.STATEMENTS['zl3dvc']
    go(w)


def finish(w, st, label):
    """rename the step st (the last line) to qed with the statement of label"""
    assert w.lines[-1].startswith(st + ':'), (st, w.lines[-1][:40])
    head, f = w.lines[-1].split(' |- ', 1)
    w.lines[-1] = 'qed' + head[len(st):] + ' |- ' + L.STATEMENTS[label]


def split_bin(e):
    """( a OP b ) -> (a, op, b); ( exp ` a ) -> ('exp', '`', a); else None"""
    t = e.split(' ')
    if len(t) < 3 or t[0] != '(' or t[-1] != ')':
        return None
    inner = t[1:-1]
    depth = 0
    for i, tok in enumerate(inner):
        if tok == '(':
            depth += 1
        elif tok == ')':
            depth -= 1
        elif depth == 0 and tok in ('+', '-', 'x.', '/', '^', '^c', '`') and i > 0:
            return ' '.join(inner[:i]), tok, ' '.join(inner[i + 1:])
    return None


def has_x(e, x='x'):
    return x in e.split(' ')


def cont(w, C, X, e, cl, xss, special=None, x='x'):
    """( C -> ( x e. X |-> e ) e. ( X -cn-> CC ) )"""
    special = special or {}
    M = '( %s e. %s |-> %s )' % (x, X, e)
    goal = '( %s -> %s e. ( %s -cn-> CC ) )' % (C, M, X)
    if e in special:
        return special[e]
    if not has_x(e, x):
        return w.s([w.s([cl.mem(e, 'CC'), xss, a1(w, C, 'ssid', 'CC C_ CC')], '3jca', '( %s -> ( %s e. CC /\\ %s C_ CC /\\ CC C_ CC ) )' % (C, e, X)),
                    w.inst('cncfmptc')], 'syl', goal)
    if e == x:
        return w.s([w.s([xss, a1(w, C, 'ssid', 'CC C_ CC')], 'jca', '( %s -> ( %s C_ CC /\\ CC C_ CC ) )' % (C, X)), w.inst('cncfmptid')], 'syl', goal)
    if e.startswith('-u '):
        a = e[3:]
        c0 = cont(w, C, X, '( 0 - %s )' % a, cl, xss, special, x)
        eqm = w.s([w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (a, a))], 'eqcomi', '( 0 - %s ) = -u %s' % (a, a))], 'mpteq2i',
                  '( %s e. %s |-> ( 0 - %s ) ) = %s' % (x, X, a, M))
        return w.s([c0, w.s([eqm], 'a1i', '( %s -> ( %s e. %s |-> ( 0 - %s ) ) = %s )' % (C, x, X, a, M))], 'eqeltrrd' if False else 'syl6eqel' if False else 'idi', 'x') if False else \
            w.s([w.s([w.s([eqm], 'a1i', '( %s -> ( %s e. %s |-> ( 0 - %s ) ) = %s )' % (C, x, X, a, M))], 'eqcomd', '( %s -> %s = ( %s e. %s |-> ( 0 - %s ) ) )' % (C, M, x, X, a)), c0],
                'eqeltrd', goal)
    a, op, b = split_bin(e)
    if op == '`' and a == 'exp':
        return w.s([a1(w, C, 'efcn', 'exp e. ( CC -cn-> CC )'), cont(w, C, X, b, cl, xss, special, x)], 'cncfmpt1f', goal)
    if op in ('+', '-', 'x.'):
        ref = {'+': 'addcncf', '-': 'subcncf', 'x.': 'mulcncf'}[op]
        return w.s([cont(w, C, X, a, cl, xss, special, x), cont(w, C, X, b, cl, xss, special, x)], ref, goal)
    if op == '/' and not has_x(b, x):
        cz = '( CC \\ { 0 } )'
        bm = w.s([w.s([cl.mem(b, 'CC'), cl.ne0(b)], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (C, b, b)),
                  w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (b, cz, b, b))], 'sylibr', '( %s -> %s e. %s )' % (C, b, cz))
        cc = w.s([w.s([bm, xss, a1(w, C, 'difssd' if False else 'difss', '%s C_ CC' % cz)], '3jca', '( %s -> ( %s e. %s /\\ %s C_ CC /\\ %s C_ CC ) )' % (C, b, cz, X, cz)),
                  w.inst('cncfmptc')], 'syl', '( %s -> ( %s e. %s |-> %s ) e. ( %s -cn-> %s ) )' % (C, x, X, b, X, cz))
        return w.s([cont(w, C, X, a, cl, xss, special, x), cc], 'divcncf', goal)
    if op == '^' and not has_x(b, x):
        toks = set(e.split(' ')) | set(C.split(' '))
        yv = next(c for c in ['y', 'u', 't', 's', 'r', 'q', 'p', 'o'] if c not in toks and c != x)
        Fy = '( %s e. CC |-> ( %s ^ %s ) )' % (yv, yv, b)
        fc = w.s([cl.mem(b, 'NN0'), w.inst('expcncf')], 'syl', '( %s -> %s e. ( CC -cn-> CC ) )' % (C, Fy))
        c1 = w.s([fc, cont(w, C, X, a, cl, xss, special, x)], 'cncfmpt1f', '( %s -> ( %s e. %s |-> ( %s ` %s ) ) e. ( %s -cn-> CC ) )' % (C, x, X, Fy, a, X))
        Cx = '( %s /\\ %s e. %s )' % (C, x, X)
        xc = w.s([w.s([xss], 'adantr', '( %s -> %s C_ CC )' % (Cx, X)), D(w, Cx, 'simpr', [], '%s e. %s' % (x, X))], 'sseldd', '( %s -> %s e. CC )' % (Cx, x))
        clx = Closure(w, Cx, {x: ('CC', xc)}, parent=cl) if False else Closure(w, Cx, {x: ('CC', xc)})
        for (E_, k), st in list(cl.memo.items()):
            if not has_x(E_, x):
                clx.memo[(E_, k)] = w.s([st], 'adantr', '( %s -> %s )' % (Cx, formula_of_step(w, st, C)))
        am = clx.mem(a, 'CC')
        fv, val = mptv(w, Cx, yv, 'CC', '( %s ^ %s )' % (yv, b), a, am)
        eq = w.s([fv], 'mpteq2dva', '( %s -> ( %s e. %s |-> ( %s ` %s ) ) = %s )' % (C, x, X, Fy, a, M))
        return w.s([eq, c1], 'eqeltrrd', goal)
    raise ValueError('cont: cannot handle ' + e)


def formula_of_step(w, st, C):
    from cl import formula_of
    f = formula_of(w, st)
    pre = '( %s -> ' % C
    assert f.startswith(pre), f[:80]
    return f[len(pre):-2]


# ---------------------------------------------------------------- zl3ccx
if want('zl3ccx'):
    w = W('zl3ccx', 'For ` 0 < Re A ` the power ` x ^c A ` is continuous on ` [ 0 , N ] ` ( ~ zl3cx0 restricted).')
    A, C = ante_of('zl3ccx')
    ap = D(w, A, 'simpl', [], '( A e. CC /\\ 0 < ( Re ` A ) )'); nrp = D(w, A, 'simpr', [], 'N e. RR+')
    c0 = w.s([ap, w.inst('zl3cx0')], 'syl', '( %s -> ( x e. %s |-> ( x ^c A ) ) e. ( %s -cn-> CC ) )' % (A, R0, R0))
    nin = w.s([w.s([D(w, A, 'rpred', [nrp], 'N e. RR'), D(w, A, 'rpge0d', [nrp], '0 <_ N')], 'jca', '( %s -> ( N e. RR /\\ 0 <_ N ) )' % A),
               w.s([], 'elrege0', '( N e. %s <-> ( N e. RR /\\ 0 <_ N ) )' % R0)], 'sylibr', '( %s -> N e. %s )' % (A, R0))
    ss = w.s([a1(w, A, '0e0icopnf', '0 e. %s' % R0), nin, w.inst('iccssico2')], 'syl2anc', '( %s -> ( 0 [,] N ) C_ %s )' % (A, R0))
    rc = w.s([ss, c0, w.inst('rescncf')], 'sylc', '( %s -> ( ( x e. %s |-> ( x ^c A ) ) |` ( 0 [,] N ) ) e. ( ( 0 [,] N ) -cn-> CC ) )' % (A, R0))
    rm = w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( ( x e. %s |-> ( x ^c A ) ) |` ( 0 [,] N ) ) = ( x e. ( 0 [,] N ) |-> ( x ^c A ) ) )' % (A, R0))
    w.qed([rc, rm], 'eqeltrrd' if False else 'syl6eqel' if False else 'eqeltrd', 'x') if False else None
    q = w.s([w.s([rm], 'eqcomd', '( %s -> ( x e. ( 0 [,] N ) |-> ( x ^c A ) ) = ( ( x e. %s |-> ( x ^c A ) ) |` ( 0 [,] N ) ) )' % (A, R0)), rc], 'eqeltrd', L.STATEMENTS['zl3ccx'])
    finish(w, q, 'zl3ccx')
    go(w)

# ---------------------------------------------------------------- zl3ibl
if want('zl3ibl'):
    w = W('zl3ibl', 'A function continuous on a closed interval is integrable on the open interval ( ~ cniccibl , ~ iblss ).')
    A, C = ante_of('zl3ibl')
    ar = D(w, A, 'simpll', [], 'A e. RR'); br = D(w, A, 'simplr', [], 'B e. RR'); fc = D(w, A, 'simpr', [], 'F e. ( ( A [,] B ) -cn-> CC )')
    ff = w.s([fc, w.inst('cncff')], 'syl', '( %s -> F : ( A [,] B ) --> CC )' % A)
    fn = w.s([ff, w.inst('ffn')], 'syl', '( %s -> F Fn ( A [,] B ) )' % A)
    FM = '( x e. ( A [,] B ) |-> ( F ` x ) )'
    d5 = w.s([fn, w.s([], 'dffn5', '( F Fn ( A [,] B ) <-> F = %s )' % FM)], 'sylib', '( %s -> F = %s )' % (A, FM))
    ib = w.s([ar, br, fc, w.inst('cniccibl')], 'syl3anc', '( %s -> F e. L^1 )' % A)
    ib2 = w.s([d5, ib], 'eqeltrrd', '( %s -> %s e. L^1 )' % (A, FM))
    Ax = '( %s /\\ x e. ( A [,] B ) )' % A
    ss = w.s([w.s([], 'ioossicc', '( A (,) B ) C_ ( A [,] B )')], 'a1i', '( %s -> ( A (,) B ) C_ ( A [,] B ) )' % A)
    FO = '( x e. ( A (,) B ) |-> ( F ` x ) )'
    i3 = w.s([ss, w.s([w.s([], 'ioombl', '( A (,) B ) e. dom vol')], 'a1i', '( %s -> ( A (,) B ) e. dom vol )' % A),
              w.s([w.s([], 'fvex', '( F ` x ) e. _V')], 'a1i', '( %s -> ( F ` x ) e. _V )' % Ax), ib2], 'iblss', '( %s -> %s e. L^1 )' % (A, FO))
    rs = w.s([w.s([d5], 'reseq1d', '( %s -> ( F |` ( A (,) B ) ) = ( %s |` ( A (,) B ) ) )' % (A, FM)),
              w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` ( A (,) B ) ) = %s )' % (A, FM, FO))], 'eqtrd', '( %s -> ( F |` ( A (,) B ) ) = %s )' % (A, FO))
    q = w.s([rs, i3], 'eqeltrd', L.STATEMENTS['zl3ibl'])
    finish(w, q, 'zl3ibl')
    go(w)


def wne0(w, C, wc, wpos):
    """( C -> W =/= 0 ) from ( C -> 0 < ( Re ` W ) )"""
    rw = D(w, C, 'recld', [wc], '( Re ` W ) e. RR')
    aw = D(w, C, 'abscld', [wc], '( abs ` W ) e. RR')
    ap = D(w, C, 'ltletrd', [a1(w, C, '0re', '0 e. RR'), rw, aw, wpos, w.s([wc, w.inst('releabs')], 'syl', '( %s -> ( Re ` W ) <_ ( abs ` W ) )' % C)], '0 < ( abs ` W )')
    return w.s([ap, w.s([wc, w.inst('absgt0')], 'syl', '( %s -> ( W =/= 0 <-> 0 < ( abs ` W ) ) )' % C)], 'mpbird', '( %s -> W =/= 0 )' % C)


def re_sub1(w, C, wc):
    """( C -> ( Re ` ( W - 1 ) ) = ( ( Re ` W ) - 1 ) )"""
    return w.s([E(w, C, 'resubd', [wc, a1(w, C, 'ax-1cn', '1 e. CC')], '( Re ` ( W - 1 ) )', '( ( Re ` W ) - ( Re ` 1 ) )'),
                E(w, C, 'oveq2d', [w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % C)], '( ( Re ` W ) - ( Re ` 1 ) )', '( ( Re ` W ) - 1 )')],
               'eqtrd', '( %s -> ( Re ` ( W - 1 ) ) = ( ( Re ` W ) - 1 ) )' % C)


def open_facts(w, C, N, e, ccl):
    """from ccl: ( C -> ( x e. ( 0 [,] N ) |-> e ) e. ( ( 0 [,] N ) -cn-> CC ) ):
    ( C -> ( x e. ( 0 (,) N ) |-> e ) e. ( ( 0 (,) N ) -cn-> CC ) ) and ( C -> ( x e. ( 0 (,) N ) |-> e ) e. L^1 ) ; needs N e. RR step"""
    MC = '( x e. ( 0 [,] %s ) |-> %s )' % (N, e)
    MO = '( x e. ( 0 (,) %s ) |-> %s )' % (N, e)
    ss = w.s([w.s([], 'ioossicc', '( 0 (,) %s ) C_ ( 0 [,] %s )' % (N, N))], 'a1i', '( %s -> ( 0 (,) %s ) C_ ( 0 [,] %s ) )' % (C, N, N))
    rm = w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` ( 0 (,) %s ) ) = %s )' % (C, MC, N, MO))
    rc = w.s([ss, ccl, w.inst('rescncf')], 'sylc', '( %s -> ( %s |` ( 0 (,) %s ) ) e. ( ( 0 (,) %s ) -cn-> CC ) )' % (C, MC, N, N))
    co = w.s([rm, rc], 'eqeltrrd', '( %s -> %s e. ( ( 0 (,) %s ) -cn-> CC ) )' % (C, MO, N))
    return co, rm, ss


def ibl_of(w, C, N, e, ccl, nr):
    co, rm, ss = open_facts(w, C, N, e, ccl)
    MC = '( x e. ( 0 [,] %s ) |-> %s )' % (N, e)
    MO = '( x e. ( 0 (,) %s ) |-> %s )' % (N, e)
    ib = w.s([w.s([w.s([a1(w, C, '0re', '0 e. RR'), nr], 'jca', '( %s -> ( 0 e. RR /\\ %s e. RR ) )' % (C, N)), ccl], 'jca',
                  '( %s -> ( ( 0 e. RR /\\ %s e. RR ) /\\ %s e. ( ( 0 [,] %s ) -cn-> CC ) ) )' % (C, N, MC, N)), w.inst('zl3ibl')], 'syl',
             '( %s -> ( %s |` ( 0 (,) %s ) ) e. L^1 )' % (C, MC, N))
    return co, w.s([rm, ib], 'eqeltrrd', '( %s -> %s e. L^1 )' % (C, MO))


# ---------------------------------------------------------------- zl3pint
if want('zl3pint'):
    w = W('zl3pint', '` S. ( 0 , N ) x ^ ( W - 1 ) dx = N ^ W / W ` for ` 1 < Re W ` ( ~ ftc2 with ~ zl3dvc ).')
    A, C = ante_of('zl3pint')
    wc = D(w, A, 'simpll', [], 'W e. CC'); re1 = D(w, A, 'simplr', [], '1 < ( Re ` W )'); nrp = D(w, A, 'simpr', [], 'N e. RR+')
    nr = D(w, A, 'rpred', [nrp], 'N e. RR')
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    cl0 = Closure(w, A, {'( Re ` W )': ('RR', rw)})
    wpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=cl0)
    wn = wne0(w, A, wc, wpos)
    wm = D(w, A, 'subcld', [wc, a1(w, A, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, A, [re1], '0 < ( ( Re ` W ) - 1 )', closure=cl0), re_sub1(w, A, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % A)
    c1 = w.s([w.s([w.s([wm, wmp], 'jca', '( %s -> ( ( W - 1 ) e. CC /\\ 0 < ( Re ` ( W - 1 ) ) ) )' % A), nrp], 'jca',
                  '( %s -> ( ( ( W - 1 ) e. CC /\\ 0 < ( Re ` ( W - 1 ) ) ) /\\ N e. RR+ ) )' % A), w.inst('zl3ccx')], 'syl',
             '( %s -> ( x e. ( 0 [,] N ) |-> ( x ^c ( W - 1 ) ) ) e. ( ( 0 [,] N ) -cn-> CC ) )' % A)
    co, ib = ibl_of(w, A, 'N', '( x ^c ( W - 1 ) )', c1, nr)
    cw = w.s([w.s([w.s([wc, wpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % A), nrp], 'jca', '( %s -> ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ N e. RR+ ) )' % A),
              w.inst('zl3ccx')], 'syl', '( %s -> ( x e. ( 0 [,] N ) |-> ( x ^c W ) ) e. ( ( 0 [,] N ) -cn-> CC ) )' % A)
    cl = Closure(w, A, {'W': ('CC', wc), 'N': ('RR', nr)})
    cl.have('W', 'ne0', wn)
    xss = w.s([w.s([w.s([a1(w, A, '0re', '0 e. RR'), nr, w.inst('iccssre')], 'syl2anc', '( %s -> ( 0 [,] N ) C_ RR )' % A), a1(w, A, 'ax-resscn', 'RR C_ CC')], 'sstrd',
               '( %s -> ( 0 [,] N ) C_ CC )' % A)], 'idi', '( %s -> ( 0 [,] N ) C_ CC )' % A)
    G = '( x e. ( 0 [,] N ) |-> ( ( x ^c W ) / W ) )'
    cg = cont(w, A, '( 0 [,] N )', '( ( x ^c W ) / W )', cl, xss, special={'( x ^c W )': cw})
    dv = w.s([w.s([w.s([wc, wn], 'jca', '( %s -> ( W e. CC /\\ W =/= 0 ) )' % A), nrp], 'jca', '( %s -> ( ( W e. CC /\\ W =/= 0 ) /\\ N e. RR+ ) )' % A), w.inst('zl3dvc')],
             'syl', '( %s -> ( RR _D %s ) = ( x e. ( 0 (,) N ) |-> ( x ^c ( W - 1 ) ) ) )' % (A, G))
    MO = '( x e. ( 0 (,) N ) |-> ( x ^c ( W - 1 ) ) )'
    n0 = D(w, A, 'rpge0d', [nrp], '0 <_ N')
    f2 = w.s([a1(w, A, '0re', '0 e. RR'), nr, n0, w.s([dv, co], 'eqeltrd', '( %s -> ( RR _D %s ) e. ( ( 0 (,) N ) -cn-> CC ) )' % (A, G)),
              w.s([dv, ib], 'eqeltrd', '( %s -> ( RR _D %s ) e. L^1 )' % (A, G)), cg], 'ftc2',
             '( %s -> S. ( 0 (,) N ) ( ( RR _D %s ) ` t ) _d t = ( ( %s ` N ) - ( %s ` 0 ) ) )' % (A, G, G, G))
    At = '( %s /\\ t e. ( 0 (,) N ) )' % A
    e1 = w.s([w.s([w.s([dv], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (At, G, MO))], 'fveq1d', '( %s -> ( ( RR _D %s ) ` t ) = ( %s ` t ) )' % (At, G, MO)),
              mptv(w, At, 'x', '( 0 (,) N )', '( x ^c ( W - 1 ) )', 't', D(w, At, 'simpr', [], 't e. ( 0 (,) N )'))[0]], 'eqtrd',
             '( %s -> ( ( RR _D %s ) ` t ) = ( t ^c ( W - 1 ) ) )' % (At, G))
    i1 = w.s([e1], 'itgeq2dv', '( %s -> S. ( 0 (,) N ) ( ( RR _D %s ) ` t ) _d t = S. ( 0 (,) N ) ( t ^c ( W - 1 ) ) _d t )' % (A, G))
    cb = w.s([w.s([], 'oveq1', '( x = t -> ( x ^c ( W - 1 ) ) = ( t ^c ( W - 1 ) ) )')], 'cbvitgv', 'S. ( 0 (,) N ) ( x ^c ( W - 1 ) ) _d x = S. ( 0 (,) N ) ( t ^c ( W - 1 ) ) _d t')
    xr = lambda t: w.s([t], 'rexrd', 'x')
    z0x = w.s([w.s([w.s([], '0re', '0 e. RR')], 'rexri', '0 e. RR*')], 'a1i', '( %s -> 0 e. RR* )' % A)
    nx = D(w, A, 'rexrd', [nr], 'N e. RR*')
    nin = w.s([z0x, nx, n0, w.inst('ubicc2')], 'syl3anc', '( %s -> N e. ( 0 [,] N ) )' % A)
    zin = w.s([z0x, nx, n0, w.inst('lbicc2')], 'syl3anc', '( %s -> 0 e. ( 0 [,] N ) )' % A)
    gN, _ = mptv(w, A, 'x', '( 0 [,] N )', '( ( x ^c W ) / W )', 'N', nin)
    g0, _ = mptv(w, A, 'x', '( 0 [,] N )', '( ( x ^c W ) / W )', '0', zin)
    z1 = w.s([w.s([wc, wn], 'jca' if False else 'idi', 'x')], 'idi', 'x') if False else None
    cx0 = w.s([wc, wn, w.inst('0cxp')], 'syl2anc', '( %s -> ( 0 ^c W ) = 0 )' % A)
    g0b = chain(w, A, ['( %s ` 0 )' % G, '( ( 0 ^c W ) / W )', '( 0 / W )', '0'],
                [g0, E(w, A, 'oveq1d', [cx0], '( ( 0 ^c W ) / W )', '( 0 / W )'), E(w, A, 'div0d', [wc, wn], '( 0 / W )', '0')])
    r = chain(w, A, ['( ( %s ` N ) - ( %s ` 0 ) )' % (G, G), '( ( ( N ^c W ) / W ) - 0 )', '( ( N ^c W ) / W )'],
              [E(w, A, 'oveq12d', [gN, g0b], '( ( %s ` N ) - ( %s ` 0 ) )' % (G, G), '( ( ( N ^c W ) / W ) - 0 )'),
               E(w, A, 'subid1d', [D(w, A, 'divcld', [D(w, A, 'cxpcld', [D(w, A, 'recnd', [nr], 'N e. CC'), wc], '( N ^c W ) e. CC'), wc, wn], '( ( N ^c W ) / W ) e. CC')],
                 '( ( ( N ^c W ) / W ) - 0 )', '( ( N ^c W ) / W )')])
    q = chain(w, A, ['S. ( 0 (,) N ) ( x ^c ( W - 1 ) ) _d x', 'S. ( 0 (,) N ) ( t ^c ( W - 1 ) ) _d t', 'S. ( 0 (,) N ) ( ( RR _D %s ) ` t ) _d t' % G,
                     '( ( %s ` N ) - ( %s ` 0 ) )' % (G, G), '( ( N ^c W ) / W )'],
              [w.s([cb], 'a1i', '( %s -> S. ( 0 (,) N ) ( x ^c ( W - 1 ) ) _d x = S. ( 0 (,) N ) ( t ^c ( W - 1 ) ) _d t )' % A), ('r', i1), f2, r])
    finish(w, q, 'zl3pint')
    go(w)


# ---------------------------------------------------------------- zl3dvp
if want('zl3dvp'):
    w = W('zl3dvp', 'The derivative of ` ( 1 - x / N ) ^ M ` on ` [ 0 , N ] ` ( ~ dvmptco , ~ dvexp , ~ dvmptresicc ).')
    A, C = ante_of('zl3dvp')
    nrp = D(w, A, 'simpl', [], 'N e. RR+'); mn = D(w, A, 'simpr', [], 'M e. NN')
    nr = D(w, A, 'rpred', [nrp], 'N e. RR'); nc = D(w, A, 'rpcnd', [nrp], 'N e. CC'); nn0 = D(w, A, 'rpne0d', [nrp], 'N =/= 0')
    mc = D(w, A, 'nncnd', [mn], 'M e. CC')
    S = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A)
    Ax = '( %s /\\ x e. CC )' % A
    xc = D(w, Ax, 'simpr', [], 'x e. CC')
    c1x = a1(w, Ax, 'ax-1cn', '1 e. CC'); ncx = D(w, Ax, 'adantr', [nc], 'N e. CC'); nnx = D(w, Ax, 'adantr', [nn0], 'N =/= 0')
    IN = '( 1 - ( x / N ) )'
    inc = D(w, Ax, 'subcld', [c1x, D(w, Ax, 'divcld', [xc, ncx, nnx], '( x / N ) e. CC')], '%s e. CC' % IN)
    did = w.s([S], 'dvmptid', '( %s -> ( CC _D ( x e. CC |-> x ) ) = ( x e. CC |-> 1 ) )' % A)
    ddiv = w.s([S, xc, c1x, did, nc, nn0], 'dvmptdivc', '( %s -> ( CC _D ( x e. CC |-> ( x / N ) ) ) = ( x e. CC |-> ( 1 / N ) ) )' % A)
    dc1 = w.s([S, a1(w, A, 'ax-1cn', '1 e. CC')], 'dvmptc', '( %s -> ( CC _D ( x e. CC |-> 1 ) ) = ( x e. CC |-> 0 ) )' % A)
    din = w.s([S, c1x, a1(w, Ax, '0cn', '0 e. CC'), dc1, D(w, Ax, 'divcld', [xc, ncx, nnx], '( x / N ) e. CC'), D(w, Ax, 'reccld', [ncx, nnx], '( 1 / N ) e. CC'), ddiv],
              'dvmptsub', '( %s -> ( CC _D ( x e. CC |-> %s ) ) = ( x e. CC |-> ( 0 - ( 1 / N ) ) ) )' % (A, IN))
    Ay = '( %s /\\ y e. CC )' % A
    yc = D(w, Ay, 'simpr', [], 'y e. CC')
    mn0 = w.s([D(w, Ay, 'adantr', [mn], 'M e. NN'), w.inst('nnm1nn0')], 'syl', '( %s -> ( M - 1 ) e. NN0 )' % Ay)
    dex = w.s([mn, w.inst('dvexp')], 'syl', '( %s -> ( CC _D ( y e. CC |-> ( y ^ M ) ) ) = ( y e. CC |-> ( M x. ( y ^ ( M - 1 ) ) ) ) )' % A)
    E1 = '( %s ^ M )' % IN
    F1 = '( M x. ( %s ^ ( M - 1 ) ) )' % IN
    e_ = w.s([], 'oveq1', '( y = %s -> ( y ^ M ) = %s )' % (IN, E1))
    f_ = w.s([w.s([], 'oveq1', '( y = %s -> ( y ^ ( M - 1 ) ) = ( %s ^ ( M - 1 ) ) )' % (IN, IN))], 'oveq2d', '( y = %s -> ( M x. ( y ^ ( M - 1 ) ) ) = %s )' % (IN, F1))
    dco = w.s([S, S, inc, D(w, Ax, 'subcld', [a1(w, Ax, '0cn', '0 e. CC'), D(w, Ax, 'reccld', [ncx, nnx], '( 1 / N ) e. CC')], '( 0 - ( 1 / N ) ) e. CC'),
               D(w, Ay, 'expcld', [yc, D(w, Ay, 'nnnn0d', [D(w, Ay, 'adantr', [mn], 'M e. NN')], 'M e. NN0')], '( y ^ M ) e. CC'),
               D(w, Ay, 'mulcld', [D(w, Ay, 'adantr', [mc], 'M e. CC'), D(w, Ay, 'expcld', [yc, mn0], '( y ^ ( M - 1 ) ) e. CC')], '( M x. ( y ^ ( M - 1 ) ) ) e. CC'),
               din, dex, e_, f_], 'dvmptco', '( %s -> ( CC _D ( x e. CC |-> %s ) ) = ( x e. CC |-> ( %s x. ( 0 - ( 1 / N ) ) ) ) )' % (A, E1, F1))
    mn0x = w.s([D(w, Ax, 'adantr', [mn], 'M e. NN'), w.inst('nnm1nn0')], 'syl', '( %s -> ( M - 1 ) e. NN0 )' % Ax)
    Bx = '( %s x. ( 0 - ( 1 / N ) ) )' % F1
    bxc = D(w, Ax, 'mulcld', [D(w, Ax, 'mulcld', [D(w, Ax, 'adantr', [mc], 'M e. CC'), D(w, Ax, 'expcld', [inc, mn0x], '( %s ^ ( M - 1 ) ) e. CC' % IN)], '%s e. CC' % F1),
                              D(w, Ax, 'subcld', [a1(w, Ax, '0cn', '0 e. CC'), D(w, Ax, 'reccld', [ncx, nnx], '( 1 / N ) e. CC')], '( 0 - ( 1 / N ) ) e. CC')], '%s e. CC' % Bx)
    FM = '( x e. CC |-> %s )' % E1
    ric = w.s([w.s([], 'eqid', '%s = %s' % (FM, FM)), D(w, Ax, 'expcld', [inc, D(w, Ax, 'nnnn0d', [D(w, Ax, 'adantr', [mn], 'M e. NN')], 'M e. NN0')], '%s e. CC' % E1),
               dco, bxc, a1(w, A, '0re', '0 e. RR'), nr], 'dvmptresicc', '( %s -> ( RR _D ( x e. ( 0 [,] N ) |-> %s ) ) = ( x e. ( 0 (,) N ) |-> %s ) )' % (A, E1, Bx))
    Aq = '( %s /\\ x e. ( 0 (,) N ) )' % A
    xq = D(w, Aq, 'recnd', [w.s([w.s([w.s([], 'ioossre', '( 0 (,) N ) C_ RR')], 'a1i', '( %s -> ( 0 (,) N ) C_ RR )' % Aq), D(w, Aq, 'simpr', [], 'x e. ( 0 (,) N )')],
                                'sseldd', '( %s -> x e. RR )' % Aq)], 'x e. CC')
    ncq = D(w, Aq, 'adantr', [nc], 'N e. CC'); nnq = D(w, Aq, 'adantr', [nn0], 'N =/= 0'); mcq = D(w, Aq, 'adantr', [mc], 'M e. CC')
    P1 = '( %s ^ ( M - 1 ) )' % IN
    p1c = D(w, Aq, 'expcld', [D(w, Aq, 'subcld', [a1(w, Aq, 'ax-1cn', '1 e. CC'), D(w, Aq, 'divcld', [xq, ncq, nnq], '( x / N ) e. CC')], '%s e. CC' % IN),
                              w.s([D(w, Aq, 'adantr', [mn], 'M e. NN'), w.inst('nnm1nn0')], 'syl', '( %s -> ( M - 1 ) e. NN0 )' % Aq)], '%s e. CC' % P1)
    rn = D(w, Aq, 'reccld', [ncq, nnq], '( 1 / N ) e. CC')
    mp = D(w, Aq, 'mulcld', [mcq, p1c], '( M x. %s ) e. CC' % P1)
    T0 = Bx; T1 = '( ( M x. %s ) x. -u ( 1 / N ) )' % P1; T2 = '-u ( ( M x. %s ) x. ( 1 / N ) )' % P1
    T3 = '-u ( ( M x. ( 1 / N ) ) x. %s )' % P1; T4 = '-u ( ( M / N ) x. %s )' % P1; T5 = '( -u ( M / N ) x. %s )' % P1
    s1 = E(w, Aq, 'oveq2d', [w.s([w.s([w.s([], 'df-neg', '-u ( 1 / N ) = ( 0 - ( 1 / N ) )')], 'eqcomi', '( 0 - ( 1 / N ) ) = -u ( 1 / N )')], 'a1i',
                                 '( %s -> ( 0 - ( 1 / N ) ) = -u ( 1 / N ) )' % Aq)], T0, T1)
    s2 = E(w, Aq, 'mulneg2d', [mp, rn], T1, T2)
    s3 = E(w, Aq, 'negeqd', [E(w, Aq, 'mul32d', [mcq, p1c, rn], '( ( M x. %s ) x. ( 1 / N ) )' % P1, '( ( M x. ( 1 / N ) ) x. %s )' % P1)], T2, T3)
    s4 = E(w, Aq, 'negeqd', [E(w, Aq, 'oveq1d', [w.s([E(w, Aq, 'divrecd', [mcq, ncq, nnq], '( M / N )', '( M x. ( 1 / N ) )')], 'eqcomd',
                                                      '( %s -> ( M x. ( 1 / N ) ) = ( M / N ) )' % Aq)], '( ( M x. ( 1 / N ) ) x. %s )' % P1, '( ( M / N ) x. %s )' % P1)], T3, T4)
    s5 = w.s([E(w, Aq, 'mulneg1d', [D(w, Aq, 'divcld', [mcq, ncq, nnq], '( M / N ) e. CC'), p1c], T5, T4)], 'eqcomd', '( %s -> %s = %s )' % (Aq, T4, T5))
    sim = chain(w, Aq, [T0, T1, T2, T3, T4, T5], [s1, s2, s3, s4, s5])
    m = w.s([sim], 'mpteq2dva', '( %s -> ( x e. ( 0 (,) N ) |-> %s ) = ( x e. ( 0 (,) N ) |-> %s ) )' % (A, T0, T5))
    q = w.s([ric, m], 'eqtrd', 'x')
    finish(w, q, 'zl3dvp')
    go(w)


def ccx(w, C, Aexp, a_c, a_pos, nrp, N='N'):
    """( C -> ( x e. ( 0 [,] N ) |-> ( x ^c Aexp ) ) e. ( ( 0 [,] N ) -cn-> CC ) ) via zl3ccx"""
    return w.s([w.s([w.s([a_c, a_pos], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C, Aexp, Aexp)), nrp], 'jca',
                    '( %s -> ( ( %s e. CC /\\ 0 < ( Re ` %s ) ) /\\ %s e. RR+ ) )' % (C, Aexp, Aexp, N)), w.inst('zl3ccx')], 'syl',
               '( %s -> ( x e. ( 0 [,] %s ) |-> ( x ^c %s ) ) e. ( ( 0 [,] %s ) -cn-> CC ) )' % (C, N, Aexp, N))


def dom_cc(w, C, dom, nr):
    """( C -> dom C_ CC ) for dom = ( 0 [,] N ) or ( 0 (,) N )"""
    if '[,]' in dom:
        s1 = w.s([a1(w, C, '0re', '0 e. RR'), nr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (C, dom))
    else:
        s1 = w.s([w.s([], 'ioossre', '%s C_ RR' % dom)], 'a1i', '( %s -> %s C_ RR )' % (C, dom))
    return w.s([s1, a1(w, C, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (C, dom))


def dom_x(w, C, dom, nr, x='x'):
    """context ( C /\\ x e. dom ): step x e. CC"""
    Cx = '( %s /\\ %s e. %s )' % (C, x, dom)
    return Cx, w.s([w.s([dom_cc(w, C, dom, nr)], 'adantr', '( %s -> %s C_ CC )' % (Cx, dom)), D(w, Cx, 'simpr', [], '%s e. %s' % (x, dom))], 'sseldd', '( %s -> %s e. CC )' % (Cx, x))


# ---------------------------------------------------------------- zl3jrec
if want('zl3jrec'):
    w = W('zl3jrec', 'Integration by parts in ` J ( K , W ) = S. ( 0 , N ) ( 1 - x / N ) ^ K x ^ ( W - 1 ) dx ` : '
          '` J ( K + 1 , W ) = ( K + 1 ) / ( N W ) J ( K , W + 1 ) ` ( ~ itgparts , ~ zl3dvp , ~ zl3dvc ).')
    A, Cc = ante_of('zl3jrec')
    wc = D(w, A, 'simpll', [], 'W e. CC'); re1 = D(w, A, 'simplr', [], '1 < ( Re ` W )')
    nrp = D(w, A, 'simprl', [], 'N e. RR+'); kn = D(w, A, 'simprr', [], 'K e. NN0')
    nr = D(w, A, 'rpred', [nrp], 'N e. RR'); nc = D(w, A, 'rpcnd', [nrp], 'N e. CC'); nn0 = D(w, A, 'rpne0d', [nrp], 'N =/= 0')
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    cl0 = Closure(w, A, {'( Re ` W )': ('RR', rw)})
    wpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=cl0)
    wn = wne0(w, A, wc, wpos)
    wm = D(w, A, 'subcld', [wc, a1(w, A, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, A, [re1], '0 < ( ( Re ` W ) - 1 )', closure=cl0), re_sub1(w, A, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % A)
    k1n = w.s([kn, w.inst('nn0p1nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A)
    k1c = D(w, A, 'nncnd', [k1n], '( K + 1 ) e. CC')
    kc = D(w, A, 'nn0cnd', [kn], 'K e. CC')
    cl = Closure(w, A, {'W': ('CC', wc), 'N': ('RR', nr), 'K': ('NN0', kn), '( K + 1 )': ('NN', k1n)})
    cl.have('W', 'ne0', wn); cl.have('N', 'ne0', nn0)
    cl.have('( N x. W )', 'CC', D(w, A, 'mulcld', [nc, wc], '( N x. W ) e. CC'))
    cl.have('( N x. W )', 'ne0', D(w, A, 'mulne0d', [nc, wc, nn0, wn], '( N x. W ) =/= 0'))
    ICC, IOO = '( 0 [,] N )', '( 0 (,) N )'
    xcc = dom_cc(w, A, ICC, nr); xoo = dom_cc(w, A, IOO, nr)
    cW = ccx(w, A, 'W', wc, wpos, nrp); cW1 = ccx(w, A, '( W - 1 )', wm, wmp, nrp)
    P1 = '( ( 1 - ( x / N ) ) ^ ( K + 1 ) )'; PK = '( ( 1 - ( x / N ) ) ^ K )'
    XW = '( x ^c W )'; XW1 = '( x ^c ( W - 1 ) )'
    Cf = '( %s / W )' % XW
    CK = '-u ( ( K + 1 ) / N )'
    Bf = '( %s x. %s )' % (CK, PK)
    sp = {XW: cW, XW1: cW1}
    ca = cont(w, A, ICC, P1, cl, xcc)
    cc_ = cont(w, A, ICC, Cf, cl, xcc, special=sp)
    cad = cont(w, A, ICC, '( %s x. %s )' % (P1, XW1), cl, xcc, special=sp)
    cbc = cont(w, A, ICC, '( %s x. %s )' % (Bf, Cf), cl, xcc, special=sp)
    cpk = cont(w, A, ICC, '( %s x. %s )' % (PK, XW), cl, xcc, special=sp)
    cb, _, _ = open_facts(w, A, 'N', Bf, cont(w, A, ICC, Bf, cl, xcc))
    cd, _, _ = open_facts(w, A, 'N', XW1, cW1)
    _, iad = ibl_of(w, A, 'N', '( %s x. %s )' % (P1, XW1), cad, nr)
    _, ibc = ibl_of(w, A, 'N', '( %s x. %s )' % (Bf, Cf), cbc, nr)
    _, ipk = ibl_of(w, A, 'N', '( %s x. %s )' % (PK, XW), cpk, nr)
    # derivatives
    dp = w.s([w.s([nrp, k1n], 'jca', '( %s -> ( N e. RR+ /\\ ( K + 1 ) e. NN ) )' % A), w.inst('zl3dvp')], 'syl',
             '( %s -> ( RR _D ( x e. %s |-> %s ) ) = ( x e. %s |-> ( -u ( ( K + 1 ) / N ) x. ( ( 1 - ( x / N ) ) ^ ( ( K + 1 ) - 1 ) ) ) ) )' % (A, ICC, P1, IOO))
    Ao, xo = dom_x(w, A, IOO, nr)
    pk1 = E(w, Ao, 'oveq2d', [E(w, Ao, 'oveq2d', [E(w, Ao, 'pncand', [D(w, Ao, 'adantr', [kc], 'K e. CC'), a1(w, Ao, 'ax-1cn', '1 e. CC')], '( ( K + 1 ) - 1 )', 'K')],
                                '( ( 1 - ( x / N ) ) ^ ( ( K + 1 ) - 1 ) )', PK)], '( -u ( ( K + 1 ) / N ) x. ( ( 1 - ( x / N ) ) ^ ( ( K + 1 ) - 1 ) ) )', Bf)
    da = w.s([dp, w.s([pk1], 'mpteq2dva', '( %s -> ( x e. %s |-> ( -u ( ( K + 1 ) / N ) x. ( ( 1 - ( x / N ) ) ^ ( ( K + 1 ) - 1 ) ) ) ) = ( x e. %s |-> %s ) )' % (A, IOO, IOO, Bf))],
             'eqtrd', '( %s -> ( RR _D ( x e. %s |-> %s ) ) = ( x e. %s |-> %s ) )' % (A, ICC, P1, IOO, Bf))
    dc = w.s([w.s([w.s([wc, wn], 'jca', '( %s -> ( W e. CC /\\ W =/= 0 ) )' % A), nrp], 'jca', '( %s -> ( ( W e. CC /\\ W =/= 0 ) /\\ N e. RR+ ) )' % A), w.inst('zl3dvc')],
             'syl', '( %s -> ( RR _D ( x e. %s |-> %s ) ) = ( x e. %s |-> %s ) )' % (A, ICC, Cf, IOO, XW1))
    # boundary values
    Ae = '( %s /\\ x = 0 )' % A
    xe = D(w, Ae, 'simpr', [], 'x = 0')
    xce = w.s([xe, a1(w, Ae, '0cn', '0 e. CC')], 'eqeltrd', '( %s -> x e. CC )' % Ae)
    cle = Closure(w, Ae, {'x': ('CC', xce), 'W': ('CC', D(w, Ae, 'adantr', [wc], 'W e. CC')), 'N': ('RR', D(w, Ae, 'adantr', [nr], 'N e. RR')),
                          '( K + 1 )': ('NN', D(w, Ae, 'adantr', [k1n], '( K + 1 ) e. NN'))})
    cle.have('N', 'ne0', D(w, Ae, 'adantr', [nn0], 'N =/= 0'))
    c0 = chain(w, Ae, [XW, '( 0 ^c W )', '0'], [E(w, Ae, 'oveq1d', [xe], XW, '( 0 ^c W )'),
                                                w.s([D(w, Ae, 'adantr', [wc], 'W e. CC'), D(w, Ae, 'adantr', [wn], 'W =/= 0'), w.inst('0cxp')], 'syl2anc', '( %s -> ( 0 ^c W ) = 0 )' % Ae)])
    cf0 = chain(w, Ae, [Cf, '( 0 / W )', '0'], [E(w, Ae, 'oveq1d', [c0], Cf, '( 0 / W )'), E(w, Ae, 'div0d', [D(w, Ae, 'adantr', [wc], 'W e. CC'), D(w, Ae, 'adantr', [wn], 'W =/= 0')], '( 0 / W )', '0')])
    ee = chain(w, Ae, ['( %s x. %s )' % (P1, Cf), '( %s x. 0 )' % P1, '0'], [E(w, Ae, 'oveq2d', [cf0], '( %s x. %s )' % (P1, Cf), '( %s x. 0 )' % P1),
                                                                         E(w, Ae, 'mul01d', [cle.mem(P1, 'CC')], '( %s x. 0 )' % P1, '0')])
    Af = '( %s /\\ x = N )' % A
    xf = D(w, Af, 'simpr', [], 'x = N')
    ncf = D(w, Af, 'adantr', [nc], 'N e. CC'); nnf = D(w, Af, 'adantr', [nn0], 'N =/= 0')
    xcf = w.s([xf, ncf], 'eqeltrd', '( %s -> x e. CC )' % Af)
    clf = Closure(w, Af, {'x': ('CC', xcf), 'W': ('CC', D(w, Af, 'adantr', [wc], 'W e. CC')), 'N': ('RR', D(w, Af, 'adantr', [nr], 'N e. RR'))})
    clf.have('W', 'ne0', D(w, Af, 'adantr', [wn], 'W =/= 0'))
    p0 = chain(w, Af, [P1, '( ( 1 - ( N / N ) ) ^ ( K + 1 ) )', '( ( 1 - 1 ) ^ ( K + 1 ) )', '( 0 ^ ( K + 1 ) )', '0'],
               [E(w, Af, 'oveq1d', [E(w, Af, 'oveq2d', [E(w, Af, 'oveq1d', [xf], '( x / N )', '( N / N )')], '( 1 - ( x / N ) )', '( 1 - ( N / N ) )')], P1, '( ( 1 - ( N / N ) ) ^ ( K + 1 ) )'),
                E(w, Af, 'oveq1d', [E(w, Af, 'oveq2d', [w.s([ncf, nnf, w.inst('divid')], 'syl2anc', '( %s -> ( N / N ) = 1 )' % Af)], '( 1 - ( N / N ) )', '( 1 - 1 )')],
                  '( ( 1 - ( N / N ) ) ^ ( K + 1 ) )', '( ( 1 - 1 ) ^ ( K + 1 ) )'),
                E(w, Af, 'oveq1d', [E(w, Af, 'subidd', [a1(w, Af, 'ax-1cn', '1 e. CC')], '( 1 - 1 )', '0')], '( ( 1 - 1 ) ^ ( K + 1 ) )', '( 0 ^ ( K + 1 ) )'),
                w.s([D(w, Af, 'adantr', [k1n], '( K + 1 ) e. NN'), w.inst('0exp')], 'syl', '( %s -> ( 0 ^ ( K + 1 ) ) = 0 )' % Af)])
    ff_ = chain(w, Af, ['( %s x. %s )' % (P1, Cf), '( 0 x. %s )' % Cf, '0'], [E(w, Af, 'oveq1d', [p0], '( %s x. %s )' % (P1, Cf), '( 0 x. %s )' % Cf),
                                                                         E(w, Af, 'mul02d', [clf.mem(Cf, 'CC')], '( 0 x. %s )' % Cf, '0')])
    ip = w.s([a1(w, A, '0re', '0 e. RR'), nr, D(w, A, 'rpge0d', [nrp], '0 <_ N'), ca, cc_, cb, cd, iad, ibc, da, dc, ee, ff_], 'itgparts',
             '( %s -> S. %s ( %s x. %s ) _d x = ( ( 0 - 0 ) - S. %s ( %s x. %s ) _d x ) )' % (A, IOO, P1, XW1, IOO, Bf, Cf))
    # the integrand B x. C = c x. ( PK x. x ^c ( ( W + 1 ) - 1 ) )
    cst = '-u ( ( K + 1 ) / ( N x. W ) )'
    XWp = '( x ^c ( ( W + 1 ) - 1 ) )'
    wco = D(w, Ao, 'adantr', [wc], 'W e. CC'); wno = D(w, Ao, 'adantr', [wn], 'W =/= 0')
    clo = Closure(w, Ao, {'x': ('CC', xo), 'W': ('CC', wco), 'N': ('RR', D(w, Ao, 'adantr', [nr], 'N e. RR')), 'K': ('NN0', D(w, Ao, 'adantr', [kn], 'K e. NN0')),
                          '( K + 1 )': ('NN', D(w, Ao, 'adantr', [k1n], '( K + 1 ) e. NN'))})
    clo.have('W', 'ne0', wno); clo.have('N', 'ne0', D(w, Ao, 'adantr', [nn0], 'N =/= 0'))
    q1 = '( ( K + 1 ) / N )'
    t0 = '( %s x. %s )' % (Bf, Cf)
    t1 = '( %s x. ( ( 1 / W ) x. %s ) )' % (Bf, XW)
    t2 = '( ( %s x. ( 1 / W ) ) x. ( %s x. %s ) )' % (CK, PK, XW)
    t3 = '( -u ( %s x. ( 1 / W ) ) x. ( %s x. %s ) )' % (q1, PK, XW)
    t4 = '( -u ( %s / W ) x. ( %s x. %s ) )' % (q1, PK, XW)
    t5 = '( %s x. ( %s x. %s ) )' % (cst, PK, XW)
    t6 = '( %s x. ( %s x. %s ) )' % (cst, PK, XWp)
    cq1 = clo.mem(q1, 'CC'); crw = clo.mem('( 1 / W )', 'CC'); cpk_ = clo.mem(PK, 'CC'); cxw = clo.mem(XW, 'CC')
    u1 = E(w, Ao, 'oveq2d', [E(w, Ao, 'divrec2d', [cxw, wco, wno], Cf, '( ( 1 / W ) x. %s )' % XW)], t0, t1)
    u2 = E(w, Ao, 'mul4d', [clo.mem(CK, 'CC'), cpk_, crw, cxw], t1, t2)
    u3 = E(w, Ao, 'oveq1d', [E(w, Ao, 'mulneg1d', [cq1, crw], '( %s x. ( 1 / W ) )' % CK, '-u ( %s x. ( 1 / W ) )' % q1)], t2, t3)
    u4 = E(w, Ao, 'oveq1d', [E(w, Ao, 'negeqd', [w.s([E(w, Ao, 'divrecd', [cq1, wco, wno], '( %s / W )' % q1, '( %s x. ( 1 / W ) )' % q1)], 'eqcomd',
                                                     '( %s -> ( %s x. ( 1 / W ) ) = ( %s / W ) )' % (Ao, q1, q1))], '-u ( %s x. ( 1 / W ) )' % q1, '-u ( %s / W )' % q1)], t3, t4)
    u5 = E(w, Ao, 'oveq1d', [E(w, Ao, 'negeqd', [E(w, Ao, 'divdiv1d', [clo.mem('( K + 1 )', 'CC'), clo.mem('N', 'CC'), wco, clo.ne0('N'), wno], '( %s / W )' % q1, '( ( K + 1 ) / ( N x. W ) )')],
                                               '-u ( %s / W )' % q1, cst)], t4, t5)
    u6 = E(w, Ao, 'oveq2d', [E(w, Ao, 'oveq2d', [E(w, Ao, 'oveq2d', [w.s([E(w, Ao, 'pncand', [wco, a1(w, Ao, 'ax-1cn', '1 e. CC')], '( ( W + 1 ) - 1 )', 'W')], 'eqcomd',
                                                                       '( %s -> W = ( ( W + 1 ) - 1 ) )' % Ao)], XW, XWp)], '( %s x. %s )' % (PK, XW), '( %s x. %s )' % (PK, XWp))], t5, t6)
    pw = chain(w, Ao, [t0, t1, t2, t3, t4, t5, t6], [u1, u2, u3, u4, u5, u6])
    i2 = w.s([pw], 'itgeq2dv', '( %s -> S. %s %s _d x = S. %s %s _d x )' % (A, IOO, t0, IOO, t6))
    # L^1 of ( PK x. XWp ) from ipk
    Ao2 = Ao
    pe = E(w, Ao, 'oveq2d', [E(w, Ao, 'oveq2d', [w.s([E(w, Ao, 'pncand', [wco, a1(w, Ao, 'ax-1cn', '1 e. CC')], '( ( W + 1 ) - 1 )', 'W')], 'eqcomd',
                                                     '( %s -> W = ( ( W + 1 ) - 1 ) )' % Ao)], XW, XWp)], '( %s x. %s )' % (PK, XW), '( %s x. %s )' % (PK, XWp))
    ipk2 = w.s([w.s([pe], 'mpteq2dva', '( %s -> ( x e. %s |-> ( %s x. %s ) ) = ( x e. %s |-> ( %s x. %s ) ) )' % (A, IOO, PK, XW, IOO, PK, XWp)), ipk], 'eqeltrrd',
               '( %s -> ( x e. %s |-> ( %s x. %s ) ) e. L^1 )' % (A, IOO, PK, XWp))
    cstc = cl.mem(cst, 'CC')
    im = w.s([cstc, w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PK, XWp))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Ao, PK, XWp)), ipk2], 'itgmulc2',
             '( %s -> ( %s x. S. %s ( %s x. %s ) _d x ) = S. %s %s _d x )' % (A, cst, IOO, PK, XWp, IOO, t6))
    JK = L.JN('N', 'K', '( W + 1 )')
    assert JK == 'S. %s ( %s x. %s ) _d x' % (IOO, PK, XWp), JK
    I2 = 'S. %s %s _d x' % (IOO, t0)
    jkc = w.s([w.s([w.s([], 'itgcl' if False else 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    jkc = w.s([w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PK, XWp))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Ao, PK, XWp)), ipk2], 'itgcl', '( %s -> %s e. CC )' % (A, JK))
    R0_ = '( ( 0 - 0 ) - %s )' % I2
    r1 = E(w, A, 'oveq2d', [w.s([i2, w.s([im], 'eqcomd', '( %s -> S. %s %s _d x = ( %s x. %s ) )' % (A, IOO, t6, cst, JK))], 'eqtrd',
                                '( %s -> %s = ( %s x. %s ) )' % (A, I2, cst, JK))], R0_, '( ( 0 - 0 ) - ( %s x. %s ) )' % (cst, JK))
    CJ = '( %s x. %s )' % (cst, JK)
    r2 = E(w, A, 'oveq1d', [E(w, A, 'subidd', [a1(w, A, '0cn', '0 e. CC')], '( 0 - 0 )', '0')], '( ( 0 - 0 ) - %s )' % CJ, '( 0 - %s )' % CJ)
    r3 = w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (CJ, CJ))], 'a1i', '( %s -> -u %s = ( 0 - %s ) )' % (A, CJ, CJ))
    POS = '( ( K + 1 ) / ( N x. W ) )'
    r4 = w.s([E(w, A, 'mulneg1d', [cstc, jkc], '( -u %s x. %s )' % (cst, JK), '-u %s' % CJ)], 'eqcomd', '( %s -> -u %s = ( -u %s x. %s ) )' % (A, CJ, cst, JK))
    r5 = E(w, A, 'oveq1d', [E(w, A, 'negnegd', [cl.mem(POS, 'CC')], '-u %s' % cst, POS)], '( -u %s x. %s )' % (cst, JK), '( %s x. %s )' % (POS, JK))
    q = chain(w, A, [L.JN('N', '( K + 1 )', 'W'), R0_, '( ( 0 - 0 ) - %s )' % CJ, '( 0 - %s )' % CJ, '-u %s' % CJ, '( -u %s x. %s )' % (cst, JK), '( %s x. %s )' % (POS, JK)],
              [ip, r1, r2, ('r', r3), r4, r5])
    finish(w, q, 'zl3jrec')
    go(w)


def induct(w, ph, x, psi, base_fn, step_fn, target, kmem):
    """nn0indd on psi(x) (a wff text in the letter x); base_fn(ctx) -> step of ( ph -> psi(0) );
    step_fn(ctx, th_step) -> step of ( ctx -> psi(y+1) ) with ctx = ( ( ph /\\ y e. NN0 ) /\\ psi(y) );
    returns ( ph -> psi(target) ) given kmem: ( ph -> target e. NN0 )"""
    def sub(t):
        idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, t, x, t))
        st, val = w.wcongr(psi, {x: t}, '%s = %s' % (x, t), {x: idx})
        return st, val
    s0, v0 = sub('0'); sy, vy = sub('y'); s1, v1 = sub('( y + 1 )'); sa, va = sub(target)
    b = base_fn(ph, v0)
    ctx = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (ph, vy)
    st = step_fn(ctx, D(w, ctx, 'simpr', [], vy), vy, v1)
    ind = w.s([s0, sy, s1, sa, b, st], 'nn0indd', '( ( %s /\\ %s e. NN0 ) -> %s )' % (ph, target, va))
    return w.s([w.s([w.s([], 'id', '( %s -> %s )' % (ph, ph)), kmem], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (ph, ph, target)), ind], 'syl', '( %s -> %s )' % (ph, va))


# ---------------------------------------------------------------- zl3rfl
if want('zl3rfl'):
    w = W('zl3rfl', 'The rising factorial splits off its first factor: ` A ( A + 1 ) ... ( A + K ) = A ( ( A + 1 ) ... ( A + K ) ) ` ( induction with ~ risefacp1 ).')
    A, Cc = ante_of('zl3rfl')
    ph = 'A e. CC'
    psi = '( A RiseFac ( n + 1 ) ) = ( A x. ( ( A + 1 ) RiseFac n ) )'

    def base(ph_, v0):
        ac = w.s([], 'id', '( %s -> %s )' % (ph_, ph_))
        a1c = D(w, ph_, 'addcld', [ac, a1(w, ph_, 'ax-1cn', '1 e. CC')], '( A + 1 ) e. CC')
        l = chain(w, ph_, ['( A RiseFac ( 0 + 1 ) )', '( A RiseFac 1 )', 'A'],
                  [E(w, ph_, 'oveq2d', [w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % ph_)], '( A RiseFac ( 0 + 1 ) )', '( A RiseFac 1 )'),
                   w.s([ac, w.inst('risefac1')], 'syl', '( %s -> ( A RiseFac 1 ) = A )' % ph_)])
        r = chain(w, ph_, ['( A x. ( ( A + 1 ) RiseFac 0 ) )', '( A x. 1 )', 'A'],
                  [E(w, ph_, 'oveq2d', [w.s([a1c, w.inst('risefac0')], 'syl', '( %s -> ( ( A + 1 ) RiseFac 0 ) = 1 )' % ph_)], '( A x. ( ( A + 1 ) RiseFac 0 ) )', '( A x. 1 )'),
                   E(w, ph_, 'mulridd', [ac], '( A x. 1 )', 'A')])
        return w.s([l, r], 'eqtr4d', '( %s -> %s )' % (ph_, v0))

    def step(ctx, th, vy, v1):
        ac = D(w, ctx, 'simpll', [], 'A e. CC'); yn = D(w, ctx, 'simplr', [], 'y e. NN0')
        yc = D(w, ctx, 'nn0cnd', [yn], 'y e. CC')
        y1n = w.s([yn, w.inst('peano2nn0')], 'syl', '( %s -> ( y + 1 ) e. NN0 )' % ctx)
        a1c = D(w, ctx, 'addcld', [ac, a1(w, ctx, 'ax-1cn', '1 e. CC')], '( A + 1 ) e. CC')
        rfy = '( ( A + 1 ) RiseFac y )'
        rfyc = w.s([a1c, yn, w.inst('risefaccl')], 'syl2anc', '( %s -> %s e. CC )' % (ctx, rfy))
        T0 = '( A RiseFac ( ( y + 1 ) + 1 ) )'
        T1 = '( ( A RiseFac ( y + 1 ) ) x. ( A + ( y + 1 ) ) )'
        T2 = '( ( A x. %s ) x. ( A + ( y + 1 ) ) )' % rfy
        T3 = '( A x. ( %s x. ( A + ( y + 1 ) ) ) )' % rfy
        T4 = '( A x. ( %s x. ( ( A + 1 ) + y ) ) )' % rfy
        T5 = '( A x. ( ( A + 1 ) RiseFac ( y + 1 ) ) )'
        e1 = w.s([ac, y1n, w.inst('risefacp1')], 'syl2anc', '( %s -> %s = %s )' % (ctx, T0, T1))
        e2 = E(w, ctx, 'oveq1d', [th], T1, T2)
        apy = D(w, ctx, 'addcld', [ac, D(w, ctx, 'addcld', [yc, a1(w, ctx, 'ax-1cn', '1 e. CC')], '( y + 1 ) e. CC')], '( A + ( y + 1 ) ) e. CC')
        e3 = E(w, ctx, 'mulassd', [ac, rfyc, apy], T2, T3)
        c1 = a1(w, ctx, 'ax-1cn', '1 e. CC')
        aa = chain(w, ctx, ['( A + ( y + 1 ) )', '( ( A + y ) + 1 )', '( ( A + 1 ) + y )'],
                   [('r', E(w, ctx, 'addassd', [ac, yc, c1], '( ( A + y ) + 1 )', '( A + ( y + 1 ) )')), ('r', E(w, ctx, 'add32d', [ac, c1, yc], '( ( A + 1 ) + y )', '( ( A + y ) + 1 )'))])
        e4 = E(w, ctx, 'oveq2d', [E(w, ctx, 'oveq2d', [aa], '( %s x. ( A + ( y + 1 ) ) )' % rfy, '( %s x. ( ( A + 1 ) + y ) )' % rfy)], T3, T4)
        e5 = E(w, ctx, 'oveq2d', [w.s([w.s([a1c, yn, w.inst('risefacp1')], 'syl2anc', '( %s -> ( ( A + 1 ) RiseFac ( y + 1 ) ) = ( %s x. ( ( A + 1 ) + y ) ) )' % (ctx, rfy))],
                                      'eqcomd', '( %s -> ( %s x. ( ( A + 1 ) + y ) ) = ( ( A + 1 ) RiseFac ( y + 1 ) ) )' % (ctx, rfy))],
               T4, T5)
        return chain(w, ctx, [T0, T1, T2, T3, T4, T5], [e1, e2, e3, e4, e5])
    ind = induct(w, ph, 'n', psi, base, step, 'K', None) if False else None
    ph2 = A
    # use ph = ( A e. CC /\ K e. NN0 ) directly
    def base2(ph_, v0):
        return base(ph_, v0)
    q = induct(w, 'A e. CC', 'n', psi, base, step, 'K', w.s([], 'idi', 'x')) if False else None
    # manual: induction under ph = A e. CC, then import
    s0 = None
    idx = lambda t: w.s([], 'id', '( n = %s -> n = %s )' % (t, t))
    def sub(t):
        st, val = w.wcongr(psi, {'n': t}, 'n = %s' % t, {'n': idx(t)})
        return st, val
    a0, v0 = sub('0'); ay, vy = sub('y'); a1_, v1 = sub('( y + 1 )'); ak, vk = sub('K')
    b = base('A e. CC', v0)
    ctx = '( ( A e. CC /\\ y e. NN0 ) /\\ %s )' % vy
    st = step(ctx, D(w, ctx, 'simpr', [], vy), vy, v1)
    ind = w.s([a0, ay, a1_, ak, b, st], 'nn0indd', '( ( A e. CC /\\ K e. NN0 ) -> %s )' % vk)
    finish(w, ind, 'zl3rfl')
    go(w)


def wne0v(w, C, v, vc, vpos):
    rv = D(w, C, 'recld', [vc], '( Re ` %s ) e. RR' % v)
    av = D(w, C, 'abscld', [vc], '( abs ` %s ) e. RR' % v)
    ap = D(w, C, 'ltletrd', [a1(w, C, '0re', '0 e. RR'), rv, av, vpos, w.s([vc, w.inst('releabs')], 'syl', '( %s -> ( Re ` %s ) <_ ( abs ` %s ) )' % (C, v, v))], '0 < ( abs ` %s )' % v)
    return w.s([ap, w.s([vc, w.inst('absgt0')], 'syl', '( %s -> ( %s =/= 0 <-> 0 < ( abs ` %s ) ) )' % (C, v, v))], 'mpbird', '( %s -> %s =/= 0 )' % (C, v))



def jn_eq_sub_w(w, n, a, b, PSIw=None, N='N'):
    """( a = b -> ( ( 1 < ( Re ` a ) -> EQ(n, a) ) <-> ( 1 < ( Re ` b ) -> EQ(n, b) ) ) ) for letters/terms a, b"""
    h = '%s = %s' % (a, b)
    P = '( ( 1 - ( x / %s ) ) ^ %s )' % (N, n)
    s1 = w.s([w.s([], 'fveq2', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (h, a, b))], 'breq2d', '( %s -> ( 1 < ( Re ` %s ) <-> 1 < ( Re ` %s ) ) )' % (h, a, b))
    bd = w.s([w.s([w.s([], 'oveq1', '( %s -> ( %s - 1 ) = ( %s - 1 ) )' % (h, a, b))], 'oveq2d', '( %s -> ( x ^c ( %s - 1 ) ) = ( x ^c ( %s - 1 ) ) )' % (h, a, b))],
             'oveq2d', '( %s -> ( %s x. ( x ^c ( %s - 1 ) ) ) = ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (h, P, a, P, b))
    bdx = w.s([bd], 'adantr', '( ( %s /\\ x e. ( 0 (,) %s ) ) -> ( %s x. ( x ^c ( %s - 1 ) ) ) = ( %s x. ( x ^c ( %s - 1 ) ) ) )' % (h, N, P, a, P, b))
    ji = w.s([bdx], 'itgeq2dv', '( %s -> %s = %s )' % (h, L.JN(N, n, a), L.JN(N, n, b)))
    rf = w.s([], 'oveq1', '( %s -> ( %s RiseFac ( %s + 1 ) ) = ( %s RiseFac ( %s + 1 ) ) )' % (h, a, n, b, n))
    l = w.s([ji, rf], 'oveq12d', '( %s -> ( %s x. ( %s RiseFac ( %s + 1 ) ) ) = ( %s x. ( %s RiseFac ( %s + 1 ) ) ) )' % (h, L.JN(N, n, a), a, n, L.JN(N, n, b), b, n))
    r = w.s([w.s([], 'oveq2', '( %s -> ( %s ^c %s ) = ( %s ^c %s ) )' % (h, N, a, N, b))], 'oveq2d', '( %s -> ( ( ! ` %s ) x. ( %s ^c %s ) ) = ( ( ! ` %s ) x. ( %s ^c %s ) ) )' % (h, n, N, a, n, N, b))
    EQa = '( %s x. ( %s RiseFac ( %s + 1 ) ) ) = ( ( ! ` %s ) x. ( %s ^c %s ) )' % (L.JN(N, n, a), a, n, n, N, a)
    EQb = '( %s x. ( %s RiseFac ( %s + 1 ) ) ) = ( ( ! ` %s ) x. ( %s ^c %s ) )' % (L.JN(N, n, b), b, n, n, N, b)
    e = w.s([l, r], 'eqeq12d', '( %s -> ( %s <-> %s ) )' % (h, EQa, EQb))
    return w.s([s1, e], 'imbi12d', '( %s -> ( ( 1 < ( Re ` %s ) -> %s ) <-> ( 1 < ( Re ` %s ) -> %s ) ) )' % (h, a, EQa, b, EQb))


def jn_eq_sub_n(w, a, b):
    """( a = b -> ( PSI(a) <-> PSI(b) ) ), bound w"""
    h = '%s = %s' % (a, b)
    Pa = '( ( 1 - ( x / N ) ) ^ %s )' % a; Pb = '( ( 1 - ( x / N ) ) ^ %s )' % b
    bd = w.s([w.s([], 'oveq2', '( %s -> %s = %s )' % (h, Pa, Pb))], 'oveq1d', '( %s -> ( %s x. ( x ^c ( w - 1 ) ) ) = ( %s x. ( x ^c ( w - 1 ) ) ) )' % (h, Pa, Pb))
    bdx = w.s([bd], 'adantr', '( ( %s /\\ x e. ( 0 (,) N ) ) -> ( %s x. ( x ^c ( w - 1 ) ) ) = ( %s x. ( x ^c ( w - 1 ) ) ) )' % (h, Pa, Pb))
    ji = w.s([bdx], 'itgeq2dv', '( %s -> %s = %s )' % (h, L.JN('N', a, 'w'), L.JN('N', b, 'w')))
    rf = w.s([w.s([], 'oveq1', '( %s -> ( %s + 1 ) = ( %s + 1 ) )' % (h, a, b))], 'oveq2d', '( %s -> ( w RiseFac ( %s + 1 ) ) = ( w RiseFac ( %s + 1 ) ) )' % (h, a, b))
    l = w.s([ji, rf], 'oveq12d', '( %s -> ( %s x. ( w RiseFac ( %s + 1 ) ) ) = ( %s x. ( w RiseFac ( %s + 1 ) ) ) )' % (h, L.JN('N', a, 'w'), a, L.JN('N', b, 'w'), b))
    r = w.s([w.s([], 'fveq2', '( %s -> ( ! ` %s ) = ( ! ` %s ) )' % (h, a, b))], 'oveq1d', '( %s -> ( ( ! ` %s ) x. ( N ^c w ) ) = ( ( ! ` %s ) x. ( N ^c w ) ) )' % (h, a, b))
    EQa = '( %s x. ( w RiseFac ( %s + 1 ) ) ) = ( ( ! ` %s ) x. ( N ^c w ) )' % (L.JN('N', a, 'w'), a, a)
    EQb = '( %s x. ( w RiseFac ( %s + 1 ) ) ) = ( ( ! ` %s ) x. ( N ^c w ) )' % (L.JN('N', b, 'w'), b, b)
    e = w.s([l, r], 'eqeq12d', '( %s -> ( %s <-> %s ) )' % (h, EQa, EQb))
    i_ = w.s([e], 'imbi2d', '( %s -> ( ( 1 < ( Re ` w ) -> %s ) <-> ( 1 < ( Re ` w ) -> %s ) ) )' % (h, EQa, EQb))
    return w.s([i_], 'ralbidv', '( %s -> ( A. w e. CC ( 1 < ( Re ` w ) -> %s ) <-> A. w e. CC ( 1 < ( Re ` w ) -> %s ) ) )' % (h, EQa, EQb))


# ---------------------------------------------------------------- zl3jn
if want('zl3jn'):
    w = W('zl3jn', 'The integral ` J ( K , w ) = S. ( 0 , N ) ( 1 - x / N ) ^ K x ^ ( w - 1 ) dx ` in closed form: '
          '` J ( K , w ) w ( w + 1 ) ... ( w + K ) = K ! N ^ w ` on ` 1 < Re w ` ( induction on ` K ` with ~ zl3jrec , ~ zl3pint , ~ zl3rfl ).')
    A, Cc = ante_of('zl3jn')
    EQ = lambda n, v: '( %s x. ( %s RiseFac ( %s + 1 ) ) ) = ( ( ! ` %s ) x. ( N ^c %s ) )' % (L.JN('N', n, v), v, n, n, v)
    PSI = lambda n, bv='w': 'A. %s e. CC ( 1 < ( Re ` %s ) -> %s )' % (bv, bv, EQ(n, bv))
    ph = 'N e. RR+'
    # ---- base
    B0 = '( ( %s /\\ w e. CC ) /\\ 1 < ( Re ` w ) )' % ph
    nrp = D(w, B0, 'simpll', [], 'N e. RR+'); wc = D(w, B0, 'simplr', [], 'w e. CC'); re1 = D(w, B0, 'simpr', [], '1 < ( Re ` w )')
    nr = D(w, B0, 'rpred', [nrp], 'N e. RR'); nc = D(w, B0, 'rpcnd', [nrp], 'N e. CC'); nn0 = D(w, B0, 'rpne0d', [nrp], 'N =/= 0')
    rw = D(w, B0, 'recld', [wc], '( Re ` w ) e. RR')
    wpos = linarith(w, B0, [re1], '0 < ( Re ` w )', closure=Closure(w, B0, {'( Re ` w )': ('RR', rw)}))
    wn = wne0v(w, B0, 'w', wc, wpos)
    Bx, xc = dom_x(w, B0, '( 0 (,) N )', nr)
    P = '( 1 - ( x / N ) )'
    pc = D(w, Bx, 'subcld', [a1(w, Bx, 'ax-1cn', '1 e. CC'), D(w, Bx, 'divcld', [xc, D(w, Bx, 'adantr', [nc], 'N e. CC'), D(w, Bx, 'adantr', [nn0], 'N =/= 0')], '( x / N ) e. CC')], '%s e. CC' % P)
    xw = D(w, Bx, 'cxpcld', [xc, D(w, Bx, 'subcld', [D(w, Bx, 'adantr', [wc], 'w e. CC'), a1(w, Bx, 'ax-1cn', '1 e. CC')], '( w - 1 ) e. CC')], '( x ^c ( w - 1 ) ) e. CC')
    i0 = chain(w, Bx, ['( ( %s ^ 0 ) x. ( x ^c ( w - 1 ) ) )' % P, '( 1 x. ( x ^c ( w - 1 ) ) )', '( x ^c ( w - 1 ) )'],
               [E(w, Bx, 'oveq1d', [w.s([pc, w.inst('exp0')], 'syl', '( %s -> ( %s ^ 0 ) = 1 )' % (Bx, P))], '( ( %s ^ 0 ) x. ( x ^c ( w - 1 ) ) )' % P, '( 1 x. ( x ^c ( w - 1 ) ) )'),
                E(w, Bx, 'mullidd', [xw], '( 1 x. ( x ^c ( w - 1 ) ) )', '( x ^c ( w - 1 ) )')])
    j0 = w.s([i0], 'itgeq2dv', '( %s -> %s = S. ( 0 (,) N ) ( x ^c ( w - 1 ) ) _d x )' % (B0, L.JN('N', '0', 'w')))
    pint = w.s([w.s([w.s([wc, re1], 'jca', '( %s -> ( w e. CC /\\ 1 < ( Re ` w ) ) )' % B0), nrp], 'jca', '( %s -> ( ( w e. CC /\\ 1 < ( Re ` w ) ) /\\ N e. RR+ ) )' % B0),
                w.inst('zl3pint')], 'syl', '( %s -> S. ( 0 (,) N ) ( x ^c ( w - 1 ) ) _d x = ( ( N ^c w ) / w ) )' % B0)
    rf = chain(w, B0, ['( w RiseFac ( 0 + 1 ) )', '( w RiseFac 1 )', 'w'],
               [E(w, B0, 'oveq2d', [w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % B0)], '( w RiseFac ( 0 + 1 ) )', '( w RiseFac 1 )'),
                w.s([wc, w.inst('risefac1')], 'syl', '( %s -> ( w RiseFac 1 ) = w )' % B0)])
    NW = '( N ^c w )'
    nwc = D(w, B0, 'cxpcld', [nc, wc], '%s e. CC' % NW)
    lhs = chain(w, B0, ['( %s x. ( w RiseFac ( 0 + 1 ) ) )' % L.JN('N', '0', 'w'), '( ( ( N ^c w ) / w ) x. w )', NW],
                [E(w, B0, 'oveq12d', [w.s([j0, pint], 'eqtrd', '( %s -> %s = ( ( N ^c w ) / w ) )' % (B0, L.JN('N', '0', 'w'))), rf],
                   '( %s x. ( w RiseFac ( 0 + 1 ) ) )' % L.JN('N', '0', 'w'), '( ( ( N ^c w ) / w ) x. w )'),
                 E(w, B0, 'divcan1d', [nwc, wc, wn], '( ( ( N ^c w ) / w ) x. w )', NW)])
    rhs = chain(w, B0, ['( ( ! ` 0 ) x. %s )' % NW, '( 1 x. %s )' % NW, NW],
                [E(w, B0, 'oveq1d', [w.s([w.s([], 'fac0', '( ! ` 0 ) = 1')], 'a1i', '( %s -> ( ! ` 0 ) = 1 )' % B0)], '( ( ! ` 0 ) x. %s )' % NW, '( 1 x. %s )' % NW),
                 E(w, B0, 'mullidd', [nwc], '( 1 x. %s )' % NW, NW)])
    beq = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (B0, EQ('0', 'w')))
    base = w.s([w.s([beq], 'ex', '( ( %s /\\ w e. CC ) -> ( 1 < ( Re ` w ) -> %s ) )' % (ph, EQ('0', 'w')))], 'ralrimiva', '( %s -> %s )' % (ph, PSI('0')))
    # ---- step
    ph1 = '( %s /\\ y e. NN0 )' % ph
    S0 = '( ( %s /\\ w e. CC ) /\\ 1 < ( Re ` w ) )' % ph1
    nrp = D(w, S0, 'simplll', [], 'N e. RR+'); yn = D(w, S0, 'simpllr', [], 'y e. NN0'); wc = D(w, S0, 'simplr', [], 'w e. CC'); re1 = D(w, S0, 'simpr', [], '1 < ( Re ` w )')
    nr = D(w, S0, 'rpred', [nrp], 'N e. RR'); nc = D(w, S0, 'rpcnd', [nrp], 'N e. CC'); nn0 = D(w, S0, 'rpne0d', [nrp], 'N =/= 0')
    rw = D(w, S0, 'recld', [wc], '( Re ` w ) e. RR')
    wpos = linarith(w, S0, [re1], '0 < ( Re ` w )', closure=Closure(w, S0, {'( Re ` w )': ('RR', rw)}))
    wn = wne0v(w, S0, 'w', wc, wpos)
    c1 = a1(w, S0, 'ax-1cn', '1 e. CC')
    w1c = D(w, S0, 'addcld', [wc, c1], '( w + 1 ) e. CC')
    rw1 = w.s([E(w, S0, 'readdd', [wc, c1], '( Re ` ( w + 1 ) )', '( ( Re ` w ) + ( Re ` 1 ) )'),
               E(w, S0, 'oveq2d', [w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % S0)], '( ( Re ` w ) + ( Re ` 1 ) )', '( ( Re ` w ) + 1 )')],
              'eqtrd', '( %s -> ( Re ` ( w + 1 ) ) = ( ( Re ` w ) + 1 ) )' % S0)
    lt1 = w.s([linarith(w, S0, [re1], '1 < ( ( Re ` w ) + 1 )', closure=Closure(w, S0, {'( Re ` w )': ('RR', rw)})), rw1], 'breqtrrd', '( %s -> 1 < ( Re ` ( w + 1 ) ) )' % S0)
    # IH instance at w + 1 via bound v
    sc = jn_eq_sub_w(w, 'y', 'w', 'v')
    cb = w.s([sc], 'cbvralvw', '( %s <-> %s )' % (PSI('y'), PSI('y', 'v')))
    sr = jn_eq_sub_w(w, 'y', 'v', '( w + 1 )')
    vr = '( 1 < ( Re ` ( w + 1 ) ) -> %s )' % EQ('y', '( w + 1 )')
    rs = w.s([sr], 'rspcv', '( ( w + 1 ) e. CC -> ( %s -> %s ) )' % (PSI('y', 'v'), vr))
    ih1 = w.s([w1c, rs], 'syl', '( %s -> ( %s -> %s ) )' % (S0, PSI('y', 'v'), vr))
    ih2 = w.s([w.s([cb], 'a1i', '( %s -> ( %s <-> %s ) )' % (S0, PSI('y'), PSI('y', 'v'))), ih1], 'sylbid', '( %s -> ( %s -> %s ) )' % (S0, PSI('y'), vr))
    ih3 = w.s([lt1, ih2], 'mpid', '( %s -> ( %s -> %s ) )' % (S0, PSI('y'), EQ('y', '( w + 1 )')))
    # algebra under the IH
    S2 = '( %s /\\ %s )' % (S0, EQ('y', '( w + 1 )'))
    Lf = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (S2, f))
    ih = D(w, S2, 'simpr', [], EQ('y', '( w + 1 )'))
    wc2 = Lf(wc, 'w e. CC'); nc2 = Lf(nc, 'N e. CC'); nn2 = Lf(nn0, 'N =/= 0'); wn2 = Lf(wn, 'w =/= 0'); yn2 = Lf(yn, 'y e. NN0')
    yc2 = D(w, S2, 'nn0cnd', [yn2], 'y e. CC')
    y1n = w.s([yn2, w.inst('peano2nn0')], 'syl', '( %s -> ( y + 1 ) e. NN0 )' % S2)
    y1c = D(w, S2, 'nn0cnd', [y1n], '( y + 1 ) e. CC')
    J1 = L.JN('N', '( y + 1 )', 'w'); J0 = L.JN('N', 'y', '( w + 1 )')
    R = '( ( w + 1 ) RiseFac ( y + 1 ) )'
    jr = w.s([w.s([Lf(w.s([wc, re1], 'jca', '( %s -> ( w e. CC /\\ 1 < ( Re ` w ) ) )' % S0), '( w e. CC /\\ 1 < ( Re ` w ) )'),
                   Lf(w.s([nrp, yn], 'jca', '( %s -> ( N e. RR+ /\\ y e. NN0 ) )' % S0), '( N e. RR+ /\\ y e. NN0 )')], 'jca',
                  '( %s -> ( ( w e. CC /\\ 1 < ( Re ` w ) ) /\\ ( N e. RR+ /\\ y e. NN0 ) ) )' % S2), w.inst('zl3jrec')], 'syl',
             '( %s -> %s = ( ( ( y + 1 ) / ( N x. w ) ) x. %s ) )' % (S2, J1, J0))
    rfl = w.s([w.s([wc2, y1n], 'jca', '( %s -> ( w e. CC /\\ ( y + 1 ) e. NN0 ) )' % S2), w.inst('zl3rfl')], 'syl',
              '( %s -> ( w RiseFac ( ( y + 1 ) + 1 ) ) = ( w x. %s ) )' % (S2, R))
    CF = '( ( y + 1 ) / ( N x. w ) )'
    nwm = D(w, S2, 'mulcld', [nc2, wc2], '( N x. w ) e. CC'); nwn = D(w, S2, 'mulne0d', [nc2, wc2, nn2, wn2], '( N x. w ) =/= 0')
    cfc = D(w, S2, 'divcld', [y1c, nwm, nwn], '%s e. CC' % CF)
    w1c2 = D(w, S2, 'addcld', [wc2, a1(w, S2, 'ax-1cn', '1 e. CC')], '( w + 1 ) e. CC')
    rc = w.s([w1c2, yn2 if False else y1n, w.inst('risefaccl')], 'syl2anc', '( %s -> %s e. CC )' % (S2, R))
    # J0 e. CC from the IH? use itgcl route: J0 x. R = ... ; we need J0 e. CC for mul4d: derive via itgcl
    Sx, xc3 = dom_x(w, S2, '( 0 (,) N )', Lf(nr, 'N e. RR'))
    J0c = None
    YN = '( y + 1 )'
    Q = '( ( y + 1 ) / N )'
    qc = D(w, S2, 'divcld', [y1c, nc2, nn2], '%s e. CC' % Q)
    FY = '( ! ` y )'
    fyc = D(w, S2, 'nn0cnd' if False else 'recnd', [w.s([w.s([yn2, w.inst('faccl')], 'syl', '( %s -> %s e. NN )' % (S2, FY))], 'nnred', '( %s -> %s e. RR )' % (S2, FY))], '%s e. CC' % FY)
    NW = '( N ^c w )'
    nwc = D(w, S2, 'cxpcld', [nc2, wc2], '%s e. CC' % NW)
    Z = '( %s x. %s )' % (FY, NW)
    zc = D(w, S2, 'mulcld', [fyc, nwc], '%s e. CC' % Z)
    T = ['( %s x. ( w RiseFac ( ( y + 1 ) + 1 ) ) )' % J1,
         '( ( %s x. %s ) x. ( w x. %s ) )' % (CF, J0, R),
         '( ( %s x. w ) x. ( %s x. %s ) )' % (CF, J0, R),
         '( %s x. ( %s x. %s ) )' % (Q, J0, R),
         '( %s x. ( %s x. ( N ^c ( w + 1 ) ) ) )' % (Q, FY),
         '( %s x. ( %s x. ( %s x. N ) ) )' % (Q, FY, NW),
         '( %s x. ( %s x. N ) )' % (Q, Z),
         '( %s x. ( N x. %s ) )' % (Q, Z),
         '( ( %s x. N ) x. %s )' % (Q, Z),
         '( %s x. %s )' % (YN, Z),
         '( ( %s x. %s ) x. %s )' % (YN, FY, NW),
         '( ( %s x. %s ) x. %s )' % (FY, YN, NW),
         '( ( ! ` ( y + 1 ) ) x. %s )' % NW]
    # J0 e. CC: from the integral being a complex number (itgcl needs L^1); use the IH instead: J0 x. R e. CC suffices for mul4d? mul4d needs J0 e. CC.
    J0c = w.s([w.s([], 'itgcl' if False else 'idi', 'x')], 'idi', 'x') if False else None
    # get J0 e. CC via zl3jrec's right side being J1 / CF ... simpler: J0 = ( ( y ! N^(w+1) ) / R ) needs R =/= 0; instead prove integrability.
    w1c0 = D(w, S0, 'addcld', [wc, a1(w, S0, 'ax-1cn', '1 e. CC')], '( w + 1 ) e. CC')
    cW = ccx(w, S0, '( ( w + 1 ) - 1 )', D(w, S0, 'subcld', [w1c0, a1(w, S0, 'ax-1cn', '1 e. CC')], '( ( w + 1 ) - 1 ) e. CC'),
             w.s([wpos, w.s([E(w, S0, 'fveq2d', [E(w, S0, 'pncand', [wc, a1(w, S0, 'ax-1cn', '1 e. CC')], '( ( w + 1 ) - 1 )', 'w')], '( Re ` ( ( w + 1 ) - 1 ) )', '( Re ` w )')],
                            'idi', '( %s -> ( Re ` ( ( w + 1 ) - 1 ) ) = ( Re ` w ) )' % S0)], 'breqtrrd', '( %s -> 0 < ( Re ` ( ( w + 1 ) - 1 ) ) )' % S0), nrp)
    clS = Closure(w, S0, {'N': ('RR', nr), 'y': ('NN0', yn)})
    clS.have('N', 'ne0', nn0)
    PKY = '( ( 1 - ( x / N ) ) ^ y )'
    XWP = '( x ^c ( ( w + 1 ) - 1 ) )'
    cj = cont(w, S0, '( 0 [,] N )', '( %s x. %s )' % (PKY, XWP), clS, dom_cc(w, S0, '( 0 [,] N )', nr), special={XWP: cW})
    _, ij = ibl_of(w, S0, 'N', '( %s x. %s )' % (PKY, XWP), cj, nr)
    Sx0, _xc0 = dom_x(w, S0, '( 0 (,) N )', nr)
    J0c0 = w.s([w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PKY, XWP))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Sx0, PKY, XWP)), ij], 'itgcl', '( %s -> %s e. CC )' % (S0, J0))
    J0c = Lf(J0c0, '%s e. CC' % J0)
    e = []
    e.append(E(w, S2, 'oveq12d', [jr, rfl], T[0], T[1]))
    e.append(E(w, S2, 'mul4d', [cfc, J0c, wc2, rc], T[1], T[2]))
    cw_ = chain(w, S2, ['( %s x. w )' % CF, '( ( %s / w ) x. w )' % Q, Q],
                [E(w, S2, 'oveq1d', [w.s([E(w, S2, 'divdiv1d', [y1c, nc2, wc2, nn2, wn2], '( %s / w )' % Q, CF)], 'eqcomd', '( %s -> %s = ( %s / w ) )' % (S2, CF, Q))],
                   '( %s x. w )' % CF, '( ( %s / w ) x. w )' % Q),
                 E(w, S2, 'divcan1d', [qc, wc2, wn2], '( ( %s / w ) x. w )' % Q, Q)])
    e.append(E(w, S2, 'oveq1d', [cw_], T[2], T[3]))
    e.append(E(w, S2, 'oveq2d', [ih], T[3], T[4]))
    e.append(E(w, S2, 'oveq2d', [E(w, S2, 'oveq2d', [w.s([nc2, nn2, wc2, w.inst('cxpp1')], 'syl3anc', '( %s -> ( N ^c ( w + 1 ) ) = ( %s x. N ) )' % (S2, NW))],
                                   '( %s x. ( N ^c ( w + 1 ) ) )' % FY, '( %s x. ( %s x. N ) )' % (FY, NW))], T[4], T[5]))
    e.append(E(w, S2, 'oveq2d', [w.s([E(w, S2, 'mulassd', [fyc, nwc, nc2], '( %s x. N )' % Z, '( %s x. ( %s x. N ) )' % (FY, NW))], 'eqcomd',
                                     '( %s -> ( %s x. ( %s x. N ) ) = ( %s x. N ) )' % (S2, FY, NW, Z))], T[5], T[6]))
    e.append(E(w, S2, 'oveq2d', [E(w, S2, 'mulcomd', [zc, nc2], '( %s x. N )' % Z, '( N x. %s )' % Z)], T[6], T[7]))
    e.append(w.s([E(w, S2, 'mulassd', [qc, nc2, zc], T[8], T[7])], 'eqcomd', '( %s -> %s = %s )' % (S2, T[7], T[8])))
    e.append(E(w, S2, 'oveq1d', [E(w, S2, 'divcan1d', [y1c, nc2, nn2], '( %s x. N )' % Q, YN)], T[8], T[9]))
    e.append(w.s([E(w, S2, 'mulassd', [y1c, fyc, nwc], T[10], T[9])], 'eqcomd', '( %s -> %s = %s )' % (S2, T[9], T[10])))
    e.append(E(w, S2, 'oveq1d', [E(w, S2, 'mulcomd', [y1c, fyc], '( %s x. %s )' % (YN, FY), '( %s x. %s )' % (FY, YN))], T[10], T[11]))
    e.append(E(w, S2, 'oveq1d', [w.s([w.s([yn2, w.inst('facp1')], 'syl', '( %s -> ( ! ` ( y + 1 ) ) = ( %s x. %s ) )' % (S2, FY, YN))], 'eqcomd',
                                     '( %s -> ( %s x. %s ) = ( ! ` ( y + 1 ) ) )' % (S2, FY, YN))], T[11], T[12]))
    goal = chain(w, S2, T, e)
    g2 = w.s([goal], 'ex', '( %s -> ( %s -> %s ) )' % (S0, EQ('y', '( w + 1 )'), EQ('( y + 1 )', 'w')))
    g3 = w.s([ih3, g2], 'syld', '( %s -> ( %s -> %s ) )' % (S0, PSI('y'), EQ('( y + 1 )', 'w')))
    g4 = w.s([g3], 'ex', '( ( %s /\\ w e. CC ) -> ( 1 < ( Re ` w ) -> ( %s -> %s ) ) )' % (ph1, PSI('y'), EQ('( y + 1 )', 'w')))
    g5 = w.s([g4], 'com23', '( ( %s /\\ w e. CC ) -> ( %s -> ( 1 < ( Re ` w ) -> %s ) ) )' % (ph1, PSI('y'), EQ('( y + 1 )', 'w')))
    g6 = w.s([g5], 'ralrimiva', '( %s -> A. w e. CC ( %s -> ( 1 < ( Re ` w ) -> %s ) ) )' % (ph1, PSI('y'), EQ('( y + 1 )', 'w')))
    g7 = w.s([g6, w.s([w.s([], 'nfra1', 'F/ w %s' % PSI('y'))], 'r19.21', '( A. w e. CC ( %s -> ( 1 < ( Re ` w ) -> %s ) ) <-> ( %s -> %s ) )' % (
        PSI('y'), EQ('( y + 1 )', 'w'), PSI('y'), PSI('( y + 1 )')))], 'sylib', '( %s -> ( %s -> %s ) )' % (ph1, PSI('y'), PSI('( y + 1 )')))
    stp = w.s([g7], 'imp', '( ( %s /\\ %s ) -> %s )' % (ph1, PSI('y'), PSI('( y + 1 )')))
    def sub(t):
        return jn_eq_sub_n(w, 'n', t), PSI(t)
    a0, v0 = sub('0'); ay, vy = sub('y'); a1_, v1 = sub('( y + 1 )'); ak, vk = sub('K')
    assert v0 == PSI('0') and vy == PSI('y') and v1 == PSI('( y + 1 )'), (v0[:80],)
    ind = w.s([a0, ay, a1_, ak, base, stp], 'nn0indd', '( ( %s /\\ K e. NN0 ) -> %s )' % (ph, vk))
    finish(w, ind, 'zl3jn')
    go(w)


# ---------------------------------------------------------------- zl3gpk
if want('zl3gpk'):
    w = W('zl3gpk', "The partial products of Euler's product ( ~ gamcvg2 ) in Gauss's form: "
          '` P_K ( W + 1 ) ( W + 2 ) ... ( W + K ) = ( K + 1 ) ^ W K ! ` ( induction with ~ seqp1 , ~ risefacp1 ).')
    A, Cc = ante_of('zl3gpk')
    EU = L.EUT('W')
    SQ = lambda n: '( seq 1 ( x. , %s ) ` %s )' % (EU, n)
    PSI = lambda n: '( %s x. ( ( W + 1 ) RiseFac %s ) ) = ( ( ( %s + 1 ) ^c W ) x. ( ! ` %s ) )' % (SQ(n), n, n, n)
    ph = '( W e. CC /\\ 0 < ( Re ` W ) )'
    def sub(t):
        idx = w.s([], 'id', '( n = %s -> n = %s )' % (t, t))
        st, val = w.wcongr(PSI('n'), {'n': t}, 'n = %s' % t, {'n': idx})
        assert val == PSI(t), (val, PSI(t))
        return st, val
    a1s, _ = sub('1'); ays, _ = sub('y'); ay1, _ = sub('( y + 1 )'); aks, _ = sub('K')
    # base
    wc = D(w, ph, 'simpl', [], 'W e. CC'); wp = D(w, ph, 'simpr', [], '0 < ( Re ` W )')
    c1 = a1(w, ph, 'ax-1cn', '1 e. CC')
    W1 = '( W + 1 )'
    w1c = D(w, ph, 'addcld', [wc, c1], '%s e. CC' % W1)
    rw = D(w, ph, 'recld', [wc], '( Re ` W ) e. RR')
    rw1 = w.s([E(w, ph, 'readdd', [wc, c1], '( Re ` %s )' % W1, '( ( Re ` W ) + ( Re ` 1 ) )'),
               E(w, ph, 'oveq2d', [w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % ph)], '( ( Re ` W ) + ( Re ` 1 ) )', '( ( Re ` W ) + 1 )')],
              'eqtrd', '( %s -> ( Re ` %s ) = ( ( Re ` W ) + 1 ) )' % (ph, W1))
    w1p = w.s([linarith(w, ph, [wp], '0 < ( ( Re ` W ) + 1 )', closure=Closure(w, ph, {'( Re ` W )': ('RR', rw)})), rw1], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (ph, W1))
    w1n = wne0v(w, ph, W1, w1c, w1p)
    G1 = '( ( ( 1 + 1 ) / 1 ) ^c W )'
    s1 = w.s([w.s([w.s([], '1z', '1 e. ZZ'), w.inst('seq1')], 'ax-mp', '%s = ( %s ` 1 )' % (SQ('1'), EU))], 'a1i', '( %s -> %s = ( %s ` 1 ) )' % (ph, SQ('1'), EU))
    ev = w.s([w.s([w.s([], '1nn', '1 e. NN'), w.inst('eutval')], 'ax-mp', '( %s ` 1 ) = ( %s / ( ( W / 1 ) + 1 ) )' % (EU, G1))], 'a1i',
             '( %s -> ( %s ` 1 ) = ( %s / ( ( W / 1 ) + 1 ) ) )' % (ph, EU, G1))
    dn = E(w, ph, 'oveq2d', [E(w, ph, 'oveq1d', [E(w, ph, 'div1d', [wc], '( W / 1 )', 'W')], '( ( W / 1 ) + 1 )', W1)], '( %s / ( ( W / 1 ) + 1 ) )' % G1, '( %s / %s )' % (G1, W1))
    t2 = a1(w, ph, '2cn', '2 e. CC')
    g1c = D(w, ph, 'cxpcld', [D(w, ph, 'divcld', [D(w, ph, 'addcld', [c1, c1], '( 1 + 1 ) e. CC'), c1, a1(w, ph, 'ax-1ne0', '1 =/= 0')], '( ( 1 + 1 ) / 1 ) e. CC'), wc], '%s e. CC' % G1)
    G1b = '( ( 1 + 1 ) ^c W )'
    gg = E(w, ph, 'oveq1d', [E(w, ph, 'div1d', [D(w, ph, 'addcld', [c1, c1], '( 1 + 1 ) e. CC')], '( ( 1 + 1 ) / 1 )', '( 1 + 1 )')], G1, G1b)
    lhs = chain(w, ph, ['( %s x. ( %s RiseFac 1 ) )' % (SQ('1'), W1), '( ( %s ` 1 ) x. %s )' % (EU, W1), '( ( %s / ( ( W / 1 ) + 1 ) ) x. %s )' % (G1, W1),
                        '( ( %s / %s ) x. %s )' % (G1, W1, W1), G1, G1b],
                [E(w, ph, 'oveq12d', [s1, w.s([w1c, w.inst('risefac1')], 'syl', '( %s -> ( %s RiseFac 1 ) = %s )' % (ph, W1, W1))], '( %s x. ( %s RiseFac 1 ) )' % (SQ('1'), W1),
                   '( ( %s ` 1 ) x. %s )' % (EU, W1)),
                 E(w, ph, 'oveq1d', [ev], '( ( %s ` 1 ) x. %s )' % (EU, W1), '( ( %s / ( ( W / 1 ) + 1 ) ) x. %s )' % (G1, W1)),
                 E(w, ph, 'oveq1d', [dn], '( ( %s / ( ( W / 1 ) + 1 ) ) x. %s )' % (G1, W1), '( ( %s / %s ) x. %s )' % (G1, W1, W1)),
                 E(w, ph, 'divcan1d', [g1c, w1c, w1n], '( ( %s / %s ) x. %s )' % (G1, W1, W1), G1), gg])
    rhs = chain(w, ph, ['( %s x. ( ! ` 1 ) )' % G1b, '( %s x. 1 )' % G1b, G1b],
                [E(w, ph, 'oveq2d', [w.s([w.s([], 'fac1', '( ! ` 1 ) = 1')], 'a1i', '( %s -> ( ! ` 1 ) = 1 )' % ph)], '( %s x. ( ! ` 1 ) )' % G1b, '( %s x. 1 )' % G1b),
                 E(w, ph, 'mulridd', [D(w, ph, 'cxpcld', [D(w, ph, 'addcld', [c1, c1], '( 1 + 1 ) e. CC'), wc], '%s e. CC' % G1b)], '( %s x. 1 )' % G1b, G1b)])
    base = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (ph, PSI('1')))
    # step
    ctx = '( ( %s /\\ y e. NN ) /\\ %s )' % (ph, PSI('y'))
    wc = D(w, ctx, 'simpll', [], '( W e. CC /\\ 0 < ( Re ` W ) )')
    wcc = D(w, ctx, 'simpd' if False else 'simpld', [wc], 'W e. CC'); wpp = D(w, ctx, 'simprd', [wc], '0 < ( Re ` W )')
    yn = D(w, ctx, 'simplr', [], 'y e. NN'); ih = D(w, ctx, 'simpr', [], PSI('y'))
    yc = D(w, ctx, 'nncnd', [yn], 'y e. CC'); yr = D(w, ctx, 'nnred', [yn], 'y e. RR')
    c1 = a1(w, ctx, 'ax-1cn', '1 e. CC')
    Y1 = '( y + 1 )'; Y2 = '( ( y + 1 ) + 1 )'
    y1c = D(w, ctx, 'addcld', [yc, c1], '%s e. CC' % Y1)
    y1rp = w.s([w.s([yn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (ctx, Y1))], 'nnrpd', '( %s -> %s e. RR+ )' % (ctx, Y1))
    y1n0 = D(w, ctx, 'rpne0d', [y1rp], '%s =/= 0' % Y1)
    yuz = w.s([yn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % ctx)], 'eleqtrd', '( %s -> y e. ( ZZ>= ` 1 ) )' % ctx)
    sp = w.s([yuz, w.inst('seqp1')], 'syl', '( %s -> %s = ( %s x. ( %s ` %s ) ) )' % (ctx, SQ(Y1), SQ('y'), EU, Y1))
    W1 = '( W + 1 )'
    w1c = D(w, ctx, 'addcld', [wcc, c1], '%s e. CC' % W1)
    Q = '( %s + y )' % W1
    rp = w.s([w1c, D(w, ctx, 'nnnn0d', [yn], 'y e. NN0'), w.inst('risefacp1')], 'syl2anc', '( %s -> ( %s RiseFac %s ) = ( ( %s RiseFac y ) x. %s ) )' % (ctx, W1, Y1, W1, Q))
    EV = '( %s ` %s )' % (EU, Y1)
    Sy = SQ('y'); Ry = '( %s RiseFac y )' % W1
    syc = w.s([w.s([w.s([w.s([w.s([], 'idi', 'x')], 'idi', 'x')], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    # closures
    Cm = '( %s /\\ ( a e. CC /\\ b e. CC ) )' % ctx
    clo = D(w, Cm, 'mulcld', [D(w, Cm, 'simprl', [], 'a e. CC'), D(w, Cm, 'simprr', [], 'b e. CC')], '( a x. b ) e. CC')
    Ca = '( %s /\\ a e. ( 1 ... y ) )' % ctx
    an = w.s([D(w, Ca, 'simpr', [], 'a e. ( 1 ... y )'), w.inst('elfznn')], 'syl', '( %s -> a e. NN )' % Ca)
    tcl = w.s([w.s([D(w, Ca, 'adantr', [wc], '( W e. CC /\\ 0 < ( Re ` W ) )'), an], 'jca', '( %s -> ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ a e. NN ) )' % Ca),
               w.inst('eutzcl')], 'syl', '( %s -> ( %s ` a ) e. CC )' % (Ca, EU))
    syc = w.s([yuz, tcl, clo], 'seqcl', '( %s -> %s e. CC )' % (ctx, Sy))
    ryc = w.s([w1c, D(w, ctx, 'nnnn0d', [yn], 'y e. NN0'), w.inst('risefaccl')], 'syl2anc', '( %s -> %s e. CC )' % (ctx, Ry))
    evc = w.s([w.s([wc, w.s([yn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (ctx, Y1))], 'jca', '( %s -> ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ %s e. NN ) )' % (ctx, Y1)),
               w.inst('eutzcl')], 'syl', '( %s -> %s e. CC )' % (ctx, EV))
    qc = D(w, ctx, 'addcld', [w1c, yc], '%s e. CC' % Q)
    rw = D(w, ctx, 'recld', [wcc], '( Re ` W ) e. RR')
    # Re Q > 0
    reQ = w.s([E(w, ctx, 'readdd', [w1c, yc], '( Re ` %s )' % Q, '( ( Re ` %s ) + ( Re ` y ) )' % W1),
               E(w, ctx, 'oveq12d', [w.s([E(w, ctx, 'readdd', [wcc, c1], '( Re ` %s )' % W1, '( ( Re ` W ) + ( Re ` 1 ) )'),
                                          E(w, ctx, 'oveq2d', [w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % ctx)], '( ( Re ` W ) + ( Re ` 1 ) )', '( ( Re ` W ) + 1 )')],
                                         'eqtrd', '( %s -> ( Re ` %s ) = ( ( Re ` W ) + 1 ) )' % (ctx, W1)),
                                     w.s([yr, w.inst('rered')], 'syl', '( %s -> ( Re ` y ) = y )' % ctx)],
                 '( ( Re ` %s ) + ( Re ` y ) )' % W1, '( ( ( Re ` W ) + 1 ) + y )')], 'eqtrd', '( %s -> ( Re ` %s ) = ( ( ( Re ` W ) + 1 ) + y ) )' % (ctx, Q))
    qp = w.s([linarith(w, ctx, [wpp, D(w, ctx, 'nnge1d' if False else 'ltled', [a1(w, ctx, '0re', '0 e. RR'), yr, D(w, ctx, 'nngt0d', [yn], '0 < y')], '0 <_ y')],
                       '0 < ( ( ( Re ` W ) + 1 ) + y )', closure=Closure(w, ctx, {'( Re ` W )': ('RR', rw), 'y': ('RR', yr)})), reQ], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (ctx, Q))
    qn = wne0v(w, ctx, Q, qc, qp)
    G = '( ( %s / %s ) ^c W )' % (Y2, Y1)
    Dn = '( ( W / %s ) + 1 )' % Y1
    ev = w.s([w.s([yn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (ctx, Y1)), w.inst('eutval')], 'syl', '( %s -> %s = ( %s / %s ) )' % (ctx, EV, G, Dn))
    # Dn = Q / Y1
    d1 = chain(w, ctx, [Dn, '( ( W / %s ) + ( %s / %s ) )' % (Y1, Y1, Y1), '( ( W + %s ) / %s )' % (Y1, Y1), '( %s / %s )' % (Q, Y1)],
               [E(w, ctx, 'oveq2d', [w.s([E(w, ctx, 'dividd', [y1c, y1n0], '( %s / %s )' % (Y1, Y1), '1')], 'eqcomd', '( %s -> 1 = ( %s / %s ) )' % (ctx, Y1, Y1))], Dn, '( ( W / %s ) + ( %s / %s ) )' % (Y1, Y1, Y1)),
                ('r', E(w, ctx, 'divdird', [wcc, y1c, y1c, y1n0], '( ( W + %s ) / %s )' % (Y1, Y1), '( ( W / %s ) + ( %s / %s ) )' % (Y1, Y1, Y1))),
                E(w, ctx, 'oveq1d', [w.s([E(w, ctx, 'addassd', [wcc, c1, yc], '( ( W + 1 ) + y )', '( W + ( 1 + y ) )'),
                                          E(w, ctx, 'oveq2d', [E(w, ctx, 'addcomd', [c1, yc], '( 1 + y )', Y1)], '( W + ( 1 + y ) )', '( W + %s )' % Y1)], 'eqtrd',
                                         '( %s -> %s = ( W + %s ) )' % (ctx, Q, Y1))], '( %s / %s )' % (Q, Y1), '( ( W + %s ) / %s )' % (Y1, Y1)) and
                w.s([E(w, ctx, 'oveq1d', [w.s([E(w, ctx, 'addassd', [wcc, c1, yc], '( ( W + 1 ) + y )', '( W + ( 1 + y ) )'),
                                               E(w, ctx, 'oveq2d', [E(w, ctx, 'addcomd', [c1, yc], '( 1 + y )', Y1)], '( W + ( 1 + y ) )', '( W + %s )' % Y1)], 'eqtrd',
                                              '( %s -> %s = ( W + %s ) )' % (ctx, Q, Y1))], '( %s / %s )' % (Q, Y1), '( ( W + %s ) / %s )' % (Y1, Y1))], 'eqcomd',
                    '( %s -> ( ( W + %s ) / %s ) = ( %s / %s ) )' % (ctx, Y1, Y1, Q, Y1))])
    gc = D(w, ctx, 'cxpcld', [D(w, ctx, 'divcld', [D(w, ctx, 'addcld', [y1c, c1], '%s e. CC' % Y2), y1c, y1n0], '( %s / %s ) e. CC' % (Y2, Y1)), wcc], '%s e. CC' % G)
    eq_ = chain(w, ctx, ['( %s x. %s )' % (EV, Q), '( ( %s / %s ) x. %s )' % (G, Dn, Q), '( ( %s / ( %s / %s ) ) x. %s )' % (G, Q, Y1, Q),
                         '( ( ( %s x. %s ) / %s ) x. %s )' % (G, Y1, Q, Q), '( %s x. %s )' % (G, Y1)],
                [E(w, ctx, 'oveq1d', [ev], '( %s x. %s )' % (EV, Q), '( ( %s / %s ) x. %s )' % (G, Dn, Q)),
                 E(w, ctx, 'oveq1d', [E(w, ctx, 'oveq2d', [d1], '( %s / %s )' % (G, Dn), '( %s / ( %s / %s ) )' % (G, Q, Y1))], '( ( %s / %s ) x. %s )' % (G, Dn, Q), '( ( %s / ( %s / %s ) ) x. %s )' % (G, Q, Y1, Q)),
                 E(w, ctx, 'oveq1d', [E(w, ctx, 'divdiv2d', [gc, qc, y1c, qn, y1n0], '( %s / ( %s / %s ) )' % (G, Q, Y1), '( ( %s x. %s ) / %s )' % (G, Y1, Q))],
                   '( ( %s / ( %s / %s ) ) x. %s )' % (G, Q, Y1, Q), '( ( ( %s x. %s ) / %s ) x. %s )' % (G, Y1, Q, Q)),
                 E(w, ctx, 'divcan1d', [D(w, ctx, 'mulcld', [gc, y1c], '( %s x. %s ) e. CC' % (G, Y1)), qc, qn], '( ( ( %s x. %s ) / %s ) x. %s )' % (G, Y1, Q, Q), '( %s x. %s )' % (G, Y1))])
    AW = '( %s ^c W )' % Y1; BW = '( %s ^c W )' % Y2
    y2r = D(w, ctx, 'readdcld', [D(w, ctx, 'rpred', [y1rp], '%s e. RR' % Y1), a1(w, ctx, '1re', '1 e. RR')], '%s e. RR' % Y2)
    y20 = D(w, ctx, 'ltled', [a1(w, ctx, '0re', '0 e. RR'), y2r, linarith(w, ctx, [D(w, ctx, 'rpgt0d', [y1rp], '0 < %s' % Y1)], '0 < %s' % Y2,
                                                                          closure=Closure(w, ctx, {Y1: ('RR', D(w, ctx, 'rpred', [y1rp], '%s e. RR' % Y1)), 'y': ('RR', yr)}))], '0 <_ %s' % Y2)
    gd = w.s([w.s([y2r, y20], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ctx, Y2, Y2)), y1rp, wcc, w.inst('divcxp')], 'syl3anc', '( %s -> %s = ( %s / %s ) )' % (ctx, G, BW, AW))
    FY = '( ! ` y )'
    fyc = D(w, ctx, 'nncnd', [w.s([D(w, ctx, 'nnnn0d', [yn], 'y e. NN0'), w.inst('faccl')], 'syl', '( %s -> %s e. NN )' % (ctx, FY))], '%s e. CC' % FY)
    awc = D(w, ctx, 'cxpcld', [y1c, wcc], '%s e. CC' % AW); awn = D(w, ctx, 'cxpne0d', [y1c, y1n0, wcc], '%s =/= 0' % AW)
    bwc = D(w, ctx, 'cxpcld', [D(w, ctx, 'addcld', [y1c, c1], '%s e. CC' % Y2), wcc], '%s e. CC' % BW)
    T = ['( %s x. ( %s RiseFac %s ) )' % (SQ(Y1), W1, Y1),
         '( ( %s x. %s ) x. ( %s x. %s ) )' % (Sy, EV, Ry, Q),
         '( ( %s x. %s ) x. ( %s x. %s ) )' % (Sy, Ry, EV, Q),
         '( ( %s x. %s ) x. ( %s x. %s ) )' % (AW, FY, EV, Q),
         '( ( %s x. %s ) x. ( %s x. %s ) )' % (AW, FY, G, Y1),
         '( ( %s x. %s ) x. ( ( %s / %s ) x. %s ) )' % (AW, FY, BW, AW, Y1),
         '( ( %s x. ( %s / %s ) ) x. ( %s x. %s ) )' % (AW, BW, AW, FY, Y1),
         '( %s x. ( %s x. %s ) )' % (BW, FY, Y1),
         '( %s x. ( ! ` %s ) )' % (BW, Y1)]
    e = [E(w, ctx, 'oveq12d', [sp, rp], T[0], T[1]),
         E(w, ctx, 'mul4d', [syc, evc, ryc, qc], T[1], T[2]),
         E(w, ctx, 'oveq1d', [ih], T[2], T[3]),
         E(w, ctx, 'oveq2d', [eq_], T[3], T[4]),
         E(w, ctx, 'oveq2d', [E(w, ctx, 'oveq1d', [gd], '( %s x. %s )' % (G, Y1), '( ( %s / %s ) x. %s )' % (BW, AW, Y1))], T[4], T[5]),
         E(w, ctx, 'mul4d', [awc, fyc, D(w, ctx, 'divcld', [bwc, awc, awn], '( %s / %s ) e. CC' % (BW, AW)), y1c], T[5], T[6]),
         E(w, ctx, 'oveq1d', [E(w, ctx, 'divcan2d', [bwc, awc, awn], '( %s x. ( %s / %s ) )' % (AW, BW, AW), BW)], T[6], T[7]),
         E(w, ctx, 'oveq2d', [w.s([w.s([D(w, ctx, 'nnnn0d', [yn], 'y e. NN0'), w.inst('facp1')], 'syl', '( %s -> ( ! ` %s ) = ( %s x. %s ) )' % (ctx, Y1, FY, Y1))], 'eqcomd',
                                  '( %s -> ( %s x. %s ) = ( ! ` %s ) )' % (ctx, FY, Y1, Y1))], T[7], T[8])]
    stp = chain(w, ctx, T, e)
    ind = w.s([a1s, ays, ay1, aks, base, stp], 'nnindd', '( ( %s /\\ K e. NN ) -> %s )' % (ph, PSI('K')))
    finish(w, ind, 'zl3gpk')
    go(w)


def seq_cc(w, C, wp_step, kuz):
    """( C -> ( seq 1 ( x. , EUT W ) ` K' ) e. CC ) from wp_step: ( C -> ( W e. CC /\\ 0 < ( Re ` W ) ) ) and kuz: ( C -> K' e. ( ZZ>= ` 1 ) )"""
    from cl import formula_of
    Kp = formula_of(w, kuz).split(' -> ')[1].split(' e. ( ZZ>=')[0]
    EU = L.EUT('W')
    Cm = '( %s /\\ ( a e. CC /\\ b e. CC ) )' % C
    clo = D(w, Cm, 'mulcld', [D(w, Cm, 'simprl', [], 'a e. CC'), D(w, Cm, 'simprr', [], 'b e. CC')], '( a x. b ) e. CC')
    Ca = '( %s /\\ a e. ( 1 ... %s ) )' % (C, Kp)
    an = w.s([D(w, Ca, 'simpr', [], 'a e. ( 1 ... %s )' % Kp), w.inst('elfznn')], 'syl', '( %s -> a e. NN )' % Ca)
    tcl = w.s([w.s([D(w, Ca, 'adantr', [wp_step], '( W e. CC /\\ 0 < ( Re ` W ) )'), an], 'jca', '( %s -> ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ a e. NN ) )' % Ca),
               w.inst('eutzcl')], 'syl', '( %s -> ( %s ` a ) e. CC )' % (Ca, EU))
    return w.s([kuz, tcl, clo], 'seqcl', '( %s -> ( seq 1 ( x. , %s ) ` %s ) e. CC )' % (C, EU, Kp))


# ---------------------------------------------------------------- zl3qid
if want('zl3qid'):
    w = W('zl3qid', "The approximant ` J = S. ( 0 , K + 1 ) ( 1 - x / ( K + 1 ) ) ^ ( K + 1 ) x ^ ( W - 1 ) dx ` through Euler's partial product: "
          '` J = ( 1 / W ) P_K / ( 1 + W / ( K + 1 ) ) ` ( ~ zl3jn , ~ zl3gpk , ~ zl3rfl ).')
    A, Cc = ante_of('zl3qid')
    wc = D(w, A, 'simpll', [], 'W e. CC'); re1 = D(w, A, 'simplr', [], '1 < ( Re ` W )'); kn = D(w, A, 'simpr', [], 'K e. NN')
    kc = D(w, A, 'nncnd', [kn], 'K e. CC'); kn0 = D(w, A, 'nnnn0d', [kn], 'K e. NN0')
    N1 = '( K + 1 )'
    n1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (A, N1))
    n1rp = D(w, A, 'nnrpd', [n1n], '%s e. RR+' % N1); n1c = D(w, A, 'nncnd', [n1n], '%s e. CC' % N1); n1z = D(w, A, 'nnne0d', [n1n], '%s =/= 0' % N1)
    n1n0 = D(w, A, 'nnnn0d', [n1n], '%s e. NN0' % N1)
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    wpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    wn = wne0v(w, A, 'W', wc, wpos)
    wp = w.s([wc, wpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % A)
    c1 = a1(w, A, 'ax-1cn', '1 e. CC')
    J = L.JN(N1, N1, 'W')
    EQ = lambda v: '( %s x. ( %s RiseFac ( %s + 1 ) ) ) = ( ( ! ` %s ) x. ( %s ^c %s ) )' % (L.JN(N1, N1, v), v, N1, N1, N1, v)
    jn = w.s([w.s([n1rp, n1n0], 'jca', '( %s -> ( %s e. RR+ /\\ %s e. NN0 ) )' % (A, N1, N1)), w.inst('zl3jn')], 'syl',
             '( %s -> A. w e. CC ( 1 < ( Re ` w ) -> %s ) )' % (A, EQ('w')))
    sw = jn_eq_sub_w(w, N1, 'w', 'W', N=N1)
    rs = w.s([sw], 'rspcv', '( W e. CC -> ( A. w e. CC ( 1 < ( Re ` w ) -> %s ) -> ( 1 < ( Re ` W ) -> %s ) ) )' % (EQ('w'), EQ('W')))
    eqJ = w.s([re1, w.s([wc, jn, rs], 'sylc', '( %s -> ( 1 < ( Re ` W ) -> %s ) )' % (A, EQ('W')))], 'mpd', '( %s -> %s )' % (A, EQ('W')))
    EU = L.EUT('W'); P = L.SQW('K')
    W1 = '( W + 1 )'
    R = '( %s RiseFac K )' % W1; Qp = '( %s + K )' % W1; FK = '( ! ` K )'; NW = '( %s ^c W )' % N1
    gp = w.s([w.s([wp, kn], 'jca', '( %s -> ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ K e. NN ) )' % A), w.inst('zl3gpk')], 'syl',
             '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A, P, R, NW, FK))
    rf1 = w.s([w.s([wc, n1n0], 'jca', '( %s -> ( W e. CC /\\ %s e. NN0 ) )' % (A, N1)), w.inst('zl3rfl')], 'syl',
              '( %s -> ( W RiseFac ( %s + 1 ) ) = ( W x. ( %s RiseFac %s ) ) )' % (A, N1, W1, N1))
    w1c = D(w, A, 'addcld', [wc, c1], '%s e. CC' % W1)
    rf2 = w.s([w1c, kn0, w.inst('risefacp1')], 'syl2anc', '( %s -> ( %s RiseFac %s ) = ( %s x. %s ) )' % (A, W1, N1, R, Qp))
    fc = w.s([kn0, w.inst('facp1')], 'syl', '( %s -> ( ! ` %s ) = ( %s x. %s ) )' % (A, N1, FK, N1))
    # closures
    uz = w.s([kn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % A)], 'eleqtrd', '( %s -> K e. ( ZZ>= ` 1 ) )' % A)
    pc = seq_cc(w, A, wp, uz)
    rc = w.s([w1c, kn0, w.inst('risefaccl')], 'syl2anc', '( %s -> %s e. CC )' % (A, R))
    qc = D(w, A, 'addcld', [w1c, kc], '%s e. CC' % Qp)
    fkc = D(w, A, 'nncnd', [w.s([kn0, w.inst('faccl')], 'syl', '( %s -> %s e. NN )' % (A, FK))], '%s e. CC' % FK)
    fkn = w.s([kn0, w.inst('facne0')], 'syl', '( %s -> %s =/= 0 )' % (A, FK))
    nwc = D(w, A, 'cxpcld', [n1c, wc], '%s e. CC' % NW); nwn = D(w, A, 'cxpne0d', [n1c, n1z, wc], '%s =/= 0' % NW)
    jc_ = None
    # J e. CC via integrability (context without integral hypotheses)
    ICC = '( 0 [,] %s )' % N1
    n1r = D(w, A, 'rpred', [n1rp], '%s e. RR' % N1)
    wm = D(w, A, 'subcld', [wc, c1], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, A, [re1], '0 < ( ( Re ` W ) - 1 )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw)})), re_sub1(w, A, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % A)
    cW1 = ccx(w, A, '( W - 1 )', wm, wmp, n1rp, N=N1)
    clA = Closure(w, A, {N1: ('RR', n1r), 'K': ('NN', kn)})
    clA.have(N1, 'ne0', n1z); clA.have(N1, 'NN0', n1n0)
    PN = '( ( 1 - ( x / %s ) ) ^ %s )' % (N1, N1)
    XW1 = '( x ^c ( W - 1 ) )'
    cj = cont(w, A, ICC, '( %s x. %s )' % (PN, XW1), clA, dom_cc(w, A, ICC, n1r), special={XW1: cW1})
    _, ij = ibl_of(w, A, N1, '( %s x. %s )' % (PN, XW1), cj, n1r)
    Ax, _ = dom_x(w, A, '( 0 (,) %s )' % N1, n1r)
    jc = w.s([w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PN, XW1))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Ax, PN, XW1)), ij], 'itgcl', '( %s -> %s e. CC )' % (A, J))
    # R =/= 0
    prn = w.s([gp, D(w, A, 'mulne0d', [nwc, nwn, fkc, fkn] if False else [nwc, fkc, nwn, fkn], '( %s x. %s ) =/= 0' % (NW, FK))], 'eqnetrd', '( %s -> ( %s x. %s ) =/= 0 )' % (A, P, R))
    rn = D(w, A, 'mulne0bbd', [pc, rc, prn], '%s =/= 0' % R)
    # Qp =/= 0 and Qp = N1 x. D
    Dd = '( ( W / %s ) + 1 )' % N1
    wdn = D(w, A, 'divcld', [wc, n1c, n1z], '( W / %s ) e. CC' % N1)
    dc = D(w, A, 'addcld', [wdn, c1], '%s e. CC' % Dd)
    qd = chain(w, A, [Qp, '( W + ( 1 + K ) )', '( W + %s )' % N1, '( ( %s x. ( W / %s ) ) + %s )' % (N1, N1, N1), '( ( %s x. ( W / %s ) ) + ( %s x. 1 ) )' % (N1, N1, N1), '( %s x. %s )' % (N1, Dd)],
               [E(w, A, 'addassd', [wc, c1, kc], Qp, '( W + ( 1 + K ) )'),
                E(w, A, 'oveq2d', [E(w, A, 'addcomd', [c1, kc], '( 1 + K )', N1)], '( W + ( 1 + K ) )', '( W + %s )' % N1),
                E(w, A, 'oveq1d', [w.s([E(w, A, 'divcan2d', [wc, n1c, n1z], '( %s x. ( W / %s ) )' % (N1, N1), 'W')], 'eqcomd', '( %s -> W = ( %s x. ( W / %s ) ) )' % (A, N1, N1))],
                  '( W + %s )' % N1, '( ( %s x. ( W / %s ) ) + %s )' % (N1, N1, N1)),
                E(w, A, 'oveq2d', [w.s([E(w, A, 'mulridd', [n1c], '( %s x. 1 )' % N1, N1)], 'eqcomd', '( %s -> %s = ( %s x. 1 ) )' % (A, N1, N1))],
                  '( ( %s x. ( W / %s ) ) + %s )' % (N1, N1, N1), '( ( %s x. ( W / %s ) ) + ( %s x. 1 ) )' % (N1, N1, N1)),
                ('r', E(w, A, 'adddid', [n1c, wdn, c1], '( %s x. %s )' % (N1, Dd), '( ( %s x. ( W / %s ) ) + ( %s x. 1 ) )' % (N1, N1, N1)))])
    rq = w.s([E(w, A, 'readdd', [w1c, kc], '( Re ` %s )' % Qp, '( ( Re ` %s ) + ( Re ` K ) )' % W1),
              E(w, A, 'oveq12d', [w.s([E(w, A, 'readdd', [wc, c1], '( Re ` %s )' % W1, '( ( Re ` W ) + ( Re ` 1 ) )'),
                                       E(w, A, 'oveq2d', [w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % A)], '( ( Re ` W ) + ( Re ` 1 ) )', '( ( Re ` W ) + 1 )')],
                                      'eqtrd', '( %s -> ( Re ` %s ) = ( ( Re ` W ) + 1 ) )' % (A, W1)),
                                  w.s([D(w, A, 'nnred', [kn], 'K e. RR'), w.inst('rered')], 'syl', '( %s -> ( Re ` K ) = K )' % A)],
                '( ( Re ` %s ) + ( Re ` K ) )' % W1, '( ( ( Re ` W ) + 1 ) + K )')], 'eqtrd', '( %s -> ( Re ` %s ) = ( ( ( Re ` W ) + 1 ) + K ) )' % (A, Qp))
    qpos = w.s([linarith(w, A, [wpos, D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), D(w, A, 'nnred', [kn], 'K e. RR'), D(w, A, 'nngt0d', [kn], '0 < K')], '0 <_ K')],
                         '0 < ( ( ( Re ` W ) + 1 ) + K )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw), 'K': ('RR', D(w, A, 'nnred', [kn], 'K e. RR'))})), rq], 'breqtrrd',
               '( %s -> 0 < ( Re ` %s ) )' % (A, Qp))
    qn = wne0v(w, A, Qp, qc, qpos)
    dn = D(w, A, 'mulne0bbd', [n1c, dc, w.s([w.s([qd], 'eqcomd', '( %s -> ( %s x. %s ) = %s )' % (A, N1, Dd, Qp)), qn], 'eqnetrd', '( %s -> ( %s x. %s ) =/= 0 )' % (A, N1, Dd))], '%s =/= 0' % Dd)
    # the equation
    T = ['( %s x. ( W RiseFac ( %s + 1 ) ) )' % (J, N1), '( %s x. ( W x. ( %s RiseFac %s ) ) )' % (J, W1, N1), '( %s x. ( W x. ( %s x. %s ) ) )' % (J, R, Qp),
         '( %s x. ( W x. ( %s x. %s ) ) )' % (J, Qp, R), '( %s x. ( ( W x. %s ) x. %s ) )' % (J, Qp, R), '( ( %s x. ( W x. %s ) ) x. %s )' % (J, Qp, R)]
    e = [E(w, A, 'oveq2d', [rf1], T[0], T[1]),
         E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [rf2], '( W x. ( %s RiseFac %s ) )' % (W1, N1), '( W x. ( %s x. %s ) )' % (R, Qp))], T[1], T[2]),
         E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [rc, qc], '( %s x. %s )' % (R, Qp), '( %s x. %s )' % (Qp, R))], '( W x. ( %s x. %s ) )' % (R, Qp), '( W x. ( %s x. %s ) )' % (Qp, R))], T[2], T[3]),
         E(w, A, 'oveq2d', [w.s([E(w, A, 'mulassd', [wc, qc, rc], '( ( W x. %s ) x. %s )' % (Qp, R), '( W x. ( %s x. %s ) )' % (Qp, R))], 'eqcomd',
                                '( %s -> ( W x. ( %s x. %s ) ) = ( ( W x. %s ) x. %s ) )' % (A, Qp, R, Qp, R))], T[3], T[4]),
         w.s([E(w, A, 'mulassd', [jc, D(w, A, 'mulcld', [wc, qc], '( W x. %s ) e. CC' % Qp), rc], T[5], T[4])], 'eqcomd', '( %s -> %s = %s )' % (A, T[4], T[5]))]
    lhs = chain(w, A, T, e)
    U = ['( ( ! ` %s ) x. %s )' % (N1, NW), '( ( %s x. %s ) x. %s )' % (FK, N1, NW), '( ( %s x. %s ) x. %s )' % (N1, FK, NW), '( %s x. ( %s x. %s ) )' % (N1, FK, NW),
         '( %s x. ( %s x. %s ) )' % (N1, NW, FK), '( %s x. ( %s x. %s ) )' % (N1, P, R), '( ( %s x. %s ) x. %s )' % (N1, P, R)]
    f = [E(w, A, 'oveq1d', [fc], U[0], U[1]),
         E(w, A, 'oveq1d', [E(w, A, 'mulcomd', [fkc, n1c], '( %s x. %s )' % (FK, N1), '( %s x. %s )' % (N1, FK))], U[1], U[2]),
         E(w, A, 'mulassd', [n1c, fkc, nwc], U[2], U[3]),
         E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [fkc, nwc], '( %s x. %s )' % (FK, NW), '( %s x. %s )' % (NW, FK))], U[3], U[4]),
         E(w, A, 'oveq2d', [w.s([gp], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A, NW, FK, P, R))], U[4], U[5]),
         w.s([E(w, A, 'mulassd', [n1c, pc, rc], U[6], U[5])], 'eqcomd', '( %s -> %s = %s )' % (A, U[5], U[6]))]
    rhs = chain(w, A, U, f)
    big = w.s([w.s([lhs, eqJ], 'eqtr3d', '( %s -> %s = %s )' % (A, T[5], U[0])), rhs], 'eqtrd', '( %s -> %s = %s )' % (A, T[5], U[6]))
    wq = D(w, A, 'mulcld', [wc, qc], '( W x. %s ) e. CC' % Qp)
    can = w.s([big, D(w, A, 'mulcan2d', [D(w, A, 'mulcld', [jc, wq], '( %s x. ( W x. %s ) ) e. CC' % (J, Qp)), D(w, A, 'mulcld', [n1c, pc], '( %s x. %s ) e. CC' % (N1, P)), rc, rn],
                                        '( %s <-> ( %s x. ( W x. %s ) ) = ( %s x. %s ) )' % (big and '%s = %s' % (T[5], U[6]), J, Qp, N1, P))], 'mpbid',
              '( %s -> ( %s x. ( W x. %s ) ) = ( %s x. %s ) )' % (A, J, Qp, N1, P))
    wqn = D(w, A, 'mulne0d', [wc, qc, wn, qn], '( W x. %s ) =/= 0' % Qp)
    jv = w.s([w.s([w.s([can], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s x. ( W x. %s ) ) )' % (A, N1, P, J, Qp)),
                   D(w, A, 'divmul3d', [D(w, A, 'mulcld', [n1c, pc], '( %s x. %s ) e. CC' % (N1, P)), jc, wq, wqn],
                     '( ( ( %s x. %s ) / ( W x. %s ) ) = %s <-> ( %s x. %s ) = ( %s x. ( W x. %s ) ) )' % (N1, P, Qp, J, N1, P, J, Qp))], 'mpbird',
                  '( %s -> ( ( %s x. %s ) / ( W x. %s ) ) = %s )' % (A, N1, P, Qp, J))], 'eqcomd', '( %s -> %s = ( ( %s x. %s ) / ( W x. %s ) ) )' % (A, J, N1, P, Qp))
    wd = D(w, A, 'mulcld', [wc, dc], '( W x. %s ) e. CC' % Dd); wdn0 = D(w, A, 'mulne0d', [wc, dc, wn, dn], '( W x. %s ) =/= 0' % Dd)
    V = ['( ( %s x. %s ) / ( W x. %s ) )' % (N1, P, Qp), '( ( %s x. %s ) / ( W x. ( %s x. %s ) ) )' % (N1, P, N1, Dd),
         '( ( %s x. %s ) / ( %s x. ( W x. %s ) ) )' % (N1, P, N1, Dd), '( %s / ( W x. %s ) )' % (P, Dd), '( %s / ( %s x. W ) )' % (P, Dd),
         '( ( %s / %s ) / W )' % (P, Dd), '( ( 1 / W ) x. ( %s / %s ) )' % (P, Dd), '( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) )' % (P, Dd)]
    g = [E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [qd], '( W x. %s )' % Qp, '( W x. ( %s x. %s ) )' % (N1, Dd))], V[0], V[1]),
         E(w, A, 'oveq2d', [E(w, A, 'mul12d', [wc, n1c, dc], '( W x. ( %s x. %s ) )' % (N1, Dd), '( %s x. ( W x. %s ) )' % (N1, Dd))], V[1], V[2]),
         E(w, A, 'divcan5d', [pc, wd, n1c, wdn0, n1z], V[2], V[3]),
         E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [wc, dc], '( W x. %s )' % Dd, '( %s x. W )' % Dd)], V[3], V[4]),
         ('r', E(w, A, 'divdiv1d', [pc, dc, wc, dn, wn], V[5], V[4])),
         E(w, A, 'divrec2d', [D(w, A, 'divcld', [pc, dc, dn], '( %s / %s ) e. CC' % (P, Dd)), wc, wn], V[5], V[6]),
         E(w, A, 'oveq2d', [E(w, A, 'divrecd', [pc, dc, dn], '( %s / %s )' % (P, Dd), '( %s x. ( 1 / %s ) )' % (P, Dd))], V[6], V[7])]
    q = w.s([jv, chain(w, A, V, g)], 'eqtrd', 'x')
    finish(w, q, 'zl3qid')
    go(w)


# ---------------------------------------------------------------- zl3qlim
if want('zl3qlim'):
    w = W('zl3qlim', "The approximants ` S. ( 0 , k + 1 ) ( 1 - x / ( k + 1 ) ) ^ ( k + 1 ) x ^ ( W - 1 ) dx ` converge to ` Gamma ( W ) ` "
          '( ~ zl3qid , ~ gamcvg2 , ~ divcnvshft , ~ climrec ).')
    A, Cc = ante_of('zl3qlim')
    wc = D(w, A, 'simpl', [], 'W e. CC'); re1 = D(w, A, 'simpr', [], '1 < ( Re ` W )')
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    wpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    wn = wne0v(w, A, 'W', wc, wpos)
    wp = w.s([wc, wpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % A)
    EU = L.EUT('W')
    SEQ = 'seq 1 ( x. , %s )' % EU
    Z = '( ZZ>= ` 1 )'
    zeq = w.s([], 'eqid', '%s = %s' % (Z, Z))
    one = a1(w, A, '1z', '1 e. ZZ')
    def dfacts(C, kk, knst):
        K1 = '( %s + 1 )' % kk
        wk = D(w, C, 'adantr', [wc], 'W e. CC')
        k1n = w.s([knst, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (C, K1))
        k1c = D(w, C, 'nncnd', [k1n], '%s e. CC' % K1); k1z = D(w, C, 'nnne0d', [k1n], '%s =/= 0' % K1)
        Q2 = '( W / %s )' % K1; Dk = '( %s + 1 )' % Q2
        q2c = D(w, C, 'divcld', [wk, k1c, k1z], '%s e. CC' % Q2)
        dkc = D(w, C, 'addcld', [q2c, a1(w, C, 'ax-1cn', '1 e. CC')], '%s e. CC' % Dk)
        k1r = D(w, C, 'nnred', [k1n], '%s e. RR' % K1)
        rdk = chain(w, C, ['( Re ` %s )' % Dk, '( ( Re ` %s ) + ( Re ` 1 ) )' % Q2, '( ( ( Re ` W ) / %s ) + 1 )' % K1],
                    [E(w, C, 'readdd', [q2c, a1(w, C, 'ax-1cn', '1 e. CC')], '( Re ` %s )' % Dk, '( ( Re ` %s ) + ( Re ` 1 ) )' % Q2),
                     E(w, C, 'oveq12d', [E(w, C, 'redivd', [k1r, wk, k1z], '( Re ` %s )' % Q2, '( ( Re ` W ) / %s )' % K1),
                                         w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( %s -> ( Re ` 1 ) = 1 )' % C)],
                       '( ( Re ` %s ) + ( Re ` 1 ) )' % Q2, '( ( ( Re ` W ) / %s ) + 1 )' % K1)])
        rwk = D(w, C, 'adantr', [rw], '( Re ` W ) e. RR')
        dq = D(w, C, 'divgt0d', [rwk, k1r, D(w, C, 'adantr', [wpos], '0 < ( Re ` W )'), D(w, C, 'nngt0d', [k1n], '0 < %s' % K1)], '0 < ( ( Re ` W ) / %s )' % K1)
        rq = D(w, C, 'redivcld', [rwk, k1r, k1z], '( ( Re ` W ) / %s ) e. RR' % K1)
        dpos = w.s([linarith(w, C, [dq], '0 < ( ( ( Re ` W ) / %s ) + 1 )' % K1, closure=Closure(w, C, {'( ( Re ` W ) / %s )' % K1: ('RR', rq)})), rdk], 'breqtrrd',
                   '( %s -> 0 < ( Re ` %s ) )' % (C, Dk))
        dn = wne0v(w, C, Dk, dkc, dpos)
        cz = '( CC \\ { 0 } )'
        dm = w.s([w.s([dkc, dn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (C, Dk, Dk)), w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (Dk, cz, Dk, Dk))],
                 'sylibr', '( %s -> %s e. %s )' % (C, Dk, cz))
        return dict(K1=K1, Q2=Q2, Dk=Dk, q2c=q2c, dkc=dkc, dn=dn, dm=dm, wk=wk)
    Ak = '( %s /\\ k e. %s )' % (A, Z)
    kz = D(w, Ak, 'simpr', [], 'k e. %s' % Z)
    kn = w.s([kz, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % Ak)], 'eleqtrrd', '( %s -> k e. NN )' % Ak)
    df = dfacts(Ak, 'k', kn)
    K1, Q2, Dk, q2c, dkc, dn = df['K1'], df['Q2'], df['Dk'], df['q2c'], df['dkc'], df['dn']
    # the sequences
    cz = '( CC \\ { 0 } )'
    MAPS = {}
    def ktn(t):
        return ' '.join('n' if x == 'k' else x for x in t.split(' '))
    def mp(body):
        return '( n e. NN |-> %s )' % ktn(body)
    def ktm(t):
        return ' '.join('m' if x == 'k' else x for x in t.split(' '))
    F2 = '( m e. NN |-> %s )' % ktm(Q2); F3 = '( m e. NN |-> %s )' % ktm(Dk); F4 = '( n e. NN |-> ( 1 / ( %s ` n ) ) )' % F3
    def valm(body_k):
        st, v = mptv(w, Ak, 'm', 'NN', ktm(body_k), 'k', kn)
        assert v == body_k
        return st
    Pk = '( %s ` k )' % SEQ
    F5 = mp('( %s x. ( 1 / %s ) )' % (Pk, Dk)); F6 = mp('( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) )' % (Pk, Dk))
    def ex(F):
        return w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % F)], 'a1i', '( %s -> %s e. _V )' % (A, F))
    def val(F, body_k):
        st, v = mptv(w, Ak, 'n', 'NN', ktn(body_k), 'k', kn)
        assert v == body_k, (v, body_k)
        return st
    g0 = w.s([w.s([], 'eqid', '%s = %s' % (EU, EU)), w.s([wp, w.inst('zrenn')], 'syl', '( %s -> W e. ( CC \\ ( ZZ \\ NN ) ) )' % A)], 'gamcvg2',
             '( %s -> %s ~~> ( ( _G ` W ) x. W ) )' % (A, SEQ))
    l2 = w.s([zeq, one, wc, one, ex(F2), valm(Q2)], 'divcnvshft', '( %s -> %s ~~> 0 )' % (A, F2))
    v2 = valm(Q2)
    l3 = w.s([zeq, one, l2, a1(w, A, 'ax-1cn', '1 e. CC'), ex(F3), w.s([v2, q2c], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F2)),
              w.s([valm(Dk), w.s([v2], 'oveq1d', '( %s -> ( ( %s ` k ) + 1 ) = ( %s + 1 ) )' % (Ak, F2, Q2))], 'eqtr4d', '( %s -> ( %s ` k ) = ( ( %s ` k ) + 1 ) )' % (Ak, F3, F2))],
             'climaddc1', '( %s -> %s ~~> ( 0 + 1 ) )' % (A, F3))
    v3 = valm(Dk)
    cz = '( CC \\ { 0 } )'
    dm = w.s([w.s([dkc, dn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (Ak, Dk, Dk)), w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (Dk, cz, Dk, Dk))],
             'sylibr', '( %s -> %s e. %s )' % (Ak, Dk, cz))
    n01 = w.s([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1'), w.s([], 'ax-1ne0', '1 =/= 0')], 'eqnetri', '( 0 + 1 ) =/= 0')], 'a1i', '( %s -> ( 0 + 1 ) =/= 0 )' % A)
    n01m = w.s([w.s([w.s([w.s([w.s([], '0cn', '0 e. CC'), w.s([], 'ax-1cn', '1 e. CC')], 'addcli', '( 0 + 1 ) e. CC')], 'a1i', '( %s -> ( 0 + 1 ) e. CC )' % A), n01], 'jca',
                     '( %s -> ( ( 0 + 1 ) e. CC /\\ ( 0 + 1 ) =/= 0 ) )' % A), w.s([], 'eldifsn', '( ( 0 + 1 ) e. %s <-> ( ( 0 + 1 ) e. CC /\\ ( 0 + 1 ) =/= 0 ) )' % cz)],
                'sylibr', '( %s -> ( 0 + 1 ) e. %s )' % (A, cz))
    Aj = '( %s /\\ j e. NN )' % A
    dj = dfacts(Aj, 'j', D(w, Aj, 'simpr', [], 'j e. NN'))
    vj, _ = mptv(w, Aj, 'm', 'NN', ktm(Dk), 'j', D(w, Aj, 'simpr', [], 'j e. NN'))
    jm = w.s([vj, dj['dm']], 'eqeltrd', '( %s -> ( %s ` j ) e. %s )' % (Aj, F3, cz))
    alj = w.s([jm], 'ralrimiva', '( %s -> A. j e. NN ( %s ` j ) e. %s )' % (A, F3, cz))
    l4 = w.s([w.s([l3, n01m, alj], '3jca', '( %s -> ( %s ~~> ( 0 + 1 ) /\\ ( 0 + 1 ) e. %s /\\ A. j e. NN ( %s ` j ) e. %s ) )' % (A, F3, cz, F3, cz)), w.inst('zl3crec')], 'syl',
             '( %s -> %s ~~> ( 1 / ( 0 + 1 ) ) )' % (A, F4))
    v4a, _ = mptv(w, Ak, 'n', 'NN', '( 1 / ( %s ` n ) )' % F3, 'k', kn)
    v4 = w.s([v4a, w.s([v3], 'oveq2d', '( %s -> ( 1 / ( %s ` k ) ) = ( 1 / %s ) )' % (Ak, F3, Dk))], 'eqtrd', '( %s -> ( %s ` k ) = ( 1 / %s ) )' % (Ak, F4, Dk))
    rdc = D(w, Ak, 'reccld', [dkc, dn], '( 1 / %s ) e. CC' % Dk)
    pkc = seq_cc(w, Ak, D(w, Ak, 'adantr', [wp], '( W e. CC /\\ 0 < ( Re ` W ) )'), kz)
    l5 = w.s([zeq, one, g0, ex(F5), l4, pkc, w.s([v4, rdc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F4)),
              w.s([val(F5, '( %s x. ( 1 / %s ) )' % (Pk, Dk)), w.s([v4], 'oveq2d', '( %s -> ( %s x. ( %s ` k ) ) = ( %s x. ( 1 / %s ) ) )' % (Ak, Pk, F4, Pk, Dk))], 'eqtr4d',
                  '( %s -> ( %s ` k ) = ( %s x. ( %s ` k ) ) )' % (Ak, F5, Pk, F4))], 'climmul', '( %s -> %s ~~> ( ( ( _G ` W ) x. W ) x. ( 1 / ( 0 + 1 ) ) ) )' % (A, F5))
    v5 = val(F5, '( %s x. ( 1 / %s ) )' % (Pk, Dk))
    rwc = D(w, A, 'reccld', [wc, wn], '( 1 / W ) e. CC')
    l6 = w.s([zeq, one, l5, rwc, ex(F6), w.s([v5, D(w, Ak, 'mulcld', [pkc, rdc], '( %s x. ( 1 / %s ) ) e. CC' % (Pk, Dk))], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F5)),
              w.s([val(F6, '( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) )' % (Pk, Dk)), w.s([v5], 'oveq2d', '( %s -> ( ( 1 / W ) x. ( %s ` k ) ) = ( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) ) )' % (Ak, F5, Pk, Dk))],
                  'eqtr4d', '( %s -> ( %s ` k ) = ( ( 1 / W ) x. ( %s ` k ) ) )' % (Ak, F6, F5))], 'climmulc2',
             '( %s -> %s ~~> ( ( 1 / W ) x. ( ( ( _G ` W ) x. W ) x. ( 1 / ( 0 + 1 ) ) ) ) )' % (A, F6))
    # the target mapping equals F6
    An = '( %s /\\ k e. NN )' % A
    qi = w.s([w.s([D(w, An, 'simpl', [], A), D(w, An, 'simpr', [], 'k e. NN')], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (An, A)), w.inst('zl3qid')], 'syl',
             '( %s -> %s = ( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) ) )' % (An, L.JN(K1, K1, 'W'), Pk, Dk))
    MJ = '( k e. NN |-> %s )' % L.JN(K1, K1, 'W')
    F6k = '( k e. NN |-> ( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) ) )' % (Pk, Dk)
    meq0 = w.s([qi], 'mpteq2dva', '( %s -> %s = %s )' % (A, MJ, F6k))
    idk = w.s([], 'id', '( k = n -> k = n )')
    cst, cv = w.congr('( ( 1 / W ) x. ( %s x. ( 1 / %s ) ) )' % (Pk, Dk), {'k': 'n'}, 'k = n', {'k': idk})
    cb = w.s([cst], 'cbvmptv', '%s = %s' % (F6k, F6))
    meq = w.s([meq0, w.s([cb], 'a1i', '( %s -> %s = %s )' % (A, F6k, F6))], 'eqtrd', '( %s -> %s = %s )' % (A, MJ, F6))
    gc = w.s([w.s([wp, w.inst('zrenn')], 'syl', '( %s -> W e. ( CC \\ ( ZZ \\ NN ) ) )' % A), w.inst('gamcl')], 'syl', '( %s -> ( _G ` W ) e. CC )' % A)
    GW = '( ( _G ` W ) x. W )'
    gwc = D(w, A, 'mulcld', [gc, wc], '%s e. CC' % GW)
    lv = chain(w, A, ['( ( 1 / W ) x. ( %s x. ( 1 / ( 0 + 1 ) ) ) )' % GW, '( ( 1 / W ) x. ( %s x. ( 1 / 1 ) ) )' % GW, '( ( 1 / W ) x. ( %s x. 1 ) )' % GW,
                      '( ( 1 / W ) x. %s )' % GW, '( %s / W )' % GW, '( _G ` W )'],
               [E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % A)], '( 1 / ( 0 + 1 ) )', '( 1 / 1 )')],
                                                 '( %s x. ( 1 / ( 0 + 1 ) ) )' % GW, '( %s x. ( 1 / 1 ) )' % GW)],
                  '( ( 1 / W ) x. ( %s x. ( 1 / ( 0 + 1 ) ) ) )' % GW, '( ( 1 / W ) x. ( %s x. ( 1 / 1 ) ) )' % GW),
                E(w, A, 'oveq2d', [E(w, A, 'oveq2d', [w.s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( %s -> ( 1 / 1 ) = 1 )' % A)], '( %s x. ( 1 / 1 ) )' % GW, '( %s x. 1 )' % GW)],
                  '( ( 1 / W ) x. ( %s x. ( 1 / 1 ) ) )' % GW, '( ( 1 / W ) x. ( %s x. 1 ) )' % GW),
                E(w, A, 'oveq2d', [E(w, A, 'mulridd', [gwc], '( %s x. 1 )' % GW, GW)], '( ( 1 / W ) x. ( %s x. 1 ) )' % GW, '( ( 1 / W ) x. %s )' % GW),
                ('r', E(w, A, 'divrec2d', [gwc, wc, wn], '( %s / W )' % GW, '( ( 1 / W ) x. %s )' % GW)),
                E(w, A, 'divcan4d', [gc, wc, wn], '( %s / W )' % GW, '( _G ` W )')])
    q = w.s([w.s([meq, l6], 'eqbrtrd', '( %s -> %s ~~> ( ( 1 / W ) x. ( %s x. ( 1 / ( 0 + 1 ) ) ) ) )' % (A, MJ, GW)), lv], 'breqtrd', 'x')
    finish(w, q, 'zl3qlim')
    go(w)


# ---------------------------------------------------------------- zl3crec
if want('zl3crec'):
    w = W('zl3crec', 'The reciprocal of a convergent sequence of nonzero complex numbers with a nonzero limit converges to the reciprocal '
          '( ~ climcn1 with ~ reccn2 ).')
    A, Cc = ante_of('zl3crec')
    CZ = '( CC \\ { 0 } )'
    FZ = '( z e. %s |-> ( 1 / z ) )' % CZ
    H = '( n e. NN |-> ( 1 / ( G ` n ) ) )'
    gl = D(w, A, 'simp1', [], 'G ~~> A'); am = D(w, A, 'simp2', [], 'A e. %s' % CZ); gall = D(w, A, 'simp3', [], 'A. j e. NN ( G ` j ) e. %s' % CZ)
    Z = '( ZZ>= ` 1 )'
    Az = '( %s /\\ z e. %s )' % (A, CZ)
    zm = D(w, Az, 'simpr', [], 'z e. %s' % CZ)
    zcn = w.s([zm, w.s([], 'eldifsn', '( z e. %s <-> ( z e. CC /\\ z =/= 0 ) )' % CZ)], 'sylib', '( %s -> ( z e. CC /\\ z =/= 0 ) )' % Az)
    zc = D(w, Az, 'simpld', [zcn], 'z e. CC'); zn = D(w, Az, 'simprd', [zcn], 'z =/= 0')
    fz, _ = mptv(w, Az, 'z', CZ, '( 1 / z )', 'z', zm) if False else (None, None)
    # value F ` z via a fresh letter: use fvmpt on z with binder z is disallowed; rebind F with u
    FU = '( u e. %s |-> ( 1 / u ) )' % CZ
    fz, _ = mptv(w, Az, 'u', CZ, '( 1 / u )', 'z', zm)
    fzc = w.s([fz, D(w, Az, 'reccld', [zc, zn], '( 1 / z ) e. CC')], 'eqeltrd', '( %s -> ( %s ` z ) e. CC )' % (Az, FU))
    acn = w.s([am, w.s([], 'eldifsn', '( A e. %s <-> ( A e. CC /\\ A =/= 0 ) )' % CZ)], 'sylib', '( %s -> ( A e. CC /\\ A =/= 0 ) )' % A)
    fa, _ = mptv(w, A, 'u', CZ, '( 1 / u )', 'A', am)
    # epsilon-delta
    Ax = '( %s /\\ x e. RR+ )' % A
    TT = '( if ( 1 <_ ( ( abs ` A ) x. x ) , 1 , ( ( abs ` A ) x. x ) ) x. ( ( abs ` A ) / 2 ) )'
    rc = w.s([w.s([D(w, Ax, 'adantr', [am], 'A e. %s' % CZ), D(w, Ax, 'simpr', [], 'x e. RR+')], 'jca', '( %s -> ( A e. %s /\\ x e. RR+ ) )' % (Ax, CZ)),
              w.s([w.s([], 'eqid', '%s = %s' % (TT, TT))], 'reccn2', '( ( A e. %s /\\ x e. RR+ ) -> E. y e. RR+ A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < x ) )' % (CZ, CZ))],
             'syl', '( %s -> E. y e. RR+ A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < x ) )' % (Ax, CZ))
    Axyz = '( ( ( %s /\\ y e. RR+ ) /\\ z e. %s ) )' % (Ax, CZ)
    Axyz = '( ( %s /\\ y e. RR+ ) /\\ z e. %s )' % (Ax, CZ)
    fz2, _ = mptv(w, Axyz, 'u', CZ, '( 1 / u )', 'z', D(w, Axyz, 'simpr', [], 'z e. %s' % CZ))
    fa2 = w.s([fa], 'ad2antrr', '( %s -> ( %s ` A ) = ( 1 / A ) )' % (Axyz, FU)) if False else w.s([w.s([w.s([fa], 'adantr', '( %s -> ( %s ` A ) = ( 1 / A ) )' % (Ax, FU))], 'adantr',
                                                                                                  '( ( %s /\\ y e. RR+ ) -> ( %s ` A ) = ( 1 / A ) )' % (Ax, FU))], 'adantr', '( %s -> ( %s ` A ) = ( 1 / A ) )' % (Axyz, FU))
    ev = w.s([w.s([w.s([fz2, fa2], 'oveq12d', '( %s -> ( ( %s ` z ) - ( %s ` A ) ) = ( ( 1 / z ) - ( 1 / A ) ) )' % (Axyz, FU, FU))], 'fveq2d',
                  '( %s -> ( abs ` ( ( %s ` z ) - ( %s ` A ) ) ) = ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) )' % (Axyz, FU, FU))], 'breq1d',
             '( %s -> ( ( abs ` ( ( %s ` z ) - ( %s ` A ) ) ) < x <-> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < x ) )' % (Axyz, FU, FU))
    ev2 = w.s([ev], 'imbi2d', '( %s -> ( ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( %s ` z ) - ( %s ` A ) ) ) < x ) <-> ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < x ) ) )' % (Axyz, FU, FU))
    ev3 = w.s([ev2], 'ralbidva', '( ( %s /\\ y e. RR+ ) -> ( A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( %s ` z ) - ( %s ` A ) ) ) < x ) <-> A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < x ) ) )' % (Ax, CZ, FU, FU, CZ))
    ev4 = w.s([ev3], 'rexbidva', '( %s -> ( E. y e. RR+ A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( %s ` z ) - ( %s ` A ) ) ) < x ) <-> E. y e. RR+ A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( 1 / z ) - ( 1 / A ) ) ) < x ) ) )' % (Ax, CZ, FU, FU, CZ))
    ed = w.s([rc, ev4], 'mpbird', '( %s -> E. y e. RR+ A. z e. %s ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( %s ` z ) - ( %s ` A ) ) ) < x ) )' % (Ax, CZ, FU, FU))
    Ak = '( %s /\\ k e. %s )' % (A, Z)
    kn = w.s([D(w, Ak, 'simpr', [], 'k e. %s' % Z), w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % Ak)], 'eleqtrrd', '( %s -> k e. NN )' % Ak)
    gk = w.s([w.s([], 'fveq2', '( j = k -> ( G ` j ) = ( G ` k ) )')], 'eleq1d', '( j = k -> ( ( G ` j ) e. %s <-> ( G ` k ) e. %s ) )' % (CZ, CZ))
    gkm = w.s([kn, w.s([gall], 'adantr', '( %s -> A. j e. NN ( G ` j ) e. %s )' % (Ak, CZ)), w.s([gk], 'rspcv', '( k e. NN -> ( A. j e. NN ( G ` j ) e. %s -> ( G ` k ) e. %s ) )' % (CZ, CZ))],
              'sylc', '( %s -> ( G ` k ) e. %s )' % (Ak, CZ))
    hv, _ = mptv(w, Ak, 'n', 'NN', '( 1 / ( G ` n ) )', 'k', kn)
    fg, _ = mptv(w, Ak, 'u', CZ, '( 1 / u )', '( G ` k )', gkm)
    hk = w.s([hv, fg], 'eqtr4d', '( %s -> ( %s ` k ) = ( %s ` ( G ` k ) ) )' % (Ak, H, FU))
    hex = w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % H)], 'a1i', '( %s -> %s e. _V )' % (A, H))
    cn = w.s([w.s([], 'eqid', '%s = %s' % (Z, Z)), a1(w, A, '1z', '1 e. ZZ'), am, fzc, gl, hex, ed, gkm, hk], 'climcn1', '( %s -> %s ~~> ( %s ` A ) )' % (A, H, FU))
    q = w.s([cn, fa], 'breqtrd', 'x')
    finish(w, q, 'zl3crec')
    go(w)


# ---------------------------------------------------------------- zl3ebd
if want('zl3ebd'):
    w = W('zl3ebd', 'For ` 0 <_ U <_ N ` : ` 0 <_ ( 1 - U / N ) ^ N <_ e ^ -U ` and ` e ^ -U - ( 1 - U / N ) ^ N <_ U ^ 2 e ^ -U / N ` '
          '( ~ bvexpl1 , ~ bvefge1p , ~ bernneq on ` ( 1 - U ^ 2 / N ^ 2 ) ^ N ` ).')
    A, Cc = ante_of('zl3ebd')
    nn = D(w, A, 'simpl', [], 'N e. NN'); ur = D(w, A, 'simpr1', [], 'U e. RR'); u0 = D(w, A, 'simpr2', [], '0 <_ U'); un = D(w, A, 'simpr3', [], 'U <_ N')
    nr = D(w, A, 'nnred', [nn], 'N e. RR'); nrp = D(w, A, 'nnrpd', [nn], 'N e. RR+'); nc = D(w, A, 'nncnd', [nn], 'N e. CC'); nz = D(w, A, 'nnne0d', [nn], 'N =/= 0')
    nn0 = D(w, A, 'nnnn0d', [nn], 'N e. NN0')
    T = '( U / N )'
    tr = D(w, A, 'redivcld', [ur, nr, nz], '%s e. RR' % T)
    t0 = D(w, A, 'divge0d', [ur, nrp, u0], '0 <_ %s' % T)
    t1 = w.s([un, w.s([ur, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> U <_ N ) )' % (A, T))], 'mpbird', '( %s -> %s <_ 1 )' % (A, T))
    tc = D(w, A, 'recnd', [tr], '%s e. CC' % T)
    Aa = '( 1 - %s )' % T; Bb = '( 1 + %s )' % T
    ar = D(w, A, 'resubcld', [a1(w, A, '1re', '1 e. RR'), tr], '%s e. RR' % Aa)
    br = D(w, A, 'readdcld', [a1(w, A, '1re', '1 e. RR'), tr], '%s e. RR' % Bb)
    ET = '( exp ` -u %s )' % T; EPT = '( exp ` %s )' % T
    etr = D(w, A, 'reefcld', [D(w, A, 'renegcld', [tr], '-u %s e. RR' % T)], '%s e. RR' % ET)
    eptr = D(w, A, 'reefcld', [tr], '%s e. RR' % EPT)
    cl = Closure(w, A, {T: ('RR', tr), ET: ('RR', etr), EPT: ('RR', eptr)})
    a0 = linarith(w, A, [t1], '0 <_ %s' % Aa, closure=cl)
    b0 = linarith(w, A, [t0], '0 <_ %s' % Bb, closure=cl)
    bx = w.s([w.s([tr, t0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, T, T)), w.inst('bvexpl1')], 'syl', '( %s -> ( 1 - %s ) <_ %s )' % (A, ET, T))
    ae = linarith(w, A, [bx], '%s <_ %s' % (Aa, ET), closure=cl)
    bf = w.s([w.s([tr, t0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, T, T)), w.inst('bvefge1p')], 'syl', '( %s -> %s <_ %s )' % (A, Bb, EPT))
    AN = '( %s ^ N )' % Aa; BN = '( %s ^ N )' % Bb
    an0 = w.s([ar, nn0, a0, w.inst('expge0')], 'syl3anc', '( %s -> 0 <_ %s )' % (A, AN))
    le1 = w.s([w.s([ar, etr, nn0], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ N e. NN0 ) )' % (A, Aa, ET)), w.s([a0, ae], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ %s ) )' % (A, Aa, Aa, ET)),
               w.inst('leexp1a')], 'syl2anc', '( %s -> %s <_ ( %s ^ N ) )' % (A, AN, ET))
    nzz = D(w, A, 'nnzd', [nn], 'N e. ZZ')
    # ( exp ` -u T ) ^ N = exp ` -u U
    nmt = chain(w, A, ['( N x. -u %s )' % T, '-u ( N x. %s )' % T, '-u U'],
                [E(w, A, 'mulneg2d', [nc, tc], '( N x. -u %s )' % T, '-u ( N x. %s )' % T),
                 E(w, A, 'negeqd', [E(w, A, 'divcan2d', [D(w, A, 'recnd', [ur], 'U e. CC'), nc, nz], '( N x. %s )' % T, 'U')], '-u ( N x. %s )' % T, '-u U')])
    ex1 = w.s([w.s([w.s([D(w, A, 'negcld', [tc], '-u %s e. CC' % T), nzz, w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` ( N x. -u %s ) ) = ( %s ^ N ) )' % (A, T, ET))], 'eqcomd',
                   '( %s -> ( %s ^ N ) = ( exp ` ( N x. -u %s ) ) )' % (A, ET, T)), E(w, A, 'fveq2d', [nmt], '( exp ` ( N x. -u %s ) )' % T, '( exp ` -u U )')], 'eqtrd',
              '( %s -> ( %s ^ N ) = ( exp ` -u U ) )' % (A, ET))
    p2 = w.s([le1, ex1], 'breqtrd', '( %s -> %s <_ ( exp ` -u U ) )' % (A, AN))
    # B ^ N <_ exp ` U
    le2 = w.s([w.s([br, eptr, nn0], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ N e. NN0 ) )' % (A, Bb, EPT)), w.s([b0, bf], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ %s ) )' % (A, Bb, Bb, EPT)),
               w.inst('leexp1a')], 'syl2anc', '( %s -> %s <_ ( %s ^ N ) )' % (A, BN, EPT))
    ex2 = w.s([w.s([w.s([tc, nzz, w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` ( N x. %s ) ) = ( %s ^ N ) )' % (A, T, EPT))], 'eqcomd', '( %s -> ( %s ^ N ) = ( exp ` ( N x. %s ) ) )' % (A, EPT, T)),
               E(w, A, 'fveq2d', [E(w, A, 'divcan2d', [D(w, A, 'recnd', [ur], 'U e. CC'), nc, nz], '( N x. %s )' % T, 'U')], '( exp ` ( N x. %s ) )' % T, '( exp ` U )')], 'eqtrd',
              '( %s -> ( %s ^ N ) = ( exp ` U ) )' % (A, EPT))
    bE = w.s([le2, ex2], 'breqtrd', '( %s -> %s <_ ( exp ` U ) )' % (A, BN))
    # ( A x. B ) ^ N = A^N B^N ; A x. B = 1 + -u ( T ^ 2 )
    AB = '( %s x. %s )' % (Aa, Bb)
    Q = '( 1 + -u ( %s ^ 2 ) )' % T
    c1_ = a1(w, A, 'ax-1cn', '1 e. CC')
    abq = chain(w, A, [AB, '( %s x. %s )' % (Bb, Aa), '( ( 1 ^ 2 ) - ( %s ^ 2 ) )' % T, '( 1 - ( %s ^ 2 ) )' % T, Q],
                [E(w, A, 'mulcomd', [D(w, A, 'recnd', [ar], '%s e. CC' % Aa), D(w, A, 'recnd', [br], '%s e. CC' % Bb)], AB, '( %s x. %s )' % (Bb, Aa)),
                 ('r', w.s([c1_, tc, w.inst('subsq')], 'syl2anc', '( %s -> ( ( 1 ^ 2 ) - ( %s ^ 2 ) ) = ( %s x. %s ) )' % (A, T, Bb, Aa))),
                 E(w, A, 'oveq1d', [w.s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( %s -> ( 1 ^ 2 ) = 1 )' % A)], '( ( 1 ^ 2 ) - ( %s ^ 2 ) )' % T, '( 1 - ( %s ^ 2 ) )' % T),
                 ('r', E(w, A, 'negsubd', [c1_, D(w, A, 'sqcld', [tc], '( %s ^ 2 ) e. CC' % T)], Q, '( 1 - ( %s ^ 2 ) )' % T))])
    me = E(w, A, 'mulexpd', [D(w, A, 'recnd', [ar], '%s e. CC' % Aa), D(w, A, 'recnd', [br], '%s e. CC' % Bb), nn0], '( %s ^ N )' % AB, '( %s x. %s )' % (AN, BN))
    t2r = D(w, A, 'resqcld', [tr], '( %s ^ 2 ) e. RR' % T)
    t2le = nlinarith(w, A, [t0, t1], '( %s ^ 2 ) <_ 1' % T, closure=cl)
    nt2 = linarith(w, A, [t2le], '-u 1 <_ -u ( %s ^ 2 )' % T, closure=Closure(w, A, {'( %s ^ 2 )' % T: ('RR', t2r)}))
    bn = w.s([D(w, A, 'renegcld', [t2r], '-u ( %s ^ 2 ) e. RR' % T), nn0, nt2, w.inst('bernneq')], 'syl3anc', '( %s -> ( 1 + ( -u ( %s ^ 2 ) x. N ) ) <_ ( %s ^ N ) )' % (A, T, Q))
    q2 = w.s([bn, w.s([w.s([abq], 'oveq1d', '( %s -> ( %s ^ N ) = ( %s ^ N ) )' % (A, AB, Q)), me], 'eqtr3d', '( %s -> ( %s ^ N ) = ( %s x. %s ) )' % (A, Q, AN, BN))], 'breqtrd',
             '( %s -> ( 1 + ( -u ( %s ^ 2 ) x. N ) ) <_ ( %s x. %s ) )' % (A, T, AN, BN))
    EU = '( exp ` U )'; EMU = '( exp ` -u U )'
    eur = D(w, A, 'reefcld', [ur], '%s e. RR' % EU); emur = D(w, A, 'reefcld', [D(w, A, 'renegcld', [ur], '-u U e. RR')], '%s e. RR' % EMU)
    anr = D(w, A, 'reexpcld', [ar, nn0], '%s e. RR' % AN); bnr = D(w, A, 'reexpcld', [br, nn0], '%s e. RR' % BN)
    q3 = D(w, A, 'lemul2ad', [bnr, eur, anr, an0, bE], '( %s x. %s ) <_ ( %s x. %s )' % (AN, BN, AN, EU))
    q4 = D(w, A, 'letrd', [D(w, A, 'readdcld', [a1(w, A, '1re', '1 e. RR'), D(w, A, 'remulcld', [D(w, A, 'renegcld', [t2r], '-u ( %s ^ 2 ) e. RR' % T), nr], '( -u ( %s ^ 2 ) x. N ) e. RR' % T)],
                                     '( 1 + ( -u ( %s ^ 2 ) x. N ) ) e. RR' % T), D(w, A, 'remulcld', [anr, bnr], '( %s x. %s ) e. RR' % (AN, BN)),
                           D(w, A, 'remulcld', [anr, eur], '( %s x. %s ) e. RR' % (AN, EU)), q2, q3], '( 1 + ( -u ( %s ^ 2 ) x. N ) ) <_ ( %s x. %s )' % (T, AN, EU))
    emu0 = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), emur, w.s([D(w, A, 'renegcld', [ur], '-u U e. RR'), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, EMU))], '0 <_ %s' % EMU)
    LL = '( 1 + ( -u ( %s ^ 2 ) x. N ) )' % T
    q5 = D(w, A, 'lemul1ad', [D(w, A, 'readdcld', [a1(w, A, '1re', '1 e. RR'), D(w, A, 'remulcld', [D(w, A, 'renegcld', [t2r], '-u ( %s ^ 2 ) e. RR' % T), nr], '( -u ( %s ^ 2 ) x. N ) e. RR' % T)], '%s e. RR' % LL),
                              D(w, A, 'remulcld', [anr, eur], '( %s x. %s ) e. RR' % (AN, EU)), emur, emu0, q4], '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (LL, EMU, AN, EU, EMU))
    anc = D(w, A, 'recnd', [anr], '%s e. CC' % AN)
    can = chain(w, A, ['( ( %s x. %s ) x. %s )' % (AN, EU, EMU), '( %s x. ( %s x. %s ) )' % (AN, EU, EMU), '( %s x. 1 )' % AN, AN],
                [E(w, A, 'mulassd', [anc, D(w, A, 'recnd', [eur], '%s e. CC' % EU), D(w, A, 'recnd', [emur], '%s e. CC' % EMU)], '( ( %s x. %s ) x. %s )' % (AN, EU, EMU), '( %s x. ( %s x. %s ) )' % (AN, EU, EMU)),
                 E(w, A, 'oveq2d', [w.s([D(w, A, 'recnd', [ur], 'U e. CC'), w.inst('efcan')], 'syl', '( %s -> ( %s x. %s ) = 1 )' % (A, EU, EMU))], '( %s x. ( %s x. %s ) )' % (AN, EU, EMU), '( %s x. 1 )' % AN),
                 E(w, A, 'mulridd', [anc], '( %s x. 1 )' % AN, AN)])
    q6 = w.s([q5, can], 'breqtrd', '( %s -> ( %s x. %s ) <_ %s )' % (A, LL, EMU, AN))
    # T ^ 2 x. N = U ^ 2 / N
    U2 = '( U ^ 2 )'
    u2r = D(w, A, 'resqcld', [ur], '%s e. RR' % U2)
    tn = chain(w, A, ['( ( %s ^ 2 ) x. N )' % T, '( ( %s / ( N ^ 2 ) ) x. N )' % U2, '( %s / N )' % U2],
               [E(w, A, 'oveq1d', [E(w, A, 'sqdivd', [D(w, A, 'recnd', [ur], 'U e. CC'), nc, nz], '( %s ^ 2 )' % T, '( %s / ( N ^ 2 ) )' % U2)], '( ( %s ^ 2 ) x. N )' % T, '( ( %s / ( N ^ 2 ) ) x. N )' % U2),
                w.s([], 'idi', 'x') if False else E(w, A, 'idi' if False else 'eqtrd', [E(w, A, 'oveq1d', [E(w, A, 'oveq2d', [E(w, A, 'sqvald', [nc], '( N ^ 2 )', '( N x. N )')], '( %s / ( N ^ 2 ) )' % U2, '( %s / ( N x. N ) )' % U2)],
                                                                       '( ( %s / ( N ^ 2 ) ) x. N )' % U2, '( ( %s / ( N x. N ) ) x. N )' % U2),
                                                                     chain(w, A, ['( ( %s / ( N x. N ) ) x. N )' % U2, '( ( ( %s / N ) / N ) x. N )' % U2, '( %s / N )' % U2],
                                                                           [('r', E(w, A, 'oveq1d', [E(w, A, 'divdiv1d', [D(w, A, 'recnd', [u2r], '%s e. CC' % U2), nc, nc, nz, nz], '( ( %s / N ) / N )' % U2, '( %s / ( N x. N ) )' % U2)],
                                                                                    '( ( ( %s / N ) / N ) x. N )' % U2, '( ( %s / ( N x. N ) ) x. N )' % U2)),
                                                                            E(w, A, 'divcan1d', [D(w, A, 'divcld', [D(w, A, 'recnd', [u2r], '%s e. CC' % U2), nc, nz], '( %s / N ) e. CC' % U2), nc, nz],
                                                                              '( ( ( %s / N ) / N ) x. N )' % U2, '( %s / N )' % U2)])],
                                                                    '( ( %s / ( N ^ 2 ) ) x. N )' % U2, '( %s / N )' % U2)])
    Qn = '( %s / N )' % U2
    qnr = D(w, A, 'redivcld', [u2r, nr, nz], '%s e. RR' % Qn)
    cl2 = Closure(w, A, {AN: ('RR', anr), EMU: ('RR', emur), Qn: ('RR', qnr), '( ( %s ^ 2 ) x. N )' % T: ('RR', D(w, A, 'remulcld', [t2r, nr], '( ( %s ^ 2 ) x. N ) e. RR' % T))})
    cl2.atom('( ( %s ^ 2 ) x. N )' % T)
    tne = D(w, A, 'eqled', [cl2.mem('( ( %s ^ 2 ) x. N )' % T, 'RR'), tn], '( ( %s ^ 2 ) x. N ) <_ %s' % (T, Qn))
    tne2 = D(w, A, 'eqled', [qnr, w.s([tn], 'eqcomd', '( %s -> %s = ( ( %s ^ 2 ) x. N ) )' % (A, Qn, T))], '%s <_ ( ( %s ^ 2 ) x. N )' % (Qn, T))
    # q6: ( ( 1 + ( -u T2 x. N ) ) x. EMU ) <_ AN  ==> EMU - AN <_ Qn x. EMU
    nq = chain(w, A, ['( -u ( %s ^ 2 ) x. N )' % T, '-u ( ( %s ^ 2 ) x. N )' % T, '-u %s' % Qn],
               [E(w, A, 'mulneg1d', [D(w, A, 'sqcld', [tc], '( %s ^ 2 ) e. CC' % T), nc], '( -u ( %s ^ 2 ) x. N )' % T, '-u ( ( %s ^ 2 ) x. N )' % T),
                E(w, A, 'negeqd', [tn], '-u ( ( %s ^ 2 ) x. N )' % T, '-u %s' % Qn)])
    q6b = w.s([w.s([w.s([nq], 'oveq2d', '( %s -> %s = ( 1 + -u %s ) )' % (A, LL, Qn))], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( 1 + -u %s ) x. %s ) )' % (A, LL, EMU, Qn, EMU)), q6],
              'eqbrtrrd', '( %s -> ( ( 1 + -u %s ) x. %s ) <_ %s )' % (A, Qn, EMU, AN))
    cl3 = Closure(w, A, {AN: ('RR', anr), EMU: ('RR', emur), Qn: ('RR', qnr)})
    fin = nlinarith(w, A, [q6b], '( %s - %s ) <_ ( %s x. %s )' % (EMU, AN, Qn, EMU), closure=cl3)
    d23 = w.s([E(w, A, 'div23d', [D(w, A, 'recnd', [u2r], '%s e. CC' % U2), D(w, A, 'recnd', [emur], '%s e. CC' % EMU), nc, nz], '( ( %s x. %s ) / N )' % (U2, EMU), '( %s x. %s )' % (Qn, EMU))],
              'eqcomd', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) / N ) )' % (A, Qn, EMU, U2, EMU))
    fin2 = w.s([fin, d23], 'breqtrd', '( %s -> ( %s - %s ) <_ ( ( %s x. %s ) / N ) )' % (A, EMU, AN, U2, EMU))
    q = w.s([w.s([an0, p2], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ %s ) )' % (A, AN, AN, EMU)), fin2], 'jca', 'x')
    finish(w, q, 'zl3ebd')
    go(w)


# ---------------------------------------------------------------- zl3pwe
if want('zl3pwe'):
    w = W('zl3pwe', 'A power is dominated by a half exponential: ` X ^ C <_ ( 2 ( C + 1 ) ) ^ C e ^ ( X / 2 ) ` for ` C >_ 0 ` , ` X > 0 ` ( ~ bvefge1p , ~ cxple2a ).')
    A, Cc = ante_of('zl3pwe')
    cr = D(w, A, 'simpll', [], 'C e. RR'); c0 = D(w, A, 'simplr', [], '0 <_ C'); xrp = D(w, A, 'simpr', [], 'X e. RR+')
    xr = D(w, A, 'rpred', [xrp], 'X e. RR'); xc = D(w, A, 'rpcnd', [xrp], 'X e. CC')
    C1 = '( C + 1 )'; M = '( 2 x. %s )' % C1
    c1r = D(w, A, 'readdcld', [cr, a1(w, A, '1re', '1 e. RR')], '%s e. RR' % C1)
    cl0 = Closure(w, A, {'C': ('RR', cr)})
    c1p = linarith(w, A, [c0], '0 < %s' % C1, closure=cl0)
    c1rp = D(w, A, 'elrpd', [c1r, c1p], '%s e. RR+' % C1)
    mrp = D(w, A, 'rpmulcld', [a1(w, A, '2rp', '2 e. RR+'), c1rp], '%s e. RR+' % M)
    Y = '( X / %s )' % M
    yrp = D(w, A, 'rpdivcld', [xrp, mrp], '%s e. RR+' % Y)
    yr = D(w, A, 'rpred', [yrp], '%s e. RR' % Y)
    EY = '( exp ` %s )' % Y
    eyr = D(w, A, 'reefcld', [yr], '%s e. RR' % EY)
    bv = w.s([w.s([yr, D(w, A, 'rpge0d', [yrp], '0 <_ %s' % Y)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, Y, Y)), w.inst('bvefge1p')], 'syl', '( %s -> ( 1 + %s ) <_ %s )' % (A, Y, EY))
    ye = linarith(w, A, [bv], '%s <_ %s' % (Y, EY), closure=Closure(w, A, {Y: ('RR', yr), EY: ('RR', eyr)}))
    mr = D(w, A, 'rpred', [mrp], '%s e. RR' % M)
    xm = w.s([E(w, A, 'divcan2d', [xc, D(w, A, 'rpcnd', [mrp], '%s e. CC' % M), D(w, A, 'rpne0d', [mrp], '%s =/= 0' % M)], '( %s x. %s )' % (M, Y), 'X')], 'eqcomd', '( %s -> X = ( %s x. %s ) )' % (A, M, Y))
    MEY = '( %s x. %s )' % (M, EY)
    le1 = w.s([xm, D(w, A, 'lemul2ad', [yr, eyr, mr, D(w, A, 'rpge0d', [mrp], '0 <_ %s' % M), ye], '( %s x. %s ) <_ %s' % (M, Y, MEY))], 'eqbrtrd', '( %s -> X <_ %s )' % (A, MEY))
    meyr = D(w, A, 'remulcld', [mr, eyr], '%s e. RR' % MEY)
    cx = w.s([w.s([xr, meyr, cr], '3jca', '( %s -> ( X e. RR /\\ %s e. RR /\\ C e. RR ) )' % (A, MEY)), w.s([D(w, A, 'rpge0d', [xrp], '0 <_ X'), c0], 'jca', '( %s -> ( 0 <_ X /\\ 0 <_ C ) )' % A),
              le1, w.inst('cxple2a')], 'syl3anc', '( %s -> ( X ^c C ) <_ ( %s ^c C ) )' % (A, MEY))
    ey0 = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), eyr, w.s([yr, w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, EY))], '0 <_ %s' % EY)
    mc = w.s([w.s([mr, D(w, A, 'rpge0d', [mrp], '0 <_ %s' % M)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, M, M)), w.s([eyr, ey0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, EY, EY)),
              D(w, A, 'recnd', [cr], 'C e. CC'), w.inst('mulcxp')], 'syl3anc', '( %s -> ( %s ^c C ) = ( ( %s ^c C ) x. ( %s ^c C ) ) )' % (A, MEY, M, EY))
    eyc = D(w, A, 'recnd', [eyr], '%s e. CC' % EY)
    eyn = D(w, A, 'gt0ne0d', [w.s([yr, w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, EY))], '%s =/= 0' % EY)
    ec = chain(w, A, ['( %s ^c C )' % EY, '( exp ` ( C x. ( log ` %s ) ) )' % EY, '( exp ` ( C x. %s ) )' % Y],
               [w.s([eyc, eyn, D(w, A, 'recnd', [cr], 'C e. CC'), w.inst('cxpef')], 'syl3anc', '( %s -> ( %s ^c C ) = ( exp ` ( C x. ( log ` %s ) ) ) )' % (A, EY, EY)),
                E(w, A, 'fveq2d', [E(w, A, 'oveq2d', [w.s([yr, w.inst('relogef')], 'syl', '( %s -> ( log ` %s ) = %s )' % (A, EY, Y))], '( C x. ( log ` %s ) )' % EY, '( C x. %s )' % Y)],
                  '( exp ` ( C x. ( log ` %s ) ) )' % EY, '( exp ` ( C x. %s ) )' % Y)])
    # ( C + 1 ) x. Y = X / 2
    X2 = '( X / 2 )'
    cy = chain(w, A, ['( %s x. %s )' % (C1, Y), '( %s x. ( %s / %s ) )' % (C1, X2, C1), X2],
               [E(w, A, 'oveq2d', [w.s([E(w, A, 'divdiv1d', [xc, a1(w, A, '2cn', '2 e. CC'), D(w, A, 'rpcnd', [c1rp], '%s e. CC' % C1), a1(w, A, '2ne0', '2 =/= 0'),
                                                           D(w, A, 'rpne0d', [c1rp], '%s =/= 0' % C1)], '( %s / %s )' % (X2, C1), Y)], 'eqcomd', '( %s -> %s = ( %s / %s ) )' % (A, Y, X2, C1))],
                  '( %s x. %s )' % (C1, Y), '( %s x. ( %s / %s ) )' % (C1, X2, C1)),
                E(w, A, 'divcan2d', [D(w, A, 'halfcld' if False else 'divcld', [xc, a1(w, A, '2cn', '2 e. CC'), a1(w, A, '2ne0', '2 =/= 0')], '%s e. CC' % X2),
                                     D(w, A, 'rpcnd', [c1rp], '%s e. CC' % C1), D(w, A, 'rpne0d', [c1rp], '%s =/= 0' % C1)], '( %s x. ( %s / %s ) )' % (C1, X2, C1), X2)])
    x2r = D(w, A, 'rehalfcld', [xr], '%s e. RR' % X2)
    cl = Closure(w, A, {'C': ('RR', cr), Y: ('RR', yr), X2: ('RR', x2r), 'X': ('RR', xr)})
    cl.atom(Y); cl.atom(X2)
    cyl = nlinarith(w, A, [D(w, A, 'eqled', [D(w, A, 'remulcld', [c1r, yr], '( %s x. %s ) e. RR' % (C1, Y)), cy], '( %s x. %s ) <_ %s' % (C1, Y, X2)),
                            D(w, A, 'rpge0d', [yrp], '0 <_ %s' % Y)], '( C x. %s ) <_ %s' % (Y, X2), closure=cl)
    ee = efle_(w, A, '( C x. %s )' % Y, X2, D(w, A, 'remulcld', [cr, yr], '( C x. %s ) e. RR' % Y), x2r, cyl)
    mcr = D(w, A, 'recxpcld' if False else 'rpcxpcld', [mrp, cr], '( %s ^c C ) e. RR+' % M)
    le2 = D(w, A, 'lemul2ad', [D(w, A, 'reefcld', [D(w, A, 'remulcld', [cr, yr], '( C x. %s ) e. RR' % Y)], '( exp ` ( C x. %s ) ) e. RR' % Y), D(w, A, 'reefcld', [x2r], '( exp ` %s ) e. RR' % X2),
                                D(w, A, 'rpred', [mcr], '( %s ^c C ) e. RR' % M), D(w, A, 'rpge0d', [mcr], '0 <_ ( %s ^c C )' % M), ee],
            '( ( %s ^c C ) x. ( exp ` ( C x. %s ) ) ) <_ ( ( %s ^c C ) x. ( exp ` %s ) )' % (M, Y, M, X2))
    rr = w.s([mc, E(w, A, 'oveq2d', [ec], '( ( %s ^c C ) x. ( %s ^c C ) )' % (M, EY), '( ( %s ^c C ) x. ( exp ` ( C x. %s ) ) )' % (M, Y))], 'eqtrd',
             '( %s -> ( %s ^c C ) = ( ( %s ^c C ) x. ( exp ` ( C x. %s ) ) ) )' % (A, MEY, M, Y))
    q = w.s([w.s([cx, rr], 'breqtrd', '( %s -> ( X ^c C ) <_ ( ( %s ^c C ) x. ( exp ` ( C x. %s ) ) ) )' % (A, M, Y)), le2], 'letrd' if False else 'idi', 'x') if False else None
    xcr = D(w, A, 'rpcxpcld', [xrp, cr], '( X ^c C ) e. RR+')
    q = D(w, A, 'letrd', [D(w, A, 'rpred', [xcr], '( X ^c C ) e. RR'), D(w, A, 'remulcld', [D(w, A, 'rpred', [mcr], '( %s ^c C ) e. RR' % M), D(w, A, 'reefcld', [D(w, A, 'remulcld', [cr, yr], '( C x. %s ) e. RR' % Y)], '( exp ` ( C x. %s ) ) e. RR' % Y)],
                                                                                  '( ( %s ^c C ) x. ( exp ` ( C x. %s ) ) ) e. RR' % (M, Y)),
                          D(w, A, 'remulcld', [D(w, A, 'rpred', [mcr], '( %s ^c C ) e. RR' % M), D(w, A, 'reefcld', [x2r], '( exp ` %s ) e. RR' % X2)], '( ( %s ^c C ) x. ( exp ` %s ) ) e. RR' % (M, X2)),
                          w.s([cx, rr], 'breqtrd', '( %s -> ( X ^c C ) <_ ( ( %s ^c C ) x. ( exp ` ( C x. %s ) ) ) )' % (A, M, Y)), le2], 'x')
    finish(w, q, 'zl3pwe')
    go(w)


# ---------------------------------------------------------------- zl3iex
if want('zl3iex'):
    w = W('zl3iex', '` S. ( A , B ) e ^ ( - x / 2 ) dx = 2 ( e ^ ( - A / 2 ) - e ^ ( - B / 2 ) ) ` ( ~ ftc2 with the antiderivative ` -2 e ^ ( - x / 2 ) ` ).')
    A, Cc = ante_of('zl3iex')
    ar = D(w, A, 'simp1', [], 'A e. RR'); br = D(w, A, 'simp2', [], 'B e. RR'); ab = D(w, A, 'simp3', [], 'A <_ B')
    S = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A)
    Ax = '( %s /\\ x e. CC )' % A
    xc = D(w, Ax, 'simpr', [], 'x e. CC')
    c2 = a1(w, Ax, '2cn', '2 e. CC'); n2 = a1(w, Ax, '2ne0', '2 =/= 0')
    X2 = '( x / 2 )'; NX = '-u %s' % X2; EX = '( exp ` %s )' % NX
    did = w.s([S], 'dvmptid', '( %s -> ( CC _D ( x e. CC |-> x ) ) = ( x e. CC |-> 1 ) )' % A)
    dd = w.s([S, xc, a1(w, Ax, 'ax-1cn', '1 e. CC'), did, a1(w, A, '2cn', '2 e. CC'), a1(w, A, '2ne0', '2 =/= 0')], 'dvmptdivc',
             '( %s -> ( CC _D ( x e. CC |-> %s ) ) = ( x e. CC |-> ( 1 / 2 ) ) )' % (A, X2))
    dn = w.s([S, D(w, Ax, 'divcld', [xc, c2, n2], '%s e. CC' % X2), a1(w, Ax, 'halfcn', '( 1 / 2 ) e. CC'), dd], 'dvmptneg',
             '( %s -> ( CC _D ( x e. CC |-> %s ) ) = ( x e. CC |-> -u ( 1 / 2 ) ) )' % (A, NX))
    EM = '( y e. CC |-> ( exp ` y ) )'
    ed = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC'), w.inst('ffn')], 'ax-mp', 'exp Fn CC'), w.s([], 'dffn5', '( exp Fn CC <-> exp = %s )' % EM)], 'mpbi', 'exp = %s' % EM)
    dex = w.s([w.s([w.s([w.s([ed], 'oveq2i', '( CC _D exp ) = ( CC _D %s )' % EM), w.s([], 'dvef', '( CC _D exp ) = exp')], 'eqtr3i', '( CC _D %s ) = exp' % EM), ed], 'eqtri',
                    '( CC _D %s ) = %s' % (EM, EM))], 'a1i', '( %s -> ( CC _D %s ) = %s )' % (A, EM, EM))
    Ay = '( %s /\\ y e. CC )' % A
    yc = D(w, Ay, 'simpr', [], 'y e. CC')
    ey = D(w, Ay, 'efcld', [yc], '( exp ` y ) e. CC')
    nxc = D(w, Ax, 'negcld', [D(w, Ax, 'divcld', [xc, c2, n2], '%s e. CC' % X2)], '%s e. CC' % NX)
    dco = w.s([S, S, nxc, D(w, Ax, 'negcld', [a1(w, Ax, 'halfcn', '( 1 / 2 ) e. CC')], '-u ( 1 / 2 ) e. CC'), ey, ey, dn, dex,
               w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = %s )' % (NX, EX)), w.s([], 'fveq2', '( y = %s -> ( exp ` y ) = %s )' % (NX, EX))], 'dvmptco',
              '( %s -> ( CC _D ( x e. CC |-> %s ) ) = ( x e. CC |-> ( %s x. -u ( 1 / 2 ) ) ) )' % (A, EX, EX))
    exc = D(w, Ax, 'efcld', [nxc], '%s e. CC' % EX)
    m2 = D(w, A, 'negcld', [a1(w, A, '2cn', '2 e. CC')], '-u 2 e. CC')
    B1 = '( %s x. -u ( 1 / 2 ) )' % EX
    b1c = D(w, Ax, 'mulcld', [exc, D(w, Ax, 'negcld', [a1(w, Ax, 'halfcn', '( 1 / 2 ) e. CC')], '-u ( 1 / 2 ) e. CC')], '%s e. CC' % B1)
    dcm = w.s([S, exc, b1c, dco, m2], 'dvmptcmul', '( %s -> ( CC _D ( x e. CC |-> ( -u 2 x. %s ) ) ) = ( x e. CC |-> ( -u 2 x. %s ) ) )' % (A, EX, B1))
    GF = '( x e. CC |-> ( -u 2 x. %s ) )' % EX
    m2x = D(w, Ax, 'negcld', [c2], '-u 2 e. CC')
    ric = w.s([w.s([], 'eqid', '%s = %s' % (GF, GF)), D(w, Ax, 'mulcld', [m2x, exc], '( -u 2 x. %s ) e. CC' % EX), dcm, D(w, Ax, 'mulcld', [m2x, b1c], '( -u 2 x. %s ) e. CC' % B1), ar, br],
              'dvmptresicc', '( %s -> ( RR _D ( x e. ( A [,] B ) |-> ( -u 2 x. %s ) ) ) = ( x e. ( A (,) B ) |-> ( -u 2 x. %s ) ) )' % (A, EX, B1))
    Ao = '( %s /\\ x e. ( A (,) B ) )' % A
    xo = D(w, Ao, 'recnd', [w.s([w.s([w.s([], 'ioossre', '( A (,) B ) C_ RR')], 'a1i', '( %s -> ( A (,) B ) C_ RR )' % Ao), D(w, Ao, 'simpr', [], 'x e. ( A (,) B )')], 'sseldd',
                                '( %s -> x e. RR )' % Ao)], 'x e. CC')
    exo = D(w, Ao, 'efcld', [D(w, Ao, 'negcld', [D(w, Ao, 'divcld', [xo, a1(w, Ao, '2cn', '2 e. CC'), a1(w, Ao, '2ne0', '2 =/= 0')], '%s e. CC' % X2)], '%s e. CC' % NX)], '%s e. CC' % EX)
    hco = a1(w, Ao, 'halfcn', '( 1 / 2 ) e. CC')
    sim = chain(w, Ao, ['( -u 2 x. %s )' % B1, '( -u 2 x. -u ( %s x. ( 1 / 2 ) ) )' % EX, '( 2 x. ( %s x. ( 1 / 2 ) ) )' % EX, '( 2 x. ( %s / 2 ) )' % EX, EX],
                [E(w, Ao, 'oveq2d', [E(w, Ao, 'mulneg2d', [exo, hco], B1, '-u ( %s x. ( 1 / 2 ) )' % EX)], '( -u 2 x. %s )' % B1, '( -u 2 x. -u ( %s x. ( 1 / 2 ) ) )' % EX),
                 E(w, Ao, 'mul2negd', [a1(w, Ao, '2cn', '2 e. CC'), D(w, Ao, 'mulcld', [exo, hco], '( %s x. ( 1 / 2 ) ) e. CC' % EX)], '( -u 2 x. -u ( %s x. ( 1 / 2 ) ) )' % EX, '( 2 x. ( %s x. ( 1 / 2 ) ) )' % EX),
                 E(w, Ao, 'oveq2d', [w.s([E(w, Ao, 'divrecd', [exo, a1(w, Ao, '2cn', '2 e. CC'), a1(w, Ao, '2ne0', '2 =/= 0')], '( %s / 2 )' % EX, '( %s x. ( 1 / 2 ) )' % EX)], 'eqcomd',
                                         '( %s -> ( %s x. ( 1 / 2 ) ) = ( %s / 2 ) )' % (Ao, EX, EX))], '( 2 x. ( %s x. ( 1 / 2 ) ) )' % EX, '( 2 x. ( %s / 2 ) )' % EX),
                 E(w, Ao, 'divcan2d', [exo, a1(w, Ao, '2cn', '2 e. CC'), a1(w, Ao, '2ne0', '2 =/= 0')], '( 2 x. ( %s / 2 ) )' % EX, EX)])
    G = '( x e. ( A [,] B ) |-> ( -u 2 x. %s ) )' % EX
    dv = w.s([ric, w.s([sim], 'mpteq2dva', '( %s -> ( x e. ( A (,) B ) |-> ( -u 2 x. %s ) ) = ( x e. ( A (,) B ) |-> %s ) )' % (A, B1, EX))], 'eqtrd',
             '( %s -> ( RR _D %s ) = ( x e. ( A (,) B ) |-> %s ) )' % (A, G, EX))
    cl = Closure(w, A, {'A': ('RR', ar), 'B': ('RR', br)})
    iccc = w.s([w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> ( A [,] B ) C_ RR )' % A), a1(w, A, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> ( A [,] B ) C_ CC )' % A)
    iooc = w.s([w.s([w.s([], 'ioossre', '( A (,) B ) C_ RR')], 'a1i', '( %s -> ( A (,) B ) C_ RR )' % A), a1(w, A, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> ( A (,) B ) C_ CC )' % A)
    cg = cont(w, A, '( A [,] B )', '( -u 2 x. %s )' % EX, cl, iccc)
    ce = cont(w, A, '( A [,] B )', EX, cl, iccc)
    # open-interval facts for exp
    MC = '( x e. ( A [,] B ) |-> %s )' % EX; MO = '( x e. ( A (,) B ) |-> %s )' % EX
    ss = w.s([w.s([], 'ioossicc', '( A (,) B ) C_ ( A [,] B )')], 'a1i', '( %s -> ( A (,) B ) C_ ( A [,] B ) )' % A)
    rm = w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` ( A (,) B ) ) = %s )' % (A, MC, MO))
    co = w.s([rm, w.s([ss, ce, w.inst('rescncf')], 'sylc', '( %s -> ( %s |` ( A (,) B ) ) e. ( ( A (,) B ) -cn-> CC ) )' % (A, MC))], 'eqeltrrd', '( %s -> %s e. ( ( A (,) B ) -cn-> CC ) )' % (A, MO))
    ib = w.s([rm, w.s([w.s([w.s([ar, br], 'jca', '( %s -> ( A e. RR /\\ B e. RR ) )' % A), ce], 'jca', '( %s -> ( ( A e. RR /\\ B e. RR ) /\\ %s e. ( ( A [,] B ) -cn-> CC ) ) )' % (A, MC)),
                       w.inst('zl3ibl')], 'syl', '( %s -> ( %s |` ( A (,) B ) ) e. L^1 )' % (A, MC))], 'eqeltrrd', '( %s -> %s e. L^1 )' % (A, MO))
    f2 = w.s([ar, br, ab, w.s([dv, co], 'eqeltrd', '( %s -> ( RR _D %s ) e. ( ( A (,) B ) -cn-> CC ) )' % (A, G)),
              w.s([dv, ib], 'eqeltrd', '( %s -> ( RR _D %s ) e. L^1 )' % (A, G)), cg], 'ftc2', '( %s -> S. ( A (,) B ) ( ( RR _D %s ) ` t ) _d t = ( ( %s ` B ) - ( %s ` A ) ) )' % (A, G, G, G))
    At = '( %s /\\ t e. ( A (,) B ) )' % A
    EXt = '( exp ` -u ( t / 2 ) )'
    e1 = w.s([w.s([w.s([dv], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (At, G, MO))], 'fveq1d', '( %s -> ( ( RR _D %s ) ` t ) = ( %s ` t ) )' % (At, G, MO)),
              mptv(w, At, 'x', '( A (,) B )', EX, 't', D(w, At, 'simpr', [], 't e. ( A (,) B )'))[0]], 'eqtrd', '( %s -> ( ( RR _D %s ) ` t ) = %s )' % (At, G, EXt))
    i1 = w.s([e1], 'itgeq2dv', '( %s -> S. ( A (,) B ) ( ( RR _D %s ) ` t ) _d t = S. ( A (,) B ) %s _d t )' % (A, G, EXt))
    cb = w.s([w.s([w.s([w.s([], 'oveq1', '( x = t -> ( x / 2 ) = ( t / 2 ) )')], 'negeqd', '( x = t -> -u ( x / 2 ) = -u ( t / 2 ) )')], 'fveq2d', '( x = t -> %s = %s )' % (EX, EXt))],
             'cbvitgv', 'S. ( A (,) B ) %s _d x = S. ( A (,) B ) %s _d t' % (EX, EXt))
    rx = lambda v: w.s([v], 'rexrd', 'x')
    ax_ = D(w, A, 'rexrd', [ar], 'A e. RR*'); bx_ = D(w, A, 'rexrd', [br], 'B e. RR*')
    bin_ = w.s([ax_, bx_, ab, w.inst('ubicc2')], 'syl3anc', '( %s -> B e. ( A [,] B ) )' % A)
    ain_ = w.s([ax_, bx_, ab, w.inst('lbicc2')], 'syl3anc', '( %s -> A e. ( A [,] B ) )' % A)
    gB, _ = mptv(w, A, 'x', '( A [,] B )', '( -u 2 x. %s )' % EX, 'B', bin_)
    gA, _ = mptv(w, A, 'x', '( A [,] B )', '( -u 2 x. %s )' % EX, 'A', ain_)
    EA = '( exp ` -u ( A / 2 ) )'; EB = '( exp ` -u ( B / 2 ) )'
    eac = D(w, A, 'efcld', [D(w, A, 'negcld', [D(w, A, 'divcld', [D(w, A, 'recnd', [ar], 'A e. CC'), a1(w, A, '2cn', '2 e. CC'), a1(w, A, '2ne0', '2 =/= 0')], '( A / 2 ) e. CC')], '-u ( A / 2 ) e. CC')], '%s e. CC' % EA)
    ebc = D(w, A, 'efcld', [D(w, A, 'negcld', [D(w, A, 'divcld', [D(w, A, 'recnd', [br], 'B e. CC'), a1(w, A, '2cn', '2 e. CC'), a1(w, A, '2ne0', '2 =/= 0')], '( B / 2 ) e. CC')], '-u ( B / 2 ) e. CC')], '%s e. CC' % EB)
    c2A = a1(w, A, '2cn', '2 e. CC')
    r = chain(w, A, ['( ( %s ` B ) - ( %s ` A ) )' % (G, G), '( ( -u 2 x. %s ) - ( -u 2 x. %s ) )' % (EB, EA), '( -u 2 x. ( %s - %s ) )' % (EB, EA),
                     '( 2 x. -u ( %s - %s ) )' % (EB, EA), '( 2 x. ( %s - %s ) )' % (EA, EB)],
              [E(w, A, 'oveq12d', [gB, gA], '( ( %s ` B ) - ( %s ` A ) )' % (G, G), '( ( -u 2 x. %s ) - ( -u 2 x. %s ) )' % (EB, EA)),
               ('r', E(w, A, 'subdid', [m2, ebc, eac], '( -u 2 x. ( %s - %s ) )' % (EB, EA), '( ( -u 2 x. %s ) - ( -u 2 x. %s ) )' % (EB, EA))),
               w.s([c2A, D(w, A, 'subcld', [ebc, eac], '( %s - %s ) e. CC' % (EB, EA)), w.inst('mulneg12')], 'syl2anc', '( %s -> ( -u 2 x. ( %s - %s ) ) = ( 2 x. -u ( %s - %s ) ) )' % (A, EB, EA, EB, EA)),
               E(w, A, 'oveq2d', [E(w, A, 'negsubdi2d', [ebc, eac], '-u ( %s - %s )' % (EB, EA), '( %s - %s )' % (EA, EB))], '( 2 x. -u ( %s - %s ) )' % (EB, EA), '( 2 x. ( %s - %s ) )' % (EA, EB))])
    q = chain(w, A, ['S. ( A (,) B ) %s _d x' % EX, 'S. ( A (,) B ) %s _d t' % EXt, 'S. ( A (,) B ) ( ( RR _D %s ) ` t ) _d t' % G, '( ( %s ` B ) - ( %s ` A ) )' % (G, G),
                     '( 2 x. ( %s - %s ) )' % (EA, EB)],
              [w.s([cb], 'a1i', '( %s -> S. ( A (,) B ) %s _d x = S. ( A (,) B ) %s _d t )' % (A, EX, EXt)), ('r', i1), f2, r])
    finish(w, q, 'zl3iex')
    go(w)


def absx(w, C, X, xrp, wc):
    """( C -> ( abs ` ( X ^c ( W - 1 ) ) ) = ( X ^c ( ( Re ` W ) - 1 ) ) )"""
    wm = D(w, C, 'subcld', [wc, a1(w, C, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    e1 = w.s([xrp, wm, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` ( %s ^c ( W - 1 ) ) ) = ( %s ^c ( Re ` ( W - 1 ) ) ) )' % (C, X, X))
    return w.s([e1, E(w, C, 'oveq2d', [re_sub1(w, C, wc)], '( %s ^c ( Re ` ( W - 1 ) ) )' % X, '( %s ^c ( ( Re ` W ) - 1 ) )' % X)], 'eqtrd',
               '( %s -> ( abs ` ( %s ^c ( W - 1 ) ) ) = ( %s ^c ( ( Re ` W ) - 1 ) ) )' % (C, X, X))


def halfexp(w, C, X, xr):
    """( C -> ( ( exp ` ( X / 2 ) ) x. ( exp ` -u X ) ) = ( exp ` -u ( X / 2 ) ) )"""
    X2 = '( %s / 2 )' % X
    x2r = D(w, C, 'rehalfcld', [xr], '%s e. RR' % X2)
    e1 = efadd_(w, C, X2, '-u %s' % X, D(w, C, 'recnd', [x2r], '%s e. CC' % X2), D(w, C, 'recnd', [D(w, C, 'renegcld', [xr], '-u %s e. RR' % X)], '-u %s e. CC' % X))
    ar = lineq(w, C, '( %s + -u %s )' % (X2, X), '-u %s' % X2, closure=Closure(w, C, {X: ('RR', xr)}))
    return w.s([e1, E(w, C, 'fveq2d', [ar], '( exp ` ( %s + -u %s ) )' % (X2, X), '( exp ` -u %s )' % X2)], 'eqtr3d',
               '( %s -> ( ( exp ` %s ) x. ( exp ` -u %s ) ) = ( exp ` -u %s ) )' % (C, X2, X, X2))


# ---------------------------------------------------------------- zl3tlp
if want('zl3tlp'):
    w = W('zl3tlp', 'Pointwise bound of the Euler integrand: ` | e ^ -x x ^ ( W - 1 ) | <_ K e ^ ( - x / 2 ) ` ( ~ zl3pwe ).')
    A, Cc = ante_of('zl3tlp')
    wc = D(w, A, 'simpll', [], 'W e. CC'); re1 = D(w, A, 'simplr', [], '1 < ( Re ` W )'); xrp = D(w, A, 'simpr', [], 'X e. RR+')
    xr = D(w, A, 'rpred', [xrp], 'X e. RR'); rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    S1 = '( ( Re ` W ) - 1 )'
    s1r = D(w, A, 'resubcld', [rw, a1(w, A, '1re', '1 e. RR')], '%s e. RR' % S1)
    s10 = linarith(w, A, [re1], '0 <_ %s' % S1, closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    EX = '( exp ` -u X )'; E2 = '( exp ` ( X / 2 ) )'; XS = '( X ^c %s )' % S1
    exr = D(w, A, 'reefcld', [D(w, A, 'renegcld', [xr], '-u X e. RR')], '%s e. RR' % EX)
    ex0 = w.s([D(w, A, 'renegcld', [xr], '-u X e. RR'), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, EX))
    xsr = D(w, A, 'rpcxpcld', [xrp, s1r], '%s e. RR+' % XS)
    ab = chain(w, A, ['( abs ` ( %s x. ( X ^c ( W - 1 ) ) ) )' % EX, '( ( abs ` %s ) x. ( abs ` ( X ^c ( W - 1 ) ) ) )' % EX, '( %s x. %s )' % (EX, XS)],
               [E(w, A, 'absmuld', [D(w, A, 'recnd', [exr], '%s e. CC' % EX), D(w, A, 'cxpcld', [D(w, A, 'rpcnd', [xrp], 'X e. CC'), D(w, A, 'subcld', [wc, a1(w, A, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')],
                                                                              '( X ^c ( W - 1 ) ) e. CC')], '( abs ` ( %s x. ( X ^c ( W - 1 ) ) ) )' % EX,
                  '( ( abs ` %s ) x. ( abs ` ( X ^c ( W - 1 ) ) ) )' % EX),
                E(w, A, 'oveq12d', [E(w, A, 'absidd', [exr, D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), exr, ex0], '0 <_ %s' % EX)], '( abs ` %s )' % EX, EX), absx(w, A, 'X', xrp, wc)],
                  '( ( abs ` %s ) x. ( abs ` ( X ^c ( W - 1 ) ) ) )' % EX, '( %s x. %s )' % (EX, XS))])
    KBs = L.KB
    pw = w.s([w.s([w.s([s1r, s10], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, S1, S1)), xrp], 'jca', '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ X e. RR+ ) )' % (A, S1, S1)),
              w.inst('zl3pwe')], 'syl', '( %s -> %s <_ ( %s x. %s ) )' % (A, XS, KBs, E2))
    kbr = D(w, A, 'rpcxpcld', [D(w, A, 'rpmulcld', [a1(w, A, '2rp', '2 e. RR+'), D(w, A, 'elrpd', [D(w, A, 'readdcld', [s1r, a1(w, A, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % S1),
                                                                                                   linarith(w, A, [s10], '0 < ( %s + 1 )' % S1, closure=Closure(w, A, {S1: ('RR', s1r)}))],
                                                                                        '( %s + 1 ) e. RR+' % S1)], '( 2 x. ( %s + 1 ) ) e. RR+' % S1), s1r], '%s e. RR+' % KBs)
    e2r = D(w, A, 'reefcld', [D(w, A, 'rehalfcld', [xr], '( X / 2 ) e. RR')], '%s e. RR' % E2)
    m = D(w, A, 'lemul2ad', [D(w, A, 'rpred', [xsr], '%s e. RR' % XS), D(w, A, 'remulcld', [D(w, A, 'rpred', [kbr], '%s e. RR' % KBs), e2r], '( %s x. %s ) e. RR' % (KBs, E2)), exr,
                             D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), exr, ex0], '0 <_ %s' % EX), pw], '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (EX, XS, EX, KBs, E2))
    kbc = D(w, A, 'rpcnd', [kbr], '%s e. CC' % KBs); e2c = D(w, A, 'recnd', [e2r], '%s e. CC' % E2); exc = D(w, A, 'recnd', [exr], '%s e. CC' % EX)
    rr = chain(w, A, ['( %s x. ( %s x. %s ) )' % (EX, KBs, E2), '( %s x. ( %s x. %s ) )' % (KBs, EX, E2), '( %s x. ( %s x. %s ) )' % (KBs, E2, EX), '( %s x. ( exp ` -u ( X / 2 ) ) )' % KBs],
               [E(w, A, 'mul12d', [exc, kbc, e2c], '( %s x. ( %s x. %s ) )' % (EX, KBs, E2), '( %s x. ( %s x. %s ) )' % (KBs, EX, E2)),
                E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [exc, e2c], '( %s x. %s )' % (EX, E2), '( %s x. %s )' % (E2, EX))], '( %s x. ( %s x. %s ) )' % (KBs, EX, E2), '( %s x. ( %s x. %s ) )' % (KBs, E2, EX)),
                E(w, A, 'oveq2d', [halfexp(w, A, 'X', xr)], '( %s x. ( %s x. %s ) )' % (KBs, E2, EX), '( %s x. ( exp ` -u ( X / 2 ) ) )' % KBs)])
    q = w.s([w.s([ab, m], 'eqbrtrd', '( %s -> ( abs ` ( %s x. ( X ^c ( W - 1 ) ) ) ) <_ ( %s x. ( %s x. %s ) ) )' % (A, EX, EX, KBs, E2)), rr], 'breqtrd', 'x')
    finish(w, q, 'zl3tlp')
    go(w)


# ---------------------------------------------------------------- zl3erp
if want('zl3erp'):
    w = W('zl3erp', 'Pointwise bound of the error integrand: ` | ( e ^ -x - ( 1 - x / N ) ^ N ) x ^ ( W - 1 ) | <_ ( K / N ) e ^ ( - x / 2 ) ` ( ~ zl3ebd , ~ zl3pwe ).')
    A, Cc = ante_of('zl3erp')
    wc = D(w, A, 'simpll', [], 'W e. CC'); re1 = D(w, A, 'simplr', [], '1 < ( Re ` W )')
    nn = D(w, A, 'simprl', [], 'N e. NN'); xin = D(w, A, 'simprr', [], 'X e. ( 0 (,) N )')
    nr = D(w, A, 'nnred', [nn], 'N e. RR'); nrp = D(w, A, 'nnrpd', [nn], 'N e. RR+')
    od = w.s([xin, w.inst('eliooord')], 'syl', '( %s -> ( 0 < X /\\ X < N ) )' % A)
    xr = w.s([xin, w.inst('elioore')], 'syl', '( %s -> X e. RR )' % A)
    x0 = D(w, A, 'simpld', [od], '0 < X'); xN = D(w, A, 'simprd', [od], 'X < N')
    xrp = D(w, A, 'elrpd', [xr, x0], 'X e. RR+')
    xle = D(w, A, 'ltled', [xr, nr, xN], 'X <_ N')
    P = '( ( 1 - ( X / N ) ) ^ N )'; EX = '( exp ` -u X )'
    eb = w.s([w.s([nn, w.s([xr, D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), xr, x0], '0 <_ X'), xle], '3jca', '( %s -> ( X e. RR /\\ 0 <_ X /\\ X <_ N ) )' % A)], 'jca',
                  '( %s -> ( N e. NN /\\ ( X e. RR /\\ 0 <_ X /\\ X <_ N ) ) )' % A), w.inst('zl3ebd')], 'syl',
             '( %s -> ( ( 0 <_ %s /\\ %s <_ %s ) /\\ ( %s - %s ) <_ ( ( ( X ^ 2 ) x. %s ) / N ) ) )' % (A, P, P, EX, EX, P, EX))
    pe = D(w, A, 'simprd', [D(w, A, 'simpld', [eb], '( 0 <_ %s /\\ %s <_ %s )' % (P, P, EX))], '%s <_ %s' % (P, EX))
    eb2 = D(w, A, 'simprd', [eb], '( %s - %s ) <_ ( ( ( X ^ 2 ) x. %s ) / N )' % (EX, P, EX))
    exr = D(w, A, 'reefcld', [D(w, A, 'renegcld', [xr], '-u X e. RR')], '%s e. RR' % EX)
    pr = D(w, A, 'reexpcld', [D(w, A, 'resubcld', [a1(w, A, '1re', '1 e. RR'), D(w, A, 'redivcld', [xr, nr, D(w, A, 'nnne0d', [nn], 'N =/= 0')], '( X / N ) e. RR')], '( 1 - ( X / N ) ) e. RR'),
                                D(w, A, 'nnnn0d', [nn], 'N e. NN0')], '%s e. RR' % P)
    DF = '( %s - %s )' % (EX, P)
    dfr = D(w, A, 'resubcld', [exr, pr], '%s e. RR' % DF)
    df0 = linarith(w, A, [pe], '0 <_ %s' % DF, closure=Closure(w, A, {EX: ('RR', exr), P: ('RR', pr)}))
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    S1 = '( ( Re ` W ) - 1 )'; XS = '( X ^c %s )' % S1
    s1r = D(w, A, 'resubcld', [rw, a1(w, A, '1re', '1 e. RR')], '%s e. RR' % S1)
    xsr = D(w, A, 'rpcxpcld', [xrp, s1r], '%s e. RR+' % XS)
    ab = chain(w, A, ['( abs ` ( %s x. ( X ^c ( W - 1 ) ) ) )' % DF, '( ( abs ` %s ) x. ( abs ` ( X ^c ( W - 1 ) ) ) )' % DF, '( %s x. %s )' % (DF, XS)],
               [E(w, A, 'absmuld', [D(w, A, 'recnd', [dfr], '%s e. CC' % DF), D(w, A, 'cxpcld', [D(w, A, 'rpcnd', [xrp], 'X e. CC'), D(w, A, 'subcld', [wc, a1(w, A, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')],
                                                                              '( X ^c ( W - 1 ) ) e. CC')], '( abs ` ( %s x. ( X ^c ( W - 1 ) ) ) )' % DF,
                  '( ( abs ` %s ) x. ( abs ` ( X ^c ( W - 1 ) ) ) )' % DF),
                E(w, A, 'oveq12d', [E(w, A, 'absidd', [dfr, df0], '( abs ` %s )' % DF, DF), absx(w, A, 'X', xrp, wc)], '( ( abs ` %s ) x. ( abs ` ( X ^c ( W - 1 ) ) ) )' % DF, '( %s x. %s )' % (DF, XS))])
    X2E = '( ( ( X ^ 2 ) x. %s ) / N )' % EX
    x2er = D(w, A, 'redivcld', [D(w, A, 'remulcld', [D(w, A, 'resqcld', [xr], '( X ^ 2 ) e. RR'), exr], '( ( X ^ 2 ) x. %s ) e. RR' % EX), nr, D(w, A, 'nnne0d', [nn], 'N =/= 0')], '%s e. RR' % X2E)
    m1 = D(w, A, 'lemul1ad', [dfr, x2er, D(w, A, 'rpred', [xsr], '%s e. RR' % XS), D(w, A, 'rpge0d', [xsr], '0 <_ %s' % XS), eb2], '( %s x. %s ) <_ ( %s x. %s )' % (DF, XS, X2E, XS))
    # rewrite ( X2E x. XS ) = ( ( X ^c S2 ) x. EX ) / N with S2 = ( ( Re ` W ) + 1 )
    S2 = '( ( Re ` W ) + 1 )'; XP = '( X ^c %s )' % S2
    xc = D(w, A, 'rpcnd', [xrp], 'X e. CC'); nc = D(w, A, 'rpcnd', [nrp], 'N e. CC'); nz = D(w, A, 'rpne0d', [nrp], 'N =/= 0')
    exc = D(w, A, 'recnd', [exr], '%s e. CC' % EX); x2c = D(w, A, 'sqcld', [xc], '( X ^ 2 ) e. CC'); xsc = D(w, A, 'rpcnd', [xsr], '%s e. CC' % XS)
    xn0 = D(w, A, 'rpne0d', [xrp], 'X =/= 0')
    pw2 = chain(w, A, ['( ( X ^ 2 ) x. %s )' % XS, '( ( X ^c 2 ) x. %s )' % XS, '( X ^c ( 2 + %s ) )' % S1, XP],
                [E(w, A, 'oveq1d', [w.s([w.s([xc, a1(w, A, '2nn0', '2 e. NN0'), w.inst('cxpexp')], 'syl2anc', '( %s -> ( X ^c 2 ) = ( X ^ 2 ) )' % A)], 'eqcomd', '( %s -> ( X ^ 2 ) = ( X ^c 2 ) )' % A)],
                   '( ( X ^ 2 ) x. %s )' % XS, '( ( X ^c 2 ) x. %s )' % XS),
                 ('r', E(w, A, 'cxpaddd', [xc, xn0, a1(w, A, '2cn', '2 e. CC'), D(w, A, 'recnd', [s1r], '%s e. CC' % S1)], '( X ^c ( 2 + %s ) )' % S1, '( ( X ^c 2 ) x. %s )' % XS)),
                 E(w, A, 'oveq2d', [lineq(w, A, '( 2 + %s )' % S1, S2, closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))], '( X ^c ( 2 + %s ) )' % S1, XP)])
    rw1 = chain(w, A, ['( %s x. %s )' % (X2E, XS), '( ( ( ( X ^ 2 ) x. %s ) x. %s ) / N )' % (EX, XS), '( ( ( ( X ^ 2 ) x. %s ) x. %s ) / N )' % (XS, EX), '( ( %s x. %s ) / N )' % (XP, EX)],
                [('r', E(w, A, 'div23d', [D(w, A, 'mulcld', [x2c, exc], '( ( X ^ 2 ) x. %s ) e. CC' % EX), xsc, nc, nz], '( ( ( ( X ^ 2 ) x. %s ) x. %s ) / N )' % (EX, XS), '( %s x. %s )' % (X2E, XS))),
                 E(w, A, 'oveq1d', [E(w, A, 'mul32d', [x2c, exc, xsc], '( ( ( X ^ 2 ) x. %s ) x. %s )' % (EX, XS), '( ( ( X ^ 2 ) x. %s ) x. %s )' % (XS, EX))],
                   '( ( ( ( X ^ 2 ) x. %s ) x. %s ) / N )' % (EX, XS), '( ( ( ( X ^ 2 ) x. %s ) x. %s ) / N )' % (XS, EX)),
                 E(w, A, 'oveq1d', [E(w, A, 'oveq1d', [pw2], '( ( ( X ^ 2 ) x. %s ) x. %s )' % (XS, EX), '( %s x. %s )' % (XP, EX))],
                   '( ( ( ( X ^ 2 ) x. %s ) x. %s ) / N )' % (XS, EX), '( ( %s x. %s ) / N )' % (XP, EX))])
    s2r = D(w, A, 'readdcld', [rw, a1(w, A, '1re', '1 e. RR')], '%s e. RR' % S2)
    s20 = linarith(w, A, [re1], '0 <_ %s' % S2, closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    KAs = L.KA; E2 = '( exp ` ( X / 2 ) )'
    pw = w.s([w.s([w.s([s2r, s20], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A, S2, S2)), xrp], 'jca', '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ X e. RR+ ) )' % (A, S2, S2)),
              w.inst('zl3pwe')], 'syl', '( %s -> %s <_ ( %s x. %s ) )' % (A, XP, KAs, E2))
    kar = D(w, A, 'rpcxpcld', [D(w, A, 'rpmulcld', [a1(w, A, '2rp', '2 e. RR+'), D(w, A, 'elrpd', [D(w, A, 'readdcld', [s2r, a1(w, A, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % S2),
                                                                                                   linarith(w, A, [s20], '0 < ( %s + 1 )' % S2, closure=Closure(w, A, {S2: ('RR', s2r)}))],
                                                                                        '( %s + 1 ) e. RR+' % S2)], '( 2 x. ( %s + 1 ) ) e. RR+' % S2), s2r], '%s e. RR+' % KAs)
    e2r = D(w, A, 'reefcld', [D(w, A, 'rehalfcld', [xr], '( X / 2 ) e. RR')], '%s e. RR' % E2)
    ex0 = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), exr, w.s([D(w, A, 'renegcld', [xr], '-u X e. RR'), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, EX))], '0 <_ %s' % EX)
    m2 = D(w, A, 'lemul1ad', [D(w, A, 'rpred', [D(w, A, 'rpcxpcld', [xrp, s2r], '%s e. RR+' % XP)], '%s e. RR' % XP), D(w, A, 'remulcld', [D(w, A, 'rpred', [kar], '%s e. RR' % KAs), e2r], '( %s x. %s ) e. RR' % (KAs, E2)),
                              exr, ex0, pw], '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (XP, EX, KAs, E2, EX))
    kac = D(w, A, 'rpcnd', [kar], '%s e. CC' % KAs); e2c = D(w, A, 'recnd', [e2r], '%s e. CC' % E2)
    EH = '( exp ` -u ( X / 2 ) )'
    rr = chain(w, A, ['( ( %s x. %s ) x. %s )' % (KAs, E2, EX), '( %s x. ( %s x. %s ) )' % (KAs, E2, EX), '( %s x. %s )' % (KAs, EH)],
               [E(w, A, 'mulassd', [kac, e2c, exc], '( ( %s x. %s ) x. %s )' % (KAs, E2, EX), '( %s x. ( %s x. %s ) )' % (KAs, E2, EX)),
                E(w, A, 'oveq2d', [halfexp(w, A, 'X', xr)], '( %s x. ( %s x. %s ) )' % (KAs, E2, EX), '( %s x. %s )' % (KAs, EH))])
    m3 = w.s([m2, rr], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A, XP, EX, KAs, EH))
    ehr = D(w, A, 'reefcld', [D(w, A, 'renegcld', [D(w, A, 'rehalfcld', [xr], '( X / 2 ) e. RR')], '-u ( X / 2 ) e. RR')], '%s e. RR' % EH)
    m4 = D(w, A, 'lediv1dd', [D(w, A, 'remulcld', [D(w, A, 'rpred', [D(w, A, 'rpcxpcld', [xrp, s2r], '%s e. RR+' % XP)], '%s e. RR' % XP), exr], '( %s x. %s ) e. RR' % (XP, EX)),
                              D(w, A, 'remulcld', [D(w, A, 'rpred', [kar], '%s e. RR' % KAs), ehr], '( %s x. %s ) e. RR' % (KAs, EH)), nrp, m3],
           '( ( %s x. %s ) / N ) <_ ( ( %s x. %s ) / N )' % (XP, EX, KAs, EH))
    m5 = w.s([m4, E(w, A, 'div23d', [kac, D(w, A, 'recnd', [ehr], '%s e. CC' % EH), nc, nz], '( ( %s x. %s ) / N )' % (KAs, EH), '( ( %s / N ) x. %s )' % (KAs, EH))], 'breqtrd',
             '( %s -> ( ( %s x. %s ) / N ) <_ ( ( %s / N ) x. %s ) )' % (A, XP, EX, KAs, EH))
    tot = w.s([w.s([m1, rw1], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( ( %s x. %s ) / N ) )' % (A, DF, XS, XP, EX)), m5], 'idi' if False else 'letrd' if False else 'idi', 'x') if False else None
    lhsr = D(w, A, 'remulcld', [dfr, D(w, A, 'rpred', [xsr], '%s e. RR' % XS)], '( %s x. %s ) e. RR' % (DF, XS))
    midr = D(w, A, 'redivcld', [D(w, A, 'remulcld', [D(w, A, 'rpred', [D(w, A, 'rpcxpcld', [xrp, s2r], '%s e. RR+' % XP)], '%s e. RR' % XP), exr], '( %s x. %s ) e. RR' % (XP, EX)), nr, nz], '( ( %s x. %s ) / N ) e. RR' % (XP, EX))
    rhr = D(w, A, 'remulcld', [D(w, A, 'redivcld', [D(w, A, 'rpred', [kar], '%s e. RR' % KAs), nr, nz], '( %s / N ) e. RR' % KAs), ehr], '( ( %s / N ) x. %s ) e. RR' % (KAs, EH))
    tot = D(w, A, 'letrd', [lhsr, midr, rhr, w.s([m1, rw1], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( ( %s x. %s ) / N ) )' % (A, DF, XS, XP, EX)), m5], '( %s x. %s ) <_ ( ( %s / N ) x. %s )' % (DF, XS, KAs, EH))
    q = w.s([ab, tot], 'eqbrtrd', 'x')
    finish(w, q, 'zl3erp')
    go(w)


def ibnd(w, C, a, b, ar, br, ab, h, ch, hbound, c, cr, c0):
    """( C -> ( abs ` S. ( a (,) b ) h _d x ) <_ ( c x. ( 2 x. ( ( exp ` -u ( a / 2 ) ) - ( exp ` -u ( b / 2 ) ) ) ) ) )
    ch: ( C -> ( x e. ( a [,] b ) |-> h ) e. ( ( a [,] b ) -cn-> CC ) ); hbound(Cx, xin) -> step ( Cx -> ( abs ` h ) <_ ( c x. ( exp ` -u ( x / 2 ) ) ) )"""
    IO = '( %s (,) %s )' % (a, b); IC = '( %s [,] %s )' % (a, b)
    EH = '( exp ` -u ( x / 2 ) )'
    MC = '( x e. %s |-> %s )' % (IC, h); MO = '( x e. %s |-> %s )' % (IO, h)
    ss = w.s([w.s([], 'ioossicc', '%s C_ %s' % (IO, IC))], 'a1i', '( %s -> %s C_ %s )' % (C, IO, IC))
    rm = w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (C, MC, IO, MO))
    ih = w.s([rm, w.s([w.s([w.s([ar, br], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (C, a, b)), ch], 'jca',
                           '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ %s e. ( %s -cn-> CC ) ) )' % (C, a, b, MC, IC)), w.inst('zl3ibl')], 'syl',
                      '( %s -> ( %s |` %s ) e. L^1 )' % (C, MC, IO))], 'eqeltrrd', '( %s -> %s e. L^1 )' % (C, MO))
    Cx = '( %s /\\ x e. %s )' % (C, IO)
    xin = D(w, Cx, 'simpr', [], 'x e. %s' % IO)
    # h e. CC from continuity
    hcc = w.s([w.s([w.s([w.s([ch, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (C, MC, IC)), w.s([w.s([], 'eqid', '%s = %s' % (MC, MC))], 'idi', '%s = %s' % (MC, MC))], 'idi', 'x')],
                   'idi', 'x')], 'idi', 'x') if False else None
    fm = w.s([w.s([ch, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (C, MC, IC)), w.s([w.s([], 'eqid', '%s = %s' % (MC, MC))], 'fmpt', '( A. x e. %s %s e. CC <-> %s : %s --> CC )' % (IC, h, MC, IC))],
             'sylibr', '( %s -> A. x e. %s %s e. CC )' % (C, IC, h))
    hcx = w.s([w.s([fm], 'r19.21bi', '( ( %s /\\ x e. %s ) -> %s e. CC )' % (C, IC, h)), w.s([w.s([ss], 'adantr', '( %s -> %s C_ %s )' % (Cx, IO, IC)), xin], 'sseldd', '( %s -> x e. %s )' % (Cx, IC))],
              'idi' if False else 'syldan' if False else 'idi', 'x') if False else None
    xic = w.s([w.s([ss], 'adantr', '( %s -> %s C_ %s )' % (Cx, IO, IC)), xin], 'sseldd', '( %s -> x e. %s )' % (Cx, IC))
    CI = '( %s /\\ x e. %s )' % (C, IC)
    hci = w.s([fm], 'r19.21bi', '( %s -> %s e. CC )' % (CI, h))
    hcx = w.s([w.s([D(w, Cx, 'simpl', [], C), xic], 'jca', '( %s -> %s )' % (Cx, CI)), hci], 'syl', '( %s -> %s e. CC )' % (Cx, h))
    ia = w.s([hcx, ih], 'itgabs', '( %s -> ( abs ` S. %s %s _d x ) <_ S. %s ( abs ` %s ) _d x )' % (C, IO, h, IO, h))
    iba = w.s([hcx, ih], 'iblabs', '( %s -> ( x e. %s |-> ( abs ` %s ) ) e. L^1 )' % (C, IO, h))
    # RHS integrability: ( x e. IO |-> ( c x. EH ) )
    xss = w.s([w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (C, IC)), a1(w, C, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (C, IC))
    cl = Closure(w, C, {c: ('RR', cr)})
    cc = cont(w, C, IC, '( %s x. %s )' % (c, EH), cl, xss)
    MC2 = '( x e. %s |-> ( %s x. %s ) )' % (IC, c, EH); MO2 = '( x e. %s |-> ( %s x. %s ) )' % (IO, c, EH)
    rm2 = w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (C, MC2, IO, MO2))
    ib2 = w.s([rm2, w.s([w.s([w.s([ar, br], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (C, a, b)), cc], 'jca',
                             '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ %s e. ( %s -cn-> CC ) ) )' % (C, a, b, MC2, IC)), w.inst('zl3ibl')], 'syl',
                        '( %s -> ( %s |` %s ) e. L^1 )' % (C, MC2, IO))], 'eqeltrrd', '( %s -> %s e. L^1 )' % (C, MO2))
    xr = w.s([xin, w.inst('elioore')], 'syl', '( %s -> x e. RR )' % Cx)
    ehr = D(w, Cx, 'reefcld', [D(w, Cx, 'renegcld', [D(w, Cx, 'rehalfcld', [xr], '( x / 2 ) e. RR')], '-u ( x / 2 ) e. RR')], '%s e. RR' % EH)
    il = w.s([iba, ib2, D(w, Cx, 'abscld', [hcx], '( abs ` %s ) e. RR' % h), D(w, Cx, 'remulcld', [D(w, Cx, 'adantr', [cr], '%s e. RR' % c), ehr], '( %s x. %s ) e. RR' % (c, EH)),
              hbound(Cx, xin)], 'itgle', '( %s -> S. %s ( abs ` %s ) _d x <_ S. %s ( %s x. %s ) _d x )' % (C, IO, h, IO, c, EH))
    # S. ( c x. EH ) = c x. S. EH
    MO3 = '( x e. %s |-> %s )' % (IO, EH)
    ce = cont(w, C, IC, EH, cl, xss)
    MC3 = '( x e. %s |-> %s )' % (IC, EH)
    rm3 = w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (C, MC3, IO, MO3))
    ib3 = w.s([rm3, w.s([w.s([w.s([ar, br], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (C, a, b)), ce], 'jca',
                             '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ %s e. ( %s -cn-> CC ) ) )' % (C, a, b, MC3, IC)), w.inst('zl3ibl')], 'syl',
                        '( %s -> ( %s |` %s ) e. L^1 )' % (C, MC3, IO))], 'eqeltrrd', '( %s -> %s e. L^1 )' % (C, MO3))
    im = w.s([D(w, C, 'recnd', [cr], '%s e. CC' % c), w.s([w.s([], 'fvex', '%s e. _V' % EH)], 'a1i', '( %s -> %s e. _V )' % (Cx, EH)), ib3], 'itgmulc2',
             '( %s -> ( %s x. S. %s %s _d x ) = S. %s ( %s x. %s ) _d x )' % (C, c, IO, EH, IO, c, EH))
    ie = w.s([ar, br, ab, w.inst('zl3iex')], 'syl3anc', '( %s -> S. %s %s _d x = ( 2 x. ( ( exp ` -u ( %s / 2 ) ) - ( exp ` -u ( %s / 2 ) ) ) ) )' % (C, IO, EH, a, b))
    RV = '( 2 x. ( ( exp ` -u ( %s / 2 ) ) - ( exp ` -u ( %s / 2 ) ) ) )' % (a, b)
    ev = w.s([w.s([im], 'eqcomd', '( %s -> S. %s ( %s x. %s ) _d x = ( %s x. S. %s %s _d x ) )' % (C, IO, c, EH, c, IO, EH)),
              E(w, C, 'oveq2d', [ie], '( %s x. S. %s %s _d x )' % (c, IO, EH), '( %s x. %s )' % (c, RV))], 'eqtrd', '( %s -> S. %s ( %s x. %s ) _d x = ( %s x. %s ) )' % (C, IO, c, EH, c, RV))
    s1 = w.s([ia, il], 'idi' if False else 'letrd' if False else 'idi', 'x') if False else None
    i1r = w.s([w.s([], 'idi', 'x')], 'idi', 'x') if False else None
    ia_r = D(w, C, 'abscld', [w.s([w.s([hcx], 'idi' if False else 'idi', '( %s -> %s e. CC )' % (Cx, h)), ih], 'itgcl', '( %s -> S. %s %s _d x e. CC )' % (C, IO, h))], '( abs ` S. %s %s _d x ) e. RR' % (IO, h))
    ib_r = w.s([w.s([D(w, Cx, 'abscld', [hcx], '( abs ` %s ) e. RR' % h)], 'idi', '( %s -> ( abs ` %s ) e. RR )' % (Cx, h)), iba], 'itgrecl', '( %s -> S. %s ( abs ` %s ) _d x e. RR )' % (C, IO, h))
    ic_r = w.s([D(w, Cx, 'remulcld', [D(w, Cx, 'adantr', [cr], '%s e. RR' % c), ehr], '( %s x. %s ) e. RR' % (c, EH)), ib2], 'itgrecl', '( %s -> S. %s ( %s x. %s ) _d x e. RR )' % (C, IO, c, EH))
    tt = D(w, C, 'letrd', [ia_r, ib_r, ic_r, ia, il], '( abs ` S. %s %s _d x ) <_ S. %s ( %s x. %s ) _d x' % (IO, h, IO, c, EH))
    return w.s([tt, ev], 'breqtrd', '( %s -> ( abs ` S. %s %s _d x ) <_ ( %s x. %s ) )' % (C, IO, h, c, RV))


def kconst(w, C, S1, s1r, s10):
    """( C -> ( ( 2 x. ( S1 + 1 ) ) ^c S1 ) e. RR+ )"""
    return D(w, C, 'rpcxpcld', [D(w, C, 'rpmulcld', [a1(w, C, '2rp', '2 e. RR+'), D(w, C, 'elrpd', [D(w, C, 'readdcld', [s1r, a1(w, C, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % S1),
                                                                                                 linarith(w, C, [s10], '0 < ( %s + 1 )' % S1, closure=Closure(w, C, {S1: ('RR', s1r)}))],
                                                                                      '( %s + 1 ) e. RR+' % S1)], '( 2 x. ( %s + 1 ) ) e. RR+' % S1), s1r], '( ( 2 x. ( %s + 1 ) ) ^c %s ) e. RR+' % (S1, S1))


# ---------------------------------------------------------------- zl3tail
if want('zl3tail'):
    w = W('zl3tail', 'The tail of the Euler integral: ` | S. ( A , B ) e ^ -x x ^ ( W - 1 ) dx | <_ 2 K e ^ ( - A / 2 ) ` ( ~ zl3tlp , ~ zl3iex ).')
    Ctx, Cc = ante_of('zl3tail')
    wc = D(w, Ctx, 'simpll', [], 'W e. CC'); re1 = D(w, Ctx, 'simplr', [], '1 < ( Re ` W )')
    arp = D(w, Ctx, 'simpr1', [], 'A e. RR+'); br = D(w, Ctx, 'simpr2', [], 'B e. RR'); ab = D(w, Ctx, 'simpr3', [], 'A <_ B')
    ar = D(w, Ctx, 'rpred', [arp], 'A e. RR')
    brp = D(w, Ctx, 'elrpd', [br, D(w, Ctx, 'ltletrd', [a1(w, Ctx, '0re', '0 e. RR'), ar, br, D(w, Ctx, 'rpgt0d', [arp], '0 < A'), ab], '0 < B')], 'B e. RR+')
    rw = D(w, Ctx, 'recld', [wc], '( Re ` W ) e. RR')
    wm = D(w, Ctx, 'subcld', [wc, a1(w, Ctx, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, Ctx, [re1], '0 < ( ( Re ` W ) - 1 )', closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)})), re_sub1(w, Ctx, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % Ctx)
    c0B = ccx(w, Ctx, '( W - 1 )', wm, wmp, brp, N='B')
    XW1 = '( x ^c ( W - 1 ) )'
    ssab = w.s([w.s([a1(w, Ctx, '0re', '0 e. RR'), br], 'jca', '( %s -> ( 0 e. RR /\\ B e. RR ) )' % Ctx),
                w.s([D(w, Ctx, 'rpge0d', [arp], '0 <_ A'), D(w, Ctx, 'leidd', [br], 'B <_ B')], 'jca', '( %s -> ( 0 <_ A /\\ B <_ B ) )' % Ctx), w.inst('iccss')], 'syl2anc',
               '( %s -> ( A [,] B ) C_ ( 0 [,] B ) )' % Ctx)
    MB = '( x e. ( 0 [,] B ) |-> %s )' % XW1; MAB = '( x e. ( A [,] B ) |-> %s )' % XW1
    cab = w.s([w.s([ssab, w.inst('resmpt')], 'syl', '( %s -> ( %s |` ( A [,] B ) ) = %s )' % (Ctx, MB, MAB)),
               w.s([ssab, c0B, w.inst('rescncf')], 'sylc', '( %s -> ( %s |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> CC ) )' % (Ctx, MB))], 'eqeltrrd',
              '( %s -> %s e. ( ( A [,] B ) -cn-> CC ) )' % (Ctx, MAB))
    xss = w.s([w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> ( A [,] B ) C_ RR )' % Ctx), a1(w, Ctx, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> ( A [,] B ) C_ CC )' % Ctx)
    h = '( ( exp ` -u x ) x. %s )' % XW1
    ch = cont(w, Ctx, '( A [,] B )', h, Closure(w, Ctx, {}), xss, special={XW1: cab})
    S1 = '( ( Re ` W ) - 1 )'
    s1r = D(w, Ctx, 'resubcld', [rw, a1(w, Ctx, '1re', '1 e. RR')], '%s e. RR' % S1)
    s10 = linarith(w, Ctx, [re1], '0 <_ %s' % S1, closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)}))
    kb = kconst(w, Ctx, S1, s1r, s10)
    KBs = L.KB
    def hb(Cx, xin):
        xr = w.s([xin, w.inst('elioore')], 'syl', '( %s -> x e. RR )' % Cx)
        xp = D(w, Cx, 'ltletrd' if False else 'lttrd', [a1(w, Cx, '0re', '0 e. RR'), D(w, Cx, 'adantr', [ar], 'A e. RR'), xr, D(w, Cx, 'adantr', [D(w, Ctx, 'rpgt0d', [arp], '0 < A')], '0 < A'),
                                                       D(w, Cx, 'simpld', [w.s([xin, w.inst('eliooord')], 'syl', '( %s -> ( A < x /\\ x < B ) )' % Cx)], 'A < x')], '0 < x')
        xrp = D(w, Cx, 'elrpd', [xr, xp], 'x e. RR+')
        return w.s([w.s([D(w, Cx, 'adantr', [w.s([wc, re1], 'jca', '( %s -> %s )' % (Ctx, L.HW))], L.HW), xrp], 'jca', '( %s -> ( %s /\\ x e. RR+ ) )' % (Cx, L.HW)), w.inst('zl3tlp')], 'syl',
                   '( %s -> ( abs ` %s ) <_ ( %s x. ( exp ` -u ( x / 2 ) ) ) )' % (Cx, h, KBs))
    ib = ibnd(w, Ctx, 'A', 'B', ar, br, ab, h, ch, hb, KBs, D(w, Ctx, 'rpred', [kb], '%s e. RR' % KBs), D(w, Ctx, 'rpge0d', [kb], '0 <_ %s' % KBs))
    EA = '( exp ` -u ( A / 2 ) )'; EB = '( exp ` -u ( B / 2 ) )'
    ear = D(w, Ctx, 'reefcld', [D(w, Ctx, 'renegcld', [D(w, Ctx, 'rehalfcld', [ar], '( A / 2 ) e. RR')], '-u ( A / 2 ) e. RR')], '%s e. RR' % EA)
    ebr = D(w, Ctx, 'reefcld', [D(w, Ctx, 'renegcld', [D(w, Ctx, 'rehalfcld', [br], '( B / 2 ) e. RR')], '-u ( B / 2 ) e. RR')], '%s e. RR' % EB)
    eb0 = D(w, Ctx, 'ltled', [a1(w, Ctx, '0re', '0 e. RR'), ebr, w.s([D(w, Ctx, 'renegcld', [D(w, Ctx, 'rehalfcld', [br], '( B / 2 ) e. RR')], '-u ( B / 2 ) e. RR'), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (Ctx, EB))], '0 <_ %s' % EB)
    cl = Closure(w, Ctx, {KBs: ('RR', D(w, Ctx, 'rpred', [kb], '%s e. RR' % KBs)), EA: ('RR', ear), EB: ('RR', ebr)})
    fin = nlinarith(w, Ctx, [eb0, D(w, Ctx, 'rpge0d', [kb], '0 <_ %s' % KBs)], '( %s x. ( 2 x. ( %s - %s ) ) ) <_ ( ( 2 x. %s ) x. %s )' % (KBs, EA, EB, KBs, EA), closure=cl)
    q = w.s([ib, fin], 'letrd' if False else 'idi', 'x') if False else None
    lhs = '( abs ` %s )' % L.EIF('A', 'B')
    q = D(w, Ctx, 'letrd', [D(w, Ctx, 'abscld', [w.s([w.s([], 'idi', 'x')], 'idi', 'x') if False else
                                                 w.s([ib], 'idi' if False else 'idi', 'x') if False else None], 'x') if False else None,
                           ], 'x') if False else None
    # reals for letrd
    lr = w.s([ib, fin], 'idi', 'x') if False else None
    mid = '( %s x. ( 2 x. ( %s - %s ) ) )' % (KBs, EA, EB)
    midr = D(w, Ctx, 'remulcld', [D(w, Ctx, 'rpred', [kb], '%s e. RR' % KBs), D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'resubcld', [ear, ebr], '( %s - %s ) e. RR' % (EA, EB))],
                                                                                  '( 2 x. ( %s - %s ) ) e. RR' % (EA, EB))], '%s e. RR' % mid)
    rhr = D(w, Ctx, 'remulcld', [D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'rpred', [kb], '%s e. RR' % KBs)], '( 2 x. %s ) e. RR' % KBs), ear], '( ( 2 x. %s ) x. %s ) e. RR' % (KBs, EA))
    # lhs real: abs of an integral is real (from the integral in CC)
    Cx = '( %s /\\ x e. ( A (,) B ) )' % Ctx
    from cl import formula_of
    lhsr = w.s([w.s([w.s([], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    q = w.s([w.s([ib, fin], 'idi', 'x')], 'idi', 'x') if False else None
    lhsr = w.s([w.s([w.s([ib], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    q = w.s([ib, fin], 'letrd' if False else 'idi', 'x') if False else None
    q = w.s([ib, fin], 'idi', 'x') if False else None
    q = w.s([w.s([], 'idi', 'x')], 'idi', 'x') if False else None
    # use lelttr-free chaining: letrd needs the three reals; the lhs is real by abscld of itgcl, which ibnd already produced -- recompute
    icc = w.s([w.s([w.s([], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    lhsr = D(w, Ctx, 'abscld', [w.s([w.s([w.s([], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else w.lines and None], 'x') if False else None
    q = w.s([ib, fin], 'idi', 'x') if False else None
    finish_ = None
    # simplest: lhs <_ mid <_ rhs with letrd; the lhs reality via ( abs ` S. ) e. RR from abscld of the integral's closure
    itc = w.s([w.s([w.s([], 'idi', 'x')], 'idi', 'x')], 'idi', 'x') if False else None
    q = w.s([ib, fin], 'idi', 'x') if False else None
    lt = w.s([w.s([], 'idi', 'x')], 'idi', 'x') if False else None
    q = w.s([ib, fin], 'idi', 'x') if False else None
    q = w.s([w.s([], 'idi', 'x')], 'idi', 'x') if False else None
    q = None
    ibs = [l for l in w.lines if ('itgcl |- ( %s -> %s e. CC )' % (Ctx, L.EIF('A', 'B'))) in l]
    ic_name = ibs[0].split(':')[0]
    lhsr = D(w, Ctx, 'abscld', [ic_name], '%s e. RR' % lhs)
    q = D(w, Ctx, 'letrd', [lhsr, midr, rhr, ib, fin], 'x')
    finish(w, q, 'zl3tail')
    go(w)


# ---------------------------------------------------------------- zl3err
if want('zl3err'):
    w = W('zl3err', 'The error of the approximant: ` | S. ( 0 , N ) e ^ -x x ^ ( W - 1 ) dx - S. ( 0 , N ) ( 1 - x / N ) ^ N x ^ ( W - 1 ) dx | <_ 2 K / N ` '
          '( ~ zl3erp , ~ zl3iex ).')
    Ctx, Cc = ante_of('zl3err')
    wc = D(w, Ctx, 'simpll', [], 'W e. CC'); re1 = D(w, Ctx, 'simplr', [], '1 < ( Re ` W )'); nn = D(w, Ctx, 'simpr', [], 'N e. NN')
    nr = D(w, Ctx, 'nnred', [nn], 'N e. RR'); nrp = D(w, Ctx, 'nnrpd', [nn], 'N e. RR+'); nz = D(w, Ctx, 'nnne0d', [nn], 'N =/= 0')
    rw = D(w, Ctx, 'recld', [wc], '( Re ` W ) e. RR')
    wm = D(w, Ctx, 'subcld', [wc, a1(w, Ctx, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, Ctx, [re1], '0 < ( ( Re ` W ) - 1 )', closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)})), re_sub1(w, Ctx, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % Ctx)
    XW1 = '( x ^c ( W - 1 ) )'
    cW1 = ccx(w, Ctx, '( W - 1 )', wm, wmp, nrp)
    ICC = '( 0 [,] N )'; IOO = '( 0 (,) N )'
    xss = dom_cc(w, Ctx, ICC, nr)
    cl = Closure(w, Ctx, {'N': ('RR', nr)})
    cl.have('N', 'ne0', nz); cl.have('N', 'NN0', D(w, Ctx, 'nnnn0d', [nn], 'N e. NN0'))
    P = '( ( 1 - ( x / N ) ) ^ N )'; EXx = '( exp ` -u x )'
    f = '( %s x. %s )' % (EXx, XW1); g = '( %s x. %s )' % (P, XW1); h = '( ( %s - %s ) x. %s )' % (EXx, P, XW1)
    cf = cont(w, Ctx, ICC, f, cl, xss, special={XW1: cW1})
    cg = cont(w, Ctx, ICC, g, cl, xss, special={XW1: cW1})
    ch = cont(w, Ctx, ICC, h, cl, xss, special={XW1: cW1})
    _, iff = ibl_of(w, Ctx, 'N', f, cf, nr)
    _, igg = ibl_of(w, Ctx, 'N', g, cg, nr)
    Cx = '( %s /\\ x e. %s )' % (Ctx, IOO)
    fv = w.s([w.s([], 'ovex', '%s e. _V' % f)], 'a1i', '( %s -> %s e. _V )' % (Cx, f))
    gv = w.s([w.s([], 'ovex', '%s e. _V' % g)], 'a1i', '( %s -> %s e. _V )' % (Cx, g))
    isub = w.s([fv, iff, gv, igg], 'itgsub', '( %s -> S. %s ( %s - %s ) _d x = ( S. %s %s _d x - S. %s %s _d x ) )' % (Ctx, IOO, f, g, IOO, f, IOO, g))
    Cx2, xc = dom_x(w, Ctx, IOO, nr)
    clx = Closure(w, Cx2, {'x': ('CC', xc), 'W': ('CC', D(w, Cx2, 'adantr', [wc], 'W e. CC')), 'N': ('RR', D(w, Cx2, 'adantr', [nr], 'N e. RR'))})
    clx.have('N', 'ne0', D(w, Cx2, 'adantr', [nz], 'N =/= 0')); clx.have('N', 'NN0', D(w, Cx2, 'adantr', [D(w, Ctx, 'nnnn0d', [nn], 'N e. NN0')], 'N e. NN0'))
    pw = E(w, Cx2, 'subdird', [clx.mem(EXx, 'CC'), clx.mem(P, 'CC'), clx.mem(XW1, 'CC')], h, '( %s - %s )' % (f, g))
    ieq = w.s([w.s([pw], 'eqcomd', '( %s -> ( %s - %s ) = %s )' % (Cx2, f, g, h))], 'itgeq2dv', '( %s -> S. %s ( %s - %s ) _d x = S. %s %s _d x )' % (Ctx, IOO, f, g, IOO, h))
    KAs = L.KA
    S2 = '( ( Re ` W ) + 1 )'
    s2r = D(w, Ctx, 'readdcld', [rw, a1(w, Ctx, '1re', '1 e. RR')], '%s e. RR' % S2)
    s20 = linarith(w, Ctx, [re1], '0 <_ %s' % S2, closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)}))
    ka = kconst(w, Ctx, S2, s2r, s20)
    Q = '( %s / N )' % KAs
    qrp = D(w, Ctx, 'rpdivcld', [ka, nrp], '%s e. RR+' % Q)
    def hb(Cxx, xin):
        return w.s([w.s([D(w, Cxx, 'adantr', [w.s([wc, re1], 'jca', '( %s -> %s )' % (Ctx, L.HW))], L.HW), w.s([D(w, Cxx, 'adantr', [nn], 'N e. NN'), xin], 'jca', '( %s -> ( N e. NN /\\ x e. %s ) )' % (Cxx, IOO))],
                        'jca', '( %s -> ( %s /\\ ( N e. NN /\\ x e. %s ) ) )' % (Cxx, L.HW, IOO)), w.inst('zl3erp')], 'syl',
                   '( %s -> ( abs ` %s ) <_ ( %s x. ( exp ` -u ( x / 2 ) ) ) )' % (Cxx, h, Q))
    z0 = a1(w, Ctx, '0re', '0 e. RR')
    ib = ibnd(w, Ctx, '0', 'N', z0, nr, D(w, Ctx, 'nnge1d' if False else 'rpge0d', [nrp], '0 <_ N'), h, ch, hb, Q, D(w, Ctx, 'rpred', [qrp], '%s e. RR' % Q), D(w, Ctx, 'rpge0d', [qrp], '0 <_ %s' % Q))
    E0 = '( exp ` -u ( 0 / 2 ) )'; EN = '( exp ` -u ( N / 2 ) )'
    e0 = chain(w, Ctx, [E0, '( exp ` -u 0 )', '( exp ` 0 )', '1'],
               [E(w, Ctx, 'fveq2d', [E(w, Ctx, 'negeqd', [E(w, Ctx, 'div0d', [a1(w, Ctx, '2cn', '2 e. CC'), a1(w, Ctx, '2ne0', '2 =/= 0')], '( 0 / 2 )', '0')], '-u ( 0 / 2 )', '-u 0')], E0, '( exp ` -u 0 )'),
                E(w, Ctx, 'fveq2d', [w.s([w.s([], 'neg0', '-u 0 = 0')], 'a1i', '( %s -> -u 0 = 0 )' % Ctx)], '( exp ` -u 0 )', '( exp ` 0 )'),
                w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( %s -> ( exp ` 0 ) = 1 )' % Ctx)])
    RV = '( %s x. ( 2 x. ( %s - %s ) ) )' % (Q, E0, EN)
    RV1 = '( %s x. ( 2 x. ( 1 - %s ) ) )' % (Q, EN)
    rv1 = E(w, Ctx, 'oveq2d', [E(w, Ctx, 'oveq2d', [E(w, Ctx, 'oveq1d', [e0], '( %s - %s )' % (E0, EN), '( 1 - %s )' % EN)], '( 2 x. ( %s - %s ) )' % (E0, EN), '( 2 x. ( 1 - %s ) )' % EN)], RV, RV1)
    enr = D(w, Ctx, 'reefcld', [D(w, Ctx, 'renegcld', [D(w, Ctx, 'rehalfcld', [nr], '( N / 2 ) e. RR')], '-u ( N / 2 ) e. RR')], '%s e. RR' % EN)
    en0 = D(w, Ctx, 'ltled', [a1(w, Ctx, '0re', '0 e. RR'), enr, w.s([D(w, Ctx, 'renegcld', [D(w, Ctx, 'rehalfcld', [nr], '( N / 2 ) e. RR')], '-u ( N / 2 ) e. RR'), w.inst('efgt0')], 'syl',
                                                                '( %s -> 0 < %s )' % (Ctx, EN))], '0 <_ %s' % EN)
    clq = Closure(w, Ctx, {Q: ('RR', D(w, Ctx, 'rpred', [qrp], '%s e. RR' % Q)), EN: ('RR', enr)})
    fin = nlinarith(w, Ctx, [en0, D(w, Ctx, 'rpge0d', [qrp], '0 <_ %s' % Q)], '%s <_ ( 2 x. %s )' % (RV1, Q), closure=clq)
    kac = D(w, Ctx, 'rpcnd', [ka], '%s e. CC' % KAs)
    tq = w.s([E(w, Ctx, 'divassd', [a1(w, Ctx, '2cn', '2 e. CC'), kac, D(w, Ctx, 'rpcnd', [nrp], 'N e. CC'), nz], '( ( 2 x. %s ) / N )' % KAs, '( 2 x. %s )' % Q)], 'eqcomd',
             '( %s -> ( 2 x. %s ) = ( ( 2 x. %s ) / N ) )' % (Ctx, Q, KAs))
    lhs = '( abs ` ( %s - %s ) )' % (L.EIF('0', 'N'), L.JN('N', 'N', 'W'))
    lh1 = E(w, Ctx, 'fveq2d', [w.s([ieq, isub], 'eqtr3d', '( %s -> S. %s %s _d x = ( S. %s %s _d x - S. %s %s _d x ) )' % (Ctx, IOO, h, IOO, f, IOO, g))],
            '( abs ` S. %s %s _d x )' % (IOO, h), lhs)
    ibs = [l for l in w.lines if ('itgcl |- ( %s -> S. %s %s _d x e. CC )' % (Ctx, IOO, h)) in l]
    lhsr = D(w, Ctx, 'abscld', [ibs[0].split(':')[0]], '( abs ` S. %s %s _d x ) e. RR' % (IOO, h))
    rvr = w.s([w.s([], 'idi', 'x')], 'idi', 'x') if False else None
    rv1r = D(w, Ctx, 'remulcld', [D(w, Ctx, 'rpred', [qrp], '%s e. RR' % Q), D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'resubcld', [a1(w, Ctx, '1re', '1 e. RR'), enr], '( 1 - %s ) e. RR' % EN)],
                                                                                   '( 2 x. ( 1 - %s ) ) e. RR' % EN)], '%s e. RR' % RV1)
    t1 = D(w, Ctx, 'letrd', [lhsr, rv1r, D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'rpred', [qrp], '%s e. RR' % Q)], '( 2 x. %s ) e. RR' % Q),
                             w.s([ib, rv1], 'breqtrd', '( %s -> ( abs ` S. %s %s _d x ) <_ %s )' % (Ctx, IOO, h, RV1)), fin], '( abs ` S. %s %s _d x ) <_ ( 2 x. %s )' % (IOO, h, Q))
    q = w.s([w.s([lh1, t1], 'eqbrtrrd', '( %s -> %s <_ ( 2 x. %s ) )' % (Ctx, lhs, Q)), tq], 'breqtrd', 'x')
    finish(w, q, 'zl3err')
    go(w)


# ---------------------------------------------------------------- zl3eub
if want('zl3eub'):
    w = W('zl3eub', 'The Euler integral up to ` T >_ 2 ` against ` Gamma ( W ) ` : split at ` n = |_ T ` ; the error ( ~ zl3err ) and the tail '
          '( ~ zl3tail , ~ bvexpl2 ) are ` O ( 1 / n ) ` .')
    Ctx, Cc = ante_of('zl3eub')
    wc = D(w, Ctx, 'simpll', [], 'W e. CC'); re1 = D(w, Ctx, 'simplr', [], '1 < ( Re ` W )')
    tr = D(w, Ctx, 'simprl', [], 'T e. RR'); t2 = D(w, Ctx, 'simprr', [], '2 <_ T')
    HWs = w.s([wc, re1], 'jca', '( %s -> %s )' % (Ctx, L.HW))
    n = '( |_ ` T )'
    nz = D(w, Ctx, 'flcld', [tr], '%s e. ZZ' % n)
    n2 = w.s([t2, w.s([tr, a1(w, Ctx, '2z', '2 e. ZZ'), w.inst('flge')], 'syl2anc', '( %s -> ( 2 <_ T <-> 2 <_ %s ) )' % (Ctx, n))], 'mpbid', '( %s -> 2 <_ %s )' % (Ctx, n))
    nT = w.s([tr, w.inst('flle')], 'syl', '( %s -> %s <_ T )' % (Ctx, n))
    nr = D(w, Ctx, 'zred', [nz], '%s e. RR' % n)
    cl0 = Closure(w, Ctx, {n: ('RR', nr), 'T': ('RR', tr)})
    n0 = linarith(w, Ctx, [n2], '0 < %s' % n, closure=cl0)
    nn = w.s([w.s([nz, n0], 'jca', '( %s -> ( %s e. ZZ /\\ 0 < %s ) )' % (Ctx, n, n)), w.s([], 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (n, n, n))], 'sylibr', '( %s -> %s e. NN )' % (Ctx, n))
    nrp = D(w, Ctx, 'nnrpd', [nn], '%s e. RR+' % n)
    trp = D(w, Ctx, 'elrpd', [tr, linarith(w, Ctx, [t2], '0 < T', closure=cl0)], 'T e. RR+')
    rw = D(w, Ctx, 'recld', [wc], '( Re ` W ) e. RR')
    wm = D(w, Ctx, 'subcld', [wc, a1(w, Ctx, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, Ctx, [re1], '0 < ( ( Re ` W ) - 1 )', closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)})), re_sub1(w, Ctx, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % Ctx)
    XW1 = '( x ^c ( W - 1 ) )'
    f = '( ( exp ` -u x ) x. %s )' % XW1
    cT = ccx(w, Ctx, '( W - 1 )', wm, wmp, trp, N='T')
    cn_ = ccx(w, Ctx, '( W - 1 )', wm, wmp, nrp, N=n)
    xsT = dom_cc(w, Ctx, '( 0 [,] T )', tr); xsn = dom_cc(w, Ctx, '( 0 [,] %s )' % n, nr)
    clc = Closure(w, Ctx, {})
    cfT = cont(w, Ctx, '( 0 [,] T )', f, clc, xsT, special={XW1: cT})
    cfn = cont(w, Ctx, '( 0 [,] %s )' % n, f, clc, xsn, special={XW1: cn_})
    _, i0 = ibl_of(w, Ctx, n, f, cfn, nr)
    ss = w.s([w.s([a1(w, Ctx, '0re', '0 e. RR'), tr], 'jca', '( %s -> ( 0 e. RR /\\ T e. RR ) )' % Ctx),
              w.s([D(w, Ctx, 'rpge0d', [nrp], '0 <_ %s' % n), D(w, Ctx, 'leidd', [tr], 'T <_ T')], 'jca', '( %s -> ( 0 <_ %s /\\ T <_ T ) )' % (Ctx, n)), w.inst('iccss')], 'syl2anc',
             '( %s -> ( %s [,] T ) C_ ( 0 [,] T ) )' % (Ctx, n))
    MT = '( x e. ( 0 [,] T ) |-> %s )' % f; MnT = '( x e. ( %s [,] T ) |-> %s )' % (n, f); MnTo = '( x e. ( %s (,) T ) |-> %s )' % (n, f)
    cnT = w.s([w.s([ss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` ( %s [,] T ) ) = %s )' % (Ctx, MT, n, MnT)),
               w.s([ss, cfT, w.inst('rescncf')], 'sylc', '( %s -> ( %s |` ( %s [,] T ) ) e. ( ( %s [,] T ) -cn-> CC ) )' % (Ctx, MT, n, n))], 'eqeltrrd',
              '( %s -> %s e. ( ( %s [,] T ) -cn-> CC ) )' % (Ctx, MnT, n))
    ss2 = w.s([w.s([], 'ioossicc', '( %s (,) T ) C_ ( %s [,] T )' % (n, n))], 'a1i', '( %s -> ( %s (,) T ) C_ ( %s [,] T ) )' % (Ctx, n, n))
    i1 = w.s([w.s([ss2, w.inst('resmpt')], 'syl', '( %s -> ( %s |` ( %s (,) T ) ) = %s )' % (Ctx, MnT, n, MnTo)),
              w.s([w.s([w.s([nr, tr], 'jca', '( %s -> ( %s e. RR /\\ T e. RR ) )' % (Ctx, n)), cnT], 'jca', '( %s -> ( ( %s e. RR /\\ T e. RR ) /\\ %s e. ( ( %s [,] T ) -cn-> CC ) ) )' % (Ctx, n, MnT, n)),
                   w.inst('zl3ibl')], 'syl', '( %s -> ( %s |` ( %s (,) T ) ) e. L^1 )' % (Ctx, MnT, n))], 'eqeltrrd', '( %s -> %s e. L^1 )' % (Ctx, MnTo))
    Cx, xc = dom_x(w, Ctx, '( 0 (,) T )', tr)
    clx = Closure(w, Cx, {'x': ('CC', xc), 'W': ('CC', D(w, Cx, 'adantr', [wc], 'W e. CC'))})
    fcx = clx.mem(f, 'CC')
    nin = w.s([w.s([nr, D(w, Ctx, 'rpge0d', [nrp], '0 <_ %s' % n), nT], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ T ) )' % (Ctx, n, n, n)),
               w.s([a1(w, Ctx, '0re', '0 e. RR'), tr, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( 0 [,] T ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ T ) ) )' % (Ctx, n, n, n, n))], 'mpbird',
              '( %s -> %s e. ( 0 [,] T ) )' % (Ctx, n))
    I0 = L.EIF('0', n); I1 = L.EIF(n, 'T'); IT = L.EIF('0', 'T')
    sp = w.s([a1(w, Ctx, '0re', '0 e. RR'), tr, nin, fcx, i0, i1], 'itgsplitioo', '( %s -> %s = ( %s + %s ) )' % (Ctx, IT, I0, I1))
    J = L.JN(n, n, 'W'); G = '( _G ` W )'
    Cx0, xc0 = dom_x(w, Ctx, '( 0 (,) %s )' % n, nr)
    Cx1 = '( %s /\\ x e. ( %s (,) T ) )' % (Ctx, n)
    xc1 = D(w, Cx1, 'recnd', [w.s([D(w, Cx1, 'simpr', [], 'x e. ( %s (,) T )' % n), w.inst('elioore')], 'syl', '( %s -> x e. RR )' % Cx1)], 'x e. CC')
    i0c = w.s([Closure(w, Cx0, {'x': ('CC', xc0), 'W': ('CC', D(w, Cx0, 'adantr', [wc], 'W e. CC'))}).mem(f, 'CC'), i0], 'itgcl', '( %s -> %s e. CC )' % (Ctx, I0))
    i1c = w.s([Closure(w, Cx1, {'x': ('CC', xc1), 'W': ('CC', D(w, Cx1, 'adantr', [wc], 'W e. CC'))}).mem(f, 'CC'), i1], 'itgcl', '( %s -> %s e. CC )' % (Ctx, I1))
    # J e. CC and G e. CC
    PN = '( ( 1 - ( x / %s ) ) ^ %s )' % (n, n)
    cln = Closure(w, Ctx, {n: ('RR', nr)}); cln.have(n, 'ne0', D(w, Ctx, 'nnne0d', [nn], '%s =/= 0' % n)); cln.have(n, 'NN0', D(w, Ctx, 'nnnn0d', [nn], '%s e. NN0' % n))
    cj = cont(w, Ctx, '( 0 [,] %s )' % n, '( %s x. %s )' % (PN, XW1), cln, xsn, special={XW1: cn_})
    _, ij = ibl_of(w, Ctx, n, '( %s x. %s )' % (PN, XW1), cj, nr)
    jc = w.s([w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PN, XW1))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Cx0, PN, XW1)), ij], 'itgcl', '( %s -> %s e. CC )' % (Ctx, J))
    rwpos = linarith(w, Ctx, [re1], '0 < ( Re ` W )', closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)}))
    gc = w.s([w.s([w.s([wc, rwpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % Ctx), w.inst('zrenn')], 'syl', '( %s -> W e. ( CC \\ ( ZZ \\ NN ) ) )' % Ctx), w.inst('gamcl')], 'syl',
             '( %s -> %s e. CC )' % (Ctx, G))
    # triangle
    X0 = '( %s + %s )' % (I0, I1); Y0 = '( %s + %s )' % (J, I1)
    tri1 = D(w, Ctx, 'abs3difd', [D(w, Ctx, 'addcld', [i0c, i1c], '%s e. CC' % X0), gc, D(w, Ctx, 'addcld', [jc, i1c], '%s e. CC' % Y0)],
             '( abs ` ( %s - %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - %s ) ) )' % (X0, G, X0, Y0, Y0, G))
    e1 = E(w, Ctx, 'fveq2d', [E(w, Ctx, 'pnpcan2d', [i0c, jc, i1c], '( %s - %s )' % (X0, Y0), '( %s - %s )' % (I0, J))], '( abs ` ( %s - %s ) )' % (X0, Y0), '( abs ` ( %s - %s ) )' % (I0, J))
    e2 = E(w, Ctx, 'fveq2d', [E(w, Ctx, 'addsubd', [jc, i1c, gc], '( %s - %s )' % (Y0, G), '( ( %s - %s ) + %s )' % (J, G, I1))], '( abs ` ( %s - %s ) )' % (Y0, G), '( abs ` ( ( %s - %s ) + %s ) )' % (J, G, I1))
    tri2 = D(w, Ctx, 'abstrid', [D(w, Ctx, 'subcld', [jc, gc], '( %s - %s ) e. CC' % (J, G)), i1c], '( abs ` ( ( %s - %s ) + %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` %s ) )' % (J, G, I1, J, G, I1))
    er = w.s([w.s([HWs, nn], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (Ctx, L.HW, n)), w.inst('zl3err')], 'syl', '( %s -> ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) / %s ) )' % (Ctx, I0, J, L.KA, n))
    ta = w.s([w.s([HWs, w.s([nrp, tr, nT], '3jca', '( %s -> ( %s e. RR+ /\\ T e. RR /\\ %s <_ T ) )' % (Ctx, n, n))], 'jca', '( %s -> ( %s /\\ ( %s e. RR+ /\\ T e. RR /\\ %s <_ T ) ) )' % (Ctx, L.HW, n, n)),
              w.inst('zl3tail')], 'syl', '( %s -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. ( exp ` -u ( %s / 2 ) ) ) )' % (Ctx, I1, L.KB, n))
    EN = '( exp ` -u ( %s / 2 ) )' % n
    n2r = D(w, Ctx, 'rehalfcld', [nr], '( %s / 2 ) e. RR' % n)
    bx = w.s([w.s([n2r, D(w, Ctx, 'ltled', [a1(w, Ctx, '0re', '0 e. RR'), n2r, D(w, Ctx, 'halfpos2' if False else 'divgt0d', [nr, a1(w, Ctx, '2re', '2 e. RR'), n0, a1(w, Ctx, '2pos', '0 < 2')],
                                                                                                                  '0 < ( %s / 2 )' % n)], '0 <_ ( %s / 2 )' % n)], 'jca',
                  '( %s -> ( ( %s / 2 ) e. RR /\\ 0 <_ ( %s / 2 ) ) )' % (Ctx, n, n)), w.inst('bvexpl2')], 'syl', '( %s -> ( %s x. ( %s / 2 ) ) <_ ( 1 - %s ) )' % (Ctx, EN, n, EN))
    enr = D(w, Ctx, 'reefcld', [D(w, Ctx, 'renegcld', [n2r], '-u ( %s / 2 ) e. RR' % n)], '%s e. RR' % EN)
    en0 = D(w, Ctx, 'ltled', [a1(w, Ctx, '0re', '0 e. RR'), enr, w.s([D(w, Ctx, 'renegcld', [n2r], '-u ( %s / 2 ) e. RR' % n), w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (Ctx, EN))], '0 <_ %s' % EN)
    kbr = kconst(w, Ctx, '( ( Re ` W ) - 1 )', D(w, Ctx, 'resubcld', [rw, a1(w, Ctx, '1re', '1 e. RR')], '( ( Re ` W ) - 1 ) e. RR'),
                 linarith(w, Ctx, [re1], '0 <_ ( ( Re ` W ) - 1 )', closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)})))
    kar = kconst(w, Ctx, '( ( Re ` W ) + 1 )', D(w, Ctx, 'readdcld', [rw, a1(w, Ctx, '1re', '1 e. RR')], '( ( Re ` W ) + 1 ) e. RR'),
                 linarith(w, Ctx, [re1], '0 <_ ( ( Re ` W ) + 1 )', closure=Closure(w, Ctx, {'( Re ` W )': ('RR', rw)})))
    KAs, KBs = L.KA, L.KB
    # en x. n <_ 2  => ( 2 KB ) en <_ ( 4 KB ) / n : multiply out with n > 0
    ENn = '( %s x. %s )' % (EN, n)
    cln2 = Closure(w, Ctx, {EN: ('RR', enr), n: ('RR', nr), '( %s / 2 )' % n: ('RR', n2r)})
    cln2.atom('( %s / 2 )' % n)
    hh = lineq(w, Ctx, '( %s / 2 )' % n, '( ( 1 / 2 ) x. %s )' % n, closure=Closure(w, Ctx, {n: ('RR', nr)})) if False else None
    n2eq = w.s([E(w, Ctx, 'divrec2d', [D(w, Ctx, 'recnd', [nr], '%s e. CC' % n), a1(w, Ctx, '2cn', '2 e. CC'), a1(w, Ctx, '2ne0', '2 =/= 0')], '( %s / 2 )' % n, '( ( 1 / 2 ) x. %s )' % n)],
               'idi', '( %s -> ( %s / 2 ) = ( ( 1 / 2 ) x. %s ) )' % (Ctx, n, n))
    bx2 = w.s([bx, E(w, Ctx, 'oveq2d', [n2eq], '( %s x. ( %s / 2 ) )' % (EN, n), '( %s x. ( ( 1 / 2 ) x. %s ) )' % (EN, n))], 'eqbrtrrd' if False else 'idi', 'x') if False else None
    bx2 = w.s([w.s([E(w, Ctx, 'oveq2d', [n2eq], '( %s x. ( %s / 2 ) )' % (EN, n), '( %s x. ( ( 1 / 2 ) x. %s ) )' % (EN, n))], 'eqcomd',
                   '( %s -> ( %s x. ( ( 1 / 2 ) x. %s ) ) = ( %s x. ( %s / 2 ) ) )' % (Ctx, EN, n, EN, n)), bx], 'eqbrtrd',
              '( %s -> ( %s x. ( ( 1 / 2 ) x. %s ) ) <_ ( 1 - %s ) )' % (Ctx, EN, n, EN))
    cln3 = Closure(w, Ctx, {EN: ('RR', enr), n: ('RR', nr)})
    enn = nlinarith(w, Ctx, [bx2, en0], '( %s x. %s ) <_ 2' % (EN, n), closure=cln3)
    en2n = w.s([enn, D(w, Ctx, 'lemuldiv' if False else 'idi', [], 'x') if False else
                w.s([enr, a1(w, Ctx, '2re', '2 e. RR'), w.s([nr, n0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (Ctx, n, n)), w.inst('lemuldiv')], 'syl3anc',
                    '( %s -> ( ( %s x. %s ) <_ 2 <-> %s <_ ( 2 / %s ) ) )' % (Ctx, EN, n, EN, n))], 'mpbid', '( %s -> %s <_ ( 2 / %s ) )' % (Ctx, EN, n))
    K2B = '( 2 x. %s )' % KBs
    k2br = D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'rpred', [kbr], '%s e. RR' % KBs)], '%s e. RR' % K2B)
    tb = D(w, Ctx, 'lemul2ad', [enr, D(w, Ctx, 'redivcld', [a1(w, Ctx, '2re', '2 e. RR'), nr, D(w, Ctx, 'nnne0d', [nn], '%s =/= 0' % n)], '( 2 / %s ) e. RR' % n), k2br,
                               D(w, Ctx, 'ltled', [a1(w, Ctx, '0re', '0 e. RR'), k2br, D(w, Ctx, 'rpgt0d', [D(w, Ctx, 'rpmulcld', [a1(w, Ctx, '2rp', '2 e. RR+'), kbr], '%s e. RR+' % K2B)], '0 < %s' % K2B)], '0 <_ %s' % K2B),
                               en2n], '( %s x. %s ) <_ ( %s x. ( 2 / %s ) )' % (K2B, EN, K2B, n))
    # algebra: ( K2B x. ( 2 / n ) ) = ( ( 4 x. KB ) / n ); KK / n = ( 2 KA ) / n + ( 4 KB ) / n
    nc = D(w, Ctx, 'recnd', [nr], '%s e. CC' % n); nne = D(w, Ctx, 'nnne0d', [nn], '%s =/= 0' % n)
    kbc = D(w, Ctx, 'rpcnd', [kbr], '%s e. CC' % KBs); kac = D(w, Ctx, 'rpcnd', [kar], '%s e. CC' % KAs)
    c2 = a1(w, Ctx, '2cn', '2 e. CC')
    a4 = chain(w, Ctx, ['( %s x. ( 2 / %s ) )' % (K2B, n), '( ( %s x. 2 ) / %s )' % (K2B, n), '( ( 4 x. %s ) / %s )' % (KBs, n)],
               [('r', E(w, Ctx, 'divassd', [D(w, Ctx, 'mulcld', [c2, kbc], '%s e. CC' % K2B), c2, nc, nne], '( ( %s x. 2 ) / %s )' % (K2B, n), '( %s x. ( 2 / %s ) )' % (K2B, n))),
                E(w, Ctx, 'oveq1d', [lineq(w, Ctx, '( %s x. 2 )' % K2B, '( 4 x. %s )' % KBs, closure=Closure(w, Ctx, {KBs: ('RR', D(w, Ctx, 'rpred', [kbr], '%s e. RR' % KBs))}))],
                  '( ( %s x. 2 ) / %s )' % (K2B, n), '( ( 4 x. %s ) / %s )' % (KBs, n))])
    kkn = E(w, Ctx, 'divdird', [D(w, Ctx, 'mulcld', [c2, kac], '( 2 x. %s ) e. CC' % KAs), D(w, Ctx, 'mulcld', [a1(w, Ctx, '4cn', '4 e. CC'), kbc], '( 4 x. %s ) e. CC' % KBs), nc, nne],
            '( %s / %s )' % (L.KK, n), '( ( ( 2 x. %s ) / %s ) + ( ( 4 x. %s ) / %s ) )' % (KAs, n, KBs, n))
    # final linear combination
    at = {}
    U = '( ( 2 x. %s ) / %s )' % (KAs, n); V = '( ( 4 x. %s ) / %s )' % (KBs, n)
    a_1 = '( abs ` ( %s - %s ) )' % (I0, J); a_2 = '( abs ` ( %s - %s ) )' % (J, G); a_3 = '( abs ` %s )' % I1; LHS = '( abs ` ( %s - %s ) )' % (IT, G)
    lhs_eq = E(w, Ctx, 'fveq2d', [E(w, Ctx, 'oveq1d', [sp], '( %s - %s )' % (IT, G), '( %s - %s )' % (X0, G))], LHS, '( abs ` ( %s - %s ) )' % (X0, G))
    b1 = w.s([lhs_eq, w.s([tri1, w.s([e1, E(w, Ctx, 'idi' if False else 'eqid' if False else 'idi', [], 'x') if False else e2], 'idi', 'x') if False else None], 'idi', 'x') if False else tri1], 'eqbrtrd',
             '( %s -> %s <_ ( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - %s ) ) ) )' % (Ctx, LHS, X0, Y0, Y0, G))
    b2 = w.s([b1, E(w, Ctx, 'oveq12d', [e1, e2], '( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - %s ) ) )' % (X0, Y0, Y0, G), '( %s + ( abs ` ( ( %s - %s ) + %s ) ) )' % (a_1, J, G, I1))],
             'breqtrd', '( %s -> %s <_ ( %s + ( abs ` ( ( %s - %s ) + %s ) ) ) )' % (Ctx, LHS, a_1, J, G, I1))
    def R(t, st):
        return (t, ('RR', st))
    reals = {}
    lr = D(w, Ctx, 'abscld', [w.s([i0c, i1c], 'idi', 'x') if False else D(w, Ctx, 'subcld', [D(w, Ctx, 'addcld', [i0c, i1c], '%s e. CC' % X0), gc], '( %s - %s ) e. CC' % (X0, G))], '( abs ` ( %s - %s ) ) e. RR' % (X0, G))
    lr2 = w.s([lhs_eq, lr], 'eqeltrd' if False else 'idi', 'x') if False else D(w, Ctx, 'abscld', [D(w, Ctx, 'subcld', [w.s([sp, D(w, Ctx, 'addcld', [i0c, i1c], '%s e. CC' % X0)], 'eqeltrd', '( %s -> %s e. CC )' % (Ctx, IT)), gc], '( %s - %s ) e. CC' % (IT, G))], '%s e. RR' % LHS)
    clf = Closure(w, Ctx, {LHS: ('RR', lr2), a_1: ('RR', D(w, Ctx, 'abscld', [D(w, Ctx, 'subcld', [i0c, jc], '( %s - %s ) e. CC' % (I0, J))], '%s e. RR' % a_1)),
                           a_2: ('RR', D(w, Ctx, 'abscld', [D(w, Ctx, 'subcld', [jc, gc], '( %s - %s ) e. CC' % (J, G))], '%s e. RR' % a_2)),
                           a_3: ('RR', D(w, Ctx, 'abscld', [i1c], '%s e. RR' % a_3)),
                           '( abs ` ( ( %s - %s ) + %s ) )' % (J, G, I1): ('RR', D(w, Ctx, 'abscld', [D(w, Ctx, 'addcld', [D(w, Ctx, 'subcld', [jc, gc], '( %s - %s ) e. CC' % (J, G)), i1c],
                                                                                                         '( ( %s - %s ) + %s ) e. CC' % (J, G, I1))], '( abs ` ( ( %s - %s ) + %s ) ) e. RR' % (J, G, I1))),
                           U: ('RR', D(w, Ctx, 'redivcld', [D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'rpred', [kar], '%s e. RR' % KAs)], '( 2 x. %s ) e. RR' % KAs), nr, nne], '%s e. RR' % U)),
                           V: ('RR', D(w, Ctx, 'redivcld', [D(w, Ctx, 'remulcld', [a1(w, Ctx, '4re', '4 e. RR'), D(w, Ctx, 'rpred', [kbr], '%s e. RR' % KBs)], '( 4 x. %s ) e. RR' % KBs), nr, nne], '%s e. RR' % V)),
                           '( %s x. %s )' % (K2B, EN): ('RR', D(w, Ctx, 'remulcld', [k2br, enr], '( %s x. %s ) e. RR' % (K2B, EN))),
                           '( %s / %s )' % (L.KK, n): ('RR', D(w, Ctx, 'redivcld', [D(w, Ctx, 'readdcld', [D(w, Ctx, 'remulcld', [a1(w, Ctx, '2re', '2 e. RR'), D(w, Ctx, 'rpred', [kar], '%s e. RR' % KAs)], '( 2 x. %s ) e. RR' % KAs),
                                                                                                          D(w, Ctx, 'remulcld', [a1(w, Ctx, '4re', '4 e. RR'), D(w, Ctx, 'rpred', [kbr], '%s e. RR' % KBs)], '( 4 x. %s ) e. RR' % KBs)],
                                                                                         '%s e. RR' % L.KK), nr, nne], '( %s / %s ) e. RR' % (L.KK, n)))})
    for t in list(clf.memo.keys()):
        clf.atom(t[0])
    tb2 = w.s([tb, a4], 'breqtrd', '( %s -> ( %s x. %s ) <_ %s )' % (Ctx, K2B, EN, V))
    kk1 = D(w, Ctx, 'eqled', [clf.mem('( %s / %s )' % (L.KK, n), 'RR'), kkn], '( %s / %s ) <_ ( %s + %s )' % (L.KK, n, U, V))
    kk2 = D(w, Ctx, 'eqled', [D(w, Ctx, 'readdcld', [clf.mem(U, 'RR'), clf.mem(V, 'RR')], '( %s + %s ) e. RR' % (U, V)), w.s([kkn], 'eqcomd', '( %s -> ( %s + %s ) = ( %s / %s ) )' % (Ctx, U, V, L.KK, n))],
              '( %s + %s ) <_ ( %s / %s )' % (U, V, L.KK, n))
    q = linarith(w, Ctx, [b2, tri2, er, ta, tb2, kk1, kk2], '%s <_ ( %s + ( %s / %s ) )' % (LHS, a_2, L.KK, n), closure=clf)
    finish(w, q, 'zl3eub')
    go(w)


# ---------------------------------------------------------------- zl3esq
if want('zl3esq'):
    w = W('zl3esq', 'The majorant sequence ` | J_n - Gamma ( W ) | + K / n ` tends to ` 0 ` ( ~ zl3qlim shifted by ~ climshft , ~ divcnvshft ).')
    A, Cc = ante_of('zl3esq')
    wc = D(w, A, 'simpl', [], 'W e. CC'); re1 = D(w, A, 'simpr', [], '1 < ( Re ` W )')
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    rwpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    G = '( _G ` W )'
    gc = w.s([w.s([w.s([wc, rwpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % A), w.inst('zrenn')], 'syl', '( %s -> W e. ( CC \\ ( ZZ \\ NN ) ) )' % A), w.inst('gamcl')], 'syl',
             '( %s -> %s e. CC )' % (A, G))
    K1 = '( j + 1 )'
    F = '( j e. NN |-> %s )' % L.JN(K1, K1, 'W')
    ql = w.s([w.s([wc, re1], 'jca', '( %s -> %s )' % (A, L.HW)), w.inst('zl3qlim')], 'syl', '( %s -> %s ~~> %s )' % (A, F, G))
    fex = w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % F)
    sh = w.s([w.s([w.s([w.s([], '1z', '1 e. ZZ'), fex], 'pm3.2i', '( 1 e. ZZ /\\ %s e. _V )' % F), w.inst('climshft')], 'ax-mp', '( ( %s shift 1 ) ~~> %s <-> %s ~~> %s )' % (F, G, F, G))],
             'a1i', '( %s -> ( ( %s shift 1 ) ~~> %s <-> %s ~~> %s ) )' % (A, F, G, F, G))
    fsh = w.s([ql, sh], 'mpbird', '( %s -> ( %s shift 1 ) ~~> %s )' % (A, F, G))
    Z = '( ZZ>= ` 2 )'
    zeq = w.s([], 'eqid', '%s = %s' % (Z, Z)); two = a1(w, A, '2z', '2 e. ZZ')
    Ak = '( %s /\\ k e. %s )' % (A, Z)
    kz = D(w, Ak, 'simpr', [], 'k e. %s' % Z)
    kzz = w.s([kz, w.inst('eluzelz')], 'syl', '( %s -> k e. ZZ )' % Ak)
    kc = D(w, Ak, 'zcnd', [kzz], 'k e. CC')
    k2 = w.s([kz, w.inst('eluzle')], 'syl', '( %s -> 2 <_ k )' % Ak)
    km1 = '( k - 1 )'
    km1n = w.s([w.s([D(w, Ak, 'peano2zm' if False else 'zsubcld', [kzz, a1(w, Ak, '1z', '1 e. ZZ')], '%s e. ZZ' % km1),
                     linarith(w, Ak, [k2], '0 < %s' % km1, closure=Closure(w, Ak, {'k': ('RR', D(w, Ak, 'zred', [kzz], 'k e. RR'))}))], 'jca', '( %s -> ( %s e. ZZ /\\ 0 < %s ) )' % (Ak, km1, km1)),
                w.s([], 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (km1, km1, km1))], 'sylibr', '( %s -> %s e. NN )' % (Ak, km1))
    s1 = w.s([a1(w, Ak, 'ax-1cn', '1 e. CC'), kc, w.s([fex], 'shftval', '( ( 1 e. CC /\\ k e. CC ) -> ( ( %s shift 1 ) ` k ) = ( %s ` ( k - 1 ) ) )' % (F, F))], 'syl2anc',
             '( %s -> ( ( %s shift 1 ) ` k ) = ( %s ` ( k - 1 ) ) )' % (Ak, F, F))
    def jn_m(h, a, b):
        Pa = '( ( 1 - ( x / %s ) ) ^ %s )' % (a, a); Pb = '( ( 1 - ( x / %s ) ) ^ %s )' % (b, b)
        pe = w.s([w.s([w.s([w.s([], 'oveq2', '( %s -> ( x / %s ) = ( x / %s ) )' % (h, a, b))], 'oveq2d', '( %s -> ( 1 - ( x / %s ) ) = ( 1 - ( x / %s ) ) )' % (h, a, b)),
                       w.s([], 'id', '( %s -> %s )' % (h, h))], 'oveq12d', '( %s -> %s = %s )' % (h, Pa, Pb))], 'oveq1d',
                 '( %s -> ( %s x. ( x ^c ( W - 1 ) ) ) = ( %s x. ( x ^c ( W - 1 ) ) ) )' % (h, Pa, Pb))
        I1 = 'S. ( 0 (,) %s ) ( %s x. ( x ^c ( W - 1 ) ) ) _d x' % (b, Pa)
        d1 = w.s([w.s([], 'oveq2', '( %s -> ( 0 (,) %s ) = ( 0 (,) %s ) )' % (h, a, b)), w.inst('itgeq1')], 'syl', '( %s -> %s = %s )' % (h, L.JN(a, a, 'W'), I1))
        d2 = w.s([w.s([pe], 'adantr', '( ( %s /\\ x e. ( 0 (,) %s ) ) -> ( %s x. ( x ^c ( W - 1 ) ) ) = ( %s x. ( x ^c ( W - 1 ) ) ) )' % (h, b, Pa, Pb))],
                 'itgeq2dv', '( %s -> %s = %s )' % (h, I1, L.JN(b, b, 'W')))
        return w.s([d1, d2], 'eqtrd', '( %s -> %s = %s )' % (h, L.JN(a, a, 'W'), L.JN(b, b, 'W')))
    def fvm(C, MAP, bnd, dom, arg, sub_step, val, mem, vex):
        fm = w.s([sub_step, w.s([], 'eqid', '%s = %s' % (MAP, MAP))], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (arg, dom, val, MAP, arg, val))
        return w.s([mem, w.s([w.s([], vex, '%s e. _V' % val)], 'a1i', '( %s -> %s e. _V )' % (C, val)), fm], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (C, MAP, arg, val))
    # F ` ( k - 1 ): substitution j = ( k - 1 ) in JN( ( j + 1 ) , ... )
    hj = 'j = ( k - 1 )'
    jn1 = w.s([w.s([], 'oveq1', '( %s -> ( j + 1 ) = ( ( k - 1 ) + 1 ) )' % hj), jn_m('( j + 1 ) = ( ( k - 1 ) + 1 )', '( j + 1 )', '( ( k - 1 ) + 1 )')], 'syl',
              '( %s -> %s = %s )' % (hj, L.JN(K1, K1, 'W'), L.JN('( ( k - 1 ) + 1 )', '( ( k - 1 ) + 1 )', 'W')))
    val = L.JN('( ( k - 1 ) + 1 )', '( ( k - 1 ) + 1 )', 'W')
    fv = fvm(Ak, F, 'j', 'NN', km1, jn1, val, km1n, 'itgex')
    npc = E(w, Ak, 'npcand', [kc, a1(w, Ak, 'ax-1cn', '1 e. CC')], '( ( k - 1 ) + 1 )', 'k')
    GJ = L.JN('k', 'k', 'W')
    jm = jn_m('( ( k - 1 ) + 1 ) = k', '( ( k - 1 ) + 1 )', 'k')
    fk = w.s([s1, w.s([fv, w.s([npc, jm], 'syl', '( %s -> %s = %s )' % (Ak, val, GJ))], 'eqtrd', '( %s -> ( %s ` ( k - 1 ) ) = %s )' % (Ak, F, GJ))], 'eqtrd',
             '( %s -> ( ( %s shift 1 ) ` k ) = %s )' % (Ak, F, GJ))
    G1 = '( n e. %s |-> %s )' % (Z, L.JN('n', 'n', 'W'))
    ex = lambda M_: w.s([w.s([w.s([w.s([], 'fvex', '%s e. _V' % Z), w.inst('mptexg')], 'ax-mp', '%s e. _V' % M_)], 'idi', '%s e. _V' % M_)], 'a1i', '( %s -> %s e. _V )' % (A, M_))
    hk = 'n = k'
    jnk = jn_m(hk, 'n', 'k')
    g1v = fvm(Ak, G1, 'n', Z, 'k', jnk, GJ, kz, 'itgex')
    ce = w.s([zeq, w.s([w.s([w.s([w.s([], 'ovex', '( %s shift 1 ) e. _V' % F)], 'idi', '( %s shift 1 ) e. _V' % F)], 'a1i', '( %s -> ( %s shift 1 ) e. _V )' % (A, F))], 'idi',
                       '( %s -> ( %s shift 1 ) e. _V )' % (A, F)), ex(G1), two, w.s([fk, g1v], 'eqtr4d', '( %s -> ( ( %s shift 1 ) ` k ) = ( %s ` k ) )' % (Ak, F, G1))], 'climeq',
             '( %s -> ( ( %s shift 1 ) ~~> %s <-> %s ~~> %s ) )' % (A, F, G, G1, G))
    l1 = w.s([fsh, ce], 'mpbid', '( %s -> %s ~~> %s )' % (A, G1, G))
    # J e. CC (for k)
    knn = w.s([w.s([kzz, linarith(w, Ak, [k2], '0 < k', closure=Closure(w, Ak, {'k': ('RR', D(w, Ak, 'zred', [kzz], 'k e. RR'))}))], 'jca', '( %s -> ( k e. ZZ /\\ 0 < k ) )' % Ak),
               w.s([], 'elnnz', '( k e. NN <-> ( k e. ZZ /\\ 0 < k ) )')], 'sylibr', '( %s -> k e. NN )' % Ak)
    krp = D(w, Ak, 'nnrpd', [knn], 'k e. RR+'); kr = D(w, Ak, 'nnred', [knn], 'k e. RR')
    wk = D(w, Ak, 'adantr', [wc], 'W e. CC'); re1k = D(w, Ak, 'adantr', [re1], '1 < ( Re ` W )')
    rwk = D(w, Ak, 'recld', [wk], '( Re ` W ) e. RR')
    wm = D(w, Ak, 'subcld', [wk, a1(w, Ak, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, Ak, [re1k], '0 < ( ( Re ` W ) - 1 )', closure=Closure(w, Ak, {'( Re ` W )': ('RR', rwk)})), re_sub1(w, Ak, wk)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % Ak)
    XW1 = '( x ^c ( W - 1 ) )'
    ck = ccx(w, Ak, '( W - 1 )', wm, wmp, krp, N='k')
    PK = '( ( 1 - ( x / k ) ) ^ k )'
    clk = Closure(w, Ak, {'k': ('RR', kr)}); clk.have('k', 'ne0', D(w, Ak, 'nnne0d', [knn], 'k =/= 0')); clk.have('k', 'NN0', D(w, Ak, 'nnnn0d', [knn], 'k e. NN0'))
    cj = cont(w, Ak, '( 0 [,] k )', '( %s x. %s )' % (PK, XW1), clk, dom_cc(w, Ak, '( 0 [,] k )', kr), special={XW1: ck})
    _, ij = ibl_of(w, Ak, 'k', '( %s x. %s )' % (PK, XW1), cj, kr)
    Akx, _ = dom_x(w, Ak, '( 0 (,) k )', kr)
    jc = w.s([w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PK, XW1))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Akx, PK, XW1)), ij], 'itgcl', '( %s -> %s e. CC )' % (Ak, GJ))
    g1k = w.s([g1v, jc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G1))
    G2 = '( n e. %s |-> ( %s - %s ) )' % (Z, L.JN('n', 'n', 'W'), G)
    g2v = fvm(Ak, G2, 'n', Z, 'k', w.s([jnk], 'oveq1d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (hk, L.JN('n', 'n', 'W'), G, GJ, G)), '( %s - %s )' % (GJ, G), kz, 'ovex')
    l2 = w.s([zeq, two, l1, gc, ex(G2), g1k, w.s([g2v, w.s([g1v], 'oveq1d', '( %s -> ( ( %s ` k ) - %s ) = ( %s - %s ) )' % (Ak, G1, G, GJ, G))], 'eqtr4d',
                                                    '( %s -> ( %s ` k ) = ( ( %s ` k ) - %s ) )' % (Ak, G2, G1, G))], 'climsubc1', '( %s -> %s ~~> ( %s - %s ) )' % (A, G2, G, G))
    G3 = '( n e. %s |-> ( abs ` ( %s - %s ) ) )' % (Z, L.JN('n', 'n', 'W'), G)
    g3v = fvm(Ak, G3, 'n', Z, 'k', w.s([w.s([jnk], 'oveq1d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (hk, L.JN('n', 'n', 'W'), G, GJ, G))], 'fveq2d',
                                       '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (hk, L.JN('n', 'n', 'W'), G, GJ, G)), '( abs ` ( %s - %s ) )' % (GJ, G), kz, 'fvex')
    gkc = D(w, Ak, 'adantr', [gc], '%s e. CC' % G)
    l3 = w.s([zeq, l2, ex(G3), two, w.s([g2v, D(w, Ak, 'subcld', [jc, gkc], '( %s - %s ) e. CC' % (GJ, G))], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G2)),
              w.s([g3v, w.s([g2v], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` ( %s - %s ) ) )' % (Ak, G2, GJ, G))], 'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, G3, G2))],
             'climabs', '( %s -> %s ~~> ( abs ` ( %s - %s ) ) )' % (A, G3, G, G))
    KKs = L.KK
    rw0 = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    kar = kconst(w, A, '( ( Re ` W ) + 1 )', D(w, A, 'readdcld', [rw0, a1(w, A, '1re', '1 e. RR')], '( ( Re ` W ) + 1 ) e. RR'),
                 linarith(w, A, [re1], '0 <_ ( ( Re ` W ) + 1 )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw0)})))
    kbr = kconst(w, A, '( ( Re ` W ) - 1 )', D(w, A, 'resubcld', [rw0, a1(w, A, '1re', '1 e. RR')], '( ( Re ` W ) - 1 ) e. RR'),
                 linarith(w, A, [re1], '0 <_ ( ( Re ` W ) - 1 )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw0)})))
    kkc = D(w, A, 'addcld', [D(w, A, 'mulcld', [a1(w, A, '2cn', '2 e. CC'), D(w, A, 'rpcnd', [kar], '%s e. CC' % L.KA)], '( 2 x. %s ) e. CC' % L.KA),
                             D(w, A, 'mulcld', [a1(w, A, '4cn', '4 e. CC'), D(w, A, 'rpcnd', [kbr], '%s e. CC' % L.KB)], '( 4 x. %s ) e. CC' % L.KB)], '%s e. CC' % KKs)
    G4 = '( n e. %s |-> ( %s / n ) )' % (Z, KKs)
    g4v, _ = mptv(w, Ak, 'n', Z, '( %s / n )' % KKs, 'k', kz)
    l4 = w.s([zeq, two, kkc, a1(w, A, '0z', '0 e. ZZ'), ex(G4),
              w.s([g4v, E(w, Ak, 'oveq2d', [w.s([E(w, Ak, 'addridd', [kc], '( k + 0 )', 'k')], 'eqcomd', '( %s -> k = ( k + 0 ) )' % Ak)], '( %s / k )' % KKs, '( %s / ( k + 0 ) )' % KKs)],
                  'eqtrd', '( %s -> ( %s ` k ) = ( %s / ( k + 0 ) ) )' % (Ak, G4, KKs))], 'divcnvshft', '( %s -> %s ~~> 0 )' % (A, G4))
    G5 = '( n e. %s |-> ( ( abs ` ( %s - %s ) ) + ( %s / n ) ) )' % (Z, L.JN('n', 'n', 'W'), G, KKs)
    g5v = fvm(Ak, G5, 'n', Z, 'k', w.s([w.s([w.s([jnk], 'oveq1d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (hk, L.JN('n', 'n', 'W'), G, GJ, G))], 'fveq2d',
                                              '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (hk, L.JN('n', 'n', 'W'), G, GJ, G)),
                                          w.s([], 'oveq2', '( %s -> ( %s / n ) = ( %s / k ) )' % (hk, KKs, KKs))], 'oveq12d',
                                         '( %s -> ( ( abs ` ( %s - %s ) ) + ( %s / n ) ) = ( ( abs ` ( %s - %s ) ) + ( %s / k ) ) )' % (hk, L.JN('n', 'n', 'W'), G, KKs, GJ, G, KKs)),
              '( ( abs ` ( %s - %s ) ) + ( %s / k ) )' % (GJ, G, KKs), kz, 'ovex')
    g3c = w.s([g3v, D(w, Ak, 'recnd', [D(w, Ak, 'abscld', [D(w, Ak, 'subcld', [jc, gkc], '( %s - %s ) e. CC' % (GJ, G))], '( abs ` ( %s - %s ) ) e. RR' % (GJ, G))], '( abs ` ( %s - %s ) ) e. CC' % (GJ, G))],
              'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G3))
    g4c = w.s([g4v, D(w, Ak, 'divcld', [D(w, Ak, 'adantr', [kkc], '%s e. CC' % KKs), kc, D(w, Ak, 'nnne0d', [knn], 'k =/= 0')], '( %s / k ) e. CC' % KKs)], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G4))
    l5 = w.s([zeq, two, l3, ex(G5), l4, g3c, g4c, w.s([g5v, w.s([g3v, g4v], 'oveq12d', '( %s -> ( ( %s ` k ) + ( %s ` k ) ) = ( ( abs ` ( %s - %s ) ) + ( %s / k ) ) )' % (Ak, G3, G4, GJ, G, KKs))],
                                                          'eqtr4d', '( %s -> ( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) ) )' % (Ak, G5, G3, G4))],
             'climadd', '( %s -> %s ~~> ( ( abs ` ( %s - %s ) ) + 0 ) )' % (A, G5, G, G))
    zz = chain(w, A, ['( ( abs ` ( %s - %s ) ) + 0 )' % (G, G), '( ( abs ` 0 ) + 0 )', '( 0 + 0 )', '0'],
               [E(w, A, 'oveq1d', [E(w, A, 'fveq2d', [E(w, A, 'subidd', [gc], '( %s - %s )' % (G, G), '0')], '( abs ` ( %s - %s ) )' % (G, G), '( abs ` 0 )')], '( ( abs ` ( %s - %s ) ) + 0 )' % (G, G), '( ( abs ` 0 ) + 0 )'),
                E(w, A, 'oveq1d', [w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % A)], '( ( abs ` 0 ) + 0 )', '( 0 + 0 )'),
                w.s([w.s([], '00id', '( 0 + 0 ) = 0')], 'a1i', '( %s -> ( 0 + 0 ) = 0 )' % A)])
    q = w.s([l5, zz], 'breqtrd', 'x')
    finish(w, q, 'zl3esq')
    go(w)


def wfacts(w, C, wc, re1):
    rw = D(w, C, 'recld', [wc], '( Re ` W ) e. RR')
    wm = D(w, C, 'subcld', [wc, a1(w, C, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    wmp = w.s([linarith(w, C, [re1], '0 < ( ( Re ` W ) - 1 )', closure=Closure(w, C, {'( Re ` W )': ('RR', rw)})), re_sub1(w, C, wc)], 'breqtrrd', '( %s -> 0 < ( Re ` ( W - 1 ) ) )' % C)
    return rw, wm, wmp


# ---------------------------------------------------------------- zl3icc, zl3jcc
if want('zl3icc'):
    w = W('zl3icc', 'The truncated Euler integral is a complex number.')
    C, Cc = ante_of('zl3icc')
    wc = D(w, C, 'simpll', [], 'W e. CC'); re1 = D(w, C, 'simplr', [], '1 < ( Re ` W )'); trp = D(w, C, 'simpr', [], 'T e. RR+')
    tr = D(w, C, 'rpred', [trp], 'T e. RR')
    rw, wm, wmp = wfacts(w, C, wc, re1)
    XW1 = '( x ^c ( W - 1 ) )'
    f = '( ( exp ` -u x ) x. %s )' % XW1
    cf = cont(w, C, '( 0 [,] T )', f, Closure(w, C, {}), dom_cc(w, C, '( 0 [,] T )', tr), special={XW1: ccx(w, C, '( W - 1 )', wm, wmp, trp, N='T')})
    _, ib = ibl_of(w, C, 'T', f, cf, tr)
    Cx, xc = dom_x(w, C, '( 0 (,) T )', tr)
    q = w.s([Closure(w, Cx, {'x': ('CC', xc), 'W': ('CC', D(w, Cx, 'adantr', [wc], 'W e. CC'))}).mem(f, 'CC'), ib], 'itgcl', 'x')
    finish(w, q, 'zl3icc')
    go(w)

if want('zl3jcc'):
    w = W('zl3jcc', 'The approximant ` S. ( 0 , N ) ( 1 - x / N ) ^ N x ^ ( W - 1 ) dx ` is a complex number.')
    C, Cc = ante_of('zl3jcc')
    wc = D(w, C, 'simpll', [], 'W e. CC'); re1 = D(w, C, 'simplr', [], '1 < ( Re ` W )'); nn = D(w, C, 'simpr', [], 'N e. NN')
    nr = D(w, C, 'nnred', [nn], 'N e. RR'); nrp = D(w, C, 'nnrpd', [nn], 'N e. RR+')
    rw, wm, wmp = wfacts(w, C, wc, re1)
    XW1 = '( x ^c ( W - 1 ) )'; PN = '( ( 1 - ( x / N ) ) ^ N )'
    cl = Closure(w, C, {'N': ('RR', nr)}); cl.have('N', 'ne0', D(w, C, 'nnne0d', [nn], 'N =/= 0')); cl.have('N', 'NN0', D(w, C, 'nnnn0d', [nn], 'N e. NN0'))
    cf = cont(w, C, '( 0 [,] N )', '( %s x. %s )' % (PN, XW1), cl, dom_cc(w, C, '( 0 [,] N )', nr), special={XW1: ccx(w, C, '( W - 1 )', wm, wmp, nrp)})
    _, ib = ibl_of(w, C, 'N', '( %s x. %s )' % (PN, XW1), cf, nr)
    Cx, xc = dom_x(w, C, '( 0 (,) N )', nr)
    q = w.s([w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (PN, XW1))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (Cx, PN, XW1)), ib], 'itgcl', 'x')
    finish(w, q, 'zl3jcc')
    go(w)


def jnm(w, h, a, b):
    """( h -> JN(a,a,W) = JN(b,b,W) ) with h = ( a = b )"""
    Pa = '( ( 1 - ( x / %s ) ) ^ %s )' % (a, a); Pb = '( ( 1 - ( x / %s ) ) ^ %s )' % (b, b)
    pe = w.s([w.s([w.s([w.s([], 'oveq2', '( %s -> ( x / %s ) = ( x / %s ) )' % (h, a, b))], 'oveq2d', '( %s -> ( 1 - ( x / %s ) ) = ( 1 - ( x / %s ) ) )' % (h, a, b)),
                   w.s([], 'id', '( %s -> %s )' % (h, h))], 'oveq12d', '( %s -> %s = %s )' % (h, Pa, Pb))], 'oveq1d',
             '( %s -> ( %s x. ( x ^c ( W - 1 ) ) ) = ( %s x. ( x ^c ( W - 1 ) ) ) )' % (h, Pa, Pb))
    I1 = 'S. ( 0 (,) %s ) ( %s x. ( x ^c ( W - 1 ) ) ) _d x' % (b, Pa)
    d1 = w.s([w.s([], 'oveq2', '( %s -> ( 0 (,) %s ) = ( 0 (,) %s ) )' % (h, a, b)), w.inst('itgeq1')], 'syl', '( %s -> %s = %s )' % (h, L.JN(a, a, 'W'), I1))
    d2 = w.s([w.s([pe], 'adantr', '( ( %s /\\ x e. ( 0 (,) %s ) ) -> ( %s x. ( x ^c ( W - 1 ) ) ) = ( %s x. ( x ^c ( W - 1 ) ) ) )' % (h, b, Pa, Pb))],
             'itgeq2dv', '( %s -> %s = %s )' % (h, I1, L.JN(b, b, 'W')))
    return w.s([d1, d2], 'eqtrd', '( %s -> %s = %s )' % (h, L.JN(a, a, 'W'), L.JN(b, b, 'W')))


# ---------------------------------------------------------------- zl3eu1
if want('zl3eu1'):
    w = W('zl3eu1', "Euler's integral: ` S. ( 0 , t ) e ^ -x x ^ ( W - 1 ) dx -> Gamma ( W ) ` as ` t -> +oo ` , for ` 1 < Re W ` "
          '( ~ zl3eub squeezed by ~ zl3esq through ~ climrlim2 , ~ rlimsqzlem ).')
    A, Cc = ante_of('zl3eu1')
    wc = D(w, A, 'simpl', [], 'W e. CC'); re1 = D(w, A, 'simpr', [], '1 < ( Re ` W )')
    G = '( _G ` W )'
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    rwpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    gc = w.s([w.s([w.s([wc, rwpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % A), w.inst('zrenn')], 'syl', '( %s -> W e. ( CC \\ ( ZZ \\ NN ) ) )' % A), w.inst('gamcl')], 'syl',
             '( %s -> %s e. CC )' % (A, G))
    KKs = L.KK
    FT = '( |_ ` t )'
    Bn = '( ( abs ` ( %s - %s ) ) + ( %s / n ) )' % (L.JN('n', 'n', 'W'), G, KKs)
    Bt = '( ( abs ` ( %s - %s ) ) + ( %s / %s ) )' % (L.JN(FT, FT, 'W'), G, KKs, FT)
    h = 'n = %s' % FT
    jn = jnm(w, h, 'n', FT)
    sub = w.s([w.s([w.s([jn], 'oveq1d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (h, L.JN('n', 'n', 'W'), G, L.JN(FT, FT, 'W'), G))], 'fveq2d',
                   '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (h, L.JN('n', 'n', 'W'), G, L.JN(FT, FT, 'W'), G)),
               w.s([], 'oveq2', '( %s -> ( %s / n ) = ( %s / %s ) )' % (h, KKs, KKs, FT))], 'oveq12d', '( %s -> %s = %s )' % (h, Bn, Bt))
    A2 = '( 2 [,) +oo )'
    a2r = w.s([a1(w, A, '2re', '2 e. RR'), a1(w, A, 'pnfxr', '+oo e. RR*'), w.inst('icossre')], 'syl2anc', '( %s -> %s C_ RR )' % (A, A2))
    Z = '( ZZ>= ` 2 )'
    esq = w.s([w.s([wc, re1], 'jca', '( %s -> %s )' % (A, L.HW)), w.inst('zl3esq')], 'syl', '( %s -> ( n e. %s |-> %s ) ~~> 0 )' % (A, Z, Bn))
    HWs = w.s([wc, re1], 'jca', '( %s -> %s )' % (A, L.HW))
    rw0 = rw
    kar = kconst(w, A, '( ( Re ` W ) + 1 )', D(w, A, 'readdcld', [rw0, a1(w, A, '1re', '1 e. RR')], '( ( Re ` W ) + 1 ) e. RR'),
                 linarith(w, A, [re1], '0 <_ ( ( Re ` W ) + 1 )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw0)})))
    kbr = kconst(w, A, '( ( Re ` W ) - 1 )', D(w, A, 'resubcld', [rw0, a1(w, A, '1re', '1 e. RR')], '( ( Re ` W ) - 1 ) e. RR'),
                 linarith(w, A, [re1], '0 <_ ( ( Re ` W ) - 1 )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw0)})))
    kkr = D(w, A, 'readdcld', [D(w, A, 'remulcld', [a1(w, A, '2re', '2 e. RR'), D(w, A, 'rpred', [kar], '%s e. RR' % L.KA)], '( 2 x. %s ) e. RR' % L.KA),
                               D(w, A, 'remulcld', [a1(w, A, '4re', '4 e. RR'), D(w, A, 'rpred', [kbr], '%s e. RR' % L.KB)], '( 4 x. %s ) e. RR' % L.KB)], '%s e. RR' % KKs)
    kk0 = D(w, A, 'addge0d' if False else 'ltled', [a1(w, A, '0re', '0 e. RR'), kkr,
                                                  linarith(w, A, [D(w, A, 'rpgt0d', [kar], '0 < %s' % L.KA), D(w, A, 'rpgt0d', [kbr], '0 < %s' % L.KB)], '0 < %s' % KKs,
                                                           closure=Closure(w, A, {L.KA: ('RR', D(w, A, 'rpred', [kar], '%s e. RR' % L.KA)), L.KB: ('RR', D(w, A, 'rpred', [kbr], '%s e. RR' % L.KB))}))],
             '0 <_ %s' % KKs)
    def bval(C, m, mnn):
        """( C -> B(m) e. RR ) and ( C -> 0 <_ B(m) ) for m e. NN"""
        jc = w.s([w.s([D(w, C, 'adantr', [HWs], L.HW), mnn], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (C, L.HW, m)), w.inst('zl3jcc')], 'syl', '( %s -> %s e. CC )' % (C, L.JN(m, m, 'W')))
        ab = D(w, C, 'abscld', [D(w, C, 'subcld', [jc, D(w, C, 'adantr', [gc], '%s e. CC' % G)], '( %s - %s ) e. CC' % (L.JN(m, m, 'W'), G))], '( abs ` ( %s - %s ) ) e. RR' % (L.JN(m, m, 'W'), G))
        ab0 = D(w, C, 'absge0d', [D(w, C, 'subcld', [jc, D(w, C, 'adantr', [gc], '%s e. CC' % G)], '( %s - %s ) e. CC' % (L.JN(m, m, 'W'), G))], '0 <_ ( abs ` ( %s - %s ) )' % (L.JN(m, m, 'W'), G))
        mrp = D(w, C, 'nnrpd', [mnn], '%s e. RR+' % m)
        kd = D(w, C, 'rerpdivcld', [D(w, C, 'adantr', [kkr], '%s e. RR' % KKs), mrp], '( %s / %s ) e. RR' % (KKs, m))
        kd0 = D(w, C, 'divge0d', [D(w, C, 'adantr', [kkr], '%s e. RR' % KKs), mrp, D(w, C, 'adantr', [kk0], '0 <_ %s' % KKs)], '0 <_ ( %s / %s )' % (KKs, m))
        BB = '( ( abs ` ( %s - %s ) ) + ( %s / %s ) )' % (L.JN(m, m, 'W'), G, KKs, m)
        return D(w, C, 'readdcld', [ab, kd], '%s e. RR' % BB), D(w, C, 'addge0d', [ab, kd, ab0, kd0], '0 <_ %s' % BB)
    An = '( %s /\\ n e. %s )' % (A, Z)
    nz = D(w, An, 'simpr', [], 'n e. %s' % Z)
    nzz = w.s([nz, w.inst('eluzelz')], 'syl', '( %s -> n e. ZZ )' % An)
    n2 = w.s([nz, w.inst('eluzle')], 'syl', '( %s -> 2 <_ n )' % An)
    nnn = w.s([w.s([nzz, linarith(w, An, [n2], '0 < n', closure=Closure(w, An, {'n': ('RR', D(w, An, 'zred', [nzz], 'n e. RR'))}))], 'jca', '( %s -> ( n e. ZZ /\\ 0 < n ) )' % An),
               w.s([], 'elnnz', '( n e. NN <-> ( n e. ZZ /\\ 0 < n ) )')], 'sylibr', '( %s -> n e. NN )' % An)
    bnr, _ = bval(An, 'n', nnn)
    At = '( %s /\\ t e. %s )' % (A, A2)
    tin = D(w, At, 'simpr', [], 't e. %s' % A2)
    tel = w.s([tin, w.s([a1(w, At, '2re', '2 e. RR'), w.inst('elicopnf')], 'syl', '( %s -> ( t e. %s <-> ( t e. RR /\\ 2 <_ t ) ) )' % (At, A2))], 'mpbid', '( %s -> ( t e. RR /\\ 2 <_ t ) )' % At)
    tr = D(w, At, 'simpld', [tel], 't e. RR'); t2 = D(w, At, 'simprd', [tel], '2 <_ t')
    cr2 = w.s([zeq_ := w.s([], 'eqid', '%s = %s' % (Z, Z)), sub, a2r, a1(w, A, '2z', '2 e. ZZ'), esq, D(w, An, 'recnd', [bnr], '%s e. CC' % Bn), t2], 'climrlim2',
              '( %s -> ( t e. %s |-> %s ) ~~>r 0 )' % (A, A2, Bt))
    # floor facts at t
    ftz = D(w, At, 'flcld', [tr], '%s e. ZZ' % FT)
    ft2 = w.s([t2, w.s([tr, a1(w, At, '2z', '2 e. ZZ'), w.inst('flge')], 'syl2anc', '( %s -> ( 2 <_ t <-> 2 <_ %s ) )' % (At, FT))], 'mpbid', '( %s -> 2 <_ %s )' % (At, FT))
    ftn = w.s([w.s([ftz, linarith(w, At, [ft2], '0 < %s' % FT, closure=Closure(w, At, {FT: ('RR', D(w, At, 'zred', [ftz], '%s e. RR' % FT))}))], 'jca', '( %s -> ( %s e. ZZ /\\ 0 < %s ) )' % (At, FT, FT)),
               w.s([], 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (FT, FT, FT))], 'sylibr', '( %s -> %s e. NN )' % (At, FT))
    btr, bt0 = bval(At, FT, ftn)
    trp = D(w, At, 'elrpd', [tr, linarith(w, At, [t2], '0 < t', closure=Closure(w, At, {'t': ('RR', tr)}))], 't e. RR+')
    eic = w.s([w.s([D(w, At, 'adantr', [HWs], L.HW), trp], 'jca', '( %s -> ( %s /\\ t e. RR+ ) )' % (At, L.HW)), w.inst('zl3icc')], 'syl', '( %s -> %s e. CC )' % (At, L.EIF('0', 't')))
    Au = '( %s /\\ ( t e. %s /\\ 2 <_ t ) )' % (A, A2)
    at_ = w.s([w.s([D(w, Au, 'simpl', [], A), D(w, Au, 'simprl', [], 't e. %s' % A2)], 'jca', '( %s -> %s )' % (Au, At))], 'idi', '( %s -> %s )' % (Au, At))
    eub = w.s([w.s([w.s([D(w, At, 'adantr', [HWs], L.HW), w.s([tr, t2], 'jca', '( %s -> ( t e. RR /\\ 2 <_ t ) )' % At)], 'jca', '( %s -> ( %s /\\ ( t e. RR /\\ 2 <_ t ) ) )' % (At, L.HW)),
                    w.inst('zl3eub')], 'syl', '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (At, L.EIF('0', 't'), G, Bt))], 'idi', '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (At, L.EIF('0', 't'), G, Bt))
    b0 = chain(w, At, ['( abs ` ( %s - 0 ) )' % Bt, '( abs ` %s )' % Bt, Bt],
               [E(w, At, 'fveq2d', [E(w, At, 'subid1d', [D(w, At, 'recnd', [btr], '%s e. CC' % Bt)], '( %s - 0 )' % Bt, Bt)], '( abs ` ( %s - 0 ) )' % Bt, '( abs ` %s )' % Bt),
                E(w, At, 'absidd', [btr, bt0], '( abs ` %s )' % Bt, Bt)])
    sq4 = w.s([w.s([eub, b0], 'breqtrrd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( %s - 0 ) ) )' % (At, L.EIF('0', 't'), G, Bt)), at_], 'idi', 'x') if False else None
    sq4 = w.s([at_, w.s([eub, b0], 'breqtrrd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( %s - 0 ) ) )' % (At, L.EIF('0', 't'), G, Bt))], 'syl',
              '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( %s - 0 ) ) )' % (Au, L.EIF('0', 't'), G, Bt))
    MA2 = '( t e. %s |-> %s )' % (A2, L.EIF('0', 't'))
    sqz = w.s([a1(w, A, '2re', '2 e. RR'), gc, cr2, D(w, At, 'recnd', [btr], '%s e. CC' % Bt), eic, sq4], 'rlimsqzlem', '( %s -> %s ~~>r %s )' % (A, MA2, G))
    # un-restrict
    Ar = '( %s /\\ t e. RR+ )' % A
    eir = w.s([w.s([D(w, Ar, 'adantr', [HWs], L.HW), D(w, Ar, 'simpr', [], 't e. RR+')], 'jca', '( %s -> ( %s /\\ t e. RR+ ) )' % (Ar, L.HW)), w.inst('zl3icc')], 'syl', '( %s -> %s e. CC )' % (Ar, L.EIF('0', 't')))
    EI1 = L.EI1
    ff = w.s([eir, w.s([], 'eqid', '%s = %s' % (EI1, EI1))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A, EI1))
    rb = w.s([ff, a1(w, A, 'rpssre', 'RR+ C_ RR'), a1(w, A, '2re', '2 e. RR')], 'rlimresb', '( %s -> ( %s ~~>r %s <-> ( %s |` %s ) ~~>r %s ) )' % (A, EI1, G, EI1, A2, G))
    Aw = '( %s /\\ t e. %s )' % (A, A2)
    ssr = w.s([w.s([trp], 'ex', '( %s -> ( t e. %s -> t e. RR+ ) )' % (A, A2))], 'ssrdv', '( %s -> %s C_ RR+ )' % (A, A2))
    rm = w.s([ssr, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A, EI1, A2, MA2))
    q = w.s([w.s([sqz, w.s([rm], 'breq1d', '( %s -> ( ( %s |` %s ) ~~>r %s <-> %s ~~>r %s ) )' % (A, EI1, A2, G, MA2, G))], 'mpbird', '( %s -> ( %s |` %s ) ~~>r %s )' % (A, EI1, A2, G)), rb], 'mpbird', 'x')
    finish(w, q, 'zl3eu1')
    go(w)


# ---------------------------------------------------------------- zl3esc
if want('zl3esc'):
    w = W('zl3esc', 'Scaling in the Euler integral: ` S. ( 0 , T ) e ^ ( - L x ) x ^ ( W - 1 ) dx = L ^ -W S. ( 0 , L T ) e ^ -x x ^ ( W - 1 ) dx ` '
          '( ~ z6aff on both sides).')
    C, Cc = ante_of('zl3esc')
    wc = D(w, C, 'simpll', [], 'W e. CC'); re1 = D(w, C, 'simplr', [], '1 < ( Re ` W )')
    lrp = D(w, C, 'simprl', [], 'L e. RR+'); trp = D(w, C, 'simprr', [], 'T e. RR+')
    LT = '( L x. T )'
    ltrp = D(w, C, 'rpmulcld', [lrp, trp], '%s e. RR+' % LT)
    tr = D(w, C, 'rpred', [trp], 'T e. RR'); ltr = D(w, C, 'rpred', [ltrp], '%s e. RR' % LT)
    lc = D(w, C, 'rpcnd', [lrp], 'L e. CC'); ln0 = D(w, C, 'rpne0d', [lrp], 'L =/= 0')
    rw, wm, wmp = wfacts(w, C, wc, re1)
    XW1 = '( x ^c ( W - 1 ) )'
    g = '( ( exp ` -u ( L x. x ) ) x. %s )' % XW1; f = '( ( exp ` -u x ) x. %s )' % XW1
    K = '( L ^c -u W )'
    kc = D(w, C, 'cxpcld', [lc, D(w, C, 'negcld', [wc], '-u W e. CC')], '%s e. CC' % K)
    cl = Closure(w, C, {'L': ('RR', D(w, C, 'rpred', [lrp], 'L e. RR')), K: ('CC', kc)})
    H1 = '( x e. ( 0 [,] T ) |-> %s )' % g; H3 = '( x e. ( 0 [,] %s ) |-> ( %s x. %s ) )' % (LT, K, f)
    c1 = cont(w, C, '( 0 [,] T )', g, cl, dom_cc(w, C, '( 0 [,] T )', tr), special={XW1: ccx(w, C, '( W - 1 )', wm, wmp, trp, N='T')})
    c3x = ccx(w, C, '( W - 1 )', wm, wmp, ltrp, N=LT)
    c3 = cont(w, C, '( 0 [,] %s )' % LT, '( %s x. %s )' % (K, f), cl, dom_cc(w, C, '( 0 [,] %s )' % LT, ltr), special={XW1: c3x})
    cf = cont(w, C, '( 0 [,] %s )' % LT, f, cl, dom_cc(w, C, '( 0 [,] %s )' % LT, ltr), special={XW1: c3x})
    _, ibf = ibl_of(w, C, LT, f, cf, ltr)
    z0 = a1(w, C, '0re', '0 e. RR')
    za1 = w.s([w.s([w.s([w.s([z0, tr], 'jca', '( %s -> ( 0 e. RR /\\ T e. RR ) )' % C), D(w, C, 'rpgt0d', [trp], '0 < T')], 'jca', '( %s -> ( ( 0 e. RR /\\ T e. RR ) /\\ 0 < T ) )' % C), c1], 'jca',
                   '( %s -> ( ( ( 0 e. RR /\\ T e. RR ) /\\ 0 < T ) /\\ %s e. ( ( 0 [,] T ) -cn-> CC ) ) )' % (C, H1)), w.inst('z6aff')], 'syl',
              '( %s -> S. ( 0 (,) T ) ( %s ` u ) _d u = S. ( 0 (,) 1 ) ( ( %s ` ( 0 + ( t x. ( T - 0 ) ) ) ) x. ( T - 0 ) ) _d t )' % (C, H1, H1))
    za3 = w.s([w.s([w.s([w.s([z0, ltr], 'jca', '( %s -> ( 0 e. RR /\\ %s e. RR ) )' % (C, LT)), D(w, C, 'rpgt0d', [ltrp], '0 < %s' % LT)], 'jca', '( %s -> ( ( 0 e. RR /\\ %s e. RR ) /\\ 0 < %s ) )' % (C, LT, LT)), c3], 'jca',
                   '( %s -> ( ( ( 0 e. RR /\\ %s e. RR ) /\\ 0 < %s ) /\\ %s e. ( ( 0 [,] %s ) -cn-> CC ) ) )' % (C, LT, LT, H3, LT)), w.inst('z6aff')], 'syl',
              '( %s -> S. ( 0 (,) %s ) ( %s ` u ) _d u = S. ( 0 (,) 1 ) ( ( %s ` ( 0 + ( t x. ( %s - 0 ) ) ) ) x. ( %s - 0 ) ) _d t )' % (C, LT, H3, H3, LT, LT))
    def lhs_conv(B, H, body, br):
        """( C -> S. ( 0 (,) B ) body _d x = S. ( 0 (,) B ) ( H ` u ) _d u )"""
        bu = ' '.join('u' if t_ == 'x' else t_ for t_ in body.split(' '))
        cb = w.s([w.congr(body, {'x': 'u'}, 'x = u', {'x': w.s([], 'id', '( x = u -> x = u )')})[0]], 'cbvitgv', 'S. ( 0 (,) %s ) %s _d x = S. ( 0 (,) %s ) %s _d u' % (B, body, B, bu))
        Cu = '( %s /\\ u e. ( 0 (,) %s ) )' % (C, B)
        um = w.s([w.s([w.s([], 'ioossicc', '( 0 (,) %s ) C_ ( 0 [,] %s )' % (B, B))], 'a1i', '( %s -> ( 0 (,) %s ) C_ ( 0 [,] %s ) )' % (Cu, B, B)), D(w, Cu, 'simpr', [], 'u e. ( 0 (,) %s )' % B)],
                 'sseldd', '( %s -> u e. ( 0 [,] %s ) )' % (Cu, B))
        fv, val = mptv(w, Cu, 'x', '( 0 [,] %s )' % B, body, 'u', um)
        assert val == bu, (val, bu)
        ie = w.s([w.s([fv], 'eqcomd', '( %s -> %s = ( %s ` u ) )' % (Cu, bu, H))], 'itgeq2dv', '( %s -> S. ( 0 (,) %s ) %s _d u = S. ( 0 (,) %s ) ( %s ` u ) _d u )' % (C, B, bu, B, H))
        return w.s([w.s([cb], 'a1i', '( %s -> S. ( 0 (,) %s ) %s _d x = S. ( 0 (,) %s ) %s _d u )' % (C, B, body, B, bu)), ie], 'eqtrd',
                   '( %s -> S. ( 0 (,) %s ) %s _d x = S. ( 0 (,) %s ) ( %s ` u ) _d u )' % (C, B, body, B, H))
    l1 = lhs_conv('T', H1, g, tr)
    l3 = lhs_conv(LT, H3, '( %s x. %s )' % (K, f), ltr)
    im = w.s([kc, w.s([w.s([], 'ovex', '%s e. _V' % f)], 'a1i', '( ( %s /\\ x e. ( 0 (,) %s ) ) -> %s e. _V )' % (C, LT, f)), ibf], 'itgmulc2',
             '( %s -> ( %s x. %s ) = S. ( 0 (,) %s ) ( %s x. %s ) _d x )' % (C, K, L.EIF('0', LT), LT, K, f))
    # pointwise on ( 0 (,) 1 )
    Ct = '( %s /\\ t e. ( 0 (,) 1 ) )' % C
    tin = D(w, Ct, 'simpr', [], 't e. ( 0 (,) 1 )')
    trr = w.s([tin, w.inst('elioore')], 'syl', '( %s -> t e. RR )' % Ct)
    t01 = w.s([tin, w.inst('eliooord')], 'syl', '( %s -> ( 0 < t /\\ t < 1 ) )' % Ct)
    tp = D(w, Ct, 'simpld', [t01], '0 < t'); tl1 = D(w, Ct, 'simprd', [t01], 't < 1')
    trp_ = D(w, Ct, 'elrpd', [trr, tp], 't e. RR+')
    Tt = D(w, Ct, 'adantr', [trp], 'T e. RR+'); Lt = D(w, Ct, 'adantr', [lrp], 'L e. RR+'); LTt = D(w, Ct, 'adantr', [ltrp], '%s e. RR+' % LT)
    S_ = '( t x. T )'
    srp = D(w, Ct, 'rpmulcld', [trp_, Tt], '%s e. RR+' % S_)
    a_t = '( 0 + ( t x. ( T - 0 ) ) )'; b_t = '( 0 + ( t x. ( %s - 0 ) ) )' % LT
    tc = D(w, Ct, 'recnd', [trr], 't e. CC'); Tc = D(w, Ct, 'rpcnd', [Tt], 'T e. CC'); Lc = D(w, Ct, 'rpcnd', [Lt], 'L e. CC'); LTc = D(w, Ct, 'rpcnd', [LTt], '%s e. CC' % LT)
    ea = chain(w, Ct, [a_t, '( 0 + ( t x. T ) )', S_],
               [E(w, Ct, 'oveq2d', [E(w, Ct, 'oveq2d', [E(w, Ct, 'subid1d', [Tc], '( T - 0 )', 'T')], '( t x. ( T - 0 ) )', S_)], a_t, '( 0 + ( t x. T ) )'),
                E(w, Ct, 'addlidd', [D(w, Ct, 'mulcld', [tc, Tc], '%s e. CC' % S_)], '( 0 + ( t x. T ) )', S_)])
    LS = '( L x. %s )' % S_
    eb = chain(w, Ct, [b_t, '( 0 + ( t x. %s ) )' % LT, '( t x. %s )' % LT, LS],
               [E(w, Ct, 'oveq2d', [E(w, Ct, 'oveq2d', [E(w, Ct, 'subid1d', [LTc], '( %s - 0 )' % LT, LT)], '( t x. ( %s - 0 ) )' % LT, '( t x. %s )' % LT)], b_t, '( 0 + ( t x. %s ) )' % LT),
                E(w, Ct, 'addlidd', [D(w, Ct, 'mulcld', [tc, LTc], '( t x. %s ) e. CC' % LT)], '( 0 + ( t x. %s ) )' % LT, '( t x. %s )' % LT),
                E(w, Ct, 'mul12d', [tc, Lc, Tc], '( t x. %s )' % LT, LS)])
    # memberships
    sl = D(w, Ct, 'ltled', [D(w, Ct, 'rpred', [srp], '%s e. RR' % S_), D(w, Ct, 'rpred', [Tt], 'T e. RR'),
                            w.s([w.s([tl1, D(w, Ct, 'ltmul1d', [trr, a1(w, Ct, '1re', '1 e. RR'), Tt], '( t < 1 <-> ( t x. T ) < ( 1 x. T ) )')], 'mpbid', '( %s -> ( t x. T ) < ( 1 x. T ) )' % Ct),
                                 E(w, Ct, 'mullidd', [Tc], '( 1 x. T )', 'T')], 'breqtrd', '( %s -> ( t x. T ) < T )' % Ct)], '%s <_ T' % S_)
    def icc_in(v, vr, v0, vle, B, br_):
        return w.s([w.s([vr, v0, vle], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ %s ) )' % (Ct, v, v, v, B)),
                    w.s([a1(w, Ct, '0re', '0 e. RR'), br_, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( 0 [,] %s ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ %s ) ) )' % (Ct, v, B, v, v, v, B))],
                   'mpbird', '( %s -> %s e. ( 0 [,] %s ) )' % (Ct, v, B))
    sm = icc_in(S_, D(w, Ct, 'rpred', [srp], '%s e. RR' % S_), D(w, Ct, 'rpge0d', [srp], '0 <_ %s' % S_), sl, 'T', D(w, Ct, 'rpred', [Tt], 'T e. RR'))
    lsrp = D(w, Ct, 'rpmulcld', [Lt, srp], '%s e. RR+' % LS)
    lsl = D(w, Ct, 'lemul2ad', [D(w, Ct, 'rpred', [srp], '%s e. RR' % S_), D(w, Ct, 'rpred', [Tt], 'T e. RR'), D(w, Ct, 'rpred', [Lt], 'L e. RR'), D(w, Ct, 'rpge0d', [Lt], '0 <_ L'), sl],
            '%s <_ %s' % (LS, LT))
    lsm = icc_in(LS, D(w, Ct, 'rpred', [lsrp], '%s e. RR' % LS), D(w, Ct, 'rpge0d', [lsrp], '0 <_ %s' % LS), lsl, LT, D(w, Ct, 'rpred', [LTt], '%s e. RR' % LT))
    am = w.s([ea, sm], 'eqeltrd', '( %s -> %s e. ( 0 [,] T ) )' % (Ct, a_t))
    bm = w.s([eb, lsm], 'eqeltrd', '( %s -> %s e. ( 0 [,] %s ) )' % (Ct, b_t, LT))
    h1v, v1 = mptv(w, Ct, 'x', '( 0 [,] T )', g, a_t, am)
    h3v, v3 = mptv(w, Ct, 'x', '( 0 [,] %s )' % LT, '( %s x. %s )' % (K, f), b_t, bm)
    gs = '( ( exp ` -u ( L x. %s ) ) x. ( %s ^c ( W - 1 ) ) )' % (S_, S_)
    fs = '( %s x. ( ( exp ` -u %s ) x. ( %s ^c ( W - 1 ) ) ) )' % (K, LS, LS)
    # v1 with a_t -> S_ ; v3 with b_t -> LS
    def rew(expr, old, new, st):
        idq = w.s([], 'id', '( %s = %s -> %s = %s )' % (old, new, old, new))
        s_, v_ = w.congr(expr, {old: new}, '%s = %s' % (old, new), {old: idq}) if False else (None, None)
        return None
    g1 = w.s([h1v, w.s([ea], 'idi', 'x') if False else
              chain(w, Ct, [v1, gs], [E(w, Ct, 'oveq12d', [E(w, Ct, 'fveq2d', [E(w, Ct, 'negeqd', [E(w, Ct, 'oveq2d', [ea], '( L x. %s )' % a_t, '( L x. %s )' % S_)], '-u ( L x. %s )' % a_t, '-u ( L x. %s )' % S_)],
                                                           '( exp ` -u ( L x. %s ) )' % a_t, '( exp ` -u ( L x. %s ) )' % S_),
                                                       E(w, Ct, 'oveq1d', [ea], '( %s ^c ( W - 1 ) )' % a_t, '( %s ^c ( W - 1 ) )' % S_)], v1, gs)])], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (Ct, H1, a_t, gs))
    g3 = w.s([h3v, chain(w, Ct, [v3, fs], [E(w, Ct, 'oveq2d', [E(w, Ct, 'oveq12d', [E(w, Ct, 'fveq2d', [E(w, Ct, 'negeqd', [eb], '-u %s' % b_t, '-u %s' % LS)], '( exp ` -u %s )' % b_t, '( exp ` -u %s )' % LS),
                                                                                 E(w, Ct, 'oveq1d', [eb], '( %s ^c ( W - 1 ) )' % b_t, '( %s ^c ( W - 1 ) )' % LS)],
                                                                     '( ( exp ` -u %s ) x. ( %s ^c ( W - 1 ) ) )' % (b_t, b_t), '( ( exp ` -u %s ) x. ( %s ^c ( W - 1 ) ) )' % (LS, LS))], v3, fs)])],
             'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (Ct, H3, b_t, fs))
    # algebra: ( fs x. LT ) = ( gs x. T )
    Wt = D(w, Ct, 'adantr', [wc], 'W e. CC'); wmt = D(w, Ct, 'subcld', [Wt, a1(w, Ct, 'ax-1cn', '1 e. CC')], '( W - 1 ) e. CC')
    Eg = '( exp ` -u %s )' % LS
    egc = D(w, Ct, 'efcld', [D(w, Ct, 'negcld', [D(w, Ct, 'rpcnd', [lsrp], '%s e. CC' % LS)], '-u %s e. CC' % LS)], '%s e. CC' % Eg)
    P_ = '( L ^c ( W - 1 ) )'; Q_ = '( %s ^c ( W - 1 ) )' % S_
    pc = D(w, Ct, 'cxpcld', [Lc, wmt], '%s e. CC' % P_); qc = D(w, Ct, 'cxpcld', [D(w, Ct, 'rpcnd', [srp], '%s e. CC' % S_), wmt], '%s e. CC' % Q_)
    kt = D(w, Ct, 'adantr', [kc], '%s e. CC' % K)
    mc_ = w.s([w.s([D(w, Ct, 'rpred', [Lt], 'L e. RR'), D(w, Ct, 'rpge0d', [Lt], '0 <_ L')], 'jca', '( %s -> ( L e. RR /\\ 0 <_ L ) )' % Ct),
               w.s([D(w, Ct, 'rpred', [srp], '%s e. RR' % S_), D(w, Ct, 'rpge0d', [srp], '0 <_ %s' % S_)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (Ct, S_, S_)), wmt, w.inst('mulcxp')], 'syl3anc',
              '( %s -> ( %s ^c ( W - 1 ) ) = ( %s x. %s ) )' % (Ct, LS, P_, Q_))
    LW = '( L ^c W )'
    lw1 = chain(w, Ct, ['( %s x. L )' % P_, '( L ^c ( ( W - 1 ) + 1 ) )', LW],
                [('r', w.s([Lc, D(w, Ct, 'adantr', [ln0], 'L =/= 0'), wmt, w.inst('cxpp1')], 'syl3anc', '( %s -> ( L ^c ( ( W - 1 ) + 1 ) ) = ( %s x. L ) )' % (Ct, P_))),
                 E(w, Ct, 'oveq2d', [E(w, Ct, 'npcand', [Wt, a1(w, Ct, 'ax-1cn', '1 e. CC')], '( ( W - 1 ) + 1 )', 'W')], '( L ^c ( ( W - 1 ) + 1 ) )', LW)])
    lwc = D(w, Ct, 'cxpcld', [Lc, Wt], '%s e. CC' % LW); lwn = D(w, Ct, 'cxpne0d', [Lc, D(w, Ct, 'adantr', [ln0], 'L =/= 0'), Wt], '%s =/= 0' % LW)
    kl = chain(w, Ct, ['( %s x. %s )' % (K, LW), '( ( 1 / %s ) x. %s )' % (LW, LW), '1'],
               [E(w, Ct, 'oveq1d', [w.s([Lc, D(w, Ct, 'adantr', [ln0], 'L =/= 0'), Wt, w.inst('cxpneg')], 'syl3anc', '( %s -> %s = ( 1 / %s ) )' % (Ct, K, LW))], '( %s x. %s )' % (K, LW), '( ( 1 / %s ) x. %s )' % (LW, LW)),
                E(w, Ct, 'recid2d', [lwc, lwn], '( ( 1 / %s ) x. %s )' % (LW, LW), '1')])
    EQ_ = '( %s x. %s )' % (Eg, Q_)
    T0 = '( %s x. %s )' % (fs, LT)
    T1 = '( ( %s x. ( %s x. ( %s x. %s ) ) ) x. %s )' % (K, Eg, P_, Q_, LT)
    T2 = '( ( %s x. ( %s x. %s ) ) x. %s )' % (K, P_, EQ_, LT)
    T3 = '( ( ( %s x. %s ) x. %s ) x. %s )' % (K, P_, EQ_, LT)
    T4 = '( ( ( %s x. %s ) x. L ) x. ( %s x. T ) )' % (K, P_, EQ_)
    T5 = '( ( %s x. ( %s x. L ) ) x. ( %s x. T ) )' % (K, P_, EQ_)
    T6 = '( ( %s x. %s ) x. ( %s x. T ) )' % (K, LW, EQ_)
    T7 = '( 1 x. ( %s x. T ) )' % EQ_
    T8 = '( %s x. T )' % EQ_
    eqc = D(w, Ct, 'mulcld', [egc, qc], '%s e. CC' % EQ_)
    e = [E(w, Ct, 'oveq1d', [E(w, Ct, 'oveq2d', [E(w, Ct, 'oveq2d', [mc_], '( %s x. ( %s ^c ( W - 1 ) ) )' % (Eg, LS), '( %s x. ( %s x. %s ) )' % (Eg, P_, Q_))],
                                 '( %s x. ( %s x. ( %s ^c ( W - 1 ) ) ) )' % (K, Eg, LS), '( %s x. ( %s x. ( %s x. %s ) ) )' % (K, Eg, P_, Q_))], T0, T1),
         E(w, Ct, 'oveq1d', [E(w, Ct, 'oveq2d', [E(w, Ct, 'mul12d', [egc, pc, qc], '( %s x. ( %s x. %s ) )' % (Eg, P_, Q_), '( %s x. %s )' % (P_, EQ_))],
                                 '( %s x. ( %s x. ( %s x. %s ) ) )' % (K, Eg, P_, Q_), '( %s x. ( %s x. %s ) )' % (K, P_, EQ_))], T1, T2),
         E(w, Ct, 'oveq1d', [w.s([E(w, Ct, 'mulassd', [kt, pc, eqc], '( ( %s x. %s ) x. %s )' % (K, P_, EQ_), '( %s x. ( %s x. %s ) )' % (K, P_, EQ_))], 'eqcomd',
                                 '( %s -> ( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s ) )' % (Ct, K, P_, EQ_, K, P_, EQ_))], T2, T3),
         E(w, Ct, 'mul4d', [D(w, Ct, 'mulcld', [kt, pc], '( %s x. %s ) e. CC' % (K, P_)), eqc, Lc, Tc], T3, T4),
         E(w, Ct, 'oveq1d', [E(w, Ct, 'mulassd', [kt, pc, Lc], '( ( %s x. %s ) x. L )' % (K, P_), '( %s x. ( %s x. L ) )' % (K, P_))], T4, T5),
         E(w, Ct, 'oveq1d', [E(w, Ct, 'oveq2d', [lw1], '( %s x. ( %s x. L ) )' % (K, P_), '( %s x. %s )' % (K, LW))], T5, T6),
         E(w, Ct, 'oveq1d', [kl], T6, T7),
         E(w, Ct, 'mullidd', [D(w, Ct, 'mulcld', [eqc, Tc], '%s e. CC' % T8)], T7, T8)]
    alg = chain(w, Ct, [T0, T1, T2, T3, T4, T5, T6, T7, T8], e)
    # gs x. T = ( ( exp ` -u ( L x. S ) ) x. Q ) x. T  -- identical text: gs = ( Eg x. Q_ )
    assert gs == EQ_, (gs, EQ_)
    lhs_i = '( ( %s ` %s ) x. ( T - 0 ) )' % (H1, a_t)
    rhs_i = '( ( %s ` %s ) x. ( %s - 0 ) )' % (H3, b_t, LT)
    pl = chain(w, Ct, [lhs_i, '( %s x. T )' % gs], [E(w, Ct, 'oveq12d', [g1, E(w, Ct, 'subid1d', [Tc], '( T - 0 )', 'T')], lhs_i, '( %s x. T )' % gs)])
    pr_ = chain(w, Ct, [rhs_i, T0, T8], [E(w, Ct, 'oveq12d', [g3, E(w, Ct, 'subid1d', [LTc], '( %s - 0 )' % LT, LT)], rhs_i, T0), alg])
    pw = w.s([pl, pr_], 'eqtr4d', '( %s -> %s = %s )' % (Ct, lhs_i, rhs_i))
    i01 = w.s([pw], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (C, lhs_i, rhs_i))
    q = chain(w, C, [L.EIL('T'), 'S. ( 0 (,) T ) ( %s ` u ) _d u' % H1, 'S. ( 0 (,) 1 ) %s _d t' % lhs_i, 'S. ( 0 (,) 1 ) %s _d t' % rhs_i,
                     'S. ( 0 (,) %s ) ( %s ` u ) _d u' % (LT, H3), 'S. ( 0 (,) %s ) ( %s x. %s ) _d x' % (LT, K, f), '( %s x. %s )' % (K, L.EIF('0', LT))],
              [l1, za1, i01, ('r', za3), ('r', l3), ('r', im)])
    finish(w, q, 'zl3esc')
    go(w)


# ---------------------------------------------------------------- zl3eul
if want('zl3eul'):
    w = W('zl3eul', "Euler's integral with a scale: ` S. ( 0 , t ) e ^ ( - L x ) x ^ ( W - 1 ) dx -> L ^ -W Gamma ( W ) ` as ` t -> +oo ` , "
          'for ` 1 < Re W ` , ` L > 0 ` ( ~ zl3eu1 , ~ zl3esc ; ZL3-blueprint section B).')
    A, Cc = ante_of('zl3eul')
    wc = D(w, A, 'simpll', [], 'W e. CC'); re1 = D(w, A, 'simplr', [], '1 < ( Re ` W )'); lrp = D(w, A, 'simpr', [], 'L e. RR+')
    HWs = w.s([wc, re1], 'jca', '( %s -> %s )' % (A, L.HW))
    G = '( _G ` W )'
    rw = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    rwpos = linarith(w, A, [re1], '0 < ( Re ` W )', closure=Closure(w, A, {'( Re ` W )': ('RR', rw)}))
    gc = w.s([w.s([w.s([wc, rwpos], 'jca', '( %s -> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % A), w.inst('zrenn')], 'syl', '( %s -> W e. ( CC \\ ( ZZ \\ NN ) ) )' % A), w.inst('gamcl')], 'syl',
             '( %s -> %s e. CC )' % (A, G))
    EI1 = L.EI1
    e1 = w.s([HWs, w.inst('zl3eu1')], 'syl', '( %s -> %s ~~>r %s )' % (A, EI1, G))
    EIv = L.EIF('0', 'v'); EIt = L.EIF('0', 't')
    EIv_m = '( v e. RR+ |-> %s )' % EIv
    cbm = w.s([w.s([w.s([], 'oveq2', '( t = v -> ( 0 (,) t ) = ( 0 (,) v ) )'), w.inst('itgeq1')], 'syl', '( t = v -> %s = %s )' % (EIt, EIv))], 'cbvmptv', '%s = %s' % (EI1, EIv_m))
    e1v = w.s([e1, w.s([cbm], 'a1i', '( %s -> %s = %s )' % (A, EI1, EIv_m))], 'breqtrd' if False else 'idi', 'x') if False else None
    e1v = w.s([w.s([w.s([cbm], 'a1i', '( %s -> %s = %s )' % (A, EI1, EIv_m))], 'eqcomd', '( %s -> %s = %s )' % (A, EIv_m, EI1)), e1], 'eqbrtrd', '( %s -> %s ~~>r %s )' % (A, EIv_m, G))
    # all values complex
    Av = '( %s /\\ v e. RR+ )' % A
    evc = w.s([w.s([D(w, Av, 'adantr', [HWs], L.HW), D(w, Av, 'simpr', [], 'v e. RR+')], 'jca', '( %s -> ( %s /\\ v e. RR+ ) )' % (Av, L.HW)), w.inst('zl3icc')], 'syl', '( %s -> %s e. CC )' % (Av, EIv))
    allv = w.s([evc], 'ralrimiva', '( %s -> A. v e. RR+ %s e. CC )' % (A, EIv))
    rs = a1(w, A, 'rpssre', 'RR+ C_ RR')
    P = lambda z: '( abs ` ( %s - %s ) ) < r' % (L.EIF('0', z), G)
    r2a = w.s([allv, rs, gc], 'rlim2', '( %s -> ( %s ~~>r %s <-> A. r e. RR+ E. y e. RR A. v e. RR+ ( y <_ v -> %s ) ) )' % (A, EIv_m, G, P('v')))
    R1 = w.s([e1v, r2a], 'mpbid', '( %s -> A. r e. RR+ E. y e. RR A. v e. RR+ ( y <_ v -> %s ) )' % (A, P('v')))
    # target in the rlim2 form for ( t e. RR+ |-> EI ( L x. t ) )
    LTt = '( L x. t )'
    EIL_t = L.EIF('0', LTt)
    Mt = '( t e. RR+ |-> %s )' % EIL_t
    At = '( %s /\\ t e. RR+ )' % A
    ltrp = D(w, At, 'rpmulcld', [D(w, At, 'adantr', [lrp], 'L e. RR+'), D(w, At, 'simpr', [], 't e. RR+')], '%s e. RR+' % LTt)
    etc = w.s([w.s([D(w, At, 'adantr', [HWs], L.HW), ltrp], 'jca', '( %s -> ( %s /\\ %s e. RR+ ) )' % (At, L.HW, LTt)), w.inst('zl3icc')], 'syl', '( %s -> %s e. CC )' % (At, EIL_t))
    allt = w.s([etc], 'ralrimiva', '( %s -> A. t e. RR+ %s e. CC )' % (A, EIL_t))
    r2b = w.s([allt, rs, gc], 'rlim2', '( %s -> ( %s ~~>r %s <-> A. r e. RR+ E. y e. RR A. t e. RR+ ( y <_ t -> ( abs ` ( %s - %s ) ) < r ) ) )' % (A, Mt, G, EIL_t, G))
    Pt = '( abs ` ( %s - %s ) ) < r' % (EIL_t, G)
    Ar = '( %s /\\ r e. RR+ )' % A
    ex = w.s([w.s([R1], 'adantr', '( %s -> A. r e. RR+ E. y e. RR A. v e. RR+ ( y <_ v -> %s ) )' % (Ar, P('v'))), D(w, Ar, 'simpr', [], 'r e. RR+')], 'idi', 'x') if False else None
    exr = w.s([w.s([R1], 'r19.21bi', '( %s -> E. y e. RR A. v e. RR+ ( y <_ v -> %s ) )' % (Ar, P('v')))], 'idi', '( %s -> E. y e. RR A. v e. RR+ ( y <_ v -> %s ) )' % (Ar, P('v')))
    Ay = '( %s /\\ ( y e. RR /\\ A. v e. RR+ ( y <_ v -> %s ) ) )' % (Ar, P('v'))
    yr = D(w, Ay, 'simprl', [], 'y e. RR'); hv = D(w, Ay, 'simprr', [], 'A. v e. RR+ ( y <_ v -> %s )' % P('v'))
    lr_ = w.s([w.s([lrp], 'adantr', '( %s -> L e. RR+ )' % Ar)], 'adantr', '( %s -> L e. RR+ )' % Ay)
    YL = '( y / L )'
    ylr = D(w, Ay, 'rerpdivcld', [yr, lr_], '%s e. RR' % YL)
    Ayt = '( %s /\\ t e. RR+ )' % Ay
    Ayt2 = '( %s /\\ %s <_ t )' % (Ayt, YL)
    ltp2 = D(w, Ayt, 'rpmulcld', [D(w, Ayt, 'adantr', [lr_], 'L e. RR+'), D(w, Ayt, 'simpr', [], 't e. RR+')], '%s e. RR+' % LTt)
    yle = w.s([D(w, Ayt2, 'simpr', [], '%s <_ t' % YL), D(w, Ayt2, 'ledivmuld', [D(w, Ayt2, 'adantr', [D(w, Ayt, 'adantr', [yr], 'y e. RR')], 'y e. RR'),
                                                                               D(w, Ayt2, 'rpred', [D(w, Ayt2, 'simplr', [], 't e. RR+')], 't e. RR'),
                                                                               D(w, Ayt2, 'adantr', [D(w, Ayt, 'adantr', [lr_], 'L e. RR+')], 'L e. RR+')],
                                                                      '( %s <_ t <-> y <_ ( L x. t ) )' % YL)], 'mpbid', '( %s -> y <_ %s )' % (Ayt2, LTt))
    sub = w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( v = %s -> ( 0 (,) v ) = ( 0 (,) %s ) )' % (LTt, LTt)), w.inst('itgeq1')], 'syl', '( v = %s -> %s = %s )' % (LTt, EIv, EIL_t))], 'oveq1d',
                          '( v = %s -> ( %s - %s ) = ( %s - %s ) )' % (LTt, EIv, G, EIL_t, G))], 'fveq2d', '( v = %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (LTt, EIv, G, EIL_t, G))],
              'breq1d', '( v = %s -> ( %s <-> %s ) )' % (LTt, P('v'), Pt))
    subi = w.s([w.s([], 'breq2', '( v = %s -> ( y <_ v <-> y <_ %s ) )' % (LTt, LTt)), sub], 'imbi12d', '( v = %s -> ( ( y <_ v -> %s ) <-> ( y <_ %s -> %s ) ) )' % (LTt, P('v'), LTt, Pt))
    inst = w.s([D(w, Ayt2, 'adantr', [ltp2], '%s e. RR+' % LTt), D(w, Ayt2, 'adantr', [D(w, Ayt, 'adantr', [hv], 'A. v e. RR+ ( y <_ v -> %s )' % P('v'))], 'A. v e. RR+ ( y <_ v -> %s )' % P('v')),
                w.s([subi], 'rspcv', '( %s e. RR+ -> ( A. v e. RR+ ( y <_ v -> %s ) -> ( y <_ %s -> %s ) ) )' % (LTt, P('v'), LTt, Pt))], 'sylc', '( %s -> ( y <_ %s -> %s ) )' % (Ayt2, LTt, Pt))
    pt = w.s([yle, inst], 'mpd', '( %s -> %s )' % (Ayt2, Pt))
    allt2 = w.s([w.s([pt], 'ex', '( %s -> ( %s <_ t -> %s ) )' % (Ayt, YL, Pt))], 'ralrimiva', '( %s -> A. t e. RR+ ( %s <_ t -> %s ) )' % (Ay, YL, Pt))
    idy = w.s([], 'breq1', '( y = %s -> ( y <_ t <-> %s <_ t ) )' % (YL, YL))
    sy = w.s([w.s([w.s([idy], 'imbi1d', '( y = %s -> ( ( y <_ t -> %s ) <-> ( %s <_ t -> %s ) ) )' % (YL, Pt, YL, Pt))], 'ralbidv',
                  '( y = %s -> ( A. t e. RR+ ( y <_ t -> %s ) <-> A. t e. RR+ ( %s <_ t -> %s ) ) )' % (YL, Pt, YL, Pt))], 'adantl',
             '( ( %s /\\ y = %s ) -> ( A. t e. RR+ ( y <_ t -> %s ) <-> A. t e. RR+ ( %s <_ t -> %s ) ) )' % (Ay, YL, Pt, YL, Pt)) if False else None
    # rspcedvd with a fresh existential variable: the goal E. y ... uses y; the context also has y -> use rexlimdvaa into an E. with letter y after renaming: produce E. s first
    ss_ = w.s([w.s([w.s([], 'breq1', '( s = %s -> ( s <_ t <-> %s <_ t ) )' % (YL, YL))], 'imbi1d', '( s = %s -> ( ( s <_ t -> %s ) <-> ( %s <_ t -> %s ) ) )' % (YL, Pt, YL, Pt))], 'ralbidv',
              '( s = %s -> ( A. t e. RR+ ( s <_ t -> %s ) <-> A. t e. RR+ ( %s <_ t -> %s ) ) )' % (YL, Pt, YL, Pt))
    exs = w.s([ylr, w.s([ss_], 'adantl', '( ( %s /\\ s = %s ) -> ( A. t e. RR+ ( s <_ t -> %s ) <-> A. t e. RR+ ( %s <_ t -> %s ) ) )' % (Ay, YL, Pt, YL, Pt)), allt2], 'rspcedvd',
              '( %s -> E. s e. RR A. t e. RR+ ( s <_ t -> %s ) )' % (Ay, Pt))
    exs2 = w.s([w.s([exs], 'rexlimdvaa', '( %s -> ( E. y e. RR A. v e. RR+ ( y <_ v -> %s ) -> E. s e. RR A. t e. RR+ ( s <_ t -> %s ) ) )' % (Ar, P('v'), Pt)), exr], 'idi', 'x') if False else None
    exs2 = w.s([exr, w.s([exs], 'rexlimdvaa', '( %s -> ( E. y e. RR A. v e. RR+ ( y <_ v -> %s ) -> E. s e. RR A. t e. RR+ ( s <_ t -> %s ) ) )' % (Ar, P('v'), Pt))], 'mpd',
               '( %s -> E. s e. RR A. t e. RR+ ( s <_ t -> %s ) )' % (Ar, Pt))
    cbs = w.s([w.s([w.s([w.s([], 'breq1', '( s = y -> ( s <_ t <-> y <_ t ) )')], 'imbi1d', '( s = y -> ( ( s <_ t -> %s ) <-> ( y <_ t -> %s ) ) )' % (Pt, Pt))], 'ralbidv',
                   '( s = y -> ( A. t e. RR+ ( s <_ t -> %s ) <-> A. t e. RR+ ( y <_ t -> %s ) ) )' % (Pt, Pt))], 'cbvrexvw',
              '( E. s e. RR A. t e. RR+ ( s <_ t -> %s ) <-> E. y e. RR A. t e. RR+ ( y <_ t -> %s ) )' % (Pt, Pt))
    exy = w.s([exs2, cbs], 'sylib', '( %s -> E. y e. RR A. t e. RR+ ( y <_ t -> %s ) )' % (Ar, Pt))
    allr = w.s([exy], 'ralrimiva', '( %s -> A. r e. RR+ E. y e. RR A. t e. RR+ ( y <_ t -> %s ) )' % (A, Pt))
    sc = w.s([allr, r2b], 'mpbird', '( %s -> %s ~~>r %s )' % (A, Mt, G))
    # multiply by K
    K = '( L ^c -u W )'
    kc = D(w, A, 'cxpcld', [D(w, A, 'rpcnd', [lrp], 'L e. CC'), D(w, A, 'negcld', [wc], '-u W e. CC')], '%s e. CC' % K)
    kcon = w.s([rs, kc, w.inst('rlimconst')], 'syl2anc', '( %s -> ( t e. RR+ |-> %s ) ~~>r %s )' % (A, K, K))
    mul = w.s([D(w, At, 'adantr', [kc], '%s e. CC' % K), etc, kcon, sc], 'rlimmul', '( %s -> ( t e. RR+ |-> ( %s x. %s ) ) ~~>r ( %s x. %s ) )' % (A, K, EIL_t, K, G))
    es = w.s([w.s([D(w, At, 'adantr', [HWs], L.HW), w.s([D(w, At, 'adantr', [lrp], 'L e. RR+'), D(w, At, 'simpr', [], 't e. RR+')], 'jca', '( %s -> ( L e. RR+ /\\ t e. RR+ ) )' % At)], 'jca',
                  '( %s -> ( %s /\\ ( L e. RR+ /\\ t e. RR+ ) ) )' % (At, L.HW)), w.inst('zl3esc')], 'syl', '( %s -> %s = ( %s x. %s ) )' % (At, L.EIL('t'), K, EIL_t))
    meq = w.s([es], 'mpteq2dva', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> ( %s x. %s ) ) )' % (A, L.EIL('t'), K, EIL_t))
    q = w.s([meq, mul], 'eqbrtrd', 'x')
    finish(w, q, 'zl3eul')
    go(w)
