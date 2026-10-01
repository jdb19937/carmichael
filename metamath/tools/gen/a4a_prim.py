"""Sortie A4a, batch 6: primeGo and isPrimeTD (spec and cost)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

PGF = lambda d, f: '( 1st ` ( ( M PrimeGo %s ) ` %s ) )' % (d, f)
RHS = lambda d: 'A. e e. NN0 ( ( %s <_ e /\\ ( e x. e ) <_ M ) -> -. e || M )' % d
INN = lambda d, f: '( ( 2 <_ %s /\\ M < ( %s + %s ) ) -> ( %s = 1o <-> %s ) )' % (d, d, f, PGF(d, f), RHS(d))
PHI = lambda f: '( M e. NN0 -> A. d e. NN0 %s )' % INN('d', f)

# --------------------------------------------------------------- base
if not only or 'primegospecb' in only:
    w = W('primegospecb', 'Base of the induction for the specification of primeGo (Lean: primeGo_spec, zero fuel).')
    A = '( ( M e. NN0 /\\ d e. NN0 ) /\\ ( 2 <_ d /\\ M < ( d + 0 ) ) )'
    mn = w.s([], 'simpll', '( %s -> M e. NN0 )' % A)
    dn = w.s([], 'simplr', '( %s -> d e. NN0 )' % A)
    d2 = w.s([], 'simprl', '( %s -> 2 <_ d )' % A)
    mlt = w.s([], 'simprr', '( %s -> M < ( d + 0 ) )' % A)
    pg0 = w.s([mn, dn, w.inst('primego0')], 'syl2anc', '( %s -> ( ( M PrimeGo d ) ` 0 ) = <. 1o , 0 >. )' % A)
    p1 = projeq(w, A, '( ( M PrimeGo d ) ` 0 )', pg0, '1o', '0',
                w.s([w.s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % A),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A), 1)
    # M < d
    dr = w.s([dn], 'nn0red', '( %s -> d e. RR )' % A)
    mr = w.s([mn], 'nn0red', '( %s -> M e. RR )' % A)
    d0 = w.s([w.s([dr], 'recnd', '( %s -> d e. CC )' % A)], 'addridd', '( %s -> ( d + 0 ) = d )' % A)
    mltd = w.s([mlt, d0], 'breqtrd', '( %s -> M < d )' % A)
    # the quantified side
    B = '( %s /\\ e e. NN0 )' % A
    C = '( %s /\\ ( d <_ e /\\ ( e x. e ) <_ M ) )' % B
    en = w.s([], 'simplr', '( %s -> e e. NN0 )' % C)
    de = w.s([], 'simprl', '( %s -> d <_ e )' % C)
    ee = w.s([], 'simprr', '( %s -> ( e x. e ) <_ M )' % C)
    erc = w.s([en], 'nn0red', '( %s -> e e. RR )' % C)
    eg0 = w.s([en], 'nn0ge0d', '( %s -> 0 <_ e )' % C)
    drc = w.s([dr], 'ad2antrr', '( %s -> d e. RR )' % C)
    mrc = w.s([mr], 'ad2antrr', '( %s -> M e. RR )' % C)
    d2c = w.s([d2], 'ad2antrr', '( %s -> 2 <_ d )' % C)
    e1 = lin.linarith(w, C, [d2c, de], '1 <_ e', leaves={'d': drc, 'e': erc})
    sq = w.s([erc, erc, eg0, e1], 'lemulge11d', '( %s -> e <_ ( e x. e ) )' % C)
    sqr = w.s([erc, erc], 'remulcld', '( %s -> ( e x. e ) e. RR )' % C)
    dm = w.s([drc, erc, mrc, de, w.s([erc, sqr, mrc, sq, ee], 'letrd', '( %s -> e <_ M )' % C)], 'letrd', '( %s -> d <_ M )' % C)
    mm = w.s([mrc, drc, mrc, w.s([mltd], 'ad2antrr', '( %s -> M < d )' % C), dm], 'ltletrd', '( %s -> M < M )' % C)
    nmm = w.s([mrc], 'ltnrd', '( %s -> -. M < M )' % C)
    nd = w.s([mm, nmm], 'pm2.21dd', '( %s -> -. e || M )' % C)
    ral = w.s([w.s([nd], 'ex', '( %s -> ( ( d <_ e /\\ ( e x. e ) <_ M ) -> -. e || M ) )' % B)], 'ralrimiva',
              '( %s -> %s )' % (A, RHS('d')))
    bi = w.s([p1, ral], '2thd', '( %s -> ( %s = 1o <-> %s ) )' % (A, PGF('d', '0'), RHS('d')))
    w.qed([w.s([w.s([bi], 'ex', '( ( M e. NN0 /\\ d e. NN0 ) -> %s )' % INN('d', '0'))], 'ralrimiva',
               '( M e. NN0 -> A. d e. NN0 %s )' % INN('d', '0'))], 'id', PHI('0')) if False else None
    w.lines = [l for l in w.lines if not l.startswith('qed')]
    w.qed([w.s([bi], 'ex', '( ( M e. NN0 /\\ d e. NN0 ) -> %s )' % INN('d', '0'))], 'ralrimiva', PHI('0'))
    run(w)

BODY = lambda d, v: '( ( %s <_ %s /\\ ( %s x. %s ) <_ M ) -> -. %s || M )' % (d, v, v, v, v)
RALV = lambda d, v: 'A. %s e. NN0 %s' % (v, BODY(d, v))

def sbe(w, d, frm, to):
    """( frm = to -> ( BODY(d, frm) <-> BODY(d, to) ) )"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
    st, new = w.wcongr(BODY(d, frm), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
    assert new == BODY(d, to), new
    return st

# --------------------------------------------------------------- primegosl1
if not only or 'primegosl1' in only:
    w = W('primegosl1', 'A divisor search may start one higher when the current candidate does not divide (Lean: the index shift inside primeGo_spec).')
    A = '( ( M e. NN0 /\\ D e. NN0 ) /\\ ( 2 <_ D /\\ -. D || M ) )'
    mn = w.s([], 'simpll', '( %s -> M e. NN0 )' % A)
    dn = w.s([], 'simplr', '( %s -> D e. NN0 )' % A)
    d2 = w.s([], 'simprl', '( %s -> 2 <_ D )' % A)
    ndm = w.s([], 'simprr', '( %s -> -. D || M )' % A)
    D1 = '( D + 1 )'
    # ---- forward, with the hypothesis renamed to g
    HG = RALV(D1, 'g')
    T = '( %s /\\ %s )' % (A, HG)
    T2 = '( %s /\\ e e. NN0 )' % T
    T3 = '( %s /\\ ( D <_ e /\\ ( e x. e ) <_ M ) )' % T2
    en = w.s([], 'simplr', '( %s -> e e. NN0 )' % T3)
    de = w.s([], 'simprl', '( %s -> D <_ e )' % T3)
    ee = w.s([], 'simprr', '( %s -> ( e x. e ) <_ M )' % T3)
    dnt = w.s([dn], 'ad3antrrr', '( %s -> D e. NN0 )' % T3)
    dr = w.s([dnt], 'nn0red', '( %s -> D e. RR )' % T3)
    er = w.s([en], 'nn0red', '( %s -> e e. RR )' % T3)
    ndmt = w.s([ndm], 'ad3antrrr', '( %s -> -. D || M )' % T3)
    # case e = D
    U = '( %s /\\ e = D )' % T3
    cu = w.s([w.s([], 'simpr', '( %s -> e = D )' % U)], 'breq1d', '( %s -> ( e || M <-> D || M ) )' % U)
    ru = w.s([w.s([ndmt], 'adantr', '( %s -> -. D || M )' % U), cu], 'mtbird', '( %s -> -. e || M )' % U)
    # case e =/= D
    V = '( %s /\\ -. e = D )' % T3
    nev = w.s([w.s([], 'simpr', '( %s -> -. e = D )' % V)], 'neqned', '( %s -> e =/= D )' % V)
    dltv = w.s([w.s([dr], 'adantr', '( %s -> D e. RR )' % V), w.s([er], 'adantr', '( %s -> e e. RR )' % V)], 'ltlend',
               '( %s -> ( D < e <-> ( D <_ e /\\ e =/= D ) ) )' % V)
    dlt = w.s([dltv, w.s([w.s([de], 'adantr', '( %s -> D <_ e )' % V), nev], 'jca',
                         '( %s -> ( D <_ e /\\ e =/= D ) )' % V)], 'mpbird', '( %s -> D < e )' % V)
    dz = w.s([w.s([dnt], 'adantr', '( %s -> D e. NN0 )' % V)], 'nn0zd', '( %s -> D e. ZZ )' % V)
    ez = w.s([w.s([en], 'adantr', '( %s -> e e. NN0 )' % V)], 'nn0zd', '( %s -> e e. ZZ )' % V)
    d1le = w.s([w.s([dz, ez, w.inst('zltp1le')], 'syl2anc', '( %s -> ( D < e <-> %s <_ e ) )' % (V, D1)), dlt], 'mpbid',
               '( %s -> %s <_ e )' % (V, D1))
    hgv = w.s([], 'simp-4r', '( %s -> %s )' % (V, HG))
    inst = w.s([sbe(w, D1, 'g', 'e'), hgv, w.s([en], 'adantr', '( %s -> e e. NN0 )' % V)], 'rspcdva', '( %s -> %s )' % (V, BODY(D1, 'e')))
    rv = w.s([inst, w.s([d1le, w.s([ee], 'adantr', '( %s -> ( e x. e ) <_ M )' % V)], 'jca',
                        '( %s -> ( %s <_ e /\\ ( e x. e ) <_ M ) )' % (V, D1))], 'mpd', '( %s -> -. e || M )' % V)
    nd = w.s([ru, rv], 'pm2.61dan', '( %s -> -. e || M )' % T3)
    fg = w.s([w.s([w.s([nd], 'ex', '( %s -> %s )' % (T2, BODY('D', 'e')))], 'ralrimiva', '( %s -> %s )' % (T, RALV('D', 'e')))], 'ex',
             '( %s -> ( %s -> %s ) )' % (A, HG, RALV('D', 'e')))
    cbv = w.s([sbe(w, D1, 'e', 'g')], 'cbvralvw', '( %s <-> %s )' % (RALV(D1, 'e'), HG))
    fwd = w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, RALV(D1, 'e'), HG)), fg], 'sylbid',
              '( %s -> ( %s -> %s ) )' % (A, RALV(D1, 'e'), RALV('D', 'e')))
    # ---- backward
    HG2 = RALV('D', 'g')
    S = '( %s /\\ %s )' % (A, HG2)
    S2 = '( %s /\\ e e. NN0 )' % S
    S3 = '( %s /\\ ( %s <_ e /\\ ( e x. e ) <_ M ) )' % (S2, D1)
    en2 = w.s([], 'simplr', '( %s -> e e. NN0 )' % S3)
    d1e = w.s([], 'simprl', '( %s -> %s <_ e )' % (S3, D1))
    ee2 = w.s([], 'simprr', '( %s -> ( e x. e ) <_ M )' % S3)
    dr2 = w.s([w.s([dn], 'ad3antrrr', '( %s -> D e. NN0 )' % S3)], 'nn0red', '( %s -> D e. RR )' % S3)
    er2 = w.s([en2], 'nn0red', '( %s -> e e. RR )' % S3)
    dle2 = lin.linarith(w, S3, [d1e], 'D <_ e', leaves={'D': dr2, 'e': er2})
    hg2 = w.s([], 'simpllr', '( %s -> %s )' % (S3, HG2))
    inst2 = w.s([sbe(w, 'D', 'g', 'e'), hg2, en2], 'rspcdva', '( %s -> %s )' % (S3, BODY('D', 'e')))
    rv2 = w.s([inst2, w.s([dle2, ee2], 'jca', '( %s -> ( D <_ e /\\ ( e x. e ) <_ M ) )' % S3)], 'mpd', '( %s -> -. e || M )' % S3)
    bg = w.s([w.s([w.s([rv2], 'ex', '( %s -> %s )' % (S2, BODY(D1, 'e')))], 'ralrimiva', '( %s -> %s )' % (S, RALV(D1, 'e')))], 'ex',
             '( %s -> ( %s -> %s ) )' % (A, HG2, RALV(D1, 'e')))
    cbv2 = w.s([sbe(w, 'D', 'e', 'g')], 'cbvralvw', '( %s <-> %s )' % (RALV('D', 'e'), HG2))
    bwd = w.s([w.s([cbv2], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, RALV('D', 'e'), HG2)), bg], 'sylbid',
              '( %s -> ( %s -> %s ) )' % (A, RALV('D', 'e'), RALV(D1, 'e')))
    w.qed([fwd, bwd], 'impbid', '( %s -> ( %s <-> %s ) )' % (A, RALV(D1, 'e'), RALV('D', 'e')))
    run(w)

# --------------------------------------------------------------- primegosl2
if not only or 'primegosl2' in only:
    w = W('primegosl2', 'Past the square root there is no divisor left to find (Lean: the first branch of primeGo_spec).')
    A = '( ( M e. NN0 /\\ D e. NN0 ) /\\ M < ( D x. D ) )'
    mn = w.s([], 'simpll', '( %s -> M e. NN0 )' % A)
    dn = w.s([], 'simplr', '( %s -> D e. NN0 )' % A)
    mlt = w.s([], 'simpr', '( %s -> M < ( D x. D ) )' % A)
    T = '( %s /\\ e e. NN0 )' % A
    T2 = '( %s /\\ ( D <_ e /\\ ( e x. e ) <_ M ) )' % T
    en = w.s([], 'simplr', '( %s -> e e. NN0 )' % T2)
    de = w.s([], 'simprl', '( %s -> D <_ e )' % T2)
    ee = w.s([], 'simprr', '( %s -> ( e x. e ) <_ M )' % T2)
    dnn = w.s([dn], 'ad2antrr', '( %s -> D e. NN0 )' % T2)
    dr = w.s([dnn], 'nn0red', '( %s -> D e. RR )' % T2)
    dg0 = w.s([dnn], 'nn0ge0d', '( %s -> 0 <_ D )' % T2)
    er = w.s([en], 'nn0red', '( %s -> e e. RR )' % T2)
    mr = w.s([w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T2)], 'nn0red', '( %s -> M e. RR )' % T2)
    dd = w.s([dr, dr], 'remulcld', '( %s -> ( D x. D ) e. RR )' % T2)
    eesq = w.s([er, er], 'remulcld', '( %s -> ( e x. e ) e. RR )' % T2)
    sq = lin.nlinarith(w, T2, [de, dg0], '( D x. D ) <_ ( e x. e )', leaves={'D': dr, 'e': er})
    mm = w.s([mr, dd, mr, w.s([mlt], 'ad2antrr', '( %s -> M < ( D x. D ) )' % T2),
              w.s([dd, eesq, mr, sq, ee], 'letrd', '( %s -> ( D x. D ) <_ M )' % T2)], 'ltletrd', '( %s -> M < M )' % T2)
    nd = w.s([mm, w.s([mr], 'ltnrd', '( %s -> -. M < M )' % T2)], 'pm2.21dd', '( %s -> -. e || M )' % T2)
    w.qed([w.s([nd], 'ex', '( %s -> %s )' % (T, BODY('D', 'e')))], 'ralrimiva', '( %s -> %s )' % (A, RALV('D', 'e')))
    run(w)

# --------------------------------------------------------------- primegosl3
if not only or 'primegosl3' in only:
    w = W('primegosl3', 'A divisor at the current candidate refutes the specification (Lean: the second branch of primeGo_spec).')
    A = '( ( M e. NN0 /\\ D e. NN0 ) /\\ ( -. M < ( D x. D ) /\\ D || M ) )'
    mn = w.s([], 'simpll', '( %s -> M e. NN0 )' % A)
    dn = w.s([], 'simplr', '( %s -> D e. NN0 )' % A)
    nml = w.s([], 'simprl', '( %s -> -. M < ( D x. D ) )' % A)
    dm = w.s([], 'simprr', '( %s -> D || M )' % A)
    T = '( %s /\\ %s )' % (A, RALV('D', 'e'))
    ral = w.s([], 'simpr', '( %s -> %s )' % (T, RALV('D', 'e')))
    dnt = w.s([dn], 'adantr', '( %s -> D e. NN0 )' % T)
    inst = w.s([sbe(w, 'D', 'e', 'D'), ral, dnt], 'rspcdva', '( %s -> %s )' % (T, BODY('D', 'D')))
    dr = w.s([dnt], 'nn0red', '( %s -> D e. RR )' % T)
    mr = w.s([w.s([mn], 'adantr', '( %s -> M e. NN0 )' % T)], 'nn0red', '( %s -> M e. RR )' % T)
    dd = w.s([dr, dr], 'remulcld', '( %s -> ( D x. D ) e. RR )' % T)
    dle = w.s([], 'leidd', '( %s -> D <_ D )' % T)
    ddm = w.s([w.s([dd, mr], 'lenltd', '( %s -> ( ( D x. D ) <_ M <-> -. M < ( D x. D ) ) )' % T),
               w.s([nml], 'adantr', '( %s -> -. M < ( D x. D ) )' % T)], 'mpbird', '( %s -> ( D x. D ) <_ M )' % T)
    ndm = w.s([inst, w.s([dle, ddm], 'jca', '( %s -> ( D <_ D /\\ ( D x. D ) <_ M ) )' % T)], 'mpd', '( %s -> -. D || M )' % T)
    w.qed([w.s([dm], 'adantr', '( %s -> D || M )' % T), ndm], 'pm2.65da', '( %s -> -. %s )' % (A, RALV('D', 'e')))
    run(w)

def sbi(w, frm, to, f):
    """( frm = to -> ( INN(frm,f) <-> INN(to,f) ) )"""
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
    st, new = w.wcongr(INN(frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
    assert new == INN(to, f), '\n%s\n%s' % (new, INN(to, f))
    return st

# --------------------------------------------------------------- step
if not only or 'primegospecs' in only:
    w = W('primegospecs', 'Step of the induction for the specification of primeGo (Lean: primeGo_spec, one more unit of fuel).')
    IHD = 'A. d e. NN0 %s' % INN('d', 'F')
    IHC = 'A. c e. NN0 %s' % INN('c', 'F')
    A = '( F e. NN0 /\\ ( M e. NN0 -> %s ) )' % IHD
    AC = '( F e. NN0 /\\ ( M e. NN0 -> %s ) )' % IHC
    cbv = w.s([sbi(w, 'd', 'c', 'F')], 'cbvralvw', '( %s <-> %s )' % (IHD, IHC))
    conv = w.s([w.s([], 'simpl', '( %s -> F e. NN0 )' % A),
                w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 -> %s ) )' % (A, IHD)),
                     w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd',
                         '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))], 'syld', '( %s -> ( M e. NN0 -> %s ) )' % (A, IHC))], 'jca',
               '( %s -> %s )' % (A, AC))
    # ---- the main step under AC
    B1 = '( %s /\\ M e. NN0 )' % AC
    B2 = '( %s /\\ d e. NN0 )' % B1
    B = '( %s /\\ ( 2 <_ d /\\ M < ( d + ( F + 1 ) ) ) )' % B2
    fn = w.s([], 'simp-4l', '( %s -> F e. NN0 )' % B)
    mn = w.s([], 'simpllr', '( %s -> M e. NN0 )' % B)
    dn = w.s([], 'simplr', '( %s -> d e. NN0 )' % B)
    d2 = w.s([], 'simprl', '( %s -> 2 <_ d )' % B)
    mlt = w.s([], 'simprr', '( %s -> M < ( d + ( F + 1 ) ) )' % B)
    ihc = w.s([w.s([], 'simp-4r', '( %s -> ( M e. NN0 -> %s ) )' % (B, IHC)), mn], 'mpd', '( %s -> %s )' % (B, IHC))
    d1n = w.s([dn, w.inst('peano2nn0')], 'syl', '( %s -> ( d + 1 ) e. NN0 )' % B)
    inst = w.s([sbi(w, 'c', '( d + 1 )', 'F'), ihc, d1n], 'rspcdva', '( %s -> %s )' % (B, INN('( d + 1 )', 'F')))
    dr = w.s([dn], 'nn0red', '( %s -> d e. RR )' % B)
    mr = w.s([mn], 'nn0red', '( %s -> M e. RR )' % B)
    fr = w.s([fn], 'nn0red', '( %s -> F e. RR )' % B)
    h1 = lin.linarith(w, B, [d2], '2 <_ ( d + 1 )', leaves={'d': dr})
    h2 = lin.linarith(w, B, [mlt], 'M < ( ( d + 1 ) + F )', leaves={'d': dr, 'M': mr, 'F': fr})
    ihapp = w.s([inst, w.s([h1, h2], 'jca', '( %s -> ( 2 <_ ( d + 1 ) /\\ M < ( ( d + 1 ) + F ) ) )' % B)], 'mpd',
                '( %s -> ( %s = 1o <-> %s ) )' % (B, PGF('( d + 1 )', 'F'), RALV('( d + 1 )', 'e')))
    C1 = 'M < ( d x. d )'
    C2 = '( M mod d ) = 0'
    PGN = '<. %s , ( ( 2nd ` ( ( M PrimeGo ( d + 1 ) ) ` F ) ) + 1 ) >.' % PGF('( d + 1 )', 'F')
    IF2 = 'if ( %s , <. (/) , 1 >. , %s )' % (C2, PGN)
    val = '( ( M PrimeGo d ) ` ( F + 1 ) )'
    pgp1 = w.s([w.s([mn, dn], 'jca', '( %s -> ( M e. NN0 /\\ d e. NN0 ) )' % B), fn, w.inst('primegop1')], 'syl2anc',
               '( %s -> %s = if ( %s , <. 1o , 1 >. , %s ) )' % (B, val, C1, IF2))
    vt1, vf1 = ifproj(w, B, val, pgp1, C1, '<. 1o , 1 >.', IF2)
    T1 = '( %s /\\ %s )' % (B, C1)
    NF = '( %s /\\ -. %s )' % (B, C1)
    vt2, vf2 = ifproj(w, NF, val, vf1, C2, '<. (/) , 1 >.', PGN)
    T2 = '( %s /\\ %s )' % (NF, C2)
    T3 = '( %s /\\ -. %s )' % (NF, C2)
    def vex(a, e, lab):
        return w.s([w.s([], lab, '%s e. _V' % e)], 'a1i', '( %s -> %s e. _V )' % (a, e))
    # case 1
    p1 = projeq(w, T1, val, vt1, '1o', '1', vex(T1, '1o', '1oex'), vex(T1, '1', '1ex'), 1)
    r1 = w.s([w.s([w.s([w.s([mn], 'adantr', '( %s -> M e. NN0 )' % T1), w.s([dn], 'adantr', '( %s -> d e. NN0 )' % T1)], 'jca',
                       '( %s -> ( M e. NN0 /\\ d e. NN0 ) )' % T1), w.s([], 'simpr', '( %s -> %s )' % (T1, C1))], 'jca',
                  '( %s -> ( ( M e. NN0 /\\ d e. NN0 ) /\\ %s ) )' % (T1, C1)), w.inst('primegosl2')], 'syl',
             '( %s -> %s )' % (T1, RALV('d', 'e')))
    c1 = w.s([p1, r1], '2thd', '( %s -> ( %s = 1o <-> %s ) )' % (T1, PGF('d', '( F + 1 )'), RALV('d', 'e')))
    # case 2
    p2 = projeq(w, T2, val, vt2, '(/)', '1', vex(T2, '(/)', '0ex'), vex(T2, '1', '1ex'), 1)
    nl2 = w.s([w.s([p2], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (T2, PGF('d', '( F + 1 )'))), zne1o(w, T2)], 'mtbird',
              '( %s -> -. %s = 1o )' % (T2, PGF('d', '( F + 1 )')))
    d1nn = w.s([w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T2),
                lin.linarith(w, T2, [w.s([d2], 'ad2antrr', '( %s -> 2 <_ d )' % T2)], '1 <_ d',
                             leaves={'d': w.s([w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T2)], 'nn0red', '( %s -> d e. RR )' % T2)}),
                w.inst('elnnnn0c')], 'sylanbrc', '( %s -> d e. NN )' % T2)
    dvd2 = w.s([w.s([d1nn, w.s([w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T2)], 'nn0zd', '( %s -> M e. ZZ )' % T2), w.inst('dvdsval3')], 'syl2anc',
                    '( %s -> ( d || M <-> %s ) )' % (T2, C2)), w.s([], 'simpr', '( %s -> %s )' % (T2, C2))], 'mpbird',
               '( %s -> d || M )' % T2)
    cj2 = w.s([w.s([w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T2), w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T2)], 'jca',
                   '( %s -> ( M e. NN0 /\\ d e. NN0 ) )' % T2),
               w.s([w.s([], 'simplr', '( %s -> -. %s )' % (T2, C1)), dvd2], 'jca', '( %s -> ( -. %s /\\ d || M ) )' % (T2, C1))], 'jca',
              '( %s -> ( ( M e. NN0 /\\ d e. NN0 ) /\\ ( -. %s /\\ d || M ) ) )' % (T2, C1))
    nr2 = w.s([cj2, w.inst('primegosl3')], 'syl', '( %s -> -. %s )' % (T2, RALV('d', 'e')))
    c2 = w.s([nl2, nr2], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (T2, PGF('d', '( F + 1 )'), RALV('d', 'e')))
    # case 3
    cl3 = w.s([w.s([w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T3), w.s([d1n], 'ad2antrr', '( %s -> ( d + 1 ) e. NN0 )' % T3)], 'jca',
                   '( %s -> ( M e. NN0 /\\ ( d + 1 ) e. NN0 ) )' % T3), w.s([fn], 'ad2antrr', '( %s -> F e. NN0 )' % T3), w.inst('primegocl')], 'syl2anc',
              '( %s -> ( ( M PrimeGo ( d + 1 ) ) ` F ) e. ( 2o X. NN0 ) )' % T3)
    q1, q2 = paircl(w, T3, '( ( M PrimeGo ( d + 1 ) ) ` F )', cl3, '2o', 'NN0')
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` ( ( M PrimeGo ( d + 1 ) ) ` F ) ) + 1 ) e. NN0 )' % T3)
    p3 = projeq(w, T3, val, vf2, PGF('( d + 1 )', 'F'), '( ( 2nd ` ( ( M PrimeGo ( d + 1 ) ) ` F ) ) + 1 )', q1, q2p, 1)
    d1nn3 = w.s([w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T3),
                 lin.linarith(w, T3, [w.s([d2], 'ad2antrr', '( %s -> 2 <_ d )' % T3)], '1 <_ d',
                              leaves={'d': w.s([w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T3)], 'nn0red', '( %s -> d e. RR )' % T3)}),
                 w.inst('elnnnn0c')], 'sylanbrc', '( %s -> d e. NN )' % T3)
    ndvd3 = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (T3, C2)),
                 w.s([d1nn3, w.s([w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T3)], 'nn0zd', '( %s -> M e. ZZ )' % T3), w.inst('dvdsval3')], 'syl2anc',
                     '( %s -> ( d || M <-> %s ) )' % (T3, C2))], 'mtbird', '( %s -> -. d || M )' % T3)
    cj3 = w.s([w.s([w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T3), w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T3)], 'jca',
                   '( %s -> ( M e. NN0 /\\ d e. NN0 ) )' % T3),
               w.s([w.s([d2], 'ad2antrr', '( %s -> 2 <_ d )' % T3), ndvd3], 'jca', '( %s -> ( 2 <_ d /\\ -. d || M ) )' % T3)], 'jca',
              '( %s -> ( ( M e. NN0 /\\ d e. NN0 ) /\\ ( 2 <_ d /\\ -. d || M ) ) )' % T3)
    sh = w.s([cj3, w.inst('primegosl1')], 'syl', '( %s -> ( %s <-> %s ) )' % (T3, RALV('( d + 1 )', 'e'), RALV('d', 'e')))
    c3 = w.s([w.s([w.s([p3], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (T3, PGF('d', '( F + 1 )'), PGF('( d + 1 )', 'F'))),
                   w.s([ihapp], 'ad2antrr', '( %s -> ( %s = 1o <-> %s ) )' % (T3, PGF('( d + 1 )', 'F'), RALV('( d + 1 )', 'e')))], 'bitrd',
                  '( %s -> ( %s = 1o <-> %s ) )' % (T3, PGF('d', '( F + 1 )'), RALV('( d + 1 )', 'e'))), sh], 'bitrd',
             '( %s -> ( %s = 1o <-> %s ) )' % (T3, PGF('d', '( F + 1 )'), RALV('d', 'e')))
    cnf = w.s([c2, c3], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (NF, PGF('d', '( F + 1 )'), RALV('d', 'e')))
    main = w.s([c1, cnf], 'pm2.61dan', '( %s -> ( %s = 1o <-> %s ) )' % (B, PGF('d', '( F + 1 )'), RALV('d', 'e')))
    mn2 = w.s([w.s([w.s([main], 'ex', '( %s -> %s )' % (B2, INN('d', '( F + 1 )')))], 'ralrimiva',
                   '( %s -> A. d e. NN0 %s )' % (B1, INN('d', '( F + 1 )')))], 'ex', '( %s -> %s )' % (AC, PHI('( F + 1 )')))
    w.qed([conv, mn2], 'syl', '( %s -> %s )' % (A, PHI('( F + 1 )')))
    run(w)

# --------------------------------------------------------------- assembly
if not only or 'primegospecl' in only:
    w = W('primegospecl', 'The specification of primeGo, as the induction on the fuel delivers it.')
    st, pt = fuelind(w, PHI('f'), 'F', 'primegospecb', 'primegospecs', fvar='f')
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
    run(w)

if not only or 'primegospec' in only:
    w = W('primegospec', 'primeGo reports true exactly when no candidate from D up to the square root divides M (Lean: primeGo_spec).')
    T = '( ( M e. NN0 /\\ D e. NN0 /\\ F e. NN0 ) /\\ ( 2 <_ D /\\ M < ( D + F ) ) )'
    mn = w.s([], 'simpl1', '( %s -> M e. NN0 )' % T)
    dn = w.s([], 'simpl2', '( %s -> D e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    d2 = w.s([], 'simprl', '( %s -> 2 <_ D )' % T)
    mlt = w.s([], 'simprr', '( %s -> M < ( D + F ) )' % T)
    ral = w.s([w.s([fn, w.inst('primegospecl')], 'syl', '( %s -> %s )' % (T, PHI('F'))), mn], 'mpd',
              '( %s -> A. d e. NN0 %s )' % (T, INN('d', 'F')))
    inst = w.s([sbi(w, 'd', 'D', 'F'), ral, dn], 'rspcdva', '( %s -> %s )' % (T, INN('D', 'F')))
    w.qed([inst, w.s([d2, mlt], 'jca', '( %s -> ( 2 <_ D /\\ M < ( D + F ) ) )' % T)], 'mpd',
          '( %s -> ( %s = 1o <-> %s ) )' % (T, PGF('D', 'F'), RALV('D', 'e')))
    run(w)

SQM = SQ('M')
PGC = lambda d, f: '( 2nd ` ( ( M PrimeGo %s ) ` %s ) )' % (d, f)
BND = lambda d: '( ( %s + 2 ) - %s )' % (SQM, d)
INC = lambda d, f: '( %s <_ ( %s + 1 ) -> %s <_ %s )' % (d, SQM, PGC(d, f), BND(d))
PHC = lambda f: '( M e. NN0 -> A. d e. NN0 %s )' % INC('d', f)

def sbc(w, frm, to, f):
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
    st, new = w.wcongr(INC(frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
    assert new == INC(to, f), '\n%s\n%s' % (new, INC(to, f))
    return st

def sqmr(w, a, mnstep):
    """( a -> SQ( M ) e. RR )"""
    return w.s([w.s([mnstep, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (a, SQM))], 'nn0red', '( %s -> %s e. RR )' % (a, SQM))

# --------------------------------------------------------------- primegocost base
if not only or 'primegocostb' in only:
    w = W('primegocostb', 'Base of the induction for the cost of primeGo (Lean: primeGo_cost, zero fuel).')
    A = '( ( M e. NN0 /\\ d e. NN0 ) /\\ %s <_ ( %s + 1 ) )' % ('d', SQM)
    mn = w.s([], 'simpll', '( %s -> M e. NN0 )' % A)
    dn = w.s([], 'simplr', '( %s -> d e. NN0 )' % A)
    dle = w.s([], 'simpr', '( %s -> d <_ ( %s + 1 ) )' % (A, SQM))
    pg0 = w.s([mn, dn, w.inst('primego0')], 'syl2anc', '( %s -> ( ( M PrimeGo d ) ` 0 ) = <. 1o , 0 >. )' % A)
    p2 = projeq(w, A, '( ( M PrimeGo d ) ` 0 )', pg0, '1o', '0',
                w.s([w.s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % A),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A), 2)
    li = lin.linarith(w, A, [dle], '0 <_ %s' % BND('d'), leaves={SQM: sqmr(w, A, mn), 'd': w.s([dn], 'nn0red', '( %s -> d e. RR )' % A)})
    bd = w.s([p2, li], 'eqbrtrd', '( %s -> %s <_ %s )' % (A, PGC('d', '0'), BND('d')))
    w.qed([w.s([bd], 'ex', '( ( M e. NN0 /\\ d e. NN0 ) -> %s )' % INC('d', '0'))], 'ralrimiva', PHC('0'))
    run(w)

# --------------------------------------------------------------- primegocost step
if not only or 'primegocosts' in only:
    w = W('primegocosts', 'Step of the induction for the cost of primeGo (Lean: primeGo_cost, one more unit of fuel).')
    IHD = 'A. d e. NN0 %s' % INC('d', 'F')
    IHC = 'A. c e. NN0 %s' % INC('c', 'F')
    A = '( F e. NN0 /\\ ( M e. NN0 -> %s ) )' % IHD
    AC = '( F e. NN0 /\\ ( M e. NN0 -> %s ) )' % IHC
    cbv = w.s([sbc(w, 'd', 'c', 'F')], 'cbvralvw', '( %s <-> %s )' % (IHD, IHC))
    conv = w.s([w.s([], 'simpl', '( %s -> F e. NN0 )' % A),
                w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 -> %s ) )' % (A, IHD)),
                     w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd',
                         '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))], 'syld', '( %s -> ( M e. NN0 -> %s ) )' % (A, IHC))], 'jca',
               '( %s -> %s )' % (A, AC))
    B1 = '( %s /\\ M e. NN0 )' % AC
    B2 = '( %s /\\ d e. NN0 )' % B1
    B = '( %s /\\ d <_ ( %s + 1 ) )' % (B2, SQM)
    fn = w.s([], 'simp-4l', '( %s -> F e. NN0 )' % B)
    mn = w.s([], 'simpllr', '( %s -> M e. NN0 )' % B)
    dn = w.s([], 'simplr', '( %s -> d e. NN0 )' % B)
    dle = w.s([], 'simpr', '( %s -> d <_ ( %s + 1 ) )' % (B, SQM))
    dr = w.s([dn], 'nn0red', '( %s -> d e. RR )' % B)
    sq = sqmr(w, B, mn)
    ihc = w.s([w.s([], 'simp-4r', '( %s -> ( M e. NN0 -> %s ) )' % (B, IHC)), mn], 'mpd', '( %s -> %s )' % (B, IHC))
    d1n = w.s([dn, w.inst('peano2nn0')], 'syl', '( %s -> ( d + 1 ) e. NN0 )' % B)
    inst = w.s([sbc(w, 'c', '( d + 1 )', 'F'), ihc, d1n], 'rspcdva', '( %s -> %s )' % (B, INC('( d + 1 )', 'F')))
    C1 = 'M < ( d x. d )'
    C2 = '( M mod d ) = 0'
    PGN = '<. %s , ( %s + 1 ) >.' % (PGF('( d + 1 )', 'F'), PGC('( d + 1 )', 'F'))
    IF2 = 'if ( %s , <. (/) , 1 >. , %s )' % (C2, PGN)
    val = '( ( M PrimeGo d ) ` ( F + 1 ) )'
    pgp1 = w.s([w.s([mn, dn], 'jca', '( %s -> ( M e. NN0 /\\ d e. NN0 ) )' % B), fn, w.inst('primegop1')], 'syl2anc',
               '( %s -> %s = if ( %s , <. 1o , 1 >. , %s ) )' % (B, val, C1, IF2))
    vt1, vf1 = ifproj(w, B, val, pgp1, C1, '<. 1o , 1 >.', IF2)
    T1 = '( %s /\\ %s )' % (B, C1)
    NF = '( %s /\\ -. %s )' % (B, C1)
    vt2, vf2 = ifproj(w, NF, val, vf1, C2, '<. (/) , 1 >.', PGN)
    T2 = '( %s /\\ %s )' % (NF, C2)
    T3 = '( %s /\\ -. %s )' % (NF, C2)
    def vex(a, e, lab):
        return w.s([w.s([], lab, '%s e. _V' % e)], 'a1i', '( %s -> %s e. _V )' % (a, e))
    def one(a, dlestep, drs, sqs):
        return lin.linarith(w, a, [dlestep], '1 <_ %s' % BND('d'), leaves={SQM: sqs, 'd': drs})
    # case 1: cost 1
    p1 = projeq(w, T1, val, vt1, '1o', '1', vex(T1, '1o', '1oex'), vex(T1, '1', '1ex'), 2)
    c1 = w.s([p1, one(T1, w.s([dle], 'adantr', '( %s -> d <_ ( %s + 1 ) )' % (T1, SQM)),
                      w.s([dr], 'adantr', '( %s -> d e. RR )' % T1), w.s([sq], 'adantr', '( %s -> %s e. RR )' % (T1, SQM)))], 'eqbrtrd',
             '( %s -> %s <_ %s )' % (T1, PGC('d', '( F + 1 )'), BND('d')))
    # case 2: cost 1
    p2 = projeq(w, T2, val, vt2, '(/)', '1', vex(T2, '(/)', '0ex'), vex(T2, '1', '1ex'), 2)
    c2 = w.s([p2, one(T2, w.s([dle], 'ad2antrr', '( %s -> d <_ ( %s + 1 ) )' % (T2, SQM)),
                      w.s([dr], 'ad2antrr', '( %s -> d e. RR )' % T2), w.s([sq], 'ad2antrr', '( %s -> %s e. RR )' % (T2, SQM)))], 'eqbrtrd',
             '( %s -> %s <_ %s )' % (T2, PGC('d', '( F + 1 )'), BND('d')))
    # case 3
    mn3 = w.s([mn], 'ad2antrr', '( %s -> M e. NN0 )' % T3)
    dn3 = w.s([dn], 'ad2antrr', '( %s -> d e. NN0 )' % T3)
    fn3 = w.s([fn], 'ad2antrr', '( %s -> F e. NN0 )' % T3)
    d1n3 = w.s([d1n], 'ad2antrr', '( %s -> ( d + 1 ) e. NN0 )' % T3)
    dr3 = w.s([dr], 'ad2antrr', '( %s -> d e. RR )' % T3)
    sq3 = w.s([sq], 'ad2antrr', '( %s -> %s e. RR )' % (T3, SQM))
    mr3 = w.s([mn3], 'nn0red', '( %s -> M e. RR )' % T3)
    dd3 = w.s([dr3, dr3], 'remulcld', '( %s -> ( d x. d ) e. RR )' % T3)
    ddm = w.s([w.s([dd3, mr3], 'lenltd', '( %s -> ( ( d x. d ) <_ M <-> -. %s ) )' % (T3, C1)),
               w.s([], 'simplr', '( %s -> -. %s )' % (T3, C1))], 'mpbird', '( %s -> ( d x. d ) <_ M )' % T3)
    dsq = w.s([w.s([dn3, mn3, w.inst('nsqrtle')], 'syl2anc', '( %s -> ( d <_ %s <-> ( d x. d ) <_ M ) )' % (T3, SQM)), ddm], 'mpbird',
              '( %s -> d <_ %s )' % (T3, SQM))
    hyp3 = lin.linarith(w, T3, [dsq], '( d + 1 ) <_ ( %s + 1 )' % SQM, leaves={SQM: sq3, 'd': dr3})
    ihapp = w.s([w.s([inst], 'ad2antrr', '( %s -> %s )' % (T3, INC('( d + 1 )', 'F'))), hyp3], 'mpd',
                '( %s -> %s <_ %s )' % (T3, PGC('( d + 1 )', 'F'), BND('( d + 1 )')))
    cl3 = w.s([w.s([mn3, d1n3], 'jca', '( %s -> ( M e. NN0 /\\ ( d + 1 ) e. NN0 ) )' % T3), fn3, w.inst('primegocl')], 'syl2anc',
              '( %s -> ( ( M PrimeGo ( d + 1 ) ) ` F ) e. ( 2o X. NN0 ) )' % T3)
    q1, q2 = paircl(w, T3, '( ( M PrimeGo ( d + 1 ) ) ` F )', cl3, '2o', 'NN0')
    q2r = w.s([q2], 'nn0red', '( %s -> %s e. RR )' % (T3, PGC('( d + 1 )', 'F')))
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (T3, PGC('( d + 1 )', 'F')))
    p3 = projeq(w, T3, val, vf2, PGF('( d + 1 )', 'F'), '( %s + 1 )' % PGC('( d + 1 )', 'F'), q1, q2p, 2)
    li3 = lin.linarith(w, T3, [ihapp], '( %s + 1 ) <_ %s' % (PGC('( d + 1 )', 'F'), BND('d')),
                       leaves={SQM: sq3, 'd': dr3, PGC('( d + 1 )', 'F'): q2r})
    c3 = w.s([p3, li3], 'eqbrtrd', '( %s -> %s <_ %s )' % (T3, PGC('d', '( F + 1 )'), BND('d')))
    cnf = w.s([c2, c3], 'pm2.61dan', '( %s -> %s <_ %s )' % (NF, PGC('d', '( F + 1 )'), BND('d')))
    main = w.s([c1, cnf], 'pm2.61dan', '( %s -> %s <_ %s )' % (B, PGC('d', '( F + 1 )'), BND('d')))
    mn2 = w.s([w.s([w.s([main], 'ex', '( %s -> %s )' % (B2, INC('d', '( F + 1 )')))], 'ralrimiva',
                   '( %s -> A. d e. NN0 %s )' % (B1, INC('d', '( F + 1 )')))], 'ex', '( %s -> %s )' % (AC, PHC('( F + 1 )')))
    w.qed([conv, mn2], 'syl', '( %s -> %s )' % (A, PHC('( F + 1 )')))
    run(w)

# --------------------------------------------------------------- primegocost assembly
if not only or 'primegocostl' in only:
    w = W('primegocostl', 'The cost of primeGo, as the induction on the fuel delivers it.')
    st, pt = fuelind(w, PHC('f'), 'F', 'primegocostb', 'primegocosts', fvar='f')
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
    run(w)

if not only or 'primegocost' in only:
    w = W('primegocost', 'The cost of primeGo (Lean: primeGo_cost).')
    T = '( ( M e. NN0 /\\ D e. NN0 /\\ F e. NN0 ) /\\ D <_ ( %s + 1 ) )' % SQM
    mn = w.s([], 'simpl1', '( %s -> M e. NN0 )' % T)
    dn = w.s([], 'simpl2', '( %s -> D e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    dle = w.s([], 'simpr', '( %s -> D <_ ( %s + 1 ) )' % (T, SQM))
    ral = w.s([w.s([fn, w.inst('primegocostl')], 'syl', '( %s -> %s )' % (T, PHC('F'))), mn], 'mpd',
              '( %s -> A. d e. NN0 %s )' % (T, INC('d', 'F')))
    inst = w.s([sbc(w, 'd', 'D', 'F'), ral, dn], 'rspcdva', '( %s -> %s )' % (T, INC('D', 'F')))
    w.qed([inst, dle], 'mpd', '( %s -> %s <_ %s )' % (T, PGC('D', 'F'), BND('D')))
    run(w)

RAL2 = RALV('2', 'e')

# --------------------------------------------------------------- primetdbi
if not only or 'primetdbi' in only:
    w = W('primetdbi', 'Primality by trial division up to the square root (Lean: Nat.prime_def_le_sqrt, in the form the loop invariant delivers).')
    U = 'M e. ( ZZ>= ` 2 )'
    A = '( %s /\\ %s )' % (U, RAL2)
    uz = w.s([], 'simpl', '( %s -> %s )' % (A, U))
    ral = w.s([], 'simpr', '( %s -> %s )' % (A, RAL2))
    B = '( %s /\\ z e. Prime )' % A
    C = '( %s /\\ ( z ^ 2 ) <_ M )' % B
    zp = w.s([], 'simplr', '( %s -> z e. Prime )' % C)
    zn = w.s([zp, w.inst('prmnn')], 'syl', '( %s -> z e. NN )' % C)
    zn0 = w.s([zn], 'nnnn0d', '( %s -> z e. NN0 )' % C)
    zu = w.s([zp, w.inst('prmuz2')], 'syl', '( %s -> z e. ( ZZ>= ` 2 ) )' % C)
    z2 = w.s([w.s([zu, w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ z e. ZZ /\\ 2 <_ z ) )' % C)], 'simp3d', '( %s -> 2 <_ z )' % C)
    sv = w.s([w.s([zn0], 'nn0cnd', '( %s -> z e. CC )' % C), w.inst('sqval')], 'syl', '( %s -> ( z ^ 2 ) = ( z x. z ) )' % C)
    zz = w.s([sv, w.s([], 'simpr', '( %s -> ( z ^ 2 ) <_ M )' % C)], 'eqbrtrrd',
             '( %s -> ( z x. z ) <_ M )' % C)
    inst = w.s([sbe(w, '2', 'e', 'z'), w.s([ral], 'ad2antrr', '( %s -> %s )' % (C, RAL2)), zn0], 'rspcdva', '( %s -> %s )' % (C, BODY('2', 'z')))
    nzm = w.s([inst, w.s([z2, zz], 'jca', '( %s -> ( 2 <_ z /\\ ( z x. z ) <_ M ) )' % C)], 'mpd', '( %s -> -. z || M )' % C)
    ralz = w.s([w.s([nzm], 'ex', '( %s -> ( ( z ^ 2 ) <_ M -> -. z || M ) )' % B)], 'ralrimiva',
               '( %s -> A. z e. Prime ( ( z ^ 2 ) <_ M -> -. z || M ) )' % A)
    fwd = w.s([w.s([w.s([uz, ralz], 'jca', '( %s -> ( %s /\\ A. z e. Prime ( ( z ^ 2 ) <_ M -> -. z || M ) ) )' % (A, U)),
                    w.s([w.s([], 'isprm5', '( M e. Prime <-> ( %s /\\ A. z e. Prime ( ( z ^ 2 ) <_ M -> -. z || M ) ) )' % U)], 'a1i',
                        '( %s -> ( M e. Prime <-> ( %s /\\ A. z e. Prime ( ( z ^ 2 ) <_ M -> -. z || M ) ) ) )' % (A, U))], 'mpbird',
                   '( %s -> M e. Prime )' % A)], 'ex', '( %s -> ( %s -> M e. Prime ) )' % (U, RAL2))
    # backward
    A2 = '( %s /\\ M e. Prime )' % U
    D2 = '( %s /\\ e e. NN0 )' % A2
    E2 = '( %s /\\ ( 2 <_ e /\\ ( e x. e ) <_ M ) )' % D2
    G2 = '( %s /\\ e || M )' % E2
    en = w.s([], 'simpllr', '( %s -> e e. NN0 )' % G2)
    e2 = w.s([], 'simplrl', '( %s -> 2 <_ e )' % G2)
    ee = w.s([], 'simplrr', '( %s -> ( e x. e ) <_ M )' % G2)
    edm = w.s([], 'simpr', '( %s -> e || M )' % G2)
    mp = w.s([], 'simp-4r', '( %s -> M e. Prime )' % G2)
    tz = w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % G2)
    euz = w.s([w.s([tz, w.s([en], 'nn0zd', '( %s -> e e. ZZ )' % G2), e2], '3jca',
                   '( %s -> ( 2 e. ZZ /\\ e e. ZZ /\\ 2 <_ e ) )' % G2), w.inst('eluz2')], 'sylibr',
              '( %s -> e e. ( ZZ>= ` 2 ) )' % G2)
    i4 = w.s([mp, w.s([w.s([], 'isprm4', '( M e. Prime <-> ( %s /\\ A. z e. ( ZZ>= ` 2 ) ( z || M -> z = M ) ) )' % U)], 'a1i',
                      '( %s -> ( M e. Prime <-> ( %s /\\ A. z e. ( ZZ>= ` 2 ) ( z || M -> z = M ) ) ) )' % (G2, U))], 'mpbid',
             '( %s -> ( %s /\\ A. z e. ( ZZ>= ` 2 ) ( z || M -> z = M ) ) )' % (G2, U))
    sbz = w.s([w.s([w.s([], 'id', '( z = e -> z = e )')], 'breq1d', '( z = e -> ( z || M <-> e || M ) )'),
               w.s([w.s([], 'id', '( z = e -> z = e )')], 'eqeq1d', '( z = e -> ( z = M <-> e = M ) )')], 'imbi12d',
              '( z = e -> ( ( z || M -> z = M ) <-> ( e || M -> e = M ) ) )')
    em = w.s([sbz, w.s([i4], 'simprd', '( %s -> A. z e. ( ZZ>= ` 2 ) ( z || M -> z = M ) )' % G2), euz], 'rspcdva',
             '( %s -> ( e || M -> e = M ) )' % G2)
    eqm = w.s([em, edm], 'mpd', '( %s -> e = M )' % G2)
    cg, _ = w.congr('( e x. e )', {}, G2, {}, rules={'e': ('M', eqm)})
    mm = w.s([cg, ee], 'eqbrtrrd', '( %s -> ( M x. M ) <_ M )' % G2)
    mz = w.s([w.s([mp, w.inst('prmnn')], 'syl', '( %s -> M e. NN )' % G2)], 'nnred', '( %s -> M e. RR )' % G2)
    m2 = w.s([w.s([w.s([], 'simp-4l', '( %s -> %s )' % (G2, U)), w.inst('eluz2')], 'sylib',
                  '( %s -> ( 2 e. ZZ /\\ M e. ZZ /\\ 2 <_ M ) )' % G2)], 'simp3d', '( %s -> 2 <_ M )' % G2)
    nmm = w.s([lin.nlinarith(w, G2, [m2], 'M < ( M x. M )', leaves={'M': mz}), w.s([mz, w.s([mz, mz], 'remulcld', '( %s -> ( M x. M ) e. RR )' % G2)], 'ltnled',
                                                                                  '( %s -> ( M < ( M x. M ) <-> -. ( M x. M ) <_ M ) )' % G2)], 'mpbid',
              '( %s -> -. ( M x. M ) <_ M )' % G2)
    nedm = w.s([mm, nmm], 'pm2.65da', '( %s -> -. e || M )' % E2)
    bwd = w.s([w.s([w.s([nedm], 'ex', '( %s -> %s )' % (D2, BODY('2', 'e')))], 'ralrimiva', '( %s -> %s )' % (A2, RAL2))], 'ex',
              '( %s -> ( M e. Prime -> %s ) )' % (U, RAL2))
    w.qed([fwd, bwd], 'impbid', '( %s -> ( %s <-> M e. Prime ) )' % (U, RAL2))
    run(w)

# --------------------------------------------------------------- isPrimeTD
IPV = '( IsPrimeTD ` M )'
PGM = '( ( M PrimeGo 2 ) ` M )'
if not only or 'isprimetdspec' in only:
    w = W('isprimetdspec', 'isPrimeTD decides primality (Lean: isPrimeTD_spec).')
    A = 'M e. NN0'
    mn = w.s([], 'id', '( %s -> M e. NN0 )' % A)
    mr = w.s([mn], 'nn0red', '( %s -> M e. RR )' % A)
    v = w.s([mn, w.inst('isprimetdval')], 'syl',
            '( %s -> %s = if ( M < 2 , <. (/) , 1 >. , <. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >. ) )' % (A, IPV, PGM, PGM))
    vt, vf = ifproj(w, A, IPV, v, 'M < 2', '<. (/) , 1 >.', '<. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >.' % (PGM, PGM))
    T = '( %s /\\ M < 2 )' % A
    F = '( %s /\\ -. M < 2 )' % A
    # case M < 2
    pt = projeq(w, T, IPV, vt, '(/)', '1', w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % T),
                w.s([w.s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % T), 1)
    nl = w.s([w.s([pt], 'eqeq1d', '( %s -> ( ( 1st ` %s ) = 1o <-> (/) = 1o ) )' % (T, IPV)), zne1o(w, T)], 'mtbird',
             '( %s -> -. ( 1st ` %s ) = 1o )' % (T, IPV))
    P2 = '( %s /\\ M e. Prime )' % T
    m2p = w.s([w.s([w.s([], 'simpr', '( %s -> M e. Prime )' % P2), w.inst('prmuz2')], 'syl', '( %s -> M e. ( ZZ>= ` 2 ) )' % P2),
               w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ M e. ZZ /\\ 2 <_ M ) )' % P2)
    m2 = w.s([m2p], 'simp3d', '( %s -> 2 <_ M )' % P2)
    nlt = w.s([w.s([w.s([mr], 'ad2antrr', '( %s -> M e. RR )' % P2),
                    w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % P2)], 'lenltd',
                   '( %s -> ( 2 <_ M <-> -. M < 2 ) )' % P2), m2], 'mpbid', '( %s -> -. M < 2 )' % P2)
    npr = w.s([w.s([], 'simplr', '( %s -> M < 2 )' % P2), nlt], 'pm2.65da', '( %s -> -. M e. Prime )' % T)
    ct = w.s([nl, npr], '2falsed', '( %s -> ( ( 1st ` %s ) = 1o <-> M e. Prime ) )' % (T, IPV))
    # case 2 <_ M
    mnf = w.s([mn], 'adantr', '( %s -> M e. NN0 )' % F)
    mrf = w.s([mr], 'adantr', '( %s -> M e. RR )' % F)
    m2f = w.s([w.s([mrf, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % F)], 'lenltd', '( %s -> ( 2 <_ M <-> -. M < 2 ) )' % F),
               w.s([], 'simpr', '( %s -> -. M < 2 )' % F)], 'mpbird', '( %s -> 2 <_ M )' % F)
    muz = w.s([w.s([w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % F), w.s([mnf], 'nn0zd', '( %s -> M e. ZZ )' % F), m2f], '3jca',
                   '( %s -> ( 2 e. ZZ /\\ M e. ZZ /\\ 2 <_ M ) )' % F), w.inst('eluz2')], 'sylibr', '( %s -> M e. ( ZZ>= ` 2 ) )' % F)
    n2 = w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % F)
    cl = w.s([w.s([mnf, n2], 'jca', '( %s -> ( M e. NN0 /\\ 2 e. NN0 ) )' % F), mnf, w.inst('primegocl')], 'syl2anc',
             '( %s -> %s e. ( 2o X. NN0 ) )' % (F, PGM))
    q1, q2 = paircl(w, F, PGM, cl, '2o', 'NN0')
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` %s ) + 1 ) e. NN0 )' % (F, PGM))
    pf = projeq(w, F, IPV, vf, '( 1st ` %s )' % PGM, '( ( 2nd ` %s ) + 1 )' % PGM, q1, q2p, 1)
    le2 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.inst('leid')], 'ax-mp', '2 <_ 2')], 'a1i', '( %s -> 2 <_ 2 )' % F)
    mlt = lin.linarith(w, F, [m2f], 'M < ( 2 + M )', leaves={'M': mrf})
    spec = w.s([w.s([w.s([mnf, n2, mnf], '3jca', '( %s -> ( M e. NN0 /\\ 2 e. NN0 /\\ M e. NN0 ) )' % F),
                     w.s([le2, mlt], 'jca', '( %s -> ( 2 <_ 2 /\\ M < ( 2 + M ) ) )' % F)], 'jca',
                    '( %s -> ( ( M e. NN0 /\\ 2 e. NN0 /\\ M e. NN0 ) /\\ ( 2 <_ 2 /\\ M < ( 2 + M ) ) ) )' % F), w.inst('primegospec')], 'syl',
               '( %s -> ( ( 1st ` %s ) = 1o <-> %s ) )' % (F, PGM, RAL2))
    bi = w.s([muz, w.inst('primetdbi')], 'syl', '( %s -> ( %s <-> M e. Prime ) )' % (F, RAL2))
    cf = w.s([w.s([w.s([pf], 'eqeq1d', '( %s -> ( ( 1st ` %s ) = 1o <-> ( 1st ` %s ) = 1o ) )' % (F, IPV, PGM)), spec], 'bitrd',
                  '( %s -> ( ( 1st ` %s ) = 1o <-> %s ) )' % (F, IPV, RAL2)), bi], 'bitrd',
             '( %s -> ( ( 1st ` %s ) = 1o <-> M e. Prime ) )' % (F, IPV))
    w.qed([ct, cf], 'pm2.61dan', '( %s -> ( ( 1st ` %s ) = 1o <-> M e. Prime ) )' % (A, IPV))
    run(w)

if not only or 'isprimetdcost' in only:
    w = W('isprimetdcost', 'The cost of isPrimeTD (Lean: isPrimeTD_cost).')
    A = 'M e. NN0'
    mn = w.s([], 'id', '( %s -> M e. NN0 )' % A)
    mr = w.s([mn], 'nn0red', '( %s -> M e. RR )' % A)
    sq = sqmr(w, A, mn)
    sqn = w.s([mn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A, SQM))
    v = w.s([mn, w.inst('isprimetdval')], 'syl',
            '( %s -> %s = if ( M < 2 , <. (/) , 1 >. , <. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >. ) )' % (A, IPV, PGM, PGM))
    vt, vf = ifproj(w, A, IPV, v, 'M < 2', '<. (/) , 1 >.', '<. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >.' % (PGM, PGM))
    T = '( %s /\\ M < 2 )' % A
    F = '( %s /\\ -. M < 2 )' % A
    pt = projeq(w, T, IPV, vt, '(/)', '1', w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % T),
                w.s([w.s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % T), 2)
    ge0 = w.s([w.s([sqn], 'adantr', '( %s -> %s e. NN0 )' % (T, SQM))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (T, SQM))
    lt = lin.linarith(w, T, [ge0], '1 <_ ( %s + 1 )' % SQM, leaves={SQM: w.s([sq], 'adantr', '( %s -> %s e. RR )' % (T, SQM))})
    ct = w.s([pt, lt], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( %s + 1 ) )' % (T, IPV, SQM))
    # case 2 <_ M
    mnf = w.s([mn], 'adantr', '( %s -> M e. NN0 )' % F)
    mrf = w.s([mr], 'adantr', '( %s -> M e. RR )' % F)
    sqf = w.s([sq], 'adantr', '( %s -> %s e. RR )' % (F, SQM))
    sqnf = w.s([sqn], 'adantr', '( %s -> %s e. NN0 )' % (F, SQM))
    m2f = w.s([w.s([mrf, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % F)], 'lenltd', '( %s -> ( 2 <_ M <-> -. M < 2 ) )' % F),
               w.s([], 'simpr', '( %s -> -. M < 2 )' % F)], 'mpbird', '( %s -> 2 <_ M )' % F)
    n2 = w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % F)
    n1 = w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % F)
    o1 = w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % F)
    m1 = lin.linarith(w, F, [m2f], '1 <_ M', leaves={'M': mrf})
    onele = w.s([o1, m1], 'eqbrtrd', '( %s -> ( 1 x. 1 ) <_ M )' % F)
    sq1 = w.s([w.s([n1, mnf, w.inst('nsqrtle')], 'syl2anc', '( %s -> ( 1 <_ %s <-> ( 1 x. 1 ) <_ M ) )' % (F, SQM)), onele], 'mpbird',
              '( %s -> 1 <_ %s )' % (F, SQM))
    dle = lin.linarith(w, F, [sq1], '2 <_ ( %s + 1 )' % SQM, leaves={SQM: sqf})
    cost = w.s([w.s([w.s([mnf, n2, mnf], '3jca', '( %s -> ( M e. NN0 /\\ 2 e. NN0 /\\ M e. NN0 ) )' % F), dle], 'jca',
                    '( %s -> ( ( M e. NN0 /\\ 2 e. NN0 /\\ M e. NN0 ) /\\ 2 <_ ( %s + 1 ) ) )' % (F, SQM)), w.inst('primegocost')], 'syl',
               '( %s -> ( 2nd ` %s ) <_ ( ( %s + 2 ) - 2 ) )' % (F, PGM, SQM))
    cl = w.s([w.s([mnf, n2], 'jca', '( %s -> ( M e. NN0 /\\ 2 e. NN0 ) )' % F), mnf, w.inst('primegocl')], 'syl2anc',
             '( %s -> %s e. ( 2o X. NN0 ) )' % (F, PGM))
    q1, q2 = paircl(w, F, PGM, cl, '2o', 'NN0')
    q2r = w.s([q2], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (F, PGM))
    q2p = w.s([q2, w.inst('peano2nn0')], 'syl', '( %s -> ( ( 2nd ` %s ) + 1 ) e. NN0 )' % (F, PGM))
    pf = projeq(w, F, IPV, vf, '( 1st ` %s )' % PGM, '( ( 2nd ` %s ) + 1 )' % PGM, q1, q2p, 2)
    li = lin.linarith(w, F, [cost], '( ( 2nd ` %s ) + 1 ) <_ ( %s + 1 )' % (PGM, SQM),
                      leaves={SQM: sqf, '( 2nd ` %s )' % PGM: q2r})
    cf = w.s([pf, li], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( %s + 1 ) )' % (F, IPV, SQM))
    w.qed([ct, cf], 'pm2.61dan', '( %s -> ( 2nd ` %s ) <_ ( %s + 1 ) )' % (A, IPV, SQM))
    run(w)
