"""Sortie A4a, batch 8: the quotient of a successful division, and divOut."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DQ = '( |_ ` ( R / D ) )'
MD = '( R mod D ) = 0'

def qctx(w, A):
    dn = w.s([], 'simpll', '( %s -> D e. NN )' % A)
    rn = w.s([], 'simplr', '( %s -> R e. NN0 )' % A)
    return dn, rn

def qbasics(w, A, dn, rn, md):
    """( A -> D || R ), ( A -> ( R / D ) e. ZZ ), ( A -> DQ = ( R / D ) ), ( A -> DQ e. NN0 )"""
    dz = w.s([dn], 'nnzd', '( %s -> D e. ZZ )' % A)
    rz = w.s([rn], 'nn0zd', '( %s -> R e. ZZ )' % A)
    dne = w.s([dn], 'nnne0d', '( %s -> D =/= 0 )' % A)
    dr = w.s([w.s([dz, dne, rz], '3jca', '( %s -> ( D e. ZZ /\\ D =/= 0 /\\ R e. ZZ ) )' % A), w.inst('dvdsval3')], 'syl',
             '( %s -> ( D || R <-> %s ) )' % (A, MD)) if False else None
    dvb = w.s([dn, rz, w.inst('dvdsval3')], 'syl2anc', '( %s -> ( D || R <-> %s ) )' % (A, MD))
    dvd = w.s([dvb, md], 'mpbird', '( %s -> D || R )' % A)
    qz = w.s([w.s([w.s([dz, dne, rz], '3jca', '( %s -> ( D e. ZZ /\\ D =/= 0 /\\ R e. ZZ ) )' % A), w.inst('dvdsval2')], 'syl',
                  '( %s -> ( D || R <-> ( R / D ) e. ZZ ) )' % A), dvd], 'mpbid', '( %s -> ( R / D ) e. ZZ )' % A)
    fl = w.s([qz, w.inst('flid')], 'syl', '( %s -> %s = ( R / D ) )' % (A, DQ))
    ge0 = w.s([w.s([w.s([rn], 'nn0red', '( %s -> R e. RR )' % A), w.s([rn], 'nn0ge0d', '( %s -> 0 <_ R )' % A)], 'jca',
                   '( %s -> ( R e. RR /\\ 0 <_ R ) )' % A),
               w.s([w.s([dn], 'nnred', '( %s -> D e. RR )' % A), w.s([dn], 'nngt0d', '( %s -> 0 < D )' % A)], 'jca',
                   '( %s -> ( D e. RR /\\ 0 < D ) )' % A), w.inst('divge0')], 'syl2anc', '( %s -> 0 <_ ( R / D ) )' % A)
    qn0 = w.s([fl, w.s([qz, ge0, w.inst('elnn0z')], 'sylanbrc', '( %s -> ( R / D ) e. NN0 )' % A)], 'eqeltrd', '( %s -> %s e. NN0 )' % (A, DQ))
    return dvd, qz, fl, qn0

A0 = '( ( D e. NN /\\ R e. NN0 ) /\\ %s )' % MD

# --------------------------------------------------------------- divoutq1 / q2
if not only or 'divoutqv' in only:
    w = W('divoutqv', 'The floor of an exact quotient is the quotient.')
    dn, rn = qctx(w, A0)
    md = w.s([], 'simpr', '( %s -> %s )' % (A0, MD))
    dvd, qz, fl, qn0 = qbasics(w, A0, dn, rn, md)
    idx = [i for i, l in enumerate(w.lines) if l.startswith(fl + ':')][0]
    w.lines[idx] = w.lines[idx].replace(fl + ':', 'qed:', 1)
    w.lines = w.lines[:idx + 1]
    run(w)

if not only or 'divoutqcl' in only:
    w = W('divoutqcl', 'The floor of an exact quotient is a nonnegative integer.')
    dn, rn = qctx(w, A0)
    md = w.s([], 'simpr', '( %s -> %s )' % (A0, MD))
    dvd, qz, fl, qn0 = qbasics(w, A0, dn, rn, md)
    idx = [i for i, l in enumerate(w.lines) if l.startswith(qn0 + ':')][0]
    w.lines[idx] = w.lines[idx].replace(qn0 + ':', 'qed:', 1)
    w.lines = w.lines[:idx + 1]
    run(w)

if not only or 'divoutqmul' in only:
    w = W('divoutqmul', 'The divisor times the exact quotient is the dividend.')
    dn, rn = qctx(w, A0)
    md = w.s([], 'simpr', '( %s -> %s )' % (A0, MD))
    dvd, qz, fl, qn0 = qbasics(w, A0, dn, rn, md)
    dc = w.s([w.s([dn], 'nnred', '( %s -> D e. RR )' % A0)], 'recnd', '( %s -> D e. CC )' % A0)
    rc = w.s([rn], 'nn0cnd', '( %s -> R e. CC )' % A0)
    dne = w.s([dn], 'nnne0d', '( %s -> D =/= 0 )' % A0)
    cn = w.s([rc, dc, dne, w.inst('divcan2')], 'syl3anc', '( %s -> ( D x. ( R / D ) ) = R )' % A0)
    w.qed([w.s([fl], 'oveq2d', '( %s -> ( D x. %s ) = ( D x. ( R / D ) ) )' % (A0, DQ)), cn], 'eqtrd',
          '( %s -> ( D x. %s ) = R )' % (A0, DQ))
    run(w)

if not only or 'divoutqdvd' in only:
    w = W('divoutqdvd', 'The exact quotient divides the dividend.')
    dn, rn = qctx(w, A0)
    md = w.s([], 'simpr', '( %s -> %s )' % (A0, MD))
    dvd, qz, fl, qn0 = qbasics(w, A0, dn, rn, md)
    mul = w.s([], 'divoutqmul', '( %s -> ( D x. %s ) = R )' % (A0, DQ))
    d2 = w.s([w.s([dn], 'nnzd', '( %s -> D e. ZZ )' % A0), w.s([qn0], 'nn0zd', '( %s -> %s e. ZZ )' % (A0, DQ)), w.inst('dvdsmul2')], 'syl2anc',
             '( %s -> %s || ( D x. %s ) )' % (A0, DQ, DQ))
    w.qed([d2, mul], 'breqtrd', '( %s -> %s || R )' % (A0, DQ))
    run(w)

A1 = '( ( D e. NN /\\ R e. NN0 ) /\\ ( %s /\\ 2 <_ D ) )' % MD
if not only or 'divoutqdbl' in only:
    w = W('divoutqdbl', 'Each successful division at least halves the dividend (Lean: the halving step of divOut_cost).')
    dn, rn = qctx(w, A1)
    md = w.s([], 'simprl', '( %s -> %s )' % (A1, MD))
    d2h = w.s([], 'simprr', '( %s -> 2 <_ D )' % A1)
    dvd, qz, fl, qn0 = qbasics(w, A1, dn, rn, md)
    mul = w.s([w.s([w.s([dn, rn], 'jca', '( %s -> ( D e. NN /\\ R e. NN0 ) )' % A1), md], 'jca',
                   '( %s -> ( ( D e. NN /\\ R e. NN0 ) /\\ %s ) )' % (A1, MD)), w.inst('divoutqmul')], 'syl',
              '( %s -> ( D x. %s ) = R )' % (A1, DQ))
    qr = w.s([qn0], 'nn0red', '( %s -> %s e. RR )' % (A1, DQ))
    qg = w.s([qn0], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A1, DQ))
    dr = w.s([dn], 'nnred', '( %s -> D e. RR )' % A1)
    li = lin.nlinarith(w, A1, [d2h, qg], '( %s x. 2 ) <_ ( D x. %s )' % (DQ, DQ), leaves={DQ: qr, 'D': dr})
    w.qed([li, mul], 'breqtrd', '( %s -> ( %s x. 2 ) <_ R )' % (A1, DQ))
    run(w)

A2 = '( ( D e. NN /\\ R e. NN0 ) /\\ ( %s /\\ 2 <_ D ) /\\ 1 <_ R )' % MD
if not only or 'divoutqpos' in only:
    w = W('divoutqpos', 'A successful division of a positive dividend leaves a positive quotient.')
    dn = w.s([], 'simp1l', '( %s -> D e. NN )' % A2)
    rn = w.s([], 'simp1r', '( %s -> R e. NN0 )' % A2)
    md = w.s([], 'simp2l', '( %s -> %s )' % (A2, MD))
    r1 = w.s([], 'simp3', '( %s -> 1 <_ R )' % A2)
    B = '( ( D e. NN /\\ R e. NN0 ) /\\ %s )' % MD
    cj = w.s([w.s([dn, rn], 'jca', '( %s -> ( D e. NN /\\ R e. NN0 ) )' % A2), md], 'jca', '( %s -> %s )' % (A2, B))
    qn0 = w.s([cj, w.inst('divoutqcl')], 'syl', '( %s -> %s e. NN0 )' % (A2, DQ))
    mul = w.s([cj, w.inst('divoutqmul')], 'syl', '( %s -> ( D x. %s ) = R )' % (A2, DQ))
    # if DQ = 0 then R = 0, contradicting 1 <_ R
    C = '( %s /\\ %s = 0 )' % (A2, DQ)
    z = w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (C, DQ))], 'oveq2d', '( %s -> ( D x. %s ) = ( D x. 0 ) )' % (C, DQ)),
             w.s([w.s([w.s([w.s([dn], 'adantr', '( %s -> D e. NN )' % C)], 'nnred', '( %s -> D e. RR )' % C)], 'recnd', '( %s -> D e. CC )' % C),
                  w.inst('mul01')], 'syl', '( %s -> ( D x. 0 ) = 0 )' % C)], 'eqtrd', '( %s -> ( D x. %s ) = 0 )' % (C, DQ))
    r0 = w.s([w.s([mul], 'adantr', '( %s -> ( D x. %s ) = R )' % (C, DQ)), z], 'eqtr3d', '( %s -> R = 0 )' % C)
    le10 = w.s([w.s([r1], 'adantr', '( %s -> 1 <_ R )' % C), r0], 'breqtrd', '( %s -> 1 <_ 0 )' % C)
    n10 = w.s([w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % C),
               w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % C),
                    w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % C)], 'ltnled',
                   '( %s -> ( 0 < 1 <-> -. 1 <_ 0 ) )' % C)], 'mpbid', '( %s -> -. 1 <_ 0 )' % C)
    nz = w.s([le10, n10], 'pm2.65da', '( %s -> -. %s = 0 )' % (A2, DQ))
    ne = w.s([nz], 'neqned', '( %s -> %s =/= 0 )' % (A2, DQ))
    nn = w.s([qn0, ne, w.inst('elnnne0')], 'sylanbrc', '( %s -> %s e. NN )' % (A2, DQ))
    w.qed([nn], 'nnge1d', '( %s -> 1 <_ %s )' % (A2, DQ))
    run(w)

DOV = lambda r, f: '( ( D DivOut %s ) ` %s )' % (r, f)
F1 = lambda r, f: '( 1st ` %s )' % DOV(r, f)
F2 = lambda r, f: '( 2nd ` %s )' % DOV(r, f)
DQr = '( |_ ` ( r / D ) )'
MDr = '( r mod D ) = 0'

def dofam(label, OUT, INN, basefn, truefn, falsefn, desc, finalfn, only=()):
    """base, step, fuelind and assembly for a divOut-shaped fuel recursion whose
    induction property is ( OUT -> A. r e. NN0 INN( r , f ) )."""
    PHI = lambda f: '( %s -> A. r e. NN0 %s )' % (OUT, INN('r', f))
    def sb(w, frm, to, f):
        idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
        st, new = w.wcongr(INN(frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
        assert new == INN(to, f), '\n%s\n%s' % (new, INN(to, f))
        return st
    ok = True
    if not only or label + 'b' in only:
        w = W(label + 'b', 'Base of the induction for ' + label + '.')
        B0 = '( %s /\\ r e. NN0 )' % OUT
        st = basefn(w, B0)
        w.qed([st], 'ralrimiva', PHI('0'))
        ok = w.run() and ok
    if not only or label + 's' in only:
        w = W(label + 's', 'Step of the induction for ' + label + '.')
        IHD = 'A. r e. NN0 %s' % INN('r', 'F')
        IHC = 'A. c e. NN0 %s' % INN('c', 'F')
        A = '( F e. NN0 /\\ ( %s -> %s ) )' % (OUT, IHD)
        AC = '( F e. NN0 /\\ ( %s -> %s ) )' % (OUT, IHC)
        cbv = w.s([sb(w, 'r', 'c', 'F')], 'cbvralvw', '( %s <-> %s )' % (IHD, IHC))
        conv = w.s([w.s([], 'simpl', '( %s -> F e. NN0 )' % A),
                    w.s([w.s([], 'simpr', '( %s -> ( %s -> %s ) )' % (A, OUT, IHD)),
                         w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd',
                             '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))], 'syld', '( %s -> ( %s -> %s ) )' % (A, OUT, IHC))], 'jca',
                   '( %s -> %s )' % (A, AC))
        B1 = '( %s /\\ %s )' % (AC, OUT)
        B = '( %s /\\ r e. NN0 )' % B1
        ctx = {}
        ctx['fn'] = w.s([], 'simplll', '( %s -> F e. NN0 )' % B)
        ctx['ih'] = w.s([], 'simpllr', '( %s -> ( %s -> %s ) )' % (B, OUT, IHC))
        ctx['out'] = w.s([], 'simplr', '( %s -> %s )' % (B, OUT))
        ctx['rn'] = w.s([], 'simpr', '( %s -> r e. NN0 )' % B)
        ctx['ihc'] = w.s([ctx['ih'], ctx['out']], 'mpd', '( %s -> %s )' % (B, IHC))
        ctx['sb'] = sb
        ctx['INN'] = INN
        T = '( %s /\\ %s )' % (B, MDr)
        F_ = '( %s /\\ -. %s )' % (B, MDr)
        st1 = truefn(w, B, T, ctx)
        st2 = falsefn(w, B, F_, ctx)
        main = w.s([st1, st2], 'pm2.61dan', '( %s -> %s )' % (B, INN('r', '( F + 1 )')))
        w.qed([conv, w.s([w.s([main], 'ralrimiva', '( %s -> A. r e. NN0 %s )' % (B1, INN('r', '( F + 1 )')))], 'ex',
                         '( %s -> %s )' % (AC, PHI('( F + 1 )')))], 'syl', '( %s -> %s )' % (A, PHI('( F + 1 )')))
        ok = w.run() and ok
    if not only or label + 'l' in only:
        w = W(label + 'l', desc + ' (as the induction on the fuel delivers it)')
        st, pt = fuelind(w, PHI('f'), 'F', label + 'b', label + 's', fvar='f')
        w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
        ok = w.run() and ok
    if not only or label in only:
        w = W(label, desc)
        finalfn(w, PHI, INN, sb)
        ok = w.run() and ok
    return ok

def divval(w, B, dn, rn, fn):
    """( B -> DOV(r,'( F + 1 )') = if ( MDr , <. F1(DQr,F) , ( F2(DQr,F) + 1 ) >. , <. r , 0 >. ) )"""
    return w.s([w.s([dn, rn], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % B), fn, w.inst('divoutp1')], 'syl2anc',
               '( %s -> %s = if ( %s , <. %s , ( %s + 1 ) >. , <. r , 0 >. ) )' % (B, DOV('r', '( F + 1 )'), MDr, F1(DQr, 'F'), F2(DQr, 'F')))

def divzero(w, B, dn, rn):
    return w.s([dn, rn, w.inst('divout0')], 'syl2anc', '( %s -> %s = <. r , 0 >. )' % (B, DOV('r', '0')))

def divcl(w, A, r, f, dn, rnst, fnst):
    return w.s([w.s([dn, rnst], 'jca', '( %s -> ( D e. NN /\\ %s e. NN0 ) )' % (A, r)), fnst, w.inst('divoutcl')], 'syl2anc',
               '( %s -> %s e. ( NN0 X. NN0 ) )' % (A, DOV(r, f)))

def qhyp(w, A, dn, rn, mdst):
    """( A -> ( ( D e. NN /\\ r e. NN0 ) /\\ ( r mod D ) = 0 ) )"""
    return w.s([w.s([dn, rn], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % A), mdst], 'jca',
               '( %s -> ( ( D e. NN /\\ r e. NN0 ) /\\ %s ) )' % (A, MDr))

# ======================================================================= divoutdvd
OUT = 'D e. NN'
INN = lambda r, f: '%s || %s' % (F1(r, f), r)
def _b(w, B0):
    dn = w.s([], 'simpl', '( %s -> D e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    v = divzero(w, B0, dn, rn)
    p1 = projeq(w, B0, DOV('r', '0'), v, 'r', '0', w.s([rn], 'elexd', '( %s -> r e. _V )' % B0),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % B0), 1)
    rid = w.s([w.s([rn], 'nn0zd', '( %s -> r e. ZZ )' % B0), w.inst('iddvds')], 'syl', '( %s -> r || r )' % B0)
    return w.s([p1, rid], 'eqbrtrd', '( %s -> %s )' % (B0, INN('r', '0')))
def _t(w, B, T, ctx):
    dn = w.s([ctx['out']], 'adantr', '( %s -> D e. NN )' % T)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % T)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % T)
    md = w.s([], 'simpr', '( %s -> %s )' % (T, MDr))
    v = divval(w, T, dn, rn, fn)
    vt, vf = ifproj(w, T, DOV('r', '( F + 1 )'), v, MDr, '<. %s , ( %s + 1 ) >.' % (F1(DQr, 'F'), F2(DQr, 'F')), '<. r , 0 >.')
    # under T the condition already holds, so use iftrued directly
    it = w.s([md], 'iftrued', '( %s -> if ( %s , <. %s , ( %s + 1 ) >. , <. r , 0 >. ) = <. %s , ( %s + 1 ) >. )' % (T, MDr, F1(DQr, 'F'), F2(DQr, 'F'), F1(DQr, 'F'), F2(DQr, 'F')))
    val = w.s([v, it], 'eqtrd', '( %s -> %s = <. %s , ( %s + 1 ) >. )' % (T, DOV('r', '( F + 1 )'), F1(DQr, 'F'), F2(DQr, 'F')))
    qh = qhyp(w, T, dn, rn, md)
    qn = w.s([qh, w.inst('divoutqcl')], 'syl', '( %s -> %s e. NN0 )' % (T, DQr))
    cl = divcl(w, T, DQr, 'F', dn, qn, fn)
    a1, b1 = paircl(w, T, DOV(DQr, 'F'), cl, 'NN0', 'NN0')
    b1p = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (T, F2(DQr, 'F')))
    p1 = projeq(w, T, DOV('r', '( F + 1 )'), val, F1(DQr, 'F'), '( %s + 1 )' % F2(DQr, 'F'), a1, b1p, 1)
    ihq = w.s([ctx['sb'](w, 'c', DQr, 'F'), w.s([ctx['ihc']], 'adantr', '( %s -> A. c e. NN0 %s )' % (T, INN('c', 'F'))), qn], 'rspcdva',
              '( %s -> %s )' % (T, INN(DQr, 'F')))
    qd = w.s([qh, w.inst('divoutqdvd')], 'syl', '( %s -> %s || r )' % (T, DQr))
    tr = w.s([w.s([w.s([a1], 'nn0zd', '( %s -> %s e. ZZ )' % (T, F1(DQr, 'F'))), w.s([qn], 'nn0zd', '( %s -> %s e. ZZ )' % (T, DQr)),
                   w.s([rn], 'nn0zd', '( %s -> r e. ZZ )' % T)], '3jca',
                  '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ r e. ZZ ) )' % (T, F1(DQr, 'F'), DQr)), w.inst('dvdstr')], 'syl',
             '( %s -> ( ( %s /\\ %s || r ) -> %s || r ) )' % (T, INN(DQr, 'F'), DQr, F1(DQr, 'F')))
    dd = w.s([tr, w.s([ihq, qd], 'jca', '( %s -> ( %s /\\ %s || r ) )' % (T, INN(DQr, 'F'), DQr))], 'mpd',
             '( %s -> %s || r )' % (T, F1(DQr, 'F')))
    return w.s([p1, dd], 'eqbrtrd', '( %s -> %s )' % (T, INN('r', '( F + 1 )')))
def _f(w, B, F_, ctx):
    dn = w.s([ctx['out']], 'adantr', '( %s -> D e. NN )' % F_)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % F_)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % F_)
    nmd = w.s([], 'simpr', '( %s -> -. %s )' % (F_, MDr))
    v = divval(w, F_, dn, rn, fn)
    iff = w.s([nmd], 'iffalsed', '( %s -> if ( %s , <. %s , ( %s + 1 ) >. , <. r , 0 >. ) = <. r , 0 >. )' % (F_, MDr, F1(DQr, 'F'), F2(DQr, 'F')))
    val = w.s([v, iff], 'eqtrd', '( %s -> %s = <. r , 0 >. )' % (F_, DOV('r', '( F + 1 )')))
    p1 = projeq(w, F_, DOV('r', '( F + 1 )'), val, 'r', '0', w.s([rn], 'elexd', '( %s -> r e. _V )' % F_),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % F_), 1)
    rid = w.s([w.s([rn], 'nn0zd', '( %s -> r e. ZZ )' % F_), w.inst('iddvds')], 'syl', '( %s -> r || r )' % F_)
    return w.s([p1, rid], 'eqbrtrd', '( %s -> %s )' % (F_, INN('r', '( F + 1 )')))
def _fin(w, PHI, INN, sb):
    T = '( D e. NN /\\ R e. NN0 /\\ F e. NN0 )'
    dn = w.s([], 'simp1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simp2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simp3', '( %s -> F e. NN0 )' % T)
    ral = w.s([w.s([fn, w.inst('divoutdvdl')], 'syl', '( %s -> %s )' % (T, PHI('F'))), dn], 'mpd',
              '( %s -> A. r e. NN0 %s )' % (T, INN('r', 'F')))
    w.qed([sb(w, 'r', 'R', 'F'), ral, rn], 'rspcdva', '( %s -> %s )' % (T, INN('R', 'F')))
dofam('divoutdvd', OUT, INN, _b, _t, _f, 'The divide-out loop returns a divisor of its input (Lean: divOut_dvd).', _fin, only=only)

THEN = '<. %s , ( %s + 1 ) >.' % (F1(DQr, 'F'), F2(DQr, 'F'))
ELSE = '<. r , 0 >.'
IFV = 'if ( %s , %s , %s )' % (MDr, THEN, ELSE)

def branch(w, A, dn, rn, fn, true):
    """the value of DOV(r,'( F + 1 )') on the branch A (which carries MDr or its negation)"""
    v = divval(w, A, dn, rn, fn)
    if true:
        i = w.s([w.s([], 'simpr', '( %s -> %s )' % (A, MDr))], 'iftrued', '( %s -> %s = %s )' % (A, IFV, THEN))
        return w.s([v, i], 'eqtrd', '( %s -> %s = %s )' % (A, DOV('r', '( F + 1 )'), THEN))
    i = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (A, MDr))], 'iffalsed', '( %s -> %s = %s )' % (A, IFV, ELSE))
    return w.s([v, i], 'eqtrd', '( %s -> %s = %s )' % (A, DOV('r', '( F + 1 )'), ELSE))

def rex(w, A, rn):
    return w.s([rn], 'elexd', '( %s -> r e. _V )' % A)
def zex(w, A):
    return w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A)

# ======================================================================= divoutndvd
OUT2 = '( D e. NN /\\ 2 <_ D )'
INN2 = lambda r, f: '( ( 1 <_ %s /\\ %s <_ %s ) -> -. D || %s )' % (r, r, f, F1(r, f))
def _b(w, B0):
    dn = w.s([], 'simpll', '( %s -> D e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    C = '( %s /\\ ( 1 <_ r /\\ r <_ 0 ) )' % B0
    rr = w.s([w.s([rn], 'adantr', '( %s -> r e. NN0 )' % C)], 'nn0red', '( %s -> r e. RR )' % C)
    bad = lin.linarith(w, C, [w.s([], 'simprl', '( %s -> 1 <_ r )' % C), w.s([], 'simprr', '( %s -> r <_ 0 )' % C)], '1 <_ 0', leaves={'r': rr})
    n10 = w.s([w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % C),
               w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % C),
                    w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % C)], 'ltnled', '( %s -> ( 0 < 1 <-> -. 1 <_ 0 ) )' % C)], 'mpbid',
              '( %s -> -. 1 <_ 0 )' % C)
    return w.s([w.s([bad, n10], 'pm2.21dd', '( %s -> -. D || %s )' % (C, F1('r', '0')))], 'ex', '( %s -> %s )' % (B0, INN2('r', '0')))
def _t(w, B, T, ctx):
    out = w.s([ctx['out']], 'adantr', '( %s -> %s )' % (T, OUT2))
    dn = w.s([out], 'simpld', '( %s -> D e. NN )' % T)
    d2 = w.s([out], 'simprd', '( %s -> 2 <_ D )' % T)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % T)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % T)
    md = w.s([], 'simpr', '( %s -> %s )' % (T, MDr))
    val = branch(w, T, dn, rn, fn, True)
    U = '( %s /\\ ( 1 <_ r /\\ r <_ ( F + 1 ) ) )' % T
    dnU = w.s([dn], 'adantr', '( %s -> D e. NN )' % U)
    d2U = w.s([d2], 'adantr', '( %s -> 2 <_ D )' % U)
    rnU = w.s([rn], 'adantr', '( %s -> r e. NN0 )' % U)
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    mdU = w.s([md], 'adantr', '( %s -> %s )' % (U, MDr))
    r1 = w.s([], 'simprl', '( %s -> 1 <_ r )' % U)
    rf = w.s([], 'simprr', '( %s -> r <_ ( F + 1 ) )' % U)
    H1 = '( ( D e. NN /\\ r e. NN0 ) /\\ %s )' % MDr
    cj = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U), mdU], 'jca', '( %s -> %s )' % (U, H1))
    qn = w.s([cj, w.inst('divoutqcl')], 'syl', '( %s -> %s e. NN0 )' % (U, DQr))
    H2 = '( ( D e. NN /\\ r e. NN0 ) /\\ ( %s /\\ 2 <_ D ) )' % MDr
    cj2 = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U),
               w.s([mdU, d2U], 'jca', '( %s -> ( %s /\\ 2 <_ D ) )' % (U, MDr))], 'jca', '( %s -> %s )' % (U, H2))
    dbl = w.s([cj2, w.inst('divoutqdbl')], 'syl', '( %s -> ( %s x. 2 ) <_ r )' % (U, DQr))
    H3 = '( ( D e. NN /\\ r e. NN0 ) /\\ ( %s /\\ 2 <_ D ) /\\ 1 <_ r )' % MDr
    cj3 = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U),
               w.s([mdU, d2U], 'jca', '( %s -> ( %s /\\ 2 <_ D ) )' % (U, MDr)), r1], '3jca', '( %s -> %s )' % (U, H3))
    q1 = w.s([cj3, w.inst('divoutqpos')], 'syl', '( %s -> 1 <_ %s )' % (U, DQr))
    qr = w.s([qn], 'nn0red', '( %s -> %s e. RR )' % (U, DQr))
    rr = w.s([rnU], 'nn0red', '( %s -> r e. RR )' % U)
    fr = w.s([fnU], 'nn0red', '( %s -> F e. RR )' % U)
    qlt = lin.linarith(w, U, [dbl, q1, rf], '%s < ( F + 1 )' % DQr, leaves={DQr: qr, 'r': rr, 'F': fr})
    qle = w.s([w.s([w.s([qn], 'nn0zd', '( %s -> %s e. ZZ )' % (U, DQr)), w.s([fnU], 'nn0zd', '( %s -> F e. ZZ )' % U), w.inst('zleltp1')],
                   'syl2anc', '( %s -> ( %s <_ F <-> %s < ( F + 1 ) ) )' % (U, DQr, DQr)), qlt], 'mpbird', '( %s -> %s <_ F )' % (U, DQr))
    ihq = w.s([ctx['sb'](w, 'c', DQr, 'F'), w.s([ctx['ihc']], 'ad2antrr', '( %s -> A. c e. NN0 %s )' % (U, INN2('c', 'F'))), qn], 'rspcdva',
              '( %s -> %s )' % (U, INN2(DQr, 'F')))
    nd = w.s([ihq, w.s([q1, qle], 'jca', '( %s -> ( 1 <_ %s /\\ %s <_ F ) )' % (U, DQr, DQr))], 'mpd',
             '( %s -> -. D || %s )' % (U, F1(DQr, 'F')))
    valU = w.s([val], 'adantr', '( %s -> %s = %s )' % (U, DOV('r', '( F + 1 )'), THEN))
    cl = divcl(w, U, DQr, 'F', dnU, qn, fnU)
    a1, b1 = paircl(w, U, DOV(DQr, 'F'), cl, 'NN0', 'NN0')
    b1p = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (U, F2(DQr, 'F')))
    p1 = projeq(w, U, DOV('r', '( F + 1 )'), valU, F1(DQr, 'F'), '( %s + 1 )' % F2(DQr, 'F'), a1, b1p, 1)
    ndr = w.s([w.s([p1], 'breq2d', '( %s -> ( D || %s <-> D || %s ) )' % (U, F1('r', '( F + 1 )'), F1(DQr, 'F'))), nd], 'mtbird',
              '( %s -> -. D || %s )' % (U, F1('r', '( F + 1 )')))
    return w.s([ndr], 'ex', '( %s -> %s )' % (T, INN2('r', '( F + 1 )')))
def _f(w, B, F_, ctx):
    out = w.s([ctx['out']], 'adantr', '( %s -> %s )' % (F_, OUT2))
    dn = w.s([out], 'simpld', '( %s -> D e. NN )' % F_)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % F_)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % F_)
    nmd = w.s([], 'simpr', '( %s -> -. %s )' % (F_, MDr))
    val = branch(w, F_, dn, rn, fn, False)
    p1 = projeq(w, F_, DOV('r', '( F + 1 )'), val, 'r', '0', rex(w, F_, rn), zex(w, F_), 1)
    ndr = w.s([nmd, w.s([dn, w.s([rn], 'nn0zd', '( %s -> r e. ZZ )' % F_), w.inst('dvdsval3')], 'syl2anc',
                        '( %s -> ( D || r <-> %s ) )' % (F_, MDr))], 'mtbird', '( %s -> -. D || r )' % F_)
    nd2 = w.s([w.s([p1], 'breq2d', '( %s -> ( D || %s <-> D || r ) )' % (F_, F1('r', '( F + 1 )'))), ndr], 'mtbird',
              '( %s -> -. D || %s )' % (F_, F1('r', '( F + 1 )')))
    return w.s([nd2], 'a1d', '( %s -> %s )' % (F_, INN2('r', '( F + 1 )')))
def _fin(w, PHI, INN, sb):
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ ( 2 <_ D /\\ 1 <_ R /\\ R <_ F ) )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    d2 = w.s([], 'simpr1', '( %s -> 2 <_ D )' % T)
    r1 = w.s([], 'simpr2', '( %s -> 1 <_ R )' % T)
    rf = w.s([], 'simpr3', '( %s -> R <_ F )' % T)
    ral = w.s([w.s([fn, w.inst('divoutndvdl')], 'syl', '( %s -> %s )' % (T, PHI('F'))),
               w.s([dn, d2], 'jca', '( %s -> %s )' % (T, OUT2))], 'mpd', '( %s -> A. r e. NN0 %s )' % (T, INN('r', 'F')))
    inst = w.s([sb(w, 'r', 'R', 'F'), ral, rn], 'rspcdva', '( %s -> %s )' % (T, INN('R', 'F')))
    w.qed([inst, w.s([r1, rf], 'jca', '( %s -> ( 1 <_ R /\\ R <_ F ) )' % T)], 'mpd', '( %s -> -. D || %s )' % (T, F1('R', 'F')))
dofam('divoutndvd', OUT2, INN2, _b, _t, _f, 'The divide-out loop leaves no factor of the divisor (Lean: divOut_not_dvd).', _fin, only=only)

# ======================================================================= divoutcost
INN3 = lambda r, f: '( 1 <_ %s -> ( %s + %s ) <_ %s )' % (r, F2(r, f), LG(F1(r, f)), LG(r))
def zerocase(w, A, dn, rn, val, r, f):
    """the ( 0 + LG( r ) ) <_ LG( r ) bound when the loop returns <. r , 0 >."""
    p1 = projeq(w, A, DOV('r', f), val, 'r', '0', rex(w, A, rn), zex(w, A), 1)
    p2 = projeq(w, A, DOV('r', f), val, 'r', '0', rex(w, A, rn), zex(w, A), 2)
    lgn = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), rn, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, LG('r')))
    lgc = w.s([lgn], 'nn0cnd', '( %s -> %s e. CC )' % (A, LG('r')))
    e1, _ = rweq(w, A, '%s' % LG(F1('r', f)), F1('r', f), 'r', p1)
    sum_ = w.s([p2, e1], 'oveq12d', '( %s -> ( %s + %s ) = ( 0 + %s ) )' % (A, F2('r', f), LG(F1('r', f)), LG('r')))
    zz = w.s([lgc], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A, LG('r'), LG('r')))
    return w.s([w.s([sum_, zz], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A, F2('r', f), LG(F1('r', f)), LG('r'))),
                w.s([], 'leidd', '( %s -> %s <_ %s )' % (A, LG('r'), LG('r')))], 'eqbrtrd',
               '( %s -> ( %s + %s ) <_ %s )' % (A, F2('r', f), LG(F1('r', f)), LG('r')))
def _b(w, B0):
    dn = w.s([], 'simpll', '( %s -> D e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    val = divzero(w, B0, dn, rn)
    return w.s([zerocase(w, B0, dn, rn, val, 'r', '0')], 'a1d', '( %s -> %s )' % (B0, INN3('r', '0')))
def _t(w, B, T, ctx):
    out = w.s([ctx['out']], 'adantr', '( %s -> %s )' % (T, OUT2))
    dn = w.s([out], 'simpld', '( %s -> D e. NN )' % T)
    d2 = w.s([out], 'simprd', '( %s -> 2 <_ D )' % T)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % T)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % T)
    md = w.s([], 'simpr', '( %s -> %s )' % (T, MDr))
    val = branch(w, T, dn, rn, fn, True)
    U = '( %s /\\ 1 <_ r )' % T
    dnU = w.s([dn], 'adantr', '( %s -> D e. NN )' % U)
    d2U = w.s([d2], 'adantr', '( %s -> 2 <_ D )' % U)
    rnU = w.s([rn], 'adantr', '( %s -> r e. NN0 )' % U)
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    mdU = w.s([md], 'adantr', '( %s -> %s )' % (U, MDr))
    r1 = w.s([], 'simpr', '( %s -> 1 <_ r )' % U)
    H1 = '( ( D e. NN /\\ r e. NN0 ) /\\ %s )' % MDr
    cj = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U), mdU], 'jca', '( %s -> %s )' % (U, H1))
    qn = w.s([cj, w.inst('divoutqcl')], 'syl', '( %s -> %s e. NN0 )' % (U, DQr))
    H2 = '( ( D e. NN /\\ r e. NN0 ) /\\ ( %s /\\ 2 <_ D ) )' % MDr
    cj2 = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U),
               w.s([mdU, d2U], 'jca', '( %s -> ( %s /\\ 2 <_ D ) )' % (U, MDr))], 'jca', '( %s -> %s )' % (U, H2))
    dbl = w.s([cj2, w.inst('divoutqdbl')], 'syl', '( %s -> ( %s x. 2 ) <_ r )' % (U, DQr))
    H3 = '( ( D e. NN /\\ r e. NN0 ) /\\ ( %s /\\ 2 <_ D ) /\\ 1 <_ r )' % MDr
    cj3 = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U),
               w.s([mdU, d2U], 'jca', '( %s -> ( %s /\\ 2 <_ D ) )' % (U, MDr)), r1], '3jca', '( %s -> %s )' % (U, H3))
    q1 = w.s([cj3, w.inst('divoutqpos')], 'syl', '( %s -> 1 <_ %s )' % (U, DQr))
    qnn = w.s([qn, q1, w.inst('elnnnn0c')], 'sylanbrc', '( %s -> %s e. NN )' % (U, DQr))
    rnn = w.s([rnU, r1, w.inst('elnnnn0c')], 'sylanbrc', '( %s -> r e. NN )' % U)
    uz2 = w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % U)
    le22 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.inst('leid')], 'ax-mp', '2 <_ 2')], 'a1i', '( %s -> 2 <_ 2 )' % U)
    b2 = w.s([w.s([uz2, uz2, le22], '3jca', '( %s -> ( 2 e. ZZ /\\ 2 e. ZZ /\\ 2 <_ 2 ) )' % U), w.inst('eluz2')], 'sylibr',
             '( %s -> 2 e. ( ZZ>= ` 2 ) )' % U)
    suc = w.s([w.s([w.s([b2, w.s([qnn, rnn], 'jca', '( %s -> ( %s e. NN /\\ r e. NN ) )' % (U, DQr))], 'jca',
                        '( %s -> ( 2 e. ( ZZ>= ` 2 ) /\\ ( %s e. NN /\\ r e. NN ) ) )' % (U, DQr)), dbl], 'jca',
                   '( %s -> ( ( 2 e. ( ZZ>= ` 2 ) /\\ ( %s e. NN /\\ r e. NN ) ) /\\ ( %s x. 2 ) <_ r ) )' % (U, DQr, DQr)),
               w.inst('nlogsuc')], 'syl', '( %s -> ( %s + 1 ) <_ %s )' % (U, LG(DQr), LG('r')))
    ihq = w.s([ctx['sb'](w, 'c', DQr, 'F'), w.s([ctx['ihc']], 'ad2antrr', '( %s -> A. c e. NN0 %s )' % (U, INN3('c', 'F'))), qn], 'rspcdva',
              '( %s -> %s )' % (U, INN3(DQr, 'F')))
    ihv = w.s([ihq, q1], 'mpd', '( %s -> ( %s + %s ) <_ %s )' % (U, F2(DQr, 'F'), LG(F1(DQr, 'F')), LG(DQr)))
    valU = w.s([val], 'adantr', '( %s -> %s = %s )' % (U, DOV('r', '( F + 1 )'), THEN))
    cl = divcl(w, U, DQr, 'F', dnU, qn, fnU)
    a1, b1 = paircl(w, U, DOV(DQr, 'F'), cl, 'NN0', 'NN0')
    b1p = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (U, F2(DQr, 'F')))
    p1 = projeq(w, U, DOV('r', '( F + 1 )'), valU, F1(DQr, 'F'), '( %s + 1 )' % F2(DQr, 'F'), a1, b1p, 1)
    p2 = projeq(w, U, DOV('r', '( F + 1 )'), valU, F1(DQr, 'F'), '( %s + 1 )' % F2(DQr, 'F'), a1, b1p, 2)
    # closures for linarith
    lgq = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % U), qn, w.inst('nlogcl')], 'syl2anc',
                   '( %s -> %s e. NN0 )' % (U, LG(DQr)))], 'nn0red', '( %s -> %s e. RR )' % (U, LG(DQr)))
    lgr = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % U), rnU, w.inst('nlogcl')], 'syl2anc',
                   '( %s -> %s e. NN0 )' % (U, LG('r')))], 'nn0red', '( %s -> %s e. RR )' % (U, LG('r')))
    lgf = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % U), a1, w.inst('nlogcl')], 'syl2anc',
                   '( %s -> %s e. NN0 )' % (U, LG(F1(DQr, 'F'))))], 'nn0red', '( %s -> %s e. RR )' % (U, LG(F1(DQr, 'F'))))
    b1r = w.s([b1], 'nn0red', '( %s -> %s e. RR )' % (U, F2(DQr, 'F')))
    li = lin.linarith(w, U, [ihv, suc], '( ( %s + 1 ) + %s ) <_ %s' % (F2(DQr, 'F'), LG(F1(DQr, 'F')), LG('r')),
                      leaves={F2(DQr, 'F'): b1r, LG(F1(DQr, 'F')): lgf, LG(DQr): lgq, LG('r'): lgr})
    e1, _ = rweq(w, U, LG(F1('r', '( F + 1 )')), F1('r', '( F + 1 )'), F1(DQr, 'F'), p1)
    sum_ = w.s([p2, e1], 'oveq12d', '( %s -> ( %s + %s ) = ( ( %s + 1 ) + %s ) )' % (U, F2('r', '( F + 1 )'), LG(F1('r', '( F + 1 )')), F2(DQr, 'F'), LG(F1(DQr, 'F'))))
    return w.s([w.s([sum_, li], 'eqbrtrd', '( %s -> ( %s + %s ) <_ %s )' % (U, F2('r', '( F + 1 )'), LG(F1('r', '( F + 1 )')), LG('r')))], 'ex',
               '( %s -> %s )' % (T, INN3('r', '( F + 1 )')))
def _f(w, B, F_, ctx):
    out = w.s([ctx['out']], 'adantr', '( %s -> %s )' % (F_, OUT2))
    dn = w.s([out], 'simpld', '( %s -> D e. NN )' % F_)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % F_)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % F_)
    val = branch(w, F_, dn, rn, fn, False)
    return w.s([zerocase(w, F_, dn, rn, val, 'r', '( F + 1 )')], 'a1d', '( %s -> %s )' % (F_, INN3('r', '( F + 1 )')))
def _fin(w, PHI, INN, sb):
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ ( 2 <_ D /\\ 1 <_ R ) )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    d2 = w.s([], 'simprl', '( %s -> 2 <_ D )' % T)
    r1 = w.s([], 'simprr', '( %s -> 1 <_ R )' % T)
    ral = w.s([w.s([fn, w.inst('divoutcostl')], 'syl', '( %s -> %s )' % (T, PHI('F'))),
               w.s([dn, d2], 'jca', '( %s -> %s )' % (T, OUT2))], 'mpd', '( %s -> A. r e. NN0 %s )' % (T, INN('r', 'F')))
    inst = w.s([sb(w, 'r', 'R', 'F'), ral, rn], 'rspcdva', '( %s -> %s )' % (T, INN('R', 'F')))
    w.qed([inst, r1], 'mpd', '( %s -> ( %s + %s ) <_ %s )' % (T, F2('R', 'F'), LG(F1('R', 'F')), LG('R')))
dofam('divoutcost', OUT2, INN3, _b, _t, _f, 'The cost of the divide-out loop (Lean: divOut_cost).', _fin, only=only)

# ======================================================================= divoutprm
OUT4 = '( D e. NN /\\ P e. Prime )'
INN4 = lambda r, f: '( P || %s -> ( P || %s \\/ P || D ) )' % (r, F1(r, f))
def _b(w, B0):
    dn = w.s([], 'simpll', '( %s -> D e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    val = divzero(w, B0, dn, rn)
    p1 = projeq(w, B0, DOV('r', '0'), val, 'r', '0', rex(w, B0, rn), zex(w, B0), 1)
    U = '( %s /\\ P || r )' % B0
    pr = w.s([w.s([p1], 'adantr', '( %s -> %s = r )' % (U, F1('r', '0'))), w.s([], 'simpr', '( %s -> P || r )' % U)], 'breqtrrd',
             '( %s -> P || %s )' % (U, F1('r', '0')))
    return w.s([w.s([pr], 'orcd', '( %s -> ( P || %s \\/ P || D ) )' % (U, F1('r', '0')))], 'ex', '( %s -> %s )' % (B0, INN4('r', '0')))
def _t(w, B, T, ctx):
    out = w.s([ctx['out']], 'adantr', '( %s -> %s )' % (T, OUT4))
    dn = w.s([out], 'simpld', '( %s -> D e. NN )' % T)
    pp = w.s([out], 'simprd', '( %s -> P e. Prime )' % T)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % T)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % T)
    md = w.s([], 'simpr', '( %s -> %s )' % (T, MDr))
    val = branch(w, T, dn, rn, fn, True)
    U = '( %s /\\ P || r )' % T
    dnU = w.s([dn], 'adantr', '( %s -> D e. NN )' % U)
    ppU = w.s([pp], 'adantr', '( %s -> P e. Prime )' % U)
    rnU = w.s([rn], 'adantr', '( %s -> r e. NN0 )' % U)
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    mdU = w.s([md], 'adantr', '( %s -> %s )' % (U, MDr))
    pdr = w.s([], 'simpr', '( %s -> P || r )' % U)
    H1 = '( ( D e. NN /\\ r e. NN0 ) /\\ %s )' % MDr
    cj = w.s([w.s([dnU, rnU], 'jca', '( %s -> ( D e. NN /\\ r e. NN0 ) )' % U), mdU], 'jca', '( %s -> %s )' % (U, H1))
    qn = w.s([cj, w.inst('divoutqcl')], 'syl', '( %s -> %s e. NN0 )' % (U, DQr))
    mul = w.s([cj, w.inst('divoutqmul')], 'syl', '( %s -> ( D x. %s ) = r )' % (U, DQr))
    pdm = w.s([mul, pdr], 'breqtrrd', '( %s -> P || ( D x. %s ) )' % (U, DQr))
    eu = w.s([w.s([ppU, w.s([dnU], 'nnzd', '( %s -> D e. ZZ )' % U), w.s([qn], 'nn0zd', '( %s -> %s e. ZZ )' % (U, DQr))], '3jca',
                  '( %s -> ( P e. Prime /\\ D e. ZZ /\\ %s e. ZZ ) )' % (U, DQr)), w.inst('euclemma')], 'syl',
             '( %s -> ( P || ( D x. %s ) <-> ( P || D \\/ P || %s ) ) )' % (U, DQr, DQr))
    disj = w.s([eu, pdm], 'mpbid', '( %s -> ( P || D \\/ P || %s ) )' % (U, DQr))
    valU = w.s([val], 'adantr', '( %s -> %s = %s )' % (U, DOV('r', '( F + 1 )'), THEN))
    cl = divcl(w, U, DQr, 'F', dnU, qn, fnU)
    a1, b1 = paircl(w, U, DOV(DQr, 'F'), cl, 'NN0', 'NN0')
    b1p = w.s([b1, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (U, F2(DQr, 'F')))
    p1 = projeq(w, U, DOV('r', '( F + 1 )'), valU, F1(DQr, 'F'), '( %s + 1 )' % F2(DQr, 'F'), a1, b1p, 1)
    C1 = '( %s /\\ P || D )' % U
    c1 = w.s([w.s([], 'simpr', '( %s -> P || D )' % C1)], 'olcd',
             '( %s -> ( P || %s \\/ P || D ) )' % (C1, F1('r', '( F + 1 )')))
    C2 = '( %s /\\ P || %s )' % (U, DQr)
    ihq = w.s([ctx['sb'](w, 'c', DQr, 'F'), w.s([ctx['ihc']], 'ad3antrrr', '( %s -> A. c e. NN0 %s )' % (C2, INN4('c', 'F'))),
               w.s([qn], 'adantr', '( %s -> %s e. NN0 )' % (C2, DQr))], 'rspcdva', '( %s -> %s )' % (C2, INN4(DQr, 'F')))
    ihv = w.s([ihq, w.s([], 'simpr', '( %s -> P || %s )' % (C2, DQr))], 'mpd', '( %s -> ( P || %s \\/ P || D ) )' % (C2, F1(DQr, 'F')))
    c2 = w.s([w.s([w.s([p1], 'adantr', '( %s -> %s = %s )' % (C2, F1('r', '( F + 1 )'), F1(DQr, 'F')))], 'breq2d',
                  '( %s -> ( P || %s <-> P || %s ) )' % (C2, F1('r', '( F + 1 )'), F1(DQr, 'F')))], 'orbi1d',
             '( %s -> ( ( P || %s \\/ P || D ) <-> ( P || %s \\/ P || D ) ) )' % (C2, F1('r', '( F + 1 )'), F1(DQr, 'F')))
    c2b = w.s([c2, ihv], 'mpbird', '( %s -> ( P || %s \\/ P || D ) )' % (C2, F1('r', '( F + 1 )')))
    return w.s([w.s([c1, c2b, disj], 'mpjaodan', '( %s -> ( P || %s \\/ P || D ) )' % (U, F1('r', '( F + 1 )')))], 'ex',
               '( %s -> %s )' % (T, INN4('r', '( F + 1 )')))
def _f(w, B, F_, ctx):
    out = w.s([ctx['out']], 'adantr', '( %s -> %s )' % (F_, OUT4))
    dn = w.s([out], 'simpld', '( %s -> D e. NN )' % F_)
    rn = w.s([ctx['rn']], 'adantr', '( %s -> r e. NN0 )' % F_)
    fn = w.s([ctx['fn']], 'adantr', '( %s -> F e. NN0 )' % F_)
    val = branch(w, F_, dn, rn, fn, False)
    p1 = projeq(w, F_, DOV('r', '( F + 1 )'), val, 'r', '0', rex(w, F_, rn), zex(w, F_), 1)
    U = '( %s /\\ P || r )' % F_
    pr = w.s([w.s([p1], 'adantr', '( %s -> %s = r )' % (U, F1('r', '( F + 1 )'))), w.s([], 'simpr', '( %s -> P || r )' % U)], 'breqtrrd',
             '( %s -> P || %s )' % (U, F1('r', '( F + 1 )')))
    return w.s([w.s([pr], 'orcd', '( %s -> ( P || %s \\/ P || D ) )' % (U, F1('r', '( F + 1 )')))], 'ex',
               '( %s -> %s )' % (F_, INN4('r', '( F + 1 )')))
def _fin(w, PHI, INN, sb):
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ ( P e. Prime /\\ P || R ) )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    pp = w.s([], 'simprl', '( %s -> P e. Prime )' % T)
    pd = w.s([], 'simprr', '( %s -> P || R )' % T)
    ral = w.s([w.s([fn, w.inst('divoutprml')], 'syl', '( %s -> %s )' % (T, PHI('F'))),
               w.s([dn, pp], 'jca', '( %s -> %s )' % (T, OUT4))], 'mpd', '( %s -> A. r e. NN0 %s )' % (T, INN('r', 'F')))
    inst = w.s([sb(w, 'r', 'R', 'F'), ral, rn], 'rspcdva', '( %s -> %s )' % (T, INN('R', 'F')))
    w.qed([inst, pd], 'mpd', '( %s -> ( P || %s \\/ P || D ) )' % (T, F1('R', 'F')))
dofam('divoutprm', OUT4, INN4, _b, _t, _f, 'A prime factor of the input either survives the divide-out loop or is the divisor (Lean: divOut_prime).', _fin, only=only)

# ======================================================================= divoutpos
if not only or 'divoutpos' in only:
    w = W('divoutpos', 'The divide-out loop leaves a positive result (Lean: Nat.pos_of_dvd_of_pos at the call site).')
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ 1 <_ R )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    r1 = w.s([], 'simpr', '( %s -> 1 <_ R )' % T)
    dvd = w.s([w.s([dn, rn, fn], '3jca', '( %s -> ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) )' % T), w.inst('divoutdvd')], 'syl',
              '( %s -> %s || R )' % (T, F1('R', 'F')))
    cl = w.s([w.s([dn, rn], 'jca', '( %s -> ( D e. NN /\\ R e. NN0 ) )' % T), fn, w.inst('divoutcl')], 'syl2anc',
             '( %s -> %s e. ( NN0 X. NN0 ) )' % (T, DOV('R', 'F')))
    a1, b1 = paircl(w, T, DOV('R', 'F'), cl, 'NN0', 'NN0')
    C = '( %s /\\ %s = 0 )' % (T, F1('R', 'F'))
    d0 = w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (C, F1('R', 'F'))),
              w.s([dvd], 'adantr', '( %s -> %s || R )' % (C, F1('R', 'F')))], 'eqbrtrrd', '( %s -> 0 || R )' % C)
    r0 = w.s([w.s([w.s([w.s([rn], 'adantr', '( %s -> R e. NN0 )' % C)], 'nn0zd', '( %s -> R e. ZZ )' % C), w.inst('0dvds')], 'syl',
                  '( %s -> ( 0 || R <-> R = 0 ) )' % C), d0], 'mpbid', '( %s -> R = 0 )' % C)
    le10 = w.s([w.s([r1], 'adantr', '( %s -> 1 <_ R )' % C), r0], 'breqtrd', '( %s -> 1 <_ 0 )' % C)
    n10 = w.s([w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % C),
               w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % C),
                    w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % C)], 'ltnled', '( %s -> ( 0 < 1 <-> -. 1 <_ 0 ) )' % C)], 'mpbid',
              '( %s -> -. 1 <_ 0 )' % C)
    nz = w.s([le10, n10], 'pm2.65da', '( %s -> -. %s = 0 )' % (T, F1('R', 'F')))
    nn = w.s([a1, w.s([nz], 'neqned', '( %s -> %s =/= 0 )' % (T, F1('R', 'F'))), w.inst('elnnne0')], 'sylanbrc', '( %s -> %s e. NN )' % (T, F1('R', 'F')))
    w.qed([nn], 'nnge1d', '( %s -> 1 <_ %s )' % (T, F1('R', 'F')))
    run(w)
