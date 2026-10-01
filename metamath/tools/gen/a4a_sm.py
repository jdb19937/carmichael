"""Sortie A4a, batch 9: smoothGo and smoothTD (the smoothness loop)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

SG = lambda d, r, f: '( ( %s SmoothGo %s ) ` %s )' % (d, r, f)
G1 = lambda d, r, f: '( 1st ` %s )' % SG(d, r, f)
G2 = lambda d, r, f: '( 2nd ` %s )' % SG(d, r, f)
DI = lambda d, r: '( ( %s DivOut %s ) ` %s )' % (d, r, r)
D1 = lambda d, r: '( 1st ` %s )' % DI(d, r)
D2 = lambda d, r: '( 2nd ` %s )' % DI(d, r)

def sgfam(label, INN, basefn, stepfn, desc, finalfn, only=(), INNC=None, innercbv=None):
    """base, step, fuelind and assembly for a smoothGo-shaped fuel recursion whose
    induction property is A. d e. NN A. r e. NN0 INN( d , r , f )."""
    PHI = lambda f: 'A. d e. NN A. r e. NN0 %s' % INN('d', 'r', f)
    INN2 = INNC or INN
    def mk(TMPL):
        def sbo_(w, frm, to, f, qv):
            idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
            st, new = w.wcongr('A. %s e. NN0 %s' % (qv, TMPL(frm, qv, f)), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
            assert new == 'A. %s e. NN0 %s' % (qv, TMPL(to, qv, f)), '\n%s' % new
            return st
        def sbi_(w, dv, frm, to, f):
            idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
            st, new = w.wcongr(TMPL(dv, frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
            assert new == TMPL(dv, to, f), '\n%s\n%s' % (new, TMPL(dv, to, f))
            return st
        return sbo_, sbi_
    sboA, sbiA = mk(INN)
    def sbo(w, frm, to, f, qv):
        """( frm = to -> ( A. qv e. NN0 INN(frm,qv,f) <-> A. qv e. NN0 INN(to,qv,f) ) )"""
        idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
        st, new = w.wcongr('A. %s e. NN0 %s' % (qv, INN2(frm, qv, f)), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
        assert new == 'A. %s e. NN0 %s' % (qv, INN2(to, qv, f)), '\n%s' % new
        return st
    def sbi(w, dv, frm, to, f):
        idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
        st, new = w.wcongr(INN2(dv, frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
        assert new == INN2(dv, to, f), '\n%s\n%s' % (new, INN2(dv, to, f))
        return st
    ok = True
    if not only or label + 'b' in only:
        w = W(label + 'b', 'Base of the induction for ' + label + '.')
        B0 = '( d e. NN /\\ r e. NN0 )'
        st = basefn(w, B0)
        inner = w.s([st], 'ralrimiva', '( d e. NN -> A. r e. NN0 %s )' % INN('d', 'r', '0'))
        w.qed([inner], 'rgen', PHI('0'))
        ok = w.run() and ok
    if not only or label + 's' in only:
        w = W(label + 's', 'Step of the induction for ' + label + '.')
        IHD = PHI('F')
        IHC = 'A. c e. NN A. q e. NN0 %s' % INN2('c', 'q', 'F')
        A = '( F e. NN0 /\\ %s )' % IHD
        AC = '( F e. NN0 /\\ %s )' % IHC
        if innercbv is None:
            pre = IHD
        else:
            ic = innercbv(w)
            e1 = w.s([ic], 'ralbii', '( A. r e. NN0 %s <-> A. r e. NN0 %s )' % (INN('d', 'r', 'F'), INN2('d', 'r', 'F')))
            e2 = w.s([e1], 'ralbii', '( %s <-> A. d e. NN A. r e. NN0 %s )' % (IHD, INN2('d', 'r', 'F')))
            pre = 'A. d e. NN A. r e. NN0 %s' % INN2('d', 'r', 'F')
        cbvi = w.s([sbi(w, 'd', 'r', 'q', 'F')], 'cbvralvw', '( A. r e. NN0 %s <-> A. q e. NN0 %s )' % (INN2('d', 'r', 'F'), INN2('d', 'q', 'F')))
        st1 = w.s([cbvi], 'ralbii', '( %s <-> A. d e. NN A. q e. NN0 %s )' % (pre, INN2('d', 'q', 'F')))
        st2 = w.s([sbo(w, 'd', 'c', 'F', 'q')], 'cbvralvw', '( A. d e. NN A. q e. NN0 %s <-> %s )' % (INN2('d', 'q', 'F'), IHC))
        cbvp = w.s([st1, st2], 'bitri', '( %s <-> %s )' % (pre, IHC))
        cbv = cbvp if innercbv is None else w.s([e2, cbvp], 'bitri', '( %s <-> %s )' % (IHD, IHC))
        conv = w.s([w.s([], 'simpl', '( %s -> F e. NN0 )' % A),
                    w.s([w.s([], 'simpr', '( %s -> %s )' % (A, IHD)),
                         w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'mpbid', '( %s -> %s )' % (A, IHC))], 'jca',
                   '( %s -> %s )' % (A, AC))
        B = '( ( %s /\\ d e. NN ) /\\ r e. NN0 )' % AC
        ctx = {'sbo': sbo, 'sbi': sbi, 'INN': INN2}
        ctx['fn'] = w.s([], 'simplll', '( %s -> F e. NN0 )' % B)
        ctx['ihc'] = w.s([], 'simpllr', '( %s -> %s )' % (B, IHC))
        ctx['dn'] = w.s([], 'simplr', '( %s -> d e. NN )' % B)
        ctx['rn'] = w.s([], 'simpr', '( %s -> r e. NN0 )' % B)
        main = stepfn(w, B, ctx)
        w.qed([conv, w.s([w.s([main], 'ralrimiva', '( ( %s /\\ d e. NN ) -> A. r e. NN0 %s )' % (AC, INN('d', 'r', '( F + 1 )'))),
                          ], 'ralrimiva', '( %s -> %s )' % (AC, PHI('( F + 1 )')))], 'syl', '( %s -> %s )' % (A, PHI('( F + 1 )')))
        ok = w.run() and ok
    if not only or label + 'l' in only:
        w = W(label + 'l', desc + ' (as the induction on the fuel delivers it)')
        st, pt = fuelind(w, PHI('f'), 'F', label + 'b', label + 's', fvar='f')
        w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
        ok = w.run() and ok
    if not only or label in only:
        w = W(label, desc)
        finalfn(w, PHI, INN, sboA, sbiA)
        ok = w.run() and ok
    return ok

# ======================================================================= smoothgodvd
INN = lambda d, r, f: '%s || %s' % (G1(d, r, f), r)
def _b(w, B0):
    dn = w.s([], 'simpl', '( %s -> d e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    v = w.s([dn, rn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. r , 0 >. )' % (B0, SG('d', 'r', '0')))
    p1 = projeq(w, B0, SG('d', 'r', '0'), v, 'r', '0', w.s([rn], 'elexd', '( %s -> r e. _V )' % B0),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % B0), 1)
    rid = w.s([w.s([rn], 'nn0zd', '( %s -> r e. ZZ )' % B0), w.inst('iddvds')], 'syl', '( %s -> r || r )' % B0)
    return w.s([p1, rid], 'eqbrtrd', '( %s -> %s )' % (B0, INN('d', 'r', '0')))
def _s(w, B, ctx):
    dn, rn, fn, ihc = ctx['dn'], ctx['rn'], ctx['fn'], ctx['ihc']
    DO = D1('d', 'r')
    v = w.s([w.s([dn, rn], 'jca', '( %s -> ( d e. NN /\\ r e. NN0 ) )' % B), fn, w.inst('smoothgop1')], 'syl2anc',
            '( %s -> %s = <. %s , ( ( %s + %s ) + 1 ) >. )' % (B, SG('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F'), G2('( d + 1 )', DO, 'F'), D2('d', 'r')))
    dcl = w.s([w.s([dn, rn], 'jca', '( %s -> ( d e. NN /\\ r e. NN0 ) )' % B), rn, w.inst('divoutcl')], 'syl2anc',
              '( %s -> %s e. ( NN0 X. NN0 ) )' % (B, DI('d', 'r')))
    q1, q2 = paircl(w, B, DI('d', 'r'), dcl, 'NN0', 'NN0')
    d1n = w.s([dn, w.inst('peano2nn')], 'syl', '( %s -> ( d + 1 ) e. NN )' % B)
    scl = w.s([w.s([d1n, q1], 'jca', '( %s -> ( ( d + 1 ) e. NN /\\ %s e. NN0 ) )' % (B, DO)), fn, w.inst('smoothgocl')], 'syl2anc',
              '( %s -> %s e. ( NN0 X. NN0 ) )' % (B, SG('( d + 1 )', DO, 'F')))
    s1, s2 = paircl(w, B, SG('( d + 1 )', DO, 'F'), scl, 'NN0', 'NN0')
    s2s = w.s([w.s([s2, q2], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (B, G2('( d + 1 )', DO, 'F'), D2('d', 'r'))), w.inst('peano2nn0')], 'syl',
              '( %s -> ( ( %s + %s ) + 1 ) e. NN0 )' % (B, G2('( d + 1 )', DO, 'F'), D2('d', 'r')))
    p1 = projeq(w, B, SG('d', 'r', '( F + 1 )'), v, G1('( d + 1 )', DO, 'F'),
                '( ( %s + %s ) + 1 )' % (G2('( d + 1 )', DO, 'F'), D2('d', 'r')), s1, s2s, 1)
    iho = w.s([ctx['sbo'](w, 'c', '( d + 1 )', 'F', 'q'), ihc, d1n], 'rspcdva',
              '( %s -> A. q e. NN0 %s )' % (B, ctx['INN']('( d + 1 )', 'q', 'F')))
    ihq = w.s([ctx['sbi'](w, '( d + 1 )', 'q', DO, 'F'), iho, q1], 'rspcdva', '( %s -> %s )' % (B, ctx['INN']('( d + 1 )', DO, 'F')))
    dvd = w.s([w.s([dn, rn, rn], '3jca', '( %s -> ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) )' % B), w.inst('divoutdvd')], 'syl',
              '( %s -> %s || r )' % (B, DO))
    tr = w.s([w.s([w.s([s1], 'nn0zd', '( %s -> %s e. ZZ )' % (B, G1('( d + 1 )', DO, 'F'))), w.s([q1], 'nn0zd', '( %s -> %s e. ZZ )' % (B, DO)),
                   w.s([rn], 'nn0zd', '( %s -> r e. ZZ )' % B)], '3jca',
                  '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ r e. ZZ ) )' % (B, G1('( d + 1 )', DO, 'F'), DO)), w.inst('dvdstr')], 'syl',
             '( %s -> ( ( %s || %s /\\ %s || r ) -> %s || r ) )' % (B, G1('( d + 1 )', DO, 'F'), DO, DO, G1('( d + 1 )', DO, 'F')))
    dd = w.s([tr, w.s([ihq, dvd], 'jca', '( %s -> ( %s || %s /\\ %s || r ) )' % (B, G1('( d + 1 )', DO, 'F'), DO, DO))], 'mpd',
             '( %s -> %s || r )' % (B, G1('( d + 1 )', DO, 'F')))
    return w.s([p1, dd], 'eqbrtrd', '( %s -> %s )' % (B, INN('d', 'r', '( F + 1 )')))
def _fin(w, PHI, INN, sbo, sbi):
    T = '( D e. NN /\\ R e. NN0 /\\ F e. NN0 )'
    dn = w.s([], 'simp1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simp2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simp3', '( %s -> F e. NN0 )' % T)
    ral = w.s([fn, w.inst('smoothgodvdl')], 'syl', '( %s -> %s )' % (T, PHI('F')))
    o = w.s([sbo(w, 'd', 'D', 'F', 'r'), ral, dn], 'rspcdva', '( %s -> A. r e. NN0 %s )' % (T, INN('D', 'r', 'F')))
    w.qed([sbi(w, 'D', 'r', 'R', 'F'), o, rn], 'rspcdva', '( %s -> %s )' % (T, INN('D', 'R', 'F')))
sgfam('smoothgodvd', INN, _b, _s, 'The smoothness loop returns a divisor of its input (Lean: smoothGo_dvd).', _fin, only=only)

# ======================================================================= divoutcst
if not only or 'divoutcst' in only:
    w = W('divoutcst', 'The cost of the inner divide-out loop, at the fuel the smoothness loop gives it.')
    T = '( D e. NN /\\ R e. NN0 /\\ 2 <_ D )'
    LHS = '( %s + %s )' % (D2('D', 'R'), LG(D1('D', 'R')))
    dn = w.s([], 'simp1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simp2', '( %s -> R e. NN0 )' % T)
    d2 = w.s([], 'simp3', '( %s -> 2 <_ D )' % T)
    # case 1 <_ R
    A = '( %s /\\ 1 <_ R )' % T
    c1 = w.s([w.s([w.s([w.s([dn], 'adantr', '( %s -> D e. NN )' % A), w.s([rn], 'adantr', '( %s -> R e. NN0 )' % A),
                        w.s([rn], 'adantr', '( %s -> R e. NN0 )' % A)], '3jca', '( %s -> ( D e. NN /\\ R e. NN0 /\\ R e. NN0 ) )' % A),
                   w.s([w.s([d2], 'adantr', '( %s -> 2 <_ D )' % A), w.s([], 'simpr', '( %s -> 1 <_ R )' % A)], 'jca',
                       '( %s -> ( 2 <_ D /\\ 1 <_ R ) )' % A)], 'jca',
                  '( %s -> ( ( D e. NN /\\ R e. NN0 /\\ R e. NN0 ) /\\ ( 2 <_ D /\\ 1 <_ R ) ) )' % A), w.inst('divoutcost')], 'syl',
             '( %s -> %s <_ %s )' % (A, LHS, LG('R')))
    # case R = 0
    B = '( %s /\\ -. 1 <_ R )' % T
    nnn = w.s([w.s([], 'simpr', '( %s -> -. 1 <_ R )' % B),
               w.s([w.inst('nnge1')], 'a1i', '( %s -> ( R e. NN -> 1 <_ R ) )' % B)], 'mtod', '( %s -> -. R e. NN )' % B)
    r0b = w.s([nnn, w.s([w.s([rn], 'adantr', '( %s -> R e. NN0 )' % B), w.inst('elnn0')], 'sylib', '( %s -> ( R e. NN \\/ R = 0 ) )' % B)], 'orcnd',
              '( %s -> R = 0 )' % B)
    dnb = w.s([dn], 'adantr', '( %s -> D e. NN )' % B)
    dv0 = w.s([dnb, w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % B), w.inst('divout0')], 'syl2anc',
              '( %s -> ( ( D DivOut 0 ) ` 0 ) = <. 0 , 0 >. )' % B)
    zv = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % B)
    q1 = projeq(w, B, '( ( D DivOut 0 ) ` 0 )', dv0, '0', '0', zv, zv, 1)
    q2 = projeq(w, B, '( ( D DivOut 0 ) ` 0 )', dv0, '0', '0', zv, zv, 2)
    lg0 = w.s([w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % B),
                        w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % B)], 'jca', '( %s -> ( 2 e. NN0 /\\ 0 e. NN0 ) )' % B),
                   w.s([w.s([w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % B),
                            w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % B),
                                 w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % B)], 'ltnled',
                                '( %s -> ( 0 < 1 <-> -. 1 <_ 0 ) )' % B)], 'mpbid', '( %s -> -. 1 <_ 0 )' % B)], 'intnand',
                       '( %s -> -. ( 2 <_ 2 /\\ 1 <_ 0 ) )' % B)], 'jca',
                  '( %s -> ( ( 2 e. NN0 /\\ 0 e. NN0 ) /\\ -. ( 2 <_ 2 /\\ 1 <_ 0 ) ) )' % B), w.inst('nlogz')], 'syl',
              '( %s -> %s = 0 )' % (B, LG('0')))
    lhs0, _ = rweq(w, B, LHS, 'R', '0', r0b)
    rhs0, _ = rweq(w, B, LG('R'), 'R', '0', r0b)
    e1, _ = rweq(w, B, LG(D1('D', '0')), D1('D', '0'), '0', q1)
    tot = w.s([lhs0, w.s([q2, e1], 'oveq12d', '( %s -> ( %s + %s ) = ( 0 + %s ) )' % (B, D2('D', '0'), LG(D1('D', '0')), LG('0')))], 'eqtrd',
              '( %s -> %s = ( 0 + %s ) )' % (B, LHS, LG('0')))
    tot2 = w.s([tot, w.s([lg0], 'oveq2d', '( %s -> ( 0 + %s ) = ( 0 + 0 ) )' % (B, LG('0')))], 'eqtrd', '( %s -> %s = ( 0 + 0 ) )' % (B, LHS))
    z00 = w.s([w.s([], '00id', '( 0 + 0 ) = 0')], 'a1i', '( %s -> ( 0 + 0 ) = 0 )' % B)
    tot3 = w.s([tot2, z00], 'eqtrd', '( %s -> %s = 0 )' % (B, LHS))
    rhs1 = w.s([rhs0, lg0], 'eqtrd', '( %s -> %s = 0 )' % (B, LG('R')))
    zle = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('leid')], 'ax-mp', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % B)
    c2 = w.s([tot3, w.s([zle, rhs1], 'breqtrrd', '( %s -> 0 <_ %s )' % (B, LG('R')))], 'eqbrtrd', '( %s -> %s <_ %s )' % (B, LHS, LG('R')))
    w.qed([c1, c2], 'pm2.61dan', '( %s -> %s <_ %s )' % (T, LHS, LG('R')))
    run(w)

# ======================================================================= smoothgocost
INN = lambda d, r, f: '( 2 <_ %s -> ( %s + %s ) <_ ( %s + %s ) )' % (d, G2(d, r, f), LG(G1(d, r, f)), f, LG(r))
def sgctx(w, B, ctx):
    """the common pieces of a smoothGo cons step"""
    dn, rn, fn = ctx['dn'], ctx['rn'], ctx['fn']
    DO = D1('d', 'r')
    v = w.s([w.s([dn, rn], 'jca', '( %s -> ( d e. NN /\\ r e. NN0 ) )' % B), fn, w.inst('smoothgop1')], 'syl2anc',
            '( %s -> %s = <. %s , ( ( %s + %s ) + 1 ) >. )' % (B, SG('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F'), G2('( d + 1 )', DO, 'F'), D2('d', 'r')))
    dcl = w.s([w.s([dn, rn], 'jca', '( %s -> ( d e. NN /\\ r e. NN0 ) )' % B), rn, w.inst('divoutcl')], 'syl2anc',
              '( %s -> %s e. ( NN0 X. NN0 ) )' % (B, DI('d', 'r')))
    q1, q2 = paircl(w, B, DI('d', 'r'), dcl, 'NN0', 'NN0')
    d1n = w.s([dn, w.inst('peano2nn')], 'syl', '( %s -> ( d + 1 ) e. NN )' % B)
    scl = w.s([w.s([d1n, q1], 'jca', '( %s -> ( ( d + 1 ) e. NN /\\ %s e. NN0 ) )' % (B, DO)), fn, w.inst('smoothgocl')], 'syl2anc',
              '( %s -> %s e. ( NN0 X. NN0 ) )' % (B, SG('( d + 1 )', DO, 'F')))
    s1, s2 = paircl(w, B, SG('( d + 1 )', DO, 'F'), scl, 'NN0', 'NN0')
    s2s = w.s([w.s([s2, q2], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (B, G2('( d + 1 )', DO, 'F'), D2('d', 'r'))), w.inst('peano2nn0')], 'syl',
              '( %s -> ( ( %s + %s ) + 1 ) e. NN0 )' % (B, G2('( d + 1 )', DO, 'F'), D2('d', 'r')))
    p1 = projeq(w, B, SG('d', 'r', '( F + 1 )'), v, G1('( d + 1 )', DO, 'F'),
                '( ( %s + %s ) + 1 )' % (G2('( d + 1 )', DO, 'F'), D2('d', 'r')), s1, s2s, 1)
    p2 = projeq(w, B, SG('d', 'r', '( F + 1 )'), v, G1('( d + 1 )', DO, 'F'),
                '( ( %s + %s ) + 1 )' % (G2('( d + 1 )', DO, 'F'), D2('d', 'r')), s1, s2s, 2)
    return DO, q1, q2, d1n, s1, s2, p1, p2

def ihat(w, B, ctx, dexpr, rexpr, dstep, rstep):
    """instantiate the induction hypothesis at ( dexpr , rexpr )"""
    o = w.s([ctx['sbo'](w, 'c', dexpr, 'F', 'q'), ctx['ihc'], dstep], 'rspcdva',
            '( %s -> A. q e. NN0 %s )' % (B, ctx['INN'](dexpr, 'q', 'F')))
    return w.s([ctx['sbi'](w, dexpr, 'q', rexpr, 'F'), o, rstep], 'rspcdva', '( %s -> %s )' % (B, ctx['INN'](dexpr, rexpr, 'F')))

def lgcl(w, A, e, est):
    n = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), est, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, LG(e)))
    return w.s([n], 'nn0red', '( %s -> %s e. RR )' % (A, LG(e)))

def _b(w, B0):
    dn = w.s([], 'simpl', '( %s -> d e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    v = w.s([dn, rn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. r , 0 >. )' % (B0, SG('d', 'r', '0')))
    rv = w.s([rn], 'elexd', '( %s -> r e. _V )' % B0)
    zv = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % B0)
    p1 = projeq(w, B0, SG('d', 'r', '0'), v, 'r', '0', rv, zv, 1)
    p2 = projeq(w, B0, SG('d', 'r', '0'), v, 'r', '0', rv, zv, 2)
    e1, _ = rweq(w, B0, LG(G1('d', 'r', '0')), G1('d', 'r', '0'), 'r', p1)
    lhs = w.s([p2, e1], 'oveq12d', '( %s -> ( %s + %s ) = ( 0 + %s ) )' % (B0, G2('d', 'r', '0'), LG(G1('d', 'r', '0')), LG('r')))
    lgr0 = lgcl(w, B0, 'r', rn)
    z0r = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % B0), lgr0], 'readdcld', '( %s -> ( 0 + %s ) e. RR )' % (B0, LG('r')))
    return w.s([w.s([lhs, w.s([z0r], 'leidd', '( %s -> ( 0 + %s ) <_ ( 0 + %s ) )' % (B0, LG('r'), LG('r')))], 'eqbrtrd',
                    '( %s -> ( %s + %s ) <_ ( 0 + %s ) )' % (B0, G2('d', 'r', '0'), LG(G1('d', 'r', '0')), LG('r')))], 'a1d',
               '( %s -> %s )' % (B0, INN('d', 'r', '0')))
def _s(w, B, ctx):
    dn, rn, fn = ctx['dn'], ctx['rn'], ctx['fn']
    DO, q1, q2, d1n, s1, s2, p1, p2 = sgctx(w, B, ctx)
    U = '( %s /\\ 2 <_ d )' % B
    dnU = w.s([dn], 'adantr', '( %s -> d e. NN )' % U)
    rnU = w.s([rn], 'adantr', '( %s -> r e. NN0 )' % U)
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    d2 = w.s([], 'simpr', '( %s -> 2 <_ d )' % U)
    q1U = w.s([q1], 'adantr', '( %s -> %s e. NN0 )' % (U, DO))
    q2U = w.s([q2], 'adantr', '( %s -> %s e. NN0 )' % (U, D2('d', 'r')))
    d1nU = w.s([d1n], 'adantr', '( %s -> ( d + 1 ) e. NN )' % U)
    s1U = w.s([s1], 'adantr', '( %s -> %s e. NN0 )' % (U, G1('( d + 1 )', DO, 'F')))
    s2U = w.s([s2], 'adantr', '( %s -> %s e. NN0 )' % (U, G2('( d + 1 )', DO, 'F')))
    dcst = w.s([w.s([dnU, rnU, d2], '3jca', '( %s -> ( d e. NN /\\ r e. NN0 /\\ 2 <_ d ) )' % U), w.inst('divoutcst')], 'syl',
               '( %s -> ( %s + %s ) <_ %s )' % (U, D2('d', 'r'), LG(DO), LG('r')))
    ctxU = dict(ctx); ctxU['ihc'] = w.s([ctx['ihc']], 'adantr', '( %s -> %s )' % (U, 'A. c e. NN A. q e. NN0 ' + INN('c', 'q', 'F')))
    ih = ihat(w, U, ctxU, '( d + 1 )', DO, d1nU, q1U)
    dr = w.s([dnU], 'nnred', '( %s -> d e. RR )' % U)
    d21 = lin.linarith(w, U, [d2], '2 <_ ( d + 1 )', leaves={'d': dr})
    ihv = w.s([ih, d21], 'mpd', '( %s -> ( %s + %s ) <_ ( F + %s ) )' % (U, G2('( d + 1 )', DO, 'F'), LG(G1('( d + 1 )', DO, 'F')), LG(DO)))
    lgdo = lgcl(w, U, DO, q1U)
    lgr = lgcl(w, U, 'r', rnU)
    lgs = lgcl(w, U, G1('( d + 1 )', DO, 'F'), s1U)
    s2r = w.s([s2U], 'nn0red', '( %s -> %s e. RR )' % (U, G2('( d + 1 )', DO, 'F')))
    q2r = w.s([q2U], 'nn0red', '( %s -> %s e. RR )' % (U, D2('d', 'r')))
    fr = w.s([fnU], 'nn0red', '( %s -> F e. RR )' % U)
    GOALL = '( ( ( %s + %s ) + 1 ) + %s )' % (G2('( d + 1 )', DO, 'F'), D2('d', 'r'), LG(G1('( d + 1 )', DO, 'F')))
    li = lin.linarith(w, U, [ihv, dcst], '%s <_ ( ( F + 1 ) + %s )' % (GOALL, LG('r')),
                      leaves={G2('( d + 1 )', DO, 'F'): s2r, D2('d', 'r'): q2r, LG(G1('( d + 1 )', DO, 'F')): lgs,
                              LG(DO): lgdo, LG('r'): lgr, 'F': fr})
    e1, _ = rweq(w, U, LG(G1('d', 'r', '( F + 1 )')), G1('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F'), w.s([p1], 'adantr',
                 '( %s -> %s = %s )' % (U, G1('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F'))))
    lhs = w.s([w.s([p2], 'adantr', '( %s -> %s = ( ( %s + %s ) + 1 ) )' % (U, G2('d', 'r', '( F + 1 )'), G2('( d + 1 )', DO, 'F'), D2('d', 'r'))), e1],
              'oveq12d', '( %s -> ( %s + %s ) = %s )' % (U, G2('d', 'r', '( F + 1 )'), LG(G1('d', 'r', '( F + 1 )')), GOALL))
    return w.s([w.s([lhs, li], 'eqbrtrd', '( %s -> ( %s + %s ) <_ ( ( F + 1 ) + %s ) )' % (U, G2('d', 'r', '( F + 1 )'), LG(G1('d', 'r', '( F + 1 )')), LG('r')))],
               'ex', '( %s -> %s )' % (B, INN('d', 'r', '( F + 1 )')))
def _fin(w, PHI, INN, sbo, sbi):
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ 2 <_ D )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    d2 = w.s([], 'simpr', '( %s -> 2 <_ D )' % T)
    ral = w.s([fn, w.inst('smoothgocostl')], 'syl', '( %s -> %s )' % (T, PHI('F')))
    o = w.s([sbo(w, 'd', 'D', 'F', 'r'), ral, dn], 'rspcdva', '( %s -> A. r e. NN0 %s )' % (T, INN('D', 'r', 'F')))
    i = w.s([sbi(w, 'D', 'r', 'R', 'F'), o, rn], 'rspcdva', '( %s -> %s )' % (T, INN('D', 'R', 'F')))
    w.qed([i, d2], 'mpd', '( %s -> ( %s + %s ) <_ ( F + %s ) )' % (T, G2('D', 'R', 'F'), LG(G1('D', 'R', 'F')), LG('R')))
sgfam('smoothgocost', INN, _b, _s, 'The cost of the smoothness loop (Lean: smoothGo_cost).', _fin, only=only)

# ======================================================================= smoothgoprm
INN = lambda d, r, f: '( ( P e. Prime /\\ P || %s ) -> ( P || %s \\/ P < ( %s + %s ) ) )' % (r, G1(d, r, f), d, f)
def _b(w, B0):
    dn = w.s([], 'simpl', '( %s -> d e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    v = w.s([dn, rn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. r , 0 >. )' % (B0, SG('d', 'r', '0')))
    p1 = projeq(w, B0, SG('d', 'r', '0'), v, 'r', '0', w.s([rn], 'elexd', '( %s -> r e. _V )' % B0),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % B0), 1)
    U = '( %s /\\ ( P e. Prime /\\ P || r ) )' % B0
    pd = w.s([], 'simprr', '( %s -> P || r )' % U)
    pg = w.s([w.s([p1], 'adantr', '( %s -> %s = r )' % (U, G1('d', 'r', '0'))), pd], 'breqtrrd', '( %s -> P || %s )' % (U, G1('d', 'r', '0')))
    return w.s([w.s([pg], 'orcd', '( %s -> ( P || %s \\/ P < ( d + 0 ) ) )' % (U, G1('d', 'r', '0')))], 'ex', '( %s -> %s )' % (B0, INN('d', 'r', '0')))
def _s(w, B, ctx):
    dn, rn, fn = ctx['dn'], ctx['rn'], ctx['fn']
    DO, q1, q2, d1n, s1, s2, p1, p2 = sgctx(w, B, ctx)
    U = '( %s /\\ ( P e. Prime /\\ P || r ) )' % B
    dnU = w.s([dn], 'adantr', '( %s -> d e. NN )' % U)
    rnU = w.s([rn], 'adantr', '( %s -> r e. NN0 )' % U)
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    q1U = w.s([q1], 'adantr', '( %s -> %s e. NN0 )' % (U, DO))
    d1nU = w.s([d1n], 'adantr', '( %s -> ( d + 1 ) e. NN )' % U)
    s1U = w.s([s1], 'adantr', '( %s -> %s e. NN0 )' % (U, G1('( d + 1 )', DO, 'F')))
    p1U = w.s([p1], 'adantr', '( %s -> %s = %s )' % (U, G1('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F')))
    pp = w.s([], 'simprl', '( %s -> P e. Prime )' % U)
    pdr = w.s([], 'simprr', '( %s -> P || r )' % U)
    dr = w.s([dnU], 'nnred', '( %s -> d e. RR )' % U)
    fr = w.s([fnU], 'nn0red', '( %s -> F e. RR )' % U)
    pz = w.s([pp, w.inst('prmz')], 'syl', '( %s -> P e. ZZ )' % U)
    pr = w.s([pz], 'zred', '( %s -> P e. RR )' % U)
    disj = w.s([w.s([w.s([dnU, rnU, rnU], '3jca', '( %s -> ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) )' % U),
                     w.s([pp, pdr], 'jca', '( %s -> ( P e. Prime /\\ P || r ) )' % U)], 'jca',
                    '( %s -> ( ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) /\\ ( P e. Prime /\\ P || r ) ) )' % U), w.inst('divoutprm')], 'syl',
               '( %s -> ( P || %s \\/ P || d ) )' % (U, DO))
    # case P || DO
    C1 = '( %s /\\ P || %s )' % (U, DO)
    ctx1 = dict(ctx); ctx1['ihc'] = w.s([ctx['ihc']], 'ad2antrr', '( %s -> %s )' % (C1, 'A. c e. NN A. q e. NN0 ' + INN('c', 'q', 'F')))
    ih = ihat(w, C1, ctx1, '( d + 1 )', DO, w.s([d1nU], 'adantr', '( %s -> ( d + 1 ) e. NN )' % C1),
              w.s([q1U], 'adantr', '( %s -> %s e. NN0 )' % (C1, DO)))
    ihv = w.s([ih, w.s([w.s([pp], 'adantr', '( %s -> P e. Prime )' % C1), w.s([], 'simpr', '( %s -> P || %s )' % (C1, DO))], 'jca',
                       '( %s -> ( P e. Prime /\\ P || %s ) )' % (C1, DO))], 'mpd',
              '( %s -> ( P || %s \\/ P < ( ( d + 1 ) + F ) ) )' % (C1, G1('( d + 1 )', DO, 'F')))
    E1 = '( %s /\\ P || %s )' % (C1, G1('( d + 1 )', DO, 'F'))
    e1 = w.s([w.s([w.s([w.s([p1U], 'ad2antrr', '( %s -> %s = %s )' % (E1, G1('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F')))], 'breq2d',
                       '( %s -> ( P || %s <-> P || %s ) )' % (E1, G1('d', 'r', '( F + 1 )'), G1('( d + 1 )', DO, 'F'))),
                  w.s([], 'simpr', '( %s -> P || %s )' % (E1, G1('( d + 1 )', DO, 'F')))], 'mpbird',
                 '( %s -> P || %s )' % (E1, G1('d', 'r', '( F + 1 )')))], 'orcd',
             '( %s -> ( P || %s \\/ P < ( d + ( F + 1 ) ) ) )' % (E1, G1('d', 'r', '( F + 1 )')))
    E2 = '( %s /\\ P < ( ( d + 1 ) + F ) )' % C1
    lt2 = lin.linarith(w, E2, [w.s([], 'simpr', '( %s -> P < ( ( d + 1 ) + F ) )' % E2)], 'P < ( d + ( F + 1 ) )',
                       leaves={'P': w.s([pr], 'ad2antrr', '( %s -> P e. RR )' % E2), 'd': w.s([dr], 'ad2antrr', '( %s -> d e. RR )' % E2),
                               'F': w.s([fr], 'ad2antrr', '( %s -> F e. RR )' % E2)})
    e2 = w.s([lt2], 'olcd', '( %s -> ( P || %s \\/ P < ( d + ( F + 1 ) ) ) )' % (E2, G1('d', 'r', '( F + 1 )')))
    c1 = w.s([e1, e2, ihv], 'mpjaodan', '( %s -> ( P || %s \\/ P < ( d + ( F + 1 ) ) ) )' % (C1, G1('d', 'r', '( F + 1 )')))
    # case P || d
    C2 = '( %s /\\ P || d )' % U
    ple = w.s([w.s([w.s([pz], 'adantr', '( %s -> P e. ZZ )' % C2), w.s([dnU], 'adantr', '( %s -> d e. NN )' % C2), w.inst('dvdsle')], 'syl2anc',
                   '( %s -> ( P || d -> P <_ d ) )' % C2), w.s([], 'simpr', '( %s -> P || d )' % C2)], 'mpd', '( %s -> P <_ d )' % C2)
    fge = w.s([w.s([fnU], 'adantr', '( %s -> F e. NN0 )' % C2)], 'nn0ge0d', '( %s -> 0 <_ F )' % C2)
    lt3 = lin.linarith(w, C2, [ple, fge], 'P < ( d + ( F + 1 ) )',
                       leaves={'P': w.s([pr], 'adantr', '( %s -> P e. RR )' % C2), 'd': w.s([dr], 'adantr', '( %s -> d e. RR )' % C2),
                               'F': w.s([fr], 'adantr', '( %s -> F e. RR )' % C2)})
    c2 = w.s([lt3], 'olcd', '( %s -> ( P || %s \\/ P < ( d + ( F + 1 ) ) ) )' % (C2, G1('d', 'r', '( F + 1 )')))
    return w.s([w.s([c1, c2, disj], 'mpjaodan', '( %s -> ( P || %s \\/ P < ( d + ( F + 1 ) ) ) )' % (U, G1('d', 'r', '( F + 1 )')))], 'ex',
               '( %s -> %s )' % (B, INN('d', 'r', '( F + 1 )')))
def _fin(w, PHI, INN, sbo, sbi):
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ ( P e. Prime /\\ P || R ) )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    hy = w.s([], 'simpr', '( %s -> ( P e. Prime /\\ P || R ) )' % T)
    ral = w.s([fn, w.inst('smoothgoprml')], 'syl', '( %s -> %s )' % (T, PHI('F')))
    o = w.s([sbo(w, 'd', 'D', 'F', 'r'), ral, dn], 'rspcdva', '( %s -> A. r e. NN0 %s )' % (T, INN('D', 'r', 'F')))
    i = w.s([sbi(w, 'D', 'r', 'R', 'F'), o, rn], 'rspcdva', '( %s -> %s )' % (T, INN('D', 'R', 'F')))
    w.qed([i, hy], 'mpd', '( %s -> ( P || %s \\/ P < ( D + F ) ) )' % (T, G1('D', 'R', 'F')))
sgfam('smoothgoprm', INN, _b, _s, 'Every prime factor of the input either survives the smoothness loop or is below the range reached (Lean: smoothGo_prime).', _fin, only=only)

# ======================================================================= smoothgondvd
BOD = lambda d, r, f, v: '( ( %s <_ %s /\\ %s < ( %s + %s ) ) -> -. %s || %s )' % (d, v, v, d, f, v, G1(d, r, f))
INN = lambda d, r, f: '( ( 2 <_ %s /\\ 1 <_ %s ) -> A. e e. NN0 %s )' % (d, r, BOD(d, r, f, 'e'))
INNG = lambda d, r, f: '( ( 2 <_ %s /\\ 1 <_ %s ) -> A. g e. NN0 %s )' % (d, r, BOD(d, r, f, 'g'))
def _icbv(w):
    idg = w.s([], 'id', '( e = g -> e = g )')
    cg, bg = w.wcongr(BOD('d', 'r', 'F', 'e'), {'e': 'g'}, 'e = g', {'e': idg})
    assert bg == BOD('d', 'r', 'F', 'g'), bg
    cb = w.s([cg], 'cbvralvw', '( A. e e. NN0 %s <-> A. g e. NN0 %s )' % (BOD('d', 'r', 'F', 'e'), BOD('d', 'r', 'F', 'g')))
    return w.s([cb], 'imbi2i', '( %s <-> %s )' % (INN('d', 'r', 'F'), INNG('d', 'r', 'F')))
def _b(w, B0):
    dn = w.s([], 'simpl', '( %s -> d e. NN )' % B0)
    rn = w.s([], 'simpr', '( %s -> r e. NN0 )' % B0)
    U = '( %s /\\ ( 2 <_ d /\\ 1 <_ r ) )' % B0
    V = '( %s /\\ e e. NN0 )' % U
    X = '( %s /\\ ( d <_ e /\\ e < ( d + 0 ) ) )' % V
    dr = w.s([w.s([dn], 'ad3antrrr', '( %s -> d e. NN )' % X)], 'nnred', '( %s -> d e. RR )' % X)
    er = w.s([w.s([], 'simplr', '( %s -> e e. NN0 )' % X)], 'nn0red', '( %s -> e e. RR )' % X)
    bad = lin.linarith(w, X, [w.s([], 'simprl', '( %s -> d <_ e )' % X), w.s([], 'simprr', '( %s -> e < ( d + 0 ) )' % X)], 'd < d',
                       leaves={'d': dr, 'e': er})
    nd = w.s([bad, w.s([dr], 'ltnrd', '( %s -> -. d < d )' % X)], 'pm2.21dd', '( %s -> -. e || %s )' % (X, G1('d', 'r', '0')))
    return w.s([w.s([w.s([nd], 'ex', '( %s -> %s )' % (V, BOD('d', 'r', '0', 'e')))], 'ralrimiva',
                    '( %s -> A. e e. NN0 %s )' % (U, BOD('d', 'r', '0', 'e')))], 'ex', '( %s -> %s )' % (B0, INN('d', 'r', '0')))
def _s(w, B, ctx):
    dn, rn, fn = ctx['dn'], ctx['rn'], ctx['fn']
    DO, q1, q2, d1n, s1, s2, p1, p2 = sgctx(w, B, ctx)
    SGP = G1('( d + 1 )', DO, 'F')
    U = '( %s /\\ ( 2 <_ d /\\ 1 <_ r ) )' % B
    dnU = w.s([dn], 'adantr', '( %s -> d e. NN )' % U)
    rnU = w.s([rn], 'adantr', '( %s -> r e. NN0 )' % U)
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    q1U = w.s([q1], 'adantr', '( %s -> %s e. NN0 )' % (U, DO))
    d1nU = w.s([d1n], 'adantr', '( %s -> ( d + 1 ) e. NN )' % U)
    s1U = w.s([s1], 'adantr', '( %s -> %s e. NN0 )' % (U, SGP))
    p1U = w.s([p1], 'adantr', '( %s -> %s = %s )' % (U, G1('d', 'r', '( F + 1 )'), SGP))
    d2 = w.s([], 'simprl', '( %s -> 2 <_ d )' % U)
    r1 = w.s([], 'simprr', '( %s -> 1 <_ r )' % U)
    dr = w.s([dnU], 'nnred', '( %s -> d e. RR )' % U)
    fr = w.s([fnU], 'nn0red', '( %s -> F e. RR )' % U)
    HD = '( ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) /\\ 1 <_ r )'
    q1pos = w.s([w.s([w.s([dnU, rnU, rnU], '3jca', '( %s -> ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) )' % U), r1], 'jca', '( %s -> %s )' % (U, HD)),
                 w.inst('divoutpos')], 'syl', '( %s -> 1 <_ %s )' % (U, DO))
    rle = w.s([], 'leidd', '( %s -> r <_ r )' % U)
    HN = '( ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) /\\ ( 2 <_ d /\\ 1 <_ r /\\ r <_ r ) )'
    ndvd = w.s([w.s([w.s([dnU, rnU, rnU], '3jca', '( %s -> ( d e. NN /\\ r e. NN0 /\\ r e. NN0 ) )' % U),
                     w.s([d2, r1, rle], '3jca', '( %s -> ( 2 <_ d /\\ 1 <_ r /\\ r <_ r ) )' % U)], 'jca', '( %s -> %s )' % (U, HN)),
                w.inst('divoutndvd')], 'syl', '( %s -> -. d || %s )' % (U, DO))
    sdvd = w.s([w.s([d1nU, q1U, fnU], '3jca', '( %s -> ( ( d + 1 ) e. NN /\\ %s e. NN0 /\\ F e. NN0 ) )' % (U, DO)), w.inst('smoothgodvd')], 'syl',
               '( %s -> %s || %s )' % (U, SGP, DO))
    d21 = lin.linarith(w, U, [d2], '2 <_ ( d + 1 )', leaves={'d': dr})
    ctxU = dict(ctx); ctxU['ihc'] = w.s([ctx['ihc']], 'adantr', '( %s -> %s )' % (U, 'A. c e. NN A. q e. NN0 ' + INNG('c', 'q', 'F')))
    ih = ihat(w, U, ctxU, '( d + 1 )', DO, d1nU, q1U)
    ihg = w.s([ih, w.s([d21, q1pos], 'jca', '( %s -> ( 2 <_ ( d + 1 ) /\\ 1 <_ %s ) )' % (U, DO))], 'mpd',
              '( %s -> A. g e. NN0 %s )' % (U, BOD('( d + 1 )', DO, 'F', 'g')))
    V = '( %s /\\ e e. NN0 )' % U
    X = '( %s /\\ ( d <_ e /\\ e < ( d + ( F + 1 ) ) ) )' % V
    en = w.s([], 'simplr', '( %s -> e e. NN0 )' % X)
    de = w.s([], 'simprl', '( %s -> d <_ e )' % X)
    elt = w.s([], 'simprr', '( %s -> e < ( d + ( F + 1 ) ) )' % X)
    drX = w.s([dr], 'ad2antrr', '( %s -> d e. RR )' % X)
    frX = w.s([fr], 'ad2antrr', '( %s -> F e. RR )' % X)
    erX = w.s([en], 'nn0red', '( %s -> e e. RR )' % X)
    p1X = w.s([p1U], 'ad2antrr', '( %s -> %s = %s )' % (X, G1('d', 'r', '( F + 1 )'), SGP))
    C1 = '( %s /\\ e = d )' % X
    dz = w.s([w.s([dnU], 'ad3antrrr', '( %s -> d e. NN )' % C1)], 'nnzd', '( %s -> d e. ZZ )' % C1)
    sz = w.s([w.s([s1U], 'ad3antrrr', '( %s -> %s e. NN0 )' % (C1, SGP))], 'nn0zd', '( %s -> %s e. ZZ )' % (C1, SGP))
    qz = w.s([w.s([q1U], 'ad3antrrr', '( %s -> %s e. NN0 )' % (C1, DO))], 'nn0zd', '( %s -> %s e. ZZ )' % (C1, DO))
    tr = w.s([w.s([dz, sz, qz], '3jca', '( %s -> ( d e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ ) )' % (C1, SGP, DO)), w.inst('dvdstr')], 'syl',
             '( %s -> ( ( d || %s /\\ %s || %s ) -> d || %s ) )' % (C1, SGP, SGP, DO, DO))
    Y = '( %s /\\ d || %s )' % (C1, SGP)
    got = w.s([w.s([tr], 'adantr', '( %s -> ( ( d || %s /\\ %s || %s ) -> d || %s ) )' % (Y, SGP, SGP, DO, DO)),
               w.s([w.s([], 'simpr', '( %s -> d || %s )' % (Y, SGP)),
                    w.s([sdvd], 'ad4antr', '( %s -> %s || %s )' % (Y, SGP, DO))], 'jca',
                   '( %s -> ( d || %s /\\ %s || %s ) )' % (Y, SGP, SGP, DO))], 'mpd', '( %s -> d || %s )' % (Y, DO))
    ndn = w.s([got, w.s([ndvd], 'ad4antr', '( %s -> -. d || %s )' % (Y, DO))], 'pm2.65da', '( %s -> -. d || %s )' % (C1, SGP))
    b1 = w.s([w.s([w.s([p1X], 'adantr', '( %s -> %s = %s )' % (C1, G1('d', 'r', '( F + 1 )'), SGP))], 'breq2d',
                  '( %s -> ( e || %s <-> e || %s ) )' % (C1, G1('d', 'r', '( F + 1 )'), SGP)),
              w.s([w.s([], 'simpr', '( %s -> e = d )' % C1)], 'breq1d', '( %s -> ( e || %s <-> d || %s ) )' % (C1, SGP, SGP))], 'bitrd',
             '( %s -> ( e || %s <-> d || %s ) )' % (C1, G1('d', 'r', '( F + 1 )'), SGP))
    c1 = w.s([ndn, b1], 'mtbird', '( %s -> -. e || %s )' % (C1, G1('d', 'r', '( F + 1 )')))
    C2 = '( %s /\\ -. e = d )' % X
    nev = w.s([w.s([], 'simpr', '( %s -> -. e = d )' % C2)], 'neqned', '( %s -> e =/= d )' % C2)
    drC = w.s([drX], 'adantr', '( %s -> d e. RR )' % C2)
    erC = w.s([erX], 'adantr', '( %s -> e e. RR )' % C2)
    frC = w.s([frX], 'adantr', '( %s -> F e. RR )' % C2)
    dlt = w.s([w.s([drC, erC], 'ltlend', '( %s -> ( d < e <-> ( d <_ e /\\ e =/= d ) ) )' % C2),
               w.s([w.s([de], 'adantr', '( %s -> d <_ e )' % C2), nev], 'jca', '( %s -> ( d <_ e /\\ e =/= d ) )' % C2)], 'mpbird',
              '( %s -> d < e )' % C2)
    d1le = w.s([w.s([w.s([w.s([dnU], 'ad3antrrr', '( %s -> d e. NN )' % C2)], 'nnzd', '( %s -> d e. ZZ )' % C2),
                     w.s([w.s([en], 'adantr', '( %s -> e e. NN0 )' % C2)], 'nn0zd', '( %s -> e e. ZZ )' % C2), w.inst('zltp1le')], 'syl2anc',
                    '( %s -> ( d < e <-> ( d + 1 ) <_ e ) )' % C2), dlt], 'mpbid', '( %s -> ( d + 1 ) <_ e )' % C2)
    eup = lin.linarith(w, C2, [w.s([elt], 'adantr', '( %s -> e < ( d + ( F + 1 ) ) )' % C2)], 'e < ( ( d + 1 ) + F )',
                       leaves={'d': drC, 'e': erC, 'F': frC})
    idg2 = w.s([], 'id', '( g = e -> g = e )')
    cg2, be = w.wcongr(BOD('( d + 1 )', DO, 'F', 'g'), {'g': 'e'}, 'g = e', {'g': idg2})
    inst = w.s([cg2, w.s([ihg], 'ad3antrrr', '( %s -> A. g e. NN0 %s )' % (C2, BOD('( d + 1 )', DO, 'F', 'g'))),
                w.s([en], 'adantr', '( %s -> e e. NN0 )' % C2)], 'rspcdva', '( %s -> %s )' % (C2, be))
    nds2 = w.s([inst, w.s([d1le, eup], 'jca', '( %s -> ( ( d + 1 ) <_ e /\\ e < ( ( d + 1 ) + F ) ) )' % C2)], 'mpd',
               '( %s -> -. e || %s )' % (C2, SGP))
    c2 = w.s([nds2, w.s([w.s([p1X], 'adantr', '( %s -> %s = %s )' % (C2, G1('d', 'r', '( F + 1 )'), SGP))], 'breq2d',
                        '( %s -> ( e || %s <-> e || %s ) )' % (C2, G1('d', 'r', '( F + 1 )'), SGP))], 'mtbird',
             '( %s -> -. e || %s )' % (C2, G1('d', 'r', '( F + 1 )')))
    nd = w.s([c1, c2], 'pm2.61dan', '( %s -> -. e || %s )' % (X, G1('d', 'r', '( F + 1 )')))
    return w.s([w.s([w.s([nd], 'ex', '( %s -> %s )' % (V, BOD('d', 'r', '( F + 1 )', 'e')))], 'ralrimiva',
                    '( %s -> A. e e. NN0 %s )' % (U, BOD('d', 'r', '( F + 1 )', 'e')))], 'ex', '( %s -> %s )' % (B, INN('d', 'r', '( F + 1 )')))
def _fin(w, PHI, INN, sbo, sbi):
    T = '( ( D e. NN /\\ R e. NN0 /\\ F e. NN0 ) /\\ ( 2 <_ D /\\ 1 <_ R ) )'
    dn = w.s([], 'simpl1', '( %s -> D e. NN )' % T)
    rn = w.s([], 'simpl2', '( %s -> R e. NN0 )' % T)
    fn = w.s([], 'simpl3', '( %s -> F e. NN0 )' % T)
    hy = w.s([], 'simpr', '( %s -> ( 2 <_ D /\\ 1 <_ R ) )' % T)
    ral = w.s([fn, w.inst('smoothgondvdl')], 'syl', '( %s -> %s )' % (T, PHI('F')))
    o = w.s([sbo(w, 'd', 'D', 'F', 'r'), ral, dn], 'rspcdva', '( %s -> A. r e. NN0 %s )' % (T, INN('D', 'r', 'F')))
    i = w.s([sbi(w, 'D', 'r', 'R', 'F'), o, rn], 'rspcdva', '( %s -> %s )' % (T, INN('D', 'R', 'F')))
    w.qed([i, hy], 'mpd', '( %s -> A. e e. NN0 %s )' % (T, BOD('D', 'R', 'F', 'e')))
sgfam('smoothgondvd', INN, _b, _s, 'The smoothness loop leaves no factor in the range it has swept (Lean: smoothGo_not_dvd).', _fin,
      only=only, INNC=INNG, innercbv=_icbv)

# ======================================================================= smoothTD
SGK = '( ( 2 SmoothGo K ) ` ( Y - 1 ) )'
SG1 = '( 1st ` %s )' % SGK
SG2 = '( 2nd ` %s )' % SGK
STV = '( Y SmoothTD K )'
SMO = 'A. p e. Prime ( p || K -> p <_ Y )'
ATD = '( ( Y e. NN /\\ K e. NN0 ) /\\ 1 <_ K )'
SMOP = 'A. p e. Prime ( p || K -> p <_ Y )'
SMOT = 'A. t e. Prime ( t || K -> t <_ Y )'

def tdctx(w, A, yn, kn):
    n2 = w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % A)
    ym1 = w.s([yn, w.inst('nnm1nn0')], 'syl', '( %s -> ( Y - 1 ) e. NN0 )' % A)
    scl = w.s([w.s([n2, kn], 'jca', '( %s -> ( 2 e. NN /\\ K e. NN0 ) )' % A), ym1, w.inst('smoothgocl')], 'syl2anc',
              '( %s -> %s e. ( NN0 X. NN0 ) )' % (A, SGK))
    a1, a2 = paircl(w, A, SGK, scl, 'NN0', 'NN0')
    sdvd = w.s([w.s([n2, kn, ym1], '3jca', '( %s -> ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) )' % A), w.inst('smoothgodvd')], 'syl',
               '( %s -> %s || K )' % (A, SG1))
    return n2, ym1, a1, a2, sdvd

if not only or 'smoothtdf' in only:
    w = W('smoothtdf', 'If the smoothness loop leaves 1 then every prime factor is small (Lean: the forward half of smoothTD_spec).')
    yn = w.s([], 'simpll', '( %s -> Y e. NN )' % ATD)
    kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % ATD)
    n2, ym1, a1, a2, sdvd = tdctx(w, ATD, yn, kn)
    B = '( %s /\\ %s = 1 )' % (ATD, SG1)
    C = '( %s /\\ p e. Prime )' % B
    D = '( %s /\\ p || K )' % C
    pp = w.s([], 'simplr', '( %s -> p e. Prime )' % D)
    pk = w.s([], 'simpr', '( %s -> p || K )' % D)
    pz = w.s([pp, w.inst('prmz')], 'syl', '( %s -> p e. ZZ )' % D)
    pr = w.s([pz], 'zred', '( %s -> p e. RR )' % D)
    p2 = w.s([w.s([w.s([pp, w.inst('prmuz2')], 'syl', '( %s -> p e. ( ZZ>= ` 2 ) )' % D), w.inst('eluz2')], 'sylib',
                  '( %s -> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )' % D)], 'simp3d', '( %s -> 2 <_ p )' % D)
    disj = w.s([w.s([w.s([w.s([n2], 'ad3antrrr', '( %s -> 2 e. NN )' % D), w.s([kn], 'ad3antrrr', '( %s -> K e. NN0 )' % D),
                          w.s([ym1], 'ad3antrrr', '( %s -> ( Y - 1 ) e. NN0 )' % D)], '3jca',
                         '( %s -> ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) )' % D),
                    w.s([pp, pk], 'jca', '( %s -> ( p e. Prime /\\ p || K ) )' % D)], 'jca',
                   '( %s -> ( ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) /\\ ( p e. Prime /\\ p || K ) ) )' % D), w.inst('smoothgoprm')], 'syl',
               '( %s -> ( p || %s \\/ p < ( 2 + ( Y - 1 ) ) ) )' % (D, SG1))
    E1 = '( %s /\\ p || %s )' % (D, SG1)
    pd1 = w.s([w.s([], 'simpr', '( %s -> p || %s )' % (E1, SG1)), w.s([], 'simp-4r', '( %s -> %s = 1 )' % (E1, SG1))], 'breqtrd',
              '( %s -> p || 1 )' % E1)
    ple1 = w.s([w.s([w.s([pz], 'adantr', '( %s -> p e. ZZ )' % E1), w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % E1),
                     w.inst('dvdsle')], 'syl2anc', '( %s -> ( p || 1 -> p <_ 1 ) )' % E1), pd1], 'mpd', '( %s -> p <_ 1 )' % E1)
    prE = w.s([pr], 'adantr', '( %s -> p e. RR )' % E1)
    bad = lin.linarith(w, E1, [ple1, w.s([p2], 'adantr', '( %s -> 2 <_ p )' % E1)], 'p < p', leaves={'p': prE})
    c1 = w.s([bad, w.s([prE], 'ltnrd', '( %s -> -. p < p )' % E1)], 'pm2.21dd', '( %s -> p <_ Y )' % E1)
    E2 = '( %s /\\ p < ( 2 + ( Y - 1 ) ) )' % D
    prF = w.s([pr], 'adantr', '( %s -> p e. RR )' % E2)
    ynF = w.s([yn], 'ad4antr', '( %s -> Y e. NN )' % E2)
    yrF = w.s([ynF], 'nnred', '( %s -> Y e. RR )' % E2)
    plty = lin.linarith(w, E2, [w.s([], 'simpr', '( %s -> p < ( 2 + ( Y - 1 ) ) )' % E2)], 'p < ( Y + 1 )', leaves={'p': prF, 'Y': yrF})
    c2 = w.s([w.s([w.s([pz], 'adantr', '( %s -> p e. ZZ )' % E2), w.s([ynF], 'nnzd', '( %s -> Y e. ZZ )' % E2), w.inst('zleltp1')], 'syl2anc',
                  '( %s -> ( p <_ Y <-> p < ( Y + 1 ) ) )' % E2), plty], 'mpbird', '( %s -> p <_ Y )' % E2)
    py = w.s([c1, c2, disj], 'mpjaodan', '( %s -> p <_ Y )' % D)
    w.qed([w.s([w.s([py], 'ex', '( %s -> ( p || K -> p <_ Y ) )' % C)], 'ralrimiva', '( %s -> %s )' % (B, SMOP))], 'ex',
          '( %s -> ( %s = 1 -> %s ) )' % (ATD, SG1, SMOP))
    run(w)

if not only or 'smoothtdb' in only:
    w = W('smoothtdb', 'If every prime factor is small then the smoothness loop leaves 1 (Lean: the backward half of smoothTD_spec).')
    yn = w.s([], 'simpll', '( %s -> Y e. NN )' % ATD)
    kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % ATD)
    k1 = w.s([], 'simpr', '( %s -> 1 <_ K )' % ATD)
    n2, ym1, a1, a2, sdvd = tdctx(w, ATD, yn, kn)
    le22 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.inst('leid')], 'ax-mp', '2 <_ 2')], 'a1i', '( %s -> 2 <_ 2 )' % ATD)
    B = '( %s /\\ %s )' % (ATD, SMOT)
    F_ = '( %s /\\ -. %s = 1 )' % (B, SG1)
    sn0 = w.s([a1], 'ad2antrr', '( %s -> %s e. NN0 )' % (F_, SG1))
    sdv = w.s([sdvd], 'ad2antrr', '( %s -> %s || K )' % (F_, SG1))
    knF = w.s([kn], 'ad2antrr', '( %s -> K e. NN0 )' % F_)
    k1F = w.s([k1], 'ad2antrr', '( %s -> 1 <_ K )' % F_)
    ynF = w.s([yn], 'ad2antrr', '( %s -> Y e. NN )' % F_)
    ym1F = w.s([ym1], 'ad2antrr', '( %s -> ( Y - 1 ) e. NN0 )' % F_)
    n2F = w.s([n2], 'ad2antrr', '( %s -> 2 e. NN )' % F_)
    le22F = w.s([le22], 'ad2antrr', '( %s -> 2 <_ 2 )' % F_)
    G_ = '( %s /\\ %s = 0 )' % (F_, SG1)
    kz = w.s([w.s([knF], 'adantr', '( %s -> K e. NN0 )' % G_)], 'nn0zd', '( %s -> K e. ZZ )' % G_)
    k0 = w.s([w.s([kz, w.inst('0dvds')], 'syl', '( %s -> ( 0 || K <-> K = 0 ) )' % G_),
              w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (G_, SG1)), w.s([sdv], 'adantr', '( %s -> %s || K )' % (G_, SG1))], 'eqbrtrrd',
                  '( %s -> 0 || K )' % G_)], 'mpbid', '( %s -> K = 0 )' % G_)
    bad2 = w.s([w.s([k1F], 'adantr', '( %s -> 1 <_ K )' % G_), k0], 'breqtrd', '( %s -> 1 <_ 0 )' % G_)
    n10 = w.s([w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % G_),
               w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % G_),
                    w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % G_)], 'ltnled', '( %s -> ( 0 < 1 <-> -. 1 <_ 0 ) )' % G_)], 'mpbid',
              '( %s -> -. 1 <_ 0 )' % G_)
    snz = w.s([bad2, n10], 'pm2.65da', '( %s -> -. %s = 0 )' % (F_, SG1))
    snn = w.s([sn0, w.s([snz], 'neqned', '( %s -> %s =/= 0 )' % (F_, SG1)), w.inst('elnnne0')], 'sylanbrc', '( %s -> %s e. NN )' % (F_, SG1))
    sne1 = w.s([w.s([], 'simpr', '( %s -> -. %s = 1 )' % (F_, SG1))], 'neqned', '( %s -> %s =/= 1 )' % (F_, SG1))
    s2 = w.s([w.s([snn, sne1], 'jca', '( %s -> ( %s e. NN /\\ %s =/= 1 ) )' % (F_, SG1, SG1)), w.inst('eluz2b3')], 'sylibr',
             '( %s -> %s e. ( ZZ>= ` 2 ) )' % (F_, SG1))
    ex = w.s([s2, w.inst('exprmfct')], 'syl', '( %s -> E. p e. Prime p || %s )' % (F_, SG1))
    H_ = '( %s /\\ ( p e. Prime /\\ p || %s ) )' % (F_, SG1)
    pp2 = w.s([], 'simprl', '( %s -> p e. Prime )' % H_)
    ps = w.s([], 'simprr', '( %s -> p || %s )' % (H_, SG1))
    pz2 = w.s([pp2, w.inst('prmz')], 'syl', '( %s -> p e. ZZ )' % H_)
    pr2 = w.s([pz2], 'zred', '( %s -> p e. RR )' % H_)
    p22 = w.s([w.s([w.s([pp2, w.inst('prmuz2')], 'syl', '( %s -> p e. ( ZZ>= ` 2 ) )' % H_), w.inst('eluz2')], 'sylib',
                   '( %s -> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )' % H_)], 'simp3d', '( %s -> 2 <_ p )' % H_)
    trz = w.s([pz2, w.s([w.s([sn0], 'adantr', '( %s -> %s e. NN0 )' % (H_, SG1))], 'nn0zd', '( %s -> %s e. ZZ )' % (H_, SG1)),
               w.s([w.s([knF], 'adantr', '( %s -> K e. NN0 )' % H_)], 'nn0zd', '( %s -> K e. ZZ )' % H_)], '3jca',
              '( %s -> ( p e. ZZ /\\ %s e. ZZ /\\ K e. ZZ ) )' % (H_, SG1))
    pdk = w.s([w.s([trz, w.inst('dvdstr')], 'syl', '( %s -> ( ( p || %s /\\ %s || K ) -> p || K ) )' % (H_, SG1, SG1)),
               w.s([ps, w.s([sdv], 'adantr', '( %s -> %s || K )' % (H_, SG1))], 'jca', '( %s -> ( p || %s /\\ %s || K ) )' % (H_, SG1, SG1))], 'mpd',
              '( %s -> p || K )' % H_)
    smoH = w.s([], 'simpllr', '( %s -> %s )' % (H_, SMOT))
    sbt = w.s([w.s([w.s([w.s([], 'id', '( t = p -> t = p )')], 'breq1d', '( t = p -> ( t || K <-> p || K ) )'),
                    w.s([w.s([], 'id', '( t = p -> t = p )')], 'breq1d', '( t = p -> ( t <_ Y <-> p <_ Y ) )')], 'imbi12d',
                   '( t = p -> ( ( t || K -> t <_ Y ) <-> ( p || K -> p <_ Y ) ) )')], 'id',
              '( t = p -> ( ( t || K -> t <_ Y ) <-> ( p || K -> p <_ Y ) ) )')
    w.lines.pop()
    sbt = w.s([w.s([w.s([], 'id', '( t = p -> t = p )')], 'breq1d', '( t = p -> ( t || K <-> p || K ) )'),
               w.s([w.s([], 'id', '( t = p -> t = p )')], 'breq1d', '( t = p -> ( t <_ Y <-> p <_ Y ) )')], 'imbi12d',
              '( t = p -> ( ( t || K -> t <_ Y ) <-> ( p || K -> p <_ Y ) ) )')
    pyH = w.s([sbt, smoH, pp2], 'rspcdva', '( %s -> ( p || K -> p <_ Y ) )' % H_)
    pyv = w.s([pyH, pdk], 'mpd', '( %s -> p <_ Y )' % H_)
    yrH = w.s([w.s([ynF], 'adantr', '( %s -> Y e. NN )' % H_)], 'nnred', '( %s -> Y e. RR )' % H_)
    plt = lin.linarith(w, H_, [pyv], 'p < ( 2 + ( Y - 1 ) )', leaves={'p': pr2, 'Y': yrH})
    ndv = w.s([w.s([w.s([w.s([n2F], 'adantr', '( %s -> 2 e. NN )' % H_), w.s([knF], 'adantr', '( %s -> K e. NN0 )' % H_),
                         w.s([ym1F], 'adantr', '( %s -> ( Y - 1 ) e. NN0 )' % H_)], '3jca',
                        '( %s -> ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) )' % H_),
                   w.s([w.s([le22F], 'adantr', '( %s -> 2 <_ 2 )' % H_), w.s([k1F], 'adantr', '( %s -> 1 <_ K )' % H_)], 'jca',
                       '( %s -> ( 2 <_ 2 /\\ 1 <_ K ) )' % H_)], 'jca',
                  '( %s -> ( ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) /\\ ( 2 <_ 2 /\\ 1 <_ K ) ) )' % H_), w.inst('smoothgondvd')], 'syl',
              '( %s -> A. e e. NN0 ( ( 2 <_ e /\\ e < ( 2 + ( Y - 1 ) ) ) -> -. e || %s ) )' % (H_, SG1))
    sbe = w.s([w.s([w.s([w.s([], 'id', '( e = p -> e = p )')], 'breq2d', '( e = p -> ( 2 <_ e <-> 2 <_ p ) )'),
                    w.s([w.s([], 'id', '( e = p -> e = p )')], 'breq1d', '( e = p -> ( e < ( 2 + ( Y - 1 ) ) <-> p < ( 2 + ( Y - 1 ) ) ) )')], 'anbi12d',
                   '( e = p -> ( ( 2 <_ e /\\ e < ( 2 + ( Y - 1 ) ) ) <-> ( 2 <_ p /\\ p < ( 2 + ( Y - 1 ) ) ) ) )'),
               w.s([w.s([w.s([], 'id', '( e = p -> e = p )')], 'breq1d', '( e = p -> ( e || %s <-> p || %s ) )' % (SG1, SG1))], 'notbid',
                   '( e = p -> ( -. e || %s <-> -. p || %s ) )' % (SG1, SG1))], 'imbi12d',
              '( e = p -> ( ( ( 2 <_ e /\\ e < ( 2 + ( Y - 1 ) ) ) -> -. e || %s ) <-> ( ( 2 <_ p /\\ p < ( 2 + ( Y - 1 ) ) ) -> -. p || %s ) ) )' % (SG1, SG1))
    pn0 = w.s([w.s([pp2, w.inst('prmnn')], 'syl', '( %s -> p e. NN )' % H_)], 'nnnn0d', '( %s -> p e. NN0 )' % H_)
    insts = w.s([sbe, ndv, pn0], 'rspcdva', '( %s -> ( ( 2 <_ p /\\ p < ( 2 + ( Y - 1 ) ) ) -> -. p || %s ) )' % (H_, SG1))
    nps = w.s([insts, w.s([p22, plt], 'jca', '( %s -> ( 2 <_ p /\\ p < ( 2 + ( Y - 1 ) ) ) )' % H_)], 'mpd', '( %s -> -. p || %s )' % (H_, SG1))
    absurd = w.s([ps, nps], 'pm2.21dd', '( %s -> %s = 1 )' % (H_, SG1))
    elim = w.s([w.s([absurd], 'rexlimdvaa', '( %s -> ( E. p e. Prime p || %s -> %s = 1 ) )' % (F_, SG1, SG1)), ex], 'mpd',
               '( %s -> %s = 1 )' % (F_, SG1))
    got = w.s([elim, w.s([], 'simpr', '( %s -> -. %s = 1 )' % (F_, SG1))], 'pm2.65da', '( %s -> -. -. %s = 1 )' % (B, SG1))
    w.qed([w.s([got], 'notnotrd', '( %s -> %s = 1 )' % (B, SG1))], 'ex', '( %s -> ( %s -> %s = 1 ) )' % (ATD, SMOT, SG1))
    run(w)

if not only or 'smoothtdbi' in only:
    w = W('smoothtdbi', 'The smoothness loop leaves 1 exactly when every prime factor is small.')
    f = w.s([], 'smoothtdf', '( %s -> ( %s = 1 -> %s ) )' % (ATD, SG1, SMOP))
    b = w.s([], 'smoothtdb', '( %s -> ( %s -> %s = 1 ) )' % (ATD, SMOT, SG1))
    cbv = w.s([w.s([w.s([w.s([], 'id', '( p = t -> p = t )')], 'breq1d', '( p = t -> ( p || K <-> t || K ) )'),
                    w.s([w.s([], 'id', '( p = t -> p = t )')], 'breq1d', '( p = t -> ( p <_ Y <-> t <_ Y ) )')], 'imbi12d',
                   '( p = t -> ( ( p || K -> p <_ Y ) <-> ( t || K -> t <_ Y ) ) )')], 'cbvralvw', '( %s <-> %s )' % (SMOP, SMOT))
    b2 = w.s([w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (ATD, SMOP, SMOT))], 'biimpd', '( %s -> ( %s -> %s ) )' % (ATD, SMOP, SMOT)), b],
             'syld', '( %s -> ( %s -> %s = 1 ) )' % (ATD, SMOP, SG1))
    w.qed([f, b2], 'impbid', '( %s -> ( %s = 1 <-> %s ) )' % (ATD, SG1, SMOP))
    run(w)

if not only or 'smoothtdspec' in only:
    w = W('smoothtdspec', 'smoothTD decides smoothness (Lean: smoothTD_spec).')
    yn = w.s([], 'simpll', '( %s -> Y e. NN )' % ATD)
    kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % ATD)
    n2, ym1, a1, a2, sdvd = tdctx(w, ATD, yn, kn)
    v = w.s([yn, kn, w.inst('smoothtdval')], 'syl2anc', '( %s -> %s = <. if ( %s = 1 , 1o , (/) ) , ( %s + 1 ) >. )' % (ATD, STV, SG1, SG2))
    xa = w.s([w.s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % ATD),
              w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % ATD)], 'ifcld', '( %s -> if ( %s = 1 , 1o , (/) ) e. 2o )' % (ATD, SG1))
    xb = w.s([a2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ATD, SG2))
    p1 = projeq(w, ATD, STV, v, 'if ( %s = 1 , 1o , (/) )' % SG1, '( %s + 1 )' % SG2, xa, xb, 1)
    st, sf = ifproj(w, ATD, '( 1st ` %s )' % STV, p1, '%s = 1' % SG1, '1o', '(/)')
    bi = w.s([], 'smoothtdbi', '( %s -> ( %s = 1 <-> %s ) )' % (ATD, SG1, SMOP))
    T = '( %s /\\ %s = 1 )' % (ATD, SG1)
    F_ = '( %s /\\ -. %s = 1 )' % (ATD, SG1)
    lt = w.s([st, w.s([], 'eqidd', '( %s -> 1o = 1o )' % T)], 'eqtrd', '( %s -> ( 1st ` %s ) = 1o )' % (T, STV))
    rt = w.s([w.s([bi], 'adantr', '( %s -> ( %s = 1 <-> %s ) )' % (T, SG1, SMOP)), w.s([], 'simpr', '( %s -> %s = 1 )' % (T, SG1))], 'mpbid',
             '( %s -> %s )' % (T, SMOP))
    ct = w.s([lt, rt], '2thd', '( %s -> ( ( 1st ` %s ) = 1o <-> %s ) )' % (T, STV, SMOP))
    nl = w.s([w.s([sf], 'eqeq1d', '( %s -> ( ( 1st ` %s ) = 1o <-> (/) = 1o ) )' % (F_, STV)), zne1o(w, F_)], 'mtbird',
             '( %s -> -. ( 1st ` %s ) = 1o )' % (F_, STV))
    nr = w.s([w.s([], 'simpr', '( %s -> -. %s = 1 )' % (F_, SG1)), w.s([bi], 'adantr', '( %s -> ( %s = 1 <-> %s ) )' % (F_, SG1, SMOP))], 'mtbid',
             '( %s -> -. %s )' % (F_, SMOP))
    cf = w.s([nl, nr], '2falsed', '( %s -> ( ( 1st ` %s ) = 1o <-> %s ) )' % (F_, STV, SMOP))
    w.qed([ct, cf], 'pm2.61dan', '( %s -> ( ( 1st ` %s ) = 1o <-> %s ) )' % (ATD, STV, SMOP))
    run(w)

if not only or 'smoothtdcost' in only:
    w = W('smoothtdcost', 'The cost of smoothTD (Lean: smoothTD_cost).')
    A = '( Y e. NN /\\ K e. NN0 )'
    yn = w.s([], 'simpl', '( %s -> Y e. NN )' % A)
    kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A)
    n2, ym1, a1, a2, sdvd = tdctx(w, A, yn, kn)
    le22 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.inst('leid')], 'ax-mp', '2 <_ 2')], 'a1i', '( %s -> 2 <_ 2 )' % A)
    v = w.s([yn, kn, w.inst('smoothtdval')], 'syl2anc', '( %s -> %s = <. if ( %s = 1 , 1o , (/) ) , ( %s + 1 ) >. )' % (A, STV, SG1, SG2))
    xa = w.s([w.s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % A),
              w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % A)], 'ifcld', '( %s -> if ( %s = 1 , 1o , (/) ) e. 2o )' % (A, SG1))
    xb = w.s([a2, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (A, SG2))
    p2 = projeq(w, A, STV, v, 'if ( %s = 1 , 1o , (/) )' % SG1, '( %s + 1 )' % SG2, xa, xb, 2)
    cost = w.s([w.s([w.s([n2, kn, ym1], '3jca', '( %s -> ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) )' % A), le22], 'jca',
                    '( %s -> ( ( 2 e. NN /\\ K e. NN0 /\\ ( Y - 1 ) e. NN0 ) /\\ 2 <_ 2 ) )' % A), w.inst('smoothgocost')], 'syl',
               '( %s -> ( %s + %s ) <_ ( ( Y - 1 ) + %s ) )' % (A, SG2, LG(SG1), LG('K')))
    lgs = lgcl(w, A, SG1, a1)
    lgk = lgcl(w, A, 'K', kn)
    lgs0 = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), a1, w.inst('nlogcl')], 'syl2anc',
                    '( %s -> %s e. NN0 )' % (A, LG(SG1)))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A, LG(SG1)))
    s2r = w.s([a2], 'nn0red', '( %s -> %s e. RR )' % (A, SG2))
    yr = w.s([yn], 'nnred', '( %s -> Y e. RR )' % A)
    li = lin.linarith(w, A, [cost, lgs0], '( %s + 1 ) <_ ( ( Y + %s ) + 2 )' % (SG2, LG('K')),
                      leaves={SG2: s2r, LG(SG1): lgs, LG('K'): lgk, 'Y': yr})
    w.qed([p2, li], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( ( Y + %s ) + 2 ) )' % (A, STV, LG('K')))
    run(w)
