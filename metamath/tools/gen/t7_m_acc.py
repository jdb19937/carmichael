"""T7: the accumulator of the multiplication loop (Lean ` mulGo [] xs ( take i ys ) ` ,
` condAdd ` ): the word after ` i ` iterations as a ` seq ` , its step, typing,
length bound and value (Lean ` toNat_mulGo ` , ` mulGo_length ` )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from cl import Closure
from lin import linarith, lineq

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN, LN2 = '( # ` L )', "( # ` L' )"
TA = '( toNat ` L )'


def tmcacc0():
    w = W('tmcacc0', 'The accumulator of the multiplication starts empty (Lean ` mulGo [] xs [] = [] ` ).')
    s1 = w.s([closed(w, '0 e. ZZ', '0z', '0 e. ZZ') if False else w.s([], '0z', '0 e. ZZ'), w.inst('seq1')], 'ax-mp' if False else 'syl', '') if False else None
    z = w.s([], '0z', '0 e. ZZ')
    s1 = w.s([z, w.inst('seq1')], 'ax-mp', '%s = ( %s ` 0 )' % (ACCN('0'), INITF))
    idk = w.s([], 'id', '( k = 0 -> k = 0 )')
    cg, new = w.congr(INITB('k'), {'k': '0'}, 'k = 0', {'k': idk})
    assert new == INITB('0')
    iv = w.s([w.s([], '0ex', '(/) e. _V'), w.s([], 'ovex', '( 0 - 1 ) e. _V')], 'ifex', '%s e. _V' % INITB('0'))
    fv = w.s([cg, w.s([], 'eqid', '%s = %s' % (INITF, INITF)), iv], 'fvmpt', '( 0 e. NN0 -> ( %s ` 0 ) = %s )' % (INITF, INITB('0')))
    fv2 = w.s([w.s([], '0nn0', '0 e. NN0'), fv], 'ax-mp', '( %s ` 0 ) = %s' % (INITF, INITB('0')))
    it = w.s([w.s([], 'eqid', '0 = 0')], 'iftruei' if False else 'ifeq1' if False else 'iftruei', '') if False else None
    it = w.s([w.s([], 'eqid', '0 = 0'), w.inst('iftrue')], 'ax-mp', '%s = (/)' % INITB('0'))
    w.qed([s1, w.s([fv2, it], 'eqtri', '( %s ` 0 ) = (/)' % INITF)], 'eqtri', ST_ACC0)
    return w.run()


def tmcaccs():
    ph = 'N e. NN0'
    w = W('tmcaccs', 'The step of the multiplication accumulator (Lean ` condAdd ` ): iteration ` N ` adds the '
                     'multiplicand shifted by ` N ` when bit ` N ` of the multiplier is set.')
    nn = w.s([], 'id', '( N e. NN0 -> N e. NN0 )')
    nu = w.s([nn, w.s([], 'elnn0uz', '( N e. NN0 <-> N e. ( ZZ>= ` 0 ) )')], 'sylib', '( %s -> N e. ( ZZ>= ` 0 ) )' % ph)
    s1 = w.s([nu, w.inst('seqp1')], 'syl', '( %s -> %s = ( %s %s ( %s ` ( N + 1 ) ) ) )' % (ph, ACCN('( N + 1 )'), ACCN('N'), STEPF, INITF))
    n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    iex = w.s([w.s([], '0ex', '(/) e. _V'), w.s([], 'ovex', '( ( N + 1 ) - 1 ) e. _V')], 'ifex', '%s e. _V' % INITB('( N + 1 )'))
    iv = mval(w, ph, 'k', 'NN0', INITB, '( N + 1 )', n1, w.s([iex], 'a1i', '( %s -> %s e. _V )' % (ph, INITB('( N + 1 )'))))
    nz = w.s([w.s([nn, w.inst('nn0p1nn')], 'syl', '( %s -> ( N + 1 ) e. NN )' % ph), w.inst('nnne0')], 'syl', '( %s -> ( N + 1 ) =/= 0 )' % ph)
    nz2 = w.s([nz], 'neneqd', '( %s -> -. ( N + 1 ) = 0 )' % ph)
    if1 = w.s([nz2], 'iffalsed', '( %s -> %s = ( ( N + 1 ) - 1 ) )' % (ph, INITB('( N + 1 )')))
    pc = w.s([w.s([nn], 'nn0cnd', '( %s -> N e. CC )' % ph), w.s([], '1cnd', '( %s -> 1 e. CC )' % ph)], 'pncand', '( %s -> ( ( N + 1 ) - 1 ) = N )' % ph)
    iv2 = w.s([w.s([iv, if1], 'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = ( ( N + 1 ) - 1 ) )' % (ph, INITF)), pc], 'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = N )' % (ph, INITF))
    s2 = w.s([iv2], 'oveq2d', '( %s -> ( %s %s ( %s ` ( N + 1 ) ) ) = ( %s %s N ) )' % (ph, ACCN('N'), STEPF, INITF, ACCN('N'), STEPF))
    # rename the binders of the step so that the accumulator (which contains a and b) can be substituted
    ida = w.s([], 'id', '( a = c -> a = c )')
    c1, n1_ = w.congr(STEPB('a', 'b'), {'a': 'c'}, 'a = c', {'a': ida})
    idb = w.s([], 'id', '( b = d -> b = d )')
    c2, n2_ = w.congr(STEPB('c', 'b'), {'b': 'd'}, 'b = d', {'b': idb})
    assert n1_ == STEPB('c', 'b') and n2_ == STEPB('c', 'd')
    cb = w.s([c1, c2], 'cbvmpov', '%s = %s' % (STEPF, STEPG))
    s3 = w.s([w.s([cb], 'a1i', '( %s -> %s = %s )' % (ph, STEPF, STEPG))], 'oveqd', '( %s -> ( %s %s N ) = ( %s %s N ) )' % (ph, ACCN('N'), STEPF, ACCN('N'), STEPG))
    A = ACCN('N')
    idc = w.s([], 'id', '( c = %s -> c = %s )' % (A, A))
    e1, m1 = w.congr(STEPB('c', 'd'), {'c': A}, 'c = %s' % A, {'c': idc})
    idd = w.s([], 'id', '( d = N -> d = N )')
    e2, m2 = w.congr(STEPB(A, 'd'), {'d': 'N'}, 'd = N', {'d': idd})
    assert m1 == STEPB(A, 'd') and m2 == STEPB(A, 'N')
    ov = w.s([e1, e2, w.s([], 'eqid', '%s = %s' % (STEPG, STEPG))], 'ovmpog',
             '( ( %s e. _V /\\ N e. _V /\\ %s e. _V ) -> ( %s %s N ) = %s )' % (A, STEPB(A, 'N'), A, STEPG, STEPB(A, 'N')))
    av = closed(w, ph, 'fvex', '%s e. _V' % A)
    nv = w.s([nn], 'elexd', '( %s -> N e. _V )' % ph)
    sv = w.s([w.s([], 'fvex', "( ( %s addBits %s ) ` (/) ) e. _V" % (A, SHF('N'))), w.s([], 'fvex', '%s e. _V' % A)], 'ifex', '%s e. _V' % STEPB(A, 'N'))
    s4 = w.s([av, nv, w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ph, STEPB(A, 'N'))), ov], 'syl3anc', '( %s -> ( %s %s N ) = %s )' % (ph, A, STEPG, STEPB(A, 'N')))
    ch = w.s([w.s([w.s([s1, s2], 'eqtrd', '( %s -> %s = ( %s %s N ) )' % (ph, ACCN('( N + 1 )'), A, STEPF)), s3], 'eqtrd',
                  '( %s -> %s = ( %s %s N ) )' % (ph, ACCN('( N + 1 )'), A, STEPG)), s4], 'eqtrd', '( %s -> %s = %s )' % (ph, ACCN('( N + 1 )'), STEPB(A, 'N')))
    w.qed([ch], 'id' if False else 'syl' if False else 'mpbi' if False else 'eqtrd' if False else 'id', ST_ACCS) if False else None
    w.lines[-1] = w.lines[-1].replace('%s:' % ch, 'qed:', 1) if False else w.lines[-1]
    # turn the last step into qed
    last = w.lines.pop()
    name, rest = last.split(':', 1)
    assert name == ch
    w.lines.append('qed:' + rest)
    return w.run()


def tmcacc():
    ph = PH_LL
    w = W('tmcacc', 'The accumulator of the multiplication after ` N ` iterations is a bit word of length at most '
                    '` ( # ` L ) + N ` whose value, while ` N ` is within the multiplier, is the multiplicand times the '
                    'value of the first ` N ` multiplier bits (Lean ` mulGo_length ` , ` toNat_mulGo ` ).')
    P = PACC
    subs = []
    for tgt, idl in [('0', 'x = 0'), ('y', 'x = y'), ('( y + 1 )', 'x = ( y + 1 )'), ('N', 'x = N')]:
        idx = w.s([], 'id', '( %s -> %s )' % (idl, idl))
        cg, new = w.wcongr(P('x'), {'x': tgt}, idl, {'x': idx})
        assert new == P(tgt), (new, P(tgt))
        subs.append(cg)
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    # ---- base
    a0 = closed(w, ph, 'tmcacc0', ST_ACC0)
    wz = w.s([a0, closed(w, ph, 'wrd0', '(/) e. Word 2o')], 'eqeltrd', '( %s -> %s e. Word 2o )' % (ph, ACCN('0')))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN))
    l0 = w.s([w.s([a0], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` (/) ) )' % (ph, ACCN('0'))), closed(w, ph, 'hash0', '( # ` (/) ) = 0')], 'eqtrd',
             '( %s -> ( # ` %s ) = 0 )' % (ph, ACCN('0')))
    c0 = Closure(w, ph, {LN: ('NN0', la), '( # ` %s )' % ACCN('0'): ('NN0', w.s([wz, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ACCN('0'))))})
    le0 = linarith(w, ph, [l0, c0.ge0(LN)], '( # ` %s ) <_ ( %s + 0 )' % (ACCN('0'), LN), closure=c0, atoms=['( # ` %s )' % ACCN('0')])
    t0 = w.s([w.s([a0], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` (/) ) )' % (ph, ACCN('0'))), closed(w, ph, 'tonat0', '( toNat ` (/) ) = 0')], 'eqtrd',
             '( %s -> ( toNat ` %s ) = 0 )' % (ph, ACCN('0')))
    p0 = w.s([closed(w, ph, 'pfx00', "( L' prefix 0 ) = (/)")], 'fveq2d', "( %s -> ( toNat ` ( L' prefix 0 ) ) = ( toNat ` (/) ) )" % ph)
    p0b = w.s([p0, closed(w, ph, 'tonat0', '( toNat ` (/) ) = 0')], 'eqtrd', "( %s -> ( toNat ` ( L' prefix 0 ) ) = 0 )" % ph)
    tl = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TA))
    m0 = w.s([w.s([p0b], 'oveq2d', "( %s -> ( %s x. ( toNat ` ( L' prefix 0 ) ) ) = ( %s x. 0 ) )" % (ph, TA, TA)),
              w.s([w.s([tl], 'nn0cnd', '( %s -> %s e. CC )' % (ph, TA))], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (ph, TA))], 'eqtrd',
             "( %s -> ( %s x. ( toNat ` ( L' prefix 0 ) ) ) = 0 )" % (ph, TA))
    v0 = w.s([w.s([t0, m0], 'eqtr4d', "( %s -> ( toNat ` %s ) = ( %s x. ( toNat ` ( L' prefix 0 ) ) ) )" % (ph, ACCN('0'), TA))], 'a1d',
             "( %s -> ( 0 <_ %s -> ( toNat ` %s ) = ( %s x. ( toNat ` ( L' prefix 0 ) ) ) ) )" % (ph, LN2, ACCN('0'), TA))
    base = w.s([w.s([wz, le0], 'jca', '( %s -> ( %s e. Word 2o /\\ ( # ` %s ) <_ ( %s + 0 ) ) )' % (ph, ACCN('0'), ACCN('0'), LN)), v0], 'jca',
               '( %s -> %s )' % (ph, P('0')))
    # ---- step
    ps = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (ph, P('y'))
    A_ = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ps, f))
    AA = lambda st, f: w.s([st], 'adantlr', '( %s -> %s )' % (ps, f)) if False else None
    yy = w.s([], 'simplr', '( %s -> y e. NN0 )' % ps)
    llp = w.s([w.s([], 'simpll', '( %s -> %s )' % (ps, ph))], 'simpld', '( %s -> L e. Word 2o )' % ps)
    ll2p = w.s([w.s([], 'simpll', '( %s -> %s )' % (ps, ph))], 'simprd', "( %s -> L' e. Word 2o )" % ps)
    ih = w.s([], 'simpr', '( %s -> %s )' % (ps, P('y')))
    ihp = parts(w, ps, ih, parse_conj(P('y')))
    ih1 = ihp['%s e. Word 2o' % ACCN('y')]
    ih2 = ihp['( # ` %s ) <_ ( %s + y )' % (ACCN('y'), LN)]
    ih3 = ihp["( y <_ %s -> ( toNat ` %s ) = ( %s x. ( toNat ` ( L' prefix y ) ) ) )" % (LN2, ACCN('y'), TA)]
    Y1 = '( y + 1 )'
    AB = '( ( %s addBits %s ) ` (/) )' % (ACCN('y'), SHF('y'))
    IFA = STEPB(ACCN('y'), 'y')
    st = w.s([yy, w.inst('tmcaccs')], 'syl', '( %s -> %s = %s )' % (ps, ACCN(Y1), IFA))
    b0 = closed(w, ps, '0el2o', '(/) e. 2o')
    rw = w.s([b0, yy, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS y ) e. Word 2o )' % ps)
    shw = w.s([rw, llp, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, SHF('y')))
    abw = w.s([ih1, shw, b0, w.inst('addbitscl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ps, AB))
    wy1 = w.s([st, w.s([abw, ih1], 'ifcld', '( %s -> %s e. Word 2o )' % (ps, IFA))], 'eqeltrd', '( %s -> %s e. Word 2o )' % (ps, ACCN(Y1)))
    lap, lbp = w.s([llp, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LN)), w.s([ll2p, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LN2))
    lacc = w.s([ih1, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, ACCN('y')))
    lsh = w.s([shw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, SHF('y')))
    shl = w.s([w.s([rw, llp, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` ( (/) repeatS y ) ) + %s ) )' % (ps, SHF('y'), LN)),
               w.s([w.s([w.s([b0, yy, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS y ) ) = y )' % ps)], 'oveq1d',
                        '( %s -> ( ( # ` ( (/) repeatS y ) ) + %s ) = ( y + %s ) )' % (ps, LN, LN))], 'id', '') if False else
               w.s([w.s([b0, yy, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS y ) ) = y )' % ps)], 'oveq1d',
                   '( %s -> ( ( # ` ( (/) repeatS y ) ) + %s ) = ( y + %s ) )' % (ps, LN, LN))], 'eqtrd', '( %s -> ( # ` %s ) = ( y + %s ) )' % (ps, SHF('y'), LN))
    cs = Closure(w, ps, {'y': ('NN0', yy), LN: ('NN0', lap), LN2: ('NN0', lbp), '( # ` %s )' % ACCN('y'): ('NN0', lacc), '( # ` %s )' % SHF('y'): ('NN0', lsh)})
    C1 = "( L' ` y ) = 1o"
    # length, case set bit
    pa = '( %s /\\ %s )' % (ps, C1)
    Aa = lambda s_, f: w.s([s_], 'adantr', '( %s -> %s )' % (pa, f))
    ea = w.s([Aa(st, '%s = %s' % (ACCN(Y1), IFA)), w.s([w.s([], 'simpr', '( %s -> %s )' % (pa, C1))], 'iftrued', '( %s -> %s = %s )' % (pa, IFA, AB))], 'eqtrd',
             '( %s -> %s = %s )' % (pa, ACCN(Y1), AB))
    MXS = 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (ACCN('y'), SHF('y'), SHF('y'), ACCN('y'))
    abl = w.s([Aa(ih1, '%s e. Word 2o' % ACCN('y')), Aa(shw, '%s e. Word 2o' % SHF('y')), closed(w, pa, '0el2o', '(/) e. 2o'), w.inst('addbitslen')], 'syl3anc',
              '( %s -> ( # ` %s ) <_ ( %s + 1 ) )' % (pa, AB, MXS))
    ca = Closure(w, pa, {'y': ('NN0', Aa(yy, 'y e. NN0')), LN: ('NN0', Aa(lap, '%s e. NN0' % LN)), '( # ` %s )' % ACCN('y'): ('NN0', Aa(lacc, '( # ` %s ) e. NN0' % ACCN('y'))),
                         '( # ` %s )' % SHF('y'): ('NN0', Aa(lsh, '( # ` %s ) e. NN0' % SHF('y')))})
    mxle = w.s([ca.mem('( # ` %s )' % ACCN('y'), 'RR'), ca.mem('( # ` %s )' % SHF('y'), 'RR'), ca.mem('( %s + y )' % LN, 'RR'), w.inst('maxle')], 'syl3anc',
               '( %s -> ( %s <_ ( %s + y ) <-> ( ( # ` %s ) <_ ( %s + y ) /\\ ( # ` %s ) <_ ( %s + y ) ) ) )' % (pa, MXS, LN, ACCN('y'), LN, SHF('y'), LN))
    shle = linarith(w, pa, [Aa(shl, '( # ` %s ) = ( y + %s )' % (SHF('y'), LN))], '( # ` %s ) <_ ( %s + y )' % (SHF('y'), LN), closure=ca)
    mx = w.s([mxle, w.s([Aa(ih2, '( # ` %s ) <_ ( %s + y )' % (ACCN('y'), LN)), shle], 'jca',
                        '( %s -> ( ( # ` %s ) <_ ( %s + y ) /\\ ( # ` %s ) <_ ( %s + y ) ) )' % (pa, ACCN('y'), LN, SHF('y'), LN))], 'mpbird',
             '( %s -> %s <_ ( %s + y ) )' % (pa, MXS, LN))
    ca.leaf(MXS, 'RR', w.s([w.s([Aa(lsh, '( # ` %s ) e. NN0' % SHF('y')), Aa(lacc, '( # ` %s ) e. NN0' % ACCN('y'))], 'ifcld', '( %s -> %s e. NN0 )' % (pa, MXS))], 'nn0red',
                            '( %s -> %s e. RR )' % (pa, MXS)))
    ca.leaf('( # ` %s )' % AB, 'NN0', w.s([w.s([Aa(ih1, '%s e. Word 2o' % ACCN('y')), Aa(shw, '%s e. Word 2o' % SHF('y')), closed(w, pa, '0el2o', '(/) e. 2o'),
                                                w.inst('addbitscl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (pa, AB)), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pa, AB)))
    lab_ = linarith(w, pa, [abl, mx], '( # ` %s ) <_ ( %s + %s )' % (AB, LN, Y1), closure=ca)
    lena = w.s([w.s([ea], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (pa, ACCN(Y1), AB)), lab_], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( %s + %s ) )' % (pa, ACCN(Y1), LN, Y1))
    # length, case clear bit
    pb = '( %s /\\ -. %s )' % (ps, C1)
    Ab = lambda s_, f: w.s([s_], 'adantr', '( %s -> %s )' % (pb, f))
    eb = w.s([Ab(st, '%s = %s' % (ACCN(Y1), IFA)), w.s([w.s([], 'simpr', '( %s -> -. %s )' % (pb, C1))], 'iffalsed', '( %s -> %s = %s )' % (pb, IFA, ACCN('y')))], 'eqtrd',
             '( %s -> %s = %s )' % (pb, ACCN(Y1), ACCN('y')))
    cb = Closure(w, pb, {'y': ('NN0', Ab(yy, 'y e. NN0')), LN: ('NN0', Ab(lap, '%s e. NN0' % LN)), '( # ` %s )' % ACCN('y'): ('NN0', Ab(lacc, '( # ` %s ) e. NN0' % ACCN('y')))})
    lbb = linarith(w, pb, [Ab(ih2, '( # ` %s ) <_ ( %s + y )' % (ACCN('y'), LN))], '( # ` %s ) <_ ( %s + %s )' % (ACCN('y'), LN, Y1), closure=cb)
    lenb = w.s([w.s([eb], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (pb, ACCN(Y1), ACCN('y'))), lbb], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( %s + %s ) )' % (pb, ACCN(Y1), LN, Y1))
    leny = w.s([lena, lenb], 'pm2.61dan', '( %s -> ( # ` %s ) <_ ( %s + %s ) )' % (ps, ACCN(Y1), LN, Y1))
    # value
    pv = '( %s /\\ %s <_ %s )' % (ps, Y1, LN2)
    Av = lambda s_, f: w.s([s_], 'adantr', '( %s -> %s )' % (pv, f))
    le1 = w.s([], 'simpr', '( %s -> %s <_ %s )' % (pv, Y1, LN2))
    yv = Av(yy, 'y e. NN0')
    cv = Closure(w, pv, {'y': ('NN0', yv), LN2: ('NN0', Av(lbp, '%s e. NN0' % LN2))})
    ylt = linarith(w, pv, [le1], 'y < %s' % LN2, closure=cv)
    yle = linarith(w, pv, [le1], 'y <_ %s' % LN2, closure=cv)
    ih3v = w.s([yle, Av(ih3, "( y <_ %s -> ( toNat ` %s ) = ( %s x. ( toNat ` ( L' prefix y ) ) ) )" % (LN2, ACCN('y'), TA))], 'mpd',
               "( %s -> ( toNat ` %s ) = ( %s x. ( toNat ` ( L' prefix y ) ) ) )" % (pv, ACCN('y'), TA))
    ez = w.s([cv.mem('y', 'ZZ'), closed(w, pv, '0z', '0 e. ZZ'), cv.mem(LN2, 'ZZ'), w.inst('elfzo')], 'syl3anc',
             '( %s -> ( y e. ( 0 ..^ %s ) <-> ( 0 <_ y /\\ y < %s ) ) )' % (pv, LN2, LN2))
    yfo = w.s([ez, w.s([cv.ge0('y'), ylt], 'jca', '( %s -> ( 0 <_ y /\\ y < %s ) )' % (pv, LN2))], 'mpbird', '( %s -> y e. ( 0 ..^ %s ) )' % (pv, LN2))
    ll2v = Av(ll2p, "L' e. Word 2o")
    pf1 = w.s([ll2v, yfo, w.inst('tm2lpfxs1')], 'syl2anc', "( %s -> ( L' prefix %s ) = ( ( L' prefix y ) ++ <\" ( L' ` y ) \"> ) )" % (pv, Y1))
    lyb = w.s([ll2v, yfo, w.inst('wrdsymbcl')], 'syl2anc', "( %s -> ( L' ` y ) e. 2o )" % pv)
    pfw = w.s([ll2v, w.inst('pfxcl')], 'syl', "( %s -> ( L' prefix y ) e. Word 2o )" % pv)
    tsn = w.s([w.s([pf1], 'fveq2d', "( %s -> ( toNat ` ( L' prefix %s ) ) = ( toNat ` ( ( L' prefix y ) ++ <\" ( L' ` y ) \"> ) ) )" % (pv, Y1)),
               w.s([pfw, lyb, w.inst('tonatsnoc')], 'syl2anc', "( %s -> ( toNat ` ( ( L' prefix y ) ++ <\" ( L' ` y ) \"> ) ) = ( ( toNat ` ( L' prefix y ) ) + ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ ( # ` ( L' prefix y ) ) ) ) ) )" % pv)],
              'eqtrd', "( %s -> ( toNat ` ( L' prefix %s ) ) = ( ( toNat ` ( L' prefix y ) ) + ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ ( # ` ( L' prefix y ) ) ) ) ) )" % (pv, Y1))
    yfz = w.s([yfo, w.inst('elfzofz')], 'syl', '( %s -> y e. ( 0 ... %s ) )' % (pv, LN2))
    pl = w.s([ll2v, yfz, w.inst('pfxlen')], 'syl2anc', "( %s -> ( # ` ( L' prefix y ) ) = y )" % pv)
    PP = "( toNat ` ( L' prefix y ) )"
    tsn2 = w.s([tsn, w.s([w.s([w.s([pl], 'oveq2d', "( %s -> ( 2 ^ ( # ` ( L' prefix y ) ) ) = ( 2 ^ y ) )" % pv)], 'oveq2d',
                             "( %s -> ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ ( # ` ( L' prefix y ) ) ) ) = ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ y ) ) )" % pv)], 'oveq2d',
                         "( %s -> ( %s + ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ ( # ` ( L' prefix y ) ) ) ) ) = ( %s + ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ y ) ) ) )" % (pv, PP, PP))],
               'eqtrd', "( %s -> ( toNat ` ( L' prefix %s ) ) = ( %s + ( ( bToNat ` ( L' ` y ) ) x. ( 2 ^ y ) ) ) )" % (pv, Y1, PP))
    GOALV = "( toNat ` %s ) = ( %s x. ( toNat ` ( L' prefix %s ) ) )" % (ACCN(Y1), TA, Y1)
    tlv = w.s([Av(llp, 'L e. Word 2o'), w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (pv, TA))
    ppv = w.s([pfw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (pv, PP))
    E2 = '( 2 ^ y )'
    e2c = w.s([closed(w, pv, '2cn', '2 e. CC'), yv], 'expcld', '( %s -> %s e. CC )' % (pv, E2))
    tlc = w.s([tlv], 'nn0cnd', '( %s -> %s e. CC )' % (pv, TA))
    ppc = w.s([ppv], 'nn0cnd', '( %s -> %s e. CC )' % (pv, PP))
    # case set
    pva = '( %s /\\ %s )' % (pv, C1)
    V = lambda s_, f: w.s([s_], 'adantr', '( %s -> %s )' % (pva, f))
    c1v = w.s([], 'simpr', '( %s -> %s )' % (pva, C1))
    eav = w.s([V(w.s([st], 'adantr', '( %s -> %s = %s )' % (pv, ACCN(Y1), IFA)), '%s = %s' % (ACCN(Y1), IFA)), w.s([c1v], 'iftrued', '( %s -> %s = %s )' % (pva, IFA, AB))],
              'eqtrd', '( %s -> %s = %s )' % (pva, ACCN(Y1), AB))
    ta1 = w.s([w.s([eav], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (pva, ACCN(Y1), AB)),
               w.s([V(w.s([ih1], 'adantr', '( %s -> %s e. Word 2o )' % (pv, ACCN('y'))), '%s e. Word 2o' % ACCN('y')), V(w.s([shw], 'adantr', '( %s -> %s e. Word 2o )' % (pv, SHF('y'))), '%s e. Word 2o' % SHF('y')),
                    closed(w, pva, '0el2o', '(/) e. 2o'), w.inst('tonataddbits')], 'syl3anc',
                   '( %s -> ( toNat ` %s ) = ( ( ( toNat ` %s ) + ( toNat ` %s ) ) + ( bToNat ` (/) ) ) )' % (pva, AB, ACCN('y'), SHF('y')))], 'eqtrd',
              '( %s -> ( toNat ` %s ) = ( ( ( toNat ` %s ) + ( toNat ` %s ) ) + ( bToNat ` (/) ) ) )' % (pva, ACCN(Y1), ACCN('y'), SHF('y')))
    tshv = w.s([V(w.s([llp], 'adantr', '( %s -> L e. Word 2o )' % pv), 'L e. Word 2o'), V(yv, 'y e. NN0'), w.inst('tonatrep0a')], 'syl2anc',
               '( %s -> ( toNat ` %s ) = ( %s x. %s ) )' % (pva, SHF('y'), E2, TA))
    r1 = w.s([V(ih3v, "( toNat ` %s ) = ( %s x. %s )" % (ACCN('y'), TA, PP)), tshv], 'oveq12d',
             '( %s -> ( ( toNat ` %s ) + ( toNat ` %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (pva, ACCN('y'), SHF('y'), TA, PP, E2, TA))
    r2 = w.s([r1, closed(w, pva, 'bwbn0', '( bToNat ` (/) ) = 0')], 'oveq12d',
             '( %s -> ( ( ( toNat ` %s ) + ( toNat ` %s ) ) + ( bToNat ` (/) ) ) = ( ( ( %s x. %s ) + ( %s x. %s ) ) + 0 ) )' % (pva, ACCN('y'), SHF('y'), TA, PP, E2, TA))
    bn1 = w.s([w.s([c1v], 'fveq2d', "( %s -> ( bToNat ` ( L' ` y ) ) = ( bToNat ` 1o ) )" % pva), closed(w, pva, 'bwbn1', '( bToNat ` 1o ) = 1')], 'eqtrd',
              "( %s -> ( bToNat ` ( L' ` y ) ) = 1 )" % pva)
    rhs1 = w.s([V(tsn2, "( toNat ` ( L' prefix %s ) ) = ( %s + ( ( bToNat ` ( L' ` y ) ) x. %s ) )" % (Y1, PP, E2)),
                w.s([w.s([w.s([bn1], 'oveq1d', "( %s -> ( ( bToNat ` ( L' ` y ) ) x. %s ) = ( 1 x. %s ) )" % (pva, E2, E2)),
                          w.s([V(e2c, '%s e. CC' % E2)], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (pva, E2, E2))], 'eqtrd',
                         "( %s -> ( ( bToNat ` ( L' ` y ) ) x. %s ) = %s )" % (pva, E2, E2))], 'oveq2d',
                    "( %s -> ( %s + ( ( bToNat ` ( L' ` y ) ) x. %s ) ) = ( %s + %s ) )" % (pva, PP, E2, PP, E2))],
               'eqtrd', "( %s -> ( toNat ` ( L' prefix %s ) ) = ( %s + %s ) )" % (pva, Y1, PP, E2))
    rhs2 = w.s([rhs1], 'oveq2d', "( %s -> ( %s x. ( toNat ` ( L' prefix %s ) ) ) = ( %s x. ( %s + %s ) ) )" % (pva, TA, Y1, TA, PP, E2))
    dist = w.s([V(tlc, '%s e. CC' % TA), V(ppc, '%s e. CC' % PP), V(e2c, '%s e. CC' % E2)], 'adddid',
               '( %s -> ( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (pva, TA, PP, E2, TA, PP, TA, E2))
    com = w.s([V(tlc, '%s e. CC' % TA), V(e2c, '%s e. CC' % E2)], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (pva, TA, E2, E2, TA))
    dist2 = w.s([dist, w.s([com], 'oveq2d', '( %s -> ( ( %s x. %s ) + ( %s x. %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (pva, TA, PP, TA, E2, TA, PP, E2, TA))],
                'eqtrd', '( %s -> ( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (pva, TA, PP, E2, TA, PP, E2, TA))
    SUMX = '( ( %s x. %s ) + ( %s x. %s ) )' % (TA, PP, E2, TA)
    sc = w.s([w.s([V(tlc, '%s e. CC' % TA), V(ppc, '%s e. CC' % PP)], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (pva, TA, PP)),
              w.s([V(e2c, '%s e. CC' % E2), V(tlc, '%s e. CC' % TA)], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (pva, E2, TA))], 'addcld', '( %s -> %s e. CC )' % (pva, SUMX))
    az = w.s([sc], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (pva, SUMX, SUMX))
    lhs = w.s([w.s([ta1, r2], 'eqtrd', '( %s -> ( toNat ` %s ) = ( %s + 0 ) )' % (pva, ACCN(Y1), SUMX)), az], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (pva, ACCN(Y1), SUMX))
    rhs = w.s([rhs2, dist2], 'eqtrd', "( %s -> ( %s x. ( toNat ` ( L' prefix %s ) ) ) = %s )" % (pva, TA, Y1, SUMX))
    vca = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (pva, GOALV))
    # case clear
    pvb = '( %s /\\ -. %s )' % (pv, C1)
    Vb = lambda s_, f: w.s([s_], 'adantr', '( %s -> %s )' % (pvb, f))
    nc = w.s([], 'simpr', '( %s -> -. %s )' % (pvb, C1))
    ebv = w.s([Vb(w.s([st], 'adantr', '( %s -> %s = %s )' % (pv, ACCN(Y1), IFA)), '%s = %s' % (ACCN(Y1), IFA)), w.s([nc], 'iffalsed', '( %s -> %s = %s )' % (pvb, IFA, ACCN('y')))],
              'eqtrd', '( %s -> %s = %s )' % (pvb, ACCN(Y1), ACCN('y')))
    lhsb = w.s([w.s([ebv], 'fveq2d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (pvb, ACCN(Y1), ACCN('y'))), Vb(ih3v, "( toNat ` %s ) = ( %s x. %s )" % (ACCN('y'), TA, PP))],
               'eqtrd', '( %s -> ( toNat ` %s ) = ( %s x. %s ) )' % (pvb, ACCN(Y1), TA, PP))
    lz = w.s([nc, w.s([Vb(lyb, "( L' ` y ) e. 2o"), w.inst('bwel2on')], 'syl', "( %s -> ( -. ( L' ` y ) = 1o <-> ( L' ` y ) = (/) ) )" % pvb)], 'mpbid',
             "( %s -> ( L' ` y ) = (/) )" % pvb)
    bn0 = w.s([w.s([lz], 'fveq2d', "( %s -> ( bToNat ` ( L' ` y ) ) = ( bToNat ` (/) ) )" % pvb), closed(w, pvb, 'bwbn0', '( bToNat ` (/) ) = 0')], 'eqtrd',
              "( %s -> ( bToNat ` ( L' ` y ) ) = 0 )" % pvb)
    z1 = w.s([w.s([bn0], 'oveq1d', "( %s -> ( ( bToNat ` ( L' ` y ) ) x. %s ) = ( 0 x. %s ) )" % (pvb, E2, E2)),
              w.s([Vb(e2c, '%s e. CC' % E2)], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (pvb, E2))], 'eqtrd', "( %s -> ( ( bToNat ` ( L' ` y ) ) x. %s ) = 0 )" % (pvb, E2))
    rb1 = w.s([Vb(tsn2, "( toNat ` ( L' prefix %s ) ) = ( %s + ( ( bToNat ` ( L' ` y ) ) x. %s ) )" % (Y1, PP, E2)),
               w.s([z1], 'oveq2d', "( %s -> ( %s + ( ( bToNat ` ( L' ` y ) ) x. %s ) ) = ( %s + 0 ) )" % (pvb, PP, E2, PP))], 'eqtrd',
              "( %s -> ( toNat ` ( L' prefix %s ) ) = ( %s + 0 ) )" % (pvb, Y1, PP))
    rb2 = w.s([rb1, w.s([Vb(ppc, '%s e. CC' % PP)], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (pvb, PP, PP))], 'eqtrd', "( %s -> ( toNat ` ( L' prefix %s ) ) = %s )" % (pvb, Y1, PP))
    rhsb = w.s([rb2], 'oveq2d', "( %s -> ( %s x. ( toNat ` ( L' prefix %s ) ) ) = ( %s x. %s ) )" % (pvb, TA, Y1, TA, PP))
    vcb = w.s([lhsb, rhsb], 'eqtr4d', '( %s -> %s )' % (pvb, GOALV))
    vv = w.s([vca, vcb], 'pm2.61dan', '( %s -> %s )' % (pv, GOALV))
    vimp = w.s([vv], 'ex', '( %s -> ( %s <_ %s -> %s ) )' % (ps, Y1, LN2, GOALV))
    step = w.s([w.s([wy1, leny], 'jca', '( %s -> ( %s e. Word 2o /\\ ( # ` %s ) <_ ( %s + %s ) ) )' % (ps, ACCN(Y1), ACCN(Y1), LN, Y1)), vimp], 'jca',
               '( %s -> %s )' % (ps, P(Y1)))
    w.qed(subs + [base, step], 'nn0indd', ST_ACC)
    return w.run()


if __name__ == '__main__':
    if want('tmcacc0'): tmcacc0()
    if want('tmcaccs'): tmcaccs()
    if want('tmcacc'): tmcacc()
