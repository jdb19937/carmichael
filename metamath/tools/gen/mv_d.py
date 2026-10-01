"""Sortie MV, section D: integrability of the Fejer-type kernels (mvsinabs, mvibl, mvkibl)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from mvlib import *
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def mvsinabs():
    w = W('mvsinabs', '| sin X | <_ | X | for real X.')
    A0 = 'X e. RR'
    xr = w.s([], 'id', '( X e. RR -> X e. RR )')
    Y = '( abs ` X )'
    cl = Closure(w, A0, {'X': ('RR', xr)})
    yr = cl.mem(Y, 'RR')
    y0 = w.s([cl.mem('X', 'CC')], 'absge0d', '( %s -> 0 <_ %s )' % (A0, Y))
    SY = '( sin ` %s )' % Y; SX = '( sin ` X )'
    AY = '( abs ` %s )' % SY; AX = '( abs ` %s )' % SX
    ao = ap(w, A0, 'absor', [xr], '( %s = X \\/ %s = -u X )' % (Y, Y))
    c1a = '( %s /\\ %s = X )' % (A0, Y)
    e1 = w.s([], 'simpr', '( %s -> %s = X )' % (c1a, Y))
    k1 = dst(w, c1a, [dst(w, c1a, [e1], 'fveq2d', '%s = %s' % (SY, SX))], 'fveq2d', '%s = %s' % (AY, AX))
    c2a = '( %s /\\ %s = -u X )' % (A0, Y)
    e2 = w.s([], 'simpr', '( %s -> %s = -u X )' % (c2a, Y))
    xc2 = lift(w, cl.mem('X', 'CC'), c2a)
    s2 = eqt(w, c2a, dst(w, c2a, [e2], 'fveq2d', '%s = ( sin ` -u X )' % SY), ap(w, c2a, 'sinneg', [xc2], '( sin ` -u X ) = -u %s' % SX))
    k2 = eqt(w, c2a, dst(w, c2a, [s2], 'fveq2d', '%s = ( abs ` -u %s )' % (AY, SX)),
             ap(w, c2a, 'absneg', [w.s([xc2], 'sincld', '( %s -> %s e. CC )' % (c2a, SX))], '( abs ` -u %s ) = %s' % (SX, AX)))
    eqa = w.s([k1, k2, ao], 'mpjaodan', '( %s -> %s = %s )' % (A0, AY, AX))
    # | sin Y | <_ Y
    lt = w.s([yr, a1(w, A0, '1re', '1 e. RR')], 'letrid', '( %s -> ( %s <_ 1 \\/ 1 <_ %s ) )' % (A0, Y, Y))
    ca = '( %s /\\ %s <_ 1 )' % (A0, Y)
    yra = lift(w, yr, ca); y0a = lift(w, y0, ca); y1a = w.s([], 'simpr', '( %s -> %s <_ 1 )' % (ca, Y))
    cla = Closure(w, ca, {Y: [('RR', yra), ('ge0', y0a)], '_pi': ('RR+', a1(w, ca, 'pirp', '_pi e. RR+'))})
    pir = cla.mem('_pi', 'RR')
    p3 = a1(w, ca, 'pigt3', '3 < _pi')
    ypi = linarith(w, ca, [y1a, p3], '%s <_ _pi' % Y, closure=cla)
    bi = w.s([a1(w, ca, '0re', '0 e. RR'), pir, w.inst('elicc2')], 'syl2anc',
             '( %s -> ( %s e. ( 0 [,] _pi ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ _pi ) ) )' % (ca, Y, Y, Y, Y))
    ym = w.s([w.s([yra, y0a, ypi], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ _pi ) )' % (ca, Y, Y, Y)), bi], 'mpbird', '( %s -> %s e. ( 0 [,] _pi ) )' % (ca, Y))
    s0 = ap(w, ca, 'sinq12ge0', [ym], '0 <_ %s' % SY)
    sre = cla.mem(SY, 'RR')
    ai = w.s([sre, s0], 'absidd', '( %s -> %s = %s )' % (ca, AY, SY))
    lo = w.s([a1(w, ca, '0re', '0 e. RR'), yra], 'leloed', '( %s -> ( 0 <_ %s <-> ( 0 < %s \\/ 0 = %s ) ) )' % (ca, Y, Y, Y))
    lo2 = w.s([y0a, lo], 'mpbid', '( %s -> ( 0 < %s \\/ 0 = %s ) )' % (ca, Y, Y))
    cb = '( %s /\\ 0 < %s )' % (ca, Y)
    yp = w.s([lift(w, yra, cb), w.s([], 'simpr', '( %s -> 0 < %s )' % (cb, Y))], 'elrpd', '( %s -> %s e. RR+ )' % (cb, Y))
    sl = ap(w, cb, 'sinltx', [yp], '%s < %s' % (SY, Y))
    clb = Closure(w, cb, {Y: ('RR', lift(w, yra, cb))})
    sle1 = ltle(w, cb, clb, sl)
    cc_ = '( %s /\\ 0 = %s )' % (ca, Y)
    e0 = w.s([], 'simpr', '( %s -> 0 = %s )' % (cc_, Y))
    z1 = eqt(w, cc_, dst(w, cc_, [eqc(w, cc_, e0)], 'fveq2d', '%s = ( sin ` 0 )' % SY), a1(w, cc_, 'sin0', '( sin ` 0 ) = 0'))
    sle2 = w.s([eqt(w, cc_, z1, e0), w.s([lift(w, yra, cc_)], 'leidd', '( %s -> %s <_ %s )' % (cc_, Y, Y))], 'eqbrtrd', '( %s -> %s <_ %s )' % (cc_, SY, Y))
    sle = w.s([sle1, sle2, lo2], 'mpjaodan', '( %s -> %s <_ %s )' % (ca, SY, Y))
    fa = w.s([ai, sle], 'eqbrtrd', '( %s -> %s <_ %s )' % (ca, AY, Y))
    cd = '( %s /\\ 1 <_ %s )' % (A0, Y)
    yrd = lift(w, yr, cd)
    fb = w.s([w.s([w.s([w.s([lift(w, yr, cd)], 'resincld', '( %s -> %s e. RR )' % (cd, SY))], 'recnd', '( %s -> %s e. CC )' % (cd, SY))], 'abscld', '( %s -> %s e. RR )' % (cd, AY)),
              a1(w, cd, '1re', '1 e. RR'), yrd, w.s([ap(w, cd, 'sinbnd', [yrd], '( -u 1 <_ %s /\\ %s <_ 1 )' % (SY, SY)), w.s([w.s([yrd], 'resincld', '( %s -> %s e. RR )' % (cd, SY)), a1(w, cd, '1re', '1 e. RR')], 'absled', '( %s -> ( %s <_ 1 <-> ( -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (cd, AY, SY, SY))], 'mpbird', '( %s -> %s <_ 1 )' % (cd, AY)), w.s([], 'simpr', '( %s -> 1 <_ %s )' % (cd, Y))],
             'letrd', '( %s -> %s <_ %s )' % (cd, AY, Y))
    fy = w.s([fa, fb, lt], 'mpjaodan', '( %s -> %s <_ %s )' % (A0, AY, Y))
    w.s([eqa, fy], 'eqbrtrrd', '( %s -> %s <_ %s )' % (A0, AX, Y))
    qedlast(w)
    go(w)



def mvibl():
    w = W('mvibl', 'A continuous function on an open bounded interval that is bounded there is integrable (bddibl with cnmbf).')
    I = '( A (,) B )'
    A0 = '( ( A e. RR /\\ B e. RR ) /\\ ( F e. ( %s -cn-> CC ) /\\ Z e. RR /\\ A. y e. %s ( abs ` ( F ` y ) ) <_ Z ) )' % (I, I)
    P = parts(w, A0)
    ar, br, fc, zr, bd = P['A e. RR'], P['B e. RR'], P['F e. ( %s -cn-> CC )' % I], P['Z e. RR'], P['A. y e. %s ( abs ` ( F ` y ) ) <_ Z' % I]
    ioo = a1(w, A0, 'ioombl', '%s e. dom vol' % I)
    mb = w.s([ioo, fc, w.inst('cnmbf')], 'syl2anc', '( %s -> F e. MblFn )' % A0)
    ff = ap(w, A0, 'cncff', [fc], 'F : %s --> CC' % I)
    dm = ap(w, A0, 'fdm', [ff], 'dom F = %s' % I)
    vr = w.s([dst(w, A0, [dm], 'fveq2d', '( vol ` dom F ) = ( vol ` %s )' % I), w.s([ar, br, w.inst('ioovolcl')], 'syl2anc', '( %s -> ( vol ` %s ) e. RR )' % (A0, I))],
             'eqeltrd', '( %s -> ( vol ` dom F ) e. RR )' % A0)
    PHI = '( abs ` ( F ` y ) ) <_ Z'
    rq = w.s([dm], 'raleqdv', '( %s -> ( A. y e. dom F %s <-> A. y e. %s %s ) )' % (A0, PHI, I, PHI))
    bd2 = w.s([bd, rq], 'mpbird', '( %s -> A. y e. dom F %s )' % (A0, PHI))
    ante = 'x = Z'
    idst = w.s([], 'id', '( x = Z -> x = Z )')
    cst, new = w.wcongr('A. y e. dom F ( abs ` ( F ` y ) ) <_ x', {'x': 'Z'}, ante, {'x': idst})
    ex = w.s([zr, bd2, w.s([cst], 'rspcev', '( ( Z e. RR /\\ A. y e. dom F %s ) -> E. x e. RR A. y e. dom F ( abs ` ( F ` y ) ) <_ x )' % PHI)],
             'syl2anc', '( %s -> E. x e. RR A. y e. dom F ( abs ` ( F ` y ) ) <_ x )' % A0)
    w.s([mb, vr, ex, w.inst('bddibl')], 'syl3anc', '( %s -> F e. L^1 )' % A0)
    qedlast(w)
    go(w)


def mvkibl():
    w = W('mvkibl', 'The kernels sin ^ 2 ( A t ) cos ( H t ) / t ^ 2 and sin ^ 2 ( A t ) / t ^ 2 are integrable on ( U , V ) for 0 <_ U (bounded by A ^ 2, continuous: mvibl).')
    A0 = '( ( A e. RR /\\ H e. RR ) /\\ ( U e. RR /\\ V e. RR /\\ 0 <_ U ) )'
    P = parts(w, A0)
    ar, hr, ur, vr, u0 = P['A e. RR'], P['H e. RR'], P['U e. RR'], P['V e. RR'], P['0 <_ U']
    I = IOO('U', 'V')
    cl = Closure(w, A0, {'A': ('RR', ar), 'H': ('RR', hr), 'U': ('RR', ur), 'V': ('RR', vr)})
    domss = w.s([a1(w, A0, 'ioossre', '%s C_ RR' % I), a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, I))

    def pos(v):
        Av = '( %s /\\ %s e. %s )' % (A0, v, I)
        m = w.s([], 'simpr', '( %s -> %s e. %s )' % (Av, v, I))
        vr_ = ap(w, Av, 'elioore', [m], '%s e. RR' % v)
        oo = ap(w, Av, 'eliooord', [m], '( U < %s /\\ %s < V )' % (v, v))
        v0 = w.s([a1(w, Av, '0re', '0 e. RR') if False else w.s([], '0red', '( %s -> 0 e. RR )' % Av), lift(w, ur, Av), vr_, lift(w, u0, Av),
                  dst(w, Av, [oo], 'simpld', 'U < %s' % v)], 'lelttrd', '( %s -> 0 < %s )' % (Av, v))
        sq = '( %s ^ 2 )' % v
        sqp = w.s([vr_, w.s([v0], 'gt0ne0d', '( %s -> %s =/= 0 )' % (Av, v))], 'sqgt0d', '( %s -> 0 < %s )' % (Av, sq))
        sqr = w.s([vr_], 'resqcld', '( %s -> %s e. RR )' % (Av, sq))
        c = Closure(w, Av, {'A': ('RR', lift(w, ar, Av)), 'H': ('RR', lift(w, hr, Av)), v: [('RR', vr_), ('gt0', v0)],
                            sq: [('RR', sqr), ('gt0', sqp), ('ne0', w.s([sqp], 'gt0ne0d', '( %s -> %s =/= 0 )' % (Av, sq)))]})
        return Av, m, vr_, v0, c

    def one(E, Es, withcos):
        Av, m, vr_, v0, c = pos('t')
        cn = CN(w, A0, 't', I, domss, cl, c)
        F = '( t e. %s |-> %s )' % (I, E)
        fcn = cn(E)
        As, ms, sr, s0, cs = pos('s')
        fv = fvmd(w, As, 't', I, E, 's', ms, cs.mem(Es, 'CC'))
        KSs = KS('A', 's'); S2 = '( s ^ 2 )'
        ks0 = w.s([cs.mem('( sin ` ( A x. s ) )', 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (As, KSs))
        # KS <_ ( A ^ 2 ) x. ( s ^ 2 )
        asr = cs.mem('( A x. s )', 'RR')
        sa = ap(w, As, 'mvsinabs', [asr], '( abs ` ( sin ` ( A x. s ) ) ) <_ ( abs ` ( A x. s ) )')
        sq1 = w.s([J(w, As, cs.mem('( abs ` ( sin ` ( A x. s ) ) )', 'RR'), w.s([cs.mem('( sin ` ( A x. s ) )', 'CC')], 'absge0d', '( %s -> 0 <_ ( abs ` ( sin ` ( A x. s ) ) ) )' % As)),
                   J(w, As, cs.mem('( abs ` ( A x. s ) )', 'RR'), sa), w.inst('le2sq2')], 'syl2anc',
                  '( %s -> ( ( abs ` ( sin ` ( A x. s ) ) ) ^ 2 ) <_ ( ( abs ` ( A x. s ) ) ^ 2 ) )' % As)
        r1 = ap(w, As, 'absresq', [cs.mem('( sin ` ( A x. s ) )', 'RR')], '( ( abs ` ( sin ` ( A x. s ) ) ) ^ 2 ) = %s' % KSs)
        r2 = ap(w, As, 'absresq', [asr], '( ( abs ` ( A x. s ) ) ^ 2 ) = ( ( A x. s ) ^ 2 )')
        r3 = w.s([cs.mem('A', 'CC'), cs.mem('s', 'CC')], 'sqmuld', '( %s -> ( ( A x. s ) ^ 2 ) = ( ( A ^ 2 ) x. %s ) )' % (As, S2))
        kle = w.s([w.s([r1, sq1], 'eqbrtrrd', '( %s -> %s <_ ( ( abs ` ( A x. s ) ) ^ 2 ) )' % (As, KSs)), eqt(w, As, r2, r3)], 'breqtrd',
                  '( %s -> %s <_ ( ( A ^ 2 ) x. %s ) )' % (As, KSs, S2))
        mc = w.s([cs.mem('( A ^ 2 )', 'CC'), cs.mem(S2, 'CC')], 'mulcomd', '( %s -> ( ( A ^ 2 ) x. %s ) = ( %s x. ( A ^ 2 ) ) )' % (As, S2, S2))
        kle2 = w.s([kle, mc], 'breqtrd', '( %s -> %s <_ ( %s x. ( A ^ 2 ) ) )' % (As, KSs, S2))
        if withcos:
            C = '( cos ` ( H x. s ) )'; AC = '( abs ` %s )' % C
            num = '( %s x. %s )' % (KSs, C)
            hs = cs.mem('( H x. s )', 'RR')
            cb = w.s([ap(w, As, 'cosbnd', [hs], '( -u 1 <_ %s /\\ %s <_ 1 )' % (C, C)),
                      w.s([cs.mem(C, 'RR'), a1(w, As, '1re', '1 e. RR')], 'absled', '( %s -> ( %s <_ 1 <-> ( -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (As, AC, C, C))],
                     'mpbird', '( %s -> %s <_ 1 )' % (As, AC))
            am = w.s([cs.mem(KSs, 'CC'), cs.mem(C, 'CC')], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. %s ) )' % (As, num, KSs, AC))
            ai = w.s([cs.mem(KSs, 'RR'), ks0], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (As, KSs, KSs))
            am2 = eqt(w, As, am, dst(w, As, [ai], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (KSs, AC, KSs, AC)))
            X = '( %s x. %s )' % (KSs, AC)
            x1 = w.s([cs.mem(AC, 'RR'), a1(w, As, '1re', '1 e. RR'), cs.mem(KSs, 'RR'), ks0, cb], 'lemul2ad', '( %s -> %s <_ ( %s x. 1 ) )' % (As, X, KSs))
            x2 = w.s([x1, w.s([cs.mem(KSs, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (As, KSs, KSs))], 'breqtrd', '( %s -> %s <_ %s )' % (As, X, KSs))
            xle = w.s([cs.mem(X, 'RR'), cs.mem(KSs, 'RR'), cs.mem('( %s x. ( A ^ 2 ) )' % S2, 'RR'), x2, kle2], 'letrd',
                      '( %s -> %s <_ ( %s x. ( A ^ 2 ) ) )' % (As, X, S2))
        else:
            num = KSs; X = KSs; xle = kle2
            am2 = w.s([cs.mem(KSs, 'RR'), ks0], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (As, KSs, KSs))
        ad = w.s([cs.mem(num, 'CC'), cs.mem(S2, 'CC'), cs.ne0(S2)], 'absdivd', '( %s -> ( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) ) )' % (As, num, S2, num, S2))
        as2 = w.s([cs.mem(S2, 'RR'), w.s([cs.mem('s', 'RR')], 'sqge0d', '( %s -> 0 <_ %s )' % (As, S2))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (As, S2, S2))
        ad2 = eqt(w, As, ad, dst(w, As, [am2, as2], 'oveq12d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( %s / %s )' % (num, S2, X, S2)))
        s2rp = w.s([cs.mem(S2, 'RR'), cs.gt0(S2)], 'elrpd', '( %s -> %s e. RR+ )' % (As, S2))
        dv = w.s([cs.mem(X, 'RR'), cs.mem('( A ^ 2 )', 'RR'), s2rp], 'ledivmuld', '( %s -> ( ( %s / %s ) <_ ( A ^ 2 ) <-> %s <_ ( %s x. ( A ^ 2 ) ) ) )' % (As, X, S2, X, S2))
        q = w.s([xle, dv], 'mpbird', '( %s -> ( %s / %s ) <_ ( A ^ 2 ) )' % (As, X, S2))
        b1 = w.s([ad2, q], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( A ^ 2 ) )' % (As, Es))
        b2 = w.s([dst(w, As, [fv], 'fveq2d', '( abs ` ( %s ` s ) ) = ( abs ` %s )' % (F, Es)), b1], 'eqbrtrd', '( %s -> ( abs ` ( %s ` s ) ) <_ ( A ^ 2 ) )' % (As, F))
        ra = w.s([b2], 'ralrimiva', '( %s -> A. s e. %s ( abs ` ( %s ` s ) ) <_ ( A ^ 2 ) )' % (A0, I, F))
        return ap(w, A0, 'mvibl', [J(w, A0, J(w, A0, ur, vr), J(w, A0, fcn, cl.mem('( A ^ 2 )', 'RR'), ra))], '%s e. L^1' % F)
    k1 = one(KC('A', 'H'), KC('A', 'H', 's'), True)
    k2 = one(KQ('A'), KQ('A', 's'), False)
    J(w, A0, k1, k2)
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvsinabs()
    mvibl()
    mvkibl()
