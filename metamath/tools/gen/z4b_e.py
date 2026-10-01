"""Sortie Z4b, section E: the window sieve (LargeSieve window_sieve, steps 2-5):
the Farey family as a finite point set, its spacing and range, the regrouping
of the per-modulus Farey sums, and the assembly with lsfiber and lspts."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z4blib import *
from z4alib import crfin, crz, crcop, win, dchyp, EV, DB, PC, WSUM
from lin import linarith, nlinarith
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def rabmem(w, ante, mem, v, dom, body_, a):
    """( ante -> ( a e. dom /\\ body[v:=a] ) ) from mem: ( ante -> a e. { v e. dom | body } )"""
    eq = '%s = %s' % (v, a)
    s1, nb = w.wcongr(body_, {v: a}, eq, {v: w.s([], 'id', '( %s -> %s )' % (eq, eq))})
    er = w.s([s1], 'elrab', '( %s e. { %s e. %s | %s } <-> ( %s e. %s /\\ %s ) )' % (a, v, dom, body_, a, dom, nb))
    return w.s([mem, er], 'sylib', '( %s -> ( %s e. %s /\\ %s ) )' % (ante, a, dom, nb)), nb


def memparts(w, ante, pmem, p):
    """from pmem: ( ante -> p e. FP ): steps p = <. 1st , 2nd >., 1st p e. NN, 1st p <_ Q0, 2nd p e. CR(1st p)"""
    m = ap(w, ante, 'lswinmem', [pmem], '( %s = <. ( 1st ` %s ) , ( 2nd ` %s ) >. /\\ ( 1st ` %s ) e. %s /\\ ( 2nd ` %s ) e. %s )' % (
        p, p, p, p, Q0S, p, CR('( 1st ` %s )' % p)))
    e = st(w, ante, [m], 'simp1d', '%s = <. ( 1st ` %s ) , ( 2nd ` %s ) >.' % (p, p, p))
    q = st(w, ante, [m], 'simp2d', '( 1st ` %s ) e. %s' % (p, Q0S))
    v = st(w, ante, [m], 'simp3d', '( 2nd ` %s ) e. %s' % (p, CR('( 1st ` %s )' % p)))
    qn = ap(w, ante, 'elfznn', [q], '( 1st ` %s ) e. NN' % p)
    ql = ap(w, ante, 'elfzle2', [q], '( 1st ` %s ) <_ %s' % (p, Q0))
    return e, qn, ql, v


if __name__ == '__main__':
    # ---- lswinmem
    A0 = 'p e. %s' % FP
    w = W('lswinmem', 'An element of the Farey family U_ q ( { q } X. CR(q) ) is the pair of its denominator q <_ |_ Q and a numerator coprime to q.')
    Ain = '( p = <. q , u >. /\\ ( q e. %s /\\ u e. %s ) )' % (Q0S, CR('q'))
    e1 = w.s([], 'simpl', '( %s -> p = <. q , u >. )' % Ain)
    vq = w.s([], 'vex', 'q e. _V'); vu = w.s([], 'vex', 'u e. _V')
    f1 = w.s([e1, w.s([vq, vu], 'op1std', '( p = <. q , u >. -> ( 1st ` p ) = q )')], 'syl', '( %s -> ( 1st ` p ) = q )' % Ain)
    f2 = w.s([e1, w.s([vq, vu], 'op2ndd', '( p = <. q , u >. -> ( 2nd ` p ) = u )')], 'syl', '( %s -> ( 2nd ` p ) = u )' % Ain)
    eq = st(w, Ain, [f1, f2], 'opeq12d', '<. ( 1st ` p ) , ( 2nd ` p ) >. = <. q , u >.')
    c1 = st(w, Ain, [e1, eq], 'eqtr4d', 'p = <. ( 1st ` p ) , ( 2nd ` p ) >.')
    qm = w.s([], 'simprl', '( %s -> q e. %s )' % (Ain, Q0S)); um = w.s([], 'simprr', '( %s -> u e. %s )' % (Ain, CR('q')))
    c2 = st(w, Ain, [f1, qm], 'eqeltrd', '( 1st ` p ) e. %s' % Q0S)
    crq, _ = w.congr(CR('q'), {'q': '( 1st ` p )'}, Ain, {'q': eqc(w, Ain, f1)})
    c3 = st(w, Ain, [f2, st(w, Ain, [um, crq], 'eleqtrd', 'u e. %s' % CR('( 1st ` p )'))], 'eqeltrd', '( 2nd ` p ) e. %s' % CR('( 1st ` p )'))
    C = concl('lswinmem')
    cj = st(w, Ain, [c1, c2, c3], '3jca', C)
    ex = w.s([cj], 'exlimivv', '( E. q E. u %s -> %s )' % (Ain, C))
    el = w.s([], 'eliunxp', '( p e. %s <-> E. q E. u %s )' % (FP, Ain))
    w.qed([el, ex], 'sylbi', STATEMENTS['lswinmem']); go(w)

    # ---- lsblkre
    A0 = '( f e. NN /\\ %s )' % HW
    w = W('lsblkre', 'The primitive-character block of a window sum is a nonnegative real (LargeSieve window_sieve, hBlock0).')
    fnn = w.s([], 'simpl', '( %s -> f e. NN )' % A0); hw = w.s([], 'simpr', '( %s -> %s )' % (A0, HW))
    Ax = '( %s /\\ x e. %s )' % (A0, PC('f'))
    xm = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, PC('f')))
    xs, _ = rabmem(w, Ax, xm, 'y', DB('f'), '( f DChrCond y ) = f', 'x')
    xd = st(w, Ax, [xs], 'simpld', 'x e. %s' % DB('f'))
    Axn = '( %s /\\ n e. W )' % Ax
    nz, an = win(w, Axn, lift(w, hw, Axn), w.s([], 'simpr', '( %s -> n e. W )' % Axn))
    g, z, d, l = dchyp(w, 'f')
    xn = w.s([g, z, d, l, lift(w, xd, Axn), nz], 'dchrzrhcl', '( %s -> %s e. CC )' % (Axn, EV('x', 'f', 'n')))
    ws = st(w, Ax, [lift(w, st(w, A0, [hw], 'simp1d', 'W e. Fin'), Ax), st(w, Axn, [an, xn], 'mulcld', '( ( A ` n ) x. %s ) e. CC' % EV('x', 'f', 'n'))], 'fsumcl', '%s e. CC' % WSUM('x', 'f'))
    ab = st(w, Ax, [ws], 'abscld', '( abs ` %s ) e. RR' % WSUM('x', 'f'))
    pf = w.s([fnn, w.inst('dchrprimsfi')], 'syl', '( %s -> %s e. Fin )' % (A0, PC('f')))
    br = st(w, A0, [pf, st(w, Ax, [ab], 'resqcld', '%s e. RR' % ABS2(WSUM('x', 'f')))], 'fsumrecl', '%s e. RR' % BLK('f'))
    b0 = st(w, A0, [pf, st(w, Ax, [ab], 'resqcld', '%s e. RR' % ABS2(WSUM('x', 'f'))), st(w, Ax, [ab], 'sqge0d', '0 <_ %s' % ABS2(WSUM('x', 'f')))], 'fsumge0', '0 <_ %s' % BLK('f'))
    w.qed([br, b0], 'jca', STATEMENTS['lsblkre']); go(w)

    # ---- lswinlem1: the Farey family is a finite point family, D = 1 / Q ^ 2 > 0
    A0 = '( Q e. RR /\\ 2 <_ Q )'
    w = W('lswinlem1', 'The Farey family of denominators up to |_ Q is finite, its points v / q are real, and 1 / Q ^ 2 > 0 (LargeSieve window_sieve, step 4).')
    qr = w.s([], 'simpl', '( %s -> Q e. RR )' % A0); q2 = w.s([], 'simpr', '( %s -> 2 <_ Q )' % A0)
    c = ctx(w, A0, {'Q': ('RR', qr)})
    qp = qpos(w, A0, qr, q2)
    c.leaf('Q', 'RR+', st(w, A0, [qr, qp], 'elrpd', 'Q e. RR+'))
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, Q0S))
    Aq = '( %s /\\ q e. %s )' % (A0, Q0S)
    xf = ap(w, Aq, 'xpfi', [a1(w, Aq, 'snfi', '{ q } e. Fin'), crfin(w, Aq, 'q')], '( { q } X. %s ) e. Fin' % CR('q'))
    ral = st(w, A0, [xf], 'ralrimiva', 'A. q e. %s ( { q } X. %s ) e. Fin' % (Q0S, CR('q')))
    fpf = ap(w, A0, 'iunfi', [fz, ral], '%s e. Fin' % FP)
    Ap = '( %s /\\ p e. %s )' % (A0, FP)
    pe, qn, ql, vm = memparts(w, Ap, w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, FP)), 'p')
    vz = crz(w, Ap, vm, '( 2nd ` p )', '( 1st ` p )')
    yr = st(w, Ap, [st(w, Ap, [vz], 'zred', '( 2nd ` p ) e. RR'), st(w, Ap, [qn], 'nnred', '( 1st ` p ) e. RR'), st(w, Ap, [qn], 'nnne0d', '( 1st ` p ) =/= 0')], 'redivcld',
            '( ( 2nd ` p ) / ( 1st ` p ) ) e. RR')
    yf = st(w, A0, [yr], 'fmptd', '%s : %s --> RR' % (YF, FP))
    w.qed([fpf, yf, c.mem(DQ2, 'RR+')], '3jca', STATEMENTS['lswinlem1']); go(w)


def yval(w, ante, pmem, qn, vz, p):
    """( ante -> ( YF ` p ) = ( ( 2nd ` p ) / ( 1st ` p ) ) )"""
    yr = st(w, ante, [st(w, ante, [vz], 'zred', '( 2nd ` %s ) e. RR' % p), st(w, ante, [qn], 'nnred', '( 1st ` %s ) e. RR' % p),
                      st(w, ante, [qn], 'nnne0d', '( 1st ` %s ) =/= 0' % p)], 'redivcld', '( ( 2nd ` %s ) / ( 1st ` %s ) ) e. RR' % (p, p))
    return fvmd(w, ante, 'p', FP, '( ( 2nd ` p ) / ( 1st ` p ) )', p, pmem, st(w, ante, [yr], 'recnd', '( ( 2nd ` %s ) / ( 1st ` %s ) ) e. CC' % (p, p))), yr


if __name__ == '__main__':
    # ---- lswinlem2: the Farey points are 1 / Q ^ 2 separated
    A0 = '( Q e. RR /\\ 2 <_ Q )'
    w = W('lswinlem2', 'Distinct points of the Farey family of denominators up to |_ Q are 1 / Q ^ 2 apart (LargeSieve window_sieve, step 5 separation, from farey_sep_abs).')
    Ab = '( ( %s /\\ ( a e. %s /\\ b e. %s ) ) /\\ a =/= b )' % (A0, FP, FP)
    L = lambda s_: lift(w, s_, Ab)
    qr = L(w.s([], 'simpl', '( %s -> Q e. RR )' % A0)); q2 = L(w.s([], 'simpr', '( %s -> 2 <_ Q )' % A0))
    am = w.s([], 'simplrl', '( %s -> a e. %s )' % (Ab, FP)); bm = w.s([], 'simplrr', '( %s -> b e. %s )' % (Ab, FP))
    ae, aq, aql, av = memparts(w, Ab, am, 'a'); be, bq, bql, bv = memparts(w, Ab, bm, 'b')
    avz = crz(w, Ab, av, '( 2nd ` a )', '( 1st ` a )'); bvz = crz(w, Ab, bv, '( 2nd ` b )', '( 1st ` b )')
    def nn0(vm, p):
        return ap(w, Ab, 'elfzonn0', [ap(w, Ab, 'elrabi', [vm], '( 2nd ` %s ) e. ( 0 ..^ ( 1st ` %s ) )' % (p, p))], '( 2nd ` %s ) e. NN0' % p)
    av0 = nn0(av, 'a'); bv0 = nn0(bv, 'b')
    ag = crcop(w, Ab, av, '( 2nd ` a )', '( 1st ` a )'); bg = crcop(w, Ab, bv, '( 2nd ` b )', '( 1st ` b )')
    # the pairs differ
    NE = '( ( 1st ` a ) = ( 1st ` b ) /\\ ( 2nd ` a ) = ( 2nd ` b ) )'
    Ae = '( %s /\\ %s )' % (Ab, NE)
    op = w.s([w.s([], 'simpr', '( %s -> %s )' % (Ae, NE)), w.inst('opeq12')], 'syl',
             '( %s -> <. ( 1st ` a ) , ( 2nd ` a ) >. = <. ( 1st ` b ) , ( 2nd ` b ) >. )' % Ae)
    abq = eqt(w, Ae, eqt(w, Ae, lift(w, ae, Ae), op), eqc(w, Ae, lift(w, be, Ae)))
    imp = w.s([abq], 'ex', '( %s -> ( %s -> a = b ) )' % (Ab, NE))
    nab = st(w, Ab, [w.s([], 'simpr', '( %s -> a =/= b )' % Ab)], 'neneqd', '-. a = b')
    nne = st(w, Ab, [nab, imp], 'mtod', '-. %s' % NE)
    FS = '( 1 / ( ( 1st ` a ) x. ( 1st ` b ) ) ) <_ ( abs ` ( ( ( 2nd ` a ) / ( 1st ` a ) ) - ( ( 2nd ` b ) / ( 1st ` b ) ) ) )'
    fs = ap(w, Ab, 'fareysep', [J(w, Ab, J(w, Ab, J(w, Ab, aq, bq), J(w, Ab, av0, bv0)), J(w, Ab, ag, bg), nne)], FS)
    ya, yar = yval(w, Ab, am, aq, avz, 'a'); yb, ybr = yval(w, Ab, bm, bq, bvz, 'b')
    yd = st(w, Ab, [st(w, Ab, [ya, yb], 'oveq12d', '( ( %s ` a ) - ( %s ` b ) ) = ( ( ( 2nd ` a ) / ( 1st ` a ) ) - ( ( 2nd ` b ) / ( 1st ` b ) ) )' % (YF, YF))], 'fveq2d',
            '( abs ` ( ( %s ` a ) - ( %s ` b ) ) ) = ( abs ` ( ( ( 2nd ` a ) / ( 1st ` a ) ) - ( ( 2nd ` b ) / ( 1st ` b ) ) ) )' % (YF, YF))
    fs2 = st(w, Ab, [fs, yd], 'breqtrrd', '( 1 / ( ( 1st ` a ) x. ( 1st ` b ) ) ) <_ ( abs ` ( ( %s ` a ) - ( %s ` b ) ) )' % (YF, YF))
    # 1 / Q ^ 2 <_ 1 / ( q q' )
    fl = ap(w, Ab, 'flle', [qr], '%s <_ Q' % Q0)
    c = ctx(w, Ab, {'Q': ('RR', qr), '( 1st ` a )': ('NN', aq), '( 1st ` b )': ('NN', bq)})
    c.leaf(Q0, 'RR', c.mem(Q0, 'RR') if False else st(w, Ab, [ap(w, Ab, 'flcl', [qr], '%s e. ZZ' % Q0)], 'zred', '%s e. RR' % Q0))
    qa = st(w, Ab, [c.mem('( 1st ` a )', 'RR'), c.mem(Q0, 'RR'), qr, aql, fl], 'letrd', '( 1st ` a ) <_ Q')
    qb = st(w, Ab, [c.mem('( 1st ` b )', 'RR'), c.mem(Q0, 'RR'), qr, bql, fl], 'letrd', '( 1st ` b ) <_ Q')
    qp = qpos(w, Ab, qr, q2)
    a0 = c.ge0('( 1st ` a )'); b0 = c.ge0('( 1st ` b )')
    pr0 = st(w, Ab, [c.mem('( 1st ` a )', 'RR'), qr, c.mem('( 1st ` b )', 'RR'), qr, a0, b0, qa, qb], 'lemul12ad', '( ( 1st ` a ) x. ( 1st ` b ) ) <_ ( Q x. Q )')
    pr = st(w, Ab, [pr0, st(w, Ab, [st(w, Ab, [qr], 'recnd', 'Q e. CC')], 'sqvald', '( Q ^ 2 ) = ( Q x. Q )')], 'breqtrrd', '( ( 1st ` a ) x. ( 1st ` b ) ) <_ ( Q ^ 2 )')
    c.leaf('Q', 'RR+', st(w, Ab, [qr, qp], 'elrpd', 'Q e. RR+'))
    lr = st(w, Ab, [J(w, Ab, J(w, Ab, c.mem('( ( 1st ` a ) x. ( 1st ` b ) )', 'RR'), c.gt0('( ( 1st ` a ) x. ( 1st ` b ) )')), J(w, Ab, c.mem('( Q ^ 2 )', 'RR'), c.gt0('( Q ^ 2 )'))),
                    w.inst('lerec')], 'syl',
            '( ( ( 1st ` a ) x. ( 1st ` b ) ) <_ ( Q ^ 2 ) <-> %s <_ ( 1 / ( ( 1st ` a ) x. ( 1st ` b ) ) ) )' % DQ2)
    rc = st(w, Ab, [pr, lr], 'mpbid', '%s <_ ( 1 / ( ( 1st ` a ) x. ( 1st ` b ) ) )' % DQ2)
    yaR = st(w, Ab, [ya, yar], 'eqeltrd', '( %s ` a ) e. RR' % YF); ybR = st(w, Ab, [yb, ybr], 'eqeltrd', '( %s ` b ) e. RR' % YF)
    ydr = st(w, Ab, [yaR, ybR], 'resubcld', '( ( %s ` a ) - ( %s ` b ) ) e. RR' % (YF, YF))
    c.leaf('( abs ` ( ( %s ` a ) - ( %s ` b ) ) )' % (YF, YF), 'RR', st(w, Ab, [st(w, Ab, [ydr], 'recnd', '( ( %s ` a ) - ( %s ` b ) ) e. CC' % (YF, YF))], 'abscld', '( abs ` ( ( %s ` a ) - ( %s ` b ) ) ) e. RR' % (YF, YF)))
    fin = st(w, Ab, [c.mem(DQ2, 'RR'), c.mem('( 1 / ( ( 1st ` a ) x. ( 1st ` b ) ) )', 'RR'), c.mem('( abs ` ( ( %s ` a ) - ( %s ` b ) ) )' % (YF, YF), 'RR'), rc, fs2], 'letrd',
             '%s <_ ( abs ` ( ( %s ` a ) - ( %s ` b ) ) )' % (DQ2, YF, YF))
    Aab = '( %s /\\ ( a e. %s /\\ b e. %s ) )' % (A0, FP, FP)
    ex = w.s([fin], 'ex', '( %s -> ( a =/= b -> %s <_ ( abs ` ( ( %s ` a ) - ( %s ` b ) ) ) ) )' % (Aab, DQ2, YF, YF))
    w.qed([ex], 'ralrimivva', STATEMENTS['lswinlem2']); go(w)

    # ---- lswinlem3: the Farey points lie in [ 0 , 1 - 1 / Q ^ 2 ]
    A0 = '( Q e. RR /\\ 2 <_ Q )'
    w = W('lswinlem3', 'The points of the Farey family of denominators up to |_ Q lie in [ 0 , 1 - 1 / Q ^ 2 ] (LargeSieve window_sieve, step 5 range).')
    Aa = '( %s /\\ a e. %s )' % (A0, FP)
    L = lambda s_: lift(w, s_, Aa)
    qr = L(w.s([], 'simpl', '( %s -> Q e. RR )' % A0)); q2 = L(w.s([], 'simpr', '( %s -> 2 <_ Q )' % A0))
    am = w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, FP))
    ae, aq, aql, av = memparts(w, Aa, am, 'a')
    avz = crz(w, Aa, av, '( 2nd ` a )', '( 1st ` a )')
    afz = ap(w, Aa, 'elrabi', [av], '( 2nd ` a ) e. ( 0 ..^ ( 1st ` a ) )')
    v0 = ap(w, Aa, 'elfzole1', [afz], '0 <_ ( 2nd ` a )')
    vlt = ap(w, Aa, 'elfzolt2', [afz], '( 2nd ` a ) < ( 1st ` a )')
    vle = st(w, Aa, [vlt, ap(w, Aa, 'zltlem1', [avz, st(w, Aa, [aq], 'nnzd', '( 1st ` a ) e. ZZ')], '( ( 2nd ` a ) < ( 1st ` a ) <-> ( 2nd ` a ) <_ ( ( 1st ` a ) - 1 ) )')], 'mpbid',
             '( 2nd ` a ) <_ ( ( 1st ` a ) - 1 )')
    ya, yar = yval(w, Aa, am, aq, avz, 'a')
    V = '( 2nd ` a )'; Qa = '( 1st ` a )'
    c = ctx(w, Aa, {'Q': ('RR', qr), Qa: ('NN', aq), V: ('ZZ', avz)})
    qarp = c.mem(Qa, 'RR+')
    y0 = st(w, Aa, [c.mem(V, 'RR'), qarp, v0], 'divge0d', '0 <_ ( %s / %s )' % (V, Qa))
    d1 = st(w, Aa, [c.mem(V, 'RR'), c.mem('( %s - 1 )' % Qa, 'RR'), qarp, vle], 'lediv1dd', '( %s / %s ) <_ ( ( %s - 1 ) / %s )' % (V, Qa, Qa, Qa))
    d2 = eqt(w, Aa, st(w, Aa, [c.mem(Qa, 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % Aa), c.mem(Qa, 'CC'), c.ne0(Qa)], 'divsubdird',
                       '( ( %s - 1 ) / %s ) = ( ( %s / %s ) - ( 1 / %s ) )' % (Qa, Qa, Qa, Qa, Qa)),
             st(w, Aa, [ap(w, Aa, 'divid', [c.mem(Qa, 'CC'), c.ne0(Qa)], '( %s / %s ) = 1' % (Qa, Qa))], 'oveq1d', '( ( %s / %s ) - ( 1 / %s ) ) = ( 1 - ( 1 / %s ) )' % (Qa, Qa, Qa, Qa)))
    fl = ap(w, Aa, 'flle', [qr], '%s <_ Q' % Q0)
    c.leaf(Q0, 'RR', st(w, Aa, [ap(w, Aa, 'flcl', [qr], '%s e. ZZ' % Q0)], 'zred', '%s e. RR' % Q0))
    qa = st(w, Aa, [c.mem(Qa, 'RR'), c.mem(Q0, 'RR'), qr, aql, fl], 'letrd', '%s <_ Q' % Qa)
    qp = qpos(w, Aa, qr, q2)
    q1 = st(w, Aa, [w.s([], '1red', '( %s -> 1 e. RR )' % Aa), a1(w, Aa, '2re', '2 e. RR'), qr, a1(w, Aa, '1le2', '1 <_ 2'), q2], 'letrd', '1 <_ Q')
    qqq = ap(w, Aa, 'lemulge11', [J(w, Aa, J(w, Aa, qr, qr), J(w, Aa, st(w, Aa, [qr, qp], 'ltled', '0 <_ Q'), q1))], 'Q <_ ( Q x. Q )')
    qq2 = st(w, Aa, [qqq, st(w, Aa, [st(w, Aa, [qr], 'recnd', 'Q e. CC')], 'sqvald', '( Q ^ 2 ) = ( Q x. Q )')], 'breqtrrd', 'Q <_ ( Q ^ 2 )')
    qsq = st(w, Aa, [c.mem(Qa, 'RR'), qr, st(w, Aa, [qr], 'resqcld', '( Q ^ 2 ) e. RR'), qa, qq2], 'letrd', '%s <_ ( Q ^ 2 )' % Qa)
    c.leaf('Q', 'RR+', st(w, Aa, [qr, qp], 'elrpd', 'Q e. RR+'))
    lr = w.s([J(w, Aa, J(w, Aa, c.mem(Qa, 'RR'), c.gt0(Qa)), J(w, Aa, c.mem('( Q ^ 2 )', 'RR'), c.gt0('( Q ^ 2 )'))), w.inst('lerec')], 'syl',
             '( %s -> ( %s <_ ( Q ^ 2 ) <-> %s <_ ( 1 / %s ) ) )' % (Aa, Qa, DQ2, Qa))
    rc = st(w, Aa, [qsq, lr], 'mpbid', '%s <_ ( 1 / %s )' % (DQ2, Qa))
    YA = '( %s ` a )' % YF
    c.leaf(YF.join(['( ', ' ` a )']), 'RR', st(w, Aa, [ya, yar], 'eqeltrd', '( %s ` a ) e. RR' % YF))
    u1 = st(w, Aa, [d1, d2], 'breqtrd', '( %s / %s ) <_ ( 1 - ( 1 / %s ) )' % (V, Qa, Qa))
    u2 = st(w, Aa, [c.mem(DQ2, 'RR'), c.mem('( 1 / %s )' % Qa, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % Aa), rc], 'lesub2dd', '( 1 - ( 1 / %s ) ) <_ ( 1 - %s )' % (Qa, DQ2))
    u3 = st(w, Aa, [c.mem('( %s / %s )' % (V, Qa), 'RR'), c.mem('( 1 - ( 1 / %s ) )' % Qa, 'RR'), c.mem('( 1 - %s )' % DQ2, 'RR'), u1, u2], 'letrd', '( %s / %s ) <_ ( 1 - %s )' % (V, Qa, DQ2))
    up = st(w, Aa, [ya, u3], 'eqbrtrd', '%s <_ ( 1 - %s )' % (YA, DQ2))
    lo = st(w, Aa, [y0, ya], 'breqtrrd', '0 <_ %s' % YA)
    w.qed([J(w, Aa, lo, up)], 'ralrimiva', STATEMENTS['lswinlem3']); go(w)


def trigeq(w, ante, eqst, a, b):
    """( ante -> X(a) = X(b) ) for X(y) = | TRIG(A,y) | ^ 2, from eqst: ( ante -> a = b )"""
    An = '( %s /\\ n e. W )' % ante
    e = lift(w, eqst, An)
    e1 = st(w, An, [e], 'oveq2d', '( ( n - M ) x. %s ) = ( ( n - M ) x. %s )' % (a, b))
    e2 = st(w, An, [e1], 'oveq2d', '( %s x. ( ( n - M ) x. %s ) ) = ( %s x. ( ( n - M ) x. %s ) )' % (C2, a, C2, b))
    e3 = st(w, An, [e2], 'fveq2d', '%s = %s' % (EAT('( n - M )', a), EAT('( n - M )', b)))
    e4 = st(w, An, [e3], 'oveq2d', '( ( A ` n ) x. %s ) = ( ( A ` n ) x. %s )' % (EAT('( n - M )', a), EAT('( n - M )', b)))
    s = st(w, ante, [e4], 'sumeq2dv', '%s = %s' % (TRIG('A', a), TRIG('A', b)))
    return st(w, ante, [st(w, ante, [s], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (TRIG('A', a), TRIG('A', b)))], 'oveq1d', '%s = %s' % (ABS2(TRIG('A', a)), ABS2(TRIG('A', b))))


def xcl(w, ante, hwst, mzst, yst, y):
    """( ante -> X(y) e. RR ) from yst: ( ante -> y e. RR ), hwst: HW, mzst: M e. ZZ"""
    An = '( %s /\\ n e. W )' % ante
    nz, an = win(w, An, lift(w, hwst, An), w.s([], 'simpr', '( %s -> n e. W )' % An))
    nmc = st(w, An, [st(w, An, [nz, lift(w, mzst, An)], 'zsubcld', '( n - M ) e. ZZ')], 'zcnd', '( n - M ) e. CC')
    ec = ap(w, An, 'eatcl', [nmc, st(w, An, [lift(w, yst, An)], 'recnd', '%s e. CC' % y)], '%s e. CC' % EAT('( n - M )', y))
    tc = st(w, ante, [st(w, ante, [hwst], 'simp1d', 'W e. Fin'), st(w, An, [an, ec], 'mulcld', '( ( A ` n ) x. %s ) e. CC' % EAT('( n - M )', y))], 'fsumcl', '%s e. CC' % TRIG('A', y))
    return st(w, ante, [st(w, ante, [tc], 'abscld', '( abs ` %s ) e. RR' % TRIG('A', y))], 'resqcld', '%s e. RR' % ABS2(TRIG('A', y)))


if __name__ == '__main__':
    # ---- lswinlem4: the regrouping of the Farey sums as one sum over the Farey family
    A0 = '( Q e. RR /\\ %s )' % HWM
    w = W('lswinlem4', 'The per-denominator Farey sums regroup as one sum over the Farey family (LargeSieve window_sieve, hstep4).')
    P = parts(w, A0)
    hw, mz = P[HW], P['M e. ZZ']
    X = lambda y: ABS2(TRIG('A', y))
    Ai = 'i = <. q , u >.'
    vq = w.s([], 'vex', 'q e. _V'); vu = w.s([], 'vex', 'u e. _V')
    f1 = w.s([vq, vu], 'op1std', '( %s -> ( 1st ` i ) = q )' % Ai); f2 = w.s([vq, vu], 'op2ndd', '( %s -> ( 2nd ` i ) = u )' % Ai)
    fq = st(w, Ai, [f2, f1], 'oveq12d', '( ( 2nd ` i ) / ( 1st ` i ) ) = ( u / q )')
    h1 = trigeq(w, Ai, fq, '( ( 2nd ` i ) / ( 1st ` i ) )', '( u / q )')
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, Q0S))
    Aq = '( %s /\\ q e. %s )' % (A0, Q0S)
    crf = crfin(w, Aq, 'q')
    Aqu = '( %s /\\ ( q e. %s /\\ u e. %s ) )' % (A0, Q0S, CR('q'))
    qn = ap(w, Aqu, 'elfznn', [w.s([], 'simprl', '( %s -> q e. %s )' % (Aqu, Q0S))], 'q e. NN')
    uz = crz(w, Aqu, w.s([], 'simprr', '( %s -> u e. %s )' % (Aqu, CR('q'))), 'u', 'q')
    uq = st(w, Aqu, [st(w, Aqu, [uz], 'zred', 'u e. RR'), st(w, Aqu, [qn], 'nnred', 'q e. RR'), st(w, Aqu, [qn], 'nnne0d', 'q =/= 0')], 'redivcld', '( u / q ) e. RR')
    cc = st(w, Aqu, [xcl(w, Aqu, lift(w, hw, Aqu), lift(w, mz, Aqu), uq, '( u / q )')], 'recnd', '%s e. CC' % X('( u / q )'))
    f2d = st(w, A0, [h1, fz, crf, cc], 'fsum2d',
             'sum_ q e. %s sum_ u e. %s %s = sum_ i e. %s %s' % (Q0S, CR('q'), X('( u / q )'), FP, X('( ( 2nd ` i ) / ( 1st ` i ) )')))
    Ai2 = '( %s /\\ i e. %s )' % (A0, FP)
    im = w.s([], 'simpr', '( %s -> i e. %s )' % (Ai2, FP))
    ie, iq, iql, iv = memparts(w, Ai2, im, 'i')
    ivz = crz(w, Ai2, iv, '( 2nd ` i )', '( 1st ` i )')
    yi, yir = yval(w, Ai2, im, iq, ivz, 'i')
    t2 = trigeq(w, Ai2, eqc(w, Ai2, yi), '( ( 2nd ` i ) / ( 1st ` i ) )', '( %s ` i )' % YF)
    s2 = st(w, A0, [t2], 'sumeq2dv', 'sum_ i e. %s %s = sum_ i e. %s %s' % (FP, X('( ( 2nd ` i ) / ( 1st ` i ) )'), FP, X('( %s ` i )' % YF)))
    fin = eqt(w, A0, f2d, s2); qedlast(w); go(w)

    # ---- lswin: the window sieve from the per-modulus bound (steps 2-5)
    A0 = HWIN
    w = W('lswin', 'Window sieve (LargeSieve window_sieve, steps 2-5): for coefficients on integers coprime to every modulus up to Q, with frequencies within E of M, the sum over q <_ Q of the per-modulus primitive-character blocks weighted f / phi ( q ) is at most ( Q ^ 2 + 4 pi E ) times the mass.')
    P = parts(w, A0)
    qr, q2, hwm, hw, mz, erp, copq, frq = P['Q e. RR'], P['2 <_ Q'], P[HWM], P[HW], P['M e. ZZ'], P['E e. RR+'], P[COPQ], P[FRQ]
    Aq = '( %s /\\ q e. %s )' % (A0, Q0S)
    L = lambda s_: lift(w, s_, Aq)
    qm = w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, Q0S))
    qn = ap(w, Aq, 'elfznn', [qm], 'q e. NN')
    sb, _ = w.wcongr('A. m e. W ( m gcd s ) = 1', {'s': 'q'}, 's = q', {'s': w.s([], 'id', '( s = q -> s = q )')})
    cop = st(w, Aq, [sb, L(copq), qm], 'rspcdva', COPALL('q'))
    ESQ = lambda Qv: 'sum_ u e. %s %s' % (CR(Qv), ABS2(TRIG('A', '( u / %s )' % Qv)))
    LHS = lambda Qv: 'sum_ f e. %s ( ( f / ( phi ` %s ) ) x. %s )' % (DIV(Qv), Qv, BLK('f'))
    lf = ap(w, Aq, 'lsfiber', [J(w, Aq, J(w, Aq, qn, st(w, Aq, [L(mz)], 'zred', 'M e. RR')), L(hw), cop)], '%s <_ %s' % (LHS('q'), ESQ('q')))
    # closures of the two sides at q
    DVq = '{ d e. NN | d || q }'
    dvf = ap(w, Aq, 'dvdsfi', [qn], '%s e. Fin' % DVq)
    DIVB = '( d || q /\\ ( ( mmu ` ( q / d ) ) =/= 0 /\\ ( ( q / d ) gcd d ) = 1 ) )'
    ssr = w.s([w.s([w.s([], 'simpl', '( %s -> d || q )' % DIVB)], 'a1i', '( d e. NN -> ( %s -> d || q ) )' % DIVB)], 'ss2rabi', '%s C_ %s' % (DIV('q'), DVq))
    divf = st(w, Aq, [dvf, w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (Aq, DIV('q'), DVq))], 'ssfid', '%s e. Fin' % DIV('q'))
    Aqf = '( %s /\\ f e. %s )' % (Aq, DIV('q'))
    fnn = ap(w, Aqf, 'elrabi', [w.s([], 'simpr', '( %s -> f e. %s )' % (Aqf, DIV('q')))], 'f e. NN')
    blk = ap(w, Aqf, 'lsblkre', [J(w, Aqf, fnn, lift(w, hw, Aqf))], '( %s e. RR /\\ 0 <_ %s )' % (BLK('f'), BLK('f')))
    blkr = st(w, Aqf, [blk], 'simpld', '%s e. RR' % BLK('f'))
    ph_ = ap(w, Aqf, 'phicl', [lift(w, qn, Aqf)], '( phi ` q ) e. NN')
    fr = st(w, Aqf, [st(w, Aqf, [fnn], 'nnred', 'f e. RR'), st(w, Aqf, [ph_], 'nnred', '( phi ` q ) e. RR'), st(w, Aqf, [ph_], 'nnne0d', '( phi ` q ) =/= 0')], 'redivcld', '( f / ( phi ` q ) ) e. RR')
    lr = st(w, Aq, [divf, st(w, Aqf, [fr, blkr], 'remulcld', '( ( f / ( phi ` q ) ) x. %s ) e. RR' % BLK('f'))], 'fsumrecl', '%s e. RR' % LHS('q'))
    Aqu = '( %s /\\ u e. %s )' % (Aq, CR('q'))
    uz = crz(w, Aqu, w.s([], 'simpr', '( %s -> u e. %s )' % (Aqu, CR('q'))), 'u', 'q')
    qnu = lift(w, qn, Aqu)
    uq = st(w, Aqu, [st(w, Aqu, [uz], 'zred', 'u e. RR'), st(w, Aqu, [qnu], 'nnred', 'q e. RR'), st(w, Aqu, [qnu], 'nnne0d', 'q =/= 0')], 'redivcld', '( u / q ) e. RR')
    rr_ = st(w, Aq, [crfin(w, Aq, 'q'), xcl(w, Aqu, lift(w, hw, Aqu), lift(w, mz, Aqu), uq, '( u / q )')], 'fsumrecl', '%s e. RR' % ESQ('q'))
    fz = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, Q0S))
    s1 = st(w, A0, [fz, lr, rr_, lf], 'fsumle', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (Q0S, LHS('q'), Q0S, ESQ('q')))
    qq = J(w, A0, qr, q2)
    s2 = ap(w, A0, 'lswinlem4', [J(w, A0, qr, hwm)], concl('lswinlem4'))
    pts = ap(w, A0, 'lswinlem1', [qq], concl('lswinlem1'))
    sep = ap(w, A0, 'lswinlem2', [qq], concl('lswinlem2'))
    rng = ap(w, A0, 'lswinlem3', [qq], concl('lswinlem3'))
    SWA = SW('A')
    lp = ap(w, A0, 'lspts', [J(w, A0, hwm, pts, J(w, A0, sep, rng, J(w, A0, erp, frq)))],
            'sum_ i e. %s %s <_ ( ( ( 1 / %s ) + %s ) x. %s )' % (FP, ABS2(TRIG('A', '( %s ` i )' % YF)), DQ2, WR(), SWA))
    c = ctx(w, A0, {'Q': ('RR', qr)})
    qp = qpos(w, A0, qr, q2)
    c.leaf('Q', 'RR+', st(w, A0, [qr, qp], 'elrpd', 'Q e. RR+'))
    rec = st(w, A0, [c.mem('( Q ^ 2 )', 'CC'), c.ne0('( Q ^ 2 )')], 'recrecd', '( 1 / %s ) = ( Q ^ 2 )' % DQ2)
    r2 = st(w, A0, [st(w, A0, [rec], 'oveq1d', '( ( 1 / %s ) + %s ) = ( ( Q ^ 2 ) + %s )' % (DQ2, WR(), WR()))], 'oveq1d',
            '( ( ( 1 / %s ) + %s ) x. %s ) = ( ( ( Q ^ 2 ) + %s ) x. %s )' % (DQ2, WR(), SWA, WR(), SWA))
    lp2 = st(w, A0, [lp, r2], 'breqtrd', 'sum_ i e. %s %s <_ ( ( ( Q ^ 2 ) + %s ) x. %s )' % (FP, ABS2(TRIG('A', '( %s ` i )' % YF)), WR(), SWA))
    sLr = st(w, A0, [fz, lr], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (Q0S, LHS('q')))
    sRr = st(w, A0, [fz, rr_], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (Q0S, ESQ('q')))
    Anw = '( %s /\\ n e. W )' % A0
    _, anw = win(w, Anw, lift(w, hw, Anw), w.s([], 'simpr', '( %s -> n e. W )' % Anw))
    swr = st(w, A0, [st(w, A0, [hw], 'simp1d', 'W e. Fin'), st(w, Anw, [st(w, Anw, [anw], 'abscld', '( abs ` ( A ` n ) ) e. RR')], 'resqcld', '%s e. RR' % ABS2('( A ` n )'))], 'fsumrecl', '%s e. RR' % SWA)
    c.leaf(SWA, 'RR', swr); c.leaf('E', 'RR+', erp)
    cr_ = c.mem('( ( ( Q ^ 2 ) + %s ) x. %s )' % (WR(), SWA), 'RR')
    fin = st(w, A0, [sLr, sRr, cr_, s1, st(w, A0, [s2, lp2], 'eqbrtrd', 'sum_ q e. %s %s <_ ( ( ( Q ^ 2 ) + %s ) x. %s )' % (Q0S, ESQ('q'), WR(), SWA))], 'letrd',
             concl('lswin'))
    qedlast(w); go(w)


def inrab(w, ante, v, dom, body_, a, domst, bodyst):
    """( ante -> a e. { v e. dom | body } ) from domst: ( ante -> a e. dom ), bodyst: ( ante -> body[v:=a] )"""
    eq = '%s = %s' % (v, a)
    s1, nb = w.wcongr(body_, {v: a}, eq, {v: w.s([], 'id', '( %s -> %s )' % (eq, eq))})
    er = w.s([s1], 'elrab', '( %s e. { %s e. %s | %s } <-> ( %s e. %s /\\ %s ) )' % (a, v, dom, body_, a, dom, nb))
    return w.s([J(w, ante, domst, bodyst), er], 'sylibr', '( %s -> %s e. { %s e. %s | %s } )' % (ante, a, v, dom, body_))


RFB = lambda e, f='f', N='N': '( ( %s x. %s ) <_ %s /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd %s ) = 1 ) )' % (e, f, N, e, e, f)
DIVB = lambda g, d='d': '( %s || %s /\\ ( ( mmu ` ( %s / %s ) ) =/= 0 /\\ ( ( %s / %s ) gcd %s ) = 1 ) )' % (d, g, g, d, g, d, d)


if __name__ == '__main__':
    # ---- lswinreglem1: r |-> r f is a bijection from Lean's r-range onto the moduli q with f e. DIV(q)
    A0 = '( N e. NN0 /\\ f e. ( 1 ... N ) )'
    w = W('lswinreglem1', 'Lemma for lswinreg: r |-> r f maps the squarefree cofactors r coprime to f with r f <_ N bijectively onto the moduli q <_ N having f as a DIV-divisor.')
    n0 = w.s([], 'simpl', '( %s -> N e. NN0 )' % A0); fm = w.s([], 'simpr', '( %s -> f e. ( 1 ... N ) )' % A0)
    nz = st(w, A0, [n0], 'nn0zd', 'N e. ZZ'); fnn = ap(w, A0, 'elfznn', [fm], 'f e. NN')
    RFN = RF('N'); TGN = TG('N'); MP = '( l e. %s |-> ( l x. f ) )' % RFN
    fz = lambda ante, x: ap(w, ante, 'fznn', [lift(w, nz, ante)], '( %s e. ( 1 ... N ) <-> ( %s e. NN /\\ %s <_ N ) )' % (x, x, x))
    # closures
    Al = '( %s /\\ l e. %s )' % (A0, RFN)
    lnn_ = ap(w, Al, 'elfznn', [ap(w, Al, 'elrabi', [w.s([], 'simpr', '( %s -> l e. %s )' % (Al, RFN))], 'l e. ( 1 ... N )')], 'l e. NN')
    h2 = st(w, Al, [st(w, Al, [lnn_], 'nncnd', 'l e. CC'), st(w, Al, [lift(w, fnn, Al)], 'nncnd', 'f e. CC')], 'mulcld', '( l x. f ) e. CC')
    Av = '( %s /\\ v e. %s )' % (A0, TGN)
    vnn_ = ap(w, Av, 'elfznn', [ap(w, Av, 'elrabi', [w.s([], 'simpr', '( %s -> v e. %s )' % (Av, TGN))], 'v e. ( 1 ... N )')], 'v e. NN')
    h3 = st(w, Av, [st(w, Av, [vnn_], 'nncnd', 'v e. CC'), st(w, Av, [lift(w, fnn, Av)], 'nncnd', 'f e. CC'), st(w, Av, [lift(w, fnn, Av)], 'nnne0d', 'f =/= 0')], 'divcld', '( v / f ) e. CC')
    # forward
    Af = '( %s /\\ ( l e. %s /\\ v = ( l x. f ) ) )' % (A0, RFN)
    L = lambda s_: lift(w, s_, Af)
    lm, _ = rabmem(w, Af, w.s([], 'simprl', '( %s -> l e. %s )' % (Af, RFN)), 'r', '( 1 ... N )', RFB('r'), 'l')
    l1n = st(w, Af, [lm], 'simpld', 'l e. ( 1 ... N )'); lrest = st(w, Af, [lm], 'simprd', RFB('l'))
    lfle = st(w, Af, [lrest], 'simpld', '( l x. f ) <_ N'); lmu = st(w, Af, [st(w, Af, [lrest], 'simprd', '( ( mmu ` l ) =/= 0 /\\ ( l gcd f ) = 1 )')], 'simpld', '( mmu ` l ) =/= 0')
    lg = st(w, Af, [st(w, Af, [lrest], 'simprd', '( ( mmu ` l ) =/= 0 /\\ ( l gcd f ) = 1 )')], 'simprd', '( l gcd f ) = 1')
    lnn = ap(w, Af, 'elfznn', [l1n], 'l e. NN'); veq = w.s([], 'simprr', '( %s -> v = ( l x. f ) )' % Af)
    fnf = L(fnn)
    vnn = st(w, Af, [veq, st(w, Af, [lnn, fnf], 'nnmulcld', '( l x. f ) e. NN')], 'eqeltrd', 'v e. NN')
    vle = st(w, Af, [veq, lfle], 'eqbrtrd', 'v <_ N')
    v1n = st(w, Af, [J(w, Af, vnn, vle), fz(Af, 'v')], 'mpbird', 'v e. ( 1 ... N )')
    lc = st(w, Af, [lnn], 'nncnd', 'l e. CC'); fc = st(w, Af, [fnf], 'nncnd', 'f e. CC'); fne = st(w, Af, [fnf], 'nnne0d', 'f =/= 0')
    vf = eqt(w, Af, st(w, Af, [veq], 'oveq1d', '( v / f ) = ( ( l x. f ) / f )'), st(w, Af, [lc, fc, fne], 'divcan4d', '( ( l x. f ) / f ) = l'))
    fdv = st(w, Af, [ap(w, Af, 'dvdsmul2', [st(w, Af, [lnn], 'nnzd', 'l e. ZZ'), st(w, Af, [fnf], 'nnzd', 'f e. ZZ')], 'f || ( l x. f )'), veq], 'breqtrrd', 'f || v')
    mu = st(w, Af, [st(w, Af, [vf], 'fveq2d', '( mmu ` ( v / f ) ) = ( mmu ` l )'), lmu], 'eqnetrd', '( mmu ` ( v / f ) ) =/= 0')
    gc = eqt(w, Af, st(w, Af, [vf], 'oveq1d', '( ( v / f ) gcd f ) = ( l gcd f )'), lg)
    fdiv = inrab(w, Af, 'd', 'NN', DIVB('v'), 'f', fnf, J(w, Af, fdv, J(w, Af, mu, gc)))
    vtg = inrab(w, Af, 'g', '( 1 ... N )', 'f e. %s' % DIV('g'), 'v', v1n, fdiv)
    fwd = w.s([J(w, Af, vtg, eqc(w, Af, vf))], 'ex', '( %s -> ( ( l e. %s /\\ v = ( l x. f ) ) -> ( v e. %s /\\ l = ( v / f ) ) ) )' % (A0, RFN, TGN))
    # backward
    Ab = '( %s /\\ ( v e. %s /\\ l = ( v / f ) ) )' % (A0, TGN)
    L = lambda s_: lift(w, s_, Ab)
    vm, _ = rabmem(w, Ab, w.s([], 'simprl', '( %s -> v e. %s )' % (Ab, TGN)), 'g', '( 1 ... N )', 'f e. %s' % DIV('g'), 'v')
    v1n = st(w, Ab, [vm], 'simpld', 'v e. ( 1 ... N )'); fdv_ = st(w, Ab, [vm], 'simprd', 'f e. %s' % DIV('v'))
    vv = st(w, Ab, [v1n, fz(Ab, 'v')], 'mpbid', '( v e. NN /\\ v <_ N )')
    vnn = st(w, Ab, [vv], 'simpld', 'v e. NN'); vle = st(w, Ab, [vv], 'simprd', 'v <_ N')
    fd, _ = rabmem(w, Ab, fdv_, 'd', 'NN', DIVB('v'), 'f')
    frest = st(w, Ab, [fd], 'simprd', DIVB('v', 'f'))
    fdvd = st(w, Ab, [frest], 'simpld', 'f || v')
    fmu = st(w, Ab, [st(w, Ab, [frest], 'simprd', '( ( mmu ` ( v / f ) ) =/= 0 /\\ ( ( v / f ) gcd f ) = 1 )')], 'simpld', '( mmu ` ( v / f ) ) =/= 0')
    fg = st(w, Ab, [st(w, Ab, [frest], 'simprd', '( ( mmu ` ( v / f ) ) =/= 0 /\\ ( ( v / f ) gcd f ) = 1 )')], 'simprd', '( ( v / f ) gcd f ) = 1')
    fnf = L(fnn); leq = w.s([], 'simprr', '( %s -> l = ( v / f ) )' % Ab)
    vfn = st(w, Ab, [fdvd, ap(w, Ab, 'nndivdvds', [vnn, fnf], '( f || v <-> ( v / f ) e. NN )')], 'mpbid', '( v / f ) e. NN')
    lnn = st(w, Ab, [leq, vfn], 'eqeltrd', 'l e. NN')
    fc = st(w, Ab, [fnf], 'nncnd', 'f e. CC'); fne = st(w, Ab, [fnf], 'nnne0d', 'f =/= 0'); vc = st(w, Ab, [vnn], 'nncnd', 'v e. CC')
    lf = eqt(w, Ab, st(w, Ab, [leq], 'oveq1d', '( l x. f ) = ( ( v / f ) x. f )'), st(w, Ab, [vc, fc, fne], 'divcan1d', '( ( v / f ) x. f ) = v'))
    lfle = st(w, Ab, [lf, vle], 'eqbrtrd', '( l x. f ) <_ N')
    lr = st(w, Ab, [lnn], 'nnred', 'l e. RR'); fr = st(w, Ab, [fnf], 'nnred', 'f e. RR')
    lle1 = ap(w, Ab, 'lemulge11', [J(w, Ab, J(w, Ab, lr, fr), J(w, Ab, st(w, Ab, [lnn], 'nnnn0d', 'l e. NN0') and st(w, Ab, [lr, st(w, Ab, [lnn], 'nngt0d', '0 < l')], 'ltled', '0 <_ l'), ap(w, Ab, 'nnge1', [fnf], '1 <_ f')))], 'l <_ ( l x. f )')
    lle = st(w, Ab, [lr, st(w, Ab, [lr, fr], 'remulcld', '( l x. f ) e. RR'), st(w, Ab, [L(nz)], 'zred', 'N e. RR'), lle1, lfle], 'letrd', 'l <_ N')
    l1n = st(w, Ab, [J(w, Ab, lnn, lle), fz(Ab, 'l')], 'mpbird', 'l e. ( 1 ... N )')
    lmu = st(w, Ab, [st(w, Ab, [leq], 'fveq2d', '( mmu ` l ) = ( mmu ` ( v / f ) )'), fmu], 'eqnetrd', '( mmu ` l ) =/= 0')
    lg = eqt(w, Ab, st(w, Ab, [leq], 'oveq1d', '( l gcd f ) = ( ( v / f ) gcd f )'), fg)
    lrf = inrab(w, Ab, 'r', '( 1 ... N )', RFB('r'), 'l', l1n, J(w, Ab, lfle, J(w, Ab, lmu, lg)))
    bwd = w.s([J(w, Ab, lrf, eqc(w, Ab, lf))], 'ex', '( %s -> ( ( v e. %s /\\ l = ( v / f ) ) -> ( l e. %s /\\ v = ( l x. f ) ) ) )' % (A0, TGN, RFN))
    bi = st(w, A0, [fwd, bwd], 'impbid', '( ( l e. %s /\\ v = ( l x. f ) ) <-> ( v e. %s /\\ l = ( v / f ) ) )' % (RFN, TGN))
    w.qed([w.s([], 'eqid', '%s = %s' % (MP, MP)), h2, h3, bi], 'f1od', STATEMENTS['lswinreglem1']); go(w)

    # ---- lswinreg: Lean's hregroup + hfiber in divisor form
    w = W('lswinreg', 'Regrouping the pair sum of window_sieve by the modulus q = r f: summing over conductors f <_ N and squarefree cofactors r coprime to f with r f <_ N equals summing over q <_ N and the divisors f e. DIV(q) (LargeSieve window_sieve, hregroup and hfiber).')
    hyps_of(w, 'lswinreg')
    A0 = 'ph'
    N1 = '( 1 ... N )'; RFN = RF('N'); TGN = TG('N')
    Hq = lambda q, f='f': '( ( %s / ( phi ` %s ) ) x. B )' % (f, q)
    IF_ = 'if ( f e. %s , %s , 0 )' % (DIV('q'), Hq('q'))
    nz = st(w, A0, ['n'], 'nn0zd', 'N e. ZZ')
    fzf = w.s([], 'fzfid', '( ph -> %s e. Fin )' % N1)
    def hcl(ante, qnn, fnn):
        """( ante -> H(q,f) e. CC )"""
        ph_ = ap(w, ante, 'phicl', [qnn], '( phi ` q ) e. NN')
        bc = w.s([J(w, ante, lift(w, w.s([], 'id', '( ph -> ph )'), ante) if ante != 'ph' else None, fnn), 'b'], 'syl', '( %s -> B e. CC )' % ante)
        return st(w, ante, [st(w, ante, [st(w, ante, [fnn], 'nncnd', 'f e. CC'), st(w, ante, [ph_], 'nncnd', '( phi ` q ) e. CC'), st(w, ante, [ph_], 'nnne0d', '( phi ` q ) =/= 0')], 'divcld',
                                        '( f / ( phi ` q ) ) e. CC'), bc], 'mulcld', '%s e. CC' % Hq('q'))
    # (a) at each q: sum over DIV(q) as a sum over ( 1 ... N )
    Aq = '( ph /\\ q e. %s )' % N1
    qnn = ap(w, Aq, 'elfznn', [w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, N1))], 'q e. NN')
    qle = ap(w, Aq, 'elfzle2', [w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, N1))], 'q <_ N')
    Aqf = '( %s /\\ f e. %s )' % (Aq, DIV('q'))
    fd, _ = rabmem(w, Aqf, w.s([], 'simpr', '( %s -> f e. %s )' % (Aqf, DIV('q'))), 'd', 'NN', DIVB('q'), 'f')
    fnn = st(w, Aqf, [fd], 'simpld', 'f e. NN'); fdq = st(w, Aqf, [st(w, Aqf, [fd], 'simprd', DIVB('q', 'f'))], 'simpld', 'f || q')
    fle = st(w, Aqf, [fdq, ap(w, Aqf, 'dvdsle', [st(w, Aqf, [fnn], 'nnzd', 'f e. ZZ'), lift(w, qnn, Aqf)], '( f || q -> f <_ q )')], 'mpd', 'f <_ q')
    fleN = st(w, Aqf, [st(w, Aqf, [fnn], 'nnred', 'f e. RR'), st(w, Aqf, [lift(w, qnn, Aqf)], 'nnred', 'q e. RR'), st(w, Aqf, [lift(w, nz, Aqf)], 'zred', 'N e. RR'), fle, lift(w, qle, Aqf)], 'letrd', 'f <_ N')
    fN = st(w, Aqf, [J(w, Aqf, fnn, fleN), ap(w, Aqf, 'fznn', [lift(w, nz, Aqf)], '( f e. %s <-> ( f e. NN /\\ f <_ N ) )' % N1)], 'mpbird', 'f e. %s' % N1)
    dss = st(w, Aq, [w.s([fN], 'ex', '( %s -> ( f e. %s -> f e. %s ) )' % (Aq, DIV('q'), N1))], 'ssrdv', '%s C_ %s' % (DIV('q'), N1))
    Aqf2 = Aqf
    hc_qf = st(w, Aqf, [st(w, Aqf, [st(w, Aqf, [fnn], 'nncnd', 'f e. CC'), st(w, Aqf, [ap(w, Aqf, 'phicl', [lift(w, qnn, Aqf)], '( phi ` q ) e. NN')], 'nncnd', '( phi ` q ) e. CC'),
                                     st(w, Aqf, [ap(w, Aqf, 'phicl', [lift(w, qnn, Aqf)], '( phi ` q ) e. NN')], 'nnne0d', '( phi ` q ) =/= 0')], 'divcld', '( f / ( phi ` q ) ) e. CC'),
                       w.s([J(w, Aqf, w.s([], 'simpll', '( %s -> ph )' % Aqf), fnn), 'b'], 'syl', '( %s -> B e. CC )' % Aqf)], 'mulcld', '%s e. CC' % Hq('q'))
    ral = st(w, Aq, [hc_qf], 'ralrimiva', 'A. f e. %s %s e. CC' % (DIV('q'), Hq('q')))
    olc = st(w, Aq, [lift(w, fzf, Aq)], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (N1, N1))
    ssa = ap(w, Aq, 'sumss2', [J(w, Aq, J(w, Aq, dss, ral), olc)], 'sum_ f e. %s %s = sum_ f e. %s %s' % (DIV('q'), Hq('q'), N1, IF_))
    sa = st(w, A0, [ssa], 'sumeq2dv', 'sum_ q e. %s sum_ f e. %s %s = sum_ q e. %s sum_ f e. %s %s' % (N1, DIV('q'), Hq('q'), N1, N1, IF_))
    # (b) swap
    Aqf3 = '( ph /\\ ( q e. %s /\\ f e. %s ) )' % (N1, N1)
    qn3 = ap(w, Aqf3, 'elfznn', [w.s([], 'simprl', '( %s -> q e. %s )' % (Aqf3, N1))], 'q e. NN')
    fn3 = ap(w, Aqf3, 'elfznn', [w.s([], 'simprr', '( %s -> f e. %s )' % (Aqf3, N1))], 'f e. NN')
    ph3 = ap(w, Aqf3, 'phicl', [qn3], '( phi ` q ) e. NN')
    h3 = st(w, Aqf3, [st(w, Aqf3, [st(w, Aqf3, [fn3], 'nncnd', 'f e. CC'), st(w, Aqf3, [ph3], 'nncnd', '( phi ` q ) e. CC'), st(w, Aqf3, [ph3], 'nnne0d', '( phi ` q ) =/= 0')], 'divcld', '( f / ( phi ` q ) ) e. CC'),
                      w.s([J(w, Aqf3, w.s([], 'simpl', '( %s -> ph )' % Aqf3), fn3), 'b'], 'syl', '( %s -> B e. CC )' % Aqf3)], 'mulcld', '%s e. CC' % Hq('q'))
    if3 = st(w, Aqf3, [h3, w.s([], '0cnd', '( %s -> 0 e. CC )' % Aqf3)], 'ifcld', '%s e. CC' % IF_)
    sb = st(w, A0, [fzf, fzf, if3], 'fsumcom', 'sum_ q e. %s sum_ f e. %s %s = sum_ f e. %s sum_ q e. %s %s' % (N1, N1, IF_, N1, N1, IF_))
    # (c) at each f: the sum over q as the sum over TG(f), then over RF(N) by r |-> r f
    Af = '( ph /\\ f e. %s )' % N1
    fnnf = ap(w, Af, 'elfznn', [w.s([], 'simpr', '( %s -> f e. %s )' % (Af, N1))], 'f e. NN')
    tgs = a1(w, Af, 'ssrab2', '%s C_ %s' % (TGN, N1))
    Afq = '( %s /\\ q e. %s )' % (Af, TGN)
    qnq = ap(w, Afq, 'elfznn', [ap(w, Afq, 'elrabi', [w.s([], 'simpr', '( %s -> q e. %s )' % (Afq, TGN))], 'q e. %s' % N1)], 'q e. NN')
    phq = ap(w, Afq, 'phicl', [qnq], '( phi ` q ) e. NN')
    hfq = st(w, Afq, [st(w, Afq, [st(w, Afq, [lift(w, fnnf, Afq)], 'nncnd', 'f e. CC'), st(w, Afq, [phq], 'nncnd', '( phi ` q ) e. CC'), st(w, Afq, [phq], 'nnne0d', '( phi ` q ) =/= 0')], 'divcld', '( f / ( phi ` q ) ) e. CC'),
                      w.s([J(w, Afq, w.s([], 'simpll', '( %s -> ph )' % Afq), lift(w, fnnf, Afq)), 'b'], 'syl', '( %s -> B e. CC )' % Afq)], 'mulcld', '%s e. CC' % Hq('q'))
    ralq = st(w, Af, [hfq], 'ralrimiva', 'A. q e. %s %s e. CC' % (TGN, Hq('q')))
    olcf = st(w, Af, [lift(w, fzf, Af)], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (N1, N1))
    ITG_ = 'if ( q e. %s , %s , 0 )' % (TGN, Hq('q'))
    ssc = ap(w, Af, 'sumss2', [J(w, Af, J(w, Af, tgs, ralq), olcf)], 'sum_ q e. %s %s = sum_ q e. %s %s' % (TGN, Hq('q'), N1, ITG_))
    Afq2 = '( %s /\\ q e. %s )' % (Af, N1)
    sub, _ = w.wcongr('f e. %s' % DIV('g'), {'g': 'q'}, 'g = q', {'g': w.s([], 'id', '( g = q -> g = q )')})
    e3 = ap(w, Afq2, 'elrab3' if False else 'elrab3', [w.s([], 'simpr', '( %s -> q e. %s )' % (Afq2, N1))], '( q e. %s <-> f e. %s )' % (TGN, DIV('q'))) if False else \
        w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Afq2, N1)), w.s([sub], 'elrab3', '( q e. %s -> ( q e. %s <-> f e. %s ) )' % (N1, TGN, DIV('q')))], 'syl', '( %s -> ( q e. %s <-> f e. %s ) )' % (Afq2, TGN, DIV('q')))
    ifb = st(w, Afq2, [e3], 'ifbid', '%s = %s' % (ITG_, IF_))
    sc2 = st(w, Af, [ifb], 'sumeq2dv', 'sum_ q e. %s %s = sum_ q e. %s %s' % (N1, ITG_, N1, IF_))
    sc = eqt(w, Af, eqc(w, Af, sc2), eqc(w, Af, ssc))     # sum_ q e. N1 IF = sum_ q e. TG H
    # (d) reindex by r |-> r f
    f1 = ap(w, Af, 'lswinreglem1', [J(w, Af, lift(w, 'n', Af), w.s([], 'simpr', '( %s -> f e. %s )' % (Af, N1)))], concl('lswinreglem1').replace('f e. ( 1 ... N )', 'f e. ( 1 ... N )'))
    rff = ap(w, Af, 'rabfi', [lift(w, fzf, Af)], '%s e. Fin' % RFN) if False else w.s([lift(w, fzf, Af), w.inst('rabfi')], 'syl', '( %s -> %s e. Fin )' % (Af, RFN))
    subq, _ = w.congr(Hq('q'), {'q': '( h x. f )'}, 'q = ( h x. f )', {'q': w.s([], 'id', '( q = ( h x. f ) -> q = ( h x. f ) )')})
    Afh = '( %s /\\ h e. %s )' % (Af, RFN)
    hnn = ap(w, Afh, 'elfznn', [ap(w, Afh, 'elrabi', [w.s([], 'simpr', '( %s -> h e. %s )' % (Afh, RFN))], 'h e. %s' % N1)], 'h e. NN')
    hf = st(w, Afh, [st(w, Afh, [hnn], 'nncnd', 'h e. CC'), st(w, Afh, [lift(w, fnnf, Afh)], 'nncnd', 'f e. CC')], 'mulcld', '( h x. f ) e. CC')
    fvh = fvmd(w, Afh, 'l', RFN, '( l x. f )', 'h', w.s([], 'simpr', '( %s -> h e. %s )' % (Afh, RFN)), hf)
    fo = st(w, Af, [subq, rff, f1, fvh, hfq], 'fsumf1o', 'sum_ q e. %s %s = sum_ h e. %s %s' % (TGN, Hq('q'), RFN, Hq('( h x. f )')))
    subh, _ = w.congr(Hq('( h x. f )'), {'h': 'r'}, 'h = r', {'h': w.s([], 'id', '( h = r -> h = r )')})
    cbv = a1(w, Af, 'cbvsumv', 'x') if False else w.s([w.s([subh], 'cbvsumv', 'sum_ h e. %s %s = sum_ r e. %s %s' % (RFN, Hq('( h x. f )'), RFN, Hq('( r x. f )')))], 'a1i',
                                                   '( %s -> sum_ h e. %s %s = sum_ r e. %s %s )' % (Af, RFN, Hq('( h x. f )'), RFN, Hq('( r x. f )')))
    perf = eqt(w, Af, eqt(w, Af, sc, fo), cbv)
    sd = st(w, A0, [perf], 'sumeq2dv', 'sum_ f e. %s sum_ q e. %s %s = sum_ f e. %s sum_ r e. %s %s' % (N1, N1, IF_, N1, RFN, Hq('( r x. f )')))
    fin = eqc(w, A0, eqt(w, A0, eqt(w, A0, sa, sb), sd)); qedlast(w); go(w)
