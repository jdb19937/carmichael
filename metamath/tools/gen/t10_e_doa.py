"""T10: the divOut arithmetic the divOutF loop reads (Lean ` divOut_cost_pos_iff ` , ` divOut_fst_of_cost_zero ` ,
the invariant ` DOInv ` 's relation with its existential ` r' ` made explicit as ` r / d ^ i ` ).

  docp   ` 0 < ( divOut d r f ).2 <-> ( f =/= 0 /\ r mod d = 0 ) `
  dofz   ` ( divOut d r f ).2 = 0 -> ( divOut d r f ).1 = r `
  dosh   for ` i <_ ( divOut d r f ).2 ` : ` i <_ f ` and
         ` divOut d r f = ( ( divOut d ( r / d ^ i ) ( f - i ) ).1 , ( divOut d ( r / d ^ i ) ( f - i ) ).2 + i ) `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_e_doa.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, lineq
from cl import Closure

SEL = sys.argv[1:]
DOX = lambda r, f: '( ( G DivOut %s ) ` %s )' % (r, f)
P1 = lambda x: '( 1st ` %s )' % x
P2 = lambda x: '( 2nd ` %s )' % x
PH3 = '( G e. NN /\\ F e. NN0 /\\ H e. NN0 )'
RI = lambda i: '( |_ ` ( F / ( G ^ %s ) ) )' % i
ST_DOCP = '( %s -> ( 0 < %s <-> ( H =/= 0 /\\ ( F mod G ) = 0 ) ) )' % (PH3, P2(DOX('F', 'H')))
ST_DOFZ = '( ( %s /\\ %s = 0 ) -> %s = F )' % (PH3, P2(DOX('F', 'H')), P1(DOX('F', 'H')))
SHV = lambda i: '<. %s , ( %s + %s ) >.' % (P1(DOX(RI(i), '( H - %s )' % i)), P2(DOX(RI(i), '( H - %s )' % i)), i)
ST_DOSH = ('( ( %s /\\ ( I e. NN0 /\\ I <_ %s ) ) -> ( I <_ H /\\ %s = %s ) )'
           % (PH3, P2(DOX('F', 'H')), DOX('F', 'H'), SHV('I')))
STMTS_DOA = {'docp': ST_DOCP, 'dofz': ST_DOFZ, 'dosh': ST_DOSH}


def val0(w, pc, gnn, rn, r, f, f0):
    """( pc -> DOX( r , f ) = <. r , 0 >. ) from f0 : ( pc -> f = 0 )"""
    s = w.s
    e1 = s([f0], 'fveq2d', '( %s -> %s = %s )' % (pc, DOX(r, f), DOX(r, '0')))
    e2 = s([gnn, rn, w.inst('divout0')], 'syl2anc', '( %s -> %s = <. %s , 0 >. )' % (pc, DOX(r, '0'), r))
    return s([e1, e2], 'eqtrd', '( %s -> %s = <. %s , 0 >. )' % (pc, DOX(r, f), r))


def valp(w, pc, gnn, rn, r, f, fnn):
    """( pc -> DOX( r , f ) = if ( ( r mod G ) = 0 , <. a , ( b + 1 ) >. , <. r , 0 >. ) ) for f e. NN (fnn)"""
    s = w.s
    f1 = '( %s - 1 )' % f
    f1n = s([fnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (pc, f1))
    hh = s([s([fnn], 'nncnd', '( %s -> %s e. CC )' % (pc, f)), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % pc)],
           'npcand', '( %s -> ( %s + 1 ) = %s )' % (pc, f1, f))
    e1 = s([s([hh], 'eqcomd', '( %s -> %s = ( %s + 1 ) )' % (pc, f, f1))], 'fveq2d',
           '( %s -> %s = %s )' % (pc, DOX(r, f), DOX(r, '( %s + 1 )' % f1)))
    Q = '( |_ ` ( %s / G ) )' % r
    A_, B_ = P1(DOX(Q, f1)), P2(DOX(Q, f1))
    IFV_ = 'if ( ( %s mod G ) = 0 , <. %s , ( %s + 1 ) >. , <. %s , 0 >. )' % (r, A_, B_, r)
    e2 = s([s([gnn, rn], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (pc, r)), f1n, w.inst('divoutp1')], 'syl2anc',
           '( %s -> %s = %s )' % (pc, DOX(r, '( %s + 1 )' % f1), IFV_))
    return s([e1, e2], 'eqtrd', '( %s -> %s = %s )' % (pc, DOX(r, f), IFV_)), Q, f1, f1n, A_, B_, IFV_


def snd_of(w, pc, x, a, b, xeq, aex, bex):
    """( pc -> ( 2nd ` x ) = b ) from xeq : ( pc -> x = <. a , b >. )"""
    s = w.s
    e = s([xeq], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pc, x, a, b))
    return s([e, s([aex, bex, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pc, a, b, b))], 'eqtrd',
             '( %s -> ( 2nd ` %s ) = %s )' % (pc, x, b))


def fst_of(w, pc, x, a, b, xeq, aex, bex):
    s = w.s
    e = s([xeq], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (pc, x, a, b))
    return s([e, s([aex, bex, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (pc, a, b, a))], 'eqtrd',
             '( %s -> ( 1st ` %s ) = %s )' % (pc, x, a))


def ex_(w, pc, t, kind):
    return w.s([w.s([], kind, '%s e. _V' % t)], 'a1i', '( %s -> %s e. _V )' % (pc, t))


def cases_do(w, ph, gnn, rn, fn_, r, f, body):
    """body(pc, kind, val) for the three cases of DOX( r , f ): kind 'f0' (f = 0), 'dv' (f =/= 0, r mod G = 0),
    'nd' (f =/= 0, r mod G =/= 0); val : ( pc -> DOX( r , f ) = <. x , y >. ) and (x, y, xex, yex); combined by pm2.61dan"""
    s = w.s
    L = lambda pc, st, base: s([st], 'adantr', '( %s -> %s )' % (pc, concl(w, base, st)))
    # f = 0
    p0 = '( %s /\\ %s = 0 )' % (ph, f)
    v0 = val0(w, p0, L(p0, gnn, ph), L(p0, rn, ph), r, f, s([], 'simpr', '( %s -> %s = 0 )' % (p0, f)))
    o0 = body(p0, 'f0', v0, (r, '0', s([L(p0, rn, ph)], 'elexd', '( %s -> %s e. _V )' % (p0, r)),
                              s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % p0)))
    pn = '( %s /\\ -. %s = 0 )' % (ph, f)
    fne = s([s([], 'simpr', '( %s -> -. %s = 0 )' % (pn, f))], 'neqned', '( %s -> %s =/= 0 )' % (pn, f))
    fnn = s([s([L(pn, fn_, ph), fne], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (pn, f, f)),
             s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (f, f, f))], 'sylibr', '( %s -> %s e. NN )' % (pn, f))
    vp, Q, f1, f1n, A_, B_, IFV0 = valp(w, pn, L(pn, gnn, ph), L(pn, rn, ph), r, f, fnn)
    outs = []
    for dv in (True, False):
        c = '( %s mod G ) = 0' % r
        pc = '( %s /\\ %s )' % (pn, c if dv else '-. %s' % c)
        cs = s([], 'simpr', '( %s -> %s )' % (pc, c if dv else '-. %s' % c))
        IFV_ = IFV0
        if dv:
            v = s([L(pc, vp, pn), s([cs], 'iftrued', '( %s -> %s = <. %s , ( %s + 1 ) >. )' % (pc, IFV_, A_, B_))], 'eqtrd',
                  '( %s -> %s = <. %s , ( %s + 1 ) >. )' % (pc, DOX(r, f), A_, B_))
            outs.append(body(pc, 'dv', v, (A_, '( %s + 1 )' % B_, ex_(w, pc, A_, 'fvex'), ex_(w, pc, '( %s + 1 )' % B_, 'ovex')),
                             extra=dict(Q=Q, f1=f1, f1n=L(pc, f1n, pn), fne=L(pc, fne, pn), fnn=L(pc, fnn, pn), dvs=cs)))
        else:
            v = s([L(pc, vp, pn), s([cs], 'iffalsed', '( %s -> %s = <. %s , 0 >. )' % (pc, IFV_, r))], 'eqtrd',
                  '( %s -> %s = <. %s , 0 >. )' % (pc, DOX(r, f), r))
            outs.append(body(pc, 'nd', v, (r, '0', s([L(pc, L(pn, rn, ph), pn)], 'elexd', '( %s -> %s e. _V )' % (pc, r)),
                                            s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % pc)),
                             extra=dict(fne=L(pc, fne, pn), nd=cs)))
    X = concl(w, p0, o0)
    on = s(outs, 'pm2.61dan', '( %s -> %s )' % (pn, X))
    return s([o0, on], 'pm2.61dan', '( %s -> %s )' % (ph, X))


def docp():
    lab = 'docp'
    w = W(lab, 'Lean\'s ` divOut_cost_pos_iff ` : ` divOut d r f ` charges at least once exactly when the fuel is not zero '
               'and ` d ` divides ` r ` .')
    ph = PH3
    s = w.s
    gnn, fn, hn = s([], 'simp1', '( %s -> G e. NN )' % ph), s([], 'simp2', '( %s -> F e. NN0 )' % ph), s([], 'simp3', '( %s -> H e. NN0 )' % ph)
    RHS = '( H =/= 0 /\\ ( F mod G ) = 0 )'
    X2 = P2(DOX('F', 'H'))

    def body(pc, kind, v, xy, extra=None):
        x, y, xe, ye = xy
        c2 = snd_of(w, pc, DOX('F', 'H'), x, y, v, xe, ye)
        lt = s([c2], 'breq2d', '( %s -> ( 0 < %s <-> 0 < %s ) )' % (pc, X2, y))
        if kind == 'dv':
            qn = s([L0(w, pc, 'F e. NN0'), L0(w, pc, 'G e. NN'), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, extra['Q']))
            dcl = s([s([L0(w, pc, 'G e. NN'), qn], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (pc, extra['Q'])), extra['f1n'],
                     w.inst('divoutcl')], 'syl2anc', '( %s -> %s e. ( NN0 X. NN0 ) )' % (pc, DOX(extra['Q'], extra['f1'])))
            bn = s([dcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pc, P2(DOX(extra['Q'], extra['f1']))))
            pos = s([s([bn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (pc, y))], 'nngt0d', '( %s -> 0 < %s )' % (pc, y))
            l = s([pos, lt], 'mpbird', '( %s -> 0 < %s )' % (pc, X2))
            r = s([extra['fne'], extra['dvs']], 'jca', '( %s -> %s )' % (pc, RHS))
            return s([l, r], '2thd', '( %s -> ( 0 < %s <-> %s ) )' % (pc, X2, RHS))
        n0 = s([s([], '0re', '0 e. RR')], 'ltnri', '-. 0 < 0')
        nl = s([lt, s([n0], 'a1i', '( %s -> -. 0 < 0 )' % pc)], 'mtbird', '( %s -> -. 0 < %s )' % (pc, X2))
        if kind == 'f0':
            hz = s([], 'simpr', '( %s -> H = 0 )' % pc)
            nr = s([s([hz, s([], 'nne', '( -. H =/= 0 <-> H = 0 )')], 'sylibr', '( %s -> -. H =/= 0 )' % pc)], 'intnanrd',
                   '( %s -> -. %s )' % (pc, RHS))
        else:
            nr = s([extra['nd']], 'intnand', '( %s -> -. %s )' % (pc, RHS))
        return s([nl, nr], '2falsed', '( %s -> ( 0 < %s <-> %s ) )' % (pc, X2, RHS))

    def L0(w_, pc, leaf):
        return lf(pc, leaf)

    def lf(pc, leaf):
        base = {'G e. NN': gnn, 'F e. NN0': fn, 'H e. NN0': hn}[leaf]
        cur = ph
        st = base
        # peel pc = ( ( ph /\ a ) /\ b ) ...
        parts = []
        t = pc
        while t != ph:
            inner = t[2:-2]
            # split at the last top-level /\
            d = 0; k = None
            toks = inner.split(' ')
            for j, tk in enumerate(toks):
                if tk in ('(', '<.', '{'):
                    d += 1
                elif tk in (')', '>.', '}'):
                    d -= 1
                elif tk == '/\\' and d == 0:
                    k = j
            left = ' '.join(toks[:k])
            parts.append(t)
            t = left
        for p in reversed(parts):
            st = s([st], 'adantr', '( %s -> %s )' % (p, leaf))
        return st
    top = cases_do(w, ph, gnn, fn, hn, 'F', 'H', body)
    w.lines[-1] = 'qed' + w.lines[-1][len(top):]
    return w.run()


def lift_from(w, ph, pc, st):
    """lift st : ( ph -> X ) to pc, pc = ( ( ph /\ a ) /\ b ) ... (by adantr)"""
    s = w.s
    X = concl(w, ph, st)
    chain = []
    t = pc
    while t != ph:
        inner = t[2:-2]
        toks = inner.split(' ')
        d = 0; k = None
        for j, tk in enumerate(toks):
            if tk in ('(', '<.', '{'):
                d += 1
            elif tk in (')', '>.', '}'):
                d -= 1
            elif tk == '/\\' and d == 0:
                k = j
        chain.append(t)
        t = ' '.join(toks[:k])
    for p in reversed(chain):
        st = s([st], 'adantr', '( %s -> %s )' % (p, X))
    return st


def dofz():
    lab = 'dofz'
    w = W(lab, 'Lean\'s ` divOut_fst_of_cost_zero ` : when ` divOut d r f ` charges nothing it returns ` r ` .')
    s = w.s
    ph = '( %s /\\ %s = 0 )' % (PH3, P2(DOX('F', 'H')))
    p3 = s([], 'simpl', '( %s -> %s )' % (ph, PH3))
    gnn = s([p3, w.inst('simp1d') if False else p3], 'simp1d', '( %s -> G e. NN )' % ph) if False else s([p3], 'simp1d', '( %s -> G e. NN )' % ph)
    fn = s([p3], 'simp2d', '( %s -> F e. NN0 )' % ph)
    hn = s([p3], 'simp3d', '( %s -> H e. NN0 )' % ph)
    z = s([], 'simpr', '( %s -> %s = 0 )' % (ph, P2(DOX('F', 'H'))))
    X1 = P1(DOX('F', 'H'))

    def body(pc, kind, v, xy, extra=None):
        x, y, xe, ye = xy
        if kind != 'dv':
            return fst_of(w, pc, DOX('F', 'H'), x, y, v, xe, ye)
        c2 = snd_of(w, pc, DOX('F', 'H'), x, y, v, xe, ye)
        qn = s([lift_from(w, ph, pc, fn), lift_from(w, ph, pc, gnn), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, extra['Q']))
        dcl = s([s([lift_from(w, ph, pc, gnn), qn], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (pc, extra['Q'])), extra['f1n'],
                 w.inst('divoutcl')], 'syl2anc', '( %s -> %s e. ( NN0 X. NN0 ) )' % (pc, DOX(extra['Q'], extra['f1'])))
        bn = s([dcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pc, P2(DOX(extra['Q'], extra['f1']))))
        yn0 = s([s([bn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (pc, y)), w.inst('nnne0')], 'syl', '( %s -> %s =/= 0 )' % (pc, y))
        n0 = s([c2, yn0], 'eqnetrd', '( %s -> %s =/= 0 )' % (pc, P2(DOX('F', 'H'))))
        return s([lift_from(w, ph, pc, z), n0], 'pm2.21ddne', '( %s -> %s = F )' % (pc, X1))
    top = cases_do(w, ph, gnn, fn, hn, 'F', 'H', body)
    w.lines[-1] = 'qed' + w.lines[-1][len(top):]
    return w.run()


def dosh():
    lab = 'dosh'
    w = W(lab, 'The invariant of Lean\'s ` divOutF ` loop ( ` DOInv ` ) with its witness explicit: after ` i <_ ( divOut d r f ).2 ` '
               'divisions the current number is ` r / d ^ i ` (floor), ` i <_ f ` and ` divOut d r f ` is ` divOut d ( r / d ^ i ) '
               '( f - i ) ` with ` i ` more charged.')
    s = w.s
    ph = PH3
    R = P2(DOX('F', 'H'))
    gnn, fn, hn = s([], 'simp1', '( %s -> G e. NN )' % ph), s([], 'simp2', '( %s -> F e. NN0 )' % ph), s([], 'simp3', '( %s -> H e. NN0 )' % ph)
    PS = lambda t: '( %s <_ %s -> ( %s <_ H /\\ %s = %s ) )' % (t, R, t, DOX('F', 'H'), SHV(t))

    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    dcl = s([s([gnn, fn], 'jca', '( %s -> ( G e. NN /\\ F e. NN0 ) )' % ph), hn, w.inst('divoutcl')], 'syl2anc',
            '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, DOX('F', 'H')))
    # base: SHV( 0 ) = DO
    g0 = s([s([s([gnn], 'nncnd', '( %s -> G e. CC )' % ph), w.inst('exp0')], 'syl', '( %s -> ( G ^ 0 ) = 1 )' % ph)], 'oveq2d',
           '( %s -> ( F / ( G ^ 0 ) ) = ( F / 1 ) )' % ph)
    d1 = s([s([fn], 'nn0cnd', '( %s -> F e. CC )' % ph), w.inst('div1')], 'syl', '( %s -> ( F / 1 ) = F )' % ph)
    fz = s([s([fn], 'nn0zd', '( %s -> F e. ZZ )' % ph), w.inst('flid')], 'syl', '( %s -> ( |_ ` F ) = F )' % ph)
    r0 = s([s([s([g0, d1], 'eqtrd', '( %s -> ( F / ( G ^ 0 ) ) = F )' % ph)], 'fveq2d', '( %s -> %s = ( |_ ` F ) )' % (ph, RI('0'))), fz],
           'eqtrd', '( %s -> %s = F )' % (ph, RI('0')))
    h0 = s([s([hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('subid1')], 'syl', '( %s -> ( H - 0 ) = H )' % ph)
    rw1, x1 = w.rewrite(SHV('0'), {RI('0'): ('F', r0), '( H - 0 )': ('H', h0)}, ph)
    b2 = s([s([dcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, R))], 'nn0cnd', '( %s -> %s e. CC )' % (ph, R))
    a0 = s([b2, w.inst('addrid')], 'syl', '( %s -> ( %s + 0 ) = %s )' % (ph, R, R))
    rw2, x2 = w.rewrite(x1, {'( %s + 0 )' % R: (R, a0)}, ph)
    e12 = s([s([rw1, rw2], 'eqtrd', '( %s -> %s = %s )' % (ph, SHV('0'), x2)),
             s([s([dcl, w.inst('1st2nd2')], 'syl', '( %s -> %s = %s )' % (ph, DOX('F', 'H'), x2))], 'eqcomd',
               '( %s -> %s = %s )' % (ph, x2, DOX('F', 'H')))], 'eqtrd', '( %s -> %s = %s )' % (ph, SHV('0'), DOX('F', 'H')))
    base = s([s([s([hn], 'nn0ge0d', '( %s -> 0 <_ H )' % ph), s([e12], 'eqcomd', '( %s -> %s = %s )' % (ph, DOX('F', 'H'), SHV('0')))],
                'jca', '( %s -> ( 0 <_ H /\\ %s = %s ) )' % (ph, DOX('F', 'H'), SHV('0')))], 'a1d', '( %s -> %s )' % (ph, PS('0')))
    # step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ %s )' % (a, R)
    La = lambda st: lift_from(w, ph, a2, st)
    mn = s([s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ %s )' % (a2, R))
    gn2, fn2, hn2 = La(gnn), La(fn), La(hn)
    cl = Closure(w, a2, {'m': ('NN0', mn), 'H': ('NN0', hn2), 'F': ('NN0', fn2), 'G': ('NN', gn2)})
    rn = s([La(dcl), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (a2, R))
    cl.leaf(R, 'NN0', rn)
    mle = linarith(w, a2, [m1l], 'm <_ %s' % R, closure=cl)
    ih = s([mle, ih0], 'mpd', '( %s -> ( m <_ H /\\ %s = %s ) )' % (a2, DOX('F', 'H'), SHV('m')))
    mh = s([ih], 'simpld', '( %s -> m <_ H )' % a2)
    dv = s([ih], 'simprd', '( %s -> %s = %s )' % (a2, DOX('F', 'H'), SHV('m')))
    RM, FMm = RI('m'), '( H - m )'
    Gm = '( G ^ m )'
    gmn = s([gn2, mn, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (a2, Gm))
    rmn = s([fn2, gmn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (a2, RM))
    hmn = s([mn, hn2, mh, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (a2, FMm))
    Dm = DOX(RM, FMm)
    dmc = s([s([gn2, rmn], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (a2, RM)), hmn, w.inst('divoutcl')], 'syl2anc',
            '( %s -> %s e. ( NN0 X. NN0 ) )' % (a2, Dm))
    cm = P2(Dm)
    cmn = s([dmc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (a2, cm))
    cl.leaf(cm, 'NN0', cmn)
    # R = cm + m
    rr = snd_of(w, a2, DOX('F', 'H'), P1(Dm), '( %s + m )' % cm, dv, ex_(w, a2, P1(Dm), 'fvex'), ex_(w, a2, '( %s + m )' % cm, 'ovex'))
    cpos = linarith(w, a2, [rr, m1l], '0 < %s' % cm, closure=cl)
    cp = s([s([gn2, rmn, hmn], '3jca', '( %s -> ( G e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (a2, RM, FMm)),
            w.inst('docp')], 'syl', '( %s -> ( 0 < %s <-> ( %s =/= 0 /\\ ( %s mod G ) = 0 ) ) )' % (a2, cm, FMm, RM))
    both = s([cpos, cp], 'mpbid', '( %s -> ( %s =/= 0 /\\ ( %s mod G ) = 0 ) )' % (a2, FMm, RM))
    fne = s([both], 'simpld', '( %s -> %s =/= 0 )' % (a2, FMm))
    mdz = s([both], 'simprd', '( %s -> ( %s mod G ) = 0 )' % (a2, RM))
    fmnn = s([s([hmn, fne], 'jca', '( %s -> ( %s e. NN0 /\\ %s =/= 0 ) )' % (a2, FMm, FMm)),
              s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (FMm, FMm, FMm))], 'sylibr', '( %s -> %s e. NN )' % (a2, FMm))

    one = s([fmnn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (a2, FMm))
    m1h = linarith(w, a2, [one], '( m + 1 ) <_ H', closure=cl)
    vp, Q, f1, f1n, A_, B_, IFV_ = valp(w, a2, gn2, rmn, RM, FMm, fmnn)
    v1 = s([vp, s([mdz], 'iftrued', '( %s -> %s = <. %s , ( %s + 1 ) >. )' % (a2, IFV_, A_, B_))], 'eqtrd',
           '( %s -> %s = <. %s , ( %s + 1 ) >. )' % (a2, Dm, A_, B_))
    # Q = r_( m + 1 ) , f1 = H - ( m + 1 )
    fr = s([fn2], 'nn0red', '( %s -> F e. RR )' % a2)
    qd = s([fr, gmn, gn2, w.inst('fldiv2')], 'syl3anc', '( %s -> %s = ( |_ ` ( F / ( %s x. G ) ) ) )' % (a2, Q, Gm))
    ep = s([s([gn2], 'nncnd', '( %s -> G e. CC )' % a2), mn, w.inst('expp1')], 'syl2anc',
           '( %s -> ( G ^ ( m + 1 ) ) = ( %s x. G ) )' % (a2, Gm))
    qe = s([qd, s([s([s([ep], 'eqcomd', '( %s -> ( %s x. G ) = ( G ^ ( m + 1 ) ) )' % (a2, Gm))], 'oveq2d',
                     '( %s -> ( F / ( %s x. G ) ) = ( F / ( G ^ ( m + 1 ) ) ) )' % (a2, Gm))], 'fveq2d',
                  '( %s -> ( |_ ` ( F / ( %s x. G ) ) ) = %s )' % (a2, Gm, RI('( m + 1 )')))], 'eqtrd', '( %s -> %s = %s )' % (a2, Q, RI('( m + 1 )')))
    fe = s([cl.mem('H', 'CC'), cl.mem('m', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % a2), w.inst('subsub4')],
           'syl3anc', '( %s -> %s = ( H - ( m + 1 ) ) )' % (a2, f1))
    PV = '<. %s , ( %s + 1 ) >.' % (A_, B_)
    rw3, x3 = w.rewrite(PV, {Q: (RI('( m + 1 )'), qe), f1: ('( H - ( m + 1 ) )', fe)}, a2)
    D1 = DOX(RI('( m + 1 )'), '( H - ( m + 1 ) )')
    assert x3 == '<. %s , ( %s + 1 ) >.' % (P1(D1), P2(D1)), x3
    v2 = s([v1, rw3], 'eqtrd', '( %s -> %s = %s )' % (a2, Dm, x3))
    rw4, x4 = w.rewrite(SHV('m'), {Dm: (x3, v2)}, a2)
    A1, B1 = P1(D1), P2(D1)
    pe1 = s([ex_(w, a2, A1, 'fvex'), ex_(w, a2, '( %s + 1 )' % B1, 'ovex'), w.inst('op1stg')], 'syl2anc',
            '( %s -> ( 1st ` %s ) = %s )' % (a2, x3, A1))
    pe2 = s([ex_(w, a2, A1, 'fvex'), ex_(w, a2, '( %s + 1 )' % B1, 'ovex'), w.inst('op2ndg')], 'syl2anc',
            '( %s -> ( 2nd ` %s ) = ( %s + 1 ) )' % (a2, x3, B1))
    rw5, x5 = w.rewrite(x4, {'( 1st ` %s )' % x3: (A1, pe1), '( 2nd ` %s )' % x3: ('( %s + 1 )' % B1, pe2)}, a2)
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % a2)
    g1n = s([gn2, m1n, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( G ^ ( m + 1 ) ) e. NN )' % a2)
    r1n = s([fn2, g1n, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (a2, RI('( m + 1 )')))
    h1n = s([m1n, hn2, m1h, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( H - ( m + 1 ) ) e. NN0 )' % a2)
    d1c = s([s([gn2, r1n], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (a2, RI('( m + 1 )'))), h1n, w.inst('divoutcl')],
            'syl2anc', '( %s -> %s e. ( NN0 X. NN0 ) )' % (a2, D1))
    cl.leaf(B1, 'NN0', s([d1c, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (a2, B1)))
    ar = lineq(w, a2, '( ( %s + 1 ) + m )' % B1, '( %s + ( m + 1 ) )' % B1, closure=cl)
    rw6, x6 = w.rewrite(x5, {'( ( %s + 1 ) + m )' % B1: ('( %s + ( m + 1 ) )' % B1, ar)}, a2)
    assert x6 == SHV('( m + 1 )'), x6
    fin = s([dv, s([s([rw4, rw5], 'eqtrd', '( %s -> %s = %s )' % (a2, SHV('m'), x5)), rw6], 'eqtrd', '( %s -> %s = %s )' % (a2, SHV('m'), x6))],
            'eqtrd', '( %s -> %s = %s )' % (a2, DOX('F', 'H'), x6))
    st1 = s([m1h, fin], 'jca', '( %s -> ( ( m + 1 ) <_ H /\\ %s = %s ) )' % (a2, DOX('F', 'H'), x6))
    st = s([st1], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( %s /\\ ( I e. NN0 /\\ I <_ %s ) )' % (ph, R)
    i2 = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), s([], 'simprl', '( %s -> I e. NN0 )' % p)], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)),
            ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    w.qed([s([], 'simprr', '( %s -> I <_ %s )' % (p, R)), i2], 'mpd', ST_DOSH)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
