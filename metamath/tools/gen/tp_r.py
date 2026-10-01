"""Sortie TP: Turan's second main theorem (tpmaxg: any finite index set, designated maximal entry, lower bound T;
tpmax, tpmaxlb: Lean turan_power_sum_max, turan_power_sum_max_lb)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift, WIN, CN
import cl as _cl
import ef2lib as E
import mvlib

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


ZX = '( Z ` X )'
AZ = '( abs ` %s )' % ZX
PS = lambda k: 'sum_ j e. I ( ( Z ` j ) ^ %s )' % k
BODY = lambda k: '( %s x. ( T ^ %s ) ) <_ ( abs ` %s )' % (CN(), k, PS(k))
GA = ('( ( N e. NN /\\ M e. NN0 ) /\\ ( I e. Fin /\\ ( # ` I ) <_ N /\\ Z : I --> CC ) /\\ '
      '( X e. I /\\ A. y e. I ( abs ` ( Z ` y ) ) <_ %s /\\ ( T e. RR /\\ 0 <_ T /\\ T <_ %s ) ) )' % (AZ, AZ))
GOAL = 'E. k e. %s %s' % (WIN(), BODY('k'))
S['tpmaxg'] = '( %s -> %s )' % (GA, GOAL)
tplib.S['tpmaxg'] = S['tpmaxg']


def fvc(w, K, var, dom, body, arg, argin):
    ida = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, arg, var, arg))
    cg, val = w.congr(body, {var: arg}, '%s = %s' % (var, arg), {var: ida})
    ex = w.s([], 'ovex', '%s e. _V' % val)
    mp = '( %s e. %s |-> %s )' % (var, dom, body)
    st = w.s([cg, w.s([], 'eqid', '%s = %s' % (mp, mp)), ex], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (arg, dom, mp, arg, val))
    return w.s([argin, st], 'syl', '( %s -> ( %s ` %s ) = %s )' % (K, mp, arg, val))


def gen_maxg():
    w = W('tpmaxg', 'Turan\'s second main theorem for any finite index set: if ` # I <_ N ` , ` Z_X ` has the largest modulus and ` 0 <_ T <_ abs Z_X ` , '
               'some ` k e. [ M + 1 , M + N ] ` has ` ( N / ( 8 e ( M + N ) ) ) ^ N T ^ k <_ abs sum_( j e. I ) Z_j ^ k ` .')
    A0 = GA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( N e. NN /\\ M e. NN0 )'); t2 = s([], 'simp2', '( I e. Fin /\\ ( # ` I ) <_ N /\\ Z : I --> CC )')
    t3 = s([], 'simp3', '( X e. I /\\ A. y e. I ( abs ` ( Z ` y ) ) <_ %s /\\ ( T e. RR /\\ 0 <_ T /\\ T <_ %s ) )' % (AZ, AZ))
    nn = s([t1], 'simpld', 'N e. NN'); mm = s([t1], 'simprd', 'M e. NN0')
    ifin = s([t2], 'simp1d', 'I e. Fin'); hle = s([t2], 'simp2d', '( # ` I ) <_ N'); zf = s([t2], 'simp3d', 'Z : I --> CC')
    xi = s([t3], 'simp1d', 'X e. I'); zb = s([t3], 'simp2d', 'A. y e. I ( abs ` ( Z ` y ) ) <_ %s' % AZ)
    tt = s([t3], 'simp3d', '( T e. RR /\\ 0 <_ T /\\ T <_ %s )' % AZ)
    tr = s([tt], 'simp1d', 'T e. RR'); t0 = s([tt], 'simp2d', '0 <_ T'); tz = s([tt], 'simp3d', 'T <_ %s' % AZ)
    zxc = s([zf, xi], 'ffvelcdmd', '%s e. CC' % ZX)
    c = Closure(w, A0, {'N': ('NN', nn), 'M': ('NN0', mm), 'T': ('RR', tr), ZX: ('CC', zxc)})
    c.have('T', 'ge0', t0); c.atom(ZX)
    # the window contains M + 1; CN is in [ 0 , 1 ]
    m1w = ap(w, A0, 'elfzd', '( M + 1 ) e. %s' % WIN(), c,
             facts=[c.mem('( M + 1 )', 'ZZ'), c.mem('( M + N )', 'ZZ'), s([c.mem('( M + 1 )', 'RR')], 'leidd', '( M + 1 ) <_ ( M + 1 )'),
                    lin.linarith(w, A0, [s([nn], 'nnge1d', '1 <_ N')], '( M + 1 ) <_ ( M + N )', closure=c)])
    E1 = '( exp ` 1 )'
    BASE = '( N / ( ( 8 x. %s ) x. ( M + N ) ) )' % E1
    FF_ = '( n e. NN |-> ( 2 x. ( ( 1 / 2 ) ^ n ) ) )'; GG_ = '( n e. NN0 |-> ( 1 / ( ! ` n ) ) )'
    e2 = s([w.s([w.s([], 'eqid', '%s = %s' % (FF_, FF_)), w.s([], 'eqid', '%s = %s' % (GG_, GG_))], 'ege2le3', '( 2 <_ _e /\\ _e <_ 3 )')], 'a1i', '( 2 <_ _e /\\ _e <_ 3 )')
    ee = s([w.s([], 'df-e', '_e = ( exp ` 1 )')], 'a1i', '_e = ( exp ` 1 )')
    e2b = s([s([e2], 'simpld', '2 <_ _e'), ee], 'breqtrd', '2 <_ %s' % E1)
    c.atom(E1); c.have(E1, 'RR', c.mem(E1, 'RR'))
    c.have('( ( 8 x. %s ) x. ( M + N ) )' % E1, 'RR+', c.mem('( ( 8 x. %s ) x. ( M + N ) )' % E1, 'RR+'))
    bg0 = c.ge0(BASE)
    den = '( ( 8 x. %s ) x. ( M + N ) )' % E1
    c.atom(den)
    dge = lin.nlinarith(w, A0, [e2b, c.ge0('M'), s([nn], 'nnge1d', '1 <_ N')], 'N <_ ( 1 x. %s )' % den, closure=Closure(w, A0, {'N': ('NN', nn), 'M': ('NN0', mm), E1: ('RR', c.mem(E1, 'RR'))}))
    ble = s([dge, ap(w, A0, 'ledivmul2d', '( %s <_ 1 <-> N <_ ( 1 x. %s ) )' % (BASE, den), c)], 'mpbird', '%s <_ 1' % BASE)
    cnle = s([s([c.mem(BASE, 'RR'), bg0, ble], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 )' % (BASE, BASE, BASE)), c.mem('N', 'NN0'), w.inst('exple1')], 'syl2anc', '%s <_ 1' % CN())
    c.atom(CN()); c.have(CN(), 'RR', c.mem(CN(), 'RR'))
    cn0 = ap(w, A0, 'expge0d', '0 <_ %s' % CN(), c, facts=[bg0])
    c.have(CN(), 'ge0', cn0)
    # the power sum is complex (any k e. NN0)
    def psc(K, k, kn0):
        Kj = '( %s /\\ j e. I )' % K
        zj = w.s([_cl.lift(w, zf, Kj), w.s([], 'simpr', '( %s -> j e. I )' % Kj)], 'ffvelcdmd', '( %s -> ( Z ` j ) e. CC )' % Kj)
        return w.s([_cl.lift(w, ifin, K), w.s([zj, _cl.lift(w, kn0, Kj)], 'expcld', '( %s -> ( ( Z ` j ) ^ %s ) e. CC )' % (Kj, k))], 'fsumcl', '( %s -> %s e. CC )' % (K, PS(k)))
    def exhibit(K, bst):
        """( K -> GOAL ) from bst: ( K -> BODY ( M + 1 ) )"""
        idk = w.s([], 'id', '( k = ( M + 1 ) -> k = ( M + 1 ) )')
        cg, nw = w.wcongr(BODY('k'), {'k': '( M + 1 )'}, 'k = ( M + 1 )', {'k': idk})
        return w.s([_cl.lift(w, m1w, K), bst, w.s([cg], 'rspcev', '( ( ( M + 1 ) e. %s /\\ %s ) -> %s )' % (WIN(), nw, GOAL))], 'syl2anc', '( %s -> %s )' % (K, GOAL))
    # ---- case Z_X = 0 : T = 0
    C0 = '( %s /\\ %s = 0 )' % (A0, ZX)
    L0 = lambda st: _cl.lift(w, st, C0)
    c0_ = Closure(w, C0, {'N': ('NN', L0(nn)), 'M': ('NN0', L0(mm)), 'T': ('RR', L0(tr))})
    c0_.have(ZX, 'CC', L0(zxc)); c0_.atom(ZX)
    az0 = w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (C0, ZX))], 'fveq2d', '( %s -> %s = ( abs ` 0 ) )' % (C0, AZ)),
               w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % C0)], 'eqtrd', '( %s -> %s = 0 )' % (C0, AZ))
    teq = lin.lineq(w, C0, 'T', '0', hyps=[L0(tz), az0, L0(t0)], closure=c0_)
    tpow = w.s([w.s([teq], 'oveq1d', '( %s -> ( T ^ ( M + 1 ) ) = ( 0 ^ ( M + 1 ) ) )' % C0), w.s([c0_.mem('( M + 1 )', 'NN')], '0expd', '( %s -> ( 0 ^ ( M + 1 ) ) = 0 )' % C0)],
               'eqtrd', '( %s -> ( T ^ ( M + 1 ) ) = 0 )' % C0)
    lhs0 = w.s([w.s([tpow], 'oveq2d', '( %s -> ( %s x. ( T ^ ( M + 1 ) ) ) = ( %s x. 0 ) )' % (C0, CN(), CN())),
                w.s([L0(c.mem(CN(), 'CC'))], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (C0, CN()))], 'eqtrd', '( %s -> ( %s x. ( T ^ ( M + 1 ) ) ) = 0 )' % (C0, CN()))
    pc0 = psc(C0, '( M + 1 )', c0_.mem('( M + 1 )', 'NN0'))
    b0 = w.s([lhs0, w.s([pc0], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (C0, PS('( M + 1 )')))], 'eqbrtrd', '( %s -> %s )' % (C0, BODY('( M + 1 )')))
    case0 = exhibit(C0, b0)
    # ---- case Z_X =/= 0
    C1 = '( %s /\\ -. %s = 0 )' % (A0, ZX)
    L1 = lambda st: _cl.lift(w, st, C1)
    zn0 = w.s([w.s([], 'simpr', '( %s -> -. %s = 0 )' % (C1, ZX))], 'neqned', '( %s -> %s =/= 0 )' % (C1, ZX))
    # ---- sub-case N = 1
    C1b = '( %s /\\ -. 2 <_ N )' % C1
    Lb = lambda st: _cl.lift(w, st, C1b)
    cb = Closure(w, C1b, {'N': ('NN', Lb(L1(nn))), 'M': ('NN0', Lb(L1(mm))), 'T': ('RR', Lb(L1(tr)))})
    nlt2 = w.s([w.s([], 'simpr', '( %s -> -. 2 <_ N )' % C1b), ap(w, C1b, 'ltnled', '( N < 2 <-> -. 2 <_ N )', cb)], 'mpbird', '( %s -> N < 2 )' % C1b)
    np1 = w.s([nlt2, w.s([cb.mem('N', 'ZZ'), w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % C1b), w.inst('zltp1le')], 'syl2anc',
                         '( %s -> ( N < 2 <-> ( N + 1 ) <_ 2 ) )' % C1b)], 'mpbid', '( %s -> ( N + 1 ) <_ 2 )' % C1b)
    hI = w.s([Lb(L1(ifin)), w.inst('hashcl')], 'syl', '( %s -> ( # ` I ) e. NN0 )' % C1b)
    cb.have('( # ` I )', 'NN0', hI)
    ine = w.s([Lb(L1(xi)), w.inst('ne0i')], 'syl', '( %s -> I =/= (/) )' % C1b)
    h1 = w.s([Lb(L1(ifin)), ine, w.inst('hashge1')], 'syl2anc', '( %s -> 1 <_ ( # ` I ) )' % C1b)
    hdi = w.s([Lb(L1(ifin)), Lb(L1(xi)), w.inst('hashdifsn')], 'syl2anc', '( %s -> ( # ` ( I \\ { X } ) ) = ( ( # ` I ) - 1 ) )' % C1b)
    h0 = lin.lineq(w, C1b, '( ( # ` I ) - 1 )', '0', hyps=[h1, Lb(L1(hle)), np1], closure=cb)
    dz = w.s([hdi, h0], 'eqtrd', '( %s -> ( # ` ( I \\ { X } ) ) = 0 )' % C1b)
    de = w.s([dz, w.s([w.s([Lb(L1(ifin)), w.inst('diffi')], 'syl', '( %s -> ( I \\ { X } ) e. Fin )' % C1b), w.inst('hasheq0')], 'syl',
                      '( %s -> ( ( # ` ( I \\ { X } ) ) = 0 <-> ( I \\ { X } ) = (/) ) )' % C1b)], 'mpbid', '( %s -> ( I \\ { X } ) = (/) )' % C1b)
    isn = w.s([w.s([Lb(L1(xi)), w.inst('difsnid')], 'syl', '( %s -> ( ( I \\ { X } ) u. { X } ) = I )' % C1b),
               w.s([w.s([de], 'uneq1d', '( %s -> ( ( I \\ { X } ) u. { X } ) = ( (/) u. { X } ) )' % C1b), w.s([w.s([], '0un', '( (/) u. { X } ) = { X }')], 'a1i', '( %s -> ( (/) u. { X } ) = { X } )' % C1b)],
                   'eqtrd', '( %s -> ( ( I \\ { X } ) u. { X } ) = { X } )' % C1b)], 'eqtr3d', '( %s -> I = { X } )' % C1b)
    m1n0 = cb.mem('( M + 1 )', 'NN0')
    sI = w.s([isn], 'sumeq1d', '( %s -> %s = sum_ j e. { X } ( ( Z ` j ) ^ ( M + 1 ) ) )' % (C1b, PS('( M + 1 )')))
    idjx = w.s([], 'id', '( j = X -> j = X )')
    cjx, _ = w.congr('( ( Z ` j ) ^ ( M + 1 ) )', {'j': 'X'}, 'j = X', {'j': idjx})
    zxm = w.s([Lb(L1(zxc)), m1n0], 'expcld', '( %s -> ( %s ^ ( M + 1 ) ) e. CC )' % (C1b, ZX))
    ssn = w.s([Lb(L1(xi)), zxm, w.s([cjx], 'sumsn', '( ( X e. I /\\ ( %s ^ ( M + 1 ) ) e. CC ) -> sum_ j e. { X } ( ( Z ` j ) ^ ( M + 1 ) ) = ( %s ^ ( M + 1 ) ) )' % (ZX, ZX))],
              'syl2anc', '( %s -> sum_ j e. { X } ( ( Z ` j ) ^ ( M + 1 ) ) = ( %s ^ ( M + 1 ) ) )' % (C1b, ZX))
    ab1 = w.s([w.s([w.s([sI, ssn], 'eqtrd', '( %s -> %s = ( %s ^ ( M + 1 ) ) )' % (C1b, PS('( M + 1 )'), ZX))], 'fveq2d',
                   '( %s -> ( abs ` %s ) = ( abs ` ( %s ^ ( M + 1 ) ) ) )' % (C1b, PS('( M + 1 )'), ZX)),
               w.s([Lb(L1(zxc)), m1n0], 'absexpd', '( %s -> ( abs ` ( %s ^ ( M + 1 ) ) ) = ( %s ^ ( M + 1 ) ) )' % (C1b, ZX, AZ))], 'eqtrd',
              '( %s -> ( abs ` %s ) = ( %s ^ ( M + 1 ) ) )' % (C1b, PS('( M + 1 )'), AZ))
    cb.have(AZ, 'RR', Lb(L1(c.mem(AZ, 'RR')))); cb.atom(AZ)
    tpw = ap(w, C1b, 'leexp1ad', '( T ^ ( M + 1 ) ) <_ ( %s ^ ( M + 1 ) )' % AZ, cb, facts=[Lb(L1(tz)), Lb(L1(t0))])
    cb.have(CN(), 'RR', Lb(L1(c.mem(CN(), 'RR')))); cb.have(CN(), 'ge0', Lb(L1(cn0))); cb.atom(CN())
    cb.have('T', 'ge0', Lb(L1(t0)))
    tg = ap(w, C1b, 'expge0d', '0 <_ ( T ^ ( M + 1 ) )', cb)
    mm12 = ap(w, C1b, 'lemul12ad', '( %s x. ( T ^ ( M + 1 ) ) ) <_ ( 1 x. ( %s ^ ( M + 1 ) ) )' % (CN(), AZ), cb, facts=[Lb(L1(cnle)), tpw, tg])
    mm13 = w.s([mm12, ap(w, C1b, 'mullidd', '( 1 x. ( %s ^ ( M + 1 ) ) ) = ( %s ^ ( M + 1 ) )' % (AZ, AZ), cb)], 'breqtrd', '( %s -> ( %s x. ( T ^ ( M + 1 ) ) ) <_ ( %s ^ ( M + 1 ) ) )' % (C1b, CN(), AZ))
    bb = w.s([mm13, ab1], 'breqtrrd', '( %s -> %s )' % (C1b, BODY('( M + 1 )')))
    caseb = exhibit(C1b, bb)
    # ---- sub-case 2 <_ N: normalise and apply tpmaxn
    C1a = '( %s /\\ 2 <_ N )' % C1
    La = lambda st: _cl.lift(w, st, C1a)
    sa = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C1a, f))
    ca = Closure(w, C1a, {'N': ('NN', La(L1(nn))), 'M': ('NN0', La(L1(mm))), 'T': ('RR', La(L1(tr))), ZX: ('CC', La(L1(zxc)))})
    ca.have(ZX, 'ne0', La(zn0)); ca.atom(ZX)
    WW = '( x e. I |-> ( ( Z ` x ) / %s ) )' % ZX
    Cx = '( %s /\\ x e. I )' % C1a
    zxx = w.s([_cl.lift(w, La(L1(zf)), Cx), w.s([], 'simpr', '( %s -> x e. I )' % Cx)], 'ffvelcdmd', '( %s -> ( Z ` x ) e. CC )' % Cx)
    cxx = Closure(w, Cx, {'( Z ` x )': ('CC', zxx), ZX: ('CC', _cl.lift(w, La(L1(zxc)), Cx))}); cxx.have(ZX, 'ne0', _cl.lift(w, La(zn0), Cx)); cxx.atom(ZX); cxx.atom('( Z ` x )')
    wwf = sa([cxx.mem('( ( Z ` x ) / %s )' % ZX, 'CC'), w.s([], 'eqid', '%s = %s' % (WW, WW))], 'fmptd', '%s : I --> CC' % WW)
    # abs WW_f <_ 1
    Cf = '( %s /\\ f e. I )' % C1a
    fin_ = w.s([], 'simpr', '( %s -> f e. I )' % Cf)
    zfc = w.s([_cl.lift(w, La(L1(zf)), Cf), fin_], 'ffvelcdmd', '( %s -> ( Z ` f ) e. CC )' % Cf)
    cf = Closure(w, Cf, {'( Z ` f )': ('CC', zfc), ZX: ('CC', _cl.lift(w, La(L1(zxc)), Cf))}); cf.have(ZX, 'ne0', _cl.lift(w, La(zn0), Cf)); cf.atom(ZX); cf.atom('( Z ` f )')
    wv = fvc(w, Cf, 'x', 'I', '( ( Z ` x ) / %s )' % ZX, 'f', fin_)
    idyf = w.s([], 'id', '( y = f -> y = f )')
    cyf, nyf = w.wcongr('( abs ` ( Z ` y ) ) <_ %s' % AZ, {'y': 'f'}, 'y = f', {'y': idyf})
    zfb = w.s([fin_, _cl.lift(w, La(L1(zb)), Cf), w.s([cyf], 'rspcv', '( f e. I -> ( A. y e. I ( abs ` ( Z ` y ) ) <_ %s -> %s ) )' % (AZ, nyf))], 'sylc', '( %s -> %s )' % (Cf, nyf))
    cf.have(AZ, 'RR+', ap(w, Cf, 'absrpcld', '%s e. RR+' % AZ, cf)); cf.atom(AZ)
    cf.have('( abs ` ( Z ` f ) )', 'RR', cf.mem('( abs ` ( Z ` f ) )', 'RR')); cf.atom('( abs ` ( Z ` f ) )')
    ad = ap(w, Cf, 'absdivd', '( abs ` ( ( Z ` f ) / %s ) ) = ( ( abs ` ( Z ` f ) ) / %s )' % (ZX, AZ), cf)
    le1 = w.s([lin.linarith(w, Cf, [zfb], '( abs ` ( Z ` f ) ) <_ ( 1 x. %s )' % AZ, closure=cf),
               ap(w, Cf, 'ledivmul2d', '( ( ( abs ` ( Z ` f ) ) / %s ) <_ 1 <-> ( abs ` ( Z ` f ) ) <_ ( 1 x. %s ) )' % (AZ, AZ), cf)], 'mpbird', '( %s -> ( ( abs ` ( Z ` f ) ) / %s ) <_ 1 )' % (Cf, AZ))
    wfb = w.s([w.s([w.s([wv], 'fveq2d', '( %s -> ( abs ` ( %s ` f ) ) = ( abs ` ( ( Z ` f ) / %s ) ) )' % (Cf, WW, ZX)), ad], 'eqtrd',
                   '( %s -> ( abs ` ( %s ` f ) ) = ( ( abs ` ( Z ` f ) ) / %s ) )' % (Cf, WW, AZ)), le1], 'eqbrtrd', '( %s -> ( abs ` ( %s ` f ) ) <_ 1 )' % (Cf, WW))
    alf = w.s([wfb], 'ralrimiva', '( %s -> A. f e. I ( abs ` ( %s ` f ) ) <_ 1 )' % (C1a, WW))
    idfy = w.s([], 'id', '( f = y -> f = y )')
    cfy, nfy = w.wcongr('( abs ` ( %s ` f ) ) <_ 1' % WW, {'f': 'y'}, 'f = y', {'f': idfy})
    aly = sa([alf, w.s([cfy], 'cbvralvw', '( A. f e. I ( abs ` ( %s ` f ) ) <_ 1 <-> A. y e. I %s )' % (WW, nfy))], 'sylib', 'A. y e. I %s' % nfy)
    wx = fvc(w, C1a, 'x', 'I', '( ( Z ` x ) / %s )' % ZX, 'X', La(L1(xi)))
    wx1 = sa([wx, ap(w, C1a, 'dividd', '( %s / %s ) = 1' % (ZX, ZX), ca)], 'eqtrd', '( %s ` X ) = 1' % WW)
    MN = tsub(stmt('tpmaxn'), {'W': WW})
    mna, mnc = ante_of(MN)
    have = {'( N e. NN /\\ 2 <_ N /\\ M e. NN0 )': sa([La(L1(nn)), w.s([], 'simpr', '( %s -> 2 <_ N )' % C1a), La(L1(mm))], '3jca', '( N e. NN /\\ 2 <_ N /\\ M e. NN0 )'),
            'I e. Fin': La(L1(ifin)), '( # ` I ) <_ N': La(L1(hle)), '%s : I --> CC' % WW: wwf, 'X e. I': La(L1(xi)), body_of(w, aly): aly, '( %s ` X ) = 1' % WW: wx1}
    mn = sa([conj(w, C1a, mna, have), w.inst('tpmaxn')], 'syl', mnc)
    PW = lambda k: 'sum_ j e. I ( ( %s ` j ) ^ %s )' % (WW, k)
    Ck = '( %s /\\ k e. %s )' % (C1a, WIN())
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ck, f))
    Lk = lambda st: _cl.lift(w, st, Ck)
    kin = w.s([], 'simpr', '( %s -> k e. %s )' % (Ck, WIN()))
    ck = Closure(w, Ck, {'M': ('NN0', Lk(La(L1(mm)))), 'T': ('RR', Lk(La(L1(tr)))), 'k': ('ZZ', w.s([kin, w.inst('elfzelz')], 'syl', '( %s -> k e. ZZ )' % Ck)),
                         ZX: ('CC', Lk(La(L1(zxc))))})
    ck.have(ZX, 'ne0', Lk(La(zn0))); ck.atom(ZX); ck.have('T', 'ge0', Lk(La(L1(t0))))
    kle = w.s([kin, w.inst('elfzle1')], 'syl', '( %s -> ( M + 1 ) <_ k )' % Ck)
    kn0 = w.s([w.s([ck.mem('k', 'ZZ'), lin.linarith(w, Ck, [kle, ck.ge0('M')], '0 <_ k', closure=ck)], 'jca', '( %s -> ( k e. ZZ /\\ 0 <_ k ) )' % Ck), w.inst('elnn0z')],
              'sylibr', '( %s -> k e. NN0 )' % Ck)
    ck.have('k', 'NN0', kn0)
    Cj = '( %s /\\ j e. I )' % Ck
    jI = w.s([], 'simpr', '( %s -> j e. I )' % Cj)
    zj = w.s([_cl.lift(w, Lk(La(L1(zf))), Cj), jI], 'ffvelcdmd', '( %s -> ( Z ` j ) e. CC )' % Cj)
    cj = Closure(w, Cj, {'( Z ` j )': ('CC', zj), ZX: ('CC', _cl.lift(w, Lk(La(L1(zxc))), Cj)), 'k': ('NN0', _cl.lift(w, kn0, Cj))})
    cj.have(ZX, 'ne0', _cl.lift(w, Lk(La(zn0)), Cj)); cj.atom(ZX); cj.atom('( Z ` j )')
    wj = fvc(w, Cj, 'x', 'I', '( ( Z ` x ) / %s )' % ZX, 'j', jI)
    q1 = w.s([wj], 'oveq1d', '( %s -> ( ( %s ` j ) ^ k ) = ( ( ( Z ` j ) / %s ) ^ k ) )' % (Cj, WW, ZX))
    q2 = ap(w, Cj, 'expdivd', '( ( ( Z ` j ) / %s ) ^ k ) = ( ( ( Z ` j ) ^ k ) / ( %s ^ k ) )' % (ZX, ZX), cj)
    s1 = sk([w.s([q1, q2], 'eqtrd', '( %s -> ( ( %s ` j ) ^ k ) = ( ( ( Z ` j ) ^ k ) / ( %s ^ k ) ) )' % (Cj, WW, ZX))], 'sumeq2dv',
            '%s = sum_ j e. I ( ( ( Z ` j ) ^ k ) / ( %s ^ k ) )' % (PW('k'), ZX))
    ck.have('( %s ^ k )' % ZX, 'CC', ck.mem('( %s ^ k )' % ZX, 'CC'))
    ZK = '( %s ^ k )' % ZX
    zkn = ap(w, Ck, 'expne0d', '%s =/= 0' % ZK, ck, facts=[ck.mem('k', 'ZZ')])
    ck.have(ZK, 'ne0', zkn); ck.atom(ZK)
    s2 = sk([Lk(La(L1(ifin))), ck.mem(ZK, 'CC'), cj.mem('( ( Z ` j ) ^ k )', 'CC'), zkn], 'fsumdivc', '( %s / %s ) = sum_ j e. I ( ( ( Z ` j ) ^ k ) / %s )' % (PS('k'), ZK, ZK))
    s3 = sk([s1, s2], 'eqtr4d', '%s = ( %s / %s )' % (PW('k'), PS('k'), ZK))
    psk = psc(Ck, 'k', kn0)
    ck.have(PS('k'), 'CC', psk); ck.atom(PS('k'))
    s4 = sk([sk([s3], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s / %s ) )' % (PW('k'), PS('k'), ZK)), ap(w, Ck, 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (PS('k'), ZK, PS('k'), ZK), ck)],
            'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (PW('k'), PS('k'), ZK))
    s5 = ap(w, Ck, 'absexpd', '( abs ` %s ) = ( %s ^ k )' % (ZK, AZ), ck)
    AK = '( %s ^ k )' % AZ
    s6 = sk([s4, sk([s5], 'oveq2d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / %s )' % (PS('k'), ZK, PS('k'), AK))], 'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) / %s )' % (PW('k'), PS('k'), AK))
    ck.have(AZ, 'RR+', ap(w, Ck, 'absrpcld', '%s e. RR+' % AZ, ck)); ck.atom(AZ)
    ck.have(AK, 'RR+', ck.mem(AK, 'RR+')); ck.atom(AK)
    ck.have('( abs ` %s )' % PS('k'), 'RR', ck.mem('( abs ` %s )' % PS('k'), 'RR')); ck.atom('( abs ` %s )' % PS('k'))
    ck.have(CN(), 'RR', Lk(La(L1(c.mem(CN(), 'RR'))))); ck.have(CN(), 'ge0', Lk(La(L1(cn0)))); ck.atom(CN())
    Ck2 = '( %s /\\ %s <_ ( abs ` %s ) )' % (Ck, CN(), PW('k'))
    L2 = lambda st: _cl.lift(w, st, Ck2)
    c2 = Closure(w, Ck2, {})
    for tt_, kd in ((CN(), 'RR'), (AK, 'RR+'), ('( abs ` %s )' % PS('k'), 'RR'), ('T', 'RR'), (AZ, 'RR+')):
        c2.have(tt_, kd, L2(ck.mem(tt_, kd))); c2.atom(tt_)
    c2.have(CN(), 'ge0', L2(ck.ge0(CN()))); c2.have('T', 'ge0', L2(ck.ge0('T'))); c2.have('k', 'NN0', L2(kn0))
    h2 = w.s([w.s([], 'simpr', '( %s -> %s <_ ( abs ` %s ) )' % (Ck2, CN(), PW('k'))), L2(s6)], 'breqtrd', '( %s -> %s <_ ( ( abs ` %s ) / %s ) )' % (Ck2, CN(), PS('k'), AK))
    h3 = w.s([h2, ap(w, Ck2, 'lemuldivd', '( ( %s x. %s ) <_ ( abs ` %s ) <-> %s <_ ( ( abs ` %s ) / %s ) )' % (CN(), AK, PS('k'), CN(), PS('k'), AK), c2)], 'mpbird',
             '( %s -> ( %s x. %s ) <_ ( abs ` %s ) )' % (Ck2, CN(), AK, PS('k')))
    tk = ap(w, Ck2, 'leexp1ad', '( T ^ k ) <_ %s' % AK, c2, facts=[L2(Lk(La(L1(tz)))), L2(Lk(La(L1(t0))))])
    h4 = ap(w, Ck2, 'lemul2ad', '( %s x. ( T ^ k ) ) <_ ( %s x. %s )' % (CN(), CN(), AK), c2, facts=[tk])
    h5 = w.s([h4, h3], 'letrd', '( %s -> %s )' % (Ck2, BODY('k')))
    imp = w.s([h5], 'ex', '( %s -> ( %s <_ ( abs ` %s ) -> %s ) )' % (Ck, CN(), PW('k'), BODY('k')))
    rx = sa([imp], 'reximdva', '( E. k e. %s %s <_ ( abs ` %s ) -> %s )' % (WIN(), CN(), PW('k'), GOAL))
    casea = sa([mn, rx], 'mpd', GOAL)
    c1g = w.s([casea, caseb], 'pm2.61dan', '( %s -> %s )' % (C1, GOAL))
    w.qed([case0, c1g], 'pm2.61dan', S['tpmaxg'])
    return run(w)


S['tpmaxlb'] = tplib.S['tpmaxlb']
S['tpmax'] = tplib.S['tpmax']


def gen_maxlb():
    w = W('tpmaxlb', 'Lean ` turan_power_sum_max_lb ` : Turan\'s second main theorem against any lower bound ` 0 <_ T <_ abs z_0 ` on the largest modulus.')
    A0, GC = ante_of(S['tpmaxlb'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X0 = '( 0 ..^ N )'
    t1 = s([], 'simp1', '( N e. NN /\\ M e. NN0 /\\ Z : %s --> CC )' % X0)
    hb = s([], 'simp2', 'A. j e. %s ( abs ` ( Z ` j ) ) <_ ( abs ` ( Z ` 0 ) )' % X0)
    tt = s([], 'simp3', '( T e. RR /\\ 0 <_ T /\\ T <_ ( abs ` ( Z ` 0 ) ) )')
    nn = s([t1], 'simp1d', 'N e. NN'); mm = s([t1], 'simp2d', 'M e. NN0'); zf = s([t1], 'simp3d', 'Z : %s --> CC' % X0)
    idjy = w.s([], 'id', '( j = y -> j = y )')
    cjy, njy = w.wcongr('( abs ` ( Z ` j ) ) <_ ( abs ` ( Z ` 0 ) )', {'j': 'y'}, 'j = y', {'j': idjy})
    hy = s([hb, w.s([cjy], 'cbvralvw', '( A. j e. %s ( abs ` ( Z ` j ) ) <_ ( abs ` ( Z ` 0 ) ) <-> A. y e. %s %s )' % (X0, X0, njy))], 'sylib', 'A. y e. %s %s' % (X0, njy))
    c = Closure(w, A0, {'N': ('NN', nn)})
    hn = s([c.mem('N', 'NN0'), w.inst('hashfzo0')], 'syl', '( # ` %s ) = N' % X0)
    hle = s([hn, s([c.mem('N', 'RR')], 'leidd', 'N <_ N')], 'eqbrtrd', '( # ` %s ) <_ N' % X0)
    z0 = s([nn, w.inst('lbfzo0')], 'sylibr', '0 e. %s' % X0)
    MG = tsub(stmt('tpmaxg'), {'I': X0, 'X': '0'})
    ga, gc = ante_of(MG)
    have = {'( N e. NN /\\ M e. NN0 )': s([nn, mm], 'jca', '( N e. NN /\\ M e. NN0 )'),
            '( 0 ..^ N ) e. Fin': s([w.s([], 'fzofi', '%s e. Fin' % X0)], 'a1i', '%s e. Fin' % X0), '( # ` %s ) <_ N' % X0: hle, 'Z : %s --> CC' % X0: zf,
            '0 e. %s' % X0: z0, 'A. y e. %s %s' % (X0, njy): hy, '( T e. RR /\\ 0 <_ T /\\ T <_ ( abs ` ( Z ` 0 ) ) )': tt}
    w.qed([conj(w, A0, ga, have), w.inst('tpmaxg')], 'syl', S['tpmaxlb'])
    return run(w)


def gen_max():
    w = W('tpmax', 'Lean ` turan_power_sum_max ` : for ` z_0 ` of largest modulus some ` k e. [ M + 1 , M + N ] ` has '
               '` ( N / ( 8 e ( M + N ) ) ) ^ N abs z_0 ^ k <_ abs sum_j z_j ^ k ` .')
    A0, GC = ante_of(S['tpmax'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X0 = '( 0 ..^ N )'
    t1 = s([], 'simpl', '( N e. NN /\\ M e. NN0 /\\ Z : %s --> CC )' % X0)
    hb = s([], 'simpr', 'A. j e. %s ( abs ` ( Z ` j ) ) <_ ( abs ` ( Z ` 0 ) )' % X0)
    nn = s([t1], 'simp1d', 'N e. NN'); zf = s([t1], 'simp3d', 'Z : %s --> CC' % X0)
    z0 = s([nn, w.inst('lbfzo0')], 'sylibr', '0 e. %s' % X0)
    zc = s([zf, z0], 'ffvelcdmd', '( Z ` 0 ) e. CC')
    ar = s([zc], 'abscld', '( abs ` ( Z ` 0 ) ) e. RR')
    t3 = s([ar, s([zc], 'absge0d', '0 <_ ( abs ` ( Z ` 0 ) )'), s([ar], 'leidd', '( abs ` ( Z ` 0 ) ) <_ ( abs ` ( Z ` 0 ) )')], '3jca',
           '( ( abs ` ( Z ` 0 ) ) e. RR /\\ 0 <_ ( abs ` ( Z ` 0 ) ) /\\ ( abs ` ( Z ` 0 ) ) <_ ( abs ` ( Z ` 0 ) ) )')
    LB = tsub(S['tpmaxlb'], {'T': '( abs ` ( Z ` 0 ) )'})
    la, lc = ante_of(LB)
    w.qed([s([t1, hb, t3], '3jca', la), w.inst('tpmaxlb')], 'syl', S['tpmax'])
    return run(w)


if __name__ == '__main__':
    gen_maxg()
    gen_maxlb()
    gen_max()
