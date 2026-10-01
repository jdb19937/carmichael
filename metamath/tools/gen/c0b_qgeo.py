"""Sortie C0b, batch 6: the geometry of the four quarters of a rectangle
(crectmid and crectq1-crectq4)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from lin import linarith

RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')
H1 = '( ( %s - %s ) / 2 )' % (RB, RA); H2 = '( ( %s - %s ) / 2 )' % (IB, IA)
XD = 'X = ( ( %s + %s ) / 2 )' % (RA, RB)
YD = 'Y = ( ( %s + %s ) / 2 )' % (IA, IB)
A0 = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (AB, GEO, XD, YD)


def base(w):
    ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
    geo = w.s([], 'simp2', '( %s -> %s )' % (A0, GEO))
    md = w.s([], 'simp3', '( %s -> ( %s /\\ %s ) )' % (A0, XD, YD))
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
    br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
    bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
    ler = w.s([geo, w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A0, RA, RB))
    lei = w.s([geo, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, IA, IB))
    xd = w.s([md, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, XD))
    yd = w.s([md, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, YD))
    xr = w.s([xd, w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)) if False else w.s([ar, br], 'readdcld', '( %s -> ( %s + %s ) e. RR )' % (A0, RA, RB))], 'rehalfcld', '( %s -> ( ( %s + %s ) / 2 ) e. RR )' % (A0, RA, RB))], 'eqeltrd', '( %s -> X e. RR )' % A0)
    yr = w.s([yd, w.s([w.s([ai, bi], 'readdcld', '( %s -> ( %s + %s ) e. RR )' % (A0, IA, IB))], 'rehalfcld', '( %s -> ( ( %s + %s ) / 2 ) e. RR )' % (A0, IA, IB))], 'eqeltrd', '( %s -> Y e. RR )' % A0)
    return dict(ab=ab, ac=ac, bc=bc, ar=ar, br=br, ai=ai, bi=bi, ler=ler, lei=lei, xd=xd, yd=yd, xr=xr, yr=yr)


# ---- crectmid
w = W('crectmid', 'The midpoint coordinates of a rectangle lie between the corner coordinates and halve the sides.')
d = base(w)
LV = {RA: d['ar'], RB: d['br'], IA: d['ai'], IB: d['bi'], 'X': d['xr'], 'Y': d['yr']}
HY = [d['ler'], d['lei'], d['xd'], d['yd']]
g1 = linarith(w, A0, HY, '%s <_ X' % RA, leaves=LV)
g2 = linarith(w, A0, HY, 'X <_ %s' % RB, leaves=LV)
g3 = linarith(w, A0, HY, '%s <_ Y' % IA, leaves=LV)
g4 = linarith(w, A0, HY, 'Y <_ %s' % IB, leaves=LV)
g5 = linarith(w, A0, HY, '( X - %s ) <_ %s' % (RA, H1), leaves=LV)
g6 = linarith(w, A0, HY, '( %s - X ) <_ %s' % (RB, H1), leaves=LV)
g7 = linarith(w, A0, HY, '( Y - %s ) <_ %s' % (IA, H2), leaves=LV)
g8 = linarith(w, A0, HY, '( %s - Y ) <_ %s' % (IB, H2), leaves=LV)
c1 = w.s([d['xr'], d['yr']], 'jca', '( %s -> ( X e. RR /\\ Y e. RR ) )' % A0)
c2 = w.s([w.s([g1, g2], 'jca', '( %s -> ( %s <_ X /\\ X <_ %s ) )' % (A0, RA, RB)), w.s([g3, g4], 'jca', '( %s -> ( %s <_ Y /\\ Y <_ %s ) )' % (A0, IA, IB))], 'jca',
         '( %s -> ( ( %s <_ X /\\ X <_ %s ) /\\ ( %s <_ Y /\\ Y <_ %s ) ) )' % (A0, RA, RB, IA, IB))
c3 = w.s([w.s([g5, g6], 'jca', '( %s -> ( ( X - %s ) <_ %s /\\ ( %s - X ) <_ %s ) )' % (A0, RA, H1, RB, H1)), w.s([g7, g8], 'jca', '( %s -> ( ( Y - %s ) <_ %s /\\ ( %s - Y ) <_ %s ) )' % (A0, IA, H2, IB, H2))], 'jca',
         '( %s -> ( ( ( X - %s ) <_ %s /\\ ( %s - X ) <_ %s ) /\\ ( ( Y - %s ) <_ %s /\\ ( %s - Y ) <_ %s ) ) )' % (A0, RA, H1, RB, H1, IA, H2, IB, H2))
w.qed([c1, c2, c3], '3jca', '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( ( %s <_ X /\\ X <_ %s ) /\\ ( %s <_ Y /\\ Y <_ %s ) ) /\\ ( ( ( X - %s ) <_ %s /\\ ( %s - X ) <_ %s ) /\\ ( ( Y - %s ) <_ %s /\\ ( %s - Y ) <_ %s ) ) ) )'
      % (A0, RA, RB, IA, IB, RA, H1, RB, H1, IA, H2, IB, H2)); run(w)


def QC(P, Q):
    return ('( ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) ) /\\ '
            '( ( %s crect %s ) C_ ( A crect B ) /\\ ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s ) ) )'
            % (P, Q, P, Q, P, Q, P, Q, Q, P, H1, Q, P, H2))


def quarter(label, desc, P, rp, ip, Q, rq, iq, pick):
    w = W(label, desc)
    d = base(w)
    m = w.s([], 'crectmid', '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( ( %s <_ X /\\ X <_ %s ) /\\ ( %s <_ Y /\\ Y <_ %s ) ) /\\ ( ( ( X - %s ) <_ %s /\\ ( %s - X ) <_ %s ) /\\ ( ( Y - %s ) <_ %s /\\ ( %s - Y ) <_ %s ) ) ) )'
                            % (A0, RA, RB, IA, IB, RA, H1, RB, H1, IA, H2, IB, H2))
    p2 = w.s([m, w.inst('simp2')], 'syl', '( %s -> ( ( %s <_ X /\\ X <_ %s ) /\\ ( %s <_ Y /\\ Y <_ %s ) ) )' % (A0, RA, RB, IA, IB))
    p3 = w.s([m, w.inst('simp3')], 'syl', '( %s -> ( ( ( X - %s ) <_ %s /\\ ( %s - X ) <_ %s ) /\\ ( ( Y - %s ) <_ %s /\\ ( %s - Y ) <_ %s ) ) )' % (A0, RA, H1, RB, H1, IA, H2, IB, H2))
    g = {}
    g[1] = w.s([p2, w.inst('simpll')], 'syl', '( %s -> %s <_ X )' % (A0, RA))
    g[2] = w.s([p2, w.inst('simplr')], 'syl', '( %s -> X <_ %s )' % (A0, RB))
    g[3] = w.s([p2, w.inst('simprl')], 'syl', '( %s -> %s <_ Y )' % (A0, IA))
    g[4] = w.s([p2, w.inst('simprr')], 'syl', '( %s -> Y <_ %s )' % (A0, IB))
    g[5] = w.s([p3, w.inst('simpll')], 'syl', '( %s -> ( X - %s ) <_ %s )' % (A0, RA, H1))
    g[6] = w.s([p3, w.inst('simplr')], 'syl', '( %s -> ( %s - X ) <_ %s )' % (A0, RB, H1))
    g[7] = w.s([p3, w.inst('simprl')], 'syl', '( %s -> ( Y - %s ) <_ %s )' % (A0, IA, H2))
    g[8] = w.s([p3, w.inst('simprr')], 'syl', '( %s -> ( %s - Y ) <_ %s )' % (A0, IB, H2))
    rl = {RA: d['ar'], RB: d['br'], IA: d['ai'], IB: d['bi'], 'X': d['xr'], 'Y': d['yr']}
    lid = {RA: w.s([d['ar']], 'leidd', '( %s -> %s <_ %s )' % (A0, RA, RA)),
           RB: w.s([d['br']], 'leidd', '( %s -> %s <_ %s )' % (A0, RB, RB)),
           IA: w.s([d['ai']], 'leidd', '( %s -> %s <_ %s )' % (A0, IA, IA)),
           IB: w.s([d['bi']], 'leidd', '( %s -> %s <_ %s )' % (A0, IB, IB))}
    ic = closed(w, A0, 'ax-icn', '_i e. CC')

    def cc(V, a, b):
        if V in ('A', 'B'):
            return d['ac'] if V == 'A' else d['bc']
        return w.s([w.s([rl[a]], 'recnd', '( %s -> %s e. CC )' % (A0, a)), w.s([ic, w.s([rl[b]], 'recnd', '( %s -> %s e. CC )' % (A0, b))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, b))], 'addcld', '( %s -> %s e. CC )' % (A0, V))

    def coords(V, a, b):
        if V in ('A', 'B'):
            return (w.s([], 'eqidd', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A0, V, V)),
                    w.s([], 'eqidd', '( %s -> ( Im ` %s ) = ( Im ` %s ) )' % (A0, V, V)))
        return (w.s([rl[a], rl[b], w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, V, a)),
                w.s([rl[a], rl[b], w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, V, b)))
    pc = cc(P, rp, ip); qc = cc(Q, rq, iq)
    sRP, sIP = coords(P, rp, ip); sRQ, sIQ = coords(Q, rq, iq)
    leR = g[pick['leR']] if isinstance(pick['leR'], int) else lid[pick['leR']]
    leI = g[pick['leI']] if isinstance(pick['leI'], int) else lid[pick['leI']]
    o1 = w.s([leR, sRP, sRQ], '3brtr4d', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, P, Q))
    o2 = w.s([leI, sIP, sIQ], '3brtr4d', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, P, Q))
    def pk(k):
        v = pick[k]
        return g[v] if isinstance(v, int) else lid[v]
    c1 = w.s([pk('loR'), sRP], 'breqtrrd', '( %s -> %s <_ ( Re ` %s ) )' % (A0, RA, P))
    c2 = w.s([sRQ, pk('hiR')], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ %s )' % (A0, Q, RB))
    c3 = w.s([pk('loI'), sIP], 'breqtrrd', '( %s -> %s <_ ( Im ` %s ) )' % (A0, IA, P))
    c4 = w.s([sIQ, pk('hiI')], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ %s )' % (A0, Q, IB))
    pq = w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, P, Q))
    inc = w.s([w.s([c1, c2], 'jca', '( %s -> ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) )' % (A0, RA, P, Q, RB)),
               w.s([c3, c4], 'jca', '( %s -> ( %s <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ %s ) )' % (A0, IA, P, Q, IB))], 'jca',
              '( %s -> ( ( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) /\\ ( %s <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ %s ) ) )' % (A0, RA, P, Q, RB, IA, P, Q, IB))
    ss = w.s([d['ab'], pq, inc, w.inst('crectss2')], 'syl3anc', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, P, Q))
    e1 = w.s([w.s([sRQ, sRP], 'oveq12d', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) = ( %s - %s ) )' % (A0, Q, P, rq, rp)), g[pick['sR']]], 'eqbrtrd',
             '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s )' % (A0, Q, P, H1))
    e2 = w.s([w.s([sIQ, sIP], 'oveq12d', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) = ( %s - %s ) )' % (A0, Q, P, iq, ip)), g[pick['sI']]], 'eqbrtrd',
             '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s )' % (A0, Q, P, H2))
    L = w.s([pq, w.s([o1, o2], 'jca', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, P, Q, P, Q))], 'jca',
            '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) ) )' % (A0, P, Q, P, Q, P, Q))
    R = w.s([ss, w.s([e1, e2], 'jca', '( %s -> ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s ) )' % (A0, Q, P, H1, Q, P, H2))], 'jca',
            '( %s -> ( ( %s crect %s ) C_ ( A crect B ) /\\ ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s ) ) )' % (A0, P, Q, Q, P, H1, Q, P, H2))
    w.qed([L, R], 'jca', '( %s -> %s )' % (A0, QC(P, Q)))
    run(w)

XY = PT('X', 'Y')
quarter('crectq1', 'The lower left quarter of a rectangle.', 'A', RA, IA, XY, 'X', 'Y',
        dict(leR=1, leI=3, loR=RA, hiR=2, loI=IA, hiI=4, sR=5, sI=7))
quarter('crectq2', 'The lower right quarter of a rectangle.', PT('X', IA), 'X', IA, PT(RB, 'Y'), RB, 'Y',
        dict(leR=2, leI=3, loR=1, hiR=RB, loI=IA, hiI=4, sR=6, sI=7))
quarter('crectq3', 'The upper right quarter of a rectangle.', XY, 'X', 'Y', 'B', RB, IB,
        dict(leR=2, leI=4, loR=1, hiR=RB, loI=3, hiI=IB, sR=6, sI=8))
quarter('crectq4', 'The upper left quarter of a rectangle.', PT(RA, 'Y'), RA, 'Y', PT('X', IB), 'X', IB,
        dict(leR=1, leI=4, loR=RA, hiR=2, loI=3, hiI=IB, sR=5, sI=8))


# ---- rectintqabs: the triangle inequality over the four quarters
QRT = [('1', 'A', PT('X', 'Y')), ('2', PT('X', IA), PT(RB, 'Y')), ('3', PT('X', 'Y'), 'B'), ('4', PT(RA, 'Y'), PT('X', IB))]
w = W('rectintqabs', 'A rectangle boundary integral is bounded by the sum of the absolute values of its four quarter integrals.')
A1 = '( %s /\\ %s /\\ %s )' % (PS, XD, YD)
d = ctx(w, A1)
xd = w.s([], 'simp2', '( %s -> %s )' % (A1, XD))
yd = w.s([], 'simp3', '( %s -> %s )' % (A1, YD))
mid = w.s([d['ab'], d['geo'], w.s([xd, yd], 'jca', '( %s -> ( %s /\\ %s ) )' % (A1, XD, YD))], '3jca', '( %s -> %s )' % (A1, A0))
Is = []; cc = {}
for num, P, Q in QRT:
    cq = w.s([mid, w.inst('crectq' + num)], 'syl', '( %s -> %s )' % (A1, QC(P, Q)))
    ccp = w.s([cq, w.inst('simpll')], 'syl', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A1, P, Q))
    ordp = w.s([cq, w.inst('simplr')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A1, P, Q, P, Q))
    inc = w.s([cq, w.inst('simprl')], 'syl', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A1, P, Q))
    ssd = w.s([inc, d['rss']], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A1, P, Q))
    psq = w.s([ccp, ordp, w.s([d['fcn'], ssd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (A1, P, Q))], '3jca', '( %s -> %s )' % (A1, PSOF(P, Q)))
    I = '( F rectint <. %s , %s >. )' % (P, Q)
    Is.append(I)
    cc[I] = w.s([psq, w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A1, I))
qt = w.s([d['ab'], d['geo'], w.s([d['fcn'], d['rss']], 'jca', '( %s -> %s )' % (A1, FCN))], '3jca', '( %s -> %s )' % (A1, PS))
qtr = w.s([qt, xd, yd, w.inst('rectintqtr')], 'syl3anc', '( %s -> ( F rectint <. A , B >. ) = ( ( %s + %s ) + ( %s + %s ) ) )' % (A1, Is[0], Is[1], Is[2], Is[3]))
S1 = '( %s + %s )' % (Is[0], Is[1]); S2 = '( %s + %s )' % (Is[2], Is[3])
c1 = w.s([cc[Is[0]], cc[Is[1]]], 'addcld', '( %s -> %s e. CC )' % (A1, S1))
c2 = w.s([cc[Is[2]], cc[Is[3]]], 'addcld', '( %s -> %s e. CC )' % (A1, S2))
ar_ = [w.s([cc[x]], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, x)) for x in Is]
t0 = w.s([c1, c2], 'abstrid', '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, S1, S2, S1, S2))
t1 = w.s([cc[Is[0]], cc[Is[1]]], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, S1, Is[0], Is[1]))
t2 = w.s([cc[Is[2]], cc[Is[3]]], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A1, S2, Is[2], Is[3]))
as1 = w.s([c1], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, S1))
as2 = w.s([c2], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, S2))
p12 = w.s([ar_[0], ar_[1]], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A1, Is[0], Is[1]))
p34 = w.s([ar_[2], ar_[3]], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A1, Is[2], Is[3]))
tot = w.s([as1, as2, p12, p34, t1, t2], 'le2addd', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A1, S1, S2, Is[0], Is[1], Is[2], Is[3]))
abt = w.s([w.s([c1, c2], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A1, S1, S2))], 'abscld', '( %s -> ( abs ` ( %s + %s ) ) e. RR )' % (A1, S1, S2))
chn = w.s([abt, w.s([as1, as2], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A1, S1, S2)), w.s([p12, p34], 'readdcld', '( %s -> ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) e. RR )' % (A1, Is[0], Is[1], Is[2], Is[3])), t0, tot], 'letrd',
          '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A1, S1, S2, Is[0], Is[1], Is[2], Is[3]))
w.qed([w.s([qtr], 'fveq2d', '( %s -> ( abs ` ( F rectint <. A , B >. ) ) = ( abs ` ( %s + %s ) ) )' % (A1, S1, S2)), chn], 'eqbrtrd',
      '( %s -> ( abs ` ( F rectint <. A , B >. ) ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A1, Is[0], Is[1], Is[2], Is[3])); run(w)
