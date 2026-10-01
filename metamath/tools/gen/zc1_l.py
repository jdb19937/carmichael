"""Sortie ZC1: the box count from square counts (boxcnt, Lean box_count_core): fibres of q |-> floor ( Im q )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c0lib import hyp
from c8_o import numst
from c8_n import sqparts, sqre_at, sqcc
from c10_f import crfacts, clo
import zc1_i
from zc1_i import encode
import lin
lin.FASTPATH = True

L_ = '( log ` ( A x. ( T + 2 ) ) )'
QB = '( K x. ( 2 x. %s ) )' % L_


def SUBT(t):
    return '{ p e. G | p e. %s }' % SQ(CT(t), R138)


BXH = ['( ph -> G e. Fin )',
       '( ( ph /\\ q e. G ) -> ( W e. RR /\\ 0 <_ W ) )',
       '( ( ph /\\ q e. G ) -> ( q e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) )',
       '( ph -> ( ( T e. RR /\\ 1 <_ T ) /\\ ( A e. RR /\\ 1 <_ A ) /\\ ( K e. RR /\\ 0 <_ K ) ) )',
       '( ( ph /\\ t e. RR ) -> sum_ q e. %s W <_ ( K x. ( log ` ( A x. ( ( abs ` t ) + 2 ) ) ) ) )' % SUBT('t')]
S['boxcnt'] = '( ph -> sum_ q e. G W <_ ( ( 4 x. T ) x. %s ) )' % QB


def gen_boxcnt():
    w = W('boxcnt', 'Box count from square counts (Lean ` box_count_core ` ): if every square of half-side ` 13 / 8 ` about ` 2 + i t ` carries weight at most ` K log ( A ( abs t + 2 ) ) ` of the finite set ` G ` of points of ` [ 1 / 2 , 1 ] x. [ - T , T ] ` , ` T >_ 1 ` , then ` G ` carries at most ` 4 T K 2 log ( A ( T + 2 ) ) ` : the fibres of ` q |-> floor ( Im q ) ` lie in the squares at heights ` m + 1 / 2 ` ( ~ fsumiun , ~ invdisjrab ).')
    h = [hyp(w, str(i + 1), 'boxcnt.%d' % (i + 1), f) for i, f in enumerate(BXH)]
    A0 = 'ph'
    s = lambda hs, r, f: w.s(hs, r, '( ph -> %s )' % f)
    Y1, Y2, Y3 = top_and(ante_of(BXH[3])[1])
    y1 = s([h[3], w.inst('simp1')], 'syl', Y1); y2 = s([h[3], w.inst('simp2')], 'syl', Y2); y3 = s([h[3], w.inst('simp3')], 'syl', Y3)
    tr = s([y1, w.inst('simpl')], 'syl', 'T e. RR'); t1 = s([y1, w.inst('simpr')], 'syl', '1 <_ T')
    ar = s([y2, w.inst('simpl')], 'syl', 'A e. RR'); a1 = s([y2, w.inst('simpr')], 'syl', '1 <_ A')
    kr = s([y3, w.inst('simpl')], 'syl', 'K e. RR'); k0 = s([y3, w.inst('simpr')], 'syl', '0 <_ K')
    FT = '( |_ ` T )'
    LO = '( -u %s - 1 )' % FT
    I = '( %s ... %s )' % (LO, FT)
    FL = '( |_ ` ( Im ` q ) )'
    FLU = '( |_ ` ( Im ` u ) )'
    FB = lambda m: '{ u e. G | %s = %s }' % (FLU, m)
    ftz = s([tr], 'flcld', '%s e. ZZ' % FT)
    loz = s([s([ftz], 'znegcld', '-u %s e. ZZ' % FT), s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')], 'zsubcld', '%s e. ZZ' % LO)
    ftr = s([ftz], 'zred', '%s e. RR' % FT)
    ftle = s([tr, w.inst('flle')], 'syl', '%s <_ T' % FT)
    ftlt = s([tr, w.inst('flltp1')], 'syl', 'T < ( %s + 1 )' % FT)
    # (a) FL e. I for q e. G
    Aq = '( ph /\\ q e. G )'
    sq = lambda hs, r, f: w.s(hs, r, '( %s -> %s )' % (Aq, f))
    Lq = lambda st: lift(w, st, Aq)
    q3 = sq([], 'x', 'x') if False else '3'
    Z1, Z2, Z3 = top_and(ante_of(BXH[2])[1])
    qc = sq([h[2], w.inst('simp1')], 'syl', 'q e. CC'); qre = sq([h[2], w.inst('simp2')], 'syl', Z2); qim = sq([h[2], w.inst('simp3')], 'syl', Z3)
    imr = sq([qc], 'imcld', '( Im ` q ) e. RR'); rer = sq([qc], 'recld', '( Re ` q ) e. RR')
    ab = sq([qim, sq([imr, Lq(tr)], 'absled', '( ( abs ` ( Im ` q ) ) <_ T <-> ( -u T <_ ( Im ` q ) /\\ ( Im ` q ) <_ T ) )')], 'mpbid', '( -u T <_ ( Im ` q ) /\\ ( Im ` q ) <_ T )')
    ilo = sq([ab, w.inst('simpl')], 'syl', '-u T <_ ( Im ` q )'); ihi = sq([ab, w.inst('simpr')], 'syl', '( Im ` q ) <_ T')
    flz = sq([imr], 'flcld', '%s e. ZZ' % FL)
    lvq = {'( Im ` q )': imr, 'T': Lq(tr), FT: Lq(ftr)}
    l1 = lin8(w, Aq, [ilo, Lq(ftlt)], '%s <_ ( Im ` q )' % LO, lvq)
    g1 = sq([l1, sq([imr, Lq(loz), w.inst('flge')], 'syl2anc', '( %s <_ ( Im ` q ) <-> %s <_ %s )' % (LO, LO, FL))], 'mpbid', '%s <_ %s' % (LO, FL))
    fli = sq([imr, w.inst('flle')], 'syl', '%s <_ ( Im ` q )' % FL)
    l2 = sq([sq([flz], 'zred', '%s e. RR' % FL), imr, Lq(tr), fli, ihi], 'letrd', '%s <_ T' % FL)
    g2 = sq([l2, sq([Lq(tr), flz, w.inst('flge')], 'syl2anc', '( %s <_ T <-> %s <_ %s )' % (FL, FL, FT))], 'mpbid', '%s <_ %s' % (FL, FT))
    fi = sq([sq([sq([Lq(loz), Lq(ftz), flz], '3jca', '( %s e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ )' % (LO, FT, FL)), sq([g1, g2], 'jca', '( %s <_ %s /\\ %s <_ %s )' % (LO, FL, FL, FT))], 'jca',
                '( ( %s e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ ) /\\ ( %s <_ %s /\\ %s <_ %s ) )' % (LO, FT, FL, LO, FL, FL, FT)),
             w.s([], 'elfz2', '( %s e. %s <-> ( ( %s e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ ) /\\ ( %s <_ %s /\\ %s <_ %s ) ) )' % (FL, I, LO, FT, FL, LO, FL, FL, FT))], 'sylibr', '%s e. %s' % (FL, I))
    # (b) G = U_ m e. I FB ( m )
    ex = sq([fi, w.s([w.s([], 'risset', '( %s e. %s <-> E. m e. %s m = %s )' % (FL, I, I, FL)), w.s([w.s([], 'eqcom', '( m = %s <-> %s = m )' % (FL, FL))], 'rexbii', '( E. m e. %s m = %s <-> E. m e. %s %s = m )' % (I, FL, I, FL))],
                              'bitri', '( %s e. %s <-> E. m e. %s %s = m )' % (FL, I, I, FL))], 'sylib', 'E. m e. %s %s = m' % (I, FL))
    alq = s([ex], 'ralrimiva', 'A. q e. G E. m e. %s %s = m' % (I, FL))
    equ = w.wcongr('E. m e. %s %s = m' % (I, FL), {'q': 'u'}, 'q = u', {'q': w.s([], 'id', '( q = u -> q = u )')})[0]
    alu = s([alq, w.s([equ], 'cbvralvw', '( A. q e. G E. m e. %s %s = m <-> A. u e. G E. m e. %s %s = m )' % (I, FL, I, FLU))], 'sylib', 'A. u e. G E. m e. %s %s = m' % (I, FLU))
    rid = s([alu, w.s([], 'rabid2', '( G = { u e. G | E. m e. %s %s = m } <-> A. u e. G E. m e. %s %s = m )' % (I, FLU, I, FLU))],
            'sylibr', 'G = { u e. G | E. m e. %s %s = m }' % (I, FLU))
    IU = 'U_ m e. %s %s' % (I, FB('m'))
    iu = s([w.s([], 'iunrab', '%s = { u e. G | E. m e. %s %s = m }' % (IU, I, FLU))], 'a1i', '%s = { u e. G | E. m e. %s %s = m }' % (IU, I, FLU))
    geq = s([rid, s([iu], 'eqcomd', '{ u e. G | E. m e. %s %s = m } = %s' % (I, FLU, IU))], 'eqtrd', 'G = %s' % IU)
    # (c) fsumiun
    Ak = '( ph /\\ m e. %s )' % I
    fbf = w.s([lift(w, h[0], Ak), w.s([w.s([], 'ssrab2', '%s C_ G' % FB('m'))], 'a1i', '( %s -> %s C_ G )' % (Ak, FB('m')))], 'ssfid', '( %s -> %s e. Fin )' % (Ak, FB('m')))
    dj = s([w.s([], 'invdisjrab', 'Disj_ m e. %s %s' % (I, FB('m')))], 'a1i', 'Disj_ m e. %s %s' % (I, FB('m')))
    Akq = '( ph /\\ ( m e. %s /\\ q e. %s ) )' % (I, FB('m'))
    qg = w.s([w.s([], 'simprr', '( %s -> q e. %s )' % (Akq, FB('m'))), w.inst('elrabi')], 'syl', '( %s -> q e. G )' % Akq)
    def wreal(ante, phst, qgst):
        """( ante -> W e. RR ) and ( ante -> 0 <_ W ) from ( ante -> ph ), ( ante -> q e. G )"""
        j = w.s([phst, qgst], 'jca', '( %s -> ( ph /\\ q e. G ) )' % ante)
        b = w.s([j, h[1]], 'syl', '( %s -> ( W e. RR /\\ 0 <_ W ) )' % ante)
        return w.s([b, w.inst('simpl')], 'syl', '( %s -> W e. RR )' % ante), w.s([b, w.inst('simpr')], 'syl', '( %s -> 0 <_ W )' % ante)
    wkr, _ = wreal(Akq, w.s([], 'simpl', '( %s -> ph )' % Akq), qg)
    wkc = w.s([wkr], 'recnd', '( %s -> W e. CC )' % Akq)
    ifin = s([], 'fzfid', '%s e. Fin' % I)
    fsi = s([ifin, fbf, dj, wkc], 'fsumiun', 'sum_ q e. %s W = sum_ m e. %s sum_ q e. %s W' % (IU, I, FB('m')))
    sg = s([s([geq], 'sumeq1d', 'sum_ q e. G W = sum_ q e. %s W' % IU), fsi], 'eqtrd', 'sum_ q e. G W = sum_ m e. %s sum_ q e. %s W' % (I, FB('m')))
    return w, dict(h=h, s=s, tr=tr, t1=t1, ar=ar, a1=a1, kr=kr, k0=k0, FT=FT, LO=LO, I=I, FL=FL, FB=FB, ftz=ftz, loz=loz, ftr=ftr, ftle=ftle, ftlt=ftlt, sg=sg, wreal=wreal, ifin=ifin, fbf=fbf, Ak=Ak)


def gen_boxcnt_full():
    w, d = gen_boxcnt()
    h, s = d['h'], d['s']
    tr, t1, ar, a1, kr, k0 = d['tr'], d['t1'], d['ar'], d['a1'], d['kr'], d['k0']
    FT, LO, I, FL, FB, Ak = d['FT'], d['LO'], d['I'], d['FL'], d['FB'], d['Ak']
    FLU = '( |_ ` ( Im ` u ) )'
    sk = lambda hs, r, f: w.s(hs, r, '( %s -> %s )' % (Ak, f))
    Lk = lambda st: lift(w, st, Ak)
    kI = sk([], 'simpr', 'm e. %s' % I)
    kz = sk([kI, w.inst('elfzelz')], 'syl', 'm e. ZZ')
    kr_ = sk([kz], 'zred', 'm e. RR')
    TK = '( m + ( 1 / 2 ) )'
    tkr = sk([kr_, numst(w, Ak, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % TK)
    klo = sk([kI, w.inst('elfzle1')], 'syl', '%s <_ m' % LO); khi = sk([kI, w.inst('elfzle2')], 'syl', 'm <_ %s' % FT)
    # FB ( m ) C_ SUBT ( TK )
    Ckq = '( %s /\\ q e. %s )' % (Ak, FB('m'))
    sc = lambda hs, r, f: w.s(hs, r, '( %s -> %s )' % (Ckq, f))
    Lc = lambda st: lift(w, st, Ckq)
    qfb = sc([], 'simpr', 'q e. %s' % FB('m'))
    eb = w.s([w.s([w.s([w.s([], 'fveq2', '( u = q -> ( Im ` u ) = ( Im ` q ) )')], 'fveq2d', '( u = q -> %s = %s )' % (FLU, FL))], 'eqeq1d', '( u = q -> ( %s = m <-> %s = m ) )' % (FLU, FL))],
             'elrab', '( q e. %s <-> ( q e. G /\\ %s = m ) )' % (FB('m'), FL))
    qq = sc([qfb, eb], 'sylib', '( q e. G /\\ %s = m )' % FL)
    qg = sc([qq, w.inst('simpl')], 'syl', 'q e. G'); fk = sc([qq, w.inst('simpr')], 'syl', '%s = m' % FL)
    Z3 = ante_of(BXH[2])[1]
    z3 = sc([sc([Lc(s([], 'id', 'ph') if False else w.s([], 'simpll', '( %s -> ph )' % Ckq)) if False else w.s([], 'simpll', '( %s -> ph )' % Ckq), qg], 'jca', '( ph /\\ q e. G )'), h[2]], 'syl', Z3)
    qc = sc([z3, w.inst('simp1')], 'syl', 'q e. CC')
    qre = sc([z3, w.inst('simp2')], 'syl', top_and(Z3)[1])
    rlo = sc([qre, w.inst('simpl')], 'syl', '( 1 / 2 ) <_ ( Re ` q )'); rhi = sc([qre, w.inst('simpr')], 'syl', '( Re ` q ) <_ 1')
    imr = sc([qc], 'imcld', '( Im ` q ) e. RR')
    fle = sc([sc([imr, w.inst('flle')], 'syl', '%s <_ ( Im ` q )' % FL), fk], 'eqbrtrrd', 'm <_ ( Im ` q )') if False else \
        sc([fk, sc([imr, w.inst('flle')], 'syl', '%s <_ ( Im ` q )' % FL)], 'eqbrtrrd', 'm <_ ( Im ` q )')
    flt = sc([sc([imr, w.inst('flltp1')], 'syl', '( Im ` q ) < ( %s + 1 )' % FL), sc([fk], 'oveq1d', '( %s + 1 ) = ( m + 1 )' % FL)], 'breqtrd', '( Im ` q ) < ( m + 1 )')
    CK = CT(TK)
    ckc, rck, ick = crfacts(w, Ckq, '2', TK, numst(w, Ckq, '2', 'RR'), Lc(tkr))
    r138 = numst(w, Ckq, R138, 'RR')
    sa, sb = sqcc(w, Ckq, ckc, r138, c=CK, r=R138)
    ps = sqparts(w, Ckq, sqre_at(w, Ckq, ckc, r138, c=CK, r=R138), c=CK, r=R138)
    SA, SB = SQA(CK, R138), SQB(CK, R138)
    lv = {'( Re ` q )': sc([qc], 'recld', '( Re ` q ) e. RR'), '( Im ` q )': imr, 'm': Lc(kr_)}
    for e, st in (('( Re ` %s )' % CK, ckc), ('( Im ` %s )' % CK, ckc), ('( Re ` %s )' % SA, sa), ('( Im ` %s )' % SA, sa), ('( Re ` %s )' % SB, sb), ('( Im ` %s )' % SB, sb)):
        lv[e] = sc([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hy = [rck, ick, rlo, rhi, fle, flt] + ps
    qsq = encode(w, Ckq, qc, sa, sb, SA, SB, 'q', lin8(w, Ckq, hy, '( Re ` %s ) <_ ( Re ` q )' % SA, lv), lin8(w, Ckq, hy, '( Re ` q ) <_ ( Re ` %s )' % SB, lv),
                 lin8(w, Ckq, hy, '( Im ` %s ) <_ ( Im ` q )' % SA, lv), lin8(w, Ckq, hy, '( Im ` q ) <_ ( Im ` %s )' % SB, lv))
    sube = w.s([], 'eleq1', '( p = q -> ( p e. %s <-> q e. %s ) )' % (SQ(CK, R138), SQ(CK, R138)))
    qst = sc([sube, qg, qsq], 'elrabd', 'q e. %s' % SUBT(TK))
    fbs = sk([w.s([qst], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (Ak, FB('m'), SUBT(TK)))], 'ssrdv', '%s C_ %s' % (FB('m'), SUBT(TK)))
    # fsumless into SUBT
    stf = sk([Lk(h[0]), sk([w.s([], 'ssrab2', '%s C_ G' % SUBT(TK))], 'a1i', '%s C_ G' % SUBT(TK))], 'ssfid', '%s e. Fin' % SUBT(TK))
    As = '( %s /\\ q e. %s )' % (Ak, SUBT(TK))
    qgs = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (As, SUBT(TK))), w.inst('elrabi')], 'syl', '( %s -> q e. G )' % As)
    wsr, wsg = d['wreal'](As, w.s([], 'simpll', '( %s -> ph )' % As), qgs)
    le1 = sk([stf, wsr, wsg, fbs], 'fsumless', 'sum_ q e. %s W <_ sum_ q e. %s W' % (FB('m'), SUBT(TK)))
    # the square hypothesis at t = TK
    H5 = BXH[4]
    body5 = ante_of(H5)[1]
    al5 = s([h[4]], 'ralrimiva', 'A. t e. RR %s' % body5)
    b5k = tsub(body5, {'t': TK})
    eqt = w.wcongr(body5, {'t': TK}, 't = %s' % TK, {'t': w.s([], 'id', '( t = %s -> t = %s )' % (TK, TK))})[0]
    h5k = sk([eqt, Lk(al5), tkr], 'rspcdva', b5k)
    # K log ( A ( abs TK + 2 ) ) <_ K ( 2 log ( A ( T + 2 ) ) )
    ATK = '( abs ` %s )' % TK
    atk = sk([sk([tkr], 'recnd', '%s e. CC' % TK)], 'abscld', '%s e. RR' % ATK)
    lvk = {'m': kr_, FT: Lk(d['ftr']), 'T': Lk(tr)}
    B_ = '( T + ( 1 / 2 ) )'
    abk = sk([sk([lin8(w, Ak, [klo, Lk(d['ftle'])], '-u %s <_ %s' % (B_, TK), lvk), lin8(w, Ak, [khi, Lk(d['ftle'])], '%s <_ %s' % (TK, B_), lvk)], 'jca', '( -u %s <_ %s /\\ %s <_ %s )' % (B_, TK, TK, B_)),
              sk([tkr, sk([Lk(tr), numst(w, Ak, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % B_)], 'absled', '( %s <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (ATK, B_, B_, TK, TK, B_))],
             'mpbird', '%s <_ %s' % (ATK, B_))
    X1 = '( A x. ( %s + 2 ) )' % ATK
    X2 = '( 2 x. ( A x. ( T + 2 ) ) )'
    lva = {'A': Lk(ar), 'T': Lk(tr), ATK: atk}
    hA1 = sk([Lk(ar), sk([sk([Lk(tr), numst(w, Ak, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % B_), atk], 'resubcld', '( %s - %s ) e. RR' % (B_, ATK)),
              lin8(w, Ak, [Lk(a1)], '0 <_ A', lva), lin8(w, Ak, [abk], '0 <_ ( %s - %s )' % (B_, ATK), lva)], 'mulge0d', '0 <_ ( A x. ( %s - %s ) )' % (B_, ATK))
    hA2 = sk([Lk(ar), Lk(tr), lin8(w, Ak, [Lk(a1)], '0 <_ A', lva), lin8(w, Ak, [Lk(t1)], '0 <_ T', lva)], 'mulge0d', '0 <_ ( A x. T )')
    import cl as _cl
    c = _cl.Closure(w, Ak, lva)
    for k_ in lva:
        c.atom(k_)
    x12 = lin.linarith(w, Ak, [hA1, hA2, Lk(a1)], '%s <_ %s' % (X1, X2), closure=c, products=True)
    x1p = sk([c.mem(X1, 'RR'), lin.linarith(w, Ak, [Lk(a1), sk([sk([tkr], 'recnd', '%s e. CC' % TK)], 'absge0d', '0 <_ %s' % ATK),
                                                   sk([Lk(ar), atk, lin8(w, Ak, [Lk(a1)], '0 <_ A', lva), sk([sk([tkr], 'recnd', '%s e. CC' % TK)], 'absge0d', '0 <_ %s' % ATK)], 'mulge0d', '0 <_ ( A x. %s )' % ATK)],
                                         '0 < %s' % X1, closure=c, products=True)], 'elrpd', '%s e. RR+' % X1)
    AT2 = '( A x. ( T + 2 ) )'
    at2p = sk([c.mem(AT2, 'RR'), lin.linarith(w, Ak, [Lk(a1), Lk(t1), hA2], '0 < %s' % AT2, closure=c, products=True)], 'elrpd', '%s e. RR+' % AT2)
    x2p = sk([numst(w, Ak, '2', 'RR+'), at2p], 'rpmulcld', '%s e. RR+' % X2)
    lx = sk([x12, sk([x1p, x2p], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (X1, X2, X1, X2))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (X1, X2))
    lm = sk([numst(w, Ak, '2', 'RR+'), at2p], 'relogmuld', '( log ` %s ) = ( ( log ` 2 ) + %s )' % (X2, L_))
    a3 = lin.linarith(w, Ak, [Lk(a1), Lk(t1), hA2], '2 <_ %s' % AT2, closure=c, products=True)
    l2a = sk([a3, sk([numst(w, Ak, '2', 'RR+'), at2p], 'logled', '( 2 <_ %s <-> ( log ` 2 ) <_ %s )' % (AT2, L_))], 'mpbid', '( log ` 2 ) <_ %s' % L_)
    lvl = {'( log ` %s )' % X1: sk([x1p], 'relogcld', '( log ` %s ) e. RR' % X1), '( log ` %s )' % X2: sk([x2p], 'relogcld', '( log ` %s ) e. RR' % X2),
           '( log ` 2 )': sk([numst(w, Ak, '2', 'RR+')], 'relogcld', '( log ` 2 ) e. RR'), L_: sk([at2p], 'relogcld', '%s e. RR' % L_)}
    ll = lin8(w, Ak, [lx, lm, l2a], '( log ` %s ) <_ ( 2 x. %s )' % (X1, L_), lvl)
    kl = sk([lvl['( log ` %s )' % X1], sk([numst(w, Ak, '2', 'RR'), lvl[L_]], 'remulcld', '( 2 x. %s ) e. RR' % L_), Lk(kr), Lk(d['k0']), ll], 'lemul2ad',
            '( K x. ( log ` %s ) ) <_ %s' % (X1, QB))
    # chain for the fibre
    Afb = '( %s /\\ q e. %s )' % (Ak, FB('m'))
    qg2 = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Afb, FB('m'))), w.inst('elrabi')], 'syl', '( %s -> q e. G )' % Afb)
    wfr, _ = d['wreal'](Afb, w.s([], 'simpll', '( %s -> ph )' % Afb), qg2)
    sfb = sk([Lk(h[0]) and d['fbf'], wfr], 'fsumrecl', 'sum_ q e. %s W e. RR' % FB('m'))
    sst = sk([stf, wsr], 'fsumrecl', 'sum_ q e. %s W e. RR' % SUBT(TK))
    KX = '( K x. ( log ` %s ) )' % X1
    qbr = sk([Lk(kr), sk([numst(w, Ak, '2', 'RR'), lvl[L_]], 'remulcld', '( 2 x. %s ) e. RR' % L_)], 'remulcld', '%s e. RR' % QB)
    st1 = sk([sst, sk([Lk(kr), lvl['( log ` %s )' % X1]], 'remulcld', '%s e. RR' % KX), qbr, h5k, kl], 'letrd', 'sum_ q e. %s W <_ %s' % (SUBT(TK), QB))
    fbq = sk([sfb, sst, qbr, le1, st1], 'letrd', 'sum_ q e. %s W <_ %s' % (FB('m'), QB))
    # (e) sum over I
    tot = s([d['ifin'], sfb, qbr, fbq], 'fsumle', 'sum_ m e. %s sum_ q e. %s W <_ sum_ m e. %s %s' % (I, FB('m'), I, QB))
    return w, d, dict(tot=tot, qbr=qbr, lvl=lvl, at2p=at2p)


def gen_boxcnt_final():
    w, d, e = gen_boxcnt_full()
    h, s = d['h'], d['s']
    tr, t1, kr, k0, ar, a1 = d['tr'], d['t1'], d['kr'], d['k0'], d['ar'], d['a1']
    FT, LO, I = d['FT'], d['LO'], d['I']
    # QB e. RR in ph context
    at2 = '( A x. ( T + 2 ) )'
    lva = {'A': ar, 'T': tr}
    import cl as _cl
    c = _cl.Closure(w, 'ph', lva)
    for k_ in lva:
        c.atom(k_)
    hA2 = s([ar, tr, lin8(w, 'ph', [a1], '0 <_ A', lva), lin8(w, 'ph', [t1], '0 <_ T', lva)], 'mulge0d', '0 <_ ( A x. T )')
    at2p = s([c.mem(at2, 'RR'), lin.linarith(w, 'ph', [a1, t1, hA2], '0 < %s' % at2, closure=c, products=True)], 'elrpd', '%s e. RR+' % at2)
    lr = s([at2p], 'relogcld', '%s e. RR' % L_)
    l0 = s([c.mem(at2, 'RR'), lin.linarith(w, 'ph', [a1, t1, hA2], '1 <_ %s' % at2, closure=c, products=True), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L_)
    qbr = s([kr, s([numst(w, 'ph', '2', 'RR'), lr], 'remulcld', '( 2 x. %s ) e. RR' % L_)], 'remulcld', '%s e. RR' % QB)
    qb0 = s([kr, s([numst(w, 'ph', '2', 'RR'), lr], 'remulcld', '( 2 x. %s ) e. RR' % L_), k0, s([numst(w, 'ph', '2', 'RR'), lr, numst(w, 'ph', '2', 'ge0'), l0], 'mulge0d', '0 <_ ( 2 x. %s )' % L_)],
            'mulge0d', '0 <_ %s' % QB)
    fc = s([d['ifin'], s([qbr], 'recnd', '%s e. CC' % QB)], 'fsumconst', 'sum_ m e. %s %s = ( ( # ` %s ) x. %s )' % (I, QB, I, QB)) if False else \
        s([s([d['ifin'], s([qbr], 'recnd', '%s e. CC' % QB)], 'jca', '( %s e. Fin /\\ %s e. CC )' % (I, QB)), w.inst('fsumconst')], 'syl', 'sum_ m e. %s %s = ( ( # ` %s ) x. %s )' % (I, QB, I, QB))
    # # I = ( FT - LO ) + 1 <_ 4 T
    ft1 = s([t1, s([tr, s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('flge')], 'syl2anc', '( 1 <_ T <-> 1 <_ %s )' % FT)], 'mpbid', '1 <_ %s' % FT)
    lvf = {FT: d['ftr'], 'T': tr}
    uz = s([s([d['loz'], d['ftz'], lin8(w, 'ph', [ft1], '%s <_ %s' % (LO, FT), lvf)], '3jca', '( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s )' % (LO, FT, LO, FT)),
            w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (FT, LO, LO, FT, LO, FT))], 'sylibr', '%s e. ( ZZ>= ` %s )' % (FT, LO))
    hf = s([uz, w.inst('hashfz')], 'syl', '( # ` %s ) = ( ( %s - %s ) + 1 )' % (I, FT, LO))
    HI = '( # ` %s )' % I
    hir = s([s([s([d['ftz'], d['loz']], 'zsubcld', '( %s - %s ) e. ZZ' % (FT, LO)), s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')], 'zaddcld', '( ( %s - %s ) + 1 ) e. ZZ' % (FT, LO))], 'zred',
            '( ( %s - %s ) + 1 ) e. RR' % (FT, LO))
    hir = s([hf, hir], 'eqeltrrd' if False else 'eqeltrd', '%s e. RR' % HI) if False else s([s([hf], 'eqcomd', '( ( %s - %s ) + 1 ) = %s' % (FT, LO, HI)), hir], 'eqeltrrd', '%s e. RR' % HI)
    lvh = {FT: d['ftr'], 'T': tr, HI: hir}
    h4 = lin8(w, 'ph', [hf, d['ftle'], t1], '%s <_ ( 4 x. T )' % HI, lvh)
    m = s([hir, s([numst(w, 'ph', '4', 'RR'), tr], 'remulcld', '( 4 x. T ) e. RR'), qbr, qb0, h4], 'lemul1ad', '( %s x. %s ) <_ ( ( 4 x. T ) x. %s )' % (HI, QB, QB))
    SGK = 'sum_ m e. %s sum_ q e. %s W' % (I, d['FB']('m'))
    Ak = d['Ak']
    Afb = '( %s /\\ q e. %s )' % (Ak, d['FB']('m'))
    qg2 = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Afb, d['FB']('m'))), w.inst('elrabi')], 'syl', '( %s -> q e. G )' % Afb)
    wfr, _ = d['wreal'](Afb, w.s([], 'simpll', '( %s -> ph )' % Afb), qg2)
    sfb = w.s([d['fbf'], wfr], 'fsumrecl', '( %s -> sum_ q e. %s W e. RR )' % (Ak, d['FB']('m')))
    sgr = s([d['ifin'], sfb], 'fsumrecl', '%s e. RR' % SGK)
    sq_ = s([d['ifin'], lift(w, qbr, Ak)], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (I, QB))
    t2 = s([e['tot'], fc], 'breqtrd', '%s <_ ( %s x. %s )' % (SGK, HI, QB))
    t3 = s([sgr, s([hir, qbr], 'remulcld', '( %s x. %s ) e. RR' % (HI, QB)), s([s([numst(w, 'ph', '4', 'RR'), tr], 'remulcld', '( 4 x. T ) e. RR'), qbr], 'remulcld', '( ( 4 x. T ) x. %s ) e. RR' % QB), t2, m],
           'letrd', '%s <_ ( ( 4 x. T ) x. %s )' % (SGK, QB))
    w.qed([d['sg'], t3], 'eqbrtrd', S['boxcnt'])
    return run8(w)


if __name__ == '__main__':
    gen_boxcnt_final()
