"""Sortie TP: Lean core_norm_bound (tpcore): the radius of ~ tprad, the order of ~ tpord, then ~ tpcore1 against ~ tpfin."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift, WIN, CN
import cl as _cl
import ef2lib as E
import mvlib
from z4blib import fvmd
from tp_k import DS

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()

def fvc(w, K, var, dom, body, arg, argin):
    """( K -> ( ( var e. dom |-> body ) ` arg ) = body[arg] ) through the closed fvmpt (K may bind var)"""
    ida = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, arg, var, arg))
    cg, val = w.congr(body, {var: arg}, '%s = %s' % (var, arg), {var: ida})
    if val.startswith('if ( '):
        inner = val[len('if ( '):-2]
        # DS form: if ( RA <_ IA , IA , RA )
        parts = inner.split(' , ')
        a_, b_ = parts[-2], parts[-1]
        ex = w.s([w.s([], 'fvex', '%s e. _V' % a_), w.s([], 'fvex', '%s e. _V' % b_)], 'ifex', '%s e. _V' % val)
    else:
        ex = w.s([], 'fvex', '%s e. _V' % val)
    mp = '( %s e. %s |-> %s )' % (var, dom, body)
    st = w.s([cg, w.s([], 'eqid', '%s = %s' % (mp, mp)), ex], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (arg, dom, mp, arg, val))
    return w.s([argin, st], 'syl', '( %s -> ( %s ` %s ) = %s )' % (K, mp, arg, val))


X = '( 0 ..^ N )'
DEX = '( ( N - 1 ) / ( M + N ) )'
PSJ = lambda k: 'sum_ j e. %s ( ( V ` j ) ^ %s )' % (X, k)
CA = ('( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ ( V : %s --> CC /\\ A. r e. %s ( abs ` ( V ` r ) ) <_ 1 ) /\\ '
      '( J e. %s /\\ ( V ` J ) = 1 ) )' % (X, X, X))
S['tpcore'] = '( %s -> E. k e. %s %s <_ ( abs ` %s ) )' % (CA, WIN(), CN(), PSJ('k'))
tplib.S['tpcore'] = S['tpcore']


def gen_core():
    w = W('tpcore', 'Lean ` core_norm_bound ` : for nodes ` v_h ` of modulus <_ 1 with ` v_J = 1 ` and ` 2 <_ N ` , some power sum with exponent in '
               '` [ M + 1 , M + N ] ` has modulus at least ` ( N / ( 8 e ( M + N ) ) ) ^ N ` .')
    A0 = CA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( N e. NN /\\ 2 <_ N /\\ M e. NN0 )'); t2 = s([], 'simp2', '( V : %s --> CC /\\ A. r e. %s ( abs ` ( V ` r ) ) <_ 1 )' % (X, X))
    t3 = s([], 'simp3', '( J e. %s /\\ ( V ` J ) = 1 )' % X)
    nn = s([t1], 'simp1d', 'N e. NN'); n2 = s([t1], 'simp2d', '2 <_ N'); mm = s([t1], 'simp3d', 'M e. NN0')
    vf = s([t2], 'simpld', 'V : %s --> CC' % X); vb = s([t2], 'simprd', 'A. r e. %s ( abs ` ( V ` r ) ) <_ 1' % X)
    jn = s([t3], 'simpld', 'J e. %s' % X); vj1 = s([t3], 'simprd', '( V ` J ) = 1')
    c = Closure(w, A0, {'N': ('NN', nn), 'M': ('NN0', mm)})
    kp = lin.linarith(w, A0, [n2], '0 < ( N - 1 )', closure=c)
    c.have('( N - 1 )', 'gt0', kp)
    drp = c.mem(DEX, 'RR+')
    # ---- reindexing the power sums along a permutation s (context without the contradiction hypothesis)
    SF = 's : %s -1-1-onto-> %s' % (X, X)
    U = '( u e. %s |-> ( V ` ( s ` u ) ) )' % X
    R0 = '( ( %s /\\ %s ) /\\ k e. %s )' % (A0, SF, WIN())
    L0 = lambda st: _cl.lift(w, st, R0)
    sfr = w.s([], 'simplr', '( %s -> %s )' % (R0, SF))
    R0q = '( %s /\\ q e. %s )' % (R0, X)
    qx = w.s([], 'simpr', '( %s -> q e. %s )' % (R0q, X))
    sq = w.s([w.s([_cl.lift(w, sfr, R0q), w.inst('f1of')], 'syl', '( %s -> s : %s --> %s )' % (R0q, X, X)), qx], 'ffvelcdmd', '( %s -> ( s ` q ) e. %s )' % (R0q, X))
    vsq = w.s([_cl.lift(w, vf, R0q), sq], 'ffvelcdmd', '( %s -> ( V ` ( s ` q ) ) e. CC )' % R0q)
    kin = w.s([], 'simpr', '( %s -> k e. %s )' % (R0, WIN()))
    kle = w.s([kin, w.inst('elfzle1')], 'syl', '( %s -> ( M + 1 ) <_ k )' % R0)
    kzz = w.s([kin, w.inst('elfzelz')], 'syl', '( %s -> k e. ZZ )' % R0)
    ck = Closure(w, R0, {'M': ('NN0', L0(mm)), 'k': ('ZZ', kzz)})
    k0 = lin.linarith(w, R0, [kle, ck.ge0('M')], '0 <_ k', closure=ck)
    kn0 = w.s([w.s([kzz, k0], 'jca', '( %s -> ( k e. ZZ /\\ 0 <_ k ) )' % R0), w.inst('elnn0z')], 'sylibr', '( %s -> k e. NN0 )' % R0)
    uqv = fvmd(w, R0q, 'u', X, '( V ` ( s ` u ) )', 'q', qx, vsq)
    uq_k = w.s([uqv], 'oveq1d', '( %s -> ( ( %s ` q ) ^ k ) = ( ( V ` ( s ` q ) ) ^ k ) )' % (R0q, U))
    s1 = w.s([uq_k], 'sumeq2dv', '( %s -> sum_ q e. %s ( ( %s ` q ) ^ k ) = sum_ q e. %s ( ( V ` ( s ` q ) ) ^ k ) )' % (R0, X, U, X))
    idjs = w.s([], 'id', '( j = ( s ` q ) -> j = ( s ` q ) )')
    cgj, _ = w.congr('( ( V ` j ) ^ k )', {'j': '( s ` q )'}, 'j = ( s ` q )', {'j': idjs})
    R0j = '( %s /\\ j e. %s )' % (R0, X)
    vjc = w.s([w.s([_cl.lift(w, vf, R0j), w.s([], 'simpr', '( %s -> j e. %s )' % (R0j, X))], 'ffvelcdmd', '( %s -> ( V ` j ) e. CC )' % R0j), _cl.lift(w, kn0, R0j)],
              'expcld', '( %s -> ( ( V ` j ) ^ k ) e. CC )' % R0j)
    fo = w.s([cgj, w.s([w.s([], 'fzofi', '%s e. Fin' % X)], 'a1i', '( %s -> %s e. Fin )' % (R0, X)), sfr, w.s([], 'eqidd', '( %s -> ( s ` q ) = ( s ` q ) )' % R0q), vjc],
             'fsumf1o', '( %s -> %s = sum_ q e. %s ( ( V ` ( s ` q ) ) ^ k ) )' % (R0, PSJ('k'), X))
    reix = w.s([s1, fo], 'eqtr4d', '( %s -> sum_ q e. %s ( ( %s ` q ) ^ k ) = %s )' % (R0, X, U, PSJ('k')))
    # ---- the contradiction hypothesis, with a fresh quantifier letter
    NEGz = 'A. z e. %s -. %s <_ ( abs ` %s )' % (WIN(), CN(), PSJ('z'))
    B = '( %s /\\ %s )' % (A0, NEGz)
    sb = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (B, f))
    LB = lambda st: _cl.lift(w, st, B)
    # distances and the radius
    DSx = DS('( V ` x )')
    DF = '( x e. %s |-> %s )' % (X, DSx)
    Ax = '( %s /\\ x e. %s )' % (A0, X)
    vx = w.s([_cl.lift(w, vf, Ax), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, X))], 'ffvelcdmd', '( %s -> ( V ` x ) e. CC )' % Ax)
    cx = Closure(w, Ax, {'( V ` x )': ('CC', vx)}); cx.atom('( V ` x )')
    dff = s([cx.mem(DSx, 'RR'), w.s([], 'eqid', '%s = %s' % (DF, DF))], 'fmptd', '%s : %s --> RR' % (DF, X))
    BR = lambda r: '( ( %s / 4 ) ^ N ) <_ prod_ h e. %s ( abs ` ( %s - ( %s ` h ) ) )' % (DEX, X, r, DF)
    rad = apc(w, A0, 'tprad', 'E. r e. ( 0 [,] %s ) %s' % (DEX, BR('r')), c, facts=[nn, dff, drp])
    idrt = w.s([], 'id', '( r = t -> r = t )')
    cgrt, nrt = w.wcongr(BR('r'), {'r': 't'}, 'r = t', {'r': idrt})
    radt = s([rad, w.s([cgrt], 'cbvrexvw', '( E. r e. ( 0 [,] %s ) %s <-> E. t e. ( 0 [,] %s ) %s )' % (DEX, BR('r'), DEX, nrt))], 'sylib', 'E. t e. ( 0 [,] %s ) %s' % (DEX, nrt))
    T0 = '( %s /\\ t e. ( 0 [,] %s ) )' % (B, DEX)
    T1 = '( %s /\\ %s )' % (T0, BR('t'))
    s1_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (T1, f))
    L1 = lambda st: _cl.lift(w, st, T1)
    L0t = lambda st: _cl.lift(w, st, T0)
    c1 = Closure(w, T1, {'N': ('NN', L1(nn)), 'M': ('NN0', L1(mm))})
    c1.have('( N - 1 )', 'gt0', L1(kp))
    tin = w.s([], 'simpr', '( %s -> t e. ( 0 [,] %s ) )' % (T0, DEX))
    c0t = Closure(w, T0, {'N': ('NN', L0t(nn)), 'M': ('NN0', L0t(mm))}); c0t.have('( N - 1 )', 'gt0', L0t(kp))
    el = w.s([tin, w.s([w.s([], '0red', '( %s -> 0 e. RR )' % T0), c0t.mem(DEX, 'RR'), w.inst('elicc2')], 'syl2anc',
                       '( %s -> ( t e. ( 0 [,] %s ) <-> ( t e. RR /\\ 0 <_ t /\\ t <_ %s ) ) )' % (T0, DEX, DEX))], 'mpbid', '( %s -> ( t e. RR /\\ 0 <_ t /\\ t <_ %s ) )' % (T0, DEX))
    tr0 = w.s([el], 'simp1d', '( %s -> t e. RR )' % T0); tg0 = w.s([el], 'simp2d', '( %s -> 0 <_ t )' % T0); tle0 = w.s([el], 'simp3d', '( %s -> t <_ %s )' % (T0, DEX))
    tr = L1(tr0); tg = L1(tg0); tle = L1(tle0)
    c1.have('t', 'RR', tr); c0t.have('t', 'RR', tr0)
    # the product in the letter g, with the distances written out
    PG = 'prod_ g e. %s ( abs ` ( t - %s ) )' % (X, DS('( V ` g )'))
    idhg = w.s([], 'id', '( h = g -> h = g )')
    chg, _ = w.congr('( abs ` ( t - ( %s ` h ) ) )' % DF, {'h': 'g'}, 'h = g', {'h': idhg})
    cb1 = w.s([chg], 'cbvprodv', 'prod_ h e. %s ( abs ` ( t - ( %s ` h ) ) ) = prod_ g e. %s ( abs ` ( t - ( %s ` g ) ) )' % (X, DF, X, DF))
    T1g = '( %s /\\ g e. %s )' % (T1, X)
    gx = w.s([], 'simpr', '( %s -> g e. %s )' % (T1g, X))
    vg = w.s([_cl.lift(w, L1(vf), T1g), gx], 'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % T1g)
    cg_ = Closure(w, T1g, {'( V ` g )': ('CC', vg), 't': ('RR', _cl.lift(w, tr, T1g))}); cg_.atom('( V ` g )')
    dfg = fvc(w, T1g, 'x', X, DSx, 'g', gx)
    pe = w.s([w.s([w.s([dfg], 'oveq2d', '( %s -> ( t - ( %s ` g ) ) = ( t - %s ) )' % (T1g, DF, DS('( V ` g )')))], 'fveq2d',
                  '( %s -> ( abs ` ( t - ( %s ` g ) ) ) = ( abs ` ( t - %s ) ) )' % (T1g, DF, DS('( V ` g )')))], 'prodeq2dv',
             '( %s -> prod_ g e. %s ( abs ` ( t - ( %s ` g ) ) ) = %s )' % (T1, X, DF, PG))
    pge = s1_([s1_([w.s([], 'simpr', '( %s -> %s )' % (T1, BR('t'))), s1_([cb1], 'a1i', tplib.formula_of_step(w, cb1))], 'breqtrd',
                   '( ( %s / 4 ) ^ N ) <_ prod_ g e. %s ( abs ` ( t - ( %s ` g ) ) )' % (DEX, X, DF)), pe], 'breqtrd', '( ( %s / 4 ) ^ N ) <_ %s' % (DEX, PG))
    D4 = '( ( %s / 4 ) ^ N )' % DEX
    c1.have(D4, 'RR+', c1.mem(D4, 'RR+')); c1.atom(D4)
    pgr = s1_([s1_([w.s([], 'fzofi', '%s e. Fin' % X)], 'a1i', '%s e. Fin' % X), cg_.mem('( abs ` ( t - %s ) )' % DS('( V ` g )'), 'RR')], 'fprodrecl', '%s e. RR' % PG)
    c1.have(PG, 'RR', pgr); c1.atom(PG)
    pgp = lin.linarith(w, T1, [pge, c1.gt0(D4)], '0 < %s' % PG, closure=c1)
    # every distance differs from t
    T0q = '( ( %s /\\ q e. %s ) /\\ %s = t )' % (T0, X, DS('( V ` q )'))
    qx0 = w.s([], 'simplr', '( %s -> q e. %s )' % (T0q, X))
    T0qg = '( %s /\\ g e. %s )' % (T0q, X)
    vgq = w.s([_cl.lift(w, L0t(vf), T0qg), w.s([], 'simpr', '( %s -> g e. %s )' % (T0qg, X))], 'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % T0qg)
    cgq = Closure(w, T0qg, {'( V ` g )': ('CC', vgq), 't': ('RR', _cl.lift(w, tr0, T0qg))}); cgq.atom('( V ` g )')
    T0qe = '( %s /\\ g = q )' % T0q
    idgq = w.s([], 'id', '( g = q -> g = q )')
    cgqq, _ = w.congr('( abs ` ( t - %s ) )' % DS('( V ` g )'), {'g': 'q'}, 'g = q', {'g': idgq})
    e1 = w.s([w.s([], 'simpr', '( %s -> g = q )' % T0qe), cgqq], 'syl', '( %s -> ( abs ` ( t - %s ) ) = ( abs ` ( t - %s ) ) )' % (T0qe, DS('( V ` g )'), DS('( V ` q )')))
    e2 = w.s([w.s([_cl.lift(w, w.s([], 'simpr', '( %s -> %s = t )' % (T0q, DS('( V ` q )'))), T0qe)], 'oveq2d', '( %s -> ( t - %s ) = ( t - t ) )' % (T0qe, DS('( V ` q )')))], 'fveq2d',
                  '( %s -> ( abs ` ( t - %s ) ) = ( abs ` ( t - t ) ) )' % (T0qe, DS('( V ` q )')))
    ct_ = Closure(w, T0qe, {'t': ('RR', _cl.lift(w, tr0, T0qe))})
    e3 = w.s([w.s([ap(w, T0qe, 'subidd', '( t - t ) = 0', ct_)], 'fveq2d', '( %s -> ( abs ` ( t - t ) ) = ( abs ` 0 ) )' % T0qe),
              w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % T0qe)], 'eqtrd', '( %s -> ( abs ` ( t - t ) ) = 0 )' % T0qe)
    e4 = w.s([e1, e2, e3], '3eqtrd', '( %s -> ( abs ` ( t - %s ) ) = 0 )' % (T0qe, DS('( V ` g )')))
    pz = w.s([w.s([], 'nfv', 'F/ g %s' % T0q), w.s([w.s([], 'fzofi', '%s e. Fin' % X)], 'a1i', '( %s -> %s e. Fin )' % (T0q, X)),
              cgq.mem('( abs ` ( t - %s ) )' % DS('( V ` g )'), 'CC'), qx0, e4], 'fprodeq0g', '( %s -> %s = 0 )' % (T0q, PG))
    pzi = w.s([pz], 'ex', '( ( %s /\\ q e. %s ) -> ( %s = t -> %s = 0 ) )' % (T0, X, DS('( V ` q )'), PG))
    T1q = '( %s /\\ q e. %s )' % (T1, X)
    t1t0 = w.s([w.s([_cl.lift(w, w.s([], 'simpl', '( %s -> %s )' % (T1, T0)), T1q), w.s([], 'simpr', '( %s -> q e. %s )' % (T1q, X))], 'jca',
                    '( %s -> ( %s /\\ q e. %s ) )' % (T1q, T0, X)), pzi], 'syl', '( %s -> ( %s = t -> %s = 0 ) )' % (T1q, DS('( V ` q )'), PG))
    pgn = w.s([_cl.lift(w, pgp, T1q)], 'gt0ne0d', '( %s -> %s =/= 0 )' % (T1q, PG))
    nq = w.s([pgn, w.s([t1t0], 'necon3ad', '( %s -> ( %s =/= 0 -> -. %s = t ) )' % (T1q, PG, DS('( V ` q )')))], 'mpd', '( %s -> -. %s = t )' % (T1q, DS('( V ` q )')))
    nq = w.s([nq], 'neqned', '( %s -> %s =/= t )' % (T1q, DS('( V ` q )')))
    alln = w.s([nq], 'ralrimiva', '( %s -> A. q e. %s %s =/= t )' % (T1, X, DS('( V ` q )')))
    # t > 0: the node V_J = 1 has distance 0
    VJ = '( V ` J )'
    idqJ = w.s([], 'id', '( q = J -> q = J )')
    cqJ, nqJ = w.wcongr('%s =/= t' % DS('( V ` q )'), {'q': 'J'}, 'q = J', {'q': idqJ})
    dJ = s1_([L1(jn), alln, w.s([cqJ], 'rspcv', '( J e. %s -> ( A. q e. %s %s =/= t -> %s ) )' % (X, X, DS('( V ` q )'), nqJ))], 'sylc', nqJ)
    d1 = s([s([vj1], 'oveq1d', '( %s - 1 ) = ( 1 - 1 )' % VJ), s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( 1 - 1 ) = 0')], 'eqtrd', '( %s - 1 ) = 0' % VJ)
    RAJ = '( abs ` ( Re ` ( %s - 1 ) ) )' % VJ; IAJ = '( abs ` ( Im ` ( %s - 1 ) ) )' % VJ
    ra_ = s([s([s([s([d1], 'fveq2d', '( Re ` ( %s - 1 ) ) = ( Re ` 0 )' % VJ), s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( Re ` 0 ) = 0')], 'eqtrd', '( Re ` ( %s - 1 ) ) = 0' % VJ)],
                'fveq2d', '%s = ( abs ` 0 )' % RAJ), s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '%s = 0' % RAJ)
    ia_ = s([s([s([s([d1], 'fveq2d', '( Im ` ( %s - 1 ) ) = ( Im ` 0 )' % VJ), s([w.s([], 'im0', '( Im ` 0 ) = 0')], 'a1i', '( Im ` 0 ) = 0')], 'eqtrd', '( Im ` ( %s - 1 ) ) = 0' % VJ)],
                'fveq2d', '%s = ( abs ` 0 )' % IAJ), s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '%s = 0' % IAJ)
    dz = s([s([s([ra_, ia_], 'breq12d', '( %s <_ %s <-> 0 <_ 0 )' % (RAJ, IAJ)), ia_, ra_], 'ifbieq12d', '%s = if ( 0 <_ 0 , 0 , 0 )' % DS(VJ)),
            s([w.s([], 'ifid', 'if ( 0 <_ 0 , 0 , 0 ) = 0')], 'a1i', 'if ( 0 <_ 0 , 0 , 0 ) = 0')], 'eqtrd', '%s = 0' % DS(VJ))
    t0n = s1_([L1(dz), dJ], 'eqnetrrd', '0 =/= t')
    tp = s1_([s1_([t0n], 'necomd', 't =/= 0'), ap(w, T1, 'leltned', '( 0 < t <-> t =/= 0 )', c1, facts=[tg])], 'mpbird', '0 < t')
    c1.have('t', 'gt0', tp)
    # the factors | t - d_x | as a map to RR+
    DSp = DS('( V ` p )')
    FF = '( p e. %s |-> ( abs ` ( t - %s ) ) )' % (X, DSp)
    T1x = '( %s /\\ p e. %s )' % (T1, X)
    xx = w.s([], 'simpr', '( %s -> p e. %s )' % (T1x, X))
    vxx = w.s([_cl.lift(w, L1(vf), T1x), xx], 'ffvelcdmd', '( %s -> ( V ` p ) e. CC )' % T1x)
    cxx = Closure(w, T1x, {'( V ` p )': ('CC', vxx), 't': ('RR', _cl.lift(w, tr, T1x))}); cxx.atom('( V ` p )')
    idqx = w.s([], 'id', '( q = p -> q = p )')
    cqx, nqx = w.wcongr('%s =/= t' % DS('( V ` q )'), {'q': 'p'}, 'q = p', {'q': idqx})
    dxt = w.s([xx, _cl.lift(w, alln, T1x), w.s([cqx], 'rspcv', '( p e. %s -> ( A. q e. %s %s =/= t -> %s ) )' % (X, X, DS('( V ` q )'), nqx))], 'sylc', '( %s -> %s )' % (T1x, nqx))
    cxx.have('( t - %s )' % DSp, 'ne0', ap(w, T1x, 'subne0d', '( t - %s ) =/= 0' % DSp, cxx, facts=[w.s([dxt], 'necomd', '( %s -> t =/= %s )' % (T1x, DSp))]))
    ffr = s1_([ap(w, T1x, 'absrpcld', '( abs ` ( t - %s ) ) e. RR+' % DSp, cxx), w.s([], 'eqid', '%s = %s' % (FF, FF))], 'fmptd', '%s : %s --> RR+' % (FF, X))
    # C ^ N <_ prod_ y ( FF ` y )
    T1y = '( %s /\\ y e. %s )' % (T1, X)
    yx = w.s([], 'simpr', '( %s -> y e. %s )' % (T1y, X))
    vy = w.s([_cl.lift(w, L1(vf), T1y), yx], 'ffvelcdmd', '( %s -> ( V ` y ) e. CC )' % T1y)
    cy = Closure(w, T1y, {'( V ` y )': ('CC', vy), 't': ('RR', _cl.lift(w, tr, T1y))}); cy.atom('( V ` y )')
    ffy = fvc(w, T1y, 'p', X, '( abs ` ( t - %s ) )' % DSp, 'y', yx)
    py = s1_([ffy], 'prodeq2dv', 'prod_ y e. %s ( %s ` y ) = prod_ y e. %s ( abs ` ( t - %s ) )' % (X, FF, X, DS('( V ` y )')))
    idyg = w.s([], 'id', '( y = g -> y = g )')
    cyg, _ = w.congr('( abs ` ( t - %s ) )' % DS('( V ` y )'), {'y': 'g'}, 'y = g', {'y': idyg})
    cb2 = w.s([cyg], 'cbvprodv', 'prod_ y e. %s ( abs ` ( t - %s ) ) = %s' % (X, DS('( V ` y )'), PG))
    pyg = s1_([py, s1_([cb2], 'a1i', tplib.formula_of_step(w, cb2))], 'eqtrd', 'prod_ y e. %s ( %s ` y ) = %s' % (X, FF, PG))
    C4 = '( %s / 4 )' % DEX
    hyp = s1_([pge, pyg], 'breqtrrd', '( %s ^ N ) <_ prod_ y e. %s ( %s ` y )' % (C4, X, FF))
    ORD = tsub(stmt('tpord'), {'F': FF, 'C': C4})
    oa, oc = ante_of(ORD)
    have = {'N e. NN0': c1.mem('N', 'NN0'), '%s : %s --> RR+' % (FF, X): ffr, '%s e. RR+' % C4: c1.mem(C4, 'RR+'), body_of(w, hyp): hyp}
    ordst = s1_([conj(w, T1, oa, have), w.inst('tpord')], 'syl', oc)
    ALLI = oc.split(' /\\ ', 1)[1][:-2]
    # ---- under the permutation s
    S1 = '( %s /\\ ( %s /\\ %s ) )' % (T1, SF, ALLI)
    ss_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (S1, f))
    LS = lambda st: _cl.lift(w, st, S1)
    sfs = w.s([], 'simprl', '( %s -> %s )' % (S1, SF)); alli = w.s([], 'simprr', '( %s -> %s )' % (S1, ALLI))
    sff = ss_([sfs, w.inst('f1of')], 'syl', 's : %s --> %s' % (X, X))
    cs = Closure(w, S1, {'N': ('NN', LS(L1(nn))), 'M': ('NN0', LS(L1(mm))), 't': ('RR', LS(tr))})
    cs.have('( N - 1 )', 'gt0', LS(L1(kp))); cs.have('t', 'gt0', LS(tp))
    def at_s(K, zv, zin):
        """( K -> ( s ` zv ) e. X ), ( K -> ( U ` zv ) = ( V ` ( s ` zv ) ) ), ( K -> ( V ` ( s ` zv ) ) e. CC )"""
        szx = w.s([_cl.lift(w, sff, K), zin], 'ffvelcdmd', '( %s -> ( s ` %s ) e. %s )' % (K, zv, X))
        vsz = w.s([_cl.lift(w, LS(L1(vf)), K), szx], 'ffvelcdmd', '( %s -> ( V ` ( s ` %s ) ) e. CC )' % (K, zv))
        uz = fvc(w, K, 'u', X, '( V ` ( s ` u ) )', zv, zin) if zv != 'u' else None
        return szx, uz, vsz
    # U : X --> CC
    S1x = '( %s /\\ u e. %s )' % (S1, X)
    _, _, vsx = at_s(S1x, 'u', w.s([], 'simpr', '( %s -> u e. %s )' % (S1x, X)))
    uf = ss_([vsx, w.s([], 'eqid', '%s = %s' % (U, U))], 'fmptd', '%s : %s --> CC' % (U, X))
    # abs U_r <_ 1
    idrz = w.s([], 'id', '( r = w -> r = w )')
    crz, nrz = w.wcongr('( abs ` ( V ` r ) ) <_ 1', {'r': 'w'}, 'r = w', {'r': idrz})
    vbw = ss_([LS(L1(vb)), w.s([crz], 'cbvralvw', '( A. r e. %s ( abs ` ( V ` r ) ) <_ 1 <-> A. w e. %s %s )' % (X, X, nrz))], 'sylib', 'A. w e. %s %s' % (X, nrz))
    S1r = '( %s /\\ f e. %s )' % (S1, X)
    rin = w.s([], 'simpr', '( %s -> f e. %s )' % (S1r, X))
    srx, ur, vsr = at_s(S1r, 'f', rin)
    idws = w.s([], 'id', '( w = ( s ` f ) -> w = ( s ` f ) )')
    cws, nws = w.wcongr(nrz, {'w': '( s ` f )'}, 'w = ( s ` f )', {'w': idws})
    vsrb = w.s([srx, _cl.lift(w, vbw, S1r), w.s([cws], 'rspcv', '( ( s ` f ) e. %s -> ( A. w e. %s %s -> %s ) )' % (X, X, nrz, nws))], 'sylc', '( %s -> %s )' % (S1r, nws))
    urb = w.s([w.s([ur], 'fveq2d', '( %s -> ( abs ` ( %s ` f ) ) = ( abs ` ( V ` ( s ` f ) ) ) )' % (S1r, U)), vsrb], 'eqbrtrd', '( %s -> ( abs ` ( %s ` f ) ) <_ 1 )' % (S1r, U))
    ubf = w.s([urb], 'ralrimiva', '( %s -> A. f e. %s ( abs ` ( %s ` f ) ) <_ 1 )' % (S1, X, U))
    idfr = w.s([], 'id', '( f = r -> f = r )')
    cfr, nfr = w.wcongr('( abs ` ( %s ` f ) ) <_ 1' % U, {'f': 'r'}, 'f = r', {'f': idfr})
    ub = ss_([ubf, w.s([cfr], 'cbvralvw', '( A. f e. %s ( abs ` ( %s ` f ) ) <_ 1 <-> A. r e. %s %s )' % (X, U, X, nfr))], 'sylib', 'A. r e. %s %s' % (X, nfr))
    # the node J' = `' s ` J
    JP = "( `' s ` J )"
    jp = ss_([sfs, LS(L1(jn)), w.inst('f1ocnvdm')], 'syl2anc', '%s e. %s' % (JP, X))
    sjp = ss_([sfs, LS(L1(jn)), w.inst('f1ocnvfv2')], 'syl2anc', '( s ` %s ) = J' % JP)
    ujp = fvc(w, S1, 'u', X, '( V ` ( s ` u ) )', JP, jp)
    uj1 = ss_([ujp, ss_([sjp], 'fveq2d', '( V ` ( s ` %s ) ) = ( V ` J )' % JP), LS(L1(vj1))], '3eqtrd', '( %s ` %s ) = 1' % (U, JP))
    # distances of U differ from t
    idqw = w.s([], 'id', '( q = w -> q = w )')
    cqw, nqw = w.wcongr('%s =/= t' % DS('( V ` q )'), {'q': 'w'}, 'q = w', {'q': idqw})
    allw = ss_([LS(alln), w.s([cqw], 'cbvralvw', '( A. q e. %s %s =/= t <-> A. w e. %s %s )' % (X, DS('( V ` q )'), X, nqw))], 'sylib', 'A. w e. %s %s' % (X, nqw))
    S1q = '( %s /\\ q e. %s )' % (S1, X)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (S1q, X))
    sqx, uq, vsq_ = at_s(S1q, 'q', qin)
    cwq, nwq = w.wcongr(nqw, {'w': '( s ` q )'}, 'w = ( s ` q )', {'w': w.s([], 'id', '( w = ( s ` q ) -> w = ( s ` q ) )')})
    dsq = w.s([sqx, _cl.lift(w, allw, S1q), w.s([cwq], 'rspcv', '( ( s ` q ) e. %s -> ( A. w e. %s %s -> %s ) )' % (X, X, nqw, nwq))], 'sylc', '( %s -> %s )' % (S1q, nwq))
    rq, _ = w.rewrite(DS('( %s ` q )' % U), {'( %s ` q )' % U: ('( V ` ( s ` q ) )', uq)}, S1q)
    dsu = w.s([rq, dsq], 'eqnetrd', '( %s -> %s =/= t )' % (S1q, DS('( %s ` q )' % U)))
    alldu = w.s([dsu], 'ralrimiva', '( %s -> A. q e. %s %s =/= t )' % (S1, X, DS('( %s ` q )' % U)))
    # prefix products of U
    S1n = '( %s /\\ n e. %s )' % (S1, X)
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (S1n, X))
    idin = w.s([], 'id', '( i = n -> i = n )')
    ABODY = ALLI.split(' e. %s ' % X, 1)[1]
    cin, nin_ = w.wcongr(ABODY, {'i': 'n'}, 'i = n', {'i': idin})
    an = w.s([nin, _cl.lift(w, alli, S1n), w.s([cin], 'rspcv', '( n e. %s -> ( %s -> %s ) )' % (X, ALLI, nin_))], 'sylc', '( %s -> %s )' % (S1n, nin_))
    PH = 'prod_ h e. ( 0 ..^ ( n + 1 ) ) ( %s ` ( s ` h ) )' % FF
    PY = 'prod_ y e. ( 0 ..^ ( n + 1 ) ) ( abs ` ( t - %s ) )' % DS('( %s ` y )' % U)
    idhy = w.s([], 'id', '( h = y -> h = y )')
    chy, _ = w.congr('( %s ` ( s ` h ) )' % FF, {'h': 'y'}, 'h = y', {'h': idhy})
    cb3 = w.s([chy], 'cbvprodv', '%s = prod_ y e. ( 0 ..^ ( n + 1 ) ) ( %s ` ( s ` y ) )' % (PH, FF))
    S1ny = '( %s /\\ y e. ( 0 ..^ ( n + 1 ) ) )' % S1n
    nss = w.s([w.s([w.s([nin, w.inst('fzofzp1')], 'syl', '( %s -> ( n + 1 ) e. ( 0 ... N ) )' % S1n), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` ( n + 1 ) ) )' % S1n),
               w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ ( n + 1 ) ) C_ %s )' % (S1n, X))
    yX = w.s([_cl.lift(w, nss, S1ny), w.s([], 'simpr', '( %s -> y e. ( 0 ..^ ( n + 1 ) ) )' % S1ny)], 'sseldd', '( %s -> y e. %s )' % (S1ny, X))
    syx, uy, vsy = at_s(S1ny, 'y', yX)
    cny = Closure(w, S1ny, {'( V ` ( s ` y ) )': ('CC', vsy), 't': ('RR', _cl.lift(w, LS(tr), S1ny))}); cny.atom('( V ` ( s ` y ) )')
    ffs = fvc(w, S1ny, 'p', X, '( abs ` ( t - %s ) )' % DSp, '( s ` y )', syx)
    ry, _ = w.rewrite('( abs ` ( t - %s ) )' % DS('( %s ` y )' % U), {'( %s ` y )' % U: ('( V ` ( s ` y ) )', uy)}, S1ny)
    fy2 = w.s([ffs, ry], 'eqtr4d', '( %s -> ( %s ` ( s ` y ) ) = ( abs ` ( t - %s ) ) )' % (S1ny, FF, DS('( %s ` y )' % U)))
    pyy = w.s([fy2], 'prodeq2dv', '( %s -> prod_ y e. ( 0 ..^ ( n + 1 ) ) ( %s ` ( s ` y ) ) = %s )' % (S1n, FF, PY))
    pfu = w.s([an, w.s([w.s([cb3], 'a1i', '( %s -> %s = prod_ y e. ( 0 ..^ ( n + 1 ) ) ( %s ` ( s ` y ) ) )' % (S1n, PH, FF)), pyy], 'eqtrd',
                          '( %s -> %s = %s )' % (S1n, PH, PY))], 'breqtrd', '( %s -> ( %s ^ ( n + 1 ) ) <_ %s )' % (S1n, C4, PY))
    prefu = w.s([pfu], 'ralrimiva', '( %s -> A. n e. %s ( %s ^ ( n + 1 ) ) <_ %s )' % (S1, X, C4, PY))
    # window bound for U with C := CN
    S1k = '( %s /\\ k e. %s )' % (S1, WIN())
    kin2 = w.s([], 'simpr', '( %s -> k e. %s )' % (S1k, WIN()))
    a0S = _cl.lift(w, w.s([], 'simpl', '( %s -> %s )' % (B, A0)), S1k)
    toR0 = w.s([w.s([a0S, _cl.lift(w, sfs, S1k)], 'jca', '( %s -> ( %s /\\ %s ) )' % (S1k, A0, SF)), kin2], 'jca', '( %s -> %s )' % (S1k, R0))
    rk = w.s([toR0, reix], 'syl', '( %s -> sum_ q e. %s ( ( %s ` q ) ^ k ) = %s )' % (S1k, X, U, PSJ('k')))
    negz = _cl.lift(w, w.s([], 'simpr', '( %s -> %s )' % (B, NEGz)), S1k)
    idzk = w.s([], 'id', '( z = k -> z = k )')
    czk, nzk = w.wcongr('-. %s <_ ( abs ` %s )' % (CN(), PSJ('z')), {'z': 'k'}, 'z = k', {'z': idzk})
    nk = w.s([kin2, negz, w.s([czk], 'rspcv', '( k e. %s -> ( %s -> %s ) )' % (WIN(), NEGz, nzk))], 'sylc', '( %s -> %s )' % (S1k, nzk))
    ck2 = Closure(w, S1k, {'N': ('NN', _cl.lift(w, LS(L1(nn)), S1k)), 'M': ('NN0', _cl.lift(w, LS(L1(mm)), S1k))})
    PSk = PSJ('k')
    psc0 = w.s([w.s([w.s([], 'fzofi', '%s e. Fin' % X)], 'a1i', '( %s -> %s e. Fin )' % (R0, X)), vjc], 'fsumcl', '( %s -> %s e. CC )' % (R0, PSk))
    psc = w.s([toR0, psc0], 'syl', '( %s -> %s e. CC )' % (S1k, PSk))
    ck2.have('( abs ` %s )' % PSk, 'RR', w.s([psc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (S1k, PSk))); ck2.atom('( abs ` %s )' % PSk)
    cnr = ck2.mem(CN(), 'RR'); ck2.atom(CN())
    lt = w.s([nk, ap(w, S1k, 'ltnled', '( ( abs ` %s ) < %s <-> -. %s <_ ( abs ` %s ) )' % (PSk, CN(), CN(), PSk), ck2)], 'mpbird', '( %s -> ( abs ` %s ) < %s )' % (S1k, PSk, CN()))
    le = ap(w, S1k, 'ltled', '( abs ` %s ) <_ %s' % (PSk, CN()), ck2, facts=[lt])
    wk = w.s([w.s([w.s([rk], 'fveq2d', '( %s -> ( abs ` sum_ q e. %s ( ( %s ` q ) ^ k ) ) = ( abs ` %s ) )' % (S1k, X, U, PSk)), le], 'eqbrtrd',
                  '( %s -> ( abs ` sum_ q e. %s ( ( %s ` q ) ^ k ) ) <_ %s )' % (S1k, X, U, CN()))], 'ralrimiva',
              '( %s -> A. k e. %s ( abs ` sum_ q e. %s ( ( %s ` q ) ^ k ) ) <_ %s )' % (S1, WIN(), X, U, CN()))
    # tpcore1 and tpfin
    C1 = tsub(stmt('tpcore1'), {'D': DEX, 'V': U, 'J': JP, 'R': 't', 'C': CN()})
    c1a, c1c = ante_of(C1)
    cs.have(CN(), 'RR', cs.mem(CN(), 'RR'))
    have = {'( N e. NN /\\ 2 <_ N /\\ M e. NN0 )': LS(L1(t1)), '%s = %s' % (DEX, DEX): ss_([], 'eqidd', '%s = %s' % (DEX, DEX)),
            '%s : %s --> CC' % (U, X): uf, 'A. r e. %s ( abs ` ( %s ` r ) ) <_ 1' % (X, U): ub, '%s e. %s' % (JP, X): jp, '( %s ` %s ) = 1' % (U, JP): uj1,
            '( t e. RR /\\ 0 < t /\\ t <_ %s )' % DEX: ss_([LS(tr), LS(tp), LS(tle)], '3jca', '( t e. RR /\\ 0 < t /\\ t <_ %s )' % DEX),
            'A. q e. %s %s =/= t' % (X, DS('( %s ` q )' % U)): alldu, body_of(w, prefu): prefu,
            '( %s e. RR /\\ 0 <_ %s )' % (CN(), CN()): ss_([cs.mem(CN(), 'RR'), cs.ge0(CN())], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (CN(), CN())),
            body_of(w, wk): wk}
    core1 = ss_([conj(w, S1, c1a, have), w.inst('tpcore1')], 'syl', c1c)
    FIN = tsub(stmt('tpfin'), {'D': DEX})
    fa, fc = ante_of(FIN)
    fin = ss_([ss_([LS(L1(t1)), ss_([], 'eqidd', '%s = %s' % (DEX, DEX))], 'jca', fa), w.inst('tpfin')], 'syl', fc)
    QC = fc.rsplit(' < _pi', 1)[0]
    cs.have('_pi', 'RR', ss_([w.s([], 'pire', '_pi e. RR')], 'a1i', '_pi e. RR'))
    cs.atom(QC)
    G = '_pi < _pi'
    csq = Closure(w, S1, {'N': ('NN', LS(L1(nn))), 'M': ('NN0', LS(L1(mm)))}); csq.have('( N - 1 )', 'gt0', LS(L1(kp)))
    klt = lin.linarith(w, S1, [csq.ge0('M')], '( N - 1 ) < ( 1 x. ( M + N ) )', closure=csq)
    dlt = ss_([klt, ap(w, S1, 'ltdivmul2d', '( %s < 1 <-> ( N - 1 ) < ( 1 x. ( M + N ) ) )' % DEX, csq)], 'mpbird', '%s < 1' % DEX)
    csq.have('( 1 - %s )' % DEX, 'gt0', lin.linarith(w, S1, [dlt], '0 < ( 1 - %s )' % DEX, closure=csq))
    GTD = '( ( 2 ^ i ) x. ( ( 4 / %s ) ^ ( i + 1 ) ) )' % DEX
    Si = '( %s /\\ i e. %s )' % (T1, X)
    csi = Closure(w, Si, {'N': ('NN', _cl.lift(w, L1(nn), Si)), 'M': ('NN0', _cl.lift(w, L1(mm), Si)),
                          'i': ('NN0', w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (Si, X)), w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Si))})
    csi.have('( N - 1 )', 'gt0', _cl.lift(w, L1(kp), Si))
    gsr = LS(s1_([s1_([w.s([], 'fzofi', '%s e. Fin' % X)], 'a1i', '%s e. Fin' % X), csi.mem(GTD, 'RR')], 'fsumrecl', 'sum_ i e. %s %s e. RR' % (X, GTD)))
    csq.have('sum_ i e. %s %s' % (X, GTD), 'RR', gsr); csq.atom('sum_ i e. %s %s' % (X, GTD))
    ppi = ss_([cs.mem('_pi', 'RR'), csq.mem(QC, 'RR'), cs.mem('_pi', 'RR'), core1, fin], 'lelttrd', G)
    e1 = w.s([ppi], 'ex', '( %s -> ( ( %s /\\ %s ) -> %s ) )' % (T1, SF, ALLI, G))
    e2 = w.s([e1], 'exlimdv', '( %s -> ( E. s ( %s /\\ %s ) -> %s ) )' % (T1, SF, ALLI, G))
    e3 = w.s([ordst, e2], 'mpd', '( %s -> %s )' % (T1, G))
    e4 = w.s([e3], 'ex', '( %s -> ( %s -> %s ) )' % (T0, BR('t'), G))
    e5 = sb([e4], 'rexlimdva', '( E. t e. ( 0 [,] %s ) %s -> %s )' % (DEX, BR('t'), G))
    e6 = sb([LB(radt), e5], 'mpd', G)
    e7 = sb([sb([w.s([], 'pire', '_pi e. RR')], 'a1i', '_pi e. RR')], 'ltnrd', '-. %s' % G)
    nz = s([e6, e7], 'pm2.65da', '-. %s' % NEGz)
    NEGk = 'A. k e. %s -. %s <_ ( abs ` %s )' % (WIN(), CN(), PSJ('k'))
    idkz = w.s([], 'id', '( k = z -> k = z )')
    ckz, nkz = w.wcongr('-. %s <_ ( abs ` %s )' % (CN(), PSJ('k')), {'k': 'z'}, 'k = z', {'k': idkz})
    bi = w.s([ckz], 'cbvralvw', '( %s <-> %s )' % (NEGk, NEGz))
    nk_ = s([nz, bi], 'sylnibr', '-. %s' % NEGk)
    w.qed([nk_, w.s([], 'dfrex2', '( E. k e. %s %s <_ ( abs ` %s ) <-> -. %s )' % (WIN(), CN(), PSJ('k'), NEGk))], 'sylibr', S['tpcore'])
    return run(w)


if __name__ == '__main__':
    gen_core()
