"""Sortie EF56: the window functional of g at S <_ 5/8 (ef6pw: the zeros of g lie on Re = 1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef2lib import zs_unpack


def gen_pw():
    w = W('ef6pw', 'The zeros of ` g ` in the windows of Lean ` exists_good_sigma ` lie on ` Re = 1 ` ( ~ ef5g0 ), so at ` S <_ 5 / 8 ` none has real part ` S ` and the window functional of ` g ` is at most ` 2 ` times the total weight, ` <_ 2304000 log ^ 2 ( T + 4 ) ` ( ~ ef3sgw ).')
    A0 = ante_of(S['ef6pw'])[0]
    c = Ctx(w, A0)
    g = c.g
    tr = g('T e. RR'); t2 = g('2 <_ T'); pr = g('P e. RR'); mn = g('M e. NN0'); sr = g('S e. RR'); s58 = g('S <_ ( 5 / 8 )')
    Aj = '( %s /\\ j e. ( 0 ..^ M ) )' % A0
    cj = Ctx(w, Aj)
    jz = cj([cj([], 'simpr', 'j e. ( 0 ..^ M )'), w.inst('elfzoelz')], 'syl', 'j e. ZZ')
    jr = cj([jz], 'zred', 'j e. RR')
    CT_ = '( ( P + ( j / 2 ) ) + ( 1 / 4 ) )'
    ctr = cj([cj([lift(w, pr, Aj), cj([jr], 'rehalfcld', '( j / 2 ) e. RR')], 'readdcld', '( P + ( j / 2 ) ) e. RR'), numst(w, Aj, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % CT_)
    Z = ZK('j', 'P', GF)
    Aq = '( %s /\\ q e. %s )' % (Aj, Z)
    cq = Ctx(w, Aq)
    Lq = lambda st: lift(w, st, Aq)
    d = zs_unpack(w, Aq, GF, CT_, Lq(ctr), 'q', cq([], 'simpr', 'q e. %s' % Z))
    rq = '( Re ` q )'
    r0 = lin8(w, Aq, d['hy'], '0 < %s' % rq, d['lv'])
    qh = cq([cq([d['cc'], r0], 'jca', '( q e. CC /\\ 0 < %s )' % rq), cq([cq.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < %s ) )' % (HP0, rq))], 'mpbird', 'q e. %s' % HP0)
    g0 = cq([d['fz'], cq([qh, w.inst('ef5g0')], 'syl', tsub(S['ef5g0'], {'S': 'q'}).split(' -> ', 1)[1][:-2])], 'mpbid', 'E. n e. ZZ q = %s' % GFZ('n'))
    An = '( ( %s /\\ n e. ZZ ) /\\ q = %s )' % (Aq, GFZ('n'))
    cn = Ctx(w, An)
    nz = cn.g('n e. ZZ')
    TN = '( 2 x. ( _pi x. n ) )'
    imr = cn([cn([numst(w, An, '2', 'RR'), cn([cn.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR'), cn([nz], 'zred', 'n e. RR')], 'remulcld', '( _pi x. n ) e. RR')], 'remulcld', '%s e. RR' % TN),
              cn([numst(w, An, '2', 'RR'), cn.a1(w.s([], '1lt2', '1 < 2'), '1 < 2')], 'rplogcld', '( log ` 2 ) e. RR+')], 'rerpdivcld', '%s e. RR' % IMN('n'))
    re1n = cn([cn([cn.g('q = %s' % GFZ('n'))], 'fveq2d', '%s = ( Re ` %s )' % (rq, GFZ('n'))), cn([numst(w, An, '1', 'RR'), imr], 'crred', '( Re ` %s ) = 1' % GFZ('n'))], 'eqtrd', '%s = 1' % rq)
    re1 = cq([w.s([w.s([re1n], 'ex', '( ( %s /\\ n e. ZZ ) -> ( q = %s -> %s = 1 ) )' % (Aq, GFZ('n'), rq))], 'rexlimdva', '( %s -> ( E. n e. ZZ q = %s -> %s = 1 ) )' % (Aq, GFZ('n'), rq)), g0], 'x', 'x') if False else \
        cq([g0, w.s([w.s([re1n], 'ex', '( ( %s /\\ n e. ZZ ) -> ( q = %s -> %s = 1 ) )' % (Aq, GFZ('n'), rq))], 'rexlimdva', '( %s -> ( E. n e. ZZ q = %s -> %s = 1 ) )' % (Aq, GFZ('n'), rq))], 'mpd', '%s = 1' % rq)
    rqr = d['lv'][rq]
    lvs = {'S': Lq(sr), rq: rqr}
    rne = cq([cq([lin8(w, Aq, [re1, Lq(s58)], 'S < %s' % rq, lvs)], 'gtned', '%s =/= S' % rq)], 'idi', '%s =/= S' % rq)
    # the kernel is at most 2
    X = '( abs ` ( S - %s ) )' % rq
    dr = cq([Lq(sr), rqr], 'resubcld', '( S - %s ) e. RR' % rq)
    xr = cq([cq([dr], 'recnd', '( S - %s ) e. CC' % rq)], 'abscld', '%s e. RR' % X)
    x1 = cq([cq([rqr, Lq(sr)], 'resubcld', '( %s - S ) e. RR' % rq), w.inst('leabs')], 'syl', '( %s - S ) <_ ( abs ` ( %s - S ) )' % (rq, rq))
    x2 = cq([x1, cq([cq([rqr], 'recnd', '%s e. CC' % rq), cq([Lq(sr)], 'recnd', 'S e. CC')], 'abssubd', '( abs ` ( %s - S ) ) = %s' % (rq, X))], 'breqtrd', '( %s - S ) <_ %s' % (rq, X))
    x4 = lin8(w, Aq, [x2, re1, Lq(s58)], '( 1 / 4 ) <_ %s' % X, dict(lvs, **{X: xr}))
    xp = cq([xr, lin8(w, Aq, [x4], '0 < %s' % X, {X: xr})], 'elrpd', '%s e. RR+' % X)
    H = '( 1 / 2 )'
    q4 = '( 1 / 4 )'
    sq = cq([cq([numst(w, Aq, q4, 'RR'), xr, numst(w, Aq, H, 'RR')], '3jca', '( %s e. RR /\\ %s e. RR /\\ %s e. RR )' % (q4, X, H)),
             cq([lin8(w, Aq, [], '0 <_ %s' % q4, {}), lin8(w, Aq, [], '0 <_ %s' % H, {})], 'jca', '( 0 <_ %s /\\ 0 <_ %s )' % (q4, H)), x4], '3jca' if False else 'x', 'x') if False else None
    c2a = cq([cq([cq([numst(w, Aq, q4, 'RR'), xr, numst(w, Aq, H, 'RR')], '3jca', '( %s e. RR /\\ %s e. RR /\\ %s e. RR )' % (q4, X, H)),
                  cq([lin8(w, Aq, [], '0 <_ %s' % q4, {}), lin8(w, Aq, [], '0 <_ %s' % H, {})], 'jca', '( 0 <_ %s /\\ 0 <_ %s )' % (q4, H)), x4], '3jca',
              '( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( 0 <_ %s /\\ 0 <_ %s ) /\\ %s <_ %s )' % (q4, X, H, q4, H, q4, X)), w.inst('cxple2a')], 'syl', '( %s ^c %s ) <_ ( %s ^c %s )' % (q4, H, X, H))
    s14 = w.s([w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '0le1', '0 <_ 1')], 'pm3.2i', '( 1 e. RR /\\ 0 <_ 1 )'), w.s([w.s([], '4re', '4 e. RR'), w.s([], '4pos', '0 < 4')], 'elrpii', '4 e. RR+')], 'pm3.2i', '( ( 1 e. RR /\\ 0 <_ 1 ) /\\ 4 e. RR+ )'), w.inst('sqrtdiv')], 'ax-mp', '( sqrt ` ( 1 / 4 ) ) = ( ( sqrt ` 1 ) / ( sqrt ` 4 ) )')
    s14b = w.s([s14, w.s([w.s([], 'sqrt1', '( sqrt ` 1 ) = 1'), w.s([], 'sqrt4', '( sqrt ` 4 ) = 2')], 'oveq12i', '( ( sqrt ` 1 ) / ( sqrt ` 4 ) ) = ( 1 / 2 )')], 'eqtri', '( sqrt ` ( 1 / 4 ) ) = ( 1 / 2 )')
    q4h = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '4cn', '4 e. CC'), w.s([], '4ne0', '4 =/= 0')], 'divcli', '( 1 / 4 ) e. CC'), w.inst('cxpsqrt')], 'ax-mp', '( %s ^c %s ) = ( sqrt ` %s )' % (q4, H, q4)), s14b], 'eqtri', '( %s ^c %s ) = %s' % (q4, H, H))
    c2b = cq([cq.a1(w.s([q4h], 'eqcomi', '%s = ( %s ^c %s )' % (H, q4, H)), '%s = ( %s ^c %s )' % (H, q4, H)), c2a], 'eqbrtrd', '%s <_ ( %s ^c %s )' % (H, X, H))
    XH = '( %s ^c %s )' % (X, H)
    xhp = cq([xp, numst(w, Aq, H, 'RR')], 'rpcxpcld', '%s e. RR+' % XH)
    ng = cq([cq([xp], 'rpcnd', '%s e. CC' % X), cq([xp], 'rpne0d', '%s =/= 0' % X), numst(w, Aq, H, 'CC'), w.inst('cxpneg')], 'syl3anc', '( %s ^c -u %s ) = ( 1 / %s )' % (X, H, XH))
    hp = numst(w, Aq, H, 'RR+')
    rb = cq([hp, xhp, numst(w, Aq, '1', 'RR'), lin8(w, Aq, [], '0 <_ 1', {}), c2b], 'lediv2ad', '( 1 / %s ) <_ ( 1 / %s )' % (XH, H))
    two = cq.a1(w.s([w.s([], '2cn', '2 e. CC'), w.inst('recrec' if False else 'x')], 'x', 'x'), 'x') if False else cq.a1(w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'recreci', '( 1 / ( 1 / 2 ) ) = 2'), '( 1 / ( 1 / 2 ) ) = 2')
    RSq = RS('S')
    k2 = cq([cq([ng, rb], 'eqbrtrd', '%s <_ ( 1 / %s )' % (RSq, H)), two], 'breqtrd', '%s <_ 2' % RSq)
    WQq = WQ('q', GF)
    # the terms
    zc = tsub(ante_of(stmt('ef2zs'))[1], {'F': GF, 'A': '1', 'T': CT_})
    zs = cj([cj([cj.a1(w.s([], 'ef2ddg', DD(GF, '1')), DD(GF, '1')), ctr], 'jca', '( %s /\\ %s e. RR )' % (DD(GF, '1'), CT_)), w.inst('ef2zs')], 'syl', zc)
    zfin = cj([zs, w.inst('simp1')], 'syl', top_and(zc)[0])
    zall = cj([zs, w.inst('simp2')], 'syl', top_and(zc)[1])
    mo = w.s([zall], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Aq, GF))
    OG = '( %s holord q )' % GF
    ogr = cq([mo], 'nnred', '%s e. RR' % OG)
    og0 = cq([cq([mo], 'nnnn0d', '%s e. NN0' % OG)], 'nn0ge0d', '0 <_ %s' % OG)
    W1 = '( 1 + ( abs ` ( Im ` q ) ) )'
    aim = cq([cq([cq([d['cc']], 'imcld', '( Im ` q ) e. RR')], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    w1p = cq([cq([numst(w, Aq, '1', 'RR'), aim], 'readdcld', '%s e. RR' % W1), lin8(w, Aq, [cq([cq([cq([d['cc']], 'imcld', '( Im ` q ) e. RR')], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < %s' % W1, {'( abs ` ( Im ` q ) )': aim})], 'elrpd', '%s e. RR+' % W1)
    wqr = cq([ogr, w1p], 'rerpdivcld', '%s e. RR' % WQq)
    wq0 = cq([ogr, w1p, og0], 'divge0d', '0 <_ %s' % WQq)
    rsr = cq([cq([xp, cq([numst(w, Aq, H, 'RR')], 'renegcld', '-u %s e. RR' % H)], 'rpcxpcld', '%s e. RR+' % RSq)], 'rpred', '%s e. RR' % RSq)
    tl = cq([rsr, numst(w, Aq, '2', 'RR'), wqr, wq0, k2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 2 )' % (WQq, RSq, WQq))
    IN1 = 'sum_ q e. %s ( %s x. %s )' % (Z, WQq, RSq)
    IN2 = 'sum_ q e. %s ( %s x. 2 )' % (Z, WQq)
    INW = 'sum_ q e. %s %s' % (Z, WQq)
    fi1 = cj([zfin, cq([wqr, rsr], 'remulcld', '( %s x. %s ) e. RR' % (WQq, RSq)), cq([wqr, numst(w, Aq, '2', 'RR')], 'remulcld', '( %s x. 2 ) e. RR' % WQq), tl], 'fsumle', '%s <_ %s' % (IN1, IN2))
    fi2 = cj([zfin, cj([], '2cnd', '2 e. CC'), cq([wqr], 'recnd', '%s e. CC' % WQq)], 'fsummulc1', '( %s x. 2 ) = %s' % (INW, IN2))
    inn = cj([fi1, cj([fi2], 'eqcomd', '%s = ( %s x. 2 )' % (IN2, INW))], 'breqtrd', '%s <_ ( %s x. 2 )' % (IN1, INW))
    in1r = cj([zfin, cq([wqr, rsr], 'remulcld', '( %s x. %s ) e. RR' % (WQq, RSq))], 'fsumrecl', '%s e. RR' % IN1)
    inwr = cj([zfin, wqr], 'fsumrecl', '%s e. RR' % INW)
    JR = '( 0 ..^ M )'
    fzo = c.a1(w.s([], 'fzofi', '%s e. Fin' % JR), '%s e. Fin' % JR)
    O1 = 'sum_ j e. %s %s' % (JR, IN1)
    O2 = 'sum_ j e. %s ( %s x. 2 )' % (JR, INW)
    OW = 'sum_ j e. %s %s' % (JR, INW)
    fo1 = c([fzo, in1r, cj([inwr, numst(w, Aj, '2', 'RR')], 'remulcld', '( %s x. 2 ) e. RR' % INW), inn], 'fsumle', '%s <_ %s' % (O1, O2))
    fo2 = c([fzo, c([], '2cnd', '2 e. CC'), cj([inwr], 'recnd', '%s e. CC' % INW)], 'fsummulc1', '( %s x. 2 ) = %s' % (OW, O2))
    out = c([fo1, c([fo2], 'eqcomd', '%s = ( %s x. 2 )' % (O2, OW))], 'breqtrd', '%s <_ ( %s x. 2 )' % (O1, OW))
    SG_ = tsub(stmt('ef3sgw'), {'F': GF, 'A': '1'})
    sga, sgc = ante_of(SG_)
    sgw = c([rebuild(w, c, sga, {DD(GF, '1'): c.a1(w.s([], 'ef2ddg', DD(GF, '1')), DD(GF, '1'))}), w.inst('ef3sgw')], 'syl', sgc)
    owr = c([fzo, inwr], 'fsumrecl', '%s e. RR' % OW)
    L4 = LT41
    l4r = c([c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), c([c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 4 )', {'T': tr})], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( 1 x. ( T + 4 ) ) e. RR+')], 'relogcld', '%s e. RR' % L4)
    l4s = c([l4r], 'resqcld', '( %s ^ 2 ) e. RR' % L4)
    l4s0 = c([l4r], 'sqge0d', '0 <_ ( %s ^ 2 ) ' % L4) if False else c([l4r], 'sqge0d', '0 <_ ( %s ^ 2 )' % L4)
    fin = lin8(w, A0, [out, sgw, l4s0], '%s <_ ( %s x. ( %s ^ 2 ) )' % (O1, KS, L4), {O1: c([fzo, in1r], 'fsumrecl', '%s e. RR' % O1), OW: owr, '( %s ^ 2 )' % L4: l4s})
    rn = c([w.s([rne], 'ralrimiva', '( %s -> A. q e. %s %s =/= S )' % (Aj, Z, rq))], 'ralrimiva', 'A. j e. %s A. q e. %s %s =/= S' % (JR, Z, rq))
    w.qed([rn, fin], 'jca', S['ef6pw'])
    return run8(w)


GENS = {'ef6pw': gen_pw}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
