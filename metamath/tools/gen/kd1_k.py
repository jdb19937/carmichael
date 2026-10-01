"""Sortie KD1: the general-k diagonal bound, parametrized (kddiag)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from mvlib import ringeq
from lin import linarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def mval(w, ante, M, n, body, memn, bodycl, cls='RR'):
    """( ante -> ( M ` n ) = body ) for M = ( n e. NN |-> body ) at its own binder (fvmpt2)"""
    fe = w.s([w.s([], 'eqid', '%s = %s' % (M, M))], 'fvmpt2', '( ( %s e. NN /\\ %s e. %s ) -> ( %s ` %s ) = %s )' % (n, body, cls, M, n, body))
    return w.s([memn, bodycl, fe], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, M, n, body))


def gen_diag():
    w = W('kddiag', 'Lean ` KDerivDetect.tsum_vonMangoldt_log_pow_rpow_le ` : ` sum Lam ( n ) ( log n ) ^ K n ^ -u ( 1 + V + W ) <_ ( K ! / V ^ K ) ( ( 5 / 4 ) / W + 5 ) ` (Lean ` 1 / w + 2 ` ; ZC1 ` vmsharp ` ), with the convergence.')
    A0 = S['kddiag'].split(' -> ( seq')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    vw = s([], 'simpl', '( V e. RR+ /\\ W e. RR+ /\\ W <_ 1 )')
    vp = s([vw], 'simp1d', 'V e. RR+'); wp = s([vw], 'simp2d', 'W e. RR+'); w1 = s([vw], 'simp3d', 'W <_ 1'); kk = s([], 'simpr', 'K e. NN0')
    vr = s([vp], 'rpred', 'V e. RR'); wr = s([wp], 'rpred', 'W e. RR')
    Q = '( ( ! ` K ) / ( V ^ K ) )'
    fk = s([kk], 'faccld', '( ! ` K ) e. NN')
    vk = s([vp, s([kk], 'nn0zd', 'K e. ZZ')], 'rpexpcld', '( V ^ K ) e. RR+')
    qrp = s([s([fk], 'nnrpd', '( ! ` K ) e. RR+'), vk], 'rpdivcld', '%s e. RR+' % Q)
    qr = s([qrp], 'rpred', '%s e. RR' % Q); q0 = s([qrp], 'rpge0d', '0 <_ %s' % Q)
    X1 = '( 1 + ( V + W ) )'; X2 = '( 1 + W )'
    G = '( n e. NN |-> ( ( ( Lam ` n ) x. ( ( log ` n ) ^ K ) ) x. ( n ^c -u %s ) ) )' % X1
    F0 = '( n e. NN |-> ( ( Lam ` n ) x. ( n ^c -u %s ) ) )' % X2
    H = '( n e. NN |-> ( %s x. ( ( Lam ` n ) x. ( n ^c -u %s ) ) ) )' % (Q, X2)
    GB = lambda x: '( ( ( Lam ` %s ) x. ( ( log ` %s ) ^ K ) ) x. ( %s ^c -u %s ) )' % (x, x, x, X1)
    FB = lambda x: '( ( Lam ` %s ) x. ( %s ^c -u %s ) )' % (x, x, X2)
    HB = lambda x: '( %s x. %s )' % (Q, FB(x))
    gb, fb, hb = GB('k'), FB('k'), HB('k')
    def block(An, nn):
        t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (An, f))
        ad = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (An, formula_of(w, st).split(' -> ', 1)[1][:-2]))
        lam = t([nn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR'); lam0 = t([nn, w.inst('vmage0')], 'syl', '0 <_ ( Lam ` k )')
        nr = t([nn], 'nnrpd', 'k e. RR+')
        L = '( log ` k )'
        lr = t([nr], 'relogcld', '%s e. RR' % L)
        l0 = t([t([nn], 'nnred', 'k e. RR'), t([nn], 'nnge1d', '1 <_ k'), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L)
        c = Closure(w, An, {'V': ('RR', ad(vr)), 'W': ('RR', ad(wr))})
        x1r = c.mem('-u %s' % X1, 'RR'); x2r = c.mem('-u %s' % X2, 'RR')
        E1 = '( k ^c -u %s )' % X1; E2 = '( k ^c -u %s )' % X2; NV = '( k ^c V )'
        e1 = t([nr, x1r], 'rpcxpcld', '%s e. RR+' % E1); e2 = t([nr, x2r], 'rpcxpcld', '%s e. RR+' % E2)
        nv = t([nr, ad(vr)], 'rpcxpcld', '%s e. RR+' % NV)
        lk = t([lr, ad(kk)], 'reexpcld', '( %s ^ K ) e. RR' % L)
        lk0 = t([lr, ad(kk), l0], 'expge0d', '0 <_ ( %s ^ K )' % L)
        gbr = t([t([lam, lk], 'remulcld', '( ( Lam ` k ) x. ( %s ^ K ) ) e. RR' % L), t([e1], 'rpred', '%s e. RR' % E1)], 'remulcld', '%s e. RR' % gb)
        gb0 = t([t([lam, lk], 'remulcld', '( ( Lam ` k ) x. ( %s ^ K ) ) e. RR' % L), t([e1], 'rpred', '%s e. RR' % E1),
                 t([lam, lk, lam0, lk0], 'mulge0d', '0 <_ ( ( Lam ` k ) x. ( %s ^ K ) )' % L), t([e1], 'rpge0d', '0 <_ %s' % E1)], 'mulge0d', '0 <_ %s' % gb)
        fbr = t([lam, t([e2], 'rpred', '%s e. RR' % E2)], 'remulcld', '%s e. RR' % fb)
        fb0 = t([lam, t([e2], 'rpred', '%s e. RR' % E2), lam0, t([e2], 'rpge0d', '0 <_ %s' % E2)], 'mulge0d', '0 <_ %s' % fb)
        hbr = t([ad(qr), fbr], 'remulcld', '%s e. RR' % hb)
        hb0 = t([ad(qr), fbr, ad(q0), fb0], 'mulge0d', '0 <_ %s' % hb)
        lp = t([ad(vp), ad(kk), nn, w.inst('kdlogpow')], 'syl3anc', '( %s ^ K ) <_ ( ( ( ! ` K ) x. %s ) / ( V ^ K ) )' % (L, NV))
        d23 = t([t([ad(fk)], 'nncnd', '( ! ` K ) e. CC'), t([nv], 'rpcnd', '%s e. CC' % NV), t([ad(vk)], 'rpcnd', '( V ^ K ) e. CC'), t([ad(vk)], 'rpne0d', '( V ^ K ) =/= 0')],
                'div23d', '( ( ( ! ` K ) x. %s ) / ( V ^ K ) ) = ( %s x. %s )' % (NV, Q, NV))
        lp2 = t([lp, d23], 'breqtrd', '( %s ^ K ) <_ ( %s x. %s )' % (L, Q, NV))
        QN = '( %s x. %s )' % (Q, NV)
        qnr = t([ad(qr), t([nv], 'rpred', '%s e. RR' % NV)], 'remulcld', '%s e. RR' % QN)
        s1 = t([lk, qnr, lam, lam0, lp2], 'lemul2ad', '( ( Lam ` k ) x. ( %s ^ K ) ) <_ ( ( Lam ` k ) x. %s )' % (L, QN))
        s2 = t([t([lam, lk], 'remulcld', '( ( Lam ` k ) x. ( %s ^ K ) ) e. RR' % L), t([lam, qnr], 'remulcld', '( ( Lam ` k ) x. %s ) e. RR' % QN),
                t([e1], 'rpred', '%s e. RR' % E1), t([e1], 'rpge0d', '0 <_ %s' % E1), s1], 'lemul1ad', '%s <_ ( ( ( Lam ` k ) x. %s ) x. %s )' % (gb, QN, E1))
        cc = Closure(w, An, {'( Lam ` k )': ('CC', t([lam], 'recnd', '( Lam ` k ) e. CC')), Q: ('CC', t([ad(qr)], 'recnd', '%s e. CC' % Q)),
                             NV: ('CC', t([nv], 'rpcnd', '%s e. CC' % NV)), E1: ('CC', t([e1], 'rpcnd', '%s e. CC' % E1))})
        for a_ in ('( Lam ` k )', Q, NV, E1):
            cc.atom(a_)
        r1 = ringeq(w, An, '( ( ( Lam ` k ) x. %s ) x. %s )' % (QN, E1), '( %s x. ( ( Lam ` k ) x. ( %s x. %s ) ) )' % (Q, NV, E1), cc)
        ncn = t([nr], 'rpcnd', 'k e. CC'); nne = t([nr], 'rpne0d', 'k =/= 0')
        cx = t([ncn, nne, t([ad(vr)], 'recnd', 'V e. CC'), t([x1r], 'recnd', '-u %s e. CC' % X1)], 'cxpaddd', '( k ^c ( V + -u %s ) ) = ( %s x. %s )' % (X1, NV, E1))
        cv = Closure(w, An, {'V': ('CC', t([ad(vr)], 'recnd', 'V e. CC')), 'W': ('CC', t([ad(wr)], 'recnd', 'W e. CC'))})
        ex = ringeq(w, An, '( V + -u %s )' % X1, '-u %s' % X2, cv)
        cx2 = t([t([ex], 'oveq2d', '( k ^c ( V + -u %s ) ) = %s' % (X1, E2)), cx], 'eqtr3d', '%s = ( %s x. %s )' % (E2, NV, E1))
        r2 = t([t([cx2], 'oveq2d', '( ( Lam ` k ) x. %s ) = ( ( Lam ` k ) x. ( %s x. %s ) )' % (E2, NV, E1))], 'oveq2d',
               '( %s x. ( ( Lam ` k ) x. %s ) ) = ( %s x. ( ( Lam ` k ) x. ( %s x. %s ) ) )' % (Q, E2, Q, NV, E1))
        r3 = t([r1, r2], 'eqtr4d', '( ( ( Lam ` k ) x. %s ) x. %s ) = %s' % (QN, E1, hb))
        gh = t([s2, r3], 'breqtrd', '%s <_ %s' % (gb, hb))
        return dict(gbr=gbr, gb0=gb0, fbr=fbr, fb0=fb0, hbr=hbr, hb0=hb0, gh=gh)
    An = '( %s /\\ k e. NN )' % A0
    nnA = w.s([], 'simpr', '( %s -> k e. NN )' % An)
    bA = block(An, nnA)
    Au = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A0
    nnU = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Au), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> k e. NN )' % Au)
    bU = block(Au, nnU)
    def tv(ante, nn, M, BOD, cl_):
        idx = w.s([], 'id', '( n = k -> n = k )')
        st, new = w.congr(BOD('n'), {'n': 'k'}, 'n = k', {'n': idx})
        assert new == BOD('k'), new
        return fvmd(w, ante, M, 'k', BOD('k'), nn, cl_, st, var='n')
    gvA = tv(An, nnA, G, GB, bA['gbr']); fvA = tv(An, nnA, F0, FB, bA['fbr']); hvA = tv(An, nnA, H, HB, bA['hbr'])
    gvU = tv(Au, nnU, G, GB, bU['gbr']); fvU = tv(Au, nnU, F0, FB, bU['fbr']); hvU = tv(Au, nnU, H, HB, bU['hbr'])
    uz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0)
    onez = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0)
    fvr = w.s([fvA, bA['fbr']], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (An, F0))
    gvc = w.s([w.s([gvA, bA['gbr']], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (An, G))], 'recnd', '( %s -> ( %s ` k ) e. CC )' % (An, G))
    hvc = w.s([w.s([hvA, bA['hbr']], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (An, H))], 'recnd', '( %s -> ( %s ` k ) e. CC )' % (An, H))
    c1w = s([s([s([wr], 'id', 'W e. RR') if False else wr, s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), wr], 'readdcld', '%s e. RR' % X2)], 'jca', 'T.') if False else None][0:0] or [], 'T.', 'T.') if False else None
    x2r = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), wr], 'readdcld', '%s e. RR' % X2)
    cw = Closure(w, A0, {'W': ('RR', wr)})
    x21 = linarith(w, A0, [s([wp], 'rpgt0d', '0 < W')], '1 < %s' % X2, closure=cw)
    fcv = s([x2r, x21, w.inst('vmsercvg')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % F0)
    # |G n| <_ Q ( F0 n ) on ZZ>= 1
    agU = w.s([w.s([w.s([gvU], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Au, G, gb)), w.s([bU['gbr'], bU['gb0']], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (Au, gb, gb))],
                   'eqtrd', '( %s -> ( abs ` ( %s ` k ) ) = %s )' % (Au, G, gb)), w.s([bU['gh'], w.s([fvU], 'oveq2d', '( %s -> ( %s x. ( %s ` k ) ) = %s )' % (Au, Q, F0, hb))], 'breqtrrd',
                                                                                      '( %s -> %s <_ ( %s x. ( %s ` k ) ) )' % (Au, gb, Q, F0))],
              'eqbrtrd', '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) ) )' % (Au, G, Q, F0))
    gcv = w.s([uz, one, fvr, gvc, fcv, qr, agU], 'cvgcmpce', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, G))
    ahU = w.s([w.s([w.s([hvU], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Au, H, hb)), w.s([bU['hbr'], bU['hb0']], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (Au, hb, hb))],
                   'eqtrd', '( %s -> ( abs ` ( %s ` k ) ) = %s )' % (Au, H, hb)), w.s([fvU], 'oveq2d', '( %s -> ( %s x. ( %s ` k ) ) = %s )' % (Au, Q, F0, hb))],
              'eqtr4d', '( %s -> ( abs ` ( %s ` k ) ) = ( %s x. ( %s ` k ) ) )' % (Au, H, Q, F0))
    ahU2 = w.s([ahU, w.s([w.s([w.s([w.s([], 'eqid', 'T.')], 'id', 'T.')], 'id', 'T.')], 'id', 'T.') if False else None][0:1] and
               [w.s([ahU], 'eqled', '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) ) )' % (Au, H, Q, F0))][0], 'id', 'T.') if False else \
        w.s([w.s([w.s([hvU], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Au, H, hb)), w.s([bU['hbr'], bU['hb0']], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (Au, hb, hb))],
                 'eqtrd', '( %s -> ( abs ` ( %s ` k ) ) = %s )' % (Au, H, hb)), w.s([fvU], 'oveq2d', '( %s -> ( %s x. ( %s ` k ) ) = %s )' % (Au, Q, F0, hb))], 'T.', 'T.') if False else \
        w.s([ahU], 'eqled', '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) ) )' % (Au, H, Q, F0))
    hcv = w.s([uz, one, fvr, hvc, fcv, qr, ahU2], 'cvgcmpce', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, H))
    le1 = w.s([uz, onez, gvA, bA['gbr'], hvA, bA['hbr'], w.s([bA['gh']], 'id', '( %s -> %s <_ %s )' % (An, gb, hb)) if False else bA['gh'], gcv, hcv], 'isumle',
              '( %s -> sum_ k e. NN %s <_ sum_ k e. NN %s )' % (A0, gb, hb))
    mc = w.s([uz, onez, fvA, w.s([bA['fbr']], 'recnd', '( %s -> %s e. CC )' % (An, fb)), fcv, s([qr], 'recnd', '%s e. CC' % Q)], 'isummulc2',
             '( %s -> ( %s x. sum_ k e. NN %s ) = sum_ k e. NN %s )' % (A0, Q, fb, hb))
    VMk = 'sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u %s ) )' % X2
    assert VMk == 'sum_ k e. NN %s' % fb
    vs2 = s([s([wp, w1], 'jca', '( W e. RR+ /\\ W <_ 1 )'), w.inst('vmsharp')], 'syl', '%s <_ ( ( ( 5 / 4 ) / W ) + 5 )' % VMk)
    sfr = w.s([uz, onez, fvA, bA['fbr'], fcv], 'isumrecl', '( %s -> sum_ k e. NN %s e. RR )' % (A0, fb))
    RB = '( ( ( 5 / 4 ) / W ) + 5 )'
    rbr = s([s([s([w.s([w.s([], '5re', '5 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '4ne0', '4 =/= 0')], 'redivcli', '( 5 / 4 ) e. RR')], 'a1i', '( 5 / 4 ) e. RR'), wp], 'rerpdivcld', '( ( 5 / 4 ) / W ) e. RR'),
             s([w.s([], '5re', '5 e. RR')], 'a1i', '5 e. RR')], 'readdcld', '%s e. RR' % RB)
    le2 = s([sfr, rbr, qr, q0, vs2], 'lemul2ad', '( %s x. sum_ k e. NN %s ) <_ ( %s x. %s )' % (Q, fb, Q, RB))
    ghr = w.s([uz, onez, gvA, bA['gbr'], gcv], 'isumrecl', '( %s -> sum_ k e. NN %s e. RR )' % (A0, gb))
    hhr = w.s([uz, onez, hvA, bA['hbr'], hcv], 'isumrecl', '( %s -> sum_ k e. NN %s e. RR )' % (A0, hb))
    le3 = s([ghr, hhr, s([qr, rbr], 'remulcld', '( %s x. %s ) e. RR' % (Q, RB)), le1, s([mc, le2], 'eqbrtrrd', 'sum_ k e. NN %s <_ ( %s x. %s )' % (hb, Q, RB))], 'letrd',
            'sum_ k e. NN %s <_ ( %s x. %s )' % (gb, Q, RB))
    idk = w.s([], 'id', '( k = n -> k = n )')
    ck, nk = w.congr(GB('k'), {'k': 'n'}, 'k = n', {'k': idk})
    cbg = w.s([ck], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (GB('k'), GB('n')))
    le4 = s([w.s([cbg], 'a1i', '( %s -> sum_ k e. NN %s = sum_ n e. NN %s )' % (A0, GB('k'), GB('n'))), le3], 'eqbrtrrd', 'sum_ n e. NN %s <_ ( %s x. %s )' % (GB('n'), Q, RB))
    w.qed([gcv, le4], 'jca', S['kddiag'])
    return run(w)


if __name__ == '__main__':
    gen_diag()
