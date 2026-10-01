"""Sortie ZC1: the zeta lower bound 1 / u <_ zeta ( 1 + u ) (zlbterm, zetalb)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
import cl as _cl
from c8_o import numst
import lin
lin.FASTPATH = True

UU = '( U e. RR+ /\\ U <_ 1 )'
S['zlbterm'] = '( ( %s /\\ J e. NN ) -> ( ( ( J ^c -u U ) - ( ( J + 1 ) ^c -u U ) ) / U ) <_ ( J ^c -u ( 1 + U ) ) )' % UU
S['zetalb'] = '( %s -> ( 1 / U ) <_ sum_ k e. NN ( k ^c -u ( 1 + U ) ) )' % UU


def clo_atoms(w, A0, lv):
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    return c


def gen_zlbterm():
    w = W('zlbterm', 'Termwise comparison for the zeta lower bound: ` ( J ^ -u - ( J + 1 ) ^ -u ) / u <_ J ^ - ( 1 + u ) ` for ` 0 < u <_ 1 ` ( ~ z5dbern : ` ( 1 + 1 / J ) ^ u <_ 1 + u / J ` ).')
    A0 = ante_of(S['zlbterm'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    uu = s([], 'simpl', UU); jn = s([], 'simpr', 'J e. NN')
    up = s([uu, w.inst('simpl')], 'syl', 'U e. RR+'); u1 = s([uu, w.inst('simpr')], 'syl', 'U <_ 1')
    ur = s([up], 'rpred', 'U e. RR'); uc = s([up], 'rpcnd', 'U e. CC'); u0 = s([up], 'rpge0d', '0 <_ U')
    jp = s([jn], 'nnrpd', 'J e. RR+'); jr = s([jn], 'nnred', 'J e. RR'); jc = s([jn], 'nncnd', 'J e. CC'); jne = s([jn], 'nnne0d', 'J =/= 0')
    J1 = '( J + 1 )'
    j1p = s([jp, s([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')], 'rpaddcld', '%s e. RR+' % J1)
    nur = s([ur], 'renegcld', '-u U e. RR')
    A = '( J ^c -u U )'; B = '( %s ^c -u U )' % J1
    ap = s([jp, nur], 'rpcxpcld', '%s e. RR+' % A); bp = s([j1p, nur], 'rpcxpcld', '%s e. RR+' % B)
    Q = '( %s / J )' % J1
    qp = s([j1p, jp], 'rpdivcld', '%s e. RR+' % Q); qr = s([qp], 'rpred', '%s e. RR' % Q)
    Y = '( 1 / J )'
    yr = s([jp], 'rpreccld', '%s e. RR+' % Y)
    qd = s([s([jc, s([], '1cnd', '1 e. CC'), jc, jne], 'divdird', '%s = ( ( J / J ) + %s )' % (Q, Y)), s([s([jc, jne], 'dividd', '( J / J ) = 1')], 'oveq1d', '( ( J / J ) + %s ) = ( 1 + %s )' % (Y, Y))],
            'eqtrd', '%s = ( 1 + %s )' % (Q, Y))
    lvq = {Q: qr, Y: s([yr], 'rpred', '%s e. RR' % Y)}
    q1 = lin8(w, A0, [qd, s([yr], 'rpge0d', '0 <_ %s' % Y)], '1 <_ %s' % Q, lvq)
    R = '( %s ^c U )' % Q
    rp = s([qp, ur], 'rpcxpcld', '%s e. RR+' % R)
    zb = s([s([s([qr, q1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (Q, Q)), s([ur, s([u0, u1], 'jca', '( 0 <_ U /\\ U <_ 1 )')], 'jca', '( U e. RR /\\ ( 0 <_ U /\\ U <_ 1 ) )')], 'jca',
               '( ( %s e. RR /\\ 1 <_ %s ) /\\ ( U e. RR /\\ ( 0 <_ U /\\ U <_ 1 ) ) )' % (Q, Q)), w.inst('z5dbern')], 'syl', '%s <_ ( 1 + ( U x. ( %s - 1 ) ) )' % (R, Q))
    qm1 = lin.lineq(w, A0, '( %s - 1 )' % Q, Y, hyps=[qd], closure=clo_atoms(w, A0, lvq))
    zb2 = s([zb, s([s([qm1], 'oveq2d', '( U x. ( %s - 1 ) ) = ( U x. %s )' % (Q, Y))], 'oveq2d', '( 1 + ( U x. ( %s - 1 ) ) ) = ( 1 + ( U x. %s ) )' % (Q, Y))], 'breqtrd',
            '%s <_ ( 1 + ( U x. %s ) )' % (R, Y))
    # r >_ 1
    cl0 = s([s([s([qr, q1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (Q, Q)), s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), ur], 'jca', '( 0 e. RR /\\ U e. RR )'), u0], '3jca',
               '( ( %s e. RR /\\ 1 <_ %s ) /\\ ( 0 e. RR /\\ U e. RR ) /\\ 0 <_ U )' % (Q, Q)), w.inst('cxplea')], 'syl', '( %s ^c 0 ) <_ %s' % (Q, R))
    r1 = s([s([s([qp], 'rpcnd', '%s e. CC' % Q), w.inst('cxp0')], 'syl', '( %s ^c 0 ) = 1' % Q), cl0], 'eqbrtrrd', '1 <_ %s' % R)
    # s = Q ^c -u U = 1 / r = b / a
    Sv = '( %s ^c -u U )' % Q
    sneg = s([s([qp], 'rpcnd', '%s e. CC' % Q), s([qp], 'rpne0d', '%s =/= 0' % Q), uc], 'cxpnegd', '%s = ( 1 / %s )' % (Sv, R))
    rs1 = s([s([s([rp], 'rpcnd', '%s e. CC' % R), s([rp], 'rpne0d', '%s =/= 0' % R)], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (R, R)), s([sneg], 'oveq2d', '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (R, Sv, R, R))],
            'x', 'x') if False else s([s([sneg], 'oveq2d', '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (R, Sv, R, R)), s([s([rp], 'rpcnd', '%s e. CC' % R), s([rp], 'rpne0d', '%s =/= 0' % R)], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (R, R))],
                                    'eqtrd', '( %s x. %s ) = 1' % (R, Sv))
    sdv = s([s([j1p], 'rpred', '%s e. RR' % J1), s([j1p], 'rpge0d', '0 <_ %s' % J1), jp, s([nur], 'recnd', '-u U e. CC')], 'divcxpd', '%s = ( %s / %s )' % (Sv, B, A)) if False else \
        s([s([j1p], 'rpred', '%s e. RR' % J1), s([j1p], 'rpge0d', '0 <_ %s' % J1), jp, s([nur], 'recnd', '-u U e. CC')], 'divcxpd', '%s = ( %s / %s )' % (Sv, B, A))
    bsa = s([s([s([sdv], 'oveq1d', '( %s x. %s ) = ( ( %s / %s ) x. %s )' % (Sv, A, B, A, A)), s([s([bp], 'rpcnd', '%s e. CC' % B), s([ap], 'rpcnd', '%s e. CC' % A), s([ap], 'rpne0d', '%s =/= 0' % A)], 'divcan1d',
                                                                                                                     '( ( %s / %s ) x. %s ) = %s' % (B, A, A, B))], 'eqtrd', '( %s x. %s ) = %s' % (Sv, A, B))], 'eqcomd', '%s = ( %s x. %s )' % (B, Sv, A))
    spp = s([qp, nur], 'rpcxpcld', '%s e. RR+' % Sv)
    # c = J ^c -u ( 1 + U ) = ( 1 / J ) x. a
    C_ = '( J ^c -u ( 1 + U ) )'
    ng = s([s([], '1cnd', '1 e. CC'), uc], 'negdid', '-u ( 1 + U ) = ( -u 1 + -u U )')
    ca = s([jc, jne, s([s([], '1cnd', '1 e. CC')], 'negcld', '-u 1 e. CC'), s([uc], 'negcld', '-u U e. CC')], 'cxpaddd', '( J ^c ( -u 1 + -u U ) ) = ( ( J ^c -u 1 ) x. %s )' % A)
    cm1 = s([s([jc, jne, s([], '1cnd', '1 e. CC')], 'cxpnegd', '( J ^c -u 1 ) = ( 1 / ( J ^c 1 ) )'), s([s([jc], 'cxp1d', '( J ^c 1 ) = J')], 'oveq2d', '( 1 / ( J ^c 1 ) ) = %s' % Y)], 'eqtrd', '( J ^c -u 1 ) = %s' % Y)
    cc = s([s([s([ng], 'oveq2d', '%s = ( J ^c ( -u 1 + -u U ) )' % C_), ca], 'eqtrd', '%s = ( ( J ^c -u 1 ) x. %s )' % (C_, A)), s([cm1], 'oveq1d', '( ( J ^c -u 1 ) x. %s ) = ( %s x. %s )' % (A, Y, A))],
            'eqtrd', '%s = ( %s x. %s )' % (C_, Y, A))
    # the inequality in atoms a, s, r, y, U
    ar = s([ap], 'rpred', '%s e. RR' % A); sr = s([spp], 'rpred', '%s e. RR' % Sv); rr = s([rp], 'rpred', '%s e. RR' % R); yrr = s([yr], 'rpred', '%s e. RR' % Y)
    lv = {A: ar, Sv: sr, R: rr, Y: yrr, 'U': ur}
    c = clo_atoms(w, A0, lv)
    UY = '( U x. %s )' % Y
    uy0 = s([ur, yrr, u0, s([yr], 'rpge0d', '0 <_ %s' % Y)], 'mulge0d', '0 <_ %s' % UY)
    h0 = s([s([rr, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % R), sr, lin8(w, A0, [r1], '0 <_ ( %s - 1 )' % R, lv), s([spp], 'rpge0d', '0 <_ %s' % Sv)], 'mulge0d',
           '0 <_ ( ( %s - 1 ) x. %s )' % (R, Sv))
    s1 = lin.linarith(w, A0, [h0, rs1], '%s <_ 1' % Sv, closure=c, products=True)
    h1 = s([c.mem('( ( 1 + %s ) - %s )' % (UY, R), 'RR'), sr, lin.linarith(w, A0, [zb2], '0 <_ ( ( 1 + %s ) - %s )' % (UY, R), closure=c, products=True), s([spp], 'rpge0d', '0 <_ %s' % Sv)], 'mulge0d',
           '0 <_ ( ( ( 1 + %s ) - %s ) x. %s )' % (UY, R, Sv))
    h2 = s([c.mem(UY, 'RR'), c.mem('( 1 - %s )' % Sv, 'RR'), uy0, lin8(w, A0, [s1], '0 <_ ( 1 - %s )' % Sv, lv)], 'mulge0d', '0 <_ ( %s x. ( 1 - %s ) )' % (UY, Sv))
    sge = lin.linarith(w, A0, [h1, h2, rs1], '( 1 - %s ) <_ %s' % (UY, Sv), closure=c, products=True)
    h3 = s([c.mem('( %s - ( 1 - %s ) )' % (Sv, UY), 'RR'), ar, lin.linarith(w, A0, [sge], '0 <_ ( %s - ( 1 - %s ) )' % (Sv, UY), closure=c, products=True), s([ap], 'rpge0d', '0 <_ %s' % A)], 'mulge0d',
           '0 <_ ( ( %s - ( 1 - %s ) ) x. %s )' % (Sv, UY, A))
    lv2 = dict(lv); lv2[B] = s([bp], 'rpred', '%s e. RR' % B); lv2[C_] = s([s([jp, s([s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), ur], 'readdcld', '( 1 + U ) e. RR')], 'renegcld', '-u ( 1 + U ) e. RR')], 'rpcxpcld',
                                                                        '%s e. RR+' % C_)], 'rpred', '%s e. RR' % C_)
    c2 = clo_atoms(w, A0, lv2)
    ucc = s([cc], 'oveq2d', '( U x. %s ) = ( U x. ( %s x. %s ) )' % (C_, Y, A))
    key = lin.linarith(w, A0, [h3, bsa, ucc], '( %s - %s ) <_ ( U x. %s )' % (A, B, C_), closure=c2, products=True)
    fin = s([key, s([s([ar, s([bp], 'rpred', '%s e. RR' % B)], 'resubcld', '( %s - %s ) e. RR' % (A, B)), lv2[C_], up], 'ledivmuld', '( ( ( %s - %s ) / U ) <_ %s <-> ( %s - %s ) <_ ( U x. %s ) )' % (A, B, C_, A, B, C_))],
            'mpbird', '( ( %s - %s ) / U ) <_ %s' % (A, B, C_))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['zlbterm']))
    return run8(w)


def gen_zetalb():
    w = W('zetalb', 'Lower bound ` 1 / u <_ zeta ( 1 + u ) ` for ` 0 < u <_ 1 ` (Lean ` one_div_le_tsum_zeta ` , Census): the partial sums dominate the telescoping sums ` ( 1 - n ^ -u ) / u ` ( ~ zlbterm , ~ telfsumo , ~ cxpnegcvg , ~ climle ).')
    A0 = UU
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    uu = s([], 'id', UU)
    up = s([uu, w.inst('simpl')], 'syl', 'U e. RR+')
    ur = s([up], 'rpred', 'U e. RR'); uc = s([up], 'rpcnd', 'U e. CC')
    IU = '( 1 / U )'
    iur = s([up], 'rpreccld', '%s e. RR+' % IU); iuc = s([iur], 'rpcnd', '%s e. CC' % IU); iurr = s([iur], 'rpred', '%s e. RR' % IU)
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = s([], '1zzd', '1 e. ZZ')
    Fm = '( n e. NN |-> ( n ^c -u U ) )'
    Hm = '( n e. NN |-> ( %s x. ( n ^c -u U ) ) )' % IU
    Gm = '( n e. NN |-> ( %s - ( %s x. ( n ^c -u U ) ) ) )' % (IU, IU)
    fcv = s([up, w.inst('cxpnegcvg')], 'syl', '%s ~~> 0' % Fm)
    Ai = '( %s /\\ i e. NN )' % A0
    si = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    Li = lambda st: lift(w, st, Ai)
    inn = si([], 'simpr', 'i e. NN'); ip = si([inn], 'nnrpd', 'i e. RR+')
    IUi = '( i ^c -u U )'
    iuu = si([ip, si([Li(ur)], 'renegcld', '-u U e. RR')], 'rpcxpcld', '%s e. RR+' % IUi)
    iuuc = si([iuu], 'rpcnd', '%s e. CC' % IUi); iuur = si([iuu], 'rpred', '%s e. RR' % IUi)
    mv = lambda body, val: _cg.mptval(w, Ai, 'n', 'NN', body, 'i', inn, exs=si([w.s([], 'ovex', '%s e. _V' % val)], 'a1i', '%s e. _V' % val), gen=w.g)[0]
    fi = mv('( n ^c -u U )', IUi)
    hi = mv('( %s x. ( n ^c -u U ) )' % IU, '( %s x. %s )' % (IU, IUi))
    gi = mv('( %s - ( %s x. ( n ^c -u U ) ) )' % (IU, IU), '( %s - ( %s x. %s ) )' % (IU, IU, IUi))
    fic = si([fi, iuuc], 'eqeltrd', '( %s ` i ) e. CC' % Fm)
    hi2 = si([hi, si([si([fi], 'oveq2d', '( %s x. ( %s ` i ) ) = ( %s x. %s )' % (IU, Fm, IU, IUi))], 'eqcomd', '( %s x. %s ) = ( %s x. ( %s ` i ) )' % (IU, IUi, IU, Fm))],
             'eqtrd', '( %s ` i ) = ( %s x. ( %s ` i ) )' % (Hm, IU, Fm))
    hex_ = s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % Hm)], 'a1i', '%s e. _V' % Hm)
    hcv = w.s([nnuz, one, fcv, iuc, hex_, fic, hi2], 'climmulc2', '( %s -> %s ~~> ( %s x. 0 ) )' % (A0, Hm, IU))
    hic = si([hi, si([Li(iuc), iuuc], 'mulcld', '( %s x. %s ) e. CC' % (IU, IUi))], 'eqeltrd', '( %s ` i ) e. CC' % Hm)
    gi2 = si([gi, si([si([hi], 'oveq2d', '( %s - ( %s ` i ) ) = ( %s - ( %s x. %s ) )' % (IU, Hm, IU, IU, IUi))], 'eqcomd', '( %s - ( %s x. %s ) ) = ( %s - ( %s ` i ) )' % (IU, IU, IUi, IU, Hm))],
             'eqtrd', '( %s ` i ) = ( %s - ( %s ` i ) )' % (Gm, IU, Hm))
    gex = s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % Gm)], 'a1i', '%s e. _V' % Gm)
    gcv = w.s([nnuz, one, hcv, iuc, gex, hic, gi2], 'climsubc2', '( %s -> %s ~~> ( %s - ( %s x. 0 ) ) )' % (A0, Gm, IU, IU))
    lim = s([s([s([iuc], 'mul01d', '( %s x. 0 ) = 0' % IU)], 'oveq2d', '( %s - ( %s x. 0 ) ) = ( %s - 0 )' % (IU, IU, IU)), s([iuc], 'subid1d', '( %s - 0 ) = %s' % (IU, IU))], 'eqtrd',
            '( %s - ( %s x. 0 ) ) = %s' % (IU, IU, IU))
    gcv2 = s([gcv, lim], 'breqtrd', '%s ~~> %s' % (Gm, IU))
    ZS_ = 'sum_ k e. NN ( k ^c -u ( 1 + U ) )'
    CS = '( NN X. { %s } )' % ZS_
    ssi = w.s([w.s([nnuz], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'eqimssi', '( ZZ>= ` 1 ) C_ NN')
    ccv = w.s([ssi, w.s([], 'nnex', 'NN e. _V')], 'climconst2', '( ( %s e. CC /\\ 1 e. ZZ ) -> %s ~~> %s )' % (ZS_, CS, ZS_))
    s1u = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), ur], 'readdcld', '( 1 + U ) e. RR')
    g1 = lin8(w, A0, [s([up], 'rpgt0d', '0 < U')], '1 < ( 1 + U )', {'U': ur})
    Tm = '( t e. NN |-> ( t ^c -u ( 1 + U ) ) )'
    zcv = s([s([s1u, g1], 'jca', '( ( 1 + U ) e. RR /\\ 1 < ( 1 + U ) )'), w.inst('zetacvg1')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % Tm)
    K1U = '( k ^c -u ( 1 + U ) )'
    def tval(ante, kst):
        sa = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        kp_ = sa([kst], 'nnrpd', 'k e. RR+')
        kr_ = sa([kp_, sa([lift(w, s1u, ante)], 'renegcld', '-u ( 1 + U ) e. RR')], 'rpcxpcld', '%s e. RR+' % K1U)
        tk = _cg.mptval(w, ante, 't', 'NN', '( t ^c -u ( 1 + U ) )', 'k', kst, exs=sa([w.s([], 'ovex', '%s e. _V' % K1U)], 'a1i', '%s e. _V' % K1U), gen=w.g)[0]
        return tk, kr_
    Ak = '( %s /\\ k e. NN )' % A0
    tk0, k1r0 = tval(Ak, w.s([], 'simpr', '( %s -> k e. NN )' % Ak))
    zsc = s([nnuz, one, tk0, w.s([k1r0], 'rpcnd', '( %s -> %s e. CC )' % (Ak, K1U)), zcv], 'isumcl', '%s e. CC' % ZS_)
    zr = s([nnuz, one, tk0, w.s([k1r0], 'rpred', '( %s -> %s e. RR )' % (Ak, K1U)), zcv], 'isumrecl', '%s e. RR' % ZS_)
    ccv2 = s([s([zsc, one], 'jca', '( %s e. CC /\\ 1 e. ZZ )' % ZS_), ccv], 'syl', '%s ~~> %s' % (CS, ZS_))
    ck = si([inn, w.s([w.s([], 'sumex', '%s e. _V' % ZS_)], 'fvconst2', '( i e. NN -> ( %s ` i ) = %s )' % (CS, ZS_))], 'syl', '( %s ` i ) = %s' % (CS, ZS_))
    ckr = si([si([ck], 'eqcomd', '%s = ( %s ` i )' % (ZS_, CS)), Li(zr)], 'eqeltrrd', '( %s ` i ) e. RR' % CS)
    GI = '( %s - ( %s x. %s ) )' % (IU, IU, IUi)
    gir = si([Li(iurr), si([Li(iurr), iuur], 'remulcld', '( %s x. %s ) e. RR' % (IU, IUi))], 'resubcld', '%s e. RR' % GI)
    gkr = si([gi, gir], 'eqeltrd', '( %s ` i ) e. RR' % Gm)
    # G ( i ) <_ zeta sum
    FZ = '( 1 ..^ i )'
    TEL = 'sum_ j e. %s ( ( j ^c -u U ) - ( ( j + 1 ) ^c -u U ) )' % FZ
    e1 = w.s([], 'oveq1', '( m = j -> ( m ^c -u U ) = ( j ^c -u U ) )')
    e2 = w.s([], 'oveq1', '( m = ( j + 1 ) -> ( m ^c -u U ) = ( ( j + 1 ) ^c -u U ) )')
    e3 = w.s([], 'oveq1', '( m = 1 -> ( m ^c -u U ) = ( 1 ^c -u U ) )')
    e4 = w.s([], 'oveq1', '( m = i -> ( m ^c -u U ) = %s )' % IUi)
    iuz = si([inn, w.s([], 'elnnuz', '( i e. NN <-> i e. ( ZZ>= ` 1 ) )')], 'sylib', 'i e. ( ZZ>= ` 1 )')
    Aim = '( %s /\\ m e. ( 1 ... i ) )' % Ai
    mn = w.s([w.s([], 'simpr', '( %s -> m e. ( 1 ... i ) )' % Aim), w.inst('elfznn')], 'syl', '( %s -> m e. NN )' % Aim)
    mc = w.s([w.s([mn], 'nncnd', '( %s -> m e. CC )' % Aim), w.s([lift(w, uc, Aim)], 'negcld', '( %s -> -u U e. CC )' % Aim)], 'cxpcld', '( %s -> ( m ^c -u U ) e. CC )' % Aim)
    tel = w.s([e1, e2, e3, e4, iuz, mc], 'telfsumo', '( %s -> %s = ( ( 1 ^c -u U ) - %s ) )' % (Ai, TEL, IUi))
    c1u = si([si([Li(uc)], 'negcld', '-u U e. CC'), w.inst('1cxp')], 'syl', '( 1 ^c -u U ) = 1')
    tel2 = si([tel, si([c1u], 'oveq1d', '( ( 1 ^c -u U ) - %s ) = ( 1 - %s )' % (IUi, IUi))], 'eqtrd', '%s = ( 1 - %s )' % (TEL, IUi))
    fzf = si([w.s([], 'fzofi', '%s e. Fin' % FZ)], 'a1i', '%s e. Fin' % FZ)
    Aij = '( %s /\\ j e. %s )' % (Ai, FZ)
    juz = w.s([w.s([], 'simpr', '( %s -> j e. %s )' % (Aij, FZ)), w.inst('elfzouz')], 'syl', '( %s -> j e. ( ZZ>= ` 1 ) )' % Aij)
    jnn = w.s([juz, w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> j e. NN )' % Aij)
    TJ = '( ( j ^c -u U ) - ( ( j + 1 ) ^c -u U ) )'
    jp_ = w.s([jnn], 'nnrpd', '( %s -> j e. RR+ )' % Aij)
    nur_ = w.s([lift(w, ur, Aij)], 'renegcld', '( %s -> -u U e. RR )' % Aij)
    ja = w.s([w.s([jp_, nur_], 'rpcxpcld', '( %s -> ( j ^c -u U ) e. RR+ )' % Aij)], 'rpred', '( %s -> ( j ^c -u U ) e. RR )' % Aij)
    jb = w.s([w.s([w.s([jp_, w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % Aij)], 'rpaddcld', '( %s -> ( j + 1 ) e. RR+ )' % Aij), nur_], 'rpcxpcld', '( %s -> ( ( j + 1 ) ^c -u U ) e. RR+ )' % Aij)],
             'rpred', '( %s -> ( ( j + 1 ) ^c -u U ) e. RR )' % Aij)
    tjr = w.s([ja, jb], 'resubcld', '( %s -> %s e. RR )' % (Aij, TJ))
    divs = si([fzf, Li(uc), w.s([tjr], 'recnd', '( %s -> %s e. CC )' % (Aij, TJ)), si([Li(up)], 'rpne0d', 'U =/= 0')], 'fsumdivc', '( %s / U ) = sum_ j e. %s ( %s / U )' % (TEL, FZ, TJ))
    ZT = tsub(S['zlbterm'], {'J': 'j'})
    zta, ztc = ante_of(ZT)
    zt = w.s([w.s([lift(w, uu, Aij), jnn], 'jca', '( %s -> %s )' % (Aij, zta)), w.inst('zlbterm')], 'syl', '( %s -> %s )' % (Aij, ztc))
    J1U = '( j ^c -u ( 1 + U ) )'
    j1r = w.s([w.s([jp_, w.s([lift(w, s1u, Aij)], 'renegcld', '( %s -> -u ( 1 + U ) e. RR )' % Aij)], 'rpcxpcld', '( %s -> %s e. RR+ )' % (Aij, J1U))], 'rpred', '( %s -> %s e. RR )' % (Aij, J1U))
    fle = si([fzf, w.s([tjr, lift(w, up, Aij)], 'rerpdivcld', '( %s -> ( %s / U ) e. RR )' % (Aij, TJ)), j1r, zt], 'fsumle', 'sum_ j e. %s ( %s / U ) <_ sum_ j e. %s %s' % (FZ, TJ, FZ, J1U))
    cvs = si([w.s([w.s([], 'oveq1', '( j = k -> ( j ^c -u ( 1 + U ) ) = ( k ^c -u ( 1 + U ) ) )')], 'cbvsumv', 'sum_ j e. %s %s = sum_ k e. %s %s' % (FZ, J1U, FZ, K1U))], 'x', 'x') if False else \
        si([w.s([w.s([], 'oveq1', '( j = k -> ( j ^c -u ( 1 + U ) ) = ( k ^c -u ( 1 + U ) ) )')], 'cbvsumv', 'sum_ j e. %s %s = sum_ k e. %s %s' % (FZ, J1U, FZ, K1U))], 'a1i',
           'sum_ j e. %s %s = sum_ k e. %s %s' % (FZ, J1U, FZ, K1U))
    Aik = '( %s /\\ k e. NN )' % Ai
    tk, k1r = tval(Aik, w.s([], 'simpr', '( %s -> k e. NN )' % Aik))
    fzs = si([w.s([], 'fzossnn', '( 1 ..^ i ) C_ NN')], 'a1i', '( 1 ..^ i ) C_ NN')
    il = w.s([nnuz, Li(one), fzf, fzs, tk, w.s([k1r], 'rpred', '( %s -> %s e. RR )' % (Aik, K1U)), w.s([k1r], 'rpge0d', '( %s -> 0 <_ %s )' % (Aik, K1U)), Li(zcv)], 'isumless',
             '( %s -> sum_ k e. %s %s <_ %s )' % (Ai, FZ, K1U, ZS_))
    # G ( i ) = ( 1 - i ^c -u U ) / U = TEL / U
    gdiv = si([si([si([Li(uc), si([Li(up)], 'rpne0d', 'U =/= 0'), si([], '1cnd', '1 e. CC'), iuuc], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    lvg = {IU: Li(iurr), IUi: iuur, 'U': Li(ur)}
    gq = si([si([s1 for s1 in []] or [si([], '1cnd', '1 e. CC'), iuuc, Li(uc), si([Li(up)], 'rpne0d', 'U =/= 0')], 'divsubdird', '( ( 1 - %s ) / U ) = ( ( 1 / U ) - ( %s / U ) )' % (IUi, IUi))], 'x', 'x') if False else \
        si([si([], '1cnd', '1 e. CC'), iuuc, Li(uc), si([Li(up)], 'rpne0d', 'U =/= 0')], 'divsubdird', '( ( 1 - %s ) / U ) = ( ( 1 / U ) - ( %s / U ) )' % (IUi, IUi))
    gq2 = si([iuuc, Li(uc), si([Li(up)], 'rpne0d', 'U =/= 0')], 'divrec2d', '( %s / U ) = ( %s x. %s )' % (IUi, IU, IUi))
    gq3 = si([gq, si([gq2], 'oveq2d', '( ( 1 / U ) - ( %s / U ) ) = ( ( 1 / U ) - ( %s x. %s ) )' % (IUi, IU, IUi))], 'eqtrd', '( ( 1 - %s ) / U ) = %s' % (IUi, GI))
    tdiv = si([si([tel2], 'oveq1d', '( %s / U ) = ( ( 1 - %s ) / U )' % (TEL, IUi)), gq3], 'eqtrd', '( %s / U ) = %s' % (TEL, GI))
    ch = si([si([si([gi, si([tdiv], 'eqcomd', '%s = ( %s / U )' % (GI, TEL))], 'eqtrd', '( %s ` i ) = ( %s / U )' % (Gm, TEL)), divs], 'eqtrd', '( %s ` i ) = sum_ j e. %s ( %s / U )' % (Gm, FZ, TJ)),
             si([fle, cvs], 'breqtrd', 'sum_ j e. %s ( %s / U ) <_ sum_ k e. %s %s' % (FZ, TJ, FZ, K1U))], 'eqbrtrd', '( %s ` i ) <_ sum_ k e. %s %s' % (Gm, FZ, K1U))
    gz = si([ch, il], 'letrd' if False else 'x', 'x') if False else None
    sfr = si([fzf, w.s([w.s([w.s([w.s([], 'simpr', '( ( %s /\\ k e. %s ) -> k e. %s )' % (Ai, FZ, FZ)), w.inst('elfzouz')], 'syl', '( ( %s /\\ k e. %s ) -> k e. ( ZZ>= ` 1 ) )' % (Ai, FZ)),
                                   w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr', '( ( %s /\\ k e. %s ) -> k e. NN )' % (Ai, FZ))], 'x', 'x') if False else None], 'x', 'x') if False else None
    Aikf = '( %s /\\ k e. %s )' % (Ai, FZ)
    kfn = w.s([w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Aikf, FZ)), w.inst('elfzouz')], 'syl', '( %s -> k e. ( ZZ>= ` 1 ) )' % Aikf), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')],
              'sylibr', '( %s -> k e. NN )' % Aikf)
    _, kfr = tval(Aikf, kfn)
    sfr = si([fzf, w.s([kfr], 'rpred', '( %s -> %s e. RR )' % (Aikf, K1U))], 'fsumrecl', 'sum_ k e. %s %s e. RR' % (FZ, K1U))
    gz = si([gkr, sfr, Li(zr), ch, il], 'letrd', '( %s ` i ) <_ %s' % (Gm, ZS_))
    gzc = si([gz, si([ck], 'eqcomd', '%s = ( %s ` i )' % (ZS_, CS))], 'breqtrd', '( %s ` i ) <_ ( %s ` i )' % (Gm, CS))
    ren = lambda st, f: w.s([st], 'x', f)
    fin = w.s([nnuz, one, gcv2, ccv2, gkr, ckr, gzc], 'climle', '( %s -> %s <_ %s )' % (A0, IU, ZS_))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['zetalb']))
    return run8(w)


if __name__ == '__main__':
    gen_zlbterm()
    gen_zetalb()
