"""Sortie EF56: the explicit formula at the character mod 1 (ef6z1) and the combined explicit_formula (ef6ef)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_f import c1_facts
from ef4_h import abs_tpi

NX1 = '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1


def gen_z1():
    from ef4_e import box_hp
    from ef4_g import elrab_unpack
    w = W('ef6z1', 'Lean ` explicit_formula ` for the Riemann zeta function (the trivial character mod 1): for ` y >_ 100 ` , ` T >_ 2 ` , ` abs ( psi ( y ) - y + sum_rho m_rho y ^ rho / rho ) <_ 10 ^ 12 ( y log ^ 2 ( T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( T + 2 ) + log ^ 2 ( T y ) ) ` , the sum over the zeros of ` zeta ` in ` [ 1 / 2 , 1 ] x [ - T , T ] ` ( ~ ef1psb , ~ ef6cnt ).')
    A0, G = ante_of(S['ef6z1'])
    c = Ctx(w, A0)
    yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    nx = nx1(w, A0)
    f = c1_facts(w, c, yr, y100)
    cnt = c([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('ef6cnt')], 'syl', CBNDZ)
    PSB = tsub(stmt('ef1psb'), Z1S)
    pba, pbc = ante_of(PSB)
    psb = c([rebuild(w, c, pba, {NX1: nx}), w.inst('ef1psb')], 'syl', pbc)
    RE = tsub(stmt('ef1redge'), dict(Z1S, C=C1))
    rea, rec_ = ante_of(RE)
    red = c([rebuild(w, c, rea, {NX1: nx, 'Y e. RR+': f['yp'], '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g']}), w.inst('ef1redge')], 'syl', rec_)
    cv, pse = top_and(rec_)
    RHL = pse.split(' = ', 1)[1]
    psc = c([c([red, w.inst('simpr')], 'syl', pse), c([c([red, w.inst('simpl')], 'syl', cv), w.inst('climcl')], 'syl', '%s e. CC' % RHL)], 'eqeltrd', '%s e. CC' % PSZ1)
    An = '( %s /\\ n e. ( 1 ... ( |_ ` Y ) ) )' % A0
    cn = Ctx(w, An)
    nin = cn([cn([], 'simpr', 'n e. ( 1 ... ( |_ ` Y ) )'), w.inst('elfznn')], 'syl', 'n e. NN')
    XCn = '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` n ) )' % U1
    tn = cn([cn([cn([lift(w, nx, An), nin], 'jca', '( %s /\\ n e. NN )' % NX1), w.inst('lchrcl')], 'syl', '%s e. CC' % XCn), cn([cn([nin, w.inst('vmacl')], 'syl', '( Lam ` n ) e. RR')], 'recnd', '( Lam ` n ) e. CC')], 'mulcld',
            '( %s x. ( Lam ` n ) ) e. CC' % XCn)
    psic = c([c([], 'fzfid', '( 1 ... ( |_ ` Y ) ) e. Fin'), tn], 'fsumcl', '%s e. CC' % PSIz)
    EZ = tsub(stmt('ezf'), dict(Z1S, A='( 1 / 2 )'))
    eza, ezc = ante_of(EZ)
    ez = c([rebuild(w, c, eza, {NX1: nx, '( 1 / 2 ) e. RR': numst(w, A0, '( 1 / 2 )', 'RR'), '0 < ( 1 / 2 )': c.a1(w.s([], 'halfgt0', '0 < ( 1 / 2 )'), '0 < ( 1 / 2 )'),
                                 '( 1 / 2 ) <_ 1': c.a1(w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], '1re', '1 e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'ltleii', '( 1 / 2 ) <_ 1'), '( 1 / 2 ) <_ 1')}), w.inst('ezf')], 'syl', ezc)
    zfin, zord = conj_split(w, A0, ez)
    Aq = '( %s /\\ q e. %s )' % (A0, CFZ)
    cq = Ctx(w, Aq)
    qz = cq([], 'simpr', 'q e. %s' % CFZ)
    qbx, _, _ = elrab_unpack(w, Aq, 'r', BOX('( 1 / 2 )', 'T'), '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E1, 'q', qz)
    qh = box_hp(w, Aq, 'q', qbx, numst(w, Aq, '( 1 / 2 )', 'RR'), cq.a1(w.s([], 'halfgt0', '0 < ( 1 / 2 )'), '0 < ( 1 / 2 )'), lift(w, tr, Aq), '( 1 / 2 )')
    qc, q0, _ = hp0_facts(cq, 'q', qh)
    qne = ne0_re(cq, 'q', qc, q0)
    EH = '( %s holord q )' % E1
    oq = cq([qz, cq([lift(w, zord, Aq), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (CFZ, EH))], 'mpd', '%s e. NN' % EH)
    tq = cq([cq([oq], 'nncnd', '%s e. CC' % EH), cq([cq([cq([lift(w, f['yp'], Aq)], 'rpcnd', 'Y e. CC'), qc], 'cxpcld', '( Y ^c q ) e. CC'), qc, qne], 'divcld', '( ( Y ^c q ) / q ) e. CC')], 'mulcld',
            '%s e. CC' % TZ)
    scc = c([zfin, tq], 'fsumcl', '%s e. CC' % SCz)
    tpc = c.a1(w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI), '%s e. CC' % TPI)
    ycc = c([yr], 'recnd', 'Y e. CC')
    clz = Closure(w, A0, {PSZ1: ('CC', psc), SCz: ('CC', scc), PSIz: ('CC', psic), TPI: ('CC', tpc), 'Y': ('CC', ycc)})
    for k in (PSZ1, SCz, PSIz, TPI, 'Y'):
        clz.atom(k)
    AA = '( ( %s + ( %s x. %s ) ) - ( %s x. Y ) )' % (PSZ1, TPI, SCz, TPI)
    BB = '( %s - ( %s x. %s ) )' % (PSZ1, TPI, PSIz)
    SUM = '( ( %s - Y ) + %s )' % (PSIz, SCz)
    eq = ringeq(w, A0, '( %s x. %s )' % (TPI, SUM), '( %s - %s )' % (AA, BB), clz)
    aac = clz.mem(AA, 'CC'); bbc = clz.mem(BB, 'CC')
    ad = c([aac, bbc, w.inst('abs2dif2')], 'syl2anc', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (AA, BB, AA, BB))
    PI2 = '( 2 x. _pi )'
    atp = abs_tpi(w, c)
    sc2 = clz.mem(SUM, 'CC')
    am = c([c([tpc, sc2], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TPI, SUM, TPI, SUM)), c([atp], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, SUM, PI2, SUM))], 'eqtrd',
            '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, SUM, PI2, SUM))
    l1 = c([c([c([am], 'eqcomd', '( %s x. ( abs ` %s ) ) = ( abs ` ( %s x. %s ) )' % (PI2, SUM, TPI, SUM)), c([eq], 'fveq2d', '( abs ` ( %s x. %s ) ) = ( abs ` ( %s - %s ) )' % (TPI, SUM, AA, BB))], 'eqtrd',
               '( %s x. ( abs ` %s ) ) = ( abs ` ( %s - %s ) )' % (PI2, SUM, AA, BB)), ad], 'eqbrtrd', '( %s x. ( abs ` %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (PI2, SUM, AA, BB))
    CB = CBNDZ.split(' <_ ', 1)[1]
    PB = pbc.split(' <_ ', 1)[1]
    RHS1 = '( %s + %s )' % (CB, PB)
    tp = c([tr, lin8(w, A0, [t2], '0 < T', {'T': tr})], 'elrpd', 'T e. RR+')
    cl = Closure(w, A0, {'Y': ('RR+', f['yp']), 'T': ('RR+', tp), '_pi': ('RR+', c.a1(w.s([], 'pirp', '_pi e. RR+'), '_pi e. RR+'))})
    LTY = '( log ` ( T x. Y ) )'
    lv1 = {'( abs ` %s )' % AA: c([aac], 'abscld', '( abs ` %s ) e. RR' % AA), '( abs ` %s )' % BB: c([bbc], 'abscld', '( abs ` %s ) e. RR' % BB)}
    for k in (CB, PB):
        lv1[k] = cl.mem(k, 'RR')
    l2 = c([cnt, psb], 'le2addd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ %s' % (AA, BB, RHS1))
    pi2p = c([c.a1(w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), c.a1(w.s([], 'pirp', '_pi e. RR+'), '_pi e. RR+')], 'rpmulcld', '%s e. RR+' % PI2)
    R_ = '( ( %s x. ( %s + %s ) ) + ( ( ; ; 2 0 0 x. ( ( Y x. ( %s ^ 2 ) ) / T ) ) + ( ; 3 0 x. ( %s ^ 2 ) ) ) )' % (KZ, P1z, P2z, LTY, LTY)
    e2 = c([c([numst(w, A0, '2', 'CC'), c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mulcld', '%s e. CC' % PI2), cl.mem('( %s x. ( %s + %s ) )' % (KZ, P1z, P2z), 'CC'),
            cl.mem('( ( ; ; 2 0 0 x. ( ( Y x. ( %s ^ 2 ) ) / T ) ) + ( ; 3 0 x. ( %s ^ 2 ) ) )' % (LTY, LTY), 'CC')], 'adddid', '( %s x. %s ) = %s' % (PI2, R_, RHS1))
    l3 = le_tr(w, A0, l1, '( %s x. ( abs ` %s ) )' % (PI2, SUM), '( ( abs ` %s ) + ( abs ` %s ) )' % (AA, BB), c([l2, c([e2], 'eqcomd', '%s = ( %s x. %s )' % (RHS1, PI2, R_))], 'breqtrd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s x. %s )' % (AA, BB, PI2, R_)),
               '( %s x. %s )' % (PI2, R_))
    asr = c([sc2], 'abscld', '( abs ` %s ) e. RR' % SUM)
    l4 = c([l3, c([asr, cl.mem(R_, 'RR'), pi2p], 'lemul2d', '( ( abs ` %s ) <_ %s <-> ( %s x. ( abs ` %s ) ) <_ ( %s x. %s ) )' % (SUM, R_, PI2, SUM, PI2, R_))], 'mpbird', '( abs ` %s ) <_ %s' % (SUM, R_))
    # log ( ( 1 x. T ) x. Y ) = log ( T x. Y )
    e_t = c([c([c([tr], 'recnd', 'T e. CC')], 'mullidd', '( 1 x. T ) = T')], 'oveq1d', '( ( 1 x. T ) x. Y ) = ( T x. Y )')
    e_l = c([e_t], 'fveq2d', '%s = %s' % (LNYz, LTY))
    e_s = c([e_l], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (LNYz, LTY))
    e_p = c([c([c([e_s], 'oveq2d', '( Y x. ( %s ^ 2 ) ) = ( Y x. ( %s ^ 2 ) )' % (LNYz, LTY))], 'oveq1d', '%s = ( ( Y x. ( %s ^ 2 ) ) / T )' % (P1z, LTY))], 'idi', '%s = ( ( Y x. ( %s ^ 2 ) ) / T )' % (P1z, LTY))
    p10 = c([cl.mem('( Y x. ( %s ^ 2 ) )' % LNYz, 'RR'), tp, c([yr, cl.mem('( %s ^ 2 )' % LNYz, 'RR'), lin8(w, A0, [y100], '0 <_ Y', {'Y': yr}), c([cl.mem(LNYz, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNYz)], 'mulge0d', '0 <_ ( Y x. ( %s ^ 2 ) )' % LNYz)], 'divge0d', '0 <_ %s' % P1z)
    p20 = c([cl.mem('( Y ^c ( 5 / 8 ) )', 'RR'), cl.mem('( %s ^ 2 )' % LNTz, 'RR'), c([c([f['yp'], numst(w, A0, '( 5 / 8 )', 'RR')], 'rpcxpcld', '( Y ^c ( 5 / 8 ) ) e. RR+')], 'rpge0d', '0 <_ ( Y ^c ( 5 / 8 ) )'), c([cl.mem(LNTz, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNTz)], 'mulge0d', '0 <_ %s' % P2z)
    ly0 = c([cl.mem(LNYz, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNYz)
    lvr = {P1z: cl.mem(P1z, 'RR'), P2z: cl.mem(P2z, 'RR'), '( %s ^ 2 )' % LNYz: cl.mem('( %s ^ 2 )' % LNYz, 'RR'), '( %s ^ 2 )' % LTY: cl.mem('( %s ^ 2 )' % LTY, 'RR'), '( ( Y x. ( %s ^ 2 ) ) / T )' % LTY: cl.mem('( ( Y x. ( %s ^ 2 ) ) / T )' % LTY, 'RR')}
    GR = G.split(' <_ ', 1)[1]
    l5 = lin8(w, A0, [e_p, e_s, p10, p20, ly0], '%s <_ %s' % (R_, GR), lvr)
    fin = le_tr(w, A0, l4, '( abs ` %s )' % SUM, R_, l5, GR)
    w.qed([fin], 'idi', S['ef6z1'])
    return run8(w)



def gen_ef():
    w = W('ef6ef', 'Lean ` explicit_formula ` (frozen ledger contract, ` C5 = 10 ^ 12 ` ): for ` chi ` nonprincipal or the trivial character mod 1, ` y >_ 100 ` , ` T >_ 2 ` , ` N <_ y ` , ` abs ( psi ( y , chi ) - [ chi = 1 ] y + sum_rho m_rho y ^ rho / rho ) <_ 10 ^ 12 ( y log ^ 2 ( N T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( N ( T + 2 ) ) + log ^ 2 ( N T y ) ) ` ( ~ ef4ef , ~ ef6z1 ).')
    A0, G = ante_of(S['ef6ef'])
    c = Ctx(w, A0)
    GR = G.split(' <_ ', 1)[1]
    IFX = 'if ( X = %s , Y , 0 )' % U0N
    # case 1: nonprincipal
    A1 = '( %s /\\ X =/= %s )' % (A0, U0N)
    c1 = Ctx(w, A1)
    nx = c1.g(NX)
    xn = c1([], 'simpr', 'X =/= %s' % U0N)
    yr = c1.g('Y e. RR'); y100 = c1.g('; ; 1 0 0 <_ Y'); tr = c1.g('T e. RR'); t2 = c1.g('2 <_ T')
    chi = c1([nx, xn], 'jca', CHI)
    EF4 = stmt('ef4ef')
    e4a, e4c = ante_of(EF4)
    ef4 = c1([rebuild(w, c1, e4a, {CHI: chi}), w.inst('ef4ef')], 'syl', e4c)
    i0 = c1([c1([xn], 'neneqd', '-. X = %s' % U0N)], 'iffalsed', '%s = 0' % IFX)
    An = '( %s /\\ n e. ( 1 ... ( |_ ` Y ) ) )' % A1
    cn = Ctx(w, An)
    nin = cn([cn([], 'simpr', 'n e. ( 1 ... ( |_ ` Y ) )'), w.inst('elfznn')], 'syl', 'n e. NN')
    XCn = '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` n ) )'
    tn = cn([cn([cn([lift(w, nx, An), nin], 'jca', '( %s /\\ n e. NN )' % NX), w.inst('lchrcl')], 'syl', '%s e. CC' % XCn), cn([cn([nin, w.inst('vmacl')], 'syl', '( Lam ` n ) e. RR')], 'recnd', '( Lam ` n ) e. CC')], 'mulcld',
            '( %s x. ( Lam ` n ) ) e. CC' % XCn)
    psic = c1([c1([], 'fzfid', '( 1 ... ( |_ ` Y ) ) e. Fin'), tn], 'fsumcl', '%s e. CC' % PSI)
    ps0 = c1([c1([i0], 'oveq2d', '( %s - %s ) = ( %s - 0 )' % (PSI, IFX, PSI)), c1([psic], 'subid1d', '( %s - 0 ) = %s' % (PSI, PSI))], 'eqtrd', '( %s - %s ) = %s' % (PSI, IFX, PSI))
    lhs = c1([c1([ps0], 'oveq1d', '( ( %s - %s ) + %s ) = ( %s + %s )' % (PSI, IFX, SCE, PSI, SCE))], 'fveq2d', '( abs ` ( ( %s - %s ) + %s ) ) = ( abs ` ( %s + %s ) )' % (PSI, IFX, SCE, PSI, SCE))
    nn = c1([nx, w.inst('simpl')], 'syl', 'N e. NN')
    f = c1_facts(w, c1, yr, y100)
    tp = c1([tr, lin8(w, A1, [t2], '0 < T', {'T': tr})], 'elrpd', 'T e. RR+')
    cl = Closure(w, A1, {'Y': ('RR+', f['yp']), 'T': ('RR+', tp), 'N': ('NN', nn)})
    Q = '( ( %s + %s ) + ( %s ^ 2 ) )' % (P1, P2, LNY)
    p10 = c1([cl.mem('( Y x. ( %s ^ 2 ) )' % LNY, 'RR'), tp, c1([yr, cl.mem('( %s ^ 2 )' % LNY, 'RR'), lin8(w, A1, [y100], '0 <_ Y', {'Y': yr}), c1([cl.mem(LNY, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNY)], 'mulge0d', '0 <_ ( Y x. ( %s ^ 2 ) )' % LNY)], 'divge0d', '0 <_ %s' % P1)
    p20 = c1([cl.mem('( Y ^c ( 5 / 8 ) )', 'RR'), cl.mem('( %s ^ 2 )' % LNT, 'RR'), c1([c1([f['yp'], numst(w, A1, '( 5 / 8 )', 'RR')], 'rpcxpcld', '( Y ^c ( 5 / 8 ) ) e. RR+')], 'rpge0d', '0 <_ ( Y ^c ( 5 / 8 ) )'), c1([cl.mem(LNT, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNT)], 'mulge0d', '0 <_ %s' % P2)
    ly0 = c1([cl.mem(LNY, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNY)
    q0 = lin8(w, A1, [p10, p20, ly0], '0 <_ %s' % Q, {P1: cl.mem(P1, 'RR'), P2: cl.mem(P2, 'RR'), '( %s ^ 2 )' % LNY: cl.mem('( %s ^ 2 )' % LNY, 'RR')})
    kk = lin8(w, A1, [q0], '( %s x. %s ) <_ ( %s x. %s )' % (KE, Q, KF, Q), {Q: cl.mem(Q, 'RR')})
    case1 = c1([c1([lhs, ef4], 'eqbrtrd', '( abs ` ( ( %s - %s ) + %s ) ) <_ ( %s x. %s )' % (PSI, IFX, SCE, KE, Q)), kk], 'x', 'x') if False else None
    A_ = '( abs ` ( ( %s - %s ) + %s ) )' % (PSI, IFX, SCE)
    AR = c1([c1([lhs, c1([c1([psic, c1([cl.mem('( %s ^ 2 )' % LNY, 'RR')], 'x', 'x') if False else psic], 'x', 'x')], 'x', 'x')], 'x', 'x')], 'x', 'x') if False else None
    sce_r = c1([ef4, w.inst('x')], 'x', 'x') if False else None
    lhs2 = c1([lhs, ef4], 'eqbrtrd', '%s <_ ( %s x. %s )' % (A_, KE, Q))
    case1 = le_tr(w, A1, lhs2, A_, '( %s x. %s )' % (KE, Q), kk, '( %s x. %s )' % (KF, Q))
    # case 2: N = 1 , X = 0g
    A2 = '( %s /\\ ( N = 1 /\\ X = %s ) )' % (A0, U0N)
    c2 = Ctx(w, A2)
    n1 = c2([c2([], 'simpr', '( N = 1 /\\ X = %s )' % U0N), w.inst('simpl')], 'syl', 'N = 1')
    x0 = c2([c2([], 'simpr', '( N = 1 /\\ X = %s )' % U0N), w.inst('simpr')], 'syl', 'X = %s' % U0N)
    u0 = c2([c2([n1], 'fveq2d', '( DChr ` N ) = ( DChr ` 1 )')], 'fveq2d', '%s = %s' % (U0N, U1))
    xu = c2([x0, u0], 'eqtrd', 'X = %s' % U1)
    z1 = c2([c2.g(YT), w.inst('ef6z1')], 'syl', S['ef6z1'].split(' -> ', 1)[1][:-2])
    IFZ = 'if ( %s = %s , Y , 0 )' % (U1, U1)
    iy = c2([c2.a1(w.s([], 'eqid', '%s = %s' % (U1, U1)), '%s = %s' % (U1, U1))], 'iftrued', '%s = Y' % IFZ)
    GZ = tsub(G, dict(Z1S))
    lz = c2([c2([c2([iy], 'oveq2d', '( %s - %s ) = ( %s - Y )' % (PSIz, IFZ, PSIz))], 'oveq1d', '( ( %s - %s ) + %s ) = ( ( %s - Y ) + %s )' % (PSIz, IFZ, SCz, PSIz, SCz))], 'fveq2d',
            '( abs ` ( ( %s - %s ) + %s ) ) = ( abs ` ( ( %s - Y ) + %s ) )' % (PSIz, IFZ, SCz, PSIz, SCz))
    gz = c2([lz, z1], 'eqbrtrd', GZ)
    tr_, new = w.wcongr(G, {'N': '1', 'X': U1}, A2, {'N': n1, 'X': xu})
    assert ' '.join(new.split()) == ' '.join(GZ.split()), (new[:300], GZ[:300])
    case2 = c2([gz, tr_], 'mpbird', G)
    orr = c.g('( X =/= %s \\/ ( N = 1 /\\ X = %s ) )' % (U0N, U0N))
    w.qed([case1, case2, orr], 'mpjaodan', S['ef6ef'])
    return run8(w)


GENS = {'ef6z1': gen_z1, 'ef6ef': gen_ef}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
