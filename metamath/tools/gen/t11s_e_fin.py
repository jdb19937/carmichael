"""T11 (scan): Lean's ` scanF_le_B ` at the machine (the frozen ~ tmiscfb ), with the loop letters ` R ` , ` N' ` , ` P' ` ,
` U' ` bound by equations (t11s_d_loop.py ` PSI_T `) until the last step.

  tmiscfp   the prologue: ` moveEntry 1 7 5 ; isZero 1 5 ; moveEntry 7 1 5 ; load' ( carry := !flag , flag := false ) `
            from the data into the family at 0, within ` 4 TMB b ` steps
  tmiscfe   the epilogue: ` moveEntry 1 7 5 ; dropNum 1 ; moveEntry 7 1 5 ` from the family at ` R ` to the frozen post
            (the leftover fuel dropped, the flag kept), within ` 3 TMB b ` steps
  tmiscfa   prologue + loop (~ tmiscfl ) + epilogue, the charges telescoped (~ telfsumo ) and bounded (~ tmscfar )
  tmiscfb   scanF_le_B (the letters instantiated)

    MM_DB=sorties/t11.mm MM_HEAP=16g python3 tools/gen/t11s_e_fin.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11s_d_loop import *
from t10_u_s2s import expose
import t11s_g_far as FAR
t6blib._STMT.update(FAR.STMTS)

SEL = sys.argv[1:]
NF0, PF0 = '( %s ` 0 )' % NV, '( %s ` 0 )' % PV
NFR, PFR = '( %s ` R )' % NV, '( %s ` R )' % PV
P1BND = '( 4 x. ( TMB ` B ) )'
P3BND = '( 3 x. ( TMB ` B ) )'
_C_SCF, DFIN_CLS, _N_SCF = triple_parts(CONCL_SCF)
CONCL_FP = TRI(CS('scf'), CLN(LMF['Z2'], NF0, PF0), P1BND)
CONCL_FE = TRI(CLN(LMF['Y5'], NFR, PFR), DFIN_CLS, P3BND)
for _l, _c in (('tmiscfp', CONCL_FP), ('tmiscfe', CONCL_FE), ('tmiscfa', CONCL_SCF)):
    add11(_l, PSI_T, _c)
    ORDER11.remove(_l)
    ORDER11.insert(ORDER11.index('tmiscfb'), _l)
WZ = '( encNatGam ` Z )'
LWZ = '( # ` %s )' % WZ
P2B = '( 2 ^ B )'


def h_lt(w, ph, B, cl, ghb):
    """( ph -> H < ( 2 ^ B ) ) from ( G + H ) < 2 ^ B"""
    s = w.s
    hr, gr = cl.mem('H', 'RR'), cl.mem('G', 'RR')
    hgh = s([s([hr, gr], 'addge02d', '( %s -> ( 0 <_ G <-> H <_ ( G + H ) ) )' % ph), cl.ge0('G')], 'mpbid', '( %s -> H <_ ( G + H ) )' % ph)
    return s([hr, cl.mem('( G + H )', 'RR'), pnr(w, ph, 'B', B.bn), hgh, ghb], 'lelttrd', '( %s -> H < %s )' % (ph, P2B))


def lwz_facts(w, ph, B, c):
    """( ph -> LWZ e. NN0 ) , ( ph -> LWZ <_ B ) , ( ph -> ( ( 2 x. LWZ ) + 4 ) <_ ( TMB ` B ) ) (~ tmscmeb )"""
    s = w.s
    lwn = s([encw(w, ph, 'Z', B.zn), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LWZ))
    lw = s([s([B.zn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` Z ) ) )' % (ph, LWZ)),
            s([B.zn, B.bn, c[LT2('Z')], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` Z ) ) <_ B )' % ph)], 'eqbrtrd',
           '( %s -> %s <_ B )' % (ph, LWZ))
    mb, _ = inst(w, ph, 'tmscmeb', {'L': LWZ}, Bld(w, ph, c, {'%s e. NN0' % LWZ: lwn, '%s <_ B' % LWZ: lw}))
    return lwn, lw, mb


def tmiscfp():
    lab = 'tmiscfp'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'The prologue of Lean\'s ` scanF ` at the machine: ` z ` is moved aside (~ tmime ), ` isZero 1 5 ` (~ tmiizbs ) '
               'tests the fuel, ` z ` is moved back keeping the flag (~ tmimebo ) and ` load\' ( carry := !flag , flag := false ) ` '
               '(~ tm2flg ) enters the loop family at 0 (its carry ` 0 =/= R ` , its flag off, its stacks the data), within '
               '` 4 TMB b ` steps.')
    s = w.s
    B = Sf(w, ph, T)
    c, mk = B.c, B.mk
    cl = B.cl
    r0 = B.r0
    g = lambda k: B.S0.vals[k][2]
    cl.atom(P2B)
    ghb = c['( G + H ) < ( 2 ^ B )']
    hlt = h_lt(w, ph, B, cl, ghb)
    R = B.run()
    EHX = EWg('H', "X'")
    E7 = EWg('Z', '( D ` 7 )')
    B.call(R, 'tmime', {'K': '1', 'J': '7', 'I': '5', 'W': WZ, 'X': EHX, 'P': PL('P', 2), 'E': LMF['Y2']},
           {WRD(WZ, BITS): engb(w, ph, 'Z', B.zn)},
           [('1', EHX, B.gam[EHX] if EHX in B.gam else B.g(EHX, ewg_(w, ph, 'H', B.hn, "X'", B.x2w))),
            ('7', E7, B.g(E7, ewg_(w, ph, 'Z', B.zn, '( D ` 7 )', g('7'))))])
    B.call(R, 'tmiizbs', {'K': '1', 'I': '5', 'F': 'H', 'N': 'B', 'X': "X'", 'P': PL('P', 3), 'E': LMF['Y3']},
           {'H < %s' % P2B: hlt}, [])
    V = 'if ( H = 0 , 1o , (/) )'
    E1b = EWg('Z', EHX)
    B.call(R, 'tmimebo', {'K': '7', 'J': '1', 'I': '5', 'F': 'Z', 'N': 'B', 'X': '( D ` 7 )', 'O': V, 'P': PL('P', 4), 'E': LMF['Z1']},
           {}, [('7', '( D ` 7 )', g('7')), ('1', E1b, g('1'))])
    kw = lambda t: {'car': 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t, 'fl': '(/)'}
    NO = NFL(V)
    N0c = NCL('0')
    pr = '( %s /\\ r e. %s )' % (ph, NO)
    rr, fr = A8.nfl_unpack(w, pr, V, 'r', s([], 'simpr', '( %s -> r e. %s )' % (pr, NO)))
    nv = lset_val2(w, pr, kw, 'r', rr)
    NR = '( %s ` r )' % L_CNF
    bi0 = r0['( 0 = R <-> H = 0 )']
    cif = s([s([s([fr], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (pr, V)),
                s([s([], 'tmcif1', '( %s = 1o <-> H = 0 )' % V)], 'a1i', '( %s -> ( %s = 1o <-> H = 0 ) )' % (pr, V))], 'bitrd',
               '( %s -> ( ( TMfl ` r ) = 1o <-> H = 0 ) )' % pr), lift_from(w, ph, pr, s([bi0], 'bicomd', '( %s -> ( H = 0 <-> 0 = R ) )' % ph))],
             'bitrd', '( %s -> ( ( TMfl ` r ) = 1o <-> 0 = R ) )' % pr)
    ca = s([nv['fields']['car'], s([cif], 'ifbid', '( %s -> if ( ( TMfl ` r ) = 1o , (/) , 1o ) = if ( 0 = R , (/) , 1o ) )' % pr)], 'eqtrd',
           '( %s -> ( TMcar ` %s ) = if ( 0 = R , (/) , 1o ) )' % (pr, NR))
    fa = s([nv['fields']['fl'], lift_from(w, ph, pr, s([r0['-. %s' % SJ('0')]], 'iffalsed', '( %s -> if ( %s , 1o , (/) ) = (/) )' % (ph, SJ('0'))))],
           'eqtr4d', '( %s -> ( TMfl ` %s ) = if ( %s , 1o , (/) ) )' % (pr, NR, SJ('0')))
    inm = rab_in(w, pr, N0c, lambda t: COND(t, '0'), NR, nv['mem'], s([ca, fa], 'jca', '( %s -> %s )' % (pr, COND(NR, '0'))))
    hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, NO, L_CNF, N0c))
    B.call(R, 'tm2flg', {'A': LMF['Z1'], 'E': LMF['Z2'], 'F': L_CNF, 'N': NO, "N'": N0c},
           {LTY(L_CNF): lset_ty2(w, ph, mk, L_CNF, kw), SSS(NO): B.ss(NO), SSS(N0c): B.ss(N0c),
            'A. r e. %s ( %s ` r ) e. %s' % (NO, L_CNF, N0c): hl}, [])
    cur, out = R.normalize(N8)
    assert out == [('1', E1b)], out
    t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
    assert C1 == CS('scf'), (C1, CS('scf'))
    D1s = triple_D(D1)
    u1 = upidv(w, ph, 'D', '1', E1b, B.S0.vals['1'][1], mk['tv'], B.dd, mk['k']['1']['kd'])
    # PB( 0 ) = D
    z0 = closed(w, ph, '0nn0', '0 e. NN0')
    zle = s([B.rn], 'nn0ge0d', '( %s -> 0 <_ R )' % ph)
    pv0, S0p = B.pv('0', z0, zle)
    nsj0 = r0['-. %s' % SJ('0')]
    g0 = s([s([B.gn], 'nn0cnd', '( %s -> G e. CC )' % ph), w.inst('addrid')], 'syl', '( %s -> ( G + 0 ) = G )' % ph)
    h0 = s([s([B.hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('subid1')], 'syl', '( %s -> ( H - 0 ) = H )' % ph)
    r_0 = {FU('0'): ('H', s([s([nsj0], 'iffalsed', '( %s -> %s = %s )' % (ph, FU('0'), HI('0'))), h0], 'eqtrd', '( %s -> %s = H )' % (ph, FU('0')))),
           KG('0'): ('G', s([s([nsj0], 'iffalsed', '( %s -> %s = %s )' % (ph, KG('0'), GI('0'))), g0], 'eqtrd', '( %s -> %s = G )' % (ph, KG('0')))),
           S6('0'): (D6, s([nsj0], 'iffalsed', '( %s -> %s = %s )' % (ph, S6('0'), D6)))}
    rp0, xp0 = w.rewrite(PB('0'), r_0, ph)
    E2g = EWg('G', 'Y')
    assert xp0 == UP(UP(UP('D', '1', E1b), '2', E2g), '6', D6), xp0
    ra, xa = w.rewrite(xp0, {UP('D', '1', E1b): ('D', u1)}, ph)
    u2 = upidv(w, ph, 'D', '2', E2g, B.S0.vals['2'][1], mk['tv'], B.dd, mk['k']['2']['kd'])
    rb, xb = w.rewrite(xa, {UP('D', '2', E2g): ('D', u2)}, ph)
    u6 = upidv(w, ph, 'D', '6', D6, B.S0.vals['6'][1], mk['tv'], B.dd, mk['k']['6']['kd'])
    assert xb == UP('D', '6', D6), xb
    pd = s([s([s([s([s([pv0, rp0], 'eqtrd', '( %s -> %s = %s )' % (ph, PF0, xp0)), ra], 'eqtrd', '( %s -> %s = %s )' % (ph, PF0, xa)), rb],
                    'eqtrd', '( %s -> %s = %s )' % (ph, PF0, xb)), u6], 'eqtrd', '( %s -> %s = D )' % (ph, PF0))], 'eqcomd',
           '( %s -> D = %s )' % (ph, PF0))
    assert D1s == UP('D', '1', E1b), D1s
    de = s([u1, pd], 'eqtrd', '( %s -> %s = %s )' % (ph, D1s, PF0))
    ceq = s([clnneq(w, ph, LMF['Z2'], s([B.nv('0', z0)], 'eqcomd', '( %s -> %s = %s )' % (ph, N0c, NF0)), N0c, NF0, D1s),
             clneq(w, ph, LMF['Z2'], NF0, de, D1s, PF0)], 'eqtrd', '( %s -> %s = %s )' % (ph, D1, CLN(LMF['Z2'], NF0, PF0)))
    t1, C1, D1, n1 = hrrw(w, ph, t1, C1, D1, n1, deq=ceq)
    # the bound: ( ( ( 2 LWZ + 4 ) + TMB B ) + TMB B ) + 1 <_ 4 TMB B
    lwn, lw, mb = lwz_facts(w, ph, B, c)
    clb = Closure(w, ph, {'B': ('NN0', B.bn)})
    clb.leaf(TBB, 'NN0', tbn(w, ph, 'B', B.bn))
    clb.leaf(LWZ, 'NN0', lwn)
    tb1 = s([s([B.bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TBB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TBB))
    le = linarith(w, ph, [mb, tb1], '%s <_ %s' % (n1, P1BND), closure=clb, atoms=[TBB, LWZ])
    st = hrle(w, ph, mk['phm'], t1, C1, D1, n1, P1BND, clb.mem(P1BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run(unify_only=UO)


def tmiscfe():
    lab = 'tmiscfe'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'The epilogue of Lean\'s ` scanF ` at the machine: from the loop family at ` R ` , ` moveEntry 1 7 5 ; dropNum 1 ; '
               'moveEntry 7 1 5 ` (~ tmimebo , ~ tmidropnb ) drop the leftover fuel keeping the flag, within ` 3 TMB b ` steps; '
               'the flag and stacks 2 and 6 are the frozen ` if ( NONE , .. , .. ) ` forms (~ tmscr0 ).')
    s = w.s
    B = Sf(w, ph, T)
    c, mk = B.c, B.mk
    cl = B.cl
    r0 = B.r0
    g = lambda k: B.S0.vals[k][2]
    cl.atom(P2B)
    ghb = c['( G + H ) < ( 2 ^ B )']
    hlt = h_lt(w, ph, B, cl, ghb)
    rle_ = s([s([B.rn], 'nn0red', '( %s -> R e. RR )' % ph)], 'leidd', '( %s -> R <_ R )' % ph)
    pvR, _ = B.pv('R', B.rn, rle_)
    SR = B.pbst('R', B.rn, rle_)
    VR = 'if ( %s , 1o , (/) )' % SJ('R')
    NVR = NFL(VR)
    FLV = lambda t: '( TMfl ` %s ) = %s' % (t, VR)
    # ( N' ` R ) C_ NFL( VR )
    ssr = rab_h_ss(w, ph, 'TMSt', lambda t: COND(t, 'R'), FLV,
                   lambda pp, t: s([s([], 'simpr', '( %s -> %s )' % (COND(t, 'R'), FLV(t)))], 'a1i', '( %s -> ( %s -> %s ) )' % (pp, COND(t, 'R'), FLV(t))))
    nss = s([B.nv('R', B.rn), ssr], 'eqsstrd', '( %s -> %s C_ %s )' % (ph, NFR, NVR))
    # the epilogue runs on the family stacks at R, a chain of three updates of D (so that the normal form is over D)
    R2 = B.run()
    R2.S = SR
    R2.chain = [('1', E1(FU('R'))), ('2', E2(KG('R'))), ('6', S6('R'))]
    assert chain_text('D', R2.chain) == SR.D, (SR.D,)
    R2.gam.update(B.gam)
    FR = FU('R')
    E1R = EWg(FR, "X'")
    # FU( R ) <_ H < 2 ^ B (~ tmscfue )
    fue, _ = inst(w, ph, 'tmscfue', {}, Bld(w, ph, c, {'R e. NN0': B.rn, 'R <_ H': B.rle}))
    f1 = s([fue], 'simpld', '( %s -> ( ( 1 <_ R -> ( %s + 1 ) <_ H ) /\\ %s <_ H ) )' % (ph, HI('R'), HI('R')))
    fim = s([f1], 'simpld', '( %s -> ( 1 <_ R -> ( %s + 1 ) <_ H ) )' % (ph, HI('R')))
    fle = s([f1], 'simprd', '( %s -> %s <_ H )' % (ph, HI('R')))
    htn = s([fue], 'simprd', '( %s -> %s e. NN0 )' % (ph, HI('R')))
    pa = '( %s /\\ %s )' % (ph, SJ('R'))
    La = lambda x: lift_from(w, ph, pa, x)
    sja = s([], 'simpr', '( %s -> %s )' % (pa, SJ('R')))
    r1a = s([s([s([sja], 'simprd', '( %s -> -. %s )' % (pa, NONE)), La(r0['( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (NONE, KF)])],
               'mpd', '( %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (pa, KF))], 'simpld', '( %s -> 1 <_ R )' % pa)
    fa1 = s([s([sja], 'iftrued', '( %s -> %s = ( %s + 1 ) )' % (pa, FR, HI('R'))), s([r1a, La(fim)], 'mpd', '( %s -> ( %s + 1 ) <_ H )' % (pa, HI('R')))],
            'eqbrtrd', '( %s -> %s <_ H )' % (pa, FR))
    pb = '( %s /\\ -. %s )' % (ph, SJ('R'))
    fb1 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pb, SJ('R')))], 'iffalsed', '( %s -> %s = %s )' % (pb, FR, HI('R'))), lift_from(w, ph, pb, fle)],
            'eqbrtrd', '( %s -> %s <_ H )' % (pb, FR))
    frh = s([fa1, fb1], 'pm2.61dan', '( %s -> %s <_ H )' % (ph, FR))
    frn = s([s([htn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, HI('R'))), htn], 'ifcld', '( %s -> %s e. NN0 )' % (ph, FR))
    cl.leaf(FR, 'NN0', frn)
    frlt = s([cl.mem(FR, 'RR'), cl.mem('H', 'RR'), pnr(w, ph, 'B', B.bn), frh, hlt], 'lelttrd', '( %s -> %s < %s )' % (ph, FR, P2B))
    e1rg = B.g(E1R, ewg_(w, ph, FR, frn, "X'", B.x2w))
    E7b = EWg('Z', '( D ` 7 )')
    B.call(R2, 'tmimebo', {'K': '1', 'J': '7', 'I': '5', 'F': 'Z', 'N': 'B', 'X': E1R, 'O': VR, 'P': PL('P', 6), 'E': LMF['Y6']},
           {}, [('1', E1R, e1rg), ('7', E7b, B.g(E7b, ewg_(w, ph, 'Z', B.zn, '( D ` 7 )', g('7'))))], pre=(NFR, nss))
    Son, old = expose(w, ph, B, R2, '1')
    B.call(R2, 'tmidropnb', {'K': '1', 'F': FR, 'N': 'B', 'X': "X'", 'O': VR, 'P': PL('P', 7), 'E': LMF['Y7']},
           {'%s e. NN0' % FR: frn, '%s < %s' % (FR, P2B): frlt}, [('1', "X'", B.x2w)], on=(Son, old))
    E1f = EWg('Z', "X'")
    B.call(R2, 'tmimebo', {'K': '7', 'J': '1', 'I': '5', 'F': 'Z', 'N': 'B', 'X': '( D ` 7 )', 'O': VR, 'P': PL('P', 8), 'E': 'E'},
           {}, [('7', '( D ` 7 )', g('7')), ('1', E1f, B.g(E1f, ewg_(w, ph, 'Z', B.zn, "X'", B.x2w)))])
    cur, out = R2.normalize(N8)
    assert out == [('1', E1f), ('2', E2(KG('R'))), ('6', S6('R'))], out
    t, C, D, n = R2.tri, R2.C0, R2.cur, R2.n
    assert C == CLN(LMF['Y5'], NFR, SR.D), (C[:300],)
    # the frozen post
    NONEc = NONE
    sjb = s([s([s([], 'eqid', 'R = R')], 'biantrur', '( -. %s <-> %s )' % (NONEc, SJ('R')))], 'a1i',
            '( %s -> ( -. %s <-> %s ) )' % (ph, NONEc, SJ('R')))
    sjb2 = s([sjb], 'bicomd', '( %s -> ( %s <-> -. %s ) )' % (ph, SJ('R'), NONEc))
    IFV_ = lambda a, b: 'if ( %s , %s , %s )' % (NONEc, a, b)
    vr1 = s([sjb2], 'ifbid', '( %s -> %s = if ( -. %s , 1o , (/) ) )' % (ph, VR, NONEc))
    vr2 = s([vr1, s([s([], 'ifnot', 'if ( -. %s , 1o , (/) ) = %s' % (NONEc, IFV_('(/)', '1o')))], 'a1i',
                    '( %s -> if ( -. %s , 1o , (/) ) = %s )' % (ph, NONEc, IFV_('(/)', '1o')))], 'eqtrd', '( %s -> %s = %s )' % (ph, VR, IFV_('(/)', '1o')))
    ENC6 = ENCL(PFS, D6)
    s61 = s([sjb2], 'ifbid', '( %s -> %s = if ( -. %s , %s , %s ) )' % (ph, S6('R'), NONEc, ENC6, D6))
    s62 = s([s61, s([s([], 'ifnot', 'if ( -. %s , %s , %s ) = %s' % (NONEc, ENC6, D6, IFV_(D6, ENC6)))], 'a1i',
                    '( %s -> if ( -. %s , %s , %s ) = %s )' % (ph, NONEc, ENC6, D6, IFV_(D6, ENC6)))], 'eqtrd',
            '( %s -> %s = %s )' % (ph, S6('R'), IFV_(D6, ENC6)))
    IF2 = IFV_(EWg('( G + H )', 'Y'), EWg(KF, 'Y'))
    # stack 2 by cases
    pn = '( %s /\\ %s )' % (ph, NONEc)
    Ln = lambda x: lift_from(w, ph, pn, x)
    nnn = s([s([], 'simpr', '( %s -> %s )' % (pn, NONEc))], 'notnotd', '( %s -> -. -. %s )' % (pn, NONEc))
    nsjn = s([nnn], 'intnand', '( %s -> -. %s )' % (pn, SJ('R')))
    rhn = s([s([], 'simpr', '( %s -> %s )' % (pn, NONEc)), Ln(r0['( %s -> R = H )' % NONEc])], 'mpd', '( %s -> R = H )' % pn)
    kn1 = s([s([nsjn], 'iffalsed', '( %s -> %s = %s )' % (pn, KG('R'), GI('R'))), s([rhn], 'oveq2d', '( %s -> %s = ( G + H ) )' % (pn, GI('R')))],
            'eqtrd', '( %s -> %s = ( G + H ) )' % (pn, KG('R')))
    k2n = s([s([kn1], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` ( G + H ) ) )' % (pn, KG('R')))], 'oveq1d',
            '( %s -> %s = %s )' % (pn, E2(KG('R')), EWg('( G + H )', 'Y')))
    i2n = s([s([], 'simpr', '( %s -> %s )' % (pn, NONEc))], 'iftrued', '( %s -> %s = %s )' % (pn, IF2, EWg('( G + H )', 'Y')))
    e2n = s([k2n, i2n], 'eqtr4d', '( %s -> %s = %s )' % (pn, E2(KG('R')), IF2))
    ps_ = '( %s /\\ -. %s )' % (ph, NONEc)
    Ls = lambda x: lift_from(w, ph, ps_, x)
    nss_ = s([], 'simpr', '( %s -> -. %s )' % (ps_, NONEc))
    sjs = s([s([s([], 'eqid', 'R = R')], 'a1i', '( %s -> R = R )' % ps_), nss_], 'jca', '( %s -> %s )' % (ps_, SJ('R')))
    grk = s([s([nss_, Ls(r0['( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (NONEc, KF)])], 'mpd',
               '( %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (ps_, KF))], 'simprd', '( %s -> ( ( G + R ) - 1 ) = %s )' % (ps_, KF))
    ks1 = s([s([sjs], 'iftrued', '( %s -> %s = ( %s - 1 ) )' % (ps_, KG('R'), GI('R'))), grk], 'eqtrd', '( %s -> %s = %s )' % (ps_, KG('R'), KF))
    k2s = s([s([ks1], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` %s ) )' % (ps_, KG('R'), KF))], 'oveq1d',
            '( %s -> %s = %s )' % (ps_, E2(KG('R')), EWg(KF, 'Y')))
    i2s = s([nss_], 'iffalsed', '( %s -> %s = %s )' % (ps_, IF2, EWg(KF, 'Y')))
    e2s = s([k2s, i2s], 'eqtr4d', '( %s -> %s = %s )' % (ps_, E2(KG('R')), IF2))
    e2 = s([e2n, e2s], 'pm2.61dan', '( %s -> %s = %s )' % (ph, E2(KG('R')), IF2))
    Dst = triple_D(D)
    rf, xf = w.rewrite(Dst, {E2(KG('R')): (IF2, e2), S6('R'): (IFV_(D6, ENC6), s62)}, ph)
    NIF = NFL(IFV_('(/)', '1o'))
    FLI = lambda t: '( TMfl ` %s ) = %s' % (t, IFV_('(/)', '1o'))
    nfe = rab_h_eq(w, ph, 'TMSt', FLV, FLI,
                   lambda pp, t: s([lift_from(w, ph, pp, vr2)], 'eqeq2d', '( %s -> ( %s <-> %s ) )' % (pp, FLV(t), FLI(t))))
    ceqf = s([clnneq(w, ph, 'E', nfe, NVR, NIF, Dst), clneq(w, ph, 'E', NIF, rf, Dst, xf)], 'eqtrd',
             '( %s -> %s = %s )' % (ph, D, CLN('E', NIF, xf)))
    # the pre at ( P' ` R )
    cpre = clneq(w, ph, LMF['Y5'], NFR, s([pvR], 'eqcomd', '( %s -> %s = %s )' % (ph, PB('R'), PFR)), SR.D, PFR)
    t, C, D, n = hrrw(w, ph, t, C, D, n, ceq=cpre, deq=ceqf)
    assert D == DFIN_CLS, (D[:300], DFIN_CLS[:300])
    assert C == CLN(LMF['Y5'], NFR, PFR)
    # the bound: TMB B + TMB B + TMB B = 3 TMB B
    clb = Closure(w, ph, {'B': ('NN0', B.bn)})
    clb.leaf(TBB, 'NN0', tbn(w, ph, 'B', B.bn))
    le = linarith(w, ph, [], '%s <_ %s' % (n, P3BND), closure=clb, atoms=[TBB])
    st = hrle(w, ph, mk['phm'], t, C, D, n, P3BND, clb.mem(P3BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run(unify_only=UO)


def vn_nn0(w, pp, t, tn, tle, f):
    """( pp -> VN( t ) e. NN0 ) from t e. NN0 , t <_ R ; f the facts (lifted to pp)"""
    s = w.s
    rr = lambda st, x: s([st], 'nn0red', '( %s -> %s e. RR )' % (pp, x))
    th = s([rr(tn, t), rr(f['rn'], 'R'), rr(f['hn'], 'H'), tle, f['rle']], 'letrd', '( %s -> %s <_ H )' % (pp, t))
    htn = s([tn, f['hn'], th, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (pp, HI(t)))
    gtn = s([f['gn'], tn], 'nn0addcld', '( %s -> %s e. NN0 )' % (pp, GI(t)))
    b = CA.base4(w, pp, [f['ww'], f['fn'], f['zn'], f['on']], '%s e. NN0' % GI(t), gtn)
    sc = s([s([b, htn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (pp, concl(w, pp, b), HI(t))), w.inst('scancl')], 'syl',
           '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (pp, SCf(GI(t), HI(t))))
    v = s([sc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pp, Vf(t)))
    return s([closed(w, pp, '0nn0', '0 e. NN0'), v], 'ifcld', '( %s -> %s e. NN0 )' % (pp, VN(t)))


def tmiscfa():
    lab = 'tmiscfa'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scanF_le_B ` at the machine, with the loop letters bound by equations: the prologue (~ tmiscfp ), the loop '
               '(~ tmiscfl , ` R ` iterations of ` scanBody ` ), the epilogue (~ tmiscfe ); the per-iteration charges telescope '
               '(~ telfsumo ) to ` 64 U ( scan .. ).2 ` and the whole fits Lean\'s bound (~ tmscfar ).')
    s = w.s
    c = Ctx(w, ph, T)
    phm = c[PHM]
    hn, gn, bn, cn = c['H e. NN0'], c['G e. NN0'], c['B e. NN0'], c['C e. NN0']
    ww, fn, zn, on = c['W e. Word NN0'], c['F e. NN0'], c['Z e. NN0'], c['O e. NN0']
    at = Bld(w, ph, c, {})(AT)
    r0 = CA.r0facts(w, ph, at)
    rn, rle = r0['R e. NN0'], r0['R <_ H']
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn), 'G': ('NN0', gn), 'H': ('NN0', hn), 'R': ('NN0', rn)})
    cl.leaf('( # ` W )', 'NN0', nw)
    msn = cl.mem(MS, 'NN0')
    cl.leaf(UU, 'NN0', tbn(w, ph, MS, msn))
    # ---------------- 1. prologue + loop + epilogue
    tp = lift_from(w, PSI, ph, s([], 'tmiscfp', STMTS11['tmiscfp']))
    tl = lift_from(w, PSI, ph, s([], 'tmiscfl', STMTS11['tmiscfl']))
    te = lift_from(w, PSI, ph, s([], 'tmiscfe', STMTS11['tmiscfe']))
    C1, D1, n1 = triple_parts(CONCL_FP)
    C2, D2, n2 = triple_parts(LCONCL)
    C3, D3, n3 = triple_parts(CONCL_FE)
    assert D1 == C2 and D2 == C3 and C1 == _C_SCF and D3 == DFIN_CLS
    t = hrseq(w, ph, phm, tp, tl, C1, D1, D2, n1, n2)
    n12 = '( %s + %s )' % (n1, n2)
    t = hrseq(w, ph, phm, t, te, C1, D2, D3, n12, n3)
    n = '( %s + %s )' % (n12, n3)
    # ---------------- 2. the charges telescope
    SMT = 'sum_ i e. ( 0 ..^ R ) ( ( %s ` i ) + 1 )' % UV
    assert n2 == '( %s + 1 )' % SMT, n2
    DIF = lambda x: '( ( %s x. %s ) - ( %s x. %s ) )' % (K64, VN(x), K64, VN(J1(x)))
    pi = '( %s /\\ i e. ( 0 ..^ R ) )' % ph
    Li = lambda x: lift_from(w, ph, pi, x)
    io = s([], 'simpr', '( %s -> i e. ( 0 ..^ R ) )' % pi)
    iin = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    i1le = s([io, w.inst('elfzop1le2')], 'syl', '( %s -> ( i + 1 ) <_ R )' % pi)
    i1n = s([iin, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % pi)
    ile = s([s([iin], 'nn0red', '( %s -> i e. RR )' % pi), s([Li(rn)], 'nn0red', '( %s -> R e. RR )' % pi),
             s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % pi)], 'ltled', '( %s -> i <_ R )' % pi)
    fi = {'hn': Li(hn), 'gn': Li(gn), 'rn': Li(rn), 'rle': Li(rle), 'ww': Li(ww), 'fn': Li(fn), 'zn': Li(zn), 'on': Li(on)}
    vi = vn_nn0(w, pi, 'i', iin, ile, fi)
    vi1 = vn_nn0(w, pi, '( i + 1 )', i1n, i1le, fi)
    n64 = lambda pp: s([s([s([], '6nn0', '6 e. NN0'), s([], '4nn0', '4 e. NN0')], 'deccl', '; 6 4 e. NN0')], 'a1i', '( %s -> ; 6 4 e. NN0 )' % pp)
    k64 = s([n64(pi), tbn(w, pi, MS, Li(msn)), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pi, K64))
    ka = s([s([k64], 'nn0cnd', '( %s -> %s e. CC )' % (pi, K64)), s([vi], 'nn0cnd', '( %s -> %s e. CC )' % (pi, VN('i')))], 'mulcld',
           '( %s -> ( %s x. %s ) e. CC )' % (pi, K64, VN('i')))
    kb = s([s([k64], 'nn0cnd', '( %s -> %s e. CC )' % (pi, K64)), s([vi1], 'nn0cnd', '( %s -> %s e. CC )' % (pi, VN('( i + 1 )')))], 'mulcld',
           '( %s -> ( %s x. %s ) e. CC )' % (pi, K64, VN('( i + 1 )')))
    dcc = s([ka, kb], 'subcld', '( %s -> %s e. CC )' % (pi, DIF('i')))
    fam = Li(c['%s = %s' % (UV, UFM)])
    uvi = s([s([fam], 'fveq1d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (pi, UV, UFM)),
             mval(w, pi, 'j', 'NN0', UB, 'i', iin, s([s([], 'ovex', '%s e. _V' % UB('i'))], 'a1i', '( %s -> %s e. _V )' % (pi, UB('i'))))],
            'eqtrd', '( %s -> ( %s ` i ) = %s )' % (pi, UV, UB('i')))
    npc = s([dcc, s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % pi), w.inst('npcan')], 'syl2anc',
            '( %s -> ( %s + 1 ) = %s )' % (pi, UB('i'), DIF('i')))
    term = s([s([uvi], 'oveq1d', '( %s -> ( ( %s ` i ) + 1 ) = ( %s + 1 ) )' % (pi, UV, UB('i'))), npc], 'eqtrd',
             '( %s -> ( ( %s ` i ) + 1 ) = %s )' % (pi, UV, DIF('i')))
    se_ = s([term], 'sumeq2dv', '( %s -> %s = sum_ i e. ( 0 ..^ R ) %s )' % (ph, SMT, DIF('i')))
    KA = lambda x: '( %s x. %s )' % (K64, VN(x))

    def kcong(a_):
        e = s([], 'id', '( k = %s -> k = %s )' % (a_, a_))
        cg, new = w.congr(KA('k'), {'k': a_}, 'k = %s' % a_, {'k': e})
        assert new == KA(a_), new
        return cg
    ruz = s([rn, s([s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % ph)], 'eleqtrd', '( %s -> R e. ( ZZ>= ` 0 ) )' % ph)
    pk = '( %s /\\ k e. ( 0 ... R ) )' % ph
    Lk = lambda x: lift_from(w, ph, pk, x)
    kk = s([], 'simpr', '( %s -> k e. ( 0 ... R ) )' % pk)
    kn = s([kk, w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    kle = s([kk, w.inst('elfzle2')], 'syl', '( %s -> k <_ R )' % pk)
    fk = {x: Lk(y) for x, y in (('hn', hn), ('gn', gn), ('rn', rn), ('rle', rle), ('ww', ww), ('fn', fn), ('zn', zn), ('on', on))}
    vk = vn_nn0(w, pk, 'k', kn, kle, fk)
    k64k = s([n64(pk), tbn(w, pk, MS, Lk(msn)), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pk, K64))
    kac = s([s([k64k], 'nn0cnd', '( %s -> %s e. CC )' % (pk, K64)), s([vk], 'nn0cnd', '( %s -> %s e. CC )' % (pk, VN('k')))], 'mulcld',
            '( %s -> %s e. CC )' % (pk, KA('k')))
    tel = s([kcong('i'), kcong('( i + 1 )'), kcong('0'), kcong('R'), ruz, kac], 'telfsumo',
            '( %s -> sum_ i e. ( 0 ..^ R ) %s = ( %s - %s ) )' % (ph, DIF('i'), KA('0'), KA('R')))
    stl = s([se_, tel], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (ph, SMT, KA('0'), KA('R')))
    SC2_ = SC2
    k0 = s([r0['%s = %s' % (VN('0'), SC2)]], 'oveq2d', '( %s -> %s = ( %s x. %s ) )' % (ph, KA('0'), K64, SC2_))
    kR0 = s([r0['%s = 0' % VN('R')]], 'oveq2d', '( %s -> %s = ( %s x. 0 ) )' % (ph, KA('R'), K64))
    scc = s([CA.base4(w, ph, [ww, fn, zn, on], 'G e. NN0', gn), hn], 'jca',
            '( %s -> ( ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ G e. NN0 ) /\\ H e. NN0 ) )' % ph)
    sc2n = s([s([scc, w.inst('scancl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, SC)), w.inst('xp2nd')], 'syl',
             '( %s -> %s e. NN0 )' % (ph, SC2_))
    cl.leaf(SC2_, 'NN0', sc2n)
    KS = '( %s x. %s )' % (K64, SC2_)
    kR = s([kR0, s([cl.mem(K64, 'CC')], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (ph, K64))], 'eqtrd', '( %s -> %s = 0 )' % (ph, KA('R')))
    smt2 = s([s([stl, s([k0, kR], 'oveq12d', '( %s -> ( %s - %s ) = ( %s - 0 ) )' % (ph, KA('0'), KA('R'), KS))], 'eqtrd',
               '( %s -> %s = ( %s - 0 ) )' % (ph, SMT, KS)), s([cl.mem(KS, 'CC')], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (ph, KS, KS))], 'eqtrd',
             '( %s -> %s = %s )' % (ph, SMT, KS))
    rn_, nx = w.rewrite(n, {SMT: (KS, smt2)}, ph)
    # ---------------- 3. the bound (~ tmscfar at N := # W , S := ( scan .. ).2 )
    m = {'N': '( # ` W )', 'S': SC2_}
    far, cfar = inst(w, ph, 'tmscfar', m, Bld(w, ph, c, {'( # ` W ) e. NN0': nw, '%s e. NN0' % SC2_: sc2n}))
    LHSi, BND = tsub_text(FAR.LHS_FAR, m), tsub_text(FAR.BND_FAR, m)
    assert nx == LHSi, (nx, LHSi)
    assert BND == _N_SCF, (BND, _N_SCF)
    le = s([far], 'simpld', '( %s -> %s <_ %s )' % (ph, LHSi, BND))
    bndn = s([far], 'simprd', '( %s -> %s e. NN0 )' % (ph, BND))
    t, C, D, n = hrrw(w, ph, t, C1, D3, n, neq=rn_)
    assert n == nx
    st = hrle(w, ph, phm, t, C, D, n, BND, bndn, le)
    finish(w, st, lab)
    return w.run(unify_only=UO)


def tmiscfb():
    lab = 'tmiscfb'
    ph = cj(TREE_SCF)
    w = W(lab, 'Lean\'s ` scanF_le_B ` at the machine (Steps23.lean, Step5\'s consumer): with ` Q ` of numbers in ` [ 1 , 2 ^ bq ) ` '
               'on 4, ` x ` and ` theta ` on 0, ` z ` and the fuel on 1, ` k ` on 2 and ` x z theta k + fuel < 2 ^ b ` , the machine '
               'ends with the flag set exactly on success, the fuel dropped, ` k\' ` (or ` k + fuel ` ) on 2 and the pool (or nothing) '
               'pushed on 6, within ` ( ( scan Q x z theta k fuel ).2 + 1 ) B ( 48 ( # Q + 1 ) ( bq + b ) + 4 # Q + 102 ) ` steps '
               '(~ tmiscfa at the loop letters).')
    s = w.s
    c = Ctx(w, ph, TREE_SCF)
    m = {'R': RV, NV: tsub_text(NFM, {'R': RV}), PV: tsub_text(PFM, {'R': RV}), UV: tsub_text(UFM, {'R': RV})}
    ex = {}
    for k_ in ('R', NV, PV, UV):
        v = m[k_]
        eqt = '%s = %s' % (v, v)
        ex[eqt] = s([s([], 'eqid', eqt)], 'a1i', '( %s -> %s )' % (ph, eqt))
    st, cc = inst(w, ph, 'tmiscfa', m, Bld(w, ph, c, ex))
    assert cc == CONCL_SCF
    qed_as(w, st, STMTS11[lab])
    return w.run(unify_only=UO)


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
