"""T7c: Lean's ` isPrimeTDF ` at the machine (T7b-HANDOFF item 4): ~ tm2fipt at TMIipt.

  tmienc2   ( encNatGam ` 2 ) pushed as its two bits: the stack word of ` pushNum x 2 `
  tmipt1    pushNum s 2 ; dup xm t u ; cmpFrag t s        (the ` m < 2 ` test)
  tmipt2    pushNum xd 2 ; dup xm xf s                     (the loop's counters)
  tmipt3    primeGoF (~ tmipgr at d = 2 , fuel = m )
  tmipt4    dropNum xd ; dropNum xf , the flag kept
  tmiptr    ~ tm2fipt assembled ( R , S letters)
  tmiptb    Lean ` isPrimeTDF_le_B `

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_e_ipt.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *
from cl import Closure
import lin
from lin import linarith, lineq, nlinarith
from t7_v_leb import tmb_lin
from t7b_h_dmq import ifmax_le, rab_elim
import t7c_d_pgl as PGL

lin.FASTPATH = True
SEL = sys.argv[1:]

IPT = FRAGS['ipt']
LM = IPT.lmap()
Z0 = '<. 1 , (/) >.'
B1 = '<. 1 , 1o >.'
PUSH2 = lambda X: '( <" %s "> ++ ( <" %s "> ++ ( <" 4 "> ++ %s ) ) )' % (Z0, B1, X)
ST_ENC2 = "( X e. Word Gamma' -> %s = %s )" % (EW('2', 'X'), PUSH2('X'))


def tmienc2():
    lab = 'tmienc2'
    ph = "X e. Word Gamma'"
    w = W(lab, 'The stack word of ` pushNum x 2 ` (Lean ` encodeNatGamma 2 ++ comma :: _ ` ): the two bits of '
               '` 2 ` , least significant first, then the terminator.')
    c0 = closed(w, ph, '0nn0', '0 e. NN0')
    c1 = closed(w, ph, '1nn0', '1 e. NN0')
    a1 = w.s([c0, w.inst('encnatsuc')], 'syl', '( %s -> ( encodeNat ` ( 0 + 1 ) ) = ( incBits ` ( encodeNat ` 0 ) ) )' % ph)
    a2 = w.s([closed(w, ph, '0p1e1', '( 0 + 1 ) = 1')], 'fveq2d', '( %s -> ( encodeNat ` ( 0 + 1 ) ) = ( encodeNat ` 1 ) )' % ph)
    a3 = w.s([closed(w, ph, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'fveq2d', '( %s -> ( incBits ` ( encodeNat ` 0 ) ) = ( incBits ` (/) ) )' % ph)
    e1 = w.s([w.s([w.s([a2, a1], 'eqtr3d', '( %s -> ( encodeNat ` 1 ) = ( incBits ` ( encodeNat ` 0 ) ) )' % ph), a3], 'eqtrd',
                  '( %s -> ( encodeNat ` 1 ) = ( incBits ` (/) ) )' % ph), closed(w, ph, 'incbitsnil', '( incBits ` (/) ) = <" 1o ">')],
             'eqtrd', '( %s -> ( encodeNat ` 1 ) = <" 1o "> )' % ph)
    b1 = w.s([c1, w.inst('encnatsuc')], 'syl', '( %s -> ( encodeNat ` ( 1 + 1 ) ) = ( incBits ` ( encodeNat ` 1 ) ) )' % ph)
    b2 = w.s([closed(w, ph, '1p1e2', '( 1 + 1 ) = 2')], 'fveq2d', '( %s -> ( encodeNat ` ( 1 + 1 ) ) = ( encodeNat ` 2 ) )' % ph)
    b3 = w.s([e1], 'fveq2d', '( %s -> ( incBits ` ( encodeNat ` 1 ) ) = ( incBits ` <" 1o "> ) )' % ph)
    o2 = closed(w, ph, '1oel2o', '1o e. 2o')
    s1 = w.s([o2], 's1cld', '( %s -> <" 1o "> e. Word 2o )' % ph)
    b4 = w.s([s1, w.inst('ccatrid')], 'syl', '( %s -> ( <" 1o "> ++ (/) ) = <" 1o "> )' % ph)
    b4c = w.s([b4], 'fveq2d', '( %s -> ( incBits ` ( <" 1o "> ++ (/) ) ) = ( incBits ` <" 1o "> ) )' % ph)
    w0 = closed(w, ph, 'wrd0', '(/) e. Word 2o')
    b5 = w.s([w0, w.inst('incbitscons1')], 'syl', '( %s -> ( incBits ` ( <" 1o "> ++ (/) ) ) = ( <" (/) "> ++ ( incBits ` (/) ) ) )' % ph)
    b6 = w.s([closed(w, ph, 'incbitsnil', '( incBits ` (/) ) = <" 1o ">')], 'oveq2d',
             '( %s -> ( <" (/) "> ++ ( incBits ` (/) ) ) = ( <" (/) "> ++ <" 1o "> ) )' % ph)
    inc1 = w.s([w.s([b4c, b5], 'eqtr3d', '( %s -> ( incBits ` <" 1o "> ) = ( <" (/) "> ++ ( incBits ` (/) ) ) )' % ph), b6], 'eqtrd',
               '( %s -> ( incBits ` <" 1o "> ) = ( <" (/) "> ++ <" 1o "> ) )' % ph)
    E2 = '( <" (/) "> ++ <" 1o "> )'
    e2 = w.s([w.s([w.s([b2, b1], 'eqtr3d', '( %s -> ( encodeNat ` 2 ) = ( incBits ` ( encodeNat ` 1 ) ) )' % ph), b3], 'eqtrd',
                  '( %s -> ( encodeNat ` 2 ) = ( incBits ` <" 1o "> ) )' % ph), inc1], 'eqtrd', '( %s -> ( encodeNat ` 2 ) = %s )' % (ph, E2))
    g1 = w.s([closed(w, ph, '2nn0', '2 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 2 ) = ( inclBool o. ( encodeNat ` 2 ) ) )' % ph)
    g1b = w.s([g1, w.s([e2], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 2 ) ) = ( inclBool o. %s ) )' % (ph, E2))], 'eqtrd',
              '( %s -> ( encNatGam ` 2 ) = ( inclBool o. %s ) )' % (ph, E2))
    z2 = closed(w, ph, '0el2o', '(/) e. 2o')
    s0 = w.s([z2], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ph)
    ff = closed(w, ph, 'inclboolf', "inclBool : 2o --> Gamma'")
    g2 = w.s([s0, s1, ff, w.inst('ccatco')], 'syl3anc',
             '( %s -> ( inclBool o. %s ) = ( ( inclBool o. <" (/) "> ) ++ ( inclBool o. <" 1o "> ) ) )' % (ph, E2))
    h0 = w.s([z2, ff, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" (/) "> ) = <" ( inclBool ` (/) ) "> )' % ph)
    h0b = w.s([h0, w.s([w.s([z2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ph, Z0))], 's1eqd',
                       '( %s -> <" ( inclBool ` (/) ) "> = <" %s "> )' % (ph, Z0))], 'eqtrd', '( %s -> ( inclBool o. <" (/) "> ) = <" %s "> )' % (ph, Z0))
    h1 = w.s([o2, ff, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" 1o "> ) = <" ( inclBool ` 1o ) "> )' % ph)
    h1b = w.s([h1, w.s([w.s([o2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = %s )' % (ph, B1))], 's1eqd',
                       '( %s -> <" ( inclBool ` 1o ) "> = <" %s "> )' % (ph, B1))], 'eqtrd', '( %s -> ( inclBool o. <" 1o "> ) = <" %s "> )' % (ph, B1))
    AB = '( <" %s "> ++ <" %s "> )' % (Z0, B1)
    g3 = w.s([g2, w.s([h0b, h1b], 'oveq12d', '( %s -> ( ( inclBool o. <" (/) "> ) ++ ( inclBool o. <" 1o "> ) ) = %s )' % (ph, AB))], 'eqtrd',
             '( %s -> ( inclBool o. %s ) = %s )' % (ph, E2, AB))
    g4 = w.s([g1b, g3], 'eqtrd', '( %s -> ( encNatGam ` 2 ) = %s )' % (ph, AB))
    k1 = w.s([g4], 'oveq1d', '( %s -> %s = ( %s ++ ( <" 4 "> ++ X ) ) )' % (ph, EW('2', 'X'), AB))
    gz = w.s([w.s([z2, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, Z0))], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, Z0))
    gb = w.s([w.s([o2, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1))], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1))
    x4 = wg4(w, ph, 'X', w.s([], 'id', "( %s -> X e. Word Gamma' )" % ph))
    k2 = w.s([gz, gb, x4, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ ( <" 4 "> ++ X ) ) = %s )' % (ph, AB, PUSH2('X')))
    w.qed([k1, k2], 'eqtrd', ST_ENC2)
    return w.run()


TB = '( TMB ` N )'
TB1 = '( TMB ` ( N + 1 ) )'
NUMS1 = ('F e. NN0', 'N e. NN0', 'F < ( 2 ^ N )')
DATA1 = (NUMS1, (WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % EW('F', 'X'))
N1C = '{ h e. TMSt | ( TMcmp ` h ) = ( F Ncmp 2 ) }'
T1B = '( ( 2 x. %s ) + 3 )' % TB
T2B = '( %s + 3 )' % TB
DP = UP(UP('D', 'J', EW('2', '( D ` J )')), 'I', EW('F', '( D ` I )'))
RV2 = '( 2nd ` ( ( F PrimeGo 2 ) ` F ) )'
QV2 = '( 1st ` ( ( F PrimeGo 2 ) ` F ) )'
SV2 = tsub_text(PGL.SV, {'G': '2', 'H': 'F'})
DPP = UP(UP('D', 'J', EW('( 2 + S )', '( D ` J )')), 'I', EW('( F - S )', '( D ` I )'))
QCLS2 = '{ h e. TMSt | ( TMfl ` h ) = %s }' % QV2
NIP = '{ h e. TMSt | ( TMfl ` h ) = ( 1st ` ( IsPrimeTD ` F ) ) }'
BND3 = tsub_text(PGL.BND_R, {'N': '( N + 1 )'})
T4B = '( 2 x. %s )' % TB1
DATA3 = (NUMS1, ('-. F < 2', 'R = %s' % RV2, 'S = %s' % SV2), ((WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % EW('F', 'X')))
DATAR = (NUMS1, ('R = %s' % RV2, 'S = %s' % SV2), ((WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % EW('F', 'X')))


def STMT(lab):
    head = ((T_PHM7, IPT.pred()), (idx_tree(K6), dist_tree(K6)))
    if lab == 'tmipt1':
        return head + (DATA1,), TRI(CLN(LM['P0'], SS, 'D'), CLN(LM["B'"], N1C, 'D'), T1B)
    if lab == 'tmipt2':
        return head + (DATA1,), TRI(CLN(LM['E0'], N1C, 'D'), CLN(LM["E'"], SS, DP), T2B)
    if lab == 'tmipt3':
        return head + (DATA3,), TRI(CLN(LM["E'"], SS, DP), CLN(LM['E"'], QCLS2, DPP), BND3)
    if lab == 'tmipt4':
        return head + (DATA3,), TRI(CLN(LM['E"'], QCLS2, DPP), CLN('E', NIP, 'D'), T4B)


def start(lab, desc, deep=()):
    T, C = STMT(lab)
    ph = cj(T)
    w = W(lab, desc)
    c, mk, ne, base = setup(w, ph, T, K6, IPT.pred(), 'ipt')
    for fname, ks, P_, E_ in deep:
        pr = FRAGS[fname].pred(ks, 'T', 'M', P_, E_)
        base.update(unfold_all(w, ph, base[pr], fname, ks, P_, E_, rec=False))
    return T, C, ph, w, c, mk, ne, base


def stacks0(w, ph, c, mk, ne, known):
    dd = c[STKD('D')]
    vals = {}
    for s_ in K6:
        vals[s_] = known[s_] if s_ in known else selfval(w, ph, mk, 'D', dd, s_)
    return Stacks(w, ph, mk, 'D', dd, ne, vals)


def eqv(S, s_, val):
    txt, st, g = S.vals[s_]
    assert txt == val, (txt, val)
    return {'( %s ` %s ) = %s' % (S.D, s_, val): st}


def letg(w, ph, mk, s_, Z, zg):
    return w.s([zg, mk['k'][s_]['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, Z, GX(s_)))


def pushes(w, ph, run, mk, s_, labs, cls, nss):
    """the three pushes of ` pushNum s 2 ` on stack s_ at the labels labs = ( A0 , A1 , A2 , exit )"""
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    gz = w.s([closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, Z0))
    gb = w.s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1))
    old, oldst, oldg = run.S.vals[s_]
    cur = old
    curg = oldg
    for k, (Z, zg) in enumerate([('4', g4), (B1, gb), (Z0, gz)]):
        new = '( <" %s "> ++ %s )' % (Z, cur)
        ng = wgcat(w, ph, '<" %s ">' % Z, cur, w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, Z)), curg)
        ex = {'%s e. %s' % (Z, GX(s_)): letg(w, ph, mk, s_, Z, zg), '%s C_ ( 2nd ` T )' % cls: nss}
        run.call('tm2fpshn', {'A': labs[k], 'E': labs[k + 1], 'K': s_, 'Z': Z, 'N': cls}, ex, [(s_, new, ng)])
        cur, curg = new, ng
    assert cur == PUSH2(old), cur
    return old


def enc2_eq(w, ph, S, s_, old, oldg):
    """( ph -> ( Dcur ` s_ ) = ( ( inclBool o. ( encodeNat ` 2 ) ) ++ ( <" 4 "> ++ old ) ) ) and the EW form"""
    e = w.s([oldg, w.inst('tmienc2')], 'syl', '( %s -> %s = %s )' % (ph, EW('2', old), PUSH2(old)))
    v = w.s([S.vals[s_][1], e], 'eqtr4d', '( %s -> ( %s ` %s ) = %s )' % (ph, S.D, s_, EW('2', old)))
    gv = w.s([closed(w, ph, '2nn0', '2 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 2 ) = ( inclBool o. ( encodeNat ` 2 ) ) )' % ph)
    v2 = w.s([v, w.s([gv], 'oveq1d', '( %s -> %s = %s )' % (ph, EW('2', old), CC('( inclBool o. ( encodeNat ` 2 ) )', YX(old))))], 'eqtrd',
             '( %s -> ( %s ` %s ) = %s )' % (ph, S.D, s_, CC('( inclBool o. ( encodeNat ` 2 ) )', YX(old))))
    return v, v2, e


def tmipt1():
    lab = 'tmipt1'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The ` m < 2 ` test of Lean\'s ` isPrimeTDF xm xd xf s t u ` , ` pushNum s 2 ; dup xm t u ; cmpFrag t s ` , '
        'wherever ` isPrimeTDF ` is installed: ` cmp ` compares ` m ` with ` 2 ` and every stack is restored.',
        deep=[('dup', ['K', 'I"', 'I0'], PL('P', 8), PL(PL('P', 9), 0))])
    fn, nn = c['F e. NN0'], c['N e. NN0']
    xg = c[WRD('X', GAM)]
    S0 = stacks0(w, ph, c, mk, ne, {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ph, 'F', fn, 'X', xg))})
    run = Run(w, ph, mk, S0, base, c)
    ssid = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    old = pushes(w, ph, run, mk, "I'", [PL('P', 0), PL('P', 1), PL('P', 2), PL(PL('P', 8), 0)], SS, ssid)
    DV = lambda s_: '( D ` %s )' % s_
    dg = lambda s_: S0.vals[s_][2]
    run.call('tmidupb', {'K': 'K', 'J': 'I"', 'I': 'I0', 'F': 'F', 'X': 'X', 'P': PL('P', 8), 'E': PL(PL('P', 9), 0)},
             eqv(run.S, 'K', EW('F', 'X')), [('I"', EW('F', DV('I"')), ewg(w, ph, 'F', fn, DV('I"'), dg('I"')))])
    S = run.S
    EF, E2 = ENC('F'), ENC('2')
    v, v2, _ = enc2_eq(w, ph, S, "I'", DV("I'"), dg("I'"))
    gvf = w.s([fn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = ( inclBool o. %s ) )' % (ph, EF))
    vf = w.s([S.vals['I"'][1], w.s([gvf], 'oveq1d', '( %s -> %s = %s )' % (ph, EW('F', DV('I"')), CC('( inclBool o. %s )' % EF, YX(DV('I"')))))], 'eqtrd',
             '( %s -> ( %s ` I" ) = %s )' % (ph, S.D, CC('( inclBool o. %s )' % EF, YX(DV('I"')))))
    ef = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    two = closed(w, ph, '2nn0', '2 e. NN0')
    e2w = w.s([two, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, E2))
    ex5 = {'( %s ` I" ) = %s' % (S.D, CC('( inclBool o. %s )' % EF, YX(DV('I"')))): vf,
           "( %s ` I' ) = %s" % (S.D, CC('( inclBool o. %s )' % E2, YX(DV("I'")))): v2,
           WRD(EF, '2o'): ef, WRD(E2, '2o'): e2w, WRD(DV("I'"), GAM): dg("I'"), WRD(DV('I"'), GAM): dg('I"')}
    tf = w.s([fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, EF))
    t2 = w.s([two, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = 2 )' % (ph, E2))
    nc = w.s([tf, t2], 'oveq12d', '( %s -> ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) = ( F Ncmp 2 ) )' % (ph, EF, E2))
    OLD = '{ h e. TMSt | ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) }' % (EF, E2)
    ce = w.s([nc], 'eqeq2d', '( %s -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) <-> ( TMcmp ` h ) = ( F Ncmp 2 ) ) )' % (ph, EF, E2))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) <-> ( TMcmp ` h ) = ( F Ncmp 2 ) ) )'
                  % (ph, EF, E2))], 'rabbidva', '( %s -> %s = %s )' % (ph, OLD, N1C))
    run.call('tmicmp', {'K': 'I"', 'J': "I'", 'L': EF, "L'": E2, 'X': DV('I"'), 'Y': DV("I'"), 'P': PL('P', 9), 'E': PL('P', 3)},
             ex5, [('I"', DV('I"'), dg('I"')), ("I'", DV("I'"), dg("I'"))], cls_rw=(rb, N1C))
    cur, out = run.normalize(K6)
    assert out == [], out
    assert cur == CLN(PL('P', 3), N1C, 'D'), cur
    # the bound
    LF, L2 = '( # ` %s )' % EF, '( # ` %s )' % E2
    cl = Closure(w, ph, {'N': ('NN0', nn), 'F': ('NN0', fn)})
    lf = w.s([fn, nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, LF))
    four = w.s([closed(w, ph, '2lt4', '2 < 4'), w.s([closed(w, ph, 'sq2', '( 2 ^ 2 ) = 4')], 'eqcomd', '( %s -> 4 = ( 2 ^ 2 ) )' % ph)], 'breqtrd',
               '( %s -> 2 < ( 2 ^ 2 ) )' % ph)
    l2 = w.s([two, two, four, w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ 2 )' % (ph, L2))
    cl.leaf(LF, 'NN0', w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LF)))
    cl.leaf(L2, 'NN0', w.s([e2w, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, L2)))
    NB = '( N + 2 )'
    a1 = linarith(w, ph, [lf, cl.ge0('N')], '%s <_ %s' % (LF, NB), closure=cl)
    a2 = linarith(w, ph, [l2, cl.ge0('N')], '%s <_ %s' % (L2, NB), closure=cl)
    MX = 'if ( %s <_ %s , %s , %s )' % (LF, L2, L2, LF)
    mx = ifmax_le(w, ph, LF, L2, NB, cl.mem(LF, 'RR'), cl.mem(L2, 'RR'), cl.mem(NB, 'RR'), a1, a2)
    cl.leaf(MX, 'NN0', w.s([cl.mem(L2, 'NN0'), cl.mem(LF, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MX)))
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    cl.leaf(TB, 'NN0', tbn)
    tl = tmb_lin(w, ph, nn, '2')
    le = linarith(w, ph, [mx, tl, cl.ge0('N'), cl.ge0(TB)], '%s <_ %s' % (run.n, T1B), closure=cl)
    hrle(w, ph, mk['phm'], run.tri, run.C0, run.cur, run.n, T1B, cl.mem(T1B, 'NN0'), le, qed=True)
    return w.run()


def tmipt2():
    lab = 'tmipt2'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The counters of Lean\'s ` isPrimeTDF xm xd xf s t u ` in the case ` 2 <_ m ` , ` pushNum xd 2 ; dup xm xf s ` , '
        'wherever ` isPrimeTDF ` is installed: the divisor ` 2 ` on ` xd ` and the fuel ` m ` on ` xf ` .',
        deep=[('dup', ['K', 'I', "I'"], PL('P', 10), LM["E'"])])
    fn, nn = c['F e. NN0'], c['N e. NN0']
    xg = c[WRD('X', GAM)]
    S0 = stacks0(w, ph, c, mk, ne, {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ph, 'F', fn, 'X', xg))})
    run = Run(w, ph, mk, S0, base, c)
    nss = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % N1C)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, N1C)), mk['seq']], 'sseqtrrd',
              '( %s -> %s C_ ( 2nd ` T ) )' % (ph, N1C))
    old = pushes(w, ph, run, mk, 'J', [PL('P', 5), PL('P', 6), PL('P', 7), PL(PL('P', 10), 0)], N1C, nss)
    DV = lambda s_: '( D ` %s )' % s_
    dg = lambda s_: S0.vals[s_][2]
    run.call('tmidupb', {'K': 'K', 'J': 'I', 'I': "I'", 'F': 'F', 'X': 'X', 'P': PL('P', 10), 'E': LM["E'"]},
             eqv(run.S, 'K', EW('F', 'X')), [('I', EW('F', DV('I')), ewg(w, ph, 'F', fn, DV('I'), dg('I')))], pre=(N1C, nss))
    # the J value in the EW form
    e = w.s([dg('J'), w.inst('tmienc2')], 'syl', '( %s -> %s = %s )' % (ph, EW('2', DV('J')), PUSH2(DV('J'))))
    DQ = UP(UP('D', 'J', PUSH2(DV('J'))), 'I', EW('F', DV('I')))
    run.normalize(K6)
    assert run.S.D == DQ, run.S.D
    r, new = w.rewrite(DQ, {PUSH2(DV('J')): (EW('2', DV('J')), w.s([e], 'eqcomd', '( %s -> %s = %s )' % (ph, PUSH2(DV('J')), EW('2', DV('J')))))}, ph)
    assert new == DP, new
    d = clneq(w, ph, LM["E'"], SS, r, DQ, DP)
    t2, C2, D2, n2 = hrrw(w, ph, run.tri, run.C0, run.cur, run.n, deq=d)
    cl = Closure(w, ph, {'N': ('NN0', nn)})
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    cl.leaf(TB, 'NN0', tbn)
    le = linarith(w, ph, [cl.ge0(TB)], '%s <_ %s' % (n2, T2B), closure=cl)
    hrle(w, ph, mk['phm'], t2, C2, D2, n2, T2B, cl.mem(T2B, 'NN0'), le, qed=True)
    return w.run()


def big_facts(w, ph, c, cl):
    """under -. F < 2 : 2 < 2 ^ N , F < 2 ^ ( N + 1 ) , ( 2 + F ) < 2 ^ ( N + 1 )"""
    fn, nn = c['F e. NN0'], c['N e. NN0']
    fr = w.s([fn], 'nn0red', '( %s -> F e. RR )' % ph)
    le2 = w.s([w.s([closed(w, ph, '2re', '2 e. RR'), fr], 'lenltd', '( %s -> ( 2 <_ F <-> -. F < 2 ) )' % ph), c['-. F < 2']], 'mpbird',
              '( %s -> 2 <_ F )' % ph)
    p2, p21 = '( 2 ^ N )', '( 2 ^ ( N + 1 ) )'
    ep = w.s([closed(w, ph, '2cn', '2 e. CC'), nn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ph, p21, p2))
    cl.atom(p2); cl.atom(p21)
    a = linarith(w, ph, [c['F < ( 2 ^ N )'], ep, cl.ge0('F')], 'F < %s' % p21, closure=cl, atoms=[p2, p21])
    b = linarith(w, ph, [c['F < ( 2 ^ N )'], ep, le2], '( 2 + F ) < %s' % p21, closure=cl, atoms=[p2, p21])
    return le2, a, b


def tmipt3():
    lab = 'tmipt3'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The loop of Lean\'s ` isPrimeTDF xm xd xf s t u ` in the case ` 2 <_ m ` : ` primeGoF ` from the divisor 2 '
        'with fuel ` m ` (~ tmipgr at ` N + 1 ` ) reaches ` flag = ( primeGo m 2 m ).1 ` , the counters at ` S ` .',
        deep=[('drop', ['J'], PL('P', 12), PL(PL('P', 13), 0))])
    fn, nn = c['F e. NN0'], c['N e. NN0']
    xg = c[WRD('X', GAM)]
    cl = Closure(w, ph, {'F': ('NN0', fn), 'N': ('NN0', nn)})
    le2, flt1, f2lt1 = big_facts(w, ph, c, cl)
    S0 = stacks0(w, ph, c, mk, ne, {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ph, 'F', fn, 'X', xg))})
    DV = lambda s_: '( D ` %s )' % s_
    dg = lambda s_: S0.vals[s_][2]
    two = closed(w, ph, '2nn0', '2 e. NN0')
    Sp = S0.upd('J', EW('2', DV('J')), ewg(w, ph, '2', two, DV('J'), dg('J'))).upd('I', EW('F', DV('I')), ewg(w, ph, 'F', fn, DV('I'), dg('I')))
    assert Sp.D == DP
    n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    ex = dict(base)
    ex.update({'2 e. NN': closed(w, ph, '2nn', '2 e. NN'), '( N + 1 ) e. NN0': n1, 'F < ( 2 ^ ( N + 1 ) )': flt1,
               '( 2 + F ) < ( 2 ^ ( N + 1 ) )': f2lt1, WRD(DV('J'), GAM): dg('J'), WRD(DV('I'), GAM): dg('I'), STKD(DP): Sp.memb,
               '( %s ` K ) = %s' % (DP, EW('F', 'X')): Sp.vals['K'][1], '( %s ` J ) = %s' % (DP, EW('2', DV('J'))): Sp.vals['J'][1],
               '( %s ` I ) = %s' % (DP, EW('F', DV('I'))): Sp.vals['I'][1]})
    t, cc = inst(w, ph, 'tmipgr', {'P': PL('P', 11), 'E': PL(PL('P', 12), 0), 'G': '2', 'H': 'F', 'N': '( N + 1 )',
                                    'Y': DV('J'), 'Z': DV('I'), 'D': DP}, Bld(w, ph, c, ex))
    Ca, Da, n = triple_parts(cc)
    OLD = UP(UP(DP, 'J', EW('( 2 + S )', DV('J'))), 'I', EW('( F - S )', DV('I')))
    assert Da == CLN(PL(PL('P', 12), 0), QCLS2, OLD), Da
    # S facts
    rn, sn, sle, rle = rs_facts(w, ph, c, cl)
    gs = w.s([two, sn], 'nn0addcld', '( %s -> ( 2 + S ) e. NN0 )' % ph)
    hsl = linarith(w, ph, [sle, rle], 'S <_ F', closure=cl)
    hs = w.s([sn, fn, hsl, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( F - S ) e. NN0 )' % ph)
    togk = lambda X, s_, g: w.s([g, mk['k'][s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    ya = ewg(w, ph, '( 2 + S )', gs, DV('J'), dg('J'))
    zb = ewg(w, ph, '( F - S )', hs, DV('I'), dg('I'))
    u4 = up4(w, ph, 'D', 'J', EW('2', DV('J')), 'I', EW('F', DV('I')), EW('( 2 + S )', DV('J')), EW('( F - S )', DV('I')), mk['tv'], c[STKD('D')],
             ne('J', 'I'), mk['k']['J']['kd'], togk(EW('2', DV('J')), 'J', Sp.vals['J'][2]), togk(EW('( 2 + S )', DV('J')), 'J', ya),
             mk['k']['I']['kd'], togk(EW('F', DV('I')), 'I', Sp.vals['I'][2]), togk(EW('( F - S )', DV('I')), 'I', zb))
    d = clneq(w, ph, PL(PL('P', 12), 0), QCLS2, u4, OLD, DPP)
    hrrw(w, ph, t, Ca, Da, n, deq=d, qed=True)
    return w.run()


def rs_facts(w, ph, c, cl):
    """R e. NN0 , S e. NN0 , S <_ R , R <_ F from the hypotheses R = .. , S = .."""
    fn = c['F e. NN0']
    two = closed(w, ph, '2nn0', '2 e. NN0')
    j3 = w.s([fn, two, fn], '3jca', '( %s -> ( F e. NN0 /\\ 2 e. NN0 /\\ F e. NN0 ) )' % ph)
    pc = w.s([w.s([fn, two], 'jca', '( %s -> ( F e. NN0 /\\ 2 e. NN0 ) )' % ph), fn, w.inst('primegocl')], 'syl2anc',
             '( %s -> ( ( F PrimeGo 2 ) ` F ) e. ( 2o X. NN0 ) )' % ph)
    req = c['R = %s' % RV2]
    rn = w.s([req, w.s([pc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, RV2))], 'eqeltrd', '( %s -> R e. NN0 )' % ph)
    rle = w.s([req, w.s([j3, w.inst('tmipgle')], 'syl', '( %s -> %s <_ F )' % (ph, RV2))], 'eqbrtrd', '( %s -> R <_ F )' % ph)
    cl.leaf('R', 'NN0', rn)
    seq = c['S = %s' % SV2]
    EARLY2 = tsub_text(PGL.EARLY, {'G': '2', 'H': 'F'})
    A1 = '( %s /\\ %s )' % (ph, EARLY2)
    A2 = '( %s /\\ -. %s )' % (ph, EARLY2)
    e1 = w.s([w.s([seq], 'adantr', '( %s -> S = %s )' % (A1, SV2)), w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, EARLY2))], 'iftrued',
              '( %s -> %s = ( R - 1 ) )' % (A1, SV2))], 'eqtrd', '( %s -> S = ( R - 1 ) )' % A1)
    rp = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, EARLY2))], 'simpld', '( %s -> 0 < R )' % A1)
    rn1 = w.s([rn], 'adantr', '( %s -> R e. NN0 )' % A1)
    rnn = w.s([w.s([rn1, rp], 'jca', '( %s -> ( R e. NN0 /\\ 0 < R ) )' % A1), w.inst('elnnnn0b')], 'sylibr', '( %s -> R e. NN )' % A1)
    s1 = w.s([e1, w.s([rnn, w.inst('nnm1nn0')], 'syl', '( %s -> ( R - 1 ) e. NN0 )' % A1)], 'eqeltrd', '( %s -> S e. NN0 )' % A1)
    cl1 = Closure(w, A1, {'R': ('NN0', rn1), 'S': ('NN0', s1)})
    le1 = linarith(w, A1, [e1], 'S <_ R', closure=cl1)
    e2 = w.s([w.s([seq], 'adantr', '( %s -> S = %s )' % (A2, SV2)), w.s([w.s([], 'simpr', '( %s -> -. %s )' % (A2, EARLY2))], 'iffalsed',
              '( %s -> %s = R )' % (A2, SV2))], 'eqtrd', '( %s -> S = R )' % A2)
    rn2 = w.s([rn], 'adantr', '( %s -> R e. NN0 )' % A2)
    s2 = w.s([e2, rn2], 'eqeltrd', '( %s -> S e. NN0 )' % A2)
    le2 = w.s([e2, w.s([w.s([rn2], 'nn0red', '( %s -> R e. RR )' % A2)], 'leidd', '( %s -> R <_ R )' % A2)], 'eqbrtrd', '( %s -> S <_ R )' % A2)
    sn = w.s([s1, s2], 'pm2.61dan', '( %s -> S e. NN0 )' % ph)
    sle = w.s([le1, le2], 'pm2.61dan', '( %s -> S <_ R )' % ph)
    cl.leaf('S', 'NN0', sn)
    return rn, sn, sle, rle


def tmipt4():
    lab = 'tmipt4'
    T, C, ph, w, c, mk, ne, base = start(lab,
        'The tail of Lean\'s ` isPrimeTDF xm xd xf s t u ` in the case ` 2 <_ m ` : ` dropNum xd ; dropNum xf ` '
        'restores the stacks and keeps the flag (~ tmidropnb ), which is ` ( isPrimeTD m ).1 ` .',
        deep=[('drop', ['J'], PL('P', 12), PL(PL('P', 13), 0)), ('drop', ['I'], PL('P', 13), 'E')])
    fn, nn = c['F e. NN0'], c['N e. NN0']
    xg = c[WRD('X', GAM)]
    cl = Closure(w, ph, {'F': ('NN0', fn), 'N': ('NN0', nn)})
    le2, flt1, f2lt1 = big_facts(w, ph, c, cl)
    rn, sn, sle, rle = rs_facts(w, ph, c, cl)
    S0 = stacks0(w, ph, c, mk, ne, {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ph, 'F', fn, 'X', xg))})
    DV = lambda s_: '( D ` %s )' % s_
    dg = lambda s_: S0.vals[s_][2]
    two = closed(w, ph, '2nn0', '2 e. NN0')
    gs = w.s([two, sn], 'nn0addcld', '( %s -> ( 2 + S ) e. NN0 )' % ph)
    hsl = linarith(w, ph, [sle, rle], 'S <_ F', closure=cl)
    hs = w.s([sn, fn, hsl, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( F - S ) e. NN0 )' % ph)
    VJ, VI = EW('( 2 + S )', DV('J')), EW('( F - S )', DV('I'))
    gJ, gI = ewg(w, ph, '( 2 + S )', gs, DV('J'), dg('J')), ewg(w, ph, '( F - S )', hs, DV('I'), dg('I'))
    SI = S0.upd('I', VI, gI)
    SIJ = SI.upd('J', VJ, gJ)
    run = Run(w, ph, mk, S0, base, c)
    run.S = SIJ; run.chain = [('I', VI), ('J', VJ)]
    run.gam[VI] = gI; run.gam[VJ] = gJ
    n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    gslt = linarith(w, ph, [f2lt1, hsl], '( 2 + S ) < ( 2 ^ ( N + 1 ) )', closure=cl, atoms=['( 2 ^ ( N + 1 ) )'])
    fslt = linarith(w, ph, [flt1, cl.ge0('S')], '( F - S ) < ( 2 ^ ( N + 1 ) )', closure=cl, atoms=['( 2 ^ ( N + 1 ) )'])
    ex1 = {'( 2 + S ) e. NN0': gs, '( N + 1 ) e. NN0': n1, '( 2 + S ) < ( 2 ^ ( N + 1 ) )': gslt, WRD(DV('J'), GAM): dg('J')}
    run.call('tmidropnb', {'K': 'J', 'F': '( 2 + S )', 'X': DV('J'), 'O': QV2, 'N': '( N + 1 )', 'P': PL('P', 12), 'E': PL(PL('P', 13), 0)},
             ex1, [('J', DV('J'), dg('J'))], on=(SI, [('I', VI)]))
    run.normalize(K6)
    # the flag is isPrimeTD's
    ipv = w.s([fn, w.inst('isprimetdval')], 'syl', '( %s -> ( IsPrimeTD ` F ) = if ( F < 2 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) )' % (ph, QV2, RV2))
    ipf = w.s([ipv, w.s([c['-. F < 2']], 'iffalsed', '( %s -> if ( F < 2 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) = <. %s , ( %s + 1 ) >. )'
                                                   % (ph, QV2, RV2, QV2, RV2))], 'eqtrd', '( %s -> ( IsPrimeTD ` F ) = <. %s , ( %s + 1 ) >. )' % (ph, QV2, RV2))
    pc = w.s([w.s([fn, two], 'jca', '( %s -> ( F e. NN0 /\\ 2 e. NN0 ) )' % ph), fn, w.inst('primegocl')], 'syl2anc',
             '( %s -> ( ( F PrimeGo 2 ) ` F ) e. ( 2o X. NN0 ) )' % ph)
    qv = w.s([w.s([pc, w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (ph, QV2))], 'elexd', '( %s -> %s e. _V )' % (ph, QV2))
    rv1 = w.s([w.s([w.s([pc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, RV2)), w.inst('peano2nn0')], 'syl',
                   '( %s -> ( %s + 1 ) e. NN0 )' % (ph, RV2))], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (ph, RV2))
    o1 = w.s([qv, rv1, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , ( %s + 1 ) >. ) = %s )' % (ph, QV2, RV2, QV2))
    q1 = w.s([w.s([ipf], 'fveq2d', '( %s -> ( 1st ` ( IsPrimeTD ` F ) ) = ( 1st ` <. %s , ( %s + 1 ) >. ) )' % (ph, QV2, RV2)), o1], 'eqtrd',
             '( %s -> ( 1st ` ( IsPrimeTD ` F ) ) = %s )' % (ph, QV2))
    ce = w.s([w.s([q1], 'eqcomd', '( %s -> %s = ( 1st ` ( IsPrimeTD ` F ) ) )' % (ph, QV2))], 'eqeq2d',
             '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = ( 1st ` ( IsPrimeTD ` F ) ) ) )' % (ph, QV2))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = ( 1st ` ( IsPrimeTD ` F ) ) ) )' % (ph, QV2))],
             'rabbidva', '( %s -> %s = %s )' % (ph, QCLS2, NIP))
    ex2 = {'( F - S ) e. NN0': hs, '( N + 1 ) e. NN0': n1, '( F - S ) < ( 2 ^ ( N + 1 ) )': fslt, WRD(DV('I'), GAM): dg('I')}
    run.call('tmidropnb', {'K': 'I', 'F': '( F - S )', 'X': DV('I'), 'O': QV2, 'N': '( N + 1 )', 'P': PL('P', 13), 'E': 'E'},
             ex2, [('I', DV('I'), dg('I'))], on=(S0, []), cls_rw=(rb, NIP))
    cur, out = run.normalize(K6)
    assert out == [] and cur == CLN('E', NIP, 'D'), (out, cur)
    # the pre stacks: UPD( UPD( D , I , VI ) , J , VJ ) = DPP
    togk = lambda X, s_, g: w.s([g, mk['k'][s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    sw = upc(w, ph, 'D', 'J', VJ, 'I', VI, mk['tv'], c[STKD('D')], ne('J', 'I'), mk['k']['J']['kd'], togk(VJ, 'J', gJ),
             mk['k']['I']['kd'], togk(VI, 'I', gI))
    # sw : UPD( UPD( D , J , VJ ) , I , VI ) = UPD( UPD( D , I , VI ) , J , VJ )
    ceq = clneq(w, ph, LM['E"'], QCLS2, sw, DPP, SIJ.D)
    ceq2 = w.s([ceq], 'eqcomd', '( %s -> %s = %s )' % (ph, CLN(LM['E"'], QCLS2, SIJ.D), CLN(LM['E"'], QCLS2, DPP)))
    t2, C2, D2, n2 = hrrw(w, ph, run.tri, run.C0, run.cur, run.n, ceq=ceq2)
    tb1 = w.s([w.s([n1, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB1))
    cl.leaf(TB1, 'NN0', tb1)
    le = linarith(w, ph, [cl.ge0(TB1)], '%s <_ %s' % (n2, T4B), closure=cl)
    hrle(w, ph, mk['phm'], t2, C2, D2, n2, T4B, cl.mem(T4B, 'NN0'), le, qed=True)
    return w.run()


L_F0 = LSET(fl='(/)')
CLT = PGL.CLT
GM_I = {'P0': LM['P0'], "B'": LM["B'"], 'B"': LM['B"'], 'E0': LM['E0'], "E'": LM["E'"], 'E"': LM['E"'], 'E': 'E',
        'C': CLT, 'L': L_F0, 'D': 'D', 'T1': T1B, 'T"': T2B, 'T0': BND3, "T'": T4B, 'N': SS, 'N1': N1C, 'N"': SS,
        'N0': QCLS2, "N'": NIP, 'D0': 'D', "D'": DP, 'D"': DPP}
_IA, _IC = split_imp(stmt('tm2fipt'))
ITREE = tsub(parse_conj(_IA), GM_I)
ICONCL = tsub_text(_IC, GM_I)
T_IR = ((T_PHM7, IPT.pred()), (idx_tree(K6), dist_tree(K6)), DATAR)
from t6blib import _split_top, _outer


def tmiptr():
    lab = 'tmiptr'
    ph = cj(T_IR)
    C = '( %s -> %s )' % (ph, ICONCL)
    w = W(lab, 'Lean\'s ` isPrimeTDF xm xd xf s t u ` at the machine, wherever it is installed (the core of '
               '` isPrimeTDF_le_B ` ): ~ tm2fipt with the test ` m < 2 ` (~ tmipt1 ), the load ` flag := false ` '
               'for ` m < 2 ` , and otherwise the counters (~ tmipt2 ), the loop (~ tmipt3 ) and the drops (~ tmipt4 ).')
    c, mk, ne, base = setup(w, ph, T_IR, K6, IPT.pred(), 'ipt')
    def unf(fname, ks, P_, E_):
        pr = FRAGS[fname].pred(ks, 'T', 'M', P_, E_)
        base.update(unfold_all(w, ph, base[pr], fname, ks, P_, E_, rec=False))
    unf('pg', K6, PL('P', 11), PL(PL('P', 12), 0))
    unf('iz', ['I', "I'"], PL(PL('P', 11), 2), PL(PL('P', 11), 0))
    unf('drop', ['J'], PL('P', 12), PL(PL('P', 13), 0))
    unf('drop', ['I'], PL('P', 13), 'E')
    fn, nn = c['F e. NN0'], c['N e. NN0']
    cl = Closure(w, ph, {'F': ('NN0', fn), 'N': ('NN0', nn)})
    rn, sn, sle, rle = rs_facts(w, ph, c, cl)
    ex = dict(base)
    b01 = lambda X_of: w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    ex[CTY(CLT)] = PGL.lamty(w, ph, mk, CLT, XL, '2o', w.s([], '2oex', '2o e. _V'), b01(XL))
    ex[LTY(L_F0)] = PGL.ldty(w, ph, mk, lambda t: dict(fl='(/)'))
    tbn = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB))
    n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    tb1 = w.s([w.s([n1, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB1))
    cl.leaf(TB, 'NN0', tbn); cl.leaf(TB1, 'NN0', tb1)
    for e_ in [T1B, T2B, BND3, T4B]:
        ex['%s e. NN0' % e_] = cl.mem(e_, 'NN0')
    ex['1 <_ %s' % T2B] = linarith(w, ph, [cl.ge0(TB)], '1 <_ %s' % T2B, closure=cl)
    ssS = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    ex['( 2nd ` T ) C_ ( 2nd ` T )'] = ssS
    def rabss(R_):
        return w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % R_)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, R_)), mk['seq']], 'sseqtrrd',
                   '( %s -> %s C_ ( 2nd ` T ) )' % (ph, R_))
    for R_ in [N1C, QCLS2, NIP]:
        ex['%s C_ ( 2nd ` T )' % R_] = rabss(R_)
    ex[STKD('D')] = c[STKD('D')]
    # the triples
    def cite(lab_, ante_tree, concl_text, ps=ph, bld=None):
        a = (bld or Bld(w, ps, c, ex))(ante_tree)
        return w.s([a, w.inst(lab_)], 'syl', '( %s -> %s )' % (ps, concl_text))
    T1_, C1_ = STMT('tmipt1')
    ex[C1_] = cite('tmipt1', T1_, C1_)
    # the dispatch
    DISJ = ITREE[1][2][1]
    DA, DB = _split_top(_outer(DISJ), '\\/')
    HT, HLD, DEQ = parse_conj(DA)
    HTF, TRIS = parse_conj(DB)
    A1 = '( %s /\\ F < 2 )' % ph
    A2 = '( %s /\\ -. F < 2 )' % ph
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A1, concl(w, ph, st)))
    two = closed(w, ph, '2nn0', '2 e. NN0')
    nl = w.s([w.s([fn, two], 'jca', '( %s -> ( F e. NN0 /\\ 2 e. NN0 ) )' % ph), w.inst('ncmplt')], 'syl',
             '( %s -> ( ( F Ncmp 2 ) = (/) <-> F < 2 ) )' % ph)
    X_of = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    def clt_at(pm, mm, cmp_eq_or_ne, true):
        xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', w.s([], '1oex', '1o e. _V'), w.s([], '0ex', '(/) e. _V'))
        cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
        if true:
            return w.s([cv, w.s([cmp_eq_or_ne], 'iftrued', '( %s -> %s = 1o )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CLT))
        c0 = w.s([cv, w.s([cmp_eq_or_ne], 'iffalsed', '( %s -> %s = (/) )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CLT))
        return not1o(w, pm, c0, CLT, 'm')
    # case F < 2
    pm = '( %s /\\ m e. %s )' % (A1, N1C)
    Lm = lambda st, a=A1: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, a, st)))
    mm, mc = rab_elim(w, pm, N1C, lambda h: '( TMcmp ` %s ) = ( F Ncmp 2 )' % h, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, N1C)))
    nc0 = w.s([w.s([], 'simpr', '( %s -> F < 2 )' % A1), L1(nl)], 'mpbird', '( %s -> ( F Ncmp 2 ) = (/) )' % A1)
    cm0 = w.s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = (/) )' % pm)
    ht = w.s([clt_at(pm, mm, cm0, True)], 'ralrimiva', '( %s -> %s )' % (A1, HT))
    nv = load_val(w, pm, lambda t: dict(fl='(/)'), 'm', mm)
    NVM = '( %s ` m )' % L_F0
    ipv = w.s([fn, w.inst('isprimetdval')], 'syl', '( %s -> ( IsPrimeTD ` F ) = if ( F < 2 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) )' % (ph, QV2, RV2))
    ipt_ = w.s([L1(ipv), w.s([w.s([], 'simpr', '( %s -> F < 2 )' % A1)], 'iftrued',
                             '( %s -> if ( F < 2 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) = <. (/) , 1 >. )' % (A1, QV2, RV2))], 'eqtrd',
               '( %s -> ( IsPrimeTD ` F ) = <. (/) , 1 >. )' % A1)
    o1 = w.s([w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A1), w.s([w.s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % A1),
              w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. (/) , 1 >. ) = (/) )' % A1)
    q0 = w.s([w.s([ipt_], 'fveq2d', '( %s -> ( 1st ` ( IsPrimeTD ` F ) ) = ( 1st ` <. (/) , 1 >. ) )' % A1), o1], 'eqtrd',
             '( %s -> ( 1st ` ( IsPrimeTD ` F ) ) = (/) )' % A1)
    fz = w.s([nv['fields']['fl'], Lm(q0)], 'eqtr4d', '( %s -> ( TMfl ` %s ) = ( 1st ` ( IsPrimeTD ` F ) ) )' % (pm, NVM))
    rin = rab_in(w, pm, NIP, lambda t: '( TMfl ` %s ) = ( 1st ` ( IsPrimeTD ` F ) )' % t, NVM, nv['mem'], fz)
    hld = w.s([rin], 'ralrimiva', '( %s -> %s )' % (A1, HLD))
    deq = w.s([], 'eqidd', '( %s -> D = D )' % A1)
    da = w.s([ht, hld, deq], '3jca', '( %s -> %s )' % (A1, DA))
    o_1 = w.s([da], 'orcd', '( %s -> %s )' % (A1, DISJ))
    # case 2 <_ F
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ph, st)))
    pm2 = '( %s /\\ m e. %s )' % (A2, N1C)
    Lm2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm2, concl(w, A2, st)))
    mm2, mc2 = rab_elim(w, pm2, N1C, lambda h: '( TMcmp ` %s ) = ( F Ncmp 2 )' % h, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm2, N1C)))
    nn0_ = w.s([w.s([], 'simpr', '( %s -> -. F < 2 )' % A2), L2(nl)], 'mtbird', '( %s -> -. ( F Ncmp 2 ) = (/) )' % A2)
    cmn = w.s([Lm2(nn0_), w.s([mc2], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = (/) <-> ( F Ncmp 2 ) = (/) ) )' % pm2)], 'mtbird',
              '( %s -> -. ( TMcmp ` m ) = (/) )' % pm2)
    htf = w.s([clt_at(pm2, mm2, cmn, False)], 'ralrimiva', '( %s -> %s )' % (A2, HTF))
    ex2 = {k: L2(v) for k, v in ex.items()}
    ex2['-. F < 2'] = w.s([], 'simpr', '( %s -> -. F < 2 )' % A2)
    c2 = Ctx(w, A2, T_IR, root=w.s([], 'simpl', '( %s -> %s )' % (A2, ph)))
    bld2 = Bld(w, A2, c2, ex2)
    tr = []
    for l_ in ['tmipt2', 'tmipt3', 'tmipt4']:
        Tl, Cl = STMT(l_)
        tr.append(cite(l_, Tl, Cl, ps=A2, bld=bld2))
    trs = w.s(tr, '3jca', '( %s -> %s )' % (A2, cj(TRIS)))
    db = w.s([htf, trs], 'jca', '( %s -> %s )' % (A2, DB))
    o_2 = w.s([db], 'olcd', '( %s -> %s )' % (A2, DISJ))
    ex[DISJ] = w.s([o_1, o_2], 'pm2.61dan', '( %s -> %s )' % (ph, DISJ))
    st = Bld(w, ph, c, ex)(ITREE)
    w.qed([st, w.inst('tm2fipt')], 'syl', C)
    return w.run()


BNDB = '( ( ( 2nd ` ( IsPrimeTD ` F ) ) + 1 ) x. ( TMB ` ( ( 3 x. N ) + 7 ) ) )'
T_IB = ((T_PHM7, IPT.pred()), (idx_tree(K6), dist_tree(K6)), DATA1)
CONCL_IB = TRI(CLN(LM['P0'], SS, 'D'), CLN('E', NIP, 'D'), BNDB)


def tmiptb():
    lab = 'tmiptb'
    ph = cj(T_IB)
    C = '( %s -> %s )' % (ph, CONCL_IB)
    w = W(lab, 'Lean\'s ` isPrimeTDF_le_B ` at the machine: wherever ` isPrimeTDF xm xd xf s t u ` is installed, from '
               'any state with ` m < 2 ^ N ` on ` xm ` the machine reaches ` flag = ( isPrimeTD m ).1 ` with every '
               'stack restored, within ` ( ( isPrimeTD m ).2 + 1 ) x. B ( 3 N + 7 ) ` steps (~ tmiptr ).')
    c = Ctx(w, ph, T_IB)
    SV2t = tsub_text(SV2, {'R': RV2})
    e1 = closed(w, ph, 'eqid', '%s = %s' % (RV2, RV2))
    e2 = closed(w, ph, 'eqid', '%s = %s' % (SV2t, SV2t))
    t, cc = inst(w, ph, 'tmiptr', {'R': RV2, 'S': SV2t}, Bld(w, ph, c, {'%s = %s' % (RV2, RV2): e1, '%s = %s' % (SV2t, SV2t): e2}))
    Ca, Da, n = triple_parts(cc)
    assert Ca == CLN(LM['P0'], SS, 'D') and Da == CLN('E', NIP, 'D'), (Ca, Da)
    fn, nn = c['F e. NN0'], c['N e. NN0']
    phm = c[PHM]
    two = closed(w, ph, '2nn0', '2 e. NN0')
    j3 = w.s([fn, two, fn], '3jca', '( %s -> ( F e. NN0 /\\ 2 e. NN0 /\\ F e. NN0 ) )' % ph)
    pc = w.s([w.s([fn, two], 'jca', '( %s -> ( F e. NN0 /\\ 2 e. NN0 ) )' % ph), fn, w.inst('primegocl')], 'syl2anc',
             '( %s -> ( ( F PrimeGo 2 ) ` F ) e. ( 2o X. NN0 ) )' % ph)
    rn = w.s([pc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, RV2))
    rle = w.s([j3, w.inst('tmipgle')], 'syl', '( %s -> %s <_ F )' % (ph, RV2))
    n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    tbN = w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))
    tb1N = w.s([n1, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB1))
    tb1ge = w.s([tb1N, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB1))
    tbs = w.s([nn, w.inst('tplbsuc')], 'syl', '( %s -> %s <_ %s )' % (ph, TB, TB1))
    b37 = w.s([nn, w.inst('tplb37')], 'syl', '( %s -> ( TMB ` ( ( 3 x. N ) + 7 ) ) = ( ; 2 7 x. %s ) )' % (ph, TB1))
    ipv = w.s([fn, w.inst('isprimetdval')], 'syl', '( %s -> ( IsPrimeTD ` F ) = if ( F < 2 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. ) )' % (ph, QV2, RV2))
    V2 = '( 2nd ` ( IsPrimeTD ` F ) )'
    def case(A, cond_true, V, vex1, vex2, first, second, extra_hyps):
        """( A -> n <_ BNDB ) in one case of F < 2"""
        L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A, concl(w, ph, st)))
        cnd = w.s([], 'simpr', '( %s -> %s )' % (A, cond_true))
        IFV = 'if ( F < 2 , <. (/) , 1 >. , <. %s , ( %s + 1 ) >. )' % (QV2, RV2)
        iv = w.s([cnd], 'iftrued' if cond_true == 'F < 2' else 'iffalsed', '( %s -> %s = <. %s , %s >. )' % (A, IFV, first, second))
        ip = w.s([L(ipv), iv], 'eqtrd', '( %s -> ( IsPrimeTD ` F ) = <. %s , %s >. )' % (A, first, second))
        o2 = w.s([vex1, vex2, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (A, first, second, second))
        v2 = w.s([w.s([ip], 'fveq2d', '( %s -> %s = ( 2nd ` <. %s , %s >. ) )' % (A, V2, first, second)), o2], 'eqtrd', '( %s -> %s = %s )' % (A, V2, second))
        TGT = '( ( %s + 1 ) x. ( ; 2 7 x. %s ) )' % (second, TB1)
        be = w.s([w.s([v2], 'oveq1d', '( %s -> ( %s + 1 ) = ( %s + 1 ) )' % (A, V2, second)), L(b37)], 'oveq12d', '( %s -> %s = %s )' % (A, BNDB, TGT))
        cl = Closure(w, A, {'F': ('NN0', L(fn)), 'N': ('NN0', L(nn)), RV2: ('NN0', L(rn)), TB: ('NN', L(tbN)), TB1: ('NN', L(tb1N))})
        for a_ in [RV2, TB, TB1]:
            cl.atom(a_)
        le = nlinarith(w, A, [L(tbs), L(tb1ge), cl.ge0(RV2), cl.ge0(TB)] + extra_hyps(A, L, cl), '%s <_ %s' % (n, TGT), closure=cl,
                       atoms=[RV2, TB, TB1])
        return w.s([le, be], 'breqtrrd', '( %s -> %s <_ %s )' % (A, n, BNDB)), v2
    A1 = '( %s /\\ F < 2 )' % ph
    A2 = '( %s /\\ -. F < 2 )' % ph
    def ex1(A, L, cl):
        cl.have('F', 'NN0', L(fn))
        f1 = w.s([w.s([cl.mem('F', 'ZZ'), closed(w, A, '2z', '2 e. ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( F < 2 <-> ( F + 1 ) <_ 2 ) )' % A),
                  w.s([], 'simpr', '( %s -> F < 2 )' % A)], 'mpbird' if False else 'mpbid' if False else 'mpbird', '') if False else None
        zl = w.s([cl.mem('F', 'ZZ'), closed(w, A, '2z', '2 e. ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( F < 2 <-> ( F + 1 ) <_ 2 ) )' % A)
        f1 = w.s([w.s([], 'simpr', '( %s -> F < 2 )' % A), zl], 'mpbid', '( %s -> ( F + 1 ) <_ 2 )' % A)
        r1 = linarith(w, A, [L(rle), f1], '%s <_ 1' % RV2, closure=cl, atoms=[RV2])
        return [r1, w.s([w.s([closed(w, A, '1re', '1 e. RR'), cl.mem(RV2, 'RR')], 'jca', '') if False else r1], 'id', '') if False else r1]
    v1a = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A1)
    v1b = w.s([w.s([], '1ex', '1 e. _V')], 'a1i', '( %s -> 1 e. _V )' % A1)
    le1, v21 = case(A1, 'F < 2', V2, v1a, v1b, '(/)', '1', ex1)
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ph, st)))
    v2a = w.s([w.s([L2(pc), w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (A2, QV2))], 'elexd', '( %s -> %s e. _V )' % (A2, QV2))
    r1n = w.s([L2(rn), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (A2, RV2))
    v2b = w.s([r1n], 'elexd', '( %s -> ( %s + 1 ) e. _V )' % (A2, RV2))
    le2, v22 = case(A2, '-. F < 2', V2, v2a, v2b, QV2, '( %s + 1 )' % RV2, lambda A, L, cl: [])
    le = w.s([le1, le2], 'pm2.61dan', '( %s -> %s <_ %s )' % (ph, n, BNDB))
    # BNDB e. NN0
    vn1 = w.s([v21, closed(w, A1, '1nn0', '1 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (A1, V2))
    vn2 = w.s([v22, r1n], 'eqeltrd', '( %s -> %s e. NN0 )' % (A2, V2))
    vn = w.s([vn1, vn2], 'pm2.61dan', '( %s -> %s e. NN0 )' % (ph, V2))
    tb37 = w.s([w.s([w.s([w.s([closed(w, ph, '3nn0', '3 e. NN0'), nn], 'nn0mulcld', '( %s -> ( 3 x. N ) e. NN0 )' % ph),
                           closed(w, ph, '7nn0', '7 e. NN0')], 'nn0addcld', '( %s -> ( ( 3 x. N ) + 7 ) e. NN0 )' % ph), w.inst('tmbcl')], 'syl',
                     '( %s -> ( TMB ` ( ( 3 x. N ) + 7 ) ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` ( ( 3 x. N ) + 7 ) ) e. NN0 )' % ph)
    bn = w.s([w.s([vn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, V2)), tb37], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, BNDB))
    hrle(w, ph, phm, t, Ca, Da, n, BNDB, bn, le, qed=True)
    return w.run()


STMTS = {'tmienc2': ST_ENC2}
STMTS['tmiptb'] = '( %s -> %s )' % (cj(T_IB), CONCL_IB)
STMTS['tmiptr'] = '( %s -> %s )' % (cj(T_IR), ICONCL)
for _l in ['tmipt1', 'tmipt2', 'tmipt3', 'tmipt4']:
    _T, _C = STMT(_l)
    STMTS[_l] = '( %s -> %s )' % (cj(_T), _C)

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
