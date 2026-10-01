"""T7: ` subCx x y z ` at the machine (Steps23 ` subCx_le_B ` ): ` sub x y z x `
(~ tmcsubx ) then ` canonNum x z ` (~ tmccans ) on the encodings of two
numbers below ` 2 ^ N ` ; the truncated difference, in ` ( TMB ` N ) ` .

    MM_DB=sorties/t7.mm python3 tools/gen/t7_u_subc.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7sub import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine, togk, letgk
import num

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tmcsubcb():
    lab = 'tmcsubcb'
    TREE = TREE_SUBC()
    ph = cj(TREE)
    w = W(lab, '` subCx_le_B ` at the machine: ` sub x y z x ` then ` canonNum x z ` on the encodings of '
               '` F , G < 2 ^ N ` leave the encoding of the truncated difference ` F - G ` on ` x ` , in '
               '` ( TMB ` N ) ` steps (~ tmcsubx , ~ tmccans , T4 ~ tonatsubtrunc ).')
    c = Ctx(w, ph, TREE)
    mk = machine(w, ph, c, ['K', 'J', 'I'])
    phm, tv = mk['phm'], mk['tv']
    K_ = lambda k: mk['k'][k]
    ff, gg, nn = c['F e. NN0'], c['G e. NN0'], c['N e. NN0']
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    EF, EG = '( encodeNat ` F )', '( encodeNat ` G )'
    ef = w.s([ff, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    eg = w.s([gg, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    dk = w.s([c[DATA_SUBC[1][1][0]], w.s([w.s([ff, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = ( inclBool o. %s ) )' % (ph, EF))], 'oveq1d',
             '( %s -> ( ( encNatGam ` F ) ++ ( <" 4 "> ++ X ) ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (ph, EF))], 'eqtrd',
             '( %s -> ( D ` K ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (ph, EF))
    dj = w.s([c[DATA_SUBC[1][1][1]], w.s([w.s([gg, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` G ) = ( inclBool o. %s ) )' % (ph, EG))], 'oveq1d',
             '( %s -> ( ( encNatGam ` G ) ++ ( <" 4 "> ++ Y ) ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) ) )' % (ph, EG))], 'eqtrd',
             '( %s -> ( D ` J ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) ) )' % (ph, EG))
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    m1 = {'L': EF, "L'": EG}
    bld = Builder(w, ph, c, {'T e. V': tv, MTY: mk['mt'], WRD(EF, '2o'): ef, WRD(EG, '2o'): eg, leaf(dk): dk, leaf(dj): dj})
    t1, c1 = inst(w, ph, 'tmcsubx', m1, bld)
    C1, D1, n1 = triple_parts(c1)
    ST = "( ( %s subTrunc %s ) ` (/) )" % (EF, EG)
    ZTe = '( inclBool o. %s )' % ST
    V = CC(ZTe, '( <" 4 "> ++ X )')
    U1 = UP('D', 'K', V); U2 = UP(U1, 'J', 'Y')
    assert D1 == CLN('E', SS, U2), D1
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    stw = w.s([ef, eg, b0, w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, ST))
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    x4 = w.s([w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph), xg, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    vg = w.s([w.s([stw, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ZTe)), x4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, V))
    vk = togk(w, ph, mk, V, 'K', vg)
    yk = togk(w, ph, mk, 'Y', 'J', yg)
    s1 = updcl(w, ph, 'D', 'K', V, tv, dd, K_('K')['kd'], vk)
    s2 = updcl(w, ph, U1, 'J', 'Y', tv, s1, K_('J')['kd'], yk)
    v1 = updnv(w, ph, U1, 'J', 'Y', 'K', tv, s1, K_('J')['kd'], elv(w, ph, yg, 'Y'), K_('K')['kd'], c['K =/= J'])
    v2 = updkv(w, ph, 'D', 'K', V, tv, dd, K_('K')['kd'], elv(w, ph, vg, V))
    u2k = w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, U2, V))
    CM = dict(CANS_LAB); CM.update({'L': ST, 'X': 'X', 'D': U2})
    bld2 = Builder(w, ph, c, {'T e. V': tv, MTY: mk['mt'], WRD(ST, '2o'): stw, STKD(U2): s2, '( %s ` K ) = %s' % (U2, V): u2k})
    t2, c2 = inst(w, ph, 'tmccans', CM, bld2)
    C2, D2, n2 = triple_parts(c2)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, phm, t1, t2, C1, D1, D2, n1, n2)
    # the value of the difference
    ENA = '( encNatGam ` ( toNat ` %s ) )' % ST
    TE = '( toNat ` %s )' % EF; TG = '( toNat ` %s )' % EG
    ts = w.s([ef, eg, b0, w.inst('tonatsubtrunc')], 'syl3anc', '( %s -> ( toNat ` %s ) = if ( %s < ( %s + ( bToNat ` (/) ) ) , 0 , ( %s - ( %s + ( bToNat ` (/) ) ) ) ) )' % (ph, ST, TE, TG, TE, TG))
    tf = w.s([ff, w.inst('tonatencnat')], 'syl', '( %s -> %s = F )' % (ph, TE))
    tg = w.s([gg, w.inst('tonatencnat')], 'syl', '( %s -> %s = G )' % (ph, TG))
    gz = w.s([w.s([tg, closed(w, ph, 'bwbn0', '( bToNat ` (/) ) = 0')], 'oveq12d', '( %s -> ( %s + ( bToNat ` (/) ) ) = ( G + 0 ) )' % (ph, TG)),
              w.s([w.s([gg], 'nn0cnd', '( %s -> G e. CC )' % ph)], 'addridd', '( %s -> ( G + 0 ) = G )' % ph)], 'eqtrd', '( %s -> ( %s + ( bToNat ` (/) ) ) = G )' % (ph, TG))
    r, new = w.rewrite('if ( %s < ( %s + ( bToNat ` (/) ) ) , 0 , ( %s - ( %s + ( bToNat ` (/) ) ) ) )' % (TE, TG, TE, TG),
                       {TE: ('F', tf), '( %s + ( bToNat ` (/) ) )' % TG: ('G', gz)}, ph)
    assert new == TRUNC, new
    tv2 = w.s([ts, r], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (ph, ST, TRUNC))
    W0 = CC(ENA, '( <" 4 "> ++ X )')
    W1 = CC('( encNatGam ` %s )' % TRUNC, '( <" 4 "> ++ X )')
    we = w.s([w.s([tv2], 'fveq2d', '( %s -> %s = ( encNatGam ` %s ) )' % (ph, ENA, TRUNC))], 'oveq1d', '( %s -> %s = %s )' % (ph, W0, W1))
    assert D2 == CLN('G0', SS, UP(U2, 'K', W0)), D2
    # collapse UPD( UPD( UPD( D , K , V ) , J , Y ) , K , W0 ) = UPD( UPD( D , K , W1 ) , J , Y )
    tn = w.s([stw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, ST))
    eng = w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ENA))
    w0g = w.s([eng, x4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, W0))
    w0k = togk(w, ph, mk, W0, 'K', w0g)
    e1 = upc(w, ph, U1, 'J', 'Y', 'K', W0, tv, s1, w.s([c['K =/= J']], 'necomd', '( %s -> J =/= K )' % ph), K_('J')['kd'], yk, K_('K')['kd'], w0k)
    e2 = up2(w, ph, 'D', 'K', V, W0, tv, dd, K_('K')['kd'], vk, w0k)
    r2, n_2 = w.rewrite(UP(UP(U1, 'K', W0), 'J', 'Y'), {UP(U1, 'K', W0): (UP('D', 'K', W0), e2)}, ph)
    u4 = upeq(w, ph, 'D', 'K', we, W0, W1)
    r4, n_4 = w.rewrite(n_2, {UP('D', 'K', W0): (UP('D', 'K', W1), u4)}, ph)
    F0 = UP(U2, 'K', W0)
    FIN = UP(UP('D', 'K', W1), 'J', 'Y')
    assert n_4 == FIN, n_4
    fa = w.s([e1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, F0, n_2))
    fb = w.s([fa, r4], 'eqtrd', '( %s -> %s = %s )' % (ph, F0, FIN))
    deq = clneq(w, ph, 'G0', SS, fb, F0, FIN)
    t3, C3, D3, n3 = hrrw(w, ph, t12, C1, D2, '( %s + %s )' % (n1, n2), deq=deq)
    # the bound
    MX = tsub_text(MXA, m1)
    A_, B_ = '( # ` %s )' % EF, '( # ` %s )' % EG
    la = w.s([ff, nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, A_))
    lb = w.s([gg, nn, c['G < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, B_))
    a0 = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, A_))
    bb0 = w.s([eg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, B_))
    cl = Closure(w, ph, {A_: ('NN0', a0), B_: ('NN0', bb0), 'N': ('NN0', nn)})
    mle = w.s([cl.mem(A_, 'RR'), cl.mem(B_, 'RR'), cl.mem('N', 'RR'), w.inst('maxle')], 'syl3anc', '( %s -> ( %s <_ N <-> ( %s <_ N /\\ %s <_ N ) ) )' % (ph, MX, A_, B_))
    mx = w.s([mle, w.s([la, lb], 'jca', '( %s -> ( %s <_ N /\\ %s <_ N ) )' % (ph, A_, B_))], 'mpbird', '( %s -> %s <_ N )' % (ph, MX))
    LS = '( # ` %s )' % ST
    sl = w.s([ef, eg, b0, w.inst('subtrunclen')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, LS, MX))
    lsl = w.s([stw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LS))
    mx0 = w.s([bb0, a0], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MX))
    five = closed(w, ph, '5nn0', '5 e. NN0')
    le5 = w.s([num.le_lit(w, '5', '; 6 4')], 'a1i', '( %s -> 5 <_ ; 6 4 )' % ph)
    tl = w.s([w.s([nn, five, le5], '3jca', '( %s -> ( N e. NN0 /\\ 5 e. NN0 /\\ 5 <_ ; 6 4 ) )' % ph), w.inst('tmblin')], 'syl', '( %s -> ( 5 x. ( N + 2 ) ) <_ ( TMB ` N ) )' % ph)
    tb0 = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` N ) e. NN0 )' % ph)
    cl2 = Closure(w, ph, {LS: ('NN0', lsl), MX: ('NN0', mx0), 'N': ('NN0', nn), '( TMB ` N )': ('NN0', tb0)})
    le = linarith(w, ph, [sl, mx, tl], '%s <_ ( TMB ` N )' % n3, closure=cl2)
    hrle(w, ph, phm, t3, C3, D3, n3, '( TMB ` N )', tb0, le, qed=True)
    assert TRI(C3, D3, '( TMB ` N )') == CONCL_SUBC, (TRI(C3, D3, '( TMB ` N )'), CONCL_SUBC)
    return w.run()


if __name__ == '__main__':
    if want('tmcsubcb'): tmcsubcb()
