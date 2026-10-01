"""Sortie T21b: t21bf (badSet as a function: values, size bound D, members >= 2)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from c8lib import lin8

E10 = '( exp ` ; 1 0 )'
L191 = '( l ^c %s )' % F191
LL = '( log ` l )'
BADl = BAD(L191, TAUl, 'V')
IFV = 'if ( b <_ l , %s , (/) )' % BADl
FZ = '( 2 ... ( |_ ` %s ) )' % L191
PN = '( ~P NN i^i Fin )'
J = '( |^ ` %s )' % D0


def gen_bf():
    w = W('t21bf', 'The exceptional sets ` bad ( l ) ` of T2.1 as a function on ` NN0 ` (empty below the threshold ` b ` ): finite sets of naturals ` >_ 2 ` , of size at most ` D = ceil ( c_2 ( nu ) e ^ ( ( 191 / 900 ) c_3 rho ) ) ` uniformly in ` l ` (Lean ` badSet ` , ` badSet_ge_two ` , ` badSet_card_le ` at ` x >_ x_2 ` ; ~ t21card ).')
    A0, concl = split_imp(SB['t21bf'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    rp_, vr, v1, br = u['R e. RR+'], u['V e. RR'], u['1 <_ V'], u['b e. RR']
    AXb = '( ( exp ` ; 1 0 ) <_ x /\\ ( ; 4 0 x. R ) <_ ( log ` x ) )'
    AX = u['A. x e. RR ( b <_ x -> %s )' % AXb]
    rr = s([rp_], 'rpred', 'R e. RR')
    # D0 real, >= 0 ; J in NN0
    c10 = s([s([w.s([w.s([w.s([], '1nn', '1 e. NN') if False else None], 'x', 'x')], 'x', 'x') if False else num.nn(w, 10)], 'a1i', '; 1 0 e. NN')], 'x', 'x') if False else None
    t10 = num.nn(w, 10)
    e10 = w.s([t10, w.s([num.nn(w, 10), w.s([num.nn0(w, 10), num.nn0(w, 10)], 'x', 'x') if False else w.s([num.nn(w, 10), num.nn0(w, 10)], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    p1010 = w.s([w.s([num.nn(w, 10), num.nn0(w, 10)], 'jca', '( ; 1 0 e. NN /\\ ; 1 0 e. NN0 )') if False else None], 'x', 'x') if False else None
    a1 = w.s([w.s([num.nn(w, 10), num.nn0(w, 10)], 'pm3.2i', '( ; 1 0 e. NN /\\ ; 1 0 e. NN0 )'), w.inst('nnexpcl')], 'ax-mp', '( ; 1 0 ^ ; 1 0 ) e. NN')
    a2 = w.s([w.s([num.nn(w, 10), w.s([a1], 'nnnn0i', '( ; 1 0 ^ ; 1 0 ) e. NN0')], 'pm3.2i', '( ; 1 0 e. NN /\\ ( ; 1 0 ^ ; 1 0 ) e. NN0 )'), w.inst('nnexpcl')], 'ax-mp', '%s e. NN' % C2T)
    c2r = s([w.s([a2], 'nnrei', '%s e. RR' % C2T)], 'a1i', '%s e. RR' % C2T)
    c20 = s([w.s([w.s([a2], 'nnnn0i', '%s e. NN0' % C2T)], 'nn0ge0i', '0 <_ %s' % C2T)], 'a1i', '0 <_ %s' % C2T)
    V2 = '( V + 2 )'
    v2r = s([vr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % V2)
    v20 = lin.linarith(w, A0, [v1], '0 <_ %s' % V2, leaves={'V': vr})
    EXC = '( exp ` ( %s x. ( %s x. R ) ) )' % (F191, C13)
    exr = s([s([s([num.real(w, F191)], 'a1i', '%s e. RR' % F191), s([s([num.real(w, C13)], 'a1i', '%s e. RR' % C13), rr], 'remulcld', '( %s x. R ) e. RR' % C13)], 'remulcld', '( %s x. ( %s x. R ) ) e. RR' % (F191, C13))], 'rpefcld', '%s e. RR+' % EXC)
    CV = '( %s x. %s )' % (C2T, V2)
    cvr = s([c2r, v2r], 'remulcld', '%s e. RR' % CV)
    cv0 = s([c2r, v2r, c20, v20], 'mulge0d', '0 <_ %s' % CV)
    d0r = s([cvr, s([exr], 'rpred', '%s e. RR' % EXC)], 'remulcld', '%s e. RR' % D0)
    d00 = s([cvr, s([exr], 'rpred', '%s e. RR' % EXC), cv0, s([exr], 'rpge0d', '0 <_ %s' % EXC)], 'mulge0d', '0 <_ %s' % D0)
    jz = s([d0r, w.inst('ceilcl')], 'syl', '%s e. ZZ' % J)
    jge = s([d0r, w.inst('ceilge')], 'syl', '%s <_ %s' % (D0, J))
    jr = s([jz], 'zred', '%s e. RR' % J)
    j0 = lin.linarith(w, A0, [d00, jge], '0 <_ %s' % J, leaves={D0: d0r, J: jr}) if False else s([s([], '0red', '0 e. RR'), d0r, jr, d00, jge], 'letrd', '0 <_ %s' % J)
    jn0 = s([s([jz, j0], 'jca', '( %s e. ZZ /\\ 0 <_ %s )' % (J, J)), w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (J, J, J))], 'sylibr', '%s e. NN0' % J)
    # per l
    Al = '( %s /\\ l e. NN0 )' % A0
    sl = S_(w, Al)
    Ll = lambda st: lift(w, st, Al)
    ln0 = sl([], 'simpr', 'l e. NN0')
    lr = sl([ln0], 'nn0red', 'l e. RR')
    def memb(v):
        Av = '( %s /\\ %s e. NN0 )' % (A0, v)
        sv = S_(w, Av)
        Lv = L191.replace('l', v) if False else '( %s ^c %s )' % (v, F191)
        FZv = '( 2 ... ( |_ ` %s ) )' % Lv
        BADv = BAD(Lv, '( 1 - ( R / ( log ` %s ) ) )' % v, 'V')
        IFv = 'if ( b <_ %s , %s , (/) )' % (v, BADv)
        fzn = sv([w.s([w.s([], '2nn', '2 e. NN'), w.inst('fzssnn')], 'ax-mp', '%s C_ NN' % FZv)], 'a1i', '%s C_ NN' % FZv)
        bss = sv([sv([w.s([], 'ssrab2', '%s C_ %s' % (BADv, FZv))], 'a1i', '%s C_ %s' % (BADv, FZv)), fzn], 'sstrd', '%s C_ NN' % BADv)
        bpw = sv([bss, w.s([w.s([], 'nnex', 'NN e. _V')], 'elpw2', '( %s e. ~P NN <-> %s C_ NN )' % (BADv, BADv))], 'sylibr', '%s e. ~P NN' % BADv)
        bfin = sv([sv([w.s([], 'fzfi', '%s e. Fin' % FZv)], 'a1i', '%s e. Fin' % FZv), sv([w.s([], 'ssrab2', '%s C_ %s' % (BADv, FZv))], 'a1i', '%s C_ %s' % (BADv, FZv))], 'ssfid', '%s e. Fin' % BADv)
        bin_ = sv([sv([bpw, bfin], 'jca', '( %s e. ~P NN /\\ %s e. Fin )' % (BADv, BADv)), w.s([], 'elin', '( %s e. %s <-> ( %s e. ~P NN /\\ %s e. Fin ) )' % (BADv, PN, BADv, BADv))], 'sylibr', '%s e. %s' % (BADv, PN))
        z0 = w.s([w.s([w.s([w.s([], '0ss', '(/) C_ NN'), w.s([w.s([], 'nnex', 'NN e. _V')], 'elpw2', '( (/) e. ~P NN <-> (/) C_ NN )')], 'mpbir', '(/) e. ~P NN'), w.s([], '0fi', '(/) e. Fin')], 'pm3.2i', '( (/) e. ~P NN /\\ (/) e. Fin )'),
                  w.s([], 'elin', '( (/) e. %s <-> ( (/) e. ~P NN /\\ (/) e. Fin ) )' % PN)], 'mpbir', '(/) e. %s' % PN)
        ifin = sv([bin_, sv([z0], 'a1i', '(/) e. %s' % PN)], 'ifcld', '%s e. %s' % (IFv, PN))
        return ifin, bfin
    ifk, _ = memb('k')
    ifin, bfin = memb('l')
    fm = s([ifk], 'fmptd', '%s : NN0 --> %s' % (FF, PN))
    import congr as _cg
    BODYk = 'if ( b <_ k , %s , (/) )' % BAD('( k ^c %s )' % F191, TAUk, 'V')
    ck, fval = w.congr(BODYk, {'k': 'l'}, 'k = l', {'k': w.s([], 'id', '( k = l -> k = l )')})
    assert fval == IFV, fval
    fv = w.s([w.s([], 'eqid', '%s = %s' % (FF, FF)), ck, ln0, sl([ifin], 'elexd', '%s e. _V' % IFV)], 'fvmptd3', '( %s -> ( %s ` l ) = %s )' % (Al, FF, IFV))
    # card: case b <_ l
    Ab = '( %s /\\ b <_ l )' % Al
    sb = S_(w, Ab)
    Lb = lambda st: lift(w, st, Ab)
    bl = sb([], 'simpr', 'b <_ l')
    body = '( b <_ x -> %s )' % AXb
    cg, inst = w.wcongr(body, {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
    rs = sb([Lb(lr), Lb(AX), w.s([cg], 'rspcv', '( l e. RR -> ( A. x e. RR %s -> %s ) )' % (body, inst))], 'sylc', inst)
    both = sb([bl, rs], 'mpd', '( %s <_ l /\\ ( ; 4 0 x. R ) <_ %s )' % (E10, LL))
    e10l = sb([both], 'simpld', '%s <_ l' % E10); r40 = sb([both], 'simprd', '( ; 4 0 x. R ) <_ %s' % LL)
    e10r = sb([sb([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'reefcld', '%s e. RR' % E10)
    g11 = ap(w, Ab, [sb([num.rp(w, '; 1 0')], 'a1i', '; 1 0 e. RR+')], 'efgt1p', '( 1 + ; 1 0 ) < %s' % E10)
    l1 = lin8(w, Ab, [g11, e10l], '1 < l', {E10: e10r, 'l': Lb(lr)})
    lp = sb([Lb(lr), lin.linarith(w, Ab, [l1], '0 < l', leaves={'l': Lb(lr)})], 'elrpd', 'l e. RR+')
    e10p = sb([sb([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'rpefcld', '%s e. RR+' % E10)
    f191 = sb([num.real(w, F191)], 'a1i', '%s e. RR' % F191)
    cx = sb([e10r, sb([e10p], 'rpge0d', '0 <_ %s' % E10), Lb(lr), f191, sb([num.le_lit(w, '0', F191)], 'a1i', '0 <_ %s' % F191), e10l], 'cxple2ad', '( %s ^c %s ) <_ %s' % (E10, F191, L191))
    ce = sb([sb([e10p], 'rpcnd', '%s e. CC' % E10), sb([e10p], 'rpne0d', '%s =/= 0' % E10), sb([num.cc(w, F191)], 'a1i', '%s e. CC' % F191)], 'cxpefd', '( %s ^c %s ) = ( exp ` ( %s x. ( log ` %s ) ) )' % (E10, F191, F191, E10))
    le10 = ap(w, Ab, [sb([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'relogef', '( log ` %s ) = ; 1 0' % E10)
    A_ = '( ; ; 1 9 1 / ; 9 0 )'
    mm_ = sb([sb([le10], 'oveq2d', '( %s x. ( log ` %s ) ) = ( %s x. ; 1 0 )' % (F191, E10, F191)), lin.lineq(w, Ab, '( %s x. ; 1 0 )' % F191, A_)], 'eqtrd', '( %s x. ( log ` %s ) ) = %s' % (F191, E10, A_))
    EA = '( exp ` %s )' % A_
    ce2 = sb([ce, sb([mm_], 'fveq2d', '( exp ` ( %s x. ( log ` %s ) ) ) = %s' % (F191, E10, EA))], 'eqtrd', '( %s ^c %s ) = %s' % (E10, F191, EA))
    ga = ap(w, Ab, [sb([num.rp(w, A_)], 'a1i', '%s e. RR+' % A_)], 'efgt1p', '( 1 + %s ) < %s' % (A_, EA))
    ear = sb([sb([num.real(w, A_)], 'a1i', '%s e. RR' % A_)], 'reefcld', '%s e. RR' % EA)
    l191r = sb([lp, f191], 'rpcxpcld', '%s e. RR+' % L191)
    two = lin8(w, Ab, [ga, sb([ce2, cx], 'eqbrtrrd', '%s <_ %s' % (EA, L191))], '2 <_ %s' % L191, {EA: ear, L191: sb([l191r], 'rpred', '%s e. RR' % L191)})
    lgp = ap(w, Ab, [sb([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+'), lp], 'logltb', '( 1 < l <-> ( log ` 1 ) < %s )' % LL)
    lg0 = sb([sb([sb([w.s([], 'log1', '( log ` 1 ) = 0')], 'a1i', '( log ` 1 ) = 0')], 'eqcomd', '0 = ( log ` 1 )'), sb([l1, lgp], 'mpbid', '( log ` 1 ) < %s' % LL)], 'eqbrtrd', '0 < %s' % LL)
    llp = sb([sb([lp], 'relogcld', '%s e. RR' % LL), lg0], 'elrpd', '%s e. RR+' % LL)
    RL = '( R / %s )' % LL
    r40b = lin8(w, Ab, [r40], 'R <_ ( %s x. ( 1 / ; 4 0 ) )' % LL, {'R': Lb(rr), LL: sb([llp], 'rpred', '%s e. RR' % LL)})
    rl = sb([r40b, sb([Lb(rr), sb([num.real(w, '( 1 / ; 4 0 )')], 'a1i', '( 1 / ; 4 0 ) e. RR'), llp], 'ledivmuld', '( %s <_ ( 1 / ; 4 0 ) <-> R <_ ( %s x. ( 1 / ; 4 0 ) ) )' % (RL, LL))], 'mpbird', '%s <_ ( 1 / ; 4 0 )' % RL)
    t39 = lin8(w, Ab, [rl], '( ; 3 9 / ; 4 0 ) <_ %s' % TAUl, {RL: sb([Lb(rr), llp], 'rerpdivcld', '%s e. RR' % RL)})
    cd = ap(w, Ab, [Lb(rp_), Lb(vr), Lb(v1), Lb(lr), l1, two, t39], 't21card', '( # ` %s ) <_ %s' % (BADl, D0))
    ift = sb([bl, w.s([], 'iftrue', '( b <_ l -> %s = %s )' % (IFV, BADl))], 'syl', '%s = %s' % (IFV, BADl))
    fvb = sb([Lb(fv), ift], 'eqtrd', '( %s ` l ) = %s' % (FF, BADl))
    hb = sb([sb([fvb], 'fveq2d', '( # ` ( %s ` l ) ) = ( # ` %s )' % (FF, BADl)), sb([cd, Lb(jge)], 'x', 'x') if False else sb([sb([bfin], 'x', 'x')], 'x', 'x') if False else None], 'x', 'x') if False else None
    hbr = sb([sb([Lb(bfin), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % BADl)], 'nn0red', '( # ` %s ) e. RR' % BADl)
    cdj = sb([hbr, Lb(d0r), Lb(jr), cd, Lb(jge)], 'letrd', '( # ` %s ) <_ %s' % (BADl, J))
    c1 = sb([sb([fvb], 'fveq2d', '( # ` ( %s ` l ) ) = ( # ` %s )' % (FF, BADl)), cdj], 'eqbrtrd', '( # ` ( %s ` l ) ) <_ %s' % (FF, J))
    # case not b <_ l
    An = '( %s /\\ -. b <_ l )' % Al
    sn = S_(w, An)
    iff = sn([sn([], 'simpr', '-. b <_ l'), w.s([], 'iffalse', '( -. b <_ l -> %s = (/) )' % IFV)], 'syl', '%s = (/)' % IFV)
    fvn = sn([lift(w, fv, An), iff], 'eqtrd', '( %s ` l ) = (/)' % FF)
    c2 = sn([sn([sn([fvn], 'fveq2d', '( # ` ( %s ` l ) ) = ( # ` (/) )' % FF), sn([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( # ` (/) ) = 0')], 'eqtrd', '( # ` ( %s ` l ) ) = 0' % FF), lift(w, j0, An)], 'eqbrtrd', '( # ` ( %s ` l ) ) <_ %s' % (FF, J))
    cl_ = sl([c1, c2], 'pm2.61dan', '( # ` ( %s ` l ) ) <_ %s' % (FF, J))
    al1 = s([cl_], 'ralrimiva', 'A. l e. NN0 ( # ` ( %s ` l ) ) <_ %s' % (FF, J))
    # members >= 2
    Ai = '( %s /\\ i e. ( %s ` l ) )' % (Al, FF)
    si = S_(w, Ai)
    iin = si([si([], 'simpr', 'i e. ( %s ` l )' % FF), lift(w, fv, Ai)], 'eleqtrd', 'i e. %s' % IFV)
    Aib = '( %s /\\ b <_ l )' % Ai
    ib = w.s([w.s([lift(w, iin, Aib), w.s([w.s([], 'simpr', '( %s -> b <_ l )' % Aib), w.s([], 'iftrue', '( b <_ l -> %s = %s )' % (IFV, BADl))], 'syl', '( %s -> %s = %s )' % (Aib, IFV, BADl))], 'eleqtrd', '( %s -> i e. %s )' % (Aib, BADl)),
              w.s([], 'elrabi', 'x') if False else w.inst('elrabi')], 'syl', '( %s -> i e. %s )' % (Aib, FZ))
    i2 = w.s([ib, w.inst('elfzle1')], 'syl', '( %s -> 2 <_ i )' % Aib)
    Ain = '( %s /\\ -. b <_ l )' % Ai
    i0 = w.s([lift(w, iin, Ain), w.s([w.s([], 'simpr', '( %s -> -. b <_ l )' % Ain), w.s([], 'iffalse', '( -. b <_ l -> %s = (/) )' % IFV)], 'syl', '( %s -> %s = (/) )' % (Ain, IFV))], 'eleqtrd', '( %s -> i e. (/) )' % Ain)
    i2n = w.s([i0, w.s([w.s([], 'noel', '-. i e. (/)'), w.s([], 'pm2.21', '( -. i e. (/) -> ( i e. (/) -> 2 <_ i ) )')], 'ax-mp', '( i e. (/) -> 2 <_ i )')], 'syl', '( %s -> 2 <_ i )' % Ain)
    ii = si([i2, i2n], 'pm2.61dan', '2 <_ i')
    al2 = s([sl([ii], 'ralrimiva', 'A. i e. ( %s ` l ) 2 <_ i' % FF)], 'ralrimiva', 'A. l e. NN0 A. i e. ( %s ` l ) 2 <_ i' % FF)
    w.qed([jn0, fm, s([al1, al2], 'jca', '( A. l e. NN0 ( # ` ( %s ` l ) ) <_ %s /\\ A. l e. NN0 A. i e. ( %s ` l ) 2 <_ i )' % (FF, J, FF))], '3jca', SB['t21bf'])
    return go(w)


if __name__ == '__main__':
    gen_bf()
