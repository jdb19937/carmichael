"""T7b: ` incr ` , ` predNum ` , ` isZero ` installed, from any state (the union
over the pinned values of ~ tmiinc , ~ tmiprd , ~ tmiiz by ~ tmchiun , the
pattern of ~ tmccans ).  Lean's runs lemmas are stated from any ` v ` .

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_e_froms.py tmiincs tmiprds tmiizs
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from t7_e_cmp import machine, togk
from t7b_c_runs import runs_stmt

SEL = sys.argv[1:]
IFL0 = 'if ( ( toNat ` L ) = 0 , 1o , (/) )'
NFL = '{ h e. TMSt | ( TMfl ` h ) = %s }' % IFL0
SRC = {'tmiincs': 'tmiinc', 'tmiprds': 'tmiprd', 'tmiizs': 'tmiiz'}
XM = {'O': '( TMfl ` x )', 'Q': '( TMcmp ` x )', 'R': '( TMcar ` x )'}


def froms_stmt(lab):
    T, C = runs_stmt(SRC[lab])
    Cc, Dd, n = triple_parts(C)
    Cn = Cc.replace(NPC, SS)
    if lab == 'tmiizs':
        post = CLN('E', NFL, 'D')
    else:
        post = Dd.replace(NPC, SS)
    return T, TRI(Cn, post, n)


def union_from_S(w, ph, c, mk, tx, Dpost, n, nn0, cfpost):
    """from tx : ( ph -> C( ( P ` 0 ) , NP_x , D ) ~~> Dpost in n ) (x free, not in ph), the triple from
    C( ( P ` 0 ) , S , D ) (tmchiun, the tmccans pattern)"""
    phm = mk['phm']; seq = mk['seq']
    A = '( P ` 0 )'
    NPX = NP(XM['O'], XM['Q'], XM['R'])
    TRI_X = TRI(CLN(A, NPX, 'D'), Dpost, n)
    ral = w.s([tx], 'ralrimivw', '( %s -> A. x e. TMSt %s )' % (ph, TRI_X))
    j2 = w.s([cfpost, nn0], 'jca', '( %s -> ( %s C_ ( TM2Cfg ` T ) /\\ %s e. NN0 ) )' % (ph, Dpost, n))
    UN = 'U_ x e. TMSt %s' % CLN(A, NPX, 'D')
    hi = w.s([phm, j2, ral, w.inst('tmchiun')], 'syl3anc', '( %s -> %s )' % (ph, TRI(UN, Dpost, n)))
    UNP = 'U_ x e. TMSt %s' % NPX
    ydef = lambda y: NP('( TMfl ` %s )' % y, '( TMcmp ` %s )' % y, '( TMcar ` %s )' % y)
    ida = w.s([], 'id', '( x = y -> x = y )')
    cg, new = w.congr(NPX, {'x': 'y'}, 'x = y', {'x': ida})
    assert new == ydef('y'), new
    yy = w.s([], 'id', '( y e. TMSt -> y e. TMSt )')
    fe = lambda f: w.s([], 'eqidd', '( y e. TMSt -> ( %s ` y ) = ( %s ` y ) )' % (ACC[f], ACC[f]))
    cond = lambda t: '( ( TMfl ` %s ) = ( TMfl ` y ) /\\ ( TMcmp ` %s ) = ( TMcmp ` y ) /\\ ( TMcar ` %s ) = ( TMcar ` y ) )' % (t, t, t)
    c3 = w.s([fe('fl'), fe('cmp'), fe('car')], '3jca', '( y e. TMSt -> %s )' % cond('y'))
    yin = rab_in(w, 'y e. TMSt', ydef('y'), cond, 'y', yy, c3)
    s2i = w.s([cg], 'ssiun2s', '( y e. TMSt -> %s C_ %s )' % (ydef('y'), UNP))
    yu = w.s([s2i, yin], 'sseldd', '( y e. TMSt -> y e. %s )' % UNP)
    su = w.s([yu], 'ssriv', 'TMSt C_ %s' % UNP)
    su2 = w.s([seq, w.s([su], 'a1i', '( %s -> TMSt C_ %s )' % (ph, UNP))], 'eqsstrd', '( %s -> ( 2nd ` T ) C_ %s )' % (ph, UNP))
    sd = w.s([], 'ssid', '{ D } C_ { D }')
    x1 = w.s([su2, w.s([sd], 'a1i', '( %s -> { D } C_ { D } )' % ph), w.inst('xpss12')], 'syl2anc',
             '( %s -> ( ( 2nd ` T ) X. { D } ) C_ ( %s X. { D } ) )' % (ph, UNP))
    sl = w.s([], 'ssid', '{ ( inl ` %s ) } C_ { ( inl ` %s ) }' % (A, A))
    x2 = w.s([w.s([sl], 'a1i', '( %s -> { ( inl ` %s ) } C_ { ( inl ` %s ) } )' % (ph, A, A)), x1, w.inst('xpss12')], 'syl2anc',
             '( %s -> %s C_ ( { ( inl ` %s ) } X. ( %s X. { D } ) ) )' % (ph, CLN(A, SS, 'D'), A, UNP))
    e1 = w.s([], 'xpiundir', '( %s X. { D } ) = U_ x e. TMSt ( %s X. { D } )' % (UNP, NPX))
    e1b = w.s([e1], 'xpeq2i', '( { ( inl ` %s ) } X. ( %s X. { D } ) ) = ( { ( inl ` %s ) } X. U_ x e. TMSt ( %s X. { D } ) )' % (A, UNP, A, NPX))
    e2 = w.s([], 'xpiundi', '( { ( inl ` %s ) } X. U_ x e. TMSt ( %s X. { D } ) ) = %s' % (A, NPX, UN))
    e3 = w.s([e1b, e2], 'eqtri', '( { ( inl ` %s ) } X. ( %s X. { D } ) ) = %s' % (A, UNP, UN))
    x3 = w.s([x2, w.s([e3], 'a1i', '( %s -> ( { ( inl ` %s ) } X. ( %s X. { D } ) ) = %s )' % (ph, A, UNP, UN))], 'sseqtrd',
             '( %s -> %s C_ %s )' % (ph, CLN(A, SS, 'D'), UN))
    return hrssc(w, ph, phm, hi, UN, Dpost, n, CLN(A, SS, 'D'), x3)


def pred_labs(w, ph, c, fname):
    """the unfolded predicate's leaves (label typings etc.) of the antecedent's predicate"""
    f = FRAGS[fname]
    return unfold_all(w, ph, c[f.pred()], fname, f.stacks, 'P', 'E')


def froms(lab):
    T, C = froms_stmt(lab)
    src = SRC[lab]
    fname = {'tmiincs': 'inc', 'tmiprds': 'prd', 'tmiizs': 'iz'}[lab]
    _, C0 = runs_stmt(src)
    ph = cj(T)
    w = W(lab, 'The installed form ~ %s from any state (Lean\'s runs lemma is stated from any ` v ` ): '
               'the union over the pinned register values, ~ tmchiun .' % src)
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ['K'])
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    ll, xg, dd = c[WRD('L', '2o')], c[WRD('X', GAM)], c[STKD('D')]
    un = pred_labs(w, ph, c, fname)
    el = un[LAB('E')]
    t = w.s([], src, '( %s -> %s )' % (ph, tsub_text(C0, XM)))
    Cx, Dx, n = triple_parts(tsub_text(C0, XM))
    _, Dpost, _ = triple_parts(C)
    NPX = NP(XM['O'], XM['Q'], XM['R'])
    ll0 = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    cl = Closure(w, ph, {'( # ` L )': ('NN0', ll0)})
    nn0 = cl.mem(n, 'NN0')
    if lab == 'tmiizs':
        NZX = '{ h e. TMSt | ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = ( TMcmp ` x ) ) }' % IFL0
        sim = w.s([], 'simpl', '( ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = ( TMcmp ` x ) ) -> ( TMfl ` h ) = %s )' % (IFL0, IFL0))
        sim2 = w.s([sim], 'a1i', '( h e. TMSt -> ( ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = ( TMcmp ` x ) ) -> ( TMfl ` h ) = %s ) )' % (IFL0, IFL0))
        rs = w.s([sim2], 'ss2rabi', '%s C_ %s' % (NZX, NFL))
        ss0 = w.s([rs], 'a1i', '( %s -> %s C_ %s )' % (ph, NZX, NFL))
        ss = clnss(w, ph, 'E', NZX, NFL, 'D', ss0)
        nfs = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NFL)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NFL)), seq], 'sseqtrrd',
                  '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NFL))
        cf = cfgcl(w, ph, 'E', NFL, 'D', tv, el, nfs, dd)
    else:
        W_ = 'incBits' if lab == 'tmiincs' else 'predBits'
        WORD = CC('( inclBool o. ( %s ` L ) )' % W_, YX4)
        U = UP('D', 'K', WORD)
        s1 = w.s([], 'ssrab2', '%s C_ TMSt' % NPX)
        s2 = w.s([w.s([s1], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPX)), seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPX))
        ss = clnss(w, ph, 'E', NPX, SS, U, s2)
        wcl = w.s([ll, w.inst('incbitscl' if lab == 'tmiincs' else 'predbitscl')], 'syl',
                  '( %s -> ( %s ` L ) e. Word 2o )' % (ph, W_))
        ib = w.s([wcl, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. ( %s ` L ) ) e. Word Gamma' )" % (ph, W_))
        g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
        x4 = w.s([w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % ph), xg, w.inst('ccatcl')], 'syl2anc',
                 "( %s -> %s e. Word Gamma' )" % (ph, YX4))
        ex = w.s([ib, x4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, WORD))
        uc = updcl(w, ph, 'D', 'K', WORD, tv, dd, mk['k']['K']['kd'], togk(w, ph, mk, WORD, 'K', ex))
        ssS = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
        cf = cfgcl(w, ph, 'E', SS, U, tv, el, ssS, uc)
    tx = hrssd(w, ph, phm, t, Cx, Dx, n, Dpost, ss, cf)
    union_from_S(w, ph, c, mk, tx, Dpost, n, nn0, cf)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()



SRCB = {'tmiizbs': ('tmiizb', 'iz'), 'tmiincbs': ('tmiincb', 'inc'), 'tmiprdbs': ('tmiprdb', 'prd')}
NFB = '{ h e. TMSt | ( TMfl ` h ) = if ( F = 0 , 1o , (/) ) }'


def fromsb_stmt(lab):
    src, fn = SRCB[lab]
    T, C = runs_stmt(src)
    Cc, Dd, n = triple_parts(C)
    Cn = Cc.replace(NPC, SS)
    post = CLN('E', NFB, 'D') if lab == 'tmiizbs' else Dd.replace(NPC, SS)
    return T, TRI(Cn, post, n)


def fromsb(lab):
    T, C = fromsb_stmt(lab)
    src, fname = SRCB[lab]
    _, C0 = runs_stmt(src)
    ph = cj(T)
    w = W(lab, 'The installed form ~ %s from any state (Lean\'s runs lemma is stated from any ` v ` ): the union '
               'over the pinned register values, ~ tmchiun .' % src)
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ['K'])
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    xg, dd = c[WRD('X', GAM)], c[STKD('D')]
    un = pred_labs(w, ph, c, fname)
    el = un[LAB('E')]
    t = w.s([], src, '( %s -> %s )' % (ph, tsub_text(C0, XM)))
    Cx, Dx, n = triple_parts(tsub_text(C0, XM))
    _, Dpost, _ = triple_parts(C)
    NPX = NP(XM['O'], XM['Q'], XM['R'])
    nn = c['N e. NN0']
    nn0 = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ph), w.inst('nnnn0')], 'syl', '( %s -> ( TMB ` N ) e. NN0 )' % ph)
    if lab == 'tmiizbs':
        IF_ = 'if ( F = 0 , 1o , (/) )'
        NZX = '{ h e. TMSt | ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = ( TMcmp ` x ) ) }' % IF_
        sim = w.s([], 'simpl', '( ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = ( TMcmp ` x ) ) -> ( TMfl ` h ) = %s )' % (IF_, IF_))
        sim2 = w.s([sim], 'a1i', '( h e. TMSt -> ( ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = ( TMcmp ` x ) ) -> ( TMfl ` h ) = %s ) )' % (IF_, IF_))
        rs = w.s([sim2], 'ss2rabi', '%s C_ %s' % (NZX, NFB))
        ss = clnss(w, ph, 'E', NZX, NFB, 'D', w.s([rs], 'a1i', '( %s -> %s C_ %s )' % (ph, NZX, NFB)))
        nfs = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NFB)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NFB)), seq], 'sseqtrrd',
                  '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NFB))
        cf = cfgcl(w, ph, 'E', NFB, 'D', tv, el, nfs, dd)
    else:
        V_ = '( F + 1 )' if lab == 'tmiincbs' else '( F - 1 )'
        fv_ = c['F e. NN0'] if lab == 'tmiincbs' else c['F e. NN']
        vn = w.s([fv_, w.inst('peano2nn0' if lab == 'tmiincbs' else 'nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, V_))
        WORD = CC('( encNatGam ` %s )' % V_, YX4)
        U = UP('D', 'K', WORD)
        s1 = w.s([], 'ssrab2', '%s C_ TMSt' % NPX)
        s2 = w.s([w.s([s1], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPX)), seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPX))
        ss = clnss(w, ph, 'E', NPX, SS, U, s2)
        eg = w.s([vn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` %s ) e. Word Gamma' )" % (ph, V_))
        g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
        x4 = w.s([w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % ph), xg, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, YX4))
        ex = w.s([eg, x4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, WORD))
        uc = updcl(w, ph, 'D', 'K', WORD, tv, dd, mk['k']['K']['kd'], togk(w, ph, mk, WORD, 'K', ex))
        ssS = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
        cf = cfgcl(w, ph, 'E', SS, U, tv, el, ssS, uc)
    tx = hrssd(w, ph, phm, t, Cx, Dx, n, Dpost, ss, cf)
    union_from_S(w, ph, c, mk, tx, Dpost, n, nn0, cf)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        if l in SRCB:
            fromsb(l)
        else:
            froms(l)
