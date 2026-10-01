"""T15 (f): the pushNum installation at the concrete program (t15kpnv) and its length lemma."""
import os, sys, json
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
import num

L_ = '( 2nd ` ( 1st ` T ) )'
S_ = '( TM2Stmt ` T )'
G1 = '( 1st ` ( 1st ` T ) )'
HL = 'A. v e. Word A ( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. %s )' % L_
HM = ('A. v e. Word A ( ( ( # ` v ) <_ ; 3 0 /\\ ( R TMWalk v ) e. %s ) -> '
      '( M ` ( TMLab ` v ) ) = ( R TMWalk v ) )' % S_)
CTX = ['( ( T e. _V /\\ R e. _V ) /\\ %s = TMGam /\\ ( 2nd ` T ) = TMSt )' % G1,
       '( ( 0 ... ; 3 0 ) C_ A /\\ A C_ NN0 )', HL, HM]
LEN = '( # ` ( encNatGam ` N ) )'
DOM = '( 0 ... ( %s + 1 ) )' % LEN
PF = '( k e. %s |-> if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) )' % (DOM, LEN)
WD = '( <" 4 "> ++ ( reverse ` ( encNatGam ` N ) ) )'


def STMT(k):
    return ('<. 0 , <. K , <. ( ( 2nd ` T ) X. { ( %s ` %s ) } ) , <. 5 , ( ( 2nd ` T ) X. { ( P ` ( %s + 1 ) ) } ) >. >. >. >.'
            % (WD, k, k))


def t15enl():
    w = W('t15enl', 'The encoding of N has at most N letters.')
    ph = 'N e. NN0'
    two = w.s([], '2z', '2 e. ZZ')
    u2 = w.s([two, w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    u2d = a1(w, ph, u2, '2 e. ( ZZ>= ` 2 )')
    idn = w.s([], 'id', '( N e. NN0 -> N e. NN0 )')
    lt = w.s([u2d, idn, w.inst('bernneq3')], 'syl2anc', '( N e. NN0 -> N < ( 2 ^ N ) )')
    le = w.s([idn, idn, lt, w.inst('encnatlenpow')], 'syl3anc', '( N e. NN0 -> ( # ` ( encodeNat ` N ) ) <_ N )')
    gl = w.s([idn, w.inst('encnatgamlen')], 'syl', '( N e. NN0 -> ( # ` ( encNatGam ` N ) ) = ( # ` ( encodeNat ` N ) ) )')
    le2 = w.s([gl, le], 'eqbrtrd', '( N e. NN0 -> ( # ` ( encNatGam ` N ) ) <_ N )')
    gw = w.s([idn, w.inst('encnatgamcl')], 'syl', "( N e. NN0 -> ( encNatGam ` N ) e. Word Gamma' )")
    gn = w.s([gw, w.inst('lencl')], 'syl', '( N e. NN0 -> ( # ` ( encNatGam ` N ) ) e. NN0 )')
    gr = w.s([gn], 'nn0red', '( N e. NN0 -> ( # ` ( encNatGam ` N ) ) e. RR )')
    nr = w.s([idn], 'nn0red', '( N e. NN0 -> N e. RR )')
    one = a1(w, ph, w.s([], '1re', '1 e. RR'), '1 e. RR')
    w.qed([gr, nr, one, le2], 'leadd1dd', '( N e. NN0 -> ( ( # ` ( encNatGam ` N ) ) + 1 ) <_ ( N + 1 ) )')
    return w


def t15kpnv():
    lab = 't15kpnv'
    w = W(lab, 'The installation predicate ~ df-tmipnv holds at the concrete program.')
    hs = []
    forms = CTX + ['W e. Word A', '( ( # ` W ) + 1 ) <_ ; 3 0', 'P = ( TMpnF W N X )', 'E e. %s' % L_,
                   '( R TMWalk W ) = ( TMnpnv K N T P E )', 'K e. ( 0 ..^ 8 )', 'E = X', 'N e. NN0',
                   '( 0 ... ( N + 1 ) ) C_ A']
    for i, f in enumerate(forms):
        n = 'h%d' % (i + 1)
        w.lines.append('%s::%s.%d |- ( ph -> %s )' % (n, lab, i + 1, f))
        hs.append(n)
    h = dict(zip(['t', 'a', 'l', 'm', 'w', 'd', 'p', 'e', 'r', 'k', 'x', 'n', 'z'], hs))
    tr = w.s([h['t']], 'simp1d', '( ph -> ( T e. _V /\\ R e. _V ) )')
    tv = w.s([tr], 'simpld', '( ph -> T e. _V )')
    rv = w.s([tr], 'simprd', '( ph -> R e. _V )')
    tg = w.s([h['t']], 'simp2d', '( ph -> %s = TMGam )' % G1)
    ts = w.s([h['t']], 'simp3d', '( ph -> ( 2nd ` T ) = TMSt )')
    sA = w.s([h['a']], 'simprd', '( ph -> A C_ NN0 )')
    # domain in the alphabet
    gw = w.s([h['n'], w.inst('encnatgamcl')], 'syl', "( ph -> ( encNatGam ` N ) e. Word Gamma' )")
    ln = w.s([gw, w.inst('lencl')], 'syl', '( ph -> %s e. NN0 )' % LEN)
    l1 = w.s([ln, w.inst('peano2nn0')], 'syl', '( ph -> ( %s + 1 ) e. NN0 )' % LEN)
    n1 = w.s([h['n'], w.inst('peano2nn0')], 'syl', '( ph -> ( N + 1 ) e. NN0 )')
    en = w.s([h['n'], w.inst('t15enl')], 'syl', '( ph -> ( %s + 1 ) <_ ( N + 1 ) )' % LEN)
    l1z = w.s([l1], 'nn0zd', '( ph -> ( %s + 1 ) e. ZZ )' % LEN)
    n1z = w.s([n1], 'nn0zd', '( ph -> ( N + 1 ) e. ZZ )')
    ez = w.s([l1z, n1z, w.inst('eluz')], 'syl2anc', '( ph -> ( ( N + 1 ) e. ( ZZ>= ` ( %s + 1 ) ) <-> ( %s + 1 ) <_ ( N + 1 ) ) )' % (LEN, LEN))
    eu = w.s([en, ez], 'mpbird', '( ph -> ( N + 1 ) e. ( ZZ>= ` ( %s + 1 ) ) )' % LEN)
    fs = w.s([eu, w.inst('fzss2')], 'syl', '( ph -> %s C_ ( 0 ... ( N + 1 ) ) )' % DOM)
    dA = w.s([fs, h['z']], 'sstrd', '( ph -> %s C_ A )' % DOM)
    # P as the mapping
    df = w.s([], 'df-tmpnf', '( TMpnF W N X ) = %s' % PF)
    ppf = w.s([h['p'], df], 'eqtrdi', '( ph -> P = %s )' % PF)
    xl = w.s([h['x'], h['e']], 'eqeltrrd', '( ph -> X e. %s )' % L_)
    # t15ap at W, index k (under a context)

    def labk(ante, kstep, k, sub):
        """( ante -> ( W ++ <" k "> ) e. Word A ), ( ante -> ( ( # ` ( W ++ <" k "> ) ) + 0 ) <_ ; 3 0 )"""
        wa = sub(h['w']); da = sub(h['d']); sa = sub(sA)
        j1 = w.s([wa, da], 'jca', '( %s -> ( W e. Word A /\\ ( ( # ` W ) + 1 ) <_ ; 3 0 ) )' % ante)
        z0 = a1(w, ante, w.s([], '0nn0', '0 e. NN0'), '0 e. NN0')
        p1 = a1(w, ante, w.s([], '0p1e1', '( 0 + 1 ) = 1'), '( 0 + 1 ) = 1')
        j2 = w.s([w.s([z0, p1], 'jca', '( %s -> ( 0 e. NN0 /\\ ( 0 + 1 ) = 1 ) )' % ante),
                  w.s([kstep, sa], 'jca', '( %s -> ( %s e. A /\\ A C_ NN0 ) )' % (ante, k))], 'jca',
                 '( %s -> ( ( 0 e. NN0 /\\ ( 0 + 1 ) = 1 ) /\\ ( %s e. A /\\ A C_ NN0 ) ) )' % (ante, k))
        jj = w.s([j1, j2], 'jca', '( %s -> ( ( W e. Word A /\\ ( ( # ` W ) + 1 ) <_ ; 3 0 ) /\\ ( ( 0 e. NN0 /\\ ( 0 + 1 ) = 1 ) /\\ ( %s e. A /\\ A C_ NN0 ) ) ) )' % (ante, k))
        Wk = '( W ++ <" %s "> )' % k
        t = w.s([jj, w.inst('t15ap')], 'syl', '( %s -> ( ( ( TMLab ` W ) ` %s ) = ( TMLab ` %s ) /\\ %s e. Word A /\\ ( ( # ` %s ) + 0 ) <_ ; 3 0 ) )' % (ante, k, Wk, Wk, Wk))
        a = w.s([t], 'simp2d', '( %s -> %s e. Word A )' % (ante, Wk))
        b = w.s([t], 'simp3d', '( %s -> ( ( # ` %s ) + 0 ) <_ ; 3 0 )' % (ante, Wk))
        return a, b, z0

    # (a) P : DOM --> L
    pk = '( ph /\\ k e. %s )' % DOM
    sub1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pk, formula(w, st).split(' -> ', 1)[1][:-2]))
    km = w.s([], 'simpr', '( %s -> k e. %s )' % (pk, DOM))
    kA = w.s([sub1(dA), km], 'sseldd', '( %s -> k e. A )' % pk)
    a_, b_, z0 = labk(pk, kA, 'k', sub1)
    hl1 = sub1(h['l'])
    jl = w.s([hl1, w.s([a_, b_, z0], '3jca', '( %s -> ( ( W ++ <" k "> ) e. Word A /\\ ( ( # ` ( W ++ <" k "> ) ) + 0 ) <_ ; 3 0 /\\ 0 e. NN0 ) )' % pk)],
             'jca', '( %s -> ( %s /\\ ( ( W ++ <" k "> ) e. Word A /\\ ( ( # ` ( W ++ <" k "> ) ) + 0 ) <_ ; 3 0 /\\ 0 e. NN0 ) ) )' % (pk, HL))
    lm = w.s([jl, w.inst('t15lab')], 'syl', '( %s -> ( TMLab ` ( W ++ <" k "> ) ) e. %s )' % (pk, L_))
    iv = w.s([sub1(xl), lm], 'ifcld', '( %s -> if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) e. %s )' % (pk, LEN, L_))
    fm = w.s([iv], 'fmptd', '( ph -> %s : %s --> %s )' % (PF, DOM, L_))
    fq = w.s([ppf], 'feq1d', '( ph -> ( P : %s --> %s <-> %s : %s --> %s ) )' % (DOM, L_, PF, DOM, L_))
    fa = w.s([fm, fq], 'mpbird', '( ph -> P : %s --> %s )' % (DOM, L_))
    # (b) last value
    pe = '( ph /\\ k = ( %s + 1 ) )' % LEN
    ke = w.s([], 'simpr', '( %s -> k = ( %s + 1 ) )' % (pe, LEN))
    it = w.s([ke], 'iftrued', '( %s -> if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) = X )' % (pe, LEN))
    lf = w.s([l1, w.s([], 'nn0fz0', '( ( %s + 1 ) e. NN0 <-> ( %s + 1 ) e. %s )' % (LEN, LEN, DOM))], 'sylib', '( ph -> ( %s + 1 ) e. %s )' % (LEN, DOM))
    xv = w.s([xl], 'elexd', '( ph -> X e. _V )')
    dfd = a1(w, 'ph', w.s([], 'eqid', '%s = %s' % (PF, PF)), '%s = %s' % (PF, PF))
    fl = w.s([dfd, it, lf, xv], 'fvmptd', '( ph -> ( %s ` ( %s + 1 ) ) = X )' % (PF, LEN))
    fl2 = w.s([ppf], 'fveq1d', '( ph -> ( P ` ( %s + 1 ) ) = ( %s ` ( %s + 1 ) ) )' % (LEN, PF, LEN))
    xe = w.s([h['x']], 'eqcomd', '( ph -> X = E )')
    fb = w.s([fl2, fl, xe], '3eqtrd', '( ph -> ( P ` ( %s + 1 ) ) = E )' % LEN)
    # (c) the pushes
    pc = '( ph /\\ k e. ( 0 ..^ ( %s + 1 ) ) )' % LEN
    sub2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pc, formula(w, st).split(' -> ', 1)[1][:-2]))
    kc = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ ( %s + 1 ) ) )' % (pc, LEN))
    kdm = w.s([kc, w.inst('elfzofz')], 'syl', '( %s -> k e. %s )' % (pc, DOM))
    kn = w.s([kc, w.inst('elfzonn0')], 'syl', '( %s -> k e. NN0 )' % pc)
    kA2 = w.s([sub2(dA), kdm], 'sseldd', '( %s -> k e. A )' % pc)
    klt = w.s([kc, w.inst('elfzolt2')], 'syl', '( %s -> k < ( %s + 1 ) )' % (pc, LEN))
    kne = w.s([klt], 'ltned', '( %s -> k =/= ( %s + 1 ) )' % (pc, LEN))
    knq = w.s([kne], 'neneqd', '( %s -> -. k = ( %s + 1 ) )' % (pc, LEN))
    ifk = w.s([knq], 'iffalsed', '( %s -> if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) = ( TMLab ` ( W ++ <" k "> ) ) )' % (pc, LEN))
    a2, b2, z02 = labk(pc, kA2, 'k', sub2)
    lx = w.s([], 'fvexd', '( %s -> ( TMLab ` ( W ++ <" k "> ) ) e. _V )' % pc)
    ifx = w.s([ifk, lx], 'eqeltrd', '( %s -> if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) e. _V )' % (pc, LEN))
    pv0 = w.s([kdm, ifx, w.s([], 'eqid', '%s = %s' % (PF, PF))], 'fvmpt2' if False else 'fvmpt2', '')
    w.lines.pop()
    fe = w.s([], 'eqid', '%s = %s' % (PF, PF))
    fv2 = w.s([fe], 'fvmpt2', '( ( k e. %s /\\ if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) e. _V ) -> ( %s ` k ) = if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) )' % (DOM, LEN, PF, LEN))
    pv1 = w.s([kdm, ifx, fv2], 'syl2anc', '( %s -> ( %s ` k ) = if ( k = ( %s + 1 ) , X , ( TMLab ` ( W ++ <" k "> ) ) ) )' % (pc, PF, LEN))
    pv2 = w.s([sub2(ppf)], 'fveq1d', '( %s -> ( P ` k ) = ( %s ` k ) )' % (pc, PF))
    pv = w.s([pv2, pv1, ifk], '3eqtrd', '( %s -> ( P ` k ) = ( TMLab ` ( W ++ <" k "> ) ) )' % pc)
    # walk
    wk = w.s([sub2(rv), sub2(h['w']), kA2, w.inst('tmwalks1')], 'syl3anc', '( %s -> ( R TMWalk ( W ++ <" k "> ) ) = ( ( R TMWalk W ) ` k ) )' % pc)
    w2 = w.s([sub2(h['r'])], 'fveq1d', '( %s -> ( ( R TMWalk W ) ` k ) = ( ( TMnpnv K N T P E ) ` k ) )' % pc)
    NB = PNV_BODY
    dfn = w.s([], 'df-tmnpnv', '( TMnpnv K N T P E ) = %s' % NB)
    dfnd = a1(w, pc, dfn, '( TMnpnv K N T P E ) = %s' % NB)
    pj = '( %s /\\ j = k )' % pc
    body = NB[len('( j e. NN0 |-> '):-2]
    eqj = w.s([], 'id', '( j = k -> j = k )')
    st, val = cong(w, body, {'j': 'k'}, 'j = k', {'j': eqj})
    stj = w.s([st], 'adantl', '( %s -> %s = %s )' % (pj, body, val))
    ox = w.s([], 'opex', '%s e. _V' % val)
    oxd = a1(w, pc, ox, '%s e. _V' % val)
    w3 = w.s([dfnd, stj, kn, oxd], 'fvmptd', '( %s -> ( ( TMnpnv K N T P E ) ` k ) = %s )' % (pc, val))
    assert val == STMT('k'), val
    wall = w.s([wk, w2, w3], '3eqtrd', '( %s -> ( R TMWalk ( W ++ <" k "> ) ) = %s )' % (pc, val))
    # typing of the statement
    kk = w.s([sub2(tg), sub2(h['k'])], 'jca', '( %s -> ( %s = TMGam /\\ K e. ( 0 ..^ 8 ) ) )' % (pc, G1))
    kd = w.s([kk, w.inst('t15kdom')], 'syl', "( %s -> ( K e. dom %s /\\ ( %s ` K ) = Gamma' ) )" % (pc, G1, G1))
    kd1 = w.s([kd], 'simpld', '( %s -> K e. dom %s )' % (pc, G1))
    kd2 = w.s([kd], 'simprd', "( %s -> ( %s ` K ) = Gamma' )" % (pc, G1))
    g4 = w.s([w.s([], 'gamma4', "4 e. Gamma'"), w.inst('s1cl')], 'ax-mp', "<\" 4 \"> e. Word Gamma'")
    g4d = a1(w, pc, g4, "<\" 4 \"> e. Word Gamma'")
    rvw = w.s([sub2(gw), w.inst('revcl')], 'syl', "( %s -> ( reverse ` ( encNatGam ` N ) ) e. Word Gamma' )" % pc)
    wdw = w.s([g4d, rvw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (pc, WD))
    wl = w.s([g4d, rvw, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` <" 4 "> ) + ( # ` ( reverse ` ( encNatGam ` N ) ) ) ) )' % (pc, WD))
    s1l = a1(w, pc, w.s([], 's1len', '( # ` <" 4 "> ) = 1'), '( # ` <" 4 "> ) = 1')
    rl = w.s([sub2(gw), w.inst('revlen')], 'syl', '( %s -> ( # ` ( reverse ` ( encNatGam ` N ) ) ) = %s )' % (pc, LEN))
    wl2 = w.s([s1l, rl], 'oveq12d', '( %s -> ( ( # ` <" 4 "> ) + ( # ` ( reverse ` ( encNatGam ` N ) ) ) ) = ( 1 + %s ) )' % (pc, LEN))
    lnc = w.s([sub2(ln)], 'nn0cnd', '( %s -> %s e. CC )' % (pc, LEN))
    onec = a1(w, pc, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    ac = w.s([onec, lnc], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (pc, LEN, LEN))
    wl3 = w.s([wl, wl2, ac], '3eqtrd', '( %s -> ( # ` %s ) = ( %s + 1 ) )' % (pc, WD, LEN))
    fz = w.s([wl3], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ ( %s + 1 ) ) )' % (pc, WD, LEN))
    kc2 = w.s([kc, fz], 'eleqtrrd', '( %s -> k e. ( 0 ..^ ( # ` %s ) ) )' % (pc, WD))
    let = w.s([wdw, kc2, w.inst('wrdsymbcl')], 'syl2anc', "( %s -> ( %s ` k ) e. Gamma' )" % (pc, WD))
    gex = a1(w, pc, w.s([], 'gammaex', "Gamma' e. _V"), "Gamma' e. _V")
    c1 = w.s([w.s([gex, let], 'jca', "( %s -> ( Gamma' e. _V /\\ ( %s ` k ) e. Gamma' ) )" % (pc, WD)), w.inst('t15cst')], 'syl',
             "( %s -> ( ( 2nd ` T ) X. { ( %s ` k ) } ) e. ( Gamma' ^m ( 2nd ` T ) ) )" % (pc, WD))
    e1 = w.s([kd2], 'oveq1d', "( %s -> ( ( %s ` K ) ^m ( 2nd ` T ) ) = ( Gamma' ^m ( 2nd ` T ) ) )" % (pc, G1))
    c1b = w.s([c1, e1], 'eleqtrrd', "( %s -> ( ( 2nd ` T ) X. { ( %s ` k ) } ) e. ( ( %s ` K ) ^m ( 2nd ` T ) ) )" % (pc, WD, G1))
    k1 = w.s([kc, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. %s )' % (pc, DOM))
    pk1 = w.s([sub2(fa), k1], 'ffvelcdmd', '( %s -> ( P ` ( k + 1 ) ) e. %s )' % (pc, L_))
    lex = a1(w, pc, w.s([], 'fvex', '%s e. _V' % L_), '%s e. _V' % L_)
    c2 = w.s([w.s([lex, pk1], 'jca', '( %s -> ( %s e. _V /\\ ( P ` ( k + 1 ) ) e. %s ) )' % (pc, L_, L_)), w.inst('t15cst')], 'syl',
             '( %s -> ( ( 2nd ` T ) X. { ( P ` ( k + 1 ) ) } ) e. ( %s ^m ( 2nd ` T ) ) )' % (pc, L_))
    tv2 = sub2(tv)
    gt = w.s([tv2, c2, w.inst('tm2goto')], 'syl2anc', '( %s -> <. 5 , ( ( 2nd ` T ) X. { ( P ` ( k + 1 ) ) } ) >. e. %s )' % (pc, S_))
    jk = w.s([kd1, c1b], 'jca', "( %s -> ( K e. dom %s /\\ ( ( 2nd ` T ) X. { ( %s ` k ) } ) e. ( ( %s ` K ) ^m ( 2nd ` T ) ) ) )" % (pc, G1, WD, G1))
    ty = w.s([tv2, jk, gt, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (pc, val, S_))
    j1 = w.s([sub2(h['l']), sub2(h['m'])], 'jca', '( %s -> ( %s /\\ %s ) )' % (pc, HL, HM))
    j2 = w.s([a2, b2, z02], '3jca', '( %s -> ( ( W ++ <" k "> ) e. Word A /\\ ( ( # ` ( W ++ <" k "> ) ) + 0 ) <_ ; 3 0 /\\ 0 e. NN0 ) )' % pc)
    j3 = w.s([wall, ty], 'jca', '( %s -> ( ( R TMWalk ( W ++ <" k "> ) ) = %s /\\ %s e. %s ) )' % (pc, val, val, S_))
    o = w.s([j1, j2, j3, w.inst('t15own')], 'syl3anc', '( %s -> ( ( M ` ( TMLab ` ( W ++ <" k "> ) ) ) = %s /\\ ( TMLab ` ( W ++ <" k "> ) ) e. %s ) )' % (pc, val, L_))
    o1 = w.s([o], 'simpld', '( %s -> ( M ` ( TMLab ` ( W ++ <" k "> ) ) ) = %s )' % (pc, val))
    e2 = w.s([pv], 'fveq2d', '( %s -> ( M ` ( P ` k ) ) = ( M ` ( TMLab ` ( W ++ <" k "> ) ) ) )' % pc)
    ok = w.s([e2, o1], 'eqtrd', '( %s -> ( M ` ( P ` k ) ) = %s )' % (pc, val))
    fc = w.s([ok], 'ralrimiva', '( ph -> A. k e. ( 0 ..^ ( %s + 1 ) ) ( M ` ( P ` k ) ) = %s )' % (LEN, val))
    ab = w.s([fa, fb], 'jca', '( ph -> ( P : %s --> %s /\\ ( P ` ( %s + 1 ) ) = E ) )' % (DOM, L_, LEN))
    rhs = '( ( P : %s --> %s /\\ ( P ` ( %s + 1 ) ) = E ) /\\ A. k e. ( 0 ..^ ( %s + 1 ) ) ( M ` ( P ` k ) ) = %s )' % (DOM, L_, LEN, LEN, val)
    allc = w.s([ab, fc], 'jca', '( ph -> %s )' % rhs)
    dft = w.s([], 'df-tmipnv', '( TMIpnv K N T M P E <-> %s )' % rhs)
    w.qed([allc, dft], 'sylibr', '( ph -> TMIpnv K N T M P E )')
    return w


def formula(w, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            return l.split('|- ', 1)[1]
    raise KeyError(st)


GENS = {'t15enl': t15enl, 't15kpnv': t15kpnv}

if __name__ == '__main__':
    for lab in sys.argv[1:] or list(GENS):
        w = GENS[lab]()
        if w.run() and lab == 't15kpnv':
            REG = os.path.join(ROOT, 'scratch', 't15', 'kinds.json')
            reg = json.load(open(REG)); reg['TMIpnv'] = {'label': 't15kpnv', 'r': 1}
            json.dump(reg, open(REG, 'w'), indent=1)
