"""T12: outputF at the machine (Lean ` outputF_runs ` ).

  t12entenc  the entries of a list of numbers are ` encodeOutput ` 's flattened word (Lean ` encodeOutput_eq ` )
  tmimesb    ` moveEntries x y s ` at the machine (~ tm2lmes at the concrete handlers, ~ tmclhi )
  tmiout     Lean's ` outputF_runs `

    MM_DB=sorties/t12.mm python3 tools/gen/t12_f_out.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t7_e_cmp import machine, togk
import t7c_h_lst as LST
from t9_f_exs import clear_extra
from t12_d_fal import to_init
from t10_u_s2s import me_bound_n
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
GM = "( w e. Word ( { 1 } X. 2o ) |-> ( w ++ <\" 4 \"> ) )"
PM = "( p e. NN0 |-> ( ( encNatGam ` p ) ++ <\" 4 \"> ) )"
FLAT = lambda w_: "( ( freeMnd ` Gamma' ) gsum ( %s o. %s ) )" % (PM, w_)
ST_ENTENC = '( W e. Word NN0 -> ( entries ` ( encNatGam o. W ) ) = %s )' % FLAT('W')

K3 = ['K', 'J', 'I']
DATA_MES = ((STKD('D'), '( D ` K ) = ( ( encListB ` L ) ++ R )'), ('L e. Word Word ( { 1 } X. 2o )', WRD('R', GAM)),
            ('B e. NN0', 'A. w e. ran L ( # ` w ) <_ B'))
TREE_MES = LST.TREE('mes', K3, DATA_MES)
CONCL_MES = TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP(UP('D', 'K', 'R'), 'J', '( ( entries ` ( reverse ` L ) ) ++ ( D ` J ) )')),
                '( ( ( # ` L ) x. ( ( 2 x. B ) + 6 ) ) + 3 )')
LST.TREES['tmimesb'] = TREE_MES
LST.CONCL['tmimesb'] = CONCL_MES
add12('tmimesb', TREE_MES, CONCL_MES)


def t12entenc():
    lab = 't12entenc'
    ph = 'W e. Word NN0'
    w = W(lab, 'The entries of the list ` W ` of numbers, each ` encodeNat p ` followed by a comma, are the flattened '
               'word of ~ df-encout (Lean: ` encodeOutput_eq ` , ` entries ( S.map encodeNat ) ` ).')
    s = w.s
    ww = s([], 'id', '( %s -> W e. Word NN0 )' % ph)
    ENG = 'encNatGam'
    fn = s([s([], 'encnatgamf', "encNatGam : NN0 --> Word Gamma'"), w.inst('ffn')], 'ax-mp', 'encNatGam Fn NN0')
    df5 = s([fn, w.inst('dffn5')], 'mpbi', 'encNatGam = ( p e. NN0 |-> ( encNatGam ` p ) )')
    efa = s([df5], 'a1i', '( %s -> encNatGam = ( p e. NN0 |-> ( encNatGam ` p ) ) )' % ph)
    gma = s([], 'eqidd', '( %s -> %s = %s )' % (ph, GM, GM))
    pp = '( %s /\\ p e. NN0 )' % ph
    pn = s([], 'simpr', '( %s -> p e. NN0 )' % pp)
    ev = s([pn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` p ) = ( inclBool o. ( encodeNat ` p ) ) )' % pp)
    ec = s([pn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` p ) e. Word 2o )' % pp)
    ib = s([ec, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. ( encodeNat ` p ) ) e. Word %s )' % (pp, BITS))
    eb = s([ev, ib], 'eqeltrd', '( %s -> ( encNatGam ` p ) e. Word %s )' % (pp, BITS))
    sub = s([], 'oveq1', '( w = ( encNatGam ` p ) -> ( w ++ <" 4 "> ) = ( ( encNatGam ` p ) ++ <" 4 "> ) )')
    co = s([eb, efa, gma, sub], 'fmptco', '( %s -> ( %s o. encNatGam ) = %s )' % (ph, GM, PM))
    ca = s([], 'coass', '( ( %s o. encNatGam ) o. W ) = ( %s o. ( encNatGam o. W ) )' % (GM, GM))
    c2 = s([co], 'coeq1d', '( %s -> ( ( %s o. encNatGam ) o. W ) = ( %s o. W ) )' % (ph, GM, PM))
    c3 = s([s([ca], 'a1i', '( %s -> ( ( %s o. encNatGam ) o. W ) = ( %s o. ( encNatGam o. W ) ) )' % (ph, GM, GM)), c2], 'eqtr3d',
           '( %s -> ( %s o. ( encNatGam o. W ) ) = ( %s o. W ) )' % (ph, GM, PM))
    lg = s([ww, w.inst('tm2lencgam')], 'syl', '( %s -> ( encNatGam o. W ) e. Word Word %s )' % (ph, BITS))
    ev2 = s([lg, w.inst('tm2lentval')], 'syl', "( %s -> ( entries ` ( encNatGam o. W ) ) = ( ( freeMnd ` Gamma' ) gsum ( %s o. ( encNatGam o. W ) ) ) )"
            % (ph, GM))
    g2 = s([c3], 'oveq2d', "( %s -> ( ( freeMnd ` Gamma' ) gsum ( %s o. ( encNatGam o. W ) ) ) = %s )" % (ph, GM, FLAT('W')))
    w.qed([ev2, g2], 'eqtrd', ST_ENTENC)
    return w.run()


def tmimesb():
    return LST.simple_b('tmimesb', 'mes', 'tm2lmes', K3,
                        'Lean\'s ` moveEntries_runs ` at the machine: wherever ` moveEntries x y s ` is installed, the list of bit '
                        'words on ` x ` (entries of length at most ` B ` ) is moved entry by entry onto ` y ` , reversed, and '
                        'its ` bra ` popped (~ tm2lmes at the concrete handlers, ~ tmclhi ).')


def clear_call(w, ph, B, R, k, A, E, leq):
    """B.call of ~ tm2fclr on stack k (labels A E); records the cost atom ( # ` ( Dcur ` k ) ) with its value in leq"""
    s = w.s
    txt, st0, g0 = R.S.vals[k]
    Dcur = R.S.D
    atom = '( # ` ( %s ` %s ) )' % (Dcur, k)
    if Dcur != 'D' or txt != DK(k):
        leq.append((atom, s([st0], 'fveq2d', '( %s -> %s = ( # ` %s ) )' % (ph, atom, txt)), txt, g0))
    ex = clear_extra(w, ph, B.mk, k)
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    B.call(R, 'tm2fclr', {'A': A, 'E': E, 'K': k, 'F': RDE, 'C': CNDA}, ex, [(k, '(/)', wrd0)])
    if leq and leq[-1][0] == atom:
        # keep the running bound small: ( # ` ( Dcur ` k ) ) -> ( # ` value )
        rn, n2 = w.rewrite(R.n, {atom: ('( # ` %s )' % txt, leq[-1][1])}, ph)
        R.tri, _, _, R.n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, neq=rn)
        leq.pop()
        if txt != DK(k):
            leq.append(('( # ` %s )' % txt, None, txt, g0))


def tmiout():
    lab = 'tmiout'
    T = numtree(TREE_OUT)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` outputF_runs ` at the machine: wherever ` outputF ` is installed, with the witness list ` U ` on 4 '
               'and ` m ` on 7 it clears the scratch stacks, reverses ` U ` onto 0 (~ tmilrevb ), moves its entries onto 1 '
               '(~ tmimesb ), puts ` m ` on top (~ tmime ) and clears 7 and 4: the stacks are '
               '` Frag.initStacks 1 ( encodeOutput ( m , U ) ) ` .')
    s = w.s
    c0 = Ctx(w, ph, T)
    ww, fn, bn, nn = c0['W e. Word NN0'], c0['F e. NN0'], c0['B e. NN0'], c0['N e. NN0']
    xg, yg = c0[WG('X')], c0[WG('Y')]
    E4 = ENCL('W', 'X')
    E7 = EWg('F', 'Y')
    eqs = {'4': (E4, enclg(w, ph, 'W', ww, 'X', xg)), '7': (E7, ewg_(w, ph, 'F', fn, 'Y', yg))}
    B = Base(w, ph, T, N8, 'out', eqs)
    c, mk = B.c, B.mk
    LM = FRAGS['out'].lmap()
    F_ = FRAGS['out']
    R = B.run()
    leq = []
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    # 1-6. clear 0 1 2 3 5 6
    for i, k in enumerate(['0', '1', '2', '3', '5', '6']):
        nxt = LM['Z%d' % (i + 2)] if i < 5 else None
        if nxt is None:
            fn0, cks0, en0, exn0 = F_.children[0]
            nxt = LM[en0]
        clear_call(w, ph, B, R, k, LM['Z%d' % (i + 1)], nxt, leq)

    def cp(j):
        fn_, cks, en, exn = F_.children[j]
        return PL('P', F_.slot(j)), LM[exn]
    # 7. revList 4 0 2
    P, E = cp(0)
    RW = '( reverse ` W )'
    rww = s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RW))
    V0 = '( ( encList ` %s ) ++ (/) )' % RW
    g0 = B.g(V0, enclg(w, ph, RW, rww, '(/)', wrd0))
    B.call(R, 'tmilrevb', {'K': '4', 'J': '0', 'I': '2', 'L': 'W', 'R': 'X', 'B': 'B', 'P': P, 'E': E},
           {'W e. Word NN0': ww, RALB('W', 'B'): c[RALB('W', 'B')]}, [('4', 'X', xg), ('0', V0, g0)])
    # 8. moveEntries 0 1 2 on L = encNatGam o. reverse W
    P, E = cp(1)
    L = '( encNatGam o. %s )' % RW
    lw = s([rww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, L, BITS))
    le = s([rww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, RW, L))
    V0b = '( ( encListB ` %s ) ++ (/) )' % L
    v0 = s([R.S.vals['0'][1], s([le], 'oveq1d', '( %s -> %s = %s )' % (ph, V0, V0b))], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, R.S.D, V0b))
    rr = s([s([ww, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran W )' % (ph, RW)), c[RALB('W', 'B')], w.inst('ssralv')], 'sylc',
           '( %s -> %s )' % (ph, RALB(RW, 'B')))
    rb = s([rww, bn, rr, w.inst('tm2lrnenc')], 'syl3anc', '( %s -> A. w e. ran %s ( # ` w ) <_ B )' % (ph, L))
    ENT = '( ( entries ` ( reverse ` %s ) ) ++ (/) )' % L
    rlw = s([lw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word Word %s )' % (ph, L, BITS))
    eg = s([rlw, w.inst('tm2lentcl')], 'syl', "( %s -> ( entries ` ( reverse ` %s ) ) e. Word Gamma' )" % (ph, L))
    gE = B.g(ENT, wgcat(w, ph, '( entries ` ( reverse ` %s ) )' % L, '(/)', eg, wrd0))
    B.call(R, 'tmimesb', {'K': '0', 'J': '1', 'I': '2', 'L': L, 'R': '(/)', 'B': 'B', 'P': P, 'E': E},
           {'( %s ` 0 ) = %s' % (R.S.D, V0b): v0, '%s e. Word Word %s' % (L, BITS): lw,
            'A. w e. ran %s ( # ` w ) <_ B' % L: rb, WG('(/)'): wrd0},
           [('0', '(/)', wrd0), ('1', ENT, gE)])
    # 9. moveEntry 7 1 2
    P, E = cp(2)
    WF = '( encNatGam ` F )'
    V1 = '( %s ++ ( <" 4 "> ++ %s ) )' % (WF, ENT)
    g1 = B.g(V1, ewg_(w, ph, 'F', fn, ENT, gE))
    B.call(R, 'tmime', {'K': '7', 'J': '1', 'I': '2', 'W': WF, 'X': 'Y', 'P': P, 'E': E},
           {WRD(WF, BITS): engb(w, ph, 'F', fn)}, [('7', 'Y', yg), ('1', V1, g1)])
    # 10-11. clear 7 , clear 4
    Z7 = [l for l in F_.labels if l not in ('Z1', 'Z2', 'Z3', 'Z4', 'Z5', 'Z6')]
    assert Z7 == ['Z7', 'Z8'], Z7
    clear_call(w, ph, B, R, '7', LM['Z7'], LM['Z8'], leq)
    clear_call(w, ph, B, R, '4', LM['Z8'], 'E', leq)
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    print('COST', n, file=sys.stderr)
    Dc = triple_D(D)
    # stack 1: V1 = ( F encodeOutput W )
    OUT = '( F encodeOutput W )'
    er = s([eg, w.inst('ccatrid')], 'syl', '( %s -> %s = ( entries ` ( reverse ` %s ) ) )' % (ph, ENT, L))
    ef = s([s([], 'encnatgamf', "encNatGam : NN0 --> Word Gamma'")], 'a1i', "( %s -> encNatGam : NN0 --> Word Gamma' )" % ph)
    rc = s([ww, ef, w.inst('revco')], 'syl2anc', '( %s -> ( encNatGam o. ( reverse ` W ) ) = ( reverse ` ( encNatGam o. W ) ) )' % ph)
    LW_ = '( encNatGam o. W )'
    lwg = s([ww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LW_, BITS))
    rr2 = s([s([rc], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( reverse ` %s ) ) )' % (ph, L, LW_)),
             s([lwg, w.inst('revrev')], 'syl', '( %s -> ( reverse ` ( reverse ` %s ) ) = %s )' % (ph, LW_, LW_))], 'eqtrd',
            '( %s -> ( reverse ` %s ) = %s )' % (ph, L, LW_))
    en = s([s([rr2], 'fveq2d', '( %s -> ( entries ` ( reverse ` %s ) ) = ( entries ` %s ) )' % (ph, L, LW_)),
            s([ww, w.inst('t12entenc')], 'syl', '( %s -> ( entries ` %s ) = %s )' % (ph, LW_, FLAT('W')))], 'eqtrd',
           '( %s -> ( entries ` ( reverse ` %s ) ) = %s )' % (ph, L, FLAT('W')))
    ent = s([er, en], 'eqtrd', '( %s -> %s = %s )' % (ph, ENT, FLAT('W')))
    r1, x1 = w.rewrite(V1, {ENT: (FLAT('W'), ent)}, ph)
    ov = s([fn, ww, w.inst('encoutval')], 'syl2anc', '( %s -> %s = %s )' % (ph, OUT, x1))
    v1 = s([r1, s([ov], 'eqcomd', '( %s -> %s = %s )' % (ph, x1, OUT))], 'eqtrd', '( %s -> %s = %s )' % (ph, V1, OUT))
    vals = {}
    for k in N8:
        txt, st, g = R.S.vals[k]
        if k == '1':
            assert txt == V1, txt
            vals[k] = s([st, v1], 'eqtrd', '( %s -> ( %s ` 1 ) = %s )' % (ph, Dc, OUT))
        else:
            assert txt == '(/)', (k, txt)
            vals[k] = st
    og = s([fn, ww, w.inst('encoutcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, OUT))
    ov_ = s([og], 'elexd', '( %s -> %s e. _V )' % (ph, OUT))
    deq = to_init(w, ph, B, R, '1', OUT, ov_, og, vals, Dc)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, deq, Dc, INIT('1', OUT)))
    # the bound
    cl = Closure(w, ph, {'B': ('NN0', bn), 'N': ('NN0', nn), 'F': ('NN0', fn)})
    for k in N8:
        cl.leaf(LEN(DK(k)), 'NN0', s([B.S0.vals[k][2], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN(DK(k)))))
    for X_, g_ in (('X', xg), ('Y', yg), ('W', ww)):
        cl.leaf(LEN(X_), 'NN0', s([g_, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN(X_))))
    hyps = []
    for atom, eqst, txt, g_ in leq:
        if txt == '(/)' or eqst is None and atom in (LEN('X'), LEN('Y')):
            continue
        cl.leaf(atom, 'NN0', s([g_, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, atom)))
    h0 = s([], 'hash0', '( # ` (/) ) = 0')
    hyps.append(s([h0], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ph))
    cl.atom('( # ` (/) )')
    # # L = # W
    LL = '( # ` %s )' % L
    ll = s([s([rww, ef, w.inst('lenco')], 'syl2anc',
              '( %s -> %s = ( # ` %s ) )' % (ph, LL, RW)),
            s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqtrd', '( %s -> %s = ( # ` W ) )' % (ph, LL))
    cl.leaf(LL, 'NN0', s([ll, cl.mem(LEN('W'), 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, LL)))
    hyps.append(ll)
    hyps.append(s([ll], 'oveq1d', '( %s -> ( %s x. ( ( 2 x. B ) + 6 ) ) = ( ( # ` W ) x. ( ( 2 x. B ) + 6 ) ) )' % (ph, LL)))
    from t10_n_rgf import tmbn
    cl.leaf('( TMB ` N )', 'NN0', tmbn(w, ph, 'N', nn))
    cl.leaf('( TMB ` B )', 'NN0', tmbn(w, ph, 'B', bn))
    mb = me_bound_n(w, ph, 'F', fn, c[LT2('F', 'N')], 'N', nn, cl)
    hyps.append(mb)
    le_ = linarith(w, ph, hyps, '%s <_ %s' % (n, OUTC), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, OUTC, cl.mem(OUTC, 'NN0'), le_)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
