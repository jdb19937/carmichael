"""T12: callees of the scales at the machine.

  tmipnv    ` pushNum K N ` at a class ` N ` (the predicate ` TMIpnv ` , ~ tm2fpnw )
  tmipnvb   its ` B ` form ( ` N < 2 ^ B ` , Lean ` pushNum_le_B ` )
  tmiprdbl  ` predNum ` on a bit length: ` bl F ` becomes ` Nlog F ` (Lean ` predNum_le_B' ` with ` bl_pred ` )

    MM_DB=sorties/t12.mm python3 tools/gen/t12_g_sc0.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t10_n_rgf import tmbn
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
WN = '( encNatGam ` N )'
TREE_PNV = ((T_PHM7, FRAGS['pnv'].pred()), (IDX('K'), ('N e. NN0', STKD('D'))))
CONCL_PNV = TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP('D', 'K', EWg('N', DK('K')))), '( ( # ` %s ) + 1 )' % WN)
add12('tmipnv', TREE_PNV, CONCL_PNV)
TREE_PNVB = ((T_PHM7, FRAGS['pnv'].pred()), (IDX('K'), ('N e. NN0', STKD('D')), ('B e. NN0', LT2('N', 'B'))))
CONCL_PNVB = TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP('D', 'K', EWg('N', DK('K')))), '( TMB ` B )')
add12('tmipnvb', TREE_PNVB, CONCL_PNVB)
BLF = '( bl ` F )'
TREE_PBL = ((T_PHM7, 'TMIprd K J T M P E'), (IDX('K'), IDX('J'), 'K =/= J'),
            (('F e. NN0', 'N e. NN0', LT2(BLF, 'N')), (WG('X'), STKD('D')), '( D ` K ) = %s' % EWg(BLF, 'X')))
CONCL_PBL = TRI(CLN('( P ` 0 )', S, 'D'), CLN('E', S, UP('D', 'K', EWg('( 2 Nlog F )', 'X'))), '( TMB ` N )')
add12('tmiprdbl', TREE_PBL, CONCL_PBL)


def tmipnv():
    lab = 'tmipnv'
    T = TREE_PNV
    ph = cj(T)
    w = W(lab, 'Lean\'s ` pushNum_runs ` at a number ` N ` : wherever ` TMIpnv K N ` is installed, the comma and the bits of '
               '` N ` from the last one are pushed on ` K ` , one label each (~ tm2fpnw ), ending at the exit.')
    s = w.s
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ['K'])
    nn = c['N e. NN0']
    u = s([c[FRAGS['pnv'].pred()], w.inst('tmipnvu')], 'syl', '( %s -> %s )' % (ph, PNV_RHS))
    pf = s([s([u], 'simpld', '( %s -> ( P : ( 0 ... %s ) --> ( 2nd ` ( 1st ` T ) ) /\\ ( P ` %s ) = E ) )' % (ph, NWN_, NWN_))], 'simpld',
           '( %s -> P : ( 0 ... %s ) --> ( 2nd ` ( 1st ` T ) ) )' % (ph, NWN_))
    pe = s([s([u], 'simpld', '( %s -> ( P : ( 0 ... %s ) --> ( 2nd ` ( 1st ` T ) ) /\\ ( P ` %s ) = E ) )' % (ph, NWN_, NWN_))], 'simprd',
           '( %s -> ( P ` %s ) = E )' % (ph, NWN_))
    peq = s([u], 'simprd', '( %s -> %s )' % (ph, PNV_EQ))
    gW = s([nn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, WN))
    ex = {PHM: mk['phm'], 'K e. %s' % DOMT: mk['k']['K']['kd'], STKD('D'): c[STKD('D')],
          WRD(WN, GX('K')): togk(w, ph, mk, WN, 'K', gW), '4 e. %s' % GX('K'): letgk(w, ph, mk, '4', 'K', closed(w, ph, 'gamma4', "4 e. Gamma'")),
          'P : ( 0 ... %s ) --> ( 2nd ` ( 1st ` T ) )' % NWN_: pf, PNV_EQ: peq, '%s C_ %s' % (S, S): closed(w, ph, 'ssid', '%s C_ %s' % (S, S))}
    t, cc = inst(w, ph, 'tm2fpnw', {'I': 'P', 'W': WN, 'Y': '4', 'N': S, 'K': 'K', 'D': 'D'}, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    DPOST = UP('D', 'K', '( %s ++ ( <" 4 "> ++ ( D ` K ) ) )' % WN)
    assert D1 == CLN('( P ` %s )' % NWN_, S, DPOST), D1
    a = s([pe], 'fveq2d', '( %s -> ( inl ` ( P ` %s ) ) = ( inl ` E ) )' % (ph, NWN_))
    b = s([a], 'sneqd', '( %s -> { ( inl ` ( P ` %s ) ) } = { ( inl ` E ) } )' % (ph, NWN_))
    d = s([b], 'xpeq1d', '( %s -> %s = %s )' % (ph, D1, CLN('E', S, DPOST)))
    t, C, D, n = hrrw(w, ph, t, C1, D1, n1, deq=d)
    w.qed([t, w.inst('biid')], 'mpbi', STMTS12[lab])
    return w.run()


def tmipnvb():
    lab = 'tmipnvb'
    T = TREE_PNVB
    ph = cj(T)
    w = W(lab, 'Lean\'s ` pushNum_le_B ` at a number ` N < 2 ^ B ` (~ tmipnv ).')
    s = w.s
    c = Ctx(w, ph, T)
    nn, bn = c['N e. NN0'], c['B e. NN0']
    t, cc = inst(w, ph, 'tmipnv', {}, Bld(w, ph, c, {}))
    C1, D1, n1 = triple_parts(cc)
    cl = Closure(w, ph, {'N': ('NN0', nn), 'B': ('NN0', bn)})
    LW = '( # ` %s )' % WN
    le0 = s([nn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` N ) ) )' % (ph, LW))
    lp = s([nn, bn, c[LT2('N', 'B')], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` N ) ) <_ B )' % ph)
    en = s([s([nn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` N ) e. Word 2o )' % ph), w.inst('lencl')], 'syl',
           '( %s -> ( # ` ( encodeNat ` N ) ) e. NN0 )' % ph)
    cl.leaf('( # ` ( encodeNat ` N ) )', 'NN0', en)
    cl.leaf(LW, 'NN0', s([le0, en], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, LW)))
    TBB = '( TMB ` B )'
    cl.leaf(TBB, 'NN0', tmbn(w, ph, 'B', bn))
    lin_ = s([bn, closed(w, ph, '1nn0', '1 e. NN0'), s([num.le_lit(w, '1', '; 6 4')], 'a1i', '( %s -> 1 <_ ; 6 4 )' % ph), w.inst('tmblin')],
             'syl3anc', '( %s -> ( 1 x. ( B + 2 ) ) <_ %s )' % (ph, TBB))
    le = linarith(w, ph, [le0, lp, lin_, cl.ge0('B')], '%s <_ %s' % (n1, TBB), closure=cl)
    phm = s([c[cj(T_PHM7)]], 'simpld', '( %s -> %s )' % (ph, PHM))
    st = hrle(w, ph, phm, t, C1, D1, n1, TBB, cl.mem(TBB, 'NN0'), le)
    w.qed([st, w.inst('biid')], 'mpbi', STMTS12[lab])
    return w.run()


def tmiprdbl():
    lab = 'tmiprdbl'
    T0 = TREE_PBL
    ph0 = cj(T0)
    w = W(lab, 'Lean\'s ` predNum_le_B\' ` on a bit length with ` bl_pred ` : ` predNum ` turns ` bl F ` into ` Nat.log 2 F ` '
               '(~ tmiprdbs for ` F =/= 0 ` , ~ tmiprds on the empty word for ` F = 0 ` ).')
    s = w.s
    outs = []
    for zero in (True, False):
        cnd = 'F = 0' if zero else '-. F = 0'
        T = (T0, cnd)
        pc = cj(T)
        c = Ctx(w, pc, T)
        mk = machine(w, pc, c, ['K', 'J'])
        fn, nn = c['F e. NN0'], c['N e. NN0']
        xg, dd = c[WG('X')], c[STKD('D')]
        ex = {PHM: mk['phm']}
        if not zero:
            fnn = s([s([fn, s([c[cnd]], 'neqned', '( %s -> F =/= 0 )' % pc)], 'jca', '( %s -> ( F e. NN0 /\\ F =/= 0 ) )' % pc),
                     w.inst('elnnne0')], 'sylibr', '( %s -> F e. NN )' % pc)
            bl1 = s([fnn, w.inst('blnlog')], 'syl', '( %s -> ( 2 Nlog F ) = ( %s - 1 ) )' % (pc, BLF))
            blc = s([fn, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (pc, BLF))
            # bl F e. NN: bl F = Nlog F + 1
            nlc = s([closed(w, pc, '2nn0', '2 e. NN0'), fn, w.inst('nlogcl')], 'syl2anc', '( %s -> ( 2 Nlog F ) e. NN0 )' % pc)
            cl = Closure(w, pc, {})
            cl.leaf(BLF, 'NN0', blc)
            cl.leaf('( 2 Nlog F )', 'NN0', nlc)
            b1 = linarith(w, pc, [bl1, cl.ge0('( 2 Nlog F )')], '1 <_ %s' % BLF, closure=cl)
            bnn = s([s([blc, b1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (pc, BLF, BLF)), w.inst('elnnnn0c')], 'sylibr',
                    '( %s -> %s e. NN )' % (pc, BLF))
            ex['%s e. NN' % BLF] = bnn
            t, cc = inst(w, pc, 'tmiprdbs', {'F': BLF}, Bld(w, pc, c, ex))
            C1, D1, n1 = triple_parts(cc)
            e = s([bl1], 'eqcomd', '( %s -> ( %s - 1 ) = ( 2 Nlog F ) )' % (pc, BLF))
            rd, xd = w.rewrite(D1, {'( %s - 1 )' % BLF: ('( 2 Nlog F )', e)}, pc)
            t, C, D, n = hrrw(w, pc, t, C1, D1, n1, deq=rd)
            outs.append(t)
        else:
            f0 = c[cnd]
            b0 = s([s([f0], 'fveq2d', '( %s -> %s = ( bl ` 0 ) )' % (pc, BLF)), closed(w, pc, 'bl0', '( bl ` 0 ) = 0')], 'eqtrd',
                   '( %s -> %s = 0 )' % (pc, BLF))
            E0 = '( encodeNat ` 0 )'
            ev = s([closed(w, pc, '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. %s ) )' % (pc, E0))
            dk0 = s([c['( D ` K ) = %s' % EWg(BLF, 'X')], s([s([s([b0], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` 0 ) )' % (pc, BLF)), ev],
                                                                'eqtrd', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (pc, BLF, E0))],
                                                              'oveq1d', '( %s -> %s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (pc, EWg(BLF, 'X'), E0))],
                   'eqtrd', '( %s -> ( D ` K ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (pc, E0))
            ex['( D ` K ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) )' % E0] = dk0
            ex['%s e. Word 2o' % E0] = s([closed(w, pc, '0nn0', '0 e. NN0'), w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (pc, E0))
            t, cc = inst(w, pc, 'tmiprds', {'L': E0}, Bld(w, pc, c, ex))
            C1, D1, n1 = triple_parts(cc)
            # ( predBits ` ( encodeNat ` 0 ) ) = ( encodeNat ` 0 ) (both empty), then EW( Nlog F , X )
            e0 = closed(w, pc, 'encnat0', '( encodeNat ` 0 ) = (/)')
            pb = s([s([e0], 'fveq2d', '( %s -> ( predBits ` %s ) = ( predBits ` (/) ) )' % (pc, E0)), closed(w, pc, 'predbitsnil', '( predBits ` (/) ) = (/)'),
                    s([e0], 'eqcomd', '( %s -> (/) = %s )' % (pc, E0))], '3eqtrd', '( %s -> ( predBits ` %s ) = %s )' % (pc, E0, E0))
            nl0 = s([s([f0], 'oveq2d', '( %s -> ( 2 Nlog F ) = ( 2 Nlog 0 ) )' % pc), nlog0(w, pc)], 'eqtrd', '( %s -> ( 2 Nlog F ) = 0 )' % pc)
            eg = s([s([nl0], 'fveq2d', '( %s -> ( encNatGam ` ( 2 Nlog F ) ) = ( encNatGam ` 0 ) )' % pc), ev], 'eqtrd',
                   '( %s -> ( encNatGam ` ( 2 Nlog F ) ) = ( inclBool o. %s ) )' % (pc, E0))
            IB = '( inclBool o. ( predBits ` %s ) )' % E0
            ib = s([s([pb], 'coeq2d', '( %s -> %s = ( inclBool o. %s ) )' % (pc, IB, E0)), s([eg], 'eqcomd', '( %s -> ( inclBool o. %s ) = ( encNatGam ` ( 2 Nlog F ) ) )' % (pc, E0))],
                    'eqtrd', '( %s -> %s = ( encNatGam ` ( 2 Nlog F ) ) )' % (pc, IB))
            rd, xd = w.rewrite(D1, {IB: ('( encNatGam ` ( 2 Nlog F ) )', ib)}, pc)
            t, C, D, n = hrrw(w, pc, t, C1, D1, n1, deq=rd)
            # cost ( 2 x. ( # ` ( encodeNat ` 0 ) ) ) + 3 <_ TMB N
            cl = Closure(w, pc, {'N': ('NN0', nn)})
            LE0 = '( # ` %s )' % E0
            l0 = s([s([e0], 'fveq2d', '( %s -> %s = ( # ` (/) ) )' % (pc, LE0)), closed(w, pc, 'hash0', '( # ` (/) ) = 0')], 'eqtrd', '( %s -> %s = 0 )' % (pc, LE0))
            cl.leaf(LE0, 'NN0', s([l0, closed(w, pc, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (pc, LE0)))
            TN = '( TMB ` N )'
            cl.leaf(TN, 'NN0', tmbn(w, pc, 'N', nn))
            lin_ = s([nn, closed(w, pc, '2nn0', '2 e. NN0'), s([num.le_lit(w, '2', '; 6 4')], 'a1i', '( %s -> 2 <_ ; 6 4 )' % pc), w.inst('tmblin')],
                     'syl3anc', '( %s -> ( 2 x. ( N + 2 ) ) <_ %s )' % (pc, TN))
            le = linarith(w, pc, [l0, lin_, cl.ge0('N')], '%s <_ %s' % (n, TN), closure=cl)
            outs.append(hrle(w, pc, mk['phm'], t, C, D, n, TN, cl.mem(TN, 'NN0'), le))
            continue
        # F =/= 0: the cost is already ( TMB ` N )
    w.qed(outs, 'pm2.61dan', STMTS12[lab])
    return w.run()


def nlog0(w, ph):
    """( ph -> ( 2 Nlog 0 ) = 0 )"""
    s = w.s
    j = s([closed(w, ph, '2nn0', '2 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0')], 'jca', '( %s -> ( 2 e. NN0 /\\ 0 e. NN0 ) )' % ph)
    nle = s([s([s([], '0re', '0 e. RR'), s([], '1re', '1 e. RR')], 'ltnlei', '( 0 < 1 <-> -. 1 <_ 0 )'), s([], '0lt1', '0 < 1')], 'mpbi', '-. 1 <_ 0')
    nc = s([s([nle], 'intnan', '-. ( 2 <_ 2 /\\ 1 <_ 0 )')], 'a1i', '( %s -> -. ( 2 <_ 2 /\\ 1 <_ 0 ) )' % ph)
    jj = s([j, nc], 'jca', '( %s -> ( ( 2 e. NN0 /\\ 0 e. NN0 ) /\\ -. ( 2 <_ 2 /\\ 1 <_ 0 ) ) )' % ph)
    return s([jj, w.inst('nlogz')], 'syl', '( %s -> ( 2 Nlog 0 ) = 0 )' % ph)


import num

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
