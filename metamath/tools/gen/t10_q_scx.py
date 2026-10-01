"""T10: subCx at the machine (Lean ` subCx_le_B ` ) at ` x y z = 5 6 7 ` : ` sub x y z x ; canonNum x z ` .

    MM_DB=sorties/t10.mm python3 tools/gen/t10_q_scx.py tmiscxb
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t10_e_doa import ex_, lift_from
import num

SEL = sys.argv[1:]
LM = FRAGS['scx'].lmap()


def tmiscxb():
    lab = 'tmiscxb'
    T = numtree(TREE_SCX)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` subCx_le_B ` at the machine ( ` x y z = 5 6 7 ` ): ` sub x y z x ` (~ tmisub ) leaves the truncated '
               'difference of the bit words on ` x ` , ` canonNum x z ` (~ tmicans ) makes it canonical: ` a - b ` on ` x ` '
               '(here ` b <_ a ` ), ` b ` consumed, within ` B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    fn, gn, nn = c0['F e. NN0'], c0['G e. NN0'], c0['N e. NN0']
    eqs = {'5': (EWg('F', 'X'), ewg_(w, ph, 'F', fn, 'X', c0[WG('X')])), '6': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', c0[WG('Y')]))}
    B = Base(w, ph, T, N8, 'scx', eqs)
    c, mk = B.c, B.mk
    R = B.run()
    EF, EG = '( encodeNat ` F )', '( encodeNat ` G )'
    efw = s([fn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    egw = s([gn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    vf = s([s([fn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = ( inclBool o. %s ) )' % (ph, EF))], 'oveq1d',
           '( %s -> %s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (ph, EWg('F', 'X'), EF))
    vg = s([s([gn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` G ) = ( inclBool o. %s ) )' % (ph, EG))], 'oveq1d',
           '( %s -> %s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) ) )' % (ph, EWg('G', 'Y'), EG))
    d5 = s([B.S0.vals['5'][1], vf], 'eqtrd', '( %s -> ( D ` 5 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (ph, EF))
    d6 = s([B.S0.vals['6'][1], vg], 'eqtrd', '( %s -> ( D ` 6 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) ) )' % (ph, EG))
    SL = '( ( %s subTrunc %s ) ` (/) )' % (EF, EG)
    slw = s([efw, egw, closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('subtrunccl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, SL))
    ESL = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) )' % SL
    gsl = wgcat(w, ph, '( inclBool o. %s )' % SL, '( <" 4 "> ++ X )', s([slw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, SL)),
                wg4(w, ph, 'X', c0[WG('X')]))
    B.call(R, 'tmisub', {'K': '5', 'J': '6', 'I': '7', 'L': EF, "L'": EG, 'X': 'X', 'Y': 'Y', 'P': PL('P', 0), 'E': LM['Y2']},
           {'%s e. Word 2o' % EF: efw, "%s e. Word 2o" % EG: egw, '( D ` 5 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) )' % EF: d5,
            '( D ` 6 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) )' % EG: d6},
           [('5', ESL, B.g(ESL, gsl)), ('6', 'Y', c0[WG('Y')])])
    TN = '( toNat ` %s )' % SL
    tnn = s([slw, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TN))
    ET = EWg(TN, 'X')
    B.call(R, 'tmicans', {'K': '5', 'J': '7', 'L': SL, 'X': 'X', 'P': PL('P', 1), 'E': 'E'},
           {'%s e. Word 2o' % SL: slw}, [('5', ET, B.g(ET, ewg_(w, ph, TN, tnn, 'X', c0[WG('X')])))])
    cur, out = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # toNat of the difference
    ts = s([efw, egw, closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('tonatsubtrunc')], 'syl3anc',
           '( %s -> %s = if ( ( toNat ` %s ) < ( ( toNat ` %s ) + ( bToNat ` (/) ) ) , 0 , ( ( toNat ` %s ) - ( ( toNat ` %s ) + ( bToNat ` (/) ) ) ) ) )'
           % (ph, TN, EF, EG, EF, EG))
    tf = s([fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, EF))
    tg = s([gn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ph, EG))
    b0 = s([s([], 'bwbn0', '( bToNat ` (/) ) = 0')], 'a1i', '( %s -> ( bToNat ` (/) ) = 0 )' % ph)
    r1, x1 = w.rewrite('if ( ( toNat ` %s ) < ( ( toNat ` %s ) + ( bToNat ` (/) ) ) , 0 , ( ( toNat ` %s ) - ( ( toNat ` %s ) + ( bToNat ` (/) ) ) ) )'
                       % (EF, EG, EF, EG), {'( toNat ` %s )' % EF: ('F', tf), '( toNat ` %s )' % EG: ('G', tg), '( bToNat ` (/) )': ('0', b0)}, ph)
    cl = Closure(w, ph, {'F': ('NN0', fn), 'G': ('NN0', gn), 'N': ('NN0', nn)})
    g0 = s([s([cl.mem('G', 'CC'), w.inst('addrid')], 'syl', '( %s -> ( G + 0 ) = G )' % ph)], 'id', '') if False else \
        s([cl.mem('G', 'CC'), w.inst('addrid')], 'syl', '( %s -> ( G + 0 ) = G )' % ph)
    r2, x2 = w.rewrite(x1, {'( G + 0 )': ('G', g0)}, ph)
    nlt = s([cl.mem('G', 'RR'), cl.mem('F', 'RR'), c['G <_ F']], 'lenltd' if False else 'lenltd', '') if False else None
    nlt = s([c['G <_ F'], s([cl.mem('G', 'RR'), cl.mem('F', 'RR')], 'lenltd', '( %s -> ( G <_ F <-> -. F < G ) )' % ph)], 'mpbid', '( %s -> -. F < G )' % ph)
    i2 = s([nlt], 'iffalsed', '( %s -> %s = ( F - G ) )' % (ph, x2))
    tv = s([s([s([ts, r1], 'eqtrd', '( %s -> %s = %s )' % (ph, TN, x1)), r2], 'eqtrd', '( %s -> %s = %s )' % (ph, TN, x2)), i2], 'eqtrd',
           '( %s -> %s = ( F - G ) )' % (ph, TN))
    Dc = triple_D(D)
    rf, xf = w.rewrite(Dc, {TN: ('( F - G )', tv)}, ph)
    DF_ = UPS('D', ('5', EWg('( F - G )', 'X')), ('6', 'Y'))
    assert xf == DF_, (xf, DF_)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, rf, Dc, xf))
    # the bound
    LF, LG, LS = '( # ` %s )' % EF, '( # ` %s )' % EG, '( # ` %s )' % SL
    MX = 'if ( %s <_ %s , %s , %s )' % (LF, LG, LG, LF)
    lf = s([fn, nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, LF))
    lg = s([gn, nn, c['G < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, LG))
    for x_, w_ in ((LF, efw), (LG, egw), (LS, slw)):
        cl.leaf(x_, 'NN0', s([w_, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, x_)))
    mxn = s([s([s([egw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LG)), s([efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LF))],
               'ifcld', '( %s -> %s e. NN0 )' % (ph, MX))], 'id', '') if False else \
        s([s([egw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LG)), s([efw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LF))],
          'ifcld', '( %s -> %s e. NN0 )' % (ph, MX))
    cl.leaf(MX, 'NN0', mxn)
    mle = s([s([s([cl.mem(LF, 'RR'), cl.mem(LG, 'RR'), cl.mem('N', 'RR')], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ N e. RR ) )' % (ph, LF, LG)),
                w.inst('maxle')], 'syl', '( %s -> ( %s <_ N <-> ( %s <_ N /\\ %s <_ N ) ) )' % (ph, MX, LF, LG)),
             s([lf, lg], 'jca', '( %s -> ( %s <_ N /\\ %s <_ N ) )' % (ph, LF, LG))], 'mpbird', '( %s -> %s <_ N )' % (ph, MX))
    sle = s([efw, egw, closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('subtrunclen')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, LS, MX))
    TB = '( TMB ` N )'
    cl.leaf(TB, 'NN0', s([s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TB)))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([nn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc', '( %s -> ( 4 x. ( ( N + 2 ) ^ 2 ) ) <_ %s )' % (ph, TB))
    q2 = nlinarith(w, ph, [qd, cl.ge0('N')], '( ( 5 x. N ) + ; 1 0 ) <_ %s' % TB, closure=cl, atoms=['N', TB])
    le = linarith(w, ph, [mle, sle, q2], '%s <_ %s' % (n, TB), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, TB, cl.mem(TB, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
