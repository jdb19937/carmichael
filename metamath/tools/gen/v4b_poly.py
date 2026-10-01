"""Sortie v4b block 8b: the degree-four exponential bound.

poly4le  ( ( L e. RR /\\ ; ; ; ; ; ; 6 4 0 0 0 0 0 <_ L ) ->
             ( ( ; 1 0 x. L ) x. ( ( 1 + L ) ^ 2 ) ) <_ ( exp ` ( L / 5 ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import mkst
import num
from lin import linarith, nlinarith

C64 = num.nat_text(6400000)
C16 = num.nat_text(160000)
C40 = num.nat_text(40)
C10 = num.nat_text(10)
C20 = num.nat_text(20)
ANT = '( L e. RR /\\ %s <_ L )' % C64
E = '( L / %s )' % C20
LHS = '( ( %s x. L ) x. ( ( 1 + L ) ^ 2 ) )' % C10


def poly4le():
    w = W('poly4le', 'For L at least 6400000 the degree-four polynomial bound '
                     '10 L ( 1 + L ) ^ 2 <_ exp ( L / 5 ).')
    st = mkst(w, ANT)
    lre = st([], 'simpl', 'L e. RR')
    lge = st([], 'simpr', '%s <_ L' % C64)
    LV = {'L': lre}
    l1 = linarith(w, ANT, [lge], '1 <_ L', leaves=LV)
    l0 = linarith(w, ANT, [lge], '0 <_ L', leaves=LV)
    lrp = st([lre, linarith(w, ANT, [lge], '0 < L', leaves=LV)], 'elrpd', 'L e. RR+')
    n2 = st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    n3 = st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')
    n4 = st([w.s([], '4nn0', '4 e. NN0')], 'a1i', '4 e. NN0')
    l2re = st([lre, n2], 'reexpcld', '( L ^ 2 ) e. RR')
    l3re = st([lre, n3], 'reexpcld', '( L ^ 3 ) e. RR')
    l4re = st([lre, n4], 'reexpcld', '( L ^ 4 ) e. RR')
    l3ge = st([lre, n3, l0, w.inst('expge0')], 'syl3anc', '0 <_ ( L ^ 3 )')
    lcc = st([lre], 'recnd', 'L e. CC')
    # ---- ( 1 + L ) ^ 2 <_ 4 ( L ^ 2 ) ------------------------------------
    onepl = st([st([], '1red', '1 e. RR'), lre], 'readdcld', '( 1 + L ) e. RR')
    twol = st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), lre], 'remulcld',
              '( 2 x. L ) e. RR')
    sq1 = st([st([onepl, linarith(w, ANT, [l1], '0 <_ ( 1 + L )', leaves=LV)], 'jca',
                 '( ( 1 + L ) e. RR /\\ 0 <_ ( 1 + L ) )'),
              st([twol, linarith(w, ANT, [l1], '0 <_ ( 2 x. L )', leaves=LV)], 'jca',
                 '( ( 2 x. L ) e. RR /\\ 0 <_ ( 2 x. L ) )'), w.inst('le2sq')], 'syl2anc',
             '( ( 1 + L ) <_ ( 2 x. L ) <-> ( ( 1 + L ) ^ 2 ) <_ ( ( 2 x. L ) ^ 2 ) )')
    sq2a = st([sq1, linarith(w, ANT, [l1], '( 1 + L ) <_ ( 2 x. L )', leaves=LV)], 'mpbid',
              '( ( 1 + L ) ^ 2 ) <_ ( ( 2 x. L ) ^ 2 )')
    sqm = st([st([st([], '2cnd', '2 e. CC'), lcc], 'sqmuld',
                 '( ( 2 x. L ) ^ 2 ) = ( ( 2 ^ 2 ) x. ( L ^ 2 ) )'),
              st([st([w.s([], 'sq2', '( 2 ^ 2 ) = 4')], 'a1i', '( 2 ^ 2 ) = 4')], 'oveq1d',
                 '( ( 2 ^ 2 ) x. ( L ^ 2 ) ) = ( 4 x. ( L ^ 2 ) )')], 'eqtrd',
             '( ( 2 x. L ) ^ 2 ) = ( 4 x. ( L ^ 2 ) )')
    sq3 = st([sq2a, sqm], 'breqtrd', '( ( 1 + L ) ^ 2 ) <_ ( 4 x. ( L ^ 2 ) )')
    # ---- 10 L ( 1 + L ) ^ 2 <_ 40 ( L ^ 3 ) -------------------------------
    tenl = st([st([num.re_nat(w, 10)], 'a1i', '%s e. RR' % C10), lre], 'remulcld',
              '( %s x. L ) e. RR' % C10)
    sqre = st([onepl, n2], 'reexpcld', '( ( 1 + L ) ^ 2 ) e. RR')
    fourl = st([st([w.s([], '4re', '4 e. RR')], 'a1i', '4 e. RR'), l2re], 'remulcld',
               '( 4 x. ( L ^ 2 ) ) e. RR')
    mul1 = st([sqre, fourl, tenl, linarith(w, ANT, [l1], '0 <_ ( %s x. L )' % C10, leaves=LV), sq3],
              'lemul2ad', '%s <_ ( ( %s x. L ) x. ( 4 x. ( L ^ 2 ) ) )' % (LHS, C10))
    l3eq = st([lcc, n2], 'expp1d', '( L ^ ( 2 + 1 ) ) = ( ( L ^ 2 ) x. L )')
    e21 = st([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'a1i', '( 2 + 1 ) = 3')
    l3v = st([st([e21], 'oveq2d', '( L ^ ( 2 + 1 ) ) = ( L ^ 3 )'), l3eq], 'eqtr3d',
             '( L ^ 3 ) = ( ( L ^ 2 ) x. L )')
    lm = st([st([st([num.cc_nat(w, 10)], 'a1i', '%s e. CC' % C10), lcc,
                 st([w.s([], '4cn', '4 e. CC')], 'a1i', '4 e. CC'),
                 st([l2re], 'recnd', '( L ^ 2 ) e. CC')], 'mul4d',
                '( ( %s x. L ) x. ( 4 x. ( L ^ 2 ) ) ) = ( ( %s x. 4 ) x. ( L x. ( L ^ 2 ) ) )'
                % (C10, C10)),
             st([st([num.mul_nat(w, 10, 4)], 'a1i', '( %s x. 4 ) = %s' % (C10, C40)),
                 st([st([lcc, st([l2re], 'recnd', '( L ^ 2 ) e. CC')], 'mulcomd',
                        '( L x. ( L ^ 2 ) ) = ( ( L ^ 2 ) x. L )'), l3v], 'eqtr4d',
                    '( L x. ( L ^ 2 ) ) = ( L ^ 3 )')], 'oveq12d',
                '( ( %s x. 4 ) x. ( L x. ( L ^ 2 ) ) ) = ( %s x. ( L ^ 3 ) )' % (C10, C40))],
            'eqtrd',
            '( ( %s x. L ) x. ( 4 x. ( L ^ 2 ) ) ) = ( %s x. ( L ^ 3 ) )' % (C10, C40))
    step1 = st([mul1, lm], 'breqtrd', '%s <_ ( %s x. ( L ^ 3 ) )' % (LHS, C40))
    # ---- ( 20 ^ 4 ) = 160000 ---------------------------------------------
    c20 = st([num.cc_nat(w, 20)], 'a1i', '%s e. CC' % C20)
    pw = {1: st([c20], 'exp1d', '( %s ^ 1 ) = %s' % (C20, C20))}
    vals = {1: 20}
    for k in (1, 2, 3):
        nk = st([w.s([], '%dnn0' % k, '%d e. NN0' % k)], 'a1i', '%d e. NN0' % k)
        raw = st([c20, nk], 'expp1d',
                 '( %s ^ ( %d + 1 ) ) = ( ( %s ^ %d ) x. %s )' % (C20, k, C20, k, C20))
        pl = st([w.s([], '%dp1e%d' % (k, k + 1), '( %d + 1 ) = %d' % (k, k + 1))], 'a1i',
                '( %d + 1 ) = %d' % (k, k + 1))
        lhsk = st([st([pl], 'oveq2d',
                      '( %s ^ ( %d + 1 ) ) = ( %s ^ %d )' % (C20, k, C20, k + 1)), raw],
                  'eqtr3d',
                  '( %s ^ %d ) = ( ( %s ^ %d ) x. %s )' % (C20, k + 1, C20, k, C20))
        prod = st([st([pw[k]], 'oveq1d',
                      '( ( %s ^ %d ) x. %s ) = ( %s x. %s )'
                      % (C20, k, C20, num.nat_text(vals[k]), C20)),
                   st([num.mul_nat(w, vals[k], 20)], 'a1i',
                      '( %s x. %s ) = %s' % (num.nat_text(vals[k]), C20,
                                             num.nat_text(vals[k] * 20)))], 'eqtrd',
                  '( ( %s ^ %d ) x. %s ) = %s'
                  % (C20, k, C20, num.nat_text(vals[k] * 20)))
        pw[k + 1] = st([lhsk, prod], 'eqtrd',
                       '( %s ^ %d ) = %s' % (C20, k + 1, num.nat_text(vals[k] * 20)))
        vals[k + 1] = vals[k] * 20
    # ---- ( 40 x. ( L ^ 3 ) ) <_ ( E ^ 4 ) --------------------------------
    c20ne = st([num.fact(w, C20, 'ne0')], 'a1i', '%s =/= 0' % C20)
    edv = st([lcc, st([c20, c20ne], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (C20, C20)), n4,
              w.inst('expdiv')], 'syl3anc',
             '( %s ^ 4 ) = ( ( L ^ 4 ) / ( %s ^ 4 ) )' % (E, C20))
    edv2 = st([edv, st([pw[4]], 'oveq2d',
                       '( ( L ^ 4 ) / ( %s ^ 4 ) ) = ( ( L ^ 4 ) / %s )' % (C20, C16))],
              'eqtrd', '( %s ^ 4 ) = ( ( L ^ 4 ) / %s )' % (E, C16))
    c16re = st([num.re_nat(w, 160000)], 'a1i', '%s e. RR' % C16)
    c16pos = st([num.fact(w, C16, 'gt0')], 'a1i', '0 < %s' % C16)
    c40l3 = st([st([num.re_nat(w, 40)], 'a1i', '%s e. RR' % C40), l3re], 'remulcld',
               '( %s x. ( L ^ 3 ) ) e. RR' % C40)
    lmd = st([c40l3, l4re, st([c16re, c16pos], 'jca', '( %s e. RR /\\ 0 < %s )' % (C16, C16)),
              w.inst('lemuldiv')], 'syl3anc',
             '( ( ( %s x. ( L ^ 3 ) ) x. %s ) <_ ( L ^ 4 ) <-> ( %s x. ( L ^ 3 ) ) <_ ( ( L ^ 4 ) / %s ) )'
             % (C40, C16, C40, C16))
    m32 = st([st([st([num.cc_nat(w, 40)], 'a1i', '%s e. CC' % C40),
                  st([l3re], 'recnd', '( L ^ 3 ) e. CC'),
                  st([num.cc_nat(w, 160000)], 'a1i', '%s e. CC' % C16)], 'mul32d',
                 '( ( %s x. ( L ^ 3 ) ) x. %s ) = ( ( %s x. %s ) x. ( L ^ 3 ) )'
                 % (C40, C16, C40, C16)),
              st([st([num.mul_nat(w, 40, 160000)], 'a1i',
                     '( %s x. %s ) = %s' % (C40, C16, C64))], 'oveq1d',
                 '( ( %s x. %s ) x. ( L ^ 3 ) ) = ( %s x. ( L ^ 3 ) )' % (C40, C16, C64))],
             'eqtrd',
             '( ( %s x. ( L ^ 3 ) ) x. %s ) = ( %s x. ( L ^ 3 ) )' % (C40, C16, C64))
    n3b = st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')
    l4raw = st([lcc, n3b], 'expp1d', '( L ^ ( 3 + 1 ) ) = ( ( L ^ 3 ) x. L )')
    l4v = st([st([st([w.s([], '3p1e4', '( 3 + 1 ) = 4')], 'a1i', '( 3 + 1 ) = 4')], 'oveq2d',
                 '( L ^ ( 3 + 1 ) ) = ( L ^ 4 )'), l4raw], 'eqtr3d',
             '( L ^ 4 ) = ( ( L ^ 3 ) x. L )')
    nl = nlinarith(w, ANT, [lge, l3ge],
                   '( %s x. ( L ^ 3 ) ) <_ ( ( L ^ 3 ) x. L )' % C64,
                   leaves={'L': lre, '( L ^ 3 )': l3re}, atoms=['( L ^ 3 )'])
    prod0 = st([nl, l4v], 'breqtrrd', '( %s x. ( L ^ 3 ) ) <_ ( L ^ 4 )' % C64)
    prod1 = st([m32, prod0], 'eqbrtrd',
               '( ( %s x. ( L ^ 3 ) ) x. %s ) <_ ( L ^ 4 )' % (C40, C16))
    step2 = st([st([lmd, prod1], 'mpbid',
                   '( %s x. ( L ^ 3 ) ) <_ ( ( L ^ 4 ) / %s )' % (C40, C16)),
                st([edv2], 'eqcomd', '( ( L ^ 4 ) / %s ) = ( %s ^ 4 )' % (C16, E))],
               'breqtrd', '( %s x. ( L ^ 3 ) ) <_ ( %s ^ 4 )' % (C40, E))
    # ---- ( E ^ 4 ) <_ exp ( L / 5 ) --------------------------------------
    c20rp = st([num.rp_nat(w, 20)], 'a1i', '%s e. RR+' % C20)
    erp = st([lrp, c20rp], 'rpdivcld', '%s e. RR+' % E)
    ere = st([erp], 'rpred', '%s e. RR' % E)
    ege = st([erp, w.inst('rpge0')], 'syl', '0 <_ %s' % E)
    efre = st([ere], 'reefcld', '( exp ` %s ) e. RR' % E)
    eflt = st([erp, w.inst('efgt1p')], 'syl', '( 1 + %s ) < ( exp ` %s )' % (E, E))
    onee = st([st([], '1red', '1 e. RR'), ere], 'readdcld', '( 1 + %s ) e. RR' % E)
    efle = st([onee, efre, eflt], 'ltled', '( 1 + %s ) <_ ( exp ` %s )' % (E, E))
    eple = linarith(w, ANT, [ege], '%s <_ ( 1 + %s )' % (E, E),
                    leaves={E: ere, 'L': lre}, atoms=[E])
    eleexp = st([ere, onee, efre, eple, efle], 'letrd', '%s <_ ( exp ` %s )' % (E, E))
    pow4 = st([st([ere, efre, n4], '3jca',
                  '( %s e. RR /\\ ( exp ` %s ) e. RR /\\ 4 e. NN0 )' % (E, E)),
               st([ege, eleexp], 'jca', '( 0 <_ %s /\\ %s <_ ( exp ` %s ) )' % (E, E, E)),
               w.inst('leexp1a')], 'syl2anc',
              '( %s ^ 4 ) <_ ( ( exp ` %s ) ^ 4 )' % (E, E))
    n4z = st([w.s([], '4z', '4 e. ZZ')], 'a1i', '4 e. ZZ')
    ecc = st([ere], 'recnd', '%s e. CC' % E)
    efe = st([ecc, n4z, w.inst('efexp')], 'syl2anc',
             '( exp ` ( 4 x. %s ) ) = ( ( exp ` %s ) ^ 4 )' % (E, E))
    dva = st([st([st([w.s([], '4cn', '4 e. CC')], 'a1i', '4 e. CC'), lcc, c20, c20ne],
                 'divassd', '( ( 4 x. L ) / %s ) = ( 4 x. %s )' % (C20, E))], 'eqcomd',
             '( 4 x. %s ) = ( ( 4 x. L ) / %s )' % (E, C20))
    c45 = st([st([num.mul_nat(w, 4, 5)], 'a1i', '( 4 x. 5 ) = %s' % C20)], 'eqcomd',
             '%s = ( 4 x. 5 )' % C20)
    dvb = st([c45], 'oveq2d',
             '( ( 4 x. L ) / %s ) = ( ( 4 x. L ) / ( 4 x. 5 ) )' % C20)
    dc5 = st([lcc, st([st([w.s([], '5cn', '5 e. CC')], 'a1i', '5 e. CC'),
                       st([w.s([], '5ne0', '5 =/= 0')], 'a1i', '5 =/= 0')], 'jca',
                      '( 5 e. CC /\\ 5 =/= 0 )'),
              st([st([w.s([], '4cn', '4 e. CC')], 'a1i', '4 e. CC'),
                  st([w.s([], '4ne0', '4 =/= 0')], 'a1i', '4 =/= 0')], 'jca',
                 '( 4 e. CC /\\ 4 =/= 0 )'), w.inst('divcan5')], 'syl3anc',
             '( ( 4 x. L ) / ( 4 x. 5 ) ) = ( L / 5 )')
    ident = st([st([dva, dvb], 'eqtrd',
                   '( 4 x. %s ) = ( ( 4 x. L ) / ( 4 x. 5 ) )' % E), dc5], 'eqtrd',
               '( 4 x. %s ) = ( L / 5 )' % E)
    efeq = st([st([ident], 'fveq2d',
                  '( exp ` ( 4 x. %s ) ) = ( exp ` ( L / 5 ) )' % E), efe], 'eqtr3d',
              '( exp ` ( L / 5 ) ) = ( ( exp ` %s ) ^ 4 )' % E)
    step3 = st([pow4, st([efeq], 'eqcomd',
                         '( ( exp ` %s ) ^ 4 ) = ( exp ` ( L / 5 ) )' % E)], 'breqtrd',
               '( %s ^ 4 ) <_ ( exp ` ( L / 5 ) )' % E)
    # ---- the chain -------------------------------------------------------
    lhsre = st([tenl, sqre], 'remulcld', '%s e. RR' % LHS)
    e4re = st([ere, n4], 'reexpcld', '( %s ^ 4 ) e. RR' % E)
    efLre = st([st([lre, st([w.s([], '5re', '5 e. RR')], 'a1i', '5 e. RR'),
                    st([w.s([], '5ne0', '5 =/= 0')], 'a1i', '5 =/= 0')], 'redivcld',
                   '( L / 5 ) e. RR')], 'reefcld', '( exp ` ( L / 5 ) ) e. RR')
    ch1 = st([lhsre, c40l3, e4re, step1, step2], 'letrd', '%s <_ ( %s ^ 4 )' % (LHS, E))
    w.qed([lhsre, e4re, efLre, ch1, step3], 'letrd',
          '( %s -> %s <_ ( exp ` ( L / 5 ) ) )' % (ANT, LHS))
    return w


def main(names=None):
    fns = {'poly4le': poly4le}
    ok = True
    for nm in (names or ['poly4le']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
