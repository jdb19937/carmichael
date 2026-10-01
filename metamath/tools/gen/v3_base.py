"""Sortie v3: the base case and the induction of the smooth Euler-product bound.

smsum0  ( ( (/) C_ Prime /\\ W e. NN ) ->
            sum_ j e. SM( (/) , W ) ( 1 / j ) <_ prod_ p e. (/) ( 1 / ( 1 - ( 1 / p ) ) ) )
smsum   ( ( Q e. Fin /\\ Q C_ Prime /\\ W e. NN ) ->
            sum_ j e. SM( Q , W ) ( 1 / j ) <_ prod_ p e. Q ( 1 / ( 1 - ( 1 / p ) ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst, SMS
from cl import lift

FACT = '( 1 / ( 1 - ( 1 / p ) ) )'
PFV = '{ r e. Prime | r || v }'


def SUMS(E):
    return 'sum_ j e. %s ( 1 / j )' % SMS(E, 'W')


def PRODS(E):
    return 'prod_ p e. %s %s' % (E, FACT)


def PROP(E):
    return '( ( %s C_ Prime /\\ W e. NN ) -> %s <_ %s )' % (E, SUMS(E), PRODS(E))


def subst(w, E, name):
    """the findcard2s substitution lemma ( x = E -> ( ph <-> ph[E] ) )"""
    s1 = w.s([], 'sseq1', '( x = %s -> ( x C_ Prime <-> %s C_ Prime ) )' % (E, E))
    s2 = w.s([s1], 'anbi1d',
             '( x = %s -> ( ( x C_ Prime /\\ W e. NN ) <-> ( %s C_ Prime /\\ W e. NN ) ) )' % (E, E))
    s3 = w.s([], 'sseq2', '( x = %s -> ( %s C_ x <-> %s C_ %s ) )' % (E, PFV, PFV, E))
    s4 = w.s([s3], 'rabbidv', '( x = %s -> %s = %s )' % (E, SMS('x', 'W'), SMS(E, 'W')))
    s5 = w.s([s4], 'sumeq1d', '( x = %s -> %s = %s )' % (E, SUMS('x'), SUMS(E)))
    s6 = w.s([], 'prodeq1', '( x = %s -> %s = %s )' % (E, PRODS('x'), PRODS(E)))
    s7 = w.s([s5, s6], 'breq12d',
             '( x = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (E, SUMS('x'), PRODS('x'), SUMS(E), PRODS(E)))
    return w.s([s2, s7], 'imbi12d', '( x = %s -> ( %s <-> %s ) )' % (E, PROP('x'), PROP(E)))


def smsum0():
    w = WS('smsum0', 'The base case of the smooth Euler-product bound: only 1 is smooth for '
                     'the empty set of primes.')
    A = '( (/) C_ Prime /\\ W e. NN )'
    st = mkst(w, A)
    wnn = st([], 'simpr', 'W e. NN')
    AV = '( %s /\\ v e. ( 1 ... W ) )' % A
    sv = mkst(w, AV)
    vnn = sv([sv([], 'simpr', 'v e. ( 1 ... W )'), w.inst('elfznn')], 'syl', 'v e. NN')
    # forward: PF( v ) C_ (/) -> v = 1
    AF = '( %s /\\ %s C_ (/) )' % (AV, PFV)
    sf = mkst(w, AF)
    pf0 = sf([sf([], 'simpr', '%s C_ (/)' % PFV), w.inst('ss0')], 'syl', '%s = (/)' % PFV)
    nodv = sf([sf([w.s([], 'rabeq0', '( %s = (/) <-> A. r e. Prime -. r || v )' % PFV)], 'a1i',
                  '( %s = (/) <-> A. r e. Prime -. r || v )' % PFV), pf0], 'mpbid',
              'A. r e. Prime -. r || v')
    nex = sf([sf([w.s([], 'ralnex',
                      '( A. r e. Prime -. r || v <-> -. E. r e. Prime r || v )')], 'a1i',
                 '( A. r e. Prime -. r || v <-> -. E. r e. Prime r || v )'), nodv], 'mpbid',
             '-. E. r e. Prime r || v')
    AG = '( %s /\\ 1 < v )' % AF
    sg = mkst(w, AG)
    vuz = sg([sg([lift(w, vnn, AG), sg([], 'simpr', '1 < v')], 'jca', '( v e. NN /\\ 1 < v )'),
              sg([w.s([], 'eluz2b2', '( v e. ( ZZ>= ` 2 ) <-> ( v e. NN /\\ 1 < v ) )')], 'a1i',
                 '( v e. ( ZZ>= ` 2 ) <-> ( v e. NN /\\ 1 < v ) )')], 'mpbird',
             'v e. ( ZZ>= ` 2 )')
    ex = sg([vuz, w.inst('exprmfct')], 'syl', 'E. p e. Prime p || v')
    cbv = w.s([w.s([], 'breq1', '( p = r -> ( p || v <-> r || v ) )')], 'cbvrexvw',
              '( E. p e. Prime p || v <-> E. r e. Prime r || v )')
    exr = sg([sg([cbv], 'a1i', '( E. p e. Prime p || v <-> E. r e. Prime r || v )'), ex],
             'mpbid', 'E. r e. Prime r || v')
    n1lt = sf([exr, lift(w, nex, AG)], 'pm2.65da', '-. 1 < v')
    veq1 = sf([sf([sf([lift(w, vnn, AF), w.inst('nngt1ne1')], 'syl', '( 1 < v <-> v =/= 1 )'),
                   n1lt], 'mtbid', '-. v =/= 1'), w.inst('nne')], 'sylib', 'v = 1')
    fwd = sv([veq1], 'ex', '( %s C_ (/) -> v = 1 )' % PFV)
    # backward: v = 1 -> PF( v ) C_ (/)
    AB = '( %s /\\ v = 1 )' % AV
    sb = mkst(w, AB)
    pfeq = sb([sb([sb([], 'simpr', 'v = 1')], 'breq2d', '( r || v <-> r || 1 )')], 'rabbidv',
              '%s = { r e. Prime | r || 1 }' % PFV)
    ral1 = w.s([w.s([], 'nprmdvds1', '( r e. Prime -> -. r || 1 )')], 'rgen',
               'A. r e. Prime -. r || 1')
    r0 = w.s([w.s([], 'rabeq0',
                  '( { r e. Prime | r || 1 } = (/) <-> A. r e. Prime -. r || 1 )'), ral1],
             'mpbir', '{ r e. Prime | r || 1 } = (/)')
    pf0b = sb([pfeq, sb([r0], 'a1i', '{ r e. Prime | r || 1 } = (/)')], 'eqtrd',
              '%s = (/)' % PFV)
    ss0b = sb([pf0b, sb([w.s([], 'ssid', '(/) C_ (/)')], 'a1i', '(/) C_ (/)')], 'eqsstrd',
              '%s C_ (/)' % PFV)
    bwd = sv([ss0b], 'ex', '( v = 1 -> %s C_ (/) )' % PFV)
    bic = sv([fwd, bwd], 'impbid', '( %s C_ (/) <-> v = 1 )' % PFV)
    rab1 = st([bic], 'rabbidva', '%s = { v e. ( 1 ... W ) | v = 1 }' % SMS('(/)', 'W'))
    onefz = st([st([st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), wnn,
                    st([wnn, w.inst('nnge1')], 'syl', '1 <_ W')], '3jca',
                   '( 1 e. NN /\\ W e. NN /\\ 1 <_ W )'),
                st([w.s([], 'elfz1b',
                        '( 1 e. ( 1 ... W ) <-> ( 1 e. NN /\\ W e. NN /\\ 1 <_ W ) )')], 'a1i',
                   '( 1 e. ( 1 ... W ) <-> ( 1 e. NN /\\ W e. NN /\\ 1 <_ W ) )')], 'mpbird',
               '1 e. ( 1 ... W )')
    rsn = st([onefz, w.inst('rabsn')], 'syl', '{ v e. ( 1 ... W ) | v = 1 } = { 1 }')
    seteq = st([rab1, rsn], 'eqtrd', '%s = { 1 }' % SMS('(/)', 'W'))
    onecn = st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')
    d11 = st([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')
    d11c = st([d11, onecn], 'eqeltrd', '( 1 / 1 ) e. CC')
    sm1 = st([st([onefz, d11c], 'jca', '( 1 e. ( 1 ... W ) /\\ ( 1 / 1 ) e. CC )'),
              st([w.s([w.s([], 'oveq2', '( j = 1 -> ( 1 / j ) = ( 1 / 1 ) )')], 'sumsn',
                      '( ( 1 e. ( 1 ... W ) /\\ ( 1 / 1 ) e. CC ) -> '
                      'sum_ j e. { 1 } ( 1 / j ) = ( 1 / 1 ) )')], 'a1i',
                 '( ( 1 e. ( 1 ... W ) /\\ ( 1 / 1 ) e. CC ) -> '
                 'sum_ j e. { 1 } ( 1 / j ) = ( 1 / 1 ) )')], 'mpd',
             'sum_ j e. { 1 } ( 1 / j ) = ( 1 / 1 )')
    sm2 = st([sm1, d11], 'eqtrd', 'sum_ j e. { 1 } ( 1 / j ) = 1')
    sval = st([st([seteq], 'sumeq1d', '%s = sum_ j e. { 1 } ( 1 / j )' % SUMS('(/)')), sm2],
              'eqtrd', '%s = 1' % SUMS('(/)'))
    pval = st([w.s([], 'prod0', '%s = 1' % PRODS('(/)'))], 'a1i', '%s = 1' % PRODS('(/)'))
    le11 = st([st([], '1red', '1 e. RR')], 'leidd', '1 <_ 1')
    one1 = st([pval], 'eqcomd', '1 = %s' % PRODS('(/)'))
    rhs = st([le11, one1], 'breqtrd', '1 <_ %s' % PRODS('(/)'))
    w.qed([sval, rhs], 'eqbrtrd', '( %s -> %s <_ %s )' % (A, SUMS('(/)'), PRODS('(/)')))
    return w





YZ = '( y u. { z } )'


def smsum():
    w = WS('smsum', 'The Euler-product bound for a harmonic sum restricted to the integers '
                    'whose prime divisors lie in a finite set of primes.')
    # the four substitution lemmas of findcard2s
    h1 = subst(w, '(/)', 'h1')
    h2 = subst(w, 'y', 'h2')
    h3 = subst(w, YZ, 'h3')
    h4 = subst(w, 'Q', 'h4')
    base = w.s([], 'smsum0', PROP('(/)'))
    # the inductive step
    CH = PROP('y')
    AS = '( ( ( y e. Fin /\\ -. z e. y ) /\\ %s ) /\\ ( %s C_ Prime /\\ W e. NN ) )' % (CH, YZ)
    st = mkst(w, AS)
    yfin = st([], 'simplll', 'y e. Fin')
    nzy = st([], 'simpllr', '-. z e. y')
    ihyp = st([], 'simplr', CH)
    unss = st([], 'simprl', '%s C_ Prime' % YZ)
    wnn = st([], 'simprr', 'W e. NN')
    ysub = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    yprm = st([ysub, unss], 'sstrd', 'y C_ Prime')
    zsn = st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')
    zun = st([st([w.s([], 'ssun2', '{ z } C_ %s' % YZ)], 'a1i', '{ z } C_ %s' % YZ), zsn],
             'sseldd', 'z e. %s' % YZ)
    zprm = st([unss, zun], 'sseldd', 'z e. Prime')
    ihconc = st([ihyp, st([yprm, wnn], 'jca', '( y C_ Prime /\\ W e. NN )')], 'mpd',
                '%s <_ %s' % (SUMS('y'), PRODS('y')))
    stepa = st([st([st([zprm, wnn], 'jca', '( z e. Prime /\\ W e. NN )'),
                    st([yfin, yprm], 'jca', '( y e. Fin /\\ y C_ Prime )')], 'jca',
                   '( ( z e. Prime /\\ W e. NN ) /\\ ( y e. Fin /\\ y C_ Prime ) )'), nzy],
               'jca',
               '( ( ( z e. Prime /\\ W e. NN ) /\\ ( y e. Fin /\\ y C_ Prime ) ) /\\ -. z e. y )')
    stepi = st([stepa, w.inst('smsumstep')], 'syl',
               '( %s <_ %s -> %s <_ %s )' % (SUMS('y'), PRODS('y'), SUMS(YZ), PRODS(YZ)))
    concl = st([stepi, ihconc], 'mpd', '%s <_ %s' % (SUMS(YZ), PRODS(YZ)))
    ex1 = w.s([concl], 'ex',
              '( ( ( y e. Fin /\\ -. z e. y ) /\\ %s ) -> %s )' % (CH, PROP(YZ)))
    h6 = w.s([ex1], 'ex',
             '( ( y e. Fin /\\ -. z e. y ) -> ( %s -> %s ) )' % (CH, PROP(YZ)))
    fin = w.s([h1, h2, h3, h4, base, h6], 'findcard2s',
              '( Q e. Fin -> %s )' % PROP('Q'))
    w.qed([fin], '3impib',
          '( ( Q e. Fin /\\ Q C_ Prime /\\ W e. NN ) -> %s <_ %s )' % (SUMS('Q'), PRODS('Q')))
    return w


ALL = {'smsum0': smsum0, 'smsum': smsum}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
