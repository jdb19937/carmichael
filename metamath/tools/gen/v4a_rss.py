"""Sortie v4a: the base case and the induction of the radical-fibre Euler bound."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import RS, DEN, mkst
from cl import lift

YZ = '( y u. { z } )'
PFV = '{ r e. Prime | r || v }'


def FACT(P):
    return '( ( 2 / %s ) / ( 1 - ( 2 / %s ) ) )' % (P, P)


def SUMS(E):
    return 'sum_ j e. %s %s' % (RS(E, 'C'), DEN('j'))


def PRODQ(E):
    return 'prod_ n e. %s %s' % (E, FACT('n'))


def PROP(E):
    return ('( ( %s C_ Prime /\\ A. e e. %s 3 <_ e /\\ C e. NN ) -> %s <_ %s )'
            % (E, E, SUMS(E), PRODQ(E)))


def subst(w, E):
    a1 = w.s([], 'sseq1', '( x = %s -> ( x C_ Prime <-> %s C_ Prime ) )' % (E, E))
    a2 = w.s([], 'raleq', '( x = %s -> ( A. e e. x 3 <_ e <-> A. e e. %s 3 <_ e ) )' % (E, E))
    a3 = w.s([a1, a2], '3anbi12d',
             '( x = %s -> ( ( x C_ Prime /\\ A. e e. x 3 <_ e /\\ C e. NN ) <-> '
             '( %s C_ Prime /\\ A. e e. %s 3 <_ e /\\ C e. NN ) ) )' % (E, E, E))
    b1 = w.s([], 'eqeq2', '( x = %s -> ( %s = x <-> %s = %s ) )' % (E, PFV, PFV, E))
    b2 = w.s([b1], 'rabbidv', '( x = %s -> %s = %s )' % (E, RS('x', 'C'), RS(E, 'C')))
    b3 = w.s([b2], 'sumeq1d', '( x = %s -> %s = %s )' % (E, SUMS('x'), SUMS(E)))
    c1 = w.s([], 'prodeq1', '( x = %s -> %s = %s )' % (E, PRODQ('x'), PRODQ(E)))
    d = w.s([b3, c1], 'breq12d',
            '( x = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (E, SUMS('x'), PRODQ('x'), SUMS(E), PRODQ(E)))
    return w.s([a3, d], 'imbi12d', '( x = %s -> ( %s <-> %s ) )' % (E, PROP('x'), PROP(E)))


A0 = '( (/) C_ Prime /\\ A. e e. (/) 3 <_ e /\\ C e. NN )'


def rs0():
    w = WS('rs0', 'The base case of the radical-fibre Euler-product bound: only 1 has an '
                  'empty set of prime divisors.')
    st = mkst(w, A0)
    cnn = st([], 'simp3', 'C e. NN')
    AV = '( %s /\\ v e. ( 1 ... C ) )' % A0
    sv = mkst(w, AV)
    vnn = sv([sv([], 'simpr', 'v e. ( 1 ... C )'), w.inst('elfznn')], 'syl', 'v e. NN')
    AF = '( %s /\\ %s = (/) )' % (AV, PFV)
    sf = mkst(w, AF)
    pf0 = sf([], 'simpr', '%s = (/)' % PFV)
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
    fwd = sv([veq1], 'ex', '( %s = (/) -> v = 1 )' % PFV)
    AB = '( %s /\\ v = 1 )' % AV
    sb = mkst(w, AB)
    pfeq = sb([sb([sb([], 'simpr', 'v = 1')], 'breq2d', '( r || v <-> r || 1 )')], 'rabbidv',
              '%s = { r e. Prime | r || 1 }' % PFV)
    ral1 = w.s([w.s([], 'nprmdvds1', '( r e. Prime -> -. r || 1 )')], 'rgen',
               'A. r e. Prime -. r || 1')
    r0 = w.s([w.s([], 'rabeq0',
                  '( { r e. Prime | r || 1 } = (/) <-> A. r e. Prime -. r || 1 )'), ral1],
             'mpbir', '{ r e. Prime | r || 1 } = (/)')
    pf0b = sb([pfeq, sb([r0], 'a1i', '{ r e. Prime | r || 1 } = (/)')], 'eqtrd', '%s = (/)' % PFV)
    bwd = sv([pf0b], 'ex', '( v = 1 -> %s = (/) )' % PFV)
    bic = sv([fwd, bwd], 'impbid', '( %s = (/) <-> v = 1 )' % PFV)
    rab1 = st([bic], 'rabbidva', '%s = { v e. ( 1 ... C ) | v = 1 }' % RS('(/)', 'C'))
    onefz = st([st([st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), cnn,
                    st([cnn, w.inst('nnge1')], 'syl', '1 <_ C')], '3jca',
                   '( 1 e. NN /\\ C e. NN /\\ 1 <_ C )'),
                st([w.s([], 'elfz1b',
                        '( 1 e. ( 1 ... C ) <-> ( 1 e. NN /\\ C e. NN /\\ 1 <_ C ) )')], 'a1i',
                   '( 1 e. ( 1 ... C ) <-> ( 1 e. NN /\\ C e. NN /\\ 1 <_ C ) )')], 'mpbird',
               '1 e. ( 1 ... C )')
    rsn = st([onefz, w.inst('rabsn')], 'syl', '{ v e. ( 1 ... C ) | v = 1 } = { 1 }')
    seteq = st([rab1, rsn], 'eqtrd', '%s = { 1 }' % RS('(/)', 'C'))
    # ( 0 sigma 1 ) = 1
    sg2 = st([st([st([w.s([], '2prm', '2 e. Prime')], 'a1i', '2 e. Prime'),
                  st([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), w.inst('0sgmppw')],
                 'syl2anc', '( 0 sigma ( 2 ^ 0 ) ) = ( 0 + 1 )')], 'id', 'x')
    w.lines.pop()
    sg2 = w.lines[-1].split(':')[0]
    e20 = st([st([], '2cnd', '2 e. CC'), w.inst('exp0')], 'syl', '( 2 ^ 0 ) = 1')
    sgone = st([st([st([e20], 'eqcomd', '1 = ( 2 ^ 0 )')], 'oveq2d',
                   '( 0 sigma 1 ) = ( 0 sigma ( 2 ^ 0 ) )'),
                st([sg2, st([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( 0 + 1 ) = 1')],
                   'eqtrd', '( 0 sigma ( 2 ^ 0 ) ) = 1')], 'eqtrd', '( 0 sigma 1 ) = 1')
    d11 = st([st([sgone], 'oveq1d', '%s = ( 1 / 1 )' % DEN('1')),
              st([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')], 'eqtrd',
             '%s = 1' % DEN('1'))
    d11c = st([d11, st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'eqeltrd',
              '%s e. CC' % DEN('1'))
    sba = w.s([], 'oveq2', '( j = 1 -> ( 0 sigma j ) = ( 0 sigma 1 ) )')
    sbb = w.s([], 'id', '( j = 1 -> j = 1 )')
    sbc = w.s([sba, sbb], 'oveq12d', '( j = 1 -> %s = %s )' % (DEN('j'), DEN('1')))
    sm1 = st([st([onefz, d11c], 'jca', '( 1 e. ( 1 ... C ) /\\ %s e. CC )' % DEN('1')),
              st([w.s([sbc], 'sumsn',
                      '( ( 1 e. ( 1 ... C ) /\\ %s e. CC ) -> sum_ j e. { 1 } %s = %s )'
                      % (DEN('1'), DEN('j'), DEN('1')))], 'a1i',
                 '( ( 1 e. ( 1 ... C ) /\\ %s e. CC ) -> sum_ j e. { 1 } %s = %s )'
                 % (DEN('1'), DEN('j'), DEN('1')))], 'mpd',
             'sum_ j e. { 1 } %s = %s' % (DEN('j'), DEN('1')))
    sval = st([st([st([seteq], 'sumeq1d', '%s = sum_ j e. { 1 } %s' % (SUMS('(/)'), DEN('j'))),
                   sm1], 'eqtrd', '%s = %s' % (SUMS('(/)'), DEN('1'))), d11], 'eqtrd',
              '%s = 1' % SUMS('(/)'))
    pval = st([w.s([], 'prod0', '%s = 1' % PRODQ('(/)'))], 'a1i', '%s = 1' % PRODQ('(/)'))
    rhs = st([st([st([], '1red', '1 e. RR')], 'leidd', '1 <_ 1'),
              st([pval], 'eqcomd', '1 = %s' % PRODQ('(/)'))], 'breqtrd', '1 <_ %s' % PRODQ('(/)'))
    w.qed([sval, rhs], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, SUMS('(/)'), PRODQ('(/)')))
    return w


def rssum():
    w = WS('rssum', 'The Euler-product bound for the sum of the divisor count over the '
                    'integers whose set of prime divisors is a given finite set of primes '
                    'at least 3.')
    h1 = subst(w, '(/)')
    h2 = subst(w, 'y')
    h3 = subst(w, YZ)
    h4 = subst(w, 'Q')
    base = w.s([], 'rs0', PROP('(/)'))
    BS = ('( ( y e. Fin /\\ -. z e. y ) /\\ '
          '( %s C_ Prime /\\ A. e e. %s 3 <_ e /\\ C e. NN ) )' % (YZ, YZ))
    st = mkst(w, BS)
    yfin = st([], 'simpll', 'y e. Fin')
    nzy = st([], 'simplr', '-. z e. y')
    unss = st([], 'simpr1', '%s C_ Prime' % YZ)
    ralu = st([], 'simpr2', 'A. e e. %s 3 <_ e' % YZ)
    cnn = st([], 'simpr3', 'C e. NN')
    ysub = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    yprm = st([ysub, unss], 'sstrd', 'y C_ Prime')
    raly = st([st([ysub, w.inst('ssralv')], 'syl',
                  '( A. e e. %s 3 <_ e -> A. e e. y 3 <_ e )' % YZ), ralu], 'mpd',
              'A. e e. y 3 <_ e')
    zun = st([st([w.s([], 'ssun2', '{ z } C_ %s' % YZ)], 'a1i', '{ z } C_ %s' % YZ),
              st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')], 'sseldd',
             'z e. %s' % YZ)
    zprm = st([unss, zun], 'sseldd', 'z e. Prime')
    sbz = w.s([], 'breq2', '( e = z -> ( 3 <_ e <-> 3 <_ z ) )')
    z3 = st([sbz, ralu, zun], 'rspcdva', '3 <_ z')
    stepi = st([st([st([st([zprm, z3, cnn], '3jca', '( z e. Prime /\\ 3 <_ z /\\ C e. NN )'),
                       st([yfin, yprm, raly], '3jca',
                          '( y e. Fin /\\ y C_ Prime /\\ A. e e. y 3 <_ e )')], 'jca',
                       '( ( z e. Prime /\\ 3 <_ z /\\ C e. NN ) /\\ '
                       '( y e. Fin /\\ y C_ Prime /\\ A. e e. y 3 <_ e ) )'), nzy], 'jca',
                   '( ( ( z e. Prime /\\ 3 <_ z /\\ C e. NN ) /\\ '
                   '( y e. Fin /\\ y C_ Prime /\\ A. e e. y 3 <_ e ) ) /\\ -. z e. y )'),
                w.inst('rsstep')], 'syl',
               '( %s <_ %s -> %s <_ %s )' % (SUMS('y'), PRODQ('y'), SUMS(YZ), PRODQ(YZ)))
    AI2 = '( %s /\\ %s )' % (BS, PROP('y'))
    si = mkst(w, AI2)
    ihyp = si([], 'simpr', PROP('y'))
    ihc = si([ihyp, si([lift(w, yprm, AI2), lift(w, raly, AI2), lift(w, cnn, AI2)], '3jca',
                       '( y C_ Prime /\\ A. e e. y 3 <_ e /\\ C e. NN )')], 'mpd',
             '%s <_ %s' % (SUMS('y'), PRODQ('y')))
    fin1 = si([lift(w, stepi, AI2), ihc], 'mpd', '%s <_ %s' % (SUMS(YZ), PRODQ(YZ)))
    ex0 = w.s([fin1], 'exp31',
              '( ( y e. Fin /\\ -. z e. y ) -> '
              '( ( %s C_ Prime /\\ A. e e. %s 3 <_ e /\\ C e. NN ) -> ( %s -> %s <_ %s ) ) )'
              % (YZ, YZ, PROP('y'), SUMS(YZ), PRODQ(YZ)))
    h6 = w.s([ex0], 'com23',
             '( ( y e. Fin /\\ -. z e. y ) -> ( %s -> %s ) )' % (PROP('y'), PROP(YZ)))
    fin = w.s([h1, h2, h3, h4, base, h6], 'findcard2s', '( Q e. Fin -> %s )' % PROP('Q'))
    w.qed([fin], 'imp',
          '( ( Q e. Fin /\\ ( Q C_ Prime /\\ A. e e. Q 3 <_ e /\\ C e. NN ) ) -> %s <_ %s )'
          % (SUMS('Q'), PRODQ('Q')))
    return w


ALL = {'rs0': rs0, 'rssum': rssum}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
