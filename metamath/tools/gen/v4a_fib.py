"""Sortie v4a: the fibre bound and the lower bound for the Selberg bounding sum."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import CS, DEN, mkst, csel
from cl import lift
from v4a_tb import SH, SH2, SHP, SHV, SHV3, SHVM, SHVP, TBODY, TMR, TRAL, TB, shparts

PFQ = '{ q e. Prime | q || %s }'
PFR = '{ r e. Prime | r || %s }'
PFQL = PFQ % 'L'
RSL = '{ v e. ( 1 ... Z ) | %s = %s }' % (PFR % 'v', PFQL)
CSZ = CS('( 2 x. M )', 'Z')
GTL = '( ( V ` L ) x. prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) )' % (PFR % 'L')
FACT = '( ( 2 / %s ) / ( 1 - ( 2 / %s ) ) )'
AFIB = '( %s /\\ ( L e. NN /\\ L || P ) )' % TB


def cbvpf(w, J):
    """closed step: { r e. Prime | r || J } = { q e. Prime | q || J }"""
    b = w.s([], 'breq1', '( r = q -> ( r || %s <-> q || %s ) )' % (J, J))
    return w.s([b], 'cbvrabv', '%s = %s' % (PFR % J, PFQ % J))


def twinfib():
    w = WS('twinfib', 'The fibre of the inflated density sum over a divisor L of the sifting '
                      'product is at most the Selberg term at L.')
    st = mkst(w, AFIB)
    tmid = st([], 'simpl', '( %s /\\ %s /\\ %s )' % (SH, TMR, TRAL))
    sh = shparts(w, st, st([tmid], 'simp1d', SH))
    mnn = st([st([tmid], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    znn = st([st([tmid], 'simp2d', TMR)], 'simp2d', 'Z e. NN')
    lpair = st([], 'simpr', '( L e. NN /\\ L || P )')
    lnn = st([lpair], 'simpld', 'L e. NN')
    ldp = st([lpair], 'simprd', 'L || P')
    pnn = sh['pnn']
    pz = st([pnn], 'nnzd', 'P e. ZZ')
    lz = st([lnn], 'nnzd', 'L e. ZZ')
    # the prime divisors of L
    qfin = st([lnn, w.inst('pffinq')], 'syl', '%s e. Fin' % PFQL)
    qprm = st([w.s([], 'ssrab2', '%s C_ Prime' % PFQL)], 'a1i', '%s C_ Prime' % PFQL)
    elql = w.s([w.s([], 'breq1', '( q = e -> ( q || L <-> e || L ) )')], 'elrab',
               '( e e. %s <-> ( e e. Prime /\\ e || L ) )' % PFQL)
    AE = '( %s /\\ e e. %s )' % (AFIB, PFQL)
    se = mkst(w, AE)
    emem = se([se([elql], 'a1i',
                  '( e e. %s <-> ( e e. Prime /\\ e || L ) )' % PFQL),
               se([], 'simpr', 'e e. %s' % PFQL)], 'mpbid', '( e e. Prime /\\ e || L )')
    eprm = se([emem], 'simpld', 'e e. Prime')
    edl = se([emem], 'simprd', 'e || L')
    edp = se([se([se([se([se([eprm, w.inst('prmnn')], 'syl', 'e e. NN')], 'nnzd', 'e e. ZZ'),
                   lift(w, lz, AE), lift(w, pz, AE)], '3jca',
                  '( e e. ZZ /\\ L e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
               '( ( e || L /\\ L || P ) -> e || P )'),
              se([edl, lift(w, ldp, AE)], 'jca', '( e || L /\\ L || P )')], 'mpd', 'e || P')
    e3 = se([se([lift(w, tmid, AE), se([eprm, edp], 'jca', '( e e. Prime /\\ e || P )')], 'jca',
                '( ( %s /\\ %s /\\ %s ) /\\ ( e e. Prime /\\ e || P ) )' % (SH, TMR, TRAL)),
             w.inst('twinp3')], 'syl',
            '( 3 <_ e /\\ ( V ` e ) = ( 2 / e ) /\\ -. e || ( 2 x. M ) )')
    ral3 = st([se([e3], 'simp1d', '3 <_ e')], 'ralrimiva', 'A. e e. %s 3 <_ e' % PFQL)
    # rssum at Q := PF( L )
    rs = st([st([qfin, st([qprm, ral3, znn], '3jca',
                          '( %s C_ Prime /\\ A. e e. %s 3 <_ e /\\ Z e. NN )' % (PFQL, PFQL))],
                'jca',
                '( %s e. Fin /\\ ( %s C_ Prime /\\ A. e e. %s 3 <_ e /\\ Z e. NN ) )'
                % (PFQL, PFQL, PFQL)), w.inst('rssum')], 'syl',
            'sum_ j e. %s %s <_ prod_ n e. %s %s'
            % (RSL, DEN('j'), PFQL, FACT % ('n', 'n')))
    # the Euler product is the Selberg term
    AN = '( %s /\\ n e. %s )' % (AFIB, PFQL)
    sn = mkst(w, AN)
    elqn = w.s([w.s([], 'breq1', '( q = n -> ( q || L <-> n || L ) )')], 'elrab',
               '( n e. %s <-> ( n e. Prime /\\ n || L ) )' % PFQL)
    nmem = sn([sn([elqn], 'a1i', '( n e. %s <-> ( n e. Prime /\\ n || L ) )' % PFQL),
               sn([], 'simpr', 'n e. %s' % PFQL)], 'mpbid', '( n e. Prime /\\ n || L )')
    nprm = sn([nmem], 'simpld', 'n e. Prime')
    ndl = sn([nmem], 'simprd', 'n || L')
    ndp = sn([sn([sn([sn([sn([nprm, w.inst('prmnn')], 'syl', 'n e. NN')], 'nnzd', 'n e. ZZ'),
                   lift(w, lz, AN), lift(w, pz, AN)], '3jca',
                  '( n e. ZZ /\\ L e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
               '( ( n || L /\\ L || P ) -> n || P )'),
              sn([ndl, lift(w, ldp, AN)], 'jca', '( n || L /\\ L || P )')], 'mpd', 'n || P')
    nvd = sn([sn([sn([lift(w, tmid, AN), sn([nprm, ndp], 'jca',
                                            '( n e. Prime /\\ n || P )')], 'jca',
                     '( ( %s /\\ %s /\\ %s ) /\\ ( n e. Prime /\\ n || P ) )'
                     % (SH, TMR, TRAL)), w.inst('twinp3')], 'syl',
                 '( 3 <_ n /\\ ( V ` n ) = ( 2 / n ) /\\ -. n || ( 2 x. M ) )')], 'simp2d',
              '( V ` n ) = ( 2 / n )')
    bodyeq = sn([sn([nvd], 'oveq1d', '( ( V ` n ) / ( 1 - ( V ` n ) ) ) = '
                    '( ( 2 / n ) / ( 1 - ( V ` n ) ) )'),
                 sn([sn([nvd], 'oveq2d', '( 1 - ( V ` n ) ) = ( 1 - ( 2 / n ) )')], 'oveq2d',
                    '( ( 2 / n ) / ( 1 - ( V ` n ) ) ) = %s' % (FACT % ('n', 'n')))], 'eqtrd',
                '( ( V ` n ) / ( 1 - ( V ` n ) ) ) = %s' % (FACT % ('n', 'n')))
    prd1 = st([bodyeq], 'prodeq2dv',
              'prod_ n e. %s ( ( V ` n ) / ( 1 - ( V ` n ) ) ) = prod_ n e. %s %s'
              % (PFQL, PFQL, FACT % ('n', 'n')))
    cbn = w.s([w.s([w.s([], 'fveq2', '( n = p -> ( V ` n ) = ( V ` p ) )'),
                    w.s([w.s([], 'fveq2', '( n = p -> ( V ` n ) = ( V ` p ) )')], 'oveq2d',
                        '( n = p -> ( 1 - ( V ` n ) ) = ( 1 - ( V ` p ) ) )')], 'oveq12d',
                   '( n = p -> ( ( V ` n ) / ( 1 - ( V ` n ) ) ) = '
                   '( ( V ` p ) / ( 1 - ( V ` p ) ) ) )')], 'cbvprodv',
              'prod_ n e. %s ( ( V ` n ) / ( 1 - ( V ` n ) ) ) = '
              'prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) )' % (PFQL, PFQL))
    cbrq = cbvpf(w, 'L')
    prdset = st([st([cbrq], 'a1i', '%s = %s' % (PFR % 'L', PFQL)), w.inst('prodeq1')], 'syl',
                'prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) ) = '
                'prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) )' % (PFR % 'L', PFQL))
    gtf = st([st([sh['sh'], lpair], 'jca', '( %s /\\ ( L e. NN /\\ L || P ) )' % SH),
              w.inst('gtfprod')], 'syl',
             '%s = prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) )' % (GTL, PFR % 'L'))
    eulr = st([st([gtf, prdset], 'eqtrd',
                  '%s = prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) )' % (GTL, PFQL)),
               st([st([st([cbn], 'a1i',
                          'prod_ n e. %s ( ( V ` n ) / ( 1 - ( V ` n ) ) ) = '
                          'prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) )' % (PFQL, PFQL))],
                       'eqcomd',
                       'prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) ) = '
                       'prod_ n e. %s ( ( V ` n ) / ( 1 - ( V ` n ) ) )' % (PFQL, PFQL)),
                   prd1], 'eqtrd',
                  'prod_ p e. %s ( ( V ` p ) / ( 1 - ( V ` p ) ) ) = prod_ n e. %s %s'
                  % (PFQL, PFQL, FACT % ('n', 'n')))], 'eqtrd',
              '%s = prod_ n e. %s %s' % (GTL, PFQL, FACT % ('n', 'n')))
    rs2 = st([rs, st([eulr], 'eqcomd',
                     'prod_ n e. %s %s = %s' % (PFQL, FACT % ('n', 'n'), GTL))], 'breqtrd',
             'sum_ j e. %s %s <_ %s' % (RSL, DEN('j'), GTL))
    # ---- the indicator sum over CSZ is the sum over RSL
    def rslel(el):
        b = w.s([], 'breq2', '( v = %s -> ( r || v <-> r || %s ) )' % (el, el))
        rb = w.s([b], 'rabbidv', '( v = %s -> %s = %s )' % (el, PFR % 'v', PFR % el))
        eq = w.s([rb], 'eqeq1d',
                 '( v = %s -> ( %s = %s <-> %s = %s ) )' % (el, PFR % 'v', PFQL, PFR % el, PFQL))
        return w.s([eq], 'elrab',
                   '( %s e. %s <-> ( %s e. ( 1 ... Z ) /\ %s = %s ) )'
                   % (el, RSL, el, PFR % el, PFQL))
    # (a) RSL is contained in CSZ
    AM = '( %s /\ m e. %s )' % (AFIB, RSL)
    sm = mkst(w, AM)
    mrsl = rslel('m')
    mmem = sm([sm([mrsl], 'a1i',
                  '( m e. %s <-> ( m e. ( 1 ... Z ) /\ %s = %s ) )' % (RSL, PFR % 'm', PFQL)),
               sm([], 'simpr', 'm e. %s' % RSL)], 'mpbid',
              '( m e. ( 1 ... Z ) /\ %s = %s )' % (PFR % 'm', PFQL))
    mfz = sm([mmem], 'simpld', 'm e. ( 1 ... Z )')
    mpf = sm([mmem], 'simprd', '%s = %s' % (PFR % 'm', PFQL))
    mnn2 = sm([mfz, w.inst('elfznn')], 'syl', 'm e. NN')
    mq = sm([sm([sm([cbvpf(w, 'm')], 'a1i', '%s = %s' % (PFR % 'm', PFQ % 'm'))], 'eqcomd',
                '%s = %s' % (PFQ % 'm', PFR % 'm')), mpf], 'eqtrd',
            '%s = %s' % (PFQ % 'm', PFQL))
    mcop = sm([sm([lift(w, tmid, AM), lift(w, lpair, AM),
                   sm([mnn2, mq], 'jca', '( m e. NN /\ %s = %s )' % (PFQ % 'm', PFQL))],
                  '3jca',
                  '( ( %s /\ %s /\ %s ) /\ ( L e. NN /\ L || P ) /\ '
                  '( m e. NN /\ %s = %s ) )' % (SH, TMR, TRAL, PFQ % 'm', PFQL)),
               w.inst('twincop')], 'syl', '( m gcd ( 2 x. M ) ) = 1')
    mcs = sm([sm([mfz, mcop], 'jca',
                 '( m e. ( 1 ... Z ) /\ ( m gcd ( 2 x. M ) ) = 1 )'),
              sm([csel(w, 'm', '( 2 x. M )', 'Z')], 'a1i',
                 '( m e. %s <-> ( m e. ( 1 ... Z ) /\ ( m gcd ( 2 x. M ) ) = 1 ) )' % CSZ)],
             'mpbird', 'm e. %s' % CSZ)
    rsub = st([st([mcs], 'ex', '( m e. %s -> m e. %s )' % (RSL, CSZ))], 'ssrdv',
              '%s C_ %s' % (RSL, CSZ))
    # (b) the indicator vanishes off RSL
    jcsel = csel(w, 'j', '( 2 x. M )', 'Z')
    jrsl = rslel('j')
    ADJ = '( %s /\ j e. ( %s \ %s ) )' % (AFIB, CSZ, RSL)
    sdj = mkst(w, ADJ)
    jin = sdj([sdj([], 'simpr', 'j e. ( %s \ %s )' % (CSZ, RSL)), w.inst('eldifi')], 'syl',
              'j e. %s' % CSZ)
    jnin = sdj([sdj([], 'simpr', 'j e. ( %s \ %s )' % (CSZ, RSL)), w.inst('eldifn')], 'syl',
               '-. j e. %s' % RSL)
    AEQ = '( %s /\ L = ( P gcd j ) )' % ADJ
    seq = mkst(w, AEQ)
    jfz2 = seq([seq([seq([jcsel], 'a1i',
                         '( j e. %s <-> ( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 ) )'
                         % CSZ), lift(w, jin, AEQ)], 'mpbid',
                    '( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 )')], 'simpld',
               'j e. ( 1 ... Z )')
    jm2 = seq([seq([jcsel], 'a1i',
                   '( j e. %s <-> ( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 ) )' % CSZ),
               lift(w, jin, AEQ)], 'mpbid',
              '( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 )')
    jnn2 = seq([seq([jm2], 'simpld', 'j e. ( 1 ... Z )'), w.inst('elfznn')], 'syl', 'j e. NN')
    jle2 = seq([seq([jm2], 'simpld', 'j e. ( 1 ... Z )'), w.inst('elfzle2')], 'syl', 'j <_ Z')
    jco2 = seq([jm2], 'simprd', '( j gcd ( 2 x. M ) ) = 1')
    jgfe = seq([seq([lift(w, tmid, AEQ), lift(w, lpair, AEQ),
                     seq([jnn2, jle2, jco2], '3jca',
                         '( j e. NN /\ j <_ Z /\ ( j gcd ( 2 x. M ) ) = 1 )')], '3jca',
                    '( ( %s /\ %s /\ %s ) /\ ( L e. NN /\ L || P ) /\ '
                    '( j e. NN /\ j <_ Z /\ ( j gcd ( 2 x. M ) ) = 1 ) )' % (SH, TMR, TRAL)),
                w.inst('twingf')], 'syl',
               '( L = ( P gcd j ) <-> %s = %s )' % (PFQ % 'j', PFQL))
    pfj = seq([jgfe, seq([], 'simpr', 'L = ( P gcd j )')], 'mpbid',
              '%s = %s' % (PFQ % 'j', PFQL))
    pfjr = seq([seq([cbvpf(w, 'j')], 'a1i', '%s = %s' % (PFR % 'j', PFQ % 'j')), pfj], 'eqtrd',
               '%s = %s' % (PFR % 'j', PFQL))
    jinr = seq([seq([jfz2, pfjr], 'jca',
                    '( j e. ( 1 ... Z ) /\ %s = %s )' % (PFR % 'j', PFQL)),
                seq([jrsl], 'a1i',
                    '( j e. %s <-> ( j e. ( 1 ... Z ) /\ %s = %s ) )'
                    % (RSL, PFR % 'j', PFQL))], 'mpbird', 'j e. %s' % RSL)
    nleq = sdj([jnin, jinr], 'mtand', '-. L = ( P gcd j )')
    zerob = sdj([nleq], 'iffalsed', 'if ( L = ( P gcd j ) , %s , 0 ) = 0' % DEN('j'))
    # (c) on RSL the indicator holds
    AJR = '( %s /\ j e. %s )' % (AFIB, RSL)
    sjr = mkst(w, AJR)
    jrm = sjr([sjr([jrsl], 'a1i',
                   '( j e. %s <-> ( j e. ( 1 ... Z ) /\ %s = %s ) )' % (RSL, PFR % 'j', PFQL)),
               sjr([], 'simpr', 'j e. %s' % RSL)], 'mpbid',
              '( j e. ( 1 ... Z ) /\ %s = %s )' % (PFR % 'j', PFQL))
    jrfz = sjr([jrm], 'simpld', 'j e. ( 1 ... Z )')
    jrpf = sjr([jrm], 'simprd', '%s = %s' % (PFR % 'j', PFQL))
    jrq = sjr([sjr([sjr([cbvpf(w, 'j')], 'a1i', '%s = %s' % (PFR % 'j', PFQ % 'j'))], 'eqcomd',
                   '%s = %s' % (PFQ % 'j', PFR % 'j')), jrpf], 'eqtrd',
              '%s = %s' % (PFQ % 'j', PFQL))
    jrnn = sjr([jrfz, w.inst('elfznn')], 'syl', 'j e. NN')
    jrle = sjr([jrfz, w.inst('elfzle2')], 'syl', 'j <_ Z')
    jrcop = sjr([sjr([lift(w, tmid, AJR), lift(w, lpair, AJR),
                      sjr([jrnn, jrq], 'jca',
                          '( j e. NN /\ %s = %s )' % (PFQ % 'j', PFQL))], '3jca',
                     '( ( %s /\ %s /\ %s ) /\ ( L e. NN /\ L || P ) /\ '
                     '( j e. NN /\ %s = %s ) )' % (SH, TMR, TRAL, PFQ % 'j', PFQL)),
                 w.inst('twincop')], 'syl', '( j gcd ( 2 x. M ) ) = 1')
    jrgf = sjr([sjr([lift(w, tmid, AJR), lift(w, lpair, AJR),
                     sjr([jrnn, jrle, jrcop], '3jca',
                         '( j e. NN /\ j <_ Z /\ ( j gcd ( 2 x. M ) ) = 1 )')], '3jca',
                    '( ( %s /\ %s /\ %s ) /\ ( L e. NN /\ L || P ) /\ '
                    '( j e. NN /\ j <_ Z /\ ( j gcd ( 2 x. M ) ) = 1 ) )' % (SH, TMR, TRAL)),
                w.inst('twingf')], 'syl',
               '( L = ( P gcd j ) <-> %s = %s )' % (PFQ % 'j', PFQL))
    jrtrue = sjr([jrgf, jrq], 'mpbird', 'L = ( P gcd j )')
    onebody = sjr([jrtrue], 'iftrued', 'if ( L = ( P gcd j ) , %s , 0 ) = %s'
                  % (DEN('j'), DEN('j')))
    # (d)(e) the two sums agree
    denrp = sjr([sjr([sjr([sjr([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), jrnn,
                          w.inst('sgmnncl')], 'syl2anc', '( 0 sigma j ) e. NN')], 'nnrpd',
                     '( 0 sigma j ) e. RR+'), sjr([jrnn], 'nnrpd', 'j e. RR+')], 'rpdivcld',
                '%s e. RR+' % DEN('j'))
    ifccR = sjr([sjr([denrp], 'rpcnd', '%s e. CC' % DEN('j')),
                 sjr([sjr([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
                'if ( L = ( P gcd j ) , %s , 0 ) e. CC' % DEN('j'))
    csfin = st([st([], 'fzfid', '( 1 ... Z ) e. Fin'),
                st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % CSZ)], 'a1i',
                   '%s C_ ( 1 ... Z )' % CSZ)], 'ssfid', '%s e. Fin' % CSZ)
    ss = st([rsub, ifccR, zerob, csfin], 'fsumss',
            'sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 ) = '
            'sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 )' % (RSL, DEN('j'), CSZ, DEN('j')))
    rsum = st([onebody], 'sumeq2dv',
              'sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 ) = sum_ j e. %s %s'
              % (RSL, DEN('j'), RSL, DEN('j')))
    w.qed([st([st([ss], 'eqcomd',
                  'sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 ) = '
                  'sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 )'
                  % (CSZ, DEN('j'), RSL, DEN('j'))), rsum], 'eqtrd',
              'sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 ) = sum_ j e. %s %s'
              % (CSZ, DEN('j'), RSL, DEN('j'))), rs2], 'eqbrtrd',
          '( %s -> sum_ j e. %s if ( L = ( P gcd j ) , %s , 0 ) <_ %s )'
          % (AFIB, CSZ, DEN('j'), GTL))
    return w


ALL = {'twinfib': twinfib}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
