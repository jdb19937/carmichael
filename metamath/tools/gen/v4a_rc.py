"""Sortie v4a: divisibility of the support quadratic depends only on the residue."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import QF, mkst
from cl import lift

A = ('( ( D e. NN /\\ M e. ZZ ) /\\ ( R e. ZZ /\\ N e. ZZ ) /\\ '
     '( R mod D ) = ( N mod D ) )')


def quadmod():
    w = WS('quadmod', 'Divisibility of R ( M R + 1 ) by D depends only on R modulo D.')
    st = mkst(w, A)
    dnn = st([st([], 'simp1', '( D e. NN /\\ M e. ZZ )')], 'simpld', 'D e. NN')
    mz = st([st([], 'simp1', '( D e. NN /\\ M e. ZZ )')], 'simprd', 'M e. ZZ')
    rz = st([st([], 'simp2', '( R e. ZZ /\\ N e. ZZ )')], 'simpld', 'R e. ZZ')
    nz = st([st([], 'simp2', '( R e. ZZ /\\ N e. ZZ )')], 'simprd', 'N e. ZZ')
    hyp = st([], 'simp3', '( R mod D ) = ( N mod D )')
    drp = st([dnn], 'nnrpd', 'D e. RR+')
    mm = st([], 'eqidd', '( M mod D ) = ( M mod D )')
    s1 = st([mz, mz, rz, nz, drp, mm, hyp], 'modmul12d',
            '( ( M x. R ) mod D ) = ( ( M x. N ) mod D )')
    mrz = st([mz, rz], 'zmulcld', '( M x. R ) e. ZZ')
    mnz = st([mz, nz], 'zmulcld', '( M x. N ) e. ZZ')
    mrr = st([mrz], 'zred', '( M x. R ) e. RR')
    mnr = st([mnz], 'zred', '( M x. N ) e. RR')
    one = st([], '1red', '1 e. RR')
    o1 = st([], 'eqidd', '( 1 mod D ) = ( 1 mod D )')
    s2 = st([mrr, mnr, one, one, drp, s1, o1], 'modadd12d',
            '( ( ( M x. R ) + 1 ) mod D ) = ( ( ( M x. N ) + 1 ) mod D )')
    p1z = st([mrz, st([], '1zzd', '1 e. ZZ')], 'zaddcld', '( ( M x. R ) + 1 ) e. ZZ')
    p2z = st([mnz, st([], '1zzd', '1 e. ZZ')], 'zaddcld', '( ( M x. N ) + 1 ) e. ZZ')
    s3 = st([rz, nz, p1z, p2z, drp, hyp, s2], 'modmul12d',
            '( %s mod D ) = ( %s mod D )' % (QF('R'), QF('N')))
    q1z = st([rz, p1z], 'zmulcld', '%s e. ZZ' % QF('R'))
    q2z = st([nz, p2z], 'zmulcld', '%s e. ZZ' % QF('N'))
    b1 = st([dnn, q1z, w.inst('dvdsval3')], 'syl2anc',
            '( D || %s <-> ( %s mod D ) = 0 )' % (QF('R'), QF('R')))
    b2 = st([dnn, q2z, w.inst('dvdsval3')], 'syl2anc',
            '( D || %s <-> ( %s mod D ) = 0 )' % (QF('N'), QF('N')))
    b3 = st([s3], 'eqeq1d',
            '( ( %s mod D ) = 0 <-> ( %s mod D ) = 0 )' % (QF('R'), QF('N')))
    b2r = st([b2], 'bicomd',
             '( ( %s mod D ) = 0 <-> D || %s )' % (QF('N'), QF('N')))
    w.qed([b1, b3, b2r], '3bitrd',
          '( %s -> ( D || %s <-> D || %s ) )' % (A, QF('R'), QF('N')))
    return w


ALL = {'quadmod': quadmod}


# ---------------------------------------------------------------- rc1, rcprm
from v4a_lib import RT

A1 = 'M e. ZZ'


def rc1():
    w = WS('rc1', 'The quadratic X ( M X + 1 ) has one root modulo 1.')
    st = mkst(w, A1)
    AV = '( %s /\\ v e. ( 0 ..^ 1 ) )' % A1
    sv = mkst(w, AV)
    vz = sv([sv([], 'simpr', 'v e. ( 0 ..^ 1 )'), w.inst('elfzoelz')], 'syl', 'v e. ZZ')
    mz = sv([], 'simpl', 'M e. ZZ')
    qz = sv([vz, sv([sv([mz, vz], 'zmulcld', '( M x. v ) e. ZZ'), sv([], '1zzd', '1 e. ZZ')],
                    'zaddcld', '( ( M x. v ) + 1 ) e. ZZ')], 'zmulcld', '%s e. ZZ' % QF('v'))
    dv1 = sv([qz, w.inst('1dvds')], 'syl', '1 || %s' % QF('v'))
    ral = st([dv1], 'ralrimiva', 'A. v e. ( 0 ..^ 1 ) 1 || %s' % QF('v'))
    rid = st([ral, st([w.s([], 'rabid2',
                      '( ( 0 ..^ 1 ) = %s <-> A. v e. ( 0 ..^ 1 ) 1 || %s )' % (RT('1'), QF('v')))],
                 'a1i',
                 '( ( 0 ..^ 1 ) = %s <-> A. v e. ( 0 ..^ 1 ) 1 || %s )' % (RT('1'), QF('v')))], 'mpbird', '( 0 ..^ 1 ) = %s' % RT('1'))
    fzo = st([w.s([], 'fzo01', '( 0 ..^ 1 ) = { 0 }')], 'a1i', '( 0 ..^ 1 ) = { 0 }')
    seteq = st([st([rid], 'eqcomd', '%s = ( 0 ..^ 1 )' % RT('1')), fzo], 'eqtrd',
               '%s = { 0 }' % RT('1'))
    hs = st([st([w.s([], 'c0ex', '0 e. _V')], 'a1i', '0 e. _V'), w.inst('hashsng')], 'syl',
            '( # ` { 0 } ) = 1')
    w.qed([st([seteq], 'fveq2d', '( # ` %s ) = ( # ` { 0 } )' % RT('1')), hs], 'eqtrd',
          '( %s -> ( # ` %s ) = 1 )' % (A1, RT('1')))
    return w


AP = '( M e. NN /\\ D e. Prime /\\ -. D || M )'
SINV = '( ( -u M ^ ( D - 2 ) ) mod D )'


def rcprm():
    w = WS('rcprm', 'For a prime D not dividing M the quadratic X ( M X + 1 ) has exactly '
                    'two roots modulo D, namely 0 and the inverse of -u M.')
    st = mkst(w, AP)
    mnn = st([], 'simp1', 'M e. NN')
    dprm = st([], 'simp2', 'D e. Prime')
    ndm = st([], 'simp3', '-. D || M')
    mz = st([mnn], 'nnzd', 'M e. ZZ')
    nmz = st([mz], 'znegcld', '-u M e. ZZ')
    dnn = st([dprm, w.inst('prmnn')], 'syl', 'D e. NN')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    # -. D || -u M
    ndnm = st([st([dz, mz, w.inst('dvdsnegb')], 'syl2anc', '( D || M <-> D || -u M )'), ndm],
              'mtbid', '-. D || -u M')
    trip = st([dprm, nmz, ndnm], '3jca', '( D e. Prime /\\ -u M e. ZZ /\\ -. D || -u M )')
    eqi = w.s([], 'eqid', '%s = %s' % (SINV, SINV))
    pdc = w.s([eqi], 'prmdiv',
              '( ( D e. Prime /\\ -u M e. ZZ /\\ -. D || -u M ) -> '
              '( %s e. ( 1 ... ( D - 1 ) ) /\\ D || ( ( -u M x. %s ) - 1 ) ) )' % (SINV, SINV))
    pd = st([trip, pdc], 'syl',
            '( %s e. ( 1 ... ( D - 1 ) ) /\\ D || ( ( -u M x. %s ) - 1 ) )' % (SINV, SINV))
    sfz = st([pd], 'simpld', '%s e. ( 1 ... ( D - 1 ) )' % SINV)
    # ( 0 ..^ D ) = ( 0 ... ( D - 1 ) )
    fzoe = st([dz, w.inst('fzoval')], 'syl', '( 0 ..^ D ) = ( 0 ... ( D - 1 ) )')
    onu = st([st([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0'),
                  st([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', 'NN0 = ( ZZ>= ` 0 )')],
                 'eleqtrd', '1 e. ( ZZ>= ` 0 )')
    ss1 = st([onu, w.inst('fzss1')], 'syl',
             '( 1 ... ( D - 1 ) ) C_ ( 0 ... ( D - 1 ) )')
    sfz0 = st([ss1, sfz], 'sseldd', '%s e. ( 0 ... ( D - 1 ) )' % SINV)
    sfzo = st([sfz0, st([fzoe], 'eqcomd', '( 0 ... ( D - 1 ) ) = ( 0 ..^ D )')], 'eleqtrd',
              '%s e. ( 0 ..^ D )' % SINV)
    lb = st([st([w.s([], 'lbfzo0', '( 0 e. ( 0 ..^ D ) <-> D e. NN )')], 'a1i',
               '( 0 e. ( 0 ..^ D ) <-> D e. NN )'), dnn], 'mpbird', '0 e. ( 0 ..^ D )')
    # the predicate, for v in ( 0 ..^ D )
    AV = '( %s /\\ v e. ( 0 ..^ D ) )' % AP
    sv = mkst(w, AV)
    vfzo = sv([], 'simpr', 'v e. ( 0 ..^ D )')
    vz = sv([vfzo, w.inst('elfzoelz')], 'syl', 'v e. ZZ')
    mvz = sv([lift(w, mz, AV), vz], 'zmulcld', '( M x. v ) e. ZZ')
    mv1z = sv([mvz, sv([], '1zzd', '1 e. ZZ')], 'zaddcld', '( ( M x. v ) + 1 ) e. ZZ')
    eucl = sv([lift(w, dprm, AV), vz, mv1z, w.inst('euclemma')], 'syl3anc',
              '( D || %s <-> ( D || v \\/ D || ( ( M x. v ) + 1 ) ) )' % QF('v'))
    # D || v <-> v = 0
    vmod = sv([vfzo, w.inst('zmodidfzoimp')], 'syl', '( v mod D ) = v')
    dv0 = sv([lift(w, dnn, AV), vz, w.inst('dvdsval3')], 'syl2anc',
             '( D || v <-> ( v mod D ) = 0 )')
    dv0b = sv([dv0, sv([vmod], 'eqeq1d', '( ( v mod D ) = 0 <-> v = 0 )')], 'bitrd',
              '( D || v <-> v = 0 )')
    # D || ( ( M x. v ) + 1 ) <-> v = SINV
    mc = sv([lift(w, mz, AV)], 'zcnd', 'M e. CC')
    vc = sv([vz], 'zcnd', 'v e. CC')
    onec = sv([sv([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    neg1 = sv([mc, vc, w.inst('mulneg1')], 'syl2anc', '( -u M x. v ) = -u ( M x. v )')
    neg2 = sv([neg1], 'oveq1d', '( ( -u M x. v ) - 1 ) = ( -u ( M x. v ) - 1 )')
    mvc = sv([mvz], 'zcnd', '( M x. v ) e. CC')
    neg3 = sv([mvc, onec, w.inst('negdi2')], 'syl2anc',
              '-u ( ( M x. v ) + 1 ) = ( -u ( M x. v ) - 1 )')
    negeq = sv([neg2, sv([neg3], 'eqcomd', '( -u ( M x. v ) - 1 ) = -u ( ( M x. v ) + 1 )')],
               'eqtrd', '( ( -u M x. v ) - 1 ) = -u ( ( M x. v ) + 1 )')
    dneg = sv([lift(w, dz, AV), mv1z, w.inst('dvdsnegb')], 'syl2anc',
              '( D || ( ( M x. v ) + 1 ) <-> D || -u ( ( M x. v ) + 1 ) )')
    dneg2 = sv([dneg, sv([sv([negeq], 'eqcomd',
                             '-u ( ( M x. v ) + 1 ) = ( ( -u M x. v ) - 1 )')], 'breq2d',
                         '( D || -u ( ( M x. v ) + 1 ) <-> D || ( ( -u M x. v ) - 1 ) )')],
                'bitrd', '( D || ( ( M x. v ) + 1 ) <-> D || ( ( -u M x. v ) - 1 ) )')
    vfz = sv([vfzo, lift(w, fzoe, AV)], 'eleqtrd', 'v e. ( 0 ... ( D - 1 ) )')
    peqc = w.s([eqi], 'prmdiveq',
               '( ( D e. Prime /\\ -u M e. ZZ /\\ -. D || -u M ) -> '
               '( ( v e. ( 0 ... ( D - 1 ) ) /\\ D || ( ( -u M x. v ) - 1 ) ) <-> v = %s ) )'
               % SINV)
    peq = sv([lift(w, trip, AV), peqc], 'syl',
             '( ( v e. ( 0 ... ( D - 1 ) ) /\\ D || ( ( -u M x. v ) - 1 ) ) <-> v = %s )' % SINV)
    abs1 = sv([vfz], 'biantrurd',
              '( D || ( ( -u M x. v ) - 1 ) <-> '
              '( v e. ( 0 ... ( D - 1 ) ) /\\ D || ( ( -u M x. v ) - 1 ) ) )')
    dv1b = sv([sv([dneg2, abs1], 'bitrd',
                  '( D || ( ( M x. v ) + 1 ) <-> '
                  '( v e. ( 0 ... ( D - 1 ) ) /\\ D || ( ( -u M x. v ) - 1 ) ) )'), peq],
              'bitrd', '( D || ( ( M x. v ) + 1 ) <-> v = %s )' % SINV)
    orb = sv([dv0b, dv1b], 'orbi12d',
             '( ( D || v \\/ D || ( ( M x. v ) + 1 ) ) <-> ( v = 0 \\/ v = %s ) )' % SINV)
    elp = sv([sv([w.s([], 'elpr', '( v e. { 0 , %s } <-> ( v = 0 \\/ v = %s ) )' % (SINV, SINV))],
                 'a1i', '( v e. { 0 , %s } <-> ( v = 0 \\/ v = %s ) )' % (SINV, SINV))], 'bicomd',
             '( ( v = 0 \\/ v = %s ) <-> v e. { 0 , %s } )' % (SINV, SINV))
    full = sv([sv([eucl, orb], 'bitrd',
                  '( D || %s <-> ( v = 0 \\/ v = %s ) )' % (QF('v'), SINV)), elp], 'bitrd',
              '( D || %s <-> v e. { 0 , %s } )' % (QF('v'), SINV))
    rab1 = st([full], 'rabbidva',
              '%s = { v e. ( 0 ..^ D ) | v e. { 0 , %s } }' % (RT('D'), SINV))
    din = w.s([], 'dfin5', '( ( 0 ..^ D ) i^i { 0 , %s } ) = { x e. ( 0 ..^ D ) | x e. { 0 , %s } }'
              % (SINV, SINV))
    cbv = w.s([w.s([], 'eleq1', '( x = v -> ( x e. { 0 , %s } <-> v e. { 0 , %s } ) )' % (SINV, SINV))],
              'cbvrabv',
              '{ x e. ( 0 ..^ D ) | x e. { 0 , %s } } = { v e. ( 0 ..^ D ) | v e. { 0 , %s } }'
              % (SINV, SINV))
    din2 = st([st([din], 'a1i',
                  '( ( 0 ..^ D ) i^i { 0 , %s } ) = { x e. ( 0 ..^ D ) | x e. { 0 , %s } }'
                  % (SINV, SINV)),
               st([cbv], 'a1i',
                  '{ x e. ( 0 ..^ D ) | x e. { 0 , %s } } = { v e. ( 0 ..^ D ) | v e. { 0 , %s } }'
                  % (SINV, SINV))], 'eqtrd',
              '( ( 0 ..^ D ) i^i { 0 , %s } ) = { v e. ( 0 ..^ D ) | v e. { 0 , %s } }'
              % (SINV, SINV))
    prss = st([st([lb, sfzo], 'jca', '( 0 e. ( 0 ..^ D ) /\\ %s e. ( 0 ..^ D ) )' % SINV),
               st([w.s([], 'prssi',
                       '( ( 0 e. ( 0 ..^ D ) /\\ %s e. ( 0 ..^ D ) ) -> { 0 , %s } C_ ( 0 ..^ D ) )'
                       % (SINV, SINV))], 'a1i',
                  '( ( 0 e. ( 0 ..^ D ) /\\ %s e. ( 0 ..^ D ) ) -> { 0 , %s } C_ ( 0 ..^ D ) )'
                  % (SINV, SINV))], 'mpd', '{ 0 , %s } C_ ( 0 ..^ D )' % SINV)
    ineq = st([st([w.s([], 'sseqin2',
                       '( { 0 , %s } C_ ( 0 ..^ D ) <-> ( ( 0 ..^ D ) i^i { 0 , %s } ) = { 0 , %s } )'
                       % (SINV, SINV, SINV))], 'a1i',
                  '( { 0 , %s } C_ ( 0 ..^ D ) <-> ( ( 0 ..^ D ) i^i { 0 , %s } ) = { 0 , %s } )'
                  % (SINV, SINV, SINV)), prss], 'mpbid',
              '( ( 0 ..^ D ) i^i { 0 , %s } ) = { 0 , %s }' % (SINV, SINV))
    seteq = st([rab1, st([din2, ineq], 'eqtr3d',
                         '{ v e. ( 0 ..^ D ) | v e. { 0 , %s } } = { 0 , %s }' % (SINV, SINV))],
               'eqtrd', '%s = { 0 , %s }' % (RT('D'), SINV))
    # 0 =/= SINV
    sge1 = st([sfz, w.inst('elfzle1')], 'syl', '1 <_ %s' % SINV)
    sre = st([st([sfz, w.inst('elfzelz')], 'syl', '%s e. ZZ' % SINV)], 'zred', '%s e. RR' % SINV)
    from lin import linarith
    s0lt = linarith(w, AP, [sge1], '0 < %s' % SINV, leaves={SINV: sre})
    sne = st([s0lt], 'ltned', '0 =/= %s' % SINV)
    hpr = st([st([st([w.s([], 'c0ex', '0 e. _V')], 'a1i', '0 e. _V'),
                  st([sre], 'elexd', '%s e. _V' % SINV), w.inst('hashprg')], 'syl2anc',
                 '( 0 =/= %s <-> ( # ` { 0 , %s } ) = 2 )' % (SINV, SINV)), sne], 'mpbid',
              '( # ` { 0 , %s } ) = 2' % SINV)
    w.qed([st([seteq], 'fveq2d', '( # ` %s ) = ( # ` { 0 , %s } )' % (RT('D'), SINV)), hpr],
          'eqtrd', '( %s -> ( # ` %s ) = 2 )' % (AP, RT('D')))
    return w


ALL['rc1'] = rc1
ALL['rcprm'] = rcprm


if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
