"""Sortie z4c: the harmonic sum is at most K / phi ( K ) times the coprime harmonic sum.

cophrmh is V3's cophrm (tools/gen/v3_cop.py) without its final logarithm step:
the body of cophrm up to `mulle` is reused verbatim, and the conclusion stops at
( HARM <_ ( KPHI x. SCOP ) ), so that a consumer may put any lower bound of the
harmonic sum in front of it (cophrmfl: harmoniclbnd at a real A).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v3_cop import *
from v3_cop import WS, mkst, lift, linarith, rege0c


def cophrmh():
    w = WS('cophrmh', 'The harmonic sum up to W is at most K / phi ( K ) times '
                     'the harmonic sum over the integers up to W coprime to K.')
    st = mkst(w, AK)
    knn = st([], 'simpl', 'K e. NN')
    wnn = st([], 'simpr', 'W e. NN')
    fzfin = st([], 'fzfid', '%s e. Fin' % FZW)
    smss = st([w.s([], 'ssrab2', '%s C_ %s' % (SMK, FZW))], 'a1i', '%s C_ %s' % (SMK, FZW))
    smfin = st([fzfin, smss], 'ssfid', '%s e. Fin' % SMK)
    csss = st([w.s([], 'ssrab2', '%s C_ %s' % (CSK, FZW))], 'a1i', '%s C_ %s' % (CSK, FZW))
    csfin = st([fzfin, csss], 'ssfid', '%s e. Fin' % CSK)
    # G and H are nonnegative functions
    AO = '( %s /\\ o e. %s )' % (AK, SMK)
    so = mkst(w, AO)
    onn = so([so([lift(w, smss, AO), so([], 'simpr', 'o e. %s' % SMK)], 'sseldd',
                 'o e. %s' % FZW), w.inst('elfznn')], 'syl', 'o e. NN')
    orp = so([so([onn], 'nnrpd', 'o e. RR+')], 'rpreccld', '( 1 / o ) e. RR+')
    gel = rege0c(w, AO, '( 1 / o )', orp)
    gfn = st([gel, w.s([], 'eqid', '%s = %s' % (GMAPC, GMAPC))], 'fmptd',
             '%s : %s --> ( 0 [,) +oo )' % (GMAPC, SMK))
    AFF = '( %s /\\ f e. %s )' % (AK, CSK)
    sff = mkst(w, AFF)
    fnn = sff([sff([lift(w, csss, AFF), sff([], 'simpr', 'f e. %s' % CSK)], 'sseldd',
                   'f e. %s' % FZW), w.inst('elfznn')], 'syl', 'f e. NN')
    frp = sff([sff([fnn], 'nnrpd', 'f e. RR+')], 'rpreccld', '( 1 / f ) e. RR+')
    hel = rege0c(w, AFF, '( 1 / f )', frp)
    hfn = st([hel, w.s([], 'eqid', '%s = %s' % (HMAPC, HMAPC))], 'fmptd',
             '%s : %s --> ( 0 [,) +oo )' % (HMAPC, CSK))
    f1 = st([], 'cof1', '%s : %s -1-1-> %s' % (FMAPC, FZW, XSC))
    spu = st([st([smfin, csfin, fzfin], '3jca',
                 '( %s e. Fin /\\ %s e. Fin /\\ %s e. Fin )' % (SMK, CSK, FZW)),
              st([gfn, hfn], 'jca',
                 '( %s : %s --> ( 0 [,) +oo ) /\\ %s : %s --> ( 0 [,) +oo ) )'
                 % (GMAPC, SMK, HMAPC, CSK)), f1, w.inst('sumprodub')], 'syl3anc',
             '%s <_ ( %s x. %s )' % (SBODYC, SMSUMI, SCOPH))
    # the two right-hand sums
    AI = '( %s /\\ i e. %s )' % (AK, SMK)
    si = mkst(w, AI)
    gival = si([si([si([], 'simpr', 'i e. %s' % SMK),
                    si([w.s([], 'ovex', '( 1 / i ) e. _V')], 'a1i', '( 1 / i ) e. _V')], 'jca',
                   '( i e. %s /\\ ( 1 / i ) e. _V )' % SMK),
                si([w.s([w.s([], 'oveq2', '( o = i -> ( 1 / o ) = ( 1 / i ) )'),
                         w.s([], 'eqid', '%s = %s' % (GMAPC, GMAPC))], 'fvmptg',
                        '( ( i e. %s /\\ ( 1 / i ) e. _V ) -> ( %s ` i ) = ( 1 / i ) )'
                        % (SMK, GMAPC))], 'a1i',
                   '( ( i e. %s /\\ ( 1 / i ) e. _V ) -> ( %s ` i ) = ( 1 / i ) )'
                   % (SMK, GMAPC))], 'mpd', '( %s ` i ) = ( 1 / i )' % GMAPC)
    gsum = st([gival], 'sumeq2dv', '%s = %s' % (SMSUMI, SMSUMII))
    cbg = st([w.s([w.s([], 'oveq2', '( i = j -> ( 1 / i ) = ( 1 / j ) )')], 'cbvsumv',
                  '%s = %s' % (SMSUMII, SMSUMJ))], 'a1i', '%s = %s' % (SMSUMII, SMSUMJ))
    gsum2 = st([gsum, cbg], 'eqtrd', '%s = %s' % (SMSUMI, SMSUMJ))
    AJ = '( %s /\\ j e. %s )' % (AK, CSK)
    sj = mkst(w, AJ)
    hjval = sj([sj([sj([], 'simpr', 'j e. %s' % CSK),
                    sj([w.s([], 'ovex', '( 1 / j ) e. _V')], 'a1i', '( 1 / j ) e. _V')], 'jca',
                   '( j e. %s /\\ ( 1 / j ) e. _V )' % CSK),
                sj([w.s([w.s([], 'oveq2', '( f = j -> ( 1 / f ) = ( 1 / j ) )'),
                         w.s([], 'eqid', '%s = %s' % (HMAPC, HMAPC))], 'fvmptg',
                        '( ( j e. %s /\\ ( 1 / j ) e. _V ) -> ( %s ` j ) = ( 1 / j ) )'
                        % (CSK, HMAPC))], 'a1i',
                   '( ( j e. %s /\\ ( 1 / j ) e. _V ) -> ( %s ` j ) = ( 1 / j ) )'
                   % (CSK, HMAPC))], 'mpd', '( %s ` j ) = ( 1 / j )' % HMAPC)
    hsum = st([hjval], 'sumeq2dv', '%s = %s' % (SCOPH, SCOP))
    rhs = st([gsum2, hsum], 'oveq12d',
             '( %s x. %s ) = ( %s x. %s )' % (SMSUMI, SCOPH, SMSUMJ, SCOP))
    spu2 = st([spu, rhs], 'breqtrd', '%s <_ ( %s x. %s )' % (SBODYC, SMSUMJ, SCOP))
    # the left-hand body is 1 / m
    AM = '( %s /\\ m e. %s )' % (AK, FZW)
    sm = mkst(w, AM)
    mfz = sm([], 'simpr', 'm e. %s' % FZW)
    spl = sm([sm([], 'id', AM), w.inst('cosplit')], 'syl',
             '( ( m gcd ( K ^ m ) ) e. %s /\\ ( m / ( m gcd ( K ^ m ) ) ) e. %s /\\ '
             '( ( m gcd ( K ^ m ) ) x. ( m / ( m gcd ( K ^ m ) ) ) ) = m )' % (SMK, CSK))
    GM = '( m gcd ( K ^ m ) )'
    BM = '( m / ( m gcd ( K ^ m ) ) )'
    gsm = sm([spl], 'simp1d', '%s e. %s' % (GM, SMK))
    bcs = sm([spl], 'simp2d', '%s e. %s' % (BM, CSK))
    prodm = sm([spl], 'simp3d', '( %s x. %s ) = m' % (GM, BM))
    tm = w.s([], 'id', '( t = m -> t = m )')
    ktm = w.s([tm], 'oveq2d', '( t = m -> ( K ^ t ) = ( K ^ m ) )')
    gtm = w.s([tm, ktm], 'oveq12d', '( t = m -> ( t gcd ( K ^ t ) ) = %s )' % GM)
    btm = w.s([tm, gtm], 'oveq12d',
              '( t = m -> ( t / ( t gcd ( K ^ t ) ) ) = %s )' % BM)
    cbp = w.s([gtm, btm], 'opeq12d', '( t = m -> %s = %s )' % (PAIRC('t'), PAIRC('m')))
    fmv = sm([sm([mfz, sm([w.s([], 'opex', '%s e. _V' % PAIRC('m'))], 'a1i',
                          '%s e. _V' % PAIRC('m'))], 'jca',
                 '( m e. %s /\\ %s e. _V )' % (FZW, PAIRC('m'))),
              sm([w.s([cbp, w.s([], 'eqid', '%s = %s' % (FMAPC, FMAPC))], 'fvmptg',
                      '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )'
                      % (FZW, PAIRC('m'), FMAPC, PAIRC('m')))], 'a1i',
                 '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )'
                 % (FZW, PAIRC('m'), FMAPC, PAIRC('m')))], 'mpd',
             '( %s ` m ) = %s' % (FMAPC, PAIRC('m')))
    gex = w.s([], 'ovex', '%s e. _V' % GM)
    bex = w.s([], 'ovex', '%s e. _V' % BM)
    o1 = w.s([gex, bex], 'op1st', '( 1st ` %s ) = %s' % (PAIRC('m'), GM))
    o2 = w.s([gex, bex], 'op2nd', '( 2nd ` %s ) = %s' % (PAIRC('m'), BM))
    f1st = sm([sm([fmv], 'fveq2d',
                  '( 1st ` ( %s ` m ) ) = ( 1st ` %s )' % (FMAPC, PAIRC('m'))),
               sm([o1], 'a1i', '( 1st ` %s ) = %s' % (PAIRC('m'), GM))], 'eqtrd',
              '( 1st ` ( %s ` m ) ) = %s' % (FMAPC, GM))
    f2nd = sm([sm([fmv], 'fveq2d',
                  '( 2nd ` ( %s ` m ) ) = ( 2nd ` %s )' % (FMAPC, PAIRC('m'))),
               sm([o2], 'a1i', '( 2nd ` %s ) = %s' % (PAIRC('m'), BM))], 'eqtrd',
              '( 2nd ` ( %s ` m ) ) = %s' % (FMAPC, BM))
    gval = sm([sm([gsm, sm([w.s([], 'ovex', '( 1 / %s ) e. _V' % GM)], 'a1i',
                           '( 1 / %s ) e. _V' % GM)], 'jca',
                  '( %s e. %s /\\ ( 1 / %s ) e. _V )' % (GM, SMK, GM)),
               sm([w.s([w.s([], 'oveq2', '( o = %s -> ( 1 / o ) = ( 1 / %s ) )' % (GM, GM)),
                        w.s([], 'eqid', '%s = %s' % (GMAPC, GMAPC))], 'fvmptg',
                       '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                       % (GM, SMK, GM, GMAPC, GM, GM))], 'a1i',
                  '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                  % (GM, SMK, GM, GMAPC, GM, GM))], 'mpd',
              '( %s ` %s ) = ( 1 / %s )' % (GMAPC, GM, GM))
    hval = sm([sm([bcs, sm([w.s([], 'ovex', '( 1 / %s ) e. _V' % BM)], 'a1i',
                           '( 1 / %s ) e. _V' % BM)], 'jca',
                  '( %s e. %s /\\ ( 1 / %s ) e. _V )' % (BM, CSK, BM)),
               sm([w.s([w.s([], 'oveq2', '( f = %s -> ( 1 / f ) = ( 1 / %s ) )' % (BM, BM)),
                        w.s([], 'eqid', '%s = %s' % (HMAPC, HMAPC))], 'fvmptg',
                       '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                       % (BM, CSK, BM, HMAPC, BM, BM))], 'a1i',
                  '( ( %s e. %s /\\ ( 1 / %s ) e. _V ) -> ( %s ` %s ) = ( 1 / %s ) )'
                  % (BM, CSK, BM, HMAPC, BM, BM))], 'mpd',
              '( %s ` %s ) = ( 1 / %s )' % (HMAPC, BM, BM))
    b1 = sm([sm([f1st], 'fveq2d',
                '( %s ` ( 1st ` ( %s ` m ) ) ) = ( %s ` %s )' % (GMAPC, FMAPC, GMAPC, GM)),
             gval], 'eqtrd',
            '( %s ` ( 1st ` ( %s ` m ) ) ) = ( 1 / %s )' % (GMAPC, FMAPC, GM))
    b2 = sm([sm([f2nd], 'fveq2d',
                '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( %s ` %s )' % (HMAPC, FMAPC, HMAPC, BM)),
             hval], 'eqtrd',
            '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( 1 / %s )' % (HMAPC, FMAPC, BM))
    bmul = sm([b1, b2], 'oveq12d',
              '%s = ( ( 1 / %s ) x. ( 1 / %s ) )' % (BODYC, GM, BM))
    mnn = sm([mfz, w.inst('elfznn')], 'syl', 'm e. NN')
    gmnn = sm([sm([lift(w, smss, AM), gsm], 'sseldd', '%s e. %s' % (GM, FZW)),
               w.inst('elfznn')], 'syl', '%s e. NN' % GM)
    bmnn = sm([sm([lift(w, csss, AM), bcs], 'sseldd', '%s e. %s' % (BM, FZW)),
               w.inst('elfznn')], 'syl', '%s e. NN' % BM)
    onec = sm([sm([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    dmd = sm([sm([onec, onec], 'jca', '( 1 e. CC /\\ 1 e. CC )'),
              sm([sm([sm([gmnn], 'nncnd', '%s e. CC' % GM),
                      sm([gmnn], 'nnne0d', '%s =/= 0' % GM)], 'jca',
                     '( %s e. CC /\\ %s =/= 0 )' % (GM, GM)),
                  sm([sm([bmnn], 'nncnd', '%s e. CC' % BM),
                      sm([bmnn], 'nnne0d', '%s =/= 0' % BM)], 'jca',
                     '( %s e. CC /\\ %s =/= 0 )' % (BM, BM))], 'jca',
                 '( ( %s e. CC /\\ %s =/= 0 ) /\\ ( %s e. CC /\\ %s =/= 0 ) )'
                 % (GM, GM, BM, BM)), w.inst('divmuldiv')], 'syl2anc',
             '( ( 1 / %s ) x. ( 1 / %s ) ) = ( ( 1 x. 1 ) / ( %s x. %s ) )' % (GM, BM, GM, BM))
    t11 = sm([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')
    dmd2 = sm([dmd, sm([sm([t11], 'oveq1d',
                           '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / ( %s x. %s ) )'
                           % (GM, BM, GM, BM)),
                        sm([prodm], 'oveq2d',
                           '( 1 / ( %s x. %s ) ) = ( 1 / m )' % (GM, BM))], 'eqtrd',
                       '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / m )' % (GM, BM))], 'eqtrd',
              '( ( 1 / %s ) x. ( 1 / %s ) ) = ( 1 / m )' % (GM, BM))
    bfin = sm([bmul, dmd2], 'eqtrd', '%s = ( 1 / m )' % BODYC)
    lsum = st([bfin], 'sumeq2dv', '%s = %s' % (SBODYC, HARM))
    main = st([lsum, spu2], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (HARM, SMSUMJ, SCOP))
    # smsum at Q = PF( K )
    sbq = w.s([], 'breq1', '( p = q -> ( p || K <-> q || K ) )')
    cbk = w.s([sbq], 'cbvrabv', '{ p e. Prime | p || K } = %s' % PFK)
    pffin0 = st([knn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || K } e. Fin')
    pffin = st([st([cbk], 'a1i', '{ p e. Prime | p || K } = %s' % PFK), pffin0], 'eqeltrrd',
               '%s e. Fin' % PFK)
    pfsub = st([w.s([], 'ssrab2', '%s C_ Prime' % PFK)], 'a1i', '%s C_ Prime' % PFK)
    sms = st([pffin, pfsub, wnn, w.inst('smsum')], 'syl3anc', '%s <_ %s' % (SMSUMJ, PRPFK))
    # PRPFK = K / phi ( K )
    AP = '( %s /\\ p e. %s )' % (AK, PFK)
    sp = mkst(w, AP)
    pprm = sp([lift(w, pfsub, AP), sp([], 'simpr', 'p e. %s' % PFK)], 'sseldd', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    pre = sp([prp], 'rpred', 'p e. RR')
    ppos = sp([prp], 'rpgt0d', '0 < p')
    pge = sp([sp([pprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )'), w.inst('eluzle')],
             'syl', '2 <_ p')
    p1lt = linarith(w, AP, [pge], '1 < p', leaves={'p': pre})
    prc = sp([sp([sp([pre, ppos], 'jca', '( p e. RR /\\ 0 < p )'), w.inst('recgt1')], 'syl',
                 '( 1 < p <-> ( 1 / p ) < 1 )'), p1lt], 'mpbid', '( 1 / p ) < 1')
    prire = sp([sp([prp], 'rpreccld', '( 1 / p ) e. RR+')], 'rpred', '( 1 / p ) e. RR')
    pone = sp([], '1red', '1 e. RR')
    psubr = sp([pone, prire], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    psub0 = sp([sp([prire, pone], 'posdifd', '( ( 1 / p ) < 1 <-> 0 < ( 1 - ( 1 / p ) ) )'),
                prc], 'mpbid', '0 < ( 1 - ( 1 / p ) )')
    psubrp = sp([psubr, psub0], 'elrpd', '( 1 - ( 1 / p ) ) e. RR+')
    psubc = sp([psubr], 'recnd', '( 1 - ( 1 / p ) ) e. CC')
    psubne = sp([psubrp], 'rpne0d', '( 1 - ( 1 / p ) ) =/= 0')
    onec2 = sp([sp([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    fd = st([pffin, onec2, psubc, psubne], 'fproddiv',
            '%s = ( prod_ p e. %s 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) )' % (PRPFK, PFK, PFK))
    p1v = st([st([pffin], 'olcd', '( %s C_ ( ZZ>= ` M ) \\/ %s e. Fin )' % (PFK, PFK)),
              w.inst('prod1')], 'syl', 'prod_ p e. %s 1 = 1' % PFK)
    phival = st([knn, w.inst('phipfprod')], 'syl',
                'prod_ p e. %s ( 1 - ( 1 / p ) ) = %s' % (PFK, PHIK))
    phinn = st([knn], 'phicld', '( phi ` K ) e. NN')
    phirp = st([phinn], 'nnrpd', '( phi ` K ) e. RR+')
    krp = st([knn], 'nnrpd', 'K e. RR+')
    phikrp = st([phirp, krp], 'rpdivcld', '%s e. RR+' % PHIK)
    phikc = st([st([phikrp], 'rpred', '%s e. RR' % PHIK)], 'recnd', '%s e. CC' % PHIK)
    phikne = st([phikrp], 'rpne0d', '%s =/= 0' % PHIK)
    fd2 = st([fd, st([st([p1v], 'oveq1d',
                         '( prod_ p e. %s 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) ) = '
                         '( 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) )' % (PFK, PFK, PFK)),
                      st([phival], 'oveq2d',
                         '( 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) ) = ( 1 / %s )' % (PFK, PHIK))],
                     'eqtrd',
                     '( prod_ p e. %s 1 / prod_ p e. %s ( 1 - ( 1 / p ) ) ) = ( 1 / %s )'
                     % (PFK, PFK, PHIK))], 'eqtrd', '%s = ( 1 / %s )' % (PRPFK, PHIK))
    rd = st([st([st([st([phinn], 'nncnd', '( phi ` K ) e. CC'),
                     st([phinn], 'nnne0d', '( phi ` K ) =/= 0')], 'jca',
                    '( ( phi ` K ) e. CC /\\ ( phi ` K ) =/= 0 )'),
                 st([st([knn], 'nncnd', 'K e. CC'), st([knn], 'nnne0d', 'K =/= 0')], 'jca',
                    '( K e. CC /\\ K =/= 0 )')], 'jca',
                '( ( ( phi ` K ) e. CC /\\ ( phi ` K ) =/= 0 ) /\\ ( K e. CC /\\ K =/= 0 ) )'),
             w.inst('recdiv')], 'syl', '( 1 / %s ) = %s' % (PHIK, KPHI))
    prval = st([fd2, rd], 'eqtrd', '%s = %s' % (PRPFK, KPHI))
    sms2 = st([sms, prval], 'breqtrd', '%s <_ %s' % (SMSUMJ, KPHI))
    # assemble
    ANJ = '( %s /\\ j e. %s )' % (AK, SMK)
    snj = mkst(w, ANJ)
    jnn1 = snj([snj([lift(w, smss, ANJ), snj([], 'simpr', 'j e. %s' % SMK)], 'sseldd',
                    'j e. %s' % FZW), w.inst('elfznn')], 'syl', 'j e. NN')
    jrp1 = snj([snj([jnn1], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jre1 = snj([jrp1], 'rpred', '( 1 / j ) e. RR')
    smre = st([smfin, jre1], 'fsumrecl', '%s e. RR' % SMSUMJ)
    smge = st([smfin, jre1, snj([jrp1], 'rpge0d', '0 <_ ( 1 / j )')], 'fsumge0',
              '0 <_ %s' % SMSUMJ)
    ACJ = '( %s /\\ j e. %s )' % (AK, CSK)
    scj = mkst(w, ACJ)
    jnn2 = scj([scj([lift(w, csss, ACJ), scj([], 'simpr', 'j e. %s' % CSK)], 'sseldd',
                    'j e. %s' % FZW), w.inst('elfznn')], 'syl', 'j e. NN')
    jrp2 = scj([scj([jnn2], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jre2 = scj([jrp2], 'rpred', '( 1 / j ) e. RR')
    scre = st([csfin, jre2], 'fsumrecl', '%s e. RR' % SCOP)
    scge = st([csfin, jre2, scj([jrp2], 'rpge0d', '0 <_ ( 1 / j )')], 'fsumge0', '0 <_ %s' % SCOP)
    AMM = '( %s /\\ m e. %s )' % (AK, FZW)
    smm = mkst(w, AMM)
    mre = smm([smm([smm([smm([], 'simpr', 'm e. %s' % FZW), w.inst('elfznn')], 'syl', 'm e. NN')],
                   'nnrpd', 'm e. RR+')], 'rpreccld', '( 1 / m ) e. RR+')
    hre = st([fzfin, smm([mre], 'rpred', '( 1 / m ) e. RR')], 'fsumrecl', '%s e. RR' % HARM)
    kphire = st([st([krp, phirp], 'rpdivcld', '%s e. RR+' % KPHI)], 'rpred', '%s e. RR' % KPHI)
    mulle = st([smre, kphire, scre, scge, sms2], 'lemul1ad',
               '( %s x. %s ) <_ ( %s x. %s )' % (SMSUMJ, SCOP, KPHI, SCOP))
    p1re = st([smre, scre], 'remulcld', '( %s x. %s ) e. RR' % (SMSUMJ, SCOP))
    p2re = st([kphire, scre], 'remulcld', '( %s x. %s ) e. RR' % (KPHI, SCOP))
    w.qed([hre, p1re, p2re, main, mulle], 'letrd', '( %s -> %s <_ ( %s x. %s ) )' % (AK, HARM, KPHI, SCOP))
    return w


ALL = {'cophrmh': cophrmh}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
