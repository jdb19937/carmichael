"""Sortie v4b: bruntit, Brun-Titchmarsh for the progression 1 mod M."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import TT, SS, DV, GTV, V, mkst
import num
from lin import linarith, nlinarith, lineq

C2E8 = num.nat_text(200000000)
C64 = num.nat_text(6400000)
FR = '( %s / %s )' % (num.nat_text(19), num.nat_text(20))
ANT = ('( ( N e. NN0 /\\ M e. ( ZZ>= ` 2 ) ) /\\ ( M <_ ( N ^c %s ) /\\ ( exp ` %s ) <_ N ) )'
       % (FR, C2E8))
NM = '( N / M )'
LG = '( log ` %s )' % NM
E25 = '( exp ` ( ( 2 / 5 ) x. %s ) )' % LG
ZF = '( |_ ` %s )' % E25
PM = '( phi ` M )'
WU = '( N / ( %s x. %s ) )' % (PM, LG)
TTS = TT
GOAL = '( # ` %s ) <_ ( ( 3 x. N ) / ( %s x. %s ) )' % (TTS, PM, LG)
K14 = '( %s / 5 )' % num.nat_text(14)
K5 = '( 5 / %s )' % num.nat_text(14)
G = '( ( %s / M ) x. ( %s x. %s ) )' % (PM, K5, LG)
ERB = '( ( %s ^ 2 ) x. ( ( 1 + %s ) ^ 2 ) )' % (E25, LG)
LOGZ2 = '( log ` ( %s ^ 2 ) )' % ZF
ETERM = '( ( %s ^ 2 ) x. ( ( 1 + %s ) ^ 2 ) )' % (ZF, LOGZ2)
SSZ = SS.replace(' Z ', ' %s ' % ZF).replace('( Z ^ 2 )', '( %s ^ 2 )' % ZF)


def subZ(expr):
    return expr.replace('( 0 ... Z )', '( 0 ... %s )' % ZF).replace(
        '( Z ^ 2 )', '( %s ^ 2 )' % ZF)


def bruntit():
    w = W('bruntit', 'Brun-Titchmarsh for the arithmetic progression 1 mod M: the primes '
                     'up to N congruent to 1 mod M number at most 3 N / ( phi ( M ) log ( N / M ) ).')
    st = mkst(w, ANT)
    SSF = subZ(SS)
    nn0 = st([], 'simpll', 'N e. NN0')
    muz = st([], 'simplr', 'M e. ( ZZ>= ` 2 )')
    hmy = st([], 'simprl', 'M <_ ( N ^c %s )' % FR)
    hy = st([], 'simprr', '( exp ` %s ) <_ N' % C2E8)
    mnn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    nre = st([nn0], 'nn0red', 'N e. RR')
    mrp = st([mnn, w.inst('nnrp')], 'syl', 'M e. RR+')
    mre = st([mrp], 'rpred', 'M e. RR')
    mne = st([mrp], 'rpne0d', 'M =/= 0')
    c2e8 = st([num.re_nat(w, 200000000)], 'a1i', '%s e. RR' % C2E8)
    efrp = st([c2e8, w.inst('rpefcl')], 'syl', '( exp ` %s ) e. RR+' % C2E8)
    efpos = st([efrp, w.inst('rpgt0')], 'syl', '0 < ( exp ` %s )' % C2E8)
    npos = st([st([], '0red', '0 e. RR'), st([efrp], 'rpred', '( exp ` %s ) e. RR' % C2E8),
               nre, efpos, hy], 'ltletrd', '0 < N')
    nrp = st([nre, npos], 'elrpd', 'N e. RR+')
    nmrp = st([nrp, mrp], 'rpdivcld', '%s e. RR+' % NM)
    lgre = st([nmrp], 'relogcld', '%s e. RR' % LG)
    LV = {LG: lgre}
    # --- log bounds -------------------------------------------------------
    lognre = st([nrp], 'relogcld', '( log ` N ) e. RR')
    logmre = st([mrp], 'relogcld', '( log ` M ) e. RR')
    lgef = st([c2e8, w.inst('relogef')], 'syl',
              '( log ` ( exp ` %s ) ) = %s' % (C2E8, C2E8))
    lgmono = st([efrp, nrp, w.inst('logleb')], 'syl2anc',
                '( ( exp ` %s ) <_ N <-> ( log ` ( exp ` %s ) ) <_ ( log ` N ) )'
                % (C2E8, C2E8))
    hlogn = st([st([lgmono, hy], 'mpbid',
                   '( log ` ( exp ` %s ) ) <_ ( log ` N )' % C2E8), lgef], 'eqbrtrrd',
               '%s <_ ( log ` N )' % C2E8)
    frre = st([num.real(w, FR)], 'a1i', '%s e. RR' % FR)
    cxrp = st([nrp, frre, w.inst('rpcxpcl')], 'syl2anc', '( N ^c %s ) e. RR+' % FR)
    lgmono2 = st([mrp, cxrp, w.inst('logleb')], 'syl2anc',
                 '( M <_ ( N ^c %s ) <-> ( log ` M ) <_ ( log ` ( N ^c %s ) ) )' % (FR, FR))
    lgcx = st([nrp, frre, w.inst('logcxp')], 'syl2anc',
              '( log ` ( N ^c %s ) ) = ( %s x. ( log ` N ) )' % (FR, FR))
    hlogm = st([st([lgmono2, hmy], 'mpbid',
                   '( log ` M ) <_ ( log ` ( N ^c %s ) )' % FR), lgcx], 'breqtrd',
               '( log ` M ) <_ ( %s x. ( log ` N ) )' % FR)
    lgeq = st([nrp, mrp, w.inst('relogdiv')], 'syl2anc',
              '%s = ( ( log ` N ) - ( log ` M ) )' % LG)
    LV2 = {'( log ` N )': lognre, '( log ` M )': logmre}
    hsub = linarith(w, ANT, [hlogn, hlogm],
                    '%s <_ ( ( log ` N ) - ( log ` M ) )' % C64, leaves=LV2)
    hL = st([hsub, lgeq], 'breqtrrd', '%s <_ %s' % (C64, LG))
    hL1 = linarith(w, ANT, [hL], '1 <_ %s' % LG, leaves=LV)
    hL0 = linarith(w, ANT, [hL], '0 <_ %s' % LG, leaves=LV)
    hLpos = linarith(w, ANT, [hL], '0 < %s' % LG, leaves=LV)
    lgrp = st([lgre, hLpos], 'elrpd', '%s e. RR+' % LG)
    # --- the level, from btlev --------------------------------------------
    ALL = '( %s e. RR /\\ %s <_ %s )' % (LG, C64, LG)
    CONCL = ('( ( %s e. NN /\\ 2 <_ %s ) /\\ ( ( %s x. %s ) <_ ( log ` %s ) /\\ '
             '( log ` %s ) <_ ( ( 2 / 5 ) x. %s ) ) /\\ %s <_ %s )'
             % (ZF, ZF, K5, LG, ZF, ZF, LG, ZF, E25))
    hyl = st([lgre, hL], 'jca', ALL)
    lev = st([hyl, w.inst('btlev')], 'syl', CONCL)
    zfnn = st([st([lev], 'simp1d', '( %s e. NN /\\ 2 <_ %s )' % (ZF, ZF))], 'simpld',
              '%s e. NN' % ZF)
    lzlb = st([st([lev], 'simp2d',
                  '( ( %s x. %s ) <_ ( log ` %s ) /\\ ( log ` %s ) <_ ( ( 2 / 5 ) x. %s ) )'
                  % (K5, LG, ZF, ZF, LG))], 'simpld',
              '( %s x. %s ) <_ ( log ` %s )' % (K5, LG, ZF))
    zfrp = st([zfnn, w.inst('nnrp')], 'syl', '%s e. RR+' % ZF)
    zfre = st([zfrp], 'rpred', '%s e. RR' % ZF)
    logzre = st([zfrp], 'relogcld', '( log ` %s ) e. RR' % ZF)
    # --- the sieve at Z := ZF ----------------------------------------------
    from v4b_lib import SH, TT as TTX
    SHZ = subZ(SH)
    SSF2 = SSF
    PHZ = '( M e. ( ZZ>= ` 2 ) /\\ %s e. NN /\\ N e. NN0 )' % ZF
    phz = st([muz, zfnn, nn0], '3jca', PHZ)
    shz = st([phz, w.inst('progsh')], 'syl', SHZ)
    ssrpz = st([shz, w.inst('ssrp')], 'syl', '%s e. RR+' % SSF)
    ssre = st([ssrpz], 'rpred', '%s e. RR' % SSF)
    main = st([phz, w.inst('progmain')], 'syl',
              '( # ` %s ) <_ ( ( ( %s / %s ) + %s ) + %s )' % (TTX, NM, SSF, ETERM, ZF))
    ssge = st([phz, w.inst('progssge')], 'syl',
              '( ( %s / M ) x. ( log ` %s ) ) <_ %s' % (PM, ZF, SSF))
    # --- the main term, from btmain ----------------------------------------
    pmnn = st([mnn, w.inst('phicld')], 'syl', '%s e. NN' % PM)
    pmrp = st([pmnn, w.inst('nnrp')], 'syl', '%s e. RR+' % PM)
    pmre = st([pmrp], 'rpred', '%s e. RR' % PM)
    pmM = st([pmrp, mrp], 'rpdivcld', '( %s / M ) e. RR+' % PM)
    pmMre = st([pmM], 'rpred', '( %s / M ) e. RR' % PM)
    pmMge = st([pmM, w.inst('rpge0')], 'syl', '0 <_ ( %s / M )' % PM)
    k5rp = st([num.rp(w, K5)], 'a1i', '%s e. RR+' % K5)
    k5lg = st([k5rp, lgrp], 'rpmulcld', '( %s x. %s ) e. RR+' % (K5, LG))
    grp = st([pmM, k5lg], 'rpmulcld', '%s e. RR+' % G)
    gle = st([st([k5lg], 'rpred', '( %s x. %s ) e. RR' % (K5, LG)), logzre, pmMre, pmMge,
              lzlb], 'lemul2ad',
             '%s <_ ( ( %s / M ) x. ( log ` %s ) )' % (G, PM, ZF))
    gss = st([st([grp], 'rpred', '%s e. RR' % G),
              st([pmMre, logzre], 'remulcld',
                 '( ( %s / M ) x. ( log ` %s ) ) e. RR' % (PM, ZF)),
              ssre, gle, ssge], 'letrd', '%s <_ %s' % (G, SSF))
    bant = st([st([mrp, pmrp], 'jca', '( M e. RR+ /\\ %s e. RR+ )' % PM),
               st([lgrp, nrp], 'jca', '( %s e. RR+ /\\ N e. RR+ )' % LG),
               st([ssrpz, gss], 'jca', '( %s e. RR+ /\\ %s <_ %s )' % (SSF, G, SSF))],
              '3jca',
              '( ( M e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. RR+ /\\ N e. RR+ ) /\\ ( %s e. RR+ /\\ %s <_ %s ) )'
              % (PM, LG, SSF, G, SSF))
    mterm = st([bant, w.inst('btmain')], 'syl',
               '( %s / %s ) <_ ( %s x. %s )' % (NM, SSF, K14, WU))
    # --- the error term, from bterr -----------------------------------------
    err0 = st([hyl, w.inst('bterr')], 'syl',
              '( %s + %s ) <_ ( ( 1 / 5 ) x. ( ( exp ` %s ) / %s ) )' % (ETERM, ZF, LG, LG))
    efn = st([nmrp, w.inst('reeflog')], 'syl', '( exp ` %s ) = %s' % (LG, NM))
    err1 = st([err0, st([st([efn], 'oveq1d',
                            '( ( exp ` %s ) / %s ) = ( %s / %s )' % (LG, LG, NM, LG))],
                        'oveq2d',
                        '( ( 1 / 5 ) x. ( ( exp ` %s ) / %s ) ) = ( ( 1 / 5 ) x. ( %s / %s ) )'
                        % (LG, LG, NM, LG))], 'breqtrd',
              '( %s + %s ) <_ ( ( 1 / 5 ) x. ( %s / %s ) )' % (ETERM, ZF, NM, LG))
    nre2 = nre
    nmre = st([nmrp], 'rpred', '%s e. RR' % NM)
    wrp = st([nrp, st([pmrp, lgrp], 'rpmulcld', '( %s x. %s ) e. RR+' % (PM, LG))],
             'rpdivcld', '%s e. RR+' % WU)
    wre = st([wrp], 'rpred', '%s e. RR' % WU)
    dd = st([st([nre], 'recnd', 'N e. CC'),
             st([st([mre], 'recnd', 'M e. CC'), mne], 'jca', '( M e. CC /\\ M =/= 0 )'),
             st([st([lgre], 'recnd', '%s e. CC' % LG),
                 st([lgrp], 'rpne0d', '%s =/= 0' % LG)], 'jca',
                '( %s e. CC /\\ %s =/= 0 )' % (LG, LG)), w.inst('divdiv1')], 'syl3anc',
            '( %s / %s ) = ( N / ( M x. %s ) )' % (NM, LG, LG))
    pmleM = linarith(w, ANT, [st([muz, w.inst('phibnd')], 'syl', '%s <_ ( M - 1 )' % PM)],
                     '%s <_ M' % PM, leaves={PM: pmre, 'M': mre})
    lgge = st([lgrp, w.inst('rpge0')], 'syl', '0 <_ %s' % LG)
    pmlg = st([st([st([pmre, mre,
                       st([lgre, lgge], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (LG, LG))],
                      '3jca',
                      '( %s e. RR /\\ M e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (PM, LG, LG)),
                   pmleM], 'jca',
                  '( ( %s e. RR /\\ M e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s <_ M )'
                  % (PM, LG, LG, PM)), w.inst('lemul1a')], 'syl',
               '( %s x. %s ) <_ ( M x. %s )' % (PM, LG, LG))
    nge = st([nrp, w.inst('rpge0')], 'syl', '0 <_ N')
    ld = st([st([pmrp, lgrp], 'rpmulcld', '( %s x. %s ) e. RR+' % (PM, LG)),
             st([mrp, lgrp], 'rpmulcld', '( M x. %s ) e. RR+' % LG), nre, nge, pmlg],
            'lediv2ad', '( N / ( M x. %s ) ) <_ %s' % (LG, WU))
    nmlg = st([dd, ld], 'eqbrtrd', '( %s / %s ) <_ %s' % (NM, LG, WU))
    f5re = st([num.real(w, '( 1 / 5 )')], 'a1i', '( 1 / 5 ) e. RR')
    f5ge = st([num.fact(w, '( 1 / 5 )', 'ge0')], 'a1i', '0 <_ ( 1 / 5 )')
    nmlgre = st([nmre, lgre, st([lgrp], 'rpne0d', '%s =/= 0' % LG)], 'redivcld',
                '( %s / %s ) e. RR' % (NM, LG))
    n2n0 = st([num.nn0(w, 2)], 'a1i', '2 e. NN0')
    lz2re = st([st([zfrp, st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'rpexpcld',
                   '( %s ^ 2 ) e. RR+' % ZF)], 'relogcld', '%s e. RR' % LOGZ2)
    etre = st([st([zfre, n2n0], 'reexpcld', '( %s ^ 2 ) e. RR' % ZF),
               st([st([st([], '1red', '1 e. RR'), lz2re], 'readdcld',
                      '( 1 + %s ) e. RR' % LOGZ2), n2n0], 'reexpcld',
                  '( ( 1 + %s ) ^ 2 ) e. RR' % LOGZ2)], 'remulcld', '%s e. RR' % ETERM)
    eterm = st([st([etre, zfre], 'readdcld', '( %s + %s ) e. RR' % (ETERM, ZF)),
                st([f5re, nmlgre], 'remulcld',
                   '( ( 1 / 5 ) x. ( %s / %s ) ) e. RR' % (NM, LG)),
                st([f5re, wre], 'remulcld', '( ( 1 / 5 ) x. %s ) e. RR' % WU), err1,
                st([nmlgre, wre, f5re, f5ge, nmlg], 'lemul2ad',
                   '( ( 1 / 5 ) x. ( %s / %s ) ) <_ ( ( 1 / 5 ) x. %s )' % (NM, LG, WU))],
               'letrd', '( %s + %s ) <_ ( ( 1 / 5 ) x. %s )' % (ETERM, ZF, WU))
    # --- the final combination ----------------------------------------------
    httre = st([st([st([st([], 'fzfid', '( 0 ... N ) e. Fin'),
                        st([w.s([], 'ssrab2', '%s C_ ( 0 ... N )' % TTX)], 'a1i',
                           '%s C_ ( 0 ... N )' % TTX)], 'ssfid', '%s e. Fin' % TTX),
                    w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TTX)], 'nn0red',
               '( # ` %s ) e. RR' % TTX)
    nssre = st([nmre, ssre, st([ssrpz], 'rpne0d', '%s =/= 0' % SSF)], 'redivcld',
               '( %s / %s ) e. RR' % (NM, SSF))
    fin = linarith(w, ANT, [main, mterm, eterm],
                   '( # ` %s ) <_ ( 3 x. %s )' % (TTX, WU),
                   leaves={'( # ` %s )' % TTX: httre, '( %s / %s )' % (NM, SSF): nssre,
                           ETERM: etre, ZF: zfre, WU: wre},
                   atoms=[ETERM, '( %s / %s )' % (NM, SSF), WU, ZF])
    wid = st([st([num.cc_nat(w, 3)], 'a1i', '3 e. CC'), st([nre], 'recnd', 'N e. CC'),
              st([st([pmrp, lgrp], 'rpmulcld', '( %s x. %s ) e. RR+' % (PM, LG))], 'rpcnd',
                 '( %s x. %s ) e. CC' % (PM, LG)),
              st([st([pmrp, lgrp], 'rpmulcld', '( %s x. %s ) e. RR+' % (PM, LG))], 'rpne0d',
                 '( %s x. %s ) =/= 0' % (PM, LG))], 'divassd',
             '( ( 3 x. N ) / ( %s x. %s ) ) = ( 3 x. %s )' % (PM, LG, WU))
    w.qed([fin, st([wid], 'eqcomd',
                   '( 3 x. %s ) = ( ( 3 x. N ) / ( %s x. %s ) )' % (WU, PM, LG))], 'breqtrd',
          '( %s -> %s )' % (ANT, GOAL))
    return w


def main(names=None):
    fns = {'bruntit': bruntit}
    ok = True
    for nm in (names or ['bruntit']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
