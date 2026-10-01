"""Sortie v4b block 7c: the Selberg bounding sum of the progression sieve.

progsum   ( PH -> sum_ w e. CS ( 1 / w ) <_ SS )
progssge  ( PH -> ( ( ( phi ` M ) / M ) x. ( log ` Z ) ) <_ SS )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import P, PH, V, Y, T, DV, PF, RAD, GTV, GTR, SS, SH, mkst
from cl import lift

CS = '{ x e. ( 1 ... Z ) | ( x gcd M ) = 1 }'
DVP = DV(P)
RDW = RAD('w')
IFL = 'if ( l = %s , ( 1 / w ) , 0 )' % RDW
IFR = 'if ( %s = l , ( 1 / w ) , 0 )' % RDW
TERM = 'if ( ( l ^ 2 ) <_ %s , %s , 0 )' % (Y, GTV('l'))
LHS = 'sum_ w e. %s ( 1 / w )' % CS
ELCS = '( w e. %s <-> ( w e. ( 1 ... Z ) /\\ ( w gcd M ) = 1 ) )' % CS
ELDVP = '( l e. %s <-> ( l e. NN /\\ l || %s ) )' % (DVP, P)
PFW = PF('w', 'u')


def progsum():
    w = W('progsum', 'The Selberg bounding sum of the progression sieve dominates the '
                     'coprime harmonic sum up to the sifting level.')
    st = mkst(w, PH)
    phs = st([], 'id', PH)
    muz = st([], 'simp1', 'M e. ( ZZ>= ` 2 )')
    mnn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    znn = st([], 'simp2', 'Z e. NN')
    zre = st([znn], 'nnred', 'Z e. RR')
    zz = st([znn], 'nnzd', 'Z e. ZZ')
    pn = st([], 'progpnn',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )'
            % (P, P, P, T))
    pp = st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))
    pnn = st([pp], 'simpld', '%s e. NN' % P)
    psq = st([pp], 'simprd', '( mmu ` %s ) =/= 0' % P)
    sh = st([], 'progsh', SH)
    dvpfin = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    fzf = st([], 'fzfid', '( 1 ... Z ) e. Fin')
    csss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % CS)], 'a1i', '%s C_ ( 1 ... Z )' % CS)
    csfin = st([fzf, csss], 'ssfid', '%s e. Fin' % CS)
    elcs = w.s([w.s([w.s([], 'oveq1', '( x = w -> ( x gcd M ) = ( w gcd M ) )')], 'eqeq1d',
                    '( x = w -> ( ( x gcd M ) = 1 <-> ( w gcd M ) = 1 ) )')], 'elrab', ELCS)
    eldvp = w.s([w.s([], 'breq1', '( x = l -> ( x || %s <-> l || %s ) )' % (P, P))], 'elrab',
                ELDVP)
    # ---- RAD( w ) e. DVP for w in CS -------------------------------------
    AW = '( %s /\\ w e. %s )' % (PH, CS)
    sw = mkst(w, AW)
    LW = lambda s: lift(w, s, AW)
    wpair = sw([sw([], 'simpr', 'w e. %s' % CS), sw([elcs], 'a1i', ELCS)], 'mpbid',
               '( w e. ( 1 ... Z ) /\\ ( w gcd M ) = 1 )')
    wfz = sw([wpair], 'simpld', 'w e. ( 1 ... Z )')
    wcop = sw([wpair], 'simprd', '( w gcd M ) = 1')
    wnn = sw([wfz, w.inst('elfznn')], 'syl', 'w e. NN')
    wleZ = sw([wfz, w.inst('elfzle2')], 'syl', 'w <_ Z')
    rl = sw([wnn, w.inst('radlem')], 'syl',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s /\\ %s || w )'
            % (RDW, RDW, RDW, PFW, RDW))
    radnn = sw([sw([rl], 'simp1d', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (RDW, RDW))],
               'simpld', '%s e. NN' % RDW)
    raddvw = sw([rl], 'simp3d', '%s || w' % RDW)
    radle = sw([sw([sw([sw([radnn], 'nnzd', '%s e. ZZ' % RDW), wnn], 'jca',
                       '( %s e. ZZ /\\ w e. NN )' % RDW), w.inst('dvdsle')], 'syl',
                   '( %s || w -> %s <_ w )' % (RDW, RDW)), raddvw], 'mpd', '%s <_ w' % RDW)
    radleZ = sw([sw([radnn], 'nnred', '%s e. RR' % RDW), sw([wnn], 'nnred', 'w e. RR'),
                 LW(zre), radle, wleZ], 'letrd', '%s <_ Z' % RDW)
    # each prime of w divides P
    AJ = '( %s /\\ j e. %s )' % (AW, PFW)
    sj = mkst(w, AJ)
    LJ = lambda s: lift(w, s, AJ)
    elju = w.s([w.s([], 'breq1', '( u = j -> ( u || w <-> j || w ) )')], 'elrab',
               '( j e. %s <-> ( j e. Prime /\\ j || w ) )' % PFW)
    jpair = sj([sj([], 'simpr', 'j e. %s' % PFW),
                sj([elju], 'a1i', '( j e. %s <-> ( j e. Prime /\\ j || w ) )' % PFW)], 'mpbid',
               '( j e. Prime /\\ j || w )')
    jprm = sj([jpair], 'simpld', 'j e. Prime')
    jdvw = sj([jpair], 'simprd', 'j || w')
    jnn = sj([jprm, w.inst('prmnn')], 'syl', 'j e. NN')
    jle = sj([sj([sj([sj([jnn], 'nnzd', 'j e. ZZ'), LJ(wnn)], 'jca',
                     '( j e. ZZ /\\ w e. NN )'), w.inst('dvdsle')], 'syl',
                 '( j || w -> j <_ w )'), jdvw], 'mpd', 'j <_ w')
    jleZ = sj([sj([jnn], 'nnred', 'j e. RR'), sj([LJ(wnn)], 'nnred', 'w e. RR'),
               LJ(LW(zre)), jle, LJ(wleZ)], 'letrd', 'j <_ Z')
    dg = sj([sj([sj([jnn], 'nnzd', 'j e. ZZ'), sj([LJ(wnn)], 'nnzd', 'w e. ZZ'),
                 sj([LJ(LW(mnn))], 'nnzd', 'M e. ZZ')], '3jca',
                '( j e. ZZ /\\ w e. ZZ /\\ M e. ZZ )'), w.inst('dvdsgcd')], 'syl',
            '( ( j || w /\\ j || M ) -> j || ( w gcd M ) )')
    dg2 = sj([jdvw, dg], 'mpand', '( j || M -> j || ( w gcd M ) )')
    dg3 = sj([LJ(wcop)], 'breq2d', '( j || ( w gcd M ) <-> j || 1 )')
    dg4 = sj([dg2, dg3], 'sylibd', '( j || M -> j || 1 )')
    jn1 = sj([jprm, w.inst('nprmdvds1')], 'syl', '-. j || 1')
    jnM = sj([jn1, dg4], 'mtod', '-. j || M')
    jP = sj([sj([LJ(LW(phs)), jprm, w.inst('progpel')], 'syl2anc',
                '( j || %s <-> ( j <_ Z /\\ -. j || M ) )' % P),
             sj([jleZ, jnM], 'jca', '( j <_ Z /\\ -. j || M )')], 'mpbird', 'j || %s' % P)
    jral = sw([jP], 'ralrimiva', 'A. j e. %s j || %s' % (PFW, P))
    pffin = sw([sw([w.s([w.s([], 'breq1', '( q = u -> ( q || w <-> u || w ) )')], 'cbvrabv',
                        '{ q e. Prime | q || w } = %s' % PFW)], 'a1i',
                   '{ q e. Prime | q || w } = %s' % PFW),
                sw([wnn, w.inst('pffinq')], 'syl', '{ q e. Prime | q || w } e. Fin')],
               'eqeltrrd', '%s e. Fin' % PFW)
    pfss = sw([w.s([], 'ssrab2', '%s C_ Prime' % PFW)], 'a1i', '%s C_ Prime' % PFW)
    exd = sw([sw([pffin, pfss], 'jca', '( %s e. Fin /\\ %s C_ Prime )' % (PFW, PFW)),
              w.inst('extrwprmdvds')], 'syl',
             '( ( %s e. ZZ /\\ A. j e. %s j || %s ) -> prod_ j e. %s j || %s )'
             % (P, PFW, P, PFW, P))
    dv0 = sw([exd, sw([sw([LW(pnn)], 'nnzd', '%s e. ZZ' % P), jral], 'jca',
                      '( %s e. ZZ /\\ A. j e. %s j || %s )' % (P, PFW, P))], 'mpd',
             'prod_ j e. %s j || %s' % (PFW, P))
    cbj = sw([w.s([w.s([], 'id', '( j = e -> j = e )')], 'cbvprodv',
                  'prod_ j e. %s j = %s' % (PFW, RDW))], 'a1i',
             'prod_ j e. %s j = %s' % (PFW, RDW))
    radP = sw([cbj, dv0], 'eqbrtrrd', '%s || %s' % (RDW, P))
    eldr = w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (RDW, P, RDW, P))],
               'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (RDW, DVP, RDW, RDW, P))
    raddvp = sw([sw([eldr], 'a1i',
                    '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (RDW, DVP, RDW, RDW, P)),
                 sw([radnn, radP], 'jca', '( %s e. NN /\\ %s || %s )' % (RDW, RDW, P))],
                'mpbird', '%s e. %s' % (RDW, DVP))
    # ---- the fibre decomposition -----------------------------------------
    wrec = sw([sw([sw([wnn, w.inst('nnrp')], 'syl', 'w e. RR+')], 'rpreccld',
                  '( 1 / w ) e. RR+')], 'rpcnd', '( 1 / w ) e. CC')
    site = sw([w.s([], 'eqidd', '( l = %s -> ( 1 / w ) = ( 1 / w ) )' % RDW),
               LW(dvpfin), raddvp, wrec], 'sumite',
              'sum_ l e. %s %s = ( 1 / w )' % (DVP, IFL))
    dec = st([sw([site], 'eqcomd', '( 1 / w ) = sum_ l e. %s %s' % (DVP, IFL))], 'sumeq2dv',
             '%s = sum_ w e. %s sum_ l e. %s %s' % (LHS, CS, DVP, IFL))
    # the body closure for fsumcom
    AWL = '( %s /\\ ( w e. %s /\\ l e. %s ) )' % (PH, CS, DVP)
    swl = mkst(w, AWL)
    wl1 = swl([swl([], 'simprl', 'w e. %s' % CS),
               swl([elcs], 'a1i', ELCS)], 'mpbid',
              '( w e. ( 1 ... Z ) /\\ ( w gcd M ) = 1 )')
    wlrec = swl([swl([swl([swl([swl([wl1], 'simpld', 'w e. ( 1 ... Z )'),
                                w.inst('elfznn')], 'syl', 'w e. NN'), w.inst('nnrp')], 'syl',
                          'w e. RR+')], 'rpreccld', '( 1 / w ) e. RR+')], 'rpcnd',
                '( 1 / w ) e. CC')
    wlif = swl([wlrec, swl([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFL)
    com = st([csfin, dvpfin, wlif], 'fsumcom',
             'sum_ w e. %s sum_ l e. %s %s = sum_ l e. %s sum_ w e. %s %s'
             % (CS, DVP, IFL, DVP, CS, IFL))
    # ---- the term comparison ---------------------------------------------
    AL = '( %s /\\ l e. %s )' % (PH, DVP)
    sl = mkst(w, AL)
    LL = lambda x: lift(w, x, AL)
    lpair = sl([sl([], 'simpr', 'l e. %s' % DVP), sl([eldvp], 'a1i', ELDVP)], 'mpbid',
               '( l e. NN /\\ l || %s )' % P)
    lnn = sl([lpair], 'simpld', 'l e. NN')
    ldvP = sl([lpair], 'simprd', 'l || %s' % P)
    lre = sl([lnn], 'nnred', 'l e. RR')
    lsq = sl([sl([LL(pnn), lnn, ldvP, w.inst('dvdssqf')], 'syl3anc',
                 '( ( mmu ` %s ) =/= 0 -> ( mmu ` l ) =/= 0 )' % P), LL(psq)], 'mpd',
             '( mmu ` l ) =/= 0')
    gtv = sl([lnn, lsq, w.inst('progvgt')], 'syl2anc', '%s = %s' % (GTV('l'), GTR('l')))
    ssv = sl([LL(sh), sl([lnn, ldvP], 'jca',
                 '( l e. NN /\\ l || %s )' % P), w.inst('ssterm')], 'syl2anc',
             '( %s e. RR /\\ 0 <_ %s )' % (TERM, TERM))
    termre = sl([ssv], 'simpld', '%s e. RR' % TERM)
    # the inner body: l = RAD( w ) rewritten as RAD( w ) = l
    ALW = '( %s /\\ w e. %s )' % (AL, CS)
    slw = mkst(w, ALW)
    LLW = lambda x: lift(w, x, ALW)
    ifc = slw([slw([w.s([], 'eqcom', '( l = %s <-> %s = l )' % (RDW, RDW))], 'a1i',
                   '( l = %s <-> %s = l )' % (RDW, RDW))], 'ifbid', '%s = %s' % (IFL, IFR))
    bodyeq = sl([ifc], 'sumeq2dv',
                'sum_ w e. %s %s = sum_ w e. %s %s' % (CS, IFL, CS, IFR))
    lwp = slw([slw([], 'simpr', 'w e. %s' % CS), slw([elcs], 'a1i', ELCS)], 'mpbid',
              '( w e. ( 1 ... Z ) /\\ ( w gcd M ) = 1 )')
    lwrp = slw([slw([slw([slw([lwp], 'simpld', 'w e. ( 1 ... Z )'), w.inst('elfznn')], 'syl',
                         'w e. NN'), w.inst('nnrp')], 'syl', 'w e. RR+')], 'rpreccld',
               '( 1 / w ) e. RR+')
    lwifre = slw([slw([lwrp], 'rpred', '( 1 / w ) e. RR'), slw([], '0red', '0 e. RR')],
                 'ifcld', '%s e. RR' % IFL)
    sumre = sl([LL(csfin), lwifre], 'fsumrecl', 'sum_ w e. %s %s e. RR' % (CS, IFL))
    # the body over the whole range ( 1 ... Z )
    AZ = '( %s /\\ w e. ( 1 ... Z ) )' % AL
    sz = mkst(w, AZ)
    zrp = sz([sz([sz([sz([], 'simpr', 'w e. ( 1 ... Z )'), w.inst('elfznn')], 'syl',
                     'w e. NN'), w.inst('nnrp')], 'syl', 'w e. RR+')], 'rpreccld',
             '( 1 / w ) e. RR+')
    zre2 = sz([sz([zrp], 'rpred', '( 1 / w ) e. RR'), sz([], '0red', '0 e. RR')], 'ifcld',
              '%s e. RR' % IFR)
    zrec = sz([zrp], 'rpred', '( 1 / w ) e. RR')
    zpos = sz([sz([], '0red', '0 e. RR'), zrec, sz([zrp, w.inst('rpgt0')], 'syl',
                                                   '0 < ( 1 / w )')], 'ltled',
              '0 <_ ( 1 / w )')
    AZT = '( %s /\\ %s = l )' % (AZ, RDW)
    szt = mkst(w, AZT)
    zt = szt([lift(w, zpos, AZT),
              szt([szt([], 'simpr', '%s = l' % RDW)], 'iftrued', '%s = ( 1 / w )' % IFR)],
             'breqtrrd', '0 <_ %s' % IFR)
    AZF = '( %s /\\ -. %s = l )' % (AZ, RDW)
    szf = mkst(w, AZF)
    zf = szf([szf([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0'),
              szf([szf([], 'simpr', '-. %s = l' % RDW)], 'iffalsed', '%s = 0' % IFR)],
             'breqtrrd', '0 <_ %s' % IFR)
    zge = w.s([zt, zf], 'pm2.61dan', '( %s -> 0 <_ %s )' % (AZ, IFR))
    zsumre = sl([LL(fzf), zre2], 'fsumrecl', 'sum_ w e. ( 1 ... Z ) %s e. RR' % IFR)
    csre = sl([LL(csfin), slw([slw([lwrp], 'rpred', '( 1 / w ) e. RR'),
                              slw([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFR)],
              'fsumrecl', 'sum_ w e. %s %s e. RR' % (CS, IFR))
    gtrre = sl([sl([LL(sh), sl([lnn, ldvP], 'jca',
                       '( l e. NN /\\ l || %s )' % P), w.inst('gtrp')], 'syl2anc',
                   '%s e. RR+' % GTV('l'))], 'rpred', '%s e. RR' % GTV('l'))
    gtrre2 = sl([gtv, gtrre], 'eqeltrrd', '%s e. RR' % GTR('l'))
    # ---- case l <_ Z -----------------------------------------------------
    ALT = '( %s /\\ l <_ Z )' % AL
    slt = mkst(w, ALT)
    LT = lambda x: lift(w, x, ALT)
    lge0 = sl([sl([], '0red', '0 e. RR'), lre,
               sl([sl([lnn, w.inst('nnrp')], 'syl', 'l e. RR+'), w.inst('rpgt0')], 'syl',
                  '0 < l')], 'ltled', '0 <_ l')
    zge0 = sl([sl([], '0red', '0 e. RR'), LL(zre),
               sl([sl([LL(znn), w.inst('nnrp')], 'syl', 'Z e. RR+'), w.inst('rpgt0')],
                  'syl', '0 < Z')], 'ltled', '0 <_ Z')
    sqb = slt([slt([LT(lre), LT(lge0)], 'jca', '( l e. RR /\\ 0 <_ l )'),
               slt([LT(LL(zre)), LT(zge0)], 'jca', '( Z e. RR /\\ 0 <_ Z )'),
               w.inst('le2sq')], 'syl2anc', '( l <_ Z <-> ( l ^ 2 ) <_ %s )' % Y)
    sq = slt([sqb, slt([], 'simpr', 'l <_ Z')], 'mpbid', '( l ^ 2 ) <_ %s' % Y)
    termT = slt([sq], 'iftrued', '%s = %s' % (TERM, GTV('l')))
    lessT = LT(sl([LL(fzf), zre2, zge, LL(csss)], 'fsumless',
                   'sum_ w e. %s %s <_ sum_ w e. ( 1 ... Z ) %s' % (CS, IFR, IFR)))
    fibT = slt([slt([LT(LL(znn)), slt([LT(lnn), LT(lsq)], 'jca',
                                      '( l e. NN /\\ ( mmu ` l ) =/= 0 )')], 'jca',
                    '( Z e. NN /\\ ( l e. NN /\\ ( mmu ` l ) =/= 0 ) )'), w.inst('progfib')],
               'syl', 'sum_ w e. ( 1 ... Z ) %s <_ %s' % (IFR, GTR('l')))
    chT1 = slt([LT(csre), LT(zsumre), LT(gtrre2), lessT, fibT], 'letrd',
               'sum_ w e. %s %s <_ %s' % (CS, IFR, GTR('l')))
    chT2 = slt([chT1, LT(sl([gtv], 'eqcomd', '%s = %s' % (GTR('l'), GTV('l'))))], 'breqtrd',
               'sum_ w e. %s %s <_ %s' % (CS, IFR, GTV('l')))
    chT3 = slt([chT2, termT], 'breqtrrd', 'sum_ w e. %s %s <_ %s' % (CS, IFR, TERM))
    caseT = slt([LT(bodyeq), chT3], 'eqbrtrd', 'sum_ w e. %s %s <_ %s' % (CS, IFL, TERM))
    # ---- case -. l <_ Z --------------------------------------------------
    ALF = '( %s /\\ -. l <_ Z )' % AL
    slf = mkst(w, ALF)
    LFF = lambda x: lift(w, x, ALF)
    zlt = slf([slf([LFF(LL(zre)), LFF(lre), w.inst('ltnle')], 'syl2anc',
                   '( Z < l <-> -. l <_ Z )'), slf([], 'simpr', '-. l <_ Z')], 'mpbird',
              'Z < l')
    lsqre = slf([LFF(lre), slf([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
                '( l ^ 2 ) e. RR')
    zsqre = slf([LFF(LL(zre)), slf([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')],
                'reexpcld', '%s e. RR' % Y)
    sqlt = slf([slf([slf([LFF(LL(zre)), LFF(zge0)], 'jca', '( Z e. RR /\\ 0 <_ Z )'),
                     slf([LFF(lre), LFF(lge0)], 'jca', '( l e. RR /\\ 0 <_ l )'),
                     w.inst('lt2sq')], 'syl2anc', '( Z < l <-> %s < ( l ^ 2 ) )' % Y),
                zlt], 'mpbid', '%s < ( l ^ 2 )' % Y)
    nsq = slf([slf([zsqre, lsqre, w.inst('ltnle')], 'syl2anc',
                   '( %s < ( l ^ 2 ) <-> -. ( l ^ 2 ) <_ %s )' % (Y, Y)), sqlt], 'mpbid',
              '-. ( l ^ 2 ) <_ %s' % Y)
    termF = slf([nsq], 'iffalsed', '%s = 0' % TERM)
    # the fibre is empty
    ALFW = '( %s /\\ w e. %s )' % (ALF, CS)
    sfw = mkst(w, ALFW)
    LFW = lambda x: lift(w, x, ALFW)
    fwp = sfw([sfw([], 'simpr', 'w e. %s' % CS), sfw([elcs], 'a1i', ELCS)], 'mpbid',
              '( w e. ( 1 ... Z ) /\\ ( w gcd M ) = 1 )')
    fwfz = sfw([fwp], 'simpld', 'w e. ( 1 ... Z )')
    fwnn = sfw([fwfz, w.inst('elfznn')], 'syl', 'w e. NN')
    frl = sfw([fwnn, w.inst('radlem')], 'syl',
              '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s /\\ %s || w )'
              % (RDW, RDW, RDW, PFW, RDW))
    frnn = sfw([sfw([frl], 'simp1d', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (RDW, RDW))],
               'simpld', '%s e. NN' % RDW)
    frdv = sfw([frl], 'simp3d', '%s || w' % RDW)
    frle = sfw([sfw([sfw([sfw([frnn], 'nnzd', '%s e. ZZ' % RDW), fwnn], 'jca',
                         '( %s e. ZZ /\\ w e. NN )' % RDW), w.inst('dvdsle')], 'syl',
                    '( %s || w -> %s <_ w )' % (RDW, RDW)), frdv], 'mpd', '%s <_ w' % RDW)
    frleZ = sfw([sfw([frnn], 'nnred', '%s e. RR' % RDW), sfw([fwnn], 'nnred', 'w e. RR'),
                 LFW(LFF(LL(zre))), frle,
                 sfw([fwfz, w.inst('elfzle2')], 'syl', 'w <_ Z')], 'letrd', '%s <_ Z' % RDW)
    frlt = sfw([sfw([frnn], 'nnred', '%s e. RR' % RDW), LFW(LFF(LL(zre))), LFW(LFF(lre)),
                frleZ, LFW(zlt)], 'lelttrd', '%s < l' % RDW)
    frne = sfw([sfw([sfw([frnn], 'nnred', '%s e. RR' % RDW), frlt], 'ltned',
                    '%s =/= l' % RDW)], 'necomd', 'l =/= %s' % RDW)
    frnq = sfw([frne], 'neneqd', '-. l = %s' % RDW)
    frz = sfw([frnq], 'iffalsed', '%s = 0' % IFL)
    sum0 = slf([slf([frz], 'sumeq2dv',
                    'sum_ w e. %s %s = sum_ w e. %s 0' % (CS, IFL, CS)),
                slf([slf([LFF(LL(csfin))], 'olcd',
                         '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (CS, CS)),
                     w.inst('sumz')], 'syl', 'sum_ w e. %s 0 = 0' % CS)], 'eqtrd',
               'sum_ w e. %s %s = 0' % (CS, IFL))
    caseF = slf([sum0, slf([slf([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0'), termF],
                           'breqtrrd', '0 <_ %s' % TERM)], 'eqbrtrd',
                'sum_ w e. %s %s <_ %s' % (CS, IFL, TERM))
    cmp = w.s([caseT, caseF], 'pm2.61dan',
              '( %s -> sum_ w e. %s %s <_ %s )' % (AL, CS, IFL, TERM))
    le = st([dvpfin, sumre, termre, cmp], 'fsumle',
            'sum_ l e. %s sum_ w e. %s %s <_ %s' % (DVP, CS, IFL, SS))
    w.qed([st([dec, com], 'eqtrd',
              '%s = sum_ l e. %s sum_ w e. %s %s' % (LHS, DVP, CS, IFL)), le], 'eqbrtrd',
          '( %s -> %s <_ %s )' % (PH, LHS, SS))
    return w


def progssge():
    w = W('progssge', 'The Selberg bounding sum of the progression sieve is at least '
                      '( phi ( M ) / M ) log Z.')
    st = mkst(w, PH)
    muz = st([], 'simp1', 'M e. ( ZZ>= ` 2 )')
    mnn = st([muz, w.inst('eluz2nn')], 'syl', 'M e. NN')
    znn = st([], 'simp2', 'Z e. NN')
    sh = st([], 'progsh', SH)
    ssre = st([st([sh, w.inst('ssrp')], 'syl', '%s e. RR+' % SS)], 'rpred', '%s e. RR' % SS)
    coph = st([mnn, znn, w.inst('cophrm')], 'syl2anc',
              '( ( ( phi ` M ) / M ) x. ( log ` Z ) ) <_ sum_ j e. %s ( 1 / j )' % CS)
    cbs = st([w.s([w.s([], 'oveq2', '( j = w -> ( 1 / j ) = ( 1 / w ) )')], 'cbvsumv',
                  'sum_ j e. %s ( 1 / j ) = %s' % (CS, LHS))], 'a1i',
             'sum_ j e. %s ( 1 / j ) = %s' % (CS, LHS))
    coph2 = st([coph, cbs], 'breqtrd', '( ( ( phi ` M ) / M ) x. ( log ` Z ) ) <_ %s' % LHS)
    sm = st([], 'progsum', '%s <_ %s' % (LHS, SS))
    fzf = st([], 'fzfid', '( 1 ... Z ) e. Fin')
    csss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % CS)], 'a1i', '%s C_ ( 1 ... Z )' % CS)
    csfin = st([fzf, csss], 'ssfid', '%s e. Fin' % CS)
    AW2 = '( %s /\\ w e. %s )' % (PH, CS)
    sw2 = mkst(w, AW2)
    wre = sw2([sw2([sw2([sw2([sw2([], 'simpr', 'w e. %s' % CS), w.inst('elrabi')], 'syl',
                             'w e. ( 1 ... Z )'), w.inst('elfznn')], 'syl', 'w e. NN'),
                    w.inst('nnrp')], 'syl', 'w e. RR+')], 'rpreccld', '( 1 / w ) e. RR+')
    lhsre = st([csfin, sw2([wre], 'rpred', '( 1 / w ) e. RR')], 'fsumrecl', '%s e. RR' % LHS)
    phre = st([st([st([mnn, w.inst('phicld')], 'syl', '( phi ` M ) e. NN')], 'nnred',
                  '( phi ` M ) e. RR'), st([mnn], 'nnred', 'M e. RR'),
               st([mnn], 'nnne0d', 'M =/= 0')], 'redivcld', '( ( phi ` M ) / M ) e. RR')
    logre = st([st([znn, w.inst('nnrp')], 'syl', 'Z e. RR+')], 'relogcld',
               '( log ` Z ) e. RR')
    w.qed([st([phre, logre], 'remulcld',
              '( ( ( phi ` M ) / M ) x. ( log ` Z ) ) e. RR'), lhsre, ssre, coph2, sm],
          'letrd',
          '( %s -> ( ( ( phi ` M ) / M ) x. ( log ` Z ) ) <_ %s )' % (PH, SS))
    return w


def main(names=None):
    fns = {'progsum': progsum, 'progssge': progssge}
    ok = True
    for nm in (names or ['progsum', 'progssge']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
