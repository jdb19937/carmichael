"""Sortie A4c, batch 8: completeness of the DP table across one step
(Lean: AlgExtract.tblComplete_dpStep)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DS = '( ( L DpStep P ) ` T )'
DS1 = '( 1st ` %s )' % DS
T3 = '( L e. NN /\\ P e. NN0 /\\ T e. Tbl )'
CSE = '( <" P "> ++ E )'
PU = 'prod_ q e. u q'
SD = '( u \\ { P } )'
PSD = 'prod_ q e. %s q' % SD
MU = '( %s mod L )' % PU
MSD = '( %s mod L )' % PSD

if not only or 'tblcmps' in only:
    w = W('tblcmps', 'A DP step preserves completeness of the table (Lean: tblComplete_dpStep).')
    TCE = TC('L', 'T', 'E')
    A = '( %s /\\ E e. Word NN0 /\\ %s )' % (T3, TCE)
    ll = w.s([w.s([], 'simp1', '( %s -> %s )' % (A, T3))], 'simp1d', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([], 'simp1', '( %s -> %s )' % (A, T3))], 'simp2d', '( %s -> P e. NN0 )' % A)
    tt = w.s([w.s([], 'simp1', '( %s -> %s )' % (A, T3))], 'simp3d', '( %s -> T e. Tbl )' % A)
    dpo = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A), tt], 'jca', '( %s -> %s )' % (A, DPO))
    ee = w.s([], 'simp2', '( %s -> E e. Word NN0 )' % A)
    tc = w.s([], 'simp3', '( %s -> %s )' % (A, TCE))
    s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A)
    cse = w.s([s1, ee, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (A, CSE))
    rncs = w.s([pp, ee, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran E ) )' % (A, CSE))
    B = '( %s /\\ u e. ~P ran %s )' % (A, CSE)
    U = '( %s /\\ u =/= (/) )' % B
    up = lambda st, f: w.s([w.s([st], 'adantr', '( %s -> %s )' % (B, f))], 'adantr', '( %s -> %s )' % (U, f))
    llU = up(ll, 'L e. NN'); ppU = up(pp, 'P e. NN0'); ttU = up(tt, 'T e. Tbl'); dpoU = up(dpo, DPO)
    eeU = up(ee, 'E e. Word NN0'); tcU = up(tc, TCE); cseU = up(cse, '%s e. Word NN0' % CSE)
    rncsU = up(rncs, 'ran %s = ( { P } u. ran E )' % CSE)
    uu = w.s([w.s([], 'simpr', '( %s -> u e. ~P ran %s )' % (B, CSE))], 'adantr', '( %s -> u e. ~P ran %s )' % (U, CSE))
    unz = w.s([], 'simpr', '( %s -> u =/= (/) )' % U)
    fs = w.s([w.s([cseU, uu], 'jca', '( %s -> ( %s e. Word NN0 /\\ u e. ~P ran %s ) )' % (U, CSE, CSE)), w.inst('tcsfin')], 'syl',
             '( %s -> ( u e. Fin /\\ u C_ NN0 ) )' % U)
    ufin = w.s([fs], 'simpld', '( %s -> u e. Fin )' % U)
    un0s = w.s([fs], 'simprd', '( %s -> u C_ NN0 )' % U)
    uss = w.s([w.s([uu, w.inst('elpwi')], 'syl', '( %s -> u C_ ran %s )' % (U, CSE)), rncsU], 'sseqtrd',
              '( %s -> u C_ ( { P } u. ran E ) )' % U)
    #   ( u \ { P } ) C_ ran E, the chain used in both cases
    sdss = w.s([w.s([uss, w.inst('ssdif')], 'syl', '( %s -> %s C_ ( ( { P } u. ran E ) \\ { P } ) )' % (U, SD)),
                w.s([w.s([], 'unsndif', '( ( { P } u. ran E ) \\ { P } ) C_ ran E')], 'a1i',
                    '( %s -> ( ( { P } u. ran E ) \\ { P } ) C_ ran E )' % U)], 'sstrd',
               '( %s -> %s C_ ran E )' % (U, SD))
    uex = w.s([uu], 'elexd', '( %s -> u e. _V )' % U)
    sdex = w.s([uex, w.inst('difexg')], 'syl', '( %s -> %s e. _V )' % (U, SD))
    sdpw = w.s([sdss, w.s([sdex, w.inst('elpwg')], 'syl', '( %s -> ( %s e. ~P ran E <-> %s C_ ran E ) )' % (U, SD, SD))],
               'mpbird', '( %s -> %s e. ~P ran E )' % (U, SD))
    GOAL = '( %s ` %s ) =/= %s' % (DS1, MU, NONE)
    # ================================================= case P e. u
    C1 = '( %s /\\ P e. u )' % U
    c1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C1, f))
    pu = w.s([], 'simpr', '( %s -> P e. u )' % C1)
    spl = w.s([w.s([c1(ufin, 'u e. Fin'), c1(un0s, 'u C_ NN0'), pu], '3jca',
                   '( %s -> ( u e. Fin /\\ u C_ NN0 /\\ P e. u ) )' % C1), w.inst('prodsplitp')], 'syl',
              '( %s -> %s = ( P x. %s ) )' % (C1, PU, PSD))
    #  --- sub-case ( u \ { P } ) = (/)
    E1 = '( %s /\\ %s = (/) )' % (C1, SD)
    e1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E1, f))
    sdz = w.s([], 'simpr', '( %s -> %s = (/) )' % (E1, SD))
    p1 = w.s([w.s([sdz], 'prodeq1d', '( %s -> %s = prod_ q e. (/) q )' % (E1, PSD)),
              w.s([w.s([], 'prod0', 'prod_ q e. (/) q = 1')], 'a1i', '( %s -> prod_ q e. (/) q = 1 )' % E1)], 'eqtrd',
             '( %s -> %s = 1 )' % (E1, PSD))
    pe = w.s([w.s([e1(spl, '%s = ( P x. %s )' % (PU, PSD)),
                   w.s([p1], 'oveq2d', '( %s -> ( P x. %s ) = ( P x. 1 ) )' % (E1, PSD))], 'eqtrd',
                  '( %s -> %s = ( P x. 1 ) )' % (E1, PU)),
              w.s([w.s([e1(c1(ppU, 'P e. NN0'), 'P e. NN0')], 'nn0cnd', '( %s -> P e. CC )' % E1)], 'mulridd',
                  '( %s -> ( P x. 1 ) = P )' % E1)], 'eqtrd', '( %s -> %s = P )' % (E1, PU))
    slf = w.s([e1(c1(dpoU, DPO), DPO), w.inst('dpstepself')], 'syl', '( %s -> ( %s ` ( P mod L ) ) =/= %s )' % (E1, DS1, NONE))
    g1 = w.s([w.s([w.s([pe], 'oveq1d', '( %s -> %s = ( P mod L ) )' % (E1, MU))], 'fveq2d',
                  '( %s -> ( %s ` %s ) = ( %s ` ( P mod L ) ) )' % (E1, DS1, MU, DS1)), slf], 'eqnetrd',
             '( %s -> %s )' % (E1, GOAL))
    #  --- sub-case ( u \ { P } ) =/= (/)
    E2 = '( %s /\\ -. %s = (/) )' % (C1, SD)
    e2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E2, f))
    sdnz = w.s([w.s([], 'simpr', '( %s -> -. %s = (/) )' % (E2, SD)), w.inst('neqned')], 'syl',
               '( %s -> %s =/= (/) )' % (E2, SD))
    ihb, _ = inst1(w, E2, e2(c1(tcU, TCE), TCE), 's', '~P ran E',
                   '( s =/= (/) -> ( T ` ( prod_ q e. s q mod L ) ) =/= %s )' % NONE, SD,
                   e2(c1(sdpw, '%s e. ~P ran E' % SD), '%s e. ~P ran E' % SD))
    tnn = w.s([ihb, sdnz], 'mpd', '( %s -> ( T ` %s ) =/= %s )' % (E2, MSD, NONE))
    tm = w.s([w.s([w.s([e2(c1(llU, 'L e. NN'), 'L e. NN'), e2(c1(eeU, 'E e. Word NN0'), 'E e. Word NN0')], 'jca',
                       '( %s -> ( L e. NN /\\ E e. Word NN0 ) )' % E2),
                   e2(c1(sdpw, '%s e. ~P ran E' % SD), '%s e. ~P ran E' % SD)], 'jca',
                  '( %s -> ( ( L e. NN /\\ E e. Word NN0 ) /\\ %s e. ~P ran E ) )' % (E2, SD)), w.inst('tcsmod')], 'syl',
              '( %s -> ( %s e. NN0 /\\ %s < L ) )' % (E2, MSD, MSD))
    hit = w.s([w.s([e2(c1(dpoU, DPO), DPO),
                    w.s([w.s([tm], 'simpld', '( %s -> %s e. NN0 )' % (E2, MSD)),
                         w.s([tm], 'simprd', '( %s -> %s < L )' % (E2, MSD)), tnn], '3jca',
                        '( %s -> ( %s e. NN0 /\\ %s < L /\\ ( T ` %s ) =/= %s ) )' % (E2, MSD, MSD, MSD, NONE))], 'jca',
                   '( %s -> ( %s /\\ ( %s e. NN0 /\\ %s < L /\\ ( T ` %s ) =/= %s ) ) )' % (E2, DPO, MSD, MSD, MSD, NONE)),
               w.inst('dpstephit')], 'syl', '( %s -> ( %s ` ( ( %s x. P ) mod L ) ) =/= %s )' % (E2, DS1, MSD, NONE))
    psdn = w.s([w.s([e2(c1(eeU, 'E e. Word NN0'), 'E e. Word NN0'),
                     e2(c1(sdpw, '%s e. ~P ran E' % SD), '%s e. ~P ran E' % SD)], 'jca',
                    '( %s -> ( E e. Word NN0 /\\ %s e. ~P ran E ) )' % (E2, SD)), w.inst('tcsprod')], 'syl',
               '( %s -> %s e. NN0 )' % (E2, PSD))
    mmr = w.s([w.s([psdn, e2(c1(ppU, 'P e. NN0'), 'P e. NN0'), e2(c1(llU, 'L e. NN'), 'L e. NN')], '3jca',
                   '( %s -> ( %s e. NN0 /\\ P e. NN0 /\\ L e. NN ) )' % (E2, PSD)), w.inst('modmulr')], 'syl',
              '( %s -> ( ( %s x. P ) mod L ) = ( ( %s x. P ) mod L ) )' % (E2, MSD, PSD))
    comm = w.s([w.s([e2(c1(ppU, 'P e. NN0'), 'P e. NN0')], 'nn0cnd', '( %s -> P e. CC )' % E2),
                w.s([psdn], 'nn0cnd', '( %s -> %s e. CC )' % (E2, PSD))], 'mulcomd',
               '( %s -> ( P x. %s ) = ( %s x. P ) )' % (E2, PSD, PSD))
    peq = w.s([e2(spl, '%s = ( P x. %s )' % (PU, PSD)), comm], 'eqtrd', '( %s -> %s = ( %s x. P ) )' % (E2, PU, PSD))
    meq = w.s([w.s([peq], 'oveq1d', '( %s -> %s = ( ( %s x. P ) mod L ) )' % (E2, MU, PSD)),
               w.s([mmr], 'eqcomd', '( %s -> ( ( %s x. P ) mod L ) = ( ( %s x. P ) mod L ) )' % (E2, PSD, MSD))], 'eqtrd',
              '( %s -> %s = ( ( %s x. P ) mod L ) )' % (E2, MU, MSD))
    g2 = w.s([w.s([meq], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` ( ( %s x. P ) mod L ) ) )' % (E2, DS1, MU, DS1, MSD)), hit],
             'eqnetrd', '( %s -> %s )' % (E2, GOAL))
    gg1 = w.s([g1, g2], 'pm2.61dan', '( %s -> %s )' % (C1, GOAL))
    # ================================================= case -. P e. u
    C2 = '( %s /\\ -. P e. u )' % U
    c2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C2, f))
    dsn = w.s([w.s([], 'simpr', '( %s -> -. P e. u )' % C2), w.inst('difsn')], 'syl', '( %s -> %s = u )' % (C2, SD))
    upw = w.s([w.s([dsn], 'eqcomd', '( %s -> u = %s )' % (C2, SD)),
               c2(sdpw, '%s e. ~P ran E' % SD)], 'eqeltrd', '( %s -> u e. ~P ran E )' % C2)
    ihb2, _ = inst1(w, C2, c2(tcU, TCE), 's', '~P ran E',
                    '( s =/= (/) -> ( T ` ( prod_ q e. s q mod L ) ) =/= %s )' % NONE, 'u', upw)
    tnn2 = w.s([ihb2, c2(unz, 'u =/= (/)')], 'mpd', '( %s -> ( T ` %s ) =/= %s )' % (C2, MU, NONE))
    tm2 = w.s([w.s([w.s([c2(llU, 'L e. NN'), c2(eeU, 'E e. Word NN0')], 'jca',
                        '( %s -> ( L e. NN /\\ E e. Word NN0 ) )' % C2), upw], 'jca',
                   '( %s -> ( ( L e. NN /\\ E e. Word NN0 ) /\\ u e. ~P ran E ) )' % C2), w.inst('tcsmod')], 'syl',
              '( %s -> ( %s e. NN0 /\\ %s < L ) )' % (C2, MU, MU))
    gg2 = w.s([w.s([c2(dpoU, DPO), w.s([w.s([tm2], 'simpld', '( %s -> %s e. NN0 )' % (C2, MU)), tnn2], 'jca',
                                       '( %s -> ( %s e. NN0 /\\ ( T ` %s ) =/= %s ) )' % (C2, MU, MU, NONE))], 'jca',
                   '( %s -> ( %s /\\ ( %s e. NN0 /\\ ( T ` %s ) =/= %s ) ) )' % (C2, DPO, MU, MU, NONE)),
               w.inst('dpstepnn')], 'syl', '( %s -> %s )' % (C2, GOAL))
    fin = w.s([gg1, gg2], 'pm2.61dan', '( %s -> %s )' % (U, GOAL))
    imp = w.s([fin], 'ex', '( %s -> ( u =/= (/) -> %s ) )' % (B, GOAL))
    gen = w.s([imp], 'ralrimiva', '( %s -> %s )' % (A, TC('L', DS1, CSE, 'u')))
    body = TC('L', DS1, CSE, 's')
    cv = ralconv(w, '~P ran %s' % CSE, 's', 'u', body[len('A. s e. ~P ran %s ' % CSE):])
    w.qed([gen, w.s([cv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, TC('L', DS1, CSE, 'u'), body))], 'mpbid',
          '( %s -> %s )' % (A, body))
    run(w)
