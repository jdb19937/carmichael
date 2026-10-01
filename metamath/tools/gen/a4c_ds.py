"""Sortie A4c, batch 4: one DP step (Lean: AlgExtract.dpStep_*)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

PM = '( P mod L )'
SNT = '( ( T SetIfNone %s ) ` <" P "> )' % PM
DGL = '( ( ( ( L DpGo P ) ` T ) ` L ) ` %s )' % SNT
DS = '( ( L DpStep P ) ` T )'
DV = lambda x: '( ( 1st ` %s ) ` %s )' % (DS, x)

def dctx(w, A, tag=None):
    """L e. NN, P e. NN0, T e. Tbl from a step reaching DPO"""
    if tag is None:
        dp = w.s([], 'id', '( %s -> %s )' % (A, DPO))
    else:
        dp = w.s([], tag, '( %s -> %s )' % (A, DPO))
    ll = w.s([w.s([dp], 'simpld', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([dp], 'simpld', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A)], 'simprd', '( %s -> P e. NN0 )' % A)
    tt = w.s([dp], 'simprd', '( %s -> T e. Tbl )' % A)
    l0 = w.s([ll], 'nnnn0d', '( %s -> L e. NN0 )' % A)
    return dp, ll, pp, tt, l0

# ------------------------------------------------------------------ dpstepmcl
if not only or 'dpstepmcl' in only:
    w = W('dpstepmcl', 'The residue of the new prime is a residue.')
    A = '( L e. NN /\\ P e. NN0 )'
    ll = w.s([], 'simpl', '( %s -> L e. NN )' % A)
    pp = w.s([], 'simpr', '( %s -> P e. NN0 )' % A)
    w.qed([w.s([pp], 'nn0zd', '( %s -> P e. ZZ )' % A), ll, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, PM))
    run(w)

# ------------------------------------------------------------------ dpstepacl
if not only or 'dpstepacl' in only:
    w = W('dpstepacl', 'The table a DP step starts the propagation from.')
    dp, ll, pp, tt, l0 = dctx(w, DPO)
    m = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % DPO), w.inst('dpstepmcl')], 'syl',
            '( %s -> %s e. NN0 )' % (DPO, PM))
    s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % DPO)
    w.qed([w.s([w.s([tt, m], 'jca', '( %s -> ( T e. Tbl /\\ %s e. NN0 ) )' % (DPO, PM)), s1], 'jca',
               '( %s -> ( ( T e. Tbl /\\ %s e. NN0 ) /\\ <" P "> e. Word NN0 ) )' % (DPO, PM)), w.inst('setifnonecl')], 'syl',
          '( %s -> %s e. Tbl )' % (DPO, SNT))
    run(w)

def dsval(w, A, dp, ll, pp, tt):
    return w.s([dp, w.inst('dpstepval')], 'syl',
               '( %s -> %s = <. ( 1st ` %s ) , ( ( 2nd ` %s ) + 1 ) >. )' % (A, DS, DGL, DGL))

def dsp1(w, A, dp, ll, pp, tt):
    """( A -> ( 1st ` DS ) = ( 1st ` DGL ) )"""
    v = dsval(w, A, dp, ll, pp, tt)
    return prj(w, A, DS, v, '( 1st ` %s )' % DGL, '( ( 2nd ` %s ) + 1 )' % DGL, 1)

def dgctx(w, A, dp, l0, acl):
    """the three-way antecedent dpgo* wants, at F := L and A := SNT"""
    return w.s([dp, w.s([l0, acl], 'jca', '( %s -> ( L e. NN0 /\\ %s e. Tbl ) )' % (A, SNT))], 'jca',
               '( %s -> ( %s /\\ ( L e. NN0 /\\ %s e. Tbl ) ) )' % (A, DPO, SNT))

# ------------------------------------------------------------------ dpstepcost
if not only or 'dpstepcost' in only:
    w = W('dpstepcost', 'A DP step charges one unit per residue plus one (Lean: dpStep_cost).')
    dp, ll, pp, tt, l0 = dctx(w, DPO)
    acl = w.s([], 'dpstepacl', '( %s -> %s e. Tbl )' % (DPO, SNT))
    p2 = prj(w, DPO, DS, dsval(w, DPO, dp, ll, pp, tt), '( 1st ` %s )' % DGL, '( ( 2nd ` %s ) + 1 )' % DGL, 2)
    c = w.s([dgctx(w, DPO, dp, l0, acl), w.inst('dpgocost')], 'syl', '( %s -> ( 2nd ` %s ) = L )' % (DPO, DGL))
    w.qed([p2, w.s([c], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( L + 1 ) )' % (DPO, DGL))], 'eqtrd',
          '( %s -> ( 2nd ` %s ) = ( L + 1 ) )' % (DPO, DS))
    run(w)

# ------------------------------------------------------------------ dpsteppers
PA = '( %s /\\ ( C e. NN0 /\\ ( T ` C ) =/= %s ) )' % (DPO, NONE)
if not only or 'dpsteppers' in only:
    w = W('dpsteppers', 'A DP step leaves a nonempty entry alone (Lean: dpStep_persist).')
    dp, ll, pp, tt, l0 = dctx(w, PA, 'simpl')
    cc = w.s([], 'simprl', '( %s -> C e. NN0 )' % PA)
    nn = w.s([], 'simprr', '( %s -> ( T ` C ) =/= %s )' % (PA, NONE))
    acl = w.s([dp, w.inst('dpstepacl')], 'syl', '( %s -> %s e. Tbl )' % (PA, SNT))
    m = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % PA), w.inst('dpstepmcl')], 'syl',
            '( %s -> %s e. NN0 )' % (PA, PM))
    s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % PA)
    t3 = w.s([tt, m, s1], '3jca', '( %s -> ( T e. Tbl /\\ %s e. NN0 /\\ <" P "> e. Word NN0 ) )' % (PA, PM))
    sp = w.s([w.s([t3, w.s([cc, nn], 'jca', '( %s -> ( C e. NN0 /\\ ( T ` C ) =/= %s ) )' % (PA, NONE))], 'jca',
                  '( %s -> ( ( T e. Tbl /\\ %s e. NN0 /\\ <" P "> e. Word NN0 ) /\\ ( C e. NN0 /\\ ( T ` C ) =/= %s ) ) )' % (PA, PM, NONE)),
              w.inst('sinpers')], 'syl', '( %s -> ( %s ` C ) = ( T ` C ) )' % (PA, SNT))
    snn = w.s([sp, nn], 'eqnetrd', '( %s -> ( %s ` C ) =/= %s )' % (PA, SNT, NONE))
    per = w.s([w.s([dp, w.s([l0, acl], 'jca', '( %s -> ( L e. NN0 /\\ %s e. Tbl ) )' % (PA, SNT)),
                    w.s([cc, snn], 'jca', '( %s -> ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (PA, SNT, NONE))], '3jca',
                   '( %s -> ( %s /\\ ( L e. NN0 /\\ %s e. Tbl ) /\\ ( C e. NN0 /\\ ( %s ` C ) =/= %s ) ) )' % (PA, DPO, SNT, SNT, NONE)),
               w.inst('dpgopers')], 'syl', '( %s -> ( ( 1st ` %s ) ` C ) = ( %s ` C ) )' % (PA, DGL, SNT))
    p1 = dsp1(w, PA, dp, ll, pp, tt)
    w.qed([w.s([p1], 'fveq1d', '( %s -> %s = ( ( 1st ` %s ) ` C ) )' % (PA, DV('C'), DGL)),
           w.s([per, sp], 'eqtrd', '( %s -> ( ( 1st ` %s ) ` C ) = ( T ` C ) )' % (PA, DGL))], 'eqtrd',
          '( %s -> %s = ( T ` C ) )' % (PA, DV('C')))
    run(w)

# ------------------------------------------------------------------ dpstepnn
if not only or 'dpstepnn' in only:
    w = W('dpstepnn', 'A DP step keeps a nonempty entry nonempty (Lean: dpStep_ne_none).')
    p = w.s([], 'dpsteppers', '( %s -> %s = ( T ` C ) )' % (PA, DV('C')))
    nn = w.s([], 'simprr', '( %s -> ( T ` C ) =/= %s )' % (PA, NONE))
    w.qed([p, nn], 'eqnetrd', '( %s -> %s =/= %s )' % (PA, DV('C'), NONE))
    run(w)

# ------------------------------------------------------------------ dpstepself
if not only or 'dpstepself' in only:
    w = W('dpstepself', 'A DP step fills the residue of the new prime (Lean: dpStep_self).')
    dp, ll, pp, tt, l0 = dctx(w, DPO)
    acl = w.s([], 'dpstepacl', '( %s -> %s e. Tbl )' % (DPO, SNT))
    m = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % DPO), w.inst('dpstepmcl')], 'syl',
            '( %s -> %s e. NN0 )' % (DPO, PM))
    s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % DPO)
    slf = w.s([w.s([tt, m, s1], '3jca', '( %s -> ( T e. Tbl /\\ %s e. NN0 /\\ <" P "> e. Word NN0 ) )' % (DPO, PM)),
               w.inst('sinself')], 'syl', '( %s -> ( %s ` %s ) =/= %s )' % (DPO, SNT, PM, NONE))
    nn = w.s([w.s([dp, w.s([l0, acl], 'jca', '( %s -> ( L e. NN0 /\\ %s e. Tbl ) )' % (DPO, SNT)),
                   w.s([m, slf], 'jca', '( %s -> ( %s e. NN0 /\\ ( %s ` %s ) =/= %s ) )' % (DPO, PM, SNT, PM, NONE))], '3jca',
                  '( %s -> ( %s /\\ ( L e. NN0 /\\ %s e. Tbl ) /\\ ( %s e. NN0 /\\ ( %s ` %s ) =/= %s ) ) )' % (DPO, DPO, SNT, PM, SNT, PM, NONE)),
               w.inst('dpgonn')], 'syl', '( %s -> ( ( 1st ` %s ) ` %s ) =/= %s )' % (DPO, DGL, PM, NONE))
    p1 = dsp1(w, DPO, dp, ll, pp, tt)
    w.qed([w.s([p1], 'fveq1d', '( %s -> %s = ( ( 1st ` %s ) ` %s ) )' % (DPO, DV(PM), DGL, PM)), nn], 'eqnetrd',
          '( %s -> %s =/= %s )' % (DPO, DV(PM), NONE))
    run(w)

# ------------------------------------------------------------------ dpstephit
HA = '( %s /\\ ( R e. NN0 /\\ R < L /\\ ( T ` R ) =/= %s ) )' % (DPO, NONE)
RM = '( ( R x. P ) mod L )'
if not only or 'dpstephit' in only:
    w = W('dpstephit', 'A DP step propagates every snapshot entry (Lean: dpStep_hit).')
    dp, ll, pp, tt, l0 = dctx(w, HA, 'simpl')
    hy = w.s([], 'simpr', '( %s -> ( R e. NN0 /\\ R < L /\\ ( T ` R ) =/= %s ) )' % (HA, NONE))
    acl = w.s([dp, w.inst('dpstepacl')], 'syl', '( %s -> %s e. Tbl )' % (HA, SNT))
    hit = w.s([w.s([dp, w.s([l0, acl], 'jca', '( %s -> ( L e. NN0 /\\ %s e. Tbl ) )' % (HA, SNT)), hy], '3jca',
                   '( %s -> ( %s /\\ ( L e. NN0 /\\ %s e. Tbl ) /\\ ( R e. NN0 /\\ R < L /\\ ( T ` R ) =/= %s ) ) )' % (HA, DPO, SNT, NONE)),
               w.inst('dpgohit')], 'syl', '( %s -> ( ( 1st ` %s ) ` %s ) =/= %s )' % (HA, DGL, RM, NONE))
    p1 = dsp1(w, HA, dp, ll, pp, tt)
    w.qed([w.s([p1], 'fveq1d', '( %s -> %s = ( ( 1st ` %s ) ` %s ) )' % (HA, DV(RM), DGL, RM)), hit], 'eqnetrd',
          '( %s -> %s =/= %s )' % (HA, DV(RM), NONE))
    run(w)

# ------------------------------------------------------------------ dpstepcases
CA = '( %s /\\ ( C e. NN0 /\\ %s =/= %s ) )' % (DPO, DV('C'), NONE)
def RBS(v, tgt):
    return '( ( ( T ` %s ) =/= %s /\\ C = ( ( %s x. P ) mod L ) ) /\\ ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` %s ) ) ) )' % (v, NONE, v, tgt, v)
if not only or 'dpstepcases' in only:
    w = W('dpstepcases', 'Every nonempty entry after a DP step is old, the new prime, or an extension (Lean: dpStep_cases).')
    GL = '( ( 1st ` %s ) ` C )' % DGL
    NEW = '( C = %s /\\ ( 2nd ` %s ) = <" P "> )' % (PM, DV('C'))
    CONC = '( ( T ` C ) = %s \\/ ( %s \\/ E. r e. ( 0 ..^ L ) %s ) )' % (DV('C'), NEW, RBS('r', DV('C')))
    dp, ll, pp, tt, l0 = dctx(w, CA, 'simpl')
    cc = w.s([], 'simprl', '( %s -> C e. NN0 )' % CA)
    nn = w.s([], 'simprr', '( %s -> %s =/= %s )' % (CA, DV('C'), NONE))
    acl = w.s([dp, w.inst('dpstepacl')], 'syl', '( %s -> %s e. Tbl )' % (CA, SNT))
    m = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % CA), w.inst('dpstepmcl')], 'syl',
            '( %s -> %s e. NN0 )' % (CA, PM))
    s1 = w.s([pp, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % CA)
    p1 = dsp1(w, CA, dp, ll, pp, tt)
    dveq = w.s([p1], 'fveq1d', '( %s -> %s = %s )' % (CA, DV('C'), GL))
    glnn = w.s([w.s([dveq], 'eqcomd', '( %s -> %s = %s )' % (CA, GL, DV('C'))), nn], 'eqnetrd',
               '( %s -> %s =/= %s )' % (CA, GL, NONE))
    cas = w.s([w.s([dp, w.s([l0, acl], 'jca', '( %s -> ( L e. NN0 /\\ %s e. Tbl ) )' % (CA, SNT)),
                    w.s([cc, glnn], 'jca', '( %s -> ( C e. NN0 /\\ %s =/= %s ) )' % (CA, GL, NONE))], '3jca',
                   '( %s -> ( %s /\\ ( L e. NN0 /\\ %s e. Tbl ) /\\ ( C e. NN0 /\\ %s =/= %s ) ) )' % (CA, DPO, SNT, GL, NONE)),
               w.inst('dpgocases')], 'syl',
              '( %s -> ( ( %s ` C ) = %s \\/ E. r e. ( 0 ..^ L ) %s ) )' % (CA, SNT, GL, RBS('r', GL)))
    # ---- the accumulator branch: sincases
    LB = '( %s /\\ ( %s ` C ) = %s )' % (CA, SNT, GL)
    lfl = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (LB, f))
    sq = w.s([], 'simpr', '( %s -> ( %s ` C ) = %s )' % (LB, SNT, GL))
    snn = w.s([sq, lfl(glnn, '%s =/= %s' % (GL, NONE))], 'eqnetrd', '( %s -> ( %s ` C ) =/= %s )' % (LB, SNT, NONE))
    sc = w.s([w.s([w.s([lfl(tt, 'T e. Tbl'), lfl(m, '%s e. NN0' % PM), lfl(s1, '<" P "> e. Word NN0')], '3jca',
                       '( %s -> ( T e. Tbl /\\ %s e. NN0 /\\ <" P "> e. Word NN0 ) )' % (LB, PM)),
                   w.s([lfl(cc, 'C e. NN0'), snn], 'jca', '( %s -> ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (LB, SNT, NONE))], 'jca',
                  '( %s -> ( ( T e. Tbl /\\ %s e. NN0 /\\ <" P "> e. Word NN0 ) /\\ ( C e. NN0 /\\ ( %s ` C ) =/= %s ) ) )' % (LB, PM, SNT, NONE)),
               w.inst('sincases')], 'syl',
              '( %s -> ( ( T ` C ) = ( %s ` C ) \\/ ( C = %s /\\ ( 2nd ` ( %s ` C ) ) = <" P "> ) ) )' % (LB, SNT, PM, SNT))
    sdv = w.s([sq, w.s([lfl(dveq, '%s = %s' % (DV('C'), GL))], 'eqcomd', '( %s -> %s = %s )' % (LB, GL, DV('C')))], 'eqtrd',
              '( %s -> ( %s ` C ) = %s )' % (LB, SNT, DV('C')))
    b1 = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ ( T ` C ) = ( %s ` C ) ) -> ( T ` C ) = ( %s ` C ) )' % (LB, SNT, SNT)),
                   w.s([sdv], 'adantr', '( ( %s /\\ ( T ` C ) = ( %s ` C ) ) -> ( %s ` C ) = %s )' % (LB, SNT, SNT, DV('C')))], 'eqtrd',
                  '( ( %s /\\ ( T ` C ) = ( %s ` C ) ) -> ( T ` C ) = %s )' % (LB, SNT, DV('C')))], 'orcd',
             '( ( %s /\\ ( T ` C ) = ( %s ` C ) ) -> %s )' % (LB, SNT, CONC))
    NB = '( C = %s /\\ ( 2nd ` ( %s ` C ) ) = <" P "> )' % (PM, SNT)
    LN = '( %s /\\ %s )' % (LB, NB)
    b2 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (LN, NB))], 'simpld', '( %s -> C = %s )' % (LN, PM)),
                   w.s([w.s([w.s([sdv], 'adantr', '( %s -> ( %s ` C ) = %s )' % (LN, SNT, DV('C')))], 'fveq2d',
                            '( %s -> ( 2nd ` ( %s ` C ) ) = ( 2nd ` %s ) )' % (LN, SNT, DV('C'))),
                        w.s([w.s([], 'simpr', '( %s -> %s )' % (LN, NB))], 'simprd',
                            '( %s -> ( 2nd ` ( %s ` C ) ) = <" P "> )' % (LN, SNT))], 'eqtr3d',
                       '( %s -> ( 2nd ` %s ) = <" P "> )' % (LN, DV('C')))], 'jca', '( %s -> %s )' % (LN, NEW))], 'orcd',
             '( %s -> ( %s \\/ E. r e. ( 0 ..^ L ) %s ) )' % (LN, NEW, RBS('r', DV('C'))))
    b2o = w.s([b2], 'olcd', '( %s -> %s )' % (LN, CONC))
    lall = w.s([sc, w.s([b1], 'ex', '( %s -> ( ( T ` C ) = ( %s ` C ) -> %s ) )' % (LB, SNT, CONC)),
                w.s([b2o], 'ex', '( %s -> ( %s -> %s ) )' % (LB, NB, CONC))], 'mpjaod', '( %s -> %s )' % (LB, CONC))
    imp1 = w.s([lall], 'ex', '( %s -> ( ( %s ` C ) = %s -> %s ) )' % (CA, SNT, GL, CONC))
    # ---- the propagation branch
    bi = w.s([w.s([dveq], 'eqcomd', '( %s -> %s = %s )' % (CA, GL, DV('C')))], 'fveq2d',
             '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (CA, GL, DV('C')))
    bi1 = w.s([bi], 'eqeq1d', '( %s -> ( ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) <-> ( 2nd ` %s ) = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) ) )' % (CA, GL, DV('C')))
    bi2 = w.s([bi1], 'anbi2d', '( %s -> ( %s <-> %s ) )' % (CA, RBS('r', GL), RBS('r', DV('C'))))
    rim = w.s([w.s([bi2], 'biimpd', '( %s -> ( %s -> %s ) )' % (CA, RBS('r', GL), RBS('r', DV('C'))))], 'reximdv',
              '( %s -> ( E. r e. ( 0 ..^ L ) %s -> E. r e. ( 0 ..^ L ) %s ) )' % (CA, RBS('r', GL), RBS('r', DV('C'))))
    imp2 = w.s([rim, w.s([w.s([], 'olc', '( E. r e. ( 0 ..^ L ) %s -> ( %s \\/ E. r e. ( 0 ..^ L ) %s ) )' % (RBS('r', DV('C')), NEW, RBS('r', DV('C')))),
                          w.s([], 'olc', '( ( %s \\/ E. r e. ( 0 ..^ L ) %s ) -> %s )' % (NEW, RBS('r', DV('C')), CONC))], 'syl',
                         '( E. r e. ( 0 ..^ L ) %s -> %s )' % (RBS('r', DV('C')), CONC))], 'syl6',
               '( %s -> ( E. r e. ( 0 ..^ L ) %s -> %s ) )' % (CA, RBS('r', GL), CONC))
    w.qed([cas, imp1, imp2], 'mpjaod', '( %s -> %s )' % (CA, CONC))
    run(w)
