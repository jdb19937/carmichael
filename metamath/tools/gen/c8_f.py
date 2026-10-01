"""Sortie C8, section 2: derivatives of the grid terms (dvfaff, hlogtdv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *

CCPR = 'CC e. { RR , CC }'


def ccpr(w, ante):
    return w.s([w.s([], 'cnelprrecn', CCPR)], 'a1i', '( %s -> %s )' % (ante, CCPR))


def inst(w, ante, allst, var, T, body, dom, mem):
    """( ante -> body[var := T] ) from allst: ( ante -> A. var e. dom body ) and mem: ( ante -> T e. dom )"""
    idv = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, T, var, T))
    cg, new = w.wcongr(body, {var: T}, '%s = %s' % (var, T), {var: idv})
    return w.s([cg, allst, mem], 'rspcdva', '( %s -> %s )' % (ante, new)), new


def essc(w, ante, eto):
    """( ante -> E C_ CC ) from eto: ( ante -> E e. TOP )"""
    u = w.s([eto, w.inst('elssuni')], 'syl', '( %s -> E C_ U. %s )' % (ante, TOP))
    return w.s([u, w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'sseqtrrdi', '( %s -> E C_ CC )' % ante)


def gen_dvfaff():
    w = W('dvfaff', 'The derivative of ` F ` composed with the affine map ` w |-> A + T ( w - A ) ` on an open set.')
    ALLV = 'A. v e. E %s e. D' % AFF('T', 'v')
    A0 = '( %s /\\ ( E e. %s /\\ ( A e. CC /\\ T e. CC ) ) /\\ %s )' % (HOL, TOP, ALLV)
    hol = w.s([], 'simp1', '( %s -> %s )' % (A0, HOL))
    h2 = w.s([], 'simp2', '( %s -> ( E e. %s /\\ ( A e. CC /\\ T e. CC ) ) )' % (A0, TOP))
    allv = w.s([], 'simp3', '( %s -> %s )' % (A0, ALLV))
    eto = w.s([h2, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    at = w.s([h2, w.inst('simpr')], 'syl', '( %s -> ( A e. CC /\\ T e. CC ) )' % A0)
    ac = w.s([at, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    tc = w.s([at, w.inst('simpr')], 'syl', '( %s -> T e. CC )' % A0)
    cc = ccpr(w, A0)
    A1 = '( %s /\\ w e. CC )' % A0
    wc1 = w.s([], 'simpr', '( %s -> w e. CC )' % A1)
    ac1 = w.s([ac], 'adantr', '( %s -> A e. CC )' % A1)
    tc1 = w.s([tc], 'adantr', '( %s -> T e. CC )' % A1)
    did = w.s([cc], 'dvmptid', '( %s -> ( CC _D ( w e. CC |-> w ) ) = ( w e. CC |-> 1 ) )' % A0)
    dc = w.s([cc, ac], 'dvmptc', '( %s -> ( CC _D ( w e. CC |-> A ) ) = ( w e. CC |-> 0 ) )' % A0)
    one1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % A1)
    z1 = w.s([], '0cnd', '( %s -> 0 e. CC )' % A1)
    dsub = w.s([cc, wc1, one1, did, ac1, z1, dc], 'dvmptsub', '( %s -> ( CC _D ( w e. CC |-> ( w - A ) ) ) = ( w e. CC |-> ( 1 - 0 ) ) )' % A0)
    wa1 = w.s([wc1, ac1], 'subcld', '( %s -> ( w - A ) e. CC )' % A1)
    omz = w.s([one1, z1], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % A1)
    dmul = w.s([cc, wa1, omz, dsub, tc], 'dvmptcmul', '( %s -> ( CC _D ( w e. CC |-> ( T x. ( w - A ) ) ) ) = ( w e. CC |-> ( T x. ( 1 - 0 ) ) ) )' % A0)
    twa = w.s([tc1, wa1], 'mulcld', '( %s -> ( T x. ( w - A ) ) e. CC )' % A1)
    tom = w.s([tc1, omz], 'mulcld', '( %s -> ( T x. ( 1 - 0 ) ) e. CC )' % A1)
    dadd = w.s([cc, ac1, z1, dc, twa, tom, dmul], 'dvmptadd',
               '( %s -> ( CC _D ( w e. CC |-> %s ) ) = ( w e. CC |-> ( 0 + ( T x. ( 1 - 0 ) ) ) ) )' % (A0, AFF('T', 'w')))
    affc = w.s([ac1, twa], 'addcld', '( %s -> %s e. CC )' % (A1, AFF('T', 'w')))
    bc = w.s([z1, tom], 'addcld', '( %s -> ( 0 + ( T x. ( 1 - 0 ) ) ) e. CC )' % A1)
    ecc = essc(w, A0, eto)
    jeq = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    dres = w.s([cc, affc, bc, dadd, ecc, jeq, keq, eto], 'dvmptres',
               '( %s -> ( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> ( 0 + ( T x. ( 1 - 0 ) ) ) ) )' % (A0, AFF('T', 'w')))
    sb1 = w.s([w.s([w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), w.inst('subid1')], 'syl', '( %s -> ( 1 - 0 ) = 1 )' % A0)], 'oveq2d',
                   '( %s -> ( T x. ( 1 - 0 ) ) = ( T x. 1 ) )' % A0), w.s([tc], 'mulridd', '( %s -> ( T x. 1 ) = T )' % A0)], 'eqtrd',
              '( %s -> ( T x. ( 1 - 0 ) ) = T )' % A0)
    sb2 = w.s([w.s([sb1], 'oveq2d', '( %s -> ( 0 + ( T x. ( 1 - 0 ) ) ) = ( 0 + T ) )' % A0), w.s([tc], 'addlidd', '( %s -> ( 0 + T ) = T )' % A0)], 'eqtrd',
              '( %s -> ( 0 + ( T x. ( 1 - 0 ) ) ) = T )' % A0)
    sb3 = w.s([sb2], 'mpteq2dv', '( %s -> ( w e. E |-> ( 0 + ( T x. ( 1 - 0 ) ) ) ) = ( w e. E |-> T ) )' % A0)
    dinner = w.s([dres, sb3], 'eqtrd', '( %s -> ( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> T ) )' % (A0, AFF('T', 'w')))
    # outer
    dout = w.s([hol, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. D |-> ( F ` z ) ) ) = ( z e. D |-> ( ( CC _D F ) ` z ) ) )' % A0)
    A2 = '( %s /\\ w e. E )' % A0
    win = w.s([], 'simpr', '( %s -> w e. E )' % A2)
    affd, _ = inst(w, A2, w.s([allv], 'adantr', '( %s -> %s )' % (A2, ALLV)), 'v', 'w', '%s e. D' % AFF('T', 'v'), 'E', win)
    tc2 = w.s([tc], 'adantr', '( %s -> T e. CC )' % A2)
    A3 = '( %s /\\ z e. D )' % A0
    zin = w.s([], 'simpr', '( %s -> z e. D )' % A3)
    fz = w.s([w.s([w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)], 'adantr',
             '( %s -> F : D --> CC )' % A3)
    fzc = w.s([fz, zin], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A3)
    dfz = w.s([w.s([w.s([hol, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % A0)], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % A3), zin],
              'ffvelcdmd', '( %s -> ( ( CC _D F ) ` z ) e. CC )' % A3)
    e1 = w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (AFF('T', 'w'), AFF('T', 'w')))
    e2 = w.s([], 'fveq2', '( z = %s -> ( ( CC _D F ) ` z ) = ( ( CC _D F ) ` %s ) )' % (AFF('T', 'w'), AFF('T', 'w')))
    w.qed([cc, cc, affd, tc2, fzc, dfz, dinner, dout, e1, e2], 'dvmptco',
          '( %s -> ( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> ( ( ( CC _D F ) ` %s ) x. T ) ) )' % (A0, FA('T', 'w'), AFF('T', 'w')))
    return run8(w)


def gen_hlogtdv():
    w = W('hlogtdv', 'The derivative of the principal logarithm of a quotient of two affine values of ` F ` is a function on the open set.')
    BODY = '( ( %s e. D /\\ %s e. D ) /\\ ( %s =/= 0 /\\ %s e. %s ) )' % (AFF('U', 'v'), AFF('T', 'v'), FA('T', 'v'), QT('U', 'T', 'v'), SLIT)
    ALLV = 'A. v e. E %s' % BODY
    A0 = '( %s /\\ ( E e. %s /\\ ( A e. CC /\\ ( U e. CC /\\ T e. CC ) ) ) /\\ %s )' % (HOL, TOP, ALLV)
    hol = w.s([], 'simp1', '( %s -> %s )' % (A0, HOL))
    h2 = w.s([], 'simp2', '( %s -> ( E e. %s /\\ ( A e. CC /\\ ( U e. CC /\\ T e. CC ) ) ) )' % (A0, TOP))
    allv = w.s([], 'simp3', '( %s -> %s )' % (A0, ALLV))
    eto = w.s([h2, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    aut = w.s([h2, w.inst('simpr')], 'syl', '( %s -> ( A e. CC /\\ ( U e. CC /\\ T e. CC ) ) )' % A0)
    ac = w.s([aut, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    ut = w.s([aut, w.inst('simpr')], 'syl', '( %s -> ( U e. CC /\\ T e. CC ) )' % A0)
    uc = w.s([ut, w.inst('simpl')], 'syl', '( %s -> U e. CC )' % A0)
    tc = w.s([ut, w.inst('simpr')], 'syl', '( %s -> T e. CC )' % A0)
    cc = ccpr(w, A0)
    # the two dvfaff instances
    PU = '( ( ( %s e. D /\\ %s e. D ) /\\ ( %s =/= 0 /\\ %s e. %s ) ) -> %s e. D )' % (AFF('U', 'v'), AFF('T', 'v'), FA('T', 'v'), QT('U', 'T', 'v'), SLIT, AFF('U', 'v'))
    PT = '( ( ( %s e. D /\\ %s e. D ) /\\ ( %s =/= 0 /\\ %s e. %s ) ) -> %s e. D )' % (AFF('U', 'v'), AFF('T', 'v'), FA('T', 'v'), QT('U', 'T', 'v'), SLIT, AFF('T', 'v'))
    au = w.s([allv, w.s([w.s([], 'simpll', PU)], 'ralimi', '( %s -> A. v e. E %s e. D )' % (ALLV, AFF('U', 'v')))], 'syl', '( %s -> A. v e. E %s e. D )' % (A0, AFF('U', 'v')))
    at_ = w.s([allv, w.s([w.s([], 'simplr', PT)], 'ralimi', '( %s -> A. v e. E %s e. D )' % (ALLV, AFF('T', 'v')))], 'syl', '( %s -> A. v e. E %s e. D )' % (A0, AFF('T', 'v')))
    DU = '( ( ( CC _D F ) ` %s ) x. U )' % AFF('U', 'w')
    DT = '( ( ( CC _D F ) ` %s ) x. T )' % AFF('T', 'w')
    dvu = w.s([hol, w.s([eto, w.s([ac, uc], 'jca', '( %s -> ( A e. CC /\\ U e. CC ) )' % A0)], 'jca', '( %s -> ( E e. %s /\\ ( A e. CC /\\ U e. CC ) ) )' % (A0, TOP)), au,
               w.inst('dvfaff')], 'syl3anc', '( %s -> ( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> %s ) )' % (A0, FA('U', 'w'), DU))
    dvt = w.s([hol, w.s([eto, w.s([ac, tc], 'jca', '( %s -> ( A e. CC /\\ T e. CC ) )' % A0)], 'jca', '( %s -> ( E e. %s /\\ ( A e. CC /\\ T e. CC ) ) )' % (A0, TOP)), at_,
               w.inst('dvfaff')], 'syl3anc', '( %s -> ( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> %s ) )' % (A0, FA('T', 'w'), DT))
    # pointwise facts at w
    A1 = '( %s /\\ w e. E )' % A0
    win = w.s([], 'simpr', '( %s -> w e. E )' % A1)
    bw, BW = inst(w, A1, w.s([allv], 'adantr', '( %s -> %s )' % (A1, ALLV)), 'v', 'w', BODY, 'E', win)
    pud = w.s([bw, w.inst('simpll')], 'syl', '( %s -> %s e. D )' % (A1, AFF('U', 'w')))
    ptd = w.s([bw, w.inst('simplr')], 'syl', '( %s -> %s e. D )' % (A1, AFF('T', 'w')))
    nzt = w.s([bw, w.inst('simprl')], 'syl', '( %s -> %s =/= 0 )' % (A1, FA('T', 'w')))
    sl = w.s([bw, w.inst('simprr')], 'syl', '( %s -> %s e. %s )' % (A1, QT('U', 'T', 'w'), SLIT))
    ff1 = w.s([w.s([w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)], 'adantr', '( %s -> F : D --> CC )' % A1)
    df1 = w.s([w.s([hol, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % A0)], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % A1)
    fuc = w.s([ff1, pud], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, FA('U', 'w')))
    ftc = w.s([ff1, ptd], 'ffvelcdmd', '( %s -> %s e. CC )' % (A1, FA('T', 'w')))
    duc = w.s([w.s([df1, pud], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` %s ) e. CC )' % (A1, AFF('U', 'w'))), w.s([uc], 'adantr', '( %s -> U e. CC )' % A1)], 'mulcld',
              '( %s -> %s e. CC )' % (A1, DU))
    dtc = w.s([w.s([df1, ptd], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` %s ) e. CC )' % (A1, AFF('T', 'w'))), w.s([tc], 'adantr', '( %s -> T e. CC )' % A1)], 'mulcld',
              '( %s -> %s e. CC )' % (A1, DT))
    ftn = w.s([w.s([ftc, nzt], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A1, FA('T', 'w'), FA('T', 'w'))),
               w.s([], 'eldifsn', '( %s e. ( CC \\ { 0 } ) <-> ( %s e. CC /\\ %s =/= 0 ) )' % (FA('T', 'w'), FA('T', 'w'), FA('T', 'w')))], 'sylibr',
              '( %s -> %s e. ( CC \\ { 0 } ) )' % (A1, FA('T', 'w')))
    QD = '( ( ( %s x. %s ) - ( %s x. %s ) ) / ( %s ^ 2 ) )' % (DU, FA('T', 'w'), DT, FA('U', 'w'), FA('T', 'w'))
    ddiv = w.s([cc, fuc, duc, dvu, ftn, dtc, dvt], 'dvmptdiv', '( %s -> ( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> %s ) )' % (A0, QT('U', 'T', 'w'), QD))
    qdc = w.s([w.s([w.s([duc, ftc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A1, DU, FA('T', 'w'))), w.s([dtc, fuc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A1, DT, FA('U', 'w')))],
                   'subcld', '( %s -> ( ( %s x. %s ) - ( %s x. %s ) ) e. CC )' % (A1, DU, FA('T', 'w'), DT, FA('U', 'w'))),
               w.s([ftc, w.s([], '2nn0', '2 e. NN0') if False else w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A1)], 'expcld', '( %s -> ( %s ^ 2 ) e. CC )' % (A1, FA('T', 'w'))),
               w.s([ftc, nzt, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % A1)], 'expne0d', '( %s -> ( %s ^ 2 ) =/= 0 )' % (A1, FA('T', 'w')))],
              'divcld', '( %s -> %s e. CC )' % (A1, QD))
    # the logarithm on the slit plane
    LOGD = '( log |` %s )' % SLIT
    e1 = w.s([], 'eqid', '%s = %s' % (SLIT, SLIT))
    lcn = w.s([e1], 'logcn', '%s e. ( %s -cn-> CC )' % (LOGD, SLIT))
    lf = w.s([w.s([lcn, w.inst('cncff')], 'ax-mp', '%s : %s --> CC' % (LOGD, SLIT))], 'a1i', '( %s -> %s : %s --> CC )' % (A0, LOGD, SLIT))
    lm = w.s([lf], 'feqmptd', '( %s -> %s = ( y e. %s |-> ( %s ` y ) ) )' % (A0, LOGD, SLIT, LOGD))
    lm2 = w.s([w.s([w.s([], 'fvres', '( y e. %s -> ( %s ` y ) = ( log ` y ) )' % (SLIT, LOGD))], 'mpteq2ia',
                   '( y e. %s |-> ( %s ` y ) ) = ( y e. %s |-> ( log ` y ) )' % (SLIT, LOGD, SLIT))], 'a1i',
              '( %s -> ( y e. %s |-> ( %s ` y ) ) = ( y e. %s |-> ( log ` y ) ) )' % (A0, SLIT, LOGD, SLIT))
    lm3 = w.s([lm, lm2], 'eqtrd', '( %s -> %s = ( y e. %s |-> ( log ` y ) ) )' % (A0, LOGD, SLIT))
    dl0 = w.s([w.s([e1], 'dvlog', '( CC _D %s ) = ( y e. %s |-> ( 1 / y ) )' % (LOGD, SLIT))], 'a1i', '( %s -> ( CC _D %s ) = ( y e. %s |-> ( 1 / y ) ) )' % (A0, LOGD, SLIT))
    dl = w.s([w.s([w.s([lm3], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D ( y e. %s |-> ( log ` y ) ) ) )' % (A0, LOGD, SLIT))], 'eqcomd',
                  '( %s -> ( CC _D ( y e. %s |-> ( log ` y ) ) ) = ( CC _D %s ) )' % (A0, SLIT, LOGD)), dl0], 'eqtrd',
             '( %s -> ( CC _D ( y e. %s |-> ( log ` y ) ) ) = ( y e. %s |-> ( 1 / y ) ) )' % (A0, SLIT, SLIT))
    A2 = '( %s /\\ y e. %s )' % (A0, SLIT)
    yin = w.s([], 'simpr', '( %s -> y e. %s )' % (A2, SLIT))
    yne = w.s([w.s([w.s([w.s([], 'slitss', '%s C_ ( CC \\ { 0 } )' % SLIT)], 'a1i', '( %s -> %s C_ ( CC \\ { 0 } ) )' % (A2, SLIT)), yin], 'sseldd',
                   '( %s -> y e. ( CC \\ { 0 } ) )' % A2)], 'eldifsni' if False else 'idi', 'X') if False else None
    yc0 = w.s([w.s([w.s([], 'slitss', '%s C_ ( CC \\ { 0 } )' % SLIT)], 'a1i', '( %s -> %s C_ ( CC \\ { 0 } ) )' % (A2, SLIT)), yin], 'sseldd', '( %s -> y e. ( CC \\ { 0 } ) )' % A2)
    yne = w.s([yc0, w.inst('eldifsni')], 'syl', '( %s -> y =/= 0 )' % A2)
    yc = w.s([yc0, w.inst('eldifi')], 'syl', '( %s -> y e. CC )' % A2)
    lyc = w.s([yc, yne], 'logcld', '( %s -> ( log ` y ) e. CC )' % A2)
    ryc = w.s([yc, yne], 'reccld', '( %s -> ( 1 / y ) e. CC )' % A2)
    f1 = w.s([], 'fveq2', '( y = %s -> ( log ` y ) = ( log ` %s ) )' % (QT('U', 'T', 'w'), QT('U', 'T', 'w')))
    f2 = w.s([], 'oveq2', '( y = %s -> ( 1 / y ) = ( 1 / %s ) )' % (QT('U', 'T', 'w'), QT('U', 'T', 'w')))
    DL = '( ( 1 / %s ) x. %s )' % (QT('U', 'T', 'w'), QD)
    dco = w.s([cc, cc, sl, qdc, lyc, ryc, ddiv, dl, f1, f2], 'dvmptco',
              '( %s -> ( CC _D ( w e. E |-> ( log ` %s ) ) ) = ( w e. E |-> %s ) )' % (A0, QT('U', 'T', 'w'), DL))
    # closure of the derivative
    qc = w.s([fuc, ftc, nzt], 'divcld', '( %s -> %s e. CC )' % (A1, QT('U', 'T', 'w')))
    qne = w.s([w.s([w.s([w.s([], 'slitss', '%s C_ ( CC \\ { 0 } )' % SLIT)], 'a1i', '( %s -> %s C_ ( CC \\ { 0 } ) )' % (A1, SLIT)), sl], 'sseldd',
                   '( %s -> %s e. ( CC \\ { 0 } ) )' % (A1, QT('U', 'T', 'w'))), w.inst('eldifsni')], 'syl', '( %s -> %s =/= 0 )' % (A1, QT('U', 'T', 'w')))
    dlc = w.s([w.s([qc, qne], 'reccld', '( %s -> ( 1 / %s ) e. CC )' % (A1, QT('U', 'T', 'w'))), qdc], 'mulcld', '( %s -> %s e. CC )' % (A1, DL))
    mf = w.s([dlc], 'fmpttd', '( %s -> ( w e. E |-> %s ) : E --> CC )' % (A0, DL))
    w.qed([mf, w.s([dco], 'feq1d', '( %s -> ( ( CC _D ( w e. E |-> ( log ` %s ) ) ) : E --> CC <-> ( w e. E |-> %s ) : E --> CC ) )' % (A0, QT('U', 'T', 'w'), DL))],
          'mpbird', '( %s -> ( CC _D ( w e. E |-> ( log ` %s ) ) ) : E --> CC )' % (A0, QT('U', 'T', 'w')))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_dvfaff, gen_hlogtdv]:
        g()
