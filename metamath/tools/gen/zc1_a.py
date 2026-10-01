"""Sortie ZC1: the generic strip count (jenstrip), C10's lchrzq with F, the bound and the centre bound as hypotheses."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import num
from c10_freeze import S as FS
from c8_n import sqparts, sqre_at, sqcc
from c8_o import numst, sqab_st
from c9_b import decode
import c9_h
patch(c9_h)
from c9_h import c0_facts
from c10_f import crfacts, clo
import lin
lin.FASTPATH = True

R38, R298 = '( 3 / 8 )', '( ; 2 9 / 8 )'


def gen_jenstrip():
    w = W('jenstrip', 'Generic strip count: for ` F ` holomorphic on the right half-plane, bounded by ` B ` on the square of half-side ` 7 / 4 ` about ` 2 + i T ` and with ` M <_ abs F ( 2 + i T ) ` , the zeros in ` [ 3 / 8 , 29 / 8 ] x. [ T - 13 / 32 , T + 13 / 32 ] ` have mass at most ` log ( B / M ) / log ( 25 / 24 ) ` ( ~ jenrct ; C10\'s ~ lchrzq with the data as hypotheses).')
    A0 = JH
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2, X3 = top_and(A0)
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2); x3 = s([], 'simp3', X3)
    hol = s([x1, w.inst('simpl')], 'syl', HOLF('F', HP0))
    tr = s([x1, w.inst('simpr')], 'syl', 'T e. RR')
    bre = s([x2, w.inst('simpl')], 'syl', 'B e. RR')
    fbx = s([x2, w.inst('simpr')], 'syl', top_and(X2)[1])
    mrp = s([x3, w.inst('simpl')], 'syl', 'M e. RR+')
    mle = s([x3, w.inst('simpr')], 'syl', top_and(X3)[1])
    c0, re0, im0 = c0_facts(w, A0, tr)
    QAt, QBt = QA('T'), QB('T')
    ta = s([tr, numst(w, A0, R1332, 'RR')], 'resubcld', '( T - %s ) e. RR' % R1332)
    tb = s([tr, numst(w, A0, R1332, 'RR')], 'readdcld', '( T + %s ) e. RR' % R1332)
    qac, reA, imA = crfacts(w, A0, R38, '( T - %s )' % R1332, numst(w, A0, R38, 'RR'), ta)
    qbc, reB, imB = crfacts(w, A0, R298, '( T + %s )' % R1332, numst(w, A0, R298, 'RR'), tb)
    rl = lambda e, st: (e, s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e))
    lv = dict([rl('( Re ` %s )' % QAt, qac), rl('( Re ` %s )' % QBt, qbc), rl('( Im ` %s )' % QAt, qac), rl('( Im ` %s )' % QBt, qbc),
               rl('( Re ` %s )' % C0, c0), rl('( Im ` %s )' % C0, c0)])
    lv['T'] = tr
    geo = s([lin8(w, A0, [reA, reB], '( Re ` %s ) <_ ( Re ` %s )' % (QAt, QBt), lv), lin8(w, A0, [imA, imB], '( Im ` %s ) <_ ( Im ` %s )' % (QAt, QBt), lv)], 'jca', GEOG(QAt, QBt))
    r74 = numst(w, A0, R74, 'RR'); r18 = numst(w, A0, R18, 'RR')
    SA, SB = SQA(C0, R74), SQB(C0, R74)
    OA, OB = SQA(QAt, R18), SQB(QBt, R18)
    sab = sqab_st(w, A0, c0, r74, C0, R74)
    oa, _ = sqcc(w, A0, qac, r18, c=QAt, r=R18)
    _, ob = sqcc(w, A0, qbc, r18, c=QBt, r=R18)
    ps = sqparts(w, A0, sqre_at(w, A0, c0, r74, c=C0, r=R74), c=C0, r=R74)
    pa = sqparts(w, A0, sqre_at(w, A0, qac, r18, c=QAt, r=R18), c=QAt, r=R18)
    pb = sqparts(w, A0, sqre_at(w, A0, qbc, r18, c=QBt, r=R18), c=QBt, r=R18)
    sac = s([sab, w.inst('simpl')], 'syl', '%s e. CC' % SA); sbc = s([sab, w.inst('simpr')], 'syl', '%s e. CC' % SB)
    for e, st in ((SA, sac), (SB, sbc), (OA, oa), (OB, ob)):
        lv.update(dict([rl('( Re ` %s )' % e, st), rl('( Im ` %s )' % e, st)]))
    hy = [re0, im0, reA, reB, imA, imB] + ps + pa + pb
    i1 = lin8(w, A0, hy, '( Re ` %s ) <_ ( Re ` %s )' % (SA, OA), lv)
    i2 = lin8(w, A0, hy, '( Re ` %s ) <_ ( Re ` %s )' % (OB, SB), lv)
    i3 = lin8(w, A0, hy, '( Im ` %s ) <_ ( Im ` %s )' % (SA, OA), lv)
    i4 = lin8(w, A0, hy, '( Im ` %s ) <_ ( Im ` %s )' % (OB, SB), lv)
    CS = tsub(stmt('crectss2'), {'A': SA, 'B': SB, 'C': OA, 'E': OB})
    csa, csc = ante_of(CS)
    Y1, Y2, Y3 = top_and(csa)
    oss = s([s([sab, s([oa, ob], 'jca', Y2), s([s([i1, i2], 'jca', top_and(Y3)[0]), s([i3, i4], 'jca', top_and(Y3)[1])], 'jca', Y3)], '3jca', csa), w.inst('crectss2')], 'syl', csc)
    lt = s([lin8(w, A0, [], '%s < 2' % R74, {}), re0], 'breqtrrd', '%s < ( Re ` %s )' % (R74, C0))
    f = tsub(stmt('sqhp0'), {'C': C0, 'R': R74})
    fa, fc = ante_of(f)
    shp = s([s([s([c0, r74], 'jca', '( %s e. CC /\\ %s e. RR )' % (C0, R74)), lt], 'jca', fa), w.inst('sqhp0')], 'syl', fc)
    ohp = s([oss, shp], 'sstrd', '( %s crect %s ) C_ %s' % (OA, OB, HP0))
    JR = tsub(FS['jenrct'], {'F': 'F', 'D': HP0, 'A': QAt, 'B': QBt, 'M': R18, 'C': C0, 'R': R74, 'V': R4225, 'Y': 'B'})
    jra, jrc = ante_of(JR)
    J1, J2, J3 = top_and(jra)
    j1 = s([hol, s([s([qac, qbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (QAt, QBt)), geo], 'jca', top_and(J1)[1]), s([numst(w, A0, R18, 'RR+'), ohp], 'jca', top_and(J1)[2])], '3jca', J1)
    K1, K2, K3 = top_and(J2)
    INT = INTG(QAt, QBt, C0)
    lvs = [reA, reB, imA, imB, re0, im0]
    it = s([c0, s([s([lin8(w, A0, lvs, '( Re ` %s ) < ( Re ` %s )' % (QAt, C0), lv), lin8(w, A0, lvs, '( Re ` %s ) < ( Re ` %s )' % (C0, QBt), lv)], 'jca',
                      '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (QAt, C0, C0, QBt)),
                    s([lin8(w, A0, lvs, '( Im ` %s ) < ( Im ` %s )' % (QAt, C0), lv), lin8(w, A0, lvs, '( Im ` %s ) < ( Im ` %s )' % (C0, QBt), lv)], 'jca',
                      '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (QAt, C0, C0, QBt))], 'jca', INT[len('( %s e. CC /\\ ' % C0):-2])], 'jca', INT)
    cq = w.s([s([qac, qbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (QAt, QBt)), it, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. ( %s crect %s ) )' % (A0, C0, QAt, QBt))
    LC = '( F ` %s )' % C0
    ALC = '( abs ` %s )' % LC
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)),
             s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))], 'mpbird', '%s e. %s' % (C0, HP0))
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), c0h], 'ffvelcdmd', '%s e. CC' % LC)
    alr = s([lfc], 'abscld', '%s e. RR' % ALC)
    mr = s([mrp], 'rpred', 'M e. RR')
    mgt = s([mrp], 'rpgt0d', '0 < M')
    apos = lin8(w, A0, [mle, mgt], '0 < %s' % ALC, {ALC: alr, 'M': mr})
    lne = s([apos, s([lfc, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < %s )' % (LC, ALC))], 'mpbird', '%s =/= 0' % LC)
    k1 = s([cq, lne], 'jca', K1)
    k2 = s([numst(w, A0, R74, 'RR+'), shp], 'jca', K2)
    Q = '( %s crect %s )' % (QAt, QBt)
    Aj = '( %s /\\ j e. %s )' % (A0, Q)
    sj = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aj, f))
    Lj = lambda st: lift(w, st, Aj)
    dj = decode(w, Aj, sj([], 'simpr', 'j e. %s' % Q), Lj(qac), Lj(qbc), QAt, QBt, Q, U='j')
    jc = dj[0]
    D_ = '( %s - j )' % C0
    dc = sj([Lj(c0), jc], 'subcld', '%s e. CC' % D_)
    rd = sj([Lj(c0), jc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` j ) )' % (D_, C0))
    idd = sj([Lj(c0), jc], 'imsubd', '( Im ` %s ) = ( ( Im ` %s ) - ( Im ` j ) )' % (D_, C0))
    RD, ID = '( Re ` %s )' % D_, '( Im ` %s )' % D_
    lvj = {k_: Lj(v_) for k_, v_ in lv.items()}
    lvj.update({RD: sj([dc], 'recld', '%s e. RR' % RD), ID: sj([dc], 'imcld', '%s e. RR' % ID), '( Re ` j )': sj([jc], 'recld', '( Re ` j ) e. RR'),
                '( Im ` j )': sj([jc], 'imcld', '( Im ` j ) e. RR')})
    hj = [Lj(re0), Lj(im0), Lj(reA), Lj(reB), Lj(imA), Lj(imB), rd, idd] + dj[1:]
    f1 = lin8(w, Aj, hj, '0 <_ ( %s - %s )' % (R138, RD), lvj); f2 = lin8(w, Aj, hj, '0 <_ ( %s + %s )' % (R138, RD), lvj)
    f3 = lin8(w, Aj, hj, '0 <_ ( %s - %s )' % (R1332, ID), lvj); f4 = lin8(w, Aj, hj, '0 <_ ( %s + %s )' % (R1332, ID), lvj)
    def rr_(e):
        c = clo(w, Aj, lvj); return c.mem(e, 'RR')
    h1 = sj([rr_('( %s - %s )' % (R138, RD)), rr_('( %s + %s )' % (R138, RD)), f1, f2], 'mulge0d', '0 <_ ( ( %s - %s ) x. ( %s + %s ) )' % (R138, RD, R138, RD))
    h2 = sj([rr_('( %s - %s )' % (R1332, ID)), rr_('( %s + %s )' % (R1332, ID)), f3, f4], 'mulge0d', '0 <_ ( ( %s - %s ) x. ( %s + %s ) )' % (R1332, ID, R1332, ID))
    AD = '( abs ` %s )' % D_
    a2 = sj([dc], 'absvalsq2d', '( %s ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (AD, RD, ID))
    q1 = sj([sj([lvj[RD]], 'recnd', '%s e. CC' % RD)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (RD, RD, RD))
    q2 = sj([sj([lvj[ID]], 'recnd', '%s e. CC' % ID)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (ID, ID, ID))
    VV = '( %s ^ 2 )' % R4225
    lit = num.mul_lits(w, R4225, R4225)
    LV2 = num.lit_text(num.lit_value(R4225) ** 2)
    v2 = sj([sj([numst(w, Aj, R4225, 'CC')], 'sqvald', '%s = ( %s x. %s )' % (VV, R4225, R4225)), w.s([lit], 'a1i', '( %s -> ( %s x. %s ) = %s )' % (Aj, R4225, R4225, LV2))],
            'eqtrd', '%s = %s' % (VV, LV2))
    lvj2 = dict(lvj)
    adr = sj([dc], 'abscld', '%s e. RR' % AD)
    lvj2['( %s ^ 2 )' % AD] = sj([adr], 'resqcld', '( %s ^ 2 ) e. RR' % AD)
    lvj2['( %s ^ 2 )' % RD] = sj([lvj[RD]], 'resqcld', '( %s ^ 2 ) e. RR' % RD)
    lvj2['( %s ^ 2 )' % ID] = sj([lvj[ID]], 'resqcld', '( %s ^ 2 ) e. RR' % ID)
    lvj2[VV] = sj([numst(w, Aj, R4225, 'RR')], 'resqcld', '%s e. RR' % VV)
    le2 = lin.linarith(w, Aj, [a2, q1, q2, v2, h1, h2], '( %s ^ 2 ) <_ %s' % (AD, VV), closure=clo(w, Aj, lvj2), products=True)
    eq2 = sj([adr, numst(w, Aj, R4225, 'RR'), sj([dc], 'absge0d', '0 <_ %s' % AD), numst(w, Aj, R4225, 'ge0')], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ %s )' % (AD, R4225, AD, VV))
    dj1 = sj([le2, eq2], 'mpbird', '%s <_ %s' % (AD, R4225))
    alj = s([dj1], 'ralrimiva', 'A. j e. %s ( abs ` ( %s - j ) ) <_ %s' % (Q, C0, R4225))
    k3 = s([numst(w, A0, R4225, 'RR+'), lin8(w, A0, [], '%s <_ %s' % (R4225, R74), {}), alj], '3jca', K3)
    j2 = s([k1, k2, k3], '3jca', J2)
    j3 = s([bre, fbx], 'jca', J3)
    jr = s([s([j1, j2, j3], '3jca', jra), w.inst('jenrct')], 'syl', jrc)
    ZF_, ALQ, INEQ0 = top_and(jrc)
    zfin = s([jr, w.inst('simp1')], 'syl', ZF_); alq = s([jr, w.inst('simp2')], 'syl', ALQ); iq0 = s([jr, w.inst('simp3')], 'syl', INEQ0)
    SH = MASS(ZQF, 'F')
    Aq = '( %s /\\ q e. %s )' % (A0, ZQF)
    hqn = w.s([alq], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)
    shr = s([zfin, w.s([hqn], 'nnred', '( %s -> ( F holord q ) e. RR )' % Aq)], 'fsumrecl', '%s e. RR' % SH)
    ml = num.mul_lits(w, R4225, R2524)
    v4c = numst(w, A0, R4225, 'CC'); v4n = s([numst(w, A0, R4225, 'RR+')], 'rpne0d', '%s =/= 0' % R4225)
    dmu = s([s([numst(w, A0, R74, 'CC'), numst(w, A0, R2524, 'CC'), s([v4c, v4n], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (R4225, R4225))], '3jca',
               '( %s e. CC /\\ %s e. CC /\\ ( %s e. CC /\\ %s =/= 0 ) )' % (R74, R2524, R4225, R4225)), w.inst('divmul')], 'syl',
            '( ( %s / %s ) = %s <-> ( %s x. %s ) = %s )' % (R74, R4225, R2524, R4225, R2524, R74))
    rv = s([w.s([ml], 'a1i', '( %s -> ( %s x. %s ) = %s )' % (A0, R4225, R2524, R74)), dmu], 'mpbird', '( %s / %s ) = %s' % (R74, R4225, R2524))
    lg = s([s([rv], 'fveq2d', '( log ` ( %s / %s ) ) = ( log ` %s )' % (R74, R4225, R2524))], 'oveq2d',
           '( %s x. ( log ` ( %s / %s ) ) ) = ( %s x. ( log ` %s ) )' % (SH, R74, R4225, SH, R2524))
    ineq1 = s([s([lg], 'eqcomd', '( %s x. ( log ` %s ) ) = ( %s x. ( log ` ( %s / %s ) ) )' % (SH, R2524, SH, R74, R4225)), iq0], 'eqbrtrd',
              '( %s x. ( log ` %s ) ) <_ ( log ` ( B / %s ) )' % (SH, R2524, ALC))
    # B / abs F ( C0 ) <_ B / M : B >= abs F ( C0 ) >= M > 0
    INS = INTG(SA, SB, C0)
    ps_re = [re0, im0] + ps
    ins = s([c0, s([s([lin8(w, A0, ps_re, '( Re ` %s ) < ( Re ` %s )' % (SA, C0), lv), lin8(w, A0, ps_re, '( Re ` %s ) < ( Re ` %s )' % (C0, SB), lv)], 'jca',
                       '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (SA, C0, C0, SB)),
                     s([lin8(w, A0, ps_re, '( Im ` %s ) < ( Im ` %s )' % (SA, C0), lv), lin8(w, A0, ps_re, '( Im ` %s ) < ( Im ` %s )' % (C0, SB), lv)], 'jca',
                       '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (SA, C0, C0, SB))], 'jca', INS[len('( %s e. CC /\\ ' % C0):-2])], 'jca', INS)
    csq = w.s([s([sac, sbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), ins, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. %s )' % (A0, C0, SQ(C0, R74)))
    subx = w.s([w.s([], 'fveq2', '( x = %s -> ( F ` x ) = %s )' % (C0, LC))], 'fveq2d', '( x = %s -> ( abs ` ( F ` x ) ) = %s )' % (C0, ALC))
    subx2 = w.s([subx], 'breq1d', '( x = %s -> ( ( abs ` ( F ` x ) ) <_ B <-> %s <_ B ) )' % (C0, ALC))
    bge = w.s([subx2, fbx, csq], 'rspcdva', '( %s -> %s <_ B )' % (A0, ALC))
    lvb = {ALC: alr, 'M': mr, 'B': bre}
    bpos = lin8(w, A0, [bge, mle, mgt], '0 < B', lvb)
    brp = s([bre, bpos], 'elrpd', 'B e. RR+')
    alcp = s([alr, apos], 'elrpd', '%s e. RR+' % ALC)
    dle = s([mrp, alcp, bre, s([brp], 'rpge0d', '0 <_ B'), mle], 'lediv2ad', '( B / %s ) <_ ( B / M )' % ALC)
    q1p = s([brp, alcp], 'rpdivcld', '( B / %s ) e. RR+' % ALC)
    q2p = s([brp, mrp], 'rpdivcld', '( B / M ) e. RR+')
    ll = s([dle, s([q1p, q2p], 'logled', '( ( B / %s ) <_ ( B / M ) <-> ( log ` ( B / %s ) ) <_ ( log ` ( B / M ) ) )' % (ALC, ALC))], 'mpbid',
           '( log ` ( B / %s ) ) <_ ( log ` ( B / M ) )' % ALC)
    l25 = s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25)
    fin = s([s([shr, l25], 'remulcld', '( %s x. %s ) e. RR' % (SH, L25)), s([q1p], 'relogcld', '( log ` ( B / %s ) ) e. RR' % ALC),
             s([q2p], 'relogcld', '( log ` ( B / M ) ) e. RR'), ineq1, ll], 'letrd', '( %s x. %s ) <_ ( log ` ( B / M ) )' % (SH, L25))
    goal = S['jenstrip']
    assert goal == '( %s -> ( %s /\\ %s /\\ ( %s x. %s ) <_ ( log ` ( B / M ) ) ) )' % (A0, ZF_, ALQ, SH, L25), goal
    w.qed([zfin, alq, fin], '3jca', goal)
    return run8(w)


if __name__ == '__main__':
    gen_jenstrip()
