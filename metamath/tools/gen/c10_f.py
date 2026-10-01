"""Sortie C10: the zero count on one strip (lchrzq)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
import congr as _cg
import num
from c10_freeze import S as FS, ZR
from c8_n import sqparts, sqre_at, sqcc
from c8_o import numst, sqab_st
from c9_b import decode
import c9_h
patch_stmt(c9_h)
from c9_h import c0_facts, lf_hol
import lin
lin.FASTPATH = True

R38, R298 = '( 3 / 8 )', '( ; 2 9 / 8 )'


def crfacts(w, ante, re_t, im_t, rst, ist):
    """( re + i im ) e. CC, Re = re, Im = im"""
    E = '( %s + ( _i x. %s ) )' % (re_t, im_t)
    ec = w.s([w.s([rst], 'recnd', '( %s -> %s e. CC )' % (ante, re_t)), w.s([closed(w, ante, 'ax-icn', '_i e. CC'), w.s([ist], 'recnd', '( %s -> %s e. CC )' % (ante, im_t))], 'mulcld',
              '( %s -> ( _i x. %s ) e. CC )' % (ante, im_t))], 'addcld', '( %s -> %s e. CC )' % (ante, E))
    re_ = w.s([rst, ist], 'crred', '( %s -> ( Re ` %s ) = %s )' % (ante, E, re_t))
    im_ = w.s([rst, ist], 'crimd', '( %s -> ( Im ` %s ) = %s )' % (ante, E, im_t))
    return ec, re_, im_


def clo(w, ante, lv):
    import cl as _cl
    c = _cl.Closure(w, ante, {})
    for a, st in lv.items():
        c.leaf(a, 'RR', st)
    return c


def gen_lchrzq():
    w = W('lchrzq', 'The zeros of ` L ( s , chi ) ` , ` chi ` nonprincipal, in the strip ` [ 3 / 8 , 29 / 8 ] x. [ T - 13 / 32 , T + 13 / 32 ] ` have multiplicity mass at most ` log ( 40 N ( abs T + 2 ) ) / log ( 25 / 24 ) ` : ~ jenrct at ` C = 2 + i T ` , ` R = 7 / 4 ` , ` V = 42 / 25 ` ( ~ lchrsqb , ~ lchrctr ).')
    A0 = '( %s /\\ T e. RR )' % CHI
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tr = s([], 'simpr', 'T e. RR')
    c0, re0, im0 = c0_facts(w, A0, tr)
    hol = lf_hol(w, A0, chi)
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
    # the outer rectangle inside SQ ( C0 , 7 / 4 ) inside HP0
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
    X1, X2, X3 = top_and(csa)
    oss = s([s([sab, s([oa, ob], 'jca', X2), s([s([i1, i2], 'jca', top_and(X3)[0]), s([i3, i4], 'jca', top_and(X3)[1])], 'jca', X3)], '3jca', csa), w.inst('crectss2')], 'syl', csc)
    lt = s([lin8(w, A0, [], '%s < 2' % R74, {}), re0], 'breqtrrd', '%s < ( Re ` %s )' % (R74, C0))
    f = tsub(stmt('sqhp0'), {'C': C0, 'R': R74})
    fa, fc = ante_of(f)
    shp = s([s([s([c0, r74], 'jca', '( %s e. CC /\\ %s e. RR )' % (C0, R74)), lt], 'jca', fa), w.inst('sqhp0')], 'syl', fc)
    ohp = s([oss, shp], 'sstrd', '( %s crect %s ) C_ %s' % (OA, OB, HP0))
    JR = tsub(FS['jenrct'], {'F': LFN, 'D': HP0, 'A': QAt, 'B': QBt, 'M': R18, 'C': C0, 'R': R74, 'V': R4225, 'Y': B20})
    jra, jrc = ante_of(JR)
    J1, J2, J3 = top_and(jra)
    j1 = s([hol, s([s([qac, qbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (QAt, QBt)), geo], 'jca', top_and(J1)[1]), s([numst(w, A0, R18, 'RR+'), ohp], 'jca', top_and(J1)[2])], '3jca', J1)
    # J2
    K1, K2, K3 = top_and(J2)
    INT = INTG(QAt, QBt, C0)
    lvs = [reA, reB, imA, imB, re0, im0]
    it = s([c0, s([s([lin8(w, A0, lvs, '( Re ` %s ) < ( Re ` %s )' % (QAt, C0), lv), lin8(w, A0, lvs, '( Re ` %s ) < ( Re ` %s )' % (C0, QBt), lv)], 'jca',
                      '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (QAt, C0, C0, QBt)),
                    s([lin8(w, A0, lvs, '( Im ` %s ) < ( Im ` %s )' % (QAt, C0), lv), lin8(w, A0, lvs, '( Im ` %s ) < ( Im ` %s )' % (C0, QBt), lv)], 'jca',
                      '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (QAt, C0, C0, QBt))], 'jca', INT[len('( %s e. CC /\\ ' % C0):-2])], 'jca', INT)
    cq = w.s([s([qac, qbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (QAt, QBt)), it, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. ( %s crect %s ) )' % (A0, C0, QAt, QBt))
    lb = s([s([chi, tr], 'jca', A0), w.inst('lchrctr')], 'syl', '( 1 / 2 ) <_ ( abs ` ( %s ` %s ) )' % (LFN, C0))
    LC = '( %s ` %s )' % (LFN, C0)
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)),
             s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))], 'mpbird', '%s e. %s' % (C0, HP0))
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), c0h], 'ffvelcdmd', '%s e. CC' % LC)
    alr = s([lfc], 'abscld', '( abs ` %s ) e. RR' % LC)
    apos = lin8(w, A0, [lb], '0 < ( abs ` %s )' % LC, {'( abs ` %s )' % LC: alr})
    lne = s([apos, s([lfc, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (LC, LC))], 'mpbird', '%s =/= 0' % LC)
    k1 = s([cq, lne], 'jca', K1)
    k2 = s([numst(w, A0, R74, 'RR+'), shp], 'jca', K2)
    # the disc: every point of the strip is within 42 / 25 of C0
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
    R138_ = R138
    f1 = lin8(w, Aj, hj, '0 <_ ( %s - %s )' % (R138_, RD), lvj); f2 = lin8(w, Aj, hj, '0 <_ ( %s + %s )' % (R138_, RD), lvj)
    f3 = lin8(w, Aj, hj, '0 <_ ( %s - %s )' % (R1332, ID), lvj); f4 = lin8(w, Aj, hj, '0 <_ ( %s + %s )' % (R1332, ID), lvj)
    def rr_(e):
        c = clo(w, Aj, lvj); return c.mem(e, 'RR')
    h1 = sj([rr_('( %s - %s )' % (R138_, RD)), rr_('( %s + %s )' % (R138_, RD)), f1, f2], 'mulge0d', '0 <_ ( ( %s - %s ) x. ( %s + %s ) )' % (R138_, RD, R138_, RD))
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
    # J3: the bound on SQ ( C0 , 7 / 4 )
    SQC = SQ(C0, R74)
    Ax = '( %s /\\ x e. %s )' % (A0, SQC)
    SB = tsub(stmt('lchrsqb'), {'U': 'x'})
    sba, sbc_ = ante_of(SB)
    sbx = w.s([w.s([w.s([lift(w, chi, Ax), lift(w, tr, Ax)], 'jca', '( %s -> ( %s /\\ T e. RR ) )' % (Ax, CHI)), w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, SQC))], 'jca', '( %s -> %s )' % (Ax, sba)),
               w.inst('lchrsqb')], 'syl', '( %s -> %s )' % (Ax, sbc_))
    fbx = s([sbx], 'ralrimiva', 'A. x e. %s %s' % (SQC, sbc_))
    nn = s([s([chi, w.inst('simpl')], 'syl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), w.inst('simpl')], 'syl', 'N e. NN')
    nr = s([nn], 'nnred', 'N e. RR')
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    at2 = s([atr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '( ( abs ` T ) + 2 ) e. RR')
    b20r = s([s([numst(w, A0, '; 2 0', 'RR'), nr], 'remulcld', '( ; 2 0 x. N ) e. RR'), at2], 'remulcld', '%s e. RR' % B20)
    j3 = s([b20r, fbx], 'jca', J3)
    jr = s([s([j1, j2, j3], '3jca', jra), w.inst('jenrct')], 'syl', jrc)
    ZF, ALQ, INEQ0 = top_and(jrc)
    zfin = s([jr, w.inst('simp1')], 'syl', ZF); alq = s([jr, w.inst('simp2')], 'syl', ALQ); iq0 = s([jr, w.inst('simp3')], 'syl', INEQ0)
    ZQT = ZQ('T')
    SH = 'sum_ q e. %s ( %s holord q )' % (ZQT, LFN)
    Aq = '( %s /\\ q e. %s )' % (A0, ZQT)
    hqn = w.s([alq], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Aq, LFN))
    shr = s([zfin, w.s([hqn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Aq, LFN))], 'fsumrecl', '%s e. RR' % SH)
    # ( 7 / 4 ) / ( 42 / 25 ) = 25 / 24
    ml = num.mul_lits(w, R4225, R2524)
    v4c = numst(w, A0, R4225, 'CC'); v4n = s([numst(w, A0, R4225, 'RR+')], 'rpne0d', '%s =/= 0' % R4225)
    dmu = s([s([numst(w, A0, R74, 'CC'), numst(w, A0, R2524, 'CC'), s([v4c, v4n], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (R4225, R4225))], '3jca',
               '( %s e. CC /\\ %s e. CC /\\ ( %s e. CC /\\ %s =/= 0 ) )' % (R74, R2524, R4225, R4225)), w.inst('divmul')], 'syl',
            '( ( %s / %s ) = %s <-> ( %s x. %s ) = %s )' % (R74, R4225, R2524, R4225, R2524, R74))
    rv = s([w.s([ml], 'a1i', '( %s -> ( %s x. %s ) = %s )' % (A0, R4225, R2524, R74)), dmu], 'mpbird', '( %s / %s ) = %s' % (R74, R4225, R2524))
    lg = s([s([rv], 'fveq2d', '( log ` ( %s / %s ) ) = ( log ` %s )' % (R74, R4225, R2524))], 'oveq2d',
           '( %s x. ( log ` ( %s / %s ) ) ) = ( %s x. ( log ` %s ) )' % (SH, R74, R4225, SH, R2524))
    ineq1 = s([s([lg], 'eqcomd', '( %s x. ( log ` %s ) ) = ( %s x. ( log ` ( %s / %s ) ) )' % (SH, R2524, SH, R74, R4225)), iq0], 'eqbrtrd',
              '( %s x. ( log ` %s ) ) <_ ( log ` ( %s / ( abs ` %s ) ) )' % (SH, R2524, B20, LC))
    # B20 / abs L ( C0 ) <_ B40
    ALC = '( abs ` %s )' % LC
    nrp = s([nn], 'nnrpd', 'N e. RR+')
    AT2 = '( ( abs ` T ) + 2 )'
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    at2p = s([at2, lin8(w, A0, [ag0], '0 < %s' % AT2, {'( abs ` T )': atr})], 'elrpd', '%s e. RR+' % AT2)
    xtp = s([nrp, at2p], 'rpmulcld', '%s e. RR+' % XT)
    b40p = s([numst(w, A0, '; 4 0', 'RR+'), xtp], 'rpmulcld', '%s e. RR+' % B40)
    b20p = s([s([numst(w, A0, '; 2 0', 'RR+'), nrp], 'rpmulcld', '( ; 2 0 x. N ) e. RR+'), at2p], 'rpmulcld', '%s e. RR+' % B20)
    alcp = s([alr, apos], 'elrpd', '%s e. RR+' % ALC)
    qp = s([b20p, alcp], 'rpdivcld', '( %s / %s ) e. RR+' % (B20, ALC))
    b2x = s([s([numst(w, A0, '; 2 0', 'CC'), s([nr], 'recnd', 'N e. CC'), s([at2], 'recnd', '%s e. CC' % AT2)], 'mulassd', '%s = ( ; 2 0 x. %s )' % (B20, XT))], 'eqcomd',
              '( ; 2 0 x. %s ) = %s' % (XT, B20))
    xtr = s([xtp], 'rpred', '%s e. RR' % XT)
    hint = s([s([alr, numst(w, A0, '( 1 / 2 )', 'RR')], 'resubcld', '( %s - ( 1 / 2 ) ) e. RR' % ALC), xtr,
              lin8(w, A0, [lb], '0 <_ ( %s - ( 1 / 2 ) )' % ALC, {ALC: alr}), s([xtp], 'rpge0d', '0 <_ %s' % XT)], 'mulge0d', '0 <_ ( ( %s - ( 1 / 2 ) ) x. %s )' % (ALC, XT))
    b20r2 = s([b20p], 'rpred', '%s e. RR' % B20)
    lvb = {ALC: alr, XT: xtr, B20: b20r2}
    ml2 = lin.linarith(w, A0, [b2x, hint], '%s <_ ( %s x. %s )' % (B20, ALC, B40), closure=clo(w, A0, lvb), products=True)
    dl = s([ml2, s([b20r2, s([b40p], 'rpred', '%s e. RR' % B40), alcp], 'ledivmuld', '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B20, ALC, B40, B20, ALC, B40))], 'mpbird',
           '( %s / %s ) <_ %s' % (B20, ALC, B40))
    ll = s([dl, s([qp, b40p], 'logled', '( ( %s / %s ) <_ %s <-> ( log ` ( %s / %s ) ) <_ ( log ` %s ) )' % (B20, ALC, B40, B20, ALC, B40))], 'mpbid',
           '( log ` ( %s / %s ) ) <_ ( log ` %s )' % (B20, ALC, B40))
    l25 = s([numst(w, A0, R2524, 'RR+')], 'relogcld', '( log ` %s ) e. RR' % R2524)
    fin = s([s([shr, l25], 'remulcld', '( %s x. ( log ` %s ) ) e. RR' % (SH, R2524)), s([qp], 'relogcld', '( log ` ( %s / %s ) ) e. RR' % (B20, ALC)),
             s([b40p], 'relogcld', '( log ` %s ) e. RR' % B40), ineq1, ll], 'letrd', '( %s x. ( log ` %s ) ) <_ ( log ` %s )' % (SH, R2524, B40))
    goal = FS['lchrzq']
    assert goal == '( %s -> ( %s /\\ %s /\\ ( %s x. ( log ` %s ) ) <_ ( log ` %s ) ) )' % (A0, ZF, ALQ, SH, R2524, B40), goal
    w.qed([zfin, alq, fin], '3jca', goal)
    return run8(w)


if __name__ == '__main__':
    gen_lchrzq()
