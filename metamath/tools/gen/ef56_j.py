"""Sortie EF56: the zeta contour identity (ef6id; Lean contour_zeta hmaster)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts


def gen_id():
    w = W('ef6id', 'The contour identity of Lean ` contour_zeta ` ( ` hmaster ` ): the residue identities of ` eta ` and ` g ` on the rectangle ` [ S , c ] x [ - U , V ] ` ( ~ ef6rid ) subtracted, the right edges of the difference integrand split at ` +- T ` ( ~ ef6ldf , ~ ef4vsl ), the middle minus the Perron sum ( ~ ef6rm ).')
    A0, G = ante_of(S['ef6id'])
    c = Ctx(w, A0)
    g = c.g
    yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    ur = g('U e. RR'); vr = g('V e. RR'); tu = g('T <_ U'); tv = g('T <_ V')
    sr = g('S e. RR'); s916 = g('( 9 / ; 1 6 ) <_ S'); sc1 = g('S < %s' % C1)
    f = c1_facts(w, c, yr, y100)
    lvn = {'T': tr, 'U': ur, 'V': vr, 'S': sr}
    nur, ntr = c([ur], 'renegcld', '-u U e. RR'), c([tr], 'renegcld', '-u T e. RR')
    # the two residue identities
    def rid(F, ddlab):
        ddst = c.a1(w.s([], ddlab, DD(F, '1')), DD(F, '1'))
        R = tsub(stmt('ef6rid'), {'F': F, 'A': '1'})
        ra, rc = ante_of(R)
        st = c([rebuild(w, c, ra, {DD(F, '1'): ddst}), w.inst('ef6rid')], 'syl', rc)
        e, cls = top_and(rc)
        eq = c([st, w.inst('simpl')], 'syl', e)
        cl2 = c([st, w.inst('simpr')], 'syl', cls)
        a, b = top_and(cls)
        a1_, a2_ = conj_split(w, A0, c([cl2, w.inst('simpl')], 'syl', a))
        b1_, b2_ = conj_split(w, A0, c([cl2, w.inst('simpr')], 'syl', b))
        return eq, a1_, a2_, b1_, b2_
    eqE, botE, topE, leftE, rE = rid(ETA, 'ef2dde')
    eqG, botG, topG, leftG, rG = rid(GF, 'ef2ddg')
    # the right edge is in D2
    def vline(lo, hi, lor, hir):
        At = '( %s /\\ l e. ( %s [,] %s ) )' % (A0, lo, hi)
        ct = Ctx(w, At)
        tin = ct([], 'simpr', 'l e. ( %s [,] %s )' % (lo, hi))
        trr, _, _ = icc_out(ct, 'l', lo, hi, tin, lift(w, lor, At), lift(w, hir, At))
        z = PTL(C1, 'l')
        zc = ptc(ct, C1, 'l', lift(w, f['c1r'], At), trr)
        rz = ct([lift(w, f['c1r'], At), trr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (z, C1))
        r1 = ct([lift(w, f['c1g'], At), ct([rz], 'eqcomd', '%s = ( Re ` %s )' % (C1, z))], 'breqtrd', '1 < ( Re ` %s )' % z)
        PTS = tsub(S['ef6pt'], {'Z': z})
        pa, pc = ante_of(PTS)
        pt = ct([ct([lift(w, f['yp'], At), ct([zc, r1], 'jca', top_and(pa)[1])], 'jca', pa), w.inst('ef6pt')], 'syl', pc)
        mem = ct([pt, w.inst('simpl')], 'syl', '%s e. %s' % (z, D2))
        al = c([mem], 'ralrimiva', 'A. l e. ( %s [,] %s ) %s e. %s' % (lo, hi, z, D2))
        cb, _ = cbvral(w, '( %s [,] %s )' % (lo, hi), 'l', 't', '%s e. %s' % (z, D2))
        return c([al, c.a1(cb, '( A. l e. ( %s [,] %s ) %s e. %s <-> A. t e. ( %s [,] %s ) %s e. %s )' % (lo, hi, z, D2, lo, hi, PTL(C1, 't'), D2))], 'mpbid', 'A. t e. ( %s [,] %s ) %s e. %s' % (lo, hi, PTL(C1, 't'), D2))
    def inicc(x, lo, hi, xr, lor, hir, l1, l2):
        return icc_in(c, x, lo, hi, xr, lor, hir, l1, l2)
    uvl = lin8(w, A0, [tu, tv, t2], '-u U <_ V', lvn)
    nuin = inicc('-u U', '-u U', 'V', nur, nur, vr, c([nur], 'leidd', '-u U <_ -u U'), uvl)
    vin = inicc('V', '-u U', 'V', vr, nur, vr, uvl, c([vr], 'leidd', 'V <_ V'))
    ntin = inicc('-u T', '-u U', 'V', ntr, nur, vr, lin8(w, A0, [tu], '-u U <_ -u T', lvn), lin8(w, A0, [tv, t2], '-u T <_ V', lvn))
    ptin = inicc('T', '-u U', 'V', tr, nur, vr, lin8(w, A0, [tu, t2], '-u U <_ T', lvn), tv)
    allR = vline('-u U', 'V', nur, vr)
    def vseg(a, b, ain, bin_):
        VS = tsub(stmt('ef3vseg'), {'P': C1, 'L': '-u U', 'H': 'V', 'E': a, 'K': b, 'D': D2})
        va, vcn = ante_of(VS)
        return c([conj(w, A0, va, {'%s e. RR' % C1: f['c1r'], '-u U e. RR': nur, 'V e. RR': vr, '%s e. ( -u U [,] V )' % a: ain, '%s e. ( -u U [,] V )' % b: bin_,
                                   top_and(top_and(va)[1])[1]: allR}), w.inst('ef3vseg')], 'syl', vcn)
    P_ = PTL
    reals = {'-u U': nur, 'V': vr, '-u T': ntr, 'T': tr}
    pcc = lambda y: ptc(c, C1, y, f['c1r'], reals[y])
    # HD continuity and RE - RG = HD lint R
    he = c([hol_eta(w, A0), f['yp'], w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (HE, LD0E))
    hg = c([hol_gf(w, A0), f['yp'], w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (HG, LD0G))
    AR, BR = P_(C1, '-u U'), P_(C1, 'V')
    LF = tsub(stmt('ef6ldf'), {'A': AR, 'B': BR, 'F': HE, 'G': HG, 'D': LD0E, 'E': LD0G})
    la, lc_ = ante_of(LF)
    ldf = c([c([c([pcc('-u U'), pcc('V')], 'jca', top_and(la)[0]), c([he, hg], 'jca', top_and(la)[1]), vseg('-u U', 'V', nuin, vin)], '3jca', la), w.inst('ef6ldf')], 'syl', lc_)
    hcn = c([ldf, w.inst('simpl')], 'syl', top_and(lc_)[0])
    HDR = '( %s lint <. %s , %s >. )' % (HD, AR, BR)
    dRE = c([ldf, w.inst('simpr')], 'syl', '%s = ( %s - %s )' % (HDR, EDG['RE'], EDG['RG']))
    # split HD's right edge
    def vsl(P, Q, R, pr_, qr_, rr_, l1, l2, l3, allst):
        V1 = tsub(stmt('ef4vsl'), {'G': HD, 'D': D2, 'C': C1, 'P': P, 'Q': Q, 'R': R})
        v1a, v1c = ante_of(V1)
        return c([conj(w, A0, v1a, {'%s e. ( %s -cn-> CC )' % (HD, D2): hcn, '%s e. RR' % C1: f['c1r'], '%s e. RR' % P: pr_, '%s e. RR' % Q: qr_, '%s e. RR' % R: rr_,
                                    '%s <_ %s' % (P, Q): l1, '%s <_ %s' % (Q, R): l2, '%s < %s' % (P, R): l3, top_and(v1a)[2]: allst}), w.inst('ef4vsl')], 'syl', v1c)
    s1 = vsl('-u U', '-u T', 'V', nur, ntr, vr, lin8(w, A0, [tu], '-u U <_ -u T', lvn), lin8(w, A0, [tv, t2], '-u T <_ V', lvn), lin8(w, A0, [tu, tv, t2], '-u U < V', lvn), allR)
    allTV = vline('-u T', 'V', ntr, vr)
    s2 = vsl('-u T', 'T', 'V', ntr, tr, vr, lin8(w, A0, [t2], '-u T <_ T', lvn), tv, lin8(w, A0, [tv, t2], '-u T < V', lvn), allTV)
    MIDD = '( %s lint <. %s , %s >. )' % (HD, P_(C1, '-u T'), P_(C1, 'T'))
    R2 = '( %s lint <. %s , %s >. )' % (HD, P_(C1, '-u T'), P_(C1, 'V'))
    RM = tsub(stmt('ef6rm'), {'C': C1})
    rma, rmc = ante_of(RM)
    rm = c([conj(w, A0, rma, {'Y e. RR+': f['yp'], '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g'], 'T e. RR': tr}), w.inst('ef6rm')], 'syl', rmc)
    # PSZ e. CC
    RE_ = tsub(stmt('ef1redge'), dict(Z1S, C=C1))
    rea, rec_ = ante_of(RE_)
    red = c([conj(w, A0, rea, {'( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1: nx1(w, A0), 'Y e. RR+': f['yp'], '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g'], 'T e. RR': tr}), w.inst('ef1redge')], 'syl', rec_)
    cv, pse = top_and(rec_)
    RHL = pse.split(' = ', 1)[1]
    rhc = c([c([red, w.inst('simpl')], 'syl', cv), w.inst('climcl')], 'syl', '%s e. CC' % RHL)
    psc = c([c([red, w.inst('simpr')], 'syl', pse), rhc], 'eqeltrd', '%s e. CC' % PSZ1)
    # EBD, ETD e. CC
    def lcl(a, b, ain, bin_, ya, yb):
        seg = vseg(ya, yb, ain, bin_)
        return c([c([c([pcc(ya), pcc(yb)], 'jca', '( %s e. CC /\\ %s e. CC )' % (a, b)), c([hcn, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (HD, D2, a, b, D2))], 'jca',
                    '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (a, b, HD, D2, a, b, D2)), w.inst('lintcl')], 'syl', '( %s lint <. %s , %s >. ) e. CC' % (HD, a, b))
    ebc = lcl(P_(C1, '-u U'), P_(C1, '-u T'), nuin, ntin, '-u U', '-u T')
    etc_ = lcl(P_(C1, 'T'), P_(C1, 'V'), ptin, vin, 'T', 'V')
    # algebra: RE = RG + ( EBD + ( -u PSZ + ETD ) )
    e_r2 = c([s2, c([rm], 'oveq1d', '( %s + %s ) = ( -u %s + %s )' % (MIDD, ETD, PSZ1, ETD))], 'eqtrd', '%s = ( -u %s + %s )' % (R2, PSZ1, ETD))
    e_r = c([s1, c([e_r2], 'oveq2d', '( %s + %s ) = ( %s + ( -u %s + %s ) )' % (EBD, R2, EBD, PSZ1, ETD))], 'eqtrd', '%s = ( %s + ( -u %s + %s ) )' % (HDR, EBD, PSZ1, ETD))
    QQ = '( %s + ( -u %s + %s ) )' % (EBD, PSZ1, ETD)
    dq = c([c([dRE], 'eqcomd', '( %s - %s ) = %s' % (EDG['RE'], EDG['RG'], HDR)), e_r], 'eqtrd', '( %s - %s ) = %s' % (EDG['RE'], EDG['RG'], QQ))
    qc = c([ebc, c([c([psc], 'negcld', '-u %s e. CC' % PSZ1), etc_], 'addcld', '( -u %s + %s ) e. CC' % (PSZ1, ETD))], 'addcld', '%s e. CC' % QQ)
    reeq = c([dq, c([rE, rG, qc, w.inst('subadd2')], 'syl3anc' if False else 'x', 'x')], 'x', 'x') if False else None
    reeq = c([c([rE, rG, qc], 'subaddd', '( ( %s - %s ) = %s <-> ( %s + %s ) = %s )' % (EDG['RE'], EDG['RG'], QQ, EDG['RG'], QQ, EDG['RE'])), dq], 'mpbid', '( %s + %s ) = %s' % (EDG['RG'], QQ, EDG['RE']))
    X1 = '( ( ( %s + %s ) - %s ) - %s )' % (EDG['BOTE'], EDG['RE'], EDG['TOPE'], EDG['LEFTE'])
    X1b = '( ( ( %s + ( %s + %s ) ) - %s ) - %s )' % (EDG['BOTE'], EDG['RG'], QQ, EDG['TOPE'], EDG['LEFTE'])
    x1eq = c([c([c([c([reeq], 'eqcomd', '%s = ( %s + %s )' % (EDG['RE'], EDG['RG'], QQ))], 'oveq2d', '( %s + %s ) = ( %s + ( %s + %s ) )' % (EDG['BOTE'], EDG['RE'], EDG['BOTE'], EDG['RG'], QQ))],
                'oveq1d', '( ( %s + %s ) - %s ) = ( ( %s + ( %s + %s ) ) - %s )' % (EDG['BOTE'], EDG['RE'], EDG['TOPE'], EDG['BOTE'], EDG['RG'], QQ, EDG['TOPE']))], 'oveq1d', '%s = %s' % (X1, X1b))
    X2 = '( ( ( %s + %s ) - %s ) - %s )' % (EDG['BOTG'], EDG['RG'], EDG['TOPG'], EDG['LEFTG'])
    X1c = c([eqE, c([c([c([botE, rE], 'addcld', '( %s + %s ) e. CC' % (EDG['BOTE'], EDG['RE'])), topE], 'subcld', '( ( %s + %s ) - %s ) e. CC' % (EDG['BOTE'], EDG['RE'], EDG['TOPE'])), leftE], 'subcld', '%s e. CC' % X1)], 'x', 'x') if False else None
    e1 = c([eqE, x1eq], 'eqtrd', '( %s x. %s ) = %s' % (TPI, SRE, X1b))
    lhs = c([c([e1, eqG], 'oveq12d', '( ( %s x. %s ) - ( %s x. %s ) ) = ( %s - %s )' % (TPI, SRE, TPI, SRG, X1b, X2))], 'oveq2d', '%s = ( %s + ( %s - %s ) )' % (IDL, PSZ1, X1b, X2))
    cl = Closure(w, A0, {EDG['BOTE']: ('CC', botE), EDG['BOTG']: ('CC', botG), EDG['TOPE']: ('CC', topE), EDG['TOPG']: ('CC', topG), EDG['LEFTE']: ('CC', leftE), EDG['LEFTG']: ('CC', leftG),
                         EDG['RG']: ('CC', rG), EBD: ('CC', ebc), ETD: ('CC', etc_), PSZ1: ('CC', psc)})
    for k in (EDG['BOTE'], EDG['BOTG'], EDG['TOPE'], EDG['TOPG'], EDG['LEFTE'], EDG['LEFTG'], EDG['RG'], EBD, ETD, PSZ1):
        cl.atom(k)
    rq = ringeq(w, A0, '( %s + ( %s - %s ) )' % (PSZ1, X1b, X2), IDR, cl)
    ident = c([lhs, rq], 'eqtrd', '%s = %s' % (IDL, IDR))
    clos = c([c([c([botE, botG], 'jca', '( %s e. CC /\\ %s e. CC )' % (EDG['BOTE'], EDG['BOTG'])), c([topE, topG], 'jca', '( %s e. CC /\\ %s e. CC )' % (EDG['TOPE'], EDG['TOPG']))], 'jca', top_and(IDC)[0]),
              c([c([leftE, leftG], 'jca', '( %s e. CC /\\ %s e. CC )' % (EDG['LEFTE'], EDG['LEFTG'])), c([ebc, etc_], 'jca', '( %s e. CC /\\ %s e. CC )' % (EBD, ETD))], 'jca', top_and(IDC)[1]), psc], '3jca', IDC)
    w.qed([ident, clos], 'jca', S['ef6id'])
    return run8(w)


GENS = {'ef6id': gen_id}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
