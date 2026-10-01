"""Sortie KD1: the geometry of the Cauchy squares about s0 = ( 1 + E ) + i T (kdgeo)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift
from lin import linarith, nlinarith, lineq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def corners(w, ante, C, Rs, cc, reC, imC, rr):
    """Re/Im of C -/+ ( Rs + i Rs ) given Re C = reC, Im C = imC steps (( ante -> ( Re ` C ) = .. ))"""
    a = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (ante, f))
    RI_ = '( %s + ( _i x. %s ) )' % (Rs, Rs)
    rc = a([rr], 'recnd', '%s e. CC' % Rs)
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ante)
    ric = a([rc, a([ic, rc], 'mulcld', '( _i x. %s ) e. CC' % Rs)], 'addcld', '%s e. CC' % RI_)
    crr = a([rr, rr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (RI_, Rs))
    cri = a([rr, rr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (RI_, Rs))
    out = {}
    lo, hi = QLO(C, Rs), QHI(C, Rs)
    out['lo'] = a([cc, ric], 'subcld', '%s e. CC' % lo); out['hi'] = a([cc, ric], 'addcld', '%s e. CC' % hi)
    for nm, op, lab, part, cr, cv in (('ReA', '-', 'resub', 'Re', crr, reC), ('ReB', '+', 'readd', 'Re', crr, reC), ('ImA', '-', 'imsub', 'Im', cri, imC), ('ImB', '+', 'imadd', 'Im', cri, imC)):
        X = lo if op == '-' else hi
        e1 = a([cc, ric, w.inst(lab)], 'syl2anc', '( %s ` %s ) = ( ( %s ` %s ) %s ( %s ` %s ) )' % (part, X, part, C, op, part, RI_))
        from cl import split_imp
        cvv = split_imp(formula_of(w, cv))[1].split(' = ', 1)[1]
        e2 = a([cv, cr], 'oveq12d', '( ( %s ` %s ) %s ( %s ` %s ) ) = ( %s %s %s )' % (part, C, op, part, RI_, cvv, op, Rs))
        out[nm] = a([e1, e2], 'eqtrd', '( %s ` %s ) = ( %s %s %s )' % (part, X, cvv, op, Rs))
    return out


def gen_geo():
    w = W('kdgeo', 'Geometry of the Cauchy squares about ` s0 = ( 1 + E ) + i T ` , ` 0 < E <_ 1 / 20 ` : ` SQ ( s0 , R ) ` ( ` 1 / 3 <_ R <_ 2 / 5 ` ) lies in the open ` 13 / 8 ` square about ` 2 + i T ` and within ` 3 / 2 ` of ` 2 + i T ` ; ` SQ ( s0 , E / 2 ) ` lies in that square and in ` Re > 1 + E / 4 ` .')
    A0 = S['kdgeo'].split(' -> ( ( ')[0][2:]
    s = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (A0, f))
    tr = s([], 'simp1', 'T e. RR'); ee = s([], 'simp2', '( E e. RR+ /\\ E <_ %s )' % R120); ri = s([], 'simp3', 'R e. ( ( 1 / 3 ) [,] ( 2 / 5 ) )')
    ep = s([ee], 'simpld', 'E e. RR+'); e20 = s([ee], 'simprd', 'E <_ %s' % R120)
    er = s([ep], 'rpred', 'E e. RR')
    c0 = Closure(w, A0, {'T': ('RR', tr), 'E': ('RR', er)})
    rel = s([ri, s([c0.mem('( 1 / 3 )', 'RR'), c0.mem('( 2 / 5 )', 'RR'), w.inst('elicc2')], 'syl2anc', '( R e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) <-> ( R e. RR /\\ ( 1 / 3 ) <_ R /\\ R <_ ( 2 / 5 ) ) )')],
            'mpbid', '( R e. RR /\\ ( 1 / 3 ) <_ R /\\ R <_ ( 2 / 5 ) )')
    rr = s([rel], 'simp1d', 'R e. RR'); r1 = s([rel], 'simp2d', '( 1 / 3 ) <_ R'); r2 = s([rel], 'simp3d', 'R <_ ( 2 / 5 )')
    e0 = s([ep], 'rpgt0d', '0 < E')
    c0.leaf('R', 'RR', rr)
    SS = S0(); CC_ = CT('T')
    oe = c0.mem('( 1 + E )', 'RR')
    s0c = s([s([oe], 'recnd', '( 1 + E ) e. CC'), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
             'addcld', '%s e. CC' % SS)
    rs0 = s([oe, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + E )' % SS)
    is0 = s([oe, tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % SS)
    two = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
    ccc = s([s([two], 'recnd', '2 e. CC'), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CC_)
    rc0 = s([two, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 2' % CC_)
    ic0 = s([two, tr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % CC_)
    r138 = c0.mem(R138, 'RR')
    K13 = corners(w, A0, CC_, R138, ccc, rc0, ic0, r138)
    KR = corners(w, A0, SS, 'R', s0c, rs0, is0, rr)
    E2 = '( E / 2 )'
    e2r = c0.mem(E2, 'RR')
    KE = corners(w, A0, SS, E2, s0c, rs0, is0, e2r)
    lin_ = lambda hyps, goal: linarith(w, A0, hyps, goal, closure=c0)
    def inside(K):
        lo, hi = QLO(SS, K['_R']), QHI(SS, K['_R'])
        return lo, hi
    def ORECT(Kc, Rs, hyps):
        lo, hi = QLO(SS, Rs), QHI(SS, Rs)
        for key, x in (('ReA', A13), ('ReB', B13), ('ImA', A13), ('ImB', B13)):
            pass
        A_, B_ = A13, B13
        g1 = lin_(hyps + [K13['ReA'], Kc['ReA']], '( Re ` %s ) < ( Re ` %s )' % (A_, lo))
        g2 = lin_(hyps + [K13['ReB'], Kc['ReB']], '( Re ` %s ) < ( Re ` %s )' % (hi, B_))
        g3 = lin_(hyps + [K13['ImA'], Kc['ImA']], '( Im ` %s ) < ( Im ` %s )' % (A_, lo))
        g4 = lin_(hyps + [K13['ImB'], Kc['ImB']], '( Im ` %s ) < ( Im ` %s )' % (hi, B_))
        j = s([s([g1, g2], 'jca', '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (A_, lo, hi, B_)),
               s([g3, g4], 'jca', '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (A_, lo, hi, B_))], 'jca',
              '( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )' % (A_, lo, hi, B_, A_, lo, hi, B_))
        return s([s([K13['lo'], K13['hi']], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), s([Kc['lo'], Kc['hi']], 'jca', '( %s e. CC /\\ %s e. CC )' % (lo, hi)), j, w.inst('crectorect')],
                 'syl3anc', '%s C_ %s' % (SQ(SS, Rs), O13))
    for e_ in ('( Re ` %s )' % x for x in (A13, B13, QLO(SS, 'R'), QHI(SS, 'R'), QLO(SS, E2), QHI(SS, E2))):
        pass
    for X in (A13, B13, QLO(SS, 'R'), QHI(SS, 'R'), QLO(SS, E2), QHI(SS, E2)):
        for part in ('Re', 'Im'):
            st = K13 if X in (A13, B13) else (KR if 'R' in X.split() else KE)
            xc = st['lo'] if X.startswith('( %s -' % (CC_ if X in (A13, B13) else SS)) else st['hi']
            c0.leaf('( %s ` %s )' % (part, X), 'RR', s([xc], 'recld' if part == 'Re' else 'imcld', '( %s ` %s ) e. RR' % (part, X)))
            c0.atom('( %s ` %s )' % (part, X))
    G1 = ORECT(KR, 'R', [r1, r2, e0, e20])
    G3 = ORECT(KE, E2, [e0, e20])
    # G4: SQ(s0, E/2) C_ HP(1 + E/4)
    loE, hiE = QLO(SS, E2), QHI(SS, E2)
    Az = '( %s /\\ z e. %s )' % (A0, SQ(SS, E2))
    a = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (Az, f))
    L = lambda st: lift(w, st, Az)
    ez = a([a([], 'simpr', 'z e. %s' % SQ(SS, E2)), a([L(KE['lo']), L(KE['hi']), w.inst('elcrect')], 'syl2anc',
                                                          '( z e. %s <-> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (SQ(SS, E2), loE, hiE, loE, hiE))],
           'mpbid', '( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (loE, hiE, loE, hiE))
    zc = a([ez], 'simp1d', 'z e. CC')
    zre = a([ez], 'simp2d', '( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (loE, hiE))
    rlo = L(c0.mem('( Re ` %s )' % loE, 'RR')); rhi = L(c0.mem('( Re ` %s )' % hiE, 'RR'))
    zre2 = a([zre, a([rlo, rhi, w.inst('elicc2')], 'syl2anc', '( ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) <-> ( ( Re ` z ) e. RR /\\ ( Re ` %s ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( Re ` %s ) ) )' % (loE, hiE, loE, hiE))],
             'mpbid', '( ( Re ` z ) e. RR /\\ ( Re ` %s ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ ( Re ` %s ) )' % (loE, hiE))
    zl = a([zre2], 'simp2d', '( Re ` %s ) <_ ( Re ` z )' % loE)
    cz = Closure(w, Az, {'E': ('RR', L(er)), '( Re ` %s )' % loE: ('RR', rlo), '( Re ` z )': ('RR', a([zre2], 'simp1d', '( Re ` z ) e. RR'))})
    cz.atom('( Re ` %s )' % loE); cz.atom('( Re ` z )')
    q1 = linarith(w, Az, [zl, L(KE['ReA']), L(e0)], '( 1 + ( E / 4 ) ) < ( Re ` z )', closure=cz)
    HQ = HP('( 1 + ( E / 4 ) )')
    zh = a([a([zc, q1], 'jca', '( z e. CC /\\ ( 1 + ( E / 4 ) ) < ( Re ` z ) )'), a([cz.mem('( 1 + ( E / 4 ) )', 'RR'), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ ( 1 + ( E / 4 ) ) < ( Re ` z ) ) )' % HQ)],
           'mpbird', 'z e. %s' % HQ)
    G4 = s([w.s([zh], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (A0, SQ(SS, E2), HQ))], 'ssrdv', '%s C_ %s' % (SQ(SS, E2), HQ))
    # G2: distance to 2 + i T
    loR, hiR = QLO(SS, 'R'), QHI(SS, 'R')
    Au = '( %s /\\ u e. %s )' % (A0, SQ(SS, 'R'))
    b = lambda h, r_, f: w.s(h, r_, '( %s -> %s )' % (Au, f))
    M = lambda st: lift(w, st, Au)
    eu = b([b([], 'simpr', 'u e. %s' % SQ(SS, 'R')), b([M(KR['lo']), M(KR['hi']), w.inst('elcrect')], 'syl2anc',
                                                         '( u e. %s <-> ( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (SQ(SS, 'R'), loR, hiR, loR, hiR))],
           'mpbid', '( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (loR, hiR, loR, hiR))
    uc = b([eu], 'simp1d', 'u e. CC')
    def bounds(part):
        mem = b([eu], 'simp2d' if part == 'Re' else 'simp3d', '( %s ` u ) e. ( ( %s ` %s ) [,] ( %s ` %s ) )' % (part, part, loR, part, hiR))
        lo_ = M(c0.mem('( %s ` %s )' % (part, loR), 'RR')); hi_ = M(c0.mem('( %s ` %s )' % (part, hiR), 'RR'))
        e_ = b([mem, b([lo_, hi_, w.inst('elicc2')], 'syl2anc', '( ( %s ` u ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( ( %s ` u ) e. RR /\\ ( %s ` %s ) <_ ( %s ` u ) /\\ ( %s ` u ) <_ ( %s ` %s ) ) )' % (
            part, part, loR, part, hiR, part, part, loR, part, part, part, hiR))], 'mpbid', '( ( %s ` u ) e. RR /\\ ( %s ` %s ) <_ ( %s ` u ) /\\ ( %s ` u ) <_ ( %s ` %s ) )' % (part, part, loR, part, part, part, hiR))
        return b([e_], 'simp1d', '( %s ` u ) e. RR' % part), b([e_], 'simp2d', '( %s ` %s ) <_ ( %s ` u )' % (part, loR, part)), b([e_], 'simp3d', '( %s ` u ) <_ ( %s ` %s )' % (part, part, hiR))
    rur, rul, ruh = bounds('Re'); iur, iul, iuh = bounds('Im')
    W_ = '( u - %s )' % CC_
    rw = b([uc, M(ccc)], 'resubd', '( Re ` %s ) = ( ( Re ` u ) - ( Re ` %s ) )' % (W_, CC_))
    iw = b([uc, M(ccc)], 'imsubd', '( Im ` %s ) = ( ( Im ` u ) - ( Im ` %s ) )' % (W_, CC_))
    wc = b([uc, M(ccc)], 'subcld', '%s e. CC' % W_)
    X = '( Re ` %s )' % W_; Y = '( Im ` %s )' % W_; AW = '( abs ` %s )' % W_
    cu = Closure(w, Au, {'E': ('RR', M(er)), 'T': ('RR', M(tr)), 'R': ('RR', M(rr)), '( Re ` u )': ('RR', rur), '( Im ` u )': ('RR', iur),
                         '( Re ` %s )' % loR: ('RR', M(c0.mem('( Re ` %s )' % loR, 'RR'))), '( Re ` %s )' % hiR: ('RR', M(c0.mem('( Re ` %s )' % hiR, 'RR'))),
                         '( Im ` %s )' % loR: ('RR', M(c0.mem('( Im ` %s )' % loR, 'RR'))), '( Im ` %s )' % hiR: ('RR', M(c0.mem('( Im ` %s )' % hiR, 'RR'))),
                         '( Re ` %s )' % CC_: ('RR', b([M(ccc)], 'recld', '( Re ` %s ) e. RR' % CC_)), '( Im ` %s )' % CC_: ('RR', b([M(ccc)], 'imcld', '( Im ` %s ) e. RR' % CC_)),
                         X: ('RR', b([wc], 'recld', '%s e. RR' % X)), Y: ('RR', b([wc], 'imcld', '%s e. RR' % Y)), AW: ('RR', b([wc], 'abscld', '%s e. RR' % AW))})
    for e_ in list(cu.leaves):
        if e_ not in ('E', 'T', 'R'):
            cu.atom(e_)
    hy = [rul, ruh, iul, iuh, M(KR['ReA']), M(KR['ReB']), M(KR['ImA']), M(KR['ImB']), M(rc0), M(ic0), rw, iw, M(r1), M(r2), M(e0), M(e20)]
    xl = linarith(w, Au, hy, '-u ( 7 / 5 ) <_ %s' % X, closure=cu)
    xh = linarith(w, Au, hy, '%s <_ ( 7 / 5 )' % X, closure=cu)
    yl = linarith(w, Au, hy, '-u ( 2 / 5 ) <_ %s' % Y, closure=cu)
    yh = linarith(w, Au, hy, '%s <_ ( 2 / 5 )' % Y, closure=cu)
    x2 = nlinarith(w, Au, [xl, xh], '( %s ^ 2 ) <_ ( ; 4 9 / ; 2 5 )' % X, closure=cu)
    y2 = nlinarith(w, Au, [yl, yh], '( %s ^ 2 ) <_ ( 4 / ; 2 5 )' % Y, closure=cu)
    av = b([wc, w.inst('absvalsq2')], 'syl', '( %s ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (AW, X, Y))
    cu.leaf('( %s ^ 2 )' % X, 'RR', b([cu.mem(X, 'RR')], 'resqcld', '( %s ^ 2 ) e. RR' % X)); cu.atom('( %s ^ 2 )' % X)
    cu.leaf('( %s ^ 2 )' % Y, 'RR', b([cu.mem(Y, 'RR')], 'resqcld', '( %s ^ 2 ) e. RR' % Y)); cu.atom('( %s ^ 2 )' % Y)
    cu.leaf('( %s ^ 2 )' % AW, 'RR', b([cu.mem(AW, 'RR')], 'resqcld', '( %s ^ 2 ) e. RR' % AW)); cu.atom('( %s ^ 2 )' % AW)
    a2 = linarith(w, Au, [av, x2, y2], '( %s ^ 2 ) <_ ( ( 3 / 2 ) ^ 2 )' % AW, closure=cu)
    le = b([cu.mem(AW, 'RR'), cu.mem('( 3 / 2 )', 'RR'), b([wc], 'absge0d', '0 <_ %s' % AW), cu.ge0('( 3 / 2 )')], 'le2sqd', '( %s <_ ( 3 / 2 ) <-> ( %s ^ 2 ) <_ ( ( 3 / 2 ) ^ 2 ) )' % (AW, AW))
    du = b([a2, le], 'mpbird', '%s <_ ( 3 / 2 )' % AW)
    G2 = s([du], 'ralrimiva', 'A. u e. %s %s <_ ( 3 / 2 )' % (SQ(SS, 'R'), '( abs ` ( u - %s ) )' % CC_))
    w.qed([s([G1, G2], 'jca', '( %s C_ %s /\\ A. u e. %s ( abs ` ( u - %s ) ) <_ ( 3 / 2 ) )' % (SQ(SS, 'R'), O13, SQ(SS, 'R'), CC_)),
           s([G3, G4], 'jca', '( %s C_ %s /\\ %s C_ %s )' % (SQ(SS, E2), O13, SQ(SS, E2), HQ))], 'jca', S['kdgeo'])
    return run(w)



if __name__ == '__main__':
    gen_geo()
