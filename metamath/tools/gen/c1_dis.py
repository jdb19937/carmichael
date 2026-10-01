"""Sortie C1 section 5.1: the distance from a strictly interior point to the
boundary frame of a rectangle."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

RP = RE('P'); IP = IM('P')
INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
RBD = '( R e. RR /\\ ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (
    RP, RA, RB, RP, IP, IA, IB, IP)

# ---- csegdisi / csegdisr ---------------------------------------------------
for lab, CO, eqlem, abslem, sublem, desc in (
        ('csegdisi', 'Im', 'cseghim', 'absimle', 'imsubd',
         'On a horizontal segment every point is at least as far from P as the '
         'difference of the imaginary parts.'),
        ('csegdisr', 'Re', 'csegvre', 'absrele', 'resubd',
         'On a vertical segment every point is at least as far from P as the '
         'difference of the real parts.')):
    w = W(lab, desc)
    CS = '( %s ` S )' % CO; CT = '( %s ` T )' % CO; CPP = '( %s ` P )' % CO
    GEOH = '( S e. CC /\\ T e. CC /\\ %s = %s )' % (CS, CT)
    HYP = '( P e. CC /\\ R e. RR /\\ R <_ ( abs ` ( %s - %s ) ) )' % (CS, CPP)
    A0 = '( %s /\\ %s )' % (GEOH, HYP)
    A1 = '( %s /\\ u e. ( S cseg T ) )' % A0
    h1 = w.s([], 'simpl', '( %s -> %s )' % (A0, GEOH))
    h2 = w.s([], 'simpr', '( %s -> %s )' % (A0, HYP))
    sc = w.s([h1, w.inst('simp1')], 'syl', '( %s -> S e. CC )' % A0)
    tc = w.s([h1, w.inst('simp2')], 'syl', '( %s -> T e. CC )' % A0)
    pc = w.s([h2, w.inst('simp1')], 'syl', '( %s -> P e. CC )' % A0)
    rr = w.s([h2, w.inst('simp2')], 'syl', '( %s -> R e. RR )' % A0)
    rle = w.s([h2, w.inst('simp3')], 'syl', '( %s -> R <_ ( abs ` ( %s - %s ) ) )' % (A0, CS, CPP))
    him = w.s([h1, w.inst(eqlem)], 'syl', '( %s -> A. u e. ( S cseg T ) %s = %s )' % (A0, '( %s ` u )' % CO, CS))
    ucl = w.s([sc, tc, w.inst('csegcl')], 'syl2anc', '( %s -> ( S cseg T ) C_ CC )' % A0)
    umem = w.s([], 'simpr', '( %s -> u e. ( S cseg T ) )' % A1)
    uc = w.s([w.s([ucl], 'adantr', '( %s -> ( S cseg T ) C_ CC )' % A1), umem], 'sseldd', '( %s -> u e. CC )' % A1)
    pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
    imu = w.s([w.s([him], 'adantr', '( %s -> A. u e. ( S cseg T ) %s = %s )' % (A1, '( %s ` u )' % CO, CS)), umem, w.inst('rspa')],
              'syl2anc', '( %s -> %s = %s )' % (A1, '( %s ` u )' % CO, CS))
    upc = w.s([uc, pc1], 'subcld', '( %s -> ( u - P ) e. CC )' % A1)
    ims = w.s([uc, pc1], sublem, '( %s -> ( %s ` ( u - P ) ) = ( %s - %s ) )' % (A1, CO, '( %s ` u )' % CO, CPP))
    eq = w.s([ims, w.s([imu], 'oveq1d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (A1, '( %s ` u )' % CO, CPP, CS, CPP))],
             'eqtrd', '( %s -> ( %s ` ( u - P ) ) = ( %s - %s ) )' % (A1, CO, CS, CPP))
    le1 = w.s([upc, w.inst(abslem)], 'syl', '( %s -> ( abs ` ( %s ` ( u - P ) ) ) <_ ( abs ` ( u - P ) ) )' % (A1, CO))
    le2 = w.s([w.s([eq], 'fveq2d', '( %s -> ( abs ` ( %s ` ( u - P ) ) ) = ( abs ` ( %s - %s ) ) )' % (A1, CO, CS, CPP)), le1],
              'eqbrtrrd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( u - P ) ) )' % (A1, CS, CPP))
    scd = w.s([w.s([w.s([sc], 'adantr', '( %s -> S e. CC )' % A1)], '%scld' % CO.lower(), '( %s -> %s e. RR )' % (A1, CS))], 'recnd', '( %s -> %s e. CC )' % (A1, CS))
    pcd = w.s([w.s([pc1], '%scld' % CO.lower(), '( %s -> %s e. RR )' % (A1, CPP))], 'recnd', '( %s -> %s e. CC )' % (A1, CPP))
    arr = w.s([w.s([scd, pcd], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A1, CS, CPP))], 'abscld', '( %s -> ( abs ` ( %s - %s ) ) e. RR )' % (A1, CS, CPP))
    urr = w.s([upc], 'abscld', '( %s -> ( abs ` ( u - P ) ) e. RR )' % A1)
    fin = w.s([w.s([rr], 'adantr', '( %s -> R e. RR )' % A1), arr, urr, w.s([rle], 'adantr', '( %s -> R <_ ( abs ` ( %s - %s ) ) )' % (A1, CS, CPP)), le2],
              'letrd', '( %s -> R <_ ( abs ` ( u - P ) ) )' % A1)
    w.qed([fin], 'ralrimiva', '( %s -> A. u e. ( S cseg T ) R <_ ( abs ` ( u - P ) ) )' % A0); run1(w)

# ---- crectdis --------------------------------------------------------------
w = W('crectdis', 'Every point of the boundary frame of a rectangle is at least '
      'R away from a strictly interior point P, when R is below each of the four '
      'coordinate gaps.')
A0 = '( %s /\\ %s /\\ %s )' % (AB, INT, RBD)
PHI = 'R <_ ( abs ` ( u - P ) )'
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
it = w.s([], 'simp2', '( %s -> %s )' % (A0, INT))
rb = w.s([], 'simp3', '( %s -> %s )' % (A0, RBD))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lr = w.s([ineq, w.inst('simpll')], 'syl', '( %s -> %s < %s )' % (A0, RA, RP))
rr_ = w.s([ineq, w.inst('simplr')], 'syl', '( %s -> %s < %s )' % (A0, RP, RB))
li = w.s([ineq, w.inst('simprl')], 'syl', '( %s -> %s < %s )' % (A0, IA, IP))
ri = w.s([ineq, w.inst('simprr')], 'syl', '( %s -> %s < %s )' % (A0, IP, IB))
rr = w.s([rb, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
bds = w.s([rb, w.inst('simpr')], 'syl', '( %s -> ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (A0, RP, RA, RB, RP, IP, IA, IB, IP))
b1 = w.s([bds, w.inst('simpll')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, RP, RA))
b2 = w.s([bds, w.inst('simplr')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, RB, RP))
b3 = w.s([bds, w.inst('simprl')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, IP, IA))
b4 = w.s([bds, w.inst('simprr')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, IB, IP))
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP))
pi = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
re10 = w.s([br, ai, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, P10, RB))
im10 = w.s([br, ai, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, P10, IA))
re01 = w.s([ar, bi, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, P01, RA))
im01 = w.s([ar, bi, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, P01, IB))
leAP = w.s([li], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IP))
lePB = w.s([ri], 'ltled', '( %s -> %s <_ %s )' % (A0, IP, IB))
leAPr = w.s([lr], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RP))
lePBr = w.s([rr_], 'ltled', '( %s -> %s <_ %s )' % (A0, RP, RB))
out = []
# edge 0: bottom, Im, S = A
a0 = w.s([ai, pi, leAP], 'abssuble0d', '( %s -> ( abs ` ( %s - %s ) ) = ( %s - %s ) )' % (A0, IA, IP, IP, IA))
h0a = w.s([ac, cc[P10], w.s([im10], 'eqcomd', '( %s -> %s = ( Im ` %s ) )' % (A0, IA, P10))], '3jca',
          '( %s -> ( A e. CC /\\ %s e. CC /\\ %s = ( Im ` %s ) ) )' % (A0, P10, IA, P10))
h0b = w.s([pc, rr, w.s([b3, a0], 'breqtrrd', '( %s -> R <_ ( abs ` ( %s - %s ) ) )' % (A0, IA, IP))], '3jca',
          '( %s -> ( P e. CC /\\ R e. RR /\\ R <_ ( abs ` ( %s - %s ) ) ) )' % (A0, IA, IP))
out.append(w.s([h0a, h0b, w.inst('csegdisi')], 'syl2anc', '( %s -> A. u e. %s %s )' % (A0, SEGS[0], PHI)))
# edge 1: right, Re, S = P10
a1 = w.s([pr, br, lePBr], 'abssubge0d', '( %s -> ( abs ` ( %s - %s ) ) = ( %s - %s ) )' % (A0, RB, RP, RB, RP))
rw1 = w.s([w.s([re10], 'oveq1d', '( %s -> ( ( Re ` %s ) - %s ) = ( %s - %s ) )' % (A0, P10, RP, RB, RP))], 'fveq2d',
          '( %s -> ( abs ` ( ( Re ` %s ) - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A0, P10, RP, RB, RP))
h1a = w.s([cc[P10], bc, re10], '3jca', '( %s -> ( %s e. CC /\\ B e. CC /\\ ( Re ` %s ) = %s ) )' % (A0, P10, P10, RB))
h1b = w.s([pc, rr, w.s([w.s([b2, a1], 'breqtrrd', '( %s -> R <_ ( abs ` ( %s - %s ) ) )' % (A0, RB, RP)), rw1], 'breqtrrd',
                       '( %s -> R <_ ( abs ` ( ( Re ` %s ) - %s ) ) )' % (A0, P10, RP))], '3jca',
          '( %s -> ( P e. CC /\\ R e. RR /\\ R <_ ( abs ` ( ( Re ` %s ) - %s ) ) ) )' % (A0, P10, RP))
out.append(w.s([h1a, h1b, w.inst('csegdisr')], 'syl2anc', '( %s -> A. u e. %s %s )' % (A0, SEGS[1], PHI)))
# edge 2: top, Im, S = B
a2 = w.s([pi, bi, lePB], 'abssubge0d', '( %s -> ( abs ` ( %s - %s ) ) = ( %s - %s ) )' % (A0, IB, IP, IB, IP))
h2a = w.s([bc, cc[P01], w.s([im01], 'eqcomd', '( %s -> %s = ( Im ` %s ) )' % (A0, IB, P01))], '3jca',
          '( %s -> ( B e. CC /\\ %s e. CC /\\ %s = ( Im ` %s ) ) )' % (A0, P01, IB, P01))
h2b = w.s([pc, rr, w.s([b4, a2], 'breqtrrd', '( %s -> R <_ ( abs ` ( %s - %s ) ) )' % (A0, IB, IP))], '3jca',
          '( %s -> ( P e. CC /\\ R e. RR /\\ R <_ ( abs ` ( %s - %s ) ) ) )' % (A0, IB, IP))
out.append(w.s([h2a, h2b, w.inst('csegdisi')], 'syl2anc', '( %s -> A. u e. %s %s )' % (A0, SEGS[2], PHI)))
# edge 3: left, Re, S = P01
a3 = w.s([ar, pr, leAPr], 'abssuble0d', '( %s -> ( abs ` ( %s - %s ) ) = ( %s - %s ) )' % (A0, RA, RP, RP, RA))
rw3 = w.s([w.s([re01], 'oveq1d', '( %s -> ( ( Re ` %s ) - %s ) = ( %s - %s ) )' % (A0, P01, RP, RA, RP))], 'fveq2d',
          '( %s -> ( abs ` ( ( Re ` %s ) - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A0, P01, RP, RA, RP))
h3a = w.s([cc[P01], ac, re01], '3jca', '( %s -> ( %s e. CC /\\ A e. CC /\\ ( Re ` %s ) = %s ) )' % (A0, P01, P01, RA))
h3b = w.s([pc, rr, w.s([w.s([b1, a3], 'breqtrrd', '( %s -> R <_ ( abs ` ( %s - %s ) ) )' % (A0, RA, RP)), rw3], 'breqtrrd',
                       '( %s -> R <_ ( abs ` ( ( Re ` %s ) - %s ) ) )' % (A0, P01, RP))], '3jca',
          '( %s -> ( P e. CC /\\ R e. RR /\\ R <_ ( abs ` ( ( Re ` %s ) - %s ) ) ) )' % (A0, P01, RP))
out.append(w.s([h3a, h3b, w.inst('csegdisr')], 'syl2anc', '( %s -> A. u e. %s %s )' % (A0, SEGS[3], PHI)))
u1 = w.s([w.s([out[0], out[1]], 'jca', '( %s -> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (A0, SEGS[0], PHI, SEGS[1], PHI)), w.inst('ralunb')],
         'sylibr', '( %s -> A. u e. ( %s u. %s ) %s )' % (A0, SEGS[0], SEGS[1], PHI))
u2 = w.s([w.s([out[2], out[3]], 'jca', '( %s -> ( A. u e. %s %s /\\ A. u e. %s %s ) )' % (A0, SEGS[2], PHI, SEGS[3], PHI)), w.inst('ralunb')],
         'sylibr', '( %s -> A. u e. ( %s u. %s ) %s )' % (A0, SEGS[2], SEGS[3], PHI))
w.qed([w.s([u1, u2], 'jca', '( %s -> ( A. u e. ( %s u. %s ) %s /\\ A. u e. ( %s u. %s ) %s ) )' % (A0, SEGS[0], SEGS[1], PHI, SEGS[2], SEGS[3], PHI)), w.inst('ralunb')],
      'sylibr', '( %s -> A. u e. %s %s )' % (A0, FR, PHI)); run1(w)
