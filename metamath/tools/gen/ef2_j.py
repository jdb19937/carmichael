"""Sortie EF2: the boundary integral of a finite sum of functions continuous on a carrier of the frame (ef2rsum)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import lin
lin.FASTPATH = True

A_, B_ = '( P + ( _i x. S ) )', '( Q + ( _i x. R ) )'
C10, C01 = '( Q + ( _i x. S ) )', '( P + ( _i x. R ) )'
SEG = [(A_, C10), (C10, B_), (B_, C01), (C01, A_)]
SG = ['( %s cseg %s )' % e for e in SEG]
FRX = '( ( %s u. %s ) u. ( %s u. %s ) )' % tuple(SG)
SUMF = '( b e. D |-> sum_ k e. K ( ( G ` k ) ` b ) )'
RI = lambda F: '( %s rectint <. %s , %s >. )' % (F, A_, B_)
LI = lambda F, i: '( %s lint <. %s , %s >. )' % (F, SEG[i][0], SEG[i][1])
S['ef2rsum'] = ('( ( ( ( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ R e. RR ) ) /\\ ( K e. Fin /\\ D C_ CC ) ) /\\ ( A. j e. K ( G ` j ) e. ( D -cn-> CC ) /\\ %s C_ D ) ) -> '
                '%s = sum_ k e. K %s )') % (FRX, RI(SUMF), RI('( G ` k )'))


def gen_rsum():
    w = W('ef2rsum', 'The boundary integral of a finite sum of functions continuous on a set containing the four edges of a rectangle is the sum of their boundary integrals (C0c ~ lintfsum on each edge, ~ rectintco ; the solid rectangle need not lie in the domain, unlike ~ rectintsum ).')
    A0, GC = ante_of(S['ef2rsum'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2 = top_and(A0)
    x1 = s([], 'simpl', X1); x2 = s([], 'simpr', X2)
    Y1, Y2 = top_and(X1)
    y1 = s([x1, w.inst('simpl')], 'syl', Y1); y2 = s([x1, w.inst('simpr')], 'syl', Y2)
    pq = s([y1, w.inst('simpl')], 'syl', '( P e. RR /\\ Q e. RR )'); sr = s([y1, w.inst('simpr')], 'syl', '( S e. RR /\\ R e. RR )')
    pr = s([pq, w.inst('simpl')], 'syl', 'P e. RR'); qr = s([pq, w.inst('simpr')], 'syl', 'Q e. RR')
    sr_ = s([sr, w.inst('simpl')], 'syl', 'S e. RR'); rr = s([sr, w.inst('simpr')], 'syl', 'R e. RR')
    kf = s([y2, w.inst('simpl')], 'syl', 'K e. Fin'); dcc = s([y2, w.inst('simpr')], 'syl', 'D C_ CC')
    gall = s([x2, w.inst('simpl')], 'syl', 'A. j e. K ( G ` j ) e. ( D -cn-> CC )')
    frd = s([x2, w.inst('simpr')], 'syl', '%s C_ D' % FRX)
    # corners and edges
    def cc(re, im, rst, ist):
        ic = s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([ist], 'recnd', '%s e. CC' % im)], 'mulcld', '( _i x. %s ) e. CC' % im)
        return s([s([rst], 'recnd', '%s e. CC' % re), ic], 'addcld', '( %s + ( _i x. %s ) ) e. CC' % (re, im))
    cst = {A_: cc('P', 'S', pr, sr_), B_: cc('Q', 'R', qr, rr), C10: cc('Q', 'S', qr, sr_), C01: cc('P', 'R', pr, rr)}
    H12 = '( %s u. %s )' % (SG[0], SG[1]); H34 = '( %s u. %s )' % (SG[2], SG[3])
    h12 = s([s([w.s([], 'ssun1', '%s C_ %s' % (H12, FRX))], 'a1i', '%s C_ %s' % (H12, FRX)), frd], 'sstrd', '%s C_ D' % H12)
    h34 = s([s([w.s([], 'ssun2', '%s C_ %s' % (H34, FRX))], 'a1i', '%s C_ %s' % (H34, FRX)), frd], 'sstrd', '%s C_ D' % H34)
    segd = [s([s([w.s([], 'ssun1', '%s C_ %s' % (SG[0], H12))], 'a1i', '%s C_ %s' % (SG[0], H12)), h12], 'sstrd', '%s C_ D' % SG[0]),
            s([s([w.s([], 'ssun2', '%s C_ %s' % (SG[1], H12))], 'a1i', '%s C_ %s' % (SG[1], H12)), h12], 'sstrd', '%s C_ D' % SG[1]),
            s([s([w.s([], 'ssun1', '%s C_ %s' % (SG[2], H34))], 'a1i', '%s C_ %s' % (SG[2], H34)), h34], 'sstrd', '%s C_ D' % SG[2]),
            s([s([w.s([], 'ssun2', '%s C_ %s' % (SG[3], H34))], 'a1i', '%s C_ %s' % (SG[3], H34)), h34], 'sstrd', '%s C_ D' % SG[3])]
    # the sum mapping, edge by edge
    co = lambda F, fex: s([fex, s([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )'), s([sr_, rr], 'jca', '( S e. RR /\\ R e. RR )'), w.inst('rectintco')], 'syl3anc',
                          '%s = ( ( %s + %s ) + ( %s + %s ) )' % (RI(F), LI(F, 0), LI(F, 1), LI(F, 2), LI(F, 3)))
    dex = s([s([w.s([], 'cnex', 'CC e. _V')], 'a1i', 'CC e. _V'), dcc], 'ssexd', 'D e. _V')
    sex = s([dex, w.inst('mptexg')], 'syl', '%s e. _V' % SUMF)
    c0 = co(SUMF, sex)
    lf = []
    for i in range(4):
        LF = tsub(stmt('lintfsum'), {'A': SEG[i][0], 'B': SEG[i][1], 'u': 'b'})
        la, lc = ante_of(LF)
        have = {'( %s e. CC /\\ %s e. CC )' % SEG[i]: s([cst[SEG[i][0]], cst[SEG[i][1]]], 'jca', '( %s e. CC /\\ %s e. CC )' % SEG[i]), 'K e. Fin': kf, 'D C_ CC': dcc,
                'A. j e. K ( G ` j ) e. ( D -cn-> CC )': gall, '%s C_ D' % SG[i]: segd[i]}
        lf.append(s([conj(w, A0, la, have), w.inst('lintfsum')], 'syl', lc))
    SK = lambda i: 'sum_ k e. K %s' % LI('( G ` k )', i)
    lhs = s([c0, s([s([lf[0], lf[1]], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (LI(SUMF, 0), LI(SUMF, 1), SK(0), SK(1))),
                    s([lf[2], lf[3]], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (LI(SUMF, 2), LI(SUMF, 3), SK(2), SK(3)))], 'oveq12d',
                   '( ( %s + %s ) + ( %s + %s ) ) = ( ( %s + %s ) + ( %s + %s ) )' % (LI(SUMF, 0), LI(SUMF, 1), LI(SUMF, 2), LI(SUMF, 3), SK(0), SK(1), SK(2), SK(3)))],
            'eqtrd', '%s = ( ( %s + %s ) + ( %s + %s ) )' % (RI(SUMF), SK(0), SK(1), SK(2), SK(3)))
    # each term, edge by edge
    Ak = '( %s /\\ k e. K )' % A0
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    sub = w.s([w.s([], 'fveq2', '( j = k -> ( G ` j ) = ( G ` k ) )')], 'eleq1d', '( j = k -> ( ( G ` j ) e. ( D -cn-> CC ) <-> ( G ` k ) e. ( D -cn-> CC ) ) )')
    gk = sk([sub, up(w, gall, Ak), sk([], 'simpr', 'k e. K')], 'rspcdva', '( G ` k ) e. ( D -cn-> CC )')
    lcl = []
    for i in range(4):
        lcl.append(sk([sk([up(w, cst[SEG[i][0]], Ak), up(w, cst[SEG[i][1]], Ak)], 'jca', '( %s e. CC /\\ %s e. CC )' % SEG[i]), sk([gk, up(w, segd[i], Ak)], 'jca',
                      '( ( G ` k ) e. ( D -cn-> CC ) /\\ %s C_ D )' % SG[i]), w.inst('lintcl')], 'syl2anc', '%s e. CC' % LI('( G ` k )', i)))
    s12 = sk([lcl[0], lcl[1]], 'addcld', '( %s + %s ) e. CC' % (LI('( G ` k )', 0), LI('( G ` k )', 1)))
    s34 = sk([lcl[2], lcl[3]], 'addcld', '( %s + %s ) e. CC' % (LI('( G ` k )', 2), LI('( G ` k )', 3)))
    Ck = w.s([], 'fvex', '( G ` k ) e. _V')
    ck = sk([sk([Ck], 'a1i', '( G ` k ) e. _V'), sk([up(w, pr, Ak), up(w, qr, Ak)], 'jca', '( P e. RR /\\ Q e. RR )'), sk([up(w, sr_, Ak), up(w, rr, Ak)], 'jca', '( S e. RR /\\ R e. RR )'),
              w.inst('rectintco')], 'syl3anc', '%s = ( ( %s + %s ) + ( %s + %s ) )' % (RI('( G ` k )'), LI('( G ` k )', 0), LI('( G ` k )', 1), LI('( G ` k )', 2), LI('( G ` k )', 3)))
    T12 = '( %s + %s )' % (LI('( G ` k )', 0), LI('( G ` k )', 1)); T34 = '( %s + %s )' % (LI('( G ` k )', 2), LI('( G ` k )', 3))
    se = s([ck], 'sumeq2dv', 'sum_ k e. K %s = sum_ k e. K ( %s + %s )' % (RI('( G ` k )'), T12, T34))
    fa = s([kf, s12, s34], 'fsumadd', 'sum_ k e. K ( %s + %s ) = ( sum_ k e. K %s + sum_ k e. K %s )' % (T12, T34, T12, T34))
    fb = s([kf, lcl[0], lcl[1]], 'fsumadd', 'sum_ k e. K %s = ( %s + %s )' % (T12, SK(0), SK(1)))
    fc = s([kf, lcl[2], lcl[3]], 'fsumadd', 'sum_ k e. K %s = ( %s + %s )' % (T34, SK(2), SK(3)))
    rhs = s([s([se, fa], 'eqtrd', 'sum_ k e. K %s = ( sum_ k e. K %s + sum_ k e. K %s )' % (RI('( G ` k )'), T12, T34)),
             s([fb, fc], 'oveq12d', '( sum_ k e. K %s + sum_ k e. K %s ) = ( ( %s + %s ) + ( %s + %s ) )' % (T12, T34, SK(0), SK(1), SK(2), SK(3)))], 'eqtrd',
            'sum_ k e. K %s = ( ( %s + %s ) + ( %s + %s ) )' % (RI('( G ` k )'), SK(0), SK(1), SK(2), SK(3)))
    w.qed([lhs, rhs], 'eqtr4d', S['ef2rsum'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2rsum']:
        {'ef2rsum': gen_rsum}[g]()
