"""Sortie A4c, batch 3d: dpGo nonemptiness and the hit."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

X = ACC('a')
A3 = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (DPO, NONE)

# ================================================================= dpgonn
if not only or 'dpgonn' in only:
    w = W('dpgonn', 'The dpGo loop keeps a nonempty entry nonempty (Lean: dpGo_ne_none).')
    p = w.s([], 'dpgopers', '( %s -> ( ( 1st ` %s ) ` C ) = ( A ` C ) )' % (A3, DG('F', 'A')))
    nn = w.s([w.s([], 'simp3', '( %s -> ( C e. NN0 /\\ ( A ` C ) =/= %s ) )' % (A3, NONE))], 'simprd',
             '( %s -> ( A ` C ) =/= %s )' % (A3, NONE))
    w.qed([p, nn], 'eqnetrd', '( %s -> ( ( 1st ` %s ) ` C ) =/= %s )' % (A3, DG('F', 'A'), NONE))
    run(w)

# ================================================================= dpgohit
QU = [('a', 'Tbl'), ('r', 'NN0')]
RMOD = '( ( r x. P ) mod L )'
BODY = '( ( r < f /\\ ( T ` r ) =/= %s ) -> ( ( 1st ` %s ) ` %s ) =/= %s )' % (NONE, DG('f', 'a'), RMOD, NONE)

def _b(w, ctx, goal):
    A = ctx.A
    n = w.s([ctx.v[1], w.inst('nn0nlt0')], 'syl', '( %s -> -. r < 0 )' % A)
    return w.s([w.s([n], 'intnanrd', '( %s -> -. ( r < 0 /\\ ( T ` r ) =/= %s ) )' % (A, NONE))], 'pm2.21d',
               '( %s -> %s )' % (A, goal))

def _s(w, ctx, goal):
    A = ctx.A
    HY = '( r < ( F + 1 ) /\\ ( T ` r ) =/= %s )' % NONE
    U = '( %s /\\ %s )' % (A, HY)
    lf = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    out = lf(ctx.out, DPO); fst = lf(ctx.fuel, 'F e. NN0'); ast = lf(ctx.v[0], 'a e. Tbl'); rst = lf(ctx.v[1], 'r e. NN0')
    ih = lf(ctx.ih, ctx.ihf)
    hlt = w.s([w.s([], 'simpr', '( %s -> %s )' % (U, HY))], 'simpld', '( %s -> r < ( F + 1 ) )' % U)
    hnn = w.s([w.s([], 'simpr', '( %s -> %s )' % (U, HY))], 'simprd', '( %s -> ( T ` r ) =/= %s )' % (U, NONE))
    xcl = w.s([w.s([out, w.s([fst, ast], 'jca', '( %s -> ( F e. NN0 /\\ a e. Tbl ) )' % U)], 'jca',
                   '( %s -> ( %s /\\ ( F e. NN0 /\\ a e. Tbl ) ) )' % (U, DPO)), w.inst('dpgoacl')], 'syl',
              '( %s -> %s e. Tbl )' % (U, X))
    val = dp_p1(w, ctx)
    p1 = prj(w, A, DG('( F + 1 )', 'a'), val, '( 1st ` %s )' % DG('F', X), '( ( 2nd ` %s ) + 1 )' % DG('F', X), 1)
    p1U = w.s([p1], 'adantr', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (U, DG('( F + 1 )', 'a'), DG('F', X)))
    tgt = '( ( 1st ` %s ) ` %s ) =/= %s' % (DG('F', X), RMOD, NONE)
    # ---- r = F
    C1 = '( %s /\\ r = F )' % U
    lfc = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C1, f))
    req = w.s([], 'simpr', '( %s -> r = F )' % C1)
    tfnn = w.s([w.s([req], 'fveq2d', '( %s -> ( T ` r ) = ( T ` F ) )' % C1), lfc(hnn, '( T ` r ) =/= %s' % NONE)],
               'eqnetrrd', '( %s -> ( T ` F ) =/= %s )' % (C1, NONE))
    slf = dp_lem(w, C1, 'dpgoacself', lfc(out, DPO), lfc(fst, 'F e. NN0'), lfc(ast, 'a e. Tbl'), 'a', tfnn,
                 '( T ` F ) =/= %s' % NONE, '( %s ` %s ) =/= %s' % (X, MOD, NONE))
    mcl = w.s([w.s([w.s([w.s([lfc(out, DPO)], 'simpld', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % C1),
                         lfc(fst, 'F e. NN0')], 'jca', '( %s -> ( ( L e. NN /\\ P e. NN0 ) /\\ F e. NN0 ) )' % C1),
                    ], 'syl', None)], 'id', None)
    w.lines.pop(); w.lines.pop()
    mcl = w.s([w.s([w.s([lfc(out, DPO)], 'simpld', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % C1),
                    lfc(fst, 'F e. NN0')], 'jca', '( %s -> ( ( L e. NN /\\ P e. NN0 ) /\\ F e. NN0 ) )' % C1),
               w.inst('dpgomcl')], 'syl', '( %s -> %s e. NN0 )' % (C1, MOD))
    nnst = w.s([w.s([lfc(out, DPO),
                     w.s([lfc(fst, 'F e. NN0'), lfc(xcl, '%s e. Tbl' % X)], 'jca',
                         '( %s -> ( F e. NN0 /\\ %s e. Tbl ) )' % (C1, X)),
                     w.s([mcl, slf], 'jca', '( %s -> ( %s e. NN0 /\\ ( %s ` %s ) =/= %s ) )' % (C1, MOD, X, MOD, NONE))],
                    '3jca', '( %s -> ( %s /\\ ( F e. NN0 /\\ %s e. Tbl ) /\\ ( %s e. NN0 /\\ ( %s ` %s ) =/= %s ) ) )'
                    % (C1, DPO, X, MOD, X, MOD, NONE)), w.inst('dpgonn')], 'syl',
               '( %s -> ( ( 1st ` %s ) ` %s ) =/= %s )' % (C1, DG('F', X), MOD, NONE))
    rw = w.s([req], 'oveq1d', '( %s -> ( r x. P ) = ( F x. P ) )' % C1)
    rw2 = w.s([rw], 'oveq1d', '( %s -> %s = %s )' % (C1, RMOD, MOD))
    g1 = w.s([w.s([rw2], 'fveq2d', '( %s -> ( ( 1st ` %s ) ` %s ) = ( ( 1st ` %s ) ` %s ) )' % (C1, DG('F', X), RMOD, DG('F', X), MOD)),
              nnst], 'eqnetrd', '( %s -> %s )' % (C1, tgt))
    # ---- r =/= F
    C2 = '( %s /\\ -. r = F )' % U
    lfd = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C2, f))
    rne = w.s([w.s([], 'simpr', '( %s -> -. r = F )' % C2), w.inst('neqned')], 'syl', '( %s -> r =/= F )' % C2)
    rz = w.s([lfd(rst, 'r e. NN0')], 'nn0zd', '( %s -> r e. ZZ )' % C2)
    fz = w.s([lfd(fst, 'F e. NN0')], 'nn0zd', '( %s -> F e. ZZ )' % C2)
    rle = w.s([lfd(hlt, 'r < ( F + 1 )'),
               w.s([rz, fz, w.inst('zleltp1')], 'syl2anc', '( %s -> ( r <_ F <-> r < ( F + 1 ) ) )' % C2)],
              'mpbird', '( %s -> r <_ F )' % C2)
    rlt = w.s([w.s([w.s([lfd(rst, 'r e. NN0')], 'nn0red', '( %s -> r e. RR )' % C2),
                    w.s([lfd(fst, 'F e. NN0')], 'nn0red', '( %s -> F e. RR )' % C2)], 'ltlend',
                   '( %s -> ( r < F <-> ( r <_ F /\\ F =/= r ) ) )' % C2),
               w.s([rle, w.s([rne], 'necomd', '( %s -> F =/= r )' % C2)], 'jca',
                   '( %s -> ( r <_ F /\\ F =/= r ) )' % C2)], 'mpbird', '( %s -> r < F )' % C2)
    rn = ctx.rn
    ihb = subst(subst(subst(BODY, 'f', 'F'), 'a', rn[0]), 'r', rn[1])
    ihx, bd = instn(w, C2, lfd(ih, ctx.ihf), [(rn[0], 'Tbl'), (rn[1], 'NN0')], ihb, [X, 'r'],
                    [lfd(xcl, '%s e. Tbl' % X), lfd(rst, 'r e. NN0')])
    g2 = w.s([ihx, w.s([rlt, lfd(hnn, '( T ` r ) =/= %s' % NONE)], 'jca',
                       '( %s -> ( r < F /\\ ( T ` r ) =/= %s ) )' % (C2, NONE))], 'mpd', '( %s -> %s )' % (C2, tgt))
    both = w.s([g1, g2], 'pm2.61dan', '( %s -> %s )' % (U, tgt))
    fin = w.s([w.s([p1U], 'fveq1d', '( %s -> ( ( 1st ` %s ) ` %s ) = ( ( 1st ` %s ) ` %s ) )' % (U, DG('( F + 1 )', 'a'), RMOD, DG('F', X), RMOD)),
               both], 'eqnetrd', '( %s -> ( ( 1st ` %s ) ` %s ) =/= %s )' % (U, DG('( F + 1 )', 'a'), RMOD, NONE))
    return w.s([fin], 'ex', '( %s -> %s )' % (A, goal))

def _i(w):
    A = '( %s /\\ ( F e. NN0 /\\ A e. Tbl ) /\\ ( R e. NN0 /\\ R < F /\\ ( T ` R ) =/= %s ) )' % (DPO, NONE)
    dpo = w.s([], 'simp1', '( %s -> %s )' % (A, DPO))
    ff = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)], 'simpld', '( %s -> F e. NN0 )' % A)
    aa = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ A e. Tbl ) )' % A)], 'simprd', '( %s -> A e. Tbl )' % A)
    rr = w.s([w.s([], 'simp3', '( %s -> ( R e. NN0 /\\ R < F /\\ ( T ` R ) =/= %s ) )' % (A, NONE))], 'simp1d',
             '( %s -> R e. NN0 )' % A)
    rlt = w.s([w.s([], 'simp3', '( %s -> ( R e. NN0 /\\ R < F /\\ ( T ` R ) =/= %s ) )' % (A, NONE))], 'simp2d',
              '( %s -> R < F )' % A)
    rnn = w.s([w.s([], 'simp3', '( %s -> ( R e. NN0 /\\ R < F /\\ ( T ` R ) =/= %s ) )' % (A, NONE))], 'simp3d',
              '( %s -> ( T ` R ) =/= %s )' % (A, NONE))
    PH = qphi(DPO, QU, subst(BODY, 'f', 'F'))
    ral = w.s([w.s([ff, w.inst('dpgohitl')], 'syl', '( %s -> %s )' % (A, PH)), dpo], 'mpd',
              '( %s -> %s )' % (A, quantify(QU, ['a', 'r'], subst(BODY, 'f', 'F'))))
    st, bd = instn(w, A, ral, QU, subst(BODY, 'f', 'F'), ['A', 'R'], [aa, rr])
    fin = w.s([st, w.s([rlt, rnn], 'jca', '( %s -> ( R < F /\\ ( T ` R ) =/= %s ) )' % (A, NONE))], 'mpd',
              '( %s -> ( ( 1st ` %s ) ` ( ( R x. P ) mod L ) ) =/= %s )' % (A, DG('F', 'A'), NONE))
    w.lines[-1] = w.lines[-1].replace('%s:' % fin, 'qed:', 1)

qfuel(run, 'dpgohit', DPO, QU, BODY, _b, _s, instfn=_i, only=only,
      desc='The dpGo loop propagates every snapshot entry below the fuel (Lean: dpGo_hit).')
