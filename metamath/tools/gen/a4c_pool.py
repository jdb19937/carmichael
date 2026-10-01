"""Sortie A4c, batch 13: membership and duplicate-freeness of the pool loop
(Lean: AlgScan.poolGo_mem, poolGo_nodup, poolAlg_spec)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

PGO = lambda s: '( ( ( X PoolGo Z ) ` K ) ` %s )' % s
PG = lambda s: '( 1st ` %s )' % PGO(s)
CSV = '( <" P "> ++ V )'
PP = '( ( P x. K ) + 1 )'
OUT = '( X e. NN0 /\\ Z e. NN0 /\\ K e. NN0 )'
BD = lambda dd: '( ( ( ( %s x. K ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) )' % dd
BDP = '( ( %s = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) )' % PP
BODY = '( p e. ran %s <-> E. d e. ran s %s )' % (PG('s'), BD('d'))

def outs(w, A, st):
    xx = w.s([st], 'simp1d', '( %s -> X e. NN0 )' % A)
    zz = w.s([st], 'simp2d', '( %s -> Z e. NN0 )' % A)
    kk = w.s([st], 'simp3d', '( %s -> K e. NN0 )' % A)
    xz = w.s([w.s([xx, zz], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % A), kk], 'jca',
             '( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % A)
    return xx, zz, kk, xz

def _b(w, ctx, goal):
    A = ctx.A
    xx, zz, kk, xz = outs(w, A, ctx.out)
    v = w.s([xz, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (A, PGO('(/)')))
    p1 = prj(w, A, PGO('(/)'), v, '(/)', '0', 1,
             aex=w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A),
             bex=w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A))
    rn0s = w.s([w.s([p1], 'rneqd', '( %s -> ran %s = ran (/) )' % (A, PG('(/)'))),
                w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % A)], 'eqtrd',
               '( %s -> ran %s = (/) )' % (A, PG('(/)')))
    nel = w.s([w.s([rn0s], 'eleq2d', '( %s -> ( p e. ran %s <-> p e. (/) ) )' % (A, PG('(/)'))),
               w.s([w.s([], 'noel', '-. p e. (/)')], 'a1i', '( %s -> -. p e. (/) )' % A)], 'mtbird',
              '( %s -> -. p e. ran %s )' % (A, PG('(/)')))
    idq = w.s([], 'id', '( ran (/) = (/) -> ran (/) = (/) )')
    rxe0 = w.s([idq], 'rexeqdv', '( ran (/) = (/) -> ( E. d e. ran (/) %s <-> E. d e. (/) %s ) )' % (BD('d'), BD('d')))
    rxe1 = w.s([w.s([], 'rn0', 'ran (/) = (/)'), rxe0], 'ax-mp',
               '( E. d e. ran (/) %s <-> E. d e. (/) %s )' % (BD('d'), BD('d')))
    nrx0 = w.s([w.s([], 'rex0', '-. E. d e. (/) %s' % BD('d')), rxe1], 'mtbir', '-. E. d e. ran (/) %s' % BD('d'))
    nrx = w.s([nrx0], 'a1i', '( %s -> -. E. d e. ran (/) %s )' % (A, BD('d')))
    return w.s([nel, nrx], '2falsed', '( %s -> %s )' % (A, goal))

def rexcons(w, ante, rcstep, pexstep):
    """( ante -> ( E. d e. ran CSV BD( d ) <-> ( BDP \\/ E. d e. ran V BD( d ) ) ) )"""
    EQ = 'ran %s = ( { P } u. ran V )' % CSV
    idq = w.s([], 'id', '( %s -> %s )' % (EQ, EQ))
    st = w.s([idq], 'rexeqdv',
             '( %s -> ( E. d e. ran %s %s <-> E. d e. ( { P } u. ran V ) %s ) )' % (EQ, CSV, BD('d'), BD('d')))
    s1 = w.s([rcstep, st], 'syl',
             '( %s -> ( E. d e. ran %s %s <-> E. d e. ( { P } u. ran V ) %s ) )' % (ante, CSV, BD('d'), BD('d')))
    un = w.s([w.s([], 'rexun', '( E. d e. ( { P } u. ran V ) %s <-> ( E. d e. { P } %s \\/ E. d e. ran V %s ) )'
                   % (BD('d'), BD('d'), BD('d')))], 'a1i',
             '( %s -> ( E. d e. ( { P } u. ran V ) %s <-> ( E. d e. { P } %s \\/ E. d e. ran V %s ) ) )'
             % (ante, BD('d'), BD('d'), BD('d')))
    sbd = w.s([], 'oveq1', '( d = P -> ( d x. K ) = ( P x. K ) )')
    sbd2 = w.s([sbd], 'oveq1d', '( d = P -> ( ( d x. K ) + 1 ) = %s )' % PP)
    sbd3 = w.s([sbd2], 'eqeq1d', '( d = P -> ( ( ( d x. K ) + 1 ) = p <-> %s = p ) )' % PP)
    sbd4 = w.s([sbd3], 'anbi1d', '( d = P -> ( ( ( ( d x. K ) + 1 ) = p /\\ p <_ X ) <-> ( %s = p /\\ p <_ X ) ) )' % PP)
    sbd5 = w.s([sbd4], 'anbi1d', '( d = P -> ( %s <-> %s ) )' % (BD('d'), BDP))
    sn = w.s([pexstep, w.s([sbd5], 'rexsng', '( P e. _V -> ( E. d e. { P } %s <-> %s ) )' % (BD('d'), BDP))], 'syl',
             '( %s -> ( E. d e. { P } %s <-> %s ) )' % (ante, BD('d'), BDP))
    fin = w.s([w.s([s1, un], 'bitrd',
                   '( %s -> ( E. d e. ran %s %s <-> ( E. d e. { P } %s \\/ E. d e. ran V %s ) ) )' % (ante, CSV, BD('d'), BD('d'), BD('d'))),
               w.s([sn], 'orbi1d',
                   '( %s -> ( ( E. d e. { P } %s \\/ E. d e. ran V %s ) <-> ( %s \\/ E. d e. ran V %s ) ) )' % (ante, BD('d'), BD('d'), BDP, BD('d')))],
              'bitrd', '( %s -> ( E. d e. ran %s %s <-> ( %s \\/ E. d e. ran V %s ) ) )' % (ante, CSV, BD('d'), BDP, BD('d')))
    return fin

def _s(w, ctx, goal):
    A = ctx.A
    xx, zz, kk, xz = outs(w, A, ctx.out)
    vv = ctx.wrd; pp = ctx.let; pn = ctx.v[0]
    r = ctx.rn
    ppn = w.s([w.s([pp, kk], 'nn0mulcld', '( %s -> ( P x. K ) e. NN0 )' % A), w.inst('peano2nn0')], 'syl',
              '( %s -> %s e. NN0 )' % (A, PP))
    pgcl = w.s([w.s([xz, vv, w.inst('poolgocl')], 'syl2anc', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (A, PGO('V'))),
                w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (A, PG('V')))
    rcs = w.s([pp, vv, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A, CSV))
    pex = w.s([pp], 'elexd', '( %s -> P e. _V )' % A)
    rx = rexcons(w, A, rcs, pex)
    ihb = subst(subst(BODY, 's', 'V'), 'p', r[0])
    ihp, _ = instn(w, A, ctx.ih, [(r[0], 'NN0')], ihb, ['p'], [pn])
    COND = '( %s <_ X /\\ Z < %s )' % (PP, PP)
    PRM = '( 1st ` ( IsPrimeTD ` %s ) ) = 1o' % PP
    TH = 'if ( %s , ( <" %s "> ++ %s ) , %s )' % (PRM, PP, PG('V'), PG('V'))
    C1 = '( ( %s + ( 2nd ` ( IsPrimeTD ` %s ) ) ) + 1 )' % ('( 2nd ` %s )' % PGO('V'), PP)
    C2 = '( %s + 1 )' % ('( 2nd ` %s )' % PGO('V'))
    IFE = 'if ( %s , <. %s , %s >. , <. %s , %s >. )' % (COND, TH, C1, PG('V'), C2)
    val = w.s([w.s([xz, pp], 'jca', '( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ P e. NN0 ) )' % A), vv,
               w.inst('poolgocs')], 'syl2anc', '( %s -> %s = %s )' % (A, PGO(CSV), IFE))
    ift, iff = ifproj(w, A, PGO(CSV), val, COND, '<. %s , %s >.' % (TH, C1), '<. %s , %s >.' % (PG('V'), C2))
    RHS = '( %s \\/ E. d e. ran V %s )' % (BDP, BD('d'))
    GOAL = '( p e. ran %s <-> E. d e. ran %s %s )' % (PG(CSV), CSV, BD('d'))
    # ------------------------------------------------- the candidate is in range
    T1 = '( %s /\\ %s )' % (A, COND)
    t1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (T1, f))
    s1c = w.s([t1(ppn, '%s e. NN0' % PP), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (T1, PP))
    catw = w.s([s1c, t1(pgcl, '%s e. Word NN0' % PG('V')), w.inst('ccatcl')], 'syl2anc',
               '( %s -> ( <" %s "> ++ %s ) e. Word NN0 )' % (T1, PP, PG('V')))
    thw = w.s([catw, t1(pgcl, '%s e. Word NN0' % PG('V'))], 'ifcld', '( %s -> %s e. Word NN0 )' % (T1, TH))
    pt = prj(w, T1, PGO(CSV), ift, TH, C1, 1,
             aex=w.s([thw], 'elexd', '( %s -> %s e. _V )' % (T1, TH)),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % C1)], 'a1i', '( %s -> %s e. _V )' % (T1, C1)))
    prmbi = w.s([t1(ppn, '%s e. NN0' % PP), w.inst('isprimetdspec')], 'syl',
                '( %s -> ( %s <-> %s e. Prime ) )' % (T1, PRM, PP))
    #   prime
    U1 = '( %s /\\ %s )' % (T1, PRM)
    u1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U1, f))
    ke = w.s([w.s([], 'simpr', '( %s -> %s )' % (U1, PRM))], 'iftrued',
             '( %s -> %s = ( <" %s "> ++ %s ) )' % (U1, TH, PP, PG('V')))
    rk = w.s([u1(pt, '%s = %s' % (PG(CSV), TH)), ke], 'eqtrd',
             '( %s -> %s = ( <" %s "> ++ %s ) )' % (U1, PG(CSV), PP, PG('V')))
    elj = w.s([w.s([u1(t1(ppn, '%s e. NN0' % PP), '%s e. NN0' % PP),
                    u1(t1(pgcl, '%s e. Word NN0' % PG('V')), '%s e. Word NN0' % PG('V'))], 'jca',
                   '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (U1, PP, PG('V'))),
               u1(t1(pn, 'p e. NN0'), 'p e. NN0')], 'jca',
              '( %s -> ( ( %s e. NN0 /\\ %s e. Word NN0 ) /\\ p e. NN0 ) )' % (U1, PP, PG('V')))
    elk = w.s([elj, w.inst('algelcs')], 'syl',
              '( %s -> ( p e. ran ( <" %s "> ++ %s ) <-> ( p = %s \\/ p e. ran %s ) ) )' % (U1, PP, PG('V'), PP, PG('V')))
    lhs1 = w.s([w.s([w.s([rk], 'rneqd', '( %s -> ran %s = ran ( <" %s "> ++ %s ) )' % (U1, PG(CSV), PP, PG('V')))], 'eleq2d',
                    '( %s -> ( p e. ran %s <-> p e. ran ( <" %s "> ++ %s ) ) )' % (U1, PG(CSV), PP, PG('V'))), elk], 'bitrd',
               '( %s -> ( p e. ran %s <-> ( p = %s \\/ p e. ran %s ) ) )' % (U1, PG(CSV), PP, PG('V')))
    #   p = PP <-> BDP
    E1 = '( %s /\\ p = %s )' % (U1, PP)
    e1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E1, f))
    pe = w.s([], 'simpr', '( %s -> p = %s )' % (E1, PP))
    ple = w.s([w.s([pe], 'breq1d', '( %s -> ( p <_ X <-> %s <_ X ) )' % (E1, PP)),
               e1(u1(w.s([w.s([], 'simpr', '( %s -> %s )' % (T1, COND))], 'simpld', '( %s -> %s <_ X )' % (T1, PP)), '%s <_ X' % PP),
                  '%s <_ X' % PP)], 'mpbird', '( %s -> p <_ X )' % E1)
    pzl = w.s([w.s([pe], 'breq2d', '( %s -> ( Z < p <-> Z < %s ) )' % (E1, PP)),
               e1(u1(w.s([w.s([], 'simpr', '( %s -> %s )' % (T1, COND))], 'simprd', '( %s -> Z < %s )' % (T1, PP)), 'Z < %s' % PP),
                  'Z < %s' % PP)], 'mpbird', '( %s -> Z < p )' % E1)
    ppr = w.s([e1(u1(prmbi, '( %s <-> %s e. Prime )' % (PRM, PP)), '( %s <-> %s e. Prime )' % (PRM, PP)),
               e1(w.s([], 'simpr', '( %s -> %s )' % (U1, PRM)), PRM)], 'mpbid', '( %s -> %s e. Prime )' % (E1, PP))
    pprm = w.s([w.s([pe], 'eleq1d', '( %s -> ( p e. Prime <-> %s e. Prime ) )' % (E1, PP)), ppr], 'mpbird',
               '( %s -> p e. Prime )' % E1)
    bdpf = w.s([w.s([w.s([pe], 'eqcomd', '( %s -> %s = p )' % (E1, PP)), ple], 'jca',
                    '( %s -> ( %s = p /\\ p <_ X ) )' % (E1, PP)),
                w.s([pzl, pprm], 'jca', '( %s -> ( Z < p /\\ p e. Prime ) )' % E1)], 'jca', '( %s -> %s )' % (E1, BDP))
    E2 = '( %s /\\ %s )' % (U1, BDP)
    bdpb = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (E2, BDP))], 'simpld', '( %s -> ( %s = p /\\ p <_ X ) )' % (E2, PP))], 'simpld',
               '( %s -> %s = p )' % (E2, PP))
    peqb = w.s([bdpb], 'eqcomd', '( %s -> p = %s )' % (E2, PP))
    eqbi = w.s([w.s([bdpf], 'ex', '( %s -> ( p = %s -> %s ) )' % (U1, PP, BDP)),
                w.s([peqb], 'ex', '( %s -> ( %s -> p = %s ) )' % (U1, BDP, PP))], 'impbid',
               '( %s -> ( p = %s <-> %s ) )' % (U1, PP, BDP))
    g1 = w.s([lhs1, w.s([eqbi, u1(t1(ihp, '( p e. ran %s <-> E. d e. ran V %s )' % (PG('V'), BD('d'))),
                                  '( p e. ran %s <-> E. d e. ran V %s )' % (PG('V'), BD('d')))], 'orbi12d',
                        '( %s -> ( ( p = %s \\/ p e. ran %s ) <-> %s ) )' % (U1, PP, PG('V'), RHS))], 'bitrd',
             '( %s -> ( p e. ran %s <-> %s ) )' % (U1, PG(CSV), RHS))
    gg1 = w.s([g1, u1(t1(rx, '( E. d e. ran %s %s <-> %s )' % (CSV, BD('d'), RHS)),
                      '( E. d e. ran %s %s <-> %s )' % (CSV, BD('d'), RHS))], 'bitr4d', '( %s -> %s )' % (U1, GOAL))
    #   not prime
    N1 = '( %s /\\ -. %s )' % (T1, PRM)
    n1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (N1, f))
    kf = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (N1, PRM))], 'iffalsed', '( %s -> %s = %s )' % (N1, TH, PG('V')))
    rnn = w.s([n1(pt, '%s = %s' % (PG(CSV), TH)), kf], 'eqtrd', '( %s -> %s = %s )' % (N1, PG(CSV), PG('V')))
    nprm = w.s([n1(prmbi, '( %s <-> %s e. Prime )' % (PRM, PP)), w.s([], 'simpr', '( %s -> -. %s )' % (N1, PRM))], 'mtbid',
               '( %s -> -. %s e. Prime )' % (N1, PP))
    N1B = '( %s /\\ %s )' % (N1, BDP)
    bq = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (N1B, BDP))], 'simpld',
                  '( %s -> ( %s = p /\\ p <_ X ) )' % (N1B, PP))], 'simpld', '( %s -> %s = p )' % (N1B, PP))
    bpr = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (N1B, BDP))], 'simprd',
                   '( %s -> ( Z < p /\\ p e. Prime ) )' % N1B)], 'simprd', '( %s -> p e. Prime )' % N1B)
    ppr2 = w.s([bq, bpr], 'eqeltrd', '( %s -> %s e. Prime )' % (N1B, PP))
    nbdp = w.s([ppr2, w.s([nprm], 'adantr', '( %s -> -. %s e. Prime )' % (N1B, PP))], 'pm2.65da',
               '( %s -> -. %s )' % (N1, BDP))
    g2 = w.s([w.s([w.s([rnn], 'rneqd', '( %s -> ran %s = ran %s )' % (N1, PG(CSV), PG('V')))], 'eleq2d',
                  '( %s -> ( p e. ran %s <-> p e. ran %s ) )' % (N1, PG(CSV), PG('V'))),
              w.s([n1(t1(ihp, '( p e. ran %s <-> E. d e. ran V %s )' % (PG('V'), BD('d'))),
                      '( p e. ran %s <-> E. d e. ran V %s )' % (PG('V'), BD('d'))),
                   w.s([nbdp, w.s([w.s([], 'biorf', '( -. %s -> ( E. d e. ran V %s <-> %s ) )' % (BDP, BD('d'), RHS))], 'a1i',
                                  '( %s -> ( -. %s -> ( E. d e. ran V %s <-> %s ) ) )' % (N1, BDP, BD('d'), RHS))], 'mpd',
                       '( %s -> ( E. d e. ran V %s <-> %s ) )' % (N1, BD('d'), RHS))], 'bitrd',
                  '( %s -> ( p e. ran %s <-> %s ) )' % (N1, PG('V'), RHS))], 'bitrd',
             '( %s -> ( p e. ran %s <-> %s ) )' % (N1, PG(CSV), RHS))
    gg2 = w.s([g2, n1(t1(rx, '( E. d e. ran %s %s <-> %s )' % (CSV, BD('d'), RHS)),
                      '( E. d e. ran %s %s <-> %s )' % (CSV, BD('d'), RHS))], 'bitr4d', '( %s -> %s )' % (N1, GOAL))
    gt = w.s([gg1, gg2], 'pm2.61dan', '( %s -> %s )' % (T1, GOAL))
    # ------------------------------------------------- out of range
    F1 = '( %s /\\ -. %s )' % (A, COND)
    f1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (F1, f))
    pf = prj(w, F1, PGO(CSV), iff, PG('V'), C2, 1,
             aex=w.s([f1(pgcl, '%s e. Word NN0' % PG('V'))], 'elexd', '( %s -> %s e. _V )' % (F1, PG('V'))),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % C2)], 'a1i', '( %s -> %s e. _V )' % (F1, C2)))
    F1B = '( %s /\\ %s )' % (F1, BDP)
    fq = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (F1B, BDP))], 'simpld',
                  '( %s -> ( %s = p /\\ p <_ X ) )' % (F1B, PP))], 'simpld', '( %s -> %s = p )' % (F1B, PP))
    fle = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (F1B, BDP))], 'simpld',
                   '( %s -> ( %s = p /\\ p <_ X ) )' % (F1B, PP))], 'simprd', '( %s -> p <_ X )' % F1B)
    fzl = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (F1B, BDP))], 'simprd',
                   '( %s -> ( Z < p /\\ p e. Prime ) )' % F1B)], 'simpld', '( %s -> Z < p )' % F1B)
    fcond = w.s([w.s([fle, w.s([fq], 'breq1d', '( %s -> ( %s <_ X <-> p <_ X ) )' % (F1B, PP))], 'mpbird',
                     '( %s -> %s <_ X )' % (F1B, PP)),
                 w.s([fzl, w.s([fq], 'breq2d', '( %s -> ( Z < %s <-> Z < p ) )' % (F1B, PP))], 'mpbird',
                     '( %s -> Z < %s )' % (F1B, PP))], 'jca', '( %s -> %s )' % (F1B, COND))
    nbdp2 = w.s([fcond, w.s([w.s([], 'simpr', '( %s -> -. %s )' % (F1, COND))], 'adantr',
                            '( %s -> -. %s )' % (F1B, COND))], 'pm2.65da', '( %s -> -. %s )' % (F1, BDP))
    g3 = w.s([w.s([w.s([pf], 'rneqd', '( %s -> ran %s = ran %s )' % (F1, PG(CSV), PG('V')))], 'eleq2d',
                  '( %s -> ( p e. ran %s <-> p e. ran %s ) )' % (F1, PG(CSV), PG('V'))),
              w.s([f1(ihp, '( p e. ran %s <-> E. d e. ran V %s )' % (PG('V'), BD('d'))),
                   w.s([nbdp2, w.s([w.s([], 'biorf', '( -. %s -> ( E. d e. ran V %s <-> %s ) )' % (BDP, BD('d'), RHS))], 'a1i',
                                   '( %s -> ( -. %s -> ( E. d e. ran V %s <-> %s ) ) )' % (F1, BDP, BD('d'), RHS))], 'mpd',
                       '( %s -> ( E. d e. ran V %s <-> %s ) )' % (F1, BD('d'), RHS))], 'bitrd',
                  '( %s -> ( p e. ran %s <-> %s ) )' % (F1, PG('V'), RHS))], 'bitrd',
             '( %s -> ( p e. ran %s <-> %s ) )' % (F1, PG(CSV), RHS))
    gf = w.s([g3, f1(rx, '( E. d e. ran %s %s <-> %s )' % (CSV, BD('d'), RHS))], 'bitr4d', '( %s -> %s )' % (F1, GOAL))
    return w.s([gt, gf], 'pm2.61dan', '( %s -> %s )' % (A, goal))

def _i(w):
    A = '( %s /\\ ( W e. Word NN0 /\\ P e. NN0 ) )' % OUT
    out = w.s([], 'simpl', '( %s -> %s )' % (A, OUT))
    ww = w.s([], 'simprl', '( %s -> W e. Word NN0 )' % A)
    pn = w.s([], 'simprr', '( %s -> P e. NN0 )' % A)
    PH = qphi(OUT, [('p', 'NN0')], subst(BODY, 's', 'W'))
    ral = w.s([w.s([ww, w.inst('poolgomem')], 'syl', '( %s -> %s )' % (A, PH)), out], 'mpd',
              '( %s -> %s )' % (A, quantify([('p', 'NN0')], ['p'], subst(BODY, 's', 'W'))))
    st, bd = instn(w, A, ral, [('p', 'NN0')], subst(BODY, 's', 'W'), ['P'], [pn])
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)

qwrd(run, 'poolgomem', OUT, [('p', 'NN0')], BODY, _b, _s, instfn=_i, only=only,
     desc='Membership in the pool loop (Lean: poolGo_mem).')

# ================================================================= poolgondp
PHI2 = "( %s -> ( Fun `' s -> Fun `' %s ) )" % (OUT, PG('s'))

def _b2(w, goal):
    A = OUT
    xx, zz, kk, xz = outs(w, A, w.s([], 'id', '( %s -> %s )' % (A, A)))
    v = w.s([xz, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (A, PGO('(/)')))
    p1 = prj(w, A, PGO('(/)'), v, '(/)', '0', 1,
             aex=w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A),
             bex=w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % A))
    bi = w.s([w.s([p1], 'cnveqd', "( %s -> `' %s = `' (/) )" % (A, PG('(/)')))], 'funeqd',
             "( %s -> ( Fun `' %s <-> Fun `' (/) ) )" % (A, PG('(/)')))
    fu = w.s([w.s([w.s([], 'algndp0', "Fun `' (/)")], 'a1i', "( %s -> Fun `' (/) )" % A), bi], 'mpbird',
             "( %s -> Fun `' %s )" % (A, PG('(/)')))
    w.qed([fu], 'a1d', goal)

def _s2(w, A, ih, co):
    U = "( %s /\\ %s )" % (A, OUT)
    up = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    vv = up(w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A), 'V e. Word NN0')
    pp = up(w.s([], 'simp2', '( %s -> P e. NN0 )' % A), 'P e. NN0')
    ihs = up(w.s([], 'simp3', '( %s -> %s )' % (A, ih)), ih)
    out = w.s([], 'simpr', '( %s -> %s )' % (U, OUT))
    xx, zz, kk, xz = outs(w, U, out)
    ihv = w.s([ihs, out], 'mpd', "( %s -> ( Fun `' V -> Fun `' %s ) )" % (U, PG('V')))
    T = "( %s /\\ Fun `' %s )" % (U, CSV)
    t = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (T, f))
    ndc = w.s([t(pp, 'P e. NN0'), t(vv, 'V e. Word NN0'), w.inst('algndpcs')], 'syl2anc',
              "( %s -> ( Fun `' %s <-> ( -. P e. ran V /\\ Fun `' V ) ) )" % (T, CSV))
    nds = w.s([w.s([], 'simpr', "( %s -> Fun `' %s )" % (T, CSV)), ndc], 'mpbid',
              "( %s -> ( -. P e. ran V /\\ Fun `' V ) )" % T)
    pnv = w.s([nds], 'simpld', '( %s -> -. P e. ran V )' % T)
    fuv = w.s([t(ihv, "( Fun `' V -> Fun `' %s )" % PG('V')), w.s([nds], 'simprd', "( %s -> Fun `' V )" % T)], 'mpd',
              "( %s -> Fun `' %s )" % (T, PG('V')))
    ppn = w.s([w.s([t(pp, 'P e. NN0'), t(kk, 'K e. NN0')], 'nn0mulcld', '( %s -> ( P x. K ) e. NN0 )' % T),
               w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (T, PP))
    pgcl = w.s([w.s([t(xz, '( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 )'), t(vv, 'V e. Word NN0'), w.inst('poolgocl')], 'syl2anc',
                    '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (T, PGO('V'))), w.inst('xp1st')], 'syl',
               '( %s -> %s e. Word NN0 )' % (T, PG('V')))
    COND = '( %s <_ X /\\ Z < %s )' % (PP, PP)
    PRM = '( 1st ` ( IsPrimeTD ` %s ) ) = 1o' % PP
    TH = 'if ( %s , ( <" %s "> ++ %s ) , %s )' % (PRM, PP, PG('V'), PG('V'))
    C1 = '( ( %s + ( 2nd ` ( IsPrimeTD ` %s ) ) ) + 1 )' % ('( 2nd ` %s )' % PGO('V'), PP)
    C2 = '( %s + 1 )' % ('( 2nd ` %s )' % PGO('V'))
    IFE = 'if ( %s , <. %s , %s >. , <. %s , %s >. )' % (COND, TH, C1, PG('V'), C2)
    val = w.s([w.s([t(xz, '( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 )'), t(pp, 'P e. NN0')], 'jca',
                   '( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ P e. NN0 ) )' % T),
               t(vv, 'V e. Word NN0'), w.inst('poolgocs')], 'syl2anc', '( %s -> %s = %s )' % (T, PGO(CSV), IFE))
    ift, iff = ifproj(w, T, PGO(CSV), val, COND, '<. %s , %s >.' % (TH, C1), '<. %s , %s >.' % (PG('V'), C2))
    GOAL = "Fun `' %s" % PG(CSV)
    # --- in range
    T1 = '( %s /\\ %s )' % (T, COND)
    t1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (T1, f))
    s1c = w.s([t1(ppn, '%s e. NN0' % PP), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (T1, PP))
    catw = w.s([s1c, t1(pgcl, '%s e. Word NN0' % PG('V')), w.inst('ccatcl')], 'syl2anc',
               '( %s -> ( <" %s "> ++ %s ) e. Word NN0 )' % (T1, PP, PG('V')))
    thw = w.s([catw, t1(pgcl, '%s e. Word NN0' % PG('V'))], 'ifcld', '( %s -> %s e. Word NN0 )' % (T1, TH))
    pt = prj(w, T1, PGO(CSV), ift, TH, C1, 1,
             aex=w.s([thw], 'elexd', '( %s -> %s e. _V )' % (T1, TH)),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % C1)], 'a1i', '( %s -> %s e. _V )' % (T1, C1)))
    prmbi = w.s([t1(ppn, '%s e. NN0' % PP), w.inst('isprimetdspec')], 'syl',
                '( %s -> ( %s <-> %s e. Prime ) )' % (T1, PRM, PP))
    U1 = '( %s /\\ %s )' % (T1, PRM)
    u1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U1, f))
    ke = w.s([w.s([], 'simpr', '( %s -> %s )' % (U1, PRM))], 'iftrued',
             '( %s -> %s = ( <" %s "> ++ %s ) )' % (U1, TH, PP, PG('V')))
    rk = w.s([u1(pt, '%s = %s' % (PG(CSV), TH)), ke], 'eqtrd',
             '( %s -> %s = ( <" %s "> ++ %s ) )' % (U1, PG(CSV), PP, PG('V')))
    ppr = w.s([u1(prmbi, '( %s <-> %s e. Prime )' % (PRM, PP)), w.s([], 'simpr', '( %s -> %s )' % (U1, PRM))], 'mpbid',
              '( %s -> %s e. Prime )' % (U1, PP))
    #   the candidate is not already there
    BDPP = '( ( ( ( d x. K ) + 1 ) = %s /\\ %s <_ X ) /\\ ( Z < %s /\\ %s e. Prime ) )' % (PP, PP, PP, PP)
    memb = w.s([w.s([u1(t1(t(out, OUT), OUT), OUT),
                     w.s([u1(t1(t(vv, 'V e. Word NN0'), 'V e. Word NN0'), 'V e. Word NN0'),
                          u1(t1(ppn, '%s e. NN0' % PP), '%s e. NN0' % PP)], 'jca',
                         '( %s -> ( V e. Word NN0 /\\ %s e. NN0 ) )' % (U1, PP))], 'jca',
                    '( %s -> ( %s /\\ ( V e. Word NN0 /\\ %s e. NN0 ) ) )' % (U1, OUT, PP)), w.inst('poolgomemi')], 'syl',
               '( %s -> ( %s e. ran %s <-> E. d e. ran V %s ) )' % (U1, PP, PG('V'), BDPP))
    D1 = '( %s /\\ d e. ran V )' % U1
    d1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D1, f))
    dn = w.s([w.s([d1(u1(t1(t(vv, 'V e. Word NN0'), 'V e. Word NN0'), 'V e. Word NN0'), 'V e. Word NN0'),
                   w.s([], 'simpr', '( %s -> d e. ran V )' % D1)], 'jca',
                  '( %s -> ( V e. Word NN0 /\\ d e. ran V ) )' % D1), w.inst('algwrdrn')], 'syl',
             '( %s -> d e. NN0 )' % D1)
    D2 = '( %s /\\ %s )' % (D1, BDPP)
    d2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D2, f))
    deq = w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (D2, BDPP))], 'simpld',
                   '( %s -> ( ( ( d x. K ) + 1 ) = %s /\\ %s <_ X ) )' % (D2, PP, PP))], 'simpld',
              '( %s -> ( ( d x. K ) + 1 ) = %s )' % (D2, PP))
    kkD = d2(d1(u1(t1(t(kk, 'K e. NN0'), 'K e. NN0'), 'K e. NN0'), 'K e. NN0'), 'K e. NN0')
    ppD = d2(d1(u1(t1(t(pp, 'P e. NN0'), 'P e. NN0'), 'P e. NN0'), 'P e. NN0'), 'P e. NN0')
    dnD = d2(dn, 'd e. NN0')
    #   K is nonzero because the candidate is prime
    KZ = '( %s /\\ K = 0 )' % D2
    kz = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (KZ, f))
    k0 = w.s([], 'simpr', '( %s -> K = 0 )' % KZ)
    pz = w.s([w.s([w.s([k0], 'oveq2d', '( %s -> ( P x. K ) = ( P x. 0 ) )' % KZ),
                   w.s([w.s([kz(ppD, 'P e. NN0')], 'nn0cnd', '( %s -> P e. CC )' % KZ)], 'mul01d',
                       '( %s -> ( P x. 0 ) = 0 )' % KZ)], 'eqtrd', '( %s -> ( P x. K ) = 0 )' % KZ)], 'oveq1d',
             '( %s -> %s = ( 0 + 1 ) )' % (KZ, PP))
    pz2 = w.s([pz, w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % KZ)], 'eqtrd',
              '( %s -> %s = 1 )' % (KZ, PP))
    p1pr = w.s([pz2, kz(d2(d1(ppr, '%s e. Prime' % PP), '%s e. Prime' % PP), '%s e. Prime' % PP)], 'eqeltrrd',
               '( %s -> 1 e. Prime )' % KZ)
    knz = w.s([p1pr, w.s([w.s([], '1nprm', '-. 1 e. Prime')], 'a1i', '( %s -> -. 1 e. Prime )' % KZ)], 'pm2.65da',
              '( %s -> -. K = 0 )' % D2)
    knn = w.s([w.s([kkD, w.s([knz, w.inst('neqned')], 'syl', '( %s -> K =/= 0 )' % D2)], 'jca',
                   '( %s -> ( K e. NN0 /\\ K =/= 0 ) )' % D2),
               w.s([w.s([], 'elnnne0', '( K e. NN <-> ( K e. NN0 /\\ K =/= 0 ) )')], 'a1i',
                   '( %s -> ( K e. NN <-> ( K e. NN0 /\\ K =/= 0 ) ) )' % D2)], 'mpbird', '( %s -> K e. NN )' % D2)
    dc = w.s([dnD], 'nn0cnd', '( %s -> d e. CC )' % D2)
    pc = w.s([ppD], 'nn0cnd', '( %s -> P e. CC )' % D2)
    kc = w.s([kkD], 'nn0cnd', '( %s -> K e. CC )' % D2)
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % D2)
    acbi = w.s([w.s([dc, kc], 'mulcld', '( %s -> ( d x. K ) e. CC )' % D2),
                w.s([pc, kc], 'mulcld', '( %s -> ( P x. K ) e. CC )' % D2), one], 'addcan2d',
               '( %s -> ( ( ( d x. K ) + 1 ) = %s <-> ( d x. K ) = ( P x. K ) ) )' % (D2, PP))
    cancadd = w.s([deq, acbi], 'mpbid', '( %s -> ( d x. K ) = ( P x. K ) )' % D2)
    deqp = w.s([w.s([dc, pc, kc, w.s([knn], 'nnne0d', '( %s -> K =/= 0 )' % D2)], 'mulcan2d',
                    '( %s -> ( ( d x. K ) = ( P x. K ) <-> d = P ) )' % D2), cancadd], 'mpbid',
               '( %s -> d = P )' % D2)
    pin = w.s([w.s([deqp], 'eqcomd', '( %s -> P = d )' % D2),
               w.s([w.s([], 'simpr', '( %s -> d e. ran V )' % D1)], 'adantr', '( %s -> d e. ran V )' % D2)], 'eqeltrd',
              '( %s -> P e. ran V )' % D2)
    contra = w.s([pin, d2(d1(u1(t1(pnv, '-. P e. ran V'), '-. P e. ran V'), '-. P e. ran V'), '-. P e. ran V')], 'pm2.65da',
                 '( %s -> -. %s )' % (D1, BDPP))
    nrx2 = w.s([contra], 'nrexdv', '( %s -> -. E. d e. ran V %s )' % (U1, BDPP))
    nmem = w.s([memb, nrx2], 'mtbird', '( %s -> -. %s e. ran %s )' % (U1, PP, PG('V')))
    ndc2 = w.s([u1(t1(ppn, '%s e. NN0' % PP), '%s e. NN0' % PP),
                u1(t1(pgcl, '%s e. Word NN0' % PG('V')), '%s e. Word NN0' % PG('V')), w.inst('algndpcs')], 'syl2anc',
               "( %s -> ( Fun `' ( <\" %s \"> ++ %s ) <-> ( -. %s e. ran %s /\\ Fun `' %s ) ) )" % (U1, PP, PG('V'), PP, PG('V'), PG('V')))
    fuc = w.s([w.s([nmem, u1(t1(fuv, "Fun `' %s" % PG('V')), "Fun `' %s" % PG('V'))], 'jca',
                   "( %s -> ( -. %s e. ran %s /\\ Fun `' %s ) )" % (U1, PP, PG('V'), PG('V'))), ndc2], 'mpbird',
              "( %s -> Fun `' ( <\" %s \"> ++ %s ) )" % (U1, PP, PG('V')))
    gu = w.s([fuc, w.s([w.s([rk], 'cnveqd', "( %s -> `' %s = `' ( <\" %s \"> ++ %s ) )" % (U1, PG(CSV), PP, PG('V')))], 'funeqd',
                       "( %s -> ( Fun `' %s <-> Fun `' ( <\" %s \"> ++ %s ) ) )" % (U1, PG(CSV), PP, PG('V')))], 'mpbird',
             '( %s -> %s )' % (U1, GOAL))
    N1 = '( %s /\\ -. %s )' % (T1, PRM)
    n1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (N1, f))
    kf = w.s([w.s([], 'simpr', '( %s -> -. %s )' % (N1, PRM))], 'iffalsed', '( %s -> %s = %s )' % (N1, TH, PG('V')))
    rnn = w.s([n1(pt, '%s = %s' % (PG(CSV), TH)), kf], 'eqtrd', '( %s -> %s = %s )' % (N1, PG(CSV), PG('V')))
    gnp = w.s([n1(t1(fuv, "Fun `' %s" % PG('V')), "Fun `' %s" % PG('V')),
               w.s([w.s([rnn], 'cnveqd', "( %s -> `' %s = `' %s )" % (N1, PG(CSV), PG('V')))], 'funeqd',
                   "( %s -> ( Fun `' %s <-> Fun `' %s ) )" % (N1, PG(CSV), PG('V')))], 'mpbird', '( %s -> %s )' % (N1, GOAL))
    gt = w.s([gu, gnp], 'pm2.61dan', '( %s -> %s )' % (T1, GOAL))
    F1 = '( %s /\\ -. %s )' % (T, COND)
    f1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (F1, f))
    pf = prj(w, F1, PGO(CSV), iff, PG('V'), C2, 1,
             aex=w.s([f1(pgcl, '%s e. Word NN0' % PG('V'))], 'elexd', '( %s -> %s e. _V )' % (F1, PG('V'))),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % C2)], 'a1i', '( %s -> %s e. _V )' % (F1, C2)))
    gf = w.s([f1(fuv, "Fun `' %s" % PG('V')),
              w.s([w.s([pf], 'cnveqd', "( %s -> `' %s = `' %s )" % (F1, PG(CSV), PG('V')))], 'funeqd',
                  "( %s -> ( Fun `' %s <-> Fun `' %s ) )" % (F1, PG(CSV), PG('V')))], 'mpbird', '( %s -> %s )' % (F1, GOAL))
    fin = w.s([gt, gf], 'pm2.61dan', '( %s -> %s )' % (T, GOAL))
    w.qed([w.s([fin], 'ex', "( %s -> ( Fun `' %s -> %s ) )" % (U, CSV, GOAL))], 'ex', '( %s -> %s )' % (A, co))

family(run, 'poolgondpl', PHI2, _b2, _s2,
       desc='The pool loop is duplicate-free, as algwrdi delivers it.', only=only)

if not only or 'poolgondp' in only:
    w = W('poolgondp', 'The pool loop is duplicate-free (Lean: poolGo_nodup).')
    A = "( %s /\\ ( W e. Word NN0 /\\ Fun `' W ) )" % OUT
    out = w.s([], 'simpl', '( %s -> %s )' % (A, OUT))
    ww = w.s([], 'simprl', '( %s -> W e. Word NN0 )' % A)
    fu = w.s([], 'simprr', "( %s -> Fun `' W )" % A)
    st = w.s([w.s([ww, w.inst('poolgondpl')], 'syl', "( %s -> ( %s -> ( Fun `' W -> Fun `' %s ) ) )" % (A, OUT, PG('W'))),
              out], 'mpd', "( %s -> ( Fun `' W -> Fun `' %s ) )" % (A, PG('W')))
    w.qed([st, fu], 'mpd', "( %s -> Fun `' %s )" % (A, PG('W')))
    run(w)

# ================================================================= poolalgspec
if not only or 'poolbd' in only:
    w = W('poolbd', 'The two readings of the pool condition agree.')
    L = '( ( D = P /\\ P <_ X ) /\\ ( Z < P /\\ P e. Prime ) )'
    R = '( ( D <_ X /\\ D e. Prime /\\ Z < D ) /\\ P = D )'
    dp = w.s([w.s([], 'simpl', '( %s -> ( D = P /\\ P <_ X ) )' % L)], 'simpld', '( %s -> D = P )' % L)
    dle = w.s([w.s([w.s([], 'simpl', '( %s -> ( D = P /\\ P <_ X ) )' % L)], 'simprd', '( %s -> P <_ X )' % L),
               w.s([dp], 'breq1d', '( %s -> ( D <_ X <-> P <_ X ) )' % L)], 'mpbird', '( %s -> D <_ X )' % L)
    dpr = w.s([w.s([w.s([], 'simpr', '( %s -> ( Z < P /\\ P e. Prime ) )' % L)], 'simprd', '( %s -> P e. Prime )' % L),
               w.s([dp], 'eleq1d', '( %s -> ( D e. Prime <-> P e. Prime ) )' % L)], 'mpbird', '( %s -> D e. Prime )' % L)
    dzl = w.s([w.s([w.s([], 'simpr', '( %s -> ( Z < P /\\ P e. Prime ) )' % L)], 'simpld', '( %s -> Z < P )' % L),
               w.s([dp], 'breq2d', '( %s -> ( Z < D <-> Z < P ) )' % L)], 'mpbird', '( %s -> Z < D )' % L)
    fwd = w.s([w.s([dle, dpr, dzl], '3jca', '( %s -> ( D <_ X /\\ D e. Prime /\\ Z < D ) )' % L),
               w.s([dp], 'eqcomd', '( %s -> P = D )' % L)], 'jca', '( %s -> %s )' % (L, R))
    pd = w.s([w.s([], 'simpr', '( %s -> P = D )' % R)], 'eqcomd', '( %s -> D = P )' % R)
    ple = w.s([w.s([w.s([], 'simpl', '( %s -> ( D <_ X /\\ D e. Prime /\\ Z < D ) )' % R)], 'simp1d',
                   '( %s -> D <_ X )' % R), w.s([pd], 'breq1d', '( %s -> ( D <_ X <-> P <_ X ) )' % R)], 'mpbid',
              '( %s -> P <_ X )' % R)
    ppr = w.s([w.s([w.s([], 'simpl', '( %s -> ( D <_ X /\\ D e. Prime /\\ Z < D ) )' % R)], 'simp2d',
                   '( %s -> D e. Prime )' % R), w.s([pd], 'eleq1d', '( %s -> ( D e. Prime <-> P e. Prime ) )' % R)], 'mpbid',
              '( %s -> P e. Prime )' % R)
    pzl = w.s([w.s([w.s([], 'simpl', '( %s -> ( D <_ X /\\ D e. Prime /\\ Z < D ) )' % R)], 'simp3d',
                   '( %s -> Z < D )' % R), w.s([pd], 'breq2d', '( %s -> ( Z < D <-> Z < P ) )' % R)], 'mpbid',
              '( %s -> Z < P )' % R)
    bwd = w.s([w.s([pd, ple], 'jca', '( %s -> ( D = P /\\ P <_ X ) )' % R),
               w.s([pzl, ppr], 'jca', '( %s -> ( Z < P /\\ P e. Prime ) )' % R)], 'jca', '( %s -> %s )' % (R, L))
    w.qed([fwd, bwd], 'impbii', '( %s <-> %s )' % (L, R))
    run(w)

PRDW = PRD('W')
XC = '( %s ^ 5 )' % PRDW
DVW = '( 1st ` ( DivisorsOf ` W ) )'
PGO5 = lambda s: '( ( ( %s PoolGo Z ) ` K ) ` %s )' % (XC, s)
PG5 = lambda s: '( 1st ` %s )' % PGO5(s)
PA5 = '( ( ( W PoolAlg %s ) ` Z ) ` K )' % XC
POOL = '( ( ran W pool Z ) ` K )'
DK = '( ( d x. K ) + 1 )'
BD1 = '( ( %s = p /\\ p <_ %s ) /\\ ( Z < p /\\ p e. Prime ) )' % (DK, XC)
BD2 = '( ( %s <_ %s /\\ %s e. Prime /\\ Z < %s ) /\\ p = %s )' % (DK, XC, DK, DK, DK)
BD2L = '( ( %s <_ ( xceil ` ran W ) /\\ %s e. Prime /\\ Z < %s ) /\\ p = %s )' % (DK, DK, DK, DK)
DIVSL = '{ m e. ( 1 ... ( Lmod ` ran W ) ) | m || ( Lmod ` ran W ) }'
def DIVS(x): return '{ m e. ( 1 ... %s ) | m || %s }' % (x, x)

def pactx(w, A, wst, fust, prst):
    """typing shared by poolalgmem and poolalgspec"""
    ffn = w.s([wst, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % A)
    ssn = w.s([ffn, w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % A)
    pw = w.s([w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'elpw2', '( ran W e. ~P NN0 <-> ran W C_ NN0 )')], 'a1i',
             '( %s -> ( ran W e. ~P NN0 <-> ran W C_ NN0 ) )' % A)
    pwm = w.s([pw, ssn], 'mpbird', '( %s -> ran W e. ~P NN0 )' % A)
    fi = w.s([wst, w.inst('algwrdfi')], 'syl', '( %s -> ran W e. Fin )' % A)
    fpw = w.s([pwm, fi], 'elind', '( %s -> ran W e. ( ~P NN0 i^i Fin ) )' % A)
    prdn = w.s([wst, w.inst('algprodcl')], 'syl', '( %s -> %s e. NN0 )' % (A, PRDW))
    xcn = w.s([prdn, w.s([w.s([], '5nn0', '5 e. NN0')], 'a1i', '( %s -> 5 e. NN0 )' % A)], 'nn0expcld',
              '( %s -> %s e. NN0 )' % (A, XC))
    lm = w.s([wst, fust, w.inst('lmodwrd')], 'syl2anc', '( %s -> ( Lmod ` ran W ) = %s )' % (A, PRDW))
    xc = w.s([wst, fust, w.inst('xceilwrd')], 'syl2anc', '( %s -> ( xceil ` ran W ) = %s )' % (A, XC))
    dsp = w.s([w.s([wst, fust, prst], '3jca', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A),
               w.inst('divisorsofspec')], 'syl',
              "( %s -> ( Fun `' %s /\\ ran %s = %s ) )" % (A, DVW, DVW, DIVS(PRDW)))
    dvcl = w.s([w.s([wst, w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` W ) e. ( Word NN0 X. NN0 ) )' % A),
                w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (A, DVW))
    return fpw, prdn, xcn, lm, xc, dsp, dvcl

if not only or 'poolalgmem' in only:
    w = W('poolalgmem', 'The pool the algorithm builds is the pool of the analysis, elementwise.')
    A = "( ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) /\\ ( Z e. NN0 /\\ K e. NN0 ) /\\ p e. NN0 )"
    ww = w.s([w.s([], 'simp1', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A)], 'simp1d',
             '( %s -> W e. Word NN0 )' % A)
    fu = w.s([w.s([], 'simp1', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A)], 'simp2d',
             "( %s -> Fun `' W )" % A)
    pr = w.s([w.s([], 'simp1', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A)], 'simp3d',
             '( %s -> A. q e. ran W q e. Prime )' % A)
    zz = w.s([w.s([], 'simp2', '( %s -> ( Z e. NN0 /\\ K e. NN0 ) )' % A)], 'simpld', '( %s -> Z e. NN0 )' % A)
    kk = w.s([w.s([], 'simp2', '( %s -> ( Z e. NN0 /\\ K e. NN0 ) )' % A)], 'simprd', '( %s -> K e. NN0 )' % A)
    pn = w.s([], 'simp3', '( %s -> p e. NN0 )' % A)
    fpw, prdn, xcn, lm, xc, dsp, dvcl = pactx(w, A, ww, fu, pr)
    rndv = w.s([dsp], 'simprd', '( %s -> ran %s = %s )' % (A, DVW, DIVS(PRDW)))
    mem = w.s([w.s([w.s([xcn, zz, kk], '3jca', '( %s -> ( %s e. NN0 /\\ Z e. NN0 /\\ K e. NN0 ) )' % (A, XC)),
                    w.s([dvcl, pn], 'jca', '( %s -> ( %s e. Word NN0 /\\ p e. NN0 ) )' % (A, DVW))], 'jca',
                   '( %s -> ( ( %s e. NN0 /\\ Z e. NN0 /\\ K e. NN0 ) /\\ ( %s e. Word NN0 /\\ p e. NN0 ) ) )' % (A, XC, DVW)),
               w.inst('poolgomemi')], 'syl', '( %s -> ( p e. ran %s <-> E. d e. ran %s %s ) )' % (A, PG5(DVW), DVW, BD1))
    bdbi = w.s([w.s([w.s([], 'poolbd', '( %s <-> %s )' % (BD1, BD2))], 'rexbii',
                    '( E. d e. ran %s %s <-> E. d e. ran %s %s )' % (DVW, BD1, DVW, BD2))], 'a1i',
               '( %s -> ( E. d e. ran %s %s <-> E. d e. ran %s %s ) )' % (A, DVW, BD1, DVW, BD2))
    # rewrite the domain and the ceiling
    dsl = w.s([lm, w.inst('divseteqi')], 'syl', '( %s -> %s = %s )' % (A, DIVSL, DIVS(PRDW)))
    domeq = w.s([dsl, w.s([rndv], 'eqcomd', '( %s -> %s = ran %s )' % (A, DIVS(PRDW), DVW))], 'eqtrd',
                '( %s -> %s = ran %s )' % (A, DIVSL, DVW))
    ceq = w.s([xc], 'breq2d', '( %s -> ( %s <_ ( xceil ` ran W ) <-> %s <_ %s ) )' % (A, DK, DK, XC))
    ceq2 = w.s([ceq], '3anbi1d',
               '( %s -> ( ( %s <_ ( xceil ` ran W ) /\\ %s e. Prime /\\ Z < %s ) <-> ( %s <_ %s /\\ %s e. Prime /\\ Z < %s ) ) )'
               % (A, DK, DK, DK, DK, XC, DK, DK))
    ceq3 = w.s([ceq2], 'anbi1d', '( %s -> ( %s <-> %s ) )' % (A, BD2L, BD2))
    rexc = w.s([ceq3], 'rexbidv', '( %s -> ( E. d e. %s %s <-> E. d e. %s %s ) )' % (A, DIVSL, BD2L, DIVSL, BD2))
    rexd = w.s([domeq], 'rexeqdv', '( %s -> ( E. d e. %s %s <-> E. d e. ran %s %s ) )' % (A, DIVSL, BD2, DVW, BD2))
    ep = w.s([w.s([fpw, zz, kk], '3jca', '( %s -> ( ran W e. ( ~P NN0 i^i Fin ) /\\ Z e. NN0 /\\ K e. NN0 ) )' % A),
              w.inst('elpool')], 'syl', '( %s -> ( p e. %s <-> E. d e. %s %s ) )' % (A, POOL, DIVSL, BD2L))
    w.qed([w.s([mem, bdbi], 'bitrd', '( %s -> ( p e. ran %s <-> E. d e. ran %s %s ) )' % (A, PG5(DVW), DVW, BD2)),
           w.s([w.s([ep, rexc], 'bitrd', '( %s -> ( p e. %s <-> E. d e. %s %s ) )' % (A, POOL, DIVSL, BD2)), rexd], 'bitrd',
               '( %s -> ( p e. %s <-> E. d e. ran %s %s ) )' % (A, POOL, DVW, BD2))], 'bitr4d',
          '( %s -> ( p e. ran %s <-> p e. %s ) )' % (A, PG5(DVW), POOL))
    run(w)

if not only or 'poolalgspec' in only:
    w = W('poolalgspec', 'Step 3 enumerates the pool without duplicates (Lean: poolAlg_spec).')
    A = "( ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) /\\ ( Z e. NN0 /\\ K e. NN0 ) )"
    ww = w.s([w.s([], 'simpl', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A)], 'simp1d',
             '( %s -> W e. Word NN0 )' % A)
    fu = w.s([w.s([], 'simpl', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A)], 'simp2d',
             "( %s -> Fun `' W )" % A)
    pr = w.s([w.s([], 'simpl', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A)], 'simp3d',
             '( %s -> A. q e. ran W q e. Prime )' % A)
    zz = w.s([], 'simprl', '( %s -> Z e. NN0 )' % A)
    kk = w.s([], 'simprr', '( %s -> K e. NN0 )' % A)
    fpw, prdn, xcn, lm, xc, dsp, dvcl = pactx(w, A, ww, fu, pr)
    fudv = w.s([dsp], 'simpld', "( %s -> Fun `' %s )" % (A, DVW))
    A3 = "( ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) /\\ ( Z e. NN0 /\\ K e. NN0 ) /\\ p e. NN0 )"
    # the value of poolAlg
    SND = '( ( 2nd ` ( DivisorsOf ` W ) ) + ( 2nd ` %s ) )' % PGO5(DVW)
    val = w.s([w.s([w.s([w.s([ww, xcn], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. NN0 ) )' % (A, XC)), zz], 'jca',
                        '( %s -> ( ( W e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 ) )' % (A, XC)), kk], 'jca',
                   '( %s -> ( ( ( W e. Word NN0 /\\ %s e. NN0 ) /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % (A, XC)),
               w.inst('poolalgval')], 'syl', '( %s -> %s = <. %s , %s >. )' % (A, PA5, PG5(DVW), SND))
    pgcl = w.s([w.s([w.s([w.s([xcn, zz], 'jca', '( %s -> ( %s e. NN0 /\\ Z e. NN0 ) )' % (A, XC)), kk], 'jca',
                         '( %s -> ( ( %s e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % (A, XC)), dvcl, w.inst('poolgocl')], 'syl2anc',
                    '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (A, PGO5(DVW))), w.inst('xp1st')], 'syl',
               '( %s -> %s e. Word NN0 )' % (A, PG5(DVW)))
    p1 = prj(w, A, PA5, val, PG5(DVW), SND, 1,
             aex=w.s([pgcl], 'elexd', '( %s -> %s e. _V )' % (A, PG5(DVW))),
             bex=w.s([w.s([], 'ovex', '%s e. _V' % SND)], 'a1i', '( %s -> %s e. _V )' % (A, SND)))
    ndp = w.s([w.s([w.s([xcn, zz, kk], '3jca', '( %s -> ( %s e. NN0 /\\ Z e. NN0 /\\ K e. NN0 ) )' % (A, XC)),
                    w.s([dvcl, fudv], 'jca', "( %s -> ( %s e. Word NN0 /\\ Fun `' %s ) )" % (A, DVW, DVW))], 'jca',
                   "( %s -> ( ( %s e. NN0 /\\ Z e. NN0 /\\ K e. NN0 ) /\\ ( %s e. Word NN0 /\\ Fun `' %s ) ) )" % (A, XC, DVW, DVW)),
               w.inst('poolgondp')], 'syl', "( %s -> Fun `' %s )" % (A, PG5(DVW)))
    fufin = w.s([ndp, w.s([w.s([p1], 'cnveqd', "( %s -> `' ( 1st ` %s ) = `' %s )" % (A, PA5, PG5(DVW)))], 'funeqd',
                          "( %s -> ( Fun `' ( 1st ` %s ) <-> Fun `' %s ) )" % (A, PA5, PG5(DVW)))], 'mpbird',
                "( %s -> Fun `' ( 1st ` %s ) )" % (A, PA5))
    # ---- ran PG5 C_ POOL
    B = '( %s /\\ p e. ran %s )' % (A, PG5(DVW))
    b = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (B, f))
    pn = w.s([w.s([b(pgcl, '%s e. Word NN0' % PG5(DVW)), w.s([], 'simpr', '( %s -> p e. ran %s )' % (B, PG5(DVW)))], 'jca',
                  '( %s -> ( %s e. Word NN0 /\\ p e. ran %s ) )' % (B, PG5(DVW), PG5(DVW))), w.inst('algwrdrn')], 'syl',
             '( %s -> p e. NN0 )' % B)
    mem1 = w.s([w.s([b(w.s([], 'simpl', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A),
                       "( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime )"),
                     b(w.s([], 'simpr', '( %s -> ( Z e. NN0 /\\ K e. NN0 ) )' % A), '( Z e. NN0 /\\ K e. NN0 )'), pn], '3jca',
                    '( %s -> %s )' % (B, A3)), w.inst('poolalgmem')], 'syl',
               '( %s -> ( p e. ran %s <-> p e. %s ) )' % (B, PG5(DVW), POOL))
    ss1 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> p e. ran %s )' % (B, PG5(DVW))), mem1], 'mpbid',
                        '( %s -> p e. %s )' % (B, POOL))], 'ex',
                   '( %s -> ( p e. ran %s -> p e. %s ) )' % (A, PG5(DVW), POOL))], 'ssrdv',
              '( %s -> ran %s C_ %s )' % (A, PG5(DVW), POOL))
    # ---- POOL C_ ran PG5
    D = '( %s /\\ p e. %s )' % (A, POOL)
    d = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D, f))
    ep = w.s([w.s([d(fpw, 'ran W e. ( ~P NN0 i^i Fin )'), d(zz, 'Z e. NN0'), d(kk, 'K e. NN0')], '3jca',
                  '( %s -> ( ran W e. ( ~P NN0 i^i Fin ) /\\ Z e. NN0 /\\ K e. NN0 ) )' % D), w.inst('elpool')], 'syl',
             '( %s -> ( p e. %s <-> E. d e. %s %s ) )' % (D, POOL, DIVSL, BD2L))
    rx = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (D, POOL)), ep], 'mpbid',
             '( %s -> E. d e. %s %s )' % (D, DIVSL, BD2L))
    E = '( %s /\\ d e. %s )' % (D, DIVSL)
    e = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (E, f))
    erd = w.s([w.s([w.s([], 'breq1', '( m = d -> ( m || ( Lmod ` ran W ) <-> d || ( Lmod ` ran W ) ) )')], 'elrab',
                   '( d e. %s <-> ( d e. ( 1 ... ( Lmod ` ran W ) ) /\\ d || ( Lmod ` ran W ) ) )' % DIVSL)], 'a1i',
              '( %s -> ( d e. %s <-> ( d e. ( 1 ... ( Lmod ` ran W ) ) /\\ d || ( Lmod ` ran W ) ) ) )' % (E, DIVSL))
    dfz = w.s([w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (E, DIVSL)), erd], 'mpbid',
                   '( %s -> ( d e. ( 1 ... ( Lmod ` ran W ) ) /\\ d || ( Lmod ` ran W ) ) )' % E)], 'simpld',
              '( %s -> d e. ( 1 ... ( Lmod ` ran W ) ) )' % E)
    dnn = w.s([w.s([w.s([dfz, w.inst('elfzelz')], 'syl', '( %s -> d e. ZZ )' % E),
                    w.s([dfz, w.inst('elfzle1')], 'syl', '( %s -> 1 <_ d )' % E)], 'jca',
                   '( %s -> ( d e. ZZ /\\ 1 <_ d ) )' % E),
               w.s([w.s([], 'elnnz1', '( d e. NN <-> ( d e. ZZ /\\ 1 <_ d ) )')], 'a1i',
                   '( %s -> ( d e. NN <-> ( d e. ZZ /\\ 1 <_ d ) ) )' % E)], 'mpbird', '( %s -> d e. NN )' % E)
    dkn = w.s([w.s([w.s([dnn], 'nnnn0d', '( %s -> d e. NN0 )' % E), e(d(kk, 'K e. NN0'), 'K e. NN0')], 'nn0mulcld',
                   '( %s -> ( d x. K ) e. NN0 )' % E), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (E, DK))
    F = '( %s /\\ %s )' % (E, BD2L)
    f = lambda st, f_: w.s([st], 'adantr', '( %s -> %s )' % (F, f_))
    peq = w.s([w.s([], 'simpr', '( %s -> %s )' % (F, BD2L))], 'simprd', '( %s -> p = %s )' % (F, DK))
    pnf = w.s([peq, f(dkn, '%s e. NN0' % DK)], 'eqeltrd', '( %s -> p e. NN0 )' % F)
    pn2 = w.s([rx, w.s([w.s([pnf], 'ex', '( %s -> ( %s -> p e. NN0 ) )' % (E, BD2L))], 'rexlimdva',
                       '( %s -> ( E. d e. %s %s -> p e. NN0 ) )' % (D, DIVSL, BD2L))], 'mpd', '( %s -> p e. NN0 )' % D)
    mem2 = w.s([w.s([d(w.s([], 'simpl', "( %s -> ( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime ) )" % A),
                       "( W e. Word NN0 /\\ Fun `' W /\\ A. q e. ran W q e. Prime )"),
                     d(w.s([], 'simpr', '( %s -> ( Z e. NN0 /\\ K e. NN0 ) )' % A), '( Z e. NN0 /\\ K e. NN0 )'), pn2], '3jca',
                    '( %s -> %s )' % (D, A3)), w.inst('poolalgmem')], 'syl',
               '( %s -> ( p e. ran %s <-> p e. %s ) )' % (D, PG5(DVW), POOL))
    ss2 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (D, POOL)), mem2], 'mpbird',
                        '( %s -> p e. ran %s )' % (D, PG5(DVW)))], 'ex',
                   '( %s -> ( p e. %s -> p e. ran %s ) )' % (A, POOL, PG5(DVW)))], 'ssrdv',
              '( %s -> %s C_ ran %s )' % (A, POOL, PG5(DVW)))
    rneq = w.s([ss1, ss2], 'eqssd', '( %s -> ran %s = %s )' % (A, PG5(DVW), POOL))
    rnfin = w.s([w.s([p1], 'rneqd', '( %s -> ran ( 1st ` %s ) = ran %s )' % (A, PA5, PG5(DVW))), rneq], 'eqtrd',
                '( %s -> ran ( 1st ` %s ) = %s )' % (A, PA5, POOL))
    w.qed([fufin, rnfin], 'jca', "( %s -> ( Fun `' ( 1st ` %s ) /\\ ran ( 1st ` %s ) = %s ) )" % (A, PA5, PA5, POOL))
    run(w)
