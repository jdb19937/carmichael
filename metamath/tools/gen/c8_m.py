"""Sortie C8, section 3: a local Lipschitz bound bounds the derivative
(dvlipbnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from cl import lift
import cl
import lin
from c8_freeze import S

L = '( ( CC _D F ) ` X )'
AL = '( abs ` %s )' % L
EPS = '( %s - K )' % AL
DX = '( D \\ { X } )'


def GB(v):
    return '( ( ( F ` %s ) - ( F ` X ) ) / ( %s - X ) )' % (v, v)


GW = '( w e. %s |-> %s )' % (DX, GB('w'))
LIM = lambda v, d, e: '( ( %s =/= X /\\ ( abs ` ( %s - X ) ) < %s ) -> ( abs ` ( ( %s ` %s ) - %s ) ) < %s )' % (v, v, d, GW, v, L, e)


def gen_dvlipbnd():
    w = W('dvlipbnd', 'A local Lipschitz bound at a point bounds the derivative there.')
    LIP = 'A. y e. D ( ( abs ` ( y - X ) ) < S -> ( abs ` ( ( F ` y ) - ( F ` X ) ) ) <_ ( K x. ( abs ` ( y - X ) ) ) )'
    A0 = '( %s /\\ ( X e. D /\\ ( K e. RR /\\ S e. RR+ ) ) /\\ %s )' % (HOL, LIP)
    assert '( %s -> %s <_ K )' % (A0, AL) == S['dvlipbnd']
    hol = w.s([], 'simp1', '( %s -> %s )' % (A0, HOL))
    xks = w.s([], 'simp2', '( %s -> ( X e. D /\\ ( K e. RR /\\ S e. RR+ ) ) )' % A0)
    lip = w.s([], 'simp3', '( %s -> %s )' % (A0, LIP))
    xd = w.s([xks, w.inst('simpl')], 'syl', '( %s -> X e. D )' % A0)
    kr = w.s([xks, w.inst('simprl')], 'syl', '( %s -> K e. RR )' % A0)
    srp = w.s([xks, w.inst('simprr')], 'syl', '( %s -> S e. RR+ )' % A0)
    fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    dd = w.s([hol, w.inst('simpr')], 'syl', '( %s -> D C_ dom ( CC _D F ) )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    xc = w.s([dcc, xd], 'sseldd', '( %s -> X e. CC )' % A0)
    DF = '( CC _D F )'
    fun = w.s([w.s([w.s([], 'dvfcn', '%s : dom %s --> CC' % (DF, DF))], 'a1i', '( %s -> %s : dom %s --> CC )' % (A0, DF, DF))], 'ffund', '( %s -> Fun %s )' % (A0, DF))
    xl = w.s([w.s([dd, xd], 'sseldd', '( %s -> X e. dom %s )' % (A0, DF)), w.s([fun, w.inst('funfvbrb')], 'syl', '( %s -> ( X e. dom %s <-> X %s %s ) )' % (A0, DF, DF, L))],
             'mpbid', '( %s -> X %s %s )' % (A0, DF, L))
    TT = '( %s |`t CC )' % TOP
    ccs = closed(w, A0, 'ssid', 'CC C_ CC')
    eld = w.s([w.s([], 'eqid', '%s = %s' % (TT, TT)), w.s([], 'eqid', '%s = %s' % (TOP, TOP)), w.s([], 'eqid', '%s = %s' % (GW, GW)), ccs, ff, dcc], 'eldv',
              '( %s -> ( X %s %s <-> ( X e. ( ( int ` %s ) ` D ) /\\ %s e. ( %s limCC X ) ) ) )' % (A0, DF, L, TT, L, GW))
    lim = w.s([w.s([xl, eld], 'mpbid', '( %s -> ( X e. ( ( int ` %s ) ` D ) /\\ %s e. ( %s limCC X ) ) )' % (A0, TT, L, GW))], 'simprd', '( %s -> %s e. ( %s limCC X ) )' % (A0, L, GW))
    Aw = '( %s /\\ w e. %s )' % (A0, DX)
    wel = w.s([w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, DX)), w.inst('eldifsn')], 'sylib', '( %s -> ( w e. D /\\ w =/= X ) )' % Aw)
    wd = w.s([wel, w.inst('simpl')], 'syl', '( %s -> w e. D )' % Aw)
    wne = w.s([wel, w.inst('simpr')], 'syl', '( %s -> w =/= X )' % Aw)
    wc = w.s([lift(w, dcc, Aw), wd], 'sseldd', '( %s -> w e. CC )' % Aw)
    gwc = w.s([w.s([w.s([lift(w, ff, Aw), wd], 'ffvelcdmd', '( %s -> ( F ` w ) e. CC )' % Aw), w.s([lift(w, ff, Aw), lift(w, xd, Aw)], 'ffvelcdmd', '( %s -> ( F ` X ) e. CC )' % Aw)],
                   'subcld', '( %s -> ( ( F ` w ) - ( F ` X ) ) e. CC )' % Aw),
               w.s([wc, lift(w, xc, Aw)], 'subcld', '( %s -> ( w - X ) e. CC )' % Aw), w.s([wc, lift(w, xc, Aw), wne], 'subne0d', '( %s -> ( w - X ) =/= 0 )' % Aw)],
              'divcld', '( %s -> %s e. CC )' % (Aw, GB('w')))
    gf = w.s([gwc, w.s([], 'eqid', '%s = %s' % (GW, GW))], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, GW, DX))
    dxc = w.s([w.s([w.s([], 'difss', '%s C_ D' % DX)], 'a1i', '( %s -> %s C_ D )' % (A0, DX)), dcc], 'sstrd', '( %s -> %s C_ CC )' % (A0, DX))
    ALLE = 'A. e e. RR+ E. d e. RR+ A. v e. %s %s' % (DX, LIM('v', 'd', 'e'))
    el3 = w.s([gf, dxc, xc], 'ellimc3', '( %s -> ( %s e. ( %s limCC X ) <-> ( %s e. CC /\\ %s ) ) )' % (A0, L, GW, L, ALLE))
    alle = w.s([w.s([lim, el3], 'mpbid', '( %s -> ( %s e. CC /\\ %s ) )' % (A0, L, ALLE))], 'simprd', '( %s -> %s )' % (A0, ALLE))
    lc = w.s([w.s([lim, el3], 'mpbid', '( %s -> ( %s e. CC /\\ %s ) )' % (A0, L, ALLE))], 'simpld', '( %s -> %s e. CC )' % (A0, L))
    alr = w.s([lc], 'abscld', '( %s -> %s e. RR )' % (A0, AL))
    # ---- assume K < |L|
    AC = '( %s /\\ K < %s )' % (A0, AL)
    kl = w.s([], 'simpr', '( %s -> K < %s )' % (AC, AL))
    epr = w.s([lift(w, alr, AC), lift(w, kr, AC)], 'resubcld', '( %s -> %s e. RR )' % (AC, EPS))
    epp = w.s([kl, w.s([lift(w, kr, AC), lift(w, alr, AC)], 'posdifd', '( %s -> ( K < %s <-> 0 < %s ) )' % (AC, AL, EPS))], 'mpbid', '( %s -> 0 < %s )' % (AC, EPS))
    eprp = w.s([epr, epp], 'elrpd', '( %s -> %s e. RR+ )' % (AC, EPS))
    EXD = 'E. d e. RR+ A. v e. %s %s' % (DX, LIM('v', 'd', EPS))
    c1 = w.s([], 'breq2', '( e = %s -> ( ( abs ` ( ( %s ` v ) - %s ) ) < e <-> ( abs ` ( ( %s ` v ) - %s ) ) < %s ) )' % (EPS, GW, L, GW, L, EPS))
    c2 = w.s([c1], 'imbi2d', '( e = %s -> ( %s <-> %s ) )' % (EPS, LIM('v', 'd', 'e'), LIM('v', 'd', EPS)))
    c3 = w.s([c2], 'ralbidv', '( e = %s -> ( A. v e. %s %s <-> A. v e. %s %s ) )' % (EPS, DX, LIM('v', 'd', 'e'), DX, LIM('v', 'd', EPS)))
    c4 = w.s([c3], 'rexbidv', '( e = %s -> ( E. d e. RR+ A. v e. %s %s <-> %s ) )' % (EPS, DX, LIM('v', 'd', 'e'), EXD))
    exd = w.s([c4, lift(w, alle, AC), eprp], 'rspcdva', '( %s -> %s )' % (AC, EXD))
    BALL = 'A. z e. CC ( ( abs ` ( z - X ) ) < r -> z e. D )'
    dop = w.s([hol, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    exr = w.s([dop, xd, w.inst('cnopnbl')], 'syl2anc', '( %s -> E. r e. RR+ %s )' % (A0, BALL))
    AD = '( %s /\\ d e. RR+ )' % AC
    ALLV = 'A. v e. %s %s' % (DX, LIM('v', 'd', EPS))
    AD2 = '( %s /\\ %s )' % (AD, ALLV)
    AR = '( %s /\\ r e. RR+ )' % AD2
    A5 = '( %s /\\ %s )' % (AR, BALL)
    Lf = lambda st: lift(w, st, A5)
    drp = Lf(w.s([], 'simpr', '( %s -> d e. RR+ )' % AD))
    allv = Lf(w.s([], 'simpr', '( %s -> %s )' % (AD2, ALLV)))
    rrp = Lf(w.s([], 'simpr', '( %s -> r e. RR+ )' % AR))
    ball = w.s([], 'simpr', '( %s -> %s )' % (A5, BALL))
    srp5 = Lf(srp)
    M1 = 'if ( d <_ r , d , r )'
    M2 = 'if ( %s <_ S , %s , S )' % (M1, M1)
    T = '( %s / 2 )' % M2
    m1 = w.s([drp, rrp, w.inst('ifcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A5, M1))
    m2 = w.s([m1, srp5, w.inst('ifcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A5, M2))
    tp = w.s([m2], 'rphalfcld', '( %s -> %s e. RR+ )' % (A5, T))
    rd = lambda st, e: w.s([st], 'rpred', '( %s -> %s e. RR )' % (A5, e))
    dr, rr_, sr, m1r, m2r, tr = rd(drp, 'd'), rd(rrp, 'r'), rd(srp5, 'S'), rd(m1, M1), rd(m2, M2), rd(tp, T)
    tm2 = w.s([m2, w.inst('rphalflt')], 'syl', '( %s -> %s < %s )' % (A5, T, M2))
    m2m1 = w.s([m1r, sr, w.inst('min1')], 'syl2anc', '( %s -> %s <_ %s )' % (A5, M2, M1))
    m2s = w.s([m1r, sr, w.inst('min2')], 'syl2anc', '( %s -> %s <_ S )' % (A5, M2))
    m1d = w.s([dr, rr_, w.inst('min1')], 'syl2anc', '( %s -> %s <_ d )' % (A5, M1))
    m1r2 = w.s([dr, rr_, w.inst('min2')], 'syl2anc', '( %s -> %s <_ r )' % (A5, M1))
    tm1 = w.s([tr, m2r, m1r, tm2, m2m1], 'ltletrd', '( %s -> %s < %s )' % (A5, T, M1))
    td = w.s([tr, m1r, dr, tm1, m1d], 'ltletrd', '( %s -> %s < d )' % (A5, T))
    trr = w.s([tr, m1r, rr_, tm1, m1r2], 'ltletrd', '( %s -> %s < r )' % (A5, T))
    ts = w.s([tr, m2r, sr, tm2, m2s], 'ltletrd', '( %s -> %s < S )' % (A5, T))
    Z = '( X + %s )' % T
    xc5 = Lf(xc)
    tc = w.s([tr], 'recnd', '( %s -> %s e. CC )' % (A5, T))
    zc = w.s([xc5, tc], 'addcld', '( %s -> %s e. CC )' % (A5, Z))
    zx = w.s([xc5, tc], 'pncan2d', '( %s -> ( %s - X ) = %s )' % (A5, Z, T))
    DZ = '( abs ` ( %s - X ) )' % Z
    azx = w.s([w.s([zx], 'fveq2d', '( %s -> %s = ( abs ` %s ) )' % (A5, DZ, T)), w.s([tr, w.s([tp], 'rpge0d', '( %s -> 0 <_ %s )' % (A5, T))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A5, T, T))],
              'eqtrd', '( %s -> %s = %s )' % (A5, DZ, T))
    lt = lambda st, b: w.s([azx, st], 'eqbrtrd', '( %s -> %s < %s )' % (A5, DZ, b))
    zd_, zr, zs = lt(td, 'd'), lt(trr, 'r'), lt(ts, 'S')
    subz = w.s([w.s([w.s([w.s([], 'oveq1', '( z = %s -> ( z - X ) = ( %s - X ) )' % (Z, Z))], 'fveq2d', '( z = %s -> ( abs ` ( z - X ) ) = %s )' % (Z, DZ))], 'breq1d',
                    '( z = %s -> ( ( abs ` ( z - X ) ) < r <-> %s < r ) )' % (Z, DZ)), w.s([], 'eleq1', '( z = %s -> ( z e. D <-> %s e. D ) )' % (Z, Z))], 'imbi12d',
               '( z = %s -> ( ( ( abs ` ( z - X ) ) < r -> z e. D ) <-> ( %s < r -> %s e. D ) ) )' % (Z, DZ, Z))
    zdd = w.s([zr, w.s([subz, ball, zc], 'rspcdva', '( %s -> ( %s < r -> %s e. D ) )' % (A5, DZ, Z))], 'mpd', '( %s -> %s e. D )' % (A5, Z))
    zne = w.s([w.s([zx, w.s([tp], 'rpne0d', '( %s -> %s =/= 0 )' % (A5, T))], 'eqnetrd', '( %s -> ( %s - X ) =/= 0 )' % (A5, Z))], 'subne0ad', '( %s -> %s =/= X )' % (A5, Z))
    zdx = w.s([w.s([zdd, zne], 'jca', '( %s -> ( %s e. D /\\ %s =/= X ) )' % (A5, Z, Z)), w.inst('eldifsn')], 'sylibr', '( %s -> %s e. %s )' % (A5, Z, DX))
    GV = '( %s ` %s )' % (GW, Z)
    subv = w.s([w.s([w.s([], 'neeq1', '( v = %s -> ( v =/= X <-> %s =/= X ) )' % (Z, Z)),
                     w.s([w.s([w.s([], 'oveq1', '( v = %s -> ( v - X ) = ( %s - X ) )' % (Z, Z))], 'fveq2d', '( v = %s -> ( abs ` ( v - X ) ) = %s )' % (Z, DZ))], 'breq1d',
                         '( v = %s -> ( ( abs ` ( v - X ) ) < d <-> %s < d ) )' % (Z, DZ))], 'anbi12d',
                    '( v = %s -> ( ( v =/= X /\\ ( abs ` ( v - X ) ) < d ) <-> ( %s =/= X /\\ %s < d ) ) )' % (Z, Z, DZ)),
                w.s([w.s([w.s([w.s([], 'fveq2', '( v = %s -> ( %s ` v ) = %s )' % (Z, GW, GV))], 'fvoveq1d' if False else 'oveq1d', '( v = %s -> ( ( %s ` v ) - %s ) = ( %s - %s ) )' % (Z, GW, L, GV, L))],
                         'fveq2d', '( v = %s -> ( abs ` ( ( %s ` v ) - %s ) ) = ( abs ` ( %s - %s ) ) )' % (Z, GW, L, GV, L))], 'breq1d',
                    '( v = %s -> ( ( abs ` ( ( %s ` v ) - %s ) ) < %s <-> ( abs ` ( %s - %s ) ) < %s ) )' % (Z, GW, L, EPS, GV, L, EPS))], 'imbi12d',
               '( v = %s -> ( %s <-> ( ( %s =/= X /\\ %s < d ) -> ( abs ` ( %s - %s ) ) < %s ) ) )' % (Z, LIM('v', 'd', EPS), Z, DZ, GV, L, EPS))
    limz = w.s([w.s([zne, zd_], 'jca', '( %s -> ( %s =/= X /\\ %s < d ) )' % (A5, Z, DZ)),
                w.s([subv, allv, zdx], 'rspcdva', '( %s -> ( ( %s =/= X /\\ %s < d ) -> ( abs ` ( %s - %s ) ) < %s ) )' % (A5, Z, DZ, GV, L, EPS))], 'mpd',
               '( %s -> ( abs ` ( %s - %s ) ) < %s )' % (A5, GV, L, EPS))
    FD = '( abs ` ( ( F ` %s ) - ( F ` X ) ) )' % Z
    suby = w.s([w.s([w.s([w.s([], 'oveq1', '( y = %s -> ( y - X ) = ( %s - X ) )' % (Z, Z))], 'fveq2d', '( y = %s -> ( abs ` ( y - X ) ) = %s )' % (Z, DZ))], 'breq1d',
                    '( y = %s -> ( ( abs ` ( y - X ) ) < S <-> %s < S ) )' % (Z, DZ)),
                w.s([w.s([w.s([w.s([], 'fveq2', '( y = %s -> ( F ` y ) = ( F ` %s ) )' % (Z, Z))], 'oveq1d', '( y = %s -> ( ( F ` y ) - ( F ` X ) ) = ( ( F ` %s ) - ( F ` X ) ) )' % (Z, Z))],
                         'fveq2d', '( y = %s -> ( abs ` ( ( F ` y ) - ( F ` X ) ) ) = %s )' % (Z, FD)),
                     w.s([w.s([w.s([], 'oveq1', '( y = %s -> ( y - X ) = ( %s - X ) )' % (Z, Z))], 'fveq2d', '( y = %s -> ( abs ` ( y - X ) ) = %s )' % (Z, DZ))], 'oveq2d',
                         '( y = %s -> ( K x. ( abs ` ( y - X ) ) ) = ( K x. %s ) )' % (Z, DZ))], 'breq12d',
                    '( y = %s -> ( ( abs ` ( ( F ` y ) - ( F ` X ) ) ) <_ ( K x. ( abs ` ( y - X ) ) ) <-> %s <_ ( K x. %s ) ) )' % (Z, FD, DZ))], 'imbi12d',
               '( y = %s -> ( ( ( abs ` ( y - X ) ) < S -> ( abs ` ( ( F ` y ) - ( F ` X ) ) ) <_ ( K x. ( abs ` ( y - X ) ) ) ) <-> ( %s < S -> %s <_ ( K x. %s ) ) ) )' % (Z, DZ, FD, DZ))
    lipz = w.s([zs, w.s([suby, Lf(lip), zdd], 'rspcdva', '( %s -> ( %s < S -> %s <_ ( K x. %s ) ) )' % (A5, DZ, FD, DZ))], 'mpd', '( %s -> %s <_ ( K x. %s ) )' % (A5, FD, DZ))
    subw = w.s([w.s([w.s([], 'fveq2', '( w = %s -> ( F ` w ) = ( F ` %s ) )' % (Z, Z))], 'oveq1d', '( w = %s -> ( ( F ` w ) - ( F ` X ) ) = ( ( F ` %s ) - ( F ` X ) ) )' % (Z, Z)),
                     w.s([], 'oveq1', '( w = %s -> ( w - X ) = ( %s - X ) )' % (Z, Z))], 'oveq12d', '( w = %s -> %s = %s )' % (Z, GB('w'), GB(Z)))
    gvz = mptval(w, A5, 'w', DX, GW, Z, GB(Z), subw, zdx)
    fz = w.s([Lf(ff), zdd], 'ffvelcdmd', '( %s -> ( F ` %s ) e. CC )' % (A5, Z))
    fx = w.s([Lf(ff), Lf(xd)], 'ffvelcdmd', '( %s -> ( F ` X ) e. CC )' % A5)
    fdc = w.s([fz, fx], 'subcld', '( %s -> ( ( F ` %s ) - ( F ` X ) ) e. CC )' % (A5, Z))
    zxc = w.s([zc, xc5], 'subcld', '( %s -> ( %s - X ) e. CC )' % (A5, Z))
    agv = w.s([w.s([gvz], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A5, GV, GB(Z))),
               w.s([fdc, zxc, w.s([zx, w.s([tp], 'rpne0d', '( %s -> %s =/= 0 )' % (A5, T))], 'eqnetrd', '( %s -> ( %s - X ) =/= 0 )' % (A5, Z))], 'absdivd',
                   '( %s -> ( abs ` %s ) = ( %s / %s ) )' % (A5, GB(Z), FD, DZ))], 'eqtrd', '( %s -> ( abs ` %s ) = ( %s / %s ) )' % (A5, GV, FD, DZ))
    fdr = w.s([fdc], 'abscld', '( %s -> %s e. RR )' % (A5, FD))
    dzr = w.s([zxc], 'abscld', '( %s -> %s e. RR )' % (A5, DZ))
    dzp = w.s([w.s([tp], 'rpgt0d', '( %s -> 0 < %s )' % (A5, T)), azx], 'breqtrrd', '( %s -> 0 < %s )' % (A5, DZ))
    k5 = Lf(kr)
    lipc = w.s([lipz, w.s([w.s([k5], 'recnd', '( %s -> K e. CC )' % A5), w.s([dzr], 'recnd', '( %s -> %s e. CC )' % (A5, DZ))], 'mulcomd',
                          '( %s -> ( K x. %s ) = ( %s x. K ) )' % (A5, DZ, DZ))], 'breqtrd', '( %s -> %s <_ ( %s x. K ) )' % (A5, FD, DZ))
    gk0 = w.s([lipc, w.s([fdr, k5, w.s([dzr, dzp], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A5, DZ, DZ)), w.inst('ledivmul')], 'syl3anc',
                         '( %s -> ( ( %s / %s ) <_ K <-> %s <_ ( %s x. K ) ) )' % (A5, FD, DZ, FD, DZ))], 'mpbird', '( %s -> ( %s / %s ) <_ K )' % (A5, FD, DZ))
    gk = w.s([agv, gk0], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ K )' % (A5, GV))
    gvc = w.s([w.s([Lf(gf), zdx], 'ffvelcdmd', '( %s -> %s e. CC )' % (A5, GV))], 'idi', '( %s -> %s e. CC )' % (A5, GV))
    lc5 = Lf(lc)
    tri = w.s([lc5, gvc], 'abs2difd', '( %s -> ( %s - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) ) )' % (A5, AL, GV, L, GV))
    tri2 = w.s([tri, w.s([lc5, gvc], 'abssubd', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A5, L, GV, GV, L))], 'breqtrd',
               '( %s -> ( %s - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) ) )' % (A5, AL, GV, GV, L))
    lv = {AL: Lf(alr), '( abs ` %s )' % GV: w.s([gvc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A5, GV)),
          '( abs ` ( %s - %s ) )' % (GV, L): w.s([w.s([gvc, lc5], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A5, GV, L))], 'abscld', '( %s -> ( abs ` ( %s - %s ) ) e. RR )' % (A5, GV, L)),
          'K': k5}
    cl_ = cl.Closure(w, A5, lv)
    for k in lv:
        cl_.atom(k)
    bad = lin.linarith(w, A5, [tri2, gk, limz], '%s < %s' % (AL, AL), closure=cl_)
    fin5 = w.s([bad, w.s([Lf(alr)], 'ltnrd', '( %s -> -. %s < %s )' % (A5, AL, AL))], 'pm2.21dd', '( %s -> %s <_ K )' % (A5, AL))
    r1 = w.s([w.s([fin5], 'ex', '( %s -> ( %s -> %s <_ K ) )' % (AR, BALL, AL))], 'rexlimdva', '( %s -> ( E. r e. RR+ %s -> %s <_ K ) )' % (AD2, BALL, AL))
    r2 = w.s([r1, lift(w, exr, AD2)], 'mpd', '( %s -> %s <_ K )' % (AD2, AL))
    r3 = w.s([w.s([r2], 'ex', '( %s -> ( %s -> %s <_ K ) )' % (AD, ALLV, AL))], 'rexlimdva', '( %s -> ( %s -> %s <_ K ) )' % (AC, EXD, AL))
    case1 = w.s([r3, exd], 'mpd', '( %s -> %s <_ K )' % (AC, AL))
    AN = '( %s /\\ -. K < %s )' % (A0, AL)
    case2 = w.s([w.s([], 'simpr', '( %s -> -. K < %s )' % (AN, AL)), w.s([lift(w, alr, AN), lift(w, kr, AN)], 'lenltd', '( %s -> ( %s <_ K <-> -. K < %s ) )' % (AN, AL, AL))],
                'mpbird', '( %s -> %s <_ K )' % (AN, AL))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s <_ K )' % (A0, AL))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_dvlipbnd]:
        g()
