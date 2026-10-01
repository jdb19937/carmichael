"""Sortie TP: the bound on a Newton coefficient over the square (tpbb, the coefficient estimate inside Lean
exists_window_interpolant: ` abs b_K <_ ( 4 R / pi ) ( 1 / ( 1 - R ) ) ^ Y / prod_( g e. K ) abs ( R - d_g ) ` )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift
import cl as _cl
import ef2lib as E
import mvlib
from z4blib import fvmd
from tp_g import FY, CN0, TPI, FRAB
from tp_k import DS, RA, IA, AR, BR, FRS, CRS, INSR, sqbase

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


PK = 'prod_ g e. K ( d - ( V ` g ) )'
GK = '( d e. %s |-> ( ( %s ` d ) / %s ) )' % (FRS, FY, PK)
PL = 'prod_ g e. K ( abs ` ( R - %s ) )' % DS('( V ` g )')
MB = '( ( ( 1 / ( 1 - R ) ) ^ Y ) / %s )' % PL
BA = ('( ( R e. RR /\\ 0 < R /\\ R < 1 ) /\\ ( Y e. NN /\\ ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ K C_ ( 0 ..^ N ) ) /\\ '
      'A. r e. ( 0 ..^ N ) %s =/= R )' % DS('( V ` r )'))
S['tpbb'] = '( %s -> ( abs ` ( ( %s rectint <. %s , %s >. ) / %s ) ) <_ ( ( ( 4 x. R ) / _pi ) x. %s ) )' % (BA, GK, AR, BR, TPI, MB)


def gen_bb():
    w = W('tpbb', 'The Newton coefficient bound on the square: ` abs ( ( 1 / 2 pi i ) rectint ( 1 / d ) ^ Y / prod_( g e. K ) ( d - V_g ) ) <_ '
               '( 4 R / pi ) ( 1 / ( 1 - R ) ) ^ Y / prod_( g e. K ) abs ( R - d_g ) ` , ` d_g ` the sup-norm distance of ` V_g ` from 1 '
               '(Lean ` exists_window_interpolant ` , its coefficient estimate; the perimeter ` 8 R ` replaces ` 2 pi R ` ).')
    A0 = BA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( R e. RR /\\ 0 < R /\\ R < 1 )'); t2 = s([], 'simp2', '( Y e. NN /\\ ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ K C_ ( 0 ..^ N ) )')
    alln = s([], 'simp3', 'A. r e. ( 0 ..^ N ) %s =/= R' % DS('( V ` r )'))
    rr = s([t1], 'simp1d', 'R e. RR'); r0 = s([t1], 'simp2d', '0 < R'); r1 = s([t1], 'simp3d', 'R < 1')
    yn = s([t2], 'simp1d', 'Y e. NN'); nv = s([t2], 'simp2d', '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )'); ks = s([t2], 'simp3d', 'K C_ ( 0 ..^ N )')
    vf = s([nv], 'simprd', 'V : ( 0 ..^ N ) --> CC')
    c = Closure(w, A0, {'R': ('RR', rr), 'Y': ('NN', yn)})
    omr = lin.linarith(w, A0, [r1], '0 < ( 1 - R )', closure=c)
    c.have('( 1 - R )', 'gt0', omr)
    d = sqbase(w, A0, c)
    geo1 = lin.linarith(w, A0, [d['ra'], d['rb'], r0], '( Re ` %s ) <_ ( Re ` %s )' % (AR, BR), closure=c)
    geo2 = lin.linarith(w, A0, [d['ia'], d['ib'], r0], '( Im ` %s ) <_ ( Im ` %s )' % (AR, BR), closure=c)
    geo = s([geo1, geo2], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (AR, BR, AR, BR))
    fru = s([d['ab'], geo, w.inst('crectfru')], 'syl2anc', '%s C_ %s' % (FRS, CRS))
    ra0 = s([omr, d['ra']], 'breqtrrd', '0 < ( Re ` %s )' % AR)
    rh = s([s([d['ab'], ra0], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ 0 < ( Re ` %s ) )' % (AR, BR, AR)), w.inst('ef2rhp')], 'syl',
           '( %s C_ %s /\\ %s C_ %s )' % (CRS, E.HP0, CRS, CN0))
    frc = s([fru, s([rh], 'simprd', '%s C_ %s' % (CRS, CN0))], 'sstrd', '%s C_ %s' % (FRS, CN0))
    frcc = s([frc, s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % FRS)
    # node facts at q e. K: V_q e. CC, DS ( V_q ) =/= R, V_q off the frame
    def node(Kc, qv, qinK):
        qN = w.s([_cl.lift(w, ks, Kc), qinK], 'sseldd', '( %s -> %s e. ( 0 ..^ N ) )' % (Kc, qv))
        vq = w.s([_cl.lift(w, vf, Kc), qN], 'ffvelcdmd', '( %s -> ( V ` %s ) e. CC )' % (Kc, qv))
        idr = w.s([], 'id', '( r = %s -> r = %s )' % (qv, qv))
        cg, nw = w.wcongr('%s =/= R' % DS('( V ` r )'), {'r': qv}, 'r = %s' % qv, {'r': idr})
        dq = w.s([qN, _cl.lift(w, alln, Kc), w.s([cg], 'rspcv', '( %s e. ( 0 ..^ N ) -> ( A. r e. ( 0 ..^ N ) %s =/= R -> %s ) )' % (qv, DS('( V ` r )'), nw))],
                 'sylc', '( %s -> %s )' % (Kc, nw))
        sv = w.s([w.s([w.s([_cl.lift(w, rr, Kc), _cl.lift(w, r0, Kc)], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % Kc), w.s([vq, dq], 'jca', '( %s -> ( ( V ` %s ) e. CC /\\ %s ) )' % (Kc, qv, nw))],
                      'jca', '( %s -> ( ( R e. RR /\\ 0 < R ) /\\ ( ( V ` %s ) e. CC /\\ %s ) ) )' % (Kc, qv, nw)), w.inst('tpsqv')], 'syl',
                 '( %s -> ( -. ( V ` %s ) e. %s /\\ ( ( V ` %s ) e. %s -> %s ) /\\ ( %s <-> %s < R ) ) )' % (Kc, qv, FRS, qv, CRS, INSR('( V ` %s )' % qv), INSR('( V ` %s )' % qv), DS('( V ` %s )' % qv)))
        off = w.s([sv], 'simp1d', '( %s -> -. ( V ` %s ) e. %s )' % (Kc, qv, FRS))
        return vq, dq, off
    # the frame avoids every node of K
    Ax = '( %s /\\ x e. %s )' % (A0, FRS)
    Axq = '( %s /\\ q e. K )' % Ax
    _, _, offq = node(Axq, 'q', w.s([], 'simpr', '( %s -> q e. K )' % Axq))
    neq = w.s([_cl.lift(w, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, FRS)), Axq), offq, w.inst('nelne2')], 'syl2anc', '( %s -> x =/= ( V ` q ) )' % Axq)
    avoid = w.s([w.s([neq], 'ralrimiva', '( %s -> A. q e. K x =/= ( V ` q ) )' % Ax)], 'ralrimiva', '( %s -> A. x e. %s A. q e. K x =/= ( V ` q ) )' % (A0, FRS))
    # continuity of GK
    GC = tsub(stmt('tpgcn'), {'E': FRS, 'C': '1'})
    ga, gc = ante_of(GC)
    have = {'Y e. NN': yn, '1 e. CC': s([], '1cnd', '1 e. CC'), '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )': nv, 'K C_ ( 0 ..^ N )': ks,
            '%s C_ %s' % (FRS, CN0): frc, body_of(w, avoid): avoid}
    g1 = s([conj(w, A0, ga, have), w.inst('tpgcn')], 'syl', gc)
    Ad = '( %s /\\ d e. %s )' % (A0, FRS)
    dfr = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, FRS))
    cd = Closure(w, Ad, {})
    fyh = w.s([_cl.lift(w, yn, Ad), w.inst('tpfh')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (Ad, FY, CN0, CN0, FY))
    fyf = w.s([w.s([fyh], 'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Ad, FY, CN0)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Ad, FY, CN0))
    fyv = w.s([fyf, w.s([_cl.lift(w, frc, Ad), dfr], 'sseldd', '( %s -> d e. %s )' % (Ad, CN0))], 'ffvelcdmd', '( %s -> ( %s ` d ) e. CC )' % (Ad, FY))
    cd.have('( %s ` d )' % FY, 'CC', fyv); cd.atom('( %s ` d )' % FY)
    Adg = '( %s /\\ g e. K )' % Ad
    vg, _, offg = node(Adg, 'g', w.s([], 'simpr', '( %s -> g e. K )' % Adg))
    dc = w.s([_cl.lift(w, frcc, Ad), dfr], 'sseldd', '( %s -> d e. CC )' % Ad)
    cdg = Closure(w, Adg, {'d': ('CC', _cl.lift(w, dc, Adg)), '( V ` g )': ('CC', vg)}); cdg.atom('( V ` g )')
    dne = w.s([_cl.lift(w, dfr, Adg), offg, w.inst('nelne2')], 'syl2anc', '( %s -> d =/= ( V ` g ) )' % Adg)
    cdg.have('( d - ( V ` g ) )', 'ne0', ap(w, Adg, 'subne0d', '( d - ( V ` g ) ) =/= 0', cdg, facts=[dne]))
    kf = s([s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin'), ks, w.inst('ssfi')], 'syl2anc', 'K e. Fin')
    pdc = w.s([_cl.lift(w, kf, Ad), cdg.mem('( d - ( V ` g ) )', 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Ad, PK))
    pdn = w.s([_cl.lift(w, kf, Ad), cdg.mem('( d - ( V ` g ) )', 'CC'), cdg.ne0('( d - ( V ` g ) )')], 'fprodn0', '( %s -> %s =/= 0 )' % (Ad, PK))
    cd.have(PK, 'CC', pdc); cd.have(PK, 'ne0', pdn); cd.atom(PK)
    Q1 = '( ( %s ` d ) / %s )' % (FY, PK)
    meq = w.s([ap(w, Ad, 'mullidd', '( 1 x. %s ) = %s' % (Q1, Q1), cd)], 'mpteq2dva', '( %s -> ( d e. %s |-> ( 1 x. %s ) ) = %s )' % (A0, FRS, Q1, GK))
    gcn = s([meq, g1], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (GK, FRS))
    # pointwise bound on the frame
    Au = '( %s /\\ u e. %s )' % (A0, FRS)
    ufr = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, FRS))
    Lu = lambda st: _cl.lift(w, st, Au)
    sq = w.s([w.s([w.s([Lu(rr), Lu(r0)], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % Au), ufr], 'jca', '( %s -> ( ( R e. RR /\\ 0 < R ) /\\ u e. %s ) )' % (Au, FRS)),
              w.inst('tpsqf')], 'syl', '( %s -> ( %s = R /\\ ( 1 - R ) <_ ( abs ` u ) ) )' % (Au, DS('u')))
    dsu = w.s([sq], 'simpld', '( %s -> %s = R )' % (Au, DS('u'))); mod = w.s([sq], 'simprd', '( %s -> ( 1 - R ) <_ ( abs ` u ) )' % Au)
    uc = w.s([Lu(frcc), ufr], 'sseldd', '( %s -> u e. CC )' % Au)
    ucn = w.s([Lu(frc), ufr], 'sseldd', '( %s -> u e. %s )' % (Au, CN0))
    cu = Closure(w, Au, {'R': ('RR', Lu(rr)), 'Y': ('NN', Lu(yn)), 'u': ('CC', uc)})
    cu.have('( 1 - R )', 'RR+', w.s([Lu(c.mem('( 1 - R )', 'RR')), Lu(omr)], 'elrpd', '( %s -> ( 1 - R ) e. RR+ )' % Au))
    cu.have('( abs ` u )', 'RR', cu.mem('( abs ` u )', 'RR')); cu.atom('( abs ` u )')
    aup = lin.linarith(w, Au, [mod, Lu(omr)], '0 < ( abs ` u )', closure=cu)
    cu.have('( abs ` u )', 'RR+', w.s([cu.mem('( abs ` u )', 'RR'), aup], 'elrpd', '( %s -> ( abs ` u ) e. RR+ )' % Au))
    un0 = w.s([w.s([ucn, w.s([], 'eldifsn', '( u e. %s <-> ( u e. CC /\\ u =/= 0 ) )' % CN0)], 'sylib', '( %s -> ( u e. CC /\\ u =/= 0 ) )' % Au), w.inst('simpr')], 'syl', '( %s -> u =/= 0 )' % Au)
    cu.have('u', 'ne0', un0)
    FU = '( %s ` u )' % FY
    fyu = fvmd(w, Au, 'o', CN0, '( ( 1 / o ) ^ Y )', 'u', ucn, cu.mem('( ( 1 / u ) ^ Y )', 'CC'))
    PU = 'prod_ g e. K ( u - ( V ` g ) )'
    Aug = '( %s /\\ g e. K )' % Au
    vgu, dgu, offgu = node(Aug, 'g', w.s([], 'simpr', '( %s -> g e. K )' % Aug))
    cug = Closure(w, Aug, {'u': ('CC', _cl.lift(w, uc, Aug)), '( V ` g )': ('CC', vgu), 'R': ('RR', _cl.lift(w, rr, Aug))}); cug.atom('( V ` g )')
    une = w.s([_cl.lift(w, ufr, Aug), offgu, w.inst('nelne2')], 'syl2anc', '( %s -> u =/= ( V ` g ) )' % Aug)
    cug.have('( u - ( V ` g ) )', 'ne0', ap(w, Aug, 'subne0d', '( u - ( V ` g ) ) =/= 0', cug, facts=[une]))
    kfu = Lu(kf)
    puc = w.s([kfu, cug.mem('( u - ( V ` g ) )', 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Au, PU))
    pun = w.s([kfu, cug.mem('( u - ( V ` g ) )', 'CC'), cug.ne0('( u - ( V ` g ) )')], 'fprodn0', '( %s -> %s =/= 0 )' % (Au, PU))
    cu.have(PU, 'CC', puc); cu.have(PU, 'ne0', pun); cu.atom(PU)
    gv = fvmd(w, Au, 'd', FRS, '( ( %s ` d ) / %s )' % (FY, PK), 'u', ufr, w.s([], 'ovexd', '( %s -> ( %s / %s ) e. _V )' % (Au, FU, PU)))
    # abs ( GK ` u ) = abs ( ( 1 / u ) ^ Y ) / abs PU
    WU = '( ( 1 / u ) ^ Y )'
    cu.have(WU, 'CC', cu.mem(WU, 'CC')); cu.atom(WU)
    g2 = w.s([gv, w.s([fyu], 'oveq1d', '( %s -> ( %s / %s ) = ( %s / %s ) )' % (Au, FU, PU, WU, PU))], 'eqtrd', '( %s -> ( %s ` u ) = ( %s / %s ) )' % (Au, GK, WU, PU))
    a1 = w.s([g2], 'fveq2d', '( %s -> ( abs ` ( %s ` u ) ) = ( abs ` ( %s / %s ) ) )' % (Au, GK, WU, PU))
    a2 = ap(w, Au, 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (WU, PU, WU, PU), cu)
    # abs ( ( 1 / u ) ^ Y ) = ( 1 / abs u ) ^ Y
    yz = cu.mem('Y', 'NN0')
    cu.have('( 1 / u )', 'CC', cu.mem('( 1 / u )', 'CC')); cu.atom('( 1 / u )')
    b1 = ap(w, Au, 'absexpd', '( abs ` %s ) = ( ( abs ` ( 1 / u ) ) ^ Y )' % WU, cu)
    cu.have('u', 'CC', uc)
    b2 = w.s([ap(w, Au, 'absdivd', '( abs ` ( 1 / u ) ) = ( ( abs ` 1 ) / ( abs ` u ) )', cu),
              w.s([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % Au)], 'oveq1d', '( %s -> ( ( abs ` 1 ) / ( abs ` u ) ) = ( 1 / ( abs ` u ) ) )' % Au)],
             'eqtrd', '( %s -> ( abs ` ( 1 / u ) ) = ( 1 / ( abs ` u ) ) )' % Au)
    b3 = w.s([b1, w.s([b2], 'oveq1d', '( %s -> ( ( abs ` ( 1 / u ) ) ^ Y ) = ( ( 1 / ( abs ` u ) ) ^ Y ) )' % Au)], 'eqtrd', '( %s -> ( abs ` %s ) = ( ( 1 / ( abs ` u ) ) ^ Y ) )' % (Au, WU))
    rc = w.s([mod, ap(w, Au, 'lerecd', '( ( 1 - R ) <_ ( abs ` u ) <-> ( 1 / ( abs ` u ) ) <_ ( 1 / ( 1 - R ) ) )', cu)], 'mpbid', '( %s -> ( 1 / ( abs ` u ) ) <_ ( 1 / ( 1 - R ) ) )' % Au)
    b4 = ap(w, Au, 'leexp1ad', '( ( 1 / ( abs ` u ) ) ^ Y ) <_ ( ( 1 / ( 1 - R ) ) ^ Y )', cu, facts=[rc])
    wle = w.s([b3, b4], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( ( 1 / ( 1 - R ) ) ^ Y ) )' % (Au, WU))
    # abs PU >_ PL
    pa = w.s([kfu, cug.mem('( u - ( V ` g ) )', 'CC')], 'z5fprodabs', '( %s -> ( abs ` %s ) = prod_ g e. K ( abs ` ( u - ( V ` g ) ) ) )' % (Au, PU))
    sl = w.s([w.s([_cl.lift(w, uc, Aug), vgu], 'jca', '( %s -> ( u e. CC /\\ ( V ` g ) e. CC ) )' % Aug), w.inst('tpsupl')], 'syl',
             '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( u - ( V ` g ) ) ) )' % (Aug, DS('u'), DS('( V ` g )')))
    sl2 = w.s([w.s([w.s([_cl.lift(w, dsu, Aug)], 'oveq1d', '( %s -> ( %s - %s ) = ( R - %s ) )' % (Aug, DS('u'), DS('( V ` g )'), DS('( V ` g )')))], 'fveq2d',
                   '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( R - %s ) ) )' % (Aug, DS('u'), DS('( V ` g )'), DS('( V ` g )'))), sl], 'eqbrtrrd',
              '( %s -> ( abs ` ( R - %s ) ) <_ ( abs ` ( u - ( V ` g ) ) ) )' % (Aug, DS('( V ` g )')))
    cug.have(DS('( V ` g )'), 'RR', cug.mem(DS('( V ` g )'), 'RR')); cug.atom(DS('( V ` g )'))
    pl = w.s([w.s([], 'nfv', 'F/ g %s' % Au), kfu, cug.mem('( abs ` ( R - %s ) )' % DS('( V ` g )'), 'RR'), cug.ge0('( abs ` ( R - %s ) )' % DS('( V ` g )')),
              cug.mem('( abs ` ( u - ( V ` g ) ) )', 'RR'), sl2], 'fprodle', '( %s -> %s <_ prod_ g e. K ( abs ` ( u - ( V ` g ) ) ) )' % (Au, PL))
    pl2 = w.s([pl, pa], 'breqtrrd', '( %s -> %s <_ ( abs ` %s ) )' % (Au, PL, PU))
    # PL e. RR+
    ne_g = w.s([dgu], 'necomd', '( %s -> R =/= %s )' % (Aug, DS('( V ` g )')))
    cug.have('( R - %s )' % DS('( V ` g )'), 'ne0', ap(w, Aug, 'subne0d', '( R - %s ) =/= 0' % DS('( V ` g )'), cug, facts=[ne_g]))
    plr = w.s([kfu, ap(w, Aug, 'absrpcld', '( abs ` ( R - %s ) ) e. RR+' % DS('( V ` g )'), cug)], 'fprodrpcl', '( %s -> %s e. RR+ )' % (Au, PL))
    cu.have(PL, 'RR+', plr); cu.atom(PL)
    cu.have('( abs ` %s )' % WU, 'RR', cu.mem('( abs ` %s )' % WU, 'RR')); cu.atom('( abs ` %s )' % WU)
    cu.have('( abs ` %s )' % PU, 'RR', cu.mem('( abs ` %s )' % PU, 'RR')); cu.atom('( abs ` %s )' % PU)
    X1 = '( ( 1 / ( 1 - R ) ) ^ Y )'
    cu.have(X1, 'RR', cu.mem(X1, 'RR')); cu.atom(X1)
    q = ap(w, Au, 'lediv12ad', '( ( abs ` %s ) / ( abs ` %s ) ) <_ ( %s / %s )' % (WU, PU, X1, PL), cu, facts=[wle, pl2])
    ub = w.s([w.s([a1, a2], 'eqtrd', '( %s -> ( abs ` ( %s ` u ) ) = ( ( abs ` %s ) / ( abs ` %s ) ) )' % (Au, GK, WU, PU)), q], 'eqbrtrd',
             '( %s -> ( abs ` ( %s ` u ) ) <_ %s )' % (Au, GK, MB))
    allub = w.s([ub], 'ralrimiva', '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ %s )' % (A0, FRS, GK, MB))
    # rectintabse
    RB = tsub(stmt('rectintabse'), {'A': AR, 'B': BR, 'F': GK, 'D': FRS, 'E': FRS, 'M': MB})
    rba, rbc = ante_of(RB)
    Ag = '( %s /\\ g e. K )' % A0
    vg0, dg0, _ = node(Ag, 'g', w.s([], 'simpr', '( %s -> g e. K )' % Ag))
    cg0 = Closure(w, Ag, {'R': ('RR', _cl.lift(w, rr, Ag)), '( V ` g )': ('CC', vg0)}); cg0.atom('( V ` g )')
    cg0.have(DS('( V ` g )'), 'RR', cg0.mem(DS('( V ` g )'), 'RR')); cg0.atom(DS('( V ` g )'))
    cg0.have('( R - %s )' % DS('( V ` g )'), 'ne0', ap(w, Ag, 'subne0d', '( R - %s ) =/= 0' % DS('( V ` g )'), cg0, facts=[w.s([dg0], 'necomd', '( %s -> R =/= %s )' % (Ag, DS('( V ` g )')))]))
    plr0 = s([kf, ap(w, Ag, 'absrpcld', '( abs ` ( R - %s ) ) e. RR+' % DS('( V ` g )'), cg0)], 'fprodrpcl', '%s e. RR+' % PL)
    c.have(PL, 'RR+', plr0); c.atom(PL)
    mbr = c.mem(MB, 'RR')
    have = {'( %s e. CC /\\ %s e. CC )' % (AR, BR): d['ab'], body_of(w, geo): geo, '%s e. ( %s -cn-> CC )' % (GK, FRS): gcn,
            '%s C_ %s' % (FRS, FRS): s([w.s([], 'ssid', '%s C_ %s' % (FRS, FRS))], 'a1i', '%s C_ %s' % (FRS, FRS)), '%s e. RR' % MB: mbr, body_of(w, allub): allub}
    ml = s([conj(w, A0, rba, have), w.inst('rectintabse')], 'syl', rbc)
    I = '( %s rectint <. %s , %s >. )' % (GK, AR, BR)
    per = '( ( ( Re ` %s ) - ( Re ` %s ) ) + ( ( Im ` %s ) - ( Im ` %s ) ) )' % (BR, AR, BR, AR)
    c.atom(MB)
    p4 = lin.lineq(w, A0, per, '( 4 x. R )', hyps=[d['ra'], d['rb'], d['ia'], d['ib']], closure=c)
    ml2 = s([ml, s([p4], 'oveq2d', '( ( 2 x. %s ) x. %s ) = ( ( 2 x. %s ) x. ( 4 x. R ) )' % (MB, per, MB))], 'breqtrd', '( abs ` %s ) <_ ( ( 2 x. %s ) x. ( 4 x. R ) )' % (I, MB))
    # abs ( I / TPI ) = abs I / ( 2 pi )
    c.have('_pi', 'RR+', s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '_pi e. RR+'))
    ic = s([d['ab'], s([gcn, s([w.s([], 'ssid', '%s C_ %s' % (FRS, FRS))], 'a1i', '%s C_ %s' % (FRS, FRS))], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GK, FRS, FRS, FRS)),
            w.inst('rectintcle')], 'syl2anc', '%s e. CC' % I)
    c.have(I, 'CC', ic); c.atom(I)
    tic = c.mem('( _i x. _pi )', 'CC')
    c.have(TPI, 'CC', c.mem(TPI, 'CC'))
    ine = s([w.s([], 'ine0', '_i =/= 0')], 'a1i', '_i =/= 0')
    c.have('_i', 'ne0', ine)
    c.have('( _i x. _pi )', 'ne0', ap(w, A0, 'mulne0d', '( _i x. _pi ) =/= 0', c))
    c.have(TPI, 'ne0', ap(w, A0, 'mulne0d', '%s =/= 0' % TPI, c)); c.atom(TPI)
    e1 = ap(w, A0, 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (I, TPI, I, TPI), c)
    t1 = ap(w, A0, 'absmuld', '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI, c)
    t2 = ap(w, A0, 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )', c)
    t3 = s([s([w.s([], 'absi', '( abs ` _i ) = 1')], 'a1i', '( abs ` _i ) = 1'), ap(w, A0, 'absidd', '( abs ` _pi ) = _pi', c)], 'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')
    t4 = s([ap(w, A0, 'absidd', '( abs ` 2 ) = 2', c), s([t2, t3], 'eqtrd', '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. ( 1 x. _pi ) )')
    t5 = mvlib.ringeq(w, A0, '( 2 x. ( 1 x. _pi ) )', '( 2 x. _pi )', c)
    tabs = s([t1, t4, t5], '3eqtrd', '( abs ` %s ) = ( 2 x. _pi )' % TPI)
    e2 = s([e1, s([tabs], 'oveq2d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / ( 2 x. _pi ) )' % (I, TPI, I))], 'eqtrd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( 2 x. _pi ) )' % (I, TPI, I))
    c.have('( abs ` %s )' % I, 'RR', c.mem('( abs ` %s )' % I, 'RR')); c.atom('( abs ` %s )' % I)
    le1 = ap(w, A0, 'lediv1dd', '( ( abs ` %s ) / ( 2 x. _pi ) ) <_ ( ( ( 2 x. %s ) x. ( 4 x. R ) ) / ( 2 x. _pi ) )' % (I, MB), c, facts=[ml2])
    # ( ( 2 MB ) ( 4 R ) ) / ( 2 pi ) = ( ( 4 R ) / pi ) MB
    f1 = s([mvlib.ringeq(w, A0, '( ( 2 x. %s ) x. ( 4 x. R ) )' % MB, '( 2 x. ( %s x. ( 4 x. R ) ) )' % MB, c)], 'oveq1d',
           '( ( ( 2 x. %s ) x. ( 4 x. R ) ) / ( 2 x. _pi ) ) = ( ( 2 x. ( %s x. ( 4 x. R ) ) ) / ( 2 x. _pi ) )' % (MB, MB))
    f2 = ap(w, A0, 'divcan5d', '( ( 2 x. ( %s x. ( 4 x. R ) ) ) / ( 2 x. _pi ) ) = ( ( %s x. ( 4 x. R ) ) / _pi )' % (MB, MB), c)
    f3 = ap(w, A0, 'divassd', '( ( %s x. ( 4 x. R ) ) / _pi ) = ( %s x. ( ( 4 x. R ) / _pi ) )' % (MB, MB), c)
    f4 = ap(w, A0, 'mulcomd', '( %s x. ( ( 4 x. R ) / _pi ) ) = ( ( ( 4 x. R ) / _pi ) x. %s )' % (MB, MB), c)
    fe = s([s([f1, f2, f3], '3eqtrd', '( ( ( 2 x. %s ) x. ( 4 x. R ) ) / ( 2 x. _pi ) ) = ( %s x. ( ( 4 x. R ) / _pi ) )' % (MB, MB)), f4], 'eqtrd',
           '( ( ( 2 x. %s ) x. ( 4 x. R ) ) / ( 2 x. _pi ) ) = ( ( ( 4 x. R ) / _pi ) x. %s )' % (MB, MB))
    fin = s([le1, fe], 'breqtrd', '( ( abs ` %s ) / ( 2 x. _pi ) ) <_ ( ( ( 4 x. R ) / _pi ) x. %s )' % (I, MB))
    w.qed([e2, fin], 'eqbrtrd', S['tpbb'])
    return run(w)


S['tpbic'] = '( %s -> ( ( %s rectint <. %s , %s >. ) / %s ) e. CC )' % (BA, GK, AR, BR, TPI)


def gen_bic():
    w = W('tpbic', 'The Newton coefficient on the square is a complex number (continuity of the integrand on the frame, C1 ~ rectintcle ).')
    A0 = BA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( R e. RR /\\ 0 < R /\\ R < 1 )'); t2 = s([], 'simp2', '( Y e. NN /\\ ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ K C_ ( 0 ..^ N ) )')
    alln = s([], 'simp3', 'A. r e. ( 0 ..^ N ) %s =/= R' % DS('( V ` r )'))
    rr = s([t1], 'simp1d', 'R e. RR'); r0 = s([t1], 'simp2d', '0 < R'); r1 = s([t1], 'simp3d', 'R < 1')
    yn = s([t2], 'simp1d', 'Y e. NN'); nv = s([t2], 'simp2d', '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )'); ks = s([t2], 'simp3d', 'K C_ ( 0 ..^ N )')
    vf = s([nv], 'simprd', 'V : ( 0 ..^ N ) --> CC')
    c = Closure(w, A0, {'R': ('RR', rr), 'Y': ('NN', yn)})
    omr = lin.linarith(w, A0, [r1], '0 < ( 1 - R )', closure=c)
    c.have('( 1 - R )', 'gt0', omr)
    d = sqbase(w, A0, c)
    geo1 = lin.linarith(w, A0, [d['ra'], d['rb'], r0], '( Re ` %s ) <_ ( Re ` %s )' % (AR, BR), closure=c)
    geo2 = lin.linarith(w, A0, [d['ia'], d['ib'], r0], '( Im ` %s ) <_ ( Im ` %s )' % (AR, BR), closure=c)
    geo = s([geo1, geo2], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (AR, BR, AR, BR))
    fru = s([d['ab'], geo, w.inst('crectfru')], 'syl2anc', '%s C_ %s' % (FRS, CRS))
    ra0 = s([omr, d['ra']], 'breqtrrd', '0 < ( Re ` %s )' % AR)
    rh = s([s([d['ab'], ra0], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ 0 < ( Re ` %s ) )' % (AR, BR, AR)), w.inst('ef2rhp')], 'syl',
           '( %s C_ %s /\\ %s C_ %s )' % (CRS, E.HP0, CRS, CN0))
    frc = s([fru, s([rh], 'simprd', '%s C_ %s' % (CRS, CN0))], 'sstrd', '%s C_ %s' % (FRS, CN0))
    frcc = s([frc, s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % FRS)
    # node facts at q e. K: V_q e. CC, DS ( V_q ) =/= R, V_q off the frame
    def node(Kc, qv, qinK):
        qN = w.s([_cl.lift(w, ks, Kc), qinK], 'sseldd', '( %s -> %s e. ( 0 ..^ N ) )' % (Kc, qv))
        vq = w.s([_cl.lift(w, vf, Kc), qN], 'ffvelcdmd', '( %s -> ( V ` %s ) e. CC )' % (Kc, qv))
        idr = w.s([], 'id', '( r = %s -> r = %s )' % (qv, qv))
        cg, nw = w.wcongr('%s =/= R' % DS('( V ` r )'), {'r': qv}, 'r = %s' % qv, {'r': idr})
        dq = w.s([qN, _cl.lift(w, alln, Kc), w.s([cg], 'rspcv', '( %s e. ( 0 ..^ N ) -> ( A. r e. ( 0 ..^ N ) %s =/= R -> %s ) )' % (qv, DS('( V ` r )'), nw))],
                 'sylc', '( %s -> %s )' % (Kc, nw))
        sv = w.s([w.s([w.s([_cl.lift(w, rr, Kc), _cl.lift(w, r0, Kc)], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % Kc), w.s([vq, dq], 'jca', '( %s -> ( ( V ` %s ) e. CC /\\ %s ) )' % (Kc, qv, nw))],
                      'jca', '( %s -> ( ( R e. RR /\\ 0 < R ) /\\ ( ( V ` %s ) e. CC /\\ %s ) ) )' % (Kc, qv, nw)), w.inst('tpsqv')], 'syl',
                 '( %s -> ( -. ( V ` %s ) e. %s /\\ ( ( V ` %s ) e. %s -> %s ) /\\ ( %s <-> %s < R ) ) )' % (Kc, qv, FRS, qv, CRS, INSR('( V ` %s )' % qv), INSR('( V ` %s )' % qv), DS('( V ` %s )' % qv)))
        off = w.s([sv], 'simp1d', '( %s -> -. ( V ` %s ) e. %s )' % (Kc, qv, FRS))
        return vq, dq, off
    # the frame avoids every node of K
    Ax = '( %s /\\ x e. %s )' % (A0, FRS)
    Axq = '( %s /\\ q e. K )' % Ax
    _, _, offq = node(Axq, 'q', w.s([], 'simpr', '( %s -> q e. K )' % Axq))
    neq = w.s([_cl.lift(w, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, FRS)), Axq), offq, w.inst('nelne2')], 'syl2anc', '( %s -> x =/= ( V ` q ) )' % Axq)
    avoid = w.s([w.s([neq], 'ralrimiva', '( %s -> A. q e. K x =/= ( V ` q ) )' % Ax)], 'ralrimiva', '( %s -> A. x e. %s A. q e. K x =/= ( V ` q ) )' % (A0, FRS))
    # continuity of GK
    GC = tsub(stmt('tpgcn'), {'E': FRS, 'C': '1'})
    ga, gc = ante_of(GC)
    have = {'Y e. NN': yn, '1 e. CC': s([], '1cnd', '1 e. CC'), '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )': nv, 'K C_ ( 0 ..^ N )': ks,
            '%s C_ %s' % (FRS, CN0): frc, body_of(w, avoid): avoid}
    g1 = s([conj(w, A0, ga, have), w.inst('tpgcn')], 'syl', gc)
    Ad = '( %s /\\ d e. %s )' % (A0, FRS)
    dfr = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, FRS))
    cd = Closure(w, Ad, {})
    fyh = w.s([_cl.lift(w, yn, Ad), w.inst('tpfh')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (Ad, FY, CN0, CN0, FY))
    fyf = w.s([w.s([fyh], 'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Ad, FY, CN0)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Ad, FY, CN0))
    fyv = w.s([fyf, w.s([_cl.lift(w, frc, Ad), dfr], 'sseldd', '( %s -> d e. %s )' % (Ad, CN0))], 'ffvelcdmd', '( %s -> ( %s ` d ) e. CC )' % (Ad, FY))
    cd.have('( %s ` d )' % FY, 'CC', fyv); cd.atom('( %s ` d )' % FY)
    Adg = '( %s /\\ g e. K )' % Ad
    vg, _, offg = node(Adg, 'g', w.s([], 'simpr', '( %s -> g e. K )' % Adg))
    dc = w.s([_cl.lift(w, frcc, Ad), dfr], 'sseldd', '( %s -> d e. CC )' % Ad)
    cdg = Closure(w, Adg, {'d': ('CC', _cl.lift(w, dc, Adg)), '( V ` g )': ('CC', vg)}); cdg.atom('( V ` g )')
    dne = w.s([_cl.lift(w, dfr, Adg), offg, w.inst('nelne2')], 'syl2anc', '( %s -> d =/= ( V ` g ) )' % Adg)
    cdg.have('( d - ( V ` g ) )', 'ne0', ap(w, Adg, 'subne0d', '( d - ( V ` g ) ) =/= 0', cdg, facts=[dne]))
    kf = s([s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin'), ks, w.inst('ssfi')], 'syl2anc', 'K e. Fin')
    pdc = w.s([_cl.lift(w, kf, Ad), cdg.mem('( d - ( V ` g ) )', 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Ad, PK))
    pdn = w.s([_cl.lift(w, kf, Ad), cdg.mem('( d - ( V ` g ) )', 'CC'), cdg.ne0('( d - ( V ` g ) )')], 'fprodn0', '( %s -> %s =/= 0 )' % (Ad, PK))
    cd.have(PK, 'CC', pdc); cd.have(PK, 'ne0', pdn); cd.atom(PK)
    Q1 = '( ( %s ` d ) / %s )' % (FY, PK)
    meq = w.s([ap(w, Ad, 'mullidd', '( 1 x. %s ) = %s' % (Q1, Q1), cd)], 'mpteq2dva', '( %s -> ( d e. %s |-> ( 1 x. %s ) ) = %s )' % (A0, FRS, Q1, GK))
    gcn = s([meq, g1], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (GK, FRS))
    I = '( %s rectint <. %s , %s >. )' % (GK, AR, BR)
    ic = s([d['ab'], s([gcn, s([w.s([], 'ssid', '%s C_ %s' % (FRS, FRS))], 'a1i', '%s C_ %s' % (FRS, FRS))], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GK, FRS, FRS, FRS)),
            w.inst('rectintcle')], 'syl2anc', '%s e. CC' % I)
    c.have(I, 'CC', ic); c.atom(I)
    c.have('_i', 'ne0', s([w.s([], 'ine0', '_i =/= 0')], 'a1i', '_i =/= 0'))
    c.have('_pi', 'RR+', s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '_pi e. RR+'))
    c.have('( _i x. _pi )', 'ne0', ap(w, A0, 'mulne0d', '( _i x. _pi ) =/= 0', c))
    c.have(TPI, 'ne0', ap(w, A0, 'mulne0d', '%s =/= 0' % TPI, c))
    w.qed([ic, c.mem(TPI, 'CC'), c.ne0(TPI)], 'divcld', S['tpbic'])
    return run(w)


if __name__ == '__main__':
    gen_bb()
    gen_bic()
