"""Sortie ZC1: box counts for zeta (zc1one, Lean zeroCountBox_one_le) and the principal character (zc1tle,
zeroCountBox_trivChar_le), and the sum over all characters (zc1sum, sum_zeroCountBox_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
from c9_b import decode
from c10_f import crfacts, clo
import cl as _cl
import zc1_c, zc1_d, zc1_e, zc1_i, zc1_j, zc1_k, zc1_l, zc1_m, zc1_q, zc1_s
from zc1_c import u1base, U1
from zc1_q import box_hp
import lin
lin.FASTPATH = True

H = '( 1 / 2 )'
C64 = '; ; ; 6 4 0 0'
ZF1 = ZF(E1, H, 'T')
S['zc1one'] = '( ( T e. RR /\\ 1 <_ T ) -> %s <_ ( %s x. ( T x. ( log ` ( T + 2 ) ) ) ) )' % (ZC(E1, H, 'T'), C64)


def gen_zc1one():
    w = W('zc1one', 'Box zero count for ` E1 = ( s - 1 ) zeta ( s ) ` (Lean ` zeroCountBox_one_le ` , ` 1120 ` there): at most ` 6400 T log ( T + 2 ) ` for ` T >_ 1 ` ( ~ zc1ezt , ~ etazc , ~ boxcnt ).')
    A0 = ante_of(S['zc1one'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'simpl', 'T e. RR'); t1 = s([], 'simpr', '1 <_ T')
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    EZ = tsub(S['ezf'], {'N': '1', 'X': U1, 'A': H})
    eza, ezc = ante_of(EZ)
    hr = numst(w, A0, H, 'RR')
    ez = s([s([nx1, s([s([hr, numst(w, A0, H, 'gt0'), lin8(w, A0, [], '%s <_ 1' % H, {})], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (H, H, H)), tr], 'jca', top_and(eza)[1])], 'jca', eza),
            w.inst('ezf')], 'syl', ezc)
    gfin = s([ez, w.inst('simpl')], 'syl', '%s e. Fin' % ZF1)
    alnn = s([ez, w.inst('simpr')], 'syl', 'A. q e. %s ( %s holord q ) e. NN' % (ZF1, E1))
    Aq = '( %s /\\ q e. %s )' % (A0, ZF1)
    sq = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    Lq = lambda st: lift(w, st, Aq)
    BOXH = BOX(H, 'T')
    subr = w.s([w.s([], 'neeq1', '( r = q -> ( r =/= 1 <-> q =/= 1 ) )'), w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (E1, E1))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (E1, E1))],
               'anbi12d', '( r = q -> ( ( r =/= 1 /\\ ( %s ` r ) = 0 ) <-> ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (E1, E1))
    elq = w.s([subr], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (ZF1, BOXH, E1))
    qq = sq([sq([], 'simpr', 'q e. %s' % ZF1), elq], 'sylib', '( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (BOXH, E1))
    qb = sq([qq, w.inst('simpl')], 'syl', 'q e. %s' % BOXH); qn1 = sq([qq, w.inst('simprl')], 'syl', 'q =/= 1'); eq0 = sq([qq, w.inst('simprr')], 'syl', '( %s ` q ) = 0' % E1)
    BA, BB = '( %s + ( _i x. -u T ) )' % H, '( 1 + ( _i x. T ) )'
    bac, rbA, ibA = crfacts(w, Aq, H, '-u T', numst(w, Aq, H, 'RR'), sq([Lq(tr)], 'renegcld', '-u T e. RR'))
    bbc, rbB, ibB = crfacts(w, Aq, '1', 'T', numst(w, Aq, '1', 'RR'), Lq(tr))
    dq = decode(w, Aq, qb, bac, bbc, BA, BB, BOXH, U='q')
    qc = dq[0]
    lvq = {'( Re ` q )': sq([qc], 'recld', '( Re ` q ) e. RR'), '( Im ` q )': sq([qc], 'imcld', '( Im ` q ) e. RR'), 'T': Lq(tr)}
    for e, st in (('( Re ` %s )' % BA, bac), ('( Im ` %s )' % BA, bac), ('( Re ` %s )' % BB, bbc), ('( Im ` %s )' % BB, bbc)):
        lvq[e] = sq([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hyq = [rbA, ibA, rbB, ibB] + dq[1:]
    rlo = lin8(w, Aq, hyq, '( 1 / 2 ) <_ ( Re ` q )', lvq); rhi = lin8(w, Aq, hyq, '( Re ` q ) <_ 1', lvq)
    iq = sq([sq([lin8(w, Aq, hyq, '-u T <_ ( Im ` q )', lvq), lin8(w, Aq, hyq, '( Im ` q ) <_ T', lvq)], 'jca', '( -u T <_ ( Im ` q ) /\\ ( Im ` q ) <_ T )'),
             sq([lvq['( Im ` q )'], Lq(tr)], 'absled', '( ( abs ` ( Im ` q ) ) <_ T <-> ( -u T <_ ( Im ` q ) /\\ ( Im ` q ) <_ T ) )')], 'mpbird', '( abs ` ( Im ` q ) ) <_ T')
    qhp = sq([sq([qc, lin8(w, Aq, [rlo], '0 < ( Re ` q )', lvq)], 'jca', '( q e. CC /\\ 0 < ( Re ` q ) )'),
              sq([sq([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbird', 'q e. %s' % HP0)
    EZT = tsub(S['zc1ezt'], {'P': 'q'})
    eta_, etc_ = ante_of(EZT)
    ezt = sq([sq([qhp, qn1], 'jca', eta_), w.inst('zc1ezt')], 'syl', etc_)
    ole = sq([ezt, w.inst('simpl')], 'syl', top_and(etc_)[0])
    eta0 = sq([eq0, sq([ezt, w.inst('simpr')], 'syl', top_and(etc_)[1])], 'mpd', '( %s ` q ) = 0' % ETA)
    on0 = sq([qhp, w.inst('etaord')], 'syl', '( %s holord q ) e. NN0' % ETA)
    e1n = w.s([alnn], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Aq, E1))
    fl = s([gfin, sq([e1n], 'nnred', '( %s holord q ) e. RR' % E1), sq([on0], 'nn0red', '( %s holord q ) e. RR' % ETA), ole], 'fsumle', '%s <_ %s' % (MASS(ZF1, E1), MASS(ZF1, ETA)))
    PH = A0
    BH = [tsub(x, {'ph': PH, 'G': ZF1, 'W': HO(ETA), 'A': '1', 'K': '; ; 8 0 0'}) for x in zc1_l.BXH]
    b2 = sq([sq([on0], 'nn0red', '( %s holord q ) e. RR' % ETA), sq([on0], 'nn0ge0d', '0 <_ ( %s holord q )' % ETA)], 'jca', ante_of(BH[1])[1])
    b3 = sq([qc, sq([rlo, rhi], 'jca', '( ( 1 / 2 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )'), iq], '3jca', ante_of(BH[2])[1])
    b4 = s([s([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )'), s([numst(w, A0, '1', 'RR'), lin8(w, A0, [], '1 <_ 1', {})], 'jca', '( 1 e. RR /\\ 1 <_ 1 )'),
            s([numst(w, A0, '; ; 8 0 0', 'RR'), numst(w, A0, '; ; 8 0 0', 'ge0')], 'jca', '( ; ; 8 0 0 e. RR /\\ 0 <_ ; ; 8 0 0 )')], '3jca', ante_of(BH[3])[1])
    At = '( %s /\\ t e. RR )' % A0
    st_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (At, f))
    ZE_t = ZS(ETA, 't')
    SUB = tsub(zc1_l.SUBT('t'), {'G': ZF1})
    Atq = '( %s /\\ q e. %s )' % (At, SUB)
    stq = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Atq, f))
    SQt = SQ(CT('t'), R138)
    esb = w.s([w.s([], 'eleq1', '( p = q -> ( p e. %s <-> q e. %s ) )' % (SQt, SQt))], 'elrab', '( q e. %s <-> ( q e. %s /\\ q e. %s ) )' % (SUB, ZF1, SQt))
    qs2 = stq([stq([], 'simpr', 'q e. %s' % SUB), esb], 'sylib', '( q e. %s /\\ q e. %s )' % (ZF1, SQt))
    qz = stq([qs2, w.inst('simpl')], 'syl', 'q e. %s' % ZF1); qsq = stq([qs2, w.inst('simpr')], 'syl', 'q e. %s' % SQt)
    toAq = stq([stq([], 'simpll', A0), qz], 'jca', Aq)
    e0t = stq([toAq, eta0], 'syl', '( %s ` q ) = 0' % ETA)
    subl = w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (ETA, ETA))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (ETA, ETA))
    qze = stq([subl, qsq, e0t], 'elrabd', 'q e. %s' % ZE_t)
    ssb = st_([w.s([qze], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (At, SUB, ZE_t))], 'ssrdv', '%s C_ %s' % (SUB, ZE_t))
    LZ = tsub(S['etazc'], {'T': 't'})
    lza, lzc = ante_of(LZ)
    lz = st_([st_([], 'simpr', 't e. RR'), w.inst('etazc')], 'syl', lzc)
    zlf = st_([lz, w.inst('simp1')], 'syl', top_and(lzc)[0]); zln = st_([lz, w.inst('simp2')], 'syl', top_and(lzc)[1]); zlm = st_([lz, w.inst('simp3')], 'syl', top_and(lzc)[2])
    Atz = '( %s /\\ q e. %s )' % (At, ZE_t)
    zqn = w.s([zln], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Atz, ETA))
    le = st_([zlf, w.s([zqn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Atz, ETA)), w.s([w.s([zqn], 'nnnn0d', '( %s -> ( %s holord q ) e. NN0 )' % (Atz, ETA))], 'nn0ge0d', '( %s -> 0 <_ ( %s holord q ) )' % (Atz, ETA)), ssb],
             'fsumless', '%s <_ %s' % (MASS(SUB, ETA), MASS(ZE_t, ETA)))
    Rt = ante_of(BH[4])[1].split(' <_ ', 1)[1]
    msr = st_([st_([lift(w, gfin, At), w.s([w.s([], 'ssrab2', '%s C_ %s' % (SUB, ZF1))], 'a1i', '( %s -> %s C_ %s )' % (At, SUB, ZF1))], 'ssfid', '%s e. Fin' % SUB),
               w.s([w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (Atq, A0)), qz], 'jca', '( %s -> %s )' % (Atq, Aq)), b2], 'syl', '( %s -> ( ( %s holord q ) e. RR /\\ 0 <_ ( %s holord q ) ) )' % (Atq, ETA, ETA)),
                    w.inst('simpl')], 'syl', '( %s -> ( %s holord q ) e. RR )' % (Atq, ETA))], 'fsumrecl', '%s e. RR' % MASS(SUB, ETA))
    mlr = st_([zlf, w.s([zqn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Atz, ETA))], 'fsumrecl', '%s e. RR' % MASS(ZE_t, ETA))
    AT2t = '( ( abs ` t ) + 2 )'
    atc = st_([st_([], 'simpr', 't e. RR')], 'recnd', 't e. CC')
    at2r = st_([st_([atc], 'abscld', '( abs ` t ) e. RR'), numst(w, At, '2', 'RR')], 'readdcld', '%s e. RR' % AT2t)
    m1 = st_([st_([at2r], 'recnd', '%s e. CC' % AT2t)], 'mullidd', '( 1 x. %s ) = %s' % (AT2t, AT2t))
    zlm2 = st_([zlm, st_([st_([st_([m1], 'fveq2d', '( log ` ( 1 x. %s ) ) = ( log ` %s )' % (AT2t, AT2t))], 'oveq2d',
                             '( ; ; 8 0 0 x. ( log ` ( 1 x. %s ) ) ) = ( ; ; 8 0 0 x. ( log ` %s ) )' % (AT2t, AT2t))], 'eqcomd',
                        '( ; ; 8 0 0 x. ( log ` %s ) ) = ( ; ; 8 0 0 x. ( log ` ( 1 x. %s ) ) )' % (AT2t, AT2t))], 'breqtrd', '%s <_ %s' % (MASS(ZE_t, ETA), Rt))
    at2p = st_([at2r, lin8(w, At, [st_([atc], 'absge0d', '0 <_ ( abs ` t )')], '0 < %s' % AT2t, {'( abs ` t )': st_([atc], 'abscld', '( abs ` t ) e. RR')})], 'elrpd', '%s e. RR+' % AT2t)
    RR_ = st_([numst(w, At, '; ; 8 0 0', 'RR'), st_([st_([numst(w, At, '1', 'RR+'), at2p], 'rpmulcld', '( 1 x. %s ) e. RR+' % AT2t)], 'relogcld', '( log ` ( 1 x. %s ) ) e. RR' % AT2t)],
              'remulcld', '%s e. RR' % Rt)
    b5 = st_([msr, mlr, RR_, le, zlm2], 'letrd', '%s <_ %s' % (MASS(SUB, ETA), Rt))
    BC = tsub(S['boxcnt'], {'ph': PH, 'G': ZF1, 'W': HO(ETA), 'A': '1', 'K': '; ; 8 0 0'})
    bc = w.s([gfin, b2, b3, b4, b5], 'boxcnt', BC)
    L_ = '( log ` ( T + 2 ) )'
    T2 = '( T + 2 )'
    t2p = s([s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % T2), lin8(w, A0, [t1], '0 < %s' % T2, {'T': tr})], 'elrpd', '%s e. RR+' % T2)
    m2 = s([s([t2p], 'rpcnd', '%s e. CC' % T2)], 'mullidd', '( 1 x. %s ) = %s' % (T2, T2))
    bcr = '( ( 4 x. T ) x. %s )' % tsub(zc1_l.QB, {'K': '; ; 8 0 0', 'A': '1'})
    bc2 = s([bc, s([s([s([s([m2], 'fveq2d', '( log ` ( 1 x. %s ) ) = %s' % (T2, L_))], 'oveq2d', '( 2 x. ( log ` ( 1 x. %s ) ) ) = ( 2 x. %s )' % (T2, L_))], 'oveq2d',
                       '( ; ; 8 0 0 x. ( 2 x. ( log ` ( 1 x. %s ) ) ) ) = ( ; ; 8 0 0 x. ( 2 x. %s ) )' % (T2, L_))], 'oveq2d',
                  '%s = ( ( 4 x. T ) x. ( ; ; 8 0 0 x. ( 2 x. %s ) ) )' % (bcr, L_))], 'breqtrd', '%s <_ ( ( 4 x. T ) x. ( ; ; 8 0 0 x. ( 2 x. %s ) ) )' % (MASS(ZF1, ETA), L_))
    ms1 = s([gfin, sq([e1n], 'nnred', '( %s holord q ) e. RR' % E1)], 'fsumrecl', '%s e. RR' % MASS(ZF1, E1))
    ms2 = s([gfin, sq([on0], 'nn0red', '( %s holord q ) e. RR' % ETA)], 'fsumrecl', '%s e. RR' % MASS(ZF1, ETA))
    lv = {'T': tr, L_: s([t2p], 'relogcld', '%s e. RR' % L_), MASS(ZF1, E1): ms1, MASS(ZF1, ETA): ms2}
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    fin = lin.linarith(w, A0, [fl, bc2], '%s <_ ( %s x. ( T x. %s ) )' % (MASS(ZF1, E1), C64, L_), closure=c, products=True)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['zc1one']))
    return run8(w)


PRx = '( %s /\\ X = ( 0g ` ( DChr ` N ) ) )' % NX
S['zc1tle'] = '( ( %s /\\ ( T e. RR /\\ 1 <_ T ) ) -> %s <_ ( %s x. ( T x. ( log ` ( T + 2 ) ) ) ) )' % (PRx, ZC(E, H, 'T'), C64)
EX = '( N DChrLF x )'
S['zc1sum'] = ('( ( N e. NN /\\ ( T e. RR /\\ 1 <_ T ) ) -> sum_ x e. ( Base ` ( DChr ` N ) ) %s <_ ( %s x. ( ( T x. N ) x. ( log ` ( N x. ( T + 2 ) ) ) ) ) )') % (ZC(EX, H, 'T'), C64)


def gen_zc1tle():
    w = W('zc1tle', 'Box zero count for the principal character mod ` N ` (Lean ` zeroCountBox_trivChar_le ` ): at most ` 6400 T log ( T + 2 ) ` ( ~ zc1teq , ~ zc1one ).')
    A0 = ante_of(S['zc1tle'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pr = s([], 'simpl', PRx); tt = s([], 'simpr', '( T e. RR /\\ 1 <_ T )')
    tr = s([tt, w.inst('simpl')], 'syl', 'T e. RR')
    TE = tsub(S['zc1teq'], {'A': H})
    tea, tec = ante_of(TE)
    te = s([s([pr, s([s([numst(w, A0, H, 'RR'), numst(w, A0, H, 'gt0'), lin8(w, A0, [], '%s <_ 1' % H, {})], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (H, H, H)), tr], 'jca', top_and(tea)[1])],
               'jca', tea), w.inst('zc1teq')], 'syl', tec)
    one = s([tt, w.inst('zc1one')], 'syl', ante_of(S['zc1one'])[1])
    w.lines.append('qed:%s:idi |- %s' % (s([te, one], 'eqbrtrd', ante_of(S['zc1tle'])[1]), S['zc1tle']))
    return run8(w)


def gen_zc1sum():
    w = W('zc1sum', 'The frozen Z4b interface (Lean ` sum_zeroCountBox_le ` , ` C1 = 1120 ` there): the box counts of all characters mod ` N ` sum to at most ` 6400 T N log ( N ( T + 2 ) ) ` for ` T >_ 1 ` ( ~ zc1cnt , ~ zc1tle , ~ dchrhash ).')
    A0 = ante_of(S['zc1sum'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nn = s([], 'simpl', 'N e. NN'); tt = s([], 'simpr', '( T e. RR /\\ 1 <_ T )')
    tr = s([tt, w.inst('simpl')], 'syl', 'T e. RR'); t1 = s([tt, w.inst('simpr')], 'syl', '1 <_ T')
    nr = s([nn], 'nnred', 'N e. RR'); n1 = s([nn], 'nnge1d', '1 <_ N')
    D = '( Base ` ( DChr ` N ) )'
    g = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); b = w.s([], 'eqid', '%s = %s' % (D, D))
    df = s([nn, w.s([g, b], 'dchrfi', '( N e. NN -> %s e. Fin )' % D)], 'syl', '%s e. Fin' % D) if False else w.s([nn, w.s([g, b], 'dchrfi', '( N e. NN -> %s e. Fin )' % D)], 'syl', '( %s -> %s e. Fin )' % (A0, D))
    dh = w.s([nn, w.s([g, b], 'dchrhash', '( N e. NN -> ( # ` %s ) = ( phi ` N ) )' % D)], 'syl', '( %s -> ( # ` %s ) = ( phi ` N ) )' % (A0, D))
    L_ = '( log ` ( N x. ( T + 2 ) ) )'
    CC_ = '( %s x. ( T x. %s ) )' % (C64, L_)
    lv0 = {'N': nr, 'T': tr}
    c0 = _cl.Closure(w, A0, lv0)
    for k_ in lv0:
        c0.atom(k_)
    nt = s([nr, tr, lin8(w, A0, [n1], '0 <_ N', lv0), lin8(w, A0, [t1], '0 <_ T', lv0)], 'mulge0d', '0 <_ ( N x. T )')
    xp = s([c0.mem('( N x. ( T + 2 ) )', 'RR'), lin.linarith(w, A0, [n1, t1, nt], '0 < ( N x. ( T + 2 ) )', closure=c0, products=True)], 'elrpd', '( N x. ( T + 2 ) ) e. RR+')
    lr = s([xp], 'relogcld', '%s e. RR' % L_)
    ccr = s([numst(w, A0, C64, 'RR'), s([tr, lr], 'remulcld', '( T x. %s ) e. RR' % L_)], 'remulcld', '%s e. RR' % CC_)
    Ax = '( %s /\\ x e. %s )' % (A0, D)
    sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ax, f))
    Lx = lambda st: lift(w, st, Ax)
    xb = sx([], 'simpr', 'x e. %s' % D)
    NXx = '( N e. NN /\\ x e. %s )' % D
    nxx = sx([Lx(nn), xb], 'jca', NXx)
    ZX = ZC(EX, H, 'T')
    # the count of each character is at most CC_
    U0 = '( 0g ` ( DChr ` N ) )'
    Ap = '( %s /\\ x = %s )' % (Ax, U0)
    Anp = '( %s /\\ x =/= %s )' % (Ax, U0)
    TL = tsub(S['zc1tle'], {'X': 'x'})
    tla, tlc = ante_of(TL)
    tl = w.s([w.s([w.s([lift(w, nxx, Ap), w.s([], 'simpr', '( %s -> x = %s )' % (Ap, U0))], 'jca', '( %s -> %s )' % (Ap, top_and(tla)[0])), lift(w, tt, Ap)], 'jca', '( %s -> %s )' % (Ap, tla)),
              w.inst('zc1tle')], 'syl', '( %s -> %s )' % (Ap, tlc))
    T2 = '( T + 2 )'
    t2p = s([s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % T2), lin8(w, A0, [t1], '0 < %s' % T2, {'T': tr})], 'elrpd', '%s e. RR+' % T2)
    lle = s([lin.linarith(w, A0, [n1, t1, nt], '%s <_ ( N x. ( T + 2 ) )' % T2, closure=c0, products=True), s([t2p, xp], 'logled', '( %s <_ ( N x. ( T + 2 ) ) <-> ( log ` %s ) <_ %s )' % (T2, T2, L_))],
            'mpbid', '( log ` %s ) <_ %s' % (T2, L_))
    l2r = s([t2p], 'relogcld', '( log ` %s ) e. RR' % T2)
    lv = {'T': tr, '( log ` %s )' % T2: l2r, L_: lr}
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    hint = s([tr, s([lr, l2r], 'resubcld', '( %s - ( log ` %s ) ) e. RR' % (L_, T2)), lin8(w, A0, [t1], '0 <_ T', {'T': tr}), lin8(w, A0, [lle], '0 <_ ( %s - ( log ` %s ) )' % (L_, T2), lv)], 'mulge0d',
             '0 <_ ( T x. ( %s - ( log ` %s ) ) )' % (L_, T2))
    mono = lin.linarith(w, A0, [hint], '( %s x. ( T x. ( log ` %s ) ) ) <_ %s' % (C64, T2, CC_), closure=c, products=True)
    zxr = None
    pcase = w.s([tl, lift(w, mono, Ap)], 'x', 'x') if False else None
    # ZX e. RR on Ax
    EZ = tsub(S['ezf'], {'X': 'x', 'A': H})
    eza, ezc = ante_of(EZ)
    ez = sx([sx([nxx, sx([sx([numst(w, Ax, H, 'RR'), numst(w, Ax, H, 'gt0'), lin8(w, Ax, [], '%s <_ 1' % H, {})], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (H, H, H)), Lx(tr)], 'jca', top_and(eza)[1])], 'jca', eza),
             w.inst('ezf')], 'syl', ezc)
    ZFX = ZF(EX, H, 'T')
    Axq = '( %s /\\ q e. %s )' % (Ax, ZFX)
    zxn = w.s([sx([ez, w.inst('simpr')], 'syl', 'A. q e. %s ( %s holord q ) e. NN' % (ZFX, EX))], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Axq, EX))
    zxr = sx([sx([ez, w.inst('simpl')], 'syl', '%s e. Fin' % ZFX), w.s([zxn], 'nnred', '( %s -> ( %s holord q ) e. RR )' % (Axq, EX))], 'fsumrecl', '%s e. RR' % ZX)
    pc = w.s([lift(w, zxr, Ap), w.s([lift(w, lift(w, s([numst(w, A0, C64, 'RR'), s([tr, l2r], 'remulcld', '( T x. ( log ` %s ) ) e. RR' % T2)], 'remulcld', '( %s x. ( T x. ( log ` %s ) ) ) e. RR' % (C64, T2)), Ax), Ap)], 'x', 'x') if False else
              lift(w, s([numst(w, A0, C64, 'RR'), s([tr, l2r], 'remulcld', '( T x. ( log ` %s ) ) e. RR' % T2)], 'remulcld', '( %s x. ( T x. ( log ` %s ) ) ) e. RR' % (C64, T2)), Ap),
              lift(w, ccr, Ap), tl, lift(w, mono, Ap)], 'letrd', '( %s -> %s <_ %s )' % (Ap, ZX, CC_))
    CN = tsub(S['zc1cnt'], {'X': 'x'})
    cna, cnc = ante_of(CN)
    chix = w.s([lift(w, nxx, Anp), w.s([], 'simpr', '( %s -> x =/= %s )' % (Anp, U0))], 'jca', '( %s -> %s )' % (Anp, top_and(cna)[0]))
    nc = w.s([w.s([chix, lift(w, tt, Anp)], 'jca', '( %s -> %s )' % (Anp, cna)), w.inst('zc1cnt')], 'syl', '( %s -> %s )' % (Anp, cnc))
    each = sx([pc, nc, w.s([], 'exmidne', '( x = %s \\/ x =/= %s )' % (U0, U0)) and sx([w.s([], 'exmidne', '( x = %s \\/ x =/= %s )' % (U0, U0))], 'a1i', '( x = %s \\/ x =/= %s )' % (U0, U0))], 'mpjaodan', '%s <_ %s' % (ZX, CC_))
    fl = s([df, zxr, lift(w, ccr, Ax), each], 'fsumle', 'sum_ x e. %s %s <_ sum_ x e. %s %s' % (D, ZX, D, CC_))
    fc = s([s([df, s([ccr], 'recnd', '%s e. CC' % CC_)], 'jca', '( %s e. Fin /\\ %s e. CC )' % (D, CC_)), w.inst('fsumconst')], 'syl', 'sum_ x e. %s %s = ( ( # ` %s ) x. %s )' % (D, CC_, D, CC_))
    ph = s([nn, w.inst('z5phile')], 'syl', '( phi ` N ) <_ N')
    HD = '( # ` %s )' % D
    hdr = s([dh, s([s([nn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nnred', '( phi ` N ) e. RR')], 'eqeltrrd' if False else 'x', 'x') if False else \
        s([s([dh], 'eqcomd', '( phi ` N ) = %s' % HD), s([s([nn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nnred', '( phi ` N ) e. RR')], 'eqeltrrd', '%s e. RR' % HD)
    hle = s([dh, ph], 'eqbrtrd', '%s <_ N' % HD)
    cc0 = s([numst(w, A0, C64, 'RR'), s([tr, lr], 'remulcld', '( T x. %s ) e. RR' % L_), numst(w, A0, C64, 'ge0'),
             s([tr, lr, lin8(w, A0, [t1], '0 <_ T', {'T': tr}), s([c0.mem('( N x. ( T + 2 ) )', 'RR'), lin.linarith(w, A0, [n1, t1, nt], '1 <_ ( N x. ( T + 2 ) )', closure=c0, products=True), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L_)],
               'mulge0d', '0 <_ ( T x. %s )' % L_)], 'mulge0d', '0 <_ %s' % CC_)
    m = s([hdr, nr, ccr, cc0, hle], 'lemul1ad', '( %s x. %s ) <_ ( N x. %s )' % (HD, CC_, CC_))
    SX = 'sum_ x e. %s %s' % (D, ZX)
    sxr = s([df, zxr], 'fsumrecl', '%s e. RR' % SX)
    lvf = {SX: sxr, 'N': nr, 'T': tr, L_: lr, '( ( # ` %s ) x. %s )' % (D, CC_): s([hdr, ccr], 'remulcld', '( %s x. %s ) e. RR' % (HD, CC_))}
    cf = _cl.Closure(w, A0, lvf)
    for k_ in lvf:
        cf.atom(k_)
    t1_ = s([fl, fc], 'breqtrd', '%s <_ ( %s x. %s )' % (SX, HD, CC_))
    fin = lin.linarith(w, A0, [t1_, m], '%s <_ ( %s x. ( ( T x. N ) x. %s ) )' % (SX, C64, L_), closure=cf, products=True)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['zc1sum']))
    return run8(w)


if __name__ == '__main__':
    gen_zc1one()
    gen_zc1tle()
    gen_zc1sum()
