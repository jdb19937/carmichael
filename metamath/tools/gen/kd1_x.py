"""Sortie KD1: the representation with its Cauchy remainder at s0 = ( 1 + E ) + i T (kdrep)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_rep():
    w = W('kdrep', 'Lean ` KDerivDetect ` steps 1 with the Cauchy remainder, as consumed by ` norm_LSeries_ge_of_turan ` : at ` s0 = ( 1 + E ) + i T ` , ` 0 < E <_ 1 / 20 ` , ` abs ( sum_ZD m / ( s0 - q ) ^ ( K + 1 ) + LSeries ( log ^ K chi Lam ) ( s0 ) / K ! ) <_ 2 3 ^ K 17500000 log ( N ( abs T + 2 ) ) ` ( ` kdrem ` , ` kdrepg ` , ` kdrepb ` , ` kdlsalg ` ).')
    A0 = KDH
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    tek = s([], 'simpr', '( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ K e. NN0 )' % R120)
    tr = s([tek], 'simp1d', 'T e. RR'); ee = s([tek], 'simp2d', '( E e. RR+ /\\ E <_ %s )' % R120); kk = s([tek], 'simp3d', 'K e. NN0')
    ep = s([ee], 'simpld', 'E e. RR+'); er = s([ep], 'rpred', 'E e. RR'); e20 = s([ee], 'simprd', 'E <_ %s' % R120)
    nx = s([chi], 'simpld', NXH)
    SS = S0()
    c = Closure(w, A0, {'E': ('RR', er), 'T': ('RR', tr)})
    e1 = linarith(w, A0, [e20], 'E <_ 1', closure=c)
    oe = c.mem('( 1 + E )', 'RR')
    s0c = s([s([oe], 'recnd', '( 1 + E ) e. CC'), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SS)
    rs0 = s([oe, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + E )' % SS)
    # S1 = ( -1 ) ^ K LSK
    B0 = '( %s /\\ ( ( E e. RR+ /\\ E <_ 1 ) /\\ ( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ K e. NN0 ) ) )' % (NXH, SS, SS)
    b0 = s([nx, s([s([ep, e1], 'jca', '( E e. RR+ /\\ E <_ 1 )'), s([s0c, rs0, kk], '3jca', '( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ K e. NN0 )' % (SS, SS))], 'jca',
                   '( ( E e. RR+ /\\ E <_ 1 ) /\\ ( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ K e. NN0 ) )' % (SS, SS))], 'jca', B0)
    LSA = tsub(S['kdlsalg'], {'S': SS})
    la, lc = split_imp(LSA)
    lsa = s([b0, w.inst('kdlsalg')], 'syl', lc)
    LS = LSK('K', SS)
    # LSK e. CC (under the LFN-free antecedent B0)
    TB = lambda x: '( ( ( ( log ` %s ) ^ K ) x. ( %s x. ( Lam ` %s ) ) ) x. ( %s ^c -u %s ) )' % (x, CHV(x), x, x, SS)
    G = '( n e. NN |-> %s )' % TB('n')
    LSB = tsub(S['kdlsb'], {'S': SS})
    lba, lbc = split_imp(LSB)
    bB = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (B0, f))
    nxB = bB([], 'simpl', NXH); eeB = bB([], 'simprl', '( E e. RR+ /\\ E <_ 1 )'); sgB = bB([], 'simprr', '( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ K e. NN0 )' % (SS, SS))
    lsb = bB([nxB, eeB, sgB, w.inst('kdlsb')], 'syl3anc', lbc)
    cvg = bB([lsb], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % G)
    Bk = '( %s /\\ k e. NN )' % B0
    q = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Bk, f))
    Lk = lambda st: lift(w, st, Bk)
    kn = q([], 'simpr', 'k e. NN')
    chk = q([q([Lk(nxB), kn], 'jca', '( %s /\\ k e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CHV('k'))
    lam = q([q([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    lkK = q([q([q([q([kn], 'nnrpd', 'k e. RR+')], 'relogcld', '( log ` k ) e. RR')], 'recnd', '( log ` k ) e. CC'), q([Lk(sgB)], 'simp3d', 'K e. NN0')], 'expcld', '( ( log ` k ) ^ K ) e. CC')
    ek = q([q([kn], 'nncnd', 'k e. CC'), q([q([Lk(sgB)], 'simp1d', '%s e. CC' % SS)], 'negcld', '-u %s e. CC' % SS)], 'cxpcld', '( k ^c -u %s ) e. CC' % SS)
    tbc = q([q([lkK, q([chk, lam], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHV('k'))], 'mulcld', '( ( ( log ` k ) ^ K ) x. ( %s x. ( Lam ` k ) ) ) e. CC' % CHV('k')), ek], 'mulcld', '%s e. CC' % TB('k'))
    idn = w.s([], 'id', '( n = k -> n = k )')
    cn, vn = w.congr(TB('n'), {'n': 'k'}, 'n = k', {'n': idn})
    gv = fvmd(w, Bk, G, 'k', vn, kn, tbc, cn, var='n')
    lskc = bB([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )') and bB([], '1zzd', '1 e. ZZ'), gv, tbc, cvg], 'T.', 'T.') if False else \
        w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % B0), gv, tbc, cvg], 'isumcl', '( %s -> sum_ k e. NN %s e. CC )' % (B0, TB('k')))
    idk = w.s([], 'id', '( k = n -> k = n )')
    ck, nk = w.congr(TB('k'), {'k': 'n'}, 'k = n', {'k': idk})
    cbl = w.s([ck], 'cbvsumv', 'sum_ k e. NN %s = %s' % (TB('k'), LS))
    lsc = s([b0, w.s([w.s([cbl], 'a1i', '( %s -> sum_ k e. NN %s = %s )' % (B0, TB('k'), LS)), lskc], 'eqeltrrd', '( %s -> %s e. CC )' % (B0, LS))], 'syl', '%s e. CC' % LS)
    # the finite sum over the zeros
    Aq = '( %s /\\ q e. %s )' % (A0, ZD())
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    L = lambda st: lift(w, st, Aq)
    qq = a([], 'simpr', 'q e. %s' % ZD())
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0]); zord = s([lz], 'simp2d', top_and(lzc)[1])
    mqn = a([qq, a([L(zord), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (ZD(), MU('q')))], 'mpd', '%s e. NN' % MU('q'))
    mqc = a([mqn], 'nncnd', '%s e. CC' % MU('q'))
    rq = a([L(chi), L(tr), qq, w.inst('kdre1')], 'syl3anc', '( Re ` q ) <_ 1')
    SQ13 = SQ(CT('T'), R138)
    from kd1_q import corners
    cct = a([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % Aq), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([L(tr)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CT('T'))
    cq = Closure(w, Aq, {'T': ('RR', L(tr))})
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    ric = a([a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
            'addcld', '%s e. CC' % RI_)
    sqcc = a([a([a([cct, ric], 'subcld', '%s e. CC' % A13), a([cct, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    qc = a([sqcc, a([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Aq, ZD(), SQ13)), qq], 'sseldd', 'q e. %s' % SQ13)], 'sseldd', 'q e. CC')
    D_ = '( %s - q )' % SS
    dc = a([L(s0c), qc], 'subcld', '%s e. CC' % D_)
    rd = a([L(s0c), qc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` q ) )' % (D_, SS))
    cq.leaf('E', 'RR', L(er)); cq.leaf('( Re ` q )', 'RR', a([qc], 'recld', '( Re ` q ) e. RR')); cq.atom('( Re ` q )')
    cq.leaf('( Re ` %s )' % SS, 'RR', a([L(s0c)], 'recld', '( Re ` %s ) e. RR' % SS)); cq.atom('( Re ` %s )' % SS)
    cq.leaf('( Re ` %s )' % D_, 'RR', a([dc], 'recld', '( Re ` %s ) e. RR' % D_)); cq.atom('( Re ` %s )' % D_)
    rpos = linarith(w, Aq, [rd, L(rs0), rq, L(s([ep], 'rpgt0d', '0 < E'))], '0 < ( Re ` %s )' % D_, closure=cq)
    rne = a([rpos], 'gt0ne0d', '( Re ` %s ) =/= 0' % D_)
    rne0 = a([rne, w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % Aq)], 'neeqtrrd', '( Re ` %s ) =/= ( Re ` 0 )' % D_)
    dn = a([rne0, w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (D_, D_))], 'necon3i', '( ( Re ` %s ) =/= ( Re ` 0 ) -> %s =/= 0 )' % (D_, D_))], 'syl', '%s =/= 0' % D_)
    Y_ = '( %s ^ ( K + 1 ) )' % D_
    k1 = L(s([kk, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0'))
    yc = a([dc, k1], 'expcld', '%s e. CC' % Y_)
    yn = a([dc, dn, a([k1], 'nn0zd', '( K + 1 ) e. ZZ')], 'expne0d', '%s =/= 0' % Y_)
    TQ = '( %s / %s )' % (MU('q'), Y_)
    tqc = a([mqc, yc, yn], 'divcld', '%s e. CC' % TQ)
    SG = 'sum_ q e. %s %s' % (ZD(), TQ)
    sgc = s([zfin, tqc], 'fsumcl', '%s e. CC' % SG)
    Cc = '( ( -u 1 ^ K ) x. ( ! ` K ) )'
    p_ = '( -u 1 ^ K )'; f_ = '( ! ` K )'
    pc_ = s([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % A0), kk], 'expcld', '%s e. CC' % p_)
    fk = s([kk, w.inst('faccl')], 'syl', '%s e. NN' % f_)
    fc_ = s([fk], 'nncnd', '%s e. CC' % f_)
    ccc = s([pc_, fc_], 'mulcld', '%s e. CC' % Cc)
    wv = fvmd(w, Aq, WMM, 'q', MU('q'), qq, w.s([w.s([], 'ovex', '%s e. _V' % MU('q'))], 'a1i', '( %s -> %s e. _V )' % (Aq, MU('q'))),
              w.s([], 'oveq2', '( p = q -> %s = %s )' % (MU('p'), MU('q'))), var='p')
    PQK = PQ('K', SS)
    assert PQK == '( %s / %s )' % (Cc, Y_), PQK
    t1 = a([wv], 'oveq1d', '( ( %s ` q ) x. %s ) = ( %s x. %s )' % (WMM, PQK, MU('q'), PQK))
    t2 = a([mqc, L(ccc), yc, yn], 'div12d', '( %s x. %s ) = ( %s x. %s )' % (MU('q'), PQK, Cc, TQ))
    tt = a([t1, t2], 'eqtrd', '( ( %s ` q ) x. %s ) = ( %s x. %s )' % (WMM, PQK, Cc, TQ))
    SW = 'sum_ q e. %s ( ( %s ` q ) x. %s )' % (ZD(), WMM, PQK)
    swe = s([tt], 'sumeq2dv', '%s = sum_ q e. %s ( %s x. %s )' % (SW, ZD(), Cc, TQ))
    fsm = s([zfin, ccc, tqc], 'fsummulc2', '( %s x. %s ) = sum_ q e. %s ( %s x. %s )' % (Cc, SG, ZD(), Cc, TQ))
    swe2 = s([swe, fsm], 'eqtr4d', '%s = ( %s x. %s )' % (SW, Cc, SG))
    PSK = PSINST('K', SS)
    S1K = S1I('K', SS)
    assert PSK == '( -u %s - %s )' % (S1K, SW), PSK[:300]
    Y2 = '( %s / %s )' % (LS, f_)
    y2c = s([lsc, fc_, s([fk], 'nnne0d', '%s =/= 0' % f_)], 'divcld', '%s e. CC' % Y2)
    lsy = s([lsc, fc_, s([fk], 'nnne0d', '%s =/= 0' % f_)], 'divcan2d', '( %s x. %s ) = %s' % (f_, Y2, LS))
    X = '( %s + %s )' % (SG, Y2)
    e_ps1 = s([s([s([lsa, s([s([lsy], 'eqcomd', '%s = ( %s x. %s )' % (LS, f_, Y2))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (p_, LS, p_, f_, Y2))], 'eqtrd',
                   '%s = ( %s x. ( %s x. %s ) )' % (S1K, p_, f_, Y2))], 'negeqd', '-u %s = -u ( %s x. ( %s x. %s ) )' % (S1K, p_, f_, Y2)), swe2], 'oveq12d',
              '%s = ( -u ( %s x. ( %s x. %s ) ) - ( %s x. %s ) )' % (PSK, p_, f_, Y2, Cc, SG))
    cr = Closure(w, A0, {p_: ('CC', pc_), f_: ('CC', fc_), Y2: ('CC', y2c), SG: ('CC', sgc)})
    for a_ in (p_, f_, Y2, SG):
        cr.atom(a_)
    e_ps2 = ringeq(w, A0, '( -u ( %s x. ( %s x. %s ) ) - ( %s x. %s ) )' % (p_, f_, Y2, Cc, SG), '-u ( %s x. %s )' % (Cc, X), cr)
    eps = s([e_ps1, e_ps2], 'eqtrd', '%s = -u ( %s x. %s )' % (PSK, Cc, X))
    xc = s([sgc, y2c], 'addcld', '%s e. CC' % X)
    ab1 = s([s([eps], 'fveq2d', '( abs ` %s ) = ( abs ` -u ( %s x. %s ) )' % (PSK, Cc, X)), s([s([ccc, xc], 'mulcld', '( %s x. %s ) e. CC' % (Cc, X))], 'absnegd', '( abs ` -u ( %s x. %s ) ) = ( abs ` ( %s x. %s ) )' % (Cc, X, Cc, X)),
             s([ccc, xc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (Cc, X, Cc, X))], '3eqtrd', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (PSK, Cc, X))
    ap = s([s([pc_, fc_], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (Cc, p_, f_)),
            s([s([s([w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % A0), kk], 'absexpd', '( abs ` %s ) = ( ( abs ` -u 1 ) ^ K )' % p_),
                  s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('absneg')], 'ax-mp', '( abs ` -u 1 ) = ( abs ` 1 )'), w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtri', '( abs ` -u 1 ) = 1')], 'a1i', '( %s -> ( abs ` -u 1 ) = 1 )' % A0) and
                    s([w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('absneg')], 'ax-mp', '( abs ` -u 1 ) = ( abs ` 1 )'), w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtri', '( abs ` -u 1 ) = 1')], 'a1i', '( %s -> ( abs ` -u 1 ) = 1 )' % A0)], 'oveq1d', '( ( abs ` -u 1 ) ^ K ) = ( 1 ^ K )'),
                  s([s([kk], 'nn0zd', 'K e. ZZ'), w.inst('1exp')], 'syl', '( 1 ^ K ) = 1')], '3eqtrd', '( abs ` %s ) = 1' % p_),
               s([s([fk], 'nnred', '%s e. RR' % f_), s([s([fk], 'nnrpd', '%s e. RR+' % f_)], 'rpge0d', '0 <_ %s' % f_)], 'absidd', '( abs ` %s ) = %s' % (f_, f_))], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( 1 x. %s )' % (p_, f_, f_)),
            s([fc_], 'mullidd', '( 1 x. %s ) = %s' % (f_, f_))], '3eqtrd', '( abs ` %s ) = %s' % (Cc, f_))
    ab2 = s([ab1, s([ap], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (Cc, X, f_, X))], 'eqtrd', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (PSK, f_, X))
    # the remainder: kdrem, kdrepg, kdrepb
    Ag = '( %s /\\ %s )' % (A0, HGP())
    g = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ag, f))
    rg = w.s([], 'kdrepg', S['kdrepg'])
    rb = w.s([], 'kdrepb', S['kdrepb'])
    DN = '( ( ( CC Dn g ) ` K ) ` %s )' % SS
    B2 = '( ( 2 x. ( 3 ^ K ) ) x. %s )' % KL
    bb = g([g([rg], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (DN, PSK)), rb], 'eqbrtrrd', '( abs ` %s ) <_ ( %s x. %s )' % (PSK, f_, B2))
    bb2 = g([lift(w, ab2, Ag), bb], 'eqbrtrrd', '( %s x. ( abs ` %s ) ) <_ ( %s x. %s )' % (f_, X, f_, B2))
    nxg = lift(w, nx, Ag); trg = lift(w, tr, Ag); kkg = lift(w, kk, Ag)
    at = g([g([trg], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    at0 = g([g([trg], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    cg = Closure(w, Ag, {'( abs ` T )': ('RR', at)}); cg.atom('( abs ` T )')
    t2p = g([cg.mem('( ( abs ` T ) + 2 )', 'RR'), linarith(w, Ag, [at0], '0 < ( ( abs ` T ) + 2 )', closure=cg)], 'elrpd', '( ( abs ` T ) + 2 ) e. RR+')
    XT = '( N x. ( ( abs ` T ) + 2 ) )'
    xtp = g([g([g([nxg], 'simpld', 'N e. NN')], 'nnrpd', 'N e. RR+'), t2p], 'rpmulcld', '%s e. RR+' % XT)
    lg = g([xtp], 'relogcld', '( log ` %s ) e. RR' % XT)
    cb2 = Closure(w, Ag, {'( log ` %s )' % XT: ('RR', lg), '( 3 ^ K )': ('RR', g([w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % Ag), kkg], 'reexpcld', '( 3 ^ K ) e. RR'))})
    cb2.atom('( log ` %s )' % XT); cb2.atom('( 3 ^ K )')
    b2r = cb2.mem(B2, 'RR')
    axr = g([lift(w, xc, Ag)], 'abscld', '( abs ` %s ) e. RR' % X)
    fkp = g([lift(w, fk, Ag)], 'nnrpd', '%s e. RR+' % f_)
    lm = g([axr, b2r, fkp], 'lemul2d', '( ( abs ` %s ) <_ %s <-> ( %s x. ( abs ` %s ) ) <_ ( %s x. %s ) )' % (X, B2, f_, X, f_, B2))
    fin_g = g([bb2, lm], 'mpbird', '( abs ` %s ) <_ %s' % (X, B2))
    REM = tsub(S['kdrem'], {})
    ra, rc = split_imp(REM)
    ex_g = s([s([chi, tr], 'jca', ra), w.inst('kdrem')], 'syl', rc)
    assert S['kdrep'].endswith('( abs ` %s ) <_ %s )' % (X, B2)), S['kdrep'][-300:]
    w.qed([ex_g, fin_g], 'exlimddv', S['kdrep'])
    return run(w)




if __name__ == '__main__':
    gen_rep()
