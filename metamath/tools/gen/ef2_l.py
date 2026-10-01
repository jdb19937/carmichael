"""Sortie EF2: the strip residue theorem about a generic centre T (ef2stc) and Lean rectInt_strip (ef2strip)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
from z4blib import fvmd
import ef2_h, ef2_i, ef2_j, ef2_k
from ef2_h import CN0
import lin
lin.FASTPATH = True

C0_ = CT('T')
QA_, QB_ = SQA(C0_, R138), SQB(C0_, R138)
Q_ = SQ(C0_, R138)
Z_ = ZS('F', 'T')
D1 = "( ( `' Re \" ( ( Re ` %s ) (,) ( Re ` %s ) ) ) i^i ( `' Im \" ( ( Im ` %s ) (,) ( Im ` %s ) ) ) )" % (QA_, QB_, QA_, QB_)
E_ = '( %s \\ %s )' % (D1, Z_)
SA, SB = '( S + ( _i x. L ) )', '( C + ( _i x. H ) )'
R_ = '( %s crect %s )' % (SA, SB)
FRX = tsub(ef2_j.FRX, {'P': 'S', 'Q': 'C', 'S': 'L', 'R': 'H'})
FRAB = tsub(ef2_i.FRAB, {'A': SA, 'B': SB})
TMq = lambda q: '( d e. %s |-> ( ( F holord %s ) x. ( ( %s ` d ) / ( d - %s ) ) ) )' % (E_, q, PKF(), q)
GF = '( a e. %s |-> %s )' % (Z_, TMq('a'))
PSI = '( b e. %s |-> sum_ k e. %s ( ( %s ` k ) ` b ) )' % (E_, Z_, GF)
LDIB = '( b e. { v e. %s | ( F ` v ) =/= 0 } |-> ( ( ( ( CC _D F ) ` b ) / ( F ` b ) ) x. ( ( Y ^c b ) / b ) ) )' % HP0
F1 = '( d e. %s |-> ( ( CC _D h ) ` d ) )' % D1
G1 = '( d e. %s |-> ( h ` d ) )' % D1
M2 = '( e e. %s |-> ( ( %s ` e ) / ( %s ` e ) ) )' % (D1, F1, G1)
P1 = '( d e. %s |-> ( %s ` d ) )' % (D1, PKF())
PHI = '( c e. %s |-> ( ( %s ` c ) x. ( %s ` c ) ) )' % (D1, M2, P1)
HR = '( %s |` %s )' % (PHI, E_)
ZIT = '{ p e. %s | %s }' % (Z_, SIN('p'))
X1 = '( %s /\\ T e. RR /\\ ( Y e. RR /\\ 1 < Y ) )' % DD()
X2 = ('( ( ( S e. RR /\\ C e. RR ) /\\ ( L e. RR /\\ H e. RR ) ) /\\ ( ( ( 3 / 8 ) < S /\\ S < C /\\ C < ( ; 2 9 / 8 ) ) /\\ '
      '( ( T - %s ) < L /\\ L < H /\\ H < ( T + %s ) ) ) )') % (R138, R138)
FRH_ = 'A. p e. %s ( ( F ` p ) = 0 -> %s )' % (R_, SIN('p'))
S['ef2stc'] = '( ( %s /\\ %s /\\ %s ) -> ( %s rectint <. %s , %s >. ) = ( %s x. sum_ q e. %s ( ( F holord q ) x. ( ( Y ^c q ) / q ) ) ) )' % (
    X1, X2, FRH_, LDI(), SA, SB, TPI, ZIT)


def facts0(w, C, a0):
    """the h-free facts in context C with a0 : ( C -> ante )"""
    A0 = ante_of(S['ef2stc'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    f = {}
    x1 = s([a0, w.inst('simp1')], 'syl', X1); x2 = s([a0, w.inst('simp2')], 'syl', X2); f['frh'] = s([a0, w.inst('simp3')], 'syl', FRH_)
    f['dd'] = s([x1, w.inst('simp1')], 'syl', DD()); f['tr'] = s([x1, w.inst('simp2')], 'syl', 'T e. RR')
    y2 = s([x1, w.inst('simp3')], 'syl', '( Y e. RR /\\ 1 < Y )')
    f['yr'] = s([y2, w.inst('simpl')], 'syl', 'Y e. RR'); y1 = s([y2, w.inst('simpr')], 'syl', '1 < Y')
    f['yrp'] = s([f['yr'], lin8(w, C, [y1], '0 < Y', {'Y': f['yr']})], 'elrpd', 'Y e. RR+')
    V1, V2 = top_and(X2)
    v1 = s([x2, w.inst('simpl')], 'syl', V1); v2 = s([x2, w.inst('simpr')], 'syl', V2)
    sc = s([v1, w.inst('simpl')], 'syl', '( S e. RR /\\ C e. RR )'); lh = s([v1, w.inst('simpr')], 'syl', '( L e. RR /\\ H e. RR )')
    for k, st, rel in (('S', sc, 'simpl'), ('C', sc, 'simpr'), ('L', lh, 'simpl'), ('H', lh, 'simpr')):
        f[k] = s([st, w.inst(rel)], 'syl', '%s e. RR' % k)
    f['sc'] = sc; f['lh'] = lh; f['v1'] = v1
    W1, W2 = top_and(V2)
    w1 = s([v2, w.inst('simpl')], 'syl', W1); w2 = s([v2, w.inst('simpr')], 'syl', W2)
    ineq = []
    for st, F3 in ((w1, W1), (w2, W2)):
        for k, part in zip(('simp1', 'simp2', 'simp3'), top_and(F3)):
            ineq.append(s([st, w.inst(k)], 'syl', part))
    f['ineq'] = ineq
    d = sq_data(w, C, 'T', f['tr'])
    f['sq'] = d
    lv = dict(d['lv']); lv.update({'S': f['S'], 'C': f['C'], 'L': f['L'], 'H': f['H'], 'T': f['tr']})
    # the strip corners
    def cor(re, im):
        c = s([s([f[re]], 'recnd', '%s e. CC' % re), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([f[im]], 'recnd', '%s e. CC' % im)], 'mulcld', '( _i x. %s ) e. CC' % im)],
              'addcld', '( %s + ( _i x. %s ) ) e. CC' % (re, im))
        rr = s([f[re], f[im]], 'crred', '( Re ` ( %s + ( _i x. %s ) ) ) = %s' % (re, im, re))
        ii = s([f[re], f[im]], 'crimd', '( Im ` ( %s + ( _i x. %s ) ) ) = %s' % (re, im, im))
        return c, rr, ii
    f['sa'], f['rsa'], f['isa'] = cor('S', 'L'); f['sb'], f['rsb'], f['isb'] = cor('C', 'H')
    for x, st in ((SA, f['sa']), (SB, f['sb'])):
        lv['( Re ` %s )' % x] = s([st], 'recld', '( Re ` %s ) e. RR' % x)
        lv['( Im ` %s )' % x] = s([st], 'imcld', '( Im ` %s ) e. RR' % x)
    f['lv'] = lv
    hy = d['eqs'] + ineq + [f['rsa'], f['isa'], f['rsb'], f['isb']]
    f['hy'] = hy
    abq = s([d['a'], d['b']], 'jca', '( %s e. CC /\\ %s e. CC )' % (QA_, QB_))
    f['abq'] = abq
    f['d1o'] = s([w.s([], 'orectopn', '%s e. ( TopOpen ` CCfld )' % D1)], 'a1i', '%s e. ( TopOpen ` CCfld )' % D1)
    f['d1q'] = s([abq, w.inst('orectss')], 'syl', '%s C_ %s' % (D1, Q_))
    rq0 = lin8(w, C, hy, '0 < ( Re ` %s )' % QA_, lv)
    rh = s([s([abq, rq0], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ 0 < ( Re ` %s ) )' % (QA_, QB_, QA_)), w.inst('ef2rhp')], 'syl', '( %s C_ %s /\\ %s C_ %s )' % (Q_, HP0, Q_, CN0))
    f['qhp'] = s([rh, w.inst('simpl')], 'syl', '%s C_ %s' % (Q_, HP0)); f['qcn'] = s([rh, w.inst('simpr')], 'syl', '%s C_ %s' % (Q_, CN0))
    f['d1hp'] = s([f['d1q'], f['qhp']], 'sstrd', '%s C_ %s' % (D1, HP0)); f['d1cn'] = s([f['d1q'], f['qcn']], 'sstrd', '%s C_ %s' % (D1, CN0))
    CR = tsub(stmt('crectorect'), {'A': QA_, 'B': QB_, 'P': SA, 'Q': SB})
    cra, crc = ante_of(CR)
    have = {'( %s e. CC /\\ %s e. CC )' % (QA_, QB_): abq, '( %s e. CC /\\ %s e. CC )' % (SA, SB): s([f['sa'], f['sb']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB))}
    for g in ('( Re ` %s ) < ( Re ` %s )' % (QA_, SA), '( Re ` %s ) < ( Re ` %s )' % (SB, QB_), '( Im ` %s ) < ( Im ` %s )' % (QA_, SA), '( Im ` %s ) < ( Im ` %s )' % (SB, QB_)):
        have[g] = lin8(w, C, hy, g, lv)
    f['rd1'] = s([conj(w, C, cra, have), w.inst('crectorect')], 'syl', crc)
    f['absb'] = have['( %s e. CC /\\ %s e. CC )' % (SA, SB)]
    zc = tsub(ante_of(S['ef2zs'])[1], {})
    zs = s([s([f['dd'], f['tr']], 'jca', '( %s /\\ T e. RR )' % DD()), w.inst('ef2zs')], 'syl', zc)
    f['zfin'] = s([zs, w.inst('simp1')], 'syl', top_and(zc)[0]); f['zall'] = s([zs, w.inst('simp2')], 'syl', top_and(zc)[1])
    f['ed1'] = s([w.s([], 'difss', '%s C_ %s' % (E_, D1))], 'a1i', '%s C_ %s' % (E_, D1))
    f['ecn'] = s([f['ed1'], f['d1cn']], 'sstrd', '%s C_ %s' % (E_, CN0))
    f['ecc'] = s([f['ecn'], s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % E_)
    f['geo'] = [lin8(w, C, hy, g, lv) for g in ('0 < ( Re ` %s )' % SA, '( Re ` %s ) <_ ( Re ` %s )' % (SA, SB), '( Im ` %s ) <_ ( Im ` %s )' % (SA, SB))]
    return f


def frame_facts(w, C, f):
    """( C -> FRAB C_ E_ ), ( C -> FRX C_ E_ ), ( C -> FRAB = FRX )"""
    s = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (C, fm))
    geo2 = s([f['geo'][1], f['geo'][2]], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (SA, SB, SA, SB))
    fru = s([f['absb'], geo2, w.inst('crectfru')], 'syl2anc', '%s C_ %s' % (FRAB, R_))
    FRE = tsub(stmt('crectfre'), {'A': SA, 'B': SB})
    fre = s([f['absb'], geo2, w.inst('crectfre')], 'syl2anc', ante_of(FRE)[1])
    DISJ = ante_of(FRE)[1][len('A. u e. %s ' % FRAB):]
    Cu = '( %s /\\ u e. %s )' % (C, FRAB)
    su = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Cu, fm))
    uf = su([], 'simpr', 'u e. %s' % FRAB)
    dj = w.s([fre], 'r19.21bi', '( %s -> %s )' % (Cu, DISJ))
    ur = su([up(w, fru, Cu), uf], 'sseldd', 'u e. %s' % R_)
    ud1 = su([up(w, f['rd1'], Cu), ur], 'sseldd', 'u e. %s' % D1)
    Cz = '( %s /\\ u e. %s )' % (Cu, Z_)
    sz = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Cz, fm))
    uz = sz([], 'simpr', 'u e. %s' % Z_)
    e1 = w.s([w.s([], 'fveq2', '( r = u -> ( F ` r ) = ( F ` u ) )')], 'eqeq1d', '( r = u -> ( ( F ` r ) = 0 <-> ( F ` u ) = 0 ) )')
    fz = sz([sz([uz, w.s([e1], 'elrab', '( u e. %s <-> ( u e. %s /\\ ( F ` u ) = 0 ) )' % (Z_, Q_))], 'sylib', '( u e. %s /\\ ( F ` u ) = 0 )' % Q_), w.inst('simpr')], 'syl', '( F ` u ) = 0')
    idp = w.s([], 'id', '( p = u -> p = u )')
    cp, _ = w.wcongr('( ( F ` p ) = 0 -> %s )' % SIN('p'), {'p': 'u'}, 'p = u', {'p': idp})
    fh = sz([cp, up(w, f['frh'], Cz), up(w, ur, Cz)], 'rspcdva', '( ( F ` u ) = 0 -> %s )' % SIN('u'))
    sin = sz([fz, fh], 'mpd', SIN('u'))
    Ra, Rb, Ia, Ib = top_and(top_and(SIN('u'))[0])[0], top_and(top_and(SIN('u'))[0])[1], top_and(top_and(SIN('u'))[1])[0], top_and(top_and(SIN('u'))[1])[1]
    s1 = sz([sin, w.inst('simpl')], 'syl', top_and(SIN('u'))[0]); s2 = sz([sin, w.inst('simpr')], 'syl', top_and(SIN('u'))[1])
    ra = sz([s1, w.inst('simpl')], 'syl', Ra); rb = sz([s1, w.inst('simpr')], 'syl', Rb); ia = sz([s2, w.inst('simpl')], 'syl', Ia); ib = sz([s2, w.inst('simpr')], 'syl', Ib)
    lvz = {k: up(w, v, Cz) for k, v in f['lv'].items()}
    ucc = sz([sz([up(w, f['sa'], Cz), up(w, f['sb'], Cz), w.inst('crectss')], 'syl2anc', '%s C_ CC' % R_), up(w, ur, Cz)], 'sseldd', 'u e. CC')
    lvz['( Re ` u )'] = sz([ucc], 'recld', '( Re ` u ) e. RR'); lvz['( Im ` u )'] = sz([ucc], 'imcld', '( Im ` u ) e. RR')
    hyz = [up(w, st, Cz) for st in (f['rsa'], f['isa'], f['rsb'], f['isb'])] + [ra, rb, ia, ib]
    n1 = sz([lin8(w, Cz, hyz, '( Re ` %s ) < ( Re ` u )' % SA, lvz)], 'gtned', '( Re ` u ) =/= ( Re ` %s )' % SA)
    n2 = sz([lin8(w, Cz, hyz, '( Re ` u ) < ( Re ` %s )' % SB, lvz)], 'ltned', '( Re ` u ) =/= ( Re ` %s )' % SB)
    n3 = sz([lin8(w, Cz, hyz, '( Im ` %s ) < ( Im ` u )' % SA, lvz)], 'gtned', '( Im ` u ) =/= ( Im ` %s )' % SA)
    n4 = sz([lin8(w, Cz, hyz, '( Im ` u ) < ( Im ` %s )' % SB, lvz)], 'ltned', '( Im ` u ) =/= ( Im ` %s )' % SB)
    DR = DISJ[2:DISJ.index(' \\/ ( ( Im')]
    DI = DISJ[DISJ.index('( ( Im'):-2]
    nr = sz([sz([n1, n2], 'jca', '( ( Re ` u ) =/= ( Re ` %s ) /\\ ( Re ` u ) =/= ( Re ` %s ) )' % (SA, SB)),
             w.s([], 'neanior', '( ( ( Re ` u ) =/= ( Re ` %s ) /\\ ( Re ` u ) =/= ( Re ` %s ) ) <-> -. %s )' % (SA, SB, DR))], 'sylib', '-. %s' % DR)
    ni = sz([sz([n3, n4], 'jca', '( ( Im ` u ) =/= ( Im ` %s ) /\\ ( Im ` u ) =/= ( Im ` %s ) )' % (SA, SB)),
             w.s([], 'neanior', '( ( ( Im ` u ) =/= ( Im ` %s ) /\\ ( Im ` u ) =/= ( Im ` %s ) ) <-> -. %s )' % (SA, SB, DI))], 'sylib', '-. %s' % DI)
    nd = sz([sz([nr, ni], 'jca', '( -. %s /\\ -. %s )' % (DR, DI)), w.s([], 'ioran', '( -. %s <-> ( -. %s /\\ -. %s ) )' % (DISJ, DR, DI))], 'sylibr', '-. %s' % DISJ)
    nz = su([up(w, dj, Cz), nd], 'pm2.65da', '-. u e. %s' % Z_)
    ue = su([ud1, nz], 'eldifd', 'u e. %s' % E_)
    fe = s([w.s([ue], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (C, FRAB, E_))], 'ssrdv', '%s C_ %s' % (FRAB, E_))
    eq, new = w.congr(FRAB, {}, C, {}, rules={'( Re ` %s )' % SB: ('C', f['rsb']), '( Im ` %s )' % SA: ('L', f['isa']), '( Re ` %s )' % SA: ('S', f['rsa']), '( Im ` %s )' % SB: ('H', f['isb'])})
    assert new == FRX, (new, FRX)
    fx = s([eq, fe], 'eqsstrrd', '%s C_ %s' % (FRX, E_))
    return fe, fx, eq, fru


def gen_stc():
    w = W('ef2stc', 'The strip residue theorem about a generic centre ` T ` : for a ` DiskData ` function ` F ` whose zeros in the closed rectangle ` [ S , C ] x. [ L , H ] ` (inside the ` 13 / 8 ` square about ` 2 + i T ` ) are strictly inside, the boundary integral of ` ( F-prime / F ) ( s ) y ^ s / s ` is ` 2 pi i ` times the sum of ` m_rho y ^ rho / rho ` over those zeros ( ~ ef2lds , ~ ef2stk , ~ ef2rsum ; Cauchy-Goursat for ` ( h-prime / h ) y ^ s / s ` by ~ ef2dvh and ~ rectintgour ).')
    A0, GC = ante_of(S['ef2stc'])
    s = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (A0, fm))
    f0 = facts0(w, A0, s([], 'id', A0))
    fe, fx, freq, fru = frame_facts(w, A0, f0)
    # zdfac: the cofactor h
    ZD = stmt('zdfac')
    za, zcn = ante_of(ZD)
    fc0 = s([s([f0['dd'], f0['tr']], 'jca', '( %s /\\ T e. RR )' % DD()), w.inst('ef2cnz')], 'syl', '( F ` %s ) =/= 0' % C0_)
    hol0 = dd_parts(w, A0, f0['dd'])[0]
    exh = s([hol0, f0['tr'], fc0, w.inst('zdfac')], 'syl3anc', zcn)
    HB = zcn[len('E. h '):]
    Ah = '( %s /\\ %s )' % (A0, HB)
    sh = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Ah, fm))
    U = lambda k: up(w, f0[k], Ah)
    hb = sh([], 'simpr', HB)
    B1, B2, B3 = top_and(HB)
    hh = sh([hb, w.inst('simp1')], 'syl', B1); nzq = sh([hb, w.inst('simp3')], 'syl', B3)
    ddt = sh([U('dd'), U('tr')], 'jca', '( %s /\\ T e. RR )' % DD())
    lds = sh([sh([ddt, hb], 'jca', ante_of(S['ef2lds'])[0]), w.inst('ef2lds')], 'syl', ante_of(S['ef2lds'])[1])
    feh = up(w, fe, Ah); fxh = up(w, fx, Ah)
    K = '( TopOpen ` CCfld )'
    yrp = U('yrp')
    # ---- the cofactor term: Goursat ----
    dh = sh([hh, w.s([], 'ef2dvh', '( %s -> %s )' % (HOLF('h', HP0), HOLF('( CC _D h )', HP0)))], 'syl', HOLF('( CC _D h )', HP0))
    d1o = U('d1o'); d1hp = U('d1hp'); d1cn = U('d1cn')
    def res(Fh, Fn, Dn, sub_ss):
        ZR = tsub(stmt('zl2hres'), {'F': Fn, 'D': Dn, 'U': D1, 'z': 'd'})
        za_, zc_ = ante_of(ZR)
        return sh([sh([Fh, sh([d1o, sub_ss], 'jca', '( %s e. %s /\\ %s C_ %s )' % (D1, K, D1, Dn))], 'jca', za_), w.s([], 'zl2hres', ZR)], 'syl', zc_)
    f1h = res(dh, '( CC _D h )', HP0, d1hp)
    g1h = res(hh, 'h', HP0, d1hp)
    pkh = sh([yrp, w.s([], 'pkfhol', '( Y e. RR+ -> %s )' % HOLF(PKF(), CN0))], 'syl', HOLF(PKF(), CN0))
    p1h = res(pkh, PKF(), CN0, d1cn)
    Av = '( %s /\\ v e. %s )' % (Ah, D1)
    sv = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Av, fm))
    vd = sv([], 'simpr', 'v e. %s' % D1)
    g1v = fvmd(w, Av, 'd', D1, '( h ` d )', 'v', vd, w.s([], 'fvexd', '( %s -> ( h ` v ) e. _V )' % Av))
    subz = w.s([w.s([], 'fveq2', '( z = v -> ( h ` z ) = ( h ` v ) )')], 'neeq1d', '( z = v -> ( ( h ` z ) =/= 0 <-> ( h ` v ) =/= 0 ) )')
    hv0 = sv([subz, up(w, nzq, Av), sv([up(w, U('d1q'), Av), vd], 'sseldd', 'v e. %s' % Q_)], 'rspcdva', '( h ` v ) =/= 0')
    nzg = w.s([sv([g1v, hv0], 'eqnetrd', '( %s ` v ) =/= 0' % G1)], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (Ah, D1, G1))
    HD = tsub(stmt('holdiv'), {'F': F1, 'G': G1, 'D': D1, 'z': 'e'})
    m2h = sh([f1h, g1h, nzg, w.s([], 'holdiv', HD)], 'syl3anc', HOLF(M2, D1))
    HM = tsub(stmt('holmul'), {'F': M2, 'G': P1, 'D': D1, 'z': 'c'})
    phh = sh([m2h, p1h, w.s([], 'holmul', HM)], 'syl2anc', HOLF(PHI, D1))
    hc = sh([sh([phh, up(w, f0['rd1'], Ah)], 'jca', '( %s /\\ %s C_ %s )' % (HOLF(PHI, D1), R_, D1)), w.inst('holcrect')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (PHI, D1, R_, PHI))
    RG = tsub(stmt('rectintgour'), {'F': PHI, 'D': D1, 'A': SA, 'B': SB})
    rga, rgc = ante_of(RG)
    geo = [up(w, g, Ah) for g in f0['geo']]
    hv = {'( %s e. CC /\\ %s e. CC )' % (SA, SB): U('absb'), '( Re ` %s ) <_ ( Re ` %s )' % (SA, SB): geo[1], '( Im ` %s ) <_ ( Im ` %s )' % (SA, SB): geo[2], body_of(w, hc): hc}
    iphi = sh([conj(w, Ah, rga, hv), w.inst('rectintgour')], 'syl', rgc)
    phcn = sh([phh, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PHI, D1))
    ed1 = U('ed1')
    hrc = sh([ed1, phcn, w.inst('rescncf')], 'sylc', '%s e. ( %s -cn-> CC )' % (HR, E_))
    phx = sh([sh([d1o, w.inst('elex')], 'syl', '%s e. _V' % D1), w.inst('mptexg')], 'syl', '%s e. _V' % PHI)
    hrx = sh([phx, w.inst('resexg')], 'syl', '%s e. _V' % HR)
    Au2 = '( %s /\\ u e. %s )' % (Ah, E_)
    hrv = w.s([w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au2, E_)), w.inst('fvres')], 'syl', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (Au2, HR, PHI))], 'ralrimiva',
              '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (Ah, E_, HR, PHI))
    EQ = tsub(stmt('rectinteqe'), {'F': HR, 'G': PHI, 'V': '_V', 'E': E_, 'A': SA, 'B': SB})
    eqa, eqc = ante_of(EQ)
    ihr = sh([conj(w, Ah, eqa, {'( %s e. CC /\\ %s e. CC )' % (SA, SB): U('absb'), '%s C_ %s' % (FRAB, E_): feh, '%s e. _V' % HR: hrx, '%s e. _V' % PHI: phx, body_of(w, hrv): hrv}),
              w.inst('rectinteqe')], 'syl', eqc)
    ihr0 = sh([ihr, iphi], 'eqtrd', '( %s rectint <. %s , %s >. ) = 0' % (HR, SA, SB))
    # ---- the partial-fraction family ----
    zfin = U('zfin'); zall = U('zall'); ecc = U('ecc'); ecn = U('ecn')
    eex = sh([sh([w.s([], 'cnex', 'CC e. _V')], 'a1i', 'CC e. _V'), ecc], 'ssexd', '%s e. _V' % E_)
    def mk_cc(C, kst, K):
        subq = w.s([w.s([], 'oveq2', '( q = %s -> ( F holord q ) = ( F holord %s ) )' % (K, K))], 'eleq1d', '( q = %s -> ( ( F holord q ) e. NN <-> ( F holord %s ) e. NN ) )' % (K, K))
        return w.s([w.s([subq, up(w, zall, C), kst], 'rspcdva', '( %s -> ( F holord %s ) e. NN )' % (C, K))], 'nncnd', '( %s -> ( F holord %s ) e. CC )' % (C, K))
    def kin(C, kst, K):
        """K e. Z_ gives K e. Q_, K e. CC, K =/= 0"""
        sc = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (C, fm))
        kq = sc([kst, w.inst('elrabi')], 'syl', '%s e. %s' % (K, Q_))
        kcn = sc([up(w, U('qcn'), C), kq], 'sseldd', '%s e. %s' % (K, CN0))
        e2 = sc([kcn, w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (K, CN0, K, K))], 'sylib', '( %s e. CC /\\ %s =/= 0 )' % (K, K))
        return kq, sc([e2, w.inst('simpl')], 'syl', '%s e. CC' % K), sc([e2, w.inst('simpr')], 'syl', '%s =/= 0' % K)
    def gfv(C, kst, K):
        return fvmd(w, C, 'a', Z_, TMq('a'), K, kst, w.s([up(w, eex, C), w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (C, TMq(K))))
    Aj = '( %s /\\ j e. %s )' % (Ah, Z_)
    sj = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Aj, fm))
    jz = sj([], 'simpr', 'j e. %s' % Z_)
    jq, jc, jn0 = kin(Aj, jz, 'j')
    DJ = '( %s \\ { j } )' % CN0
    ejd = sj([sj([up(w, ecn, Aj), sj([jz, w.inst('elndif')], 'syl', '-. j e. %s' % E_)], 'jca', '( %s C_ %s /\\ -. j e. %s )' % (E_, CN0, E_)),
              w.s([], 'ssdifsn', '( %s C_ %s <-> ( %s C_ %s /\\ -. j e. %s ) )' % (E_, DJ, E_, CN0, E_))], 'sylibr', '%s C_ %s' % (E_, DJ))
    TC = tsub(ef2_i.S['ef2tmc'], {'M': '( F holord j )', 'Q': 'j', 'E': E_})
    tca, tcc = ante_of(TC)
    tmc = sj([sj([up(w, yrp, Aj), sj([mk_cc(Aj, jz, 'j'), jc], 'jca', '( ( F holord j ) e. CC /\\ j e. CC )'), ejd], '3jca', tca), w.inst('ef2tmc')], 'syl', tcc)
    gjc = sj([gfv(Aj, jz, 'j'), tmc], 'eqeltrd', '( %s ` j ) e. ( %s -cn-> CC )' % (GF, E_))
    gall = w.s([gjc], 'ralrimiva', '( %s -> A. j e. %s ( %s ` j ) e. ( %s -cn-> CC ) )' % (Ah, Z_, GF, E_))
    Ak = '( %s /\\ k e. %s )' % (Ah, Z_)
    sk = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Ak, fm))
    kz = sk([], 'simpr', 'k e. %s' % Z_)
    subj = w.s([w.s([], 'fveq2', '( j = k -> ( %s ` j ) = ( %s ` k ) )' % (GF, GF))], 'eleq1d', '( j = k -> ( ( %s ` j ) e. ( %s -cn-> CC ) <-> ( %s ` k ) e. ( %s -cn-> CC ) ) )' % (GF, E_, GF, E_))
    gkc = sk([subj, up(w, gall, Ak), kz], 'rspcdva', '( %s ` k ) e. ( %s -cn-> CC )' % (GF, E_))
    gkm = sk([sk([gkc, w.inst('cncff')], 'syl', '( %s ` k ) : %s --> CC' % (GF, E_))], 'feqmptd', '( %s ` k ) = ( b e. %s |-> ( ( %s ` k ) ` b ) )' % (GF, E_, GF))
    gkm2 = sk([gkm, gkc], 'eqeltrrd', '( b e. %s |-> ( ( %s ` k ) ` b ) ) e. ( %s -cn-> CC )' % (E_, GF, E_))
    psic = sh([ecc, zfin, gkm2], 'zl3fsc', '%s e. ( %s -cn-> CC )' % (PSI, E_))
    RS = tsub(ef2_j.S['ef2rsum'], {'P': 'S', 'Q': 'C', 'S': 'L', 'R': 'H', 'K': Z_, 'D': E_, 'G': GF})
    rsa_, rsc_ = ante_of(RS)
    hvr = {'( S e. RR /\\ C e. RR )': U('sc'), '( L e. RR /\\ H e. RR )': U('lh'), '%s e. Fin' % Z_: zfin, '%s C_ CC' % E_: ecc, body_of(w, gall): gall, '%s C_ %s' % (FRX, E_): fxh}
    rsum = sh([conj(w, Ah, rsa_, hvr), w.inst('ef2rsum')], 'syl', rsc_)
    # ---- each term: ef2stk ----
    kq, kc, kn0 = kin(Ak, kz, 'k')
    mkc = mk_cc(Ak, kz, 'k')
    DK = '( %s \\ { k } )' % CN0
    ekd = sk([sk([up(w, ecn, Ak), sk([kz, w.inst('elndif')], 'syl', '-. k e. %s' % E_)], 'jca', '( %s C_ %s /\\ -. k e. %s )' % (E_, CN0, E_)),
              w.s([], 'ssdifsn', '( %s C_ %s <-> ( %s C_ %s /\\ -. k e. %s ) )' % (E_, DK, E_, CN0, E_))], 'sylibr', '%s C_ %s' % (E_, DK))
    INSK = INS('k', SA, SB)
    Akr = '( %s /\\ k e. %s )' % (Ak, R_)
    sr = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Akr, fm))
    e1 = w.s([w.s([], 'fveq2', '( r = k -> ( F ` r ) = ( F ` k ) )')], 'eqeq1d', '( r = k -> ( ( F ` r ) = 0 <-> ( F ` k ) = 0 ) )')
    fk0 = sr([sr([up(w, kz, Akr), w.s([e1], 'elrab', '( k e. %s <-> ( k e. %s /\\ ( F ` k ) = 0 ) )' % (Z_, Q_))], 'sylib', '( k e. %s /\\ ( F ` k ) = 0 )' % Q_), w.inst('simpr')], 'syl', '( F ` k ) = 0')
    idp = w.s([], 'id', '( p = k -> p = k )')
    cp, _ = w.wcongr('( ( F ` p ) = 0 -> %s )' % SIN('p'), {'p': 'k'}, 'p = k', {'p': idp})
    sink = sr([fk0, sr([cp, up(w, U('frh'), Akr), sr([], 'simpr', 'k e. %s' % R_)], 'rspcdva', '( ( F ` k ) = 0 -> %s )' % SIN('k'))], 'mpd', SIN('k'))
    lvr = {kk: up(w, vv, Akr) for kk, vv in f0['lv'].items()}
    kcr = up(w, kc, Akr)
    lvr['( Re ` k )'] = sr([kcr], 'recld', '( Re ` k ) e. RR'); lvr['( Im ` k )'] = sr([kcr], 'imcld', '( Im ` k ) e. RR')
    S1_, S2_ = top_and(SIN('k'))
    s1 = sr([sink, w.inst('simpl')], 'syl', S1_); s2 = sr([sink, w.inst('simpr')], 'syl', S2_)
    hyr = [sr([s1, w.inst('simpl')], 'syl', top_and(S1_)[0]), sr([s1, w.inst('simpr')], 'syl', top_and(S1_)[1]), sr([s2, w.inst('simpl')], 'syl', top_and(S2_)[0]),
           sr([s2, w.inst('simpr')], 'syl', top_and(S2_)[1])] + [up(w, f0[x], Akr) for x in ('rsa', 'isa', 'rsb', 'isb')]
    hvi = {}
    for g in ('( Re ` %s ) < ( Re ` k )' % SA, '( Re ` k ) < ( Re ` %s )' % SB, '( Im ` %s ) < ( Im ` k )' % SA, '( Im ` k ) < ( Im ` %s )' % SB):
        hvi[g] = lin8(w, Akr, hyr, g, lvr)
    insk = w.s([conj(w, Akr, INSK, hvi)], 'ex', '( %s -> ( k e. %s -> %s ) )' % (Ak, R_, INSK))
    ST = tsub(ef2_i.S['ef2stk'], {'A': SA, 'B': SB, 'M': '( F holord k )', 'Q': 'k', 'E': E_})
    sta, stc = ante_of(ST)
    hvs = {'Y e. RR+': up(w, yrp, Ak), '( %s e. CC /\\ %s e. CC )' % (SA, SB): up(w, U('absb'), Ak), '0 < ( Re ` %s )' % SA: up(w, geo[0], Ak),
           '( Re ` %s ) <_ ( Re ` %s )' % (SA, SB): up(w, geo[1], Ak), '( Im ` %s ) <_ ( Im ` %s )' % (SA, SB): up(w, geo[2], Ak), '( F holord k ) e. CC': mkc, 'k e. CC': kc,
           '%s C_ %s' % (E_, DK): ekd, '%s C_ %s' % (FRAB, E_): up(w, feh, Ak), body_of(w, insk): insk}
    stk = sk([conj(w, Ak, sta, hvs), w.inst('ef2stk')], 'syl', stc)
    XK = '( %s x. ( ( F holord k ) x. ( ( Y ^c k ) / k ) ) )' % TPI
    ik = sk([sk([gfv(Ak, kz, 'k')], 'oveq1d', '( ( %s ` k ) rectint <. %s , %s >. ) = ( %s rectint <. %s , %s >. )' % (GF, SA, SB, TMq('k'), SA, SB)), stk], 'eqtrd',
            '( ( %s ` k ) rectint <. %s , %s >. ) = if ( %s , %s , 0 )' % (GF, SA, SB, INSK, XK))
    rules = {'( Re ` %s )' % SA: ('S', up(w, f0['rsa'], Ak)), '( Im ` %s )' % SA: ('L', up(w, f0['isa'], Ak)), '( Re ` %s )' % SB: ('C', up(w, f0['rsb'], Ak)), '( Im ` %s )' % SB: ('H', up(w, f0['isb'], Ak))}
    bi, newi = w.wcongr(INSK, {}, Ak, {}, rules=rules)
    assert newi == SIN('k'), newi
    ik2 = sk([ik, sk([bi], 'ifbid', 'if ( %s , %s , 0 ) = if ( %s , %s , 0 )' % (INSK, XK, SIN('k'), XK))], 'eqtrd', '( ( %s ` k ) rectint <. %s , %s >. ) = if ( %s , %s , 0 )' % (GF, SA, SB, SIN('k'), XK))
    s_if = sh([ik2], 'sumeq2dv', 'sum_ k e. %s ( ( %s ` k ) rectint <. %s , %s >. ) = sum_ k e. %s if ( %s , %s , 0 )' % (Z_, GF, SA, SB, Z_, SIN('k'), XK))
    # sumss2: back to the strict zeros
    AkI = '( %s /\\ k e. %s )' % (Ah, ZIT)
    si = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (AkI, fm))
    kzi = si([si([], 'simpr', 'k e. %s' % ZIT), w.inst('elrabi')], 'syl', 'k e. %s' % Z_)
    kq2, kc2, kn02 = kin(AkI, kzi, 'k')
    tpc = si([si([], '2cnd', '2 e. CC'), si([si([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), si([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    YK = '( ( Y ^c k ) / k )'
    ykc = si([si([si([up(w, yrp, AkI)], 'rpcnd', 'Y e. CC'), kc2], 'cxpcld', '( Y ^c k ) e. CC'), kc2, kn02], 'divcld', '%s e. CC' % YK)
    mykc = si([mk_cc(AkI, kzi, 'k'), ykc], 'mulcld', '( ( F holord k ) x. %s ) e. CC' % YK)
    xkc = si([tpc, mykc], 'mulcld', '%s e. CC' % XK)
    allx = w.s([xkc], 'ralrimiva', '( %s -> A. k e. %s %s e. CC )' % (Ah, ZIT, XK))
    zis = sh([w.s([], 'ssrab2', '%s C_ %s' % (ZIT, Z_))], 'a1i', '%s C_ %s' % (ZIT, Z_))
    orf = sh([zfin], 'olcd', '( %s C_ ( ZZ>= ` 0 ) \\/ %s e. Fin )' % (Z_, Z_))
    SS2 = tsub('( ( ( A C_ B /\\ A. k e. A C e. CC ) /\\ ( B C_ ( ZZ>= ` M ) \\/ B e. Fin ) ) -> sum_ k e. A C = sum_ k e. B if ( k e. A , C , 0 ) )', {'A': ZIT, 'B': Z_, 'C': XK, 'M': '0'})
    ssa, ssc = ante_of(SS2)
    ss2 = sh([sh([sh([zis, allx], 'jca', top_and(ssa)[0]), orf], 'jca', ssa), w.inst('sumss2')], 'syl', ssc)
    idpk = w.s([], 'id', '( p = k -> p = k )')
    cpk, _ = w.wcongr(SIN('p'), {'p': 'k'}, 'p = k', {'p': idpk})
    elr = w.s([cpk], 'elrab', '( k e. %s <-> ( k e. %s /\\ %s ) )' % (ZIT, Z_, SIN('k')))
    bik = sk([sk([kz, w.inst('ibar')], 'syl', '( %s <-> ( k e. %s /\\ %s ) )' % (SIN('k'), Z_, SIN('k'))), sk([elr], 'a1i', '( k e. %s <-> ( k e. %s /\\ %s ) )' % (ZIT, Z_, SIN('k')))], 'bitr4d',
             '( k e. %s <-> %s )' % (ZIT, SIN('k')))
    ifk = sk([bik], 'ifbid', 'if ( k e. %s , %s , 0 ) = if ( %s , %s , 0 )' % (ZIT, XK, SIN('k'), XK))
    sif2 = sh([ifk], 'sumeq2dv', 'sum_ k e. %s if ( k e. %s , %s , 0 ) = sum_ k e. %s if ( %s , %s , 0 )' % (Z_, ZIT, XK, Z_, SIN('k'), XK))
    zif = sh([ss2, sif2], 'eqtrd', 'sum_ k e. %s %s = sum_ k e. %s if ( %s , %s , 0 )' % (ZIT, XK, Z_, SIN('k'), XK))
    tpc_h = sh([sh([], '2cnd', '2 e. CC'), sh([sh([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sh([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    zitf = sh([zfin, zis], 'ssfid', '%s e. Fin' % ZIT)
    MY = '( ( F holord k ) x. %s )' % YK
    fmc = sh([zitf, tpc_h, mykc], 'fsummulc2', '( %s x. sum_ k e. %s %s ) = sum_ k e. %s %s' % (TPI, ZIT, MY, ZIT, XK))
    idkq = w.s([], 'id', '( k = q -> k = q )')
    ckq, _ = w.congr(MY, {'k': 'q'}, 'k = q', {'k': idkq})
    cbs = sh([w.s([ckq], 'cbvsumv', 'sum_ k e. %s %s = sum_ q e. %s ( ( F holord q ) x. ( ( Y ^c q ) / q ) )' % (ZIT, MY, ZIT))], 'a1i',
             'sum_ k e. %s %s = sum_ q e. %s ( ( F holord q ) x. ( ( Y ^c q ) / q ) )' % (ZIT, MY, ZIT))
    RHS = '( %s x. sum_ q e. %s ( ( F holord q ) x. ( ( Y ^c q ) / q ) ) )' % (TPI, ZIT)
    rhs1 = sh([sh([cbs], 'oveq2d', '( %s x. sum_ k e. %s %s ) = %s' % (TPI, ZIT, MY, RHS))], 'eqcomd', '%s = ( %s x. sum_ k e. %s %s )' % (RHS, TPI, ZIT, MY))
    rhs2 = sh([sh([rhs1, fmc], 'eqtrd', '%s = sum_ k e. %s %s' % (RHS, ZIT, XK)), zif], 'eqtrd', '%s = sum_ k e. %s if ( %s , %s , 0 )' % (RHS, Z_, SIN('k'), XK))
    ISUM = 'sum_ k e. %s ( ( %s ` k ) rectint <. %s , %s >. )' % (Z_, GF, SA, SB)
    ipsi = sh([sh([rsum, s_if], 'eqtrd', '( %s rectint <. %s , %s >. ) = sum_ k e. %s if ( %s , %s , 0 )' % (PSI, SA, SB, Z_, SIN('k'), XK)), rhs2], 'eqtr4d',
              '( %s rectint <. %s , %s >. ) = %s' % (PSI, SA, SB, RHS))
    # ---- the pointwise identity on the carrier ----
    Au = '( %s /\\ u e. %s )' % (Ah, E_)
    su = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Au, fm))
    ue = su([], 'simpr', 'u e. %s' % E_)
    ud1 = su([ue, w.inst('eldifi')], 'syl', 'u e. %s' % D1)
    unz = su([ue, w.inst('eldifn')], 'syl', '-. u e. %s' % Z_)
    uq = su([up(w, U('d1q'), Au), ud1], 'sseldd', 'u e. %s' % Q_)
    uhp = su([up(w, U('d1hp'), Au), ud1], 'sseldd', 'u e. %s' % HP0)
    ucn = su([up(w, U('d1cn'), Au), ud1], 'sseldd', 'u e. %s' % CN0)
    uc = su([su([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0), ucn], 'sseldd', 'u e. CC')
    e1u = w.s([w.s([], 'fveq2', '( r = u -> ( F ` r ) = ( F ` u ) )')], 'eqeq1d', '( r = u -> ( ( F ` r ) = 0 <-> ( F ` u ) = 0 ) )')
    Af = '( %s /\\ ( F ` u ) = 0 )' % Au
    uzf = w.s([w.s([up(w, uq, Af), w.s([], 'simpr', '( %s -> ( F ` u ) = 0 )' % Af)], 'jca', '( %s -> ( u e. %s /\\ ( F ` u ) = 0 ) )' % (Af, Q_)),
               w.s([e1u], 'elrab', '( u e. %s <-> ( u e. %s /\\ ( F ` u ) = 0 ) )' % (Z_, Q_))], 'sylibr', '( %s -> u e. %s )' % (Af, Z_))
    fu0 = su([su([uzf, up(w, unz, Af)], 'pm2.65da', '-. ( F ` u ) = 0')], 'neqned', '( F ` u ) =/= 0')
    LDOM = '{ v e. %s | ( F ` v ) =/= 0 }' % HP0
    subv = w.s([w.s([], 'fveq2', '( v = u -> ( F ` v ) = ( F ` u ) )')], 'neeq1d', '( v = u -> ( ( F ` v ) =/= 0 <-> ( F ` u ) =/= 0 ) )')
    uld = su([subv, uhp, fu0], 'elrabd', 'u e. %s' % LDOM)
    QU = '( ( ( CC _D F ) ` u ) / ( F ` u ) )'
    YU = '( ( Y ^c u ) / u )'
    ldv = fvmd(w, Au, 'b', LDOM, '( ( ( ( CC _D F ) ` b ) / ( F ` b ) ) x. ( ( Y ^c b ) / b ) )', 'u', uld, w.s([], 'ovexd', '( %s -> ( %s x. %s ) e. _V )' % (Au, QU, YU)))
    SK = 'sum_ k e. %s ( ( F holord k ) / ( u - k ) )' % Z_
    HQ = '( ( ( CC _D h ) ` u ) / ( h ` u ) )'
    EQz = '( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( sum_ k e. %s ( ( F holord k ) / ( z - k ) ) + ( ( ( CC _D h ) ` z ) / ( h ` z ) ) )' % Z_
    idz = w.s([], 'id', '( z = u -> z = u )')
    cz, newz = w.wcongr(EQz, {'z': 'u'}, 'z = u', {'z': idz})
    ldsu = su([cz, up(w, lds, Au), su([uq, unz], 'eldifd', 'u e. ( %s \\ %s )' % (Q_, Z_))], 'rspcdva', newz)
    pkv = fvmd(w, Au, 'o', CN0, '( ( Y ^c o ) / o )', 'u', ucn, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Au, YU)))
    G_ = '( %s ` u )' % PKF()
    gc = su([su([up(w, pkh, Au), w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PKF(), CN0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (PKF(), CN0))
    gcc = su([gc, ucn], 'ffvelcdmd', '%s e. CC' % G_)
    # per k
    Auk = '( %s /\\ k e. %s )' % (Au, Z_)
    sq_ = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (Auk, fm))
    kz = sq_([], 'simpr', 'k e. %s' % Z_)
    kq, kc, kn0 = kin(Auk, kz, 'k')
    mkc = mk_cc(Auk, kz, 'k')
    uk = sq_([sq_([kz, up(w, unz, Auk)], 'jca', '( k e. %s /\\ -. u e. %s )' % (Z_, Z_)), w.inst('nelne2')], 'syl', 'k =/= u')
    ukn = sq_([up(w, uc, Auk), kc, sq_([uk], 'necomd', 'u =/= k')], 'subne0d', '( u - k ) =/= 0')
    ukc = sq_([up(w, uc, Auk), kc], 'subcld', '( u - k ) e. CC')
    gku = sq_([sq_([gfv(Auk, kz, 'k')], 'fveq1d', '( ( %s ` k ) ` u ) = ( %s ` u )' % (GF, TMq('k'))),
               fvmd(w, Auk, 'd', E_, '( ( F holord k ) x. ( ( %s ` d ) / ( d - k ) ) )' % PKF(), 'u', up(w, ue, Auk),
                    w.s([], 'ovexd', '( %s -> ( ( F holord k ) x. ( %s / ( u - k ) ) ) e. _V )' % (Auk, G_)))], 'eqtrd', '( ( %s ` k ) ` u ) = ( ( F holord k ) x. ( %s / ( u - k ) ) )' % (GF, G_))
    d32 = sq_([mkc, ukc, up(w, gcc, Auk), ukn], 'div32d', '( ( ( F holord k ) / ( u - k ) ) x. %s ) = ( ( F holord k ) x. ( %s / ( u - k ) ) )' % (G_, G_))
    tk = sq_([d32, gku], 'eqtr4d', '( ( ( F holord k ) / ( u - k ) ) x. %s ) = ( ( %s ` k ) ` u )' % (G_, GF))
    tkc = sq_([mkc, ukc, ukn], 'divcld', '( ( F holord k ) / ( u - k ) ) e. CC')
    skc = su([up(w, U('zfin'), Au), tkc], 'fsumcl', '%s e. CC' % SK)
    hdf = sh([hh, w.inst('holf')], 'syl', '( CC _D h ) : %s --> CC' % HP0)
    dhc = su([up(w, hdf, Au), uhp], 'ffvelcdmd', '( ( CC _D h ) ` u ) e. CC')
    subz2 = w.s([w.s([], 'fveq2', '( z = u -> ( h ` z ) = ( h ` u ) )')], 'neeq1d', '( z = u -> ( ( h ` z ) =/= 0 <-> ( h ` u ) =/= 0 ) )')
    hun = su([subz2, up(w, nzq, Au), uq], 'rspcdva', '( h ` u ) =/= 0')
    hucc = fcc(w, Au, up(w, hh, Au), 'h', HP0, 'u', uhp)
    hqc = su([dhc, hucc, hun], 'divcld', '%s e. CC' % HQ)
    psv = fvmd(w, Au, 'b', E_, 'sum_ k e. %s ( ( %s ` k ) ` b )' % (Z_, GF), 'u', ue, su([w.s([], 'sumex', 'sum_ k e. %s ( ( %s ` k ) ` u ) e. _V' % (Z_, GF))], 'a1i',
              'sum_ k e. %s ( ( %s ` k ) ` u ) e. _V' % (Z_, GF)))
    PSU = '( %s ` u )' % PSI
    # the value of the cofactor term
    hr1 = su([ue, w.inst('fvres')], 'syl', '( %s ` u ) = ( %s ` u )' % (HR, PHI))
    M2u = '( %s ` u )' % M2; P1u = '( %s ` u )' % P1
    hr2 = fvmd(w, Au, 'c', D1, '( ( %s ` c ) x. ( %s ` c ) )' % (M2, P1), 'u', ud1, w.s([], 'ovexd', '( %s -> ( %s x. %s ) e. _V )' % (Au, M2u, P1u)))
    F1u = '( %s ` u )' % F1; G1u = '( %s ` u )' % G1
    m2v = fvmd(w, Au, 'e', D1, '( ( %s ` e ) / ( %s ` e ) )' % (F1, G1), 'u', ud1, w.s([], 'ovexd', '( %s -> ( %s / %s ) e. _V )' % (Au, F1u, G1u)))
    f1v = fvmd(w, Au, 'd', D1, '( ( CC _D h ) ` d )', 'u', ud1, w.s([], 'fvexd', '( %s -> ( ( CC _D h ) ` u ) e. _V )' % Au))
    g1v = fvmd(w, Au, 'd', D1, '( h ` d )', 'u', ud1, w.s([], 'fvexd', '( %s -> ( h ` u ) e. _V )' % Au))
    p1v = fvmd(w, Au, 'd', D1, '( %s ` d )' % PKF(), 'u', ud1, w.s([], 'fvexd', '( %s -> %s e. _V )' % (Au, G_)))
    m2e = su([m2v, su([f1v, g1v], 'oveq12d', '( %s / %s ) = %s' % (F1u, G1u, HQ))], 'eqtrd', '%s = %s' % (M2u, HQ))
    hrv_ = su([su([hr1, hr2], 'eqtrd', '( %s ` u ) = ( %s x. %s )' % (HR, M2u, P1u)), su([m2e, p1v], 'oveq12d', '( %s x. %s ) = ( %s x. %s )' % (M2u, P1u, HQ, G_))], 'eqtrd',
              '( %s ` u ) = ( %s x. %s )' % (HR, HQ, G_))
    # the chain
    c1 = su([ldv, su([ldsu], 'oveq1d', '( %s x. %s ) = ( ( %s + %s ) x. %s )' % (QU, YU, SK, HQ, YU))], 'eqtrd', '( %s ` u ) = ( ( %s + %s ) x. %s )' % (LDIB, SK, HQ, YU))
    c2 = su([c1, su([su([pkv], 'eqcomd', '%s = %s' % (YU, G_))], 'oveq2d', '( ( %s + %s ) x. %s ) = ( ( %s + %s ) x. %s )' % (SK, HQ, YU, SK, HQ, G_))], 'eqtrd',
            '( %s ` u ) = ( ( %s + %s ) x. %s )' % (LDIB, SK, HQ, G_))
    c3 = su([c2, su([skc, hqc, gcc], 'adddird', '( ( %s + %s ) x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (SK, HQ, G_, SK, G_, HQ, G_))], 'eqtrd',
            '( %s ` u ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (LDIB, SK, G_, HQ, G_))
    sm = su([up(w, U('zfin'), Au), gcc, tkc], 'fsummulc1', '( %s x. %s ) = sum_ k e. %s ( ( ( F holord k ) / ( u - k ) ) x. %s )' % (SK, G_, Z_, G_))
    sm2 = su([sm, su([tk], 'sumeq2dv', 'sum_ k e. %s ( ( ( F holord k ) / ( u - k ) ) x. %s ) = sum_ k e. %s ( ( %s ` k ) ` u )' % (Z_, G_, Z_, GF))], 'eqtrd',
             '( %s x. %s ) = sum_ k e. %s ( ( %s ` k ) ` u )' % (SK, G_, Z_, GF))
    sm3 = su([sm2, psv], 'eqtr4d', '( %s x. %s ) = %s' % (SK, G_, PSU))
    psc = su([sm3, su([skc, gcc], 'mulcld', '( %s x. %s ) e. CC' % (SK, G_))], 'eqeltrrd', '%s e. CC' % PSU)
    sm4 = su([sm3, su([su([psc], 'mullidd', '( 1 x. %s ) = %s' % (PSU, PSU))], 'eqcomd', '%s = ( 1 x. %s )' % (PSU, PSU))], 'eqtrd', '( %s x. %s ) = ( 1 x. %s )' % (SK, G_, PSU))
    c4 = su([c3, su([sm4, su([hrv_], 'eqcomd', '( %s x. %s ) = ( %s ` u )' % (HQ, G_, HR))], 'oveq12d', '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( 1 x. %s ) + ( %s ` u ) )' % (SK, G_, HQ, G_, PSU, HR))],
            'eqtrd', '( %s ` u ) = ( ( 1 x. %s ) + ( %s ` u ) )' % (LDIB, PSU, HR))
    ptw = w.s([c4], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( ( 1 x. ( %s ` u ) ) + ( %s ` u ) ) )' % (Ah, E_, LDIB, PSI, HR))
    # rectintlce
    hpx = sh([sh([w.s([], 'hpopn', '%s e. %s' % (HP0, K))], 'a1i', '%s e. %s' % (HP0, K)), w.inst('elex')], 'syl', '%s e. _V' % HP0)
    ldx = sh([sh([hpx, w.inst('rabexg')], 'syl', '%s e. _V' % LDOM), w.inst('mptexg')], 'syl', '%s e. _V' % LDIB)
    LC = tsub(stmt('rectintlce'), {'F': LDIB, 'C': '1', 'G': PSI, 'H': HR, 'D': E_, 'E': E_, 'V': '_V', 'A': SA, 'B': SB})
    lca, lcc = ante_of(LC)
    hvl = {'( %s e. CC /\\ %s e. CC )' % (SA, SB): U('absb'), '%s C_ %s' % (FRAB, E_): feh, '%s e. _V' % LDIB: ldx, '1 e. CC': sh([], '1cnd', '1 e. CC'),
           '%s e. ( %s -cn-> CC )' % (PSI, E_): psic, '%s e. ( %s -cn-> CC )' % (HR, E_): hrc, '%s C_ %s' % (E_, E_): sh([w.s([], 'ssid', '%s C_ %s' % (E_, E_))], 'a1i', '%s C_ %s' % (E_, E_)),
           body_of(w, ptw): ptw}
    lce = sh([conj(w, Ah, lca, hvl), w.inst('rectintlce')], 'syl', lcc)
    IPS = '( %s rectint <. %s , %s >. )' % (PSI, SA, SB); IHR = '( %s rectint <. %s , %s >. )' % (HR, SA, SB)
    ILB = '( %s rectint <. %s , %s >. )' % (LDIB, SA, SB)
    MYq = '( ( F holord q ) x. ( ( Y ^c q ) / q ) )'
    sumk = sh([zitf, mykc], 'fsumcl', 'sum_ k e. %s %s e. CC' % (ZIT, MY))
    sumq = sh([cbs, sumk], 'eqeltrrd', 'sum_ q e. %s %s e. CC' % (ZIT, MYq))
    rhc = sh([tpc_h, sumq], 'mulcld', '%s e. CC' % RHS)
    a1 = sh([lce, sh([sh([ipsi], 'oveq2d', '( 1 x. %s ) = ( 1 x. %s )' % (IPS, RHS)), ihr0], 'oveq12d', '( ( 1 x. %s ) + %s ) = ( ( 1 x. %s ) + 0 )' % (IPS, IHR, RHS))], 'eqtrd',
            '%s = ( ( 1 x. %s ) + 0 )' % (ILB, RHS))
    a2 = sh([a1, sh([sh([sh([rhc], 'mullidd', '( 1 x. %s ) = %s' % (RHS, RHS))], 'oveq1d', '( ( 1 x. %s ) + 0 ) = ( %s + 0 )' % (RHS, RHS)), sh([rhc], 'addridd', '( %s + 0 ) = %s' % (RHS, RHS))], 'eqtrd',
                        '( ( 1 x. %s ) + 0 ) = %s' % (RHS, RHS))], 'eqtrd', '%s = %s' % (ILB, RHS))
    idub = w.s([], 'id', '( u = b -> u = b )')
    LBODY = '( ( ( ( CC _D F ) ` u ) / ( F ` u ) ) x. ( ( Y ^c u ) / u ) )'
    cub, _ = w.congr(LBODY, {'u': 'b'}, 'u = b', {'u': idub})
    lq = w.s([w.s([cub], 'cbvmptv', '%s = %s' % (LDI(), LDIB))], 'oveq1i', '( %s rectint <. %s , %s >. ) = %s' % (LDI(), SA, SB, ILB))
    fin_ = sh([sh([lq], 'a1i', '( %s rectint <. %s , %s >. ) = %s' % (LDI(), SA, SB, ILB)), a2], 'eqtrd', GC)
    ex_ = w.s([fin_], 'ex', '( %s -> ( %s -> %s ) )' % (A0, HB, GC))
    w.qed([exh, w.s([ex_], 'exlimdv', '( %s -> ( E. h %s -> %s ) )' % (A0, HB, GC))], 'mpd', S['ef2stc'])
    return run8(w)


def gen_strip():
    w = W('ef2strip', 'Lean ` rectInt_strip ` on squares: over a strip ` [ S , C ] x. [ L , H ] ` of height at most 1 with ` 9 / 16 <_ S < C <_ 5 / 4 ` , if the zeros of the ` DiskData ` function ` F ` in the closed rectangle are strictly inside, the boundary integral of ` ( F-prime / F ) ( s ) y ^ s / s ` is ` 2 pi i ` times the sum of ` m_rho y ^ rho / rho ` over the square zeros about the mid-height that lie strictly inside ( ~ ef2stc at ` T = ( L + H ) / 2 ` ).')
    A0, GC = ante_of(S['ef2strip'])
    s = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (A0, fm))
    dd = s([], 'simp1', DD()); sh_ = s([], 'simp2', ef2lib_SH); frh = s([], 'simp3', FRH_)
    Y1, Y2, Y3 = top_and(ef2lib_SH)
    y1 = s([sh_, w.inst('simp1')], 'syl', Y1); y2 = s([sh_, w.inst('simp2')], 'syl', Y2); y3 = s([sh_, w.inst('simp3')], 'syl', Y3)
    sc = s([y2, w.inst('simpl')], 'syl', '( S e. RR /\\ C e. RR )'); sci = s([y2, w.inst('simpr')], 'syl', top_and(Y2)[1])
    lh = s([y3, w.inst('simpl')], 'syl', '( L e. RR /\\ H e. RR )'); lhi = s([y3, w.inst('simpr')], 'syl', top_and(Y3)[1])
    rl = {k: s([st, w.inst(r)], 'syl', '%s e. RR' % k) for k, st, r in (('S', sc, 'simpl'), ('C', sc, 'simpr'), ('L', lh, 'simpl'), ('H', lh, 'simpr'))}
    hy = [s([sci, w.inst(k)], 'syl', p) for k, p in zip(('simp1', 'simp2', 'simp3'), top_and(top_and(Y2)[1]))]
    hy += [s([lhi, w.inst(k)], 'syl', p) for k, p in zip(('simpl', 'simpr'), top_and(top_and(Y3)[1]))]
    TAU_ = '( ( L + H ) / 2 )'
    tr = s([s([rl['L'], rl['H']], 'readdcld', '( L + H ) e. RR'), numst(w, A0, '2', 'RR'), s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')], 'redivcld', '%s e. RR' % TAU_)
    ST = tsub(S['ef2stc'], {'T': TAU_})
    sta, stc = ante_of(ST)
    lv = dict(rl)
    have = {DD(): dd, '%s e. RR' % TAU_: tr, Y1: y1, '( S e. RR /\\ C e. RR )': sc, '( L e. RR /\\ H e. RR )': lh, FRH_: frh}
    for g in ('( 3 / 8 ) < S', 'S < C', 'C < ( ; 2 9 / 8 )', '( %s - %s ) < L' % (TAU_, R138), 'L < H', 'H < ( %s + %s )' % (TAU_, R138)):
        have[g] = lin8(w, A0, hy, g, lv)
    w.qed([conj(w, A0, sta, have), w.s([], 'ef2stc', ST)], 'syl', S['ef2strip'])
    return run8(w)


ef2lib_SH = SH_ = __import__('ef2lib').SH


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2stc', 'ef2strip']:
        {'ef2stc': gen_stc, 'ef2strip': gen_strip}[g]()
