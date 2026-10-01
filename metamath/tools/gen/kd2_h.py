"""Sortie KD2: kderiv_detection assembly (kd2da, kd2db, kd2det).  MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_h.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from kd2lib import *
from cl import formula_of, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, nlinarith
from mvlib import ringeq, ringeqp
import num

only = sys.argv[1:]
LY = '( log ` Y )'
ND = NDET('E', LY); MD = MDET('E', LY)


def prelude(w, A, a0, noz=False):
    """facts from a0 : ( A -> A0H ) (A0B with noz)"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    g1 = d('simpld', [a0], '( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( N <_ Y /\\ ( ( abs ` T ) + 2 ) <_ Y ) )' % CHI)
    if noz:
        g2 = d('simprd', [a0], '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) )' % (R5000, LY))
    else:
        g2 = d('simprd', [a0], '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ E. p e. CC ( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E ) )' % (R5000, LY, LFN, ONE('T')))
    chi = d('simp1d', [g1], CHI); ty_ = d('simp2d', [g1], '( T e. RR /\\ Y e. RR )'); ny_ = d('simp3d', [g1], '( N <_ Y /\\ ( ( abs ` T ) + 2 ) <_ Y )')
    tr = d('simpld', [ty_], 'T e. RR'); yr = d('simprd', [ty_], 'Y e. RR'); ny = d('simpld', [ny_], 'N <_ Y'); tyy = d('simprd', [ny_], '( ( abs ` T ) + 2 ) <_ Y')
    if noz:
        ee = d('simpld', [g2], '( E e. RR+ /\\ E <_ %s )' % R5000); h12 = d('simprd', [g2], '1 <_ ( ( ; 1 2 x. E ) x. %s )' % LY); hz = None
    else:
        ee = d('simp1d', [g2], '( E e. RR+ /\\ E <_ %s )' % R5000); h12 = d('simp2d', [g2], '1 <_ ( ( ; 1 2 x. E ) x. %s )' % LY)
        hz = d('simp3d', [g2], 'E. p e. CC ( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E )' % (LFN, ONE('T')))
    ep = d('simpld', [ee], 'E e. RR+'); e5 = d('simprd', [ee], 'E <_ %s' % R5000)
    er = d('rpred', [ep], 'E e. RR'); e0 = d('rpge0d', [ep], '0 <_ E')
    nn = d('simpld', [d('simpld', [chi], NXH)], 'N e. NN'); nr = d('nnred', [nn], 'N e. RR')
    cly = Closure(w, A, {'N': ('RR', nr), 'Y': ('RR', yr)})
    y1 = linarith(w, A, [ny, d('nnge1d', [nn], '1 <_ N')], '1 <_ Y', closure=cly)
    yp = d('elrpd', [yr, linarith(w, A, [y1], '0 < Y', closure=cly)], 'Y e. RR+')
    lr = d('relogcld', [yp], '%s e. RR' % LY); l0 = d('logge0d', [yr, y1], '0 <_ %s' % LY)
    at = d('abscld', [d('recnd', [tr], 'T e. CC')], '( abs ` T ) e. RR'); at0 = d('absge0d', [d('recnd', [tr], 'T e. CC')], '0 <_ ( abs ` T )')
    T2 = '( ( abs ` T ) + 2 )'
    t2r = d('readdcld', [at, a1(w, A, '2re', '2 e. RR')], '%s e. RR' % T2)
    cla = Closure(w, A, {'( abs ` T )': ('RR', at)}); cla.atom('( abs ` T )')
    t2p = d('elrpd', [t2r, linarith(w, A, [at0], '0 < %s' % T2, closure=cla)], '%s e. RR+' % T2)
    NT = '( N x. %s )' % T2
    mm = d('lemul12ad', [nr, yr, t2r, yr, d('nn0ge0d', [d('nnnn0d', [nn], 'N e. NN0')], '0 <_ N'), d('rpge0d', [t2p], '0 <_ %s' % T2), ny, tyy], '%s <_ ( Y x. Y )' % NT)
    ntp = d('rpmulcld', [d('nnrpd', [nn], 'N e. RR+'), t2p], '%s e. RR+' % NT)
    lx = d('mpbid', [mm, d('logled', [ntp, d('rpmulcld', [yp, yp], '( Y x. Y ) e. RR+')], '( %s <_ ( Y x. Y ) <-> %s <_ ( log ` ( Y x. Y ) ) )' % (NT, LOGX))], '%s <_ ( log ` ( Y x. Y ) )' % LOGX)
    lx2 = d('breqtrd', [lx, d('relogmuld', [yp, yp], '( log ` ( Y x. Y ) ) = ( %s + %s )' % (LY, LY))], '%s <_ ( %s + %s )' % (LOGX, LY, LY))
    lxr = d('relogcld', [ntp], '%s e. RR' % LOGX)
    lx0 = d('logge0d', [d('rpred', [ntp], '%s e. RR' % NT), d('lemul12ad' if False else 'mulge1d' if False else 'idi', [], 'T.') if False else
                        linarith(w, A, [d('lemul12ad', [a1(w, A, '1re', '1 e. RR'), nr, a1(w, A, '1re', '1 e. RR'), t2r, a1(w, A, '0le1', '0 <_ 1'), a1(w, A, '0le1', '0 <_ 1'), d('nnge1d', [nn], '1 <_ N'),
                                                         linarith(w, A, [at0], '1 <_ %s' % T2, closure=cla)], '( 1 x. 1 ) <_ %s' % NT), a1(w, A, '1t1e1', '( 1 x. 1 ) = 1')],
                                 '1 <_ %s' % NT, closure=Closure(w, A, {NT: ('RR', d('rpred', [ntp], '%s e. RR' % NT))}) if False else None) if False else
                        d('eqbrtrrd', [a1(w, A, '1t1e1', '( 1 x. 1 ) = 1'), d('lemul12ad', [a1(w, A, '1re', '1 e. RR'), nr, a1(w, A, '1re', '1 e. RR'), t2r, a1(w, A, '0le1', '0 <_ 1'), a1(w, A, '0le1', '0 <_ 1'),
                                                                                        d('nnge1d', [nn], '1 <_ N'), linarith(w, A, [at0], '1 <_ %s' % T2, closure=cla)], '( 1 x. 1 ) <_ %s' % NT)], '1 <_ %s' % NT)],
             '0 <_ %s' % LOGX)
    nd_ = use(w, A, 'kdndet', {'L': LY}, d('jca', [d('jca', [er, e0], '( E e. RR /\\ 0 <_ E )'), d('jca', [lr, l0], '( %s e. RR /\\ 0 <_ %s )' % (LY, LY))], '( ( E e. RR /\\ 0 <_ E ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (LY, LY)))
    ndn = d('simp1d', [nd_], '%s e. NN' % ND)
    ndl = d('simpld', [d('simp3d', [nd_], '( ( 6 + ( ( %s x. E ) x. %s ) ) <_ %s /\\ %s < ( 7 + ( ( %s x. E ) x. %s ) ) )' % (C8E8, LY, ND, ND, C8E8, LY))], '( 6 + ( ( %s x. E ) x. %s ) ) <_ %s' % (C8E8, LY, ND))
    ndr = d('nnred', [ndn], '%s e. RR' % ND)
    cln = Closure(w, A, {'E': ('RR', er), LY: ('RR', lr), ND: ('RR', ndr)}); cln.atom(LY); cln.atom(ND)
    ndbig = nlinarith(w, A, [ndl, h12], '; ; ; ; ; ; ; 7 0 0 0 0 0 0 6 <_ %s' % ND, closure=cln)
    return dict(chi=chi, tr=tr, yr=yr, yp=yp, y1=y1, ep=ep, e5=e5, er=er, e0=e0, h12=h12, hz=hz, nn=nn, lr=lr, l0=l0, lx2=lx2, lxr=lxr, lx0=lx0, ndn=ndn, ndl=ndl, ndr=ndr, ndbig=ndbig)


def gen_dA():
    w = W('kd2da', 'Section 4.4 step 3 at the headline constants: the Turan floor ` Q ` at Ndet gives ` (j+1)! ( 3 / 4 ) Q <_ abs LSK ( j + 1 , s0 ) ` ( ~ kd2lsb with ~ kd2bfar , ~ kd2bcau ; ` KL <_ 35000000 L ` from ` log ( N ( abs T + 2 ) ) <_ 2 log Y ` ).')
    A0 = S['kd2da'].split(' -> ( ( ! `')[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    a0 = d('simpl', [], A0H)
    P = prelude(w, A0, a0)
    hj = d('simpr', [], '( J e. NN0 /\\ ( ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) /\\ ( J + 2 ) <_ ( 7 x. %s ) ) /\\ %s <_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ ( J + 2 ) ) ) ) )' % (ND, ND, QJ, Z6, MU(), S0()))
    jn = d('simp1d', [hj], 'J e. NN0'); rg = d('simp2d', [hj], '( ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) /\\ ( J + 2 ) <_ ( 7 x. %s ) )' % (ND, ND))
    r1 = d('simpld', [rg], '( ( 6 x. %s ) + 1 ) <_ ( J + 2 )' % ND)
    hq = d('simp3d', [hj], '%s <_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ ( J + 2 ) ) ) )' % (QJ, Z6, MU(), S0()))
    clk = Closure(w, A0, {LOGX: ('RR', P['lxr']), LY: ('RR', P['lr'])}); clk.atom(LOGX); clk.atom(LY)
    klr = clk.mem(KL, 'RR')
    kl35 = linarith(w, A0, [P['lx2']], '%s <_ ( %s x. %s )' % (KL, C35, LY), closure=clk)
    kl0 = linarith(w, A0, [P['lx0']], '0 <_ %s' % KL, closure=clk)
    BHs = d('3jca', [d('jca', [P['ep'], P['e5']], '( E e. RR+ /\\ E <_ %s )' % R5000), d('jca', [P['ndn'], jn], '( %s e. NN /\\ J e. NN0 )' % ND), r1],
            '( ( E e. RR+ /\\ E <_ %s ) /\\ ( %s e. NN /\\ J e. NN0 ) /\\ ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) )' % (R5000, ND, ND))
    LHs = d('jca', [d('jca', [P['lr'], P['l0']], '( %s e. RR /\\ 0 <_ %s )' % (LY, LY)), P['ndl']], '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( 6 + ( ( %s x. E ) x. %s ) ) <_ %s )' % (LY, LY, C8E8, LY, ND))
    cln = Closure(w, A0, {ND: ('RR', P['ndr'])}); cln.atom(ND)
    n49 = linarith(w, A0, [P['ndbig']], '; 4 9 <_ %s' % ND, closure=cln)
    sub = {'N': ND, 'L': LY, 'C': KL}
    bf = use(w, A0, 'kd2bfar', sub, d('3jca', [BHs, d('jca', [LHs, n49], '( %s /\\ ; 4 9 <_ %s )' % (formula_of(w, LHs).split(' -> ', 1)[1][:-2], ND)), d('jca', [klr, kl35], '( %s e. RR /\\ %s <_ ( %s x. %s ) )' % (KL, KL, C35, LY))],
                                     inst_stmt('kd2bfar', sub)[0]))
    bc = use(w, A0, 'kd2bcau', sub, d('3jca', [BHs, LHs, d('3jca', [klr, kl0, kl35], '( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( %s x. %s ) )' % (KL, KL, KL, C35, LY))], inst_stmt('kd2bcau', sub)[0]))
    clq = Closure(w, A0, {'E': ('RR+', P['ep']), ND: ('NN', P['ndn']), 'J': ('NN0', jn)}); clq.atom(ND)
    tp = d('simpli' if False else 'idi', [], 'T.') if False else None
    t = w.s([], 'kd2tc', S['kd2tc'])
    clq.leaf(C56E, 'RR+', w.s([w.s([t], 'simpli', '%s e. RR+' % C56E)], 'a1i', '( %s -> %s e. RR+ )' % (A0, C56E))); clq.atom(C56E)
    qr = clq.mem(QJ, 'RR')
    cl20 = Closure(w, A0, {'E': ('RR', P['er'])})
    e20 = linarith(w, A0, [P['e5']], 'E <_ %s' % R120, closure=cl20)
    lsb = use(w, A0, 'kd2lsb', {'Q': QJ}, d('jca', [d('jca', [P['chi'], d('3jca', [P['tr'], P['ep'], e20], '( T e. RR /\\ E e. RR+ /\\ E <_ %s )' % R120)], '( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ %s ) )' % (CHI, R120)),
                                                     d('jca', [d('jca', [jn, qr], '( J e. NN0 /\\ %s e. RR )' % QJ), d('3jca', [hq, bf, bc], '( %s <_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ ( J + 2 ) ) ) ) /\\ %s <_ ( %s / 8 ) /\\ %s <_ ( %s / 8 ) )' % (QJ, Z6, MU(), S0(), FAR(KL), QJ, CAU(KL), QJ))],
                                                       '( ( J e. NN0 /\\ %s e. RR ) /\\ ( %s <_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ ( J + 2 ) ) ) ) /\\ %s <_ ( %s / 8 ) /\\ %s <_ ( %s / 8 ) ) )' % (QJ, QJ, Z6, MU(), S0(), FAR(KL), QJ, CAU(KL), QJ))],
                                                  inst_stmt('kd2lsb', {'Q': QJ})[0]))
    w.qed([lsb], 'idi', S['kd2da'])
    return only_run(w, only)


def gen_dB():
    w = W('kd2db', 'Section 4.4 steps 4-5 at the headline constants: the three tails ( ~ kd2sub with ~ kd2bpp , ~ kd2blow , ~ kd2bhigh ), the Abel boundary ( ~ kd2abel , ~ kd2wb , ~ kd2bbd ) and the endgame ( ~ kd2am , ~ kd2kb , ~ kd2ibl , ~ kd2bend ).')
    A0 = S['kd2db'].split(' -> ' + FINAL)[0][2:]
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    a0 = d('simpl', [], A0B)
    P = prelude(w, A0, a0, noz=True)
    ep, er, e5, tr, chi = P['ep'], P['er'], P['e5'], P['tr'], P['chi']
    nxh = d('simpld', [chi], NXH)
    hj = d('simpr', [], HJB)
    jn = d('simp1d', [hj], 'J e. NN0'); rg = d('simp2d', [hj], '( ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) /\\ ( J + 2 ) <_ ( 7 x. %s ) )' % (ND, ND))
    r1 = d('simpld', [rg], '( ( 6 x. %s ) + 1 ) <_ ( J + 2 )' % ND); r2 = d('simprd', [rg], '( J + 2 ) <_ ( 7 x. %s )' % ND)
    LS = LSK('( J + 1 )', S0())
    hls = d('simp3d', [hj], '( %s x. ( ( 3 / 4 ) x. %s ) ) <_ ( abs ` %s )' % (FJ, QJ, LS))
    ndn, ndr = P['ndn'], P['ndr']
    j1 = d('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    fnn = d('faccld', [j1], '%s e. NN' % FJ)
    t = w.s([], 'kd2tc', S['kd2tc'])
    tcp = w.s([w.s([t], 'simpli', '%s e. RR+' % C56E)], 'a1i', '( %s -> %s e. RR+ )' % (A0, C56E))
    cl = Closure(w, A0, {'E': ('RR+', ep), ND: ('NN', ndn), 'J': ('NN0', jn), '( J + 1 )': ('NN0', j1), C56E: ('RR+', tcp)})
    cl.atom(ND); cl.atom(C56E)
    cl.leaf(FJ, 'RR+', d('nnrpd', [fnn], '%s e. RR+' % FJ))
    e1p = d('syl', [a1(w, A0, '1re', '1 e. RR'), w.inst('rpefcl')], '( exp ` 1 ) e. RR+')
    cl.leaf('( exp ` 1 )', 'RR+', e1p)
    qr = cl.mem(QJ, 'RR'); qp = cl.mem(QJ, 'RR+')
    Q8J = '( %s / 8 )' % QJ; FQ8J = '( %s x. %s )' % (FJ, Q8J)
    # X1, X2
    MDr = cl.mem(MD, 'RR')
    RR_ = '( %s / E )' % MD
    rrp = d('rpdivcld', [cl.mem(MD, 'RR+'), ep], '%s e. RR+' % RR_)
    cl.leaf(RR_, 'RR+', rrp)
    Aa = '( %s / ( ; 1 6 x. E ) )' % MD; Bb = '( ( ; 1 6 x. %s ) / E )' % MD
    ae = d('eqtr4d', [d('oveq2d', [d('mulcomd', [a1(w, A0, None, None)] if False else [w.s([num.cc(w, '; 1 6')], 'a1i', '( %s -> ; 1 6 e. CC )' % A0), d('rpcnd', [ep], 'E e. CC')], '( ; 1 6 x. E ) = ( E x. ; 1 6 )')],
                                  '%s = ( %s / ( E x. ; 1 6 ) )' % (Aa, MD)),
                      d('divdiv1d', [cl.mem(MD, 'CC'), d('rpcnd', [ep], 'E e. CC'), w.s([num.cc(w, '; 1 6')], 'a1i', '( %s -> ; 1 6 e. CC )' % A0), d('rpne0d', [ep], 'E =/= 0'), w.s([num.ne0_nat(w, 16)], 'a1i', '( %s -> ; 1 6 =/= 0 )' % A0)],
                        '( %s / ; 1 6 ) = ( %s / ( E x. ; 1 6 ) )' % (RR_, MD))], '%s = ( %s / ; 1 6 )' % (Aa, RR_))
    be = d('divassd', [w.s([num.cc(w, '; 1 6')], 'a1i', '( %s -> ; 1 6 e. CC )' % A0), cl.mem(MD, 'CC'), d('rpcnd', [ep], 'E e. CC'), d('rpne0d', [ep], 'E =/= 0')], '%s = ( ; 1 6 x. %s )' % (Bb, RR_))
    ar = cl.mem(Aa, 'RR'); br = cl.mem(Bb, 'RR')
    clr = Closure(w, A0, {RR_: ('RR', d('rpred', [rrp], '%s e. RR' % RR_)), Aa: ('RR', ar), Bb: ('RR', br)}); 
    for a in (RR_, Aa, Bb):
        clr.atom(a)
    a0_ = linarith(w, A0, [ae, d('rpge0d', [rrp], '0 <_ %s' % RR_)], '0 <_ %s' % Aa, closure=clr)
    ab_ = linarith(w, A0, [ae, be, d('rpge0d', [rrp], '0 <_ %s' % RR_)], '%s <_ %s' % (Aa, Bb), closure=clr)
    X1, X2 = XO_, XT_
    x1p = d('rpefcld', [ar], '%s e. RR+' % X1); x2p = d('rpefcld', [br], '%s e. RR+' % X2)
    x1r = d('rpred', [x1p], '%s e. RR' % X1); x2r = d('rpred', [x2p], '%s e. RR' % X2)
    ef0 = a1(w, A0, 'ef0', '( exp ` 0 ) = 1')
    x11 = d('breqtrrd' if False else 'eqbrtrrd', [ef0, d('mpbid', [a0_, d('syl2anc', [a1(w, A0, '0re', '0 e. RR'), ar, w.inst('efle')], '( 0 <_ %s <-> ( exp ` 0 ) <_ %s )' % (Aa, X1))], '( exp ` 0 ) <_ %s' % X1)],
            '1 <_ %s' % X1)
    x12 = d('mpbid', [ab_, d('syl2anc', [ar, br, w.inst('efle')], '( %s <_ %s <-> %s <_ %s )' % (Aa, Bb, X1, X2))], '%s <_ %s' % (X1, X2))
    l1 = d('relogefd', [ar], '( log ` %s ) = %s' % (X1, Aa)); l2 = d('relogefd', [br], '( log ` %s ) = %s' % (X2, Bb))
    # E . R = MD
    erd = d('divcan2d', [cl.mem(MD, 'CC'), d('rpcnd', [ep], 'E e. CC'), d('rpne0d', [ep], 'E =/= 0')], '( E x. %s ) = %s' % (RR_, MD))
    cln = Closure(w, A0, {'E': ('RR', er), ND: ('RR', ndr), RR_: ('RR', d('rpred', [rrp], '%s e. RR' % RR_)), Bb: ('RR', br)})
    for a in (ND, RR_, Bb):
        cln.atom(a)
    b20 = nlinarith(w, A0, [be, erd, e5, P['ndbig'], d('rpge0d', [rrp], '0 <_ %s' % RR_)], '; 2 0 <_ %s' % Bb, closure=cln)
    e20 = d('mpbid', [b20, d('syl2anc', [w.s([num.real(w, '; 2 0')], 'a1i', '( %s -> ; 2 0 e. RR )' % A0), br, w.inst('efle')], '( ; 2 0 <_ %s <-> ( exp ` ; 2 0 ) <_ %s )' % (Bb, X2))],
             '( exp ` ; 2 0 ) <_ %s' % X2)
    # tails
    e120 = linarith(w, A0, [e5], 'E <_ %s' % R120, closure=Closure(w, A0, {'E': ('RR', er)}))
    sb = use(w, A0, 'kd2sub', {'Y': X1, 'Z': X2},
             d('3jca', [nxh, d('3jca', [tr, ep, e120], '( T e. RR /\\ E e. RR+ /\\ E <_ %s )' % R120),
                        d('3jca', [d('jca', [x1r, x11], '( %s e. RR /\\ 1 <_ %s )' % (X1, X1)), d('jca', [x2r, x12], '( %s e. RR /\\ %s <_ %s )' % (X2, X1, X2)), jn],
                          '( ( %s e. RR /\\ 1 <_ %s ) /\\ ( %s e. RR /\\ %s <_ %s ) /\\ J e. NN0 )' % (X1, X1, X2, X1, X2))],
               inst_stmt('kd2sub', {'Y': X1, 'Z': X2})[0]))
    BHs = d('3jca', [d('jca', [ep, e5], '( E e. RR+ /\\ E <_ %s )' % R5000), d('jca', [ndn, jn], '( %s e. NN /\\ J e. NN0 )' % ND), r1],
            '( ( E e. RR+ /\\ E <_ %s ) /\\ ( %s e. NN /\\ J e. NN0 ) /\\ ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) )' % (R5000, ND, ND))
    cln2 = Closure(w, A0, {ND: ('RR', ndr)}); cln2.atom(ND)
    HHs = d('3jca', [ep, d('jca', [ndn, jn], '( %s e. NN /\\ J e. NN0 )' % ND), r2], '( E e. RR+ /\\ ( %s e. NN /\\ J e. NN0 ) /\\ ( J + 2 ) <_ ( 7 x. %s ) )' % (ND, ND))
    bpp = use(w, A0, 'kd2bpp', {'N': ND}, BHs)
    blow = use(w, A0, 'kd2blow', {'N': ND}, d('jca', [BHs, linarith(w, A0, [P['ndbig']], '5 <_ %s' % ND, closure=cln2)], '( %s /\\ 5 <_ %s )' % (formula_of(w, BHs).split(' -> ', 1)[1][:-2], ND)))
    bhigh = use(w, A0, 'kd2bhigh', {'N': ND}, HHs)
    bbd = use(w, A0, 'kd2bbd', {'N': ND}, d('jca', [BHs, r2], '( %s /\\ ( J + 2 ) <_ ( 7 x. %s ) )' % (formula_of(w, BHs).split(' -> ', 1)[1][:-2], ND)))
    bend = use(w, A0, 'kd2bend', {'N': ND}, d('jca', [HHs, linarith(w, A0, [P['ndbig']], '; ; ; ; 7 3 9 8 4 <_ %s' % ND, closure=cln2)], '( %s /\\ ; ; ; ; 7 3 9 8 4 <_ %s )' % (formula_of(w, HHs).split(' -> ', 1)[1][:-2], ND)))
    from kd2_e import psmem, cpcc
    F = FJ; K1 = '( J + 1 )'
    B54 = '( ( ( 5 / 4 ) / E ) + 5 )'
    DG = DG2(K1, '( E / 2 )')
    T1_ = '( ; 2 0 x. ( ( 4 ^ %s ) x. %s ) )' % (K1, F)
    T2_ = '( ( ( log ` %s ) ^ %s ) x. %s )' % (X1, K1, B54)
    ZE = '( %s ^c -u ( E / 2 ) )' % X2
    T3_ = '( %s x. %s )' % (ZE, DG)
    q8r = cl.mem(Q8J, 'RR'); fr = cl.mem(F, 'RR'); f0 = cl.ge0(F)
    b1 = d('lemul2ad', [cl.mem('( ; 2 0 x. ( 4 ^ %s ) )' % K1, 'RR'), q8r, fr, f0, bpp], '( %s x. ( ; 2 0 x. ( 4 ^ %s ) ) ) <_ %s' % (F, K1, FQ8J))
    cl4 = Closure(w, A0, {F: ('CC', cl.mem(F, 'CC')), '( 4 ^ %s )' % K1: ('CC', cl.mem('( 4 ^ %s )' % K1, 'CC'))}); cl4.atom(F); cl4.atom('( 4 ^ %s )' % K1)
    t1 = d('eqbrtrrd', [ringeq(w, A0, '( %s x. ( ; 2 0 x. ( 4 ^ %s ) ) )' % (F, K1), T1_, cl4), b1], '%s <_ %s' % (T1_, FQ8J))
    t2 = d('eqbrtrd', [d('oveq1d', [d('oveq1d', [l1], '( ( log ` %s ) ^ %s ) = ( %s ^ %s )' % (X1, K1, Aa, K1))], '%s = ( ( %s ^ %s ) x. %s )' % (T2_, Aa, K1, B54)), blow], '%s <_ %s' % (T2_, FQ8J))
    x2c = d('rpcnd', [x2p], '%s e. CC' % X2); x2n = d('rpne0d', [x2p], '%s =/= 0' % X2)
    ze1 = d('cxpefd', [x2c, x2n, d('negcld', [d('rpcnd', [d('rphalfcld', [ep], '( E / 2 ) e. RR+')], '( E / 2 ) e. CC')], '-u ( E / 2 ) e. CC')], '%s = ( exp ` ( -u ( E / 2 ) x. ( log ` %s ) ) )' % (ZE, X2))
    cle = Closure(w, A0, {'E': ('CC', d('rpcnd', [ep], 'E e. CC')), RR_: ('CC', d('rpcnd', [rrp], '%s e. CC' % RR_)), MD: ('CC', cl.mem(MD, 'CC'))}); cle.atom(RR_); cle.atom(MD)
    x_ = ringeq(w, A0, '( -u ( E / 2 ) x. ( ; 1 6 x. %s ) )' % RR_, '-u ( 8 x. ( E x. %s ) )' % RR_, cle)
    x3 = chain(w, A0, ['( -u ( E / 2 ) x. ( log ` %s ) )' % X2, '( -u ( E / 2 ) x. %s )' % Bb, '( -u ( E / 2 ) x. ( ; 1 6 x. %s ) )' % RR_, '-u ( 8 x. ( E x. %s ) )' % RR_, '-u ( 8 x. %s )' % MD],
               [d('oveq2d', [l2], '( -u ( E / 2 ) x. ( log ` %s ) ) = ( -u ( E / 2 ) x. %s )' % (X2, Bb)), d('oveq2d', [be], '( -u ( E / 2 ) x. %s ) = ( -u ( E / 2 ) x. ( ; 1 6 x. %s ) )' % (Bb, RR_)), x_,
                d('negeqd', [d('oveq2d', [erd], '( 8 x. ( E x. %s ) ) = ( 8 x. %s )' % (RR_, MD))], '-u ( 8 x. ( E x. %s ) ) = -u ( 8 x. %s )' % (RR_, MD))])
    zee = d('eqtrd', [ze1, d('fveq2d', [x3], '( exp ` ( -u ( E / 2 ) x. ( log ` %s ) ) ) = ( exp ` -u ( 8 x. %s ) )' % (X2, MD))], '%s = ( exp ` -u ( 8 x. %s ) )' % (ZE, MD))
    t3 = d('eqbrtrd', [d('oveq1d', [zee], '%s = ( ( exp ` -u ( 8 x. %s ) ) x. %s )' % (T3_, MD, DG)), bhigh], '%s <_ %s' % (T3_, FQ8J))
    TLx = '( ( %s + %s ) + %s )' % (T1_, T2_, T3_)
    # |DW| lower bound
    DW = DWIN('J', X1, X2)
    LSc = use(w, A0, 'kd2lscl', {'K': K1, 'S': S0()}, d('3jca', [nxh, d('jca', [ep, linarith(w, A0, [e5], 'E <_ 1', closure=Closure(w, A0, {'E': ('RR', er)}))], '( E e. RR+ /\\ E <_ 1 )'),
                                                          d('3jca', [d('addcld', [d('recnd', [d('readdcld', [a1(w, A0, '1re', '1 e. RR'), er], '( 1 + E ) e. RR')], '( 1 + E ) e. CC'), d('mulcld', [a1(w, A0, 'ax-icn', '_i e. CC'), d('recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % S0()),
                                                                     d('syl2anc', [d('readdcld', [a1(w, A0, '1re', '1 e. RR'), er], '( 1 + E ) e. RR'), tr, w.inst('crre')], '( Re ` %s ) = ( 1 + E )' % S0()), j1],
                                                            '( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ %s e. NN0 )' % (S0(), S0(), K1))],
                                               '( %s /\\ ( E e. RR+ /\\ E <_ 1 ) /\\ ( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ %s e. NN0 ) )' % (NXH, S0(), S0(), K1)))
    ab = use(w, A0, 'kd2abel', {'Y': X1, 'Z': X2}, d('3jca', [nxh, d('3jca', [tr, er, jn], '( T e. RR /\\ E e. RR /\\ J e. NN0 )'), d('3jca', [x1p, x2r, x12], '( %s e. RR+ /\\ %s e. RR /\\ %s <_ %s )' % (X1, X2, X1, X2))],
                                                        inst_stmt('kd2abel', {'Y': X1, 'Z': X2})[0]))
    abc = inst_stmt('kd2abel', {'Y': X1, 'Z': X2})[1]
    ibl = d('simpld', [ab], top_and(abc)[0]); dwe = d('simprd', [ab], top_and(abc)[1])
    PHZ = PHI('J', X2); PWZ = PWS('T', X1, X2)
    IP = 'S. ( %s (,) %s ) ( %s x. %s ) _d u' % (X1, X2, PSI('J', 'u'), PWS('T', X1, 'u'))
    PS12 = PSET(X1, X2)
    Ap = '( %s /\\ p e. %s )' % (A0, PS12)
    pm = psmem(w, Ap, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, PS12)), X1, X2)
    cpp = cpcc(w, Ap, 'p', pm['pn'], lift(w, nxh, Ap), lift(w, tr, Ap))
    psf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` %s ) ) e. Fin' % X2), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` %s ) )' % (PS12, X2))], '%s e. Fin' % PS12)
    pwzc = d('fsumcl', [psf, cpp], '%s e. CC' % PWZ)
    phzr = d('remulcld', [d('reexpcld', [d('relogcld', [x2p], '( log ` %s ) e. RR' % X2), j1], '( ( log ` %s ) ^ %s ) e. RR' % (X2, K1)), d('rpred', [d('rpcxpcld', [x2p, d('renegcld', [er], '-u E e. RR')], '( %s ^c -u E ) e. RR+' % X2)], '( %s ^c -u E ) e. RR' % X2)],
              '%s e. RR' % PHZ)
    x2ge1 = d('letrd', [a1(w, A0, '1re', '1 e. RR'), x1r, x2r, x11, x12], '1 <_ %s' % X2)
    phz0 = d('mulge0d', [d('reexpcld', [d('relogcld', [x2p], '( log ` %s ) e. RR' % X2), j1], '( ( log ` %s ) ^ %s ) e. RR' % (X2, K1)), d('rpred', [d('rpcxpcld', [x2p, d('renegcld', [er], '-u E e. RR')], '( %s ^c -u E ) e. RR+' % X2)], '( %s ^c -u E ) e. RR' % X2),
                         d('expge0d', [d('relogcld', [x2p], '( log ` %s ) e. RR' % X2), j1, d('logge0d', [x2r, x2ge1], '0 <_ ( log ` %s )' % X2)], '0 <_ ( ( log ` %s ) ^ %s )' % (X2, K1)),
                         d('rpge0d', [d('rpcxpcld', [x2p, d('renegcld', [er], '-u E e. RR')], '( %s ^c -u E ) e. RR+' % X2)], '0 <_ ( %s ^c -u E )' % X2)], '0 <_ %s' % PHZ)
    # u facts
    YZ = '( %s (,) %s )' % (X1, X2)
    Au = '( %s /\\ u e. %s )' % (A0, YZ)
    du = lambda ref, h, c: D(w, Au, ref, h, c)
    L = lambda st: lift(w, st, Au)
    uy = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, YZ))
    ur = du('syl', [uy, w.inst('elioore')], 'u e. RR')
    uo = du('syl', [uy, w.inst('eliooord')], '( %s < u /\\ u < %s )' % (X1, X2))
    u1 = du('letrd', [a1(w, Au, '1re', '1 e. RR'), L(x1r), ur, L(x11), du('ltled', [L(x1r), ur, du('simpld', [uo], '%s < u' % X1)], '%s <_ u' % X1)], '1 <_ u')
    up = du('elrpd', [ur, du('ltletrd', [a1(w, Au, '0re', '0 e. RR'), a1(w, Au, '1re', '1 e. RR'), ur, a1(w, Au, '0lt1', '0 < 1'), u1], '0 < u')], 'u e. RR+')
    lu = du('relogcld', [up], '( log ` u ) e. RR')
    PSu = PSI('J', 'u'); PWu = PWS('T', X1, 'u')
    CX = '( u ^c ( -u 1 - E ) )'
    psr = du('remulcld', [du('remulcld', [du('rpred', [du('rpcxpcld', [up, du('resubcld', [du('renegcld', [a1(w, Au, '1re', '1 e. RR')], '-u 1 e. RR'), L(er)], '( -u 1 - E ) e. RR')], '%s e. RR+' % CX)], '%s e. RR' % CX),
                                        du('reexpcld', [lu, L(jn)], '( ( log ` u ) ^ J ) e. RR')], '( %s x. ( ( log ` u ) ^ J ) ) e. RR' % CX),
                          du('resubcld', [du('readdcld', [du('nn0red', [L(jn)], 'J e. RR'), a1(w, Au, '1re', '1 e. RR')], '( J + 1 ) e. RR'), du('remulcld', [L(er), lu], '( E x. ( log ` u ) ) e. RR')],
                             '( ( J + 1 ) - ( E x. ( log ` u ) ) ) e. RR')], '%s e. RR' % PSu)
    PSU_ = PSET(X1, 'u')
    Apu = '( %s /\\ p e. %s )' % (Au, PSU_)
    pmu = psmem(w, Apu, 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (Apu, PSU_)), X1, 'u')
    cpu = cpcc(w, Apu, 'p', pmu['pn'], lift(w, nxh, Apu), lift(w, tr, Apu))
    pwuc = du('fsumcl', [du('ssfid', [du('fzfid', [], '( 1 ... ( |_ ` u ) ) e. Fin'), a1(w, Au, 'ssrab2', '%s C_ ( 1 ... ( |_ ` u ) )' % PSU_)], '%s e. Fin' % PSU_), cpu], '%s e. CC' % PWu)
    h4 = du('jca', [psr, pwuc], '( %s e. RR /\\ %s e. CC )' % (PSu, PWu))
    ipc = d('itgcl', [du('mulcld', [du('recnd', [psr], '%s e. CC' % PSu), pwuc], '( %s x. %s ) e. CC' % (PSu, PWu)), ibl], '%s e. CC' % IP)
    Aq = Ap
    phpc = D(w, Aq, 'mulcld', [D(w, Aq, 'expcld', [D(w, Aq, 'recnd', [D(w, Aq, 'relogcld', [D(w, Aq, 'nnrpd', [pm['pn']], 'p e. RR+')], '( log ` p ) e. RR')], '( log ` p ) e. CC'), lift(w, j1, Aq)], '( ( log ` p ) ^ %s ) e. CC' % K1),
                               D(w, Aq, 'cxpcld', [D(w, Aq, 'nncnd', [pm['pn']], 'p e. CC'), D(w, Aq, 'negcld', [lift(w, d('recnd', [er], 'E e. CC'), Aq)], '-u E e. CC')], '( p ^c -u E ) e. CC')], '%s e. CC' % PHI('J', 'p'))
    dwc = d('fsumcl', [psf, D(w, Aq, 'mulcld', [phpc, cpp], '( %s x. %s ) e. CC' % (PHI('J', 'p'), CP('p')))], '%s e. CC' % DW)
    A_ = '( %s x. %s )' % (PHZ, PWZ)
    ac = d('mulcld', [d('recnd', [phzr], '%s e. CC' % PHZ), pwzc], '%s e. CC' % A_)
    # |DW| >_ F (3/4) Q - 3 F Q / 8
    ad = d('abs2difd', [LSc, dwc], '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (LS, DW, LS, DW))
    # boundary
    wb = use(w, A0, 'kd2wb', {'Y': X1, 'U': X2, 'Z': X2}, d('3jca', [nxh, d('3jca', [tr, x1r, x2r], '( T e. RR /\\ %s e. RR /\\ %s e. RR )' % (X1, X2)), d('3jca', [x2r, e20, d('leidd', [x2r], '%s <_ %s' % (X2, X2))], '( %s e. RR /\\ ( exp ` ; 2 0 ) <_ %s /\\ %s <_ %s )' % (X2, X2, X2, X2))],
                                                                  inst_stmt('kd2wb', {'Y': X1, 'U': X2, 'Z': X2})[0]))
    WBR = '( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. ( log ` %s ) ) + 5 ) )' % X2
    ba = d('eqtrd', [d('absmuld', [d('recnd', [phzr], '%s e. CC' % PHZ), pwzc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (A_, PHZ, PWZ)),
                     d('oveq1d', [d('absidd', [phzr, phz0], '( abs ` %s ) = %s' % (PHZ, PHZ))], '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (PHZ, PWZ, PHZ, PWZ))],
            '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (A_, PHZ, PWZ))
    wbr = cl.mem(WBR, 'RR') if False else d('remulcld', [d('rpred', [e1p], '( exp ` 1 ) e. RR'), d('readdcld', [d('remulcld', [w.s([num.real(w, '( 5 / 4 )')], 'a1i', '( %s -> ( 5 / 4 ) e. RR )' % A0), d('relogcld', [x2p], '( log ` %s ) e. RR' % X2)],
                                                                                                           '( ( 5 / 4 ) x. ( log ` %s ) ) e. RR' % X2), a1(w, A0, '5re', '5 e. RR')], '( ( ( 5 / 4 ) x. ( log ` %s ) ) + 5 ) e. RR' % X2)], '%s e. RR' % WBR)
    bb = d('lemul2ad', [d('abscld', [pwzc], '( abs ` %s ) e. RR' % PWZ), wbr, phzr, phz0, wb], '( %s x. ( abs ` %s ) ) <_ ( %s x. %s )' % (PHZ, PWZ, PHZ, WBR))
    # PHZ x. WBR = bbd LHS
    ce = d('cxpefd', [x2c, x2n, d('negcld', [d('recnd', [er], 'E e. CC')], '-u E e. CC')], '( %s ^c -u E ) = ( exp ` ( -u E x. ( log ` %s ) ) )' % (X2, X2))
    xe_ = ringeq(w, A0, '( -u E x. ( ; 1 6 x. %s ) )' % RR_, '-u ( ; 1 6 x. ( E x. %s ) )' % RR_, cle)
    xe2 = chain(w, A0, ['( -u E x. ( log ` %s ) )' % X2, '( -u E x. %s )' % Bb, '( -u E x. ( ; 1 6 x. %s ) )' % RR_, '-u ( ; 1 6 x. ( E x. %s ) )' % RR_, '-u ( ; 1 6 x. %s )' % MD],
                [d('oveq2d', [l2], '( -u E x. ( log ` %s ) ) = ( -u E x. %s )' % (X2, Bb)), d('oveq2d', [be], '( -u E x. %s ) = ( -u E x. ( ; 1 6 x. %s ) )' % (Bb, RR_)), xe_,
                 d('negeqd', [d('oveq2d', [erd], '( ; 1 6 x. ( E x. %s ) ) = ( ; 1 6 x. %s )' % (RR_, MD))], '-u ( ; 1 6 x. ( E x. %s ) ) = -u ( ; 1 6 x. %s )' % (RR_, MD))])
    cee = d('eqtrd', [ce, d('fveq2d', [xe2], '( exp ` ( -u E x. ( log ` %s ) ) ) = ( exp ` -u ( ; 1 6 x. %s ) )' % (X2, MD))], '( %s ^c -u E ) = ( exp ` -u ( ; 1 6 x. %s ) )' % (X2, MD))
    BBD = '( ( ( %s ^ %s ) x. ( exp ` -u ( ; 1 6 x. %s ) ) ) x. ( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) ) )' % (Bb, K1, MD, Bb)
    pe = d('oveq12d', [d('oveq12d', [d('oveq1d', [l2], '( ( log ` %s ) ^ %s ) = ( %s ^ %s )' % (X2, K1, Bb, K1)), cee], '%s = ( ( %s ^ %s ) x. ( exp ` -u ( ; 1 6 x. %s ) ) )' % (PHZ, Bb, K1, MD)),
                       d('oveq2d', [d('oveq1d', [d('oveq2d', [l2], '( ( 5 / 4 ) x. ( log ` %s ) ) = ( ( 5 / 4 ) x. %s )' % (X2, Bb))], '( ( ( 5 / 4 ) x. ( log ` %s ) ) + 5 ) = ( ( ( 5 / 4 ) x. %s ) + 5 )' % (X2, Bb))],
                         '%s = ( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) )' % (WBR, Bb))], '( %s x. %s ) = %s' % (PHZ, WBR, BBD))
    bdry = d('breqtrd', [d('eqbrtrd', [ba, bb], '( abs ` %s ) <_ ( %s x. %s )' % (A_, PHZ, WBR)), pe], '( abs ` %s ) <_ %s' % (A_, BBD))
    bdry2 = d('letrd', [d('abscld', [ac], '( abs ` %s ) e. RR' % A_), cl.mem(BBD, 'RR') if False else d('remulcld' if False else 'eqeltrd', [d('eqcomd', [pe], '%s = ( %s x. %s )' % (BBD, PHZ, WBR)), d('remulcld', [phzr, wbr], '( %s x. %s ) e. RR' % (PHZ, WBR))], '%s e. RR' % BBD),
                        cl.mem(FQ8J, 'RR'), bdry, bbd], '( abs ` %s ) <_ %s' % (A_, FQ8J))
    # IP = A_ - DW
    ipe = d('eqtr3d', [d('oveq2d', [dwe], '( %s - %s ) = ( %s - ( %s - %s ) )' % (A_, DW, A_, A_, IP)), d('nncand', [ac, ipc], '( %s - ( %s - %s ) ) = %s' % (A_, A_, IP, IP))] if False else
             [d('nncand', [ac, ipc], '( %s - ( %s - %s ) ) = %s' % (A_, A_, IP, IP)), d('oveq2d', [dwe], '( %s - %s ) = ( %s - ( %s - %s ) )' % (A_, DW, A_, A_, IP))], 'T.') if False else \
        d('eqtr4d', [d('nncand', [ac, ipc], '( %s - ( %s - %s ) ) = %s' % (A_, A_, IP, IP)), d('oveq2d', [dwe], '( %s - %s ) = ( %s - ( %s - %s ) )' % (A_, DW, A_, A_, IP))] if False else
          [d('nncand', [ac, ipc], '( %s - ( %s - %s ) ) = %s' % (A_, A_, IP, IP)), d('eqcomd', [d('oveq2d', [dwe], '( %s - %s ) = ( %s - ( %s - %s ) )' % (A_, DW, A_, A_, IP))], '( %s - ( %s - %s ) ) = ( %s - %s )' % (A_, A_, IP, A_, DW))],
          '%s = ( %s - %s )' % (IP, A_, DW)) if False else None
    ipe = d('eqtr3d', [d('nncand', [ac, ipc], '( %s - ( %s - %s ) ) = %s' % (A_, A_, IP, IP)), d('oveq2d', [dwe], '( %s - %s ) = ( %s - ( %s - %s ) )' % (A_, DW, A_, A_, IP))], '%s = ( %s - %s )' % (IP, A_, DW)) if False else \
        d('eqtr2d', [d('oveq2d', [dwe], '( %s - %s ) = ( %s - ( %s - %s ) )' % (A_, DW, A_, A_, IP)), d('nncand', [ac, ipc], '( %s - ( %s - %s ) ) = %s' % (A_, A_, IP, IP))], '%s = ( %s - %s )' % (IP, A_, DW))
    ad2 = d('abs2difd', [dwc, ac], '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (DW, A_, DW, A_))
    ad3 = d('eqtr4d', [d('fveq2d', [ipe], '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IP, A_, DW)), d('abssubd', [dwc, ac], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (DW, A_, A_, DW))] if False else
             [d('fveq2d', [ipe], '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IP, A_, DW)), d('abssubd', [ac, dwc], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (A_, DW, DW, A_))] if False else
             [d('fveq2d', [ipe], '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IP, A_, DW)), d('abssubd', [dwc, ac], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (DW, A_, A_, DW))],
             '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IP, DW, A_)) if False else None
    ad3 = d('eqtrd', [d('fveq2d', [ipe], '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IP, A_, DW)), d('abssubd', [ac, dwc], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (A_, DW, DW, A_))],
             '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IP, DW, A_))
    ATLx = '( abs ` ( %s - %s ) )' % (LS, DW)
    atoms = [(('( abs ` %s )' % LS), d('abscld', [LSc], '( abs ` %s ) e. RR' % LS)), (('( abs ` %s )' % DW), d('abscld', [dwc], '( abs ` %s ) e. RR' % DW)),
             (ATLx, d('abscld', [d('subcld', [LSc, dwc], '( %s - %s ) e. CC' % (LS, DW))], '%s e. RR' % ATLx)), (T1_, cl.mem(T1_, 'RR') if False else d('eqeltrrd', [ringeq(w, A0, '( %s x. ( ; 2 0 x. ( 4 ^ %s ) ) )' % (F, K1), T1_, cl4), cl.mem('( %s x. ( ; 2 0 x. ( 4 ^ %s ) ) )' % (F, K1), 'RR')], '%s e. RR' % T1_)),
             (T2_, d('remulcld', [d('reexpcld', [d('relogcld', [x1p], '( log ` %s ) e. RR' % X1), j1], '( ( log ` %s ) ^ %s ) e. RR' % (X1, K1)), cl.mem(B54, 'RR')], '%s e. RR' % T2_)),
             (T3_, d('remulcld', [d('rpred', [d('rpcxpcld', [x2p, d('renegcld', [d('rpred', [d('rphalfcld', [ep], '( E / 2 ) e. RR+')], '( E / 2 ) e. RR')], '-u ( E / 2 ) e. RR')], '%s e. RR+' % ZE)], '%s e. RR' % ZE), cl.mem(DG, 'RR')], '%s e. RR' % T3_)),
             ('( abs ` %s )' % A_, d('abscld', [ac], '( abs ` %s ) e. RR' % A_)),
             ('( abs ` ( %s - %s ) )' % (DW, A_), d('abscld', [d('subcld', [dwc, ac], '( %s - %s ) e. CC' % (DW, A_))], '( abs ` ( %s - %s ) ) e. RR' % (DW, A_))), ('( abs ` %s )' % IP, d('abscld', [ipc], '( abs ` %s ) e. RR' % IP))]
    cla = Closure(w, A0, {F: ('RR', fr), QJ: ('RR', qr)}); cla.atom(F); cla.atom(QJ)
    for E_, st in atoms:
        cla.leaf(E_, 'RR', st)
    ipb = nlinarith(w, A0, [hls, ad, sb, t1, t2, t3, bdry2, ad2, ad3], '( %s x. ( %s / 4 ) ) <_ ( abs ` %s )' % (F, QJ, IP), closure=cla)
    # endgame
    C7 = '( ( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) ) / ( E ^ J ) )'
    GG = '( ( %s x. ( E ^ J ) ) / ; 6 8 )' % QJ
    clg = Closure(w, A0, {'E': ('RR+', ep), 'J': ('NN0', jn), QJ: ('RR+', qp)}); clg.atom(QJ)
    clg.leaf('( ! ` J )', 'RR+', d('nnrpd', [d('faccld', [jn], '( ! ` J ) e. NN')], '( ! ` J ) e. RR+'))
    c7p = clg.mem(C7, 'RR+'); ggp = clg.mem(GG, 'RR+')
    brp = d('elrpd', [br, d('ltletrd', [a1(w, A0, '0re', '0 e. RR'), w.s([num.real(w, '; 2 0')], 'a1i', '( %s -> ; 2 0 e. RR )' % A0), br, w.s([num.le_nat(w, 0, 20, strict=True)], 'a1i', '( %s -> 0 < ; 2 0 )' % A0), b20], '0 < %s' % Bb)], '%s e. RR+' % Bb)
    lk = d('breqtrrd' if False else 'idi', [], 'T.') if False else None
    lkk = linarith(w, A0, [l1, l2, a0_], '( ( log ` %s ) - ( log ` %s ) ) <_ %s' % (X2, X1, Bb),
                   closure=Closure(w, A0, {'( log ` %s )' % X1: ('RR', d('relogcld', [x1p], '( log ` %s ) e. RR' % X1)), '( log ` %s )' % X2: ('RR', d('relogcld', [x2p], '( log ` %s ) e. RR' % X2)), Aa: ('RR', ar), Bb: ('RR', br)}) if True else None)
    # G C7 = F Q / 4
    EJ = '( E ^ J )'; IEJ = '( 1 / %s )' % EJ
    ejc = clg.mem(EJ, 'CC'); ejn = clg.ne0(EJ)
    c7e = d('divrecd', [clg.mem('( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) )', 'CC'), ejc, ejn], '%s = ( ( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) ) x. %s )' % (C7, IEJ))
    clh = Closure(w, A0, {QJ: ('CC', clg.mem(QJ, 'CC')), EJ: ('CC', ejc), IEJ: ('CC', d('reccld', [ejc, ejn], '%s e. CC' % IEJ)), '( ! ` J )': ('CC', clg.mem('( ! ` J )', 'CC')), 'J': ('CC', d('nn0cnd', [jn], 'J e. CC'))})
    for a in (QJ, EJ, IEJ, '( ! ` J )'):
        clh.atom(a)
    g1 = ringeq(w, A0, '( %s x. ( ( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) ) x. %s ) )' % (GG, IEJ), '( ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) x. ( %s x. %s ) )' % (QJ, EJ, IEJ), clh)
    g2 = d('recidd', [ejc, ejn], '( %s x. %s ) = 1' % (EJ, IEJ))
    g3 = d('syl', [jn, w.inst('facp1')], '%s = ( ( ! ` J ) x. ( J + 1 ) )' % F)
    GC = '( %s x. %s )' % (GG, C7)
    gce = chain(w, A0, [GC, '( %s x. ( ( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) ) x. %s ) )' % (GG, IEJ), '( ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) x. ( %s x. %s ) )' % (QJ, EJ, IEJ),
                        '( ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) x. 1 )' % QJ, '( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 )' % QJ, '( ( %s x. %s ) / 4 )' % (QJ, F)],
                [d('oveq2d', [c7e], '%s = ( %s x. ( ( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) ) x. %s ) )' % (GC, GG, IEJ)), g1,
                 d('oveq2d', [g2], '( ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) x. ( %s x. %s ) ) = ( ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) x. 1 )' % (QJ, EJ, IEJ, QJ)),
                 d('mulridd', [clh.mem('( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 )' % QJ, 'CC')], '( ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) x. 1 ) = ( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 )' % (QJ, QJ)),
                 d('oveq1d', [d('oveq2d', [d('eqcomd', [g3], '( ( ! ` J ) x. ( J + 1 ) ) = %s' % F)], '( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) = ( %s x. %s )' % (QJ, QJ, F))],
                   '( ( %s x. ( ( ! ` J ) x. ( J + 1 ) ) ) / 4 ) = ( ( %s x. %s ) / 4 )' % (QJ, QJ, F))])
    clz = Closure(w, A0, {F: ('RR', fr), QJ: ('RR', qr), '( abs ` %s )' % IP: ('RR', d('abscld', [ipc], '( abs ` %s ) e. RR' % IP))}); clz.atom(F); clz.atom(QJ); clz.atom('( abs ` %s )' % IP)
    gcl = nlinarith(w, A0, [gce, ipb], '%s <_ ( abs ` %s )' % (GC, IP), closure=clz) if False else \
        d('breqtrrd' if False else 'eqbrtrd', [d('eqtrd', [gce, ringeq(w, A0, '( ( %s x. %s ) / 4 )' % (QJ, F), '( %s x. ( %s / 4 ) )' % (F, QJ), Closure(w, A0, {F: ('CC', clh.mem(F, 'CC') if False else d('nncnd', [fnn], '%s e. CC' % F)), QJ: ('CC', clg.mem(QJ, 'CC'))}))],
                                              '%s = ( %s x. ( %s / 4 ) )' % (GC, F, QJ)), ipb], '%s <_ ( abs ` %s )' % (GC, IP))
    # h5 via kd2kb
    lux = du('mpbid', [du('ltled', [ur, L(x2r), du('simprd', [uo], 'u < %s' % X2)], 'u <_ %s' % X2), du('logled', [up, L(x2p)], '( u <_ %s <-> ( log ` u ) <_ ( log ` %s ) )' % (X2, X2))], '( log ` u ) <_ ( log ` %s )' % X2)
    elu = du('breqtrd', [du('lemul2ad', [lu, du('relogcld', [L(x2p)], '( log ` %s ) e. RR' % X2), L(er), L(P['e0']), lux], '( E x. ( log ` u ) ) <_ ( E x. ( log ` %s ) )' % X2),
                         du('eqtrd', [du('oveq2d', [L(l2)], '( E x. ( log ` %s ) ) = ( E x. %s )' % (X2, Bb)), du('eqtrd', [du('oveq2d', [L(be)], '( E x. %s ) = ( E x. ( ; 1 6 x. %s ) )' % (Bb, RR_)),
                                                                                                            du('eqtrd', [ringeq(w, Au, '( E x. ( ; 1 6 x. %s ) )' % RR_, '( ; 1 6 x. ( E x. %s ) )' % RR_, Closure(w, Au, {'E': ('CC', L(d('rpcnd', [ep], 'E e. CC'))), RR_: ('CC', L(d('rpcnd', [rrp], '%s e. CC' % RR_)))})),
                                                                                                                         du('oveq2d', [L(erd)], '( ; 1 6 x. ( E x. %s ) ) = ( ; 1 6 x. %s )' % (RR_, MD))], '( E x. ( ; 1 6 x. %s ) ) = ( ; 1 6 x. %s )' % (RR_, MD))],
                                                                                                  '( E x. %s ) = ( ; 1 6 x. %s )' % (Bb, MD))], '( E x. ( log ` %s ) ) = ( ; 1 6 x. %s )' % (X2, MD))],
              '( E x. ( log ` u ) ) <_ ( ; 1 6 x. %s )' % MD)
    cln3 = Closure(w, A0, {ND: ('RR', ndr), 'J': ('RR', d('nn0red', [jn], 'J e. RR'))}); cln3.atom(ND)
    mdj = linarith(w, A0, [r1], '%s <_ ( J + 1 )' % MD, closure=cln3)
    kb = use(w, Au, 'kd2kb', {'M': MD, 'U': 'u'}, du('jca', [du('jca', [L(ep), du('3jca', [L(jn), L(MDr), L(mdj)], '( J e. NN0 /\\ %s e. RR /\\ %s <_ ( J + 1 ) )' % (MD, MD))], '( E e. RR+ /\\ ( J e. NN0 /\\ %s e. RR /\\ %s <_ ( J + 1 ) ) )' % (MD, MD)),
                                                             du('3jca', [ur, u1, elu], '( u e. RR /\\ 1 <_ u /\\ ( E x. ( log ` u ) ) <_ ( ; 1 6 x. %s ) )' % MD)],
                                                     inst_stmt('kd2kb', {'M': MD, 'U': 'u'})[0]))
    ib2 = use(w, A0, 'kd2ibl', {'Y': X1, 'Z': X2}, d('3jca', [nxh, tr, d('3jca', [x1p, x2r, x12], '( %s e. RR+ /\\ %s e. RR /\\ %s <_ %s )' % (X1, X2, X1, X2))], inst_stmt('kd2ibl', {'Y': X1, 'Z': X2})[0]))
    H1 = d('3jca', [x1p, x2r, x12], '( %s e. RR+ /\\ %s e. RR /\\ %s <_ %s )' % (X1, X2, X1, X2))
    H6 = d('3jca', [c7p, d('jca', [brp, lkk], '( %s e. RR+ /\\ ( ( log ` %s ) - ( log ` %s ) ) <_ %s )' % (Bb, X2, X1, Bb)), d('jca', [ggp, gcl], '( %s e. RR+ /\\ %s <_ ( abs ` %s ) )' % (GG, GC, IP))],
           '( %s e. RR+ /\\ ( %s e. RR+ /\\ ( ( log ` %s ) - ( log ` %s ) ) <_ %s ) /\\ ( %s e. RR+ /\\ %s <_ ( abs ` %s ) ) )' % (C7, Bb, X2, X1, Bb, GG, GC, IP))
    ISQ = 'S. %s ( ( ( abs ` %s ) ^ 2 ) / u ) _d u' % (YZ, PWu)
    am = d('kd2am', [H1, ibl, ib2, h4, kb, H6], '( ( %s ^ 2 ) / %s ) <_ %s' % (GG, Bb, ISQ))
    # kd2bend and the final
    WW = '( ( ( E ^ 3 ) x. %s ) x. ( exp ` ( 6 x. %s ) ) )' % (MD, MD)
    BE = '( ( E x. ( %s ^ 2 ) ) / ( ; 1 6 x. %s ) )' % (GG, MD)
    bee = d('eqtrd', [d('divdiv2d', [clg.mem('( %s ^ 2 )' % GG, 'CC'), cl.mem('( ; 1 6 x. %s )' % MD, 'CC'), d('rpcnd', [ep], 'E e. CC'), cl.ne0('( ; 1 6 x. %s )' % MD), d('rpne0d', [ep], 'E =/= 0')],
                        '( ( %s ^ 2 ) / %s ) = ( ( ( %s ^ 2 ) x. E ) / ( ; 1 6 x. %s ) )' % (GG, Bb, GG, MD)),
                      d('oveq1d', [d('mulcomd', [clg.mem('( %s ^ 2 )' % GG, 'CC'), d('rpcnd', [ep], 'E e. CC')], '( ( %s ^ 2 ) x. E ) = ( E x. ( %s ^ 2 ) )' % (GG, GG))],
                        '( ( ( %s ^ 2 ) x. E ) / ( ; 1 6 x. %s ) ) = %s' % (GG, MD, BE))], '( ( %s ^ 2 ) / %s ) = %s' % (GG, Bb, BE))
    wr = cl.mem(WW, 'RR'); w0 = cl.ge0(WW)
    isr = d('itgrecl', [du('rerpdivcld', [du('resqcld', [du('abscld', [pwuc], '( abs ` %s ) e. RR' % PWu)], '( ( abs ` %s ) ^ 2 ) e. RR' % PWu), up], '( ( ( abs ` %s ) ^ 2 ) / u ) e. RR' % PWu), ib2], '%s e. RR' % ISQ)
    f1 = d('lemul2ad', [d('rerpdivcld', [clg.mem('( %s ^ 2 )' % GG, 'RR'), brp], '( ( %s ^ 2 ) / %s ) e. RR' % (GG, Bb)), isr, wr, w0, am], '( %s x. ( ( %s ^ 2 ) / %s ) ) <_ ( %s x. %s )' % (WW, GG, Bb, WW, ISQ))
    f2 = d('breqtrd', [bend, d('oveq2d', [d('eqcomd', [bee], '%s = ( ( %s ^ 2 ) / %s )' % (BE, GG, Bb))], '( %s x. %s ) = ( %s x. ( ( %s ^ 2 ) / %s ) )' % (WW, BE, WW, GG, Bb))],
            '1 <_ ( %s x. ( ( %s ^ 2 ) / %s ) )' % (WW, GG, Bb))
    fin = d('letrd', [a1(w, A0, '1re', '1 e. RR'), d('remulcld', [wr, d('rerpdivcld', [clg.mem('( %s ^ 2 )' % GG, 'RR'), brp], '( ( %s ^ 2 ) / %s ) e. RR' % (GG, Bb))], '( %s x. ( ( %s ^ 2 ) / %s ) ) e. RR' % (WW, GG, Bb)),
                      d('remulcld', [wr, isr], '( %s x. %s ) e. RR' % (WW, ISQ)), f2, f1], FINAL)
    w.qed([fin], 'idi', S['kd2db'])
    return only_run(w, only)


def gen_det():
    w = W('kd2det', 'Lean ` KDerivDetect.kderiv_detection ` (TZ Theorem 4.2 shape) at the Metamath constants: a zero of a nonprincipal ` chi ` within ` eta ` of ` 1 + i T ` forces ` 1 <_ eta^3 M e^(6M) S. ( X1 , X2 ) abs S ( u )^2 / u ` with ` M = Mdet ` ( ~ sdzc at ` 6 eta ` , ~ kdturan , ~ kd2da , ~ kd2db ).')
    A0 = A0H
    d = lambda ref, h, c: D(w, A0, ref, h, c)
    P = prelude(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    ep, er, e5, tr, chi, hz = P['ep'], P['er'], P['e5'], P['tr'], P['chi'], P['hz']
    ndn, ndr = P['ndn'], P['ndr']
    # Z6 count <_ Ndet (sdzc at 6 E)
    cle = Closure(w, A0, {'E': ('RR', er)})
    e6p = d('rpmulcld', [w.s([num.rp(w, '6')], 'a1i', '( %s -> 6 e. RR+ )' % A0), ep], '( 6 x. E ) e. RR+')
    e6s = linarith(w, A0, [e5], '( 6 x. E ) <_ %s' % R120, closure=cle)
    sd = use(w, A0, 'sdzc', {'W': '( 6 x. E )'}, d('jca', [chi, d('jca', [tr, d('jca', [e6p, e6s], '( ( 6 x. E ) e. RR+ /\\ ( 6 x. E ) <_ %s )' % R120)], '( T e. RR /\\ ( ( 6 x. E ) e. RR+ /\\ ( 6 x. E ) <_ %s ) )' % R120)],
                                                                   '( %s /\\ ( T e. RR /\\ ( ( 6 x. E ) e. RR+ /\\ ( 6 x. E ) <_ %s ) ) )' % (CHI, R120)))
    SZ = 'sum_ q e. %s %s' % (Z6, MU())
    elx = d('lemul2ad', [P['lxr'], d('readdcld', [P['lr'], P['lr']], '( %s + %s ) e. RR' % (LY, LY)), er, P['e0'], P['lx2']], '( E x. %s ) <_ ( E x. ( %s + %s ) )' % (LOGX, LY, LY))
    szr = d('fsumrecl', [d('ssfid', [d('simp1d', [use(w, A0, 'lchrzc8', {}, d('jca', [chi, tr], '( %s /\\ T e. RR )' % CHI))], top_and(split_imp(stmt('lchrzc8'))[1])[0]),
                                     a1(w, A0, 'ssrab2', '%s C_ %s' % (Z6, ZD()))], '%s e. Fin' % Z6),
                         D(w, '( %s /\\ q e. %s )' % (A0, Z6), 'nnred', [D(w, '( %s /\\ q e. %s )' % (A0, Z6), 'mpd', [D(w, '( %s /\\ q e. %s )' % (A0, Z6), 'sseldd', [a1(w, '( %s /\\ q e. %s )' % (A0, Z6), 'ssrab2', '%s C_ %s' % (Z6, ZD())), w.s([], 'simpr', '( ( %s /\\ q e. %s ) -> q e. %s )' % (A0, Z6, Z6))], 'q e. %s' % ZD()),
                                                                                                        lift(w, D(w, A0, 'syl', [d('simp2d', [use(w, A0, 'lchrzc8', {}, d('jca', [chi, tr], '( %s /\\ T e. RR )' % CHI))], top_and(split_imp(stmt('lchrzc8'))[1])[1]), w.inst('rsp')],
                                                                                                                  '( q e. %s -> %s e. NN )' % (ZD(), MU())), '( %s /\\ q e. %s )' % (A0, Z6))], '%s e. NN' % MU())], '%s e. RR' % MU())],
              '%s e. RR' % SZ)
    cls = Closure(w, A0, {'E': ('RR', er), LOGX: ('RR', P['lxr']), LY: ('RR', P['lr']), SZ: ('RR', szr), ND: ('RR', ndr)})
    for a in (LOGX, LY, SZ, ND):
        cls.atom(a)
    cnt = nlinarith(w, A0, [sd, elx, P['ndl']], '%s <_ %s' % (SZ, ND), closure=cls)
    mdn = d('nn0mulcld', [a1(w, A0, '6nn0', '6 e. NN0'), d('nnnn0d', [ndn], '%s e. NN0' % ND)], '%s e. NN0' % MD)
    e12 = linarith(w, A0, [e5], 'E <_ ( 1 / 2 )', closure=cle)
    tu = use(w, A0, 'kdturan', {'J': ND, 'M': MD}, d('jca', [d('jca', [chi, d('3jca', [tr, ep, e12], '( T e. RR /\\ E e. RR+ /\\ E <_ ( 1 / 2 ) )')], '( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ ( 1 / 2 ) ) )' % CHI),
                                                           d('3jca', [d('jca', [ndn, cnt], '( %s e. NN /\\ %s <_ %s )' % (ND, SZ, ND)), hz, mdn],
                                                             '( ( %s e. NN /\\ %s <_ %s ) /\\ E. p e. CC ( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E ) /\\ %s e. NN0 )' % (ND, SZ, ND, LFN, ONE('T'), MD))],
                                                     inst_stmt('kdturan', {'J': ND, 'M': MD})[0]))
    RNG = '( ( %s + 1 ) ... ( %s + %s ) )' % (MD, MD, ND)
    COEF = '( %s / ( ( 8 x. ( exp ` 1 ) ) x. ( %s + %s ) ) )' % (ND, MD, ND)
    SL = lambda ex: 'sum_ q e. %s ( %s / ( ( %s - q ) ^ %s ) )' % (Z6, MU(), S0(), ex)
    PHIL = '( ( %s ^ %s ) x. ( ( 1 / ( 2 x. E ) ) ^ l ) ) <_ ( abs ` %s )' % (COEF, ND, SL('l'))
    Al = '( %s /\\ l e. %s )' % (A0, RNG)
    dl = lambda ref, h, c: D(w, Al, ref, h, c)
    L = lambda st: lift(w, st, Al)
    lin_ = w.s([], 'simpr', '( %s -> l e. %s )' % (Al, RNG))
    lz = dl('syl', [lin_, w.inst('elfzelz')], 'l e. ZZ')
    lge = dl('syl', [lin_, w.inst('elfzle1')], '( %s + 1 ) <_ l' % MD); lle = dl('syl', [lin_, w.inst('elfzle2')], 'l <_ ( %s + %s )' % (MD, ND))
    J_ = '( l - 2 )'
    clj = Closure(w, Al, {'l': ('RR', dl('zred', [lz], 'l e. RR')), ND: ('RR', L(ndr))}); clj.atom(ND)
    jz = dl('zsubcld' if False else 'zsubcld', [lz, a1(w, Al, '2z', '2 e. ZZ')], '%s e. ZZ' % J_)
    j0 = linarith(w, Al, [lge, L(P['ndbig'])], '0 <_ %s' % J_, closure=clj)
    jn = dl('mpbir2and' if False else 'mpbird', [dl('jca', [jz, j0], '( %s e. ZZ /\\ 0 <_ %s )' % (J_, J_)), a1(w, Al, 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (J_, J_, J_))], '%s e. NN0' % J_)
    j2 = dl('npcand', [dl('zcnd', [lz], 'l e. CC'), a1(w, Al, '2cn', '2 e. CC')], '( %s + 2 ) = l' % J_)
    r1 = dl('breqtrrd', [lge, j2], '( %s + 1 ) <_ ( %s + 2 )' % (MD, J_))
    cl7 = Closure(w, Al, {ND: ('CC', dl('nncnd', [L(ndn)], '%s e. CC' % ND))}); cl7.atom(ND)
    r2 = dl('eqbrtrd', [j2, dl('breqtrd', [lle, ringeq(w, Al, '( %s + %s )' % (MD, ND), '( 7 x. %s )' % ND, cl7)], 'l <_ ( 7 x. %s )' % ND)], '( %s + 2 ) <_ ( 7 x. %s )' % (J_, ND))
    # sum at exponent l = ( l - 2 ) + 2 (antecedent without q)
    se = dl('sumeq2sdv', [dl('oveq2d', [dl('oveq2d', [dl('eqcomd', [j2], 'l = ( %s + 2 )' % J_)], '( ( %s - q ) ^ l ) = ( ( %s - q ) ^ ( %s + 2 ) )' % (S0(), S0(), J_))],
                                        '( %s / ( ( %s - q ) ^ l ) ) = ( %s / ( ( %s - q ) ^ ( %s + 2 ) ) )' % (MU(), S0(), MU(), S0(), J_))], '%s = %s' % (SL('l'), SL('( %s + 2 )' % J_)))
    # coefficient 1 / ( 56 e )
    E1 = '( exp ` 1 )'
    cle1 = Closure(w, Al, {ND: ('CC', dl('nncnd', [L(ndn)], '%s e. CC' % ND)), E1: ('CC', dl('rpcnd', [dl('syl', [a1(w, Al, '1re', '1 e. RR'), w.inst('rpefcl')], '%s e. RR+' % E1)], '%s e. CC' % E1))})
    cle1.atom(ND); cle1.atom(E1)
    c1 = dl('eqtrd', [dl('oveq12d', [dl('eqcomd', [dl('mullidd', [cle1.mem(ND, 'CC')], '( 1 x. %s ) = %s' % (ND, ND))], '%s = ( 1 x. %s )' % (ND, ND)),
                                     ringeq(w, Al, '( ( 8 x. %s ) x. ( %s + %s ) )' % (E1, MD, ND), '( %s x. %s )' % (C56E, ND), cle1)], '%s = ( ( 1 x. %s ) / ( %s x. %s ) )' % (COEF, ND, C56E, ND)),
                      dl('divcan5rd', [a1(w, Al, 'ax-1cn', '1 e. CC'), cle1.mem(C56E, 'CC'), cle1.mem(ND, 'CC'), dl('rpne0d', [lift(w, w.s([w.s([], 'kd2tc', S['kd2tc'])], 'simpli', '%s e. RR+' % C56E) if False else
                                                                                                                                   w.s([w.s([w.s([], 'kd2tc', S['kd2tc'])], 'simpli', '%s e. RR+' % C56E)], 'a1i', '( %s -> %s e. RR+ )' % (A0, C56E)), Al)], '%s =/= 0' % C56E),
                                      dl('nnne0d', [L(ndn)], '%s =/= 0' % ND)], '( ( 1 x. %s ) / ( %s x. %s ) ) = ( 1 / %s )' % (ND, C56E, ND, C56E))], '%s = ( 1 / %s )' % (COEF, C56E))
    q1 = dl('oveq12d', [dl('oveq1d', [c1], '( %s ^ %s ) = ( ( 1 / %s ) ^ %s )' % (COEF, ND, C56E, ND)), dl('oveq2d', [dl('eqcomd', [j2], 'l = ( %s + 2 )' % J_)], '( ( 1 / ( 2 x. E ) ) ^ l ) = ( ( 1 / ( 2 x. E ) ) ^ ( %s + 2 ) )' % J_)],
            '( ( %s ^ %s ) x. ( ( 1 / ( 2 x. E ) ) ^ l ) ) = %s' % (COEF, ND, QQ(ND, 'E', J_)))
    Alp = '( %s /\\ %s )' % (Al, PHIL)
    hq = D(w, Alp, 'breqtrd', [D(w, Alp, 'eqbrtrrd', [lift(w, q1, Alp), w.s([], 'simpr', '( %s -> %s )' % (Alp, PHIL))], '%s <_ ( abs ` %s )' % (QQ(ND, 'E', J_), SL('l'))),
                               D(w, Alp, 'fveq2d', [lift(w, se, Alp)], '( abs ` %s ) = ( abs ` %s )' % (SL('l'), SL('( %s + 2 )' % J_)))], '%s <_ ( abs ` %s )' % (QQ(ND, 'E', J_), SL('( %s + 2 )' % J_)))
    A0p = lift(w, w.s([], 'id', '( %s -> %s )' % (A0, A0)), Alp)
    ra = D(w, Alp, 'use' if False else 'jca', [lift(w, r1, Alp), lift(w, r2, Alp)], '( ( %s + 1 ) <_ ( %s + 2 ) /\\ ( %s + 2 ) <_ ( 7 x. %s ) )' % (MD, J_, J_, ND))
    dA = use(w, Alp, 'kd2da', {'J': J_}, D(w, Alp, 'jca', [A0p, D(w, Alp, '3jca', [lift(w, jn, Alp), ra, hq], inst_stmt('kd2da', {'J': J_})[0].split(' /\\ ', 1)[1][:-2] if False else
                                                                                   '( %s e. NN0 /\\ ( ( %s + 1 ) <_ ( %s + 2 ) /\\ ( %s + 2 ) <_ ( 7 x. %s ) ) /\\ %s <_ ( abs ` %s ) )' % (J_, MD, J_, J_, ND, QQ(ND, 'E', J_), SL('( %s + 2 )' % J_)))],
                                                           inst_stmt('kd2da', {'J': J_})[0]))
    a0b = D(w, Alp, 'jca', [D(w, Alp, 'simpld', [A0p], '( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( N <_ Y /\\ ( ( abs ` T ) + 2 ) <_ Y ) )' % CHI),
                            D(w, Alp, 'jca', [D(w, Alp, 'jca', [lift(w, ep, Alp), lift(w, e5, Alp)], '( E e. RR+ /\\ E <_ %s )' % R5000), lift(w, P['h12'], Alp)], '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) )' % (R5000, LY))], A0B)
    dB = use(w, Alp, 'kd2db', {'J': J_}, D(w, Alp, 'jca', [a0b, D(w, Alp, '3jca', [lift(w, jn, Alp), ra, dA], inst_stmt('kd2db', {'J': J_})[0][len(A0B) + 6:-2])], inst_stmt('kd2db', {'J': J_})[0]))
    rl = d('rexlimdva', [w.s([dB], 'ex', '( %s -> ( %s -> %s ) )' % (Al, PHIL, FINAL))], '( E. l e. %s %s -> %s )' % (RNG, PHIL, FINAL))
    fin = d('mpd', [tu, rl], FINAL)
    w.qed([fin], 'idi', S['kd2det'])
    return only_run(w, only)


if __name__ == '__main__':
    gen_dA()
    gen_dB()
    gen_det()
