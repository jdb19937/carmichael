"""Sortie GF1, section G: Halasz duality (gf1half finite form, gf1hal).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_g.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from gf1lib import *
from mvlib import ringeq

only = sys.argv[1:]

c = lambda n: '( C ` %s )' % n
b = lambda n: '( B ` %s )' % n
x = lambda j, n: '( ( X ` %s ) ` %s )' % (j, n)
cx = lambda j, n: '( %s x. %s )' % (c(n), x(j, n))
F = lambda j, v='n': 'sum_ %s e. M %s' % (v, cx(j, v))
PHI = lambda i: 'if ( %s = 0 , 1 , ( ( abs ` %s ) / %s ) )' % (F(i, 'p'), F(i, 'p'), F(i, 'p'))
ZF = '( i e. J |-> %s )' % PHI('i')
z = lambda j: '( %s ` %s )' % (ZF, j)
G = lambda n, j='j': 'sum_ %s e. J ( %s x. %s )' % (j, z(j), x(j, n))
AN = lambda n: 'if ( %s = 0 , 0 , ( ( ( abs ` %s ) ^ 2 ) / %s ) )' % (b(n), c(n), b(n))
GR = lambda j, k, n: '( ( %s x. %s ) x. ( * ` %s ) )' % (b(n), x(j, n), x(k, n))
GRAM = lambda j, k: 'sum_ n e. M %s' % GR(j, k, 'n')
S['gf1half.1'] = '( ph -> ( J e. Fin /\\ M e. Fin ) )'
S['gf1half.2'] = '( ( ph /\\ ( j e. J /\\ n e. M ) ) -> %s e. CC )' % x('j', 'n')
S['gf1half.3'] = '( ( ph /\\ n e. M ) -> ( %s e. CC /\\ ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s =/= 0 -> 0 < %s ) ) )' % (c('n'), b('n'), b('n'), c('n'), b('n'))
S['gf1half'] = ('( ph -> ( sum_ j e. J ( abs ` %s ) ^ 2 ) <_ ( sum_ n e. M %s x. sum_ j e. J sum_ k e. J ( abs ` %s ) ) )'
                % (F('j'), AN('n'), GRAM('j', 'k')))


def gen_half():
    w = W('gf1half', 'Halasz duality with majorants for a finite sum over ` n ` (the finite core of Lean ` halasz_duality ` ): phases ` z_j ` with ` z_j F_j = abs F_j ` , ~ csbren , and the expansion of ` sum_n b_n abs ( G ( n ) ) ^ 2 ` into Gram entries.')
    h1, h2, h3 = ehyps(w, 'gf1half')
    A = 'ph'
    d = mk(w, A)
    jf = d('simpld', [h1], 'J e. Fin'); mf = d('simprd', [h1], 'M e. Fin')
    # ---------------- n-level facts
    An = '( ph /\\ n e. M )'
    dn = mk(w, An)
    cn = dn('simp1d', [h3], '%s e. CC' % c('n'))
    bpair = dn('simp2d', [h3], '( %s e. RR /\\ 0 <_ %s )' % (b('n'), b('n')))
    br = dn('simpld', [bpair], '%s e. RR' % b('n')); b0 = dn('simprd', [bpair], '0 <_ %s' % b('n'))
    cb = dn('simp3d', [h3], '( %s =/= 0 -> 0 < %s )' % (c('n'), b('n')))
    CA2 = '( ( abs ` %s ) ^ 2 )' % c('n')
    ca2r = dn('resqcld', [dn('abscld', [cn], '( abs ` %s ) e. RR' % c('n'))], '%s e. RR' % CA2)
    # b = 0
    Az = '( %s /\\ %s = 0 )' % (An, b('n'))
    dz = mk(w, Az)
    bz = w.s([], 'simpr', '( %s -> %s = 0 )' % (Az, b('n')))
    anz = dz('iftrued', [bz], '%s = 0' % AN('n'))
    nlt = dz('mtbird' if False else 'mpbird', [], '') if False else None
    n0b = dz('breqtrrd' if False else 'syl', [bz, w.inst('lt0ne0')], '') if False else None
    notpos = dz('mtbird', [dz('ltnrd', [a1(w, Az, '0re', '0 e. RR')], '-. 0 < 0'), dz('breq2d', [bz], '( 0 < %s <-> 0 < 0 )' % b('n'))], '-. 0 < %s' % b('n'))
    c0 = dz('mpd', [notpos, dz('necon1bd', [lift(w, cb, Az)], '( -. 0 < %s -> %s = 0 )' % (b('n'), c('n')))], '%s = 0' % c('n'))
    kz1 = dz('eqtrd', [dz('oveq1d', [dz('eqtrd', [dz('fveq2d', [c0], '( abs ` %s ) = ( abs ` 0 )' % c('n')), a1(w, Az, 'abs0', '( abs ` 0 ) = 0')], '( abs ` %s ) = 0' % c('n'))],
                                    '%s = ( 0 ^ 2 )' % CA2), a1(w, Az, 'sq0', '( 0 ^ 2 ) = 0')], '%s = 0' % CA2)
    kz2 = dz('eqtrd', [dz('oveq1d', [anz], '( %s x. %s ) = ( 0 x. %s )' % (AN('n'), b('n'), b('n'))), dz('mul02d', [dz('recnd', [lift(w, br, Az)], '%s e. CC' % b('n'))], '( 0 x. %s ) = 0' % b('n'))],
              '( %s x. %s ) = 0' % (AN('n'), b('n')))
    keyz = dz('eqtr4d', [kz1, kz2], '%s = ( %s x. %s )' % (CA2, AN('n'), b('n')))
    anrz = dz('eqeltrd', [anz, a1(w, Az, '0re', '0 e. RR')], '%s e. RR' % AN('n'))
    an0z = dz('breqtrrd', [dz('leidd', [a1(w, Az, '0re', '0 e. RR')], '0 <_ 0'), anz], '0 <_ %s' % AN('n'))
    bz_ = dz('3jca', [anrz, an0z, keyz], '( %s e. RR /\\ 0 <_ %s /\\ %s = ( %s x. %s ) )' % (AN('n'), AN('n'), CA2, AN('n'), b('n')))
    # b =/= 0
    Anz = '( %s /\\ %s =/= 0 )' % (An, b('n'))
    dnz = mk(w, Anz)
    bnz = w.s([], 'simpr', '( %s -> %s =/= 0 )' % (Anz, b('n')))
    anq = dnz('syl', [bnz, w.inst('ifnefalse')], '%s = ( %s / %s )' % (AN('n'), CA2, b('n')))
    brz = lift(w, br, Anz)
    bpos = dnz('ltlend' if False else 'mpbir2and' if False else 'syl3anc', [a1(w, Anz, '0re', '0 e. RR'), brz, D(w, Anz, 'jca', [lift(w, b0, Anz), D(w, Anz, 'necomd', [bnz], '0 =/= %s' % b('n'))], '( 0 <_ %s /\\ 0 =/= %s )' % (b('n'), b('n'))), w.inst('ltlen')] if False else [], '') if False else None
    bpos = dnz('mpbird', [dnz('jca', [lift(w, b0, Anz), bnz], '( 0 <_ %s /\\ %s =/= 0 )' % (b('n'), b('n'))),
                          dnz('syl2anc', [a1(w, Anz, '0re', '0 e. RR'), brz, w.inst('ltlen')], '( 0 < %s <-> ( 0 <_ %s /\\ %s =/= 0 ) )' % (b('n'), b('n'), b('n')))], '0 < %s' % b('n'))
    qr = dnz('redivcld', [lift(w, ca2r, Anz), brz, bnz], '( %s / %s ) e. RR' % (CA2, b('n')))
    q0 = dnz('divge0d', [lift(w, ca2r, Anz), dnz('elrpd', [brz, bpos], '%s e. RR+' % b('n')), dnz('sqge0d', [dnz('abscld', [lift(w, cn, Anz)], '( abs ` %s ) e. RR' % c('n'))], '0 <_ %s' % CA2)],
                 '0 <_ ( %s / %s )' % (CA2, b('n')))
    anrn = dnz('eqeltrd', [anq, qr], '%s e. RR' % AN('n'))
    an0n = dnz('breqtrrd', [q0, anq], '0 <_ %s' % AN('n'))
    keyn = dnz('eqtr2d', [dnz('oveq1d', [anq], '( %s x. %s ) = ( ( %s / %s ) x. %s )' % (AN('n'), b('n'), CA2, b('n'), b('n'))),
                          dnz('divcan1d', [dnz('recnd', [lift(w, ca2r, Anz)], '%s e. CC' % CA2), dnz('recnd', [brz], '%s e. CC' % b('n')), bnz], '( ( %s / %s ) x. %s ) = %s' % (CA2, b('n'), b('n'), CA2))],
                  '%s = ( %s x. %s )' % (CA2, AN('n'), b('n')))
    bn_ = dnz('3jca', [anrn, an0n, keyn], '( %s e. RR /\\ 0 <_ %s /\\ %s = ( %s x. %s ) )' % (AN('n'), AN('n'), CA2, AN('n'), b('n')))
    anall = dn('pm2.61dane' if False else 'pm2.61dane', [bz_, bn_], '( %s e. RR /\\ 0 <_ %s /\\ %s = ( %s x. %s ) )' % (AN('n'), AN('n'), CA2, AN('n'), b('n')))
    anr = dn('simp1d', [anall], '%s e. RR' % AN('n')); an0 = dn('simp2d', [anall], '0 <_ %s' % AN('n')); key = dn('simp3d', [anall], '%s = ( %s x. %s )' % (CA2, AN('n'), b('n')))
    # sqrt pieces
    SA = '( sqrt ` %s )' % AN('n'); SB = '( sqrt ` %s )' % b('n')
    sar = dn('resqrtcld', [anr, an0], '%s e. RR' % SA); sa0 = dn('sqrtge0d', [anr, an0], '0 <_ %s' % SA)
    sbr = dn('resqrtcld', [br, b0], '%s e. RR' % SB); sb0 = dn('sqrtge0d', [br, b0], '0 <_ %s' % SB)
    acr = dn('abscld', [cn], '( abs ` %s ) e. RR' % c('n')); ac0 = dn('absge0d', [cn], '0 <_ ( abs ` %s )' % c('n'))
    sq1 = dn('eqcomd', [dn('syl', [dn('jca', [acr, ac0], '( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) )' % (c('n'), c('n'))), w.inst('sqrtsq')], '( sqrt ` %s ) = ( abs ` %s )' % (CA2, c('n')))],
               '( abs ` %s ) = ( sqrt ` %s )' % (c('n'), CA2))
    sq2 = dn('fveq2d', [key], '( sqrt ` %s ) = ( sqrt ` ( %s x. %s ) )' % (CA2, AN('n'), b('n')))
    sq3 = dn('syl', [dn('jca', [dn('jca', [anr, an0], '( %s e. RR /\\ 0 <_ %s )' % (AN('n'), AN('n'))), bpair], '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (AN('n'), AN('n'), b('n'), b('n'))),
                     w.inst('sqrtmul')], '( sqrt ` ( %s x. %s ) ) = ( %s x. %s )' % (AN('n'), b('n'), SA, SB))
    csq = chain(w, An, ['( abs ` %s )' % c('n'), '( sqrt ` %s )' % CA2, '( sqrt ` ( %s x. %s ) )' % (AN('n'), b('n')), '( %s x. %s )' % (SA, SB)], [sq1, sq2, sq3])
    saq = dn('syl', [dn('jca', [anr, an0], '( %s e. RR /\\ 0 <_ %s )' % (AN('n'), AN('n'))), w.inst('resqrtth')], '( %s ^ 2 ) = %s' % (SA, AN('n')))
    sbq = dn('syl', [bpair, w.inst('resqrtth')], '( %s ^ 2 ) = %s' % (SB, b('n')))
    # ---------------- j-level: phases
    Aj = '( ph /\\ j e. J )'
    dj = mk(w, Aj)
    Ajn = '( %s /\\ n e. M )' % Aj
    h2a = w.s([h2], 'anassrs', '( %s -> %s e. CC )' % (Ajn, x('j', 'n')))
    toAn = D(w, Ajn, 'jca', [w.s([], 'simpll', '( %s -> ph )' % Ajn), w.s([], 'simpr', '( %s -> n e. M )' % Ajn)], An)
    cnj = w.s([toAn, cn], 'syl', '( %s -> %s e. CC )' % (Ajn, c('n')))
    cxc = D(w, Ajn, 'mulcld', [cnj, h2a], '%s e. CC' % cx('j', 'n'))
    mfj = lift(w, mf, Aj)
    Fc = dj('fsumcl', [mfj, cxc], '%s e. CC' % F('j'))
    Fp = w.s([w.s([w.s([], 'fveq2', '( p = n -> ( C ` p ) = ( C ` n ) )'), w.s([], 'fveq2', '( p = n -> ( ( X ` j ) ` p ) = ( ( X ` j ) ` n ) )')], 'oveq12d',
                  '( p = n -> %s = %s )' % (cx('j', 'p'), cx('j', 'n')))], 'cbvsumv', '%s = %s' % (F('j', 'p'), F('j')))
    Fpc = dj('eqeltrd', [a1(w, Aj, 'idi' if False else 'eqid', '') if False else w.s([Fp], 'a1i', '( %s -> %s = %s )' % (Aj, F('j', 'p'), F('j'))), Fc], '%s e. CC' % F('j', 'p'))
    # substitution i -> j in PHI
    s1 = w.s([w.s([w.s([], 'fveq2', '( i = j -> ( X ` i ) = ( X ` j ) )')], 'fveq1d', '( i = j -> ( ( X ` i ) ` p ) = ( ( X ` j ) ` p ) )')], 'oveq2d',
             '( i = j -> %s = %s )' % (cx('i', 'p'), cx('j', 'p')))
    s2 = w.s([s1], 'sumeq2sdv', '( i = j -> %s = %s )' % (F('i', 'p'), F('j', 'p')))
    s3 = w.s([s2], 'eqeq1d', '( i = j -> ( %s = 0 <-> %s = 0 ) )' % (F('i', 'p'), F('j', 'p')))
    s4 = w.s([w.s([s2], 'fveq2d', '( i = j -> ( abs ` %s ) = ( abs ` %s ) )' % (F('i', 'p'), F('j', 'p'))), s2], 'oveq12d',
             '( i = j -> ( ( abs ` %s ) / %s ) = ( ( abs ` %s ) / %s ) )' % (F('i', 'p'), F('i', 'p'), F('j', 'p'), F('j', 'p')))
    s5 = w.s([s3, s4], 'ifbieq2d', '( i = j -> %s = %s )' % (PHI('i'), PHI('j')))
    phex = a1(w, Aj, 'ifex', '%s e. _V' % PHI('j'), [w.s([], '1ex', '1 e. _V'), w.s([], 'ovex', '( ( abs ` %s ) / %s ) e. _V' % (F('j', 'p'), F('j', 'p')))])
    zv = dj('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Aj, ZF, ZF)), w.s([s5], 'adantl', '( ( %s /\\ i = j ) -> %s = %s )' % (Aj, PHI('i'), PHI('j'))),
                       w.s([], 'simpr', '( %s -> j e. J )' % Aj), phex], '%s = %s' % (z('j'), PHI('j')))
    FP = F('j', 'p')
    # case F = 0
    A0 = '( %s /\\ %s = 0 )' % (Aj, FP)
    d0 = mk(w, A0)
    f0 = w.s([], 'simpr', '( %s -> %s = 0 )' % (A0, FP))
    z1 = d0('eqtrd', [lift(w, zv, A0), d0('iftrued', [f0], '%s = 1' % PHI('j'))], '%s = 1' % z('j'))
    zc0 = d0('eqeltrd', [z1, a1(w, A0, 'ax-1cn', '1 e. CC')], '%s e. CC' % z('j'))
    zF0 = d0('eqtr4d', [d0('eqtrd', [d0('oveq12d', [z1, f0], '( %s x. %s ) = ( 1 x. 0 )' % (z('j'), FP)), a1(w, A0, 'mul01i' if False else 'ax-mp', '( 1 x. 0 ) = 0', [w.s([], 'ax-1cn', '1 e. CC'), w.inst('mul01')])],
                                    '( %s x. %s ) = 0' % (z('j'), FP)),
                        d0('eqtrd', [d0('fveq2d', [f0], '( abs ` %s ) = ( abs ` 0 )' % FP), a1(w, A0, 'abs0', '( abs ` 0 ) = 0')], '( abs ` %s ) = 0' % FP)],
               '( %s x. %s ) = ( abs ` %s )' % (z('j'), FP, FP))
    za0 = d0('eqtrd', [d0('fveq2d', [z1], '( abs ` %s ) = ( abs ` 1 )' % z('j')), a1(w, A0, 'abs1', '( abs ` 1 ) = 1')], '( abs ` %s ) = 1' % z('j'))
    c0_ = d0('3jca', [zc0, zF0, za0], '( %s e. CC /\\ ( %s x. %s ) = ( abs ` %s ) /\\ ( abs ` %s ) = 1 )' % (z('j'), z('j'), FP, FP, z('j')))
    # case F =/= 0
    A1 = '( %s /\\ %s =/= 0 )' % (Aj, FP)
    d1 = mk(w, A1)
    fn = w.s([], 'simpr', '( %s -> %s =/= 0 )' % (A1, FP))
    fpc1 = lift(w, Fpc, A1)
    AF = '( abs ` %s )' % FP
    afc = d1('recnd', [d1('abscld', [fpc1], '%s e. RR' % AF)], '%s e. CC' % AF)
    zq = d1('eqtrd', [lift(w, zv, A1), d1('syl', [fn, w.inst('ifnefalse')], '%s = ( %s / %s )' % (PHI('j'), AF, FP))], '%s = ( %s / %s )' % (z('j'), AF, FP))
    zc1 = d1('eqeltrd', [zq, d1('divcld', [afc, fpc1, fn], '( %s / %s ) e. CC' % (AF, FP))], '%s e. CC' % z('j'))
    zF1 = d1('eqtrd', [d1('oveq1d', [zq], '( %s x. %s ) = ( ( %s / %s ) x. %s )' % (z('j'), FP, AF, FP, FP)), d1('divcan1d', [afc, fpc1, fn], '( ( %s / %s ) x. %s ) = %s' % (AF, FP, FP, AF))],
              '( %s x. %s ) = %s' % (z('j'), FP, AF))
    afr = d1('abscld', [fpc1], '%s e. RR' % AF)
    za1 = chain(w, A1, ['( abs ` %s )' % z('j'), '( abs ` ( %s / %s ) )' % (AF, FP), '( ( abs ` %s ) / %s )' % (AF, AF), '( %s / %s )' % (AF, AF), '1'],
                [d1('fveq2d', [zq], '( abs ` %s ) = ( abs ` ( %s / %s ) )' % (z('j'), AF, FP)), d1('absdivd', [afc, fpc1, fn], '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / %s )' % (AF, FP, AF, AF)),
                 d1('oveq1d', [d1('absidd', [afr, d1('absge0d', [fpc1], '0 <_ %s' % AF)], '( abs ` %s ) = %s' % (AF, AF))], '( ( abs ` %s ) / %s ) = ( %s / %s )' % (AF, AF, AF, AF)),
                 d1('dividd', [afc, d1('absne0d', [fpc1, fn], '%s =/= 0' % AF)], '( %s / %s ) = 1' % (AF, AF))])
    c1_ = d1('3jca', [zc1, zF1, za1], '( %s e. CC /\\ ( %s x. %s ) = ( abs ` %s ) /\\ ( abs ` %s ) = 1 )' % (z('j'), z('j'), FP, FP, z('j')))
    zall = dj('pm2.61dane', [c0_, c1_], '( %s e. CC /\\ ( %s x. %s ) = ( abs ` %s ) /\\ ( abs ` %s ) = 1 )' % (z('j'), z('j'), FP, FP, z('j')))
    zc = dj('simp1d', [zall], '%s e. CC' % z('j'))
    za = dj('simp3d', [zall], '( abs ` %s ) = 1' % z('j'))
    Fpj = w.s([Fp], 'a1i', '( %s -> %s = %s )' % (Aj, FP, F('j')))
    zF = dj('eqtr3d' if False else 'eqtrd', [dj('oveq2d', [dj('eqcomd', [Fpj], '%s = %s' % (F('j'), FP))], '( %s x. %s ) = ( %s x. %s )' % (z('j'), F('j'), z('j'), FP)),
                                             dj('eqtrd', [dj('simp2d', [zall], '( %s x. %s ) = ( abs ` %s )' % (z('j'), FP, FP)), dj('fveq2d', [Fpj], '( abs ` %s ) = ( abs ` %s )' % (FP, F('j')))],
                                                '( %s x. %s ) = ( abs ` %s )' % (z('j'), FP, F('j')))], '( %s x. %s ) = ( abs ` %s )' % (z('j'), F('j'), F('j')))
    def re(st, target):
        """( target -> X ) from st ( source -> X ) with every leaf conjunct of source a conjunct of target"""
        from cl import formula_of
        src, concl = split_imp(formula_of(w, st))
        if src == target:
            return st
        return w.s([proj(w, target, src), st], 'syl', '( %s -> %s )' % (target, concl))
    # ---------------- step 3: sum_j |F_j| = sum_n c(n) G(n)
    SUMF = 'sum_ j e. J ( abs ` %s )' % F('j')
    zFr = dj('eqcomd', [zF], '( abs ` %s ) = ( %s x. %s )' % (F('j'), z('j'), F('j')))
    e1 = d('sumeq2dv', [zFr], '%s = sum_ j e. J ( %s x. %s )' % (SUMF, z('j'), F('j')))
    W_ = '( %s x. %s )' % (z('j'), cx('j', 'n'))
    e2 = dj('fsummulc2', [mfj, zc, cxc], '( %s x. %s ) = sum_ n e. M %s' % (z('j'), F('j'), W_))
    e2s = d('sumeq2dv', [e2], 'sum_ j e. J ( %s x. %s ) = sum_ j e. J sum_ n e. M %s' % (z('j'), F('j'), W_))
    Ajn2 = '( ph /\\ ( j e. J /\\ n e. M ) )'
    wc_ = D(w, Ajn, 'mulcld', [lift(w, zc, Ajn), cxc], '%s e. CC' % W_)
    e3 = d('fsumcom', [jf, mf, w.s([wc_], 'anasss', '( %s -> %s e. CC )' % (Ajn2, W_))], 'sum_ j e. J sum_ n e. M %s = sum_ n e. M sum_ j e. J %s' % (W_, W_))
    Anj = '( %s /\\ j e. J )' % An
    zcn = re(zc, Anj); xcn = re(h2a, Anj); ccn = re(cnj, Anj)
    zx = '( %s x. %s )' % (z('j'), x('j', 'n'))
    zxc = D(w, Anj, 'mulcld', [zcn, xcn], '%s e. CC' % zx)
    clr = Closure(w, Anj, {z('j'): ('CC', zcn), c('n'): ('CC', ccn), x('j', 'n'): ('CC', xcn)})
    for a_ in [z('j'), c('n'), x('j', 'n')]:
        clr.atom(a_)
    e4a = ringeq(w, Anj, W_, '( %s x. %s )' % (c('n'), zx), clr)
    e4b = dn('sumeq2dv', [e4a], 'sum_ j e. J %s = sum_ j e. J ( %s x. %s )' % (W_, c('n'), zx))
    jfn = lift(w, jf, An)
    e4c = dn('fsummulc2', [jfn, cn, zxc], '( %s x. %s ) = sum_ j e. J ( %s x. %s )' % (c('n'), G('n'), c('n'), zx))
    e4 = dn('eqtr4d', [e4b, e4c], 'sum_ j e. J %s = ( %s x. %s )' % (W_, c('n'), G('n')))
    e4s = d('sumeq2dv', [e4], 'sum_ n e. M sum_ j e. J %s = sum_ n e. M ( %s x. %s )' % (W_, c('n'), G('n')))
    SC = 'sum_ n e. M ( %s x. %s )' % (c('n'), G('n'))
    eqS = chain(w, A, [SUMF, 'sum_ j e. J ( %s x. %s )' % (z('j'), F('j')), 'sum_ j e. J sum_ n e. M %s' % W_, 'sum_ n e. M sum_ j e. J %s' % W_, SC], [e1, e2s, e3, e4s])
    sfr = dj('abscld', [Fc], '( abs ` %s ) e. RR' % F('j'))
    sr = d('fsumrecl', [jf, sfr], '%s e. RR' % SUMF)
    s0 = d('fsumge0', [jf, sfr, dj('absge0d', [Fc], '0 <_ ( abs ` %s )' % F('j'))], '0 <_ %s' % SUMF)
    # ---------------- step 4: S <_ P
    Gc = dn('fsumcl', [jfn, zxc], '%s e. CC' % G('n'))
    cG = dn('mulcld', [cn, Gc], '( %s x. %s ) e. CC' % (c('n'), G('n')))
    aS = d('eqtr3d', [d('absidd', [sr, s0], '( abs ` %s ) = %s' % (SUMF, SUMF)), d('fveq2d', [eqS], '( abs ` %s ) = ( abs ` %s )' % (SUMF, SC))], '%s = ( abs ` %s )' % (SUMF, SC)) if False else \
        d('eqtr3d', [d('absidd', [sr, s0], '( abs ` %s ) = %s' % (SUMF, SUMF)), d('fveq2d', [eqS], '( abs ` %s ) = ( abs ` %s )' % (SUMF, SC))], '%s = ( abs ` %s )' % (SUMF, SC))
    fa = d('fsumabs', [mf, cG], '( abs ` %s ) <_ sum_ n e. M ( abs ` ( %s x. %s ) )' % (SC, c('n'), G('n')))
    AG = '( abs ` %s )' % G('n')
    pm = dn('absmuld', [cn, Gc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. %s )' % (c('n'), G('n'), c('n'), AG))
    P_ = 'sum_ n e. M ( ( abs ` %s ) x. %s )' % (c('n'), AG)
    pe = d('sumeq2dv', [pm], 'sum_ n e. M ( abs ` ( %s x. %s ) ) = %s' % (c('n'), G('n'), P_))
    SP = d('breqtrd', [d('eqbrtrd', [aS, fa], '%s <_ sum_ n e. M ( abs ` ( %s x. %s ) )' % (SUMF, c('n'), G('n'))), pe], '%s <_ %s' % (SUMF, P_))
    agr = dn('abscld', [Gc], '%s e. RR' % AG); ag0 = dn('absge0d', [Gc], '0 <_ %s' % AG)
    pr_ = dn('remulcld', [acr, agr], '( ( abs ` %s ) x. %s ) e. RR' % (c('n'), AG))
    Pr = d('fsumrecl', [mf, pr_], '%s e. RR' % P_)
    # ---------------- step 5: Cauchy-Schwarz
    SBG = '( %s x. %s )' % (SB, AG)
    sbgr = dn('remulcld', [sbr, agr], '%s e. RR' % SBG)
    p1 = dn('oveq1d', [csq], '( ( abs ` %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (c('n'), AG, SA, SB, AG))
    p2 = dn('mulassd', [dn('recnd', [sar], '%s e. CC' % SA), dn('recnd', [sbr], '%s e. CC' % SB), dn('recnd', [agr], '%s e. CC' % AG)], '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (SA, SB, AG, SA, SBG))
    pP = d('sumeq2dv', [dn('eqtrd', [p1, p2], '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (c('n'), AG, SA, SBG))], '%s = sum_ n e. M ( %s x. %s )' % (P_, SA, SBG))
    cs = d('csbren', [mf, sar, sbgr], '( sum_ n e. M ( %s x. %s ) ^ 2 ) <_ ( sum_ n e. M ( %s ^ 2 ) x. sum_ n e. M ( %s ^ 2 ) )' % (SA, SBG, SA, SBG))
    AN_ = 'sum_ n e. M %s' % AN('n')
    T_ = 'sum_ n e. M ( %s x. ( %s ^ 2 ) )' % (b('n'), AG)
    ca = d('sumeq2dv', [saq], 'sum_ n e. M ( %s ^ 2 ) = %s' % (SA, AN_))
    cb_ = d('sumeq2dv', [dn('eqtrd', [dn('sqmuld', [dn('recnd', [sbr], '%s e. CC' % SB), dn('recnd', [agr], '%s e. CC' % AG)], '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (SBG, SB, AG)),
                                     dn('oveq1d', [sbq], '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) = ( %s x. ( %s ^ 2 ) )' % (SB, AG, b('n'), AG))], '( %s ^ 2 ) = ( %s x. ( %s ^ 2 ) )' % (SBG, b('n'), AG))],
             'sum_ n e. M ( %s ^ 2 ) = %s' % (SBG, T_))
    P2 = '( %s ^ 2 )' % P_
    cs2 = d('breqtrd', [d('eqbrtrd', [d('oveq1d', [pP], '%s = ( sum_ n e. M ( %s x. %s ) ^ 2 )' % (P2, SA, SBG)), cs],
                                   '%s <_ ( sum_ n e. M ( %s ^ 2 ) x. sum_ n e. M ( %s ^ 2 ) )' % (P2, SA, SBG)),
                         d('oveq12d', [ca, cb_], '( sum_ n e. M ( %s ^ 2 ) x. sum_ n e. M ( %s ^ 2 ) ) = ( %s x. %s )' % (SA, SBG, AN_, T_))],
            '%s <_ ( %s x. %s )' % (P2, AN_, T_))
    # ---------------- step 6: T = sum_j sum_k w_jk Gram_jk and T <_ sum sum |Gram|
    Ank = '( %s /\\ k e. J )' % An
    zk = z('k'); xk = x('k', 'n')
    zkc = w.s([w.s([], 'simpr', '( %s -> k e. J )' % Ank), w.s([w.s([], 'fveq2', '( j = k -> %s = %s )' % (z('j'), zk))], 'idi', '( j = k -> %s = %s )' % (z('j'), zk))], 'idi', '') if False else None
    # z(k), x(k,n) in CC under Ank: rename j -> k in the Anj facts
    def ren_k(st, fj, fk):
        """( Ank -> fk ) from st ( Anj -> fj ) by rspcv on j"""
        ra = D(w, An, 'ralrimiva', [st], 'A. j e. J %s' % fj)
        e = w.s([], 'idi', '') if False else None
        return ra
    zra = D(w, An, 'ralrimiva', [zcn], 'A. j e. J %s e. CC' % z('j'))
    xra = D(w, An, 'ralrimiva', [xcn], 'A. j e. J %s e. CC' % x('j', 'n'))
    fz = w.s([w.s([w.s([], 'fveq2', '( j = k -> %s = %s )' % (z('j'), zk))], 'eleq1d', '( j = k -> ( %s e. CC <-> %s e. CC ) )' % (z('j'), zk))], 'rspcv',
             '( k e. J -> ( A. j e. J %s e. CC -> %s e. CC ) )' % (z('j'), zk))
    fx = w.s([w.s([w.s([w.s([], 'fveq2', '( j = k -> ( X ` j ) = ( X ` k ) )')], 'fveq1d', '( j = k -> %s = %s )' % (x('j', 'n'), xk))], 'eleq1d',
                  '( j = k -> ( %s e. CC <-> %s e. CC ) )' % (x('j', 'n'), xk))], 'rspcv', '( k e. J -> ( A. j e. J %s e. CC -> %s e. CC ) )' % (x('j', 'n'), xk))
    kin = w.s([], 'simpr', '( %s -> k e. J )' % Ank)
    zkc = D(w, Ank, 'sylc', [kin, lift(w, zra, Ank), fz], '%s e. CC' % zk)
    xkc = D(w, Ank, 'sylc', [kin, lift(w, xra, Ank), fx], '%s e. CC' % xk)
    zxk = '( %s x. %s )' % (zk, xk)
    zxkc = D(w, Ank, 'mulcld', [zkc, xkc], '%s e. CC' % zxk)
    Gk = 'sum_ k e. J %s' % zxk
    gg = w.s([w.s([w.s([], 'fveq2', '( j = k -> %s = %s )' % (z('j'), zk)), w.s([w.s([], 'fveq2', '( j = k -> ( X ` j ) = ( X ` k ) )')], 'fveq1d', '( j = k -> %s = %s )' % (x('j', 'n'), xk))],
                  'oveq12d', '( j = k -> %s = %s )' % (zx_ := '( %s x. %s )' % (z('j'), x('j', 'n')), zxk))], 'cbvsumv', '%s = %s' % (G('n'), Gk))
    avs = dn('syl', [Gc, w.inst('absvalsq')], '( %s ^ 2 ) = ( %s x. ( * ` %s ) )' % (AG, G('n'), G('n')))
    cjg = dn('eqtrd', [dn('fveq2d', [w.s([gg], 'a1i', '( %s -> %s = %s )' % (An, G('n'), Gk))], '( * ` %s ) = ( * ` %s )' % (G('n'), Gk)),
                       dn('fsumcj', [jfn, zxkc], '( * ` %s ) = sum_ k e. J ( * ` %s )' % (Gk, zxk))], '( * ` %s ) = sum_ k e. J ( * ` %s )' % (G('n'), zxk))
    cjkc = D(w, Ank, 'cjcld', [zxkc], '( * ` %s ) e. CC' % zxk)
    f2 = dn('fsum2mul', [jfn, jfn, zxc, cjkc], 'sum_ j e. J sum_ k e. J ( %s x. ( * ` %s ) ) = ( %s x. sum_ k e. J ( * ` %s ) )' % (zx_, zxk, G('n'), zxk))
    gcg = dn('eqtr4d', [dn('oveq2d', [cjg], '( %s x. ( * ` %s ) ) = ( %s x. sum_ k e. J ( * ` %s ) )' % (G('n'), G('n'), G('n'), zxk)), f2],
             '( %s x. ( * ` %s ) ) = sum_ j e. J sum_ k e. J ( %s x. ( * ` %s ) )' % (G('n'), G('n'), zx_, zxk))
    bnc = dn('recnd', [br], '%s e. CC' % b('n'))
    Q_ = lambda: '( %s x. ( * ` %s ) )' % (zx_, zxk)
    Anjk = '( %s /\\ k e. J )' % Anj
    qc = D(w, Anjk, 'mulcld', [lift(w, zxc, Anjk), re(cjkc, Anjk)], '%s e. CC' % Q_())
    m1 = D(w, Anj, 'fsummulc2', [lift(w, jfn, Anj), lift(w, bnc, Anj), qc], '( %s x. sum_ k e. J %s ) = sum_ k e. J ( %s x. %s )' % (b('n'), Q_(), b('n'), Q_()))
    sqc = D(w, Anj, 'fsumcl', [lift(w, jfn, Anj), qc], 'sum_ k e. J %s e. CC' % Q_())
    m0 = dn('fsummulc2', [jfn, bnc, sqc], '( %s x. sum_ j e. J sum_ k e. J %s ) = sum_ j e. J ( %s x. sum_ k e. J %s )' % (b('n'), Q_(), b('n'), Q_()))
    WJK = '( ( %s x. ( * ` %s ) ) x. %s )' % (z('j'), zk, GR('j', 'k', 'n'))
    cjm = D(w, Anjk, 'cjmuld', [re(zkc, Anjk), re(xkc, Anjk)], '( * ` %s ) = ( ( * ` %s ) x. ( * ` %s ) )' % (zxk, zk, xk))
    czk = D(w, Anjk, 'cjcld', [re(zkc, Anjk)], '( * ` %s ) e. CC' % zk); cxk = D(w, Anjk, 'cjcld', [re(xkc, Anjk)], '( * ` %s ) e. CC' % xk)
    clq = Closure(w, Anjk, {b('n'): ('CC', lift(w, lift(w, bnc, Anj), Anjk)), z('j'): ('CC', lift(w, zcn, Anjk)), x('j', 'n'): ('CC', lift(w, xcn, Anjk)), '( * ` %s )' % zk: ('CC', czk), '( * ` %s )' % xk: ('CC', cxk)})
    for a_ in [b('n'), z('j'), x('j', 'n'), '( * ` %s )' % zk, '( * ` %s )' % xk]:
        clq.atom(a_)
    t1 = D(w, Anjk, 'oveq2d', [D(w, Anjk, 'oveq2d', [cjm], '%s = ( %s x. ( ( * ` %s ) x. ( * ` %s ) ) )' % (Q_(), zx_, zk, xk))],
           '( %s x. %s ) = ( %s x. ( %s x. ( ( * ` %s ) x. ( * ` %s ) ) ) )' % (b('n'), Q_(), b('n'), zx_, zk, xk))
    t2 = ringeq(w, Anjk, '( %s x. ( %s x. ( ( * ` %s ) x. ( * ` %s ) ) ) )' % (b('n'), zx_, zk, xk), WJK, clq)
    tjk = D(w, Anjk, 'eqtrd', [t1, t2], '( %s x. %s ) = %s' % (b('n'), Q_(), WJK))
    sk = D(w, Anj, 'eqtrd', [m1, D(w, Anj, 'sumeq2dv', [tjk], 'sum_ k e. J ( %s x. %s ) = sum_ k e. J %s' % (b('n'), Q_(), WJK))],
           '( %s x. sum_ k e. J %s ) = sum_ k e. J %s' % (b('n'), Q_(), WJK))
    sj = dn('eqtrd', [m0, dn('sumeq2dv', [sk], 'sum_ j e. J ( %s x. sum_ k e. J %s ) = sum_ j e. J sum_ k e. J %s' % (b('n'), Q_(), WJK))],
            '( %s x. sum_ j e. J sum_ k e. J %s ) = sum_ j e. J sum_ k e. J %s' % (b('n'), Q_(), WJK))
    pern = chain(w, An, ['( %s x. ( %s ^ 2 ) )' % (b('n'), AG), '( %s x. ( %s x. ( * ` %s ) ) )' % (b('n'), G('n'), G('n')), '( %s x. sum_ j e. J sum_ k e. J %s )' % (b('n'), Q_()), 'sum_ j e. J sum_ k e. J %s' % WJK],
                 [dn('oveq2d', [avs], '( %s x. ( %s ^ 2 ) ) = ( %s x. ( %s x. ( * ` %s ) ) )' % (b('n'), AG, b('n'), G('n'), G('n'))),
                  dn('oveq2d', [gcg], '( %s x. ( %s x. ( * ` %s ) ) ) = ( %s x. sum_ j e. J sum_ k e. J %s )' % (b('n'), G('n'), G('n'), b('n'), Q_())), sj])
    T1 = d('sumeq2dv', [pern], '%s = sum_ n e. M sum_ j e. J sum_ k e. J %s' % (T_, WJK))
    # swaps
    wjkc = D(w, Anjk, 'mulcld', [D(w, Anjk, 'mulcld', [lift(w, zcn, Anjk), czk], '( %s x. ( * ` %s ) ) e. CC' % (z('j'), zk)),
                                 D(w, Anjk, 'mulcld', [D(w, Anjk, 'mulcld', [lift(w, lift(w, bnc, Anj), Anjk), lift(w, xcn, Anjk)], '( %s x. %s ) e. CC' % (b('n'), x('j', 'n'))), cxk],
                                   '%s e. CC' % GR('j', 'k', 'n'))], '%s e. CC' % WJK)
    skc = D(w, Anj, 'fsumcl', [lift(w, jfn, Anj), wjkc], 'sum_ k e. J %s e. CC' % WJK)
    Anj2 = '( ph /\\ ( n e. M /\\ j e. J ) )'
    T2 = d('fsumcom', [mf, jf, w.s([skc], 'anasss', '( %s -> sum_ k e. J %s e. CC )' % (Anj2, WJK))],
           'sum_ n e. M sum_ j e. J sum_ k e. J %s = sum_ j e. J sum_ n e. M sum_ k e. J %s' % (WJK, WJK))
    # per j: sum_n sum_k = sum_k sum_n
    Ajnk = '( ( %s /\\ n e. M ) /\\ k e. J )' % Aj
    wjkc2 = re(wjkc, Ajnk)
    Ajnk2 = '( %s /\\ ( n e. M /\\ k e. J ) )' % Aj
    T3j = dj('fsumcom', [mfj, lift(w, jf, Aj), w.s([wjkc2], 'anasss', '( %s -> %s e. CC )' % (Ajnk2, WJK))],
             'sum_ n e. M sum_ k e. J %s = sum_ k e. J sum_ n e. M %s' % (WJK, WJK))
    T3 = d('sumeq2dv', [T3j], 'sum_ j e. J sum_ n e. M sum_ k e. J %s = sum_ j e. J sum_ k e. J sum_ n e. M %s' % (WJK, WJK))
    # per (j,k): sum_n w GR = w Gram
    Ajk = '( %s /\\ k e. J )' % Aj
    WW = '( %s x. ( * ` %s ) )' % (z('j'), zk)
    Ajkn = '( %s /\\ n e. M )' % Ajk
    grc = D(w, Ajkn, 'mulcld', [D(w, Ajkn, 'mulcld', [re(bnc, Ajkn), re(xcn, Ajkn)], '( %s x. %s ) e. CC' % (b('n'), x('j', 'n'))), D(w, Ajkn, 'cjcld', [re(xkc, Ajkn)], '( * ` %s ) e. CC' % xk)],
            '%s e. CC' % GR('j', 'k', 'n'))
    zkc_jk = re(zkc, Ajkn) if False else None
    # z(k) under Ajk: from zc by rspcv on j
    zraA = d('ralrimiva', [zc], 'A. j e. J %s e. CC' % z('j'))
    zkA = D(w, Ajk, 'sylc', [w.s([], 'simpr', '( %s -> k e. J )' % Ajk), lift(w, zraA, Ajk), fz], '%s e. CC' % zk)
    wwc = D(w, Ajk, 'mulcld', [lift(w, zc, Ajk), D(w, Ajk, 'cjcld', [zkA], '( * ` %s ) e. CC' % zk)], '%s e. CC' % WW)
    fm = D(w, Ajk, 'fsummulc2', [lift(w, mfj, Ajk), wwc, grc], '( %s x. %s ) = sum_ n e. M %s' % (WW, GRAM('j', 'k'), WJK))
    T4 = d('sumeq2dv', [dj('sumeq2dv', [D(w, Ajk, 'eqcomd', [fm], 'sum_ n e. M %s = ( %s x. %s )' % (WJK, WW, GRAM('j', 'k')))],
                           'sum_ k e. J sum_ n e. M %s = sum_ k e. J ( %s x. %s )' % (WJK, WW, GRAM('j', 'k')))],
           'sum_ j e. J sum_ k e. J sum_ n e. M %s = sum_ j e. J sum_ k e. J ( %s x. %s )' % (WJK, WW, GRAM('j', 'k')))
    TT = 'sum_ j e. J sum_ k e. J ( %s x. %s )' % (WW, GRAM('j', 'k'))
    Teq = chain(w, A, [T_, 'sum_ n e. M sum_ j e. J sum_ k e. J %s' % WJK, 'sum_ j e. J sum_ n e. M sum_ k e. J %s' % WJK, 'sum_ j e. J sum_ k e. J sum_ n e. M %s' % WJK, TT], [T1, T2, T3, T4])
    tn_r = dn('remulcld', [br, dn('resqcld', [agr], '( %s ^ 2 ) e. RR' % AG)], '( %s x. ( %s ^ 2 ) ) e. RR' % (b('n'), AG))
    tn_0 = dn('mulge0d', [br, dn('resqcld', [agr], '( %s ^ 2 ) e. RR' % AG), b0, dn('sqge0d', [agr], '0 <_ ( %s ^ 2 )' % AG)], '0 <_ ( %s x. ( %s ^ 2 ) )' % (b('n'), AG))
    Tr = d('fsumrecl', [mf, tn_r], '%s e. RR' % T_); T0 = d('fsumge0', [mf, tn_r, tn_0], '0 <_ %s' % T_)
    gramc = D(w, Ajk, 'fsumcl', [lift(w, mfj, Ajk), grc], '%s e. CC' % GRAM('j', 'k'))
    wg = D(w, Ajk, 'mulcld', [wwc, gramc], '( %s x. %s ) e. CC' % (WW, GRAM('j', 'k')))
    SKW = 'sum_ k e. J ( %s x. %s )' % (WW, GRAM('j', 'k'))
    skwc = dj('fsumcl', [lift(w, jf, Aj), wg], '%s e. CC' % SKW)
    ab1 = d('fsumabs', [jf, skwc], '( abs ` %s ) <_ sum_ j e. J ( abs ` %s )' % (TT, SKW))
    ab2j = dj('fsumabs', [lift(w, jf, Aj), wg], '( abs ` %s ) <_ sum_ k e. J ( abs ` ( %s x. %s ) )' % (SKW, WW, GRAM('j', 'k')))
    AGR = '( abs ` %s )' % GRAM('j', 'k')
    awg0 = D(w, Ajk, 'eqtrd', [D(w, Ajk, 'absmuld', [wwc, gramc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. %s )' % (WW, GRAM('j', 'k'), WW, AGR)),
                             D(w, Ajk, 'oveq1d', [chain(w, Ajk, ['( abs ` %s )' % WW, '( ( abs ` %s ) x. ( abs ` ( * ` %s ) ) )' % (z('j'), zk), '( 1 x. 1 )', '1'],
                                                        [D(w, Ajk, 'absmuld', [lift(w, zc, Ajk), D(w, Ajk, 'cjcld', [zkA], '( * ` %s ) e. CC' % zk)], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( * ` %s ) ) )' % (WW, z('j'), zk)),
                                                         D(w, Ajk, 'oveq12d', [lift(w, za, Ajk),
                                                                               D(w, Ajk, 'eqtrd', [D(w, Ajk, 'abscjd', [zkA], '( abs ` ( * ` %s ) ) = ( abs ` %s )' % (zk, zk)),
                                                                                                   D(w, Ajk, 'sylc', [w.s([], 'simpr', '( %s -> k e. J )' % Ajk), lift(w, d('ralrimiva', [za], 'A. j e. J ( abs ` %s ) = 1' % z('j')), Ajk),
                                                                                                                      w.s([w.s([w.s([w.s([], 'fveq2', '( j = k -> %s = %s )' % (z('j'), zk))], 'fveq2d', '( j = k -> ( abs ` %s ) = ( abs ` %s ) )' % (z('j'), zk))],
                                                                                                                               'eqeq1d', '( j = k -> ( ( abs ` %s ) = 1 <-> ( abs ` %s ) = 1 ) )' % (z('j'), zk))], 'rspcv',
                                                                                                                          '( k e. J -> ( A. j e. J ( abs ` %s ) = 1 -> ( abs ` %s ) = 1 ) )' % (z('j'), zk))], '( abs ` %s ) = 1' % zk)],
                                                                                  '( abs ` ( * ` %s ) ) = 1' % zk)], '( ( abs ` %s ) x. ( abs ` ( * ` %s ) ) ) = ( 1 x. 1 )' % (z('j'), zk)),
                                                         a1(w, Ajk, '1t1e1', '( 1 x. 1 ) = 1')])],
                                '( ( abs ` %s ) x. %s ) = ( 1 x. %s )' % (WW, AGR, AGR))], '( abs ` ( %s x. %s ) ) = ( 1 x. %s )' % (WW, GRAM('j', 'k'), AGR))
    awg = D(w, Ajk, 'eqtrd', [awg0,
                             D(w, Ajk, 'mullidd', [D(w, Ajk, 'recnd', [D(w, Ajk, 'abscld', [gramc], '%s e. RR' % AGR)], '%s e. CC' % AGR)], '( 1 x. %s ) = %s' % (AGR, AGR))], '( abs ` ( %s x. %s ) ) = %s' % (WW, GRAM('j', 'k'), AGR))
    ab2 = dj('breqtrd', [ab2j, dj('sumeq2dv', [awg], 'sum_ k e. J ( abs ` ( %s x. %s ) ) = sum_ k e. J %s' % (WW, GRAM('j', 'k'), AGR))], '( abs ` %s ) <_ sum_ k e. J %s' % (SKW, AGR))
    agrr = D(w, Ajk, 'abscld', [gramc], '%s e. RR' % AGR)
    skr = dj('fsumrecl', [lift(w, jf, Aj), agrr], 'sum_ k e. J %s e. RR' % AGR)
    ab3 = d('fsumle', [jf, dj('abscld', [skwc], '( abs ` %s ) e. RR' % SKW), skr, ab2], 'sum_ j e. J ( abs ` %s ) <_ sum_ j e. J sum_ k e. J %s' % (SKW, AGR))
    QQ = 'sum_ j e. J sum_ k e. J %s' % AGR
    Tabs = d('eqtr3d', [d('absidd', [Tr, T0], '( abs ` %s ) = %s' % (T_, T_)), d('fveq2d', [Teq], '( abs ` %s ) = ( abs ` %s )' % (T_, TT))], '%s = ( abs ` %s )' % (T_, TT))
    TQ0 = d('eqbrtrd', [Tabs, ab1], '%s <_ sum_ j e. J ( abs ` %s )' % (T_, SKW))
    TQ = d('letrd', [Tr, d('fsumrecl', [jf, dj('abscld', [skwc], '( abs ` %s ) e. RR' % SKW)], 'sum_ j e. J ( abs ` %s ) e. RR' % SKW), d('fsumrecl', [jf, skr], '%s e. RR' % QQ), TQ0, ab3],
            '%s <_ %s' % (T_, QQ))
    # ---------------- step 7
    ANr = d('fsumrecl', [mf, anr], '%s e. RR' % AN_); AN0 = d('fsumge0', [mf, anr, an0], '0 <_ %s' % AN_)
    ss = d('lemul12ad', [sr, Pr, sr, Pr, s0, SP, s0, SP], '( %s x. %s ) <_ ( %s x. %s )' % (SUMF, SUMF, P_, P_))
    ss2 = d('eqbrtrrd', [d('sqvald', [d('recnd', [sr], '%s e. CC' % SUMF)], '( %s ^ 2 ) = ( %s x. %s )' % (SUMF, SUMF, SUMF)), ss], '( %s ^ 2 ) <_ ( %s x. %s )' % (SUMF, P_, P_)) if False else \
        d('breqtrrd', [d('eqbrtrd', [d('sqvald', [d('recnd', [sr], '%s e. CC' % SUMF)], '( %s ^ 2 ) = ( %s x. %s )' % (SUMF, SUMF, SUMF)), ss], '( %s ^ 2 ) <_ ( %s x. %s )' % (SUMF, P_, P_)),
                       d('sqvald', [d('recnd', [Pr], '%s e. CC' % P_)], '( %s ^ 2 ) = ( %s x. %s )' % (P_, P_, P_))], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (SUMF, P_))
    last = d('lemul2ad', [Tr, d('fsumrecl', [jf, skr], '%s e. RR' % QQ), ANr, AN0, TQ], '( %s x. %s ) <_ ( %s x. %s )' % (AN_, T_, AN_, QQ))
    f1 = d('letrd', [d('resqcld', [sr], '( %s ^ 2 ) e. RR' % SUMF), d('resqcld', [Pr], '( %s ^ 2 ) e. RR' % P_), d('remulcld', [ANr, Tr], '( %s x. %s ) e. RR' % (AN_, T_)), ss2, cs2],
            '( %s ^ 2 ) <_ ( %s x. %s )' % (SUMF, AN_, T_))
    fin = d('letrd', [d('resqcld', [sr], '( %s ^ 2 ) e. RR' % SUMF), d('remulcld', [ANr, Tr], '( %s x. %s ) e. RR' % (AN_, T_)), d('remulcld', [ANr, d('fsumrecl', [jf, skr], '%s e. RR' % QQ)], '( %s x. %s ) e. RR' % (AN_, QQ)), f1, last],
             split_imp(S['gf1half'])[1])
    w.qed([fin], 'idi', S['gf1half'])
    return run(w, only)


if __name__ == '__main__':
    gen_half()
