"""Sortie C2 section 3.5a: the Schwarz-type bound from the two-point Cauchy difference."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

TPI = '( 2 x. ( _i x. _pi ) )'

# ---- abstpi ----------------------------------------------------------------
w = W('abstpi', 'The modulus of two pi i.')
t2r = w.s([], '2re', '2 e. RR')
t2c = w.s([t2r], 'recni', '2 e. CC')
pir = w.s([], 'pire', '_pi e. RR')
pic = w.s([pir], 'recni', '_pi e. CC')
ic = w.s([], 'ax-icn', '_i e. CC')
ip = w.s([ic, pic], 'mulcli', '( _i x. _pi ) e. CC')
a1 = w.s([t2c, ip], 'absmuli', '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
a2 = w.s([ic, pic], 'absmuli', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )')
ai = w.s([], 'absi', '( abs ` _i ) = 1')
pige0 = w.s([w.s([], 'pirp', '_pi e. RR+'), w.inst('rpge0')], 'ax-mp', '0 <_ _pi')
apid = w.s([pir, pige0, w.inst('absid')], 'mp2an', '( abs ` _pi ) = _pi')
a2b = w.s([a2, w.s([ai, apid], 'oveq12i', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtri',
          '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')
a2c = w.s([a2b, w.s([pic], 'mullidi', '( 1 x. _pi ) = _pi')], 'eqtri', '( abs ` ( _i x. _pi ) ) = _pi')
a2r = w.s([t2r, w.s([], '0le2', '0 <_ 2'), w.inst('absid')], 'mp2an', '( abs ` 2 ) = 2')
w.qed([a1, w.s([a2r, a2c], 'oveq12i', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. _pi )')], 'eqtri',
      '( abs ` %s ) = ( 2 x. _pi )' % TPI); run1(w)

# ---- rectintsch ------------------------------------------------------------
RQ = RE('Q'); IQ = IM('Q')
INTQ = '( Q e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RQ, RQ, RB, IA, IQ, IQ, IB)
RBDP = RBD('P', 'R'); RBDQ = RBD('Q', 'S')
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
E2 = '( ( A crect B ) \\ { P , Q } )'
KER = MP('z', E2, '( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) )')
II = RINT(KER, 'A', 'B')
C1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INTP, INTQ, HOLO)
C2 = '( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) )' % (RBDP, RBDQ)
C3 = '( ( M e. RR /\\ %s ) /\\ ( F ` P ) = 0 )' % ALF
AQ = '( abs ` ( F ` Q ) )'; DD = '( abs ` ( Q - P ) )'
L0 = '( ( 2 x. _pi ) x. %s )' % AQ
RS = '( R x. S )'
TT = '( ( ( 2 x. M ) x. %s ) x. %s )' % (PER, DD)

w = W('rectintsch', 'Schwarz-type bound: a function holomorphic on a rectangle and vanishing at a strictly interior point P is small at a second strictly interior point Q, the constant coming from the two-point Cauchy estimate.')
A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1))
c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
mal = w.s([c3, w.inst('simpl')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
fp0 = w.s([c3, w.inst('simpr')], 'syl', '( %s -> ( F ` P ) = 0 )' % A0)
mr = w.s([mal, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
rb1 = w.s([c2, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
rb2 = w.s([c2, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ 0 < S ) )' % (A0, RBDQ))
rr = w.s([w.s([rb1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
sr = w.s([w.s([rb2, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDQ)), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
rp = w.s([rb1, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
sp = w.s([rb2, w.inst('simpr')], 'syl', '( %s -> 0 < S )' % A0)
rrp = w.s([rr, rp], 'elrpd', '( %s -> R e. RR+ )' % A0)
srp = w.s([sr, sp], 'elrpd', '( %s -> S e. RR+ )' % A0)
rsrp = w.s([rrp, srp], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, RS))
ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
pq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INTP, INTQ))
ho = w.s([c1, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
it = w.s([pq, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
iq = w.s([pq, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
fcn = w.s([ho, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rdv = w.s([ho, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
dvs = w.s([w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), ff, dcc], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
rdd = w.s([rdv, dvs], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
qc = w.s([iq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
pd = w.s([rdd, w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> P e. D )' % A0)
qd = w.s([rdd, w.s([ab, iq, w.inst('crectinp')], 'syl2anc', '( %s -> Q e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> Q e. D )' % A0)
fpc = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
fqc = w.s([ff, qd], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
# II is a complex number
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
sp1 = w.s([w.s([], 'snsspr1', '{ P } C_ { P , Q }')], 'a1i', '( %s -> { P } C_ { P , Q } )' % A0)
sp2 = w.s([w.s([], 'snsspr2', '{ Q } C_ { P , Q }')], 'a1i', '( %s -> { Q } C_ { P , Q } )' % A0)
e2cp = w.s([crss, sp1], 'ssdif2d', '( %s -> %s C_ ( CC \\ { P } ) )' % (A0, E2))
e2cq = w.s([crss, sp2], 'ssdif2d', '( %s -> %s C_ ( CC \\ { Q } ) )' % (A0, E2))
e2cr = w.s([w.s([], 'difss', '%s C_ ( A crect B )' % E2)], 'a1i', '( %s -> %s C_ ( A crect B ) )' % (A0, E2))
e2d = w.s([e2cr, rdd], 'sstrd', '( %s -> %s C_ D )' % (A0, E2))
kcn = w.s([fcn, e2d, w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ ( CC \\ { P } ) ) )' % (A0, E2)),
                          w.s([qc, e2cq], 'jca', '( %s -> ( Q e. CC /\\ %s C_ ( CC \\ { Q } ) ) )' % (A0, E2))], 'jca',
                         '( %s -> ( ( P e. CC /\\ %s C_ ( CC \\ { P } ) ) /\\ ( Q e. CC /\\ %s C_ ( CC \\ { Q } ) ) ) )' % (A0, E2, E2)),
             w.inst('qf2cn')], 'syl3anc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, KER, E2))
fre2 = w.s([ab, it, iq, w.inst('crectfrd')], 'syl3anc', '( %s -> %s C_ %s )' % (A0, FR, E2))
iicl = w.s([ab, w.s([kcn, fre2], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, KER, E2, FR, E2)), w.inst('rectintcle')],
           'syl2anc', '( %s -> %s e. CC )' % (A0, II))
# the two-point formula and its modulus
cd = w.s([ab, pq, ho, w.inst('rectintcaud')], 'syl3anc', '( %s -> ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) = ( ( P - Q ) x. %s ) )' % (A0, TPI, II))
tpic = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([w.s([], 'pire', '_pi e. RR')], 'recni', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI)], 'a1i', '( %s -> %s e. CC )' % (A0, TPI))
negq = w.s([fqc], 'negcld', '( %s -> -u ( F ` Q ) e. CC )' % A0)
e1 = w.s([w.s([fp0], 'oveq1d', '( %s -> ( ( F ` P ) - ( F ` Q ) ) = ( 0 - ( F ` Q ) ) )' % A0),
          w.s([w.s([w.s([], 'df-neg', '-u ( F ` Q ) = ( 0 - ( F ` Q ) )')], 'eqcomi', '( 0 - ( F ` Q ) ) = -u ( F ` Q )')], 'a1i',
              '( %s -> ( 0 - ( F ` Q ) ) = -u ( F ` Q ) )' % A0)], 'eqtrd', '( %s -> ( ( F ` P ) - ( F ` Q ) ) = -u ( F ` Q ) )' % A0)
lhs1 = w.s([w.s([e1], 'oveq2d', '( %s -> ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) = ( %s x. -u ( F ` Q ) ) )' % (A0, TPI, TPI))], 'fveq2d',
           '( %s -> ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) = ( abs ` ( %s x. -u ( F ` Q ) ) ) )' % (A0, TPI, TPI))
lhs2 = w.s([tpic, negq], 'absmuld', '( %s -> ( abs ` ( %s x. -u ( F ` Q ) ) ) = ( ( abs ` %s ) x. ( abs ` -u ( F ` Q ) ) ) )' % (A0, TPI, TPI))
lhs3 = w.s([w.s([w.s([], 'abstpi', '( abs ` %s ) = ( 2 x. _pi )' % TPI)], 'a1i', '( %s -> ( abs ` %s ) = ( 2 x. _pi ) )' % (A0, TPI)),
            w.s([fqc], 'absnegd', '( %s -> ( abs ` -u ( F ` Q ) ) = %s )' % (A0, AQ))], 'oveq12d',
           '( %s -> ( ( abs ` %s ) x. ( abs ` -u ( F ` Q ) ) ) = %s )' % (A0, TPI, L0))
lhs = w.s([w.s([lhs1, lhs2], 'eqtrd', '( %s -> ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) = ( ( abs ` %s ) x. ( abs ` -u ( F ` Q ) ) ) )' % (A0, TPI, TPI)), lhs3],
          'eqtrd', '( %s -> ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) = %s )' % (A0, TPI, L0))
rhs1 = w.s([w.s([pc, qc], 'subcld', '( %s -> ( P - Q ) e. CC )' % A0), iicl], 'absmuld',
           '( %s -> ( abs ` ( ( P - Q ) x. %s ) ) = ( ( abs ` ( P - Q ) ) x. ( abs ` %s ) ) )' % (A0, II, II))
rhs2 = w.s([w.s([pc, qc], 'abssubd', '( %s -> ( abs ` ( P - Q ) ) = %s )' % (A0, DD))], 'oveq1d',
           '( %s -> ( ( abs ` ( P - Q ) ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, II, DD, II))
rhs = w.s([rhs1, rhs2], 'eqtrd', '( %s -> ( abs ` ( ( P - Q ) x. %s ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, II, DD, II))
eqv = w.s([w.s([w.s([cd], 'fveq2d', '( %s -> ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) = ( abs ` ( ( P - Q ) x. %s ) ) )' % (A0, TPI, II)), rhs],
                'eqtrd', '( %s -> ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, TPI, DD, II))], 'idi',
          '( %s -> ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, TPI, DD, II))
key = w.s([w.s([lhs], 'eqcomd', '( %s -> %s = ( abs ` ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) ) )' % (A0, L0, TPI)), eqv], 'eqtrd',
          '( %s -> %s = ( %s x. ( abs ` %s ) ) )' % (A0, L0, DD, II))
# the ML bound on the kernel integral
ce2 = w.s([c1, c2, mal, w.inst('rectintce2')], 'syl3anc',
          '( %s -> ( abs ` %s ) <_ ( ( 2 x. ( M / %s ) ) x. %s ) )' % (A0, II, RS, PER))
# assemble
qpc = w.s([qc, pc], 'subcld', '( %s -> ( Q - P ) e. CC )' % A0)
ddr = w.s([qpc], 'abscld', '( %s -> %s e. RR )' % (A0, DD))
dd0 = w.s([qpc], 'absge0d', '( %s -> 0 <_ %s )' % (A0, DD))
iir = w.s([iicl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, II))
ar_ = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br_ = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai_ = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi_ = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
perr = w.s([w.s([br_, ar_], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)),
            w.s([bi_, ai_], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
mrs = w.s([mr, rsrp], 'rerpdivcld', '( %s -> ( M / %s ) e. RR )' % (A0, RS))
t2md = w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), mrs], 'remulcld', '( %s -> ( 2 x. ( M / %s ) ) e. RR )' % (A0, RS))
bnd1 = w.s([iir, w.s([t2md, perr], 'remulcld', '( %s -> ( ( 2 x. ( M / %s ) ) x. %s ) e. RR )' % (A0, RS, PER)),
            w.s([ddr, dd0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, DD, DD))], '3jca',
           '( %s -> ( ( abs ` %s ) e. RR /\\ ( ( 2 x. ( M / %s ) ) x. %s ) e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A0, II, RS, PER, DD, DD))
bnd = w.s([bnd1, ce2, w.inst('lemul2a')], 'syl2anc',
          '( %s -> ( %s x. ( abs ` %s ) ) <_ ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) )' % (A0, DD, II, DD, RS, PER))
step = w.s([key, bnd], 'eqbrtrd', '( %s -> %s <_ ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) )' % (A0, L0, DD, RS, PER))
# rewrite the right side as T / RS
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
perc = w.s([perr], 'recnd', '( %s -> %s e. CC )' % (A0, PER))
ddc = w.s([ddr], 'recnd', '( %s -> %s e. CC )' % (A0, DD))
rsc = w.s([w.s([rsrp], 'rpred', '( %s -> %s e. RR )' % (A0, RS))], 'recnd', '( %s -> %s e. CC )' % (A0, RS))
rsne = w.s([rsrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, RS))
t2c = w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)], 'recnd', '( %s -> 2 e. CC )' % A0)
q1 = w.s([w.s([t2c, mc, rsc, rsne], 'divassd', '( %s -> ( ( 2 x. M ) / %s ) = ( 2 x. ( M / %s ) ) )' % (A0, RS, RS))], 'eqcomd',
         '( %s -> ( 2 x. ( M / %s ) ) = ( ( 2 x. M ) / %s ) )' % (A0, RS, RS))
q2 = w.s([w.s([q1], 'oveq1d', '( %s -> ( ( 2 x. ( M / %s ) ) x. %s ) = ( ( ( 2 x. M ) / %s ) x. %s ) )' % (A0, RS, PER, RS, PER)),
          w.s([w.s([w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0), perc, rsc, rsne], 'div23d',
                   '( %s -> ( ( ( 2 x. M ) x. %s ) / %s ) = ( ( ( 2 x. M ) / %s ) x. %s ) )' % (A0, PER, RS, RS, PER))], 'eqcomd',
              '( %s -> ( ( ( 2 x. M ) / %s ) x. %s ) = ( ( ( 2 x. M ) x. %s ) / %s ) )' % (A0, RS, PER, PER, RS))], 'eqtrd',
         '( %s -> ( ( 2 x. ( M / %s ) ) x. %s ) = ( ( ( 2 x. M ) x. %s ) / %s ) )' % (A0, RS, PER, PER, RS))
q3 = w.s([w.s([ddc, w.s([w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0), perc], 'mulcld', '( %s -> ( ( 2 x. M ) x. %s ) e. CC )' % (A0, PER)),
               rsc, rsne], 'divassd', '( %s -> ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) = ( %s x. ( ( ( 2 x. M ) x. %s ) / %s ) ) )' % (A0, DD, PER, RS, DD, PER, RS))], 'eqcomd',
         '( %s -> ( %s x. ( ( ( 2 x. M ) x. %s ) / %s ) ) = ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) )' % (A0, DD, PER, RS, DD, PER, RS))
q4 = w.s([w.s([ddc, w.s([w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0), perc], 'mulcld', '( %s -> ( ( 2 x. M ) x. %s ) e. CC )' % (A0, PER))],
              'mulcomd', '( %s -> ( %s x. ( ( 2 x. M ) x. %s ) ) = %s )' % (A0, DD, PER, TT))], 'oveq1d',
         '( %s -> ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) = ( %s / %s ) )' % (A0, DD, PER, RS, TT, RS))
rw = w.s([w.s([w.s([q2], 'oveq2d', '( %s -> ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) = ( %s x. ( ( ( 2 x. M ) x. %s ) / %s ) ) )' % (A0, DD, RS, PER, DD, PER, RS)), q3],
               'eqtrd', '( %s -> ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) = ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) )' % (A0, DD, RS, PER, DD, PER, RS)), q4],
          'eqtrd', '( %s -> ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) = ( %s / %s ) )' % (A0, DD, RS, PER, TT, RS))
step2 = w.s([step, rw], 'breqtrd', '( %s -> %s <_ ( %s / %s ) )' % (A0, L0, TT, RS))
aqr = w.s([fqc], 'abscld', '( %s -> %s e. RR )' % (A0, AQ))
l0r = w.s([w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0)], 'remulcld',
                '( %s -> ( 2 x. _pi ) e. RR )' % A0), aqr], 'remulcld', '( %s -> %s e. RR )' % (A0, L0))
ttr = w.s([w.s([w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), mr], 'remulcld', '( %s -> ( 2 x. M ) e. RR )' % A0), perr], 'remulcld',
               '( %s -> ( ( 2 x. M ) x. %s ) e. RR )' % (A0, PER)), ddr], 'remulcld', '( %s -> %s e. RR )' % (A0, TT))
w.qed([step2, w.s([l0r, ttr, w.s([w.s([rsrp], 'rpred', '( %s -> %s e. RR )' % (A0, RS)), w.s([rsrp], 'rpgt0d', '( %s -> 0 < %s )' % (A0, RS))], 'jca',
                                 '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, RS, RS)), w.inst('lemuldiv')], 'syl3anc',
                  '( %s -> ( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) ) )' % (A0, L0, RS, TT, L0, TT, RS))],
      'mpbird', '( %s -> ( %s x. %s ) <_ %s )' % (A0, L0, RS, TT)); run1(w)
