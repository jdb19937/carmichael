"""Sortie ZC1: the Euler factor of the principal character: squarefree terms (eufsq), the product identity (euf1),
its nonvanishing (eufne0), and the primitive character of the principal character is 1 (prmcy1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import lin
lin.FASTPATH = True

PD = '{ q e. Prime | q || D }'
PN = '{ q e. Prime | q || N }'
DN = '{ x e. NN | x || N }'
SQD = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || N ) }'


def EUF(n, s):
    return 'prod_ p e. { q e. Prime | q || %s } ( 1 - ( p ^c -u %s ) )' % (n, s)


def PFP(n, s):
    return 'sum_ d e. { x e. NN | x || %s } ( ( mmu ` d ) x. ( d ^c -u %s ) )' % (n, s)


S['eufsq'] = '( ( ( D e. NN /\\ ( mmu ` D ) =/= 0 ) /\\ S e. CC ) -> ( ( mmu ` D ) x. ( D ^c -u S ) ) = prod_ p e. %s -u ( p ^c -u S ) )' % PD
S['euf1'] = '( ( N e. NN /\\ S e. CC ) -> %s = %s )' % (PFP('N', 'S'), EUF('N', 'S'))
S['eufne0'] = '( ( N e. NN /\\ ( S e. CC /\\ 0 < ( Re ` S ) ) ) -> %s =/= 0 )' % EUF('N', 'S')


def gen_eufsq():
    w = W('eufsq', 'For squarefree ` D ` , ` mu ( D ) D ^ -s ` is the product of ` - p ^ -s ` over the primes dividing ` D ` ( ~ muval2 , ~ sqfprodid , ~ fprodefsumfi ).')
    A0, GC = ante_of(S['eufsq'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    dm = s([], 'simpl', '( D e. NN /\\ ( mmu ` D ) =/= 0 )')
    dn = s([dm, w.inst('simpl')], 'syl', 'D e. NN'); mne = s([dm, w.inst('simpr')], 'syl', '( mmu ` D ) =/= 0')
    sc = s([], 'simpr', 'S e. CC')
    pf = s([dn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || D } e. Fin')
    cvp = w.s([w.s([], 'breq1', '( p = q -> ( p || D <-> q || D ) )')], 'cbvrabv', '{ p e. Prime | p || D } = %s' % PD)
    pdf = s([s([cvp], 'a1i', '{ p e. Prime | p || D } = %s' % PD), pf], 'eqeltrrd', '%s e. Fin' % PD)
    Ap = '( %s /\\ p e. %s )' % (A0, PD)
    sp = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ap, f))
    ppr = sp([sp([], 'simpr', 'p e. %s' % PD), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = sp([ppr, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    lpr = sp([prp], 'relogcld', '( log ` p ) e. RR')
    lpc = sp([lpr], 'recnd', '( log ` p ) e. CC')
    SL = 'sum_ p e. %s ( log ` p )' % PD
    slr = s([pdf, lpr], 'fsumrecl', '%s e. RR' % SL)
    # D = prod p = prod exp ( log p ) = exp ( sum log p )
    dp = s([dm, w.inst('sqfprodid')], 'syl', 'prod_ p e. { q e. Prime | q || D } p = D')
    e1 = s([sp([prp], 'reeflog', '( exp ` ( log ` p ) ) = p') if False else w.s([prp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` ( log ` p ) ) = p )' % Ap)], 'prodeq2dv',
           'prod_ p e. %s ( exp ` ( log ` p ) ) = prod_ p e. %s p' % (PD, PD))
    fe = w.s([pdf, lpc], 'fprodefsumfi', '( %s -> prod_ p e. %s ( exp ` ( log ` p ) ) = ( exp ` %s ) )' % (A0, PD, SL))
    dexp = s([s([s([fe], 'eqcomd', '( exp ` %s ) = prod_ p e. %s ( exp ` ( log ` p ) )' % (SL, PD)), e1], 'eqtrd', '( exp ` %s ) = prod_ p e. %s p' % (SL, PD)), dp], 'eqtrd', '( exp ` %s ) = D' % SL)
    ld = s([s([s([dexp], 'eqcomd', 'D = ( exp ` %s )' % SL)], 'fveq2d', '( log ` D ) = ( log ` ( exp ` %s ) )' % SL), s([slr, w.inst('relogef')], 'syl', '( log ` ( exp ` %s ) ) = %s' % (SL, SL))], 'eqtrd',
           '( log ` D ) = %s' % SL)
    # D ^c -u S = exp ( -u S x. log D ) = exp ( sum ( -u S x. log p ) ) = prod p ^c -u S
    dc = s([dn], 'nncnd', 'D e. CC'); dne = s([dn], 'nnne0d', 'D =/= 0'); nsc = s([sc], 'negcld', '-u S e. CC')
    ce = s([s([dc, dne, nsc], '3jca', '( D e. CC /\\ D =/= 0 /\\ -u S e. CC )'), w.inst('cxpef')], 'syl', '( D ^c -u S ) = ( exp ` ( -u S x. ( log ` D ) ) )')
    ce2 = s([ce, s([s([ld], 'oveq2d', '( -u S x. ( log ` D ) ) = ( -u S x. %s )' % SL)], 'fveq2d', '( exp ` ( -u S x. ( log ` D ) ) ) = ( exp ` ( -u S x. %s ) )' % SL)], 'eqtrd',
            '( D ^c -u S ) = ( exp ` ( -u S x. %s ) )' % SL)
    SM = 'sum_ p e. %s ( -u S x. ( log ` p ) )' % PD
    fm = s([pdf, nsc, lpc], 'fsummulc2', '( -u S x. %s ) = %s' % (SL, SM))
    FM = '( k e. %s |-> ( -u S x. ( log ` k ) ) )' % PD
    # values of FM
    Ak = '( %s /\\ p e. %s )' % (A0, PD)
    vx = sp([sp([lift(w, nsc, Ap), lpc], 'mulcld', '( -u S x. ( log ` p ) ) e. CC')], 'elexd', '( -u S x. ( log ` p ) ) e. _V')
    fv, _ = _cg.mptval(w, Ap, 'k', PD, '( -u S x. ( log ` k ) )', 'p', sp([], 'simpr', 'p e. %s' % PD), exs=vx, gen=w.g)
    fvc = sp([fv, sp([lift(w, nsc, Ap), lpc], 'mulcld', '( -u S x. ( log ` p ) ) e. CC')], 'eqeltrd', '( %s ` p ) e. CC' % FM)
    fe2 = w.s([pdf, fvc], 'fprodefsumfi', '( %s -> prod_ p e. %s ( exp ` ( %s ` p ) ) = ( exp ` sum_ p e. %s ( %s ` p ) ) )' % (A0, PD, FM, PD, FM))
    sfe = s([fv], 'sumeq2dv', 'sum_ p e. %s ( %s ` p ) = %s' % (PD, FM, SM))
    pfe = s([w.s([fv], 'fveq2d', '( %s -> ( exp ` ( %s ` p ) ) = ( exp ` ( -u S x. ( log ` p ) ) ) )' % (Ap, FM))], 'prodeq2dv',
            'prod_ p e. %s ( exp ` ( %s ` p ) ) = prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) )' % (PD, FM, PD))
    ex2 = s([s([s([pfe], 'eqcomd', 'prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) ) = prod_ p e. %s ( exp ` ( %s ` p ) )' % (PD, PD, FM)), fe2], 'eqtrd',
               'prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) ) = ( exp ` sum_ p e. %s ( %s ` p ) )' % (PD, PD, FM)), s([sfe], 'fveq2d', '( exp ` sum_ p e. %s ( %s ` p ) ) = ( exp ` %s )' % (PD, FM, SM))],
            'eqtrd', 'prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) ) = ( exp ` %s )' % (PD, SM))
    pce = w.s([w.s([w.s([sp([pnn], 'nncnd', 'p e. CC'), sp([pnn], 'nnne0d', 'p =/= 0'), lift(w, nsc, Ap)], '3jca', '( %s -> ( p e. CC /\\ p =/= 0 /\\ -u S e. CC ) )' % Ap), w.inst('cxpef')], 'syl',
                   '( %s -> ( p ^c -u S ) = ( exp ` ( -u S x. ( log ` p ) ) ) )' % Ap)], 'prodeq2dv', '( %s -> prod_ p e. %s ( p ^c -u S ) = prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) ) )' % (A0, PD, PD))
    dps = s([s([ce2, s([s([fm], 'fveq2d', '( exp ` ( -u S x. %s ) ) = ( exp ` %s )' % (SL, SM)), s([ex2], 'eqcomd', '( exp ` %s ) = prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) )' % (SM, PD))],
                         'eqtrd', '( exp ` ( -u S x. %s ) ) = prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) )' % (SL, PD))], 'eqtrd', '( D ^c -u S ) = prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) )' % PD),
             s([pce], 'eqcomd', 'prod_ p e. %s ( exp ` ( -u S x. ( log ` p ) ) ) = prod_ p e. %s ( p ^c -u S )' % (PD, PD))], 'eqtrd', '( D ^c -u S ) = prod_ p e. %s ( p ^c -u S )' % PD)
    # mu ( D ) = prod -u 1
    mv = s([dm, w.inst('muval2')], 'syl', '( mmu ` D ) = ( -u 1 ^ ( # ` { p e. Prime | p || D } ) )')
    hs = s([s([cvp], 'a1i', '{ p e. Prime | p || D } = %s' % PD)], 'fveq2d', '( # ` { p e. Prime | p || D } ) = ( # ` %s )' % PD)
    mv2 = s([mv, s([hs], 'oveq2d', '( -u 1 ^ ( # ` { p e. Prime | p || D } ) ) = ( -u 1 ^ ( # ` %s ) )' % PD)], 'eqtrd', '( mmu ` D ) = ( -u 1 ^ ( # ` %s ) )' % PD)
    m1c = s([s([], '1cnd', '1 e. CC')], 'negcld', '-u 1 e. CC')
    pc = s([s([pdf, m1c], 'jca', '( %s e. Fin /\\ -u 1 e. CC )' % PD), w.inst('fprodconst')], 'syl', 'prod_ p e. %s -u 1 = ( -u 1 ^ ( # ` %s ) )' % (PD, PD))
    mp = s([mv2, s([pc], 'eqcomd', '( -u 1 ^ ( # ` %s ) ) = prod_ p e. %s -u 1' % (PD, PD))], 'eqtrd', '( mmu ` D ) = prod_ p e. %s -u 1' % PD)
    pcs = sp([sp([pnn], 'nncnd', 'p e. CC'), lift(w, nsc, Ap)], 'cxpcld', '( p ^c -u S ) e. CC')
    fmul = s([pdf, lift(w, m1c, Ap), pcs], 'fprodmul', 'prod_ p e. %s ( -u 1 x. ( p ^c -u S ) ) = ( prod_ p e. %s -u 1 x. prod_ p e. %s ( p ^c -u S ) )' % (PD, PD, PD))
    mneg = s([w.s([pcs], 'mulm1d', '( %s -> ( -u 1 x. ( p ^c -u S ) ) = -u ( p ^c -u S ) )' % Ap)], 'prodeq2dv', 'prod_ p e. %s ( -u 1 x. ( p ^c -u S ) ) = prod_ p e. %s -u ( p ^c -u S )' % (PD, PD))
    lhs = s([mp, dps], 'oveq12d', '( ( mmu ` D ) x. ( D ^c -u S ) ) = ( prod_ p e. %s -u 1 x. prod_ p e. %s ( p ^c -u S ) )' % (PD, PD))
    w.qed([s([lhs, s([fmul], 'eqcomd', '( prod_ p e. %s -u 1 x. prod_ p e. %s ( p ^c -u S ) ) = prod_ p e. %s ( -u 1 x. ( p ^c -u S ) )' % (PD, PD, PD))], 'eqtrd',
             '( ( mmu ` D ) x. ( D ^c -u S ) ) = prod_ p e. %s ( -u 1 x. ( p ^c -u S ) )' % PD), mneg], 'eqtrd', S['eufsq'])
    return run8(w)


def gen_euf1():
    w = W('euf1', 'The Euler factor of the principal character as a Dirichlet polynomial: ` sum_ ( d || N ) mu ( d ) d ^ -s = prod_ ( p || N ) ( 1 - p ^ -s ) ` ( ~ sqfdvdsum , ~ eufsq ; Lean ` eulerFactor ` ).')
    A0, GC = ante_of(S['euf1'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nn = s([], 'simpl', 'N e. NN'); sc = s([], 'simpr', 'S e. CC')
    C = '( ( mmu ` d ) x. ( d ^c -u S ) )'
    dnf = s([nn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DN)
    ss = s([w.s([w.s([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N )')], 'a1i', '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N ) )')], 'ss2rabi', '%s C_ %s' % (SQD, DN))],
           'a1i', '%s C_ %s' % (SQD, DN))
    nsc = s([sc], 'negcld', '-u S e. CC')
    def cc(ante, dnn):
        sa = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        mz = sa([dnn, w.inst('mucl')], 'syl', '( mmu ` d ) e. ZZ')
        return sa([sa([mz], 'zcnd', '( mmu ` d ) e. CC'), sa([sa([dnn], 'nncnd', 'd e. CC'), lift(w, nsc, ante)], 'cxpcld', '( d ^c -u S ) e. CC')], 'mulcld', '%s e. CC' % C)
    Ad = '( %s /\\ d e. %s )' % (A0, SQD)
    sd = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ad, f))
    eld = w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d', '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
               w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'anbi12d', '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) <-> ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )')
    eq = w.s([eld], 'elrab', '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )' % SQD)
    dd = sd([sd([], 'simpr', 'd e. %s' % SQD), eq], 'sylib', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) )')
    dnn = sd([dd, w.inst('simpl')], 'syl', 'd e. NN'); mnz = sd([dd, w.inst('simprl')], 'syl', '( mmu ` d ) =/= 0')
    Adm = '( %s /\\ d e. ( %s \\ %s ) )' % (A0, DN, SQD)
    sm = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Adm, f))
    dif = sm([], 'simpr', 'd e. ( %s \\ %s )' % (DN, SQD))
    ddn = sm([dif, w.inst('eldifi')], 'syl', 'd e. %s' % DN); dnsq = sm([dif, w.inst('eldifn')], 'syl', '-. d e. %s' % SQD)
    eldn = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || N ) )' % DN)
    d2 = sm([ddn, eldn], 'sylib', '( d e. NN /\\ d || N )')
    dnn2 = sm([d2, w.inst('simpl')], 'syl', 'd e. NN'); ddv = sm([d2, w.inst('simpr')], 'syl', 'd || N')
    # mu ( d ) = 0: otherwise d e. SQD
    Amz = '( %s /\\ ( mmu ` d ) =/= 0 )' % Adm
    inner = w.s([w.s([], 'simpr', '( %s -> ( mmu ` d ) =/= 0 )' % Amz), lift(w, ddv, Amz)], 'jca', '( %s -> ( ( mmu ` d ) =/= 0 /\\ d || N ) )' % Amz)
    both = w.s([lift(w, dnn2, Amz), inner], 'jca', '( %s -> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )' % Amz)
    ins = w.s([both, eq], 'sylibr', '( %s -> d e. %s )' % (Amz, SQD))
    m0 = w.s([ins, lift(w, dnsq, Amz)], 'pm2.65da', '( %s -> -. ( mmu ` d ) =/= 0 )' % Adm)
    m00 = sm([m0], 'nne', '( mmu ` d ) = 0') if False else sm([m0, w.s([], 'nne', '( -. ( mmu ` d ) =/= 0 <-> ( mmu ` d ) = 0 )')], 'sylib', '( mmu ` d ) = 0')
    z0 = sm([sm([m00], 'oveq1d', '%s = ( 0 x. ( d ^c -u S ) )' % C), sm([sm([sm([dnn2], 'nncnd', 'd e. CC'), lift(w, nsc, Adm)], 'cxpcld', '( d ^c -u S ) e. CC')], 'mul02d', '( 0 x. ( d ^c -u S ) ) = 0')],
            'eqtrd', '%s = 0' % C)
    fs = s([ss, cc(Ad, dnn), z0, dnf], 'fsumss', 'sum_ d e. %s %s = sum_ d e. %s %s' % (SQD, C, DN, C))
    # sqfdvdsum
    PDd = '{ q e. Prime | q || d }'
    GM = '( j e. Prime |-> -u ( j ^c -u S ) )'
    Apr = '( %s /\\ j e. Prime )' % A0
    spr = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Apr, f))
    pnn = spr([spr([], 'simpr', 'j e. Prime'), w.inst('prmnn')], 'syl', 'j e. NN')
    pv = spr([spr([spr([pnn], 'nncnd', 'j e. CC'), lift(w, nsc, Apr)], 'cxpcld', '( j ^c -u S ) e. CC')], 'negcld', '-u ( j ^c -u S ) e. CC')
    gf = s([pv], 'fmptd', '%s : Prime --> CC' % GM)
    SQ_ = tsub(stmt('sqfdvdsum'), {'G': GM})
    sqa, sqc = ante_of(SQ_)
    sq = s([s([nn, gf], 'jca', sqa), w.inst('sqfdvdsum')], 'syl', sqc)
    # value of G at a prime p, in a context with p e. Prime
    Adp = '( ( %s /\\ d e. %s ) /\\ p e. %s )' % (A0, SQD, PDd)
    sdp = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Adp, f))
    ppr = sdp([sdp([], 'simpr', 'p e. %s' % PDd), w.inst('elrabi')], 'syl', 'p e. Prime')
    vx1 = w.s([w.s([], 'negex', '-u ( p ^c -u S ) e. _V')], 'a1i', '( %s -> -u ( p ^c -u S ) e. _V )' % Adp)
    fv1, _ = _cg.mptval(w, Adp, 'j', 'Prime', '-u ( j ^c -u S )', 'p', ppr, exs=vx1, gen=w.g)
    pe1 = w.s([fv1], 'prodeq2dv', '( %s -> prod_ p e. %s ( %s ` p ) = prod_ p e. %s -u ( p ^c -u S ) )' % (Ad, PDd, GM, PDd))
    se1 = s([pe1], 'sumeq2dv', 'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s prod_ p e. %s -u ( p ^c -u S )' % (SQD, PDd, GM, SQD, PDd))
    Apn = '( %s /\\ p e. %s )' % (A0, PN)
    spn = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Apn, f))
    ppn = spn([spn([], 'simpr', 'p e. %s' % PN), w.inst('elrabi')], 'syl', 'p e. Prime')
    vx2 = w.s([w.s([], 'negex', '-u ( p ^c -u S ) e. _V')], 'a1i', '( %s -> -u ( p ^c -u S ) e. _V )' % Apn)
    fv2, _ = _cg.mptval(w, Apn, 'j', 'Prime', '-u ( j ^c -u S )', 'p', ppn, exs=vx2, gen=w.g)
    pcc = spn([spn([spn([ppn, w.inst('prmnn')], 'syl', 'p e. NN')], 'nncnd', 'p e. CC'), lift(w, nsc, Apn)], 'cxpcld', '( p ^c -u S ) e. CC')
    t2 = spn([spn([fv2], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + -u ( p ^c -u S ) )' % GM), spn([spn([], '1cnd', '1 e. CC'), pcc], 'negsubd', '( 1 + -u ( p ^c -u S ) ) = ( 1 - ( p ^c -u S ) )')],
              'eqtrd', '( 1 + ( %s ` p ) ) = ( 1 - ( p ^c -u S ) )' % GM)
    pe2 = s([t2], 'prodeq2dv', 'prod_ p e. %s ( 1 + ( %s ` p ) ) = %s' % (PN, GM, EUF('N', 'S')))
    # eufsq on SQD
    EQ = tsub(S['eufsq'], {'D': 'd'})
    eqa, eqc = ante_of(EQ)
    eu = w.s([w.s([w.s([dnn, mnz], 'jca', '( %s -> ( d e. NN /\\ ( mmu ` d ) =/= 0 ) )' % Ad), lift(w, sc, Ad)], 'jca', '( %s -> %s )' % (Ad, eqa)), w.inst('eufsq')], 'syl', '( %s -> %s )' % (Ad, eqc))
    se2 = s([eu], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s -u ( p ^c -u S )' % (SQD, C, SQD, PDd))
    chain = s([s([s([fs], 'eqcomd', '%s = sum_ d e. %s %s' % (PFP('N', 'S'), SQD, C)), se2], 'eqtrd', '%s = sum_ d e. %s prod_ p e. %s -u ( p ^c -u S )' % (PFP('N', 'S'), SQD, PDd)),
               s([se1], 'eqcomd', 'sum_ d e. %s prod_ p e. %s -u ( p ^c -u S ) = sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SQD, PDd, SQD, PDd, GM))], 'eqtrd',
              '%s = sum_ d e. %s prod_ p e. %s ( %s ` p )' % (PFP('N', 'S'), SQD, PDd, GM))
    w.qed([s([chain, sq], 'eqtrd', '%s = prod_ p e. %s ( 1 + ( %s ` p ) )' % (PFP('N', 'S'), PN, GM)), pe2], 'eqtrd', S['euf1'])
    return run8(w)


def gen_eufne0():
    w = W('eufne0', 'The Euler factor ` prod_ ( p || N ) ( 1 - p ^ -s ) ` does not vanish on ` 0 < Re s ` (Lean ` eulerFactor_ne_zero ` ; ` abs p ^ -s = p ^ -Re s < 1 ` , ~ fprodn0 ).')
    A0, GC = ante_of(S['eufne0'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nn = s([], 'simpl', 'N e. NN'); sc = s([], 'simprl', 'S e. CC'); rp = s([], 'simprr', '0 < ( Re ` S )')
    pf = s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin')
    cvp = w.s([w.s([], 'breq1', '( p = q -> ( p || N <-> q || N ) )')], 'cbvrabv', '{ p e. Prime | p || N } = %s' % PN)
    pnf = s([s([cvp], 'a1i', '{ p e. Prime | p || N } = %s' % PN), pf], 'eqeltrrd', '%s e. Fin' % PN)
    Ap = '( %s /\\ p e. %s )' % (A0, PN)
    sp = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ap, f))
    ppr = sp([sp([], 'simpr', 'p e. %s' % PN), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = sp([ppr, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn], 'nnrpd', 'p e. RR+'); pr = sp([pnn], 'nnred', 'p e. RR'); p1 = sp([ppr, w.inst('prmgt1')], 'syl', '1 < p')
    nsc = sp([lift(w, sc, Ap)], 'negcld', '-u S e. CC')
    PC = '( p ^c -u S )'
    pc = sp([sp([pnn], 'nncnd', 'p e. CC'), nsc], 'cxpcld', '%s e. CC' % PC)
    ac = sp([sp([prp, nsc], 'jca', '( p e. RR+ /\\ -u S e. CC )'), w.inst('abscxp')], 'syl', '( abs ` %s ) = ( p ^c ( Re ` -u S ) )' % PC)
    rn = sp([lift(w, sc, Ap), w.inst('reneg')], 'syl', '( Re ` -u S ) = -u ( Re ` S )')
    rsr = sp([lift(w, sc, Ap)], 'recld', '( Re ` S ) e. RR')
    nre = sp([rsr], 'renegcld', '-u ( Re ` S ) e. RR')
    lt = sp([sp([sp([pr, p1], 'jca', '( p e. RR /\\ 1 < p )'), sp([nre, sp([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR')], 'jca', '( -u ( Re ` S ) e. RR /\\ 0 e. RR )')], 'jca',
                '( ( p e. RR /\\ 1 < p ) /\\ ( -u ( Re ` S ) e. RR /\\ 0 e. RR ) )'), w.inst('cxplt')], 'syl', '( -u ( Re ` S ) < 0 <-> ( p ^c -u ( Re ` S ) ) < ( p ^c 0 ) )')
    ng = lin8(w, Ap, [lift(w, rp, Ap)], '-u ( Re ` S ) < 0', {'( Re ` S )': rsr})
    l1 = sp([ng, lt], 'mpbid', '( p ^c -u ( Re ` S ) ) < ( p ^c 0 )')
    c0 = sp([sp([pnn], 'nncnd', 'p e. CC'), w.inst('cxp0')], 'syl', '( p ^c 0 ) = 1')
    abl = sp([sp([ac, sp([rn], 'oveq2d', '( p ^c ( Re ` -u S ) ) = ( p ^c -u ( Re ` S ) )')], 'eqtrd', '( abs ` %s ) = ( p ^c -u ( Re ` S ) )' % PC), sp([l1, c0], 'breqtrd', '( p ^c -u ( Re ` S ) ) < 1')],
             'eqbrtrd', '( abs ` %s ) < 1' % PC)
    # 1 - PC =/= 0
    A1 = '( %s /\\ ( 1 - %s ) = 0 )' % (Ap, PC)
    s1 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    one1 = s1([], '1cnd', '1 e. CC')
    zz = s1([], 'simpr', '( 1 - %s ) = 0' % PC)
    bi = s1([one1, lift(w, pc, A1)], 'subeq0ad', '( ( 1 - %s ) = 0 <-> 1 = %s )' % (PC, PC))
    eq1 = s1([zz, bi], 'mpbid', '1 = %s' % PC)
    eqc = s1([eq1], 'eqcomd', '%s = 1' % PC)
    fa = s1([eqc], 'fveq2d', '( abs ` %s ) = ( abs ` 1 )' % PC)
    a1 = s1([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')
    ab1 = s1([fa, a1], 'eqtrd', '( abs ` %s ) = 1' % PC)
    r1 = s1([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    le11 = s1([r1], 'leidd', '1 <_ 1')
    ge = s1([le11, s1([ab1], 'eqcomd', '1 = ( abs ` %s )' % PC)], 'breqtrd', '1 <_ ( abs ` %s )' % PC)
    apr = sp([pc], 'abscld', '( abs ` %s ) e. RR' % PC)
    lnl = s1([r1, lift(w, apr, A1)], 'lenltd', '( 1 <_ ( abs ` %s ) <-> -. ( abs ` %s ) < 1 )' % (PC, PC))
    nl = s1([ge, lnl], 'mpbid', '-. ( abs ` %s ) < 1' % PC)
    nz = w.s([lift(w, abl, A1), nl], 'pm2.65da', '( %s -> -. ( 1 - %s ) = 0 )' % (Ap, PC))
    fne = sp([nz], 'neqned', '( 1 - %s ) =/= 0' % PC)
    fc = sp([sp([], '1cnd', '1 e. CC'), pc], 'subcld', '( 1 - %s ) e. CC' % PC)
    w.qed([pnf, fc, fne], 'fprodn0', S['eufne0'])
    return run8(w)


if __name__ == '__main__':
    gen_eufsq()
    gen_euf1()
    gen_eufne0()
