"""Sortie v2c: the fundamental theorem of the Selberg sieve.

muone     ( mmu ` 1 ) = 1
lwone     the Selberg weight at 1 is 1
lwzf lwzv the Selberg weights as a function with no bound x
mpzf mpzv mpzlam mpzum  the Lambda squared coefficients as a function
selbsieve the fundamental theorem
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2c_lib import *
from cl import lift

DVP = DV('P')
DVZ = '{ z e. NN | z || P }'
LWZB = LW('t').replace(DVP, DVZ)
LWZ = '( t e. NN |-> %s )' % LWZB


def muone():
    w = W('muone', 'The Moebius value at one.')
    PF1 = PF('1', 'p')
    ral = w.s([w.s([], 'nprmdvds1', '( p e. Prime -> -. p || 1 )')], 'rgen',
              'A. p e. Prime -. p || 1')
    emp = w.s([ral, w.s([], 'rabeq0', '( %s = (/) <-> A. p e. Prime -. p || 1 )' % PF1)],
              'mpbir', '%s = (/)' % PF1)
    h0 = w.s([w.s([emp], 'fveq2i', '( # ` %s ) = ( # ` (/) )' % PF1),
              w.s([], 'hash0', '( # ` (/) ) = 0')], 'eqtri', '( # ` %s ) = 0' % PF1)
    mv = w.s([w.s([w.s([], '1nn', '1 e. NN'), w.s([], 'sqf1', '( mmu ` 1 ) =/= 0')], 'pm3.2i',
                  '( 1 e. NN /\\ ( mmu ` 1 ) =/= 0 )'), w.inst('muval2')], 'ax-mp',
             '( mmu ` 1 ) = ( -u 1 ^ ( # ` %s ) )' % PF1)
    e0 = w.s([w.s([h0], 'oveq2i', '( -u 1 ^ ( # ` %s ) ) = ( -u 1 ^ 0 )' % PF1),
              w.s([w.s([], 'neg1cn', '-u 1 e. CC'), w.inst('exp0')], 'ax-mp',
                  '( -u 1 ^ 0 ) = 1')], 'eqtri', '( -u 1 ^ ( # ` %s ) ) = 1' % PF1)
    w.qed([mv, e0], 'eqtri', '( mmu ` 1 ) = 1')
    return w


def lwone():
    w = W('lwone', 'The Selberg weight at one is one.')
    d = shsteps(w, SH, ())
    st = d['st']
    PF1 = PF('1')
    PRD = 'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) )' % PF1
    BODY1 = ('( ( ( ( 1 / ( V ` 1 ) ) x. %s ) x. ( ( mmu ` 1 ) x. ( 1 / %s ) ) ) x. %s )'
             % (GT('1'), SS(), INNER('1')))
    # ---- 1 || P
    onedp = st([st([d['pnn']], 'nnzd', 'P e. ZZ'), w.inst('1dvds')], 'syl', '1 || P')
    tru = st([onedp], 'iftrued', '%s = %s' % (LW('1'), BODY1))
    # ---- the empty prime-divisor product
    ral = w.s([w.s([], 'nprmdvds1', '( r e. Prime -> -. r || 1 )')], 'rgen',
              'A. r e. Prime -. r || 1')
    emp = w.s([ral, w.s([], 'rabeq0', '( %s = (/) <-> A. r e. Prime -. r || 1 )' % PF1)],
              'mpbir', '%s = (/)' % PF1)
    prd = st([st([st([emp], 'a1i', '%s = (/)' % PF1)], 'prodeq1d',
                 '%s = prod_ q e. (/) ( 1 / ( 1 - ( V ` q ) ) )' % PRD),
              st([w.s([], 'prod0', 'prod_ q e. (/) ( 1 / ( 1 - ( V ` q ) ) ) = 1')], 'a1i',
                 'prod_ q e. (/) ( 1 / ( 1 - ( V ` q ) ) ) = 1')], 'eqtrd', '%s = 1' % PRD)
    # ---- the inner sum is the bounding sum
    AM = '( %s /\\ m e. %s )' % (SH, DVP)
    dm = dvpel(w, AM, 'm', d['pnn'])
    sm = dm['st']
    mc = sm([dm['nn']], 'nncnd', 'm e. CC')
    mz = sm([dm['nn']], 'nnzd', 'm e. ZZ')
    c1 = sm([sm([sm([mc], 'mullidd', '( 1 x. m ) = m')], 'oveq1d',
                '( ( 1 x. m ) ^ 2 ) = ( m ^ 2 )')], 'breq1d',
             '( ( ( 1 x. m ) ^ 2 ) <_ Y <-> ( m ^ 2 ) <_ Y )')
    c2 = sm([sm([mz, w.inst('gcd1')], 'syl', '( m gcd 1 ) = 1')], 'biantrud',
            '( ( ( 1 x. m ) ^ 2 ) <_ Y <-> '
            '( ( ( 1 x. m ) ^ 2 ) <_ Y /\\ ( m gcd 1 ) = 1 ) )')
    cond = sm([sm([c2], 'bicomd',
                  '( ( ( ( 1 x. m ) ^ 2 ) <_ Y /\\ ( m gcd 1 ) = 1 ) <-> '
                  '( ( 1 x. m ) ^ 2 ) <_ Y )'), c1], 'bitrd',
              '( ( ( ( 1 x. m ) ^ 2 ) <_ Y /\\ ( m gcd 1 ) = 1 ) <-> ( m ^ 2 ) <_ Y )')
    trm = sm([cond], 'ifbid', '%s = %s' % (INTERM('1'), SSTERM('m')))
    idm = w.s([], 'id', '( m = l -> m = l )')
    n2 = len(w.lines)
    hcb, _ = w.congr(SSTERM('m'), {'m': 'l'}, 'm = l', {'m': idm})
    sdvfix(w, n2)
    inn = st([st([trm], 'sumeq2dv',
                 '%s = sum_ m e. %s %s' % (INNER('1'), DVP, SSTERM('m'))),
              st([w.s([hcb], 'cbvsumv',
                      'sum_ m e. %s %s = %s' % (DVP, SSTERM('m'), SS()))], 'a1i',
                 'sum_ m e. %s %s = %s' % (DVP, SSTERM('m'), SS()))], 'eqtrd',
             '%s = %s' % (INNER('1'), SS()))
    # ---- rewrite the body
    n0 = len(w.lines)
    rules = {'( V ` 1 )': ('1', d['v1']),
             PRD: ('1', prd),
             '( mmu ` 1 )': ('1', st([w.s([], 'muone', '( mmu ` 1 ) = 1')], 'a1i',
                                     '( mmu ` 1 ) = 1')),
             INNER('1'): (SS(), inn)}
    rw, new = w.congr(BODY1, {}, SH, {}, rules=rules)
    sdvfix(w, n0)
    TGT = '( ( ( 1 / 1 ) x. ( 1 x. 1 ) ) x. ( 1 x. ( 1 / %s ) ) x. %s )' % (SS(), SS())
    newtxt = new if isinstance(new, str) else ' '.join(new)
    # ---- the arithmetic
    srp = st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())
    ssc = st([srp], 'rpcnd', '%s e. CC' % SS())
    ssn = st([srp], 'rpne0d', '%s =/= 0' % SS())
    irc = st([st([srp], 'rpreccld', '( 1 / %s ) e. RR+' % SS())], 'rpcnd',
             '( 1 / %s ) e. CC' % SS())
    a1 = st([st([st([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1'),
                 st([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')], 'oveq12d',
                '( ( 1 / 1 ) x. ( 1 x. 1 ) ) = ( 1 x. 1 )'),
             st([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')], 'eqtrd',
            '( ( 1 / 1 ) x. ( 1 x. 1 ) ) = 1')
    a2 = st([irc], 'mullidd', '( 1 x. ( 1 / %s ) ) = ( 1 / %s )' % (SS(), SS()))
    a3 = st([a1, a2], 'oveq12d',
            '( ( ( 1 / 1 ) x. ( 1 x. 1 ) ) x. ( 1 x. ( 1 / %s ) ) ) = ( 1 x. ( 1 / %s ) )'
            % (SS(), SS()))
    a4 = st([a3, a2], 'eqtrd',
            '( ( ( 1 / 1 ) x. ( 1 x. 1 ) ) x. ( 1 x. ( 1 / %s ) ) ) = ( 1 / %s )'
            % (SS(), SS()))
    a5 = st([a4], 'oveq1d',
            '( ( ( ( 1 / 1 ) x. ( 1 x. 1 ) ) x. ( 1 x. ( 1 / %s ) ) ) x. %s ) = '
            '( ( 1 / %s ) x. %s )' % (SS(), SS(), SS(), SS()))
    a6 = st([st([ssc, ssn], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (SS(), SS())),
             w.inst('recid2')], 'syl', '( ( 1 / %s ) x. %s ) = 1' % (SS(), SS()))
    w.qed([st([tru, rw], 'eqtrd', '%s = %s' % (LW('1'), newtxt)),
           st([a5, a6], 'eqtrd', '%s = 1' % newtxt)], 'eqtrd',
          '( %s -> %s = 1 )' % (SH, LW('1')))
    return w



def LWZD(D):
    return LW(D).replace(DVP, DVZ)


def DVZN(N):
    return '{ z e. NN | z || %s }' % N


def IFI(N):
    return 'if ( %s = ( u lcm i ) , ( ( %s ` u ) x. ( %s ` i ) ) , 0 )' % (N, LWZ, LWZ)


def INZ(N):
    return 'sum_ i e. %s %s' % (DVZN(N), IFI(N))


def MPZN(N):
    return 'sum_ u e. %s %s' % (DVZN(N), INZ(N))


MPZ = '( v e. NN |-> %s )' % MPZN('v')


def IFE(N):
    return ('if ( %s = ( u lcm e ) , ( ( %s ` u ) x. ( %s ` e ) ) , 0 )' % (N, LWZ, LWZ))


def MPZX(N):
    return 'sum_ u e. %s sum_ e e. %s %s' % (DV(N), DV(N), IFE(N))


def rabzx(w, ante, N):
    """( ante -> { z e. NN | z || N } = { x e. NN | x || N } )"""
    return w.s([w.s([w.s([], 'breq1', '( z = x -> ( z || %s <-> x || %s ) )' % (N, N))],
                    'cbvrabv', '%s = %s' % (DVZN(N), DV(N)))], 'a1i',
               '( %s -> %s = %s )' % (ante, DVZN(N), DV(N)))


def zfacts(w, d, A, N, nnn):
    """the closures needed for MPZN ( N ) under A = ( SH /\ N e. NN )"""
    st = mkst(w, A)
    sh = lift(w, d['sh'], A) if 'sh' in d else None
    finz = st([rabzx(w, A, N), st([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV(N))],
              'eqeltrd', '%s e. Fin' % DVZN(N))
    AU = '( %s /\\ u e. %s )' % (A, DVZN(N))
    su = mkst(w, AU)
    elu = w.s([w.s([], 'breq1', '( z = u -> ( z || %s <-> u || %s ) )' % (N, N))], 'elrab',
              '( u e. %s <-> ( u e. NN /\\ u || %s ) )' % (DVZN(N), N))
    unn = su([su([su([elu], 'a1i', '( u e. %s <-> ( u e. NN /\\ u || %s ) )' % (DVZN(N), N)),
                  su([], 'simpr', 'u e. %s' % DVZN(N))], 'mpbid',
                 '( u e. NN /\\ u || %s )' % N)], 'simpld', 'u e. NN')
    AUI = '( %s /\\ i e. %s )' % (AU, DVZN(N))
    si = mkst(w, AUI)
    eli = w.s([w.s([], 'breq1', '( z = i -> ( z || %s <-> i || %s ) )' % (N, N))], 'elrab',
              '( i e. %s <-> ( i e. NN /\\ i || %s ) )' % (DVZN(N), N))
    inn = si([si([si([eli], 'a1i', '( i e. %s <-> ( i e. NN /\\ i || %s ) )' % (DVZN(N), N)),
                  si([], 'simpr', 'i e. %s' % DVZN(N))], 'mpbid',
                 '( i e. NN /\\ i || %s )' % N)], 'simpld', 'i e. NN')
    lzur = si([si([si([lift(w, sh, AUI), lift(w, unn, AUI)], 'jca', '( %s /\\ u e. NN )' % SH),
                   w.inst('lwzv')], 'syl', '( %s ` u ) = %s' % (LWZ, LW('u'))),
               si([si([lift(w, sh, AUI), lift(w, unn, AUI)], 'jca', '( %s /\\ u e. NN )' % SH),
                   w.inst('lwre')], 'syl', '%s e. RR' % LW('u'))], 'eqeltrd',
              '( %s ` u ) e. RR' % LWZ)
    lzir = si([si([si([lift(w, sh, AUI), inn], 'jca', '( %s /\\ i e. NN )' % SH),
                   w.inst('lwzv')], 'syl', '( %s ` i ) = %s' % (LWZ, LW('i'))),
               si([si([lift(w, sh, AUI), inn], 'jca', '( %s /\\ i e. NN )' % SH),
                   w.inst('lwre')], 'syl', '%s e. RR' % LW('i'))], 'eqeltrd',
              '( %s ` i ) e. RR' % LWZ)
    ifir = si([si([lzur, lzir], 'remulcld', '( ( %s ` u ) x. ( %s ` i ) ) e. RR' % (LWZ, LWZ)),
               w.s([], '0red', '( %s -> 0 e. RR )' % AUI)], 'ifcld', '%s e. RR' % IFI(N))
    inr = su([lift(w, finz, AU), ifir], 'fsumrecl', '%s e. RR' % INZ(N))
    return st, finz, st([finz, inr], 'fsumrecl', '%s e. RR' % MPZN(N))


def mpzre():
    w = W('mpzre', 'The Lambda squared coefficient of the Selberg weights is real.')
    A = '( %s /\\ N e. NN )' % SH
    d = {'sh': w.s([], 'simpl', '( %s -> %s )' % (A, SH))}
    nnn = w.s([], 'simpr', '( %s -> N e. NN )' % A)
    st, finz, r = zfacts(w, d, A, 'N', nnn)
    w.qed([r, w.s([], 'eqidd', '( %s -> %s = %s )' % (A, MPZN('N'), MPZN('N')))], 'eqeltrrd'
          if False else 'eqeltrd', '( %s -> %s e. RR )' % (A, MPZN('N')))
    return w


def mpzlam():
    w = W('mpzlam', 'The Lambda squared coefficient function of the Selberg weights.')
    A = '( %s /\\ N e. NN )' % SH
    st = mkst(w, A)
    sh = w.s([], 'simpl', '( %s -> %s )' % (A, SH))
    nnn = w.s([], 'simpr', '( %s -> N e. NN )' % A)
    # ---- the substitution hypothesis of fvmptg
    EQ = 'v = N'
    seq = mkst(w, EQ)
    hrab = seq([seq([w.s([], 'breq2', '( v = N -> ( z || v <-> z || N ) )')], 'id',
                    '( z || v <-> z || N )')], 'rabbidv', '%s = %s' % (DVZN('v'), DVZN('N')))         if False else w.s([w.s([], 'breq2', '( v = N -> ( z || v <-> z || N ) )')], 'rabbidv',
                          '( v = N -> %s = %s )' % (DVZN('v'), DVZN('N')))
    hif = w.s([w.s([w.s([], 'id', '( v = N -> v = N )')], 'eqeq1d',
                   '( v = N -> ( v = ( u lcm i ) <-> N = ( u lcm i ) ) )')], 'ifbid',
              '( v = N -> %s = %s )' % (IFI('v'), IFI('N')))
    hin = seq([seq([hrab], 'sumeq1d',
                   '%s = sum_ i e. %s %s' % (INZ('v'), DVZN('N'), IFI('v'))),
               seq([hif], 'sumeq2sdv',
                   'sum_ i e. %s %s = %s' % (DVZN('N'), IFI('v'), INZ('N')))], 'eqtrd',
              '%s = %s' % (INZ('v'), INZ('N')))
    hsub = seq([seq([hrab], 'sumeq1d',
                    '%s = sum_ u e. %s %s' % (MPZN('v'), DVZN('N'), INZ('v'))),
                seq([hin], 'sumeq2sdv',
                    'sum_ u e. %s %s = %s' % (DVZN('N'), INZ('v'), MPZN('N')))], 'eqtrd',
               '%s = %s' % (MPZN('v'), MPZN('N')))
    eqf = w.s([], 'eqid', '%s = %s' % (MPZ, MPZ))
    mzr = st([st([sh, nnn], 'jca', '( %s /\\ N e. NN )' % SH), w.inst('mpzre')], 'syl',
             '%s e. RR' % MPZN('N'))
    inst = w.s([hsub, eqf], 'fvmptg',
               '( ( N e. NN /\\ %s e. RR ) -> ( %s ` N ) = %s )'
               % (MPZN('N'), MPZ, MPZN('N')))
    fv = st([nnn, mzr, inst], 'syl2anc', '( %s ` N ) = %s' % (MPZ, MPZN('N')))
    # ---- rename i to e and convert the ranges
    hcb = w.s([w.s([w.s([], 'oveq2', '( i = e -> ( u lcm i ) = ( u lcm e ) )')], 'eqeq2d',
                   '( i = e -> ( %s = ( u lcm i ) <-> %s = ( u lcm e ) ) )' % ('N', 'N')),
               w.s([w.s([], 'fveq2', '( i = e -> ( %s ` i ) = ( %s ` e ) )' % (LWZ, LWZ))],
                   'oveq2d',
                   '( i = e -> ( ( %s ` u ) x. ( %s ` i ) ) = ( ( %s ` u ) x. ( %s ` e ) ) )'
                   % (LWZ, LWZ, LWZ, LWZ))], 'ifbieq1d',
              '( i = e -> %s = %s )' % (IFI('N'), IFE('N')))
    cbv = st([w.s([hcb], 'cbvsumv',
                  '%s = sum_ e e. %s %s' % (INZ('N'), DVZN('N'), IFE('N')))], 'a1i',
             '%s = sum_ e e. %s %s' % (INZ('N'), DVZN('N'), IFE('N')))
    r1 = st([cbv], 'sumeq2sdv',
            '%s = sum_ u e. %s sum_ e e. %s %s'
            % (MPZN('N'), DVZN('N'), DVZN('N'), IFE('N')))
    r2 = st([w.s([rabzx(w, A, 'N')], 'sumeq1d',
                 '( %s -> sum_ e e. %s %s = sum_ e e. %s %s )'
                 % (A, DVZN('N'), IFE('N'), DV('N'), IFE('N')))], 'sumeq2sdv',
            'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s'
            % (DVZN('N'), DVZN('N'), IFE('N'), DVZN('N'), DV('N'), IFE('N')))
    r3 = st([rabzx(w, A, 'N')], 'sumeq1d',
            'sum_ u e. %s sum_ e e. %s %s = %s'
            % (DVZN('N'), DV('N'), IFE('N'), MPZX('N')))
    w.qed([fv, st([r1, st([r2, r3], 'eqtrd',
                          'sum_ u e. %s sum_ e e. %s %s = %s'
                          % (DVZN('N'), DVZN('N'), IFE('N'), MPZX('N')))], 'eqtrd',
                  '%s = %s' % (MPZN('N'), MPZX('N')))], 'eqtrd',
          '( %s -> ( %s ` N ) = %s )' % (A, MPZ, MPZX('N')))
    return w


def mpzf():
    w = W('mpzf', 'The Lambda squared coefficients as a real-valued function.')
    AV = '( %s /\\ v e. NN )' % SH
    st = mkst(w, SH)
    r = w.s([], 'mpzre', '( %s -> %s e. RR )' % (AV, MPZN('v')))
    ral = st([r], 'ralrimiva', 'A. v e. NN %s e. RR' % MPZN('v'))
    eqf = w.s([], 'eqid', '%s = %s' % (MPZ, MPZ))
    bi = st([w.s([eqf], 'fmpt',
                 '( A. v e. NN %s e. RR <-> %s : NN --> RR )' % (MPZN('v'), MPZ))], 'a1i',
            '( A. v e. NN %s e. RR <-> %s : NN --> RR )' % (MPZN('v'), MPZ))
    w.qed([ral, bi], 'mpbid', '( %s -> %s : NN --> RR )' % (SH, MPZ))
    return w


def mpzv():
    w = W('mpzv', 'The values of the Lambda squared coefficient function.')
    A = '( %s /\\ N e. NN )' % SH
    st = mkst(w, A)
    sh = w.s([], 'simpl', '( %s -> %s )' % (A, SH))
    nnn = w.s([], 'simpr', '( %s -> N e. NN )' % A)
    lam = st([st([sh, nnn], 'jca', '( %s /\\ N e. NN )' % SH), w.inst('mpzlam')], 'syl',
             '( %s ` N ) = %s' % (MPZ, MPZX('N')))
    AU = '( %s /\\ u e. %s )' % (A, DV('N'))
    su = mkst(w, AU)
    elu = w.s([w.s([], 'breq1', '( x = u -> ( x || N <-> u || N ) )')], 'elrab',
              '( u e. %s <-> ( u e. NN /\\ u || N ) )' % DV('N'))
    unn = su([su([su([elu], 'a1i', '( u e. %s <-> ( u e. NN /\\ u || N ) )' % DV('N')),
                  su([], 'simpr', 'u e. %s' % DV('N'))], 'mpbid',
                 '( u e. NN /\\ u || N )')], 'simpld', 'u e. NN')
    AUE = '( %s /\\ e e. %s )' % (AU, DV('N'))
    se = mkst(w, AUE)
    ele = w.s([w.s([], 'breq1', '( x = e -> ( x || N <-> e || N ) )')], 'elrab',
              '( e e. %s <-> ( e e. NN /\\ e || N ) )' % DV('N'))
    enn = se([se([se([ele], 'a1i', '( e e. %s <-> ( e e. NN /\\ e || N ) )' % DV('N')),
                  se([], 'simpr', 'e e. %s' % DV('N'))], 'mpbid',
                 '( e e. NN /\\ e || N )')], 'simpld', 'e e. NN')
    vu = se([se([lift(w, sh, AUE), lift(w, unn, AUE)], 'jca', '( %s /\\ u e. NN )' % SH),
             w.inst('lwzv')], 'syl', '( %s ` u ) = %s' % (LWZ, LW('u')))
    ve = se([se([lift(w, sh, AUE), enn], 'jca', '( %s /\\ e e. NN )' % SH),
             w.inst('lwzv')], 'syl', '( %s ` e ) = %s' % (LWZ, LW('e')))
    bod = se([se([vu, ve], 'oveq12d',
                 '( ( %s ` u ) x. ( %s ` e ) ) = ( %s x. %s )'
                 % (LWZ, LWZ, LW('u'), LW('e')))], 'ifeq1d',
             '%s = if ( N = ( u lcm e ) , ( %s x. %s ) , 0 )' % (IFE('N'), LW('u'), LW('e')))
    b1 = su([bod], 'sumeq2dv',
            'sum_ e e. %s %s = sum_ e e. %s if ( N = ( u lcm e ) , ( %s x. %s ) , 0 )'
            % (DV('N'), IFE('N'), DV('N'), LW('u'), LW('e')))
    b2 = st([b1], 'sumeq2dv', '%s = %s' % (MPZX('N'), MP('N', d='u', e='e')))
    w.qed([lam, b2], 'eqtrd', '( %s -> ( %s ` N ) = %s )' % (A, MPZ, MP('N', d='u', e='e')))
    return w


def lwzeq():
    w = W('lwzeq', 'The Selberg weight with the divisor sets written over a different bound '
                   'variable.')
    n0 = len(w.lines)
    rw, new = w.congr(LWZD('D'), {}, 'ph', {}, rules={DVZ: (DVP, rabzx(w, 'ph', 'P'))})
    sdvfix(w, n0)
    newtxt = new if isinstance(new, str) else ' '.join(new)
    assert newtxt == LW('D'), newtxt
    w.qed([rw, w.s([], 'eqidd', '( ph -> %s = %s )' % (LW('D'), LW('D')))], 'eqtrd',
          '( ph -> %s = %s )' % (LWZD('D'), LW('D')))
    return w


def lwzf():
    w = W('lwzf', 'The Selberg weights as a function with no occurrence of x.')
    AT = '( %s /\\ t e. NN )' % SH
    st = mkst(w, SH)
    eqt = w.s([], 'lwzeq', '( %s -> %s = %s )' % (AT, LWZD('t'), LW('t')))
    lwr = w.s([], 'lwre', '( %s -> %s e. RR )' % (AT, LW('t')))
    zr = w.s([eqt, lwr], 'eqeltrd', '( %s -> %s e. RR )' % (AT, LWZD('t')))
    ral = st([zr], 'ralrimiva', 'A. t e. NN %s e. RR' % LWZD('t'))
    eqf = w.s([], 'eqid', '%s = %s' % (LWZ, LWZ))
    bi = st([w.s([eqf], 'fmpt',
                 '( A. t e. NN %s e. RR <-> %s : NN --> RR )' % (LWZD('t'), LWZ))], 'a1i',
            '( A. t e. NN %s e. RR <-> %s : NN --> RR )' % (LWZD('t'), LWZ))
    w.qed([ral, bi], 'mpbid', '( %s -> %s : NN --> RR )' % (SH, LWZ))
    return w


def lwzv():
    w = W('lwzv', 'The values of the Selberg weight function.')
    A = '( %s /\\ D e. NN )' % SH
    st = mkst(w, A)
    idt = w.s([], 'id', '( t = D -> t = D )')
    n0 = len(w.lines)
    hsub, new = w.congr(LWZD('t'), {'t': 'D'}, 't = D', {'t': idt})
    sdvfix(w, n0)
    assert (new if isinstance(new, str) else ' '.join(new)) == LWZD('D')
    eqf = w.s([], 'eqid', '%s = %s' % (LWZ, LWZ))
    eqd = w.s([], 'lwzeq', '( %s -> %s = %s )' % (A, LWZD('D'), LW('D')))
    lwr = w.s([], 'lwre', '( %s -> %s e. RR )' % (A, LW('D')))
    zr = w.s([eqd, lwr], 'eqeltrd', '( %s -> %s e. RR )' % (A, LWZD('D')))
    inst = w.s([hsub, eqf], 'fvmptg',
               '( ( D e. NN /\\ %s e. RR ) -> ( %s ` D ) = %s )' % (LWZD('D'), LWZ, LWZD('D')))
    dnn = w.s([], 'simpr', '( %s -> D e. NN )' % A)
    fv = st([dnn, zr, inst], 'syl2anc', '( %s ` D ) = %s' % (LWZ, LWZD('D')))
    w.qed([fv, eqd], 'eqtrd', '( %s -> ( %s ` D ) = %s )' % (A, LWZ, LW('D')))
    return w



DVP2 = DV('P')
ERR = ('sum_ d e. %s if ( d <_ Y , ( ( 3 ^ %s ) x. ( abs ` %s ) ) , 0 )'
       % (DVP2, OM('d'), RM('d')))
UMH = ('A. y e. NN if ( y = 1 , 1 , 0 ) <_ sum_ e e. %s ( %s ` e )' % (DV('y'), MPZ))


def mpzum():
    w = W('mpzum', 'The Lambda squared coefficients of the Selberg weights are an upper '
                   'Moebius function.')
    st = mkst(w, SH)
    zf = st([w.s([], 'id', '( %s -> %s )' % (SH, SH)), w.inst('lwzf')], 'syl',
            '%s : NN --> RR' % LWZ)
    onenn = st([w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % SH)], 'id',
               '1 e. NN') if False else w.s([w.s([], '1nn', '1 e. NN')], 'a1i',
                                            '( %s -> 1 e. NN )' % SH)
    zone = st([st([st([w.s([], 'id', '( %s -> %s )' % (SH, SH)), onenn], 'jca',
                      '( %s /\\ 1 e. NN )' % SH), w.inst('lwzv')], 'syl',
                  '( %s ` 1 ) = %s' % (LWZ, LW('1'))),
               st([w.s([], 'id', '( %s -> %s )' % (SH, SH)), w.inst('lwone')], 'syl',
                  '%s = 1' % LW('1'))], 'eqtrd', '( %s ` 1 ) = 1' % LWZ)
    AY = '( %s /\\ y e. NN )' % SH
    sy = mkst(w, AY)
    ynn = w.s([], 'simpr', '( %s -> y e. NN )' % AY)
    lam = sy([sy([lift(w, zf, AY), lift(w, zone, AY), ynn], '3jca',
                 '( %s : NN --> RR /\\ ( %s ` 1 ) = 1 /\\ y e. NN )' % (LWZ, LWZ)),
              w.inst('lamsqub')], 'syl',
             'if ( y = 1 , 1 , 0 ) <_ sum_ d e. %s %s' % (DV('y'), MPZX('d')))
    AYD = '( %s /\\ d e. %s )' % (AY, DV('y'))
    sd = mkst(w, AYD)
    eld = w.s([w.s([], 'breq1', '( x = d -> ( x || y <-> d || y ) )')], 'elrab',
              '( d e. %s <-> ( d e. NN /\\ d || y ) )' % DV('y'))
    dnn = sd([sd([sd([eld], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || y ) )' % DV('y')),
                  sd([], 'simpr', 'd e. %s' % DV('y'))], 'mpbid',
                 '( d e. NN /\\ d || y )')], 'simpld', 'd e. NN')
    fvd = sd([sd([sd([lift(w, w.s([], 'id', '( %s -> %s )' % (SH, SH)), AYD), dnn], 'jca',
                     '( %s /\\ d e. NN )' % SH), w.inst('mpzlam')], 'syl',
                 '( %s ` d ) = %s' % (MPZ, MPZX('d')))], 'eqcomd',
              '%s = ( %s ` d )' % (MPZX('d'), MPZ))
    s1 = sy([fvd], 'sumeq2dv',
            'sum_ d e. %s %s = sum_ d e. %s ( %s ` d )' % (DV('y'), MPZX('d'), DV('y'), MPZ))
    cbv = sy([w.s([w.s([], 'fveq2', '( d = e -> ( %s ` d ) = ( %s ` e ) )' % (MPZ, MPZ))],
                  'cbvsumv',
                  'sum_ d e. %s ( %s ` d ) = sum_ e e. %s ( %s ` e )'
                  % (DV('y'), MPZ, DV('y'), MPZ))], 'a1i',
             'sum_ d e. %s ( %s ` d ) = sum_ e e. %s ( %s ` e )'
             % (DV('y'), MPZ, DV('y'), MPZ))
    body = sy([lam, sy([s1, cbv], 'eqtrd',
                       'sum_ d e. %s %s = sum_ e e. %s ( %s ` e )'
                       % (DV('y'), MPZX('d'), DV('y'), MPZ))], 'breqtrd',
              'if ( y = 1 , 1 , 0 ) <_ sum_ e e. %s ( %s ` e )' % (DV('y'), MPZ))
    w.qed([body], 'ralrimiva', '( %s -> %s )' % (SH, UMH))
    return w


def selbsieve():
    w = W('selbsieve', 'The fundamental theorem of the Selberg sieve.')
    d = shsteps(w, SH, ())
    st = d['st']
    MPD = MP('d', d='u', e='e')
    T1 = 'sum_ d e. %s ( ( %s ` d ) x. ( V ` d ) )' % (DVP2, MPZ)
    T2 = 'sum_ d e. %s ( ( abs ` ( %s ` d ) ) x. ( abs ` %s ) )' % (DVP2, MPZ, RM('d'))
    EMP = 'sum_ d e. %s ( ( abs ` %s ) x. ( abs ` %s ) )' % (DVP2, MPD, RM('d'))
    mzf = st([d['sh'], w.inst('mpzf')], 'syl', '%s : NN --> RR' % MPZ)
    mzu = st([d['sh'], w.inst('mpzum')], 'syl', UMH)
    su = st([st([d['sh'], st([mzf, mzu], 'jca',
                             '( %s : NN --> RR /\\ %s )' % (MPZ, UMH))], 'jca',
                '( %s /\\ ( %s : NN --> RR /\\ %s ) )' % (SH, MPZ, UMH)),
             w.inst('siftub')], 'syl',
            '%s <_ ( ( X x. %s ) + %s )' % (SF, T1, T2))
    # ---- the values of the coefficient function
    AD = '( %s /\\ d e. %s )' % (SH, DVP2)
    dd = dvpel(w, AD, 'd', d['pnn'])
    sd = dd['st']
    fvd = sd([sd([lift(w, d['sh'], AD), dd['nn']], 'jca', '( %s /\\ d e. NN )' % SH),
              w.inst('mpzv')], 'syl', '( %s ` d ) = %s' % (MPZ, MPD))
    # ---- the main term
    m1 = st([sd([fvd], 'oveq1d',
                '( ( %s ` d ) x. ( V ` d ) ) = ( %s x. ( V ` d ) )' % (MPZ, MPD))], 'sumeq2dv',
            '%s = sum_ d e. %s ( %s x. ( V ` d ) )' % (T1, DVP2, MPD))
    mm = st([d['sh'], w.inst('mpmain')], 'syl',
            'sum_ d e. %s ( %s x. ( V ` d ) ) = ( 1 / %s )' % (DVP2, MPD, SS()))
    srp = st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())
    xc = st([d['xr']], 'recnd', 'X e. CC')
    main = st([st([st([m1, mm], 'eqtrd', '%s = ( 1 / %s )' % (T1, SS()))], 'oveq2d',
                  '( X x. %s ) = ( X x. ( 1 / %s ) )' % (T1, SS())),
               st([st([xc, st([srp], 'rpcnd', '%s e. CC' % SS()),
                       st([srp], 'rpne0d', '%s =/= 0' % SS())], 'divrecd',
                      '( X / %s ) = ( X x. ( 1 / %s ) )' % (SS(), SS()))], 'eqcomd',
                  '( X x. ( 1 / %s ) ) = ( X / %s )' % (SS(), SS()))], 'eqtrd',
              '( X x. %s ) = ( X / %s )' % (T1, SS()))
    # ---- the error term
    e1 = st([sd([sd([fvd], 'fveq2d',
                    '( abs ` ( %s ` d ) ) = ( abs ` %s )' % (MPZ, MPD))], 'oveq1d',
                '( ( abs ` ( %s ` d ) ) x. ( abs ` %s ) ) = '
                '( ( abs ` %s ) x. ( abs ` %s ) )' % (MPZ, RM('d'), MPD, RM('d')))],
            'sumeq2dv', '%s = %s' % (T2, EMP))
    errle = st([e1, st([d['sh'], w.inst('selberr')], 'syl', '%s <_ %s' % (EMP, ERR))],
               'eqbrtrd', '%s <_ %s' % (T2, ERR))
    # ---- closures
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP2)
    absmp = sd([sd([sd([lift(w, d['sh'], AD), dd['nn']], 'jca', '( %s /\\ d e. NN )' % SH),
                    w.inst('lwre')], 'syl', '%s e. RR' % LW('d'))], 'id',
               '%s e. RR' % LW('d')) if False else None
    mzr = sd([sd([lift(w, d['sh'], AD), dd['nn']], 'jca', '( %s /\\ d e. NN )' % SH),
              w.inst('mpzre')], 'syl', '%s e. RR' % MPZN('d'))
    fvr = sd([sd([sd([lift(w, d['sh'], AD), dd['nn']], 'jca', '( %s /\\ d e. NN )' % SH),
                  w.inst('mpzlam')], 'syl', '( %s ` d ) = %s' % (MPZ, MPZX('d'))), ], 'id',
             'x = x') if False else None
    mpdr = sd([sd([lift(w, mzf, AD), dd['nn'], w.inst('ffvelcdm')], 'syl2anc',
                  '( %s ` d ) e. RR' % MPZ)], 'id', '( %s ` d ) e. RR' % MPZ) if False else         sd([lift(w, mzf, AD), dd['nn'], w.inst('ffvelcdm')], 'syl2anc',
           '( %s ` d ) e. RR' % MPZ)
    absmpr = sd([sd([mpdr], 'recnd', '( %s ` d ) e. CC' % MPZ)], 'abscld',
                '( abs ` ( %s ` d ) ) e. RR' % MPZ)
    ADN = '( %s /\\ n e. A )' % AD
    sn = mkst(w, ADN)
    nnnn = w.s([lift(w, d['assnn'], AD)], 'sselda', '( %s -> n e. NN )' % ADN)
    wnr = sn([lift(w, d['wf'], ADN), nnnn, w.inst('ffvelcdm')], 'syl2anc', '( W ` n ) e. RR')
    ifwr = sn([wnr, w.s([], '0red', '( %s -> 0 e. RR )' % ADN)], 'ifcld',
              'if ( d || n , ( W ` n ) , 0 ) e. RR')
    msr = sd([lift(w, d['afin'], AD), ifwr], 'fsumrecl', '%s e. RR' % MS('d'))
    vdr = sd([lift(w, d['vf'], AD), dd['nn'], w.inst('ffvelcdm')], 'syl2anc', '( V ` d ) e. RR')
    rmr = sd([msr, sd([vdr, lift(w, d['xr'], AD)], 'remulcld', '( ( V ` d ) x. X ) e. RR')],
             'resubcld', '%s e. RR' % RM('d'))
    absrm = sd([sd([rmr], 'recnd', '%s e. CC' % RM('d'))], 'abscld',
               '( abs ` %s ) e. RR' % RM('d'))
    t2r = st([finP, sd([absmpr, absrm], 'remulcld',
                       '( ( abs ` ( %s ` d ) ) x. ( abs ` %s ) ) e. RR' % (MPZ, RM('d')))],
             'fsumrecl', '%s e. RR' % T2)
    finpf = sd([sd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                   '%s = %s' % (PF('d', 'p'), PF('d'))),
               sd([dd['nn'], w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
              'eqeltrrd', '%s e. Fin' % PF('d'))
    om0 = sd([finpf, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    thr = sd([w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % AD), om0],
             'reexpcld', '( 3 ^ %s ) e. RR' % OM('d'))
    errr = st([finP, sd([sd([thr, absrm], 'remulcld',
                            '( ( 3 ^ %s ) x. ( abs ` %s ) ) e. RR' % (OM('d'), RM('d'))),
                         w.s([], '0red', '( %s -> 0 e. RR )' % AD)], 'ifcld',
                        'if ( d <_ Y , ( ( 3 ^ %s ) x. ( abs ` %s ) ) , 0 ) e. RR'
                        % (OM('d'), RM('d')))], 'fsumrecl', '%s e. RR' % ERR)
    xssr = st([d['xr'], srp], 'rerpdivcld', '( X / %s ) e. RR' % SS())
    # ---- assemble
    add = st([t2r, errr, xssr, errle], 'leadd2dd',
             '( ( X / %s ) + %s ) <_ ( ( X / %s ) + %s )' % (SS(), T2, SS(), ERR))
    rew = st([main], 'oveq1d',
             '( ( X x. %s ) + %s ) = ( ( X / %s ) + %s )' % (T1, T2, SS(), T2))
    le2 = st([rew, add], 'eqbrtrd',
             '( ( X x. %s ) + %s ) <_ ( ( X / %s ) + %s )' % (T1, T2, SS(), ERR))
    AN = '( %s /\\ n e. A )' % SH
    sn2 = mkst(w, AN)
    nnn2 = w.s([d['assnn']], 'sselda', '( %s -> n e. NN )' % AN)
    wnr2 = sn2([lift(w, d['wf'], AN), nnn2, w.inst('ffvelcdm')], 'syl2anc',
               '( W ` n ) e. RR')
    sfterm = sn2([wnr2, w.s([], '0red', '( %s -> 0 e. RR )' % AN)], 'ifcld',
                 'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) e. RR')
    sfr = st([d['afin'], sfterm], 'fsumrecl', '%s e. RR' % SF)
    lhs = st([xssr, t2r], 'readdcld', '( ( X x. %s ) + %s ) e. RR' % (T1, T2)) if False else         st([st([d['xr'], st([finP, sd([mpdr, vdr], 'remulcld',
                                      '( ( %s ` d ) x. ( V ` d ) ) e. RR' % MPZ)], 'fsumrecl',
                            '%s e. RR' % T1)], 'remulcld', '( X x. %s ) e. RR' % T1), t2r],
           'readdcld', '( ( X x. %s ) + %s ) e. RR' % (T1, T2))
    rhs = st([xssr, errr], 'readdcld', '( ( X / %s ) + %s ) e. RR' % (SS(), ERR))
    w.qed([sfr, lhs, rhs, su, le2], 'letrd',
          '( %s -> %s <_ ( ( X / %s ) + %s ) )' % (SH, SF, SS(), ERR))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['muone']:
        globals()[f]().run()
