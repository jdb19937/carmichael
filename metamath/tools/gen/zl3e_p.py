"""ZL3e: the continuation at a primitive character (PCONT parts) and the headlines.
`MM_DB=sorties/zl3e.mm python3 tools/gen/zl3e_p.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl3e_f import *
from cl import lift as _lift
lift = _lift

MAIN = __name__ == '__main__'
Z3G = LE.Z3.GAMF
LSs = lambda v: LE.Z3.LS(LE.CYM, v)
import zl2lib as _Z2
Z2S = _Z2.STATEMENTS
PR, PAR, EPS, RM, CYM, CYBM, YB = LE.PR, LE.PAR, LE.EPS, LE.RM, LE.CYM, LE.CYBM, LE.YB
FC = LE.FC
I1, I2 = LE.MPW(CYM, PAR), LE.MPW(CYBM, PAR)
DQP = LE.DQ(PAR)
MPA = '( M e. NN /\\ %s e. { 0 , 1 } )' % PAR


def pr_base(w, A, pr):
    """facts under ( A -> PR ): ch, M e. NN, Y e. Base, par, PAR e. {0,1}, YB e. Base, TA ( Y ), TA ( YB ), MPA"""
    ch = D(w, A, 'simpld', [pr], '( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) )')
    mn = D(w, A, 'simpld', [ch], 'M e. NN')
    par = D(w, A, 'syl', [ch, w.inst('zl3par')], L.split_imp(L.STATEMENTS['zl3par'])[1])
    pq = D(w, A, 'simpld', [par], '( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) )' % (PAR, YB))
    pp = D(w, A, 'simpld', [pq], '%s e. { 0 , 1 }' % PAR); ybd = D(w, A, 'simprd', [pq], '%s e. ( Base ` ( DChr ` M ) )' % YB)
    sub_P = lambda txt: ' '.join(PAR if tk == 'P' else tk for tk in txt.split())
    TAY, TAB = sub_P(L.TAZ('Y')), sub_P(L.TAZ(YB))
    taY = D(w, A, 'syl2anc', [ch, pp, w.inst('zl3ta')], TAY)
    taB = D(w, A, 'syl2anc', [D(w, A, 'jca', [mn, ybd], '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % YB), pp, w.inst('zl3ta')], TAB)
    mpa = D(w, A, 'jca', [mn, pp], MPA)
    return dict(ch=ch, mn=mn, par=par, pp=pp, ybd=ybd, taY=taY, taB=taB, mpa=mpa, TAY=TAY, TAB=TAB)


def rm_cc(w, A):
    return w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'ifcli', '%s e. CC' % RM)], 'a1i', '( %s -> %s e. CC )' % (A, RM))


# ---------------------------------------------------------------- zl3fch
if wante('zl3fch', MAIN):
    w = W('zl3fch', 'The continuation ` F ` at a primitive character is holomorphic on ` U ` ( ~ zl3fh with ~ zl3ilh , ~ zl3dq ).')
    A, Cc = ante_e('zl3fch')
    pr = w.s([], 'id', '( %s -> %s )' % (A, A))
    B = pr_base(w, A, pr)
    sub_CP = lambda C: lambda txt: ' '.join({'C': C, 'P': PAR}.get(tk, tk) for tk in txt.split())
    ilh = lambda ta, C: D(w, A, 'syl', [ta, w.inst('zl3ilh')], HOL(LE.MPW(C, PAR), 'CC'))
    hI, hJ = ilh(B['taY'], CYM), ilh(B['taB'], CYBM)
    ec = eps_cl(w, A, B['ch'], B['pp'])
    dq = D(w, A, 'syl', [B['mpa'], w.inst('zl3dq')], LE.tsub(L.split_imp(SE['zl3dq'])[1], {'P': PAR}))
    hdq = D(w, A, 'simpld', [D(w, A, 'simpld', [dq], '( %s /\\ A. v e. %s ( v =/= 1 -> ( %s ` v ) = ( ( %s - %s ) / ( v - 1 ) ) ) )' % (HOL(DQP, UO), UO, DQP, LE.GV('v', PAR), LE.GV('1', PAR)))],
             HOL(DQP, UO))
    FH = LE.tsub(L.split_imp(SE['zl3fh'])[0], {'I': I1, 'J': I2, 'E': EPS, 'R': RM, 'D': DQP, 'P': PAR})
    hyp = D(w, A, '3jca', [D(w, A, 'jca', [hI, hJ], '( %s /\\ %s )' % (HOL(I1, 'CC'), HOL(I2, 'CC'))), D(w, A, 'jca', [B['mpa'], D(w, A, 'jca', [ec, rm_cc(w, A)], '( %s e. CC /\\ %s e. CC )' % (EPS, RM))],
                                                                                                                  '( %s /\\ ( %s e. CC /\\ %s e. CC ) )' % (MPA, EPS, RM)), hdq], FH)
    assert LE.FG(I1, I2, EPS, RM, DQP, PAR) == FC
    w.qed([D(w, A, 'syl', [hyp, w.inst('zl3fh')], Cc)], 'idi', SE['zl3fch'])
    goe(w)


def il_sub(w, C, v, X, P=None):
    """closed ( v = X -> ILG(C,v,P) = ILG(C,X,P) )"""
    P = P or PAR
    ph = '%s = %s' % (v, X)
    TH = LE.THG(C, 'y', P)
    ex = lambda e: '( ( ( %s + %s ) / 2 ) - 1 )' % (e, P)
    body = lambda e: '( %s x. ( y ^c %s ) )' % (TH, ex(e))
    e1 = w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (ph, v, P, X, P))], 'oveq1d', '( %s -> ( ( %s + %s ) / 2 ) = ( ( %s + %s ) / 2 ) )' % (ph, v, P, X, P))],
                            'oveq1d', '( %s -> %s = %s )' % (ph, ex(v), ex(X)))], 'oveq2d', '( %s -> ( y ^c %s ) = ( y ^c %s ) )' % (ph, ex(v), ex(X)))], 'oveq2d', '( %s -> %s = %s )' % (ph, body(v), body(X)))
    ph2 = '( %s /\\ t e. RR+ )' % ph
    b2 = w.s([w.s([e1], 'ad2antrr', '( ( %s /\\ y e. ( 1 (,) t ) ) -> %s = %s )' % (ph2, body(v), body(X)))], 'itgeq2dv',
             '( %s -> S. ( 1 (,) t ) %s _d y = S. ( 1 (,) t ) %s _d y )' % (ph2, body(v), body(X)))
    IM = lambda e: '( t e. RR+ |-> S. ( 1 (,) t ) %s _d y )' % body(e)
    m = w.s([b2], 'mpteq2dva', '( %s -> %s = %s )' % (ph, IM(v), IM(X)))
    return w.s([m], 'fveq2d', '( %s -> %s = %s )' % (ph, LE.ILG(C, v, P), LE.ILG(C, X, P)))


def fc_body(v):
    return ('( ( ( ( ( %s ` %s ) + ( %s x. ( %s ` ( 1 - %s ) ) ) ) x. %s ) - ( %s x. ( %s / 2 ) ) ) + ( %s x. ( %s ` %s ) ) )'
            % (I1, v, EPS, I2, v, LE.GV(v, PAR), RM, LE.HV(v, PAR), RM, DQP, v))


assert FC == '( v e. %s |-> %s )' % (UO, fc_body('v'))


def fc_sub(w, X):
    """closed ( v = X -> fc_body(v) = fc_body(X) )"""
    ph = 'v = %s' % X
    a = w.s([], 'fveq2', '( %s -> ( %s ` v ) = ( %s ` %s ) )' % (ph, I1, I1, X))
    b = w.s([w.s([w.s([], 'oveq2', '( %s -> ( 1 - v ) = ( 1 - %s ) )' % (ph, X))], 'fveq2d', '( %s -> ( %s ` ( 1 - v ) ) = ( %s ` ( 1 - %s ) ) )' % (ph, I2, I2, X))], 'oveq2d',
            '( %s -> ( %s x. ( %s ` ( 1 - v ) ) ) = ( %s x. ( %s ` ( 1 - %s ) ) ) )' % (ph, EPS, I2, EPS, I2, X))
    ab = w.s([a, b], 'oveq12d', '( %s -> ( ( %s ` v ) + ( %s x. ( %s ` ( 1 - v ) ) ) ) = ( ( %s ` %s ) + ( %s x. ( %s ` ( 1 - %s ) ) ) ) )' % (ph, I1, EPS, I2, I1, X, EPS, I2, X))
    g = vsub(w, lambda q: LE.GV(q, PAR), 'v', X)
    h = vsub(w, lambda q: LE.HV(q, PAR), 'v', X)
    L_ = lambda q: '( ( %s ` %s ) + ( %s x. ( %s ` ( 1 - %s ) ) ) )' % (I1, q, EPS, I2, q)
    t1 = w.s([ab, g], 'oveq12d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ph, L_('v'), LE.GV('v', PAR), L_(X), LE.GV(X, PAR)))
    t2 = w.s([w.s([h], 'oveq1d', '( %s -> ( %s / 2 ) = ( %s / 2 ) )' % (ph, LE.HV('v', PAR), LE.HV(X, PAR)))], 'oveq2d',
             '( %s -> ( %s x. ( %s / 2 ) ) = ( %s x. ( %s / 2 ) ) )' % (ph, RM, LE.HV('v', PAR), RM, LE.HV(X, PAR)))
    t3 = w.s([w.s([], 'fveq2', '( %s -> ( %s ` v ) = ( %s ` %s ) )' % (ph, DQP, DQP, X))], 'oveq2d', '( %s -> ( %s x. ( %s ` v ) ) = ( %s x. ( %s ` %s ) ) )' % (ph, RM, DQP, RM, DQP, X))
    t12 = w.s([t1, t2], 'oveq12d', '( %s -> ( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) = ( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) )' % (ph, L_('v'), LE.GV('v', PAR), RM, LE.HV('v', PAR), L_(X), LE.GV(X, PAR), RM, LE.HV(X, PAR)))
    return w.s([t12, t3], 'oveq12d', '( %s -> %s = %s )' % (ph, fc_body('v'), fc_body(X)))


# ---------------------------------------------------------------- zl3fcv
if wante('zl3fcv', MAIN):
    w = W('zl3fcv', 'The value of the continuation ` F ` at ` Z =/= 1 ` in ` U ` .')
    A, Cc = ante_e('zl3fcv')
    pr = D(w, A, 'simpl', [], PR)
    zu = D(w, A, 'simprl', [], 'Z e. %s' % UO); z1 = D(w, A, 'simprr', [], 'Z =/= 1')
    B = pr_base(w, A, pr)
    zc, _, _ = uo_mem(w, A, 'Z', zu)
    fv = D(w, A, 'syl', [zu, w.s([fc_sub(w, 'Z'), w.s([], 'eqid', '%s = %s' % (FC, FC)), w.s([], 'ovex', '%s e. _V' % fc_body('Z'))], 'fvmpt', '( Z e. %s -> ( %s ` Z ) = %s )' % (UO, FC, fc_body('Z')))],
           '( %s ` Z ) = %s' % (FC, fc_body('Z')))
    i1 = D(w, A, 'syl', [zc, w.s([il_sub(w, CYM, 'w', 'Z'), w.s([], 'eqid', '%s = %s' % (I1, I1)), w.s([], 'fvex', '%s e. _V' % LE.ILG(CYM, 'Z', PAR))], 'fvmpt',
                                  '( Z e. CC -> ( %s ` Z ) = %s )' % (I1, LE.ILG(CYM, 'Z', PAR)))], '( %s ` Z ) = %s' % (I1, LE.ILG(CYM, 'Z', PAR)))
    omz = D(w, A, 'subcld', [cst(w, A, 'ax-1cn', '1 e. CC'), zc], '( 1 - Z ) e. CC')
    i2 = D(w, A, 'syl', [omz, w.s([il_sub(w, CYBM, 'w', '( 1 - Z )'), w.s([], 'eqid', '%s = %s' % (I2, I2)), w.s([], 'fvex', '%s e. _V' % LE.ILG(CYBM, '( 1 - Z )', PAR))], 'fvmpt',
                                   '( ( 1 - Z ) e. CC -> ( %s ` ( 1 - Z ) ) = %s )' % (I2, LE.ILG(CYBM, '( 1 - Z )', PAR)))], '( %s ` ( 1 - Z ) ) = %s' % (I2, LE.ILG(CYBM, '( 1 - Z )', PAR)))
    dq = D(w, A, 'syl', [B['mpa'], w.inst('zl3dq')], LE.tsub(L.split_imp(SE['zl3dq'])[1], {'P': PAR}))
    VALv = lambda v: '( %s =/= 1 -> ( %s ` %s ) = ( ( %s - %s ) / ( %s - 1 ) ) )' % (v, DQP, v, LE.GV(v, PAR), LE.GV('1', PAR), v)
    ralv = D(w, A, 'simprd', [D(w, A, 'simpld', [dq], '( %s /\\ A. v e. %s %s )' % (HOL(DQP, UO), UO, VALv('v')))], 'A. v e. %s %s' % (UO, VALv('v')))
    subq = w.s([w.s([], 'neeq1', '( v = Z -> ( v =/= 1 <-> Z =/= 1 ) )'),
                w.s([w.s([], 'fveq2', '( v = Z -> ( %s ` v ) = ( %s ` Z ) )' % (DQP, DQP)),
                     w.s([vsub(w, lambda q: LE.GV(q, PAR), 'v', 'Z'), w.s([], 'oveq1', '( v = Z -> ( v - 1 ) = ( Z - 1 ) )')], 'oveq12d' if False else 'idi', '') if False else
                     w.s([w.s([vsub(w, lambda q: LE.GV(q, PAR), 'v', 'Z')], 'oveq1d', '( v = Z -> ( %s - %s ) = ( %s - %s ) )' % (LE.GV('v', PAR), LE.GV('1', PAR), LE.GV('Z', PAR), LE.GV('1', PAR))),
                          w.s([], 'oveq1', '( v = Z -> ( v - 1 ) = ( Z - 1 ) )')], 'oveq12d',
                         '( v = Z -> ( ( %s - %s ) / ( v - 1 ) ) = ( ( %s - %s ) / ( Z - 1 ) ) )' % (LE.GV('v', PAR), LE.GV('1', PAR), LE.GV('Z', PAR), LE.GV('1', PAR)))], 'eqeq12d',
                    '( v = Z -> ( ( %s ` v ) = ( ( %s - %s ) / ( v - 1 ) ) <-> ( %s ` Z ) = ( ( %s - %s ) / ( Z - 1 ) ) ) )' % (DQP, LE.GV('v', PAR), LE.GV('1', PAR), DQP, LE.GV('Z', PAR), LE.GV('1', PAR)))],
               'imbi12d', '( v = Z -> ( %s <-> %s ) )' % (VALv('v'), VALv('Z')))
    dqz = D(w, A, 'mpd', [z1, D(w, A, 'mpd', [ralv, D(w, A, 'syl', [zu, w.s([subq], 'rspcv', '( Z e. %s -> ( A. v e. %s %s -> %s ) )' % (UO, UO, VALv('v'), VALv('Z')))], '( A. v e. %s %s -> %s )' % (UO, VALv('v'), VALv('Z')))], VALv('Z'))],
            '( %s ` Z ) = ( ( %s - %s ) / ( Z - 1 ) )' % (DQP, LE.GV('Z', PAR), LE.GV('1', PAR)))
    L_ = lambda q: '( ( %s ` %s ) + ( %s x. ( %s ` ( 1 - %s ) ) ) )' % (I1, q, EPS, I2, q)
    le = D(w, A, 'oveq12d', [i1, D(w, A, 'oveq2d', [i2], '( %s x. ( %s ` ( 1 - Z ) ) ) = ( %s x. %s )' % (EPS, I2, EPS, LE.ILG(CYBM, '( 1 - Z )', PAR)))], '%s = %s' % (L_('Z'), LE.L0('Z')))
    e2 = D(w, A, 'oveq12d', [D(w, A, 'oveq1d', [D(w, A, 'oveq1d', [le], '( %s x. %s ) = ( %s x. %s )' % (L_('Z'), LE.GV('Z', PAR), LE.L0('Z'), LE.GV('Z', PAR)))],
                                                '( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) = ( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) )' % (L_('Z'), LE.GV('Z', PAR), RM, LE.HV('Z', PAR), LE.L0('Z'), LE.GV('Z', PAR), RM, LE.HV('Z', PAR))),
                             D(w, A, 'oveq2d', [dqz], '( %s x. ( %s ` Z ) ) = ( %s x. ( ( %s - %s ) / ( Z - 1 ) ) )' % (RM, DQP, RM, LE.GV('Z', PAR), LE.GV('1', PAR)))],
           '%s = %s' % (fc_body('Z'), LE.FV('Z')))
    w.qed([D(w, A, 'eqtrd', [fv, e2], Cc)], 'idi', SE['zl3fcv'])
    goe(w)


# ---------------------------------------------------------------- zl3g1
if wante('zl3g1', MAIN):
    w = W('zl3g1', 'In the zeta case ` M = 1 ` the value ` g ( 1 ) = pi ^ ( 1 / 2 ) / Gamma ( 1 / 2 ) ` is 1: along ` s = 1 + 1 / j ` , ` ( s - 1 ) F ( s ) + g ( 1 ) = ( s - 1 ) zeta ( s ) = E ( s ) ` tends to ` g ( 1 ) ` ( ~ zl3fch ) and to ` E ( 1 ) = 1 ` ( ~ zl1e1 , ~ zl1ehol ).')
    A, Cc = ante_e('zl3g1')
    pr = D(w, A, 'simpl', [], PR); m1 = D(w, A, 'simpr', [], 'M = 1')
    B = pr_base(w, A, pr)
    ch, mn = B['ch'], B['mn']
    yd = D(w, A, 'simprd', [ch], 'Y e. ( Base ` ( DChr ` M ) )')
    m1s = D(w, A, 'syl', [w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('zl3m1')], '( %s = 0 /\\ %s = 1 )' % (PAR, EPS))
    p0 = D(w, A, 'simpld', [m1s], '%s = 0' % PAR)
    rm1 = D(w, A, 'iftrued', [m1], '%s = 1' % RM)
    g1 = LE.GV('1', PAR)
    fch = D(w, A, 'syl', [pr, w.inst('zl3fch')], HOL(FC, UO))
    fcn = D(w, A, 'simpld', [fch], '%s e. ( %s -cn-> CC )' % (FC, UO))
    E_ = '( M DChrLF Y )'
    HP0 = "( `' Re \" ( 0 (,) +oo ) )"
    ehol = D(w, A, 'syl', [ch, w.inst('zl1ehol')], HOL(E_, HP0))
    ecn = D(w, A, 'simpld', [ehol], '%s e. ( %s -cn-> CC )' % (E_, HP0))
    # the sequence s_j = 1 / j + 1
    Sb = lambda q: '( ( 1 / %s ) + 1 )' % q
    S = '( n e. NN |-> %s )' % Sb('n')
    R1 = '( n e. NN |-> ( 1 / n ) )'
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); one = D(w, A, '1zzd', [], '1 e. ZZ')

    def sfacts(v):
        Av_ = '( %s /\\ %s e. NN )' % (A, v)
        vn = w.s([], 'simpr', '( %s -> %s e. NN )' % (Av_, v))
        clv = Closure(w, Av_, {v: ('NN', vn)})
        sv_ = Sb(v); iv = '( 1 / %s )' % v
        svr, svc = clv.mem(sv_, 'RR'), clv.mem(sv_, 'CC')
        ivp = clv.mem(iv, 'RR+')
        s1_ = linarith(w, Av_, [D(w, Av_, 'rpgt0d', [ivp], '0 < %s' % iv)], '1 < %s' % sv_, closure=clv)
        iv1 = D(w, Av_, 'mpbird', [linarith(w, Av_, [D(w, Av_, 'nnge1d', [vn], '1 <_ %s' % v)], '1 <_ ( %s x. 1 )' % v, closure=clv),
                                   D(w, Av_, 'ledivmuld', [cst(w, Av_, '1re', '1 e. RR'), cst(w, Av_, '1re', '1 e. RR'), clv.mem(v, 'RR+')], '( %s <_ 1 <-> 1 <_ ( %s x. 1 ) )' % (iv, v))], '%s <_ 1' % iv)
        s2_ = linarith(w, Av_, [iv1], '%s <_ 2' % sv_, closure=clv)
        rs_ = D(w, Av_, 'rered', [svr], '( Re ` %s ) = %s' % (sv_, sv_))
        rngU_ = D(w, Av_, 'jca', [D(w, Av_, 'breqtrrd', [linarith(w, Av_, [s1_], '-u 1 < %s' % sv_, closure=clv), rs_], '-u 1 < ( Re ` %s )' % sv_),
                                  D(w, Av_, 'eqbrtrd', [rs_, linarith(w, Av_, [s2_], '%s < 3' % sv_, closure=clv)], '( Re ` %s ) < 3' % sv_)], '( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 )' % (sv_, sv_))
        sU_ = D(w, Av_, 'mpbird', [D(w, Av_, 'jca', [svc, rngU_], '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 ) )' % (sv_, sv_, sv_)),
                                   D(w, Av_, 'syl2anc', [D(w, Av_, 'rexrd', [cst(w, Av_, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, Av_, 'rexrd', [cst(w, Av_, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                                     '( %s e. %s <-> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 ) ) )' % (sv_, UO, sv_, sv_, sv_))], '%s e. %s' % (sv_, UO))
        rngH_ = D(w, Av_, 'jca', [D(w, Av_, 'breqtrrd', [linarith(w, Av_, [s1_], '0 < %s' % sv_, closure=clv), rs_], '0 < ( Re ` %s )' % sv_),
                                  D(w, Av_, 'ltpnfd', [D(w, Av_, 'recld', [svc], '( Re ` %s ) e. RR' % sv_)], '( Re ` %s ) < +oo' % sv_)], '( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo )' % (sv_, sv_))
        sH_ = D(w, Av_, 'mpbird', [D(w, Av_, 'jca', [svc, rngH_], '( %s e. CC /\\ ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) )' % (sv_, sv_, sv_)),
                                   D(w, Av_, 'syl2anc', [cst(w, Av_, '0xr', '0 e. RR*'), cst(w, Av_, 'pnfxr', '+oo e. RR*'), w.inst('z6melst')],
                                     '( %s e. %s <-> ( %s e. CC /\\ ( 0 < ( Re ` %s ) /\\ ( Re ` %s ) < +oo ) ) )' % (sv_, HP0, sv_, sv_, sv_))], '%s e. %s' % (sv_, HP0))
        return dict(Av=Av_, vn=vn, s=sv_, sc=svc, sr=svr, ivp=ivp, s1=s1_, rs=rs_, sU=sU_, sH=sH_)
    F_ = sfacts('j')
    Aj, jn, s, sc, sr, ijp, s1, rs, sU, sH = F_['Av'], F_['vn'], F_['s'], F_['sc'], F_['sr'], F_['ivp'], F_['s1'], F_['rs'], F_['sU'], F_['sH']
    ij = '( 1 / j )'
    r1v = fv1(w, Aj, 'n', 'NN', lambda q: '( 1 / %s )' % q, 'j', jn, 'ovex')
    sv = fv1(w, Aj, 'n', 'NN', Sb, 'j', jn, 'ovex')
    Fn = sfacts('n')
    lim0 = D(w, A, 'syl', [cst(w, A, 'ax-1cn', '1 e. CC'), w.inst('divcnv')], '%s ~~> 0' % R1)
    cS = D(w, A, 'climaddc1', [nnz, one, lim0, cst(w, A, 'ax-1cn', '1 e. CC'), D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % S),
                               D(w, Aj, 'eqeltrd', [r1v, D(w, Aj, 'rpcnd', [ijp], '%s e. CC' % ij)], '( %s ` j ) e. CC' % R1),
                               D(w, Aj, 'eqtr4d', [sv, D(w, Aj, 'oveq1d', [r1v], '( ( %s ` j ) + 1 ) = %s' % (R1, s))], '( %s ` j ) = ( ( %s ` j ) + 1 )' % (S, R1))],
           '%s ~~> ( 0 + 1 )' % S)
    cS1 = D(w, A, 'breqtrd', [cS, cst(w, A, '0p1e1', '( 0 + 1 ) = 1')], '%s ~~> 1' % S)
    rs1 = D(w, Aj, 'breqtrrd', [s1, rs], '1 < ( Re ` %s )' % s)
    sne1 = D(w, Aj, 'gtned', [s1], '%s =/= 1' % s)
    # S maps into U and into HP0
    SU = D(w, A, 'fmptd', [Fn['sU'], w.s([], 'eqid', '%s = %s' % (S, S))], '%s : NN --> %s' % (S, UO))
    SH = D(w, A, 'fmptd', [Fn['sH'], w.s([], 'eqid', '%s = %s' % (S, S))], '%s : NN --> %s' % (S, HP0))
    oneU = D(w, A, 'mpbird', [D(w, A, 'jca', [cst(w, A, 'ax-1cn', '1 e. CC'), D(w, A, 'jca', [D(w, A, 'breqtrrd', [D(w, A, 'lttrd', [cst(w, A, 'neg1rr', '-u 1 e. RR'), cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), cst(w, A, 'neg1lt0', '-u 1 < 0'), cst(w, A, '0lt1', '0 < 1')], '-u 1 < 1'),
                                                                                                   cst(w, A, 're1', '( Re ` 1 ) = 1')], '-u 1 < ( Re ` 1 )'),
                                                                                  D(w, A, 'eqbrtrd', [cst(w, A, 're1', '( Re ` 1 ) = 1'), cst(w, A, '1lt3', '1 < 3')], '( Re ` 1 ) < 3')], '( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 )')],
                                        '( 1 e. CC /\\ ( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 ) )'),
                              D(w, A, 'syl2anc', [D(w, A, 'rexrd', [cst(w, A, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, A, 'rexrd', [cst(w, A, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                                '( 1 e. %s <-> ( 1 e. CC /\\ ( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 ) ) )' % UO)], '1 e. %s' % UO)
    oneH = D(w, A, 'mpbird', [D(w, A, 'jca', [cst(w, A, 'ax-1cn', '1 e. CC'), D(w, A, 'jca', [D(w, A, 'breqtrrd', [cst(w, A, '0lt1', '0 < 1'), cst(w, A, 're1', '( Re ` 1 ) = 1')], '0 < ( Re ` 1 )'),
                                                                                  D(w, A, 'eqbrtrd', [cst(w, A, 're1', '( Re ` 1 ) = 1'), D(w, A, 'ltpnfd', [cst(w, A, '1re', '1 e. RR')], '1 < +oo')], '( Re ` 1 ) < +oo')], '( 0 < ( Re ` 1 ) /\\ ( Re ` 1 ) < +oo )')],
                                        '( 1 e. CC /\\ ( 0 < ( Re ` 1 ) /\\ ( Re ` 1 ) < +oo ) )'),
                              D(w, A, 'syl2anc', [cst(w, A, '0xr', '0 e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*'), w.inst('z6melst')],
                                '( 1 e. %s <-> ( 1 e. CC /\\ ( 0 < ( Re ` 1 ) /\\ ( Re ` 1 ) < +oo ) ) )' % HP0)], '1 e. %s' % HP0)
    cF = D(w, A, 'climcncf', [nnz, one, fcn, SU, cS1, oneU], '( %s o. %s ) ~~> ( %s ` 1 )' % (FC, S, FC))
    cE = D(w, A, 'climcncf', [nnz, one, ecn, SH, cS1, oneH], '( %s o. %s ) ~~> ( %s ` 1 )' % (E_, S, E_))
    # the pointwise identity at a free s
    As0 = '( %s /\\ s e. CC )' % A
    As = '( %s /\\ ( 1 < ( Re ` s ) /\\ ( s e. %s /\\ s e. %s ) ) )' % (As0, UO, HP0)
    L2 = lambda st, f: ad(w, As, ad(w, As0, st, f), f)
    s_c = D(w, As, 'simplr', [], 's e. CC'); s_1 = D(w, As, 'simprl', [], '1 < ( Re ` s )')
    s_U = D(w, As, 'simprrl' if False else 'simprrl', [], 's e. %s' % UO) if False else D(w, As, 'simpld', [D(w, As, 'simprr', [], '( s e. %s /\\ s e. %s )' % (UO, HP0))], 's e. %s' % UO)
    s_H = D(w, As, 'simprd', [D(w, As, 'simprr', [], '( s e. %s /\\ s e. %s )' % (UO, HP0))], 's e. %s' % HP0)
    prs = L2(pr, PR)
    MELs = '( 1 < ( Re ` s ) -> ( %s x. %s ) = ( %s - ( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) ) )' % (Z3G('s'), LSs('s'), LE.L0('s'), RM)
    mel = w.s([w.s([], 'zl3mel', '( %s -> A. s e. CC %s )' % (PR, MELs))], 'r19.21bi', '( ( %s /\\ s e. CC ) -> %s )' % (PR, MELs))
    mels = D(w, As, 'mpd', [s_1, D(w, As, 'syl', [D(w, As, 'jca', [prs, s_c], '( %s /\\ s e. CC )' % PR), mel], MELs)], MELs[MELs.index(' -> ') + 4:-2])
    LSV = LSs('s')
    DSER = '( 1 < ( Re ` s ) -> ( %s ` s ) = ( ( s - 1 ) x. %s ) )' % (E_, LSV)
    chs = L2(ch, '( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) )')
    dser = w.s([w.s([], 'zl1dser', '( ( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) ) -> A. s e. %s %s )' % (HP0, DSER))], 'r19.21bi', '( ( ( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) ) /\\ s e. %s ) -> %s )' % (HP0, DSER))
    es = D(w, As, 'mpd', [s_1, D(w, As, 'syl', [D(w, As, 'jca', [chs, s_H], '( ( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) ) /\\ s e. %s )' % HP0), dser], DSER)],
           '( %s ` s ) = ( ( s - 1 ) x. %s )' % (E_, LSV))
    ppS = L2(B['pp'], '%s e. { 0 , 1 }' % PAR)
    pn_, prr, p00, p11 = p01(w, As, ppS, PAR)
    pcc = D(w, As, 'recnd', [prr], '%s e. CC' % PAR)
    spc, reW, imW = reim_w(w, As, 's', s_c, pcc, prr, P=PAR)
    rsr = D(w, As, 'recld', [s_c], '( Re ` s ) e. RR')
    clS = Closure(w, As, {'( Re ` s )': ('RR', rsr), PAR: [('RR', prr), ('ge0', p00)]})
    w0 = D(w, As, 'breqtrrd', [linarith(w, As, [s_1, p00], '0 < ( ( ( Re ` s ) + %s ) / 2 )' % PAR, closure=clS), reW], '0 < ( Re ` %s )' % LE.WV('s', PAR))
    gga = D(w, As, 'syl2anc', [L2(B['mpa'], MPA), D(w, As, 'jca', [s_c, w0], '( s e. CC /\\ 0 < ( Re ` %s ) )' % LE.WV('s', PAR)), w.inst('zl3gga')],
            '( %s x. %s ) = 1' % (LE.GV('s', PAR), Z3G('s')))
    G_, H_ = LE.GV('s', PAR), LE.HV('s', PAR)
    ghl = D(w, As, 'syl', [L2(B['mpa'], MPA), w.inst('zl3ghl')], LE.tsub(L.split_imp(SE['zl3ghl'])[1], {'P': PAR}))
    Hxm, Gxm = '( x e. %s |-> %s )' % (UO, LE.HV('x', PAR)), '( x e. %s |-> %s )' % (UO, LE.GV('x', PAR))
    hf = D(w, As, 'syl', [D(w, As, 'simpld', [D(w, As, 'simpld', [ghl], HOL(Hxm, UO))], '%s e. ( %s -cn-> CC )' % (Hxm, UO)), w.inst('cncff')], '%s : %s --> CC' % (Hxm, UO))
    gf = D(w, As, 'syl', [D(w, As, 'simpld', [D(w, As, 'simprd', [ghl], HOL(Gxm, UO))], '%s e. ( %s -cn-> CC )' % (Gxm, UO)), w.inst('cncff')], '%s : %s --> CC' % (Gxm, UO))
    hc = D(w, As, 'eqeltrrd', [fv1(w, As, 'x', UO, lambda q: LE.HV(q, PAR), 's', s_U, 'ovex'), D(w, As, 'ffvelcdmd', [hf, s_U], '( %s ` s ) e. CC' % Hxm)], '%s e. CC' % H_)
    gc = D(w, As, 'eqeltrrd', [fv1(w, As, 'x', UO, lambda q: LE.GV(q, PAR), 's', s_U, 'ovex'), D(w, As, 'ffvelcdmd', [gf, s_U], '( %s ` s ) e. CC' % Gxm)], '%s e. CC' % G_)
    g1c = D(w, As, 'eqeltrrd', [fv1(w, As, 'x', UO, lambda q: LE.GV(q, PAR), '1', L2(oneU, '1 e. %s' % UO), 'ovex'), D(w, As, 'ffvelcdmd', [gf, L2(oneU, '1 e. %s' % UO)], '( %s ` 1 ) e. CC' % Gxm)],
            '%s e. CC' % g1)
    # IL values are complex
    ilc = lambda ta, TA_, C, X, xc: D(w, As, 'eqeltrrd', [D(w, As, 'syl', [xc, w.s([il_sub(w, C, 'w', X), w.s([], 'eqid', '%s = %s' % (LE.MPW(C, PAR), LE.MPW(C, PAR))), w.s([], 'fvex', '%s e. _V' % LE.ILG(C, X, PAR))], 'fvmpt',
                                                                                  '( %s e. CC -> ( %s ` %s ) = %s )' % (X, LE.MPW(C, PAR), X, LE.ILG(C, X, PAR)))], '( %s ` %s ) = %s' % (LE.MPW(C, PAR), X, LE.ILG(C, X, PAR))),
                                                           D(w, As, 'ffvelcdmd', [D(w, As, 'syl', [D(w, As, 'simpld', [D(w, As, 'syl', [L2(ta, TA_), w.inst('zl3ilh')], HOL(LE.MPW(C, PAR), 'CC'))], '%s e. ( CC -cn-> CC )' % LE.MPW(C, PAR)),
                                                                                                   w.inst('cncff')], '%s : CC --> CC' % LE.MPW(C, PAR)), xc], '( %s ` %s ) e. CC' % (LE.MPW(C, PAR), X))],
                                                  '%s e. CC' % LE.ILG(C, X, PAR))
    omsc = D(w, As, 'subcld', [cst(w, As, 'ax-1cn', '1 e. CC'), s_c], '( 1 - s ) e. CC')
    i1c = ilc(B['taY'], B['TAY'], CYM, 's', s_c); i2c = ilc(B['taB'], B['TAB'], CYBM, '( 1 - s )', omsc)
    ec = eps_cl(w, As, L2(ch, '( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) )'), ppS)
    l0c = D(w, As, 'addcld', [i1c, D(w, As, 'mulcld', [ec, i2c], '( %s x. %s ) e. CC' % (EPS, LE.ILG(CYBM, '( 1 - s )', PAR)))], '%s e. CC' % LE.L0('s'))
    sne1 = D(w, As, 'gtned', [D(w, As, 'eqbrtrd' if False else 'breqtrd', [s_1, D(w, As, 'eqidd', [], '( Re ` s ) = ( Re ` s )')], '1 < ( Re ` s )')], '( Re ` s ) =/= 1') if False else None
    ad1 = w.s([w.s([], 'fveq2', '( s = 1 -> ( Re ` s ) = ( Re ` 1 ) )'), w.s([], 're1', '( Re ` 1 ) = 1')], 'eqtrdi', '( s = 1 -> ( Re ` s ) = 1 )')
    sne1 = w.s([D(w, As, 'gtned', [s_1], '( Re ` s ) =/= 1'), w.s([ad1], 'necon3i', '( ( Re ` s ) =/= 1 -> s =/= 1 )')], 'syl', '( %s -> s =/= 1 )' % As)
    ad0 = w.s([w.s([], 'fveq2', '( s = 0 -> ( Re ` s ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( s = 0 -> ( Re ` s ) = 0 )')
    sne0 = w.s([D(w, As, 'gt0ne0d', [linarith(w, As, [s_1], '0 < ( Re ` s )', closure=clS)], '( Re ` s ) =/= 0'), w.s([ad0], 'necon3i', '( ( Re ` s ) =/= 0 -> s =/= 0 )')], 'syl', '( %s -> s =/= 0 )' % As)
    p0s = L2(p0, '%s = 0' % PAR)
    gsh = D(w, As, 'oveq1d', [D(w, As, 'eqtrd', [D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [p0s], '( s + %s ) = ( s + 0 )' % PAR)], '( ( s + %s ) / 2 ) = ( ( s + 0 ) / 2 )' % PAR),
                                                  D(w, As, 'oveq1d', [D(w, As, 'addridd', [s_c], '( s + 0 ) = s')], '( ( s + 0 ) / 2 ) = ( s / 2 )')], '( ( s + %s ) / 2 ) = ( s / 2 )' % PAR)],
            '%s = ( ( s / 2 ) x. %s )' % (G_, H_))
    rm1s = L2(rm1, '%s = 1' % RM)
    rmpr = D(w, As, 'eleqtrrd', [cst(w, As, '1ex' if False else 'idi', '') if False else w.s([w.s([w.s([], '1ex', '1 e. _V')], 'prid2', '1 e. { 0 , 1 }')], 'a1i', '( %s -> 1 e. { 0 , 1 } )' % As), rm1s], '%s e. { 0 , 1 }' % RM) if False else \
        D(w, As, 'eqeltrd', [rm1s, w.s([w.s([w.s([], '1ex', '1 e. _V')], 'prid2', '1 e. { 0 , 1 }')], 'a1i', '( %s -> 1 e. { 0 , 1 } )' % As)], '%s e. { 0 , 1 }' % RM)
    FALA = LE.tsub(L.split_imp(SE['zl3fal'])[0], {'L': LE.L0('s'), 'H': H_, 'G': G_, 'Z': 's', 'R': RM, 'B': '1'})
    FALC = LE.tsub(L.split_imp(SE['zl3fal'])[1], {'L': LE.L0('s'), 'H': H_, 'G': G_, 'Z': 's', 'R': RM, 'B': '1'})
    fal_h = D(w, As, '3jca', [D(w, As, 'jca', [D(w, As, 'jca', [l0c, hc], '( %s e. CC /\\ %s e. CC )' % (LE.L0('s'), H_)), D(w, As, 'jca', [gc, cst(w, As, 'ax-1cn', '1 e. CC')], '( %s e. CC /\\ 1 e. CC )' % G_)],
                                               '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ 1 e. CC ) )' % (LE.L0('s'), H_, G_)),
                              D(w, As, '3jca', [s_c, sne0, sne1], '( s e. CC /\\ s =/= 0 /\\ s =/= 1 )'),
                              D(w, As, 'jca', [rmpr, D(w, As, 'a1d', [D(w, As, 'jca', [gsh, D(w, As, 'eqidd', [], '1 = 1')], '( %s = ( ( s / 2 ) x. %s ) /\\ 1 = 1 )' % (G_, H_))],
                                                       '( %s = 1 -> ( %s = ( ( s / 2 ) x. %s ) /\\ 1 = 1 ) )' % (RM, G_, H_))], '( %s e. { 0 , 1 } /\\ ( %s = 1 -> ( %s = ( ( s / 2 ) x. %s ) /\\ 1 = 1 ) ) )' % (RM, RM, G_, H_))],
                FALA)
    fal = D(w, As, 'syl', [fal_h, w.inst('zl3fal')], '%s = ( ( %s - ( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) ) x. %s )' % (
        '( ( ( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) + ( %s x. ( ( %s - 1 ) / ( s - 1 ) ) ) ) + ( %s / ( s - 1 ) ) )' % (LE.L0('s'), G_, RM, H_, RM, G_, RM), LE.L0('s'), RM, G_))
    LAM = '( %s - ( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) )' % (LE.L0('s'), RM)
    chsZ = LE.tsub(L.split_imp(Z2S['zl2chs'])[1], {'N': 'M', 'X': 'Y', 'Z': 's'})
    lsc = D(w, As, 'simpld', [D(w, As, 'syl2anc', [chs, D(w, As, 'jca', [s_c, s_1], '( s e. CC /\\ 1 < ( Re ` s ) )'), w.inst('zl2chs')], chsZ)], '%s e. CC' % LSV)
    Wsp = LE.WV('s', PAR)
    wdm = D(w, As, 'syl2anc', [D(w, As, 'halfcld', [spc], '%s e. CC' % Wsp), w0, w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % Wsp)
    clM = Closure(w, As, {'M': ('NN', L2(mn, 'M e. NN')), '_pi': ('RR+', cst(w, As, 'pirp', '_pi e. RR+'))})
    gfc = D(w, As, 'mulcld', [D(w, As, 'cxpcld', [clM.mem('( M / _pi )', 'CC'), D(w, As, 'halfcld', [spc], '%s e. CC' % Wsp)], '( ( M / _pi ) ^c %s ) e. CC' % Wsp),
                              D(w, As, 'syl', [wdm, w.inst('gamcl')], '( _G ` %s ) e. CC' % Wsp)], '%s e. CC' % Z3G('s'))
    lsl = chain(w, As, [LSV, '( 1 x. %s )' % LSV, '( ( %s x. %s ) x. %s )' % (G_, Z3G('s'), LSV), '( %s x. ( %s x. %s ) )' % (G_, Z3G('s'), LSV), '( %s x. %s )' % (G_, LAM), '( %s x. %s )' % (LAM, G_)],
                [('r', D(w, As, 'mullidd', [lsc], '( 1 x. %s ) = %s' % (LSV, LSV))),
                 ('r', D(w, As, 'oveq1d', [gga], '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (G_, Z3G('s'), LSV, LSV))),
                 D(w, As, 'mulassd', [gc, gfc, lsc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (G_, Z3G('s'), LSV, G_, Z3G('s'), LSV)),
                 D(w, As, 'oveq2d', [mels], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (G_, Z3G('s'), LSV, G_, LAM)),
                 D(w, As, 'mulcomd', [gc, D(w, As, 'subcld', [l0c, D(w, As, 'mulcld', [D(w, As, 'recnd', [D(w, As, 'rered' if False else 'eqeltrd', [rm1s, cst(w, As, '1re', '1 e. RR')], '%s e. RR' % RM)], '%s e. CC' % RM),
                                                                                           D(w, As, 'addcld', [D(w, As, 'reccld', [s_c, sne0], '( 1 / s ) e. CC'),
                                                                                                               D(w, As, 'reccld', [omsc, D(w, As, 'subne0d', [cst(w, As, 'ax-1cn', '1 e. CC'), s_c, D(w, As, 'necomd', [sne1], '1 =/= s')], '( 1 - s ) =/= 0')], '( 1 / ( 1 - s ) ) e. CC')],
                                                                                             '( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) e. CC')], '( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) e. CC' % RM)], '%s e. CC' % LAM)],
                   '( %s x. %s ) = ( %s x. %s )' % (G_, LAM, LAM, G_))])
    FALL = '( ( ( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) + ( %s x. ( ( %s - 1 ) / ( s - 1 ) ) ) ) + ( %s / ( s - 1 ) ) )' % (LE.L0('s'), G_, RM, H_, RM, G_, RM)
    assert FALC.strip() in ('( %s = ( %s x. %s ) )' % (FALL, LAM, G_), '%s = ( %s x. %s )' % (FALL, LAM, G_)), FALC[:100]
    FALC = '%s = ( %s x. %s )' % (FALL, LAM, G_)
    d = '( s - 1 )'
    dc = D(w, As, 'subcld', [s_c, cst(w, As, 'ax-1cn', '1 e. CC')], '%s e. CC' % d); dne = D(w, As, 'subne0d', [s_c, cst(w, As, 'ax-1cn', '1 e. CC'), sne1], '%s =/= 0' % d)
    X = '( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) )' % (LE.L0('s'), G_, RM, H_)
    xc = D(w, As, 'subcld', [D(w, As, 'mulcld', [l0c, gc], '( %s x. %s ) e. CC' % (LE.L0('s'), G_)),
                             D(w, As, 'mulcld', [D(w, As, 'recnd', [D(w, As, 'eqeltrd', [rm1s, cst(w, As, '1re', '1 e. RR')], '%s e. RR' % RM)], '%s e. CC' % RM), D(w, As, 'halfcld', [hc], '( %s / 2 ) e. CC' % H_)],
                               '( %s x. ( %s / 2 ) ) e. CC' % (RM, H_))], '%s e. CC' % X)
    Q1, Q2 = '( ( %s - %s ) / %s )' % (G_, g1, d), '( ( %s - 1 ) / %s )' % (G_, d)
    q1c = D(w, As, 'divcld', [D(w, As, 'subcld', [gc, g1c], '( %s - %s ) e. CC' % (G_, g1)), dc, dne], '%s e. CC' % Q1)
    q2c = D(w, As, 'divcld', [D(w, As, 'subcld', [gc, cst(w, As, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % G_), dc, dne], '%s e. CC' % Q2)
    fvs = D(w, As, 'syl2anc', [prs, D(w, As, 'jca', [s_U, sne1], '( s e. %s /\\ s =/= 1 )' % UO), w.inst('zl3fcv')], '( %s ` s ) = %s' % (FC, LE.FV('s')))
    assert LE.FV('s') == '( %s + ( %s x. %s ) )' % (X, RM, Q1)
    fvr = D(w, As, 'eqtrd', [fvs, D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [rm1s], '( %s x. %s ) = ( 1 x. %s )' % (RM, Q1, Q1))], '( %s + ( %s x. %s ) ) = ( %s + ( 1 x. %s ) )' % (X, RM, Q1, X, Q1))],
             '( %s ` s ) = ( %s + ( 1 x. %s ) )' % (FC, X, Q1))
    assert FALL == '( ( %s + ( %s x. %s ) ) + ( %s / %s ) )' % (X, RM, Q2, RM, d), FALL
    falr = D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [rm1s], '( %s x. %s ) = ( 1 x. %s )' % (RM, Q2, Q2))], '( %s + ( %s x. %s ) ) = ( %s + ( 1 x. %s ) )' % (X, RM, Q2, X, Q2)),
                                D(w, As, 'oveq1d', [rm1s], '( %s / %s ) = ( 1 / %s )' % (RM, d, d))], '%s = ( ( %s + ( 1 x. %s ) ) + ( 1 / %s ) )' % (FALL, X, Q2, d))
    dX = '( %s x. %s )' % (d, X)
    dxc = D(w, As, 'mulcld', [dc, xc], '%s e. CC' % dX)
    id1 = chain(w, As, ['( ( %s x. ( %s + ( 1 x. %s ) ) ) + %s )' % (d, X, Q1, g1), '( ( %s + ( %s x. ( 1 x. %s ) ) ) + %s )' % (dX, d, Q1, g1), '( ( %s + ( %s x. %s ) ) + %s )' % (dX, d, Q1, g1),
                        '( ( %s + ( %s - %s ) ) + %s )' % (dX, G_, g1, g1), '( %s + ( ( %s - %s ) + %s ) )' % (dX, G_, g1, g1), '( %s + %s )' % (dX, G_)],
                [D(w, As, 'oveq1d', [D(w, As, 'adddid', [dc, xc, D(w, As, 'mulcld', [cst(w, As, 'ax-1cn', '1 e. CC'), q1c], '( 1 x. %s ) e. CC' % Q1)], '( %s x. ( %s + ( 1 x. %s ) ) ) = ( %s + ( %s x. ( 1 x. %s ) ) )' % (d, X, Q1, dX, d, Q1))],
                   '( ( %s x. ( %s + ( 1 x. %s ) ) ) + %s ) = ( ( %s + ( %s x. ( 1 x. %s ) ) ) + %s )' % (d, X, Q1, g1, dX, d, Q1, g1)),
                 D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [D(w, As, 'oveq2d', [D(w, As, 'mullidd', [q1c], '( 1 x. %s ) = %s' % (Q1, Q1))], '( %s x. ( 1 x. %s ) ) = ( %s x. %s )' % (d, Q1, d, Q1))],
                                                     '( %s + ( %s x. ( 1 x. %s ) ) ) = ( %s + ( %s x. %s ) )' % (dX, d, Q1, dX, d, Q1))], '( ( %s + ( %s x. ( 1 x. %s ) ) ) + %s ) = ( ( %s + ( %s x. %s ) ) + %s )' % (dX, d, Q1, g1, dX, d, Q1, g1)),
                 D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [D(w, As, 'divcan2d', [D(w, As, 'subcld', [gc, g1c], '( %s - %s ) e. CC' % (G_, g1)), dc, dne], '( %s x. %s ) = ( %s - %s )' % (d, Q1, G_, g1))],
                                                     '( %s + ( %s x. %s ) ) = ( %s + ( %s - %s ) )' % (dX, d, Q1, dX, G_, g1))], '( ( %s + ( %s x. %s ) ) + %s ) = ( ( %s + ( %s - %s ) ) + %s )' % (dX, d, Q1, g1, dX, G_, g1, g1)),
                 D(w, As, 'addassd', [dxc, D(w, As, 'subcld', [gc, g1c], '( %s - %s ) e. CC' % (G_, g1)), g1c], '( ( %s + ( %s - %s ) ) + %s ) = ( %s + ( ( %s - %s ) + %s ) )' % (dX, G_, g1, g1, dX, G_, g1, g1)),
                 D(w, As, 'oveq2d', [D(w, As, 'npcand', [gc, g1c], '( ( %s - %s ) + %s ) = %s' % (G_, g1, g1, G_))], '( %s + ( ( %s - %s ) + %s ) ) = ( %s + %s )' % (dX, G_, g1, g1, dX, G_))])
    id2 = chain(w, As, ['( %s x. ( ( %s + ( 1 x. %s ) ) + ( 1 / %s ) ) )' % (d, X, Q2, d), '( ( %s x. ( %s + ( 1 x. %s ) ) ) + ( %s x. ( 1 / %s ) ) )' % (d, X, Q2, d, d),
                        '( ( %s x. ( %s + ( 1 x. %s ) ) ) + 1 )' % (d, X, Q2), '( ( %s + ( %s - 1 ) ) + 1 )' % (dX, G_), '( %s + ( ( %s - 1 ) + 1 ) )' % (dX, G_), '( %s + %s )' % (dX, G_)],
                [D(w, As, 'adddid', [dc, D(w, As, 'addcld', [xc, D(w, As, 'mulcld', [cst(w, As, 'ax-1cn', '1 e. CC'), q2c], '( 1 x. %s ) e. CC' % Q2)], '( %s + ( 1 x. %s ) ) e. CC' % (X, Q2)),
                                     D(w, As, 'reccld', [dc, dne], '( 1 / %s ) e. CC' % d)], '( %s x. ( ( %s + ( 1 x. %s ) ) + ( 1 / %s ) ) ) = ( ( %s x. ( %s + ( 1 x. %s ) ) ) + ( %s x. ( 1 / %s ) ) )' % (d, X, Q2, d, d, X, Q2, d, d)),
                 D(w, As, 'oveq2d', [D(w, As, 'recidd', [dc, dne], '( %s x. ( 1 / %s ) ) = 1' % (d, d))], '( ( %s x. ( %s + ( 1 x. %s ) ) ) + ( %s x. ( 1 / %s ) ) ) = ( ( %s x. ( %s + ( 1 x. %s ) ) ) + 1 )' % (d, X, Q2, d, d, d, X, Q2)),
                 D(w, As, 'oveq1d', [D(w, As, 'eqtrd', [D(w, As, 'adddid', [dc, xc, D(w, As, 'mulcld', [cst(w, As, 'ax-1cn', '1 e. CC'), q2c], '( 1 x. %s ) e. CC' % Q2)], '( %s x. ( %s + ( 1 x. %s ) ) ) = ( %s + ( %s x. ( 1 x. %s ) ) )' % (d, X, Q2, dX, d, Q2)),
                                                        D(w, As, 'oveq2d', [D(w, As, 'eqtrd', [D(w, As, 'oveq2d', [D(w, As, 'mullidd', [q2c], '( 1 x. %s ) = %s' % (Q2, Q2))], '( %s x. ( 1 x. %s ) ) = ( %s x. %s )' % (d, Q2, d, Q2)),
                                                                                               D(w, As, 'divcan2d', [D(w, As, 'subcld', [gc, cst(w, As, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % G_), dc, dne], '( %s x. %s ) = ( %s - 1 )' % (d, Q2, G_))],
                                                                                 '( %s x. ( 1 x. %s ) ) = ( %s - 1 )' % (d, Q2, G_))], '( %s + ( %s x. ( 1 x. %s ) ) ) = ( %s + ( %s - 1 ) )' % (dX, d, Q2, dX, G_))],
                                       '( %s x. ( %s + ( 1 x. %s ) ) ) = ( %s + ( %s - 1 ) )' % (d, X, Q2, dX, G_))], '( ( %s x. ( %s + ( 1 x. %s ) ) ) + 1 ) = ( ( %s + ( %s - 1 ) ) + 1 )' % (d, X, Q2, dX, G_)),
                 D(w, As, 'addassd', [dxc, D(w, As, 'subcld', [gc, cst(w, As, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % G_), cst(w, As, 'ax-1cn', '1 e. CC')], '( ( %s + ( %s - 1 ) ) + 1 ) = ( %s + ( ( %s - 1 ) + 1 ) )' % (dX, G_, dX, G_)),
                 D(w, As, 'oveq2d', [D(w, As, 'npcand', [gc, cst(w, As, 'ax-1cn', '1 e. CC')], '( ( %s - 1 ) + 1 ) = %s' % (G_, G_))], '( %s + ( ( %s - 1 ) + 1 ) ) = ( %s + %s )' % (dX, G_, dX, G_))])
    PTW = '( ( %s x. ( %s ` s ) ) + %s )' % (d, FC, g1)
    pt = chain(w, As, ['( %s ` s )' % E_, '( %s x. %s )' % (d, LSV), '( %s x. ( %s x. %s ) )' % (d, LAM, G_), '( %s x. %s )' % (d, FALL),
                       '( %s x. ( ( %s + ( 1 x. %s ) ) + ( 1 / %s ) ) )' % (d, X, Q2, d), '( %s + %s )' % (dX, G_), '( ( %s x. ( %s + ( 1 x. %s ) ) ) + %s )' % (d, X, Q1, g1), PTW],
               [es, D(w, As, 'oveq2d', [lsl], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (d, LSV, d, LAM, G_)),
                ('r', D(w, As, 'oveq2d', [fal], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (d, FALL, d, LAM, G_))),
                D(w, As, 'oveq2d', [falr], '( %s x. %s ) = ( %s x. ( ( %s + ( 1 x. %s ) ) + ( 1 / %s ) ) )' % (d, FALL, d, X, Q2, d)),
                id2, ('r', id1),
                ('r', D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [fvr], '( %s x. ( %s ` s ) ) = ( %s x. ( %s + ( 1 x. %s ) ) )' % (d, FC, d, X, Q1))], '%s = ( ( %s x. ( %s + ( 1 x. %s ) ) ) + %s )' % (PTW, d, X, Q1, g1)))])
    COND = lambda v: '( 1 < ( Re ` %s ) /\\ ( %s e. %s /\\ %s e. %s ) )' % (v, v, UO, v, HP0)
    EQ = lambda v: '( %s ` %s ) = ( ( ( %s - 1 ) x. ( %s ` %s ) ) + %s )' % (E_, v, v, FC, v, g1)
    ral = D(w, A, 'ralrimiva', [D(w, As0, 'ex', [pt], '( %s -> %s )' % (COND('s'), EQ('s')))], 'A. s e. CC ( %s -> %s )' % (COND('s'), EQ('s')))
    X_ = s_j = Sb('j')
    ph = 's = %s' % X_
    c1 = w.s([w.s([w.s([], 'fveq2', '( %s -> ( Re ` s ) = ( Re ` %s ) )' % (ph, X_))], 'breq2d', '( %s -> ( 1 < ( Re ` s ) <-> 1 < ( Re ` %s ) ) )' % (ph, X_)),
              w.s([w.s([], 'eleq1', '( %s -> ( s e. %s <-> %s e. %s ) )' % (ph, UO, X_, UO)), w.s([], 'eleq1', '( %s -> ( s e. %s <-> %s e. %s ) )' % (ph, HP0, X_, HP0))], 'anbi12d',
                  '( %s -> ( ( s e. %s /\\ s e. %s ) <-> ( %s e. %s /\\ %s e. %s ) ) )' % (ph, UO, HP0, X_, UO, X_, HP0))], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ph, COND('s'), COND(X_)))
    c2 = w.s([w.s([], 'fveq2', '( %s -> ( %s ` s ) = ( %s ` %s ) )' % (ph, E_, E_, X_)),
              w.s([w.s([w.s([], 'oveq1', '( %s -> ( s - 1 ) = ( %s - 1 ) )' % (ph, X_)), w.s([], 'fveq2', '( %s -> ( %s ` s ) = ( %s ` %s ) )' % (ph, FC, FC, X_))], 'oveq12d',
                       '( %s -> ( ( s - 1 ) x. ( %s ` s ) ) = ( ( %s - 1 ) x. ( %s ` %s ) ) )' % (ph, FC, X_, FC, X_))], 'oveq1d',
                  '( %s -> ( ( ( s - 1 ) x. ( %s ` s ) ) + %s ) = ( ( ( %s - 1 ) x. ( %s ` %s ) ) + %s ) )' % (ph, FC, g1, X_, FC, X_, g1))], 'eqeq12d', '( %s -> ( %s <-> %s ) )' % (ph, EQ('s'), EQ(X_)))
    sub = w.s([c1, c2], 'imbi12d', '( %s -> ( ( %s -> %s ) <-> ( %s -> %s ) ) )' % (ph, COND('s'), EQ('s'), COND(X_), EQ(X_)))
    inst = D(w, Aj, 'mpd', [D(w, Aj, '3jca' if False else 'jca', [rs1 if False else D(w, Aj, 'breqtrrd', [s1, rs], '1 < ( Re ` %s )' % X_), D(w, Aj, 'jca', [sU, sH], '( %s e. %s /\\ %s e. %s )' % (X_, UO, X_, HP0))], COND(X_)),
                            D(w, Aj, 'mpd', [ad(w, Aj, ral, 'A. s e. CC ( %s -> %s )' % (COND('s'), EQ('s'))), D(w, Aj, 'syl', [sc, w.s([sub], 'rspcv', '( %s e. CC -> ( A. s e. CC ( %s -> %s ) -> ( %s -> %s ) ) )' % (X_, COND('s'), EQ('s'), COND(X_), EQ(X_)))],
                                                                                                                    '( A. s e. CC ( %s -> %s ) -> ( %s -> %s ) )' % (COND('s'), EQ('s'), COND(X_), EQ(X_)))], '( %s -> %s )' % (COND(X_), EQ(X_)))], EQ(X_))
    # the sequences
    FS, ES = '( %s o. %s )' % (FC, S), '( %s o. %s )' % (E_, S)
    fsv = D(w, Aj, 'eqtrd', [D(w, Aj, 'syl2anc', [ad(w, Aj, SU, '%s : NN --> %s' % (S, UO)), jn, w.inst('fvco3')], '( %s ` j ) = ( %s ` ( %s ` j ) )' % (FS, FC, S)),
                             D(w, Aj, 'fveq2d', [sv], '( %s ` ( %s ` j ) ) = ( %s ` %s )' % (FC, S, FC, X_))], '( %s ` j ) = ( %s ` %s )' % (FS, FC, X_))
    esv = D(w, Aj, 'eqtrd', [D(w, Aj, 'syl2anc', [ad(w, Aj, SH, '%s : NN --> %s' % (S, HP0)), jn, w.inst('fvco3')], '( %s ` j ) = ( %s ` ( %s ` j ) )' % (ES, E_, S)),
                             D(w, Aj, 'fveq2d', [sv], '( %s ` ( %s ` j ) ) = ( %s ` %s )' % (E_, S, E_, X_))], '( %s ` j ) = ( %s ` %s )' % (ES, E_, X_))
    P1b = lambda q: '( ( 1 / %s ) x. ( %s ` %s ) )' % (q, FS, q)
    P1 = '( q e. NN |-> %s )' % P1b('q')
    Kb = lambda q: '( %s + %s )' % (P1b(q), g1)
    K = '( q e. NN |-> %s )' % Kb('q')
    p1sub = w.s([w.s([], 'oveq2', '( q = j -> ( 1 / q ) = ( 1 / j ) )'), w.s([], 'fveq2', '( q = j -> ( %s ` q ) = ( %s ` j ) )' % (FS, FS))], 'oveq12d', '( q = j -> %s = %s )' % (P1b('q'), P1b('j')))
    ksub = w.s([p1sub], 'oveq1d', '( q = j -> %s = %s )' % (Kb('q'), Kb('j')))
    p1v = D(w, Aj, 'syl', [jn, w.s([p1sub, w.s([], 'eqid', '%s = %s' % (P1, P1)), w.s([], 'ovex', '%s e. _V' % P1b('j'))], 'fvmpt', '( j e. NN -> ( %s ` j ) = %s )' % (P1, P1b('j')))], '( %s ` j ) = %s' % (P1, P1b('j')))
    kv = D(w, Aj, 'syl', [jn, w.s([ksub, w.s([], 'eqid', '%s = %s' % (K, K)), w.s([], 'ovex', '%s e. _V' % Kb('j'))], 'fvmpt', '( j e. NN -> ( %s ` j ) = %s )' % (K, Kb('j')))], '( %s ` j ) = %s' % (K, Kb('j')))
    fcf = D(w, A, 'syl', [fcn, w.inst('cncff')], '%s : %s --> CC' % (FC, UO))
    fsc = D(w, Aj, 'eqeltrd', [fsv, D(w, Aj, 'ffvelcdmd', [ad(w, Aj, fcf, '%s : %s --> CC' % (FC, UO)), sU], '( %s ` %s ) e. CC' % (FC, X_))], '( %s ` j ) e. CC' % FS)
    r1c = D(w, Aj, 'eqeltrd', [r1v, D(w, Aj, 'rpcnd', [ijp], '%s e. CC' % ij)], '( %s ` j ) e. CC' % R1)
    cP1 = D(w, A, 'climmul', [nnz, one, lim0, D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % P1), cF, r1c, fsc,
                              D(w, Aj, 'eqtr4d', [p1v, D(w, Aj, 'oveq1d', [r1v], '( ( %s ` j ) x. ( %s ` j ) ) = %s' % (R1, FS, P1b('j')))], '( %s ` j ) = ( ( %s ` j ) x. ( %s ` j ) )' % (P1, R1, FS))],
           '%s ~~> ( 0 x. ( %s ` 1 ) )' % (P1, FC))
    fs1c = D(w, A, 'ffvelcdmd', [fcf, oneU], '( %s ` 1 ) e. CC' % FC)
    g1cA = D(w, A, 'eqeltrrd', [fv1(w, A, 'x', UO, lambda q: LE.GV(q, PAR), '1', oneU, 'ovex'),
                                D(w, A, 'ffvelcdmd', [D(w, A, 'syl', [D(w, A, 'simpld', [D(w, A, 'simprd', [D(w, A, 'syl', [B['mpa'], w.inst('zl3ghl')], LE.tsub(L.split_imp(SE['zl3ghl'])[1], {'P': PAR}))],
                                                                                                             HOL('( x e. %s |-> %s )' % (UO, LE.GV('x', PAR)), UO))], '( x e. %s |-> %s ) e. ( %s -cn-> CC )' % (UO, LE.GV('x', PAR), UO)),
                                                                        w.inst('cncff')], '( x e. %s |-> %s ) : %s --> CC' % (UO, LE.GV('x', PAR), UO)), oneU], '( ( x e. %s |-> %s ) ` 1 ) e. CC' % (UO, LE.GV('x', PAR)))],
                 '%s e. CC' % g1)
    p1c = D(w, Aj, 'eqeltrd', [p1v, D(w, Aj, 'mulcld', [D(w, Aj, 'rpcnd', [ijp], '%s e. CC' % ij), fsc], '%s e. CC' % P1b('j'))], '( %s ` j ) e. CC' % P1)
    cK = D(w, A, 'climaddc1', [nnz, one, cP1, g1cA, D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % K), p1c,
                               D(w, Aj, 'eqtr4d', [kv, D(w, Aj, 'oveq1d', [p1v], '( ( %s ` j ) + %s ) = %s' % (P1, g1, Kb('j')))], '( %s ` j ) = ( ( %s ` j ) + %s )' % (K, P1, g1))],
           '%s ~~> ( ( 0 x. ( %s ` 1 ) ) + %s )' % (K, FC, g1))
    ks = D(w, Aj, 'eqtrd', [kv, D(w, Aj, 'oveq1d', [D(w, Aj, 'oveq12d', [D(w, Aj, 'eqcomd', [D(w, Aj, 'pncand', [D(w, Aj, 'rpcnd', [ijp], '%s e. CC' % ij), cst(w, Aj, 'ax-1cn', '1 e. CC')], '( %s - 1 ) = %s' % (X_, ij))],
                                                                              '%s = ( %s - 1 )' % (ij, X_)), fsv], '%s = ( ( %s - 1 ) x. ( %s ` %s ) )' % (P1b('j'), X_, FC, X_))],
                                               '%s = ( ( ( %s - 1 ) x. ( %s ` %s ) ) + %s )' % (Kb('j'), X_, FC, X_, g1))], '( %s ` j ) = ( ( ( %s - 1 ) x. ( %s ` %s ) ) + %s )' % (K, X_, FC, X_, g1))
    keq = D(w, Aj, 'eqtr4d', [ks, D(w, Aj, 'eqtrd', [esv, inst], '( %s ` j ) = ( ( ( %s - 1 ) x. ( %s ` %s ) ) + %s )' % (ES, X_, FC, X_, g1))], '( %s ` j ) = ( %s ` j )' % (K, ES))
    ceq = D(w, A, 'climeq', [nnz, D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % K), D(w, A, 'coexd' if False else 'syl2anc', [D(w, A, 'elexd', [ecn], '%s e. _V' % E_) if False else w.s([ecn, w.inst('elexd' if False else 'elex')], 'syl', '( %s -> %s e. _V )' % (A, E_)),
                                                                                                                                             D(w, A, 'mptexd', [cst(w, A, 'nnex', 'NN e. _V')], '%s e. _V' % S), w.inst('coexg')], '%s e. _V' % ES),
                             one, keq], '( %s ~~> ( %s ` 1 ) <-> %s ~~> ( %s ` 1 ) )' % (K, E_, ES, E_))
    cKE = D(w, A, 'mpbird', [cE, ceq], '%s ~~> ( %s ` 1 )' % (K, E_))
    uni = D(w, A, 'syl2anc' if False else 'climuni' if False else 'syl2anc', [cK, cKE, w.inst('climuni')], '( ( 0 x. ( %s ` 1 ) ) + %s ) = ( %s ` 1 )' % (FC, g1, E_))
    lhs = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [D(w, A, 'mul02d', [fs1c], '( 0 x. ( %s ` 1 ) ) = 0' % FC)], '( ( 0 x. ( %s ` 1 ) ) + %s ) = ( 0 + %s )' % (FC, g1, g1)), D(w, A, 'addlidd', [g1cA], '( 0 + %s ) = %s' % (g1, g1))],
            '( ( 0 x. ( %s ` 1 ) ) + %s ) = %s' % (FC, g1, g1))
    # E ( 1 ) = 1
    PRN = '( n e. NN |-> if ( ( n gcd M ) = 1 , 1 , 0 ) )'
    e1 = D(w, A, 'syl', [ch, w.inst('zl1e1')], '( %s ` 1 ) = if ( %s = %s , ( ( phi ` M ) / M ) , 0 )' % (E_, CYM, PRN))
    y0 = D(w, A, 'mpbird', [D(w, A, 'eqtrd', [D(w, A, 'simprd', [pr], '( M DChrCond Y ) = M'), m1], '( M DChrCond Y ) = 1'), D(w, A, 'syl', [ch, w.inst('dchrcondeq1')], '( Y = ( 0g ` ( DChr ` M ) ) <-> ( M DChrCond Y ) = 1 )')],
            'Y = ( 0g ` ( DChr ` M ) )')
    cprn = D(w, A, 'mpbird', [y0, D(w, A, 'syl', [ch, w.inst('zl1prn')], '( %s = %s <-> Y = ( 0g ` ( DChr ` M ) ) )' % (CYM, PRN))], '%s = %s' % (CYM, PRN))
    e1v = chain(w, A, ['( %s ` 1 )' % E_, 'if ( %s = %s , ( ( phi ` M ) / M ) , 0 )' % (CYM, PRN), '( ( phi ` M ) / M )', '( ( phi ` 1 ) / 1 )', '1'],
                [e1, D(w, A, 'iftrued', [cprn], 'if ( %s = %s , ( ( phi ` M ) / M ) , 0 ) = ( ( phi ` M ) / M )' % (CYM, PRN)),
                 D(w, A, 'oveq12d', [D(w, A, 'fveq2d', [m1], '( phi ` M ) = ( phi ` 1 )'), m1], '( ( phi ` M ) / M ) = ( ( phi ` 1 ) / 1 )'),
                 cst(w, A, 'idi', '') if False else w.s([w.s([w.s([], 'phi1', '( phi ` 1 ) = 1')], 'oveq1i', '( ( phi ` 1 ) / 1 ) = ( 1 / 1 )'), w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'eqtri', '( ( phi ` 1 ) / 1 ) = 1') and
                 w.s([w.s([w.s([w.s([], 'phi1', '( phi ` 1 ) = 1')], 'oveq1i', '( ( phi ` 1 ) / 1 ) = ( 1 / 1 )'), w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'eqtri', '( ( phi ` 1 ) / 1 ) = 1')], 'a1i', '( %s -> ( ( phi ` 1 ) / 1 ) = 1 )' % A)])
    fin = D(w, A, 'eqtr3d', [lhs, D(w, A, 'eqtrd', [uni, e1v], '( ( 0 x. ( %s ` 1 ) ) + %s ) = 1' % (FC, g1))], '%s = 1' % g1)
    w.qed([fin], 'idi', SE['zl3g1'])
    goe(w)


def rm_facts(w, A):
    """closed-ish: ( A -> RM e. { 0 , 1 } ) and the step ( RM = 1 -> M = 1 )"""
    rpr = w.s([w.s([w.s([w.s([], '1ex', '1 e. _V')], 'prid2', '1 e. { 0 , 1 }'), w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }')], 'ifcli', '%s e. { 0 , 1 }' % RM)], 'a1i',
              '( %s -> %s e. { 0 , 1 } )' % (A, RM))
    h1 = w.s([], 'iffalse', '( -. M = 1 -> %s = 0 )' % RM)
    h2 = w.s([w.s([w.s([], 'eqeq1', '( %s = 0 -> ( %s = 1 <-> 0 = 1 ) )' % (RM, RM))], 'idi', '( %s = 0 -> ( %s = 1 <-> 0 = 1 ) )' % (RM, RM)),
              w.s([w.s([], '0ne1', '0 =/= 1')], 'neii', '-. 0 = 1')], 'mtbiri', '( %s = 0 -> -. %s = 1 )' % (RM, RM))
    h3 = w.s([w.s([h1, h2], 'syl', '( -. M = 1 -> -. %s = 1 )' % RM)], 'con4i', '( %s = 1 -> M = 1 )' % RM)
    return rpr, h3


def value_facts(w, As, s, s_c, s_U, B, L2):
    """complex values under As for a point s e. UO: L0 ( s ), h ( s ), g ( s ), g ( 1 )"""
    ghl = D(w, As, 'syl', [L2(B['mpa'], MPA), w.inst('zl3ghl')], LE.tsub(L.split_imp(SE['zl3ghl'])[1], {'P': PAR}))
    Hxm, Gxm = '( x e. %s |-> %s )' % (UO, LE.HV('x', PAR)), '( x e. %s |-> %s )' % (UO, LE.GV('x', PAR))
    hf = D(w, As, 'syl', [D(w, As, 'simpld', [D(w, As, 'simpld', [ghl], HOL(Hxm, UO))], '%s e. ( %s -cn-> CC )' % (Hxm, UO)), w.inst('cncff')], '%s : %s --> CC' % (Hxm, UO))
    gf = D(w, As, 'syl', [D(w, As, 'simpld', [D(w, As, 'simprd', [ghl], HOL(Gxm, UO))], '%s e. ( %s -cn-> CC )' % (Gxm, UO)), w.inst('cncff')], '%s : %s --> CC' % (Gxm, UO))
    G_, H_, g1 = LE.GV(s, PAR), LE.HV(s, PAR), LE.GV('1', PAR)
    hc = D(w, As, 'eqeltrrd', [fv1(w, As, 'x', UO, lambda q: LE.HV(q, PAR), s, s_U, 'ovex'), D(w, As, 'ffvelcdmd', [hf, s_U], '( %s ` %s ) e. CC' % (Hxm, s))], '%s e. CC' % H_)
    gc = D(w, As, 'eqeltrrd', [fv1(w, As, 'x', UO, lambda q: LE.GV(q, PAR), s, s_U, 'ovex'), D(w, As, 'ffvelcdmd', [gf, s_U], '( %s ` %s ) e. CC' % (Gxm, s))], '%s e. CC' % G_)
    one_u = uo_one(w, As)
    g1c = D(w, As, 'eqeltrrd', [fv1(w, As, 'x', UO, lambda q: LE.GV(q, PAR), '1', one_u, 'ovex'), D(w, As, 'ffvelcdmd', [gf, one_u], '( %s ` 1 ) e. CC' % Gxm)], '%s e. CC' % g1)

    def ilc(ta, TA_, C, X, xc):
        return D(w, As, 'eqeltrrd', [D(w, As, 'syl', [xc, w.s([il_sub(w, C, 'w', X), w.s([], 'eqid', '%s = %s' % (LE.MPW(C, PAR), LE.MPW(C, PAR))), w.s([], 'fvex', '%s e. _V' % LE.ILG(C, X, PAR))], 'fvmpt',
                                                               '( %s e. CC -> ( %s ` %s ) = %s )' % (X, LE.MPW(C, PAR), X, LE.ILG(C, X, PAR)))], '( %s ` %s ) = %s' % (LE.MPW(C, PAR), X, LE.ILG(C, X, PAR))),
                                     D(w, As, 'ffvelcdmd', [D(w, As, 'syl', [D(w, As, 'simpld', [D(w, As, 'syl', [L2(ta, TA_), w.inst('zl3ilh')], HOL(LE.MPW(C, PAR), 'CC'))], '%s e. ( CC -cn-> CC )' % LE.MPW(C, PAR)),
                                                                             w.inst('cncff')], '%s : CC --> CC' % LE.MPW(C, PAR)), xc], '( %s ` %s ) e. CC' % (LE.MPW(C, PAR), X))],
                 '%s e. CC' % LE.ILG(C, X, PAR))
    oms = '( 1 - %s )' % s
    omsc = D(w, As, 'subcld', [cst(w, As, 'ax-1cn', '1 e. CC'), s_c], '%s e. CC' % oms)
    i1c = ilc(B['taY'], B['TAY'], CYM, s, s_c); i2c = ilc(B['taB'], B['TAB'], CYBM, oms, omsc)
    ec = eps_cl(w, As, L2(B['ch'], '( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) )'), L2(B['pp'], '%s e. { 0 , 1 }' % PAR))
    l0c = D(w, As, 'addcld', [i1c, D(w, As, 'mulcld', [ec, i2c], '( %s x. %s ) e. CC' % (EPS, LE.ILG(CYBM, oms, PAR)))], '%s e. CC' % LE.L0(s))
    return dict(hc=hc, gc=gc, g1c=g1c, l0c=l0c, ec=ec, i1c=i1c, i2c=i2c, omsc=omsc)


def uo_one(w, A):
    return D(w, A, 'mpbird', [D(w, A, 'jca', [cst(w, A, 'ax-1cn', '1 e. CC'), D(w, A, 'jca', [D(w, A, 'breqtrrd', [D(w, A, 'lttrd', [cst(w, A, 'neg1rr', '-u 1 e. RR'), cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), cst(w, A, 'neg1lt0', '-u 1 < 0'), cst(w, A, '0lt1', '0 < 1')], '-u 1 < 1'),
                                                                                               cst(w, A, 're1', '( Re ` 1 ) = 1')], '-u 1 < ( Re ` 1 )'),
                                                                              D(w, A, 'eqbrtrd', [cst(w, A, 're1', '( Re ` 1 ) = 1'), cst(w, A, '1lt3', '1 < 3')], '( Re ` 1 ) < 3')], '( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 )')],
                                    '( 1 e. CC /\\ ( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 ) )'),
                          D(w, A, 'syl2anc', [D(w, A, 'rexrd', [cst(w, A, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, A, 'rexrd', [cst(w, A, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                            '( 1 e. %s <-> ( 1 e. CC /\\ ( -u 1 < ( Re ` 1 ) /\\ ( Re ` 1 ) < 3 ) ) )' % UO)], '1 e. %s' % UO)


def in_uo(w, Az, z, zc, lo, hi):
    """( Az -> z e. UO ) from ( Az -> -u 1 < Re z ), ( Az -> Re z < 3 )"""
    return D(w, Az, 'mpbird', [D(w, Az, 'jca', [zc, D(w, Az, 'jca', [lo, hi], '( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 )' % (z, z))], '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 ) )' % (z, z, z)),
                               D(w, Az, 'syl2anc', [D(w, Az, 'rexrd', [cst(w, Az, 'neg1rr', '-u 1 e. RR')], '-u 1 e. RR*'), D(w, Az, 'rexrd', [cst(w, Az, '3re', '3 e. RR')], '3 e. RR*'), w.inst('z6melst')],
                                 '( %s e. %s <-> ( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ ( Re ` %s ) < 3 ) ) )' % (z, UO, z, z, z))], '%s e. %s' % (z, UO))


def ne01(w, Az, z, rz_ne):
    """from ( Az -> ( Re ` z ) =/= c ) get ( Az -> z =/= c ) for c in 0, 1"""
    pass


def re_ne(w, Az, z, c, rne):
    """( Az -> z =/= c ) from ( Az -> ( Re ` z ) =/= c ), c e. { 0 , 1 }"""
    lab = {'0': 're0', '1': 're1'}[c]
    a = w.s([w.s([], 'fveq2', '( %s = %s -> ( Re ` %s ) = ( Re ` %s ) )' % (z, c, z, c)), w.s([], lab, '( Re ` %s ) = %s' % (c, c))], 'eqtrdi', '( %s = %s -> ( Re ` %s ) = %s )' % (z, c, z, c))
    return w.s([rne, w.s([a], 'necon3i', '( ( Re ` %s ) =/= %s -> %s =/= %s )' % (z, c, z, c))], 'syl', '( %s -> %s =/= %s )' % (Az, z, c))


# ---------------------------------------------------------------- zl3sery
if wante('zl3sery', MAIN):
    w = W('zl3sery', 'Part (ii) of PCONT: ` F ( z ) + R / ( z - 1 ) = L ( z , Y ) ` on ` 1 < Re z <_ 2 ` ( ~ zl3mel , ~ zl3gga , ~ zl3fal , ~ zl3g1 ).')
    A, Cc = ante_e('zl3sery')
    pr = D(w, A, 'simpl', [], PR); re_ = D(w, A, 'simpr', [], 'R = %s' % RM)
    B = pr_base(w, A, pr)
    As0 = '( %s /\\ s e. CC )' % A
    As = '( %s /\\ ( 1 < ( Re ` s ) /\\ ( Re ` s ) <_ 2 ) )' % As0
    L2 = lambda st, f: ad(w, As, ad(w, As0, st, f), f)
    s_c = D(w, As, 'simplr', [], 's e. CC'); s_1 = D(w, As, 'simprl', [], '1 < ( Re ` s )'); s_2 = D(w, As, 'simprr', [], '( Re ` s ) <_ 2')
    rsr = D(w, As, 'recld', [s_c], '( Re ` s ) e. RR')
    clS = Closure(w, As, {'( Re ` s )': ('RR', rsr)})
    s_U = in_uo(w, As, 's', s_c, linarith(w, As, [s_1], '-u 1 < ( Re ` s )', closure=clS), linarith(w, As, [s_2], '( Re ` s ) < 3', closure=clS))
    sne1 = re_ne(w, As, 's', '1', D(w, As, 'gtned', [s_1], '( Re ` s ) =/= 1'))
    sne0 = re_ne(w, As, 's', '0', D(w, As, 'gt0ne0d', [linarith(w, As, [s_1], '0 < ( Re ` s )', closure=clS)], '( Re ` s ) =/= 0'))
    prs = L2(pr, PR); res = L2(re_, 'R = %s' % RM)
    V = value_facts(w, As, 's', s_c, s_U, B, L2)
    G_, H_, g1 = LE.GV('s', PAR), LE.HV('s', PAR), LE.GV('1', PAR)
    LSV = LSs('s')
    MELs = '( 1 < ( Re ` s ) -> ( %s x. %s ) = ( %s - ( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) ) )' % (Z3G('s'), LSV, LE.L0('s'), RM)
    mel = w.s([w.s([], 'zl3mel', '( %s -> A. s e. CC %s )' % (PR, MELs))], 'r19.21bi', '( ( %s /\\ s e. CC ) -> %s )' % (PR, MELs))
    mels = D(w, As, 'mpd', [s_1, D(w, As, 'syl', [D(w, As, 'jca', [prs, s_c], '( %s /\\ s e. CC )' % PR), mel], MELs)], MELs[MELs.index(' -> ') + 4:-2])
    ppS = L2(B['pp'], '%s e. { 0 , 1 }' % PAR)
    pn_, prr, p00, p11 = p01(w, As, ppS, PAR)
    pcc = D(w, As, 'recnd', [prr], '%s e. CC' % PAR)
    spc, reW, imW = reim_w(w, As, 's', s_c, pcc, prr, P=PAR)
    clS.have(PAR, 'RR', prr); clS.have(PAR, 'ge0', p00)
    w0 = D(w, As, 'breqtrrd', [linarith(w, As, [s_1, p00], '0 < ( ( ( Re ` s ) + %s ) / 2 )' % PAR, closure=clS), reW], '0 < ( Re ` %s )' % LE.WV('s', PAR))
    gga = D(w, As, 'syl2anc', [L2(B['mpa'], MPA), D(w, As, 'jca', [s_c, w0], '( s e. CC /\\ 0 < ( Re ` %s ) )' % LE.WV('s', PAR)), w.inst('zl3gga')], '( %s x. %s ) = 1' % (G_, Z3G('s')))
    chs = L2(B['ch'], '( M e. NN /\\ Y e. ( Base ` ( DChr ` M ) ) )')
    chsZ = LE.tsub(L.split_imp(Z2S['zl2chs'])[1], {'N': 'M', 'X': 'Y', 'Z': 's'})
    lsc = D(w, As, 'simpld', [D(w, As, 'syl2anc', [chs, D(w, As, 'jca', [s_c, s_1], '( s e. CC /\\ 1 < ( Re ` s ) )'), w.inst('zl2chs')], chsZ)], '%s e. CC' % LSV)
    Wsp = LE.WV('s', PAR)
    wdm = D(w, As, 'syl2anc', [D(w, As, 'halfcld', [spc], '%s e. CC' % Wsp), w0, w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % Wsp)
    clM = Closure(w, As, {'M': ('NN', L2(B['mn'], 'M e. NN')), '_pi': ('RR+', cst(w, As, 'pirp', '_pi e. RR+'))})
    gfc = D(w, As, 'mulcld', [D(w, As, 'cxpcld', [clM.mem('( M / _pi )', 'CC'), D(w, As, 'halfcld', [spc], '%s e. CC' % Wsp)], '( ( M / _pi ) ^c %s ) e. CC' % Wsp),
                              D(w, As, 'syl', [wdm, w.inst('gamcl')], '( _G ` %s ) e. CC' % Wsp)], '%s e. CC' % Z3G('s'))
    LAMr = lambda r: '( %s - ( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) )' % (LE.L0('s'), r)
    rmc = L2(rm_cc(w, A), '%s e. CC' % RM)
    ssum = D(w, As, 'addcld', [D(w, As, 'reccld', [s_c, sne0], '( 1 / s ) e. CC'), D(w, As, 'reccld', [V['omsc'], D(w, As, 'subne0d', [cst(w, As, 'ax-1cn', '1 e. CC'), s_c, D(w, As, 'necomd', [sne1], '1 =/= s')], '( 1 - s ) =/= 0')],
                                                                                   '( 1 / ( 1 - s ) ) e. CC')], '( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) e. CC')
    lamc = D(w, As, 'subcld', [V['l0c'], D(w, As, 'mulcld', [rmc, ssum], '( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) e. CC' % RM)], '%s e. CC' % LAMr(RM))
    lsl = chain(w, As, [LSV, '( 1 x. %s )' % LSV, '( ( %s x. %s ) x. %s )' % (G_, Z3G('s'), LSV), '( %s x. ( %s x. %s ) )' % (G_, Z3G('s'), LSV), '( %s x. %s )' % (G_, LAMr(RM)), '( %s x. %s )' % (LAMr(RM), G_)],
                [('r', D(w, As, 'mullidd', [lsc], '( 1 x. %s ) = %s' % (LSV, LSV))),
                 ('r', D(w, As, 'oveq1d', [gga], '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (G_, Z3G('s'), LSV, LSV))),
                 D(w, As, 'mulassd', [V['gc'], gfc, lsc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (G_, Z3G('s'), LSV, G_, Z3G('s'), LSV)),
                 D(w, As, 'oveq2d', [mels], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (G_, Z3G('s'), LSV, G_, LAMr(RM))),
                 D(w, As, 'mulcomd', [V['gc'], lamc], '( %s x. %s ) = ( %s x. %s )' % (G_, LAMr(RM), LAMr(RM), G_))])
    # zl3fal at R
    rpr, rm_m1 = rm_facts(w, As)
    rin = D(w, As, 'eqeltrd', [res, rpr], 'R e. { 0 , 1 }')
    Ar = '( %s /\\ R = 1 )' % As
    rmone = D(w, Ar, 'eqtr3d', [ad(w, Ar, res, 'R = %s' % RM), w.s([], 'simpr', '( %s -> R = 1 )' % Ar)], '%s = 1' % RM)
    mone = D(w, Ar, 'syl', [rmone, rm_m1], 'M = 1')
    prm = D(w, Ar, 'jca', [ad(w, Ar, prs, PR), mone], '( %s /\\ M = 1 )' % PR)
    p0 = D(w, Ar, 'simpld', [D(w, Ar, 'syl', [prm, w.inst('zl3m1')], '( %s = 0 /\\ %s = 1 )' % (PAR, EPS))], '%s = 0' % PAR)
    sc_r = ad(w, Ar, s_c, 's e. CC')
    gsh = D(w, Ar, 'oveq1d', [D(w, Ar, 'eqtrd', [D(w, Ar, 'oveq1d', [D(w, Ar, 'oveq2d', [p0], '( s + %s ) = ( s + 0 )' % PAR)], '( ( s + %s ) / 2 ) = ( ( s + 0 ) / 2 )' % PAR),
                                                  D(w, Ar, 'oveq1d', [D(w, Ar, 'addridd', [sc_r], '( s + 0 ) = s')], '( ( s + 0 ) / 2 ) = ( s / 2 )')], '( ( s + %s ) / 2 ) = ( s / 2 )' % PAR)],
            '%s = ( ( s / 2 ) x. %s )' % (G_, H_))
    g1e = D(w, Ar, 'syl', [prm, w.inst('zl3g1')], '%s = 1' % g1)
    cond = D(w, As, 'ex', [D(w, Ar, 'jca', [gsh, g1e], '( %s = ( ( s / 2 ) x. %s ) /\\ %s = 1 )' % (G_, H_, g1))], '( R = 1 -> ( %s = ( ( s / 2 ) x. %s ) /\\ %s = 1 ) )' % (G_, H_, g1))
    FALA = LE.tsub(L.split_imp(SE['zl3fal'])[0], {'L': LE.L0('s'), 'H': H_, 'G': G_, 'Z': 's', 'B': g1})
    fal_h = D(w, As, '3jca', [D(w, As, 'jca', [D(w, As, 'jca', [V['l0c'], V['hc']], '( %s e. CC /\\ %s e. CC )' % (LE.L0('s'), H_)), D(w, As, 'jca', [V['gc'], V['g1c']], '( %s e. CC /\\ %s e. CC )' % (G_, g1))],
                                               '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) )' % (LE.L0('s'), H_, G_, g1)),
                              D(w, As, '3jca', [s_c, sne0, sne1], '( s e. CC /\\ s =/= 0 /\\ s =/= 1 )'),
                              D(w, As, 'jca', [rin, cond], '( R e. { 0 , 1 } /\\ ( R = 1 -> ( %s = ( ( s / 2 ) x. %s ) /\\ %s = 1 ) ) )' % (G_, H_, g1))], FALA)
    FVR = '( ( ( %s x. %s ) - ( R x. ( %s / 2 ) ) ) + ( R x. ( ( %s - %s ) / ( s - 1 ) ) ) )' % (LE.L0('s'), G_, H_, G_, g1)
    FALL = '( %s + ( R / ( s - 1 ) ) )' % FVR
    fal = D(w, As, 'syl', [fal_h, w.inst('zl3fal')], '%s = ( %s x. %s )' % (FALL, LAMr('R'), G_))
    fcv = D(w, As, 'syl2anc', [prs, D(w, As, 'jca', [s_U, sne1], '( s e. %s /\\ s =/= 1 )' % UO), w.inst('zl3fcv')], '( %s ` s ) = %s' % (FC, LE.FV('s')))
    rme = D(w, As, 'eqcomd', [res], '%s = R' % RM)
    fvr = D(w, As, 'eqtrd', [fcv, D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [rme], '( %s x. ( %s / 2 ) ) = ( R x. ( %s / 2 ) )' % (RM, H_, H_))],
                                                                  '( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) = ( ( %s x. %s ) - ( R x. ( %s / 2 ) ) )' % (LE.L0('s'), G_, RM, H_, LE.L0('s'), G_, H_)),
                                                        D(w, As, 'oveq1d', [rme], '( %s x. ( ( %s - %s ) / ( s - 1 ) ) ) = ( R x. ( ( %s - %s ) / ( s - 1 ) ) )' % (RM, G_, g1, G_, g1))],
                                          '%s = %s' % (LE.FV('s'), FVR))], '( %s ` s ) = %s' % (FC, FVR))
    lam_e = D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [rme], '( %s x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) ) = ( R x. ( ( 1 / s ) + ( 1 / ( 1 - s ) ) ) )' % RM)], '%s = %s' % (LAMr(RM), LAMr('R')))],
              '( %s x. %s ) = ( %s x. %s )' % (LAMr(RM), G_, LAMr('R'), G_))
    body = lambda v: '( ( %s ` %s ) + ( R / ( %s - 1 ) ) )' % (FC, v, v)
    pt = chain(w, As, [body('s'), FALL, '( %s x. %s )' % (LAMr('R'), G_), '( %s x. %s )' % (LAMr(RM), G_), LSV],
               [D(w, As, 'oveq1d', [fvr], '%s = %s' % (body('s'), FALL)), fal, ('r', lam_e), ('r', lsl)])
    COND = lambda v: '( 1 < ( Re ` %s ) /\\ ( Re ` %s ) <_ 2 )' % (v, v)
    ral = D(w, A, 'ralrimiva', [D(w, As0, 'ex', [pt], '( %s -> %s = %s )' % (COND('s'), body('s'), LSV))], 'A. s e. CC ( %s -> %s = %s )' % (COND('s'), body('s'), LSV))
    ph = 's = z'
    c1 = w.s([w.s([w.s([], 'fveq2', '( %s -> ( Re ` s ) = ( Re ` z ) )' % ph)], 'breq2d', '( %s -> ( 1 < ( Re ` s ) <-> 1 < ( Re ` z ) ) )' % ph),
              w.s([w.s([], 'fveq2', '( %s -> ( Re ` s ) = ( Re ` z ) )' % ph)], 'breq1d', '( %s -> ( ( Re ` s ) <_ 2 <-> ( Re ` z ) <_ 2 ) )' % ph)], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ph, COND('s'), COND('z')))
    c2 = w.s([w.s([w.s([], 'fveq2', '( %s -> ( %s ` s ) = ( %s ` z ) )' % (ph, FC, FC)), w.s([w.s([], 'oveq1', '( %s -> ( s - 1 ) = ( z - 1 ) )' % ph)], 'oveq2d', '( %s -> ( R / ( s - 1 ) ) = ( R / ( z - 1 ) ) )' % ph)],
                  'oveq12d', '( %s -> %s = %s )' % (ph, body('s'), body('z'))), vsub(w, LSs, 's', 'z')], 'eqeq12d', '( %s -> ( %s = %s <-> %s = %s ) )' % (ph, body('s'), LSV, body('z'), LSs('z')))
    cb = w.s([w.s([c1, c2], 'imbi12d', '( %s -> ( ( %s -> %s = %s ) <-> ( %s -> %s = %s ) ) )' % (ph, COND('s'), body('s'), LSV, COND('z'), body('z'), LSs('z')))], 'cbvralvw',
             '( A. s e. CC ( %s -> %s = %s ) <-> A. z e. CC ( %s -> %s = %s ) )' % (COND('s'), body('s'), LSV, COND('z'), body('z'), LSs('z')))
    w.qed([D(w, A, 'mpbid', [ral, w.s([cb], 'a1i', '( %s -> ( A. s e. CC ( %s -> %s = %s ) <-> A. z e. CC ( %s -> %s = %s ) ) )' % (A, COND('s'), body('s'), LSV, COND('z'), body('z'), LSs('z')))], Cc)],
          'idi', SE['zl3sery'])
    goe(w)


# ---------------------------------------------------------------- zl3fey
if wante('zl3fey', MAIN):
    w = W('zl3fey', 'Part (iv) of PCONT, the functional equation: on ` -1/2 <_ Re z < 0 ` , ` F ( z ) + R / ( z - 1 ) = M ^ ( 1/2 - z ) EPS QQ ( a ) ( z ) L ( 1 - z , YB ) ` ( ~ zl3mlb at ` 1 - z ` , ~ zl3yb , ~ zl3gfr ).')
    A, Cc = ante_e('zl3fey')
    pr = D(w, A, 'simpl', [], PR); re_ = D(w, A, 'simpr', [], 'R = %s' % RM)
    B = pr_base(w, A, pr)
    o = 'o'
    As0 = '( %s /\\ o e. CC )' % A
    As = '( %s /\\ ( -u ( 1 / 2 ) <_ ( Re ` o ) /\\ ( Re ` o ) < 0 ) )' % As0
    L2 = lambda st, f: ad(w, As, ad(w, As0, st, f), f)
    s_c = D(w, As, 'simplr', [], 'o e. CC'); s_lo = D(w, As, 'simprl', [], '-u ( 1 / 2 ) <_ ( Re ` o )'); s_hi = D(w, As, 'simprr', [], '( Re ` o ) < 0')
    rsr = D(w, As, 'recld', [s_c], '( Re ` o ) e. RR')
    clS = Closure(w, As, {'( Re ` o )': ('RR', rsr)})
    s_U = in_uo(w, As, 'o', s_c, linarith(w, As, [s_lo], '-u 1 < ( Re ` o )', closure=clS), linarith(w, As, [s_hi], '( Re ` o ) < 3', closure=clS))
    sne1 = re_ne(w, As, 'o', '1', D(w, As, 'ltned', [linarith(w, As, [s_hi], '( Re ` o ) < 1', closure=clS)], '( Re ` o ) =/= 1'))
    sne0 = re_ne(w, As, 'o', '0', D(w, As, 'ltned', [s_hi], '( Re ` o ) =/= 0'))
    prs = L2(pr, PR); res = L2(re_, 'R = %s' % RM)
    V = value_facts(w, As, 'o', s_c, s_U, B, L2)
    G_, H_, g1 = LE.GV('o', PAR), LE.HV('o', PAR), LE.GV('1', PAR)
    ppS = L2(B['pp'], '%s e. { 0 , 1 }' % PAR)
    # zl3fal at R
    rpr, rm_m1 = rm_facts(w, As)
    rin = D(w, As, 'eqeltrd', [res, rpr], 'R e. { 0 , 1 }')
    Ar = '( %s /\\ R = 1 )' % As
    rmone = D(w, Ar, 'eqtr3d', [ad(w, Ar, res, 'R = %s' % RM), w.s([], 'simpr', '( %s -> R = 1 )' % Ar)], '%s = 1' % RM)
    mone = D(w, Ar, 'syl', [rmone, rm_m1], 'M = 1')
    prm = D(w, Ar, 'jca', [ad(w, Ar, prs, PR), mone], '( %s /\\ M = 1 )' % PR)
    p0 = D(w, Ar, 'simpld', [D(w, Ar, 'syl', [prm, w.inst('zl3m1')], '( %s = 0 /\\ %s = 1 )' % (PAR, EPS))], '%s = 0' % PAR)
    sc_r = ad(w, Ar, s_c, 'o e. CC')
    gsh = D(w, Ar, 'oveq1d', [D(w, Ar, 'eqtrd', [D(w, Ar, 'oveq1d', [D(w, Ar, 'oveq2d', [p0], '( o + %s ) = ( o + 0 )' % PAR)], '( ( o + %s ) / 2 ) = ( ( o + 0 ) / 2 )' % PAR),
                                                  D(w, Ar, 'oveq1d', [D(w, Ar, 'addridd', [sc_r], '( o + 0 ) = o')], '( ( o + 0 ) / 2 ) = ( o / 2 )')], '( ( o + %s ) / 2 ) = ( o / 2 )' % PAR)],
            '%s = ( ( o / 2 ) x. %s )' % (G_, H_))
    g1e = D(w, Ar, 'syl', [prm, w.inst('zl3g1')], '%s = 1' % g1)
    cond = D(w, As, 'ex', [D(w, Ar, 'jca', [gsh, g1e], '( %s = ( ( o / 2 ) x. %s ) /\\ %s = 1 )' % (G_, H_, g1))], '( R = 1 -> ( %s = ( ( o / 2 ) x. %s ) /\\ %s = 1 ) )' % (G_, H_, g1))
    FALA = LE.tsub(L.split_imp(SE['zl3fal'])[0], {'L': LE.L0('o'), 'H': H_, 'G': G_, 'Z': 'o', 'B': g1})
    fal_h = D(w, As, '3jca', [D(w, As, 'jca', [D(w, As, 'jca', [V['l0c'], V['hc']], '( %s e. CC /\\ %s e. CC )' % (LE.L0('o'), H_)), D(w, As, 'jca', [V['gc'], V['g1c']], '( %s e. CC /\\ %s e. CC )' % (G_, g1))],
                                               '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) )' % (LE.L0('o'), H_, G_, g1)),
                              D(w, As, '3jca', [s_c, sne0, sne1], '( o e. CC /\\ o =/= 0 /\\ o =/= 1 )'),
                              D(w, As, 'jca', [rin, cond], '( R e. { 0 , 1 } /\\ ( R = 1 -> ( %s = ( ( o / 2 ) x. %s ) /\\ %s = 1 ) ) )' % (G_, H_, g1))], FALA)
    LAMr = lambda r: '( %s - ( %s x. ( ( 1 / o ) + ( 1 / ( 1 - o ) ) ) ) )' % (LE.L0('o'), r)
    FVR = '( ( ( %s x. %s ) - ( R x. ( %s / 2 ) ) ) + ( R x. ( ( %s - %s ) / ( o - 1 ) ) ) )' % (LE.L0('o'), G_, H_, G_, g1)
    FALL = '( %s + ( R / ( o - 1 ) ) )' % FVR
    fal = D(w, As, 'syl', [fal_h, w.inst('zl3fal')], '%s = ( %s x. %s )' % (FALL, LAMr('R'), G_))
    fcv = D(w, As, 'syl2anc', [prs, D(w, As, 'jca', [s_U, sne1], '( o e. %s /\\ o =/= 1 )' % UO), w.inst('zl3fcv')], '( %s ` o ) = %s' % (FC, LE.FV('o')))
    rme = D(w, As, 'eqcomd', [res], '%s = R' % RM)
    fvr = D(w, As, 'eqtrd', [fcv, D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [rme], '( %s x. ( %s / 2 ) ) = ( R x. ( %s / 2 ) )' % (RM, H_, H_))],
                                                                  '( ( %s x. %s ) - ( %s x. ( %s / 2 ) ) ) = ( ( %s x. %s ) - ( R x. ( %s / 2 ) ) )' % (LE.L0('o'), G_, RM, H_, LE.L0('o'), G_, H_)),
                                                        D(w, As, 'oveq1d', [rme], '( %s x. ( ( %s - %s ) / ( o - 1 ) ) ) = ( R x. ( ( %s - %s ) / ( o - 1 ) ) )' % (RM, G_, g1, G_, g1))],
                                          '%s = %s' % (LE.FV('o'), FVR))], '( %s ` o ) = %s' % (FC, FVR))
    lam_e = D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [rme], '( %s x. ( ( 1 / o ) + ( 1 / ( 1 - o ) ) ) ) = ( R x. ( ( 1 / o ) + ( 1 / ( 1 - o ) ) ) )' % RM)], '%s = %s' % (LAMr(RM), LAMr('R')))],
              '( %s x. %s ) = ( %s x. %s )' % (LAMr(RM), G_, LAMr('R'), G_))
    body = lambda v: '( ( %s ` %s ) + ( R / ( %s - 1 ) ) )' % (FC, v, v)
    part1 = chain(w, As, [body('o'), FALL, '( %s x. %s )' % (LAMr('R'), G_), '( %s x. %s )' % (LAMr(RM), G_)],
                  [D(w, As, 'oveq1d', [fvr], '%s = %s' % (body('o'), FALL)), fal, ('r', lam_e)])
    # the Mellin identity of YB at 1 - o
    OM = '( 1 - o )'
    LSB = lambda v: LE.Z3.LS(CYBM, v)
    MLB = lambda v: '( 1 < ( Re ` %s ) -> ( %s x. %s ) = ( ( %s + ( %s x. %s ) ) - ( %s x. ( ( 1 / %s ) + ( 1 / ( 1 - %s ) ) ) ) ) )' % (
        v, Z3G(v), LSB(v), LE.ILG(CYBM, v, PAR), LE.EPSB, LE.ILG(CYM, '( 1 - %s )' % v, PAR), RM, v, v)
    assert L.split_imp(SE['zl3mlb'])[1] in ('A. s e. CC %s' % MLB('s'), '( A. s e. CC %s )' % MLB('s'))
    ph = 's = %s' % OM
    e_re = w.s([w.s([], 'fveq2', '( %s -> ( Re ` s ) = ( Re ` %s ) )' % (ph, OM))], 'breq2d', '( %s -> ( 1 < ( Re ` s ) <-> 1 < ( Re ` %s ) ) )' % (ph, OM))
    e_l = w.s([vsub(w, Z3G, 's', OM), vsub(w, LSB, 's', OM)], 'oveq12d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ph, Z3G('s'), LSB('s'), Z3G(OM), LSB(OM)))
    i_a = il_sub(w, CYBM, 's', OM)
    i_b = w.s([w.s([], 'oveq2', '( %s -> ( 1 - s ) = ( 1 - %s ) )' % (ph, OM)), il_sub(w, CYM, '( 1 - s )', '( 1 - %s )' % OM)], 'syl',
              '( %s -> %s = %s )' % (ph, LE.ILG(CYM, '( 1 - s )', PAR), LE.ILG(CYM, '( 1 - %s )' % OM, PAR)))
    RHSm = lambda v: '( ( %s + ( %s x. %s ) ) - ( %s x. ( ( 1 / %s ) + ( 1 / ( 1 - %s ) ) ) ) )' % (LE.ILG(CYBM, v, PAR), LE.EPSB, LE.ILG(CYM, '( 1 - %s )' % v, PAR), RM, v, v)
    e_r = w.s([w.s([i_a, w.s([i_b], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ph, LE.EPSB, LE.ILG(CYM, '( 1 - s )', PAR), LE.EPSB, LE.ILG(CYM, '( 1 - %s )' % OM, PAR)))], 'oveq12d',
                   '( %s -> ( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) ) )' % (ph, LE.ILG(CYBM, 's', PAR), LE.EPSB, LE.ILG(CYM, '( 1 - s )', PAR), LE.ILG(CYBM, OM, PAR), LE.EPSB, LE.ILG(CYM, '( 1 - %s )' % OM, PAR))),
               vsub(w, lambda v: '( %s x. ( ( 1 / %s ) + ( 1 / ( 1 - %s ) ) ) )' % (RM, v, v), 's', OM)], 'oveq12d', '( %s -> %s = %s )' % (ph, RHSm('s'), RHSm(OM)))
    assert MLB('s') == '( 1 < ( Re ` s ) -> ( %s x. %s ) = %s )' % (Z3G('s'), LSB('s'), RHSm('s'))
    bi = w.s([e_re, w.s([e_l, e_r], 'eqeq12d', '( %s -> ( ( %s x. %s ) = %s <-> ( %s x. %s ) = %s ) )' % (ph, Z3G('s'), LSB('s'), RHSm('s'), Z3G(OM), LSB(OM), RHSm(OM)))], 'imbi12d',
             '( %s -> ( %s <-> %s ) )' % (ph, MLB('s'), MLB(OM)))
    omc = V['omsc']
    mlb = D(w, As, 'mpd', [D(w, As, 'syl', [prs, w.inst('zl3mlb')], 'A. s e. CC %s' % MLB('s')), D(w, As, 'syl', [omc, w.s([bi], 'rspcv', '( %s e. CC -> ( A. s e. CC %s -> %s ) )' % (OM, MLB('s'), MLB(OM)))],
                                                                                                  '( A. s e. CC %s -> %s )' % (MLB('s'), MLB(OM)))], MLB(OM))
    reom = D(w, As, 'eqtrd', [D(w, As, 'resubd', [cst(w, As, 'ax-1cn', '1 e. CC'), s_c], '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` o ) )' % OM),
                              D(w, As, 'oveq1d', [cst(w, As, 're1', '( Re ` 1 ) = 1')], '( ( Re ` 1 ) - ( Re ` o ) ) = ( 1 - ( Re ` o ) )')], '( Re ` %s ) = ( 1 - ( Re ` o ) )' % OM)
    om1 = D(w, As, 'breqtrrd', [linarith(w, As, [s_hi], '1 < ( 1 - ( Re ` o ) )', closure=clS), reom], '1 < ( Re ` %s )' % OM)
    mel2 = D(w, As, 'mpd', [om1, mlb], '( %s x. %s ) = %s' % (Z3G(OM), LSB(OM), RHSm(OM)))
    nn_ = D(w, As, 'nncand', [cst(w, As, 'ax-1cn', '1 e. CC'), s_c], '( 1 - %s ) = o' % OM)
    ilo = D(w, As, 'syl', [nn_, il_sub(w, CYM, '( 1 - %s )' % OM, 'o')], '%s = %s' % (LE.ILG(CYM, '( 1 - %s )' % OM, PAR), LE.ILG(CYM, 'o', PAR)))
    a1, a2 = LE.ILG(CYM, 'o', PAR), LE.ILG(CYBM, OM, PAR)
    e, eb, r = EPS, LE.EPSB, RM
    pq = '( ( 1 / %s ) + ( 1 / o ) )' % OM
    pp_ = '( ( 1 / o ) + ( 1 / %s ) )' % OM
    rh2 = D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'oveq2d', [ilo], '( %s x. %s ) = ( %s x. %s )' % (eb, LE.ILG(CYM, '( 1 - %s )' % OM, PAR), eb, a1))],
                                                  '( %s + ( %s x. %s ) ) = ( %s + ( %s x. %s ) )' % (a2, eb, LE.ILG(CYM, '( 1 - %s )' % OM, PAR), a2, eb, a1)),
                               D(w, As, 'oveq2d', [D(w, As, 'oveq2d', [D(w, As, 'oveq2d', [nn_], '( 1 / ( 1 - %s ) ) = ( 1 / o )' % OM)], '( ( 1 / %s ) + ( 1 / ( 1 - %s ) ) ) = %s' % (OM, OM, pq))],
                                 '( %s x. ( ( 1 / %s ) + ( 1 / ( 1 - %s ) ) ) ) = ( %s x. %s )' % (r, OM, OM, r, pq))],
              '%s = ( ( %s + ( %s x. %s ) ) - ( %s x. %s ) )' % (RHSm(OM), a2, eb, a1, r, pq))
    mel3 = D(w, As, 'eqtrd', [mel2, rh2], '( %s x. %s ) = ( ( %s + ( %s x. %s ) ) - ( %s x. %s ) )' % (Z3G(OM), LSB(OM), a2, eb, a1, r, pq))
    # e ( ... ) = Lambda ( o )
    yb = D(w, As, 'syl', [prs, w.inst('zl3yb')], L.split_imp(SE['zl3yb'])[1])
    eeb = D(w, As, 'simprd', [D(w, As, 'simprd', [yb], '( %s = Y /\\ ( %s x. %s ) = 1 )' % (LE.INVB, e, eb))], '( %s x. %s ) = 1' % (e, eb))
    ec, i1c, i2c = V['ec'], V['i1c'], V['i2c']
    ebc = D(w, As, 'eqeltrd' if False else 'syl', [D(w, As, 'simpld', [D(w, As, 'simpld', [yb], '( %s /\\ %s = %s )' % (LE.PRB, LE.PARB, PAR))], LE.PRB), w.inst('idi')], '') if False else None
    # EPSB e. CC : ( M DChrGS YB ) / ( i ^ PARB sqrt M )
    chB = D(w, As, 'jca', [L2(B['mn'], 'M e. NN'), L2(B['ybd'], '%s e. ( Base ` ( DChr ` M ) )' % YB)], '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % YB)
    parb = D(w, As, 'simprd', [D(w, As, 'simpld', [yb], '( %s /\\ %s = %s )' % (LE.PRB, LE.PARB, PAR))], '%s = %s' % (LE.PARB, PAR))
    ppB = D(w, As, 'eqeltrd', [parb, ppS], '%s e. { 0 , 1 }' % LE.PARB)
    pbn = par_nn0(w, As, ppB, LE.PARB)
    mcc = D(w, As, 'nncnd', [L2(B['mn'], 'M e. NN')], 'M e. CC'); mne = D(w, As, 'nnne0d', [L2(B['mn'], 'M e. NN')], 'M =/= 0')
    ib = D(w, As, 'expcld', [cst(w, As, 'ax-icn', '_i e. CC'), pbn], '( _i ^ %s ) e. CC' % LE.PARB)
    ibn = D(w, As, 'expne0d', [cst(w, As, 'ax-icn', '_i e. CC'), cst(w, As, 'ine0', '_i =/= 0'), D(w, As, 'nn0zd', [pbn], '%s e. ZZ' % LE.PARB)], '( _i ^ %s ) =/= 0' % LE.PARB)
    smc = D(w, As, 'cxpcld', [mcc, cst(w, As, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) e. CC')
    smn = D(w, As, 'cxpne0d', [mcc, mne, cst(w, As, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) =/= 0')
    QB_ = '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) )' % LE.PARB
    ebc = D(w, As, 'divcld', [D(w, As, 'syl', [chB, w.inst('dchrgscl')], '( M DChrGS %s ) e. CC' % YB), D(w, As, 'mulcld', [ib, smc], '%s e. CC' % QB_), D(w, As, 'mulne0d', [ib, ibn, smc, smn], '%s =/= 0' % QB_)],
            '%s e. CC' % eb)
    rc = L2(rm_cc(w, A), '%s e. CC' % r)
    one_c = cst(w, As, 'ax-1cn', '1 e. CC')
    omne = D(w, As, 'subne0d', [one_c, s_c, D(w, As, 'necomd', [sne1], '1 =/= o')], '%s =/= 0' % OM)
    pqc = D(w, As, 'addcld', [D(w, As, 'reccld', [omc, omne], '( 1 / %s ) e. CC' % OM), D(w, As, 'reccld', [s_c, sne0], '( 1 / o ) e. CC')], '%s e. CC' % pq)
    # e r = r
    Ac1 = '( %s /\\ M = 1 )' % As; Ac2 = '( %s /\\ -. M = 1 )' % As
    e1 = D(w, Ac1, 'simprd', [D(w, Ac1, 'syl', [D(w, Ac1, 'jca', [ad(w, Ac1, prs, PR), w.s([], 'simpr', '( %s -> M = 1 )' % Ac1)], '( %s /\\ M = 1 )' % PR), w.inst('zl3m1')], '( %s = 0 /\\ %s = 1 )' % (PAR, EPS))], '%s = 1' % EPS)
    k1 = D(w, Ac1, 'eqtrd', [D(w, Ac1, 'oveq1d', [e1], '( %s x. %s ) = ( 1 x. %s )' % (e, r, r)), D(w, Ac1, 'mullidd', [ad(w, Ac1, rc, '%s e. CC' % r)], '( 1 x. %s ) = %s' % (r, r))], '( %s x. %s ) = %s' % (e, r, r))
    r0 = D(w, Ac2, 'iffalsed', [w.s([], 'simpr', '( %s -> -. M = 1 )' % Ac2)], '%s = 0' % r)
    k2 = D(w, Ac2, 'eqtr4d', [D(w, Ac2, 'eqtrd', [D(w, Ac2, 'oveq2d', [r0], '( %s x. %s ) = ( %s x. 0 )' % (e, r, e)), D(w, Ac2, 'mul01d', [ad(w, Ac2, ec, '%s e. CC' % e)], '( %s x. 0 ) = 0' % e)], '( %s x. %s ) = 0' % (e, r)), r0],
             '( %s x. %s ) = %s' % (e, r, r))
    er = w.s([k1, k2, D(w, As, 'exmidd', [], '( M = 1 \\/ -. M = 1 )')], 'mpjaodan', '( %s -> ( %s x. %s ) = %s )' % (As, e, r, r))
    X2 = '( %s + ( %s x. %s ) )' % (a2, eb, a1)
    ebac = D(w, As, 'mulcld', [ebc, i1c], '( %s x. %s ) e. CC' % (eb, a1))
    lam_ = chain(w, As, ['( %s x. ( %s - ( %s x. %s ) ) )' % (e, X2, r, pq), '( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) )' % (e, X2, e, r, pq),
                         '( ( ( %s x. %s ) + ( %s x. ( %s x. %s ) ) ) - ( %s x. ( %s x. %s ) ) )' % (e, a2, e, eb, a1, e, r, pq),
                         '( ( ( %s x. %s ) + ( ( %s x. %s ) x. %s ) ) - ( ( %s x. %s ) x. %s ) )' % (e, a2, e, eb, a1, e, r, pq),
                         '( ( ( %s x. %s ) + ( 1 x. %s ) ) - ( %s x. %s ) )' % (e, a2, a1, r, pq),
                         '( ( ( %s x. %s ) + %s ) - ( %s x. %s ) )' % (e, a2, a1, r, pq),
                         '( ( %s + ( %s x. %s ) ) - ( %s x. %s ) )' % (a1, e, a2, r, pp_)],
                   [D(w, As, 'subdid', [ec, D(w, As, 'addcld', [i2c, ebac], '%s e. CC' % X2), D(w, As, 'mulcld', [rc, pqc], '( %s x. %s ) e. CC' % (r, pq))],
                      '( %s x. ( %s - ( %s x. %s ) ) ) = ( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) )' % (e, X2, r, pq, e, X2, e, r, pq)),
                    D(w, As, 'oveq1d', [D(w, As, 'adddid', [ec, i2c, ebac], '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. ( %s x. %s ) ) )' % (e, X2, e, a2, e, eb, a1))],
                      '( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) ) = ( ( ( %s x. %s ) + ( %s x. ( %s x. %s ) ) ) - ( %s x. ( %s x. %s ) ) )' % (e, X2, e, r, pq, e, a2, e, eb, a1, e, r, pq)),
                    D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'eqcomd', [D(w, As, 'mulassd', [ec, ebc, i1c], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (e, eb, a1, e, eb, a1))],
                                                                  '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (e, eb, a1, e, eb, a1))],
                                                      '( ( %s x. %s ) + ( %s x. ( %s x. %s ) ) ) = ( ( %s x. %s ) + ( ( %s x. %s ) x. %s ) )' % (e, a2, e, eb, a1, e, a2, e, eb, a1)),
                                         D(w, As, 'eqcomd', [D(w, As, 'mulassd', [ec, rc, pqc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (e, r, pq, e, r, pq))],
                                           '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (e, r, pq, e, r, pq))],
                      '( ( ( %s x. %s ) + ( %s x. ( %s x. %s ) ) ) - ( %s x. ( %s x. %s ) ) ) = ( ( ( %s x. %s ) + ( ( %s x. %s ) x. %s ) ) - ( ( %s x. %s ) x. %s ) )' % (e, a2, e, eb, a1, e, r, pq, e, a2, e, eb, a1, e, r, pq)),
                    D(w, As, 'oveq12d', [D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [eeb], '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (e, eb, a1, a1))],
                                                      '( ( %s x. %s ) + ( ( %s x. %s ) x. %s ) ) = ( ( %s x. %s ) + ( 1 x. %s ) )' % (e, a2, e, eb, a1, e, a2, a1)),
                                         D(w, As, 'oveq1d', [er], '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (e, r, pq, r, pq))],
                      '( ( ( %s x. %s ) + ( ( %s x. %s ) x. %s ) ) - ( ( %s x. %s ) x. %s ) ) = ( ( ( %s x. %s ) + ( 1 x. %s ) ) - ( %s x. %s ) )' % (e, a2, e, eb, a1, e, r, pq, e, a2, a1, r, pq)),
                    D(w, As, 'oveq1d', [D(w, As, 'oveq2d', [D(w, As, 'mullidd', [i1c], '( 1 x. %s ) = %s' % (a1, a1))], '( ( %s x. %s ) + ( 1 x. %s ) ) = ( ( %s x. %s ) + %s )' % (e, a2, a1, e, a2, a1))],
                      '( ( ( %s x. %s ) + ( 1 x. %s ) ) - ( %s x. %s ) ) = ( ( ( %s x. %s ) + %s ) - ( %s x. %s ) )' % (e, a2, a1, r, pq, e, a2, a1, r, pq)),
                    D(w, As, 'oveq12d', [D(w, As, 'addcomd', [D(w, As, 'mulcld', [ec, i2c], '( %s x. %s ) e. CC' % (e, a2)), i1c], '( ( %s x. %s ) + %s ) = ( %s + ( %s x. %s ) )' % (e, a2, a1, a1, e, a2)),
                                         D(w, As, 'oveq2d', [D(w, As, 'addcomd', [D(w, As, 'reccld', [omc, omne], '( 1 / %s ) e. CC' % OM), D(w, As, 'reccld', [s_c, sne0], '( 1 / o ) e. CC')], '%s = %s' % (pq, pp_))],
                                           '( %s x. %s ) = ( %s x. %s )' % (r, pq, r, pp_))],
                      '( ( ( %s x. %s ) + %s ) - ( %s x. %s ) ) = ( ( %s + ( %s x. %s ) ) - ( %s x. %s ) )' % (e, a2, a1, r, pq, a1, e, a2, r, pp_))])
    assert LAMr(RM) == '( ( %s + ( %s x. %s ) ) - ( %s x. %s ) )' % (a1, e, a2, r, pp_)
    GP, LB = Z3G(OM), LSB(OM)
    lam2 = D(w, As, 'eqcomd', [D(w, As, 'eqtrd', [D(w, As, 'oveq2d', [mel3], '( %s x. ( %s x. %s ) ) = ( %s x. ( %s - ( %s x. %s ) ) )' % (e, GP, LB, e, X2, r, pq)), lam_],
                                                 '( %s x. ( %s x. %s ) ) = %s' % (e, GP, LB, LAMr(RM)))], '%s = ( %s x. ( %s x. %s ) )' % (LAMr(RM), e, GP, LB))
    # memberships
    chsZ = LE.tsub(L.split_imp(Z2S['zl2chs'])[1], {'N': 'M', 'X': YB, 'Z': OM})
    lbc = D(w, As, 'simpld', [D(w, As, 'syl2anc', [chB, D(w, As, 'jca', [omc, om1], '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (OM, OM)), w.inst('zl2chs')], chsZ)], '%s e. CC' % LB)
    pn_, prr, p00, p11 = p01(w, As, ppS, PAR)
    pcc = D(w, As, 'recnd', [prr], '%s e. CC' % PAR)
    spc2, reW2, _ = reim_w(w, As, OM, omc, pcc, prr, P=PAR)
    W2 = LE.WV(OM, PAR)
    clS.have(PAR, 'RR', prr); clS.have(PAR, 'ge0', p00)
    w2p = D(w, As, 'breqtrrd', [linarith(w, As, [s_hi, p00], '0 < ( ( ( 1 - ( Re ` o ) ) + %s ) / 2 )' % PAR, closure=clS),
                                D(w, As, 'eqtrd', [reW2, D(w, As, 'oveq1d', [D(w, As, 'oveq1d', [reom], '( ( Re ` %s ) + %s ) = ( ( 1 - ( Re ` o ) ) + %s )' % (OM, PAR, PAR))],
                                                                           '( ( ( Re ` %s ) + %s ) / 2 ) = ( ( ( 1 - ( Re ` o ) ) + %s ) / 2 )' % (OM, PAR, PAR))], '( Re ` %s ) = ( ( ( 1 - ( Re ` o ) ) + %s ) / 2 )' % (W2, PAR))],
              '0 < ( Re ` %s )' % W2)
    w2c = D(w, As, 'halfcld', [spc2], '%s e. CC' % W2)
    clM = Closure(w, As, {'M': ('NN', L2(B['mn'], 'M e. NN')), '_pi': ('RR+', cst(w, As, 'pirp', '_pi e. RR+'))})
    gpc = D(w, As, 'mulcld', [D(w, As, 'cxpcld', [clM.mem('( M / _pi )', 'CC'), w2c], '( ( M / _pi ) ^c %s ) e. CC' % W2),
                              D(w, As, 'syl', [D(w, As, 'syl2anc', [w2c, w2p, w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % W2), w.inst('gamcl')], '( _G ` %s ) e. CC' % W2)], '%s e. CC' % GP)
    Mh = '( M ^c ( ( 1 / 2 ) - o ) )'
    mhc = D(w, As, 'cxpcld', [mcc, D(w, As, 'subcld', [cst(w, As, 'halfcn', '( 1 / 2 ) e. CC'), s_c], '( ( 1 / 2 ) - o ) e. CC')], '%s e. CC' % Mh)
    QQo = '( %s ` o )' % LE.QQ(PAR)
    QBb = lambda v: '( ( -u ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 0 ) -> ( ( %s ` %s ) e. CC /\\ ( abs ` ( %s ` %s ) ) <_ ( ; 1 2 x. ( ( ( abs ` ( Im ` %s ) ) + 2 ) ^c ( ( 1 / 2 ) - ( Re ` %s ) ) ) ) ) )' % (v, v, LE.QQ(PAR), v, LE.QQ(PAR), v, v, v)
    qb = D(w, As, 'syl', [ppS, w.inst('zl3qbnd')], 'A. z e. CC %s' % QBb('z'))
    qbo = D(w, As, 'mpd', [D(w, As, 'jca', [s_lo, D(w, As, 'ltled', [rsr, cst(w, As, '0re', '0 e. RR'), s_hi], '( Re ` o ) <_ 0')], '( -u ( 1 / 2 ) <_ ( Re ` o ) /\\ ( Re ` o ) <_ 0 )'),
                           D(w, As, 'mpd', [qb, D(w, As, 'syl', [s_c, w.s([wsub(w, QBb, 'z', 'o')], 'rspcv', '( o e. CC -> ( A. z e. CC %s -> %s ) )' % (QBb('z'), QBb('o')))], '( A. z e. CC %s -> %s )' % (QBb('z'), QBb('o')))], QBb('o'))],
           '( %s e. CC /\\ ( abs ` %s ) <_ ( ; 1 2 x. ( ( ( abs ` ( Im ` o ) ) + 2 ) ^c ( ( 1 / 2 ) - ( Re ` o ) ) ) ) )' % (QQo, QQo))
    qqc = D(w, As, 'simpld', [qbo], '%s e. CC' % QQo)
    gfr = D(w, As, 'syl2anc', [L2(B['mpa'], MPA), D(w, As, '3jca', [s_c, linarith(w, As, [s_lo], '-u 1 < ( Re ` o )', closure=clS), linarith(w, As, [s_hi], '( Re ` o ) < 1', closure=clS)],
                                                    '( o e. CC /\\ -u 1 < ( Re ` o ) /\\ ( Re ` o ) < 1 )'), w.inst('zl3gfr')], '( %s x. %s ) = ( %s x. %s )' % (GP, G_, Mh, QQo))
    RF = '( ( %s x. %s ) x. ( %s x. %s ) )' % (Mh, e, QQo, LB)
    fin_o = chain(w, As, [body('o'), '( %s x. %s )' % (LAMr(RM), G_), '( ( %s x. ( %s x. %s ) ) x. %s )' % (e, GP, LB, G_), '( %s x. ( ( %s x. %s ) x. %s ) )' % (e, GP, LB, G_),
                          '( %s x. ( ( %s x. %s ) x. %s ) )' % (e, GP, G_, LB), '( %s x. ( ( %s x. %s ) x. %s ) )' % (e, Mh, QQo, LB), '( %s x. ( %s x. ( %s x. %s ) ) )' % (e, Mh, QQo, LB),
                          '( ( %s x. %s ) x. ( %s x. %s ) )' % (e, Mh, QQo, LB), RF],
                  [part1, D(w, As, 'oveq1d', [lam2], '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) x. %s )' % (LAMr(RM), G_, e, GP, LB, G_)),
                   D(w, As, 'mulassd', [ec, D(w, As, 'mulcld', [gpc, lbc], '( %s x. %s ) e. CC' % (GP, LB)), V['gc']], '( ( %s x. ( %s x. %s ) ) x. %s ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (e, GP, LB, G_, e, GP, LB, G_)),
                   D(w, As, 'oveq2d', [D(w, As, 'mul32d', [gpc, lbc, V['gc']], '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (GP, LB, G_, GP, G_, LB))], '( %s x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (e, GP, LB, G_, e, GP, G_, LB)),
                   D(w, As, 'oveq2d', [D(w, As, 'oveq1d', [gfr], '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (GP, G_, LB, Mh, QQo, LB))], '( %s x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (e, GP, G_, LB, e, Mh, QQo, LB)),
                   D(w, As, 'oveq2d', [D(w, As, 'mulassd', [mhc, qqc, lbc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (Mh, QQo, LB, Mh, QQo, LB))], '( %s x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (e, Mh, QQo, LB, e, Mh, QQo, LB)),
                   ('r', D(w, As, 'mulassd', [ec, mhc, D(w, As, 'mulcld', [qqc, lbc], '( %s x. %s ) e. CC' % (QQo, LB))], '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (e, Mh, QQo, LB, e, Mh, QQo, LB))),
                   D(w, As, 'oveq1d', [D(w, As, 'mulcomd', [ec, mhc], '( %s x. %s ) = ( %s x. %s )' % (e, Mh, Mh, e))], '( ( %s x. %s ) x. ( %s x. %s ) ) = %s' % (e, Mh, QQo, LB, RF))])
    COND = lambda v: '( -u ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) < 0 )' % (v, v)
    RFv = lambda v: '( ( ( M ^c ( ( 1 / 2 ) - %s ) ) x. %s ) x. ( ( %s ` %s ) x. %s ) )' % (v, e, LE.QQ(PAR), v, LSB('( 1 - %s )' % v))
    assert RFv('o') == RF
    ral = D(w, A, 'ralrimiva', [D(w, As0, 'ex', [fin_o], '( %s -> %s = %s )' % (COND('o'), body('o'), RF))], 'A. o e. CC ( %s -> %s = %s )' % (COND('o'), body('o'), RF))
    ph = 'o = z'
    c1 = w.s([w.s([w.s([], 'fveq2', '( %s -> ( Re ` o ) = ( Re ` z ) )' % ph)], 'breq2d', '( %s -> ( -u ( 1 / 2 ) <_ ( Re ` o ) <-> -u ( 1 / 2 ) <_ ( Re ` z ) ) )' % ph),
              w.s([w.s([], 'fveq2', '( %s -> ( Re ` o ) = ( Re ` z ) )' % ph)], 'breq1d', '( %s -> ( ( Re ` o ) < 0 <-> ( Re ` z ) < 0 ) )' % ph)], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ph, COND('o'), COND('z')))
    c2 = w.s([w.s([w.s([], 'fveq2', '( %s -> ( %s ` o ) = ( %s ` z ) )' % (ph, FC, FC)), w.s([w.s([], 'oveq1', '( %s -> ( o - 1 ) = ( z - 1 ) )' % ph)], 'oveq2d', '( %s -> ( R / ( o - 1 ) ) = ( R / ( z - 1 ) ) )' % ph)],
                  'oveq12d', '( %s -> %s = %s )' % (ph, body('o'), body('z'))), vsub(w, RFv, 'o', 'z')], 'eqeq12d', '( %s -> ( %s = %s <-> %s = %s ) )' % (ph, body('o'), RF, body('z'), RFv('z')))
    cb = w.s([w.s([c1, c2], 'imbi12d', '( %s -> ( ( %s -> %s = %s ) <-> ( %s -> %s = %s ) ) )' % (ph, COND('o'), body('o'), RF, COND('z'), body('z'), RFv('z')))], 'cbvralvw',
             '( A. o e. CC ( %s -> %s = %s ) <-> A. z e. CC ( %s -> %s = %s ) )' % (COND('o'), body('o'), RF, COND('z'), body('z'), RFv('z')))
    w.qed([D(w, A, 'mpbid', [ral, w.s([cb], 'a1i', '( %s -> ( A. o e. CC ( %s -> %s = %s ) <-> A. z e. CC ( %s -> %s = %s ) ) )' % (A, COND('o'), body('o'), RF, COND('z'), body('z'), RFv('z')))], Cc)],
          'idi', SE['zl3fey'])
    goe(w)


def peel(w, Aprev, x, S, Bx, goal, st, ex_step):
    """from st: ( ( Aprev /\\ ( x e. S /\\ Bx ) ) -> goal ) and ex_step: ( Aprev -> E. x e. S Bx ) derive ( Aprev -> goal )"""
    a = w.s([st], 'anassrs', '( ( ( %s /\\ %s e. %s ) /\\ %s ) -> %s )' % (Aprev, x, S, Bx, goal))
    b = w.s([a], 'ex', '( ( %s /\\ %s e. %s ) -> ( %s -> %s ) )' % (Aprev, x, S, Bx, goal))
    c = D(w, Aprev, 'rexlimdva', [b], '( E. %s e. %s %s -> %s )' % (x, S, Bx, goal))
    return D(w, Aprev, 'mpd', [ex_step, c], goal)


# ---------------------------------------------------------------- zl3fgr
if wante('zl3fgr', MAIN):
    w = W('zl3fgr', 'Growth, part (i) of PCONT: ` abs F ( z ) <_ c e ^ ( 3 abs Im z ) ` on the strip ` -1/2 <_ Re z <_ 2 ` ( ~ zl3ilb , ~ zl3hgb , ~ zl3dq , ~ zl2rtn ).')
    A, Cc = ante_e('zl3fgr')
    pr = w.s([], 'id', '( %s -> %s )' % (A, A))
    B = pr_base(w, A, pr)
    ILB = lambda C, c: 'A. w e. CC ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ %s )' % (LE.ILG(C, 'w', PAR), c)
    def ren_il(C, new):
        bi = w.s([w.s([w.s([], 'breq2', '( c = %s -> ( ( abs ` %s ) <_ c <-> ( abs ` %s ) <_ %s ) )' % (new, LE.ILG(C, 'w', PAR), LE.ILG(C, 'w', PAR), new))], 'imbi2d',
                      '( c = %s -> ( ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ c ) <-> ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ %s ) ) )'
                      % (new, LE.ILG(C, 'w', PAR), LE.ILG(C, 'w', PAR), new))], 'ralbidv', '( c = %s -> ( %s <-> %s ) )' % (new, ILB(C, 'c'), ILB(C, new)))
        return w.s([bi], 'cbvrexvw', '( E. c e. RR %s <-> E. %s e. RR %s )' % (ILB(C, 'c'), new, ILB(C, new)))
    exf = D(w, A, 'mpbid', [D(w, A, 'syl', [B['taY'], w.inst('zl3ilb')], 'E. c e. RR %s' % ILB(CYM, 'c')), w.s([ren_il(CYM, 'f')], 'a1i', '( %s -> ( E. c e. RR %s <-> E. f e. RR %s ) )' % (A, ILB(CYM, 'c'), ILB(CYM, 'f')))],
            'E. f e. RR %s' % ILB(CYM, 'f'))
    exh = D(w, A, 'mpbid', [D(w, A, 'syl', [B['taB'], w.inst('zl3ilb')], 'E. c e. RR %s' % ILB(CYBM, 'c')), w.s([ren_il(CYBM, 'h')], 'a1i', '( %s -> ( E. c e. RR %s <-> E. h e. RR %s ) )' % (A, ILB(CYBM, 'c'), ILB(CYBM, 'h')))],
            'E. h e. RR %s' % ILB(CYBM, 'h'))
    E3v = lambda v: '( exp ` ( 3 x. ( abs ` ( Im ` %s ) ) ) )' % v
    HGB = lambda c: 'A. v e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` v ) /\\ ( Re ` v ) <_ 2 ) -> ( ( abs ` %s ) <_ ( %s x. %s ) /\\ ( abs ` %s ) <_ ( %s x. %s ) ) )' % (LE.HV('v', PAR), c, E3v('v'), LE.GV('v', PAR), c, E3v('v'))
    exl = D(w, A, 'mpbid', [D(w, A, 'syl', [B['mpa'], w.inst('zl3hgb')], 'E. c e. RR+ %s' % HGB('c')), w.s([w.s([wsub(w, HGB, 'c', 'l')], 'cbvrexvw', '( E. c e. RR+ %s <-> E. l e. RR+ %s )' % (HGB('c'), HGB('l')))], 'a1i',
                                                                                                   '( %s -> ( E. c e. RR+ %s <-> E. l e. RR+ %s ) )' % (A, HGB('c'), HGB('l')))], 'E. l e. RR+ %s' % HGB('l'))
    g1 = LE.GV('1', PAR)
    DQB = lambda c: 'A. v e. %s ( abs ` ( %s ` v ) ) <_ ( %s + ( ( abs ` %s ) + ( abs ` %s ) ) )' % (STR, DQP, c, LE.GV('v', PAR), g1)
    dq = D(w, A, 'syl', [B['mpa'], w.inst('zl3dq')], LE.tsub(L.split_imp(SE['zl3dq'])[1], {'P': PAR}))
    exo0 = D(w, A, 'simprd', [dq], 'E. c e. RR %s' % DQB('c'))
    exo = D(w, A, 'mpbid', [exo0, w.s([w.s([wsub(w, DQB, 'c', 'o')], 'cbvrexvw', '( E. c e. RR %s <-> E. o e. RR %s )' % (DQB('c'), DQB('o')))], 'a1i', '( %s -> ( E. c e. RR %s <-> E. o e. RR %s ) )' % (A, DQB('c'), DQB('o')))],
            'E. o e. RR %s' % DQB('o'))
    A1 = '( %s /\\ ( f e. RR /\\ %s ) )' % (A, ILB(CYM, 'f'))
    A2 = '( %s /\\ ( h e. RR /\\ %s ) )' % (A1, ILB(CYBM, 'h'))
    A3 = '( %s /\\ ( l e. RR+ /\\ %s ) )' % (A2, HGB('l'))
    A4 = '( %s /\\ ( o e. RR /\\ %s ) )' % (A3, DQB('o'))
    lift = _lift
    L4 = lambda st: lift(w, st, A4)
    fr = D(w, A4, 'simprl' if False else 'idi', [], '') if False else lift(w, w.s([], 'simprl', '( %s -> f e. RR )' % A1), A4)
    bf = lift(w, w.s([], 'simprr', '( %s -> %s )' % (A1, ILB(CYM, 'f'))), A4)
    hr = lift(w, w.s([], 'simprl', '( %s -> h e. RR )' % A2), A4); bh = lift(w, w.s([], 'simprr', '( %s -> %s )' % (A2, ILB(CYBM, 'h'))), A4)
    lrp = lift(w, w.s([], 'simprl', '( %s -> l e. RR+ )' % A3), A4); bl = lift(w, w.s([], 'simprr', '( %s -> %s )' % (A3, HGB('l'))), A4)
    orr = w.s([], 'simprl', '( %s -> o e. RR )' % A4); bo = w.s([], 'simprr', '( %s -> %s )' % (A4, DQB('o')))
    Az = '( %s /\\ z e. %s )' % (A4, STR)
    LZ = lambda st, f: ad(w, Az, st, f)
    zin = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, STR))
    zst = D(w, Az, 'sylib', [zin, w.inst('elstr')], '( z e. CC /\\ ( Re ` z ) e. ( -u ( 1 / 2 ) [,] 2 ) )')
    zc = D(w, Az, 'simpld', [zst], 'z e. CC')
    zre = D(w, Az, 'mpbid', [D(w, Az, 'simprd', [zst], '( Re ` z ) e. ( -u ( 1 / 2 ) [,] 2 )'),
                             D(w, Az, 'syl2anc', [Closure(w, Az, {}).mem('-u ( 1 / 2 )', 'RR'), cst(w, Az, '2re', '2 e. RR'), w.inst('elicc2')],
                               '( ( Re ` z ) e. ( -u ( 1 / 2 ) [,] 2 ) <-> ( ( Re ` z ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 2 ) )')],
          '( ( Re ` z ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 2 )')
    rzr = D(w, Az, 'simp1d', [zre], '( Re ` z ) e. RR'); zlo = D(w, Az, 'simp2d', [zre], '-u ( 1 / 2 ) <_ ( Re ` z )'); zhi = D(w, Az, 'simp3d', [zre], '( Re ` z ) <_ 2')
    clz = Closure(w, Az, {'( Re ` z )': ('RR', rzr)})
    zU = in_uo(w, Az, 'z', zc, linarith(w, Az, [zlo], '-u 1 < ( Re ` z )', closure=clz), linarith(w, Az, [zhi], '( Re ` z ) < 3', closure=clz))
    fcz = D(w, Az, 'syl', [zU, w.s([fc_sub(w, 'z'), w.s([], 'eqid', '%s = %s' % (FC, FC)), w.s([], 'ovex', '%s e. _V' % fc_body('z'))], 'fvmpt', '( z e. %s -> ( %s ` z ) = %s )' % (UO, FC, fc_body('z')))],
            '( %s ` z ) = %s' % (FC, fc_body('z')))
    OMz = '( 1 - z )'
    omzc = D(w, Az, 'subcld', [cst(w, Az, 'ax-1cn', '1 e. CC'), zc], '%s e. CC' % OMz)
    i1 = D(w, Az, 'syl', [zc, w.s([il_sub(w, CYM, 'w', 'z'), w.s([], 'eqid', '%s = %s' % (I1, I1)), w.s([], 'fvex', '%s e. _V' % LE.ILG(CYM, 'z', PAR))], 'fvmpt',
                                   '( z e. CC -> ( %s ` z ) = %s )' % (I1, LE.ILG(CYM, 'z', PAR)))], '( %s ` z ) = %s' % (I1, LE.ILG(CYM, 'z', PAR)))
    i2 = D(w, Az, 'syl', [omzc, w.s([il_sub(w, CYBM, 'w', OMz), w.s([], 'eqid', '%s = %s' % (I2, I2)), w.s([], 'fvex', '%s e. _V' % LE.ILG(CYBM, OMz, PAR))], 'fvmpt',
                                     '( %s e. CC -> ( %s ` %s ) = %s )' % (OMz, I2, OMz, LE.ILG(CYBM, OMz, PAR)))], '( %s ` %s ) = %s' % (I2, OMz, LE.ILG(CYBM, OMz, PAR)))
    def ilb_at(C, bnd, c, X, xc, lo, hi):
        ph = 'w = %s' % X
        body = lambda q: '( ( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) -> ( abs ` %s ) <_ %s )' % (q, q, LE.ILG(C, q, PAR), c)
        sub = w.s([w.s([w.s([w.s([], 'fveq2', '( %s -> ( Re ` w ) = ( Re ` %s ) )' % (ph, X))], 'breq2d', '( %s -> ( -u 1 <_ ( Re ` w ) <-> -u 1 <_ ( Re ` %s ) ) )' % (ph, X)),
                        w.s([w.s([], 'fveq2', '( %s -> ( Re ` w ) = ( Re ` %s ) )' % (ph, X))], 'breq1d', '( %s -> ( ( Re ` w ) <_ 3 <-> ( Re ` %s ) <_ 3 ) )' % (ph, X))], 'anbi12d',
                       '( %s -> ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) <-> ( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) ) )' % (ph, X, X)),
                   w.s([w.s([il_sub(w, C, 'w', X)], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (ph, LE.ILG(C, 'w', PAR), LE.ILG(C, X, PAR)))], 'breq1d',
                       '( %s -> ( ( abs ` %s ) <_ %s <-> ( abs ` %s ) <_ %s ) )' % (ph, LE.ILG(C, 'w', PAR), c, LE.ILG(C, X, PAR), c))], 'imbi12d', '( %s -> ( %s <-> %s ) )' % (ph, body('w'), body(X)))
        inst = D(w, Az, 'mpd', [LZ(bnd, ILB(C, c)), D(w, Az, 'syl', [xc, w.s([sub], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (X, ILB(C, c), body(X)))], '( %s -> %s )' % (ILB(C, c), body(X)))], body(X))
        return D(w, Az, 'mpd', [D(w, Az, 'jca', [lo, hi], '( -u 1 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (X, X)), inst], '( abs ` %s ) <_ %s' % (LE.ILG(C, X, PAR), c))
    b1 = ilb_at(CYM, bf, 'f', 'z', zc, linarith(w, Az, [zlo], '-u 1 <_ ( Re ` z )', closure=clz), linarith(w, Az, [zhi], '( Re ` z ) <_ 3', closure=clz))
    reom = D(w, Az, 'eqtrd', [D(w, Az, 'resubd', [cst(w, Az, 'ax-1cn', '1 e. CC'), zc], '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` z ) )' % OMz),
                              D(w, Az, 'oveq1d', [cst(w, Az, 're1', '( Re ` 1 ) = 1')], '( ( Re ` 1 ) - ( Re ` z ) ) = ( 1 - ( Re ` z ) )')], '( Re ` %s ) = ( 1 - ( Re ` z ) )' % OMz)
    b2 = ilb_at(CYBM, bh, 'h', OMz, omzc, D(w, Az, 'breqtrrd', [linarith(w, Az, [zhi], '-u 1 <_ ( 1 - ( Re ` z ) )', closure=clz), reom], '-u 1 <_ ( Re ` %s )' % OMz),
                D(w, Az, 'eqbrtrd', [reom, linarith(w, Az, [zlo], '( 1 - ( Re ` z ) ) <_ 3', closure=clz)], '( Re ` %s ) <_ 3' % OMz))
    HGBb = lambda q: '( ( -u ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 2 ) -> ( ( abs ` %s ) <_ ( l x. %s ) /\\ ( abs ` %s ) <_ ( l x. %s ) ) )' % (q, q, LE.HV(q, PAR), E3v(q), LE.GV(q, PAR), E3v(q))
    blz = D(w, Az, 'mpd', [D(w, Az, 'jca', [zlo, zhi], '( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 2 )'),
                           D(w, Az, 'mpd', [LZ(bl, HGB('l')), D(w, Az, 'syl', [zc, w.s([wsub(w, HGBb, 'v', 'z')], 'rspcv', '( z e. CC -> ( %s -> %s ) )' % (HGB('l'), HGBb('z')))], '( %s -> %s )' % (HGB('l'), HGBb('z')))], HGBb('z'))],
          '( ( abs ` %s ) <_ ( l x. %s ) /\\ ( abs ` %s ) <_ ( l x. %s ) )' % (LE.HV('z', PAR), E3v('z'), LE.GV('z', PAR), E3v('z')))
    DQBb = lambda q: '( abs ` ( %s ` %s ) ) <_ ( o + ( ( abs ` %s ) + ( abs ` %s ) ) )' % (DQP, q, LE.GV(q, PAR), g1)
    boz = D(w, Az, 'mpd', [LZ(bo, DQB('o')), D(w, Az, 'syl', [zin, w.s([wsub(w, DQBb, 'v', 'z')], 'rspcv', '( z e. %s -> ( %s -> %s ) )' % (STR, DQB('o'), DQBb('z')))], '( %s -> %s )' % (DQB('o'), DQBb('z')))], DQBb('z'))
    LZ2 = lambda st, f: lift(w, st, Az)
    Vz = value_facts(w, Az, 'z', zc, zU, B, LZ2)
    I1z, I2z, e, G_, H_ = '( %s ` z )' % I1, '( %s ` %s )' % (I2, OMz), EPS, LE.GV('z', PAR), LE.HV('z', PAR)
    DQz = '( %s ` z )' % DQP
    i1c = D(w, Az, 'eqeltrd', [i1, Vz['i1c']], '%s e. CC' % I1z)
    i2c = D(w, Az, 'eqeltrd', [i2, Vz['i2c']], '%s e. CC' % I2z)
    ec, gc, hc = Vz['ec'], Vz['gc'], Vz['hc']
    hdq = D(w, Az, 'simpld', [D(w, Az, 'simpld', [LZ2(dq, '')], '( %s /\\ A. v e. %s ( v =/= 1 -> ( %s ` v ) = ( ( %s - %s ) / ( v - 1 ) ) ) )' % (HOL(DQP, UO), UO, DQP, LE.GV('v', PAR), g1))], HOL(DQP, UO))
    dqc = D(w, Az, 'ffvelcdmd', [D(w, Az, 'syl', [D(w, Az, 'simpld', [hdq], '%s e. ( %s -cn-> CC )' % (DQP, UO)), w.inst('cncff')], '%s : %s --> CC' % (DQP, UO)), zU], '%s e. CC' % DQz)
    rmc = LZ2(rm_cc(w, A), '%s e. CC' % RM)
    rpr_, _ = rm_facts(w, Az)
    rmn, rmr, rm0, rm1_ = p01(w, Az, rpr_, RM)
    S1 = '( %s + ( %s x. %s ) )' % (I1z, e, I2z)
    T1, T2, T3 = '( %s x. %s )' % (S1, G_), '( %s x. ( %s / 2 ) )' % (RM, H_), '( %s x. %s )' % (RM, DQz)
    s1c = D(w, Az, 'addcld', [i1c, D(w, Az, 'mulcld', [ec, i2c], '( %s x. %s ) e. CC' % (e, I2z))], '%s e. CC' % S1)
    t1c = D(w, Az, 'mulcld', [s1c, gc], '%s e. CC' % T1)
    t2c = D(w, Az, 'mulcld', [rmc, D(w, Az, 'halfcld', [hc], '( %s / 2 ) e. CC' % H_)], '%s e. CC' % T2)
    t3c = D(w, Az, 'mulcld', [rmc, dqc], '%s e. CC' % T3)
    FB = fc_body('z')
    assert FB == '( ( %s - %s ) + %s )' % (T1, T2, T3)
    ab = lambda x: '( abs ` %s )' % x
    tri1 = D(w, Az, 'abstrid', [D(w, Az, 'subcld', [t1c, t2c], '( %s - %s ) e. CC' % (T1, T2)), t3c], '%s <_ ( %s + %s )' % (ab(FB), ab('( %s - %s )' % (T1, T2)), ab(T3)))
    tri2 = D(w, Az, 'abs2dif2d', [t1c, t2c], '%s <_ ( %s + %s )' % (ab('( %s - %s )' % (T1, T2)), ab(T1), ab(T2)))
    at1 = D(w, Az, 'absmuld', [s1c, gc], '%s = ( %s x. %s )' % (ab(T1), ab(S1), ab(G_)))
    ae = D(w, Az, 'syl2anc', [LZ2(B['ch'], ''), D(w, Az, 'jca', [LZ2(D(w, A, 'simprd', [pr], '( M DChrCond Y ) = M'), ''), par_nn0(w, Az, LZ2(B['pp'], ''), PAR)], '( ( M DChrCond Y ) = M /\\ %s e. NN0 )' % PAR), w.inst('zl2rtn')],
             '%s = 1' % ab(e))
    es1 = D(w, Az, 'breqtrd', [D(w, Az, 'abstrid', [i1c, D(w, Az, 'mulcld', [ec, i2c], '( %s x. %s ) e. CC' % (e, I2z))], '%s <_ ( %s + %s )' % (ab(S1), ab(I1z), ab('( %s x. %s )' % (e, I2z)))),
                               D(w, Az, 'oveq2d', [D(w, Az, 'eqtrd', [D(w, Az, 'absmuld', [ec, i2c], '%s = ( %s x. %s )' % (ab('( %s x. %s )' % (e, I2z)), ab(e), ab(I2z))),
                                                                       D(w, Az, 'eqtrd', [D(w, Az, 'oveq1d', [ae], '( %s x. %s ) = ( 1 x. %s )' % (ab(e), ab(I2z), ab(I2z))), D(w, Az, 'mullidd', [D(w, Az, 'abscld', [i2c], '%s e. RR' % ab(I2z)) and D(w, Az, 'recnd', [D(w, Az, 'abscld', [i2c], '%s e. RR' % ab(I2z))], '%s e. CC' % ab(I2z))], '( 1 x. %s ) = %s' % (ab(I2z), ab(I2z)))],
                                                                         '( %s x. %s ) = %s' % (ab(e), ab(I2z), ab(I2z)))], '%s = %s' % (ab('( %s x. %s )' % (e, I2z)), ab(I2z)))],
                                 '( %s + %s ) = ( %s + %s )' % (ab(I1z), ab('( %s x. %s )' % (e, I2z)), ab(I1z), ab(I2z)))], '%s <_ ( %s + %s )' % (ab(S1), ab(I1z), ab(I2z)))
    a1f = D(w, Az, 'eqbrtrd', [D(w, Az, 'fveq2d', [i1], '%s = %s' % (ab(I1z), ab(LE.ILG(CYM, 'z', PAR)))), b1], '%s <_ f' % ab(I1z))
    a2h = D(w, Az, 'eqbrtrd', [D(w, Az, 'fveq2d', [i2], '%s = %s' % (ab(I2z), ab(LE.ILG(CYBM, OMz, PAR)))), b2], '%s <_ h' % ab(I2z))
    at2 = D(w, Az, 'eqtrd', [D(w, Az, 'absmuld', [rmc, D(w, Az, 'halfcld', [hc], '( %s / 2 ) e. CC' % H_)], '%s = ( %s x. %s )' % (ab(T2), ab(RM), ab('( %s / 2 )' % H_))),
                             D(w, Az, 'oveq12d', [D(w, Az, 'absidd', [rmr, rm0], '%s = %s' % (ab(RM), RM)),
                                                  D(w, Az, 'eqtrd', [D(w, Az, 'absdivd', [hc, cst(w, Az, '2cn', '2 e. CC'), cst(w, Az, '2ne0', '2 =/= 0')], '%s = ( %s / ( abs ` 2 ) )' % (ab('( %s / 2 )' % H_), ab(H_))),
                                                                     D(w, Az, 'oveq2d', [D(w, Az, 'absidd', [cst(w, Az, '2re', '2 e. RR'), cst(w, Az, '0le2', '0 <_ 2')], '( abs ` 2 ) = 2')], '( %s / ( abs ` 2 ) ) = ( %s / 2 )' % (ab(H_), ab(H_)))],
                                                    '%s = ( %s / 2 )' % (ab('( %s / 2 )' % H_), ab(H_)))], '( %s x. %s ) = ( %s x. ( %s / 2 ) )' % (ab(RM), ab('( %s / 2 )' % H_), RM, ab(H_)))],
            '%s = ( %s x. ( %s / 2 ) )' % (ab(T2), RM, ab(H_)))
    at3 = D(w, Az, 'eqtrd', [D(w, Az, 'absmuld', [rmc, dqc], '%s = ( %s x. %s )' % (ab(T3), ab(RM), ab(DQz))), D(w, Az, 'oveq1d', [D(w, Az, 'absidd', [rmr, rm0], '%s = %s' % (ab(RM), RM))], '( %s x. %s ) = ( %s x. %s )' % (ab(RM), ab(DQz), RM, ab(DQz)))],
            '%s = ( %s x. %s )' % (ab(T3), RM, ab(DQz)))
    E3 = E3v('z')
    gl = D(w, Az, 'simprd', [blz], '%s <_ ( l x. %s )' % (ab(G_), E3)); hl = D(w, Az, 'simpld', [blz], '%s <_ ( l x. %s )' % (ab(H_), E3))
    fr_, hr_, lrp_, orr_ = LZ2(fr, 'f e. RR'), LZ2(hr, 'h e. RR'), LZ2(lrp, 'l e. RR+'), LZ2(orr, 'o e. RR')
    ag1 = ab(g1)
    aimz = '( abs ` ( Im ` z ) )'
    cl = Closure(w, Az, {'f': ('RR', fr_), 'h': ('RR', hr_), 'l': ('RR+', lrp_), 'o': ('RR', orr_), RM: [('RR', rmr), ('ge0', rm0)],
                         ab(I1z): [('RR', D(w, Az, 'abscld', [i1c], '%s e. RR' % ab(I1z))), ('ge0', D(w, Az, 'absge0d', [i1c], '0 <_ %s' % ab(I1z)))],
                         ab(I2z): [('RR', D(w, Az, 'abscld', [i2c], '%s e. RR' % ab(I2z))), ('ge0', D(w, Az, 'absge0d', [i2c], '0 <_ %s' % ab(I2z)))],
                         ab(S1): [('RR', D(w, Az, 'abscld', [s1c], '%s e. RR' % ab(S1))), ('ge0', D(w, Az, 'absge0d', [s1c], '0 <_ %s' % ab(S1)))],
                         ab(G_): [('RR', D(w, Az, 'abscld', [gc], '%s e. RR' % ab(G_))), ('ge0', D(w, Az, 'absge0d', [gc], '0 <_ %s' % ab(G_)))],
                         ab(H_): [('RR', D(w, Az, 'abscld', [hc], '%s e. RR' % ab(H_))), ('ge0', D(w, Az, 'absge0d', [hc], '0 <_ %s' % ab(H_)))],
                         ab(DQz): [('RR', D(w, Az, 'abscld', [dqc], '%s e. RR' % ab(DQz))), ('ge0', D(w, Az, 'absge0d', [dqc], '0 <_ %s' % ab(DQz)))],
                         ag1: [('RR', D(w, Az, 'abscld', [Vz['g1c']], '%s e. RR' % ag1)), ('ge0', D(w, Az, 'absge0d', [Vz['g1c']], '0 <_ %s' % ag1))],
                         aimz: [('RR', D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'imcld', [zc], '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '%s e. RR' % aimz)),
                                ('ge0', D(w, Az, 'absge0d', [D(w, Az, 'recnd', [D(w, Az, 'imcld', [zc], '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '0 <_ %s' % aimz))]})
    cl.leaf(E3, 'RR+', D(w, Az, 'rpefcld', [cl.mem('( 3 x. %s )' % aimz, 'RR')], '%s e. RR+' % E3))
    e31 = linarith(w, Az, [D(w, Az, 'syl2anc', [cl.mem('( 3 x. %s )' % aimz, 'RR'), cl.ge0('( 3 x. %s )' % aimz), w.inst('bvefge1p')], '( 1 + ( 3 x. %s ) ) <_ %s' % (aimz, E3)), cl.ge0('( 3 x. %s )' % aimz)],
                   '1 <_ %s' % E3, closure=cl, atoms=[E3, aimz])
    FH = '( ( abs ` f ) + ( abs ` h ) )'
    fh = linarith(w, Az, [es1, a1f, a2h, D(w, Az, 'leabsd', [fr_], 'f <_ ( abs ` f )'), D(w, Az, 'leabsd', [hr_], 'h <_ ( abs ` h )')], '%s <_ %s' % (ab(S1), FH), closure=cl,
                  atoms=[ab(S1), ab(I1z), ab(I2z), 'f', 'h', '( abs ` f )', '( abs ` h )'])
    lE = '( l x. %s )' % E3
    P1 = D(w, Az, 'lemul12ad', [cl.mem(ab(S1), 'RR'), cl.mem(FH, 'RR'), cl.mem(ab(G_), 'RR'), cl.mem(lE, 'RR'), cl.ge0(ab(S1)), cl.ge0(ab(G_)), fh, gl], '( %s x. %s ) <_ ( %s x. %s )' % (ab(S1), ab(G_), FH, lE))
    P2 = D(w, Az, 'lemul12ad', [rmr, cst(w, Az, '1re', '1 e. RR'), cl.mem('( %s / 2 )' % ab(H_), 'RR'), cl.mem('( %s / 2 )' % lE, 'RR'), rm0, cl.ge0('( %s / 2 )' % ab(H_)), rm1_,
                                linarith(w, Az, [hl], '( %s / 2 ) <_ ( %s / 2 )' % (ab(H_), lE), closure=cl, atoms=[ab(H_), lE])], '( %s x. ( %s / 2 ) ) <_ ( 1 x. ( %s / 2 ) )' % (RM, ab(H_), lE))
    dqb = linarith(w, Az, [boz, gl, D(w, Az, 'leabsd', [orr_], 'o <_ ( abs ` o )')], '%s <_ ( ( abs ` o ) + ( %s + %s ) )' % (ab(DQz), lE, ag1), closure=cl, atoms=[ab(DQz), ab(G_), lE, ag1, 'o', '( abs ` o )'])
    P3 = D(w, Az, 'lemul12ad', [rmr, cst(w, Az, '1re', '1 e. RR'), cl.mem(ab(DQz), 'RR'), cl.mem('( ( abs ` o ) + ( %s + %s ) )' % (lE, ag1), 'RR'), rm0, cl.ge0(ab(DQz)), rm1_, dqb],
           '( %s x. %s ) <_ ( 1 x. ( ( abs ` o ) + ( %s + %s ) ) )' % (RM, ab(DQz), lE, ag1))
    K0 = '( ( abs ` o ) + ( %s + 1 ) )' % ag1
    P4 = D(w, Az, 'mpbid', [D(w, Az, 'lemul2ad', [cst(w, Az, '1re', '1 e. RR'), cl.mem(E3, 'RR'), cl.mem(K0, 'RR'), cl.ge0(K0), e31], '( %s x. 1 ) <_ ( %s x. %s )' % (K0, K0, E3)),
                            D(w, Az, 'breq1d', [D(w, Az, 'mulridd', [cl.mem(K0, 'CC')], '( %s x. 1 ) = %s' % (K0, K0))], '( ( %s x. 1 ) <_ ( %s x. %s ) <-> %s <_ ( %s x. %s ) )' % (K0, K0, E3, K0, K0, E3))],
            '%s <_ ( %s x. %s )' % (K0, K0, E3))
    cc_ = '( ( ( %s x. l ) + ( 2 x. l ) ) + %s )' % (FH, K0)
    import lin as _lin
    _lin.MAXDEG = 6
    AF = ab(FB)
    cl.have(AF, 'RR', D(w, Az, 'abscld', [D(w, Az, 'addcld', [D(w, Az, 'subcld', [t1c, t2c], '( %s - %s ) e. CC' % (T1, T2)), t3c], '%s e. CC' % FB)], '%s e. RR' % AF))
    cl.have(ab('( %s - %s )' % (T1, T2)), 'RR', D(w, Az, 'abscld', [D(w, Az, 'subcld', [t1c, t2c], '( %s - %s ) e. CC' % (T1, T2))], '%s e. RR' % ab('( %s - %s )' % (T1, T2))))
    for T_, tc_ in ((T1, t1c), (T2, t2c), (T3, t3c)):
        cl.have(ab(T_), 'RR', D(w, Az, 'abscld', [tc_], '%s e. RR' % ab(T_)))
    FL = '( %s x. %s )' % (FH, lE); KE = '( %s x. %s )' % (K0, E3)
    B1 = D(w, Az, 'eqbrtrd', [at1, P1], '%s <_ %s' % (ab(T1), FL))
    B2 = D(w, Az, 'eqbrtrd', [at2, P2], '%s <_ ( 1 x. ( %s / 2 ) )' % (ab(T2), lE))
    B3 = D(w, Az, 'eqbrtrd', [at3, P3], '%s <_ ( 1 x. ( ( abs ` o ) + ( %s + %s ) ) )' % (ab(T3), lE, ag1))
    for t_ in (FL, KE, lE):
        cl.atom(t_)
    cl.have(FL, 'RR', cl.mem(FL, 'RR')); cl.have(KE, 'RR', cl.mem(KE, 'RR'))
    ce = chain(w, Az, ['( %s x. %s )' % (cc_, E3), '( ( ( ( %s x. l ) + ( 2 x. l ) ) x. %s ) + %s )' % (FH, E3, KE),
                       '( ( ( ( %s x. l ) x. %s ) + ( ( 2 x. l ) x. %s ) ) + %s )' % (FH, E3, E3, KE), '( ( %s + ( 2 x. %s ) ) + %s )' % (FL, lE, KE)],
               [D(w, Az, 'adddird', [cl.mem('( ( %s x. l ) + ( 2 x. l ) )' % FH, 'CC'), cl.mem(K0, 'CC'), cl.mem(E3, 'CC')], '( %s x. %s ) = ( ( ( ( %s x. l ) + ( 2 x. l ) ) x. %s ) + %s )' % (cc_, E3, FH, E3, KE)),
                D(w, Az, 'oveq1d', [D(w, Az, 'adddird', [cl.mem('( %s x. l )' % FH, 'CC'), cl.mem('( 2 x. l )', 'CC'), cl.mem(E3, 'CC')],
                                      '( ( ( %s x. l ) + ( 2 x. l ) ) x. %s ) = ( ( ( %s x. l ) x. %s ) + ( ( 2 x. l ) x. %s ) )' % (FH, E3, FH, E3, E3))],
                  '( ( ( ( %s x. l ) + ( 2 x. l ) ) x. %s ) + %s ) = ( ( ( ( %s x. l ) x. %s ) + ( ( 2 x. l ) x. %s ) ) + %s )' % (FH, E3, KE, FH, E3, E3, KE)),
                D(w, Az, 'oveq1d', [D(w, Az, 'oveq12d', [D(w, Az, 'mulassd', [cl.mem(FH, 'CC'), cl.mem('l', 'CC'), cl.mem(E3, 'CC')], '( ( %s x. l ) x. %s ) = %s' % (FH, E3, FL)),
                                                       D(w, Az, 'mulassd', [cl.mem('2', 'CC'), cl.mem('l', 'CC'), cl.mem(E3, 'CC')], '( ( 2 x. l ) x. %s ) = ( 2 x. %s )' % (E3, lE))],
                                      '( ( ( %s x. l ) x. %s ) + ( ( 2 x. l ) x. %s ) ) = ( %s + ( 2 x. %s ) )' % (FH, E3, E3, FL, lE))],
                  '( ( ( ( %s x. l ) x. %s ) + ( ( 2 x. l ) x. %s ) ) + %s ) = ( ( %s + ( 2 x. %s ) ) + %s )' % (FH, E3, E3, KE, FL, lE, KE))])
    bnd0 = linarith(w, Az, [tri1, tri2, B1, B2, B3, P4, cl.ge0(lE)], '%s <_ ( ( %s + ( 2 x. %s ) ) + %s )' % (AF, FL, lE, KE), closure=cl,
                    atoms=[AF, ab('( %s - %s )' % (T1, T2)), ab(T1), ab(T2), ab(T3), FL, lE, KE, '( abs ` o )', ag1])
    bnd = D(w, Az, 'breqtrrd', [bnd0, ce], '%s <_ ( %s x. %s )' % (AF, cc_, E3))
    GBODY = lambda c: 'A. z e. %s ( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (STR, FC, c, E3)
    fb = D(w, Az, 'eqbrtrd', [D(w, Az, 'fveq2d', [fcz], '( abs ` ( %s ` z ) ) = %s' % (FC, AF)), bnd], '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (FC, cc_, E3))
    ral = D(w, A4, 'ralrimiva', [fb], GBODY(cc_))
    g1c4 = value_facts(w, A4, '1', cst(w, A4, 'ax-1cn', '1 e. CC'), uo_one(w, A4), B, lambda st, f: lift(w, st, A4))['g1c']
    cl4 = Closure(w, A4, {'f': ('RR', fr), 'h': ('RR', hr), 'l': ('RR+', lrp), 'o': ('RR', orr),
                          ag1: [('RR', D(w, A4, 'abscld', [g1c4], '%s e. RR' % ag1)), ('ge0', D(w, A4, 'absge0d', [g1c4], '0 <_ %s' % ag1))]})
    crp = cl4.mem(cc_, 'RR+')
    sub = w.s([w.s([w.s([], 'oveq1', '( c = %s -> ( c x. %s ) = ( %s x. %s ) )' % (cc_, E3, cc_, E3))], 'breq2d', '( c = %s -> ( ( abs ` ( %s ` z ) ) <_ ( c x. %s ) <-> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )' % (cc_, FC, E3, FC, cc_, E3))],
              'ralbidv', '( c = %s -> ( %s <-> %s ) )' % (cc_, GBODY('c'), GBODY(cc_)))
    G4 = 'E. c e. RR+ %s' % GBODY('c')
    g4 = w.s([crp, ral, w.s([sub], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> %s )' % (cc_, GBODY(cc_), G4))], 'syl2anc', '( %s -> %s )' % (A4, G4))
    g3 = peel(w, A3, 'o', 'RR', DQB('o'), G4, g4, lift(w, exo, A3))
    g2 = peel(w, A2, 'l', 'RR+', HGB('l'), G4, g3, lift(w, exl, A2))
    g1_ = peel(w, A1, 'h', 'RR', ILB(CYBM, 'h'), G4, g2, lift(w, exh, A1))
    g0 = peel(w, A, 'f', 'RR', ILB(CYM, 'f'), G4, g1_, exf)
    w.qed([g0], 'idi', SE['zl3fgr'])
    goe(w)


# ---------------------------------------------------------------- zl3pc
if wante('zl3pc', MAIN):
    w = W('zl3pc', 'PCONT at a primitive character: the continuation ` F ` on ` U = Re^-1 ( -1 , 3 ) ` with ` T = EPS ` , ` Q = QQ ( a ) ` and ` B = 3 ` satisfies the five parts of ~ zl2cvxe .')
    A, Cc = ante_e('zl3pc')
    pr = D(w, A, 'simpl', [], PR); re_ = D(w, A, 'simpr', [], 'R = %s' % RM)
    B = pr_base(w, A, pr)
    sub = lambda txt, c: LE.tsub(txt, {'F': FC, 'U': UO, 'K': c, 'B': '3', 'T': EPS, 'Q': LE.QQ(PAR)})
    PC = lambda c: sub(LE.PCM, c)
    assert Cc.strip() in ('E. c e. RR+ %s' % PC('c'), '( E. c e. RR+ %s )' % PC('c'))
    hol = D(w, A, 'syl', [pr, w.inst('zl3fch')], HOL(FC, UO))
    Az = '( %s /\\ z e. %s )' % (A, STR)
    zin = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, STR))
    zst = D(w, Az, 'sylib', [zin, w.inst('elstr')], '( z e. CC /\\ ( Re ` z ) e. ( -u ( 1 / 2 ) [,] 2 ) )')
    zre = D(w, Az, 'mpbid', [D(w, Az, 'simprd', [zst], '( Re ` z ) e. ( -u ( 1 / 2 ) [,] 2 )'),
                             D(w, Az, 'syl2anc', [Closure(w, Az, {}).mem('-u ( 1 / 2 )', 'RR'), cst(w, Az, '2re', '2 e. RR'), w.inst('elicc2')],
                               '( ( Re ` z ) e. ( -u ( 1 / 2 ) [,] 2 ) <-> ( ( Re ` z ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 2 ) )')],
          '( ( Re ` z ) e. RR /\\ -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 2 )')
    clz = Closure(w, Az, {'( Re ` z )': ('RR', D(w, Az, 'simp1d', [zre], '( Re ` z ) e. RR'))})
    zU = in_uo(w, Az, 'z', D(w, Az, 'simpld', [zst], 'z e. CC'), linarith(w, Az, [D(w, Az, 'simp2d', [zre], '-u ( 1 / 2 ) <_ ( Re ` z )')], '-u 1 < ( Re ` z )', closure=clz),
               linarith(w, Az, [D(w, Az, 'simp3d', [zre], '( Re ` z ) <_ 2')], '( Re ` z ) < 3', closure=clz))
    sss = D(w, A, 'ssrdv', [D(w, A, 'ex', [zU], '( z e. %s -> z e. %s )' % (STR, UO))], '%s C_ %s' % (STR, UO))
    H3 = D(w, A, '3jca', [D(w, A, 'simpld', [hol], '%s e. ( %s -cn-> CC )' % (FC, UO)), D(w, A, 'simprd', [hol], '%s C_ dom ( CC _D %s )' % (UO, FC)), sss],
           '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) /\\ %s C_ %s )' % (FC, UO, UO, FC, STR, UO))
    SER = LE.tsub(L.split_imp(SE['zl3sery'])[1], {})
    ser = D(w, A, 'syl', [w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('zl3sery')], SER)
    FE = L.split_imp(SE['zl3fey'])[1]
    fey = D(w, A, 'syl', [w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('zl3fey')], FE)
    ec = eps_cl(w, A, B['ch'], B['pp'])
    ae = D(w, A, 'syl2anc', [B['ch'], D(w, A, 'jca', [D(w, A, 'simprd', [pr], '( M DChrCond Y ) = M'), par_nn0(w, A, B['pp'], PAR)], '( ( M DChrCond Y ) = M /\\ %s e. NN0 )' % PAR), w.inst('zl2rtn')],
           '( abs ` %s ) = 1' % EPS)
    QBN = L.split_imp(LE.Z3.STATEMENTS['zl3qbnd'])[1]
    qbn = D(w, A, 'syl', [B['pp'], w.inst('zl3qbnd')], LE.tsub(QBN, {'P': PAR}))
    GB = lambda c: '( ( %s e. RR+ /\\ 3 e. RR /\\ 0 <_ 3 ) /\\ A. z e. %s ( abs ` ( %s ` z ) ) <_ ( %s x. ( exp ` ( 3 x. ( abs ` ( Im ` z ) ) ) ) ) )' % (c, STR, FC, c)
    BND = lambda c: 'A. z e. %s ( abs ` ( %s ` z ) ) <_ ( %s x. ( exp ` ( 3 x. ( abs ` ( Im ` z ) ) ) ) )' % (STR, FC, c)
    Ac = '( %s /\\ c e. RR+ )' % A
    Acb = '( %s /\\ %s )' % (Ac, BND('c'))
    L_ = lambda st: lift(w, st, Acb)
    gb = D(w, Acb, 'jca', [D(w, Acb, '3jca', [lift(w, w.s([], 'simpr', '( %s -> c e. RR+ )' % Ac), Acb), cst(w, Acb, '3re', '3 e. RR'), cst(w, Acb, '0le3' if False else 'idi', '') if False else
                                           D(w, Acb, 'ltled', [cst(w, Acb, '0re', '0 e. RR'), cst(w, Acb, '3re', '3 e. RR'), cst(w, Acb, '3pos', '0 < 3')], '0 <_ 3')], '( c e. RR+ /\\ 3 e. RR /\\ 0 <_ 3 )'),
                           w.s([], 'simpr', '( %s -> %s )' % (Acb, BND('c')))], GB('c'))
    part = PC('c')
    tail = D(w, Acb, 'jca', [L_(ser), D(w, Acb, 'jca', [D(w, Acb, 'jca', [L_(ec), L_(ae)], '( %s e. CC /\\ ( abs ` %s ) = 1 )' % (EPS, EPS)), D(w, Acb, 'jca', [L_(fey), L_(qbn)],
                                                                                                                                                 '( %s /\\ %s )' % (FE, LE.tsub(QBN, {'P': PAR})))],
                                                    '( ( %s e. CC /\\ ( abs ` %s ) = 1 ) /\\ ( %s /\\ %s ) )' % (EPS, EPS, FE, LE.tsub(QBN, {'P': PAR})))],
                '( %s /\\ ( ( %s e. CC /\\ ( abs ` %s ) = 1 ) /\\ ( %s /\\ %s ) ) )' % (SER, EPS, EPS, FE, LE.tsub(QBN, {'P': PAR})))
    full = D(w, Acb, 'jca', [D(w, Acb, 'jca', [L_(H3), gb], '( ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) /\\ %s C_ %s ) /\\ %s )' % (FC, UO, UO, FC, STR, UO, GB('c'))), tail], part)
    imp = w.s([full], 'ex', '( %s -> ( %s -> %s ) )' % (Ac, BND('c'), part))
    rx = D(w, A, 'reximdva', [imp], '( E. c e. RR+ %s -> E. c e. RR+ %s )' % (BND('c'), part))
    fgr = D(w, A, 'syl', [pr, w.inst('zl3fgr')], 'E. c e. RR+ %s' % BND('c'))
    w.qed([D(w, A, 'mpd', [fgr, rx], 'E. c e. RR+ %s' % part)], 'idi', SE['zl3pc'])
    goe(w)


MC_, YP_, RP_ = LE.MC, LE.YP, LE.RP
NXS = LE.Z1.NX
TON = lambda txt: LE.tsub(txt, {'M': MC_, 'Y': YP_, 'R': RP_})


def pc_N(w, A):
    """( A -> E. c e. RR+ PCONT[ ... ] ) for A = NX ; returns (step, PCN(c))"""
    brg = w.s([], 'zl3brg', SE['zl3brg'])
    PCa = L.split_imp(SE['zl3pc'])
    pcn = w.s([], 'zl3pc', '( %s -> %s )' % (TON(PCa[0]), TON(PCa[1])))
    st = w.s([brg, pcn], 'syl', '( %s -> %s )' % (NXS, TON(PCa[1])))
    body = TON(PCa[1])
    assert body.startswith('E. c e. RR+ ') or body.startswith('( E. c e. RR+ ')
    PCN = body[len('E. c e. RR+ '):] if body.startswith('E. c') else body[len('( E. c e. RR+ '):-2]
    Z2PC = LE.tsub(Z2S_PCONT, {'F': TON(FC), 'U': UO, 'K': 'c', 'B': '3', 'T': TON(EPS), 'Q': TON(LE.QQ(PAR))})
    assert PCN == Z2PC, 'PCONT mismatch'
    return st, PCN


import zl2lib as _Z2b
Z2S_PCONT = _Z2b.PCONT

# ---------------------------------------------------------------- zl3cvxh
if wante('zl3cvxh', MAIN):
    w = W('zl3cvxh', 'The convexity bound ` CVXH ` of ZL1 for every Dirichlet character ( ~ zl2cvxe with PCONT discharged by ~ zl3pc at the conductor and the primitive character, ~ zl3brg ).')
    A, Cc = ante_e('zl3cvxh')
    assert A == NXS
    st, PCN = pc_N(w, A)
    cv = w.s([], 'zl2cvxe', '( ( %s /\\ %s ) -> %s )' % (NXS, PCN, Cc))
    s1 = w.s([w.s([cv], 'ex', '( %s -> ( %s -> %s ) )' % (NXS, PCN, Cc))], 'adantr', '( ( %s /\\ c e. RR+ ) -> ( %s -> %s ) )' % (NXS, PCN, Cc))
    s2 = D(w, A, 'rexlimdva', [s1], '( E. c e. RR+ %s -> %s )' % (PCN, Cc))
    w.qed([D(w, A, 'mpd', [st, s2], Cc)], 'idi', SE['zl3cvxh'])
    goe(w)

# ---------------------------------------------------------------- zl3lfe
if wante('zl3lfe', MAIN):
    w = W('zl3lfe', 'For T21: ` ( N DChrLF X ) ( S ) = ( ( S - 1 ) F ( S ) + R ) PF ( S ) ` on ` 1 / 200 <_ Re S <_ 2 ` at the continuation ` F ` of the primitive character ( ~ zl2lfe with PCONT discharged, Lean ` LFunction_eq_primitive_mul_prod ` ).')
    A, Cc = ante_e('zl3lfe')
    nx = D(w, A, 'simpl', [], NXS); srng = D(w, A, 'simpr', [], '( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) )')
    st, PCN = pc_N(w, NXS)
    LF_ = L.split_imp(Z2S['zl2lfe'])
    lfe = w.s([], 'zl2lfe', LE.tsub(Z2S['zl2lfe'], {'F': TON(FC), 'U': UO, 'K': 'c', 'B': '3', 'T': TON(EPS), 'Q': TON(LE.QQ(PAR))}))
    ANT = '( ( %s /\\ %s ) /\\ ( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) ) )' % (NXS, PCN)
    assert LE.tsub(Z2S['zl2lfe'], {'F': TON(FC), 'U': UO, 'K': 'c', 'B': '3', 'T': TON(EPS), 'Q': TON(LE.QQ(PAR))}) == '( %s -> %s )' % (ANT, Cc)
    Ac = '( %s /\\ c e. RR+ )' % A
    s0 = D(w, '( %s /\\ %s )' % (Ac, PCN), 'syl', [D(w, '( %s /\\ %s )' % (Ac, PCN), 'jca', [D(w, '( %s /\\ %s )' % (Ac, PCN), 'jca', [lift(w, nx, '( %s /\\ %s )' % (Ac, PCN)), w.s([], 'simpr', '( ( %s /\\ %s ) -> %s )' % (Ac, PCN, PCN))],
                                                                                          '( %s /\\ %s )' % (NXS, PCN)), lift(w, srng, '( %s /\\ %s )' % (Ac, PCN))], ANT), lfe], Cc)
    s1 = w.s([s0], 'ex', '( %s -> ( %s -> %s ) )' % (Ac, PCN, Cc))
    s2 = D(w, A, 'rexlimdva', [s1], '( E. c e. RR+ %s -> %s )' % (PCN, Cc))
    w.qed([D(w, A, 'mpd', [D(w, A, 'syl', [nx, st], 'E. c e. RR+ %s' % PCN), s2], Cc)], 'idi', SE['zl3lfe'])
    goe(w)


# ---------------------------------------------------------------- zl3dlbz
if wante('zl3dlbz', MAIN):
    w = W('zl3dlbz', '~ zl1dlbz without its hypothesis ` CVXH ` , which ~ zl3cvxh now proves for every Dirichlet character (Lean ` detector_lower_bound_of_zero_all ` ).')
    Z1 = LE.Z1
    Z6 = Z1.Z6
    A, Cc = ante_e('zl3dlbz')
    P1 = '( %s /\\ %s )' % (Z6.HZD3, Z1.NX)
    P2 = '( ( %s /\\ S =/= 1 ) /\\ %s )' % (Z6.SRNG, Z6.HDN)
    LF0 = '( %s ` S ) = 0' % Z1.LF
    P3 = '( %s /\\ ( %s = %s -> %s <_ ( abs ` ( Im ` S ) ) ) )' % (Z6.TRNG, Z1.CX, Z1.PRN, Z6.LAM60)
    A_ = '( ( %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) /\\ %s )' % (P1, P2, Z6.T1, LF0, P3)
    assert A == A_, (A[:200], A_[:200])
    p1 = D(w, A, 'simpll', [], P1); p2 = D(w, A, 'simplrl' if False else 'idi', [], '') if False else D(w, A, 'simpld', [D(w, A, 'simplr', [], '( %s /\\ ( %s /\\ %s ) )' % (P2, Z6.T1, LF0))], P2)
    tl = D(w, A, 'simprd', [D(w, A, 'simplr', [], '( %s /\\ ( %s /\\ %s ) )' % (P2, Z6.T1, LF0))], '( %s /\\ %s )' % (Z6.T1, LF0))
    t1 = D(w, A, 'simpld', [tl], Z6.T1); lf0 = D(w, A, 'simprd', [tl], LF0)
    p3 = D(w, A, 'simpr', [], P3)
    nx = D(w, A, 'simprd', [p1], Z1.NX)
    cv = D(w, A, 'syl', [nx, w.inst('zl3cvxh')], Z1.CVXHX)
    ZA = Z1.ZA
    full = D(w, A, 'jca', [D(w, A, 'jca', [p1, D(w, A, 'jca', [p2, D(w, A, 'jca', [t1, D(w, A, 'jca', [cv, lf0], '( %s /\\ %s )' % (Z1.CVXHX, LF0))], '( %s /\\ ( %s /\\ %s ) )' % (Z6.T1, Z1.CVXHX, LF0))],
                                                               '( %s /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (P2, Z6.T1, Z1.CVXHX, LF0))], '( %s /\\ ( %s /\\ ( %s /\\ ( %s /\\ %s ) ) ) )' % (P1, P2, Z6.T1, Z1.CVXHX, LF0)), p3], ZA)
    w.qed([D(w, A, 'syl', [full, w.inst('zl1dlbz')], Cc)], 'idi', SE['zl3dlbz'])
    goe(w)
