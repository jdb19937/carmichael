"""Sortie T21b: t21card (badSet_card_le)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *

Z = Z191
LXX = '( log ` X )'
RL = '( R / %s )' % LXX


def gen_card():
    w = W('t21card', 'The exceptional set at level ` 191 / 900 ` : at most ` c_2 ( nu ) e ^ ( ( 191 / 900 ) c_3 rho ) ` conductors, uniformly in ` X ` (Lean ` badSet_card_le ` ; ~ cmbad at ` S = 1 - R / log X ` , ` Z = X ^ ( 191 / 900 ) ` ).')
    A0, concl = split_imp(SB['t21card'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    rp = u['R e. RR+']; vr = u['V e. RR']; v1 = u['1 <_ V']; xr = u['X e. RR']; x1 = u['1 < X']; z2 = u['2 <_ %s' % Z]; t39 = u['( ; 3 9 / ; 4 0 ) <_ %s' % TAU]
    rr = s([rp], 'rpred', 'R e. RR')
    x0 = lin.linarith(w, A0, [x1], '0 < X', leaves={'X': xr})
    xp = s([xr, x0], 'elrpd', 'X e. RR+')
    lp = s([s([xr, x1], 'loggt0d' if False else 'x', 'x')], 'x', 'x') if False else None
    lx0 = s([s([s([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+'), xp], 'jca', '( 1 e. RR+ /\\ X e. RR+ )'), w.inst('logltb')], 'syl', '( 1 < X <-> ( log ` 1 ) < %s )' % LXX)
    lg = s([x1, lx0], 'mpbid', '( log ` 1 ) < %s' % LXX)
    lg0 = s([lg, s([w.s([], 'log1', '( log ` 1 ) = 0')], 'a1i', '( log ` 1 ) = 0')], 'x', 'x') if False else None
    lpos = s([s([s([w.s([], 'log1', '( log ` 1 ) = 0')], 'a1i', '( log ` 1 ) = 0')], 'eqcomd', '0 = ( log ` 1 )'), lg], 'eqbrtrd', '0 < %s' % LXX)
    lr = s([xp], 'relogcld', '%s e. RR' % LXX)
    lrp = s([lr, lpos], 'elrpd', '%s e. RR+' % LXX)
    rlr = s([rr, lrp], 'rerpdivcld', '%s e. RR' % RL)
    rl0 = s([rr, lrp, s([rp], 'rpge0d', '0 <_ R')], 'divge0d', '0 <_ %s' % RL)
    one = s([], '1red', '1 e. RR')
    taur = s([one, rlr], 'resubcld', '%s e. RR' % TAU)
    t1 = lin.linarith(w, A0, [rl0], '%s <_ 1' % TAU, leaves={RL: rlr})
    zr = s([xp, s([num.real(w, F191)], 'a1i', '%s e. RR' % F191)], 'rpcxpcld', '%s e. RR+' % Z)
    zrr = s([zr], 'rpred', '%s e. RR' % Z)
    # D finite, members bad
    BD = BAD(Z, TAU, 'V')
    FZ = '( 2 ... ( |_ ` %s ) )' % Z
    dfin = s([s([w.s([], 'fzfi', '%s e. Fin' % FZ)], 'a1i', '%s e. Fin' % FZ), s([w.s([], 'ssrab2', '%s C_ %s' % (BD, FZ))], 'a1i', '%s C_ %s' % (BD, FZ))], 'ssfid', '%s e. Fin' % BD)
    bce = lambda e: '%s =/= (/)' % BC(TAU, 'V', e)
    ce, _ = w.wcongr(bce('e'), {'e': 'm'}, 'e = m', {'e': w.s([], 'id', '( e = m -> e = m )')})
    ele = w.s([ce], 'elrab', '( m e. %s <-> ( m e. %s /\\ %s ) )' % (BD, FZ, bce('m')))
    Am = '( %s /\\ m e. %s )' % (A0, BD)
    sm = S_(w, Am)
    mm = sm([sm([], 'simpr', 'm e. %s' % BD), ele], 'sylib', '( m e. %s /\\ %s )' % (FZ, bce('m')))
    mfz = sm([mm], 'simpld', 'm e. %s' % FZ)
    mb = sm([mm], 'simprd', bce('m'))
    mz = sm([mfz], 'elfzelzd', 'm e. ZZ')
    m2 = sm([mfz], 'elfzle1', '2 <_ m') if False else sm([mfz, w.inst('elfzle1')], 'syl', '2 <_ m')
    mf = sm([mfz, w.inst('elfzle2')], 'syl', 'm <_ ( |_ ` %s )' % Z)
    zrm = lift(w, zrr, Am)
    mzl = sm([mf, sm([sm([zrm, mz], 'jca', '( %s e. RR /\\ m e. ZZ )' % Z), w.inst('flge')], 'syl', '( m <_ %s <-> m <_ ( |_ ` %s ) )' % (Z, Z))], 'mpbird', 'm <_ %s' % Z)
    m0 = lin.linarith(w, Am, [m2], '0 <_ m', leaves={'m': sm([mz], 'zred', 'm e. RR')})
    mn0 = sm([sm([mz, m0], 'jca', '( m e. ZZ /\\ 0 <_ m )'), w.inst('elnn0z')], 'sylibr', 'm e. NN0')
    body = '( ( m e. NN0 /\\ 2 <_ m ) /\\ ( m <_ %s /\\ %s ) )' % (Z, bce('m'))
    bm = sm([sm([mn0, m2], 'jca', '( m e. NN0 /\\ 2 <_ m )'), sm([mzl, mb], 'jca', '( m <_ %s /\\ %s )' % (Z, bce('m')))], 'jca', body)
    ral = s([bm], 'ralrimiva', 'A. m e. %s %s' % (BD, body))
    CB = '( ( %s x. ( V + 2 ) ) x. ( %s ^c ( %s x. ( 1 - %s ) ) ) )' % (C2T, Z, C13, TAU)
    cb = ap(w, A0, [taur, vr, zrr, t39, t1, v1, z2, dfin, ral], 'cmbad', '( # ` %s ) <_ %s' % (BD, CB))
    # Z ^c ( C3 ( 1 - tau ) ) = exp ( ( 191/900 ) ( C3 R ) )
    lc = s([lr], 'recnd', '%s e. CC' % LXX); ln0 = s([lrp], 'rpne0d', '%s =/= 0' % LXX)
    rc = s([rr], 'recnd', 'R e. CC'); rlc = s([rlr], 'recnd', '%s e. CC' % RL)
    one_t = s([s([], '1cnd', '1 e. CC'), rlc], 'nncand', '( 1 - %s ) = %s' % (TAU, RL))
    c13c = s([num.real(w, C13)], 'a1i', '%s e. RR' % C13)
    c13 = s([c13c], 'recnd', '%s e. CC' % C13)
    f191 = s([num.real(w, F191)], 'a1i', '%s e. RR' % F191)
    f191c = s([f191], 'recnd', '%s e. CC' % F191)
    e1 = s([s([one_t], 'oveq2d', '( %s x. ( 1 - %s ) ) = ( %s x. %s )' % (C13, TAU, C13, RL))], 'oveq2d', '( %s ^c ( %s x. ( 1 - %s ) ) ) = ( %s ^c ( %s x. %s ) )' % (Z, C13, TAU, Z, C13, RL))
    cr = s([c13, rlc], 'mulcld', '( %s x. %s ) e. CC' % (C13, RL))
    e2 = s([s([xp, f191, cr], 'x', 'x')], 'x', 'x') if False else None
    CM = '( ( ( X e. RR+ /\\ %s e. RR /\\ ( %s x. %s ) e. CC ) ) -> ( X ^c ( %s x. ( %s x. %s ) ) ) = ( %s ^c ( %s x. %s ) ) )' % (F191, C13, RL, F191, C13, RL, Z, C13, RL)
    e2 = s([s([xp, f191, cr], '3jca', '( X e. RR+ /\\ %s e. RR /\\ ( %s x. %s ) e. CC )' % (F191, C13, RL)), w.inst('cxpmul')], 'syl', '( X ^c ( %s x. ( %s x. %s ) ) ) = ( %s ^c ( %s x. %s ) )' % (F191, C13, RL, Z, C13, RL))
    EXP = '( %s x. ( %s x. %s ) )' % (F191, C13, RL)
    expc = s([f191c, cr], 'mulcld', '%s e. CC' % EXP)
    e3 = s([s([xp], 'rpcnd', 'X e. CC'), s([xp], 'rpne0d', 'X =/= 0'), expc], 'cxpefd', '( X ^c %s ) = ( exp ` ( %s x. %s ) )' % (EXP, EXP, LXX))
    # ( EXP x. L ) = ( F191 x. ( C13 x. R ) )
    a1 = s([f191c, cr, lc], 'mulassd', '( %s x. %s ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (EXP, LXX, F191, C13, RL, LXX))
    a2 = s([c13, rlc, lc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (C13, RL, LXX, C13, RL, LXX))
    a3 = s([rc, lc, ln0], 'divcan1d', '( %s x. %s ) = R' % (RL, LXX))
    a4 = s([a2, s([a3], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. R )' % (C13, RL, LXX, C13))], 'eqtrd', '( ( %s x. %s ) x. %s ) = ( %s x. R )' % (C13, RL, LXX, C13))
    a5 = s([a1, s([a4], 'oveq2d', '( %s x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( %s x. R ) )' % (F191, C13, RL, LXX, F191, C13))], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. R ) )' % (EXP, LXX, F191, C13))
    e4 = s([e3, s([a5], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. ( %s x. R ) ) )' % (EXP, LXX, F191, C13))], 'eqtrd', '( X ^c %s ) = ( exp ` ( %s x. ( %s x. R ) ) )' % (EXP, F191, C13))
    zc = s([e1, s([s([e2], 'eqcomd', '( %s ^c ( %s x. %s ) ) = ( X ^c %s )' % (Z, C13, RL, EXP)), e4], 'eqtrd', '( %s ^c ( %s x. %s ) ) = ( exp ` ( %s x. ( %s x. R ) ) )' % (Z, C13, RL, F191, C13))], 'eqtrd',
           '( %s ^c ( %s x. ( 1 - %s ) ) ) = ( exp ` ( %s x. ( %s x. R ) ) )' % (Z, C13, TAU, F191, C13))
    fin = s([cb, s([zc], 'oveq2d', '%s = ( ( %s x. ( V + 2 ) ) x. ( exp ` ( %s x. ( %s x. R ) ) ) )' % (CB, C2T, F191, C13))], 'breqtrd', concl)
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21card']))
    return go(w)


if __name__ == '__main__':
    gen_card()
