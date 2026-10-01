"""Sortie C9: bounds for abs prod_ q e. S ( U - q ) ^ ( O ` q ) (fprodlbe, fprodube)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from cl import lift
import congr as _cg
from c9_freeze import S as FS

PH0 = '( S e. Fin /\\ S C_ CC /\\ O : S --> NN0 )'
BT = '( exp ` ( ( O ` q ) x. ( log ` R ) ) )'
TQ = '( ( U - q ) ^ ( O ` q ) )'
PRU = '( abs ` prod_ q e. S %s )' % TQ
EXS = '( exp ` ( sum_ q e. S ( O ` q ) x. ( log ` R ) ) )'


def gen(lower):
    lab = 'fprodlbe' if lower else 'fprodube'
    txt = ('A lower bound ` R ` on the distances from ` U ` to the points of ` S ` gives ` R ^ sum O <_ abs prod ( U - q ) ^ ( O ` q ) ` , written with ` exp ` and ` log ` .'
           if lower else
           'An upper bound ` R ` on the distances from ` U ` to the points of ` S ` gives ` abs prod ( U - q ) ^ ( O ` q ) <_ R ^ sum O ` , written with ` exp ` and ` log ` .')
    w = W(lab, txt)
    HJ = 'A. j e. S R <_ ( abs ` ( U - j ) )' if lower else 'A. j e. S ( abs ` ( U - j ) ) <_ R'
    HQ = 'R <_ ( abs ` ( U - q ) )' if lower else '( abs ` ( U - q ) ) <_ R'
    A0 = '( %s /\\ ( U e. CC /\\ R e. RR+ /\\ %s ) )' % (PH0, HJ)
    h0 = w.s([], 'simpl', '( %s -> %s )' % (A0, PH0))
    sfin = w.s([h0, w.inst('simp1')], 'syl', '( %s -> S e. Fin )' % A0)
    scc = w.s([h0, w.inst('simp2')], 'syl', '( %s -> S C_ CC )' % A0)
    of = w.s([h0, w.inst('simp3')], 'syl', '( %s -> O : S --> NN0 )' % A0)
    uc = w.s([], 'simpr1', '( %s -> U e. CC )' % A0)
    rp = w.s([], 'simpr2', '( %s -> R e. RR+ )' % A0)
    hj = w.s([], 'simpr3', '( %s -> %s )' % (A0, HJ))
    Aq = '( %s /\\ q e. S )' % A0
    L = lambda st: lift(w, st, Aq)
    qS = w.s([], 'simpr', '( %s -> q e. S )' % Aq)
    qc = w.s([L(scc), qS], 'sseldd', '( %s -> q e. CC )' % Aq)
    oq = w.s([L(of), qS], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN0 )' % Aq)
    oz = w.s([oq], 'nn0zd', '( %s -> ( O ` q ) e. ZZ )' % Aq)
    ocq = w.s([oq], 'nn0cnd', '( %s -> ( O ` q ) e. CC )' % Aq)
    uq = w.s([L(uc), qc], 'subcld', '( %s -> ( U - q ) e. CC )' % Aq)
    auq = w.s([uq], 'abscld', '( %s -> ( abs ` ( U - q ) ) e. RR )' % Aq)
    rr = w.s([L(rp)], 'rpred', '( %s -> R e. RR )' % Aq)
    rge = w.s([L(rp)], 'rpge0d', '( %s -> 0 <_ R )' % Aq)
    lr = w.s([L(rp)], 'relogcld', '( %s -> ( log ` R ) e. RR )' % Aq)
    lrc = w.s([lr], 'recnd', '( %s -> ( log ` R ) e. CC )' % Aq)
    sub = w.s([w.s([w.s([], 'oveq2', '( j = q -> ( U - j ) = ( U - q ) )')], 'fveq2d', '( j = q -> ( abs ` ( U - j ) ) = ( abs ` ( U - q ) ) )')],
              'breq2d' if lower else 'breq1d', '( j = q -> ( %s <-> %s ) )' % (HJ.split(' ', 4)[4], HQ))
    hq = w.s([sub, L(hj), qS], 'rspcdva', '( %s -> %s )' % (Aq, HQ))
    rx = w.s([w.s([L(rp), oz], 'reexplogd' if False else 'jca', '( %s -> ( R e. RR+ /\\ ( O ` q ) e. ZZ ) )' % Aq), w.inst('reexplog')], 'syl',
             '( %s -> ( R ^ ( O ` q ) ) = %s )' % (Aq, BT))
    ae = w.s([uq, oq], 'absexpd', '( %s -> ( abs ` %s ) = ( ( abs ` ( U - q ) ) ^ ( O ` q ) ) )' % (Aq, TQ))
    if lower:
        le = w.s([w.s([w.s([rr, auq, oq], '3jca', '( %s -> ( R e. RR /\\ ( abs ` ( U - q ) ) e. RR /\\ ( O ` q ) e. NN0 ) )' % Aq),
                       w.s([rge, hq], 'jca', '( %s -> ( 0 <_ R /\\ %s ) )' % (Aq, HQ))], 'jca',
                      '( %s -> ( ( R e. RR /\\ ( abs ` ( U - q ) ) e. RR /\\ ( O ` q ) e. NN0 ) /\\ ( 0 <_ R /\\ %s ) ) )' % (Aq, HQ)), w.inst('leexp1a')], 'syl',
                '( %s -> ( R ^ ( O ` q ) ) <_ ( ( abs ` ( U - q ) ) ^ ( O ` q ) ) )' % Aq)
        tle = w.s([w.s([rx, le], 'eqbrtrrd', '( %s -> %s <_ ( ( abs ` ( U - q ) ) ^ ( O ` q ) ) )' % (Aq, BT)), ae], 'breqtrrd', '( %s -> %s <_ ( abs ` %s ) )' % (Aq, BT, TQ))
    else:
        ag = w.s([uq], 'absge0d', '( %s -> 0 <_ ( abs ` ( U - q ) ) )' % Aq)
        le = w.s([w.s([w.s([auq, rr, oq], '3jca', '( %s -> ( ( abs ` ( U - q ) ) e. RR /\\ R e. RR /\\ ( O ` q ) e. NN0 ) )' % Aq),
                       w.s([ag, hq], 'jca', '( %s -> ( 0 <_ ( abs ` ( U - q ) ) /\\ %s ) )' % (Aq, HQ))], 'jca',
                      '( %s -> ( ( ( abs ` ( U - q ) ) e. RR /\\ R e. RR /\\ ( O ` q ) e. NN0 ) /\\ ( 0 <_ ( abs ` ( U - q ) ) /\\ %s ) ) )' % (Aq, HQ)), w.inst('leexp1a')], 'syl',
                '( %s -> ( ( abs ` ( U - q ) ) ^ ( O ` q ) ) <_ ( R ^ ( O ` q ) ) )' % Aq)
        tle = w.s([w.s([ae, le], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( R ^ ( O ` q ) ) )' % (Aq, TQ)), rx], 'breqtrd', '( %s -> ( abs ` %s ) <_ %s )' % (Aq, TQ, BT))
    olr = w.s([w.s([oq], 'nn0red', '( %s -> ( O ` q ) e. RR )' % Aq), lr], 'remulcld', '( %s -> ( ( O ` q ) x. ( log ` R ) ) e. RR )' % Aq)
    bt = w.s([olr], 'reefcld', '( %s -> %s e. RR )' % (Aq, BT))
    bge = w.s([w.s([olr], 'rpefcld', '( %s -> %s e. RR+ )' % (Aq, BT))], 'rpge0d', '( %s -> 0 <_ %s )' % (Aq, BT))
    tq = w.s([uq, oq], 'expcld', '( %s -> %s e. CC )' % (Aq, TQ))
    at = w.s([tq], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Aq, TQ))
    nf = w.s([], 'nfv', 'F/ q %s' % A0)
    PB = 'prod_ q e. S %s' % BT
    PA = 'prod_ q e. S ( abs ` %s )' % TQ
    if lower:
        pl = w.s([nf, sfin, bt, bge, at, tle], 'fprodle', '( %s -> %s <_ %s )' % (A0, PB, PA))
    else:
        pl = w.s([nf, sfin, at, w.s([tq], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Aq, TQ)), bt, tle], 'fprodle', '( %s -> %s <_ %s )' % (A0, PA, PB))
    pab = w.s([sfin, tq], 'z5fprodabs', '( %s -> %s = %s )' % (A0, PRU, PA))
    # prod exp = exp sum
    MP = '( x e. S |-> ( ( O ` x ) x. ( log ` R ) ) )'
    fv, val = _cg.mptval(w, Aq, 'x', 'S', '( ( O ` x ) x. ( log ` R ) )', 'q', qS, gen=w.g)
    assert val == '( ( O ` q ) x. ( log ` R ) )', val
    fvc = w.s([fv, w.s([ocq, lrc], 'mulcld', '( %s -> %s e. CC )' % (Aq, val))], 'eqeltrd', '( %s -> ( %s ` q ) e. CC )' % (Aq, MP))
    pe = w.s([sfin, fvc], 'fprodefsumfi', '( %s -> prod_ q e. S ( exp ` ( %s ` q ) ) = ( exp ` sum_ q e. S ( %s ` q ) ) )' % (A0, MP, MP))
    p1 = w.s([w.s([fv], 'fveq2d', '( %s -> ( exp ` ( %s ` q ) ) = %s )' % (Aq, MP, BT))], 'prodeq2dv', '( %s -> prod_ q e. S ( exp ` ( %s ` q ) ) = %s )' % (A0, MP, PB))
    s1 = w.s([fv], 'sumeq2dv', '( %s -> sum_ q e. S ( %s ` q ) = sum_ q e. S ( ( O ` q ) x. ( log ` R ) ) )' % (A0, MP))
    lrc0 = w.s([w.s([rp], 'relogcld', '( %s -> ( log ` R ) e. RR )' % A0)], 'recnd', '( %s -> ( log ` R ) e. CC )' % A0)
    sm = w.s([sfin, lrc0, ocq],
             'fsummulc1', '( %s -> ( sum_ q e. S ( O ` q ) x. ( log ` R ) ) = sum_ q e. S ( ( O ` q ) x. ( log ` R ) ) )' % A0)
    s2 = w.s([w.s([s1, sm], 'eqtr4d', '( %s -> sum_ q e. S ( %s ` q ) = ( sum_ q e. S ( O ` q ) x. ( log ` R ) ) )' % (A0, MP))], 'fveq2d',
             '( %s -> ( exp ` sum_ q e. S ( %s ` q ) ) = %s )' % (A0, MP, EXS))
    pbe = w.s([w.s([p1, pe], 'eqtr3d', '( %s -> %s = ( exp ` sum_ q e. S ( %s ` q ) ) )' % (A0, PB, MP)), s2], 'eqtrd', '( %s -> %s = %s )' % (A0, PB, EXS))
    if lower:
        goal = '( %s -> %s <_ %s )' % (A0, EXS, PRU)
        w.qed([w.s([pbe, pl], 'eqbrtrrd', '( %s -> %s <_ %s )' % (A0, EXS, PA)), pab], 'breqtrrd', goal)
    else:
        goal = '( %s -> %s <_ %s )' % (A0, PRU, EXS)
        w.qed([w.s([pab, pl], 'eqbrtrd', '( %s -> %s <_ %s )' % (A0, PRU, PB)), pbe], 'breqtrd', goal)
    assert goal == FS[lab], (goal, FS[lab])
    return run8(w)


if __name__ == '__main__':
    gen(True)
    gen(False)
