"""Sortie CEN1: conjugation of k ^c S (cencjcx) and the product character value (cenprodv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen1lib import *
from cl import split_imp
from c9lib import top_and

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_cjcx():
    w = W('cencjcx', 'Conjugation of a power of a positive integer: ` * ( K ^c S ) = K ^c ( * S ) ` (Lean Census ` conj_natCast_cpow_mul_I ` , ` conj_natCast_cpow_ofReal ` , ` conj_natCast_cpow_neg_mul_I ` ).')
    A0, C0 = split_imp(S['cencjcx'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    kn = s([], 'simpl', 'K e. NN'); sc = s([], 'simpr', 'S e. CC')
    kc = s([kn], 'nncnd', 'K e. CC'); kne = s([kn], 'nnne0d', 'K =/= 0'); kr = s([kn], 'nnrpd', 'K e. RR+')
    lr = s([kr], 'relogcld', '( log ` K ) e. RR'); lc = s([lr], 'recnd', '( log ` K ) e. CC')
    LK = '( log ` K )'
    M1 = '( S x. %s )' % LK
    CS = '( * ` S )'
    M2 = '( %s x. %s )' % (CS, LK)
    e1 = s([kc, kne, sc], 'cxpefd', '( K ^c S ) = ( exp ` %s )' % M1)
    f1 = s([e1], 'fveq2d', '( * ` ( K ^c S ) ) = ( * ` ( exp ` %s ) )' % M1)
    mc = s([sc, lc], 'mulcld', '%s e. CC' % M1)
    g1 = s([mc, w.inst('efcj')], 'syl', '( exp ` ( * ` %s ) ) = ( * ` ( exp ` %s ) )' % (M1, M1))
    h1 = s([sc, lc], 'cjmuld', '( * ` %s ) = ( %s x. ( * ` %s ) )' % (M1, CS, LK))
    h2 = s([lr], 'cjred', '( * ` %s ) = %s' % (LK, LK))
    h3 = s([h2], 'oveq2d', '( %s x. ( * ` %s ) ) = %s' % (CS, LK, M2))
    h4 = s([h1, h3], 'eqtrd', '( * ` %s ) = %s' % (M1, M2))
    h5 = s([h4], 'fveq2d', '( exp ` ( * ` %s ) ) = ( exp ` %s )' % (M1, M2))
    csc = s([sc], 'cjcld', '%s e. CC' % CS)
    e2 = s([kc, kne, csc], 'cxpefd', '( K ^c %s ) = ( exp ` %s )' % (CS, M2))
    c1 = s([f1, g1], 'eqtr4d', '( * ` ( K ^c S ) ) = ( exp ` ( * ` %s ) )' % M1)
    c2 = s([c1, h5], 'eqtrd', '( * ` ( K ^c S ) ) = ( exp ` %s )' % M2)
    w.qed([c2, e2], 'eqtr4d', S['cencjcx'])
    return run(w)


def gen_prodv():
    w = W('cenprodv', 'The product character ` chi1 . conj chi2 ` mod ` U V ` at an integer ` A ` : ` chi1 ( A ) x. * chi2 ( A ) ` (Lean Census ` prodChar_apply ` ; ZF2 ~ dchrindmulval with the inverse character, ~ dchrinv ).')
    A0, C0 = split_imp(S['cenprodv'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); az = s([], 'simp3', 'A e. ZZ')
    un = s([h1], 'simpld', 'U e. NN'); vn = s([h1], 'simprd', 'V e. NN')
    xd = s([h2], 'simpld', 'X e. ( Base ` ( DChr ` U ) )'); zd = s([h2], 'simprd', 'Z e. ( Base ` ( DChr ` V ) )')
    GV = '( DChr ` V )'; DV = '( Base ` %s )' % GV; IV = '( invg ` %s )' % GV
    IZ = '( %s ` Z )' % IV
    grp = s([s([vn, w.inst('dchrabl')], 'syl', '%s e. Abel' % GV), w.inst('ablgrp')], 'syl', '%s e. Grp' % GV)
    izd = s([grp, zd, w.s([], 'eqid', '%s = %s' % (DV, DV)), w.s([], 'eqid', '%s = %s' % (IV, IV)), w.inst('grpinvcl')], 'syl2anc', '%s e. %s' % (IZ, DV)) if False else None
    eqd = w.s([], 'eqid', '%s = %s' % (DV, DV)); eqi = w.s([], 'eqid', '%s = %s' % (IV, IV))
    gi = w.s([eqd, eqi], 'grpinvcl', '( ( %s e. Grp /\\ Z e. %s ) -> %s e. %s )' % (GV, DV, IZ, DV))
    izd = s([grp, zd, gi], 'syl2anc', '%s e. %s' % (IZ, DV))
    LV = '( ( ZRHom ` ( Z/nZ ` V ) ) ` A )'
    DM = stmt('dchrindmulval').replace('( V DChrInd ( U x. V ) ) ` Z )', '( V DChrInd ( U x. V ) ) ` %s )' % IZ).replace(
        '( Z ` ( ( ZRHom ` ( Z/nZ ` V ) ) ` A ) )', '( %s ` %s )' % (IZ, LV)).replace('Z e. ( Base ` ( DChr ` V ) )', '%s e. %s' % (IZ, DV))
    da, dc = split_imp(DM)
    dm = s([s([un, vn], 'jca', '( U e. NN /\\ V e. NN )'), s([xd, izd], 'jca', '( X e. ( Base ` ( DChr ` U ) ) /\\ %s e. %s )' % (IZ, DV)), az, w.inst('dchrindmulval')], 'syl3anc', dc)
    inv = s([w.s([], 'eqid', '%s = %s' % (GV, GV)), eqd, zd, eqi], 'dchrinv', '%s = ( * o. Z )' % IZ)
    f1 = s([inv], 'fveq1d', '( %s ` %s ) = ( ( * o. Z ) ` %s )' % (IZ, LV, LV))
    ZV = '( Z/nZ ` V )'; BV = '( Base ` %s )' % ZV; LVF = '( ZRHom ` %s )' % ZV
    zf = s([w.s([], 'eqid', '%s = %s' % (GV, GV)), w.s([], 'eqid', '%s = %s' % (ZV, ZV)), eqd, w.s([], 'eqid', '%s = %s' % (BV, BV)), zd], 'dchrf', 'Z : %s --> CC' % BV)
    fo = w.s([w.s([], 'eqid', '%s = %s' % (ZV, ZV)), w.s([], 'eqid', '%s = %s' % (BV, BV)), w.s([], 'eqid', '%s = %s' % (LVF, LVF))], 'znzrhfo', '( V e. NN0 -> %s : ZZ -onto-> %s )' % (LVF, BV))
    lf = s([s([s([vn], 'nnnn0d', 'V e. NN0'), fo], 'syl', '%s : ZZ -onto-> %s' % (LVF, BV)), w.inst('fof')], 'syl', '%s : ZZ --> %s' % (LVF, BV))
    lb = s([lf, az], 'ffvelcdmd', '%s e. %s' % (LV, BV))
    f2 = s([zf, lb, w.inst('fvco3')], 'syl2anc', '( ( * o. Z ) ` %s ) = ( * ` ( Z ` %s ) )' % (LV, LV))
    f3 = s([f1, f2], 'eqtrd', '( %s ` %s ) = ( * ` ( Z ` %s ) )' % (IZ, LV, LV))
    XA = CHV('A', 'U', 'X')
    f4 = s([f3], 'oveq2d', '( %s x. ( %s ` %s ) ) = ( %s x. ( * ` ( Z ` %s ) ) )' % (XA, IZ, LV, XA, LV))
    w.qed([dm, f4], 'eqtrd', S['cenprodv'])
    return run(w)


if __name__ == '__main__':
    gen_cjcx()
    gen_prodv()
