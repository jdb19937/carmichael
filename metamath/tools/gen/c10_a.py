"""Sortie C10: the Blaschke frame inequality (blfr)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
from c10_freeze import S as FS
import lin
lin.FASTPATH = True


def gen_blfr():
    w = W('blfr', 'The normalised Blaschke numerator ` R - ( * ( Q - C ) / R ) ( U - C ) ` of a point ` Q ` of the closed disc of radius ` R ` about ` C ` is at most ` abs ( U - Q ) ` in modulus at every ` U ` outside the open disc: ` abs ( R ^ 2 - * x y ) ^ 2 - R ^ 2 abs ( y - x ) ^ 2 = ( R ^ 2 - abs x ^ 2 ) ( R ^ 2 - abs y ^ 2 ) ` .')
    A0 = '( ( C e. CC /\\ R e. RR+ ) /\\ ( Q e. CC /\\ ( abs ` ( Q - C ) ) <_ R ) /\\ ( U e. CC /\\ R <_ ( abs ` ( U - C ) ) ) )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    cs = s([], 'simp1l', 'C e. CC'); rp = s([], 'simp1r', 'R e. RR+')
    qc = s([], 'simp2l', 'Q e. CC'); hq = s([], 'simp2r', '( abs ` ( Q - C ) ) <_ R')
    uc = s([], 'simp3l', 'U e. CC'); hu = s([], 'simp3r', 'R <_ ( abs ` ( U - C ) )')
    X, Y = '( Q - C )', '( U - C )'
    xc = s([qc, cs], 'subcld', '%s e. CC' % X); yc = s([uc, cs], 'subcld', '%s e. CC' % Y)
    rr = s([rp], 'rpred', 'R e. RR'); rc = s([rr], 'recnd', 'R e. CC'); rne = s([rp], 'rpne0d', 'R =/= 0')
    rge = s([rp], 'rpge0d', '0 <_ R')
    CX = '( * ` %s )' % X
    cxc = s([xc], 'cjcld', '%s e. CC' % CX)
    K = '( %s / R )' % CX
    kc = s([cxc, rc, rne], 'divcld', '%s e. CC' % K)
    KY = '( %s x. %s )' % (K, Y)
    kyc = s([kc, yc], 'mulcld', '%s e. CC' % KY)
    b = '( R - %s )' % KY
    assert b == BLF('Q', 'U')
    bc = s([rc, kyc], 'subcld', '%s e. CC' % b)
    # |b|^2 = ( |R|^2 + |KY|^2 ) - 2 Re( R * conj KY )
    P1 = '( Re ` ( R x. ( * ` %s ) ) )' % KY
    sq1 = s([rc, kyc, w.inst('sqabssub')], 'syl2anc',
            '( ( abs ` %s ) ^ 2 ) = ( ( ( ( abs ` R ) ^ 2 ) + ( ( abs ` %s ) ^ 2 ) ) - ( 2 x. %s ) )' % (b, KY, P1))
    ar = s([rr, rge], 'absidd', '( abs ` R ) = R')
    ar2 = s([ar], 'oveq1d', '( ( abs ` R ) ^ 2 ) = ( R ^ 2 )')
    # P1 = Re( y * conj x )
    P = '( Re ` ( %s x. %s ) )' % (Y, CX)
    cr = s([rr], 'cjred', '( * ` R ) = R')
    t1 = s([cr], 'oveq1d', '( ( * ` R ) x. ( * ` %s ) ) = ( R x. ( * ` %s ) )' % (KY, KY))
    t2 = s([rc, kyc], 'cjmuld', '( * ` ( R x. %s ) ) = ( ( * ` R ) x. ( * ` %s ) )' % (KY, KY))
    t3 = s([t2, t1], 'eqtrd', '( * ` ( R x. %s ) ) = ( R x. ( * ` %s ) )' % (KY, KY))
    rky = '( R x. %s )' % KY
    rkyc = s([rc, kyc], 'mulcld', '%s e. CC' % rky)
    t4 = s([rkyc], 'recjd', '( Re ` ( * ` %s ) ) = ( Re ` %s )' % (rky, rky))
    t5 = s([t3], 'fveq2d', '( Re ` ( * ` %s ) ) = %s' % (rky, P1))
    t6 = s([t5, t4], 'eqtr3d', '%s = ( Re ` %s )' % (P1, rky))
    m1 = s([rc, kc, yc], 'mulassd', '( ( R x. %s ) x. %s ) = %s' % (K, Y, rky))
    m2 = s([cxc, rc, rne], 'divcan2d', '( R x. %s ) = %s' % (K, CX))
    m3 = s([m2], 'oveq1d', '( ( R x. %s ) x. %s ) = ( %s x. %s )' % (K, Y, CX, Y))
    m4 = s([m1, m3], 'eqtr3d', '%s = ( %s x. %s )' % (rky, CX, Y))
    m5 = s([cxc, yc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (CX, Y, Y, CX))
    m6 = s([s([m4, m5], 'eqtrd', '%s = ( %s x. %s )' % (rky, Y, CX))], 'fveq2d', '( Re ` %s ) = %s' % (rky, P))
    pe = s([t6, m6], 'eqtrd', '%s = %s' % (P1, P))
    # |KY| = k |y|, k = |K| = |x| / R
    k = '( abs ` %s )' % K
    AX, AY = '( abs ` %s )' % X, '( abs ` %s )' % Y
    ky = s([kc, yc], 'absmuld', '( abs ` %s ) = ( %s x. %s )' % (KY, k, AY))
    ky2 = s([ky], 'oveq1d', '( ( abs ` %s ) ^ 2 ) = ( ( %s x. %s ) ^ 2 )' % (KY, k, AY))
    kcc = s([kc], 'abscld', '%s e. RR' % k); kcx = s([kcc], 'recnd', '%s e. CC' % k)
    axr = s([xc], 'abscld', '%s e. RR' % AX); ayr = s([yc], 'abscld', '%s e. RR' % AY)
    ayc = s([ayr], 'recnd', '%s e. CC' % AY)
    ky3 = s([kcx, ayc], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (k, AY, k, AY))
    kye = s([ky2, ky3], 'eqtrd', '( ( abs ` %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (KY, k, AY))
    kd = s([cxc, rc, rne], 'absdivd', '%s = ( ( abs ` %s ) / ( abs ` R ) )' % (k, CX))
    kd2 = s([s([xc], 'abscjd', '( abs ` %s ) = %s' % (CX, AX)), ar], 'oveq12d', '( ( abs ` %s ) / ( abs ` R ) ) = ( %s / R )' % (CX, AX))
    kv = s([kd, kd2], 'eqtrd', '%s = ( %s / R )' % (k, AX))
    axc = s([axr], 'recnd', '%s e. CC' % AX)
    kr = s([s([kv], 'oveq1d', '( %s x. R ) = ( ( %s / R ) x. R )' % (k, AX)), s([axc, rc, rne], 'divcan1d', '( ( %s / R ) x. R ) = %s' % (AX, AX))],
           'eqtrd', '( %s x. R ) = %s' % (k, AX))
    ax2 = s([s([kr], 'oveq1d', '( ( %s x. R ) ^ 2 ) = ( %s ^ 2 )' % (k, AX)), s([kcx, rc], 'sqmuld', '( ( %s x. R ) ^ 2 ) = ( ( %s ^ 2 ) x. ( R ^ 2 ) )' % (k, k))],
            'eqtr3d', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( R ^ 2 ) )' % (AX, k))
    # k <_ 1, 0 <_ k
    kl1 = s([s([s([axr, rp], 'jca', '( %s e. RR /\\ R e. RR+ )' % AX), w.inst('divle1le')], 'syl', '( ( %s / R ) <_ 1 <-> %s <_ R )' % (AX, AX)), hq], 'mpbird',
            '( %s / R ) <_ 1' % AX)
    kle = s([kv, kl1], 'eqbrtrd', '%s <_ 1' % k)
    kge = s([kc], 'absge0d', '0 <_ %s' % k)
    one = s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    k2 = s([s([s([kcc, kge], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (k, k)), s([one, kle], 'jca', '( 1 e. RR /\\ %s <_ 1 )' % k)], 'jca',
               '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( 1 e. RR /\\ %s <_ 1 ) )' % (k, k, k)), w.inst('le2sq2')], 'syl', '( %s ^ 2 ) <_ ( 1 ^ 2 )' % k)
    k21 = s([k2, s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')], 'breqtrd', '( %s ^ 2 ) <_ 1' % k)
    y2 = s([s([s([rr, rge], 'jca', '( R e. RR /\\ 0 <_ R )'), s([ayr, hu], 'jca', '( %s e. RR /\\ R <_ %s )' % (AY, AY))], 'jca',
               '( ( R e. RR /\\ 0 <_ R ) /\\ ( %s e. RR /\\ R <_ %s ) )' % (AY, AY)), w.inst('le2sq2')], 'syl', '( R ^ 2 ) <_ ( %s ^ 2 )' % AY)
    K2, Y2, R2 = '( %s ^ 2 )' % k, '( %s ^ 2 )' % AY, '( R ^ 2 )'
    k2r = s([kcc], 'resqcld', '%s e. RR' % K2); y2r = s([ayr], 'resqcld', '%s e. RR' % Y2); r2r = s([rr], 'resqcld', '%s e. RR' % R2)
    g1 = s([one, k2r], 'subge0d', '( 0 <_ ( 1 - %s ) <-> %s <_ 1 )' % (K2, K2))
    g1 = s([k21, g1], 'mpbird', '0 <_ ( 1 - %s )' % K2)
    g2 = s([y2r, r2r], 'subge0d', '( 0 <_ ( %s - %s ) <-> %s <_ %s )' % (Y2, R2, R2, Y2))
    g2 = s([y2, g2], 'mpbird', '0 <_ ( %s - %s )' % (Y2, R2))
    H = s([s([one, k2r], 'resubcld', '( 1 - %s ) e. RR' % K2), s([y2r, r2r], 'resubcld', '( %s - %s ) e. RR' % (Y2, R2)), g1, g2], 'mulge0d',
          '0 <_ ( ( 1 - %s ) x. ( %s - %s ) )' % (K2, Y2, R2))
    # |U - Q|^2
    D = '( U - Q )'
    dd = s([uc, qc, cs], 'nnncan2d', '( %s - %s ) = %s' % (Y, X, D))
    sq2 = s([yc, xc, w.inst('sqabssub')], 'syl2anc', '( ( abs ` ( %s - %s ) ) ^ 2 ) = ( ( %s + ( %s ^ 2 ) ) - ( 2 x. %s ) )' % (Y, X, Y2, AX, P))
    sq2 = s([s([s([dd], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (Y, X, D))], 'oveq1d', '( ( abs ` ( %s - %s ) ) ^ 2 ) = ( ( abs ` %s ) ^ 2 )' % (Y, X, D)), sq2],
            'eqtr3d', '( ( abs ` %s ) ^ 2 ) = ( ( %s + ( %s ^ 2 ) ) - ( 2 x. %s ) )' % (D, Y2, AX, P))
    # assemble |b|^2 <_ |D|^2
    Lb, Ld = '( ( abs ` %s ) ^ 2 )' % b, '( ( abs ` %s ) ^ 2 )' % D
    AB2 = '( ( abs ` %s ) ^ 2 )' % KY
    pr = s([s([yc, cxc], 'mulcld', '( %s x. %s ) e. CC' % (Y, CX))], 'recld', '%s e. RR' % P)
    p1r = s([s([rc, s([kyc], 'cjcld', '( * ` %s ) e. CC' % KY)], 'mulcld', '( R x. ( * ` %s ) ) e. CC' % KY)], 'recld', '%s e. RR' % P1)
    lv = {'R': rr, K2: k2r, Y2: y2r, R2: r2r, P: pr, P1: p1r, AB2: s([s([kyc], 'abscld', '( abs ` %s ) e. RR' % KY)], 'resqcld', '%s e. RR' % AB2),
          '( %s ^ 2 )' % AX: s([axr], 'resqcld', '( %s ^ 2 ) e. RR' % AX), Lb: s([s([bc], 'abscld', '( abs ` %s ) e. RR' % b)], 'resqcld', '%s e. RR' % Lb),
          Ld: s([s([s([uc, qc], 'subcld', '%s e. CC' % D)], 'abscld', '( abs ` %s ) e. RR' % D)], 'resqcld', '%s e. RR' % Ld),
          '( ( abs ` R ) ^ 2 )': s([s([rc], 'abscld', '( abs ` R ) e. RR')], 'resqcld', '( ( abs ` R ) ^ 2 ) e. RR')}
    import cl as _cl
    c = _cl.Closure(w, A0, {})
    for a, st in lv.items():
        c.leaf(a, 'RR', st)
    le = lin.linarith(w, A0, [sq1, ar2, pe, kye, ax2, sq2, H], '%s <_ %s' % (Lb, Ld), closure=c, products=True)
    absb = s([bc], 'abscld', '( abs ` %s ) e. RR' % b); absd = s([s([uc, qc], 'subcld', '%s e. CC' % D)], 'abscld', '( abs ` %s ) e. RR' % D)
    eq = s([absb, absd, s([bc], 'absge0d', '0 <_ ( abs ` %s )' % b), s([s([uc, qc], 'subcld', '%s e. CC' % D)], 'absge0d', '0 <_ ( abs ` %s )' % D)], 'le2sqd',
           '( ( abs ` %s ) <_ ( abs ` %s ) <-> %s <_ %s )' % (b, D, Lb, Ld))
    goal = '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (A0, b, D)
    assert goal == FS['blfr']
    w.qed([le, eq], 'mpbird', goal)
    return run8(w)


if __name__ == '__main__':
    gen_blfr()
