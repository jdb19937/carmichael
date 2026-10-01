"""ZL3e section I: the theta integrals IL are entire and bounded on vertical strips.
`MM_DB=sorties/zl3e.mm python3 tools/gen/zl3e_i.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl3e_base import *

MAIN = __name__ == '__main__'

# ---------------------------------------------------------------- zl3pib
if wante('zl3pib', MAIN):
    w = W('zl3pib', 'The improper parameter integral of ~ zl3pih is bounded by the series of its unit-interval majorants: ` abs ( lim_t S. ( 1 , t ) G y ^ S ) <_ sum_j MJ ( j ) ` ( ~ zl3pcv , ~ zl3pbd , ~ zl3msum ).')
    A, Cc = ante_e('zl3pib')
    PHV = L.PHV
    phv = D(w, A, 'simpl', [], PHV)
    tr3 = D(w, A, 'simpr', [], '( S e. CC /\\ R e. RR /\\ ( ( abs ` ( Re ` S ) ) + 1 ) <_ R )')
    sc = D(w, A, 'simp1d', [tr3], 'S e. CC'); rr = D(w, A, 'simp2d', [tr3], 'R e. RR'); rle = D(w, A, 'simp3d', [tr3], '( ( abs ` ( Re ` S ) ) + 1 ) <_ R')
    kb = D(w, A, 'simprd', [phv], '( K e. RR+ /\\ B e. RR+ /\\ A. v e. ( 1 [,) +oo ) ( abs ` ( G ` v ) ) <_ ( K x. ( exp ` -u ( B x. v ) ) ) )')
    krp = D(w, A, 'simp1d', [kb], 'K e. RR+'); brp = D(w, A, 'simp2d', [kb], 'B e. RR+')
    PCV = L.split_imp(L.STATEMENTS['zl3pcv'])[1]
    pcv = D(w, A, 'syl2anc', [phv, sc, w.inst('zl3pcv')], PCV)
    SUMX = PCV[PCV.index(' ~~>r ') + 6:]
    ff = imp_f(w, A, phv, sc, 'S')
    val = val_of(w, A, L.IMP('S'), SUMX, pcv, ff)
    PAx = L.PA('S', 'j', '( j + 1 )', 'x'); PAy = L.PA('S', 'j', '( j + 1 )')
    PAi = L.PA('S', 'i', '( i + 1 )', 'x')
    F1 = '( i e. NN |-> %s )' % PAi
    G1 = '( q e. NN |-> ( abs ` ( %s ` q ) ) )' % F1
    F2 = '( i e. NN |-> %s )' % L.MJ('i')
    F2j = '( j e. NN |-> %s )' % L.MJ('j')
    iv = w.s([w.s([], 'id', '( i = j -> i = j )'), w.s([], 'oveq1', '( i = j -> ( i + 1 ) = ( j + 1 ) )')], 'oveq12d', '( i = j -> ( i (,) ( i + 1 ) ) = ( j (,) ( j + 1 ) ) )')
    subPA = w.s([iv, w.s([], 'itgeq1', '( ( i (,) ( i + 1 ) ) = ( j (,) ( j + 1 ) ) -> %s = %s )' % (PAi, PAx))], 'syl', '( i = j -> %s = %s )' % (PAi, PAx))
    subG = w.s([w.s([], 'fveq2', '( q = j -> ( %s ` q ) = ( %s ` j ) )' % (F1, F1))], 'fveq2d', '( q = j -> ( abs ` ( %s ` q ) ) = ( abs ` ( %s ` j ) ) )' % (F1, F1))
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')

    def per_j(Aj, jn):
        jr = D(w, Aj, 'nnred', [jn], 'j e. RR'); j1 = D(w, Aj, 'nnge1d', [jn], '1 <_ j')
        j1r = D(w, Aj, 'syl', [jr, w.inst('peano2re')], '( j + 1 ) e. RR')
        phj, scj = ad(w, Aj, phv, PHV), ad(w, Aj, sc, 'S e. CC')
        pay = D(w, Aj, 'itgcl', [ibl_pa(w, Aj, phj, jr, j1, j1r, 'S', scj, P='j', Q='( j + 1 )'),
                                 integrand_cl(w, Aj, phj, jr, j1, j1r, 'S', scj, P='j', Q='( j + 1 )')], '%s e. CC' % PAy)
        cxy = w.s([cbv_xy(w, 'j', '( j + 1 )')], 'a1i', '( %s -> %s = %s )' % (Aj, PAx, PAy))
        pax = D(w, Aj, 'eqeltrd', [cxy, pay], '%s e. CC' % PAx)
        jiv = D(w, Aj, 'mpbir3and', [D(w, Aj, 'syl2anc', [jr, j1r, w.inst('elicc2')], '( ( j + 1 ) e. ( j [,] ( j + 1 ) ) <-> ( ( j + 1 ) e. RR /\\ j <_ ( j + 1 ) /\\ ( j + 1 ) <_ ( j + 1 ) ) )'),
                                     j1r, D(w, Aj, 'lep1d', [jr], 'j <_ ( j + 1 )'), D(w, Aj, 'leidd', [j1r], '( j + 1 ) <_ ( j + 1 )')], '( j + 1 ) e. ( j [,] ( j + 1 ) )')
        pbd = D(w, Aj, 'syl3anc', [phj, D(w, Aj, 'jca31' if False else '3jca', [ad(w, Aj, rr, 'R e. RR'), scj, ad(w, Aj, rle, '( ( abs ` ( Re ` S ) ) + 1 ) <_ R')],
                                           '( R e. RR /\\ S e. CC /\\ ( ( abs ` ( Re ` S ) ) + 1 ) <_ R )'),
                                   D(w, Aj, 'jca', [jn, jiv], '( j e. NN /\\ ( j + 1 ) e. ( j [,] ( j + 1 ) ) )'), w.inst('zl3pbd')],
                  '( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s )' % (PAy, L.MJ('j'), L.PV('S', 'j', '( j + 1 )'), L.MJ('j')))
        ble = D(w, Aj, 'eqbrtrd', [D(w, Aj, 'fveq2d', [cxy], '( abs ` %s ) = ( abs ` %s )' % (PAx, PAy)), D(w, Aj, 'simpld', [pbd], '( abs ` %s ) <_ %s' % (PAy, L.MJ('j')))],
                '( abs ` %s ) <_ %s' % (PAx, L.MJ('j')))
        cl = Closure(w, Aj, {'j': ('NN', jn), 'K': ('RR+', ad(w, Aj, krp, 'K e. RR+')), 'B': ('RR+', ad(w, Aj, brp, 'B e. RR+')), 'R': ('RR', ad(w, Aj, rr, 'R e. RR'))})
        mjr = cl.mem(L.MJ('j'), 'RR')
        f1 = D(w, Aj, 'syl', [jn, w.s([subPA, w.s([], 'eqid', '%s = %s' % (F1, F1)), w.s([], 'itgex' if False else 'ovex', '%s e. _V' % PAx) if False else w.s([], 'itgex', '%s e. _V' % PAx)], 'fvmpt',
                                        '( j e. NN -> ( %s ` j ) = %s )' % (F1, PAx))], '( %s ` j ) = %s' % (F1, PAx))
        g1 = D(w, Aj, 'eqtrd', [D(w, Aj, 'syl', [jn, w.s([subG, w.s([], 'eqid', '%s = %s' % (G1, G1)), w.s([], 'fvex', '( abs ` ( %s ` j ) ) e. _V' % F1)], 'fvmpt',
                                                        '( j e. NN -> ( %s ` j ) = ( abs ` ( %s ` j ) ) )' % (G1, F1))], '( %s ` j ) = ( abs ` ( %s ` j ) )' % (G1, F1)),
                                D(w, Aj, 'fveq2d', [f1], '( abs ` ( %s ` j ) ) = ( abs ` %s )' % (F1, PAx))], '( %s ` j ) = ( abs ` %s )' % (G1, PAx))
        f2 = D(w, Aj, 'syl', [jn, w.s([mj_sub(w, 'i', 'j', 'R'), w.s([], 'eqid', '%s = %s' % (F2, F2)), w.s([], 'ovex', '%s e. _V' % L.MJ('j'))], 'fvmpt',
                                       '( j e. NN -> ( %s ` j ) = %s )' % (F2, L.MJ('j')))], '( %s ` j ) = %s' % (F2, L.MJ('j')))
        return dict(pax=pax, ble=ble, mjr=mjr, f1=f1, g1=g1, f2=f2, ar=D(w, Aj, 'abscld', [pax], '( abs ` %s ) e. RR' % PAx), a0=D(w, Aj, 'absge0d', [pax], '0 <_ ( abs ` %s )' % PAx))
    Aj = '( %s /\\ j e. NN )' % A
    P = per_j(Aj, w.s([], 'simpr', '( %s -> j e. NN )' % Aj))
    Az = '( %s /\\ j e. ( ZZ>= ` 1 ) )' % A
    Q = per_j(Az, D(w, Az, 'sylibr', [w.s([], 'simpr', '( %s -> j e. ( ZZ>= ` 1 ) )' % Az), w.inst('elnnuz')], 'j e. NN'))
    one = D(w, A, '1zzd', [], '1 e. ZZ')
    msumj = D(w, A, 'syl3anc', [krp, brp, rr, w.inst('zl3msum')], 'seq 1 ( + , %s ) e. dom ~~>' % F2j)
    cbF2 = w.s([mj_sub(w, 'j', 'i', 'R')], 'cbvmptv', '%s = %s' % (F2j, F2))
    msum = D(w, A, 'eleqtrd' if False else 'mpbid', [msumj, w.s([w.s([w.s([cbF2, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (F2j, F2))], 'eleq1i',
                                                                    '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (F2j, F2))], 'a1i',
                                                        '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A, F2j, F2))], 'seq 1 ( + , %s ) e. dom ~~>' % F2)
    cG = D(w, A, 'cvgcmp', [nnz, D(w, A, '1nn', [], '1 e. NN') if False else cst(w, A, '1nn', '1 e. NN'),
                            D(w, Aj, 'eqeltrd', [P['f2'], P['mjr']], '( %s ` j ) e. RR' % F2), D(w, Aj, 'eqeltrd', [P['g1'], P['ar']], '( %s ` j ) e. RR' % G1), msum,
                            D(w, Az, 'breqtrrd', [Q['a0'], Q['g1']], '0 <_ ( %s ` j )' % G1),
                            D(w, Az, 'breqtrrd', [D(w, Az, 'breqtrd', [D(w, Az, 'eqbrtrd', [Q['g1'], Q['ble']], '( %s ` j ) <_ %s' % (G1, L.MJ('j'))), D(w, Az, 'eqcomd', [Q['f2']], '%s = ( %s ` j )' % (L.MJ('j'), F2))],
                                                        '( %s ` j ) <_ ( %s ` j )' % (G1, F2)), D(w, Az, 'eqidd', [], '( %s ` j ) = ( %s ` j )' % (F2, F2))], '( %s ` j ) <_ ( %s ` j )' % (G1, F2))],
            'seq 1 ( + , %s ) e. dom ~~>' % G1)
    g1f1 = D(w, Aj, 'eqtrd', [P['g1'], D(w, Aj, 'fveq2d', [D(w, Aj, 'eqcomd', [P['f1']], '%s = ( %s ` j )' % (PAx, F1))], '( abs ` %s ) = ( abs ` ( %s ` j ) )' % (PAx, F1))],
             '( %s ` j ) = ( abs ` ( %s ` j ) )' % (G1, F1))
    f1c = D(w, Aj, 'eqeltrd', [P['f1'], P['pax']], '( %s ` j ) e. CC' % F1)
    cF = D(w, A, 'abscvgcvg', [nnz, one, g1f1, f1c, cG], 'seq 1 ( + , %s ) e. dom ~~>' % F1)
    SA = 'sum_ j e. NN ( abs ` %s )' % PAx
    l1 = D(w, A, 'isumclim2', [nnz, one, P['f1'], P['pax'], cF], 'seq 1 ( + , %s ) ~~> %s' % (F1, SUMX))
    l2 = D(w, A, 'isumclim2', [nnz, one, P['g1'], D(w, Aj, 'recnd', [P['ar']], '( abs ` %s ) e. CC' % PAx), cG], 'seq 1 ( + , %s ) ~~> %s' % (G1, SA))
    ab = D(w, A, 'iserabs', [nnz, l1, l2, one, f1c, g1f1], '( abs ` %s ) <_ %s' % (SUMX, SA))
    le2 = D(w, A, 'isumle', [nnz, one, P['g1'], P['ar'], P['f2'], P['mjr'], P['ble'], cG, msum], '%s <_ sum_ j e. NN %s' % (SA, L.MJ('j')))
    sar = D(w, A, 'isumrecl', [nnz, one, P['g1'], P['ar'], cG], '%s e. RR' % SA)
    smr = D(w, A, 'isumrecl', [nnz, one, P['f2'], P['mjr'], msum], 'sum_ j e. NN %s e. RR' % L.MJ('j'))
    sxc = D(w, A, 'isumcl', [nnz, one, P['f1'], P['pax'], cF], '%s e. CC' % SUMX)
    bnd = D(w, A, 'letrd', [D(w, A, 'abscld', [sxc], '( abs ` %s ) e. RR' % SUMX), sar, smr, ab, le2], '( abs ` %s ) <_ sum_ j e. NN %s' % (SUMX, L.MJ('j')))
    IV = '( ~~>r ` %s )' % L.IMP('S')
    c1 = D(w, A, 'eqeltrd', [val, sxc], '%s e. CC' % IV)
    c2 = D(w, A, 'eqbrtrd', [D(w, A, 'fveq2d', [val], '( abs ` %s ) = ( abs ` %s )' % (IV, SUMX)), bnd], '( abs ` %s ) <_ sum_ j e. NN %s' % (IV, L.MJ('j')))
    w.qed([D(w, A, 'jca', [c1, c2], Cc)], 'idi', SE['zl3pib'])
    goe(w)


THm = lambda v: LE.tsub(LE.THG('C', v, 'P'), {'n': 'm'})
GR = LE.GR
assert GR == '( r e. ( 1 [,) +oo ) |-> %s )' % THm('r')


def gr_val(w, Aty, yU, y='y'):
    """( Aty -> ( GR ` y ) = THG ( C , y , P ) ), yU: ( Aty -> y e. ( 1 [,) +oo ) )"""
    SMD = lambda v, q: LE.tsub(LE.THG('C', v, 'P')[len('sum_ n e. NN '):], {'n': q})
    cbs = w.s([vsub(w, lambda q: SMD(y, q), 'm', 'n')], 'cbvsumv', '%s = %s' % (THm(y), LE.THG('C', y, 'P')))
    return D(w, Aty, 'eqtrd', [fv1(w, Aty, 'r', '( 1 [,) +oo )', THm, y, yU, 'sumex'), w.s([cbs], 'a1i', '( %s -> %s = %s )' % (Aty, THm(y), LE.THG('C', y, 'P')))],
             '( %s ` %s ) = %s' % (GR, y, LE.THG('C', y, 'P')))


# ---------------------------------------------------------------- zl3ilv
if wante('zl3ilv', MAIN):
    w = W('zl3ilv', 'The theta integral ` IL ` as an instance of ~ zl3pih : the theta series written ` ( r e. ( 1 [,) +oo ) |-> sum_ m ... ) ` satisfies its hypotheses ( ~ zl3thph ), and ` IL ( C , w ) ` is its parameter integral at ` ( w + P ) / 2 - 1 ` .')
    A, Cc = ante_e('zl3ilv')
    ta = w.s([], 'id', '( %s -> %s )' % (A, A)) if False else None
    GTH0 = L.GTH
    PHT0 = L.PHT
    thph0 = D(w, A, 'syl', [w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('zl3thph')], PHT0) if False else w.s([w.inst('zl3thph')], 'idi', '( %s -> %s )' % (A, PHT0)) if False else None
    thph0 = w.s([], 'zl3thph', '( %s -> %s )' % (A, PHT0))
    SMD = lambda v, q: LE.tsub(LE.THG('C', v, 'P')[len('sum_ n e. NN '):], {'n': q})
    cbs_r = w.s([vsub(w, lambda q: SMD('r', q), 'n', 'm')], 'cbvsumv', '%s = %s' % (LE.THG('C', 'r', 'P'), THm('r')))
    eyr = w.s([vsub(w, lambda v: LE.THG('C', v, 'P'), 'y', 'r'), w.s([cbs_r], 'a1i', '( y = r -> %s = %s )' % (LE.THG('C', 'r', 'P'), THm('r')))], 'eqtrd',
              '( y = r -> %s = %s )' % (LE.THG('C', 'y', 'P'), THm('r')))
    assert GTH0 == '( y e. ( 1 [,) +oo ) |-> %s )' % LE.THG('C', 'y', 'P')
    eqG = w.s([w.s([eyr], 'cbvmptv', '%s = %s' % (GTH0, GR))], 'a1i', '( %s -> %s = %s )' % (A, GTH0, GR))
    wb, PHTB = w.wcongr(PHT0, {}, A, {}, rules={GTH0: (GR, eqG)})
    assert PHTB == LE.PHR, (PHTB, LE.PHR)
    phr = D(w, A, 'mpbid', [thph0, wb], LE.PHR)
    Aw = '( %s /\\ w e. CC )' % A
    At = '( %s /\\ t e. RR+ )' % Aw
    Aty = '( %s /\\ y e. ( 1 (,) t ) )' % At
    trt = D(w, Aty, 'rpred', [w.s([], 'simplr', '( %s -> t e. RR+ )' % Aty)], 't e. RR')
    yin = w.s([], 'simpr', '( %s -> y e. ( 1 (,) t ) )' % Aty)
    b = D(w, Aty, 'mpbid', [yin, D(w, Aty, 'syl2anc', [cst(w, Aty, '1xr', '1 e. RR*'), D(w, Aty, 'rexrd', [trt], 't e. RR*'), w.inst('elioo2')],
                                   '( y e. ( 1 (,) t ) <-> ( y e. RR /\\ 1 < y /\\ y < t ) )')], '( y e. RR /\\ 1 < y /\\ y < t )')
    yr = D(w, Aty, 'simp1d', [b], 'y e. RR'); y1 = D(w, Aty, 'simp2d', [b], '1 < y')
    yU = D(w, Aty, 'mpbird', [D(w, Aty, 'jca', [yr, D(w, Aty, 'ltled', [cst(w, Aty, '1re', '1 e. RR'), yr, y1], '1 <_ y')], '( y e. RR /\\ 1 <_ y )'),
                              D(w, Aty, 'syl', [cst(w, Aty, '1re', '1 e. RR'), w.inst('elicopnf')], '( y e. ( 1 [,) +oo ) <-> ( y e. RR /\\ 1 <_ y ) )')], 'y e. ( 1 [,) +oo )')
    gv = gr_val(w, Aty, yU)
    S_ = '( ( ( w + P ) / 2 ) - 1 )'
    ie = D(w, At, 'itgeq2dv', [D(w, Aty, 'oveq1d', [gv], '( ( %s ` y ) x. ( y ^c %s ) ) = ( %s x. ( y ^c %s ) )' % (GR, S_, LE.THG('C', 'y', 'P'), S_))],
           'S. ( 1 (,) t ) ( ( %s ` y ) x. ( y ^c %s ) ) _d y = S. ( 1 (,) t ) ( %s x. ( y ^c %s ) ) _d y' % (GR, S_, LE.THG('C', 'y', 'P'), S_))
    me = D(w, Aw, 'mpteq2dva', [ie], '%s = ( t e. RR+ |-> S. ( 1 (,) t ) ( %s x. ( y ^c %s ) ) _d y )' % (LE.IMR(S_), LE.THG('C', 'y', 'P'), S_))
    fe = D(w, Aw, 'fveq2d', [me], '( ~~>r ` %s ) = %s' % (LE.IMR(S_), LE.ILG('C', 'w', 'P')))
    ral = D(w, A, 'ralrimiva', [D(w, Aw, 'eqcomd', [fe], '%s = ( ~~>r ` %s )' % (LE.ILG('C', 'w', 'P'), LE.IMR(S_)))], 'A. w e. CC %s = ( ~~>r ` %s )' % (LE.ILG('C', 'w', 'P'), LE.IMR(S_)))
    w.qed([D(w, A, 'jca', [phr, ral], Cc)], 'idi', SE['zl3ilv'])
    goe(w)


def imr_sub(w, s, X):
    """closed ( s = X -> ( ~~>r ` IMR(s) ) = ( ~~>r ` IMR(X) ) )"""
    ph = '%s = %s' % (s, X)
    body = lambda e: '( ( %s ` y ) x. ( y ^c %s ) )' % (GR, e)
    b = w.s([w.s([w.s([], 'oveq2', '( %s -> ( y ^c %s ) = ( y ^c %s ) )' % (ph, s, X))], 'oveq2d', '( %s -> %s = %s )' % (ph, body(s), body(X)))], 'adantr',
            '( ( %s /\\ y e. ( 1 (,) t ) ) -> %s = %s )' % (ph, body(s), body(X)))
    ph2 = '( %s /\\ t e. RR+ )' % ph
    b2 = w.s([w.s([w.s([w.s([], 'oveq2', '( %s -> ( y ^c %s ) = ( y ^c %s ) )' % (ph, s, X))], 'oveq2d', '( %s -> %s = %s )' % (ph, body(s), body(X)))], 'ad2antrr',
              '( ( %s /\\ y e. ( 1 (,) t ) ) -> %s = %s )' % (ph2, body(s), body(X)))], 'itgeq2dv',
             '( %s -> S. ( 1 (,) t ) %s _d y = S. ( 1 (,) t ) %s _d y )' % (ph2, body(s), body(X)))
    m = w.s([b2], 'mpteq2dva', '( %s -> %s = %s )' % (ph, LE.IMR(s), LE.IMR(X)))
    return w.s([m], 'fveq2d', '( %s -> ( ~~>r ` %s ) = ( ~~>r ` %s ) )' % (ph, LE.IMR(s), LE.IMR(X)))


# ---------------------------------------------------------------- zl3ilh
if wante('zl3ilh', MAIN):
    w = W('zl3ilh', 'The theta integral ` w |-> IL ( C , w ) ` is entire: ~ zl3pih composed with the affine map ` w |-> ( w + P ) / 2 - 1 ` ( ~ zl3hco , ~ zl3haff ).')
    A, Cc = ante_e('zl3ilh')
    ilv = w.s([], 'zl3ilv', '( %s -> %s )' % (A, L.split_imp(SE['zl3ilv'])[1]))
    phr = D(w, A, 'simpld', [ilv], LE.PHR)
    S_ = '( ( ( w + P ) / 2 ) - 1 )'
    RALW = 'A. w e. CC %s = ( ~~>r ` %s )' % (LE.ILG('C', 'w', 'P'), LE.IMR(S_))
    ral = D(w, A, 'simprd', [ilv], RALW)
    KT, BB = L.KT, '( _pi / M )'
    bodyv = lambda v: '( abs ` ( %s ` %s ) ) <_ ( %s x. ( exp ` -u ( %s x. %s ) ) )' % (GR, v, KT, BB, v)
    X1 = '( %s : ( 1 [,) +oo ) --> CC /\\ ( %s |` ( 1 (,) +oo ) ) e. ( ( 1 (,) +oo ) -cn-> CC ) )' % (GR, GR)
    X2 = '( %s e. RR+ /\\ %s e. RR+ /\\ A. v e. ( 1 [,) +oo ) %s )' % (KT, BB, bodyv('v'))
    assert LE.PHR == '( %s /\\ %s )' % (X1, X2)
    x1 = D(w, A, 'simpld', [phr], X1); x2 = D(w, A, 'simprd', [phr], X2)
    ralv = D(w, A, 'simp3d', [x2], 'A. v e. ( 1 [,) +oo ) %s' % bodyv('v'))
    raly = D(w, A, 'mpbid', [ralv, w.s([w.s([wsub(w, bodyv, 'v', 'y')], 'cbvralvw', '( A. v e. ( 1 [,) +oo ) %s <-> A. y e. ( 1 [,) +oo ) %s )' % (bodyv('v'), bodyv('y')))], 'a1i',
                                        '( %s -> ( A. v e. ( 1 [,) +oo ) %s <-> A. y e. ( 1 [,) +oo ) %s ) )' % (A, bodyv('v'), bodyv('y')))], 'A. y e. ( 1 [,) +oo ) %s' % bodyv('y'))
    PHY = '( %s /\\ ( %s e. RR+ /\\ %s e. RR+ /\\ A. y e. ( 1 [,) +oo ) %s ) )' % (X1, KT, BB, bodyv('y'))
    phy = D(w, A, 'jca', [x1, D(w, A, '3jca', [D(w, A, 'simp1d', [x2], '%s e. RR+' % KT), D(w, A, 'simp2d', [x2], '%s e. RR+' % BB), raly], '( %s e. RR+ /\\ %s e. RR+ /\\ A. y e. ( 1 [,) +oo ) %s )' % (KT, BB, bodyv('y')))], PHY)
    PIH = '( s e. CC |-> ( ~~>r ` %s ) )' % LE.IMR('s')
    pih = D(w, A, 'syl', [phy, w.inst('zl3pih')], HOL(PIH, 'CC'))
    mn, pp = ta_facts(w, A, w.s([], 'id', '( %s -> %s )' % (A, A)))
    pn, pr, p0, p1 = p01(w, A, pp)
    pc = D(w, A, 'recnd', [pr], 'P e. CC')
    B_ = '( ( P / 2 ) - 1 )'
    AFFb = lambda z: '( ( ( 1 / 2 ) x. %s ) + %s )' % (z, B_)
    bc = D(w, A, 'subcld', [D(w, A, 'halfcld', [pc], '( P / 2 ) e. CC'), cst(w, A, 'ax-1cn', '1 e. CC')], '%s e. CC' % B_)
    AFFz = '( z e. CC |-> %s )' % AFFb('z')
    AFF = '( x e. CC |-> %s )' % AFFb('x')
    aff0 = D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), bc], '( ( 1 / 2 ) e. CC /\\ %s e. CC )' % B_), cst(w, A, 'cnopn', 'CC e. ( TopOpen ` CCfld )'), w.inst('zl3haff')],
            HOL(AFFz, 'CC'))
    cbA = w.s([w.s([vsub(w, AFFb, 'z', 'x')], 'cbvmptv', '%s = %s' % (AFFz, AFF))], 'a1i', '( %s -> %s = %s )' % (A, AFFz, AFF))
    aff = D(w, A, 'mpbid', [aff0, hol_eq(w, A, cbA, AFFz, AFF, 'CC')], HOL(AFF, 'CC'))
    Av = '( %s /\\ v e. CC )' % A
    vc = w.s([], 'simpr', '( %s -> v e. CC )' % Av)
    affv = fv1(w, Av, 'x', 'CC', AFFb, 'v', vc, 'ovex')
    affc = D(w, Av, 'eqeltrd', [affv, D(w, Av, 'addcld', [D(w, Av, 'mulcld', [cst(w, Av, 'halfcn', '( 1 / 2 ) e. CC'), vc], '( ( 1 / 2 ) x. v ) e. CC'), ad(w, Av, bc, '%s e. CC' % B_)], '%s e. CC' % AFFb('v'))],
             '( %s ` v ) e. CC' % AFF)
    rng = D(w, A, 'ralrimiva', [affc], 'A. v e. CC ( %s ` v ) e. CC' % AFF)
    hco = D(w, A, 'syl3anc', [pih, aff, rng, w.inst('zl3hco')], HOL('( z e. CC |-> ( %s ` ( %s ` z ) ) )' % (PIH, AFF), 'CC'))
    Zm = '( z e. CC |-> ( %s ` ( %s ` z ) ) )' % (PIH, AFF)
    Wm = '( w e. CC |-> ( %s ` ( %s ` w ) ) )' % (PIH, AFF)
    e1 = w.s([w.s([w.s([], 'fveq2', '( z = w -> ( %s ` z ) = ( %s ` w ) )' % (AFF, AFF))], 'fveq2d', '( z = w -> ( %s ` ( %s ` z ) ) = ( %s ` ( %s ` w ) ) )' % (PIH, AFF, PIH, AFF))],
             'cbvmptv', '%s = %s' % (Zm, Wm))
    Aw = '( %s /\\ w e. CC )' % A
    wc = w.s([], 'simpr', '( %s -> w e. CC )' % Aw)
    affw = fv1(w, Aw, 'x', 'CC', AFFb, 'w', wc, 'ovex')
    pcw = ad(w, Aw, pc, 'P e. CC')
    hw = D(w, Aw, 'halfcld', [wc], '( w / 2 ) e. CC'); hp = D(w, Aw, 'halfcld', [pcw], '( P / 2 ) e. CC')
    alg = chain(w, Aw, [AFFb('w'), '( ( w / 2 ) + %s )' % B_, '( ( ( w / 2 ) + ( P / 2 ) ) - 1 )', '( ( ( w + P ) / 2 ) - 1 )'],
                [D(w, Aw, 'oveq1d', [D(w, Aw, 'eqcomd', [D(w, Aw, 'divrec2d', [wc, cst(w, Aw, '2cn', '2 e. CC'), cst(w, Aw, '2ne0', '2 =/= 0')], '( w / 2 ) = ( ( 1 / 2 ) x. w )')],
                                                        '( ( 1 / 2 ) x. w ) = ( w / 2 )')], '%s = ( ( w / 2 ) + %s )' % (AFFb('w'), B_)),
                 ('r', D(w, Aw, 'addsubassd', [hw, hp, cst(w, Aw, 'ax-1cn', '1 e. CC')], '( ( ( w / 2 ) + ( P / 2 ) ) - 1 ) = ( ( w / 2 ) + %s )' % B_)),
                 D(w, Aw, 'oveq1d', [D(w, Aw, 'eqcomd', [D(w, Aw, 'divdird', [wc, pcw, cst(w, Aw, '2cn', '2 e. CC'), cst(w, Aw, '2ne0', '2 =/= 0')], '( ( w + P ) / 2 ) = ( ( w / 2 ) + ( P / 2 ) )')],
                                                        '( ( w / 2 ) + ( P / 2 ) ) = ( ( w + P ) / 2 )')], '( ( ( w / 2 ) + ( P / 2 ) ) - 1 ) = ( ( ( w + P ) / 2 ) - 1 )')])
    sc_ = D(w, Aw, 'subcld', [D(w, Aw, 'halfcld', [D(w, Aw, 'addcld', [wc, pcw], '( w + P ) e. CC')], '( ( w + P ) / 2 ) e. CC'), cst(w, Aw, 'ax-1cn', '1 e. CC')], '%s e. CC' % S_)
    pihv = D(w, Aw, 'syl', [sc_, w.s([imr_sub(w, 's', S_), w.s([], 'eqid', '%s = %s' % (PIH, PIH)), w.s([], 'fvex', '( ~~>r ` %s ) e. _V' % LE.IMR(S_))], 'fvmpt',
                                     '( %s e. CC -> ( %s ` %s ) = ( ~~>r ` %s ) )' % (S_, PIH, S_, LE.IMR(S_)))], '( %s ` %s ) = ( ~~>r ` %s )' % (PIH, S_, LE.IMR(S_)))
    val = chain(w, Aw, ['( %s ` ( %s ` w ) )' % (PIH, AFF), '( %s ` %s )' % (PIH, S_), '( ~~>r ` %s )' % LE.IMR(S_), LE.ILG('C', 'w', 'P')],
                [D(w, Aw, 'fveq2d', [D(w, Aw, 'eqtrd', [affw, alg], '( %s ` w ) = %s' % (AFF, S_))], '( %s ` ( %s ` w ) ) = ( %s ` %s )' % (PIH, AFF, PIH, S_)),
                 pihv, ('r', D(w, Aw, 'r19.21bi' if False else 'r19.21bi', [], '') if False else ('r', w.s([ral], 'r19.21bi', '( %s -> %s = ( ~~>r ` %s ) )' % (Aw, LE.ILG('C', 'w', 'P'), LE.IMR(S_))))[1])])
    e2 = D(w, A, 'mpteq2dva', [val], '%s = %s' % (Wm, LE.MPW('C', 'P')))
    eq = D(w, A, 'eqtrd', [w.s([e1], 'a1i', '( %s -> %s = %s )' % (A, Zm, Wm)), e2], '%s = %s' % (Zm, LE.MPW('C', 'P')))
    fin = D(w, A, 'mpbid', [hco, hol_eq(w, A, eq, Zm, LE.MPW('C', 'P'), 'CC')], Cc)
    w.qed([fin], 'idi', SE['zl3ilh'])
    goe(w)


# ---------------------------------------------------------------- zl3ilb
if wante('zl3ilb', MAIN):
    w = W('zl3ilb', 'The theta integral ` IL ( C , w ) ` is bounded on the strip ` -1 <_ Re w <_ 3 ` ( ~ zl3pib at ` R = 5 / 2 ` ).')
    A, Cc = ante_e('zl3ilb')
    ilv = w.s([], 'zl3ilv', '( %s -> %s )' % (A, L.split_imp(SE['zl3ilv'])[1]))
    phr = D(w, A, 'simpld', [ilv], LE.PHR)
    S_ = '( ( ( w + P ) / 2 ) - 1 )'
    RALW = 'A. w e. CC %s = ( ~~>r ` %s )' % (LE.ILG('C', 'w', 'P'), LE.IMR(S_))
    ral = D(w, A, 'simprd', [ilv], RALW)
    KT, BB, R5 = L.KT, '( _pi / M )', '( 5 / 2 )'
    MJr = lambda j: LE.tsub(L.MJ(j), {'K': KT, 'B': BB, 'R': R5})
    SMJ = 'sum_ j e. NN %s' % MJr('j')
    mn, pp = ta_facts(w, A, w.s([], 'id', '( %s -> %s )' % (A, A)))
    pn, pr, p0, p1 = p01(w, A, pp)
    clA = Closure(w, A, {'M': ('NN', mn), '_pi': ('RR+', cst(w, A, 'pirp', '_pi e. RR+'))})
    ktp, bbp = clA.mem(KT, 'RR+'), clA.mem(BB, 'RR+')
    r5 = clA.mem(R5, 'RR')
    # SMJ is real
    F2j = '( j e. NN |-> %s )' % MJr('j'); F2 = '( i e. NN |-> %s )' % MJr('i')
    msumj = D(w, A, 'syl3anc', [ktp, bbp, r5, w.inst('zl3msum')], 'seq 1 ( + , %s ) e. dom ~~>' % F2j)
    cbF2 = w.s([mj_sub(w, 'j', 'i', R5) if False else vsub(w, MJr, 'j', 'i')], 'cbvmptv', '%s = %s' % (F2j, F2))
    msum = D(w, A, 'mpbid', [msumj, w.s([w.s([w.s([cbF2, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (F2j, F2))], 'eleq1i',
                                               '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (F2j, F2))], 'a1i',
                                         '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A, F2j, F2))], 'seq 1 ( + , %s ) e. dom ~~>' % F2)
    Aj = '( %s /\\ j e. NN )' % A
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    clj = Closure(w, Aj, {'j': ('NN', jn), 'M': ('NN', ad(w, Aj, mn, 'M e. NN')), '_pi': ('RR+', cst(w, Aj, 'pirp', '_pi e. RR+'))})
    mjr = clj.mem(MJr('j'), 'RR')
    f2 = D(w, Aj, 'syl', [jn, w.s([vsub(w, MJr, 'i', 'j'), w.s([], 'eqid', '%s = %s' % (F2, F2)), w.s([], 'ovex', '%s e. _V' % MJr('j'))], 'fvmpt',
                                   '( j e. NN -> ( %s ` j ) = %s )' % (F2, MJr('j')))], '( %s ` j ) = %s' % (F2, MJr('j')))
    smr = D(w, A, 'isumrecl', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), D(w, A, '1zzd', [], '1 e. ZZ'), f2, mjr, msum], '%s e. RR' % SMJ)
    # the bound at w
    Aw = '( %s /\\ w e. CC )' % A
    Aw2 = '( %s /\\ ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) )' % Aw
    wc = D(w, Aw2, 'simplr', [], 'w e. CC')
    lo = D(w, Aw2, 'simprl', [], '-u 1 <_ ( Re ` w )'); hi = D(w, Aw2, 'simprr', [], '( Re ` w ) <_ 3')
    L2 = lambda st, f: ad(w, Aw2, ad(w, Aw, st, f), f)
    pr2, p02, p12 = L2(pr, 'P e. RR'), L2(p0, '0 <_ P'), L2(p1, 'P <_ 1')
    pc2 = D(w, Aw2, 'recnd', [pr2], 'P e. CC')
    spc, reW, imW = reim_w(w, Aw2, 'w', wc, pc2, pr2)
    Wv = '( ( w + P ) / 2 )'
    wv_c = D(w, Aw2, 'halfcld', [spc], '%s e. CC' % Wv)
    sc_ = D(w, Aw2, 'subcld', [wv_c, cst(w, Aw2, 'ax-1cn', '1 e. CC')], '%s e. CC' % S_)
    reS = chain(w, Aw2, ['( Re ` %s )' % S_, '( ( Re ` %s ) - ( Re ` 1 ) )' % Wv, '( ( ( ( Re ` w ) + P ) / 2 ) - 1 )'],
                [D(w, Aw2, 'resubd', [wv_c, cst(w, Aw2, 'ax-1cn', '1 e. CC')], '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` 1 ) )' % (S_, Wv)),
                 D(w, Aw2, 'oveq12d', [reW, cst(w, Aw2, 're1', '( Re ` 1 ) = 1')], '( ( Re ` %s ) - ( Re ` 1 ) ) = ( ( ( ( Re ` w ) + P ) / 2 ) - 1 )' % Wv)])
    rwr = D(w, Aw2, 'recld', [wc], '( Re ` w ) e. RR')
    cl = Closure(w, Aw2, {'( Re ` w )': ('RR', rwr), 'P': [('RR', pr2), ('ge0', p02)]})
    rsr = D(w, Aw2, 'recld', [sc_], '( Re ` %s ) e. RR' % S_)
    ab = D(w, Aw2, 'mpbird', [D(w, Aw2, 'jca', [D(w, Aw2, 'breqtrrd', [linarith(w, Aw2, [lo, p02], '-u ( 3 / 2 ) <_ ( ( ( ( Re ` w ) + P ) / 2 ) - 1 )', closure=cl), reS], '-u ( 3 / 2 ) <_ ( Re ` %s )' % S_),
                                                D(w, Aw2, 'eqbrtrd', [reS, linarith(w, Aw2, [hi, p12], '( ( ( ( Re ` w ) + P ) / 2 ) - 1 ) <_ ( 3 / 2 )', closure=cl)], '( Re ` %s ) <_ ( 3 / 2 )' % S_)],
                                          '( -u ( 3 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 3 / 2 ) )' % (S_, S_)),
                                  D(w, Aw2, 'absled', [rsr, cl.mem('( 3 / 2 )', 'RR')], '( ( abs ` ( Re ` %s ) ) <_ ( 3 / 2 ) <-> ( -u ( 3 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 3 / 2 ) ) )' % (S_, S_, S_))],
             '( abs ` ( Re ` %s ) ) <_ ( 3 / 2 )' % S_)
    cl.have('( abs ` ( Re ` %s ) )' % S_, 'RR', D(w, Aw2, 'abscld', [D(w, Aw2, 'recnd', [rsr], '( Re ` %s ) e. CC' % S_)], '( abs ` ( Re ` %s ) ) e. RR' % S_))
    rle = linarith(w, Aw2, [ab], '( ( abs ` ( Re ` %s ) ) + 1 ) <_ %s' % (S_, R5), closure=cl)
    PIB = LE.tsub(L.split_imp(SE['zl3pib'])[1], {'G': GR, 'K': KT, 'B': BB, 'S': S_, 'R': R5})
    pib = D(w, Aw2, 'syl2anc', [L2(phr, LE.PHR), D(w, Aw2, '3jca', [sc_, L2(r5, '%s e. RR' % R5), rle], '( %s e. CC /\\ %s e. RR /\\ ( ( abs ` ( Re ` %s ) ) + 1 ) <_ %s )' % (S_, R5, S_, R5)),
                                w.inst('zl3pib')], PIB)
    IV = '( ~~>r ` %s )' % LE.IMR(S_)
    bnd = D(w, Aw2, 'simprd', [pib], '( abs ` %s ) <_ %s' % (IV, SMJ))
    ev = w.s([ral], 'r19.21bi', '( %s -> %s = %s )' % (Aw, LE.ILG('C', 'w', 'P'), IV))
    b2 = D(w, Aw2, 'eqbrtrd', [D(w, Aw2, 'fveq2d', [ad(w, Aw2, ev, '%s = %s' % (LE.ILG('C', 'w', 'P'), IV))], '( abs ` %s ) = ( abs ` %s )' % (LE.ILG('C', 'w', 'P'), IV)), bnd],
           '( abs ` %s ) <_ %s' % (LE.ILG('C', 'w', 'P'), SMJ))
    BODY = lambda c: 'A. w e. CC ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ %s )' % (LE.ILG('C', 'w', 'P'), c)
    ral2 = D(w, A, 'ralrimiva', [D(w, Aw, 'ex', [b2], '( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ %s )' % (LE.ILG('C', 'w', 'P'), SMJ))], BODY(SMJ))
    csub = w.s([w.s([w.s([], 'breq2', '( c = %s -> ( ( abs ` %s ) <_ c <-> ( abs ` %s ) <_ %s ) )' % (SMJ, LE.ILG('C', 'w', 'P'), LE.ILG('C', 'w', 'P'), SMJ))], 'imbi2d',
                     '( c = %s -> ( ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ c ) <-> ( ( -u 1 <_ ( Re ` w ) /\\ ( Re ` w ) <_ 3 ) -> ( abs ` %s ) <_ %s ) ) )'
                     % (SMJ, LE.ILG('C', 'w', 'P'), LE.ILG('C', 'w', 'P'), SMJ))], 'ralbidv', '( c = %s -> ( %s <-> %s ) )' % (SMJ, BODY('c'), BODY(SMJ)))
    fin = w.s([smr, ral2, w.s([csub], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. c e. RR %s )' % (SMJ, BODY(SMJ), BODY('c')))], 'syl2anc', '( %s -> E. c e. RR %s )' % (A, BODY('c')))
    w.qed([fin], 'idi', SE['zl3ilb'])
    goe(w)
