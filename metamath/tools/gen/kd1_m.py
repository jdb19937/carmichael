"""Sortie KD1: the twisted log-power series on Re S = 1 + E is bounded by the diagonal (kdlsb)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from kd1_k import mval

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_lsb():
    w = W('kdlsb', 'Lean ` KDerivDetect.norm_LSeries_log_pow_le ` : on ` Re S = 1 + E ` the series ` sum ( log n ) ^ K chi ( n ) Lam ( n ) n ^ -u S ` converges and is at most the diagonal ` sum Lam ( n ) ( log n ) ^ K n ^ -u ( 1 + E ) ` (for ` E <_ 1 ` ; ` kdterm ` , ` kddiag ` ).')
    A0 = S['kdlsb'].split(' -> ( seq')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simp1', NXH)
    ee = s([], 'simp2', '( E e. RR+ /\\ E <_ 1 )'); ep = s([ee], 'simpld', 'E e. RR+'); e1 = s([ee], 'simprd', 'E <_ 1')
    sg = s([], 'simp3', '( S e. CC /\\ ( Re ` S ) = ( 1 + E ) /\\ K e. NN0 )')
    sc = s([sg], 'simp1d', 'S e. CC'); rs = s([sg], 'simp2d', '( Re ` S ) = ( 1 + E )'); kk = s([sg], 'simp3d', 'K e. NN0')
    er = s([ep], 'rpred', 'E e. RR')
    H2 = '( E / 2 )'
    h2 = s([ep], 'rphalfcld', '%s e. RR+' % H2)
    c = Closure(w, A0, {'E': ('RR', er)})
    import lin
    h21 = lin.linarith(w, A0, [e1, s([ep], 'rpgt0d', '0 < E')], '%s <_ 1' % H2, closure=c)
    dg = s([s([h2, h2, h21], '3jca', '( %s e. RR+ /\\ %s e. RR+ /\\ %s <_ 1 )' % (H2, H2, H2)), kk, w.inst('kddiag')], 'syl2anc',
           '( %s e. dom ~~> /\\ %s <_ ( ( ( ! ` K ) / ( %s ^ K ) ) x. ( ( ( 5 / 4 ) / %s ) + 5 ) ) )' % (
               DIAGSEQ('K', '( 1 + ( %s + %s ) )' % (H2, H2)), DIAG('K', '( 1 + ( %s + %s ) )' % (H2, H2)), H2, H2))
    dcv0 = s([dg], 'simpld', '%s e. dom ~~>' % DIAGSEQ('K', '( 1 + ( %s + %s ) )' % (H2, H2)))
    hh = s([s([er], 'recnd', 'E e. CC')], '2halvesd', '( %s + %s ) = E' % (H2, H2))
    cr, new = w.congr(DIAGSEQ('K', '( 1 + ( %s + %s ) )' % (H2, H2)), {}, A0, {}, rules={'( %s + %s )' % (H2, H2): ('E', hh)})
    assert new == DIAGSEQ('K', '( 1 + E )'), new
    dcv = s([cr, dcv0], 'eleq1d' if False else 'T.', 'T.') if False else s([dcv0, s([cr], 'eleq1d', '( %s e. dom ~~> <-> %s e. dom ~~> )' % (DIAGSEQ('K', '( 1 + ( %s + %s ) )' % (H2, H2)), new))], 'mpbid', '%s e. dom ~~>' % new)
    F = '( n e. NN |-> ( ( ( Lam ` n ) x. ( ( log ` n ) ^ K ) ) x. ( n ^c -u ( 1 + E ) ) ) )'
    TB = lambda x: '( ( ( ( log ` %s ) ^ K ) x. ( %s x. ( Lam ` %s ) ) ) x. ( %s ^c -u S ) )' % (x, CHV(x), x, x)
    FB = lambda x: '( ( ( Lam ` %s ) x. ( ( log ` %s ) ^ K ) ) x. ( %s ^c -u ( 1 + E ) ) )' % (x, x, x)
    AB = lambda x: '( abs ` %s )' % TB(x)
    G = '( n e. NN |-> %s )' % TB('n')
    AG = '( n e. NN |-> %s )' % AB('n')
    def block(Ak, kn):
        t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
        ad = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Ak, formula_of(w, st).split(' -> ', 1)[1][:-2]))
        tb = t([ad(nx), t([ad(sc), ad(kk), kn], '3jca', '( S e. CC /\\ K e. NN0 /\\ k e. NN )'), w.inst('kdterm')], 'syl2anc',
               '( abs ` %s ) <_ ( ( ( Lam ` k ) x. ( ( log ` k ) ^ K ) ) x. ( k ^c -u ( Re ` S ) ) )' % TB('k'))
        rsk = t([t([ad(rs)], 'negeqd', '-u ( Re ` S ) = -u ( 1 + E )')], 'oveq2d', '( k ^c -u ( Re ` S ) ) = ( k ^c -u ( 1 + E ) )')
        tb2 = t([tb, t([rsk], 'oveq2d', '( ( ( Lam ` k ) x. ( ( log ` k ) ^ K ) ) x. ( k ^c -u ( Re ` S ) ) ) = %s' % FB('k'))], 'breqtrd', '( abs ` %s ) <_ %s' % (TB('k'), FB('k')))
        kr = t([kn], 'nnrpd', 'k e. RR+')
        lr = t([kr], 'relogcld', '( log ` k ) e. RR')
        lam = t([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')
        fbr = t([t([lam, t([lr, ad(kk)], 'reexpcld', '( ( log ` k ) ^ K ) e. RR')], 'remulcld', '( ( Lam ` k ) x. ( ( log ` k ) ^ K ) ) e. RR'),
                 t([t([kr, t([t([w.s([], '1red', '( %s -> 1 e. RR )' % Ak), ad(er)], 'readdcld', '( 1 + E ) e. RR')], 'renegcld', '-u ( 1 + E ) e. RR')], 'rpcxpcld', '( k ^c -u ( 1 + E ) ) e. RR+')], 'rpred', '( k ^c -u ( 1 + E ) ) e. RR')],
                'remulcld', '%s e. RR' % FB('k'))
        chk = t([t([ad(nx), kn], 'jca', '( %s /\\ k e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CHV('k'))
        tbc = t([t([t([t([lr], 'recnd', '( log ` k ) e. CC'), ad(kk)], 'expcld', '( ( log ` k ) ^ K ) e. CC'), t([chk, t([lam], 'recnd', '( Lam ` k ) e. CC')], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHV('k'))],
                   'mulcld', '( ( ( log ` k ) ^ K ) x. ( %s x. ( Lam ` k ) ) ) e. CC' % CHV('k')), t([t([kn], 'nncnd', 'k e. CC'), t([ad(sc)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')],
                'mulcld', '%s e. CC' % TB('k'))
        abr = t([tbc], 'abscld', '%s e. RR' % AB('k')); ab0 = t([tbc], 'absge0d', '0 <_ %s' % AB('k'))
        return dict(tb2=tb2, fbr=fbr, tbc=tbc, abr=abr, ab0=ab0)
    def val(ante, kn, M, BOD, cl_):
        idx = w.s([], 'id', '( n = k -> n = k )')
        st, new = w.congr(BOD('n'), {'n': 'k'}, 'n = k', {'n': idx})
        return fvmd(w, ante, M, 'k', BOD('k'), kn, cl_, st, var='n')
    Ak = '( %s /\\ k e. NN )' % A0
    knA = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    bA = block(Ak, knA)
    Au = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A0
    knU = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Au), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> k e. NN )' % Au)
    bU = block(Au, knU)
    fA = val(Ak, knA, F, FB, bA['fbr']); gA = val(Ak, knA, G, TB, bA['tbc']); aA = val(Ak, knA, AG, AB, bA['abr'])
    fU = val(Au, knU, F, FB, bU['fbr']); gU = val(Au, knU, G, TB, bU['tbc']); aU = val(Au, knU, AG, AB, bU['abr'])
    uz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A0)
    onez = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0)
    fr = w.s([fA, bA['fbr']], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, F))
    ar = w.s([aA, bA['abr']], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, AG))
    gc = w.s([gA, bA['tbc']], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G))
    a0U = w.s([aU, bU['ab0']], 'breqtrrd', '( %s -> 0 <_ ( %s ` k ) )' % (Au, AG))
    alU = w.s([w.s([aU, bU['tb2']], 'eqbrtrd', '( %s -> ( %s ` k ) <_ %s )' % (Au, AG, FB('k'))), fU], 'breqtrrd', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Au, AG, F))
    acv = w.s([uz, one, fr, ar, dcv, a0U, alU], 'cvgcmp', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, AG))
    # G converges: |G k| <_ 1 x. F k
    gle = w.s([w.s([w.s([gU], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = %s )' % (Au, G, AB('k'))), bU['tb2']], 'eqbrtrd', '( %s -> ( abs ` ( %s ` k ) ) <_ %s )' % (Au, G, FB('k'))),
               w.s([w.s([fU], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (Au, FB('k'), F)), w.s([w.s([w.s([fU, bU['fbr']], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Au, F))], 'recnd', '( %s -> ( %s ` k ) e. CC )' % (Au, F))], 'mullidd',
                                                                                                                                                  '( %s -> ( 1 x. ( %s ` k ) ) = ( %s ` k ) )' % (Au, F, F))],
                   'eqtr4d', '( %s -> %s = ( 1 x. ( %s ` k ) ) )' % (Au, FB('k'), F))], 'breqtrd', '( %s -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) )' % (Au, G, F))
    gcv = w.s([uz, one, fr, gc, dcv, w.s([], '1red', '( %s -> 1 e. RR )' % A0), gle], 'cvgcmpce', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, G))
    # the sums
    SG = 'sum_ k e. NN %s' % TB('k'); SA = 'sum_ k e. NN %s' % AB('k'); SF = 'sum_ k e. NN %s' % FB('k')
    cg = w.s([uz, onez, gA, bA['tbc'], gcv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, G, SG))
    ca = w.s([uz, onez, aA, w.s([bA['abr']], 'recnd', '( %s -> %s e. CC )' % (Ak, AB('k'))), acv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, AG, SA))
    ab = w.s([uz, cg, ca, onez, gc, w.s([aA, w.s([gA], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = %s )' % (Ak, G, AB('k')))], 'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, AG, G))],
             'iserabs', '( %s -> ( abs ` %s ) <_ %s )' % (A0, SG, SA))
    le = w.s([uz, onez, aA, bA['abr'], fA, bA['fbr'], bA['tb2'], acv, dcv], 'isumle', '( %s -> %s <_ %s )' % (A0, SA, SF))
    sgr = w.s([uz, onez, aA, bA['abr'], acv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SA))
    sfr = w.s([uz, onez, fA, bA['fbr'], dcv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SF))
    agr = s([s([cg, w.inst('climcl')], 'syl', '%s e. CC' % SG)], 'abscld', '( abs ` %s ) e. RR' % SG)
    tot = s([agr, sgr, sfr, ab, le], 'letrd', '( abs ` %s ) <_ %s' % (SG, SF))
    # binder k -> n
    def cbv(BOD):
        idk = w.s([], 'id', '( k = n -> k = n )')
        ck, nk = w.congr(BOD('k'), {'k': 'n'}, 'k = n', {'k': idk})
        return w.s([ck], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (BOD('k'), BOD('n')))
    cG = cbv(TB); cF = cbv(FB)
    fin = s([s([w.s([cG], 'a1i', '( %s -> %s = sum_ n e. NN %s )' % (A0, SG, TB('n')))], 'fveq2d', '( abs ` %s ) = ( abs ` sum_ n e. NN %s )' % (SG, TB('n'))), tot,
             w.s([cF], 'a1i', '( %s -> %s = sum_ n e. NN %s )' % (A0, SF, FB('n')))], '3brtr3d', '( abs ` sum_ n e. NN %s ) <_ sum_ n e. NN %s' % (TB('n'), FB('n')))
    w.qed([gcv, fin], 'jca', S['kdlsb'])
    return run(w)


if __name__ == '__main__':
    gen_lsb()
