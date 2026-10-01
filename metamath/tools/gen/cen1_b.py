"""Sortie CEN1: the real Lambda series at 1 + U (cenvmb) and comparison convergence (cencvg)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen1lib import *
from cl import split_imp
from c9lib import top_and
from congr import mptval

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def vmseq(Z, n='n'):
    return '( %s e. NN |-> ( ( Lam ` %s ) x. ( %s ^c -u %s ) ) )' % (n, n, n, Z)


def gen_vmb():
    w = W('cenvmb', 'The real Lambda series at ` 1 + U ` is real and its real part is at most ` ( 5 / 4 ) / U + 5 ` (Lean Census ` LSeries_ofReal_eq ` with ` tsum_vonMangoldt_rpow_le ` , whose ` 1 / u + 2 ` is ZC1 ~ vmsharp ).')
    A0, C0 = split_imp(S['cenvmb'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    Z = '( 1 + U )'
    up = s([], 'simpl', 'U e. RR+'); ur = s([up], 'rpred', 'U e. RR')
    zr = s([s([], '1red', '1 e. RR'), ur], 'readdcld', '%s e. RR' % Z)
    zc = s([zr], 'recnd', '%s e. CC' % Z)
    rz = s([zr], 'rered', '( Re ` %s ) = %s' % (Z, Z))
    z1 = s([s([], '1red', '1 e. RR'), up], 'ltaddrpd', '1 < %s' % Z)
    z1r = s([z1, rz], 'breqtrrd', '1 < ( Re ` %s )' % Z)
    cv = s([zc, z1r, w.inst('zrvmc')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % vmseq(Z))
    A1 = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % A1)
    BODY = '( ( Lam ` n ) x. ( n ^c -u %s ) )' % Z
    VAL = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % Z
    lz = w.s([], 'simpl', '( %s -> %s )' % (A1, A0))
    zr1 = w.s([lz, zr], 'syl', '( %s -> %s e. RR )' % (A1, Z))
    vr = w.s([w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % A1),
              w.s([w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % A1), w.s([zr1], 'renegcld', '( %s -> -u %s e. RR )' % (A1, Z))], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (A1, Z))],
                  'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (A1, Z))], 'remulcld', '( %s -> %s e. RR )' % (A1, VAL))
    fv, val = mptval(w, A1, 'n', 'NN', BODY, 'k', kn, exs=w.s([vr], 'elexd', '( %s -> %s e. _V )' % (A1, VAL)))
    assert val == VAL, val
    SM = VM(Z)
    sr = s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([], '1zzd', '1 e. ZZ'), fv, vr, cv], 'isumrecl', '%s e. RR' % SM)
    rs = s([sr], 'rered', '( Re ` %s ) = %s' % (SM, SM))
    vb = s([w.inst('vmsharp')], 'id', 'x') if False else w.s([], 'vmsharp', '( %s -> %s <_ ( ( ( 5 / 4 ) / U ) + 5 ) )' % (A0, SM))
    bd = s([rs, vb], 'eqbrtrd', '( Re ` %s ) <_ ( ( ( 5 / 4 ) / U ) + 5 )' % SM)
    w.qed([sr, bd], 'jca', S['cenvmb'])
    return run(w)


def gen_cvg():
    w = W('cencvg', 'Convergence of ` sum B k ^ -S ` from ` abs B <_ C Lam ( k ) ` on ` 1 < Re S ` (Lean Census ` summable_term_of_le ` ; ~ cvgcmpce against ZR ~ zrvmc at ` Re S ` ).')
    PH = 'ph'
    h = {}
    for i in range(1, 5):
        h[i] = w.s([], 'cencvg.%d' % i, S['cencvg.%d' % i], name='h%d' % i)
    s = lambda hh, r, f: w.s(hh, r, '( ph -> %s )' % f)
    sc = s([h[1]], 'simpld', 'S e. CC'); s1 = s([h[1]], 'simprd', '1 < ( Re ` S )')
    RS = '( Re ` S )'
    rsr = s([sc], 'recld', '%s e. RR' % RS)
    rrs = s([rsr], 'rered', '( Re ` %s ) = %s' % (RS, RS))
    cv = s([s([rsr], 'recnd', '%s e. CC' % RS), s([s1, rrs], 'breqtrrd', '1 < ( Re ` %s )' % RS), w.inst('zrvmc')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % vmseq(RS))
    A1 = '( ph /\\ k e. NN )'
    a = lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (A1, f))
    kn = a([], 'simpr', 'k e. NN')
    rsr1 = a([a([], 'simpl', 'ph'), rsr], 'syl', '%s e. RR' % RS)
    krp = a([kn], 'nnrpd', 'k e. RR+')
    FV = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % RS
    lr = a([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')
    cpr = a([krp, a([rsr1], 'renegcld', '-u %s e. RR' % RS)], 'rpcxpcld', '( k ^c -u %s ) e. RR+' % RS)
    fr = a([lr, a([cpr], 'rpred', '( k ^c -u %s ) e. RR' % RS)], 'remulcld', '%s e. RR' % FV)
    fv, val = mptval(w, A1, 'n', 'NN', '( ( Lam ` n ) x. ( n ^c -u %s ) )' % RS, 'k', kn, exs=a([fr], 'elexd', '%s e. _V' % FV), gen=w.g)
    frr = a([fv, fr], 'eqeltrd', '( %s ` k ) e. RR' % vmseq(RS))
    GB = '( B x. ( k ^c -u S ) )'
    GM = '( k e. NN |-> %s )' % GB
    sc1 = a([a([], 'simpl', 'ph'), sc], 'syl', 'S e. CC')
    nsc = a([sc1], 'negcld', '-u S e. CC')
    kc = a([kn], 'nncnd', 'k e. CC'); kne = a([kn], 'nnne0d', 'k =/= 0')
    cpc = a([kc, kne, nsc], 'cxpcld', '( k ^c -u S ) e. CC') if False else a([kc, nsc], 'cxpcld', '( k ^c -u S ) e. CC')
    gbc = a([h[3], cpc], 'mulcld', '%s e. CC' % GB)
    gv = w.s([s([], 'eqidd', '%s = %s' % (GM, GM)), a([gbc], 'elexd', '%s e. _V' % GB)], 'fvmpt2d', '( %s -> ( %s ` k ) = %s )' % (A1, GM, GB))
    gc = a([gv, gbc], 'eqeltrd', '( %s ` k ) e. CC' % GM)
    # the bound on ( ph /\ k e. NN )
    ab = a([h[3], cpc], 'absmuld', '( abs ` %s ) = ( ( abs ` B ) x. ( abs ` ( k ^c -u S ) ) )' % GB)
    ac = a([krp, nsc, w.inst('abscxp')], 'syl2anc', '( abs ` ( k ^c -u S ) ) = ( k ^c ( Re ` -u S ) )')
    rn = a([sc1], 'renegd', '( Re ` -u S ) = -u %s' % RS)
    ac2 = a([ac, a([rn], 'oveq2d', '( k ^c ( Re ` -u S ) ) = ( k ^c -u %s )' % RS)], 'eqtrd', '( abs ` ( k ^c -u S ) ) = ( k ^c -u %s )' % RS)
    ab2 = a([ab, a([ac2], 'oveq2d', '( ( abs ` B ) x. ( abs ` ( k ^c -u S ) ) ) = ( ( abs ` B ) x. ( k ^c -u %s ) )' % RS)], 'eqtrd',
            '( abs ` %s ) = ( ( abs ` B ) x. ( k ^c -u %s ) )' % (GB, RS))
    cr1 = a([a([], 'simpl', 'ph'), h[2]], 'syl', 'C e. RR')
    CL = '( C x. ( Lam ` k ) )'
    le1 = a([a([h[3]], 'abscld', '( abs ` B ) e. RR'), a([cr1, lr], 'remulcld', '%s e. RR' % CL), a([cpr], 'rpred', '( k ^c -u %s ) e. RR' % RS), a([cpr], 'rpge0d', '0 <_ ( k ^c -u %s )' % RS), h[4]],
             'lemul1ad', '( ( abs ` B ) x. ( k ^c -u %s ) ) <_ ( %s x. ( k ^c -u %s ) )' % (RS, CL, RS))
    as_ = a([a([cr1], 'recnd', 'C e. CC'), a([lr], 'recnd', '( Lam ` k ) e. CC'), a([a([cpr], 'rpred', '( k ^c -u %s ) e. RR' % RS)], 'recnd', '( k ^c -u %s ) e. CC' % RS)],
            'mulassd', '( %s x. ( k ^c -u %s ) ) = ( C x. %s )' % (CL, RS, FV))
    le2 = a([le1, as_], 'breqtrd', '( ( abs ` B ) x. ( k ^c -u %s ) ) <_ ( C x. %s )' % (RS, FV))
    le3 = a([ab2, le2], 'eqbrtrd', '( abs ` %s ) <_ ( C x. %s )' % (GB, FV))
    le4 = a([a([gv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (GM, GB)), le3], 'eqbrtrd', '( abs ` ( %s ` k ) ) <_ ( C x. %s )' % (GM, FV))
    le5 = a([le4, a([fv], 'oveq2d', '( C x. ( %s ` k ) ) = ( C x. %s )' % (vmseq(RS), FV))], 'breqtrrd', '( abs ` ( %s ` k ) ) <_ ( C x. ( %s ` k ) )' % (GM, vmseq(RS)))
    # transfer to the letter m (cvgcmpce needs $d k G)
    Qk = '( abs ` ( %s ` k ) ) <_ ( C x. ( %s ` k ) )' % (GM, vmseq(RS))
    Qm = '( abs ` ( %s ` m ) ) <_ ( C x. ( %s ` m ) )' % (GM, vmseq(RS))
    ral = s([le5], 'ralrimiva', 'A. k e. NN %s' % Qk)
    n3 = w.s([w.s([], 'nfmpt1', 'F/_ k %s' % GM), w.s([], 'nfcv', 'F/_ k m')], 'nffv', 'F/_ k ( %s ` m )' % GM)
    n5 = w.s([w.s([], 'nfcv', 'F/_ k abs'), n3], 'nffv', 'F/_ k ( abs ` ( %s ` m ) )' % GM)
    n8 = w.s([n5, w.s([], 'nfcv', 'F/_ k <_'), w.s([], 'nfcv', 'F/_ k ( C x. ( %s ` m ) )' % vmseq(RS))], 'nfbr', 'F/ k %s' % Qm)
    e2 = w.s([w.s([], 'fveq2', '( k = m -> ( %s ` k ) = ( %s ` m ) )' % (GM, GM))], 'fveq2d', '( k = m -> ( abs ` ( %s ` k ) ) = ( abs ` ( %s ` m ) ) )' % (GM, GM))
    e4 = w.s([w.s([], 'fveq2', '( k = m -> ( %s ` k ) = ( %s ` m ) )' % (vmseq(RS), vmseq(RS)))], 'oveq2d', '( k = m -> ( C x. ( %s ` k ) ) = ( C x. ( %s ` m ) ) )' % (vmseq(RS), vmseq(RS)))
    e5 = w.s([e2, e4], 'breq12d', '( k = m -> ( %s <-> %s ) )' % (Qk, Qm))
    rs = w.s([n8, e5], 'rspc', '( m e. NN -> ( A. k e. NN %s -> %s ) )' % (Qk, Qm))
    A2 = '( ph /\\ m e. ( ZZ>= ` 1 ) )'
    m2 = w.s([w.s([], 'simpr', '( %s -> m e. ( ZZ>= ` 1 ) )' % A2), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrrdi', '( %s -> m e. NN )' % A2)
    le6 = w.s([m2, w.s([w.s([], 'simpl', '( %s -> ph )' % A2), ral], 'syl', '( %s -> A. k e. NN %s )' % (A2, Qk)), rs], 'sylc', '( %s -> %s )' % (A2, Qm))
    A3 = '( ph /\\ m e. NN )'
    mn = w.s([], 'simpr', '( %s -> m e. NN )' % A3)
    rs3 = w.s([w.s([], 'simpl', '( %s -> ph )' % A3), rsr], 'syl', '( %s -> %s e. RR )' % (A3, RS))
    FVm = '( ( Lam ` m ) x. ( m ^c -u %s ) )' % RS
    frm = w.s([w.s([mn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` m ) e. RR )' % A3),
               w.s([w.s([w.s([mn], 'nnrpd', '( %s -> m e. RR+ )' % A3), w.s([rs3], 'renegcld', '( %s -> -u %s e. RR )' % (A3, RS))], 'rpcxpcld', '( %s -> ( m ^c -u %s ) e. RR+ )' % (A3, RS))],
                   'rpred', '( %s -> ( m ^c -u %s ) e. RR )' % (A3, RS))], 'remulcld', '( %s -> %s e. RR )' % (A3, FVm))
    fvm, _ = mptval(w, A3, 'n', 'NN', '( ( Lam ` n ) x. ( n ^c -u %s ) )' % RS, 'm', mn, exs=w.s([frm], 'elexd', '( %s -> %s e. _V )' % (A3, FVm)), gen=w.g)
    frr3 = w.s([fvm, frm], 'eqeltrd', '( %s -> ( %s ` m ) e. RR )' % (A3, vmseq(RS)))
    gf = s([gbc], 'fmptd', '%s : NN --> CC' % GM)
    gc3 = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % A3), gf], 'syl', '( %s -> %s : NN --> CC )' % (A3, GM)), mn], 'ffvelcdmd', '( %s -> ( %s ` m ) e. CC )' % (A3, GM))
    w.qed([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), frr3, gc3, cv, h[2], le6], 'cvgcmpce', S['cencvg'])
    return run(w)


if __name__ == '__main__':
    gen_vmb()
    gen_cvg()
