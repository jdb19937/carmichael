"""EF1 sections 4-5, the assembly: ef1an, ef1pt, ef1psb.
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_g.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from lin import linarith, lineq
from cl import formula_of

only = sys.argv[1:]

# ---------------------------------------------------------------- ef1an: | chi ( K ) Lam ( K ) Z | <_ Lam ( K ) | Z |
if __name__ == '__main__' and (not only or 'ef1an' in only):
    w = W('ef1an', 'A twisted von Mangoldt coefficient is at most ` Lam ( K ) ` in modulus: ` | chi ( K ) Lam ( K ) Z | <_ Lam ( K ) | Z | ` '
          '( ~ lchvmtm at ` 0 ` ; Lean ` norm_perron_term_le ` ).')
    A0 = STATEMENTS['ef1an'].split(' -> ( abs')[0][2:]
    nx = D(w, A0, 'simpl', [], NX); kn = D(w, A0, 'simprl', [], 'K e. NN'); zc = D(w, A0, 'simprr', [], 'Z e. CC')
    c0 = a1(w, A0, '0cn', '0 e. CC')
    tm = w.s([D(w, A0, 'jca', [nx, D(w, A0, 'jca', [kn, c0], '( K e. NN /\\ 0 e. CC )')], '( %s /\\ ( K e. NN /\\ 0 e. CC ) )' % NX), w.inst('lchvmtm')], 'syl',
             '( %s -> ( abs ` ( %s x. ( K ^c -u 0 ) ) ) <_ ( ( Lam ` K ) x. ( K ^c -u ( Re ` 0 ) ) ) )' % (A0, AN('K')))
    kc = D(w, A0, 'nncnd', [kn], 'K e. CC')
    k0 = w.s([w.s([w.s([w.s([], 'neg0', '-u 0 = 0')], 'oveq2i', '( K ^c -u 0 ) = ( K ^c 0 )')], 'a1i', '( %s -> ( K ^c -u 0 ) = ( K ^c 0 ) )' % A0), w.s([kc, w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A0)],
             'eqtrd', '( %s -> ( K ^c -u 0 ) = 1 )' % A0)
    rn = w.s([w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'negeqi', '-u ( Re ` 0 ) = -u 0'), w.s([], 'neg0', '-u 0 = 0')], 'eqtri', '-u ( Re ` 0 ) = 0')
    r1 = w.s([w.s([rn], 'oveq2i', '( K ^c -u ( Re ` 0 ) ) = ( K ^c 0 )')], 'a1i', '( %s -> ( K ^c -u ( Re ` 0 ) ) = ( K ^c 0 ) )' % A0)
    r0 = w.s([r1, w.s([kc, w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A0)], 'eqtrd', '( %s -> ( K ^c -u ( Re ` 0 ) ) = 1 )' % A0)
    qf = w.s([nx, w.inst('lchvmf')], 'syl', '( %s -> ( q e. NN |-> %s ) : NN --> CC )' % (A0, AN('q')))
    anc = w.s([w.s([kn, w.inst('lchvmval')], 'syl', '( %s -> ( ( q e. NN |-> %s ) ` K ) = %s )' % (A0, AN('q'), AN('K'))), w.s([qf, kn], 'ffvelcdmd', '( %s -> ( ( q e. NN |-> %s ) ` K ) e. CC )' % (A0, AN('q')))],
              'eqeltrrd', '( %s -> %s e. CC )' % (A0, AN('K')))
    lam = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` K ) e. RR )' % A0)
    a1_ = w.s([w.s([w.s([k0], 'oveq2d', '( %s -> ( %s x. ( K ^c -u 0 ) ) = ( %s x. 1 ) )' % (A0, AN('K'), AN('K'))), D(w, A0, 'mulridd', [anc], '( %s x. 1 ) = %s' % (AN('K'), AN('K')))], 'eqtrd',
                   '( %s -> ( %s x. ( K ^c -u 0 ) ) = %s )' % (A0, AN('K'), AN('K')))], 'fveq2d', '( %s -> ( abs ` ( %s x. ( K ^c -u 0 ) ) ) = ( abs ` %s ) )' % (A0, AN('K'), AN('K')))
    b1 = w.s([w.s([r0], 'oveq2d', '( %s -> ( ( Lam ` K ) x. ( K ^c -u ( Re ` 0 ) ) ) = ( ( Lam ` K ) x. 1 ) )' % A0), D(w, A0, 'mulridd', [D(w, A0, 'recnd', [lam], '( Lam ` K ) e. CC')], '( ( Lam ` K ) x. 1 ) = ( Lam ` K )')],
             'eqtrd', '( %s -> ( ( Lam ` K ) x. ( K ^c -u ( Re ` 0 ) ) ) = ( Lam ` K ) )' % A0)
    ale = w.s([w.s([a1_, tm], 'eqbrtrrd', '( %s -> ( abs ` %s ) <_ ( ( Lam ` K ) x. ( K ^c -u ( Re ` 0 ) ) ) )' % (A0, AN('K'))), b1], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( Lam ` K ) )' % (A0, AN('K')))
    am = D(w, A0, 'absmuld', [anc, zc], '( abs ` ( %s x. Z ) ) = ( ( abs ` %s ) x. ( abs ` Z ) )' % (AN('K'), AN('K')))
    le = D(w, A0, 'lemul1ad', [D(w, A0, 'abscld', [anc], '( abs ` %s ) e. RR' % AN('K')), lam, D(w, A0, 'abscld', [zc], '( abs ` Z ) e. RR'), D(w, A0, 'absge0d', [zc], '0 <_ ( abs ` Z )'), ale],
           '( ( abs ` %s ) x. ( abs ` Z ) ) <_ ( ( Lam ` K ) x. ( abs ` Z ) )' % AN('K'))
    w.qed([am, le], 'eqbrtrd', STATEMENTS['ef1an'])
    go(w, only)


def uzge(w, A, Mz, Nz, le, M_, N_):
    """( A -> N_ e. ( ZZ>= ` M_ ) ) from M_, N_ e. ZZ and M_ <_ N_"""
    return w.s([D(w, A, '3jca', [Mz, Nz, le], '( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s )' % (M_, N_, M_, N_)),
                w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (N_, M_, M_, N_, M_, N_))], 'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (A, N_, M_))


# ---------------------------------------------------------------- ef1pt: the partial sums
if __name__ == '__main__' and (not only or 'ef1pt' in only):
    sys.argv = sys.argv[:1]
    from ef1_f import yctx, lift, tpiabs
    w = W('ef1pt', 'The Perron-weighted partial sums track ` psi ( y , chi ) ` : for ` M >_ 2 floor y + 2 ` , '
          '` | sum_ ( n <_ M ) chi ( n ) Lam ( n ) K ( y / n ) - 2 pi i psi ( y , chi ) | <_ 310 y L ^ 2 / T + 16 L ^ 2 ` : the sum split at '
          '` floor y - 1 ` , ` floor y ` , ` floor y + 1 ` and ` 2 floor y + 1 ` into the regions of ~ ef1lft , ~ ef1nr , ~ ef1mr , ~ ef1tl .')
    A0 = STATEMENTS['ef1pt'].split(' -> ( abs')[0][2:]
    nx = D(w, A0, 'simpll', [], NX); yt = D(w, A0, 'simplr', [], YT); mz = D(w, A0, 'simpr', [], 'M e. ( ZZ>= ` %s )' % F2)
    d = yctx(w, A0, yt); cl = d['cl']
    F = FL; F1 = '( %s + 1 )' % F; FM = '( %s - 1 )' % F; F2p = '( %s + 2 )' % F; F21 = '( ( 2 x. %s ) + 1 )' % F
    mzz = w.s([mz, w.inst('eluzelz')], 'syl', '( %s -> M e. ZZ )' % A0)
    mge = w.s([mz, w.inst('eluzle')], 'syl', '( %s -> %s <_ M )' % (A0, F2))
    cl.leaf('M', 'RR', D(w, A0, 'zred', [mzz], 'M e. RR'))
    fz = d['fz']
    fmz = w.s([fz, w.inst('peano2zm')], 'syl', '( %s -> %s e. ZZ )' % (A0, FM))
    f1z = D(w, A0, 'peano2zd', [fz], '%s e. ZZ' % F1)
    f2pz = D(w, A0, 'zaddcld', [fz, a1(w, A0, '2z', '2 e. ZZ')], '%s e. ZZ' % F2p)
    f21z = D(w, A0, 'peano2zd', [D(w, A0, 'zmulcld', [a1(w, A0, '2z', '2 e. ZZ'), fz], '( 2 x. %s ) e. ZZ' % F)], '%s e. ZZ' % F21)
    f100 = linarith(w, A0, [d['y100'], d['flt']], '; 9 9 < %s' % F, closure=cl)
    tpc, tpa = tpiabs(w, A0)

    def nnof(C, to0, nin, lo, lo1):
        """( C -> n e. NN ) from nin: ( C -> n e. ( lo ... M ) ), lo1: ( A0 -> 1 <_ lo )"""
        nz = w.s([nin, w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % C)
        nl = w.s([nin, w.inst('elfzle1')], 'syl', '( %s -> %s <_ n )' % (C, lo))
        clc = Closure(w, C, {'n': ('RR', D(w, C, 'zred', [nz], 'n e. RR')), FL: ('RR', lift(w, C, to0, d['fr'], '%s e. RR' % FL))})
        n1 = linarith(w, C, [nl, lift(w, C, to0, lo1, '1 <_ %s' % lo)], '1 <_ n', closure=clc)
        return w.s([D(w, C, 'jca', [nz, n1], '( n e. ZZ /\\ 1 <_ n )'), w.s([], 'elnnz1', '( n e. NN <-> ( n e. ZZ /\\ 1 <_ n ) )')], 'sylibr', '( %s -> n e. NN )' % C)

    def tfacts(C, to0, kn, k):
        t = {}
        qv = w.s([kn, w.inst('lchvmval')], 'syl', '( %s -> ( ( q e. NN |-> %s ) ` %s ) = %s )' % (C, AN('q'), k, AN(k)))
        qf = w.s([w.s([to0, nx], 'syl', '( %s -> %s )' % (C, NX)), w.inst('lchvmf')], 'syl', '( %s -> ( q e. NN |-> %s ) : NN --> CC )' % (C, AN('q')))
        t['anc'] = w.s([qv, w.s([qf, kn], 'ffvelcdmd', '( %s -> ( ( q e. NN |-> %s ) ` %s ) e. CC )' % (C, AN('q'), k))], 'eqeltrrd', '( %s -> %s e. CC )' % (C, AN(k)))
        krp = D(w, C, 'nnrpd', [kn], '%s e. RR+' % k)
        t['kcc'] = w.s([D(w, C, 'rpdivcld', [lift(w, C, to0, d['yrp'], 'Y e. RR+'), krp], '( Y / %s ) e. RR+' % k), lift(w, C, to0, d['c0rp'], '%s e. RR+' % C0),
                        lift(w, C, to0, d['trp'], 'T e. RR+'), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (C, KC(k)))
        t['ptc'] = D(w, C, 'mulcld', [t['anc'], t['kcc']], '%s e. CC' % PTERM(k, C0))
        nxk = D(w, C, 'jca', [w.s([to0, nx], 'syl', '( %s -> %s )' % (C, NX)), D(w, C, 'jca', [kn, t['kcc']], '( %s e. NN /\\ %s e. CC )' % (k, KC(k)))], '( %s /\\ ( %s e. NN /\\ %s e. CC ) )' % (NX, k, KC(k)))
        t['bR'] = w.s([nxk, w.inst('ef1an')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (C, PTERM(k, C0), ER(k)))
        kmt = D(w, C, 'subcld', [t['kcc'], lift(w, C, to0, tpc, '%s e. CC' % TPI)], '( %s - %s ) e. CC' % (KC(k), TPI))
        t['kmt'] = kmt
        nxl = D(w, C, 'jca', [w.s([to0, nx], 'syl', '( %s -> %s )' % (C, NX)), D(w, C, 'jca', [kn, kmt], '( %s e. NN /\\ ( %s - %s ) e. CC )' % (k, KC(k), TPI))],
                '( %s /\\ ( %s e. NN /\\ ( %s - %s ) e. CC ) )' % (NX, k, KC(k), TPI))
        t['bL'] = w.s([nxl, w.inst('ef1an')], 'syl', '( %s -> ( abs ` ( %s x. ( %s - %s ) ) ) <_ %s )' % (C, AN(k), KC(k), TPI, EL(k)))
        return t

    PTn = PTERM('n', C0)
    one1 = a1(w, A0, '1z', '1 e. ZZ')
    cl1 = linarith(w, A0, [], '1 <_ 1', closure=cl)

    def ctxn(X, lo, lo1):
        C = '( %s /\\ n e. %s )' % (A0, X)
        to0 = w.s([], 'simpl', '( %s -> %s )' % (C, A0))
        nin = w.s([], 'simpr', '( %s -> n e. %s )' % (C, X))
        kn = nnof(C, to0, nin, lo, lo1)
        return C, to0, kn

    IM = '( 1 ... M )'
    C1, t01, kn1 = ctxn(IM, '1', cl1)
    tf1 = tfacts(C1, t01, kn1, 'n')
    # split ( 1 ... M ) at F - 1
    fmin = w.s([one1, mzz, fmz, linarith(w, A0, [f100], '1 <_ %s' % FM, closure=cl), linarith(w, A0, [mge, f100], '%s <_ M' % FM, closure=cl)], 'elfzd', '( %s -> %s e. %s )' % (A0, FM, IM))
    s1 = w.s([fmin, tf1['ptc']], 'ef1fzs', '( %s -> sum_ n e. %s %s = ( sum_ n e. ( 1 ... %s ) %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) )' % (A0, IM, PTn, FM, PTn, FM, PTn))
    np1 = D(w, A0, 'npcand', [D(w, A0, 'zcnd', [fz], '%s e. CC' % F), a1(w, A0, 'ax-1cn', '1 e. CC')], '( %s + 1 ) = %s' % (FM, F))
    s1b = w.s([w.s([np1], 'oveq1d', '( %s -> ( ( %s + 1 ) ... M ) = ( %s ... M ) )' % (A0, FM, F))], 'sumeq1d', '( %s -> sum_ n e. ( ( %s + 1 ) ... M ) %s = sum_ n e. ( %s ... M ) %s )' % (A0, FM, PTn, F, PTn))
    # peel off n = F and n = F + 1
    f1_ = D(w, A0, 'nnge1d', [d['fnn']], '1 <_ %s' % F)
    CF, t0F, knF = ctxn('( %s ... M )' % F, F, f1_)
    tfF = tfacts(CF, t0F, knF, 'n')
    muF = uzge(w, A0, fz, mzz, linarith(w, A0, [mge, f100], '%s <_ M' % F, closure=cl), F, 'M')

    def subk(a, b):
        return w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) = ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % (a, b, a, b))], 'fveq2d', '( %s = %s -> %s = %s )' % (a, b, XC(a), XC(b))),
                    w.s([], 'fveq2', '( %s = %s -> ( Lam ` %s ) = ( Lam ` %s ) )' % (a, b, a, b))], 'oveq12d', '( %s = %s -> %s = %s )' % (a, b, AN(a), AN(b)))

    def pts(a, b):
        yx = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( Y / %s ) = ( Y / %s ) )' % (a, b, a, b))], 'oveq1d', '( %s = %s -> ( ( Y / %s ) ^c z ) = ( ( Y / %s ) ^c z ) )' % (a, b, a, b))], 'oveq1d',
                      '( %s = %s -> ( ( ( Y / %s ) ^c z ) / z ) = ( ( ( Y / %s ) ^c z ) / z ) )' % (a, b, a, b))], 'mpteq2dv', '( %s = %s -> %s = %s )' % (a, b, PKF('( Y / %s )' % a), PKF('( Y / %s )' % b)))
        pl = w.s([yx], 'oveq1d', '( %s = %s -> %s = %s )' % (a, b, KC(a), KC(b)))
        return w.s([subk(a, b), pl], 'oveq12d', '( %s = %s -> %s = %s )' % (a, b, PTERM(a, C0), PTERM(b, C0)))

    s2 = w.s([muF, tfF['ptc'], pts('n', F)], 'fsum1p', '( %s -> sum_ n e. ( %s ... M ) %s = ( %s + sum_ n e. ( %s ... M ) %s ) )' % (A0, F, PTn, PTERM(F, C0), F1, PTn))
    f11 = linarith(w, A0, [f1_], '1 <_ %s' % F1, closure=cl)
    CG, t0G, knG = ctxn('( %s ... M )' % F1, F1, f11)
    tfG = tfacts(CG, t0G, knG, 'n')
    muG = uzge(w, A0, f1z, mzz, linarith(w, A0, [mge, f100], '%s <_ M' % F1, closure=cl), F1, 'M')
    s3 = w.s([muG, tfG['ptc'], pts('n', F1)], 'fsum1p', '( %s -> sum_ n e. ( %s ... M ) %s = ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) )' % (A0, F1, PTn, PTERM(F1, C0), F1, PTn))
    f12 = lineq(w, A0, '( %s + 1 )' % F1, F2p, closure=cl)
    s3b = w.s([w.s([f12], 'oveq1d', '( %s -> ( ( %s + 1 ) ... M ) = ( %s ... M ) )' % (A0, F1, F2p))], 'sumeq1d', '( %s -> sum_ n e. ( ( %s + 1 ) ... M ) %s = sum_ n e. ( %s ... M ) %s )' % (A0, F1, PTn, F2p, PTn))
    # split ( F + 2 ... M ) at 2 F + 1
    f2p1 = linarith(w, A0, [f1_], '1 <_ %s' % F2p, closure=cl)
    CH, t0H, knH = ctxn('( %s ... M )' % F2p, F2p, f2p1)
    tfH = tfacts(CH, t0H, knH, 'n')
    f21in = w.s([f2pz, mzz, f21z, linarith(w, A0, [f1_], '%s <_ %s' % (F2p, F21), closure=cl), linarith(w, A0, [mge, f100], '%s <_ M' % F21, closure=cl)], 'elfzd',
                '( %s -> %s e. ( %s ... M ) )' % (A0, F21, F2p))
    s4 = w.s([f21in, tfH['ptc']], 'ef1fzs', '( %s -> sum_ n e. ( %s ... M ) %s = ( sum_ n e. ( %s ... %s ) %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) )' % (A0, F2p, PTn, F2p, F21, PTn, F21, PTn))
    f22 = lineq(w, A0, '( %s + 1 )' % F21, F2, closure=cl)
    s4b = w.s([w.s([f22], 'oveq1d', '( %s -> ( ( %s + 1 ) ... M ) = ( %s ... M ) )' % (A0, F21, F2))], 'sumeq1d', '( %s -> sum_ n e. ( ( %s + 1 ) ... M ) %s = sum_ n e. ( %s ... M ) %s )' % (A0, F21, PTn, F2, PTn))
    # psi = sum_ ( 1 ... F - 1 ) + a_F
    CP, t0P, knP = ctxn('( 1 ... %s )' % F, '1', cl1)
    tfP = tfacts(CP, t0P, knP, 'n')
    fu1 = uzge(w, A0, one1, fz, f1_, '1', F)
    ps1 = w.s([fu1, tfP['anc'], subk('n', F)], 'fsumm1', '( %s -> %s = ( sum_ n e. ( 1 ... %s ) %s + %s ) )' % (A0, PSI, FM, AN('n'), AN(F)))

    IL1 = '( 1 ... %s )' % FM; IMD = '( %s ... %s )' % (F2p, F21); ITL = '( %s ... M )' % F2
    SL1 = 'sum_ n e. %s %s' % (IL1, PTn); PL = 'sum_ n e. %s %s' % (IL1, AN('n'))
    SMID = 'sum_ n e. %s %s' % (IMD, PTn); STL = 'sum_ n e. %s %s' % (ITL, PTn)
    TF = PTERM(F, C0); TG = PTERM(F1, C0)
    S = 'sum_ n e. %s %s' % (IM, PTn)
    R = '( %s + ( %s + %s ) )' % (TG, SMID, STL)
    CL_, t0L, knL = ctxn(IL1, '1', cl1)
    tfL = tfacts(CL_, t0L, knL, 'n')
    CM_, t0M, knM = ctxn(IMD, F2p, f2p1)
    tfM = tfacts(CM_, t0M, knM, 'n')
    f21_ = linarith(w, A0, [f1_], '1 <_ %s' % F2, closure=cl)
    CT_, t0T, knT = ctxn(ITL, F2, f21_)
    tfT = tfacts(CT_, t0T, knT, 'n')
    finL = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IL1)); finM = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IMD)); finT = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, ITL))
    slc = w.s([finL, tfL['ptc']], 'fsumcl', '( %s -> %s e. CC )' % (A0, SL1)); plc = w.s([finL, tfL['anc']], 'fsumcl', '( %s -> %s e. CC )' % (A0, PL))
    smc = w.s([finM, tfM['ptc']], 'fsumcl', '( %s -> %s e. CC )' % (A0, SMID)); stc = w.s([finT, tfT['ptc']], 'fsumcl', '( %s -> %s e. CC )' % (A0, STL))
    AF = '( %s ... M )' % F
    CFp = '( %s /\\ n = %s )' % (A0, F)
    tfF0 = tfacts(A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)), d['fnn'], F)
    f1nn = D(w, A0, 'peano2nnd', [d['fnn']], '%s e. NN' % F1)
    tfG0 = tfacts(A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)), f1nn, F1)
    rc = D(w, A0, 'addcld', [tfG0['ptc'], D(w, A0, 'addcld', [smc, stc], '( %s + %s ) e. CC' % (SMID, STL))], '%s e. CC' % R)
    # S = SL1 + ( TF + R )
    e_s = chain(w, A0, [S, '( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s )' % (SL1, FM, PTn), '( %s + sum_ n e. %s %s )' % (SL1, AF, PTn), '( %s + ( %s + sum_ n e. ( %s ... M ) %s ) )' % (SL1, TF, F1, PTn),
                        '( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) )' % (SL1, TF, TG, F1, PTn), '( %s + ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) )' % (SL1, TF, TG, F2p, PTn),
                        '( %s + ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) )' % (SL1, TF, TG, SMID, F21, PTn), '( %s + ( %s + %s ) )' % (SL1, TF, R)],
                [s1, w.s([s1b], 'oveq2d', '( %s -> ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) = ( %s + sum_ n e. %s %s ) )' % (A0, SL1, FM, PTn, SL1, AF, PTn)),
                 w.s([s2], 'oveq2d', '( %s -> ( %s + sum_ n e. %s %s ) = ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) )' % (A0, SL1, AF, PTn, SL1, TF, F1, PTn)),
                 w.s([w.s([s3], 'oveq2d', '( %s -> ( %s + sum_ n e. ( %s ... M ) %s ) = ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) )' % (A0, TF, F1, PTn, TF, TG, F1, PTn))], 'oveq2d',
                     '( %s -> ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) = ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) )' % (A0, SL1, TF, F1, PTn, SL1, TF, TG, F1, PTn)),
                 w.s([w.s([w.s([s3b], 'oveq2d', '( %s -> ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) = ( %s + sum_ n e. ( %s ... M ) %s ) )' % (A0, TG, F1, PTn, TG, F2p, PTn))], 'oveq2d',
                          '( %s -> ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) = ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) )' % (A0, TF, TG, F1, PTn, TF, TG, F2p, PTn))], 'oveq2d',
                     '( %s -> ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) = ( %s + ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) ) )' % (A0, SL1, TF, TG, F1, PTn, SL1, TF, TG, F2p, PTn)),
                 w.s([w.s([w.s([s4], 'oveq2d', '( %s -> ( %s + sum_ n e. ( %s ... M ) %s ) = ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) )' % (A0, TG, F2p, PTn, TG, SMID, F21, PTn))], 'oveq2d',
                          '( %s -> ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) = ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) )' % (A0, TF, TG, F2p, PTn, TF, TG, SMID, F21, PTn))], 'oveq2d',
                     '( %s -> ( %s + ( %s + ( %s + sum_ n e. ( %s ... M ) %s ) ) ) = ( %s + ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) ) )' % (A0, SL1, TF, TG, F2p, PTn, SL1, TF, TG, SMID, F21, PTn)),
                 w.s([w.s([w.s([w.s([s4b], 'oveq2d', '( %s -> ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) = ( %s + %s ) )' % (A0, SMID, F21, PTn, SMID, STL))], 'oveq2d',
                               '( %s -> ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) = %s )' % (A0, TG, SMID, F21, PTn, R))], 'oveq2d',
                          '( %s -> ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) = ( %s + %s ) )' % (A0, TF, TG, SMID, F21, PTn, TF, R))], 'oveq2d',
                     '( %s -> ( %s + ( %s + ( %s + ( %s + sum_ n e. ( ( %s + 1 ) ... M ) %s ) ) ) ) = ( %s + ( %s + %s ) ) )' % (A0, SL1, TF, TG, SMID, F21, PTn, SL1, TF, R))])
    TPL = '( %s x. %s )' % (TPI, PL); TAF = '( %s x. %s )' % (TPI, AN(F))
    tpsi = w.s([w.s([ps1], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( %s + %s ) ) )' % (A0, TPI, PSI, TPI, PL, AN(F))),
                D(w, A0, 'adddid', [tpc, plc, tfF0['anc']], '( %s x. ( %s + %s ) ) = ( %s + %s )' % (TPI, PL, AN(F), TPL, TAF))], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s + %s ) )' % (A0, TPI, PSI, TPL, TAF))
    X = '( %s - ( %s x. %s ) )' % (S, TPI, PSI)
    AL = '( %s - %s )' % (SL1, TPL); BF = '( %s - %s )' % (TF, TAF)
    tfr = D(w, A0, 'addcld', [tfF0['ptc'], rc], '( %s + %s ) e. CC' % (TF, R))
    tplc = D(w, A0, 'mulcld', [tpc, plc], '%s e. CC' % TPL); tafc = D(w, A0, 'mulcld', [tpc, tfF0['anc']], '%s e. CC' % TAF)
    xe = chain(w, A0, [X, '( ( %s + ( %s + %s ) ) - ( %s + %s ) )' % (SL1, TF, R, TPL, TAF), '( %s + ( ( %s + %s ) - %s ) )' % (AL, TF, R, TAF), '( %s + ( %s + %s ) )' % (AL, BF, R)],
               [w.s([e_s, tpsi], 'oveq12d', '( %s -> %s = ( ( %s + ( %s + %s ) ) - ( %s + %s ) ) )' % (A0, X, SL1, TF, R, TPL, TAF)),
                D(w, A0, 'addsub4d', [slc, tfr, tplc, tafc], '( ( %s + ( %s + %s ) ) - ( %s + %s ) ) = ( %s + ( ( %s + %s ) - %s ) )' % (SL1, TF, R, TPL, TAF, AL, TF, R, TAF)),
                w.s([D(w, A0, 'addsubd', [tfF0['ptc'], rc, tafc], '( ( %s + %s ) - %s ) = ( %s + %s )' % (TF, R, TAF, BF, R))], 'oveq2d',
                    '( %s -> ( %s + ( ( %s + %s ) - %s ) ) = ( %s + ( %s + %s ) ) )' % (A0, AL, TF, R, TAF, AL, BF, R))])
    # AL as a sum
    TA = lambda n: '( %s x. %s )' % (TPI, AN(n))
    AK = lambda n: '( %s x. ( %s - %s ) )' % (AN(n), KC(n), TPI)
    tfL_tpc = lift(w, CL_, t0L, tpc, '%s e. CC' % TPI)
    mc = w.s([finL, tpc, tfL['anc']], 'fsummulc2', '( %s -> %s = sum_ n e. %s %s )' % (A0, TPL, IL1, TA('n')))
    fsub = w.s([finL, tfL['ptc'], D(w, CL_, 'mulcld', [tfL_tpc, tfL['anc']], '%s e. CC' % TA('n'))], 'fsumsub', '( %s -> sum_ n e. %s ( %s - %s ) = ( %s - sum_ n e. %s %s ) )' % (A0, IL1, PTn, TA('n'), SL1, IL1, TA('n')))

    def akeq(C, t, n, tpcC):
        sd = D(w, C, 'subdid', [t['anc'], t['kcc'], tpcC], '%s = ( %s - ( %s x. %s ) )' % (AK(n), PTERM(n, C0), AN(n), TPI))
        mcm = D(w, C, 'mulcomd', [t['anc'], tpcC], '( %s x. %s ) = %s' % (AN(n), TPI, TA(n)))
        return w.s([w.s([sd, w.s([mcm], 'oveq2d', '( %s -> ( %s - ( %s x. %s ) ) = ( %s - %s ) )' % (C, PTERM(n, C0), AN(n), TPI, PTERM(n, C0), TA(n)))], 'eqtrd',
                        '( %s -> %s = ( %s - %s ) )' % (C, AK(n), PTERM(n, C0), TA(n)))], 'eqcomd', '( %s -> ( %s - %s ) = %s )' % (C, PTERM(n, C0), TA(n), AK(n)))

    ake = akeq(CL_, tfL, 'n', tfL_tpc)
    se = w.s([ake], 'sumeq2dv', '( %s -> sum_ n e. %s ( %s - %s ) = sum_ n e. %s %s )' % (A0, IL1, PTn, TA('n'), IL1, AK('n')))
    ALS = 'sum_ n e. %s %s' % (IL1, AK('n'))
    ale = chain(w, A0, [AL, '( %s - sum_ n e. %s %s )' % (SL1, IL1, TA('n')), 'sum_ n e. %s ( %s - %s )' % (IL1, PTn, TA('n')), ALS],
                [w.s([mc], 'oveq2d', '( %s -> %s = ( %s - sum_ n e. %s %s ) )' % (A0, AL, SL1, IL1, TA('n'))), ('r', fsub), se])
    bfe = w.s([akeq(A0, tfF0, F, tpc)], 'idi', '( %s -> %s = %s )' % (A0, BF, AK(F)))
    akcL = D(w, CL_, 'mulcld', [tfL['anc'], tfL['kmt']], '%s e. CC' % AK('n'))
    fa1 = w.s([finL, akcL], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ n e. %s ( abs ` %s ) )' % (A0, ALS, IL1, AK('n')))
    lamL = w.s([knL, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % CL_)
    elL = D(w, CL_, 'remulcld', [lamL, D(w, CL_, 'abscld', [tfL['kmt']], '( abs ` ( %s - %s ) ) e. RR' % (KC('n'), TPI))], '%s e. RR' % EL('n'))
    fl1 = w.s([finL, D(w, CL_, 'abscld', [akcL], '( abs ` %s ) e. RR' % AK('n')), elL, tfL['bL']], 'fsumle', '( %s -> sum_ n e. %s ( abs ` %s ) <_ sum_ n e. %s %s )' % (A0, IL1, AK('n'), IL1, EL('n')))
    lft = w.s([yt, w.inst('ef1lft')], 'syl', '( %s -> sum_ n e. %s %s <_ ( ; 4 6 x. %s ) )' % (A0, IL1, EL('n'), YL))
    def fsumbnd(C, t, kn, fin_, X, sumlab, cst):
        fa = w.s([fin_, t['ptc']], 'fsumabs', '( %s -> ( abs ` sum_ n e. %s %s ) <_ sum_ n e. %s ( abs ` %s ) )' % (A0, X, PTn, X, PTn))
        lam = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % C)
        er = D(w, C, 'remulcld', [lam, D(w, C, 'abscld', [t['kcc']], '( abs ` %s ) e. RR' % KC('n'))], '%s e. RR' % ER('n'))
        fl = w.s([fin_, D(w, C, 'abscld', [t['ptc']], '( abs ` %s ) e. RR' % PTn), er, t['bR']], 'fsumle', '( %s -> sum_ n e. %s ( abs ` %s ) <_ sum_ n e. %s %s )' % (A0, X, PTn, X, ER('n')))
        return fa, fl, er
    fam, flm, erM = fsumbnd(CM_, tfM, knM, finM, IMD, 'ef1mr', 45)
    fat, flt_, erT = fsumbnd(CT_, tfT, knT, finT, ITL, 'ef1tl', 216)
    mr = w.s([yt, w.inst('ef1mr')], 'syl', '( %s -> sum_ n e. %s %s <_ ( ; 4 5 x. %s ) )' % (A0, IMD, ER('n'), YL))
    tl = w.s([D(w, A0, 'jca', [yt, mz], '( %s /\\ M e. ( ZZ>= ` %s ) )' % (YT, F2)), w.inst('ef1tl')], 'syl', '( %s -> sum_ n e. %s %s <_ ( ; ; 2 1 6 x. %s ) )' % (A0, ITL, ER('n'), YL))
    nr = w.s([yt, w.inst('ef1nr')], 'syl', '( %s -> ( %s + %s ) <_ ( ; 1 6 x. %s ) )' % (A0, EL(F), ER(F1), L2))
    # triangle inequalities
    alc = w.s([finL, akcL], 'fsumcl', '( %s -> %s e. CC )' % (A0, ALS))
    akF = D(w, A0, 'mulcld', [tfF0['anc'], tfF0['kmt']], '%s e. CC' % AK(F))
    alcc = D(w, A0, 'subcld', [slc, tplc], '%s e. CC' % AL); bfc = D(w, A0, 'subcld', [tfF0['ptc'], tafc], '%s e. CC' % BF)
    smst = D(w, A0, 'addcld', [smc, stc], '( %s + %s ) e. CC' % (SMID, STL))
    tr1 = D(w, A0, 'abstrid', [alcc, D(w, A0, 'addcld', [bfc, rc], '( %s + %s ) e. CC' % (BF, R))], '( abs ` ( %s + ( %s + %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( %s + %s ) ) )' % (AL, BF, R, AL, BF, R))
    tr2 = D(w, A0, 'abstrid', [bfc, rc], '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (BF, R, BF, R))
    tr3 = D(w, A0, 'abstrid', [tfG0['ptc'], smst], '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s + %s ) ) )' % (R, TG, SMID, STL))
    tr4 = D(w, A0, 'abstrid', [smc, stc], '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SMID, STL, SMID, STL))
    ax = w.s([xe], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( %s + ( %s + %s ) ) ) )' % (A0, X, AL, BF, R))
    aal = w.s([ale], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, AL, ALS))
    abf = w.s([bfe], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, BF, AK(F)))
    rr = lambda e, st: cl.leaf(e, 'RR', st)
    for e, cst in [('( abs ` %s )' % X, D(w, A0, 'subcld', [w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, IM)), tf1['ptc']], 'fsumcl', '( %s -> %s e. CC )' % (A0, S)),
                                                               D(w, A0, 'mulcld', [tpc, w.s([w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (A0, F)), tfP['anc']], 'fsumcl', '( %s -> %s e. CC )' % (A0, PSI))], '( %s x. %s ) e. CC' % (TPI, PSI))],
                                                    '%s e. CC' % X)),
                   ('( abs ` ( %s + ( %s + %s ) ) )' % (AL, BF, R), D(w, A0, 'addcld', [alcc, D(w, A0, 'addcld', [bfc, rc], '( %s + %s ) e. CC' % (BF, R))], '( %s + ( %s + %s ) ) e. CC' % (AL, BF, R))),
                   ('( abs ` %s )' % AL, alcc), ('( abs ` %s )' % ALS, alc), ('( abs ` ( %s + %s ) )' % (BF, R), D(w, A0, 'addcld', [bfc, rc], '( %s + %s ) e. CC' % (BF, R))),
                   ('( abs ` %s )' % BF, bfc), ('( abs ` %s )' % AK(F), akF), ('( abs ` %s )' % R, rc), ('( abs ` %s )' % TG, tfG0['ptc']), ('( abs ` ( %s + %s ) )' % (SMID, STL), smst),
                   ('( abs ` %s )' % SMID, smc), ('( abs ` %s )' % STL, stc)]:
        rr(e, D(w, A0, 'abscld', [cst], '%s e. RR' % e))
    rr('sum_ n e. %s ( abs ` %s )' % (IL1, AK('n')), w.s([finL, D(w, CL_, 'abscld', [akcL], '( abs ` %s ) e. RR' % AK('n'))], 'fsumrecl', '( %s -> sum_ n e. %s ( abs ` %s ) e. RR )' % (A0, IL1, AK('n'))))
    rr('sum_ n e. %s %s' % (IL1, EL('n')), w.s([finL, elL], 'fsumrecl', '( %s -> sum_ n e. %s %s e. RR )' % (A0, IL1, EL('n'))))
    for X_, C_, t_, er_, fin_ in [(IMD, CM_, tfM, erM, finM), (ITL, CT_, tfT, erT, finT)]:
        rr('sum_ n e. %s ( abs ` %s )' % (X_, PTn), w.s([fin_, D(w, C_, 'abscld', [t_['ptc']], '( abs ` %s ) e. RR' % PTn)], 'fsumrecl', '( %s -> sum_ n e. %s ( abs ` %s ) e. RR )' % (A0, X_, PTn)))
        rr('sum_ n e. %s %s' % (X_, ER('n')), w.s([fin_, er_], 'fsumrecl', '( %s -> sum_ n e. %s %s e. RR )' % (A0, X_, ER('n'))))
    rr(EL(F), D(w, A0, 'remulcld', [w.s([d['fnn'], w.inst('vmacl')], 'syl', '( %s -> ( Lam ` %s ) e. RR )' % (A0, F)), D(w, A0, 'abscld', [tfF0['kmt']], '( abs ` ( %s - %s ) ) e. RR' % (KC(F), TPI))], '%s e. RR' % EL(F)))
    rr(ER(F1), D(w, A0, 'remulcld', [w.s([f1nn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` %s ) e. RR )' % (A0, F1)), D(w, A0, 'abscld', [tfG0['kcc']], '( abs ` %s ) e. RR' % KC(F1))], '%s e. RR' % ER(F1)))
    l2r = D(w, A0, 'resqcld', [d['L']], '%s e. RR' % L2)
    rr(L2, l2r)
    y2 = D(w, A0, 'remulcld', [d['yr'], l2r], '( Y x. %s ) e. RR' % L2)
    ylr = D(w, A0, 'rerpdivcld', [y2, d['trp']], '%s e. RR' % YL)
    rr(YL, ylr)
    yl0 = D(w, A0, 'divge0d', [y2, d['trp'], D(w, A0, 'mulge0d', [d['yr'], l2r, D(w, A0, 'rpge0d', [d['yrp']], '0 <_ Y'), D(w, A0, 'sqge0d', [d['L']], '0 <_ %s' % L2)], '0 <_ ( Y x. %s )' % L2)], '0 <_ %s' % YL)
    fin_ = linarith(w, A0, [ax, tr1, aal, fa1, fl1, lft, tr2, abf, tfF0['bL'], tr3, tfG0['bR'], tr4, fam, flm, mr, fat, flt_, tl, nr, yl0],
                    '( abs ` %s ) <_ ( ( ; ; 3 1 0 x. %s ) + ( ; 1 6 x. %s ) )' % (X, YL, L2), closure=cl, atoms=[YL, L2])
    w.qed([fin_], 'idi', STATEMENTS['ef1pt'])
    go(w, only)

# ---------------------------------------------------------------- ef1psb: perronSum_sub_psiChi_le
if __name__ == '__main__' and (not only or 'ef1psb' in only):
    sys.argv = sys.argv[:1]
    from ef1_f import yctx, lift, tpiabs
    w = W('ef1psb', 'The series side of the explicit formula: at ` c = 1 + 1 / log y ` the Perron-weighted sum ` sum_ n chi ( n ) Lam ( n ) K ( y / n ) ` '
          'is ` 2 pi i psi ( y , chi ) ` up to ` 2 pi ( 200 y L ^ 2 / T + 30 L ^ 2 ) ` , ` L = log ( T y ) ` (Lean ` perronSum_sub_psiChi_le ` with the '
          'kernel ` 2 pi i ` times Lean\'s).  The limit of ~ ef1pt ; the series converges by ~ ef1redge .')
    A0 = '( %s /\\ %s )' % (NX, YT)
    nx = D(w, A0, 'simpl', [], NX); yt = D(w, A0, 'simpr', [], YT)
    d = yctx(w, A0, yt); cl = d['cl']
    tpc, tpa = tpiabs(w, A0)
    PM = '( n e. NN |-> %s )' % PTERM('n', C0)
    GS = 'seq 1 ( + , %s )' % PM
    RL = '( %s lint <. %s , %s >. )' % (RHF, LO(C0), HI(C0))
    red = w.s([D(w, A0, 'jca', [nx, D(w, A0, 'jca', [D(w, A0, '3jca', [d['yrp'], d['c0r'], d['c0gt']], '( Y e. RR+ /\\ %s e. RR /\\ 1 < %s )' % (C0, C0)), d['tr']],
                                                  '( ( Y e. RR+ /\\ %s e. RR /\\ 1 < %s ) /\\ T e. RR )' % (C0, C0))], '( %s /\\ ( ( Y e. RR+ /\\ %s e. RR /\\ 1 < %s ) /\\ T e. RR ) )' % (NX, C0, C0)),
               w.inst('ef1redge')], 'syl', '( %s -> ( %s ~~> %s /\\ %s = %s ) )' % (A0, GS, RL, PS(C0), RL))
    conv = w.s([D(w, A0, 'simpld', [red], '%s ~~> %s' % (GS, RL)), D(w, A0, 'simprd', [red], '%s = %s' % (PS(C0), RL))], 'breqtrrd', '( %s -> %s ~~> %s )' % (A0, GS, PS(C0)))
    TPSI = '( %s x. %s )' % (TPI, PSI)
    AK = '( %s /\\ k e. NN )' % A0
    to0 = w.s([], 'simpl', '( %s -> %s )' % (AK, A0)); kn = w.s([], 'simpr', '( %s -> k e. NN )' % AK)
    # the partial sums are the finite sums
    AKN = '( %s /\\ n e. ( 1 ... k ) )' % AK
    nn_ = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... k ) )' % AKN), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AKN)
    t0n = w.s([], 'simpll', '( %s -> %s )' % (AKN, A0))
    qv = w.s([nn_, w.inst('lchvmval')], 'syl', '( %s -> ( ( q e. NN |-> %s ) ` n ) = %s )' % (AKN, AN('q'), AN('n')))
    qf = w.s([w.s([t0n, nx], 'syl', '( %s -> %s )' % (AKN, NX)), w.inst('lchvmf')], 'syl', '( %s -> ( q e. NN |-> %s ) : NN --> CC )' % (AKN, AN('q')))
    anc = w.s([qv, w.s([qf, nn_], 'ffvelcdmd', '( %s -> ( ( q e. NN |-> %s ) ` n ) e. CC )' % (AKN, AN('q')))], 'eqeltrrd', '( %s -> %s e. CC )' % (AKN, AN('n')))
    kcc = w.s([D(w, AKN, 'rpdivcld', [lift(w, AKN, t0n, d['yrp'], 'Y e. RR+'), D(w, AKN, 'nnrpd', [nn_], 'n e. RR+')], '( Y / n ) e. RR+'), lift(w, AKN, t0n, d['c0rp'], '%s e. RR+' % C0),
               lift(w, AKN, t0n, d['trp'], 'T e. RR+'), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (AKN, KC('n')))
    ptc = D(w, AKN, 'mulcld', [anc, kcc], '%s e. CC' % PTERM('n', C0))
    PTj = PTERM('j', C0)
    ANJ = '( %s /\\ j e. NN )' % A0
    # ( PM ` j ) = PTERM ( j ): fvmptd with n = j
    def subk(a, b):
        return w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) = ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % (a, b, a, b))], 'fveq2d', '( %s = %s -> %s = %s )' % (a, b, XC(a), XC(b))),
                    w.s([], 'fveq2', '( %s = %s -> ( Lam ` %s ) = ( Lam ` %s ) )' % (a, b, a, b))], 'oveq12d', '( %s = %s -> %s = %s )' % (a, b, AN(a), AN(b)))

    def pts(a, b):
        yx = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( Y / %s ) = ( Y / %s ) )' % (a, b, a, b))], 'oveq1d', '( %s = %s -> ( ( Y / %s ) ^c z ) = ( ( Y / %s ) ^c z ) )' % (a, b, a, b))], 'oveq1d',
                      '( %s = %s -> ( ( ( Y / %s ) ^c z ) / z ) = ( ( ( Y / %s ) ^c z ) / z ) )' % (a, b, a, b))], 'mpteq2dv', '( %s = %s -> %s = %s )' % (a, b, PKF('( Y / %s )' % a), PKF('( Y / %s )' % b)))
        pl = w.s([yx], 'oveq1d', '( %s = %s -> %s = %s )' % (a, b, KC(a), KC(b)))
        return w.s([subk(a, b), pl], 'oveq12d', '( %s = %s -> %s = %s )' % (a, b, PTERM(a, C0), PTERM(b, C0)))

    AKJ = '( %s /\\ j e. ( 1 ... k ) )' % AK
    jn = w.s([w.s([], 'simpr', '( %s -> j e. ( 1 ... k ) )' % AKJ), w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % AKJ)
    t0j = w.s([], 'simpll', '( %s -> %s )' % (AKJ, A0))
    qvj = w.s([jn, w.inst('lchvmval')], 'syl', '( %s -> ( ( q e. NN |-> %s ) ` j ) = %s )' % (AKJ, AN('q'), AN('j')))
    qfj = w.s([w.s([t0j, nx], 'syl', '( %s -> %s )' % (AKJ, NX)), w.inst('lchvmf')], 'syl', '( %s -> ( q e. NN |-> %s ) : NN --> CC )' % (AKJ, AN('q')))
    ancj = w.s([qvj, w.s([qfj, jn], 'ffvelcdmd', '( %s -> ( ( q e. NN |-> %s ) ` j ) e. CC )' % (AKJ, AN('q')))], 'eqeltrrd', '( %s -> %s e. CC )' % (AKJ, AN('j')))
    kccj = w.s([D(w, AKJ, 'rpdivcld', [lift(w, AKJ, t0j, d['yrp'], 'Y e. RR+'), D(w, AKJ, 'nnrpd', [jn], 'j e. RR+')], '( Y / j ) e. RR+'), lift(w, AKJ, t0j, d['c0rp'], '%s e. RR+' % C0),
                lift(w, AKJ, t0j, d['trp'], 'T e. RR+'), w.inst('pkcl')], 'syl3anc', '( %s -> %s e. CC )' % (AKJ, KC('j')))
    ptcj = D(w, AKJ, 'mulcld', [ancj, kccj], '%s e. CC' % PTj)
    pmj = w.s([w.s([w.s([], 'eqid', '%s = %s' % (PM, PM))], 'a1i', '( %s -> %s = %s )' % (AKJ, PM, PM)), w.s([pts('n', 'j')], 'adantl', '( ( %s /\\ n = j ) -> %s = %s )' % (AKJ, PTERM('n', C0), PTj)),
               jn, ptcj], 'fvmptd', '( %s -> ( %s ` j ) = %s )' % (AKJ, PM, PTj))
    kuz = w.s([kn, w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylib', '( %s -> k e. ( ZZ>= ` 1 ) )' % AK)
    fss = w.s([pmj, kuz, ptcj], 'fsumser', '( %s -> sum_ j e. ( 1 ... k ) %s = ( %s ` k ) )' % (AK, PTj, GS))
    SJ = 'sum_ j e. ( 1 ... k ) %s' % PTj
    SN = 'sum_ n e. ( 1 ... k ) %s' % PTERM('n', C0)
    cbj = w.s([w.s([pts('j', 'n')], 'cbvsumv', '%s = %s' % (SJ, SN))], 'a1i', '( %s -> %s = %s )' % (AK, SJ, SN))
    gsk = w.s([w.s([fss], 'eqcomd', '( %s -> ( %s ` k ) = %s )' % (AK, GS, SJ)), cbj], 'eqtrd', '( %s -> ( %s ` k ) = %s )' % (AK, GS, SN))

    snc = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... k ) e. Fin )' % AK), ptc], 'fsumcl', '( %s -> %s e. CC )' % (AK, SN))
    gskc = w.s([gsk, snc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (AK, GS))
    psic = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (A0, FL)),
                D(w, '( %s /\\ n e. ( 1 ... %s ) )' % (A0, FL), 'eqeltrrd', [w.s([w.s([w.s([], 'simpr', '( ( %s /\\ n e. ( 1 ... %s ) ) -> n e. ( 1 ... %s ) )' % (A0, FL, FL)), w.inst('elfznn')], 'syl',
                                                                                  '( ( %s /\\ n e. ( 1 ... %s ) ) -> n e. NN )' % (A0, FL)), w.inst('lchvmval')], 'syl',
                                                                           '( ( %s /\\ n e. ( 1 ... %s ) ) -> ( ( q e. NN |-> %s ) ` n ) = %s )' % (A0, FL, AN('q'), AN('n'))),
                                                                     w.s([w.s([w.s([w.s([], 'simpl', '( ( %s /\\ n e. ( 1 ... %s ) ) -> %s )' % (A0, FL, A0)), nx], 'syl', '( ( %s /\\ n e. ( 1 ... %s ) ) -> %s )' % (A0, FL, NX)), w.inst('lchvmf')],
                                                                              'syl', '( ( %s /\\ n e. ( 1 ... %s ) ) -> ( q e. NN |-> %s ) : NN --> CC )' % (A0, FL, AN('q'))),
                                                                          w.s([w.s([], 'simpr', '( ( %s /\\ n e. ( 1 ... %s ) ) -> n e. ( 1 ... %s ) )' % (A0, FL, FL)), w.inst('elfznn')], 'syl', '( ( %s /\\ n e. ( 1 ... %s ) ) -> n e. NN )' % (A0, FL))],
                                                                         'ffvelcdmd', '( ( %s /\\ n e. ( 1 ... %s ) ) -> ( ( q e. NN |-> %s ) ` n ) e. CC )' % (A0, FL, AN('q')))], '%s e. CC' % AN('n'))],
               'fsumcl', '( %s -> %s e. CC )' % (A0, PSI))
    tpsic = D(w, A0, 'mulcld', [tpc, psic], '%s e. CC' % TPSI)
    GP = '( m e. NN |-> ( ( %s ` m ) - %s ) )' % (GS, TPSI)
    gpk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (GP, GP))], 'a1i', '( %s -> %s = %s )' % (AK, GP, GP)),
               w.s([w.s([w.s([], 'fveq2', '( m = k -> ( %s ` m ) = ( %s ` k ) )' % (GS, GS))], 'oveq1d', '( m = k -> ( ( %s ` m ) - %s ) = ( ( %s ` k ) - %s ) )' % (GS, TPSI, GS, TPSI))], 'adantl',
                   '( ( %s /\\ m = k ) -> ( ( %s ` m ) - %s ) = ( ( %s ` k ) - %s ) )' % (AK, GS, TPSI, GS, TPSI)), kn,
               w.s([w.s([], 'ovex', '( ( %s ` k ) - %s ) e. _V' % (GS, TPSI))], 'a1i', '( %s -> ( ( %s ` k ) - %s ) e. _V )' % (AK, GS, TPSI))], 'fvmptd', '( %s -> ( %s ` k ) = ( ( %s ` k ) - %s ) )' % (AK, GP, GS, TPSI))
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = a1(w, A0, '1z', '1 e. ZZ')
    gpe = w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % GP)], 'a1i', '( %s -> %s e. _V )' % (A0, GP))
    cs1 = w.s([nnz, one, conv, tpsic, gpe, gskc, gpk], 'climsubc1', '( %s -> %s ~~> ( %s - %s ) )' % (A0, GP, PS(C0), TPSI))
    H = '( i e. NN |-> ( abs ` ( %s ` i ) ) )' % GP
    gpkc = w.s([gpk, D(w, AK, 'subcld', [gskc, lift(w, AK, to0, tpsic, '%s e. CC' % TPSI)], '( ( %s ` k ) - %s ) e. CC' % (GS, TPSI))], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (AK, GP))
    hk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (H, H))], 'a1i', '( %s -> %s = %s )' % (AK, H, H)),
              w.s([w.s([w.s([], 'fveq2', '( i = k -> ( %s ` i ) = ( %s ` k ) )' % (GP, GP))], 'fveq2d', '( i = k -> ( abs ` ( %s ` i ) ) = ( abs ` ( %s ` k ) ) )' % (GP, GP))], 'adantl',
                  '( ( %s /\\ i = k ) -> ( abs ` ( %s ` i ) ) = ( abs ` ( %s ` k ) ) )' % (AK, GP, GP)), kn,
              w.s([w.s([], 'fvex', '( abs ` ( %s ` k ) ) e. _V' % GP)], 'a1i', '( %s -> ( abs ` ( %s ` k ) ) e. _V )' % (AK, GP))], 'fvmptd', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (AK, H, GP))
    he = w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % H)], 'a1i', '( %s -> %s e. _V )' % (A0, H))
    DIF = '( %s - %s )' % (PS(C0), TPSI)
    ca = w.s([nnz, cs1, he, one, gpkc, hk], 'climabs', '( %s -> %s ~~> ( abs ` %s ) )' % (A0, H, DIF))
    ZF = '( ZZ>= ` %s )' % F2
    f2nn = D(w, A0, 'nnaddcld', [D(w, A0, 'nnmulcld', [a1(w, A0, '2nn', '2 e. NN'), d['fnn']], '( 2 x. %s ) e. NN' % FL), a1(w, A0, '2nn', '2 e. NN')], '%s e. NN' % F2)
    f2z = D(w, A0, 'nnzd', [f2nn], '%s e. ZZ' % F2)
    l2r = D(w, A0, 'resqcld', [d['L']], '%s e. RR' % L2)
    y2 = D(w, A0, 'remulcld', [d['yr'], l2r], '( Y x. %s ) e. RR' % L2)
    ylr = D(w, A0, 'rerpdivcld', [y2, d['trp']], '%s e. RR' % YL)
    cl.leaf(YL, 'RR', ylr); cl.leaf(L2, 'RR', l2r)
    BP = '( ( ; ; 3 1 0 x. %s ) + ( ; 1 6 x. %s ) )' % (YL, L2)
    bpr = cl.mem(BP, 'RR')
    CS = '( %s X. { %s } )' % (ZF, BP)
    ccv = w.s([D(w, A0, 'recnd', [bpr], '%s e. CC' % BP), f2z, w.s([w.s([], 'ssid', '%s C_ %s' % (ZF, ZF)), w.s([], 'fvex', '%s e. _V' % ZF)], 'climconst2', '( ( %s e. CC /\\ %s e. ZZ ) -> %s ~~> %s )' % (BP, F2, CS, BP))],
              'syl2anc', '( %s -> %s ~~> %s )' % (A0, CS, BP))
    AZ = '( %s /\\ k e. %s )' % (A0, ZF)
    az0 = w.s([], 'simpl', '( %s -> %s )' % (AZ, A0)); azk = w.s([], 'simpr', '( %s -> k e. %s )' % (AZ, ZF))
    knz = w.s([lift(w, AZ, az0, f2nn, '%s e. NN' % F2), azk, w.inst('eluznn')], 'syl2anc', '( %s -> k e. NN )' % AZ)
    toAK = D(w, AZ, 'jca', [az0, knz], AK)
    L_ = lambda st: w.s([toAK, st], 'syl', '( %s -> %s )' % (AZ, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    hkz = w.s([L_(hk), w.s([L_(gpk)], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` ( ( %s ` k ) - %s ) ) )' % (AZ, GP, GS, TPSI))], 'eqtrd', '( %s -> ( %s ` k ) = ( abs ` ( ( %s ` k ) - %s ) ) )' % (AZ, H, GS, TPSI))
    hkz2 = w.s([hkz, w.s([w.s([L_(gsk)], 'oveq1d', '( %s -> ( ( %s ` k ) - %s ) = ( %s - %s ) )' % (AZ, GS, TPSI, SN, TPSI))], 'fveq2d',
                         '( %s -> ( abs ` ( ( %s ` k ) - %s ) ) = ( abs ` ( %s - %s ) ) )' % (AZ, GS, TPSI, SN, TPSI))], 'eqtrd', '( %s -> ( %s ` k ) = ( abs ` ( %s - %s ) ) )' % (AZ, H, SN, TPSI))
    pt = w.s([], 'ef1pt', '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (AZ, SN, TPSI, BP))
    csk = w.s([lift(w, AZ, az0, bpr, '%s e. RR' % BP), azk, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` k ) = %s )' % (AZ, CS, BP))
    hkr = w.s([hkz2, D(w, AZ, 'abscld', [D(w, AZ, 'subcld', [L_(snc), lift(w, AZ, az0, tpsic, '%s e. CC' % TPSI)], '( %s - %s ) e. CC' % (SN, TPSI))], '( abs ` ( %s - %s ) ) e. RR' % (SN, TPSI))], 'eqeltrd',
              '( %s -> ( %s ` k ) e. RR )' % (AZ, H))
    csr = w.s([csk, lift(w, AZ, az0, bpr, '%s e. RR' % BP)], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (AZ, CS))
    hle = w.s([w.s([hkz2, pt], 'eqbrtrd', '( %s -> ( %s ` k ) <_ %s )' % (AZ, H, BP)), w.s([csk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (AZ, BP, CS))], 'breqtrd', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (AZ, H, CS))
    cle = w.s([w.s([], 'eqid', '%s = %s' % (ZF, ZF)), f2z, ca, ccv, hkr, csr, hle], 'climle', '( %s -> ( abs ` %s ) <_ %s )' % (A0, DIF, BP))
    # 310 X + 16 L2 <_ 2 pi ( 200 X + 30 L2 )
    yl0 = D(w, A0, 'divge0d', [y2, d['trp'], D(w, A0, 'mulge0d', [d['yr'], l2r, D(w, A0, 'rpge0d', [d['yrp']], '0 <_ Y'), D(w, A0, 'sqge0d', [d['L']], '0 <_ %s' % L2)], '0 <_ ( Y x. %s )' % L2)], '0 <_ %s' % YL)
    l20 = D(w, A0, 'sqge0d', [d['L']], '0 <_ %s' % L2)
    pr = a1(w, A0, 'pire', '_pi e. RR')
    p2 = w.s([w.s([w.s([], 'pigt2lt4', '( 2 < _pi /\\ _pi < 4 )')], 'simpli', '2 < _pi')], 'a1i', '( %s -> 2 < _pi )' % A0)
    p2l = D(w, A0, 'ltled', [a1(w, A0, '2re', '2 e. RR'), pr, p2], '2 <_ _pi')
    m1 = D(w, A0, 'lemul1ad', [a1(w, A0, '2re', '2 e. RR'), pr, ylr, yl0, p2l], '( 2 x. %s ) <_ ( _pi x. %s )' % (YL, YL))
    m2 = D(w, A0, 'lemul1ad', [a1(w, A0, '2re', '2 e. RR'), pr, l2r, l20, p2l], '( 2 x. %s ) <_ ( _pi x. %s )' % (L2, L2))
    cl.leaf('_pi', 'RR', pr)
    fin_ = linarith(w, A0, [m1, m2, yl0, l20], '%s <_ %s' % (BP, BND), closure=cl, products=True, atoms=[YL, L2])
    psc = w.s([conv, w.inst('climcl')], 'syl', '( %s -> %s e. CC )' % (A0, PS(C0)))
    adr = D(w, A0, 'abscld', [D(w, A0, 'subcld', [psc, tpsic], '%s e. CC' % DIF)], '( abs ` %s ) e. RR' % DIF)
    w.qed([adr, bpr, cl.mem(BND, 'RR'), cle, fin_], 'letrd', STATEMENTS['ef1psb'])
    go(w, only)
