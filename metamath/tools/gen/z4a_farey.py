"""Sortie Z4a, batch 6: Farey spacing on the line (LargeSieve farey_sep_abs)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from z4alib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

FA = '( ( ( Q e. NN /\\ R e. NN ) /\\ ( A e. NN0 /\\ B e. NN0 ) ) /\\ ( ( A gcd Q ) = 1 /\\ ( B gcd R ) = 1 ) /\\ -. ( Q = R /\\ A = B ) )'
D = '( ( A x. R ) - ( B x. Q ) )'
S_fareysep = '( %s -> ( 1 / ( Q x. R ) ) <_ ( abs ` ( ( A / Q ) - ( B / R ) ) ) )' % FA


def parts(w, ante, fst):
    """q r a b ga gb ne under ante from fst: ( ante -> FA )"""
    p1 = w.s([fst], 'simp1d', '( %s -> ( ( Q e. NN /\\ R e. NN ) /\\ ( A e. NN0 /\\ B e. NN0 ) ) )' % ante)
    qr = w.s([p1], 'simpld', '( %s -> ( Q e. NN /\\ R e. NN ) )' % ante); ab = w.s([p1], 'simprd', '( %s -> ( A e. NN0 /\\ B e. NN0 ) )' % ante)
    g = w.s([fst], 'simp2d', '( %s -> ( ( A gcd Q ) = 1 /\\ ( B gcd R ) = 1 ) )' % ante)
    return (w.s([qr], 'simpld', '( %s -> Q e. NN )' % ante), w.s([qr], 'simprd', '( %s -> R e. NN )' % ante),
            w.s([ab], 'simpld', '( %s -> A e. NN0 )' % ante), w.s([ab], 'simprd', '( %s -> B e. NN0 )' % ante),
            w.s([g], 'simpld', '( %s -> ( A gcd Q ) = 1 )' % ante), w.s([g], 'simprd', '( %s -> ( B gcd R ) = 1 )' % ante),
            w.s([fst], 'simp3d', '( %s -> -. ( Q = R /\\ A = B ) )' % ante))


if __name__ == '__main__':
    # ---- fareyseplem: the cross numerator is nonzero (Lean hnum)
    B0 = '( %s /\\ %s = 0 )' % (FA, D)
    w = W('fareyseplem', 'Lemma for fareysep: distinct reduced fractions A / Q and B / R have a nonzero cross numerator A R - B Q (Lean hnum).')
    q, r, a, b, ga, gb, ne = parts(w, B0, w.s([], 'simpl', '( %s -> %s )' % (B0, FA)))
    qz = w.s([q], 'nnzd', '( %s -> Q e. ZZ )' % B0); rz = w.s([r], 'nnzd', '( %s -> R e. ZZ )' % B0)
    az = w.s([a], 'nn0zd', '( %s -> A e. ZZ )' % B0); bz = w.s([b], 'nn0zd', '( %s -> B e. ZZ )' % B0)
    ar = w.s([az, rz], 'zmulcld', '( %s -> ( A x. R ) e. ZZ )' % B0); bq = w.s([bz, qz], 'zmulcld', '( %s -> ( B x. Q ) e. ZZ )' % B0)
    eq = w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (B0, D)), w.s([w.s([ar], 'zcnd', '( %s -> ( A x. R ) e. CC )' % B0), w.s([bq], 'zcnd', '( %s -> ( B x. Q ) e. CC )' % B0)], 'subeq0ad', '( %s -> ( %s = 0 <-> ( A x. R ) = ( B x. Q ) ) )' % (B0, D))], 'mpbid', '( %s -> ( A x. R ) = ( B x. Q ) )' % B0)
    q1 = w.s([w.s([bz, qz, w.inst('dvdsmul2')], 'syl2anc', '( %s -> Q || ( B x. Q ) )' % B0), eq], 'breqtrrd', '( %s -> Q || ( A x. R ) )' % B0)
    qa = w.s([w.s([qz, az], 'gcdcomd', '( %s -> ( Q gcd A ) = ( A gcd Q ) )' % B0), ga], 'eqtrd', '( %s -> ( Q gcd A ) = 1 )' % B0)
    qdr = w.s([w.s([q1, qa], 'jca', '( %s -> ( Q || ( A x. R ) /\\ ( Q gcd A ) = 1 ) )' % B0), w.s([qz, az, rz, w.inst('coprmdvds')], 'syl3anc', '( %s -> ( ( Q || ( A x. R ) /\\ ( Q gcd A ) = 1 ) -> Q || R ) )' % B0)], 'mpd', '( %s -> Q || R )' % B0)
    r1 = w.s([w.s([az, rz, w.inst('dvdsmul2')], 'syl2anc', '( %s -> R || ( A x. R ) )' % B0), eq], 'breqtrd', '( %s -> R || ( B x. Q ) )' % B0)
    rb = w.s([w.s([rz, bz], 'gcdcomd', '( %s -> ( R gcd B ) = ( B gcd R ) )' % B0), gb], 'eqtrd', '( %s -> ( R gcd B ) = 1 )' % B0)
    rdq = w.s([w.s([r1, rb], 'jca', '( %s -> ( R || ( B x. Q ) /\\ ( R gcd B ) = 1 ) )' % B0), w.s([rz, bz, qz, w.inst('coprmdvds')], 'syl3anc', '( %s -> ( ( R || ( B x. Q ) /\\ ( R gcd B ) = 1 ) -> R || Q ) )' % B0)], 'mpd', '( %s -> R || Q )' % B0)
    qer = w.s([w.s([w.s([q], 'nnnn0d', '( %s -> Q e. NN0 )' % B0), w.s([r], 'nnnn0d', '( %s -> R e. NN0 )' % B0)], 'jca', '( %s -> ( Q e. NN0 /\\ R e. NN0 ) )' % B0), w.s([qdr, rdq], 'jca', '( %s -> ( Q || R /\\ R || Q ) )' % B0), w.inst('dvdseq')], 'syl2anc', '( %s -> Q = R )' % B0)
    eq2 = w.s([eq, w.s([qer], 'oveq2d', '( %s -> ( B x. Q ) = ( B x. R ) )' % B0)], 'eqtrd', '( %s -> ( A x. R ) = ( B x. R ) )' % B0)
    aeb = w.s([eq2, w.s([w.s([az], 'zcnd', '( %s -> A e. CC )' % B0), w.s([bz], 'zcnd', '( %s -> B e. CC )' % B0), w.s([r], 'nncnd', '( %s -> R e. CC )' % B0), w.s([r], 'nnne0d', '( %s -> R =/= 0 )' % B0)], 'mulcan2d', '( %s -> ( ( A x. R ) = ( B x. R ) <-> A = B ) )' % B0)], 'mpbid', '( %s -> A = B )' % B0)
    both = w.s([qer, aeb], 'jca', '( %s -> ( Q = R /\\ A = B ) )' % B0)
    imp = w.s([both], 'ex', '( %s -> ( %s = 0 -> ( Q = R /\\ A = B ) ) )' % (FA, D))
    ne0 = w.s([w.s([], 'simp3', '( %s -> -. ( Q = R /\\ A = B ) )' % FA), imp], 'mtod', '( %s -> -. %s = 0 )' % (FA, D))
    w.qed([ne0], 'neqned', '( %s -> %s =/= 0 )' % (FA, D)); run(w)

    # ---- fareysep
    w = W('fareysep', 'Farey spacing on the line (LargeSieve farey_sep_abs): distinct fractions A / Q and B / R in lowest terms are at distance at least 1 / ( Q R ).')
    q, r, a, b, ga, gb, ne = parts(w, FA, w.s([], 'id', '( %s -> %s )' % (FA, FA)))
    qz = w.s([q], 'nnzd', '( %s -> Q e. ZZ )' % FA); rz = w.s([r], 'nnzd', '( %s -> R e. ZZ )' % FA)
    az = w.s([a], 'nn0zd', '( %s -> A e. ZZ )' % FA); bz = w.s([b], 'nn0zd', '( %s -> B e. ZZ )' % FA)
    dz = w.s([w.s([az, rz], 'zmulcld', '( %s -> ( A x. R ) e. ZZ )' % FA), w.s([bz, qz], 'zmulcld', '( %s -> ( B x. Q ) e. ZZ )' % FA)], 'zsubcld', '( %s -> %s e. ZZ )' % (FA, D))
    dn = w.s([], 'fareyseplem', '( %s -> %s =/= 0 )' % (FA, D))
    ad = w.s([dz, dn, w.inst('nnabscl')], 'syl2anc', '( %s -> ( abs ` %s ) e. NN )' % (FA, D))
    qr = w.s([q, r], 'nnmulcld', '( %s -> ( Q x. R ) e. NN )' % FA)
    le = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % FA), w.s([ad], 'nnred', '( %s -> ( abs ` %s ) e. RR )' % (FA, D)), w.s([qr], 'nnrpd', '( %s -> ( Q x. R ) e. RR+ )' % FA), w.s([ad], 'nnge1d', '( %s -> 1 <_ ( abs ` %s ) )' % (FA, D))], 'lediv1dd', '( %s -> ( 1 / ( Q x. R ) ) <_ ( ( abs ` %s ) / ( Q x. R ) ) )' % (FA, D))
    qc = w.s([q], 'nncnd', '( %s -> Q e. CC )' % FA); rc = w.s([r], 'nncnd', '( %s -> R e. CC )' % FA)
    ds = w.s([w.s([az], 'zcnd', '( %s -> A e. CC )' % FA), qc, w.s([bz], 'zcnd', '( %s -> B e. CC )' % FA), rc, w.s([q], 'nnne0d', '( %s -> Q =/= 0 )' % FA), w.s([r], 'nnne0d', '( %s -> R =/= 0 )' % FA)], 'divsubdivd', '( %s -> ( ( A / Q ) - ( B / R ) ) = ( %s / ( Q x. R ) ) )' % (FA, D))
    qrr = w.s([qr], 'nnred', '( %s -> ( Q x. R ) e. RR )' % FA)
    ab1 = w.s([w.s([dz], 'zcnd', '( %s -> %s e. CC )' % (FA, D)), w.s([qr], 'nncnd', '( %s -> ( Q x. R ) e. CC )' % FA), w.s([qr], 'nnne0d', '( %s -> ( Q x. R ) =/= 0 )' % FA)], 'absdivd', '( %s -> ( abs ` ( %s / ( Q x. R ) ) ) = ( ( abs ` %s ) / ( abs ` ( Q x. R ) ) ) )' % (FA, D, D))
    ab2 = w.s([qrr, w.s([w.s([qr], 'nnrpd', '( %s -> ( Q x. R ) e. RR+ )' % FA)], 'rpge0d', '( %s -> 0 <_ ( Q x. R ) )' % FA)], 'absidd', '( %s -> ( abs ` ( Q x. R ) ) = ( Q x. R ) )' % FA)
    ab3 = w.s([ab1, w.s([ab2], 'oveq2d', '( %s -> ( ( abs ` %s ) / ( abs ` ( Q x. R ) ) ) = ( ( abs ` %s ) / ( Q x. R ) ) )' % (FA, D, D))], 'eqtrd', '( %s -> ( abs ` ( %s / ( Q x. R ) ) ) = ( ( abs ` %s ) / ( Q x. R ) ) )' % (FA, D, D))
    ab4 = w.s([w.s([ds], 'fveq2d', '( %s -> ( abs ` ( ( A / Q ) - ( B / R ) ) ) = ( abs ` ( %s / ( Q x. R ) ) ) )' % (FA, D)), ab3], 'eqtrd', '( %s -> ( abs ` ( ( A / Q ) - ( B / R ) ) ) = ( ( abs ` %s ) / ( Q x. R ) ) )' % (FA, D))
    w.qed([le, ab4], 'breqtrrd', S_fareysep); run(w)
