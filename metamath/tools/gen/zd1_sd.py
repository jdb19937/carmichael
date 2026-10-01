"""Sortie ZD1: Lemma 8.1 as a series bound (Lean sigma_diag_le, generic in the summand)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import lift
from zd1_hb import fnre

K = '( %s x. %s )' % (C12, XB)
G = 'seq 1 ( + , F )'
KC = '( NN X. { %s } )' % K


def zdsigdiag():
    w = W('zdsigdiag', "Lemma 8.1, the diagonal (Lean sigma_diag_le): for log D >_ 200, 99 / 100 <_ T <_ 1 and any nonnegative F on NN with "
                       "F ( n ) <_ 3 f ( n ) e ^ ( - n / X ) (Lean cDet_sq_div_bMaj_le_term), the series of F converges and its sum is "
                       "<_ 10 ^ 9 X ^ ( 2 - 2 T ).  Log-free: the log X of I4* is cancelled by the window width ell = log D / 100.")
    hyps_of(w, 'zdsigdiag')
    ante = 'ph'
    st = mkst(w, ante)
    h0 = bind(w, ante, '1', '2', HZD, HT)
    f = h0facts(w, ante, h0)
    xbr = st([st([f['xprp'], f['br']], 'rpcxpcld', '%s e. RR+' % XB)], 'rpred', '%s e. RR' % XB)
    kr = st([litr(w, ante, C12), xbr], 'remulcld', '%s e. RR' % K)
    # partial sums: ( ( ph /\ j e. NN ) -> ( G ` j ) <_ K )
    a = '( ph /\\ j e. NN )'
    sa = mkst(w, a)
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % a)
    R = '( 1 ... j )'
    b = '( %s /\\ n e. %s )' % (a, R)
    sb = mkst(w, b)
    nn = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (b, R)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % b)
    phb = w.s([], 'simpll', '( %s -> ph )' % b)
    fr = w.s([phb, nn, '3'], 'syl2anc', '( %s -> ( F ` n ) e. RR )' % b)
    fl = w.s([phb, nn, '5'], 'syl2anc', '( %s -> ( F ` n ) <_ ( 3 x. ( %s x. %s ) ) )' % (b, FN('n'), EN('n')))
    fnr = fnre(w, b, nn, lift(w, f['dr'], b), lift(w, f['d1'], b), lift(w, f['tr'], b))
    ndx = sb([sb([sb([nn], 'nnred', 'n e. RR')], 'renegcld', '-u n e. RR'), lift(w, f['xprp'], b)], 'rerpdivcld', '( -u n / %s ) e. RR' % XP)
    TT = '( %s x. %s )' % (FN('n'), EN('n'))
    ttr = sb([fnr, sb([ndx], 'reefcld', '%s e. RR' % EN('n'))], 'remulcld', '%s e. RR' % TT)
    fin = sa([], 'fzfid', '%s e. Fin' % R)
    s1 = sa([fin, fr, sb([a1c(w, b, '3re', '3 e. RR'), ttr], 'remulcld', '( 3 x. %s ) e. RR' % TT), fl], 'fsumle',
            'sum_ n e. %s ( F ` n ) <_ sum_ n e. %s ( 3 x. %s )' % (R, R, TT))
    ST = 'sum_ n e. %s %s' % (R, TT)
    mc = sa([fin, a1c(w, a, '3cn', '3 e. CC'), w.s([ttr], 'recnd', '( %s -> %s e. CC )' % (b, TT))], 'fsummulc2',
            '( 3 x. %s ) = sum_ n e. %s ( 3 x. %s )' % (ST, R, TT))
    sf = w.s([lift(w, h0, a), jn, w.inst('zdsigfin')], 'syl2anc', '( %s -> %s <_ ( %s x. %s ) )' % (a, ST.replace('( 1 ... j )', '( 1 ... j )'), C12T, XB))
    str_ = sa([fin, ttr], 'fsumrecl', '%s e. RR' % ST)
    SF = 'sum_ n e. %s ( F ` n )' % R
    sfr = sa([fin, fr], 'fsumrecl', '%s e. RR' % SF)
    s1b = sa([s1, mc], 'breqtrrd', '%s <_ ( 3 x. %s )' % (SF, ST))
    bound = linarith(w, a, [s1b, sf], '%s <_ %s' % (SF, K), leaves={SF: sfr, ST: str_, XB: lift(w, xbr, a)})
    juz = w.s([jn, w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylib', '( %s -> j e. ( ZZ>= ` 1 ) )' % a)
    ser = sa([w.s([], 'eqidd', '( %s -> ( F ` n ) = ( F ` n ) )' % b), juz, w.s([fr], 'recnd', '( %s -> ( F ` n ) e. CC )' % b)], 'fsumser',
             '%s = ( %s ` j )' % (SF, G))
    pk = sa([ser, bound], 'eqbrtrrd', '( %s ` j ) <_ %s' % (G, K))
    gr = sa([ser, sfr], 'eqeltrrd', '( %s ` j ) e. RR' % G)
    # convergence (isumsup2, with its k := n)
    ral = w.s([pk], 'ralrimiva', '( ph -> A. j e. NN ( %s ` j ) <_ %s )' % (G, K))
    cg = w.s([w.s([], 'breq2', '( x = %s -> ( ( %s ` j ) <_ x <-> ( %s ` j ) <_ %s ) )' % (K, G, G, K))], 'ralbidv',
             '( x = %s -> ( A. j e. NN ( %s ` j ) <_ x <-> A. j e. NN ( %s ` j ) <_ %s ) )' % (K, G, G, K))
    ex = w.s([kr, ral, w.s([cg], 'rspcev', '( ( %s e. RR /\\ A. j e. NN ( %s ` j ) <_ %s ) -> E. x e. RR A. j e. NN ( %s ` j ) <_ x )' % (K, G, K, G))],
             'syl2anc', '( ph -> E. x e. RR A. j e. NN ( %s ` j ) <_ x )' % G)
    nuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    eqg = w.s([], 'eqid', '%s = %s' % (G, G))
    one = w.s([], '1zzd', '( ph -> 1 e. ZZ )')
    an = '( ph /\\ n e. NN )'
    fe = w.s([], 'eqidd', '( %s -> ( F ` n ) = ( F ` n ) )' % an)
    SUP = 'sup ( ran %s , RR , < )' % G
    cv = w.s([nuz, eqg, one, fe, '3', '4', ex], 'isumsup2', '( ph -> %s ~~> %s )' % (G, SUP))
    dm = w.s([w.s([], 'climrel', 'Rel ~~>'), cv, w.inst('releldm')], 'sylancr', '( ph -> %s e. dom ~~> )' % G)
    SN = 'sum_ n e. NN ( F ` n )'
    cl2 = w.s([nuz, one, fe, w.s(['3'], 'recnd', '( %s -> ( F ` n ) e. CC )' % an), dm], 'isumclim2', '( ph -> %s ~~> %s )' % (G, SN))
    # the constant sequence
    kc = w.s([w.s([kr], 'recnd', '( ph -> %s e. CC )' % K), one,
              w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqimss2i', '( ZZ>= ` 1 ) C_ NN'), w.s([], 'nnex', 'NN e. _V')], 'climconst2',
                  '( ( %s e. CC /\\ 1 e. ZZ ) -> %s ~~> %s )' % (K, KC, K))], 'syl2anc', '( ph -> %s ~~> %s )' % (KC, K))
    fv = w.s([lift(w, kr, a), jn, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` j ) = %s )' % (a, KC, K))
    kcr = w.s([fv, lift(w, kr, a)], 'eqeltrd', '( %s -> ( %s ` j ) e. RR )' % (a, KC))
    le8 = w.s([pk, fv], 'breqtrrd', '( %s -> ( %s ` j ) <_ ( %s ` j ) )' % (a, G, KC))
    sle = w.s([nuz, one, cl2, kc, gr, kcr, le8], 'climle', '( ph -> %s <_ %s )' % (SN, K))
    w.qed([dm, sle], 'jca', STATEMENTS['zdsigdiag'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['zdsigdiag']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
