"""Sortie ZR: generic lemmas zrrec (Re of 1/Z), zrexp (the exp pole bound), zrisre (Re of a series)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift


def gen_rec():
    w = W('zrrec', 'The real part of ` 1 / Z ` is ` Re Z / abs Z ^ 2 ` ( ~ recval , ~ redivd , ~ recj ).')
    A0 = ante_of(S['zrrec'])[0]
    c = Ctx(w, A0)
    zc = c.g('Z e. CC'); zn = c.g('Z =/= 0')
    rv = c([zc, zn], 'jca', '( Z e. CC /\\ Z =/= 0 )')
    e1 = c([rv, w.inst('recval')], 'syl', '( 1 / Z ) = ( ( * ` Z ) / ( ( abs ` Z ) ^ 2 ) )')
    AB = '( ( abs ` Z ) ^ 2 )'
    ar = c([c([zc], 'abscld', '( abs ` Z ) e. RR')], 'resqcld', '%s e. RR' % AB)
    a0 = c([zc, zn], 'absne0d', '( abs ` Z ) =/= 0')
    acc = c([c([zc], 'abscld', '( abs ` Z ) e. RR')], 'recnd', '( abs ` Z ) e. CC')
    an = c([a0, c([acc, w.inst('sqne0')], 'syl', '( %s =/= 0 <-> ( abs ` Z ) =/= 0 )' % AB)], 'mpbird', '%s =/= 0' % AB)
    cj = c([zc], 'cjcld', '( * ` Z ) e. CC')
    e2 = c([ar, cj, an], 'redivd', '( Re ` ( ( * ` Z ) / %s ) ) = ( ( Re ` ( * ` Z ) ) / %s )' % (AB, AB))
    e3 = c([c([zc], 'recjd', '( Re ` ( * ` Z ) ) = ( Re ` Z )')], 'oveq1d', '( ( Re ` ( * ` Z ) ) / %s ) = ( ( Re ` Z ) / %s )' % (AB, AB))
    e0 = c([e1], 'fveq2d', '( Re ` ( 1 / Z ) ) = ( Re ` ( ( * ` Z ) / %s ) )' % AB)
    fin = c([c([e0, e2], 'eqtrd', '( Re ` ( 1 / Z ) ) = ( ( Re ` ( * ` Z ) ) / %s )' % AB), e3], 'eqtrd', '( Re ` ( 1 / Z ) ) = ( ( Re ` Z ) / %s )' % AB)
    w.qed([fin], 'idi', S['zrrec'])
    return run8(w)


def gen_exp():
    w = W('zrexp', 'Lean ` norm_inv_exp_sub_one_sub_inv_le ` : ` abs ( 1 / ( exp V - 1 ) - 1 / V ) <_ 10 ` for ` 0 < abs V <_ 9 / 10 ` ( ~ zl3eqb , ~ abs2difd , ~ subrecd ).')
    A0 = ante_of(S['zrexp'])[0]
    c = Ctx(w, A0)
    vc = c.g('V e. CC'); vn = c.g('V =/= 0'); vb = c.g('( abs ` V ) <_ ( 9 / ; 1 0 )')
    E = '( exp ` V )'; D = '( %s - 1 )' % E
    ec = c([vc], 'efcld', '%s e. CC' % E)
    dc = c([ec, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % D)
    a, d, e = '( abs ` V )', '( abs ` %s )' % D, '( abs ` ( %s - V ) )' % D
    ar = c([vc], 'abscld', '%s e. RR' % a); dr = c([dc], 'abscld', '%s e. RR' % d)
    er = c([c([dc, vc], 'subcld', '( %s - V ) e. CC' % D)], 'abscld', '%s e. RR' % e)
    ap = c([vn, c([vc, w.inst('absgt0')], 'syl', '( V =/= 0 <-> 0 < %s )' % a)], 'mpbid', '0 < %s' % a)
    lv = {a: ar, d: dr, e: er}
    a1 = lin8(w, A0, [vb], '%s <_ 1' % a, lv)
    h1 = c([c([vc, a1], 'jca', '( V e. CC /\\ %s <_ 1 )' % a), w.inst('zl3eqb')], 'syl', '%s <_ ( %s ^ 2 )' % (e, a))
    h2a = c([vc, dc], 'abs2difd', '( %s - %s ) <_ ( abs ` ( V - %s ) )' % (a, d, D))
    h2b = c([vc, dc], 'abssubd', '( abs ` ( V - %s ) ) = %s' % (D, e))
    h2 = c([h2a, h2b], 'breqtrd', '( %s - %s ) <_ %s' % (a, d, e))
    pa = c([c([ap], 'ltled', '0 <_ %s' % a), lin8(w, A0, [vb], '0 <_ ( ( 9 / ; 1 0 ) - %s )' % a, lv)], 'mulge0d', '0 <_ ( %s x. ( ( 9 / ; 1 0 ) - %s ) )' % (a, a))
    dl = lin8(w, A0, [h1, h2, pa], '( %s / ; 1 0 ) <_ %s' % (a, d), lv, products=True)
    dp = lin8(w, A0, [dl, ap], '0 < %s' % d, lv)
    abz = c([dc, w.inst('abs00')], 'syl', '( %s = 0 <-> %s = 0 )' % (d, D))
    nb = c([abz], 'necon3bid', '( %s =/= 0 <-> %s =/= 0 )' % (d, D))
    dnz = c([c([dp], 'gt0ne0d', '%s =/= 0' % d), nb], 'mpbid', '%s =/= 0' % D)
    sr = c([dc, vc, dnz, vn], 'subrecd', '( ( 1 / %s ) - ( 1 / V ) ) = ( ( V - %s ) / ( %s x. V ) )' % (D, D, D))
    DV = '( %s x. V )' % D
    dvc = c([dc, vc], 'mulcld', '%s e. CC' % DV)
    dvn = c([dc, vc, dnz, vn], 'mulne0d', '%s =/= 0' % DV)
    ab1 = c([c([vc, dc], 'subcld', '( V - %s ) e. CC' % D), dvc, dvn], 'absdivd', '( abs ` ( ( V - %s ) / %s ) ) = ( ( abs ` ( V - %s ) ) / ( abs ` %s ) )' % (D, DV, D, DV))
    ab2 = c([dc, vc], 'absmuld', '( abs ` %s ) = ( %s x. %s )' % (DV, d, a))
    Y = '( %s x. %s )' % (d, a)
    ab3 = c([h2b, ab2], 'oveq12d', '( ( abs ` ( V - %s ) ) / ( abs ` %s ) ) = ( %s / %s )' % (D, DV, e, Y))
    L0 = '( abs ` ( ( 1 / %s ) - ( 1 / V ) ) )' % D
    eq = c([c([sr], 'fveq2d', '%s = ( abs ` ( ( V - %s ) / %s ) )' % (L0, D, DV)), c([ab1, ab3], 'eqtrd', '( abs ` ( ( V - %s ) / %s ) ) = ( %s / %s )' % (D, DV, e, Y))],
            'eqtrd', '%s = ( %s / %s )' % (L0, e, Y))
    yp = c([c([dr, ar], 'remulcld', '%s e. RR' % Y), c([dp, ap], 'mulgt0d', '0 < %s' % Y)], 'elrpd', '%s e. RR+' % Y)
    pb = c([c([ap], 'ltled', '0 <_ %s' % a), lin8(w, A0, [dl], '0 <_ ( %s - ( %s / ; 1 0 ) )' % (d, a), lv)], 'mulge0d', '0 <_ ( %s x. ( %s - ( %s / ; 1 0 ) ) )' % (a, d, a))
    key = lin8(w, A0, [h1, pb], '%s <_ ( ; 1 0 x. %s )' % (e, Y), lv, products=True)
    t10 = numst8(w, A0, '; 1 0', 'RR')
    le = c([key, c([er, t10, yp], 'ledivmul2d', '( ( %s / %s ) <_ ; 1 0 <-> %s <_ ( ; 1 0 x. %s ) )' % (e, Y, e, Y))], 'mpbird', '( %s / %s ) <_ ; 1 0' % (e, Y))
    fin = c([eq, le], 'eqbrtrd', '%s <_ ; 1 0' % L0)
    w.qed([fin], 'idi', S['zrexp'])
    return run8(w)


def gen_isre():
    w = W('zrisre', 'The real part of a convergent complex series is the sum of the real parts, which converges ( ~ climre , ~ fsumre , ~ isumclim ).')
    A0 = ante_of(S['zrisre'])[0]
    c = Ctx(w, A0)
    ff = c.g('F : NN --> CC'); dm = c.g('seq 1 ( + , F ) e. dom ~~>')
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    fk = ck([lift(w, ff, Ak), kn], 'ffvelcdmd', '( F ` k ) e. CC')
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = c([], '1zzd', '1 e. ZZ')
    eqk = ck([], 'eqidd', '( F ` k ) = ( F ` k )')
    SF = 'sum_ k e. NN ( F ` k )'
    cl1 = c([nnu, one, eqk, fk, dm], 'isumclim2', 'seq 1 ( + , F ) ~~> %s' % SF)
    G = 'seq 1 ( + , ( Re o. F ) )'
    gv = c.a1(w.s([], 'seqex', '%s e. _V' % G), '%s e. _V' % G)
    An = '( %s /\\ n e. NN )' % A0
    cn = Ctx(w, An)
    nn_ = cn([], 'simpr', 'n e. NN')
    Aj = '( %s /\\ j e. ( 1 ... n ) )' % An
    cj = Ctx(w, Aj)
    jn = cj([cj([], 'simpr', 'j e. ( 1 ... n )'), w.inst('elfznn')], 'syl', 'j e. NN')
    fj = cj([lift(w, ff, Aj), jn], 'ffvelcdmd', '( F ` j ) e. CC')
    eqj = cj([], 'eqidd', '( F ` j ) = ( F ` j )')
    nuz = cn([nn_, w.inst('elnnuz')], 'sylib', 'n e. ( ZZ>= ` 1 )')
    s1 = cn([eqj, nuz, fj], 'fsumser', 'sum_ j e. ( 1 ... n ) ( F ` j ) = ( seq 1 ( + , F ) ` n )')
    fcj = cj([lift(w, ff, Aj), jn, w.inst('fvco3')], 'syl2anc', '( ( Re o. F ) ` j ) = ( Re ` ( F ` j ) )')
    rj = cj([fj], 'recld', '( Re ` ( F ` j ) ) e. RR')
    s2 = cn([fcj, nuz, cj([rj], 'recnd', '( Re ` ( F ` j ) ) e. CC')], 'fsumser', 'sum_ j e. ( 1 ... n ) ( Re ` ( F ` j ) ) = ( %s ` n )' % G)
    s3 = cn([cn([], 'fzfid', '( 1 ... n ) e. Fin'), fj], 'fsumre', '( Re ` sum_ j e. ( 1 ... n ) ( F ` j ) ) = sum_ j e. ( 1 ... n ) ( Re ` ( F ` j ) )')
    s4 = cn([s1], 'fveq2d', '( Re ` sum_ j e. ( 1 ... n ) ( F ` j ) ) = ( Re ` ( seq 1 ( + , F ) ` n ) )')
    gk = cn([cn([s2], 'eqcomd', '( %s ` n ) = sum_ j e. ( 1 ... n ) ( Re ` ( F ` j ) )' % G),
             cn([cn([s3], 'eqcomd', 'sum_ j e. ( 1 ... n ) ( Re ` ( F ` j ) ) = ( Re ` sum_ j e. ( 1 ... n ) ( F ` j ) )'), s4], 'eqtrd',
                'sum_ j e. ( 1 ... n ) ( Re ` ( F ` j ) ) = ( Re ` ( seq 1 ( + , F ) ` n ) )')], 'eqtrd', '( %s ` n ) = ( Re ` ( seq 1 ( + , F ) ` n ) )' % G)
    pk = cn([s1, cn([cn([], 'fzfid', '( 1 ... n ) e. Fin'), fj], 'fsumcl', 'sum_ j e. ( 1 ... n ) ( F ` j ) e. CC')], 'eqeltrrd', '( seq 1 ( + , F ) ` n ) e. CC')
    cl2 = c([nnu, cl1, gv, one, pk, gk], 'climre', '%s ~~> ( Re ` %s )' % (G, SF))
    rd = w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( %s ~~> ( Re ` %s ) -> %s e. dom ~~> )' % (G, SF, G))
    dm2 = c([cl2, rd], 'syl', '%s e. dom ~~>' % G)
    fck = ck([lift(w, ff, Ak), kn, w.inst('fvco3')], 'syl2anc', '( ( Re o. F ) ` k ) = ( Re ` ( F ` k ) )')
    rk = ck([ck([fk], 'recld', '( Re ` ( F ` k ) ) e. RR')], 'recnd', '( Re ` ( F ` k ) ) e. CC')
    e = c([nnu, one, fck, rk, cl2], 'isumclim', 'sum_ k e. NN ( Re ` ( F ` k ) ) = ( Re ` %s )' % SF)
    fin = c([c([e], 'eqcomd', '( Re ` %s ) = sum_ k e. NN ( Re ` ( F ` k ) )' % SF), dm2], 'jca', ante_of(S['zrisre'])[1])
    w.qed([fin], 'idi', S['zrisre'])
    return run8(w)


def gen_sadd():
    w = W('zrsadd', 'The sum of two convergent series ( ~ climadd , ~ seradd , ~ serf ).')
    A0 = ante_of(S['zrsadd'])[0]
    c = Ctx(w, A0)
    ff = c.g('F : NN --> CC'); gf = c.g('G : NN --> CC'); hf = c.g('H : NN --> CC')
    AL = 'A. k e. NN ( H ` k ) = ( ( F ` k ) + ( G ` k ) )'
    al = c.g(AL)
    cf = c.g('seq 1 ( + , F ) ~~> A'); cg = c.g('seq 1 ( + , G ) ~~> B')
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = c([], '1zzd', '1 e. ZZ')
    An = '( %s /\\ n e. NN )' % A0
    cn = Ctx(w, An)
    nn_ = cn([], 'simpr', 'n e. NN')
    sf = {}
    for X, xf in (('F', ff), ('G', gf)):
        xn = cn([lift(w, xf, An), nn_], 'ffvelcdmd', '( %s ` n ) e. CC' % X)
        sf[X] = c([nnu, one, xn], 'serf', 'seq 1 ( + , %s ) : NN --> CC' % X)
    Aj = '( %s /\\ j e. ( 1 ... n ) )' % An
    cj = Ctx(w, Aj)
    jn = cj([cj([], 'simpr', 'j e. ( 1 ... n )'), w.inst('elfznn')], 'syl', 'j e. NN')
    fj = cj([lift(w, ff, Aj), jn], 'ffvelcdmd', '( F ` j ) e. CC')
    gj = cj([lift(w, gf, Aj), jn], 'ffvelcdmd', '( G ` j ) e. CC')
    hj, _ = ral_at(w, Aj, lift(w, al, Aj), 'k', 'j', '( H ` k ) = ( ( F ` k ) + ( G ` k ) )', jn)
    nuz = cn([nn_, w.inst('elnnuz')], 'sylib', 'n e. ( ZZ>= ` 1 )')
    sa = cn([nuz, fj, gj, hj], 'seradd', '( seq 1 ( + , H ) ` n ) = ( ( seq 1 ( + , F ) ` n ) + ( seq 1 ( + , G ) ` n ) )')
    sfn = cn([lift(w, sf['F'], An), nn_], 'ffvelcdmd', '( seq 1 ( + , F ) ` n ) e. CC')
    sgn = cn([lift(w, sf['G'], An), nn_], 'ffvelcdmd', '( seq 1 ( + , G ) ` n ) e. CC')
    hv = c.a1(w.s([], 'seqex', 'seq 1 ( + , H ) e. _V'), 'seq 1 ( + , H ) e. _V')
    fin = c([nnu, one, cf, hv, cg, sfn, sgn, sa], 'climadd', 'seq 1 ( + , H ) ~~> ( A + B )')
    w.qed([fin], 'idi', S['zrsadd'])
    return run8(w)


GENS = {'zrrec': gen_rec, 'zrexp': gen_exp, 'zrisre': gen_isre, 'zrsadd': gen_sadd}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
