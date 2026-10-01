"""T7: the ` _le_B ` forms of the delivered composites at the encodings of
numbers below ` 2 ^ N ` (Lean ` dup_le_B ` , ` dropNum_le_B ` , ` isZero_le_B ` ,
` incr_le_B ` , ` predNum_le_B ` , ` cmp_correct ` ), and the N-level fact
` predBits ( encodeNat F ) = encodeNat ( F - 1 ) ` .

    MM_DB=sorties/t7.mm python3 tools/gen/t7_v_leb.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7leb import *
from cl import Closure
from lin import linarith, lineq
from t7_e_cmp import machine
import num

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def S_(l):
    return dict(STMTS7)[l]


def enc_facts(w, ph, F, fnn, nn, flt, fpos=False):
    """for F < 2 ^ N: ( encodeNat ` F ) typed, encNatGam ` F = inclBool o. it, lengths <_ N"""
    EF = '( encodeNat ` %s )' % F
    fn0 = w.s([fnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, F)) if fpos else fnn
    ef = w.s([fn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    gv = w.s([fn0, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (ph, F, EF))
    le = w.s([fn0, nn, flt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` %s ) <_ N )' % (ph, EF))
    return dict(EF=EF, fn0=fn0, ef=ef, gv=gv, le=le)


def tmb_lin(w, ph, nn, cst):
    """( ph -> ( c x. ( N + 2 ) ) <_ ( TMB ` N ) )"""
    cn = closed(w, ph, '%snn0' % cst, '%s e. NN0' % cst)
    le = w.s([num.le_lit(w, cst, '; 6 4')], 'a1i', '( %s -> %s <_ ; 6 4 )' % (ph, cst))
    return w.s([w.s([nn, cn, le], '3jca', '( %s -> ( N e. NN0 /\\ %s e. NN0 /\\ %s <_ ; 6 4 ) )' % (ph, cst, cst)), w.inst('tmblin')], 'syl',
               '( %s -> ( %s x. ( N + 2 ) ) <_ ( TMB ` N ) )' % (ph, cst))


def finish(w, ph, phm, tri, C, D, n, nn, leaves, hyps, cst):
    tb0 = w.s([w.s([nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` N ) e. NN0 )' % ph)
    tl = tmb_lin(w, ph, nn, cst)
    lv = dict(leaves); lv['N'] = nn; lv['( TMB ` N )'] = tb0
    cl = Closure(w, ph, {k: ('NN0', v) for k, v in lv.items()})
    n0 = w.s([nn], 'nn0ge0d', '( %s -> 0 <_ N )' % ph)
    le = linarith(w, ph, list(hyps) + [tl, n0], '%s <_ ( TMB ` N )' % n, closure=cl)
    hrle(w, ph, phm, tri, C, D, n, '( TMB ` N )', tb0, le, qed=True)


def tmcdupb():
    lab = 'tmcdupb'
    ph = cj(TREE_DUPB)
    w = W(lab, '` dup_le_B ` at the machine: ` dup x y s ` on the encoding of ` F < 2 ^ N ` in ` ( TMB ` N ) ` '
               'steps (~ tmcdup ).')
    c = Ctx(w, ph, TREE_DUPB)
    phm = c[PHM]
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    ib = w.s([e['ef'], w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, e['EF'], BITS))
    wb = w.s([e['gv'], ib], 'eqeltrd', '( %s -> %s e. Word %s )' % (ph, ENF, BITS))
    bld = Builder(w, ph, c, {'T e. V': w.s([phm], 'simpld', '( %s -> T e. V )' % ph), MTY: w.s([phm], 'simprd', '( %s -> %s )' % (ph, MTY)),
                             WRD(ENF, BITS): wb})
    t, cc = inst(w, ph, 'tmcdup', {'W': ENF}, bld)
    C1, D1, n1 = triple_parts(cc)
    ln = w.s([w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF, e['EF'])),
                   w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))], 'eqtrd',
                  '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF, e['EF']))], 'id', None) if False else \
        w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF, e['EF'])),
             w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))], 'eqtrd',
            '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF, e['EF']))
    lw = w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENF))
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t, C1, D1, n1, c['N e. NN0'], {'( # ` %s )' % ENF: lw, '( # ` %s )' % e['EF']: le0}, [ln, e['le']], '3')
    return w.run()


def base(w, ph, c):
    phm = c[PHM]
    return phm, {'T e. V': w.s([phm], 'simpld', '( %s -> T e. V )' % ph), MTY: w.s([phm], 'simprd', '( %s -> %s )' % (ph, MTY))}


def enc_bits(w, ph, e, F='F'):
    ib = w.s([e['ef'], w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. %s ) e. Word %s )' % (ph, e['EF'], BITS))
    return w.s([e['gv'], ib], 'eqeltrd', '( %s -> ( encNatGam ` %s ) e. Word %s )' % (ph, F, BITS))


def dk_inc(w, ph, e, dk, F='F', X='X', K='K'):
    """( D ` K ) = ( inclBool o. EF ) ++ ... from the encNatGam form"""
    ENX = '( encNatGam ` %s )' % F
    return w.s([dk, w.s([e['gv']], 'oveq1d', '( %s -> ( %s ++ ( <" 4 "> ++ %s ) ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, ENX, X, e['EF'], X))], 'eqtrd',
               '( %s -> ( D ` %s ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, K, e['EF'], X))


def tmcdropb():
    lab = 'tmcdropb'
    ph = cj(TREE_DROPB)
    w = W(lab, '` dropNum_le_B ` at the machine: ` dropNum x ` on the encoding of ` F < 2 ^ N ` in ` ( TMB ` N ) ` '
               'steps (~ tmcdrop ; the state is left arbitrary).')
    c = Ctx(w, ph, TREE_DROPB)
    phm, ex = base(w, ph, c)
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    wb = enc_bits(w, ph, e)
    ex[WRD(ENF, BITS)] = wb
    t, cc = inst(w, ph, 'tmcdrop', {'W': ENF}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    ln = w.s([w.s([e['gv']], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( inclBool o. %s ) ) )' % (ph, ENF, e['EF'])),
              w.s([e['ef'], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, e['EF'], e['EF']))], 'eqtrd',
             '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENF, e['EF']))
    lw = w.s([wb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENF))
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t, C1, D1, n1, c['N e. NN0'], {'( # ` %s )' % ENF: lw, '( # ` %s )' % e['EF']: le0}, [ln, e['le']], '1')
    return w.run()


def tmcizb():
    lab = 'tmcizb'
    ph = cj(TREE_IZB)
    w = W(lab, '` isZero_le_B ` at the machine: ` isZero x s ` on the encoding of ` F < 2 ^ N ` sets ` flag ` to '
               '` [ F = 0 ] ` , keeps ` cmp ` , in ` ( TMB ` N ) ` steps (~ tmciz ).')
    c = Ctx(w, ph, TREE_IZB)
    phm, ex = base(w, ph, c)
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    dki = dk_inc(w, ph, e, c[DK_F])
    ex[WRD(e['EF'], '2o')] = e['ef']
    ex[formula(w, dki)[len('( %s -> ' % ph):-2]] = dki
    t, cc = inst(w, ph, 'tmciz', {'L': e['EF']}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    tn = w.s([e['fn0'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, e['EF']))
    r, new = w.rewrite(D1, {'( toNat ` %s )' % e['EF']: ('F', tn)}, ph)
    t2, C2, D2, n2 = hrrw(w, ph, t, C1, D1, n1, deq=r)
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t2, C2, D2, n2, c['N e. NN0'], {'( # ` %s )' % e['EF']: le0}, [e['le']], '3')
    return w.run()


def tmcincb():
    lab = 'tmcincb'
    ph = cj(TREE_INCB)
    w = W(lab, '` incr_le_B ` at the machine: ` incr y s ` on the encoding of ` F < 2 ^ N ` leaves the encoding of '
               '` F + 1 ` , keeps ` flag ` , ` cmp ` , ` carry ` , in ` ( TMB ` N ) ` steps (~ tmcincr , ~ encnatsuc ).')
    c = Ctx(w, ph, TREE_INCB)
    phm, ex = base(w, ph, c)
    e = enc_facts(w, ph, 'F', c['F e. NN0'], c['N e. NN0'], c['F < ( 2 ^ N )'])
    dki = dk_inc(w, ph, e, c[DK_F])
    ex[WRD(e['EF'], '2o')] = e['ef']
    ex[formula(w, dki)[len('( %s -> ' % ph):-2]] = dki
    t, cc = inst(w, ph, 'tmcincr', {'L': e['EF']}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    f1 = w.s([e['fn0'], w.inst('peano2nn0')], 'syl', '( %s -> ( F + 1 ) e. NN0 )' % ph)
    es = w.s([e['fn0'], w.inst('encnatsuc')], 'syl', '( %s -> ( encodeNat ` ( F + 1 ) ) = ( incBits ` %s ) )' % (ph, e['EF']))
    g1 = w.s([f1, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` ( F + 1 ) ) = ( inclBool o. ( encodeNat ` ( F + 1 ) ) ) )' % ph)
    v = w.s([g1, w.s([es], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` ( F + 1 ) ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ph, e['EF']))], 'eqtrd',
            '( %s -> ( encNatGam ` ( F + 1 ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ph, e['EF']))
    vr = w.s([v], 'eqcomd', '( %s -> ( inclBool o. ( incBits ` %s ) ) = ( encNatGam ` ( F + 1 ) ) )' % (ph, e['EF']))
    r, new = w.rewrite(D1, {'( inclBool o. ( incBits ` %s ) )' % e['EF']: ('( encNatGam ` ( F + 1 ) )', vr)}, ph)
    t2, C2, D2, n2 = hrrw(w, ph, t, C1, D1, n1, deq=r)
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t2, C2, D2, n2, c['N e. NN0'], {'( # ` %s )' % e['EF']: le0}, [e['le']], '2')
    return w.run()


def tmccmpb():
    lab = 'tmccmpb'
    ph = cj(TREE_CMPB)
    w = W(lab, '` cmp_correct ` at the machine with a ` TMB ` bound: ` cmpFrag x y ` on the encodings of '
               '` F , G < 2 ^ N ` consumes both and sets ` cmp ` to ` F Ncmp G ` (~ tmccmp ).')
    c = Ctx(w, ph, TREE_CMPB)
    phm, ex = base(w, ph, c)
    nn = c['N e. NN0']
    e = enc_facts(w, ph, 'F', c['F e. NN0'], nn, c['F < ( 2 ^ N )'])
    g = enc_facts(w, ph, 'G', c['G e. NN0'], nn, c['G < ( 2 ^ N )'])
    dk = dk_inc(w, ph, e, c[DK_F])
    dj = dk_inc(w, ph, g, c['( D ` J ) = ( %s ++ ( <" 4 "> ++ Y ) )' % ENG], 'G', 'Y', 'J')
    ex[WRD(e['EF'], '2o')] = e['ef']; ex[WRD(g['EF'], '2o')] = g['ef']
    for st in (dk, dj):
        ex[formula(w, st)[len('( %s -> ' % ph):-2]] = st
    t, cc = inst(w, ph, 'tmccmp', {'L': e['EF'], "L'": g['EF']}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    tf = w.s([e['fn0'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, e['EF']))
    tg = w.s([g['fn0'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ph, g['EF']))
    r, new = w.rewrite(D1, {'( toNat ` %s )' % e['EF']: ('F', tf), '( toNat ` %s )' % g['EF']: ('G', tg)}, ph)
    t2, C2, D2, n2 = hrrw(w, ph, t, C1, D1, n1, deq=r)
    A_, B_ = '( # ` %s )' % e['EF'], '( # ` %s )' % g['EF']
    a0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, A_))
    b0 = w.s([g['ef'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, B_))
    MX = 'if ( %s <_ %s , %s , %s )' % (A_, B_, B_, A_)
    cl = Closure(w, ph, {A_: ('NN0', a0), B_: ('NN0', b0), 'N': ('NN0', nn)})
    mle = w.s([cl.mem(A_, 'RR'), cl.mem(B_, 'RR'), cl.mem('N', 'RR'), w.inst('maxle')], 'syl3anc', '( %s -> ( %s <_ N <-> ( %s <_ N /\\ %s <_ N ) ) )' % (ph, MX, A_, B_))
    mx = w.s([mle, w.s([e['le'], g['le']], 'jca', '( %s -> ( %s <_ N /\\ %s <_ N ) )' % (ph, A_, B_))], 'mpbird', '( %s -> %s <_ N )' % (ph, MX))
    mx0 = w.s([b0, a0], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MX))
    finish(w, ph, phm, t2, C2, D2, n2, nn, {MX: mx0}, [mx], '1')
    return w.run()


def tmcpredenc():
    lab = 'tmcpredenc'
    ph = 'F e. NN'
    w = W(lab, 'Decrementing the encoding of a positive number gives the encoding of its predecessor (Lean '
               '` canon_predBits ` with ` toNat_predBits ` ): equal values (T4 ~ tonatpredbits ) and equal lengths '
               '(the bit length of ` F - 1 ` drops exactly when ` F ` is a power of two, ~ blchar ).')
    ff = w.s([], 'id', '( %s -> F e. NN )' % ph)
    f0 = w.s([ff], 'nnnn0d', '( %s -> F e. NN0 )' % ph)
    EF = '( encodeNat ` F )'; PB = '( predBits ` %s )' % EF; EM = '( encodeNat ` ( F - 1 ) )'
    fm = w.s([ff, w.inst('nnm1nn0')], 'syl', '( %s -> ( F - 1 ) e. NN0 )' % ph)
    ef = w.s([f0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    pb = w.s([ef, w.inst('predbitscl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, PB))
    em = w.s([fm, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EM))
    tf = w.s([f0, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, EF))
    tm = w.s([fm, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = ( F - 1 ) )' % (ph, EM))
    g1 = w.s([w.s([ff, w.inst('nnge1')], 'syl', '( %s -> 1 <_ F )' % ph), w.s([tf], 'eqcomd', '( %s -> F = ( toNat ` %s ) )' % (ph, EF))], 'breqtrd',
             '( %s -> 1 <_ ( toNat ` %s ) )' % (ph, EF))
    tp = w.s([ef, g1, w.inst('tonatpredbits')], 'syl2anc', '( %s -> ( ( toNat ` %s ) + 1 ) = ( toNat ` %s ) )' % (ph, PB, EF))
    tpb = w.s([pb, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, PB))
    cl = Closure(w, ph, {'( toNat ` %s )' % PB: ('NN0', tpb), 'F': ('NN0', f0), '( toNat ` %s )' % EF: ('NN0', w.s([ef, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, EF)))})
    tv = lineq(w, ph, '( toNat ` %s )' % PB, '( F - 1 )', hyps=[tp, tf], closure=cl)
    teq = w.s([tv, tm], 'eqtr4d', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ph, PB, EM))
    # lengths
    V = '( 2 Nlog F )'
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    two_a = w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    vcl = w.s([closed(w, ph, '2nn0', '2 e. NN0'), f0, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, V))
    lo = w.s([two_a, ff, w.inst('nlogle')], 'syl2anc', '( %s -> ( 2 ^ %s ) <_ F )' % (ph, V))
    hi = w.s([two_a, ff, w.inst('nloglt')], 'syl2anc', '( %s -> F < ( 2 ^ ( %s + 1 ) ) )' % (ph, V))
    blF = w.s([ff, w.inst('blpos')], 'syl', '( %s -> ( bl ` F ) = ( %s + 1 ) )' % (ph, V))
    lEF = w.s([w.s([f0, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = ( bl ` F ) )' % (ph, EF)), blF], 'eqtrd', '( %s -> ( # ` %s ) = ( %s + 1 ) )' % (ph, EF, V))
    pl = w.s([ef, w.inst('predbitslen2')], 'syl', '( %s -> ( # ` %s ) = if ( ( 2 x. ( toNat ` %s ) ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) - 1 ) , ( # ` %s ) ) )' % (ph, PB, EF, EF, EF, EF))
    vc = w.s([vcl], 'nn0cnd', '( %s -> %s e. CC )' % (ph, V))
    pn = w.s([vc, closed(w, ph, 'ax-1cn', '1 e. CC')], 'pncand', '( %s -> ( ( %s + 1 ) - 1 ) = %s )' % (ph, V, V))
    OLDIF = 'if ( ( 2 x. ( toNat ` %s ) ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) - 1 ) , ( # ` %s ) )' % (EF, EF, EF, EF)
    r1, n1 = w.rewrite(OLDIF, {'( toNat ` %s )' % EF: ('F', tf), '( # ` %s )' % EF: ('( %s + 1 )' % V, lEF)}, ph)
    NEWIF = 'if ( ( 2 x. F ) = ( 2 ^ ( %s + 1 ) ) , %s , ( %s + 1 ) )' % (V, V, V)
    r2, n2 = w.rewrite(n1, {'( ( %s + 1 ) - 1 )' % V: (V, pn)}, ph)
    assert n2 == NEWIF, n2
    lpb = w.s([w.s([pl, r1], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (ph, PB, n1)), r2], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (ph, PB, NEWIF))
    lem = w.s([fm, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = ( bl ` ( F - 1 ) ) )' % (ph, EM))
    P2V = '( 2 ^ %s )' % V
    p2v = w.s([closed(w, ph, '2nn', '2 e. NN'), vcl, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, P2V))
    e2 = w.s([closed(w, ph, '2cn', '2 e. CC'), vcl, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( %s x. 2 ) )' % (ph, V, P2V))
    COND = '( 2 x. F ) = ( 2 ^ ( %s + 1 ) )' % V
    # case A: 2 F = 2 ^ ( V + 1 ) , so F = 2 ^ V
    pa = '( %s /\\ %s )' % (ph, COND)
    LA = Lifter(w, pa)
    ca = w.s([], 'simpr', '( %s -> %s )' % (pa, COND))
    clA = Closure(w, pa, {'F': ('NN0', LA(f0, 'F e. NN0')), P2V: ('NN0', w.s([LA(p2v, '%s e. NN' % P2V)], 'nnnn0d', '( %s -> %s e. NN0 )' % (pa, P2V)))})
    fv = lineq(w, pa, 'F', P2V, hyps=[w.s([ca, LA(e2, '( 2 ^ ( %s + 1 ) ) = ( %s x. 2 )' % (V, P2V))], 'eqtrd', '( %s -> ( 2 x. F ) = ( %s x. 2 ) )' % (pa, P2V))], closure=clA)
    ifA = w.s([ca], 'iftrued', '( %s -> %s = %s )' % (pa, NEWIF, V))
    # A1: V = 0
    pa0 = '( %s /\\ %s = 0 )' % (pa, V)
    v0 = w.s([], 'simpr', '( %s -> %s = 0 )' % (pa0, V))
    f1 = w.s([w.s([fv], 'adantr', '( %s -> F = %s )' % (pa0, P2V)), w.s([w.s([v0], 'oveq2d', '( %s -> %s = ( 2 ^ 0 ) )' % (pa0, P2V)),
              w.s([closed(w, pa0, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % pa0)], 'eqtrd', '( %s -> %s = 1 )' % (pa0, P2V))], 'eqtrd',
             '( %s -> F = 1 )' % pa0)
    fm0 = w.s([w.s([f1], 'oveq1d', '( %s -> ( F - 1 ) = ( 1 - 1 ) )' % pa0), closed(w, pa0, '1m1e0', '( 1 - 1 ) = 0')], 'eqtrd', '( %s -> ( F - 1 ) = 0 )' % pa0)
    bl0_ = w.s([w.s([fm0], 'fveq2d', '( %s -> ( bl ` ( F - 1 ) ) = ( bl ` 0 ) )' % pa0), closed(w, pa0, 'bl0', '( bl ` 0 ) = 0')], 'eqtrd', '( %s -> ( bl ` ( F - 1 ) ) = 0 )' % pa0)
    blA0 = w.s([bl0_, w.s([v0], 'eqcomd', '( %s -> 0 = %s )' % (pa0, V))], 'eqtrd', '( %s -> ( bl ` ( F - 1 ) ) = %s )' % (pa0, V))
    # A2: V e. NN
    pa1 = '( %s /\\ %s e. NN )' % (pa, V)
    L1 = Lifter(w, pa1, 'ad2antrr')
    vn = w.s([], 'simpr', '( %s -> %s e. NN )' % (pa1, V))
    vm = w.s([vn, w.inst('nnm1nn0')], 'syl', '( %s -> ( %s - 1 ) e. NN0 )' % (pa1, V))
    P2W = '( 2 ^ ( %s - 1 ) )' % V
    p2w = w.s([closed(w, pa1, '2nn', '2 e. NN'), vm, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (pa1, P2W))
    e3 = w.s([closed(w, pa1, '2cn', '2 e. CC'), vn, w.inst('expm1t')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (pa1, P2V, P2W))
    clB = Closure(w, pa1, {'F': ('NN0', L1(f0, 'F e. NN0')), P2V: ('NN0', w.s([L1(p2v, '%s e. NN' % P2V)], 'nnnn0d', '( %s -> %s e. NN0 )' % (pa1, P2V))),
                           P2W: ('NN0', w.s([p2w], 'nnnn0d', '( %s -> %s e. NN0 )' % (pa1, P2W)))})
    w1 = w.s([p2w, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pa1, P2W))
    fvA = w.s([fv], 'adantr', '( %s -> F = %s )' % (pa1, P2V))
    lo2 = linarith(w, pa1, [fvA, e3, w1], '%s <_ ( F - 1 )' % P2W, closure=clB)
    hi2 = linarith(w, pa1, [fvA], '( F - 1 ) < %s' % P2V, closure=clB)
    ge1 = linarith(w, pa1, [w1, lo2], '1 <_ ( F - 1 )', closure=clB)
    fmN = w.s([L1(fm, '( F - 1 ) e. NN0'), ge1], 'jca', '( %s -> ( ( F - 1 ) e. NN0 /\\ 1 <_ ( F - 1 ) ) )' % pa1)
    fmN = w.s([fmN, w.s([], 'elnnnn0c', '( ( F - 1 ) e. NN <-> ( ( F - 1 ) e. NN0 /\\ 1 <_ ( F - 1 ) ) )')], 'sylibr', '( %s -> ( F - 1 ) e. NN )' % pa1)
    bc = w.s([w.s([fmN, vn], 'jca', '( %s -> ( ( F - 1 ) e. NN /\\ %s e. NN ) )' % (pa1, V)), w.s([lo2, hi2], 'jca', '( %s -> ( %s <_ ( F - 1 ) /\\ ( F - 1 ) < %s ) )' % (pa1, P2W, P2V))],
             'jca', '( %s -> ( ( ( F - 1 ) e. NN /\\ %s e. NN ) /\\ ( %s <_ ( F - 1 ) /\\ ( F - 1 ) < %s ) ) )' % (pa1, V, P2W, P2V))
    blA1 = w.s([bc, w.inst('blchar')], 'syl', '( %s -> ( bl ` ( F - 1 ) ) = %s )' % (pa1, V))
    en = w.s([LA(vcl, '%s e. NN0' % V), w.s([], 'elnn0', '( %s e. NN0 <-> ( %s e. NN \\/ %s = 0 ) )' % (V, V, V))], 'sylib', '( %s -> ( %s e. NN \\/ %s = 0 ) )' % (pa, V, V))
    blA = w.s([blA1, blA0, en], 'mpjaodan', '( %s -> ( bl ` ( F - 1 ) ) = %s )' % (pa, V))
    caseA = w.s([w.s([LA(lem, '( # ` %s ) = ( bl ` ( F - 1 ) )' % EM), blA], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (pa, EM, V)), ifA], 'eqtr4d',
                '( %s -> ( # ` %s ) = %s )' % (pa, EM, NEWIF))
    # case B
    pb_ = '( %s /\\ -. %s )' % (ph, COND)
    LB = Lifter(w, pb_)
    cb = w.s([], 'simpr', '( %s -> -. %s )' % (pb_, COND))
    ifB = w.s([cb], 'iffalsed', '( %s -> %s = ( %s + 1 ) )' % (pb_, NEWIF, V))
    pq = '( %s /\\ %s = F )' % (pb_, P2V)
    eqq = w.s([w.s([w.s([], 'simpr', '( %s -> %s = F )' % (pq, P2V))], 'oveq1d', '( %s -> ( %s x. 2 ) = ( F x. 2 ) )' % (pq, P2V)),
               w.s([w.s([w.s([f0], 'nn0cnd', '( %s -> F e. CC )' % ph)], 'ad2antrr', '( %s -> F e. CC )' % pq), closed(w, pq, '2cn', '2 e. CC')], 'mulcomd', '( %s -> ( F x. 2 ) = ( 2 x. F ) )' % pq)],
              'eqtrd', '( %s -> ( %s x. 2 ) = ( 2 x. F ) )' % (pq, P2V))
    cq = w.s([w.s([w.s([e2], 'ad2antrr', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( %s x. 2 ) )' % (pq, V, P2V)), eqq], 'eqtrd', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( 2 x. F ) )' % (pq, V))], 'eqcomd',
             '( %s -> %s )' % (pq, COND))
    nq = w.s([w.s([cq], 'ex', '( %s -> ( %s = F -> %s ) )' % (pb_, P2V, COND)), cb], 'mtod', '( %s -> -. %s = F )' % (pb_, P2V))
    clC = Closure(w, pb_, {'F': ('NN0', LB(f0, 'F e. NN0')), P2V: ('NN0', w.s([LB(p2v, '%s e. NN' % P2V)], 'nnnn0d', '( %s -> %s e. NN0 )' % (pb_, P2V))),
                           V: ('NN0', LB(vcl, '%s e. NN0' % V))})
    lne = w.s([w.s([clC.mem(P2V, 'RR'), clC.mem('F', 'RR')], 'ltlend', '( %s -> ( %s < F <-> ( %s <_ F /\\ F =/= %s ) ) )' % (pb_, P2V, P2V, P2V)),
               w.s([LB(lo, '%s <_ F' % P2V), w.s([w.s([nq], 'neqned', '( %s -> %s =/= F )' % (pb_, P2V))], 'necomd', '( %s -> F =/= %s )' % (pb_, P2V))], 'jca',
                   '( %s -> ( %s <_ F /\\ F =/= %s ) )' % (pb_, P2V, P2V))], 'mpbird', '( %s -> %s < F )' % (pb_, P2V))
    zl = w.s([clC.mem(P2V, 'ZZ'), clC.mem('F', 'ZZ'), w.inst('zltlem1')], 'syl2anc', '( %s -> ( %s < F <-> %s <_ ( F - 1 ) ) )' % (pb_, P2V, P2V))
    lo3 = w.s([zl, lne], 'mpbid', '( %s -> %s <_ ( F - 1 ) )' % (pb_, P2V))
    V1 = '( %s + 1 )' % V
    p2v1 = w.s([closed(w, pb_, '2nn', '2 e. NN'), w.s([LB(vcl, '%s e. NN0' % V), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pb_, V1)), w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (pb_, V1))
    clC.leaf('( 2 ^ %s )' % V1, 'NN0', w.s([p2v1], 'nnnn0d', '( %s -> ( 2 ^ %s ) e. NN0 )' % (pb_, V1)))
    hi3 = linarith(w, pb_, [LB(hi, 'F < ( 2 ^ %s )' % V1)], '( F - 1 ) < ( 2 ^ %s )' % V1, closure=clC)
    ge1b = linarith(w, pb_, [w.s([LB(p2v, '%s e. NN' % P2V), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pb_, P2V)), lo3], '1 <_ ( F - 1 )', closure=clC)
    fmNb = w.s([w.s([LB(fm, '( F - 1 ) e. NN0'), ge1b], 'jca', '( %s -> ( ( F - 1 ) e. NN0 /\\ 1 <_ ( F - 1 ) ) )' % pb_),
                w.s([], 'elnnnn0c', '( ( F - 1 ) e. NN <-> ( ( F - 1 ) e. NN0 /\\ 1 <_ ( F - 1 ) ) )')], 'sylibr', '( %s -> ( F - 1 ) e. NN )' % pb_)
    v1n = w.s([LB(vcl, '%s e. NN0' % V), w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (pb_, V1))
    pnB = w.s([LB(pn, '( %s - 1 ) = %s' % (V1, V))], 'oveq2d', '( %s -> ( 2 ^ ( %s - 1 ) ) = %s )' % (pb_, V1, P2V))
    lo4 = w.s([pnB, lo3], 'eqbrtrd', '( %s -> ( 2 ^ ( %s - 1 ) ) <_ ( F - 1 ) )' % (pb_, V1))
    bcB = w.s([w.s([fmNb, v1n], 'jca', '( %s -> ( ( F - 1 ) e. NN /\\ %s e. NN ) )' % (pb_, V1)), w.s([lo4, hi3], 'jca', '( %s -> ( ( 2 ^ ( %s - 1 ) ) <_ ( F - 1 ) /\\ ( F - 1 ) < ( 2 ^ %s ) ) )' % (pb_, V1, V1))],
              'jca', '( %s -> ( ( ( F - 1 ) e. NN /\\ %s e. NN ) /\\ ( ( 2 ^ ( %s - 1 ) ) <_ ( F - 1 ) /\\ ( F - 1 ) < ( 2 ^ %s ) ) ) )' % (pb_, V1, V1, V1))
    blB = w.s([bcB, w.inst('blchar')], 'syl', '( %s -> ( bl ` ( F - 1 ) ) = %s )' % (pb_, V1))
    caseB = w.s([w.s([LB(lem, '( # ` %s ) = ( bl ` ( F - 1 ) )' % EM), blB], 'eqtrd', '( %s -> ( # ` %s ) = %s )' % (pb_, EM, V1)), ifB], 'eqtr4d',
                '( %s -> ( # ` %s ) = %s )' % (pb_, EM, NEWIF))
    lemif = w.s([caseA, caseB], 'pm2.61dan', '( %s -> ( # ` %s ) = %s )' % (ph, EM, NEWIF))
    leq = w.s([lpb, lemif], 'eqtr4d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, PB, EM))
    bu = w.s([pb, em, w.inst('bwuniq')], 'syl2anc', '( %s -> ( %s = %s <-> ( ( # ` %s ) = ( # ` %s ) /\\ ( toNat ` %s ) = ( toNat ` %s ) ) ) )' % (ph, PB, EM, PB, EM, PB, EM))
    w.qed([bu, w.s([leq, teq], 'jca', '( %s -> ( ( # ` %s ) = ( # ` %s ) /\\ ( toNat ` %s ) = ( toNat ` %s ) ) )' % (ph, PB, EM, PB, EM))], 'mpbird', S_('tmcpredenc'))
    return w.run()


def tmcprdb():
    lab = 'tmcprdb'
    ph = cj(TREE_PRDB)
    w = W(lab, '` predNum_le_B ` at the machine: ` predNum x s ` on the encoding of ` 1 <_ F < 2 ^ N ` leaves the '
               'encoding of ` F - 1 ` , keeps ` flag ` , ` cmp ` , ` carry ` , in ` ( TMB ` N ) ` steps (~ tmcprdn , '
               '~ tmcpredenc ).')
    c = Ctx(w, ph, TREE_PRDB)
    phm, ex = base(w, ph, c)
    e = enc_facts(w, ph, 'F', c['F e. NN'], c['N e. NN0'], c['F < ( 2 ^ N )'], fpos=True)
    dki = dk_inc(w, ph, e, c[DK_F])
    ex[WRD(e['EF'], '2o')] = e['ef']
    ex[formula(w, dki)[len('( %s -> ' % ph):-2]] = dki
    t, cc = inst(w, ph, 'tmcprdn', {'L': e['EF']}, Builder(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    fm = w.s([c['F e. NN'], w.inst('nnm1nn0')], 'syl', '( %s -> ( F - 1 ) e. NN0 )' % ph)
    pe = w.s([c['F e. NN'], w.inst('tmcpredenc')], 'syl', '( %s -> ( predBits ` %s ) = ( encodeNat ` ( F - 1 ) ) )' % (ph, e['EF']))
    g1 = w.s([fm, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` ( F - 1 ) ) = ( inclBool o. ( encodeNat ` ( F - 1 ) ) ) )' % ph)
    v = w.s([g1, w.s([pe], 'coeq2d', '( %s -> ( inclBool o. ( predBits ` %s ) ) = ( inclBool o. ( encodeNat ` ( F - 1 ) ) ) )' % (ph, e['EF']))], 'eqtr4d',
            '( %s -> ( encNatGam ` ( F - 1 ) ) = ( inclBool o. ( predBits ` %s ) ) )' % (ph, e['EF']))
    vr = w.s([v], 'eqcomd', '( %s -> ( inclBool o. ( predBits ` %s ) ) = ( encNatGam ` ( F - 1 ) ) )' % (ph, e['EF']))
    r, new = w.rewrite(D1, {'( inclBool o. ( predBits ` %s ) )' % e['EF']: ('( encNatGam ` ( F - 1 ) )', vr)}, ph)
    t2, C2, D2, n2 = hrrw(w, ph, t, C1, D1, n1, deq=r)
    le0 = w.s([e['ef'], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, e['EF']))
    finish(w, ph, phm, t2, C2, D2, n2, c['N e. NN0'], {'( # ` %s )' % e['EF']: le0}, [e['le']], '2')
    return w.run()


if __name__ == '__main__':
    for l in ['tmcdupb', 'tmcdropb', 'tmcizb', 'tmcincb', 'tmcpredenc', 'tmcprdb', 'tmccmpb']:
        if want(l) and l in globals(): globals()[l]()
