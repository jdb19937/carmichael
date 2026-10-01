"""Sortie A2, batch 1: the eventual calculus.
E. m e. NN0 A. n e. ( ZZ>= ` m ) ... : conjunction, thresholds, and the
divergence facts Step2W and Step3W read off the filter."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

L2 = '( ell2 ` n )'; L3 = '( ell3 ` n )'

# ------------------------------------------------------------------ evan2
w = WH('evan2', 'Two eventual statements hold eventually together (Lean: filter_upwards with two facts).')
h1 = w.h(EV('ps')); h2 = w.h(EV('ch'))
j = w.s([h1, h2], 'jca', '( ph -> ( %s /\\ %s ) )' % (EV('ps'), EV('ch')))
u = w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
b = w.s([u], 'rexanuz2', '( %s <-> ( %s /\\ %s ) )' % (EV('( ps /\\ ch )'), EV('ps'), EV('ch')))
w.qed([j, b], 'sylibr', '( ph -> %s )' % EV('( ps /\\ ch )'))
run(w)

# ------------------------------------------------------------------ evimd
w = WH('evimd', 'An eventual statement upgraded pointwise (Lean: filter_upwards ... with n h).')
h1 = w.h(EV('ps')); h2 = w.hc('( ( ph /\\ ps ) -> ch )')
e = w.s([h2], 'ex', '( ph -> ( ps -> ch ) )')
r = w.s([e], 'ralimdv', '( ph -> ( A. n e. ( ZZ>= ` m ) ps -> A. n e. ( ZZ>= ` m ) ch ) )')
x = w.s([r], 'reximdv', '( ph -> ( %s -> %s ) )' % (EV('ps'), EV('ch')))
w.qed([h1, x], 'mpd', '( ph -> %s )' % EV('ch'))
run(w)

# ------------------------------------------------------------------ evge3
w = W('evge3', 'Eventually n is at least 3 (Lean: eventually_ge_atTop 3).')
i = w.s([], 'id', '( n e. ( ZZ>= ` 3 ) -> n e. ( ZZ>= ` 3 ) )')
r = w.s([i], 'rgen', 'A. n e. ( ZZ>= ` 3 ) n e. ( ZZ>= ` 3 )')
n0 = w.s([], '3nn0', '3 e. NN0')
l1 = w.s([], 'id', '( m = 3 -> m = 3 )')
c, res = w.wcongr('A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` 3 )', {'m': '3'}, 'm = 3', {'m': l1})
j = w.s([n0, r], 'pm3.2i', '( 3 e. NN0 /\\ A. n e. ( ZZ>= ` 3 ) n e. ( ZZ>= ` 3 ) )')
ii = w.s([c], 'rspcev', '( ( 3 e. NN0 /\\ A. n e. ( ZZ>= ` 3 ) n e. ( ZZ>= ` 3 ) ) -> %s )' % EV('n e. ( ZZ>= ` 3 )'))
w.qed([j, ii], 'ax-mp', EV('n e. ( ZZ>= ` 3 )'))
run(w)

# ------------------------------------------------------------------ lognge
w = W('lognge', 'log tends to infinity: every real bound is eventually exceeded (Lean: Real.tendsto_log_atTop composed with tendsto_natCast_atTop_atTop).')
EB = '( exp ` B )'; EB1 = '( %s + 1 )' % EB; M = '( Nceil ` %s )' % EB1
A0 = 'B e. RR'; A = '( B e. RR /\\ n e. ( ZZ>= ` %s ) )' % M
b = w.s([], 'simpl', '( %s -> B e. RR )' % A)
nu = w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` %s ) )' % (A, M))
eb = w.s([b], 'reefcld', '( %s -> %s e. RR )' % (A, EB))
eb0 = w.s([b, w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, EB))
ebge = w.s([eb0], 'ltled', '( %s -> 0 <_ %s )' % (A, EB))
ebrp = w.s([eb, eb0], 'elrpd', '( %s -> %s e. RR+ )' % (A, EB))
one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
eb1 = w.s([eb, one], 'readdcld', '( %s -> %s e. RR )' % (A, EB1))
mle = w.s([eb1, w.inst('nceilge')], 'syl', '( %s -> %s <_ %s )' % (A, EB1, M))
mn0 = w.s([eb1, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (A, M))
mr = w.s([mn0], 'nn0red', '( %s -> %s e. RR )' % (A, M))
nz = w.s([nu, w.inst('eluzelz')], 'syl', '( %s -> n e. ZZ )' % A)
nr = w.s([nz], 'zred', '( %s -> n e. RR )' % A)
mn = w.s([nu, w.inst('eluzle')], 'syl', '( %s -> %s <_ n )' % (A, M))
ch = w.s([eb1, mr, nr, mle, mn], 'letrd', '( %s -> %s <_ n )' % (A, EB1))
le1 = linarith(w, A, [ebge, ch], '1 <_ n', leaves={EB: eb, 'n': nr})
jn = w.s([nz, le1], 'jca', '( %s -> ( n e. ZZ /\\ 1 <_ n ) )' % A)
nn = w.s([jn, w.inst('elnnz1')], 'sylibr', '( %s -> n e. NN )' % A)
nrp = w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % A)
ebn = linarith(w, A, [ch], '%s <_ n' % EB, leaves={EB: eb, 'n': nr})
bi = w.s([ebrp, nrp, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ n <-> ( log ` %s ) <_ ( log ` n ) ) )' % (A, EB, EB))
ll = w.s([ebn, bi], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` n ) )' % (A, EB))
re = w.s([b, w.inst('relogef')], 'syl', '( %s -> ( log ` %s ) = B )' % (A, EB))
re2 = w.s([re], 'eqcomd', '( %s -> B = ( log ` %s ) )' % (A, EB))
res = w.s([re2, ll], 'eqbrtrd', '( %s -> B <_ ( log ` n ) )' % A)
ral = w.s([res], 'ralrimiva', '( %s -> A. n e. ( ZZ>= ` %s ) B <_ ( log ` n ) )' % (A0, M))
eb_ = w.s([], 'id', '( %s -> B e. RR )' % A0)
eb0_ = w.s([eb_], 'reefcld', '( %s -> %s e. RR )' % (A0, EB))
one_ = w.s([], '1red', '( %s -> 1 e. RR )' % A0)
eb1_ = w.s([eb0_, one_], 'readdcld', '( %s -> %s e. RR )' % (A0, EB1))
m0 = w.s([eb1_, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (A0, M))
l1 = w.s([], 'id', '( m = %s -> m = %s )' % (M, M))
c, _r = w.wcongr('A. n e. ( ZZ>= ` m ) B <_ ( log ` n )', {'m': M}, 'm = %s' % M, {'m': l1})
j2 = w.s([m0, ral], 'jca', '( %s -> ( %s e. NN0 /\\ A. n e. ( ZZ>= ` %s ) B <_ ( log ` n ) ) )' % (A0, M, M))
ii = w.s([c], 'rspcev', '( ( %s e. NN0 /\\ A. n e. ( ZZ>= ` %s ) B <_ ( log ` n ) ) -> %s )' % (M, M, EV('B <_ ( log ` n )')))
w.qed([j2, ii], 'syl', '( %s -> %s )' % (A0, EV('B <_ ( log ` n )')))
run(w)

# -------------------------------------------- pullbacks of logsqlerpow
LSP = lambda U: 'A. u e. ( %s [,) +oo ) ( ( log ` u ) ^ 2 ) <_ ( u ^c R )' % U


def pullback(lem, thm, F, G, gelab, realstep, idlab, desc1, desc2):
    """the eventual bound ( G ^ 2 ) <_ ( F ^c R ) from logsqlerpow along F"""
    PH = '( R e. RR+ /\\ U e. RR /\\ %s )' % LSP('U')
    GOAL = '( %s ^ 2 ) <_ ( %s ^c R )' % (G, F)
    GOALB = GOAL
    w = W(lem, desc1)
    src1c = w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))
    src1 = w.s([src1c], 'a1i', '( %s -> %s )' % (PH, EV('n e. ( ZZ>= ` 3 )')))
    ur = w.s([], 'simp2', '( %s -> U e. RR )' % PH)
    src2 = w.s([ur, w.inst(gelab)], 'syl', '( %s -> %s )' % (PH, EV('U <_ %s' % F)))
    both = w.s([src1, src2], 'evan2', '( %s -> %s )' % (PH, EV('( n e. ( ZZ>= ` 3 ) /\\ U <_ %s )' % F)))
    AA = '( %s /\\ ( n e. ( ZZ>= ` 3 ) /\\ U <_ %s ) )' % (PH, F)
    rr = w.s([], 'simpl1', '( %s -> R e. RR+ )' % AA)
    ur2 = w.s([], 'simpl2', '( %s -> U e. RR )' % AA)
    rall = w.s([], 'simpl3', '( %s -> %s )' % (AA, LSP('U')))
    n3 = w.s([], 'simprl', '( %s -> n e. ( ZZ>= ` 3 ) )' % AA)
    ule = w.s([], 'simprr', '( %s -> U <_ %s )' % (AA, F))
    n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % AA)
    nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> n e. NN )' % AA)
    n0 = w.s([nn], 'nnnn0d', '( %s -> n e. NN0 )' % AA)
    nrp = w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % AA)
    fr = realstep(w, AA, n2, n0, nrp)
    jf = w.s([fr, ule], 'jca', '( %s -> ( %s e. RR /\\ U <_ %s ) )' % (AA, F, F))
    ic = w.s([ur2, w.inst('elicopnf')], 'syl', '( %s -> ( %s e. ( U [,) +oo ) <-> ( %s e. RR /\\ U <_ %s ) ) )' % (AA, F, F, F))
    mem = w.s([jf, ic], 'mpbird', '( %s -> %s e. ( U [,) +oo ) )' % (AA, F))
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (F, F))
    sb, _r = w.wcongr('( ( log ` u ) ^ 2 ) <_ ( u ^c R )', {'u': F}, 'u = %s' % F, {'u': idu})
    ins = w.s([sb, rall, mem], 'rspcdva', '( %s -> ( ( log ` %s ) ^ 2 ) <_ ( %s ^c R ) )' % (AA, F, F))
    ident = idlab(w, AA, n0)          # ( AA -> G = ( log ` F ) )
    sq = w.s([ident], 'oveq1d', '( %s -> ( %s ^ 2 ) = ( ( log ` %s ) ^ 2 ) )' % (AA, G, F))
    pt = w.s([sq, ins], 'eqbrtrd', '( %s -> %s )' % (AA, GOALB))
    w.qed([both, pt], 'evimd', '( %s -> %s )' % (PH, EV(GOAL)))
    run(w)

    w = W(thm, desc2)
    A0 = 'R e. RR+'
    lem3 = w.s([], lem, '( ( R e. RR+ /\\ l e. RR /\\ %s ) -> %s )' % (LSP('l'), EV(GOAL)))
    ex = w.s([lem3], '3expia', '( ( R e. RR+ /\\ l e. RR ) -> ( %s -> %s ) )' % (LSP('l'), EV(GOAL)))
    rl = w.s([ex], 'rexlimdva', '( %s -> ( E. l e. RR %s -> %s ) )' % (A0, LSP('l'), EV(GOAL)))
    idl = w.s([], 'id', '( m = l -> m = l )')
    cb, _r = w.wcongr(LSP('m'), {'m': 'l'}, 'm = l', {'m': idl})
    bi = w.s([cb], 'cbvrexvw', '( E. m e. RR %s <-> E. l e. RR %s )' % (LSP('m'), LSP('l')))
    src = w.s([], 'logsqlerpow', '( R e. RR+ -> E. m e. RR %s )' % LSP('m'))
    src2 = w.s([src, w.s([bi], 'a1i', '( %s -> ( E. m e. RR %s <-> E. l e. RR %s ) )' % (A0, LSP('m'), LSP('l')))], 'mpbid',
               '( %s -> E. l e. RR %s )' % (A0, LSP('l')))
    w.qed([src2, rl], 'mpd', '( %s -> %s )' % (A0, EV(GOAL)))
    run(w)


def real_ell2(w, AA, n2, n0, nrp):
    return w.s([n2, w.inst('ell2cl')], 'syl', '( %s -> ( ell2 ` n ) e. RR )' % AA)


def id_ell3(w, AA, n0):
    return w.s([n0, w.inst('ell3val')], 'syl', '( %s -> ( ell3 ` n ) = ( log ` ( ell2 ` n ) ) )' % AA)


def real_log(w, AA, n2, n0, nrp):
    return w.s([nrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` n ) e. RR )' % AA)


def id_ell2(w, AA, n0):
    return w.s([n0, w.inst('ell2val')], 'syl', '( %s -> ( ell2 ` n ) = ( log ` ( log ` n ) ) )' % AA)


pullback('ell3sqlem', 'ell3sqle', L2, L3, 'ell2ge', real_ell2, id_ell3,
         'Lemma for ell3sqle: the threshold of logsqlerpow pulled back along ell2.',
         'Eventually ( ell3 n ) ^ 2 <_ ( ell2 n ) ^c R (Lean: isLittleO_log_rpow_atTop composed with tendsto_ell2, Step2W.lean hlog_rpow).')
pullback('ell2sqlem', 'ell2sqle', '( log ` n )', L2, 'lognge', real_log, id_ell2,
         'Lemma for ell2sqle: the threshold of logsqlerpow pulled back along log.',
         'Eventually ( ell2 n ) ^ 2 <_ ( log n ) ^c R (Lean: isLittleO_log_rpow_atTop composed with Real.tendsto_log_atTop).')

# ----------------------------------------------------- ell3lecxp, quadexp
w = W('ell3lecxp', 'Eventually a constant multiple of ell3 is below any positive power of ell2 (Lean: Step2W.lean hlog_rpow, 4 C1 log u <_ u ^ ( 1 / 99 ) pulled back along ell2).')
PH = '( C e. RR /\\ 0 <_ C /\\ R e. RR+ )'
GOAL = '( C x. %s ) <_ ( %s ^c R )' % (L3, L2)
cr = w.s([], 'simp1', '( %s -> C e. RR )' % PH)
c0 = w.s([], 'simp2', '( %s -> 0 <_ C )' % PH)
rp = w.s([], 'simp3', '( %s -> R e. RR+ )' % PH)
s1 = w.s([rp, w.inst('ell3sqle')], 'syl', '( %s -> %s )' % (PH, EV('( %s ^ 2 ) <_ ( %s ^c R )' % (L3, L2))))
s2 = w.s([cr, w.inst('ell3ge')], 'syl', '( %s -> %s )' % (PH, EV('C <_ %s' % L3)))
s3 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( %s -> %s )' % (PH, EV('n e. ( ZZ>= ` 3 )')))
both, tx = evand(w, PH, [s1, s2, s3],
                 ['( %s ^ 2 ) <_ ( %s ^c R )' % (L3, L2), 'C <_ %s' % L3, 'n e. ( ZZ>= ` 3 )'])
AA = '( %s /\\ %s )' % (PH, tx)
acr = w.s([], 'simpl1', '( %s -> C e. RR )' % AA)
ac0 = w.s([], 'simpl2', '( %s -> 0 <_ C )' % AA)
sq = w.s([], 'simprll', '( %s -> ( %s ^ 2 ) <_ ( %s ^c R ) )' % (AA, L3, L2))
cle = w.s([], 'simprlr', '( %s -> C <_ %s )' % (AA, L3))
n3 = w.s([], 'simprr', '( %s -> n e. ( ZZ>= ` 3 ) )' % AA)
l3r = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (AA, L3))
l30 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % AA), acr, l3r, ac0, cle], 'letrd', '( %s -> 0 <_ %s )' % (AA, L3))
mul = w.s([acr, l3r, l3r, l30, cle], 'lemul1ad', '( %s -> ( C x. %s ) <_ ( %s x. %s ) )' % (AA, L3, L3, L3))
l3c = w.s([l3r], 'recnd', '( %s -> %s e. CC )' % (AA, L3))
sv = w.s([l3c], 'sqvald', '( %s -> ( %s ^ 2 ) = ( %s x. %s ) )' % (AA, L3, L3, L3))
mul2 = w.s([sv, mul], 'breqtrrd', '( %s -> ( C x. %s ) <_ ( %s ^ 2 ) )' % (AA, L3, L3))
cxr = w.s([w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % AA), w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (AA, L2))
l2ge0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % AA), l3r, cxr, l30, w.s([n3, w.inst('ell3lt')], 'syl', '( %s -> %s < %s )' % (AA, L3, L2))], 'lelttrd', '( %s -> 0 < %s )' % (AA, L2))
l2g = w.s([l2ge0], 'ltled', '( %s -> 0 <_ %s )' % (AA, L2))
rr = w.s([], 'simpl3', '( %s -> R e. RR+ )' % AA)
rrr = w.s([rr], 'rpred', '( %s -> R e. RR )' % AA)
cxpr = w.s([cxr, l2g, rrr], 'recxpcld', '( %s -> ( %s ^c R ) e. RR )' % (AA, L2))
sqr = w.s([l3r], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (AA, L3))
cmr = w.s([acr, l3r], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (AA, L3))
pt = w.s([cmr, sqr, cxpr, mul2, sq], 'letrd', '( %s -> %s )' % (AA, GOAL))
w.qed([both, pt], 'evimd', '( %s -> %s )' % (PH, EV(GOAL)))
run(w)

w = W('quadexp', 'Eventually a constant multiple of ( ell2 n ) ^ 2 is below ( log n ) ^c R, i.e. below exp ( R ell2 n ) (Lean: eventually_quad_le_exp composed with tendsto_ell2, Step3W.lean).')
PH = '( K e. RR /\\ 0 <_ K /\\ R e. RR+ )'
SQ = '( %s ^ 2 )' % L2
LN = '( log ` n )'
GOAL = '( K x. %s ) <_ ( %s ^c R )' % (SQ, LN)
kr = w.s([], 'simp1', '( %s -> K e. RR )' % PH)
k0 = w.s([], 'simp2', '( %s -> 0 <_ K )' % PH)
rp = w.s([], 'simp3', '( %s -> R e. RR+ )' % PH)
rh = w.s([rp], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % PH)
s1 = w.s([rh, w.inst('ell2sqle')], 'syl', '( %s -> %s )' % (PH, EV('%s <_ ( %s ^c ( R / 2 ) )' % (SQ, LN))))
one = w.s([], '1red', '( %s -> 1 e. RR )' % PH)
kp1 = w.s([kr, one], 'readdcld', '( %s -> ( K + 1 ) e. RR )' % PH)
s2 = w.s([kp1, w.inst('ell2ge')], 'syl', '( %s -> %s )' % (PH, EV('( K + 1 ) <_ %s' % L2)))
s3 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( %s -> %s )' % (PH, EV('n e. ( ZZ>= ` 3 )')))
both, tx = evand(w, PH, [s1, s2, s3],
                 ['%s <_ ( %s ^c ( R / 2 ) )' % (SQ, LN), '( K + 1 ) <_ %s' % L2, 'n e. ( ZZ>= ` 3 )'])
AA = '( %s /\\ %s )' % (PH, tx)
akr = w.s([], 'simpl1', '( %s -> K e. RR )' % AA)
ak0 = w.s([], 'simpl2', '( %s -> 0 <_ K )' % AA)
arp = w.s([], 'simpl3', '( %s -> R e. RR+ )' % AA)
sq1 = w.s([], 'simprll', '( %s -> %s <_ ( %s ^c ( R / 2 ) ) )' % (AA, SQ, LN))
kle = w.s([], 'simprlr', '( %s -> ( K + 1 ) <_ %s )' % (AA, L2))
n3 = w.s([], 'simprr', '( %s -> n e. ( ZZ>= ` 3 ) )' % AA)
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % AA)
nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> n e. NN )' % AA)
nr = w.s([nn], 'nnred', '( %s -> n e. RR )' % AA)
nge1 = w.s([nn], 'nnge1d', '( %s -> 1 <_ n )' % AA)
lnr = w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % AA)
lncl = w.s([lnr, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (AA, LN))
ln0 = w.s([nr, nge1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (AA, LN))
l2r = w.s([n2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (AA, L2))
l21 = linarith(w, AA, [kle, ak0], '1 <_ %s' % L2, leaves={'K': akr, L2: l2r})
l20 = linarith(w, AA, [kle, ak0], '0 <_ %s' % L2, leaves={'K': akr, L2: l2r})
kl2 = linarith(w, AA, [kle], 'K <_ %s' % L2, leaves={'K': akr, L2: l2r})
sqr = w.s([l2r], 'resqcld', '( %s -> %s e. RR )' % (AA, SQ))
sq0 = w.s([l2r], 'sqge0d', '( %s -> 0 <_ %s )' % (AA, SQ))
mg = w.s([l2r, l2r, l20, l21], 'lemulge11d', '( %s -> %s <_ ( %s x. %s ) )' % (AA, L2, L2, L2))
l2c = w.s([l2r], 'recnd', '( %s -> %s e. CC )' % (AA, L2))
sv = w.s([l2c], 'sqvald', '( %s -> %s = ( %s x. %s ) )' % (AA, SQ, L2, L2))
mg2 = w.s([sv, mg], 'breqtrrd', '( %s -> %s <_ %s )' % (AA, L2, SQ))
kle2 = w.s([akr, l2r, sqr, kl2, mg2], 'letrd', '( %s -> K <_ %s )' % (AA, SQ))
mul = w.s([akr, sqr, sqr, sq0, kle2], 'lemul1ad', '( %s -> ( K x. %s ) <_ ( %s x. %s ) )' % (AA, SQ, SQ, SQ))
sqc = w.s([sqr], 'recnd', '( %s -> %s e. CC )' % (AA, SQ))
sv2 = w.s([sqc], 'sqvald', '( %s -> ( %s ^ 2 ) = ( %s x. %s ) )' % (AA, SQ, SQ, SQ))
mul2 = w.s([sv2, mul], 'breqtrrd', '( %s -> ( K x. %s ) <_ ( %s ^ 2 ) )' % (AA, SQ, SQ))
rhh = w.s([arp], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % AA)
rhr = w.s([rhh], 'rpred', '( %s -> ( R / 2 ) e. RR )' % AA)
cxr = w.s([lncl, ln0, rhr], 'recxpcld', '( %s -> ( %s ^c ( R / 2 ) ) e. RR )' % (AA, LN))
cx0 = w.s([lncl, ln0, rhr], 'cxpge0d', '( %s -> 0 <_ ( %s ^c ( R / 2 ) ) )' % (AA, LN))
bi = w.s([sqr, cxr, sq0, cx0], 'le2sqd', '( %s -> ( %s <_ ( %s ^c ( R / 2 ) ) <-> ( %s ^ 2 ) <_ ( ( %s ^c ( R / 2 ) ) ^ 2 ) ) )' % (AA, SQ, LN, SQ, LN))
le2 = w.s([sq1, bi], 'mpbid', '( %s -> ( %s ^ 2 ) <_ ( ( %s ^c ( R / 2 ) ) ^ 2 ) )' % (AA, SQ, LN))
lnc = w.s([lncl], 'recnd', '( %s -> %s e. CC )' % (AA, LN))
rc = w.s([arp], 'rpcnd', '( %s -> R e. CC )' % AA)
t2 = w.s([], '2cnd', '( %s -> 2 e. CC )' % AA)
t2n = w.s([], '2ne0', '2 =/= 0')
t2nd = w.s([t2n], 'a1i', '( %s -> 2 =/= 0 )' % AA)
dc = w.s([rc, t2, t2nd], 'divcan1d', '( %s -> ( ( R / 2 ) x. 2 ) = R )' % AA)
n0c = w.s([], '2nn0', '2 e. NN0')
n0cd = w.s([n0c], 'a1i', '( %s -> 2 e. NN0 )' % AA)
rhc = w.s([rhr], 'recnd', '( %s -> ( R / 2 ) e. CC )' % AA)
cm = w.s([lnc, rhc, n0cd, w.inst('cxpmul2')], 'syl3anc', '( %s -> ( %s ^c ( ( R / 2 ) x. 2 ) ) = ( ( %s ^c ( R / 2 ) ) ^ 2 ) )' % (AA, LN, LN))
oe = w.s([dc], 'oveq2d', '( %s -> ( %s ^c ( ( R / 2 ) x. 2 ) ) = ( %s ^c R ) )' % (AA, LN, LN))
cid = w.s([w.s([cm], 'eqcomd', '( %s -> ( ( %s ^c ( R / 2 ) ) ^ 2 ) = ( %s ^c ( ( R / 2 ) x. 2 ) ) )' % (AA, LN, LN)), oe], 'eqtrd', '( %s -> ( ( %s ^c ( R / 2 ) ) ^ 2 ) = ( %s ^c R ) )' % (AA, LN, LN))
le3 = w.s([le2, cid], 'breqtrd', '( %s -> ( %s ^ 2 ) <_ ( %s ^c R ) )' % (AA, SQ, LN))
kmr = w.s([akr, sqr], 'remulcld', '( %s -> ( K x. %s ) e. RR )' % (AA, SQ))
ssr = w.s([sqr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (AA, SQ))
rrr = w.s([arp], 'rpred', '( %s -> R e. RR )' % AA)
cxr2 = w.s([lncl, ln0, rrr], 'recxpcld', '( %s -> ( %s ^c R ) e. RR )' % (AA, LN))
pt = w.s([kmr, ssr, cxr2, mul2, le3], 'letrd', '( %s -> %s )' % (AA, GOAL))
w.qed([both, pt], 'evimd', '( %s -> %s )' % (PH, EV(GOAL)))
run(w)
