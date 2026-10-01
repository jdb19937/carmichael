"""T11 helper (scan): the arithmetic of the scan loop at the machine (Lean ` scanIters ` , ` SCInv ` and the facts
` scanBody_runs ` reads), over the letter ` R ` of the iteration count (t11s_b_defs.py).

  tmscr0   the count: ` R e. NN0 ` , ` R <_ fuel ` , ` 0 = R <-> fuel = 0 ` , no success flag at 0, the charge ` VN ` at 0
           and at ` R ` , ` R = fuel ` on a failure, ` k + R - 1 = k' ` on a success
  tmscrn   an iteration ` i < R ` without success at ` k + i ` : no success flag at ` i + 1 ` , and ` i + 1 = R ` iff the
           fuel is spent
  tmscrs   an iteration with success at ` k + i ` : the scan succeeds, ` i + 1 = R ` , the returned pool is ` k + i ` 's
  tmscva   the charge of an iteration, ` k + i ` not coprime
  tmscvb   ... coprime, pool too small
  tmscvc   ... success

    MM_DB=sorties/t11.mm python3 tools/gen/t11s_c_arith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, lineq
from cl import Closure
from t10_e_doa import lift_from
from t6blib import _split_top, _outer
import t6blib
from t11s_b_defs import *

SEL = sys.argv[1:]
UO = os.environ.get('T11S_UO') == '1'
STMTS = {}
TREES = {}


def add(label, tree, concl_):
    STMTS[label] = '( %s -> %s )' % (cj(tree), concl_)
    TREES[label] = (tree, concl_)
    t6blib._STMT[label] = STMTS[label]


C0_T = ((('R e. NN0', 'R <_ H'), ('( 0 = R <-> H = 0 )', '-. %s' % SJ('0'))),
        (('%s = %s' % (VN('0'), SC2), '%s = 0' % VN('R')),
         ('( %s -> R = H )' % NONE, '( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (NONE, KF))))
add('tmscr0', AT, cj(C0_T))
TI = (AT, IFZ)
add('tmscrn', (TI, '-. %s' % SUC(GI('i'))), '( -. %s /\\ ( %s = R <-> %s = 0 ) )' % (SJ(I1), I1, HI(I1)))
add('tmscrs', (TI, SUC(GI('i'))), '( ( -. %s /\\ %s = R ) /\\ %s = %s )' % (NONE, I1, PFS, PA1(GI('i'))))
add('tmscva', (TI, '-. %s' % CPc(GI('i'))), '%s = ( ( %s + %s ) + 1 )' % (VN('i'), VN(I1), ACP(GI('i'))))
add('tmscvb', (TI, ('%s' % CPc(GI('i')), '-. %s' % OLE(GI('i')))),
    '%s = ( ( ( %s + %s ) + %s ) + 1 )' % (VN('i'), VN(I1), ACP(GI('i')), CPA(GI('i'))))
add('tmscvc', (TI, SUC(GI('i'))), '( %s = ( ( %s + %s ) + 1 ) /\\ %s = 0 )' % (VN('i'), ACP(GI('i')), CPA(GI('i')), VN(I1)))

SOME_ = lambda k, f: '( 1st ` %s ) =/= ( inr ` (/) )' % SCf(k, f)


def ifparts(text):
    """(c, a, b) of the text ` if ( c , a , b ) `"""
    toks = text.split()
    assert toks[0] == 'if' and toks[1] == '(' and toks[-1] == ')', text[:80]
    parts = _split_top(toks[2:-1], ',')
    assert len(parts) == 3, len(parts)
    return parts


def pairparts(text):
    toks = text.split()
    assert toks[0] == '<.' and toks[-1] == '>.', text[:80]
    parts = _split_top(toks[1:-1], ',')
    assert len(parts) == 2
    return parts


def vex(w, ph, x):
    s = w.s
    toks = x.split()
    if x == '0':
        return s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ph)
    d = 0
    for t in toks[1:-1]:
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        elif d == 0 and t == '`':
            return s([s([], 'fvex', '%s e. _V' % x)], 'a1i', '( %s -> %s e. _V )' % (ph, x))
    return s([s([], 'ovex', '%s e. _V' % x)], 'a1i', '( %s -> %s e. _V )' % (ph, x))


def snd(w, ph, pair):
    """( ph -> ( 2nd ` <. a , b >. ) = b )"""
    a, b = pairparts(pair)
    return w.s([vex(w, ph, a), vex(w, ph, b), w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (ph, pair, b))


def r0facts(w, ph, atst):
    """the parts of ~ tmscr0 under ph from atst : ( ph -> AT )"""
    st = w.s([atst, w.inst('tmscr0')], 'syl', '( %s -> %s )' % (ph, cj(C0_T)))
    return Ctx(w, ph, C0_T, root=st)


def ifacts(w, ph, c):
    """facts under an antecedent with AT and i e. ( 0 ..^ R )"""
    s = w.s
    r0 = r0facts(w, ph, c[cj(AT)])
    io = c[IFZ]
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ph)
    i1le = s([io, w.inst('elfzop1le2')], 'syl', '( %s -> %s <_ R )' % (ph, I1))
    gn, hn = c['G e. NN0'], c['H e. NN0']
    cl = Closure(w, ph, {'i': ('NN0', inn), 'G': ('NN0', gn), 'H': ('NN0', hn), 'R': ('NN0', r0['R e. NN0'])})
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, I1))
    i1h = linarith(w, ph, [i1le, r0['R <_ H']], '%s <_ H' % I1, closure=cl)
    hin = s([i1n, hn, i1h, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, HI(I1)))
    gin = s([gn, inn], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, GI('i')))
    nsi = s([s([s([cl.mem('i', 'RR'), ilt], 'ltned', '( %s -> i =/= R )' % ph)], 'neneqd', '( %s -> -. i = R )' % ph)], 'intnanrd',
            '( %s -> -. %s )' % (ph, SJ('i')))
    return dict(r0=r0, inn=inn, ilt=ilt, i1le=i1le, cl=cl, i1n=i1n, i1h=i1h, hin=hin, gin=gin, nsi=nsi, gn=gn, hn=hn)


def base4(w, ph, st4, last, lst):
    """( ph -> ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ last ) )"""
    s = w.s
    ww, fn, zn, on = st4
    a = s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph)
    b = s([a, zn], 'jca', '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % ph)
    c = s([b, on], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % ph)
    return s([c, lst], 'jca', '( %s -> ( ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ %s ) )' % (ph, last))


def h4(c):
    return c[cj(HYP4)]


def some_inst(w, ph, c, nn):
    """~ tmscsome under ph from nn : ( ph -> -. NONE ): the Ctx of its conclusion"""
    s = w.s
    sm = s([nn], 'neqned', '( %s -> %s )' % (ph, SOMEne))
    ante = '( %s /\\ ( ( G e. NN0 /\\ H e. NN0 ) /\\ %s ) )' % (cj(HYP4), SOMEne)
    a = s([h4(c), s([c['( G e. NN0 /\\ H e. NN0 )'], sm], 'jca', '( %s -> ( ( G e. NN0 /\\ H e. NN0 ) /\\ %s ) )' % (ph, SOMEne))], 'jca',
          '( %s -> %s )' % (ph, ante))
    CT = (('G <_ %s' % KF, '%s < ( G + H )' % KF), (SUC(KF), '%s = %s' % (PFS, PA1(KF))))
    st = s([a, w.inst('tmscsome')], 'syl', '( %s -> %s )' % (ph, cj(CT)))
    return Ctx(w, ph, CT, root=st), sm


def tmscr0():
    lab = 'tmscr0'
    ph = cj(AT)
    w = W(lab, 'The iteration count of the scan loop at the machine (Lean ` scanIters ` , ` scanIters_le_fuel ` ): ` R ` is '
               'the fuel on a failure and ` k\' - k + 1 ` on a success; it is at most the fuel, zero exactly with the fuel, the '
               'success flag is off at 0, and the charge ` VN ` is the scan cost at 0 and 0 at ` R ` (~ scan0 , ~ tmscsome ).')
    s = w.s
    c = Ctx(w, ph, AT)
    gn, hn, req = c['G e. NN0'], c['H e. NN0'], c[REQ]
    # ---- NONE
    pN = '( %s /\\ %s )' % (ph, NONE)
    LN = lambda st: lift_from(w, ph, pN, st)
    nN = s([], 'simpr', '( %s -> %s )' % (pN, NONE))
    rhN = s([LN(req), s([nN], 'iftrued', '( %s -> %s = H )' % (pN, RV))], 'eqtrd', '( %s -> R = H )' % pN)
    hNr = s([LN(hn)], 'nn0red', '( %s -> H e. RR )' % pN)
    rnN = s([rhN, LN(hn)], 'eqeltrd', '( %s -> R e. NN0 )' % pN)
    rlN = s([rhN, s([hNr], 'leidd', '( %s -> H <_ H )' % pN)], 'eqbrtrd', '( %s -> R <_ H )' % pN)
    biN = s([s([rhN], 'eqeq2d', '( %s -> ( 0 = R <-> 0 = H ) )' % pN), s([s([], 'eqcom', '( 0 = H <-> H = 0 )')], 'a1i',
                                                                         '( %s -> ( 0 = H <-> H = 0 ) )' % pN)], 'bitrd',
            '( %s -> ( 0 = R <-> H = 0 ) )' % pN)
    nnN = s([nN], 'notnotd', '( %s -> -. -. %s )' % (pN, NONE))
    sj0N = s([nnN], 'intnand', '( %s -> -. %s )' % (pN, SJ('0')))
    sjRN = s([nnN], 'intnand', '( %s -> -. %s )' % (pN, SJ('R')))
    vr1 = s([sjRN], 'iffalsed', '( %s -> %s = %s )' % (pN, VN('R'), Vf('R')))
    hr0 = s([s([rhN], 'oveq2d', '( %s -> ( H - R ) = ( H - H ) )' % pN), s([s([LN(hn)], 'nn0cnd', '( %s -> H e. CC )' % pN)], 'subidd',
                                                                          '( %s -> ( H - H ) = 0 )' % pN)], 'eqtrd', '( %s -> ( H - R ) = 0 )' % pN)
    gr = s([rhN], 'oveq2d', '( %s -> ( G + R ) = ( G + H ) )' % pN)
    rv, xv = w.rewrite(Vf('R'), {'( H - R )': ('0', hr0), '( G + R )': ('( G + H )', gr)}, pN)
    assert xv == '( 2nd ` %s )' % SCf('( G + H )', '0'), xv
    ghn = s([LN(gn), LN(hn)], 'nn0addcld', '( %s -> ( G + H ) e. NN0 )' % pN)
    b5 = base4(w, pN, [LN(c[x]) for x in ('W e. Word NN0', 'F e. NN0', 'Z e. NN0', 'O e. NN0')], '( G + H ) e. NN0', ghn)
    P0 = '<. ( inr ` (/) ) , 0 >.'
    z0 = s([b5, w.inst('scan0')], 'syl', '( %s -> %s = %s )' % (pN, SCf('( G + H )', '0'), P0))
    z2 = s([s([z0], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (pN, xv, P0)), snd(w, pN, P0)], 'eqtrd', '( %s -> %s = 0 )' % (pN, xv))
    vrN = s([s([vr1, rv], 'eqtrd', '( %s -> %s = %s )' % (pN, VN('R'), xv)), z2], 'eqtrd', '( %s -> %s = 0 )' % (pN, VN('R')))
    # ---- SOME
    pS = '( %s /\\ -. %s )' % (ph, NONE)
    LS = lambda st: lift_from(w, ph, pS, st)
    nS = s([], 'simpr', '( %s -> -. %s )' % (pS, NONE))
    cS = Ctx(w, pS, (AT, '-. %s' % NONE))
    sc, sm = some_inst(w, pS, cS, nS)
    rS = s([LS(req), s([nS], 'iffalsed', '( %s -> %s = ( ( %s - G ) + 1 ) )' % (pS, RV, KF))], 'eqtrd',
           '( %s -> R = ( ( %s - G ) + 1 ) )' % (pS, KF))
    b4 = base4(w, pS, [LS(c[x]) for x in ('W e. Word NN0', 'F e. NN0', 'Z e. NN0', 'O e. NN0')], '( G e. NN0 /\\ H e. NN0 )',
               s([LS(gn), LS(hn)], 'jca', '( %s -> ( G e. NN0 /\\ H e. NN0 ) )' % pS))
    dj = s([b4, sm], 'jca', '( %s -> ( %s /\\ %s ) )' % (pS, concl(w, pS, b4), SOMEne))
    kn = s([s([dj, w.inst('scandj')], 'syl', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (pS, KF, PFS))], 'simpld', '( %s -> %s e. NN0 )' % (pS, KF))
    gk, kl = sc['G <_ %s' % KF], sc['%s < ( G + H )' % KF]
    kgn = s([LS(gn), kn, gk, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( %s - G ) e. NN0 )' % (pS, KF))
    rnS = s([rS, s([kgn, w.inst('peano2nn0')], 'syl', '( %s -> ( ( %s - G ) + 1 ) e. NN0 )' % (pS, KF))], 'eqeltrd', '( %s -> R e. NN0 )' % pS)
    clS = Closure(w, pS, {'G': ('NN0', LS(gn)), 'H': ('NN0', LS(hn)), KF: ('NN0', kn), 'R': ('NN0', rnS)})
    ghS = clS.mem('( G + H )', 'NN0')
    kf1 = s([kl, s([kn, ghS, w.inst('nn0ltp1le')], 'syl2anc', '( %s -> ( %s < ( G + H ) <-> ( %s + 1 ) <_ ( G + H ) ) )' % (pS, KF, KF))], 'mpbid',
            '( %s -> ( %s + 1 ) <_ ( G + H ) )' % (pS, KF))
    rlS = linarith(w, pS, [rS, kf1], 'R <_ H', closure=clS)
    r1S = linarith(w, pS, [rS, gk], '1 <_ R', closure=clS)
    n0R = s([s([s([linarith(w, pS, [rS, gk], '0 < R', closure=clS)], 'gt0ne0d', '( %s -> R =/= 0 )' % pS)], 'necomd', '( %s -> 0 =/= R )' % pS)],
            'neneqd', '( %s -> -. 0 = R )' % pS)
    nH0 = s([s([linarith(w, pS, [gk, kl], '0 < H', closure=clS)], 'gt0ne0d', '( %s -> H =/= 0 )' % pS)], 'neneqd', '( %s -> -. H = 0 )' % pS)
    biS = s([s([n0R, nH0], 'jca', '( %s -> ( -. 0 = R /\\ -. H = 0 ) )' % pS), w.inst('pm5.21')], 'syl', '( %s -> ( 0 = R <-> H = 0 ) )' % pS)
    sj0S = s([n0R], 'intnanrd', '( %s -> -. %s )' % (pS, SJ('0')))
    sjR = s([s([s([s([], 'eqid', 'R = R')], 'a1i', '( %s -> R = R )' % pS), nS], 'jca', '( %s -> %s )' % (pS, SJ('R')))], 'iftrued',
            '( %s -> %s = 0 )' % (pS, VN('R')))
    grk = lineq(w, pS, '( ( G + R ) - 1 )', KF, hyps=[rS], closure=clS)
    x2 = s([s([r1S, grk], 'jca', '( %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (pS, KF))], 'ex',
           '( %s -> ( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) ) )' % (ph, NONE, KF))
    x1 = s([rhN], 'ex', '( %s -> ( %s -> R = H ) )' % (ph, NONE))
    # ---- combine
    rn = s([rnN, rnS], 'pm2.61dan', '( %s -> R e. NN0 )' % ph)
    rl = s([rlN, rlS], 'pm2.61dan', '( %s -> R <_ H )' % ph)
    bi = s([biN, biS], 'pm2.61dan', '( %s -> ( 0 = R <-> H = 0 ) )' % ph)
    sj0 = s([sj0N, sj0S], 'pm2.61dan', '( %s -> -. %s )' % (ph, SJ('0')))
    vr = s([vrN, sjR], 'pm2.61dan', '( %s -> %s = 0 )' % (ph, VN('R')))
    v0 = s([sj0], 'iffalsed', '( %s -> %s = %s )' % (ph, VN('0'), Vf('0')))
    g0 = s([s([gn], 'nn0cnd', '( %s -> G e. CC )' % ph), w.inst('addrid')], 'syl', '( %s -> ( G + 0 ) = G )' % ph)
    h0 = s([s([hn], 'nn0cnd', '( %s -> H e. CC )' % ph), w.inst('subid1')], 'syl', '( %s -> ( H - 0 ) = H )' % ph)
    r0v, x0v = w.rewrite(Vf('0'), {'( G + 0 )': ('G', g0), '( H - 0 )': ('H', h0)}, ph)
    assert x0v == SC2, x0v
    v0f = s([v0, r0v], 'eqtrd', '( %s -> %s = %s )' % (ph, VN('0'), SC2))
    a = s([s([rn, rl], 'jca', '( %s -> ( R e. NN0 /\\ R <_ H ) )' % ph), s([bi, sj0], 'jca', '( %s -> %s )' % (ph, cj(C0_T[0][1])))], 'jca',
          '( %s -> %s )' % (ph, cj(C0_T[0])))
    b = s([s([v0f, vr], 'jca', '( %s -> %s )' % (ph, cj(C0_T[1][0]))), s([x1, x2], 'jca', '( %s -> %s )' % (ph, cj(C0_T[1][1])))], 'jca',
          '( %s -> %s )' % (ph, cj(C0_T[1])))
    w.qed([a, b], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


def tmscrn():
    lab = 'tmscrn'
    T = TREES[lab][0]
    ph = cj(T)
    w = W(lab, 'An iteration ` i < R ` of the scan loop without success at ` k + i ` : the success flag is off at ` i + 1 ` '
               '(a success at ` i + 1 = R ` would be one at ` k + i ` , ~ tmscsome ), and ` i + 1 = R ` exactly when the fuel '
               '` fuel - ( i + 1 ) ` is spent.')
    s = w.s
    c = Ctx(w, ph, T)
    f = ifacts(w, ph, c)
    r0, cl = f['r0'], f['cl']
    nsuc = c['-. %s' % SUC(GI('i'))]
    # no success flag at i + 1
    q = '( %s /\\ %s )' % (ph, SJ(I1))
    L = lambda st: lift_from(w, ph, q, st)
    sjq = s([], 'simpr', '( %s -> %s )' % (q, SJ(I1)))
    e1 = s([sjq], 'simpld', '( %s -> %s = R )' % (q, I1))
    ns = s([sjq], 'simprd', '( %s -> -. %s )' % (q, NONE))
    x2 = L(r0['( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (NONE, KF)])
    gr = s([s([ns, x2], 'mpd', '( %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (q, KF))], 'simprd', '( %s -> ( ( G + R ) - 1 ) = %s )' % (q, KF))
    clq = Closure(w, q, {'i': ('NN0', L(f['inn'])), 'G': ('NN0', L(f['gn'])), 'R': ('NN0', L(r0['R e. NN0']))})
    kfr = s([gr, clq.mem('( ( G + R ) - 1 )', 'RR')], 'eqeltrrd', '( %s -> %s e. RR )' % (q, KF))
    clq.leaf(KF, 'RR', kfr)
    kfe = lineq(w, q, KF, GI('i'), hyps=[gr, e1], closure=clq)
    cq = Ctx(w, q, (T, SJ(I1)))
    sc, _ = some_inst(w, q, cq, ns)
    sk = sc[SUC(KF)]
    bi, new = w.wcongr(SUC(KF), {}, q, {}, rules={KF: (GI('i'), kfe)})
    assert new == SUC(GI('i')), new
    sgi = s([sk, bi], 'mpbid', '( %s -> %s )' % (q, SUC(GI('i'))))
    nsj = s([sgi, L(nsuc)], 'pm2.65da', '( %s -> -. %s )' % (ph, SJ(I1)))
    # i + 1 = R <-> H - ( i + 1 ) = 0
    q1 = '( %s /\\ %s = R )' % (ph, I1)
    L1 = lambda st: lift_from(w, ph, q1, st)
    e11 = s([], 'simpr', '( %s -> %s = R )' % (q1, I1))
    im = s([L1(nsj), s([], 'imnan', '( ( %s = R -> -. -. %s ) <-> -. %s )' % (I1, NONE, SJ(I1)))], 'sylibr' if False else 'sylibr',
           '( %s -> ( %s = R -> -. -. %s ) )' % (q1, I1, NONE))
    nn1 = s([s([e11, im], 'mpd', '( %s -> -. -. %s )' % (q1, NONE))], 'notnotrd', '( %s -> %s )' % (q1, NONE))
    rh = s([nn1, L1(r0['( %s -> R = H )' % NONE])], 'mpd', '( %s -> R = H )' % q1)
    cl1 = Closure(w, q1, {'i': ('NN0', L1(f['inn'])), 'H': ('NN0', L1(f['hn'])), 'R': ('NN0', L1(r0['R e. NN0']))})
    d1 = s([lineq(w, q1, HI(I1), '0', hyps=[e11, rh], closure=cl1)], 'ex', '( %s -> ( %s = R -> %s = 0 ) )' % (ph, I1, HI(I1)))
    q2 = '( %s /\\ %s = 0 )' % (ph, HI(I1))
    L2 = lambda st: lift_from(w, ph, q2, st)
    cl2 = Closure(w, q2, {'i': ('NN0', L2(f['inn'])), 'H': ('NN0', L2(f['hn'])), 'R': ('NN0', L2(r0['R e. NN0']))})
    d2 = s([lineq(w, q2, I1, 'R', hyps=[s([], 'simpr', '( %s -> %s = 0 )' % (q2, HI(I1))), L2(f['i1le']), L2(r0['R <_ H'])], closure=cl2)], 'ex',
           '( %s -> ( %s = 0 -> %s = R ) )' % (ph, HI(I1), I1))
    b = s([d1, d2], 'impbid', '( %s -> ( %s = R <-> %s = 0 ) )' % (ph, I1, HI(I1)))
    w.qed([nsj, b], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


def tmscrs():
    lab = 'tmscrs'
    T = TREES[lab][0]
    ph = cj(T)
    w = W(lab, 'An iteration ` i < R ` of the scan loop with success at ` k + i ` : the scan succeeds (~ tmscnone ), there is no '
               'success before ` k + i ` (~ tmscmin ), so ` k\' = k + i ` , ` i + 1 = R ` and the returned pool is the pool at '
               '` k + i ` (~ tmscsome ).')
    s = w.s
    c = Ctx(w, ph, T)
    f = ifacts(w, ph, c)
    r0, cl = f['r0'], f['cl']
    suc = c[SUC(GI('i'))]
    gin = f['gin']
    ggi = linarith(w, ph, [cl.ge0('i')], 'G <_ %s' % GI('i'), closure=cl)
    glt = linarith(w, ph, [f['ilt'], r0['R <_ H']], '%s < ( G + H )' % GI('i'), closure=cl)
    # the scan succeeds
    q = '( %s /\\ %s )' % (ph, NONE)
    L = lambda st: lift_from(w, ph, q, st)
    NA = '( ( %s /\\ ( G e. NN0 /\\ H e. NN0 ) ) /\\ ( %s /\\ ( %s e. NN0 /\\ G <_ %s /\\ %s < ( G + H ) ) ) )' % (
        cj(HYP4), NONE, GI('i'), GI('i'), GI('i'))
    na = s([s([L(h4(c)), L(c['( G e. NN0 /\\ H e. NN0 )'])], 'jca', '( %s -> ( %s /\\ ( G e. NN0 /\\ H e. NN0 ) ) )' % (q, cj(HYP4))),
            s([s([], 'simpr', '( %s -> %s )' % (q, NONE)), s([L(gin), L(ggi), L(glt)], '3jca',
                                                             '( %s -> ( %s e. NN0 /\\ G <_ %s /\\ %s < ( G + H ) ) )' % (q, GI('i'), GI('i'), GI('i')))],
              'jca', '( %s -> ( %s /\\ ( %s e. NN0 /\\ G <_ %s /\\ %s < ( G + H ) ) ) )' % (q, NONE, GI('i'), GI('i'), GI('i')))], 'jca',
           '( %s -> %s )' % (q, NA))
    nsq = s([na, w.inst('tmscnone')], 'syl', '( %s -> -. %s )' % (q, SUC(GI('i'))))
    nn = s([L(suc), nsq], 'pm2.65da', '( %s -> -. %s )' % (ph, NONE))
    sc, sm = some_inst(w, ph, c, nn)
    gr = s([s([nn, r0['( -. %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (NONE, KF)]], 'mpd',
              '( %s -> ( 1 <_ R /\\ ( ( G + R ) - 1 ) = %s ) )' % (ph, KF))], 'simprd', '( %s -> ( ( G + R ) - 1 ) = %s )' % (ph, KF))
    kfr = s([gr, cl.mem('( ( G + R ) - 1 )', 'RR')], 'eqeltrrd', '( %s -> %s e. RR )' % (ph, KF))
    cl.leaf(KF, 'RR', kfr)
    # no success before k'
    q2 = '( %s /\\ %s < %s )' % (ph, GI('i'), KF)
    L2 = lambda st: lift_from(w, ph, q2, st)
    MA = '( ( %s /\\ ( G e. NN0 /\\ H e. NN0 ) ) /\\ ( %s /\\ ( %s e. NN0 /\\ G <_ %s /\\ %s < %s ) ) )' % (
        cj(HYP4), SOMEne, GI('i'), GI('i'), GI('i'), KF)
    ma = s([s([L2(h4(c)), L2(c['( G e. NN0 /\\ H e. NN0 )'])], 'jca', '( %s -> ( %s /\\ ( G e. NN0 /\\ H e. NN0 ) ) )' % (q2, cj(HYP4))),
            s([L2(sm), s([L2(gin), L2(ggi), s([], 'simpr', '( %s -> %s < %s )' % (q2, GI('i'), KF))], '3jca',
                         '( %s -> ( %s e. NN0 /\\ G <_ %s /\\ %s < %s ) )' % (q2, GI('i'), GI('i'), GI('i'), KF))],
              'jca', '( %s -> ( %s /\\ ( %s e. NN0 /\\ G <_ %s /\\ %s < %s ) ) )' % (q2, SOMEne, GI('i'), GI('i'), GI('i'), KF))], 'jca',
           '( %s -> %s )' % (q2, MA))
    nsq2 = s([ma, w.inst('tmscmin')], 'syl', '( %s -> -. %s )' % (q2, SUC(GI('i'))))
    nlt = s([L2(suc), nsq2], 'pm2.65da', '( %s -> -. %s < %s )' % (ph, GI('i'), KF))
    kle = s([nlt, s([kfr, cl.mem(GI('i'), 'RR')], 'lenltd', '( %s -> ( %s <_ %s <-> -. %s < %s ) )' % (ph, KF, GI('i'), GI('i'), KF))], 'mpbird',
            '( %s -> %s <_ %s )' % (ph, KF, GI('i')))
    i1r = lineq(w, ph, I1, 'R', hyps=[gr, kle, f['i1le']], closure=cl)
    kfe = lineq(w, ph, KF, GI('i'), hyps=[gr, i1r], closure=cl)
    pf = sc['%s = %s' % (PFS, PA1(KF))]
    rp, xp = w.rewrite(PA1(KF), {KF: (GI('i'), kfe)}, ph)
    assert xp == PA1(GI('i')), xp
    pfe = s([pf, rp], 'eqtrd', '( %s -> %s = %s )' % (ph, PFS, PA1(GI('i'))))
    w.qed([s([nn, i1r], 'jca', '( %s -> ( -. %s /\\ %s = R ) )' % (ph, NONE, I1)), pfe], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


def value(w, ph, c, f, branch):
    """( ph -> VN( i ) = ( 2nd ` ( the branch of scanp1 ) ) ) ; branch a list of (step, truth) for the ifs"""
    s = w.s
    cl = f['cl']
    v0 = s([f['nsi']], 'iffalsed', '( %s -> %s = %s )' % (ph, VN('i'), Vf('i')))
    H1 = '( %s + 1 )' % HI(I1)
    hh = lineq(w, ph, HI('i'), H1, closure=cl)
    rv, xv = w.rewrite(Vf('i'), {HI('i'): (H1, hh)}, ph)
    m = {'S': 'W', 'X': 'F', 'K': GI('i'), 'F': HI(I1)}
    ex = {'W e. Word NN0': c['W e. Word NN0'], 'F e. NN0': c['F e. NN0'], 'Z e. NN0': c['Z e. NN0'], 'O e. NN0': c['O e. NN0'],
          '%s e. NN0' % GI('i'): f['gin'], '%s e. NN0' % HI(I1): f['hin']}
    sp, cc = inst(w, ph, 'scanp1', m, Bld(w, ph, c, ex))
    lhs, rhs = cc.split(' = ', 1)
    assert '( 2nd ` %s )' % lhs == xv, (lhs, xv)
    cur = rhs
    e = s([rv, s([sp], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (ph, xv, cur))], 'eqtrd', '( %s -> %s = ( 2nd ` %s ) )' % (ph, Vf('i'), cur))
    for st, truth in branch:
        cnd, a, b = ifparts(cur)
        nxt = a if truth else b
        e2 = s([st], 'iftrued' if truth else 'iffalsed', '( %s -> %s = %s )' % (ph, cur, nxt))
        e = s([e, s([e2], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, cur, nxt))], 'eqtrd',
              '( %s -> %s = ( 2nd ` %s ) )' % (ph, Vf('i'), nxt))
        cur = nxt
    val = pairparts(cur)[1]
    e = s([e, snd(w, ph, cur)], 'eqtrd', '( %s -> %s = %s )' % (ph, Vf('i'), val))
    return s([v0, e], 'eqtrd', '( %s -> %s = %s )' % (ph, VN('i'), val)), val


def next_v(w, ph, f, val, nsj1):
    """rewrite ( 2nd ` SC( ( G + i ) + 1 , H - ( i + 1 ) ) ) in val to VN( i + 1 ) (nsj1 : -. SJ( i + 1 ))"""
    s = w.s
    cl = f['cl']
    ga = s([cl.mem('G', 'CC'), cl.mem('i', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ph)], 'addassd',
           '( %s -> ( %s + 1 ) = %s )' % (ph, GI('i'), GI(I1)))
    V1 = '( 2nd ` %s )' % SCf('( %s + 1 )' % GI('i'), HI(I1))
    r1, x1 = w.rewrite(V1, {'( %s + 1 )' % GI('i'): (GI(I1), ga)}, ph)
    assert x1 == Vf(I1), x1
    vn1 = s([nsj1], 'iffalsed', '( %s -> %s = %s )' % (ph, VN(I1), Vf(I1)))
    e = s([r1, vn1], 'eqtr4d', '( %s -> %s = %s )' % (ph, V1, VN(I1)))
    return w.rewrite(val, {V1: (VN(I1), e)}, ph)


def nsuc_rn(w, ph, c, nsuc):
    """~ tmscrn under ph from nsuc : ( ph -> -. SUC ( G + i ) )"""
    s = w.s
    a = s([c[cj(TI)], nsuc], 'jca', '( %s -> ( %s /\\ -. %s ) )' % (ph, cj(TI), SUC(GI('i'))))
    st = s([a, w.inst('tmscrn')], 'syl', '( %s -> %s )' % (ph, TREES['tmscrn'][1]))
    return s([st], 'simpld', '( %s -> -. %s )' % (ph, SJ(I1)))


def tmscva():
    lab = 'tmscva'
    T = TREES[lab][0]
    ph = cj(T)
    w = W(lab, 'The charge of an iteration of the scan loop at ` k + i ` not coprime (~ scanp1 ): ` VN i = VN ( i + 1 ) + a + 1 ` '
               'with ` a ` the ` coprimeTo ` charge.')
    s = w.s
    c = Ctx(w, ph, T)
    f = ifacts(w, ph, c)
    ncp = c['-. %s' % CPc(GI('i'))]
    nsj1 = nsuc_rn(w, ph, c, s([ncp], 'intnanrd', '( %s -> -. %s )' % (ph, SUC(GI('i')))))
    v, val = value(w, ph, c, f, [(ncp, False)])
    r, x = next_v(w, ph, f, val, nsj1)
    w.qed([v, r], 'eqtrd', STMTS[lab])
    return w.run(unify_only=UO)


def tmscvb():
    lab = 'tmscvb'
    T = TREES[lab][0]
    ph = cj(T)
    w = W(lab, 'The charge of an iteration of the scan loop at ` k + i ` coprime with a pool below ` theta ` (~ scanp1 ): '
               '` VN i = VN ( i + 1 ) + a + c + 1 ` with ` a ` , ` c ` the ` coprimeTo ` and ` poolAlg ` charges.')
    s = w.s
    c = Ctx(w, ph, T)
    f = ifacts(w, ph, c)
    cp, nle = c[CPc(GI('i'))], c['-. %s' % OLE(GI('i'))]
    nsj1 = nsuc_rn(w, ph, c, s([nle], 'intnand', '( %s -> -. %s )' % (ph, SUC(GI('i')))))
    v, val = value(w, ph, c, f, [(cp, True), (nle, False)])
    r, x = next_v(w, ph, f, val, nsj1)
    w.qed([v, r], 'eqtrd', STMTS[lab])
    return w.run(unify_only=UO)


def tmscvc():
    lab = 'tmscvc'
    T = TREES[lab][0]
    ph = cj(T)
    w = W(lab, 'The charge of the successful iteration of the scan loop (~ scanp1 , ~ tmscrs ): ` VN i = a + c + 1 ` and '
               '` VN ( i + 1 ) = 0 ` .')
    s = w.s
    c = Ctx(w, ph, T)
    f = ifacts(w, ph, c)
    suc = c[SUC(GI('i'))]
    cp = s([suc], 'simpld', '( %s -> %s )' % (ph, CPc(GI('i'))))
    le = s([suc], 'simprd', '( %s -> %s )' % (ph, OLE(GI('i'))))
    v, val = value(w, ph, c, f, [(cp, True), (le, True)])
    rs = s([c[cj(T)] if False else s([c[cj(TI)], suc], 'jca', '( %s -> %s )' % (ph, cj(T))), w.inst('tmscrs')], 'syl',
           '( %s -> %s )' % (ph, TREES['tmscrs'][1]))
    a = s([rs], 'simpld', '( %s -> ( -. %s /\\ %s = R ) )' % (ph, NONE, I1))
    sj = s([s([a], 'simprd', '( %s -> %s = R )' % (ph, I1)), s([a], 'simpld', '( %s -> -. %s )' % (ph, NONE))], 'jca', '( %s -> %s )' % (ph, SJ(I1)))
    v1 = s([sj], 'iftrued', '( %s -> %s = 0 )' % (ph, VN(I1)))
    w.qed([v, v1], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


if __name__ == '__main__':
    if 'show' in SEL:
        for l in STMTS:
            print(l, len(STMTS[l].split()))
    for l in SEL:
        if l != 'show':
            globals()[l]()
