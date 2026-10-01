"""T9: the state sequence of the extraction loop (Lean ` extractFin ` unrolled): ~ df-exstop , ~ df-exst , ~ df-exit .

  exstopv    value of ` ExStOp `
  exstopcl   ` ExStOp ` maps states to states
  tmexif1    ` if ( ph , 1o , (/) ) = 1o <-> ph `
  exstv      value of ` ExSt ` : a ` seq `
  exst0      the sequence starts at the given state
  exstp1     one step of the sequence is ` ExStOp ` at the next pool element
  exstcl     the sequence stays in the state set along the pool
  exitv      value of ` ExIt `
  exitp      the stop index: in ` ( 0 ... # W ) ` , the pool is exhausted or the last step hit, earlier indices are
             pool indices without a hit

    MM_DB=sorties/t9.mm python3 tools/gen/t9_h_seq.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq

SEL = sys.argv[1:]
PH_OP = '( ( L e. NN /\\ G e. NN0 ) /\\ ( Z e. %s /\\ F e. NN0 ) )' % STY
ZPV = '( Z ( L ExStOp G ) F )'
ST_OPV = '( %s -> %s = %s )' % (PH_OP, ZPV, STOPB('L', 'G', 'Z', 'F'))
ST_OPCL = '( %s -> %s e. %s )' % (PH_OP, ZPV, STY)
ST_IF1 = '( if ( ph , 1o , (/) ) = 1o <-> ph )'
PH_S = '( ( L e. NN /\\ G e. NN0 ) /\\ ( W e. Word NN0 /\\ Z e. %s ) )' % STY
SQW = SQ('W', 'L', 'G', 'Z')
FFW = SQF_('W', 'Z', 'L', 'G')
ST_SV = '( %s -> %s = seq 0 ( ( L ExStOp G ) , %s ) )' % (PH_S, SQW, FFW)
ST_S0 = '( %s -> ( %s ` 0 ) = Z )' % (PH_S, SQW)
ST_SP1 = '( ( %s /\\ I e. NN0 ) -> ( %s ` ( I + 1 ) ) = ( ( %s ` I ) ( L ExStOp G ) ( W ` I ) ) )' % (PH_S, SQW, SQW)
ST_SCL = '( ( %s /\\ I e. ( 0 ... ( # ` W ) ) ) -> ( %s ` I ) e. %s )' % (PH_S, SQW, STY)
RW_ = RIT('W', 'L', 'G', 'Z')
SSET = STOPSET('W', SQW)
ST_IV = '( %s -> %s = inf ( %s , RR , < ) )' % (PH_S, RW_, SSET)
HI = lambda t: ZH('( %s ` %s )' % (SQW, t))
ST_IP = ('( %s -> ( %s e. ( 0 ... ( # ` W ) ) /\\ ( %s = ( # ` W ) \\/ %s = 1o ) /\\ A. i e. ( 0 ..^ %s ) ( i e. ( 0 ..^ ( # ` W ) ) /\\ -. %s = 1o ) ) )'
         % (PH_S, RW_, RW_, HI(RW_), RW_, HI('i')))


def _cg(w, expr, var, val):
    h, n = w.congr(expr, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    if h is None:
        h = w.s([], 'eqidd', '( %s = %s -> %s = %s )' % (var, val, expr, expr)); n = expr
    return h, n


def sty_ex(w):
    """closed: STY e. _V"""
    s = w.s
    tex = s([s([], 'df-tbl', 'Tbl = ( ( Word NN0 |_| 1o ) ^m NN0 )'), s([], 'ovex', '( ( Word NN0 |_| 1o ) ^m NN0 ) e. _V')], 'eqeltri', 'Tbl e. _V')
    t2 = s([tex, s([], '2oex', '2o e. _V')], 'xpex', '( Tbl X. 2o ) e. _V')
    wn = s([s([], 'nn0ex', 'NN0 e. _V'), w.inst('wrdexg')], 'ax-mp', 'Word NN0 e. _V')
    t3 = s([wn, t2], 'xpex', '( Word NN0 X. ( Tbl X. 2o ) ) e. _V')
    return s([s([], 'nn0ex', 'NN0 e. _V'), t3], 'xpex', '%s e. _V' % STY), wn


def exstopv():
    lab = 'exstopv'
    ph = PH_OP
    w = W(lab, 'Value of ~ df-exstop .')
    s = w.s
    IN = lambda l, n: '( x e. %s , p e. NN0 |-> %s )' % (STY, STOPB(l, n, 'x', 'p'))
    h1, n1 = _cg(w, IN('l', 'n'), 'l', 'L')
    h2, n2 = _cg(w, n1, 'n', 'G')
    assert n2 == IN('L', 'G'), n2
    df = s([], 'df-exstop', DF_EXSTOP)
    ov = s([h1, h2, df], 'ovmpog', '( ( L e. NN /\\ G e. NN0 /\\ %s e. _V ) -> ( L ExStOp G ) = %s )' % (IN('L', 'G'), IN('L', 'G')))
    lg = s([], 'simpl', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph)
    zf = s([], 'simpr', '( %s -> ( Z e. %s /\\ F e. NN0 ) )' % (ph, STY))
    sx, _ = sty_ex(w)
    mex = s([s([sx, s([], 'nn0ex', 'NN0 e. _V')], 'mpoex', '%s e. _V' % IN('L', 'G'))], 'a1i', '( %s -> %s e. _V )' % (ph, IN('L', 'G')))
    o1 = s([s([lg], 'simpld', '( %s -> L e. NN )' % ph), s([lg], 'simprd', '( %s -> G e. NN0 )' % ph), mex, ov], 'syl3anc',
           '( %s -> ( L ExStOp G ) = %s )' % (ph, IN('L', 'G')))
    o2 = s([o1], 'oveqd', '( %s -> %s = ( Z %s F ) )' % (ph, ZPV, IN('L', 'G')))
    B_ = STOPB('L', 'G', 'x', 'p')
    g1, m1 = _cg(w, B_, 'x', 'Z')
    g2, m2 = _cg(w, m1, 'p', 'F')
    V = STOPB('L', 'G', 'Z', 'F')
    assert m2 == V, m2
    ov2 = s([g1, g2, s([], 'eqid', '%s = %s' % (IN('L', 'G'), IN('L', 'G')))], 'ovmpog',
            '( ( Z e. %s /\\ F e. NN0 /\\ %s e. _V ) -> ( Z %s F ) = %s )' % (STY, V, IN('L', 'G'), V))
    toks = V.split()
    # the two tuples are sets
    i1 = V.index(' , <. ')
    parts_ = V[len('if ( '):]
    from t6blib import _split_top
    inner = V.split()[2:-1]
    ps = _split_top(inner, ',')
    assert len(ps) == 3, len(ps)
    A_, C_ = ps[1], ps[2]
    bex = s([s([s([], 'opex', '%s e. _V' % A_), s([], 'opex', '%s e. _V' % C_)], 'ifex', '%s e. _V' % V)], 'a1i', '( %s -> %s e. _V )' % (ph, V))
    o3 = s([s([zf], 'simpld', '( %s -> Z e. %s )' % (ph, STY)), s([zf], 'simprd', '( %s -> F e. NN0 )' % ph), bex, ov2], 'syl3anc',
           '( %s -> ( Z %s F ) = %s )' % (ph, IN('L', 'G'), V))
    w.qed([o2, o3], 'eqtrd', ST_OPV)
    return w.run()


def exstopcl():
    lab = 'exstopcl'
    ph = PH_OP
    w = W(lab, 'One step of the extraction state stays a state (~ df-exstop ).')
    s = w.s
    c = Ctx(w, ph, (('L e. NN', 'G e. NN0'), ('Z e. %s' % STY, 'F e. NN0')))
    ln, gn, zs, fn = c['L e. NN'], c['G e. NN0'], c['Z e. %s' % STY], c['F e. NN0']
    T23 = '( Word NN0 X. ( Tbl X. 2o ) )'
    mz = s([zs, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, ZM('Z')))
    z2 = s([zs, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` Z ) e. %s )' % (ph, T23))
    uz = s([z2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ZU('Z')))
    z3 = s([z2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` Z ) ) e. ( Tbl X. 2o ) )' % ph)
    az = s([z3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, ZA('Z')))
    AZ = ZA('Z')
    dp = s([s([s([ln, fn], 'jca', '( %s -> ( L e. NN /\\ F e. NN0 ) )' % ph), az], 'jca', '( %s -> ( ( L e. NN /\\ F e. NN0 ) /\\ %s e. Tbl ) )' % (ph, AZ)),
            w.inst('dpstepcl')], 'syl', '( %s -> %s e. ( Tbl X. NN0 ) )' % (ph, DPS_('L', 'F', AZ)))
    a1 = s([dp, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, DP1('L', 'F', AZ)))
    z0 = closed(w, ph, '0el2o', '(/) e. 2o')
    def tup(m, mm, u, uu, a, aa, h, hh):
        t1 = s([aa, hh], 'opelxpd', '( %s -> <. %s , %s >. e. ( Tbl X. 2o ) )' % (ph, a, h))
        t2 = s([uu, t1], 'opelxpd', '( %s -> <. %s , <. %s , %s >. >. e. %s )' % (ph, u, a, h, T23))
        return s([mm, t2], 'opelxpd', '( %s -> %s e. %s )' % (ph, ZT(m, u, a, h), STY))
    T1 = tup(ZM('Z'), mz, ZU('Z'), uz, DP1('L', 'F', AZ), a1, '(/)', z0)
    SL = SLF('L', 'F', AZ)
    ML = '( 1 mod L )'
    mln = s([closed(w, ph, '1z', '1 e. ZZ'), ln, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ML))
    sl = s([a1, mln, w.inst('tblfv')], 'syl2anc', '( %s -> %s e. ( Word NN0 |_| 1o ) )' % (ph, SL))
    WV = '( 2nd ` %s )' % SL
    wv = s([sl, w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, WV))
    pw = s([s([wv, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, WV)), w.inst('xp1st')], 'syl',
           '( %s -> %s e. NN0 )' % (ph, PRL(WV)))
    MM = '( %s x. %s )' % (ZM('Z'), PRL(WV))
    mm = s([mz, pw], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, MM))
    WU = '( %s ++ %s )' % (WV, ZU('Z'))
    wu = s([wv, uz, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ph, WU))
    et = closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl')
    HT = 'if ( G < %s , 1o , (/) )' % MM
    ht = s([closed(w, ph, '1oel2o', '1o e. 2o'), z0], 'ifcld', '( %s -> %s e. 2o )' % (ph, HT))
    T2 = tup(MM, mm, WU, wu, 'EmptyTbl', et, HT, ht)
    ifc = s([T1, T2], 'ifcld', '( %s -> %s e. %s )' % (ph, STOPB('L', 'G', 'Z', 'F'), STY))
    w.qed([s([], 'exstopv', ST_OPV), ifc], 'eqeltrd', ST_OPCL)
    return w.run()


def tmexif1():
    lab = 'tmexif1'
    w = W(lab, 'A truth value encoded as ` 1o ` / ` (/) ` is ` 1o ` exactly when the wff holds.')
    s = w.s
    X = 'if ( ph , 1o , (/) )'
    a = s([], 'iftrue', '( ph -> %s = 1o )' % X)
    b = s([], 'iffalse', '( -. ph -> %s = (/) )' % X)
    n0 = s([s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
    cc = s([s([b], 'eqeq1d', '( -. ph -> ( %s = 1o <-> (/) = 1o ) )' % X), s([n0], 'a1i', '( -. ph -> -. (/) = 1o )')], 'mtbird',
           '( -. ph -> -. %s = 1o )' % X)
    d = s([cc], 'con4i', '( %s = 1o -> ph )' % X)
    w.qed([d, a], 'impbii', ST_IF1)
    return w.run()


def exstv():
    lab = 'exstv'
    ph = PH_S
    w = W(lab, 'Value of ~ df-exst : the state sequence is a ` seq ` of ~ df-exstop over the pool.')
    s = w.s
    MID = lambda l, n: '( p e. Word NN0 , x e. %s |-> seq 0 ( ( %s ExStOp %s ) , %s ) )' % (STY, l, n, SQF_('p', 'x', l, n))
    h1, n1 = _cg(w, MID('l', 'n'), 'l', 'L')
    h2, n2 = _cg(w, n1, 'n', 'G')
    assert n2 == MID('L', 'G'), n2
    ov = s([h1, h2, s([], 'df-exst', DF_EXST)], 'ovmpog', '( ( L e. NN /\\ G e. NN0 /\\ %s e. _V ) -> ( L ExSt G ) = %s )' % (MID('L', 'G'), MID('L', 'G')))
    c = Ctx(w, ph, (('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)))
    sx, wn = sty_ex(w)
    mex = s([s([wn, sx], 'mpoex', '%s e. _V' % MID('L', 'G'))], 'a1i', '( %s -> %s e. _V )' % (ph, MID('L', 'G')))
    o1 = s([c['L e. NN'], c['G e. NN0'], mex, ov], 'syl3anc', '( %s -> ( L ExSt G ) = %s )' % (ph, MID('L', 'G')))
    o2 = s([o1], 'oveqd', '( %s -> %s = ( W %s Z ) )' % (ph, SQW, MID('L', 'G')))
    BD = lambda p, x: 'seq 0 ( ( L ExStOp G ) , %s )' % SQF_(p, x, 'L', 'G')
    g1, m1 = _cg(w, BD('p', 'x'), 'p', 'W')
    g2, m2 = _cg(w, m1, 'x', 'Z')
    assert m2 == BD('W', 'Z'), m2
    ov2 = s([g1, g2, s([], 'eqid', '%s = %s' % (MID('L', 'G'), MID('L', 'G')))], 'ovmpog',
            '( ( W e. Word NN0 /\\ Z e. %s /\\ %s e. _V ) -> ( W %s Z ) = %s )' % (STY, BD('W', 'Z'), MID('L', 'G'), BD('W', 'Z')))
    bex = s([s([], 'seqex', '%s e. _V' % BD('W', 'Z'))], 'a1i', '( %s -> %s e. _V )' % (ph, BD('W', 'Z')))
    o3 = s([c['W e. Word NN0'], c['Z e. %s' % STY], bex, ov2], 'syl3anc', '( %s -> ( W %s Z ) = %s )' % (ph, MID('L', 'G'), BD('W', 'Z')))
    w.qed([o2, o3], 'eqtrd', ST_SV)
    return w.run()


def exst0():
    lab = 'exst0'
    ph = PH_S
    w = W(lab, 'The state sequence starts at the given state (~ exstv , ~ seq1 ).')
    s = w.s
    c = Ctx(w, ph, (('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)))
    sv = s([], 'exstv', ST_SV)
    SEQ_ = 'seq 0 ( ( L ExStOp G ) , %s )' % FFW
    f0 = s([sv], 'fveq1d', '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (ph, SQW, SEQ_))
    s1 = s([closed(w, ph, '0z', '0 e. ZZ'), w.inst('seq1')], 'syl', '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (ph, SEQ_, FFW))
    X0 = lambda t: 'if ( %s = 0 , Z , ( W ` ( %s - 1 ) ) )' % (t, t)
    xex = s([s([c['Z e. %s' % STY]], 'elexd', '( %s -> Z e. _V )' % ph), s([s([], 'fvex', '( W ` ( 0 - 1 ) ) e. _V')], 'a1i',
                                                                           '( %s -> ( W ` ( 0 - 1 ) ) e. _V )' % ph)], 'ifcld',
            '( %s -> %s e. _V )' % (ph, X0('0')))
    g0 = mval(w, ph, 'k', 'NN0', X0, '0', closed(w, ph, '0nn0', '0 e. NN0'), xex)
    i0 = s([s([], 'eqidd', '( %s -> 0 = 0 )' % ph)], 'iftrued', '( %s -> %s = Z )' % (ph, X0('0')))
    w.qed([s([s([f0, s1], 'eqtrd', '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (ph, SQW, FFW)), g0], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, SQW, X0('0'))),
           i0], 'eqtrd', ST_S0)
    return w.run()


def exstp1():
    lab = 'exstp1'
    ph = '( %s /\\ I e. NN0 )' % PH_S
    w = W(lab, 'One step of the state sequence is ~ df-exstop at the next pool element (~ exstv , ~ seqp1 ).')
    s = w.s
    c = Ctx(w, ph, ((('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)), 'I e. NN0'))
    sv = s([s([], 'exstv', ST_SV)], 'adantr', '( %s -> %s = seq 0 ( ( L ExStOp G ) , %s ) )' % (ph, SQW, FFW))
    SEQ_ = 'seq 0 ( ( L ExStOp G ) , %s )' % FFW
    iN = c['I e. NN0']
    uz = s([iN, w.inst('elnn0uz')], 'sylib', '( %s -> I e. ( ZZ>= ` 0 ) )' % ph)
    sp = s([uz, w.inst('seqp1')], 'syl', '( %s -> ( %s ` ( I + 1 ) ) = ( ( %s ` I ) ( L ExStOp G ) ( %s ` ( I + 1 ) ) ) )' % (ph, SEQ_, SEQ_, FFW))
    X0 = lambda t: 'if ( %s = 0 , Z , ( W ` ( %s - 1 ) ) )' % (t, t)
    I1 = '( I + 1 )'
    i1n = s([iN, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, I1))
    xex = s([s([c['Z e. %s' % STY]], 'elexd', '( %s -> Z e. _V )' % ph), s([s([], 'fvex', '( W ` ( %s - 1 ) ) e. _V' % I1)], 'a1i',
                                                                           '( %s -> ( W ` ( %s - 1 ) ) e. _V )' % (ph, I1))], 'ifcld',
            '( %s -> %s e. _V )' % (ph, X0(I1)))
    g1 = mval(w, ph, 'k', 'NN0', X0, I1, i1n, xex)
    nz = s([s([s([iN, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (ph, I1))], 'nnne0d', '( %s -> %s =/= 0 )' % (ph, I1))], 'neneqd',
           '( %s -> -. %s = 0 )' % (ph, I1))
    i2 = s([nz], 'iffalsed', '( %s -> %s = ( W ` ( %s - 1 ) ) )' % (ph, X0(I1), I1))
    pn = s([s([s([iN], 'nn0cnd', '( %s -> I e. CC )' % ph), closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('pncan')], 'syl2anc',
              '( %s -> ( %s - 1 ) = I )' % (ph, I1))], 'fveq2d', '( %s -> ( W ` ( %s - 1 ) ) = ( W ` I ) )' % (ph, I1))
    fv = s([s([g1, i2], 'eqtrd', '( %s -> ( %s ` %s ) = ( W ` ( %s - 1 ) ) )' % (ph, FFW, I1, I1)), pn], 'eqtrd',
           '( %s -> ( %s ` %s ) = ( W ` I ) )' % (ph, FFW, I1))
    r1 = s([sp, s([fv], 'oveq2d', '( %s -> ( ( %s ` I ) ( L ExStOp G ) ( %s ` %s ) ) = ( ( %s ` I ) ( L ExStOp G ) ( W ` I ) ) )'
                  % (ph, SEQ_, FFW, I1, SEQ_))], 'eqtrd', '( %s -> ( %s ` ( I + 1 ) ) = ( ( %s ` I ) ( L ExStOp G ) ( W ` I ) ) )' % (ph, SEQ_, SEQ_))
    a1 = s([sv], 'fveq1d', '( %s -> ( %s ` ( I + 1 ) ) = ( %s ` ( I + 1 ) ) )' % (ph, SQW, SEQ_))
    b1 = s([s([sv], 'fveq1d', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (ph, SQW, SEQ_))], 'oveq1d',
           '( %s -> ( ( %s ` I ) ( L ExStOp G ) ( W ` I ) ) = ( ( %s ` I ) ( L ExStOp G ) ( W ` I ) ) )' % (ph, SQW, SEQ_))
    w.qed([s([a1, r1], 'eqtrd', '( %s -> ( %s ` ( I + 1 ) ) = ( ( %s ` I ) ( L ExStOp G ) ( W ` I ) ) )' % (ph, SQW, SEQ_)), b1], 'eqtr4d', ST_SP1)
    return w.run()



def exstcl():
    lab = 'exstcl'
    ph0 = PH_S
    w = W(lab, 'The state sequence stays in the state set along the pool (~ exst0 , ~ exstp1 , ~ exstopcl ).')
    s = w.s
    c = Ctx(w, ph0, (('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)))
    NW = '( # ` W )'
    PS = lambda t: '( %s <_ %s -> ( %s ` %s ) e. %s )' % (t, NW, SQW, t, STY)
    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    z0 = s([s([], 'exst0', ST_S0), c['Z e. %s' % STY]], 'eqeltrd', '( %s -> ( %s ` 0 ) e. %s )' % (ph0, SQW, STY))
    base = s([z0], 'a1d', '( %s -> %s )' % (ph0, PS('0')))
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph0, PS('m'))
    a2 = '( %s /\\ ( m + 1 ) <_ %s )' % (a, NW)
    La = lambda st: s([s([s([st], 'adantr', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph0, concl(w, ph0, st)))], 'adantr', '( %s -> %s )' % (a, concl(w, ph0, st)))],
                      'adantr', '( %s -> %s )' % (a2, concl(w, ph0, st)))
    mn = s([s([], 'simplr', '( %s -> m e. NN0 )' % a)], 'adantr', '( %s -> m e. NN0 )' % a2)
    ih0 = s([s([], 'simpr', '( %s -> %s )' % (a, PS('m')))], 'adantr', '( %s -> %s )' % (a2, PS('m')))
    m1l = s([], 'simpr', '( %s -> ( m + 1 ) <_ %s )' % (a2, NW))
    lw = s([La(c['W e. Word NN0']), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (a2, NW))
    cla = Closure(w, a2, {'m': ('NN0', mn), NW: ('NN0', lw)})
    mle = linarith(w, a2, [m1l], 'm <_ %s' % NW, closure=cla)
    ih = s([mle, ih0], 'mpd', '( %s -> ( %s ` m ) e. %s )' % (a2, SQW, STY))
    mlt = linarith(w, a2, [m1l], 'm < %s' % NW, closure=cla)
    posw = linarith(w, a2, [m1l, cla.ge0('m')], '0 < %s' % NW, closure=cla)
    wnn_ = s([s([lw, posw], 'jca', '( %s -> ( %s e. NN0 /\\ 0 < %s ) )' % (a2, NW, NW)), w.inst('elnnnn0b')], 'sylibr', '( %s -> %s e. NN )' % (a2, NW))
    mfz = s([s([mn, wnn_, mlt], '3jca', '( %s -> ( m e. NN0 /\\ %s e. NN /\\ m < %s ) )' % (a2, NW, NW)), w.inst('elfzo0')], 'sylibr',
            '( %s -> m e. ( 0 ..^ %s ) )' % (a2, NW))
    wm = s([La(c['W e. Word NN0']), mfz, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( W ` m ) e. NN0 )' % a2)
    OPH = '( ( L e. NN /\\ G e. NN0 ) /\\ ( ( %s ` m ) e. %s /\\ ( W ` m ) e. NN0 ) )' % (SQW, STY)
    op_in = s([s([La(c['L e. NN']), La(c['G e. NN0'])], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % a2),
               s([ih, wm], 'jca', '( %s -> ( ( %s ` m ) e. %s /\\ ( W ` m ) e. NN0 ) )' % (a2, SQW, STY))], 'jca', '( %s -> %s )' % (a2, OPH))
    STEP = '( ( %s ` m ) ( L ExStOp G ) ( W ` m ) )' % SQW
    oc = s([op_in, w.inst('exstopcl')], 'syl', '( %s -> %s e. %s )' % (a2, STEP, STY))
    sp = s([s([s([s([], 'simpll', '( %s -> %s )' % (a, ph0)) if False else s([s([], 'simpl', '( ( %s /\\ m e. NN0 ) -> %s )' % (ph0, ph0))], 'adantr', '( %s -> %s )' % (a, ph0))], 'adantr', '( %s -> %s )' % (a2, ph0)), mn],
              'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (a2, ph0)), w.inst('exstp1')], 'syl',
           '( %s -> ( %s ` ( m + 1 ) ) = %s )' % (a2, SQW, STEP))
    q1 = s([sp, oc], 'eqeltrd', '( %s -> ( %s ` ( m + 1 ) ) e. %s )' % (a2, SQW, STY))
    st = s([q1], 'ex', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph0, PS('I')))
    p = '( %s /\\ I e. ( 0 ... %s ) )' % (ph0, NW)
    ifz = s([], 'simpr', '( %s -> I e. ( 0 ... %s ) )' % (p, NW))
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> I e. NN0 )' % p)
    ile = s([ifz, w.inst('elfzle2')], 'syl', '( %s -> I <_ %s )' % (p, NW))
    i2 = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph0)), inn], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph0)), ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    w.qed([ile, i2], 'mpd', ST_SCL)
    return w.run()


def exitv():
    lab = 'exitv'
    ph = PH_S
    w = W(lab, 'Value of ~ df-exit : the least index at which the pool is exhausted or a step hit.')
    s = w.s
    BODY = lambda l, n, p, x: 'inf ( %s , RR , < )' % STOPSET(p, '( %s ( %s ExSt %s ) %s )' % (p, l, n, x))
    RABT = lambda l, n, p, x: STOPSET(p, '( %s ( %s ExSt %s ) %s )' % (p, l, n, x))
    MID = lambda l, n: '( p e. Word NN0 , x e. %s |-> %s )' % (STY, BODY(l, n, 'p', 'x'))
    def icg(args0, var, val, mpo):
        """congruence of the inf ( or the mpo around it ) under var = val"""
        r0 = RABT(*args0)
        hr, nr = _cg(w, r0, var, val)
        args1 = [val if a_ == var else a_ for a_ in args0]
        assert nr == RABT(*args1), nr
        hi = s([hr], 'infeq1d', '( %s = %s -> %s = %s )' % (var, val, BODY(*args0), BODY(*args1)))
        if not mpo:
            return hi, BODY(*args1)
        hm = s([hi], 'mpoeq3dv', '( %s = %s -> %s = %s )' % (var, val, MID(args0[0], args0[1]), MID(args1[0], args1[1])))
        return hm, MID(args1[0], args1[1])
    h1, n1 = icg(('l', 'n', 'p', 'x'), 'l', 'L', True)
    h2, n2 = icg(('L', 'n', 'p', 'x'), 'n', 'G', True)
    assert n2 == MID('L', 'G'), n2
    ov = s([h1, h2, s([], 'df-exit', DF_EXIT)], 'ovmpog', '( ( L e. NN /\\ G e. NN0 /\\ %s e. _V ) -> ( L ExIt G ) = %s )' % (MID('L', 'G'), MID('L', 'G')))
    c = Ctx(w, ph, (('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)))
    sx, wn = sty_ex(w)
    mex = s([s([wn, sx], 'mpoex', '%s e. _V' % MID('L', 'G'))], 'a1i', '( %s -> %s e. _V )' % (ph, MID('L', 'G')))
    o1 = s([c['L e. NN'], c['G e. NN0'], mex, ov], 'syl3anc', '( %s -> ( L ExIt G ) = %s )' % (ph, MID('L', 'G')))
    o2 = s([o1], 'oveqd', '( %s -> %s = ( W %s Z ) )' % (ph, RW_, MID('L', 'G')))
    g1, m1 = icg(('L', 'G', 'p', 'x'), 'p', 'W', False)
    g2, m2 = icg(('L', 'G', 'W', 'x'), 'x', 'Z', False)
    V = BODY('L', 'G', 'W', 'Z')
    assert m2 == V, m2
    ov2 = s([g1, g2, s([], 'eqid', '%s = %s' % (MID('L', 'G'), MID('L', 'G')))], 'ovmpog',
            '( ( W e. Word NN0 /\\ Z e. %s /\\ %s e. _V ) -> ( W %s Z ) = %s )' % (STY, V, MID('L', 'G'), V))
    bex = s([s([], 'infex', '%s e. _V' % V)], 'a1i', '( %s -> %s e. _V )' % (ph, V))
    o3 = s([c['W e. Word NN0'], c['Z e. %s' % STY], bex, ov2], 'syl3anc', '( %s -> ( W %s Z ) = %s )' % (ph, MID('L', 'G'), V))
    w.qed([o2, o3], 'eqtrd', ST_IV)
    return w.run()


def exitp():
    lab = 'exitp'
    ph = PH_S
    w = W(lab, 'The stop index of the extraction loop (~ exitv ): it lies in ` ( 0 ... # W ) ` , the pool is exhausted there or the '
               'step before it hit, and every earlier index is a pool index without a hit.')
    s = w.s
    c = Ctx(w, ph, (('L e. NN', 'G e. NN0'), ('W e. Word NN0', 'Z e. %s' % STY)))
    NW = '( # ` W )'
    FZ = '( 0 ... %s )' % NW
    INF = 'inf ( %s , RR , < )' % SSET
    iv = s([], 'exitv', ST_IV)
    lw = s([c['W e. Word NN0'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
    ss1 = s([s([], 'ssrab2', '%s C_ %s' % (SSET, FZ)), s([], 'fzssuz', '%s C_ ( ZZ>= ` 0 )' % FZ)], 'sstri', '%s C_ ( ZZ>= ` 0 )' % SSET)
    ssa = s([ss1], 'a1i', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (ph, SSET))
    COND = lambda t: '( %s = %s \\/ %s = 1o )' % (t, NW, HI(t))
    wfz = s([lw, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NW, FZ))
    idc = s([s([], 'eqidd', '( %s -> %s = %s )' % (ph, NW, NW))], 'orcd', '( %s -> %s )' % (ph, COND(NW)))
    idh = s([], 'id', '( i = %s -> i = %s )' % (NW, NW))
    cg, new = w.wcongr(COND('i'), {'i': NW}, 'i = %s' % NW, {'i': idh})
    assert new == COND(NW), new
    el = s([cg], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (NW, SSET, NW, FZ, COND(NW)))
    wins = s([s([wfz, idc], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (ph, NW, FZ, COND(NW))), el], 'sylibr', '( %s -> %s e. %s )' % (ph, NW, SSET))
    nz = s([wins], 'ne0d', '( %s -> %s =/= (/) )' % (ph, SSET))
    icl = s([ssa, nz, w.inst('infssuzcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, INF, SSET))
    rin = s([iv, icl], 'eqeltrd', '( %s -> %s e. %s )' % (ph, RW_, SSET))
    idr = s([], 'id', '( i = %s -> i = %s )' % (RW_, RW_))
    cgr, newr = w.wcongr(COND('i'), {'i': RW_}, 'i = %s' % RW_, {'i': idr})
    elr = s([cgr], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (RW_, SSET, RW_, FZ, COND(RW_)))
    both = s([rin, elr], 'sylib', '( %s -> ( %s e. %s /\\ %s ) )' % (ph, RW_, FZ, COND(RW_)))
    rfz = s([both], 'simpld', '( %s -> %s e. %s )' % (ph, RW_, FZ))
    rco = s([both], 'simprd', '( %s -> %s )' % (ph, COND(RW_)))
    # earlier indices
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, RW_)
    Li = lambda st: s([st], 'adantr', '( %s -> %s )' % (pi, concl(w, ph, st)))
    ii = s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, RW_))
    fs = s([s([Li(rfz), w.inst('elfzuz3')], 'syl', '( %s -> %s e. ( ZZ>= ` %s ) )' % (pi, NW, RW_)), w.inst('fzoss2')], 'syl',
           '( %s -> ( 0 ..^ %s ) C_ ( 0 ..^ %s ) )' % (pi, RW_, NW))
    iw = s([fs, ii], 'sseldd', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NW))
    ifz = s([iw, w.inst('elfzofz')], 'syl', '( %s -> i e. %s )' % (pi, FZ))
    ilt = s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (pi, RW_))
    pa = '( %s /\\ i e. %s )' % (pi, SSET)
    le2 = s([s([Li(ssa)], 'adantr', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (pa, SSET)), s([], 'simpr', '( %s -> i e. %s )' % (pa, SSET)),
             w.inst('infssuzle')], 'syl2anc', '( %s -> %s <_ i )' % (pa, INF))
    le3 = s([s([s([Li(iv)], 'adantr', '( %s -> %s = %s )' % (pa, RW_, INF)), le2], 'eqbrtrd', '( %s -> %s <_ i )' % (pa, RW_))], 'ex',
            '( %s -> ( i e. %s -> %s <_ i ) )' % (pi, SSET, RW_))
    inn = s([ifz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pi)
    rnn = s([Li(rfz), w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (pi, RW_))
    ln_ = s([s([inn], 'nn0red', '( %s -> i e. RR )' % pi), s([rnn], 'nn0red', '( %s -> %s e. RR )' % (pi, RW_))], 'ltnled',
            '( %s -> ( i < %s <-> -. %s <_ i ) )' % (pi, RW_, RW_))
    nle = s([ilt, ln_], 'mpbid', '( %s -> -. %s <_ i )' % (pi, RW_))
    nin = s([le3, nle], 'mtod', '( %s -> -. i e. %s )' % (pi, SSET))
    rab = s([], 'rabid', '( i e. %s <-> ( i e. %s /\\ %s ) )' % (SSET, FZ, COND('i')))
    nin2 = s([nin, s([rab], 'a1i', '( %s -> ( i e. %s <-> ( i e. %s /\\ %s ) ) )' % (pi, SSET, FZ, COND('i')))], 'mtbid',
             '( %s -> -. ( i e. %s /\\ %s ) )' % (pi, FZ, COND('i')))
    j1 = s([s([], 'idd', '( %s -> ( %s -> %s ) )' % (pi, COND('i'), COND('i'))), ifz], 'jctild',
           '( %s -> ( %s -> ( i e. %s /\\ %s ) ) )' % (pi, COND('i'), FZ, COND('i')))
    nc = s([j1, nin2], 'mtod', '( %s -> -. %s )' % (pi, COND('i')))
    oh = s([s([], 'olc', '( %s = 1o -> %s )' % (HI('i'), COND('i')))], 'a1i', '( %s -> ( %s = 1o -> %s ) )' % (pi, HI('i'), COND('i')))
    nh = s([oh, nc], 'mtod', '( %s -> -. %s = 1o )' % (pi, HI('i')))
    body = s([iw, nh], 'jca', '( %s -> ( i e. ( 0 ..^ %s ) /\\ -. %s = 1o ) )' % (pi, NW, HI('i')))
    ral = s([body], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ %s ) ( i e. ( 0 ..^ %s ) /\\ -. %s = 1o ) )' % (ph, RW_, NW, HI('i')))
    w.qed([rfz, rco, ral], '3jca', ST_IP)
    return w.run()


STMTS = {'exstopv': ST_OPV, 'exstopcl': ST_OPCL, 'tmexif1': ST_IF1, 'exstv': ST_SV, 'exst0': ST_S0, 'exstp1': ST_SP1,
         'exstcl': ST_SCL, 'exitv': ST_IV, 'exitp': ST_IP}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
