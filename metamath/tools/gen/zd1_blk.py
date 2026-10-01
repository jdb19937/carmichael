"""Sortie ZD1: the dyadic block decomposition (Lean sum_mul_exp_le_blocks, with the weight e ^ -j)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import lift

NS = lambda J: '( |_ ` ( ( 2 ^ %s ) x. X ) )' % J
SA = lambda J: 'sum_ n e. ( 1 ... %s ) A' % NS(J)
EX = '( exp ` ( -u n / X ) )'
TERM = '( A x. %s )' % EX
LH = lambda J: BLK_L(J, 'X', 'A')
RH = lambda J: BLK_R(J, 'X', 'A')
BODY = lambda j: '( ( exp ` -u %s ) x. %s )' % (j, SA(j))
PJ = lambda J: '%s <_ %s' % (LH(J), RH(J))


class Ctx:
    """facts under an antecedent a that implies ph (step ph)"""
    def __init__(self, w, a, ph):
        self.w, self.a, self.ph = w, a, ph
        self.st = mkst(w, a)
        self.xrp = w.s([ph, '1'], 'syl', '( %s -> X e. RR+ )' % a)
        self.xr = self.st([self.xrp], 'rpred', 'X e. RR')

    def jfacts(self, J, jn):
        """J e. NN0 (step jn): ( 2 ^ J ) x. X e. RR+, RR; NS(J) e. NN0; range Fin"""
        st = self.st; w = self.w
        p = st([a1c(w, self.a, '2rp', '2 e. RR+'), st([jn], 'nn0zd', '%s e. ZZ' % J)], 'rpexpcld', '( 2 ^ %s ) e. RR+' % J)
        y = st([p, self.xrp], 'rpmulcld', '( ( 2 ^ %s ) x. X ) e. RR+' % J)
        yr = st([y], 'rpred', '( ( 2 ^ %s ) x. X ) e. RR' % J)
        nn0 = sy2(w, self.a, yr, st([y], 'rpge0d', '0 <_ ( ( 2 ^ %s ) x. X )' % J), 'flge0nn0', '%s e. NN0' % NS(J))
        fin = st([], 'fzfid', '( 1 ... %s ) e. Fin' % NS(J))
        return dict(p=p, y=y, yr=yr, nn0=nn0, fin=fin)

    def nfacts(self, R, nnrule=None):
        """under ( a /\\ n e. R ): n e. NN (R a ( 1 ... _ ) range unless nnrule given), A e. RR, 0 <_ A, the term's facts"""
        w = self.w
        b = '( %s /\\ n e. %s )' % (self.a, R)
        sb = mkst(w, b)
        nin = w.s([], 'simpr', '( %s -> n e. %s )' % (b, R))
        nn = nnrule(b, nin) if nnrule else w.s([nin, w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % b)
        php = lift(w, self.ph, b)
        ar = w.s([php, nn, '2'], 'syl2anc', '( %s -> A e. RR )' % b)
        a0 = w.s([php, nn, '3'], 'syl2anc', '( %s -> 0 <_ A )' % b)
        xrp = lift(w, self.xrp, b)
        nr = sb([nn], 'nnred', 'n e. RR')
        q = sb([nr, xrp], 'rerpdivcld', '( n / X ) e. RR')
        ndx = sb([sb([nr], 'renegcld', '-u n e. RR'), xrp], 'rerpdivcld', '( -u n / X ) e. RR')
        er = sb([ndx], 'reefcld', '%s e. RR' % EX)
        tr = sb([ar, er], 'remulcld', '%s e. RR' % TERM)
        # -u ( n / X ) = ( -u n / X )
        dn = sb([sb([nr], 'recnd', 'n e. CC'), sb([xrp], 'rpcnd', 'X e. CC'), sb([xrp], 'rpne0d', 'X =/= 0')], 'divnegd', '-u ( n / X ) = ( -u n / X )')
        return dict(b=b, st=sb, nin=nin, nn=nn, ar=ar, a0=a0, xrp=xrp, nr=nr, q=q, ndx=ndx, er=er, tr=tr, dn=dn)


def pcongr(w, J, v):
    """( i = J -> ( P(i) <-> P(J) ) ) for the induction variable v"""
    idv = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, J, v, J))
    st, new = w.wcongr(PJ(v), {v: J}, '%s = %s' % (v, J), {v: idv})
    return st


def zdblocks():
    w = W('zdblocks', "Block decomposition (Lean sum_mul_exp_le_blocks, blueprint Lemma 8.1 step 2 in discrete dyadic form): for A >_ 0 on NN "
                      "and X > 0, sum_ n <_ 2 ^ J X A e ^ ( - n / X ) <_ sum_ j <_ J e ^ -j sum_ n <_ 2 ^ j X A.  The weight e ^ -j "
                      "absorbs Lean's wgt j <_ e ^ -j: on the block 2 ^ j X < n, n / X > 2 ^ j >_ j + 1 (tpl2pow).")
    hyps_of(w, 'zdblocks')
    # ---- base case under ph
    a = 'ph'
    phs = w.s([], 'id', '( ph -> ph )')
    c = Ctx(w, a, phs)
    st = c.st
    z0 = a1c(w, a, '0nn0', '0 e. NN0')
    f0 = c.jfacts('0', z0)
    R0 = '( 1 ... %s )' % NS('0')
    nf = c.nfacts(R0)
    sb = nf['st']; b = nf['b']
    # e(n) <_ 1
    q0 = sb([nf['nr'], nf['xrp'], sb([sb([nf['nn']], 'nnnn0d', 'n e. NN0')], 'nn0ge0d', '0 <_ n')], 'divge0d', '0 <_ ( n / X )')
    le0 = linarith(w, b, [q0], '-u ( n / X ) <_ 0', leaves={'( n / X )': nf['q']})
    le0b = sb([sb([nf['dn']], 'eqcomd', '( -u n / X ) = -u ( n / X )'), le0], 'eqbrtrd', '( -u n / X ) <_ 0')
    efl = sb([nf['ndx'], sb([], '0red', '0 e. RR'), w.inst('efle')], 'syl2anc', '( ( -u n / X ) <_ 0 <-> %s <_ ( exp ` 0 ) )' % EX)
    e1 = sb([sb([le0b, efl], 'mpbid', '%s <_ ( exp ` 0 )' % EX), a1c(w, b, 'ef0', '( exp ` 0 ) = 1')], 'breqtrd', '%s <_ 1' % EX)
    t1 = sb([nf['er'], sb([], '1red', '1 e. RR'), nf['ar'], nf['a0'], e1], 'lemul2ad', '%s <_ ( A x. 1 )' % TERM)
    t2 = sb([t1, sb([sb([nf['ar']], 'recnd', 'A e. CC')], 'mulridd', '( A x. 1 ) = A')], 'breqtrd', '%s <_ A' % TERM)
    s0 = st([f0['fin'], nf['tr'], nf['ar'], t2], 'fsumle', '%s <_ %s' % (LH('0'), SA('0')))
    # RH(0) = ( exp ` -u 0 ) x. SA(0) = SA(0)
    s0r = st([f0['fin'], nf['ar']], 'fsumrecl', '%s e. RR' % SA('0'))
    idj = w.s([], 'id', '( j = 0 -> j = 0 )')
    cj, _new = w.congr(BODY('j'), {'j': '0'}, 'j = 0', {'j': idj})
    b0c = st([st([st([st([], '0red', '0 e. RR')], 'renegcld', '-u 0 e. RR')], 'reefcld', '( exp ` -u 0 ) e. RR'), s0r], 'remulcld', '%s e. RR' % BODY('0'))
    f1s = st([a1c(w, a, '0z', '0 e. ZZ'), st([b0c], 'recnd', '%s e. CC' % BODY('0')), w.inst('fsum1')], 'syl2anc', '%s = %s' % (RH('0'), BODY('0')))
    en0 = a1c(w, a, 'neg0', '-u 0 = 0')
    ee0 = st([st([en0], 'fveq2d', '( exp ` -u 0 ) = ( exp ` 0 )'), a1c(w, a, 'ef0', '( exp ` 0 ) = 1')], 'eqtrd', '( exp ` -u 0 ) = 1')
    bb = st([st([ee0], 'oveq1d', '%s = ( 1 x. %s )' % (BODY('0'), SA('0'))), st([st([s0r], 'recnd', '%s e. CC' % SA('0'))], 'mullidd', '( 1 x. %s ) = %s' % (SA('0'), SA('0')))],
            'eqtrd', '%s = %s' % (BODY('0'), SA('0')))
    rh0 = st([f1s, bb], 'eqtrd', '%s = %s' % (RH('0'), SA('0')))
    base = st([s0, rh0], 'breqtrrd', PJ('0'))
    # ---- the step under ( ( ph /\ k e. NN0 ) /\ P(k) )
    a = '( ph /\\ k e. NN0 )'
    aI = '( %s /\\ %s )' % (a, PJ('k'))
    phs = w.s([], 'simpl', '( %s -> ph )' % a)
    c = Ctx(w, a, phs)
    st = c.st
    kn = w.s([], 'simpr', '( %s -> k e. NN0 )' % a)
    ih = w.s([], 'simpr', '( %s -> %s )' % (aI, PJ('k')))
    k1n = sy(w, a, kn, 'peano2nn0', '( k + 1 ) e. NN0')
    fk = c.jfacts('k', kn); fk1 = c.jfacts('( k + 1 )', k1n)
    N0, N1 = NS('k'), NS('( k + 1 )')
    Y0, Y1 = '( ( 2 ^ k ) x. X )', '( ( 2 ^ ( k + 1 ) ) x. X )'
    # Y1 = Y0 x. 2
    ep = st([a1c(w, a, '2cn', '2 e. CC'), kn, w.inst('expp1')], 'syl2anc', '( 2 ^ ( k + 1 ) ) = ( ( 2 ^ k ) x. 2 )')
    y1a = st([ep], 'oveq1d', '%s = ( ( ( 2 ^ k ) x. 2 ) x. X )' % Y1)
    y1b = st([st([fk['p']], 'rpcnd', '( 2 ^ k ) e. CC'), a1c(w, a, '2cn', '2 e. CC'), st([c.xrp], 'rpcnd', 'X e. CC')], 'mul32d',
             '( ( ( 2 ^ k ) x. 2 ) x. X ) = ( %s x. 2 )' % Y0)
    y1 = st([y1a, y1b], 'eqtrd', '%s = ( %s x. 2 )' % (Y1, Y0))
    yle = linarith(w, a, [y1, st([fk['y']], 'rpge0d', '0 <_ %s' % Y0)], '%s <_ %s' % (Y0, Y1), leaves={Y0: fk['yr'], Y1: fk1['yr']})
    nle = st([fk['yr'], fk1['yr'], yle, w.inst('flwordi')], 'syl3anc', '%s <_ %s' % (N0, N1))
    R1 = '( 1 ... %s )' % N1
    R0 = '( 1 ... %s )' % N0
    RB = '( ( %s + 1 ) ... %s )' % (N0, N1)
    uz1 = w.s([sy(w, a, fk['nn0'], 'nn0p1nn', '( %s + 1 ) e. NN' % N0), w.s([], 'elnnuz', '( ( %s + 1 ) e. NN <-> ( %s + 1 ) e. ( ZZ>= ` 1 ) )' % (N0, N0))], 'sylib',
              '( %s -> ( %s + 1 ) e. ( ZZ>= ` 1 ) )' % (a, N0))
    uz2 = st([fk['yr'], fk1['yr'], yle, w.inst('flword2')], 'syl3anc', '%s e. ( ZZ>= ` %s )' % (N1, N0))
    un = st([uz1, uz2, w.inst('fzsplit2')], 'syl2anc', '%s = ( %s u. %s )' % (R1, R0, RB))
    n0r = st([fk['nn0']], 'nn0red', '%s e. RR' % N0)
    dj = st([st([n0r], 'ltp1d', '%s < ( %s + 1 )' % (N0, N0)), w.inst('fzdisj')], 'syl', '( %s i^i %s ) = (/)' % (R0, RB))
    nf1 = c.nfacts(R1)
    sp = st([dj, un, fk1['fin'], w.s([nf1['tr']], 'recnd', '( %s -> %s e. CC )' % (nf1['b'], TERM))], 'fsumsplit',
            '%s = ( sum_ n e. %s %s + sum_ n e. %s %s )' % (LH('( k + 1 )'), R0, TERM, RB, TERM))
    # the block: every term <_ e ^ -u ( k + 1 ) A
    E1 = '( exp ` -u ( k + 1 ) )'

    def nnB(bb_, nin):
        u = w.s([nin, w.inst('elun2')], 'syl', '( %s -> n e. ( %s u. %s ) )' % (bb_, R0, RB))
        m = w.s([u, lift(w, un, bb_)], 'eleqtrrd', '( %s -> n e. %s )' % (bb_, R1))
        return w.s([m, w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % bb_)
    nb = c.nfacts(RB, nnrule=nnB)
    sb = nb['st']; b = nb['b']
    kr = lift(w, st([kn], 'nn0red', 'k e. RR'), b)
    lo = w.s([nb['nin'], w.inst('elfzle1')], 'syl', '( %s -> ( %s + 1 ) <_ n )' % (b, N0))
    fl = w.s([lift(w, fk['yr'], b), w.inst('flltp1')], 'syl', '( %s -> %s < ( %s + 1 ) )' % (b, Y0, N0))
    tp = w.s([lift(w, kn, b), w.inst('tpl2pow')], 'syl', '( %s -> ( k + 1 ) <_ ( 2 ^ k ) )' % b)
    k1r = sb([kr, sb([], '1red', '1 e. RR')], 'readdcld', '( k + 1 ) e. RR')
    pkr = lift(w, st([fk['p']], 'rpred', '( 2 ^ k ) e. RR'), b)
    xr_b = sb([nb['xrp']], 'rpred', 'X e. RR')
    m1 = sb([k1r, pkr, xr_b, sb([nb['xrp']], 'rpge0d', '0 <_ X'), tp], 'lemul1ad', '( ( k + 1 ) x. X ) <_ %s' % Y0)
    n0rb = lift(w, n0r, b)
    kx = linarith(w, b, [m1, fl, lo], '( ( k + 1 ) x. X ) <_ n',
                  leaves={'( ( k + 1 ) x. X )': sb([k1r, xr_b], 'remulcld', '( ( k + 1 ) x. X ) e. RR'), Y0: lift(w, fk['yr'], b), N0: n0rb, 'n': nb['nr']})
    bi = sb([k1r, nb['nr'], nb['xrp']], 'lemuldivd', '( ( ( k + 1 ) x. X ) <_ n <-> ( k + 1 ) <_ ( n / X ) )')
    kq = sb([kx, bi], 'mpbid', '( k + 1 ) <_ ( n / X )')
    ng = linarith(w, b, [kq], '-u ( n / X ) <_ -u ( k + 1 )', leaves={'( n / X )': nb['q'], 'k': kr})
    ng2 = sb([sb([nb['dn']], 'eqcomd', '( -u n / X ) = -u ( n / X )'), ng], 'eqbrtrd', '( -u n / X ) <_ -u ( k + 1 )')
    nk1 = sb([k1r], 'renegcld', '-u ( k + 1 ) e. RR')
    efl = sb([nb['ndx'], nk1, w.inst('efle')], 'syl2anc', '( ( -u n / X ) <_ -u ( k + 1 ) <-> %s <_ %s )' % (EX, E1))
    ee = sb([ng2, efl], 'mpbid', '%s <_ %s' % (EX, E1))
    e1r = sb([nk1], 'reefcld', '%s e. RR' % E1)
    tb = sb([nb['er'], e1r, nb['ar'], nb['a0'], ee], 'lemul2ad', '%s <_ ( A x. %s )' % (TERM, E1))
    tb2 = sb([tb, sb([sb([nb['ar']], 'recnd', 'A e. CC'), sb([e1r], 'recnd', '%s e. CC' % E1)], 'mulcomd', '( A x. %s ) = ( %s x. A )' % (E1, E1))],
             'breqtrd', '%s <_ ( %s x. A )' % (TERM, E1))
    finB = st([], 'fzfid', '%s e. Fin' % RB)
    blk1 = st([finB, nb['tr'], sb([e1r, nb['ar']], 'remulcld', '( %s x. A ) e. RR' % E1), tb2], 'fsumle',
              'sum_ n e. %s %s <_ sum_ n e. %s ( %s x. A )' % (RB, TERM, RB, E1))
    e1rs = st([st([st([kn], 'nn0red', 'k e. RR'), st([], '1red', '1 e. RR')], 'readdcld', '( k + 1 ) e. RR')], 'renegcld', '-u ( k + 1 ) e. RR')
    e1ra = st([e1rs], 'reefcld', '%s e. RR' % E1)
    mc = st([finB, st([e1ra], 'recnd', '%s e. CC' % E1), w.s([nb['ar']], 'recnd', '( %s -> A e. CC )' % b)], 'fsummulc2',
            '( %s x. sum_ n e. %s A ) = sum_ n e. %s ( %s x. A )' % (E1, RB, RB, E1))
    blk2 = st([blk1, mc], 'breqtrrd', 'sum_ n e. %s %s <_ ( %s x. sum_ n e. %s A )' % (RB, TERM, E1, RB))
    ssu = w.s([a1c(w, a, 'ssun2', '%s C_ ( %s u. %s )' % (RB, R0, RB)), st([un], 'eqcomd', '( %s u. %s ) = %s' % (R0, RB, R1))], 'sseqtrd',
              '( %s -> %s C_ %s )' % (a, RB, R1))
    sl = st([fk1['fin'], nf1['ar'], nf1['a0'], ssu], 'fsumless', 'sum_ n e. %s A <_ %s' % (RB, SA('( k + 1 )')))
    sbr = st([finB, nb['ar']], 'fsumrecl', 'sum_ n e. %s A e. RR' % RB)
    s1r = st([fk1['fin'], nf1['ar']], 'fsumrecl', '%s e. RR' % SA('( k + 1 )'))
    blk3 = st([sbr, s1r, e1ra, st([st([e1rs], 'rpefcld', '%s e. RR+' % E1)], 'rpge0d', '0 <_ %s' % E1), sl], 'lemul2ad',
              '( %s x. sum_ n e. %s A ) <_ ( %s x. %s )' % (E1, RB, E1, SA('( k + 1 )')))
    # RH(k+1) = RH(k) + BODY(k+1)
    idj = w.s([], 'id', '( j = ( k + 1 ) -> j = ( k + 1 ) )')
    cj, _new = w.congr(BODY('j'), {'j': '( k + 1 )'}, 'j = ( k + 1 )', {'j': idj})
    # closure of the body on ( 0 ... ( k + 1 ) )
    bj = '( %s /\\ j e. ( 0 ... ( k + 1 ) ) )' % a
    jn = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... ( k + 1 ) ) )' % bj), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % bj)
    cj2 = Ctx(w, bj, lift(w, phs, bj))
    fj = cj2.jfacts('j', jn)
    nfj = cj2.nfacts('( 1 ... %s )' % NS('j'))
    sjr = cj2.st([fj['fin'], nfj['ar']], 'fsumrecl', '%s e. RR' % SA('j'))
    bjr = cj2.st([cj2.st([cj2.st([cj2.st([jn], 'nn0red', 'j e. RR')], 'renegcld', '-u j e. RR')], 'reefcld', '( exp ` -u j ) e. RR'), sjr], 'remulcld',
                 '%s e. RR' % BODY('j'))
    kuz = w.s([kn, w.s([], 'elnn0uz', '( k e. NN0 <-> k e. ( ZZ>= ` 0 ) )')], 'sylib', '( %s -> k e. ( ZZ>= ` 0 ) )' % a)
    p1 = st([kuz, w.s([bjr], 'recnd', '( %s -> %s e. CC )' % (bj, BODY('j'))), cj], 'fsump1', '%s = ( %s + %s )' % (RH('( k + 1 )'), RH('k'), BODY('( k + 1 )')))
    # assemble
    l0 = LH('k')
    lbr = st([finB, nb['tr']], 'fsumrecl', 'sum_ n e. %s %s e. RR' % (RB, TERM))
    l0r = st([fk['fin'], c.nfacts(R0)['tr']], 'fsumrecl', '%s e. RR' % l0)
    rhk = RH('k')
    finj = st([], 'fzfid', '( 0 ... k ) e. Fin')
    bjk = '( %s /\\ j e. ( 0 ... k ) )' % a
    jnk = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... k ) )' % bjk), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % bjk)
    cjk = Ctx(w, bjk, lift(w, phs, bjk))
    fjk = cjk.jfacts('j', jnk)
    nfjk = cjk.nfacts('( 1 ... %s )' % NS('j'))
    sjkr = cjk.st([fjk['fin'], nfjk['ar']], 'fsumrecl', '%s e. RR' % SA('j'))
    bjkr = cjk.st([cjk.st([cjk.st([cjk.st([jnk], 'nn0red', 'j e. RR')], 'renegcld', '-u j e. RR')], 'reefcld', '( exp ` -u j ) e. RR'), sjkr], 'remulcld',
                  '%s e. RR' % BODY('j'))
    rhkr = st([finj, bjkr], 'fsumrecl', '%s e. RR' % rhk)
    SB = 'sum_ n e. %s A' % RB
    lv = {l0: l0r, 'sum_ n e. %s %s' % (RB, TERM): lbr, rhk: rhkr, LH('( k + 1 )'): st([fk1['fin'], nf1['tr']], 'fsumrecl', '%s e. RR' % LH('( k + 1 )')),
          RH('( k + 1 )'): st([st([], 'fzfid', '( 0 ... ( k + 1 ) ) e. Fin'), bjr], 'fsumrecl', '%s e. RR' % RH('( k + 1 )')),
          '( %s x. %s )' % (E1, SB): st([e1ra, sbr], 'remulcld', '( %s x. %s ) e. RR' % (E1, SB)),
          BODY('( k + 1 )'): st([e1ra, s1r], 'remulcld', '%s e. RR' % BODY('( k + 1 )'))}
    L_ = lambda x: lift(w, x, aI)
    stepc = linarith(w, aI, [L_(sp), ih, L_(blk2), L_(blk3), L_(p1)], PJ('( k + 1 )'), leaves={k_: L_(v_) for k_, v_ in lv.items()})
    # ---- induction
    ci = pcongr(w, '0', 'i'); cy = pcongr(w, 'k', 'i'); cs = pcongr(w, '( k + 1 )', 'i'); cJ = pcongr(w, 'J', 'i')
    w.qed([ci, cy, cs, cJ, base, stepc], 'nn0indd', STATEMENTS['zdblocks'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['zdblocks']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
