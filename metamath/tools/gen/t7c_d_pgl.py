"""T7c: the loop of Lean's ` primeGoF ` at the machine (T7b-HANDOFF item 3):
~ tm2fpg at the families of T7c-blueprint section 3, on TMIpg.

  tmipgi1   per iteration: the loop test ( carry ), the classes, the compare triple
  tmipgi2   per iteration: the modulo triple
  tmipgi3   per iteration, in the continue case: the step triple and the continue load
  tmipgi4   per iteration: the dispatch (the two early exits and the continue case)
  tmipgt    the typings over ( 0 ... R ) , the exit test, the prologue
  tmipgl    ~ tm2fpg assembled ( P' a letter under P' = PDF )
  tmipgr    the R-form: the families evaluated at 0 and R

    MM_DB=sorties/t7c.mm python3 tools/gen/t7c_d_pgl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7clib import *
from cl import Closure
import lin
from lin import linarith, lineq, nlinarith
from t7b_h_dmq import rab_elim
from t7_e_cmp import lamty

lin.FASTPATH = True
SEL = sys.argv[1:]

PG_ = FRAGS['pg']
LM = PG_.lmap()
LB = FRAGS['pgb'].lmap(PL('P', 3), PL('P', 1))
TB = '( TMB ` N )'
PGV = '( ( F PrimeGo G ) ` H )'
QV = '( 1st ` %s )' % PGV
RV = '( 2nd ` %s )' % PGV
GR1 = '( G + ( R - 1 ) )'
EARLY = '( 0 < R /\\ ( F < ( %s x. %s ) \\/ ( F mod %s ) = 0 ) )' % (GR1, GR1, GR1)
SV = 'if ( %s , ( R - 1 ) , R )' % EARLY
CI = lambda t: 'if ( %s < R , %s , S )' % (t, t)
def NCOND(h, t):
    return '( ( TMcar ` %s ) = if ( %s < R , 1o , (/) ) /\\ ( %s = R -> ( TMfl ` %s ) = %s ) )' % (h, t, t, h, QV)
def N1COND(h, t):
    return '( TMcmp ` %s ) = ( F Ncmp ( ( G + %s ) x. ( G + %s ) ) )' % (h, t, t)
def N2COND(h, t):
    return '( TMfl ` %s ) = if ( ( F mod ( G + %s ) ) = 0 , 1o , (/) )' % (h, t)
def N0COND(h, t):
    return '( TMfl ` %s ) = if ( ( H - ( %s + 1 ) ) = 0 , 1o , (/) )' % (h, t)
FAMF = lambda cond: '( j e. NN0 |-> { h e. TMSt | %s } )' % cond('h', 'j')
RAB = lambda cond, t: '{ h e. TMSt | %s }' % cond('h', t)
NF, N1F, N2F, N0F = FAMF(NCOND), FAMF(N1COND), FAMF(N2COND), FAMF(N0COND)
def PB(t):
    return UP(UP('D', 'J', EW('( G + %s )' % CI(t), 'Y')), 'I', EW('( H - %s )' % CI(t), 'Z'))
PDF = '( j e. NN0 |-> %s )' % PB('j')
PV = "P'"
OP = '{ h e. TMSt | ( TMfl ` h ) = if ( H = 0 , 1o , (/) ) }'
CLT = '( u e. TMSt |-> if ( ( TMcmp ` u ) = (/) , 1o , (/) ) )'
NOTFL = 'if ( ( TMfl ` u ) = 1o , (/) , 1o )'
L_TT = LSET(car='(/)', fl='1o')
L_FF = LSET(car='(/)', fl='(/)')
L_NF = LSET(car=NOTFL, fl='1o')
T15 = '( 5 x. %s )' % TB
T3_ = '( 3 x. %s )' % TB

GMAP = {'P0': LM['P0'], 'P1': LM['P1'], 'A': LM['A'], 'E': 'E', 'B0': FRAGS['pgb'].entry(PL('P', 3)),
        "B'": LB["B'"], 'B"': LB['B"'], "E'": LB["E'"], 'E"': LB['E"'], "A'": LB["A'"], 'E0': LB['E0'], 'A0': LB['A0'],
        'C': CLT, 'L': L_TT, "C'": 'TMfl', "L'": L_FF, 'L"': L_NF, 'C0': 'TMcar', 'L0': L_NF,
        'N': NF, 'N1': N1F, 'N"': N2F, 'N0': N0F, 'P': PV, 'R': 'R', 'T1': T15, 'T"': T15, 'T0': T3_, 'U': TB,
        'O': '( 2nd ` T )', "O'": OP}

NUMS_L = (('F e. NN0', 'G e. NN', 'H e. NN0'), ('N e. NN0', 'F < ( 2 ^ N )', '( G + H ) < ( 2 ^ N )'))
RS_L = ('R = %s' % RV, 'S = %s' % SV, 'E e. ( 2nd ` ( 1st ` T ) )')
WDS_L = ((WRD('X', GAM), WRD('Y', GAM), WRD('Z', GAM)), (STKD('D'), '%s = %s' % (PV, PDF)),
         ('( D ` K ) = %s' % EW('F', 'X'), '( D ` J ) = %s' % EW('G', 'Y'), '( D ` I ) = %s' % EW('H', 'Z')))
T_L = ((T_PHM7, PG_.pred()), (idx_tree(K6), dist_tree(K6)), (NUMS_L, RS_L, WDS_L))
PHL = cj(T_L)
PSI = '( %s /\\ i e. ( 0 ..^ R ) )' % PHL

_A, _C = split_imp(stmt('tm2fpg'))
GTREE = tsub(parse_conj(_A), GMAP)
GCONCL = tsub_text(_C, GMAP)
PER = GTREE[1][1][1]
assert PER.startswith('A. i e. ( 0 ..^ R ) ')
BODY = parse_conj(PER[len('A. i e. ( 0 ..^ R ) '):])
# BODY = ( ( HT , classes ) , ( TRIPLE1 , DISJ ) )
HT0, CLS0 = BODY[0]
TRI1, DISJ = BODY[1]


class Lp:
    """facts under ps (the loop antecedent, possibly with i e. ( 0 ..^ R ) and more)"""
    def __init__(self, w, ps, c_root=None, lift=None, tree=None, root=None, pv=None):
        self.w, self.ps = w, ps
        self.PV = pv or PV
        tree = tree or T_L
        if root is None and ps != cj(tree):
            root = w.s([], lift or "simpl", "( %s -> %s )" % (ps, cj(tree)))
        self.c = c = Ctx(w, ps, tree, root=root)
        self.mk = machine(w, ps, c, K6)
        self.ne = ne_fn(w, ps, c, set(flat(dist_tree(K6))))
        mk = self.mk
        self.base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
        self.base.update(unfold_all(w, ps, c[PG_.pred()], 'pg', K6, 'P', 'E', rec=False))
        for s_ in K6:
            self.base['%s e. %s' % (s_, DG)] = mk['k'][s_]['kd']
        for i_, a in enumerate(K6):
            for b in K6[i_ + 1:]:
                self.base['%s =/= %s' % (a, b)] = self.ne(a, b)
                self.base['%s =/= %s' % (b, a)] = self.ne(b, a)
        self.fn, self.gnn, self.hn, self.nn = c['F e. NN0'], c['G e. NN'], c['H e. NN0'], c['N e. NN0']
        self.gn = w.s([self.gnn], 'nnnn0d', '( %s -> G e. NN0 )' % ps)
        # R and its bounds
        j3 = w.s([self.fn, self.gn, self.hn], '3jca', '( %s -> ( F e. NN0 /\\ G e. NN0 /\\ H e. NN0 ) )' % ps)
        self.j3 = j3
        pc = w.s([w.s([self.fn, self.gn], 'jca', '( %s -> ( F e. NN0 /\\ G e. NN0 ) )' % ps), self.hn, w.inst('primegocl')],
                 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (ps, PGV))
        self.q2o = w.s([pc, w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (ps, QV))
        rv0 = w.s([pc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ps, RV))
        self.req = c['R = %s' % RV]
        self.rn = w.s([self.req, rv0], 'eqeltrd', '( %s -> R e. NN0 )' % ps)
        rle0 = w.s([j3, w.inst('tmipgle')], 'syl', '( %s -> %s <_ H )' % (ps, RV))
        self.rle = w.s([self.req, rle0], 'eqbrtrd', '( %s -> R <_ H )' % ps)
        self.cl = Closure(w, ps, {'F': ('NN0', self.fn), 'G': ('NN', self.gnn), 'H': ('NN0', self.hn), 'N': ('NN0', self.nn),
                                  'R': ('NN0', self.rn)})
        self.memo = {}

    def L(self, st, ps2):
        return self.w.s([st], 'adantr', '( %s -> %s )' % (ps2, concl(self.w, self.ps, st)))

    def sfacts(self):
        """S e. NN0 , S <_ R"""
        if 'sn' in self.memo:
            return self.memo['sn'], self.memo['sle']
        w, ps, cl = self.w, self.ps, self.cl
        seq = self.c['S = %s' % SV]
        # case EARLY : S = R - 1 with 0 < R ; else S = R
        A1 = '( %s /\\ %s )' % (ps, EARLY)
        A2 = '( %s /\\ -. %s )' % (ps, EARLY)
        e1 = w.s([w.s([seq], 'adantr', '( %s -> S = %s )' % (A1, SV)), w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, EARLY))], 'iftrued',
                  '( %s -> %s = ( R - 1 ) )' % (A1, SV))], 'eqtrd', '( %s -> S = ( R - 1 ) )' % A1)
        rp = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, EARLY))], 'simpld', '( %s -> 0 < R )' % A1)
        rn1 = w.s([self.rn], 'adantr', '( %s -> R e. NN0 )' % A1)
        rnn = w.s([rn1, rp, w.inst('elnnnn0b') if False else w.inst('nn0p1gt0') if False else w.inst('elnnnn0c') if False else w.inst('nnne0') if False else w.inst('elnn0nn') if False else w.inst('elnnne0') if False else w.inst('nngt0')], 'syl', '') if False else None
        rnn = w.s([w.s([rn1, rp], 'jca', '( %s -> ( R e. NN0 /\\ 0 < R ) )' % A1), w.inst('elnnnn0b')], 'sylibr', '( %s -> R e. NN )' % A1)
        rm1 = w.s([rnn, w.inst('nnm1nn0')], 'syl', '( %s -> ( R - 1 ) e. NN0 )' % A1)
        s1 = w.s([e1, rm1], 'eqeltrd', '( %s -> S e. NN0 )' % A1)
        cl1 = Closure(w, A1, {'R': ('NN0', rn1), 'S': ('NN0', s1)})
        le1 = linarith(w, A1, [e1], 'S <_ R', closure=cl1)
        e2 = w.s([w.s([seq], 'adantr', '( %s -> S = %s )' % (A2, SV)), w.s([w.s([], 'simpr', '( %s -> -. %s )' % (A2, EARLY))], 'iffalsed',
                  '( %s -> %s = R )' % (A2, SV))], 'eqtrd', '( %s -> S = R )' % A2)
        rn2 = w.s([self.rn], 'adantr', '( %s -> R e. NN0 )' % A2)
        s2 = w.s([e2, rn2], 'eqeltrd', '( %s -> S e. NN0 )' % A2)
        le2 = w.s([e2, w.s([w.s([rn2], 'nn0red', '( %s -> R e. RR )' % A2)], 'leidd', '( %s -> R <_ R )' % A2)], 'eqbrtrd', '( %s -> S <_ R )' % A2)
        sn = w.s([s1, s2], 'pm2.61dan', '( %s -> S e. NN0 )' % ps)
        sle = w.s([le1, le2], 'pm2.61dan', '( %s -> S <_ R )' % ps)
        self.memo['sn'], self.memo['sle'] = sn, sle
        cl.leaf('S', 'NN0', sn)
        return sn, sle

    def ci(self, t, tn, tle):
        """( ps -> CI( t ) e. NN0 ) and ( ps -> CI( t ) <_ R ) for t e. NN0 , t <_ R"""
        key = ('ci', t)
        if key in self.memo:
            return self.memo[key]
        w, ps = self.w, self.ps
        sn, sle = self.sfacts()
        c1 = w.s([tn, sn], 'ifcld', '( %s -> %s e. NN0 )' % (ps, CI(t)))
        tr = w.s([tn], 'nn0red', '( %s -> %s e. RR )' % (ps, t))
        sr = w.s([sn], 'nn0red', '( %s -> S e. RR )' % ps)
        rr = w.s([self.rn], 'nn0red', '( %s -> R e. RR )' % ps)
        # if ( t < R , t , S ) <_ R : both branches <_ R
        b = w.s([tle, sle], 'jca', '( %s -> ( %s <_ R /\\ S <_ R ) )' % (ps, t))
        c2 = w.s([b, w.inst('ifboth') if False else w.inst('ifle')], 'syl', '') if False else None
        # by cases on t < R
        A1 = '( %s /\\ %s < R )' % (ps, t)
        A2 = '( %s /\\ -. %s < R )' % (ps, t)
        i1 = w.s([w.s([], 'simpr', '( %s -> %s < R )' % (A1, t))], 'iftrued', '( %s -> %s = %s )' % (A1, CI(t), t))
        i2 = w.s([w.s([], 'simpr', '( %s -> -. %s < R )' % (A2, t))], 'iffalsed', '( %s -> %s = S )' % (A2, CI(t)))
        l1 = w.s([i1, w.s([tle], 'adantr', '( %s -> %s <_ R )' % (A1, t))], 'eqbrtrd', '( %s -> %s <_ R )' % (A1, CI(t)))
        l2 = w.s([i2, w.s([sle], 'adantr', '( %s -> S <_ R )' % A2)], 'eqbrtrd', '( %s -> %s <_ R )' % (A2, CI(t)))
        c2 = w.s([l1, l2], 'pm2.61dan', '( %s -> %s <_ R )' % (ps, CI(t)))
        self.memo[key] = (c1, c2)
        return c1, c2

    def pv(self, t, tn, tle):
        """the stacks at t : ( ps -> ( P' ` t ) = PB( t ) ), the Stacks object of PB( t ), with the values at
        K , J , I"""
        key = ('pv', t)
        if key in self.memo:
            return self.memo[key]
        w, ps, c, cl = self.w, self.ps, self.c, self.cl
        cin, cle = self.ci(t, tn, tle)
        GC, HC = '( G + %s )' % CI(t), '( H - %s )' % CI(t)
        gcn = w.s([self.gn, cin], 'nn0addcld', '( %s -> %s e. NN0 )' % (ps, GC))
        hcle = w.s([cle, self.rle], 'letrd' if False else 'jca', '') if False else None
        cl.leaf(CI(t), 'NN0', cin)
        hcl = linarith(w, ps, [cle, self.rle], '%s <_ H' % CI(t), closure=cl)
        hcn = w.s([cin, self.hn, hcl, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ps, HC))
        dd = c[STKD('D')]
        vals = {'K': (EW('F', 'X'), c['( D ` K ) = %s' % EW('F', 'X')], ewg(w, ps, 'F', self.fn, 'X', c[WRD('X', GAM)]))}
        for s_ in ["I'", 'I"', 'I0']:
            vals[s_] = selfval(w, ps, self.mk, 'D', dd, s_)
        S = Stacks(w, ps, self.mk, 'D', dd, self.ne, vals)
        S = S.upd('J', EW(GC, 'Y'), ewg(w, ps, GC, gcn, 'Y', c[WRD('Y', GAM)]))
        S = S.upd('I', EW(HC, 'Z'), ewg(w, ps, HC, hcn, 'Z', c[WRD('Z', GAM)]))
        assert S.D == PB(t), (S.D, PB(t))
        pv0 = mval(w, ps, 'j', 'NN0', PB, t, tn, w.s([S.memb], 'elexd', '( %s -> %s e. _V )' % (ps, PB(t))))
        pe = w.s([c["%s = %s" % (self.PV, PDF)]], "fveq1d", "( %s -> ( %s ` %s ) = ( %s ` %s ) )" % (ps, self.PV, t, PDF, t))
        pvs = w.s([pe, pv0], "eqtrd", "( %s -> ( %s ` %s ) = %s )" % (ps, self.PV, t, PB(t)))
        self.memo[key] = (pvs, S, gcn, hcn)
        return self.memo[key]

    def pvals(self, t, tn, tle):
        """( ps -> ( P' ` t ) e. Stk ) and the three value equations at ( P' ` t ) , and the Stacks on ( P' ` t )"""
        key = ('pvals', t)
        if key in self.memo:
            return self.memo[key]
        w, ps = self.w, self.ps
        pvs, S, gcn, hcn = self.pv(t, tn, tle)
        PT = '( %s ` %s )' % (self.PV, t)
        mem = w.s([pvs, S.memb], 'eqeltrd', '( %s -> %s e. %s )' % (ps, PT, STK_T))
        out = {}
        for s_ in K6:
            txt, st, g = S.vals[s_]
            e = w.s([pvs], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, PT, s_, S.D, s_))
            out[s_] = (txt, w.s([e, st], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PT, s_, txt)), g)
        SP = Stacks(w, ps, self.mk, PT, mem, self.ne, out)
        self.memo[key] = (mem, SP)
        return mem, SP

    def famv(self, cond, t, tn):
        """( ps -> ( FAM ` t ) = RAB( t ) )"""
        return famval(self.w, self.ps, cond, t, tn)

    def famss(self, cond, t, tn):
        """( ps -> ( FAM ` t ) C_ ( 2nd ` T ) )"""
        w, ps = self.w, self.ps
        fv = self.famv(cond, t, tn)
        ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % RAB(cond, t))], 'a1i', '( %s -> %s C_ TMSt )' % (ps, RAB(cond, t)))
        s2 = w.s([ss, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, RAB(cond, t)))
        return w.s([fv, s2], 'eqsstrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, '( %s ` %s )' % (FAMF(cond), t)))


def iter_ctx(w):
    """Lp at ps = ( PHL /\\ i e. ( 0 ..^ R ) ) with i-facts"""
    lp = Lp(w, PSI)
    ps = PSI
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ R ) )' % ps)
    lp.inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    lp.ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ps)
    lp.ile = w.s([lp.ilt], 'ltled', '( %s -> i <_ R )' % ps)
    lp.cl.leaf('i', 'NN0', lp.inn)
    lp.i1n = w.s([lp.inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ps)
    zl = w.s([lp.cl.mem('i', 'ZZ'), lp.cl.mem('R', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < R <-> ( i + 1 ) <_ R ) )' % ps)
    lp.i1le = w.s([lp.ilt, zl], 'mpbid', '( %s -> ( i + 1 ) <_ R )' % ps)
    # c(i) = i
    lp.cii = w.s([lp.ilt], 'iftrued', '( %s -> %s = i )' % (ps, CI('i')))
    # G + i , H - i
    lp.gi = '( G + i )'
    lp.gin = w.s([lp.gnn, lp.inn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( G + i ) e. NN )' % ps)
    lp.gin0 = w.s([lp.gin], 'nnnn0d', '( %s -> ( G + i ) e. NN0 )' % ps)
    return lp


def stack_i(w, lp):
    """the stacks ( P' ` i ) with the values at J , I simplified by c( i ) = i"""
    ps = lp.ps
    mem, SP = lp.pvals('i', lp.inn, lp.ile)
    vals = dict(SP.vals)
    for s_, (A, B) in [('J', ('( G + %s )' % CI('i'), '( G + i )')), ('I', ('( H - %s )' % CI('i'), '( H - i )'))]:
        txt, st, g = vals[s_]
        e = w.s([lp.cii], 'oveq2d', '( %s -> %s = %s )' % (ps, A, B))
        e2 = w.s([w.s([e], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` %s ) )' % (ps, A, B))], 'oveq1d',
                 '( %s -> %s = %s )' % (ps, txt, EW(B, 'Y' if s_ == 'J' else 'Z')))
        nt = EW(B, 'Y' if s_ == 'J' else 'Z')
        st2 = w.s([st, e2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, SP.D, s_, nt))
        g2 = w.s([e2, g], 'eqeltrrd', "( %s -> %s e. Word Gamma' )" % (ps, nt))
        vals[s_] = (nt, st2, g2)
    return mem, Stacks(w, ps, lp.mk, SP.D, mem, lp.ne, vals)


def tmipgi1():
    lab = 'tmipgi1'
    C = '( %s -> ( %s /\\ %s ) )' % (PSI, cj(BODY[0]), TRI1)
    w = W(lab, 'One iteration of Lean\'s ` primeGoF ` loop at the machine ( ` PGInv ` at ` i < primeIters ` ): the loop '
               'test ` carry ` holds, the intermediate classes are classes of states, and the compare run of '
               '` primeGoBody ` (~ tmipgt1 at the divisor ` G + i ` ) goes from the invariant\'s class to the class of '
               '` compare m ( ( G + i ) x. ( G + i ) ) ` , the stacks ` ( P\' ` i ) ` kept.')
    lp = iter_ctx(w)
    ps, cl = lp.ps, lp.cl
    # HT : A. m e. ( NF ` i ) ( TMcar ` m ) = 1o
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, NF)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCOND, 'i', Lm(lp.inn), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, NF)))
    car = w.s([mc], 'simpld', '( %s -> ( TMcar ` m ) = if ( i < R , 1o , (/) ) )' % pm)
    it = w.s([Lm(lp.ilt)], 'iftrued', '( %s -> if ( i < R , 1o , (/) ) = 1o )' % pm)
    ht = w.s([w.s([car, it], 'eqtrd', '( %s -> ( TMcar ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> %s )' % (ps, HT0))
    # the classes
    c1 = lp.famss(N1COND, 'i', lp.inn)
    c2 = lp.famss(N2COND, 'i', lp.inn)
    c3 = lp.famss(N0COND, 'i', lp.inn)
    cls = w.s([c1, c2, c3], '3jca', '( %s -> %s )' % (ps, CLS0 if isinstance(CLS0, str) else cj(CLS0)))
    b0 = w.s([ht, cls], 'jca', '( %s -> %s )' % (ps, cj(BODY[0])))
    # the compare triple
    mem, SP = stack_i(w, lp)
    gilt = linarith(w, ps, [lp.ilt, lp.rle, lp.c['( G + H ) < ( 2 ^ N )']], '( G + i ) < ( 2 ^ N )', closure=cl, atoms=['( 2 ^ N )'])
    PT = "( P' ` i )"
    ex = dict(lp.base)
    ex.update({'( G + i ) e. NN0': lp.gin0, '( G + i ) < ( 2 ^ N )': gilt, STKD(PT): mem,
               '( %s ` K ) = %s' % (PT, EW('F', 'X')): SP.vals['K'][1], '( %s ` J ) = %s' % (PT, EW('( G + i )', 'Y')): SP.vals['J'][1]})
    t, cc = inst(w, ps, 'tmipgt1', {'P': PL('P', 3), 'E': PL('P', 1), 'G': '( G + i )', 'D': PT}, Bld(w, ps, lp.c, ex))
    Ca, Da, n = triple_parts(cc)
    nss = lp.famss(NCOND, 'i', lp.inn)
    B0 = GMAP['B0']
    t2 = hrssc(w, ps, lp.mk['phm'], t, Ca, Da, n, CLN(B0, '( %s ` i )' % NF, PT), clnss(w, ps, B0, '( %s ` i )' % NF, SS, PT, nss))
    fv1 = lp.famv(N1COND, 'i', lp.inn)
    e = clnneq(w, ps, GMAP["B'"], w.s([fv1], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, RAB(N1COND, 'i'), N1F)), RAB(N1COND, 'i'),
               '( %s ` i )' % N1F, PT)
    t3, C3, D3, n3 = hrrw(w, ps, t2, CLN(B0, '( %s ` i )' % NF, PT), Da, n, deq=e)
    assert '( %s -> %s )' % (ps, HR(C3, 'T', 'M', D3, n3)) == '( %s -> %s )' % (ps, TRI1), (HR(C3, 'T', 'M', D3, n3), TRI1)
    w.qed([b0, t3], 'jca', C)
    return w.run()


from t6blib import _split_top, _outer
DA, DB = _split_top(_outer(DISJ), '\\/')
HT1, HLD1, PEQ = parse_conj(DA)
HTF1, TRI2, DISJ2 = parse_conj(DB)
DA2, DB2 = _split_top(_outer(DISJ2), '\\/')
HT2, HLD2, PEQ2 = parse_conj(DA2)
HTF2, TRI3, HLD3 = parse_conj(DB2)
assert PEQ == PEQ2
GI, HI = '( G + i )', '( H - i )'
LTI = 'F < ( %s x. %s )' % (GI, GI)
DVI = '( F mod %s ) = 0' % GI
PSI3 = '( %s /\\ ( -. %s /\\ -. %s ) )' % (PSI, LTI, DVI)


def tmipgi2():
    lab = 'tmipgi2'
    C = '( %s -> %s )' % (PSI, TRI2)
    w = W(lab, 'One iteration of Lean\'s ` primeGoF ` loop at the machine: the modulo run of ` primeGoBody ` '
               '(~ tmipgt2 at the divisor ` G + i ` ) goes from the compare class to the class of '
               '` flag = [ m mod ( G + i ) = 0 ] ` , the stacks ` ( P\' ` i ) ` kept.')
    lp = iter_ctx(w)
    ps, cl = lp.ps, lp.cl
    mem, SP = stack_i(w, lp)
    gilt = linarith(w, ps, [lp.ilt, lp.rle, lp.c['( G + H ) < ( 2 ^ N )']], '( G + i ) < ( 2 ^ N )', closure=cl, atoms=['( 2 ^ N )'])
    PT = "( P' ` i )"
    ex = dict(lp.base)
    ex.update({'( G + i ) e. NN': lp.gin, '( G + i ) < ( 2 ^ N )': gilt, STKD(PT): mem,
               '( %s ` K ) = %s' % (PT, EW('F', 'X')): SP.vals['K'][1], '( %s ` J ) = %s' % (PT, EW('( G + i )', 'Y')): SP.vals['J'][1]})
    t, cc = inst(w, ps, 'tmipgt2', {'P': PL('P', 3), 'E': PL('P', 1), 'G': '( G + i )', 'D': PT}, Bld(w, ps, lp.c, ex))
    Ca, Da, n = triple_parts(cc)
    nss = lp.famss(N1COND, 'i', lp.inn)
    E0 = GMAP['E0']
    t2 = hrssc(w, ps, lp.mk['phm'], t, Ca, Da, n, CLN(E0, '( %s ` i )' % N1F, PT), clnss(w, ps, E0, '( %s ` i )' % N1F, SS, PT, nss))
    fv2 = lp.famv(N2COND, 'i', lp.inn)
    e = clnneq(w, ps, GMAP["E'"], w.s([fv2], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, RAB(N2COND, 'i'), N2F)), RAB(N2COND, 'i'),
               '( %s ` i )' % N2F, PT)
    t3, C3, D3, n3 = hrrw(w, ps, t2, CLN(E0, '( %s ` i )' % N1F, PT), Da, n, deq=e, qed=True)
    assert HR(C3, 'T', 'M', D3, n3) == TRI2, (HR(C3, 'T', 'M', D3, n3), TRI2)
    return w.run()


def pgit(w, lp, ps, inn, ilt):
    """tmipgit at I := i with R and Q: returns the three implications (as steps under ps)"""
    ilt0 = w.s([ilt, lp.req], 'breqtrd', '( %s -> i < %s )' % (ps, RV))
    j = w.s([lp.j3, w.s([inn, ilt0], 'jca', '( %s -> ( i e. NN0 /\\ i < %s ) )' % (ps, RV))], 'jca',
            '( %s -> ( ( F e. NN0 /\\ G e. NN0 /\\ H e. NN0 ) /\\ ( i e. NN0 /\\ i < %s ) ) )' % (ps, RV))
    I1 = '( i + 1 )'
    HI1 = '( H - %s )' % I1
    DD = '( %s x. %s )' % (GI, GI)
    c1 = '( F < %s -> ( %s = %s /\\ %s = 1o ) )' % (DD, RV, I1, QV)
    c2 = '( ( -. F < %s /\\ ( F mod %s ) = 0 ) -> ( %s = %s /\\ %s = (/) ) )' % (DD, GI, RV, I1, QV)
    c3 = ('( ( -. F < %s /\\ -. ( F mod %s ) = 0 ) -> ( ( %s < %s <-> -. %s = 0 ) /\\ ( %s = 0 -> ( %s = %s /\\ %s = 1o ) ) ) )'
          % (DD, GI, I1, RV, HI1, HI1, RV, I1, QV))
    it = w.s([j, w.inst('tmipgit')], 'syl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ps, c1, c2, c3))
    return (w.s([it, w.inst('simp1')], 'syl', '( %s -> %s )' % (ps, c1)),
            w.s([it, w.inst('simp2')], 'syl', '( %s -> %s )' % (ps, c2)),
            w.s([it, w.inst('simp3')], 'syl', '( %s -> %s )' % (ps, c3)))


def tmipgi3():
    lab = 'tmipgi3'
    C = '( %s -> ( %s /\\ %s ) )' % (PSI3, TRI3, HLD3)
    w = W(lab, 'One iteration of Lean\'s ` primeGoF ` loop at the machine, the continue case ( ` m ` is not below '
               '` ( G + i ) ^ 2 ` and not divisible by ` G + i ` ): the step run of ` primeGoBody ` (~ tmipgt3 ) '
               'takes the stacks from ` ( P\' ` i ) ` to ` ( P\' ` ( i + 1 ) ) ` , and the load '
               '` carry := !flag , flag := true ` lands in the invariant\'s class at ` i + 1 ` (Lean '
               '` primeIters_succ_next ` ).')
    lp = Lp(w, PSI3, lift='simpll')
    ps = PSI3
    lp_ps = lp
    # i facts under PSI3
    ii = w.s([], 'simplr', '( %s -> i e. ( 0 ..^ R ) )' % ps)
    lp.inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    lp.ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ps)
    lp.ile = w.s([lp.ilt], 'ltled', '( %s -> i <_ R )' % ps)
    cl = lp.cl
    cl.leaf('i', 'NN0', lp.inn)
    lp.i1n = w.s([lp.inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ps)
    zl = w.s([cl.mem('i', 'ZZ'), cl.mem('R', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < R <-> ( i + 1 ) <_ R ) )' % ps)
    lp.i1le = w.s([lp.ilt, zl], 'mpbid', '( %s -> ( i + 1 ) <_ R )' % ps)
    lp.cii = w.s([lp.ilt], 'iftrued', '( %s -> %s = i )' % (ps, CI('i')))
    lp.gin = w.s([lp.gnn, lp.inn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( G + i ) e. NN )' % ps)
    lp.gin0 = w.s([lp.gin], 'nnnn0d', '( %s -> ( G + i ) e. NN0 )' % ps)
    nlt = w.s([], 'simprl', '( %s -> -. %s )' % (ps, LTI))
    ndv = w.s([], 'simprr', '( %s -> -. %s )' % (ps, DVI))
    # c( i + 1 ) = i + 1
    I1 = '( i + 1 )'
    A1 = '( %s /\\ %s < R )' % (ps, I1)
    A2 = '( %s /\\ -. %s < R )' % (ps, I1)
    ca = w.s([w.s([], 'simpr', '( %s -> %s < R )' % (A1, I1))], 'iftrued', '( %s -> %s = %s )' % (A1, CI(I1), I1))
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ps, st)))
    cl2 = Closure(w, A2, {'i': ('NN0', L2(lp.inn)), 'R': ('NN0', L2(lp.rn))})
    nl2 = w.s([], 'simpr', '( %s -> -. %s < R )' % (A2, I1))
    ler = w.s([cl2.mem('R', 'RR'), cl2.mem(I1, 'RR')], 'lenltd', '( %s -> ( R <_ %s <-> -. %s < R ) )' % (A2, I1, I1))
    rle2 = w.s([ler, nl2], 'mpbird', '( %s -> R <_ %s )' % (A2, I1))
    req2 = w.s([cl2.mem(I1, 'RR'), cl2.mem('R', 'RR'), L2(lp.i1le), rle2, w.inst('letri3d') if False else w.inst('eqle') if False else w.inst('letri3')], 'syl2anc', '') if False else None
    ri1 = linarith(w, A2, [L2(lp.i1le), rle2], 'R <_ %s' % I1, closure=cl2)
    rmi = lineq(w, A2, '( R - 1 )', 'i', hyps=[L2(lp.i1le), rle2], closure=cl2)
    # EARLY is false at R - 1 = i
    ew, EW2 = w.wcongr(EARLY, {}, A2, {}, rules={'( R - 1 )': ('i', rmi)})
    assert EW2 == '( 0 < R /\\ ( %s \\/ %s ) )' % (LTI, DVI), EW2
    nor = w.s([L2(nlt), L2(ndv)], 'ioran' if False else 'jca', '( %s -> ( -. %s /\\ -. %s ) )' % (A2, LTI, DVI))
    nor2 = w.s([nor, w.inst('ioran')], 'sylibr', '( %s -> -. ( %s \\/ %s ) )' % (A2, LTI, DVI))
    nea = w.s([nor2], 'intnand', '( %s -> -. %s )' % (A2, EW2))
    ne2 = w.s([ew, nea], 'mtbird', '( %s -> -. %s )' % (A2, EARLY))
    sr = w.s([L2(lp.c['S = %s' % SV]), w.s([ne2], 'iffalsed', '( %s -> %s = R )' % (A2, SV))], 'eqtrd', '( %s -> S = R )' % A2)
    rieq = lineq(w, A2, 'R', I1, hyps=[L2(lp.i1le), rle2], closure=cl2)
    cb = w.s([w.s([nl2], 'iffalsed', '( %s -> %s = S )' % (A2, CI(I1))), w.s([sr, rieq], 'eqtrd', '( %s -> S = %s )' % (A2, I1))], 'eqtrd',
             '( %s -> %s = %s )' % (A2, CI(I1), I1))
    ci1 = w.s([ca, cb], 'pm2.61dan', '( %s -> %s = %s )' % (ps, CI(I1), I1))
    # the step triple
    mem, SP = stack_i(w, lp)
    gilt = linarith(w, ps, [lp.ilt, lp.rle, lp.c['( G + H ) < ( 2 ^ N )']], '( G + i ) < ( 2 ^ N )', closure=cl, atoms=['( 2 ^ N )'])
    hin = w.s([cl.mem('i', 'ZZ'), cl.mem('H', 'ZZ'), w.inst('znnsub')], 'syl2anc', '( %s -> ( i < H <-> ( H - i ) e. NN ) )' % ps)
    ilh = linarith(w, ps, [lp.ilt, lp.rle], 'i < H', closure=cl)
    hinn = w.s([ilh, hin], 'mpbid', '( %s -> ( H - i ) e. NN )' % ps)
    hilt = linarith(w, ps, [lp.c['( G + H ) < ( 2 ^ N )'], cl.ge0('i'), cl.ge0('G')], '( H - i ) < ( 2 ^ N )', closure=cl, atoms=['( 2 ^ N )'])
    PT = "( P' ` i )"
    ex = dict(lp.base)
    ex.update({'( G + i ) e. NN0': lp.gin0, '( H - i ) e. NN': hinn, '( G + i ) < ( 2 ^ N )': gilt, '( H - i ) < ( 2 ^ N )': hilt,
               STKD(PT): mem, '( %s ` J ) = %s' % (PT, EW(GI, 'Y')): SP.vals['J'][1], '( %s ` I ) = %s' % (PT, EW(HI, 'Z')): SP.vals['I'][1]})
    t, cc = inst(w, ps, 'tmipgt3', {'P': PL('P', 3), 'E': PL('P', 1), 'G': GI, 'H': HI, 'D': PT}, Bld(w, ps, lp.c, ex))
    Ca, Da, n = triple_parts(cc)
    nss = lp.famss(N2COND, 'i', lp.inn)
    A0 = GMAP['A0']
    t2 = hrssc(w, ps, lp.mk['phm'], t, Ca, Da, n, CLN(A0, '( %s ` i )' % N2F, PT), clnss(w, ps, A0, '( %s ` i )' % N2F, SS, PT, nss))
    # the post class and stacks
    G1, H1 = '( %s + 1 )' % GI, '( %s - 1 )' % HI
    OLDC = '{ h e. TMSt | ( TMfl ` h ) = if ( %s = 0 , 1o , (/) ) }' % H1
    OLDD = UP(UP(PT, 'J', EW(G1, 'Y')), 'I', EW(H1, 'Z'))
    assert Da == CLN(GMAP["A'"], OLDC, OLDD), Da
    h1e = lineq(w, ps, H1, '( H - %s )' % I1, closure=cl)
    ce, cnew = w.rewrite(OLDC, {H1: ('( H - %s )' % I1, h1e)}, ps)
    assert cnew == RAB(N0COND, 'i'), cnew
    fv0 = lp.famv(N0COND, 'i', lp.inn)
    ce2 = w.s([ce, w.s([fv0], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, RAB(N0COND, 'i'), N0F))], 'eqtrd',
              '( %s -> %s = ( %s ` i ) )' % (ps, OLDC, N0F))
    # stacks : OLDD = ( P' ` ( i + 1 ) )
    pvi, Si, _, _ = lp.pv('i', lp.inn, lp.ile)
    r1, n1_ = w.rewrite(OLDD, {PT: (PB('i'), pvi)}, ps)
    a_, b_ = EW('( G + %s )' % CI('i'), 'Y'), EW('( H - %s )' % CI('i'), 'Z')
    togk = lambda X, s_, g: w.s([g, lp.mk['k'][s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s_)))
    gin1 = w.s([lp.gin0, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, G1))
    hin1 = w.s([hinn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, H1))
    ya = ewg(w, ps, G1, gin1, 'Y', lp.c[WRD('Y', GAM)])
    zb = ewg(w, ps, H1, hin1, 'Z', lp.c[WRD('Z', GAM)])
    dd = lp.c[STKD('D')]
    kJ, kI = lp.mk['k']['J'], lp.mk['k']['I']
    u4 = up4(w, ps, 'D', 'J', a_, 'I', b_, EW(G1, 'Y'), EW(H1, 'Z'), lp.mk['tv'], dd, lp.ne('J', 'I'), kJ['kd'],
             togk(a_, 'J', Si.vals['J'][2]), togk(EW(G1, 'Y'), 'J', ya), kI['kd'], togk(b_, 'I', Si.vals['I'][2]), togk(EW(H1, 'Z'), 'I', zb))
    NEWD = UP(UP('D', 'J', EW(G1, 'Y')), 'I', EW(H1, 'Z'))
    e1 = w.s([r1, u4], 'eqtrd', '( %s -> %s = %s )' % (ps, OLDD, NEWD))
    pv1, S1, _, _ = lp.pv(I1, lp.i1n, lp.i1le)
    g1e = w.s([w.s([ci1], 'oveq2d', '( %s -> ( G + %s ) = ( G + %s ) )' % (ps, CI(I1), I1)),
               w.s([cl.mem('G', 'CC'), cl.mem('i', 'CC'), closed(w, ps, 'ax-1cn', '1 e. CC'), w.inst('addassd') if False else w.inst('addass')], 'syl3anc',
                   '( %s -> ( ( G + i ) + 1 ) = ( G + ( i + 1 ) ) )' % ps)], 'eqtr4d', '( %s -> ( G + %s ) = %s )' % (ps, CI(I1), G1))
    h1f = w.s([w.s([ci1], 'oveq2d', '( %s -> ( H - %s ) = ( H - %s ) )' % (ps, CI(I1), I1)), w.s([h1e], 'eqcomd', '( %s -> ( H - %s ) = %s )' % (ps, I1, H1))],
              'eqtrd', '( %s -> ( H - %s ) = %s )' % (ps, CI(I1), H1))
    r2, n2_ = w.rewrite(PB(I1), {'( G + %s )' % CI(I1): (G1, g1e), '( H - %s )' % CI(I1): (H1, h1f)}, ps)
    assert n2_ == NEWD, n2_
    e2 = w.s([pv1, r2], 'eqtrd', "( %s -> ( %s ` %s ) = %s )" % (ps, PV, I1, NEWD))
    deq_s = w.s([e1, e2], 'eqtr4d', "( %s -> %s = ( %s ` %s ) )" % (ps, OLDD, PV, I1))
    POSTC = CLN(GMAP["A'"], '( %s ` i )' % N0F, '( %s ` %s )' % (PV, I1))
    d1 = clnneq(w, ps, GMAP["A'"], ce2, OLDC, '( %s ` i )' % N0F, OLDD)
    d2 = clneq(w, ps, GMAP["A'"], '( %s ` i )' % N0F, deq_s, OLDD, '( %s ` %s )' % (PV, I1))
    deq = w.s([d1, d2], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, POSTC))
    t3, C3, D3, n3 = hrrw(w, ps, t2, CLN(A0, '( %s ` i )' % N2F, PT), Da, n, deq=deq)
    assert HR(C3, 'T', 'M', D3, n3) == TRI3, (HR(C3, 'T', 'M', D3, n3), TRI3)
    # the continue load
    c1, c2, c3 = pgit(w, lp, ps, lp.inn, lp.ilt)
    j2 = w.s([nlt, ndv], 'jca', '( %s -> ( -. %s /\\ -. %s ) )' % (ps, LTI, DVI))
    HI1 = '( H - %s )' % I1
    k3 = w.s([j2, c3], 'mpd', '( %s -> ( ( %s < %s <-> -. %s = 0 ) /\\ ( %s = 0 -> ( %s = %s /\\ %s = 1o ) ) ) )' % (ps, I1, RV, HI1, HI1, RV, I1, QV))
    kb = w.s([k3], 'simpld', '( %s -> ( %s < %s <-> -. %s = 0 ) )' % (ps, I1, RV, HI1))
    kz = w.s([k3], 'simprd', '( %s -> ( %s = 0 -> ( %s = %s /\\ %s = 1o ) ) )' % (ps, HI1, RV, I1, QV))
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, N0F)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, N0COND, 'i', Lm(lp.inn), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, N0F)))
    nv = load_val(w, pm, lambda t: dict(car='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t, fl='1o'), 'm', mm,
                  clmap={'if ( ( TMfl ` m ) = 1o , (/) , 1o )': w.s([closed(w, pm, '0el2o', '(/) e. 2o'), closed(w, pm, '1oel2o', '1o e. 2o')],
                                                                    'ifcld', '( %s -> if ( ( TMfl ` m ) = 1o , (/) , 1o ) e. 2o )' % pm)})
    NVM = '( %s ` m )' % L_NF
    carv = nv['fields']['car']      # ( TMcar ` NVM ) = if ( ( TMfl ` m ) = 1o , (/) , 1o )
    flv = nv['fields']['fl']        # ( TMfl ` NVM ) = 1o
    # case split on ( H - ( i + 1 ) ) = 0
    Z1 = '( %s /\\ %s = 0 )' % (pm, HI1)
    Z2 = '( %s /\\ -. %s = 0 )' % (pm, HI1)
    LZ1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Z1, concl(w, pm, st)))
    LZ2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Z2, concl(w, pm, st)))
    IFH = 'if ( %s = 0 , 1o , (/) )' % HI1
    z1 = w.s([], 'simpr', '( %s -> %s = 0 )' % (Z1, HI1))
    fm1 = w.s([LZ1(mc), w.s([z1], 'iftrued', '( %s -> %s = 1o )' % (Z1, IFH))], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % Z1)
    car1 = w.s([LZ1(carv), w.s([fm1], 'iftrued', '( %s -> if ( ( TMfl ` m ) = 1o , (/) , 1o ) = (/) )' % Z1)], 'eqtrd',
               '( %s -> ( TMcar ` %s ) = (/) )' % (Z1, NVM))
    rq1 = w.s([z1, LZ1(Lm(kz))], 'mpd', '( %s -> ( %s = %s /\\ %s = 1o ) )' % (Z1, RV, I1, QV))
    q1 = w.s([rq1], 'simprd', '( %s -> %s = 1o )' % (Z1, QV))
    nlr1 = w.s([w.s([LZ1(Lm(kb)), w.s([z1], 'notnotd', '( %s -> -. -. %s = 0 )' % (Z1, HI1))], 'mtbird' if False else 'sylnibr',
                    '( %s -> -. %s < %s )' % (Z1, I1, RV)), LZ1(Lm(lp.req))], 'breqtrrd' if False else 'jca', '') if False else None
    nlr1 = w.s([w.s([z1], 'notnotd', '( %s -> -. -. %s = 0 )' % (Z1, HI1)), LZ1(Lm(kb))], 'mtbird',
               '( %s -> -. %s < %s )' % (Z1, I1, RV))
    ifz = w.s([w.s([w.s([LZ1(Lm(lp.req))], 'breq2d', '( %s -> ( %s < R <-> %s < %s ) )' % (Z1, I1, I1, RV)), nlr1], 'mtbird',
                   '( %s -> -. %s < R )' % (Z1, I1))], 'iffalsed', '( %s -> if ( %s < R , 1o , (/) ) = (/) )' % (Z1, I1))
    cz1 = w.s([car1, ifz], 'eqtr4d', '( %s -> ( TMcar ` %s ) = if ( %s < R , 1o , (/) ) )' % (Z1, NVM, I1))
    fz1 = w.s([LZ1(flv), q1], 'eqtr4d', '( %s -> ( TMfl ` %s ) = %s )' % (Z1, NVM, QV))
    iz1 = w.s([fz1], 'a1d', '( %s -> ( %s = R -> ( TMfl ` %s ) = %s ) )' % (Z1, I1, NVM, QV))
    co1 = w.s([cz1, iz1], 'jca', '( %s -> %s )' % (Z1, NCOND(NVM, I1)))
    # case nonzero
    z2 = w.s([], 'simpr', '( %s -> -. %s = 0 )' % (Z2, HI1))
    fm2 = w.s([LZ2(mc), w.s([z2], 'iffalsed', '( %s -> %s = (/) )' % (Z2, IFH))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % Z2)
    fn1 = not1o(w, Z2, fm2, 'TMfl', 'm')
    car2 = w.s([LZ2(carv), w.s([fn1], 'iffalsed', '( %s -> if ( ( TMfl ` m ) = 1o , (/) , 1o ) = 1o )' % Z2)], 'eqtrd',
               '( %s -> ( TMcar ` %s ) = 1o )' % (Z2, NVM))
    lr2 = w.s([z2, LZ2(Lm(kb))], 'mpbird', '( %s -> %s < %s )' % (Z2, I1, RV))
    lr2b = w.s([lr2, w.s([LZ2(Lm(lp.req))], 'eqcomd', '( %s -> %s = R )' % (Z2, RV))], 'breqtrd', '( %s -> %s < R )' % (Z2, I1))
    ift = w.s([lr2b], 'iftrued', '( %s -> if ( %s < R , 1o , (/) ) = 1o )' % (Z2, I1))
    cz2 = w.s([car2, ift], 'eqtr4d', '( %s -> ( TMcar ` %s ) = if ( %s < R , 1o , (/) ) )' % (Z2, NVM, I1))
    ne2_ = w.s([w.s([lr2b], 'ltned', '( %s -> %s =/= R )' % (Z2, I1))], 'neneqd', '( %s -> -. %s = R )' % (Z2, I1))
    iz2 = w.s([ne2_], 'pm2.21d', '( %s -> ( %s = R -> ( TMfl ` %s ) = %s ) )' % (Z2, I1, NVM, QV))
    co2 = w.s([cz2, iz2], 'jca', '( %s -> %s )' % (Z2, NCOND(NVM, I1)))
    co = w.s([co1, co2], 'pm2.61dan', '( %s -> %s )' % (pm, NCOND(NVM, I1)))
    inn1 = fam_pack(w, pm, NCOND, I1, Lm(lp.i1n), NVM, nv['mem'], co)
    hld = w.s([inn1], 'ralrimiva', '( %s -> %s )' % (ps, HLD3))
    w.qed([t3, hld], 'jca', C)
    return w.run()


PSI4 = '( %s /\\ %s )' % (PSI, LTI)
PSI5 = '( %s /\\ ( -. %s /\\ %s ) )' % (PSI, LTI, DVI)


def iter_ctx2(w, ps, lift):
    """Lp at ps = ( PSI /\\ extra ) with the i facts"""
    lp = Lp(w, ps, lift=lift)
    ii = w.s([], 'simplr', '( %s -> i e. ( 0 ..^ R ) )' % ps)
    lp.inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    lp.ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ps)
    lp.ile = w.s([lp.ilt], 'ltled', '( %s -> i <_ R )' % ps)
    cl = lp.cl
    cl.leaf('i', 'NN0', lp.inn)
    lp.i1n = w.s([lp.inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ps)
    zl = w.s([cl.mem('i', 'ZZ'), cl.mem('R', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < R <-> ( i + 1 ) <_ R ) )' % ps)
    lp.i1le = w.s([lp.ilt, zl], 'mpbid', '( %s -> ( i + 1 ) <_ R )' % ps)
    lp.cii = w.s([lp.ilt], 'iftrued', '( %s -> %s = i )' % (ps, CI('i')))
    lp.gin = w.s([lp.gnn, lp.inn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( G + i ) e. NN )' % ps)
    lp.gin0 = w.s([lp.gin], 'nnnn0d', '( %s -> ( G + i ) e. NN0 )' % ps)
    return lp


def peq_early(w, lp, ps, ri1, eor):
    """( ps -> ( P' ` ( i + 1 ) ) = ( P' ` i ) ) from ri1 : R = ( i + 1 ) and eor : ( LTI \\/ DVI )"""
    cl = lp.cl
    I1 = '( i + 1 )'
    rmi = lineq(w, ps, '( R - 1 )', 'i', hyps=[ri1], closure=cl)
    ew, EW2 = w.wcongr(EARLY, {}, ps, {}, rules={'( R - 1 )': ('i', rmi)})
    rpos = linarith(w, ps, [ri1, cl.ge0('i')], '0 < R', closure=cl)
    ea = w.s([rpos, eor], 'jca', '( %s -> %s )' % (ps, EW2))
    ear = w.s([ew, ea], 'mpbird', '( %s -> %s )' % (ps, EARLY))
    si = w.s([w.s([lp.c['S = %s' % SV], w.s([ear], 'iftrued', '( %s -> %s = ( R - 1 ) )' % (ps, SV))], 'eqtrd', '( %s -> S = ( R - 1 ) )' % ps), rmi],
             'eqtrd', '( %s -> S = i )' % ps)
    nlt = w.s([w.s([cl.mem('R', 'RR')], 'ltnrd', '( %s -> -. R < R )' % ps),
               w.s([ri1], 'breq1d', '( %s -> ( R < R <-> %s < R ) )' % (ps, I1))], 'mtbid', '( %s -> -. %s < R )' % (ps, I1))
    ci1 = w.s([w.s([nlt], 'iffalsed', '( %s -> %s = S )' % (ps, CI(I1))), si], 'eqtrd', '( %s -> %s = i )' % (ps, CI(I1)))
    pv1, _, _, _ = lp.pv(I1, lp.i1n, lp.i1le)
    pv0, _, _, _ = lp.pv('i', lp.inn, lp.ile)
    r1, x1 = w.rewrite(PB(I1), {CI(I1): ('i', ci1)}, ps)
    r0, x0 = w.rewrite(PB('i'), {CI('i'): ('i', lp.cii)}, ps)
    assert x1 == x0, (x1, x0)
    a = w.s([pv1, r1], 'eqtrd', "( %s -> ( %s ` %s ) = %s )" % (ps, PV, I1, x1))
    b = w.s([pv0, r0], 'eqtrd', "( %s -> ( %s ` i ) = %s )" % (ps, PV, x0))
    return w.s([a, b], 'eqtr4d', "( %s -> ( %s ` %s ) = ( %s ` i ) )" % (ps, PV, I1, PV))


def load_in(w, lp, ps, fam_cond, lam_kw, car_val, fl_val, ri1, qv, carv_const):
    """( ps -> A. m e. ( FAM ` i ) ( LOAD ` m ) e. ( NF ` ( i + 1 ) ) ) for a load setting car := (/) ,
    fl := fl_val (a constant), R = i + 1 (ri1), qv : ( ps -> QV = fl_val )"""
    I1 = '( i + 1 )'
    FAM = FAMF(fam_cond)
    LOAD = LSET(**lam_kw('u'))
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, FAM)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, fam_cond, 'i', Lm(lp.inn), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, FAM)))
    nv = load_val(w, pm, lam_kw, 'm', mm)
    NVM = '( %s ` m )' % LOAD
    carv = nv['fields']['car']
    flv = nv['fields']['fl']
    nlt = w.s([w.s([lp.cl.mem('R', 'RR')], 'ltnrd', '( %s -> -. R < R )' % ps),
               w.s([ri1], 'breq1d', '( %s -> ( R < R <-> %s < R ) )' % (ps, I1))], 'mtbid', '( %s -> -. %s < R )' % (ps, I1))
    ifz = w.s([Lm(nlt)], 'iffalsed', '( %s -> if ( %s < R , 1o , (/) ) = (/) )' % (pm, I1))
    cz = w.s([carv, ifz], 'eqtr4d', '( %s -> ( TMcar ` %s ) = if ( %s < R , 1o , (/) ) )' % (pm, NVM, I1))
    fz = w.s([flv, Lm(qv)], 'eqtr4d', '( %s -> ( TMfl ` %s ) = %s )' % (pm, NVM, QV))
    iz = w.s([fz], 'a1d', '( %s -> ( %s = R -> ( TMfl ` %s ) = %s ) )' % (pm, I1, NVM, QV))
    co = w.s([cz, iz], 'jca', '( %s -> %s )' % (pm, NCOND(NVM, I1)))
    inn1 = fam_pack(w, pm, NCOND, I1, Lm(lp.i1n), NVM, nv['mem'], co)
    return w.s([inn1], 'ralrimiva', '( %s -> A. m e. ( %s ` i ) %s e. ( %s ` %s ) )' % (ps, FAM, NVM, NF, I1))


def tmipgi4():
    lab = 'tmipgi4'
    C = '( %s -> %s )' % (PSI4, DA)
    w = W(lab, 'One iteration of Lean\'s ` primeGoF ` loop at the machine, the exit ` m < ( G + i ) ^ 2 ` : the branch '
               '` cmp = lt ` is taken, the load ` carry := false , flag := true ` lands in the invariant\'s class at '
               '` i + 1 = primeIters ` with the result true, and the stacks do not move (Lean ` primeIters_succ_lt ` ).')
    ps = PSI4
    lp = iter_ctx2(w, ps, 'simpll')
    cl = lp.cl
    lt = w.s([], 'simpr', '( %s -> %s )' % (ps, LTI))
    c1, c2, c3 = pgit(w, lp, ps, lp.inn, lp.ilt)
    rq = w.s([lt, c1], 'mpd', '( %s -> ( %s = ( i + 1 ) /\\ %s = 1o ) )' % (ps, RV, QV))
    ri1 = w.s([lp.req, w.s([rq], 'simpld', '( %s -> %s = ( i + 1 ) )' % (ps, RV))], 'eqtrd', '( %s -> R = ( i + 1 ) )' % ps)
    q1 = w.s([rq], 'simprd', '( %s -> %s = 1o )' % (ps, QV))
    # HT : the branch cmp = lt holds on the compare class
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, N1F)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, N1COND, 'i', Lm(lp.inn), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, N1F)))
    GG = '( %s x. %s )' % (GI, GI)
    ggn = w.s([lp.gin0, lp.gin0], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ps, GG))
    nl = w.s([w.s([lp.fn, ggn], 'jca', '( %s -> ( F e. NN0 /\\ %s e. NN0 ) )' % (ps, GG)), w.inst('ncmplt')], 'syl',
             '( %s -> ( ( F Ncmp %s ) = (/) <-> %s ) )' % (ps, GG, LTI))
    nc0 = w.s([lt, nl], 'mpbird', '( %s -> ( F Ncmp %s ) = (/) )' % (ps, GG))
    cm0 = w.s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = (/) )' % pm)
    X_of = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', w.s([], '1oex', '1o e. _V'), w.s([], '0ex', '(/) e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    ht = w.s([w.s([cv, w.s([cm0], 'iftrued', '( %s -> %s = 1o )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CLT))],
             'ralrimiva', '( %s -> %s )' % (ps, HT1))
    hld = load_in(w, lp, ps, N1COND, lambda t: dict(car='(/)', fl='1o'), '(/)', '1o', ri1, q1, None)
    assert concl(w, ps, hld) == HLD1, (concl(w, ps, hld), HLD1)
    eor = w.s([lt], 'orcd', '( %s -> ( %s \\/ %s ) )' % (ps, LTI, DVI))
    pe = peq_early(w, lp, ps, ri1, eor)
    w.qed([ht, hld, pe], '3jca', C)
    return w.run()


def tmipgi5():
    lab = 'tmipgi5'
    C = '( %s -> %s )' % (PSI5, DA2)
    w = W(lab, 'One iteration of Lean\'s ` primeGoF ` loop at the machine, the exit ` ( G + i ) || m ` : the branch on '
               '` flag ` is taken, the load ` carry := false , flag := false ` lands in the invariant\'s class at '
               '` i + 1 = primeIters ` with the result false, and the stacks do not move (Lean ` primeIters_succ_dvd ` ).')
    ps = PSI5
    lp = iter_ctx2(w, ps, 'simpll')
    nlt = w.s([], 'simprl', '( %s -> -. %s )' % (ps, LTI))
    dv = w.s([], 'simprr', '( %s -> %s )' % (ps, DVI))
    c1, c2, c3 = pgit(w, lp, ps, lp.inn, lp.ilt)
    rq = w.s([w.s([nlt, dv], 'jca', '( %s -> ( -. %s /\\ %s ) )' % (ps, LTI, DVI)), c2], 'mpd',
             '( %s -> ( %s = ( i + 1 ) /\\ %s = (/) ) )' % (ps, RV, QV))
    ri1 = w.s([lp.req, w.s([rq], 'simpld', '( %s -> %s = ( i + 1 ) )' % (ps, RV))], 'eqtrd', '( %s -> R = ( i + 1 ) )' % ps)
    q0 = w.s([rq], 'simprd', '( %s -> %s = (/) )' % (ps, QV))
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, N2F)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, N2COND, 'i', Lm(lp.inn), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, N2F)))
    ht = w.s([w.s([mc, w.s([Lm(dv)], 'iftrued', '( %s -> if ( %s , 1o , (/) ) = 1o )' % (pm, DVI))], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)],
             'ralrimiva', '( %s -> %s )' % (ps, HT2))
    hld = load_in(w, lp, ps, N2COND, lambda t: dict(car='(/)', fl='(/)'), '(/)', '(/)', ri1, q0, None)
    assert concl(w, ps, hld) == HLD2, (concl(w, ps, hld), HLD2)
    eor = w.s([dv], 'olcd', '( %s -> ( %s \\/ %s ) )' % (ps, LTI, DVI))
    pe = peq_early(w, lp, ps, ri1, eor)
    w.qed([ht, hld, pe], '3jca', C)
    return w.run()


def tmipgi6():
    lab = 'tmipgi6'
    C = '( %s -> %s )' % (PSI, DISJ)
    w = W(lab, 'One iteration of Lean\'s ` primeGoF ` loop at the machine, the dispatch of ` primeGoBody ` : the two '
               'early exits (~ tmipgi4 , ~ tmipgi5 ) or the modulo run (~ tmipgi2 ) followed by the step run and the '
               'continue load (~ tmipgi3 ).')
    ps = PSI
    lp = iter_ctx(w)
    # the lt case
    A1 = '( %s /\\ %s )' % (ps, LTI)
    a1 = w.s([], 'tmipgi4', '( %s -> %s )' % (A1, DA))
    o1 = w.s([a1], 'orcd', '( %s -> %s )' % (A1, DISJ))
    # the not-lt case
    A2 = '( %s /\\ -. %s )' % (ps, LTI)
    nlt = w.s([], 'simpr', '( %s -> -. %s )' % (A2, LTI))
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ps, st)))
    pm = '( %s /\\ m e. ( %s ` i ) )' % (A2, N1F)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, A2, st)))
    mm, mc = fam_unpack(w, pm, N1COND, 'i', Lm(L2(lp.inn)), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, N1F)))
    GG = '( %s x. %s )' % (GI, GI)
    ggn = w.s([lp.gin0, lp.gin0], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ps, GG))
    nl = w.s([w.s([lp.fn, ggn], 'jca', '( %s -> ( F e. NN0 /\\ %s e. NN0 ) )' % (ps, GG)), w.inst('ncmplt')], 'syl',
             '( %s -> ( ( F Ncmp %s ) = (/) <-> %s ) )' % (ps, GG, LTI))
    nc0 = w.s([nlt, L2(nl)], 'mtbird', '( %s -> -. ( F Ncmp %s ) = (/) )' % (A2, GG))
    cm0 = w.s([Lm(nc0), w.s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = (/) <-> ( F Ncmp %s ) = (/) ) )' % (pm, GG))], 'mtbird',
              '( %s -> -. ( TMcmp ` m ) = (/) )' % pm)
    X_of = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', w.s([], '1oex', '1o e. _V'), w.s([], '0ex', '(/) e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    c0 = w.s([cv, w.s([cm0], 'iffalsed', '( %s -> %s = (/) )' % (pm, X_of('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CLT))
    htf1 = w.s([not1o(w, pm, c0, CLT, 'm')], 'ralrimiva', '( %s -> %s )' % (A2, HTF1))
    tri2 = w.s([w.s([], 'tmipgi2', '( %s -> %s )' % (ps, TRI2))], 'adantr', '( %s -> %s )' % (A2, TRI2))
    # the inner dispatch
    B1 = '( %s /\\ %s )' % (A2, DVI)
    b1 = w.s([w.s([w.s([], 'simplr', '( %s -> -. %s )' % (B1, LTI)), w.s([], 'simpr', '( %s -> %s )' % (B1, DVI))], 'jca',
                  '( %s -> ( -. %s /\\ %s ) )' % (B1, LTI, DVI)),
              w.s([], 'simpll', '( %s -> %s )' % (B1, ps))], 'ancom' if False else 'jca', '') if False else None
    b1 = w.s([w.s([], 'simpll', '( %s -> %s )' % (B1, ps)),
              w.s([w.s([], 'simplr', '( %s -> -. %s )' % (B1, LTI)), w.s([], 'simpr', '( %s -> %s )' % (B1, DVI))], 'jca',
                  '( %s -> ( -. %s /\\ %s ) )' % (B1, LTI, DVI))], 'jca', '( %s -> %s )' % (B1, PSI5))
    da2 = w.s([b1, w.inst('tmipgi5')], 'syl', '( %s -> %s )' % (B1, DA2))
    od = w.s([da2], 'orcd', '( %s -> %s )' % (B1, DISJ2))
    B2 = '( %s /\\ -. %s )' % (A2, DVI)
    ndv = w.s([], 'simpr', '( %s -> -. %s )' % (B2, DVI))
    b2 = w.s([w.s([], 'simpll', '( %s -> %s )' % (B2, ps)),
              w.s([w.s([], 'simplr', '( %s -> -. %s )' % (B2, LTI)), ndv], 'jca', '( %s -> ( -. %s /\\ -. %s ) )' % (B2, LTI, DVI))],
             'jca', '( %s -> %s )' % (B2, PSI3))
    t3 = w.s([b2, w.inst('tmipgi3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (B2, TRI3, HLD3))
    # HTF2 : flag false on the modulo class
    pm2 = '( %s /\\ m e. ( %s ` i ) )' % (B2, N2F)
    LB2 = lambda st, a: w.s([st], 'adantr', '( %s -> %s )' % (pm2, concl(w, a, st)))
    inn2 = w.s([lp.inn], 'ad2antrr', '( %s -> i e. NN0 )' % B2)
    mm2, mc2 = fam_unpack(w, pm2, N2COND, 'i', LB2(inn2, B2), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm2, N2F)))
    f0 = w.s([mc2, w.s([LB2(ndv, B2)], 'iffalsed', '( %s -> if ( %s , 1o , (/) ) = (/) )' % (pm2, DVI))], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm2)
    htf2 = w.s([not1o(w, pm2, f0, 'TMfl', 'm')], 'ralrimiva', '( %s -> %s )' % (B2, HTF2))
    db2 = w.s([htf2, w.s([t3], 'simpld', '( %s -> %s )' % (B2, TRI3)), w.s([t3], 'simprd', '( %s -> %s )' % (B2, HLD3))], '3jca',
              '( %s -> %s )' % (B2, DB2))
    od2 = w.s([db2], 'olcd', '( %s -> %s )' % (B2, DISJ2))
    dj2 = w.s([od, od2], 'pm2.61dan', '( %s -> %s )' % (A2, DISJ2))
    db = w.s([htf1, tri2, dj2], '3jca', '( %s -> %s )' % (A2, DB))
    o2 = w.s([db], 'olcd', '( %s -> %s )' % (A2, DISJ))
    w.qed([o1, o2], 'pm2.61dan', C)
    return w.run()


TYP = GTREE[1][1][0]
EXITT = GTREE[1][2]
PRO = GTREE[2]


def c0_zero(w, lp, ps):
    """( ps -> CI( 0 ) = 0 )"""
    cl = lp.cl
    A1 = '( %s /\\ 0 < R )' % ps
    A2 = '( %s /\\ -. 0 < R )' % ps
    a = w.s([w.s([], 'simpr', '( %s -> 0 < R )' % A1)], 'iftrued', '( %s -> %s = 0 )' % (A1, CI('0')))
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (A2, concl(w, ps, st)))
    n0 = w.s([], 'simpr', '( %s -> -. 0 < R )' % A2)
    ne_ = w.s([n0], 'intnanrd', '( %s -> -. %s )' % (A2, EARLY))
    sr = w.s([L2(lp.c['S = %s' % SV]), w.s([ne_], 'iffalsed', '( %s -> %s = R )' % (A2, SV))], 'eqtrd', '( %s -> S = R )' % A2)
    cl2 = Closure(w, A2, {'R': ('NN0', L2(lp.rn))})
    ler = w.s([cl2.mem('R', 'RR'), closed(w, A2, '0re', '0 e. RR')], 'lenltd', '( %s -> ( R <_ 0 <-> -. 0 < R ) )' % A2)
    rle0 = w.s([ler, n0], 'mpbird', '( %s -> R <_ 0 )' % A2)
    r0 = lineq(w, A2, 'R', '0', hyps=[rle0, cl2.ge0('R')], closure=cl2)
    b = w.s([w.s([n0], 'iffalsed', '( %s -> %s = S )' % (A2, CI('0'))), w.s([sr, r0], 'eqtrd', '( %s -> S = 0 )' % A2)], 'eqtrd',
            '( %s -> %s = 0 )' % (A2, CI('0')))
    return w.s([a, b], 'pm2.61dan', '( %s -> %s = 0 )' % (ps, CI('0')))


def tmipgt():
    lab = 'tmipgt'
    C = '( %s -> ( %s /\\ %s /\\ %s ) )' % (PHL, TYP, EXITT, cj(PRO))
    w = W(lab, 'The frame of Lean\'s ` primeGoF ` loop at the machine: the invariant\'s classes are classes of states '
               'and its stacks stacks for ` i <_ primeIters ` , the loop test ` carry ` fails at ` primeIters ` , and '
               'the prologue ` isZero xf s ; load\' ( carry := !flag , flag := true ) ` enters the invariant at 0.')
    ps = PHL
    lp = Lp(w, ps)
    cl = lp.cl
    # TYP
    pt = '( %s /\\ i e. ( 0 ... R ) )' % ps
    lt = Lp(w, pt)
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ... R ) )' % pt)
    inn = w.s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    ile = w.s([ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ R )' % pt)
    lt.cl.leaf('i', 'NN0', inn)
    nss = lt.famss(NCOND, 'i', inn)
    mem, _ = lt.pvals('i', inn, ile)
    typ = w.s([w.s([nss, mem], 'jca', '( %s -> %s )' % (pt, TYP[len('A. i e. ( 0 ... R ) '):]))], 'ralrimiva', '( %s -> %s )' % (ps, TYP))
    # EXIT
    pm = '( %s /\\ m e. ( %s ` R ) )' % (ps, NF)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = fam_unpack(w, pm, NCOND, 'R', Lm(lp.rn), 'm', w.s([], 'simpr', '( %s -> m e. ( %s ` R ) )' % (pm, NF)))
    car = w.s([mc], 'simpld', '( %s -> ( TMcar ` m ) = if ( R < R , 1o , (/) ) )' % pm)
    nrr = w.s([Lm(w.s([cl.mem('R', 'RR')], 'ltnrd', '( %s -> -. R < R )' % ps))], 'iffalsed', '( %s -> if ( R < R , 1o , (/) ) = (/) )' % pm)
    ex_ = w.s([not1o(w, pm, w.s([car, nrr], 'eqtrd', '( %s -> ( TMcar ` m ) = (/) )' % pm), 'TMcar', 'm')], 'ralrimiva', '( %s -> %s )' % (ps, EXITT))
    # PRO : the classes
    ss0 = closed(w, ps, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    ssp = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % OP)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, OP)), lp.mk['seq']], 'sseqtrrd',
              '( %s -> %s C_ ( 2nd ` T ) )' % (ps, OP))
    # the prologue triple: isZero xf s at ( P' ` 0 )
    z0 = closed(w, ps, '0nn0', '0 e. NN0')
    z0le = w.s([lp.rn], 'nn0ge0d', '( %s -> 0 <_ R )' % ps)
    mem0, SP0 = lp.pvals('0', z0, z0le)
    c00 = c0_zero(w, lp, ps)
    h0 = w.s([w.s([c00], 'oveq2d', '( %s -> ( H - %s ) = ( H - 0 ) )' % (ps, CI('0'))),
              w.s([cl.mem('H', 'CC')], 'subid1d', '( %s -> ( H - 0 ) = H )' % ps)], 'eqtrd', '( %s -> ( H - %s ) = H )' % (ps, CI('0')))
    vI = SP0.vals['I']
    iv = w.s([vI[1], w.s([w.s([h0], 'fveq2d', '( %s -> ( encNatGam ` ( H - %s ) ) = ( encNatGam ` H ) )' % (ps, CI('0')))], 'oveq1d',
                         '( %s -> %s = %s )' % (ps, vI[0], EW('H', 'Z')))], 'eqtrd', "( %s -> ( ( %s ` 0 ) ` I ) = %s )" % (ps, PV, EW('H', 'Z')))
    hlt = linarith(w, ps, [lp.c['( G + H ) < ( 2 ^ N )'], cl.ge0('G')], 'H < ( 2 ^ N )', closure=cl, atoms=['( 2 ^ N )'])
    P0T = "( %s ` 0 )" % PV
    ex = dict(lp.base)
    ex.update({STKD(P0T): mem0, '( %s ` I ) = %s' % (P0T, EW('H', 'Z')): iv, 'H < ( 2 ^ N )': hlt})
    t, cc = inst(w, ps, 'tmiizbs', {'K': 'I', 'I': "I'", 'F': 'H', 'X': 'Z', 'P': PL('P', 2), 'E': PL('P', 0), 'D': P0T}, Bld(w, ps, lp.c, ex))
    assert cc == PRO[1][0], (cc, PRO[1][0])
    # the load into ( N ` 0 )
    pm = '( %s /\\ m e. %s )' % (ps, OP)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    mm, mc = rab_elim(w, pm, OP, lambda h: '( TMfl ` %s ) = if ( H = 0 , 1o , (/) )' % h, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (pm, OP)))
    nv = load_val(w, pm, lambda t_: dict(car='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t_, fl='1o'), 'm', mm,
                  clmap={'if ( ( TMfl ` m ) = 1o , (/) , 1o )': w.s([closed(w, pm, '0el2o', '(/) e. 2o'), closed(w, pm, '1oel2o', '1o e. 2o')],
                                                                    'ifcld', '( %s -> if ( ( TMfl ` m ) = 1o , (/) , 1o ) e. 2o )' % pm)})
    NVM = '( %s ` m )' % L_NF
    carv, flv = nv['fields']['car'], nv['fields']['fl']
    g0 = w.s([lp.j3, w.inst('tmipg0')], 'syl', '( %s -> ( ( %s = 0 <-> H = 0 ) /\\ ( H = 0 -> %s = 1o ) ) )' % (ps, RV, QV))
    r0b = w.s([w.s([lp.req], 'eqeq1d', '( %s -> ( R = 0 <-> %s = 0 ) )' % (ps, RV)), w.s([g0], 'simpld', '( %s -> ( %s = 0 <-> H = 0 ) )' % (ps, RV))],
              'bitrd', '( %s -> ( R = 0 <-> H = 0 ) )' % ps)
    hq = w.s([g0], 'simprd', '( %s -> ( H = 0 -> %s = 1o ) )' % (ps, QV))
    Z1 = '( %s /\\ H = 0 )' % pm
    Z2 = '( %s /\\ -. H = 0 )' % pm
    LZ1 = lambda st, a=pm: w.s([st], 'adantr', '( %s -> %s )' % (Z1, concl(w, a, st)))
    LZ2 = lambda st, a=pm: w.s([st], 'adantr', '( %s -> %s )' % (Z2, concl(w, a, st)))
    z1 = w.s([], 'simpr', '( %s -> H = 0 )' % Z1)
    fm1 = w.s([LZ1(mc), w.s([z1], 'iftrued', '( %s -> if ( H = 0 , 1o , (/) ) = 1o )' % Z1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % Z1)
    car1 = w.s([LZ1(carv), w.s([fm1], 'iftrued', '( %s -> if ( ( TMfl ` m ) = 1o , (/) , 1o ) = (/) )' % Z1)], 'eqtrd', '( %s -> ( TMcar ` %s ) = (/) )' % (Z1, NVM))
    rz1 = w.s([z1, LZ1(Lm(r0b))], 'mpbird', '( %s -> R = 0 )' % Z1)
    nl1 = w.s([w.s([w.s([closed(w, Z1, '0re', '0 e. RR')], 'ltnrd', '( %s -> -. 0 < 0 )' % Z1), w.s([rz1], 'breq2d', '( %s -> ( 0 < R <-> 0 < 0 ) )' % Z1)],
                   'mtbird', '( %s -> -. 0 < R )' % Z1)], 'iffalsed', '( %s -> if ( 0 < R , 1o , (/) ) = (/) )' % Z1)
    cz1 = w.s([car1, nl1], 'eqtr4d', '( %s -> ( TMcar ` %s ) = if ( 0 < R , 1o , (/) ) )' % (Z1, NVM))
    q1 = w.s([z1, LZ1(Lm(hq))], 'mpd', '( %s -> %s = 1o )' % (Z1, QV))
    iz1 = w.s([w.s([LZ1(flv), q1], 'eqtr4d', '( %s -> ( TMfl ` %s ) = %s )' % (Z1, NVM, QV))], 'a1d', '( %s -> ( 0 = R -> ( TMfl ` %s ) = %s ) )' % (Z1, NVM, QV))
    co1 = w.s([cz1, iz1], 'jca', '( %s -> %s )' % (Z1, NCOND(NVM, '0')))
    z2 = w.s([], 'simpr', '( %s -> -. H = 0 )' % Z2)
    fm2 = w.s([LZ2(mc), w.s([z2], 'iffalsed', '( %s -> if ( H = 0 , 1o , (/) ) = (/) )' % Z2)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % Z2)
    car2 = w.s([LZ2(carv), w.s([not1o(w, Z2, fm2, 'TMfl', 'm')], 'iffalsed', '( %s -> if ( ( TMfl ` m ) = 1o , (/) , 1o ) = 1o )' % Z2)], 'eqtrd',
               '( %s -> ( TMcar ` %s ) = 1o )' % (Z2, NVM))
    rn2 = w.s([z2, LZ2(Lm(r0b))], 'mtbird', '( %s -> -. R = 0 )' % Z2)
    rne = w.s([rn2], 'neqned', '( %s -> R =/= 0 )' % Z2)
    rp = w.s([LZ2(Lm(lp.rn)), rne, w.inst('elnnne0')], 'sylanbrc', '( %s -> R e. NN )' % Z2)
    rpos = w.s([rp, w.inst('nngt0')], 'syl', '( %s -> 0 < R )' % Z2)
    cz2 = w.s([car2, w.s([rpos], 'iftrued', '( %s -> if ( 0 < R , 1o , (/) ) = 1o )' % Z2)], 'eqtr4d',
              '( %s -> ( TMcar ` %s ) = if ( 0 < R , 1o , (/) ) )' % (Z2, NVM))
    n0r = w.s([w.s([rne], 'necomd', '( %s -> 0 =/= R )' % Z2)], 'neneqd', '( %s -> -. 0 = R )' % Z2)
    iz2 = w.s([n0r], 'pm2.21d', '( %s -> ( 0 = R -> ( TMfl ` %s ) = %s ) )' % (Z2, NVM, QV))
    co2 = w.s([cz2, iz2], 'jca', '( %s -> %s )' % (Z2, NCOND(NVM, '0')))
    co = w.s([co1, co2], 'pm2.61dan', '( %s -> %s )' % (pm, NCOND(NVM, '0')))
    in0 = fam_pack(w, pm, NCOND, '0', closed(w, pm, '0nn0', '0 e. NN0'), NVM, nv['mem'], co)
    hl = w.s([in0], 'ralrimiva', '( %s -> %s )' % (ps, PRO[1][1]))
    pro = w.s([w.s([ss0, ssp], 'jca', '( %s -> %s )' % (ps, cj(PRO[0]))), w.s([t, hl], 'jca', '( %s -> %s )' % (ps, cj(PRO[1])))], 'jca',
              '( %s -> %s )' % (ps, cj(PRO)))
    w.qed([typ, ex_, pro], '3jca', C)
    return w.run()


def ldty(w, ph, mk, kw_of):
    """( ph -> LSET e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )"""
    pu = 'u e. TMSt'
    rr = w.s([], 'id', '( %s -> u e. TMSt )' % pu)
    cl = st_comps(w, pu, 'u', rr)
    kw = kw_of('u')
    comps = [kw.get(f, FLD(f, 'u')) for f in ORDER]
    cls = []
    for f, comp in zip(ORDER, comps):
        if f not in kw:
            cls.append(cl[f])
        elif comp == '(/)':
            cls.append(closed(w, pu, '0el2o', '(/) e. 2o'))
        elif comp == '1o':
            cls.append(closed(w, pu, '1oel2o', '1o e. 2o'))
        else:
            cls.append(w.s([closed(w, pu, '0el2o', '(/) e. 2o'), closed(w, pu, '1oel2o', '1o e. 2o')], 'ifcld', '( %s -> %s e. 2o )' % (pu, comp)))
    mem, vals = tuple_facts(w, pu, comps, cls)
    X_of = lambda t: SETF(t, **kw_of(t))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    lt = lamty(w, ph, mk, LSET(**kw_of('u')), X_of, 'TMSt', sv, mem)
    e = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    e2 = w.s([e], 'oveq1d', '( %s -> ( TMSt ^m ( 2nd ` T ) ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    return w.s([lt, e2], 'eleqtrd', '( %s -> %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % (ph, LSET(**kw_of('u'))))


def tmipgl():
    lab = 'tmipgl'
    C = '( %s -> %s )' % (PHL, GCONCL)
    w = W(lab, 'Lean\'s ` primeGoF xm xd xf s t u ` at the machine, wherever it is installed ( ` primeGoF_le_B ` , the '
               'loop form): ~ tm2fpg at the families of ` PGInv ` (the counter ` i ` , the result class at '
               '` primeIters ` , the stacks ` ( P\' ` i ) ` ), its blocks by ~ tmipgi1 , ~ tmipgi6 and ~ tmipgt .')
    ps = PHL
    lp = Lp(w, ps)
    mk, cl = lp.mk, lp.cl
    ex = dict(lp.base)
    un = dict(lp.base)
    def unf(fname, ks, P_, E_):
        pr = FRAGS[fname].pred(ks, 'T', 'M', P_, E_)
        assert pr in un, pr
        un.update(unfold_all(w, ps, un[pr], fname, ks, P_, E_, rec=False))
    unf('pgb', K6, PL('P', 3), PL('P', 1))
    unf('iz', ['I', "I'"], PL('P', 2), PL('P', 0))
    lb = FRAGS['pgb'].lmap(PL('P', 3), PL('P', 1))
    unf('dup', ['J', "I'", 'I"'], PL(PL('P', 3), 5), lb['X1'])
    unf('dup', ['K', "I'", 'I"'], PL(PL('P', 3), 10), lb['Y1'])
    unf('inc', ['J', "I'"], PL(PL('P', 3), 15), lb['Z1'])
    ex.update(un)
    ex['E e. ( 2nd ` ( 1st ` T ) )'] = lp.c['E e. ( 2nd ` ( 1st ` T ) )']
    b01 = lambda X_of: w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    ex[CTY(CLT)] = lamty(w, ps, mk, CLT, XL, '2o', w.s([], '2oex', '2o e. _V'), b01(XL))
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ps, ST_FLTY[len('( %s -> ' % SEQ):-2]))
    ex.update(parts(w, ps, fl, parse_conj(ST_FLTY[len('( %s -> ' % SEQ):-2])))
    ex[LTY(L_TT)] = ldty(w, ps, mk, lambda t: dict(car='(/)', fl='1o'))
    ex[LTY(L_FF)] = ldty(w, ps, mk, lambda t: dict(car='(/)', fl='(/)'))
    ex[LTY(L_NF)] = ldty(w, ps, mk, lambda t: dict(car='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t, fl='1o'))
    ex['R e. NN0'] = lp.rn
    tbn = w.s([w.s([lp.nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ps, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ps, TB))
    cl.leaf(TB, 'NN0', tbn)
    for e_ in [T15, T3_, TB]:
        ex['%s e. NN0' % e_] = cl.mem(e_, 'NN0')
    # the blocks
    tg = w.s([], 'tmipgt', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ps, TYP, EXITT, cj(PRO)))
    ex[TYP] = w.s([tg, w.inst('simp1')], 'syl', '( %s -> %s )' % (ps, TYP))
    ex[EXITT] = w.s([tg, w.inst('simp2')], 'syl', '( %s -> %s )' % (ps, EXITT))
    ex[cj(PRO)] = w.s([tg, w.inst('simp3')], 'syl', '( %s -> %s )' % (ps, cj(PRO)))
    j1 = w.s([], 'tmipgi1', '( %s -> ( %s /\\ %s ) )' % (PSI, cj(BODY[0]), TRI1))
    j6 = w.s([], 'tmipgi6', '( %s -> %s )' % (PSI, DISJ))
    bb = w.s([w.s([j1], 'simpld', '( %s -> %s )' % (PSI, cj(BODY[0]))),
              w.s([w.s([j1], 'simprd', '( %s -> %s )' % (PSI, TRI1)), j6], 'jca', '( %s -> %s )' % (PSI, cj(BODY[1])))], 'jca',
             '( %s -> %s )' % (PSI, cj(BODY)))
    ex[PER] = w.s([bb], 'ralrimiva', '( %s -> %s )' % (ps, PER))
    st = Bld(w, ps, lp.c, ex)(GTREE)
    w.qed([st, w.inst('tm2fpg')], 'syl', C)
    return w.run()


WDS_R = ((WRD('X', GAM), WRD('Y', GAM), WRD('Z', GAM)), STKD('D'),
         ('( D ` K ) = %s' % EW('F', 'X'), '( D ` J ) = %s' % EW('G', 'Y'), '( D ` I ) = %s' % EW('H', 'Z')))
T_R = ((T_PHM7, PG_.pred()), (idx_tree(K6), dist_tree(K6)), (NUMS_L, RS_L, WDS_R))
QCLS = '{ h e. TMSt | ( TMfl ` h ) = %s }' % QV
DFIN = UP(UP('D', 'J', EW('( G + S )', 'Y')), 'I', EW('( H - S )', 'Z'))
_GC_R = tsub_text(GCONCL, {PV: PDF})
BND_R = triple_parts(_GC_R)[2]
CONCL_R = TRI(CLN(GMAP['P0'], SS, 'D'), CLN('E', QCLS, DFIN), BND_R)


def tmipgr():
    lab = 'tmipgr'
    ps = cj(T_R)
    C = '( %s -> %s )' % (ps, CONCL_R)
    w = W(lab, 'Lean\'s ` primeGoF_le_B ` at the machine, wherever ` primeGoF xm xd xf s t u ` is installed: from any '
               'state with ` m ` on ` xm ` , ` d ` on ` xd ` , the fuel on ` xf ` , the machine reaches ` flag = '
               '( primeGo m d fuel ).1 ` with the divisor and the fuel stacks at the exit counter ` S ` of the loop '
               '(the other stacks restored), in ` primeIters ` iterations (~ tmipgl at its stack family).')
    c = Ctx(w, ps, T_R)
    eq = closed(w, ps, 'eqid', '%s = %s' % (PDF, PDF))
    TL2 = tsub(T_L, {PV: PDF})
    root = Bld(w, ps, c, {'%s = %s' % (PDF, PDF): eq})(TL2)
    lp = Lp(w, ps, tree=TL2, root=root, pv=PDF)
    cl = lp.cl
    t, cc = inst(w, ps, 'tmipgl', {PV: PDF}, Bld(w, ps, lp.c, {'%s = %s' % (PDF, PDF): eq}))
    Ca, Da, n = triple_parts(cc)
    # ( PDF ` 0 ) = D
    z0 = closed(w, ps, '0nn0', '0 e. NN0')
    z0le = w.s([lp.rn], 'nn0ge0d', '( %s -> 0 <_ R )' % ps)
    pv0, S0, _, _ = lp.pv('0', z0, z0le)
    c00 = c0_zero(w, lp, ps)
    g0 = w.s([w.s([c00], 'oveq2d', '( %s -> ( G + %s ) = ( G + 0 ) )' % (ps, CI('0'))), w.s([cl.mem('G', 'CC')], 'addridd', '( %s -> ( G + 0 ) = G )' % ps)],
             'eqtrd', '( %s -> ( G + %s ) = G )' % (ps, CI('0')))
    h0 = w.s([w.s([c00], 'oveq2d', '( %s -> ( H - %s ) = ( H - 0 ) )' % (ps, CI('0'))), w.s([cl.mem('H', 'CC')], 'subid1d', '( %s -> ( H - 0 ) = H )' % ps)],
             'eqtrd', '( %s -> ( H - %s ) = H )' % (ps, CI('0')))
    r0, x0 = w.rewrite(PB('0'), {'( G + %s )' % CI('0'): ('G', g0), '( H - %s )' % CI('0'): ('H', h0)}, ps)
    DJ1 = UP('D', 'J', EW('G', 'Y'))
    assert x0 == UP(DJ1, 'I', EW('H', 'Z')), x0
    tv, dd = lp.mk['tv'], lp.c[STKD('D')]
    kJ, kI = lp.mk['k']['J'], lp.mk['k']['I']
    u1 = upidv(w, ps, 'D', 'J', EW('G', 'Y'), lp.c['( D ` J ) = %s' % EW('G', 'Y')], tv, dd, kJ['kd'])
    u2 = upidv(w, ps, 'D', 'I', EW('H', 'Z'), lp.c['( D ` I ) = %s' % EW('H', 'Z')], tv, dd, kI['kd'])
    r1, x1 = w.rewrite(x0, {DJ1: ('D', u1)}, ps)
    assert x1 == UP('D', 'I', EW('H', 'Z')), x1
    p0d = w.s([w.s([w.s([pv0, r0], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ps, PDF, x0)), r1], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ps, PDF, x1)), u2],
              'eqtrd', '( %s -> ( %s ` 0 ) = D )' % (ps, PDF))
    ceq = clneq(w, ps, GMAP['P0'], SS, p0d, '( %s ` 0 )' % PDF, 'D')
    # ( PDF ` R ) = DFIN
    rle = w.s([w.s([lp.rn], 'nn0red', '( %s -> R e. RR )' % ps)], 'leidd', '( %s -> R <_ R )' % ps)
    pvR, SR, _, _ = lp.pv('R', lp.rn, rle)
    ciR = w.s([w.s([cl.mem('R', 'RR')], 'ltnrd', '( %s -> -. R < R )' % ps)], 'iffalsed', '( %s -> %s = S )' % (ps, CI('R')))
    rR, xR = w.rewrite(PB('R'), {CI('R'): ('S', ciR)}, ps)
    assert xR == DFIN, xR
    pRd = w.s([pvR, rR], 'eqtrd', '( %s -> ( %s ` R ) = %s )' % (ps, PDF, DFIN))
    NFR = '( %s ` R )' % NF
    deq = clneq(w, ps, 'E', NFR, pRd, '( %s ` R )' % PDF, DFIN)
    t2, C2, D2, n2 = hrrw(w, ps, t, Ca, Da, n, ceq=ceq, deq=deq)
    # the class ( NF ` R ) C_ { flag = result }
    fvR = lp.famv(NCOND, 'R', lp.rn)
    hh = '( ( TMcar ` h ) = if ( R < R , 1o , (/) ) /\\ ( R = R -> ( TMfl ` h ) = %s ) )' % QV
    im1 = w.s([], 'simpr', '( %s -> ( R = R -> ( TMfl ` h ) = %s ) )' % (hh, QV))
    im2 = w.s([im1, w.s([], 'eqid', 'R = R')], 'mpi', '( %s -> ( TMfl ` h ) = %s )' % (hh, QV))
    rg = w.s([w.s([im2], 'a1i', '( h e. TMSt -> ( %s -> ( TMfl ` h ) = %s ) )' % (hh, QV))], 'rgen',
             'A. h e. TMSt ( %s -> ( TMfl ` h ) = %s )' % (hh, QV))
    rs = w.s([rg, w.inst('rabss2')], 'ax-mp', '%s C_ %s' % (RAB(NCOND, 'R'), QCLS)) if False else \
        w.s([w.s([im2], 'a1i', '( h e. TMSt -> ( %s -> ( TMfl ` h ) = %s ) )' % (hh, QV))], 'ss2rabi', '%s C_ %s' % (RAB(NCOND, 'R'), QCLS))
    nss = w.s([fvR, w.s([rs], 'a1i', '( %s -> %s C_ %s )' % (ps, RAB(NCOND, 'R'), QCLS))], 'eqsstrd', '( %s -> %s C_ %s )' % (ps, NFR, QCLS))
    qss = w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % QCLS)], 'a1i', '( %s -> %s C_ TMSt )' % (ps, QCLS)), lp.mk['seq']], 'sseqtrrd',
              '( %s -> %s C_ ( 2nd ` T ) )' % (ps, QCLS))
    SF = S0
    sn, sle = lp.sfacts()
    cl.leaf('S', 'NN0', sn) if False else None
    gs = w.s([lp.gn, sn], 'nn0addcld', '( %s -> ( G + S ) e. NN0 )' % ps)
    hsl = linarith(w, ps, [sle, lp.rle], 'S <_ H', closure=cl)
    hs = w.s([sn, lp.hn, hsl, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( H - S ) e. NN0 )' % ps)
    dj = updcl(w, ps, 'D', 'J', EW('( G + S )', 'Y'), tv, dd, kJ['kd'],
               w.s([ewg(w, ps, '( G + S )', gs, 'Y', lp.c[WRD('Y', GAM)]), kJ['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, EW('( G + S )', 'Y'), GX('J'))))
    dfc = updcl(w, ps, UP('D', 'J', EW('( G + S )', 'Y')), 'I', EW('( H - S )', 'Z'), tv, dj, kI['kd'],
                w.s([ewg(w, ps, '( H - S )', hs, 'Z', lp.c[WRD('Z', GAM)]), kI['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, EW('( H - S )', 'Z'), GX('I'))))
    ss = clnss(w, ps, 'E', NFR, QCLS, DFIN, nss)
    d2c = cfgcl(w, ps, 'E', QCLS, DFIN, tv, lp.c['E e. ( 2nd ` ( 1st ` T ) )'], qss, dfc)
    t3 = hrssd(w, ps, lp.mk['phm'], t2, C2, D2, n2, CLN('E', QCLS, DFIN), ss, d2c)
    w.lines[-1] = w.lines[-1].replace(t3 + ':', 'qed:', 1)
    return w.run()


STMTS = {}
STMTS['tmipgr'] = '( %s -> %s )' % (cj(T_R), CONCL_R)
STMTS['tmipgt'] ='( %s -> ( %s /\\ %s /\\ %s ) )' % (PHL, TYP, EXITT, cj(PRO))
STMTS['tmipgl'] = '( %s -> %s )' % (PHL, GCONCL)
STMTS['tmipgi2'] = '( %s -> %s )' % (PSI, TRI2)
STMTS['tmipgi3'] = '( %s -> ( %s /\\ %s ) )' % (PSI3, TRI3, HLD3)
STMTS['tmipgi1'] = '( %s -> ( %s /\\ %s ) )' % (PSI, cj(BODY[0]), TRI1)
STMTS['tmipgi4'] = '( %s -> %s )' % (PSI4, DA)
STMTS['tmipgi5'] = '( %s -> %s )' % (PSI5, DA2)
STMTS['tmipgi6'] = '( %s -> %s )' % (PSI, DISJ)
STMTS['tmipgi2'] = '( %s -> %s )' % (PSI, TRI2)
STMTS['tmipgi3'] = '( %s -> ( %s /\\ %s ) )' % (PSI3, TRI3, HLD3)

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
