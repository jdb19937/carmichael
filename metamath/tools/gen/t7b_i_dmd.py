"""T7b: the shift-down loop of the division at the machine: the blocks of
~ tm2fdmcv 's antecedent at the families of blueprint section 3.

  tmidmd1   per iteration: the divisor's top letter, the stack step, the loop
            test, popBit's interface, the class typings
  tmidmd2   per iteration: predNum j s , and dup ; dup ; cmpFrag
  tmidmd3   per iteration: isZero j s , and the ite (subtract or skip)
  tmidmdt   the typings over ( 0 ... R ) and the exit test

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_i_dmd.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith, lineq, nlinarith
from t7_e_cmp import machine
from tmdlib import up8g
from t7b_g_dmu import STMT_DDC, STMT_DSI, NCM, MXLL, MXA_
from t7b_h_dmq import T_GDM, fv, rab_elim, ifmax_le, cngt_val
from t7b_f_nat import ST_STP

SEL = sys.argv[1:]
K6 = ['K', 'J', 'I', "I'", 'I"', 'I0']
PV = "P'"
DATA_D = ((('F e. NN0', 'G e. NN', 'R e. NN0'), ('R <_ %s' % NF, 'F < ( ( 2 ^ R ) x. G )')),
          ((WRD('X', GAM), WRD('Y', GAM), STKD('D')), '%s = %s' % (PV, PDF)))


def DMAP(P='P', E='E'):
    lm = FRAGS['dmd'].lmap(P, E)
    m = {'X': XDF, 'Y"': YDF, 'H': HDF, 'Q': QDF, 'P': PV, 'N': NDF, 'N1': NSF, 'N"': NSF, 'N0': N0F, "R'": 'R', 'Z0': Z0B,
         'F': 'TMrdBit', 'C"': CNFL, 'C': CNGT, 'T1': T1B, 'T"': TQB, 'T0': T0B, "T'": TPB, "A'": E}
    for g in ['A"', 'A0', 'B"', 'D0', 'E0', 'B1_', 'E"', 'G0']:
        m[g] = lm[g]
    return m


def dblocks():
    """the down-loop leaves of tm2fdmcv at DMAP: typing, the per-iteration body tree, exit"""
    m = DMAP()
    typ = tsub_text(T_GDM[1][1][1][0], m)
    per = T_GDM[1][1][1][1]
    pre = "A. i e. ( 0 ..^ R' ) "
    assert per.startswith(pre)
    body = tsub(parse_conj(per[len(pre):]), m)
    ex = tsub_text(T_GDM[1][1][2][0], m)
    return typ, body, ex


def PH_D():
    return ((T_PHM7, FRAGS['dmd'].pred()), (idx_tree(K6), dist_tree(K6)), DATA_D)


PS = '( %s /\\ i e. ( 0 ..^ R ) )'


def nsf_val(w, ps, inn, tmst_ex, NSI):
    """( ps -> ( NSF ` i ) = TMSt ) by fvmptg (the antecedent binds k)"""
    cg = w.s([], 'eqidd', '( k = i -> TMSt = TMSt )')
    fe = w.s([], 'eqid', '%s = %s' % (NSF, NSF))
    g = w.s([cg, fe], 'fvmptg', '( ( i e. NN0 /\\ TMSt e. _V ) -> %s = TMSt )' % NSI)
    return w.s([inn, w.s([tmst_ex], 'a1i', '( %s -> TMSt e. _V )' % ps), g], 'syl2anc', '( %s -> %s = TMSt )' % (ps, NSI))


class Dn:
    """shared facts at the iteration i of the shift-down loop, under ps = ( ph /\\ i e. ( 0 ..^ R ) )"""
    def __init__(self, w, ph, c, mk, ne, closed_range=False):
        self.w, self.ph, self.c, self.mk, self.ne0 = w, ph, c, mk, ne
        self.ps = ps = (PS % ph) if not closed_range else ('( %s /\\ i e. ( 0 ... R ) )' % ph if closed_range is True else ph)
        L = self.L
        if closed_range == 'none':
            self.fn, self.gn, self.rn = c['F e. NN0'], c['G e. NN'], c['R e. NN0']
            self.rle, self.rlt = c['R <_ %s' % NF], c['F < ( ( 2 ^ R ) x. G )']
            self.cl = Closure(w, ps, {'F': ('NN0', self.fn), 'G': ('NN', self.gn), 'R': ('NN0', self.rn)})
            self.memo = {}
            self.ne = ne
            kk = mk['k']
            self.mkp = {'tv': mk['tv'], 'k': {s: {'kd': kk[s]['kd'], 'wge': kk[s]['wge']} for s in K6}}
            return
        if closed_range:
            self.ii = w.s([], 'simpr', '( %s -> i e. ( 0 ... R ) )' % ps)
            self.inn = w.s([self.ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % ps)
            self.ile = w.s([self.ii, w.inst('elfzle2')], 'syl', '( %s -> i <_ R )' % ps)
            self.fn, self.gn, self.rn = L(c['F e. NN0']), L(c['G e. NN']), L(c['R e. NN0'])
            self.rle, self.rlt = L(c['R <_ %s' % NF]), L(c['F < ( ( 2 ^ R ) x. G )'])
            self.cl = Closure(w, ps, {'i': ('NN0', self.inn), 'F': ('NN0', self.fn), 'G': ('NN', self.gn), 'R': ('NN0', self.rn)})
            self.memo = {}
            self.ne = lambda a, b: w.s([ne(a, b)], 'adantr', '( %s -> %s =/= %s )' % (ps, a, b))
            kk = mk['k']
            self.mkp = {'tv': L(mk['tv']), 'k': {s: {'kd': L(kk[s]['kd']), 'wge': L(kk[s]['wge'])} for s in K6}}
            return
        self.ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ R ) )' % ps)
        self.inn = w.s([self.ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
        self.ilt = w.s([self.ii, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ps)
        self.fn, self.gn, self.rn = L(c['F e. NN0']), L(c['G e. NN']), L(c['R e. NN0'])
        self.rle, self.rlt = L(c['R <_ %s' % NF]), L(c['F < ( ( 2 ^ R ) x. G )'])
        self.cl = Closure(w, ps, {'i': ('NN0', self.inn), 'F': ('NN0', self.fn), 'G': ('NN', self.gn), 'R': ('NN0', self.rn)})
        cl = self.cl
        self.i1 = '( i + 1 )'
        self.i1n = w.s([self.inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ps)
        zl = w.s([cl.mem('i', 'ZZ'), cl.mem('R', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < R <-> ( i + 1 ) <_ R ) )' % ps)
        self.i1le = w.s([self.ilt, zl], 'mpbid', '( %s -> ( i + 1 ) <_ R )' % ps)
        self.ile = w.s([self.ilt], 'ltled', '( %s -> i <_ R )' % ps)
        self.memo = {}
        self.ne = lambda a, b: w.s([ne(a, b)], 'adantr', '( %s -> %s =/= %s )' % (ps, a, b))
        kk = mk['k']
        self.mkp = {'tv': L(mk['tv']), 'k': {s: {'kd': L(kk[s]['kd']), 'wge': L(kk[s]['wge'])} for s in K6}}

    def L(self, st):
        if self.ps == self.ph:
            return st
        return self.w.s([st], 'adantr', '( %s -> %s )' % (self.ps, concl(self.w, self.ph, st)))

    def at(self, t, tn, tle):
        """facts at the index t (tn : t e. NN0, tle : t <_ R)"""
        if t in self.memo:
            return self.memo[t]
        w, ps, cl = self.w, self.ps, self.cl
        L = self.L
        mk = self.mk
        r = {}
        rt = '( R - %s )' % t
        r['rt'] = w.s([tn, self.rn, tle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ps, rt))
        cl.have(rt, 'NN0', r['rt'])
        d = DV(t)
        r['dvn'] = cl.mem(d, 'NN')
        cl.have(d, 'NN', r['dvn'])
        # X
        md = '( F mod %s )' % d
        mdz = cl.mem(md, 'ZZ')
        nfn = self.nfn()
        xb = '( %s bwrd %s )' % (md, NF)
        r['xb'] = w.s([mdz, nfn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, xb))
        r['xw'] = wgcat(w, ps, '( inclBool o. %s )' % xb, YXt('X'), wib(w, ps, xb, r['xb']), wg4(w, ps, 'X', L(self.c[WRD('X', GAM)])))
        # Y"
        b0 = closed(w, ps, '0el2o', '(/) e. 2o')
        rw = w.s([b0, r['rt'], w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS %s ) e. Word 2o )' % (ps, rt))
        r['rw'] = rw
        r['sh'] = w.s([rw, self.eg(), w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, SHG(rt)))
        r['yw'] = wgcat(w, ps, '( inclBool o. %s )' % SHG(rt), YXt('Y'), wib(w, ps, SHG(rt), r['sh']), wg4(w, ps, 'Y', L(self.c[WRD('Y', GAM)])))
        # H
        fq = '( |_ ` ( F / %s ) )' % d
        fqz = cl.mem(fq, 'ZZ')
        hb = '( %s bwrd %s )' % (fq, t)
        r['hb'] = w.s([fqz, tn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, hb))
        r['hw'] = wgcat(w, ps, '( inclBool o. %s )' % hb, YXt('( D ` I )'), wib(w, ps, hb, r['hb']), wg4(w, ps, '( D ` I )', self.dsw('I')))
        # Q
        eqg = w.s([r['rt'], w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` %s ) e. Word Gamma' )" % (ps, rt))
        r['qw'] = wgcat(w, ps, '( encNatGam ` %s )' % rt, YXt("( D ` I' )"), eqg, wg4(w, ps, "( D ` I' )", self.dsw("I'")))
        ex = lambda st, X: w.s([st], 'elexd', '( %s -> %s e. _V )' % (ps, X))
        r['xv'] = fv(w, ps, XDF, XDB, t, tn, ex(r['xw'], XDB(t)))
        r['yv'] = fv(w, ps, YDF, YDB, t, tn, ex(r['yw'], YDB(t)))
        r['hv'] = fv(w, ps, HDF, HDB, t, tn, ex(r['hw'], HDB(t)))
        r['qv'] = fv(w, ps, QDF, QDB, t, tn, ex(r['qw'], QDB(t)))
        # the family applications typed
        for f_, F_, B_ in [('x', XDF, XDB), ('y', YDF, YDB), ('h', HDF, HDB), ('q', QDF, QDB)]:
            r[f_ + 'g'] = w.s([r[f_ + 'v'], r[f_ + 'w']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ps, FAPP(F_, t)))
        # the stacks PDB( t )
        S = Stacks(w, ps, self.mkp, 'D', L(self.c[STKD('D')]), self.ne, {})
        S = S.upd("I'", FAPP(QDF, t), r['qg']).upd('J', FAPP(YDF, t), r['yg']).upd('I', FAPP(HDF, t), r['hg']).upd('K', FAPP(XDF, t), r['xg'])
        assert S.D == PDB(t), (S.D, PDB(t))
        r['S'] = S
        pv0 = mval(w, ps, 'j', 'NN0', PDB, t, tn, w.s([S.memb], 'elexd', '( %s -> %s e. _V )' % (ps, PDB(t))))
        pe = w.s([L(self.c['%s = %s' % (PV, PDF)])], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, PV, t, PDF, t))
        r['pv'] = w.s([pe, pv0], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PV, t, PDB(t)))
        self.memo[t] = r
        return r

    def nfn(self):
        if 'nfn' not in self.memo:
            w, ps = self.w, self.ps
            ef = w.s([self.fn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ps)
            self.memo['ef'] = ef
            self.memo['nfn'] = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF))
            self.cl.have(NF, 'NN0', self.memo['nfn'])
        return self.memo['nfn']

    def eg(self):
        if 'eg' not in self.memo:
            w, ps = self.w, self.ps
            gn0 = w.s([self.gn, w.inst('nnnn0')], 'syl', '( %s -> G e. NN0 )' % ps)
            self.memo['gn0'] = gn0
            self.memo['eg'] = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, EG))
        return self.memo['eg']

    def dsw(self, s):
        key = 'ds' + s
        if key not in self.memo:
            w, ps = self.w, self.ps
            mk = self.mk
            st = stkfv(w, ps, 'D', s, self.mkp['tv'], self.L(self.c[STKD('D')]), self.mkp['k'][s]['kd'])
            self.memo[key] = w.s([st, self.mkp['k'][s]['wge']], 'eleqtrd', "( %s -> ( D ` %s ) e. Word Gamma' )" % (ps, s))
        return self.memo[key]

    def a_0(self):
        return self.at('i', self.inn, self.ile)

    def a_1(self):
        return self.at('( i + 1 )', self.i1n, self.i1le)


def tmidmd1():
    lab = 'tmidmd1'
    typ, body, ex = dblocks()
    T = PH_D()
    ph = cj(T)
    B0, B1, B2 = body
    C = '( ( %s /\\ i e. ( 0 ..^ R ) ) -> ( %s /\\ %s ) )' % (ph, cj(B0), cj(B1))
    w = W(lab, 'One iteration of the shift-down loop of Lean\'s ` divmodCore ` at the machine, its data (Lean '
               '` DmDownInv ` ): the divisor on ` y ` starts with a zero bit, the stacks of iteration ` i + 1 ` are four '
               'updates of those of iteration ` i ` , the loop test ( ` flag ` false) holds, ` popBit ` lands in a '
               'state, and the intermediate classes are classes of states.')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K6)
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    dn = Dn(w, ph, c, mk, ne)
    ps = dn.ps
    L = dn.L
    a0, a1 = dn.a_0(), dn.a_1()
    # ---- B000: ( ( P ` i ) ` J ) = ( <" Z0 "> ++ ( Y" ` ( i + 1 ) ) )
    S0 = a0['S']
    pj = w.s([w.s([a0['pv']], 'fveq1d', '( %s -> ( ( %s ` i ) ` J ) = ( %s ` J ) )' % (ps, PV, PDB('i'))), S0.val('J')[1]], 'eqtrd',
             '( %s -> ( ( %s ` i ) ` J ) = %s )' % (ps, PV, FAPP(YDF, 'i')))
    pj2 = w.s([pj, a0['yv']], 'eqtrd', '( %s -> ( ( %s ` i ) ` J ) = %s )' % (ps, PV, YDB('i')))
    # R - i = ( R - ( i + 1 ) ) + 1
    cl = dn.cl
    E1 = '( R - ( i + 1 ) )'
    ri = lineq(w, ps, '( R - i )', '( %s + 1 )' % E1, closure=cl)
    shq = w.s([w.s([ri], 'oveq2d', '( %s -> ( (/) repeatS ( R - i ) ) = ( (/) repeatS ( %s + 1 ) ) )' % (ps, E1))], 'oveq1d',
              '( %s -> %s = %s )' % (ps, SHG('( R - i )'), SHG('( %s + 1 )' % E1)))
    v1 = w.s([dn.eg(), a1['rt'], w.inst('tmidvw1')], 'syl2anc', '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ ( inclBool o. %s ) ) )'
             % (ps, SHG('( %s + 1 )' % E1), Z0B, SHG(E1)))
    v0 = w.s([w.s([shq], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. %s ) )' % (ps, SHG('( R - i )'), SHG('( %s + 1 )' % E1))), v1],
             'eqtrd', '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ ( inclBool o. %s ) ) )' % (ps, SHG('( R - i )'), Z0B, SHG(E1)))
    v2 = w.s([v0], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) )' % (ps, YDB('i'), Z0B, SHG(E1), YXt('Y')))
    zf = closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'")
    zv = w.s([zf, closed(w, ps, '0el2o', '(/) e. 2o')], 'ffvelcdmd', "( %s -> ( inclBool ` (/) ) e. Gamma' )" % ps)
    zeq = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ps, Z0B))
    zg = w.s([zeq, zv], 'eqeltrrd', "( %s -> %s e. Gamma' )" % (ps, Z0B))
    s1g = w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, Z0B))
    ca = w.s([s1g, wib(w, ps, SHG(E1), a1['sh']), wg4(w, ps, 'Y', L(c[WRD('Y', GAM)])), w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ps, Z0B, SHG(E1), YXt('Y'), Z0B, YDB('( i + 1 )')))
    ys = w.s([v2, ca], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ps, YDB('i'), Z0B, YDB('( i + 1 )')))
    y1r = w.s([a1['yv']], 'oveq2d', '( %s -> ( <" %s "> ++ %s ) = ( <" %s "> ++ %s ) )' % (ps, Z0B, FAPP(YDF, '( i + 1 )'), Z0B, YDB('( i + 1 )')))
    b000 = w.s([w.s([pj2, ys], 'eqtrd', '( %s -> ( ( %s ` i ) ` J ) = ( <" %s "> ++ %s ) )' % (ps, PV, Z0B, YDB('( i + 1 )'))), y1r], 'eqtr4d',
               '( %s -> %s )' % (ps, B0[0][0]))
    # ---- B001: the stack step by tm2stkup8
    S1 = a1['S']
    tv = dn.mkp['tv']
    dd = L(c[STKD('D')])
    idx = tuple(dn.mkp['k'][s]['kd'] for s in ["I'", 'J', 'I', 'K'])
    nes = {'ab': dn.ne("I'", 'J'), 'ac': dn.ne("I'", 'I'), 'ad': dn.ne("I'", 'K'), 'bc': dn.ne('J', 'I'), 'bd': dn.ne('J', 'K'), 'cd': dn.ne('I', 'K')}
    togk = lambda X, s, g: w.s([g, dn.mkp['k'][s]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s)))
    i1 = '( i + 1 )'
    vals = (FAPP(QDF, 'i'), FAPP(QDF, i1), FAPP(YDF, 'i'), FAPP(YDF, i1), FAPP(HDF, 'i'), FAPP(HDF, i1), FAPP(XDF, 'i'), FAPP(XDF, i1))
    wds = (togk(vals[0], "I'", a0['qg']), togk(vals[1], "I'", a1['qg']), togk(vals[2], 'J', a0['yg']), togk(vals[3], 'J', a1['yg']),
           togk(vals[4], 'I', a0['hg']), togk(vals[5], 'I', a1['hg']), togk(vals[6], 'K', a0['xg']), togk(vals[7], 'K', a1['xg']))
    col, RHS = up8g(w, ps, 'D', "I'", 'J', 'I', 'K', vals, tv, dd, nes, idx, wds)
    assert RHS == PDB(i1)
    UP4P = lambda D_: UP(UP(UP(UP(D_, "I'", vals[1]), 'J', vals[3]), 'I', vals[5]), 'K', vals[7])
    rw_, new = w.rewrite(UP4P(FAPP(PV, 'i')), {FAPP(PV, 'i'): (PDB('i'), a0['pv'])}, ps)
    assert new == UP4P(PDB('i')), new
    e = w.s([rw_, col], 'eqtrd', '( %s -> %s = %s )' % (ps, UP4P(FAPP(PV, 'i')), RHS))
    b001 = w.s([a1['pv'], e], 'eqtr4d', '( %s -> %s )' % (ps, B0[0][1]))
    # ---- B010: the loop test on ( N ` i )
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, NDF)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, ps, st)))
    nv = fv(w, ps, NDF, NDB, 'i', dn.inn, rabV(w, ps, NDB('i')))
    mi = w.s([w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, NDF)), Lm(nv)], 'eleqtrd', '( %s -> m e. %s )' % (pm, NDB('i')))
    IFI = 'if ( i = R , 1o , (/) )'
    mm, mc = rab_elim(w, pm, NDB('i'), lambda h: '( TMfl ` %s ) = %s' % (h, IFI), 'm', mi)
    ine = w.s([w.s([cl.mem('i', 'RR'), dn.ilt], 'ltned' if False else 'jca', '') if False else None], '', '') if False else None
    ne_ir = w.s([dn.ilt], 'ltned', '( %s -> i =/= R )' % ps)
    nir = w.s([ne_ir], 'neneqd', '( %s -> -. i = R )' % ps)
    iff = w.s([nir], 'iffalsed', '( %s -> %s = (/) )' % (ps, IFI))
    fl0 = w.s([mc, Lm(iff)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    X_of = lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t
    xex = ifex_closed(w, pm, '( TMfl ` m ) = 1o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', X_of, 'm', mm, xex)
    n1 = not1o(w, pm, fl0, 'TMfl', 'm')
    it = w.s([n1], 'iffalsed', '( %s -> %s = 1o )' % (pm, X_of('m')))
    ht = w.s([w.s([cv, it], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CNFL))], 'ralrimiva', '( %s -> %s )' % (ps, B0[1][0]))
    # ---- B011: popBit lands in a state
    NSI = FAPP(NSF, 'i')
    tmst_ex = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    nsv = nsf_val(w, ps, dn.inn, tmst_ex, NSI)
    pr = '( %s /\\ r e. %s )' % (ps, NSI)
    Lr = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pr, concl(w, ps, st)))
    rt = w.s([w.s([], 'simpr', '( %s -> r e. %s )' % (pr, NSI)), Lr(nsv)], 'eleqtrd', '( %s -> r e. TMSt )' % pr)
    fb = w.s([closed(w, pr, 'tmcrdbitf', "TMrdBit e. ( TMSt ^m ( TMSt X. ( Gamma' |_| 1o ) ) )"), w.inst('elmapi')], 'syl',
             "( %s -> TMrdBit : ( TMSt X. ( Gamma' |_| 1o ) ) --> TMSt )" % pr)
    zgr = w.s([zg], 'adantr', "( %s -> %s e. Gamma' )" % (pr, Z0B))
    iz = w.s([zgr, w.inst('djulcl')], 'syl', "( %s -> ( inl ` %s ) e. ( Gamma' |_| 1o ) )" % (pr, Z0B))
    op = w.s([rt, iz], 'opelxpd', "( %s -> <. r , ( inl ` %s ) >. e. ( TMSt X. ( Gamma' |_| 1o ) ) )" % (pr, Z0B))
    fvv = w.s([fb, op], 'ffvelcdmd', '( %s -> ( TMrdBit ` <. r , ( inl ` %s ) >. ) e. TMSt )' % (pr, Z0B))
    fvv2 = w.s([fvv, w.s([Lr(nsv)], 'eqcomd', '( %s -> TMSt = %s )' % (pr, NSI))], 'eleqtrd', '( %s -> ( TMrdBit ` <. r , ( inl ` %s ) >. ) e. %s )' % (pr, Z0B, NSI))
    pif = w.s([fvv2], 'ralrimiva', '( %s -> %s )' % (ps, B0[1][1]))
    # ---- B1: the classes
    seq = L(mk['seq'])
    nss = w.s([nsv, w.s([seq], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ps)], 'eqtrd', '( %s -> %s = ( 2nd ` T ) )' % (ps, NSI))
    nss2 = w.s([nss], 'eqimssd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, NSI))
    n0v = fv(w, ps, N0F, N0B, 'i', dn.inn, rabV(w, ps, N0B('i')))
    n0s = w.s([n0v, w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % N0B('i'))], 'a1i', '( %s -> %s C_ TMSt )' % (ps, N0B('i'))), seq], 'sseqtrrd',
                         '( %s -> %s C_ ( 2nd ` T ) )' % (ps, N0B('i')))], 'eqsstrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, FAPP(N0F, 'i')))
    b1 = w.s([w.s([nss2, nss2], 'jca', '( %s -> %s )' % (ps, cj(B1[0]))), n0s], 'jca', '( %s -> %s )' % (ps, cj(B1)))
    b0 = w.s([w.s([b000, b001], 'jca', '( %s -> %s )' % (ps, cj(B0[0]))), w.s([ht, pif], 'jca', '( %s -> %s )' % (ps, cj(B0[1])))], 'jca',
             '( %s -> %s )' % (ps, cj(B0)))
    w.qed([b0, b1], 'jca', C)
    return w.run()



def setup(lab, desc, concl_fn):
    typ, body, ex = dblocks()
    T = PH_D()
    ph = cj(T)
    w = W(lab, desc)
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K6)
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    dn = Dn(w, ph, c, mk, ne)
    f = FRAGS['dmd']
    un = unfold_all(w, ph, c[f.pred()], 'dmd', K6, 'P', 'E', rec=False)
    base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt']}
    ex_ = {k: dn.L(v) for k, v in list(base.items()) + list(un.items())}
    for leaf_ in flat(T):
        ex_[leaf_] = dn.L(c[leaf_])
    return w, T, ph, c, mk, dn, body, ex_


def gamma_word_eq(w, ps, X, s_, st, g):
    """nothing: helper placeholder"""
    return st


def bl_le_n(dn, t, tn, tle):
    """( ps -> ( # ` ( encodeNat ` t ) ) <_ n ) for 0 <_ t <_ R"""
    w, ps, cl = dn.w, dn.ps, dn.cl
    nfn = dn.nfn()
    en = '( # ` ( encodeNat ` %s ) )' % t
    enbl = w.s([tn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` %s ) )' % (ps, en, t))
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    np = w.s([w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ps), nfn, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ps, NF, NF))
    cl.atom('( 2 ^ %s )' % NF)
    cl.have(t, 'NN0', tn)
    lt = linarith(w, ps, [tle, dn.rle, np], '%s < ( 2 ^ %s )' % (t, NF), closure=cl)
    bll = w.s([tn, nfn, lt, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` %s ) <_ %s )' % (ps, t, NF))
    return w.s([enbl, bll], 'eqbrtrd', '( %s -> %s <_ %s )' % (ps, en, NF))


def modle_pow(dn, t, a):
    """( ps -> ( F mod DV( t ) ) < ( 2 ^ n ) ) and ( ps -> ( F mod DV ) <_ F )"""
    w, ps, cl = dn.w, dn.ps, dn.cl
    d = DV(t)
    md = '( F mod %s )' % d
    fr = cl.mem('F', 'RR'); dp = w.s([a['dvn']], 'nnrpd', '( %s -> %s e. RR+ )' % (ps, d))
    mv = w.s([fr, dp, w.inst('modvalr')], 'syl2anc', '( %s -> %s = ( F - ( ( |_ ` ( F / %s ) ) x. %s ) ) )' % (ps, md, d, d))
    fq = '( |_ ` ( F / %s ) )' % d
    fqn = w.s([dn.fn, a['dvn'], w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, fq))
    cl.leaf(fq, 'NN0', fqn); cl.atom(md)
    cl.have(md, 'NN0', cl.mem(md, 'NN0') if False else w.s([cl.mem('F', 'ZZ'), a['dvn'], w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, md)))
    le = nlinarith(w, ps, [mv, cl.ge0(fq), cl.ge0(d)], '%s <_ F' % md, closure=cl, atoms=[fq, md])
    ef = dn.memo['ef'] if 'ef' in dn.memo else None
    dn.nfn()
    ef = dn.memo['ef']
    tl = w.s([ef, w.inst('tonatlt')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) < ( 2 ^ %s ) )' % (ps, NF))
    tf = w.s([dn.fn, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ps)
    fl = w.s([tf, tl], 'eqbrtrrd', '( %s -> F < ( 2 ^ %s ) )' % (ps, NF))
    cl.atom('( 2 ^ %s )' % NF)
    lt = linarith(w, ps, [le, fl], '%s < ( 2 ^ %s )' % (md, NF), closure=cl, atoms=[md])
    return lt, le, fl


def tmidmd2():
    lab = 'tmidmd2'
    w, T, ph, c, mk, dn, body, ex_ = setup(lab,
        'One iteration of the shift-down loop of Lean\'s ` divmodCore ` at the machine: ` predNum j s ` '
        'decrements the counter ` R - i ` , and ` dup y t s ; dup x s t ; cmpFrag t s ` compares the halved shift '
        '` 2 ^ ( R - i - 1 ) d ` with the remainder ` a mod ( 2 ^ ( R - i ) d ) ` .', None)
    B200, B201 = body[2][0]
    C = '( %s -> ( %s /\\ %s ) )' % (dn.ps, B200, B201)
    ps = dn.ps
    L = dn.L
    cl = dn.cl
    a0, a1 = dn.a_0(), dn.a_1()
    S0 = a0['S']
    PI = FAPP(PV, 'i')
    i1 = '( i + 1 )'
    RI, RI1 = '( R - i )', '( R - ( i + 1 ) )'
    phm = L(mk['phm']); tv = dn.mkp['tv']; seq = L(mk['seq'])
    kd = lambda s: dn.mkp['k'][s]['kd']
    togk = lambda X, s, g: w.s([g, dn.mkp['k'][s]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s)))
    # ( P ` i ) e. Stk and its values
    pim = w.s([a0['pv'], S0.memb], 'eqeltrd', '( %s -> %s e. %s )' % (ps, PI, STK_T))
    def pval(s):
        e = w.s([a0['pv']], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, PI, s, PDB('i'), s))
        return w.s([e, S0.val(s)[1]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PI, s, S0.val(s)[0]))
    # ---------------- predNum j s : B200
    rin = w.s([dn.ilt, w.s([cl.mem('i', 'ZZ'), cl.mem('R', 'ZZ'), w.inst('znnsub')], 'syl2anc', '( %s -> ( i < R <-> %s e. NN ) )' % (ps, RI))], 'mpbid',
              '( %s -> %s e. NN )' % (ps, RI))
    rin0 = w.s([rin, w.inst('nnnn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, RI))
    ER = '( encodeNat ` %s )' % RI
    erw = w.s([rin0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ER))
    eg = w.s([rin0, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (ps, RI, ER))
    WQ = CC('( inclBool o. %s )' % ER, YXt("( D ` I' )"))
    qe = w.s([w.s([pval("I'"), a0['qv']], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ps, PI, QDB('i'))),
              w.s([eg], 'oveq1d', '( %s -> %s = %s )' % (ps, QDB('i'), WQ))], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ps, PI, WQ))
    m1 = {'K': "I'", 'J': 'I"', 'P': PL('P', 4), 'E': PL('P', 0), 'L': ER, 'X': "( D ` I' )", 'D': PI}
    ex1 = dict(ex_)
    ex1.update({IDX("I'"): L(dn.c[IDX("I'")]), IDX('I"'): L(dn.c[IDX('I"')]), "I' =/= I\"": dn.ne("I'", 'I"'), WRD(ER, '2o'): erw,
                WRD("( D ` I' )", GAM): dn.dsw("I'"), STKD(PI): pim, "( %s ` I' ) = %s" % (PI, WQ): qe})
    t1, c1 = inst(w, ps, 'tmiprds', m1, Bld(w, ps, Ctx(w, ps, T, root=w.s([], 'simpl', '( %s -> %s )' % (ps, ph))), ex1))
    Ca, Da, n1 = triple_parts(c1)
    # pre class ( N ` i ) C_ S
    nv = fv(w, ps, NDF, NDB, 'i', dn.inn, rabV(w, ps, NDB('i')))
    nss = w.s([nv, w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NDB('i'))], 'a1i', '( %s -> %s C_ TMSt )' % (ps, NDB('i'))), seq], 'sseqtrrd',
                        '( %s -> %s C_ ( 2nd ` T ) )' % (ps, NDB('i')))], 'eqsstrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, FAPP(NDF, 'i')))
    AP = PL(PL('P', 4), 0)
    t1b = hrssc(w, ps, phm, t1, Ca, Da, n1, CLN(AP, FAPP(NDF, 'i'), PI), clnss(w, ps, AP, FAPP(NDF, 'i'), SS, PI, nss))
    # post: predBits ( enc ( R - i ) ) = enc ( R - ( i + 1 ) ) ; class S = ( NSF ` i )
    pe = w.s([rin, w.inst('tmcpredenc')], 'syl', '( %s -> ( predBits ` %s ) = ( encodeNat ` ( %s - 1 ) ) )' % (ps, ER, RI))
    r1 = lineq(w, ps, '( %s - 1 )' % RI, RI1, closure=cl)
    pe2 = w.s([pe, w.s([r1], 'fveq2d', '( %s -> ( encodeNat ` ( %s - 1 ) ) = ( encodeNat ` %s ) )' % (ps, RI, RI1))], 'eqtrd',
              '( %s -> ( predBits ` %s ) = ( encodeNat ` %s ) )' % (ps, ER, RI1))
    eg1 = w.s([a1['rt'], w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. ( encodeNat ` %s ) ) )' % (ps, RI1, RI1))
    wpe = w.s([w.s([pe2], 'coeq2d', '( %s -> ( inclBool o. ( predBits ` %s ) ) = ( inclBool o. ( encodeNat ` %s ) ) )' % (ps, ER, RI1)), eg1], 'eqtr4d',
              '( %s -> ( inclBool o. ( predBits ` %s ) ) = ( encNatGam ` %s ) )' % (ps, ER, RI1))
    wq1 = w.s([w.s([wpe], 'oveq1d', '( %s -> %s = %s )' % (ps, CC('( inclBool o. ( predBits ` %s ) )' % ER, YXt("( D ` I' )")), QDB(i1))),
               w.s([a1['qv']], 'eqcomd', '( %s -> %s = %s )' % (ps, QDB(i1), FAPP(QDF, i1)))], 'eqtrd',
              '( %s -> %s = %s )' % (ps, CC('( inclBool o. ( predBits ` %s ) )' % ER, YXt("( D ` I' )")), FAPP(QDF, i1)))
    Dpost0 = UP(PI, "I'", CC('( inclBool o. ( predBits ` %s ) )' % ER, YXt("( D ` I' )")))
    Dpost1 = UP(PI, "I'", FAPP(QDF, i1))
    assert Da == CLN(PL('P', 0), SS, Dpost0), Da
    ue = upeq(w, ps, PI, "I'", wq1, CC('( inclBool o. ( predBits ` %s ) )' % ER, YXt("( D ` I' )")), FAPP(QDF, i1))
    tmst_ex = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    NSI = FAPP(NSF, 'i')
    nsv = nsf_val(w, ps, dn.inn, tmst_ex, NSI)
    sn = w.s([seq, nsv], 'eqtr4d', '( %s -> ( 2nd ` T ) = %s )' % (ps, NSI))
    d1 = clnneq(w, ps, PL('P', 0), sn, SS, NSI, Dpost0)
    d2 = clneq(w, ps, PL('P', 0), NSI, ue, Dpost0, Dpost1)
    deq = w.s([d1, d2], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, CLN(PL('P', 0), NSI, Dpost1)))
    t1c, C1, D1, n1c = hrrw(w, ps, t1b, CLN(AP, FAPP(NDF, 'i'), PI), Da, n1, deq=deq)
    le1 = bl_le_n(dn, RI, rin0, w.s([cl.mem('R', 'RR'), cl.mem('i', 'RR'), cl.ge0('i') if False else w.s([dn.inn, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ i )' % ps)], 'subge02d' if False else 'jca', '') if False else
                      linarith(w, ps, [w.s([dn.inn, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ i )' % ps)], '%s <_ R' % RI, closure=cl))
    cl.have('( # ` %s )' % ER, 'NN0', w.s([erw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, ER)))
    cl.atom('( # ` %s )' % ER)
    b1 = linarith(w, ps, [le1], '%s <_ %s' % (n1c, T1B), closure=cl)
    t1d = hrle(w, ps, phm, t1c, C1, D1, n1c, T1B, cl.mem(T1B, 'NN0'), b1)
    assert '( %s -> %s )' % (ps, TRI(C1, D1, T1B)) == '( %s -> %s )' % (ps, B200), (TRI(C1, D1, T1B), B200)
    # ---------------- dup ; dup ; cmpFrag : B201
    Z0W = CC('<" %s ">' % Z0B, '( %s ` I )' % PI)
    S2 = UP(UP(Dpost1, 'J', FAPP(YDF, i1)), 'I', Z0W)
    # typing of S2 and its values at K and J
    zf = closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'")
    zv = w.s([zf, closed(w, ps, '0el2o', '(/) e. 2o')], 'ffvelcdmd', "( %s -> ( inclBool ` (/) ) e. Gamma' )" % ps)
    zeq = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ps, Z0B))
    zg = w.s([zeq, zv], 'eqeltrrd', "( %s -> %s e. Gamma' )" % (ps, Z0B))
    s1g = w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, Z0B))
    piI = w.s([pval('I'), a0['hg']], 'eqeltrd', "( %s -> ( %s ` I ) e. Word Gamma' )" % (ps, PI))
    z0w = wgcat(w, ps, '<" %s ">' % Z0B, '( %s ` I )' % PI, s1g, piI)
    SP = Stacks(w, ps, dn.mkp, PI, pim, dn.ne, {'K': (FAPP(XDF, 'i'), pval('K'), a0['xg'])})
    SP = SP.upd("I'", FAPP(QDF, i1), a1['qg']).upd('J', FAPP(YDF, i1), a1['yg']).upd('I', Z0W, z0w)
    assert SP.D == S2, (SP.D, S2)
    XB = '( ( F mod %s ) bwrd %s )' % (DV('i'), NF)
    WX = CC('( inclBool o. %s )' % XB, YXt('X'))
    sk = w.s([SP.val('K')[1], a0['xv']], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, S2, WX))
    WY = CC('( inclBool o. %s )' % SHG(RI1), YXt('Y'))
    sj = w.s([SP.val('J')[1], a1['yv']], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ps, S2, WY))
    m2 = {'P': PL('P', 5), "P'": PL('P', 6), 'P"': PL('P', 7), 'E': PL('P', 2), 'L': XB, "L'": SHG(RI1), 'X': 'X', 'Y': 'Y', 'D': S2}
    ex2 = dict(ex_)
    ex2.update({WRD(XB, '2o'): a0['xb'], WRD(SHG(RI1), '2o'): a1['sh'], STKD(S2): SP.memb,
                '( %s ` K ) = %s' % (S2, WX): sk, '( %s ` J ) = %s' % (S2, WY): sj})
    for s_ in ['K', 'J', 'I"', 'I0']:
        ex2[IDX(s_)] = L(dn.c[IDX(s_)])
    for a_, b_ in [('K', 'J'), ('K', 'I"'), ('K', 'I0'), ('J', 'I"'), ('J', 'I0'), ('I"', 'I0')]:
        ex2['%s =/= %s' % (a_, b_)] = dn.ne(a_, b_)
    t2, c2 = inst(w, ps, 'tmidm3', m2, Bld(w, ps, Ctx(w, ps, T, root=w.s([], 'simpl', '( %s -> %s )' % (ps, ph))), ex2))
    Cb, Db, n2 = triple_parts(c2)
    # pre class S = ( NSF ` i )
    DD0 = PL(PL('P', 5), 0)
    e_pre = clnneq(w, ps, DD0, sn, SS, NSI, S2)
    # post class { cmp = toNat L' Ncmp toNat L } = ( N0F ` i )
    NCMI = tsub_text(NCM, m2)
    lt_, mle_, fl_ = modle_pow(dn, 'i', a0)
    md = '( F mod %s )' % DV('i')
    mdn = w.s([cl.mem('F', 'ZZ'), a0['dvn'], w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, md))
    tx = w.s([mdn, dn.nfn(), lt_, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ps, XB, md))
    tsh = w.s([dn.eg(), a1['rt'], w.inst('tonatrep0a')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( 2 ^ %s ) x. ( toNat ` %s ) ) )' % (ps, SHG(RI1), RI1, EG))
    tg = w.s([dn.memo['gn0'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ps, EG))
    dvi1 = DV(i1)
    tsh2 = w.s([tsh, w.s([tg], 'oveq2d', '( %s -> ( ( 2 ^ %s ) x. ( toNat ` %s ) ) = %s )' % (ps, RI1, EG, dvi1))], 'eqtrd',
               '( %s -> ( toNat ` %s ) = %s )' % (ps, SHG(RI1), dvi1))
    vv = w.s([tsh2, tx], 'oveq12d', '( %s -> ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) = ( %s Ncmp %s ) )' % (ps, SHG(RI1), XB, dvi1, md))
    ce = w.s([vv], 'eqeq2d', '( %s -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) <-> ( TMcmp ` h ) = ( %s Ncmp %s ) ) )' % (ps, SHG(RI1), XB, dvi1, md))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` %s ) ) <-> ( TMcmp ` h ) = ( %s Ncmp %s ) ) )'
                  % (ps, SHG(RI1), XB, dvi1, md))], 'rabbidva', '( %s -> %s = %s )' % (ps, NCMI, N0B('i')))
    n0v = fv(w, ps, N0F, N0B, 'i', dn.inn, rabV(w, ps, N0B('i')))
    ncls = w.s([rb, w.s([n0v], 'eqcomd', '( %s -> %s = %s )' % (ps, N0B('i'), FAPP(N0F, 'i')))], 'eqtrd', '( %s -> %s = %s )' % (ps, NCMI, FAPP(N0F, 'i')))
    assert Db == CLN(PL('P', 2), NCMI, S2), Db
    e_post = clnneq(w, ps, PL('P', 2), ncls, NCMI, FAPP(N0F, 'i'), S2)
    t2b, C2, D2, n2b = hrrw(w, ps, t2, Cb, Db, n2, ceq=e_pre, deq=e_post)
    # bound
    nfn = dn.nfn()
    ngn = w.s([dn.eg(), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NG))
    LSH = '( # ` %s )' % SHG(RI1)
    shl = w.s([a1['rw'], dn.eg(), w.inst('ccatlen')], 'syl2anc', '( %s -> %s = ( ( # ` ( (/) repeatS %s ) ) + %s ) )' % (ps, LSH, RI1, NG))
    rpl = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), a1['rt'], w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS %s ) ) = %s )' % (ps, RI1, RI1))
    LXB = '( # ` %s )' % XB
    xl = w.s([cl.mem(md, 'ZZ'), nfn, w.inst('bwrdlen')], 'syl2anc', '( %s -> %s = %s )' % (ps, LXB, NF))
    for a_, st_ in [(NG, ngn), (LSH, w.s([a1['sh'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LSH))),
                    ('( # ` ( (/) repeatS %s ) )' % RI1, w.s([a1['rw'], w.inst('lencl')], 'syl', '( %s -> ( # ` ( (/) repeatS %s ) ) e. NN0 )' % (ps, RI1))),
                    (LXB, w.s([a0['xb'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LXB)))]:
        cl.leaf(a_, 'NN0', st_)
    cl.atom(NF)
    r1le = linarith(w, ps, [w.s([dn.inn, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ i )' % ps)], '%s <_ R' % RI1, closure=cl)
    lsh_le = linarith(w, ps, [shl, rpl, r1le, dn.rle], '%s <_ ( %s + %s )' % (LSH, NF, NG), closure=cl)
    lx_le = linarith(w, ps, [xl, cl.ge0(NG)], '%s <_ ( %s + %s )' % (LXB, NF, NG), closure=cl)
    MX = tsub_text(MXLL, m2)
    mxl = ifmax_le(w, ps, LSH, LXB, '( %s + %s )' % (NF, NG), cl.mem(LSH, 'RR'), cl.mem(LXB, 'RR'), cl.mem('( %s + %s )' % (NF, NG), 'RR'), lsh_le, lx_le)
    cl.leaf(MX, 'NN0', w.s([cl.mem(LXB, 'NN0'), cl.mem(LSH, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (ps, MX)))
    b2 = linarith(w, ps, [lsh_le, xl, mxl], '%s <_ %s' % (n2b, TQB), closure=cl)
    t2c = hrle(w, ps, phm, t2b, C2, D2, n2b, TQB, cl.mem(TQB, 'NN0'), b2)
    assert TRI(C2, D2, TQB) == B201, (TRI(C2, D2, TQB), B201)
    w.qed([t1d, t2c], 'jca', C)
    return w.run()



def common_i(w, dn, T, ph, mk):
    """facts used by the iteration's second half: the stacks S2 (after predNum , popBit , pushSym q 0),
    their values, typing"""
    ps, L, cl = dn.ps, dn.L, dn.cl
    a0, a1 = dn.a_0(), dn.a_1()
    S0 = a0['S']
    PI = FAPP(PV, 'i')
    i1 = '( i + 1 )'
    RI1 = '( R - ( i + 1 ) )'
    pim = w.s([a0['pv'], S0.memb], 'eqeltrd', '( %s -> %s e. %s )' % (ps, PI, STK_T))
    def pval(s):
        e = w.s([a0['pv']], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ps, PI, s, PDB('i'), s))
        return w.s([e, S0.val(s)[1]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ps, PI, s, S0.val(s)[0]))
    zf = closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'")
    zv = w.s([zf, closed(w, ps, '0el2o', '(/) e. 2o')], 'ffvelcdmd', "( %s -> ( inclBool ` (/) ) e. Gamma' )" % ps)
    zeq = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ps, Z0B))
    zg = w.s([zeq, zv], 'eqeltrrd', "( %s -> %s e. Gamma' )" % (ps, Z0B))
    s1g = w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, Z0B))
    piI = w.s([pval('I'), a0['hg']], 'eqeltrd', "( %s -> ( %s ` I ) e. Word Gamma' )" % (ps, PI))
    Z0W = CC('<" %s ">' % Z0B, '( %s ` I )' % PI)
    z0w = wgcat(w, ps, '<" %s ">' % Z0B, '( %s ` I )' % PI, s1g, piI)
    SP = Stacks(w, ps, dn.mkp, PI, pim, dn.ne, {'K': (FAPP(XDF, 'i'), pval('K'), a0['xg']), 'I': (FAPP(HDF, 'i'), pval('I'), a0['hg'])})
    SP = SP.upd("I'", FAPP(QDF, i1), a1['qg']).upd('J', FAPP(YDF, i1), a1['yg']).upd('I', Z0W, z0w)
    return dict(PI=PI, pim=pim, pval=pval, SP=SP, s1g=s1g, zg=zg, Z0W=Z0W, a0=a0, a1=a1, piI=piI)


def tmidmd3():
    lab = 'tmidmd3'
    w, T, ph, c, mk, dn, body, ex_ = setup(lab,
        'One iteration of the shift-down loop of Lean\'s ` divmodCore ` at the machine: its final ` isZero j s ` '
        'sets ` flag ` to whether the counter ` R - ( i + 1 ) ` is zero, i.e. whether this was the last iteration.', None)
    B21 = body[2][1]
    C = '( %s -> %s )' % (dn.ps, B21)
    ps, L, cl = dn.ps, dn.L, dn.cl
    ci = common_i(w, dn, T, ph, mk)
    a1 = ci['a1']
    i1 = '( i + 1 )'; RI1 = '( R - ( i + 1 ) )'
    phm = L(mk['phm'])
    SP = ci['SP']
    S3s = SP.upd('K', FAPP(XDF, i1), a1['xg']).upd('I', FAPP(HDF, i1), a1['hg'])
    S3 = S3s.D
    ER = '( encodeNat ` %s )' % RI1
    erw = w.s([a1['rt'], w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ps, ER))
    eg = w.s([a1['rt'], w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. %s ) )' % (ps, RI1, ER))
    WQ = CC('( inclBool o. %s )' % ER, YXt("( D ` I' )"))
    qe = w.s([w.s([S3s.val("I'")[1], a1['qv']], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ps, S3, QDB(i1))),
              w.s([eg], 'oveq1d', '( %s -> %s = %s )' % (ps, QDB(i1), WQ))], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ps, S3, WQ))
    m1 = {'K': "I'", 'I': 'I"', 'P': PL('P', 11), 'E': 'E', 'L': ER, 'X': "( D ` I' )", 'D': S3}
    ex1 = dict(ex_)
    ex1.update({IDX("I'"): L(dn.c[IDX("I'")]), IDX('I"'): L(dn.c[IDX('I"')]), "I' =/= I\"": dn.ne("I'", 'I"'), WRD(ER, '2o'): erw,
                WRD("( D ` I' )", GAM): dn.dsw("I'"), STKD(S3): S3s.memb, "( %s ` I' ) = %s" % (S3, WQ): qe})
    t1, c1 = inst(w, ps, 'tmiizs', m1, Bld(w, ps, Ctx(w, ps, T, root=w.s([], 'simpl', '( %s -> %s )' % (ps, ph))), ex1))
    Ca, Da, n1 = triple_parts(c1)
    # post class: { fl = if ( toNat ER = 0 , .. ) } = ( NDF ` ( i + 1 ) )
    tr = w.s([a1['rt'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = %s )' % (ps, ER, RI1))
    e0 = w.s([tr], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> %s = 0 ) )' % (ps, ER, RI1))
    sb = w.s([cl.mem('R', 'CC'), cl.mem(i1, 'CC')], 'subeq0ad', '( %s -> ( %s = 0 <-> R = %s ) )' % (ps, RI1, i1))
    ec = w.s([], 'eqcom', '( R = %s <-> %s = R )' % (i1, i1))
    bb = w.s([w.s([e0, sb], 'bitrd', '( %s -> ( ( toNat ` %s ) = 0 <-> R = %s ) )' % (ps, ER, i1)), w.s([ec], 'a1i', '( %s -> ( R = %s <-> %s = R ) )' % (ps, i1, i1))],
             'bitrd', '( %s -> ( ( toNat ` %s ) = 0 <-> %s = R ) )' % (ps, ER, i1))
    IF0 = 'if ( ( toNat ` %s ) = 0 , 1o , (/) )' % ER
    IF1 = 'if ( %s = R , 1o , (/) )' % i1
    ib = w.s([bb], 'ifbid', '( %s -> %s = %s )' % (ps, IF0, IF1))
    ce = w.s([ib], 'eqeq2d', '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ps, IF0, IF1))
    NFL0 = '{ h e. TMSt | ( TMfl ` h ) = %s }' % IF0
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ps, IF0, IF1))], 'rabbidva',
             '( %s -> %s = %s )' % (ps, NFL0, NDB(i1)))
    nv1 = fv(w, ps, NDF, NDB, i1, dn.i1n, rabV(w, ps, NDB(i1)))
    ncls = w.s([rb, w.s([nv1], 'eqcomd', '( %s -> %s = %s )' % (ps, NDB(i1), FAPP(NDF, i1)))], 'eqtrd', '( %s -> %s = %s )' % (ps, NFL0, FAPP(NDF, i1)))
    assert Da == CLN('E', NFL0, S3), Da
    e_post = clnneq(w, ps, 'E', ncls, NFL0, FAPP(NDF, i1), S3)
    t2, C2, D2, n2 = hrrw(w, ps, t1, Ca, Da, n1, deq=e_post)
    le = bl_le_n(dn, RI1, a1['rt'], linarith(w, ps, [w.s([dn.inn, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ i )' % ps)], '%s <_ R' % RI1, closure=cl))
    cl.leaf('( # ` %s )' % ER, 'NN0', w.s([erw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ps, ER)))
    dn.nfn()
    b = linarith(w, ps, [le], '%s <_ %s' % (n2, TPB), closure=cl)
    hrle(w, ps, phm, t2, C2, D2, n2, TPB, cl.mem(TPB, 'NN0'), b, qed=True)
    assert TRI(C2, D2, TPB) == B21, (TRI(C2, D2, TPB), B21)
    return w.run()



def tmidmd4():
    lab = 'tmidmd4'
    w, T, ph, c, mk, dn, body, ex_ = setup(lab,
        'One iteration of the shift-down loop of Lean\'s ` divmodCore ` at the machine, its ` ite ` (Lean '
        '` divmod_step ` ): when the halved shift ` 2 ^ ( R - i - 1 ) d ` fits into the remainder, '
        '` dup y t s ; sub x t s x ; incr q s ` subtracts it and sets the new quotient bit; otherwise the '
        'remainder and the doubled quotient already are the next iteration\'s.', None)
    B22 = body[2][2]
    C = '( %s -> %s )' % (dn.ps, B22)
    ps, L, cl = dn.ps, dn.L, dn.cl
    ci = common_i(w, dn, T, ph, mk)
    a0, a1, PI, SP, pval = ci['a0'], ci['a1'], ci['PI'], ci['SP'], ci['pval']
    S2 = SP.D
    phm = L(mk['phm'])
    i1 = '( i + 1 )'; RI = '( R - i )'; RI1 = '( R - ( i + 1 ) )'
    D0, D1 = DV('i'), DV(i1)
    r_ = '( F mod %s )' % D0
    q_ = '( |_ ` ( F / %s ) )' % D0
    XB = '( %s bwrd %s )' % (r_, NF)
    dn.nfn(); dn.eg()
    # DV( i ) = 2 x. DV( i + 1 )
    ri = lineq(w, ps, RI, '( %s + 1 )' % RI1, closure=cl)
    e1 = w.s([w.s([ri], 'oveq2d', '( %s -> ( 2 ^ %s ) = ( 2 ^ ( %s + 1 ) ) )' % (ps, RI, RI1)),
              w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ps), a1['rt']], 'expp1d', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( ( 2 ^ %s ) x. 2 ) )' % (ps, RI1, RI1))],
             'eqtrd', '( %s -> ( 2 ^ %s ) = ( ( 2 ^ %s ) x. 2 ) )' % (ps, RI, RI1))
    P0, P1 = '( 2 ^ %s )' % RI, '( 2 ^ %s )' % RI1
    cl.have(P0, 'NN', cl.mem(P0, 'NN')); cl.have(P1, 'NN', cl.mem(P1, 'NN'))
    s1_ = w.s([e1], 'oveq1d', '( %s -> %s = ( ( %s x. 2 ) x. G ) )' % (ps, D0, P1))
    s2_ = lineq(w, ps, '( ( %s x. 2 ) x. G )' % P1, '( 2 x. %s )' % D1, closure=cl, products=True, atoms=[P0, P1])
    dvi = w.s([s1_, s2_], 'eqtrd', '( %s -> %s = ( 2 x. %s ) )' % (ps, D0, D1))
    S_ = D1
    s_nn = a1['dvn']
    stp = w.s([dn.fn, s_nn, w.inst('tmidvstp')], 'syl2anc', '( %s -> %s )' % (ps, tsub_text(split_imp(ST_STP)[1], {'S': S_})))
    stpt = parse_conj(tsub_text(split_imp(ST_STP)[1], {'S': S_}))
    st1 = w.s([stp], 'simpld', '( %s -> %s )' % (ps, stpt[0]))
    st0 = w.s([stp], 'simprd', '( %s -> %s )' % (ps, stpt[1]))
    R2s = '( F mod ( 2 x. %s ) )' % S_
    Q2s = '( |_ ` ( F / ( 2 x. %s ) ) )' % S_
    er = w.s([dvi], 'oveq2d', '( %s -> %s = %s )' % (ps, r_, R2s))
    eq_ = w.s([w.s([dvi], 'oveq2d', '( %s -> ( F / %s ) = ( F / ( 2 x. %s ) ) )' % (ps, D0, S_))], 'fveq2d', '( %s -> %s = %s )' % (ps, q_, Q2s))
    # q < 2 ^ i
    fqn = w.s([dn.fn, a0['dvn'], w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, q_))
    ea = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ps), dn.inn, a0['rt']], 'expaddd', '( %s -> ( 2 ^ ( i + %s ) ) = ( ( 2 ^ i ) x. %s ) )' % (ps, RI, P0))
    pc = w.s([cl.mem('i', 'CC'), cl.mem('R', 'CC')], 'pncan3d', '( %s -> ( i + %s ) = R )' % (ps, RI))
    e2r = w.s([w.s([pc], 'oveq2d', '( %s -> ( 2 ^ ( i + %s ) ) = ( 2 ^ R ) )' % (ps, RI)), ea], 'eqtr3d', '( %s -> ( 2 ^ R ) = ( ( 2 ^ i ) x. %s ) )' % (ps, P0))
    PI_ = '( 2 ^ i )'; PR = '( 2 ^ R )'
    cl.have(PI_, 'NN', cl.mem(PI_, 'NN')); cl.have(PR, 'NN', cl.mem(PR, 'NN'))
    f1_ = w.s([e2r], 'oveq1d', '( %s -> ( %s x. G ) = ( ( %s x. %s ) x. G ) )' % (ps, PR, PI_, P0))
    f2_ = lineq(w, ps, '( ( %s x. %s ) x. G )' % (PI_, P0), '( %s x. %s )' % (D0, PI_), closure=cl, products=True, atoms=[PI_, PR, P0])
    f3_ = w.s([f1_, f2_], 'eqtrd', '( %s -> ( %s x. G ) = ( %s x. %s ) )' % (ps, PR, D0, PI_))
    flt = w.s([dn.rlt, f3_], 'breqtrd', '( %s -> F < ( %s x. %s ) )' % (ps, D0, PI_))
    ldm = w.s([cl.mem('F', 'RR'), cl.mem(PI_, 'RR'), w.s([cl.mem(D0, 'RR'), cl.gt0(D0)], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (ps, D0, D0)),
               w.inst('ltdivmul')], 'syl3anc', '( %s -> ( ( F / %s ) < %s <-> F < ( %s x. %s ) ) )' % (ps, D0, PI_, D0, PI_))
    fdl = w.s([flt, ldm], 'mpbird', '( %s -> ( F / %s ) < %s )' % (ps, D0, PI_))
    fle = w.s([cl.mem('F', 'RR'), w.s([a0['dvn']], 'nnrpd', '( %s -> %s e. RR+ )' % (ps, D0)), w.inst('fldivle')], 'syl2anc',
              '( %s -> %s <_ ( F / %s ) )' % (ps, q_, D0))
    cl.leaf(q_, 'NN0', fqn); cl.atom('( F / %s )' % D0)
    cl.have('( F / %s )' % D0, 'RR', cl.mem('( F / %s )' % D0, 'RR'))
    qlt = linarith(w, ps, [fle, fdl], '%s < %s' % (q_, PI_), closure=cl)
    # r < 2 ^ n , r <_ F
    lt_, mle_, fl_ = modle_pow(dn, 'i', a0)
    rn = w.s([cl.mem('F', 'ZZ'), a0['dvn'], w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ps, r_))
    cl.leaf(r_, 'NN0', rn)
    # the toNat of the shift word
    tsh = w.s([dn.eg(), a1['rt'], w.inst('tonatrep0a')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( %s x. ( toNat ` %s ) ) )' % (ps, SHG(RI1), P1, EG))
    tg = w.s([dn.memo['gn0'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ps, EG))
    tsh2 = w.s([tsh, w.s([tg], 'oveq2d', '( %s -> ( %s x. ( toNat ` %s ) ) = %s )' % (ps, P1, EG, D1))], 'eqtrd', '( %s -> ( toNat ` %s ) = %s )' % (ps, SHG(RI1), D1))
    n0v = fv(w, ps, N0F, N0B, 'i', dn.inn, rabV(w, ps, N0B('i')))
    N0I = FAPP(N0F, 'i')
    VAL = '( %s Ncmp %s )' % (D1, r_)
    gt = w.s([cl.mem(D1, 'NN0'), rn, w.inst('ncmpgt')], 'syl2anc', '( %s -> ( %s = 2o <-> %s < %s ) )' % (ps, VAL, r_, D1))
    hA = '%s <_ %s' % (D1, r_)
    # ======================= case A: subtract
    pa = '( %s /\\ %s )' % (ps, hA)
    La = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pa, concl(w, ps, st)))
    ha = w.s([], 'simpr', '( %s -> %s )' % (pa, hA))
    cla = Closure(w, pa, {})
    nl = w.s([La(cl.mem(D1, 'RR')), La(cl.mem(r_, 'RR'))], 'lenltd', '( %s -> ( %s <-> -. %s < %s ) )' % (pa, hA, r_, D1))
    nlt = w.s([ha, nl], 'mpbid', '( %s -> -. %s < %s )' % (pa, r_, D1))
    ng = w.s([La(gt), nlt], 'mtbird', '( %s -> -. %s = 2o )' % (pa, VAL))
    pm = '( %s /\\ m e. %s )' % (pa, N0I)
    Lm = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pa, st)))
    mi = w.s([w.s([], 'simpr', '( %s -> m e. %s )' % (pm, N0I)), Lm(La(n0v))], 'eleqtrd', '( %s -> m e. %s )' % (pm, N0B('i')))
    mm, mc = rab_elim(w, pm, N0B('i'), lambda h: '( TMcmp ` %s ) = %s' % (h, VAL), 'm', mi)
    cv = cngt_val(w, pm, 'm', mm, mc, VAL, Lm(ng))
    htA = w.s([cv], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pa, N0I, CNGT))
    # the subtraction run: tmidmsb at S2
    q2 = '( 2 x. %s )' % q_
    LQ = '( %s bwrd %s )' % (q2, i1)
    WX = CC('( inclBool o. %s )' % XB, YXt('X'))
    WY = CC('( inclBool o. %s )' % SHG(RI1), YXt('Y'))
    WH = CC('( inclBool o. %s )' % LQ, YXt('( D ` I )'))
    sk = w.s([SP.val('K')[1], a0['xv']], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, S2, WX))
    sj = w.s([SP.val('J')[1], a1['yv']], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ps, S2, WY))
    # S2 ` I = <" Z0 "> ++ ( PI ` I ) = ( <" Z0 "> ++ inclBool ( q bwrd i ) ) ++ 4 :: ( D ` I ) = WH
    QB_ = '( %s bwrd i )' % q_
    hi = w.s([pval('I'), a0['hv']], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ps, PI, HDB('i')))
    s1 = w.s([hi], 'oveq2d', '( %s -> ( <" %s "> ++ ( %s ` I ) ) = ( <" %s "> ++ %s ) )' % (ps, Z0B, PI, Z0B, HDB('i')))
    ca = w.s([ci['s1g'], wib(w, ps, QB_, a0['hb']), wg4(w, ps, '( D ` I )', dn.dsw('I')), w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ps, Z0B, QB_, YXt('( D ` I )'), Z0B, HDB('i')))
    w2 = w.s([cl.mem(q_, 'ZZ'), dn.inn, w.inst('tmidvw2')], 'syl2anc', '( %s -> ( <" %s "> ++ ( inclBool o. %s ) ) = ( inclBool o. %s ) )' % (ps, Z0B, QB_, LQ))
    w2b = w.s([w2], 'oveq1d', '( %s -> ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) = %s )' % (ps, Z0B, QB_, YXt('( D ` I )'), WH))
    si0 = w.s([SP.val('I')[1], s1], 'eqtrd', '( %s -> ( %s ` I ) = ( <" %s "> ++ %s ) )' % (ps, S2, Z0B, HDB('i')))
    si = w.s([si0, w.s([ca, w2b], 'eqtr3d', '( %s -> ( <" %s "> ++ %s ) = %s )' % (ps, Z0B, HDB('i'), WH))], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ps, S2, WH))
    lqw = w.s([cl.mem(q2, 'ZZ'), dn.i1n, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, LQ))
    m3 = {'P': PL('P', 8), "P'": PL('P', 9), 'P"': PL('P', 10), 'E': PL(PL('P', 11), 0), 'L': XB, "L'": SHG(RI1), 'L"': LQ,
          'X': 'X', 'Y': 'Y', 'H': '( D ` I )', 'D': S2}
    ex3 = {k: La(v) for k, v in ex_.items()}
    exa = {WRD(XB, '2o'): a0['xb'], WRD(SHG(RI1), '2o'): a1['sh'], WRD(LQ, '2o'): lqw, WRD('( D ` I )', GAM): dn.dsw('I'), STKD(S2): SP.memb,
           '( %s ` K ) = %s' % (S2, WX): sk, '( %s ` J ) = %s' % (S2, WY): sj, '( %s ` I ) = %s' % (S2, WH): si}
    for s_ in ['K', 'J', 'I', 'I"', 'I0']:
        exa[IDX(s_)] = L(dn.c[IDX(s_)])
    for a_, b_ in [('K', 'J'), ('K', 'I'), ('K', 'I"'), ('K', 'I0'), ('J', 'I'), ('J', 'I"'), ('J', 'I0'), ('I', 'I"'), ('I', 'I0'), ('I"', 'I0')]:
        exa['%s =/= %s' % (a_, b_)] = dn.ne(a_, b_)
    ex3.update({k: La(v) for k, v in exa.items()})
    ctxa = Ctx(w, pa, T, root=w.s([w.s([], 'simpl', '( %s -> %s )' % (ps, ph))], 'adantr', '( %s -> %s )' % (pa, ph)))
    t3, c3 = inst(w, pa, 'tmidmsb', m3, Bld(w, pa, ctxa, ex3))
    Ca, Da, n3 = triple_parts(c3)
    # pre: ( N0 ` i ) C_ S
    seq = L(mk['seq'])
    n0s = w.s([n0v, w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % N0B('i'))], 'a1i', '( %s -> %s C_ TMSt )' % (ps, N0B('i'))), seq], 'sseqtrrd',
                         '( %s -> %s C_ ( 2nd ` T ) )' % (ps, N0B('i')))], 'eqsstrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, N0I))
    B1_ = PL(PL('P', 8), 0)
    t3b = hrssc(w, pa, La(phm), t3, Ca, Da, n3, CLN(B1_, N0I, S2), La(clnss(w, ps, B1_, N0I, SS, S2, n0s)))
    # post words
    tshA = La(tsh2)
    tle = w.s([tshA, ha], 'eqbrtrd', '( %s -> ( toNat ` %s ) <_ %s )' % (pa, SHG(RI1), r_))
    # |SHG| <_ n via tmidvw5 : 2 ^ E G <_ r < 2 ^ n
    shlt = w.s([ha, La(lt_)], 'lelttrd', '( %s -> %s < ( 2 ^ %s ) )' % (pa, D1, NF))
    w5 = w.s([w.s([La(a1['rt']), La(dn.gn), La(dn.nfn())], '3jca', '( %s -> ( %s e. NN0 /\\ G e. NN /\\ %s e. NN0 ) )' % (pa, RI1, NF)), shlt,
              w.inst('tmidvw5')], 'syl2anc', '( %s -> ( # ` %s ) <_ %s )' % (pa, SHG(RI1), NF))
    w4 = w.s([w.s([La(dn.nfn()), La(rn), La(lt_)], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s < ( 2 ^ %s ) ) )' % (pa, NF, r_, r_, NF)),
              w.s([La(a1['sh']), w5, tle], '3jca', '( %s -> ( %s e. Word 2o /\\ ( # ` %s ) <_ %s /\\ ( toNat ` %s ) <_ %s ) )' % (pa, SHG(RI1), SHG(RI1), NF, SHG(RI1), r_)),
              w.inst('tmidvw4')], 'syl2anc', '( %s -> ( ( %s subTrunc %s ) ` (/) ) = ( ( %s - ( toNat ` %s ) ) bwrd %s ) )' % (pa, XB, SHG(RI1), r_, SHG(RI1), NF))
    # r - toNat SHG = F mod D1 (stp case 1)
    c1h = w.s([ha, La(er)], 'breqtrd', '( %s -> %s <_ %s )' % (pa, S_, R2s))
    c1 = w.s([c1h, La(st1)], 'mpd', '( %s -> ( ( F mod %s ) = ( %s - %s ) /\\ ( |_ ` ( F / %s ) ) = ( ( 2 x. %s ) + 1 ) ) )' % (pa, S_, R2s, S_, S_, Q2s))
    cm = w.s([c1], 'simpld', '( %s -> ( F mod %s ) = ( %s - %s ) )' % (pa, S_, R2s, S_))
    cq = w.s([c1], 'simprd', '( %s -> ( |_ ` ( F / %s ) ) = ( ( 2 x. %s ) + 1 ) )' % (pa, S_, Q2s))
    dif = w.s([w.s([w.s([La(er)], 'eqcomd', '( %s -> %s = %s )' % (pa, R2s, r_)), tshA], 'oveq12d', '( %s -> ( %s - %s ) = ( %s - ( toNat ` %s ) ) )' % (pa, R2s, S_, r_, SHG(RI1))),
               ], 'id' if False else 'eqcomd', '( %s -> ( %s - ( toNat ` %s ) ) = ( %s - %s ) )' % (pa, r_, SHG(RI1), R2s, S_)) if False else None
    d1 = w.s([w.s([La(er)], 'eqcomd', '( %s -> %s = %s )' % (pa, R2s, r_)), w.s([tshA], 'eqcomd', '( %s -> %s = ( toNat ` %s ) )' % (pa, S_, SHG(RI1)))],
             'oveq12d', '( %s -> ( %s - %s ) = ( %s - ( toNat ` %s ) ) )' % (pa, R2s, S_, r_, SHG(RI1)))
    fm = w.s([cm, d1], 'eqtrd', '( %s -> ( F mod %s ) = ( %s - ( toNat ` %s ) ) )' % (pa, S_, r_, SHG(RI1)))
    wx1 = w.s([w4, w.s([w.s([fm], 'eqcomd', '( %s -> ( %s - ( toNat ` %s ) ) = ( F mod %s ) )' % (pa, r_, SHG(RI1), S_))], 'oveq1d',
                          '( %s -> ( ( %s - ( toNat ` %s ) ) bwrd %s ) = ( ( F mod %s ) bwrd %s ) )' % (pa, r_, SHG(RI1), NF, S_, NF))], 'eqtrd',
              '( %s -> ( ( %s subTrunc %s ) ` (/) ) = ( ( F mod %s ) bwrd %s ) )' % (pa, XB, SHG(RI1), S_, NF))
    ZT = "( inclBool o. ( ( %s subTrunc %s ) ` (/) ) )" % (XB, SHG(RI1))
    zx = w.s([w.s([wx1], 'coeq2d', '( %s -> %s = ( inclBool o. ( ( F mod %s ) bwrd %s ) ) )' % (pa, ZT, S_, NF))], 'oveq1d',
             '( %s -> ( %s ++ %s ) = %s )' % (pa, ZT, YXt('X'), XDB(i1)))
    zx2 = w.s([zx, w.s([La(a1['xv'])], 'eqcomd', '( %s -> %s = %s )' % (pa, XDB(i1), FAPP(XDF, i1)))], 'eqtrd',
              '( %s -> ( %s ++ %s ) = %s )' % (pa, ZT, YXt('X'), FAPP(XDF, i1)))
    # incBits ( ( 2 q ) bwrd ( i + 1 ) ) = ( ( 2 q + 1 ) bwrd ( i + 1 ) ) = ( floor ( F / D1 ) bwrd ( i + 1 ) )
    w3 = w.s([La(fqn), La(dn.inn), La(qlt), w.inst('tmidvw3')], 'syl3anc', '( %s -> ( incBits ` %s ) = ( ( %s + 1 ) bwrd %s ) )' % (pa, LQ, q2, i1))
    cq2 = w.s([cq, w.s([w.s([w.s([La(eq_)], 'eqcomd', '( %s -> %s = %s )' % (pa, Q2s, q_))], 'oveq2d', '( %s -> ( 2 x. %s ) = %s )' % (pa, Q2s, q2))], 'oveq1d',
                       '( %s -> ( ( 2 x. %s ) + 1 ) = ( %s + 1 ) )' % (pa, Q2s, q2))], 'eqtrd', '( %s -> ( |_ ` ( F / %s ) ) = ( %s + 1 ) )' % (pa, S_, q2))
    w3b = w.s([w3, w.s([w.s([cq2], 'eqcomd', '( %s -> ( %s + 1 ) = ( |_ ` ( F / %s ) ) )' % (pa, q2, S_))], 'oveq1d',
                       '( %s -> ( ( %s + 1 ) bwrd %s ) = ( ( |_ ` ( F / %s ) ) bwrd %s ) )' % (pa, q2, i1, S_, i1))], 'eqtrd',
              '( %s -> ( incBits ` %s ) = ( ( |_ ` ( F / %s ) ) bwrd %s ) )' % (pa, LQ, S_, i1))
    IW = '( inclBool o. ( incBits ` %s ) )' % LQ
    hx = w.s([w.s([w3b], 'coeq2d', '( %s -> %s = ( inclBool o. ( ( |_ ` ( F / %s ) ) bwrd %s ) ) )' % (pa, IW, S_, i1))], 'oveq1d',
             '( %s -> ( %s ++ %s ) = %s )' % (pa, IW, YXt('( D ` I )'), HDB(i1)))
    hx2 = w.s([hx, w.s([La(a1['hv'])], 'eqcomd', '( %s -> %s = %s )' % (pa, HDB(i1), FAPP(HDF, i1)))], 'eqtrd',
              '( %s -> ( %s ++ %s ) = %s )' % (pa, IW, YXt('( D ` I )'), FAPP(HDF, i1)))
    POST0 = UP(UP(S2, 'K', CC(ZT, YXt('X'))), 'I', CC(IW, YXt('( D ` I )')))
    POST1 = UP(UP(S2, 'K', FAPP(XDF, i1)), 'I', FAPP(HDF, i1))
    assert Da == CLN(PL(PL('P', 11), 0), SS, POST0), Da
    r1_, new1 = w.rewrite(POST0, {CC(ZT, YXt('X')): (FAPP(XDF, i1), zx2), CC(IW, YXt('( D ` I )')): (FAPP(HDF, i1), hx2)}, pa)
    assert new1 == POST1, new1
    deq = clneq(w, pa, PL(PL('P', 11), 0), SS, r1_, POST0, POST1)
    t3c, C3, D3, n3c = hrrw(w, pa, t3b, CLN(B1_, N0I, S2), Da, n3, deq=deq)
    # bound
    LSH = '( # ` %s )' % SHG(RI1)
    LXB = '( # ` %s )' % XB
    LLQ = '( # ` %s )' % LQ
    xl = w.s([La(cl.mem(r_, 'ZZ')), La(dn.nfn()), w.inst('bwrdlen')], 'syl2anc', '( %s -> %s = %s )' % (pa, LXB, NF))
    ql = w.s([La(cl.mem(q2, 'ZZ')), La(dn.i1n), w.inst('bwrdlen')], 'syl2anc', '( %s -> %s = %s )' % (pa, LLQ, i1))
    cla = Closure(w, pa, {'i': ('NN0', La(dn.inn)), 'R': ('NN0', La(dn.rn))})
    for a_, st_ in [(NF, La(dn.nfn())), (LSH, w.s([La(a1['sh']), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pa, LSH))),
                    (LXB, w.s([La(a0['xb']), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pa, LXB))),
                    (LLQ, w.s([lqw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LLQ)) if False else w.s([La(lqw), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pa, LLQ)))]:
        cla.leaf(a_, 'NN0', st_)
    MX = tsub_text(MXA_, m3)
    mxl = ifmax_le(w, pa, LXB, LSH, NF, cla.mem(LXB, 'RR'), cla.mem(LSH, 'RR'), cla.mem(NF, 'RR'),
                   linarith(w, pa, [xl], '%s <_ %s' % (LXB, NF), closure=cla), w5)
    cla.leaf(MX, 'NN0', w.s([cla.mem(LSH, 'NN0'), cla.mem(LXB, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (pa, MX)))
    b3 = linarith(w, pa, [w5, mxl, ql, La(dn.i1le), La(dn.rle)], '%s <_ %s' % (n3c, T0B), closure=cla)
    t3d = hrle(w, pa, La(phm), t3c, C3, D3, n3c, T0B, cla.mem(T0B, 'NN0'), b3)
    caseA = w.s([w.s([htA, t3d], 'jca', '( %s -> %s )' % (pa, cj(B22[0]) if False else '( A. m e. %s ( %s ` m ) = 1o /\\ %s )' % (N0I, CNGT, TRI(C3, D3, T0B))))],
                'orcd', '( %s -> %s )' % (pa, B22))
    # ======================= case B: skip
    pb = '( %s /\\ -. %s )' % (ps, hA)
    Lb = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pb, concl(w, ps, st)))
    hb = w.s([], 'simpr', '( %s -> -. %s )' % (pb, hA))
    ltb = w.s([Lb(cl.mem(r_, 'RR')), Lb(cl.mem(D1, 'RR'))], 'ltnled', '( %s -> ( %s < %s <-> -. %s ) )' % (pb, r_, D1, hA))
    rlt = w.s([hb, ltb], 'mpbird', '( %s -> %s < %s )' % (pb, r_, D1))
    is2 = w.s([rlt, Lb(gt)], 'mpbird', '( %s -> %s = 2o )' % (pb, VAL))
    pmb = '( %s /\\ m e. %s )' % (pb, N0I)
    Lmb = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pmb, concl(w, pb, st)))
    mib = w.s([w.s([], 'simpr', '( %s -> m e. %s )' % (pmb, N0I)), Lmb(Lb(n0v))], 'eleqtrd', '( %s -> m e. %s )' % (pmb, N0B('i')))
    mmb, mcb = rab_elim(w, pmb, N0B('i'), lambda h: '( TMcmp ` %s ) = %s' % (h, VAL), 'm', mib)
    X_of = lambda t: 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t
    xex = ifex_closed(w, pmb, '( TMcmp ` m ) = 2o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cvb = mval(w, pmb, 'u', 'TMSt', X_of, 'm', mmb, xex)
    c2o = w.s([mcb, Lmb(is2)], 'eqtrd', '( %s -> ( TMcmp ` m ) = 2o )' % pmb)
    itb = w.s([c2o], 'iftrued', '( %s -> %s = (/) )' % (pmb, X_of('m')))
    czb = w.s([cvb, itb], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pmb, CNGT))
    htf = w.s([not1o(w, pmb, czb, CNGT, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pb, N0I, CNGT))
    # the skip case's data
    rlt2 = w.s([rlt, Lb(er)], 'eqbrtrrd' if False else 'breqtrd', '') if False else None
    c0h = w.s([w.s([Lb(er)], 'eqcomd', '( %s -> %s = %s )' % (pb, R2s, r_)), rlt], 'eqbrtrd', '( %s -> %s < %s )' % (pb, R2s, S_))
    c0 = w.s([c0h, Lb(st0)], 'mpd', '( %s -> ( ( F mod %s ) = %s /\\ ( |_ ` ( F / %s ) ) = ( 2 x. %s ) ) )' % (pb, S_, R2s, S_, Q2s))
    cm0 = w.s([w.s([c0], 'simpld', '( %s -> ( F mod %s ) = %s )' % (pb, S_, R2s)), w.s([Lb(er)], 'eqcomd', '( %s -> %s = %s )' % (pb, R2s, r_))], 'eqtrd',
              '( %s -> ( F mod %s ) = %s )' % (pb, S_, r_))
    cq0 = w.s([w.s([c0], 'simprd', '( %s -> ( |_ ` ( F / %s ) ) = ( 2 x. %s ) )' % (pb, S_, Q2s)),
               w.s([w.s([Lb(eq_)], 'eqcomd', '( %s -> %s = %s )' % (pb, Q2s, q_))], 'oveq2d', '( %s -> ( 2 x. %s ) = %s )' % (pb, Q2s, q2))], 'eqtrd',
              '( %s -> ( |_ ` ( F / %s ) ) = %s )' % (pb, S_, q2))
    # X ( i + 1 ) = ( P ` i ) ` K
    xe = w.s([w.s([w.s([cm0], 'oveq1d', '( %s -> ( ( F mod %s ) bwrd %s ) = %s )' % (pb, S_, NF, XB))], 'coeq2d',
                  '( %s -> ( inclBool o. ( ( F mod %s ) bwrd %s ) ) = ( inclBool o. %s ) )' % (pb, S_, NF, XB))], 'oveq1d', '( %s -> %s = %s )' % (pb, XDB(i1), XDB('i')))
    xk = w.s([w.s([Lb(a1['xv']), xe], 'eqtrd', '( %s -> %s = %s )' % (pb, FAPP(XDF, i1), XDB('i'))),
              w.s([Lb(pval('K')), Lb(a0['xv'])], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (pb, PI, XDB('i')))], 'eqtr4d',
             '( %s -> %s = ( %s ` K ) )' % (pb, FAPP(XDF, i1), PI))
    # H ( i + 1 ) = <" Z0 "> ++ ( ( P ` i ) ` I )
    he = w.s([w.s([w.s([cq0], 'oveq1d', '( %s -> ( ( |_ ` ( F / %s ) ) bwrd %s ) = %s )' % (pb, S_, i1, LQ))], 'coeq2d',
                  '( %s -> ( inclBool o. ( ( |_ ` ( F / %s ) ) bwrd %s ) ) = ( inclBool o. %s ) )' % (pb, S_, i1, LQ))], 'oveq1d', '( %s -> %s = %s )' % (pb, HDB(i1), WH))
    hz = w.s([w.s([Lb(ca), Lb(w2b)], 'eqtr3d', '( %s -> ( <" %s "> ++ %s ) = %s )' % (pb, Z0B, HDB('i'), WH)), Lb(s1)], 'eqtr2d' if False else 'id', '') if False else None
    hz = w.s([Lb(s1), w.s([Lb(ca), Lb(w2b)], 'eqtr3d', '( %s -> ( <" %s "> ++ %s ) = %s )' % (pb, Z0B, HDB('i'), WH))], 'eqtrd',
             '( %s -> ( <" %s "> ++ ( %s ` I ) ) = %s )' % (pb, Z0B, PI, WH))
    hk = w.s([w.s([Lb(a1['hv']), he], 'eqtrd', '( %s -> %s = %s )' % (pb, FAPP(HDF, i1), WH)), hz], 'eqtr4d',
             '( %s -> %s = ( <" %s "> ++ ( %s ` I ) ) )' % (pb, FAPP(HDF, i1), Z0B, PI))
    XH = '( %s = ( %s ` K ) /\\ %s = ( <" %s "> ++ ( %s ` I ) ) )' % (FAPP(XDF, i1), PI, FAPP(HDF, i1), Z0B, PI)
    DB_ = '( A. m e. %s -. ( %s ` m ) = 1o /\\ %s )' % (N0I, CNGT, XH)
    caseB = w.s([w.s([htf, w.s([xk, hk], 'jca', '( %s -> %s )' % (pb, XH))], 'jca', '( %s -> %s )' % (pb, DB_))],
                'olcd', '( %s -> %s )' % (pb, B22))
    w.qed([caseA, caseB], 'pm2.61dan', C)
    return w.run()



def tmidmdt():
    lab = 'tmidmdt'
    typ, body, ex = dblocks()
    T = PH_D()
    ph = cj(T)
    C = '( %s -> ( %s /\\ %s ) )' % (ph, typ, ex)
    w = W(lab, 'The shift-down loop of Lean\'s ` divmodCore ` at the machine: its families are typed on '
               '` ( 0 ... R ) ` and the loop test fails at ` R ` (the counter is zero, ` flag ` is set).')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K6)
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K6))))
    dn = Dn(w, ph, c, mk, ne, closed_range=True)
    pt = dn.ps
    a = dn.at('i', dn.inn, dn.ile)
    togk = lambda X, s, g: w.s([g, dn.mkp['k'][s]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (pt, X, GX(s)))
    xg, yg = togk(FAPP(XDF, 'i'), 'K', a['xg']), togk(FAPP(YDF, 'i'), 'J', a['yg'])
    hg, qg = togk(FAPP(HDF, 'i'), 'I', a['hg']), togk(FAPP(QDF, 'i'), "I'", a['qg'])
    pim = w.s([a['pv'], a['S'].memb], 'eqeltrd', '( %s -> %s e. %s )' % (pt, FAPP(PV, 'i'), STK_T))
    seq = dn.L(mk['seq'])
    nv = fv(w, pt, NDF, NDB, 'i', dn.inn, rabV(w, pt, NDB('i')))
    nss = w.s([nv, w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NDB('i'))], 'a1i', '( %s -> %s C_ TMSt )' % (pt, NDB('i'))), seq], 'sseqtrrd',
                        '( %s -> %s C_ ( 2nd ` T ) )' % (pt, NDB('i')))], 'eqsstrd', '( %s -> %s C_ ( 2nd ` T ) )' % (pt, FAPP(NDF, 'i')))
    body_t = typ[len('A. i e. ( 0 ... R ) '):]
    tt = parse_conj(body_t)
    j1 = w.s([w.s([xg, yg], 'jca', '( %s -> %s )' % (pt, cj(tt[0][0]))), w.s([hg, qg], 'jca', '( %s -> %s )' % (pt, cj(tt[0][1])))], 'jca',
             '( %s -> %s )' % (pt, cj(tt[0])))
    j2 = w.s([pim, nss], 'jca', '( %s -> %s )' % (pt, cj(tt[1])))
    ty = w.s([w.s([j1, j2], 'jca', '( %s -> %s )' % (pt, body_t))], 'ralrimiva', '( %s -> %s )' % (ph, typ))
    # the exit test at R
    rn = c['R e. NN0']
    pr = '( %s /\\ m e. ( %s ` R ) )' % (ph, NDF)
    Lr = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pr, concl(w, ph, st)))
    rv = fv(w, ph, NDF, NDB, 'R', rn, rabV(w, ph, NDB('R')))
    mr = w.s([w.s([], 'simpr', '( %s -> m e. ( %s ` R ) )' % (pr, NDF)), Lr(rv)], 'eleqtrd', '( %s -> m e. %s )' % (pr, NDB('R')))
    IFR = 'if ( R = R , 1o , (/) )'
    mm, mc = rab_elim(w, pr, NDB('R'), lambda h: '( TMfl ` %s ) = %s' % (h, IFR), 'm', mr)
    it = w.s([w.s([], 'eqidd', '( %s -> R = R )' % pr)], 'iftrued', '( %s -> %s = 1o )' % (pr, IFR))
    f1 = w.s([mc, it], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pr)
    X_of = lambda t: 'if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t
    xex = ifex_closed(w, pr, '( TMfl ` m ) = 1o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cv = mval(w, pr, 'u', 'TMSt', X_of, 'm', mm, xex)
    it2 = w.s([f1], 'iftrued', '( %s -> %s = (/) )' % (pr, X_of('m')))
    cz = w.s([cv, it2], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pr, CNFL))
    ext = w.s([not1o(w, pr, cz, CNFL, 'm')], 'ralrimiva', '( %s -> %s )' % (ph, ex))
    w.qed([ty, ext], 'jca', C)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
