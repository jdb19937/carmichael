"""T11 helper (pool): Lean's ` poolGoF ` at the machine (Steps23.lean ` poolGoBody_runs ` , ` poolGoF_runs ` ) on TMIplf:
~ tmipzg at the family of ` PLInv ` .

  tmiplia   one entry, ` p > x ` : poolPre (~ tmippr ), the branch, ` dropNum 7 `
  tmiplib   one entry, ` p <_ x ` , ` -. z < p ` : poolPre, poolCmpZ (~ tmipcz ), ` dropNum 7 `
  tmiplic   one entry, ` p <_ x ` , ` z < p ` , ` p ` prime: poolPre, poolCmpZ, ` isPrimeTDF ` (~ tmiptb ), ` moveEntry 7 3 4 `
  tmiplid   one entry, ` p <_ x ` , ` z < p ` , ` p ` not prime: ... ` dropNum 7 `
  tmipli    one entry of the ` forEntries ` loop at the family, of cost ` pgc x z k d x. 14 BB ` ( ` poolGoBody_runs ` )
  tmiplt    the frame: typing, the ` 5 ` column, the value at 0 after ` pushSym 3 bra ` , the closing ` revList 3 6 4 `
  tmipll    ~ tmipzg assembled ( P' a letter)
  tmiplf    poolGoF_runs

    MM_DB=sorties/t11p.mm python3 tools/gen/t11p_d_plf.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t7lib import mval, not1o, ifex_closed
from t5lib import hrssd, cfgcl, clnss
from t7_e_cmp import lamty
from t10_e_doa import lift_from
from t10_u_s2s import expose, me_bound_n
import num
import t6blib
import t11_g_parith as GP
import t11p_b_arith as PA
import t11p_c_pre as PC
for _D in (STMTS11, GP.STMTS, PA.STMTS, PC.STMTS_C):
    t6blib._STMT.update(_D)

SEL = sys.argv[1:]
PGf = lambda s_: '( ( ( F PoolGo Z ) ` G ) ` %s )' % s_
P1f = lambda s_: '( 1st ` %s )' % PGf(s_)
P2f = lambda s_: '( 2nd ` %s )' % PGf(s_)
FZG = '( ( F e. NN0 /\\ Z e. NN0 ) /\\ G e. NN0 )'
LG = '( encNatGam o. L )'
NLG = '( # ` %s )' % LG
DOM = '( 0 ... %s )' % NLG
EB = lambda k: '( encListB ` ( %s substr <. %s , %s >. ) )' % (LG, k, NLG)
C5 = lambda k: "( %s ++ Y' )" % EB(k)
RV = lambda k: '( reverse ` %s )' % P1f('( L prefix %s )' % k)
C3 = lambda k: ENCL(RV(k), DK(3))
PB = lambda k: UPS('D', ('3', C3(k)), ('5', C5(k)))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
PV = "P'"
PSI_T = (TREE_PLF, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
MB = '( ( 3 x. ( C + B ) ) + ; 1 0 )'
BB = '( TMB ` %s )' % MB
K14 = '( ; 1 4 x. %s )' % BB
NB = '( ( C + B ) + 1 )'
DJ = '( L ` j )'
PPJ = '( ( %s x. G ) + 1 )' % DJ
COND1 = '%s <_ F' % PPJ
COND2 = 'Z < %s' % PPJ
IP1 = '( 1st ` ( IsPrimeTD ` %s ) )' % PPJ
IP2 = '( 2nd ` ( IsPrimeTD ` %s ) )' % PPJ
PRIME = '%s = 1o' % IP1
YF = '( i e. NN0 |-> ( %s x. %s ) )' % (P2f('<" ( L ` i ) ">'), K14)
YV = '( %s x. %s )' % (P2f('<" %s ">' % DJ), K14)
PGW = P1f('L')
UB = '( ( ( # ` %s ) + 1 ) x. ( TMB ` B ) )' % PGW
DFIN = UPS('D', ('5', "Y'"), ('6', ENCL(PGW, DK(6))))
LMP = FRAGS['plf'].lmap()
GM = {'P0': LMP['Z1'], 'P1': LMP['Z2'], 'A': LMP['Z3'], "A'": LMP['Y1'], 'A"': LMP['Z4'], 'E': LMP['Z5'], "E'": LMP['Y2'],
      'E"': 'E', 'K': '5', 'I': '3', 'F': RDBRA, 'C': CNFL, 'F"': PID, 'N': S, "N'": S, 'N"': S, 'L': LG, 'R': "Y'",
      'Y': YF, 'P': PV, 'D': 'D', "D'": DFIN, 'U': UB}
_GA, _GC = split_imp(stmt('tmipzg'))
GTREE = tsub(parse_conj(_GA), GM)
GCONCL = tsub_text(_GC, GM)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in _fl if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
P0EQ = [t for t in _fl if t.startswith('( %s ` 0 ) = ' % PV)][0]
REVT = [t for t in _fl if t.startswith('( { ( inl ` %s ) }' % LMP['Y2'])][0]
JC = 'j e. ( 0 ..^ %s )' % NLG
TRI_J = TRI(CLN(LMP['Y1'], S, '( %s ` j )' % PV), CLN(LMP['Z4'], S, '( %s ` ( j + 1 ) )' % PV), YV)
CASES = {'tmiplia': ('-. %s' % COND1,), 'tmiplib': (COND1, '-. %s' % COND2), 'tmiplic': (COND1, COND2, PRIME),
         'tmiplid': (COND1, COND2, '-. %s' % PRIME)}


def case_tree(conds):
    t = (PSI_T, JC)
    for x in conds:
        t = (t, x)
    return t


for _l, _c in CASES.items():
    add11(_l, case_tree(_c), TRI_J)
add11('tmipli', (PSI_T, JC), PERB)
add11('tmiplt', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FTY, FCOL, P0EQ, REVT))
add11('tmipll', PSI_T, GCONCL)
for _l in ('tmiplia', 'tmiplib', 'tmiplic', 'tmiplid', 'tmipli', 'tmiplt', 'tmipll'):
    ORDER11.remove(_l)
    ORDER11.insert(ORDER11.index('tmiplf'), _l)
STMTS_D = {l: STMTS11[l] for l in ('tmiplia', 'tmiplib', 'tmiplic', 'tmiplid', 'tmipli', 'tmiplt', 'tmipll', 'tmiplf')}

if __name__ == '__main__' and 'show' in SEL:
    print(PERB); print(); print(P0EQ); print(); print(REVT); print(); print(GCONCL)


def tbn(w, ph, x, xn):
    T_ = '( TMB ` %s )' % x
    return w.s([w.s([xn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, T_))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, T_))


class Plf(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        fn, zn, gn = c0['F e. NN0'], c0['Z e. NN0'], c0['G e. NN0']
        lw, bn, cn = c0['L e. Word NN0'], c0['B e. NN0'], c0['C e. NN0']
        eqs = {'0': (EWg('F', 'X'), ewg_(w, ph, 'F', fn, 'X', c0[WG('X')])), '1': (EWg('Z', "X'"), ewg_(w, ph, 'Z', zn, "X'", c0[WG("X'")])),
               '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', c0[WG('Y')])), '5': (ENCL('L', "Y'"), enclg(w, ph, 'L', lw, "Y'", c0[WG("Y'")]))}
        Base.__init__(self, w, ph, T, N8, 'plf', eqs)
        s = w.s
        self.fn, self.zn, self.gn, self.lw, self.bn, self.cn = fn, zn, gn, lw, bn, cn
        self.y2w = c0[WG("Y'")]
        self.fzg = s([s([fn, zn], 'jca', '( %s -> ( F e. NN0 /\\ Z e. NN0 ) )' % ph), gn], 'jca', '( %s -> %s )' % (ph, FZG))
        self.lgw = s([lw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([lw, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc',
                    '( %s -> %s = ( # ` L ) )' % (ph, NLG))
        self.nw = s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
        self.g("Y'", self.y2w)

    def pgcl(self, S_, sw):
        w, ph, s = self.w, self.ph, self.w.s
        return s([s([self.fzg, sw], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (ph, FZG, S_)), w.inst('poolgocl')], 'syl',
                 '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, PGf(S_)))

    def rvw(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        pw = s([self.lw, w.inst('pfxcl')], 'syl', '( %s -> ( L prefix %s ) e. Word NN0 )' % (ph, k))
        p1 = s([self.pgcl('( L prefix %s )' % k, pw), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, P1f('( L prefix %s )' % k)))
        return s([p1, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RV(k)))

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        g3 = self.g(C3(k), enclg(w, ph, RV(k), self.rvw(k), DK(3), self.S0.vals['3'][2]))
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g5 = self.g(C5(k), wgcat(w, ph, EB(k), "Y'", eb, self.y2w))
        return self.S0.upd('3', C3(k), g3).upd('5', C5(k), g5)


def cmp_test(w, pc, which, a, an, b, bn, truth, cnd):
    """which 'lt': ( pc -> A. m e. CMPC( a , b ) ( CLT ` m ) = 1o ) (truth: a < b) or its negation (-. a < b);
    which 'ngt': ( pc -> A. m e. CMPC( a , b ) ( CNGT ` m ) = 1o ) (truth: -. b < a, cnd : ( pc -> a <_ b )) or the negation
    (cnd : ( pc -> -. a <_ b ))"""
    s = w.s
    CQ = CMPC(a, b)
    if which == 'lt':
        FN, XL, lem, tv = CLT, (lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t), 'ncmplt', '(/)'
        rel = '%s < %s' % (a, b)
    else:
        FN, XL, lem, tv = CNGT, (lambda t: 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t), 'ncmpgt', '2o'
        rel = '%s < %s' % (b, a)
    pm = '( %s /\\ m e. %s )' % (pc, CQ)
    mi = s([], 'simpr', '( %s -> m e. %s )' % (pm, CQ))
    cond = lambda t: '( TMcmp ` %s ) = ( %s Ncmp %s )' % (t, a, b)
    idh = s([], 'id', '( h = m -> h = m )')
    cg, new = w.wcongr(cond('h'), {'h': 'm'}, 'h = m', {'h': idh})
    both = s([mi, s([cg], 'elrab', '( m e. %s <-> ( m e. TMSt /\\ %s ) )' % (CQ, cond('m')))], 'sylib', '( %s -> ( m e. TMSt /\\ %s ) )' % (pm, cond('m')))
    mm = s([both], 'simpld', '( %s -> m e. TMSt )' % pm)
    mc = s([both], 'simprd', '( %s -> %s )' % (pm, cond('m')))
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = %s' % tv, XL('m').split(' , ')[1], XL('m').split(' , ')[2][:-2],
                      s([], '1oex' if XL('m').split(' , ')[1] == '1o' else '0ex', '%s e. _V' % XL('m').split(' , ')[1]),
                      s([], '1oex' if XL('m').split(' , ')[2][:-2] == '1o' else '0ex', '%s e. _V' % XL('m').split(' , ')[2][:-2]))
    cv = mval(w, pm, 'u', 'TMSt', XL, 'm', mm, xex)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pc, st)))
    nl = s([s([an, bn], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (pc, a, b)), w.inst(lem)], 'syl',
           '( %s -> ( ( %s Ncmp %s ) = %s <-> %s ) )' % (pc, a, b, tv, rel))
    # the case where the test is true: lt: rel holds ; ngt: rel fails
    if which == 'ngt':
        ar, br = s([an], 'nn0red', '( %s -> %s e. RR )' % (pc, a)), s([bn], 'nn0red', '( %s -> %s e. RR )' % (pc, b))
        if truth:
            nrel = s([cnd, s([ar, br], 'lenltd', '( %s -> ( %s <_ %s <-> -. %s < %s ) )' % (pc, a, b, b, a))], 'mpbid', '( %s -> -. %s )' % (pc, rel))
        else:
            nrel = s([s([br, ar], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (pc, b, a, a, b)), cnd], 'mpbird', '( %s -> %s )' % (pc, rel))
        pos = not truth
        cnd = nrel
    else:
        pos = truth
    if pos:
        nc0 = s([cnd, nl], 'mpbird', '( %s -> ( %s Ncmp %s ) = %s )' % (pc, a, b, tv))
        cm0 = s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = %s )' % (pm, tv))
        it = s([cm0], 'iftrued', '( %s -> %s = %s )' % (pm, XL('m'), XL('m').split(' , ')[1]))
        v = s([cv, it], 'eqtrd', '( %s -> ( %s ` m ) = %s )' % (pm, FN, XL('m').split(' , ')[1]))
    else:
        nn0 = s([cnd, nl], 'mtbird', '( %s -> -. ( %s Ncmp %s ) = %s )' % (pc, a, b, tv))
        cm1 = s([Lm(nn0), s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = %s <-> ( %s Ncmp %s ) = %s ) )' % (pm, tv, a, b, tv))], 'mtbird',
                '( %s -> -. ( TMcmp ` m ) = %s )' % (pm, tv))
        it = s([cm1], 'iffalsed', '( %s -> %s = %s )' % (pm, XL('m'), XL('m').split(' , ')[2][:-2]))
        v = s([cv, it], 'eqtrd', '( %s -> ( %s ` m ) = %s )' % (pm, FN, XL('m').split(' , ')[2][:-2]))
    val = concl(w, pm, v).rsplit(' = ', 1)[1]
    if val == '1o':
        return s([v], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pc, CQ, FN)), True
    return s([not1o(w, pm, v, FN, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pc, CQ, FN)), False


def cty(w, pc, mk, FN):
    s = w.s
    if FN == CLT:
        XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    else:
        XL = lambda t: 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t
    a, b = XL('u').split(' , ')[1], XL('u').split(' , ')[2][:-2]
    e = lambda x: s([], '1oel2o', '1o e. 2o') if x == '1o' else s([], '0el2o', '(/) e. 2o')
    return lamty(w, pc, mk, FN, XL, '2o', s([], '2oex', '2o e. _V'), s([e(a), e(b)], 'ifcli', '%s e. 2o' % XL('u')))


def pw2mono(w, ph, M, mn, N, nn, le):
    """( ph -> ( 2 ^ M ) <_ ( 2 ^ N ) ) from M N e. NN0 , le : M <_ N"""
    s = w.s
    uz = s([s([s([mn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, M)), s([nn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, N)), le], '3jca',
              '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (ph, M, N, M, N)), w.inst('eluz2')], 'sylibr',
           '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, N, M))
    return s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), uz, w.inst('leexp2a')], 'syl3anc',
             '( %s -> ( 2 ^ %s ) <_ ( 2 ^ %s ) )' % (ph, M, N))


def entry_case(lab, conds):
    T = numtree11(case_tree(conds))
    ph = cj(T)
    w = W(lab, 'One entry of Lean\'s ` poolGoF ` loop at the machine ( ` poolGoBody_runs ` ), in the case %s: at the family of '
               '` PLInv ` the entry ` d ` is consumed, ` p = d k + 1 ` is compared with ` x ` (~ tmippr ) and %s, within '
               '` pgc x z k d x. 14 BB ` steps (~ tmipzk ).' % ({'tmiplia': '` x < p `', 'tmiplib': '` p <_ x ` , ` p <_ z `',
                                                                   'tmiplic': '` p <_ x ` , ` z < p ` , ` p ` prime',
                                                                   'tmiplid': '` p <_ x ` , ` z < p ` , ` p ` not prime'}[lab],
                                                                  {'tmiplia': 'dropped (~ tmidropb )',
                                                                   'tmiplib': 'compared with ` z ` (~ tmipcz ) and dropped',
                                                                   'tmiplic': 'compared with ` z ` , tested (~ tmiptb ) and moved onto the kept list (~ tmime )',
                                                                   'tmiplid': 'compared with ` z ` , tested (~ tmiptb ) and dropped'}[lab]))
    B = Plf(w, ph, T)
    s, c, mk = w.s, B.c, B.mk
    jj = c[JC]
    jW = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` L ) ) )' % (ph, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` L ) ) )' % ph)
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    J1 = '( j + 1 )'
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (ph, J1, DOM))
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j'))
    PT = '( %s ` j )' % PV
    # stack 5 at j : EW( d , C5( j + 1 ) )
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.lw, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ ( # ` L ) ) --> NN0 )' % ph), jW, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (ph, LG, DJ))
    djn = s([B.lw, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, DJ))
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = s([lgj, encw(w, ph, DJ, djn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG))
    ca1 = s([egj, g4, B.y2w, w.inst('ccatass')], 'syl3anc',
            "( %s -> ( ( ( %s ` j ) ++ ( <\" 4 \"> ++ %s ) ) ++ Y' ) = ( ( %s ` j ) ++ ( ( <\" 4 \"> ++ %s ) ++ Y' ) ) )" % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, B.y2w, w.inst('ccatass')], 'syl3anc', "( %s -> ( ( <\" 4 \"> ++ %s ) ++ Y' ) = ( <\" 4 \"> ++ %s ) )" % (ph, EB(J1), C5(J1)))
    r1 = s([s([dr], 'oveq1d', "( %s -> %s = ( ( ( %s ` j ) ++ ( <\" 4 \"> ++ %s ) ) ++ Y' ) )" % (ph, C5('j'), LG, EB(J1))), ca1], 'eqtrd',
           "( %s -> %s = ( ( %s ` j ) ++ ( ( <\" 4 \"> ++ %s ) ++ Y' ) ) )" % (ph, C5('j'), LG, EB(J1)))
    r2 = s([lgj, ca2], 'oveq12d', "( %s -> ( ( %s ` j ) ++ ( ( <\" 4 \"> ++ %s ) ++ Y' ) ) = %s )" % (ph, LG, EB(J1), EWg(DJ, C5(J1))))
    iv = s([SJ.vals['5'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, C5('j'), EWg(DJ, C5(J1))))], 'eqtrd',
           '( %s -> ( %s ` 5 ) = %s )' % (ph, PT, EWg(DJ, C5(J1))))
    g51 = B.g(C5(J1), wgcat(w, ph, EB(J1), "Y'", eb1, B.y2w))
    v2 = dict(SJ.vals)
    v2['5'] = (EWg(DJ, C5(J1)), iv, B.g(EWg(DJ, C5(J1)), ewg_(w, ph, DJ, djn, C5(J1), g51)))
    SJ2 = Stacks(w, ph, mk, SJ.D, SJ.memb, SJ.ne, v2)
    # the numbers
    cl = Closure(w, ph, {'F': ('NN0', B.fn), 'Z': ('NN0', B.zn), 'G': ('NN0', B.gn), 'B': ('NN0', B.bn), 'C': ('NN0', B.cn)})
    cl.leaf(DJ, 'NN0', djn)
    DG_ = '( %s x. G )' % DJ
    dgn = s([djn, B.gn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, DG_))
    cl.leaf(DG_, 'NN0', dgn)
    ppn = cl.mem(PPJ, 'NN0')
    nbn = cl.mem(NB, 'NN0')
    CB = '( C + B )'
    cbn = cl.mem(CB, 'NN0')
    P2C, P2B, P2CB, P2NB = '( 2 ^ C )', '( 2 ^ B )', '( 2 ^ %s )' % CB, '( 2 ^ %s )' % NB
    for p_ in (P2C, P2B, P2CB, P2NB):
        cl.atom(p_)
    wr = s([s([B.lw, w.inst('wrdfn')], 'syl', '( %s -> L Fn ( 0 ..^ ( # ` L ) ) )' % ph), jW, w.inst('fnfvelrn')], 'syl2anc',
           '( %s -> %s e. ran L )' % (ph, DJ))
    djlt = s([s([], 'breq1', '( a = %s -> ( a < %s <-> %s < %s ) )' % (DJ, P2C, DJ, P2C)), wr, c[RALB('L', 'C')]], 'rspcdva',
             '( %s -> %s < %s )' % (ph, DJ, P2C))
    flt, zlt, glt = c[LT2('F')], c[LT2('Z')], c[LT2('G')]
    pn = lambda e: s([closed(w, ph, '2nn', '2 e. NN'), e, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, concl(w, ph, e).split(' e. ')[0]))
    p2cb = pn(cbn)
    m1 = s([s([s([djn], 'nn0red', '( %s -> %s e. RR )' % (ph, DJ)), s([pn(B.cn)], 'nnred', '( %s -> %s e. RR )' % (ph, P2C)),
               s([B.gn], 'nn0red', '( %s -> G e. RR )' % ph), s([pn(B.bn)], 'nnred', '( %s -> %s e. RR )' % (ph, P2B)),
               s([djn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, DJ)), s([B.gn], 'nn0ge0d', '( %s -> 0 <_ G )' % ph), djlt, glt],
              'ltmul12ad', '( %s -> %s < ( %s x. %s ) )' % (ph, DG_, P2C, P2B))], 'id', '') if False else \
        s([s([djn], 'nn0red', '( %s -> %s e. RR )' % (ph, DJ)), s([pn(B.cn)], 'nnred', '( %s -> %s e. RR )' % (ph, P2C)),
           s([B.gn], 'nn0red', '( %s -> G e. RR )' % ph), s([pn(B.bn)], 'nnred', '( %s -> %s e. RR )' % (ph, P2B)),
           s([djn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, DJ)), s([B.gn], 'nn0ge0d', '( %s -> 0 <_ G )' % ph), djlt, glt],
          'ltmul12ad', '( %s -> %s < ( %s x. %s ) )' % (ph, DG_, P2C, P2B))
    ea = s([closed(w, ph, '2cn', '2 e. CC'), B.cn, B.bn], 'expaddd', '( %s -> %s = ( %s x. %s ) )' % (ph, P2CB, P2C, P2B))
    dglt = s([m1, ea], 'breqtrrd', '( %s -> %s < %s )' % (ph, DG_, P2CB))
    e1 = s([closed(w, ph, '2cn', '2 e. CC'), cbn], 'expp1d', '( %s -> %s = ( %s x. 2 ) )' % (ph, P2NB, P2CB))
    cbge = s([p2cb, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, P2CB))
    pplt = linarith(w, ph, [dglt, e1, cbge], '%s < %s' % (PPJ, P2NB), closure=cl)
    mB = pw2mono(w, ph, 'B', B.bn, NB, nbn, linarith(w, ph, [cl.ge0('C')], 'B <_ %s' % NB, closure=cl))
    mC = pw2mono(w, ph, 'C', B.cn, NB, nbn, linarith(w, ph, [cl.ge0('B')], 'C <_ %s' % NB, closure=cl))
    flt2 = linarith(w, ph, [flt, mB], 'F < %s' % P2NB, closure=cl)
    zlt2 = linarith(w, ph, [zlt, mB], 'Z < %s' % P2NB, closure=cl)
    glt2 = linarith(w, ph, [glt, mB], 'G < %s' % P2NB, closure=cl)
    dlt2 = linarith(w, ph, [djlt, mC], '%s < %s' % (DJ, P2NB), closure=cl)
    # the Run
    B.deep('plf', 0)
    R = B.run(SJ2)
    P5 = PL('P', 5)
    lmb = FRAGS['plb'].lmap(P5, LMP['Z4'])
    E7 = EWg(PPJ, DK(7))
    g7 = B.g(E7, ewg_(w, ph, PPJ, ppn, DK(7), B.S0.vals['7'][2]))
    B.call(R, 'tmippr', {'F': 'F', 'G': 'G', 'A': DJ, 'N': NB, 'X': 'X', 'Y': 'Y', "X'": C5(J1), 'P': PL(P5, 3), 'E': lmb['Z1']},
           {'%s e. NN0' % DJ: djn, '%s e. NN0' % NB: nbn, 'F < %s' % P2NB: flt2, 'G < %s' % P2NB: glt2, '%s < %s' % (DJ, P2NB): dlt2,
            '%s < %s' % (PPJ, P2NB): pplt, "%s e. Word Gamma'" % C5(J1): g51}, [('5', C5(J1), g51), ('7', E7, g7)])
    N1 = CMPC(PPJ, 'F')
    c1 = c[conds[0]]
    ngt, ngt_true = cmp_test(w, ph, 'ngt', PPJ, ppn, 'F', B.fn, conds[0] == COND1, c1)
    TB_ = '( TMB ` %s )' % NB

    def drop7(P_, N_):
        lab_ = R.cur.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
        assert R.cur == CLN(lab_, N_, R.S.D), (R.cur[:200], N_)
        cfg = cfgcl(w, ph, lab_, S, R.S.D, mk['tv'], B.ex[LAB(lab_)], closed(w, ph, 'ssid', '%s C_ %s' % (S, S)), R.S.memb)
        R.tri = hrssd(w, ph, mk['phm'], R.tri, R.C0, R.cur, R.n, CLN(lab_, S, R.S.D), clnss(w, ph, lab_, N_, S, R.S.D, B.ss(N_)), cfg)
        R.cur = CLN(lab_, S, R.S.D)
        chain = list(R.chain)
        assert chain[-1][0] == '7', chain
        Son = R.at(chain[:-1])
        B.call(R, 'tmidropb', {'K': '7', 'F': PPJ, 'N': NB, 'X': DK(7), 'P': P_, 'E': LMP['Z4']},
               {'%s e. NN0' % PPJ: ppn, '%s e. NN0' % NB: nbn, '%s < %s' % (PPJ, P2NB): pplt}, [('7', DK(7), B.S0.vals['7'][2])],
               on=(Son, chain[:-1]))

    extra_n = []
    if not ngt_true:
        B.call(R, 'tm2fbrg', {'A': lmb['Z1'], 'C': CNGT, 'E': lmb['Y7'], 'Q': GT(lmb['Y2']), 'N': N1},
               {STMT(GT(lmb['Y2'])): gotocl(w, ph, mk['tv'], lmb['Y2'], B.ex[LAB(lmb['Y2'])]), SSS(N1): B.ss(N1),
                'A. m e. %s -. ( %s ` m ) = 1o' % (N1, CNGT): ngt, CTY(CNGT): cty(w, ph, mk, CNGT)}, [])
        drop7(PL(P5, 9), N1)
        kind = 'F'
    else:
        B.call(R, 'tm2lbrt', {'A': lmb['Z1'], 'C': CNGT, 'E': lmb['Y2'], 'Q': GT(lmb['Y7']), 'N': N1},
               {STMT(GT(lmb['Y7'])): gotocl(w, ph, mk['tv'], lmb['Y7'], B.ex[LAB(lmb['Y7'])]), SSS(N1): B.ss(N1),
                'A. m e. %s ( %s ` m ) = 1o' % (N1, CNGT): ngt, CTY(CNGT): cty(w, ph, mk, CNGT)}, [])
        B.call(R, 'tmipcz', {'Z': 'Z', 'Q': PPJ, 'N': NB, 'X': "X'", 'Y': DK(7), 'P': PL(P5, 4), 'E': lmb['Z2']},
               {'%s e. NN0' % PPJ: ppn, '%s e. NN0' % NB: nbn, 'Z < %s' % P2NB: zlt2, '%s < %s' % (PPJ, P2NB): pplt}, [], pre=(N1, B.ss(N1)))
        N2 = CMPC('Z', PPJ)
        c2 = c[conds[1]]
        lt, lt_true = cmp_test(w, ph, 'lt', 'Z', B.zn, PPJ, ppn, conds[1] == COND2, c2)
        if not lt_true:
            B.call(R, 'tm2fbrg', {'A': lmb['Z2'], 'C': CLT, 'E': lmb['Y6'], 'Q': GT(lmb['Y3']), 'N': N2},
                   {STMT(GT(lmb['Y3'])): gotocl(w, ph, mk['tv'], lmb['Y3'], B.ex[LAB(lmb['Y3'])]), SSS(N2): B.ss(N2),
                    'A. m e. %s -. ( %s ` m ) = 1o' % (N2, CLT): lt, CTY(CLT): cty(w, ph, mk, CLT)}, [])
            drop7(PL(P5, 8), N2)
            kind = 'F'
        else:
            B.call(R, 'tm2lbrt', {'A': lmb['Z2'], 'C': CLT, 'E': lmb['Y3'], 'Q': GT(lmb['Y6']), 'N': N2},
                   {STMT(GT(lmb['Y6'])): gotocl(w, ph, mk['tv'], lmb['Y6'], B.ex[LAB(lmb['Y6'])]), SSS(N2): B.ss(N2),
                    'A. m e. %s ( %s ` m ) = 1o' % (N2, CLT): lt, CTY(CLT): cty(w, ph, mk, CLT)}, [])
            ppb = linarith(w, ph, [c1, flt], '%s < %s' % (PPJ, P2B), closure=cl)
            B.call(R, 'tmiptb', {'K': '7', 'J': '4', 'I': '6', "I'": '0', 'I"': '1', 'I0': '2', 'F': PPJ, 'N': 'B', 'X': DK(7),
                                 'P': PL(P5, 5), 'E': lmb['Z3']},
                   {'%s e. NN0' % PPJ: ppn, '%s < %s' % (PPJ, P2B): ppb}, [], pre=(N2, B.ss(N2)))
            NP1 = NFL(IP1)
            pm = '( %s /\\ m e. %s )' % (ph, NP1)
            mm, mf = A8.nfl_unpack(w, pm, IP1, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NP1)))
            prc = c[conds[2]]
            if conds[2] == PRIME:
                fl1 = s([mf, lift_from(w, ph, pm, prc)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
                B.call(R, 'tm2lbrt', {'A': lmb['Z3'], 'C': 'TMfl', 'E': lmb['Y4'], 'Q': GT(lmb['Y5']), 'N': NP1},
                       {STMT(GT(lmb['Y5'])): gotocl(w, ph, mk['tv'], lmb['Y5'], B.ex[LAB(lmb['Y5'])]), SSS(NP1): B.ss(NP1),
                        'A. m e. %s ( TMfl ` m ) = 1o' % NP1: s([fl1], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ph, NP1))}, [])
                WQ = '( encNatGam ` %s )' % PPJ
                E3 = EWg(PPJ, C3('j'))
                g3 = B.g(E3, ewg_(w, ph, PPJ, ppn, C3('j'), B.gam[C3('j')]))
                B.call(R, 'tmime', {'K': '7', 'J': '3', 'I': '4', 'W': WQ, 'X': DK(7), 'P': PL(P5, 6), 'E': LMP['Z4']},
                       {WRD(WQ, BITS): engb(w, ph, PPJ, ppn)}, [('7', DK(7), B.S0.vals['7'][2]), ('3', E3, g3)], pre=(NP1, B.ss(NP1)))
                kind = 'P'
                cl2 = Closure(w, ph, {'C': ('NN0', B.cn), 'B': ('NN0', B.bn)})
                cl2.leaf(TB_, 'NN0', tbn(w, ph, NB, nbn))
                extra_n.append(me_bound_n(w, ph, PPJ, ppn, pplt, NB, nbn, cl2))
            else:
                fne = s([mf, lift_from(w, ph, pm, s([prc], 'neqned', '( %s -> %s =/= 1o )' % (ph, IP1)))], 'eqnetrd',
                        '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
                nf = s([s([fne], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (ph, NP1))
                B.call(R, 'tm2fbrg', {'A': lmb['Z3'], 'C': 'TMfl', 'E': lmb['Y5'], 'Q': GT(lmb['Y4']), 'N': NP1},
                       {STMT(GT(lmb['Y4'])): gotocl(w, ph, mk['tv'], lmb['Y4'], B.ex[LAB(lmb['Y4'])]), SSS(NP1): B.ss(NP1),
                        'A. m e. %s -. ( TMfl ` m ) = 1o' % NP1: nf}, [])
                drop7(PL(P5, 7), NP1)
                kind = 'N'
    # the stacks: PB( j + 1 )
    e, nrm, out2 = renorm(w, ph, B, R, [('3', C3('j')), ('5', C5('j'))], N8, PT=PT, pv=pvj)
    zk = s([s([s([B.fzg, B.lw], 'jca', '( %s -> ( %s /\\ L e. Word NN0 ) )' % (ph, FZG)), s([jW, B.S0.vals['3'][2]], 'jca',
                                                                                          "( %s -> ( j e. ( 0 ..^ ( # ` L ) ) /\\ ( D ` 3 ) e. Word Gamma' ) )" % ph)],
              'jca', "( %s -> ( ( %s /\\ L e. Word NN0 ) /\\ ( j e. ( 0 ..^ ( # ` L ) ) /\\ ( D ` 3 ) e. Word Gamma' ) ) )" % (ph, FZG)),
            w.inst('tmipzk')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, sub_jz(PA.EQK1), sub_jz(PA.EQK2)))
    k1 = s([zk], 'simpld', '( %s -> %s )' % (ph, sub_jz(PA.EQK1)))
    k2 = s([zk], 'simprd', '( %s -> %s )' % (ph, sub_jz(PA.EQK2)))
    KP = '( %s /\\ %s )' % (sub_jz(PA.CONDJ), sub_jz(PA.PRIMEJ))
    IFK = sub_jz(PA.EQK1).split(' = ', 1)[1]
    if kind == 'P':
        assert out2 == [('3', E3), ('5', C5(J1))], out2
        kp_ = s([s([c1, c[conds[1]]], 'jca', '( %s -> %s )' % (ph, sub_jz(PA.CONDJ))), c[conds[2]]], 'jca', '( %s -> %s )' % (ph, KP))
        v3 = s([k1, s([kp_], 'iftrued', '( %s -> %s = %s )' % (ph, IFK, E3))], 'eqtrd', '( %s -> %s = %s )' % (ph, C3(J1), E3))
        r_, nrm2 = w.rewrite(nrm, {E3: (C3(J1), s([v3], 'eqcomd', '( %s -> %s = %s )' % (ph, E3, C3(J1))))}, ph)
    else:
        assert out2 == [('3', C3('j')), ('5', C5(J1))], out2
        if kind == 'F' and conds[0] != COND1:
            nk = s([c1], 'intnanrd', '( %s -> -. %s )' % (ph, sub_jz(PA.CONDJ)))
            nkp = s([nk], 'intnanrd', '( %s -> -. %s )' % (ph, KP))
        elif kind == 'F':
            nk = s([c[conds[1]]], 'intnand', '( %s -> -. %s )' % (ph, sub_jz(PA.CONDJ)))
            nkp = s([nk], 'intnanrd', '( %s -> -. %s )' % (ph, KP))
        else:
            nkp = s([c[conds[2]]], 'intnand', '( %s -> -. %s )' % (ph, KP))
        v3 = s([k1, s([nkp], 'iffalsed', '( %s -> %s = %s )' % (ph, IFK, C3('j')))], 'eqtrd', '( %s -> %s = %s )' % (ph, C3(J1), C3('j')))
        r_, nrm2 = w.rewrite(nrm, {C3('j'): (C3(J1), s([v3], 'eqcomd', '( %s -> %s = %s )' % (ph, C3('j'), C3(J1))))}, ph)
    assert nrm2 == PB(J1), nrm2
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1))
    D0 = triple_D(R.cur)
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, D0, PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LMP['Z4'], S, deq, D0, '( %s ` %s )' % (PV, J1)))
    assert C == CLN(LMP['Y1'], S, PT), C
    # the bound
    IFC = sub_jz(PA.EQK2).split(' = ', 1)[1]
    if kind == 'F':
        if conds[0] != COND1:
            nk = s([c1], 'intnanrd', '( %s -> -. %s )' % (ph, sub_jz(PA.CONDJ)))
        else:
            nk = s([c[conds[1]]], 'intnand', '( %s -> -. %s )' % (ph, sub_jz(PA.CONDJ)))
        pg = s([k2, s([nk], 'iffalsed', '( %s -> %s = 1 )' % (ph, IFC))], 'eqtrd', '( %s -> %s = 1 )' % (ph, P2f('<" %s ">' % DJ)))
        PGV = '1'
    else:
        kc = s([c1, c[conds[1]]], 'jca', '( %s -> %s )' % (ph, sub_jz(PA.CONDJ)))
        PGV = '( %s + 1 )' % IP2
        pg = s([k2, s([kc], 'iftrued', '( %s -> %s = %s )' % (ph, IFC, PGV))], 'eqtrd', '( %s -> %s = %s )' % (ph, P2f('<" %s ">' % DJ), PGV))
    cl3 = Closure(w, ph, {'C': ('NN0', B.cn), 'B': ('NN0', B.bn)})
    mbn = cl3.mem(MB, 'NN0')
    cl3.leaf(BB, 'NN0', tbn(w, ph, MB, mbn))
    cl3.leaf(TB_, 'NN0', tbn(w, ph, NB, nbn))
    hyps = []
    hyps.append(s([nbn, mbn, linarith(w, ph, [cl3.ge0('C'), cl3.ge0('B')], '%s <_ %s' % (NB, MB), closure=cl3), w.inst('tmbmono')], 'syl3anc',
                  '( %s -> %s <_ %s )' % (ph, TB_, BB)))
    hyps.append(s([s([mbn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, BB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, BB)))
    hyps += extra_n
    YVc = '( %s x. %s )' % (PGV, K14)
    if kind in ('P', 'N'):
        M37 = '( ( 3 x. B ) + 7 )'
        T37 = '( TMB ` %s )' % M37
        m37 = cl3.mem(M37, 'NN0')
        cl3.leaf(T37, 'NN0', tbn(w, ph, M37, m37))
        ipcl = s([s([ppn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` %s ) e. ( 2o X. NN0 ) )' % (ph, PPJ)), w.inst('xp2nd')], 'syl',
                 '( %s -> %s e. NN0 )' % (ph, IP2))
        cl3.leaf(IP2, 'NN0', ipcl)
        IPP = '( %s + 1 )' % IP2
        mo = s([m37, mbn, linarith(w, ph, [cl3.ge0('C')], '%s <_ %s' % (M37, MB), closure=cl3), w.inst('tmbmono')], 'syl3anc',
               '( %s -> %s <_ %s )' % (ph, T37, BB))
        hyps.append(s([cl3.mem(T37, 'RR'), cl3.mem(BB, 'RR'), cl3.mem(IPP, 'RR'), cl3.ge0(IPP), mo], 'lemul2ad',
                      '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, IPP, T37, IPP, BB)))
        hyps.append(s([s([s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % ph), cl3.mem(IPP, 'RR'), cl3.mem(BB, 'RR'), cl3.ge0(BB),
                       linarith(w, ph, [cl3.ge0(IP2)], '1 <_ %s' % IPP, closure=cl3)], 'lemul1ad',
                      '( %s -> ( 1 x. %s ) <_ ( %s x. %s ) )' % (ph, BB, IPP, BB)))
        # 16 <_ BB
        cl4 = Closure(w, ph, {})
        cl4.leaf(MB, 'NN0', mbn)
        cl4.leaf(BB, 'NN0', cl3.mem(BB, 'NN0'))
        l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
        qd = s([mbn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
               '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, MB, BB))
        hyps.append(nlinarith(w, ph, [qd, cl4.ge0(MB)], '; 1 6 <_ %s' % BB, closure=cl4, atoms=[MB, BB]))
    if kind == 'P':
        WQ = '( encNatGam ` %s )' % PPJ
        LW = '( # ` %s )' % WQ
        cl3.leaf(LW, 'NN0', s([encw(w, ph, PPJ, ppn), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))
    atoms = [BB, TB_] + ([IP2, '( TMB ` ( ( 3 x. B ) + 7 ) )'] if kind in ('P', 'N') else []) + (['( # ` ( encNatGam ` %s ) )' % PPJ] if kind == 'P' else [])
    le = linarith(w, ph, hyps, '%s <_ %s' % (n, YVc), closure=cl3, atoms=atoms, products=True)
    rv, _ = w.rewrite(YV, {P2f('<" %s ">' % DJ): (PGV, pg)}, ph)
    le2 = s([le, s([rv], 'eqcomd', '( %s -> %s = %s )' % (ph, YVc, YV))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, n, YV))
    yvn = s([rv, cl3.mem(YVc, 'NN0')], 'eqeltrrd' if False else 'eqeltrd', '') if False else \
        s([s([rv], 'eqcomd', '( %s -> %s = %s )' % (ph, YVc, YV)), cl3.mem(YVc, 'NN0')], 'eqeltrrd', '( %s -> %s e. NN0 )' % (ph, YV))
    st = hrle(w, ph, mk['phm'], t, C, D, n, YV, yvn, le2)
    finish(w, st, lab)
    return w.run()


def sub_jz(txt):
    """PA's texts at J := j , Z' := ( D ` 3 )"""
    return txt.replace('( L ` J )', '( L ` j )').replace('( J + 1 )', '( j + 1 )').replace('( L prefix J )', '( L prefix j )').replace("Z'", '( D ` 3 )')


def tmiplia(): return entry_case('tmiplia', CASES['tmiplia'])
def tmiplib(): return entry_case('tmiplib', CASES['tmiplib'])
def tmiplic(): return entry_case('tmiplic', CASES['tmiplic'])
def tmiplid(): return entry_case('tmiplid', CASES['tmiplid'])



def yfv(w, ph, jn, j='j'):
    """( ph -> ( YF ` j ) = YV( j ) ) from jn : ( ph -> j e. NN0 )"""
    s = w.s
    YVi = lambda x: '( %s x. %s )' % (P2f('<" ( L ` %s ) ">' % x), K14)
    hy, new = w.congr(YVi('i'), {'i': j}, 'i = %s' % j, {'i': s([], 'id', '( i = %s -> i = %s )' % (j, j))})
    assert new == YVi(j), new
    fvm = s([hy, s([], 'eqid', '%s = %s' % (YF, YF)), s([], 'ovex', '%s e. _V' % YVi(j))], 'fvmpt', '( %s e. NN0 -> ( %s ` %s ) = %s )' % (j, YF, j, YVi(j)))
    return s([jn, fvm], 'syl', '( %s -> ( %s ` %s ) = %s )' % (ph, YF, j, YVi(j)))


def bbfacts(w, ph, cl, bn, cn):
    """register BB ( and MB ) as leaves of cl; return ( 1 <_ BB , ; 1 6 <_ BB )"""
    s = w.s
    mbn = cl.mem(MB, 'NN0')
    cl.leaf(BB, 'NN0', tbn(w, ph, MB, mbn))
    one = s([s([mbn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, BB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, BB))
    cl4 = Closure(w, ph, {})
    cl4.leaf(MB, 'NN0', mbn)
    cl4.leaf(BB, 'NN0', cl.mem(BB, 'NN0'))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([mbn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, MB, BB))
    return one, nlinarith(w, ph, [qd, cl4.ge0(MB)], '; 1 6 <_ %s' % BB, closure=cl4, atoms=[MB, BB])


def tmipli():
    lab = 'tmipli'
    PJ = cj((PSI_T, JC))
    w = W(lab, 'One entry of Lean\'s ` poolGoF ` loop at the machine ( ` poolGoBody_runs ` ): at the family of ` PLInv ` the body '
               'takes the stacks at ` j ` to those at ` j + 1 ` within ` pgc x z k d x. 14 BB ` steps, by cases on ` p <_ x ` , '
               '` z < p ` and the primality of ` p ` (~ tmiplia , ~ tmiplib , ~ tmiplic , ~ tmiplid ).')
    s = w.s
    st = {l: s([], l, STMTS11[l]) for l in CASES}
    PJ1 = '( %s /\\ %s )' % (PJ, COND1)
    PJ12 = '( %s /\\ %s )' % (PJ1, COND2)
    cd = s([st['tmiplic'], st['tmiplid']], 'pm2.61dan', '( %s -> %s )' % (PJ12, TRI_J))
    bcd = s([cd, st['tmiplib']], 'pm2.61dan', '( %s -> %s )' % (PJ1, TRI_J))
    a = s([bcd, st['tmiplia']], 'pm2.61dan', '( %s -> %s )' % (PJ, TRI_J))
    c = Ctx(w, PJ, (PSI_T, JC))
    jj = c[JC]
    lw = c['L e. Word NN0']
    lg = s([lw, closed(w, PJ, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = ( # ` L ) )' % (PJ, NLG))
    jW = s([jj, s([lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` L ) ) )' % (PJ, NLG))], 'eleqtrd', '( %s -> j e. ( 0 ..^ ( # ` L ) ) )' % PJ)
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % PJ)
    fv = yfv(w, PJ, jn)
    djn = s([lw, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (PJ, DJ))
    S1 = '<" %s ">' % DJ
    fzg = s([s([c['F e. NN0'], c['Z e. NN0']], 'jca', '( %s -> ( F e. NN0 /\\ Z e. NN0 ) )' % PJ), c['G e. NN0']], 'jca', '( %s -> %s )' % (PJ, FZG))
    pc = s([s([fzg, s([djn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (PJ, S1))], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (PJ, FZG, S1)),
            w.inst('poolgocl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (PJ, PGf(S1)))
    p2n = s([pc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (PJ, P2f(S1)))
    cl = Closure(w, PJ, {'B': ('NN0', c['B e. NN0']), 'C': ('NN0', c['C e. NN0'])})
    cl.leaf(P2f(S1), 'NN0', p2n)
    mbn = cl.mem(MB, 'NN0')
    cl.leaf(BB, 'NN0', tbn(w, PJ, MB, mbn))
    yvn = cl.mem(YV, 'NN0')
    C_, D_, n_ = triple_parts(TRI_J)
    t, C_, D_, n2 = hrrw(w, PJ, a, C_, D_, n_, neq=s([fv], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (PJ, YV, YF)))
    yn = s([fv, yvn], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (PJ, YF))
    w.qed([yn, t], 'jca', STMTS11['tmipli'])
    return w.run()


def tmiplt():
    lab = 'tmiplt'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` poolGoF ` loop at the machine: the family of ` PLInv ` is a stack family whose ` 5 ` column is '
               'the rest of the divisor list, at ` 0 ` it is the stacks after ` pushSym 3 bra ` , and at the end ` revList 3 6 4 ` '
               '(~ tmilrevb ) moves the kept numbers onto ` 6 ` in the order of the pool (~ tmpgmem bounds them).')
    s = w.s
    B = Plf(w, ph, T)
    c, mk = B.c, B.mk
    fam = c['%s = %s' % (PV, PF)]
    ph0t = (TREE_PLF, NUMS)
    ph0 = cj(ph0t)
    TK = (ph0t, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Plf(w, pk, TK)
    fm = s([Bk.pbst('k').memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    j0 = s([c[cj(TREE_PLF)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)),
             s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))], 'mpbird', '( %s -> %s )' % (ph, FTY))
    TJ = (T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Plf(w, pj, TJ)
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', Bj.c['j e. %s' % DOM], Bj.pbst('j'))
    col = s([SJ.vals['5'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    # the value at 0
    nlg = s([B.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
    z0 = s([nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0'))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le_ = s([B.lw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` L ) = ( encListB ` %s ) )' % (ph, LG))
    e5 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le_], 'eqtr4d',
              '( %s -> %s = ( encList ` L ) )' % (ph, EB('0')))], 'oveq1d', '( %s -> %s = %s )' % (ph, C5('0'), ENCL('L', "Y'")))
    e5b = s([e5, s([c['( D ` 5 ) = %s' % ENCL('L', "Y'")]], 'eqcomd', '( %s -> %s = ( D ` 5 ) )' % (ph, ENCL('L', "Y'")))], 'eqtrd',
            '( %s -> %s = ( D ` 5 ) )' % (ph, C5('0')))
    PG0 = PGf('( L prefix 0 )')
    p00 = s([s([s([], 'pfx00', '( L prefix 0 ) = (/)')], 'fveq2i', '%s = %s' % (PG0, PGf('(/)')))], 'a1i', '( %s -> %s = %s )' % (ph, PG0, PGf('(/)')))
    pg0 = s([p00, s([B.fzg, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (ph, PGf('(/)')))], 'eqtrd', '( %s -> %s = <. (/) , 0 >. )' % (ph, PG0))
    m1 = s([s([pg0], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. (/) , 0 >. ) )' % (ph, PG0)),
            s([s([s([], '0ex', '(/) e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. (/) , 0 >. ) = (/)')], 'a1i',
              '( %s -> ( 1st ` <. (/) , 0 >. ) = (/) )' % ph)], 'eqtrd', '( %s -> %s = (/) )' % (ph, P1f('( L prefix 0 )')))
    r0 = s([s([m1], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ph, RV('0'))), s([s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i',
                                                                                     '( %s -> ( reverse ` (/) ) = (/) )' % ph)],
           'eqtrd', '( %s -> %s = (/) )' % (ph, RV('0')))
    e3 = s([s([s([r0], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` (/) ) )' % (ph, RV('0'))),
               s([s([], 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'a1i', '( %s -> ( encList ` (/) ) = <" 2 "> )' % ph)], 'eqtrd',
              '( %s -> ( encList ` %s ) = <" 2 "> )' % (ph, RV('0')))], 'oveq1d', '( %s -> %s = ( <" 2 "> ++ ( D ` 3 ) ) )' % (ph, C3('0')))
    V3 = '( <" 2 "> ++ ( D ` 3 ) )'
    rr, xx = w.rewrite(PB('0'), {C3('0'): (V3, e3), C5('0'): ('( D ` 5 )', e5b)}, ph)
    assert xx == UPS('D', ('3', V3), ('5', DK(5))), xx
    s2 = s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
    B.g(V3, wgcat(w, ph, '<" 2 ">', DK(3), s2, B.S0.vals['3'][2]))
    nst, outn = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, [('3', V3), ('5', DK(5))], B.gam, N8)
    assert outn == [('3', V3)], outn
    p0 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx)), nst], 'eqtrd', '( %s -> %s )' % (ph, P0EQ))
    # the closing revList 3 6 4
    nz = s([nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    pvN, SN = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, NLG, nz, B.pbst(NLG))
    PTN = '( %s ` %s )' % (PV, NLG)
    SR = SN.upd('5', "Y'", B.y2w)
    R = B.run(SR)
    B.deep('plf', 1)
    R.base.update(B.ex)
    RVN = RV(NLG)
    PN = '( L prefix %s )' % NLG
    rvw = B.rvw(NLG)
    # ( L prefix NLG ) = L
    pf = s([s([B.lg], 'oveq2d', '( %s -> %s = ( L prefix ( # ` L ) ) )' % (ph, PN)),
            s([B.lw, w.inst('pfxid')], 'syl', '( %s -> ( L prefix ( # ` L ) ) = L )' % ph)], 'eqtrd', '( %s -> %s = L )' % (ph, PN))
    p1e = s([s([pf], 'fveq2d', '( %s -> %s = %s )' % (ph, PGf(PN), PGf('L')))], 'fveq2d', '( %s -> %s = %s )' % (ph, P1f(PN), PGW))
    # the entries are below 2 ^ B (~ tmpgmem )
    mem = s([s([B.fzg, B.lw], 'jca', '( %s -> ( %s /\\ L e. Word NN0 ) )' % (ph, FZG)), w.inst('tmpgmem')], 'syl',
            '( %s -> %s )' % (ph, GP.STMTS['tmpgmem'].split(' -> ', 1)[1][:-2].replace(' S ', ' L ').replace('` S )', '` L )')))
    MEMS = concl(w, ph, mem)
    ralq = s([mem], 'simpld', '( %s -> A. q e. ran %s ( q <_ F /\\ Z < q ) )' % (ph, PGW))
    lens = s([mem], 'simprd', '( %s -> ( ( # ` %s ) <_ %s /\\ ( # ` L ) <_ %s ) )' % (ph, PGW, P2f('L'), P2f('L')))
    pa = '( %s /\\ p e. ran %s )' % (ph, RVN)
    Lp = lambda st: lift_from(w, ph, pa, st)
    ain = s([], 'simpr', '( %s -> p e. ran %s )' % (pa, RVN))
    p1w = s([B.pgcl(PN, s([B.lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PN))), w.inst('xp1st')], 'syl',
            '( %s -> %s e. Word NN0 )' % (ph, P1f(PN)))
    a1 = s([Lp(s([p1w, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (ph, RVN, P1f(PN)))), ain], 'sseldd',
           '( %s -> p e. ran %s )' % (pa, P1f(PN)))
    a2 = s([a1, Lp(s([p1e], 'rneqd', '( %s -> ran %s = ran %s )' % (ph, P1f(PN), PGW)))], 'eleqtrd', '( %s -> p e. ran %s )' % (pa, PGW))
    cg, new = w.wcongr('( q <_ F /\\ Z < q )', {'q': 'p'}, 'q = p', {'q': s([], 'id', '( q = p -> q = p )')})
    pq = s([cg, a2, Lp(ralq)], 'rspcdva', '( %s -> ( p <_ F /\\ Z < p ) )' % pa)
    pgw = s([B.pgcl('L', B.lw), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PGW))
    pn = s([s([s([s([Lp(pgw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, PGW, PGW)), w.inst('frn')], 'syl',
                 '( %s -> ran %s C_ NN0 )' % (pa, PGW)), a2], 'sseldd', '( %s -> p e. NN0 )' % pa)], 'nn0red', '( %s -> p e. RR )' % pa)
    plt = s([pn, s([Lp(B.fn)], 'nn0red', '( %s -> F e. RR )' % pa), s([s([closed(w, pa, '2nn', '2 e. NN'), Lp(B.bn), w.inst('nnexpcl')], 'syl2anc',
                                                                       '( %s -> ( 2 ^ B ) e. NN )' % pa)], 'nnred', '( %s -> ( 2 ^ B ) e. RR )' % pa),
             s([pq], 'simpld', '( %s -> p <_ F )' % pa), Lp(c[LT2('F')])], 'lelttrd', '( %s -> p < ( 2 ^ B ) )' % pa)
    rp = s([plt], 'ralrimiva', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (ph, RVN))
    cb = s([s([], 'breq1', '( p = a -> ( p < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
           '( A. p e. ran %s p < ( 2 ^ B ) <-> A. a e. ran %s a < ( 2 ^ B ) )' % (RVN, RVN))
    ral = s([rp, cb], 'sylib', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (ph, RVN))
    RR = '( reverse ` %s )' % RVN
    rrw = s([rvw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RR))
    g6 = B.g(ENCL(RR, DK(6)), enclg(w, ph, RR, rrw, DK(6), B.S0.vals['6'][2]))
    B.call(R, 'tmilrevb', {'K': '3', 'J': '6', 'I': '4', 'L': RVN, 'R': DK(3), 'B': 'B', 'P': PL('P', 6), 'E': 'E'},
           {'%s e. Word NN0' % RVN: rvw, WG(DK(3)): B.S0.vals['3'][2], 'A. a e. ran %s a < ( 2 ^ B )' % RVN: ral},
           [('3', DK(3), B.S0.vals['3'][2]), ('6', ENCL(RR, DK(6)), g6)])
    PT5 = UP(PTN, '5', "Y'")
    rw1, x1 = w.rewrite(PT5, {PTN: (PB(NLG), pvN)}, ph)
    e, nrm, out2 = renorm(w, ph, B, R, [('3', C3(NLG)), ('5', C5(NLG)), ('5', "Y'")], N8, PT=PT5, pv=rw1)
    assert out2 == [('5', "Y'"), ('6', ENCL(RR, DK(6)))], out2
    rv = s([s([p1w, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, RR, P1f(PN))), p1e], 'eqtrd', '( %s -> %s = %s )' % (ph, RR, PGW))
    r2, x2 = w.rewrite(nrm, {RR: (PGW, rv)}, ph)
    assert x2 == DFIN, x2
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    D0 = triple_D(D)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, s([e, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, DFIN)), D0, DFIN))
    ln = s([s([p1w, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RVN, P1f(PN))),
            s([p1e], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, P1f(PN), PGW))], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RVN, PGW))
    rn, n2 = w.rewrite(n, {'( # ` %s )' % RVN: ('( # ` %s )' % PGW, ln)}, ph)
    assert n2 == UB, (n2, UB)
    t, C, D, n = hrrw(w, ph, t, C, D, n, neq=rn)
    assert C == CLN(LMP['Y2'], S, PT5), (C, PT5)
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([p0, t], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, REVT))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ph, FTY, FCOL, P0EQ, REVT))
    finish(w, st, lab)
    return w.run()


def tmipll():
    lab = 'tmipll'
    T = numtree11(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` poolGoF_runs ` at the machine up to the bound: ~ tmipzg at the family of ` PLInv ` ( ` P\' ` a letter), '
               'the entries by ~ tmipli , the frame by ~ tmiplt .')
    s = w.s
    B = Plf(w, ph, T)
    B.deep('plf', 0)
    B.deep('plf', 1)
    c, mk = B.c, B.mk
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmiplt', STMTS11['tmiplt']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, REVT))
    ex[FTY] = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    ex[P0EQ] = s([a2], 'simpld', '( %s -> %s )' % (ph, P0EQ))
    ex[REVT] = s([a2], 'simprd', '( %s -> %s )' % (ph, REVT))
    per = s([s([], 'tmipli', STMTS11['tmipli'])], 'ralrimiva', '( %s -> %s )' % (PSI, PER))
    ex[PER] = lift_from(w, PSI, ph, per)
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex[WG("Y'")] = B.y2w
    cl = Closure(w, ph, {'B': ('NN0', B.bn)})
    pgw = s([B.pgcl('L', B.lw), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PGW))
    cl.leaf('( # ` %s )' % PGW, 'NN0', s([pgw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, PGW)))
    cl.leaf('( TMB ` B )', 'NN0', tbn(w, ph, 'B', B.bn))
    ex['%s e. NN0' % UB] = cl.mem(UB, 'NN0')
    NQ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
    ssq = s([s([], 'ssrab2', '%s C_ %s' % (NQ, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, NQ, S))
    POPI_ = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (S, PID, S)
    ex['A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (NQ, PID, S)] = s([ssq, ex[POPI_], w.inst('ssralv')], 'sylc',
                                                                         '( %s -> A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s )' % (ph, NQ, PID, S))
    st = Bld(w, ph, c, ex)(GTREE)
    st2 = s([st, w.inst('tmipzg')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    finish(w, st2, lab)
    return w.run()


def tmiplf():
    lab = 'tmiplf'
    T = numtree11(TREE_PLF)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` poolGoF_runs ` at the machine: with ` x z k < 2 ^ b ` on ` 0 1 2 ` and the divisor list ` ds ` (entries '
               'below ` 2 ^ bd ` ) on ` 5 ` , ` 5 ` ends with the rest of its word and ` 6 ` with ` ( poolGo x z k ds ).1 ` pushed, '
               'every other stack restored, within ` ( ( poolGo x z k ds ).2 + 1 ) 16 B ( 3 ( bd + b ) + 10 ) ` steps (~ tmipll at '
               'the family; the charges sum by ~ tmipzs , the lengths by ~ tmpgmem ).')
    s = w.s
    B = Plf(w, ph, T)
    c, mk = B.c, B.mk
    eq = s([], 'eqid', '%s = %s' % (PF, PF))
    t, cc = inst(w, ph, 'tmipll', {PV: PF}, Bld(w, ph, c, {'%s = %s' % (PF, PF): s([eq], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}))
    C, D, n = triple_parts(cc)
    assert C == CS('plf') and D == CLN('E', S, DFIN), (C, D)
    # the sum
    NL_ = '( # ` L )'
    SUM0 = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NLG, YF)
    SUM1 = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NL_, YF)
    YVj = '( %s x. %s )' % (P2f('<" ( L ` j ) ">'), K14)
    SUM2 = 'sum_ j e. ( 0 ..^ %s ) ( %s + 2 )' % (NL_, YVj)
    assert SUM0 in n, n
    e1 = s([s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (ph, NLG, NL_))], 'sumeq1d', '( %s -> %s = %s )' % (ph, SUM0, SUM1))
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NL_)
    jj = s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NL_))
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
    fv = yfv(w, pj, jn)
    e2 = s([s([fv], 'oveq1d', '( %s -> ( ( %s ` j ) + 2 ) = ( %s + 2 ) )' % (pj, YF, YVj))], 'sumeq2dv', '( %s -> %s = %s )' % (ph, SUM1, SUM2))
    fzf = s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NL_)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NL_))
    DJ_ = DJ
    S1 = '<" %s ">' % DJ_
    lwj = lift_from(w, ph, pj, B.lw)
    djn = s([lwj, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pj, DJ_))
    fzgj = lift_from(w, ph, pj, B.fzg)
    pcl = s([s([fzgj, s([djn, w.inst('s1cl')], 'syl', '( %s -> %s e. Word NN0 )' % (pj, S1))], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (pj, FZG, S1)),
             w.inst('poolgocl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (pj, PGf(S1)))
    p2c = s([s([pcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pj, P2f(S1)))], 'nn0cnd', '( %s -> %s e. CC )' % (pj, P2f(S1)))
    clb = Closure(w, ph, {'B': ('NN0', B.bn), 'C': ('NN0', B.cn)})
    mbn = clb.mem(MB, 'NN0')
    clb.leaf(BB, 'NN0', tbn(w, ph, MB, mbn))
    k14c = s([clb.mem(K14, 'NN0')], 'nn0cnd', '( %s -> %s e. CC )' % (ph, K14))
    k14j = lift_from(w, ph, pj, k14c)
    yvc = s([p2c, k14j], 'mulcld', '( %s -> %s e. CC )' % (pj, YVj))
    twoc = s([s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % pj)
    SA = 'sum_ j e. ( 0 ..^ %s ) %s' % (NL_, YVj)
    SB = 'sum_ j e. ( 0 ..^ %s ) 2' % NL_
    e3 = s([fzf, yvc, twoc], 'fsumadd', '( %s -> %s = ( %s + %s ) )' % (ph, SUM2, SA, SB))
    nwn = B.nw
    e4 = s([s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NL_), s([], '2cn', '2 e. CC'), w.inst('fsumconst')], 'mp2an',
              '%s = ( ( # ` ( 0 ..^ %s ) ) x. 2 )' % (SB, NL_))], 'a1i', '( %s -> %s = ( ( # ` ( 0 ..^ %s ) ) x. 2 ) )' % (ph, SB, NL_))
    e5 = s([e4, s([s([nwn, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (ph, NL_, NL_))], 'oveq1d',
                  '( %s -> ( ( # ` ( 0 ..^ %s ) ) x. 2 ) = ( %s x. 2 ) )' % (ph, NL_, NL_))], 'eqtrd', '( %s -> %s = ( %s x. 2 ) )' % (ph, SB, NL_))
    SP = 'sum_ j e. ( 0 ..^ %s ) %s' % (NL_, P2f(S1))
    e6 = s([fzf, k14c, p2c], 'fsummulc1', '( %s -> ( %s x. %s ) = %s )' % (ph, SP, K14, SA))
    zs = s([s([B.fzg, B.lw], 'jca', '( %s -> ( %s /\\ L e. Word NN0 ) )' % (ph, FZG)), w.inst('tmipzs')], 'syl', '( %s -> %s = %s )' % (ph, SP, P2f('L')))
    e7 = s([s([e6], 'eqcomd', '( %s -> %s = ( %s x. %s ) )' % (ph, SA, SP, K14)), s([zs], 'oveq1d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ph, SP, K14, P2f('L'), K14))],
           'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (ph, SA, P2f('L'), K14))
    VAL = '( ( %s x. %s ) + ( %s x. 2 ) )' % (P2f('L'), K14, NL_)
    e8 = s([e3, s([e7, e5], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (ph, SA, SB, VAL))], 'eqtrd', '( %s -> %s = %s )' % (ph, SUM2, VAL))
    esum = s([s([e1, e2], 'eqtrd', '( %s -> %s = %s )' % (ph, SUM0, SUM2)), e8], 'eqtrd', '( %s -> %s = %s )' % (ph, SUM0, VAL))
    rn, n2 = w.rewrite(n, {SUM0: (VAL, esum)}, ph)
    # the bound
    BND = triple_parts(STMTS11['tmiplf'].rsplit(' -> ', 1)[1][:-2])[2]
    P2L = P2f('L')
    PL1 = '( # ` %s )' % PGW
    TBB = '( TMB ` B )'
    pgl = s([B.pgcl('L', B.lw), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, P2L))
    pgw = s([B.pgcl('L', B.lw), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PGW))
    clb.leaf(P2L, 'NN0', pgl)
    clb.leaf(PL1, 'NN0', s([pgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, PL1)))
    clb.leaf(NL_, 'NN0', nwn)
    clb.leaf(TBB, 'NN0', tbn(w, ph, 'B', B.bn))
    one, b16 = bbfacts(w, ph, Closure(w, ph, {'B': ('NN0', B.bn), 'C': ('NN0', B.cn)}), B.bn, B.cn)
    mem = s([s([B.fzg, B.lw], 'jca', '( %s -> ( %s /\\ L e. Word NN0 ) )' % (ph, FZG)), w.inst('tmpgmem')], 'syl',
            '( %s -> ( A. q e. ran %s ( q <_ F /\\ Z < q ) /\\ ( ( # ` %s ) <_ %s /\\ ( # ` L ) <_ %s ) ) )' % (ph, PGW, PGW, P2L, P2L))
    lens = s([mem], 'simprd', '( %s -> ( ( # ` %s ) <_ %s /\\ ( # ` L ) <_ %s ) )' % (ph, PGW, P2L, P2L))
    l1 = s([lens], 'simpld', '( %s -> %s <_ %s )' % (ph, PL1, P2L))
    l2 = s([lens], 'simprd', '( %s -> %s <_ %s )' % (ph, NL_, P2L))
    mo = s([B.bn, mbn, linarith(w, ph, [clb.ge0('C'), clb.ge0('B')], 'B <_ %s' % MB, closure=clb), w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TBB, BB))
    PP1 = '( %s + 1 )' % PL1
    QQ1 = '( %s + 1 )' % P2L
    f1 = s([clb.mem(TBB, 'RR'), clb.mem(BB, 'RR'), clb.mem(PP1, 'RR'), clb.ge0(PP1), mo], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, PP1, TBB, PP1, BB))
    f2 = s([clb.mem(PP1, 'RR'), clb.mem(QQ1, 'RR'), clb.mem(BB, 'RR'), clb.ge0(BB), linarith(w, ph, [l1], '%s <_ %s' % (PP1, QQ1), closure=clb)], 'lemul1ad',
           '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, PP1, BB, QQ1, BB))
    f3 = s([s([s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph), clb.mem(BB, 'RR'), clb.mem(P2L, 'RR'), clb.ge0(P2L),
            linarith(w, ph, [b16], '2 <_ %s' % BB, closure=clb)], 'lemul2ad', '( %s -> ( %s x. 2 ) <_ ( %s x. %s ) )' % (ph, P2L, P2L, BB))
    le2 = linarith(w, ph, [f1, f2, f3, l2, b16, one], '%s <_ %s' % (n2, BND), closure=clb, atoms=[P2L, PL1, NL_, TBB, BB], products=True)
    le = s([s([rn], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, BND, n2, BND)), le2], 'mpbird', '( %s -> %s <_ %s )' % (ph, n, BND))
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, clb.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()

if __name__ == '__main__':
    for l in SEL:
        if l != 'show':
            globals()[l]()
