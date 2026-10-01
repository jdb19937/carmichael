"""T11 helper (sortie file sorties/t11c.mm): Lean's ` coprimeToF x y z s t u ` at ` 4 2 3 5 6 7 ` (PrimList.lean
` coprimeToF_le_B ` ) on TMIcpt: ~ tm2floopu at the family of ` CpInv ` , prologue and epilogue by hand.

~ tm2fcpt is not used: its letters ` N" ` and ` N0 ` are at once the per-iteration class families
( ` ( N" ` i ) ` , ` ( N0 ` i ) ` ) and the epilogue classes ( ` N" C_ ( 2nd ` T ) ` ), which no instance with a
state-dependent iteration class satisfies.  The loop here is ~ tm2floopu with one triple per iteration.

  tmicpi   one iteration: ` cpBody ` ( ` dup 4 6 5 ; dup 2 7 5 ; modC 7 6 4 2 3 5 ; isZero 7 5 ; load' ( cmp := if flag
           then eq else lt ) ; dropNum 7 ; moveEntry 4 3 5 ; peekBraOr 4 ` ) from the family at ` i ` to ` i + 1 `
  tmicpt   the frame: the families' typings, the flag set at ` R `
  tmicpl   ~ tm2floopu at the families ( ` N' ` , ` P' ` letters)
  tmicpe   the epilogue: ` pushSym 6 comma ; pushBit 6 ( cmp =/= lt ) ; moveEntries 3 4 5 ; isZero 6 5 ; dropNum 6 `
  tmicptb  coprimeToF_le_B

    MM_DB=sorties/t11c.mm MM_HEAP=8g python3 tools/gen/t11c_cpt.py LABEL...
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
import t6blib


def _prefill():
    """the statements of sorties/t11.mm (tools/mm.py grep does not index it under MM_DB=sorties/t11c.mm)"""
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    txt = open(os.path.join(root, 'sorties', 't11.mm')).read()
    txt = re.sub(r'\$\(.*?\$\)', ' ', txt, flags=re.S)
    for m in re.finditer(r'(\S+)\s+\$[pa]\s+\|-(.*?)\$[=.]', txt, flags=re.S):
        t6blib._STMT.setdefault(m.group(1), ' '.join(m.group(2).split()))


_prefill()

from lin import linarith, nlinarith, lineq
from cl import Closure
from t7lib import famval, fam_unpack, fam_pack, ifex_closed, mval, rab_in, not1o, tuple_facts, st_comps, lamval
from t7_e_cmp import lamty
from t7_h_iz import lset_val, lset_ty
from t7b_h_dmq import rab_elim
from t10_e_doa import lift_from
from t10_u_s2s import expose
from t10_t_dn import cnfl_at, drp_empty
from t10_s_rbo import rbo_ty
import t8alib as A8
import num

SEL = sys.argv[1:]
UO = os.environ.get('T11C_UO') == '1'

CP = '( W CoprimeTo G )'
RR = '( 2nd ` %s )' % CP
CC = '( 1st ` %s )' % CP
NW = '( # ` W )'
DRP = lambda t: '( W substr <. %s , %s >. )' % (t, NW)
C4 = lambda t: ENCL(DRP(t), 'X')
PFX = lambda t: '( W prefix %s )' % t
RP = lambda t: '( reverse ` %s )' % PFX(t)
C3 = lambda t: ENCL(RP(t), DK(3))
PB = lambda t: UPS('D', ('3', C3(t)), ('4', C4(t)))
FV = lambda t: 'if ( %s = %s , 1o , (/) )' % (t, RR)
CV = lambda t: 'if ( ( %s = %s /\\ %s = (/) ) , 1o , (/) )' % (t, RR, CC)
COND = lambda h, t: '( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = %s )' % (h, FV(t), h, CV(t))
NCL = lambda t: '{ h e. TMSt | %s }' % COND('h', t)
NFM = '( j e. NN0 |-> %s )' % NCL('j')
PF = '( j e. NN0 |-> %s )' % PB('j')
NV, PV = "N'", "P'"
NQv = lambda o, q: '{ h e. TMSt | ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = %s ) }' % (o, q)
NQC = lambda o, q: (lambda t: '( ( TMfl ` %s ) = %s /\\ ( TMcmp ` %s ) = %s )' % (t, o, t, q))
TBN = '( TMB ` N )'
TPR = '( ( 6 x. %s ) + 2 )' % TBN
PSI_T = (TREE_CPT, ('%s = %s' % (NV, NFM), '%s = %s' % (PV, PF)))
PSI = cj(PSI_T)
LMP = FRAGS['cpt'].lmap()
PCB = PL('P', FRAGS['cpt'].slot(0))
LCB = FRAGS['cpb'].lmap(PCB, LMP['Z4'])
GM = {'A': LMP['Z4'], 'B0': LMP['Y1'], 'E': LMP['Z5'], 'C0': CNFL, 'R': RR, "T'": TPR, 'N': NV, 'P': PV}
_LA, _LC = split_imp(stmt('tm2floopu'))
LTREE = tsub(parse_conj(_LA), GM)
LCONCL = tsub_text(_LC, GM)
LTYP, LPER, LEXIT = LTREE[1]
_pre = 'A. i e. ( 0 ..^ %s ) ' % RR
assert LPER.startswith(_pre)
LBODY = LPER[len(_pre):]
T_I = (PSI_T, 'i e. ( 0 ..^ %s )' % RR)
UE = '( ( %s x. ( ( 2 x. N ) + 6 ) ) + ; 1 4 )' % RR
CONCL_E = TRI(CLN(LMP['Z5'], NCL(RR), PB(RR)), CLN('E', NFL(CC), 'D'), UE)
add11('tmicpi', T_I, LBODY)
add11('tmicpt', PSI_T, '( %s /\\ %s )' % (LTYP, LEXIT))
add11('tmicpl', PSI_T, LCONCL)
add11('tmicpe', TREE_CPT, CONCL_E)
for _l in ('tmicpi', 'tmicpt', 'tmicpl', 'tmicpe'):
    ORDER11.remove(_l)
    ORDER11.insert(ORDER11.index('tmicptb'), _l)

if __name__ == '__main__' and 'show' in SEL:
    for _l in ('tmicpi', 'tmicpt', 'tmicpl', 'tmicpe', 'tmicptb'):
        print(_l, len(STMTS11[_l]))
        print(STMTS11[_l]); print()


class Cp(Base):
    """the facts under an antecedent containing the cpt tree"""
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        ww, gn, nn = c0['W e. Word NN0'], c0['G e. NN0'], c0['N e. NN0']
        xw, yw = c0[WG('X')], c0[WG('Y')]
        eqs = {'4': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw)), '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', yw))}
        Base.__init__(self, w, ph, T, N8, 'cpt', eqs)
        s = w.s
        self.ww, self.gn, self.nn, self.xw, self.yw = ww, gn, nn, xw, yw
        self.nwn = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
        self.tbn = s([s([nn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TBN))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TBN))
        cpc = s([ww, gn, w.inst('coprimetocl')], 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (ph, CP))
        self.rn = s([cpc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, RR))
        self.c2 = s([cpc, w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (ph, CC))
        self.rle = s([ww, gn, w.inst('coprimetolen')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, RR, NW))
        self.pvs = {}

    def ss(self, N):
        w, ph = self.w, self.ph
        a = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % N)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, N))
        return w.s([a, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, N, S))

    def tz(self, t, tn, tle):
        """( ph -> t e. ( 0 ... # W ) ) from tle : t <_ RR"""
        w, ph, s = self.w, self.ph, self.w.s
        cl = Closure(w, ph, {})
        cl.leaf(NW, 'NN0', self.nwn)
        cl.leaf(RR, 'NN0', self.rn)
        cl.leaf(t, 'NN0', tn)
        le = linarith(w, ph, [tle, self.rle], '%s <_ %s' % (t, NW), closure=cl)
        return s([s([tn, self.nwn, le], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, t, NW, t, NW)),
                  w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, t, NW))

    def pbst(self, t):
        w, ph, s = self.w, self.ph, self.w.s
        dw = s([self.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DRP(t)))
        rw = s([s([self.ww, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PFX(t))), w.inst('revcl')], 'syl',
               '( %s -> %s e. Word NN0 )' % (ph, RP(t)))
        g3 = self.g(C3(t), enclg(w, ph, RP(t), rw, DK(3), self.S0.vals['3'][2]))
        g4 = self.g(C4(t), enclg(w, ph, DRP(t), dw, 'X', self.xw))
        return self.S0.upd('3', C3(t), g3).upd('4', C4(t), g4)

    def pv(self, t, tn):
        """(( ph -> ( P' ` t ) = PB( t ) ), Stacks at ( P' ` t )) from tn : t e. NN0"""
        if t not in self.pvs:
            fam = self.c['%s = %s' % (PV, PF)]
            self.pvs[t] = fam_at(self.w, self.ph, self.mk, self.ne, fam, PV, 'j', 'NN0', PB, t, tn, self.pbst(t))
        return self.pvs[t]

    def nv(self, t, tn):
        """( ph -> ( N' ` t ) = NCL( t ) )"""
        w, ph, s = self.w, self.ph, self.w.s
        fam = self.c['%s = %s' % (NV, NFM)]
        e = s([fam], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, NV, t, NFM, t))
        return s([e, famval(w, ph, COND, t, tn)], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, NV, t, NCL(t)))

    def nvss(self, t, tn):
        w, ph, s = self.w, self.ph, self.w.s
        return s([self.nv(t, tn), self.ss(NCL(t))], 'eqsstrd', '( %s -> ( %s ` %s ) C_ %s )' % (ph, NV, t, S))


def _fcl(w, ph, f, comp):
    """( ph -> comp e. 2o ) (or 3o for cmp) for a set field value 1o , (/) or if ( _ , 1o , (/) )"""
    if f == 'cmp':
        one, zero, cod = ('bw1oel3o', '1o e. 3o'), ('bw0el3o', '(/) e. 3o'), '3o'
    else:
        one, zero, cod = ('1oel2o', '1o e. 2o'), ('0el2o', '(/) e. 2o'), '2o'
    if comp == '1o':
        return closed(w, ph, one[0], one[1])
    if comp == '(/)':
        return closed(w, ph, zero[0], zero[1])
    e = w.s([w.s([], one[0], one[1]), w.s([], zero[0], zero[1])], 'ifcli', '%s e. %s' % (comp, cod))
    return w.s([e], 'a1i', '( %s -> %s e. %s )' % (ph, comp, cod))


def lset_val3(w, ph, kw_of, A, amem):
    """a load ` ( u e. TMSt |-> SETF( u , ... ) ) ` at A (cmp typed in 3o): value, membership, fields"""
    from t7lib import lamval, _transport
    X_of = lambda t: SETF(t, **kw_of(t))
    val = lamval(w, ph, X_of, A, amem, closed(w, ph, 'opex', '%s e. _V' % X_of(A)))
    kw = kw_of(A)
    cl = st_comps(w, ph, A, amem)
    comps = [kw.get(f, FLD(f, A)) for f in ORDER]
    cls = [_fcl(w, ph, f, comp) if f in kw else cl[f] for f, comp in zip(ORDER, comps)]
    mem, vals = tuple_facts(w, ph, comps, cls)
    N = '( %s ` %s )' % ('( u e. TMSt |-> %s )' % X_of('u'), A)
    return _transport(w, ph, N, val, mem, vals, comps)


def lset_ty3(w, ph, mk, lam, kw_of):
    from t7_e_cmp import lamty as _lamty
    X_of = lambda t: SETF(t, **kw_of(t))
    assert lam == '( u e. TMSt |-> %s )' % X_of('u')
    phu = 'u e. TMSt'
    uu = w.s([], 'id', '( %s -> u e. TMSt )' % phu)
    cl = st_comps(w, phu, 'u', uu)
    kw = kw_of('u')
    comps = [kw.get(f, FLD(f, 'u')) for f in ORDER]
    cls = [_fcl(w, phu, f, comp) if f in kw else cl[f] for f, comp in zip(ORDER, comps)]
    mem, _ = tuple_facts(w, phu, comps, cls)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    t = _lamty(w, ph, mk, lam, X_of, 'TMSt', sv, mem)
    e = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    e2 = w.s([e], 'oveq1d', '( %s -> ( TMSt ^m ( 2nd ` T ) ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    return w.s([t, e2], 'eleqtrd', '( %s -> %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % (ph, lam))


def ifeq_bi(w, ph, c1, c2, bi):
    """( ph -> if ( c1 , 1o , (/) ) = if ( c2 , 1o , (/) ) ) from bi : ( ph -> ( c1 <-> c2 ) )"""
    return w.s([bi], 'ifbid', '( %s -> if ( %s , 1o , (/) ) = if ( %s , 1o , (/) ) )' % (ph, c1, c2))


def tmicpi():
    lab = 'tmicpi'
    T = numtree11(T_I)
    ph = cj(T)
    w = W(lab, 'One iteration of Lean\'s ` coprimeToF ` loop at the machine ( ` CpInv ` , ` cpBody_runs ` ): below ` R = '
               '( coprimeTo Q k ).2 ` the flag is clear, and ` cpBody ` ( ` dup 4 6 5 ; dup 2 7 5 ; modC 7 6 4 2 3 5 ; isZero 7 5 ; '
               'load\' ( cmp := if flag then eq else lt ) ; dropNum 7 ; moveEntry 4 3 5 ; peekBraOr 4 ` ) moves the ` i ` -th entry '
               'from 4 to 3 and sets flag and cmp to their values at ` i + 1 ` (~ tmcpch ), within ` 6 B b + 2 ` steps.')
    s = w.s
    B = Cp(w, ph, T)
    c, mk = B.c, B.mk
    B.deep('cpt', 0)
    io = c['i e. ( 0 ..^ %s )' % RR]
    inn = s([io, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph)
    ilt = s([io, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ph, RR))
    cl = Closure(w, ph, {'i': ('NN0', inn), 'N': ('NN0', B.nn)})
    cl.leaf(NW, 'NN0', B.nwn)
    cl.leaf(RR, 'NN0', B.rn)
    cl.leaf(TBN, 'NN0', B.tbn)
    I1 = '( i + 1 )'
    i1n = s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, I1))
    # tmcpch at i
    WI = '( W ` i )'
    MD = '( G mod %s ) = 0' % WI
    RI = '%s = %s' % (I1, RR)
    CZ = '%s = (/)' % CC
    LN = '%s = %s' % (I1, NW)
    BODY = '( i < %s /\\ ( %s <-> ( %s /\\ %s ) ) /\\ ( ( %s \\/ %s ) <-> %s ) )' % (NW, MD, RI, CZ, MD, LN, RI)
    ch = s([s([s([B.ww, B.gn], 'jca', '( %s -> ( W e. Word NN0 /\\ G e. NN0 ) )' % ph), s([inn, ilt], 'jca', '( %s -> ( i e. NN0 /\\ i < %s ) )' % (ph, RR))],
              'jca', '( %s -> ( ( W e. Word NN0 /\\ G e. NN0 ) /\\ ( i e. NN0 /\\ i < %s ) ) )' % (ph, RR)), w.inst('tmcpch')], 'syl',
           '( %s -> %s )' % (ph, BODY))
    ilw = s([ch], 'simp1d', '( %s -> i < %s )' % (ph, NW))
    mdb = s([ch], 'simp2d', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (ph, MD, RI, CZ))
    orb = s([ch], 'simp3d', '( %s -> ( ( %s \\/ %s ) <-> %s ) )' % (ph, MD, LN, RI))
    # the flag at i is clear
    ine = s([s([cl.mem('i', 'RR'), ilt], 'ltned', '( %s -> i =/= %s )' % (ph, RR))], 'neneqd', '( %s -> -. i = %s )' % (ph, RR))
    f0 = s([ine], 'iffalsed', '( %s -> %s = (/) )' % (ph, FV('i')))
    NI = '( %s ` i )' % NV
    pm = '( %s /\\ m e. %s )' % (ph, NI)
    mni = s([s([], 'simpr', '( %s -> m e. %s )' % (pm, NI)), lift_from(w, ph, pm, s([B.c['%s = %s' % (NV, NFM)]], 'fveq1d',
                                                                                    '( %s -> %s = ( %s ` i ) )' % (ph, NI, NFM)))],
            'eleqtrd', '( %s -> m e. ( %s ` i ) )' % (pm, NFM))
    mm, mc = fam_unpack(w, pm, COND, 'i', lift_from(w, ph, pm, inn), 'm', mni)
    fl0 = s([s([mc], 'simpld', '( %s -> ( TMfl ` m ) = %s )' % (pm, FV('i'))), lift_from(w, ph, pm, f0)], 'eqtrd', '( %s -> ( TMfl ` m ) = (/) )' % pm)
    part1 = s([cnfl_at(w, pm, mm, fl0, False)], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ph, NI, CNFL))
    # the family at i, stack 4 split at its head entry
    ile = linarith(w, ph, [ilt], 'i <_ %s' % RR, closure=cl)
    pvi, SI = B.pv('i', inn)
    iw = s([s([inn, s([B.nwn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, NW)), ilw], '3jca',
              '( %s -> ( i e. NN0 /\\ %s e. ZZ /\\ i < %s ) )' % (ph, NW, NW)), w.inst('elfzo0z')], 'sylibr',
           '( %s -> i e. ( 0 ..^ %s ) )' % (ph, NW))
    V1 = DRP(I1)
    win = s([B.ww, iw, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WI))
    v1w = s([B.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, V1))
    dr = s([B.ww, iw, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, DRP('i'), WI, V1))
    ec = s([win, v1w, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" %s "> ++ %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )'
           % (ph, WI, V1, WI, V1))
    e1 = s([s([dr], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( <" %s "> ++ %s ) ) )' % (ph, DRP('i'), WI, V1)), ec], 'eqtrd',
           '( %s -> ( encList ` %s ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (ph, DRP('i'), WI, V1))
    ew = encw(w, ph, WI, win)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    elv = s([v1w, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, V1))
    ca1 = s([ew, wgcat(w, ph, '<" 4 ">', '( encList ` %s )' % V1, s4, elv), B.xw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ X ) = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) )'
            % (ph, WI, V1, WI, V1))
    ca2 = s([s4, elv, B.xw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) = ( <" 4 "> ++ %s ) )' % (ph, V1, C4(I1)))
    KT = EWg(WI, C4(I1))
    r1 = s([s([e1], 'oveq1d', '( %s -> %s = ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) ++ X ) )' % (ph, C4('i'), WI, V1)), ca1], 'eqtrd',
           '( %s -> %s = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) )' % (ph, C4('i'), WI, V1))
    r2 = s([r1, s([ca2], 'oveq2d', '( %s -> ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ ( encList ` %s ) ) ++ X ) ) = %s )' % (ph, WI, V1, KT))], 'eqtrd',
           '( %s -> %s = %s )' % (ph, C4('i'), KT))
    g1 = B.g(C4(I1), enclg(w, ph, V1, v1w, 'X', B.xw))
    gk = B.g(KT, ewg_(w, ph, WI, win, C4(I1), g1))
    chain0 = [('3', C3('i')), ('4', KT)]
    R = B.run()
    S3 = B.S0.upd('3', C3('i'), B.gam[C3('i')])
    Ssp = S3.upd('4', KT, gk)
    R.S, R.chain = Ssp, list(chain0)
    for _k, (_txt, _st, _g) in Ssp.vals.items():
        R.gam[_txt] = _g
    p2 = '( 2 ^ N )'
    # the entry bounds
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ %s ) )' % (ph, NW)), iw, w.inst('fnfvelrn')], 'syl2anc',
           '( %s -> %s e. ran W )' % (ph, WI))
    wlt = s([s([], 'breq1', '( a = %s -> ( a < %s <-> %s < %s ) )' % (WI, p2, WI, p2)), wr, c[RALB('W', 'N')]], 'rspcdva',
            '( %s -> %s < %s )' % (ph, WI, p2))
    w1 = s([s([], 'breq2', '( a = %s -> ( 1 <_ a <-> 1 <_ %s ) )' % (WI, WI)), wr, c['A. a e. ran W 1 <_ a']], 'rspcdva',
           '( %s -> 1 <_ %s )' % (ph, WI))
    winn = s([s([win, w1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (ph, WI, WI)), s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (WI, WI, WI))],
             'sylibr', '( %s -> %s e. NN )' % (ph, WI))
    GMW = '( G mod %s )' % WI
    gmn = s([s([B.gn], 'nn0zd', '( %s -> G e. ZZ )' % ph), winn, w.inst('zmodcl')], 'syl2anc',
            '( %s -> %s e. NN0 )' % (ph, GMW))
    cl.leaf(WI, 'NN0', win)
    cl.leaf(GMW, 'NN0', gmn)
    gml = s([s([B.gn], 'nn0zd', '( %s -> G e. ZZ )' % ph), winn, w.inst('zmodfzo')], 'syl2anc', '( %s -> %s e. ( 0 ..^ %s ) )' % (ph, GMW, WI))
    gml2 = s([gml, w.inst('elfzolt2')], 'syl', '( %s -> %s < %s )' % (ph, GMW, WI))
    gmlt = s([cl.mem(GMW, 'RR'), cl.mem(WI, 'RR'), s([s([s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph), B.nn], 'reexpcld',
                                                   '( %s -> %s e. RR )' % (ph, p2)), gml2, wlt], 'lttrd', '( %s -> %s < %s )' % (ph, GMW, p2))
    PB8 = lambda n: PL(PCB, n)
    # 1. dup 4 6 5
    E6a = EWg(WI, DK(6))
    g6a = B.g(E6a, ewg_(w, ph, WI, win, DK(6), B.S0.vals['6'][2]))
    B.call(R, 'tmidupb', {'K': '4', 'J': '6', 'I': '5', 'F': WI, 'N': 'N', 'X': C4(I1), 'P': PB8(2), 'E': LCB['Y2']},
           {'%s e. NN0' % WI: win, 'N e. NN0': B.nn, '%s < %s' % (WI, p2): wlt}, [('6', E6a, g6a)])
    # 2. dup 2 7 5
    E7a = EWg('G', DK(7))
    g7a = B.g(E7a, ewg_(w, ph, 'G', B.gn, DK(7), B.S0.vals['7'][2]))
    B.call(R, 'tmidupb', {'K': '2', 'J': '7', 'I': '5', 'F': 'G', 'N': 'N', 'X': 'Y', 'P': PB8(3), 'E': LCB['Y3']},
           {'G e. NN0': B.gn, 'N e. NN0': B.nn, 'G < %s' % p2: c['G < %s' % p2]}, [('7', E7a, g7a)])
    # 3. modC 7 6 4 2 3 5
    E7b = EWg(GMW, DK(7))
    g7b = B.g(E7b, ewg_(w, ph, GMW, gmn, DK(7), B.S0.vals['7'][2]))
    B.call(R, 'tmimodcb', {'K': '7', 'J': '6', 'I': '4', "I'": '2', 'I"': '3', 'I0': '5', 'F': 'G', 'G': WI, 'N': 'N',
                           'X': DK(7), 'Y': DK(6), 'P': PB8(4), 'E': LCB['Y4']},
           {'G e. NN0': B.gn, '%s e. NN' % WI: winn, 'N e. NN0': B.nn, 'G < %s' % p2: c['G < %s' % p2], '%s < %s' % (WI, p2): wlt},
           [('7', E7b, g7b), ('6', DK(6), B.S0.vals['6'][2])])
    # 4. isZero 7 5
    B.call(R, 'tmiizbs', {'K': '7', 'I': '5', 'F': GMW, 'N': 'N', 'X': DK(7), 'P': PB8(5), 'E': LCB['Z1']},
           {'%s e. NN0' % GMW: gmn, 'N e. NN0': B.nn, '%s < %s' % (GMW, p2): gmlt}, [])
    VI = 'if ( %s , 1o , (/) )' % MD
    NQI = NQv(VI, VI)
    # 5. load ( cmp := if flag then eq else lt ) : NFL( VI ) into NQ( VI , VI )
    kw = lambda t: dict(cmp='if ( ( TMfl ` %s ) = 1o , 1o , (/) )' % t)
    pr_ = '( %s /\\ r e. %s )' % (ph, NFL(VI))
    rr, rf = A8.nfl_unpack(w, pr_, VI, 'r', s([], 'simpr', '( %s -> r e. %s )' % (pr_, NFL(VI))))
    nv = lset_val3(w, pr_, kw, 'r', rr)
    NR = '( %s ` r )' % L_CFL
    flr = s([nv['fields']['fl'], rf], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pr_, NR, VI))
    ci = s([s([rf], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (pr_, VI)),
            s([s([], 'tmcif1', '( %s = 1o <-> %s )' % (VI, MD))], 'a1i', '( %s -> ( %s = 1o <-> %s ) )' % (pr_, VI, MD))], 'bitrd',
           '( %s -> ( ( TMfl ` r ) = 1o <-> %s ) )' % (pr_, MD))
    cmr = s([nv['fields']['cmp'], ifeq_bi(w, pr_, '( TMfl ` r ) = 1o', MD, ci)], 'eqtrd', '( %s -> ( TMcmp ` %s ) = %s )' % (pr_, NR, VI))
    inm = rab_in(w, pr_, NQI, NQC(VI, VI), NR, nv['mem'], s([flr, cmr], 'jca', '( %s -> %s )' % (pr_, NQC(VI, VI)(NR))))
    hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, NFL(VI), L_CFL, NQI))
    B.call(R, 'tm2flg', {'A': LCB['Z1'], 'E': LCB['Y5'], 'F': L_CFL, 'N': NFL(VI), "N'": NQI},
           {LTY(L_CFL): lset_ty3(w, ph, mk, L_CFL, kw), SSS(NFL(VI)): B.ss(NFL(VI)), SSS(NQI): B.ss(NQI),
            'A. r e. %s ( %s ` r ) e. %s' % (NFL(VI), L_CFL, NQI): hl}, [])
    # 6. dropNum 7
    Son, old = expose(w, ph, B, R, '7')
    B.call(R, 'tmidropnbq', {'K': '7', 'F': GMW, 'N': 'N', 'X': DK(7), 'O': VI, 'Q': VI, 'P': PB8(6), 'E': LCB['Y6']},
           {'%s e. NN0' % GMW: gmn, 'N e. NN0': B.nn, '%s < %s' % (GMW, p2): gmlt}, [('7', DK(7), B.S0.vals['7'][2])], on=(Son, old))
    # 7. moveEntry 4 3 5
    E3 = EWg(WI, C3('i'))
    g3 = B.g(E3, ewg_(w, ph, WI, win, C3('i'), B.gam[C3('i')]))
    B.call(R, 'tmimebq', {'K': '4', 'J': '3', 'I': '5', 'F': WI, 'N': 'N', 'X': C4(I1), 'O': VI, 'Q': VI, 'P': PB8(7), 'E': LCB['Z2']},
           {'%s e. NN0' % WI: win, 'N e. NN0': B.nn, '%s < %s' % (WI, p2): wlt}, [('4', C4(I1), g1), ('3', E3, g3)])
    # 8. peekBraOr 4: NQ( VI , VI ) into NCL( i + 1 )
    W_ = C4(I1)
    vn0 = encl_ne0(w, ph, V1, v1w, 'X', B.xw)
    eq, hg, tg = A8.word_split(w, ph, W_, g1, vn0)
    HD, TL = A8.HD0(W_), A8.TL1(W_)
    kv = s([R.S.vals['4'][1], eq], 'eqtrd', '( %s -> ( %s ` 4 ) = ( <" %s "> ++ %s ) )' % (ph, R.S.D, HD, TL))
    hb = s([v1w, B.xw, w.inst('tmexhdb')], 'syl2anc', '( %s -> ( %s = 2 <-> %s = (/) ) )' % (ph, HD, V1))
    i1z = s([iw, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ph, I1, NW))
    de = drp_empty(w, ph, B.ww, B.nwn, I1, i1z)
    e1_ = s([s([], 'tmcif1', '( %s = 1o <-> %s )' % (VI, MD))], 'a1i', '( %s -> ( %s = 1o <-> %s ) )' % (ph, VI, MD))
    e2_ = s([hb, de], 'bitrd', '( %s -> ( %s = 2 <-> %s ) )' % (ph, HD, LN))
    ob = s([e1_, e2_], 'orbi12d', '( %s -> ( ( %s = 1o \\/ %s = 2 ) <-> ( %s \\/ %s ) ) )' % (ph, VI, HD, MD, LN))
    bi = s([ob, orb], 'bitrd', '( %s -> ( ( %s = 1o \\/ %s = 2 ) <-> %s ) )' % (ph, VI, HD, RI))
    pq = '( %s /\\ r e. %s )' % (ph, NQI)
    Lq = lambda st: lift_from(w, ph, pq, st)
    rq, cq = rab_elim(w, pq, NQI, NQC(VI, VI), 'r', s([], 'simpr', '( %s -> r e. %s )' % (pq, NQI)))
    rfl = s([cq], 'simpld', '( %s -> ( TMfl ` r ) = %s )' % (pq, VI))
    rcm = s([cq], 'simprd', '( %s -> ( TMcmp ` r ) = %s )' % (pq, VI))
    NB_ = '( %s ` <. r , ( inl ` %s ) >. )' % (RBO, HD)
    V1r = 'if ( ( ( TMfl ` r ) = 1o \\/ %s = 2 ) , 1o , (/) )' % HD
    mb = s([rq, Lq(hg), w.inst('tmrdbrorc')], 'syl2anc', '( %s -> %s e. %s )' % (pq, NB_, NFL(V1r)))
    nbm, nbf = A8.nfl_unpack(w, pq, V1r, NB_, mb)
    o1 = s([s([rfl], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (pq, VI))], 'orbi1d',
           '( %s -> ( ( ( TMfl ` r ) = 1o \\/ %s = 2 ) <-> ( %s = 1o \\/ %s = 2 ) ) )' % (pq, HD, VI, HD))
    o2 = s([o1, Lq(bi)], 'bitrd', '( %s -> ( ( ( TMfl ` r ) = 1o \\/ %s = 2 ) <-> %s ) )' % (pq, HD, RI))
    fb = s([nbf, ifeq_bi(w, pq, '( ( TMfl ` r ) = 1o \\/ %s = 2 )' % HD, RI, o2)], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pq, NB_, FV(I1)))
    ihd = s([Lq(hg), w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (pq, HD, OPT))
    cb = s([s([rq, ihd, w.inst('tmrdbrorq')], 'syl2anc', '( %s -> ( TMcmp ` %s ) = ( TMcmp ` r ) )' % (pq, NB_)), rcm], 'eqtrd',
           '( %s -> ( TMcmp ` %s ) = %s )' % (pq, NB_, VI))
    cb2 = s([cb, Lq(ifeq_bi(w, ph, MD, '( %s /\\ %s )' % (RI, CZ), mdb))], 'eqtrd', '( %s -> ( TMcmp ` %s ) = %s )' % (pq, NB_, CV(I1)))
    N1c = NCL(I1)
    inn1 = rab_in(w, pq, N1c, lambda t: COND(t, I1), NB_, nbm, s([fb, cb2], 'jca', '( %s -> %s )' % (pq, COND(NB_, I1))))
    pk = s([inn1], 'ralrimiva', '( %s -> A. r e. %s %s e. %s )' % (ph, NQI, NB_, N1c))
    ex = {'( %s ` 4 ) = ( <" %s "> ++ %s )' % (R.S.D, HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
          'A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (NQI, RBO, HD, N1c): pk,
          '%s e. %s' % (RBO, A8.HDLS): rbo_ty(w, ph, mk), SSS(NQI): B.ss(NQI), SSS(N1c): B.ss(N1c)}
    B.call(R, 'tm2lpk', {'A': LCB['Z2'], 'E': LMP['Z4'], 'K': '4', 'F': RBO, 'Z': HD, 'X': TL, 'N': NQI, "N'": N1c}, ex, [])
    # the post
    cur, out2 = R.normalize(N8)
    assert out2 == [('3', E3), ('4', C4(I1))], out2
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    le = linarith(w, ph, [], '%s <_ %s' % (n, TPR), closure=cl, atoms=[TBN])
    t = hrle(w, ph, mk['phm'], t, C, D, n, TPR, cl.mem(TPR, 'NN0'), le)
    n = TPR
    # the pre class ( N' ` i ) and stacks ( P' ` i )
    X1 = chain_text('D', chain0)
    C2 = CLN(LMP['Y1'], NI, X1)
    t = hrssc(w, ph, mk['phm'], t, C, D, n, C2, clnss(w, ph, LMP['Y1'], NI, S, X1, B.nvss('i', inn)))
    rx, xx = w.rewrite(X1, {KT: (C4('i'), s([r2], 'eqcomd', '( %s -> %s = %s )' % (ph, KT, C4('i'))))}, ph)
    assert xx == PB('i'), xx
    PT = '( %s ` i )' % PV
    cpre = clneq(w, ph, LMP['Y1'], NI, s([rx, s([pvi], 'eqcomd', '( %s -> %s = %s )' % (ph, PB('i'), PT))], 'eqtrd',
                                         '( %s -> %s = %s )' % (ph, X1, PT)), X1, PT)
    # the post stacks: EW( W_i , C3( i ) ) = C3( i + 1 )
    Dst = triple_D(D)
    RPi, RP1 = RP('i'), RP(I1)
    pw = s([B.ww, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PFX('i')))
    rpw = s([pw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RPi))
    sw = s([win, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (ph, WI))
    pf1 = s([B.ww, iw, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (ph, PFX(I1), PFX('i'), WI))
    rv1 = s([s([pf1], 'fveq2d', '( %s -> %s = ( reverse ` ( %s ++ <" %s "> ) ) )' % (ph, RP1, PFX('i'), WI)),
             s([pw, sw, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ %s ) )'
               % (ph, PFX('i'), WI, WI, RPi))], 'eqtrd', '( %s -> %s = ( ( reverse ` <" %s "> ) ++ %s ) )' % (ph, RP1, WI, RPi))
    rv2 = s([rv1, s([s([s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (WI, WI))], 'oveq1i',
                       '( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s )' % (WI, RPi, WI, RPi))], 'a1i',
                    '( %s -> ( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, WI, RPi, WI, RPi))], 'eqtrd',
            '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, RP1, WI, RPi))
    ELi = '( encList ` %s )' % RPi
    ec3 = s([win, rpw, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" %s "> ++ %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ %s ) ) )'
            % (ph, WI, RPi, WI, ELi))
    el3 = s([s([rv2], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( <" %s "> ++ %s ) ) )' % (ph, RP1, WI, RPi)), ec3], 'eqtrd',
            '( %s -> ( encList ` %s ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, RP1, WI, ELi))
    elw = s([rpw, w.inst('tm2lenccl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ELi))
    d3 = B.S0.vals['3'][2]
    cb1 = s([ew, wgcat(w, ph, '<" 4 ">', ELi, s4, elw), d3, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ %s ) ) ++ ( D ` 3 ) ) = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) ) )'
            % (ph, WI, ELi, WI, ELi))
    cb2_ = s([s4, elw, d3, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) = ( <" 4 "> ++ %s ) )' % (ph, ELi, C3('i')))
    c31 = s([s([s([el3], 'oveq1d', '( %s -> %s = ( ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ %s ) ) ++ ( D ` 3 ) ) )' % (ph, C3(I1), WI, ELi)), cb1], 'eqtrd',
               '( %s -> %s = ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) ) )' % (ph, C3(I1), WI, ELi)),
             s([cb2_], 'oveq2d', '( %s -> ( ( encNatGam ` %s ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` 3 ) ) ) = %s )' % (ph, WI, ELi, E3))], 'eqtrd',
            '( %s -> %s = %s )' % (ph, C3(I1), E3))
    r3, x3 = w.rewrite(Dst, {E3: (C3(I1), s([c31], 'eqcomd', '( %s -> %s = %s )' % (ph, E3, C3(I1))))}, ph)
    assert x3 == PB(I1), x3
    pv1, _ = B.pv(I1, i1n)
    P1T = '( %s ` %s )' % (PV, I1)
    deq = s([r3, pv1], 'eqtr4d', '( %s -> %s = %s )' % (ph, Dst, P1T))
    N1 = '( %s ` %s )' % (NV, I1)
    cqe = s([B.nv(I1, i1n)], 'eqcomd', '( %s -> %s = %s )' % (ph, N1c, N1))
    lab_ = LMP['Z4']
    ceq = s([clnneq(w, ph, lab_, cqe, N1c, N1, Dst), clneq(w, ph, lab_, N1, deq, Dst, P1T)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN(lab_, N1, P1T)))
    t, C, D, n = hrrw(w, ph, t, C2, D, n, ceq=cpre, deq=ceq)
    st = s([part1, t], 'jca', '( %s -> %s )' % (ph, LBODY))
    finish(w, st, lab)
    return w.run(unify_only=UO)


def tmicpt():
    lab = 'tmicpt'
    w = W(lab, 'The frame of Lean\'s ` coprimeToF ` loop at the machine: for ` i <_ R ` the class family is a set of states '
               'and the stack family a stack assignment, and at ` R = ( coprimeTo Q k ).2 ` the flag is set.')
    s = w.s
    DI = 'i e. ( 0 ... %s )' % RR
    TT = numtree11((PSI_T, DI))
    pt = cj(TT)
    B = Cp(w, pt, TT)
    ii = B.c[DI]
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    pv, St = B.pv('i', inn)
    body = LTYP[len('A. %s ' % DI):]
    one = s([B.nvss('i', inn), St.memb], 'jca', '( %s -> %s )' % (pt, body))
    p0 = cj((PSI_T, DI))
    k = s([], 't10stk', ST_NUMS)
    one0 = s([k, one], 'mpan2', '( %s -> %s )' % (p0, body))
    typ = s([one0], 'ralrimiva', '( %s -> %s )' % (PSI, LTYP))
    TE = numtree11(PSI_T)
    pe = cj(TE)
    L = Cp(w, pe, TE)
    f1 = s([s([], 'eqidd', '( %s -> %s = %s )' % (pe, RR, RR))], 'iftrued', '( %s -> %s = 1o )' % (pe, FV(RR)))
    NE = '( %s ` %s )' % (NV, RR)
    pm = '( %s /\\ m e. %s )' % (pe, NE)
    mni = s([s([], 'simpr', '( %s -> m e. %s )' % (pm, NE)), lift_from(w, pe, pm, L.nv(RR, L.rn))], 'eleqtrd', '( %s -> m e. %s )' % (pm, NCL(RR)))
    mm, mc = rab_elim(w, pm, NCL(RR), lambda t: COND(t, RR), 'm', mni)
    fl = s([s([mc], 'simpld', '( %s -> ( TMfl ` m ) = %s )' % (pm, FV(RR))), lift_from(w, pe, pm, f1)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
    ex_ = s([cnfl_at(w, pm, mm, fl, True)], 'ralrimiva', '( %s -> %s )' % (pe, LEXIT))
    ex0 = s([k, ex_], 'mpan2', '( %s -> %s )' % (PSI, LEXIT))
    w.qed([typ, ex0], 'jca', STMTS11[lab])
    return w.run(unify_only=UO)


def tmicpl():
    lab = 'tmicpl'
    w = W(lab, 'Lean\'s ` coprimeToF ` loop at the machine: ~ tm2floopu at the families ( ` N\' ` , ` P\' ` letters), '
               '` R = ( coprimeTo Q k ).2 ` iterations of ` cpBody ` (~ tmicpi ), the frame by ~ tmicpt .')
    s = w.s
    T = numtree11(PSI_T)
    ph = cj(T)
    B = Cp(w, ph, T)
    B.deep('cpt', 0)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmicpt', STMTS11['tmicpt']))
    ex[LTYP] = s([fr], 'simpld', '( %s -> %s )' % (ph, LTYP))
    ex[LEXIT] = s([fr], 'simprd', '( %s -> %s )' % (ph, LEXIT))
    per = s([s([], 'tmicpi', STMTS11['tmicpi'])], 'ralrimiva', '( %s -> %s )' % (PSI, LPER))
    ex[LPER] = lift_from(w, PSI, ph, per)
    ex['%s e. NN0' % RR] = B.rn
    cl = Closure(w, ph, {'N': ('NN0', B.nn)})
    cl.leaf(TBN, 'NN0', B.tbn)
    ex['%s e. NN0' % TPR] = cl.mem(TPR, 'NN0')
    st = Bld(w, ph, B.c, ex)(LTREE)
    st2 = s([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ph, LCONCL))
    finish(w, st2, lab)
    return w.run(unify_only=UO)


def expose2(w, ph, B, R, k, v2, veq, g2):
    """declare stack k of the current stacks as an outer update with the value v2 (veq : ( ph -> v = v2 ))"""
    Sc = R.S
    v = Sc.vals[k][0]
    xe = w.s([Sc.vals[k][1], veq], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, Sc.D, k, v2))
    u = upidv(w, ph, Sc.D, k, v2, xe, B.mk['tv'], Sc.memb, B.mk['k'][k]['kd'])
    ue = w.s([u], 'eqcomd', '( %s -> %s = %s )' % (ph, Sc.D, UP(Sc.D, k, v2)))
    head = R.cur[:-len(' X. { %s } ) )' % Sc.D)]
    lab = head.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
    ncls = head.split(' } X. ( ', 1)[1]
    e = clneq(w, ph, lab, ncls, ue, Sc.D, UP(Sc.D, k, v2))
    R.tri, _, R.cur, _ = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=e)
    old = list(R.chain)
    Sn = Stacks(w, ph, B.mk, Sc.D, Sc.memb, Sc.ne, dict(Sc.vals))
    Sn.vals[k] = (v2, xe, g2)
    R.S = Sn.upd(k, v2, g2)
    R.chain = old + [(k, v2)]
    R.gam[v2] = g2
    return Sn, old


def tmicpe():
    lab = 'tmicpe'
    T = numtree11(TREE_CPT)
    ph = cj(T)
    w = W(lab, 'The epilogue of Lean\'s ` coprimeToF ` at the machine: from the family of ` CpInv ` at ` R = ( coprimeTo Q k ).2 ` , '
               '` pushSym 6 comma ; pushBit 6 ( decide ( cmp =/= lt ) ) ` (~ tm2fpshn , ~ tm2fpshf ), ` moveEntries 3 4 5 ` '
               '(~ tm2lmes ) restores the list on 4, ` isZero 6 5 ` (~ tmiizs ) sets the flag to ` ( coprimeTo Q k ).1 ` and '
               '` dropNum 6 ` (~ tmidropnw ) restores 6, within ` R ( 2 b + 6 ) + 14 ` steps.')
    s = w.s
    B = Cp(w, ph, T)
    c, mk = B.c, B.mk
    B.deep('cpt', 1)
    cl = Closure(w, ph, {'N': ('NN0', B.nn)})
    cl.leaf(RR, 'NN0', B.rn)
    rz = B.tz(RR, B.rn, s([cl.mem(RR, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (ph, RR, RR)))
    NR_ = NCL(RR)
    SR = B.pbst(RR)
    chain0 = [('3', C3(RR)), ('4', C4(RR))]
    R = B.run()
    R.S, R.chain = SR, list(chain0)
    for _k, (_txt, _st, _g) in SR.vals.items():
        R.gam[_txt] = _g
    nss = B.ss(NR_)
    # 1. pushSym 6 comma
    V4 = '( <" 4 "> ++ ( D ` 6 ) )'
    g4 = B.g(V4, wg4(w, ph, DK(6), B.S0.vals['6'][2]))
    B.call(R, 'tm2fpshn', {'A': LMP['Z5'], 'E': LMP['Z6'], 'K': '6', 'Z': '4', 'N': NR_},
           {'4 e. %s' % GX('6'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['6']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('6'))),
            SSS(NR_): nss}, [('6', V4, g4)])
    # 2. pushBit 6 ( cmp =/= lt )
    BB = 'if ( %s = (/) , (/) , 1o )' % CV(RR)
    ZB = '<. 1 , %s >.' % BB
    bb2 = s([s([s([], '0el2o', '(/) e. 2o'), s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % BB)], 'a1i', '( %s -> %s e. 2o )' % (ph, BB))
    zg = s([bb2, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, ZB))
    X_of = lambda t: '<. 1 , if ( ( TMcmp ` %s ) = (/) , (/) , 1o ) >.' % t
    assert P_NLT == '( u e. TMSt |-> %s )' % X_of('u')
    bu = s([s([s([], '0el2o', '(/) e. 2o'), s([], '1oel2o', '1o e. 2o')], 'ifcli', 'if ( ( TMcmp ` u ) = (/) , (/) , 1o ) e. 2o'), w.inst('bitgamma')],
           'ax-mp', "%s e. Gamma'" % X_of('u'))
    pty = lamty(w, ph, mk, P_NLT, X_of, GAM, s([], 'gammaex', "Gamma' e. _V"), bu)
    pty6 = s([pty, s([mk['k']['6']['ge']], 'oveq1d', "( %s -> ( %s ^m %s ) = ( Gamma' ^m %s ) )" % (ph, GX('6'), S, S))], 'eleqtrrd',
             '( %s -> %s e. ( %s ^m %s ) )' % (ph, P_NLT, GX('6'), S))
    pr_ = '( %s /\\ r e. %s )' % (ph, NR_)
    rr, rc = rab_elim(w, pr_, NR_, lambda t: COND(t, RR), 'r', s([], 'simpr', '( %s -> r e. %s )' % (pr_, NR_)))
    cmr = s([rc], 'simprd', '( %s -> ( TMcmp ` r ) = %s )' % (pr_, CV(RR)))
    pv_ = lamval(w, pr_, X_of, 'r', rr, closed(w, pr_, 'opex', '%s e. _V' % X_of('r')))
    rw_, xz = w.rewrite(X_of('r'), {'( TMcmp ` r )': (CV(RR), cmr)}, pr_)
    assert xz == ZB, xz
    pz = s([s([pv_, rw_], 'eqtrd', '( %s -> ( %s ` r ) = %s )' % (pr_, P_NLT, ZB))], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) = %s )' % (ph, NR_, P_NLT, ZB))
    V1 = '( <" %s "> ++ %s )' % (ZB, V4)
    g1 = B.g(V1, wgcat(w, ph, '<" %s ">' % ZB, V4, s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, ZB)), g4))
    B.call(R, 'tm2fpshf', {'A': LMP['Z6'], 'E': LMP['Z7'], 'K': '6', 'P': P_NLT, 'Z': ZB, 'N': NR_},
           {'%s e. %s' % (ZB, GX('6')): s([zg, mk['k']['6']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, ZB, GX('6'))),
            PTY(P_NLT, '6'): pty6, 'A. r e. %s ( %s ` r ) = %s' % (NR_, P_NLT, ZB): pz, SSS(NR_): nss}, [('6', V1, g1)])
    # 3. moveEntries 3 4 5 (~ tm2lmes at the concrete handlers)
    RPR = RP(RR)
    LL = '( encNatGam o. %s )' % RPR
    pw = s([B.ww, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PFX(RR)))
    rpw = s([pw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RPR))
    llw = s([rpw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LL, BITS))
    k3 = s([R.S.vals['3'][1], s([s([rpw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, RPR, LL))], 'oveq1d',
                                '( %s -> %s = ( ( encListB ` %s ) ++ ( D ` 3 ) ) )' % (ph, C3(RR), LL))], 'eqtrd',
           '( %s -> ( %s ` 3 ) = ( ( encListB ` %s ) ++ ( D ` 3 ) ) )' % (ph, R.S.D, LL))
    rs1 = s([pw, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (ph, RPR, PFX(RR)))
    SW0 = '( W substr <. 0 , %s >. )' % RR
    rs2a = s([s([B.ww, B.rn, w.inst('pfxval')], 'syl2anc', '( %s -> %s = %s )' % (ph, PFX(RR), SW0))], 'rneqd', '( %s -> ran %s = ran %s )' % (ph, PFX(RR), SW0))
    rs2b = s([B.ww, s([B.rn, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, RR)), rz, w.inst('swrdrn3')], 'syl3anc',
             '( %s -> ran %s = ( W " ( 0 ..^ %s ) ) )' % (ph, SW0, RR))
    rs2 = s([rs2a, rs2b], 'eqtrd', '( %s -> ran %s = ( W " ( 0 ..^ %s ) ) )' % (ph, PFX(RR), RR))
    rs3 = s([rs2, s([s([], 'imassrn', '( W " ( 0 ..^ %s ) ) C_ ran W' % RR)], 'a1i', '( %s -> ( W " ( 0 ..^ %s ) ) C_ ran W )' % (ph, RR))], 'eqsstrd',
            '( %s -> ran %s C_ ran W )' % (ph, PFX(RR)))
    rs4 = s([rs1, rs3], 'sstrd', '( %s -> ran %s C_ ran W )' % (ph, RPR))
    ral = s([rs4, c[RALB('W', 'N')], w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ph, RALB(RPR, 'N')))
    lrb = s([rpw, B.nn, ral, w.inst('tm2lrnenc')], 'syl3anc', '( %s -> A. w e. ran %s ( # ` w ) <_ N )' % (ph, LL))
    MEL = FRAGS['me'].lmap(PL('P', FRAGS['cpt'].slot(1)), LMP['Z9'])
    m = dict(H.hm('tm2lmes'))
    m.update({'P1': LMP['Z7'], 'A': LMP['Z8'], 'A"': LMP['Z9'], "E'": LMP['Z10'], 'E': LMP['Y3'], "A'": MEL['A'], "B'": MEL["A'"],
              'B"': MEL['A"'], "Q'": MEL["E'"], 'K': '3', 'J': '4', 'I': '5', 'L': LL, 'R': DK(3), 'B': 'N'})
    RLL = '( reverse ` %s )' % LL
    ENT = '( ( entries ` %s ) ++ %s )' % (RLL, C4(RR))
    rlw = s([llw, w.inst('revcl')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, RLL, BITS))
    gE = B.g(ENT, wgcat(w, ph, '( entries ` %s )' % RLL, C4(RR), s([rlw, w.inst('tm2lentcl')], 'syl', "( %s -> ( entries ` %s ) e. Word Gamma' )" % (ph, RLL)),
                        B.gam[C4(RR)]))
    B.call(R, 'tm2lmes', m, {'( %s ` 3 ) = ( ( encListB ` %s ) ++ ( D ` 3 ) )' % (R.S.D, LL): k3, '%s e. Word Word %s' % (LL, BITS): llw,
                             'N e. NN0': B.nn, 'A. w e. ran %s ( # ` w ) <_ N' % LL: lrb},
           [('3', DK(3), B.S0.vals['3'][2]), ('4', ENT, gE)], pre=(NR_, nss))
    # 4. isZero 6 5 on the one-bit word
    LB = '<" %s ">' % BB
    IW = '( inclBool o. %s )' % LB
    lbw = s([bb2, w.inst('s1cl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, LB))
    ico = s([bb2, closed(w, ph, 'inclboolf', "inclBool : 2o --> Gamma'"), w.inst('s1co')], 'syl2anc', '( %s -> %s = <" ( inclBool ` %s ) "> )' % (ph, IW, BB))
    ifv = s([bb2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` %s ) = %s )' % (ph, BB, ZB))
    iw1 = s([ico, s([ifv], 's1eqd', '( %s -> <" ( inclBool ` %s ) "> = <" %s "> )' % (ph, BB, ZB))], 'eqtrd', '( %s -> %s = <" %s "> )' % (ph, IW, ZB))
    V1b = '( %s ++ %s )' % (IW, V4)
    vq = s([s([iw1], 'oveq1d', '( %s -> %s = %s )' % (ph, V1b, V1))], 'eqcomd', '( %s -> %s = %s )' % (ph, V1, V1b))
    k6 = s([R.S.vals['6'][1], vq], 'eqtrd', '( %s -> ( %s ` 6 ) = %s )' % (ph, R.S.D, V1b))
    IFL = 'if ( ( toNat ` %s ) = 0 , 1o , (/) )' % LB
    B.call(R, 'tmiizs', {'K': '6', 'I': '5', 'L': LB, 'X': DK(6), 'P': PL('P', FRAGS['cpt'].slot(2)), 'E': LMP['Y4']},
           {'%s e. Word 2o' % LB: lbw, '( %s ` 6 ) = %s' % (R.S.D, V1b): k6}, [])
    # 5. dropNum 6
    iwb = s([lbw, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IW, BITS))
    g1b = B.g(V1b, wgcat(w, ph, IW, V4, s([lbw, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IW)), g4))
    Son, old = expose2(w, ph, B, R, '6', V1b, vq, g1b)
    B.call(R, 'tmidropnw', {'K': '6', 'W': IW, 'X': DK(6), 'O': IFL, 'P': PL('P', FRAGS['cpt'].slot(3)), 'E': 'E'},
           {'%s e. Word %s' % (IW, BITS): iwb}, [('6', DK(6), B.S0.vals['6'][2])], on=(Son, old))
    cur, out = R.normalize(N8)
    assert out == [('4', ENT)], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    # the stacks: ENT = ( encList ` W ) ++ X
    EP = '( encNatGam o. %s )' % PFX(RR)
    ED = '( encNatGam o. %s )' % DRP(RR)
    EGW = '( encNatGam o. W )'
    EF = closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS)
    dw = s([B.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DRP(RR)))
    rc_ = s([rpw, EF, w.inst('revco')], 'syl2anc', '( %s -> ( encNatGam o. ( reverse ` %s ) ) = %s )' % (ph, RPR, RLL))
    rr2 = s([pw, w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = %s )' % (ph, RPR, PFX(RR)))
    rv = s([rc_, s([rr2], 'coeq2d', '( %s -> ( encNatGam o. ( reverse ` %s ) ) = %s )' % (ph, RPR, EP))], 'eqtr3d', '( %s -> %s = %s )' % (ph, RLL, EP))
    Z2 = '( <" 2 "> ++ X )'
    epw = s([pw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, EP, BITS))
    edw = s([dw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, ED, BITS))
    egw = s([B.ww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, EGW, BITS))
    e1 = s([s([rv], 'fveq2d', '( %s -> ( entries ` %s ) = ( entries ` %s ) )' % (ph, RLL, EP))], 'oveq1d',
           '( %s -> %s = ( ( entries ` %s ) ++ %s ) )' % (ph, ENT, EP, C4(RR)))
    e2 = s([s([s([dw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, DRP(RR), ED))], 'oveq1d',
              '( %s -> %s = ( ( encListB ` %s ) ++ X ) )' % (ph, C4(RR), ED)),
            s([edw, B.xw, w.inst('tm2lencbcc')], 'syl2anc', '( %s -> ( ( encListB ` %s ) ++ X ) = ( ( entries ` %s ) ++ %s ) )' % (ph, ED, ED, Z2))],
           'eqtrd', '( %s -> %s = ( ( entries ` %s ) ++ %s ) )' % (ph, C4(RR), ED, Z2))
    X3 = '( ( entries ` %s ) ++ ( ( entries ` %s ) ++ %s ) )' % (EP, ED, Z2)
    e3 = s([e1, s([e2], 'oveq2d', '( %s -> ( ( entries ` %s ) ++ %s ) = %s )' % (ph, EP, C4(RR), X3))], 'eqtrd', '( %s -> %s = %s )' % (ph, ENT, X3))
    enp = s([epw, w.inst('tm2lentcl')], 'syl', "( %s -> ( entries ` %s ) e. Word Gamma' )" % (ph, EP))
    end_ = s([edw, w.inst('tm2lentcl')], 'syl', "( %s -> ( entries ` %s ) e. Word Gamma' )" % (ph, ED))
    s2 = s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
    z2g = wgcat(w, ph, '<" 2 ">', 'X', s2, B.xw)
    X4 = '( ( ( entries ` %s ) ++ ( entries ` %s ) ) ++ %s )' % (EP, ED, Z2)
    e4 = s([enp, end_, z2g, w.inst('ccatass')], 'syl3anc', '( %s -> %s = %s )' % (ph, X4, X3))
    e5 = s([epw, edw, w.inst('tm2lentcc')], 'syl2anc', '( %s -> ( entries ` ( %s ++ %s ) ) = ( ( entries ` %s ) ++ ( entries ` %s ) ) )' % (ph, EP, ED, EP, ED))
    cco = s([pw, dw, EF, w.inst('ccatco')], 'syl3anc', '( %s -> ( encNatGam o. ( %s ++ %s ) ) = ( %s ++ %s ) )' % (ph, PFX(RR), DRP(RR), EP, ED))
    pcw = s([B.ww, rz, w.inst('pfxcctswrd')], 'syl2anc', '( %s -> ( %s ++ %s ) = W )' % (ph, PFX(RR), DRP(RR)))
    e6 = s([cco, s([pcw], 'coeq2d', '( %s -> ( encNatGam o. ( %s ++ %s ) ) = %s )' % (ph, PFX(RR), DRP(RR), EGW))], 'eqtr3d',
           '( %s -> ( %s ++ %s ) = %s )' % (ph, EP, ED, EGW))
    e7 = s([s([e6], 'fveq2d', '( %s -> ( entries ` ( %s ++ %s ) ) = ( entries ` %s ) )' % (ph, EP, ED, EGW)), e5], 'eqtr3d',
           '( %s -> ( entries ` %s ) = ( ( entries ` %s ) ++ ( entries ` %s ) ) )' % (ph, EGW, EP, ED))
    X8 = '( ( entries ` %s ) ++ %s )' % (EGW, Z2)
    e8 = s([s([s([B.ww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` W ) = ( encListB ` %s ) )' % (ph, EGW))], 'oveq1d',
              '( %s -> %s = ( ( encListB ` %s ) ++ X ) )' % (ph, ENCL('W', 'X'), EGW)),
            s([egw, B.xw, w.inst('tm2lencbcc')], 'syl2anc', '( %s -> ( ( encListB ` %s ) ++ X ) = %s )' % (ph, EGW, X8))],
           'eqtrd', '( %s -> %s = %s )' % (ph, ENCL('W', 'X'), X8))
    e9 = s([s([e7], 'oveq1d', '( %s -> %s = %s )' % (ph, X8, X4)), e4], 'eqtrd', '( %s -> %s = %s )' % (ph, X8, X3))
    ent = s([e3, s([e8, e9], 'eqtrd', '( %s -> %s = %s )' % (ph, ENCL('W', 'X'), X3))], 'eqtr4d', '( %s -> %s = %s )' % (ph, ENT, ENCL('W', 'X')))
    Dst = triple_D(D)
    assert Dst == UP('D', '4', ENT), Dst
    u4 = upidv(w, ph, 'D', '4', ENCL('W', 'X'), B.S0.vals['4'][1], mk['tv'], B.dd, mk['k']['4']['kd'])
    r4, x4 = w.rewrite(Dst, {ENT: (ENCL('W', 'X'), ent)}, ph)
    deq = s([r4, u4], 'eqtrd', '( %s -> %s = D )' % (ph, Dst))
    # the flag: if ( toNat <" BB "> = 0 , 1o , (/) ) = ( coprimeTo Q k ).1
    tn_ = s([bb2, w.inst('tonats1')], 'syl', '( %s -> ( toNat ` %s ) = ( bToNat ` %s ) )' % (ph, LB, BB))
    t0 = s([s([tn_], 'eqeq1d', '( %s -> ( ( toNat ` %s ) = 0 <-> ( bToNat ` %s ) = 0 ) )' % (ph, LB, BB)),
            s([bb2, w.inst('bwbneq0')], 'syl', '( %s -> ( ( bToNat ` %s ) = 0 <-> %s = (/) ) )' % (ph, BB, BB))], 'bitrd',
           '( %s -> ( ( toNat ` %s ) = 0 <-> %s = (/) ) )' % (ph, LB, BB))
    IB = 'if ( %s = (/) , 1o , (/) )' % BB
    i1 = ifeq_bi(w, ph, '( toNat ` %s ) = 0' % LB, '%s = (/)' % BB, t0)
    n10 = s([s([], '1n0', '1o =/= (/)')], 'neii', '-. 1o = (/)')
    def neq0(pp, A, st):
        """( pp -> -. A = (/) ) from st : ( pp -> A = 1o )"""
        return s([s([st], 'eqeq1d', '( %s -> ( %s = (/) <-> 1o = (/) ) )' % (pp, A)), s([n10], 'a1i', '( %s -> -. 1o = (/) )' % pp)], 'mtbird',
                 '( %s -> -. %s = (/) )' % (pp, A))
    CVR = CV(RR)
    pa = '( %s /\\ %s = (/) )' % (ph, CC)
    ca = s([s([], 'simpr', '( %s -> %s = (/) )' % (pa, CC))], 'eqcomd', '( %s -> (/) = %s )' % (pa, CC))
    cva = s([s([s([], 'eqidd', '( %s -> %s = %s )' % (pa, RR, RR)), s([], 'simpr', '( %s -> %s = (/) )' % (pa, CC))], 'jca',
               '( %s -> ( %s = %s /\\ %s = (/) ) )' % (pa, RR, RR, CC))], 'iftrued', '( %s -> %s = 1o )' % (pa, CVR))
    bba = s([neq0(pa, CVR, cva)], 'iffalsed', '( %s -> %s = 1o )' % (pa, BB))
    ia = s([s([neq0(pa, BB, bba)], 'iffalsed', '( %s -> %s = (/) )' % (pa, IB)), ca], 'eqtrd', '( %s -> %s = %s )' % (pa, IB, CC))
    pb = '( %s /\\ %s = 1o )' % (ph, CC)
    cb = s([s([], 'simpr', '( %s -> %s = 1o )' % (pb, CC))], 'eqcomd', '( %s -> 1o = %s )' % (pb, CC))
    ncz = neq0(pb, CC, s([], 'simpr', '( %s -> %s = 1o )' % (pb, CC)))
    cvb = s([s([ncz], 'intnand', '( %s -> -. ( %s = %s /\\ %s = (/) ) )' % (pb, RR, RR, CC))], 'iffalsed', '( %s -> %s = (/) )' % (pb, CVR))
    bbb = s([cvb], 'iftrued', '( %s -> %s = (/) )' % (pb, BB))
    ib = s([s([bbb], 'iftrued', '( %s -> %s = 1o )' % (pb, IB)), cb], 'eqtrd', '( %s -> %s = %s )' % (pb, IB, CC))
    orc = s([s([B.c2, s([], 'df2o3', '2o = { (/) , 1o }')], 'eleqtrdi', '( %s -> %s e. { (/) , 1o } )' % (ph, CC)), w.inst('elpri')], 'syl',
            '( %s -> ( %s = (/) \\/ %s = 1o ) )' % (ph, CC, CC))
    ibc = s([ia, ib, orc], 'mpjaodan', '( %s -> %s = %s )' % (ph, IB, CC))
    ifc = s([i1, ibc], 'eqtrd', '( %s -> %s = %s )' % (ph, IFL, CC))
    ceq = s([clnneq(w, ph, 'E', nfl_eq(w, ph, IFL, CC, ifc), NFL(IFL), NFL(CC), Dst), clneq(w, ph, 'E', NFL(CC), deq, Dst, 'D')], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D, CLN('E', NFL(CC), 'D')))
    # the pre: chain0 = PB( RR )
    assert C == CLN(LMP['Z5'], NR_, chain_text('D', chain0)), C
    assert chain_text('D', chain0) == PB(RR)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=ceq)
    # the bound
    lnl = s([s([s([rpw, EF, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, LL, RPR)),
                s([pw, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, RPR, PFX(RR)))], 'eqtrd',
               '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, LL, PFX(RR))), s([B.ww, rz, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, PFX(RR), RR))],
            'eqtrd', '( %s -> ( # ` %s ) = %s )' % (ph, LL, RR))
    l1 = closed(w, ph, 's1len', '( # ` %s ) = 1' % LB)
    l2 = s([s([lbw, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, IW, LB)), l1], 'eqtrd', '( %s -> ( # ` %s ) = 1 )' % (ph, IW))
    rn, n2 = w.rewrite(n, {'( # ` %s )' % LL: (RR, lnl), '( # ` %s )' % LB: ('1', l1), '( # ` %s )' % IW: ('1', l2)}, ph)
    le2 = linarith(w, ph, [], '%s <_ %s' % (n2, UE), closure=cl, products=True)
    le = s([s([rn], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, UE, n2, UE)), le2], 'mpbird', '( %s -> %s <_ %s )' % (ph, n, UE))
    t = hrle(w, ph, mk['phm'], t, C, D, n, UE, cl.mem(UE, 'NN0'), le)
    finish(w, t, lab)
    return w.run(unify_only=UO)


def tmicptb():
    lab = 'tmicptb'
    T = numtree11(TREE_CPT)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` coprimeToF_le_B ` at the machine ( ` x y z s t u = 4 2 3 5 6 7 ` ): with the list ` Q ` of numbers in '
               '` [ 1 , 2 ^ b ) ` on 4 and ` k < 2 ^ b ` on 2, the machine ends with ` flag = ( coprimeTo Q k ).1 ` and every stack '
               'restored, within ` ( ( coprimeTo Q k ).2 + 1 ) B ( 2 b + 2 ) ` steps: ` pushSym 3 bra ; load\' ( cmp := lt ) ; '
               'peekBra 4 ` (~ tm2fpshn , ~ tm2flg , ~ tm2lpk ), the loop (~ tmicpl ), the epilogue (~ tmicpe ).')
    s = w.s
    B = Cp(w, ph, T)
    c, mk = B.c, B.mk
    R = B.run()
    # 1. pushSym 3 bra
    V2 = '( <" 2 "> ++ ( D ` 3 ) )'
    s2 = s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph)
    g2 = B.g(V2, wgcat(w, ph, '<" 2 ">', DK(3), s2, B.S0.vals['3'][2]))
    B.call(R, 'tm2fpshn', {'A': LMP['Z1'], 'E': LMP['Z2'], 'K': '3', 'Z': '2', 'N': S},
           {'2 e. %s' % GX('3'): s([closed(w, ph, 'gamma2', "2 e. Gamma'"), mk['k']['3']['ge']], 'eleqtrrd', '( %s -> 2 e. %s )' % (ph, GX('3')))},
           [('3', V2, g2)])
    # 2. load' ( cmp := lt )
    CM0 = '{ h e. TMSt | ( TMcmp ` h ) = (/) }'
    kw = lambda t: dict(cmp='(/)')
    pr_ = '( %s /\\ r e. %s )' % (ph, S)
    rr = s([s([], 'simpr', '( %s -> r e. %s )' % (pr_, S)), lift_from(w, ph, pr_, mk['seq'])], 'eleqtrd', '( %s -> r e. TMSt )' % pr_)
    nv = lset_val3(w, pr_, kw, 'r', rr)
    NR = '( %s ` r )' % L_CLT
    inm = rab_in(w, pr_, CM0, lambda t: '( TMcmp ` %s ) = (/)' % t, NR, nv['mem'], nv['fields']['cmp'])
    hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, S, L_CLT, CM0))
    B.call(R, 'tm2flg', {'A': LMP['Z2'], 'E': LMP['Z3'], 'F': L_CLT, 'N': S, "N'": CM0},
           {LTY(L_CLT): lset_ty3(w, ph, mk, L_CLT, kw), SSS(CM0): B.ss(CM0), 'A. r e. %s ( %s ` r ) e. %s' % (S, L_CLT, CM0): hl}, [])
    # 3. peekBra 4 into the family at 0
    W_ = ENCL('W', 'X')
    vn0 = encl_ne0(w, ph, 'W', B.ww, 'X', B.xw)
    eq, hg, tg = A8.word_split(w, ph, W_, B.gam[W_], vn0)
    HD, TL = A8.HD0(W_), A8.TL1(W_)
    kv = s([R.S.vals['4'][1], eq], 'eqtrd', '( %s -> ( %s ` 4 ) = ( <" %s "> ++ %s ) )' % (ph, R.S.D, HD, TL))
    hb0 = s([B.ww, B.xw, w.inst('tmexhdb')], 'syl2anc', '( %s -> ( %s = 2 <-> W = (/) ) )' % (ph, HD))
    tp0 = s([B.ww, B.gn, w.inst('tmcp0')], 'syl2anc', '( %s -> ( %s = 0 <-> W = (/) ) )' % (ph, RR))
    ecm = s([s([], 'eqcom', '( %s = 0 <-> 0 = %s )' % (RR, RR))], 'a1i', '( %s -> ( %s = 0 <-> 0 = %s ) )' % (ph, RR, RR))
    tq = s([ecm, tp0], 'bitr3d', '( %s -> ( 0 = %s <-> W = (/) ) )' % (ph, RR))
    bi0 = s([hb0, tq], 'bitr4d', '( %s -> ( %s = 2 <-> 0 = %s ) )' % (ph, HD, RR))
    # ( 0 = R /\ c = (/) ) fails: R = 0 forces Q = [] and c = true
    pz = '( %s /\\ 0 = %s )' % (ph, RR)
    wz = s([s([], 'simpr', '( %s -> 0 = %s )' % (pz, RR)), lift_from(w, ph, pz, tq)], 'mpbid', '( %s -> W = (/) )' % pz)
    c0v = s([s([s([wz], 'oveq1d', '( %s -> %s = ( (/) CoprimeTo G ) )' % (pz, CP)), s([lift_from(w, ph, pz, B.gn), w.inst('coprimeto0')], 'syl',
                                                                                     '( %s -> ( (/) CoprimeTo G ) = <. 1o , 0 >. )' % pz)],
               'eqtrd', '( %s -> %s = <. 1o , 0 >. )' % (pz, CP))], 'fveq2d', '( %s -> %s = ( 1st ` <. 1o , 0 >. ) )' % (pz, CC))
    o1 = s([s([], '1oex', '1o e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. 1o , 0 >. ) = 1o')
    cz1 = s([c0v, s([o1], 'a1i', '( %s -> ( 1st ` <. 1o , 0 >. ) = 1o )' % pz)], 'eqtrd', '( %s -> %s = 1o )' % (pz, CC))
    n10 = s([s([], '1n0', '1o =/= (/)')], 'neii', '-. 1o = (/)')
    ncz = s([s([cz1], 'eqeq1d', '( %s -> ( %s = (/) <-> 1o = (/) ) )' % (pz, CC)), s([n10], 'a1i', '( %s -> -. 1o = (/) )' % pz)], 'mtbird',
            '( %s -> -. %s = (/) )' % (pz, CC))
    nand = s([s([ncz], 'ex', '( %s -> ( 0 = %s -> -. %s = (/) ) )' % (ph, RR, CC)),
              s([], 'imnan', '( ( 0 = %s -> -. %s = (/) ) <-> -. ( 0 = %s /\\ %s = (/) ) )' % (RR, CC, RR, CC))], 'sylib',
             '( %s -> -. ( 0 = %s /\\ %s = (/) ) )' % (ph, RR, CC))
    cv0 = s([nand], 'iffalsed', '( %s -> %s = (/) )' % (ph, CV('0')))
    pq = '( %s /\\ r e. %s )' % (ph, CM0)
    Lq = lambda st: lift_from(w, ph, pq, st)
    rq, cq = rab_elim(w, pq, CM0, lambda t: '( TMcmp ` %s ) = (/)' % t, 'r', s([], 'simpr', '( %s -> r e. %s )' % (pq, CM0)))
    NB_ = '( TMrdBra ` <. r , ( inl ` %s ) >. )' % HD
    VB = 'if ( %s = 2 , 1o , (/) )' % HD
    mb = s([rq, Lq(hg), w.inst('tmcrdbrac')], 'syl2anc', '( %s -> %s e. %s )' % (pq, NB_, NFL(VB)))
    nbm, nbf = A8.nfl_unpack(w, pq, VB, NB_, mb)
    fb = s([nbf, Lq(ifeq_bi(w, ph, '%s = 2' % HD, '0 = %s' % RR, bi0))], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (pq, NB_, FV('0')))
    ihd = s([Lq(hg), w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (pq, HD, OPT))
    IFO = 'if ( ( inl ` %s ) = ( inl ` 2 ) , 1o , (/) )' % HD
    comps = [FLD(f, 'r') for f in ORDER[:6]] + [IFO]
    val = s([rq, ihd, w.inst('tmcrdbrav')], 'syl2anc', '( %s -> %s = %s )' % (pq, NB_, MK(*comps)))
    stc = st_comps(w, pq, 'r', rq)
    ic = s([s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFO)], 'a1i', '( %s -> %s e. 2o )' % (pq, IFO))
    mem_, vals_ = tuple_facts(w, pq, comps, [stc[f] for f in ORDER[:6]] + [ic])
    cmv = s([s([val], 'fveq2d', '( %s -> ( TMcmp ` %s ) = ( TMcmp ` %s ) )' % (pq, NB_, MK(*comps))), vals_['cmp']], 'eqtrd',
            '( %s -> ( TMcmp ` %s ) = ( TMcmp ` r ) )' % (pq, NB_))
    cm0 = s([s([cmv, cq], 'eqtrd', '( %s -> ( TMcmp ` %s ) = (/) )' % (pq, NB_)), Lq(cv0)], 'eqtr4d', '( %s -> ( TMcmp ` %s ) = %s )' % (pq, NB_, CV('0')))
    N0c = NCL('0')
    in0 = rab_in(w, pq, N0c, lambda t: COND(t, '0'), NB_, nbm, s([fb, cm0], 'jca', '( %s -> %s )' % (pq, COND(NB_, '0'))))
    pk = s([in0], 'ralrimiva', '( %s -> A. r e. %s %s e. %s )' % (ph, CM0, NB_, N0c))
    B.call(R, 'tm2lpk', {'A': LMP['Z3'], 'E': LMP['Z4'], 'K': '4', 'F': RDBRA, 'Z': HD, 'X': TL, 'N': CM0, "N'": N0c},
           {'( %s ` 4 ) = ( <" %s "> ++ %s )' % (R.S.D, HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
            'A. r e. %s ( TMrdBra ` <. r , ( inl ` %s ) >. ) e. %s' % (CM0, HD, N0c): pk, SSS(CM0): B.ss(CM0), SSS(N0c): B.ss(N0c)}, [])
    t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
    D1s = triple_D(D1)
    assert D1s == UP('D', '3', V2), D1s
    # the family at 0
    z0 = closed(w, ph, '0nn0', '0 e. NN0')
    PB0 = PB('0')
    pbx = s([B.pbst('0').memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB0))
    pfv = mval(w, ph, 'j', 'NN0', PB, '0', z0, pbx)
    rp0 = s([s([s([], 'pfx00', '%s = (/)' % PFX('0'))], 'fveq2i', '%s = ( reverse ` (/) )' % RP('0')), s([], 'rev0', '( reverse ` (/) ) = (/)')], 'eqtri',
            '%s = (/)' % RP('0'))
    el0 = s([s([rp0], 'fveq2i', '( encList ` %s ) = ( encList ` (/) )' % RP('0')), s([], 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'eqtri',
            '( encList ` %s ) = <" 2 ">' % RP('0'))
    c30 = s([s([el0], 'oveq1i', '%s = %s' % (C3('0'), V2))], 'a1i', '( %s -> %s = %s )' % (ph, C3('0'), V2))
    pv_ = s([B.ww, B.nwn, w.inst('pfxval')], 'syl2anc', '( %s -> ( W prefix %s ) = %s )' % (ph, NW, DRP('0')))
    w0 = s([pv_, s([B.ww, w.inst('pfxid')], 'syl', '( %s -> ( W prefix %s ) = W )' % (ph, NW))], 'eqtr3d', '( %s -> %s = W )' % (ph, DRP('0')))
    rs, xs = w.rewrite(PB0, {C3('0'): (V2, c30), DRP('0'): ('W', w0)}, ph)
    assert xs == UP(UP('D', '3', V2), '4', W_), xs
    u4 = upidv(w, ph, R.S.D, '4', W_, R.S.vals['4'][1], mk['tv'], R.S.memb, mk['k']['4']['kd'])
    PF0 = '( %s ` 0 )' % PF
    se = s([s([s([pfv, rs], 'eqtrd', '( %s -> %s = %s )' % (ph, PF0, xs)), u4], 'eqtrd', '( %s -> %s = %s )' % (ph, PF0, D1s))], 'eqcomd',
           '( %s -> %s = %s )' % (ph, D1s, PF0))
    NF0 = '( %s ` 0 )' % NFM
    ceq0 = s([famval(w, ph, COND, '0', z0)], 'eqcomd', '( %s -> %s = %s )' % (ph, N0c, NF0))
    lab0 = LMP['Z4']
    ceq = s([clnneq(w, ph, lab0, ceq0, N0c, NF0, D1s), clneq(w, ph, lab0, NF0, se, D1s, PF0)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D1, CLN(lab0, NF0, PF0)))
    t1, C1, D1, n1 = hrrw(w, ph, t1, C1, D1, n1, deq=ceq)
    # 4. the loop at N' := NFM , P' := PF
    ex = {'%s = %s' % (PF, PF): s([s([], 'eqid', '%s = %s' % (PF, PF))], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF)),
          '%s = %s' % (NFM, NFM): s([s([], 'eqid', '%s = %s' % (NFM, NFM))], 'a1i', '( %s -> %s = %s )' % (ph, NFM, NFM))}
    tl, cl_ = inst(w, ph, 'tmicpl', {NV: NFM, PV: PF}, Bld(w, ph, c, ex))
    C2, D2, n2 = triple_parts(cl_)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, mk['phm'], t1, tl, C1, D1, D2, n1, n2)
    n12 = '( %s + %s )' % (n1, n2)
    # 5. the epilogue from the family at R
    SRr = B.pbst(RR)
    pbr = s([SRr.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB(RR)))
    pfr = mval(w, ph, 'j', 'NN0', PB, RR, B.rn, pbr)
    PFR = '( %s ` %s )' % (PF, RR)
    NFR = '( %s ` %s )' % (NFM, RR)
    labE = LMP['Z5']
    ceqR = s([clnneq(w, ph, labE, famval(w, ph, COND, RR, B.rn), NFR, NCL(RR), PFR), clneq(w, ph, labE, NCL(RR), pfr, PFR, PB(RR))], 'eqtrd',
             '( %s -> %s = %s )' % (ph, D2, CLN(labE, NCL(RR), PB(RR))))
    t12, C12, D12, n12 = hrrw(w, ph, t12, C1, D2, n12, deq=ceqR)
    te = lift_from(w, cj(TREE_CPT), ph, s([], 'tmicpe', STMTS11['tmicpe']))
    C3_, D3_, n3 = triple_parts(CONCL_E)
    assert C3_ == D12, (C3_, D12)
    t = hrseq(w, ph, mk['phm'], t12, te, C1, D12, D3_, n12, n3)
    nT = '( %s + %s )' % (n12, n3)
    # 6. the bound
    cl = Closure(w, ph, {'N': ('NN0', B.nn)})
    cl.leaf(RR, 'NN0', B.rn)
    cl.leaf(TBN, 'NN0', B.tbn)
    M2 = '( ( 2 x. N ) + 2 )'
    TM2 = '( TMB ` %s )' % M2
    BND = '( ( %s + 1 ) x. %s )' % (RR, TM2)
    sc = s([closed(w, ph, '1nn0', '1 e. NN0'), B.nn, w.inst('tplbscale')], 'syl2anc',
           '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( TMB ` ( ( ( 1 + 1 ) x. N ) + ( 2 x. 1 ) ) ) )' % (ph, TBN))
    ae = lineq(w, ph, '( ( ( 1 + 1 ) x. N ) + ( 2 x. 1 ) )', M2, closure=cl, products=True)
    e8 = s([s([s([], '1p1e2', '( 1 + 1 ) = 2')], 'oveq1i', '( ( 1 + 1 ) ^ 3 ) = ( 2 ^ 3 )'), s([], 'cu2', '( 2 ^ 3 ) = 8')], 'eqtri', '( ( 1 + 1 ) ^ 3 ) = 8')
    ta = s([s([s([e8], 'oveq1i', '( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( 8 x. %s )' % (TBN, TBN))], 'a1i',
              '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( 8 x. %s ) )' % (ph, TBN, TBN)),
            s([sc, s([ae], 'fveq2d', '( %s -> ( TMB ` ( ( ( 1 + 1 ) x. N ) + ( 2 x. 1 ) ) ) = %s )' % (ph, TM2))], 'eqtrd',
              '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = %s )' % (ph, TBN, TM2))], 'eqtr3d', '( %s -> ( 8 x. %s ) = %s )' % (ph, TBN, TM2))
    RHS = '( ( %s + 1 ) x. ( 8 x. %s ) )' % (RR, TBN)
    rr_ = s([s([ta], 'eqcomd', '( %s -> %s = ( 8 x. %s ) )' % (ph, TM2, TBN))], 'oveq2d', '( %s -> %s = %s )' % (ph, BND, RHS))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([B.nn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc', '( %s -> ( 4 x. ( ( N + 2 ) ^ 2 ) ) <_ %s )' % (ph, TBN))
    h1 = nlinarith(w, ph, [qd, cl.ge0('N')], '( ( 2 x. N ) + 9 ) <_ ( 2 x. %s )' % TBN, closure=cl, atoms=['N', TBN])
    h2 = s([cl.mem('( ( 2 x. N ) + 9 )', 'RR'), cl.mem('( 2 x. %s )' % TBN, 'RR'), cl.mem(RR, 'RR'), cl.ge0(RR), h1], 'lemul2ad',
           '( %s -> ( %s x. ( ( 2 x. N ) + 9 ) ) <_ ( %s x. ( 2 x. %s ) ) )' % (ph, RR, RR, TBN))
    le2 = linarith(w, ph, [h1, h2, cl.ge0('N')], '%s <_ %s' % (nT, RHS), closure=cl, atoms=[RR, 'N', TBN], products=True)
    le = s([s([rr_], 'breq2d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, nT, BND, nT, RHS)), le2], 'mpbird', '( %s -> %s <_ %s )' % (ph, nT, BND))
    cl.leaf(TM2, 'NN0', s([s([cl.mem(M2, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TM2))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TM2)))
    st = hrle(w, ph, mk['phm'], t, C1, D3_, nT, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run(unify_only=UO)


if __name__ == '__main__':
    for l in SEL:
        if l != 'show':
            globals()[l]()
