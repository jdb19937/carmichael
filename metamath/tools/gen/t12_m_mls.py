"""T12: memList at ` 5 1 2 3 6 ` at the machine (Lists.lean ` memBody ` , ` memList_le_B ` ; blueprint D5).

  t12revpfx  the reversed prefix one entry on: ` encList ( rev ( L prefix ( j + 1 ) ) ) ++ Z = EW( L[j] , encList ( rev ( L prefix j ) ) ++ Z ) `
  t12rnpfx   ` A e. ran ( L prefix ( j + 1 ) ) <-> ( A e. ran ( L prefix j ) \\/ A = L[j] ) `
  tmimlbi    one entry ( ` memBody_runs ` ) along the family ` P' ` : two ` dup ` , ` cmpFrag ` , the ` ite ` by cases, ` moveEntry `
  tmimlst    the frame: the family's typing, its column 5, its values at 0 and at the end
  tmimlsl    the loop ( ` P' ` a letter): the pushes, ~ tm2lfes , ~ tmimesb , ~ tmiizbs , the load, ~ tmidropnb
  tmimlsb    ` memList_le_B ` (cost ` ( # L + 1 ) x. 6 B b ` , ` 1 <_ b ` ; blueprint section 3)

    MM_DB=sorties/t12.mm python3 tools/gen/t12_m_mls.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t7_e_cmp import machine, togk, letgk, lamty
from t7lib import mval, not1o, ifex_closed
from t10_n_rgf import tmbn
from t10_d_dot import skip_ty, cls_to, load_nfl
from t10_e_doa import lift_from
from t10_u_s2s import expose, me_bound_n
import t8alib as A8
import t7c_h_lst as LST
from t12_j_acc import encgam0, skip_to_s, notif_fleq, Plain, widen_post
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
TB = lambda x: '( TMB ` %s )' % x
NL = '( # ` L )'
LGL = '( encNatGam o. L )'
NLL = '( # ` %s )' % LGL
DOML = '( 0 ... %s )' % NLL
EBL = lambda k: '( encListB ` ( %s substr <. %s , %s >. ) )' % (LGL, k, NLL)
C5L = lambda k: '( %s ++ R )' % EBL(k)
RPF = lambda k: '( reverse ` ( L prefix %s ) )' % k
C6 = lambda k: '( ( encList ` %s ) ++ ( D ` 6 ) )' % RPF(k)
MACC = lambda k: 'if ( A e. ran ( L prefix %s ) , 1 , 0 )' % k
E3 = lambda k: EWg(MACC(k), DK(3))
PM = lambda k: UPS('D', ('3', E3(k)), ('5', C5L(k)), ('6', C6(k)))
PFM = '( k e. %s |-> %s )' % (DOML, PM('k'))
PV = "P'"
CEQ_ = '( u e. TMSt |-> if ( ( TMcmp ` u ) = 1o , 1o , (/) ) )'
W2R = '( <" 2 "> ++ R )'
MACCL = 'if ( A e. ran L , 1 , 0 )'
FLAG_ML = 'if ( A e. ran L , 1o , (/) )'

ST_REVPFX = ("( ( L e. Word NN0 /\\ ( J e. ( 0 ..^ ( # ` L ) ) /\\ Z e. Word Gamma' ) ) -> "
             "( ( encList ` ( reverse ` ( L prefix ( J + 1 ) ) ) ) ++ Z ) = "
             "( ( encNatGam ` ( L ` J ) ) ++ ( <\" 4 \"> ++ ( ( encList ` ( reverse ` ( L prefix J ) ) ) ++ Z ) ) ) )")
ST_RNPFX = ('( ( ( L e. Word NN0 /\\ J e. ( 0 ..^ ( # ` L ) ) ) /\\ A e. NN0 ) -> '
            '( A e. ran ( L prefix ( J + 1 ) ) <-> ( A e. ran ( L prefix J ) \\/ A = ( L ` J ) ) ) )')

DATA_MLS = ((STKD('D'), ('L e. Word NN0', 'A e. NN0', 'B e. NN0'), ('1 <_ B', RALB('L', 'B'), LT2('A'))),
            (WG('R'), WG('X')), (DEQ(5, ENCL('L', 'R')), DEQ(1, EWg('A', 'X'))))
TREE_MLS = TREE0('mls', DATA_MLS)
PSI_T = (TREE_MLS, '%s = %s' % (PV, PFM))
PSI = cj(PSI_T)
LMS = FRAGS['mls'].lmap()
P6 = PL('P', 6)
LMB = FRAGS['mlb'].lmap(P6, LMS['Z5'])
BODY_ENTRY = FRAGS['mlb'].entry(P6)
YM = '( ( 5 x. %s ) + 3 )' % TB('B')
YFM = '( i e. NN0 |-> %s )' % YM
PT_ = lambda j: '( %s ` %s )' % (PV, j)
HOARE_ML = TRI(CLN(BODY_ENTRY, S, PT_('j')), CLN(LMS['Z5'], S, PT_('( j + 1 )')), YM)
add12('tmimlbi', (PSI_T, 'j e. ( 0 ..^ %s )' % NLL), HOARE_ML)
FTY = '%s : %s --> ( TM2Stk ` T )' % (PV, DOML)
COLF = lambda j: '( ( %s ` %s ) ` 5 ) = %s' % (PV, j, C5L(j))
FCOL = 'A. j e. %s %s' % (DOML, COLF('j'))
P0EQ = '( %s ` 0 ) = %s' % (PV, UPS('D', ('3', '( <" 4 "> ++ ( D ` 3 ) )'), ('6', '( <" 2 "> ++ ( D ` 6 ) )')))
PNV = UPS('D', ('3', EWg(MACCL, DK(3))), ('5', W2R), ('6', '( ( encList ` ( reverse ` L ) ) ++ ( D ` 6 ) )'))
PNEQ = '( %s ` %s ) = %s' % (PV, NLL, PNV)
add12('tmimlst', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FTY, FCOL, P0EQ, PNEQ))
MLSC = '( ( %s + 1 ) x. ( 6 x. %s ) )' % (NL, TB('B'))
CONCL_MLS = TRI(CS('mls'), CLN('E', NFL(FLAG_ML), 'D'), MLSC)
add12('tmimlsl', PSI_T, CONCL_MLS)
add12('tmimlsb', TREE_MLS, CONCL_MLS)


def t12revpfx():
    lab = 't12revpfx'
    ph = "( L e. Word NN0 /\\ ( J e. ( 0 ..^ ( # ` L ) ) /\\ Z e. Word Gamma' ) )"
    w = W(lab, 'The list of the reversed prefix one entry on: the entry ` L[j] ` pushed on the list of the reversed prefix '
               '(~ tm2lpfxs1 , ~ revccat , ~ tm2lenccons ; Lists.lean ` memList_runs ` , the moved entries).')
    s = w.s
    c = Ctx(w, ph, ('L e. Word NN0', ('J e. ( 0 ..^ ( # ` L ) )', "Z e. Word Gamma'")))
    ll, jj, zw = c['L e. Word NN0'], c['J e. ( 0 ..^ ( # ` L ) )'], c["Z e. Word Gamma'"]
    LJ = '( L ` J )'
    P0_, P1_ = '( L prefix J )', '( L prefix ( J + 1 ) )'
    lj = s([ll, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, LJ))
    pf = s([ll, jj, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (ph, P1_, P0_, LJ))
    pw = s([ll, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, P0_))
    s1 = s([lj, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (ph, LJ))
    r1 = s([pw, s1, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` %s ) ) )' % (ph, P0_, LJ, LJ, P0_))
    RV = '( reverse ` %s )' % P0_
    r2 = s([s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (LJ, LJ))], 'a1i', '( %s -> ( reverse ` <" %s "> ) = <" %s "> )' % (ph, LJ, LJ))
    rv = s([s([pf], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( %s ++ <" %s "> ) ) )' % (ph, P1_, P0_, LJ)),
            s([r1, s([r2], 'oveq1d', '( %s -> ( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, LJ, RV, LJ, RV))], 'eqtrd',
              '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( <" %s "> ++ %s ) )' % (ph, P0_, LJ, LJ, RV))], 'eqtrd',
           '( %s -> ( reverse ` %s ) = ( <" %s "> ++ %s ) )' % (ph, P1_, LJ, RV))
    rvw = s([pw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RV))
    ec = s([lj, rvw, w.inst('tm2lenccons')], 'syl2anc', '( %s -> ( encList ` ( <" %s "> ++ %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (ph, LJ, RV, LJ, RV))
    el = s([s([rv], 'fveq2d', '( %s -> ( encList ` ( reverse ` %s ) ) = ( encList ` ( <" %s "> ++ %s ) ) )' % (ph, P1_, LJ, RV)), ec], 'eqtrd',
           '( %s -> ( encList ` ( reverse ` %s ) ) = ( ( encNatGam ` %s ) ++ ( <" 4 "> ++ ( encList ` %s ) ) ) )' % (ph, P1_, LJ, RV))
    EGA = '( encNatGam ` %s )' % LJ
    ELR = '( encList ` %s )' % RV
    ega = s([lj, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EGA))
    elr = s([rvw, w.inst('tm2lenccl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ELR))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    g4 = s([s4, elr, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ %s ) e. Word Gamma' )" % (ph, ELR))
    a1 = s([ega, g4, zw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ Z ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ Z ) ) )' % (ph, EGA, ELR, EGA, ELR))
    a2 = s([s4, elr, zw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ Z ) = ( <" 4 "> ++ ( %s ++ Z ) ) )' % (ph, ELR, ELR))
    t1 = s([s([el], 'oveq1d', '( %s -> ( ( encList ` ( reverse ` %s ) ) ++ Z ) = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ Z ) )' % (ph, P1_, EGA, ELR)), a1],
           'eqtrd', '( %s -> ( ( encList ` ( reverse ` %s ) ) ++ Z ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ Z ) ) )' % (ph, P1_, EGA, ELR))
    w.qed([t1, s([a2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ Z ) ) = ( %s ++ ( <" 4 "> ++ ( %s ++ Z ) ) ) )' % (ph, EGA, ELR, EGA, ELR))],
          'eqtrd', ST_REVPFX)
    return w.run()


def t12rnpfx():
    lab = 't12rnpfx'
    ph = '( ( L e. Word NN0 /\\ J e. ( 0 ..^ ( # ` L ) ) ) /\\ A e. NN0 )'
    w = W(lab, 'Membership in the range of a prefix one entry on (~ tm2lpfxs1 , ~ ccatrn , ~ s1rn ).')
    s = w.s
    ll = s([], 'simpll', '( %s -> L e. Word NN0 )' % ph)
    jj = s([], 'simplr', '( %s -> J e. ( 0 ..^ ( # ` L ) ) )' % ph)
    an = s([], 'simpr', '( %s -> A e. NN0 )' % ph)
    LJ = '( L ` J )'
    P0_, P1_ = '( L prefix J )', '( L prefix ( J + 1 ) )'
    lj = s([ll, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, LJ))
    pf = s([ll, jj, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (ph, P1_, P0_, LJ))
    pw = s([ll, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, P0_))
    s1 = s([lj, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (ph, LJ))
    rn = s([pw, s1, w.inst('ccatrn')], 'syl2anc', '( %s -> ran ( %s ++ <" %s "> ) = ( ran %s u. ran <" %s "> ) )' % (ph, P0_, LJ, P0_, LJ))
    r1 = s([lj, w.inst('s1rn')], 'syl', '( %s -> ran <" %s "> = { %s } )' % (ph, LJ, LJ))
    e = s([s([pf], 'rneqd', '( %s -> ran %s = ran ( %s ++ <" %s "> ) )' % (ph, P1_, P0_, LJ)), rn,
           s([r1], 'uneq2d', '( %s -> ( ran %s u. ran <" %s "> ) = ( ran %s u. { %s } ) )' % (ph, P0_, LJ, P0_, LJ))], '3eqtrd',
          '( %s -> ran %s = ( ran %s u. { %s } ) )' % (ph, P1_, P0_, LJ))
    b1 = s([e], 'eleq2d', '( %s -> ( A e. ran %s <-> A e. ( ran %s u. { %s } ) ) )' % (ph, P1_, P0_, LJ))
    b2 = s([], 'elun', '( A e. ( ran %s u. { %s } ) <-> ( A e. ran %s \\/ A e. { %s } ) )' % (P0_, LJ, P0_, LJ))
    b3 = s([s([an, w.inst('elsng')], 'syl', '( %s -> ( A e. { %s } <-> A = %s ) )' % (ph, LJ, LJ))], 'orbi2d',
           '( %s -> ( ( A e. ran %s \\/ A e. { %s } ) <-> ( A e. ran %s \\/ A = %s ) ) )' % (ph, P0_, LJ, P0_, LJ))
    w.qed([b1, s([s([b2], 'a1i', '( %s -> ( A e. ( ran %s u. { %s } ) <-> ( A e. ran %s \\/ A e. { %s } ) ) )' % (ph, P0_, LJ, P0_, LJ)), b3], 'bitrd',
                 '( %s -> ( A e. ( ran %s u. { %s } ) <-> ( A e. ran %s \\/ A = %s ) ) )' % (ph, P0_, LJ, P0_, LJ))], 'bitrd', ST_RNPFX)
    return w.run()


class Mls(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        ll, an, bn = c0['L e. Word NN0'], c0['A e. NN0'], c0['B e. NN0']
        rw, xw = c0[WG('R')], c0[WG('X')]
        Base.__init__(self, w, ph, T, N8, 'mls', {'5': (ENCL('L', 'R'), enclg(w, ph, 'L', ll, 'R', rw)), '1': (EWg('A', 'X'), ewg_(w, ph, 'A', an, 'X', xw))})
        s = w.s
        self.ll, self.an, self.bn, self.rw, self.xw = ll, an, bn, rw, xw
        c = self.c
        self.b1, self.alt = c['1 <_ B'], c[LT2('A')]
        self.lgw = s([ll, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LGL, BITS))
        self.lg = s([ll, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = %s )' % (ph, NLL, NL))
        self.nl = s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
        self.nll = s([self.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLL))
        self.cl = Closure(w, ph, {'A': ('NN0', an), 'B': ('NN0', bn)})
        self.cl.leaf(NL, 'NN0', self.nl); self.cl.leaf(NLL, 'NN0', self.nll)
        self.cl.leaf(TB('B'), 'NN0', tmbn(w, ph, 'B', bn))
        self.cl.atom('( 2 ^ B )')
        self.d3, self.d6, self.d2 = self.S0.vals['3'][2], self.S0.vals['6'][2], self.S0.vals['2'][2]
        # 1 < 2 ^ B from 1 <_ B
        u1 = s([s([s([closed(w, ph, '1z', '1 e. ZZ'), s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), self.b1], '3jca', '( %s -> ( 1 e. ZZ /\\ B e. ZZ /\\ 1 <_ B ) )' % ph),
                  w.inst('eluz2')], 'sylibr', '( %s -> B e. ( ZZ>= ` 1 ) )' % ph)], 'id', '') if False else \
            s([s([closed(w, ph, '1z', '1 e. ZZ'), s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), self.b1], '3jca', '( %s -> ( 1 e. ZZ /\\ B e. ZZ /\\ 1 <_ B ) )' % ph),
              w.inst('eluz2')], 'sylibr', '( %s -> B e. ( ZZ>= ` 1 ) )' % ph)
        p1 = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u1, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ 1 ) <_ ( 2 ^ B ) )' % ph)
        e21 = s([s([s([], '2cn', '2 e. CC'), w.inst('exp1')], 'ax-mp', '( 2 ^ 1 ) = 2')], 'a1i', '( %s -> ( 2 ^ 1 ) = 2 )' % ph)
        self.two_le = s([e21, p1], 'eqbrtrrd', '( %s -> 2 <_ ( 2 ^ B ) )' % ph)
        self.tb1 = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB('B'))), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB('B')))

    def maccn(self, k):
        """( ph -> MACC( k ) e. NN0 ) , ( ph -> MACC( k ) < 2 ^ B )"""
        w, ph, s = self.w, self.ph, self.w.s
        a = s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, MACC(k)))
        cond = 'A e. ran ( L prefix %s )' % k
        pt, pn = '( %s /\\ %s )' % (ph, cond), '( %s /\\ -. %s )' % (ph, cond)
        l1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = 1 )' % (pt, MACC(k))), closed(w, pt, '1le1', '1 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pt, MACC(k)))
        l2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = 0 )' % (pn, MACC(k))), closed(w, pn, '0le1', '0 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pn, MACC(k)))
        le = s([l1, l2], 'pm2.61dan', '( %s -> %s <_ 1 )' % (ph, MACC(k)))
        cl = Closure(w, ph, {'B': ('NN0', self.bn)})
        cl.leaf(MACC(k), 'NN0', a)
        cl.atom('( 2 ^ B )')
        return a, linarith(w, ph, [le, self.two_le], '%s < ( 2 ^ B )' % MACC(k), closure=cl)

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        an, _ = self.maccn(k)
        g3 = self.g(E3(k), ewg_(w, ph, MACC(k), an, DK(3), self.d3))
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LGL, k, NLL, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EBL(k)))
        g5 = self.g(C5L(k), wgcat(w, ph, EBL(k), 'R', eb, self.rw))
        pw = s([self.ll, w.inst('pfxcl')], 'syl', '( %s -> ( L prefix %s ) e. Word NN0 )' % (ph, k))
        rw_ = s([pw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RPF(k)))
        g6 = self.g(C6(k), enclg(w, ph, RPF(k), rw_, DK(6), self.d6))
        return self.S0.upd('3', E3(k), g3).upd('5', C5L(k), g5).upd('6', C6(k), g6)


def ceq_test(w, pc, F_, G_, fn, gn, truth, cnd):
    """( pc -> A. m e. CMPC( F , G ) ( CEQ ` m ) = 1o ) (truth : cnd : ( pc -> F = G )) or its negation"""
    s = w.s
    CQ = CMPC(F_, G_)
    XL = lambda t: 'if ( ( TMcmp ` %s ) = 1o , 1o , (/) )' % t
    pm = '( %s /\\ m e. %s )' % (pc, CQ)
    mi = s([], 'simpr', '( %s -> m e. %s )' % (pm, CQ))
    cond = lambda t: '( TMcmp ` %s ) = ( %s Ncmp %s )' % (t, F_, G_)
    cg, new = w.wcongr(cond('h'), {'h': 'm'}, 'h = m', {'h': s([], 'id', '( h = m -> h = m )')})
    both = s([mi, s([cg], 'elrab', '( m e. %s <-> ( m e. TMSt /\\ %s ) )' % (CQ, cond('m')))], 'sylib', '( %s -> ( m e. TMSt /\\ %s ) )' % (pm, cond('m')))
    mm = s([both], 'simpld', '( %s -> m e. TMSt )' % pm)
    mc = s([both], 'simprd', '( %s -> %s )' % (pm, cond('m')))
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = 1o', '1o', '(/)', s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', XL, 'm', mm, xex)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pc, st)))
    ne_ = s([s([fn, gn], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (pc, F_, G_)), w.inst('ncmpeq')], 'syl',
            '( %s -> ( ( %s Ncmp %s ) = 1o <-> %s = %s ) )' % (pc, F_, G_, F_, G_))
    if truth:
        nc = s([cnd, ne_], 'mpbird', '( %s -> ( %s Ncmp %s ) = 1o )' % (pc, F_, G_))
        cm = s([mc, Lm(nc)], 'eqtrd', '( %s -> ( TMcmp ` m ) = 1o )' % pm)
        v = s([cv, s([cm], 'iftrued', '( %s -> %s = 1o )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CEQ_))
        return s([v], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pc, CQ, CEQ_))
    nn0 = s([cnd, ne_], 'mtbird', '( %s -> -. ( %s Ncmp %s ) = 1o )' % (pc, F_, G_))
    cm1 = s([Lm(nn0), s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = 1o <-> ( %s Ncmp %s ) = 1o ) )' % (pm, F_, G_))], 'mtbird',
            '( %s -> -. ( TMcmp ` m ) = 1o )' % pm)
    c0 = s([cv, s([cm1], 'iffalsed', '( %s -> %s = (/) )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CEQ_))
    return s([not1o(w, pm, c0, CEQ_, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pc, CQ, CEQ_))


def tmimlbi():
    lab = 'tmimlbi'
    T0 = numtree((PSI_T, 'j e. ( 0 ..^ %s )' % NLL))
    ph = cj(T0)
    w = W(lab, 'One entry of Lean\'s ` memList ` loop at the machine ( ` memBody_runs ` ): along the family of the accumulator, '
               '` dup 5 3 2 ; dup 1 2 3 ; cmpFrag 3 2 ` (~ tmidupb , ~ tmicmpb ), the ` ite ` on ` cmp = eq ` by cases '
               '(the accumulator set to 1, or ` skip ` ), ` moveEntry 5 6 2 ` (~ tmime ), within ` 5 B b + 3 ` steps.')
    s = w.s
    outs = []
    for eq in (True, False):
        LJ = '( L ` j )'
        cc = '%s = A' % LJ if eq else '-. %s = A' % LJ
        T = (T0, cc)
        pc = cj(T)
        B = Mls(w, pc, T)
        c, mk, cl = B.c, B.mk, B.cl
        cst = c[cc]
        jj = c['j e. ( 0 ..^ %s )' % NLL]
        jL = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (pc, NLL, NL))], 'eleqtrd', '( %s -> j e. ( 0 ..^ %s ) )' % (pc, NL))
        jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (pc, DOML))
        J1 = '( j + 1 )'
        j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (pc, J1, DOML))
        fam = c['%s = %s' % (PV, PFM)]
        pvj, SJ = fam_at(w, pc, mk, B.ne, fam, PV, 'k', DOML, PM, 'j', jz, B.pbst('j'))
        PT = PT_('j')
        dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (pc, EBL('j'), LGL, EBL(J1)))
        lgj = s([s([B.ll, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ %s ) --> NN0 )' % (pc, NL)), jL, w.inst('fvco3')], 'syl2anc',
                '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (pc, LGL, LJ))
        ljn = s([B.ll, jL, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, LJ))
        sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (pc, LGL, J1, NLL, BITS))
        eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (pc, EBL(J1)))
        g4 = wg4(w, pc, EBL(J1), eb1)
        egj = s([lgj, encw(w, pc, LJ, ljn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (pc, LGL))
        ca1 = s([egj, g4, B.rw, w.inst('ccatass')], 'syl3anc',
                '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (pc, LGL, EBL(J1), LGL, EBL(J1)))
        s4 = s([closed(w, pc, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % pc)
        ca2 = s([s4, eb1, B.rw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ R ) = ( <" 4 "> ++ %s ) )' % (pc, EBL(J1), C5L(J1)))
        r1 = s([s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) )' % (pc, C5L('j'), LGL, EBL(J1))), ca1], 'eqtrd',
               '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (pc, C5L('j'), LGL, EBL(J1)))
        V5 = EWg(LJ, C5L(J1))
        r2 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) = %s )' % (pc, LGL, EBL(J1), V5))
        iv = s([SJ.vals['5'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (pc, C5L('j'), V5))], 'eqtrd', '( %s -> ( %s ` 5 ) = %s )' % (pc, PT, V5))
        g51 = B.g(C5L(J1), wgcat(w, pc, EBL(J1), 'R', eb1, B.rw))
        lr = s([s([B.ll, w.inst('wrdfn')], 'syl', '( %s -> L Fn ( 0 ..^ %s ) )' % (pc, NL)), jL, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran L )' % (pc, LJ))
        ljlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ B ) <-> %s < ( 2 ^ B ) ) )' % (LJ, LJ)), lr, c[RALB('L', 'B')]], 'rspcdva', '( %s -> %s < ( 2 ^ B ) )' % (pc, LJ))
        maj, majlt = B.maccn('j')
        cl.leaf(MACC('j'), 'NN0', maj)
        B.deep('mls', 0)
        v2 = dict(SJ.vals)
        v2['5'] = (V5, iv, B.g(V5, ewg_(w, pc, LJ, ljn, C5L(J1), g51)))
        SJ2 = Stacks(w, pc, mk, SJ.D, SJ.memb, SJ.ne, v2)
        R = B.run(SJ2)
        # 1. dup 5 3 2 ; 2. dup 1 2 3 ; 3. cmpFrag 3 2
        V3 = EWg(LJ, E3('j'))
        B.call(R, 'tmidupb', {'K': '5', 'J': '3', 'I': '2', 'F': LJ, 'N': 'B', 'X': C5L(J1), 'P': PL(P6, 4), 'E': LMB['Y2']},
               {'%s e. NN0' % LJ: ljn, '%s < ( 2 ^ B )' % LJ: ljlt, WG(C5L(J1)): g51}, [('3', V3, B.g(V3, ewg_(w, pc, LJ, ljn, E3('j'), B.gam[E3('j')])))])
        V2 = EWg('A', DK(2))
        B.call(R, 'tmidupb', {'K': '1', 'J': '2', 'I': '3', 'F': 'A', 'N': 'B', 'X': 'X', 'P': PL(P6, 5), 'E': LMB['Y3']},
               {}, [('2', V2, B.g(V2, ewg_(w, pc, 'A', B.an, DK(2), B.d2)))])
        B.call(R, 'tmicmpb', {'K': '3', 'J': '2', 'F': LJ, 'G': 'A', 'N': 'B', 'X': E3('j'), 'Y': DK(2), 'P': PL(P6, 6), 'E': LMB['Z1']},
               {'%s e. NN0' % LJ: ljn, '%s < ( 2 ^ B )' % LJ: ljlt, WG(E3('j')): B.gam[E3('j')]}, [('3', E3('j'), B.gam[E3('j')]), ('2', DK(2), B.d2)])
        CQ = CMPC(LJ, 'A')
        cty = lamty(w, pc, mk, CEQ_, lambda t: 'if ( ( TMcmp ` %s ) = 1o , 1o , (/) )' % t, '2o', s([], '2oex', '2o e. _V'),
                    s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', 'if ( ( TMcmp ` u ) = 1o , 1o , (/) ) e. 2o'))
        Z1, Z2, Z3, Z4 = LMB['Z1'], LMB['Z2'], LMB['Z3'], LMB['Z4']
        DROP0 = PL(PL(P6, 7), 0)
        ME0 = PL(PL(P6, 8), 0)
        ex = {SSS(CQ): B.ss(CQ), CTY(CEQ_): cty}
        if eq:
            ex[STMT(GT(Z4))] = gotocl(w, pc, mk['tv'], Z4, B.ex[LAB(Z4)])
            ex['A. m e. %s ( %s ` m ) = 1o' % (CQ, CEQ_)] = ceq_test(w, pc, LJ, 'A', ljn, B.an, True, cst)
            B.call(R, 'tm2lbrt', {'A': Z1, 'C': CEQ_, 'E': DROP0, 'Q': GT(Z4), 'N': CQ}, ex, [])
            widen_post(w, pc, B, R, CQ, DROP0)
            Son, old = expose(w, pc, B, R, '3')
            B.call(R, 'tmidropb', {'K': '3', 'F': MACC('j'), 'N': 'B', 'X': DK(3), 'P': PL(P6, 7), 'E': Z2},
                   {'%s e. NN0' % MACC('j'): maj, '%s < ( 2 ^ B )' % MACC('j'): majlt, WG(DK(3)): B.d3}, [('3', DK(3), B.d3)], on=(Son, old))
            K4 = '( <" 4 "> ++ ( D ` 3 ) )'
            g4_ = B.g(K4, wg4(w, pc, DK(3), B.d3))
            B.call(R, 'tm2fpshn', {'A': Z2, 'E': Z3, 'K': '3', 'Z': '4', 'N': S},
                   {'4 e. %s' % GX('3'): letgk(w, pc, mk, '4', '3', closed(w, pc, 'gamma4', "4 e. Gamma'")), SSS(S): closed(w, pc, 'ssid', '%s C_ %s' % (S, S))},
                   [('3', K4, g4_)])
            bg1 = s([closed(w, pc, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (pc, BIT1_))
            K41 = '( <" %s "> ++ %s )' % (BIT1_, K4)
            g41 = B.g(K41, wgcat(w, pc, '<" %s ">' % BIT1_, K4, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (pc, BIT1_)), g4_))
            B.call(R, 'tm2fpshn', {'A': Z3, 'E': ME0, 'K': '3', 'Z': BIT1_, 'N': S},
                   {'%s e. %s' % (BIT1_, GX('3')): s([bg1, mk['k']['3']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (pc, BIT1_, GX('3'))),
                    SSS(S): closed(w, pc, 'ssid', '%s C_ %s' % (S, S))}, [('3', K41, g41)])
            new3 = K41
        else:
            ex[STMT(GT(DROP0))] = gotocl(w, pc, mk['tv'], DROP0, B.ex[LAB(DROP0)])
            ex['A. m e. %s -. ( %s ` m ) = 1o' % (CQ, CEQ_)] = ceq_test(w, pc, LJ, 'A', ljn, B.an, False, cst)
            B.call(R, 'tm2fbrg', {'A': Z1, 'C': CEQ_, 'E': Z4, 'Q': GT(DROP0), 'N': CQ}, ex, [])
            B.call(R, 'tm2flg', {'A': Z4, 'E': ME0, 'F': LID, 'N': CQ, "N'": S},
                   {LTY(LID): skip_ty(w, pc, mk), SSS(CQ): B.ss(CQ), SSS(S): closed(w, pc, 'ssid', '%s C_ %s' % (S, S)),
                    'A. r e. %s ( %s ` r ) e. %s' % (CQ, LID, S): skip_to_s(w, pc, mk, CQ)}, [])
            new3 = None
        # moveEntry 5 6 2
        WLJ = '( encNatGam ` %s )' % LJ
        V6 = EWg(LJ, C6('j'))
        B.call(R, 'tmime', {'K': '5', 'J': '6', 'I': '2', 'W': WLJ, 'X': C5L(J1), 'P': PL(P6, 8), 'E': LMS['Z5']},
               {WRD(WLJ, BITS): engb(w, pc, LJ, ljn), WG(C5L(J1)): g51}, [('5', C5L(J1), g51), ('6', V6, B.g(V6, ewg_(w, pc, LJ, ljn, C6('j'), B.gam[C6('j')])))])
        e, nrm, out2 = renorm(w, pc, B, R, [('3', E3('j')), ('5', C5L('j')), ('6', C6('j'))], N8, PT=PT, pv=pvj)
        if eq:
            assert out2 == [('3', new3), ('5', C5L(J1)), ('6', V6)], out2
        else:
            assert out2 == [('3', E3('j')), ('5', C5L(J1)), ('6', V6)], out2
        # the accumulator at j + 1 and the moved entries
        rn = s([s([B.ll, jL], 'jca', '( %s -> ( L e. Word NN0 /\\ j e. ( 0 ..^ %s ) ) )' % (pc, NL)), B.an, w.inst('t12rnpfx')], 'syl2anc',
               '( %s -> ( A e. ran ( L prefix %s ) <-> ( A e. ran ( L prefix j ) \\/ A = %s ) ) )' % (pc, J1, LJ))
        if eq:
            m1 = s([s([s([cst], 'eqcomd', '( %s -> A = %s )' % (pc, LJ))], 'olcd', '( %s -> ( A e. ran ( L prefix j ) \\/ A = %s ) )' % (pc, LJ)), rn], 'mpbird',
                   '( %s -> A e. ran ( L prefix %s ) )' % (pc, J1))
            a1 = s([m1], 'iftrued', '( %s -> %s = 1 )' % (pc, MACC(J1)))
            e1 = s([s([B.d3, w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (pc, EWg('1', DK(3)), K41)),
                    s([s([s([a1], 'eqcomd', '( %s -> 1 = %s )' % (pc, MACC(J1)))], 'fveq2d', '( %s -> ( encNatGam ` 1 ) = ( encNatGam ` %s ) )' % (pc, MACC(J1)))], 'oveq1d',
                      '( %s -> %s = %s )' % (pc, EWg('1', DK(3)), E3(J1)))], 'eqtr3d', '( %s -> %s = %s )' % (pc, K41, E3(J1)))
            rules = {K41: (E3(J1), e1)}
        else:
            ne = s([cst], 'neqned', '( %s -> %s =/= A )' % (pc, LJ))
            nea = s([s([ne], 'necomd', '( %s -> A =/= %s )' % (pc, LJ))], 'neneqd', '( %s -> -. A = %s )' % (pc, LJ))
            bi = s([rn, s([nea], 'biorfd' if False else 'biorf', '') if False else s([nea], 'biorfd', '( %s -> ( A e. ran ( L prefix j ) <-> ( A = %s \\/ A e. ran ( L prefix j ) ) ) )' % (pc, LJ))],
                   'id', '') if False else None
            # ( A e. ran pfx( j + 1 ) <-> A e. ran pfx( j ) ) from -. A = L[j]
            o1 = s([nea, w.inst('biorf')], 'syl', '( %s -> ( A e. ran ( L prefix j ) <-> ( A = %s \\/ A e. ran ( L prefix j ) ) ) )' % (pc, LJ))
            o2 = s([], 'orcom', '( ( A = %s \\/ A e. ran ( L prefix j ) ) <-> ( A e. ran ( L prefix j ) \\/ A = %s ) )' % (LJ, LJ))
            bi = s([rn, s([o1, s([o2], 'a1i', '( %s -> ( ( A = %s \\/ A e. ran ( L prefix j ) ) <-> ( A e. ran ( L prefix j ) \\/ A = %s ) ) )' % (pc, LJ, LJ))], 'bitrd',
                            '( %s -> ( A e. ran ( L prefix j ) <-> ( A e. ran ( L prefix j ) \\/ A = %s ) ) )' % (pc, LJ))], 'bitr4d',
                   '( %s -> ( A e. ran ( L prefix %s ) <-> A e. ran ( L prefix j ) ) )' % (pc, J1))
            a1 = s([s([bi], 'ifbid', '( %s -> %s = %s )' % (pc, MACC(J1), MACC('j')))], 'eqcomd', '( %s -> %s = %s )' % (pc, MACC('j'), MACC(J1)))
            e1 = s([s([a1], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` %s ) )' % (pc, MACC('j'), MACC(J1)))], 'oveq1d', '( %s -> %s = %s )' % (pc, E3('j'), E3(J1)))
            rules = {E3('j'): (E3(J1), e1)}
        rp = s([B.ll, s([jL, B.d6], 'jca', "( %s -> ( j e. ( 0 ..^ %s ) /\\ ( D ` 6 ) e. Word Gamma' ) )" % (pc, NL)), w.inst('t12revpfx')], 'syl2anc',
               '( %s -> %s = %s )' % (pc, C6(J1), V6))
        rules[V6] = (C6(J1), s([rp], 'eqcomd', '( %s -> %s = %s )' % (pc, V6, C6(J1))))
        r_, nrm2 = w.rewrite(nrm, rules, pc)
        assert nrm2 == PM(J1), '\n%s\n%s' % (nrm2, PM(J1))
        pv1, _ = fam_at(w, pc, mk, B.ne, fam, PV, 'k', DOML, PM, J1, j1, B.pbst(J1))
        D0 = triple_D(R.cur)
        deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (pc, D0, PM(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (pc, D0, PV, J1))
        t, C, D, n = R.tri, R.C0, R.cur, R.n
        t, C, D, n = hrrw(w, pc, t, C, D, n, deq=clneq(w, pc, LMS['Z5'], S, deq, D0, PT_(J1)))
        mc = me_bound_n(w, pc, LJ, ljn, ljlt, 'B', B.bn, cl)
        le = linarith(w, pc, [mc, B.tb1], '%s <_ %s' % (n, YM), closure=cl)
        outs.append(hrle(w, pc, mk['phm'], t, C, D, n, YM, cl.mem(YM, 'NN0'), le))
        assert TRI(C, D, YM) == HOARE_ML, '\n%s\n%s' % (TRI(C, D, YM), HOARE_ML)
    st = s(outs, 'pm2.61dan', '( %s -> %s )' % (ph, HOARE_ML))
    finish(w, st, lab)
    return w.run()


def tmimlst():
    lab = 'tmimlst'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` memList ` loop at the machine: the family of the accumulator is a stack family whose 5 '
               'column is the rest of the list, at 0 it is the stacks after ` pushSym 6 bra ; pushNum 3 0 ` , at the end the '
               'accumulator records ` a e. l ` , the list\'s ` bra ` remains on 5 and the reversed list sits on 6.')
    s = w.s
    B = Mls(w, ph, T)
    c, mk = B.c, B.mk
    fam = c['%s = %s' % (PV, PFM)]
    ph0t = (TREE_MLS, NUMS)
    ph0 = cj(ph0t)
    TK = (ph0t, 'k e. %s' % DOML)
    pk = cj(TK)
    Bk = Mls(w, pk, TK)
    Sk = Bk.pbst('k')
    fm = s([Sk.memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PFM, DOML))
    j0 = s([c[cj(TREE_MLS)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fm2 = s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PFM, DOML))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOML, PFM, DOML)), fm2],
            'mpbird', '( %s -> %s )' % (ph, FTY))
    TJ = (T, 'j e. %s' % DOML)
    pj = cj(TJ)
    Bj = Mls(w, pj, TJ)
    jz = Bj.c['j e. %s' % DOML]
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PFM)], PV, 'k', DOML, PM, 'j', jz, Bj.pbst('j'))
    col = s([SJ.vals['5'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    # the value at 0
    z0 = s([B.nll, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOML))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOML, PM, '0', z0, B.pbst('0'))
    p00 = s([s([], 'pfx00', '( L prefix 0 ) = (/)')], 'a1i', '( %s -> ( L prefix 0 ) = (/) )' % ph)
    nin = s([s([s([s([p00], 'rneqd', '( %s -> ran ( L prefix 0 ) = ran (/) )' % ph), s([s([], 'rn0', 'ran (/) = (/)')], 'a1i', '( %s -> ran (/) = (/) )' % ph)], 'eqtrd',
                 '( %s -> ran ( L prefix 0 ) = (/) )' % ph)], 'eleq2d', '( %s -> ( A e. ran ( L prefix 0 ) <-> A e. (/) ) )' % ph),
              s([s([], 'noel', '-. A e. (/)')], 'a1i', '( %s -> -. A e. (/) )' % ph)], 'mtbird', '( %s -> -. A e. ran ( L prefix 0 ) )' % ph)
    a0 = s([nin], 'iffalsed', '( %s -> %s = 0 )' % (ph, MACC('0')))
    K4 = '( <" 4 "> ++ ( D ` 3 ) )'
    e3 = s([s([s([s([a0], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` 0 ) )' % (ph, MACC('0'))), encgam0(w, ph)], 'eqtrd',
                 '( %s -> ( encNatGam ` %s ) = (/) )' % (ph, MACC('0')))], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (ph, E3('0'), K4)),
            s([wg4(w, ph, DK(3), B.d3), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, K4, K4))], 'eqtrd', '( %s -> %s = %s )' % (ph, E3('0'), K4))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LGL, NLL, LGL))
    le_ = s([B.ll, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` L ) = ( encListB ` %s ) )' % (ph, LGL))
    e5 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EBL('0'), LGL)), le_], 'eqtr4d', '( %s -> %s = ( encList ` L ) )' % (ph, EBL('0')))],
           'oveq1d', '( %s -> %s = %s )' % (ph, C5L('0'), ENCL('L', 'R')))
    e5b = s([e5, s([c[DEQ(5, ENCL('L', 'R'))]], 'eqcomd', '( %s -> %s = ( D ` 5 ) )' % (ph, ENCL('L', 'R')))], 'eqtrd', '( %s -> %s = ( D ` 5 ) )' % (ph, C5L('0')))
    K2 = '( <" 2 "> ++ ( D ` 6 ) )'
    r0 = s([s([p00], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (ph, RPF('0'))), s([s([], 'rev0', '( reverse ` (/) ) = (/)')], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % ph)],
           'eqtrd', '( %s -> %s = (/) )' % (ph, RPF('0')))
    e6 = s([s([s([r0], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` (/) ) )' % (ph, RPF('0'))), s([s([], 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'a1i',
                                                                                                    '( %s -> ( encList ` (/) ) = <" 2 "> )' % ph)], 'eqtrd',
              '( %s -> ( encList ` %s ) = <" 2 "> )' % (ph, RPF('0')))], 'oveq1d', '( %s -> %s = %s )' % (ph, C6('0'), K2))
    rr, xx = w.rewrite(PM('0'), {E3('0'): (K4, e3), C5L('0'): ('( D ` 5 )', e5b), C6('0'): (K2, e6)}, ph)
    assert xx == UPS('D', ('3', K4), ('5', DK(5)), ('6', K2)), xx
    B.g(K4, wg4(w, ph, DK(3), B.d3))
    B.g(K2, wgcat(w, ph, '<" 2 ">', DK(6), s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph), B.d6))
    nst, outn = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, [('3', K4), ('5', DK(5)), ('6', K2)], B.gam, N8)
    assert outn == [('3', K4), ('6', K2)], outn
    p0 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx)), nst], 'eqtrd', '( %s -> %s )' % (ph, P0EQ))
    # the value at the end
    nz = s([B.nll, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLL, DOML))
    pvN, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOML, PM, NLL, nz, B.pbst(NLL))
    DR = '( %s substr <. %s , %s >. )' % (LGL, NLL, NLL)
    e2 = s([s([closed(w, ph, 'swrd00', '%s = (/)' % DR)], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (ph, DR)),
            closed(w, ph, 'tm2lencb0', '( encListB ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encListB ` %s ) = <" 2 "> )' % (ph, DR))
    e5n = s([e2], 'oveq1d', '( %s -> %s = %s )' % (ph, C5L(NLL), W2R))
    pfx = s([s([B.lg], 'oveq2d', '( %s -> ( L prefix %s ) = ( L prefix %s ) )' % (ph, NLL, NL)), s([B.ll, w.inst('pfxid')], 'syl', '( %s -> ( L prefix %s ) = L )' % (ph, NL))],
            'eqtrd', '( %s -> ( L prefix %s ) = L )' % (ph, NLL))
    e3n = s([s([s([s([pfx], 'rneqd', '( %s -> ran ( L prefix %s ) = ran L )' % (ph, NLL))], 'eleq2d', '( %s -> ( A e. ran ( L prefix %s ) <-> A e. ran L ) )' % (ph, NLL))],
              'ifbid', '( %s -> %s = %s )' % (ph, MACC(NLL), MACCL))], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` %s ) )' % (ph, MACC(NLL), MACCL))
    e3n2 = s([e3n], 'oveq1d', '( %s -> %s = %s )' % (ph, E3(NLL), EWg(MACCL, DK(3))))
    e6n = s([s([s([pfx], 'fveq2d', '( %s -> %s = ( reverse ` L ) )' % (ph, RPF(NLL)))], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` ( reverse ` L ) ) )' % (ph, RPF(NLL)))],
            'oveq1d', '( %s -> %s = ( ( encList ` ( reverse ` L ) ) ++ ( D ` 6 ) ) )' % (ph, C6(NLL)))
    rN, xN = w.rewrite(PM(NLL), {E3(NLL): (EWg(MACCL, DK(3)), e3n2), C5L(NLL): (W2R, e5n), C6(NLL): ('( ( encList ` ( reverse ` L ) ) ++ ( D ` 6 ) )', e6n)}, ph)
    assert xN == PNV, '\n%s\n%s' % (xN, PNV)
    pn = s([pvN, rN], 'eqtrd', '( %s -> %s )' % (ph, PNEQ))
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([p0, pn], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ph, FTY, FCOL, P0EQ, PNEQ))
    finish(w, st, lab)
    return w.run()


def tmimlsl():
    lab = 'tmimlsl'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` memList ` at the machine along the family of the accumulator ( ` P\' ` a letter): ` pushSym 6 bra ; '
               'pushNum 3 0 ` , the entry loop (~ tm2lfes , the entries by ~ tmimlbi , the frame by ~ tmimlst ), '
               '` moveEntries 6 5 2 ` (~ tmimesb ) restoring the list, ` isZero 3 2 ` (~ tmiizbs ), ` load\' ( flag := !flag ) ` , '
               '` dropNum 3 ` (~ tmidropnb ): the flag is ` a e. l ` , every stack restored, within ` ( # l + 1 ) 6 B b ` steps.')
    s = w.s
    B = Mls(w, ph, T)
    c, mk, cl, ex = B.c, B.mk, B.cl, B.ex
    B.deep('mls', 0)
    ex = dict(B.ex)
    ex.update(LST.handler_extra(w, ph, mk, LST.IFACE))
    tv, dd = mk['tv'], B.dd
    g = lambda k: B.S0.vals[k][2]
    ssid = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    fr = lift_from(w, PSI, ph, s([], 'tmimlst', STMTS12['tmimlst']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))
    fty, fcol = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY)), s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    p0eq, pneq = s([a2], 'simpld', '( %s -> %s )' % (ph, P0EQ)), s([a2], 'simprd', '( %s -> %s )' % (ph, PNEQ))
    # 1-2. the pushes
    R = B.run()
    K2 = '( <" 2 "> ++ ( D ` 6 ) )'
    g2 = B.g(K2, wgcat(w, ph, '<" 2 ">', DK(6), s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph), B.d6))
    B.call(R, 'tm2fpshn', {'A': LMS['Z1'], 'E': LMS['Z2'], 'K': '6', 'Z': '2', 'N': S},
           {'2 e. %s' % GX('6'): letgk(w, ph, mk, '2', '6', closed(w, ph, 'gamma2', "2 e. Gamma'")), SSS(S): ssid}, [('6', K2, g2)])
    K4 = '( <" 4 "> ++ ( D ` 3 ) )'
    g4 = B.g(K4, wg4(w, ph, DK(3), B.d3))
    B.call(R, 'tm2fpshn', {'A': LMS['Z2'], 'E': LMS['Z3'], 'K': '3', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('3'): letgk(w, ph, mk, '4', '3', closed(w, ph, 'gamma4', "4 e. Gamma'")), SSS(S): ssid}, [('3', K4, g4)])
    cur, out = R.normalize(N8)
    assert out == [('3', K4), ('6', K2)], out
    P0V = UPS('D', ('3', K4), ('6', K2))
    t1, C1, D1, n1 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, LMS['Z3'], S, s([p0eq], 'eqcomd', '( %s -> %s = ( %s ` 0 ) )' % (ph, P0V, PV)), P0V, PT_('0')))
    # 3. the loop
    GM = {'K': '5', 'F': 'TMrdBra', 'C': CNFL, 'N': S, 'P1': LMS['Z3'], 'A': LMS['Z4'], "A'": BODY_ENTRY, 'A"': LMS['Z5'], 'E': PL(PL('P', 7), 0),
          'L': LGL, 'R': 'R', 'P': PV, 'Y': YFM}
    _GA, _GC = split_imp(stmt('tm2lfes'))
    GT_ = tsub(parse_conj(_GA), GM)
    GC_ = tsub_text(_GC, GM)
    _fl = flat(GT_)
    PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
    PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLL):]
    assert [t for t in _fl if t.startswith('%s : ' % PV)][0] == FTY
    assert [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0] == FCOL, [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
    ex2 = dict(ex)
    ex2[FTY] = fty; ex2[FCOL] = fcol
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (PSI, NLL)
    bj = s([], 'tmimlbi', STMTS12['tmimlbi'])
    jn = s([s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NLL)), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
    cj_ = Ctx(w, pj, (PSI_T, 'j e. ( 0 ..^ %s )' % NLL))
    bnj = cj_['B e. NN0']
    clj = Closure(w, pj, {'B': ('NN0', bnj)})
    clj.leaf(TB('B'), 'NN0', tmbn(w, pj, 'B', bnj))
    ycn = clj.mem(YM, 'NN0')
    yj = s([jn, ycn, s([s([], 'eqidd', '( i = j -> %s = %s )' % (YM, YM)), s([], 'eqid', '%s = %s' % (YFM, YFM))], 'fvmptg',
                        '( ( j e. NN0 /\\ %s e. NN0 ) -> ( %s ` j ) = %s )' % (YM, YFM, YM))], 'syl2anc', '( %s -> ( %s ` j ) = %s )' % (pj, YFM, YM))
    Cb, Db, nb = triple_parts(HOARE_ML)
    tb, _, _, _ = hrrw(w, pj, bj, Cb, Db, nb, neq=s([yj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (pj, YM, YFM)))
    yjn = s([yj, ycn], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (pj, YFM))
    perb = s([yjn, tb], 'jca', '( %s -> %s )' % (pj, PERB))
    ex2[PER] = lift_from(w, PSI, ph, s([perb], 'ralrimiva', '( %s -> %s )' % (PSI, PER)))
    ex2['%s e. Word Word %s' % (LGL, BITS)] = B.lgw
    ex2[WG('R')] = B.rw
    st = Bld(w, ph, c, ex2)(GT_)
    t2 = s([st, w.inst('tm2lfes')], 'syl', '( %s -> %s )' % (ph, GC_))
    C2, D2, n2 = triple_parts(GC_)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, mk['phm'], t1, t2, C1, D1, D2, n1, n2)
    n12 = '( %s + %s )' % (n1, n2)
    NQ_ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
    ssq = s([s([], 'ssrab2', '%s C_ %s' % (NQ_, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, NQ_, S))
    # 4. the tail from ( P' ` NLL )
    PN = PT_(NLL)
    nz = s([B.nll, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLL, DOML))
    fam = c['%s = %s' % (PV, PFM)]
    pvN, SN = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOML, PM, NLL, nz, B.pbst(NLL))
    R2 = B.run(SN)
    RL = '( reverse ` L )'
    LGR = '( encNatGam o. %s )' % RL
    rlw = s([B.ll, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RL))
    lgrw = s([rlw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LGR, BITS))
    pe = pfx_eq(w, ph, B)
    rp = s([pe], 'fveq2d', '( %s -> %s = ( reverse ` L ) )' % (ph, RPF(NLL)))
    e1 = s([rp], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` %s ) )' % (ph, RPF(NLL), RL))
    e2 = s([rlw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, RL, LGR))
    e3 = s([s([e1, e2], 'eqtrd', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, RPF(NLL), LGR))], 'oveq1d',
           '( %s -> %s = ( ( encListB ` %s ) ++ ( D ` 6 ) ) )' % (ph, C6(NLL), LGR))
    v6 = s([SN.vals['6'][1], e3], 'eqtrd', '( %s -> ( %s ` 6 ) = ( ( encListB ` %s ) ++ ( D ` 6 ) ) )' % (ph, PN, LGR))
    rr = s([s([B.ll, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran L )' % (ph, RL)), c[RALB('L', 'B')], w.inst('ssralv')], 'sylc',
           '( %s -> %s )' % (ph, RALB(RL, 'B')))
    rb = s([rlw, B.bn, rr, w.inst('tm2lrnenc')], 'syl3anc', '( %s -> A. w e. ran %s ( # ` w ) <_ B )' % (ph, LGR))
    ENT = '( ( entries ` ( reverse ` %s ) ) ++ %s )' % (LGR, C5L(NLL))
    rlgw = s([lgrw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word Word %s )' % (ph, LGR, BITS))
    eg = s([rlgw, w.inst('tm2lentcl')], 'syl', "( %s -> ( entries ` ( reverse ` %s ) ) e. Word Gamma' )" % (ph, LGR))
    gE = B.g(ENT, wgcat(w, ph, '( entries ` ( reverse ` %s ) )' % LGR, C5L(NLL), eg, B.gam[C5L(NLL)]))
    B.call(R2, 'tmimesb', {'K': '6', 'J': '5', 'I': '2', 'L': LGR, 'R': DK(6), 'B': 'B', 'P': PL('P', 7), 'E': PL(PL('P', 8), 0)},
           {'( %s ` 6 ) = ( ( encListB ` %s ) ++ ( D ` 6 ) )' % (PN, LGR): v6, '%s e. Word Word %s' % (LGR, BITS): lgrw,
            'A. w e. ran %s ( # ` w ) <_ B' % LGR: rb, WG(DK(6)): B.d6}, [('6', DK(6), B.d6), ('5', ENT, gE)], pre=(NQ_, ssq))
    # ENT = ( D ` 5 )
    ef = s([s([], 'encnatgamf', "encNatGam : NN0 --> Word Gamma'")], 'a1i', "( %s -> encNatGam : NN0 --> Word Gamma' )" % ph)
    rc = s([B.ll, ef, w.inst('revco')], 'syl2anc', '( %s -> %s = ( reverse ` %s ) )' % (ph, LGR, LGL))
    rr2 = s([s([rc], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( reverse ` %s ) ) )' % (ph, LGR, LGL)),
             s([B.lgw, w.inst('revrev')], 'syl', '( %s -> ( reverse ` ( reverse ` %s ) ) = %s )' % (ph, LGL, LGL))], 'eqtrd', '( %s -> ( reverse ` %s ) = %s )' % (ph, LGR, LGL))
    e5n = s([s([closed(w, ph, 'swrd00', '( %s substr <. %s , %s >. ) = (/)' % (LGL, NLL, NLL))], 'fveq2d',
              '( %s -> ( encListB ` ( %s substr <. %s , %s >. ) ) = ( encListB ` (/) ) )' % (ph, LGL, NLL, NLL)), closed(w, ph, 'tm2lencb0', '( encListB ` (/) ) = <" 2 ">')],
            'eqtrd', '( %s -> ( encListB ` ( %s substr <. %s , %s >. ) ) = <" 2 "> )' % (ph, LGL, NLL, NLL))
    c5n = s([e5n], 'oveq1d', '( %s -> %s = %s )' % (ph, C5L(NLL), W2R))
    en = s([s([rr2], 'fveq2d', '( %s -> ( entries ` ( reverse ` %s ) ) = ( entries ` %s ) )' % (ph, LGR, LGL)), c5n], 'oveq12d',
           '( %s -> %s = ( ( entries ` %s ) ++ %s ) )' % (ph, ENT, LGL, W2R))
    bc = s([B.lgw, B.rw, w.inst('tm2lencbcc')], 'syl2anc', '( %s -> ( ( encListB ` %s ) ++ R ) = ( ( entries ` %s ) ++ %s ) )' % (ph, LGL, LGL, W2R))
    le_ = s([B.ll, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` L ) = ( encListB ` %s ) )' % (ph, LGL))
    d5 = s([c[DEQ(5, ENCL('L', 'R'))], s([le_], 'oveq1d', '( %s -> %s = ( ( encListB ` %s ) ++ R ) )' % (ph, ENCL('L', 'R'), LGL)), bc], '3eqtrd',
           '( %s -> ( D ` 5 ) = ( ( entries ` %s ) ++ %s ) )' % (ph, LGL, W2R))
    ent = s([en, s([d5], 'eqcomd', '( %s -> ( ( entries ` %s ) ++ %s ) = ( D ` 5 ) )' % (ph, LGL, W2R))], 'eqtrd', '( %s -> %s = ( D ` 5 ) )' % (ph, ENT))
    # 5. isZero 3 2 , the load , dropNum 3
    macn, maclt = B.maccn(NLL)
    B.call(R2, 'tmiizbs', {'K': '3', 'I': '2', 'F': MACC(NLL), 'N': 'B', 'X': DK(3), 'P': PL('P', 8), 'E': LMS['Z6']},
           {'%s e. NN0' % MACC(NLL): macn, '%s < ( 2 ^ B )' % MACC(NLL): maclt, WG(DK(3)): B.d3}, [])
    V1_ = 'if ( %s = 0 , 1o , (/) )' % MACC(NLL)
    V2_ = 'if ( %s = 0 , (/) , 1o )' % MACC(NLL)
    kw = lambda t: dict(fl='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t)
    B.call(R2, 'tm2flg', {'A': LMS['Z6'], 'E': PL(PL('P', 9), 0), 'F': L_NOTF, 'N': NFL(V1_), "N'": NFL(V2_)},
           {LTY(L_NOTF): lset_ty2(w, ph, mk, L_NOTF, kw), SSS(NFL(V1_)): B.ss(NFL(V1_)), SSS(NFL(V2_)): B.ss(NFL(V2_)),
            'A. r e. %s ( %s ` r ) e. %s' % (NFL(V1_), L_NOTF, NFL(V2_)): load_nfl(w, ph, mk, L_NOTF, kw, V1_, V2_, notif_fleq(w, '%s = 0' % MACC(NLL)))}, [])
    Son, old = expose(w, ph, B, R2, '3')
    B.call(R2, 'tmidropnb', {'K': '3', 'F': MACC(NLL), 'N': 'B', 'X': DK(3), 'O': V2_, 'P': PL('P', 9), 'E': 'E'},
           {'%s e. NN0' % MACC(NLL): macn, '%s < ( 2 ^ B )' % MACC(NLL): maclt, WG(DK(3)): B.d3}, [('3', DK(3), B.d3)], on=(Son, old))
    # the final stacks: PN with the updates 6 := D 6 , 5 := ENT = D 5 , 3 := E3 , 3 := D 3 ; PN = PNV
    D0 = triple_D(R2.cur)
    chain = [('3', EWg(MACCL, DK(3))), ('5', W2R), ('6', '( ( encList ` ( reverse ` L ) ) ++ ( D ` 6 ) )')] + list(R2.chain)
    r1, x1 = w.rewrite(D0, {PN: (PNV, pneq)}, ph)
    assert x1 == chain_text('D', chain), '\n%s\n%s' % (x1, chain_text('D', chain))
    r2, x2 = w.rewrite(x1, {ENT: ('( D ` 5 )', ent)}, ph)
    chain2 = [(k, ('( D ` 5 )' if v == ENT else v)) for k, v in chain]
    B.g(EWg(MACCL, DK(3)), ewg_(w, ph, MACCL, s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, MACCL)), DK(3), B.d3))
    B.g(W2R, wgcat(w, ph, '<" 2 ">', 'R', s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph), B.rw))
    B.g('( ( encList ` ( reverse ` L ) ) ++ ( D ` 6 ) )', enclg(w, ph, RL, rlw, DK(6), B.d6))
    for k, v in R2.chain:
        if v not in B.gam:
            B.gam[v] = R2.gam[v]
    nst, outn = stk_normalize(w, ph, mk, 'D', dd, B.ne, chain2, B.gam, N8)
    assert outn == [], outn
    deq = s([r1, r2, nst], '3eqtrd', '( %s -> %s = D )' % (ph, D0))
    t4, C4, D4, n4 = hrrw(w, ph, R2.tri, R2.C0, R2.cur, R2.n, deq=clneq(w, ph, 'E', NFL(V2_), deq, D0, 'D'))
    # the pre of the tail is the loop's post class NQ at PN : the mes call shrank its pre to NQ
    assert C4 == D2, '\n%s\n%s' % (C4, D2)
    t = hrseq(w, ph, mk['phm'], t12, t4, C1, D2, D4, n12, n4)
    n = '( %s + %s )' % (n12, n4)
    # the flag
    fe = s([s([], 'simpr', '( ( %s /\\ A e. ran L ) -> A e. ran L )' % ph)], 'iftrued', '( ( %s /\\ A e. ran L ) -> %s = 1 )' % (ph, MACCL))
    n1_ = s([s([fe], 'eqeq1d', '( ( %s /\\ A e. ran L ) -> ( %s = 0 <-> 1 = 0 ) )' % (ph, MACCL)), s([closed(w, '( %s /\\ A e. ran L )' % ph, 'ax-1ne0', '1 =/= 0')], 'neneqd',
                                                                                                    '( ( %s /\\ A e. ran L ) -> -. 1 = 0 )' % ph)], 'mtbird',
            '( ( %s /\\ A e. ran L ) -> -. %s = 0 )' % (ph, MACCL))
    f1 = s([s([n1_], 'iffalsed', '( ( %s /\\ A e. ran L ) -> %s = 1o )' % (ph, V2_.replace(MACC(NLL), MACCL))),
            s([s([], 'simpr', '( ( %s /\\ A e. ran L ) -> A e. ran L )' % ph)], 'iftrued', '( ( %s /\\ A e. ran L ) -> %s = 1o )' % (ph, FLAG_ML))], 'eqtr4d',
           '( ( %s /\\ A e. ran L ) -> %s = %s )' % (ph, V2_.replace(MACC(NLL), MACCL), FLAG_ML))
    pn_ = '( %s /\\ -. A e. ran L )' % ph
    fe2 = s([s([], 'simpr', '( %s -> -. A e. ran L )' % pn_)], 'iffalsed', '( %s -> %s = 0 )' % (pn_, MACCL))
    f2 = s([s([fe2], 'iftrued', '( %s -> %s = (/) )' % (pn_, V2_.replace(MACC(NLL), MACCL))),
            s([s([], 'simpr', '( %s -> -. A e. ran L )' % pn_)], 'iffalsed', '( %s -> %s = (/) )' % (pn_, FLAG_ML))], 'eqtr4d',
           '( %s -> %s = %s )' % (pn_, V2_.replace(MACC(NLL), MACCL), FLAG_ML))
    fl = s([f1, f2], 'pm2.61dan', '( %s -> %s = %s )' % (ph, V2_.replace(MACC(NLL), MACCL), FLAG_ML))
    # V2_ has MACC( NLL ) : first MACC( NLL ) = MACCL
    m_eq = s([s([s([pfx_eq(w, ph, B)], 'rneqd', '( %s -> ran ( L prefix %s ) = ran L )' % (ph, NLL))], 'eleq2d', '( %s -> ( A e. ran ( L prefix %s ) <-> A e. ran L ) )' % (ph, NLL))],
             'ifbid', '( %s -> %s = %s )' % (ph, MACC(NLL), MACCL))
    v2eq = s([s([m_eq], 'eqeq1d', '( %s -> ( %s = 0 <-> %s = 0 ) )' % (ph, MACC(NLL), MACCL))], 'ifbid', '( %s -> %s = %s )' % (ph, V2_, V2_.replace(MACC(NLL), MACCL)))
    t, C, D, n = cls_to(w, ph, (t, C1, D4, n), V2_, FLAG_ML, s([v2eq, fl], 'eqtrd', '( %s -> %s = %s )' % (ph, V2_, FLAG_ML)))
    # the bound
    SUM_ = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NLL, YFM)
    pj2 = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLL)
    jn2 = s([s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj2, NLL)), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj2)
    yj2 = s([jn2, s([cl.mem(YM, 'NN0')], 'adantr', '( %s -> %s e. NN0 )' % (pj2, YM)), s([s([], 'eqidd', '( i = j -> %s = %s )' % (YM, YM)), s([], 'eqid', '%s = %s' % (YFM, YFM))],
                                                                                          'fvmptg', '( ( j e. NN0 /\\ %s e. NN0 ) -> ( %s ` j ) = %s )' % (YM, YFM, YM))], 'syl2anc',
             '( %s -> ( %s ` j ) = %s )' % (pj2, YFM, YM))
    se = s([s([yj2], 'oveq1d', '( %s -> ( ( %s ` j ) + 2 ) = ( %s + 2 ) )' % (pj2, YFM, YM))], 'sumeq2dv', '( %s -> %s = sum_ j e. ( 0 ..^ %s ) ( %s + 2 ) )' % (ph, SUM_, NLL, YM))
    fc = s([s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NLL)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NLL)), cl.mem('( %s + 2 )' % YM, 'CC'), w.inst('fsumconst')], 'syl2anc',
           '( %s -> sum_ j e. ( 0 ..^ %s ) ( %s + 2 ) = ( ( # ` ( 0 ..^ %s ) ) x. ( %s + 2 ) ) )' % (ph, NLL, YM, NLL, YM))
    hf = s([s([s([B.nll, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (ph, NLL, NLL)), B.lg], 'eqtrd', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (ph, NLL, NL))],
           'oveq1d', '( %s -> ( ( # ` ( 0 ..^ %s ) ) x. ( %s + 2 ) ) = ( %s x. ( %s + 2 ) ) )' % (ph, NLL, YM, NL, YM))
    seq_ = s([se, fc, hf], '3eqtrd', '( %s -> %s = ( %s x. ( %s + 2 ) ) )' % (ph, SUM_, NL, YM))
    cl.leaf(SUM_, 'NN0', s([seq_, cl.mem('( %s x. ( %s + 2 ) )' % (NL, YM), 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, SUM_)))
    lgrl = s([s([rlw, ef, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, LGR, RL)), s([B.ll, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, RL, NL))],
            'eqtrd', '( %s -> ( # ` %s ) = %s )' % (ph, LGR, NL))
    cl.leaf('( # ` %s )' % LGR, 'NN0', s([lgrl, B.nl], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (ph, LGR)))
    tb64 = s([B.bn, s([num.nn0(w, 64)], 'a1i', '( %s -> ; 6 4 e. NN0 )' % ph), s([num.le_lit(w, '; 6 4', '; 6 4')], 'a1i', '( %s -> ; 6 4 <_ ; 6 4 )' % ph), w.inst('tmblin')],
             'syl3anc', '( %s -> ( ; 6 4 x. ( B + 2 ) ) <_ %s )' % (ph, TB('B')))
    le = linarith(w, ph, [seq_, lgrl, tb64, cl.ge0(NL), cl.ge0('B')], '%s <_ %s' % (n, MLSC), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, MLSC, cl.mem(MLSC, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def pfx_eq(w, ph, B):
    """( ph -> ( L prefix NLL ) = L )"""
    s = w.s
    return s([s([B.lg], 'oveq2d', '( %s -> ( L prefix %s ) = ( L prefix %s ) )' % (ph, NLL, NL)), s([B.ll, w.inst('pfxid')], 'syl', '( %s -> ( L prefix %s ) = L )' % (ph, NL))],
             'eqtrd', '( %s -> ( L prefix %s ) = L )' % (ph, NLL))


def tmimlsb():
    lab = 'tmimlsb'
    T = numtree(TREE_MLS)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` memList_le_B ` at the machine ( ` x y s t z = 5 1 2 3 6 ` ): with the list ` l ` on 5 and the number '
               '` a ` on 1 the flag ends up ` a e. l ` , every stack restored (~ tmimlsl at the family of the accumulator), within '
               '` ( # l + 1 ) 6 B b ` steps (the bound is six times Lean\'s: the callees are the ` B ` forms; T12-blueprint '
               'section 3).')
    s = w.s
    c = Ctx(w, ph, T)
    eq = s([], 'eqid', '%s = %s' % (PFM, PFM))
    t, cc = inst(w, ph, 'tmimlsl', {PV: PFM}, Bld(w, ph, c, {'%s = %s' % (PFM, PFM): s([eq], 'a1i', '( %s -> %s = %s )' % (ph, PFM, PFM))}))
    assert cc == CONCL_MLS, '\n%s\n%s' % (cc, CONCL_MLS)
    finish(w, t, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
