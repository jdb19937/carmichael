"""T9: prodLF at the machine (PrimList.lean ` prodLF_le_B ` ) on its installation predicate TMIprl.

  tmienc1     the stack word of ` pushNum x 1 `
  tmprlstep   the product of a prefix one entry longer (Lean ` take_succ ` , ` prod_append ` )
  tmprllt     Lean ` take_prod_lt ` : a prefix product is below ` 2 ^ ( ( # L + 1 ) b + 1 ) `
  tmiprli     one entry of the ` forEntries ` loop: ` mulC c w x s t ; moveEntry x w s ` at ` ProdInv `
  tmiprlt     the frame: the family's typing and ` c ` column, the prologue ` copyList ; pushNum w 1 `
  tmiprll     ~ tm2fprl assembled ( P' a letter)
  tmiprlb     prodLF_le_B

    MM_DB=sorties/t9.mm python3 tools/gen/t9_e_prl.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import num

SEL = sys.argv[1:]
Z0B = '<. 1 , (/) >.'
ST_ENC1 = "( X e. Word Gamma' -> ( ( encNatGam ` 1 ) ++ ( <\" 4 \"> ++ X ) ) = ( <\" %s \"> ++ ( <\" 4 \"> ++ X ) ) )" % B1
PR = lambda j: '( 1st ` ( ProdL ` ( L prefix %s ) ) )' % j
ST_STEP = '( ( L e. Word NN0 /\\ J e. ( 0 ..^ ( # ` L ) ) ) -> %s = ( ( L ` J ) x. %s ) )' % (PR('( J + 1 )'), PR('J'))
MB = '( ( ( ( # ` L ) + 1 ) x. B ) + 1 )'
ST_LT = ('( ( ( L e. Word NN0 /\\ B e. NN0 /\\ A. a e. ran L a < ( 2 ^ B ) ) /\\ J e. ( 0 ... ( # ` L ) ) ) -> %s < ( 2 ^ %s ) )'
         % (PR('J'), MB))


def tmienc1():
    lab = 'tmienc1'
    ph = "X e. Word Gamma'"
    w = W(lab, 'The stack word of ` pushNum x 1 ` (Lean ` encodeNatGamma 1 ++ comma :: _ ` ): the one bit of ` 1 ` , then the '
               'terminator.')
    s = w.s
    c0 = closed(w, ph, '0nn0', '0 e. NN0')
    a1 = s([c0, w.inst('encnatsuc')], 'syl', '( %s -> ( encodeNat ` ( 0 + 1 ) ) = ( incBits ` ( encodeNat ` 0 ) ) )' % ph)
    a2 = s([closed(w, ph, '0p1e1', '( 0 + 1 ) = 1')], 'fveq2d', '( %s -> ( encodeNat ` ( 0 + 1 ) ) = ( encodeNat ` 1 ) )' % ph)
    a3 = s([closed(w, ph, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'fveq2d', '( %s -> ( incBits ` ( encodeNat ` 0 ) ) = ( incBits ` (/) ) )' % ph)
    e1 = s([s([s([a2, a1], 'eqtr3d', '( %s -> ( encodeNat ` 1 ) = ( incBits ` ( encodeNat ` 0 ) ) )' % ph), a3], 'eqtrd',
              '( %s -> ( encodeNat ` 1 ) = ( incBits ` (/) ) )' % ph), closed(w, ph, 'incbitsnil', '( incBits ` (/) ) = <" 1o ">')],
           'eqtrd', '( %s -> ( encodeNat ` 1 ) = <" 1o "> )' % ph)
    g1 = s([closed(w, ph, '1nn0', '1 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 1 ) = ( inclBool o. ( encodeNat ` 1 ) ) )' % ph)
    g1b = s([g1, s([e1], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 1 ) ) = ( inclBool o. <" 1o "> ) )' % ph)], 'eqtrd',
            '( %s -> ( encNatGam ` 1 ) = ( inclBool o. <" 1o "> ) )' % ph)
    o2 = closed(w, ph, '1oel2o', '1o e. 2o')
    ff = closed(w, ph, 'inclboolf', "inclBool : 2o --> Gamma'")
    h1 = s([o2, ff, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" 1o "> ) = <" ( inclBool ` 1o ) "> )' % ph)
    h1b = s([h1, s([s([o2, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = %s )' % (ph, B1))], 's1eqd',
                   '( %s -> <" ( inclBool ` 1o ) "> = <" %s "> )' % (ph, B1))], 'eqtrd', '( %s -> ( inclBool o. <" 1o "> ) = <" %s "> )' % (ph, B1))
    g = s([g1b, h1b], 'eqtrd', '( %s -> ( encNatGam ` 1 ) = <" %s "> )' % (ph, B1))
    w.qed([g], 'oveq1d', ST_ENC1)
    return w.run()


def tmprlstep():
    lab = 'tmprlstep'
    ph = '( L e. Word NN0 /\\ J e. ( 0 ..^ ( # ` L ) ) )'
    w = W(lab, 'The product of the prefix of length ` J + 1 ` is the entry ` L ` J ` times the product of the prefix of length '
               '` J ` (Lean ` take_succ ` , ` List.prod_append ` in ` prodBody_runs ` ).')
    s = w.s
    lw = s([], 'simpl', '( %s -> L e. Word NN0 )' % ph)
    jj = s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` L ) ) )' % ph)
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... ( # ` L ) ) )' % ph)
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... ( # ` L ) ) )' % ph)
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> J e. NN0 )' % ph)
    P1, P0 = '( L prefix ( J + 1 ) )', '( L prefix J )'
    out = {}
    for P_, jv, jm in ((P1, '( J + 1 )', j1), (P0, 'J', jz)):
        pw = s([lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, P_))
        sp = s([pw, w.inst('prodlspec')], 'syl', '( %s -> ( 1st ` ( ProdL ` %s ) ) = prod_ i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i ) )' % (ph, P_, P_, P_))
        ln = s([lw, jm, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, P_, jv))
        fz = s([ln], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ %s ) )' % (ph, P_, jv))
        pe = s([fz], 'prodeq1d', '( %s -> prod_ i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i ) = prod_ i e. ( 0 ..^ %s ) ( %s ` i ) )' % (ph, P_, P_, jv, P_))
        pa = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, jv)
        fv = s([Lft(w, pa, ph, lw), Lft(w, pa, ph, jm), s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pa, jv)), w.inst('pfxfv')], 'syl3anc',
               '( %s -> ( %s ` i ) = ( L ` i ) )' % (pa, P_))
        p2 = s([fv], 'prodeq2dv', '( %s -> prod_ i e. ( 0 ..^ %s ) ( %s ` i ) = prod_ i e. ( 0 ..^ %s ) ( L ` i ) )' % (ph, jv, P_, jv))
        out[jv] = s([s([sp, pe], 'eqtrd', '( %s -> ( 1st ` ( ProdL ` %s ) ) = prod_ i e. ( 0 ..^ %s ) ( %s ` i ) )' % (ph, P_, jv, P_)), p2],
                    'eqtrd', '( %s -> ( 1st ` ( ProdL ` %s ) ) = prod_ i e. ( 0 ..^ %s ) ( L ` i ) )' % (ph, P_, jv))
    ju = s([jn, w.inst('nn0uz' if False else 'elnn0uz')], 'sylib', '( %s -> J e. ( ZZ>= ` 0 ) )' % ph)
    fs = s([ju, w.inst('fzosplitsn')], 'syl', '( %s -> ( 0 ..^ ( J + 1 ) ) = ( ( 0 ..^ J ) u. { J } ) )' % ph)
    q1 = s([fs], 'prodeq1d', '( %s -> prod_ i e. ( 0 ..^ ( J + 1 ) ) ( L ` i ) = prod_ i e. ( ( 0 ..^ J ) u. { J } ) ( L ` i ) )' % ph)
    nf1 = s([], 'nfv', 'F/ i %s' % ph)
    nf2 = s([], 'nfcv', 'F/_ i ( L ` J )')
    fin = s([s([], 'fzofi', '( 0 ..^ J ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ J ) e. Fin )' % ph)
    jv_ = s([jn], 'elexd', '( %s -> J e. _V )' % ph)
    nel = s([s([], 'fzonel', '-. J e. ( 0 ..^ J )')], 'a1i', '( %s -> -. J e. ( 0 ..^ J ) )' % ph)
    pa = '( %s /\\ i e. ( 0 ..^ J ) )' % ph
    iL = s([s([], 'simpr', '( %s -> i e. ( 0 ..^ J ) )' % pa), s([s([Lft(w, pa, ph, jz), w.inst('elfzuz3')], 'syl',
                                                                     '( %s -> ( # ` L ) e. ( ZZ>= ` J ) )' % pa), w.inst('fzoss2')], 'syl',
                                                                  '( %s -> ( 0 ..^ J ) C_ ( 0 ..^ ( # ` L ) ) )' % pa)], 'sselda' if False else 'id', '') if False else None
    ssf = s([s([jz, w.inst('elfzuz3')], 'syl', '( %s -> ( # ` L ) e. ( ZZ>= ` J ) )' % ph), w.inst('fzoss2')], 'syl',
            '( %s -> ( 0 ..^ J ) C_ ( 0 ..^ ( # ` L ) ) )' % ph)
    iL = s([Lft(w, pa, ph, ssf), s([], 'simpr', '( %s -> i e. ( 0 ..^ J ) )' % pa)], 'sseldd', '( %s -> i e. ( 0 ..^ ( # ` L ) ) )' % pa)
    lin_ = s([Lft(w, pa, ph, lw), iL, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` i ) e. NN0 )' % pa)
    lic = s([lin_], 'nn0cnd', '( %s -> ( L ` i ) e. CC )' % pa)
    fvj = s([], 'fveq2', '( i = J -> ( L ` i ) = ( L ` J ) )')
    ljn = s([lw, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` J ) e. NN0 )' % ph)
    ljc = s([ljn], 'nn0cnd', '( %s -> ( L ` J ) e. CC )' % ph)
    sp = s([nf1, nf2, fin, jv_, nel, lic, fvj, ljc], 'fprodsplitsn',
           '( %s -> prod_ i e. ( ( 0 ..^ J ) u. { J } ) ( L ` i ) = ( prod_ i e. ( 0 ..^ J ) ( L ` i ) x. ( L ` J ) ) )' % ph)
    pcl = s([fin, lic], 'fprodcl', '( %s -> prod_ i e. ( 0 ..^ J ) ( L ` i ) e. CC )' % ph)
    mc = s([pcl, ljc], 'mulcomd', '( %s -> ( prod_ i e. ( 0 ..^ J ) ( L ` i ) x. ( L ` J ) ) = ( ( L ` J ) x. prod_ i e. ( 0 ..^ J ) ( L ` i ) ) )' % ph)
    r1 = s([s([s([out['( J + 1 )'], q1], 'eqtrd', '( %s -> %s = prod_ i e. ( ( 0 ..^ J ) u. { J } ) ( L ` i ) )' % (ph, PR('( J + 1 )'))), sp], 'eqtrd',
              '( %s -> %s = ( prod_ i e. ( 0 ..^ J ) ( L ` i ) x. ( L ` J ) ) )' % (ph, PR('( J + 1 )'))), mc], 'eqtrd',
           '( %s -> %s = ( ( L ` J ) x. prod_ i e. ( 0 ..^ J ) ( L ` i ) ) )' % (ph, PR('( J + 1 )')))
    r2 = s([out['J']], 'oveq2d', '( %s -> ( ( L ` J ) x. %s ) = ( ( L ` J ) x. prod_ i e. ( 0 ..^ J ) ( L ` i ) ) )' % (ph, PR('J')))
    w.qed([r1, r2], 'eqtr4d', ST_STEP)
    return w.run()


def tmprllt():
    lab = 'tmprllt'
    ph = '( ( L e. Word NN0 /\\ B e. NN0 /\\ A. a e. ran L a < ( 2 ^ B ) ) /\\ J e. ( 0 ... ( # ` L ) ) )'
    w = W(lab, 'Lean\'s ` take_prod_lt ` : the product of a prefix of a list of numbers below ` 2 ^ b ` is below '
               '` 2 ^ ( ( # L + 1 ) b + 1 ) ` (~ tplprodle ).')
    s = w.s
    c = Ctx(w, ph, (('L e. Word NN0', 'B e. NN0', 'A. a e. ran L a < ( 2 ^ B )'), 'J e. ( 0 ... ( # ` L ) )'))
    lw, bn, ral, jz = c['L e. Word NN0'], c['B e. NN0'], c['A. a e. ran L a < ( 2 ^ B )'], c['J e. ( 0 ... ( # ` L ) )']
    P0 = '( L prefix J )'
    pw = s([lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, P0))
    ln = s([lw, jz, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = J )' % (ph, P0))
    rs = s([lw, jz, w.inst('pfxres')], 'syl2anc', '( %s -> %s = ( L |` ( 0 ..^ J ) ) )' % (ph, P0))
    rr = s([rs], 'rneqd', '( %s -> ran %s = ran ( L |` ( 0 ..^ J ) ) )' % (ph, P0))
    rss = s([rr, s([s([], 'rnresss', 'ran ( L |` ( 0 ..^ J ) ) C_ ran L')], 'a1i', '( %s -> ran ( L |` ( 0 ..^ J ) ) C_ ran L )' % ph)],
            'eqsstrd', '( %s -> ran %s C_ ran L )' % (ph, P0))
    ralp = s([rss, ral, w.inst('ssralv')], 'sylc', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (ph, P0))
    cb = s([s([], 'breq1', '( a = p -> ( a < ( 2 ^ B ) <-> p < ( 2 ^ B ) ) )')], 'cbvralvw',
           '( A. a e. ran %s a < ( 2 ^ B ) <-> A. p e. ran %s p < ( 2 ^ B ) )' % (P0, P0))
    ralq = s([ralp, cb], 'sylib', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (ph, P0))
    le = s([pw, bn, ralq, w.inst('tplprodle')], 'syl3anc', '( %s -> %s <_ ( 2 ^ ( ( # ` %s ) x. B ) ) )' % (ph, PR('J'), P0))
    le2 = s([le, s([s([ln], 'oveq1d', '( %s -> ( ( # ` %s ) x. B ) = ( J x. B ) )' % (ph, P0))], 'oveq2d',
                   '( %s -> ( 2 ^ ( ( # ` %s ) x. B ) ) = ( 2 ^ ( J x. B ) ) )' % (ph, P0))], 'breqtrd', '( %s -> %s <_ ( 2 ^ ( J x. B ) ) )' % (ph, PR('J')))
    jn = s([jz, w.inst('elfznn0')], 'syl', '( %s -> J e. NN0 )' % ph)
    jl = s([jz, w.inst('elfzle2')], 'syl', '( %s -> J <_ ( # ` L ) )' % ph)
    cl = Closure(w, ph, {'J': ('NN0', jn), 'B': ('NN0', bn)})
    cl.leaf('( # ` L )', 'NN0', s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph))
    jb = s([cl.mem('J', 'RR'), cl.mem('( # ` L )', 'RR'), cl.mem('B', 'RR'), s([bn], 'nn0ge0d', '( %s -> 0 <_ B )' % ph), jl], 'lemul1ad',
           '( %s -> ( J x. B ) <_ ( ( # ` L ) x. B ) )' % ph)
    lt = linarith(w, ph, [jb, cl.ge0('B')], '( J x. B ) < %s' % MB, closure=cl, products=True)
    e2 = s([s([closed(w, ph, '2re', '2 e. RR'), cl.mem('( J x. B )', 'ZZ'), cl.mem(MB, 'ZZ')], '3jca',
              '( %s -> ( 2 e. RR /\\ ( J x. B ) e. ZZ /\\ %s e. ZZ ) )' % (ph, MB)),
            s([closed(w, ph, '1lt2', '1 < 2'), lt], 'jca', '( %s -> ( 1 < 2 /\\ ( J x. B ) < %s ) )' % (ph, MB)), w.inst('ltexp2a')], 'syl2anc',
           '( %s -> ( 2 ^ ( J x. B ) ) < ( 2 ^ %s ) )' % (ph, MB))
    pn = s([s([pw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, P0)), w.inst('xp1st')], 'syl',
           '( %s -> %s e. NN0 )' % (ph, PR('J')))
    t1 = s([s([closed(w, ph, '2nn', '2 e. NN'), cl.mem('( J x. B )', 'NN0'), w.inst('nnexpcl')], 'syl2anc',
              '( %s -> ( 2 ^ ( J x. B ) ) e. NN )' % ph)], 'nnred', '( %s -> ( 2 ^ ( J x. B ) ) e. RR )' % ph)
    t2 = s([s([closed(w, ph, '2nn', '2 e. NN'), cl.mem(MB, 'NN0'), w.inst('nnexpcl')], 'syl2anc',
              '( %s -> ( 2 ^ %s ) e. NN )' % (ph, MB))], 'nnred', '( %s -> ( 2 ^ %s ) e. RR )' % (ph, MB))
    w.qed([s([pn], 'nn0red', '( %s -> %s e. RR )' % (ph, PR('J'))), t1, t2, le2, e2], 'lelttrd', ST_LT)
    return w.run()


# ------------------------------------------------------------ the loop's family (Lean ` ProdInv ` )
LG = '( encNatGam o. L )'
NLG = '( # ` %s )' % LG
DOM = '( 0 ... %s )' % NLG
EB = lambda k: '( encListB ` ( %s substr <. %s , %s >. ) )' % (LG, k, NLG)
ENCB = lambda k: '( %s ++ ( D ` I ) )' % EB(k)
PB = lambda k: UP(UP('D', 'I', ENCB(k)), 'J', EWg(PR(k), '( D ` J )'))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
PV = "P'"
PSI_T = (TREE_PRL, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
YB = '( 2 x. ( TMB ` %s ) )' % MB
UB = '( ( ( ( ( # ` L ) + 1 ) x. ( TMB ` B ) ) + 1 ) + 1 )'
LMP = FRAGS['prl'].lmap()
MP = {'P1': LMP['P1'], 'A': LMP['A'], "A'": LMP["A'"], 'A"': LMP['A"'], 'E': LMP['Q3'], "E'": 'E', 'P0': LMP['C0'],
      'K': 'I', 'F': RDBRA, 'C': CNFL, 'F"': PID, 'N': S, 'O': S, "N'": S, 'L': LG, 'R': '( D ` I )', 'Y': YB, 'P': PV,
      'U': UB, 'D': 'D'}
_GA, _GC = split_imp(stmt('tm2fprl'))
GTREE = tsub(parse_conj(_GA), MP)
GCONCL = tsub_text(_GC, MP)
PER = [t for t in flat(GTREE) if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in flat(GTREE) if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in flat(GTREE) if t.startswith('A. j e. ( 0 ... ')][0]
PROT = [t for t in flat(GTREE) if t.startswith('( { ( inl ` %s ) }' % LMP['C0'])][0]
ST_I = '( ( %s /\\ j e. ( 0 ..^ %s ) ) -> %s )' % (PSI, NLG, PERB)
ST_T = '( %s -> ( ( %s /\\ %s ) /\\ %s ) )' % (PSI, FTY, FCOL, PROT)
ST_L = '( %s -> %s )' % (PSI, GCONCL)


class Prl(Base):
    def __init__(self, w, ph, T):
        Base.__init__(self, w, ph, T, K5P, 'prl')
        c, s = self.c, w.s
        self.lw, self.bn, self.ral = c['L e. Word NN0'], c['B e. NN0'], c[RALB('L')]
        self.lgw = s([self.lw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([self.lw, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc',
                    '( %s -> %s = ( # ` L ) )' % (ph, NLG))
        self.cl = Closure(w, ph, {'B': ('NN0', self.bn)})
        self.cl.leaf('( # ` L )', 'NN0', s([self.lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph))

    def prn(self, k, kz):
        """( ph -> PR( k ) e. NN0 ) from kz : k e. ( 0 ... NLG )"""
        w, ph, s = self.w, self.ph, self.w.s
        pw = s([self.lw, w.inst('pfxcl')], 'syl', '( %s -> ( L prefix %s ) e. Word NN0 )' % (ph, k))
        return s([s([pw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` ( L prefix %s ) ) e. ( NN0 X. NN0 ) )' % (ph, k)),
                  w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, PR(k)))

    def pbst(self, k, kz):
        """the Stacks of PB( k )"""
        w, ph, s = self.w, self.ph, self.w.s
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g1 = self.g(ENCB(k), wgcat(w, ph, EB(k), '( D ` I )', eb, self.S0.vals['I'][2]))
        g2 = self.g(EWg(PR(k), '( D ` J )'), ewg_(w, ph, PR(k), self.prn(k, kz), '( D ` J )', self.S0.vals['J'][2]))
        return self.S0.upd('I', ENCB(k), g1).upd('J', EWg(PR(k), '( D ` J )'), g2)


def tmiprli():
    lab = 'tmiprli'
    T = (PSI_T, 'j e. ( 0 ..^ %s )' % NLG)
    ph = cj(T)
    w = W(lab, 'One entry of Lean\'s ` prodLF ` loop at the machine (` prodBody_runs ` ): at the family of ` ProdInv ` , '
               '` mulC c w x s t ` (~ tmimulb ) multiplies the entry into the accumulator and ` moveEntry x w s ` (~ tmime ) '
               'moves the product back, within ` 2 B M ` steps, ` M = ( # L + 1 ) b + 1 ` .')
    B = Prl(w, ph, T)
    s, c, mk, cl = w.s, B.c, B.mk, B.cl
    jj = c['j e. ( 0 ..^ %s )' % NLG]
    jL = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ ( # ` L ) ) )' % (ph, NLG))], 'eleqtrd',
           '( %s -> j e. ( 0 ..^ ( # ` L ) ) )' % ph)
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> ( j + 1 ) e. %s )' % (ph, DOM))
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j', jz))
    PT = '( %s ` j )' % PV
    # ( PT ` I ) = EW( ( L ` j ) , ENCB( j + 1 ) )
    J1 = '( j + 1 )'
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.lw, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ ( # ` L ) ) --> NN0 )' % ph), jL, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` ( L ` j ) ) )' % (ph, LG))
    ljn = s([B.lw, jL, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` j ) e. NN0 )' % ph)
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    di = B.S0.vals['I'][2]
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = encw(w, ph, '( L ` j )', ljn)
    ca1 = s([egj if False else s([lgj, egj], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG)), g4, di, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ ( D ` I ) ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` I ) ) ) )'
            % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, di, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` I ) ) = ( <" 4 "> ++ %s ) )' % (ph, EB(J1), ENCB(J1)))
    r1 = s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ ( D ` I ) ) )' % (ph, ENCB('j'), LG, EB(J1)))
    r2 = s([r1, ca1], 'eqtrd', '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` I ) ) ) )' % (ph, ENCB('j'), LG, EB(J1)))
    r3 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ ( D ` I ) ) ) = %s )'
           % (ph, LG, EB(J1), EWg('( L ` j )', ENCB(J1))))
    iv = s([SJ.vals['I'][1], s([r2, r3], 'eqtrd', '( %s -> %s = %s )' % (ph, ENCB('j'), EWg('( L ` j )', ENCB(J1))))], 'eqtrd',
           '( %s -> ( %s ` I ) = %s )' % (ph, PT, EWg('( L ` j )', ENCB(J1))))
    g_eb1 = B.g(ENCB(J1), wgcat(w, ph, EB(J1), '( D ` I )', eb1, di))
    # the numbers
    mbn = cl.mem(MB, 'NN0')
    FG = '( ( L ` j ) x. %s )' % PR('j')
    prj = B.prn('j', jz)
    lt_g = s([s([B.lw, B.bn, B.ral], '3jca', '( %s -> ( L e. Word NN0 /\\ B e. NN0 /\\ %s ) )' % (ph, RALB('L'))),
              s([jz, s([B.lg], 'oveq2d', '( %s -> %s = ( 0 ... ( # ` L ) ) )' % (ph, DOM))], 'eleqtrd', '( %s -> j e. ( 0 ... ( # ` L ) ) )' % ph),
              w.inst('tmprllt')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ph, PR('j'), MB))
    lrn = s([s([B.lw, w.inst('wrdfn')], 'syl', '( %s -> L Fn ( 0 ..^ ( # ` L ) ) )' % ph), jL, w.inst('fnfvelrn')], 'syl2anc',
            '( %s -> ( L ` j ) e. ran L )' % ph)
    ltb = s([lrn, B.ral, s([], 'breq1', '( a = ( L ` j ) -> ( a < ( 2 ^ B ) <-> ( L ` j ) < ( 2 ^ B ) ) )')], 'rspcdva' if False else 'rspcdv',
            '( %s -> ( L ` j ) < ( 2 ^ B ) )' % ph) if False else None
    ltb = s([s([], 'breq1', '( a = ( L ` j ) -> ( a < ( 2 ^ B ) <-> ( L ` j ) < ( 2 ^ B ) ) )'), lrn, B.ral], 'rspcdva',
            '( %s -> ( L ` j ) < ( 2 ^ B ) )' % ph)
    cl.leaf('( # ` L )', 'NN0', s([B.lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph))
    bm = linarith(w, ph, [cl.ge0('B'), cl.ge0('( # ` L )')], 'B <_ %s' % MB, closure=cl, products=True)
    bmz = s([cl.mem('B', 'ZZ'), cl.mem(MB, 'ZZ'), bm], 'eluz2' if False else 'id', '') if False else None
    bmu = s([s([cl.mem('B', 'ZZ'), cl.mem(MB, 'ZZ'), bm], '3jca', '( %s -> ( B e. ZZ /\\ %s e. ZZ /\\ B <_ %s ) )' % (ph, MB, MB)),
             w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` B ) )' % (ph, MB))
    p2 = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), bmu, w.inst('leexp2a')], 'syl3anc',
           '( %s -> ( 2 ^ B ) <_ ( 2 ^ %s ) )' % (ph, MB))
    tB = s([s([closed(w, ph, '2nn', '2 e. NN'), B.bn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ B ) e. NN )' % ph)], 'nnred',
           '( %s -> ( 2 ^ B ) e. RR )' % ph)
    tM = s([s([closed(w, ph, '2nn', '2 e. NN'), mbn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, MB))], 'nnred',
           '( %s -> ( 2 ^ %s ) e. RR )' % (ph, MB))
    lt_f = s([s([ljn], 'nn0red', '( %s -> ( L ` j ) e. RR )' % ph), tB, tM, ltb, p2], 'ltletrd', '( %s -> ( L ` j ) < ( 2 ^ %s ) )' % (ph, MB))
    # the Run
    fgn = s([ljn, prj], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, FG))
    dk = B.S0.vals['K'][2]
    g_fk = B.g(EWg(FG, '( D ` K )'), ewg_(w, ph, FG, fgn, '( D ` K )', dk))
    g_fj = B.g(EWg(FG, '( D ` J )'), ewg_(w, ph, FG, fgn, '( D ` J )', B.S0.vals['J'][2]))
    R = B.run(SJ)
    B.call(R, 'tmimulb', {'K': 'I', 'J': 'J', 'I': 'K', "I'": "I'", 'I"': 'I"', 'F': '( L ` j )', 'G': PR('j'), 'N': MB,
                          'X': ENCB(J1), 'Y': '( D ` J )', 'P': PL('P', 7), 'E': LMP['X1']},
           {'( %s ` I ) = %s' % (PT, EWg('( L ` j )', ENCB(J1))): iv, '( L ` j ) e. NN0': ljn, '%s e. NN0' % PR('j'): prj,
            '%s e. NN0' % MB: mbn, '( L ` j ) < ( 2 ^ %s )' % MB: lt_f, '%s < ( 2 ^ %s )' % (PR('j'), MB): lt_g},
           [('K', EWg(FG, '( D ` K )'), g_fk), ('I', ENCB(J1), g_eb1), ('J', '( D ` J )', B.gam['( D ` J )'])])
    S1 = R.S
    WFG = '( encNatGam ` %s )' % FG
    B.call(R, 'tmime', {'K': 'K', 'J': 'J', 'I': "I'", 'W': WFG, 'X': '( D ` K )', 'P': PL('P', 8), 'E': LMP['A"']},
           {WRD(WFG, BITS): engb(w, ph, FG, fgn), '( %s ` K ) = %s' % (S1.D, EWg(FG, '( D ` K )')): S1.vals['K'][1]},
           [('K', '( D ` K )', B.gam['( D ` K )']), ('J', EWg(FG, '( D ` J )'), g_fj)])
    e, nrm, out2 = renorm(w, ph, B, R, [('I', ENCB('j')), ('J', EWg(PR('j'), '( D ` J )'))], ['K', 'I', 'J', "I'", 'I"'], PT=PT, pv=pvj)
    assert out2 == [('I', ENCB(J1)), ('J', EWg(FG, '( D ` J )'))], out2
    # FG = PR( j + 1 )
    st = s([B.lw, jL, w.inst('tmprlstep')], 'syl2anc', '( %s -> %s = %s )' % (ph, PR(J1), FG))
    r_, nrm2 = w.rewrite(nrm, {FG: (PR(J1), s([st], 'eqcomd', '( %s -> %s = %s )' % (ph, FG, PR(J1))))}, ph)
    assert nrm2 == PB(J1), nrm2
    B.pbst(J1, j1)
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1, j1))
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, R.cur and chain_text(PT, R.chain) if False else triple_D(R.cur), PB(J1))), pv1],
            'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, triple_D(R.cur), PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LMP['A"'], S, deq, triple_D(D), '( %s ` %s )' % (PV, J1)))
    # the bound: TMB M + ( 2 # W + 4 ) <_ 2 TMB M
    lt1 = s([s([B.lw, B.bn, B.ral], '3jca', '( %s -> ( L e. Word NN0 /\\ B e. NN0 /\\ %s ) )' % (ph, RALB('L'))),
             s([j1, s([B.lg], 'oveq2d', '( %s -> %s = ( 0 ... ( # ` L ) ) )' % (ph, DOM))], 'eleqtrd', '( %s -> ( j + 1 ) e. ( 0 ... ( # ` L ) ) )' % ph),
             w.inst('tmprllt')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ph, PR(J1), MB))
    ltfg = s([st, lt1], 'eqbrtrrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, FG, MB))
    LW = '( # ` %s )' % WFG
    cl.leaf(LW, 'NN0', s([s([fgn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, WFG)), w.inst('lencl')], 'syl',
                         '( %s -> %s e. NN0 )' % (ph, LW)))
    lw_ = s([s([fgn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` %s ) ) )' % (ph, LW, FG)),
             s([fgn, mbn, ltfg, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` %s ) ) <_ %s )' % (ph, FG, MB))],
            'eqbrtrd', '( %s -> %s <_ %s )' % (ph, LW, MB))
    TM = '( TMB ` %s )' % MB
    tmn = s([s([mbn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TM))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TM))
    cl.leaf(TM, 'NN0', tmn)
    cl.leaf(MB, 'NN0', mbn)
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([mbn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, MB, TM))
    me = nlinarith(w, ph, [lw_, qd, cl.ge0(MB), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ %s' % (LW, TM), closure=cl, atoms=[MB, LW, TM])
    le = linarith(w, ph, [me], '%s <_ %s' % (n, YB), closure=cl, atoms=[LW, TM])
    hrle(w, ph, mk['phm'], t, C, D, n, YB, cl.mem(YB, 'NN0'), le, qed=True)
    return w.run()


def triple_D(Dcls):
    """the stack term of a class text C( A , N , D )"""
    tail = Dcls.rsplit(' X. { ', 1)[1]
    assert tail.endswith(' } ) )')
    return tail[:-len(' } ) )')]



def pb0(w, ph, B):
    """( ph -> PB( 0 ) = UPD( UPD( D , I , ( encList L ) ++ ( D ` I ) ) , J , <" B1 "> ++ ( <" 4 "> ++ ( D ` J ) ) ) )"""
    s = w.s
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le = s([B.lw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` L ) = ( encListB ` %s ) )' % (ph, LG))
    e1 = s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le], 'eqtr4d',
           '( %s -> %s = ( encList ` L ) )' % (ph, EB('0')))
    e1b = s([e1], 'oveq1d', '( %s -> %s = ( ( encList ` L ) ++ ( D ` I ) ) )' % (ph, ENCB('0')))
    p0 = s([s([s([], 'pfx00', '( L prefix 0 ) = (/)')], 'fveq2i', '( ProdL ` ( L prefix 0 ) ) = ( ProdL ` (/) )'),
            s([], 'prodl0', '( ProdL ` (/) ) = <. 1 , 0 >.')], 'eqtri', '( ProdL ` ( L prefix 0 ) ) = <. 1 , 0 >.')
    p1 = s([s([p0], 'fveq2i', '%s = ( 1st ` <. 1 , 0 >. )' % PR('0')),
            s([s([], '1ex', '1 e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. 1 , 0 >. ) = 1')], 'eqtri', '%s = 1' % PR('0'))
    e2 = s([s([s([s([p1], 'fveq2i', '( encNatGam ` %s ) = ( encNatGam ` 1 )' % PR('0'))], 'oveq1i',
                 '%s = %s' % (EWg(PR('0'), '( D ` J )'), EWg('1', '( D ` J )')))], 'a1i',
              '( %s -> %s = %s )' % (ph, EWg(PR('0'), '( D ` J )'), EWg('1', '( D ` J )'))),
            s([B.S0.vals['J'][2], w.inst('tmienc1')], 'syl', '( %s -> %s = ( <" %s "> ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (ph, EWg('1', '( D ` J )'), B1))],
           'eqtrd', '( %s -> %s = ( <" %s "> ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (ph, EWg(PR('0'), '( D ` J )'), B1))
    r, x = w.rewrite(PB('0'), {ENCB('0'): ('( ( encList ` L ) ++ ( D ` I ) )', e1b), EWg(PR('0'), '( D ` J )'): ('( <" %s "> ++ ( <" 4 "> ++ ( D ` J ) ) )' % B1, e2)}, ph)
    return r, x


def tmiprlt():
    lab = 'tmiprlt'
    ph = PSI
    w = W(lab, 'The frame of Lean\'s ` prodLF ` loop at the machine: the family of ` ProdInv ` is a stack family whose ` c ` '
               'column is the remaining list, and the prologue ` copyList x c s t ; pushNum w 1 ` (~ tmilcpyb , ~ tm2fpshn ) '
               'enters it at ` 0 ` .')
    s = w.s
    B = Prl(w, ph, PSI_T)
    c, mk = B.c, B.mk
    fam = c['%s = %s' % (PV, PF)]
    # the typing, under ph0 /\ k e. DOM
    ph0 = cj(TREE_PRL)
    TK = (TREE_PRL, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Prl(w, pk, TK)
    kz = Bk.c['k e. %s' % DOM]
    Sk = Bk.pbst('k', kz)
    fm = s([Sk.memb, s([], 'eqid', '%s = %s' % (PF, PF))], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    fm2 = s([fm], 'adantr', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)), fm2],
            'mpbird', '( %s -> %s )' % (ph, FTY))
    # the c column
    TJ = (PSI_T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Prl(w, pj, TJ)
    jz = Bj.c['j e. %s' % DOM]
    pvj, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', jz, Bj.pbst('j', jz))
    col = s([SJ.vals['I'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    # the prologue
    kw = B.S0.vals['K']
    kv = c['( D ` K ) = %s' % ENCL('L', 'R')]
    S0 = Stacks(w, ph, mk, 'D', B.dd, B.ne, dict(B.S0.vals))
    S0.vals['K'] = (ENCL('L', 'R'), kv, enclg(w, ph, 'L', B.lw, 'R', c[WG('R')]))
    R = B.run(S0)
    EL = '( ( encList ` L ) ++ ( D ` I ) )'
    gel = B.g(EL, enclg(w, ph, 'L', B.lw, '( D ` I )', B.S0.vals['I'][2]))
    B.call(R, 'tmilcpyb', {'K': 'K', 'J': 'I', 'I': "I'", "I'": 'I"', 'L': 'L', 'R': 'R', 'B': 'B', 'P': PL('P', 6), 'E': PL('P', 0)},
           {}, [('I', EL, gel)])
    J4 = '( <" 4 "> ++ ( D ` J ) )'
    g4 = B.g(J4, wg4(w, ph, '( D ` J )', B.S0.vals['J'][2]))
    B.call(R, 'tm2fpshn', {'A': PL('P', 0), 'E': PL('P', 1), 'K': 'J', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('J'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['J']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('J')))},
           [('J', J4, g4)])
    J41 = '( <" %s "> ++ %s )' % (B1, J4)
    bg = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, B1))
    g41 = B.g(J41, wgcat(w, ph, '<" %s ">' % B1, J4, s([bg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, B1)), g4))
    B.call(R, 'tm2fpshn', {'A': PL('P', 1), 'E': PL('P', 2), 'K': 'J', 'Z': B1, 'N': S},
           {'%s e. %s' % (B1, GX('J')): s([bg, mk['k']['J']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, B1, GX('J')))},
           [('J', J41, g41)])
    e, nrm, out2 = renorm(w, ph, B, R, [], ['K', 'I', 'J', "I'", 'I"'])
    assert out2 == [('I', EL), ('J', J41)], out2
    r0, x0 = pb0(w, ph, B)
    assert x0 == nrm, (x0, nrm)
    nlg = s([B.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
    z0 = s([nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0', z0))
    D0 = triple_D(R.cur)
    deq = s([s([e, s([r0], 'eqcomd', '( %s -> %s = %s )' % (ph, nrm, PB('0')))], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB('0'))), pv0],
            'eqtr4d', '( %s -> %s = ( %s ` 0 ) )' % (ph, D0, PV))
    t, C, D, n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, LMP['P1'], S, deq, D0, '( %s ` 0 )' % PV))
    assert n == UB, n
    tri = t
    w.qed([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), tri], 'jca', ST_T)
    return w.run()


def tmiprll():
    lab = 'tmiprll'
    ph = PSI
    w = W(lab, 'Lean\'s ` prodLF_le_B ` at the machine up to the bound: ~ tm2fprl at the family of ` ProdInv ` ( ` P\' ` a '
               'letter), the entries by ~ tmiprli , the frame by ~ tmiprlt .')
    s = w.s
    B = Prl(w, ph, PSI_T)
    B.deep('prl', 1)
    c, mk, cl = B.c, B.mk, B.cl
    ex = dict(B.ex)
    fr = s([], 'tmiprlt', ST_T)
    ex[FTY] = s([s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))], 'simprd', '( %s -> %s )' % (ph, FCOL))
    ex[PROT] = s([fr], 'simprd', '( %s -> %s )' % (ph, PROT))
    ex[PER] = s([s([], 'tmiprli', ST_I)], 'ralrimiva', '( %s -> %s )' % (ph, PER))
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex[WG('( D ` I )')] = B.S0.vals['I'][2]
    MBv = MB
    tmn = s([s([cl.mem(MB, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` %s ) e. NN )' % (ph, MB))], 'nnnn0d',
            '( %s -> ( TMB ` %s ) e. NN0 )' % (ph, MB))
    cl.leaf('( TMB ` %s )' % MB, 'NN0', tmn)
    tbn = s([s([B.bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
    cl.leaf('( TMB ` B )', 'NN0', tbn)
    ex['%s e. NN0' % YB] = cl.mem(YB, 'NN0')
    ex['%s e. NN0' % UB] = cl.mem(UB, 'NN0')
    NQ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
    ssq = s([s([], 'ssrab2', '%s C_ %s' % (NQ, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, NQ, S))
    POPI_ = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (S, PID, S)
    ex['A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (NQ, PID, S)] = s([ssq, ex[POPI_], w.inst('ssralv')], 'sylc',
                                                                         '( %s -> A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s )' % (ph, NQ, PID, S))
    st = Bld(w, ph, c, ex)(GTREE)
    w.qed([st, w.inst('tm2fprl')], 'syl', ST_L)
    return w.run()


def tmiprlb():
    lab = 'tmiprlb'
    ph = cj(TREE_PRL)
    w = W(lab, 'Lean\'s ` prodLF_le_B ` at the machine: wherever ` prodLF x w c s t ` is installed, with a list ` l ` of '
               'numbers below ` 2 ^ b ` on ` x ` , the product ` ( prodL l ).1 ` is pushed on ` w ` , every other stack '
               'restored, within ` ( ( prodL l ).2 + 1 ) B ( 2 ( # l + 1 ) b + 4 ) ` steps (~ tmiprll at the family).')
    s = w.s
    B = Prl(w, ph, TREE_PRL)
    c, mk, cl = B.c, B.mk, B.cl
    eq = s([], 'eqid', '%s = %s' % (PF, PF))
    t, cc = inst(w, ph, 'tmiprll', {PV: PF}, Bld(w, ph, c, {'%s = %s' % (PF, PF): s([eq], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))}))
    C, D, n = triple_parts(cc)
    nlg = s([B.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
    nz = s([nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    SN = B.pbst(NLG, nz)
    xex = s([SN.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PB(NLG)))
    v = mval(w, ph, 'k', DOM, PB, NLG, nz, xex)
    D0 = triple_D(D)
    r1, x1 = w.rewrite(D0, {'( %s ` %s )' % (PF, NLG): (PB(NLG), v)}, ph)
    chi = [('I', ENCB(NLG)), ('J', EWg(PR(NLG), '( D ` J )')), ('I', '( D ` I )')]
    assert x1 == chain_text('D', chi), x1
    nst, out2 = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chi, B.gam, ['K', 'I', 'J', "I'", 'I"'])
    assert out2 == [('J', EWg(PR(NLG), '( D ` J )'))], out2
    pl = s([s([B.lg], 'oveq2d', '( %s -> ( L prefix %s ) = ( L prefix ( # ` L ) ) )' % (ph, NLG)), s([B.lw, w.inst('pfxid')], 'syl',
                                                                                                  '( %s -> ( L prefix ( # ` L ) ) = L )' % ph)],
           'eqtrd', '( %s -> ( L prefix %s ) = L )' % (ph, NLG))
    pr = s([s([pl], 'fveq2d', '( %s -> ( ProdL ` ( L prefix %s ) ) = ( ProdL ` L ) )' % (ph, NLG))], 'fveq2d', '( %s -> %s = %s )' % (ph, PR(NLG), PRL('L')))
    FIN = UP('D', 'J', EWg(PRL('L'), '( D ` J )'))
    r2, x2 = w.rewrite(UP('D', 'J', EWg(PR(NLG), '( D ` J )')), {PR(NLG): (PRL('L'), pr)}, ph)
    assert x2 == FIN
    deq = s([s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, UP('D', 'J', EWg(PR(NLG), '( D ` J )')))), r2], 'eqtrd',
            '( %s -> %s = %s )' % (ph, D0, FIN))
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, deq, D0, FIN))
    # the bound
    TM = '( TMB ` %s )' % MB
    mbn = cl.mem(MB, 'NN0')
    tmn = s([s([mbn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TM))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TM))
    cl.leaf(TM, 'NN0', tmn)
    tbn = s([s([B.bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
    cl.leaf('( TMB ` B )', 'NN0', tbn)
    cl.leaf(NLG, 'NN0', nlg)
    ARG = '( ( ( 2 x. ( ( # ` L ) + 1 ) ) x. B ) + 4 )'
    TA = '( TMB ` %s )' % ARG
    sc = s([closed(w, ph, '1nn0', '1 e. NN0'), mbn, w.inst('tplbscale')], 'syl2anc',
           '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( TMB ` ( ( ( 1 + 1 ) x. %s ) + ( 2 x. 1 ) ) ) )' % (ph, TM, MB))
    ae = lineq(w, ph, '( ( ( 1 + 1 ) x. %s ) + ( 2 x. 1 ) )' % MB, ARG, closure=cl, products=True)
    sc2 = s([sc, s([ae], 'fveq2d', '( %s -> ( TMB ` ( ( ( 1 + 1 ) x. %s ) + ( 2 x. 1 ) ) ) = %s )' % (ph, MB, TA))], 'eqtrd',
            '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = %s )' % (ph, TM, TA))
    e8 = s([], 'id', '') if False else None
    import num as _num
    c8 = s([_num.mul_lits(w, '( ( 1 + 1 ) ^ 3 )', '8') if False else s([], 'eqid', '8 = 8')], 'id', '') if False else None
    cl.leaf(TA, 'NN0', s([s([cl.mem(ARG, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TA))], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TA)))
    pc = s([B.lw, w.inst('prodlcost')], 'syl', '( %s -> ( 2nd ` ( ProdL ` L ) ) = ( # ` L ) )' % ph)
    cl.leaf('( 2nd ` ( ProdL ` L ) )', 'NN0', s([s([s([B.lw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` L ) e. ( NN0 X. NN0 ) )' % ph),
                                                   w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( ProdL ` L ) ) e. NN0 )' % ph)], 'id', '') if False else
            s([s([B.lw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` L ) e. ( NN0 X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl',
              '( %s -> ( 2nd ` ( ProdL ` L ) ) e. NN0 )' % ph))
    bm = linarith(w, ph, [cl.ge0('B'), cl.ge0('( # ` L )')], 'B <_ %s' % MB, closure=cl, products=True)
    mono = s([B.bn, mbn, bm, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` B ) <_ %s )' % (ph, TM))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([mbn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc', '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, MB, TM))
    t16 = nlinarith(w, ph, [qd, cl.ge0(MB)], '; 1 6 <_ %s' % TM, closure=cl, atoms=[MB, TM])
    # n with NLG replaced by # L
    rn, n2 = w.rewrite(n, {NLG: ('( # ` L )', B.lg)}, ph)
    e8 = s([s([s([], '1p1e2', '( 1 + 1 ) = 2')], 'oveq1i', '( ( 1 + 1 ) ^ 3 ) = ( 2 ^ 3 )'), s([], 'cu2', '( 2 ^ 3 ) = 8')], 'eqtri',
           '( ( 1 + 1 ) ^ 3 ) = 8')
    ta = s([s([s([e8], 'oveq1i', '( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( 8 x. %s )' % (TM, TM))], 'a1i',
              '( %s -> ( ( ( 1 + 1 ) ^ 3 ) x. %s ) = ( 8 x. %s ) )' % (ph, TM, TM)), sc2], 'eqtr3d', '( %s -> ( 8 x. %s ) = %s )' % (ph, TM, TA))
    RHS2 = '( ( ( # ` L ) + 1 ) x. ( 8 x. %s ) )' % TM
    rr, x_ = w.rewrite(RHS2, {'( 8 x. %s )' % TM: (TA, ta), '( ( # ` L ) + 1 )': ('( ( 2nd ` ( ProdL ` L ) ) + 1 )',
                                                                                     s([pc], 'eqcomd', '( %s -> ( # ` L ) = ( 2nd ` ( ProdL ` L ) ) )' % ph) and
                                                                                     s([s([pc], 'eqcomd', '( %s -> ( # ` L ) = ( 2nd ` ( ProdL ` L ) ) )' % ph)],
                                                                                       'oveq1d', '( %s -> ( ( # ` L ) + 1 ) = ( ( 2nd ` ( ProdL ` L ) ) + 1 ) )' % ph))}, ph)
    assert x_ == PRLB, x_
    cl.leaf('( # ` L )', 'NN0', s([B.lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph))
    f1 = s([cl.mem('( TMB ` B )', 'RR'), cl.mem(TM, 'RR'), cl.mem('( # ` L )', 'RR'), cl.ge0('( # ` L )'), mono], 'lemul2ad',
           '( %s -> ( ( # ` L ) x. ( TMB ` B ) ) <_ ( ( # ` L ) x. %s ) )' % (ph, TM))
    one = linarith(w, ph, [t16], '1 <_ %s' % TM, closure=cl)
    f2 = s([closed(w, ph, '1re', '1 e. RR'), cl.mem(TM, 'RR'), cl.mem('( # ` L )', 'RR'), cl.ge0('( # ` L )'), one], 'lemul2ad',
           '( %s -> ( ( # ` L ) x. 1 ) <_ ( ( # ` L ) x. %s ) )' % (ph, TM))
    le2 = linarith(w, ph, [f1, f2, mono, t16, cl.ge0('( # ` L )')], '%s <_ %s' % (n2, RHS2), closure=cl, products=True)
    le = s([s([rn, rr], 'breq12d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, RHS2, n2, PRLB)) if False else
            s([s([rn], 'breq1d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, RHS2, n2, RHS2)), s([rr], 'breq2d',
                                                                                              '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n, RHS2, n, PRLB))],
              'bitr3d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (ph, n2, RHS2, n, PRLB)), le2], 'mpbid', '( %s -> %s <_ %s )' % (ph, n, PRLB))
    hrle(w, ph, mk['phm'], t, C, D, n, PRLB, cl.mem(PRLB, 'NN0'), le, qed=True)
    return w.run()


STMTS = {'tmienc1': ST_ENC1, 'tmprlstep': ST_STEP, 'tmprllt': ST_LT}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
