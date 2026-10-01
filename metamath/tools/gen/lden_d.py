"""Sortie LDEN, part d: the representative systems (Lean card_repIndex_le): ldencls ldenri.

    MM_DB=sorties/lden.mm MM_ENGINE=mmatch python3 tools/gen/lden_d.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ldenlib import *
import ldenlib as LL
from ef4_g import elrab_unpack, elrab_pack
from ef3lib import elrab_
from lden_a import sc_facts, num8
from zr_k import ri_facts, cell_facts
import lin as _lin
_lin.MAXPOW = 16
_lin.MAXDEG = 16

only = sys.argv[1:]
S = STATEMENTS
XPY = '( Y X. ( 0 ... %s ) )' % QP
FCC = FC('C')
FCO = tsub(FCC, {'r': 'o'})                       # the class over RIO(P) (ldenfam's $d F r)
CELLE = lambda Z: CELL('( 1st ` %s )' % Z, '( 2nd ` %s )' % Z)


def repparts(w, A, P):
    """the HREP antecedent: closure (N T S LD), scale facts, HZD, the family pieces"""
    F = {}
    F['nN'] = P['N e. NN']; F['ysub'] = P['Y C_ %s' % DB()]; F['yfin'] = P['Y e. Fin']
    F['sr'] = P['S e. RR']; F['s39'] = P['( ; 3 9 / ; 5 0 ) <_ S']; F['s1'] = P['S <_ 1']
    F['tr'] = P['T e. RR']; F['t2'] = P['2 <_ T']; F['l40'] = P[H40]; F['hgd'] = P[HGD]
    F.update(sc_facts(w, A, F['nN'], F['tr'], F['t2']))
    F['hz'] = ap(w, A, 'ldenhz', [J(w, A, J(w, A, F['nN'], J(w, A, F['tr'], F['t2'])), F['l40'])], HZD)
    F['hsig'] = P[HSIG]
    c = Closure(w, A, {'N': ('NN', F['nN']), 'T': [('RR', F['tr']), ('ge0', F['t0'])], 'S': ('RR', F['sr']), DSC: [('RR', F['dr'])], LD: [('RR', F['lr'])]})
    c.leaf(DSC, 'RR+', dst(w, A, [F['dr'], linarith(w, A, [F['d4']], '0 < %s' % DSC, closure=c)], 'elrpd', '%s e. RR+' % DSC))
    c.leaf(LD, 'RR', F['lr']); c.have(LD, 'gt0', F['lp']); c.have(LD, 'ge0', linarith(w, A, [F['l1']], '0 <_ %s' % LD, closure=c))
    c.leaf(PW, 'RR+', c.mem(PW, 'RR+'))
    c.leaf('CTau', 'NN', ctau_nn(w, A))
    c.leaf(B2, 'RR', c.mem(B2, 'RR'))
    F['b20'] = c.ge0(B2)
    # RI(P) finite
    xfin = dst(w, A, [F['yfin'], dst(w, A, [], 'fzfid', '( 0 ... %s ) e. Fin' % QP), w.inst('xpfi')], 'syl2anc', '%s e. Fin' % XPY)
    F['rfin'] = dst(w, A, [xfin, w.s([w.s([], 'ssrab2', '%s C_ %s' % (RI('P'), XPY))], 'a1i', '( %s -> %s C_ %s )' % (A, RI('P'), XPY))], 'ssfid', '%s e. Fin' % RI('P'))
    return c, F


def gen_cls():
    w = W('ldencls', 'The per-class step of Lean ` card_repIndex_le ` : one thinning class of a parity system, with a representative chosen in every cell ( ~ ac6sfi ), is a ` 1 ` -spaced family of box zeros ( ~ ldenthin ) with the ` chi_0 ` height clause, so ~ ldenfam counts it (the class over the ` o ` -bound index set ~ ldenrio ).')
    A = ante('ldencls'); P = parts(w, A)
    c, F = repparts(w, A, P)
    # FCC finite, FCC = FCO
    ffin = dst(w, A, [F['rfin'], w.s([w.s([], 'ssrab2', '%s C_ %s' % (FCC, RI('P')))], 'a1i', '( %s -> %s C_ %s )' % (A, FCC, RI('P')))], 'ssfid', '%s e. Fin' % FCC)
    rio = w.s([w.s([], 'ldenrio', S['ldenrio'])], 'rabeqi', '%s = %s' % (FCC, FCO))
    # every cell of the class is nonempty: A. x e. FCC E. y e. CC y e. CELL ( x )
    Ax = '( %s /\\ x e. %s )' % (A, FCC)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, FCC))
    xri = w.s([xin, w.inst('elrabi')], 'syl', '( %s -> x e. %s )' % (Ax, RI('P')))
    xxp, cne, _, _, _, _ = ri_facts(w, Ax, xri, 'x')
    CX_ = CELLE('x')
    ex1 = dst(w, Ax, [cne, w.s([], 'n0', '( %s =/= (/) <-> E. y y e. %s )' % (CX_, CX_))], 'sylib', 'E. y y e. %s' % CX_)
    Axy = '( %s /\\ y e. %s )' % (Ax, CX_)
    yin = w.s([], 'simpr', '( %s -> y e. %s )' % (Axy, CX_))
    fy = cell_facts(w, Axy, yin, 'y', '( 1st ` x )', '( 2nd ` x )', lift(w, F['sr'], Axy), lift(w, F['tr'], Axy))
    ycc = dst(w, Axy, [fy['cc'], yin], 'jca', '( y e. CC /\\ y e. %s )' % CX_)
    ex2 = w.s([w.s([ycc], 'ex', '( %s -> ( y e. %s -> ( y e. CC /\\ y e. %s ) ) )' % (Ax, CX_, CX_))], 'eximdv', '( %s -> ( E. y y e. %s -> E. y ( y e. CC /\\ y e. %s ) ) )' % (Ax, CX_, CX_))
    ex3 = dst(w, Ax, [ex1, ex2], 'mpd', 'E. y ( y e. CC /\\ y e. %s )' % CX_)
    ex4 = dst(w, Ax, [ex3, w.s([], 'df-rex', '( E. y e. CC y e. %s <-> E. y ( y e. CC /\\ y e. %s ) )' % (CX_, CX_))], 'sylibr', 'E. y e. CC y e. %s' % CX_)
    al = dst(w, A, [ex4], 'ralrimiva', 'A. x e. %s E. y e. CC y e. %s' % (FCC, CX_))
    PS = '( f ` x ) e. %s' % CX_
    a6 = w.s([J(w, A, ffin, al), w.s([w.s([], 'eleq1', '( y = ( f ` x ) -> ( y e. %s <-> %s ) )' % (CX_, PS))], 'ac6sfi', '( ( %s e. Fin /\\ A. x e. %s E. y e. CC y e. %s ) -> E. f ( f : %s --> CC /\\ A. x e. %s %s ) )' % (FCC, FCC, CX_, FCC, FCC, PS))],
             'syl', '( %s -> E. f ( f : %s --> CC /\\ A. x e. %s %s ) )' % (A, FCC, FCC, PS))
    # under the selector f
    HF_ = '( f : %s --> CC /\\ A. x e. %s %s )' % (FCC, FCC, PS)
    Af = '( %s /\\ %s )' % (A, HF_)
    cf = Ctx(w, Af)
    ff = cf([], 'simprl', 'f : %s --> CC' % FCC); fal = cf([], 'simprr', 'A. x e. %s %s' % (FCC, PS))
    Lf = lambda st: lift(w, st, Af)
    # ldenfam at F := FCO , K := 1st , Y := f
    SUB = {'F': FCO, 'K': '1st', 'Y': 'f'}
    HFLp = tsub(HFL, SUB)
    ffo = cf([cf.a1(rio, '%s = %s' % (FCC, FCO)), Lf(ffin)], 'eqeltrrd', '%s e. Fin' % FCO)
    Aa = '( %s /\\ a e. %s )' % (Af, FCO)
    ca = Ctx(w, Aa)
    ain = ca([], 'simpr', 'a e. %s' % FCO)
    ainc = ca([ain, ca.a1(w.s([rio], 'eleq2i', '( a e. %s <-> a e. %s )' % (FCC, FCO)), '( a e. %s <-> a e. %s )' % (FCC, FCO))], 'mpbird', 'a e. %s' % FCC)
    ari = ca([ainc, w.inst('elrabi')], 'syl', 'a e. %s' % RI('P'))
    _, acls, _ = elrab_unpack(w, Aa, 'e', RI('P'), '%s = C' % CLS('e'), 'a', ainc)
    axp, _, _, _, a1y, _ = ri_facts(w, Aa, ari, 'a')
    kad = ca([lift(w, F['ysub'], Aa), a1y], 'sseldd', '( 1st ` a ) e. %s' % DB())
    fa_, _ = inst_forall(w, Aa, lift(w, fal, Aa), 'x', PS, 'a', ainc)
    FA = '( f ` a )'
    fa = cell_facts(w, Aa, fa_, FA, '( 1st ` a )', '( 2nd ` a )', lift(w, F['sr'], Aa), lift(w, F['tr'], Aa))
    ne1 = ca([fa['zp']], 'simpld', '%s =/= 1' % FA); zer = ca([fa['zp']], 'simprd', '( ( N DChrLF ( 1st ` a ) ) ` %s ) = 0' % FA)
    ptsb = J(w, Aa, J(w, Aa, fa['re1'], fa['re2']), J(w, Aa, fa['im'], J(w, Aa, ne1, zer)))
    PTSBa = tsub(tsub(PTSB, {'a': 'a'}), SUB)
    assert body(w, ptsb, Aa) == PTSBa, (body(w, ptsb, Aa)[:200], PTSBa[:200])
    # the height clause from HGD at e := a, z := ( f ` a )
    HG = HGD[len('A. e e. %s ' % RI('P')):]
    hga, new = inst_forall(w, Aa, lift(w, F['hgd'], Aa), 'e', HG, 'a', ari)
    A1 = '( %s /\\ ( 1st ` a ) = %s )' % (Aa, ZG)
    alz = w.s([lift(w, hga, A1), w.s([], 'simpr', '( %s -> ( 1st ` a ) = %s )' % (A1, ZG))], 'mpd', '( %s -> A. z e. %s %s <_ ( abs ` ( Im ` z ) ) )' % (A1, CELLE('a'), LD))
    hz_, _ = inst_forall(w, A1, alz, 'z', '%s <_ ( abs ` ( Im ` z ) )' % LD, FA, lift(w, fa_, A1))
    ht = w.s([hz_], 'ex', '( %s -> ( ( 1st ` a ) = %s -> %s <_ ( abs ` ( Im ` %s ) ) ) )' % (Aa, ZG, LD, FA))
    ptsa = J(w, Aa, ptsb, ht)
    ptsl = dst(w, Af, [ptsa], 'ralrimiva', tsub(PTSL, SUB))
    kal = dst(w, Af, [kad], 'ralrimiva', 'A. a e. %s ( 1st ` a ) e. %s' % (FCO, DB()))
    yal = dst(w, Af, [fa['cc']], 'ralrimiva', 'A. a e. %s ( f ` a ) e. CC' % FCO)
    # SEPY on the class: ldenthin
    Aab = '( %s /\\ ( a e. %s /\\ b e. %s ) )' % (Af, FCO, FCO)
    cab = Ctx(w, Aab)
    ain2 = cab([], 'simprl', 'a e. %s' % FCO); bin2 = cab([], 'simprr', 'b e. %s' % FCO)

    def memb(Z, zin):
        zc = cab([zin, cab.a1(w.s([rio], 'eleq2i', '( %s e. %s <-> %s e. %s )' % (Z, FCC, Z, FCO)), '( %s e. %s <-> %s e. %s )' % (Z, FCC, Z, FCO))], 'mpbird', '%s e. %s' % (Z, FCC))
        zri = cab([zc, w.inst('elrabi')], 'syl', '%s e. %s' % (Z, RI('P')))
        _, zcls, _ = elrab_unpack(w, Aab, 'e', RI('P'), '%s = C' % CLS('e'), Z, zc)
        fz, _ = inst_forall(w, Aab, lift(w, fal, Aab), 'x', PS, Z, zc)
        return zri, zcls, fz
    ari2, acls2, fa2 = memb('a', ain2); bri2, bcls2, fb2 = memb('b', bin2)
    HYP = '( a =/= b /\\ ( 1st ` a ) = ( 1st ` b ) )'
    A2 = '( %s /\\ %s )' % (Aab, HYP)
    hab = w.s([], 'simpr', '( %s -> %s )' % (A2, HYP))
    ne = dst(w, A2, [hab], 'simpld', 'a =/= b'); e1 = dst(w, A2, [hab], 'simprd', '( 1st ` a ) = ( 1st ` b )')
    L2 = lambda st: lift(w, st, A2)
    cls_eq = dst(w, A2, [L2(acls2), eqc(w, A2, L2(bcls2))], 'eqtrd', '%s = %s' % (CLS('a'), CLS('b')))
    TA = ante_of(tsub(S['ldenthin'], {'Q': 'a', 'R': 'b', 'A': '( f ` a )', 'B': '( f ` b )'}))
    th = ap(w, A2, 'ldenthin', [J(w, A2, J(w, A2, J(w, A2, J(w, A2, L2(Lf(F['nN'])), L2(Lf(F['sr']))), L2(Lf(F['tt']))), J(w, A2, L2(ari2), L2(bri2))),
                                J(w, A2, J(w, A2, J(w, A2, e1, ne), cls_eq), J(w, A2, L2(fa2), L2(fb2))))], TA[1])
    assert body(w, J(w, A2, J(w, A2, J(w, A2, J(w, A2, L2(Lf(F['nN'])), L2(Lf(F['sr']))), L2(Lf(F['tt']))), J(w, A2, L2(ari2), L2(bri2))), J(w, A2, J(w, A2, J(w, A2, e1, ne), cls_eq), J(w, A2, L2(fa2), L2(fb2)))), A2) == TA[0]
    sep1 = w.s([th], 'ex', '( %s -> ( %s -> 1 <_ ( abs ` ( ( Im ` ( f ` a ) ) - ( Im ` ( f ` b ) ) ) ) ) )' % (Aab, HYP))
    sepl = dst(w, Af, [sep1], 'ralrimivva', tsub(SEPY, SUB))
    hfl = J(w, Af, J(w, Af, J(w, Af, Lf(J(w, A, F['nN'], J(w, A, F['tr'], F['t2']))), Lf(F['l40'])), Lf(F['hsig'])), J(w, Af, J(w, Af, ffo, J(w, Af, kal, yal)), J(w, Af, ptsl, sepl)))
    assert body(w, hfl, Af) == HFLp, (body(w, hfl, Af)[:300], HFLp[:300])
    fam = ap(w, Af, 'ldenfam', [hfl], tsub(concl('ldenfam'), SUB))
    hcc = dst(w, Af, [cf.a1(w.s([rio], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (FCC, FCO)), '( # ` %s ) = ( # ` %s )' % (FCC, FCO)), fam], 'eqbrtrd', '( # ` %s ) <_ %s' % (FCC, B2))
    fin_ = w.s([a6, hcc], 'exlimddv', '( %s -> %s )' % (A, concl('ldencls')))
    return fin(w, fin_)


def gen_ri():
    w = W('ldenri', '**Lean ` card_repIndex_le ` **: one parity system, thinned into ` Q1 <_ 2 log D ` classes ( ~ ldenfib ), each counted by ~ ldencls .')
    A = ante('ldenri'); P = parts(w, A)
    c, F = repparts(w, A, P)
    fib = ap(w, A, 'ldenfib', [J(w, A, F['yfin'], J(w, A, F['nN'], F['tt']))], concl('ldenfib'))
    FZ = '( 0 ..^ %s )' % Q1
    Ac = '( %s /\\ c e. %s )' % (A, FZ)
    cls = w.s([w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('ldencls')], 'syl', '( %s -> %s )' % (A, concl('ldencls')))
    # ldencls at C := c
    CC_ = tsub(concl('ldencls'), {'C': 'c'})
    clsc = w.s([w.s([], 'id', '( %s -> %s )' % (A, A)), w.inst('ldencls')], 'syl', '( %s -> %s )' % (A, CC_))
    clsc2 = lift(w, clsc, Ac)
    ffin = w.s([lift(w, F['rfin'], Ac), w.s([w.s([], 'ssrab2', '%s C_ %s' % (FC('c'), RI('P')))], 'a1i', '( %s -> %s C_ %s )' % (Ac, FC('c'), RI('P')))], 'ssfid', '( %s -> %s e. Fin )' % (Ac, FC('c')))
    hfc = w.s([w.s([ffin, w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (Ac, FC('c')))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (Ac, FC('c')))
    fzf = w.s([w.s([], 'fzofi', '%s e. Fin' % FZ)], 'a1i', '( %s -> %s e. Fin )' % (A, FZ))
    fl = dst(w, A, [fzf, hfc, lift(w, c.mem(B2, 'RR'), Ac), clsc2], 'fsumle', 'sum_ c e. %s ( # ` %s ) <_ sum_ c e. %s %s' % (FZ, FC('c'), FZ, B2))
    fc = dst(w, A, [fzf, c.mem(B2, 'CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ c e. %s %s = ( ( # ` %s ) x. %s )' % (FZ, B2, FZ, B2))
    q1 = ap(w, A, 'ldenq1', [J(w, A, F['nN'], F['tt'])], concl('ldenq1'))
    q1n = dst(w, A, [q1], 'simpld', '%s e. NN' % Q1); q1hi = dst(w, A, [dst(w, A, [q1], 'simprd', top_and(concl('ldenq1'))[1])], 'simprd', '%s <_ ( %s + 2 )' % (Q1, LD))
    hfz = w.s([dst(w, A, [q1n], 'nnnn0d', '%s e. NN0' % Q1), w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (A, FZ, Q1))
    c.leaf(Q1, 'NN', q1n)
    q2 = linarith(w, A, [q1hi, F['l40']], '%s <_ ( 2 x. %s )' % (Q1, LD), closure=c)
    m = dst(w, A, [c.mem(Q1, 'RR'), c.mem('( 2 x. %s )' % LD, 'RR'), c.mem(B2, 'RR'), F['b20'], q2], 'lemul1ad', '( %s x. %s ) <_ ( ( 2 x. %s ) x. %s )' % (Q1, B2, LD, B2))
    sc = dst(w, A, [fc, dst(w, A, [hfz], 'oveq1d', '( ( # ` %s ) x. %s ) = ( %s x. %s )' % (FZ, B2, Q1, B2))], 'eqtrd', 'sum_ c e. %s %s = ( %s x. %s )' % (FZ, B2, Q1, B2))
    SF = 'sum_ c e. %s ( # ` %s )' % (FZ, FC('c'))
    sfr = dst(w, A, [fzf, hfc], 'fsumrecl', '%s e. RR' % SF)
    t1 = dst(w, A, [fl, sc], 'breqtrd', '%s <_ ( %s x. %s )' % (SF, Q1, B2))
    t2 = dst(w, A, [sfr, c.mem('( %s x. %s )' % (Q1, B2), 'RR'), c.mem('( ( 2 x. %s ) x. %s )' % (LD, B2), 'RR'), t1, m], 'letrd', '%s <_ ( ( 2 x. %s ) x. %s )' % (SF, LD, B2))
    fin_ = dst(w, A, [fib, t2], 'eqbrtrd', concl('ldenri'))
    return fin(w, fin_)


GENS = {'ldencls': gen_cls, 'ldenri': gen_ri}
if __name__ == '__main__':
    for lab in (only or list(GENS)):
        GENS[lab]()
