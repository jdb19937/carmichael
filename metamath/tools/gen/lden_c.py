"""Sortie LDEN, part c: the family (Lean family_card_le: the cover by ld2dlvx, the class-II count by ld2ssq,
the class-I count by ldenc1 on each (i,j), the union count ldenhiu): ldenhiu ldencov ldencnt ldenii ldenci ldenfam.

    MM_DB=sorties/lden.mm MM_ENGINE=mmatch python3 tools/gen/lden_c.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ldenlib import *
import ldenlib as LL
from ef4_g import elrab_unpack, elrab_pack
from ef3lib import elrab_
from lden_a import sc_facts, num8
from lden_b import famparts
import mvlib
import lin as _lin
_lin.MAXPOW = 16
_lin.MAXDEG = 16

only = sys.argv[1:]
S = STATEMENTS
FZ = lambda x: '( 1 ... %s )' % x


def iunfam(w, A, F, i='i', j='j'):
    """finiteness of the class-I families under A (needs F['fin']): SJK(i,j) e. Fin (under A), the inner and outer unions"""
    Aij = '( %s /\\ ( %s e. %s /\\ %s e. %s ) )' % (A, i, RJ, j, KJ)
    Ai = '( %s /\\ %s e. %s )' % (A, i, RJ)
    Aj = '( %s /\\ %s e. %s )' % (Ai, j, KJ)
    sjk = w.s([lift(w, F['fin'], Aj), w.s([w.s([], 'ssrab2', '%s C_ F' % SJK(i, j))], 'a1i', '( %s -> %s C_ F )' % (Aj, SJK(i, j)))], 'ssfid', '( %s -> %s e. Fin )' % (Aj, SJK(i, j)))
    alj = w.s([sjk], 'ralrimiva', '( %s -> A. %s e. %s %s e. Fin )' % (Ai, j, KJ, SJK(i, j)))
    UJ = 'U_ %s e. %s %s' % (j, KJ, SJK(i, j))
    uj = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ai, KJ)), alj, w.inst('iunfi')], 'syl2anc', '( %s -> %s e. Fin )' % (Ai, UJ))
    ali = w.s([uj], 'ralrimiva', '( %s -> A. %s e. %s %s e. Fin )' % (A, i, RJ, UJ))
    un = w.s([w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), ali, w.inst('iunfi')], 'syl2anc', '( %s -> %s e. Fin )' % (A, UNION))
    return dict(sjk=sjk, alj=alj, uj=uj, ali=ali, un=un, Ai=Ai, Aj=Aj)


def hflparts(w, A, P):
    """the HFL antecedent: closure (N T S LD DSC), the scale facts, HZD, the family pieces"""
    F = {}
    F['nN'] = P['N e. NN']; F['tr'] = P['T e. RR']; F['t2'] = P['2 <_ T']; F['l40'] = P[H40]
    F['sr'] = P['S e. RR']; F['s39'] = P['( ; 3 9 / ; 5 0 ) <_ S']; F['s1'] = P['S <_ 1']
    F.update(sc_facts(w, A, F['nN'], F['tr'], F['t2']))
    F['hz'] = ap(w, A, 'ldenhz', [J(w, A, J(w, A, F['nN'], J(w, A, F['tr'], F['t2'])), F['l40'])], HZD)
    F['fin'] = P['F e. Fin']; F['kal'] = P['A. a e. F ( K ` a ) e. %s' % DB()]; F['yal'] = P['A. a e. F ( Y ` a ) e. CC']
    F['pts'] = P[PTSL]; F['sep'] = P[SEPY]
    F['hsig'] = P[HSIG] if HSIG in P else J(w, A, F['sr'], J(w, A, F['s39'], F['s1']))
    F['hscl'] = P[HSCL] if HSCL in P else J(w, A, F['nN'], J(w, A, F['tr'], F['t2']))
    c = Closure(w, A, {'N': ('NN', F['nN']), 'T': [('RR', F['tr']), ('ge0', F['t0'])], 'S': ('RR', F['sr']), DSC: [('RR', F['dr'])], LD: [('RR', F['lr'])]})
    c.leaf(DSC, 'RR+', dst(w, A, [F['dr'], F['lp'] if False else linarith(w, A, [F['d4']], '0 < %s' % DSC, closure=c)], 'elrpd', '%s e. RR+' % DSC))
    c.leaf(LD, 'RR', F['lr']); c.have(LD, 'gt0', F['lp']); c.have(LD, 'ge0', linarith(w, A, [F['l1']], '0 <_ %s' % LD, closure=c))
    c.leaf(PW, 'RR+', c.mem(PW, 'RR+'))
    c.have('S', 'ge0', linarith(w, A, [F['s39']], '0 <_ S', closure=c))
    F['ntd'] = F['nt']
    return c, F


def pts_at(w, Az, pts_lifted, Z, zin):
    """PTSL at a := Z (Z =/= a): dict of the components"""
    body_ = PTSL[len('A. a e. F '):]
    ins, new = inst_forall(w, Az, pts_lifted, 'a', body_, Z, zin)
    Q = parts(w, Az, top=new, step=ins)
    YZ_ = '( Y ` %s )' % Z; KZ_ = '( K ` %s )' % Z
    IM = '( abs ` ( Im ` %s ) )' % YZ_
    return {'sre': Q['S <_ ( Re ` %s )' % YZ_], 're1': Q['( Re ` %s ) <_ 1' % YZ_], 'im': Q['%s <_ T' % IM], 'ne1': Q['%s =/= 1' % YZ_],
            'zero': Q['( ( N DChrLF %s ) ` %s ) = 0' % (KZ_, YZ_)], 'ht': Q['( %s = %s -> %s <_ %s )' % (KZ_, ZG, LD, IM)],
            'body': Q[tsub(PTSB, {'a': Z})] if tsub(PTSB, {'a': Z}) in Q else None}


def gen_hiu():
    w = W('ldenhiu', 'Lean ` Finset.card_biUnion_le ` in function form: the cardinality of a finite union ` U_ x e. A ( F ` x ) ` of finite sets is at most the sum of their cardinalities (induction on the index set, ~ findcard2d , ~ hashun2 ).')
    A = ante('ldenhiu'); c = Ctx(w, A)
    afin, bfin = c.g('A e. Fin'), c.g('A. x e. A ( F ` x ) e. Fin')
    FX = '( F ` x )'; HX = '( # ` ( F ` x ) )'
    PS = lambda Sx: '( # ` U_ x e. %s %s ) <_ sum_ x e. %s %s' % (Sx, FX, Sx, HX)

    def pssub(S1, S2):
        AE = '%s = %s' % (S1, S2)
        e1 = w.s([w.s([], 'iuneq1', '( %s -> U_ x e. %s %s = U_ x e. %s %s )' % (AE, S1, FX, S2, FX))], 'fveq2d', '( %s -> ( # ` U_ x e. %s %s ) = ( # ` U_ x e. %s %s ) )' % (AE, S1, FX, S2, FX))
        e2 = w.s([], 'sumeq1', '( %s -> sum_ x e. %s %s = sum_ x e. %s %s )' % (AE, S1, HX, S2, HX))
        return w.s([e1, e2], 'breq12d', '( %s -> ( %s <-> %s ) )' % (AE, PS(S1), PS(S2)))
    h1 = pssub('y', '(/)'); h2 = pssub('y', 's'); h3 = pssub('y', '( s u. { t } )'); h4 = pssub('y', 'A')
    # base
    z1 = w.s([w.s([], '0iun', 'U_ x e. (/) %s = (/)' % FX)], 'fveq2i', '( # ` U_ x e. (/) %s ) = ( # ` (/) )' % FX)
    z2 = w.s([z1, w.s([], 'hash0', '( # ` (/) ) = 0')], 'eqtri', '( # ` U_ x e. (/) %s ) = 0' % FX)
    z3 = w.s([], 'sum0', 'sum_ x e. (/) %s = 0' % HX)
    z4 = w.s([z2, w.s([], '0le0', '0 <_ 0')], 'eqbrtri', '( # ` U_ x e. (/) %s ) <_ 0' % FX)
    z5 = w.s([z4, w.s([z3], 'eqcomi', '0 = sum_ x e. (/) %s' % HX)], 'breqtri', PS('(/)'))
    h5 = c.a1(z5, PS('(/)'))
    # step
    SQ = '( s C_ A /\\ t e. ( A \\ s ) )'
    Ai = '( %s /\\ %s )' % (A, SQ)
    Ais = '( %s /\\ %s )' % (Ai, PS('s'))
    cs = Ctx(w, Ais)
    ssa = w.s([w.s([], 'simpr', '( %s -> %s )' % (Ai, SQ))], 'adantr', '( %s -> %s )' % (Ais, SQ))
    sa = cs([ssa], 'simpld', 's C_ A'); tin = cs([ssa], 'simprd', 't e. ( A \\ s )')
    ta = cs([tin], 'eldifad', 't e. A'); tns = cs([tin], 'eldifbd', '-. t e. s')
    afin2 = w.s([w.s([afin], 'adantr', '( %s -> A e. Fin )' % Ai)], 'adantr', '( %s -> A e. Fin )' % Ais)
    bfin2 = w.s([w.s([bfin], 'adantr', '( %s -> A. x e. A %s e. Fin )' % (Ai, FX))], 'adantr', '( %s -> A. x e. A %s e. Fin )' % (Ais, FX))
    sfin = cs([afin2, sa], 'ssfid', 's e. Fin')
    imp = cs([sa, w.inst('ssralv')], 'syl', '( A. x e. A %s e. Fin -> A. x e. s %s e. Fin )' % (FX, FX))
    bfs = w.s([bfin2, imp], 'mpd', '( %s -> A. x e. s %s e. Fin )' % (Ais, FX))
    US, UT, UST = 'U_ x e. s %s' % FX, 'U_ x e. { t } %s' % FX, 'U_ x e. ( s u. { t } ) %s' % FX
    FT = '( F ` t )'
    usfin = cs([sfin, bfs, w.inst('iunfi')], 'syl2anc', '%s e. Fin' % US)
    ftfin = w.s([w.s([], 'fveq2', '( x = t -> %s = %s )' % (FX, FT))], 'eleq1d', '( x = t -> ( %s e. Fin <-> %s e. Fin ) )' % (FX, FT))
    ftfin = w.s([ftfin, bfin2, ta], 'rspcdva', '( %s -> %s e. Fin )' % (Ais, FT))
    e1 = w.s([], 'iunxun', '%s = ( %s u. %s )' % (UST, US, UT))
    e2 = w.s([w.s([], 'vex', 't e. _V'), w.s([w.s([], 'fveq2', '( x = t -> %s = %s )' % (FX, FT))], 'iunxsng', '( t e. _V -> %s = %s )' % (UT, FT))], 'ax-mp', '%s = %s' % (UT, FT))
    e3 = w.s([e1, w.s([e2], 'uneq2i', '( %s u. %s ) = ( %s u. %s )' % (US, UT, US, FT))], 'eqtri', '%s = ( %s u. %s )' % (UST, US, FT))
    hu = cs([usfin, ftfin, w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (US, FT, US, FT))
    hu2 = cs([w.s([w.s([e3], 'fveq2i', '( # ` %s ) = ( # ` ( %s u. %s ) )' % (UST, US, FT))], 'a1i', '( %s -> ( # ` %s ) = ( # ` ( %s u. %s ) ) )' % (Ais, UST, US, FT)), hu], 'eqbrtrd',
              '( # ` %s ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (UST, US, FT))
    # the sum over s u. { t } (fsumsplitsn, nf form)
    nf1 = w.s([w.s([], 'nfv', 'F/ x A e. Fin'), w.s([], 'nfra1', 'F/ x A. x e. A %s e. Fin' % FX)], 'nfan', 'F/ x %s' % A)
    nf2 = w.s([nf1, w.s([], 'nfv', 'F/ x %s' % SQ)], 'nfan', 'F/ x %s' % Ai)
    nfu = w.s([w.s([], 'nfcv', 'F/_ x #'), w.s([], 'nfiu1', 'F/_ x %s' % US)], 'nffv', 'F/_ x ( # ` %s )' % US)
    nfs = w.s([], 'nfsum1', 'F/_ x sum_ x e. s %s' % HX)
    nf3 = w.s([nfu, w.s([], 'nfcv', 'F/_ x <_'), nfs], 'nfbr', 'F/ x %s' % PS('s'))
    nf4 = w.s([nf2, nf3], 'nfan', 'F/ x %s' % Ais)
    HT = '( # ` %s )' % FT
    nfd = w.s([], 'nfcv', 'F/_ x %s' % HT)
    Ax = '( %s /\\ x e. s )' % Ais
    bx = w.s([bfs], 'r19.21bi', '( %s -> %s e. Fin )' % (Ax, FX))
    hbx = w.s([w.s([bx, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (Ax, HX))], 'nn0cnd', '( %s -> %s e. CC )' % (Ax, HX))
    dsub = w.s([w.s([], 'fveq2', '( x = t -> %s = %s )' % (FX, FT))], 'fveq2d', '( x = t -> %s = %s )' % (HX, HT))
    htn = cs([ftfin, w.inst('hashcl')], 'syl', '%s e. NN0' % HT)
    dcn = cs([htn], 'nn0cnd', '%s e. CC' % HT)
    fs = w.s([nf4, nfd, sfin, cs.a1(w.s([], 'vex', 't e. _V'), 't e. _V'), tns, hbx, dsub, dcn], 'fsumsplitsn', '( %s -> sum_ x e. ( s u. { t } ) %s = ( sum_ x e. s %s + %s ) )' % (Ais, HX, HX, HT))
    # the sum over s is real: in the letter v
    SV = 'sum_ v e. s ( # ` ( F ` v ) )'; SX = 'sum_ x e. s %s' % HX
    cbv = w.s([w.s([w.s([], 'fveq2', '( x = v -> %s = ( F ` v ) )' % FX)], 'fveq2d', '( x = v -> %s = ( # ` ( F ` v ) ) )' % HX)], 'cbvsumv', '%s = %s' % (SX, SV))
    Av = '( %s /\\ v e. s )' % Ais
    fvfin = w.s([w.s([w.s([], 'fveq2', '( x = v -> %s = ( F ` v ) )' % FX)], 'eleq1d', '( x = v -> ( %s e. Fin <-> ( F ` v ) e. Fin ) )' % FX), w.s([bfs], 'adantr', '( %s -> A. x e. s %s e. Fin )' % (Av, FX)), w.s([], 'simpr', '( %s -> v e. s )' % Av)], 'rspcdva',
               '( %s -> ( F ` v ) e. Fin )' % Av)
    hvr = w.s([w.s([fvfin, w.inst('hashcl')], 'syl', '( %s -> ( # ` ( F ` v ) ) e. NN0 )' % Av)], 'nn0red', '( %s -> ( # ` ( F ` v ) ) e. RR )' % Av)
    svr = cs([sfin, hvr], 'fsumrecl', '%s e. RR' % SV)
    ssr = cs([cs.a1(cbv, '%s = %s' % (SX, SV)), svr], 'eqeltrd', '%s e. RR' % SX)
    # the chain
    ih = w.s([], 'simpr', '( %s -> %s )' % (Ais, PS('s')))
    husr = cs([cs([usfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % US)], 'nn0red', '( # ` %s ) e. RR' % US)
    htr = cs([htn], 'nn0red', '%s e. RR' % HT)
    ad = cs([husr, ssr, htr, ih], 'leadd1dd', '( ( # ` %s ) + %s ) <_ ( %s + %s )' % (US, HT, SX, HT))
    ust_fin = cs([cs.a1(e3, '%s = ( %s u. %s )' % (UST, US, FT)), cs([usfin, ftfin, w.inst('unfi')], 'syl2anc', '( %s u. %s ) e. Fin' % (US, FT))], 'eqeltrd', '%s e. Fin' % UST)
    hustr = cs([cs([ust_fin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % UST)], 'nn0red', '( # ` %s ) e. RR' % UST)
    tr = cs([hustr, cs([husr, htr], 'readdcld', '( ( # ` %s ) + %s ) e. RR' % (US, HT)), cs([ssr, htr], 'readdcld', '( %s + %s ) e. RR' % (SX, HT)), hu2, ad], 'letrd',
            '( # ` %s ) <_ ( %s + %s )' % (UST, SX, HT))
    stp = cs([tr, cs([fs], 'eqcomd', '( %s + %s ) = sum_ x e. ( s u. { t } ) %s' % (SX, HT, HX))], 'breqtrd', PS('( s u. { t } )'))
    h6 = w.s([stp], 'ex', '( %s -> ( %s -> %s ) )' % (Ai, PS('s'), PS('( s u. { t } )')))
    fin_ = w.s([h1, h2, h3, h4, h5, h6, afin], 'findcard2d', '( %s -> %s )' % (A, PS('A')))
    return fin(w, fin_)


def hiu_at(w, A, x, X, B, xfin, bfin_x, bal):
    r"""( A -> ( # ` U_ x e. X B ) <_ sum_ x e. X ( # ` B ) ) by ldenhiu at F := ( v e. X |-> B [ x := v ] ) (ldenhiu's $d F x);
    bfin_x: ( ( A /\ x e. X ) -> B e. Fin ); A must not contain x, v"""
    Bv = tsub(B, {x: 'v'})
    MP = '( v e. %s |-> %s )' % (X, Bv)
    Ax = '( %s /\\ %s e. %s )' % (A, x, X)
    xin = w.s([], 'simpr', '( %s -> %s e. %s )' % (Ax, x, X))
    fv = fvmd(w, Ax, 'v', X, Bv, x, xin, dst(w, Ax, [bfin_x], 'elexd', '%s e. _V' % B))
    fin_x = dst(w, Ax, [fv, bfin_x], 'eqeltrd', '( %s ` %s ) e. Fin' % (MP, x))
    al = dst(w, A, [fin_x], 'ralrimiva', 'A. %s e. %s ( %s ` %s ) e. Fin' % (x, X, MP, x))
    hi = dst(w, A, [J(w, A, xfin, al), w.inst('ldenhiu')], 'syl', '( # ` U_ %s e. %s ( %s ` %s ) ) <_ sum_ %s e. %s ( # ` ( %s ` %s ) )' % (x, X, MP, x, x, X, MP, x))
    ue = dst(w, A, [fv], 'iuneq2dv', 'U_ %s e. %s ( %s ` %s ) = U_ %s e. %s %s' % (x, X, MP, x, x, X, B))
    se = dst(w, A, [dst(w, Ax, [fv], 'fveq2d', '( # ` ( %s ` %s ) ) = ( # ` %s )' % (MP, x, B))], 'sumeq2dv', 'sum_ %s e. %s ( # ` ( %s ` %s ) ) = sum_ %s e. %s ( # ` %s )' % (x, X, MP, x, x, X, B))
    return dst(w, A, [dst(w, A, [ue], 'fveq2d', '( # ` U_ %s e. %s ( %s ` %s ) ) = ( # ` U_ %s e. %s %s )' % (x, X, MP, x, x, X, B)), dst(w, A, [hi, se], 'breqtrd', '( # ` U_ %s e. %s ( %s ` %s ) ) <_ sum_ %s e. %s ( # ` %s )' % (x, X, MP, x, x, X, B))], 'eqbrtrrd',
               '( # ` U_ %s e. %s %s ) <_ sum_ %s e. %s ( # ` %s )' % (x, X, B, x, X, B))


def gen_cov():
    w = W('ldencov', 'Lean ` hcover ` of ` family_card_le ` : every member of the family is in class II ( ` abs EctrHalf >_ 1 / 4 ` ) or in a class-I family ` ( i , j ) ` ( ~ ld2dlvx at the scale ` N ( T + 2 ) ` ; the twist sum written with the letter ` e ` in the families).')
    A = ante('ldencov'); P = parts(w, A)
    c, F = hflparts(w, A, P)
    Ar = '( %s /\\ r e. F )' % A
    rin = w.s([], 'simpr', '( %s -> r e. F )' % Ar)
    Q = pts_at(w, Ar, lift(w, F['pts'], Ar), 'r', rin)
    kr, _ = inst_forall(w, Ar, lift(w, F['kal'], Ar), 'a', '( K ` a ) e. %s' % DB(), 'r', rin)
    yr, _ = inst_forall(w, Ar, lift(w, F['yal'], Ar), 'a', '( Y ` a ) e. CC', 'r', rin)
    KR, YR = '( K ` r )', '( Y ` r )'
    SUB = {'D': DSC, 'X': KR, 'S': YR, 'T': 'S', 'a': 'c'}
    DA, DC = ante_of(tsub(stmt('ld2dlvx'), SUB))
    sig = J(w, Ar, J(w, Ar, lift(w, F['s39'], Ar), lift(w, F['s1'], Ar)), J(w, Ar, Q['sre'], Q['re1']))
    hyp = J(w, Ar, J(w, Ar, J(w, Ar, lift(w, F['hz'], Ar), lift(w, F['nN'], Ar)), J(w, Ar, kr, J(w, Ar, J(w, Ar, yr, Q['ne1']), J(w, Ar, lift(w, F['sr'], Ar), sig)))), J(w, Ar, Q['ht'], Q['zero']))
    assert body(w, hyp, Ar) == DA, (body(w, hyp, Ar)[:300], DA[:300])
    dl = ap(w, Ar, 'ld2dlvx', [hyp], DC)
    CASE1 = '( 1 / 4 ) <_ ( abs ` %s )' % ECTRKC('r')
    TWn = lambda i, j: TWX(i, j, '( Im ` %s )' % YR, KR)
    CASE2 = 'E. m e. %s E. k e. %s %s <_ ( abs ` %s )' % (RJ, KJ, V8D, TWn('m', 'k'))
    assert DC == '( %s \\/ %s )' % (CASE1, CASE2), DC[:200]
    GOAL = 'r e. ( %s u. %s )' % (SII, UNION)
    # case 1
    A1 = '( %s /\\ %s )' % (Ar, CASE1)
    m1 = sii_pack(w, A1, 'r', lift(w, rin, A1), w.s([], 'simpr', '( %s -> %s )' % (A1, CASE1)))
    g1 = w.s([m1, w.inst('elun1')], 'syl', '( %s -> %s )' % (A1, GOAL))
    # case 2
    Amk = '( %s /\\ ( m e. %s /\\ k e. %s ) )' % (Ar, RJ, KJ)
    A2 = '( %s /\\ %s <_ ( abs ` %s ) )' % (Amk, V8D, TWn('m', 'k'))
    TWe = tsub(TWn('m', 'k'), {'n': 'e'})
    cg, BODYe = w.congr(TWn('m', 'k')[len('sum_ n e. %s ' % FZ(tsub(MJ, {'J': 'm', 'D': DSC}))):], {'n': 'e'}, 'n = e', {'n': w.s([], 'id', '( n = e -> n = e )')})
    cbv = w.s([cg], 'cbvsumv', '%s = %s' % (TWn('m', 'k'), TWe))
    cbvb = w.s([w.s([cbv], 'fveq2i', '( abs ` %s ) = ( abs ` %s )' % (TWn('m', 'k'), TWe))], 'breq2i', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (V8D, TWn('m', 'k'), V8D, TWe))
    lv = w.s([w.s([], 'simpr', '( %s -> %s <_ ( abs ` %s ) )' % (A2, V8D, TWn('m', 'k'))), cbvb], 'sylib', '( %s -> %s <_ ( abs ` %s ) )' % (A2, V8D, TWe))
    assert SJK('m', 'k') == '{ q e. F | %s <_ ( abs ` %s ) }' % (V8D, tsub(TWe, {'r': 'q'})), SJK('m', 'k')[:200]
    m2 = elrab_pack(w, A2, 'q', 'F', '%s <_ ( abs ` %s )' % (V8D, tsub(TWe, {'r': 'q'})), 'r', lift(w, lift(w, rin, Amk), A2), lv)
    UJm = 'U_ j e. %s %s' % (KJ, SJK('m', 'j'))
    cj, _ = w.congr(SJK('m', 'j'), {'j': 'k'}, 'j = k', {'j': w.s([], 'id', '( j = k -> j = k )')})
    s1 = w.s([cj], 'ssiun2s', '( k e. %s -> %s C_ %s )' % (KJ, SJK('m', 'k'), UJm))
    ci, _ = w.congr('U_ j e. %s %s' % (KJ, SJK('i', 'j')), {'i': 'm'}, 'i = m', {'i': w.s([], 'id', '( i = m -> i = m )')})
    s2 = w.s([ci], 'ssiun2s', '( m e. %s -> %s C_ %s )' % (RJ, UJm, UNION))
    kin = w.s([w.s([], 'simprr', '( %s -> k e. %s )' % (Amk, KJ))], 'adantr', '( %s -> k e. %s )' % (A2, KJ))
    min_ = w.s([w.s([], 'simprl', '( %s -> m e. %s )' % (Amk, RJ))], 'adantr', '( %s -> m e. %s )' % (A2, RJ))
    e1 = w.s([w.s([kin, s1], 'syl', '( %s -> %s C_ %s )' % (A2, SJK('m', 'k'), UJm)), m2], 'sseldd', '( %s -> r e. %s )' % (A2, UJm))
    e2 = w.s([w.s([min_, s2], 'syl', '( %s -> %s C_ %s )' % (A2, UJm, UNION)), e1], 'sseldd', '( %s -> r e. %s )' % (A2, UNION))
    g2 = w.s([e2, w.inst('elun2')], 'syl', '( %s -> %s )' % (A2, GOAL))
    g2e = w.s([w.s([g2], 'ex', '( %s -> ( %s <_ ( abs ` %s ) -> %s ) )' % (Amk, V8D, TWn('m', 'k'), GOAL))], 'rexlimdvva', '( %s -> ( %s -> %s ) )' % (Ar, CASE2, GOAL))
    g1e = w.s([g1], 'ex', '( %s -> ( %s -> %s ) )' % (Ar, CASE1, GOAL))
    gr = w.s([dl, g1e, g2e], 'mpjaod', '( %s -> %s )' % (Ar, GOAL))
    gre = w.s([gr], 'ex', '( %s -> ( r e. F -> %s ) )' % (A, GOAL))
    fin_ = w.s([gre], 'ssrdv', '( %s -> F C_ ( %s u. %s ) )' % (A, SII, UNION))
    return fin(w, fin_)


def gen_cnt():
    w = W('ldencnt', 'Lean ` hcardN ` , ` hcardR ` of ` family_card_le ` : ` card s <_ card sII + sum_ j sum_ k card sJK ( j , k ) ` ( ~ ldencov , ~ hashssle , ~ hashun2 , ~ ldenhiu twice).')
    A = ante('ldencnt'); P = parts(w, A)
    c, F = hflparts(w, A, P)
    cov = ap(w, A, 'ldencov', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ldencov'))
    U = iunfam(w, A, F)
    sii = dst(w, A, [F['fin'], w.s([w.s([], 'ssrab2', '%s C_ F' % SII)], 'a1i', '( %s -> %s C_ F )' % (A, SII))], 'ssfid', '%s e. Fin' % SII)
    ufin = dst(w, A, [sii, U['un'], w.inst('unfi')], 'syl2anc', '( %s u. %s ) e. Fin' % (SII, UNION))
    h1 = dst(w, A, [ufin, cov, w.inst('hashssle')], 'syl2anc', '( # ` F ) <_ ( # ` ( %s u. %s ) )' % (SII, UNION))
    h2 = dst(w, A, [sii, U['un'], w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (SII, UNION, SII, UNION))
    UJ = 'U_ j e. %s %s' % (KJ, SJK('i', 'j'))
    Ai = U['Ai']
    Aj = U['Aj']
    h3 = hiu_at(w, A, 'i', RJ, UJ, w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), U['uj'], U['ali'])
    h4 = hiu_at(w, Ai, 'j', KJ, SJK('i', 'j'), w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ai, KJ)), U['sjk'], U['alj'])
    hsjk = w.s([w.s([U['sjk'], w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (Aj, SJK('i', 'j')))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (Aj, SJK('i', 'j')))
    sj = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ai, KJ)), hsjk], 'fsumrecl', '( %s -> sum_ j e. %s ( # ` %s ) e. RR )' % (Ai, KJ, SJK('i', 'j')))
    huj = w.s([w.s([U['uj'], w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (Ai, UJ))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (Ai, UJ))
    h5 = dst(w, A, [w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), huj, sj, h4], 'fsumle', 'sum_ i e. %s ( # ` %s ) <_ %s' % (RJ, UJ, SUMJK))
    hun = dst(w, A, [dst(w, A, [U['un'], w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % UNION)], 'nn0red', '( # ` %s ) e. RR' % UNION)
    si = dst(w, A, [w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), huj], 'fsumrecl', 'sum_ i e. %s ( # ` %s ) e. RR' % (RJ, UJ))
    sjk = dst(w, A, [w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), sj], 'fsumrecl', '%s e. RR' % SUMJK)
    h6 = dst(w, A, [hun, si, sjk, h3, h5], 'letrd', '( # ` %s ) <_ %s' % (UNION, SUMJK))
    hsii = dst(w, A, [dst(w, A, [sii, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % SII)], 'nn0red', '( # ` %s ) e. RR' % SII)
    h7 = dst(w, A, [hun, sjk, hsii, h6], 'leadd2dd', '( ( # ` %s ) + ( # ` %s ) ) <_ ( ( # ` %s ) + %s )' % (SII, UNION, SII, SUMJK))
    hf = dst(w, A, [dst(w, A, [F['fin'], w.inst('hashcl')], 'syl', '( # ` F ) e. NN0')], 'nn0red', '( # ` F ) e. RR')
    hu = dst(w, A, [dst(w, A, [ufin, w.inst('hashcl')], 'syl', '( # ` ( %s u. %s ) ) e. NN0' % (SII, UNION))], 'nn0red', '( # ` ( %s u. %s ) ) e. RR' % (SII, UNION))
    t1 = dst(w, A, [hf, hu, dst(w, A, [hsii, hun], 'readdcld', '( ( # ` %s ) + ( # ` %s ) ) e. RR' % (SII, UNION)), h1, h2], 'letrd', '( # ` F ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (SII, UNION))
    fin_ = dst(w, A, [hf, dst(w, A, [hsii, hun], 'readdcld', '( ( # ` %s ) + ( # ` %s ) ) e. RR' % (SII, UNION)), dst(w, A, [hsii, sjk], 'readdcld', '( ( # ` %s ) + %s ) e. RR' % (SII, SUMJK)), t1, h7], 'letrd', concl('ldencnt'))
    return fin(w, fin_)


def gen_ii():
    w = W('ldenii', 'Lean ` hII ` of ` family_card_le ` (class II): ` card sII <_ 16 sum_ r abs EctrHalf ^ 2 <_ 16 FINAL ` ( ~ ld2ssq at the scale ` N ( T + 2 ) ` with the maps written as mappings, ~ ld2hp6 , ~ ld2vlcv for the closure of the contour integral).')
    A = ante('ldenii'); P = parts(w, A)
    c, F = hflparts(w, A, P)
    KP = '( e e. F |-> ( K ` e ) )'; YQ = '( e e. F |-> ( Y ` e ) )'
    Ae = '( %s /\\ e e. F )' % A
    ein = w.s([], 'simpr', '( %s -> e e. F )' % Ae)
    ke_, _ = inst_forall(w, Ae, lift(w, F['kal'], Ae), 'a', '( K ` a ) e. %s' % DB(), 'e', ein)
    ye_, _ = inst_forall(w, Ae, lift(w, F['yal'], Ae), 'a', '( Y ` a ) e. CC', 'e', ein)
    kf = dst(w, A, [ke_], 'fmpttd', '%s : F --> %s' % (KP, DB()))
    yf = dst(w, A, [ye_], 'fmpttd', '%s : F --> CC' % YQ)

    def vals(Az, Z, zin):
        kz, _ = inst_forall(w, Az, lift(w, F['kal'], Az), 'a', '( K ` a ) e. %s' % DB(), Z, zin)
        yz, _ = inst_forall(w, Az, lift(w, F['yal'], Az), 'a', '( Y ` a ) e. CC', Z, zin)
        kv = fvmd(w, Az, 'e', 'F', '( K ` e )', Z, zin, dst(w, Az, [kz], 'elexd', '( K ` %s ) e. _V' % Z))
        yv = fvmd(w, Az, 'e', 'F', '( Y ` e )', Z, zin, yz)
        return kv, yv, kz, yz
    # PTS' in the letter c
    SUB = {'D': DSC, 'T': 'S', 'V': 'T', 'K': KP, 'Y': YQ, 'a': 'c', 'b': 'g'}
    PTSp = tsub(PTS, SUB); SEPp = tsub(SEPY, SUB)
    Ac = '( %s /\\ c e. F )' % A
    cin = w.s([], 'simpr', '( %s -> c e. F )' % Ac)
    kvc, yvc, kzc, yzc = vals(Ac, 'c', cin)
    Qc = pts_at(w, Ac, lift(w, F['pts'], Ac), 'c', cin)
    PB = tsub(PTSB, {'a': 'c'})
    ptsc = J(w, Ac, J(w, Ac, Qc['sre'], Qc['re1']), J(w, Ac, Qc['im'], J(w, Ac, Qc['ne1'], Qc['zero'])))
    assert body(w, ptsc, Ac) == PB, (body(w, ptsc, Ac)[:200], PB[:200])
    PBp = PTSp[len('A. c e. F '):]
    bi, back = w.wcongr(PBp, {}, Ac, {}, rules={'( %s ` c )' % KP: ('( K ` c )', kvc), '( %s ` c )' % YQ: ('( Y ` c )', yvc)})
    assert back == PB, (back[:200], PB[:200])
    ptsc2 = dst(w, Ac, [ptsc, bi], 'mpbird', PBp)
    ptsp = dst(w, A, [ptsc2], 'ralrimiva', PTSp)
    # SEPY' in the letters c g
    Acg = '( %s /\\ ( c e. F /\\ g e. F ) )' % A
    cin2 = w.s([], 'simprl', '( %s -> c e. F )' % Acg); gin2 = w.s([], 'simprr', '( %s -> g e. F )' % Acg)
    kvc2, yvc2, _, _ = vals(Acg, 'c', cin2); kvg2, yvg2, _, _ = vals(Acg, 'g', gin2)
    SB = SEPY[len('A. a e. F A. b e. F '):]
    cg1, S1 = w.wcongr(SB, {'a': 'c'}, 'a = c', {'a': w.s([], 'id', '( a = c -> a = c )')})
    cg1b = w.s([cg1], 'ralbidv', '( a = c -> ( A. b e. F %s <-> A. b e. F %s ) )' % (SB, S1))
    sep1 = w.s([cg1b, lift(w, F['sep'], Acg), cin2], 'rspcdva', '( %s -> A. b e. F %s )' % (Acg, S1))
    cg2, S2 = w.wcongr(S1, {'b': 'g'}, 'b = g', {'b': w.s([], 'id', '( b = g -> b = g )')})
    sep2 = w.s([cg2, sep1, gin2], 'rspcdva', '( %s -> %s )' % (Acg, S2))
    SBp = SEPp[len('A. c e. F A. g e. F '):]
    bi2, back2 = w.wcongr(SBp, {}, Acg, {}, rules={'( %s ` c )' % KP: ('( K ` c )', kvc2), '( %s ` g )' % KP: ('( K ` g )', kvg2), '( %s ` c )' % YQ: ('( Y ` c )', yvc2), '( %s ` g )' % YQ: ('( Y ` g )', yvg2)})
    assert back2 == S2, (back2[:200], S2[:200])
    sep3 = dst(w, Acg, [sep2, bi2], 'mpbird', SBp)
    sepp = dst(w, A, [sep3], 'ralrimivva', SEPp)
    # ld2ssq
    HFAMp = tsub(LL.L2.HFAM, SUB)
    deq = dst(w, A, [], 'eqidd', '%s = ( N x. ( T + 2 ) )' % DSC)
    hfam = J(w, A, J(w, A, J(w, A, F['hz'], J(w, A, F['nN'], F['tr'])), J(w, A, F['t2'], deq)), J(w, A, J(w, A, F['sr'], J(w, A, F['s39'], F['s1'])), J(w, A, J(w, A, F['fin'], kf, yf), J(w, A, ptsp, sepp))))
    assert body(w, hfam, A) == HFAMp, (body(w, hfam, A)[:300], HFAMp[:300])
    ssq = ap(w, A, 'ld2ssq', [hfam], tsub(concl('ld2ssq'), SUB))
    ECp = lambda Z: tsub(ECTRK(Z), SUB)          # ECTRHX ( KP ` Z , YQ ` Z ) at DSC, binder c
    assert tsub(concl('ld2ssq'), SUB) == 'sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ %s' % (ECp('r'), FINALD), tsub(concl('ld2ssq'), SUB)[-300:]
    # per member: ECp ( r ) = ECTRKC ( r ) and its closure
    Ar = '( %s /\\ r e. F )' % A
    rin = w.s([], 'simpr', '( %s -> r e. F )' % Ar)
    kvr, yvr, kzr, yzr = vals(Ar, 'r', rin)
    rules = {'( %s ` r )' % KP: ('( K ` r )', kvr), '( %s ` r )' % YQ: ('( Y ` r )', yvr)}
    rules.update(img_rule(w, Ar, yvr, '( %s ` r )' % YQ, '( Y ` r )'))
    eqr, ecr = w.congr(ECp('r'), {}, Ar, {}, rules=rules)
    assert ecr == ECTRKC('r'), (ecr[:300], ECTRKC('r')[:300])
    hp6 = ap(w, Ar, 'ld2hp6', [J(w, Ar, lift(w, hfam, Ar), rin)], tsub(tsub(concl('ld2hp6'), {'Z': 'r'}), SUB))
    a7c = dst(w, Ar, [hp6], 'simpld', tsub(tsub(LL.L2.subst(LL.L2.A7C, LL.L2.FAM('r')), {'Z': 'r'}), SUB))
    cv = ap(w, Ar, 'ld2vlcv', [a7c], tsub(tsub(LL.L2.subst(concl('ld2vlcv'), LL.L2.FAM('r')), {'Z': 'r'}), SUB))
    VLp = tsub(LL.L2.VLK('r'), SUB)
    vlc = w.s([cv, w.inst('rlimcl')], 'syl', '( %s -> %s e. CC )' % (Ar, VLp))
    TPI = LL.L2.TPI
    assert ECp('r') == '( ( 1 / %s ) x. %s )' % (TPI, VLp), ECp('r')[:100]
    cr = Closure(w, Ar, {'_pi': ('RR+', a1(w, Ar, 'pirp', '_pi e. RR+')), '_i': [('CC', a1(w, Ar, 'ax-icn', '_i e. CC')), ('ne0', a1(w, Ar, 'ine0', '_i =/= 0'))], VLp: ('CC', vlc)})
    cr.atom(VLp)
    IP = '( _i x. _pi )'
    ipn = dst(w, Ar, [cr.mem('_i', 'CC'), cr.mem('_pi', 'CC'), cr.ne0('_i'), cr.ne0('_pi')], 'mulne0d', '%s =/= 0' % IP)
    cr.leaf(TPI, 'CC', cr.mem(TPI, 'CC')); cr.leaf(TPI, 'ne0', dst(w, Ar, [cr.mem('2', 'CC'), cr.mem(IP, 'CC'), cr.ne0('2'), ipn], 'mulne0d', '%s =/= 0' % TPI))
    ecc = cr.mem(ECp('r'), 'CC')
    ecc2 = dst(w, Ar, [eqc(w, Ar, eqr), ecc], 'eqeltrd', '%s e. CC' % ECTRKC('r'))
    AB2 = lambda E: '( ( abs ` %s ) ^ 2 )' % E
    ab2r = dst(w, Ar, [dst(w, Ar, [ecc2], 'abscld', '( abs ` %s ) e. RR' % ECTRKC('r'))], 'resqcld', '%s e. RR' % AB2(ECTRKC('r')))
    ab20 = dst(w, Ar, [dst(w, Ar, [ecc2], 'abscld', '( abs ` %s ) e. RR' % ECTRKC('r'))], 'sqge0d', '0 <_ %s' % AB2(ECTRKC('r')))
    tt = dst(w, Ar, [dst(w, Ar, [eqr], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (ECp('r'), ECTRKC('r')))], 'oveq1d', '%s = %s' % (AB2(ECp('r')), AB2(ECTRKC('r'))))
    SF = 'sum_ r e. F %s' % AB2(ECTRKC('r'))
    se = dst(w, A, [tt], 'sumeq2dv', 'sum_ r e. F %s = %s' % (AB2(ECp('r')), SF))
    ssq2 = dst(w, A, [eqc(w, A, se), ssq], 'eqbrtrd', '%s <_ %s' % (SF, FINALD))
    # the count: ( # SII ) x. ( 1 / 16 ) <_ sum_ r e. SII abs^2 <_ sum_ r e. F abs^2
    sii = dst(w, A, [F['fin'], w.s([w.s([], 'ssrab2', '%s C_ F' % SII)], 'a1i', '( %s -> %s C_ F )' % (A, SII))], 'ssfid', '%s e. Fin' % SII)
    As = '( %s /\\ r e. %s )' % (A, SII)
    sinn = w.s([], 'simpr', '( %s -> r e. %s )' % (As, SII))
    rF, rb = sii_unpack(w, As, 'r', sinn)
    q16 = num8(w, As, '( 1 / ; 1 6 )')
    abr_s = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (As, A)), rF], 'jca', '( %s -> %s )' % (As, Ar)), dst(w, Ar, [ecc2], 'abscld', '( abs ` %s ) e. RR' % ECTRKC('r'))], 'syl', '( %s -> ( abs ` %s ) e. RR )' % (As, ECTRKC('r')))
    q4 = num8(w, As, '( 1 / 4 )')
    q40 = lin8(w, As, [], '0 <_ ( 1 / 4 )', {})
    sq = w.s([w.s([w.s([q4, q40], 'jca', '( %s -> ( ( 1 / 4 ) e. RR /\\ 0 <_ ( 1 / 4 ) ) )' % As), w.s([abr_s, rb], 'jca', '( %s -> ( ( abs ` %s ) e. RR /\\ ( 1 / 4 ) <_ ( abs ` %s ) ) )' % (As, ECTRKC('r'), ECTRKC('r')))], 'jca',
                  '( %s -> ( ( ( 1 / 4 ) e. RR /\\ 0 <_ ( 1 / 4 ) ) /\\ ( ( abs ` %s ) e. RR /\\ ( 1 / 4 ) <_ ( abs ` %s ) ) ) )' % (As, ECTRKC('r'), ECTRKC('r'))), w.inst('le2sq2')], 'syl',
             '( %s -> ( ( 1 / 4 ) ^ 2 ) <_ %s )' % (As, AB2(ECTRKC('r'))))
    e16 = w.s([ringeqp(w, As, '( ( 1 / 4 ) ^ 2 )', '( 1 / ; 1 6 )', Closure(w, As, {})), sq], 'eqbrtrrd', '( %s -> ( 1 / ; 1 6 ) <_ %s )' % (As, AB2(ECTRKC('r'))))
    ab2rs = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (As, A)), rF], 'jca', '( %s -> %s )' % (As, Ar)), ab2r], 'syl', '( %s -> %s e. RR )' % (As, AB2(ECTRKC('r'))))
    fl = dst(w, A, [sii, q16 if False else w.s([], '0red', '( %s -> 0 e. RR )' % As) if False else num8(w, As, '( 1 / ; 1 6 )'), ab2rs, e16], 'fsumle', 'sum_ r e. %s ( 1 / ; 1 6 ) <_ sum_ r e. %s %s' % (SII, SII, AB2(ECTRKC('r'))))
    fc = dst(w, A, [sii, num8(w, A, '( 1 / ; 1 6 )', 'CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ r e. %s ( 1 / ; 1 6 ) = ( ( # ` %s ) x. ( 1 / ; 1 6 ) )' % (SII, SII))
    fless = dst(w, A, [F['fin'], ab2r, ab20, w.s([w.s([], 'ssrab2', '%s C_ F' % SII)], 'a1i', '( %s -> %s C_ F )' % (A, SII))], 'fsumless', 'sum_ r e. %s %s <_ %s' % (SII, AB2(ECTRKC('r')), SF))
    HS = '( # ` %s )' % SII
    hsr = dst(w, A, [dst(w, A, [sii, w.inst('hashcl')], 'syl', '%s e. NN0' % HS)], 'nn0red', '%s e. RR' % HS)
    c.leaf(HS, 'RR', hsr)
    ssr = dst(w, A, [sii, ab2rs], 'fsumrecl', 'sum_ r e. %s %s e. RR' % (SII, AB2(ECTRKC('r'))))
    sfr = dst(w, A, [F['fin'], ab2r], 'fsumrecl', '%s e. RR' % SF)
    c.leaf(SF, 'RR', sfr)
    t1 = dst(w, A, [eqc(w, A, fc), fl], 'eqbrtrd', '( %s x. ( 1 / ; 1 6 ) ) <_ sum_ r e. %s %s' % (HS, SII, AB2(ECTRKC('r'))))
    t2 = dst(w, A, [c.mem('( %s x. ( 1 / ; 1 6 ) )' % HS, 'RR'), ssr, sfr, t1, fless], 'letrd', '( %s x. ( 1 / ; 1 6 ) ) <_ %s' % (HS, SF))
    c.leaf('CTau', 'NN', ctau_nn(w, A))
    c.leaf(FINALD, 'RR', c.mem(FINALD, 'RR'))
    t3 = dst(w, A, [c.mem('( %s x. ( 1 / ; 1 6 ) )' % HS, 'RR'), sfr, c.mem(FINALD, 'RR'), t2, ssq2], 'letrd', '( %s x. ( 1 / ; 1 6 ) ) <_ %s' % (HS, FINALD))
    fin_ = linarith(w, A, [t3], concl('ldenii'), closure=c)
    return fin(w, fin_)


def gen_ci():
    w = W('ldenci', 'Lean ` hI ` , ` hsum ` of ` family_card_le ` (class I): every family ` sJK ( i , j ) ` has at most ` 10 ^ 10 log ^ 10 D D ^ ( ... ) ` members ( ~ ldenc1 at the scale ` N ( T + 2 ) ` , the family hypotheses in the letters ` c g ` ), so the double sum is at most ` J ( J + 1 ) ` times that.')
    A = ante('ldenci'); P = parts(w, A)
    c, F = hflparts(w, A, P)
    U = iunfam(w, A, F)
    Ai, Aj = U['Ai'], U['Aj']
    C1D = C1(DSC)
    c.leaf(C1D, 'RR', c.mem(C1D, 'RR'))
    # ldenc1 at ( i , j )
    SJ = SJK('i', 'j')
    Ac = '( %s /\\ c e. %s )' % (Aj, SJ)
    cin = w.s([], 'simpr', '( %s -> c e. %s )' % (Ac, SJ))
    TWe = tsub(TWX('i', 'j', '( Im ` ( Y ` c ) )', '( K ` c )'), {'n': 'e'})
    cF, cb, _ = elrab_unpack(w, Ac, 'q', 'F', '%s <_ ( abs ` %s )' % (V8D, tsub(TWe, {'c': 'q'})), 'c', cin)
    Lc = lambda st: lift(w, lift(w, lift(w, st, Ai), Aj), Ac)
    kc, _ = inst_forall(w, Ac, Lc(F['kal']), 'a', '( K ` a ) e. %s' % DB(), 'c', cF)
    yc, _ = inst_forall(w, Ac, Lc(F['yal']), 'a', '( Y ` a ) e. CC', 'c', cF)
    Qc = pts_at(w, Ac, Lc(F['pts']), 'c', cF)
    TWn = TWX('i', 'j', '( Im ` ( Y ` c ) )', '( K ` c )')
    cg, _ = w.congr(TWe[len('sum_ e e. %s ' % FZ(tsub(MJ, {'J': 'i', 'D': DSC}))):], {'e': 'n'}, 'e = n', {'e': w.s([], 'id', '( e = n -> e = n )')})
    cbv = w.s([cg], 'cbvsumv', '%s = %s' % (TWe, TWn))
    cbvb = w.s([w.s([cbv], 'fveq2i', '( abs ` %s ) = ( abs ` %s )' % (TWe, TWn))], 'breq2i', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (V8D, TWe, V8D, TWn))
    lvc = w.s([cb, cbvb], 'sylib', '( %s -> %s <_ ( abs ` %s ) )' % (Ac, V8D, TWn))
    kal = dst(w, Aj, [kc], 'ralrimiva', 'A. c e. %s ( K ` c ) e. %s' % (SJ, DB()))
    yal = dst(w, Aj, [yc], 'ralrimiva', 'A. c e. %s ( Y ` c ) e. CC' % SJ)
    rng = dst(w, Aj, [Qc['im']], 'ralrimiva', 'A. c e. %s ( abs ` ( Im ` ( Y ` c ) ) ) <_ T' % SJ)
    lva = dst(w, Aj, [lvc], 'ralrimiva', 'A. c e. %s %s <_ ( abs ` %s )' % (SJ, V8D, TWn))
    # SEPY' on the sub-family
    Acg = '( %s /\\ ( c e. %s /\\ g e. %s ) )' % (Aj, SJ, SJ)
    cin2 = w.s([], 'simprl', '( %s -> c e. %s )' % (Acg, SJ)); gin2 = w.s([], 'simprr', '( %s -> g e. %s )' % (Acg, SJ))
    cF2 = w.s([cin2, w.inst('elrabi')], 'syl', '( %s -> c e. F )' % Acg); gF2 = w.s([gin2, w.inst('elrabi')], 'syl', '( %s -> g e. F )' % Acg)
    SB = SEPY[len('A. a e. F A. b e. F '):]
    cg1, S1 = w.wcongr(SB, {'a': 'c'}, 'a = c', {'a': w.s([], 'id', '( a = c -> a = c )')})
    cg1b = w.s([cg1], 'ralbidv', '( a = c -> ( A. b e. F %s <-> A. b e. F %s ) )' % (SB, S1))
    sep1 = w.s([cg1b, lift(w, lift(w, lift(w, F['sep'], Ai), Aj), Acg), cF2], 'rspcdva', '( %s -> A. b e. F %s )' % (Acg, S1))
    cg2, S2 = w.wcongr(S1, {'b': 'g'}, 'b = g', {'b': w.s([], 'id', '( b = g -> b = g )')})
    sep2 = w.s([cg2, sep1, gF2], 'rspcdva', '( %s -> %s )' % (Acg, S2))
    sepp = dst(w, Aj, [sep2], 'ralrimivva', 'A. c e. %s A. g e. %s %s' % (SJ, SJ, S2))
    # the block index facts
    iin = w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, RJ))
    inn0 = w.s([iin, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai)
    ilt = w.s([iin, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (Ai, JP))
    jin = w.s([], 'simpr', '( %s -> j e. %s )' % (Aj, KJ))
    jnn0 = w.s([jin, w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % Aj)
    Lj = lambda st: lift(w, lift(w, st, Ai), Aj)
    hyp = J(w, Aj, J(w, Aj, J(w, Aj, Lj(F['hz']), Lj(F['hscl'])), J(w, Aj, Lj(F['ntd']), Lj(F['hsig']))),
            J(w, Aj, J(w, Aj, J(w, Aj, U['sjk'], J(w, Aj, kal, yal)), J(w, Aj, rng, sepp)), J(w, Aj, J(w, Aj, lift(w, inn0, Aj), lift(w, ilt, Aj)), J(w, Aj, jnn0, lva))))
    SUB = {'D': DSC, 'F': SJ, 'J': 'i', 'I': 'j', 'a': 'c', 'b': 'g'}
    CA, CC_ = ante_of(tsub(S['ldenc1'], SUB))
    assert body(w, hyp, Aj) == CA, (body(w, hyp, Aj)[:400], CA[:400])
    c1 = ap(w, Aj, 'ldenc1', [hyp], CC_)
    assert CC_ == '( # ` %s ) <_ %s' % (SJ, C1D), CC_[-200:]
    # the sums
    hsjk = w.s([w.s([U['sjk'], w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (Aj, SJ))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (Aj, SJ))
    c1r = lift(w, c.mem(C1D, 'RR'), Aj)
    fj = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ai, KJ)), hsjk, c1r, c1], 'fsumle', '( %s -> sum_ j e. %s ( # ` %s ) <_ sum_ j e. %s %s )' % (Ai, KJ, SJ, KJ, C1D))
    jp = ap(w, A, 'ld1jpar', [F['hz']], tsub(concl('ld1jpar'), {'D': DSC}))
    jpn = dst(w, A, [dst(w, A, [jp], 'simpld', '( %s e. NN /\\ 3 <_ %s )' % (JP, JP))], 'simpld', '%s e. NN' % JP)
    jpn0 = dst(w, A, [jpn], 'nnnn0d', '%s e. NN0' % JP)
    c.leaf(JP, 'NN', jpn)
    fcj = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ai, KJ)), lift(w, c.mem(C1D, 'CC'), Ai), w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ j e. %s %s = ( ( # ` %s ) x. %s ) )' % (Ai, KJ, C1D, KJ, C1D))
    hkj = w.s([jpn0, w.inst('hashfz0')], 'syl', '( %s -> ( # ` %s ) = ( %s + 1 ) )' % (A, KJ, JP))
    fcj2 = w.s([fcj, w.s([lift(w, hkj, Ai)], 'oveq1d', '( %s -> ( ( # ` %s ) x. %s ) = ( ( %s + 1 ) x. %s ) )' % (Ai, KJ, C1D, JP, C1D))], 'eqtrd', '( %s -> sum_ j e. %s %s = ( ( %s + 1 ) x. %s ) )' % (Ai, KJ, C1D, JP, C1D))
    fj2 = w.s([fj, fcj2], 'breqtrd', '( %s -> sum_ j e. %s ( # ` %s ) <_ ( ( %s + 1 ) x. %s ) )' % (Ai, KJ, SJ, JP, C1D))
    sj = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ai, KJ)), hsjk], 'fsumrecl', '( %s -> sum_ j e. %s ( # ` %s ) e. RR )' % (Ai, KJ, SJ))
    J1C = '( ( %s + 1 ) x. %s )' % (JP, C1D)
    fi = dst(w, A, [w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), sj, lift(w, c.mem(J1C, 'RR'), Ai), fj2], 'fsumle', '%s <_ sum_ i e. %s %s' % (SUMJK, RJ, J1C))
    fci = dst(w, A, [w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), c.mem(J1C, 'CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ i e. %s %s = ( ( # ` %s ) x. %s )' % (RJ, J1C, RJ, J1C))
    hrj = w.s([jpn0, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (A, RJ, JP))
    fci2 = dst(w, A, [fci, dst(w, A, [hrj], 'oveq1d', '( ( # ` %s ) x. %s ) = ( %s x. %s )' % (RJ, J1C, JP, J1C))], 'eqtrd', 'sum_ i e. %s %s = ( %s x. %s )' % (RJ, J1C, JP, J1C))
    ma = dst(w, A, [c.mem(JP, 'CC'), c.mem('( %s + 1 )' % JP, 'CC'), c.mem(C1D, 'CC')], 'mulassd', '( ( %s x. ( %s + 1 ) ) x. %s ) = ( %s x. %s )' % (JP, JP, C1D, JP, J1C))
    fin_ = dst(w, A, [fi, dst(w, A, [fci2, eqc(w, A, ma)], 'eqtrd', 'sum_ i e. %s %s = ( ( %s x. ( %s + 1 ) ) x. %s )' % (RJ, J1C, JP, JP, C1D))], 'breqtrd', concl('ldenci'))
    return fin(w, fin_)


def gen_fam():
    w = W('ldenfam', '**Lean ` family_card_le ` ** (section 3.6 core): a ` 1 ` -spaced family of box zeros with the ` chi_0 ` height clause has at most ` 2 10 ^ 26 CTau ^ 2 log ^ 12 D D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) ` members ( ~ ldencnt , ~ ldenii , ~ ldenci , ~ ldenv8 ; ` 16 10 ^ 25 + 4 10 ^ 10 <_ 2 10 ^ 26 ` ).')
    A = ante('ldenfam'); P = parts(w, A)
    c, F = hflparts(w, A, P)
    idA = w.s([], 'id', '( %s -> %s )' % (A, A))
    cnt = ap(w, A, 'ldencnt', [idA], concl('ldencnt'))
    ii = ap(w, A, 'ldenii', [idA], concl('ldenii'))
    ci = ap(w, A, 'ldenci', [idA], concl('ldenci'))
    v8 = ap(w, A, 'ldenv8', [F['hz']], tsub(concl('ldenv8'), {'D': DSC}))
    v8b = dst(w, A, [v8], 'simprd', tsub(top_and(concl('ldenv8'))[1], {'D': DSC}))
    jl = dst(w, A, [v8b], 'simprd', '( %s <_ ( 2 x. %s ) /\\ ( %s + 1 ) <_ ( 2 x. %s ) )' % (JP, LD, JP, LD))
    jl2 = dst(w, A, [jl], 'simpld', '%s <_ ( 2 x. %s )' % (JP, LD)); jl3 = dst(w, A, [jl], 'simprd', '( %s + 1 ) <_ ( 2 x. %s )' % (JP, LD))
    jp = ap(w, A, 'ld1jpar', [F['hz']], tsub(concl('ld1jpar'), {'D': DSC}))
    jpn = dst(w, A, [dst(w, A, [jp], 'simpld', '( %s e. NN /\\ 3 <_ %s )' % (JP, JP))], 'simpld', '%s e. NN' % JP)
    c.leaf(JP, 'NN', jpn)
    c.leaf('CTau', 'NN', ctau_nn(w, A))
    L = LD
    P25, P10, P26 = LL.P10('; 2 5'), LL.P10('; 1 0'), LL.P10('; 2 6')
    for p_ in (P25, P10, P26):
        c.leaf(p_, 'NN', dst(w, A, [], 'x', '') if False else w.s([w.s([w.s([], '10nn', '; 1 0 e. NN'), num.fact(w, p_.split()[-2] if False else {P25: '; 2 5', P10: '; 1 0', P26: '; 2 6'}[p_], 'NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % p_)], 'a1i', '( %s -> %s e. NN )' % (A, p_)))
    CT2 = '( CTau ^ 2 )'
    c.leaf(CT2, 'RR', c.mem(CT2, 'RR')); ct1 = ap(w, A, 'expge1', [J(w, A, c.mem('CTau', 'RR'), a1(w, A, '2nn0', '2 e. NN0'), dst(w, A, [c.mem('CTau', 'NN')], 'nnge1d', '1 <_ CTau'))], '1 <_ %s' % CT2)
    c.have(CT2, 'ge1', ct1); c.have(CT2, 'ge0', linarith(w, A, [ct1], '0 <_ %s' % CT2, closure=c))
    # the pieces
    HS = '( # ` %s )' % SII; HF = '( # ` F )'
    sii = dst(w, A, [F['fin'], w.s([w.s([], 'ssrab2', '%s C_ F' % SII)], 'a1i', '( %s -> %s C_ F )' % (A, SII))], 'ssfid', '%s e. Fin' % SII)
    c.leaf(HS, 'NN0', w.s([sii, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, HS)))
    c.leaf(HF, 'NN0', w.s([F['fin'], w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, HF)))
    U = iunfam(w, A, F)
    hsjk = w.s([w.s([U['sjk'], w.inst('hashcl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (U['Aj'], SJK('i', 'j')))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (U['Aj'], SJK('i', 'j')))
    sj = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (U['Ai'], KJ)), hsjk], 'fsumrecl', '( %s -> sum_ j e. %s ( # ` %s ) e. RR )' % (U['Ai'], KJ, SJK('i', 'j')))
    sjk = dst(w, A, [w.s([w.s([], 'fzofi', '%s e. Fin' % RJ)], 'a1i', '( %s -> %s e. Fin )' % (A, RJ)), sj], 'fsumrecl', '%s e. RR' % SUMJK)
    c.leaf(SUMJK, 'RR', sjk)
    # the arithmetic: M = CT2 ( P25 ( L^12 PW ) ); SUMJK <_ 4 M, HS <_ 16 M, B2 = 20 M
    JJ1 = '( %s x. ( %s + 1 ) )' % (JP, JP)
    L2 = '( 2 x. %s )' % L
    pr = dst(w, A, [c.mem(JP, 'RR'), c.mem(L2, 'RR'), c.mem('( %s + 1 )' % JP, 'RR'), c.mem(L2, 'RR'), c.ge0(JP), c.ge0('( %s + 1 )' % JP), jl2, jl3], 'lemul12ad',
             '%s <_ ( %s x. %s )' % (JJ1, L2, L2))
    uz = w.s([w.s([num.fact(w, '; 1 0', 'ZZ'), num.fact(w, '; 2 5', 'ZZ'), num.le_nat(w, 10, 25)], '3pm3.2i', '( ; 1 0 e. ZZ /\\ ; 2 5 e. ZZ /\\ ; 1 0 <_ ; 2 5 )'), w.s([], 'eluz2', '( ; 2 5 e. ( ZZ>= ` ; 1 0 ) <-> ( ; 1 0 e. ZZ /\\ ; 2 5 e. ZZ /\\ ; 1 0 <_ ; 2 5 ) )')], 'mpbir', '; 2 5 e. ( ZZ>= ` ; 1 0 )')
    le10 = w.s([w.s([num.fact(w, '; 1 0', 'RR'), num.le_nat(w, 1, 10), uz], '3pm3.2i', '( ; 1 0 e. RR /\\ 1 <_ ; 1 0 /\\ ; 2 5 e. ( ZZ>= ` ; 1 0 ) )'), w.inst('leexp2a')], 'ax-mp', '%s <_ %s' % (P10, P25))
    le10d = w.s([le10], 'a1i', '( %s -> %s <_ %s )' % (A, P10, P25))
    uz2 = w.s([w.s([num.fact(w, '5', 'ZZ'), num.fact(w, '; 1 2', 'ZZ'), num.le_nat(w, 5, 12)], '3pm3.2i', '( 5 e. ZZ /\\ ; 1 2 e. ZZ /\\ 5 <_ ; 1 2 )'), w.s([], 'eluz2', '( ; 1 2 e. ( ZZ>= ` 5 ) <-> ( 5 e. ZZ /\\ ; 1 2 e. ZZ /\\ 5 <_ ; 1 2 ) )')], 'mpbir', '; 1 2 e. ( ZZ>= ` 5 )')
    lge1 = linarith(w, A, [F['l40']], '1 <_ %s' % L, closure=c)
    l512 = ap(w, A, 'leexp2a', [J(w, A, c.mem(L, 'RR'), lge1, w.s([uz2], 'a1i', '( %s -> ; 1 2 e. ( ZZ>= ` 5 ) )' % A))], '( %s ^ 5 ) <_ ( %s ^ ; 1 2 )' % (L, L))
    e26 = w.s([w.s([num.fact(w, '; 1 0', 'CC'), num.fact(w, '; 2 5', 'NN0'), w.inst('expp1')], 'mp2an', '( ; 1 0 ^ ( ; 2 5 + 1 ) ) = ( %s x. ; 1 0 )' % P25), w.s([num.add_nat(w, 25, 1)], 'oveq2i', '( ; 1 0 ^ ( ; 2 5 + 1 ) ) = %s' % P26)], 'eqtr3i', '( %s x. ; 1 0 ) = %s' % (P25, P26))
    e26r = w.s([w.s([e26], 'eqcomi', '%s = ( %s x. ; 1 0 )' % (P26, P25))], 'a1i', '( %s -> %s = ( %s x. ; 1 0 ) )' % (A, P26, P25))
    for p_ in (P25, P10, L, PW, CT2, JP, HS, HF, SUMJK):
        c.atom(p_)
    L12 = '( %s ^ ; 1 2 )' % L; X12 = '( %s x. %s )' % (L12, PW)
    M = '( %s x. ( %s x. %s ) )' % (CT2, P25, X12)
    c.have(X12, 'RR', c.mem(X12, 'RR')); c.have(X12, 'ge0', c.ge0(X12))
    # class I: SUMJK <_ 4 M
    C1D = C1(DSC)
    a2 = dst(w, A, [c.mem(JJ1, 'RR'), c.mem('( %s x. %s )' % (L2, L2), 'RR'), c.mem(C1D, 'RR'), c.ge0(C1D), pr], 'lemul1ad', '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (JJ1, C1D, L2, L2, C1D))
    a3 = ringeqp(w, A, '( ( %s x. %s ) x. %s )' % (L2, L2, C1D), '( 4 x. ( %s x. %s ) )' % (P10, X12), c)
    a4 = dst(w, A, [c.mem(P10, 'RR'), c.mem(P25, 'RR'), c.mem(X12, 'RR'), c.ge0(X12), le10d], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (P10, X12, P25, X12))
    PX = '( %s x. %s )' % (P25, X12)
    a5 = dst(w, A, [num8(w, A, '1'), c.mem(CT2, 'RR'), c.mem(PX, 'RR'), c.ge0(PX), ct1], 'lemul1ad', '( 1 x. %s ) <_ ( %s x. %s )' % (PX, CT2, PX))
    a5b = dst(w, A, [eqc(w, A, dst(w, A, [c.mem(PX, 'CC')], 'mullidd', '( 1 x. %s ) = %s' % (PX, PX))), a5], 'eqbrtrd', '%s <_ %s' % (PX, M))
    c.have(M, 'RR', c.mem(M, 'RR'))
    a45 = dst(w, A, [c.mem('( %s x. %s )' % (P10, X12), 'RR'), c.mem(PX, 'RR'), c.mem(M, 'RR'), a4, a5b], 'letrd', '( %s x. %s ) <_ %s' % (P10, X12, M))
    a6 = lemul(w, A, c, a45, '4', side=2)
    a7 = dst(w, A, [c.mem('( %s x. %s )' % (JJ1, C1D), 'RR'), c.mem('( 4 x. ( %s x. %s ) )' % (P10, X12), 'RR'), c.mem('( 4 x. %s )' % M, 'RR'), dst(w, A, [a2, a3], 'breqtrd', '( %s x. %s ) <_ ( 4 x. ( %s x. %s ) )' % (JJ1, C1D, P10, X12)), a6], 'letrd', '( %s x. %s ) <_ ( 4 x. %s )' % (JJ1, C1D, M))
    sj4 = dst(w, A, [c.mem(SUMJK, 'RR'), c.mem('( %s x. %s )' % (JJ1, C1D), 'RR'), c.mem('( 4 x. %s )' % M, 'RR'), ci, a7], 'letrd', '%s <_ ( 4 x. %s )' % (SUMJK, M))
    # class II: HS <_ 16 M
    PC = '( %s x. %s )' % (P25, CT2)
    b2 = dst(w, A, [c.mem('( %s ^ 5 )' % L, 'RR'), c.mem(L12, 'RR'), c.mem(PC, 'RR'), c.ge0(PC), l512], 'lemul2ad', '( %s x. ( %s ^ 5 ) ) <_ ( %s x. %s )' % (PC, L, PC, L12))
    b3 = dst(w, A, [c.mem('( %s x. ( %s ^ 5 ) )' % (PC, L), 'RR'), c.mem('( %s x. %s )' % (PC, L12), 'RR'), c.mem(PW, 'RR'), c.ge0(PW), b2], 'lemul1ad', '( ( %s x. ( %s ^ 5 ) ) x. %s ) <_ ( ( %s x. %s ) x. %s )' % (PC, L, PW, PC, L12, PW))
    assert FINALD == '( ( %s x. ( %s ^ 5 ) ) x. %s )' % (PC, L, PW), FINALD
    b4 = ringeq(w, A, '( ( %s x. %s ) x. %s )' % (PC, L12, PW), M, c)
    b5 = lemul(w, A, c, dst(w, A, [b3, b4], 'breqtrd', '%s <_ %s' % (FINALD, M)), '; 1 6', side=2)
    hs16 = dst(w, A, [c.mem(HS, 'RR'), c.mem('( ; 1 6 x. %s )' % FINALD, 'RR'), c.mem('( ; 1 6 x. %s )' % M, 'RR'), ii, b5], 'letrd', '%s <_ ( ; 1 6 x. %s )' % (HS, M))
    # B2 = 20 M
    b2eq, B2p = w.congr(B2, {}, A, {}, rules={P26: ('( %s x. ; 1 0 )' % P25, e26r)})
    e20 = ringeq(w, A, B2p, '( ; 2 0 x. %s )' % M, c)
    c.atom(M)
    fin0 = linarith(w, A, [cnt, hs16, sj4], '%s <_ ( ; 2 0 x. %s )' % (HF, M), closure=c)
    fin_ = dst(w, A, [fin0, dst(w, A, [b2eq, e20], 'eqtrd', '%s = ( ; 2 0 x. %s )' % (B2, M))], 'breqtrrd', concl('ldenfam'))
    return fin(w, fin_)


GENS = {'ldenhiu': gen_hiu, 'ldencov': gen_cov, 'ldencnt': gen_cnt, 'ldenii': gen_ii, 'ldenci': gen_ci, 'ldenfam': gen_fam}
if __name__ == '__main__':
    for lab in (only or list(GENS)):
        GENS[lab]()
