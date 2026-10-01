"""Sortie C9: lndhre (the Re-log bound for the cofactor H on SQ(C,13/8))."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from cl import lift
from c8_o import numst, center_int
from c8_n import sqcc
from c9_freeze import S as FS
import lin
lin.FASTPATH = True

NS = NSUM('Z')
R134 = '( ; 1 3 / 4 )'
E18 = EXPL('Z', R18)
E134 = EXPL('Z', R134)
ZO = '( Z e. Fin /\\ O : Z --> NN )'
LG = lambda x: '( log ` %s )' % x


def ns_facts(w, A0, zfin, of):
    """( A0 -> NS e. RR ), ( A0 -> 0 <_ NS ) through a q-free antecedent"""
    Zq = '( %s /\\ q e. Z )' % ZO
    oqn = w.s([w.s([], 'simplr', '( %s -> O : Z --> NN )' % Zq), w.s([], 'simpr', '( %s -> q e. Z )' % Zq)], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN )' % Zq)
    oqr = w.s([oqn], 'nnred', '( %s -> ( O ` q ) e. RR )' % Zq)
    oq0 = w.s([w.s([oqn], 'nnnn0d', '( %s -> ( O ` q ) e. NN0 )' % Zq)], 'nn0ge0d', '( %s -> 0 <_ ( O ` q ) )' % Zq)
    zf = w.s([], 'simpl', '( %s -> Z e. Fin )' % ZO)
    r0 = w.s([zf, oqr], 'fsumrecl', '( %s -> %s e. RR )' % (ZO, NS))
    g0 = w.s([zf, oqr, oq0], 'fsumge0', '( %s -> 0 <_ %s )' % (ZO, NS))
    zo = w.s([zfin, of], 'jca', '( %s -> %s )' % (A0, ZO))
    return w.s([zo, r0], 'syl', '( %s -> %s e. RR )' % (A0, NS)), w.s([zo, g0], 'syl', '( %s -> 0 <_ %s )' % (A0, NS))


def in_sq(w, ante, cs, r):
    """( ante -> C e. SQ(C,r) ) for a positive literal r"""
    rst = numst(w, ante, r, 'RR'); rp = numst(w, ante, r, 'gt0')
    a, b = sqcc(w, ante, cs, rst, r=r)
    inn = center_int(w, ante, cs, rst, rp, 'C', r)
    return w.s([w.s([a, b], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ante, SQA('C', r), SQB('C', r))), inn, w.inst('crectinp')], 'syl2anc', '( %s -> C e. %s )' % (ante, SQ('C', r)))


def fac_at(w, ante, fac, T, tst):
    """( ante -> ( F ` T ) = ( PRZ(Z,T) x. ( H ` T ) ) ) from fac and tst : ( ante -> T e. D )"""
    PT = PRZ('Z', T)
    sub = w.s([w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (T, T)),
               w.s([w.s([w.s([w.s([], 'oveq1', '( z = %s -> ( z - q ) = ( %s - q ) )' % (T, T))], 'oveq1d', '( z = %s -> ( ( z - q ) ^ ( O ` q ) ) = ( ( %s - q ) ^ ( O ` q ) ) )' % (T, T))], 'prodeq2sdv',
                         '( z = %s -> %s = %s )' % (T, PRZ('Z', 'z'), PT)), w.s([], 'fveq2', '( z = %s -> ( H ` z ) = ( H ` %s ) )' % (T, T))], 'oveq12d',
                   '( z = %s -> ( %s x. ( H ` z ) ) = ( %s x. ( H ` %s ) ) )' % (T, PRZ('Z', 'z'), PT, T))], 'eqeq12d',
              '( z = %s -> ( ( F ` z ) = ( %s x. ( H ` z ) ) <-> ( F ` %s ) = ( %s x. ( H ` %s ) ) ) )' % (T, PRZ('Z', 'z'), T, PT, T))
    return w.s([sub, fac, tst], 'rspcdva', '( %s -> ( F ` %s ) = ( %s x. ( H ` %s ) ) )' % (ante, T, PT, T))


def nz_at(w, ante, hnz, T, tst):
    sub = w.s([w.s([], 'fveq2', '( z = %s -> ( H ` z ) = ( H ` %s ) )' % (T, T))], 'neeq1d', '( z = %s -> ( ( H ` z ) =/= 0 <-> ( H ` %s ) =/= 0 ) )' % (T, T))
    return w.s([sub, hnz, tst], 'rspcdva', '( %s -> ( H ` %s ) =/= 0 )' % (ante, T))


def gen_lndhre():
    w = W('lndhre', 'The real-part bound for the logarithm of the cofactor: ` log abs H ( y ) - log abs H ( C ) <_ log ( B / abs F ( C ) ) + W log 26 ` on the square of half-side ` 13 / 8 ` , ` W ` a bound for the multiplicity mass ( ~ lndhbd , ~ fprodube ).')
    X3 = '( ( F ` C ) =/= 0 /\\ ( W e. RR /\\ %s <_ W ) )' % NS
    A0 = '( ( %s /\\ %s ) /\\ %s )' % (DATA, FBD, X3)
    dst = w.s([], 'simpll', '( %s -> %s )' % (A0, DATA))
    fbd = w.s([], 'simplr', '( %s -> %s )' % (A0, FBD))
    fc0 = w.s([], 'simprl', '( %s -> ( F ` C ) =/= 0 )' % A0)
    wr = w.s([w.s([], 'simprr', '( %s -> ( W e. RR /\\ %s <_ W ) )' % (A0, NS)), w.inst('simpl')], 'syl', '( %s -> W e. RR )' % A0)
    nsw = w.s([w.s([], 'simprr', '( %s -> ( W e. RR /\\ %s <_ W ) )' % (A0, NS)), w.inst('simpr')], 'syl', '( %s -> %s <_ W )' % (A0, NS))
    d = data_parts(w, A0, dst)
    cs = d['cs']
    bst = w.s([fbd, w.inst('simpl')], 'syl', '( %s -> B e. RR )' % A0)
    fb = w.s([fbd, w.inst('simpr')], 'syl', '( %s -> A. x e. %s ( abs ` ( F ` x ) ) <_ B )' % (A0, SQ74))
    nsr, ns0 = ns_facts(w, A0, d['zfin'], d['of'])
    c138 = in_sq(w, A0, cs, R138)
    c74 = in_sq(w, A0, cs, R74)
    cd = w.s([d['s74d'], c74], 'sseldd', '( %s -> C e. D )' % A0)
    fcc = w.s([w.s([w.s([d['hol'], w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0), cd], 'ffvelcdmd', '( %s -> ( F ` C ) e. CC )' % A0)
    afc = w.s([fcc, fc0], 'absrpcld', '( %s -> ( abs ` ( F ` C ) ) e. RR+ )' % A0)
    subx = w.s([w.s([w.s([], 'fveq2', '( x = C -> ( F ` x ) = ( F ` C ) )')], 'fveq2d', '( x = C -> ( abs ` ( F ` x ) ) = ( abs ` ( F ` C ) ) )')], 'breq1d',
               '( x = C -> ( ( abs ` ( F ` x ) ) <_ B <-> ( abs ` ( F ` C ) ) <_ B ) )')
    fcb = w.s([subx, fb, c74], 'rspcdva', '( %s -> ( abs ` ( F ` C ) ) <_ B )' % A0)
    bp = w.s([bst, w.s([w.s([afc], 'rpgt0d', '( %s -> 0 < ( abs ` ( F ` C ) ) )' % A0), fcb], 'ltletrd', '( %s -> 0 < B )' % A0)], 'elrpd', '( %s -> B e. RR+ )' % A0)
    # the centre: abs F ( C ) <_ E134 abs H ( C )
    hcn = w.s([d['holh'], w.inst('simpl')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
    hf = w.s([hcn, w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % A0)
    hc = w.s([hf, cd], 'ffvelcdmd', '( %s -> ( H ` C ) e. CC )' % A0)
    hc0 = nz_at(w, A0, d['hnz'], 'C', c138)
    ahc = w.s([hc, hc0], 'absrpcld', '( %s -> ( abs ` ( H ` C ) ) e. RR+ )' % A0)
    fcC = fac_at(w, A0, d['fac'], 'C', cd)
    PC = PRZ('Z', 'C')
    r138 = numst(w, A0, R138, 'RR')
    a138c, b138c = sqcc(w, A0, cs, r138, r=R138)
    s138cc = w.s([w.s([a138c, b138c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A138, B138)), w.inst('crectss')], 'syl', '( %s -> %s C_ CC )' % (A0, SQ138))
    zc = w.s([d['zsq'], s138cc], 'sstrd', '( %s -> Z C_ CC )' % A0)
    of0 = w.s([d['of'], w.s([w.s([], 'nnssnn0', 'NN C_ NN0')], 'a1i', '( %s -> NN C_ NN0 )' % A0)], 'fssd', '( %s -> O : Z --> NN0 )' % A0)
    Aj = '( %s /\\ j e. Z )' % A0
    js = w.s([lift(w, d['zsq'], Aj), w.s([], 'simpr', '( %s -> j e. Z )' % Aj)], 'sseldd', '( %s -> j e. %s )' % (Aj, SQ138))
    jm = w.s([w.s([w.s([lift(w, cs, Aj), lift(w, r138, Aj)], 'jca', '( %s -> ( C e. CC /\\ %s e. RR ) )' % (Aj, R138)), js], 'jca',
                  '( %s -> ( ( C e. CC /\\ %s e. RR ) /\\ j e. %s ) )' % (Aj, R138, SQ138)), w.inst('sqmem')], 'syl', '( %s -> ( abs ` ( j - C ) ) <_ ( 2 x. %s ) )' % (Aj, R138))
    jcc = w.s([lift(w, s138cc, Aj), js], 'sseldd', '( %s -> j e. CC )' % Aj)
    jsub = w.s([jcc, lift(w, cs, Aj)], 'abssubd', '( %s -> ( abs ` ( j - C ) ) = ( abs ` ( C - j ) ) )' % Aj)
    ajc = w.s([w.s([jcc, lift(w, cs, Aj)], 'subcld', '( %s -> ( j - C ) e. CC )' % Aj)], 'abscld', '( %s -> ( abs ` ( j - C ) ) e. RR )' % Aj)
    jle = lin8(w, Aj, [jm], '( abs ` ( j - C ) ) <_ %s' % R134, {'( abs ` ( j - C ) )': ajc})
    jle2 = w.s([jsub, jle], 'eqbrtrrd', '( %s -> ( abs ` ( C - j ) ) <_ %s )' % (Aj, R134))
    DALL = 'A. j e. Z ( abs ` ( C - j ) ) <_ %s' % R134
    dall = w.s([jle2], 'ralrimiva', '( %s -> %s )' % (A0, DALL))
    PUB = tsub(stmt('fprodube'), {'S': 'Z', 'U': 'C', 'R': R134})
    pa, pc = ante_of(PUB)
    pub = w.s([w.s([w.s([d['zfin'], zc, of0], '3jca', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % A0),
                    w.s([cs, numst(w, A0, R134, 'RR+'), dall], '3jca', '( %s -> ( C e. CC /\\ %s e. RR+ /\\ %s ) )' % (A0, R134, DALL))], 'jca', '( %s -> %s )' % (A0, pa)),
               w.inst('fprodube')], 'syl', '( %s -> %s )' % (A0, pc))
    assert pc == '( abs ` %s ) <_ %s' % (PC, E134), pc
    # PC e. CC: from ( PC x. H C ) = F C and H C =/= 0: PC = F C / H C
    ZC = '( ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) /\\ C e. CC )'
    Zq = '( %s /\\ q e. Z )' % ZC
    zs3 = w.s([], 'simpll', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % Zq)
    qz = w.s([], 'simpr', '( %s -> q e. Z )' % Zq)
    qcq = w.s([w.s([zs3, w.inst('simp2')], 'syl', '( %s -> Z C_ CC )' % Zq), qz], 'sseldd', '( %s -> q e. CC )' % Zq)
    oqq = w.s([w.s([zs3, w.inst('simp3')], 'syl', '( %s -> O : Z --> NN0 )' % Zq), qz], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN0 )' % Zq)
    tq = w.s([w.s([w.s([], 'simplr', '( %s -> C e. CC )' % Zq), qcq], 'subcld', '( %s -> ( C - q ) e. CC )' % Zq), oqq], 'expcld', '( %s -> ( ( C - q ) ^ ( O ` q ) ) e. CC )' % Zq)
    pc0 = w.s([w.s([w.s([], 'simpl', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % ZC), w.inst('simp1')], 'syl', '( %s -> Z e. Fin )' % ZC), tq], 'fprodcl', '( %s -> %s e. CC )' % (ZC, PC))
    pcin = w.s([w.s([w.s([d['zfin'], zc, of0], '3jca', '( %s -> ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN0 ) )' % A0), cs], 'jca', '( %s -> %s )' % (A0, ZC)), pc0], 'syl', '( %s -> %s e. CC )' % (A0, PC))
    ahcr = w.s([ahc], 'rpred', '( %s -> ( abs ` ( H ` C ) ) e. RR )' % A0)
    l134 = w.s([numst(w, A0, R134, 'RR+')], 'relogcld', '( %s -> %s e. RR )' % (A0, LG(R134)))
    l18 = w.s([numst(w, A0, R18, 'RR+')], 'relogcld', '( %s -> %s e. RR )' % (A0, LG(R18)))
    N1, N8 = '( %s x. %s )' % (NS, LG(R134)), '( %s x. %s )' % (NS, LG(R18))
    n1r = w.s([nsr, l134], 'remulcld', '( %s -> %s e. RR )' % (A0, N1))
    n8r = w.s([nsr, l18], 'remulcld', '( %s -> %s e. RR )' % (A0, N8))
    e134p = w.s([n1r], 'rpefcld', '( %s -> %s e. RR+ )' % (A0, E134))
    e18p = w.s([n8r], 'rpefcld', '( %s -> %s e. RR+ )' % (A0, E18))
    m1 = w.s([w.s([pcin], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, PC)), w.s([e134p], 'rpred', '( %s -> %s e. RR )' % (A0, E134)), ahcr, pub, w.s([ahc], 'rpge0d', '( %s -> 0 <_ ( abs ` ( H ` C ) ) )' % A0)],
             'lemul1ad', '( %s -> ( ( abs ` %s ) x. ( abs ` ( H ` C ) ) ) <_ ( %s x. ( abs ` ( H ` C ) ) ) )' % (A0, PC, E134))
    am = w.s([w.s([fcC], 'fveq2d', '( %s -> ( abs ` ( F ` C ) ) = ( abs ` ( %s x. ( H ` C ) ) ) )' % (A0, PC)), w.s([pcin, hc], 'absmuld', '( %s -> ( abs ` ( %s x. ( H ` C ) ) ) = ( ( abs ` %s ) x. ( abs ` ( H ` C ) ) ) )' % (A0, PC, PC))],
             'eqtrd', '( %s -> ( abs ` ( F ` C ) ) = ( ( abs ` %s ) x. ( abs ` ( H ` C ) ) ) )' % (A0, PC))
    cb = w.s([am, m1], 'eqbrtrd', '( %s -> ( abs ` ( F ` C ) ) <_ ( %s x. ( abs ` ( H ` C ) ) ) )' % (A0, E134))
    EH = '( %s x. ( abs ` ( H ` C ) ) )' % E134
    ehp = w.s([e134p, ahc], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, EH))
    lc1 = w.s([cb, w.s([afc, ehp], 'logled', '( %s -> ( ( abs ` ( F ` C ) ) <_ %s <-> %s <_ %s ) )' % (A0, EH, LG('( abs ` ( F ` C ) )'), LG(EH)))], 'mpbid',
              '( %s -> %s <_ %s )' % (A0, LG('( abs ` ( F ` C ) )'), LG(EH)))
    lm = w.s([e134p, ahc], 'relogmuld', '( %s -> %s = ( %s + %s ) )' % (A0, LG(EH), LG(E134), LG('( abs ` ( H ` C ) )')))
    le1 = w.s([n1r, w.inst('relogef')], 'syl', '( %s -> %s = %s )' % (A0, LG(E134), N1))
    h2 = w.s([lc1, w.s([lm, w.s([le1], 'oveq1d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LG(E134), LG('( abs ` ( H ` C ) )'), N1, LG('( abs ` ( H ` C ) )')))], 'eqtrd',
                       '( %s -> %s = ( %s + %s ) )' % (A0, LG(EH), N1, LG('( abs ` ( H ` C ) )')))], 'breqtrd', '( %s -> %s <_ ( %s + %s ) )' % (A0, LG('( abs ` ( F ` C ) )'), N1, LG('( abs ` ( H ` C ) )')))
    # log 26
    l26 = LG('; 2 6')
    import num
    L8 = LG('8')
    r8 = numst(w, A0, '8', 'RR+')
    r134p = numst(w, A0, R134, 'RR+')
    e26 = w.s([num.mul_lits(w, R134, '8')], 'a1i', '( %s -> ( %s x. 8 ) = ; 2 6 )' % (A0, R134))
    l26e = w.s([w.s([w.s([e26], 'eqcomd', '( %s -> ; 2 6 = ( %s x. 8 ) )' % (A0, R134))], 'fveq2d', '( %s -> %s = %s )' % (A0, l26, LG('( %s x. 8 )' % R134))),
                w.s([r134p, r8], 'relogmuld', '( %s -> %s = ( %s + %s ) )' % (A0, LG('( %s x. 8 )' % R134), LG(R134), L8))], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, l26, LG(R134), L8))
    l18e = w.s([numst(w, A0, '1', 'RR+'), r8], 'relogdivd', '( %s -> %s = ( %s - %s ) )' % (A0, LG(R18), LG('1'), L8))
    log1 = w.s([w.s([], 'log1', '( log ` 1 ) = 0')], 'a1i', '( %s -> ( log ` 1 ) = 0 )' % A0)
    l8r = w.s([r8], 'relogcld', '( %s -> %s e. RR )' % (A0, L8))
    l26r = w.s([numst(w, A0, '; 2 6', 'RR+')], 'relogcld', '( %s -> %s e. RR )' % (A0, l26))
    l1r = w.s([numst(w, A0, '1', 'RR+')], 'relogcld', '( %s -> %s e. RR )' % (A0, LG('1')))
    lvn = {LG(R134): l134, LG(R18): l18, L8: l8r, l26: l26r, LG('1'): l1r}
    l26d = lin.lineq(w, A0, l26, '( %s - %s )' % (LG(R134), LG(R18)), hyps=[l26e, l18e, log1], closure=_clo(w, A0, lvn))
    N26 = '( %s x. %s )' % (NS, l26)
    n26 = w.s([w.s([l26d], 'oveq2d', '( %s -> %s = ( %s x. ( %s - %s ) ) )' % (A0, N26, NS, LG(R134), LG(R18))),
               w.s([w.s([nsr], 'recnd', '( %s -> %s e. CC )' % (A0, NS)), w.s([l134], 'recnd', '( %s -> %s e. CC )' % (A0, LG(R134))), w.s([l18], 'recnd', '( %s -> %s e. CC )' % (A0, LG(R18)))], 'subdid',
                   '( %s -> ( %s x. ( %s - %s ) ) = ( %s - %s ) )' % (A0, NS, LG(R134), LG(R18), N1, N8))], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A0, N26, N1, N8))
    W26 = '( W x. %s )' % l26
    l26g = w.s([numst(w, A0, '; 2 6', 'RR'), lin8(w, A0, [], '1 <_ ; 2 6', {})], 'logge0d', '( %s -> 0 <_ %s )' % (A0, l26))
    nw = w.s([nsr, wr, l26r, nsw, l26g], 'lemul1ad', '( %s -> %s <_ %s )' % (A0, N26, W26))
    LBF = LG('( B / ( abs ` ( F ` C ) ) )')
    lbf = w.s([bp, afc], 'relogdivd', '( %s -> %s = ( %s - %s ) )' % (A0, LBF, LG('B'), LG('( abs ` ( F ` C ) )')))
    # at y
    Ay = '( %s /\\ y e. %s )' % (A0, SQ138)
    L = lambda st: lift(w, st, Ay)
    ys = w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, SQ138))
    HB = tsub(stmt('lndhbd'), {'Y': 'y'})
    ha, hcc = ante_of(HB)
    hb = w.s([w.s([w.s([L(dst), L(fbd)], 'jca', '( %s -> ( %s /\\ %s ) )' % (Ay, DATA, FBD)), ys], 'jca', '( %s -> %s )' % (Ay, ha)), w.inst('lndhbd')], 'syl', '( %s -> %s )' % (Ay, hcc))
    ab74 = sqcc(w, Ay, L(cs), L(numst(w, A0, R74, 'RR')), r=R74)
    from c9_e import sqfrd_at
    sy, _ = sqfrd_at(w, Ay, L(cs), 'y', ys)
    iy = w.s([sy, w.inst('simpl')], 'syl', '( %s -> %s )' % (Ay, INTG(A74, B74, 'y')))
    y74 = w.s([w.s([ab74[0], ab74[1]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Ay, A74, B74)), iy, w.inst('crectinp')], 'syl2anc', '( %s -> y e. %s )' % (Ay, SQ74))
    yd = w.s([L(d['s74d']), y74], 'sseldd', '( %s -> y e. D )' % Ay)
    hy = w.s([L(hf), yd], 'ffvelcdmd', '( %s -> ( H ` y ) e. CC )' % Ay)
    hy0 = nz_at(w, Ay, L(d['hnz']), 'y', ys)
    ahy = w.s([hy, hy0], 'absrpcld', '( %s -> ( abs ` ( H ` y ) ) e. RR+ )' % Ay)
    M = '( B / %s )' % E18
    mp = w.s([L(bp), L(e18p)], 'rpdivcld', '( %s -> %s e. RR+ )' % (Ay, M))
    ly = w.s([hb, w.s([ahy, mp], 'logled', '( %s -> ( ( abs ` ( H ` y ) ) <_ %s <-> %s <_ %s ) )' % (Ay, M, LG('( abs ` ( H ` y ) )'), LG(M)))], 'mpbid', '( %s -> %s <_ %s )' % (Ay, LG('( abs ` ( H ` y ) )'), LG(M)))
    lmd = w.s([L(bp), L(e18p)], 'relogdivd', '( %s -> %s = ( %s - %s ) )' % (Ay, LG(M), LG('B'), LG(E18)))
    le8 = w.s([L(n8r), w.inst('relogef')], 'syl', '( %s -> %s = %s )' % (Ay, LG(E18), N8))
    h1 = w.s([ly, w.s([lmd, w.s([le8], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (Ay, LG('B'), LG(E18), LG('B'), N8))], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (Ay, LG(M), LG('B'), N8))],
             'breqtrd', '( %s -> %s <_ ( %s - %s ) )' % (Ay, LG('( abs ` ( H ` y ) )'), LG('B'), N8))
    lv = {LG('( abs ` ( H ` y ) )'): w.s([ahy], 'relogcld', '( %s -> %s e. RR )' % (Ay, LG('( abs ` ( H ` y ) )'))),
          LG('( abs ` ( H ` C ) )'): L(w.s([ahc], 'relogcld', '( %s -> %s e. RR )' % (A0, LG('( abs ` ( H ` C ) )')))),
          LG('B'): L(w.s([bp], 'relogcld', '( %s -> %s e. RR )' % (A0, LG('B')))),
          LG('( abs ` ( F ` C ) )'): L(w.s([afc], 'relogcld', '( %s -> %s e. RR )' % (A0, LG('( abs ` ( F ` C ) )')))),
          LBF: L(w.s([w.s([bp, afc], 'rpdivcld', '( %s -> ( B / ( abs ` ( F ` C ) ) ) e. RR+ )' % A0)], 'relogcld', '( %s -> %s e. RR )' % (A0, LBF))),
          N1: L(n1r), N8: L(n8r), N26: L(w.s([nsr, l26r], 'remulcld', '( %s -> %s e. RR )' % (A0, N26))), W26: L(w.s([wr, l26r], 'remulcld', '( %s -> %s e. RR )' % (A0, W26)))}
    GOALY = '( %s - %s ) <_ %s' % (LG('( abs ` ( H ` y ) )'), LG('( abs ` ( H ` C ) )'), LOGM)
    assert LOGM == '( %s + %s )' % (LBF, W26), LOGM
    fin = lin8(w, Ay, [h1, L(h2), L(lbf), L(n26), L(nw)], GOALY, lv)
    goal = '( %s -> A. y e. %s %s )' % (A0, SQ138, GOALY)
    assert goal == FS['lndhre'], (goal, FS['lndhre'])
    w.qed([fin], 'ralrimiva', goal)
    return run8(w)


def _clo(w, A0, lv):
    import cl as _cl
    c = _cl.Closure(w, A0, lv)
    for k in lv:
        c.atom(k)
    return c


if __name__ == '__main__':
    gen_lndhre()
