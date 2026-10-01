"""EF1 section 6: the interchange (ExplicitFormula 1366-1582).
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_d.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from cl import formula_of
from c0lib import vol01
from lin import linarith

only = sys.argv[1:]
U = '( 0 (,) 1 )'
L = '( B - A )'
SEG = '( A cseg B )'


def ZP(t):
    return '( A + ( %s x. ( B - A ) ) )' % t


def TK(k, t):
    return '( ( ( F ` %s ) ` %s ) x. ( B - A ) )' % (k, ZP(t))


def under(w, C, to_ph, to_mem, imp, concl):
    """( C -> concl ) from to_ph: ( C -> ph ), to_mem: ( C -> x e. X ), imp: ( ( ph /\\ x e. X ) -> concl )"""
    return w.s([to_ph, to_mem, w.s([imp], 'ex', exform(w, imp))], 'sylc', '( %s -> %s )' % (C, concl))


def exform(w, imp):
    """the formula ( ph -> ( ps -> ch ) ) of ex applied to imp: ( ( ph /\\ ps ) -> ch )"""
    from cl import split_imp
    f = formula_of(w, imp)
    a, c = split_imp(f)
    # a = ( ph /\ ps )
    toks = a.split()
    assert toks[0] == '(' and toks[-1] == ')'
    body = toks[1:-1]
    d = 0
    for i, tk in enumerate(body):
        if tk == '(':
            d += 1
        elif tk == ')':
            d -= 1
        elif tk == '/\\' and d == 0:
            return '( %s -> ( %s -> %s ) )' % (' '.join(body[:i]), ' '.join(body[i + 1:]), c)
    raise ValueError(a)


# ---------------------------------------------------------------- ef1lser: a dominated series of continuous functions, integrated along a segment
if __name__ == '__main__' and (not only or 'ef1lser' in only):
    w = W('ef1lser', 'Term-by-term integration along a segment: if continuous ` F ( k ) ` on ` D ` are bounded on the segment '
          '` [ A , B ] ` by ` G ( k ) ` with ` sum G ( k ) ` convergent, the line integrals of ` F ( k ) ` sum to the line '
          'integral of ` sum_ k F ( k ) ` .  Uniform convergence on the parameter interval (C5 ~ uhlim , the Weierstrass '
          'test) and ~ itgulm2 ; no dominated convergence.  The engine of Lean ` integral_right_edge ` .')
    for nm, f in HYPS['ef1lser']:
        w.s([], 'ef1lser.%s' % nm, f, name='h' + nm)
    ph = 'ph'
    ac = D(w, ph, 'simpld', ['h1'], 'A e. CC'); bc = D(w, ph, 'simprd', ['h1'], 'B e. CC')
    ff = D(w, ph, 'simpld', ['h2'], 'F : NN --> ( D -cn-> CC )'); sd = D(w, ph, 'simprd', ['h2'], '%s C_ D' % SEG)
    gf = D(w, ph, 'simpld', ['h3'], 'G : NN --> RR'); gcv = D(w, ph, 'simprd', ['h3'], 'seq 1 ( + , G ) e. dom ~~>')
    lc = D(w, ph, 'subcld', [bc, ac], '%s e. CC' % L)
    alr = D(w, ph, 'abscld', [lc], '( abs ` %s ) e. RR' % L); al0 = D(w, ph, 'absge0d', [lc], '0 <_ ( abs ` %s )' % L)
    ue = a1(w, ph, 'ovex', '%s e. _V' % U)
    v1, umb, uvr = vol01(w, ph)
    R4 = 'A. k e. NN A. z e. %s ( abs ` ( ( F ` k ) ` z ) ) <_ ( G ` k )' % SEG
    r4 = w.s(['h4'], 'ralrimivva', '( ph -> %s )' % R4)

    def pt(k, t):
        """facts under C = ( ( ph /\\ k e. NN ) /\\ t e. U ): the point, the value, the bound"""
        C = '( ( ph /\\ %s e. NN ) /\\ %s e. %s )' % (k, t, U)
        d = {'C': C}
        d['ph'] = w.s([], 'simpll', '( %s -> ph )' % C)
        d['kn'] = w.s([], 'simplr', '( %s -> %s e. NN )' % (C, k))
        tu = w.s([], 'simpr', '( %s -> %s e. %s )' % (C, t, U))
        t01 = w.s([a1(w, C, 'ioossicc', '%s C_ ( 0 [,] 1 )' % U), tu], 'sseldd', '( %s -> %s e. ( 0 [,] 1 ) )' % (C, t))
        acc = w.s([d['ph'], ac], 'syl', '( %s -> A e. CC )' % C); bcc = w.s([d['ph'], bc], 'syl', '( %s -> B e. CC )' % C)
        d['seg'] = w.s([acc, bcc, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. %s )' % (C, ZP(t), SEG))
        d['inD'] = w.s([w.s([d['ph'], sd], 'syl', '( %s -> %s C_ D )' % (C, SEG)), d['seg']], 'sseldd', '( %s -> %s e. D )' % (C, ZP(t)))
        d['fk'] = w.s([w.s([d['ph'], ff], 'syl', '( %s -> F : NN --> ( D -cn-> CC ) )' % C), d['kn']], 'ffvelcdmd', '( %s -> ( F ` %s ) e. ( D -cn-> CC ) )' % (C, k))
        d['val'] = w.s([w.s([d['fk'], w.inst('cncff')], 'syl', '( %s -> ( F ` %s ) : D --> CC )' % (C, k)), d['inD']], 'ffvelcdmd', '( %s -> ( ( F ` %s ) ` %s ) e. CC )' % (C, k, ZP(t)))
        d['lc'] = w.s([d['ph'], lc], 'syl', '( %s -> %s e. CC )' % (C, L))
        d['tk'] = D(w, C, 'mulcld', [d['val'], d['lc']], '%s e. CC' % TK(k, t))
        sb1 = w.s([w.s([w.s([], 'fveq2', '( k = %s -> ( F ` k ) = ( F ` %s ) )' % (k, k))], 'fveq1d', '( k = %s -> ( ( F ` k ) ` z ) = ( ( F ` %s ) ` z ) )' % (k, k))], 'fveq2d',
                  '( k = %s -> ( abs ` ( ( F ` k ) ` z ) ) = ( abs ` ( ( F ` %s ) ` z ) ) )' % (k, k))
        b1 = w.s([sb1, w.s([], 'fveq2', '( k = %s -> ( G ` k ) = ( G ` %s ) )' % (k, k))], 'breq12d',
                 '( k = %s -> ( ( abs ` ( ( F ` k ) ` z ) ) <_ ( G ` k ) <-> ( abs ` ( ( F ` %s ) ` z ) ) <_ ( G ` %s ) ) )' % (k, k, k))
        b2 = w.s([w.s([w.s([], 'fveq2', '( z = %s -> ( ( F ` %s ) ` z ) = ( ( F ` %s ) ` %s ) )' % (ZP(t), k, k, ZP(t)))], 'fveq2d',
                      '( z = %s -> ( abs ` ( ( F ` %s ) ` z ) ) = ( abs ` ( ( F ` %s ) ` %s ) ) )' % (ZP(t), k, k, ZP(t)))], 'breq1d',
                 '( z = %s -> ( ( abs ` ( ( F ` %s ) ` z ) ) <_ ( G ` %s ) <-> ( abs ` ( ( F ` %s ) ` %s ) ) <_ ( G ` %s ) ) )' % (ZP(t), k, k, k, ZP(t), k))
        rs = w.s([b1, b2], 'rspc2v', '( ( %s e. NN /\\ %s e. %s ) -> ( %s -> ( abs ` ( ( F ` %s ) ` %s ) ) <_ ( G ` %s ) ) )' % (k, ZP(t), SEG, R4, k, ZP(t), k))
        d['bnd'] = w.s([w.s([d['kn'], d['seg']], 'jca', '( %s -> ( %s e. NN /\\ %s e. %s ) )' % (C, k, ZP(t), SEG)), w.s([d['ph'], r4], 'syl', '( %s -> %s )' % (C, R4)), rs], 'sylc',
                       '( %s -> ( abs ` ( ( F ` %s ) ` %s ) ) <_ ( G ` %s ) )' % (C, k, ZP(t), k))
        return d

    # the parametrised term functions H ( a ) = ( s e. U |-> TK ( a , s ) )
    HV = lambda a: '( s e. %s |-> %s )' % (U, TK(a, 's'))
    H = '( a e. NN |-> %s )' % HV('a')
    ps = pt('a', 's')
    hvf = ps['tk']
    PA = '( ph /\\ a e. NN )'
    hvm = w.s([hvf, w.s([], 'eqid', '%s = %s' % (HV('a'), HV('a')))], 'fmptd', '( %s -> %s : %s --> CC )' % (PA, HV('a'), U))
    hvcm = elmapf(w, PA, HV('a'), a1(w, PA, 'ovex', '%s e. _V' % U), hvm, U)
    hf = w.s([hvcm, w.s([], 'eqid', '%s = %s' % (H, H))], 'fmptd', '( ph -> %s : NN --> ( CC ^m %s ) )' % (H, U))

    def hval(k, t):
        """( C -> ( ( H ` k ) ` t ) = TK ( k , t ) ) under C = ( ( ph /\\ k e. NN ) /\\ t e. U )"""
        C = '( ( ph /\\ %s e. NN ) /\\ %s e. %s )' % (k, t, U)
        PK = '( ph /\\ %s e. NN )' % k
        sub = w.s([w.s([w.s([w.s([], 'fveq2', '( a = %s -> ( F ` a ) = ( F ` %s ) )' % (k, k))], 'fveq1d', '( a = %s -> ( ( F ` a ) ` %s ) = ( ( F ` %s ) ` %s ) )' % (k, ZP('s'), k, ZP('s')))], 'oveq1d',
                       '( a = %s -> %s = %s )' % (k, TK('a', 's'), TK(k, 's')))], 'mpteq2dv', '( a = %s -> %s = %s )' % (k, HV('a'), HV(k)))
        hk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (H, H))], 'a1i', '( %s -> %s = %s )' % (PK, H, H)), w.s([sub], 'adantl', '( ( %s /\\ a = %s ) -> %s = %s )' % (PK, k, HV('a'), HV(k))),
                  w.s([], 'simpr', '( %s -> %s e. NN )' % (PK, k)), w.s([w.s([w.s([], 'ovex', '%s e. _V' % U), w.inst('mptexg')], 'ax-mp', '%s e. _V' % HV(k))], 'a1i', '( %s -> %s e. _V )' % (PK, HV(k)))],
                 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (PK, H, k, HV(k)))
        hkc = w.s([hk], 'adantr', '( %s -> ( %s ` %s ) = %s )' % (C, H, k, HV(k)))
        sub2 = w.s([w.s([w.s([w.s([], 'oveq1', '( s = %s -> ( s x. ( B - A ) ) = ( %s x. ( B - A ) ) )' % (t, t))], 'oveq2d', '( s = %s -> %s = %s )' % (t, ZP('s'), ZP(t)))], 'fveq2d',
                        '( s = %s -> ( ( F ` %s ) ` %s ) = ( ( F ` %s ) ` %s ) )' % (t, k, ZP('s'), k, ZP(t)))], 'oveq1d', '( s = %s -> %s = %s )' % (t, TK(k, 's'), TK(k, t)))
        v = pt(k, t)
        tv = w.s([w.s([w.s([], 'eqid', '%s = %s' % (HV(k), HV(k)))], 'a1i', '( %s -> %s = %s )' % (C, HV(k), HV(k))), w.s([sub2], 'adantl', '( ( %s /\\ s = %s ) -> %s = %s )' % (C, t, TK(k, 's'), TK(k, t))),
                  w.s([], 'simpr', '( %s -> %s e. %s )' % (C, t, U)), v['tk']], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (C, HV(k), t, TK(k, t)))
        return w.s([w.s([hkc], 'fveq1d', '( %s -> ( ( %s ` %s ) ` %s ) = ( %s ` %s ) )' % (C, H, k, t, HV(k), t)), tv], 'eqtrd', '( %s -> ( ( %s ` %s ) ` %s ) = %s )' % (C, H, k, t, TK(k, t))), v

    # the majorant M' ( a ) = G ( a ) | B - A |
    ML = '( a e. NN |-> ( ( G ` a ) x. ( abs ` %s ) ) )' % L
    gar = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % PA), gf], 'syl', '( %s -> G : NN --> RR )' % PA), w.s([], 'simpr', '( %s -> a e. NN )' % PA)], 'ffvelcdmd', '( %s -> ( G ` a ) e. RR )' % PA)
    mlv = D(w, PA, 'remulcld', [gar, w.s([alr], 'adantr', '( %s -> ( abs ` %s ) e. RR )' % (PA, L))], '( ( G ` a ) x. ( abs ` %s ) ) e. RR' % L)
    mlf = w.s([mlv, w.s([], 'eqid', '%s = %s' % (ML, ML))], 'fmptd', '( ph -> %s : NN --> RR )' % ML)

    def mlval(j):
        PJ = '( ph /\\ %s e. NN )' % j
        sub = w.s([w.s([], 'fveq2', '( a = %s -> ( G ` a ) = ( G ` %s ) )' % (j, j))], 'oveq1d', '( a = %s -> ( ( G ` a ) x. ( abs ` %s ) ) = ( ( G ` %s ) x. ( abs ` %s ) ) )' % (j, L, j, L))
        return w.s([w.s([w.s([], 'eqid', '%s = %s' % (ML, ML))], 'a1i', '( %s -> %s = %s )' % (PJ, ML, ML)), w.s([sub], 'adantl', '( ( %s /\\ a = %s ) -> ( ( G ` a ) x. ( abs ` %s ) ) = ( ( G ` %s ) x. ( abs ` %s ) ) )' % (PJ, j, L, j, L)),
                    w.s([], 'simpr', '( %s -> %s e. NN )' % (PJ, j)), w.s([w.s([], 'ovex', '( ( G ` %s ) x. ( abs ` %s ) ) e. _V' % (j, L))], 'a1i', '( %s -> ( ( G ` %s ) x. ( abs ` %s ) ) e. _V )' % (PJ, j, L))],
                   'fvmptd', '( %s -> ( %s ` %s ) = ( ( G ` %s ) x. ( abs ` %s ) ) )' % (PJ, ML, j, j, L))

    # G ( j ) >_ 0 (the bound at the segment's start point, t = 0 is not in U: use A itself)
    PJ = '( ph /\\ j e. NN )'
    pj = w.s([], 'simpl', '( %s -> ph )' % PJ)
    ain = w.s([w.s([pj, ac], 'syl', '( %s -> A e. CC )' % PJ), w.s([pj, bc], 'syl', '( %s -> B e. CC )' % PJ), w.inst('csegid1')], 'syl2anc', '( %s -> A e. %s )' % (PJ, SEG))
    sbj = w.s([w.s([w.s([w.s([], 'fveq2', '( k = j -> ( F ` k ) = ( F ` j ) )')], 'fveq1d', '( k = j -> ( ( F ` k ) ` z ) = ( ( F ` j ) ` z ) )')], 'fveq2d',
                    '( k = j -> ( abs ` ( ( F ` k ) ` z ) ) = ( abs ` ( ( F ` j ) ` z ) ) )'), w.s([], 'fveq2', '( k = j -> ( G ` k ) = ( G ` j ) )')], 'breq12d',
              '( k = j -> ( ( abs ` ( ( F ` k ) ` z ) ) <_ ( G ` k ) <-> ( abs ` ( ( F ` j ) ` z ) ) <_ ( G ` j ) ) )')
    sba = w.s([w.s([w.s([], 'fveq2', '( z = A -> ( ( F ` j ) ` z ) = ( ( F ` j ) ` A ) )')], 'fveq2d', '( z = A -> ( abs ` ( ( F ` j ) ` z ) ) = ( abs ` ( ( F ` j ) ` A ) ) )')], 'breq1d',
              '( z = A -> ( ( abs ` ( ( F ` j ) ` z ) ) <_ ( G ` j ) <-> ( abs ` ( ( F ` j ) ` A ) ) <_ ( G ` j ) ) )')
    bja = w.s([w.s([w.s([], 'simpr', '( %s -> j e. NN )' % PJ), ain], 'jca', '( %s -> ( j e. NN /\\ A e. %s ) )' % (PJ, SEG)), w.s([pj, r4], 'syl', '( %s -> %s )' % (PJ, R4)),
               w.s([sbj, sba], 'rspc2v', '( ( j e. NN /\\ A e. %s ) -> ( %s -> ( abs ` ( ( F ` j ) ` A ) ) <_ ( G ` j ) ) )' % (SEG, R4))], 'sylc', '( %s -> ( abs ` ( ( F ` j ) ` A ) ) <_ ( G ` j ) )' % PJ)
    fjc = w.s([w.s([w.s([w.s([pj, ff], 'syl', '( %s -> F : NN --> ( D -cn-> CC ) )' % PJ), w.s([], 'simpr', '( %s -> j e. NN )' % PJ)], 'ffvelcdmd', '( %s -> ( F ` j ) e. ( D -cn-> CC ) )' % PJ),
                     w.inst('cncff')], 'syl', '( %s -> ( F ` j ) : D --> CC )' % PJ), w.s([w.s([pj, sd], 'syl', '( %s -> %s C_ D )' % (PJ, SEG)), ain], 'sseldd', '( %s -> A e. D )' % PJ)], 'ffvelcdmd',
              '( %s -> ( ( F ` j ) ` A ) e. CC )' % PJ)
    gjr = w.s([w.s([pj, gf], 'syl', '( %s -> G : NN --> RR )' % PJ), w.s([], 'simpr', '( %s -> j e. NN )' % PJ)], 'ffvelcdmd', '( %s -> ( G ` j ) e. RR )' % PJ)
    gj0 = w.s([a1(w, PJ, '0re', '0 e. RR'), D(w, PJ, 'abscld', [fjc], '( abs ` ( ( F ` j ) ` A ) ) e. RR'), gjr, D(w, PJ, 'absge0d', [fjc], '0 <_ ( abs ` ( ( F ` j ) ` A ) )'), bja],
              'letrd', '( %s -> 0 <_ ( G ` j ) )' % PJ)
    # the uniform bound
    hj, vj = hval('j', 'y')
    CJ = vj['C']
    ab1 = w.s([w.s([hj], 'fveq2d', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s ) )' % (CJ, H, TK('j', 'y'))),
               D(w, CJ, 'absmuld', [vj['val'], vj['lc']], '( abs ` %s ) = ( ( abs ` ( ( F ` j ) ` %s ) ) x. ( abs ` %s ) )' % (TK('j', 'y'), ZP('y'), L))], 'eqtrd',
              '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) = ( ( abs ` ( ( F ` j ) ` %s ) ) x. ( abs ` %s ) ) )' % (CJ, H, ZP('y'), L))
    gjrc = w.s([gjr], 'adantr', '( %s -> ( G ` j ) e. RR )' % CJ)
    ab2 = D(w, CJ, 'lemul1ad', [D(w, CJ, 'abscld', [vj['val']], '( abs ` ( ( F ` j ) ` %s ) ) e. RR' % ZP('y')), gjrc, w.s([vj['ph'], alr], 'syl', '( %s -> ( abs ` %s ) e. RR )' % (CJ, L)),
                                  w.s([vj['ph'], al0], 'syl', '( %s -> 0 <_ ( abs ` %s ) )' % (CJ, L)), vj['bnd']],
            '( ( abs ` ( ( F ` j ) ` %s ) ) x. ( abs ` %s ) ) <_ ( ( G ` j ) x. ( abs ` %s ) )' % (ZP('y'), L, L))
    ab3 = w.s([w.s([mlval('j')], 'adantr', '( %s -> ( %s ` j ) = ( ( G ` j ) x. ( abs ` %s ) ) )' % (CJ, ML, L))], 'eqcomd', '( %s -> ( ( G ` j ) x. ( abs ` %s ) ) = ( %s ` j ) )' % (CJ, L, ML))
    bnd = w.s([w.s([ab1, ab2], 'eqbrtrd', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( ( G ` j ) x. ( abs ` %s ) ) )' % (CJ, H, L)), ab3], 'breqtrd',
              '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (CJ, H, ML))
    bndr = w.s([w.s([bnd], 'anasss', '( ( ph /\\ ( j e. NN /\\ y e. %s ) ) -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (U, H, ML))], 'ralrimivva',
               '( ph -> A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (U, H, ML))
    # seq M' converges
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = a1(w, ph, '1nn', '1 e. NN')
    mlc = w.s([w.s([w.s([pj, mlf], 'syl', '( %s -> %s : NN --> RR )' % (PJ, ML)), w.s([], 'simpr', '( %s -> j e. NN )' % PJ)], 'ffvelcdmd', '( %s -> ( %s ` j ) e. RR )' % (PJ, ML))],
              'recnd', '( %s -> ( %s ` j ) e. CC )' % (PJ, ML))
    PJU = '( ph /\\ j e. ( ZZ>= ` 1 ) )'
    jn = w.s([w.s([], 'simpr', '( %s -> j e. ( ZZ>= ` 1 ) )' % PJU), w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> j e. NN )' % PJU)
    toPJ = w.s([w.s([], 'simpl', '( %s -> ph )' % PJU), jn], 'jca', '( %s -> %s )' % (PJU, PJ))
    mljv = mlval('j')
    GJL = '( ( G ` j ) x. ( abs ` %s ) )' % L
    gjl0 = D(w, PJ, 'mulge0d', [gjr, w.s([pj, alr], 'syl', '( %s -> ( abs ` %s ) e. RR )' % (PJ, L)), gj0, w.s([pj, al0], 'syl', '( %s -> 0 <_ ( abs ` %s ) )' % (PJ, L))], '0 <_ %s' % GJL)
    gjlr = D(w, PJ, 'remulcld', [gjr, w.s([pj, alr], 'syl', '( %s -> ( abs ` %s ) e. RR )' % (PJ, L))], '%s e. RR' % GJL)
    abm = w.s([w.s([mljv], 'fveq2d', '( %s -> ( abs ` ( %s ` j ) ) = ( abs ` %s ) )' % (PJ, ML, GJL)), D(w, PJ, 'absidd', [gjlr, gjl0], '( abs ` %s ) = %s' % (GJL, GJL)),
               D(w, PJ, 'mulcomd', [D(w, PJ, 'recnd', [gjr], '( G ` j ) e. CC'), D(w, PJ, 'recnd', [w.s([pj, alr], 'syl', '( %s -> ( abs ` %s ) e. RR )' % (PJ, L))], '( abs ` %s ) e. CC' % L)],
                 '%s = ( ( abs ` %s ) x. ( G ` j ) )' % (GJL, L))], '3eqtrd', '( %s -> ( abs ` ( %s ` j ) ) = ( ( abs ` %s ) x. ( G ` j ) ) )' % (PJ, ML, L))
    abr = w.s([w.s([mlc], 'abscld', '( %s -> ( abs ` ( %s ` j ) ) e. RR )' % (PJ, ML)), abm], 'eqled', '( %s -> ( abs ` ( %s ` j ) ) <_ ( ( abs ` %s ) x. ( G ` j ) ) )' % (PJ, ML, L))
    abru = w.s([toPJ, abr], 'syl', '( %s -> ( abs ` ( %s ` j ) ) <_ ( ( abs ` %s ) x. ( G ` j ) ) )' % (PJU, ML, L))
    mlcv = w.s([nnz, one, gjr, mlc, gcv, alr, abru], 'cvgcmpce', '( ph -> seq 1 ( + , %s ) e. dom ~~> )' % ML)
    UHM = '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (ML, ML, U, H, ML)
    uhm = D(w, ph, '3jca', [mlf, mlcv, bndr], UHM)
    GT = '( t e. %s |-> sum_ k e. NN ( ( %s ` k ) ` t ) )' % (U, H)
    SQ = 'seq 1 ( oF + , %s )' % H
    ulm = w.s([hf, uhm, w.inst('uhlim')], 'syl2anc', '( ph -> %s ( ~~>u ` %s ) %s )' % (SQ, U, GT))
    PSUM = lambda n: 'sum_ k e. ( 1 ... %s ) ( ( %s ` k ) ` t )' % (n, H)
    PN = '( ph /\\ n e. NN )'
    sqf = w.s([hf, w.inst('uhpsf')], 'syl', '( ph -> %s : NN --> ( CC ^m %s ) )' % (SQ, U))
    sqe = w.s([sqf], 'feqmptd', '( ph -> %s = ( n e. NN |-> ( %s ` n ) ) )' % (SQ, SQ))
    sqn = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % PN), hf], 'syl', '( %s -> %s : NN --> ( CC ^m %s ) )' % (PN, H, U)), w.s([], 'simpr', '( %s -> n e. NN )' % PN), w.inst('uhps')], 'syl2anc',
              '( %s -> ( %s ` n ) = ( t e. %s |-> %s ) )' % (PN, SQ, U, PSUM('n')))
    SQM = '( n e. NN |-> ( t e. %s |-> %s ) )' % (U, PSUM('n'))
    sqe2 = w.s([sqe, w.s([sqn], 'mpteq2dva', '( ph -> ( n e. NN |-> ( %s ` n ) ) = %s )' % (SQ, SQM))], 'eqtrd', '( ph -> %s = %s )' % (SQ, SQM))
    ulm2 = w.s([sqe2, ulm], 'eqbrtrrd', '( ph -> %s ( ~~>u ` %s ) %s )' % (SQM, U, GT))

    def hv_at(C, toC):
        """( C -> ( ( H ` k ) ` t ) = TK ( k , t ) ) from toC: ( C -> ( ( ph /\\ k e. NN ) /\\ t e. U ) )"""
        e, _v = hval('k', 't')
        return w.s([toC, e], 'syl', '( %s -> ( ( %s ` k ) ` t ) = %s )' % (C, H, TK('k', 't')))

    def fsumblk(n):
        """under PN = ( ph /\\ n e. NN ): L^1 and value of the partial sum, and each term's integral as a line integral"""
        PN_ = '( ph /\\ %s e. NN )' % n
        PNK = '( %s /\\ k e. ( 1 ... %s ) )' % (PN_, n)
        kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... %s ) )' % (PNK, n)), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % PNK)
        php = w.s([], 'simpll', '( %s -> ph )' % PNK)
        CT = '( %s /\\ t e. %s )' % (PNK, U)
        toC = w.s([w.s([w.s([php], 'adantr', '( %s -> ph )' % CT), w.s([kn], 'adantr', '( %s -> k e. NN )' % CT)], 'jca', '( %s -> ( ph /\\ k e. NN ) )' % CT),
                   w.s([], 'simpr', '( %s -> t e. %s )' % (CT, U))], 'jca', '( %s -> ( ( ph /\\ k e. NN ) /\\ t e. %s ) )' % (CT, U))
        hvk = hv_at(CT, toC)
        mq = w.s([hvk], 'mpteq2dva', '( %s -> ( t e. %s |-> ( ( %s ` k ) ` t ) ) = ( t e. %s |-> %s ) )' % (PNK, U, H, U, TK('k', 't')))
        fkc = w.s([w.s([php, ff], 'syl', '( %s -> F : NN --> ( D -cn-> CC ) )' % PNK), kn], 'ffvelcdmd', '( %s -> ( F ` k ) e. ( D -cn-> CC ) )' % PNK)
        lh = D(w, PNK, 'jca', [w.s([php, 'h1'], 'syl', '( %s -> ( A e. CC /\\ B e. CC ) )' % PNK), D(w, PNK, 'jca', [fkc, w.s([php, sd], 'syl', '( %s -> %s C_ D )' % (PNK, SEG))],
                                                                                                         '( ( F ` k ) e. ( D -cn-> CC ) /\\ %s C_ D )' % SEG)],
               '( ( A e. CC /\\ B e. CC ) /\\ ( ( F ` k ) e. ( D -cn-> CC ) /\\ %s C_ D ) )' % SEG)
        ibk = w.s([lh, w.inst('lintibl')], 'syl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (PNK, U, TK('k', 't')))
        ibh = w.s([mq, ibk], 'eqeltrd', '( %s -> ( t e. %s |-> ( ( %s ` k ) ` t ) ) e. L^1 )' % (PNK, U, H))
        CV = '( %s /\\ ( t e. %s /\\ k e. ( 1 ... %s ) ) )' % (PN_, U, n)
        cv = w.s([w.s([], 'fvex', '( ( %s ` k ) ` t ) e. _V' % H)], 'a1i', '( %s -> ( ( %s ` k ) ` t ) e. _V )' % (CV, H))
        fs = w.s([w.s([umb], 'adantr', '( %s -> %s e. dom vol )' % (PN_, U)), w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (PN_, n)), cv, ibh], 'itgfsum',
                 '( %s -> ( ( t e. %s |-> %s ) e. L^1 /\\ S. %s %s _d t = sum_ k e. ( 1 ... %s ) S. %s ( ( %s ` k ) ` t ) _d t ) )' % (PN_, U, PSUM(n), U, PSUM(n), n, U, H))
        # each term's integral is the line integral of F ( k )
        ie = w.s([hvk], 'itgeq2dv', '( %s -> S. %s ( ( %s ` k ) ` t ) _d t = S. %s %s _d t )' % (PNK, U, H, U, TK('k', 't')))
        lv = w.s([w.s([fkc, w.s([php, ac], 'syl', '( %s -> A e. CC )' % PNK), w.s([php, bc], 'syl', '( %s -> B e. CC )' % PNK)], '3jca',
                      '( %s -> ( ( F ` k ) e. ( D -cn-> CC ) /\\ A e. CC /\\ B e. CC ) )' % PNK), w.inst('lintval')], 'syl',
                 '( %s -> ( ( F ` k ) lint <. A , B >. ) = S. %s %s _d t )' % (PNK, U, TK('k', 't')))
        tl = w.s([ie, lv], 'eqtr4d', '( %s -> S. %s ( ( %s ` k ) ` t ) _d t = ( ( F ` k ) lint <. A , B >. ) )' % (PNK, U, H))
        lcl = w.s([lh, w.inst('lintcl')], 'syl', '( %s -> ( ( F ` k ) lint <. A , B >. ) e. CC )' % PNK)
        return fs, tl, lcl, kn, php

    fsn, _tl, _lcl, _kn, _php = fsumblk('n')
    lpn = w.s([fsn], 'simpld', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (PN, U, PSUM('n')))
    iu = w.s([nnz, a1(w, ph, '1z', '1 e. ZZ'), lpn, ulm2, uvr], 'itgulm2',
             '( ph -> ( %s e. L^1 /\\ ( n e. NN |-> S. %s %s _d t ) ~~> S. %s sum_ k e. NN ( ( %s ` k ) ` t ) _d t ) )' % (GT, U, PSUM('n'), U, H))
    # identify ( n |-> S. U PSUM ( n ) ) with the partial sums of the line integrals
    LK = '( k e. NN |-> ( ( F ` k ) lint <. A , B >. ) )'
    PI = '( ph /\\ i e. NN )'
    fsi, tli, lcli, kni, phpi = fsumblk('i')
    PIK = '( %s /\\ k e. ( 1 ... i ) )' % PI
    IM = '( n e. NN |-> S. %s %s _d t )' % (U, PSUM('n'))
    subn = w.s([w.s([w.s([w.s([], 'oveq2', '( n = i -> ( 1 ... n ) = ( 1 ... i ) )')], 'sumeq1d', '( n = i -> %s = %s )' % (PSUM('n'), PSUM('i')))], 'adantr',
                    '( ( n = i /\\ t e. %s ) -> %s = %s )' % (U, PSUM('n'), PSUM('i')))], 'itgeq2dv', '( n = i -> S. %s %s _d t = S. %s %s _d t )' % (U, PSUM('n'), U, PSUM('i')))
    e1 = w.s([w.s([w.s([], 'eqid', '%s = %s' % (IM, IM))], 'a1i', '( %s -> %s = %s )' % (PI, IM, IM)), w.s([subn], 'adantl', '( ( %s /\\ n = i ) -> S. %s %s _d t = S. %s %s _d t )' % (PI, U, PSUM('n'), U, PSUM('i'))),
              w.s([], 'simpr', '( %s -> i e. NN )' % PI), w.s([w.s([], 'itgex', 'S. %s %s _d t e. _V' % (U, PSUM('i')))], 'a1i', '( %s -> S. %s %s _d t e. _V )' % (PI, U, PSUM('i')))],
             'fvmptd', '( %s -> ( %s ` i ) = S. %s %s _d t )' % (PI, IM, U, PSUM('i')))
    e2 = w.s([fsi], 'simprd', '( %s -> S. %s %s _d t = sum_ k e. ( 1 ... i ) S. %s ( ( %s ` k ) ` t ) _d t )' % (PI, U, PSUM('i'), U, H))
    e3 = w.s([tli], 'sumeq2dv', '( %s -> sum_ k e. ( 1 ... i ) S. %s ( ( %s ` k ) ` t ) _d t = sum_ k e. ( 1 ... i ) ( ( F ` k ) lint <. A , B >. ) )' % (PI, U, H))
    LKm = '( m e. NN |-> ( ( F ` m ) lint <. A , B >. ) )'
    subl = w.s([w.s([], 'fveq2', '( m = k -> ( F ` m ) = ( F ` k ) )')], 'oveq1d', '( m = k -> ( ( F ` m ) lint <. A , B >. ) = ( ( F ` k ) lint <. A , B >. ) )')
    lkvi = w.s([w.s([w.s([], 'eqid', '%s = %s' % (LKm, LKm))], 'a1i', '( %s -> %s = %s )' % (PIK, LKm, LKm)),
                w.s([subl], 'adantl', '( ( %s /\\ m = k ) -> ( ( F ` m ) lint <. A , B >. ) = ( ( F ` k ) lint <. A , B >. ) )' % PIK), kni,
                w.s([w.s([], 'ovex', '( ( F ` k ) lint <. A , B >. ) e. _V')], 'a1i', '( %s -> ( ( F ` k ) lint <. A , B >. ) e. _V )' % PIK)], 'fvmptd',
               '( %s -> ( %s ` k ) = ( ( F ` k ) lint <. A , B >. ) )' % (PIK, LKm))
    iuz = w.s([w.s([], 'simpr', '( %s -> i e. NN )' % PI), w.s([], 'elnnuz', '( i e. NN <-> i e. ( ZZ>= ` 1 ) )')], 'sylib', '( %s -> i e. ( ZZ>= ` 1 ) )' % PI)
    e4 = w.s([lkvi, iuz, lcli], 'fsumser', '( %s -> sum_ k e. ( 1 ... i ) ( ( F ` k ) lint <. A , B >. ) = ( seq 1 ( + , %s ) ` i ) )' % (PI, LKm))
    ide = chain(w, PI, ['( %s ` i )' % IM, 'S. %s %s _d t' % (U, PSUM('i')), 'sum_ k e. ( 1 ... i ) S. %s ( ( %s ` k ) ` t ) _d t' % (U, H),
                        'sum_ k e. ( 1 ... i ) ( ( F ` k ) lint <. A , B >. )', '( seq 1 ( + , %s ) ` i )' % LKm], [e1, e2, e3, e4])
    LIM = 'S. %s sum_ k e. NN ( ( %s ` k ) ` t ) _d t' % (U, H)
    ceq = w.s([nnz, w.s([w.s([w.s([], 'nnex', 'NN e. _V'), w.inst('mptexg')], 'ax-mp', '%s e. _V' % IM)], 'a1i', '( ph -> %s e. _V )' % IM),
               w.s([w.s([], 'seqex', 'seq 1 ( + , %s ) e. _V' % LKm)], 'a1i', '( ph -> seq 1 ( + , %s ) e. _V )' % LKm), a1(w, ph, '1z', '1 e. ZZ'), ide], 'climeq',
              '( ph -> ( %s ~~> %s <-> seq 1 ( + , %s ) ~~> %s ) )' % (IM, LIM, LKm, LIM))
    cv0 = w.s([w.s([iu], 'simprd', '( ph -> %s ~~> %s )' % (IM, LIM)), ceq], 'mpbid', '( ph -> seq 1 ( + , %s ) ~~> %s )' % (LKm, LIM))
    cbl = w.s([w.s([w.s([subl], 'cbvmptv', '%s = %s' % (LKm, LK)), w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (LKm, LK))], 'a1i',
              '( ph -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (LKm, LK))
    cv1 = w.s([cbl, cv0], 'eqbrtrrd', '( ph -> seq 1 ( + , %s ) ~~> %s )' % (LK, LIM))
    # the limit is the line integral of the pointwise sum
    GS = '( z e. D |-> sum_ k e. NN ( ( F ` k ) ` z ) )'
    PT = '( ph /\\ t e. %s )' % U
    ZT = ZP('t')
    vk = pt('k', 't')
    hk, _v2 = hval('k', 't')
    hk2 = w.s([hk], 'an32s', '( ( %s /\\ k e. NN ) -> ( ( %s ` k ) ` t ) = %s )' % (PT, H, TK('k', 't')))
    s1 = w.s([hk2], 'sumeq2dv', '( %s -> sum_ k e. NN ( ( %s ` k ) ` t ) = sum_ k e. NN %s )' % (PT, H, TK('k', 't')))
    FM = '( m e. NN |-> ( ( F ` m ) ` %s ) )' % ZT
    PTK = '( %s /\\ k e. NN )' % PT
    subm = w.s([w.s([], 'fveq2', '( m = k -> ( F ` m ) = ( F ` k ) )')], 'fveq1d', '( m = k -> ( ( F ` m ) ` %s ) = ( ( F ` k ) ` %s ) )' % (ZT, ZT))
    valk = w.s([vk['val']], 'an32s', '( %s -> ( ( F ` k ) ` %s ) e. CC )' % (PTK, ZT))
    fmk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (FM, FM))], 'a1i', '( %s -> %s = %s )' % (PTK, FM, FM)), w.s([subm], 'adantl', '( ( %s /\\ m = k ) -> ( ( F ` m ) ` %s ) = ( ( F ` k ) ` %s ) )' % (PTK, ZT, ZT)),
               w.s([], 'simpr', '( %s -> k e. NN )' % PTK), valk], 'fvmptd', '( %s -> ( %s ` k ) = ( ( F ` k ) ` %s ) )' % (PTK, FM, ZT))
    # convergence of the pointwise series (comparison with G)
    vj2 = pt('j', 't')
    PTJ = '( %s /\\ j e. NN )' % PT
    valj = w.s([vj2['val']], 'an32s', '( %s -> ( ( F ` j ) ` %s ) e. CC )' % (PTJ, ZT))
    subj = w.s([w.s([], 'fveq2', '( m = j -> ( F ` m ) = ( F ` j ) )')], 'fveq1d', '( m = j -> ( ( F ` m ) ` %s ) = ( ( F ` j ) ` %s ) )' % (ZT, ZT))
    fmj = w.s([w.s([w.s([], 'eqid', '%s = %s' % (FM, FM))], 'a1i', '( %s -> %s = %s )' % (PTJ, FM, FM)), w.s([subj], 'adantl', '( ( %s /\\ m = j ) -> ( ( F ` m ) ` %s ) = ( ( F ` j ) ` %s ) )' % (PTJ, ZT, ZT)),
               w.s([], 'simpr', '( %s -> j e. NN )' % PTJ), valj], 'fvmptd', '( %s -> ( %s ` j ) = ( ( F ` j ) ` %s ) )' % (PTJ, FM, ZT))
    fmjc = w.s([fmj, valj], 'eqeltrd', '( %s -> ( %s ` j ) e. CC )' % (PTJ, FM))
    gjt = w.s([w.s([w.s([], 'simpll', '( %s -> ph )' % PTJ), gf], 'syl', '( %s -> G : NN --> RR )' % PTJ), w.s([], 'simpr', '( %s -> j e. NN )' % PTJ)], 'ffvelcdmd', '( %s -> ( G ` j ) e. RR )' % PTJ)
    bj = w.s([vj2['bnd']], 'an32s', '( %s -> ( abs ` ( ( F ` j ) ` %s ) ) <_ ( G ` j ) )' % (PTJ, ZT))
    bj2 = w.s([w.s([fmj], 'fveq2d', '( %s -> ( abs ` ( %s ` j ) ) = ( abs ` ( ( F ` j ) ` %s ) ) )' % (PTJ, FM, ZT)), bj], 'eqbrtrd', '( %s -> ( abs ` ( %s ` j ) ) <_ ( G ` j ) )' % (PTJ, FM))
    bj3 = w.s([bj2, w.s([w.s([D(w, PTJ, 'recnd', [gjt], '( G ` j ) e. CC')], 'mullidd', '( %s -> ( 1 x. ( G ` j ) ) = ( G ` j ) )' % PTJ)], 'eqcomd', '( %s -> ( G ` j ) = ( 1 x. ( G ` j ) ) )' % PTJ)],
              'breqtrd', '( %s -> ( abs ` ( %s ` j ) ) <_ ( 1 x. ( G ` j ) ) )' % (PTJ, FM))
    PTJU = '( %s /\\ j e. ( ZZ>= ` 1 ) )' % PT
    jn2 = w.s([w.s([], 'simpr', '( %s -> j e. ( ZZ>= ` 1 ) )' % PTJU), w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> j e. NN )' % PTJU)
    bj4 = w.s([w.s([], 'simpl', '( %s -> %s )' % (PTJU, PT)), jn2, w.s([bj3], 'ex', '( %s -> ( j e. NN -> ( abs ` ( %s ` j ) ) <_ ( 1 x. ( G ` j ) ) ) )' % (PT, FM))], 'sylc',
              '( %s -> ( abs ` ( %s ` j ) ) <_ ( 1 x. ( G ` j ) ) )' % (PTJU, FM))
    ptph = w.s([], 'simpl', '( %s -> ph )' % PT)
    fmcv = w.s([nnz, a1(w, PT, '1nn', '1 e. NN'), gjt, fmjc, w.s([ptph, gcv], 'syl', '( %s -> seq 1 ( + , G ) e. dom ~~> )' % PT), a1(w, PT, '1re', '1 e. RR'), bj4], 'cvgcmpce',
               '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (PT, FM))
    SK = 'sum_ k e. NN ( ( F ` k ) ` %s )' % ZT
    im1 = w.s([nnz, a1(w, PT, '1z', '1 e. ZZ'), fmk, valk, fmcv, w.s([ptph, lc], 'syl', '( %s -> %s e. CC )' % (PT, L))], 'isummulc1',
              '( %s -> ( %s x. %s ) = sum_ k e. NN %s )' % (PT, SK, L, TK('k', 't')))
    # ( GS ` ZT ) = SK
    subz = w.s([w.s([w.s([], 'fveq2', '( z = %s -> ( ( F ` k ) ` z ) = ( ( F ` k ) ` %s ) )' % (ZT, ZT))], 'adantr', '( ( z = %s /\\ k e. NN ) -> ( ( F ` k ) ` z ) = ( ( F ` k ) ` %s ) )' % (ZT, ZT))],
               'sumeq2dv', '( z = %s -> sum_ k e. NN ( ( F ` k ) ` z ) = %s )' % (ZT, SK))
    t01 = w.s([a1(w, PT, 'ioossicc', '%s C_ ( 0 [,] 1 )' % U), w.s([], 'simpr', '( %s -> t e. %s )' % (PT, U))], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % PT)
    zts = w.s([w.s([ptph, ac], 'syl', '( %s -> A e. CC )' % PT), w.s([ptph, bc], 'syl', '( %s -> B e. CC )' % PT), t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. %s )' % (PT, ZT, SEG))
    ztd = w.s([w.s([ptph, sd], 'syl', '( %s -> %s C_ D )' % (PT, SEG)), zts], 'sseldd', '( %s -> %s e. D )' % (PT, ZT))
    gsv = w.s([w.s([w.s([], 'eqid', '%s = %s' % (GS, GS))], 'a1i', '( %s -> %s = %s )' % (PT, GS, GS)), w.s([subz], 'adantl', '( ( %s /\\ z = %s ) -> sum_ k e. NN ( ( F ` k ) ` z ) = %s )' % (PT, ZT, SK)),
               ztd, w.s([w.s([], 'sumex', '%s e. _V' % SK)], 'a1i', '( %s -> %s e. _V )' % (PT, SK))], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (PT, GS, ZT, SK))
    pw = chain(w, PT, ['sum_ k e. NN ( ( %s ` k ) ` t )' % H, 'sum_ k e. NN %s' % TK('k', 't'), '( %s x. %s )' % (SK, L), '( ( %s ` %s ) x. %s )' % (GS, ZT, L)],
               [s1, ('r', im1), w.s([w.s([gsv], 'eqcomd', '( %s -> %s = ( %s ` %s ) )' % (PT, SK, GS, ZT))], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( %s ` %s ) x. %s ) )' % (PT, SK, L, GS, ZT, L))])
    lie = w.s([pw], 'itgeq2dv', '( ph -> %s = S. %s ( ( %s ` %s ) x. %s ) _d t )' % (LIM, U, GS, ZT, L))
    f1 = w.s([ff, one], 'ffvelcdmd', '( ph -> ( F ` 1 ) e. ( D -cn-> CC ) )')
    dcc = w.s([f1, w.inst('cncfrss')], 'syl', '( ph -> D C_ CC )')
    dex = w.s([dcc, a1(w, ph, 'cnex', 'CC e. _V'), w.inst('ssexg')], 'syl2anc', '( ph -> D e. _V )')
    gse = w.s([dex, w.inst('mptexg')], 'syl', '( ph -> %s e. _V )' % GS)
    lvg = w.s([gse, ac, bc, w.inst('lintval')], 'syl3anc', '( ph -> ( %s lint <. A , B >. ) = S. %s ( ( %s ` %s ) x. %s ) _d t )' % (GS, U, GS, ZT, L))
    lim = w.s([lie, lvg], 'eqtr4d', '( ph -> %s = ( %s lint <. A , B >. ) )' % (LIM, GS))
    w.qed([cv1, lim], 'breqtrd', STATEMENTS['ef1lser'])
    go(w, only)


# ---------------------------------------------------------------- ef1redge: integral_right_edge
if __name__ == '__main__' and (not only or 'ef1redge' in only):
    w = W('ef1redge', 'The right edge of the Perron contour: on ` Re s = C > 1 ` the line integral of '
          '` ( sum_ k chi ( k ) Lam ( k ) k ^ -s ) y ^ s / s ` is the Perron-weighted sum ` sum_ n chi ( n ) Lam ( n ) K ( y / n ) ` , '
          'and that series converges (Lean ` integral_right_edge ` , ` summable_perron_term ` ; the kernel line is ` 2 pi i ` times '
          'Lean\'s ` perronKernel ` ; the integrand is ` -L\'/L ( s ) y ^ s / s ` by ~ lchrlogdv ).  By ~ ef1lser : no dominated convergence.')
    A0 = STATEMENTS['ef1redge'].split(' -> ( seq 1')[0][2:]
    D0 = '( CC \\ { 0 } )'
    LOs, HIs = LO(), HI()
    SEGL = '( %s cseg %s )' % (LOs, HIs)
    nx = D(w, A0, 'simpl', [], NX)
    yrp = D(w, A0, 'simprl1', [], 'Y e. RR+'); cr = D(w, A0, 'simprl2', [], 'C e. RR'); c1 = D(w, A0, 'simprl3', [], '1 < C'); tr = D(w, A0, 'simprr', [], 'T e. RR')
    cl = Closure(w, A0, {'Y': ('RR+', yrp), 'C': ('RR', cr), 'T': ('RR', tr)})
    cpos = linarith(w, A0, [c1], '0 < C', closure=cl)
    crp = D(w, A0, 'elrpd', [cr, cpos], 'C e. RR+')
    cne = D(w, A0, 'rpne0d', [crp], 'C =/= 0')
    ntr = D(w, A0, 'renegcld', [tr], '-u T e. RR')
    loc = D(w, A0, 'addcld', [D(w, A0, 'recnd', [cr], 'C e. CC'), D(w, A0, 'mulcld', [a1(w, A0, 'ax-icn', '_i e. CC'), D(w, A0, 'recnd', [ntr], '-u T e. CC')], '( _i x. -u T ) e. CC')], '%s e. CC' % LOs)
    hic = D(w, A0, 'addcld', [D(w, A0, 'recnd', [cr], 'C e. CC'), D(w, A0, 'mulcld', [a1(w, A0, 'ax-icn', '_i e. CC'), D(w, A0, 'recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % HIs)
    rlo = w.s([cr, ntr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = C )' % (A0, LOs))
    rhi = w.s([cr, tr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = C )' % (A0, HIs))
    rvre = w.s([loc, hic, w.s([rlo, rhi], 'eqtr4d', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A0, LOs, HIs)), w.inst('csegvre')], 'syl3anc',
               '( %s -> A. u e. %s ( Re ` u ) = ( Re ` %s ) )' % (A0, SEGL, LOs))
    rne0 = w.s([D(w, A0, 'jca', [D(w, A0, 'jca', [cr, cne], '( C e. RR /\\ C =/= 0 )'), D(w, A0, 'jca', [ntr, tr], '( -u T e. RR /\\ T e. RR )')],
                  '( ( C e. RR /\\ C =/= 0 ) /\\ ( -u T e. RR /\\ T e. RR ) )'), w.inst('csegne0')], 'syl', '( %s -> A. u e. %s u e. %s )' % (A0, SEGL, D0))
    segss = w.s([rne0, w.s([], 'dfss3', '( %s C_ %s <-> A. u e. %s u e. %s )' % (SEGL, D0, SEGL, D0))], 'sylibr', '( %s -> %s C_ %s )' % (A0, SEGL, D0))

    def segpt(C, to0, umem, u):
        """under C with to0: ( C -> A0 ), umem: ( C -> u e. SEGL ): u e. CC, u =/= 0, Re u = C, 1 < Re u"""
        d = {}
        ud = w.s([w.s([to0, segss], 'syl', '( %s -> %s C_ %s )' % (C, SEGL, D0)), umem], 'sseldd', '( %s -> %s e. %s )' % (C, u, D0))
        d['c'] = w.s([ud, w.inst('eldifi')], 'syl', '( %s -> %s e. CC )' % (C, u))
        d['ne'] = w.s([ud, w.inst('eldifsni')], 'syl', '( %s -> %s =/= 0 )' % (C, u))
        if u == 'u':
            AU0 = '( %s /\\ u e. %s )' % (A0, SEGL)
            base = w.s([rvre], 'r19.21bi', '( %s -> ( Re ` u ) = ( Re ` %s ) )' % (AU0, LOs))
            re0 = w.s([D(w, C, 'jca', [to0, umem], AU0), base], 'syl', '( %s -> ( Re ` u ) = ( Re ` %s ) )' % (C, LOs))
        else:
            sb = w.s([w.s([], 'fveq2', '( u = %s -> ( Re ` u ) = ( Re ` %s ) )' % (u, u))], 'eqeq1d', '( u = %s -> ( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` %s ) = ( Re ` %s ) ) )' % (u, LOs, u, LOs))
            re0 = w.s([sb, w.s([to0, rvre], 'syl', '( %s -> A. u e. %s ( Re ` u ) = ( Re ` %s ) )' % (C, SEGL, LOs)), umem], 'rspcdva', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (C, u, LOs))
        d['re'] = w.s([re0, w.s([to0, rlo], 'syl', '( %s -> ( Re ` %s ) = C )' % (C, LOs))], 'eqtrd', '( %s -> ( Re ` %s ) = C )' % (C, u))
        d['gt'] = w.s([w.s([to0, c1], 'syl', '( %s -> 1 < C )' % C), w.s([d['re']], 'eqcomd', '( %s -> C = ( Re ` %s ) )' % (C, u))], 'breqtrd', '( %s -> 1 < ( Re ` %s ) )' % (C, u))
        d['d0'] = ud
        return d

    QM = '( q e. NN |-> %s )' % AN('q')

    def kfacts(C, to0, kn, k):
        d = {}
        qf = w.s([w.s([to0, nx], 'syl', '( %s -> %s )' % (C, NX)), w.inst('lchvmf')], 'syl', '( %s -> %s : NN --> CC )' % (C, QM))
        qv = w.s([kn, w.inst('lchvmval')], 'syl', '( %s -> ( %s ` %s ) = %s )' % (C, QM, k, AN(k)))
        d['an'] = w.s([qv, w.s([qf, kn], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (C, QM, k))], 'eqeltrrd', '( %s -> %s e. CC )' % (C, AN(k)))
        d['rp'] = D(w, C, 'nnrpd', [kn], '%s e. RR+' % k)
        d['c'] = D(w, C, 'rpcnd', [d['rp']], '%s e. CC' % k)
        d['ne'] = D(w, C, 'rpne0d', [d['rp']], '%s =/= 0' % k)
        d['lam'] = w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` %s ) e. RR )' % (C, k))
        d['lam0'] = w.s([kn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` %s ) )' % (C, k))
        return d

    def ident(C, to0, kd, k, ud, u):
        """( C -> ( AN(k) x. ( ( ( Y / k ) ^c u ) / u ) ) = ( ( AN(k) x. ( k ^c -u u ) ) x. ( ( Y ^c u ) / u ) ) )"""
        yrpc = w.s([to0, yrp], 'syl', '( %s -> Y e. RR+ )' % C)
        y0 = D(w, C, 'jca', [D(w, C, 'rpred', [yrpc], 'Y e. RR'), D(w, C, 'rpge0d', [yrpc], '0 <_ Y')], '( Y e. RR /\\ 0 <_ Y )')
        dv = w.s([y0, kd['rp'], ud['c'], w.inst('divcxp')], 'syl3anc', '( %s -> ( ( Y / %s ) ^c %s ) = ( ( Y ^c %s ) / ( %s ^c %s ) ) )' % (C, k, u, u, k, u))
        cn = w.s([kd['c'], kd['ne'], ud['c'], w.inst('cxpneg')], 'syl3anc', '( %s -> ( %s ^c -u %s ) = ( 1 / ( %s ^c %s ) ) )' % (C, k, u, k, u))
        YU = '( Y ^c %s )' % u; KU = '( %s ^c %s )' % (k, u); KN = '( %s ^c -u %s )' % (k, u); YUu = '( %s / %s )' % (YU, u)
        yuc = D(w, C, 'cxpcld', [D(w, C, 'rpcnd', [yrpc], 'Y e. CC'), ud['c']], '%s e. CC' % YU)
        kuc = D(w, C, 'cxpcld', [kd['c'], ud['c']], '%s e. CC' % KU)
        kun = w.s([kd['c'], kd['ne'], ud['c'], w.inst('cxpne0')], 'syl3anc', '( %s -> %s =/= 0 )' % (C, KU))
        knc = D(w, C, 'cxpcld', [kd['c'], D(w, C, 'negcld', [ud['c']], '-u %s e. CC' % u)], '%s e. CC' % KN)
        yuuc = D(w, C, 'divcld', [yuc, ud['c'], ud['ne']], '%s e. CC' % YUu)
        Q0 = '( ( ( Y / %s ) ^c %s ) / %s )' % (k, u, u)
        q = chain(w, C, [Q0, '( ( %s / %s ) / %s )' % (YU, KU, u), '( %s / %s )' % (YUu, KU), '( %s x. ( 1 / %s ) )' % (YUu, KU), '( %s x. %s )' % (YUu, KN), '( %s x. %s )' % (KN, YUu)],
                  [w.s([dv], 'oveq1d', '( %s -> %s = ( ( %s / %s ) / %s ) )' % (C, Q0, YU, KU, u)),
                   D(w, C, 'divdiv32d', [yuc, kuc, ud['c'], kun, ud['ne']], '( ( %s / %s ) / %s ) = ( %s / %s )' % (YU, KU, u, YUu, KU)),
                   D(w, C, 'divrecd', [yuuc, kuc, kun], '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (YUu, KU, YUu, KU)),
                   w.s([w.s([cn], 'eqcomd', '( %s -> ( 1 / %s ) = %s )' % (C, KU, KN))], 'oveq2d', '( %s -> ( %s x. ( 1 / %s ) ) = ( %s x. %s ) )' % (C, YUu, KU, YUu, KN)),
                   D(w, C, 'mulcomd', [yuuc, knc], '( %s x. %s ) = ( %s x. %s )' % (YUu, KN, KN, YUu))])
        e1 = w.s([q], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (C, AN(k), Q0, AN(k), KN, YUu))
        e2 = D(w, C, 'mulassd', [kd['an'], knc, yuuc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (AN(k), KN, YUu, AN(k), KN, YUu))
        return w.s([e1, e2], 'eqtr4d', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) x. %s ) )' % (C, AN(k), Q0, AN(k), KN, YUu)), {'yuc': yuc, 'knc': knc, 'yuuc': yuuc, 'yrp': yrpc}

    d0e = w.s([w.s([], 'cnex', 'CC e. _V'), w.inst('difexg')], 'ax-mp', '%s e. _V' % D0)
    d0cc = a1(w, A0, 'difss', '%s C_ CC' % D0)
    FT = lambda k, x: '( %s x. ( ( ( Y / %s ) ^c %s ) / %s ) )' % (AN(k), k, x, x)
    FFK = lambda k: '( x e. %s |-> %s )' % (D0, FT(k, 'x'))
    PKX = lambda k: '( x e. %s |-> ( ( ( Y / %s ) ^c x ) / x ) )' % (D0, k)
    FF = '( n e. NN |-> %s )' % FFK('n')

    def ffkcn(C, to0, kd, k):
        yk = D(w, C, 'rpdivcld', [w.s([to0, yrp], 'syl', '( %s -> Y e. RR+ )' % C), kd['rp']], '( Y / %s ) e. RR+' % k)
        pk = w.s([D(w, C, 'jca', [yk, a1(w, C, 'ssid', '%s C_ %s' % (D0, D0))], '( ( Y / %s ) e. RR+ /\\ %s C_ %s )' % (k, D0, D0)), w.inst('pkfcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (C, PKX(k), D0))
        cs = w.s([kd['an'], a1(w, C, 'difss', '%s C_ CC' % D0), a1(w, C, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( %s -> ( x e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (C, D0, AN(k), D0))
        return w.s([cs, pk], 'mulcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (C, FFK(k), D0)), pk, yk

    def subk(k, n):
        """( k = n -> AN(k) = AN(n) )"""
        a = w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) = ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % (k, n, k, n))], 'fveq2d',
                     '( %s = %s -> %s = %s )' % (k, n, XC(k), XC(n))), w.s([], 'fveq2', '( %s = %s -> ( Lam ` %s ) = ( Lam ` %s ) )' % (k, n, k, n))], 'oveq12d', '( %s = %s -> %s = %s )' % (k, n, AN(k), AN(n)))
        return a

    def ffval(C, kn, k):
        """( C -> ( FF ` k ) = FFK ( k ) )"""
        yx = w.s([w.s([w.s([], 'oveq2', '( n = %s -> ( Y / n ) = ( Y / %s ) )' % (k, k))], 'oveq1d', '( n = %s -> ( ( Y / n ) ^c x ) = ( ( Y / %s ) ^c x ) )' % (k, k))], 'oveq1d',
                 '( n = %s -> ( ( ( Y / n ) ^c x ) / x ) = ( ( ( Y / %s ) ^c x ) / x ) )' % (k, k))
        bd = w.s([subk('n', k), yx], 'oveq12d', '( n = %s -> %s = %s )' % (k, FT('n', 'x'), FT(k, 'x')))
        sb = w.s([bd], 'mpteq2dv', '( n = %s -> %s = %s )' % (k, FFK('n'), FFK(k)))
        return w.s([w.s([w.s([], 'eqid', '%s = %s' % (FF, FF))], 'a1i', '( %s -> %s = %s )' % (C, FF, FF)), w.s([sb], 'adantl', '( ( %s /\\ n = %s ) -> %s = %s )' % (C, k, FFK('n'), FFK(k))), kn,
                    w.s([w.s([d0e, w.inst('mptexg')], 'ax-mp', '%s e. _V' % FFK(k))], 'a1i', '( %s -> %s e. _V )' % (C, FFK(k)))], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (C, FF, k, FFK(k)))

    def ffvv(C, kn, k, vd0, v):
        """( C -> ( ( FF ` k ) ` v ) = FT ( k , v ) ) from vd0: ( C -> v e. D0 )"""
        fk = ffval(C, kn, k)
        sb = w.s([w.s([], 'oveq2', '( x = %s -> ( ( Y / %s ) ^c x ) = ( ( Y / %s ) ^c %s ) )' % (v, k, k, v)), w.s([], 'id', '( x = %s -> x = %s )' % (v, v))], 'oveq12d',
                 '( x = %s -> ( ( ( Y / %s ) ^c x ) / x ) = ( ( ( Y / %s ) ^c %s ) / %s ) )' % (v, k, k, v, v))
        sb2 = w.s([sb], 'oveq2d', '( x = %s -> %s = %s )' % (v, FT(k, 'x'), FT(k, v)))
        vv = w.s([w.s([w.s([], 'eqid', '%s = %s' % (FFK(k), FFK(k)))], 'a1i', '( %s -> %s = %s )' % (C, FFK(k), FFK(k))), w.s([sb2], 'adantl', '( ( %s /\\ x = %s ) -> %s = %s )' % (C, v, FT(k, 'x'), FT(k, v))),
                  vd0, w.s([w.s([], 'ovex', '%s e. _V' % FT(k, v))], 'a1i', '( %s -> %s e. _V )' % (C, FT(k, v)))], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (C, FFK(k), v, FT(k, v)))
        return w.s([w.s([fk], 'fveq1d', '( %s -> ( ( %s ` %s ) ` %s ) = ( %s ` %s ) )' % (C, FF, k, v, FFK(k), v)), vv], 'eqtrd', '( %s -> ( ( %s ` %s ) ` %s ) = %s )' % (C, FF, k, v, FT(k, v)))

    # F : NN --> ( D0 -cn-> CC )
    AN_ = '( %s /\\ n e. NN )' % A0
    kdn = kfacts(AN_, w.s([], 'simpl', '( %s -> %s )' % (AN_, A0)), w.s([], 'simpr', '( %s -> n e. NN )' % AN_), 'n')
    fcn_n, _pkn, _ykn = ffkcn(AN_, w.s([], 'simpl', '( %s -> %s )' % (AN_, A0)), kdn, 'n')
    fff = w.s([fcn_n, w.s([], 'eqid', '%s = %s' % (FF, FF))], 'fmptd', '( %s -> %s : NN --> ( %s -cn-> CC ) )' % (A0, FF, D0))

    # the majorant GG ( n ) = Lam ( n ) n ^ -C ( Y ^ C / C )
    YC = '( ( Y ^c C ) / C )'
    VMT = lambda n: '( ( Lam ` %s ) x. ( %s ^c -u C ) )' % (n, n)
    VM = '( n e. NN |-> %s )' % VMT('n')
    GG = '( n e. NN |-> ( %s x. %s ) )' % (VMT('n'), YC)
    ycrp = D(w, A0, 'rpdivcld', [D(w, A0, 'rpcxpcld', [yrp, cr], '( Y ^c C ) e. RR+'), crp], '%s e. RR+' % YC)
    ycr = D(w, A0, 'rpred', [ycrp], '%s e. RR' % YC)

    def vmfacts(C, to0, kd, k):
        kc_ = D(w, C, 'rpcxpcld', [kd['rp'], D(w, C, 'renegcld', [w.s([to0, cr], 'syl', '( %s -> C e. RR )' % C)], '-u C e. RR')], '( %s ^c -u C ) e. RR+' % k)
        vr = D(w, C, 'remulcld', [kd['lam'], D(w, C, 'rpred', [kc_], '( %s ^c -u C ) e. RR' % k)], '%s e. RR' % VMT(k))
        v0 = D(w, C, 'mulge0d', [kd['lam'], D(w, C, 'rpred', [kc_], '( %s ^c -u C ) e. RR' % k), kd['lam0'], D(w, C, 'rpge0d', [kc_], '0 <_ ( %s ^c -u C )' % k)], '0 <_ %s' % VMT(k))
        return vr, v0

    def vmsub(n, k):
        return w.s([w.s([], 'fveq2', '( %s = %s -> ( Lam ` %s ) = ( Lam ` %s ) )' % (n, k, n, k)), w.s([], 'oveq1', '( %s = %s -> ( %s ^c -u C ) = ( %s ^c -u C ) )' % (n, k, n, k))], 'oveq12d',
                   '( %s = %s -> %s = %s )' % (n, k, VMT(n), VMT(k)))

    AJ = '( %s /\\ j e. NN )' % A0
    ajph = w.s([], 'simpl', '( %s -> %s )' % (AJ, A0)); ajn = w.s([], 'simpr', '( %s -> j e. NN )' % AJ)
    kdj = kfacts(AJ, ajph, ajn, 'j')
    vmj, vmj0 = vmfacts(AJ, ajph, kdj, 'j')
    subv = vmsub('n', 'j')
    vmjv = w.s([w.s([w.s([], 'eqid', '%s = %s' % (VM, VM))], 'a1i', '( %s -> %s = %s )' % (AJ, VM, VM)), w.s([subv], 'adantl', '( ( %s /\\ n = j ) -> %s = %s )' % (AJ, VMT('n'), VMT('j'))), ajn,
                w.s([w.s([], 'ovex', '%s e. _V' % VMT('j'))], 'a1i', '( %s -> %s e. _V )' % (AJ, VMT('j')))], 'fvmptd', '( %s -> ( %s ` j ) = %s )' % (AJ, VM, VMT('j')))
    GT_ = lambda n: '( %s x. %s )' % (VMT(n), YC)
    subg = w.s([vmsub('n', 'j')], 'oveq1d', '( n = j -> %s = %s )' % (GT_('n'), GT_('j')))
    ggjv = w.s([w.s([w.s([], 'eqid', '%s = %s' % (GG, GG))], 'a1i', '( %s -> %s = %s )' % (AJ, GG, GG)), w.s([subg], 'adantl', '( ( %s /\\ n = j ) -> %s = %s )' % (AJ, GT_('n'), GT_('j'))), ajn,
                w.s([w.s([], 'ovex', '%s e. _V' % GT_('j'))], 'a1i', '( %s -> %s e. _V )' % (AJ, GT_('j')))], 'fvmptd', '( %s -> ( %s ` j ) = %s )' % (AJ, GG, GT_('j')))
    ycrj = w.s([ajph, ycr], 'syl', '( %s -> %s e. RR )' % (AJ, YC))
    gtj = D(w, AJ, 'remulcld', [vmj, ycrj], '%s e. RR' % GT_('j'))
    gtj0 = D(w, AJ, 'mulge0d', [vmj, ycrj, vmj0, w.s([ajph, D(w, A0, 'rpge0d', [ycrp], '0 <_ %s' % YC)], 'syl', '( %s -> 0 <_ %s )' % (AJ, YC))], '0 <_ %s' % GT_('j'))
    # GG : NN --> RR
    AN2 = '( %s /\\ n e. NN )' % A0
    kdn2 = kfacts(AN2, w.s([], 'simpl', '( %s -> %s )' % (AN2, A0)), w.s([], 'simpr', '( %s -> n e. NN )' % AN2), 'n')
    vmn, _vmn0 = vmfacts(AN2, w.s([], 'simpl', '( %s -> %s )' % (AN2, A0)), kdn2, 'n')
    ggf = w.s([D(w, AN2, 'remulcld', [vmn, w.s([w.s([], 'simpl', '( %s -> %s )' % (AN2, A0)), ycr], 'syl', '( %s -> %s e. RR )' % (AN2, YC))], '%s e. RR' % GT_('n')), w.s([], 'eqid', '%s = %s' % (GG, GG))],
              'fmptd', '( %s -> %s : NN --> RR )' % (A0, GG))
    # convergence by comparison with the von Mangoldt series at C
    vmc = w.s([D(w, A0, 'jca', [cr, c1], '( C e. RR /\\ 1 < C )'), w.inst('vmsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, VM))
    AJU = '( %s /\\ j e. ( ZZ>= ` 1 ) )' % A0
    jnu = w.s([w.s([], 'simpr', '( %s -> j e. ( ZZ>= ` 1 ) )' % AJU), w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylibr', '( %s -> j e. NN )' % AJU)
    toAJ = D(w, AJU, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (AJU, A0)), jnu], AJ)
    ab = chain(w, AJ, ['( abs ` ( %s ` j ) )' % GG, '( abs ` %s )' % GT_('j'), GT_('j'), '( %s x. %s )' % (YC, VMT('j')), '( %s x. ( %s ` j ) )' % (YC, VM)],
               [w.s([ggjv], 'fveq2d', '( %s -> ( abs ` ( %s ` j ) ) = ( abs ` %s ) )' % (AJ, GG, GT_('j'))), D(w, AJ, 'absidd', [gtj, gtj0], '( abs ` %s ) = %s' % (GT_('j'), GT_('j'))),
                D(w, AJ, 'mulcomd', [D(w, AJ, 'recnd', [vmj], '%s e. CC' % VMT('j')), D(w, AJ, 'recnd', [ycrj], '%s e. CC' % YC)], '%s = ( %s x. %s )' % (GT_('j'), YC, VMT('j'))),
                w.s([w.s([vmjv], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (AJ, VMT('j'), VM))], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( %s ` j ) ) )' % (AJ, YC, VMT('j'), YC, VM))])
    abl = w.s([D(w, AJ, 'abscld', [D(w, AJ, 'recnd', [w.s([w.s([ajph, ggf], 'syl', '( %s -> %s : NN --> RR )' % (AJ, GG)), ajn], 'ffvelcdmd', '( %s -> ( %s ` j ) e. RR )' % (AJ, GG))], '( %s ` j ) e. CC' % GG)],
                '( abs ` ( %s ` j ) ) e. RR' % GG), ab], 'eqled', '( %s -> ( abs ` ( %s ` j ) ) <_ ( %s x. ( %s ` j ) ) )' % (AJ, GG, YC, VM))
    ablu = w.s([toAJ, abl], 'syl', '( %s -> ( abs ` ( %s ` j ) ) <_ ( %s x. ( %s ` j ) ) )' % (AJU, GG, YC, VM))
    vmjr = w.s([vmjv, vmj], 'eqeltrd', '( %s -> ( %s ` j ) e. RR )' % (AJ, VM))
    ggjc = D(w, AJ, 'recnd', [w.s([w.s([ajph, ggf], 'syl', '( %s -> %s : NN --> RR )' % (AJ, GG)), ajn], 'ffvelcdmd', '( %s -> ( %s ` j ) e. RR )' % (AJ, GG))], '( %s ` j ) e. CC' % GG)
    ggcv = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, A0, '1nn', '1 e. NN'), vmjr, ggjc, vmc, ycr, ablu], 'cvgcmpce', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GG))

    # the bound on the segment: | FF ( k ) ( v ) | <_ GG ( k )
    AKV = '( %s /\\ ( k e. NN /\\ v e. %s ) )' % (A0, SEGL)
    to0 = w.s([], 'simpl', '( %s -> %s )' % (AKV, A0)); kn = w.s([], 'simprl', '( %s -> k e. NN )' % AKV); vs = w.s([], 'simprr', '( %s -> v e. %s )' % (AKV, SEGL))
    kd = kfacts(AKV, to0, kn, 'k'); vd = segpt(AKV, to0, vs, 'v')
    fv = ffvv(AKV, kn, 'k', vd['d0'], 'v')
    idv, idx = ident(AKV, to0, kd, 'k', vd, 'v')
    ANK = '( %s x. ( k ^c -u v ) )' % AN('k'); YV = '( ( Y ^c v ) / v )'
    ankc = D(w, AKV, 'mulcld', [kd['an'], idx['knc']], '%s e. CC' % ANK)
    a1s = chain(w, AKV, ['( abs ` ( ( %s ` k ) ` v ) )' % FF, '( abs ` %s )' % FT('k', 'v'), '( abs ` ( %s x. %s ) )' % (ANK, YV), '( ( abs ` %s ) x. ( abs ` %s ) )' % (ANK, YV)],
                [w.s([fv], 'fveq2d', '( %s -> ( abs ` ( ( %s ` k ) ` v ) ) = ( abs ` %s ) )' % (AKV, FF, FT('k', 'v'))), w.s([idv], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( %s x. %s ) ) )' % (AKV, FT('k', 'v'), ANK, YV)),
                 D(w, AKV, 'absmuld', [ankc, idx['yuuc']], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (ANK, YV, ANK, YV))])
    lt = w.s([D(w, AKV, 'jca', [w.s([to0, nx], 'syl', '( %s -> %s )' % (AKV, NX)), D(w, AKV, 'jca', [kn, vd['c']], '( k e. NN /\\ v e. CC )')], '( %s /\\ ( k e. NN /\\ v e. CC ) )' % NX), w.inst('lchvmtm')],
             'syl', '( %s -> ( abs ` %s ) <_ ( ( Lam ` k ) x. ( k ^c -u ( Re ` v ) ) ) )' % (AKV, ANK))
    rw = w.s([w.s([w.s([vd['re']], 'negeqd', '( %s -> -u ( Re ` v ) = -u C )' % AKV)], 'oveq2d', '( %s -> ( k ^c -u ( Re ` v ) ) = ( k ^c -u C ) )' % AKV)], 'oveq2d',
             '( %s -> ( ( Lam ` k ) x. ( k ^c -u ( Re ` v ) ) ) = %s )' % (AKV, VMT('k')))
    b1 = w.s([lt, rw], 'breqtrd', '( %s -> ( abs ` %s ) <_ %s )' % (AKV, ANK, VMT('k')))
    yrpv = idx['yrp']
    avd = D(w, AKV, 'absdivd', [idx['yuc'], vd['c'], vd['ne']], '( abs ` %s ) = ( ( abs ` ( Y ^c v ) ) / ( abs ` v ) )' % YV)
    acx = w.s([yrpv, vd['c'], w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` ( Y ^c v ) ) = ( Y ^c ( Re ` v ) ) )' % AKV)
    acx2 = w.s([acx, w.s([vd['re']], 'oveq2d', '( %s -> ( Y ^c ( Re ` v ) ) = ( Y ^c C ) )' % AKV)], 'eqtrd', '( %s -> ( abs ` ( Y ^c v ) ) = ( Y ^c C ) )' % AKV)
    ycv = D(w, AKV, 'rpcxpcld', [yrpv, w.s([to0, cr], 'syl', '( %s -> C e. RR )' % AKV)], '( Y ^c C ) e. RR+')
    crpv = w.s([to0, crp], 'syl', '( %s -> C e. RR+ )' % AKV)
    avrp = D(w, AKV, 'absrpcld', [vd['c'], vd['ne']], '( abs ` v ) e. RR+')
    are = w.s([vd['c'], w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` v ) ) <_ ( abs ` v ) )' % AKV)
    arc = w.s([w.s([vd['re']], 'fveq2d', '( %s -> ( abs ` ( Re ` v ) ) = ( abs ` C ) )' % AKV), D(w, AKV, 'absidd', [D(w, AKV, 'rpred', [crpv], 'C e. RR'), D(w, AKV, 'rpge0d', [crpv], '0 <_ C')], '( abs ` C ) = C')],
              'eqtrd', '( %s -> ( abs ` ( Re ` v ) ) = C )' % AKV)
    cle = w.s([arc, are], 'eqbrtrrd', '( %s -> C <_ ( abs ` v ) )' % AKV)
    ld = D(w, AKV, 'lediv2ad', [crpv, avrp, D(w, AKV, 'rpred', [ycv], '( Y ^c C ) e. RR'), D(w, AKV, 'rpge0d', [ycv], '0 <_ ( Y ^c C )'), cle], '( ( Y ^c C ) / ( abs ` v ) ) <_ %s' % YC)
    b2 = w.s([w.s([avd, w.s([acx2], 'oveq1d', '( %s -> ( ( abs ` ( Y ^c v ) ) / ( abs ` v ) ) = ( ( Y ^c C ) / ( abs ` v ) ) )' % AKV)], 'eqtrd', '( %s -> ( abs ` %s ) = ( ( Y ^c C ) / ( abs ` v ) ) )' % (AKV, YV)), ld],
             'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (AKV, YV, YC))
    vmk, vmk0 = vmfacts(AKV, to0, kd, 'k')
    pr = D(w, AKV, 'lemul12ad', [D(w, AKV, 'abscld', [ankc], '( abs ` %s ) e. RR' % ANK), vmk, D(w, AKV, 'abscld', [idx['yuuc']], '( abs ` %s ) e. RR' % YV), w.s([to0, ycr], 'syl', '( %s -> %s e. RR )' % (AKV, YC)),
                                    D(w, AKV, 'absge0d', [ankc], '0 <_ ( abs ` %s )' % ANK), D(w, AKV, 'absge0d', [idx['yuuc']], '0 <_ ( abs ` %s )' % YV), b1, b2],
           '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( %s x. %s )' % (ANK, YV, VMT('k'), YC))
    subgk = w.s([vmsub('n', 'k')], 'oveq1d', '( n = k -> %s = %s )' % (GT_('n'), GT_('k')))
    ggk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (GG, GG))], 'a1i', '( %s -> %s = %s )' % (AKV, GG, GG)), w.s([subgk], 'adantl', '( ( %s /\\ n = k ) -> %s = %s )' % (AKV, GT_('n'), GT_('k'))), kn,
               w.s([w.s([], 'ovex', '%s e. _V' % GT_('k'))], 'a1i', '( %s -> %s e. _V )' % (AKV, GT_('k')))], 'fvmptd', '( %s -> ( %s ` k ) = %s )' % (AKV, GG, GT_('k')))
    bound = w.s([w.s([a1s, pr], 'eqbrtrd', '( %s -> ( abs ` ( ( %s ` k ) ` v ) ) <_ %s )' % (AKV, FF, GT_('k'))), w.s([ggk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (AKV, GT_('k'), GG))], 'breqtrd',
                '( %s -> ( abs ` ( ( %s ` k ) ` v ) ) <_ ( %s ` k ) )' % (AKV, FF, GG))
    GSF = '( v e. %s |-> sum_ k e. NN ( ( %s ` k ) ` v ) )' % (D0, FF)
    lser = w.s([D(w, A0, 'jca', [loc, hic], '( %s e. CC /\\ %s e. CC )' % (LOs, HIs)), D(w, A0, 'jca', [fff, segss], '( %s : NN --> ( %s -cn-> CC ) /\\ %s C_ %s )' % (FF, D0, SEGL, D0)),
                D(w, A0, 'jca', [ggf, ggcv], '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> )' % (GG, GG)), bound], 'ef1lser',
               '( %s -> seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> ( %s lint <. %s , %s >. ) )' % (A0, FF, LOs, HIs, GSF, LOs, HIs))

    # (a) each term: ( FF ` k ) lint = AN ( k ) x. PKL ( Y / k )
    AK = '( %s /\\ k e. NN )' % A0
    akph = w.s([], 'simpl', '( %s -> %s )' % (AK, A0)); akn = w.s([], 'simpr', '( %s -> k e. NN )' % AK)
    kdk = kfacts(AK, akph, akn, 'k')
    ffkc, pkxc, ykk = ffkcn(AK, akph, kdk, 'k')
    ffk = ffval(AK, akn, 'k')
    ffkc2 = w.s([ffk, ffkc], 'eqeltrd', '( %s -> ( %s ` k ) e. ( %s -cn-> CC ) )' % (AK, FF, D0))
    AKU = '( %s /\\ u e. %s )' % (AK, SEGL)
    ud = segpt(AKU, w.s([], 'simpll', '( %s -> %s )' % (AKU, A0)), w.s([], 'simpr', '( %s -> u e. %s )' % (AKU, SEGL)), 'u')
    fku = ffvv(AKU, w.s([], 'simplr', '( %s -> k e. NN )' % AKU), 'k', ud['d0'], 'u')
    PQ = '( ( ( Y / k ) ^c u ) / u )'
    sbx = w.s([w.s([], 'oveq2', '( x = u -> ( ( Y / k ) ^c x ) = ( ( Y / k ) ^c u ) )'), w.s([], 'id', '( x = u -> x = u )')], 'oveq12d', '( x = u -> ( ( ( Y / k ) ^c x ) / x ) = %s )' % PQ)
    pku = w.s([w.s([w.s([], 'eqid', '%s = %s' % (PKX('k'), PKX('k')))], 'a1i', '( %s -> %s = %s )' % (AKU, PKX('k'), PKX('k'))), w.s([sbx], 'adantl', '( ( %s /\\ x = u ) -> ( ( ( Y / k ) ^c x ) / x ) = %s )' % (AKU, PQ)),
               ud['d0'], w.s([w.s([], 'ovex', '%s e. _V' % PQ)], 'a1i', '( %s -> %s e. _V )' % (AKU, PQ))], 'fvmptd', '( %s -> ( %s ` u ) = %s )' % (AKU, PKX('k'), PQ))
    pw1 = w.s([fku, w.s([pku], 'oveq2d', '( %s -> ( %s x. ( %s ` u ) ) = %s )' % (AKU, AN('k'), PKX('k'), FT('k', 'u')))], 'eqtr4d', '( %s -> ( ( %s ` k ) ` u ) = ( %s x. ( %s ` u ) ) )' % (AKU, FF, AN('k'), PKX('k')))
    ralu = w.s([pw1], 'ralrimiva', '( %s -> A. u e. %s ( ( %s ` k ) ` u ) = ( %s x. ( %s ` u ) ) )' % (AK, SEGL, FF, AN('k'), PKX('k')))
    lm = w.s([D(w, AK, 'jca', [w.s([akph, D(w, A0, 'jca', [loc, hic], '( %s e. CC /\\ %s e. CC )' % (LOs, HIs))], 'syl', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (AK, LOs, HIs)),
                                D(w, AK, 'jca', [ffkc2, w.s([akph, segss], 'syl', '( %s -> %s C_ %s )' % (AK, SEGL, D0))], '( ( %s ` k ) e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (FF, D0, SEGL, D0))],
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( %s ` k ) e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (LOs, HIs, FF, D0, SEGL, D0)),
              D(w, AK, 'jca', [pkxc, kdk['an']], '( %s e. ( %s -cn-> CC ) /\\ %s e. CC )' % (PKX('k'), D0, AN('k'))), ralu, w.inst('lintmulc2')], 'syl3anc',
             '( %s -> ( ( %s ` k ) lint <. %s , %s >. ) = ( %s x. ( %s lint <. %s , %s >. ) ) )' % (AK, FF, LOs, HIs, AN('k'), PKX('k'), LOs, HIs))
    cbx = w.s([w.s([w.s([], 'oveq2', '( x = z -> ( ( Y / k ) ^c x ) = ( ( Y / k ) ^c z ) )'), w.s([], 'id', '( x = z -> x = z )')], 'oveq12d',
                   '( x = z -> ( ( ( Y / k ) ^c x ) / x ) = ( ( ( Y / k ) ^c z ) / z ) )')], 'cbvmptv', '%s = %s' % (PKX('k'), PKF('( Y / k )')))
    lpk = w.s([w.s([cbx], 'oveq1i', '( %s lint <. %s , %s >. ) = %s' % (PKX('k'), LOs, HIs, PKL('( Y / k )')))], 'a1i', '( %s -> ( %s lint <. %s , %s >. ) = %s )' % (AK, PKX('k'), LOs, HIs, PKL('( Y / k )')))
    tk = w.s([lm, w.s([lpk], 'oveq2d', '( %s -> ( %s x. ( %s lint <. %s , %s >. ) ) = %s )' % (AK, AN('k'), PKX('k'), LOs, HIs, PTERM('k')))], 'eqtrd',
             '( %s -> ( ( %s ` k ) lint <. %s , %s >. ) = %s )' % (AK, FF, LOs, HIs, PTERM('k')))
    LKM = '( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) )' % (FF, LOs, HIs)
    m1 = w.s([tk], 'mpteq2dva', '( %s -> %s = ( k e. NN |-> %s ) )' % (A0, LKM, PTERM('k')))

    def ptsub(a, b):
        """( a = b -> PTERM ( a ) = PTERM ( b ) )"""
        yx = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( Y / %s ) = ( Y / %s ) )' % (a, b, a, b))], 'oveq1d', '( %s = %s -> ( ( Y / %s ) ^c z ) = ( ( Y / %s ) ^c z ) )' % (a, b, a, b))], 'oveq1d',
                      '( %s = %s -> ( ( ( Y / %s ) ^c z ) / z ) = ( ( ( Y / %s ) ^c z ) / z ) )' % (a, b, a, b))], 'mpteq2dv', '( %s = %s -> %s = %s )' % (a, b, PKF('( Y / %s )' % a), PKF('( Y / %s )' % b)))
        pl = w.s([yx], 'oveq1d', '( %s = %s -> %s = %s )' % (a, b, PKL('( Y / %s )' % a), PKL('( Y / %s )' % b)))
        return w.s([subk(a, b), pl], 'oveq12d', '( %s = %s -> %s = %s )' % (a, b, PTERM(a), PTERM(b)))

    m2 = w.s([w.s([ptsub('k', 'n')], 'cbvmptv', '( k e. NN |-> %s ) = ( n e. NN |-> %s )' % (PTERM('k'), PTERM('n')))], 'a1i', '( %s -> ( k e. NN |-> %s ) = ( n e. NN |-> %s ) )' % (A0, PTERM('k'), PTERM('n')))
    PM = '( n e. NN |-> %s )' % PTERM('n')
    m3 = w.s([m1, m2], 'eqtrd', '( %s -> %s = %s )' % (A0, LKM, PM))
    sq = w.s([m3, w.inst('seqeq3')], 'syl', '( %s -> seq 1 ( + , %s ) = %s )' % (A0, LKM, PSER()))
    cvg = w.s([sq, lser], 'eqbrtrrd', '( %s -> %s ~~> ( %s lint <. %s , %s >. ) )' % (A0, PSER(), GSF, LOs, HIs))

    # (b) the pointwise sum is the right-edge integrand
    AU = '( %s /\\ u e. %s )' % (A0, SEGL)
    auph = w.s([], 'simpl', '( %s -> %s )' % (AU, A0)); aus = w.s([], 'simpr', '( %s -> u e. %s )' % (AU, SEGL))
    ud2 = segpt(AU, auph, aus, 'u')
    SKU = 'sum_ k e. NN ( ( %s ` k ) ` u )' % FF
    sbv = w.s([w.s([w.s([], 'fveq2', '( v = u -> ( ( %s ` k ) ` v ) = ( ( %s ` k ) ` u ) )' % (FF, FF))], 'adantr', '( ( v = u /\\ k e. NN ) -> ( ( %s ` k ) ` v ) = ( ( %s ` k ) ` u ) )' % (FF, FF))],
              'sumeq2dv', '( v = u -> sum_ k e. NN ( ( %s ` k ) ` v ) = %s )' % (FF, SKU))
    gsu = w.s([w.s([w.s([], 'eqid', '%s = %s' % (GSF, GSF))], 'a1i', '( %s -> %s = %s )' % (AU, GSF, GSF)), w.s([sbv], 'adantl', '( ( %s /\\ v = u ) -> sum_ k e. NN ( ( %s ` k ) ` v ) = %s )' % (AU, FF, SKU)),
               ud2['d0'], w.s([w.s([], 'sumex', '%s e. _V' % SKU)], 'a1i', '( %s -> %s e. _V )' % (AU, SKU))], 'fvmptd', '( %s -> ( %s ` u ) = %s )' % (AU, GSF, SKU))
    AUK = '( %s /\\ k e. NN )' % AU
    to0k = w.s([], 'simpll', '( %s -> %s )' % (AUK, A0)); knk = w.s([], 'simpr', '( %s -> k e. NN )' % AUK)
    kdu = kfacts(AUK, to0k, knk, 'k')
    udk = segpt(AUK, to0k, w.s([], 'simplr', '( %s -> u e. %s )' % (AUK, SEGL)), 'u')
    fkuk = ffvv(AUK, knk, 'k', udk['d0'], 'u')
    idu, idux = ident(AUK, to0k, kdu, 'k', udk, 'u')
    YU_ = '( ( Y ^c u ) / u )'
    TU = '( ( %s x. ( k ^c -u u ) ) x. %s )' % (AN('k'), YU_)
    s1 = w.s([w.s([fkuk, idu], 'eqtrd', '( %s -> ( ( %s ` k ) ` u ) = %s )' % (AUK, FF, TU))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (AU, SKU, TU))
    LCH = '( n e. NN |-> ( %s x. ( n ^c -u u ) ) )' % AN('n')
    lcv = w.s([D(w, AU, 'jca', [w.s([auph, nx], 'syl', '( %s -> %s )' % (AU, NX)), D(w, AU, 'jca', [ud2['c'], ud2['gt']], '( u e. CC /\\ 1 < ( Re ` u ) )')], '( %s /\\ ( u e. CC /\\ 1 < ( Re ` u ) ) )' % NX),
               w.inst('lchvmcvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (AU, LCH))
    sbn = w.s([subk('n', 'k'), w.s([], 'oveq1', '( n = k -> ( n ^c -u u ) = ( k ^c -u u ) )')], 'oveq12d', '( n = k -> ( %s x. ( n ^c -u u ) ) = ( %s x. ( k ^c -u u ) ) )' % (AN('n'), AN('k')))
    ankuc = D(w, AUK, 'mulcld', [kdu['an'], idux['knc']], '( %s x. ( k ^c -u u ) ) e. CC' % AN('k'))
    lchk = w.s([w.s([w.s([], 'eqid', '%s = %s' % (LCH, LCH))], 'a1i', '( %s -> %s = %s )' % (AUK, LCH, LCH)), w.s([sbn], 'adantl', '( ( %s /\\ n = k ) -> ( %s x. ( n ^c -u u ) ) = ( %s x. ( k ^c -u u ) ) )' % (AUK, AN('n'), AN('k'))),
                knk, ankuc], 'fvmptd', '( %s -> ( %s ` k ) = ( %s x. ( k ^c -u u ) ) )' % (AUK, LCH, AN('k')))
    yuu = D(w, AU, 'divcld', [D(w, AU, 'cxpcld', [D(w, AU, 'rpcnd', [w.s([auph, yrp], 'syl', '( %s -> Y e. RR+ )' % AU)], 'Y e. CC'), ud2['c']], '( Y ^c u ) e. CC'), ud2['c'], ud2['ne']], '%s e. CC' % YU_)
    im = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, AU, '1z', '1 e. ZZ'), lchk, ankuc, lcv, yuu], 'isummulc1',
             '( %s -> ( %s x. %s ) = sum_ k e. NN %s )' % (AU, DLV('u'), YU_, TU))
    sbz = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = u -> -u z = -u u )')], 'oveq2d', '( z = u -> ( k ^c -u z ) = ( k ^c -u u ) )')], 'oveq2d',
                          '( z = u -> ( %s x. ( k ^c -u z ) ) = ( %s x. ( k ^c -u u ) ) )' % (AN('k'), AN('k')))], 'adantr', '( ( z = u /\\ k e. NN ) -> ( %s x. ( k ^c -u z ) ) = ( %s x. ( k ^c -u u ) ) )' % (AN('k'), AN('k')))],
              'sumeq2dv', '( z = u -> %s = %s )' % (DLV('z'), DLV('u')))
    sby = w.s([w.s([], 'oveq2', '( z = u -> ( Y ^c z ) = ( Y ^c u ) )'), w.s([], 'id', '( z = u -> z = u )')], 'oveq12d', '( z = u -> ( ( Y ^c z ) / z ) = %s )' % YU_)
    rsub = w.s([sbz, sby], 'oveq12d', '( z = u -> ( %s x. ( ( Y ^c z ) / z ) ) = ( %s x. %s ) )' % (DLV('z'), DLV('u'), YU_))
    rhu = w.s([w.s([w.s([], 'eqid', '%s = %s' % (RHF, RHF))], 'a1i', '( %s -> %s = %s )' % (AU, RHF, RHF)), w.s([rsub], 'adantl', '( ( %s /\\ z = u ) -> ( %s x. ( ( Y ^c z ) / z ) ) = ( %s x. %s ) )' % (AU, DLV('z'), DLV('u'), YU_)),
               ud2['d0'], w.s([w.s([], 'ovex', '( %s x. %s ) e. _V' % (DLV('u'), YU_))], 'a1i', '( %s -> ( %s x. %s ) e. _V )' % (AU, DLV('u'), YU_))], 'fvmptd', '( %s -> ( %s ` u ) = ( %s x. %s ) )' % (AU, RHF, DLV('u'), YU_))
    eqp = chain(w, AU, ['( %s ` u )' % GSF, SKU, 'sum_ k e. NN %s' % TU, '( %s x. %s )' % (DLV('u'), YU_), '( %s ` u )' % RHF], [gsu, s1, ('r', im), ('r', rhu)])
    rall = w.s([eqp], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, SEGL, GSF, RHF))
    gse = w.s([w.s([d0e, w.inst('mptexg')], 'ax-mp', '%s e. _V' % GSF)], 'a1i', '( %s -> %s e. _V )' % (A0, GSF))
    rhe = w.s([w.s([d0e, w.inst('mptexg')], 'ax-mp', '%s e. _V' % RHF)], 'a1i', '( %s -> %s e. _V )' % (A0, RHF))
    leq = w.s([D(w, A0, 'jca', [D(w, A0, 'jca', [loc, hic], '( %s e. CC /\\ %s e. CC )' % (LOs, HIs)), D(w, A0, 'jca', [gse, rhe], '( %s e. _V /\\ %s e. _V )' % (GSF, RHF))],
                   '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (LOs, HIs, GSF, RHF)), rall, w.inst('linteq')], 'syl2anc',
              '( %s -> ( %s lint <. %s , %s >. ) = ( %s lint <. %s , %s >. ) )' % (A0, GSF, LOs, HIs, RHF, LOs, HIs))
    RL = '( %s lint <. %s , %s >. )' % (RHF, LOs, HIs)
    cv2 = w.s([cvg, leq], 'breqtrd', '( %s -> %s ~~> %s )' % (A0, PSER(), RL))
    # the sum of the series
    PSm = '( m e. NN |-> %s )' % PTERM('m')
    cbm = w.s([w.s([w.s([ptsub('m', 'n')], 'cbvmptv', '%s = %s' % (PSm, PM)), w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = %s' % (PSm, PSER()))], 'a1i',
              '( %s -> seq 1 ( + , %s ) = %s )' % (A0, PSm, PSER()))
    cv3 = w.s([cbm, cv2], 'eqbrtrd', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, PSm, RL))
    ANn = '( %s /\\ n e. NN )' % A0
    anph = w.s([], 'simpl', '( %s -> %s )' % (ANn, A0)); ann = w.s([], 'simpr', '( %s -> n e. NN )' % ANn)
    kdn3 = kfacts(ANn, anph, ann, 'n')
    ykn = D(w, ANn, 'rpdivcld', [w.s([anph, yrp], 'syl', '( %s -> Y e. RR+ )' % ANn), kdn3['rp']], '( Y / n ) e. RR+')
    pkn = w.s([D(w, ANn, 'jca', [ykn, a1(w, ANn, 'ssid', '%s C_ %s' % (D0, D0))], '( ( Y / n ) e. RR+ /\\ %s C_ %s )' % (D0, D0)), w.inst('pkfcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ANn, PKF('( Y / n )'), D0))
    lcn = w.s([D(w, ANn, 'jca', [w.s([anph, D(w, A0, 'jca', [loc, hic], '( %s e. CC /\\ %s e. CC )' % (LOs, HIs))], 'syl', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ANn, LOs, HIs)),
                                 D(w, ANn, 'jca', [pkn, w.s([anph, segss], 'syl', '( %s -> %s C_ %s )' % (ANn, SEGL, D0))], '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (PKF('( Y / n )'), D0, SEGL, D0))],
                 '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (LOs, HIs, PKF('( Y / n )'), D0, SEGL, D0)), w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (ANn, PKL('( Y / n )')))
    ptc = D(w, ANn, 'mulcld', [kdn3['an'], lcn], '%s e. CC' % PTERM('n'))
    psn = w.s([w.s([w.s([], 'eqid', '%s = %s' % (PSm, PSm))], 'a1i', '( %s -> %s = %s )' % (ANn, PSm, PSm)), w.s([ptsub('m', 'n')], 'adantl', '( ( %s /\\ m = n ) -> %s = %s )' % (ANn, PTERM('m'), PTERM('n'))),
               ann, ptc], 'fvmptd', '( %s -> ( %s ` n ) = %s )' % (ANn, PSm, PTERM('n')))
    ics = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, A0, '1z', '1 e. ZZ'), psn, ptc, cv3], 'isumclim', '( %s -> %s = %s )' % (A0, PS(), RL))
    w.qed([cv2, ics], 'jca', STATEMENTS['ef1redge'])
    go(w, only)
