"""T7b: the N-level facts of the division at the machine.

  tmidvstp  Lean ` divmod_step ` : halving the divisor ` 2 S ` to ` S `
  tmidvs    Lean ` divSteps ` as an infimum: its spec and minimality
  tmidvsle  Lean ` divSteps_le `

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_f_nat.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith, lineq, nlinarith

SEL = sys.argv[1:]

Q2 = '( |_ ` ( F / ( 2 x. S ) ) )'
R2 = '( F mod ( 2 x. S ) )'
X1 = '( ( 2 x. %s ) + 1 )' % Q2
X0 = '( 2 x. %s )' % Q2
FS = '( |_ ` ( F / S ) )'
PH_STP = '( F e. NN0 /\\ S e. NN )'
C1 = '( S <_ %s -> ( ( F mod S ) = ( %s - S ) /\\ %s = %s ) )' % (R2, R2, FS, X1)
C0 = '( %s < S -> ( ( F mod S ) = %s /\\ %s = %s ) )' % (R2, R2, FS, X0)
ST_STP = '( %s -> ( %s /\\ %s ) )' % (PH_STP, C1, C0)

RD = 'inf ( { w e. NN0 | F < ( ( 2 ^ w ) x. G ) } , RR , < )'
SD = '{ w e. NN0 | F < ( ( 2 ^ w ) x. G ) }'
PH_DV = '( F e. NN0 /\\ G e. NN )'
ST_DVS = ('( %s -> ( %s e. NN0 /\\ F < ( ( 2 ^ %s ) x. G ) /\\ A. i e. ( 0 ..^ %s ) ( ( 2 ^ i ) x. G ) <_ F ) )'
          % (PH_DV, RD, RD, RD))
ST_DVSLE = '( ( %s /\\ ( N e. NN0 /\\ F < ( 2 ^ N ) ) ) -> %s <_ N )' % (PH_DV, RD)

STMTS = {'tmidvstp': ST_STP, 'tmidvs': ST_DVS, 'tmidvsle': ST_DVSLE}


def tmidvstp():
    w = W('tmidvstp', 'One step of binary long division (Lean ` divmod_step ` ): from the remainder and quotient '
                      'by ` 2 S ` to those by ` S ` : when ` S ` fits into the remainder it is subtracted and the '
                      'quotient doubles plus one, otherwise the remainder stays and the quotient doubles.')
    ph = PH_STP
    fn = w.s([], 'simpl', '( %s -> F e. NN0 )' % ph)
    sn = w.s([], 'simpr', '( %s -> S e. NN )' % ph)
    outs = []
    for case in (1, 0):
        hyp = ('S <_ %s' % R2) if case else ('%s < S' % R2)
        ps = '( %s /\\ %s )' % (ph, hyp)
        h = w.s([], 'simpr', '( %s -> %s )' % (ps, hyp))
        f = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % ps)
        s = w.s([sn], 'adantr', '( %s -> S e. NN )' % ps)
        c = Closure(w, ps, {'F': ('NN0', f), 'S': ('NN', s)})
        c.atom(Q2); c.atom(R2); c.atom('( F / S )'); c.atom(FS)
        fr = c.mem('F', 'RR'); s2p = c.mem('( 2 x. S )', 'RR+'); sp = c.mem('S', 'RR+')
        mv = w.s([fr, s2p, w.inst('modvalr')], 'syl2anc', '( %s -> %s = ( F - ( %s x. ( 2 x. S ) ) ) )' % (ps, R2, Q2))
        mlt = w.s([fr, s2p, w.inst('modlt')], 'syl2anc', '( %s -> %s < ( 2 x. S ) )' % (ps, R2))
        mge = w.s([fr, s2p, w.inst('modge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (ps, R2))
        X = X1 if case else X0
        xz = c.mem(X, 'ZZ')
        xr = c.mem(X, 'RR')
        fsr = c.mem('( F / S )', 'RR')
        sr = c.mem('S', 'RR'); s0 = c.gt0('S')
        a = w.s([sr, s0], 'jca', '( %s -> ( S e. RR /\\ 0 < S ) )' % ps)
        le1 = linarith(w, ps, [mv, h] if case else [mv, mge], '( %s x. S ) <_ F' % X, closure=c, products=True,
                       atoms=[Q2, R2])
        lm = w.s([xr, fr, a, w.inst('lemuldiv')], 'syl3anc', '( %s -> ( ( %s x. S ) <_ F <-> %s <_ ( F / S ) ) )' % (ps, X, X))
        g1 = w.s([le1, lm], 'mpbid', '( %s -> %s <_ ( F / S ) )' % (ps, X))
        x1r = c.mem('( %s + 1 )' % X, 'RR')
        lt1 = linarith(w, ps, [mv, mlt] if case else [mv, h], 'F < ( ( %s + 1 ) x. S )' % X, closure=c, products=True,
                       atoms=[Q2, R2])
        ld = w.s([fr, x1r, a, w.inst('ltdivmul2')], 'syl3anc', '( %s -> ( ( F / S ) < ( %s + 1 ) <-> F < ( ( %s + 1 ) x. S ) ) )' % (ps, X, X))
        g2 = w.s([lt1, ld], 'mpbird', '( %s -> ( F / S ) < ( %s + 1 ) )' % (ps, X))
        fb = w.s([fsr, xz, w.inst('flbi')], 'syl2anc', '( %s -> ( %s = %s <-> ( %s <_ ( F / S ) /\\ ( F / S ) < ( %s + 1 ) ) ) )' % (ps, FS, X, X, X))
        fl = w.s([fb, w.s([g1, g2], 'jca', '( %s -> ( %s <_ ( F / S ) /\\ ( F / S ) < ( %s + 1 ) ) )' % (ps, X, X))], 'mpbird',
                 '( %s -> %s = %s )' % (ps, FS, X))
        mv1 = w.s([fr, sp, w.inst('modvalr')], 'syl2anc', '( %s -> ( F mod S ) = ( F - ( %s x. S ) ) )' % (ps, FS))
        e1 = w.s([fl], 'oveq1d', '( %s -> ( %s x. S ) = ( %s x. S ) )' % (ps, FS, X))
        e2 = w.s([e1], 'oveq2d', '( %s -> ( F - ( %s x. S ) ) = ( F - ( %s x. S ) ) )' % (ps, FS, X))
        mv2 = w.s([mv1, e2], 'eqtrd', '( %s -> ( F mod S ) = ( F - ( %s x. S ) ) )' % (ps, X))
        tgt = ('( %s - S )' % R2) if case else R2
        c.mem('( F mod S )', 'RR')
        ev = lineq(w, ps, '( F - ( %s x. S ) )' % X, tgt, hyps=[mv], closure=c, products=True, atoms=[Q2, R2])
        mod = w.s([mv2, ev], 'eqtrd', '( %s -> ( F mod S ) = %s )' % (ps, tgt))
        both = w.s([mod, fl], 'jca', '( %s -> ( ( F mod S ) = %s /\\ %s = %s ) )' % (ps, tgt, FS, X))
        outs.append(w.s([both], 'ex', '( %s -> ( %s -> ( ( F mod S ) = %s /\\ %s = %s ) ) )' % (ph, hyp, tgt, FS, X)))
    w.qed(outs, 'jca', ST_STP)
    return w.run()


def cond(t):
    return 'F < ( ( 2 ^ %s ) x. G )' % t


SDY = '{ y e. NN0 | %s }' % cond('y')


def sd_facts(w, ph):
    """SD C_ ( ZZ>= ` 0 ), and SD = SDY"""
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN0' % SD), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'sseqtri', '%s C_ ( ZZ>= ` 0 )' % SD)
    idw = w.s([], 'id', '( w = y -> w = y )')
    cg, new = w.wcongr(cond('w'), {'w': 'y'}, 'w = y', {'w': idw})
    assert new == cond('y')
    cb = w.s([cg], 'cbvrabv', '%s = %s' % (SD, SDY))
    return w.s([ss], 'a1i', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (ph, SD)), cb


def in_sd(w, ph, t, tn, lt, cb):
    """( ph -> t e. SD ) from tn : t e. NN0, lt : F < ( ( 2 ^ t ) x. G ) (t free of y)"""
    idy = w.s([], 'id', '( y = %s -> y = %s )' % (t, t))
    cg, new = w.wcongr(cond('y'), {'y': t}, 'y = %s' % t, {'y': idy})
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. NN0 /\\ %s ) )' % (t, SDY, t, cond(t)))
    j = w.s([tn, lt], 'jca', '( %s -> ( %s e. NN0 /\\ %s ) )' % (ph, t, cond(t)))
    e = w.s([j, el], 'sylibr', '( %s -> %s e. %s )' % (ph, t, SDY))
    return w.s([e, w.s([cb], 'a1i', '( %s -> %s = %s )' % (ph, SD, SDY))], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, t, SD))


def pow_ge(w, ph, c, t, lt):
    """from lt : F < ( 2 ^ t ) : F < ( ( 2 ^ t ) x. G ) (G e. NN a leaf of c)"""
    g1 = c.mem('G', 'NN')
    ge1 = w.s([g1, w.inst('nnge1')], 'syl', '( %s -> 1 <_ G )' % ph)
    p0 = c.ge0('( 2 ^ %s )' % t)
    return nlinarith(w, ph, [lt, ge1, p0], cond(t), closure=c)


def tmidvs():
    ph = PH_DV
    w = W('tmidvs', 'The number of doublings of the divisor (Lean ` divSteps ` , the least ` i ` with '
                    '` a < 2 ^ i x. d ` ) as an infimum: a nonnegative integer with Lean\'s ` divSteps_spec ` and '
                    '` divSteps_min ` .')
    fn = w.s([], 'simpl', '( %s -> F e. NN0 )' % ph)
    gn = w.s([], 'simpr', '( %s -> G e. NN )' % ph)
    c = Closure(w, ph, {'F': ('NN0', fn), 'G': ('NN', gn)})
    ssu, cb = sd_facts(w, ph)
    b3 = w.s([w.s([], 'uzid', '( 2 e. ZZ -> 2 e. ( ZZ>= ` 2 ) )'), w.s([], '2z', '2 e. ZZ')], 'mpan2' if False else 'mpbi' if False else 'ax-mp',
             '2 e. ( ZZ>= ` 2 )') if False else None
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    fl = w.s([w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph), fn, w.inst('bernneq3')], 'syl2anc', '( %s -> F < ( 2 ^ F ) )' % ph)
    fin = in_sd(w, ph, 'F', fn, pow_ge(w, ph, c, 'F', fl), cb)
    ne = w.s([fin, w.inst('ne0i')], 'syl', '( %s -> %s =/= (/) )' % (ph, SD))
    rin = w.s([ssu, ne, w.inst('infssuzcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, RD, SD))
    rin2 = w.s([rin, w.s([cb], 'a1i', '( %s -> %s = %s )' % (ph, SD, SDY))], 'eleqtrd', '( %s -> %s e. %s )' % (ph, RD, SDY))
    idy = w.s([], 'id', '( y = %s -> y = %s )' % (RD, RD))
    cg, new = w.wcongr(cond('y'), {'y': RD}, 'y = %s' % RD, {'y': idy})
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. NN0 /\\ %s ) )' % (RD, SDY, RD, cond(RD)))
    both = w.s([rin2, el], 'sylib', '( %s -> ( %s e. NN0 /\\ %s ) )' % (ph, RD, cond(RD)))
    rn = w.s([both], 'simpld', '( %s -> %s e. NN0 )' % (ph, RD))
    rs = w.s([both], 'simprd', '( %s -> %s )' % (ph, cond(RD)))
    # minimality
    ps = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, RD)
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (ps, RD))
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ps, RD))
    ps2 = '( %s /\\ %s )' % (ps, cond('i'))
    in2 = in_sd(w, ps2, 'i', w.s([inn], 'adantr', '( %s -> i e. NN0 )' % ps2), w.s([], 'simpr', '( %s -> %s )' % (ps2, cond('i'))), cb)
    ssu2 = w.s([ssu], 'adantr', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (ps, SD))
    ssu3 = w.s([ssu2], 'adantr', '( %s -> %s C_ ( ZZ>= ` 0 ) )' % (ps2, SD))
    le = w.s([ssu3, in2, w.inst('infssuzle')], 'syl2anc', '( %s -> %s <_ i )' % (ps2, RD))
    imp = w.s([le], 'ex', '( %s -> ( %s -> %s <_ i ) )' % (ps, cond('i'), RD))
    cp = Closure(w, ps, {'i': ('NN0', inn), 'F': ('NN0', w.s([fn], 'adantr', '( %s -> F e. NN0 )' % ps)),
                         'G': ('NN', w.s([gn], 'adantr', '( %s -> G e. NN )' % ps)),
                         RD: ('NN0', w.s([rn], 'adantr', '( %s -> %s e. NN0 )' % (ps, RD)))})
    nle = w.s([ilt, w.s([cp.mem('i', 'RR'), cp.mem(RD, 'RR')], 'ltnled' if False else 'jca', '( %s -> ( i e. RR /\\ %s e. RR ) )' % (ps, RD))],
              'jca', '( %s -> ( i < %s /\\ ( i e. RR /\\ %s e. RR ) ) )' % (ps, RD, RD)) if False else None
    ltb = w.s([cp.mem('i', 'RR'), cp.mem(RD, 'RR')], 'ltnled', '( %s -> ( i < %s <-> -. %s <_ i ) )' % (ps, RD, RD))
    nle = w.s([ilt, ltb], 'mpbid', '( %s -> -. %s <_ i )' % (ps, RD))
    nc = w.s([imp, nle], 'mtod', '( %s -> -. %s )' % (ps, cond('i')))
    X = '( ( 2 ^ i ) x. G )'
    lb = w.s([cp.mem(X, 'RR'), cp.mem('F', 'RR')], 'lenltd', '( %s -> ( %s <_ F <-> -. F < %s ) )' % (ps, X, X))
    le2 = w.s([nc, lb], 'mpbird', '( %s -> %s <_ F )' % (ps, X))
    ral = w.s([le2], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ %s ) %s <_ F )' % (ph, RD, X))
    w.qed([rn, rs, ral], '3jca', ST_DVS)
    return w.run()


def tmidvsle():
    ph = split_imp(ST_DVSLE)[0]
    w = W('tmidvsle', 'Lean ` divSteps_le ` : the number of doublings is at most any ` N ` with ` a < 2 ^ N ` .')
    fn = w.s([], 'simpll', '( %s -> F e. NN0 )' % ph)
    gn = w.s([], 'simplr', '( %s -> G e. NN )' % ph)
    nn = w.s([], 'simprl', '( %s -> N e. NN0 )' % ph)
    lt = w.s([], 'simprr', '( %s -> F < ( 2 ^ N ) )' % ph)
    c = Closure(w, ph, {'F': ('NN0', fn), 'G': ('NN', gn), 'N': ('NN0', nn)})
    ssu, cb = sd_facts(w, ph)
    nin = in_sd(w, ph, 'N', nn, pow_ge(w, ph, c, 'N', lt), cb)
    w.qed([ssu, nin, w.inst('infssuzle')], 'syl2anc', ST_DVSLE)
    return w.run()




# ------------------------------------------------------------------ the words of the division
Z0 = '<. 1 , (/) >.'
IB = lambda x: '( inclBool o. %s )' % x
SHW = lambda e, L: '( ( (/) repeatS %s ) ++ %s )' % (e, L)
ST_W1 = '( ( L e. Word 2o /\\ E e. NN0 ) -> %s = ( <" %s "> ++ %s ) )' % (IB(SHW('( E + 1 )', 'L')), Z0, IB(SHW('E', 'L')))
ST_W2 = '( ( Q e. ZZ /\\ I e. NN0 ) -> ( <" %s "> ++ %s ) = %s )' % (Z0, IB('( Q bwrd I )'), IB('( ( 2 x. Q ) bwrd ( I + 1 ) )'))
ST_W3 = ('( ( Q e. NN0 /\\ I e. NN0 /\\ Q < ( 2 ^ I ) ) -> ( incBits ` ( ( 2 x. Q ) bwrd ( I + 1 ) ) ) = '
         '( ( ( 2 x. Q ) + 1 ) bwrd ( I + 1 ) ) )')
ST_W4 = ('( ( ( N e. NN0 /\\ A e. NN0 /\\ A < ( 2 ^ N ) ) /\\ ( L e. Word 2o /\\ ( # ` L ) <_ N /\\ ( toNat ` L ) <_ A ) ) -> '
         '( ( ( A bwrd N ) subTrunc L ) ` (/) ) = ( ( A - ( toNat ` L ) ) bwrd N ) )')
ST_W5 = ('( ( ( E e. NN0 /\\ G e. NN /\\ N e. NN0 ) /\\ ( ( 2 ^ E ) x. G ) < ( 2 ^ N ) ) -> '
         '( # ` ( ( (/) repeatS E ) ++ ( encodeNat ` G ) ) ) <_ N )')
STMTS.update({'tmidvw1': ST_W1, 'tmidvw2': ST_W2, 'tmidvw3': ST_W3, 'tmidvw4': ST_W4, 'tmidvw5': ST_W5})


def s1map(w, ph, B, bcl):
    """( ph -> ( inclBool o. <" B "> ) = <" <. 1 , B >. "> ) from bcl : ( ph -> B e. 2o )"""
    f = closed(w, ph, 'inclboolf', "inclBool : 2o --> Gamma'")
    a = w.s([bcl, f, w.inst('s1co')], 'syl2anc', '( %s -> ( inclBool o. <" %s "> ) = <" ( inclBool ` %s ) "> )' % (ph, B, B))
    v = w.s([bcl, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` %s ) = <. 1 , %s >. )' % (ph, B, B))
    b = w.s([v], 's1eqd', '( %s -> <" ( inclBool ` %s ) "> = <" <. 1 , %s >. "> )' % (ph, B, B))
    return w.s([a, b], 'eqtrd', '( %s -> ( inclBool o. <" %s "> ) = <" <. 1 , %s >. "> )' % (ph, B, B))


def tmidvw1():
    ph = split_imp(ST_W1)[0]
    w = W('tmidvw1', 'Shifting a bit word by one more zero puts the letter ` <. 1 , (/) >. ` on top of the stack '
                     '(Lean ` bits ( false :: replicate e false ++ l ) ` ).')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    en = w.s([], 'simpr', '( %s -> E e. NN0 )' % ph)
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    one = closed(w, ph, '1nn0', '1 e. NN0')
    rc = w.s([b0, one, en, w.inst('repswccat')], 'syl3anc', '( %s -> ( ( (/) repeatS 1 ) ++ ( (/) repeatS E ) ) = ( (/) repeatS ( 1 + E ) ) )' % ph)
    r1 = w.s([b0, w.inst('repsw1')], 'syl', '( %s -> ( (/) repeatS 1 ) = <" (/) "> )' % ph)
    r1b = w.s([r1], 'oveq1d', '( %s -> ( ( (/) repeatS 1 ) ++ ( (/) repeatS E ) ) = ( <" (/) "> ++ ( (/) repeatS E ) ) )' % ph)
    ec = w.s([w.s([en], 'nn0cnd', '( %s -> E e. CC )' % ph), w.s([], '1cnd', '( %s -> 1 e. CC )' % ph)], 'addcomd',
             '( %s -> ( E + 1 ) = ( 1 + E ) )' % ph)
    re = w.s([ec], 'oveq2d', '( %s -> ( (/) repeatS ( E + 1 ) ) = ( (/) repeatS ( 1 + E ) ) )' % ph)
    r2 = w.s([re, w.s([r1b, rc], 'eqtr3d', '( %s -> ( <" (/) "> ++ ( (/) repeatS E ) ) = ( (/) repeatS ( 1 + E ) ) )' % ph)], 'eqtr4d',
             '( %s -> ( (/) repeatS ( E + 1 ) ) = ( <" (/) "> ++ ( (/) repeatS E ) ) )' % ph)
    r3 = w.s([r2], 'oveq1d', '( %s -> %s = ( ( <" (/) "> ++ ( (/) repeatS E ) ) ++ L ) )' % (ph, SHW('( E + 1 )', 'L')))
    s1w = w.s([b0], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ph)
    rw = w.s([b0, en, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS E ) e. Word 2o )' % ph)
    ca = w.s([s1w, rw, ll, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" (/) "> ++ ( (/) repeatS E ) ) ++ L ) = ( <" (/) "> ++ %s ) )' % (ph, SHW('E', 'L')))
    r4 = w.s([r3, ca], 'eqtrd', '( %s -> %s = ( <" (/) "> ++ %s ) )' % (ph, SHW('( E + 1 )', 'L'), SHW('E', 'L')))
    c1 = w.s([r4], 'coeq2d', '( %s -> %s = %s )' % (ph, IB(SHW('( E + 1 )', 'L')), IB('( <" (/) "> ++ %s )' % SHW('E', 'L'))))
    shw = w.s([rw, ll, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, SHW('E', 'L')))
    mc = w.s([s1w, shw, w.inst('bwmapccat')], 'syl2anc', '( %s -> %s = ( ( inclBool o. <" (/) "> ) ++ %s ) )'
             % (ph, IB('( <" (/) "> ++ %s )' % SHW('E', 'L')), IB(SHW('E', 'L'))))
    sm = s1map(w, ph, '(/)', b0)
    sm2 = w.s([sm], 'oveq1d', '( %s -> ( ( inclBool o. <" (/) "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, IB(SHW('E', 'L')), Z0, IB(SHW('E', 'L'))))
    w.qed([w.s([c1, mc], 'eqtrd', '( %s -> %s = ( ( inclBool o. <" (/) "> ) ++ %s ) )' % (ph, IB(SHW('( E + 1 )', 'L')), IB(SHW('E', 'L')))), sm2],
          'eqtrd', ST_W1)
    return w.run()


def tmidvw2():
    ph = split_imp(ST_W2)[0]
    w = W('tmidvw2', 'Pushing a zero bit on the ` I ` -bit word of ` Q ` gives the ` I + 1 ` -bit word of ` 2 Q ` '
                     '(the quotient of the shift-down loop doubles, Lean ` false :: ql ` ).')
    qz = w.s([], 'simpl', '( %s -> Q e. ZZ )' % ph)
    inn = w.s([], 'simpr', '( %s -> I e. NN0 )' % ph)
    q2 = '( 2 x. Q )'
    q2z = w.s([w.s([], '2z', '2 e. ZZ') if False else closed(w, ph, '2z', '2 e. ZZ'), qz], 'zmulcld', '( %s -> %s e. ZZ )' % (ph, q2))
    bc = w.s([q2z, inn, w.inst('bwrdcons')], 'syl2anc', '( %s -> ( %s bwrd ( I + 1 ) ) = ( <" if ( 0 e. ( bits ` %s ) , 1o , (/) ) "> ++ ( ( |_ ` ( %s / 2 ) ) bwrd I ) ) )'
             % (ph, q2, q2, q2))
    ne = w.s([qz, w.inst('bits0e')], 'syl', '( %s -> -. 0 e. ( bits ` %s ) )' % (ph, q2))
    iff = w.s([ne], 'iffalsed', '( %s -> if ( 0 e. ( bits ` %s ) , 1o , (/) ) = (/) )' % (ph, q2))
    s1e = w.s([iff], 's1eqd', '( %s -> <" if ( 0 e. ( bits ` %s ) , 1o , (/) ) "> = <" (/) "> )' % (ph, q2))
    qc = w.s([qz], 'zcnd', '( %s -> Q e. CC )' % ph)
    dv = w.s([qc, w.s([], '2cnd', '( %s -> 2 e. CC )' % ph), w.s([], '2ne0' if False else '2ne0', '2 =/= 0') if False else None], 'divcan3d', '') if False else None
    two_ne = closed(w, ph, '2ne0', '2 =/= 0')
    dv = w.s([qc, w.s([], '2cnd', '( %s -> 2 e. CC )' % ph), two_ne], 'divcan3d', '( %s -> ( %s / 2 ) = Q )' % (ph, q2))
    fl = w.s([w.s([dv], 'fveq2d', '( %s -> ( |_ ` ( %s / 2 ) ) = ( |_ ` Q ) )' % (ph, q2)), w.s([qz, w.inst('flid')], 'syl', '( %s -> ( |_ ` Q ) = Q )' % ph)],
             'eqtrd', '( %s -> ( |_ ` ( %s / 2 ) ) = Q )' % (ph, q2))
    fb = w.s([fl], 'oveq1d', '( %s -> ( ( |_ ` ( %s / 2 ) ) bwrd I ) = ( Q bwrd I ) )' % (ph, q2))
    cc = w.s([s1e, fb], 'oveq12d', '( %s -> ( <" if ( 0 e. ( bits ` %s ) , 1o , (/) ) "> ++ ( ( |_ ` ( %s / 2 ) ) bwrd I ) ) = ( <" (/) "> ++ ( Q bwrd I ) ) )'
             % (ph, q2, q2))
    e = w.s([bc, cc], 'eqtrd', '( %s -> ( %s bwrd ( I + 1 ) ) = ( <" (/) "> ++ ( Q bwrd I ) ) )' % (ph, q2))
    c1 = w.s([e], 'coeq2d', '( %s -> %s = %s )' % (ph, IB('( %s bwrd ( I + 1 ) )' % q2), IB('( <" (/) "> ++ ( Q bwrd I ) )')))
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    s1w = w.s([b0], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ph)
    bw = w.s([qz, inn, w.inst('bwrdcl')], 'syl2anc', '( %s -> ( Q bwrd I ) e. Word 2o )' % ph)
    mc = w.s([s1w, bw, w.inst('bwmapccat')], 'syl2anc', '( %s -> %s = ( ( inclBool o. <" (/) "> ) ++ %s ) )'
             % (ph, IB('( <" (/) "> ++ ( Q bwrd I ) )'), IB('( Q bwrd I )')))
    sm = s1map(w, ph, '(/)', b0)
    sm2 = w.s([sm], 'oveq1d', '( %s -> ( ( inclBool o. <" (/) "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ph, IB('( Q bwrd I )'), Z0, IB('( Q bwrd I )')))
    t = w.s([w.s([c1, mc], 'eqtrd', '( %s -> %s = ( ( inclBool o. <" (/) "> ) ++ %s ) )' % (ph, IB('( %s bwrd ( I + 1 ) )' % q2), IB('( Q bwrd I )'))), sm2],
            'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, IB('( %s bwrd ( I + 1 ) )' % q2), Z0, IB('( Q bwrd I )')))
    w.qed([t], 'eqcomd', ST_W2)
    return w.run()


def tmidvw3():
    ph = split_imp(ST_W3)[0]
    w = W('tmidvw3', 'Incrementing the ` I + 1 ` -bit word of an even ` 2 Q ` with ` Q < 2 ^ I ` sets its low bit '
                     '(the quotient bit of a subtraction step, Lean ` incBits ( false :: ql ) = true :: ql ` ).')
    qn = w.s([], 'simp1', '( %s -> Q e. NN0 )' % ph)
    inn = w.s([], 'simp2', '( %s -> I e. NN0 )' % ph)
    qlt = w.s([], 'simp3', '( %s -> Q < ( 2 ^ I ) )' % ph)
    c = Closure(w, ph, {'Q': ('NN0', qn), 'I': ('NN0', inn)})
    q2 = '( 2 x. Q )'; I1 = '( I + 1 )'
    L = '( %s bwrd %s )' % (q2, I1)
    q2n = c.mem(q2, 'NN0'); i1n = c.mem(I1, 'NN0')
    q2z = c.mem(q2, 'ZZ')
    lw = w.s([q2z, i1n, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, L))
    iv = w.s([lw, w.inst('incbitsval')], 'syl', '( %s -> ( incBits ` %s ) = ( ( ( toNat ` %s ) + 1 ) bwrd if ( ( ( toNat ` %s ) + 1 ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) + 1 ) , ( # ` %s ) ) ) )'
             % (ph, L, L, L, L, L, L))
    ep = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ph), inn], 'expp1d', '( %s -> ( 2 ^ %s ) = ( ( 2 ^ I ) x. 2 ) )' % (ph, I1))
    c.atom('( 2 ^ I )'); c.atom('( 2 ^ %s )' % I1)
    lt2 = linarith(w, ph, [qlt, ep], '%s < ( 2 ^ %s )' % (q2, I1), closure=c)
    tn = w.s([q2n, i1n, lt2, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = %s )' % (ph, L, q2))
    ln = w.s([q2z, i1n, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, L, I1))
    # 2 Q + 1 < 2 ^ ( I + 1 )  (Q + 1 <_ 2 ^ I)
    qz = c.mem('Q', 'ZZ'); pz = c.mem('( 2 ^ I )', 'ZZ')
    qle = w.s([qz, pz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( Q < ( 2 ^ I ) <-> ( Q + 1 ) <_ ( 2 ^ I ) ) )' % ph)
    qle2 = w.s([qlt, qle], 'mpbid', '( %s -> ( Q + 1 ) <_ ( 2 ^ I ) )' % ph)
    lt3 = linarith(w, ph, [qle2, ep], '( %s + 1 ) < ( 2 ^ %s )' % (q2, I1), closure=c)
    ne0 = w.s([lt3], 'ltned', '( %s -> ( %s + 1 ) =/= ( 2 ^ %s ) )' % (ph, q2, I1))
    ne = w.s([ne0], 'neneqd', '( %s -> -. ( %s + 1 ) = ( 2 ^ %s ) )' % (ph, q2, I1))
    # rewrite the pieces
    t1 = w.s([tn], 'oveq1d', '( %s -> ( ( toNat ` %s ) + 1 ) = ( %s + 1 ) )' % (ph, L, q2))
    p1 = w.s([ln], 'oveq2d', '( %s -> ( 2 ^ ( # ` %s ) ) = ( 2 ^ %s ) )' % (ph, L, I1))
    eq = w.s([t1, p1], 'eqeq12d', '( %s -> ( ( ( toNat ` %s ) + 1 ) = ( 2 ^ ( # ` %s ) ) <-> ( %s + 1 ) = ( 2 ^ %s ) ) )' % (ph, L, L, q2, I1))
    ne2 = w.s([eq, ne], 'mtbird', '( %s -> -. ( ( toNat ` %s ) + 1 ) = ( 2 ^ ( # ` %s ) ) )' % (ph, L, L))
    iff = w.s([ne2], 'iffalsed', '( %s -> if ( ( ( toNat ` %s ) + 1 ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) + 1 ) , ( # ` %s ) ) = ( # ` %s ) )'
              % (ph, L, L, L, L, L))
    iff2 = w.s([iff, ln], 'eqtrd', '( %s -> if ( ( ( toNat ` %s ) + 1 ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) + 1 ) , ( # ` %s ) ) = %s )'
               % (ph, L, L, L, L, I1))
    o = w.s([t1, iff2], 'oveq12d', '( %s -> ( ( ( toNat ` %s ) + 1 ) bwrd if ( ( ( toNat ` %s ) + 1 ) = ( 2 ^ ( # ` %s ) ) , ( ( # ` %s ) + 1 ) , ( # ` %s ) ) ) = ( ( %s + 1 ) bwrd %s ) )'
            % (ph, L, L, L, L, L, q2, I1))
    w.qed([iv, o], 'eqtrd', ST_W3)
    return w.run()


def tmidvw4():
    ph = split_imp(ST_W4)[0]
    w = W('tmidvw4', 'Subtracting a word of value at most ` A ` and length at most ` N ` from the ` N ` -bit word of '
                     '` A ` gives the ` N ` -bit word of the difference (no borrow; Lean ` subTrunc ` on the remainder).')
    nn = w.s([], 'simpl1', '( %s -> N e. NN0 )' % ph)
    an = w.s([], 'simpl2', '( %s -> A e. NN0 )' % ph)
    alt = w.s([], 'simpl3', '( %s -> A < ( 2 ^ N ) )' % ph)
    lw = w.s([], 'simpr1', '( %s -> L e. Word 2o )' % ph)
    lle = w.s([], 'simpr2', '( %s -> ( # ` L ) <_ N )' % ph)
    tle = w.s([], 'simpr3', '( %s -> ( toNat ` L ) <_ A )' % ph)
    X = '( A bwrd N )'
    c = Closure(w, ph, {'N': ('NN0', nn), 'A': ('NN0', an)})
    az = c.mem('A', 'ZZ')
    xw = w.s([az, nn, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, X))
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    tv = w.s([xw, lw, b0, w.inst('subtruncval')], 'syl3anc', '( %s -> ( ( %s subTrunc L ) ` (/) ) = if ( ( ( %s subBorrow L ) ` (/) ) = 1o , (/) , ( ( %s subBits L ) ` (/) ) ) )'
             % (ph, X, X, X))
    tx = w.s([an, nn, alt, w.inst('tonatbwrd2')], 'syl3anc', '( %s -> ( toNat ` %s ) = A )' % (ph, X))
    bn = closed(w, ph, 'bwbn0', '( bToNat ` (/) ) = 0')
    tl = w.s([lw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` L ) e. NN0 )' % ph)
    c.leaf('( toNat ` L )', 'NN0', tl)
    c.leaf('( toNat ` %s )' % X, 'NN0', w.s([xw, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, X)))
    c.leaf('( bToNat ` (/) )', 'NN0', w.s([b0, w.inst('bwbncl')], 'syl', '( %s -> ( bToNat ` (/) ) e. NN0 )' % ph))
    le2 = linarith(w, ph, [tle, tx, bn], '( ( toNat ` L ) + ( bToNat ` (/) ) ) <_ ( toNat ` %s )' % X, closure=c)
    be = w.s([xw, lw, b0, w.inst('subborroweq0')], 'syl3anc', '( %s -> ( ( ( %s subBorrow L ) ` (/) ) = (/) <-> ( ( toNat ` L ) + ( bToNat ` (/) ) ) <_ ( toNat ` %s ) ) )'
             % (ph, X, X))
    b00 = w.s([le2, be], 'mpbird', '( %s -> ( ( %s subBorrow L ) ` (/) ) = (/) )' % (ph, X))
    n1 = w.s([closed(w, ph, '1n0', '1o =/= (/)')], 'necomd', '( %s -> (/) =/= 1o )' % ph)
    nb = w.s([b00, n1], 'eqnetrd', '( %s -> ( ( %s subBorrow L ) ` (/) ) =/= 1o )' % (ph, X))
    nb2 = w.s([nb], 'neneqd', '( %s -> -. ( ( %s subBorrow L ) ` (/) ) = 1o )' % (ph, X))
    iff = w.s([nb2], 'iffalsed', '( %s -> if ( ( ( %s subBorrow L ) ` (/) ) = 1o , (/) , ( ( %s subBits L ) ` (/) ) ) = ( ( %s subBits L ) ` (/) ) )'
              % (ph, X, X, X))
    sv = w.s([xw, lw, b0, w.inst('subbitsval')], 'syl3anc',
             '( %s -> ( ( %s subBits L ) ` (/) ) = ( ( ( toNat ` %s ) - ( ( toNat ` L ) + ( bToNat ` (/) ) ) ) bwrd if ( ( # ` %s ) <_ ( # ` L ) , ( # ` L ) , ( # ` %s ) ) ) )'
             % (ph, X, X, X, X))
    xl = w.s([az, nn, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = N )' % (ph, X))
    # the max is N
    lnn = w.s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    c.leaf('( # ` L )', 'NN0', lnn); c.atom('( # ` %s )' % X)
    MX = 'if ( ( # ` %s ) <_ ( # ` L ) , ( # ` L ) , ( # ` %s ) )' % (X, X)
    # case split on ( # ` X ) <_ ( # ` L ): then # L = N
    ps = '( %s /\\ ( # ` %s ) <_ ( # ` L ) )' % (ph, X)
    it = w.s([], 'simpr', '( %s -> ( # ` %s ) <_ ( # ` L ) )' % (ps, X))
    i1 = w.s([it], 'iftrued', '( %s -> %s = ( # ` L ) )' % (ps, MX))
    cps = Closure(w, ps, {'N': ('NN0', w.s([nn], 'adantr', '( %s -> N e. NN0 )' % ps)),
                          '( # ` L )': ('NN0', w.s([lnn], 'adantr', '( %s -> ( # ` L ) e. NN0 )' % ps))})
    cps.leaf('( # ` %s )' % X, 'NN0', w.s([w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, X))], 'adantr', '( %s -> ( # ` %s ) e. NN0 )' % (ps, X)))
    eqn = lineq(w, ps, '( # ` L )', 'N', hyps=[w.s([lle], 'adantr', '( %s -> ( # ` L ) <_ N )' % ps), it,
                                              w.s([xl], 'adantr', '( %s -> ( # ` %s ) = N )' % (ps, X))], closure=cps)
    ca = w.s([i1, eqn], 'eqtrd', '( %s -> %s = N )' % (ps, MX))
    ps2 = '( %s /\\ -. ( # ` %s ) <_ ( # ` L ) )' % (ph, X)
    i2 = w.s([w.s([], 'simpr', '( %s -> -. ( # ` %s ) <_ ( # ` L ) )' % (ps2, X))], 'iffalsed', '( %s -> %s = ( # ` %s ) )' % (ps2, MX, X))
    cb = w.s([i2, w.s([xl], 'adantr', '( %s -> ( # ` %s ) = N )' % (ps2, X))], 'eqtrd', '( %s -> %s = N )' % (ps2, MX))
    mx = w.s([ca, cb], 'pm2.61dan', '( %s -> %s = N )' % (ph, MX))
    dif = w.s([w.s([tx, w.s([bn], 'oveq2d', '( %s -> ( ( toNat ` L ) + ( bToNat ` (/) ) ) = ( ( toNat ` L ) + 0 ) )' % ph)], 'oveq12d',
                   '( %s -> ( ( toNat ` %s ) - ( ( toNat ` L ) + ( bToNat ` (/) ) ) ) = ( A - ( ( toNat ` L ) + 0 ) ) )' % (ph, X)),
               w.s([w.s([w.s([tl], 'nn0cnd', '( %s -> ( toNat ` L ) e. CC )' % ph)], 'addridd', '( %s -> ( ( toNat ` L ) + 0 ) = ( toNat ` L ) )' % ph)],
                   'oveq2d', '( %s -> ( A - ( ( toNat ` L ) + 0 ) ) = ( A - ( toNat ` L ) ) )' % ph)], 'eqtrd',
              '( %s -> ( ( toNat ` %s ) - ( ( toNat ` L ) + ( bToNat ` (/) ) ) ) = ( A - ( toNat ` L ) ) )' % (ph, X))
    o = w.s([dif, mx], 'oveq12d', '( %s -> ( ( ( toNat ` %s ) - ( ( toNat ` L ) + ( bToNat ` (/) ) ) ) bwrd %s ) = ( ( A - ( toNat ` L ) ) bwrd N ) )' % (ph, X, MX))
    w.qed([w.s([w.s([tv, iff], 'eqtrd', '( %s -> ( ( %s subTrunc L ) ` (/) ) = ( ( %s subBits L ) ` (/) ) )' % (ph, X, X)), sv], 'eqtrd',
               '( %s -> ( ( %s subTrunc L ) ` (/) ) = ( ( ( toNat ` %s ) - ( ( toNat ` L ) + ( bToNat ` (/) ) ) ) bwrd %s ) )' % (ph, X, X, MX)), o],
          'eqtrd', ST_W4)
    return w.run()


def tmidvw5():
    ph = split_imp(ST_W5)[0]
    w = W('tmidvw5', 'A shifted canonical word whose value is below ` 2 ^ N ` has length at most ` N ` (the '
                     'subtracted shift is never longer than the remainder).')
    en = w.s([], 'simpl1', '( %s -> E e. NN0 )' % ph)
    gn = w.s([], 'simpl2', '( %s -> G e. NN )' % ph)
    nn = w.s([], 'simpl3', '( %s -> N e. NN0 )' % ph)
    lt = w.s([], 'simpr', '( %s -> ( ( 2 ^ E ) x. G ) < ( 2 ^ N ) )' % ph)
    EG = '( encodeNat ` G )'
    c = Closure(w, ph, {'E': ('NN0', en), 'G': ('NN', gn), 'N': ('NN0', nn)})
    gn0 = c.mem('G', 'NN0')
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    rw = w.s([b0, en, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS E ) e. Word 2o )' % ph)
    ew = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    cl_ = w.s([rw, ew, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` ( (/) repeatS E ) ) + ( # ` %s ) ) )' % (ph, SHW('E', EG), EG))
    rl = w.s([b0, en, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS E ) ) = E )' % ph)
    B = '( # ` %s )' % EG
    bn = w.s([ew, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, B))
    # B e. NN: G >= 1 so B = bl G >= 1
    c.leaf(B, 'NN0', bn)
    # 2 ^ ( B - 1 ) <_ G , from encnatlenle at M := B (needs B e. NN)
    e1 = w.s([gn0, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` G ) )' % (ph, B))
    e2 = w.s([gn, w.inst('blpos')], 'syl', '( %s -> ( bl ` G ) = ( ( 2 Nlog G ) + 1 ) )' % ph)
    nl = c.mem('( 2 Nlog G )', 'NN0')
    pn = w.s([nl, w.inst('nn0p1nn')], 'syl', '( %s -> ( ( 2 Nlog G ) + 1 ) e. NN )' % ph)
    bnn = w.s([w.s([e1, e2], 'eqtrd', '( %s -> %s = ( ( 2 Nlog G ) + 1 ) )' % (ph, B)), pn], 'eqeltrd', '( %s -> %s e. NN )' % (ph, B))
    ble = w.s([w.s([B], 'leidd' if False else 'leidd', '') if False else None], '', '') if False else None
    bb = w.s([w.s([bn], 'nn0red', '( %s -> %s e. RR )' % (ph, B))], 'leidd', '( %s -> %s <_ %s )' % (ph, B, B))
    p = w.s([gn0, bnn, bb, w.inst('encnatlenle')], 'syl3anc', '( %s -> ( 2 ^ ( %s - 1 ) ) <_ G )' % (ph, B))
    # 2 ^ ( E + ( B - 1 ) ) = 2 ^ E x. 2 ^ ( B - 1 ) <_ 2 ^ E x. G < 2 ^ N
    B1 = '( %s - 1 )' % B
    b1n = w.s([bnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, B1))
    c.have(B1, 'NN0', b1n)
    ea = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ph), b1n, en], 'expaddd', '( %s -> ( 2 ^ ( %s + E ) ) = ( ( 2 ^ %s ) x. ( 2 ^ E ) ) )' % (ph, B1, B1)) if False else None
    ea = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ph), en, b1n], 'expaddd', '( %s -> ( 2 ^ ( E + %s ) ) = ( ( 2 ^ E ) x. ( 2 ^ %s ) ) )' % (ph, B1, B1))
    for a in ['( 2 ^ E )', '( 2 ^ %s )' % B1, '( 2 ^ ( E + %s ) )' % B1, '( 2 ^ N )']:
        c.atom(a)
    pe = c.ge0('( 2 ^ E )')
    lt2 = nlinarith(w, ph, [ea, p, lt, pe], '( 2 ^ ( E + %s ) ) < ( 2 ^ N )' % B1, closure=c)
    two = closed(w, ph, '1lt2', '1 < 2')
    ez = c.mem('( E + %s )' % B1, 'ZZ'); nz = c.mem('N', 'ZZ')
    le3 = w.s([w.s([closed(w, ph, '2re', '2 e. RR'), ez, nz], '3jca', '( %s -> ( 2 e. RR /\\ ( E + %s ) e. ZZ /\\ N e. ZZ ) )' % (ph, B1)), two, w.inst('ltexp2')],
              'syl2anc', '( %s -> ( ( E + %s ) < N <-> ( 2 ^ ( E + %s ) ) < ( 2 ^ N ) ) )' % (ph, B1, B1))
    lt4 = w.s([lt2, le3], 'mpbird', '( %s -> ( E + %s ) < N )' % (ph, B1))
    shw_ = w.s([rw, ew, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, SHW('E', EG)))
    c.leaf('( # ` %s )' % SHW('E', EG), 'NN0', w.s([shw_, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, SHW('E', EG))))
    c.leaf('( # ` ( (/) repeatS E ) )', 'NN0', w.s([rw, w.inst('lencl')], 'syl', '( %s -> ( # ` ( (/) repeatS E ) ) e. NN0 )' % ph))
    w.qed([linarith(w, ph, [cl_, rl, lt4], '( # ` %s ) <_ N' % SHW('E', EG), closure=c)], 'id', ST_W5) if False else None
    zl = w.s([ez, nz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( ( E + %s ) < N <-> ( ( E + %s ) + 1 ) <_ N ) )' % (ph, B1, B1))
    lt5 = w.s([lt4, zl], 'mpbid', '( %s -> ( ( E + %s ) + 1 ) <_ N )' % (ph, B1))
    fin = linarith(w, ph, [cl_, rl, lt5], '( # ` %s ) <_ N' % SHW('E', EG), closure=c)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
