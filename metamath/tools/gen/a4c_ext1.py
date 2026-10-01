"""Sortie A4c, batch 14: arithmetic for the round argument of extractGo."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ------------------------------------------------------------------ modone
if not only or 'modone' in only:
    w = W('modone', 'A number congruent to one modulo the modulus has residue one.')
    A = '( ( M e. NN0 /\\ L e. NN ) /\\ L || ( M - 1 ) )'
    mm = w.s([w.s([], 'simpl', '( %s -> ( M e. NN0 /\\ L e. NN ) )' % A)], 'simpld', '( %s -> M e. NN0 )' % A)
    ll = w.s([w.s([], 'simpl', '( %s -> ( M e. NN0 /\\ L e. NN ) )' % A)], 'simprd', '( %s -> L e. NN )' % A)
    dv = w.s([], 'simpr', '( %s -> L || ( M - 1 ) )' % A)
    bi = w.s([ll, w.s([mm], 'nn0zd', '( %s -> M e. ZZ )' % A),
              w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A), w.inst('moddvds')], 'syl3anc',
             '( %s -> ( ( M mod L ) = ( 1 mod L ) <-> L || ( M - 1 ) ) )' % A)
    w.qed([dv, bi], 'mpbird', '( %s -> ( M mod L ) = ( 1 mod L ) )' % A)
    run(w)

# ------------------------------------------------------------------ extgocbd
if not only or 'extgocbd' in only:
    w = W('extgocbd', 'The supply inequality forces a hit within the batch.')
    A = '( ( C e. RR /\\ D e. RR /\\ B e. RR ) /\\ ( E e. RR /\\ ( C + B ) <_ D /\\ D <_ ( ( 0 + C ) + E ) ) )'
    cc = w.s([w.s([], 'simpl', '( %s -> ( C e. RR /\\ D e. RR /\\ B e. RR ) )' % A)], 'simp1d', '( %s -> C e. RR )' % A)
    dd = w.s([w.s([], 'simpl', '( %s -> ( C e. RR /\\ D e. RR /\\ B e. RR ) )' % A)], 'simp2d', '( %s -> D e. RR )' % A)
    bb = w.s([w.s([], 'simpl', '( %s -> ( C e. RR /\\ D e. RR /\\ B e. RR ) )' % A)], 'simp3d', '( %s -> B e. RR )' % A)
    ee = w.s([w.s([], 'simpr', '( %s -> ( E e. RR /\\ ( C + B ) <_ D /\\ D <_ ( ( 0 + C ) + E ) ) )' % A)], 'simp1d',
             '( %s -> E e. RR )' % A)
    h1 = w.s([w.s([], 'simpr', '( %s -> ( E e. RR /\\ ( C + B ) <_ D /\\ D <_ ( ( 0 + C ) + E ) ) )' % A)], 'simp2d',
             '( %s -> ( C + B ) <_ D )' % A)
    h2 = w.s([w.s([], 'simpr', '( %s -> ( E e. RR /\\ ( C + B ) <_ D /\\ D <_ ( ( 0 + C ) + E ) ) )' % A)], 'simp3d',
             '( %s -> D <_ ( ( 0 + C ) + E ) )' % A)
    li = lin.linarith(w, A, [h1, h2], 'B <_ E', leaves={'C': cc, 'D': dd, 'B': bb, 'E': ee})
    w.lines[-1] = w.lines[-1].replace('%s:' % li, 'qed:', 1)
    run(w)

# ------------------------------------------------------------------ extgol1
L1 = '( L + 1 )'
PW = '( %s ^ H )' % L1
LG = '( %s Nlog N )' % L1
PWL = '( %s ^ ( %s + 1 ) )' % (L1, LG)
SUP = '( ( %s + 1 ) x. B ) <_ ( ( 0 + ( H x. B ) ) + E )' % LG
HYP = '( ( ( %s <_ M /\\ M <_ N ) /\\ E < B ) /\\ %s )' % (PW, SUP)

if not only or 'extgol1' in only:
    w = W('extgol1', 'The extraction loop cannot run out of pool while the supply holds.')
    A = '( ( L e. NN /\\ 2 <_ L ) /\\ ( N e. NN0 /\\ B e. NN ) /\\ ( M e. NN0 /\\ H e. NN0 /\\ E e. NN0 ) )'
    U = '( %s /\\ %s )' % (A, HYP)
    a = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (U, f))
    ll = a(w.s([w.s([], 'simp1', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)], 'simpld', '( %s -> L e. NN )' % A), 'L e. NN')
    l2 = a(w.s([w.s([], 'simp1', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)], 'simprd', '( %s -> 2 <_ L )' % A), '2 <_ L')
    nn = a(w.s([w.s([], 'simp2', '( %s -> ( N e. NN0 /\\ B e. NN ) )' % A)], 'simpld', '( %s -> N e. NN0 )' % A), 'N e. NN0')
    bb = a(w.s([w.s([], 'simp2', '( %s -> ( N e. NN0 /\\ B e. NN ) )' % A)], 'simprd', '( %s -> B e. NN )' % A), 'B e. NN')
    mm = a(w.s([w.s([], 'simp3', '( %s -> ( M e. NN0 /\\ H e. NN0 /\\ E e. NN0 ) )' % A)], 'simp1d', '( %s -> M e. NN0 )' % A), 'M e. NN0')
    hh = a(w.s([w.s([], 'simp3', '( %s -> ( M e. NN0 /\\ H e. NN0 /\\ E e. NN0 ) )' % A)], 'simp2d', '( %s -> H e. NN0 )' % A), 'H e. NN0')
    ee = a(w.s([w.s([], 'simp3', '( %s -> ( M e. NN0 /\\ H e. NN0 /\\ E e. NN0 ) )' % A)], 'simp3d', '( %s -> E e. NN0 )' % A), 'E e. NN0')
    hy = w.s([], 'simpr', '( %s -> %s )' % (U, HYP))
    h1 = w.s([w.s([w.s([hy], 'simpld', '( %s -> ( ( %s <_ M /\\ M <_ N ) /\\ E < B ) )' % (U, PW))], 'simpld',
                  '( %s -> ( %s <_ M /\\ M <_ N ) )' % (U, PW))], 'simpld', '( %s -> %s <_ M )' % (U, PW))
    h2 = w.s([w.s([w.s([hy], 'simpld', '( %s -> ( ( %s <_ M /\\ M <_ N ) /\\ E < B ) )' % (U, PW))], 'simpld',
                  '( %s -> ( %s <_ M /\\ M <_ N ) )' % (U, PW))], 'simprd', '( %s -> M <_ N )' % U)
    h3 = w.s([w.s([hy], 'simpld', '( %s -> ( ( %s <_ M /\\ M <_ N ) /\\ E < B ) )' % (U, PW))], 'simprd',
             '( %s -> E < B )' % U)
    h4 = w.s([hy], 'simprd', '( %s -> %s )' % (U, SUP))
    l1n = w.s([ll, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (U, L1))
    l1n0 = w.s([l1n], 'nnnn0d', '( %s -> %s e. NN0 )' % (U, L1))
    l1r = w.s([l1n], 'nnred', '( %s -> %s e. RR )' % (U, L1))
    lr = w.s([ll], 'nnred', '( %s -> L e. RR )' % U)
    pwn = w.s([l1n, hh, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (U, PW))
    pw1 = w.s([pwn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (U, PW))
    pwr = w.s([pwn], 'nnred', '( %s -> %s e. RR )' % (U, PW))
    mr = w.s([mm], 'nn0red', '( %s -> M e. RR )' % U)
    nr = w.s([nn], 'nn0red', '( %s -> N e. RR )' % U)
    br = w.s([bb], 'nnred', '( %s -> B e. RR )' % U)
    er = w.s([ee], 'nn0red', '( %s -> E e. RR )' % U)
    hr = w.s([hh], 'nn0red', '( %s -> H e. RR )' % U)
    n1 = lin.linarith(w, U, [pw1, h1, h2], '1 <_ N', leaves={PW: pwr, 'M': mr, 'N': nr})
    nnn = w.s([w.s([nn, n1], 'jca', '( %s -> ( N e. NN0 /\\ 1 <_ N ) )' % U),
               w.s([w.s([], 'elnnnn0c', '( N e. NN <-> ( N e. NN0 /\\ 1 <_ N ) )')], 'a1i',
                   '( %s -> ( N e. NN <-> ( N e. NN0 /\\ 1 <_ N ) ) )' % U)], 'mpbird', '( %s -> N e. NN )' % U)
    l1uj = w.s([w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % U),
                w.s([l1n], 'nnzd', '( %s -> %s e. ZZ )' % (U, L1)),
                lin.linarith(w, U, [l2], '2 <_ %s' % L1, leaves={'L': lr})], '3jca',
               '( %s -> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (U, L1, L1))
    l1u = w.s([l1uj, w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` 2 ) )' % (U, L1))
    lgn = w.s([l1n0, nn, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (U, LG))
    lgr = w.s([lgn], 'nn0red', '( %s -> %s e. RR )' % (U, LG))
    # ---- ( LG + 1 ) <_ H
    NB = '( %s /\\ -. ( %s + 1 ) <_ H )' % (U, LG)
    nb = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (NB, f))
    hlt = w.s([w.s([nb(hr, 'H e. RR'), w.s([nb(lgr, '%s e. RR' % LG), w.inst('peano2re')], 'syl', '( %s -> ( %s + 1 ) e. RR )' % (NB, LG))],
                   'ltnled', '( %s -> ( H < ( %s + 1 ) <-> -. ( %s + 1 ) <_ H ) )' % (NB, LG, LG)),
               w.s([], 'simpr', '( %s -> -. ( %s + 1 ) <_ H )' % (NB, LG))], 'mpbird', '( %s -> H < ( %s + 1 ) )' % (NB, LG))
    hp1 = w.s([w.s([w.s([w.s([nb(hh, 'H e. NN0')], 'nn0zd', '( %s -> H e. ZZ )' % NB),
                         w.s([w.s([nb(lgn, '%s e. NN0' % LG)], 'nn0zd', '( %s -> %s e. ZZ )' % (NB, LG)),
                              w.inst('peano2z')], 'syl', '( %s -> ( %s + 1 ) e. ZZ )' % (NB, LG))], 'jca',
                        '( %s -> ( H e. ZZ /\\ ( %s + 1 ) e. ZZ ) )' % (NB, LG)), w.inst('zltp1le')], 'syl',
                   '( %s -> ( H < ( %s + 1 ) <-> ( H + 1 ) <_ ( %s + 1 ) ) )' % (NB, LG, LG)), hlt], 'mpbid',
              '( %s -> ( H + 1 ) <_ ( %s + 1 ) )' % (NB, LG))
    mule = w.s([w.s([w.s([w.s([nb(hr, 'H e. RR'), w.inst('peano2re')], 'syl', '( %s -> ( H + 1 ) e. RR )' % NB),
                          w.s([nb(lgr, '%s e. RR' % LG), w.inst('peano2re')], 'syl', '( %s -> ( %s + 1 ) e. RR )' % (NB, LG)),
                          w.s([nb(br, 'B e. RR'), w.s([w.s([nb(bb, 'B e. NN')], 'nnnn0d', '( %s -> B e. NN0 )' % NB)], 'nn0ge0d',
                                                      '( %s -> 0 <_ B )' % NB)], 'jca',
                              '( %s -> ( B e. RR /\\ 0 <_ B ) )' % NB)], '3jca',
                         '( %s -> ( ( H + 1 ) e. RR /\\ ( %s + 1 ) e. RR /\\ ( B e. RR /\\ 0 <_ B ) ) )' % (NB, LG)), hp1], 'jca',
                    '( %s -> ( ( ( H + 1 ) e. RR /\\ ( %s + 1 ) e. RR /\\ ( B e. RR /\\ 0 <_ B ) ) /\\ ( H + 1 ) <_ ( %s + 1 ) ) )' % (NB, LG, LG)),
                w.inst('lemul1a')], 'syl', '( %s -> ( ( H + 1 ) x. B ) <_ ( ( %s + 1 ) x. B ) )' % (NB, LG))
    dist = w.s([w.s([nb(hr, 'H e. RR')], 'recnd', '( %s -> H e. CC )' % NB),
                w.s([nb(br, 'B e. RR')], 'recnd', '( %s -> B e. CC )' % NB)], 'adddirp1d',
               '( %s -> ( ( H + 1 ) x. B ) = ( ( H x. B ) + B ) )' % NB)
    mule2 = w.s([w.s([dist], 'eqcomd', '( %s -> ( ( H x. B ) + B ) = ( ( H + 1 ) x. B ) )' % NB), mule], 'eqbrtrd',
                '( %s -> ( ( H x. B ) + B ) <_ ( ( %s + 1 ) x. B ) )' % (NB, LG))
    hbr = w.s([nb(hr, 'H e. RR'), nb(br, 'B e. RR')], 'remulcld', '( %s -> ( H x. B ) e. RR )' % NB)
    lgbr = w.s([w.s([nb(lgr, '%s e. RR' % LG), w.inst('peano2re')], 'syl', '( %s -> ( %s + 1 ) e. RR )' % (NB, LG)), nb(br, 'B e. RR')],
               'remulcld', '( %s -> ( ( %s + 1 ) x. B ) e. RR )' % (NB, LG))
    ble = w.s([w.s([w.s([hbr, lgbr, nb(br, 'B e. RR')], '3jca',
                        '( %s -> ( ( H x. B ) e. RR /\\ ( ( %s + 1 ) x. B ) e. RR /\\ B e. RR ) )' % (NB, LG)),
                    w.s([nb(er, 'E e. RR'), mule2, nb(h4, SUP)], '3jca',
                        '( %s -> ( E e. RR /\\ ( ( H x. B ) + B ) <_ ( ( %s + 1 ) x. B ) /\\ %s ) )' % (NB, LG, SUP))], 'jca',
                   '( %s -> ( ( ( H x. B ) e. RR /\\ ( ( %s + 1 ) x. B ) e. RR /\\ B e. RR ) /\\ ( E e. RR /\\ ( ( H x. B ) + B ) <_ ( ( %s + 1 ) x. B ) /\\ %s ) ) )' % (NB, LG, LG, SUP)),
               w.inst('extgocbd')], 'syl', '( %s -> B <_ E )' % NB)
    nlt = w.s([w.s([nb(er, 'E e. RR'), nb(br, 'B e. RR')], 'ltnled', '( %s -> ( E < B <-> -. B <_ E ) )' % NB),
               nb(h3, 'E < B')], 'mpbid', '( %s -> -. B <_ E )' % NB)
    conb = w.s([ble, nlt], 'pm2.21dd', '( %s -> ( %s + 1 ) <_ H )' % (NB, LG))
    hge = w.s([w.s([], 'simpr', '( ( %s /\\ ( %s + 1 ) <_ H ) -> ( %s + 1 ) <_ H )' % (U, LG, LG)), conb], 'pm2.61dan',
              '( %s -> ( %s + 1 ) <_ H )' % (U, LG))
    lg1z = w.s([w.s([lgn], 'nn0zd', '( %s -> %s e. ZZ )' % (U, LG)), w.inst('peano2z')], 'syl',
               '( %s -> ( %s + 1 ) e. ZZ )' % (U, LG))
    huzj = w.s([lg1z, w.s([hh], 'nn0zd', '( %s -> H e. ZZ )' % U), hge], '3jca',
               '( %s -> ( ( %s + 1 ) e. ZZ /\\ H e. ZZ /\\ ( %s + 1 ) <_ H ) )' % (U, LG, LG))
    huz = w.s([huzj, w.inst('eluz2')], 'sylibr', '( %s -> H e. ( ZZ>= ` ( %s + 1 ) ) )' % (U, LG))
    expm = w.s([w.s([l1r, lin.linarith(w, U, [l2], '1 <_ %s' % L1, leaves={'L': lr}), huz], '3jca',
                    '( %s -> ( %s e. RR /\\ 1 <_ %s /\\ H e. ( ZZ>= ` ( %s + 1 ) ) ) )' % (U, L1, L1, LG)),
                w.inst('leexp2a')], 'syl', '( %s -> %s <_ %s )' % (U, PWL, PW))
    pwlr = w.s([w.s([l1n, w.s([lgn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (U, LG)),
                     w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (U, PWL))], 'nnred',
               '( %s -> %s e. RR )' % (U, PWL))
    chain = lin.linarith(w, U, [expm, h1, h2], '%s <_ N' % PWL,
                         leaves={PWL: pwlr, PW: pwr, 'M': mr, 'N': nr})
    nlog = w.s([l1u, nnn, w.inst('nloglt')], 'syl2anc', '( %s -> N < %s )' % (U, PWL))
    nch = w.s([w.s([nr, pwlr], 'ltnled', '( %s -> ( N < %s <-> -. %s <_ N ) )' % (U, PWL, PWL)), nlog], 'mpbid',
              '( %s -> -. %s <_ N )' % (U, PWL))
    w.qed([chain, nch], 'pm2.65da', '( %s -> -. %s )' % (A, HYP))
    run(w)

# ------------------------------------------------------------------ extgoq
OC = '( O e. Word NN0 /\\ A. p e. ran O ( 2 <_ p /\\ p <_ X ) )'
if not only or 'extgoq' in only:
    w = W('extgoq', 'The entries of a sublist of the pool are at least two and at most the ceiling.')
    A = '( %s /\\ ( S e. Word NN0 /\\ ran S C_ ran O ) )' % OC
    p0 = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, OC))], 'simpld', '( %s -> O e. Word NN0 )' % A)
    pall = w.s([w.s([], 'simpl', '( %s -> %s )' % (A, OC))], 'simprd',
               '( %s -> A. p e. ran O ( 2 <_ p /\\ p <_ X ) )' % A)
    ss = w.s([w.s([], 'simpr', '( %s -> ( S e. Word NN0 /\\ ran S C_ ran O ) )' % A)], 'simpld',
             '( %s -> S e. Word NN0 )' % A)
    sub = w.s([w.s([], 'simpr', '( %s -> ( S e. Word NN0 /\\ ran S C_ ran O ) )' % A)], 'simprd',
              '( %s -> ran S C_ ran O )' % A)
    B = '( %s /\\ q e. ran S )' % A
    b = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (B, f))
    qp0 = w.s([b(sub, 'ran S C_ ran O'), w.s([], 'simpr', '( %s -> q e. ran S )' % B)], 'sseldd',
              '( %s -> q e. ran O )' % B)
    sbp = w.s([w.s([], 'breq2', '( p = q -> ( 2 <_ p <-> 2 <_ q ) )'),
               w.s([], 'breq1', '( p = q -> ( p <_ X <-> q <_ X ) )')], 'anbi12d',
              '( p = q -> ( ( 2 <_ p /\\ p <_ X ) <-> ( 2 <_ q /\\ q <_ X ) ) )')
    got = w.s([sbp, b(pall, 'A. p e. ran O ( 2 <_ p /\\ p <_ X )'), qp0], 'rspcdva',
              '( %s -> ( 2 <_ q /\\ q <_ X ) )' % B)
    q2 = w.s([got], 'simpld', '( %s -> 2 <_ q )' % B)
    qx = w.s([got], 'simprd', '( %s -> q <_ X )' % B)
    qn0 = w.s([w.s([b(ss, 'S e. Word NN0'), w.s([], 'simpr', '( %s -> q e. ran S )' % B)], 'jca',
                   '( %s -> ( S e. Word NN0 /\\ q e. ran S ) )' % B), w.inst('algwrdrn')], 'syl',
              '( %s -> q e. NN0 )' % B)
    qr = w.s([qn0], 'nn0red', '( %s -> q e. RR )' % B)
    q1 = lin.linarith(w, B, [q2], '1 <_ q', leaves={'q': qr})
    g1 = w.s([q1], 'ralrimiva', '( %s -> A. q e. ran S 1 <_ q )' % A)
    g2 = w.s([q2], 'ralrimiva', '( %s -> A. q e. ran S 2 <_ q )' % A)
    g3 = w.s([qx], 'ralrimiva', '( %s -> A. q e. ran S q <_ X )' % A)
    pn = w.s([ss, g1, w.inst('algprodnn')], 'syl2anc', '( %s -> %s e. NN )' % (A, PRD('S')))
    w.qed([w.s([g1, g2], 'jca', '( %s -> ( A. q e. ran S 1 <_ q /\\ A. q e. ran S 2 <_ q ) )' % A),
           w.s([g3, pn], 'jca', '( %s -> ( A. q e. ran S q <_ X /\\ %s e. NN ) )' % (A, PRD('S')))], 'jca',
          '( %s -> ( ( A. q e. ran S 1 <_ q /\\ A. q e. ran S 2 <_ q ) /\\ ( A. q e. ran S q <_ X /\\ %s e. NN ) ) )' % (A, PRD('S')))
    run(w)

# ------------------------------------------------------------------ extgol3
if not only or 'extgol3' in only:
    w = W('extgol3', 'A hit multiplies the running product by at least the modulus plus one.')
    A = ('( ( L e. NN /\\ 2 <_ L ) /\\ ( S e. Word NN0 /\\ S =/= (/) /\\ A. q e. ran S 1 <_ q ) /\\ '
         '( A. q e. ran S 2 <_ q /\\ ( %s mod L ) = ( 1 mod L ) ) )' % PRD('S'))
    ll = w.s([w.s([], 'simp1', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)], 'simpld', '( %s -> L e. NN )' % A)
    l2 = w.s([w.s([], 'simp1', '( %s -> ( L e. NN /\\ 2 <_ L ) )' % A)], 'simprd', '( %s -> 2 <_ L )' % A)
    ss = w.s([w.s([], 'simp2', '( %s -> ( S e. Word NN0 /\\ S =/= (/) /\\ A. q e. ran S 1 <_ q ) )' % A)], 'simp1d',
             '( %s -> S e. Word NN0 )' % A)
    snz = w.s([w.s([], 'simp2', '( %s -> ( S e. Word NN0 /\\ S =/= (/) /\\ A. q e. ran S 1 <_ q ) )' % A)], 'simp2d',
              '( %s -> S =/= (/) )' % A)
    s1 = w.s([w.s([], 'simp2', '( %s -> ( S e. Word NN0 /\\ S =/= (/) /\\ A. q e. ran S 1 <_ q ) )' % A)], 'simp3d',
             '( %s -> A. q e. ran S 1 <_ q )' % A)
    s2 = w.s([w.s([], 'simp3', '( %s -> ( A. q e. ran S 2 <_ q /\\ ( %s mod L ) = ( 1 mod L ) ) )' % (A, PRD('S')))], 'simpld',
             '( %s -> A. q e. ran S 2 <_ q )' % A)
    mo = w.s([w.s([], 'simp3', '( %s -> ( A. q e. ran S 2 <_ q /\\ ( %s mod L ) = ( 1 mod L ) ) )' % (A, PRD('S')))], 'simprd',
             '( %s -> ( %s mod L ) = ( 1 mod L ) )' % (A, PRD('S')))
    pn = w.s([ss, s1, w.inst('algprodnn')], 'syl2anc', '( %s -> %s e. NN )' % (A, PRD('S')))
    dvd = w.s([w.s([ll, w.s([pn], 'nnzd', '( %s -> %s e. ZZ )' % (A, PRD('S'))),
                    w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A), w.inst('moddvds')], 'syl3anc',
                   '( %s -> ( ( %s mod L ) = ( 1 mod L ) <-> L || ( %s - 1 ) ) )' % (A, PRD('S'), PRD('S'))), mo], 'mpbid',
               '( %s -> L || ( %s - 1 ) )' % (A, PRD('S')))
    lnn = w.s([ss, snz, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` S ) e. NN )' % A)
    zfz = w.s([lnn, w.s([w.s([], 'lbfzo0', '( 0 e. ( 0 ..^ ( # ` S ) ) <-> ( # ` S ) e. NN )')], 'a1i',
                        '( %s -> ( 0 e. ( 0 ..^ ( # ` S ) ) <-> ( # ` S ) e. NN ) )' % A)], 'mpbird',
              '( %s -> 0 e. ( 0 ..^ ( # ` S ) ) )' % A)
    s0r = w.s([w.s([ss, w.inst('wrdfn')], 'syl', '( %s -> S Fn ( 0 ..^ ( # ` S ) ) )' % A), zfz, w.inst('fnfvelrn')], 'syl2anc',
              '( %s -> ( S ` 0 ) e. ran S )' % A)
    s0ge = w.s([w.s([], 'breq2', '( q = ( S ` 0 ) -> ( 2 <_ q <-> 2 <_ ( S ` 0 ) ) )'), s2, s0r], 'rspcdva',
               '( %s -> 2 <_ ( S ` 0 ) )' % A)
    s0n = w.s([w.s([ss, s0r], 'jca', '( %s -> ( S e. Word NN0 /\\ ( S ` 0 ) e. ran S ) )' % A), w.inst('algwrdrn')], 'syl',
              '( %s -> ( S ` 0 ) e. NN0 )' % A)
    s0d = w.s([w.s([ss, s0r], 'jca', '( %s -> ( S e. Word NN0 /\\ ( S ` 0 ) e. ran S ) )' % A), w.inst('algdvdprod')], 'syl',
              '( %s -> ( S ` 0 ) || %s )' % (A, PRD('S')))
    s0le = w.s([w.s([w.s([w.s([s0n], 'nn0zd', '( %s -> ( S ` 0 ) e. ZZ )' % A), pn], 'jca',
                         '( %s -> ( ( S ` 0 ) e. ZZ /\\ %s e. NN ) )' % (A, PRD('S'))), w.inst('dvdsle')], 'syl',
                    '( %s -> ( ( S ` 0 ) || %s -> ( S ` 0 ) <_ %s ) )' % (A, PRD('S'), PRD('S'))), s0d], 'mpd',
               '( %s -> ( S ` 0 ) <_ %s )' % (A, PRD('S')))
    pr = w.s([pn], 'nnred', '( %s -> %s e. RR )' % (A, PRD('S')))
    s0rr = w.s([s0n], 'nn0red', '( %s -> ( S ` 0 ) e. RR )' % A)
    lr = w.s([ll], 'nnred', '( %s -> L e. RR )' % A)
    p2 = lin.linarith(w, A, [s0ge, s0le], '2 <_ %s' % PRD('S'), leaves={'( S ` 0 )': s0rr, PRD('S'): pr})
    pm1 = w.s([w.s([w.s([w.s([pn], 'nnzd', '( %s -> %s e. ZZ )' % (A, PRD('S'))), w.inst('peano2zm')], 'syl',
                        '( %s -> ( %s - 1 ) e. ZZ )' % (A, PRD('S'))),
                    lin.linarith(w, A, [p2], '1 <_ ( %s - 1 )' % PRD('S'), leaves={PRD('S'): pr})], 'jca',
                   '( %s -> ( ( %s - 1 ) e. ZZ /\\ 1 <_ ( %s - 1 ) ) )' % (A, PRD('S'), PRD('S'))),
               w.s([w.s([], 'elnnz1', '( ( %s - 1 ) e. NN <-> ( ( %s - 1 ) e. ZZ /\\ 1 <_ ( %s - 1 ) ) )' % (PRD('S'), PRD('S'), PRD('S')))],
                   'a1i', '( %s -> ( ( %s - 1 ) e. NN <-> ( ( %s - 1 ) e. ZZ /\\ 1 <_ ( %s - 1 ) ) ) )' % (A, PRD('S'), PRD('S'), PRD('S')))],
              'mpbird', '( %s -> ( %s - 1 ) e. NN )' % (A, PRD('S')))
    lle = w.s([w.s([w.s([w.s([ll], 'nnzd', '( %s -> L e. ZZ )' % A), pm1], 'jca',
                        '( %s -> ( L e. ZZ /\\ ( %s - 1 ) e. NN ) )' % (A, PRD('S'))), w.inst('dvdsle')], 'syl',
                   '( %s -> ( L || ( %s - 1 ) -> L <_ ( %s - 1 ) ) )' % (A, PRD('S'), PRD('S'))), dvd], 'mpd',
              '( %s -> L <_ ( %s - 1 ) )' % (A, PRD('S')))
    fin = lin.linarith(w, A, [lle], '( L + 1 ) <_ %s' % PRD('S'), leaves={'L': lr, PRD('S'): pr})
    w.qed([dvd, fin], 'jca', '( %s -> ( L || ( %s - 1 ) /\\ ( L + 1 ) <_ %s ) )' % (A, PRD('S'), PRD('S')))
    run(w)

# ------------------------------------------------------------------ extgol4
if not only or 'extgol4' in only:
    w = W('extgol4', 'The product of a hit is at most the ceiling to the batch size.')
    A = ('( ( X e. NN0 /\\ 1 <_ X /\\ B e. NN0 ) /\\ ( S e. Word NN0 /\\ A. q e. ran S q <_ X /\\ ( # ` S ) <_ B ) )')
    xx = w.s([w.s([], 'simpl', '( %s -> ( X e. NN0 /\\ 1 <_ X /\\ B e. NN0 ) )' % A)], 'simp1d', '( %s -> X e. NN0 )' % A)
    x1 = w.s([w.s([], 'simpl', '( %s -> ( X e. NN0 /\\ 1 <_ X /\\ B e. NN0 ) )' % A)], 'simp2d', '( %s -> 1 <_ X )' % A)
    bb = w.s([w.s([], 'simpl', '( %s -> ( X e. NN0 /\\ 1 <_ X /\\ B e. NN0 ) )' % A)], 'simp3d', '( %s -> B e. NN0 )' % A)
    ss = w.s([w.s([], 'simpr', '( %s -> ( S e. Word NN0 /\\ A. q e. ran S q <_ X /\\ ( # ` S ) <_ B ) )' % A)], 'simp1d',
             '( %s -> S e. Word NN0 )' % A)
    qx = w.s([w.s([], 'simpr', '( %s -> ( S e. Word NN0 /\\ A. q e. ran S q <_ X /\\ ( # ` S ) <_ B ) )' % A)], 'simp2d',
             '( %s -> A. q e. ran S q <_ X )' % A)
    lb = w.s([w.s([], 'simpr', '( %s -> ( S e. Word NN0 /\\ A. q e. ran S q <_ X /\\ ( # ` S ) <_ B ) )' % A)], 'simp3d',
             '( %s -> ( # ` S ) <_ B )' % A)
    ple = w.s([w.s([w.s([ss, xx], 'jca', '( %s -> ( S e. Word NN0 /\\ X e. NN0 ) )' % A), qx], 'jca',
                   '( %s -> ( ( S e. Word NN0 /\\ X e. NN0 ) /\\ A. q e. ran S q <_ X ) )' % A), w.inst('algprodle')], 'syl',
              '( %s -> %s <_ ( X ^ ( # ` S ) ) )' % (A, PRD('S')))
    lcl = w.s([ss, w.inst('lencl')], 'syl', '( %s -> ( # ` S ) e. NN0 )' % A)
    buzj = w.s([w.s([lcl], 'nn0zd', '( %s -> ( # ` S ) e. ZZ )' % A),
                w.s([bb], 'nn0zd', '( %s -> B e. ZZ )' % A), lb], '3jca',
               '( %s -> ( ( # ` S ) e. ZZ /\\ B e. ZZ /\\ ( # ` S ) <_ B ) )' % A)
    buz = w.s([buzj, w.inst('eluz2')], 'sylibr', '( %s -> B e. ( ZZ>= ` ( # ` S ) ) )' % A)
    expj = w.s([w.s([xx], 'nn0red', '( %s -> X e. RR )' % A), x1, buz], '3jca',
               '( %s -> ( X e. RR /\\ 1 <_ X /\\ B e. ( ZZ>= ` ( # ` S ) ) ) )' % A)
    expm = w.s([expj, w.inst('leexp2a')], 'syl', '( %s -> ( X ^ ( # ` S ) ) <_ ( X ^ B ) )' % A)
    pr = w.s([w.s([ss, w.inst('algprodcl')], 'syl', '( %s -> %s e. NN0 )' % (A, PRD('S')))], 'nn0red',
             '( %s -> %s e. RR )' % (A, PRD('S')))
    e1 = w.s([w.s([xx, lcl], 'nn0expcld', '( %s -> ( X ^ ( # ` S ) ) e. NN0 )' % A)], 'nn0red',
             '( %s -> ( X ^ ( # ` S ) ) e. RR )' % A)
    e2 = w.s([w.s([xx, bb], 'nn0expcld', '( %s -> ( X ^ B ) e. NN0 )' % A)], 'nn0red', '( %s -> ( X ^ B ) e. RR )' % A)
    w.qed([pr, e1, e2, ple, expm], 'letrd', '( %s -> %s <_ ( X ^ B ) )' % (A, PRD('S')))
    run(w)

# ------------------------------------------------------------------ extgol2
VEBK = ('A. w e. ~P ran O ( ( # ` w ) = B -> E. s e. ~P w ( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) ) )')
if not only or 'extgol2' in only:
    w = W('extgol2', 'A full batch of fresh elements fills the residue one (Lean: the VEBK step of extractGo_spec).')
    A = ("( ( ( L e. NN /\\ O e. Word NN0 /\\ %s ) /\\ ( G e. Word NN0 /\\ Fun `' G /\\ ( # ` G ) = B ) /\\ "
         "ran G C_ ran O ) /\\ %s )" % (VEBK, TC('L', 'T', 'G')))
    p3 = w.s([], 'simpl1', '( %s -> ( L e. NN /\\ O e. Word NN0 /\\ %s ) )' % (A, VEBK))
    ll = w.s([p3], 'simp1d', '( %s -> L e. NN )' % A)
    p0 = w.s([p3], 'simp2d', '( %s -> O e. Word NN0 )' % A)
    vb = w.s([p3], 'simp3d', '( %s -> %s )' % (A, VEBK))
    g3 = w.s([], 'simpl2', "( %s -> ( G e. Word NN0 /\\ Fun `' G /\\ ( # ` G ) = B ) )" % A)
    gg = w.s([g3], 'simp1d', '( %s -> G e. Word NN0 )' % A)
    fug = w.s([g3], 'simp2d', "( %s -> Fun `' G )" % A)
    lng = w.s([g3], 'simp3d', '( %s -> ( # ` G ) = B )' % A)
    sub = w.s([], 'simpl3', '( %s -> ran G C_ ran O )' % A)
    tc = w.s([], 'simpr', '( %s -> %s )' % (A, TC('L', 'T', 'G')))
    rex = w.s([w.s([gg], 'elexd', '( %s -> G e. _V )' % A), w.inst('rnexg')], 'syl', '( %s -> ran G e. _V )' % A)
    rpw = w.s([sub, w.s([rex, w.inst('elpwg')], 'syl', '( %s -> ( ran G e. ~P ran O <-> ran G C_ ran O ) )' % A)], 'mpbird',
              '( %s -> ran G e. ~P ran O )' % A)
    card = w.s([w.s([w.s([gg, fug], 'jca', "( %s -> ( G e. Word NN0 /\\ Fun `' G ) )" % A), w.inst('algwrdcard')], 'syl',
                    '( %s -> ( # ` ran G ) = ( # ` G ) )' % A), lng], 'eqtrd', '( %s -> ( # ` ran G ) = B )' % A)
    idw = w.s([], 'id', '( w = ran G -> w = ran G )')
    sbv, nvb = w.wcongr('( ( # ` w ) = B -> E. s e. ~P w ( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) ) )',
                        {'w': 'ran G'}, 'w = ran G', {'w': idw})
    vg = w.s([sbv, vb, rpw], 'rspcdva', '( %s -> %s )' % (A, nvb))
    got = w.s([vg, card], 'mpd', '( %s -> E. s e. ~P ran G ( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) ) )' % A)
    idc = w.s([], 'id', '( s = c -> s = c )')
    sbc, nbc = w.wcongr('( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) )', {'s': 'c'}, 's = c', {'s': idc})
    cbv = w.s([sbc], 'cbvrexv',
              '( E. s e. ~P ran G ( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) ) <-> E. c e. ~P ran G %s )' % nbc)
    got2 = w.s([got, w.s([cbv], 'a1i',
                         '( %s -> ( E. s e. ~P ran G ( s =/= (/) /\\ L || ( prod_ q e. s q - 1 ) ) <-> E. c e. ~P ran G %s ) )' % (A, nbc))],
               'mpbid', '( %s -> E. c e. ~P ran G %s )' % (A, nbc))
    C = '( %s /\\ c e. ~P ran G )' % A
    c = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (C, f))
    cpw = w.s([], 'simpr', '( %s -> c e. ~P ran G )' % C)
    D = '( %s /\\ %s )' % (C, nbc)
    d = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (D, f))
    cnz = w.s([w.s([], 'simpr', '( %s -> %s )' % (D, nbc))], 'simpld', '( %s -> c =/= (/) )' % D)
    cdv = w.s([w.s([], 'simpr', '( %s -> %s )' % (D, nbc))], 'simprd', '( %s -> L || ( prod_ q e. c q - 1 ) )' % D)
    idt = w.s([], 'id', '( s = c -> s = c )')
    sbt, nbt = w.wcongr('( s =/= (/) -> ( T ` ( prod_ q e. s q mod L ) ) =/= %s )' % NONE, {'s': 'c'}, 's = c', {'s': idt})
    tci = w.s([sbt, d(c(tc, TC('L', 'T', 'G')), TC('L', 'T', 'G')), d(cpw, 'c e. ~P ran G')], 'rspcdva',
              '( %s -> %s )' % (D, nbt))
    nne = w.s([tci, cnz], 'mpd', '( %s -> ( T ` ( prod_ q e. c q mod L ) ) =/= %s )' % (D, NONE))
    pcl = w.s([w.s([d(c(gg, 'G e. Word NN0'), 'G e. Word NN0'), d(cpw, 'c e. ~P ran G')], 'jca',
                   '( %s -> ( G e. Word NN0 /\\ c e. ~P ran G ) )' % D), w.inst('tcsprod')], 'syl',
              '( %s -> prod_ q e. c q e. NN0 )' % D)
    mo = w.s([w.s([w.s([pcl, d(c(ll, 'L e. NN'), 'L e. NN')], 'jca', '( %s -> ( prod_ q e. c q e. NN0 /\\ L e. NN ) )' % D),
                   cdv], 'jca', '( %s -> ( ( prod_ q e. c q e. NN0 /\\ L e. NN ) /\\ L || ( prod_ q e. c q - 1 ) ) )' % D),
              w.inst('modone')], 'syl', '( %s -> ( prod_ q e. c q mod L ) = ( 1 mod L ) )' % D)
    fin = w.s([w.s([w.s([mo], 'fveq2d', '( %s -> ( T ` ( prod_ q e. c q mod L ) ) = ( T ` ( 1 mod L ) ) )' % D)], 'eqcomd',
                   '( %s -> ( T ` ( 1 mod L ) ) = ( T ` ( prod_ q e. c q mod L ) ) )' % D), nne], 'eqnetrd',
              '( %s -> ( T ` ( 1 mod L ) ) =/= %s )' % (D, NONE))
    w.qed([got2, w.s([w.s([fin], 'ex', '( %s -> ( %s -> ( T ` ( 1 mod L ) ) =/= %s ) )' % (C, nbc, NONE))], 'rexlimdva',
                     '( %s -> ( E. c e. ~P ran G %s -> ( T ` ( 1 mod L ) ) =/= %s ) )' % (A, nbc, NONE))], 'mpd',
          '( %s -> ( T ` ( 1 mod L ) ) =/= %s )' % (A, NONE))
    run(w)
